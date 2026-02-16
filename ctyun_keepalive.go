package main

import (
	"bufio"
	"bytes"
	"context"
	"crypto/md5"
	"crypto/rand"
	"crypto/sha1"
	"crypto/sha256"
	"encoding/base64"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"math/big"
	"mime/multipart"
	"net/http"
	"net/url"
	"os"
	"os/signal"
	"strings"
	"sync"
	"syscall"
	"time"

	"github.com/gorilla/websocket"
)

type LoginInfo struct {
	UserAccount  string `json:"userAccount"`
	BondedDevice bool   `json:"bondedDevice"`
	SecretKey    string `json:"secretKey"`
	UserId       int    `json:"userId"`
	TenantId     int    `json:"tenantId"`
	UserName     string `json:"userName"`
}

type DesktopInfo struct {
	DesktopId           int    `json:"desktopId"`
	Host                string `json:"host"`
	Port                string `json:"port"`
	ClinkLvsOutHost     string `json:"clinkLvsOutHost"`
	CaCert              string `json:"caCert"`
	ClientCert          string `json:"clientCert"`
	ClientKey           string `json:"clientKey"`
	Token               string `json:"token"`
	TenantMemberAccount string `json:"tenantMemberAccount"`
}

func (d DesktopInfo) ToBuffer(deviceCode string) []byte {
	deviceType := "60"
	headerSize := 36
	totalSize := headerSize + len(d.Token) + 1 + len(deviceType) + 1 + len(deviceCode) + 1 + len(d.TenantMemberAccount) + 1
	buffer := make([]byte, totalSize)
	currentOffset := headerSize
	writeUint32 := func(offset int, value uint32) {
		binary.LittleEndian.PutUint32(buffer[offset:offset+4], value)
	}
	writeUint32(0, uint32(d.DesktopId))
	writeUint32(4, uint32(len(d.Token)+1))
	writeUint32(8, uint32(currentOffset))
	currentOffset += len(d.Token) + 1
	writeUint32(12, uint32(len(deviceType)+1))
	writeUint32(16, uint32(currentOffset))
	currentOffset += len(deviceType) + 1
	writeUint32(20, uint32(len(deviceCode)+1))
	writeUint32(24, uint32(currentOffset))
	currentOffset += len(deviceCode) + 1
	writeUint32(28, uint32(len(d.TenantMemberAccount)+1))
	writeUint32(32, uint32(currentOffset))
	bodyOffset := headerSize
	for _, s := range []string{d.Token, deviceType, deviceCode, d.TenantMemberAccount} {
		data := []byte(s)
		copy(buffer[bodyOffset:], data)
		bodyOffset += len(data)
		buffer[bodyOffset] = 0
		bodyOffset++
	}
	return buffer
}

type Desktop struct {
	DesktopId    string       `json:"desktopId"`
	DesktopName  string       `json:"desktopName"`
	DesktopCode  string       `json:"desktopCode"`
	UseStatusText string      `json:"useStatusText"`
	DesktopInfo  *DesktopInfo `json:"-"`
}

type ResultBase[T any] struct {
	Code int    `json:"code"`
	Msg  string `json:"msg"`
	Data T      `json:"data"`
}

type ChallengeData struct {
	ChallengeId   string `json:"challengeId"`
	ChallengeCode string `json:"challengeCode"`
}

type ClientInfo struct {
	DesktopList []Desktop `json:"desktopList"`
}

type ConnectInfo struct {
	DesktopInfo *DesktopInfo `json:"desktopInfo"`
}

type SendInfo struct {
	Type int
	Data []byte
}

type Account struct {
	UserAccount string `json:"user_account"`
	Password    string `json:"password"`
	DeviceCode  string `json:"device_code"`
}

type AccountsFile struct {
	Accounts []Account `json:"accounts"`
}

func (s SendInfo) ToBuffer(isBuildMsg bool) []byte {
	msgLength := 0
	if isBuildMsg {
		msgLength = 8
	}
	dataLength := len(s.Data)
	size := msgLength + dataLength
	buffer := make([]byte, 2+4+msgLength+dataLength)
	binary.LittleEndian.PutUint16(buffer[0:2], uint16(s.Type))
	binary.LittleEndian.PutUint32(buffer[2:6], uint32(size))
	if isBuildMsg {
		binary.LittleEndian.PutUint32(buffer[6:10], uint32(dataLength))
		binary.LittleEndian.PutUint32(buffer[10:14], 8)
	}
	if dataLength > 0 {
		copy(buffer[6+msgLength:], s.Data)
	}
	return buffer
}

func SendInfoFromBuffer(buffer []byte) []SendInfo {
	results := []SendInfo{}
	if len(buffer) == 0 {
		return results
	}
	offset := 0
	for offset+6 <= len(buffer) {
		typeValue := int(binary.LittleEndian.Uint16(buffer[offset : offset+2]))
		dataLength := int(int32(binary.LittleEndian.Uint32(buffer[offset+2 : offset+6])))
		if dataLength < 0 || offset+6+dataLength > len(buffer) {
			remaining := len(buffer) - offset
			if remaining > 0 {
				data := make([]byte, remaining)
				copy(data, buffer[offset:offset+remaining])
				results = append(results, SendInfo{Type: typeValue, Data: data})
			}
			break
		}
		data := []byte{}
		if dataLength > 0 {
			data = make([]byte, dataLength)
			copy(data, buffer[offset+6:offset+6+dataLength])
		}
		results = append(results, SendInfo{Type: typeValue, Data: data})
		offset += 6 + dataLength
		if offset+6 > len(buffer) && offset < len(buffer) {
			allZero := true
			for i := offset; i < len(buffer); i++ {
				if buffer[i] != 0 {
					allZero = false
					break
				}
			}
			if allZero {
				offset = len(buffer)
				break
			}
		}
	}
	return results
}

type Encryption struct {
	buffers       [][]byte
	authMechanism uint32
}

func NewEncryption() *Encryption {
	return &Encryption{buffers: [][]byte{}, authMechanism: 1}
}

func (e *Encryption) Execute(key []byte) []byte {
	e.resolveInboundData(key)
	n, eVal := e.getPublicKey()
	encrypted := e.l(128, "", n, eVal)
	return e.toBuffer(encrypted)
}

func (e *Encryption) resolveInboundData(data []byte) {
	if len(data) <= 16 {
		e.buffers = append(e.buffers, []byte{})
		return
	}
	buf := make([]byte, len(data[16:]))
	copy(buf, data[16:])
	e.buffers = append(e.buffers, buf)
}

func (e *Encryption) getPublicKey() (*big.Int, int) {
	if len(e.buffers) == 0 || len(e.buffers[0]) < 166 {
		return big.NewInt(0), 0
	}
	nSource := e.buffers[0][32 : 32+129]
	n := new(big.Int).SetBytes(nSource)
	eSource := e.buffers[0][163:166]
	eVal := (int(eSource[0]) << 16) | (int(eSource[1]) << 8) | int(eSource[2])
	return n, eVal
}

func (e *Encryption) l(keyLen int, label string, n *big.Int, eVal int) []byte {
	seed := make([]byte, 20)
	_, _ = rand.Read(seed)
	hLen := 20
	dbLen := keyLen - hLen - 1
	db := make([]byte, dbLen)
	lHash := sha1.Sum([]byte(label))
	copy(db[0:len(lHash)], lHash[:])
	db[dbLen-1-len(label)-1] = 1
	dbMask := e.mgf1(seed, dbLen)
	for k := 0; k < dbLen; k++ {
		db[k] ^= dbMask[k]
	}
	seedMask := e.mgf1(db, hLen)
	for k := 0; k < hLen; k++ {
		seed[k] ^= seedMask[k]
	}
	em := make([]byte, keyLen)
	copy(em[1:1+hLen], seed)
	copy(em[1+hLen:], db)
	m := new(big.Int).SetBytes(em)
	resultInt := new(big.Int).Exp(m, big.NewInt(int64(eVal)), n)
	resultBytes := resultInt.Bytes()
	if len(resultBytes) == keyLen {
		return resultBytes
	}
	final := make([]byte, keyLen)
	copy(final[keyLen-len(resultBytes):], resultBytes)
	return final
}

func (e *Encryption) mgf1(seed []byte, maskLen int) []byte {
	mask := make([]byte, maskLen)
	counter := 0
	offset := 0
	for offset < maskLen {
		c := make([]byte, 4)
		binary.BigEndian.PutUint32(c, uint32(counter))
		block := append(append([]byte{}, seed...), c...)
		hashBytes := sha1.Sum(block)
		copyLen := len(hashBytes)
		if copyLen > maskLen-offset {
			copyLen = maskLen - offset
		}
		copy(mask[offset:offset+copyLen], hashBytes[:copyLen])
		offset += len(hashBytes)
		counter++
	}
	return mask
}

func (e *Encryption) toBuffer(buffer []byte) []byte {
	result := make([]byte, 4+len(buffer))
	binary.LittleEndian.PutUint32(result[0:4], e.authMechanism)
	copy(result[4:], buffer)
	return result
}

type CtYunApi struct {
	deviceCode  string
	loginInfo   *LoginInfo
	client      *http.Client
	baseHeaders map[string]string
}

func NewCtYunApi(deviceCode string) *CtYunApi {
	return &CtYunApi{
		deviceCode: deviceCode,
		client: &http.Client{
			Timeout: 30 * time.Second,
		},
		baseHeaders: map[string]string{
			"User-Agent":     "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/137.0.0.0 Safari/537.36",
			"ctg-devicetype": "60",
			"ctg-version":    "103020001",
			"ctg-devicecode": deviceCode,
			"referer":        "https://pc.ctyun.cn/",
		},
	}
}

func (api *CtYunApi) Login(userPhone, password string) bool {
	for i := 1; i < 4; i++ {
		challenge := api.GetGenChallengeData()
		if challenge == nil {
			continue
		}
		captchaCode := api.GetCaptcha(api.GetLoginCaptcha(userPhone))
		if captchaCode == "" {
			continue
		}
		collection := url.Values{}
		collection.Add("userAccount", userPhone)
		collection.Add("password", computeSHA256(password+challenge.ChallengeCode))
		collection.Add("sha256Password", computeSHA256(computeSHA256(password)+challenge.ChallengeCode))
		collection.Add("challengeId", challenge.ChallengeId)
		collection.Add("captchaCode", captchaCode)
		api.addCollection(collection)
		var result ResultBase[LoginInfo]
		err := api.postForm("https://desk.ctyun.cn:8810/api/auth/client/login", collection, &result)
		if err == nil && result.Code == 0 {
			api.loginInfo = &result.Data
			return true
		}
		msg := result.Msg
		if msg == "" && err != nil {
			msg = err.Error()
		}
		writeLine(fmt.Sprintf("重试%d, Login Error:%s", i, msg))
		if msg == "用户名或密码错误" {
			return false
		}
	}
	return false
}

func (api *CtYunApi) GetSmsCode(userPhone string) bool {
	for i := 0; i < 3; i++ {
		captchaCode := api.GetCaptcha(api.GetSmsCodeCaptcha())
		if captchaCode != "" {
			var result ResultBase[bool]
			err := api.getJSON("https://desk.ctyun.cn:8810/api/cdserv/client/device/getSmsCode?mobilePhone="+userPhone+"&captchaCode="+captchaCode, &result)
			if err == nil && result.Code == 0 {
				return true
			}
			msg := result.Msg
			if msg == "" && err != nil {
				msg = err.Error()
			}
			writeLine(fmt.Sprintf("重试%d, GetSmsCode Error:%s", i, msg))
		}
	}
	return false
}

func (api *CtYunApi) BindingDevice(verificationCode string) bool {
	urlStr := "https://desk.ctyun.cn:8810/api/cdserv/client/device/binding?verificationCode=" + url.QueryEscape(verificationCode) + "&deviceName=Chrome%E6%B5%8F%E8%A7%88%E5%99%A8&deviceCode=" + url.QueryEscape(api.deviceCode) + "&deviceModel=Windows+NT+10.0%3B+Win64%3B+x64&sysVersion=Windows+NT+10.0%3B+Win64%3B+x64&appVersion=3.2.0&hostName=pc.ctyun.cn&deviceInfo=Win32"
	var result ResultBase[bool]
	err := api.postJSON(urlStr, nil, &result)
	if err == nil && result.Code == 0 {
		return true
	}
	msg := result.Msg
	if msg == "" && err != nil {
		msg = err.Error()
	}
	writeLine("BindingDevice Error:" + msg)
	return false
}

func (api *CtYunApi) GetGenChallengeData() *ChallengeData {
	var result ResultBase[ChallengeData]
	err := api.postJSON("https://desk.ctyun.cn:8810/api/auth/client/genChallengeData", map[string]string{}, &result)
	if err == nil && result.Code == 0 {
		return &result.Data
	}
	msg := result.Msg
	if msg == "" && err != nil {
		msg = err.Error()
	}
	writeLine("GetGenChallengeDataAsync Error:" + msg)
	return nil
}

func (api *CtYunApi) GetLoginCaptcha(userPhone string) []byte {
	urlStr := "https://desk.ctyun.cn:8810/api/auth/client/captcha?height=36&width=85&userInfo=" + url.QueryEscape(userPhone) + "&mode=auto&_t=1749139280909"
	data, err := api.getBytes(urlStr, false)
	if err != nil {
		writeLine("登录验证码获取错误：" + err.Error())
		return nil
	}
	return data
}

func (api *CtYunApi) GetSmsCodeCaptcha() []byte {
	urlStr := "https://desk.ctyun.cn:8810/api/auth/client/validateCode/captcha?width=120&height=40&_t=1766158569152"
	data, err := api.getBytes(urlStr, true)
	if err != nil {
		writeLine("短信验证码获取错误：" + err.Error())
		return nil
	}
	return data
}

func (api *CtYunApi) GetCaptcha(imgBytes []byte) string {
	if len(imgBytes) == 0 {
		return ""
	}
	writeLine("正在识别验证码.")
	body := &bytes.Buffer{}
	writer := multipart.NewWriter(body)
	part, err := writer.CreateFormField("image")
	if err != nil {
		writeLine("验证码识别错误：" + err.Error())
		return ""
	}
	encoded := base64.StdEncoding.EncodeToString(imgBytes)
	_, _ = part.Write([]byte(encoded))
	_ = writer.Close()
	headers := map[string]string{
		"Content-Type": writer.FormDataContentType(),
	}
	resp, err := api.request("POST", "https://orc.1999111.xyz/ocr", body, headers, false)
	if err != nil {
		writeLine("验证码识别错误：" + err.Error())
		return ""
	}
	writeLine("识别结果：" + string(resp))
	var result struct {
		Code    int    `json:"code"`
		Message string `json:"message"`
		Data    string `json:"data"`
	}
	_ = json.Unmarshal(resp, &result)
	return result.Data
}

func (api *CtYunApi) GetClientList() []Desktop {
	payload := map[string]any{
		"getCnt":        20,
		"desktopTypes":  []string{"1", "2001", "2002", "2003"},
		"sortType":      "createTimeV1",
	}
	var result ResultBase[ClientInfo]
	err := api.postJSON("https://desk.ctyun.cn:8810/api/desktop/client/pageDesktop", payload, &result)
	if err != nil || result.Code != 0 {
		msg := result.Msg
		if msg == "" && err != nil {
			msg = err.Error()
		}
		writeLine("获取设备信息错误。" + msg)
		return nil
	}
	return result.Data.DesktopList
}

func (api *CtYunApi) Connect(desktopId string) (*ConnectInfo, string) {
	collection := url.Values{}
	collection.Add("objId", desktopId)
	collection.Add("objType", "0")
	collection.Add("osType", "15")
	collection.Add("deviceId", "60")
	collection.Add("vdCommand", "")
	collection.Add("ipAddress", "")
	collection.Add("macAddress", "")
	api.addCollection(collection)
	var result ResultBase[ConnectInfo]
	err := api.postForm("https://desk.ctyun.cn:8810/api/desktop/client/connect", collection, &result)
	if err != nil || result.Code != 0 {
		msg := result.Msg
		if msg == "" && err != nil {
			msg = err.Error()
		}
		return nil, msg
	}
	return &result.Data, ""
}

func (api *CtYunApi) applySignature(headers map[string]string) {
	if api.loginInfo == nil {
		return
	}
	timestamp := fmt.Sprintf("%d", time.Now().UnixMilli())
	headers["ctg-userid"] = fmt.Sprintf("%d", api.loginInfo.UserId)
	headers["ctg-tenantid"] = fmt.Sprintf("%d", api.loginInfo.TenantId)
	headers["ctg-timestamp"] = timestamp
	headers["ctg-requestid"] = timestamp
	signatureStr := "60" + timestamp + fmt.Sprintf("%d", api.loginInfo.TenantId) + timestamp + fmt.Sprintf("%d", api.loginInfo.UserId) + "103020001" + api.loginInfo.SecretKey
	headers["ctg-signaturestr"] = computeMD5(signatureStr)
}

func (api *CtYunApi) addCollection(values url.Values) {
	values.Add("deviceCode", api.deviceCode)
	values.Add("deviceName", "Chrome浏览器")
	values.Add("deviceType", "60")
	values.Add("deviceModel", "Windows NT 10.0; Win64; x64")
	values.Add("appVersion", "3.2.0")
	values.Add("sysVersion", "Windows NT 10.0; Win64; x64")
	values.Add("clientVersion", "103020001")
}

func (api *CtYunApi) request(method, urlStr string, body io.Reader, headers map[string]string, signed bool) ([]byte, error) {
	req, err := http.NewRequest(method, urlStr, body)
	if err != nil {
		return nil, err
	}
	merged := map[string]string{}
	for k, v := range api.baseHeaders {
		merged[k] = v
	}
	for k, v := range headers {
		merged[k] = v
	}
	if signed {
		api.applySignature(merged)
	}
	for k, v := range merged {
		req.Header.Set(k, v)
	}
	resp, err := api.client.Do(req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	return io.ReadAll(resp.Body)
}

func (api *CtYunApi) postJSON(urlStr string, payload any, out any) error {
	var body io.Reader
	headers := map[string]string{}
	if payload != nil {
		data, _ := json.Marshal(payload)
		body = bytes.NewReader(data)
		headers["Content-Type"] = "application/json"
	}
	resp, err := api.request("POST", urlStr, body, headers, true)
	if err != nil {
		return err
	}
	if out == nil {
		return nil
	}
	return json.Unmarshal(resp, out)
}

func (api *CtYunApi) postForm(urlStr string, values url.Values, out any) error {
	body := strings.NewReader(values.Encode())
	headers := map[string]string{"Content-Type": "application/x-www-form-urlencoded"}
	resp, err := api.request("POST", urlStr, body, headers, true)
	if err != nil {
		return err
	}
	return json.Unmarshal(resp, out)
}

func (api *CtYunApi) getJSON(urlStr string, out any) error {
	resp, err := api.request("GET", urlStr, nil, map[string]string{}, true)
	if err != nil {
		return err
	}
	return json.Unmarshal(resp, out)
}

func (api *CtYunApi) getBytes(urlStr string, signed bool) ([]byte, error) {
	return api.request("GET", urlStr, nil, map[string]string{}, signed)
}

func writeLine(value string) {
	ts := time.Now().Format("15:04:05.000000")
	ts = ts[:len(ts)-4]
	fmt.Printf("[%s] %s\n", ts, value)
}

func computeMD5(value string) string {
	sum := md5.Sum([]byte(value))
	return hex.EncodeToString(sum[:])
}

func computeSHA256(value string) string {
	sum := sha256.Sum256([]byte(value))
	return hex.EncodeToString(sum[:])
}

func generateRandomString(length int) string {
	const chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789"
	b := make([]byte, length)
	_, _ = rand.Read(b)
	for i := range b {
		b[i] = chars[int(b[i])%len(chars)]
	}
	return string(b)
}

var stdinReader = bufio.NewReader(os.Stdin)

func readLine(prompt string) string {
	fmt.Print(prompt)
	line, _ := stdinReader.ReadString('\n')
	return strings.TrimRight(line, "\r\n")
}

func resolveCredentials() (string, string, string) {
	if _, err := os.Stat("/.dockerenv"); err == nil {
		return os.Getenv("APP_USER"), os.Getenv("APP_PASSWORD"), os.Getenv("DEVICECODE")
	}
	
	accountsFile := "accounts.json"
	var accounts AccountsFile
	
	if data, err := os.ReadFile(accountsFile); err == nil {
		if err := json.Unmarshal(data, &accounts); err == nil && len(accounts.Accounts) > 0 {
			account := accounts.Accounts[0]
			userBytes, _ := base64.StdEncoding.DecodeString(account.UserAccount)
			passwordBytes, _ := base64.StdEncoding.DecodeString(account.Password)
			return string(userBytes), string(passwordBytes), account.DeviceCode
		}
	}
	
	for {
		deviceCode := "web_" + generateRandomString(32)
		user := readLine("账号: ")
		password := readLine("密码: ")
		
		encodedUser := base64.StdEncoding.EncodeToString([]byte(user))
		encodedPassword := base64.StdEncoding.EncodeToString([]byte(password))
		
		accounts.Accounts = append(accounts.Accounts, Account{
			UserAccount: encodedUser,
			Password:    encodedPassword,
			DeviceCode:  deviceCode,
		})
		
		_ = os.WriteFile("DeviceCode.txt", []byte(deviceCode), 0644)
		
		continueInput := readLine("是否继续添加账户? (y/n): ")
		if strings.ToLower(strings.TrimSpace(continueInput)) != "y" {
			break
		}
	}
	
	data, _ := json.MarshalIndent(accounts, "", "  ")
	_ = os.WriteFile(accountsFile, data, 0644)
	
	if len(accounts.Accounts) > 0 {
		account := accounts.Accounts[0]
		userBytes, _ := base64.StdEncoding.DecodeString(account.UserAccount)
		passwordBytes, _ := base64.StdEncoding.DecodeString(account.Password)
		return string(userBytes), string(passwordBytes), account.DeviceCode
	}
	
	return "", "", ""
}

func receiveLoop(ctx context.Context, conn *websocket.Conn, desktop Desktop, api *CtYunApi) error {
	encryptor := NewEncryption()
	for {
		select {
		case <-ctx.Done():
			return ctx.Err()
		default:
		}
		_, message, err := conn.ReadMessage()
		if err != nil {
			return err
		}
		if len(message) >= 4 && bytes.Equal(message[:4], []byte("REDQ")) {
			writeLine(fmt.Sprintf("[%s] -> 收到保活校验", desktop.DesktopCode))
			response := encryptor.Execute(message)
			err = conn.WriteMessage(websocket.BinaryMessage, response)
			if err == nil {
				writeLine(fmt.Sprintf("[%s] -> 发送保活响应成功", desktop.DesktopCode))
			}
			continue
		}
		infos := SendInfoFromBuffer(message)
		for _, info := range infos {
			if info.Type == 103 {
				userJson, _ := json.Marshal(map[string]any{
					"type":     1,
					"userName": api.loginInfo.UserName,
					"userInfo": "",
					"userId":   api.loginInfo.UserId,
				})
				payload := SendInfo{Type: 118, Data: userJson}.ToBuffer(true)
				_ = conn.WriteMessage(websocket.BinaryMessage, payload)
			}
		}
	}
}

func keepAliveWorker(ctx context.Context, desktop Desktop, api *CtYunApi, wg *sync.WaitGroup) {
	defer wg.Done()
	initialPayload, _ := base64.StdEncoding.DecodeString("UkVEUQIAAAACAAAAGgAAAAAAAAABAAEAAAABAAAAEgAAAAkAAAAECAAA")
	uri := fmt.Sprintf("wss://%s/clinkProxy/%s/MAIN", desktop.DesktopInfo.ClinkLvsOutHost, desktop.DesktopId)
	dialer := websocket.Dialer{Subprotocols: []string{"binary"}}
	for {
		select {
		case <-ctx.Done():
			return
		default:
		}
		writeLine(fmt.Sprintf("[%s] === 新周期开始，尝试连接 ===", desktop.DesktopCode))
		header := http.Header{}
		header.Set("Origin", "https://pc.ctyun.cn")
		conn, _, err := dialer.Dial(uri, header)
		if err != nil {
			writeLine(fmt.Sprintf("[%s] 异常: %v", desktop.DesktopCode, err))
			time.Sleep(5 * time.Second)
			continue
		}
		sessionCtx, cancel := context.WithTimeout(ctx, 60*time.Minute)
		go func() {
			<-sessionCtx.Done()
			_ = conn.WriteControl(websocket.CloseMessage, websocket.FormatCloseMessage(websocket.CloseNormalClosure, "Timeout Reset"), time.Now().Add(2*time.Second))
			_ = conn.Close()
		}()
		connectMessage := map[string]any{
			"type":      1,
			"ssl":       1,
			"host":      strings.Split(desktop.DesktopInfo.ClinkLvsOutHost, ":")[0],
			"port":      strings.Split(desktop.DesktopInfo.ClinkLvsOutHost, ":")[1],
			"ca":        desktop.DesktopInfo.CaCert,
			"cert":      desktop.DesktopInfo.ClientCert,
			"key":       desktop.DesktopInfo.ClientKey,
			"servername": fmt.Sprintf("%s:%s", desktop.DesktopInfo.Host, desktop.DesktopInfo.Port),
			"oqs":       0,
		}
		connectBytes, _ := json.Marshal(connectMessage)
		_ = conn.WriteMessage(websocket.TextMessage, connectBytes)
		time.Sleep(500 * time.Millisecond)
		_ = conn.WriteMessage(websocket.BinaryMessage, initialPayload)
		writeLine(fmt.Sprintf("[%s] 连接已就绪，保持 60 秒...", desktop.DesktopCode))
		err = receiveLoop(sessionCtx, conn, desktop, api)
		cancel()
		_ = conn.Close()
		if err != nil {
			if websocket.IsCloseError(err, websocket.CloseNoStatusReceived) || strings.Contains(err.Error(), "1005") {
				writeLine(fmt.Sprintf("[%s] 警告: 连接被对端关闭(1005)，不影响脚本使用，准备重连", desktop.DesktopCode))
			} else if strings.Contains(err.Error(), "connection reset by peer") {
				writeLine(fmt.Sprintf("[%s] 警告: 连接被对端重置，不影响脚本使用，准备重连", desktop.DesktopCode))
			} else if !errors.Is(err, context.Canceled) && !errors.Is(err, context.DeadlineExceeded) {
				writeLine(fmt.Sprintf("[%s] 异常: %v", desktop.DesktopCode, err))
			}
		} else {
			writeLine(fmt.Sprintf("[%s] 60秒时间到，准备重连...", desktop.DesktopCode))
		}
		time.Sleep(5 * time.Second)
	}
}

func main() {
	writeLine("版本：v 1.0.0")
	userPhone, password, deviceCode := resolveCredentials()
	if userPhone == "" {
		return
	}
	api := NewCtYunApi(deviceCode)
	if !api.Login(userPhone, password) {
		return
	}
	if api.loginInfo != nil && !api.loginInfo.BondedDevice {
		api.GetSmsCode(userPhone)
		verificationCode := readLine("短信验证码: ")
		if !api.BindingDevice(verificationCode) {
			return
		}
	}
	desktops := api.GetClientList()
	active := []Desktop{}
	for _, d := range desktops {
		if d.UseStatusText != "运行中" {
			writeLine(fmt.Sprintf("[%s] [%s]电脑未开机，正在开机，请在2分钟后重新运行软件", d.DesktopCode, d.UseStatusText))
		}
		connectInfo, msg := api.Connect(d.DesktopId)
		if connectInfo != nil && connectInfo.DesktopInfo != nil {
			d.DesktopInfo = connectInfo.DesktopInfo
			active = append(active, d)
		} else {
			writeLine(fmt.Sprintf("Connect Error: [%s] %s", d.DesktopId, msg))
		}
	}
	if len(active) == 0 {
		return
	}
	writeLine("保活任务启动：每 60 秒强制重连一次。")
	ctx, cancel := context.WithCancel(context.Background())
	sigCh := make(chan os.Signal, 1)
	signal.Notify(sigCh, os.Interrupt, syscall.SIGTERM)
	go func() {
		<-sigCh
		cancel()
	}()
	var wg sync.WaitGroup
	for _, d := range active {
		wg.Add(1)
		go keepAliveWorker(ctx, d, api, &wg)
	}
	wg.Wait()
}

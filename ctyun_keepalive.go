package main

import (
	"bufio"
	"bytes"
	"context"
	"crypto/md5"
	"crypto/rand"
	"crypto/sha1"
	"crypto/sha256"
	"crypto/subtle"
	"crypto/tls"
	"encoding/base64"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"io/ioutil"
	"math/big"
	"mime/multipart"
	"net"
	"net/http"
	"net/url"
	"os"
	"os/signal"
	"strings"
	"sync"
	"syscall"
	"time"
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

type ResultLoginInfo struct {
	Code int       `json:"code"`
	Msg  string    `json:"msg"`
	Data LoginInfo `json:"data"`
}

type ResultChallengeData struct {
	Code int          `json:"code"`
	Msg  string       `json:"msg"`
	Data ChallengeData `json:"data"`
}

type ResultBool struct {
	Code int  `json:"code"`
	Msg  string `json:"msg"`
	Data bool `json:"data"`
}

type ResultClientInfo struct {
	Code int       `json:"code"`
	Msg  string    `json:"msg"`
	Data ClientInfo `json:"data"`
}

type ResultConnectInfo struct {
	Code int        `json:"code"`
	Msg  string     `json:"msg"`
	Data ConnectInfo `json:"data"`
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
	Salt     string    `json:"salt"`
	Accounts []Account `json:"accounts"`
}

var initialPayload []byte

func init() {
	initialPayload, _ = base64.StdEncoding.DecodeString("UkVEUQIAAAACAAAAGgAAAAAAAAABAAEAAAABAAAAEgAAAAkAAAAECAAA")
}

const (
	wsTextMessage   = 1
	wsBinaryMessage = 2
	wsCloseMessage  = 8
	wsPingMessage   = 9
	wsPongMessage   = 10
)

const (
	wsCloseNormalClosure   = 1000
	wsCloseNoStatusReceived = 1005
)

type wsCloseError struct {
	Code int
	Text string
}

func (e wsCloseError) Error() string {
	if e.Text == "" {
		return fmt.Sprintf("websocket close: %d", e.Code)
	}
	return fmt.Sprintf("websocket close: %d %s", e.Code, e.Text)
}

type WSConn struct {
	conn       net.Conn
	reader     *bufio.Reader
	writeMu    sync.Mutex
	readBuf    []byte
	messageBuf []byte
	maskBuf    []byte
}

func newWSConn(conn net.Conn) *WSConn {
	return &WSConn{
		conn:       conn,
		reader:     bufio.NewReader(conn),
		readBuf:    nil,
		messageBuf: nil,
		maskBuf:    nil,
	}
}

func dialWebSocket(uri, origin, subprotocol string) (*WSConn, *http.Response, error) {
	u, err := url.Parse(uri)
	if err != nil {
		return nil, nil, err
	}
	host := u.Host
	addr := host
	if !strings.Contains(host, ":") {
		if u.Scheme == "wss" {
			addr = host + ":443"
		} else {
			addr = host + ":80"
		}
	}
	var conn net.Conn
	if u.Scheme == "wss" {
		serverName := host
		if h, _, err := net.SplitHostPort(host); err == nil {
			serverName = h
		}
		conn, err = tls.Dial("tcp", addr, &tls.Config{ServerName: serverName})
	} else {
		conn, err = net.Dial("tcp", addr)
	}
	if err != nil {
		return nil, nil, err
	}
	keyBytes := make([]byte, 16)
	_, _ = rand.Read(keyBytes)
	key := base64.StdEncoding.EncodeToString(keyBytes)
	path := u.RequestURI()
	if path == "" {
		path = "/"
	}
	var request bytes.Buffer
	request.WriteString("GET " + path + " HTTP/1.1\r\n")
	request.WriteString("Host: " + host + "\r\n")
	request.WriteString("Upgrade: websocket\r\n")
	request.WriteString("Connection: Upgrade\r\n")
	request.WriteString("Sec-WebSocket-Key: " + key + "\r\n")
	request.WriteString("Sec-WebSocket-Version: 13\r\n")
	if origin != "" {
		request.WriteString("Origin: " + origin + "\r\n")
	}
	if subprotocol != "" {
		request.WriteString("Sec-WebSocket-Protocol: " + subprotocol + "\r\n")
	}
	request.WriteString("\r\n")
	if _, err = conn.Write(request.Bytes()); err != nil {
		_ = conn.Close()
		return nil, nil, err
	}
	reader := bufio.NewReader(conn)
	resp, err := http.ReadResponse(reader, &http.Request{Method: "GET"})
	if err != nil {
		_ = conn.Close()
		return nil, nil, err
	}
	if resp.StatusCode != http.StatusSwitchingProtocols {
		_ = conn.Close()
		return nil, resp, fmt.Errorf("websocket handshake failed: %s", resp.Status)
	}
	accept := resp.Header.Get("Sec-WebSocket-Accept")
	acceptKey := computeSHA1Base64(key + "258EAFA5-E914-47DA-95CA-C5AB0DC85B11")
	if accept != acceptKey {
		_ = conn.Close()
		return nil, resp, errors.New("websocket handshake validation failed")
	}
	return &WSConn{conn: conn, reader: reader}, resp, nil
}

func computeSHA1Base64(value string) string {
	sum := sha1.Sum([]byte(value))
	return base64.StdEncoding.EncodeToString(sum[:])
}

func (c *WSConn) ReadMessage() (int, []byte, error) {
	var messageOpcode int
	messageData := c.messageBuf[:0]
	for {
		fin, opcode, payload, err := c.readFrame()
		if err != nil {
			return 0, nil, err
		}
		switch opcode {
		case wsPingMessage:
			_ = c.writeFrame(wsPongMessage, payload)
			continue
		case wsPongMessage:
			continue
		case wsCloseMessage:
			code := wsCloseNoStatusReceived
			text := ""
			if len(payload) >= 2 {
				code = int(binary.BigEndian.Uint16(payload[:2]))
				if len(payload) > 2 {
					text = string(payload[2:])
				}
			}
			_ = c.writeFrame(wsCloseMessage, formatCloseMessage(code, text))
			return 0, nil, wsCloseError{Code: code, Text: text}
		case 0:
			if messageOpcode == 0 {
				continue
			}
			messageData = append(messageData, payload...)
			c.messageBuf = messageData
			if fin {
				return messageOpcode, messageData, nil
			}
		case wsTextMessage, wsBinaryMessage:
			if fin {
				return opcode, payload, nil
			}
			messageOpcode = opcode
			messageData = append(messageData, payload...)
			c.messageBuf = messageData
		}
	}
}

func (c *WSConn) WriteMessage(messageType int, data []byte) error {
	return c.writeFrame(messageType, data)
}

func (c *WSConn) WriteControl(messageType int, data []byte, _ time.Time) error {
	return c.writeFrame(messageType, data)
}

func (c *WSConn) Close() error {
	return c.conn.Close()
}

func (c *WSConn) readFrame() (bool, int, []byte, error) {
	var header [2]byte
	if _, err := io.ReadFull(c.reader, header[:]); err != nil {
		return false, 0, nil, err
	}
	b0 := header[0]
	b1 := header[1]
	fin := b0&0x80 != 0
	opcode := int(b0 & 0x0f)
	masked := b1&0x80 != 0
	payloadLen := int(b1 & 0x7f)
	if payloadLen == 126 {
		var ext [2]byte
		if _, err := io.ReadFull(c.reader, ext[:]); err != nil {
			return false, 0, nil, err
		}
		payloadLen = int(binary.BigEndian.Uint16(ext[:]))
	} else if payloadLen == 127 {
		var ext [8]byte
		if _, err := io.ReadFull(c.reader, ext[:]); err != nil {
			return false, 0, nil, err
		}
		length := binary.BigEndian.Uint64(ext[:])
		if length > uint64(^uint(0)>>1) {
			return false, 0, nil, errors.New("payload too large")
		}
		payloadLen = int(length)
	}
	var maskKey [4]byte
	if masked {
		if _, err := io.ReadFull(c.reader, maskKey[:]); err != nil {
			return false, 0, nil, err
		}
	}
	if cap(c.readBuf) < payloadLen {
		c.readBuf = make([]byte, payloadLen)
	}
	payload := c.readBuf[:payloadLen]
	if payloadLen > 0 {
		if _, err := io.ReadFull(c.reader, payload); err != nil {
			return false, 0, nil, err
		}
	}
	if masked {
		for i := 0; i < payloadLen; i++ {
			payload[i] ^= maskKey[i%4]
		}
	}
	return fin, opcode, payload, nil
}

func (c *WSConn) writeFrame(messageType int, data []byte) error {
	c.writeMu.Lock()
	defer c.writeMu.Unlock()
	var header [14]byte
	headerLen := 0
	header[0] = byte(0x80 | byte(messageType&0x0f))
	headerLen++
	payloadLen := len(data)
	maskBit := byte(0x80)
	if payloadLen < 126 {
		header[headerLen] = maskBit | byte(payloadLen)
		headerLen++
	} else if payloadLen <= 0xffff {
		header[headerLen] = maskBit | 126
		headerLen++
		binary.BigEndian.PutUint16(header[headerLen:headerLen+2], uint16(payloadLen))
		headerLen += 2
	} else {
		header[headerLen] = maskBit | 127
		headerLen++
		binary.BigEndian.PutUint64(header[headerLen:headerLen+8], uint64(payloadLen))
		headerLen += 8
	}
	var maskKey [4]byte
	_, _ = rand.Read(maskKey[:])
	copy(header[headerLen:headerLen+4], maskKey[:])
	headerLen += 4
	if cap(c.maskBuf) < payloadLen {
		c.maskBuf = make([]byte, payloadLen)
	}
	masked := c.maskBuf[:payloadLen]
	for i := 0; i < payloadLen; i++ {
		masked[i] = data[i] ^ maskKey[i%4]
	}
	if _, err := c.conn.Write(header[:headerLen]); err != nil {
		return err
	}
	if payloadLen > 0 {
		_, err := c.conn.Write(masked)
		return err
	}
	return nil
}

func formatCloseMessage(code int, text string) []byte {
	if code == 0 {
		return nil
	}
	buf := make([]byte, 2+len(text))
	binary.BigEndian.PutUint16(buf[0:2], uint16(code))
	copy(buf[2:], []byte(text))
	return buf
}

func isCloseError(err error, code int) bool {
	if err == nil {
		return false
	}
	if e, ok := err.(wsCloseError); ok {
		return e.Code == code
	}
	return false
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
	results := make([]SendInfo, 0, len(buffer)/6)
	if len(buffer) == 0 {
		return results
	}
	offset := 0
	for offset+6 <= len(buffer) {
		typeValue := int(binary.LittleEndian.Uint16(buffer[offset : offset+2]))
		dataLengthU := binary.LittleEndian.Uint32(buffer[offset+2 : offset+6])
		if dataLengthU > 0x7fffffff {
			remaining := len(buffer) - offset
			if remaining > 0 {
				results = append(results, SendInfo{Type: typeValue, Data: buffer[offset : offset+remaining]})
			}
			break
		}
		dataLength := int(dataLengthU)
		if offset+6+dataLength > len(buffer) {
			remaining := len(buffer) - offset
			if remaining > 0 {
				results = append(results, SendInfo{Type: typeValue, Data: buffer[offset : offset+remaining]})
			}
			break
		}
		var data []byte
		if dataLength > 0 {
			data = buffer[offset+6 : offset+6+dataLength]
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

func hasSendInfoType(buffer []byte, targetType int) bool {
	if len(buffer) == 0 {
		return false
	}
	offset := 0
	for offset+6 <= len(buffer) {
		typeValue := int(binary.LittleEndian.Uint16(buffer[offset : offset+2]))
		dataLengthU := binary.LittleEndian.Uint32(buffer[offset+2 : offset+6])
		if dataLengthU > 0x7fffffff {
			return false
		}
		dataLength := int(dataLengthU)
		if offset+6+dataLength > len(buffer) {
			return false
		}
		if typeValue == targetType {
			return true
		}
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
				return false
			}
		}
	}
	return false
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
	if len(e.buffers) == 0 {
		e.buffers = make([][]byte, 1)
	}
	if len(data) <= 16 {
		e.buffers[0] = e.buffers[0][:0]
		return
	}
	size := len(data) - 16
	if cap(e.buffers[0]) < size {
		e.buffers[0] = make([]byte, size)
	} else {
		e.buffers[0] = e.buffers[0][:size]
	}
	copy(e.buffers[0], data[16:])
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
	seedLen := len(seed)
	block := make([]byte, seedLen+4)
	copy(block, seed)
	for offset < maskLen {
		binary.BigEndian.PutUint32(block[seedLen:], uint32(counter))
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
		var result ResultLoginInfo
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
			var result ResultBool
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
	var result ResultBool
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
	var result ResultChallengeData
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
	payload := map[string]interface{}{
		"getCnt":        20,
		"desktopTypes":  []string{"1", "2001", "2002", "2003"},
		"sortType":      "createTimeV1",
	}
	var result ResultClientInfo
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
	var result ResultConnectInfo
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
	timestamp := fmt.Sprintf("%d", time.Now().UnixNano()/int64(time.Millisecond))
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
	bodyBytes, err := ioutil.ReadAll(resp.Body)
	if err != nil {
		return nil, err
	}
	if resp.StatusCode < 200 || resp.StatusCode >= 300 {
		return nil, fmt.Errorf("http status %d: %s", resp.StatusCode, strings.TrimSpace(string(bodyBytes)))
	}
	return bodyBytes, nil
}

func (api *CtYunApi) postJSON(urlStr string, payload interface{}, out interface{}) error {
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

func (api *CtYunApi) postForm(urlStr string, values url.Values, out interface{}) error {
	body := strings.NewReader(values.Encode())
	headers := map[string]string{"Content-Type": "application/x-www-form-urlencoded"}
	resp, err := api.request("POST", urlStr, body, headers, true)
	if err != nil {
		return err
	}
	return json.Unmarshal(resp, out)
}

func (api *CtYunApi) getJSON(urlStr string, out interface{}) error {
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

func getSystemFingerprint() string {
	interfaces, err := net.Interfaces()
	macAddress := "unknown"
	if err == nil {
		for _, iface := range interfaces {
			if len(iface.HardwareAddr) > 0 {
				macAddress = iface.HardwareAddr.String()
				break
			}
		}
	}
	hash := sha256.Sum256([]byte(macAddress))
	return hex.EncodeToString(hash[:])
}

func generateSalt() string {
	salt := make([]byte, 16)
	_, _ = rand.Read(salt)
	return hex.EncodeToString(salt)
}

func deriveKey(systemFingerprint, salt string) [32]byte {
	keyMaterial := systemFingerprint + "|" + salt
	return sha256.Sum256([]byte(keyMaterial))
}

func rotl32(v uint32, n uint) uint32 {
	return (v << n) | (v >> (32 - n))
}

func quarterRound(a, b, c, d uint32) (uint32, uint32, uint32, uint32) {
	a += b
	d ^= a
	d = rotl32(d, 16)
	c += d
	b ^= c
	b = rotl32(b, 12)
	a += b
	d ^= a
	d = rotl32(d, 8)
	c += d
	b ^= c
	b = rotl32(b, 7)
	return a, b, c, d
}

func chacha20Block(key [32]byte, counter uint32, nonce [12]byte) [64]byte {
	var state [16]uint32
	state[0] = 0x61707865
	state[1] = 0x3320646e
	state[2] = 0x79622d32
	state[3] = 0x6b206574
	state[4] = binary.LittleEndian.Uint32(key[0:4])
	state[5] = binary.LittleEndian.Uint32(key[4:8])
	state[6] = binary.LittleEndian.Uint32(key[8:12])
	state[7] = binary.LittleEndian.Uint32(key[12:16])
	state[8] = binary.LittleEndian.Uint32(key[16:20])
	state[9] = binary.LittleEndian.Uint32(key[20:24])
	state[10] = binary.LittleEndian.Uint32(key[24:28])
	state[11] = binary.LittleEndian.Uint32(key[28:32])
	state[12] = counter
	state[13] = binary.LittleEndian.Uint32(nonce[0:4])
	state[14] = binary.LittleEndian.Uint32(nonce[4:8])
	state[15] = binary.LittleEndian.Uint32(nonce[8:12])

	x := state
	for i := 0; i < 10; i++ {
		x[0], x[4], x[8], x[12] = quarterRound(x[0], x[4], x[8], x[12])
		x[1], x[5], x[9], x[13] = quarterRound(x[1], x[5], x[9], x[13])
		x[2], x[6], x[10], x[14] = quarterRound(x[2], x[6], x[10], x[14])
		x[3], x[7], x[11], x[15] = quarterRound(x[3], x[7], x[11], x[15])
		x[0], x[5], x[10], x[15] = quarterRound(x[0], x[5], x[10], x[15])
		x[1], x[6], x[11], x[12] = quarterRound(x[1], x[6], x[11], x[12])
		x[2], x[7], x[8], x[13] = quarterRound(x[2], x[7], x[8], x[13])
		x[3], x[4], x[9], x[14] = quarterRound(x[3], x[4], x[9], x[14])
	}
	for i := 0; i < 16; i++ {
		x[i] += state[i]
	}
	var out [64]byte
	for i := 0; i < 16; i++ {
		binary.LittleEndian.PutUint32(out[i*4:(i+1)*4], x[i])
	}
	return out
}

func chacha20XORKeyStream(dst, src []byte, key [32]byte, nonce [12]byte, counter uint32) {
	for len(src) > 0 {
		block := chacha20Block(key, counter, nonce)
		n := len(src)
		if n > 64 {
			n = 64
		}
		for i := 0; i < n; i++ {
			dst[i] = src[i] ^ block[i]
		}
		src = src[n:]
		dst = dst[n:]
		counter++
	}
}

func poly1305Sum(msg []byte, key [32]byte) [16]byte {
	r0 := uint64(key[0]) | uint64(key[1])<<8 | uint64(key[2])<<16 | uint64(key[3])<<24
	r1 := uint64(key[3])>>2 | uint64(key[4])<<6 | uint64(key[5])<<14 | uint64(key[6])<<22
	r2 := uint64(key[6])>>4 | uint64(key[7])<<4 | uint64(key[8])<<12 | uint64(key[9])<<20
	r3 := uint64(key[9])>>6 | uint64(key[10])<<2 | uint64(key[11])<<10 | uint64(key[12])<<18
	r4 := uint64(key[12])>>8 | uint64(key[13])<<0 | uint64(key[14])<<8 | uint64(key[15])<<16

	r0 &= 0x3ffffff
	r1 &= 0x3ffff03
	r2 &= 0x3ffc0ff
	r3 &= 0x3f03fff
	r4 &= 0x00fffff

	s1 := r1 * 5
	s2 := r2 * 5
	s3 := r3 * 5
	s4 := r4 * 5

	var h0, h1, h2, h3, h4 uint64

	offset := 0
	for offset < len(msg) {
		var block [16]byte
		n := len(msg) - offset
		if n > 16 {
			n = 16
		}
		copy(block[:], msg[offset:offset+n])
		var hibit uint64
		if n == 16 {
			hibit = 1 << 24
		} else {
			block[n] = 1
		}

		t0 := uint64(block[0]) | uint64(block[1])<<8 | uint64(block[2])<<16 | uint64(block[3])<<24
		t1 := uint64(block[3])>>2 | uint64(block[4])<<6 | uint64(block[5])<<14 | uint64(block[6])<<22
		t2 := uint64(block[6])>>4 | uint64(block[7])<<4 | uint64(block[8])<<12 | uint64(block[9])<<20
		t3 := uint64(block[9])>>6 | uint64(block[10])<<2 | uint64(block[11])<<10 | uint64(block[12])<<18
		t4 := uint64(block[12])>>8 | uint64(block[13])<<0 | uint64(block[14])<<8 | uint64(block[15])<<16

		h0 += t0 & 0x3ffffff
		h1 += t1 & 0x3ffffff
		h2 += t2 & 0x3ffffff
		h3 += t3 & 0x3ffffff
		h4 += (t4 & 0x3ffffff) + hibit

		d0 := h0*r0 + h1*s4 + h2*s3 + h3*s2 + h4*s1
		d1 := h0*r1 + h1*r0 + h2*s4 + h3*s3 + h4*s2
		d2 := h0*r2 + h1*r1 + h2*r0 + h3*s4 + h4*s3
		d3 := h0*r3 + h1*r2 + h2*r1 + h3*r0 + h4*s4
		d4 := h0*r4 + h1*r3 + h2*r2 + h3*r1 + h4*r0

		h0 = d0 & 0x3ffffff
		d1 += d0 >> 26
		h1 = d1 & 0x3ffffff
		d2 += d1 >> 26
		h2 = d2 & 0x3ffffff
		d3 += d2 >> 26
		h3 = d3 & 0x3ffffff
		d4 += d3 >> 26
		h4 = d4 & 0x3ffffff
		h0 += (d4 >> 26) * 5
		h1 += h0 >> 26
		h0 &= 0x3ffffff

		offset += n
	}

	h2 += h1 >> 26
	h1 &= 0x3ffffff
	h3 += h2 >> 26
	h2 &= 0x3ffffff
	h4 += h3 >> 26
	h3 &= 0x3ffffff
	h0 += (h4 >> 26) * 5
	h4 &= 0x3ffffff
	h1 += h0 >> 26
	h0 &= 0x3ffffff

	g0 := h0 + 5
	g1 := h1
	g2 := h2
	g3 := h3
	g4 := h4

	g1 += g0 >> 26
	g0 &= 0x3ffffff
	g2 += g1 >> 26
	g1 &= 0x3ffffff
	g3 += g2 >> 26
	g2 &= 0x3ffffff
	g4 += g3 >> 26
	g3 &= 0x3ffffff
	g4 -= 1 << 26

	if g4>>63 == 0 {
		h0, h1, h2, h3, h4 = g0, g1, g2, g3, g4
	}

	f0 := (h0 | (h1 << 26)) & 0xffffffff
	f1 := ((h1 >> 6) | (h2 << 20)) & 0xffffffff
	f2 := ((h2 >> 12) | (h3 << 14)) & 0xffffffff
	f3 := ((h3 >> 18) | (h4 << 8)) & 0xffffffff

	s0 := uint64(binary.LittleEndian.Uint32(key[16:20]))
	s1k := uint64(binary.LittleEndian.Uint32(key[20:24]))
	s2k := uint64(binary.LittleEndian.Uint32(key[24:28]))
	s3k := uint64(binary.LittleEndian.Uint32(key[28:32]))

	f0 += s0
	f1 += s1k + (f0 >> 32)
	f0 &= 0xffffffff
	f2 += s2k + (f1 >> 32)
	f1 &= 0xffffffff
	f3 += s3k + (f2 >> 32)
	f2 &= 0xffffffff
	f3 &= 0xffffffff

	var out [16]byte
	binary.LittleEndian.PutUint32(out[0:4], uint32(f0))
	binary.LittleEndian.PutUint32(out[4:8], uint32(f1))
	binary.LittleEndian.PutUint32(out[8:12], uint32(f2))
	binary.LittleEndian.PutUint32(out[12:16], uint32(f3))
	return out
}

func buildPoly1305Data(aad, ciphertext []byte) []byte {
	size := len(aad)
	if rem := size % 16; rem != 0 {
		size += 16 - rem
	}
	size += len(ciphertext)
	if rem := len(ciphertext) % 16; rem != 0 {
		size += 16 - rem
	}
	size += 16
	out := make([]byte, 0, size)
	out = append(out, aad...)
	if rem := len(aad) % 16; rem != 0 {
		out = append(out, make([]byte, 16-rem)...)
	}
	out = append(out, ciphertext...)
	if rem := len(ciphertext) % 16; rem != 0 {
		out = append(out, make([]byte, 16-rem)...)
	}
	var lens [16]byte
	binary.LittleEndian.PutUint64(lens[0:8], uint64(len(aad)))
	binary.LittleEndian.PutUint64(lens[8:16], uint64(len(ciphertext)))
	out = append(out, lens[:]...)
	return out
}

func chacha20poly1305Seal(key [32]byte, nonce [12]byte, plaintext []byte) []byte {
	block0 := chacha20Block(key, 0, nonce)
	var otk [32]byte
	copy(otk[:], block0[:32])
	ciphertext := make([]byte, len(plaintext))
	chacha20XORKeyStream(ciphertext, plaintext, key, nonce, 1)
	macData := buildPoly1305Data(nil, ciphertext)
	tag := poly1305Sum(macData, otk)
	out := make([]byte, 0, len(ciphertext)+16)
	out = append(out, ciphertext...)
	out = append(out, tag[:]...)
	return out
}

func chacha20poly1305Open(key [32]byte, nonce [12]byte, ciphertext []byte) ([]byte, error) {
	if len(ciphertext) < 16 {
		return nil, errors.New("invalid ciphertext")
	}
	data := ciphertext[:len(ciphertext)-16]
	tag := ciphertext[len(ciphertext)-16:]
	block0 := chacha20Block(key, 0, nonce)
	var otk [32]byte
	copy(otk[:], block0[:32])
	macData := buildPoly1305Data(nil, data)
	expected := poly1305Sum(macData, otk)
	if subtle.ConstantTimeCompare(tag, expected[:]) != 1 {
		return nil, errors.New("invalid ciphertext")
	}
	plaintext := make([]byte, len(data))
	chacha20XORKeyStream(plaintext, data, key, nonce, 1)
	return plaintext, nil
}

func encryptData(plaintext string, key [32]byte) (string, error) {
	nonce := make([]byte, 12)
	_, _ = rand.Read(nonce)
	var nonceArr [12]byte
	copy(nonceArr[:], nonce)
	ciphertext := chacha20poly1305Seal(key, nonceArr, []byte(plaintext))
	result := append(nonce, ciphertext...)
	return base64.StdEncoding.EncodeToString(result), nil
}

func decryptData(ciphertextB64 string, key [32]byte) (string, error) {
	data, err := base64.StdEncoding.DecodeString(ciphertextB64)
	if err != nil {
		return "", err
	}
	if len(data) < 12+16 {
		return "", errors.New("invalid ciphertext")
	}
	var nonce [12]byte
	copy(nonce[:], data[:12])
	ciphertext := data[12:]
	plaintext, err := chacha20poly1305Open(key, nonce, ciphertext)
	if err != nil {
		return "", err
	}
	return string(plaintext), nil
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

func decodeFirstAccount(accounts AccountsFile, systemFingerprint string) (string, string, string, bool) {
	if accounts.Salt == "" || len(accounts.Accounts) == 0 {
		return "", "", "", false
	}
	key := deriveKey(systemFingerprint, accounts.Salt)
	for _, account := range accounts.Accounts {
		user, errUser := decryptData(account.UserAccount, key)
		password, errPassword := decryptData(account.Password, key)
		deviceCode, errDevice := decryptData(account.DeviceCode, key)
		if errUser == nil && errPassword == nil && errDevice == nil && user != "" && deviceCode != "" {
			return user, password, deviceCode, true
		}
	}
	return "", "", "", false
}

func resolveCredentials() (string, string, string) {
	systemFingerprint := getSystemFingerprint()
	configFile := "config.json"
	for {
		var accounts AccountsFile
		if data, err := ioutil.ReadFile(configFile); err == nil {
			if err := json.Unmarshal(data, &accounts); err == nil {
				if user, password, deviceCode, ok := decodeFirstAccount(accounts, systemFingerprint); ok {
					return user, password, deviceCode
				}
				writeLine("config.json 解码失败，进入手动录入")
			} else {
				writeLine("解析 config.json 失败: " + err.Error())
			}
		}

		accounts = AccountsFile{
			Salt:     generateSalt(),
			Accounts: []Account{},
		}
		key := deriveKey(systemFingerprint, accounts.Salt)
		for {
			deviceCode := "web_" + generateRandomString(32)
			user := readLine("账号: ")
			password := readLine("密码: ")
			if user == "" || password == "" {
				writeLine("账号或密码不能为空")
				continue
			}

			encodedUser, errUser := encryptData(user, key)
			encodedPassword, errPassword := encryptData(password, key)
			encodedDeviceCode, errDevice := encryptData(deviceCode, key)
			if errUser != nil || errPassword != nil || errDevice != nil {
				writeLine("配置加密失败")
				continue
			}

			accounts.Accounts = append(accounts.Accounts, Account{
				UserAccount: encodedUser,
				Password:    encodedPassword,
				DeviceCode:  encodedDeviceCode,
			})

			continueInput := readLine("是否继续添加账户? (y/n): ")
			if strings.ToLower(strings.TrimSpace(continueInput)) != "y" {
				break
			}
		}

		if len(accounts.Accounts) == 0 {
			continue
		}
		data, _ := json.MarshalIndent(accounts, "", "  ")
		_ = ioutil.WriteFile(configFile, data, 0644)
		if user, password, deviceCode, ok := decodeFirstAccount(accounts, systemFingerprint); ok {
			return user, password, deviceCode
		}
		writeLine("配置写入后解码失败，重新录入")
	}
}

func receiveLoop(ctx context.Context, conn *WSConn, desktop Desktop, encryptor *Encryption, userPayload []byte) error {
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
		if len(message) >= 4 && message[0] == 'R' && message[1] == 'E' && message[2] == 'D' && message[3] == 'Q' {
			writeLine(fmt.Sprintf("[%s] -> 收到保活校验", desktop.DesktopCode))
			response := encryptor.Execute(message)
			err = conn.WriteMessage(wsBinaryMessage, response)
			if err == nil {
				writeLine(fmt.Sprintf("[%s] -> 发送保活响应成功", desktop.DesktopCode))
			}
			continue
		}
		if len(userPayload) > 0 && hasSendInfoType(message, 103) {
			_ = conn.WriteMessage(wsBinaryMessage, userPayload)
		}
	}
}

func keepAliveWorker(ctx context.Context, desktop Desktop, api *CtYunApi, userPayload []byte, wg *sync.WaitGroup) {
	defer wg.Done()
	uri := fmt.Sprintf("wss://%s/clinkProxy/%s/MAIN", desktop.DesktopInfo.ClinkLvsOutHost, desktop.DesktopId)
	encryptor := NewEncryption()
	host := desktop.DesktopInfo.Host
	port := desktop.DesktopInfo.Port
	if clinkHost := desktop.DesktopInfo.ClinkLvsOutHost; clinkHost != "" {
		parts := strings.SplitN(clinkHost, ":", 2)
		if len(parts) == 2 {
			host = parts[0]
			port = parts[1]
		} else {
			host = clinkHost
		}
	}
	connectMessage := map[string]interface{}{
		"type":      1,
		"ssl":       1,
		"host":      host,
		"port":      port,
		"ca":        desktop.DesktopInfo.CaCert,
		"cert":      desktop.DesktopInfo.ClientCert,
		"key":       desktop.DesktopInfo.ClientKey,
		"servername": fmt.Sprintf("%s:%s", desktop.DesktopInfo.Host, desktop.DesktopInfo.Port),
		"oqs":       0,
	}
	connectBytes, _ := json.Marshal(connectMessage)
	for {
		select {
		case <-ctx.Done():
			return
		default:
		}
		writeLine(fmt.Sprintf("[%s] === 新周期开始，尝试连接 ===", desktop.DesktopCode))
		conn, _, err := dialWebSocket(uri, "https://pc.ctyun.cn", "binary")
		if err != nil {
			writeLine(fmt.Sprintf("[%s] 异常: %v", desktop.DesktopCode, err))
			time.Sleep(5 * time.Second)
			continue
		}
		sessionCtx, cancel := context.WithTimeout(ctx, 60*time.Second)
		go func() {
			<-sessionCtx.Done()
			_ = conn.WriteControl(wsCloseMessage, formatCloseMessage(wsCloseNormalClosure, "Timeout Reset"), time.Now().Add(2*time.Second))
			_ = conn.Close()
		}()
		_ = conn.WriteMessage(wsTextMessage, connectBytes)
		time.Sleep(500 * time.Millisecond)
		_ = conn.WriteMessage(wsBinaryMessage, initialPayload)
		writeLine(fmt.Sprintf("[%s] 连接已就绪，保持 60 秒...", desktop.DesktopCode))
		err = receiveLoop(sessionCtx, conn, desktop, encryptor, userPayload)
		cancel()
		_ = conn.Close()
		if err != nil {
			if isCloseError(err, wsCloseNoStatusReceived) || strings.Contains(err.Error(), "1005") {
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
	var userPayload []byte
	if api.loginInfo != nil {
		userJson, _ := json.Marshal(map[string]interface{}{
			"type":     1,
			"userName": api.loginInfo.UserName,
			"userInfo": "",
			"userId":   api.loginInfo.UserId,
		})
		userPayload = SendInfo{Type: 118, Data: userJson}.ToBuffer(true)
	}
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
		go keepAliveWorker(ctx, d, api, userPayload, &wg)
	}
	wg.Wait()
}

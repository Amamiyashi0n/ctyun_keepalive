# CtYun 云桌面保活脚本

天翼云桌面连接保活工具

## 快速开始

### Python 版本

```bash
pip install websockets
python ctyun_keepalive.py
```

### Go 版本

运行：
```bash
go mod init ctyun_keepalive
go env -w GOPROXY=https://goproxy.cn,direct
go mod tidy
go run ctyun_keepalive.go
```

## 版本

v 1.0.0

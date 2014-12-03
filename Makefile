
gofdupes: gofdupes.go
	go build -ldflags "-X main.BUILDTIME '`date`'"

install: gofdupes
	cp gofdupes ~/bin

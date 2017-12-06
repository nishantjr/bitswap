all: bitswap-protocol.pdf

%.pdf: %.md
	pandoc --filter panpipe -t latex $^ -o $@

.PHONEY: all

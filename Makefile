all: bitswap-protocol.pdf

%.pdf: %.md
	pandoc --filter panpipe -t latex $^ -o $@ --variable geometry:'margin=2cm'

.PHONEY: all

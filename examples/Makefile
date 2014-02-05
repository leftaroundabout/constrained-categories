SHELL=bash

all: $(foreach hs, $(shell ls *.hs), $(hs)-stdout.txt)
.PHONY: all

%.hs-stdout.txt : %.hs
	set -o pipefail; runhaskell $< | tee $@



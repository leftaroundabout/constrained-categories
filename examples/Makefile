SHELL=bash

all: $(foreach hs, $(shell ls *.hs), $(hs)-stdout.txt)
.PHONY: all
.DELETE_ON_ERROR: all

%.hs-stdout.txt : %.hs
	set -o pipefail; runhaskell $< | tee $@



SOURCES := $(shell find . -type f -name '*.agda')

all: $(SOURCES)
	for file in $^ ; do \
		agda -c --no-main --ghc-flag=-dynamic $${file} ; \
	done

.PHONY: clean
clean:
	rm -rf src/MAlonzo
	rm -rf _build

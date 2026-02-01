ALEX 	= alex
HAPPY	= happy
CABAL 	= cabal

CORE_LEXER_IN	= src/Core/Parser/Lexer.x
CORE_LEXER_OUT	= src/Core/Parser/Lexer.hs
CORE_PARSER_IN 	= src/Core/Parser/Parser.y
CORE_PARSER_OUT = src/Core/Parser/Parser.hs

ENVML_LEXER_IN  = src/EnvML/Parser/Lexer.x
ENVML_LEXER_OUT = src/EnvML/Parser/Lexer.hs
ENVML_PARSER_IN = src/EnvML/Parser/Parser.y
ENVML_PARSER_OUT= src/EnvML/Parser/Parser.hs

GEN_FILES = $(CORE_LEXER_OUT) $(ENVML_LEXER_OUT) $(CORE_PARSER_OUT) $(ENVML_PARSER_OUT)

.PHONY: all generate clean build test

# Removed 'clean' from here so it only runs when you want it to
all: build test

build: generate
ifdef CLEAN
	@echo "Performing clean build..."
	$(CABAL) clean
endif
	$(CABAL) build

generate: $(GEN_FILES)

test: build
	$(CABAL) test

# FIXED: Target is the .hs file, Prerequisite is the .x/.y file
$(CORE_LEXER_OUT): $(CORE_LEXER_IN)
	$(ALEX) $< -o $@

$(ENVML_LEXER_OUT): $(ENVML_LEXER_IN)
	$(ALEX) $< -o $@

$(CORE_PARSER_OUT): $(CORE_PARSER_IN)
	$(HAPPY) $< -o $@

$(ENVML_PARSER_OUT): $(ENVML_PARSER_IN)
	$(HAPPY) $< -o $@

clean:
	$(CABAL) clean
	rm -f $(GEN_FILES)
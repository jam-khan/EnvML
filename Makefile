
ALEX 	= alex
HAPPY	= happy
CABAL 	= cabal

CORE_LEXER_IN	= src/CoreForAll/Parser/Lexer.x
CORE_LEXER_OUT	= src/CoreForAll/Parser/Lexer.hs
CORE_PARSER_IN 	= src/CoreForAll/Parser/Parser.y
CORE_PARSER_OUT = src/CoreForAll/Parser/Parser.hs

ENVML_LEXER_IN  = src/EnvML/Parser/HappyAlex/Lexer.x
ENVML_LEXER_OUT = src/EnvML/Parser/HappyAlex/Lexer.hs
ENVML_PARSER_IN = src/EnvML/Parser/HappyAlex/Parser.y
ENVML_PARSER_OUT= src/EnvML/Parser/HappyAlex/Parser.hs

GEN_FILES = $(CORE_LEXER_OUT) $(ENVML_LEXER_OUT) $(CORE_PARSER_OUT) $(ENVML_PARSER_OUT)

.PHONY: all generate clean build test

all: generate clean build test

# Generate lexers and parsers
generate: $(GEN_FILES)

$(CORE_LEXER_IN)   :$(CORE_LEXER_OUT)
	$(ALEX) $< -o $@
$(ENVML_LEXER_IN)  :$(ENVML_LEXER_OUT)
	$(ALEX) $< -o $@
$(CORE_PARSER_IN)  :$(CORE_PARSER_OUT)
	$(HAPPY) $< -o $@
$(ENVML_PARSER_IN) :$(ENVML_PARSER_OUT)
	$(HAPPY) $< -o $@

clean:
	$(CABAL) clean

build: generate
	$(CABAL) build

test: build
	$(CABAL) test
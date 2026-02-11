ALEX 	= alex
HAPPY	= happy
CABAL 	= cabal
GHC_WASM = wasm32-wasi-ghc

CORE_LEXER_IN	= src/CoreFE/Parser/Lexer.x
CORE_LEXER_OUT	= src/CoreFE/Parser/Lexer.hs
CORE_PARSER_IN 	= src/CoreFE/Parser/Parser.y
CORE_PARSER_OUT = src/CoreFE/Parser/Parser.hs
CORE_PARSER_INFO = src/CoreFE/Parser/Parser.info

ENVML_LEXER_IN  = src/EnvML/Parser/Lexer.x
ENVML_LEXER_OUT = src/EnvML/Parser/Lexer.hs
ENVML_PARSER_IN = src/EnvML/Parser/Parser.y
ENVML_PARSER_OUT= src/EnvML/Parser/Parser.hs
ENVML_PARSER_INFO = src/EnvML/Parser/Parser.info

WASM_SRC = src/WASM.hs
WASM_OUT = docs/WASM.wasm

GEN_FILES = $(CORE_LEXER_OUT) $(ENVML_LEXER_OUT) $(CORE_PARSER_OUT) $(ENVML_PARSER_OUT)
INFO_FILES = $(CORE_PARSER_INFO) $(ENVML_PARSER_INFO)

.PHONY: all generate clean build test info wasm

# Removed 'clean' from here so it only runs when you want it to
all: build test

build: generate
ifdef CLEAN
	@echo "Performing clean build..."
	$(CABAL) clean
endif
	$(CABAL) build

generate: $(GEN_FILES)

# Generate parser info files for debugging conflicts
info: $(INFO_FILES)

test: build
	$(CABAL) test

# WASM build - run with WASM=1 make wasm
wasm: generate
ifndef WASM
	$(error WASM build requires WASM=1 flag. Run: make wasm WASM=1)
endif
	@mkdir -p docs
	$(GHC_WASM) \
		-isrc \
		-no-hs-main \
		-optl-Wl,--export=setup \
		-optl-Wl,--export=runParse \
		-optl-Wl,--export=runElaborate \
		-optl-Wl,--export=runDeBruijn \
		-optl-Wl,--export=runCheck \
		-optl-Wl,--export=runEval \
		-optl-Wl,--export=runFull \
		-optl-Wl,--export=coreParseExp \
		-optl-Wl,--export=coreCheck \
		-optl-Wl,--export=coreEval \
		-optl-Wl,--export=coreRun \
		-optl-mexec-model=reactor \
		-o $(WASM_OUT) \
		$(WASM_SRC)

# FIXED: Target is the .hs file, Prerequisite is the .x/.y file
$(CORE_LEXER_OUT): $(CORE_LEXER_IN)
	$(ALEX) $< -o $@

$(ENVML_LEXER_OUT): $(ENVML_LEXER_IN)
	$(ALEX) $< -o $@

$(CORE_PARSER_OUT): $(CORE_PARSER_IN)
	$(HAPPY) $< -o $@

$(ENVML_PARSER_OUT): $(ENVML_PARSER_IN)
	$(HAPPY) $< -o $@

$(CORE_PARSER_INFO): $(CORE_PARSER_IN)
	$(HAPPY) -i $< -o $(CORE_PARSER_OUT)

$(ENVML_PARSER_INFO): $(ENVML_PARSER_IN)
	$(HAPPY) -i $< -o $(ENVML_PARSER_OUT)

clean:
	$(CABAL) clean
	rm -f $(GEN_FILES) $(INFO_FILES) $(WASM_OUT)
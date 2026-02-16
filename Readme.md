# EnvML - First-Class Environments Playground

A language implementation featuring first-class environments with a multi-stage compilation pipeline and interactive WASM playground.

## Table of Contents
- [Prerequisites](#prerequisites)
- [Quick Start](#quick-start)
- [WASM Playground](#wasm-playground)
- [Building from Source](#building-from-source)
- [Development](#development)

---

## Prerequisites

### Required Tools

1. **GHC (Glasgow Haskell Compiler)**
   ```bash
   # Install via GHCup (recommended)
   curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh
   
   # Verify installation
   ghc --version  # Should be >= 9.4
   ```

2. **Cabal**
   ```bash
   # Usually installed with GHC via GHCup
   cabal --version  # Should be >= 3.0
   ```

3. **Alex** (Lexer generator)
   ```bash
   cabal install alex
   ```

4. **Happy** (Parser generator)
   ```bash
   cabal install happy
   ```

5. **Make**
   ```bash
   # macOS
   xcode-select --install
   
   # Ubuntu/Debian
   sudo apt-get install build-essential
   
   # Verify
   make --version
   ```

### Optional (for WASM builds)

6. **GHC WASM Backend**
   ```bash
   # Install via GHCup
   ghcup install ghc --set 9.14.1.20251219
   ghcup install wasm32-wasi-ghc
   ```

---

## Quick Start

### 1. Clone and Setup
```bash
git clone <repository-url>
cd EnvML
```

### 2. Build the Project
```bash
# Generate lexer and parser files, then build
make

# Or with a clean build
make build CLEAN=1
```

### 3. Run Tests
```bash
make test
```

### 4. Run the REPL
```bash
cabal run EnvML
```

---

## WASM Playground

The WASM playground provides an interactive web interface to explore EnvML's compilation pipeline.

### Pre-built Playground (Recommended)

The playground is already set up in the `docs/` directory with:
- `docs/WASM.wasm` - Compiled WASM module
- `docs/index.html` - Web interface
- `docs/ghc_wasm_jsffi.js` - JavaScript FFI bindings

#### Running the Playground

**Option 1: VS Code Live Server (Recommended)**

1. Install the **Live Server** extension in VS Code
   - Open VS Code Extensions (Ctrl+Shift+X / Cmd+Shift+X)
   - Search for "Live Server" by Ritwick Dey
   - Click Install

2. Navigate to `docs/index.html` in VS Code

3. Right-click on `index.html` and select **"Open with Live Server"**

4. The playground will open in your default browser at `http://localhost:5500/docs/`

**Option 2: Python HTTP Server**
```bash
cd docs
python3 -m http.server 8000

# Visit http://localhost:8000 in your browser
```

**Option 3: Node.js HTTP Server**
```bash
cd docs
npx http-server -p 8000

# Visit http://localhost:8000 in your browser
```

### Playground Features

- **Two Modes:**
  - **EnvML** - Write and execute EnvML source code
  - **Core FE** - Write and execute Core FE expressions directly

- **Display Options:**
  - **Detailed** - Shows full AST with all internal representations
  - **Simplified** - Shows user-friendly, readable output (default)

- **Pipeline Stages:**
  - **Parse** - View the parsed AST
  - **Elaborate** - See the elaborated Named CoreFE AST
  - **De Bruijn** - View the De Bruijn indexed AST
  - **Check** - Type check the program
  - **Eval** - Evaluate and see results

- **Pre-loaded Examples** - Select from dropdown to explore language features

### Rebuilding WASM (Advanced)

If you modify the source and need to rebuild the WASM module:

```bash
# Requires wasm32-wasi-ghc installation
make wasm WASM=1

# The updated WASM.wasm will be in docs/
```

---

## Building from Source

### Makefile Targets

```bash
# Generate lexer/parser files + build project
make

# Build with clean (removes all build artifacts first)
make build CLEAN=1

# Generate only lexer and parser files
make generate

# Run tests
make test

# Generate parser info files (for debugging shift/reduce conflicts)
make info

# Build WASM module (requires wasm32-wasi-ghc)
make wasm WASM=1

# Clean all generated files and build artifacts
make clean
```

### Manual Build Steps

If you prefer not to use the Makefile:

```bash
# 1. Generate lexers
alex src/CoreFE/Parser/Lexer.x -o src/CoreFE/Parser/Lexer.hs
alex src/EnvML/Parser/Lexer.x -o src/EnvML/Parser/Lexer.hs

# 2. Generate parsers
happy src/CoreFE/Parser/Parser.y -o src/CoreFE/Parser/Parser.hs
happy src/EnvML/Parser/Parser.y -o src/EnvML/Parser/Parser.hs

# 3. Build with Cabal
cabal build

# 4. Run tests
cabal test

# 5. Run REPL
cabal run EnvML
```

---

## Development

### Project Structure

```
EnvML/
├── src/
│   ├── EnvML/           # EnvML language implementation
│   │   ├── Syntax.hs    # AST definitions
│   │   ├── Elab.hs      # Elaboration to CoreFE
│   │   └── Parser/      # Lexer and parser
│   ├── CoreFE/          # Core FE calculus
│   │   ├── Syntax.hs    # Core AST (De Bruijn)
│   │   ├── Named.hs     # Named Core AST
│   │   ├── Check.hs     # Type checker
│   │   ├── Eval.hs      # Evaluator
│   │   └── Parser/      # Core FE parser
│   ├── PrettyWeb.hs     # Web-friendly pretty printing
│   ├── WASM.hs          # WASM FFI exports
│   └── Utils.hs         # Utility functions
├── app/
│   └── Main.hs          # REPL entry point
├── test/                # Test suite
├── docs/                # WASM playground
└── Makefile
```

### Common Development Tasks

**Adding a new example to the playground:**

Edit `docs/index.html` and add to the `envmlExamples` or `coreExamples` array:

```javascript
{ 
  id: "e12", 
  label: "Your Example Name",
  code: `your code here`
}
```

**Modifying the compilation pipeline:**

1. Edit source files in `src/EnvML/` or `src/CoreFE/`
2. Rebuild: `make`
3. Test: `make test`
4. For WASM: `make wasm WASM=1`

**Debugging parser conflicts:**

```bash
# Generate .info files showing shift/reduce conflicts
make info

# Check the .info files
cat src/EnvML/Parser/Parser.info
cat src/CoreFE/Parser/Parser.info
```

---

## Troubleshooting

### "alex: command not found" or "happy: command not found"
```bash
cabal install alex
cabal install happy

# Add ~/.cabal/bin to PATH if needed
export PATH="$HOME/.cabal/bin:$PATH"
```

### WASM build fails with "wasm32-wasi-ghc: command not found"
```bash
# Install GHC WASM backend
ghcup install wasm32-wasi-ghc
```

### Playground doesn't load in browser
- Make sure you're using a local server (not `file://`)
- Check browser console for errors
- Verify `WASM.wasm` and `ghc_wasm_jsffi.js` are in the same directory as `index.html`

### Cabal build fails with dependency errors
```bash
# Update package index
cabal update

# Clean and rebuild
make clean
make
```

---

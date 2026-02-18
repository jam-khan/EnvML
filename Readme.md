# EnvML - First-Class Environments Playground

A language implementation featuring first-class environments with a multi-stage compilation pipeline and interactive WASM playground.

## Table of Contents
- [WASM Playground (No Setup Required)](#wasm-playground-no-setup-required)
- [Building from Source](#building-from-source)

---

## WASM Playground (No Setup Required)

The WASM playground provides an interactive web interface to explore EnvML's compilation pipeline without any installation.

### Running the Playground

The playground is pre-built and ready to use in the `docs/` directory. You can serve it locally using either VS Code Live Server or a Python HTTP server.

**1) Using VS Code Live Server:**

1. Install the **Live Server** extension in VS Code
   - Open VS Code Extensions (Ctrl+Shift+X / Cmd+Shift+X)
   - Search for "Live Server"
   - Click Install

2. Navigate to `docs/index.html` in VS Code

3. Right-click on `index.html` and select **"Open with Live Server"**

4. The playground will open in your default browser at `http://localhost:5500/docs/index.html`

**2) Python HTTP Server:**
```bash
cd docs
python3 -m http.server 8000
# Visit http://localhost:8000 in your browser
```

### Playground Features

- **Two Modes:**
  - **EnvML** - Write and execute EnvML source code
  - **Core FE** - Write and execute Core FE expressions directly

- **Display Options:**
  - **Detailed** - Shows full AST with all internal representations (default)
  - **Simplified** - Shows user-friendly, readable output

- **Pipeline Stages:**
  - **Parse** - View the parsed AST
  - **Elaborate** - See the elaborated Named CoreFE AST
  - **De Bruijn** - View the De Bruijn indexed AST
  - **Check** - Type check the program
  - **Eval** - Evaluate and see results

- **Pre-loaded Examples** - Select from dropdown to explore language features

---

## Building from Source

### Prerequisites

Install `make` to build and run the project:

```bash
# macOS
xcode-select --install

# Ubuntu/Debian
sudo apt-get install build-essential

# Verify
make --version
```

**Note:** The build process requires GHC and Cabal. If you don't have them installed:

- **GHC Installation:** Follow the instructions at https://www.haskell.org/ghcup/install/
- **Cabal Setup:** See the getting started guide at https://cabal.readthedocs.io/en/stable/getting-started.html
- **Alex and Happy:** These are used for lexer and parser generation. Install them with:
  ```bash
  cabal install alex
  cabal install happy
  ```

### Build and Run

```bash
# 1. Generate lexer/parser files and build the project
make

# 2. Run tests
make test

# 3. Run the REPL
cabal run
```

That's it! The `make` command handles all lexer and parser generation automatically.

### Makefile Targets

```bash
# Build project (generates parsers/lexers automatically)
make

# Build with clean (removes all build artifacts first)
make build CLEAN=1

# Run tests
make test

# Clean all generated files and build artifacts
make clean
```

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
│   └── Utils.hs         # Utility functions
├── app/
│   └── Main.hs          # REPL entry point
├── test/                # Test suite
├── docs/                # WASM playground (pre-built)
└── Makefile
```

---

## Troubleshooting

### Build fails with missing tools
```bash
# Install GHCup if not already installed
# See: https://www.haskell.org/ghcup/install/

# Install Alex and Happy
cabal install alex
cabal install happy

# Add to PATH if needed
export PATH="$HOME/.cabal/bin:$PATH"
```

### Cabal build fails with dependency errors
```bash
# Update package index
cabal update

# Clean and rebuild
make clean
make
```

### Playground doesn't load in browser
- Make sure you're using a local server (not `file://`)
- Check browser console for errors
- Verify `WASM.wasm` and `ghc_wasm_jsffi.js` are in `docs/` directory
# Strong Robertson conjecture for split-off minors

A Lean 4 formalization of the strong Robertson conjecture for split-off
minors. The project is pinned to Lean **4.32.1** and uses Mathlib **v4.32.1**
as a Git submodule.

## Prerequisites

- Git
- [VS Code](https://code.visualstudio.com/) with the official
  [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)
- `elan`, the Lean toolchain manager

Do not install `lean` or `lake` separately. `elan` reads `lean-toolchain` in
this repository and installs the exact Lean version automatically.

## Install on macOS

1. Open Terminal and ensure the Xcode Command Line Tools (including Git) are
   installed:

   ```sh
   git --version
   ```

   If macOS prompts you to install the tools, accept the prompt.

2. Install `elan`:

   ```sh
   curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
   source "$HOME/.elan/env"
   ```

3. Install VS Code, then install the official Lean extension. If you use
   Homebrew, both can be installed with:

   ```sh
   brew install --cask visual-studio-code
   code --install-extension leanprover.lean4
   ```

The same Lean binaries support both Apple Silicon and Intel Macs.

## Install on Windows

1. Install [Git for Windows](https://git-scm.com/download/win) and
   [VS Code](https://code.visualstudio.com/). In the installers, enable the
   option to add each program to `PATH`, then open a new PowerShell window.

2. Download and run the `elan` installer:

   ```powershell
   curl.exe -O --location https://elan.lean-lang.org/elan-init.ps1
   powershell -ExecutionPolicy Bypass -File .\elan-init.ps1
   Remove-Item .\elan-init.ps1
   ```

   Choose the default installation when prompted, then close and reopen
   PowerShell.

3. In VS Code, open Extensions (`Ctrl+Shift+X`) and install **Lean 4** by
   `leanprover`, or run:

   ```powershell
   code --install-extension leanprover.lean4
   ```

Native Windows is supported; WSL is not required.

## Clone and build

Clone with the Mathlib submodule:

```sh
git clone --recurse-submodules <repository-url>
cd strong-robertson-conjecture-for-split-off-minors
```

If the repository was already cloned without submodules, run:

```sh
git submodule update --init --recursive
```

Check the pinned toolchain, download Mathlib's precompiled cache, and build:

```sh
lean --version
lake exe cache get
lake build
```

The first command may take a few minutes while `elan` downloads Lean 4.32.1.
The cache command avoids compiling all of Mathlib from source. Open the
repository root in VS Code (`code .`) so the Lean extension can find
`lean-toolchain` and `lakefile.toml`.

## Project layout

- `StrongRobertson/` — formalization source files
- `StrongRobertson.lean` — root library import
- `mathlib/` — pinned Mathlib Git submodule
- `lean-toolchain` — pinned Lean compiler version
- `lakefile.toml` — Lake package configuration

## Updating the pinned dependency

Lean and Mathlib versions must stay compatible. To update, check out a matching
Mathlib release inside the submodule, update `lean-toolchain` to the version in
`mathlib/lean-toolchain`, regenerate the Lake manifest, and rebuild. Commit both
the changed submodule pointer and the toolchain/configuration files.

For current installation guidance, see the
[official Lean installation page](https://lean-lang.org/install/).

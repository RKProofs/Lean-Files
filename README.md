# Lean code corresponding to work on SSP bounds for Runge–Kutta methods

## paper: A stability order barrier and SSP bound for Runge–Kutta methods
with non-negative coefficients: AI assisted proofs

---

## Installing Lean and building the code

### Prerequisites

This project uses **Lean 4** (`leanprover/lean4:v4.32.0-rc1`) and depends on
[Mathlib](https://github.com/leanprover-community/mathlib4).  The recommended
way to install Lean is via **elan**, the Lean version manager.

#### Install elan

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Follow the on-screen prompts, then open a new shell (or run `source ~/.profile`)
so that `elan` and `lake` are on your `PATH`.

The correct Lean version is pinned in `lean-toolchain`; elan will download it
automatically the first time you build.

### Building

```bash
# Clone the repository (if you haven't already)
git clone <repo-url>
cd Lean-Files

# Download Mathlib and all other dependencies
lake exe cache get

# Build the project
lake build
```

`lake exe cache get` fetches pre-compiled Mathlib `.olean` files so you do not
have to recompile Mathlib from source (which can take hours).

### Editor support

[VS Code](https://code.visualstudio.com/) with the
[lean4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)
is the most common editor setup.  The extension calls `elan` and `lake`
automatically, so opening the repository folder is sufficient to get
interactive proof checking.

Emacs users can use [lean4-mode](https://github.com/leanprover/lean4-mode).

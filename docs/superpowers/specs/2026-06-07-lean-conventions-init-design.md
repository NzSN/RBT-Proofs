# Initialize repo with Lean 4 community conventions

**Date:** 2026-06-07
**Status:** approved

## Goal

Bring the RBT-Proofs skeleton repo into alignment with Lean 4 community conventions for a new proof project. Keep it minimal — no CI, no tooling beyond what Lean/Lake provide.

## Changes

### 1. `lean-toolchain`

Pin to a specific stable version instead of the generic `leanprover/lean4:stable`:

```
leanprover/lean4:v4.30.0
```

### 2. `lakefile.lean`

Add an explicit version to the `require mathlib` line so builds are reproducible:

```lean
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0"
```

### 3. `.gitignore`

Add missing Lean build and editor artifacts:

```
.lake/
lake-packages/
build/
*.olean
*.ilean
*.trace
.lake-packages/
*.log
*.cache
.envrc
```

(Current `.gitignore` already covers most of these; merge and deduplicate.)

### 4. `README.md`

Replace the one-liner with a proper project README including:
- Project description
- Build instructions (`lake build`)
- License line

### 5. `RBTProofs/Basic.lean`

Replace the bare comment with a proper module docstring:

```lean
/-!
# Basic definitions for Red-Black Trees

Definitions and inductive types for Red-Black Trees.
-/
```

## What stays the same

- Module structure: `RBTProofs.lean` root → `RBTProofs/Basic.lean`
- No new files, directories, scripts, CI, or developer tooling

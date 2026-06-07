# Initialize repo with Lean 4 conventions — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Bring the RBT-Proofs skeleton repo into alignment with Lean 4 community conventions (pinned versions, proper .gitignore, README, module docstring).

**Architecture:** Five single-file edits to the skeleton repo. No new files. No dependencies between tasks — each can be done independently.

**Tech Stack:** Lean 4 (v4.30.0), mathlib4 (v4.30.0)

---

### Task 1: Pin lean-toolchain to specific version

**Files:**
- Modify: `lean-toolchain`

- [ ] **Step 1: Update lean-toolchain**

Replace the contents of `lean-toolchain`:

```
leanprover/lean4:v4.30.0
```

- [ ] **Step 2: Verify**

Run: `cat lean-toolchain`
Expected: `leanprover/lean4:v4.30.0`

- [ ] **Step 3: Commit**

```bash
git add lean-toolchain
git commit -m "chore: pin lean-toolchain to v4.30.0"
```

---

### Task 2: Pin mathlib4 version in lakefile.lean

**Files:**
- Modify: `lakefile.lean`

- [ ] **Step 1: Update mathlib require line**

In `lakefile.lean`, change line 9-10 from:

```lean
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
```

to:

```lean
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0"
```

- [ ] **Step 2: Verify**

Run: `cat lakefile.lean`
Expected: The `require mathlib` line ends with `@ "v4.30.0"`

- [ ] **Step 3: Commit**

```bash
git add lakefile.lean
git commit -m "chore: pin mathlib4 to v4.30.0"
```

---

### Task 3: Complete .gitignore

**Files:**
- Modify: `.gitignore`

- [ ] **Step 1: Replace .gitignore**

Replace the entire content of `.gitignore`:

```
/.agent-shell/
/.lake/
/lake-packages/
/build/
*.olean
*.ilean
*.trace
.lake-packages/
*.log
*.cache
.envrc
```

- [ ] **Step 2: Verify**

Run: `cat .gitignore`
Expected: 11 lines, includes the new entries `.lake-packages/`, `*.log`, `*.cache`, `.envrc`

- [ ] **Step 3: Commit**

```bash
git add .gitignore
git commit -m "chore: add missing Lean build artifacts to .gitignore"
```

---

### Task 4: Write proper README.md

**Files:**
- Modify: `README.md`

- [ ] **Step 1: Replace README.md**

Replace the entire content of `README.md`:

```markdown
# RBT Proofs

Formal verification of Red-Black Tree properties using the [Lean 4](https://lean-lang.org/) theorem prover.

## Build

```bash
lake build
```

## License

MIT
```

- [ ] **Step 2: Verify**

Run: `cat README.md`
Expected: Contains project description, build instructions, and license line.

- [ ] **Step 3: Commit**

```bash
git add README.md
git commit -m "docs: write proper README with build instructions"
```

---

### Task 5: Add module docstring to Basic.lean

**Files:**
- Modify: `RBTProofs/Basic.lean`

- [ ] **Step 1: Replace Basic.lean**

Replace the entire content of `RBTProofs/Basic.lean`:

```lean
/-!
# Basic definitions for Red-Black Trees

Definitions and inductive types for Red-Black Trees.
-/
```

- [ ] **Step 2: Verify**

Run: `cat RBTProofs/Basic.lean`
Expected: Module docstring using `/-! ... -/` syntax.

- [ ] **Step 3: Commit**

```bash
git add RBTProofs/Basic.lean
git commit -m "docs: add module docstring to Basic.lean"
```

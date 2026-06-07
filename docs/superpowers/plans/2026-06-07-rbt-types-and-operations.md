# Red-Black Tree Types and Operations — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Define Red-Black Tree inductive types plus `insert`/`delete` with balancing in `RBTProofs/Basic.lean`.

**Architecture:** Single file, sequential tasks (each builds on the last). Classic Okasaki-style RBT with `Color` and `RBTree α` inductives, then insertion (balance + ins + insert), then deletion helpers (balLeft + balRight + append), then deletion (del + delete).

**Tech Stack:** Lean 4 (v4.30.0), mathlib4 (v4.30.0), `Ord α` from Init

---

### Task 1: Define Color and RBTree types

**Files:**
- Modify: `RBTProofs/Basic.lean`

- [ ] **Step 1: Replace Basic.lean with types**

Replace the entire content of `RBTProofs/Basic.lean`:

```lean
/-!
# Basic definitions for Red-Black Trees

Definitions and inductive types for Red-Black Trees.
-/

/-- The color of a Red-Black Tree node. -/
inductive Color where
  | red
  | black
  deriving Repr, DecidableEq

/-- A Red-Black Tree: either empty (`nil`) or a `node` with a color,
    left subtree, value, and right subtree. -/
inductive RBTree (α : Type u) where
  | nil
  | node (color : Color) (left : RBTree α) (val : α) (right : RBTree α)
  deriving Repr

namespace RBTree
```

- [ ] **Step 2: Verify compilation**

Run: `lake build`
Expected: Build succeeds with no errors.

Note: First `lake build` will download mathlib4 — this may take several minutes.

- [ ] **Step 3: Commit**

```bash
git add RBTProofs/Basic.lean
git commit -m "feat: define Color and RBTree inductive types"
```

---

### Task 2: Implement insertion (balance, ins, insert)

**Files:**
- Modify: `RBTProofs/Basic.lean`

- [ ] **Step 1: Append insertion functions to Basic.lean**

Append the following code to `RBTProofs/Basic.lean` (after the `namespace RBTree` line):

```lean
/-- Rebalance after insertion. Handles the 4 red-red violation cases:
    LL, LR, RL, RR. Returns a tree with root colored red. -/
def balance : Color → RBTree α → α → RBTree α → RBTree α
  | .black, .node .red (.node .red a x b) y c, z, d =>
    .node .red (.node .black a x b) y (.node .black c z d)
  | .black, .node .red a x (.node .red b y c), z, d =>
    .node .red (.node .black a x b) y (.node .black c z d)
  | .black, a, x, .node .red (.node .red b y c) z d =>
    .node .red (.node .black a x b) y (.node .black c z d)
  | .black, a, x, .node .red b y (.node .red c z d) =>
    .node .red (.node .black a x b) y (.node .black c z d)
  | color, a, x, b => .node color a x b

/-- Internal insert. Returns a tree whose root may be red. -/
def ins (t : RBTree α) (x : α) [Ord α] : RBTree α :=
  match t with
  | nil => .node .red nil x nil
  | .node color l y r =>
    match compare x y with
    | .lt => balance color (ins l x) y r
    | .eq => t
    | .gt => balance color l y (ins r x)

/-- Public insert. Inserts `x` into `t` and ensures the root is black. -/
def insert (t : RBTree α) (x : α) [Ord α] : RBTree α :=
  match ins t x with
  | .node _ l y r => .node .black l y r
  | nil => nil
```

- [ ] **Step 2: Verify compilation**

Run: `lake build`
Expected: Build succeeds with no errors.

- [ ] **Step 3: Commit**

```bash
git add RBTProofs/Basic.lean
git commit -m "feat: implement RBT insertion with balance"
```

---

### Task 3: Implement deletion helpers (balLeft, balRight, append)

**Files:**
- Modify: `RBTProofs/Basic.lean`

- [ ] **Step 1: Append deletion helpers to Basic.lean**

Append the following code to `RBTProofs/Basic.lean` (after the `insert` function, before `end RBTree`):

```lean
/-- Rebalance when left subtree is one black shorter than right.
    Returns a tree: red root = deficit resolved, black root = deficit propagated. -/
def balLeft (l : RBTree α) (x : α) (r : RBTree α) : RBTree α :=
  match l, x, r with
  | .node .red (.node .red a x' b) y c, z, d =>
    .node .red (.node .black a x' b) y (.node .black c z d)
  | .node .red a x' (.node .red b y c), z, d =>
    .node .red (.node .black a x' b) y (.node .black c z d)
  | a, z, .node .black b y (.node .red c w d) =>
    .node .black (balLeft a z b) y (.node .red c w d)
  | a, z, .node .red (.node .black b y c) w (.node .black d v e) =>
    .node .red (.node .black a z b) y (balLeft c w (.node .red d v e))
  | a, z, b => .node .black a z b

/-- Rebalance when right subtree is one black shorter than left.
    Returns a tree: red root = deficit resolved, black root = deficit propagated. -/
def balRight (l : RBTree α) (x : α) (r : RBTree α) : RBTree α :=
  match l, x, r with
  | a, z, .node .red (.node .red b y c) w d =>
    .node .red (.node .black a z b) y (.node .black c w d)
  | a, z, .node .red b y (.node .red c w d) =>
    .node .red (.node .black a z b) y (.node .black c w d)
  | .node .red a x' b, w, .node .black c z d =>
    .node .black (.node .red a x' b) w (balRight c z d)
  | .node .red (.node .black a x' b) w (.node .black c y d), v, e =>
    .node .red (balRight (.node .red a x' b) w c) y (.node .black d v e)
  | a, z, b => .node .black a z b

/-- Concatenate two trees where every value in `t1` < every value in `t2`. -/
def append (t1 t2 : RBTree α) : RBTree α :=
  match t1, t2 with
  | nil, _ => t2
  | _, nil => t1
  | .node .red a x b, .node .red c y d =>
    match append b c with
    | .node .red b' z c' => .node .red (.node .red a x b') z (.node .red c' y d)
    | bc => .node .red a x (.node .red bc y d)
  | .node .black a x b, .node .black c y d =>
    match append b c with
    | .node .red b' z c' => .node .red (.node .black a x b') z (.node .black c' y d)
    | bc => balLeft a x (.node .black bc y d)
  | .node .black a x b, .node .red c y d =>
    .node .red (append (.node .black a x b) c) y d
  | .node .red a x b, .node .black c y d =>
    .node .red a x (append b (.node .black c y d))
```

- [ ] **Step 2: Verify compilation**

Run: `lake build`
Expected: Build succeeds with no errors.

- [ ] **Step 3: Commit**

```bash
git add RBTProofs/Basic.lean
git commit -m "feat: implement RBT deletion helpers (balLeft, balRight, append)"
```

---

### Task 4: Implement deletion (del, delete)

**Files:**
- Modify: `RBTProofs/Basic.lean`

- [ ] **Step 1: Append deletion functions to Basic.lean**

Append the following code to `RBTProofs/Basic.lean` (after `append`, before `end RBTree`):

```lean
/-- Internal delete. Returns `(tree, deficit)` where `deficit` means the result
    is one black shorter than the input. -/
def del (t : RBTree α) (x : α) [Ord α] : RBTree α × Bool :=
  match t with
  | nil => (nil, false)
  | .node color l y r =>
    match compare x y with
    | .lt =>
      let (l', d) := del l x
      if d then
        let t' := balLeft l' y r
        (t', match t' with | .node .black .. => true | _ => false)
      else
        (.node color l' y r, false)
    | .eq => (append l r, color == .black)
    | .gt =>
      let (r', d) := del r x
      if d then
        let t' := balRight l y r'
        (t', match t' with | .node .black .. => true | _ => false)
      else
        (.node color l y r', false)

/-- Public delete. Removes `x` from `t` and ensures the root is black. -/
def delete (t : RBTree α) (x : α) [Ord α] : RBTree α :=
  let (t', _) := del t x
  match t' with
  | .node _ l y r => .node .black l y r
  | nil => nil

end RBTree

#eval
  let t : RBTree Nat := RBTree.nil
  let t := t.insert 5
  let t := t.insert 3
  let t := t.insert 7
  let t := t.insert 2
  let t := t.insert 4
  let t := t.insert 6
  let t := t.insert 8
  t

#eval
  let t : RBTree Nat := RBTree.nil
  let t := t.insert 5
  let t := t.insert 3
  let t := t.insert 7
  let t := t.delete 3
  t
```

- [ ] **Step 2: Verify compilation**

Run: `lake build`
Expected: Build succeeds with no errors.

- [ ] **Step 3: Run #eval blocks**

Run: `lake env lean --run RBTProofs/Basic.lean`
Expected: Outputs two tree structures with no runtime errors.

- [ ] **Step 4: Commit**

```bash
git add RBTProofs/Basic.lean
git commit -m "feat: implement RBT deletion with #eval sanity checks"
```

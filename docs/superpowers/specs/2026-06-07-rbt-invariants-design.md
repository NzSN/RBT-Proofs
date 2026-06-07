# Declare Red-Black Tree Invariants

**Date:** 2026-06-07
**Status:** approved

## Goal

Define the 5 Red-Black Tree well-formedness invariants as `Prop` predicates in a new module `RBTProofs/Invariants.lean`.

## Invariants

All defined in `namespace RBTree`:

1. **`BST [Ord α] : RBTree α → Prop`** — Binary search tree property. Every node's value is greater than all values in its left subtree and less than all values in its right subtree.

2. **`RootBlack : RBTree α → Prop`** — Root is black (or tree is empty).

3. **`NilBlack : RBTree α → Prop`** — Nil nodes are considered black. Trivially true (encoded in type), stated for completeness.

4. **`NoRedRed : RBTree α → Prop`** — No red node has a red child.

5. **`BlackHeightConsistent : RBTree α → Prop`** — Every path from root to nil has the same black height. Uses a helper `blackHeight : RBTree α → Nat`.

## Files

- **Create:** `RBTProofs/Invariants.lean` — all 5 predicates + `blackHeight` helper
- **Modify:** `RBTProofs.lean` — add `import RBTProofs.Invariants`

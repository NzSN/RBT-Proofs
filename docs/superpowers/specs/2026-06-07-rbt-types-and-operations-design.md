# Red-Black Tree Types and Operations

**Date:** 2026-06-07
**Status:** approved

## Goal

Define the Red-Black Tree inductive types plus `insert` and `delete` operations with balancing in `RBTProofs/Basic.lean`.

## Types

### `Color`
```lean
inductive Color where | red | black
deriving Repr, DecidableEq
```

### `RBTree α`
```lean
inductive RBTree (α : Type u) where
  | nil
  | node (color : Color) (left : RBTree α) (val : α) (right : RBTree α)
deriving Repr
```

## Operations

All operations require `[Ord α]` from the Lean prelude.

### Insertion

- **`balance : Color → RBTree α → α → RBTree α → RBTree α`** — rebalance after insertion. Handles the 4 RBT violation cases: LL (left child of left), LR (left child of right), RL (right child of left), RR (right child of right). Returns the balanced tree with root colored red (caller blackens if needed).

- **`ins : RBTree α → α → RBTree α`** — internal insert, recurses down the tree per the BST property, calls `balance` on the way back up when a node's specified child subtree is red with a red child. Returns a tree whose root may be red.

- **`insert : RBTree α → α → RBTree α`** — public insert. Calls `ins`, then `balance` (as a blackener) on the result to ensure the root is black.

### Deletion

- **`balLeft : RBTree α → α → RBTree α → RBTree α`** — rebalance when the left subtree is one black shorter than the right after deletion. Restores black-height equality.

- **`balRight : RBTree α → α → RBTree α → RBTree α`** — rebalance when the right subtree is one black shorter than the left after deletion.

- **`append (t1 t2 : RBTree α) : RBTree α`** — concatenate two trees where every value in `t1` < every value in `t2`. Used when deleting a node that has both children.

- **`del : RBTree α → α → RBTree α`** — internal delete. Finds the node, replaces with `append` of children when both are present, rebalances with `balLeft`/`balRight` on the way up.

- **`delete : RBTree α → α → RBTree α`** — public delete. Calls `del`, then blackens the root.

## What stays the same

- Existing module docstring
- Single file: `RBTProofs/Basic.lean`
- No well-formedness predicates or proofs (separate module later)

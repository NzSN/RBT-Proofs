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

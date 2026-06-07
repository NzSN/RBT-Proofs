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

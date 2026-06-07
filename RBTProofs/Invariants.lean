import RBTProofs.Basic

namespace RBTree

/-- Tree membership — `x` appears as a value in the tree. -/
def mem (x : α) : RBTree α → Prop
  | nil => False
  | node _ l v r => x = v ∨ mem x l ∨ mem x r

/-- Invariant 1: BST property.
    Every node's value is greater than all values in its left subtree
    and less than all values in its right subtree. -/
def BST [Ord α] : RBTree α → Prop
  | nil => True
  | node _ l v r =>
    BST l ∧ BST r ∧
    (∀ x, mem x l → compare x v = .lt) ∧
    (∀ x, mem x r → compare v x = .lt)

/-- Invariant 2: Root is black (or tree is empty). -/
def RootBlack : RBTree α → Prop
  | nil => True
  | node color _ _ _ => color = .black

/-- Invariant 3: All nil nodes are considered black.
    Always true — encoded in the type definition. -/
def NilBlack : RBTree α → Prop
  | _ => True

/-- Invariant 4: No red node has a red child. -/
def NoRedRed : RBTree α → Prop
  | nil => True
  | node .red (.node .red _ _ _) _ _ => False
  | node .red _ _ (.node .red _ _ _) => False
  | node _ l _ r => NoRedRed l ∧ NoRedRed r

/-- Black height of a tree: number of black nodes on any path from root to nil.
    nil has black height 1 (since nil is considered black). -/
def blackHeight : RBTree α → Nat
  | nil => 1
  | node .black l _ _ => blackHeight l + 1
  | node .red l _ _ => blackHeight l

/-- Invariant 5: Every path from root to nil has the same black height. -/
def BlackHeightConsistent : RBTree α → Prop
  | nil => True
  | node _ l _ r => blackHeight l = blackHeight r ∧ BlackHeightConsistent l ∧ BlackHeightConsistent r

end RBTree

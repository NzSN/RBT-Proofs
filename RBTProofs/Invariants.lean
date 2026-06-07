import RBTProofs.Basic
import Mathlib.Tactic

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

section BSTProofs

/-- Helper: transitivity of `compare` for `LinearOrder`. -/
theorem compare_lt_trans [LinearOrder α] {a b c : α} (h1 : compare a b = .lt) (h2 : compare b c = .lt) : compare a c = .lt := by
  have hlt1 : a < b := (compare_lt_iff_lt.mp h1)
  have hlt2 : b < c := (compare_lt_iff_lt.mp h2)
  have hlt3 : a < c := lt_trans hlt1 hlt2
  exact compare_lt_iff_lt.mpr hlt3

/-- `balance` preserves membership: values are just reshuffled. -/
theorem mem_balance (c : Color) (l : RBTree α) (v : α) (r : RBTree α) (y : α) :
    mem y (balance c l v r) ↔ y = v ∨ mem y l ∨ mem y r := by
  unfold balance
  split <;> simp [mem] <;> tauto

/-- Membership after `ins`: `y` is in the result iff `y = x` or `y` was in `t`. -/
theorem mem_ins (t : RBTree α) (x y : α) [LinearOrder α] : mem y (ins t x) ↔ y = x ∨ mem y t := by
  induction t with
  | nil => simp [ins, mem]
  | node color l val r ih_l ih_r =>
    simp [ins]
    split
    · rw [mem_balance]
      simp [mem, ih_l]
      tauto
    · rename_i h_eq
      have hxeq : x = val := (compare_eq_iff_eq.mp h_eq)
      simp [mem, hxeq]
    · rw [mem_balance]
      simp [mem, ih_r]
      tauto

/-- `balance` preserves BST when subtrees are BST and properly ordered. -/
theorem bst_balance [LinearOrder α] (c : Color) (l : RBTree α) (v : α) (r : RBTree α)
    (hl : BST l) (hr : BST r)
    (hll : ∀ x, mem x l → compare x v = .lt)
    (hrr : ∀ x, mem x r → compare v x = .lt) : BST (balance c l v r) := by
  match c, l, v, r with
  | .black, .node .red (.node .red a x b) y c₀, z, d =>
    rcases hl with ⟨⟨hla, hlb, hla_val, hlb_val⟩, hlc₀, hly, hlc₀_val⟩
    have hyz : compare y z = .lt := hll y (by simp [mem])
    have h_c₀_lt_z : ∀ w, mem w c₀ → compare w z = .lt := λ w hw => hll w (by simp [mem, hw])
    have h_z_lt_d : ∀ w, mem w d → compare z w = .lt := hrr
    have h_y_lt_d : ∀ w, mem w d → compare y w = .lt := λ w hw =>
      compare_lt_trans hyz (h_z_lt_d w hw)
    have h_x_lt_b : ∀ w, mem w b → compare x w = .lt := hlb_val
    have hleft : BST (.node .black a x b) := ⟨hla, hlb, hla_val, h_x_lt_b⟩
    have hright : BST (.node .black c₀ z d) := ⟨hlc₀, hr, h_c₀_lt_z, h_z_lt_d⟩
    have horderL : ∀ w, mem w (.node .black a x b) → compare w y = .lt := by
      intro w hw; simp [mem] at hw
      rcases hw with (rfl | hwa | hwb)
      · apply hly; simp [mem]
      · apply hly; simp [mem, hwa]
      · apply hly; simp [mem, hwb]
    have horderR : ∀ w, mem w (.node .black c₀ z d) → compare y w = .lt := by
      intro w hw; simp [mem] at hw
      rcases hw with (rfl | hwc | hwd)
      · exact hyz
      · exact hlc₀_val w hwc
      · exact h_y_lt_d w hwd
    -- c = .black, l = .node .red (.node .red a x b) y c₀, v = z, r = d  (definitionally)
    dsimp [balance]; exact ⟨hleft, hright, horderL, horderR⟩

  | .black, .node .red a x (.node .red b y c₀), z, d =>
    rcases hl with ⟨hla, hright_inner, hla_val, hx_r⟩
    rcases hright_inner with ⟨hlb, hlc₀, hlb_val, hlc₀_val⟩
    have hxy : compare x y = .lt := hx_r y (by simp [mem])
    have hyz : compare y z = .lt := hll y (by simp [mem])
    have h_a_lt_y : ∀ w, mem w a → compare w y = .lt := λ w hw =>
      compare_lt_trans (hla_val w hw) hxy
    have h_x_lt_b : ∀ w, mem w b → compare x w = .lt := λ w hw =>
      hx_r w (by simp [mem, hw])
    have h_c₀_lt_z : ∀ w, mem w c₀ → compare w z = .lt := λ w hw =>
      hll w (by simp [mem, hw])
    have h_y_lt_d : ∀ w, mem w d → compare y w = .lt := λ w hw =>
      compare_lt_trans hyz (hrr w hw)
    have hleft : BST (.node .black a x b) := ⟨hla, hlb, hla_val, h_x_lt_b⟩
    have hright : BST (.node .black c₀ z d) := ⟨hlc₀, hr, h_c₀_lt_z, hrr⟩
    have horderL : ∀ w, mem w (.node .black a x b) → compare w y = .lt := by
      intro w hw; simp [mem] at hw
      rcases hw with (rfl | hwa | hwb)
      · exact hxy
      · exact h_a_lt_y w hwa
      · exact hlb_val w hwb
    have horderR : ∀ w, mem w (.node .black c₀ z d) → compare y w = .lt := by
      intro w hw; simp [mem] at hw
      rcases hw with (rfl | hwc | hwd)
      · exact hyz
      · exact hlc₀_val w hwc
      · exact h_y_lt_d w hwd
    have h_eq : balance .black (.node .red a x (.node .red b y c₀)) z d = .node .red (.node .black a x b) y (.node .black c₀ z d) := by
      dsimp [balance]
    rw [h_eq]
    exact ⟨hleft, hright, horderL, horderR⟩

  | .black, a, x, .node .red (.node .red b y c₀) z d =>
    rcases hr with ⟨hright_inner, hd, hrz, hrd_val⟩
    rcases hright_inner with ⟨hlb, hlc₀, hlb_val, hlc₀_val⟩
    have hxy : compare x y = .lt := hrr y (by simp [mem])
    have hxz : compare x z = .lt := hrr z (by simp [mem])
    have hyz : compare y z = .lt := hrz y (by simp [mem])
    have h_c₀_lt_z : ∀ w, mem w c₀ → compare w z = .lt := λ w hw =>
      hrz w (by simp [mem, hw])
    have h_a_lt_y : ∀ w, mem w a → compare w y = .lt := λ w hw =>
      compare_lt_trans (hll w hw) hxy
    have h_a_lt_z : ∀ w, mem w a → compare w z = .lt := λ w hw =>
      compare_lt_trans (hll w hw) hxz
    have h_x_lt_b : ∀ w, mem w b → compare x w = .lt := λ w hw =>
      hrr w (by simp [mem, hw])
    have h_y_lt_d : ∀ w, mem w d → compare y w = .lt := λ w hw =>
      compare_lt_trans hyz (hrd_val w hw)
    have hleft : BST (.node .black a x b) := ⟨hl, hlb, hll, h_x_lt_b⟩
    have hright : BST (.node .black c₀ z d) := ⟨hlc₀, hd, h_c₀_lt_z, hrd_val⟩
    have horderL : ∀ w, mem w (.node .black a x b) → compare w y = .lt := by
      intro w hw; simp [mem] at hw
      rcases hw with (rfl | hwa | hwb)
      · exact hxy
      · exact h_a_lt_y w hwa
      · exact hlb_val w hwb
    have horderR : ∀ w, mem w (.node .black c₀ z d) → compare y w = .lt := by
      intro w hw; simp [mem] at hw
      rcases hw with (rfl | hwc | hwd)
      · exact hyz
      · exact hlc₀_val w hwc
      · exact h_y_lt_d w hwd
    have h_eq : balance .black a x (.node .red (.node .red b y c₀) z d) = .node .red (.node .black a x b) y (.node .black c₀ z d) := by
      dsimp [balance]
    rw [h_eq]
    exact ⟨hleft, hright, horderL, horderR⟩

  | .black, a, x, .node .red b y (.node .red c₀ z d) =>
    rcases hr with ⟨hlb, hright_inner, hly_left, hly_right⟩
    rcases hright_inner with ⟨hlc₀, hd, hz_left, hz_right⟩
    have hxy : compare x y = .lt := hrr y (by simp [mem])
    have hyz : compare y z = .lt := hly_right z (by simp [mem])
    have h_a_lt_y : ∀ w, mem w a → compare w y = .lt := λ w hw =>
      compare_lt_trans (hll w hw) hxy
    have h_x_lt_b : ∀ w, mem w b → compare x w = .lt := λ w hw =>
      hrr w (by simp [mem, hw])
    have h_y_lt_d : ∀ w, mem w d → compare y w = .lt := λ w hw =>
      compare_lt_trans hyz (hz_right w hw)
    have hleft : BST (.node .black a x b) := ⟨hl, hlb, hll, h_x_lt_b⟩
    have hright : BST (.node .black c₀ z d) := ⟨hlc₀, hd, hz_left, hz_right⟩
    have horderL : ∀ w, mem w (.node .black a x b) → compare w y = .lt := by
      intro w hw; simp [mem] at hw
      rcases hw with (rfl | hwa | hwb)
      · exact hxy
      · exact h_a_lt_y w hwa
      · exact hly_left w hwb
    have horderR : ∀ w, mem w (.node .black c₀ z d) → compare y w = .lt := by
      intro w hw; simp [mem] at hw
      rcases hw with (rfl | hwc | hwd)
      · exact hyz
      · exact hly_right w (by simp [mem, hwc])
      · exact h_y_lt_d w hwd
    have h_eq : balance .black a x (.node .red b y (.node .red c₀ z d)) = .node .red (.node .black a x b) y (.node .black c₀ z d) := by
      dsimp [balance]
    rw [h_eq]
    exact ⟨hleft, hright, horderL, horderR⟩

  | _, _, _, _ =>
    have h_eq : balance c l v r = .node c l v r := by
      native_decide
    rw [h_eq]
    simpa [BST] using ⟨hl, hr, hll, hrr⟩

/-- `ins` preserves BST. -/
theorem bst_ins [LinearOrder α] (t : RBTree α) (x : α) (h : BST t) : BST (ins t x) := by
  induction t with
  | nil => simp [ins, BST, mem]
  | node color l val r ih_l ih_r =>
    have h_saved := h
    rcases h with ⟨hl, hr, hll, hrr⟩
    simp [ins]
    split
    case h_1 =>
      apply bst_balance color (ins l x) val r
      · exact ih_l hl
      · exact hr
      · intro y hy
        rw [mem_ins] at hy
        rcases hy with (rfl | hy)
        · exact h
        · exact hll y hy
      · exact hrr
    case h_2 =>
      exact h_saved
    case h_3 =>
      apply bst_balance color l val (ins r x)
      · exact hl
      · exact ih_r hr
      · exact hll
      · intro y hy
        rw [mem_ins] at hy
        rcases hy with (rfl | hy)
        · have h_lt : val < x := (compare_gt_iff_gt.mp h)
          exact compare_lt_iff_lt.mpr h_lt
        · exact hrr y hy

/-- `insert` preserves BST. -/
theorem bst_insert [LinearOrder α] (t : RBTree α) (x : α) (h : BST t) : BST (insert t x) := by
  have h_ins := bst_ins t x h
  unfold insert
  cases h_ins_t : ins t x
  · simp [BST]
  · rename_i c' l' y' r'
    dsimp
    have h_ins' : BST (node c' l' y' r') := by
      rw [← h_ins_t]; exact h_ins
    simpa [BST] using h_ins'

end BSTProofs

end RBTree

import OMAStatements.S_oeis_a250880
import Mathlib

-- Proof of the conjectures in OEIS A250880 (statement by @ivillar).
-- Idea: the conditions only involve 2 X 2 blocks, so the count is a walk count on the columns of the
-- array (transfer matrix). The 256 states are lumped into 30 classes with constant numbers of successors in
-- each class (checked by decide), which gives a linear system for the class counts W n c. The recurrence
-- of order 4 follows from explicit row vectors orthogonal to all W n (an invariant subspace of the
-- transposed class matrix), and the generating function and closed forms follow from the recurrence
-- and the first values.

namespace OMAA250880Helpers

open OMA.S_oeis_a250880

instance (p q r s : ℕ) : Decidable (Blk p q r s) := by
  unfold Blk; infer_instance

/-- The states of the transfer matrix: the columns of the array, encoded as numbers in base 4
(digit j of the code is entry j). -/
abbrev R := Fin (4 ^ 4)

/-- Digit j of the code a in base 4. -/
def dig (a j : ℕ) : ℕ := a / 4 ^ j % 4

/-- Consecutive columns u, v: all the 2 X 2 blocks they form satisfy the condition. -/
abbrev BlockOK (u v : Fin 4 → Fin 4) : Prop :=
  ∀ i : Fin 3, Blk (u i.castSucc) (v i.castSucc) (u i.succ) (v i.succ)

/-- The truth table of `Blk` on entries below 4: bit ((p * 4 + q) * 4 + r) * 4 + s. -/
def blkTab : ℕ := 63746136017916708694516886842211954588748517048706087710756822688284235697391

/-- `Blk` read off the truth table. -/
def blkB (p q r s : ℕ) : Bool := Nat.testBit blkTab (((p * 4 + q) * 4 + r) * 4 + s)

theorem blk_iff : ∀ p q r s : Fin 4, blkB p q r s = true ↔ Blk p q r s := by decide +kernel

/-- The same condition on codes. -/
def compatB (r s : ℕ) : Bool :=
  blkB (dig r 0) (dig s 0) (dig r 1) (dig s 1) &&
    (blkB (dig r 1) (dig s 1) (dig r 2) (dig s 2) &&
    (blkB (dig r 2) (dig s 2) (dig r 3) (dig s 3)))

abbrev compatN (r s : ℕ) : Prop := compatB r s = true

/-- States are unconstrained. -/
abbrev ok (_r : R) : Prop := True

/-- Every state may start a walk. -/
abbrev init (_r : R) : Prop := True

/-- Compatibility of consecutive states. -/
abbrev compat (r s : R) : Prop := compatN r.val s.val

theorem dig_enc (u : Fin 4 → Fin 4) (i : Fin 4) : dig ((finFunctionFinEquiv (m := 4) (n := 4)) u).val i.val = (u i).val :=
  congrArg Fin.val (congrFun (Equiv.symm_apply_apply (finFunctionFinEquiv (m := 4) (n := 4)) u) i)

theorem dig_e0 (u : Fin 4 → Fin 4) : dig ((finFunctionFinEquiv (m := 4) (n := 4)) u).val 0 = (u 0).val := dig_enc u 0

theorem dig_e1 (u : Fin 4 → Fin 4) : dig ((finFunctionFinEquiv (m := 4) (n := 4)) u).val 1 = (u 1).val := dig_enc u 1

theorem dig_e2 (u : Fin 4 → Fin 4) : dig ((finFunctionFinEquiv (m := 4) (n := 4)) u).val 2 = (u 2).val := dig_enc u 2

theorem dig_e3 (u : Fin 4 → Fin 4) : dig ((finFunctionFinEquiv (m := 4) (n := 4)) u).val 3 = (u 3).val := dig_enc u 3


theorem blockOK_iff (u v : Fin 4 → Fin 4) :
    BlockOK u v ↔
      (Blk (u 0) (v 0) (u 1) (v 1) ∧
      (Blk (u 1) (v 1) (u 2) (v 2) ∧
      (Blk (u 2) (v 2) (u 3) (v 3)))) := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨h0, h1, h2⟩ j
    fin_cases j <;>
      first
        | exact h0
        | exact h1
        | exact h2

theorem compat_enc (u v : Fin 4 → Fin 4) :
    compat ((finFunctionFinEquiv (m := 4) (n := 4)) u) ((finFunctionFinEquiv (m := 4) (n := 4)) v) ↔ BlockOK u v := by
  rw [blockOK_iff]
  simp only [compat, compatN, compatB, Bool.and_eq_true, dig_e0, dig_e1, dig_e2, dig_e3, blk_iff]

/-- Arrays as sequences of encoded columns. -/
def enc (n : ℕ) : (Fin 4 → Fin (n + 1) → Fin 4) ≃ (Fin (n + 1) → R) where
  toFun := fun x j => (finFunctionFinEquiv (m := 4) (n := 4)) (fun i => x i j)
  invFun := fun y i j => (finFunctionFinEquiv (m := 4) (n := 4)).symm (y j) i
  left_inv := fun x => by funext i j; exact congrFun (Equiv.symm_apply_apply _ _) i
  right_inv := fun y => by funext j; exact Equiv.apply_symm_apply _ _

abbrev Walk {n : ℕ} (x : Fin (n + 1) → R) : Prop :=
  (∀ i, ok (x i)) ∧ ∀ i : Fin n, compat (x i.castSucc) (x i.succ)

theorem walk_cons (n : ℕ) (r : R) (y : Fin (n + 1) → R) :
    Walk (Fin.cons r y : Fin (n + 2) → R) ↔ ok r ∧ compat r (y 0) ∧ Walk y := by
  simp only [Walk, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.castSucc_zero,
    Fin.succ_zero_eq_one, ← Fin.succ_castSucc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨h1, ?_, h2, h4⟩
    simpa using h3
  · rintro ⟨h1, h3, h2, h4⟩
    refine ⟨⟨h1, h2⟩, ?_, h4⟩
    simpa using h3

def F (n : ℕ) (s : R) : ℕ := ∑ y : Fin (n + 1) → R, if Walk y ∧ y 0 = s then 1 else 0

theorem F_zero (s : R) : F 0 s = if ok s then 1 else 0 := by
  unfold F
  rw [← (Equiv.funUnique (Fin 1) R).symm.sum_comp]
  have h : ∀ r : R, (if Walk ((Equiv.funUnique (Fin 1) R).symm r) ∧
      (Equiv.funUnique (Fin 1) R).symm r 0 = s then 1 else 0) = if r = s then (if ok s then 1 else 0) else 0 := by
    intro r
    simp only [Equiv.funUnique_symm_apply, Walk, IsEmpty.forall_iff, and_true]
    by_cases hr : r = s
    · subst hr; simp
    · simp [hr]
  rw [Finset.sum_congr rfl (fun r _ => h r), Finset.sum_ite_eq']
  simp

theorem F_succ (n : ℕ) (s : R) :
    F (n + 1) s = ∑ t : R, if ok s ∧ compat s t then F n t else 0 := by
  have lhs : F (n + 1) s = ∑ y : Fin (n + 1) → R, if ok s ∧ compat s (y 0) ∧ Walk y then 1 else 0 := by
    unfold F
    rw [← (Fin.consEquiv (fun _ : Fin (n + 2) => R)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    have h : ∀ r : R, (if Walk ((Fin.consEquiv (fun _ : Fin (n + 2) => R)) (r, y)) ∧
        (Fin.consEquiv (fun _ : Fin (n + 2) => R)) (r, y) 0 = s then 1 else 0) =
        if r = s then (if ok s ∧ compat s (y 0) ∧ Walk y then 1 else 0) else 0 := by
      intro r
      rw [show (Fin.consEquiv (fun _ : Fin (n + 2) => R)) (r, y) = (Fin.cons r y : Fin (n + 2) → R)
        from rfl]
      simp only [walk_cons, Fin.cons_zero]
      by_cases hr : r = s
      · subst hr
        rw [if_pos rfl]
        exact if_congr ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩ rfl rfl
      · rw [if_neg hr, if_neg (show ¬((ok r ∧ compat r (y 0) ∧ Walk y) ∧ r = s) from fun h => hr h.2)]
    rw [Finset.sum_congr rfl (fun r _ => h r), Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  rw [lhs]
  unfold F
  have h2 : ∀ t : R, (if ok s ∧ compat s t then
      ∑ y : Fin (n + 1) → R, (if Walk y ∧ y 0 = t then 1 else 0) else 0) =
      ∑ y : Fin (n + 1) → R, if y 0 = t then (if ok s ∧ compat s (y 0) ∧ Walk y then 1 else 0) else 0 := by
    intro t
    split_ifs with ht
    · apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y 0 = t
      · subst hy
        rw [if_pos (rfl : y 0 = y 0)]
        exact if_congr ⟨fun h => ⟨ht.1, ht.2, h.1⟩, fun h => ⟨h.2.2, rfl⟩⟩ rfl rfl
      · rw [if_neg hy, if_neg (show ¬(Walk y ∧ y 0 = t) from fun h => hy h.2)]
    · symm
      apply Finset.sum_eq_zero
      intro y _
      by_cases hy : y 0 = t
      · subst hy; rw [if_pos rfl, if_neg (fun h => ht ⟨h.1, h.2.1⟩)]
      · rw [if_neg hy]
  rw [Finset.sum_congr rfl (fun t _ => h2 t), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]

/-- The classes of the states, one byte per state. -/
def clsTab : ℕ := 380200071427188321184880902219646493652283560820182165083886416794407707516092834037614134253210746631631976010845859052871994813535187307001037086899391622838302720110190273552745997729622093500119850171248888413113610503303583398711350925890200381796715663396233888244184726962897648957022934778098943127994437118836371113839045443681234179125865407671072023611844614020334384462892152229814085589196669512453186094128993814015498174556146440833363121185119151930129618126279176736691627354648217161980593975935437912942744798780029130679189678642561728977958882781839723136393996630926800957428080683422087123968

/-- The class of a code (states of one class have the same numbers of successors in each class). -/
def clsF (a : ℕ) : Fin 30 := ⟨(clsTab >>> (8 * a)) % 256 % 30, Nat.mod_lt _ (by norm_num)⟩

/-- The class of a state. -/
def cls (t : R) : Fin 30 := clsF t.val

/-- The codes of the states of each class. -/
def mem : Fin 30 → List ℕ :=
  ![[0, 3], [64, 67, 68, 71, 80, 83, 84, 87], [128, 131, 132, 135, 136, 139, 144, 147, 148, 151, 152, 155, 160, 163, 164, 167, 168, 171], [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255], [16, 19, 20, 23], [32, 35, 36, 39, 40, 43], [96, 99, 100, 103, 104, 107], [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127], [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191], [4, 7], [8, 11], [72, 75, 88, 91], [24, 27], [12, 13, 14, 15], [76, 77, 78, 79, 92, 93, 94, 95], [140, 141, 142, 143, 156, 157, 158, 159, 172, 173, 174, 175], [28, 29, 30, 31], [44, 45, 46, 47], [108, 109, 110, 111], [1, 2], [65, 66, 69, 70, 81, 82, 85, 86], [129, 130, 133, 134, 137, 138, 145, 146, 149, 150, 153, 154, 161, 162, 165, 166, 169, 170], [17, 18, 21, 22], [33, 34, 37, 38, 41, 42], [97, 98, 101, 102, 105, 106], [5, 6], [9, 10], [73, 74, 89, 90], [25, 26]]

/-- Mat c d: the number of successors of class d of a state of class c. -/
def Mat : Fin 30 → Fin 30 → ℤ :=
  ![![1, 3, 6, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 3, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 3, 10, 1, 0, 2, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 1, 4, 0, 1, 1, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 4, 0, 0, 1, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2, 5, 16, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 3, 10, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2, 7, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2, 7, 0, 0, 1, 0, 0, 3, 0, 0, 1, 1, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 3, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 2, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 2, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 4, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 9, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 13, 0, 0, 1, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 1, 0, 3, 0, 0, 0, 0],
    ![0, 0, 0, 5, 0, 0, 0, 0, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0],
    ![0, 0, 0, 5, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 2, 21, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 2, 7, 0, 0, 0, 1, 0, 2, 0],
    ![0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 6, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 1, 2, 0],
    ![0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 9, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 0, 0, 2, 0, 0, 1, 0, 0, 1, 1]]

/-- W n c: the number of walks with n steps starting at a given state of class c. -/
def W : ℕ → Fin 30 → ℤ
  | 0 => fun _ => 1
  | n + 1 => fun c => ∑ d, Mat c d * W n d

theorem hmem_0 : ∀ c : Fin 30, 0 ≤ c.val → c.val < 3 →
    mem c = (List.range (4 ^ 4)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_1 : ∀ c : Fin 30, 3 ≤ c.val → c.val < 6 →
    mem c = (List.range (4 ^ 4)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_2 : ∀ c : Fin 30, 6 ≤ c.val → c.val < 9 →
    mem c = (List.range (4 ^ 4)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_3 : ∀ c : Fin 30, 9 ≤ c.val → c.val < 12 →
    mem c = (List.range (4 ^ 4)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_4 : ∀ c : Fin 30, 12 ≤ c.val → c.val < 15 →
    mem c = (List.range (4 ^ 4)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_5 : ∀ c : Fin 30, 15 ≤ c.val → c.val < 18 →
    mem c = (List.range (4 ^ 4)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_6 : ∀ c : Fin 30, 18 ≤ c.val → c.val < 21 →
    mem c = (List.range (4 ^ 4)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_7 : ∀ c : Fin 30, 21 ≤ c.val → c.val < 24 →
    mem c = (List.range (4 ^ 4)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_8 : ∀ c : Fin 30, 24 ≤ c.val → c.val < 27 →
    mem c = (List.range (4 ^ 4)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_9 : ∀ c : Fin 30, 27 ≤ c.val → c.val < 30 →
    mem c = (List.range (4 ^ 4)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem : ∀ c : Fin 30, mem c = (List.range (4 ^ 4)).filter (fun a => clsF a = c) := fun c =>
  if h5 : c.val < 15 then
    if h2 : c.val < 6 then
      if h1 : c.val < 3 then
        hmem_0 c (Nat.zero_le _) h1
      else
        hmem_1 c (Nat.le_of_not_lt h1) h2
    else
      if h3 : c.val < 9 then
        hmem_2 c (Nat.le_of_not_lt h2) h3
      else
        if h4 : c.val < 12 then
          hmem_3 c (Nat.le_of_not_lt h3) h4
        else
          hmem_4 c (Nat.le_of_not_lt h4) h5
  else
    if h7 : c.val < 21 then
      if h6 : c.val < 18 then
        hmem_5 c (Nat.le_of_not_lt h5) h6
      else
        hmem_6 c (Nat.le_of_not_lt h6) h7
    else
      if h8 : c.val < 24 then
        hmem_7 c (Nat.le_of_not_lt h7) h8
      else
        if h9 : c.val < 27 then
          hmem_8 c (Nat.le_of_not_lt h8) h9
        else
          hmem_9 c (Nat.le_of_not_lt h9) c.isLt

set_option maxHeartbeats 0 in
theorem cntN : ∀ s : R, ∀ c : Fin 30,
    (((mem c).filter (fun a => compatB s.val a)).length : ℤ) = Mat (cls s) c := by
  have h_0 : ∀ a ∈ List.range' 0 31, ∀ c : Fin 30,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_1 : ∀ a ∈ List.range' 31 31, ∀ c : Fin 30,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_2 : ∀ a ∈ List.range' 62 31, ∀ c : Fin 30,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_3 : ∀ a ∈ List.range' 93 31, ∀ c : Fin 30,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_4 : ∀ a ∈ List.range' 124 31, ∀ c : Fin 30,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_5 : ∀ a ∈ List.range' 155 31, ∀ c : Fin 30,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_6 : ∀ a ∈ List.range' 186 31, ∀ c : Fin 30,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_7 : ∀ a ∈ List.range' 217 31, ∀ c : Fin 30,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_8 : ∀ a ∈ List.range' 248 8, ∀ c : Fin 30,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  exact fun s c =>
    if h4 : s.val < 124 then
      if h2 : s.val < 62 then
        if h1 : s.val < 31 then
          h_0 s.val (List.mem_range'_1.mpr ⟨(Nat.zero_le _), h1⟩) c
        else
          h_1 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h1), h2⟩) c
      else
        if h3 : s.val < 93 then
          h_2 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h2), h3⟩) c
        else
          h_3 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h3), h4⟩) c
    else
      if h6 : s.val < 186 then
        if h5 : s.val < 155 then
          h_4 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h4), h5⟩) c
        else
          h_5 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h5), h6⟩) c
      else
        if h7 : s.val < 217 then
          h_6 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h6), h7⟩) c
        else
          if h8 : s.val < 248 then
            h_7 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h7), h8⟩) c
          else
            h_8 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h8), s.isLt⟩) c

/-- U i: the row vector (class sizes) * Mat^i. -/
def U : Fin 6 → Fin 30 → ℤ :=
  ![![2, 8, 18, 64, 4, 6, 6, 16, 16, 16, 2, 2, 4, 2, 4, 8, 12, 4, 4, 4, 2, 8, 18, 4, 6, 6, 2, 2, 4, 2],
    ![2, 24, 130, 1056, 4, 6, 26, 16, 78, 214, 2, 2, 14, 2, 4, 30, 120, 4, 4, 22, 2, 26, 152, 4, 6, 30, 2, 2, 16, 2],
    ![2, 40, 348, 4516, 4, 6, 46, 16, 140, 648, 2, 2, 24, 2, 4, 52, 346, 4, 4, 40, 2, 44, 422, 4, 6, 54, 2, 2, 28, 2],
    ![2, 56, 672, 12020, 4, 6, 66, 16, 202, 1318, 2, 2, 34, 2, 4, 74, 690, 4, 4, 58, 2, 62, 828, 4, 6, 78, 2, 2, 40, 2],
    ![2, 72, 1102, 25144, 4, 6, 86, 16, 264, 2224, 2, 2, 44, 2, 4, 96, 1152, 4, 4, 76, 2, 80, 1370, 4, 6, 102, 2, 2, 52, 2],
    ![2, 88, 1638, 45464, 4, 6, 106, 16, 326, 3366, 2, 2, 54, 2, 4, 118, 1732, 4, 4, 94, 2, 98, 2048, 4, 6, 126, 2, 2, 64, 2]]

theorem totN : ∀ c : Fin 30, ((mem c).length : ℤ) = U 0 c := by decide +kernel

theorem card_cls (c : Fin 30) (P : ℕ → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun t : R => cls t = c ∧ P t.val)).card = ((mem c).filter (fun a => P a)).length := by
  have key : (Finset.univ.filter (fun t : R => cls t = c ∧ P t.val)).map Fin.valEmbedding =
      ((mem c).filter (fun a => P a)).toFinset := by
    ext a
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    rw [hmem c]
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
      exact ⟨⟨t.isLt, h1⟩, h2⟩
    · rintro ⟨⟨ha, hc⟩, h2⟩
      exact ⟨⟨a, ha⟩, ⟨hc, h2⟩, rfl⟩
  have hnd : (mem c).Nodup := by
    rw [hmem c]
    exact List.Nodup.filter _ (by first | exact List.nodup_range | exact List.nodup_range _)
  rw [← Finset.card_map Fin.valEmbedding, key, List.toFinset_card_of_nodup (hnd.filter _)]

theorem cnt : ∀ s : R, ∀ c : Fin 30,
    ((Finset.univ.filter (fun t : R => cls t = c ∧ (ok s ∧ compat s t))).card : ℤ) = Mat (cls s) c := by
  intro s c
  have h2 : Finset.univ.filter (fun t : R => cls t = c ∧ (ok s ∧ compat s t)) =
      Finset.univ.filter (fun t : R => cls t = c ∧ compatN s.val t.val) :=
    Finset.filter_congr (fun t _ => ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, trivial, h.2⟩⟩)
  rw [h2, card_cls c (fun a => compatN s.val a)]
  have h3 : (mem c).filter (fun a => decide (compatN s.val a)) = (mem c).filter (fun a => compatB s.val a) :=
    List.filter_congr (fun a _ => by simp only [compatN, Bool.decide_eq_true])
  first
    | (rw [h3]; exact cntN s c)
    | (simpa [compatN] using cntN s c)

theorem tot : ∀ c : Fin 30,
    ((Finset.univ.filter (fun t : R => cls t = c ∧ init t)).card : ℤ) = U 0 c := by
  intro c
  have h2 : Finset.univ.filter (fun t : R => cls t = c ∧ init t) =
      Finset.univ.filter (fun t : R => cls t = c ∧ (fun _ : ℕ => True) t.val) :=
    Finset.filter_congr (fun t _ => Iff.rfl)
  rw [h2, card_cls c (fun _ : ℕ => True)]
  simpa using totN c

theorem hU0 : ∀ d : Fin 30, ∑ c, U 0 c * Mat c d = U 1 d := by decide +kernel

theorem hU1 : ∀ d : Fin 30, ∑ c, U 1 c * Mat c d = U 2 d := by decide +kernel

theorem hU2 : ∀ d : Fin 30, ∑ c, U 2 c * Mat c d = U 3 d := by decide +kernel

theorem hU3 : ∀ d : Fin 30, ∑ c, U 3 c * Mat c d = U 4 d := by decide +kernel

theorem hU4 : ∀ d : Fin 30, ∑ c, U 4 c * Mat c d = U 5 d := by decide +kernel

theorem hU : ∀ (i : Fin 5) (d : Fin 30), ∑ c, U i.castSucc c * Mat c d = U i.succ d := by
  intro i d
  fin_cases i
  · exact hU0 d
  · exact hU1 d
  · exact hU2 d
  · exact hU3 d
  · exact hU4 d

/-- Coefficients of the recurrence. -/
def L : Fin 6 → ℤ := ![1, -4, 6, -4, 1, 0]

/-- Row vectors orthogonal to all the vectors W n. -/
def Rm : Fin 1 → Fin 30 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def Am : Fin 1 → Fin 1 → ℤ :=
  ![![0]]

theorem hRA : ∀ (l : Fin 1) (d : Fin 30), ∑ c, Rm l c * Mat c d = ∑ l', Am l l' * Rm l' d := by
  decide +kernel

theorem hR0 : ∀ l : Fin 1, ∑ c, Rm l c = 0 := by decide +kernel

theorem hL : ∀ c : Fin 30, ∑ i, L i * U i c = Rm 0 c := by decide +kernel

/-- The first values. -/
def vals : Fin 6 → ℤ := ![256, 2002, 6812, 16262, 31928, 55386]

theorem hV : ∀ i : Fin 6, ∑ c, U i c = vals i := by decide +kernel

theorem sum_cls (g : Fin 30 → ℤ) (P : R → Prop) [DecidablePred P] :
    (∑ t : R, if P t then g (cls t) else 0) =
      ∑ c : Fin 30, ((Finset.univ.filter (fun t => cls t = c ∧ P t)).card : ℤ) * g c := by
  rw [← Finset.sum_fiberwise Finset.univ cls]
  apply Finset.sum_congr rfl
  intro c _
  have h : ∑ t ∈ Finset.univ.filter (fun t => cls t = c), (if P t then g (cls t) else 0) =
      ∑ t ∈ Finset.univ.filter (fun t => cls t = c), (if P t then g c else 0) :=
    Finset.sum_congr rfl (fun t ht => by rw [(Finset.mem_filter.mp ht).2])
  rw [h, ← Finset.sum_filter, Finset.filter_filter, Finset.sum_const, nsmul_eq_mul]

theorem F_eq (n : ℕ) : ∀ s : R, (F n s : ℤ) = W n (cls s) := by
  induction n with
  | zero =>
    intro s
    rw [F_zero]
    simp [W, ok]
  | succ n ih =>
    intro s
    rw [F_succ]
    push_cast
    simp only [ih]
    rw [sum_cls (W n) (fun t => ok s ∧ compat s t)]
    simp only [cnt]
    rfl

theorem swap_sum (f : Fin 30 → ℤ) (n : ℕ) :
    ∑ c, f c * W (n + 1) c = ∑ d, (∑ c, f c * Mat c d) * W n d := by
  have h : ∀ c, f c * W (n + 1) c = ∑ d, f c * Mat c d * W n d := by
    intro c
    show f c * ∑ d, Mat c d * W n d = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  simp only [h, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem W_inv : ∀ (n : ℕ) (l : Fin 1), ∑ c, Rm l c * W n c = 0 := by
  intro n
  induction n with
  | zero =>
    intro l
    simpa [W] using hR0 l
  | succ n ih =>
    intro l
    rw [swap_sum]
    simp only [hRA, Finset.sum_mul]
    rw [Finset.sum_comm]
    have h : ∀ l', ∑ d, Am l l' * Rm l' d * W n d = Am l l' * ∑ d, Rm l' d * W n d := by
      intro l'
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      ring
    simp only [h, ih, mul_zero, Finset.sum_const_zero]

theorem W_shift : ∀ (i : Fin 6) (n : ℕ), ∑ c, U 0 c * W (n + i) c = ∑ c, U i c * W n c := by
  intro i
  induction i using Fin.induction with
  | zero => intro n; simp
  | succ i ih =>
    intro n
    have h1 : n + ((i.succ : Fin 6) : ℕ) = (n + 1) + ((i.castSucc : Fin 6) : ℕ) := by
      simp only [Fin.val_succ, Fin.val_castSucc]; omega
    rw [h1, ih (n + 1), swap_sum]
    simp only [hU]

theorem a_eq (n : ℕ) : (a n : ℤ) = ∑ c, U 0 c * W n c := by
  unfold a
  rw [Nat.card_congr (Equiv.subtypeEquiv (enc n)
      (p := fun x : Fin 4 → Fin (n + 1) → Fin 4 => ∀ i : Fin 3, ∀ j : Fin n,
        Blk (x i.castSucc j.castSucc) (x i.castSucc j.succ) (x i.succ j.castSucc) (x i.succ j.succ))
      (q := fun y : Fin (n + 1) → R => Walk y)
      (fun x => ⟨fun h => ⟨fun _ => trivial, fun j => (compat_enc _ _).mpr (fun i => h i j)⟩,
        fun h i j => (compat_enc _ _).mp (h.2 j) i⟩)), Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.card_filter]
  have h1 : (∑ x : Fin (n + 1) → R, if Walk x then 1 else 0) = ∑ s : R, if init s then F n s else 0 := by
    unfold F
    simp only [init, if_true]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    have hh : ∀ s : R, (if Walk y ∧ y 0 = s then 1 else 0) = if y 0 = s then (if Walk y then 1 else 0) else 0 := by
      intro s
      by_cases h : y 0 = s
      · rw [if_pos h]; exact if_congr ⟨fun hh => hh.1, fun hh => ⟨hh, h⟩⟩ rfl rfl
      · rw [if_neg h, if_neg (show ¬(Walk y ∧ y 0 = s) from fun hh => h hh.2)]
    rw [Finset.sum_congr rfl (fun s _ => hh s), Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  rw [h1]
  push_cast
  simp only [F_eq]
  rw [sum_cls (W n) init]
  simp only [tot]

theorem a_shift (i : Fin 6) (n : ℕ) : (a (n + i) : ℤ) = ∑ c, U i c * W n c := by
  rw [a_eq, W_shift]

theorem a_rec (n : ℕ) : ∑ i : Fin 6, L i * (a (n + i) : ℤ) = 0 := by
  simp only [a_shift, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ c, ∑ i, L i * (U i c * W n c) = Rm 0 c * W n c := by
    intro c
    rw [← hL c, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [h]
  exact W_inv n 0

theorem a_val (i : Fin 6) : (a i : ℤ) = vals i := by
  have h := a_shift i 0
  rw [Nat.zero_add] at h
  rw [h, ← hV i]
  apply Finset.sum_congr rfl
  intro c _
  simp [W]

theorem rec0 (n : ℕ) : (a (n + 4) : ℤ) = 4 * (a (n + 3) : ℤ) - 6 * (a (n + 2) : ℤ) + 4 * (a (n + 1) : ℤ) - (a (n) : ℤ) := by
  have h := a_rec n
  simp [Fin.sum_univ_succ, L] at h
  linarith

theorem v0 : a 0 = 256 := by
  have h := a_val 0
  simp [vals] at h
  exact_mod_cast h

theorem v1 : a 1 = 2002 := by
  have h := a_val 1
  simp [vals] at h
  exact_mod_cast h

theorem v2 : a 2 = 6812 := by
  have h := a_val 2
  simp [vals] at h
  exact_mod_cast h

theorem v3 : a 3 = 16262 := by
  have h := a_val 3
  simp [vals] at h
  exact_mod_cast h

theorem v4 : a 4 = 31928 := by
  have h := a_val 4
  simp [vals] at h
  exact_mod_cast h

theorem v5 : a 5 = 55386 := by
  have h := a_val 5
  simp [vals] at h
  exact_mod_cast h

theorem conj1 : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 788 / 3 * (n : ℚ) ^ 3 + 744 * (n : ℚ) ^ 2 + 2218 / 3 * (n : ℚ) + 256 := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hs : n < 5
    · interval_cases n <;> norm_num [v1, v2, v3, v4]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
      have g0 := ih (k + 1) (by omega) (by omega)
      have g1 := ih (k + 2) (by omega) (by omega)
      have g2 := ih (k + 3) (by omega) (by omega)
      have g3 := ih (k + 4) (by omega) (by omega)
      have hr : (a (k + 5) : ℚ) = 4 * (a (k + 4) : ℚ) - 6 * (a (k + 3) : ℚ) + 4 * (a (k + 2) : ℚ) - (a (k + 1) : ℚ) := by exact_mod_cast rec0 (k + 1)
      rw [hr, g3, g2, g1, g0]
      push_cast
      ring

theorem conj2 : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  set F' := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
  have e1 : F' * ((1 - PowerSeries.X) ^ 4) =
      F' - PowerSeries.C (4 : ℚ) * (PowerSeries.X ^ 1 * F') + PowerSeries.C (6 : ℚ) * (PowerSeries.X ^ 2 * F') - PowerSeries.C (4 : ℚ) * (PowerSeries.X ^ 3 * F') + PowerSeries.X ^ 4 * F' := by
    simp only [map_ofNat]
    ring
  have e2 : (2 * PowerSeries.X * (1001 - 598 * PowerSeries.X + 513 * PowerSeries.X ^ 2 - 128 * PowerSeries.X ^ 3) : PowerSeries ℚ) =
      PowerSeries.C (2002 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.C (1196 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (1026 : ℚ) * PowerSeries.X ^ 3 - PowerSeries.C (256 : ℚ) * PowerSeries.X ^ 4 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  simp only [F', map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
  by_cases hn : n ≤ 4
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4]
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 5 := ⟨n - 5, by omega⟩
    have h1 : (a (j + 5) : ℚ) = 4 * (a (j + 4) : ℚ) - 6 * (a (j + 3) : ℚ) + 4 * (a (j + 2) : ℚ) - (a (j + 1) : ℚ) := by exact_mod_cast rec0 (j + 1)
    simp
    linear_combination h1

theorem conj3 : ∀ n : ℕ, 4 < n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  rw [show k + 5 - 1 = k + 4 from by omega, show k + 5 - 2 = k + 3 from by omega, show k + 5 - 3 = k + 2 from by omega, show k + 5 - 4 = k + 1 from by omega]
  have h1 : (a (k + 5) : ℤ) = 4 * (a (k + 4) : ℤ) - 6 * (a (k + 3) : ℤ) + 4 * (a (k + 2) : ℤ) - (a (k + 1) : ℤ) := rec0 (k + 1)
  linear_combination h1

end OMAA250880Helpers

open OMA.S_oeis_a250880 OMAA250880Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a250880.main :=
  ⟨conj1, conj2, conj3⟩

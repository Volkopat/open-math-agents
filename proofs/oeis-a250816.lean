import OMAStatements.S_oeis_a250816
import Mathlib

-- Proof of the conjectures in OEIS A250816 (statement by @ivillar).
-- Idea: the conditions only involve 2 X 2 blocks, so the count is a walk count on the columns of the
-- array (transfer matrix). The 243 states are lumped into 35 classes with constant numbers of successors in
-- each class (checked by decide), which gives a linear system for the class counts W n c. The recurrence
-- of order 5 follows from explicit row vectors orthogonal to all W n (an invariant subspace of the
-- transposed class matrix), and the generating function and closed forms follow from the recurrence
-- and the first values.

namespace OMAA250816Helpers

open OMA.S_oeis_a250816

instance (p q r s : ℕ) : Decidable (Blk p q r s) := by
  unfold Blk; infer_instance

/-- The states of the transfer matrix: the columns of the array, encoded as numbers in base 3
(digit j of the code is entry j). -/
abbrev R := Fin (3 ^ 5)

/-- Digit j of the code a in base 3. -/
def dig (a j : ℕ) : ℕ := a / 3 ^ j % 3

/-- Consecutive columns u, v: all the 2 X 2 blocks they form satisfy the condition. -/
abbrev BlockOK (u v : Fin 5 → Fin 3) : Prop :=
  ∀ i : Fin 4, Blk (u i.castSucc) (v i.castSucc) (u i.succ) (v i.succ)

/-- The truth table of `Blk` on entries below 3: bit ((p * 3 + q) * 3 + r) * 3 + s. -/
def blkTab : ℕ := 1469163389093655077735735

/-- `Blk` read off the truth table. -/
def blkB (p q r s : ℕ) : Bool := Nat.testBit blkTab (((p * 3 + q) * 3 + r) * 3 + s)

theorem blk_iff : ∀ p q r s : Fin 3, blkB p q r s = true ↔ Blk p q r s := by decide +kernel

/-- The same condition on codes. -/
def compatB (r s : ℕ) : Bool :=
  blkB (dig r 0) (dig s 0) (dig r 1) (dig s 1) &&
    (blkB (dig r 1) (dig s 1) (dig r 2) (dig s 2) &&
    (blkB (dig r 2) (dig s 2) (dig r 3) (dig s 3) &&
    (blkB (dig r 3) (dig s 3) (dig r 4) (dig s 4))))

abbrev compatN (r s : ℕ) : Prop := compatB r s = true

/-- States are unconstrained. -/
abbrev ok (_r : R) : Prop := True

/-- Every state may start a walk. -/
abbrev init (_r : R) : Prop := True

/-- Compatibility of consecutive states. -/
abbrev compat (r s : R) : Prop := compatN r.val s.val

theorem dig_enc (u : Fin 5 → Fin 3) (i : Fin 5) : dig ((finFunctionFinEquiv (m := 3) (n := 5)) u).val i.val = (u i).val :=
  congrArg Fin.val (congrFun (Equiv.symm_apply_apply (finFunctionFinEquiv (m := 3) (n := 5)) u) i)

theorem dig_e0 (u : Fin 5 → Fin 3) : dig ((finFunctionFinEquiv (m := 3) (n := 5)) u).val 0 = (u 0).val := dig_enc u 0

theorem dig_e1 (u : Fin 5 → Fin 3) : dig ((finFunctionFinEquiv (m := 3) (n := 5)) u).val 1 = (u 1).val := dig_enc u 1

theorem dig_e2 (u : Fin 5 → Fin 3) : dig ((finFunctionFinEquiv (m := 3) (n := 5)) u).val 2 = (u 2).val := dig_enc u 2

theorem dig_e3 (u : Fin 5 → Fin 3) : dig ((finFunctionFinEquiv (m := 3) (n := 5)) u).val 3 = (u 3).val := dig_enc u 3

theorem dig_e4 (u : Fin 5 → Fin 3) : dig ((finFunctionFinEquiv (m := 3) (n := 5)) u).val 4 = (u 4).val := dig_enc u 4


theorem blockOK_iff (u v : Fin 5 → Fin 3) :
    BlockOK u v ↔
      (Blk (u 0) (v 0) (u 1) (v 1) ∧
      (Blk (u 1) (v 1) (u 2) (v 2) ∧
      (Blk (u 2) (v 2) (u 3) (v 3) ∧
      (Blk (u 3) (v 3) (u 4) (v 4))))) := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3⟩
  · rintro ⟨h0, h1, h2, h3⟩ j
    fin_cases j <;>
      first
        | exact h0
        | exact h1
        | exact h2
        | exact h3

theorem compat_enc (u v : Fin 5 → Fin 3) :
    compat ((finFunctionFinEquiv (m := 3) (n := 5)) u) ((finFunctionFinEquiv (m := 3) (n := 5)) v) ↔ BlockOK u v := by
  rw [blockOK_iff]
  simp only [compat, compatN, compatB, Bool.and_eq_true, dig_e0, dig_e1, dig_e2, dig_e3, dig_e4, blk_iff]

/-- Arrays as sequences of encoded columns. -/
def enc (n : ℕ) : (Fin 5 → Fin (n + 1) → Fin 3) ≃ (Fin (n + 1) → R) where
  toFun := fun x j => (finFunctionFinEquiv (m := 3) (n := 5)) (fun i => x i j)
  invFun := fun y i j => (finFunctionFinEquiv (m := 3) (n := 5)).symm (y j) i
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
def clsTab : ℕ := 12496874967574198940016019066399098898739317592151127177801641333052681533180035257945171982941985586726860072291545371159704319694465372996068880972250657590980255642280453612686219449588839724203762260762475091276143387426930440959608168525946891675993194834614479884352345959287188961596127008042481341479875988126831098455288466606788575442790430669118595123260883098453548243083929263847364141420545094929194460676500737486510258169915700642904942340877579683140523888281570388529327762786526799996888468416306853901145399499583162841405583466114934100747240865285806605045534464

/-- The class of a code (states of one class have the same numbers of successors in each class). -/
def clsF (a : ℕ) : Fin 35 := ⟨(clsTab >>> (8 * a)) % 256 % 35, Nat.mod_lt _ (by norm_num)⟩

/-- The class of a state. -/
def cls (t : R) : Fin 35 := clsF t.val

/-- The codes of the states of each class. -/
def mem : Fin 35 → List ℕ :=
  ![[0], [81, 84, 85, 90, 93, 94, 108, 111, 112, 117, 120, 121], [162, 165, 166, 168, 169, 170, 171, 174, 175, 177, 178, 179, 180, 183, 184, 186, 187, 188, 189, 192, 193, 195, 196, 197, 198, 201, 202, 204, 205, 206, 207, 210, 211, 213, 214, 215, 216, 219, 220, 222, 223, 224, 225, 228, 229, 231, 232, 233, 234, 237, 238, 240, 241, 242], [27, 30, 31, 36, 39, 40, 82, 91, 109, 118], [54, 57, 58, 60, 61, 62, 63, 66, 67, 69, 70, 71, 72, 75, 76, 78, 79, 80, 164, 173, 182, 191, 200, 209, 218, 227, 236], [135, 138, 139, 141, 142, 143, 144, 147, 148, 150, 151, 152, 153, 156, 157, 159, 160, 161, 163, 167, 172, 176, 181, 185, 190, 194, 199, 203, 208, 212, 217, 221, 226, 230, 235, 239], [9, 12, 13], [18, 21, 22, 24, 25, 26], [99, 102, 103, 105, 106, 107, 126, 129, 130, 132, 133, 134], [45, 48, 49, 51, 52, 53], [3, 4], [6, 7, 8], [87, 88, 89, 96, 97, 98, 114, 115, 116, 123, 124, 125], [33, 34, 35, 42, 43, 44], [15, 16, 17], [1], [28, 37], [55, 59, 64, 68, 73, 77, 137, 146, 155], [136, 140, 145, 149, 154, 158], [10], [19, 23], [100, 104, 127, 131], [46, 50], [2], [83, 92, 110, 119], [29, 38], [56, 65, 74], [11], [20], [101, 128], [47], [5], [86, 95, 113, 122], [32, 41], [14]]

/-- Mat c d: the number of successors of class d of a state of class c. -/
def Mat : Fin 35 → Fin 35 → ℤ :=
  ![![1, 5, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 5, 1, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2, 9, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 3, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 3, 12, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 5, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 5, 15, 3, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 1, 5, 2, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2, 9, 2, 0, 7, 1, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 3, 0, 0, 3, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 2, 0, 0, 3, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 5, 15, 3, 6, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 1, 5, 1, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 5, 2, 3, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2, 9, 2, 5, 7, 1, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 3, 0, 3, 3, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0],
    ![0, 0, 2, 0, 2, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 2, 0, 2, 3, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0],
    ![0, 3, 12, 0, 0, 6, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0],
    ![0, 1, 5, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 1, 5, 1, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0],
    ![0, 2, 9, 0, 0, 5, 1, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1]]

/-- W n c: the number of walks with n steps starting at a given state of class c. -/
def W : ℕ → Fin 35 → ℤ
  | 0 => fun _ => 1
  | n + 1 => fun c => ∑ d, Mat c d * W n d

theorem hmem_0 : ∀ c : Fin 35, 0 ≤ c.val → c.val < 4 →
    mem c = (List.range (3 ^ 5)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_1 : ∀ c : Fin 35, 4 ≤ c.val → c.val < 8 →
    mem c = (List.range (3 ^ 5)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_2 : ∀ c : Fin 35, 8 ≤ c.val → c.val < 12 →
    mem c = (List.range (3 ^ 5)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_3 : ∀ c : Fin 35, 12 ≤ c.val → c.val < 16 →
    mem c = (List.range (3 ^ 5)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_4 : ∀ c : Fin 35, 16 ≤ c.val → c.val < 20 →
    mem c = (List.range (3 ^ 5)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_5 : ∀ c : Fin 35, 20 ≤ c.val → c.val < 24 →
    mem c = (List.range (3 ^ 5)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_6 : ∀ c : Fin 35, 24 ≤ c.val → c.val < 28 →
    mem c = (List.range (3 ^ 5)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_7 : ∀ c : Fin 35, 28 ≤ c.val → c.val < 32 →
    mem c = (List.range (3 ^ 5)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_8 : ∀ c : Fin 35, 32 ≤ c.val → c.val < 35 →
    mem c = (List.range (3 ^ 5)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem : ∀ c : Fin 35, mem c = (List.range (3 ^ 5)).filter (fun a => clsF a = c) := fun c =>
  if h4 : c.val < 16 then
    if h2 : c.val < 8 then
      if h1 : c.val < 4 then
        hmem_0 c (Nat.zero_le _) h1
      else
        hmem_1 c (Nat.le_of_not_lt h1) h2
    else
      if h3 : c.val < 12 then
        hmem_2 c (Nat.le_of_not_lt h2) h3
      else
        hmem_3 c (Nat.le_of_not_lt h3) h4
  else
    if h6 : c.val < 24 then
      if h5 : c.val < 20 then
        hmem_4 c (Nat.le_of_not_lt h4) h5
      else
        hmem_5 c (Nat.le_of_not_lt h5) h6
    else
      if h7 : c.val < 28 then
        hmem_6 c (Nat.le_of_not_lt h6) h7
      else
        if h8 : c.val < 32 then
          hmem_7 c (Nat.le_of_not_lt h7) h8
        else
          hmem_8 c (Nat.le_of_not_lt h8) c.isLt

set_option maxHeartbeats 0 in
theorem cntN : ∀ s : R, ∀ c : Fin 35,
    (((mem c).filter (fun a => compatB s.val a)).length : ℤ) = Mat (cls s) c := by
  have h_0 : ∀ a ∈ List.range' 0 24, ∀ c : Fin 35,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_1 : ∀ a ∈ List.range' 24 24, ∀ c : Fin 35,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_2 : ∀ a ∈ List.range' 48 24, ∀ c : Fin 35,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_3 : ∀ a ∈ List.range' 72 24, ∀ c : Fin 35,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_4 : ∀ a ∈ List.range' 96 24, ∀ c : Fin 35,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_5 : ∀ a ∈ List.range' 120 24, ∀ c : Fin 35,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_6 : ∀ a ∈ List.range' 144 24, ∀ c : Fin 35,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_7 : ∀ a ∈ List.range' 168 24, ∀ c : Fin 35,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_8 : ∀ a ∈ List.range' 192 24, ∀ c : Fin 35,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_9 : ∀ a ∈ List.range' 216 24, ∀ c : Fin 35,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  have h_10 : ∀ a ∈ List.range' 240 3, ∀ c : Fin 35,
      (((mem c).filter (fun b => compatB a b)).length : ℤ) = Mat (clsF a) c := by decide +kernel
  exact fun s c =>
    if h5 : s.val < 120 then
      if h2 : s.val < 48 then
        if h1 : s.val < 24 then
          h_0 s.val (List.mem_range'_1.mpr ⟨(Nat.zero_le _), h1⟩) c
        else
          h_1 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h1), h2⟩) c
      else
        if h3 : s.val < 72 then
          h_2 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h2), h3⟩) c
        else
          if h4 : s.val < 96 then
            h_3 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h3), h4⟩) c
          else
            h_4 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h4), h5⟩) c
    else
      if h8 : s.val < 192 then
        if h6 : s.val < 144 then
          h_5 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h5), h6⟩) c
        else
          if h7 : s.val < 168 then
            h_6 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h6), h7⟩) c
          else
            h_7 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h7), h8⟩) c
      else
        if h9 : s.val < 216 then
          h_8 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h8), h9⟩) c
        else
          if h10 : s.val < 240 then
            h_9 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h9), h10⟩) c
          else
            h_10 s.val (List.mem_range'_1.mpr ⟨(Nat.le_of_not_lt h10), s.isLt⟩) c

/-- U i: the row vector (class sizes) * Mat^i. -/
def U : Fin 7 → Fin 35 → ℤ :=
  ![![1, 12, 54, 10, 27, 36, 3, 6, 12, 6, 2, 3, 12, 6, 3, 1, 2, 9, 6, 1, 2, 4, 2, 1, 4, 2, 3, 1, 1, 2, 1, 1, 4, 2, 1],
    ![3, 72, 618, 34, 80, 304, 6, 9, 66, 9, 3, 3, 39, 6, 3, 2, 4, 20, 37, 2, 3, 20, 3, 1, 11, 2, 3, 1, 1, 6, 1, 1, 13, 2, 1],
    ![6, 200, 2397, 74, 173, 941, 10, 13, 164, 13, 4, 3, 68, 6, 3, 3, 6, 31, 86, 3, 4, 45, 4, 1, 18, 2, 3, 1, 1, 10, 1, 1, 23, 2, 1],
    ![10, 420, 6384, 130, 306, 2109, 15, 18, 321, 18, 5, 3, 99, 6, 3, 4, 8, 42, 153, 4, 5, 79, 5, 1, 25, 2, 3, 1, 1, 14, 1, 1, 34, 2, 1],
    ![15, 756, 13884, 202, 479, 3970, 21, 24, 552, 24, 6, 3, 132, 6, 3, 5, 10, 53, 238, 5, 6, 122, 6, 1, 32, 2, 3, 1, 1, 18, 1, 1, 46, 2, 1],
    ![21, 1232, 26514, 290, 692, 6686, 28, 31, 872, 31, 7, 3, 167, 6, 3, 6, 12, 64, 341, 6, 7, 174, 7, 1, 39, 2, 3, 1, 1, 22, 1, 1, 59, 2, 1],
    ![28, 1872, 46203, 394, 945, 10419, 36, 39, 1296, 39, 8, 3, 204, 6, 3, 7, 14, 75, 462, 7, 8, 235, 8, 1, 46, 2, 3, 1, 1, 26, 1, 1, 73, 2, 1]]

theorem totN : ∀ c : Fin 35, ((mem c).length : ℤ) = U 0 c := by decide +kernel

theorem card_cls (c : Fin 35) (P : ℕ → Prop) [DecidablePred P] :
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

theorem cnt : ∀ s : R, ∀ c : Fin 35,
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

theorem tot : ∀ c : Fin 35,
    ((Finset.univ.filter (fun t : R => cls t = c ∧ init t)).card : ℤ) = U 0 c := by
  intro c
  have h2 : Finset.univ.filter (fun t : R => cls t = c ∧ init t) =
      Finset.univ.filter (fun t : R => cls t = c ∧ (fun _ : ℕ => True) t.val) :=
    Finset.filter_congr (fun t _ => Iff.rfl)
  rw [h2, card_cls c (fun _ : ℕ => True)]
  simpa using totN c

theorem hU0 : ∀ d : Fin 35, ∑ c, U 0 c * Mat c d = U 1 d := by decide +kernel

theorem hU1 : ∀ d : Fin 35, ∑ c, U 1 c * Mat c d = U 2 d := by decide +kernel

theorem hU2 : ∀ d : Fin 35, ∑ c, U 2 c * Mat c d = U 3 d := by decide +kernel

theorem hU3 : ∀ d : Fin 35, ∑ c, U 3 c * Mat c d = U 4 d := by decide +kernel

theorem hU4 : ∀ d : Fin 35, ∑ c, U 4 c * Mat c d = U 5 d := by decide +kernel

theorem hU5 : ∀ d : Fin 35, ∑ c, U 5 c * Mat c d = U 6 d := by decide +kernel

theorem hU : ∀ (i : Fin 6) (d : Fin 35), ∑ c, U i.castSucc c * Mat c d = U i.succ d := by
  intro i d
  fin_cases i
  · exact hU0 d
  · exact hU1 d
  · exact hU2 d
  · exact hU3 d
  · exact hU4 d
  · exact hU5 d

/-- Coefficients of the recurrence. -/
def L : Fin 7 → ℤ := ![-1, 5, -10, 10, -5, 1, 0]

/-- Row vectors orthogonal to all the vectors W n. -/
def Rm : Fin 1 → Fin 35 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def Am : Fin 1 → Fin 1 → ℤ :=
  ![![0]]

theorem hRA : ∀ (l : Fin 1) (d : Fin 35), ∑ c, Rm l c * Mat c d = ∑ l', Am l l' * Rm l' d := by
  decide +kernel

theorem hR0 : ∀ l : Fin 1, ∑ c, Rm l c = 0 := by decide +kernel

theorem hL : ∀ c : Fin 35, ∑ i, L i * U i c = Rm 0 c := by decide +kernel

/-- The first values. -/
def vals : Fin 7 → ℤ := ![243, 1389, 4321, 10233, 20631, 37333, 62469]

theorem hV : ∀ i : Fin 7, ∑ c, U i c = vals i := by decide +kernel

theorem sum_cls (g : Fin 35 → ℤ) (P : R → Prop) [DecidablePred P] :
    (∑ t : R, if P t then g (cls t) else 0) =
      ∑ c : Fin 35, ((Finset.univ.filter (fun t => cls t = c ∧ P t)).card : ℤ) * g c := by
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

theorem swap_sum (f : Fin 35 → ℤ) (n : ℕ) :
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

theorem W_shift : ∀ (i : Fin 7) (n : ℕ), ∑ c, U 0 c * W (n + i) c = ∑ c, U i c * W n c := by
  intro i
  induction i using Fin.induction with
  | zero => intro n; simp
  | succ i ih =>
    intro n
    have h1 : n + ((i.succ : Fin 7) : ℕ) = (n + 1) + ((i.castSucc : Fin 7) : ℕ) := by
      simp only [Fin.val_succ, Fin.val_castSucc]; omega
    rw [h1, ih (n + 1), swap_sum]
    simp only [hU]

theorem a_eq (n : ℕ) : (a n : ℤ) = ∑ c, U 0 c * W n c := by
  unfold a
  rw [Nat.card_congr (Equiv.subtypeEquiv (enc n)
      (p := fun x : Fin 5 → Fin (n + 1) → Fin 3 => ∀ i : Fin 4, ∀ j : Fin n,
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

theorem a_shift (i : Fin 7) (n : ℕ) : (a (n + i) : ℤ) = ∑ c, U i c * W n c := by
  rw [a_eq, W_shift]

theorem a_rec (n : ℕ) : ∑ i : Fin 7, L i * (a (n + i) : ℤ) = 0 := by
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

theorem a_val (i : Fin 7) : (a i : ℤ) = vals i := by
  have h := a_shift i 0
  rw [Nat.zero_add] at h
  rw [h, ← hV i]
  apply Finset.sum_congr rfl
  intro c _
  simp [W]

theorem rec0 (n : ℕ) : (a (n + 5) : ℤ) = 5 * (a (n + 4) : ℤ) - 10 * (a (n + 3) : ℤ) + 10 * (a (n + 2) : ℤ) - 5 * (a (n + 1) : ℤ) + (a (n) : ℤ) := by
  have h := a_rec n
  simp [Fin.sum_univ_succ, L] at h
  linarith

theorem v0 : a 0 = 243 := by
  have h := a_val 0
  simp [vals] at h
  exact_mod_cast h

theorem v1 : a 1 = 1389 := by
  have h := a_val 1
  simp [vals] at h
  exact_mod_cast h

theorem v2 : a 2 = 4321 := by
  have h := a_val 2
  simp [vals] at h
  exact_mod_cast h

theorem v3 : a 3 = 10233 := by
  have h := a_val 3
  simp [vals] at h
  exact_mod_cast h

theorem v4 : a 4 = 20631 := by
  have h := a_val 4
  simp [vals] at h
  exact_mod_cast h

theorem v5 : a 5 = 37333 := by
  have h := a_val 5
  simp [vals] at h
  exact_mod_cast h

theorem v6 : a 6 = 62469 := by
  have h := a_val 6
  simp [vals] at h
  exact_mod_cast h

theorem conj1 : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 13 * (n : ℚ) ^ 4 + 121 * (n : ℚ) ^ 3 + 439 * (n : ℚ) ^ 2 + 573 * (n : ℚ) + 243 := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hs : n < 6
    · interval_cases n <;> norm_num [v1, v2, v3, v4, v5]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
      have g0 := ih (k + 1) (by omega) (by omega)
      have g1 := ih (k + 2) (by omega) (by omega)
      have g2 := ih (k + 3) (by omega) (by omega)
      have g3 := ih (k + 4) (by omega) (by omega)
      have g4 := ih (k + 5) (by omega) (by omega)
      have hr : (a (k + 6) : ℚ) = 5 * (a (k + 5) : ℚ) - 10 * (a (k + 4) : ℚ) + 10 * (a (k + 3) : ℚ) - 5 * (a (k + 2) : ℚ) + (a (k + 1) : ℚ) := by exact_mod_cast rec0 (k + 1)
      rw [hr, g4, g3, g2, g1, g0]
      push_cast
      ring

theorem conj2 : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  set F' := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
  have e1 : F' * ((1 - PowerSeries.X) ^ 5) =
      F' - PowerSeries.C (5 : ℚ) * (PowerSeries.X ^ 1 * F') + PowerSeries.C (10 : ℚ) * (PowerSeries.X ^ 2 * F') - PowerSeries.C (10 : ℚ) * (PowerSeries.X ^ 3 * F') + PowerSeries.C (5 : ℚ) * (PowerSeries.X ^ 4 * F') - PowerSeries.X ^ 5 * F' := by
    simp only [map_ofNat]
    ring
  have e2 : (PowerSeries.X * (1389 - 2624 * PowerSeries.X + 2518 * PowerSeries.X ^ 2 - 1214 * PowerSeries.X ^ 3 + 243 * PowerSeries.X ^ 4) : PowerSeries ℚ) =
      PowerSeries.C (1389 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.C (2624 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (2518 : ℚ) * PowerSeries.X ^ 3 - PowerSeries.C (1214 : ℚ) * PowerSeries.X ^ 4 + PowerSeries.C (243 : ℚ) * PowerSeries.X ^ 5 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  simp only [F', map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
  by_cases hn : n ≤ 5
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5]
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 6 := ⟨n - 6, by omega⟩
    have h1 : (a (j + 6) : ℚ) = 5 * (a (j + 5) : ℚ) - 10 * (a (j + 4) : ℚ) + 10 * (a (j + 3) : ℚ) - 5 * (a (j + 2) : ℚ) + (a (j + 1) : ℚ) := by exact_mod_cast rec0 (j + 1)
    simp
    linear_combination h1

theorem conj3 : ∀ n : ℕ, 5 < n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  rw [show k + 6 - 1 = k + 5 from by omega, show k + 6 - 2 = k + 4 from by omega, show k + 6 - 3 = k + 3 from by omega, show k + 6 - 4 = k + 2 from by omega, show k + 6 - 5 = k + 1 from by omega]
  have h1 : (a (k + 6) : ℤ) = 5 * (a (k + 5) : ℤ) - 10 * (a (k + 4) : ℤ) + 10 * (a (k + 3) : ℤ) - 5 * (a (k + 2) : ℤ) + (a (k + 1) : ℤ) := rec0 (k + 1)
  linear_combination h1

end OMAA250816Helpers

open OMA.S_oeis_a250816 OMAA250816Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a250816.main :=
  ⟨conj1, conj2, conj3⟩

import OMAStatements.S_oeis_a250855
import Mathlib

-- Proof of the conjectures in OEIS A250855 (statement by @ivillar).
-- Idea: the conditions involve only consecutive columns, so the count is a walk count on the
-- 256 possible columns (transfer matrix). The states fall into 55 classes such that the number of successors
-- of a state in each class depends only on its own class (checked by a kernel computation, with the
-- class counts of each state packed into one base-512 number). The class-count vectors V(0), V(1), ...
-- then satisfy a linear recurrence with a 56 X 56 matrix, whose first iterates are computed
-- explicitly; they satisfy the conjectured recurrence, and so do all later ones by linearity.
-- The g.f. and the closed form follow from the recurrence and the first values.

namespace OMAA250855Helpers

open OMA.S_oeis_a250855

abbrev R := Fin 4 → Fin 4

instance (p q r s : ℤ) : Decidable (CellOK p q r s) := by unfold CellOK; infer_instance

/-- No constraint on a single state. -/
def RowOK (_r : R) : Prop := True

instance : DecidablePred RowOK := fun r => by unfold RowOK; infer_instance

/-- Consecutive columns u, v: all the subblocks they form satisfy the condition. -/
def Compat (u v : R) : Prop := ∀ i : Fin 3, CellOK ((u i.castSucc : ℕ) : ℤ) ((v i.castSucc : ℕ) : ℤ) ((u i.succ : ℕ) : ℤ) ((v i.succ : ℕ) : ℤ)

instance (u v : R) : Decidable (Compat u v) := by unfold Compat; infer_instance

/-- No constraint on the first state. -/
def Init (_r : R) : Prop := True

instance : DecidablePred Init := fun r => by unfold Init; infer_instance

abbrev ok (r : R) : Prop := RowOK r

abbrev compat (r s : R) : Prop := Compat r s

abbrev Walk {n : ℕ} (x : Fin (n + 1) → R) : Prop :=
  (∀ i, ok (x i)) ∧ ∀ i : Fin n, compat (x i.castSucc) (x i.succ)

theorem walk_cons (n : ℕ) (r : R) (y : Fin (n + 1) → R) :
    Walk (Fin.cons r y : Fin (n + 2) → R) ↔ ok r ∧ compat r (y 0) ∧ Walk y := by
  simp only [Walk, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.castSucc_zero,
    ← Fin.succ_castSucc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨h1, ?_, h2, h4⟩
    simpa using h3
  · rintro ⟨h1, h3, h2, h4⟩
    refine ⟨⟨h1, h2⟩, ?_, h4⟩
    simpa using h3

/-- Number of walks with n+1 states starting at s. -/
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

/-- Decoding of a state from its index (base 4 digits). -/
def dec (i : ℕ) : R := fun k => ⟨i / 4 ^ (k : ℕ) % 4, Nat.mod_lt _ (by norm_num)⟩

/-- Index of a state. -/
def enc (r : R) : ℕ := (r 0 : ℕ) + 4 * ((r 1 : ℕ) + 4 * ((r 2 : ℕ) + 4 * ((r 3 : ℕ))))

theorem dec_enc : ∀ r : R, dec (enc r) = r := by decide +kernel

theorem enc_lt : ∀ r : R, enc r < 256 := by decide +kernel

theorem enc_dec : ∀ i < 256, enc (dec i) = i := by decide +kernel

theorem sum_R (g : R → ℕ) : ∑ t : R, g t = ∑ i ∈ Finset.range 256, g (dec i) := by
  refine Finset.sum_nbij' (fun t => enc t) (fun i => dec i) ?_ ?_ ?_ ?_ ?_
  · intro t _; exact Finset.mem_range.mpr (enc_lt t)
  · intro i _; exact Finset.mem_univ _
  · intro t _; exact dec_enc t
  · intro i hi; exact enc_dec i (Finset.mem_range.mp hi)
  · intro t _; rw [dec_enc]

/-- Class of the state with index i (a table in base 64): states of one class have the same numbers
of successors in every class. -/
def clsN (i : ℕ) : ℕ := 2065982075728469840759487860013745402012145146488372545996159226591924905241378293749106651632577605050899265157950221771095385931509558816598814305187047495457124849476356242186287783415332249732945578760149731583297054420301510811332926961923695774657690968776375654371896219609837868132828479375006876776268849141467063672930405225460676547038913864228869397069089673174856161290226280130099342221072544280380177593990559548252402519888090835837759228744572992 / 64 ^ i % 64

def cls (r : R) : ℕ := clsN (enc r)

/-- Class transition counts; the last row (index 55) counts the admissible first states by class. -/
def MXL : List (List ℕ) := [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 0, 0, 0, 0, 20, 0],
  [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 1, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 10, 0, 0, 1, 0, 9, 0, 20, 0],
  [1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 1, 1, 0, 0, 0, 5, 0, 0, 0, 0, 0, 7, 0, 0, 10, 0, 2, 1, 0, 9, 0, 20, 0],
  [1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 4, 2, 2, 1, 1, 0, 0, 0, 5, 0, 0, 0, 0, 0, 7, 0, 0, 10, 3, 2, 1, 0, 9, 0, 20, 0],
  [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 3, 0, 0, 16, 0],
  [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 1, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 2, 3, 7, 0, 16, 0],
  [0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 2, 2, 1, 0, 3, 0, 0, 0, 0, 0, 4, 0, 0, 7, 0, 3, 2, 3, 7, 0, 16, 0],
  [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 10, 0],
  [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 4, 4, 0, 10, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 4, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 6, 0, 10, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 6, 2, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 12, 3, 10, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 6, 2, 0, 1, 0, 0, 5, 2, 0, 4, 0, 1, 0, 0, 12, 3, 10, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 3, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 6, 2, 1, 1, 0, 0, 5, 2, 0, 4, 2, 1, 0, 0, 12, 3, 10, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 5, 1, 0, 0, 1, 0, 0, 0, 0, 4, 0, 0, 1, 0, 11, 2, 10, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 5, 1, 0, 1, 1, 0, 3, 1, 0, 4, 0, 2, 1, 0, 11, 2, 10, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 3, 0, 7, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 2, 0, 0, 0, 2, 0, 0, 2, 2, 6, 1, 7, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 3, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 3, 0, 4, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 3, 2, 0, 1, 0, 0, 0, 0, 6, 2, 4, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 6, 4, 2, 1, 0, 0, 0, 0, 6, 2, 4, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 1, 1, 0, 0, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0, 0, 6, 4, 2, 1, 1, 0, 0, 0, 6, 2, 4, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0, 5, 3, 1, 1, 0, 1, 0, 0, 6, 2, 4, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 3, 1, 0, 1, 0, 0, 1, 0, 5, 1, 4, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 0, 2, 1, 1, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 0, 2, 1, 1, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 10, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 5, 0, 0, 4, 0, 1, 0, 0, 6, 0, 10, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 5, 0, 0, 4, 2, 1, 0, 0, 6, 0, 10, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 1, 0, 5, 0, 10, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 3, 0, 0, 4, 0, 2, 1, 0, 5, 0, 10, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 7, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 2, 3, 0, 7, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 3, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 4, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 6, 2, 4, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0, 0, 0, 3, 2, 0, 1, 1, 0, 0, 0, 6, 2, 4, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 1, 0, 0, 2, 1, 0, 1, 0, 1, 0, 0, 6, 2, 4, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 5, 1, 4, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 2, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 1, 0, 0, 0, 0, 0, 2, 1, 1, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 4, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0, 0, 1, 1, 0, 0, 0, 3, 0, 4, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 3, 0, 4, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 2, 0, 4, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
  [1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 5, 1, 1, 1, 1, 1, 3, 1, 4, 9, 3, 1, 1, 1, 1, 4, 14, 4, 3, 1, 6, 2, 2, 2, 2, 6, 2, 8, 12, 2, 1, 1, 1, 4, 18, 5, 2, 18, 3, 3, 3, 12, 22, 3, 40, 0]]

def MX (k j : ℕ) : ℕ := (MXL.getD k []).getD j 0

theorem MX_lt : ∀ k < 56, ∀ j < 56, MX k j < 512 := by decide +kernel

theorem clsN_lt : ∀ i < 256, clsN i < 55 := by decide +kernel

theorem cls_lt (r : R) : cls r < 56 := by
  have := clsN_lt (enc r) (enc_lt r)
  unfold cls
  omega

/-- The successor classes of state i, packed into one base 512 number, agree with the class table. -/
def HashP (i : ℕ) : Prop :=
  (∑ t ∈ Finset.range 256, if ok (dec i) ∧ compat (dec i) (dec t) then 512 ^ clsN t else 0) =
    ∑ j ∈ Finset.range 56, MX (clsN i) j * 512 ^ j

instance : DecidablePred HashP := fun i => by unfold HashP; infer_instance

theorem hashS_0 : ∀ i < 9, 0 ≤ i → HashP i := by decide +kernel
theorem hashS_1 : ∀ i < 18, 9 ≤ i → HashP i := by decide +kernel
theorem hashS_2 : ∀ i < 27, 18 ≤ i → HashP i := by decide +kernel
theorem hashS_3 : ∀ i < 36, 27 ≤ i → HashP i := by decide +kernel
theorem hashS_4 : ∀ i < 45, 36 ≤ i → HashP i := by decide +kernel
theorem hashS_5 : ∀ i < 54, 45 ≤ i → HashP i := by decide +kernel
theorem hashS_6 : ∀ i < 63, 54 ≤ i → HashP i := by decide +kernel
theorem hashS_7 : ∀ i < 72, 63 ≤ i → HashP i := by decide +kernel
theorem hashS_8 : ∀ i < 81, 72 ≤ i → HashP i := by decide +kernel
theorem hashS_9 : ∀ i < 90, 81 ≤ i → HashP i := by decide +kernel
theorem hashS_10 : ∀ i < 99, 90 ≤ i → HashP i := by decide +kernel
theorem hashS_11 : ∀ i < 108, 99 ≤ i → HashP i := by decide +kernel
theorem hashS_12 : ∀ i < 117, 108 ≤ i → HashP i := by decide +kernel
theorem hashS_13 : ∀ i < 126, 117 ≤ i → HashP i := by decide +kernel
theorem hashS_14 : ∀ i < 135, 126 ≤ i → HashP i := by decide +kernel
theorem hashS_15 : ∀ i < 144, 135 ≤ i → HashP i := by decide +kernel
theorem hashS_16 : ∀ i < 153, 144 ≤ i → HashP i := by decide +kernel
theorem hashS_17 : ∀ i < 162, 153 ≤ i → HashP i := by decide +kernel
theorem hashS_18 : ∀ i < 171, 162 ≤ i → HashP i := by decide +kernel
theorem hashS_19 : ∀ i < 180, 171 ≤ i → HashP i := by decide +kernel
theorem hashS_20 : ∀ i < 189, 180 ≤ i → HashP i := by decide +kernel
theorem hashS_21 : ∀ i < 198, 189 ≤ i → HashP i := by decide +kernel
theorem hashS_22 : ∀ i < 207, 198 ≤ i → HashP i := by decide +kernel
theorem hashS_23 : ∀ i < 216, 207 ≤ i → HashP i := by decide +kernel
theorem hashS_24 : ∀ i < 225, 216 ≤ i → HashP i := by decide +kernel
theorem hashS_25 : ∀ i < 234, 225 ≤ i → HashP i := by decide +kernel
theorem hashS_26 : ∀ i < 243, 234 ≤ i → HashP i := by decide +kernel
theorem hashS_27 : ∀ i < 252, 243 ≤ i → HashP i := by decide +kernel
theorem hashS_28 : ∀ i < 256, 252 ≤ i → HashP i := by decide +kernel

theorem hashS : ∀ i < 256, HashP i := by
  intro i hi
  by_cases h0 : i < 9
  · exact hashS_0 i h0 (by omega)
  by_cases h1 : i < 18
  · exact hashS_1 i h1 (by omega)
  by_cases h2 : i < 27
  · exact hashS_2 i h2 (by omega)
  by_cases h3 : i < 36
  · exact hashS_3 i h3 (by omega)
  by_cases h4 : i < 45
  · exact hashS_4 i h4 (by omega)
  by_cases h5 : i < 54
  · exact hashS_5 i h5 (by omega)
  by_cases h6 : i < 63
  · exact hashS_6 i h6 (by omega)
  by_cases h7 : i < 72
  · exact hashS_7 i h7 (by omega)
  by_cases h8 : i < 81
  · exact hashS_8 i h8 (by omega)
  by_cases h9 : i < 90
  · exact hashS_9 i h9 (by omega)
  by_cases h10 : i < 99
  · exact hashS_10 i h10 (by omega)
  by_cases h11 : i < 108
  · exact hashS_11 i h11 (by omega)
  by_cases h12 : i < 117
  · exact hashS_12 i h12 (by omega)
  by_cases h13 : i < 126
  · exact hashS_13 i h13 (by omega)
  by_cases h14 : i < 135
  · exact hashS_14 i h14 (by omega)
  by_cases h15 : i < 144
  · exact hashS_15 i h15 (by omega)
  by_cases h16 : i < 153
  · exact hashS_16 i h16 (by omega)
  by_cases h17 : i < 162
  · exact hashS_17 i h17 (by omega)
  by_cases h18 : i < 171
  · exact hashS_18 i h18 (by omega)
  by_cases h19 : i < 180
  · exact hashS_19 i h19 (by omega)
  by_cases h20 : i < 189
  · exact hashS_20 i h20 (by omega)
  by_cases h21 : i < 198
  · exact hashS_21 i h21 (by omega)
  by_cases h22 : i < 207
  · exact hashS_22 i h22 (by omega)
  by_cases h23 : i < 216
  · exact hashS_23 i h23 (by omega)
  by_cases h24 : i < 225
  · exact hashS_24 i h24 (by omega)
  by_cases h25 : i < 234
  · exact hashS_25 i h25 (by omega)
  by_cases h26 : i < 243
  · exact hashS_26 i h26 (by omega)
  by_cases h27 : i < 252
  · exact hashS_27 i h27 (by omega)
  exact hashS_28 i hi (by omega)

theorem hashI :
    (∑ t ∈ Finset.range 256, if Init (dec t) then 512 ^ clsN t else 0) =
      ∑ j ∈ Finset.range 56, MX 55 j * 512 ^ j := by decide +kernel

theorem digits_unique (B : ℕ) (hB : 0 < B) : ∀ (c : ℕ) (n m : ℕ → ℕ), (∀ j < c, n j < B) →
    (∀ j < c, m j < B) →
    ∑ j ∈ Finset.range c, n j * B ^ j = ∑ j ∈ Finset.range c, m j * B ^ j → ∀ j < c, n j = m j := by
  intro c
  induction c with
  | zero => intro n m _ _ _ j hj; omega
  | succ c ih =>
    intro n m hn hm h j hj
    rw [Finset.sum_range_succ', Finset.sum_range_succ'] at h
    simp only [pow_zero, mul_one, pow_succ] at h
    have e1 : ∀ f : ℕ → ℕ, ∑ k ∈ Finset.range c, f (k + 1) * (B ^ k * B) =
        B * ∑ k ∈ Finset.range c, f (k + 1) * B ^ k := by
      intro f
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [e1 n, e1 m] at h
    have h0 : n 0 = m 0 := by
      have h' := congrArg (fun z => z % B) h
      simp only [Nat.mul_add_mod] at h'
      rwa [Nat.mod_eq_of_lt (hn 0 (by omega)), Nat.mod_eq_of_lt (hm 0 (by omega))] at h'
    have h1 : ∑ k ∈ Finset.range c, n (k + 1) * B ^ k = ∑ k ∈ Finset.range c, m (k + 1) * B ^ k := by
      rw [h0] at h
      exact Nat.eq_of_mul_eq_mul_left hB (Nat.add_right_cancel h)
    rcases j with _ | j
    · exact h0
    · exact ih (fun k => n (k + 1)) (fun k => m (k + 1)) (fun k hk => hn (k + 1) (by omega))
        (fun k hk => hm (k + 1) (by omega)) h1 j (by omega)

theorem sum_cls (P : R → Prop) [DecidablePred P] (f : ℕ → ℕ) :
    (∑ t : R, if P t then f (cls t) else 0) =
      ∑ j ∈ Finset.range 56, (Finset.univ.filter (fun t : R => P t ∧ cls t = j)).card * f j := by
  have h : ∀ j, (Finset.univ.filter (fun t : R => P t ∧ cls t = j)).card * f j =
      ∑ t : R, if P t ∧ cls t = j then f j else 0 := by
    intro j
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  by_cases hP : P t
  · simp only [hP, true_and, if_true]
    rw [Finset.sum_ite_eq (Finset.range 56) (cls t) f, if_pos (Finset.mem_range.mpr (cls_lt t))]
  · simp [hP]

theorem card_lt (P : R → Prop) [DecidablePred P] : (Finset.univ.filter P).card < 512 := by
  have h1 : (Finset.univ.filter P).card ≤ (Finset.univ : Finset R).card := Finset.card_filter_le _ _
  have h2 : (Finset.univ : Finset R).card = 256 := by
    rw [Finset.card_eq_sum_ones, sum_R]
    simp
  omega

/-- From the base 512 encoding to the class counts. -/
theorem counts_of_hash (P : R → Prop) [DecidablePred P] (k : ℕ)
    (h : (∑ t ∈ Finset.range 256, if P (dec t) then 512 ^ clsN t else 0) =
      ∑ j ∈ Finset.range 56, MX k j * 512 ^ j)
    (hk : ∀ j < 56, MX k j < 512) :
    ∀ j < 56, (Finset.univ.filter (fun t : R => P t ∧ cls t = j)).card = MX k j := by
  have e : (∑ t : R, if P t then 512 ^ cls t else 0) =
      ∑ j ∈ Finset.range 56, (Finset.univ.filter (fun t : R => P t ∧ cls t = j)).card * 512 ^ j :=
    sum_cls P (fun j => 512 ^ j)
  refine digits_unique 512 (by norm_num) 56
    (fun j => (Finset.univ.filter (fun t : R => P t ∧ cls t = j)).card) (fun j => MX k j)
    (fun j _ => card_lt _) hk ?_
  rw [← e, sum_R, ← h]
  apply Finset.sum_congr rfl
  intro t ht
  unfold cls
  rw [enc_dec t (Finset.mem_range.mp ht)]

/-- Initial class vector. -/
def L0 : List ℕ := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0]

/-- Walk counts by class; coordinate 55 at time n+1 is the number of admissible walks with n+1 states. -/
def V : ℕ → ℕ → ℕ
  | 0, j => L0.getD j 0
  | n + 1, i => ∑ j ∈ Finset.range 56, MX i j * V n j

theorem V_succ (n i : ℕ) : V (n + 1) i = ∑ j ∈ Finset.range 56, MX i j * V n j := rfl

theorem base_ok : ∀ i < 256, (if ok (dec i) then 1 else 0) = L0.getD (clsN i) 0 := by decide +kernel

theorem hashS' (s : R) :
    (∑ t ∈ Finset.range 256, if ok s ∧ compat s (dec t) then 512 ^ clsN t else 0) =
      ∑ j ∈ Finset.range 56, MX (cls s) j * 512 ^ j := by
  have h := hashS (enc s) (enc_lt s)
  unfold HashP at h
  rw [dec_enc] at h
  exact h

theorem F_eq (n : ℕ) : ∀ s : R, F n s = V n (cls s) := by
  induction n with
  | zero =>
    intro s
    rw [F_zero]
    have h := base_ok (enc s) (enc_lt s)
    rw [dec_enc] at h
    exact h
  | succ n ih =>
    intro s
    rw [F_succ, V_succ]
    simp only [ih]
    rw [sum_cls (fun t => ok s ∧ compat s t) (V n)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [counts_of_hash (fun t => ok s ∧ compat s t) (cls s) (hashS' s) (MX_lt _ (cls_lt s)) j
      (Finset.mem_range.mp hj)]

theorem count_walks (n : ℕ) :
    Nat.card {y : Fin (n + 1) → R // Walk y ∧ Init (y 0)} = V (n + 1) 55 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  have h1 : (∑ x : Fin (n + 1) → R, if Walk x ∧ Init (x 0) then 1 else 0) =
      ∑ s : R, if Init s then F n s else 0 := by
    unfold F
    have h2 : ∀ s : R, (if Init s then
        (∑ y : Fin (n + 1) → R, if Walk y ∧ y 0 = s then 1 else 0) else 0) =
        ∑ y : Fin (n + 1) → R, if y 0 = s then (if Walk y ∧ Init (y 0) then 1 else 0) else 0 := by
      intro s
      by_cases hs : Init s
      · rw [if_pos hs]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : y 0 = s
        · subst hy
          rw [if_pos rfl]
          exact if_congr ⟨fun h => ⟨h.1, hs⟩, fun h => ⟨h.1, rfl⟩⟩ rfl rfl
        · rw [if_neg hy, if_neg (show ¬(Walk y ∧ y 0 = s) from fun h => hy h.2)]
      · rw [if_neg hs]
        symm
        apply Finset.sum_eq_zero
        intro y _
        by_cases hy : y 0 = s
        · subst hy
          rw [if_pos rfl, if_neg (fun h => hs h.2)]
        · rw [if_neg hy]
    rw [Finset.sum_congr rfl (fun s _ => h2 s), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  rw [h1]
  simp only [F_eq]
  rw [sum_cls Init (V n), V_succ]
  apply Finset.sum_congr rfl
  intro j hj
  rw [counts_of_hash Init 55 hashI (MX_lt _ (by norm_num)) j (Finset.mem_range.mp hj)]

theorem V_step (n : ℕ) (L L' : List ℕ) (h : ∀ j < 56, V n j = L.getD j 0)
    (h' : ∀ i < 56, ∑ j ∈ Finset.range 56, MX i j * L.getD j 0 = L'.getD i 0) :
    ∀ i < 56, V (n + 1) i = L'.getD i 0 := by
  intro i hi
  rw [V_succ, ← h' i hi]
  exact Finset.sum_congr rfl (fun j hj => by rw [h j (Finset.mem_range.mp hj)])

theorem lit0 : ∀ j < 56, V 0 j = L0.getD j 0 := fun _ _ => rfl

def L1 : List ℕ := [35, 54, 70, 80, 31, 47, 57, 22, 32, 10, 25, 41, 55, 64, 39, 48, 19, 28, 9, 13, 23, 33, 40, 30, 20, 7, 4, 8, 12, 16, 15, 34, 40, 24, 30, 12, 18, 6, 9, 16, 28, 21, 14, 5, 3, 6, 9, 5, 16, 12, 8, 3, 2, 4, 1, 256]
theorem lit1 : ∀ i < 56, V 1 i = L1.getD i 0 := V_step 0 L0 L1 lit0 (by decide +kernel)
def L2 : List ℕ := [165, 364, 616, 840, 145, 315, 480, 95, 195, 35, 109, 258, 456, 640, 246, 384, 79, 165, 31, 46, 120, 228, 340, 204, 102, 22, 10, 30, 60, 100, 45, 196, 280, 105, 168, 35, 75, 15, 24, 63, 180, 108, 54, 12, 6, 18, 36, 9, 70, 42, 21, 5, 3, 9, 1, 2670]
theorem lit2 : ∀ i < 56, V 2 i = L2.getD i 0 := V_step 1 L1 L2 lit1 (by decide +kernel)
def L3 : List ℕ := [455, 1310, 2750, 4400, 399, 1134, 2100, 252, 672, 84, 290, 900, 1980, 3280, 860, 1640, 206, 560, 74, 110, 380, 900, 1600, 800, 320, 50, 20, 80, 200, 400, 91, 650, 1100, 280, 550, 70, 196, 28, 46, 160, 680, 340, 136, 22, 10, 40, 100, 13, 200, 100, 40, 7, 4, 16, 1, 13097]
theorem lit3 : ∀ i < 56, V 3 i = L3.getD i 0 := V_step 2 L2 L3 lit2 (by decide +kernel)
def L4 : List ℕ := [969, 3445, 8645, 15925, 849, 2985, 6525, 525, 1725, 165, 605, 2325, 6125, 11725, 2225, 5025, 425, 1425, 145, 215, 925, 2625, 5425, 2325, 775, 95, 35, 175, 525, 1225, 153, 1625, 3185, 585, 1365, 117, 405, 45, 75, 325, 1925, 825, 275, 35, 15, 75, 225, 17, 455, 195, 65, 9, 5, 25, 1, 44797]
theorem lit4 : ∀ i < 56, V 4 i = L4.getD i 0 := V_step 3 L3 L4 lit3 (by decide +kernel)
def L5 : List ℕ := [1771, 7496, 21896, 45696, 1551, 6501, 16401, 946, 3696, 286, 1091, 5001, 15351, 33376, 4791, 12516, 761, 3036, 251, 371, 1911, 6321, 14896, 5586, 1596, 161, 56, 336, 1176, 3136, 231, 3416, 7616, 1056, 2856, 176, 726, 66, 111, 576, 4536, 1701, 486, 51, 21, 126, 441, 21, 896, 336, 96, 11, 6, 36, 1, 123016]
theorem lit5 : ∀ i < 56, V 5 i = L5.getD i 0 := V_step 4 L4 L5 lit4 (by decide +kernel)
def L6 : List ℕ := [2925, 14364, 47880, 111720, 2561, 12467, 35672, 1547, 7007, 455, 1785, 9506, 33320, 81144, 9114, 27048, 1239, 5733, 399, 588, 3528, 13328, 35280, 11760, 2940, 252, 84, 588, 2352, 7056, 325, 6384, 15960, 1729, 5320, 247, 1183, 91, 154, 931, 9408, 3136, 784, 70, 28, 196, 784, 25, 1596, 532, 133, 13, 7, 49, 1, 290646]
theorem lit6 : ∀ i < 56, V 6 i = L6.getD i 0 := V_step 5 L5 L6 lit5 (by decide +kernel)
def L7 : List ℕ := [4495, 25124, 94116, 242880, 3935, 21820, 69840, 2360, 12160, 680, 2724, 16528, 65136, 175680, 15856, 52704, 1884, 9920, 596, 876, 6000, 25488, 74880, 22464, 4992, 372, 120, 960, 4320, 14400, 435, 10956, 30360, 2640, 9108, 330, 1800, 120, 204, 1408, 17760, 5328, 1184, 92, 36, 288, 1296, 29, 2640, 792, 176, 15, 8, 64, 1, 614965]
theorem lit7 : ∀ i < 56, V 7 i = L7.getD i 0 := V_step 6 L6 L7 lit6 (by decide +kernel)
def L8 : List ℕ := [6545, 41025, 170625, 482625, 5729, 35649, 126225, 3417, 19737, 969, 3945, 26865, 117585, 347985, 25785, 94905, 2721, 16065, 849, 1245, 9585, 45225, 146025, 39825, 7965, 525, 165, 1485, 7425, 27225, 561, 17625, 53625, 3825, 14625, 425, 2601, 153, 261, 2025, 31185, 8505, 1701, 117, 45, 405, 2025, 33, 4125, 1125, 225, 17, 9, 81, 1, 1195457]
theorem lit8 : ∀ i < 56, V 8 i = L8.getD i 0 := V_step 7 L7 L8 lit7 (by decide +kernel)
def L9 : List ℕ := [9139, 63490, 290290, 893200, 7999, 55195, 214225, 4750, 30400, 1330, 5485, 41425, 199375, 642400, 39775, 160600, 3775, 24700, 1165, 1705, 14575, 75625, 266200, 66550, 12100, 715, 220, 2200, 12100, 48400, 703, 26950, 89320, 5320, 22330, 532, 3610, 190, 325, 2800, 51700, 12925, 2350, 145, 55, 550, 3025, 37, 6160, 1540, 280, 19, 10, 100, 1, 2172712]
theorem lit9 : ∀ i < 56, V 9 i = L9.getD i 0 := V_step 8 L8 L9 lit8 (by decide +kernel)
def L10 : List ℕ := [12341, 94116, 469216, 1560416, 10801, 81851, 345576, 6391, 44891, 1771, 7381, 61226, 321376, 1119976, 58806, 258456, 5071, 36421, 1551, 2266, 21296, 120516, 459316, 105996, 17666, 946, 286, 3146, 18876, 81796, 861, 39556, 141856, 7161, 32736, 651, 4851, 231, 396, 3751, 81796, 18876, 3146, 176, 66, 726, 4356, 41, 8866, 2046, 341, 21, 11, 121, 1, 3738406]
theorem lit10 : ∀ i < 56, V 10 i = L10.getD i 0 := V_step 9 L9 L10 lit9 (by decide +kernel)

theorem vbase : ∀ i < 56, ((L8.getD i 0 : ℕ) : ℤ) = (1 : ℤ) * ((L1.getD i 0 : ℕ) : ℤ) + (-7 : ℤ) * ((L2.getD i 0 : ℕ) : ℤ) + (21 : ℤ) * ((L3.getD i 0 : ℕ) : ℤ) + (-35 : ℤ) * ((L4.getD i 0 : ℕ) : ℤ) + (35 : ℤ) * ((L5.getD i 0 : ℕ) : ℤ) + (-21 : ℤ) * ((L6.getD i 0 : ℕ) : ℤ) + (7 : ℤ) * ((L7.getD i 0 : ℕ) : ℤ) := by decide +kernel

/-- A linear recurrence for the whole class vector (by linearity of the transfer step). -/
theorem vrec : ∀ n : ℕ, ∀ i < 56, (V (n + 8) i : ℤ) = (1 : ℤ) * (V (n + 1) i : ℤ) + (-7 : ℤ) * (V (n + 2) i : ℤ) + (21 : ℤ) * (V (n + 3) i : ℤ) + (-35 : ℤ) * (V (n + 4) i : ℤ) + (35 : ℤ) * (V (n + 5) i : ℤ) + (-21 : ℤ) * (V (n + 6) i : ℤ) + (7 : ℤ) * (V (n + 7) i : ℤ) := by
  intro n
  induction n with
  | zero =>
    intro i hi
    simp only [Nat.zero_add]
    rw [lit8 i hi, lit1 i hi, lit2 i hi, lit3 i hi, lit4 i hi, lit5 i hi, lit6 i hi, lit7 i hi]
    exact vbase i hi
  | succ n ih =>
    intro i hi
    have e : ∀ m, (V (n + 1 + m) i : ℤ) = ∑ j ∈ Finset.range 56, (MX i j : ℤ) * (V (n + m) j : ℤ) := by
      intro m
      rw [show n + 1 + m = (n + m) + 1 by omega, V_succ]
      push_cast
      rfl
    simp only [e, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [ih j (Finset.mem_range.mp hj)]
    ring

theorem a_eq (n : ℕ) : a n = V (n + 1) 55 := by
  unfold a
  rw [← count_walks]
  exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.piComm (fun _ _ => Fin 4))
    (fun x => ⟨fun h => ⟨⟨fun _ => trivial, fun j i => h i j⟩, trivial⟩, fun h i j => h.1.2 j i⟩))

theorem a_0 : a 0 = 256 := (a_eq 0).trans ((lit1 55 (by norm_num)).trans (by decide))
theorem a_1 : a 1 = 2670 := (a_eq 1).trans ((lit2 55 (by norm_num)).trans (by decide))
theorem a_2 : a 2 = 13097 := (a_eq 2).trans ((lit3 55 (by norm_num)).trans (by decide))
theorem a_3 : a 3 = 44797 := (a_eq 3).trans ((lit4 55 (by norm_num)).trans (by decide))
theorem a_4 : a 4 = 123016 := (a_eq 4).trans ((lit5 55 (by norm_num)).trans (by decide))
theorem a_5 : a 5 = 290646 := (a_eq 5).trans ((lit6 55 (by norm_num)).trans (by decide))
theorem a_6 : a 6 = 614965 := (a_eq 6).trans ((lit7 55 (by norm_num)).trans (by decide))
theorem a_7 : a 7 = 1195457 := (a_eq 7).trans ((lit8 55 (by norm_num)).trans (by decide))
theorem a_8 : a 8 = 2172712 := (a_eq 8).trans ((lit9 55 (by norm_num)).trans (by decide))

theorem a_rec (m : ℕ) : (a (m + 7) : ℤ) = (7 : ℤ) * (a (m + 6) : ℤ) + (-21 : ℤ) * (a (m + 5) : ℤ) + (35 : ℤ) * (a (m + 4) : ℤ) + (-35 : ℤ) * (a (m + 3) : ℤ) + (21 : ℤ) * (a (m + 2) : ℤ) + (-7 : ℤ) * (a (m + 1) : ℤ) + (1 : ℤ) * (a (m) : ℤ) := by
  have h := vrec m 55 (by norm_num)
  rw [show V (m + 8) 55 = a (m + 7) from (a_eq (m + 7)).symm, show V (m + 7) 55 = a (m + 6) from (a_eq (m + 6)).symm, show V (m + 6) 55 = a (m + 5) from (a_eq (m + 5)).symm, show V (m + 5) 55 = a (m + 4) from (a_eq (m + 4)).symm, show V (m + 4) 55 = a (m + 3) from (a_eq (m + 3)).symm, show V (m + 3) 55 = a (m + 2) from (a_eq (m + 2)).symm, show V (m + 2) 55 = a (m + 1) from (a_eq (m + 1)).symm, show V (m + 1) 55 = a (m) from (a_eq (m)).symm] at h
  linear_combination h

end OMAA250855Helpers

open OMA.S_oeis_a250855 OMAA250855Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a250855.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    rw [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega, show m + 8 - 3 = m + 5 by omega, show m + 8 - 4 = m + 4 by omega, show m + 8 - 5 = m + 3 by omega, show m + 8 - 6 = m + 2 by omega, show m + 8 - 7 = m + 1 by omega]
    have h := a_rec (m + 1)
    rw [show m + 1 + 1 = m + 2 by omega, show m + 1 + 2 = m + 3 by omega, show m + 1 + 3 = m + 4 by omega, show m + 1 + 4 = m + 5 by omega, show m + 1 + 5 = m + 6 by omega, show m + 1 + 6 = m + 7 by omega, show m + 1 + 7 = m + 8 by omega] at h
    linear_combination h
  · rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    set F' := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
    have e1 : F' * ((1 - PowerSeries.X) ^ 7) = F' - PowerSeries.C (7 : ℚ) * (PowerSeries.X ^ 1 * F') + PowerSeries.C (21 : ℚ) * (PowerSeries.X ^ 2 * F') - PowerSeries.C (35 : ℚ) * (PowerSeries.X ^ 3 * F') + PowerSeries.C (35 : ℚ) * (PowerSeries.X ^ 4 * F') - PowerSeries.C (21 : ℚ) * (PowerSeries.X ^ 5 * F') + PowerSeries.C (7 : ℚ) * (PowerSeries.X ^ 6 * F') - PowerSeries.X ^ 7 * F' := by
      simp only [map_ofNat]
      ring
    have e2 : (PowerSeries.X * (2670 - 5593 * PowerSeries.X + 9188 * PowerSeries.X ^ 2 - 8976 * PowerSeries.X ^ 3 + 5326 * PowerSeries.X ^ 4 - 1791 * PowerSeries.X ^ 5 + 256 * PowerSeries.X ^ 6) : PowerSeries ℚ) = PowerSeries.C (2670 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.C (5593 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (9188 : ℚ) * PowerSeries.X ^ 3 - PowerSeries.C (8976 : ℚ) * PowerSeries.X ^ 4 + PowerSeries.C (5326 : ℚ) * PowerSeries.X ^ 5 - PowerSeries.C (1791 : ℚ) * PowerSeries.X ^ 6 + PowerSeries.C (256 : ℚ) * PowerSeries.X ^ 7 := by
      simp only [map_ofNat]
      ring
    rw [e1, e2]
    ext n
    simp only [F', map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
    by_cases hn : n ≤ 7
    · interval_cases n <;> norm_num [a_1, a_2, a_3, a_4, a_5, a_6, a_7]
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + 8 := ⟨n - 8, by omega⟩
      have h := a_rec (j + 1)
      rw [show j + 1 + 1 = j + 2 by omega, show j + 1 + 2 = j + 3 by omega, show j + 1 + 3 = j + 4 by omega, show j + 1 + 4 = j + 5 by omega, show j + 1 + 5 = j + 6 by omega, show j + 1 + 6 = j + 7 by omega, show j + 1 + 7 = j + 8 by omega] at h
      have q := congrArg (Int.cast : ℤ → ℚ) h
      push_cast at q
      simp
      linear_combination q
  · intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro hn
    by_cases hb : n ≤ 7
    · interval_cases n <;> norm_num [a_1, a_2, a_3, a_4, a_5, a_6, a_7]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
      have h := a_rec (m + 1)
      rw [show m + 1 + 1 = m + 2 by omega, show m + 1 + 2 = m + 3 by omega, show m + 1 + 3 = m + 4 by omega, show m + 1 + 4 = m + 5 by omega, show m + 1 + 5 = m + 6 by omega, show m + 1 + 6 = m + 7 by omega, show m + 1 + 7 = m + 8 by omega] at h
      have q := congrArg (Int.cast : ℤ → ℚ) h
      push_cast at q
      have i1 := ih (m + 7) (by omega) (by omega)
      have i2 := ih (m + 6) (by omega) (by omega)
      have i3 := ih (m + 5) (by omega) (by omega)
      have i4 := ih (m + 4) (by omega) (by omega)
      have i5 := ih (m + 3) (by omega) (by omega)
      have i6 := ih (m + 2) (by omega) (by omega)
      have i7 := ih (m + 1) (by omega) (by omega)
      rw [q, i1, i2, i3, i4, i5, i6, i7]
      push_cast
      ring

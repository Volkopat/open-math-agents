import OMAStatements.S_oeis_a188821
import Mathlib

-- Proof of the formulas of OEIS A188821 (statement by @ivillar).
-- Idea: the conditions only involve consecutive lines, so the count is a walk count on lines (transfer matrix).
-- The lines are grouped into 15 classes such that the number of successors in each class depends only on the class
-- (checked by decide); the class counts V n c then satisfy an explicit linear system, from which the recurrence
-- follows by linear algebra, and the g.f. and the closed form follow from the recurrence and initial values.

namespace OMAA188821Helpers

open OMA.S_oeis_a188821

/-- The lines of the array (the states of the transfer matrix). -/
abbrev R := Fin 6 → Fin 2

instance (u v : R) : Decidable (BlockOK u v) := by unfold BlockOK; infer_instance

abbrev ok (_r : R) : Prop := True

abbrev ini (_r : R) : Prop := True

abbrev compat (r s : R) : Prop := BlockOK r s

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

theorem good_iff (n : ℕ) (x : Fin (n + 1) → R) : Good x ↔ Walk x ∧ ini (x 0) := by
  unfold Good
  constructor
  · intro h2
    exact ⟨⟨fun _ => trivial, fun i => h2 i.castSucc i.succ (by simp)⟩, trivial⟩
  · rintro ⟨⟨-, h2⟩, -⟩
    intro i j hij
    have hi : (i : ℕ) < n := by have := j.isLt; omega
    have e1 : (⟨i, hi⟩ : Fin n).castSucc = i := Fin.ext rfl
    have e2 : (⟨i, hi⟩ : Fin n).succ = j := Fin.ext (by simp [hij])
    have := h2 ⟨i, hi⟩
    rw [e1, e2] at this
    exact this

/-- Index of a line in the class table. -/
def code (r : R) : ℕ := (r 0 : ℕ) + 2 * ((r 1 : ℕ) + 2 * ((r 2 : ℕ) + 2 * ((r 3 : ℕ) + 2 * ((r 4 : ℕ) + 2 * ((r 5 : ℕ))))))

/-- The class of a line: lines of the same class have the same number of successors in each class. -/
def cls (r : R) : ℕ := ([0, 0, 1, 1, 0, 2, 1, 3, 0, 0, 4, 4, 0, 2, 4, 5, 1, 1, 6, 6, 4, 7, 8, 9, 1, 1, 8, 8, 4, 7, 10, 11, 0, 0, 1, 1, 0, 2, 1, 3, 2, 2, 7, 7, 2, 12, 7, 13, 1, 1, 6, 6, 4, 7, 8, 9, 3, 3, 9, 9, 5, 13, 11, 14] : List ℕ).getD (code r) 0

/-- Mt i j: the number of successors in class j of a line of class i. -/
def Mt (i j : ℕ) : ℕ :=
  (([[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [3, 3, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [3, 2, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    [6, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [6, 4, 2, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0],
    [9, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    [9, 6, 6, 2, 3, 1, 0, 3, 0, 0, 0, 0, 1, 1, 0],
    [1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [3, 5, 1, 1, 1, 0, 2, 1, 1, 1, 0, 0, 0, 0, 0],
    [9, 12, 6, 4, 6, 2, 4, 6, 4, 4, 1, 2, 1, 2, 1]] : List (List ℕ)).getD i []).getD j 0

/-- V n c: the number of walks of n + 1 lines starting at a given line of class c. -/
def V : ℕ → ℕ → ℕ
  | 0, c => ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℕ).getD c 0
  | n + 1, 0 => V n 0
  | n + 1, 1 => 2 * V n 0
  | n + 1, 2 => V n 0 + V n 1
  | n + 1, 3 => 2 * V n 0 + 2 * V n 1
  | n + 1, 4 => 3 * V n 0 + V n 2
  | n + 1, 5 => 3 * V n 0 + 3 * V n 1 + V n 2 + V n 3
  | n + 1, 6 => 4 * V n 0
  | n + 1, 7 => 3 * V n 0 + 2 * V n 1 + V n 2 + V n 4 + V n 7
  | n + 1, 8 => 6 * V n 0 + 2 * V n 2
  | n + 1, 9 => 6 * V n 0 + 4 * V n 1 + 2 * V n 2 + 2 * V n 4 + 2 * V n 7
  | n + 1, 10 => 9 * V n 0 + 6 * V n 2 + V n 12
  | n + 1, 11 => 9 * V n 0 + 6 * V n 1 + 6 * V n 2 + 2 * V n 3 + 3 * V n 4 + V n 5 + 3 * V n 7 + V n 12 + V n 13
  | n + 1, 12 => V n 0 + 2 * V n 1 + V n 6
  | n + 1, 13 => 3 * V n 0 + 5 * V n 1 + V n 2 + V n 3 + V n 4 + 2 * V n 6 + V n 7 + V n 8 + V n 9
  | n + 1, 14 => 9 * V n 0 + 12 * V n 1 + 6 * V n 2 + 4 * V n 3 + 6 * V n 4 + 2 * V n 5 + 4 * V n 6 + 6 * V n 7 + 4 * V n 8 + 4 * V n 9 + V n 10 + 2 * V n 11 + V n 12 + 2 * V n 13 + V n 14
  | _ + 1, _ => 0

theorem cls_lt : ∀ t : R, cls t < 15 := by decide +kernel

theorem sum_cls (g : ℕ → ℕ) (P : R → Prop) [DecidablePred P] :
    (∑ t : R, if P t then g (cls t) else 0) =
      ∑ c ∈ Finset.range 15, (Finset.univ.filter (fun t : R => cls t = c ∧ P t)).card * g c := by
  have h1 : ∀ t : R, (if P t then g (cls t) else 0) =
      ∑ c ∈ Finset.range 15, if cls t = c ∧ P t then g c else 0 := by
    intro t
    rw [Finset.sum_eq_single (cls t)]
    · by_cases hp : P t <;> simp [hp]
    · intro c _ hc
      rw [if_neg]
      exact fun h => hc h.1.symm
    · intro h
      exact absurd (Finset.mem_range.mpr (cls_lt t)) h
  rw [Finset.sum_congr rfl (fun t _ => h1 t), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]

theorem cnt : ∀ s : R, ∀ c < 15,
    (Finset.univ.filter (fun t : R => cls t = c ∧ (ok s ∧ compat s t))).card = Mt (cls s) c := by
  decide +kernel

theorem cnt0 : ∀ s : R, (if ok s then 1 else 0) = V 0 (cls s) := by decide +kernel

theorem tcnt : ∀ c < 15, (Finset.univ.filter (fun t : R => cls t = c ∧ ini t)).card =
    ([9, 12, 6, 4, 6, 2, 4, 6, 4, 4, 1, 2, 1, 2, 1] : List ℕ).getD c 0 := by decide +kernel

theorem step (n : ℕ) : ∀ i < 15, (∑ c ∈ Finset.range 15, Mt i c * V n c) = V (n + 1) i := by
  intro i hi
  interval_cases i <;> simp [Finset.sum_range_succ, Mt, V]

theorem F_eq (n : ℕ) : ∀ s : R, F n s = V n (cls s) := by
  induction n with
  | zero => intro s; rw [F_zero]; exact cnt0 s
  | succ n ih =>
    intro s
    rw [F_succ]
    simp only [ih]
    rw [sum_cls (V n) (fun t => ok s ∧ compat s t), ← step n (cls s) (cls_lt s)]
    apply Finset.sum_congr rfl
    intro c hc
    rw [cnt s c (Finset.mem_range.mp hc)]

/-- U n: the number of arrays with n + 1 lines. -/
def U (n : ℕ) : ℕ := 9 * V n 0 + 12 * V n 1 + 6 * V n 2 + 4 * V n 3 + 6 * V n 4 + 2 * V n 5 + 4 * V n 6 + 6 * V n 7 + 4 * V n 8 + 4 * V n 9 + V n 10 + 2 * V n 11 + V n 12 + 2 * V n 13 + V n 14

theorem usum (n : ℕ) : (∑ c ∈ Finset.range 15, ([9, 12, 6, 4, 6, 2, 4, 6, 4, 4, 1, 2, 1, 2, 1] : List ℕ).getD c 0 * V n c) = U n := by
  simp [Finset.sum_range_succ, U]

theorem a_eq (n : ℕ) : a (n + 1) = U n := by
  unfold a
  rw [Nat.card_congr (Equiv.subtypeEquivRight (good_iff n)), Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.card_filter]
  have h1 : (∑ x : Fin (n + 1) → R, if Walk x ∧ ini (x 0) then 1 else 0) =
      ∑ s : R, if ini s then F n s else 0 := by
    unfold F
    have h2 : ∀ s : R, (if ini s then ∑ y : Fin (n + 1) → R, (if Walk y ∧ y 0 = s then 1 else 0)
        else 0) = ∑ y : Fin (n + 1) → R, if y 0 = s then (if Walk y ∧ ini (y 0) then 1 else 0)
          else 0 := by
      intro s
      split_ifs with hs
      · apply Finset.sum_congr rfl
        intro y _
        by_cases hy : y 0 = s
        · subst hy; simp [hs]
        · simp [hy]
      · symm
        apply Finset.sum_eq_zero
        intro y _
        by_cases hy : y 0 = s
        · subst hy; rw [if_pos rfl, if_neg (fun h => hs h.2)]
        · rw [if_neg hy]
    rw [Finset.sum_congr rfl (fun s _ => h2 s), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_ite_eq]
    simp
  rw [h1]
  simp only [F_eq]
  rw [sum_cls (V n) (fun t => ini t), ← usum n]
  apply Finset.sum_congr rfl
  intro c hc
  rw [tcnt c (Finset.mem_range.mp hc)]

theorem up0 (n : ℕ) : U n = 9 * V n 0 + 12 * V n 1 + 6 * V n 2 + 4 * V n 3 + 6 * V n 4 + 2 * V n 5 + 4 * V n 6 + 6 * V n 7 + 4 * V n 8 + 4 * V n 9 + V n 10 + 2 * V n 11 + V n 12 + 2 * V n 13 + V n 14 := rfl

theorem up1 (n : ℕ) : U (n + 1) = 196 * V n 0 + 84 * V n 1 + 56 * V n 2 + 12 * V n 3 + 28 * V n 4 + 4 * V n 5 + 9 * V n 6 + 28 * V n 7 + 6 * V n 8 + 6 * V n 9 + V n 10 + 2 * V n 11 + 4 * V n 12 + 4 * V n 13 + V n 14 := by
  rw [up0 (n + 1)]
  simp only [V]
  ring

theorem up2 (n : ℕ) : U (n + 2) = 784 * V n 0 + 224 * V n 1 + 112 * V n 2 + 16 * V n 3 + 56 * V n 4 + 4 * V n 5 + 16 * V n 6 + 56 * V n 7 + 8 * V n 8 + 8 * V n 9 + V n 10 + 2 * V n 11 + 4 * V n 12 + 4 * V n 13 + V n 14 := by
  rw [show n + 2 = (n + 1) + 1 from rfl, up1 (n + 1)]
  simp only [V]
  ring

theorem up3 (n : ℕ) : U (n + 3) = 1936 * V n 0 + 352 * V n 1 + 176 * V n 2 + 16 * V n 3 + 88 * V n 4 + 4 * V n 5 + 16 * V n 6 + 88 * V n 7 + 8 * V n 8 + 8 * V n 9 + V n 10 + 2 * V n 11 + 4 * V n 12 + 4 * V n 13 + V n 14 := by
  rw [show n + 3 = (n + 1) + 2 from rfl, up2 (n + 1)]
  simp only [V]
  ring

theorem up4 (n : ℕ) : U (n + 4) = 3600 * V n 0 + 480 * V n 1 + 240 * V n 2 + 16 * V n 3 + 120 * V n 4 + 4 * V n 5 + 16 * V n 6 + 120 * V n 7 + 8 * V n 8 + 8 * V n 9 + V n 10 + 2 * V n 11 + 4 * V n 12 + 4 * V n 13 + V n 14 := by
  rw [show n + 4 = (n + 1) + 3 from rfl, up3 (n + 1)]
  simp only [V]
  ring

theorem up5 (n : ℕ) : U (n + 5) = 5776 * V n 0 + 608 * V n 1 + 304 * V n 2 + 16 * V n 3 + 152 * V n 4 + 4 * V n 5 + 16 * V n 6 + 152 * V n 7 + 8 * V n 8 + 8 * V n 9 + V n 10 + 2 * V n 11 + 4 * V n 12 + 4 * V n 13 + V n 14 := by
  rw [show n + 5 = (n + 1) + 4 from rfl, up4 (n + 1)]
  simp only [V]
  ring

theorem a_rec : ∀ m : ℕ, 6 ≤ m → (a m : ℤ) = 3 * (a (m - 1) : ℤ) - 3 * (a (m - 2) : ℤ) + (a (m - 3) : ℤ) := by
  intro m hm
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 6 := ⟨m - 6, by omega⟩
  rw [show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega, show k + 6 - 3 = k + 3 by omega]
  rw [show a (k + 6) = U (k + 5) from a_eq _, show a (k + 5) = U (k + 4) from a_eq _, show a (k + 4) = U (k + 3) from a_eq _, show a (k + 3) = U (k + 2) from a_eq _]
  rw [up5 k, up4 k, up3 k, up2 k]
  push_cast
  ring

theorem a_v1 : a 1 = 64 := by
  rw [show a 1 = U 0 from a_eq _]; decide +kernel

theorem a_v2 : a 2 = 441 := by
  rw [show a 2 = U 1 from a_eq _]; decide +kernel

theorem a_v3 : a 3 = 1296 := by
  rw [show a 3 = U 2 from a_eq _]; decide +kernel

theorem a_v4 : a 4 = 2704 := by
  rw [show a 4 = U 3 from a_eq _]; decide +kernel

theorem a_v5 : a 5 = 4624 := by
  rw [show a 5 = U 4 from a_eq _]; decide +kernel

theorem gf_eq : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  set F' := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
  have e1 : F' * ((1 - PowerSeries.X) ^ 3) = F' - PowerSeries.C (3 : ℚ) * (PowerSeries.X ^ 1 * F') + PowerSeries.C (3 : ℚ) * (PowerSeries.X ^ 2 * F') - PowerSeries.X ^ 3 * F' := by
    simp only [map_ofNat]
    ring
  have e2 : (PowerSeries.X * (64 + 249 * PowerSeries.X + 165 * PowerSeries.X ^ 2 + 75 * PowerSeries.X ^ 3 - 41 * PowerSeries.X ^ 4) : PowerSeries ℚ) = PowerSeries.C (64 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (249 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (165 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.C (75 : ℚ) * PowerSeries.X ^ 4 - PowerSeries.C (41 : ℚ) * PowerSeries.X ^ 5 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  simp only [F', map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
  by_cases hn : n ≤ 5
  · interval_cases n <;> norm_num [a_v1, a_v2, a_v3, a_v4, a_v5]
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 6 := ⟨n - 6, by omega⟩
    have h := a_rec (j + 6) (by omega)
    rw [show j + 6 - 1 = j + 5 by omega, show j + 6 - 2 = j + 4 by omega, show j + 6 - 3 = j + 3 by omega] at h
    have q : (a (j + 6) : ℚ) = 3 * (a (j + 5) : ℚ) - 3 * (a (j + 4) : ℚ) + (a (j + 3) : ℚ) := by exact_mod_cast h
    simp
    linear_combination q

theorem closed0 : ∀ n : ℕ, 3 ≤ n → (a n : ℤ) = 256 * (n : ℤ) ^ 2 - 384 * (n : ℤ) + 144 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hlt : n < 6
    · interval_cases n <;> norm_num [a_v3, a_v4, a_v5]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
      have h1 := ih (k + 5) (by omega) (by omega)
      have h2 := ih (k + 4) (by omega) (by omega)
      have h3 := ih (k + 3) (by omega) (by omega)
      have hr := a_rec (k + 6) (by omega)
      rw [show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega, show k + 6 - 3 = k + 3 by omega] at hr
      have q : (a (k + 6) : ℤ) = 3 * (a (k + 5) : ℤ) - 3 * (a (k + 4) : ℤ) + (a (k + 3) : ℤ) := by exact_mod_cast hr
      rw [q, h1, h2, h3]
      push_cast
      ring

end OMAA188821Helpers

open OMA.S_oeis_a188821 OMAA188821Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a188821.main :=
  ⟨a_rec, gf_eq, closed0⟩

import OMAStatements.S_oeis_a222098
import Mathlib

-- Proof of the conjectures in OEIS A222098 (statement by @ivillar).
-- Idea: all conditions involve a single row or two consecutive rows, so the count is a walk count on
-- rows (transfer matrix). Walk counts from a row depend only on its in-row difference d mod 6: d in {0,3}
-- (α) or d in {1,2} (β); rows with d in {4,5} are excluded. Checking the 36 x 36 row pairs gives
-- α' = 6α + 5β and β' = 5α + 7β, with a(n+1) = 2α(n) + 2β(n). The characteristic polynomial
-- t^2 - 13t + 17 has roots (13 ± sqrt 101)/2, which gives the recurrence, the g.f. and the closed form.

namespace OMAA222098Helpers

open OMA.S_oeis_a222098

abbrev R := Fin 2 → Fin 6

/-- Within a row, the rightward step increases by 0..3 mod 6. -/
abbrev ok (r : R) : Prop := ((r 1 - r 0 : Fin 6) : ℕ) ≤ 3

/-- Two consecutive rows: downward steps increase by 0..3 mod 6. -/
abbrev compat (r s : R) : Prop := ∀ j : Fin 2, ((s j - r j : Fin 6) : ℕ) ≤ 3

/-- The array conditions, row by row. -/
abbrev Walk {n : ℕ} (x : Fin (n + 1) → R) : Prop :=
  (∀ i, ok (x i)) ∧ ∀ i : Fin n, compat (x i.castSucc) (x i.succ)

theorem good_iff (n : ℕ) (x : Fin (n + 1) → R) : Good x ↔ Walk x ∧ x 0 0 = 0 := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨fun i => h1 i 0 1 rfl, fun i j => ?_⟩, h3 (Nat.succ_pos n)⟩
    exact h2 i.castSucc i.succ j (by simp only [Fin.val_castSucc, Fin.val_succ])
  · rintro ⟨⟨hok, hc⟩, h0⟩
    refine ⟨fun i j j' hj => ?_, fun i i' j hi => ?_, fun h => ?_⟩
    · have hj1 := j'.isLt
      have e0 : j = 0 := Fin.ext (by omega)
      have e1 : j' = 1 := Fin.ext (by omega)
      rw [e0, e1]
      exact hok i
    · have hlt : (i : ℕ) < n := by have := i'.isLt; omega
      have e1 : (⟨i, hlt⟩ : Fin n).castSucc = i := Fin.ext rfl
      have e2 : (⟨i, hlt⟩ : Fin n).succ = i' := Fin.ext (by simp; omega)
      have := hc ⟨i, hlt⟩ j
      rw [e1, e2] at this
      exact this
    · have e : (⟨0, h⟩ : Fin (n + 1)) = 0 := Fin.ext rfl
      rw [e]
      exact h0

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

/-- F(n, s): the number of row sequences of length n+1 satisfying the conditions, starting at s. -/
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
      · subst hr; simp
      · simp [hr]
    rw [Finset.sum_congr rfl (fun r _ => h r), Finset.sum_ite_eq']
    simp
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
      · subst hy; simp [ht]
      · simp [hy]
    · symm
      apply Finset.sum_eq_zero
      intro y _
      by_cases hy : y 0 = t
      · subst hy; rw [if_pos rfl, if_neg (fun h => ht ⟨h.1, h.2.1⟩)]
      · rw [if_neg hy]
  rw [Finset.sum_congr rfl (fun t _ => h2 t), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_ite_eq]
  simp

def α : ℕ → ℕ
  | 0 => 1
  | n + 1 => 6 * α n + 5 * β n
where
  β : ℕ → ℕ
  | 0 => 1
  | n + 1 => 5 * α n + 7 * β n

/-- The class of a row: its in-row difference is 0 or 3. -/
abbrev X (s : R) : Prop := (s 1 - s 0 : Fin 6) = 0 ∨ (s 1 - s 0 : Fin 6) = 3

/-- The value of F by row type: difference 0 or 3 gives α, difference 1 or 2 gives β, bad rows 0. -/
def V (n : ℕ) (s : R) : ℕ := if ok s then (if X s then α n else α.β n) else 0

theorem cA : ∀ s : R, (Finset.univ.filter (fun t : R => ok s ∧ compat s t ∧ ok t ∧ X t)).card =
    if ok s then (if X s then 6 else 5) else 0 := by decide

theorem cB : ∀ s : R, (Finset.univ.filter (fun t : R => ok s ∧ compat s t ∧ ok t ∧ ¬ X t)).card =
    if ok s then (if X s then 5 else 7) else 0 := by decide

theorem c0A : (Finset.univ.filter (fun t : R => t 0 = 0 ∧ ok t ∧ X t)).card = 2 := by decide

theorem c0B : (Finset.univ.filter (fun t : R => t 0 = 0 ∧ ok t ∧ ¬ X t)).card = 2 := by decide

theorem split_V (n : ℕ) (P : Prop) [Decidable P] (t : R) :
    (if P then V n t else 0) = (if P ∧ ok t ∧ X t then α n else 0) +
      (if P ∧ ok t ∧ ¬ X t then α.β n else 0) := by
  unfold V
  by_cases h1 : P
  · rw [if_pos h1]
    by_cases h2 : ok t
    · rw [if_pos h2]
      by_cases h3 : X t
      · rw [if_pos h3, if_pos ⟨h1, h2, h3⟩, if_neg (fun h => h.2.2 h3)]; ring
      · rw [if_neg h3, if_neg (fun h => h3 h.2.2), if_pos ⟨h1, h2, h3⟩]; ring
    · rw [if_neg h2, if_neg (fun h => h2 h.2.1), if_neg (fun h => h2 h.2.1)]
  · rw [if_neg h1, if_neg (fun h => h1 h.1), if_neg (fun h => h1 h.1)]

theorem F_eq (n : ℕ) : ∀ s : R, F n s = V n s := by
  induction n with
  | zero =>
    intro s
    rw [F_zero]
    unfold V
    by_cases h : ok s
    · rw [if_pos h, if_pos h]; split_ifs <;> rfl
    · rw [if_neg h, if_neg h]
  | succ n ih =>
    intro s
    rw [F_succ]
    simp only [ih]
    rw [Finset.sum_congr rfl (fun t _ => split_V n (ok s ∧ compat s t) t), Finset.sum_add_distrib,
      Finset.sum_ite, Finset.sum_ite]
    simp only [Finset.sum_const, Finset.sum_const_zero, smul_eq_mul, add_zero]
    have hA := cA s
    have hB := cB s
    simp only [and_assoc] at hA hB ⊢
    rw [hA, hB]
    unfold V
    split_ifs <;> simp [α, α.β] <;> ring

theorem a_succ (n : ℕ) : a (n + 1) = 2 * α n + 2 * α.β n := by
  unfold a
  rw [Nat.card_congr (Equiv.subtypeEquivRight (good_iff n)), Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.card_filter]
  have h1 : (∑ x : Fin (n + 1) → R, if Walk x ∧ x 0 0 = 0 then 1 else 0) =
      ∑ s : R, if s 0 = 0 then F n s else 0 := by
    unfold F
    have h2 : ∀ s : R, (if s 0 = 0 then ∑ y : Fin (n + 1) → R, (if Walk y ∧ y 0 = s then 1 else 0)
        else 0) = ∑ y : Fin (n + 1) → R, if y 0 = s then (if Walk y ∧ y 0 0 = 0 then 1 else 0)
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
  rw [Finset.sum_congr rfl (fun t _ => split_V n (t 0 = 0) t), Finset.sum_add_distrib,
    Finset.sum_ite, Finset.sum_ite]
  simp only [Finset.sum_const, Finset.sum_const_zero, smul_eq_mul, add_zero]
  rw [c0A, c0B]
  ring

theorem α_rec (n : ℕ) : α (n + 2) + 17 * α n = 13 * α (n + 1) := by
  simp only [α, α.β]; ring

theorem β_rec (n : ℕ) : α.β (n + 2) + 17 * α.β n = 13 * α.β (n + 1) := by
  simp only [α, α.β]; ring

theorem a_rec (n : ℕ) : a (n + 3) + 17 * a (n + 1) = 13 * a (n + 2) := by
  rw [a_succ, a_succ, a_succ]
  have h1 := α_rec n
  have h2 := β_rec n
  omega

theorem a_one : a 1 = 4 := by rw [a_succ]; simp [α, α.β]

theorem a_two : a 2 = 46 := by rw [a_succ]; simp [α, α.β]

theorem closedT (k : ℕ) :
    17 * Real.sqrt 101 * 2 ^ (k + 1) * (a (k + 1) : ℝ) =
      (13 - Real.sqrt 101) ^ (k + 1) * (-29 + 3 * Real.sqrt 101) +
        (13 + Real.sqrt 101) ^ (k + 1) * (29 + 3 * Real.sqrt 101) ∧
    17 * Real.sqrt 101 * 2 ^ (k + 2) * (a (k + 2) : ℝ) =
      (13 - Real.sqrt 101) ^ (k + 2) * (-29 + 3 * Real.sqrt 101) +
        (13 + Real.sqrt 101) ^ (k + 2) * (29 + 3 * Real.sqrt 101) := by
  have hs : Real.sqrt 101 * Real.sqrt 101 = 101 := Real.mul_self_sqrt (by norm_num)
  have r1 : (13 + Real.sqrt 101) ^ 2 = 26 * (13 + Real.sqrt 101) - 68 := by linear_combination hs
  have r2 : (13 - Real.sqrt 101) ^ 2 = 26 * (13 - Real.sqrt 101) - 68 := by linear_combination hs
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [a_one]; push_cast; ring
    · rw [a_two]; push_cast; linear_combination (-6 * Real.sqrt 101) * hs
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have h : ((a (k + 3) : ℕ) : ℝ) + 17 * a (k + 1) = 13 * a (k + 2) := by exact_mod_cast a_rec k
    have e : (a (k + 1 + 2) : ℝ) = 13 * a (k + 2) - 17 * a (k + 1) := by
      show (a (k + 3) : ℝ) = _
      linarith
    rw [e]
    obtain ⟨h1, h2⟩ := ih
    linear_combination (26 : ℝ) * h2 - (68 : ℝ) * h1 -
      (13 - Real.sqrt 101) ^ (k + 1) * (-29 + 3 * Real.sqrt 101) * r2 -
      (13 + Real.sqrt 101) ^ (k + 1) * (29 + 3 * Real.sqrt 101) * r1

end OMAA222098Helpers

open OMA.S_oeis_a222098 OMAA222098Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a222098.main := by
  refine ⟨fun n hn => ?_, ?_, fun n hn => ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega]
    have h : ((a (k + 3) : ℕ) : ℤ) + 17 * a (k + 1) = 13 * a (k + 2) := by exact_mod_cast a_rec k
    linarith
  · rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    set F' := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
    have e1 : F' * (1 - 13 * PowerSeries.X + 17 * PowerSeries.X ^ 2) =
        F' - PowerSeries.C (13 : ℚ) * (PowerSeries.X ^ 1 * F') +
          PowerSeries.C (17 : ℚ) * (PowerSeries.X ^ 2 * F') := by
      simp only [map_ofNat]
      ring
    have e2 : (2 * PowerSeries.X * (2 - 3 * PowerSeries.X) : PowerSeries ℚ) =
        PowerSeries.C (4 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.C (6 : ℚ) * PowerSeries.X ^ 2 := by
      simp only [map_ofNat]
      ring
    rw [e1, e2]
    ext n
    simp only [F', map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
    by_cases hn : n ≤ 2
    · interval_cases n <;> norm_num [a_one, a_two]
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
      have q : ((a (j + 3) : ℕ) : ℚ) + 17 * a (j + 1) = 13 * a (j + 2) := by exact_mod_cast a_rec j
      simp
      linear_combination q
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hT := (closedT k).1
    have hs : (0 : ℝ) < Real.sqrt 101 := Real.sqrt_pos.mpr (by norm_num)
    have h2 : (2 : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) = ((2 : ℝ) ^ (k + 1))⁻¹ := by
      rw [zpow_neg, zpow_natCast]
    rw [h2, ← hT]
    field_simp

import OMAStatements.S_oeis_a223270
import Mathlib

-- Proof of the conjectures in OEIS A223270 (statement by @ivillar).
-- Idea: read the array column by column. All four cell pairs between consecutive columns are horizontal
-- or diagonal neighbours, and vertical pairs are unconstrained, so the count is a walk count on columns
-- (transfer matrix). Walk counts depend only on whether a column's two faces are equal or opposite (α),
-- or adjacent (β): α' = 8α + 8β, β' = 4α, and a(n+1) = 2α(n) + 4β(n). The characteristic polynomial
-- t^2 - 8t - 32 has roots 4 ± 4*sqrt 3, which gives the recurrence, the g.f. and the closed form.

namespace OMAA223270Helpers

open OMA.S_oeis_a223270

instance (u v : Fin 6) : Decidable (adjFace u v) := by unfold adjFace; infer_instance

theorem adjFace_symm : ∀ u v : Fin 6, adjFace u v → adjFace v u := by decide

abbrev R := Fin 2 → Fin 6

/-- Columns are unconstrained (vertical neighbours are not adjacent). -/
abbrev ok (_r : R) : Prop := True

/-- Two consecutive columns: no complementary pair between them (all such cells are adjacent). -/
abbrev compat (r s : R) : Prop := ∀ j j' : Fin 2, adjFace (r j) (s j')

/-- The array conditions, row by row. -/
abbrev Walk {n : ℕ} (x : Fin (n + 1) → R) : Prop :=
  (∀ i, ok (x i)) ∧ ∀ i : Fin n, compat (x i.castSucc) (x i.succ)

theorem good_iff (n : ℕ) (x : Fin 2 → Fin (n + 1) → Fin 6) :
    Good x ↔ Walk (fun j i => x i j : Fin (n + 1) → R) ∧ x 0 0 = 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun i => trivial, fun i j j' => ?_⟩, ?_⟩
    · have hj := j.isLt
      have hj' := j'.isLt
      exact h1 (j, i.castSucc) (j', i.succ)
        ⟨by omega, by omega, Or.inr (by simp only [Fin.val_castSucc, Fin.val_succ])⟩
    · exact h2 (Nat.succ_pos n)
  · rintro ⟨⟨-, hc⟩, h0⟩
    refine ⟨fun p q hpq => ?_, fun h => ?_⟩
    · obtain ⟨-, -, h3⟩ := hpq
      rcases h3 with hg | hl
      · have hlt : (q.2 : ℕ) < n := by have := p.2.isLt; omega
        have e1 : (⟨q.2, hlt⟩ : Fin n).castSucc = q.2 := Fin.ext rfl
        have e2 : (⟨q.2, hlt⟩ : Fin n).succ = p.2 := Fin.ext (by simp; omega)
        have := hc ⟨q.2, hlt⟩ q.1 p.1
        simp only [e1, e2] at this
        exact adjFace_symm _ _ this
      · have hlt : (p.2 : ℕ) < n := by have := q.2.isLt; omega
        have e1 : (⟨p.2, hlt⟩ : Fin n).castSucc = p.2 := Fin.ext rfl
        have e2 : (⟨p.2, hlt⟩ : Fin n).succ = q.2 := Fin.ext (by simp; omega)
        have := hc ⟨p.2, hlt⟩ p.1 q.1
        simp only [e1, e2] at this
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
  | n + 1 => 8 * α n + 8 * β n
where
  β : ℕ → ℕ
  | 0 => 1
  | n + 1 => 4 * α n + 0 * β n

/-- The value of F by row type: constant rows give α, two-valued rows give β, bad rows 0. -/
def V (n : ℕ) (s : R) : ℕ := if ok s then (if ¬ adjFace (s 0) (s 1) then α n else α.β n) else 0

theorem cA : ∀ s : R, (Finset.univ.filter (fun t : R => ok s ∧ compat s t ∧ ok t ∧ ¬ adjFace (t 0) (t 1))).card =
    if ok s then (if ¬ adjFace (s 0) (s 1) then 8 else 4) else 0 := by decide

theorem cB : ∀ s : R, (Finset.univ.filter (fun t : R => ok s ∧ compat s t ∧ ok t ∧ ¬ ¬ adjFace (t 0) (t 1))).card =
    if ok s then (if ¬ adjFace (s 0) (s 1) then 8 else 0) else 0 := by decide

theorem c0A : (Finset.univ.filter (fun t : R => t 0 = 0 ∧ ok t ∧ ¬ adjFace (t 0) (t 1))).card = 2 := by decide

theorem c0B : (Finset.univ.filter (fun t : R => t 0 = 0 ∧ ok t ∧ ¬ ¬ adjFace (t 0) (t 1))).card = 4 := by decide

theorem split_V (n : ℕ) (P : Prop) [Decidable P] (t : R) :
    (if P then V n t else 0) = (if P ∧ ok t ∧ ¬ adjFace (t 0) (t 1) then α n else 0) +
      (if P ∧ ok t ∧ ¬ ¬ adjFace (t 0) (t 1) then α.β n else 0) := by
  unfold V
  by_cases h1 : P
  · rw [if_pos h1]
    by_cases h2 : ok t
    · rw [if_pos h2]
      by_cases h3 : ¬ adjFace (t 0) (t 1)
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

theorem a_succ (n : ℕ) : a (n + 1) = 2 * α n + 4 * α.β n := by
  unfold a
  rw [Nat.card_congr ((Equiv.piComm (fun (_ : Fin 2) (_ : Fin (n + 1)) => Fin 6)).subtypeEquiv
      (p := Good) (q := fun y : Fin (n + 1) → R => Walk y ∧ y 0 0 = 0)
      (fun x => good_iff n x)), Nat.card_eq_fintype_card,
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

theorem α_rec (n : ℕ) : α (n + 2) = 8 * α (n + 1) + 32 * α n := by
  simp only [α, α.β]; ring

theorem β_rec (n : ℕ) : α.β (n + 2) = 8 * α.β (n + 1) + 32 * α.β n := by
  simp only [α, α.β]; ring

theorem a_rec (n : ℕ) : a (n + 3) = 8 * a (n + 2) + 32 * a (n + 1) := by
  rw [a_succ, a_succ, a_succ, α_rec, β_rec]
  ring

theorem a_one : a 1 = 6 := by rw [a_succ]; simp [α, α.β]

theorem a_two : a 2 = 48 := by rw [a_succ]; simp [α, α.β]

theorem closedT (k : ℕ) :
    4 * (a (k + 1) : ℝ) = Real.sqrt 3 * ((4 * (1 + Real.sqrt 3)) ^ (k + 1) - (4 - 4 * Real.sqrt 3) ^ (k + 1)) ∧
    4 * (a (k + 2) : ℝ) = Real.sqrt 3 * ((4 * (1 + Real.sqrt 3)) ^ (k + 2) - (4 - 4 * Real.sqrt 3) ^ (k + 2)) := by
  have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have r1 : (4 * (1 + Real.sqrt 3)) ^ 2 = 8 * (4 * (1 + Real.sqrt 3)) + 32 := by linear_combination 16 * hs
  have r2 : (4 - 4 * Real.sqrt 3) ^ 2 = 8 * (4 - 4 * Real.sqrt 3) + 32 := by linear_combination 16 * hs
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [a_one]; push_cast; linear_combination (-8 : ℝ) * hs
    · rw [a_two]; push_cast; linear_combination (-64 : ℝ) * hs
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have h : ((a (k + 3) : ℕ) : ℝ) = ((8 * a (k + 2) + 32 * a (k + 1) : ℕ) : ℝ) := by rw [a_rec]
    push_cast at h
    rw [show k + 1 + 2 = k + 3 from rfl, h]
    obtain ⟨h1, h2⟩ := ih
    linear_combination (8 : ℝ) * h2 + (32 : ℝ) * h1 -
      Real.sqrt 3 * (4 * (1 + Real.sqrt 3)) ^ (k + 1) * r1 +
      Real.sqrt 3 * (4 - 4 * Real.sqrt 3) ^ (k + 1) * r2

end OMAA223270Helpers

open OMA.S_oeis_a223270 OMAA223270Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a223270.main := by
  refine ⟨fun n hn => ?_, ?_, fun n hn => ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega]
    exact a_rec k
  · rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    set F' := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
    have e1 : F' * (1 - 8 * PowerSeries.X - 32 * PowerSeries.X ^ 2) =
        F' - PowerSeries.C (8 : ℚ) * (PowerSeries.X ^ 1 * F') -
          PowerSeries.C (32 : ℚ) * (PowerSeries.X ^ 2 * F') := by
      simp only [map_ofNat]
      ring
    have e2 : (6 * PowerSeries.X : PowerSeries ℚ) = PowerSeries.C (6 : ℚ) * PowerSeries.X ^ 1 := by
      simp only [map_ofNat]
      ring
    rw [e1, e2]
    ext n
    simp only [F', map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
    by_cases hn : n ≤ 2
    · interval_cases n <;> norm_num [a_one, a_two]
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
      have h := a_rec j
      have q : ((a (j + 3) : ℕ) : ℚ) = ((8 * a (j + 2) + 32 * a (j + 1) : ℕ) : ℚ) := by rw [h]
      push_cast at q
      simp
      linear_combination q
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h := (closedT k).1
    linear_combination (1 / 4 : ℝ) * h

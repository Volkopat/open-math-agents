import OMAStatements.S_oeis_a183644
import Mathlib

-- Proof of the formulas in OEIS A183644 (statement by @ivillar). Status: known result (Jianing Song);
-- this is an independent proof.
-- Idea: the subblock condition involves only consecutive rows, so the count is a walk count on rows
-- (transfer matrix). A row of sum s is followed exactly by the rows of sum 8 - s, and these have the
-- same number c of successors (checked by decide). So walks from a row number c^n, and
-- a(n) = Sum over rows of c^n = 2 + 4*2^n + 6*3^n + 8*4^n + 5*5^n
-- = 2 + 2^(2+n) + 2^(3+2n) + 2*3^(1+n) + 5^(1+n); the recurrence and the g.f. follow.

namespace OMAA183644Helpers

open OMA.S_oeis_a183644

instance (u v : Fin 2 → Fin 5) : Decidable (BlockOK u v) := by
  unfold BlockOK; infer_instance

abbrev R := Fin 2 → Fin 5

/-- Rows are unconstrained. -/
abbrev ok (_r : R) : Prop := True

/-- Consecutive rows r, s: the subblock they form satisfies the stress condition. -/
abbrev compat (r s : R) : Prop := BlockOK r s

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

/-- The number of successors of a row. -/
def c (s : R) : ℕ := (Finset.univ.filter (fun t : R => compat s t)).card

/-- Successors have the same number of successors. -/
theorem closure : ∀ s t : R, compat s t → c t = c s := by decide

theorem F_eq (n : ℕ) : ∀ s : R, F n s = c s ^ n := by
  induction n with
  | zero => intro s; rw [F_zero]; simp
  | succ n ih =>
    intro s
    rw [F_succ]
    simp only [ih]
    have h : ∀ t : R, (if ok s ∧ compat s t then c t ^ n else 0) =
        if compat s t then c s ^ n else 0 := by
      intro t
      by_cases ht : compat s t
      · rw [if_pos ⟨trivial, ht⟩, if_pos ht, closure s t ht]
      · rw [if_neg (fun h => ht h.2), if_neg ht]
    rw [Finset.sum_congr rfl (fun t _ => h t), Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero,
      smul_eq_mul, add_zero, pow_succ]
    unfold c
    ring

theorem img : Finset.univ.image c = {1, 2, 3, 4, 5} := by decide
theorem k1 : (Finset.univ.filter (fun s : R => c s = 1)).card = 2 := by decide
theorem k2 : (Finset.univ.filter (fun s : R => c s = 2)).card = 4 := by decide
theorem k3 : (Finset.univ.filter (fun s : R => c s = 3)).card = 6 := by decide
theorem k4 : (Finset.univ.filter (fun s : R => c s = 4)).card = 8 := by decide
theorem k5 : (Finset.univ.filter (fun s : R => c s = 5)).card = 5 := by decide

theorem a_eq (n : ℕ) : a n = ∑ s : R, c s ^ n := by
  unfold a
  rw [Nat.card_congr (Equiv.subtypeEquivRight
      (p := fun x : Fin (n + 1) → R => ∀ i : Fin n, BlockOK (x i.castSucc) (x i.succ))
      (q := fun y : Fin (n + 1) → R => Walk y)
      (fun x => ⟨fun h => ⟨fun _ => trivial, h⟩, fun h => h.2⟩)), Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.card_filter]
  have h1 : (∑ x : Fin (n + 1) → R, if Walk x then 1 else 0) = ∑ s : R, if True then F n s else 0 := by
    unfold F
    simp only [if_true]
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
  simp only [F_eq, if_true]

theorem a_closed (n : ℕ) : a n = 2 + 4 * 2 ^ n + 6 * 3 ^ n + 8 * 4 ^ n + 5 * 5 ^ n := by
  rw [a_eq, Finset.sum_comp (fun k => k ^ n) c, img]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, k1, k2, k3, k4, k5]
  simp only [smul_eq_mul, one_pow]
  ring

end OMAA183644Helpers

open OMA.S_oeis_a183644 OMAA183644Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a183644.main := by
  refine ⟨fun n hn => ?_, ?_, fun n hn => ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
      show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega, show m + 6 - 5 = m + 1 by omega,
      a_closed, a_closed, a_closed, a_closed, a_closed, a_closed]
    push_cast
    ring
  · rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    set F' := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
    have e1 : F' * ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X) *
        (1 - 4 * PowerSeries.X) * (1 - 5 * PowerSeries.X)) =
        F' - PowerSeries.C (15 : ℚ) * (PowerSeries.X ^ 1 * F') +
          PowerSeries.C (85 : ℚ) * (PowerSeries.X ^ 2 * F') -
          PowerSeries.C (225 : ℚ) * (PowerSeries.X ^ 3 * F') +
          PowerSeries.C (274 : ℚ) * (PowerSeries.X ^ 4 * F') -
          PowerSeries.C (120 : ℚ) * (PowerSeries.X ^ 5 * F') := by
      simp only [map_ofNat]
      ring
    have e2 : (PowerSeries.X * (85 - 950 * PowerSeries.X + 3683 * PowerSeries.X ^ 2 -
        5770 * PowerSeries.X ^ 3 + 3000 * PowerSeries.X ^ 4) : PowerSeries ℚ) =
        PowerSeries.C (85 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.C (950 : ℚ) * PowerSeries.X ^ 2 +
          PowerSeries.C (3683 : ℚ) * PowerSeries.X ^ 3 - PowerSeries.C (5770 : ℚ) * PowerSeries.X ^ 4 +
          PowerSeries.C (3000 : ℚ) * PowerSeries.X ^ 5 := by
      simp only [map_ofNat]
      ring
    rw [e1, e2]
    ext n
    simp only [F', map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
    by_cases hn : n ≤ 5
    · interval_cases n <;> norm_num [a_closed]
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + 6 := ⟨n - 6, by omega⟩
      simp [a_closed]
      ring
  · rw [a_closed, show (4 : ℕ) ^ n = 2 ^ (2 * n) by rw [pow_mul]; norm_num]
    ring

import OMAStatements.S_oeis_a206248
import Mathlib

-- Proof of the conjectures in OEIS A206248 (statement by @ivillar).
-- Idea: the permanent condition involves only consecutive rows, so the count is a walk count on rows
-- (transfer matrix). From a row (p,q), the next row (r,s) needs p*s = 0 and q*r = 0. Walk counts depend
-- only on how many entries of the row are 0: both (f), exactly one (g), none (h), with
-- f' = f + 6g + 9h, g' = f + 3g, h' = f and a(n) = f(n+1). The characteristic polynomial is
-- t^3 - 4t^2 - 12t + 27 = (t + 3)(t^2 - 7t + 9), which gives the recurrence, the g.f. and, through the
-- power sums of (7 ± sqrt 13)/2, the closed form.

namespace OMAA206248Helpers

open OMA.S_oeis_a206248

abbrev R := Fin 2 → Fin 4

/-- Rows are unconstrained. -/
abbrev ok (_r : R) : Prop := True

/-- Consecutive rows r, s: the subblock they form has zero permanent. -/
abbrev compat (r s : R) : Prop := (r 0 : ℕ) * s 1 + (r 1 : ℕ) * s 0 = 0

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

/-- Walk counts by row type: both entries zero (f), exactly one zero (g), none zero (h). -/
def f : ℕ → ℕ
  | 0 => 1
  | n + 1 => f n + 6 * g n + 9 * h n
where
  g : ℕ → ℕ
  | 0 => 1
  | n + 1 => f n + 3 * g n
  h : ℕ → ℕ
  | 0 => 1
  | n + 1 => f n

abbrev Z (t : R) : Prop := t 0 = 0 ∧ t 1 = 0
abbrev O (t : R) : Prop := t 0 = 0 ∨ t 1 = 0

def V (n : ℕ) (s : R) : ℕ := if Z s then f n else if O s then f.g n else f.h n

theorem cZ : ∀ s : R, (Finset.univ.filter (fun t : R => (ok s ∧ compat s t) ∧ Z t)).card = 1 := by
  decide

theorem cO : ∀ s : R, (Finset.univ.filter (fun t : R => (ok s ∧ compat s t) ∧ ¬ Z t ∧ O t)).card =
    if Z s then 6 else if O s then 3 else 0 := by decide

theorem cN : ∀ s : R, (Finset.univ.filter (fun t : R => (ok s ∧ compat s t) ∧ ¬ Z t ∧ ¬ O t)).card =
    if Z s then 9 else 0 := by decide

theorem tZ : (Finset.univ.filter (fun t : R => True ∧ Z t)).card = 1 := by decide
theorem tO : (Finset.univ.filter (fun t : R => True ∧ ¬ Z t ∧ O t)).card = 6 := by decide
theorem tN : (Finset.univ.filter (fun t : R => True ∧ ¬ Z t ∧ ¬ O t)).card = 9 := by decide

theorem split_V (n : ℕ) (P : Prop) [Decidable P] (t : R) :
    (if P then V n t else 0) = ((if P ∧ Z t then f n else 0) +
      (if P ∧ ¬ Z t ∧ O t then f.g n else 0)) + (if P ∧ ¬ Z t ∧ ¬ O t then f.h n else 0) := by
  unfold V
  by_cases h1 : P
  · rw [if_pos h1]
    by_cases h2 : Z t
    · rw [if_pos h2, if_pos (show P ∧ Z t from ⟨h1, h2⟩),
        if_neg (show ¬(P ∧ ¬ Z t ∧ O t) from fun h => h.2.1 h2),
        if_neg (show ¬(P ∧ ¬ Z t ∧ ¬ O t) from fun h => h.2.1 h2)]
      ring
    · rw [if_neg h2, if_neg (show ¬(P ∧ Z t) from fun h => h2 h.2)]
      by_cases h3 : O t
      · rw [if_pos h3, if_pos (show P ∧ ¬ Z t ∧ O t from ⟨h1, h2, h3⟩),
          if_neg (show ¬(P ∧ ¬ Z t ∧ ¬ O t) from fun h => h.2.2 h3)]
        ring
      · rw [if_neg h3, if_neg (show ¬(P ∧ ¬ Z t ∧ O t) from fun h => h3 h.2.2),
          if_pos (show P ∧ ¬ Z t ∧ ¬ O t from ⟨h1, h2, h3⟩)]
        ring
  · rw [if_neg h1, if_neg (show ¬(P ∧ Z t) from fun h => h1 h.1),
      if_neg (show ¬(P ∧ ¬ Z t ∧ O t) from fun h => h1 h.1),
      if_neg (show ¬(P ∧ ¬ Z t ∧ ¬ O t) from fun h => h1 h.1)]

theorem sum_V (n : ℕ) (P : R → Prop) [DecidablePred P] :
    (∑ t : R, if P t then V n t else 0) =
      (Finset.univ.filter (fun t => P t ∧ Z t)).card * f n +
      (Finset.univ.filter (fun t => P t ∧ ¬ Z t ∧ O t)).card * f.g n +
      (Finset.univ.filter (fun t => P t ∧ ¬ Z t ∧ ¬ O t)).card * f.h n := by
  rw [Finset.sum_congr rfl (fun t _ => split_V n (P t) t), Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_ite, Finset.sum_ite]
  simp only [Finset.sum_const, Finset.sum_const_zero, smul_eq_mul, add_zero, mul_zero]

theorem F_eq (n : ℕ) : ∀ s : R, F n s = V n s := by
  induction n with
  | zero =>
    intro s
    rw [F_zero]
    unfold V
    simp only [ok, if_true]
    split_ifs <;> rfl
  | succ n ih =>
    intro s
    rw [F_succ]
    simp only [ih]
    rw [sum_V n (fun t => ok s ∧ compat s t), cZ s, cO s, cN s]
    unfold V
    split_ifs <;> simp [f, f.g, f.h] <;> ring

theorem a_eq (n : ℕ) : a n = f (n + 1) := by
  unfold a
  rw [Nat.card_congr (Equiv.subtypeEquivRight
      (p := fun x : Fin (n + 1) → R => ∀ i : Fin n, perm (x i.castSucc) (x i.succ) = 0)
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
  simp only [F_eq]
  rw [sum_V n (fun _ => True), tZ, tO, tN]
  simp only [f]
  ring

theorem f_rec (n : ℕ) : f (n + 3) + 27 * f n = 4 * f (n + 2) + 12 * f (n + 1) := by
  simp only [f, f.g, f.h]; ring

theorem a_rec (n : ℕ) : a (n + 3) + 27 * a n = 4 * a (n + 2) + 12 * a (n + 1) := by
  rw [a_eq, a_eq, a_eq, a_eq]
  exact f_rec (n + 1)

theorem a1 : a 1 = 49 := by rw [a_eq]; simp [f, f.g, f.h]
theorem a2 : a 2 = 361 := by rw [a_eq]; simp [f, f.g, f.h]
theorem a3 : a 3 = 1600 := by rw [a_eq]; simp [f, f.g, f.h]

/-- P(n) = r1^n + r2^n and Q(n) = sqrt(13)*(r1^n - r2^n) for r1, r2 = (7 ± sqrt 13)/2. -/
def PQ : ℕ → ℤ × ℤ
  | 0 => (2, 0)
  | 1 => (7, 13)
  | n + 2 => (7 * (PQ (n + 1)).1 - 9 * (PQ n).1, 7 * (PQ (n + 1)).2 - 9 * (PQ n).2)

theorem pq_real (n : ℕ) :
    ((7 + Real.sqrt 13) / 2) ^ n + ((7 - Real.sqrt 13) / 2) ^ n = (PQ n).1 ∧
    Real.sqrt 13 * (((7 + Real.sqrt 13) / 2) ^ n - ((7 - Real.sqrt 13) / 2) ^ n) = (PQ n).2 := by
  have hs : Real.sqrt 13 * Real.sqrt 13 = 13 := Real.mul_self_sqrt (by norm_num)
  have e1 : ((7 + Real.sqrt 13) / 2) ^ 2 = 7 * ((7 + Real.sqrt 13) / 2) - 9 := by
    linear_combination (1 / 4) * hs
  have e2 : ((7 - Real.sqrt 13) / 2) ^ 2 = 7 * ((7 - Real.sqrt 13) / 2) - 9 := by
    linear_combination (1 / 4) * hs
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [PQ]; norm_num
    | 1, _ =>
      refine ⟨?_, ?_⟩
      · simp only [PQ]; push_cast; ring
      · simp only [PQ]; push_cast; linear_combination hs
    | k + 2, ih =>
      obtain ⟨p1, q1⟩ := ih (k + 1) (by omega)
      obtain ⟨p0, q0⟩ := ih k (by omega)
      simp only [PQ]
      push_cast
      refine ⟨?_, ?_⟩
      · linear_combination 7 * p1 - 9 * p0 + ((7 + Real.sqrt 13) / 2) ^ k * e1 +
          ((7 - Real.sqrt 13) / 2) ^ k * e2
      · linear_combination 7 * q1 - 9 * q0 + Real.sqrt 13 * ((7 + Real.sqrt 13) / 2) ^ k * e1 -
          Real.sqrt 13 * ((7 - Real.sqrt 13) / 2) ^ k * e2

theorem closed_int (k : ℕ) :
    13 * (a (k + 1) : ℤ) = 54 * (-3) ^ (k + 1) + 77 * (PQ (k + 1)).1 + 20 * (PQ (k + 1)).2 ∧
    13 * (a (k + 2) : ℤ) = 54 * (-3) ^ (k + 2) + 77 * (PQ (k + 2)).1 + 20 * (PQ (k + 2)).2 ∧
    13 * (a (k + 3) : ℤ) = 54 * (-3) ^ (k + 3) + 77 * (PQ (k + 3)).1 + 20 * (PQ (k + 3)).2 := by
  induction k with
  | zero => refine ⟨?_, ?_, ?_⟩ <;> simp [a1, a2, a3, PQ] <;> norm_num
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨h2, h3, ?_⟩
    have hr := a_rec (k + 1)
    have hr' : ((a (k + 1 + 3) : ℕ) : ℤ) + 27 * a (k + 1) = 4 * a (k + 1 + 2) + 12 * a (k + 1 + 1) := by
      exact_mod_cast hr
    have p3 : PQ (k + 4) = (7 * (PQ (k + 3)).1 - 9 * (PQ (k + 2)).1,
        7 * (PQ (k + 3)).2 - 9 * (PQ (k + 2)).2) := rfl
    have p2 : PQ (k + 3) = (7 * (PQ (k + 2)).1 - 9 * (PQ (k + 1)).1,
        7 * (PQ (k + 2)).2 - 9 * (PQ (k + 1)).2) := rfl
    show 13 * (a (k + 4) : ℤ) = 54 * (-3) ^ (k + 4) + 77 * (PQ (k + 4)).1 + 20 * (PQ (k + 4)).2
    rw [p3]
    rw [p2] at h3 ⊢
    simp only at h3 ⊢
    have e4 : (a (k + 4) : ℤ) = 4 * a (k + 3) + 12 * a (k + 2) - 27 * a (k + 1) := by
      have : ((a (k + 4) : ℕ) : ℤ) + 27 * a (k + 1) = 4 * a (k + 3) + 12 * a (k + 2) := hr'
      linarith
    rw [e4]
    linear_combination 4 * h3 + 12 * h2 - 27 * h1

end OMAA206248Helpers

open OMA.S_oeis_a206248 OMAA206248Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a206248.main := by
  refine ⟨fun n hn => ?_, ?_, fun n hn => ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    rw [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
      show k + 4 - 3 = k + 1 by omega]
    have h := a_rec (k + 1)
    have h' : ((a (k + 4) : ℕ) : ℤ) + 27 * a (k + 1) = 4 * a (k + 3) + 12 * a (k + 2) := by
      exact_mod_cast h
    linarith
  · rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    set F' := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
    have e1 : F' * ((1 + 3 * PowerSeries.X) * (1 - 7 * PowerSeries.X + 9 * PowerSeries.X ^ 2)) =
        F' - PowerSeries.C (4 : ℚ) * (PowerSeries.X ^ 1 * F') -
          PowerSeries.C (12 : ℚ) * (PowerSeries.X ^ 2 * F') +
          PowerSeries.C (27 : ℚ) * (PowerSeries.X ^ 3 * F') := by
      simp only [map_ofNat]
      ring
    have e2 : (PowerSeries.X * (49 + 165 * PowerSeries.X - 432 * PowerSeries.X ^ 2) : PowerSeries ℚ) =
        PowerSeries.C (49 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (165 : ℚ) * PowerSeries.X ^ 2 -
          PowerSeries.C (432 : ℚ) * PowerSeries.X ^ 3 := by
      simp only [map_ofNat]
      ring
    rw [e1, e2]
    ext n
    simp only [F', map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
    by_cases hn : n ≤ 3
    · interval_cases n <;> norm_num [a1, a2, a3]
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
      have h := a_rec (j + 1)
      have q : ((a (j + 4) : ℕ) : ℚ) + 27 * a (j + 1) = 4 * a (j + 3) + 12 * a (j + 2) := by
        exact_mod_cast h
      simp
      linear_combination q
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hc := (closed_int k).1
    have hc' : 13 * (a (k + 1) : ℝ) = 54 * (-3) ^ (k + 1) + 77 * ((PQ (k + 1)).1 : ℝ) +
        20 * ((PQ (k + 1)).2 : ℝ) := by exact_mod_cast hc
    obtain ⟨hp, hq⟩ := pq_real (k + 1)
    rw [← hp, ← hq] at hc'
    have h2 : (2 : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) = ((1 / 2) : ℝ) ^ (k + 1) := by
      rw [zpow_neg, zpow_natCast, one_div, inv_pow]
    rw [h2]
    have e1 : ((1 / 2 : ℝ)) ^ (k + 1) * (7 - Real.sqrt 13) ^ (k + 1) = ((7 - Real.sqrt 13) / 2) ^ (k + 1) := by
      rw [← mul_pow]; ring
    have e2 : ((1 / 2 : ℝ)) ^ (k + 1) * (7 + Real.sqrt 13) ^ (k + 1) = ((7 + Real.sqrt 13) / 2) ^ (k + 1) := by
      rw [← mul_pow]; ring
    have e3 : ((1 / 2 : ℝ)) ^ (k + 1) * ((-1) ^ (k + 1) * 2 ^ (1 + (k + 1)) * 3 ^ (3 + (k + 1))) =
        54 * (-3) ^ (k + 1) := by
      have hA : ((1 / 2 : ℝ)) ^ (k + 1) * 2 ^ (k + 1) = 1 := by rw [← mul_pow]; norm_num
      have hm : (-3 : ℝ) ^ (k + 1) = (-1) ^ (k + 1) * 3 ^ (k + 1) := by rw [← mul_pow]; norm_num
      have h2' : (2 : ℝ) ^ (1 + (k + 1)) = 2 * 2 ^ (k + 1) := by ring
      have h3' : (3 : ℝ) ^ (3 + (k + 1)) = 27 * 3 ^ (k + 1) := by ring
      rw [h2', h3', hm]
      linear_combination (54 * (-1 : ℝ) ^ (k + 1) * 3 ^ (k + 1)) * hA
    push_cast at hc' ⊢
    linear_combination (1 / 13 : ℝ) * hc' - (1 / 13 : ℝ) * e3 - ((77 - 20 * Real.sqrt 13) / 13) * e1 -
      ((77 + 20 * Real.sqrt 13) / 13) * e2

import OMAStatements.S_oeis_a251293
import Mathlib

/-!
# OEIS A251293

A row belongs to one of three classes for counting continuations: the two constant
rows of sums 0 and 6, the four remaining rows whose sums are divisible by 3, and
the ten rows with nonzero residues. Their numbers of continuations follow a
two-variable linear recurrence and a geometric progression.

Source: https://oeis.org/A251293.
Original proof by @physbuzz.
-/
namespace OMA.P_oeis_a251293

open OMA.S_oeis_a251293 Real
open scoped BigOperators

abbrev R := Fin 2 → Fin 4

def adj (r s : R) : Prop :=
  (r 0 : ℕ) + r 1 + s 0 + s 1 ∈ ({3, 6, 9} : Finset ℕ)

instance (r s : R) : Decidable (adj r s) := by unfold adj; infer_instance

open Classical

def LL : ℕ → Finset (List R)
  | 0 => {[]}
  | n + 1 => ((Finset.univ : Finset R) ×ˢ LL n).image (fun p => p.1 :: p.2)

lemma mem_LL (n : ℕ) (l : List R) : l ∈ LL n ↔ l.length = n := by
  induction n generalizing l with
  | zero => simp [LL]
  | succ n ih => cases l <;> simp [LL, ih]

lemma card_cons (n : ℕ) (Q : List R → Prop) [DecidablePred Q] :
    ((LL (n + 1)).filter Q).card = ∑ s : R, ((LL n).filter (fun m => Q (s :: m))).card := by
  rw [LL, Finset.filter_image, Finset.card_image_of_injective _ (by
    intro p q h
    simp only [List.cons.injEq] at h
    exact Prod.ext h.1 h.2)]
  simp only [Finset.card_filter, Finset.sum_product]

noncomputable def f (n : ℕ) (r : R) : ℕ := ((LL n).filter (fun l => IsSolution (r :: l))).card

lemma a_eq (n : ℕ) : a n = ∑ r : R, f n r := by
  have e : {l : List R // l.length = n + 1 ∧ IsSolution l} ≃
      {l // l ∈ (LL (n + 1)).filter IsSolution} :=
    Equiv.subtypeEquivRight (fun l => by simp [mem_LL])
  rw [a, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, card_cons]
  rfl

lemma f_succ (n : ℕ) (r : R) : f (n + 1) r = ∑ s : R, if adj r s then f n s else 0 := by
  unfold f
  rw [card_cons]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hs (m : List R) : IsSolution (r :: s :: m) ↔ adj r s ∧ IsSolution (s :: m) := by
    change List.IsChain adj (r :: s :: m) ↔ adj r s ∧ List.IsChain adj (s :: m)
    simp [List.isChain_cons]
  simp only [hs]
  split_ifs with h <;> simp [h]

lemma sum_rows {M : Type*} [AddCommMonoid M] (g : R → M) :
    ∑ s : R, g s = ∑ i : Fin 4, ∑ j : Fin 4, g ![i, j] := by
  let e : Fin 4 × Fin 4 ≃ R :=
    ⟨fun p => ![p.1, p.2], fun r => (r 0, r 1), fun p => by simp,
      fun r => by ext i; fin_cases i <;> rfl⟩
  rw [← e.sum_comp, Fintype.sum_prod_type]
  rfl

def countAt (u v w : ℕ) (r : R) : ℕ :=
  let s := (r 0 : ℕ) + r 1
  if s = 0 ∨ s = 6 then u else if s = 3 then v else w

set_option maxHeartbeats 8000000 in
lemma countAt_step (u v w : ℕ) (r : R) :
    (∑ s : R, if adj r s then countAt u v w s else 0) =
      countAt (u + 4 * v) (2 * u + 4 * v) (5 * w) r := by
  obtain ⟨i, j, rfl⟩ : ∃ i j : Fin 4, ![i, j] = r :=
    ⟨r 0, r 1, by ext k; fin_cases k <;> rfl⟩
  rw [sum_rows]
  simp only [Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp +decide [countAt] <;> omega

lemma countAt_total (u v w : ℕ) : (∑ r : R, countAt u v w r) = 2 * u + 4 * v + 10 * w := by
  rw [sum_rows]
  simp +decide [Fin.sum_univ_four, countAt]
  omega

def uv : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | n + 1 => let p := uv n; (p.1 + 4 * p.2, 2 * p.1 + 4 * p.2)

lemma f_formula (n : ℕ) (r : R) : f n r = countAt (uv n).1 (uv n).2 (5 ^ n) r := by
  induction n generalizing r with
  | zero => simp [f, LL, Finset.filter_singleton, IsSolution, countAt, uv]
  | succ n ih =>
    rw [f_succ]
    simp only [ih, countAt_step, uv, pow_succ, Nat.mul_comm (5 ^ n) 5]

lemma a_formula (n : ℕ) : a n = (uv (n + 1)).2 + 10 * 5 ^ n := by
  simp only [a_eq, f_formula, countAt_total, uv]

theorem a_rec (n : ℕ) :
    (a (n + 3) : ℤ) = 10 * (a (n + 2) : ℤ) + (-21) * (a (n + 1) : ℤ) + (-20) * (a (n + 0) : ℤ) := by
  simp only [Nat.add_zero, a_formula, uv, pow_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat]
  ring

lemma a0 : (a 0 : ℤ) = 16 := by norm_num [a_formula, uv]
lemma a1 : (a 1 : ℤ) = 84 := by norm_num [a_formula, uv]
lemma a2 : (a 2 : ℤ) = 444 := by norm_num [a_formula, uv]
lemma a3 : (a 3 : ℤ) = 2356 := by norm_num [a_formula, uv]

lemma z2 (n : ℕ) : (2 : ℝ) ^ (-(n : ℤ)) = (1 / 2) ^ n := by
  rw [zpow_neg, zpow_natCast, one_div, inv_pow]

noncomputable def S (n : ℕ) : ℝ := (1 / 41) * (2 : ℝ) ^ (-(n : ℤ)) * (41 * 10 ^ (1 + n) + (123 - 19 * √41) * (5 - √41) ^ n + (5 + √41) ^ n * (123 + 19 * √41))

lemma hs : (√41) ^ 2 = 41 := Real.sq_sqrt (by norm_num)

lemma S_rec (n : ℕ) : S (n + 3) = (10 : ℝ) * S (n + 2) + (-21 : ℝ) * S (n + 1) + (-20 : ℝ) * S (n + 0) := by
  unfold S
  simp only [z2]
  linear_combination (19*((1 / 2 : ℝ) ^ n)*((5 - √41) ^ n)*(√41)^2/328 - 7*((1 / 2 : ℝ) ^ n)*((5 - √41) ^ n)*(√41)/82 - 15*((1 / 2 : ℝ) ^ n)*((5 - √41) ^ n)/8 + 19*((1 / 2 : ℝ) ^ n)*((5 + √41) ^ n)*(√41)^2/328 + 7*((1 / 2 : ℝ) ^ n)*((5 + √41) ^ n)*(√41)/82 - 15*((1 / 2 : ℝ) ^ n)*((5 + √41) ^ n)/8) * hs

lemma S1 : S 1 = 84 := by
  unfold S
  simp only [z2]
  linear_combination (19/41) * hs

lemma S2 : S 2 = 444 := by
  unfold S
  simp only [z2]
  linear_combination (313/82) * hs

lemma S3 : S 3 = 2356 := by
  unfold S
  simp only [z2]
  linear_combination (19*(√41)^2/164 + 4049/164) * hs


theorem binet (n : ℕ) (hn : 1 ≤ n) : (a n : ℝ) = S n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 4 with h | h
    · interval_cases n <;> first | (rw [S1]; exact_mod_cast a1) | (rw [S2]; exact_mod_cast a2) | (rw [S3]; exact_mod_cast a3)
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have hr := a_rec (m + 1)
      have hr' : (a (m + 4) : ℝ) = (10 : ℝ) * (a (m + 3) : ℝ) + (-21 : ℝ) * (a (m + 2) : ℝ) + (-20 : ℝ) * (a (m + 1) : ℝ) := by
        have := congrArg (fun z : ℤ => (z : ℝ)) hr
        simp only [show m + 1 + 3 = m + 4 by omega, show m + 1 + 2 = m + 3 by omega, show m + 1 + 1 = m + 2 by omega, show m + 1 + 0 = m + 1 by omega] at this
        push_cast at this
        linarith
      rw [hr', show m + 4 = (m + 1) + 3 by omega, S_rec]
      rw [ih (m + 3) (by omega) (by omega), ih (m + 2) (by omega) (by omega), ih (m + 1) (by omega) (by omega)]

open PowerSeries in
theorem full :
    (∀ n > 3, (a n : ℤ) = 10 * a (n - 1) - 21 * a (n - 2) - 20 * a (n - 3)) ∧
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * ((1 - 5 * X) * (1 - 5 * X - 4 * X ^ 2)) =
      4 * (21 - 99 * X - 80 * X ^ 2)) ∧
    (∀ n ≥ 1, (a n : ℝ) = (1 / 41) * (2 : ℝ) ^ (-(n : ℤ)) * (41 * 10 ^ (1 + n) +
      (123 - 19 * √41) * (5 - √41) ^ n + (5 + √41) ^ n * (123 + 19 * √41))) := by
  refine ⟨fun n hn => ?_, ?_, fun n hn => binet n hn⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have hr := a_rec (m + 1)
    simp only [show m + 1 + 3 = m + 4 by omega, show m + 1 + 2 = m + 3 by omega, show m + 1 + 1 = m + 2 by omega, show m + 1 + 0 = m + 1 by omega] at hr
    simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega]
    rw [hr]; ring
  · have hX : (PowerSeries.mk fun n => (a (n + 1) : ℚ)) * ((1 - 5 * X) * (1 - 5 * X - 4 * X ^ 2)) =
        PowerSeries.mk (fun n => (a (n + 1) : ℚ)) + C (-10 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 1) + C (21 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 2) + C (20 : ℚ) * (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * X ^ 3) := by
      simp only [map_neg, map_ofNat, neg_mul]; ring
    rw [hX, show (4 * (21 - 99 * X - 80 * X ^ 2) : PowerSeries ℚ) = C (84 : ℚ) * X ^ 0 + C (-396 : ℚ) * X ^ 1 + C (-320 : ℚ) * X ^ 2 by
      simp only [map_neg, map_ofNat, neg_mul, pow_zero, mul_one]; ring]
    ext c
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    rcases Nat.lt_or_ge c 3 with h | h
    · interval_cases c <;> simp [show (a 1 : ℚ) = 84 by exact_mod_cast a1, show (a 2 : ℚ) = 444 by exact_mod_cast a2, show (a 3 : ℚ) = 2356 by exact_mod_cast a3] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, c = m + 3 := ⟨c - 3, by omega⟩
      simp (disch := omega) only [if_pos, show m + 3 - 1 = m + 2 by omega,
        show m + 3 - 2 = m + 1 by omega, Nat.add_sub_cancel, coeff_C]
      have hr := a_rec (m + 1)
      simp only [show m + 1 + 3 = m + 3 + 1 by omega, show m + 1 + 2 = m + 2 + 1 by omega, show m + 1 + 1 = m + 1 + 1 by omega, show m + 1 + 0 = m + 0 + 1 by omega] at hr
      have hq := congrArg (fun z : ℤ => (z : ℚ)) hr
      push_cast at hq
      simp
      linarith

end OMA.P_oeis_a251293

theorem OMA.solution : type_of% @OMA.S_oeis_a251293.main := OMA.P_oeis_a251293.full

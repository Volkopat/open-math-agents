import OMAStatements.S_oeis_a100381
import Mathlib

/-!
# Proof of OEIS A100381 continued fraction and series identities

We prove Peter Bala's finite continued fractions for the partial sums of `1 / a(k)` and
`(-1)^k / a(k)` where `a(n) = 2^n * binomial(n, 2)`, together with the corresponding infinite
series evaluations `1 - log 2` and `3 * log(3/2) - 1` and the limits of the convergents.

Method:
1. Establish `(a (k + 2) : ℝ) = 2^(k + 1) * (k + 1) * (k + 2)` and its partial fraction
   decomposition.
2. Express `K j m` and `L j m` explicitly in terms of normalized tail sums `S j m` and `T j m`,
   proved by induction on `m` generalizing `j`, with `1 / 2 ≤ T j m ≤ 1` ensuring all
   denominators remain strictly positive.
3. Evaluate both infinite series via `Real.hasSum_pow_div_log_of_abs_lt_one` at `x = 1/2` and
   `x = -1/2`, and deduce the limits of `1 / K 0 n` and `1 / L 0 n` from `HasSum.tendsto_sum_nat`.
-/

namespace OMA.A100381Proof

open OMA.S_oeis_a100381

private lemma two_mul_choose_two (k : ℕ) : 2 * (k + 2).choose 2 = (k + 1) * (k + 2) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right, mul_add, ih]
    ring

private lemma a_cast_eq (k : ℕ) :
    (a (k + 2) : ℝ) = (2 : ℝ) ^ (k + 1) * ((k : ℝ) + 1) * ((k : ℝ) + 2) := by
  have h : a (k + 2) = 2 ^ (k + 1) * ((k + 1) * (k + 2)) := by
    dsimp [a]
    rw [pow_succ, mul_assoc, ← two_mul_choose_two k]
  rw [h]
  push_cast
  ring

private lemma a_cast_pos (k : ℕ) : 0 < (a (k + 2) : ℝ) := by
  rw [a_cast_eq]
  positivity

private lemma inv_a_eq (k : ℕ) :
    (1 : ℝ) / (a (k + 2) : ℝ) =
      (1 / 2 : ℝ) ^ (k + 1) / ((k : ℝ) + 1) - (1 / 2 : ℝ) ^ (k + 1) / ((k : ℝ) + 2) := by
  rw [a_cast_eq, one_div_pow]
  field_simp
  ring

private lemma sum_Icc_eq_sum_range (f : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 2 (n + 2), f k = ∑ i ∈ Finset.range (n + 1), f (i + 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 by omega, Finset.sum_Icc_succ_top (by omega),
      Finset.sum_range_succ, ih]

private noncomputable def S (j m : ℕ) : ℝ :=
  (2 : ℝ) ^ (j + 1) * ((j : ℝ) + 1) * ((j : ℝ) + 2) *
    ∑ i ∈ Finset.range (m + 1), (1 : ℝ) / (a (j + 2 + i) : ℝ)

private lemma S_zero (j : ℕ) : S j 0 = 1 := by
  unfold S
  rw [Nat.zero_add, Finset.range_one, Finset.sum_singleton, add_zero, a_cast_eq]
  field_simp

private lemma S_pos (j m : ℕ) : 0 < S j m := by
  apply mul_pos (by positivity)
  apply Finset.sum_pos
  · intro i _
    apply div_pos one_pos
    rw [show j + 2 + i = (j + i) + 2 by omega]
    exact a_cast_pos (j + i)
  · exact ⟨0, Finset.mem_range.mpr (Nat.succ_pos m)⟩

private lemma S_succ (j m : ℕ) :
    S j (m + 1) = 1 + ((j : ℝ) + 1) / (2 * ((j : ℝ) + 3)) * S (j + 1) m := by
  unfold S
  rw [Finset.sum_range_succ']
  have hsum :
      ∑ i ∈ Finset.range (m + 1), (1 : ℝ) / (a (j + 2 + (i + 1)) : ℝ) =
        ∑ i ∈ Finset.range (m + 1), (1 : ℝ) / (a (j + 1 + 2 + i) : ℝ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show j + 2 + (i + 1) = j + 1 + 2 + i by omega]
  rw [hsum, add_zero, a_cast_eq j]
  set P := ∑ i ∈ Finset.range (m + 1), (1 : ℝ) / (a (j + 1 + 2 + i) : ℝ)
  push_cast
  rw [pow_succ (2 : ℝ) (j + 1)]
  field_simp
  ring

private lemma K_eq (m : ℕ) : ∀ j : ℕ, K j m = (j : ℝ) + 2 * ((j : ℝ) + 2) / S j m := by
  induction m with
  | zero =>
    intro j
    simp only [K, S_zero, div_one]
    ring
  | succ m ih =>
    intro j
    have hS1 : 0 < S (j + 1) m := S_pos (j + 1) m
    have hK1 : K (j + 1) m = ((j : ℝ) + 1) + 2 * ((j : ℝ) + 3) / S (j + 1) m := by
      rw [ih (j + 1)]
      push_cast
      ring
    have hdenom1 : ((j : ℝ) + 1) + 2 * ((j : ℝ) + 3) / S (j + 1) m ≠ 0 := by positivity
    have hdenom2 : 1 + ((j : ℝ) + 1) / (2 * ((j : ℝ) + 3)) * S (j + 1) m ≠ 0 := by positivity
    rw [K, hK1, S_succ]
    field_simp
    ring

private lemma part1 (n : ℕ) :
    ∑ k ∈ Finset.Icc 2 (n + 2), (1 : ℝ) / (a k : ℝ) = 1 / K 0 n := by
  rw [sum_Icc_eq_sum_range, K_eq n 0]
  have hS0 : S 0 n = 4 * ∑ i ∈ Finset.range (n + 1), (1 : ℝ) / (a (i + 2) : ℝ) := by
    unfold S
    have hsum :
        ∑ i ∈ Finset.range (n + 1), (1 : ℝ) / (a (0 + 2 + i) : ℝ) =
          ∑ i ∈ Finset.range (n + 1), (1 : ℝ) / (a (i + 2) : ℝ) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show 0 + 2 + i = i + 2 by omega]
    rw [hsum]
    norm_num
  have hpos : 0 < ∑ i ∈ Finset.range (n + 1), (1 : ℝ) / (a (i + 2) : ℝ) := by
    have h := S_pos 0 n
    linarith
  rw [hS0]
  push_cast
  field_simp
  ring

private noncomputable def T (j m : ℕ) : ℝ :=
  (2 : ℝ) ^ (j + 1) * ((j : ℝ) + 1) * ((j : ℝ) + 2) *
    ∑ i ∈ Finset.range (m + 1), (-1 : ℝ) ^ i / (a (j + 2 + i) : ℝ)

private lemma T_zero (j : ℕ) : T j 0 = 1 := by
  unfold T
  rw [Nat.zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, add_zero, a_cast_eq]
  field_simp

private lemma T_succ (j m : ℕ) :
    T j (m + 1) = 1 - ((j : ℝ) + 1) / (2 * ((j : ℝ) + 3)) * T (j + 1) m := by
  unfold T
  rw [Finset.sum_range_succ']
  have hsum :
      ∑ i ∈ Finset.range (m + 1), (-1 : ℝ) ^ (i + 1) / (a (j + 2 + (i + 1)) : ℝ) =
        -(∑ i ∈ Finset.range (m + 1), (-1 : ℝ) ^ i / (a (j + 1 + 2 + i) : ℝ)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_succ, show j + 2 + (i + 1) = j + 1 + 2 + i by omega]
    ring
  rw [hsum, pow_zero, add_zero, a_cast_eq j]
  set Q := ∑ i ∈ Finset.range (m + 1), (-1 : ℝ) ^ i / (a (j + 1 + 2 + i) : ℝ)
  push_cast
  rw [pow_succ (2 : ℝ) (j + 1)]
  field_simp
  ring

private lemma T_bounds (m : ℕ) : ∀ j : ℕ, (1 / 2 : ℝ) ≤ T j m ∧ T j m ≤ 1 := by
  induction m with
  | zero =>
    intro j
    rw [T_zero]
    norm_num
  | succ m ih =>
    intro j
    obtain ⟨hlo, hhi⟩ := ih (j + 1)
    rw [T_succ]
    have hr_pos : 0 < ((j : ℝ) + 1) / (2 * ((j : ℝ) + 3)) := by positivity
    have hr_le : ((j : ℝ) + 1) / (2 * ((j : ℝ) + 3)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    constructor <;> nlinarith

private lemma L_eq (m : ℕ) : ∀ j : ℕ, L j m = -(j : ℝ) + 2 * ((j : ℝ) + 2) / T j m := by
  induction m with
  | zero =>
    intro j
    simp only [L, T_zero, div_one]
    ring
  | succ m ih =>
    intro j
    obtain ⟨hlo1, hhi1⟩ := T_bounds m (j + 1)
    set t := T (j + 1) m
    have ht_pos : 0 < t := by linarith
    have hlin : 2 * ((j : ℝ) + 3) - ((j : ℝ) + 1) * t ≠ 0 := by nlinarith
    have hL1 : L (j + 1) m = -((j : ℝ) + 1) + 2 * ((j : ℝ) + 3) / t := by
      rw [ih (j + 1)]
      push_cast
      ring
    have h1 : -((j : ℝ) + 1) + 2 * ((j : ℝ) + 3) / t =
        (2 * ((j : ℝ) + 3) - ((j : ℝ) + 1) * t) / t := by
      field_simp
      ring
    have h2 : 1 - ((j : ℝ) + 1) / (2 * ((j : ℝ) + 3)) * t =
        (2 * ((j : ℝ) + 3) - ((j : ℝ) + 1) * t) / (2 * ((j : ℝ) + 3)) := by
      field_simp
    rw [L, hL1, T_succ, h1, h2]
    field_simp
    ring

private lemma part2 (n : ℕ) :
    ∑ k ∈ Finset.Icc 2 (n + 2), (-1 : ℝ) ^ k / (a k : ℝ) = 1 / L 0 n := by
  rw [sum_Icc_eq_sum_range, L_eq n 0]
  have hT0 : T 0 n = 4 * ∑ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ (i + 2) / (a (i + 2) : ℝ) := by
    unfold T
    have hsum :
        ∑ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ i / (a (0 + 2 + i) : ℝ) =
          ∑ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ (i + 2) / (a (i + 2) : ℝ) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show 0 + 2 + i = i + 2 by omega, pow_add]
      norm_num
    rw [hsum]
    norm_num
  have hpos : 0 < ∑ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ (i + 2) / (a (i + 2) : ℝ) := by
    have h := (T_bounds n 0).1
    linarith
  rw [hT0]
  push_cast
  field_simp
  ring

private lemma part3 : HasSum (fun k : ℕ => (1 : ℝ) / (a (k + 2) : ℝ)) (1 - Real.log 2) := by
  have h1 : HasSum (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1) / ((k : ℝ) + 1)) (Real.log 2) := by
    have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := (1 / 2 : ℝ)) (by norm_num)
    rw [show (1 : ℝ) - 1 / 2 = (2 : ℝ)⁻¹ by norm_num, Real.log_inv, neg_neg] at h
    exact h
  have h2 : HasSum (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 2) / ((k : ℝ) + 2)) (Real.log 2 - 1 / 2) := by
    have h := (hasSum_nat_add_iff' (f := fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1) / ((k : ℝ) + 1)) 1).mpr h1
    have hsum : Real.log 2 - ∑ i ∈ Finset.range 1, (1 / 2 : ℝ) ^ (i + 1) / ((i : ℝ) + 1) =
        Real.log 2 - 1 / 2 := by
      norm_num
    rw [hsum] at h
    refine h.congr_fun fun k => ?_
    push_cast
    ring
  have h3 : HasSum (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1) / ((k : ℝ) + 2)) (2 * Real.log 2 - 1) := by
    have h := h2.mul_left 2
    rw [show 2 * (Real.log 2 - 1 / 2) = 2 * Real.log 2 - 1 by ring] at h
    refine h.congr_fun fun k => ?_
    rw [pow_succ (1 / 2 : ℝ) (k + 1)]
    ring
  have h4 := h1.sub h3
  rw [show Real.log 2 - (2 * Real.log 2 - 1) = 1 - Real.log 2 by ring] at h4
  exact h4.congr_fun inv_a_eq

private lemma part4 :
    Filter.Tendsto (fun n : ℕ => 1 / K 0 n) Filter.atTop (nhds (1 - Real.log 2)) := by
  have ht := (Filter.tendsto_add_atTop_iff_nat 1).mpr part3.tendsto_sum_nat
  refine ht.congr fun n => ?_
  rw [← sum_Icc_eq_sum_range (fun k => (1 : ℝ) / (a k : ℝ)), part1]

private lemma part5 :
    HasSum (fun k : ℕ => (-1 : ℝ) ^ (k + 2) / (a (k + 2) : ℝ)) (3 * Real.log (3 / 2) - 1) := by
  have h1 :
      HasSum (fun k : ℕ => (-1 : ℝ) ^ (k + 2) * (1 / 2 : ℝ) ^ (k + 1) / ((k : ℝ) + 1))
        (Real.log (3 / 2)) := by
    have h := (Real.hasSum_pow_div_log_of_abs_lt_one (x := (-1 / 2 : ℝ)) (by norm_num)).neg
    rw [show (1 : ℝ) - (-1 / 2 : ℝ) = 3 / 2 by norm_num, neg_neg] at h
    refine h.congr_fun fun k => ?_
    rw [show (-1 / 2 : ℝ) = (-1 : ℝ) * (1 / 2 : ℝ) by ring, mul_pow, pow_succ (-1 : ℝ) (k + 1)]
    ring
  have h2 :
      HasSum (fun k : ℕ => (-1 : ℝ) ^ (k + 3) * (1 / 2 : ℝ) ^ (k + 2) / ((k : ℝ) + 2))
        (Real.log (3 / 2) - 1 / 2) := by
    have h := (hasSum_nat_add_iff'
      (f := fun k : ℕ => (-1 : ℝ) ^ (k + 2) * (1 / 2 : ℝ) ^ (k + 1) / ((k : ℝ) + 1)) 1).mpr h1
    have hsum :
        Real.log (3 / 2) -
          ∑ i ∈ Finset.range 1, (-1 : ℝ) ^ (i + 2) * (1 / 2 : ℝ) ^ (i + 1) / ((i : ℝ) + 1) =
          Real.log (3 / 2) - 1 / 2 := by
      norm_num
    rw [hsum] at h
    refine h.congr_fun fun k => ?_
    push_cast
    ring
  have h3 :
      HasSum (fun k : ℕ => (-1 : ℝ) ^ (k + 2) * (1 / 2 : ℝ) ^ (k + 1) / ((k : ℝ) + 2))
        (1 - 2 * Real.log (3 / 2)) := by
    have h := h2.mul_left (-2)
    rw [show (-2 : ℝ) * (Real.log (3 / 2) - 1 / 2) = 1 - 2 * Real.log (3 / 2) by ring] at h
    refine h.congr_fun fun k => ?_
    rw [pow_succ (-1 : ℝ) (k + 2), pow_succ (1 / 2 : ℝ) (k + 1)]
    ring
  have h4 := h1.sub h3
  rw [show Real.log (3 / 2) - (1 - 2 * Real.log (3 / 2)) = 3 * Real.log (3 / 2) - 1 by ring] at h4
  refine h4.congr_fun fun k => ?_
  rw [show (-1 : ℝ) ^ (k + 2) / (a (k + 2) : ℝ) =
      (-1 : ℝ) ^ (k + 2) * ((1 : ℝ) / (a (k + 2) : ℝ)) by ring, inv_a_eq]
  ring

private lemma part6 :
    Filter.Tendsto (fun n : ℕ => 1 / L 0 n) Filter.atTop (nhds (3 * Real.log (3 / 2) - 1)) := by
  have ht := (Filter.tendsto_add_atTop_iff_nat 1).mpr part5.tendsto_sum_nat
  refine ht.congr fun n => ?_
  rw [← sum_Icc_eq_sum_range (fun k => (-1 : ℝ) ^ k / (a k : ℝ)), part2]

end OMA.A100381Proof

open OMA.A100381Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a100381.main :=
  ⟨part1, part2, part3, part4, part5, part6⟩

import OMAStatements.S_oeis_a267804
import Mathlib

-- Problem: A267804: Binary representation of the n-th iteration of the 'Rule 214' elementary
-- cellular automaton starting with a single ON (black) cell.
-- Upstream: formal-conjectures statements/oeis-a267804.lean:0 (declaration OMA.S_oeis_a267804.main)
-- Credit: @npnelson (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Proof. Write j = i + t for the offset of cell i from the left edge of the light cone at time
-- t. By induction on t, the cell is ON exactly when 0 <= j <= 2t and
--   t even: j mod 4 is not 1          (the row is 1011 1011 ... 1011 1),
--   t odd:  j mod 4 < 2 or j = 2t     (the row is 1100 1100 ... 1100 111).
-- Hence a(n + 2) = 10000 a(n) + 111 for even n and a(n + 2) = 10000 a(n) - 9889 for odd n,
-- which gives a(n + 4) = 10001 a(n + 2) - 10000 a(n). With a(0) = 1, a(1) = 111,
-- a(2) = 10111 and a(3) = 1100111 the generating function follows by comparing coefficients.

namespace Rule214Proof

open OMA.S_oeis_a267804 Finset

theorem rule_truth (l c r : Bool) :
    ruleOut 214 l c r = true ↔
      (l = true ∧ c = true) ∨ (l = true ∧ c ≠ true ∧ r ≠ true) ∨
      (l ≠ true ∧ c = true ∧ r ≠ true) ∨ (l ≠ true ∧ c ≠ true ∧ r = true) := by
  cases l <;> cases c <;> cases r <;> decide

/-- The predicted state of cell `i` at time `t`. -/
def Q (t : ℕ) (i : ℤ) : Prop :=
  -(t : ℤ) ≤ i ∧ i ≤ (t : ℤ) ∧
    ((t % 2 = 0 ∧ (i + t) % 4 ≠ 1) ∨ (t % 2 = 1 ∧ ((i + t) % 4 < 2 ∨ i = t)))

theorem row (t : ℕ) (i : ℤ) : cell 214 t i = true ↔ Q t i := by
  induction t generalizing i with
  | zero =>
    unfold Q
    simp [cell]
    omega
  | succ t ih =>
    simp only [cell, rule_truth, ne_eq, ih]
    by_cases hA : Q t (i - 1) <;> by_cases hB : Q t i <;> by_cases hC : Q t (i + 1) <;>
      by_cases hD : Q (t + 1) i <;>
      first
        | tauto
        | (exfalso
           unfold Q at hA hB hC hD
           push_cast at hA hB hC hD
           omega)

/-- The digit at offset `j` of row `n`. -/
def digit (n j : ℕ) : Prop :=
  (n % 2 = 0 ∧ j % 4 ≠ 1) ∨ (n % 2 = 1 ∧ (j % 4 < 2 ∨ j = 2 * n))

instance (n j : ℕ) : Decidable (digit n j) := by
  unfold digit
  infer_instance

theorem word (n : ℕ) :
    a n = ∑ j ∈ range (2 * n + 1), if digit n j then (10 : ℤ) ^ (2 * n - j) else 0 := by
  unfold a
  refine sum_congr rfl fun j hj => ?_
  have hj' := mem_range.mp hj
  have iffDigit : cell 214 n ((j : ℤ) - n) = true ↔ digit n j := by
    rw [row]
    unfold Q digit
    omega
  simp only [iffDigit]

/-- The correction when two rows are skipped. -/
def corr (n : ℕ) : ℤ := if n % 2 = 0 then 111 else -9889

theorem append_four (n : ℕ) : a (n + 2) = 10000 * a n + corr n := by
  rw [word, word]
  have len : 2 * (n + 2) + 1 = 2 * n + 1 + 1 + 1 + 1 + 1 := by omega
  rw [len, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ,
    sum_range_succ]
  have main : ∑ j ∈ range (2 * n), (if digit (n + 2) j then (10 : ℤ) ^ (2 * (n + 2) - j) else 0)
      = 10000 * ∑ j ∈ range (2 * n), (if digit n j then (10 : ℤ) ^ (2 * n - j) else 0) := by
    rw [mul_sum]
    refine sum_congr rfl fun j hj => ?_
    have hj' := mem_range.mp hj
    have exp : 2 * (n + 2) - j = (2 * n - j) + 4 := by omega
    have eqd : digit (n + 2) j ↔ digit n j := by
      unfold digit
      omega
    rw [exp, pow_add]
    simp only [eqd]
    split <;> ring
  rw [main]
  rw [show 2 * (n + 2) - (2 * n) = 4 by omega,
    show 2 * (n + 2) - (2 * n + 1) = 3 by omega,
    show 2 * (n + 2) - (2 * n + 1 + 1) = 2 by omega,
    show 2 * (n + 2) - (2 * n + 1 + 1 + 1) = 1 by omega,
    show 2 * (n + 2) - (2 * n + 1 + 1 + 1 + 1) = 0 by omega,
    show 2 * n - 2 * n = 0 by omega]
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · have d0 : digit (n + 2) (2 * n) := by
      unfold digit
      omega
    have d1 : ¬ digit (n + 2) (2 * n + 1) := by
      unfold digit
      omega
    have d2 : digit (n + 2) (2 * n + 1 + 1) := by
      unfold digit
      omega
    have d3 : digit (n + 2) (2 * n + 1 + 1 + 1) := by
      unfold digit
      omega
    have d4 : digit (n + 2) (2 * n + 1 + 1 + 1 + 1) := by
      unfold digit
      omega
    have e0 : digit n (2 * n) := by
      unfold digit
      omega
    rw [if_pos d0, if_neg d1, if_pos d2, if_pos d3, if_pos d4, if_pos e0]
    unfold corr
    rw [if_pos hn]
    ring
  · have d0 : ¬ digit (n + 2) (2 * n) := by
      unfold digit
      omega
    have d1 : ¬ digit (n + 2) (2 * n + 1) := by
      unfold digit
      omega
    have d2 : digit (n + 2) (2 * n + 1 + 1) := by
      unfold digit
      omega
    have d3 : digit (n + 2) (2 * n + 1 + 1 + 1) := by
      unfold digit
      omega
    have d4 : digit (n + 2) (2 * n + 1 + 1 + 1 + 1) := by
      unfold digit
      omega
    have e0 : digit n (2 * n) := by
      unfold digit
      omega
    rw [if_neg d0, if_neg d1, if_pos d2, if_pos d3, if_pos d4, if_pos e0]
    unfold corr
    rw [if_neg (by omega)]
    ring

theorem corr_period (n : ℕ) : corr (n + 2) = corr n := by
  unfold corr
  simp

theorem rec_four (n : ℕ) : a (n + 4) = 10001 * a (n + 2) - 10000 * a n := by
  have h := append_four (n + 2)
  rw [corr_period] at h
  linarith [append_four n]

theorem start_zero : a 0 = 1 := by decide

theorem start_one : a 1 = 111 := by decide

open PowerSeries

theorem series :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X))
      = 1 + 111 * X + 110 * X ^ 2 - 10000 * X ^ 3 := by
  let F := PowerSeries.mk (fun n => (a n : ℚ))
  change F * _ = _
  have poly : F * ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X))
      = F - (10001 : ℕ) • (F * X ^ 2) + (10000 : ℕ) • (F * X ^ 4) := by
    simp only [nsmul_eq_mul]
    ring
  rw [poly, show (111 : ℚ⟦X⟧) * X = (111 : ℕ) • X by simp [nsmul_eq_mul],
    show (110 : ℚ⟦X⟧) * X ^ 2 = (110 : ℕ) • X ^ 2 by simp [nsmul_eq_mul],
    show (10000 : ℚ⟦X⟧) * X ^ 3 = (10000 : ℕ) • X ^ 3 by simp [nsmul_eq_mul]]
  ext n
  simp only [map_add, map_sub, map_nsmul, coeff_one, coeff_X, coeff_X_pow, coeff_mul_X_pow', F,
    coeff_mk]
  simp only [nsmul_eq_mul]
  have a2 := append_four 0
  have a3 := append_four 1
  rw [start_zero] at a2
  rw [start_one] at a3
  norm_num [corr] at a2 a3
  by_cases h : n < 4
  · interval_cases n <;> norm_num [start_zero, start_one, a2, a3]
  · have hr := rec_four (n - 4)
    rw [show n - 4 + 4 = n by omega, show n - 4 + 2 = n - 2 by omega] at hr
    simp only [if_pos (show 2 ≤ n by omega), if_pos (show 4 ≤ n by omega),
      if_neg (show n ≠ 0 by omega), if_neg (show n ≠ 1 by omega),
      if_neg (show n ≠ 2 by omega), if_neg (show n ≠ 3 by omega), mul_zero, add_zero, sub_zero]
    exact_mod_cast (by linarith [hr] : a n - 10001 * a (n - 2) + 10000 * a (n - 4) = 0)

end Rule214Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a267804.main := by
  refine ⟨?_, Rule214Proof.series⟩
  intro n hn
  have h := Rule214Proof.rec_four (n - 4)
  rw [show n - 4 + 4 = n by omega, show n - 4 + 2 = n - 2 by omega] at h
  exact_mod_cast h

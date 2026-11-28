import OMAStatements.S_oeis_a087547
import Mathlib

namespace OMA.P087547

open OMA.S_oeis_a087547

/-- The integrals I k = ∫_0^1 dx / (1 + x^2)^k. -/
noncomputable def I (k : ℕ) : ℝ := ∫ x : ℝ in (0 : ℝ)..1, 1 / (1 + x ^ 2) ^ k

lemma cont (k : ℕ) : Continuous (fun x : ℝ => 1 / (1 + x ^ 2) ^ k) := by
  refine continuous_const.div (by fun_prop) (fun x => ?_)
  positivity

lemma I_one : I 1 = Real.pi / 4 := by
  unfold I
  simp only [pow_one]
  rw [integral_one_div_one_add_sq, Real.arctan_one, Real.arctan_zero, sub_zero]

/-- Reduction formula. -/
lemma I_succ (k : ℕ) : 2 * ((k : ℝ) + 1) * I (k + 2) = (2 * (k : ℝ) + 1) * I (k + 1) + 1 / 2 ^ (k + 1) := by
  have hd : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun x : ℝ => x / (1 + x ^ 2) ^ (k + 1))
      (2 * ((k : ℝ) + 1) * (1 / (1 + x ^ 2) ^ (k + 2)) - (2 * (k : ℝ) + 1) * (1 / (1 + x ^ 2) ^ (k + 1))) x := by
    intro x _
    have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
    have h1 : HasDerivAt (fun x : ℝ => (1 + x ^ 2) ^ (k + 1))
        (((k + 1 : ℕ) : ℝ) * (1 + x ^ 2) ^ k * (2 * x)) x := by
      have h0 : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * x) x := by
        have := ((hasDerivAt_id x).pow 2).const_add 1
        simpa using this
      have := h0.fun_pow (k + 1)
      simpa using this
    have h2 := (hasDerivAt_id' x).fun_div h1 (by positivity)
    refine h2.congr_deriv ?_
    push_cast
    field_simp
    ring
  have hint : IntervalIntegrable (fun x : ℝ => 2 * ((k : ℝ) + 1) * (1 / (1 + x ^ 2) ^ (k + 2))
      - (2 * (k : ℝ) + 1) * (1 / (1 + x ^ 2) ^ (k + 1))) MeasureTheory.volume 0 1 :=
    ((continuous_const.mul (cont (k + 2))).sub (continuous_const.mul (cont (k + 1)))).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x : ℝ => 2 * ((k : ℝ) + 1) * (1 / (1 + x ^ 2) ^ (k + 2)))
      MeasureTheory.volume 0 1 := (continuous_const.mul (cont (k + 2))).intervalIntegrable _ _
  have i1 : IntervalIntegrable (fun x : ℝ => (2 * (k : ℝ) + 1) * (1 / (1 + x ^ 2) ^ (k + 1)))
      MeasureTheory.volume 0 1 := (continuous_const.mul (cont (k + 1))).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  rw [intervalIntegral.integral_sub i2 i1,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
  unfold I
  have e1 : (1 : ℝ) / (1 + 1 ^ 2) ^ (k + 1) - 0 / (1 + 0 ^ 2) ^ (k + 1) = 1 / 2 ^ (k + 1) := by norm_num
  rw [e1] at h
  linarith

lemma a_eq (n : ℕ) : a n = (n.factorial : ℝ) * 2 ^ (n + 1) * I (n + 1)
    - Real.pi * ((2 * n).factorial : ℝ) / (2 ^ (n + 1) * n.factorial) := rfl

lemma a_zero : a 0 = 0 := by
  rw [a_eq, I_one]
  norm_num
  ring

lemma a_succ (n : ℕ) : a (n + 1) = (n.factorial : ℝ) + (2 * (n : ℝ) + 1) * a n := by
  have hI := I_succ n
  have hP : (2 : ℝ) ^ (n + 1) ≠ 0 := by positivity
  have hF : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn : (2 * ((n : ℝ) + 1)) ≠ 0 := by positivity
  have hI' : I (n + 2) = ((2 * (n : ℝ) + 1) * I (n + 1) + 1 / 2 ^ (n + 1)) / (2 * ((n : ℝ) + 1)) := by
    rw [eq_div_iff hn]
    linarith
  rw [a_eq, a_eq, show n + 1 + 1 = n + 2 from rfl, hI']
  have e1 : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * n.factorial := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have e2 : ((2 * (n + 1)).factorial : ℝ) = (2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 1) * (2 * n).factorial := by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 from by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  rw [e1, e2, pow_succ 2 (n + 1)]
  field_simp
  ring

/-- The auxiliary telescoping terms. -/
noncomputable def U (n i : ℕ) : ℝ := (2 : ℝ) ^ i * i.factorial * (n + 1 + i).factorial / (2 * i).factorial

noncomputable def S (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (2 : ℝ) ^ i * i.factorial * (n + i + 1).factorial / (2 * i + 1).factorial

lemma term (n i : ℕ) :
    (2 : ℝ) ^ i * i.factorial * (n + 1 + i + 1).factorial / (2 * i + 1).factorial
      - (2 * (n : ℝ) + 3) * ((2 : ℝ) ^ i * i.factorial * (n + i + 1).factorial / (2 * i + 1).factorial)
    = U n i - U n (i + 1) := by
  unfold U
  have f1 : ((n + 1 + i + 1).factorial : ℝ) = ((n : ℝ) + i + 2) * (n + i + 1).factorial := by
    rw [show n + 1 + i + 1 = (n + i + 1) + 1 from by ring, Nat.factorial_succ]
    push_cast
    ring
  have f2 : ((2 * i + 1).factorial : ℝ) = (2 * (i : ℝ) + 1) * (2 * i).factorial := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have f3 : ((2 * (i + 1)).factorial : ℝ) = (2 * (i : ℝ) + 2) * (2 * (i : ℝ) + 1) * (2 * i).factorial := by
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 from by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have f4 : ((i + 1).factorial : ℝ) = ((i : ℝ) + 1) * i.factorial := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have f5 : ((n + 1 + (i + 1)).factorial : ℝ) = ((n : ℝ) + i + 2) * (n + i + 1).factorial := by
    rw [show n + 1 + (i + 1) = (n + i + 1) + 1 from by ring, Nat.factorial_succ]
    push_cast
    ring
  have f6 : ((n + 1 + i).factorial : ℝ) = ((n + i + 1).factorial : ℝ) := by
    rw [show n + 1 + i = n + i + 1 from by ring]
  rw [f1, f2, f3, f4, f5, f6, pow_succ]
  have g1 : ((2 * i).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have g2 : (2 * (i : ℝ) + 1) ≠ 0 := by positivity
  have g3 : (2 * (i : ℝ) + 2) ≠ 0 := by positivity
  field_simp
  ring

lemma S_zero : S 0 = 1 := by
  unfold S
  simp

lemma S_succ (n : ℕ) : S (n + 1) = ((n + 1).factorial : ℝ) + (2 * (n : ℝ) + 3) * S n := by
  have hsum : ∑ i ∈ Finset.range (n + 1), (U n i - U n (i + 1)) = U n 0 - U n (n + 1) :=
    Finset.sum_range_sub' _ _
  have hU0 : U n 0 = ((n + 1).factorial : ℝ) := by
    unfold U
    simp
  have hUn : U n (n + 1) = (2 : ℝ) ^ (n + 1) * (n + 1).factorial := by
    unfold U
    have g : ((2 * (n + 1)).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [show n + 1 + (n + 1) = 2 * (n + 1) from by ring]
    field_simp
  have hlast : (2 : ℝ) ^ (n + 1) * (n + 1).factorial * (n + 1 + (n + 1) + 1).factorial
      / (2 * (n + 1) + 1).factorial = (2 : ℝ) ^ (n + 1) * (n + 1).factorial := by
    have g : ((2 * (n + 1) + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [show n + 1 + (n + 1) + 1 = 2 * (n + 1) + 1 from by ring]
    field_simp
  unfold S
  rw [Finset.sum_range_succ, hlast]
  have hterm : ∑ i ∈ Finset.range (n + 1),
        (2 : ℝ) ^ i * i.factorial * (n + 1 + i + 1).factorial / (2 * i + 1).factorial
      = (2 * (n : ℝ) + 3) * ∑ i ∈ Finset.range (n + 1),
        (2 : ℝ) ^ i * i.factorial * (n + i + 1).factorial / (2 * i + 1).factorial
        + (U n 0 - U n (n + 1)) := by
    rw [← hsum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    linarith [term n i]
  rw [hterm, hU0, hUn]
  ring

theorem main' : type_of% @OMA.S_oeis_a087547.main := by
  intro n
  change a (n + 1) = S n
  induction n with
  | zero =>
    rw [a_succ, a_zero, S_zero]
    norm_num
  | succ n ih =>
    rw [a_succ, ih, S_succ]
    push_cast
    ring

end OMA.P087547

theorem OMA.solution : type_of% @OMA.S_oeis_a087547.main := OMA.P087547.main'

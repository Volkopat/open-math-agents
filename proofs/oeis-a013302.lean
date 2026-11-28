import OMAStatements.S_oeis_a013302

/-! The factorial-scaled coefficients of `(1-X)^(-1/2)` are odd double
factorial squares. Multiplication by `1-X/2` then gives a closed form for
the sequence, from which both recurrences follow. -/

namespace OMA.S_oeis_a013302
open PowerSeries

/-- The analytic expression naming A013302 equals its algebraic generating
function throughout the real interval of convergence about zero. -/
lemma generating_function_identity {x : ℝ} (hx : x ∈ Set.Ioo (-1) 1) :
    Real.cosh (Real.log (1+x) - Real.artanh x) =
      (2-x^2) / (2*Real.sqrt (1-x^2)) := by
  have hp : 0 < 1+x := by linarith [hx.1]
  have hm : 0 < 1-x := by linarith [hx.2]
  have hs : 0 < Real.sqrt (1-x^2) := Real.sqrt_pos.mpr (by nlinarith [mul_pos hp hm])
  rw [Real.cosh_sub, Real.cosh_artanh hx, Real.sinh_artanh hx, Real.cosh_eq,
    Real.sinh_eq, Real.exp_neg, Real.exp_log hp]
  field_simp
  ring


private def oddProduct (n : ℕ) : ℚ := Nat.doubleFactorial (2*n-1)

private lemma odd_succ (n : ℕ) : oddProduct (n+1) = (2*n+1) * oddProduct n := by
  rw [oddProduct, show 2*(n+1)-1 = 2*n+1 by omega, Nat.doubleFactorial_add_one]
  simp [oddProduct]

private lemma coeff_step (n : ℕ) :
    2 * ((n : ℚ)+1) * coeff (n+1) invSqrt = (2*n+1) * coeff n invSqrt := by
  have h := Ring.choose_smul_choose (-1/2 : ℚ) (Nat.le_succ n)
  simp [Nat.choose_succ_self_right, nsmul_eq_mul] at h
  simp only [invSqrt, coeff_rescale, binomialSeries_coeff, smul_eq_mul, mul_one, pow_succ]
  linear_combination -2 * (-1 : ℚ)^n * h

private lemma factorial_step (n : ℕ) : ((2*(n+1)).factorial : ℚ) =
    (2*n+2) * (2*n+1) * ((2*n).factorial : ℚ) := by
  rw [show 2*(n+1) = (2*n+1)+1 by omega, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  ring

private lemma weighted (n : ℕ) : ((2*n).factorial : ℚ) * coeff n invSqrt = oddProduct n ^ 2 := by
  induction n with
  | zero => simp [oddProduct, invSqrt]
  | succ n ih =>
    rw [factorial_step, odd_succ, mul_pow, ← ih]
    linear_combination ((2*(n : ℚ)+1) * ((2*n).factorial : ℚ)) * coeff_step n

private lemma a_zero : a 0 = 1 := by
  simp [a, invSqrt]
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp

private lemma a_succ (n : ℕ) : a (n+1) = n*(2*n+1) * oddProduct n ^ 2 := by
  have hX : coeff (n+1) (X * invSqrt) = coeff n invSqrt := by
    simp
  have h : coeff (n+1) ((1 - C (1/2 : ℚ) * X) * invSqrt) =
      coeff (n+1) invSqrt - 1/2 * coeff n invSqrt := by
    rw [sub_mul, one_mul, map_sub, mul_assoc, coeff_C_mul, hX]
  calc
    a (n+1) = ((2*(n+1)).factorial : ℚ) * coeff (n+1) invSqrt
        - ((n : ℚ)+1)*(2*n+1)*(((2*n).factorial : ℚ) * coeff n invSqrt) := by
      rw [a, h, factorial_step]
      ring
    _ = _ := by rw [weighted, weighted, odd_succ]; ring

end OMA.S_oeis_a013302

open OMA.S_oeis_a013302

theorem OMA.solution : type_of% @OMA.S_oeis_a013302.main := by
  constructor
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k+2 := ⟨n-2, by omega⟩
    cases k with
    | zero => norm_num [a_succ, a_zero, oddProduct]
    | succ k =>
      simp only [Nat.add_sub_cancel]
      rw [show k+1+2-1 = k+1+1 by omega]
      change a ((k+1+1)+1) + _ + _ = 0
      rw [a_succ, a_succ, a_succ, odd_succ (k+1), odd_succ k]
      push_cast
      ring
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k+1 := ⟨n-1, by omega⟩
    cases k with
    | zero => norm_num [a_succ, a_zero, oddProduct]
    | succ k =>
      simp only [Nat.add_sub_cancel]
      rw [a_succ, a_succ, show 2*(k+1+1)-3 = 2*k+1 by omega]
      have hd : (Nat.doubleFactorial (2*k+1) : ℚ) = oddProduct (k+1) := by
        unfold oddProduct
        rw [show 2*(k+1)-1 = 2*k+1 by omega]
      rw [hd, odd_succ]
      push_cast
      ring

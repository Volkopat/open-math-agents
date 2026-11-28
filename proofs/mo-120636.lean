import OMAStatements.S_mo_120636

open Polynomial
open scoped BigOperators Polynomial

namespace OMA.BinomialExpectation

private noncomputable def polynomial (n : ℕ) (f : ℕ → ℝ) : ℝ[X] :=
  ∑ j ∈ Finset.range (n + 1), C (f j) * bernsteinPolynomial ℝ n j

private theorem derivative_identity (n : ℕ) (f : ℕ → ℝ) :
    (polynomial n f).derivative = (n : ℝ[X]) *
      polynomial (n - 1) (fun j => f (j + 1) - f j) := by
  cases n with
  | zero => simp [polynomial, bernsteinPolynomial]
  | succ n =>
      let B := bernsteinPolynomial ℝ n
      let c := ((n + 1 : ℕ) : ℝ[X])
      have last : B (n + 1) = 0 := bernsteinPolynomial.eq_zero_of_lt ℝ (Nat.lt_succ_self n)
      have shift :
          (∑ j ∈ Finset.range (n + 1), C (f (j + 1)) * B (j + 1)) + C (f 0) * B 0 =
            ∑ j ∈ Finset.range (n + 1), C (f j) * B j := by
        rw [← Finset.sum_range_succ' (fun j => C (f j) * B j) (n + 1),
          Finset.sum_range_succ (fun j => C (f j) * B j) (n + 1), last, mul_zero, add_zero]
      have split (j : ℕ) :
          C (f (j + 1)) * (c * (B j - B (j + 1))) =
            c * (C (f (j + 1)) * B j) - c * (C (f (j + 1)) * B (j + 1)) := by
        ring
      calc
        _ = (∑ j ∈ Finset.range (n + 1), C (f (j + 1)) * (c * (B j - B (j + 1)))) +
              C (f 0) * (-c * B 0) := by
          unfold polynomial
          rw [Polynomial.derivative_sum,
            Finset.sum_range_succ' (fun j => derivative (C (f j) * bernsteinPolynomial ℝ (n + 1) j))]
          simp only [Polynomial.derivative_C_mul, bernsteinPolynomial.derivative_succ,
            bernsteinPolynomial.derivative_zero, Nat.succ_sub_one]
          rfl
        _ = c * ((∑ j ∈ Finset.range (n + 1), C (f (j + 1)) * B j) -
              ((∑ j ∈ Finset.range (n + 1), C (f (j + 1)) * B (j + 1)) + C (f 0) * B 0)) := by
          simp only [split, Finset.sum_sub_distrib, ← Finset.mul_sum]
          ring
        _ = _ := by
          rw [shift, ← Finset.sum_sub_distrib]
          change c * (∑ j ∈ Finset.range (n + 1), (C (f (j + 1)) * B j - C (f j) * B j)) =
            c * (∑ j ∈ Finset.range (n + 1), C (f (j + 1) - f j) * B j)
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          rw [map_sub, sub_mul]

private theorem hasDeriv (f : ℕ → ℝ) (n : ℕ) (p : ℝ) :
    HasDerivAt (fun t => ∑ j ∈ Finset.range (n + 1), f j * (bernsteinPolynomial ℝ n j).eval t)
      ((n : ℝ) * ∑ j ∈ Finset.range (n - 1 + 1),
        (f (j + 1) - f j) * (bernsteinPolynomial ℝ (n - 1) j).eval p) p := by
  have h := (polynomial n f).hasDerivAt p
  rw [derivative_identity] at h
  simpa only [polynomial, Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_C,
    Polynomial.eval_finsetSum] using h

end OMA.BinomialExpectation

theorem OMA.solution : type_of% @OMA.S_mo_120636.main := by
  dsimp only
  constructor
  · exact OMA.BinomialExpectation.hasDeriv
  · refine ⟨fun x => max 1 (x + 1), 1, ?_, ?_, ?_⟩
    · intro x
      exact zero_lt_one.trans_le (le_max_left 1 (x + 1))
    · have h₁ : ConvexOn ℝ Set.univ (fun _ : ℝ => (1 : ℝ)) :=
        convexOn_const _ convex_univ
      have h₂ : ConvexOn ℝ Set.univ (fun x : ℝ => x + 1) :=
        (convexOn_id convex_univ).add_const 1
      exact h₁.sup h₂
    · intro p _
      norm_num [Finset.sum_range_succ, bernsteinPolynomial]
      ring
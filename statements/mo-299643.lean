import Mathlib

/-!
# Least eigenvalues of normalized monomial Gram matrices

Source: user39756, https://mathoverflow.net/questions/299643 (CC BY-SA 4.0).
Credit: @connoranderson.

For the lognormal law of exp(G), with G centered Gaussian of variance four,
every normalized monomial Gram matrix has all eigenvalues at least 1/3.
This probability has a density and moments of all orders. Thus the
least eigenvalues need not tend to zero over the class in the question.
For the two specific densities in the question, Chebyshev and Hermite
polynomials give exponential upper bounds with explicit factors.

For an arbitrary positive definite correlation matrix A of size p, each
positive integer k gives a determinant-free lower bound
p(1 − tr((I − A/p)^k))/k on every eigenvalue. At least one such k gives
a strictly positive bound. The expression uses only the matrix entries,
finite sums and products, and divisions by integers.
-/
namespace OMA.S_mo_299643
open MeasureTheory ProbabilityTheory Matrix Finset Set
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
noncomputable def moment (μ : Measure ℝ) (k : ℕ) : ℝ := ∫ x, x^k ∂μ
noncomputable def gram (μ : Measure ℝ) (n : ℕ) : Mat n := fun i j =>
  moment μ (i.val+j.val) / (Real.sqrt (moment μ (2*i.val))*Real.sqrt (moment μ (2*j.val)))
noncomputable def lognormal : Measure ℝ := (gaussianReal 0 4).map Real.exp
noncomputable def traceBound {n : ℕ} (A : Mat n) (k : ℕ) : ℝ :=
  (n:ℝ)*(1-((1-(n:ℝ)⁻¹ • A)^k).trace)/k

noncomputable def eigenvalue (μ : Measure ℝ) (n : ℕ) (i : Fin n) : ℝ :=
  (show (gram μ n).IsHermitian by
    ext i j
    simp [gram,Matrix.conjTranspose_apply,add_comm,mul_comm]).eigenvalues i
noncomputable def symmetricUniform : Measure ℝ :=
  (2:ENNReal)⁻¹ • volume.restrict (Set.Ioc (-1:ℝ) 1)
theorem main :
    (IsProbabilityMeasure lognormal ∧ lognormal ≪ volume ∧
      (∀ k : ℕ, Integrable (fun x : ℝ => x^k) lognormal) ∧
      (∀ n (i j : Fin n), gram lognormal n i j=Real.exp (-2*((i.val:ℝ)-j.val)^2)) ∧
      ∀ n (i : Fin n), 1/3≤eigenvalue lognormal n i) ∧
    (∀ n : ℕ, ∃ i : Fin (n+1), eigenvalue symmetricUniform (n+1) i≤(2*(n:ℝ)+1)/4^(n-1)) ∧
    (∀ n : ℕ, ∃ i : Fin (n+1), eigenvalue (gaussianReal 0 1) (n+1) i≤((n:ℝ)+1)/2^n) ∧
    (∀ n : ℕ, 0<n → ∀ (A : Mat n) (hA : A.PosDef), (∀ i,A i i=1) →
      (∀ k : ℕ, 0<k → ∀ i, traceBound A k≤hA.1.eigenvalues i) ∧
        ∃ k : ℕ, 0<k ∧ 0<traceBound A k) := by
  sorry
end OMA.S_mo_299643

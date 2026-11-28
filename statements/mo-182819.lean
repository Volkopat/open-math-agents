import Mathlib

/-!
# Reciprocal polynomials with roots off the unit circle

Source: Igor Rivin, https://mathoverflow.net/questions/182819 (CC BY-SA 3.0).
Credit: @connoranderson.

Robert Israel proposes the following monic reciprocal trinomial in the source
comments. In every positive even degree it gives a uniform coefficient bound
of three, attained at the middle coefficient.
-/

namespace OMA.S_mo_182819

open Polynomial

noncomputable def family (R : Type) [Semiring R] (n : ℕ) : R[X] :=
  X^(2*n) + 3*X^n + 1

theorem main : ∀ n : ℕ, 0 < n →
    (family ℤ n).natDegree = 2*n ∧ (family ℤ n).coeff n = 3 ∧
    (∀ j ≤ 2*n, (family ℤ n).coeff j = (family ℤ n).coeff (2*n-j)) ∧
    (∀ j, |(family ℤ n).coeff j| ≤ 3) ∧ Irreducible (family ℚ n) ∧
    ∀ z : ℂ, ‖z‖ = 1 → (family ℂ n).eval z ≠ 0 := by
  sorry

end OMA.S_mo_182819

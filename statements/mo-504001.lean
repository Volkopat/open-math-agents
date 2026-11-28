import Mathlib

/-!
# Lower bounds for difference sets of finite integer sets

Source: NumDio, https://mathoverflow.net/questions/504001
Credit: @connoranderson

The cutoff is fixed while the cardinality of the finite set tends to infinity,
as in the question. Thus both the density constant and the threshold may depend
on the cutoff. The set of bounded primes is unchanged by taking its integer part.
-/

namespace OMA.S_mo_504001

open scoped Pointwise

theorem main : ∀ X : ℕ, ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ S : Finset ℤ, N ≤ S.card →
    ∃ A : Finset ℤ, A ⊆ S - S ∧
      (∀ a ∈ A, ∀ p : ℕ, p.Prime → p ≤ X → (p : ℤ) ∣ a) ∧
      c * ((S - S).card : ℝ) ≤ (A.card : ℝ) := by
  sorry

end OMA.S_mo_504001

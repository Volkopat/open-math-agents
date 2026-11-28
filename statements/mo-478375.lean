import Mathlib

/-!
# The symmetric quantum binomial coefficient at an odd-order root of unity

Chari and Pressley, *A Guide to Quantum Groups*, Lemma 9.3.6, as quoted at
https://mathoverflow.net/questions/478375 . The quantum binomial coefficient is
specialized as a Laurent polynomial. We use its finite generating product, whose
coefficient of X^s is q^((r-s)(r-1)) times the symmetric quantum binomial.
This implements the interpretation given by Fedor Petrov and Sam Hopkins in
the source discussion and also gives zero for s > r.

Credit: @connoranderson
-/

namespace OMA.S_mo_478375

open Polynomial

noncomputable def generating (q : ℂ) (r : ℕ) : ℂ[X] :=
  ∏ j ∈ Finset.range r, (X + C ((q^2)^j))

noncomputable def quantumBinom (q : ℂ) (r s : ℕ) : ℂ :=
  q ^ (((s : ℤ) - r) * ((r : ℤ) - 1)) * (generating q r).coeff s

theorem main : ∀ l : ℕ, 1 < l → Odd l → ∀ q : ℂ, IsPrimitiveRoot q l →
    ∀ r s : ℕ, s ≤ r → quantumBinom q r s =
      quantumBinom q (r % l) (s % l) * (Nat.choose (r / l) (s / l) : ℂ) := by
  sorry

end OMA.S_mo_478375

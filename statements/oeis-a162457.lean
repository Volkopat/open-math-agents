import Mathlib

/-!
# A162457: infinitely many prime-factor triangles

Source: https://oeis.org/A162457
Credit: @etaubman

A row with index i, counted from zero, contains an (i+1)-digit prime.
Taking the product specifies the entire prime factorization with multiplicity.
The digit intervals are disjoint and increasing, so sorting gives exactly the
rows in the OEIS definition.
-/

namespace OMA.S_oeis_a162457

def factorTriangles : Set ℕ :=
  {k | ∃ h : ℕ, 0 < h ∧ ∃ p : ℕ → ℕ,
    (∀ i < h, (p i).Prime ∧ 10 ^ i ≤ p i ∧ p i < 10 ^ (i + 1)) ∧
    k = ∏ i ∈ Finset.range h, p i}

theorem main : factorTriangles.Infinite := by
  sorry

end OMA.S_oeis_a162457

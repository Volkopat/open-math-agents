import Mathlib

/-!
# A241844: Number of ordered ways to write n = k + m with k > 0 and m > 0 such that L(k) + m is prime, where L(k) is the k-th Lucas number.

Source: https://oeis.org/A241844
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A241844 (Zhi-Wei Sun, Apr 29 2014), first sentence of part (i): a(n) > 0 for all n > 1.

Conventions:
* The sequence has offset 1 (data 0, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 3, ...). `a n` is the number
  of natural numbers k with 0 < k < n (so that m = n - k > 0) such that L(k) + (n - k) is
  prime.
* L(k) is the Lucas number with L(0) = 2, L(1) = 1, L(k+2) = L(k) + L(k+1) (A000032), as in
  the examples of the entry (L(1) = 1, L(4) = 7, L(7) = 29).
* Only the first sentence of part (i) is formalized; the refinement with k > 1 for n > 5 and
  part (ii) are separate claims.
-/

namespace OMA.S_oeis_a241844

/-- The Lucas numbers: L(0) = 2, L(1) = 1, L(k+2) = L(k) + L(k+1). -/
def L : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | (k + 2) => L k + L (k + 1)

/-- A241844: number of k with 0 < k < n and L(k) + (n - k) prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {k : ℕ | 0 < k ∧ k < n ∧ (L k + (n - k)).Prime}

/-- The conjecture of Sun: a(n) > 0 for all n > 1. -/
theorem main : ∀ n : ℕ, 1 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a241844

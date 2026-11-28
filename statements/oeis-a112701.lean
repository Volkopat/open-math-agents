import Mathlib

/-!
# A112701: Partial sum of Catalan numbers (A000108) multiplied by powers of 7.

Source: https://oeis.org/A112701
Credit: @OrangeHeadz

The sequence (offset 0) is `a(n) = Sum_{k=0..n} C(k) * 7^k`, where `C(k)` is the `k`-th Catalan
number (A000108); it starts 1, 8, 106, 1821, 35435.

Conjecture (R. J. Mathar, Jun 08 2016, formula section of the entry):
`(n+1)*a(n) + (-29*n+13)*a(n-1) + 14*(2*n-1)*a(n-2) = 0`.

The same entry records the conjecture as verified (Robert Israel, Aug 04 2020, from the
differential equation satisfied by the generating function), so this is a settled claim rather
than an open problem.

Conventions:
* `a` is defined by the sum formula given in the entry, with `catalan` from Mathlib.
* The recurrence mentions `a(n-2)`, so it is stated for every `n ≥ 2` (all indices in range for
  offset 0); the source gives no further restriction.
* The coefficient `-29*n+13` is negative, so the identity is stated over the integers.
-/

namespace OMA.S_oeis_a112701

/-- `a(n) = Sum_{k=0..n} C(k) * 7^k`, with `C(k)` the Catalan numbers. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), catalan k * 7 ^ k

/-- Mathar's recurrence for A112701. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    ((n : ℤ) + 1) * (a n : ℤ) + (-29 * (n : ℤ) + 13) * (a (n - 1) : ℤ) +
      14 * (2 * (n : ℤ) - 1) * (a (n - 2) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a112701

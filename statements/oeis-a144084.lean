import Mathlib

/-!
# A144084: a Stirling-number formula for the number of partial bijections of height k

Source: https://oeis.org/A144084
Credit: @ivillar

Status: known result: the entry records that the conjecture is true.

A144084 (offset 0): T(n,k) is the number of partial bijections of height k of an n-element set;
the entry gives T(n,k) = (C(n,k)^2)*k!; rows 1; 1, 1; 1, 4, 2; 1, 9, 18, 6; 1, 16, 72, 96, 24; ...

Conjecture (Mikhail Kurkov, Jun 23 2026):
T(n, k) = Sum_{j=0..k} |Stirling1(n, n-j)| * Stirling2(n-j+1, n-k+1).
The entry records that the conjecture is true.

Formalization: T(n,k) is defined by the entry's formula k! * C(n,k)^2. `Nat.stirlingFirst` and
`Nat.stirlingSecond` are Mathlib's unsigned Stirling numbers of the first kind and Stirling
numbers of the second kind. The identity is stated for 0 ≤ k ≤ n, where all the subtractions in
the indices are exact.
-/

namespace OMA.S_oeis_a144084

/-- T(n,k) = k! * C(n,k)^2, the number of partial bijections of height k of an n-set. -/
def T (n k : ℕ) : ℕ := k.factorial * n.choose k ^ 2

/-- Kurkov's formula. -/
theorem main : ∀ n k : ℕ, k ≤ n →
    T n k = ∑ j ∈ Finset.range (k + 1),
      Nat.stirlingFirst n (n - j) * Nat.stirlingSecond (n - j + 1) (n - k + 1) := by
  sorry

end OMA.S_oeis_a144084

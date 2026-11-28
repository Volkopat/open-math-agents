import Mathlib

/-!
# A073591: a(n) = A000522(n) + 1.

Source: https://oeis.org/A073591 (OEIS Foundation, CC BY-SA 4.0)
Credit: @OrangeHeadz

The OEIS entry has offset 0 and begins 2, 3, 6, 17, 66, 327, 1958, 13701, ... Here A000522 is
the sequence `Sum_{k=0..n} n!/k!` (offset 0; 1, 2, 5, 16, 65, 326, ...), the total number of
arrangements of a set with `n` elements. The formula section of A073591 contains the conjecture
of R. J. Mathar (Feb 16 2014):

  a(n) + (-n-2)*a(n-1) + (2*n-1)*a(n-2) + (-n+2)*a(n-3) = 0.

Conventions.
* `n! / k!` is an exact division for `k ≤ n`.
* The recurrence is stated for every `n ≥ 3`, the indices for which `a(n-1)`, `a(n-2)` and
  `a(n-3)` are terms of the sequence, and as an equation in the integers.
-/

namespace OMA.S_oeis_a073591

/-- A000522: `Sum_{k=0..n} n!/k!`. -/
def A000522 (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), n.factorial / k.factorial

/-- A073591: `a n = A000522 n + 1`. -/
def a (n : ℕ) : ℤ := (A000522 n : ℤ) + 1

/-- Mathar's four-term recurrence for A073591. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    a n + (-(n : ℤ) - 2) * a (n - 1) + (2 * (n : ℤ) - 1) * a (n - 2) +
      (-(n : ℤ) + 2) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a073591

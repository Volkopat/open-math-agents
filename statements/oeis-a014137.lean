import Mathlib

/-!
# A014137: Mathar's recurrence for the partial sums of the Catalan numbers

Source: https://oeis.org/A014137
Credit: @ivillar

Status: known result (Peter J. Taylor, Mar 23 2015, cited below, shows the conjecture is true).

A014137 (offset 0) is a(n) = Sum_{k=0..n} C(k), the partial sums of the Catalan numbers
A000108, with data 1, 2, 4, 9, 23, 65, 197, ...
R. J. Mathar (Dec 14 2011) gave the recurrence
(n+1)*a(n) + (1-5*n)*a(n-1) + 2*(2*n-1)*a(n-2) = 0;
Peter J. Taylor (Mar 23 2015) notes that it reduces to 2*(2*n-1)*C(n-1) = (n+1)*C(n), a known
recurrence of the Catalan numbers, so the conjecture is true.

Formalization: `catalan k` is Mathlib's k-th Catalan number (A000108). The recurrence is stated
in ℤ for every n ≥ 2, i.e. wherever all three terms exist.
-/

namespace OMA.S_oeis_a014137

/-- A014137: a(n) = Sum_{k=0..n} C(k). -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), (catalan k : ℤ)

/-- Mathar's recurrence, for every n ≥ 2. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    ((n : ℤ) + 1) * a n + (1 - 5 * (n : ℤ)) * a (n - 1) + 2 * (2 * (n : ℤ) - 1) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a014137

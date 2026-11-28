import Mathlib

/-!
# A008544: Triple factorial numbers: Product_{k=0..n-1} (3*k+2).

Source: https://oeis.org/A008544
Credit: @ShoQo

The Mathar conjecture (as stated and resolved in the entry by Bill McEachen, Jan 01 2016):
a(n) + (1-3n)*a(n-1) + a(n-2) + (7-3n)*a(n-3) = 0.

Formalization notes:
* Offset 0: `a n = ∏_{k=0}^{n-1} (3k+2)`, with `a 0 = 1` (empty product).
* The recurrence involves a(n-3), so it is stated for `n ≥ 3`, with integer coefficients.
-/

namespace OMA.S_oeis_a008544

/-- a(n) = Product_{k=0..n-1} (3k+2). -/
def a (n : ℕ) : ℤ := ∏ k ∈ Finset.range n, (3 * (k : ℤ) + 2)

theorem main :
    ∀ n : ℕ, 3 ≤ n →
      a n + (1 - 3 * (n : ℤ)) * a (n - 1) + a (n - 2) + (7 - 3 * (n : ℤ)) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a008544

import Mathlib

/-!
# A024451: numerator of the sum of reciprocals of the first n primes

Source: https://oeis.org/A024451
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A024/A024451.seq
Credit: @Bondyboy2001

`a(n)` is the numerator of `∑_{i=1}^n 1/prime(i)`. Nicolas Bělohoubek conjectured in the OEIS
entry that all terms are squarefree.

Formalization notes:
* `Nat.nth Nat.Prime i` is the `(i+1)`-st prime, so the sum over `Finset.range n` is exactly
  the sum in the title.
* The reduced numerator is positive for positive `n`, so `Rat.num.natAbs` is the natural-number
  numerator appearing in the OEIS data.
* The offset is `0` and `a(0) = 0`; the conjecture is stated for positive `n`, since `0` is not
  squarefree in the standard sense.
-/

namespace OMA.S_oeis_a024451

/-- The numerator of the sum of reciprocals of the first `n` primes. -/
noncomputable def a (n : ℕ) : ℕ :=
  (∑ i ∈ Finset.range n, (1 : ℚ) / (Nat.nth Nat.Prime i : ℚ)).num.natAbs

theorem main : ∀ n : ℕ, 1 ≤ n → Squarefree (a n) := by
  sorry

end OMA.S_oeis_a024451

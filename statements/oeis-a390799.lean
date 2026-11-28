import Mathlib

/-!
# OEIS A390799: representations with prime and practical-number restrictions

Source: https://oeis.org/A390799, conjecture of Zhi-Wei Sun.
Credit: @gblacher2
-/

namespace OMA.S_oeis_a390799

/-- Sums of subsets of the positive divisors of `m`. -/
def divisorSums (m : ℕ) : Finset ℕ :=
  m.divisors.powerset.image (fun divisors => divisors.sum id)

/-- Count the representations using `x = (p - 1) / 2` and `y = (q - 1) / 2`.
The source's example at 74 permits `v = 0`, and requires `u > 0`. -/
def a (n : ℕ) : ℕ :=
  let roots := Finset.range (n.sqrt + 1)
  let primeRoots := roots.filter (fun k => k = 0 ∨ (2 * k + 1).Prime)
  let practicalRoots := roots.filter (fun k => k = 0 ∨ Finset.Icc 1 (2 * k) ⊆ divisorSums (2 * k))
  let candidates := (primeRoots ×ˢ primeRoots) ×ˢ (practicalRoots.erase 0 ×ˢ practicalRoots)
  (candidates.filter (fun ((x, y), (u, v)) => x ^ 4 + 2 * y ^ 2 + u ^ 2 + 3 * v ^ 2 = n)).card

theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a390799

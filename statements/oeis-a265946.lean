import Mathlib

/-!
# A265946: Sums of positive differences and negated sums of negative differences in the
# Collatz trajectory of n

Source: https://oeis.org/A265946 (conjecture in the comments of the entry)

Entry (offset 1): for each n, consider the Collatz trajectory x(1) = n, x(2), ..., x(r) = 1 and
the differences d(i) = x(i+1) - x(i); a(2n-1) is the sum of the positive differences and a(2n)
is the negated sum of the negative differences.
Conjecture: a(2n) - a(2n-1) = n - 1.

Conventions:
* `collatz x` is the 3x+1 map: x/2 for even x and 3x+1 for odd x (the trajectory of 3 is
  3, 10, 5, 16, 8, 4, 2, 1 as in the example of the entry).
* The trajectory of n stops at the first iterate equal to 1; the entry only defines a(2n-1) and
  a(2n) when this happens (the trajectory is required to end with x(r) = 1), so the statement
  assumes that some iterate of n equals 1, and `stop n` is the least t with collatz^[t] n = 1.
* `a m` is defined on all m >= 1: for odd m = 2n-1 it is the sum of the positive differences
  along the trajectory of n, for even m = 2n the negated sum of the negative ones; the
  differences are taken in the integers.
-/

namespace OMA.S_oeis_a265946

/-- The Collatz (3x+1) map. -/
def collatz (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else 3 * x + 1

/-- The first time the trajectory of n reaches 1 (meaningful when it does). -/
noncomputable def stop (n : ℕ) : ℕ := sInf {t : ℕ | collatz^[t] n = 1}

/-- The i-th difference x(i+1) - x(i) of the trajectory of n (0-indexed). -/
def diff (n i : ℕ) : ℤ := (collatz^[i + 1] n : ℤ) - (collatz^[i] n : ℤ)

/-- A265946(m). -/
noncomputable def a (m : ℕ) : ℤ :=
  if m % 2 = 1 then ∑ i ∈ Finset.range (stop ((m + 1) / 2)), max (diff ((m + 1) / 2) i) 0
  else -∑ i ∈ Finset.range (stop (m / 2)), min (diff (m / 2) i) 0

theorem main : ∀ n : ℕ, 1 ≤ n → (∃ t, collatz^[t] n = 1) →
    a (2 * n) - a (2 * n - 1) = (n : ℤ) - 1 := by
  sorry

end OMA.S_oeis_a265946

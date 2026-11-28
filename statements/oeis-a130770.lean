import Mathlib

/-!
# A130770: One third of the least common multiple of 3 and n^2+n+1.

Source: https://oeis.org/A130770
Credit: @marcelopierry

Conjecture (R. J. Mathar, Jun 13 2008, in the formulas of A130770): a(n) = A046163(n), n > 0.

Conventions:
* The sequence has offset 0: a(n) = lcm(3, n^2 + n + 1) / 3, an exact division, giving the data
  1, 1, 7, 13, 7, 31, 43, 19, 73, ...
* A046163(n) (offset 1) is the reduced denominator of (n-1)^2/(n^2 + n + 1), i.e. `Rat.den` of
  that rational number (data 1, 7, 13, 7, 31, 43, ...).
-/

namespace OMA.S_oeis_a130770

/-- A130770(n) = lcm(3, n^2 + n + 1) / 3. -/
def a (n : ℕ) : ℕ := Nat.lcm 3 (n ^ 2 + n + 1) / 3

/-- A046163(n): the reduced denominator of (n-1)^2/(n^2+n+1). -/
def A046163 (n : ℕ) : ℕ := ((((n : ℚ) - 1) ^ 2) / ((n : ℚ) ^ 2 + n + 1)).den

/-- Mathar's conjecture: A130770(n) = A046163(n) for n > 0. -/
theorem main : ∀ n : ℕ, 0 < n → a n = A046163 n := by
  sorry

end OMA.S_oeis_a130770

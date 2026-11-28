import Mathlib

/-!
# A112388: a(n) is the smallest prime p such that p^n contains every digit.

Source: https://oeis.org/A112388
Credit: @darealpandaboi

Conjecture (Robert Israel, Aug 28 2020): a(n) = 2 for all n > 168 (checked up to n = 20000).

Translation notes.
* Contains every digit means each of 0, 1, ..., 9 occurs among the decimal digits.
* 2 is the smallest prime, so a(n) = 2 holds exactly when 2^n contains every digit;
  the statement is phrased that way, which avoids defining the minimum.
* Checked by computer: among n < 3000 the largest n for which 2^n misses a digit is 168.
-/

namespace OMA.S_oeis_a112388

/-- The decimal expansion of m contains every digit 0, ..., 9. -/
def ContainsEveryDigit (m : ℕ) : Prop := ∀ d : ℕ, d < 10 → d ∈ Nat.digits 10 m

theorem main : ∀ n : ℕ, 168 < n → ContainsEveryDigit (2 ^ n) := by
  sorry

end OMA.S_oeis_a112388

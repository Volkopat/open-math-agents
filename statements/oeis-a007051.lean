import Mathlib

/-!
# A007051: a(n) = (3^n + 1)/2.

Source: https://oeis.org/A007051
Credit: @ShoQo

It appears that if s(n) is a rational sequence of the form s(1)=2,
s(n)= (2*s(n-1)+1)/(s(n-1)+2), n>1 then s(n)=a(n)/(a(n)-1). - Gary Detlefs, Nov 16 2010
(Sela Fried, 2025: the corrected conjecture is true.)

Formalization notes:
* Offset 0: `a n = (3^n + 1)/2`, exact natural-number division (3^n + 1 is even).
* The sequence `s` is any rational sequence satisfying the recurrence for `n > 1` (its value
  at 0 plays no role); the claim is stated for `n ≥ 1`.
-/

namespace OMA.S_oeis_a007051

/-- a(n) = (3^n + 1)/2. -/
def a (n : ℕ) : ℕ := (3 ^ n + 1) / 2

theorem main :
    ∀ s : ℕ → ℚ, s 1 = 2 → (∀ n : ℕ, 1 < n → s n = (2 * s (n - 1) + 1) / (s (n - 1) + 2)) →
      ∀ n : ℕ, 1 ≤ n → s n = (a n : ℚ) / ((a n : ℚ) - 1) := by
  sorry

end OMA.S_oeis_a007051

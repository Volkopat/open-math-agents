import Mathlib

/-!
# A156849: Numbers k such that k^2 == 2 (mod 23^2).

Source: https://oeis.org/A156849
Credit: @ShoQo

Conjecture (R. J. Mathar, Oct 18 2010): a(n) = a(n-1) + a(n-2) - a(n-3)
= 529*n/2 - 529/4 - 95*(-1)^n/4. (Charles R Greathouse IV, Dec 27 2011: "The conjecture is
correct.")

Formalization notes:
* Offset 1: a(n) is the n-th natural number k (in increasing order) with k^2 ≡ 2 (mod 529),
  i.e. `Nat.nth _ (n - 1)` (`Nat.nth` is 0-indexed). Data: 156, 373, 685, 902, ...
* Both parts of the conjecture are stated: the recurrence for `n ≥ 4` (so that a(n-3) is a
  term) and the closed form for `n ≥ 1`, in `ℚ`.
-/

namespace OMA.S_oeis_a156849

/-- a(n): the n-th number k with k^2 ≡ 2 (mod 23^2), for n ≥ 1. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun k => k ^ 2 % 23 ^ 2 = 2) (n - 1)

theorem main :
    (∀ n : ℕ, 4 ≤ n → (a n : ℚ) = a (n - 1) + a (n - 2) - a (n - 3)) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 529 * n / 2 - 529 / 4 - 95 * (-1) ^ n / 4) := by
  sorry

end OMA.S_oeis_a156849

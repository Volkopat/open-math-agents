import Mathlib

/-!
# A329931: Reversal of base-n digits of largest prime < n^3.

Source: https://oeis.org/A329931
Credit: @eltociear

Let `P(n)` be the largest prime `< n^3` (`prevprime(n^3)`). `a(n)` (offset 2) is the number
whose base-`n` digits are those of `P(n)` in reverse order (`a(2) = 7`, `a(3) = 23`, `a(4) = 31`).
The entry conjectures:

  a(n) < prevprime(n^3) for n >= 4.

`P(n)` is written `Nat.findGreatest Nat.Prime (n ^ 3 - 1)`, the largest `p ≤ n^3 - 1` that is
prime (there is one for `n ≥ 2`, e.g. `2`). `Nat.digits n m` lists the base-`n` digits of `m`
least significant first, so `Nat.ofDigits n (Nat.digits n m).reverse` is the digit reversal.
-/

namespace OMA.S_oeis_a329931

open Classical in
/-- `prevprime(n^3)`: the largest prime `p < n ^ 3`. -/
noncomputable def P (n : ℕ) : ℕ := Nat.findGreatest Nat.Prime (n ^ 3 - 1)

/-- OEIS A329931: the reversal of the base-`n` digits of `P n`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.ofDigits n (Nat.digits n (P n)).reverse

/-- The conjecture in OEIS A329931: `a(n) < prevprime(n^3)` for `n ≥ 4`. -/
theorem main : ∀ n : ℕ, 4 ≤ n → a n < P n := by
  sorry

end OMA.S_oeis_a329931
-- ci: re-run check-proof

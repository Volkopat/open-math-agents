import Mathlib

/-!
# A113604: first prime reached by iterating `n ↦ n +` (sum of decimal digits of `n`).

Source: https://oeis.org/A113604
Credit: @cjchaffin

The sequence name on the OEIS page writes `f(k) = k +` sum of digits of `n`. The example
and the PARI program both take `f(k) = k +` (sum of decimal digits of `k`):
`f(4) = 4+4 = 8`, `f(8) = 8+8 = 16`, `f(16) = 16+1+6 = 23`, so `a(4) = 23`.
`a(n)` is the first prime among `n, f(n), f(f(n)), …` (zero or more applications of `f`),
or `0` if no such prime exists.

Conjecture (stated on the OEIS page): `a(n) = 0` only if `n ≡ 0 (mod 3)`.

Conventions:
- The sequence has offset 1, so `n` runs over the positive integers.
- `a(n) = 0` means that no iterate `f^[k] n` (`k ≥ 0`) is prime. The conjecture is the
  implication: if that happens, then `3 ∣ n`. (The page already records the converse
  for `n > 3`: if `n > 3` and `3 ∣ n`, then `a(n) = 0`.)
-/

namespace OMA.S_oeis_a113604

/-- `f k = k +` the sum of the decimal digits of `k`. -/
def f (k : ℕ) : ℕ := k + (Nat.digits 10 k).sum

/-- `a n = 0` if and only if no iterate of `f` starting at `n` is prime. -/
def vanishes (n : ℕ) : Prop := ∀ k : ℕ, ¬ (f^[k] n).Prime

theorem main : ∀ n : ℕ, 1 ≤ n → vanishes n → 3 ∣ n := by
  sorry

end OMA.S_oeis_a113604

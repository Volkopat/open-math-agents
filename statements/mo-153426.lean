import Mathlib

/-!
# Floors of rationals to powers: infinitely many primes?

Source: https://mathoverflow.net/questions/153426/floors-of-rationals-to-powers-infinite-number-of-primes
Credit: @shc261392

Question. Let `r = a / b` be a rational number in lowest terms, larger than `1`, and not an
integer (so `b > 1`). Does the sequence `⌊r⌋, ⌊r^2⌋, ⌊r^3⌋, …` always contain an infinite number
of primes?

Reading used here (the affirmative answer): for all natural numbers `a, b` with `b > 1`,
`gcd(a, b) = 1` and `a > b`, the set of `n` with `⌊(a / b)^n⌋` prime is infinite.
-/

namespace OMA.S_mo_153426

theorem main :
    ∀ a b : ℕ, 1 < b → Nat.Coprime a b → b < a →
      {n : ℕ | (⌊((a : ℚ) / b) ^ n⌋₊).Prime}.Infinite := by
  sorry

end OMA.S_mo_153426

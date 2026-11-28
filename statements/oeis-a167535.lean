import Mathlib

/-!
# A167535: Primes which are the concatenation of two squares (in decimal notation).

Source: https://oeis.org/A167535
Credit: @keiichisince1986-bot

A167535 is the sequence `a(n)` named in the title. The entry states:
The Bunyakovsky conjecture implies that for every b coprime to 10, there are infinitely many terms
where the second square is b^2. - Robert Israel, Jun 17 2021 (The statement below is this claim,
unconditionally.)

Conventions:
- The decimal concatenation of `a^2` (with `a > 0`) followed by `b^2` is `a^2 · 10^L + b^2`, where `L` is the
  number of decimal digits of `b^2` (`b` coprime to `10` gives `b ≥ 1`, so `b^2` has no leading zero).
-/

namespace OMA.S_oeis_a167535

theorem main :
    ∀ b : ℕ, Nat.Coprime b 10 →
      {p : ℕ | p.Prime ∧ ∃ a : ℕ, 0 < a ∧ p = a ^ 2 * 10 ^ (Nat.digits 10 (b ^ 2)).length + b ^ 2}.Infinite := by
  sorry

end OMA.S_oeis_a167535

import Mathlib

/-!
# A014442: Largest prime factor of n² + 1

Source: https://oeis.org/A014442
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

All terms except `a(1) = 2` are Pythagorean primes (primes `≡ 1 mod 4`). Conjecture (OEIS):
every Pythagorean prime appears as a term at least once, i.e. every prime `p ≡ 1 (mod 4)` is the
largest prime factor of `n² + 1` for some `n ≥ 1`.

## Encoding

* "`p` is the largest prime factor of `m`": `p ∣ m` and every prime factor of `m` is `≤ p`
  (with `Nat.primeFactors`).
-/

namespace OMA.S_oeis_a014442

theorem main :
    ∀ p : ℕ, p.Prime → p % 4 = 1 →
      ∃ n : ℕ, 1 ≤ n ∧ p ∣ n ^ 2 + 1 ∧ ∀ q ∈ (n ^ 2 + 1).primeFactors, q ≤ p := by
  sorry

end OMA.S_oeis_a014442

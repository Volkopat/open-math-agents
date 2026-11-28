import Mathlib

/-!
# Arithmetic progressions and averages of two primes

Source: https://mathoverflow.net/questions/173510
Conjecture (quoted in the question): let `aₙ = a₁ + (n-1) d` with `d > a₁ ≥ 1` and
`gcd(a₁, d) = 1`. Every term of the progression greater than `φ(d) d²` is either prime or
the average of two primes that are terms of the progression.

Conventions. The terms of the progression are the `m` with `m ≡ a₁ (mod d)` and `m ≥ a₁`;
the two primes may be equal only if the term itself is prime, which is covered by the first
alternative, so they are not required to be distinct.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mo_173510

theorem main :
    ∀ a₁ d : ℕ, 1 ≤ a₁ → a₁ < d → Nat.Coprime a₁ d →
      ∀ k : ℕ, d.totient * d ^ 2 < a₁ + k * d →
        (a₁ + k * d).Prime ∨
          ∃ i j : ℕ, (a₁ + i * d).Prime ∧ (a₁ + j * d).Prime ∧
            (a₁ + i * d) + (a₁ + j * d) = 2 * (a₁ + k * d) := by
  sorry

end OMA.S_mo_173510

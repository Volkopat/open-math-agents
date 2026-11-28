import Mathlib

/-!
# A098472: Least k such that Mersenne-prime(n)*2^k - 1 is prime

Source: https://oeis.org/A098472
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Least k such that Mersenne-prime(n)*2^k - 1 is prime (A000668(n)*2^k - 1), or 0 if no such k exists.
Conjecture: Mersenne-prime(12), Mersenne-prime(14), and Mersenne-prime(15) are Riesel primes,
i.e. M(n)*2^k - 1 is composite for all k >= 1 for n in {12, 14, 15}.
-/

namespace OMA.S_oeis_a098472

def IsMersennePrime (m : ℕ) : Prop :=
  Nat.Prime m ∧ ∃ p : ℕ, m = 2 ^ p - 1

noncomputable def mersennePrime (n : ℕ) : ℕ :=
  Nat.nth IsMersennePrime (n - 1)

theorem main :
    ∀ k : ℕ, 1 ≤ k →
      ¬ Nat.Prime (mersennePrime 12 * 2 ^ k - 1) ∧
      ¬ Nat.Prime (mersennePrime 14 * 2 ^ k - 1) ∧
      ¬ Nat.Prime (mersennePrime 15 * 2 ^ k - 1) := by
  sorry

end OMA.S_oeis_a098472

import Mathlib

/-!
# A079853: Primes p for which (p-2)! == 1 (mod p^2)

Source: https://oeis.org/A079853
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Primes p for which (p-2)! == 1 (mod p^2).
It is conjectured (2009) that for n > 1, a(n) == 3 (mod 8).
Conjecture: primes p such that Sum_{k=1..p-1} k^(1-p) == -1 (mod p^2) are the odd terms
of this sequence.
-/

namespace OMA.S_oeis_a079853

theorem main :
    (∀ p : ℕ, Nat.Prime p → 2 < p →
      Nat.factorial (p - 2) ≡ 1 [MOD p ^ 2] → p % 8 = 3) ∧
    (∀ p : ℕ, Nat.Prime p → 2 < p →
      (∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod (p ^ 2)) ^ (p - 1))⁻¹ = (-1 : ZMod (p ^ 2)) ↔
        Nat.factorial (p - 2) ≡ 1 [MOD p ^ 2])) := by
  sorry

end OMA.S_oeis_a079853

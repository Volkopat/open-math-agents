import Mathlib

/-!
# OEIS A355920

Seiichi Azuma's sequence starts at exponent 3. Jason Yuen conjectured
that its largest exceptional prime at exponent `n` is congruent to 1 modulo `n`.

Source: https://oeis.org/A355920 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Solitude1312
-/

namespace OMA.S_oeis_a355920

/-- Primes for which a residue is missing among the sums of two nth powers. -/
def exceptionalPrimes (n : ℕ) : Set ℕ :=
  {p | Nat.Prime p ∧ ∃ r : ZMod p, ∀ x y : ZMod p, x ^ n + y ^ n ≠ r}

theorem main :
    ∀ n : ℕ, 3 ≤ n → ∃ p : ℕ, IsGreatest (exceptionalPrimes n) p ∧ p ≡ 1 [MOD n] := by
  sorry

end OMA.S_oeis_a355920

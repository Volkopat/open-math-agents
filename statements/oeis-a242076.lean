import Mathlib

/-!
# OEIS A242076 and the exponent of two

Source: https://oeis.org/A242076
Credit: @dwilfand-sys (Lean formalization by Codex). J. Lowell posed the
conjecture in 2014. A term k admits a factorization of 2^k+1 as a Fermat
number times a prime. Having one factor of two means divisibility by two
and failure of divisibility by four.
-/

namespace OMA.S_oeis_a242076

def isTerm (k : ℕ) : Prop :=
  ∃ j q : ℕ, Nat.Prime q ∧ 2 ^ k + 1 = (2 ^ (2 ^ j) + 1) * q

theorem main : ∀ k : ℕ, (isTerm k ∧ 2 ∣ k ∧ ¬ 4 ∣ k) ↔ k = 6 := by
  sorry

end OMA.S_oeis_a242076

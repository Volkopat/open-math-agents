import Mathlib

/-!
# Divisibility among the totients in OEIS A305058

The sequence lists, in increasing order, positive integers whose divisor count
equals the number of positive integers with that Euler totient. The conjecture
states that each term divides a later term.

Source: https://oeis.org/A305058
-/

namespace OMA.S_oeis_a305058

def IsTerm (t : ℕ) : Prop :=
  0 < t ∧ t.divisors.card = Set.ncard {m : ℕ | 0 < m ∧ Nat.totient m = t}

theorem main : ∀ t : ℕ, IsTerm t → ∃ u : ℕ, t < u ∧ t ∣ u ∧ IsTerm u := by
  sorry

end OMA.S_oeis_a305058

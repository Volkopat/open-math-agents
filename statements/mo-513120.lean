import Mathlib

/-!
# Even losing positions in the subtract-a-prime-divisor game

Philip Weiss asks whether every even number with at least three distinct odd
prime factors is winning. A move subtracts one prime divisor. The player
with no move loses, and the terminal positions are 0 and 1.

Source: https://mathoverflow.net/questions/513120, Question 1.
Credit: @witeg4
-/

namespace OMA.S_mo_513120

/-- The player to move loses exactly when every legal move gives the opponent
a winning position. Repetitions in the factor list give the same move. -/
def losing (n : ℕ) : Bool :=
  if _hn : 2 ≤ n then
    n.primeFactorsList.attach.all fun p => !(losing (n - p.val))
  else true
termination_by n
decreasing_by
  apply Nat.sub_lt (by omega)
  exact (Nat.prime_of_mem_primeFactorsList p.property).pos

theorem main : ∀ n : ℕ, Even n → 3 ≤ (n.primeFactors.erase 2).card → losing n = false := by
  sorry

end OMA.S_mo_513120

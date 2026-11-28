import OMAStatements.S_oeis_a271217

-- Problem: A271217: Number of symmetric reduced rearrangement maps.
-- Upstream: formal-conjectures statements/oeis-a271217.lean:0 (declaration OMA.S_oeis_a271217.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: with O(j): a(2j+3) = 2a(2j+2) + a(2j+1) and E(j): a(2j+4) = (2j+3)a(2j+3) + (2j+2)a(2j+1),
-- one gets a(2j+2) = (4j+1)a(2j+1) - 4j a(2j); for n = 2j+4 the conjecture is
-- (1-4j)E(j) + ((1-4j)(2j+3)-4)O(j) + (4j+3) times that identity, and for n = 2j+5 it is
-- -(4j+1)O(j+1) - (8j+6)E(j) + 2O(j).

namespace P1A271217

open OMA.S_oeis_a271217

theorem a_succ3 (n : ℕ) : a (n + 3) =
    if (n + 3) % 2 = 1 then 2 * a (n + 2) + a (n + 1)
    else ((n : ℤ) + 2) * a (n + 2) + ((n : ℤ) + 1) * a n := rfl

theorem hodd (j : ℕ) : a (2 * j + 3) = 2 * a (2 * j + 2) + a (2 * j + 1) := by
  rw [a_succ3, if_pos (show (2 * j + 3) % 2 = 1 by omega)]

theorem heven (j : ℕ) :
    a (2 * j + 4) = (2 * (j : ℤ) + 3) * a (2 * j + 3) + (2 * (j : ℤ) + 2) * a (2 * j + 1) := by
  have h := a_succ3 (2 * j + 1)
  rw [if_neg (show ¬ ((2 * j + 1 + 3) % 2 = 1) by omega), show 2 * j + 1 + 3 = 2 * j + 4 by omega,
    show 2 * j + 1 + 2 = 2 * j + 3 by omega] at h
  push_cast at h
  linear_combination h

theorem e2' (j : ℕ) :
    a (2 * j + 2) = (4 * (j : ℤ) + 1) * a (2 * j + 1) - 4 * (j : ℤ) * a (2 * j) := by
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h
    decide
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [show 2 * (i + 1) + 2 = 2 * i + 4 by omega, show 2 * (i + 1) + 1 = 2 * i + 3 by omega,
      show 2 * (i + 1) = 2 * i + 2 by omega]
    have he := heven i
    have ho := hodd i
    push_cast
    linear_combination he - (2 * (i : ℤ) + 2) * ho

end P1A271217

open OMA.S_oeis_a271217 P1A271217 in
theorem OMA.solution : type_of% @OMA.S_oeis_a271217.main := by
  intro n hn
  obtain ⟨j, rfl | rfl⟩ : ∃ j, n = 2 * j + 4 ∨ n = 2 * j + 5 := ⟨(n - 4) / 2, by omega⟩
  · rw [show 2 * j + 4 - 1 = 2 * j + 3 by omega, show 2 * j + 4 - 2 = 2 * j + 2 by omega,
      show 2 * j + 4 - 3 = 2 * j + 1 by omega, show 2 * j + 4 - 4 = 2 * j by omega]
    have e1 := heven j
    have o1 := hodd j
    have e2 := e2' j
    push_cast
    linear_combination (1 - 4 * (j : ℤ)) * e1 + ((1 - 4 * (j : ℤ)) * (2 * (j : ℤ) + 3) - 4) * o1
      + (4 * (j : ℤ) + 3) * e2
  · rw [show 2 * j + 5 - 1 = 2 * j + 4 by omega, show 2 * j + 5 - 2 = 2 * j + 3 by omega,
      show 2 * j + 5 - 3 = 2 * j + 2 by omega, show 2 * j + 5 - 4 = 2 * j + 1 by omega]
    have o2 := hodd (j + 1)
    rw [show 2 * (j + 1) + 3 = 2 * j + 5 by omega, show 2 * (j + 1) + 2 = 2 * j + 4 by omega,
      show 2 * (j + 1) + 1 = 2 * j + 3 by omega] at o2
    have e1 := heven j
    have o1 := hodd j
    push_cast
    linear_combination (-4 * (j : ℤ) - 1) * o2 + (-8 * (j : ℤ) - 6) * e1 + 2 * o1

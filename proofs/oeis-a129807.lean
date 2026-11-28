import OMAStatements.S_oeis_a129807

-- Problem: A129807: Primes congruent to +-7 mod 18.
-- Upstream: formal-conjectures statements/oeis-a129807.lean:0 (declaration OMA.S_oeis_a129807.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: p mod 18 = 7 or 11 gives p mod 9 = 7 or 2 and p is not 2. Conversely a prime
-- other than 2 is odd, and an odd number that is 7 or 2 modulo 9 is 7 or 11 modulo 18.

open OMA.S_oeis_a129807 in
theorem OMA.solution : type_of% @OMA.S_oeis_a129807.main := by
  intro p
  show (p.Prime ∧ (p % 18 = 7 ∨ p % 18 = 11)) ↔
    (((p.Prime ∧ p % 9 = 7) ∨ (p.Prime ∧ p % 9 = 2)) ∧ p ≠ 2)
  constructor
  · rintro ⟨hp, h | h⟩
    · exact ⟨Or.inl ⟨hp, by omega⟩, by omega⟩
    · exact ⟨Or.inr ⟨hp, by omega⟩, by omega⟩
  · rintro ⟨⟨hp, h⟩ | ⟨hp, h⟩, hne⟩
    · have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hne
      exact ⟨hp, Or.inl (by omega)⟩
    · have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hne
      exact ⟨hp, Or.inr (by omega)⟩

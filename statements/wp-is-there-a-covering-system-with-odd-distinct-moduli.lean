import Mathlib

-- Problem: Is there a covering system with odd distinct moduli?
-- A covering system picks finitely many distinct odd moduli m > 2 and one residue
-- class per modulus, so that every integer belongs to at least one of them.
-- Source: Wikipedia list of open problems in mathematics (not yet formalized upstream).

namespace OMA.S_wp_is_there_a_covering_system_with_odd_distinct_moduli

theorem main : ∃ S : Finset (ℕ × ℕ),
    (∀ p ∈ S, 3 ≤ p.2 ∧ p.2 % 2 = 1) ∧
    (∀ p ∈ S, ∀ q ∈ S, p.2 = q.2 → p = q) ∧
    (∀ n : ℤ, ∃ p ∈ S, ∃ t : ℤ, n = (p.1 : ℤ) + t * (p.2 : ℤ)) := by
  sorry

end OMA.S_wp_is_there_a_covering_system_with_odd_distinct_moduli

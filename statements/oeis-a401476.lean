import Mathlib

/-!
# Prime exponents giving primitive practical numbers in OEIS A401476

Frank M. Jackson conjectures that infinitely many primes `p` give a primitive
practical number of the form `2 ^ p - 2`.

A positive integer is practical if every positive integer at most it is a sum of
distinct divisors. As in OEIS A267124, a practical integer is primitive if dividing
it by any prime whose square divides it produces an integer that is no longer
practical. For a squarefree practical number this condition is vacuous.

Source: https://oeis.org/A401476 and https://oeis.org/A267124
(OEIS Foundation, CC BY-SA 4.0).
Formalized by @Qwer2077.
-/

namespace OMA.S_oeis_a401476

def IsPractical (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, 0 < m → m ≤ n → ∃ s ⊆ n.divisors, ∑ d ∈ s, d = m

def IsPrimitivePractical (n : ℕ) : Prop :=
  IsPractical n ∧ ∀ q : ℕ, q.Prime → q ^ 2 ∣ n → ¬ IsPractical (n / q)

theorem main : Set.Infinite {p : ℕ | p.Prime ∧ IsPrimitivePractical (2 ^ p - 2)} := by
  sorry

end OMA.S_oeis_a401476

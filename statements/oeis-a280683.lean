import Mathlib

/-!
# Sums of two distinct-prime products

OEIS A280683 counts ordered representations as a sum of two squarefree
semiprimes. The conjecture is that this count is positive for every
natural number greater than 82.

Sources: https://oeis.org/A280683 and https://oeis.org/A006881
(OEIS Foundation, CC BY-SA 4.0).
Credit: @wtho704
-/

namespace OMA.S_oeis_a280683

/-- A squarefree semiprime is a product of two distinct primes. -/
def IsSquarefreeSemiprime (n : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p * q

open Classical in
/-- The first summand determines an ordered representation. -/
noncomputable def count (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter fun a =>
    IsSquarefreeSemiprime a ∧ IsSquarefreeSemiprime (n - a)).card

theorem main : ∀ n : ℕ, 82 < n → 0 < count n := by
  sorry

end OMA.S_oeis_a280683

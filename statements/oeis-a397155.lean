import Mathlib

/-!
# Cubes as a semiprime plus a prime

Source: https://oeis.org/A397155 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @sturdy4days.

The conjecture in the comments asks for a prime summand and a product
of two primes. The two factors of the product may coincide.
-/

namespace OMA.S_oeis_a397155

theorem main : ∀ n : ℕ, 1 < n → ∃ p q r : ℕ,
    p.Prime ∧ q.Prime ∧ r.Prime ∧ n ^ 3 = p * q + r := by
  sorry

end OMA.S_oeis_a397155

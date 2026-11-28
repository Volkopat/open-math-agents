import Mathlib

-- Problem: Does the converse of Wolstenholme's theorem hold for all natural numbers?
-- Wolstenholme's theorem: for every prime p > 3, p ^ 2 divides Nat.choose (2 * p - 1) (p - 1).
-- The question is whether this divisibility property characterises the primes, i.e. whether
-- every n > 4 with n ^ 2 dividing Nat.choose (2 * n - 1) (n - 1) must itself be prime.

namespace OMA.S_wp_does_the_converse_of_wolstenholme_s_theorem_hold_for_all_natural_numbers

theorem main : ∀ n : ℕ, 4 < n → n ^ 2 ∣ Nat.choose (2 * n - 1) (n - 1) → n.Prime := by
  sorry

end OMA.S_wp_does_the_converse_of_wolstenholme_s_theorem_hold_for_all_natural_numbers

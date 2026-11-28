import Mathlib

/-!
# Is every integer n > 1 the sum of two squares and two central binomial coefficients?

Source: https://mathoverflow.net/questions/301581 (Zhi-Wei Sun, CC BY-SA 4.0).

The central binomial coefficients are `binom(2n, n)` (`n = 0, 1, 2, …`). Question: is every
integer `n > 1` of the form `a² + b² + binom(2c, c) + binom(2d, d)` with `a, b, c, d ∈ ℕ`?
The poser conjectures yes (verified for `n ≤ 6 × 10⁹`); `main` states it.
-/

namespace OMA.S_mo_301581

theorem main : ∀ n : ℕ, 1 < n →
    ∃ a b c d : ℕ, n = a ^ 2 + b ^ 2 + Nat.centralBinom c + Nat.centralBinom d := by
  sorry

end OMA.S_mo_301581

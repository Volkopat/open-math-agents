import Mathlib

/-!
# A primitive root g < p which is the sum of two central binomial coefficients

Source: https://mathoverflow.net/questions/301039 (Zhi-Wei Sun, CC BY-SA 4.0).

The central binomial coefficients are `binom(2n, n)` (`n = 0, 1, 2, …`). Question: does each odd
prime `p` have a primitive root `g < p` which is the sum of two central binomial coefficients? The
sum is the genuine integer sum `g = binom(2k, k) + binom(2m, m)` (clarified by the poser), and `g`
is a primitive root modulo `p` when its class in `ZMod p` has multiplicative order `p - 1`.
The poser conjectures yes; `main` states it.
-/

namespace OMA.S_mo_301039

theorem main : ∀ p : ℕ, p.Prime → p ≠ 2 → ∃ k m : ℕ,
    Nat.centralBinom k + Nat.centralBinom m < p ∧
      orderOf ((Nat.centralBinom k + Nat.centralBinom m : ℕ) : ZMod p) = p - 1 := by
  sorry

end OMA.S_mo_301039

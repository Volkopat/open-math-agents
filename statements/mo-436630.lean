import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Canonical square roots modulo primes congruent to three modulo four

Source: https://mathoverflow.net/questions/436630
Author of the source question: joro, 15 December 2022.
Credit: @etaubman

This states the three displayed congruence claims in the source, with the
original exponent range. Equality in `ZMod p` is congruence modulo `p`, and
`orderOf g = p - 1` says that `g` has maximal multiplicative order. The source's
separate question about an improved discrete logarithm attack is not a claim
in this statement.
-/

namespace OMA.S_mo_436630

def canonicalRoot (p : ℕ) (a : ZMod p) : ZMod p := a ^ ((p + 1) / 4)

theorem main : ∀ (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3)
    (g : ZMod p) (hg : orderOf g = p - 1) (n : ℕ)
    (hn₁ : 1 < n) (hn₂ : n < (p - 3) / 4),
    canonicalRoot p (g ^ (4 * n)) = g ^ (2 * n) ∧
    canonicalRoot p (g ^ (4 * n + 2)) = -(g ^ (2 * n + 1)) ∧
    canonicalRoot p (g ^ (2 * n)) = (-g) ^ n := by
  sorry

end OMA.S_mo_436630

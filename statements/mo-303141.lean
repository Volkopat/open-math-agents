import Mathlib

/-!
# Is the conjecture A + B = C following correct?

Source: https://mathoverflow.net/questions/303141/is-the-conjecture-ab-c-following-correct
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (asked on MathOverflow): let `A, B, C` be positive integers with `A + B = C` and
`gcd(A, B, C) = 1`. Let `d` be the minimum of all exponents in the prime factorisations of `A`,
`B` and `C`. Then `d ≤ 5`.

## Encoding

* Since `A, B, C` are pairwise coprime, every prime factor of `ABC` divides exactly one of them
  with the same exponent, so the exponents are the `p`-adic valuations of `ABC` at its prime
  factors (`C ≥ 2`, so there is at least one).
* `main` states the conjecture as posed: some prime factor of `ABC` has exponent `≤ 5`.
-/

namespace OMA.S_mo_303141

theorem main :
    ∀ A B C : ℕ, 0 < A → 0 < B → A + B = C → Nat.gcd (Nat.gcd A B) C = 1 →
      ∃ p ∈ (A * B * C).primeFactors, padicValNat p (A * B * C) ≤ 5 := by
  sorry

end OMA.S_mo_303141

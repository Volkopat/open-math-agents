import OMAStatements.S_oeis_a293482
import Mathlib

-- Reduction oeis-a293482.R1 of step oeis-a293482
-- Credit: @Ciphore
-- The count of fifth powers in the unit group separates into four independent
-- group-arithmetic regimes. On `(ZMod 2^e)ˣ` the order is coprime to `5`, so the power
-- map is a bijection and the count is the group order itself — the noncyclic 2-adic
-- regime. At the exceptional prime `5` the kernel of the power map picks up the factor
-- `5` from the group order `4 * 5^(e-1)`. At odd primes `p ≢ 1 (mod 5)` the group is
-- cyclic of order coprime to `5`, the kernel is trivial, and the power map is bijective.
-- At primes `p ≡ 1 (mod 5)` the cyclic group has exactly `5` fifth roots of unity, so the
-- image is one fifth of the group.

namespace OMA.R_oeis_a293482_R1

open OMA.S_oeis_a293482

/-- The 2-adic regime: the power map on `(ZMod 2^e)ˣ` is a bijection since the group order
    is coprime to `5`. -/
def H1 : Prop := (∀ e : ℕ, e ≤ 1 → a (2 ^ e) = 1) ∧
  ∀ e : ℕ, 1 ≤ e → a (2 ^ e) = 2 ^ (e - 1)

/-- The exceptional-prime regime: the count at powers of `5` itself. -/
def H2 : Prop := a 5 = 4 ∧ ∀ e : ℕ, 1 < e → a (5 ^ e) = 4 * 5 ^ (e - 2)

/-- The trivial-kernel regime: at odd primes `p ≢ 1 (mod 5)` the cyclic unit group has
    order coprime to `5` and the power map is a bijection. -/
def H3 : Prop := ∀ p e : ℕ, p.Prime → (p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4) → 1 ≤ e →
  a (p ^ e) = (p - 1) * p ^ (e - 1)

/-- The order-five-kernel regime: at primes `p ≡ 1 (mod 5)` the cyclic unit group has
    exactly `5` fifth roots of unity. -/
def H4 : Prop := ∀ p e : ℕ, p.Prime → p % 5 = 1 → 1 ≤ e →
  a (p ^ e) = (p - 1) * p ^ (e - 1) / 5

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a293482.main := by
  intro h2pow h5pow htriv hkernel
  obtain ⟨h2a, h2b⟩ := h2pow
  obtain ⟨h5a, h5b⟩ := h5pow
  exact ⟨h2a, h2b, h5a, h5b, htriv, hkernel⟩

end OMA.R_oeis_a293482_R1

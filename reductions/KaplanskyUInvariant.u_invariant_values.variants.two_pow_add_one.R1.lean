import FormalConjectures.Paper.KaplanskyUInvariant
import Mathlib

/-! Reduction of Vishik's theorem on fields of u-invariant 2^r + 1 to Izhboldin's base case
(2^3 + 1 = 9) and Vishik's inductive doubling step. `main` runs the induction on r >= 3. -/

namespace OMA.R_KaplanskyUInvariant_u_invariant_values_variants_two_pow_add_one_R1

open KaplanskyUInvariant

/-- Izhboldin (2001): there is a field of u-invariant 9, the base case r = 3 of Vishik's
theorem (2^3 + 1 = 9). -/
def H1 : Prop :=
  IsUInvariant 9

/-- Vishik's doubling step: from a field of u-invariant 2^r + 1 with r >= 3 one gets a field of
u-invariant 2^(r + 1) + 1. This is the inductive construction of Vishik (2009). -/
def H2 : Prop :=
  ∀ r : ℕ, 3 ≤ r → IsUInvariant (2 ^ r + 1) → IsUInvariant (2 ^ (r + 1) + 1)

theorem main : H1 → H2 →
    type_of% @KaplanskyUInvariant.u_invariant_values.variants.two_pow_add_one := by
  intro h1 h2
  refine Nat.le_induction ?_ ?_
  · have h9 : (2 : ℕ) ^ 3 + 1 = 9 := by norm_num
    rwa [h9]
  · intro n hn ih
    exact h2 n hn ih

end OMA.R_KaplanskyUInvariant_u_invariant_values_variants_two_pow_add_one_R1

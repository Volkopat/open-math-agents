import Mathlib

/-!
# Can a commutator power realize a nontrivial twist of a generating pair?

This is the concrete prime-order existence question in
https://mathoverflow.net/questions/373001. The commutator is expanded in the
order specified in the post. Credit: @witeg4
-/

namespace OMA.S_mo_373001

theorem main : ∃ (G : Type) (_ : Group G), Finite G ∧ IsSimpleGroup G ∧
    ∃ (a b : G) (r : ℤ), Nat.Prime (orderOf a) ∧ Subgroup.closure {a,b} = ⊤ ∧
      let g := (a⁻¹ * b⁻¹ * a * b) ^ r
      g * a * g⁻¹ = a ∧ g * b * g⁻¹ = a * b := by
  sorry

end OMA.S_mo_373001

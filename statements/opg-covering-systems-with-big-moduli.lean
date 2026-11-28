import Mathlib

/-! # Covering systems with large distinct moduli

The source asks whether a distinct covering system exists for every lower
bound. Each modulus in the finite set has one residue, and their classes
must cover every integer. Hough answered this existence question negatively.

Source: https://www.openproblemgarden.org/op/covering_systems_with_big_moduli
Reference: https://annals.math.princeton.edu/2015/181-1/p06
Credit: @steveDOTdigital
-/

namespace OMA.S_opg_covering_systems_with_big_moduli

theorem main :
    ∀ N : ℤ, ∃ (moduli : Finset ℕ) (residue : ℕ → ℤ),
      (∀ m ∈ moduli, 0 < m ∧ N ≤ (m : ℤ)) ∧
      ∀ z : ℤ, ∃ m ∈ moduli, z ≡ residue m [ZMOD (m : ℤ)] := by
  sorry

end OMA.S_opg_covering_systems_with_big_moduli

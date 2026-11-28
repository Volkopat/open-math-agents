import Mathlib

namespace OMA.S_mo_420865

abbrev Symmetric (n : ℕ) := Equiv.Perm (Fin n)

/-- Count each conjugacy class with a representative satisfying P once. -/
noncomputable def countClasses {n : ℕ} (P : Symmetric n → Prop) : ℕ :=
  {c : ConjClasses (Symmetric n) |
    ∃ g : Symmetric n, ConjClasses.mk g = c ∧ P g}.ncard

/-- For sufficiently large n, the sign row has a maximum number of
negative entries in the character table of the symmetric group. -/
theorem main :
    ∃ N : ℕ, ∀ n ≥ N,
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
        (ρ : Representation ℂ (Symmetric n) V),
        ρ.IsIrreducible →
          countClasses (fun g => (ρ.character g).re < 0) ≤
            countClasses (fun g : Symmetric n => Equiv.Perm.sign g = -1) := by
  sorry

end OMA.S_mo_420865

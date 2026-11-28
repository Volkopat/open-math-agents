import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Int.Basic

/-! Source: Question 2 at https://mathoverflow.net/questions/211276 -/

namespace OMA.S_mo_211276

def label (l : ℕ) (i : Fin (2 * l + 1)) : ℤ :=
  (i.val : ℤ) - (l : ℤ)

def IsAdditive (l : ℕ) (p : Equiv.Perm (Fin (2 * l + 1))) : Prop :=
  ∃ q : Equiv.Perm (Fin (2 * l + 1)), ∀ i, label l i + label l (p i) = label l (q i)

theorem main :
    ∀ l : ℕ,
      Subgroup.closure {p : Equiv.Perm (Fin (2 * l + 1)) | IsAdditive l p} = ⊤ := by
  sorry

end OMA.S_mo_211276

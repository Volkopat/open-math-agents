import Mathlib

/-!
# Do elements outside the penultimate left Engel set generate a finite nilpotent group?

Source: https://mathoverflow.net/questions/144090
Credit: @witeg4
-/

namespace OMA.S_mo_144090

/-- The second argument stays fixed in the iterated left Engel commutator. -/
def comm {G : Type*} [Group G] (x y : G) : ℕ → G
  | 0 => x
  | n+1 => (comm x y n)⁻¹ * y⁻¹ * comm x y n * y

def leftEngel (G : Type*) [Group G] (n : ℕ) : Set G :=
  {y | ∀ x, comm x y n = 1}

theorem main : ∀ (G : Type) [Group G] [Finite G] [Group.IsNilpotent G] (n : ℕ),
    0 < n → leftEngel G n = Set.univ →
    (∀ m : ℕ, 0 < m → m < n → leftEngel G m ≠ Set.univ) →
    Subgroup.closure (leftEngel G (n-1))ᶜ = ⊤ := by
  sorry

end OMA.S_mo_144090

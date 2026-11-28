import Mathlib.GroupTheory.Sylow

/-!
# Simultaneous minimal intersections of Sylow subgroups

Conjecture A of Francesca Lisi and Luca Sabatini asks for a single conjugating
element that gives an inclusion-minimal intersection for each Sylow subgroup
in a family belonging to distinct primes.

Source: https://arxiv.org/abs/2505.21222
Credit: @jacklarmer
-/

namespace OMA.S_arxiv_2505_21222

/-- The intersection of `H` with its conjugate `g⁻¹ H g`. -/
def conjugateIntersection {G : Type*} [Group G] (H : Subgroup G) (g : G) : Subgroup G :=
  H ⊓ H.map (MulAut.conj (g⁻¹)).toMonoidHom

theorem main :
    ∀ (G : Type*) [Group G] [Finite G] (n : ℕ) (p : Fin n → ℕ),
      Function.Injective p → (∀ i, (p i).Prime) →
      ∀ P : (i : Fin n) → Sylow (p i) G,
        ∃ x : G, ∀ (i : Fin n) (g : G),
          ¬ conjugateIntersection (P i).toSubgroup g < conjugateIntersection (P i).toSubgroup x := by
  sorry

end OMA.S_arxiv_2505_21222

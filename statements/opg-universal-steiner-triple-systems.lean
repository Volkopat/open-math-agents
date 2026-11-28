import Mathlib

namespace OMA.S_opg_universal_steiner_triple_systems

/-- The blocks have size three, and each pair of distinct points belongs to one block. -/
def IsSteinerTripleSystem {n : ℕ} (blocks : Finset (Finset (Fin n))) : Prop :=
  (∀ b ∈ blocks, b.card = 3) ∧
  (∀ x y : Fin n, x ≠ y → ∃! b : Finset (Fin n), b ∈ blocks ∧ x ∈ b ∧ y ∈ b)

/-- Every finite simple cubic graph admits an edge coloring whose incident colors
at each vertex form one of the blocks. -/
def IsUniversal {n : ℕ} (blocks : Finset (Finset (Fin n))) : Prop :=
  ∀ (m : ℕ) (G : SimpleGraph (Fin m)),
    (∀ v, (G.neighborSet v).ncard = 3) →
    ∃ color : G.edgeSet → Fin n,
      ∀ v, ∃ b ∈ blocks,
        color '' {e : G.edgeSet | (e : Sym2 (Fin m)) ∈ G.incidenceSet v} =
          (↑b : Set (Fin n))

/-- Orders of universal Steiner triple systems. -/
def HasUniversalSystem (n : ℕ) : Prop :=
  ∃ blocks : Finset (Finset (Fin n)),
    IsSteinerTripleSystem blocks ∧ IsUniversal blocks

/-- The minimum order is thirteen, and every Steiner triple system of that order
is universal. -/
theorem main :
    IsLeast {n : ℕ | HasUniversalSystem n} 13 ∧
      ∀ blocks : Finset (Finset (Fin 13)),
        IsSteinerTripleSystem blocks → IsUniversal blocks := by
  sorry

end OMA.S_opg_universal_steiner_triple_systems

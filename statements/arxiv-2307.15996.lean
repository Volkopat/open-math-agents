import Mathlib

namespace OMA.S_arxiv_2307_15996

/-- Two cells on the `m × n` grid graph are adjacent if their Manhattan distance is `1`. -/
def gridAdj {m n : ℕ} (u v : Fin m × Fin n) : Prop :=
  (u.1 = v.1 ∧ (u.2.val + 1 = v.2.val ∨ v.2.val + 1 = u.2.val)) ∨
  (u.2 = v.2 ∧ (u.1.val + 1 = v.1.val ∨ v.1.val + 1 = u.1.val))

/-- A subset `P` of grid cells is grid-connected if it is nonempty and any two cells in `P`
are joined by a finite path of grid-adjacent cells staying inside `P`. -/
def IsGridConnected {m n : ℕ} (P : Finset (Fin m × Fin n)) : Prop :=
  P.Nonempty ∧
  ∀ u ∈ P, ∀ v ∈ P,
    Relation.ReflTransGen (fun x y => x ∈ P ∧ y ∈ P ∧ gridAdj x y) u v

/-- A `t`-omino is a grid-connected subset of `t` cells. -/
def IsPolyomino {m n : ℕ} (t : ℕ) (P : Finset (Fin m × Fin n)) : Prop :=
  P.card = t ∧ IsGridConnected P

/-- A `t`-omino tiling of the `m × n` grid is a collection of pairwise disjoint `t`-ominoes
covering every cell of `Fin m × Fin n`. -/
def IsTiling {m n : ℕ} (t : ℕ) (T : Finset (Finset (Fin m × Fin n))) : Prop :=
  (∀ P ∈ T, IsPolyomino t P) ∧
  (∀ P ∈ T, ∀ Q ∈ T, P ≠ Q → Disjoint P Q) ∧
  (∀ x : Fin m × Fin n, ∃ P ∈ T, x ∈ P)

/-- One ReCom (recombination) move between two `t`-omino tilings of the `m × n` grid:
pick two distinct tiles `A, B ∈ T₁`, merge them into `A ∪ B`, and re-partition `A ∪ B` into
two disjoint `t`-ominoes `A', B'` to obtain `T₂`. -/
def ReComStep {m n : ℕ} (t : ℕ) (T₁ T₂ : Finset (Finset (Fin m × Fin n))) : Prop :=
  ∃ A ∈ T₁, ∃ B ∈ T₁, A ≠ B ∧
    ∃ A' B' : Finset (Fin m × Fin n),
      IsPolyomino t A' ∧ IsPolyomino t B' ∧ Disjoint A' B' ∧
      A ∪ B = A' ∪ B' ∧
      T₂ = insert A' (insert B' ((T₁.erase A).erase B))

/-- ReCom irreducibility conjecture for polyomino grid tilings (refuted by locked polyomino
tilings in arXiv:2307.15996): for every grid `m × n` and tile size `t ≥ 1`, any two `t`-omino
tilings of the `m × n` grid are connected by a finite sequence of ReCom moves. -/
theorem main :
    ∀ (m n t : ℕ), 0 < m → 0 < n → 0 < t →
      ∀ (T₁ T₂ : Finset (Finset (Fin m × Fin n))),
        IsTiling t T₁ → IsTiling t T₂ →
          Relation.ReflTransGen (ReComStep t) T₁ T₂ := by
  sorry

end OMA.S_arxiv_2307_15996

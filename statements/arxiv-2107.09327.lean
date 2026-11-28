import Mathlib

namespace OMA.S_arxiv_2107_09327

/-- A permutation group `G ≤ Equiv.Perm (Fin n)` is transitive if it acts transitively on `Fin n`. -/
def IsTransitivePermGroup {n : ℕ} (G : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  ∀ v w : Fin n, ∃ g ∈ G, g v = w

/-- A finite subset `F ⊆ G` is intersecting if every two elements of `F` agree on at least one point. -/
def IsIntersecting {n : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (F : Finset (Equiv.Perm (Fin n))) : Prop :=
  (∀ g ∈ F, g ∈ G) ∧ ∀ g ∈ F, ∀ h ∈ F, ∃ v : Fin n, g v = h v

/-- The cardinality of the point stabilizer `G_v = {g ∈ G | g v = v}`. -/
noncomputable def stabilizerCard {n : ℕ} (G : Subgroup (Equiv.Perm (Fin n))) (v : Fin n) : ℕ :=
  (@Finset.filter (Equiv.Perm (Fin n)) (fun g => g ∈ G ∧ g v = v) (Classical.decPred _) Finset.univ).card

/-- Conjecture (Meagher–Razafimahatratra–Spiga 2021; disproved in arXiv:2107.09327):
Every transitive permutation group `G` of degree `p * q`, where `p > q` are odd primes,
has intersection density `ρ(G) = 1`, meaning that every intersecting subset `F ⊆ G`
satisfies `|F| ≤ |G_v|` for every point `v`. -/
theorem main :
    ∀ (p q : ℕ), Nat.Prime p → Nat.Prime q → Odd p → Odd q → q < p →
    ∀ (G : Subgroup (Equiv.Perm (Fin (p * q)))),
      IsTransitivePermGroup G →
      ∀ (v : Fin (p * q)) (F : Finset (Equiv.Perm (Fin (p * q)))),
        IsIntersecting G F → F.card ≤ stabilizerCard G v := by
  sorry

end OMA.S_arxiv_2107_09327

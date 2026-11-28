import Mathlib

/-!
# The adjacency spectral radius relative to mean degree

MathOverflow 455501 by user135520, September 2023, CC BY-SA 4.0.
https://mathoverflow.net/questions/455501

For a graph with n vertices and s nonisolated vertices, the largest possible
ratio of spectral radius to positive mean degree is n/(2 sqrt(s-1)).
Stars with isolated vertices attain equality. The two-step walk estimate is
the support-sensitive form of the bound in Hong Yuan, A bound on the spectral
radius of graphs (1988), https://doi.org/10.1016/0024-3795(88)90183-8.

Every rational ratio at least one occurs even for a connected bipartite graph. The final
example gives the requested ratio two on twenty vertices.
-/

namespace OMA.S_mo_455501
open Finset SimpleGraph
variable {V : Type} [Fintype V]

noncomputable def neighbors (G : SimpleGraph V) (v : V) : Finset V := by
  classical exact G.neighborFinset v

noncomputable def totalDegree (G : SimpleGraph V) : ℕ := ∑ v, (neighbors G v).card

noncomputable def active (G : SimpleGraph V) : Finset V := by
  classical exact univ.filter fun v => (neighbors G v).Nonempty

noncomputable def meanDegree (G : SimpleGraph V) : ℝ := totalDegree G / (Fintype.card V : ℝ)

def eigenvalue (G : SimpleGraph V) (r : ℝ) : Prop :=
  ∃ x : V → ℝ, x ≠ 0 ∧ ∀ v, ∑ u ∈ neighbors G v, x u = r * x v

def topEigen (G : SimpleGraph V) (r : ℝ) : Prop := IsGreatest {t | eigenvalue G t} r

end OMA.S_mo_455501
namespace OMA.S_mo_455501

/-- A five-clique with fifteen leaves attached to its vertex zero. -/
def pineapple : SimpleGraph (Fin 20) where
  Adj i j := i ≠ j ∧ (i = 0 ∨ j = 0 ∨ i.val < 5 ∧ j.val < 5)
  symm.symm := by intro i j; aesop
  loopless := ⟨by simp⟩

end OMA.S_mo_455501
namespace OMA.S_mo_455501

theorem main :
    (∀ (V : Type) [Fintype V] (G : SimpleGraph V) (r : ℝ),
      eigenvalue G r → (active G).Nonempty →
      r^2+(active G).card ≤ (totalDegree G:ℝ)+1 ∧
      4*((active G).card-1:ℝ)*r^2 ≤ (totalDegree G:ℝ)^2) ∧
    (∀ r z : ℕ, 0<r → ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      Fintype.card V = r+1+z ∧ (active G).card=r+1 ∧ totalDegree G=2*r ∧
      topEigen G (Real.sqrt r)) ∧
    (∀ p q : ℕ, 0<q → q≤p → ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (r : ℝ),
      G.Connected ∧ G.IsBipartite ∧ 0 < meanDegree G ∧ topEigen G r ∧ q*r=p*meanDegree G) ∧
    pineapple.Connected ∧ meanDegree pineapple = 5/2 ∧ topEigen pineapple 5 := by
  sorry

end OMA.S_mo_455501

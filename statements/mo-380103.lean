import Mathlib

/-!
# The rank of a Laplacian-type matrix

Source: Seva, https://mathoverflow.net/questions/380103 (CC BY-SA 4.0).
Credit: @connoranderson.

Write M as diag(K) plus the adjacency matrix of a simple graph whose
vertex i has degree 2K_i. Over the reals, diagonal normalization gives
n k ≤ rank(M) (k+2) whenever K_i ≥ k > 0. A union of h complete tripartite
graphs with k vertices in each class has nullity at least 2h. Setting h=k³
gives n=3k⁴ and shows that the maximal real nullity has order n^(3/4)
in the regime of the question. These regular examples also settle Q3.

Over the prime field, row supports give n ≤ rank(M) (2u+1) if K_i ≤ u.
The union of h complete bipartite graphs with classes of size 2p has rank
exactly 2h. Setting h=p³ gives n=4p⁴, so the minimum modular rank has
order n^(3/4). The bounds cover arbitrary finite vertex types.
-/

namespace OMA.S_mo_380103
open Matrix Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def mat (R : Type) [CommRing R] (G : SimpleGraph ι) [DecidableRel G.Adj]
    (K : ι → ℕ) : Matrix ι ι R :=
  diagonal (fun i => (K i : R)) + G.adjMatrix R
def degrees (G : SimpleGraph ι) [DecidableRel G.Adj] (K : ι → ℕ) : Prop :=
  ∀ i, (univ.filter (G.Adj i)).card=2*K i
def partGraph (h s k : ℕ) : SimpleGraph (Fin h × Fin s × Fin k) where
  Adj x y := x.1=y.1 ∧ x.2.1≠y.2.1
  symm := ⟨fun _ _ t => ⟨t.1.symm,Ne.symm t.2⟩⟩
  loopless := ⟨fun _ t => t.2 rfl⟩
instance (h s k : ℕ) : DecidableRel (partGraph h s k).Adj :=
  fun x y => inferInstanceAs (Decidable (x.1=y.1 ∧ x.2.1≠y.2.1))

theorem main :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (K : V → ℕ) (k : ℕ), 0<k → (∀ i,k≤K i) → degrees G K →
      Fintype.card V*k ≤ (mat ℝ G K).rank*(k+2)) ∧
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (K : V → ℕ) (u p : ℕ) [Fact p.Prime], (∀ i,0<K i) → (∀ i,K i≤u) → degrees G K →
      Fintype.card V ≤ (mat (ZMod p) G K).rank*(2*u+1)) ∧
    (∀ h k : ℕ, 0<k → degrees (partGraph h 3 k) (fun _ => k) ∧
      (mat ℝ (partGraph h 3 k) (fun _ => k)).rank+2*h ≤ 3*h*k) ∧
    (∀ (h p : ℕ) [Fact p.Prime], degrees (partGraph h 2 (2*p)) (fun _ => p) ∧
      (mat (ZMod p) (partGraph h 2 (2*p)) (fun _ => p)).rank=2*h) := by
  sorry
end OMA.S_mo_380103

import FormalConjectures.ErdosProblems.«61»
import Mathlib

-- Reduction Erdos61.erdos_61.R1
-- Credit: @marcusbuffett

/-!
# Erdős 61 (Erdős–Hajnal): complete and edgeless forbidden graphs

A classical case of the conjecture: when the forbidden induced subgraph `H` is a complete graph
`K_m` or an edgeless graph on `m` vertices, Ramsey's theorem with the Erdős–Szekeres bound
(every graph on `(t+1)^m` vertices contains a clique of size `m` or an independent set of size
`t`) gives a clique or an independent set of polynomial size `n^(1/(2m+2))`. This is `H1`.
The open core `H2` is the conjecture for every other graph on `Fin m`; every graph on a finite
type is isomorphic to one on `Fin m`, and the transport is done in `main`.
-/

namespace OMA.R_Erdos61_erdos_61_R1
open Erdos61 Filter SimpleGraph

/-- Erdős–Hajnal for complete and for edgeless forbidden graphs on `m` vertices (Ramsey). -/
def H1 : Prop :=
  ∀ m : ℕ,
    (∃ c > (0 : ℝ), IsErdosHajnalLowerBound (⊤ : SimpleGraph (Fin m)) (fun n : ℕ => (n : ℝ) ^ c)) ∧
    (∃ c > (0 : ℝ), IsErdosHajnalLowerBound (⊥ : SimpleGraph (Fin m)) (fun n : ℕ => (n : ℝ) ^ c))

/-- The open core: Erdős–Hajnal for every graph on `Fin m` that is neither complete nor
edgeless. -/
def H2 : Prop :=
  ∀ (m : ℕ) (H : SimpleGraph (Fin m)), H ≠ ⊤ → H ≠ ⊥ →
    ∃ c > (0 : ℝ), IsErdosHajnalLowerBound H (fun n : ℕ => (n : ℝ) ^ c)

/-- The Erdős–Hajnal property is invariant under relabelling the vertices of `H`. -/
lemma transport {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (H : SimpleGraph α) (f : ℕ → ℝ)
    (h : IsErdosHajnalLowerBound (H.comap e.symm.toEmbedding) f) :
    IsErdosHajnalLowerBound H f := by
  unfold IsErdosHajnalLowerBound at h ⊢
  filter_upwards [h] with n hn G hG
  refine hn G ?_
  rintro ⟨g', hg'⟩
  refine hG ⟨e.toEmbedding.trans g', ?_⟩
  ext a b
  have hab : (H.comap e.symm.toEmbedding).Adj (e a) (e b) ↔ (G.comap g').Adj (e a) (e b) := by
    rw [hg']
  simpa using hab

theorem main : H1 → H2 → type_of% @Erdos61.erdos_61 := by
  intro h1 h2 α _ _ H
  let e := Fintype.equivFin α
  let H' : SimpleGraph (Fin (Fintype.card α)) := H.comap e.symm.toEmbedding
  suffices hs : ∃ c > (0 : ℝ), IsErdosHajnalLowerBound H' (fun n : ℕ => (n : ℝ) ^ c) by
    obtain ⟨c, hc, hb⟩ := hs
    exact ⟨c, hc, transport e H _ hb⟩
  by_cases ht : H' = ⊤
  · rw [ht]; exact (h1 _).1
  by_cases hb : H' = ⊥
  · rw [hb]; exact (h1 _).2
  exact h2 _ H' ht hb

end OMA.R_Erdos61_erdos_61_R1

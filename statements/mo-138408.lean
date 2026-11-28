import Mathlib

/-!
# Diameter bounds for the weighted feasible-subset intersection graph

Source: https://mathoverflow.net/questions/138408 (Robin Houston, CC BY-SA 3.0).
Credit: @connoranderson

A shortest path cannot use the same minimal threshold set to witness two of
its edges. Sperner's theorem then bounds every component diameter by the
middle binomial coefficient. A different bound is polynomial for a bounded
number of distinct weights: fix the target, partition each weight class
into target members and nonmembers, and record the occupancy of each part.
Equal occupancy profiles have equal distance to the target. We also give
a checked weighted example in which eight items require eight edges.

Ito and Demaine, "Approximability of the Subset Sum Reconfiguration Problem"
(2014), discuss the polynomial-diameter question for single-item moves.
Our unrestricted bound does not settle polynomial growth for arbitrary
weights. Single-item moves and the intersection edges here give the same
components, though their distances can differ.
-/

namespace OMA.S_mo_138408
open Finset SimpleGraph Function
noncomputable section

abbrev V (n : ℕ) := Finset (Fin n)
def weight {n : ℕ} (w : Fin n → ℕ) (s : V n) := ∑ i ∈ s, w i
def graph {n : ℕ} (w : Fin n → ℕ) (k c : ℕ) : SimpleGraph (V n) where
  Adj s t := s≠t ∧ weight w s≤c ∧ weight w t≤c ∧ k≤weight w (s∩t)
  symm := ⟨fun s t h => ⟨h.1.symm,h.2.2.1,h.2.1,by simpa [inter_comm t s] using h.2.2.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def bucket {n q : ℕ} (label : Fin n → Fin q) (t : V n) (b : Fin q × Bool) : V n :=
  univ.filter fun i => (label i, decide (i∈t))=b
def profileBound {n q : ℕ} (label : Fin n → Fin q) (t : V n) : ℕ :=
  ∏ b : Fin q × Bool, ((bucket label t b).card+1)

theorem main :
    (∀ n (w : Fin n → ℕ) k c (s t : V n),
      (graph w k c).dist s t ≤ n.choose (n/2)) ∧
    (∀ n q (label : Fin n → Fin q) (value : Fin q → ℕ) k c (s t : V n),
      (graph (value ∘ label) k c).dist s t < profileBound label t ∧
      profileBound label t ≤ (n+1)^(2*q)) ∧
    (∃ (w : Fin 8 → ℕ) (s t : V 8), (∀ i, 0 < w i) ∧
      (graph w 31 45).dist s t = 8) := by
  sorry
end
end OMA.S_mo_138408

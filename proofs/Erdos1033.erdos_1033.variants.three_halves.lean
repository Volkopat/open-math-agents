import FormalConjectures.ErdosProblems.«1033»

-- Problem: Erdős Problem 1033 — three halves
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1033.lean:70 (declaration Erdos1033.erdos_1033.variants.three_halves)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Finset

namespace OMA

def adj (u v : Fin 34) : Prop :=
  (u.val < 20 ∧ 20 ≤ v.val) ∨ (20 ≤ u.val ∧ v.val < 20) ∨
    (u.val < 20 ∧ v.val < 20 ∧ u.val / 2 = v.val / 2 ∧ u ≠ v)

instance : DecidableRel adj := fun u v => by unfold adj; infer_instance

def G : SimpleGraph (Fin 34) where
  Adj := adj
  symm := ⟨fun u v h => by unfold adj at *; omega⟩
  loopless := ⟨fun u h => by unfold adj at h; omega⟩

instance : DecidableRel G.Adj := fun u v => (inferInstance : Decidable (adj u v))

lemma deg_eq : ∀ v : Fin 34, G.degree v = if v.val < 20 then 15 else 20 := by
  decide +kernel

end OMA

theorem OMA.solution : type_of% @Erdos1033.erdos_1033.variants.three_halves := by
  intro h
  have hE : 34 ^ 2 < 4 * #OMA.G.edgeFinset := by
    have h2 := OMA.G.sum_degrees_eq_twice_card_edges
    simp only [OMA.deg_eq] at h2
    have : (∑ v : Fin 34, if v.val < 20 then 15 else 20) = 580 := by decide +kernel
    omega
  obtain ⟨t, ht, hs⟩ := h 34 OMA.G hE
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp ht.2
  have hc := ht.1
  have h1 : OMA.adj a b := hc (by simp) (by simp) hab
  have h2 : OMA.adj b c := hc (by simp) (by simp) hbc
  have h3 : OMA.adj a c := hc (by simp) (by simp) hac
  rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton, OMA.deg_eq, OMA.deg_eq, OMA.deg_eq] at hs
  -- Two vertices in the second part can never be adjacent.
  unfold OMA.adj at h1 h2 h3
  split at hs <;> split at hs <;> split at hs <;> omega

import OMAReductions.R_Erdos552_erdos_552_parts_ii_R2
import Mathlib

-- Step Erdos552.erdos_552.parts.ii.R2.H1: hypothesis H1 of reduction Erdos552.erdos_552.parts.ii.R2
-- Credit: @ivillar. In G on n + d vertices, deg_G(v) + deg_{G^c}(v) = n + d - 1, so a star K_{1,n}
-- centred at v sits in G^c exactly when v has at least n non-neighbours, i.e. deg_G(v) < d.

/-! Step Erdos552.erdos_552.parts.ii.R2.H1. -/

open SimpleGraph

namespace P8Erdos552

theorem star_iff : ∀ (n d : ℕ) (G : SimpleGraph (Fin (n+d))) [DecidableRel G.Adj],
    (completeBipartiteGraph (Fin 1) (Fin n)).IsContained Gᶜ ↔ ∃ v, G.degree v < d := by
  intro n d G _
  classical
  have hdeg : ∀ v, Gᶜ.degree v + G.degree v + 1 = n + d := by
    intro v
    have h1 := G.degree_compl (v := v)
    have h2 : G.degree v < n + d := by
      have := G.degree_lt_card_verts v
      simpa using this
    rw [Fintype.card_fin] at h1
    omega
  constructor
  · rintro ⟨f⟩
    refine ⟨f (Sum.inl 0), ?_⟩
    have hsub : (Finset.univ.image (fun i : Fin n => f (Sum.inr i))) ⊆
        Gᶜ.neighborFinset (f (Sum.inl 0)) := by
      intro w hw
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hw
      rw [mem_neighborFinset]
      have hadj : (completeBipartiteGraph (Fin 1) (Fin n)).Adj (Sum.inl 0) (Sum.inr i) := by
        simp [completeBipartiteGraph_adj]
      simpa using f.toHom.map_adj hadj
    have hinj : Function.Injective (fun i : Fin n => f (Sum.inr i)) := by
      intro a b h
      have := f.injective (by simpa using h)
      exact Sum.inr_injective this
    have hcard : (Finset.univ.image (fun i : Fin n => f (Sum.inr i))).card = n := by
      rw [Finset.card_image_of_injective _ hinj]
      simp
    have hle := Finset.card_le_card hsub
    rw [hcard, card_neighborFinset_eq_degree] at hle
    have := hdeg (f (Sum.inl 0))
    omega
  · rintro ⟨v, hv⟩
    have hge : n ≤ (Gᶜ.neighborFinset v).card := by
      rw [card_neighborFinset_eq_degree]
      have := hdeg v
      omega
    obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq hge
    let e : Fin n ≃ t := (t.equivFin.trans (finCongr htc)).symm
    have hmem : ∀ i, Gᶜ.Adj v (e i : Fin (n + d)) := fun i =>
      (mem_neighborFinset _ _ _).mp (ht (e i).2)
    let g : Fin 1 ⊕ Fin n → Fin (n + d) := Sum.elim (fun _ => v) (fun i => (e i : Fin (n + d)))
    have hg_adj : ∀ a b, (completeBipartiteGraph (Fin 1) (Fin n)).Adj a b → Gᶜ.Adj (g a) (g b) := by
      intro a b hab
      rcases a with a | a <;> rcases b with b | b
      · simp [completeBipartiteGraph_adj] at hab
      · exact hmem b
      · exact (hmem a).symm
      · simp [completeBipartiteGraph_adj] at hab
    have hg_inj : Function.Injective g := by
      intro a b hab
      rcases a with a | a <;> rcases b with b | b
      · simp [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]
      · exact absurd hab (hmem b).ne
      · exact absurd hab.symm (hmem a).ne
      · have : (e a : Fin (n + d)) = e b := hab
        exact congrArg Sum.inr (e.injective (Subtype.ext this))
    exact ⟨⟨⟨g, fun {a b} h => hg_adj a b h⟩, hg_inj⟩⟩

end P8Erdos552

theorem OMA.solution : OMA.R_Erdos552_erdos_552_parts_ii_R2.H1 :=
  P8Erdos552.star_iff

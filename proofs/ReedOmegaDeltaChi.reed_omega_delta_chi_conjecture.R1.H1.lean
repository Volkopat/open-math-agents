import OMAReductions.R_ReedOmegaDeltaChi_reed_omega_delta_chi_conjecture_R1
import Mathlib

/-! Step ReedOmegaDeltaChi.reed_omega_delta_chi_conjecture.R1.H1 (the case `Δ ≤ ω`). If `Δ = ⊤`
then `ω = ⊤` and the bound is trivial. Otherwise greedy colouring along a well order of the
vertices (`WellFounded.fix` on `WellOrderingRel`, which works for infinite graphs too) uses at most
`Δ + 1` colours, and `2(Δ + 1) ≤ ω + Δ + 2`. -/

namespace OMA.ReedH1

open SimpleGraph

variable {V : Type} (G : SimpleGraph V)

/-- Colours used by earlier neighbours (along a well order `r`). -/
def forb (r : V → V → Prop) (v : V) (rec : ∀ w, r w v → ℕ) : Set ℕ :=
  {n | ∃ w, ∃ hw : r w v, G.Adj v w ∧ rec w hw = n}

/-- Greedy colouring along the well order `WellOrderingRel`. -/
noncomputable def col : V → ℕ :=
  (WellOrderingRel.isWellOrder (α := V)).wf.fix
    (fun v rec => sInf (forb G WellOrderingRel v rec)ᶜ)

lemma col_eq (v : V) : col G v =
    sInf {n | ∃ w, ∃ _ : WellOrderingRel w v, G.Adj v w ∧ col G w = n}ᶜ := by
  unfold col
  rw [WellFounded.fix_eq]
  rfl

theorem colorable (D : ℕ) (hD : ∀ v, (G.neighborSet v).encard ≤ D) : G.Colorable (D + 1) := by
  classical
  have hF : ∀ v, {n | ∃ w, ∃ _ : WellOrderingRel w v, G.Adj v w ∧ col G w = n} ⊆
      col G '' G.neighborSet v := by
    rintro v n ⟨w, -, hw, rfl⟩
    exact ⟨w, hw, rfl⟩
  have hfin : ∀ v, (col G '' G.neighborSet v).Finite := fun v =>
    (Set.finite_of_encard_le_coe (hD v)).image _
  have hne : ∀ v, ({n | ∃ w, ∃ _ : WellOrderingRel w v, G.Adj v w ∧ col G w = n}ᶜ).Nonempty :=
    fun v => ((hfin v).subset (hF v)).infinite_compl.nonempty
  have hmem : ∀ v, col G v ∉ {n | ∃ w, ∃ _ : WellOrderingRel w v, G.Adj v w ∧ col G w = n} :=
    fun v => by rw [col_eq]; exact Nat.sInf_mem (hne v)
  have hle : ∀ v, col G v ≤ D := by
    intro v
    by_contra hlt
    push Not at hlt
    have hsub : (Finset.range (D + 1) : Set ℕ) ⊆ col G '' G.neighborSet v := by
      intro n hn
      have hn' : n < col G v := by simp at hn; omega
      apply hF v
      by_contra hc
      have := Nat.sInf_le (show n ∈ {n | ∃ w, ∃ _ : WellOrderingRel w v, G.Adj v w ∧
        col G w = n}ᶜ from hc)
      rw [← col_eq] at this
      omega
    have h1 := Set.encard_le_encard hsub
    have h2 := (Set.encard_image_le (col G) (G.neighborSet v)).trans (hD v)
    rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_range] at h1
    have := h1.trans h2
    norm_cast at this
    omega
  refine ⟨Coloring.mk (fun v => (⟨col G v, by have := hle v; omega⟩ : Fin (D + 1))) ?_⟩
  intro v w hvw heq
  simp only [Fin.mk.injEq] at heq
  by_cases h : WellOrderingRel w v
  · exact hmem v ⟨w, h, hvw, heq.symm⟩
  by_cases h' : WellOrderingRel v w
  · exact hmem w ⟨v, h', hvw.symm, heq⟩
  have := (WellOrderingRel.isWellOrder (α := V)).trichotomous w v h h'
  exact G.loopless.irrefl _ (this ▸ hvw)

theorem main (hΔ : G.emaxDegree ≤ G.ecliqueNum) :
    2 * G.chromaticNumber ≤ G.ecliqueNum + G.emaxDegree + 2 := by
  rcases eq_top_or_lt_top G.emaxDegree with htop | hlt
  · rw [htop, top_le_iff] at hΔ
    rw [hΔ, htop]; simp
  · obtain ⟨D, hD⟩ : ∃ D : ℕ, G.emaxDegree = D := ENat.ne_top_iff_exists.1 hlt.ne |>.imp
      fun _ h => h.symm
    have hdeg : ∀ v, (G.neighborSet v).encard ≤ D := fun v => by
      rw [← hD]; exact le_iSup (fun v => G.edegree v) v
    have hχ : G.chromaticNumber ≤ (D + 1 : ℕ) := (colorable G D hdeg).chromaticNumber_le
    rw [hD] at hΔ ⊢
    calc 2 * G.chromaticNumber ≤ 2 * ((D + 1 : ℕ) : ℕ∞) := by gcongr
      _ = (D : ℕ∞) + D + 2 := by push_cast; ring
      _ ≤ G.ecliqueNum + D + 2 := by gcongr

end OMA.ReedH1

theorem OMA.solution : OMA.R_ReedOmegaDeltaChi_reed_omega_delta_chi_conjecture_R1.H1 :=
  fun G h => OMA.ReedH1.main G h

import FormalConjectures.Paper.HallRatioConjecture

open Finset

-- Problem: The Hall ratio is a lower bound for the fractional chromatic number.
-- Upstream: formal-conjectures FormalConjectures/Paper/HallRatioConjecture.lean:72 (declaration HallRatioConjecture.hall_ratio_conjecture.variants.hallRatio_le_fractionalChromaticNumber)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Original proof: @LordMike, PR #489; prior shortening: @kanato1ili, PR #23648.

namespace OMA

open SimpleGraph

lemma inter_card_le {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (S I : Finset V) (hI : G.IsIndepSet (I : Set V)) :
    (I.filter (fun v => v ∈ S)).card ≤ (G.induce (S : Set V)).indepNum := by
  classical
  rw [← card_subtype]
  apply IsIndepSet.card_le_indepNum
  intro x hx y hy hxy
  simp only [mem_coe, mem_subtype] at hx hy
  have := hI (mem_coe.mpr hx) (mem_coe.mpr hy) (fun h => hxy (Subtype.ext h))
  simpa using this

lemma key {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (w : Finset V → ℝ) (hw : G.IsFractionalColoring w) :
    (S.card : ℝ) ≤ (∑ I, w I) * ((G.induce (S : Set V)).indepNum : ℝ) := by
  classical
  set α := (G.induce (S : Set V)).indepNum
  calc (S.card : ℝ) = ∑ v ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ v ∈ S, ∑ I ∈ (univ : Finset (Finset V)).filter (fun I => v ∈ I), w I :=
        sum_le_sum fun v _ => hw.cover v
    _ = ∑ v ∈ S, ∑ I, if v ∈ I then w I else 0 := by
        simp only [sum_filter]
    _ = ∑ I, ∑ v ∈ S, if v ∈ I then w I else 0 := sum_comm
    _ = ∑ I, w I * ((I.filter (fun v => v ∈ S)).card : ℝ) := by
        refine sum_congr rfl fun I _ => ?_
        rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
        congr 3
        ext v; simp [and_comm]
    _ ≤ ∑ I, w I * (α : ℝ) := by
        refine sum_le_sum fun I _ => ?_
        by_cases h : w I = 0
        · simp [h]
        · exact mul_le_mul_of_nonneg_left (by exact_mod_cast inter_card_le G S I (hw.indep I h))
            (hw.nonneg I)
    _ = (∑ I, w I) * (α : ℝ) := by rw [sum_mul]

end OMA

theorem OMA.solution : type_of% @HallRatioConjecture.hall_ratio_conjecture.variants.hallRatio_le_fractionalChromaticNumber := by
  intro V _ _ G
  unfold HallRatioConjecture.hallRatio
  apply Real.sSup_le _ G.fractionalChromaticNumber_nonneg
  rintro r ⟨S, hS, rfl⟩
  apply le_csInf G.fractionalColoringWeights_nonempty
  rintro t ⟨w, hw, rfl⟩
  exact div_le_of_le_mul₀ (by positivity) (sum_nonneg fun I _ => hw.nonneg I)
    (OMA.key G S w hw)

import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R1

/-! Union bound: `|S| ≤ |⋃ B i| ≤ ∑ |B i| ≤ q * r 3 N`, since each `B i` is a 3-AP-free subset of `[1, N]`
(`card_le_maxCard` from the merged reduction `Erdos142.erdos_142.variants.lower.R2`). -/

open Erdos142 in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R1.H2 := by
  intro N q S B hS hB
  calc S.card ≤ (Finset.univ.biUnion B).card := Finset.card_le_card hS
    _ ≤ ∑ i, (B i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin q, r 3 N := Finset.sum_le_sum fun i _ =>
        OMA.R_Erdos142_erdos_142_variants_lower_R2.card_le_maxCard (hB i).1 (hB i).2
    _ = q * r 3 N := by simp

import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R3

/-! Subadditivity twice: `r k (4N) ≤ r k (2N) + r k (2N) ≤ 4 r k N`, using `maxCard_add_le` from the merged
reduction `Erdos142.erdos_142.variants.lower.R2`. -/

open Erdos142 in
theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H3_R3.H1 := by
  intro k _ N
  have h1 := OMA.R_Erdos142_erdos_142_variants_lower_R2.maxCard_add_le k (2 * N) (2 * N)
  have h2 := OMA.R_Erdos142_erdos_142_variants_lower_R2.maxCard_add_le k N N
  have h1' : Set.IsAPOfLengthFree.maxCard k (4 * N) ≤
      Set.IsAPOfLengthFree.maxCard k (2 * N) + Set.IsAPOfLengthFree.maxCard k (2 * N) := by
    rw [show 4 * N = 2 * N + 2 * N by ring]; exact h1
  have h2' : Set.IsAPOfLengthFree.maxCard k (2 * N) ≤
      Set.IsAPOfLengthFree.maxCard k N + Set.IsAPOfLengthFree.maxCard k N := by
    rw [show 2 * N = N + N by ring]; exact h2
  show Set.IsAPOfLengthFree.maxCard k (4 * N) ≤ 4 * Set.IsAPOfLengthFree.maxCard k N
  omega

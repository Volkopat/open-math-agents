import OMAReductions.R_Erdos687_erdos_687_parts_iii_R2

/-! Reduction of step H1 of `Erdos687.erdos_687.parts.iii.R2`.

The step asks that along arbitrarily large scales `j` the residue classes up to
`2 * 2^(4j)` fail to cover `[1, 2^(6j)]`. The open core asks the same question about
the extremal cover length `Erdos687.Y`: at those scales `Y (2 * 2^(4j)) < 2^(6j)`.
The upstream-proved bridge `covered_le_max` converts any purported cover into the
inequality `K ≤ Y w`, contradicting the open core. -/

namespace OMA.R_Erdos687_erdos_687_parts_iii_R2_H1_R1

open Filter

/-- Open core: the maximal cover length stays below the cubic scale along a tail. -/
def H1 : Prop :=
  ∀ J : ℕ, ∃ j ≥ J, Erdos687.Y (2 * 2 ^ (4 * j)) < 2 ^ (6 * j)

/-- Upstream-proved bridge: the length of any cover by residues up to `w` is at most
the extremal cover length `Y w`. -/
def H2 : Prop :=
  ∀ {w K : ℕ}, Green46.IsCoveredByResidues w K → K ≤ Erdos687.Y w

theorem main : H1 → H2 → OMA.R_Erdos687_erdos_687_parts_iii_R2.H1 := by
  intro hcore hbridge J
  obtain ⟨j, hjJ, hjY⟩ := hcore J
  refine ⟨j, hjJ, ?_⟩
  intro hc
  exact (not_le_of_gt hjY) (hbridge hc)

end OMA.R_Erdos687_erdos_687_parts_iii_R2_H1_R1

import OMAStatements.S_oeis_a003075

namespace OMA.R_oeis_a003075_R1

open OMA.S_oeis_a003075

/-- Upper bounds from the published comparator networks. -/
def H1 : Prop :=
  minSize 13 ≤ 45 ∧ minSize 14 ≤ 51 ∧ minSize 15 ≤ 56 ∧ minSize 16 ≤ 60

/-- The corresponding optimality bounds. -/
def H2 : Prop :=
  45 ≤ minSize 13 ∧ 51 ≤ minSize 14 ∧ 56 ≤ minSize 15 ∧ 60 ≤ minSize 16

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a003075.main := by
  rintro ⟨u13, u14, u15, u16⟩ ⟨l13, l14, l15, l16⟩
  exact ⟨le_antisymm u13 l13, le_antisymm u14 l14, le_antisymm u15 l15, le_antisymm u16 l16⟩

end OMA.R_oeis_a003075_R1

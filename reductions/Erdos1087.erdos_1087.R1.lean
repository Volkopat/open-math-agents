import FormalConjectures.ErdosProblems.«1087»
/-! Erdős 1087 split at exponent one half.

The classical Erdős–Purdy bound (1971) gives `f n ≪ n ^ (7 / 2)`, which settles every exponent
`3 + ε` with `ε ≥ 1 / 2` (H1). The open part of the problem is the range `0 < ε < 1 / 2` (H2).
This is a classical case, not progress on the conjecture. -/
namespace OMA.R_Erdos1087_erdos_1087_R1
open Filter Asymptotics Erdos1087

/-- Erdős–Purdy range: the degenerate quadruple count is `O(n ^ (3 + ε))` for every `ε ≥ 1 / 2`. -/
def H1 : Prop := ∀ ε : ℝ, 1 / 2 ≤ ε →
  (fun n : ℕ ↦ (f n : ℝ)) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (3 + ε)

/-- The open range `0 < ε < 1 / 2`. -/
def H2 : Prop := ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
  (fun n : ℕ ↦ (f n : ℝ)) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (3 + ε)

theorem main : H1 → H2 → type_of% @Erdos1087.erdos_1087 := by
  intro h₁ h₂ ε hε
  by_cases h : ε < 1 / 2
  · exact h₂ ε hε h
  · exact h₁ ε (not_lt.1 h)

end OMA.R_Erdos1087_erdos_1087_R1

import FormalConjectures.ErdosProblems.«1109»
/-! Erdős 1109 split at exponent three quarters.

The classical Erdős–Sárközy bound (1987) `f N ≪ N ^ (3 / 4) * log N` settles every exponent
`ε > 3 / 4` (H1). The open part of the problem is the range `0 < ε ≤ 3 / 4` (H2).
This is a classical case, not progress on the conjecture. -/
namespace OMA.R_Erdos1109_erdos_1109_R1
open Filter Asymptotics Erdos1109

/-- Erdős–Sárközy range: `f N ≪ N ^ ε` for every `ε > 3 / 4`. -/
def H1 : Prop := ∀ ε : ℝ, 3 / 4 < ε →
  (fun N : ℕ => (f N : ℝ)) ≪ fun N : ℕ => (N : ℝ) ^ ε

/-- The open range `0 < ε ≤ 3 / 4`. -/
def H2 : Prop := ∀ ε : ℝ, 0 < ε → ε ≤ 3 / 4 →
  (fun N : ℕ => (f N : ℝ)) ≪ fun N : ℕ => (N : ℝ) ^ ε

theorem main : H1 → H2 → type_of% @Erdos1109.erdos_1109 := by
  intro h₁ h₂ ε hε
  by_cases h : ε ≤ 3 / 4
  · exact h₂ ε hε h
  · exact h₁ ε (not_le.1 h)

end OMA.R_Erdos1109_erdos_1109_R1

import FormalConjectures.ErdosProblems.«1201»
/-! Erdős 1201 split at exponent one half.

Erdős proved the statement for `ε = 1 / 2`, and the set `Erdos1201Set ε k` only grows with `ε`,
so every `ε ≥ 1 / 2` follows (H1). The open part of the problem is the range `0 < ε < 1 / 2` (H2).
This is a classical case, not progress on the conjecture. -/
namespace OMA.R_Erdos1201_erdos_1201_R1
open Filter Erdos1201 Nat

open scoped Classical in
/-- Erdős's range: the statement for every `ε ≥ 1 / 2`. -/
def H1 : Prop := ∀ ε : ℝ, 1 / 2 ≤ ε → ∀ η > 0, ∃ k : ℕ,
      atTop.liminf (fun x : ℕ ↦
        (((count (· ∈ Erdos1201Set ε k) x : ℝ) / (x : ℝ)) : EReal)) ≥ (1 - η : EReal)

open scoped Classical in
/-- The open range `0 < ε < 1 / 2`. -/
def H2 : Prop := ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ η > 0, ∃ k : ℕ,
      atTop.liminf (fun x : ℕ ↦
        (((count (· ∈ Erdos1201Set ε k) x : ℝ) / (x : ℝ)) : EReal)) ≥ (1 - η : EReal)

theorem main : H1 → H2 → type_of% @Erdos1201.erdos_1201 := by
  intro h₁ h₂ ε hε
  by_cases h : ε < 1 / 2
  · exact h₂ ε hε h
  · exact h₁ ε (not_lt.1 h)

end OMA.R_Erdos1201_erdos_1201_R1

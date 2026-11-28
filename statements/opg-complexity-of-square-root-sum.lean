import Mathlib

namespace OMA.S_opg_complexity_of_square_root_sum

/-- One binary natural followed by a separator. The separator also delimits zero. -/
def encodeNumber (n : ℕ) : List Computability.Γ' :=
  (Computability.encodeNat n).map Computability.Γ'.bit ++ [.comma]

/-- The binary input represents the threshold followed by the list of radicands. -/
def encodeInstance (input : ℕ × List ℕ) : List Computability.Γ' :=
  encodeNumber input.1 ++ input.2.flatMap encodeNumber

/-- Exact comparison of a finite sum of square roots with its integer threshold. -/
def BelowThreshold (input : ℕ × List ℕ) : Prop :=
  (input.2.map fun a => Real.sqrt (a : ℝ)).sum ≤ (input.1 : ℝ)

/-- Open Problem Garden asks about exact square-root sum comparison.
This is its polynomial-time question in the binary Turing model. -/
theorem main :
    ∃ answer : ℕ × List ℕ → Bool,
      (∀ input, answer input = true ↔ BelowThreshold input) ∧
      Nonempty
        (Turing.TM2ComputableInPolyTime encodeInstance (fun b : Bool => [b]) answer) := by
  sorry

end OMA.S_opg_complexity_of_square_root_sum

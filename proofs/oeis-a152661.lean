import OMAStatements.S_oeis_a152661
import Mathlib

open OMA.S_oeis_a152661 in
theorem OMA.solution : type_of% @OMA.S_oeis_a152661.main := by
  have h : ∀ j k, (2 * j + k) / 2 = j + k / 2 := by omega
  constructor <;> intro t <;> obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' t <;>
    simp [sameParity, evenOddPairs, add_assoc, h, Nat.add_sub_assoc, Nat.factorial] <;> push_cast <;> ring

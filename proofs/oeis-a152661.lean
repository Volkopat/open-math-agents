import OMAStatements.S_oeis_a152661
import Mathlib

open OMA.S_oeis_a152661 in
theorem OMA.solution : type_of% @OMA.S_oeis_a152661.main := by
  constructor <;> intro t <;> obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' t <;>
  simp [sameParity, evenOddPairs, add_assoc, show ∀ c, (2*i+c)/2 = i+c/2 by omega,
    Nat.factorial_succ] <;> ring

import Mathlib

/-!
# Mathematics Stack Exchange 4989540

Source: https://math.stackexchange.com/questions/4989540
-/

namespace OMA.S_mse_4989540

open Set Finset

def FiniteCosetUnion (S : Set ℤ) : Prop :=
  ∃ C : Finset (ℤ × ℤ), (∀ c ∈ C, c.2 ≠ 0) ∧
    S = {x | ∃ c ∈ C, c.2 ∣ x-c.1}

def ArbitraryCosetUnion (S : Set ℤ) : Prop :=
  ∃ C : Set (ℤ × ℤ), (∀ c ∈ C, c.2 ≠ 0) ∧
    S = {x | ∃ c ∈ C, c.2 ∣ x-c.1}

theorem main : ∃ S : ℕ → Set ℤ, StrictMono S ∧
      (∀ n, FiniteCosetUnion (S n)) ∧ (∀ n, ArbitraryCosetUnion (S n)) := by
  sorry

end OMA.S_mse_4989540

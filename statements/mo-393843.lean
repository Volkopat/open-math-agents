import Mathlib

/-!
# MathOverflow 393843

Source: https://mathoverflow.net/questions/393843
-/

namespace OMA.S_mo_393843

open Polynomial Set
open scoped NNReal

def HasHeightAtMost (f : ℤ[X]) (H : ℕ) : Prop :=
  ∀ i : ℕ, (f.coeff i).natAbs ≤ H

def boundedHeightFactors (degreeBound heightBound : ℕ) : Set ℤ[X] :=
  {g | g.natDegree = degreeBound ∧
    ∃ f : ℤ[X], f ≠ 0 ∧ HasHeightAtMost f heightBound ∧ g ∣ f}

theorem main : ∀ d H : ℕ, (boundedHeightFactors d H).Finite ∧
    ∀ g ∈ boundedHeightFactors d H, HasHeightAtMost g (H*(H+1)^d*2^d) := by
  sorry

end OMA.S_mo_393843

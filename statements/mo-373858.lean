import Mathlib

/-!
# Condition number of the factorially scaled Hilbert matrix

Source: https://mathoverflow.net/questions/373858 (Abhishek Halder, CC BY-SA 4.0).
Credit: @connoranderson

Reverse the coordinates and write n=m+1. The entries then become
1/(i! j! (i+j+1)) for 0≤i,j≤m. For a positive definite real matrix the
Euclidean condition number is the supremum of the quotient of two Rayleigh
quotients. Only the first m+1 coordinates of the vectors are used here.
The bounds determine the growth to within an absolute factor for every m.
We derive the diagonal inverse bounds directly by elimination. Halder also
gave the full inverse separately at https://mathoverflow.net/questions/370119.
-/

namespace OMA.S_mo_373858
open Finset
noncomputable section

def energy (m : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range (m+1), ∑ j ∈ range (m+1),
    ((x i / i.factorial) * (x j / j.factorial)) / ((i:ℝ)+j+1)

def lengthSq (m : ℕ) (x : ℕ → ℝ) : ℝ := ∑ i ∈ range (m+1), (x i)^2

def cond₂ (m : ℕ) : ℝ :=
  sSup {r | ∃ x y : ℕ → ℝ, 0 < lengthSq m x ∧ 0 < lengthSq m y ∧
    r = (energy m x * lengthSq m y)/(lengthSq m x * energy m y)}

def scale (m : ℕ) : ℝ := (2*(m:ℝ)+1)*(((2*m).factorial:ℝ)/m.factorial)^2

theorem main : ∀ m : ℕ,
    (∀ x, 0 < lengthSq m x → 0 < energy m x) ∧
    scale m ≤ cond₂ m ∧ cond₂ m ≤ 12 * scale m := by
  sorry
end
end OMA.S_mo_373858

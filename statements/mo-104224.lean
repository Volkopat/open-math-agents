import Mathlib

/-!
# A continuous two-valued correspondence with no continuous selection

Source: Brian Lins, https://mathoverflow.net/questions/104224 (CC BY-SA).
The counterexample on the unit circle is the inverse of the double covering
by squaring. Hausdorff distance uses the ambient Euclidean chordal metric.
Credit: @connoranderson.
-/
namespace OMA.S_mo_104224

def roots (x : Circle) : Set Circle := {z | z^2=x}

theorem main : (∀ x : Circle, ∃ u : Circle, roots x = {u,-u} ∧ u ≠ -u) ∧
    UpperHemicontinuous roots ∧ LowerHemicontinuous roots ∧
    (∀ x y : Circle, Metric.hausdorffDist (roots x) (roots y) ≤ dist x y / Real.sqrt 2) ∧
    ¬ ∃ g : Circle → Circle, Continuous g ∧ ∀ x, g x ∈ roots x := by
  sorry
end OMA.S_mo_104224

import Mathlib

/-!
# Pólya's cone-area inequality

Source: Sergei, https://mathoverflow.net/questions/442224 (CC BY-SA 4.0),
citing problem 230 of the 1957 Otto Dunkel Memorial Problem Book.
The first assertion is the stated graph inequality, with the common factor π
cancelled. The second gives the requested two-function generalization. Its
last hypothesis means that the slope from the origin does not decrease.
Credit: @connoranderson.
-/

namespace OMA.S_mo_442224
open Set

def regular (a : ℝ) (x v : ℝ → ℝ) : Prop :=
  ContinuousOn x (Icc 0 a) ∧ ContinuousOn v (Icc 0 a) ∧
    ∀ t ∈ Ioo 0 a, HasDerivAt x (v t) t

theorem main :
    (∀ (a b : ℝ) (f p q : ℝ → ℝ), 0<a → 0<b → f 0=0 → f a=b →
      regular a f p → (∀ t ∈ Icc 0 a, 0≤f t) →
      (∀ t ∈ Ioo 0 a, HasDerivAt p (q t) t ∧ 0≤q t) →
      2*(∫ t in (0:ℝ)..a, f t * Real.sqrt (1+(p t)^2)) ≤ b * Real.sqrt (a^2+b^2)) ∧
    (∀ (a : ℝ) (x y v w : ℝ → ℝ), 0<a → x 0=0 → y 0=0 →
      regular a x v → regular a y w →
      (∀ t ∈ Ioo 0 a, 0<x t ∧ 0≤y t ∧ 0≤v t ∧ y t*v t ≤ x t*w t) →
      2*(∫ t in (0:ℝ)..a, y t * Real.sqrt ((v t)^2+(w t)^2)) ≤
        y a * Real.sqrt ((x a)^2+(y a)^2)) := by
  sorry

end OMA.S_mo_442224

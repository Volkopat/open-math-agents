import Mathlib

/-!
# Fatou conjecture

Source: https://en.wikipedia.org/wiki/Fatou_conjecture
Credit: @hermitokatt

The source: "the Fatou conjecture states that a quadratic family of maps from the complex plane
to itself is hyperbolic for an open dense set of parameters."

Reading. The quadratic family is the standard one, `f_c (z) = z ^ 2 + c` with parameter `c : ℂ`
(every quadratic polynomial is affinely conjugate to exactly one such map, and conjugacy
preserves hyperbolicity). A polynomial is *hyperbolic* when every critical point in `ℂ` is
attracted to an attracting cycle, the point at infinity counting as a superattracting fixed point.
The only critical point of `f_c` in `ℂ` is `0`, so `f_c` is hyperbolic exactly when

* the orbit of `0` escapes to infinity (that is, `c` lies outside the Mandelbrot set), or
* the orbit of `0` converges to an attracting cycle: a cycle `z, f_c z, …, f_c^[p - 1] z` with
  `p > 0` and multiplier `‖(f_c^[p])' z‖ < 1` (superattracting cycles, multiplier `0`, included).
  "Converges to the cycle" is stated as: some subsequence `f_c^[j + p * k] 0` tends to `z`.

By Fatou's theorem every attracting cycle of `f_c` in `ℂ` attracts `0`, so the second clause is
equivalent to "`f_c` has an attracting cycle". Openness of the hyperbolic set is classical; the
open part of the conjecture is density. The statement keeps both, as the source does.
This is the same problem as `Mandelbrot.density_of_hyperbolicity` in formal-conjectures, stated
here over the whole parameter plane, as the source phrases it.
-/

namespace OMA.S_wp_fatou_conjecture

open Filter Topology Bornology

/-- The quadratic family `z ↦ z ^ 2 + c`. -/
def quadMap (c : ℂ) : ℂ → ℂ := fun z => z ^ 2 + c

/-- `z` lies on an attracting cycle of period `p` of `f`: `p > 0`, `f^[p] z = z`, and the
multiplier `(f^[p])' z` has norm `< 1`. -/
def IsAttractingCycle (f : ℂ → ℂ) (p : ℕ) (z : ℂ) : Prop :=
  0 < p ∧ f^[p] z = z ∧ DifferentiableAt ℂ f^[p] z ∧ ‖deriv f^[p] z‖ < 1

/-- `z ↦ z ^ 2 + c` is hyperbolic: its critical point `0` escapes to infinity or converges to an
attracting cycle. -/
def IsHyperbolicParam (c : ℂ) : Prop :=
  Tendsto (fun k => (quadMap c)^[k] 0) atTop (cobounded ℂ) ∨
    ∃ p z, IsAttractingCycle (quadMap c) p z ∧
      ∃ j, Tendsto (fun k => (quadMap c)^[j + p * k] 0) atTop (𝓝 z)

/-- Fatou conjecture: the parameters `c` for which `z ↦ z ^ 2 + c` is hyperbolic form an open
dense subset of `ℂ`. -/
theorem main : IsOpen {c : ℂ | IsHyperbolicParam c} ∧ Dense {c : ℂ | IsHyperbolicParam c} := by
  sorry

end OMA.S_wp_fatou_conjecture

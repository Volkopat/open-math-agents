import Mathlib

/-!
# Does there exist a compactly supported integrable function with infinite Coulomb energy?

Source: https://mathoverflow.net/questions/326993
Credit: @artnoage

The source asks for a function `f ∈ L¹(Ω)`, where `Ω ⊂ ℝ³` is a bounded domain, such that
the Coulomb energy `∬_{Ω×Ω} f(x) f(y) / |x - y| dx dy` is infinite, and adds that it suffices
to take `f ≥ 0`.

Choices made here:

* `ℝ³` is `EuclideanSpace ℝ (Fin 3)` with Lebesgue measure; a bounded domain is an open,
  connected (hence nonempty), bounded set.
* The source does not say which domain. The statement is the stronger reading: such a
  function exists on every bounded domain.
* `f` is taken nonnegative, as the source allows, so the energy is an unambiguous integral
  with values in `[0, ∞]`; it is written as an iterated lower Lebesgue integral. The integrand
  at `x = y` (where Lean's division gives `0`) is on a null set and does not matter.
-/

namespace OMA.S_mo_326993

open MeasureTheory

theorem main :
    ∀ Ω : Set (EuclideanSpace ℝ (Fin 3)), IsOpen Ω → IsConnected Ω → Bornology.IsBounded Ω →
      ∃ f : EuclideanSpace ℝ (Fin 3) → ℝ, (∀ x, 0 ≤ f x) ∧ IntegrableOn f Ω ∧
        ∫⁻ x in Ω, ∫⁻ y in Ω, ENNReal.ofReal (f x * f y / ‖x - y‖) = ⊤ := by
  sorry

end OMA.S_mo_326993

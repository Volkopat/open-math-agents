import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_mo_431075

open Filter
open scoped BigOperators

/-- A formal power series is rational when a polynomial denominator that is
invertible at zero turns it into a polynomial. -/
def IsRational (f : PowerSeries ℚ) : Prop :=
  ∃ p q : Polynomial ℚ, q.coeff 0 ≠ 0 ∧ (q : PowerSeries ℚ) * f = (p : PowerSeries ℚ)

/-- The first n factors, with exponents from the given sequence starting at index one. -/
noncomputable def partialProduct (G : ℕ → ℕ) (r n : ℕ) : Polynomial ℕ :=
  ∏ i ∈ Finset.range n,
    ∑ j ∈ Finset.range (r + 1), (Polynomial.X : Polynomial ℕ) ^ (j * G (i + 1))

/-- The number of coefficients of the partial product equal to the positive target k. -/
noncomputable def coefficientCount (G : ℕ → ℕ) (r k n : ℕ) : ℕ :=
  let p := partialProduct G r n
  (p.support.filter (fun j => p.coeff j = k)).card

/-- The coefficient counts have a rational generating function when the positive
exponent sequence tends to infinity and has a rational generating function. -/
theorem main :
    ∀ G : ℕ → ℕ, (∀ n, 0 < n → 0 < G n) →
      Tendsto G atTop atTop →
      IsRational (PowerSeries.mk (fun n => if n = 0 then 0 else (G n : ℚ))) →
      ∀ r k : ℕ, 0 < r → 0 < k →
        IsRational (PowerSeries.mk (fun n => (coefficientCount G r k n : ℚ))) := by
  sorry

end OMA.S_mo_431075

import Mathlib

/-!
# Total mass from the positive moments on [-1,1]

Source: zoidberg, https://mathoverflow.net/questions/319396 (CC BY-SA 4.0).
Credit: @connoranderson.

The measure lives on the interval as a subtype. The moment integrability
hypothesis expresses that each given positive moment is a finite Lebesgue
integral. The formula gives the total mass from the atom at zero and a series
using only positive even moments. An explicit finite/infinite pair shows
that the atom at zero must be considered separately.
-/

namespace OMA.S_mo_319396

open MeasureTheory Set
open scoped ENNReal

abbrev I := Set.Icc (-1:ℝ) 1
def origin : I := ⟨0, by norm_num [Set.mem_Icc]⟩
noncomputable def moment (μ : Measure I) (n : ℕ) := ∫ x : I, (x.val)^n ∂μ
noncomputable def term (m : ℕ → ℝ) (j : ℕ) :=
  ∑ i ∈ Finset.range (j+1), (-1:ℝ)^i * (j.choose i : ℝ) * m (2*i+2)

theorem main :
    (∀ μ : Measure I, (∀ n : ℕ, 0<n → Integrable (fun x:I => x.val^n) μ) →
      μ univ = μ {origin} + ∑' j : ℕ, ENNReal.ofReal (term (moment μ) j)) ∧
    (∃ μ ν : Measure I, μ univ = 1 ∧ ν univ = ⊤ ∧ ∀ n : ℕ, 0<n →
      Integrable (fun x : I => x.val^n) μ ∧ Integrable (fun x : I => x.val^n) ν ∧
      moment μ n = moment ν n) := by
  sorry

end OMA.S_mo_319396

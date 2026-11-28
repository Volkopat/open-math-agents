import Mathlib

/-!
# How much can an independent perturbation shrink the sample maximum?

For two independent i.i.d. samples of size N = n+1, the supremum norm means the
largest absolute observation. We treat the event with the inequality printed
in the question, and the reverse-tail interpretation of its verbal conjecture.
Under only centered unit second moments the latter has worst-case probability
of order min(1,N/t²)/(1+t²) for t ≥ 1. A single symmetric law also exhibits a
polynomial lower bound at infinitely many thresholds when N = 1.

Source: gappy3000, https://mathoverflow.net/questions/220800 (CC BY-SA 3.0).
Fedor Petrov noted the sign issue and Carlo Beenakker anticipated polynomial tails.
Credit: @connoranderson (agent: Codex)
-/
namespace OMA.S_mo_220800
open MeasureTheory
abbrev Arr (n : ℕ) := Fin (n+1) → ℝ
def standard (μ : Measure ℝ) : Prop := IsProbabilityMeasure μ ∧ Integrable id μ ∧
  Integrable (fun x : ℝ => x^2) μ ∧ (∫ x, x ∂μ)=0 ∧ (∫ x, x^2 ∂μ)=1
noncomputable def sample (n : ℕ) (μ : Measure ℝ) : Measure (Arr n) :=
  Measure.pi (fun _ => μ)
noncomputable def dropProb (μ ν : Measure ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ((sample n μ).prod (sample n ν)).real {v | ‖v.1+v.2‖+t ≤ ‖v.1‖}
noncomputable def rate (n : ℕ) (t : ℝ) : ℝ := min 1 ((n+1:ℝ)/t^2)/(1+t^2)
noncomputable def oneDrop (μ : Measure ℝ) (t : ℝ) : ℝ :=
  (μ.prod μ).real {v | |v.1+v.2|+t ≤ |v.1|}
theorem main :
    (∃ μ : Measure ℝ, standard μ ∧ ∀ c : ℝ, 0<c →
      Real.exp (-c) < (μ.prod μ).real {v | |v.1| ≤ |v.1+v.2|+1}) ∧
    (∀ n (t : ℝ), 1 ≤ t →
      (∀ μ ν : Measure ℝ, standard μ → standard ν → dropProb μ ν n t ≤ 2*rate n t) ∧
      (∃ μ ν : Measure ℝ, standard μ ∧ standard ν ∧ rate n t/24 ≤ dropProb μ ν n t)) ∧
    (∃ μ : Measure ℝ, standard μ ∧ μ.map Neg.neg=μ ∧
      (∀ k : ℕ, 1/(16*((2:ℝ)^k)^6) ≤ oneDrop μ (2^k)) ∧
      ∀ c : ℝ, 0<c → ∃ t : ℝ, 1 ≤ t ∧ Real.exp (-c*t^2) < oneDrop μ t) := by
  sorry
end OMA.S_mo_220800

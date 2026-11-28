import Mathlib

/-!
# Does uniform convergence of `E|X_n(t)|` to zero force `E sup_t |X_n(t)| → 0`?

Source: https://mathoverflow.net/questions/76624
Credit: @koolkao

Question (user16215, MathOverflow 76624, 2011; CC BY-SA 3.0). Suppose `(X_n(t))_{n ≥ 1}` is a
sequence of real-valued stochastic processes, and `T > 0` a fixed number. Do we have the
following implication?
`lim_{n → ∞} sup_{t ∈ [0,T]} E[|X_n(t)|] = 0` implies `lim_{n → ∞} E[sup_{t ∈ [0,T]} |X_n(t)|] = 0`.
If not, what are the weakest conditions on `X_n(t)` such that the implication is true?

`main` states that the implication holds for every probability space, every `T > 0` and every
sequence of processes. A disproof is a sequence of processes for which the hypothesis holds and
the conclusion fails. The edits of the question (extra modulus-of-continuity conditions) and the
"weakest conditions" part are not stated.

Translation choices:
* a process is a map `X n : ℝ → Ω → ℝ` with each `X n t` measurable, on a probability space
  `(Ω, μ)` with `Ω : Type`;
* both expectations are lower Lebesgue integrals of `ENNReal.ofReal |·|` (values in `[0, ∞]`), so
  `E[sup_t |X_n(t)|]` is defined (as an outer integral) even when the supremum over uncountably
  many `t` is not measurable, and no integrability assumption is needed;
* `sup_{t ∈ [0,T]}` is `⨆ t ∈ Set.Icc 0 T`, and the limits are `Filter.Tendsto … atTop (𝓝 0)`.
-/

namespace OMA.S_mo_76624

open MeasureTheory Filter Topology

/-- If `sup_{t ∈ [0,T]} E|X_n(t)| → 0` then `E sup_{t ∈ [0,T]} |X_n(t)| → 0`. -/
theorem main :
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℝ)
      (X : ℕ → ℝ → Ω → ℝ), 0 < T → (∀ n t, Measurable (X n t)) →
      Tendsto (fun n => ⨆ t ∈ Set.Icc 0 T, ∫⁻ ω, ENNReal.ofReal |X n t ω| ∂μ) atTop (𝓝 0) →
      Tendsto (fun n => ∫⁻ ω, ⨆ t ∈ Set.Icc 0 T, ENNReal.ofReal |X n t ω| ∂μ) atTop (𝓝 0) := by
  sorry

end OMA.S_mo_76624

import Mathlib

/-!
# Is every discrete compound Poisson distribution a mixed Poisson distribution?

Source: https://mathoverflow.net/questions/427161
Credit: @koolkao

Question (tparker, MathOverflow 427161, 2022; CC BY-SA 4.0). A mixed Poisson distribution has
PMF `f_L(k) = (1/k!) ∫_0^∞ e^{-λ} λ^k π(λ) dλ`, where the rate is a nonnegative continuous random
variable `L` with PDF `π`. A discrete compound Poisson distribution is the law of
`Y = X_1 + ⋯ + X_N`, where `N` is Poisson with rate `λ₀ > 0` and the `X_i` are i.i.d. copies of a
random variable `X` with values in the natural numbers, independent of `N`. Is every discrete
compound Poisson distribution a mixed Poisson distribution?

`main` states that the answer is yes. A disproof is a rate `λ₀ > 0` and a law of `X` on `ℕ` whose
compound Poisson PMF is not of the form `f_L` for any density `π`.

Translation choices:
* the law of `X` is a function `q : ℕ → ℝ` with `q j ≥ 0` and `∑ q j = 1` (`HasSum q 1`); the
  natural numbers include `0` (the asker says in a comment that this does not matter);
* the law of `X_1 + ⋯ + X_n` is the `n`-fold convolution power `convPow q n` (`convPow q 0` is the
  point mass at `0`), so the PMF of `Y` is `compoundPMF r q k = ∑' n, e^{-r} r^n / n! · convPow q n k`,
  by conditioning on `N = n`, where `r` is the source's `λ₀`;
* a PDF of a random variable with values in `[0, ∞)` is a measurable `ρ : ℝ → ℝ`, nonnegative on
  `[0, ∞)`, integrable on `[0, ∞)` with integral `1` (Lebesgue measure); `mixedPMF ρ k` is
  `(1/k!) ∫_{[0,∞)} e^{-x} x^k ρ(x) dx` (the source's `π` is `ρ` here);
* "is a mixed Poisson distribution" means that some such `ρ` gives
  `mixedPMF ρ k = compoundPMF r q k` for every `k : ℕ`.
-/

namespace OMA.S_mo_427161

open MeasureTheory

/-- The `n`-fold convolution power of a function `q : ℕ → ℝ` (the law of a sum of `n` i.i.d.
copies when `q` is a PMF); `convPow q 0` is the point mass at `0`. -/
noncomputable def convPow (q : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => fun k => if k = 0 then 1 else 0
  | n + 1 => fun k => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, convPow q n p.1 * q p.2

/-- The PMF of the compound Poisson sum `X_1 + ⋯ + X_N`, `N` Poisson with rate `r`. -/
noncomputable def compoundPMF (r : ℝ) (q : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑' n : ℕ, Real.exp (-r) * r ^ n / n.factorial * convPow q n k

/-- `ρ` is a probability density on `[0, ∞)`. -/
def IsDensity (ρ : ℝ → ℝ) : Prop :=
  Measurable ρ ∧ (∀ x ∈ Set.Ici (0 : ℝ), 0 ≤ ρ x) ∧ IntegrableOn ρ (Set.Ici 0) ∧
    ∫ x in Set.Ici (0 : ℝ), ρ x = 1

/-- The PMF of the mixed Poisson distribution with rate density `ρ`. -/
noncomputable def mixedPMF (ρ : ℝ → ℝ) (k : ℕ) : ℝ :=
  (1 / k.factorial) * ∫ x in Set.Ici (0 : ℝ), Real.exp (-x) * x ^ k * ρ x

/-- Every discrete compound Poisson distribution is a mixed Poisson distribution. -/
theorem main :
    ∀ (r : ℝ), 0 < r → ∀ q : ℕ → ℝ, (∀ j, 0 ≤ q j) → HasSum q 1 →
      ∃ ρ : ℝ → ℝ, IsDensity ρ ∧ ∀ k : ℕ, mixedPMF ρ k = compoundPMF r q k := by
  sorry

end OMA.S_mo_427161

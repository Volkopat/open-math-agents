import Mathlib

/-!
# Sahi's `n`-function FKG conjecture on the unit cube `[0,1]^k`

Source: https://arxiv.org/abs/2107.09838
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

E. H. Lieb and S. Sahi, "On the extension of the FKG inequality to `n` functions"
(arXiv:2107.09838, J. Math. Phys. 2022). For functions `f¹, …, fⁿ` and a permutation `σ ∈ Sₙ`
with `C_σ` cycles (in its disjoint cycle decomposition, fixed points included),
`E_σ(f¹, …, fⁿ) = ∏_{cycles c} 𝓔(∏_{i ∈ c} fⁱ)` and
`E_n(f¹, …, fⁿ) = ∑_{σ ∈ Sₙ} (-1)^{C_σ - 1} E_σ(f¹, …, fⁿ)` (so `E₂(f, g) = 𝓔(fg) - 𝓔(f)𝓔(g)`).
Conjecture 1.1 (Sahi 2008): if `f₁, …, fₙ` are positive monotone functions on an FKG poset, then
`E_n(f₁, …, fₙ) ≥ 0`. The paper proves it for all `n` on `[0,1]²` (and for indicators of rectangles
in `[0,1]^k`); its abstract states: "The general case for `ℝ^k`, `k > 2` remains open." This file
states the conjecture on the unit cube `[0,1]^k` with Lebesgue measure, for every `k` and `n` (the
cases `k ≤ 2` being the proved ones).

Modelling choices:
* `[0,1]^k` is `Set.Icc 0 1` in `Fin k → ℝ` with the componentwise order and Lebesgue measure,
  and `𝓔(g) = ∫_{[0,1]^k} g`.
* "Monotone" is the paper's convention, decreasing: `x ≤ x' → f(x) ≥ f(x')` (`AntitoneOn` on the
  cube); the increasing convention is equivalent by reversing the order. "Positive" means
  nonnegative. The functions are assumed measurable so that the integrals are meaningful (they are
  bounded on the cube by their value at `0`).
* The cycles of `σ`, fixed points included, are its orbits: the classes of `σ.SameCycle`.
-/

namespace OMA.S_arxiv_2107_09838

open MeasureTheory Classical

/-- The cycles of `σ` (orbits, fixed points included), as finsets of `Fin n`. -/
noncomputable def cycles {n : ℕ} (σ : Equiv.Perm (Fin n)) : Finset (Finset (Fin n)) :=
  Finset.univ.image fun i => Finset.univ.filter fun j => σ.SameCycle i j

/-- `𝓔(g) = ∫_{[0,1]^k} g`. -/
noncomputable def expect {k : ℕ} (g : (Fin k → ℝ) → ℝ) : ℝ :=
  ∫ x in Set.Icc (0 : Fin k → ℝ) 1, g x

/-- `E_n(f¹, …, fⁿ) = ∑_σ (-1)^{C_σ - 1} ∏_{c} 𝓔(∏_{i ∈ c} fⁱ)`. -/
noncomputable def En {k n : ℕ} (f : Fin n → (Fin k → ℝ) → ℝ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n),
    (-1 : ℝ) ^ ((cycles σ).card - 1) * ∏ c ∈ cycles σ, expect fun x => ∏ i ∈ c, f i x

/-- **Sahi's conjecture on `[0,1]^k` (open for `k > 2`).** -/
theorem main :
    ∀ (k n : ℕ) (f : Fin n → (Fin k → ℝ) → ℝ), 1 ≤ n →
      (∀ i, Measurable (f i)) →
      (∀ i, ∀ x ∈ Set.Icc (0 : Fin k → ℝ) 1, 0 ≤ f i x) →
      (∀ i, AntitoneOn (f i) (Set.Icc (0 : Fin k → ℝ) 1)) →
      0 ≤ En f := by
  sorry

end OMA.S_arxiv_2107_09838

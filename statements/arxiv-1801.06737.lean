import Mathlib

/-!
# At What Frequency Should the Kelly Bettor Bet?

Source: https://arxiv.org/abs/1801.06737 (C.-H. Hsieh, B. R. Barmish and J. A. Gubner),
Conjectures 1 and 2.
Credit: @ricnov

Setting (Section II of the paper). The returns `X k`, `k = 0, 1, ...`, are i.i.d. random variables
with `Xmin ≤ X k ≤ Xmax`, where `Xmin` and `Xmax` are support points and `-1 ≤ Xmin < 0 < Xmax < ∞`.
A fraction `K ∈ [0, 1]` of the account is bet at stage 0 and left at risk for `n` periods. The total
return is `X_n = ∏_{k < n} (1 + X k) - 1`, the expected logarithmic growth per period is
`g_n(K) = (1/n) E[log(1 + K X_n)]`, and `g_n^* = max_{K ∈ [0, 1]} g_n(K)`. The standing assumption
of the paper is `E[X 0] > 0`. The paper states two conjectures for this setting (Section V).

Conjecture 1: the optimal expected logarithmic growth `g_n^*` is non-increasing in `n`; i.e., for
all `n ≥ 1`, `g_n^* ≥ g_{n+1}^*`.

The returns satisfy the sufficient attractiveness inequality if `E[1 / (1 + X 0)] ≤ 1`. The paper
proves that this inequality guarantees `g_1^* = g_n^*` for all `n ≥ 1` (Sufficiency Theorem), and
states

Conjecture 2: satisfaction of the sufficient attractiveness inequality is necessary for the
condition `g_1^* = g_n^*` to hold for all `n ≥ 1`.

`main` is the conjunction of the two conjectures.

Conventions.
* `g_n(1)` is `-∞` when a total loss has positive probability, which a real-valued integral cannot
  express. Since `g_n(K)` tends to `g_n(1)` as `K` increases to `1` (monotone convergence on the
  events `X_n ≥ 0` and `X_n < 0`), the maximum over `[0, 1]` equals the supremum over `0 ≤ K < 1`,
  where the integrand is bounded. `gStar` is written as that supremum.
* `E[1 / (1 + X 0)]` is taken in `[0, ∞]`, with the value `∞` on the event `X 0 = -1`.
* Support points: every neighbourhood of `Xmin` and of `Xmax` has positive probability.
-/

namespace OMA.S_arxiv_1801_06737

open MeasureTheory ProbabilityTheory

/-- The total return over `n` periods, `X_n = ∏_{k < n} (1 + X k) - 1`. -/
def totalReturn {Ω : Type} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (∏ k ∈ Finset.range n, (1 + X k ω)) - 1

/-- The expected logarithmic growth per period, `g_n(K) = (1/n) E[log(1 + K X_n)]`. -/
noncomputable def g {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ) (n : ℕ)
    (K : ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∫ ω, Real.log (1 + K * totalReturn X n ω) ∂P

/-- The optimal expected logarithmic growth `g_n^*`, as the supremum of `g_n` over `0 ≤ K < 1`. -/
noncomputable def gStar {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (n : ℕ) : ℝ :=
  ⨆ K : Set.Ico (0 : ℝ) 1, g P X n K

/-- Conjectures 1 and 2 of Hsieh, Barmish and Gubner. First, `g_n^* ≥ g_{n+1}^*` for all `n ≥ 1`.
Second, if `g_n^* = g_1^*` for all `n ≥ 1`, then the sufficient attractiveness inequality
`E[1 / (1 + X 0)] ≤ 1` holds. -/
theorem main : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (Xmin Xmax : ℝ),
    (∀ k, Measurable (X k)) → iIndepFun X P → (∀ k, IdentDistrib (X k) (X 0) P P) →
    -1 ≤ Xmin → Xmin < 0 → 0 < Xmax →
    (∀ k ω, Xmin ≤ X k ω ∧ X k ω ≤ Xmax) →
    (∀ ε : ℝ, 0 < ε → 0 < P {ω | X 0 ω < Xmin + ε}) →
    (∀ ε : ℝ, 0 < ε → 0 < P {ω | Xmax - ε < X 0 ω}) →
    0 < ∫ ω, X 0 ω ∂P →
    (∀ n : ℕ, 1 ≤ n → gStar P X (n + 1) ≤ gStar P X n) ∧
      ((∀ n : ℕ, 1 ≤ n → gStar P X n = gStar P X 1) →
        ∫⁻ ω, (ENNReal.ofReal (1 + X 0 ω))⁻¹ ∂P ≤ 1) := by
  sorry

end OMA.S_arxiv_1801_06737

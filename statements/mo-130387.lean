import Mathlib

/-!
# Savings property: A transformation which turns nonnegative martingales into uniformly integrable ones

Source: https://mathoverflow.net/questions/130387
Credit: @ricnov

The source describes the savings trick of algorithmic randomness: the gambler saves all but one
dollar of her money and bets with the rest using the strategy of the original martingale. More
formally, if `(M_n)` is a nonnegative martingale, two processes are defined recursively, where
`N_n` is the new martingale and `L_n` is the savings account:
* `N_0 = M_0 + 1`, `L_0 = 0`,
* `N_{n+1} = N_n + (M_{n+1} - M_n) * (N_n - L_n) / (M_n + 1)`, `L_{n+1} = max {N_{n+1} - 1, L_n}`.

The source says that it can be shown that
1. `N_n` is a nonnegative martingale;
2. `limsup_n M_n = ∞` iff `lim_n N_n = ∞`;
3. `N_n` is uniformly integrable, and hence `N_n = E[X | G_n]` for some integrable `X`;

and asks whether there is anything like this in probability theory, namely a martingale
transformation that takes in a nonnegative martingale and returns a new martingale satisfying (1)
through (3).

`main` states that the savings transformation satisfies (1), (2) and (3). The source reports
these three facts as known and gives no proof; its question proper is a request for references.
(A fourth item of the list is struck out in the source and is not part of `main`.)

Conventions.
* A nonnegative martingale is a martingale `M` with respect to a filtration `G` on a probability
  space, with `0 ≤ M n ω` for all `n` and all `ω`.
* (2) is stated for every path `ω`, with the `limsup` taken in the extended real numbers.
* Uniform integrability is `UniformIntegrable _ 1 P`, the notion of probability theory.
-/

namespace OMA.S_mo_130387

open MeasureTheory Filter Topology

/-- One step of the savings transformation: from `(N_n, L_n)`, with `m = M_n` and `m' = M_{n+1}`,
to `(N_{n+1}, L_{n+1})`. -/
noncomputable def step (m m' : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 + (m' - m) * ((p.1 - p.2) / (m + 1)),
    max (p.1 + (m' - m) * ((p.1 - p.2) / (m + 1)) - 1) p.2)

/-- The pair `(N_n, L_n)` along the path `ω`. -/
noncomputable def savings {Ω : Type} (M : ℕ → Ω → ℝ) (ω : Ω) : ℕ → ℝ × ℝ
  | 0 => (M 0 ω + 1, 0)
  | n + 1 => step (M n ω) (M (n + 1) ω) (savings M ω n)

/-- The new martingale `N_n`. -/
noncomputable def N {Ω : Type} (M : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (savings M ω n).1

/-- The savings transformation of a nonnegative martingale `M` satisfies (1), (2) and (3):
`N` is a nonnegative martingale; along every path, `limsup M = ∞` iff `N` tends to `∞`; and `N`
is uniformly integrable, hence of the form `N_n = E[X | G_n]` for an integrable `X`. -/
theorem main : ∀ (Ω : Type) [m0 : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : Filtration ℕ m0) (M : ℕ → Ω → ℝ),
    Martingale M G P → (∀ n ω, 0 ≤ M n ω) →
    (Martingale (N M) G P ∧ ∀ n ω, 0 ≤ N M n ω) ∧
      (∀ ω, limsup (fun n => (M n ω : EReal)) atTop = ⊤ ↔
        Tendsto (fun n => N M n ω) atTop atTop) ∧
      (UniformIntegrable (N M) 1 P ∧
        ∃ X : Ω → ℝ, Integrable X P ∧ ∀ n, N M n =ᵐ[P] P[X | G n]) := by
  sorry

end OMA.S_mo_130387

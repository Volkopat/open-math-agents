import Mathlib

/-!
# Asymptotic behavior of row sums in 2-d array of random variables

Source: https://mathoverflow.net/questions/313415
Credit: @ricnov

The question. Let `f : ℕ → ℕ` be increasing. For each `m ∈ [0, 1]`, consider an infinite
two-dimensional array of random variables in which row `n` has `f n` entries
`B^m_{n,1}, ..., B^m_{n,f(n)}`. Variables in the same row are i.i.d., with
`B^m_{n,i} = (1 + 2m)^K (1 - m)^(n - K)`, where `K ∼ Bin(n, 1/2)`. (`B^m_{n,i}` is agent `i`'s
bankroll after betting a proportion `m` of her bankroll `n` times in succession, from initial
bankroll 1, on a bet with win probability 1/2 and payoff odds 2:1; on day `n`, `f n` agents have
each bet `n` times.) Let `S^m_n` be the sum of row `n`. Say that `m` does better than `m'` if
`P(S^m_n > S^{m'}_n) → 1` as `n → ∞`, and that `m` does best if `m` does better than `m'` for all
`m' ≠ m`. Does there exist `f` such that some `m` other than `1/4` or `1` does best?

`main` is the affirmative answer. (For background: `1/4` is the Kelly proportion, which maximises
the expected logarithm of the bankroll, and `1` maximises the expected bankroll.)

Conventions.
* The randomness is given through the numbers of bets won: `K m n i` is the binomial variable
  behind `B^m_{n,i}`, and `IsBettingArray` says that, for every `m ∈ [0, 1]` and every row `n ≥ 1`,
  the variables `K m n i`, `i < f n`, are independent and each has the law `Bin(n, 1/2)`, that is
  `P(K m n i = k) = (n choose k) / 2^n` for every `k`.
* The source does not say how the arrays for different `m` are coupled (the same coin flips for
  every `m`, or separate ones), nor how different rows are related. No assumption is made here:
  `main` asks for the conclusion on every probability space and for every joint distribution,
  which covers every reading.
* `f` increasing is stated as `StrictMono f`; a strictly increasing `f` is in particular
  non-decreasing, so the answer does not depend on which of the two is meant.
* `m` and `m'` range over `[0, 1]`. For `m = 1` the bankroll is `3^n` if all `n` bets are won and
  `0` otherwise (`0^0 = 1`).
-/

namespace OMA.S_mo_313415

open MeasureTheory ProbabilityTheory Filter Topology

/-- The bankroll `(1 + 2m)^k (1 - m)^(n - k)` of an agent who has bet a proportion `m` of her
bankroll `n` times in succession, from initial bankroll 1, at payoff odds 2:1, and has won `k` of
the `n` bets. -/
noncomputable def bankroll (m : ℝ) (n k : ℕ) : ℝ :=
  (1 + 2 * m) ^ k * (1 - m) ^ (n - k)

/-- `K m n i` is the number of bets won behind the entry `B^m_{n,i}` of the array for the
proportion `m`. For every `m ∈ [0, 1]` and every row `n ≥ 1`, the `f n` variables of the row are
independent, and each has the binomial law `Bin(n, 1/2)`. -/
def IsBettingArray (f : ℕ → ℕ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (K : ℝ → (n : ℕ) → Fin (f n) → Ω → ℕ) : Prop :=
  ∀ m ∈ Set.Icc (0 : ℝ) 1, ∀ n : ℕ, 1 ≤ n →
    (∀ i, Measurable (K m n i)) ∧ iIndepFun (fun i => K m n i) P ∧
      ∀ i k, P {ω | K m n i ω = k} = (n.choose k : ENNReal) / 2 ^ n

/-- The sum `S^m_n` of row `n` of the array for the proportion `m`. -/
noncomputable def rowSum (f : ℕ → ℕ) {Ω : Type} (K : ℝ → (n : ℕ) → Fin (f n) → Ω → ℕ)
    (m : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i : Fin (f n), bankroll m n (K m n i ω)

/-- `m` does better than `m'`: `P(S^m_n > S^{m'}_n) → 1` as `n → ∞`. -/
def DoesBetter (f : ℕ → ℕ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (K : ℝ → (n : ℕ) → Fin (f n) → Ω → ℕ) (m m' : ℝ) : Prop :=
  Tendsto (fun n : ℕ => P {ω | rowSum f K m' n ω < rowSum f K m n ω}) atTop (𝓝 1)

/-- There is an increasing `f` for which some proportion `m` other than `1/4` and `1` does best:
it does better than every other `m' ∈ [0, 1]`. -/
theorem main : ∃ f : ℕ → ℕ, StrictMono f ∧ ∃ m ∈ Set.Icc (0 : ℝ) 1, m ≠ 1 / 4 ∧ m ≠ 1 ∧
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (K : ℝ → (n : ℕ) → Fin (f n) → Ω → ℕ), IsBettingArray f P K →
      ∀ m' ∈ Set.Icc (0 : ℝ) 1, m' ≠ m → DoesBetter f P K m m' := by
  sorry

end OMA.S_mo_313415

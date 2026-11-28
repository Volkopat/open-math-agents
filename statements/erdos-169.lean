import Mathlib

/-!
# Erdős Problem 169

Source: https://www.erdosproblems.com/169
Credit: @shc261392

Let `k ≥ 3` and `f(k)` be the supremum of `∑_{n ∈ A} 1/n` as `A` ranges over all sets of
positive integers which do not contain a `k`-term arithmetic progression. Is
`lim_{k → ∞} f(k) / log W(k) = ∞`, where `W(k)` is the van der Waerden number?

Reading used here:
* A `k`-term arithmetic progression is `a, a + d, …, a + (k - 1) d` with `d > 0`.
* `f k` is taken in `ℝ≥0∞`: the sum over `A` is `∑' n : A, 1 / n` there, so a divergent sum is
  `⊤`. (Whether `f k` is finite for all `k` is equivalent to Erdős Problem 3, as the source
  notes, so `f k = ⊤` must be allowed.)
* `W k` is the two-colour van der Waerden number: the least `N` such that every colouring of
  `{1, …, N}` with two colours has a monochromatic `k`-term arithmetic progression.
* The limit is read as `f k / log (W k) → ∞` in `ℝ≥0∞` as `k → ∞` (for `k ≥ 3`, `W k ≥ 3` so
  `log (W k) > 0`, and only large `k` matter for the limit).
-/

namespace OMA.S_erdos_169

/-- `A` contains a `k`-term arithmetic progression with positive common difference. -/
def HasAP (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

/-- `f k`: the supremum of `∑_{n ∈ A} 1/n` over sets `A` of positive integers with no `k`-term
arithmetic progression. -/
noncomputable def f (k : ℕ) : ENNReal :=
  ⨆ (A : Set ℕ) (_ : (∀ n ∈ A, 0 < n) ∧ ¬ HasAP A k), ∑' n : A, (1 : ENNReal) / (n : ℕ)

/-- The two-colour van der Waerden number `W k`. -/
noncomputable def W (k : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ c : ℕ → Bool, ∃ a d : ℕ, 0 < d ∧
    (∀ i < k, 1 ≤ a + i * d ∧ a + i * d ≤ N) ∧ ∀ i < k, c (a + i * d) = c a}

theorem main :
    Filter.Tendsto (fun k : ℕ => f k / ENNReal.ofReal (Real.log (W k))) Filter.atTop
      (nhds (⊤ : ENNReal)) := by
  sorry

end OMA.S_erdos_169

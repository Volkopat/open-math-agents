import Mathlib

/-!
# Erdős Problem 520

Source: https://www.erdosproblems.com/520
Credit: @mattdorman

The source asks: let `f` be a Rademacher multiplicative function: for each prime `p` choose
`f(p) ∈ {-1, 1}` independently and uniformly at random, set `f(p₁ ⋯ p_r) = f(p₁) ⋯ f(p_r)` for
squarefree integers and `f(n) = 0` if `n` is not squarefree. Does there exist some constant
`c > 0` such that, almost surely,
`limsup_{N → ∞} (∑_{m ≤ N} f(m)) / √(N log log N) = c`?

Reading used here: the randomness is a sequence `ω : ℕ → Bool` of independent fair coins (the
infinite product of uniform measures on `Bool`); only the coordinates at primes are used, with
`f(p) = 1` when `ω p` is `true` and `-1` otherwise (so `f(1) = 1`). The sum runs over
`1 ≤ m ≤ N` and `log` is the natural logarithm. A limsup equal to `c` is stated directly: for
every `ε > 0` the ratio is eventually at most `c + ε` and is at least `c - ε` for infinitely many
`N`. The constant `c` is chosen before the almost-sure event, as in the source. The statement
below is the affirmative answer.
-/

open Filter MeasureTheory

namespace OMA.S_erdos_520

open Classical in
/-- The Rademacher multiplicative function with signs `f(p)` read off from `ω` at primes. -/
noncomputable def rademacher (ω : ℕ → Bool) (m : ℕ) : ℤ :=
  if Squarefree m then ∏ p ∈ m.primeFactors, (if ω p then (1 : ℤ) else -1) else 0

/-- Independent fair coins, indexed by `ℕ`. -/
noncomputable def coins : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure

/-- The normalised partial sum `(∑_{m ≤ N} f(m)) / √(N log log N)`. -/
noncomputable def ratio (ω : ℕ → Bool) (N : ℕ) : ℝ :=
  ((∑ m ∈ Finset.Icc 1 N, rademacher ω m : ℤ) : ℝ) /
    Real.sqrt ((N : ℝ) * Real.log (Real.log N))

theorem main :
    ∃ c : ℝ, 0 < c ∧ ∀ᵐ ω ∂coins, ∀ ε : ℝ, 0 < ε →
      (∀ᶠ N : ℕ in atTop, ratio ω N ≤ c + ε) ∧ (∃ᶠ N : ℕ in atTop, c - ε ≤ ratio ω N) := by
  sorry

end OMA.S_erdos_520

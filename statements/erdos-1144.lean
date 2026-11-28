import Mathlib

/-!
# Erdős Problem 1144

Source: https://www.erdosproblems.com/1144
Credit: @mattdorman

The source asks: let `f` be a random completely multiplicative function, where for each prime `p`
we independently choose `f(p) ∈ {-1, 1}` uniformly at random. Is it true that
`limsup_{N → ∞} (∑_{m ≤ N} f(m)) / √N = ∞` with probability `1`?

Reading used here: the randomness is a sequence `ω : ℕ → Bool` of independent fair coins (the
infinite product of uniform measures on `Bool`); only the coordinates at primes are used, with
`f(p) = 1` when `ω p` is `true` and `-1` otherwise. The completely multiplicative extension is
`f(m) = ∏_{p ∣ m} f(p)^{v_p(m)}` (so `f(1) = 1`). The sum runs over `1 ≤ m ≤ N`. A limsup equal to
`∞` means the ratio exceeds every bound for infinitely many `N`. The statement below is the
affirmative answer.
-/

open Filter MeasureTheory

namespace OMA.S_erdos_1144

/-- The completely multiplicative function with signs `f(p)` read off from `ω` at primes. -/
def randomCMF (ω : ℕ → Bool) (m : ℕ) : ℤ :=
  ∏ p ∈ m.primeFactors, (if ω p then (1 : ℤ) else -1) ^ (m.factorization p)

/-- Independent fair coins, indexed by `ℕ`. -/
noncomputable def coins : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype Bool).toMeasure

theorem main :
    ∀ᵐ ω ∂coins, ∀ M : ℝ, ∃ᶠ N : ℕ in atTop,
      M < ((∑ m ∈ Finset.Icc 1 N, randomCMF ω m : ℤ) : ℝ) / Real.sqrt N := by
  sorry

end OMA.S_erdos_1144

import Mathlib

/-!
# Prove or disprove a mutual information inequality

Source: https://mathoverflow.net/questions/418877
Credit: @Denyven

The author's note conjectures the displayed chain for any decreasing transition probability.
Here `q s` is the probability of binary output zero at input `s`. At the `k)-th position,
the input is `k * X₁ + Xₖ₊₁ + ⋯ + Xₙ`. Its law is an independent weighted Bernoulli plus
a binomial with `n-k` trials. Adjacent comparisons state the entire chain, and each occurrence
of `capacity` optimizes over its own Bernoulli parameter. The supremum is attained by continuity
on the compact interval `[0,1]`. We use natural logarithms.

The target is the separate general conjecture in the note. The source also asks about the
particular transition probability `q(s) = 1/(s+5)`.
-/

namespace OMA.S_mo_418877

open Finset Set

noncomputable def binomialWeight (m j : ℕ) (p : ℝ) : ℝ :=
  (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j)

/-- The expected value of `f` on the weighted Bernoulli input. -/
noncomputable def average (n k : ℕ) (p : ℝ) (f : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range (n - k + 1), binomialWeight (n - k) j p * ((1 - p) * f j + p * f (k + j))

noncomputable def information (q : ℕ → ℝ) (n k : ℕ) (p : ℝ) : ℝ :=
  Real.binEntropy (average n k p q) - average n k p (fun s => Real.binEntropy (q s))

noncomputable def capacity (q : ℕ → ℝ) (n k : ℕ) : ℝ :=
  sSup (information q n k '' Icc 0 1)

def decreasingConjecture : Prop :=
  ∀ q : ℕ → ℝ, (∀ s, q s ∈ Icc (0 : ℝ) 1) → Antitone q →
    ∀ n k : ℕ, 1 ≤ k → k < n → capacity q n k ≤ capacity q n (k + 1)

theorem main : decreasingConjecture := by
  sorry

end OMA.S_mo_418877

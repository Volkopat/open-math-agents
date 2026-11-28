import Mathlib

/-!
# Erdős Problem 952

Source: https://www.erdosproblems.com/952
Credit: @mattdorman

The source asks (the Gaussian moat problem): is there an infinite sequence of distinct Gaussian
primes `x₁, x₂, …` such that `|x_{n+1} - xₙ| ≪ 1`?

Reading used here: Gaussian primes are the prime elements of `ℤ[i]` (`Prime` in `GaussianInt`,
which allows all associates). `|x_{n+1} - xₙ| ≪ 1` means the steps are uniformly bounded; it is
stated with the integer norm `Zsqrtd.norm z = |z|²`, which is bounded exactly when `|z|` is.
The sequence is indexed from `0`. The statement below is the affirmative answer (the source
records that Erdős expected the answer to be negative; a disproof settles it equally).
-/

namespace OMA.S_erdos_952

theorem main :
    ∃ x : ℕ → GaussianInt, Function.Injective x ∧ (∀ n, Prime (x n)) ∧
      ∃ C : ℤ, ∀ n, (x (n + 1) - x n).norm ≤ C := by
  sorry

end OMA.S_erdos_952

import Mathlib

/-!
# Do the Ulam numbers have a positive density?

Source: https://en.wikipedia.org/wiki/Ulam_number
Credit: @shc261392

The Ulam numbers are `1, 2, 3, 4, 6, 8, 11, 13, 16, 18, …`: the first two are `1` and `2`, and
each later one is the smallest integer larger than the previous one that is the sum of two
distinct earlier Ulam numbers in exactly one way. Numerically the proportion of Ulam numbers up to
`N` is close to `0.074`; it is open whether they have a positive density.

Reading used here:
* `IsUlamSeq u` says that `u 0, u 1, u 2, …` lists the Ulam numbers in increasing order:
  `u 0 = 1`, `u 1 = 2`, and for `n ≥ 2`, `u n` is the least `m > u (n - 1)` with exactly one pair
  `i < j < n` such that `u i + u j = m`. This determines `u` uniquely, and such a sequence exists
  (the sequence is known to be infinite).
* "Positive density" is read as: the natural density exists and is positive, that is
  `#{n | u n ≤ N} / N` converges to some `d > 0`.
-/

namespace OMA.S_wp_do_the_ulam_numbers_have_a_positive_density

/-- Number of ways to write `m` as `u i + u j` with `i < j < n`. -/
def reps (u : ℕ → ℕ) (n m : ℕ) : ℕ :=
  ((Finset.range n ×ˢ Finset.range n).filter (fun p => p.1 < p.2 ∧ u p.1 + u p.2 = m)).card

/-- `u` lists the Ulam numbers in increasing order. -/
def IsUlamSeq (u : ℕ → ℕ) : Prop :=
  u 0 = 1 ∧ u 1 = 2 ∧
    ∀ n, 2 ≤ n → IsLeast {m : ℕ | u (n - 1) < m ∧ reps u n m = 1} (u n)

theorem main :
    ∀ u : ℕ → ℕ, IsUlamSeq u →
      ∃ d : ℝ, 0 < d ∧
        Filter.Tendsto (fun N : ℕ => ({n : ℕ | u n ≤ N}.ncard : ℝ) / N) Filter.atTop (nhds d) := by
  sorry

end OMA.S_wp_do_the_ulam_numbers_have_a_positive_density

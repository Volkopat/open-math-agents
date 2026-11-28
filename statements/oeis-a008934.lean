import Mathlib

/-!
# A008934: tournament sequences as nested sums

Source: https://oeis.org/A008934 (Benedict W. J. Irwin, Nov 26 2016)

A tournament sequence is a sequence `(a_1, ..., a_L)` with `a_1 = 1` and
`a_i < a_{i+1} ≤ 2 * a_i` for all `i`. The OEIS offset is 0 and `a(n)` counts the tournament
sequences of length `n + 1` (for example `a(3) = 7` counts the 7 sequences of length 4, as in the
entry's example section). A sequence of length `n + 1` is a function `Fin (n + 1) → ℕ`.

The conjecture says that for `n ≥ 2`
`a(n) = Sum_{i_1=1..2} Sum_{i_2=1..i_1+2} ... Sum_{i_{n-1}=1..i_1+...+i_{n-2}+2} 1`,
a nest of `n - 1` sums whose upper limit is `2` plus the sum of the outer indices
(the entry lists the cases `n = 2, 3, 4, 5`). `nest m s` is a nest of `m` such sums when the
current upper limit is `s`: the outermost index `i` runs over `1..s` and the next limit is `s + i`.
So the conjectured value of `a(n)` is `nest (n - 1) 2`.
-/

namespace OMA.S_oeis_a008934

/-- Tournament sequences of length `n + 1`. -/
def tournamentSeqs (n : ℕ) : Set (Fin (n + 1) → ℕ) :=
  {a | a 0 = 1 ∧ ∀ i : Fin n, a i.castSucc < a i.succ ∧ a i.succ ≤ 2 * a i.castSucc}

/-- OEIS A008934: the number of tournament sequences of length `n + 1`. -/
noncomputable def A (n : ℕ) : ℕ := (tournamentSeqs n).ncard

/-- `nest m s`: the value of `m` nested sums of `1`, the outermost over `i = 1..s`, each inner
upper limit being the previous limit plus the outer index. -/
def nest : ℕ → ℕ → ℕ
  | 0, _ => 1
  | m + 1, s => ∑ i ∈ Finset.Icc 1 s, nest m (s + i)

/-- Irwin's nested-sum formula for the number of tournament sequences. -/
theorem main : ∀ n : ℕ, 2 ≤ n → A n = nest (n - 1) 2 := by
  sorry

end OMA.S_oeis_a008934

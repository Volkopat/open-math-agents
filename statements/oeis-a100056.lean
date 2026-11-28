import Mathlib

/-!
# A100056: Sum of absolute differences of p(n) defined in A054065

Source: https://oeis.org/A100056 (offset 2); p(n) is defined in https://oeis.org/A054065.
Credit: @Jack-Whitcomb

The conjecture (Gary W. Adamson, 2004): a(n) provides the maximum sum of difference terms of
any permutation of 1 through n. A054065 (or reversals) give the optimal permutations and a(n)
gives the sum.

Definitions. Let τ = (1 + √5)/2. A054065: p(n) is the permutation of 1, 2, …, n obtained by
ordering the fractional parts {h τ} for h = 1, …, n; for example p(4) = (2, 4, 1, 3), since
{2τ} < {4τ} < {τ} < {3τ}. The fractional parts are pairwise distinct (τ is irrational), so p(n)
lists 1..n in increasing order of {h τ}. A100056: a(n) is the sum of the absolute values of
the differences of consecutive entries of p(n); for example a(4) = |4-2| + |1-4| + |3-1| = 7.

Two numbers h, h' in 1..n are consecutive entries of p(n), in this order, exactly when
{h τ} < {h' τ} and no g in 1..n has {h τ} < {g τ} < {h' τ}. We define a(n) as the sum of
|h - h'| over these pairs, which is the sum of the absolute differences of p(n).

The sum of difference terms of a permutation l of 1..n (a list) is the sum of |x - y| over
consecutive entries x, y of l. The conjecture says that a(n) is the greatest such sum.
-/

namespace OMA.S_oeis_a100056

open Finset

/-- The golden ratio τ = (1 + √5)/2 of A054065. -/
noncomputable def τ : ℝ := (1 + Real.sqrt 5) / 2

/-- `h` is immediately followed by `h'` in p(n): both are in 1..n, {h τ} < {h' τ}, and no
`g` in 1..n has its fractional part strictly in between. -/
def Consecutive (n h h' : ℕ) : Prop :=
  h ∈ Icc 1 n ∧ h' ∈ Icc 1 n ∧ Int.fract ((h : ℝ) * τ) < Int.fract ((h' : ℝ) * τ) ∧
    ∀ g ∈ Icc 1 n, ¬ (Int.fract ((h : ℝ) * τ) < Int.fract ((g : ℝ) * τ) ∧
      Int.fract ((g : ℝ) * τ) < Int.fract ((h' : ℝ) * τ))

open Classical in
/-- a(n): the sum of the absolute differences of consecutive entries of p(n). -/
noncomputable def a (n : ℕ) : ℕ :=
  ∑ q ∈ (Icc 1 n ×ˢ Icc 1 n).filter (fun q => Consecutive n q.1 q.2),
    Int.natAbs ((q.1 : ℤ) - (q.2 : ℤ))

/-- The sum of difference terms of a list: the sum of |x - y| over consecutive entries. -/
def jumpSum (l : List ℕ) : ℕ :=
  ((l.zip l.tail).map fun q => Int.natAbs ((q.1 : ℤ) - (q.2 : ℤ))).sum

theorem main : ∀ n : ℕ, 2 ≤ n →
    IsGreatest {s : ℕ | ∃ l : List ℕ, l.Perm (List.range' 1 n) ∧ jumpSum l = s} (a n) := by
  sorry

end OMA.S_oeis_a100056

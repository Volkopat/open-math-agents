import Mathlib

/-!
# A095689: Permutation of natural numbers, inverse permutation to A094870.

Source: https://oeis.org/A095689
Credit: @gblacher2

Conjecture (comment section of A095689, attributed there to P. Hegarty):
"lim_{n->infinity} a(n)/n = 1."

The sequence has offset 1: 1, 2, 4, 3, 5, 6, 8, 7, 10, 9, 14, 12, ...

A094870 (offset 1): a(1) = 1; for n > 1, a(n) is the minimal positive integer t not equal to
a(1), ..., a(n-1) such that t - a(n-i) is not equal to a(n-i) - a(n-2i) for all 1 <= i < n/2.
It begins 1, 2, 4, 3, 5, 6, 8, 7, 10, 9, 13, 12, ...

Modelling choices:
* `terms n` is the list A094870(1), ..., A094870(n), so A094870(k) is
  `(terms n).getD (k - 1) 0` for k ≤ n. For the new index N = n + 2, A094870(N - i) and
  A094870(N - 2i) are the entries at positions n + 1 - i and n + 1 - 2i of `terms (n + 1)`.
* "1 <= i < n/2" is read over the reals, i.e. `1 ≤ i ∧ 2 * i < N`; this is exactly the range
  in which A094870(N - 2i) is defined. Differences are taken in `ℤ`.
* The minimum is taken with `sInf`. The set is never empty: at most N - 1 values are used and
  at most one value t is excluded for each i, so the default value of `sInf` is never used.
* The inverse permutation: `a n` is the index k ≥ 1 with A094870(k) = n, taken as the least
  such k with `sInf` (A094870 is injective by construction, so the index is unique; the OEIS
  name records that A094870 is a permutation of the positive integers, so it exists for n ≥ 1).
* The limit is the usual limit of the real sequence a(n)/n as n → ∞.
-/

namespace OMA.S_oeis_a095689

/-- `terms n` is the list of the first `n` terms of A094870. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | n + 2 =>
    let l := terms (n + 1)
    l ++ [sInf {t : ℕ | 0 < t ∧ t ∉ l ∧ ∀ i : ℕ, 1 ≤ i → 2 * i < n + 2 →
      (t : ℤ) - (l.getD (n + 1 - i) 0 : ℤ) ≠
        (l.getD (n + 1 - i) 0 : ℤ) - (l.getD (n + 1 - 2 * i) 0 : ℤ)}]

/-- A094870(n), the last entry of `terms n` (offset 1). -/
noncomputable def A094870 (n : ℕ) : ℕ := (terms n).getLastD 0

/-- A095689(n): the index k ≥ 1 at which A094870 takes the value n. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | 1 ≤ k ∧ A094870 k = n}

/-- The conjecture: a(n)/n tends to 1. -/
theorem main : Filter.Tendsto (fun n : ℕ => (a n : ℝ) / (n : ℝ)) Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a095689

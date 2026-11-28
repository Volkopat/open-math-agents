import Mathlib

/-!
# A094870: a(1)=1; for n > 1, a(n) is the minimal positive integer t not equal to a(1), ..., a(n-1) such that t - a(n-i) is not equal to a(n-i) - a(n-2i) for all 1 <= i < n/2.

Source: https://oeis.org/A094870
Credit: @gblacher2

Conjecture (comment section of A094870, attributed there to P. Hegarty):
"lim_{n->infinity} a(n)/n = 1."

The sequence has offset 1: 1, 2, 4, 3, 5, 6, 8, 7, 10, 9, 13, 12, ...
(a(3) = 4: 3 is excluded because 3 - a(2) = a(2) - a(1).)

Modelling choices:
* `terms n` is the list a(1), ..., a(n), so a(k) is `(terms n).getD (k - 1) 0` for k ≤ n.
  For the new index N = n + 2, a(N - i) and a(N - 2i) are the entries at positions
  n + 1 - i and n + 1 - 2i of `terms (n + 1)`.
* "1 <= i < n/2" is read over the reals, i.e. `1 ≤ i ∧ 2 * i < N`; this is exactly the range
  in which a(N - 2i) is defined. Differences are taken in `ℤ`.
* The minimum is taken with `sInf`. The set is never empty: at most N - 1 values are used and
  at most one value t is excluded for each i, so the default value of `sInf` is never used.
* a(n) is the last entry of `terms n`, and the limit is the usual limit of the real
  sequence a(n)/n as n → ∞.
-/

namespace OMA.S_oeis_a094870

/-- `terms n` is the list of the first `n` terms a(1), ..., a(n). -/
noncomputable def terms : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | n + 2 =>
    let l := terms (n + 1)
    l ++ [sInf {t : ℕ | 0 < t ∧ t ∉ l ∧ ∀ i : ℕ, 1 ≤ i → 2 * i < n + 2 →
      (t : ℤ) - (l.getD (n + 1 - i) 0 : ℤ) ≠
        (l.getD (n + 1 - i) 0 : ℤ) - (l.getD (n + 1 - 2 * i) 0 : ℤ)}]

/-- a(n), the last entry of `terms n` (offset 1). -/
noncomputable def a (n : ℕ) : ℕ := (terms n).getLastD 0

/-- The conjecture: a(n)/n tends to 1. -/
theorem main : Filter.Tendsto (fun n : ℕ => (a n : ℝ) / (n : ℝ)) Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a094870

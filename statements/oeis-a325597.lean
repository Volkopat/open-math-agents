import Mathlib

/-!
# A325597: a(n) is the least number not 2a(m) + a(m-1) for any m < n.

Source: https://oeis.org/A325597
Credit: @eltociear

`a(1) = 1`, `a(2) = 2`, and each later term is the least number, larger than the previous term,
that is not of the form `2a(m) + a(m-1)` for any `m < n` (`1, 2, 3, 4, 6, 7, 9, 10, 12, ...`; the
entry's example: `5 = 2·2 + 1` is excluded, so `a(3) = 3`, `a(4) = 4`; then `8` and `11` are
excluded, so `a(5) = 6`, `a(6) = 7`). The entry conjectures:

  Let d(n) = 3a(n) - 4n; then d(n) is bounded, and d(n) = 0 for infinitely many n.

`main` is the conjunction of both claims (with `d` computed in `ℤ`).

On the reading of the name: taken literally, "the least number not of that form" would repeat `1`.
The entry's example and data choose new numbers in increasing order, so the definition below asks
for the least number larger than the previous term that is not excluded; this reproduces the
listed terms. `pref k` is the list `[a 1, …, a (k + 2)]`.
-/

namespace OMA.S_oeis_a325597

/-- `pref k` is the list `[a 1, a 2, …, a (k + 2)]`. -/
noncomputable def pref : ℕ → List ℕ
  | 0 => [1, 2]
  | k + 1 =>
    let l := pref k
    l ++ [sInf {x : ℕ | l.getLastD 0 < x ∧
      ∀ i : ℕ, i + 1 < l.length → x ≠ 2 * l.getD (i + 1) 0 + l.getD i 0}]

/-- OEIS A325597 (`n ≥ 1`). -/
noncomputable def a (n : ℕ) : ℕ := (pref n).getD (n - 1) 0

/-- `d(n) = 3 a(n) - 4 n`. -/
noncomputable def d (n : ℕ) : ℤ := 3 * (a n : ℤ) - 4 * n

/-- The conjectures in OEIS A325597. -/
theorem main : (∃ C : ℤ, ∀ n : ℕ, 1 ≤ n → |d n| ≤ C) ∧ {n : ℕ | 1 ≤ n ∧ d n = 0}.Infinite := by
  sorry

end OMA.S_oeis_a325597

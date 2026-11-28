import Mathlib

/-!
# A100039: positions of the fourth subsequence of the natural numbers in A100035

Source: https://oeis.org/A100039 (the underlying sequence: https://oeis.org/A100035)
Credit: @avivorly

A100035 (Reinhard Zumkeller), %N: a(n+1) occurs not earlier as a neighbor of terms = a(n): either it is
the greatest number < a(n) or, if no such number exists, the smallest number > a(n); a(1) = 1.

A100039, %N: Positions of occurrences of the natural numbers as fourth subsequence in A100035.
%C: n>1: A100035(a(n))=n and A100035(m)<>n for a(n-1)<=m<a(n).

Claim (Ralf Stephan, May 15 2007, the %F line of A100039): 2n^2 + 7n + 13 (conjectured).
That is, A100039(n) = 2n^2 + 7n + 13 for every n >= 1.

Conventions:
- The terms of A100035 are positive integers (offset 1, a(1) = 1, keyword nonn), so the greatest number
  below `a(n)` is sought among `1, ..., a(n) - 1`.
- Reading of A100035's %N: `a(n+1)` is a number `y` that has not occurred earlier as a neighbor of a term
  equal to `a(n)`, that is, the unordered pair `{a(n), y}` is not of the form `{a(i), a(i+1)}` with
  `i + 1 ≤ n`. `IsAdj l x y` says that `{x, y}` is such a pair of adjacent entries of the list `l`
  (entries `l[i]` and `l[i+1]`, in either order).
- `pre n` is the list `[b(1), ..., b(n)]` of the first `n` terms and `b n` is its last entry, so `b n` is
  A100035(n) for `n ≥ 1`; `b 0 = 0` is a junk value outside the offset.
- `nextTerm l`, with `x` the last entry of `l`: if some `y` with `1 ≤ y < x` gives a pair `{x, y}` that
  is not adjacent in `l`, the greatest such `y` (the `sSup` of a nonempty finite set of naturals);
  otherwise the least `y > x` with `{x, y}` not adjacent in `l` (an `sInf`). That last set is never
  empty: `l` has only finitely many adjacent pairs, and no `y` larger than every entry of `l` is in one.
- `s n` is A100039(n). `s 1` is the position of the fourth occurrence of `1` in A100035, as in the
  entry's example `a(1) = 22` (`Nat.nth p 3` is the fourth number satisfying `p`, counted from `0`;
  positions are `m ≥ 1`, since `b 0 = 0 ≠ 1`). For `n ≥ 1`, `s (n + 1)` is the least `m > s n` with
  `b m = n + 1`: by %C, a(n+1) is the least `m ≥ a(n)` with A100035(m) = n + 1, and `m = a(n)` itself
  is excluded because A100035(a(n)) = n (for `n = 1`, a(1) is a position of `1`).
-/

namespace OMA.S_oeis_a100039

/-- `IsAdj l x y`: the unordered pair `{x, y}` is `{l[i], l[i+1]}` for two adjacent entries of `l`. -/
def IsAdj (l : List ℕ) (x y : ℕ) : Prop :=
  ∃ i : ℕ, (l[i]? = some x ∧ l[i + 1]? = some y) ∨ (l[i]? = some y ∧ l[i + 1]? = some x)

open Classical in
/-- The term of A100035 after its first terms `l` (whose last entry is `x`): the greatest `y` with
`1 ≤ y < x` such that `{x, y}` is not adjacent in `l`, if there is one; otherwise the least `y > x`
such that `{x, y}` is not adjacent in `l`. -/
noncomputable def nextTerm (l : List ℕ) : ℕ :=
  if ∃ y : ℕ, 1 ≤ y ∧ y < l.getLastD 0 ∧ ¬ IsAdj l (l.getLastD 0) y then
    sSup {y : ℕ | 1 ≤ y ∧ y < l.getLastD 0 ∧ ¬ IsAdj l (l.getLastD 0) y}
  else
    sInf {y : ℕ | l.getLastD 0 < y ∧ ¬ IsAdj l (l.getLastD 0) y}

/-- `pre n` is the list `[b(1), ..., b(n)]` of the first `n` terms of A100035 (with `b(1) = 1`). -/
noncomputable def pre : ℕ → List ℕ
  | 0 => []
  | n + 1 => pre n ++ [if n = 0 then 1 else nextTerm (pre n)]

/-- `b n` is A100035(n) for `n ≥ 1`: the last entry of `pre n`. -/
noncomputable def b (n : ℕ) : ℕ := (pre n).getLastD 0

/-- `s n` is A100039(n): `s 1` is the position of the fourth occurrence of `1` in A100035, and for
`n ≥ 1`, `s (n + 1)` is the least position `m > s n` with `b m = n + 1`. -/
noncomputable def s : ℕ → ℕ
  | 0 => 0
  | n + 1 => if n = 0 then Nat.nth (fun m => b m = 1) 3 else sInf {m : ℕ | s n < m ∧ b m = n + 1}

theorem main : ∀ n : ℕ, 1 ≤ n → s n = 2 * n ^ 2 + 7 * n + 13 := by
  sorry

end OMA.S_oeis_a100039

import Mathlib

/-!
# A100036: the first position of each natural number in A100035

Source: https://oeis.org/A100036 (the underlying sequence: https://oeis.org/A100035)
Credit: @avivorly

A100035 (Reinhard Zumkeller), %N: a(n+1) occurs not earlier as a neighbor of terms = a(n): either it is
the greatest number < a(n) or, if no such number exists, the smallest number > a(n); a(1) = 1.

A100036, %N: a(n) = smallest m such that A100035(m) = n.
%C: Smallest positions of occurrences of the natural numbers as subsequence in A100035;
A100035(a(n)) = n and A100035(m) <> n for m < a(n).

Claim (Ralf Stephan, May 15 2007, the %F line of A100036): Conjecture: a(n) = partial sums of sequence
[1,1,1,2,2,5,2,9,2,13,2,17,2,21,2,25,2,29,2,33,...2,n/2-7,2,...].
That is, A100036(n) = d(1) + ... + d(n) for every n >= 1, with the differences `d` below. (The %F line
goes on to restate this through A096376; that restatement is not formalized here.)

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
- `a n` is A100036(n): the least position `m ≥ 1` with `b m = n` (%N; positions start at the offset 1).
- The differences `d`: the listed sequence is `d(1), d(2), ... = 1, 1, 1, 2, 2, 5, 2, 9, ..., 2, 33`, that is
  `d(1) = d(2) = d(3) = 1`, `d(4) = 2`, and for `i ≥ 5`, `d(i) = 2` for odd `i` and `d(i) = 2i - 7` for even
  `i` (`d(6) = 5`, `d(8) = 9`, ..., `d(20) = 33`). The written general term `n/2-7` does not fit the listed
  values (at place 20 it would give 3, not 33); `2i - 7` is what every listed entry gives, and it is the
  reading used here. `d 0` is never used.
-/

namespace OMA.S_oeis_a100036

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

/-- `a n` is A100036(n): the least position `m ≥ 1` with `b m = n`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m : ℕ | 1 ≤ m ∧ b m = n}

/-- The listed differences: `d 1 = d 2 = d 3 = 1`, `d 4 = 2`, and for `i ≥ 5`, `d i = 2` for odd `i`
and `d i = 2 * i - 7` for even `i`. -/
def d (i : ℕ) : ℕ :=
  if i ≤ 3 then 1 else if i = 4 then 2 else if i % 2 = 1 then 2 else 2 * i - 7

theorem main : ∀ n : ℕ, 1 ≤ n → a n = ∑ i ∈ Finset.Icc 1 n, d i := by
  sorry

end OMA.S_oeis_a100036

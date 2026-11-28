import Mathlib

/-!
# OEIS A107793: relabeled and shortened, the sequence is a shifted version of A275925

Source: https://oeis.org/A107793 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Roger L. Bagula, Jun 11 2005; edited by N. J. A. Sloane, Jun 21 2018), offset 0:
Differences between successive indices of 1's in the ternary tribonacci sequence A305390.
Data: 4, 5, 3, 5, 4, 5, 4, 5, 3, 5, ... (100 terms). Comment: Conjecture (N. J. A. Sloane,
Jun 22 2018) This is a disguised form of A275925. More precisely, if we replace the 5's by 6's
and the 4's by 5's, and ignore the first two terms, we appear to get a sequence which is a
shifted version of A275925.
A305390 (N. J. A. Sloane, Jun 21 2018), offset 0: A ternary tribonacci sequence: define the
morphism f: 1 -> 2, 2 -> 3, 3 -> 1,2,3; let S[k] be result of applying f k times to 1, for
k = 0,1,2,...; sequence gives limit S[3k+1] as k -> oo.
A275925 (N. J. A. Sloane, Aug 29 2016), offset 1: Trajectory of 3 under repeated application of
the morphism sigma: 3 -> 3656, 5 -> 365656, 6 -> 3656656.

Formalization notes:
* Words are lists of naturals; f and sigma act letter by letter (`List.flatMap`), leaving letters
  outside their alphabets alone.
* A305390 is `u`: its letter i is read off S[3i+1], which has more than i letters and is a prefix
  of every later S[3k+1] (so this is the limit word).
* A107793 is `d`: d(n) is the (n+1)-st minus the n-th index (from 0) of a 1 in `u`; the differences
  do not depend on the indexing.
* A275925 is `t`, indexed from 0: t(j) = A275925(j+1), the letter j of sigma^(j+1)(3), a prefix of
  the trajectory.
* g replaces the 5's by 6's and the 4's by 5's; M(i) = g(d(i+2)) ignores the first two terms.
* A shifted version of A275925: some integer s with M(i) = t(i+s) for every i with i + s >= 0.
  Both directions of shift are allowed, so the offset of A275925 plays no role. `main` is the
  conjecture in this form.
-/

namespace OMA.S_oeis_a107793

/-- The morphism f of A305390: 1 -> 2, 2 -> 3, 3 -> 1,2,3 (other letters are left alone). -/
def f : ℕ → List ℕ
  | 1 => [2]
  | 2 => [3]
  | 3 => [1, 2, 3]
  | c => [c]

/-- S[k]: the result of applying f k times to the word 1. -/
def S (k : ℕ) : List ℕ := (fun w : List ℕ => w.flatMap f)^[k] [1]

/-- A305390 (offset 0), the limit of S[3k+1]: its letter i is read off S[3i+1], which has more
than i letters and is a prefix of every later S[3k+1]. -/
def u (i : ℕ) : ℕ := (S (3 * i + 1)).getD i 0

/-- A107793 (offset 0): the differences between successive indices of 1's in A305390. -/
noncomputable def d (n : ℕ) : ℕ :=
  Nat.nth (fun i => u i = 1) (n + 1) - Nat.nth (fun i => u i = 1) n

/-- The morphism of A275925: 3 -> 3656, 5 -> 365656, 6 -> 3656656 (other letters left alone). -/
def sigma : ℕ → List ℕ
  | 3 => [3, 6, 5, 6]
  | 5 => [3, 6, 5, 6, 5, 6]
  | 6 => [3, 6, 5, 6, 6, 5, 6]
  | c => [c]

/-- T[k]: the result of applying sigma k times to the word 3. -/
def T (k : ℕ) : List ℕ := (fun w : List ℕ => w.flatMap sigma)^[k] [3]

/-- A275925, indexed from 0 here (t j = A275925(j+1)): the trajectory of 3 under sigma, read off
T[j+1], which has more than j letters and is a prefix of every later T[k]. -/
def t (j : ℕ) : ℕ := (T (j + 1)).getD j 0

/-- Replace the 5's by 6's and the 4's by 5's. -/
def g (x : ℕ) : ℕ := if x = 5 then 6 else if x = 4 then 5 else x

/-- A107793 relabeled, with its first two terms ignored. -/
noncomputable def M (i : ℕ) : ℕ := g (d (i + 2))

/-- Sloane's conjecture: M is a shifted version of A275925. -/
theorem main : ∃ s : ℤ, ∀ i j : ℕ, (j : ℤ) = (i : ℤ) + s → M i = t j := by
  sorry

end OMA.S_oeis_a107793

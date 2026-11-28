import Mathlib

/-!
# OEIS A286343: the greatest index of n in a Fibonacci-like sequence is A199088(n)

Source: https://oeis.org/A286343 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Rémy Sigrist, May 07 2017), offset 1: For n>0, let b(n) = greatest index of n in any
Fibonacci-like sequence containing n. This sequence is the ordinal transform of b. A Fibonacci-like
sequence f satisfies f(n+2) = f(n+1) + f(n), and is uniquely identified by its two initial terms
f(0) and f(1). For any n>0, b(n) >= 2 (as n appears at index 2 in the Fibonacci-like sequence with
initial terms n and 0). Conjecturally, for any n>1, b(n) = A199088(n).
A199088 (Casey Mongoven), offset 0: Excluding the two leftmost columns - the seeds - in the
monotonic justified array of all positive Fibonacci sequences (A160271), the lowest column index
which contains n in the smallest row which contains n (A199087). Data: 2, 2, 4, 5, 4, 6, 5, 4, ...
A160271 (Clark Kimberling): Monotonic justified array of all positive Fibonacci sequences. Every
pair a,b of nonnegative integers occurs in a row. If a>b, then a is in column 1 and b in column 2.
Each row begins with integers a,b satisfying a>b>=0. The rows are ordered by the following
relation on the first two terms a,b and c,d: (a,b)<(c,d) if and only there exists N such that
aF(n)+bF(n+1)<cF(n)+dF(n+1) for every n>=N, where F(n)=A000045(n). In terms of r(1)=a and r(2)=b,
the remaining terms of a row are determined by r(n)=r(n-1)+r(n-2). (Its listing also has a 0th row
of zeros, which contains no positive n.)

Formalization notes:
* `fib2 a b` is the Fibonacci-like sequence with f(0) = a and f(1) = b. The initial terms are
  nonnegative integers, as in the entry (with integer initial terms every index would occur, since
  F(k-1) and F(k) are coprime).
* `bIdx n` is b(n), the greatest k with f(k) = n over all initial terms a, b (`sSup`; the set is
  bounded for n >= 1).
* The rows of A160271 are the sequences `fib2 a b` with a > b >= 0; its columns are numbered from
  0, so the seeds are columns 0 and 1 and the entry in column k of row (a, b) is f(k), matching
  A199088(1) = 2. `rowLt a b c d` is Kimberling's order on rows, with `Nat.fib`.
* `IsSmallestRow n a b`: (a, b) is a row containing n that precedes every other row containing n.
  `A199088 n` is the least k >= 2 with f(k) = n in such a row.
* `main` states the conjecture for every n >= 2.
-/

namespace OMA.S_oeis_a286343

/-- The Fibonacci-like sequence with initial terms f(0) = a and f(1) = b. -/
def fib2 (a b : ℕ) : ℕ → ℕ
  | 0 => a
  | 1 => b
  | k + 2 => fib2 a b k + fib2 a b (k + 1)

/-- b(n): the greatest index of n in any Fibonacci-like sequence containing n. -/
noncomputable def bIdx (n : ℕ) : ℕ := sSup {k : ℕ | ∃ a b : ℕ, fib2 a b k = n}

/-- Kimberling's order on the rows of A160271: (a, b) < (c, d) when
a F(m) + b F(m+1) < c F(m) + d F(m+1) for every m from some point on. -/
def rowLt (a b c d : ℕ) : Prop :=
  ∃ N : ℕ, ∀ m : ℕ, N ≤ m → a * Nat.fib m + b * Nat.fib (m + 1) < c * Nat.fib m + d * Nat.fib (m + 1)

/-- (a, b) is the smallest row of A160271 that contains n (A199087). -/
def IsSmallestRow (n a b : ℕ) : Prop :=
  b < a ∧ (∃ k, fib2 a b k = n) ∧
    ∀ c d : ℕ, d < c → (∃ k, fib2 c d k = n) → (c, d) ≠ (a, b) → rowLt a b c d

/-- A199088(n): the lowest column index k >= 2 holding n in the smallest row containing n. -/
noncomputable def A199088 (n : ℕ) : ℕ :=
  sInf {k : ℕ | 2 ≤ k ∧ ∃ a b : ℕ, IsSmallestRow n a b ∧ fib2 a b k = n}

/-- The conjecture (Rémy Sigrist): b(n) = A199088(n) for every n > 1. -/
theorem main : ∀ n : ℕ, 2 ≤ n → bIdx n = A199088 n := by
  sorry

end OMA.S_oeis_a286343

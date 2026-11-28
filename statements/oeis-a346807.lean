import Mathlib

/-!
# OEIS A346807: Wu's conjecture: a(n) = n + 64 for n >= 8

Source: https://oeis.org/A346807 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (David Consiglio, Jr., Aug 04 2021), offset 1: Numbers that are the sum of ten squares in eight or more
ways. The formula section states: a(n) = n + 64 for n >= 8 (conjectured). (Chai Wah Wu, Dec 05 2023)

Formalization notes:
* A way to write n as a sum of ten squares is a partition of n into ten nonzero
  squares, that is, a multiset of ten positive integers whose squares sum to n (an element
  of `(Finset.Icc 1 n).sym 10`); `ways n` counts them, and the terms are the n with
  `8 <= ways n`.
* a(n) is the term of index n - 1 (from 0) of the terms in increasing order (`Nat.nth`), so
  a(1) is the least term, matching offset 1.
* `main` states the conjecture as worded: a(n) = n + 64 for every n >= 8.
* Controls proved in the proof file: a(1..9) = 58, 61, 64, 66, 67, 69, 70, 72, 73, as in the entry's data.
-/

namespace OMA.S_oeis_a346807

/-- The number of ways to write n as a sum of ten positive squares: the number of multisets of
ten positive integers whose squares sum to n. -/
def ways (n : ℕ) : ℕ :=
  (((Finset.Icc 1 n).sym 10).filter
    (fun s : Sym ℕ 10 => ((s : Multiset ℕ).map (· ^ 2)).sum = n)).card

/-- The terms of A346807: the numbers that are the sum of ten squares in eight or more ways. -/
def S : Set ℕ := {n | 8 ≤ ways n}

/-- A346807(n), offset 1: the n-th term in increasing order. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth (fun m => m ∈ S) (n - 1)

/-- Wu's conjecture: a(n) = n + 64 for n >= 8. -/
theorem main :
    ∀ n : ℕ, 8 ≤ n → a n = n + 64 := by
  sorry

end OMA.S_oeis_a346807

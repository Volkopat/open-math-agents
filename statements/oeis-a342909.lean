import Mathlib

/-!
# A342909: a(1)=1. Thereafter, if a(n) is a novel term a(n+1) = number of prior terms > a(n); otherwise a(n+1) = number of prior terms <= a(n).

Source: https://oeis.org/A342909
Credit: @agchua

The entry is by David James Sycamore, Mar 28 2021 (offset 1; data 1, 0, 1, 2, 0, 1, 4, 0, 2, 7, 0, 3, 2, 9, 0,
4, 13, 0, 5, 3, 13, 20, 0, 6, 5, 18, 1, 10, 4, 18, 28, ...). Its comment line, verbatim:
  The definition implies that the sequence is infinite, and a(n+1) < n for all n. Conjecture:
  Zero occurs infinitely many times.

Formalisation. As in the example of the entry, the prior terms of a(n) are a(1), ..., a(n-1),
and a(n) is novel when it differs from all of them. nextVal g n is the term that follows the
n-th term when g i is the i-th term for 1 <= i <= n. G k holds the terms a(1), ..., a(k+1) at
the indices 1, ..., k+1, and a n = G (n-1) n; the value a 0 is not used. These definitions give
the listed data. That the sequence is infinite means that a(n) is defined for every n >= 1,
which the definition provides. The theorem states a(n+1) < n for all n >= 1, and that zero
occurs infinitely many times.
-/

namespace OMA.S_oeis_a342909

/-- The term that follows the n-th term, where g i is the i-th term for 1 <= i <= n: if g n
is novel (no prior term g 1, ..., g (n-1) equals it), the number of prior terms > g n; otherwise
the number of prior terms <= g n. -/
def nextVal (g : ℕ → ℕ) (n : ℕ) : ℕ :=
  if ((Finset.Ico 1 n).filter (fun i => g i = g n)).card = 0 then
    ((Finset.Ico 1 n).filter (fun i => g n < g i)).card
  else ((Finset.Ico 1 n).filter (fun i => g i ≤ g n)).card

/-- G k holds the terms a(1), ..., a(k+1) at the indices 1, ..., k+1. -/
def G : ℕ → ℕ → ℕ
  | 0 => fun i => if i = 1 then 1 else 0
  | k + 1 => Function.update (G k) (k + 2) (nextVal (G k) (k + 1))

/-- A342909: a(n) for n >= 1. -/
def a (n : ℕ) : ℕ := G (n - 1) n

/-- a(n+1) < n for all n >= 1, and zero occurs infinitely many times. -/
theorem main : (∀ n : ℕ, 1 ≤ n → a (n + 1) < n) ∧ (∀ N : ℕ, ∃ n : ℕ, N < n ∧ a n = 0) := by
  sorry

end OMA.S_oeis_a342909

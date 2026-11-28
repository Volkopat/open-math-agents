import Mathlib

/-!
# A232656: The number of pairs of numbers below n that, when generating a Fibonacci-like sequence modulo n, contain zeros.

Source: https://oeis.org/A232656
Credit: @agchua

Formula line of A232656 (Logan J. Kleinwaks, Oct 28 2017):
  Conjecture: a(n) = Sum_{d|n} phi(d)*A001177(d), where phi = Euler's totient function (A000010).

The sequence A232656 has offset 1, and A001177 (Fibonacci entry points, least k >= 1 such that
d divides F_k = Nat.fib k) also has offset 1. Thus the conjecture is stated for all n >= 1.
Note: A232656 also lists the same formula without the word Conjecture (Richard L. Ollerton,
May 09 2021), but no proof is given in the entry.
-/

namespace OMA.S_oeis_a232656

/-- The Fibonacci-like sequence starting with (x, y): u_0 = x, u_1 = y, u_{k+2} = u_k + u_{k+1}. -/
def fibLike (x y : ℕ) : ℕ → ℕ
  | 0 => x
  | 1 => y
  | k + 2 => fibLike x y k + fibLike x y (k + 1)

open scoped Classical in
/-- A232656(n): the number of pairs (x, y) with 0 <= x, y < n whose Fibonacci-like sequence
contains a multiple of n (i.e., a zero modulo n). -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.range n ×ˢ Finset.range n).filter (fun p => ∃ k : ℕ, n ∣ fibLike p.1 p.2 k)).card

open scoped Classical in
/-- A001177(d): the Fibonacci entry point of d, i.e., the least k >= 1 such that d divides F_k. -/
noncomputable def entryPoint (d : ℕ) : ℕ :=
  if h : ∃ k : ℕ, 1 ≤ k ∧ d ∣ Nat.fib k then Nat.find h else 0

/-- Conjecture of Logan J. Kleinwaks (Oct 28 2017): a(n) = Sum_{d|n} phi(d) * A001177(d)
for all n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    a n = ∑ d ∈ n.divisors, Nat.totient d * entryPoint d := by
  sorry

end OMA.S_oeis_a232656

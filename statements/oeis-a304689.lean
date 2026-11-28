import Mathlib

/-!
# A304689: Number of nonnegative integers k such that n - F(k)*F(k+1) is positive and squarefree, where F(k) denotes the k-th Fibonacci number A000045(k).

Source: https://oeis.org/A304689
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A304689 (Zhi-Wei Sun, May 17 2018): a(n) > 0 for all n > 0, and a(n) = 1 only for
n = 1, 10, 90, 66690, 67452, 22756020.

Conventions:
* The sequence has offset 1 (data 1, 2, 3, 2, 2, 2, 4, 3, 2, 1, 3, 3, ...). `a n` is the number
  of natural numbers k >= 0 with F(k)*F(k+1) < n (so that n - F(k)*F(k+1) is positive) and
  n - F(k)*F(k+1) squarefree; F is `Nat.fib` (F(0) = 0, F(1) = 1). The natural subtraction
  is exact under the condition F(k)*F(k+1) < n.
* Squarefree is Mathlib `Squarefree` on natural numbers (1 is squarefree).
* The set of such k is finite for every n, so `Set.ncard` is its number of elements.
* Both parts of the conjecture are stated for every n >= 1. The second part is rendered
  literally as an only-if: a(n) = 1 implies n is one of the six listed values.
-/

namespace OMA.S_oeis_a304689

/-- A304689: number of k >= 0 with n - F(k)*F(k+1) positive and squarefree. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {k : ℕ | Nat.fib k * Nat.fib (k + 1) < n ∧
    Squarefree (n - Nat.fib k * Nat.fib (k + 1))}

/-- The conjecture of Sun: a(n) > 0 for all n > 0, and a(n) = 1 only for
n = 1, 10, 90, 66690, 67452, 22756020. -/
theorem main : ∀ n : ℕ, 0 < n →
    0 < a n ∧ (a n = 1 → n ∈ ({1, 10, 90, 66690, 67452, 22756020} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a304689

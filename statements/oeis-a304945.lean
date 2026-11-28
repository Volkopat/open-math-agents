import Mathlib

/-!
# A304945: Number of nonnegative integers k such that n - k*L(k) is positive and squarefree, where L(k) denotes the k-th Lucas number A000032(k).

Source: https://oeis.org/A304945
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A304945 (Zhi-Wei Sun, May 22 2018): a(n) > 0 for all n
> 0, and a(n) = 1 only for n = 1, 4, 5, 9, 10, 24, 28, 64, 100, 104, 136, 153, 172, 176, 344, 496,
856, 928, 1036, 1084, 1216, 1860.

Conventions:
* The sequence has offset 1 (data 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, ...). `a n` is the number of
  natural numbers k such that n - k*L(k) is positive and squarefree, where L(k) is the k-th Lucas
  number, exactly as in the OEIS name.
* L(k) is the k-th Lucas number A000032 (L(0) = 2, L(1) = 1, L(k+2) = L(k+1) + L(k)); it is the
  helper `L`, written as 2*F(k+1) - F(k) with F = `Nat.fib` (this equals F(k-1) + F(k+1), and the
  natural subtraction is exact since F(k) <= 2*F(k+1)).
* `Positive` is the condition k*L(k) < n, under which the natural subtraction n - k*L(k) is exact.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a304945

/-- The k-th Lucas number (A000032): 2, 1, 3, 4, 7, 11, ... -/
def L (k : ℕ) : ℕ := 2 * Nat.fib (k + 1) - Nat.fib k

/-- The condition in the name of A304945 on a tuple, for a given n. -/
def P (n : ℕ) (k : ℕ) : Prop :=
  k * L k < n ∧ Squarefree (n - k * L k)

/-- A304945: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ | P n t}

/-- The conjecture recorded in A304945. -/
theorem main : ∀ n : ℕ, 0 < n → ((0 < n → 0 < a n) ∧ (a n = 1 →
      n ∈ ({1, 4, 5, 9, 10, 24, 28, 64, 100, 104, 136, 153, 172, 176, 344, 496, 856, 928,
        1036, 1084, 1216, 1860} : Finset ℕ))) := by
  sorry

end OMA.S_oeis_a304945

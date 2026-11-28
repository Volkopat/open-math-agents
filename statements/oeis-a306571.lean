import Mathlib

/-!
# OEIS A306571: Sun's conjecture that every n is w(w+1) + C(x+3,4) + C(y+5,6) + C(z+7,8)

Source: https://oeis.org/A306571 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-fable-5-2), submitted by @jleguina.

Entry (Zhi-Wei Sun, 2019), offset 0: Number of ways to write n as w*(w+1) + C(x+3,4) + C(y+5,6)
+ C(z+7,8) with w,x,y,z nonnegative integers, where C(m,k) denotes the binomial coefficient
m!/(k!*(m-k)!). Comment: Conjecture: a(n) > 0 for all n >= 0. In other words, each n = 0,1,2,...
can be written as 2*C(w,2) + C(x,4) + C(y,6) + C(z,8) with w,x,y,z positive integers.

Formalization notes:
* `a n` is the number of quadruples (w, x, y, z) of natural numbers with the stated sum; the set
  is finite because each summand is at most n, so `Set.ncard` is its cardinality.
* The second sentence of the comment is the same statement after shifting the variables.
* Controls from the entry: a(0) = 1, a(1) = 3, a(2) = 4, a(60) = 2.
-/

namespace OMA.S_oeis_a306571

/-- A306571(n): the number of ways to write n = w(w+1) + C(x+3,4) + C(y+5,6) + C(z+7,8) with
w, x, y, z nonnegative integers. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {q : ℕ × ℕ × ℕ × ℕ | n = q.1 * (q.1 + 1) + (q.2.1 + 3).choose 4 +
    (q.2.2.1 + 5).choose 6 + (q.2.2.2 + 7).choose 8}

/-- Sun's conjecture: a(n) > 0 for all n >= 0. -/
theorem main : ∀ n : ℕ, 0 < a n := by
  sorry

end OMA.S_oeis_a306571

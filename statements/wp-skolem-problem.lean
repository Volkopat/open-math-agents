import Mathlib

/-!
# Skolem problem

Source: https://en.wikipedia.org/wiki/Skolem_problem
Credit: @ishaanzee

The Skolem problem asks whether there is an algorithm that decides, given a constant-recursive
sequence (a sequence satisfying a linear recurrence with constant coefficients, given by its
coefficients and initial values), whether the sequence contains the value zero.

Formalization choices:
* Wikipedia notes the problem can be posed over the integers, the rationals or the algebraic
  numbers. We take the integer version, the standard one (the rational version reduces to it by
  clearing denominators).
* An instance is a pair of lists of integers `(c, x)`. With `k = c.length`, it denotes the
  sequence `u` with initial values `u i = x[i]` for `i < k` (missing entries are `0`) and
  `u (n + k) = ∑ i < k, c[i] * u (n + i)`. This is Mathlib's `LinearRecurrence.mkSol`. Every
  integer constant-recursive sequence arises from some instance.
* "There is an algorithm" is `ComputablePred` (Mathlib's computability theory), with the usual
  encoding of pairs of lists of integers. Wikipedia states that it is not known whether such an
  algorithm exists and gives no conjectured answer; we state the question as asked ("there is
  an algorithm"), so a proof of `main` answers it positively and a disproof negatively.
-/

namespace OMA.S_wp_skolem_problem

/-- The linear recurrence `u (n + k) = ∑ i < k, c[i] * u (n + i)` with `k = c.length`. -/
def recurrenceOf (c : List ℤ) : LinearRecurrence ℤ where
  order := c.length
  coeffs := fun i => c.get i

/-- The integer constant-recursive sequence with coefficients `p.1` and initial values `p.2`. -/
def seqOf (p : List ℤ × List ℤ) : ℕ → ℤ :=
  (recurrenceOf p.1).mkSol (fun i => p.2.getD i 0)

/-- **Skolem problem**: it is decidable, given an integer linear recurrence and its initial
values, whether the resulting sequence has a zero term. -/
theorem main : ComputablePred (fun p : List ℤ × List ℤ => ∃ n : ℕ, seqOf p n = 0) := by
  sorry

end OMA.S_wp_skolem_problem

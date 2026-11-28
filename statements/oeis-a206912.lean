import Mathlib

/-!
# OEIS A206912: the ranks of log(n + 1) among the harmonic sums grow by 1 or 2

Source: https://oeis.org/A206912 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, Feb 13 2012), offset 1: Position of log(n+1) when the partial sums of the
harmonic series are jointly ranked with the set {log(k+1)}; complement of A206911.
Conjecture: the difference sequence of A206912 consists of 1s and 2s; see Comments at A206911.
Data: 1, 3, 4, 6, 7, 9, 10, 12, 14, 15, 17, 18, ...
The example in A206911: let S(n)=1+1/2+1/3+...+1/n and L(n)=log(n+1). Then
L(1)<S(1)<L(2)<L(3)<S(2)<L(4)<L(5)<S(3)<L(6)<..., so that A206911=(2,5,8,...).

Formalization notes:
* `harmonic j` is Mathlib's harmonic number 1 + 1/2 + ... + 1/j, a rational number.
* `a n` is the rank of log(n + 1) when the harmonic sums H(j) (j >= 1) and the numbers log(k + 1)
  (k >= 1) are ranked together: the n numbers log 2, ..., log(n + 1) come at or before it, and so
  do the harmonic sums below it. No harmonic sum equals a number log(k + 1), since e^q is
  irrational for every nonzero rational q, so counting the sums strictly below gives the rank.
* "The difference sequence consists of 1s and 2s" is stated as: a(n + 1) - a(n) is 1 or 2 for
  every n >= 1.
-/

namespace OMA.S_oeis_a206912

/-- A206912(n): the rank of log(n + 1) when the harmonic sums H(j), j >= 1, and the numbers
log(k + 1), k >= 1, are ranked together. -/
noncomputable def a (n : ℕ) : ℕ :=
  n + Set.ncard {j : ℕ | 1 ≤ j ∧ (harmonic j : ℝ) < Real.log (n + 1)}

/-- The conjecture: every difference a(n + 1) - a(n) is 1 or 2. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a (n + 1) = a n + 1 ∨ a (n + 1) = a n + 2 := by
  sorry

end OMA.S_oeis_a206912

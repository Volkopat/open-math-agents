import Mathlib

/-!
# A270440: Least k such that binomial(k, 2) >= binomial(2*n, n).

Source: https://oeis.org/A270440
Credit: @vivanpoddar

The sequence (offset 0) begins 2, 3, 4, 7, 13, 23, 44, 84, 161, 313, ...
It is defined as in the name of the entry, as the least natural number k with
binomial(k, 2) >= binomial(2n, n).

Conjecture (Vaclav Kotesovec, Mar 23 2016): a(n) ~ 2^(n + 1/2) / (Pi*n)^(1/4).
Chai Wah Wu (Mar 23 2016): a(n) = ceiling(((8*binomial(2*n,n)+1)^(1/2)+1)/2); the above conjecture is
true asymptotically.
Both assertions are stated: the closed form for every n >= 0, and the asymptotic equivalence as
n tends to infinity (the quotient of the two sides tends to 1).
-/

namespace OMA.S_oeis_a270440

open Filter Asymptotics

/-- A270440: the least k with binomial(k, 2) >= binomial(2n, n). -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | (2 * n).choose n ≤ k.choose 2}

/-- The closed form and the asymptotic behaviour of A270440. -/
theorem main :
    (∀ n : ℕ, a n = ⌈(Real.sqrt (8 * ((2 * n).choose n : ℝ) + 1) + 1) / 2⌉₊) ∧
    (fun n : ℕ => (a n : ℝ)) ~[atTop]
      (fun n : ℕ => (2 : ℝ) ^ ((n : ℝ) + 1 / 2) / (Real.pi * (n : ℝ)) ^ ((1 : ℝ) / 4)) := by
  sorry

end OMA.S_oeis_a270440

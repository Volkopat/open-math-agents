import Mathlib

/-!
# A299406: Dirichlet series zeta(s) zeta(6s) / (zeta(2s) zeta(3s))
Source: https://oeis.org/A299406 (conjecture listed in the entry of Werner Schulte, Feb 20 2018)

Conjecture: a(n) = A008836(n) * A210826(n) for n >= 1.

Conventions.
* Dirichlet series are encoded as arithmetic functions (Dirichlet convolution = product of
  Dirichlet series). `powInd k` is the indicator of the positive k-th powers, whose Dirichlet
  series is zeta(k s); zeta itself is `ArithmeticFunction.zeta` cast to integers.
* A299406 is defined by its Dirichlet g.f.: Sum a(n)/n^s * zeta(2s) * zeta(3s) = zeta(s) * zeta(6s),
  i.e. a * powInd 2 * powInd 3 = zeta * powInd 6. (This determines a uniquely.)
* A210826 is defined by its Lambert g.f. Sum_{n>=1} b(n) x^n/(1-x^n) = Sum_{n>=1} x^(n^3), i.e.
  Sum_{d | n} b(d) = [n is a cube] for n >= 1, i.e. b * zeta = powInd 3. (This determines b uniquely.)
* A008836 is the Liouville function (-1)^Omega(n), Omega = number of prime factors with multiplicity.
The theorem quantifies over all sequences satisfying the two defining identities.
-/

namespace OMA.S_oeis_a299406

open ArithmeticFunction

/-- Indicator of the positive k-th powers (Dirichlet series zeta(k s)). -/
def powInd (k : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n => if n ≠ 0 ∧ ∃ m : ℕ, m ^ k = n then 1 else 0, by simp⟩

theorem main : ∀ a b : ArithmeticFunction ℤ,
    a * powInd 2 * powInd 3 = (ArithmeticFunction.zeta : ArithmeticFunction ℤ) * powInd 6 →
    b * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) = powInd 3 →
    ∀ n : ℕ, 0 < n → a n = (-1) ^ (cardFactors n) * b n := by
  sorry

end OMA.S_oeis_a299406

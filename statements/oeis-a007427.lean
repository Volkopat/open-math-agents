import Mathlib

/-!
# A007427: Moebius transform applied twice to sequence 1,0,0,0,....

Source: https://oeis.org/A007427
Credit: @rickmanelius

Conjecture (Ralf Stephan, Jul 05 2013): Dirichlet g.f. of |a(n)|: zeta(s)^2/zeta(2s)^2
(conjectured). (Michael Shamos: The conjecture is correct because
1+Sum_{e>=1} binomial(2,e)/p^(e*s) = (p^s+1)^2/p^2s, whose product over p is
zeta(s)^2/zeta(2s)^2.)

Formalization notes:
* Offset 1. The sequence 1,0,0,0,... is `delta`: delta(1) = 1 and delta(n) = 0 for n ≥ 2.
  The Moebius transform of a sequence b is the sequence n ↦ Sum_{d | n} mu(n/d) * b(d), with d
  running over `Nat.divisors n` and mu Mathlib's Moebius function `ArithmeticFunction.moebius`.
  The sequence is `a = moebiusTransform (moebiusTransform delta)`; equivalently
  a(n) = Sum_{d | n} mu(d) * mu(n/d), the formula of Benoit Cloitre in the entry. The data begin
  1, -2, -2, 1, -2, 4, -2, 0, 1, 4, -2, -2, -2, 4, 4, 0, ..., matching the entry. Index 0 lies
  outside the sequence (Mathlib has `Nat.divisors 0 = ∅`, so a 0 = 0) and the Dirichlet series
  below does not use it.
* The Dirichlet g.f. of |a(n)| is the series Sum_{n ≥ 1} |a(n)| / n^s: Mathlib's `LSeries` of the
  complex sequence n ↦ |a(n)| (its term at n = 0 is 0 by definition). The identity is claimed on
  the half-plane Re(s) > 1, where this series converges absolutely; that is the standard reading
  of a Dirichlet g.f. identity. `LSeries` is a `tsum`, which is 0 for a series that does not
  converge, so the statement also asserts the convergence (`LSeriesSummable`): the identity
  cannot hold through a junk value.
* zeta is Mathlib's `riemannZeta`, and zeta(2s) is `riemannZeta (2 * s)`. For Re(s) > 1 it does
  not vanish, so the division is the ordinary one.
-/

namespace OMA.S_oeis_a007427

/-- The sequence 1,0,0,0,... with offset 1. -/
def delta (n : ℕ) : ℤ := if n = 1 then 1 else 0

/-- The Moebius transform of a sequence b: n ↦ Sum_{d | n} mu(n/d) * b(d). -/
def moebiusTransform (b : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, ArithmeticFunction.moebius (n / d) * b d

/-- A007427: the Moebius transform applied twice to 1,0,0,0,.... -/
def a (n : ℕ) : ℤ := moebiusTransform (moebiusTransform delta) n

/-- Stephan's conjecture: for Re(s) > 1 the Dirichlet series Sum_{n ≥ 1} |a(n)| / n^s
converges, and its sum is zeta(s)^2 / zeta(2s)^2. -/
theorem main :
    ∀ s : ℂ, 1 < s.re →
      LSeriesSummable (fun n => ((|a n| : ℤ) : ℂ)) s ∧
        LSeries (fun n => ((|a n| : ℤ) : ℂ)) s = riemannZeta s ^ 2 / riemannZeta (2 * s) ^ 2 := by
  sorry

end OMA.S_oeis_a007427

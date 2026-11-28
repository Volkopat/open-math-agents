import Mathlib

/-!
# A306825: Primitive part of A001353(n).

Source: https://oeis.org/A306825
Credit: @agchua

Comment of A306825 (the entry is by Jianing Song, Mar 16 2019):
  Conjecturally there must be infinitely many primes p such that a(p) is prime, but no such p
  is known. [By the formula below, there is no such p. - Jianing Song, Oct 31 2024]
Offset 1, first terms 1, 4, 15, 14, 209, 13, 2911, 194, 2703, 181. Here A001353 is given by
A001353(0) = 0, A001353(1) = 1, A001353(n) = 4*A001353(n-1) - A001353(n-2), and the entry's
formula a(n) = Product_{d|n} A001353(d)^mu(n/d), with mu = A008683 the Moebius function, is
used as the definition (its values are integers; we take them in the rationals). The site's
text records that the conjecture is wrong: there is no prime p such that a(p) is prime. We
state exactly that, together with the failure of the conjecture (the set of such p is not
infinite).
-/

namespace OMA.S_oeis_a306825

/-- A001353: U(0) = 0, U(1) = 1, U(n+2) = 4*U(n+1) - U(n). -/
def U : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (n + 2) => 4 * U (n + 1) - U n

/-- A306825: a(n) = Product_{d|n} A001353(d)^mu(n/d), as a rational number. -/
noncomputable def a (n : ℕ) : ℚ :=
  ∏ d ∈ n.divisors, (U d : ℚ) ^ (ArithmeticFunction.moebius (n / d))

/-- The conjecture that infinitely many primes p have a(p) prime is false, and in fact no
prime p has a(p) prime. -/
theorem main :
    ¬ {p : ℕ | p.Prime ∧ ∃ q : ℕ, q.Prime ∧ a p = q}.Infinite ∧
      ∀ p : ℕ, p.Prime → ¬ ∃ q : ℕ, q.Prime ∧ a p = q := by
  sorry

end OMA.S_oeis_a306825

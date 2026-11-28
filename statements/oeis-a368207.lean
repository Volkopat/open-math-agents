import Mathlib

/-!
# A368207: Bacher numbers

Source: https://oeis.org/A368207

A368207 (offset 1) is the number a(n) of nonnegative representations n = w*x + y*z with
max(w, x) < min(y, z). Its comments carry the following conjectures; `main` is their conjunction.

* (1) and (2), Pontus von Brömssen, Dec 18 2023: *(1) a(n) >= sigma(n)/2, with equality if and
  only if n has no middle divisors, i.e., if and only if n is in A071561. (2) a(n)/sigma(n)
  converges to 1/2.*
* Chai Wah Wu, Dec 19 2023: *a(p^m) = sigma(p^m)/2 for odd m and all prime p > 2.
  a(p^m) = (sigma(p^m)-1)/2 + p^(m/2) for even m and all prime p. a(2^m) = sigma(2^m)/2 + 1/2
  for m odd.*

Conventions:
* A representation is a quadruple (w, x, y, z) of naturals. Since max(w, x) < min(y, z) forces
  y, z >= 1, every coordinate of a representation of n is at most n, so counting quadruples in
  `{0, ..., n}^4` counts all of them.
* A middle divisor of n (A071561) is a divisor d with sqrt(n/2) <= d < sqrt(2n), that is,
  n <= 2 d^2 and d^2 < 2n.
* The identities are multiplied by 2 to stay in ℕ: sigma(p^m) is odd for even m, so
  (sigma(p^m) - 1)/2 is exact, and 2 a = sigma - 1 + 2 p^(m/2) is the same statement.
-/

namespace OMA.S_oeis_a368207

open Filter Topology ArithmeticFunction

/-- A368207: the number of `(w, x, y, z)` with `w * x + y * z = n` and `max w x < min y z`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ
      Finset.range (n + 1)).filter
    (fun q => q.1 * q.2.1 + q.2.2.1 * q.2.2.2 = n ∧ max q.1 q.2.1 < min q.2.2.1 q.2.2.2)).card

/-- `n` has a middle divisor: a divisor `d` with `sqrt (n / 2) ≤ d < sqrt (2 * n)`. -/
def HasMiddleDivisor (n : ℕ) : Prop := ∃ d ∈ n.divisors, n ≤ 2 * d ^ 2 ∧ d ^ 2 < 2 * n

/-- Conjecture (1). -/
def Conj1 : Prop :=
  ∀ n : ℕ, 1 ≤ n → sigma 1 n ≤ 2 * a n ∧
    (2 * a n = sigma 1 n ↔ ¬ HasMiddleDivisor n)

/-- Conjecture (2). -/
def Conj2 : Prop :=
  Tendsto (fun n : ℕ => (a n : ℝ) / (sigma 1 n : ℝ)) atTop (𝓝 (1 / 2))

/-- The conjecture of Chai Wah Wu on prime powers. -/
def ConjWu : Prop :=
  (∀ p m : ℕ, p.Prime → 2 < p → Odd m → 2 * a (p ^ m) = sigma 1 (p ^ m)) ∧
  (∀ p m : ℕ, p.Prime → Even m → 2 * a (p ^ m) = sigma 1 (p ^ m) - 1 + 2 * p ^ (m / 2)) ∧
  (∀ m : ℕ, Odd m → 2 * a (2 ^ m) = sigma 1 (2 ^ m) + 1)

theorem main : Conj1 ∧ Conj2 ∧ ConjWu := by
  sorry

end OMA.S_oeis_a368207

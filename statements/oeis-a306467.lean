import Mathlib

/-!
# A306467: Let S(n)_k be the smallest positive integer t that t!_k is a multiple of n (t!_k is k-tuple factorial of t); then a(n) is the smallest k for which S(n)_k = n.

Source: https://oeis.org/A306467
Credit: @agchua

Comment lines of A306467 (the entry is by Lechoslaw Ratajczak, Feb 17 2019), verbatim:
  Conjecture: consecutive primes p satisfying the equation a(p+1) = 2 are consecutive elements
  of A005383 (primes p such that (p+1)/2 are also primes, for p > 3). The conjecture was
  checked for all primes < 10^4.
  Conjecture: consecutive primes p satisfying the equations a(p+1) = 2 and a(p+2) = 3 are
  consecutive elements of A036570 (primes p such that (p+1)/2 and (p+2)/3 are also primes).
  The conjecture was checked for all primes < 10^4.
Offset 1; data 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 2, 3, 5, 1, 4, ...

Formalisation. mfact k t is the k-tuple factorial t!_k = t (t - k) (t - 2k) ..., that is the
product of the j with 1 <= j <= t and j = t (mod k). S n k is the least t > 0 with n | mfact k t,
and a n is the least k > 0 with S n k = n (both sets are nonempty for n > 0, as S n n = n).
The two conjectures say that the primes p with a(p+1) = 2 are exactly the primes p > 3 for
which (p+1)/2 is prime, and that the primes p with a(p+1) = 2 and a(p+2) = 3 are exactly the
primes p for which (p+1)/2 and (p+2)/3 are (integers and) primes.
-/

namespace OMA.S_oeis_a306467

/-- The k-tuple factorial t!_k = t (t - k) (t - 2k) ...: the product of the j with 1 <= j <= t
and j = t (mod k). -/
def mfact (k t : ℕ) : ℕ := ∏ j ∈ (Finset.Icc 1 t).filter (fun j => j % k = t % k), j

/-- S(n)_k: the smallest positive integer t such that t!_k is a multiple of n. -/
noncomputable def S (n k : ℕ) : ℕ := sInf {t | 0 < t ∧ n ∣ mfact k t}

/-- a(n): the smallest k > 0 for which S(n)_k = n. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k | 0 < k ∧ S n k = n}

/-- The two conjectures of A306467 (Lechoslaw Ratajczak). -/
theorem main :
    (∀ p : ℕ, p.Prime → (a (p + 1) = 2 ↔ 3 < p ∧ ((p + 1) / 2).Prime)) ∧
    (∀ p : ℕ, p.Prime → (a (p + 1) = 2 ∧ a (p + 2) = 3 ↔
      ((p + 1) / 2).Prime ∧ 3 ∣ p + 2 ∧ ((p + 2) / 3).Prime)) := by
  sorry

end OMA.S_oeis_a306467

import Mathlib

/-!
# A350532: Triangle read by rows: T(n,k) is the number of degree-n polynomials over Z/2Z of the form f(x)^m for some m > 1 with exactly k nonzero terms; 1 <= k <= n + 1.

Source: https://oeis.org/A350532
Credit: @agchua

Comments of A350532 (unsigned; the entry is by Peter Kagey, Jan 03 2022):
  Conjecture: T(n,n+1) = 1 if and only if n is a Mersenne prime (A000668).
  Conjecture: T(2*n,2) = n.
  Conjecture: T(2*n,3) = (n^2 - n)/2 for n >= 1.
The triangle has offset 0, so n ranges over n >= 0 (the third conjecture says n >= 1).
T n k is the number of nonzero polynomials p over ZMod 2 of degree n with exactly k nonzero
coefficients such that p = f^m for some polynomial f and some m > 1; this set is finite, and
Set.ncard is its number of elements. A000668 lists the Mersenne primes, the primes of the form
2^q - 1. The three conjectures of the entry are stated together.
-/

namespace OMA.S_oeis_a350532

open Polynomial

/-- T(n, k): the number of degree-n polynomials over Z/2Z with exactly k nonzero terms that are
an m-th power of a polynomial for some m > 1. -/
noncomputable def T (n k : ℕ) : ℕ :=
  Set.ncard {p : (ZMod 2)[X] | p ≠ 0 ∧ p.natDegree = n ∧ p.support.card = k ∧
    ∃ f : (ZMod 2)[X], ∃ m : ℕ, 1 < m ∧ p = f ^ m}

/-- A000668: n is a Mersenne prime, that is, a prime of the form 2^q - 1. -/
def IsMersennePrime (n : ℕ) : Prop := n.Prime ∧ ∃ q : ℕ, n = 2 ^ q - 1

/-- The three conjectures of the entry: T(n,n+1) = 1 iff n is a Mersenne prime;
T(2n,2) = n; T(2n,3) = (n^2 - n)/2 for n >= 1. -/
theorem main :
    (∀ n : ℕ, T n (n + 1) = 1 ↔ IsMersennePrime n) ∧
    (∀ n : ℕ, T (2 * n) 2 = n) ∧
    (∀ n : ℕ, 1 ≤ n → T (2 * n) 3 = (n ^ 2 - n) / 2) := by
  sorry

end OMA.S_oeis_a350532

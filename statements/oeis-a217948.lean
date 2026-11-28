import Mathlib

/-!
# A217948: List of numbers 2n for which the riffle permutation permutes all except the first and last of the 2n cards.

Source: https://oeis.org/A217948
Credit: @agchua

Comments of A217948 (the entry is by N. J. A. Sloane, Nov 07 2012):
  Tiago Januario (email, Jan 12 2015; see also reference) conjectures that these terms are
  always one more than a prime. - N. J. A. Sloane, Mar 02 2015
  Conjecture: a(n) = A001122(n) + 1 (via an observation by Jules Beauchamp). - Bill McEachen,
  Jun 11 2026
As in the entry's comment and Mathematica program, the riffle permutation of 2n cards sends card
r to 2r-1 if r <= n and to 2r-2n if r > n; it fixes cards 1 and 2n, and 2n is a term when n >= 2
and the permutation has just one orbit on the 2n-2 cards 2, ..., 2n-1, that is, every one of these
cards is carried to every other one by some power of the permutation. A001122 lists the primes p
with primitive root 2, that is, the primes p modulo which 2 has multiplicative order p-1. Both
sequences are increasing, so a(n) = A001122(n) + 1 for all n says exactly that the terms are the
numbers p + 1 with p in A001122; it is stated in this form, which does not presuppose that the
sequences are infinite.
-/

namespace OMA.S_oeis_a217948

/-- The riffle permutation of 2n cards: card r goes to 2r-1 if r <= n and to 2r-2n if r > n. -/
def riffle (n r : ℕ) : ℕ := if r ≤ n then 2 * r - 1 else 2 * r - 2 * n

/-- m is a term of A217948: m = 2n with n >= 2, and the riffle permutation has a single orbit on
the cards 2, ..., 2n-1. -/
def IsTerm (m : ℕ) : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧ m = 2 * n ∧
    ∀ r ∈ Finset.Icc 2 (2 * n - 1), ∀ s ∈ Finset.Icc 2 (2 * n - 1), ∃ k : ℕ, (riffle n)^[k] r = s

/-- A001122: the primes with primitive root 2. -/
noncomputable def IsA001122 (p : ℕ) : Prop := p.Prime ∧ orderOf (2 : ZMod p) = p - 1

/-- The two conjectures: every term is one more than a prime, and the terms are exactly the
numbers p + 1 with p in A001122. -/
theorem main : (∀ m : ℕ, IsTerm m → (m - 1).Prime) ∧
    (∀ m : ℕ, IsTerm m ↔ ∃ p : ℕ, IsA001122 p ∧ m = p + 1) := by
  sorry

end OMA.S_oeis_a217948

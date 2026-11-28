import Mathlib

/-!
# A117964: the 1s of A117963 mod 2

Source: https://oeis.org/A117964
Credit: @avivorly

A117964: a(n) = A117963(n) mod 2.

A117963: Antidiagonal sums of a Legendre-binomial triangle for p = 3. Formula in the entry:
a(n) = Sum_{k=0..floor(n/2)} L(C(n-k,k)/3) where L(j/p) is the Legendre symbol of j and p.

A081601: Numbers m such that 3 does not divide Sum_{k=0..m} binomial(2k,k) = A006134(m).

Conjecture (Antti Karttunen, Jan 01 2023, in A117964):
a(2*A081601(n)) = a(1+2*A081601(n)) = 1. [Conjectured, also these two formulas together seem to give the
positions of all 1's]

Conventions:
- `legendreSym 3 j` is Mathlib's Legendre symbol of `j` and the prime `3` (the instance `Fact (Nat.Prime 3)` is
  Mathlib's `Nat.fact_prime_three`): it is `0` if `3 ∣ j`, `1` if `j ≡ 1` and `-1` if `j ≡ 2 (mod 3)`.
- `A117963 n` sums over `k ∈ Finset.range (n / 2 + 1)`, that is `k = 0..floor(n/2)`; there `k ≤ n`, so the natural
  subtraction `n - k` is exact. Both sequences have offset `0`.
- `a n := A117963 n % 2` uses `Int.emod`, so `a n` is `0` or `1` also when `A117963 n < 0`.
- `inA081601 m` is the defining property of A081601 (whose first term is `0`), with `Sum_{k=0..m}` as the sum over
  `k ∈ Finset.range (m + 1)`. Ranging over the terms `A081601(n)` is the same as ranging over all `m` with
  `inA081601 m`.
- `main` states both halves of the conjecture as one equivalence for every `n`: the direction from right to left is
  the two formulas (the 1s at `2m` and `2m + 1` for every term `m` of A081601), and the direction from left to right
  is the bracketed remark (these two formulas give the positions of all 1s).
-/

namespace OMA.S_oeis_a117964

/-- A117963: `Sum_{k=0..floor(n/2)} L(C(n-k,k)/3)`, with `L` the Legendre symbol mod `3`. -/
def A117963 (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n / 2 + 1), legendreSym 3 ((n - k).choose k : ℤ)

/-- A117964: `A117963(n) mod 2`, a value in `{0, 1}`. -/
def a (n : ℕ) : ℤ := A117963 n % 2

/-- `m` is a term of A081601: `3` does not divide `Sum_{k=0..m} binomial(2k,k)`. -/
def inA081601 (m : ℕ) : Prop :=
  ¬ (3 ∣ ∑ k ∈ Finset.range (m + 1), (2 * k).choose k)

theorem main :
    ∀ n : ℕ, a n = 1 ↔ ∃ m : ℕ, inA081601 m ∧ (n = 2 * m ∨ n = 2 * m + 1) := by
  sorry

end OMA.S_oeis_a117964

import Mathlib

/-!
# A005408: The odd numbers: a(n) = 2*n + 1.

Source: https://oeis.org/A005408
Credit: @mwhuss

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The statement formalized is the conjecture on the page (Gary W. Adamson, Sep 09 2012):
"Conjecture on primes with one coach (A216371) relating to the odd integers: iff an integer is
in A216371 (primes with one coach either of the form 4q-1 or 4q+1, (q > 0)); the top row of its
coach is composed of a permutation of the first q odd integers."

Faithfulness notes:
* "one coach" is defined in A216371 as A135303((p-1)/2) = 1, i.e. phi(p) = 2 * sord(2, p),
  where sord(2, p) is A003558: the least m > 0 such that 2^m == ±1 (mod 2n+1) with p = 2n+1.
* "top row of its coach" is read from the page's own example (prime 19, q = 5):
  19: [1, 9, 5, 7, 3] interpreted as (19-1) = 2^1*9, (19-9) = 2^1*5, (19-5) = 2^1*7,
  (19-7) = 2^2*3, (19-3) = 2^4*1 — i.e. the orbit of 1 under a ↦ odd part of (p - a).
  Checked by hand against every example on the page: 19 ↦ {1,9,5,7,3}, 11 ↦ {1,5,3},
  13 ↦ {1,3,5}, 37 ↦ {1,9,7,15,11,13,3,17,5}.
* "composed of a permutation of the first q odd integers" is set equality with
  {2*i + 1 | i < q}.
-/

namespace OMA.S_oeis_a005408

/-- A003558 (the suborder of 2 mod p): the least m > 0 such that 2^m ≡ ±1 (mod p).
For odd p existence follows from Fermat's little theorem; the def is total via dite. -/
noncomputable def sord2 (p : ℕ) : ℕ := by
  classical
  exact
    if h : (∃ m : ℕ, 0 < m ∧ (2 ^ m ≡ 1 [MOD p] ∨ 2 ^ m ≡ p - 1 [MOD p])) then
      Nat.find h
    else
      0

/-- One coach step (cf. the coach interpretation in A005408): a ↦ the odd part of (p - a). -/
def coachF (p : ℕ) (a : ℕ) : ℕ :=
  (p - a) / 2 ^ padicValNat 2 (p - a)

/-- The top row of the coach of p: the orbit of 1 under the coach step. -/
def topRow (p : ℕ) : Set ℕ :=
  { a | ∃ k : ℕ, (coachF p)^[k] 1 = a }

/-- The first q odd integers: {1, 3, …, 2q − 1}. -/
def firstOdds (q : ℕ) : Set ℕ :=
  { a | ∃ i < q, a = 2 * i + 1 }

/-- A216371: odd primes with one coach, i.e. primes p with A135303((p−1)/2) = 1,
i.e. φ(p) = 2 · sord(2, p). -/
def oneCoach (p : ℕ) : Prop :=
  Nat.Prime p ∧ p > 2 ∧ Nat.totient p = 2 * sord2 p

theorem main :
    ∀ p : ℕ,
      oneCoach p ↔
        ∃ q : ℕ, 0 < q ∧ (p = 4 * q - 1 ∨ p = 4 * q + 1) ∧ topRow p = firstOdds q := by
  sorry

end OMA.S_oeis_a005408

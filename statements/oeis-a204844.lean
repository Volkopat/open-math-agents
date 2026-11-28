import Mathlib

/-!
# A204844: Cyclic primes that are not absolute primes (A003459).

Source: https://oeis.org/A204844
Credit: @darealpandaboi

Conjecture: the sequence is finite, with 999331 being the last term (cf. A293142).

Translation notes.
* A cyclic (circular) prime: every cyclic rotation of its decimal digits is prime. Rotating the
  little-endian list Nat.digits 10 p gives the same rotations as rotating the written string.
* An absolute (permutable) prime: every rearrangement of its decimal digits is prime.
* This reproduces the listed data (checked by computer): below 10^7 there are exactly 33 terms,
  the last being 999331.
-/

namespace OMA.S_oeis_a204844

/-- Every cyclic rotation of the decimal digits of p is prime. -/
def IsCircularPrime (p : ℕ) : Prop :=
  ∀ i : ℕ, i < (Nat.digits 10 p).length → (Nat.ofDigits 10 ((Nat.digits 10 p).rotate i)).Prime

/-- Every rearrangement of the decimal digits of p is prime. -/
def IsAbsolutePrime (p : ℕ) : Prop :=
  ∀ l : List ℕ, l.Perm (Nat.digits 10 p) → (Nat.ofDigits 10 l).Prime

/-- The terms: cyclic primes that are not absolute primes. -/
def S : Set ℕ := {p : ℕ | p.Prime ∧ IsCircularPrime p ∧ ¬ IsAbsolutePrime p}

theorem main : S.Finite ∧ IsGreatest S 999331 := by
  sorry

end OMA.S_oeis_a204844

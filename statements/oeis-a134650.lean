import Mathlib

/-!
# A134650: Numbers that are the sum of two consecutive primes (i.e., in A001043) but are not the sum of two sums of two consecutive primes.

Source: https://oeis.org/A134650
Credit: @darealpandaboi

Conjecture: the sequence is finite (it may be complete).

Translation notes.
* A001043 lists prime(i) + prime(i+1), i >= 1; with Nat.nth Nat.Prime indexed from 0 this is
  Nat.nth Nat.Prime i + Nat.nth Nat.Prime (i + 1), i >= 0.
* A term is such a sum that is not x + y with x, y both such sums (x = y allowed).
* Only finiteness is conjectured; may be complete is a remark, not stated. This reading
  reproduces the listed data 5, 8, 12, 18, 52, 100, 946 and finds no other term up to 100000
  (checked by computer).
-/

namespace OMA.S_oeis_a134650

/-- m is the sum of two consecutive primes. -/
def IsConsecSum (m : ℕ) : Prop := ∃ i : ℕ, m = Nat.nth Nat.Prime i + Nat.nth Nat.Prime (i + 1)

theorem main :
    {m : ℕ | IsConsecSum m ∧ ¬ ∃ x y : ℕ, IsConsecSum x ∧ IsConsecSum y ∧ m = x + y}.Finite := by
  sorry

end OMA.S_oeis_a134650

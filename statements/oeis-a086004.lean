import Mathlib

/-!
# A086004: Primes which remain prime after one and after two and after three applications of
the rotate-and-add operation of A086002.

Source: https://oeis.org/A086004
Credit: @ShoQo

Conjecture 1: "Rotation and addition of primes with even numbers of digits never yields a prime."
(R. J. Mathar, Sep 17 2009: "Conjecture 1 is true because rotation for even numbers of the form
10^k*a+b yields 10^k*b+a, so rotation-and-add yields (10^k+1)*(a+b) ...")

Formalization notes:
* The rotation of A086002: for k with d decimal digits, swap the block of the first ⌊d/2⌋
  digits with the block of the last ⌊d/2⌋ digits; for odd d the center digit stays in place
  (rot(1234) = 3412, rot(12345) = 45312). With h = ⌊d/2⌋:
  rot(k) = (k mod 10^h) * 10^(d-h) + middle * 10^h + ⌊k / 10^(d-h)⌋, where the middle block
  ⌊k / 10^h⌋ mod 10^(d-2h) is empty (zero) when d is even.
* Only Conjecture 1 of the entry is stated here; its Conjecture 2 ("There are no 5-Rotation
  Cycle Primes") is not addressed by the comment that proves Conjecture 1.
-/

namespace OMA.S_oeis_a086004

/-- Number of decimal digits (A055642, with 0 having none). -/
def numDigits (k : ℕ) : ℕ := (Nat.digits 10 k).length

/-- The rotation of A086002: swap the first and last ⌊d/2⌋ digits. -/
def rot (k : ℕ) : ℕ :=
  let d := numDigits k
  let h := d / 2
  (k % 10 ^ h) * 10 ^ (d - h) + (k / 10 ^ h % 10 ^ (d - 2 * h)) * 10 ^ h + k / 10 ^ (d - h)

theorem main : ∀ p : ℕ, p.Prime → Even (numDigits p) → ¬ (p + rot p).Prime := by
  sorry

end OMA.S_oeis_a086004

import Mathlib

/-!
# A008590: Multiples of 8.

Source: https://oeis.org/A008590
Credit: @agchua

In the comments of A008590 (from Lechoslaw Ratajczak, Sep 03 2017):
  Conjecture: let gcd_2(b,c) be the second greatest common divisor and lcd_2(b,c) be the second
  least common divisor of not coprime integers b and c. Consecutive elements of this sequence
  (for a(n) > 0) are consecutive integers m for which both Sum_{k=1..m, gcd(k,m)<>1} gcd_2(k,m)
  and Sum_{k=1..m, gcd(k,m) <>1} lcd_2(k,m) are even numbers.

The common divisors of b and c are the divisors of g = gcd(b,c). So gcd_2(b,c) is the largest
divisor of g below g (the largest proper divisor of g), and lcd_2(b,c) is the least divisor of g
above 1, which is Nat.minFac g. The entry's examples agree: for m = 24 the two sums are 44 and 36.
The positive terms of A008590 are 8, 16, 24, ...; so the conjecture says that an integer m has both
sums even if and only if m is a multiple of 8.
Range: m = 1 is left out. For m = 1 no k has gcd(k,1) <> 1, both sums are empty (equal to 0), and
the literal claim fails only by this empty case; from m = 2 on every sum contains the term k = m.
-/

namespace OMA.S_oeis_a008590

/-- gcd_2(b,c): the second greatest common divisor of b and c, i.e. the largest proper divisor
of gcd(b,c). -/
def gcd2 (b c : ℕ) : ℕ := (Nat.properDivisors (Nat.gcd b c)).sup id

/-- lcd_2(b,c): the second least common divisor of b and c, i.e. the least divisor of gcd(b,c)
that is larger than 1. -/
def lcd2 (b c : ℕ) : ℕ := Nat.minFac (Nat.gcd b c)

/-- Sum_{k=1..m, gcd(k,m)<>1} gcd_2(k,m). -/
def S1 (m : ℕ) : ℕ := ∑ k ∈ (Finset.Icc 1 m).filter (fun k => Nat.gcd k m ≠ 1), gcd2 k m

/-- Sum_{k=1..m, gcd(k,m)<>1} lcd_2(k,m). -/
def S2 (m : ℕ) : ℕ := ∑ k ∈ (Finset.Icc 1 m).filter (fun k => Nat.gcd k m ≠ 1), lcd2 k m

/-- Conjecture (Ratajczak): for m >= 2, both sums are even if and only if m is a multiple of 8. -/
theorem main : ∀ m : ℕ, 2 ≤ m → (Even (S1 m) ∧ Even (S2 m) ↔ 8 ∣ m) := by
  sorry

end OMA.S_oeis_a008590

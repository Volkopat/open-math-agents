import Mathlib

/-!
# A140869: Triangle read by rows where T(m,n) = floor((2mn+m+n-2)/2), m >= n >= 1

Source: https://oeis.org/A140869
Credit: @xor2k

Formalizes the OEIS A140869 conjecture (Vincenzo Librandi, Nov 18 2012):
If h does not belong to the sequence, then 4*h+5 is prime.

Conventions:
* `T m n = (2*m*n + m + n - 2) / 2` with natural-number floor division; for m, n >= 1 the
  numerator is at least 2, so truncated subtraction never occurs.
* h belongs to the sequence iff h = T m n for some m >= n >= 1 (the triangle rows).
* h ranges over all natural numbers (h >= 0); the sequence consists of positive integers, and
  h = 0 is included (it is not a term and 4*0+5 = 5 is prime).
* Primality is Mathlib's `Nat.Prime`.
-/

namespace OMA.S_oeis_a140869

/-- The triangle entry `T(m,n) = floor((2mn+m+n-2)/2)`. -/
def T (m n : ℕ) : ℕ :=
  (2 * m * n + m + n - 2) / 2

/-- `h` is a term of A140869, i.e. `h = T(m,n)` for some `m >= n >= 1`. -/
def InSeq (h : ℕ) : Prop :=
  ∃ m n : ℕ, 1 ≤ n ∧ n ≤ m ∧ T m n = h

/-- If `h` is not a term of A140869, then `4*h+5` is prime. -/
theorem main :
    ∀ h : ℕ, ¬ InSeq h → Nat.Prime (4 * h + 5) := by
  sorry

end OMA.S_oeis_a140869

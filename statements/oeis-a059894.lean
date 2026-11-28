import Mathlib

/-!
# A059894: complement and reverse all but the most significant bit of n

Source: https://oeis.org/A059894
Credit: @jagong-cmu

Definition in the entry: complement and reverse the order of all but the most significant bit
in binary expansion of n. n = 1ab..yz -> 1ZY..BA = a(n), where A = 1-a, B = 1-b, ... .

The entry gives two conjectures (Ralf Stephan, Aug 21 2003 and Oct 05 2003):
* a(1) = 1, a(2n) = a(n) + 2^(floor(log_2(n))+1), a(2n+1) = a(n) + 2^floor(log_2(n)).
* A000120(a(n)) = A000120(A054429(n)) = A023416(n) + 1.

Conventions:
* Offset 1, as in the entry (data: 1, 3, 2, 7, 5, 6, 4, 15, 11, 13, ...). The value `a 0 = 1`
  is a by-product of the definition and is not used.
* `Nat.digits 2 n` is the binary expansion of `n`, least significant bit first, so its last
  entry is the most significant bit 1. `List.dropLast` removes that bit, `1 - b` complements a
  bit, and `List.reverse` reverses the order; then the bit 1 is put back on top.
* `floor(log_2(n))` is `Nat.log 2 n`.
* A000120(m) (binary weight) is `(Nat.digits 2 m).sum`. A023416(n) (number of 0's in the binary
  expansion of n) is `(Nat.digits 2 n).count 0`, for `n >= 1`.
* A054429 lists each block of 2^k numbers from 2^(k+1)-1 down to 2^k, so for
  2^k <= n < 2^(k+1) its value is 2^(k+1) - 1 - (n - 2^k), with k = floor(log_2(n)). The
  ℕ subtractions are exact for `n >= 1`.
* Both conjectures are stated for every `n >= 1`, as a conjunction.
-/

namespace OMA.S_oeis_a059894

/-- A059894: complement and reverse all but the most significant bit of `n`. -/
def a (n : ℕ) : ℕ :=
  Nat.ofDigits 2 ((((Nat.digits 2 n).dropLast).map (fun b => 1 - b)).reverse ++ [1])

/-- A000120: the binary weight of `m`. -/
def wt (m : ℕ) : ℕ := (Nat.digits 2 m).sum

/-- A023416: the number of 0's in the binary expansion of `n` (for `n >= 1`). -/
def zeros (n : ℕ) : ℕ := (Nat.digits 2 n).count 0

/-- A054429: each block 2^k, ..., 2^(k+1)-1 in reverse order. -/
def rev (n : ℕ) : ℕ := 2 ^ (Nat.log 2 n + 1) - 1 - (n - 2 ^ Nat.log 2 n)

/-- The two conjectures of the entry. -/
theorem main :
    a 1 = 1 ∧
      (∀ n : ℕ, 1 ≤ n →
        a (2 * n) = a n + 2 ^ (Nat.log 2 n + 1) ∧ a (2 * n + 1) = a n + 2 ^ Nat.log 2 n) ∧
      (∀ n : ℕ, 1 ≤ n → wt (a n) = wt (rev n) ∧ wt (rev n) = zeros n + 1) := by
  sorry

end OMA.S_oeis_a059894

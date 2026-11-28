import Mathlib

/-!
# A255683: Sum of the binary numbers whose digits are cyclic permutations of the binary expansion of n.

Source: https://oeis.org/A255683
Credit: @rickmanelius

Conjecture (Peter Bala, Mar 02 2015): For n >= 0 and 0 <= i <= 2^n - 1 we conjecture
a(2^n + i) = (2^(n+1) - 1)*A063787(i+1).

Here A063787 is the sequence with a(2^k) = k + 1 and a(2^k + i) = 1 + a(i) for k >= 0 and
0 < i < 2^k (offset 1: 1, 2, 2, 3, 2, 3, 3, 4, ...).

Formalization notes:
* `a n` is A255683(n) (offset 1). If n has L binary digits, its cyclic permutations are the L
  rotations of the digit string, counted with multiplicity, each read back in base 2 with
  leading zeros allowed. The example of the entry is 6 = 110, with rotations 110, 101, 011 and
  sum 6 + 5 + 3 = 14. The Mathematica programs sum RotateRight[w, r] over r = 1..L, so a
  repeated rotation counts again: 3 = 11 gives 3 + 3 = 6, and a(3) = 6 in the data.
* `Nat.digits 2 n` lists the binary digits of n least significant first. Summing
  `Nat.ofDigits 2 (l.rotate r)` over r < L, for this list l, gives the same sum as the entry:
  the reverse of `l.rotate r` is `l.reverse.rotate (L - r)` (and `l.rotate L = l`), so both
  sides run over the same L rotations of the usual digit string.
* `b n` is A063787(n), by its defining rule. For n >= 1 let k = `Nat.log 2 n`, so that
  2^k <= n < 2^(k+1). Then b(n) = k + 1 when n = 2^k, and otherwise n = 2^k + i with
  0 < i < 2^k and b(n) = 1 + b(i). The value b 0 = 0 is a junk value that the statement never
  reads, since it only uses b (i + 1).
* The ranges are the ones of the entry: every n >= 0 and every i with 0 <= i <= 2^n - 1
  (2^n >= 1, so the natural subtraction 2^n - 1 is exact, and so is 2^(n+1) - 1).
* Checked by computation: the 59 data terms of A255683 and the 1000 terms of its b-file agree
  with `a`, the 34 data terms of A063787 agree with `b`, and the conjecture holds for all
  n <= 17 and all i in range.
-/

namespace OMA.S_oeis_a255683

/-- A255683: the sum of the numbers whose binary digits are the cyclic rotations of the
binary digits of `n`, one for each of the `L` rotations, where `L` is the number of digits. -/
def a (n : ℕ) : ℕ :=
  ∑ r ∈ Finset.range (Nat.digits 2 n).length, Nat.ofDigits 2 ((Nat.digits 2 n).rotate r)

/-- A063787, by its definition: b(2^k) = k + 1, and b(2^k + i) = 1 + b(i) for 0 < i < 2^k.
The value at 0 is a junk value. -/
def b (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else if n = 2 ^ Nat.log 2 n then Nat.log 2 n + 1
  else 1 + b (n - 2 ^ Nat.log 2 n)
termination_by n
decreasing_by
  have h1 : 0 < 2 ^ Nat.log 2 n := pow_pos (by norm_num) _
  omega

/-- Bala's conjecture: for n >= 0 and 0 <= i <= 2^n - 1,
a(2^n + i) = (2^(n+1) - 1) * A063787(i + 1). -/
theorem main : ∀ n i : ℕ, i ≤ 2 ^ n - 1 → a (2 ^ n + i) = (2 ^ (n + 1) - 1) * b (i + 1) := by
  sorry

end OMA.S_oeis_a255683

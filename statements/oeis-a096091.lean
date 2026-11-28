import Mathlib

/-!
# A096091: Numbers n with property that largest number formed from digits of n (A004186(n)) is divisible by smallest number formed from digits of n (A004185(n)).

Source: https://oeis.org/A096091

Comments in the entry (Amarnath Murthy, Jun 22 2004):

  The number N = d*10^m*(10^k-1)/9 is a member for all m, k where 1 < d < 10, since the quotient
  is 10^m. E.g., for d = 7, m = 4, k = 8 we get N = 777777770000.
  Conjecture: There are infinitely many terms besides these.

Translation notes (please check):
* A004186(n) = arrange the decimal digits of n in decreasing order; A004185(n) = arrange the
  decimal digits of n in increasing order, then omit the (leading) zeros.
  `Nat.digits 10 n` is the little-endian digit list, and `Nat.ofDigits 10` reads a little-endian
  list back (zeros in the most significant places contribute nothing). The sorted digit lists
  are written as a counting sort: `sortedDigits order n` lists, for each digit d in `order`,
  as many copies of d as there are in n. With order 0,1,...,9 the little-endian list is
  nondecreasing, so the most significant digits are the largest: this is A004186. With order
  9,8,...,0 the most significant digits are the smallest and the zeros disappear: this is A004185.
* A term is a positive n with A004185(n) dividing A004186(n).
* The phrase: these, refers to the numbers d*10^m*(10^k-1)/9 with 1 < d < 10 and m, k arbitrary;
  this range of d is copied literally from the entry. The natural-number division (10^k-1)/9 is
  exact (it is the repunit with k ones) and 10^k - 1 never underflows.
* Infinitely many is stated as: beyond every bound N there is such a term.
* Remark for the reviewer: a later comment in the entry (Jon E. Schoenfield, Jul 26 2015) already
  asserts, without proof, that infinitely many terms remain. The witnesses used in the proof are
  the numbers 10^(N+2) + 5 (105, 1005, 10005, ...), for which A004186 = 51 * 10^(N+1) and
  A004185 = 15; they are not multiples of 10 and their nonzero digits are not all equal, so they
  are also outside the wider families mentioned in that later comment (in particular the case
  d = 1 is avoided as well).
-/

namespace OMA.S_oeis_a096091

/-- Counting sort of the decimal digits of `n`: for each digit `d` in `order`, as many copies
of `d` as occur among the decimal digits of `n`. -/
def sortedDigits (order : List ℕ) (n : ℕ) : List ℕ :=
  order.flatMap (fun d => List.replicate ((Nat.digits 10 n).count d) d)

/-- A004186: arrange the digits of n in decreasing order (little-endian list is increasing). -/
def A004186 (n : ℕ) : ℕ := Nat.ofDigits 10 (sortedDigits [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] n)

/-- A004185: arrange the digits of n in increasing order, zeros omitted. -/
def A004185 (n : ℕ) : ℕ := Nat.ofDigits 10 (sortedDigits [9, 8, 7, 6, 5, 4, 3, 2, 1, 0] n)

theorem main : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ A004185 n ∣ A004186 n ∧
    ¬ ∃ d m k : ℕ, 1 < d ∧ d < 10 ∧ n = d * 10 ^ m * ((10 ^ k - 1) / 9) := by
  sorry

end OMA.S_oeis_a096091

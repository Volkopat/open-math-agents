import Mathlib

/-!
# A083754: a(1) = 1 and then smallest odd number not occurring earlier such that the concatenation a(1)a(2)a(3)... is a prime.

Source: https://oeis.org/A083754
Credit: @gblacher2

Conjecture (comment section of A083754, Amarnath Murthy and Meenakshi Srikanth, May 06 2003):
"all odd numbers not of the type 10k+5 are members."

The sequence has offset 1: 1, 3, 7, 11, 9, 27, 63, 31, 53, 21, 13, 83, ...
(13, 137, 13711 are primes; 1379 is not, so 11 follows 7.)

Modelling choices:
* Concatenation is decimal: `concat x y` writes the base-10 digits of `x` followed by those
  of `y` (`Nat.digits 10 y` has no leading zeros); `concatList` concatenates a list in order.
* `terms n` is the list a(1), ..., a(n). After a(1) = 1, the next term is the least odd number
  not among the earlier terms whose appended concatenation is prime, taken with `sInf`.
  Such a number always exists: by the prime number theorem, for large `d` some prime has the
  current concatenation followed by a `d`-digit block (first digit nonzero) as its decimal
  expansion, and that block is odd; so the default value of `sInf` on the empty set is never used.
* "Of the type 10k+5" means `m % 10 = 5` for a natural number `k`; "members" means terms a(n)
  with n ≥ 1.
-/

namespace OMA.S_oeis_a083754

/-- Decimal concatenation: the digits of `x` followed by the digits of `y`. -/
def concat (x y : ℕ) : ℕ := x * 10 ^ (Nat.digits 10 y).length + y

/-- Decimal concatenation of the numbers of a list, in order. -/
def concatList (l : List ℕ) : ℕ := l.foldl concat 0

/-- `terms n` is the list of the first `n` terms a(1), ..., a(n). -/
noncomputable def terms : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | n + 2 =>
    let l := terms (n + 1)
    l ++ [sInf {m : ℕ | Odd m ∧ m ∉ l ∧ (concatList (l ++ [m])).Prime}]

/-- a(n), the last entry of `terms n` (offset 1). -/
noncomputable def a (n : ℕ) : ℕ := (terms n).getLastD 0

/-- The conjecture: every odd number not of the form 10k+5 occurs in the sequence. -/
theorem main : ∀ m : ℕ, Odd m → m % 10 ≠ 5 → ∃ n : ℕ, 1 ≤ n ∧ a n = m := by
  sorry

end OMA.S_oeis_a083754

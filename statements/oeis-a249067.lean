import Mathlib

/-!
# A249067: Smallest k such that {first digit of j*n, 0<=j<=k} = {0,1,...,9}.

Source: https://oeis.org/A249067
Credit: @rickmanelius

Conjecture (Charles R Greathouse IV, Oct 20 2014): a(n) <= N for all n. Perhaps N can be taken
as 81. (Charles R Greathouse IV, Mar 17 2018: The conjecture above is true. In fact, a(n) takes
on precisely 37 values: 9, 11, 12, 13, 14, 15, 16, 17, 18, 21, 22, 23, 24, 25, 26, 27, 31, 32,
33, 34, 35, 36, 41, 42, 43, 44, 45, 51, 52, 53, 54, 61, 62, 63, 71, 72, and 81.)

Formalization notes:
* Offset 1: the sequence is defined for n ≥ 1 (data: 9, 45, 27, 23, 18, ...). For n = 0 every
  multiple is 0 and no k exists, so both claims are stated for `1 ≤ n`.
* The first digit of m is its most significant decimal digit: the last entry of Mathlib's
  `Nat.digits 10 m`, which lists the digits least significant first. Mathlib has
  `Nat.digits 10 0 = []`; the first digit of 0 is 0 (`getLastD 0`), which is how the entry counts
  j = 0: it is the only multiple whose first digit is 0.
* `covers n k` says {first digit of j*n : 0 ≤ j ≤ k} = {0,1,...,9}, with j ranging over
  `Finset.Icc 0 k` and {0,1,...,9} written as `Finset.Icc 0 9`.
* a(n) is the least such k, written `sInf {k | covers n k}`. In ℕ, `sInf ∅ = 0`, so a bound on
  `a n` alone would hold for free if no k existed. Each claim therefore also asks that some k
  exists: (∃ k, covers n k) ∧ a n ≤ N says exactly that a(n) is defined and a(n) ≤ N.
* The comment makes two claims, and both are stated. The conjecture proper is its first
  sentence: some N has a(n) ≤ N for all n (first conjunct). The second sentence proposes the
  value N = 81 (second conjunct); when the source names a value it is stated too, and the 2018
  comment confirms it (81 is the largest of the 37 values). The second conjunct implies the
  first; the first is kept so that the statement reads as the comment does.
-/

namespace OMA.S_oeis_a249067

/-- The first (most significant) decimal digit of `m`, and 0 for `m = 0`. -/
def firstDigit (m : ℕ) : ℕ := (Nat.digits 10 m).getLastD 0

/-- {first digit of j*n : 0 ≤ j ≤ k} = {0,1,...,9}. -/
def covers (n k : ℕ) : Prop :=
  (Finset.Icc 0 k).image (fun j => firstDigit (j * n)) = Finset.Icc 0 9

/-- a(n) = smallest k such that {first digit of j*n : 0 ≤ j ≤ k} = {0,1,...,9}. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | covers n k}

theorem main :
    (∃ N : ℕ, ∀ n : ℕ, 1 ≤ n → (∃ k, covers n k) ∧ a n ≤ N) ∧
    (∀ n : ℕ, 1 ≤ n → (∃ k, covers n k) ∧ a n ≤ 81) := by
  sorry

end OMA.S_oeis_a249067

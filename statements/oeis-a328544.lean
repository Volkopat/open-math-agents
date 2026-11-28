import Mathlib

/-!
# A328544: Numbers k such that k multiplied by any of its digits contains k as a substring

Source: https://oeis.org/A328544 (conjecture in the comments of the entry)

Conjecture: the sequence consists of 0, 5, 6, and the numbers 11...1.

Conventions:
* `dec k` is the list of decimal digits of `k`, most significant first; the number 0 is
  written with the single digit 0 (so 0 is a term: its only digit is 0 and 0 * 0 = 0).
* `k` contains `m` as a substring when the digit list of `m` is a contiguous sublist
  (`List.IsInfix`) of the digit list of `k`.
* `good k` says that for every digit `d` of `k`, the decimal representation of `k * d`
  contains that of `k` as a substring.
* The numbers 11...1 are the repunits `repunit m` with `m >= 1` ones (so 1, 11, 111, ...).
* The statement is the full characterization: `good k` holds exactly for these numbers.
-/

namespace OMA.S_oeis_a328544

/-- Decimal digits of `k`, most significant first; 0 is the single digit 0. -/
def dec (k : ℕ) : List ℕ := if k = 0 then [0] else (Nat.digits 10 k).reverse

/-- `k` multiplied by any of its digits contains `k` as a substring. -/
def good (k : ℕ) : Prop := ∀ d ∈ dec k, List.IsInfix (dec k) (dec (k * d))

/-- The repunit with `m` decimal digits, all equal to 1. -/
def repunit (m : ℕ) : ℕ := Nat.ofDigits 10 (List.replicate m 1)

theorem main : ∀ k : ℕ, good k ↔ (k = 0 ∨ k = 5 ∨ k = 6 ∨ ∃ m ≥ 1, k = repunit m) := by
  sorry

end OMA.S_oeis_a328544

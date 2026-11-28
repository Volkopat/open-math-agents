import Mathlib

/-!
# A320572: The smallest integer m such that each nonzero digit appears in the decimal representation of the sequence n^1, n^2, ..., n^x, where 1 <= x <= m, or 0 if no such m exists.

Source: https://oeis.org/A320572
Credit: @azmiozgen

Conjecture (Robert Israel, from the entry; verified for n <= 10^7): a(n) <= 15, with a(n) = 15 only
for numbers of the form 2 * 10^k.

Formalization notes:
* a(n), offset 1, is the least m ≥ 1 such that each digit 1..9 occurs among the decimal digits of
  n^1, ..., n^m, or 0 if there is no such m.
* Stated for every n ≥ 1: a(n) ≤ 15, and a(n) = 15 iff n = 2 * 10^k for some k.
* Controls (computed): a(1..32) = 0, 15, 8, 10, 11, 12, 7, 5, 6, 0, 7, 6, 6, 5, 9, 5, 6, 4, 5, 15, 8, 6,
  4, 5, 8, 5, 4, 5, 7, 8, 7, 7, as in the entry; for n < 5000 the maximum is 15, attained exactly at
  2, 20, 200, 2000.
-/

namespace OMA.S_oeis_a320572

/-- Every digit `1..9` occurs in `n^1, ..., n^m`. -/
def Covers (n m : ℕ) : Prop :=
  ∀ d : ℕ, 1 ≤ d → d ≤ 9 → ∃ x : ℕ, 1 ≤ x ∧ x ≤ m ∧ d ∈ Nat.digits 10 (n ^ x)

/-- A320572(n). -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ m : ℕ, 1 ≤ m ∧ Covers n m then Nat.find h else 0

/-- Israel's conjecture. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n ≤ 15 ∧ (a n = 15 ↔ ∃ k : ℕ, n = 2 * 10 ^ k) := by
  sorry

end OMA.S_oeis_a320572

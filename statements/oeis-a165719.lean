import Mathlib

/-!
# A165719: Integers of the form k*(k+9)/8

Source: https://oeis.org/A165719
Credit: @xor2k

Formalizes the OEIS A165719 conjecture (Bill McEachen, May 06 2026):
Conjecture: Valid k values are pairs of the form (8*m-1,8*m) for m=1,2,3.... If true, 17 is the
only prime term.

Conventions:
* As in the entry's example (k = 1,2,...) and its formula via A047521, `k` ranges over the
  positive integers; `v` is a term iff `k * (k + 9) = 8 * v` for some `k ≥ 1`. This reproduces the
  OEIS data 14, 17, 45, 50, 92, ...
* A value `k ≥ 1` is valid iff `k*(k+9)/8` is an integer, i.e. `8 ∣ k * (k + 9)`.
* Both claims are stated: the description of the valid `k`, and that the prime terms are exactly
  `17` (so `17` is a term, it is prime, and no other term is prime).
-/

namespace OMA.S_oeis_a165719

/-- `v` is a term of A165719: `v = k * (k + 9) / 8` exactly, for some positive integer `k`. -/
def IsTerm (v : ℕ) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ k * (k + 9) = 8 * v

/-- The valid `k ≥ 1` are exactly `8m - 1` and `8m` for `m ≥ 1`, and `17` is the only prime
term. -/
theorem main :
    (∀ k : ℕ, 1 ≤ k →
      ((8 ∣ k * (k + 9)) ↔ ∃ m : ℕ, 1 ≤ m ∧ (k = 8 * m - 1 ∨ k = 8 * m))) ∧
    (∀ v : ℕ, (IsTerm v ∧ v.Prime) ↔ v = 17) := by
  sorry

end OMA.S_oeis_a165719

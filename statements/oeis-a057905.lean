import Mathlib

/-!
# A057905: Positive integers that are not the sum of exactly four positive cubes.

Source: https://oeis.org/A057905
Credit: @rpabani

Conjecture (Charles R Greathouse IV, 2017, in OEIS A057905): this sequence is finite, with
7373170279850 as its last member.

Both parts are stated. The second already implies the first for a set of natural numbers, but the
source asserts both, so both are kept.
-/

namespace OMA.S_oeis_a057905

/-- The positive integers that are not a sum of exactly four positive cubes (OEIS A057905). -/
def S : Set ℕ :=
  {n | 0 < n ∧ ¬ ∃ a b c d : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
    a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 = n}

theorem main : S.Finite ∧ IsGreatest S 7373170279850 := by
  sorry

end OMA.S_oeis_a057905

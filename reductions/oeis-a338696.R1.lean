import OMAStatements.S_oeis_a338696

-- Reduction oeis-a338696.R1 of A338696: Number of ways to write n as x^3 + y^2 + z*(3*z+2), where x and y are nonnegative integers, and z is an integer.
-- Credit: @jarrettbranch
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_oeis_a338696_R1

open OMA.S_oeis_a338696

/-- Even `n > 60` is `x^3 + y^2 + z(3z + 2)`. -/
def H1 : Prop := ∀ n : ℕ, 60 < n → Even n → 0 < a n

/-- Odd `n > 60` is `x^3 + y^2 + z(3z + 2)`. -/
def H2 : Prop := ∀ n : ℕ, 60 < n → Odd n → 0 < a n

/-- `19` has no representation (direct computation). -/
theorem a_19 : a 19 = 0 := by decide +kernel

/-- Every `0 < n ≤ 60` other than `19` has a representation (direct computation). -/
theorem small : ∀ n ≤ 60, 0 < n → n ≠ 19 → 0 < a n := by decide +kernel

/-- The exception `19` and all `n ≤ 60` are checked by computation; `n > 60` is split by parity. -/
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a338696.main := by
  intro h1 h2 n hn0
  constructor
  · rintro h rfl
    rw [a_19] at h
    exact lt_irrefl 0 h
  · intro hn
    rcases (show n ≤ 60 ∨ 60 < n by omega) with hs | hl
    · exact small n hs hn0 hn
    · rcases Nat.even_or_odd n with he | ho
      · exact h1 n hl he
      · exact h2 n hl ho

end OMA.R_oeis_a338696_R1

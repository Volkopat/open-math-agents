import FormalConjectures.OEIS.«153330»

-- Reduction OeisA153330.conjecture2.R1 of Collatz step differences — conjecture2
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target is a conjunction of four statements about the level sets `indices v` of the
-- Collatz step-difference sequence, one per value that is claimed to occur only once
-- (or, for `v = 3`, exactly at the two indices `4` and `5`).

namespace OMA.R_OeisA153330_conjecture2_R1

/-- The value `1` is attained at the single index `n = 1`. -/
def H1 : Prop := OeisA153330.indices 1 = {1}

/-- The value `6` is attained at the single index `n = 2`. -/
def H2 : Prop := OeisA153330.indices 6 = {2}

/-- The value `16` is attained at the single index `n = 8`. -/
def H3 : Prop := OeisA153330.indices 16 = {8}

/-- The value `3` is attained exactly at the two indices `n = 4` and `n = 5`. -/
def H4 : Prop := OeisA153330.indices 3 = {4, 5}

theorem main : H1 → H2 → H3 → H4 → type_of% @OeisA153330.conjecture2 := by
  intro h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end OMA.R_OeisA153330_conjecture2_R1

import FormalConjectures.Books.BugeaudDistributionModuloOne.IntDistanceDistribution
-- Credit: @PetrouilFan

namespace OMA.R_Bugeaud01_problem_10_3_R1

/-- Waldschmidt's conjecture: a polynomial lower bound for the distance of `exp n`
to the nearest integer (the genuinely open, stronger hypothesis). -/
def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n → (n : ℝ) ^ (-c) < distToNearestInt (Real.exp n)

/-- The upstream-proved transfer: Waldschmidt's polynomial bound implies Mahler's
exponential bound `problem_10_3` (`Bugeaud01.problem_10_3_of_waldschmidt`, no sorry). -/
def H2 : Prop :=
  (∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n → (n : ℝ) ^ (-c) < distToNearestInt (Real.exp n)) →
    (∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → Real.exp (-c * n) < distToNearestInt (Real.exp n))

theorem main : H1 → H2 → type_of% @Bugeaud01.problem_10_3 := by
  intro h1 h2
  exact h2 h1

end OMA.R_Bugeaud01_problem_10_3_R1

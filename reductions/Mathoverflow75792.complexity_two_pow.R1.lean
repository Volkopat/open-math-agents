import FormalConjectures.Mathoverflow.«75792»

-- Reduction Mathoverflow75792.complexity_two_pow.R1
-- Credit: @PetrouilFan
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Mathoverflow75792_complexity_two_pow_R1

/-- Proved upper bound: `2^n` is reachable in `2*n` steps (upstream `Reachable.pow`). -/
def H1 : Prop := ∀ n : ℕ, 0 < n → Mathoverflow75792.Reachable (2 ^ n) (2 * n)

/-- Open minimality: no `n' < 2*n` reaches `2^n`. -/
def H2 : Prop := ∀ n : ℕ, 0 < n → ∀ n' < 2 * n, ¬ Mathoverflow75792.Reachable (2 ^ n) n'

theorem main : H1 → H2 → type_of% @Mathoverflow75792.complexity_two_pow := by
  intro h1 h2 n hn
  exact Mathoverflow75792.Reachable.complexity_eq (h1 n hn) (h2 n hn)

end OMA.R_Mathoverflow75792_complexity_two_pow_R1

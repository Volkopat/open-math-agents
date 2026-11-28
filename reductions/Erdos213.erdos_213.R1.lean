import FormalConjectures.ErdosProblems.«213»

-- Reduction Erdos213.erdos_213.R1
-- Credit: @PetrouilFan
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos213_erdos_213_R1

def H1 : Prop := Erdos213.Erdos213For 7

def H2 : Prop := ∀ n : ℕ, 4 ≤ n → n ≠ 7 → Erdos213.Erdos213For n

theorem main : H1 → H2 → type_of% @Erdos213.erdos_213 := by
  intro h1 h2 n hn
  by_cases h : n = 7
  · subst n
    exact h1
  · exact h2 n hn h

end OMA.R_Erdos213_erdos_213_R1

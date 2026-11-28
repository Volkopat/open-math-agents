import FormalConjectures.ErdosProblems.«556»

-- Reduction Erdos556.erdos_556.variants.kss_large_odd.R1 of Erdős Problem 556 — kss large odd
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos556_erdos_556_variants_kss_large_odd_R1

open Filter SimpleGraph

def H1 : Prop :=
  ∀ᶠ n : ℕ in atTop, Odd n → multicolourRamsey (cycleGraph n) 3 ≤ 4 * n - 3

def H2 : Prop :=
  ∀ᶠ n : ℕ in atTop, Odd n → 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

theorem main : H1 → H2 → type_of% @Erdos556.erdos_556.variants.kss_large_odd :=
  fun h1 h2 =>
    Filter.Eventually.mono (Filter.Eventually.and h1 h2)
      (fun n hn hodd => le_antisymm (hn.1 hodd) (hn.2 hodd))

end OMA.R_Erdos556_erdos_556_variants_kss_large_odd_R1
-- ci: re-run check-proof

import FormalConjectures.ErdosProblems.«1107»

-- Reduction Erdos1107.erdos_1107.R1 of Erdős Problem 1107
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 1107: the known case `r = 2` and the open cases `r ≥ 3`

The target asks, for every `r ≥ 2`, whether every large integer is a sum of at most `r + 1`
numbers that are `r`-full. The reduction is the split by `r` and nothing more.

* `H1` (known, deep): the case `r = 2`, a theorem of Heath-Brown (*Ternary quadratic forms and
  sums of three square-full numbers*, 1988). It is the statement of the catalogue problem
  `Erdos1107.erdos_1107.variants.two`, which has a merged reduction of its own.
* `H2` (open): the cases `r ≥ 3`.

Both hypotheses are special cases of the target, and together they are the target.
-/

namespace OMA.R_Erdos1107_erdos_1107_R1
open Filter

/-- Heath-Brown: every large integer is a sum of at most three square-full numbers. -/
def H1 : Prop :=
  ∀ᶠ n in atTop, Erdos1107.SumOfRPowerful 2 n

/-- For `r ≥ 3`, every large integer is a sum of at most `r + 1` numbers that are `r`-full. -/
def H2 : Prop :=
  ∀ r ≥ 3, ∀ᶠ n in atTop, Erdos1107.SumOfRPowerful r n

theorem main : H1 → H2 → type_of% @Erdos1107.erdos_1107 := by
  intro h1 h2 r hr
  by_cases h : r = 2
  · subst h
    exact h1
  · exact h2 r (by omega)

end OMA.R_Erdos1107_erdos_1107_R1

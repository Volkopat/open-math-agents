import OMAStatements.S_oeis_a070548
import Mathlib

/-! Steinerberger's asymptotics for the counts of n <= x with Möbius value +1 and -1 (OEIS
A070548) have three parts. The first says that the two counts together, that is the number of
squarefree integers up to x, are asymptotic to (6 / pi^2) x; this is the classical theorem on the
density of the squarefree numbers and is provable from the identity
[n squarefree] = sum of mu(d) over d^2 | n and sum mu(d) / d^2 = 1 / zeta(2). The other two parts
are of a different order of difficulty: the bound for the difference of the two counts under the
Riemann hypothesis, and the statement that each sign has density 3 / pi^2, which is equivalent
to the prime number theorem. -/

namespace OMA.R_oeis_a070548_R1

open OMA.S_oeis_a070548

/-- The density of the squarefree numbers is 6 / pi^2. -/
def H1 : Prop :=
  Filter.Tendsto (fun n : ℕ => ((countSign 1 n : ℝ) + countSign (-1) n) / n)
    Filter.atTop (nhds (6 / Real.pi ^ 2))

/-- The Mertens-type parts: the conditional square-root bound and the density 3 / pi^2 of each
sign. -/
def H2 : Prop :=
  (RiemannHypothesis → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      |(countSign 1 n : ℝ) - countSign (-1) n| < (n : ℝ) ^ (1 / 2 + ε)) ∧
    Filter.Tendsto (fun n : ℕ => (countSign 1 n : ℝ) / n)
      Filter.atTop (nhds (3 / Real.pi ^ 2))

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a070548.main := by
  intro h1 h2
  exact ⟨h1, h2.1, h2.2⟩

end OMA.R_oeis_a070548_R1

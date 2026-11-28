import Mathlib

/-!
# Diagonal Ramsey numbers

Source: https://www.openproblemgarden.org/op/diagonal_ramsey_numbers
Credit: @Mapika

Let `R(k,k)` denote the `k`-th diagonal Ramsey number. Conjecture (Erdős): the limit
`lim_{k → ∞} R(k,k)^(1/k)` exists. The page also poses the problem of determining that limit;
that part asks for a value and is not stated here. `main` states the highlighted conjecture.

Conventions:
- `diagonalRamsey k` is the least `N` such that for every simple graph `C` on `Fin N` (the edges
  of the first colour; its complement `Cᶜ` holds the edges of the second colour), the complete
  graph `K_k` is contained in `C` or in `Cᶜ` (as a subgraph, not necessarily induced). This is
  the definition of `SimpleGraph.diagonalRamsey` (via `classicalRamsey` and `graphRamsey`) in
  formal-conjectures (FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Ramsey.lean),
  inlined because that library is not imported here. By Ramsey's theorem the set is nonempty for
  every `k`, so the `sInf` is never the junk value of an empty set.
- The `k`-th root is the real power `R(k) ^ (1 / k)` with `k` cast to `ℝ`, as in upstream
  `Erdos77.erdos_77`. The value at `k = 0` is irrelevant for a limit.
- *The limit exists* means: there is a real number `L` with `R(k)^(1/k) → L` as `k → ∞` along
  the naturals. A finite limit is the standard reading; since `√2 ≤ R(k)^(1/k) ≤ 4` for all
  `k ≥ 3`, an infinite limit is impossible anyway.

Upstream overlap: `Erdos77.erdos_77` (FormalConjectures/ErdosProblems/77.lean) states the
`question value` version, that `R(k)^(1/k)` tends to an unspecified `erdos_77.answer`. The
statement here is the existence part only, with no answer constant.
-/

namespace OMA.S_opg_diagonal_ramsey_numbers

open Filter Topology

/-- The diagonal Ramsey number `R(k,k)`: the least `N` such that every red/blue colouring of
the edges of `K_N` (red edges `C`, blue edges `Cᶜ`) has a red or a blue copy of `K_k`. -/
noncomputable def diagonalRamsey (k : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ C : SimpleGraph (Fin N),
    (⊤ : SimpleGraph (Fin k)).IsContained C ∨ (⊤ : SimpleGraph (Fin k)).IsContained Cᶜ}

/-- Erdős: the limit of `R(k,k)^(1/k)` as `k → ∞` exists. -/
theorem main : ∃ L : ℝ,
    Tendsto (fun k : ℕ => (diagonalRamsey k : ℝ) ^ (1 / (k : ℝ))) atTop (𝓝 L) := by
  sorry

end OMA.S_opg_diagonal_ramsey_numbers

import Mathlib

/-!
# A340630: Minimal sum of an n × n grid of nonnegative integers with distinct von Neumann neighborhood sums

Source: https://oeis.org/A340630
Credit: @Rickxscz

Formalizes the conjecture in OEIS A340630 (Hugo van der Sanden, Jan 13 2021):
Fill an `n × n` square with nonnegative integers so that all `n ^ 2` von Neumann
neighborhoods have distinct sums; let `a(n)` be the smallest possible sum of the entries.
Conjecture: `a(n) = ⌈(n ^ 4 - n ^ 2 + 14) / 10⌉`, matching the lower bound, for all `n > n₀`
for some constant `n₀`.

Conventions:
* An `n × n` square of nonnegative integers is a function `M : Fin n → Fin n → ℕ` (allowing `0`,
  as in all OEIS examples).
* The closed von Neumann neighborhood of cell `(i, j)` consists of `(i, j)` together with its
  orthogonally adjacent cells inside the `n × n` grid, i.e., all `(i', j') : Fin n × Fin n`
  with Manhattan distance `Nat.dist i.val i'.val + Nat.dist j.val j'.val ≤ 1`. This matches
  the OEIS examples (e.g., for `n = 3`, `{0, 0, 0; 0, 1, 3; 1, 4, 0}` gives neighborhood sums
  `{0, 1, 3; 2, 8, 4; 5, 6, 7}`) and the OEIS lower-bound proof (`5a(n) - S_e - 2S_c`).
* All `n ^ 2` von Neumann neighborhoods have distinct sums iff `neighborhoodSum M` is injective.
* For every `n : ℕ`, a valid grid exists (e.g., distinct powers of `2`), so the set of sums of
  valid `n × n` grids is nonempty and `sInf` gives its exact minimum `a(n)`.
* `ceiling((n ^ 4 - n ^ 2 + 14) / 10)` is written directly via `Nat.ceil` over `ℚ`.
-/

namespace OMA.S_oeis_a340630

/-- The closed von Neumann neighborhood of cell `p` in an `n × n` grid:
`p` itself together with its orthogonally adjacent cells in the grid. -/
def vonNeumann (n : ℕ) (p : Fin n × Fin n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun q => Nat.dist p.1.val q.1.val + Nat.dist p.2.val q.2.val ≤ 1

/-- The sum of the entries of an `n × n` grid `M` over the closed von Neumann
neighborhood of cell `p`. -/
def neighborhoodSum {n : ℕ} (M : Fin n → Fin n → ℕ) (p : Fin n × Fin n) : ℕ :=
  ∑ q ∈ vonNeumann n p, M q.1 q.2

/-- An `n × n` grid of nonnegative integers is valid if all `n ^ 2` von Neumann
neighborhoods have pairwise distinct sums. -/
def IsValidGrid {n : ℕ} (M : Fin n → Fin n → ℕ) : Prop :=
  Function.Injective (neighborhoodSum M)

/-- The total sum of all entries of an `n × n` grid `M`. -/
def gridSum {n : ℕ} (M : Fin n → Fin n → ℕ) : ℕ :=
  ∑ i : Fin n, ∑ j : Fin n, M i j

/-- OEIS A340630: the smallest possible sum of entries of an `n × n` square of
nonnegative integers whose `n ^ 2` von Neumann neighborhoods have distinct sums. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {s : ℕ | ∃ M : Fin n → Fin n → ℕ, IsValidGrid M ∧ gridSum M = s}

/-- Conjecture (OEIS A340630): `a(n) = ⌈(n ^ 4 - n ^ 2 + 14) / 10⌉` for all `n > n₀`
for some constant `n₀`. -/
theorem main :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ < n →
      a n = Nat.ceil (((n : ℚ) ^ 4 - (n : ℚ) ^ 2 + 14) / 10) := by
  sorry

end OMA.S_oeis_a340630

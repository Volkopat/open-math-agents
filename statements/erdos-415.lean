import Mathlib

/-!
# Erdős Problem 415

Source: https://www.erdosproblems.com/415
Credit: @sntntHb

For any `n` let `F(n)` be the largest `k` such that any of the `k!` possible ordering patterns
appears in some sequence of `φ(m+1), …, φ(m+k)` with `m + k ≤ n`. Is it true that
`F(n) = (c + o(1)) log log log n` for some constant `c`? (The problem goes on to ask which
pattern fails first, and whether the natural ordering is the most likely one; those parts are
not formalized here.)

We formalize the first question. As noted on the problem page, the asymptotic of Pollack,
Pomerance and Treviño for the longest monotone run of `φ` gives `F(n) = o(log log log n)`, so
this question has a negative answer (the intended constant being positive, since Erdős and
Graham claimed `F(n) ≍ log log log n`). We state that negative answer: there is no constant
`c > 0` with `F(n) / log log log n → c`.

Conventions:
- An ordering pattern of length `k` is a permutation `σ` of `Fin k`; it appears at `m` when
  `φ(m+1+i) < φ(m+1+j) ↔ σ i < σ j` for all `i, j`, i.e. with strict inequalities (the page notes
  that the source is ambiguous on this point and that it only matters for the final question).
- `F n` is the supremum of the admissible `k`; the set of admissible `k` contains `0` and is
  bounded by `n`, so this is a true maximum.
-/

namespace OMA.S_erdos_415

open Filter Topology

/-- The pattern `σ` of length `k` appears in `φ(m+1), …, φ(m+k)`. -/
def Appears (k m : ℕ) (σ : Equiv.Perm (Fin k)) : Prop :=
  ∀ i j : Fin k, Nat.totient (m + 1 + i) < Nat.totient (m + 1 + j) ↔ σ i < σ j

/-- `F(n)`: the largest `k` such that every ordering pattern of length `k` appears in some
`φ(m+1), …, φ(m+k)` with `m + k ≤ n`. -/
noncomputable def F (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∀ σ : Equiv.Perm (Fin k), ∃ m : ℕ, m + k ≤ n ∧ Appears k m σ}

/-- The first question has a negative answer: `F(n)` is not `(c + o(1)) log log log n` for any
constant `c > 0`. -/
theorem main : ¬ ∃ c : ℝ, 0 < c ∧
    Tendsto (fun n : ℕ => (F n : ℝ) / Real.log (Real.log (Real.log n))) atTop (𝓝 c) := by
  sorry

end OMA.S_erdos_415

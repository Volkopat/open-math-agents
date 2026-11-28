import Mathlib

/-!
# Erdős Problem 776

Source: https://www.erdosproblems.com/776
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Let `r ≥ 2` and let `A_1, …, A_m ⊆ {1, …, n}` be such that `A_i ⊄ A_j` for all `i ≠ j`, and such
that whenever some `A_i` has size `t`, at least `r` of the sets have size `t`. How large must `n`
be (as a function of `r`) to ensure that there is such a family which achieves `n - 3` distinct
set sizes?

Conventions:
* the ground set `{1, …, n}` is modelled by `Fin n`; the condition `A_i ⊄ A_j` for `i ≠ j` forces
  the sets to be distinct, so a family is a `Finset (Finset (Fin n))` that is an antichain for `⊆`;
* `n₀ r` is the least threshold such that a family with `n - 3` distinct sizes exists for every
  `n > n₀ r`, i.e. the largest `n` for which no such family exists (`sSup` of that set);
  if that set were unbounded or empty, `sSup` would be `0` and the statement below would be
  false, so no junk value can make it true;
* "achieves `n - 3` distinct sizes" is taken as exactly `n - 3` sizes; this is equivalent to
  "at least `n - 3`", since deleting every set of one size keeps both conditions, and `n - 2`
  sizes are never achievable for `r > 1` (as the source notes);
* the question asks for the order of `n₀ r`; the source records the answer `n₀(r) ∼ 2r` as
  `r → ∞` (He and Tang), and that asymptotic is the statement below (`r ≥ 2` is automatic
  in the limit `r → ∞`).
-/

namespace OMA.S_erdos_776

open Filter Topology

/-- `F` is an admissible family on `Fin n` for the parameter `r`: an antichain for inclusion in
which every occurring set size occurs at least `r` times, with exactly `n - 3` distinct sizes. -/
def IsAdmissible (r n : ℕ) (F : Finset (Finset (Fin n))) : Prop :=
  IsAntichain (· ⊆ ·) (F : Set (Finset (Fin n))) ∧
  (∀ A ∈ F, r ≤ (F.filter (fun B => B.card = A.card)).card) ∧
  (F.image Finset.card).card = n - 3

/-- The largest `n` for which no admissible family on `Fin n` exists. -/
noncomputable def n₀ (r : ℕ) : ℕ :=
  sSup {n : ℕ | ¬ ∃ F : Finset (Finset (Fin n)), IsAdmissible r n F}

/-- Erdős Problem 776 (answer recorded on the source page): `n₀(r) ∼ 2r` as `r → ∞`. -/
theorem main : Tendsto (fun r : ℕ => (n₀ r : ℝ) / (r : ℝ)) atTop (𝓝 2) := by
  sorry

end OMA.S_erdos_776

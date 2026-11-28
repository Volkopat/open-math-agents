import Mathlib

/-! Source: https://mathoverflow.net/questions/120027 -/

namespace OMA.S_mo_120027

/-- A directed walk, with specified endpoints and length. Vertices may repeat. -/
inductive Walk {n : ℕ} (adj : Fin n → Fin n → Prop) : Fin n → Fin n → ℕ → Prop
  | nil (v : Fin n) : Walk adj v v 0
  | step {u v w : Fin n} {k : ℕ} :
      adj u v → Walk adj v w k → Walk adj u w (k + 1)

noncomputable def outdegree {n : ℕ} (adj : Fin n → Fin n → Prop) (v : Fin n) : ℕ := by
  classical
  exact (Finset.univ.filter (adj v)).card

/-- A lower bound d on the minimum outdegree is feasible if the digraph
has no loops and no closed walk of the given length. -/
def FeasibleOutdegree (n m d : ℕ) : Prop :=
  ∃ adj : Fin n → Fin n → Prop,
    (∀ v, ¬ adj v v) ∧ (∀ v, ¬ Walk adj v v m) ∧ (∀ v, d ≤ outdegree adj v)

/-- The proposed outdegree bound holds for every positive length. For each
odd length of at least three the exact maximum is ⌊n/2⌋. -/
theorem main :
    (∀ (n m d : ℕ), 0 < n → 0 < m → FeasibleOutdegree n m d →
      d * (2 * m - 1) < m * n) ∧
    (∀ (n m : ℕ), 0 < n → 3 ≤ m → Odd m →
      IsGreatest {d : ℕ | FeasibleOutdegree n m d} (n / 2)) := by
  sorry

end OMA.S_mo_120027

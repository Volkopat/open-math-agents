import Mathlib

/-!
# Turán Problem for 10-Cycles in the Hypercube

Source: https://www.openproblemgarden.org/op/turan_problem_for_10_cycles_in_the_hypercube
Credit: @AkiRA-COM-FP

Formalizes Erdős's conjecture `ex(Q_n, C_10) = o(|E(Q_n)|)` as `n → ∞`, where `Q_n` is the
`n`-dimensional hypercube graph on `Fin n → Bool` with edges between vertices differing in
exactly one coordinate, and `ContainsC10 H` means `H` contains a `10`-cycle as a subgraph.
-/

namespace OMA.S_opg_turan_problem_for_10_cycles_in_the_hypercube

/-- The `n`-dimensional hypercube graph `Q_n` on `{0, 1}^n`, where two vertices are adjacent
iff they differ in exactly one coordinate. -/
def hypercubeGraph (n : ℕ) : SimpleGraph (Fin n → Bool) where
  Adj u v := (Finset.univ.filter (fun i : Fin n => u i ≠ v i)).card = 1
  symm := ⟨fun u v h => by
    have hEq : (Finset.univ.filter (fun i : Fin n => v i ≠ u i)) =
        (Finset.univ.filter (fun i : Fin n => u i ≠ v i)) := by
      ext i; simp [ne_comm]
    rw [hEq, h]⟩
  loopless := ⟨fun u h => by simp at h⟩

/-- A subgraph `H` of `Q_n` contains a `10`-cycle. -/
def ContainsC10 {n : ℕ} (H : SimpleGraph (Fin n → Bool)) : Prop :=
  ∃ v : Fin 10 → (Fin n → Bool),
    Function.Injective v ∧ ∀ i : Fin 10, H.Adj (v i) (v (i + 1))

/-- Erdős's Turán conjecture for `10`-cycles in the hypercube `Q_n`:
`ex(Q_n, C_10) = o(e(Q_n))` as `n → ∞`. -/
theorem main :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ H : SimpleGraph (Fin n → Bool),
          H ≤ hypercubeGraph n → ¬ ContainsC10 H →
          (H.edgeSet.ncard : ℝ) ≤ ε * ((hypercubeGraph n).edgeSet.ncard : ℝ) := by
  sorry

end OMA.S_opg_turan_problem_for_10_cycles_in_the_hypercube

import Mathlib

/-!
# Capped probabilities of finitely many events

Daniel asks when a finite probability distribution can give prescribed lower
bounds to event probabilities while bounding each atom by a common cap.
Here the atoms may have different caps. The criterion only uses their caps,
the demands, and their event memberships. For any nonnegative weighting of
the events, the score of an atom is the total weight of the events containing
it. The first assertion tests only thresholds equal to an atom score.
The second assertion exhibits six events for which weighting a subset of
events equally passes every test against the maximum covered count, while a
nonuniform weighting certifies infeasibility.

Source: Daniel, https://mathoverflow.net/questions/238612 (CC BY-SA 4.0).
Credit: @connoranderson (agent: Codex)
-/

namespace OMA.S_mo_238612
open Finset
def feasible {n k : ℕ} (A : Fin k → Finset (Fin n)) (cap : Fin n→ℝ) (d : Fin k→ℝ) : Prop :=
  ∃ p : Fin n→ℝ, (∀ j, 0 ≤ p j ∧ p j ≤ cap j) ∧ (∑ j, p j)=1 ∧ ∀ i, d i ≤ ∑ j ∈ A i,p j

def score {n k : ℕ} (A : Fin k → Finset (Fin n)) (w : Fin k→ℝ) (j : Fin n) : ℝ :=
  ∑ i, if j∈A i then w i else 0

theorem main :
    (∀ (n k : ℕ) (A : Fin k→Finset (Fin n)) (cap : Fin n→ℝ) (d : Fin k→ℝ),
      (∀ j, 0 ≤ cap j) → (feasible A cap d ↔ 1 ≤ ∑ j, cap j ∧
        ∀ (w : Fin k→ℝ), (∀ i, 0 ≤ w i) → ∀ s : Fin n, (∑ i, w i*d i) ≤
          score A w s+∑ j, cap j*max (score A w j-score A w s) 0)) ∧
    (∃ (A : Fin 6→Finset (Fin 6)) (d : Fin 6→ℝ), (∀ i, 0 ≤ d i ∧ d i ≤ 1) ∧
      (∀ S : Finset (Fin 6), ∃ j : Fin 6, (∑ i ∈ S,d i) ≤ ∑ i ∈ S, (if j∈A i then (1:ℝ) else 0)) ∧
      ¬feasible A (fun _ => 1) d) := by
  sorry
end OMA.S_mo_238612

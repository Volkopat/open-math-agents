import Mathlib

-- Formalization by Herman Palmgren (@PalmtreeBranch), using Codex.

/-!
# OEIS A391538

Ruediger Jehn conjectured an exact value for the three-basket game for every
number of coins greater than four. On each turn the opponent selects a basket.
The player then chooses one remaining coin and places it in that basket. The
player receives the largest basket total at the end.

Source: https://oeis.org/A391538

Fabien Nießen and Silas Rathke solve the case of 2025 coins in the 2025
MATH+ Advent Calendar, challenge 1.
-/

namespace OMA.S_oeis_a391538

/-- The player can guarantee a final basket worth at least `target`, starting
with the given remaining coins and the three current basket totals. -/
inductive CanForce (target : ℕ) : Finset ℕ → (Fin 3 → ℕ) → Prop
  | finish {score} (reached : ∃ i, target ≤ score i) : CanForce target ∅ score
  | turn {coins score} (choice : Fin 3 → ℕ) (legal : ∀ i, choice i ∈ coins)
      (play : ∀ i, CanForce target (coins.erase (choice i))
        (Function.update score i (score i + choice i))) :
      CanForce target coins score

/-- Jehn's conjectured optimum for all `n > 4`. -/
theorem main : ∀ n : ℕ, 4 < n →
    IsGreatest {t : ℕ | CanForce t (Finset.Icc 1 n) (fun _ => 0)}
      (n + n * (n - 1) / 6) := by
  sorry

end OMA.S_oeis_a391538

import Mathlib

/-!
# Weighted adjacent transpositions and the diameter of the symmetric group

Source: Miriam Flander, https://mathoverflow.net/questions/275692 (CC BY-SA 4.0).
Contribution by @connoranderson.

On n+1 positions, a letter j swaps positions j and j+1 and costs w(j).
The reversal is farthest from the identity for all nonnegative weights.
The diameter is the minimum cost among reversal words of length binomial(n+1,2). In S₃, weights (2,1) give diameter four,
where the proposed expression 2w₁+w₂ is five.
-/

namespace OMA.S_mo_275692
abbrev G (n : ℕ) := Equiv.Perm (Fin (n+1))
def step {n : ℕ} (p : G n) (j : Fin n) : G n := (Equiv.swap j.castSucc j.succ).trans p
def run {n : ℕ} (p : G n) : List (Fin n) → G n
  | [] => p
  | j::l => run (step p j) l
def cost {n : ℕ} (w : Fin n → ℝ) (l : List (Fin n)) := (l.map w).sum
def costs {n : ℕ} (w : Fin n → ℝ) (p q : G n) : Set ℝ :=
  {c | ∃ l : List (Fin n), run p l=q ∧ cost w l=c}
noncomputable def distance {n : ℕ} (w : Fin n → ℝ) (p q : G n) := sInf (costs w p q)

theorem main :
    (∀ (n : ℕ) (w : Fin n → ℝ), (∀ j,0 ≤ w j) →
      IsGreatest {d : ℝ | ∃ p q : G n, distance w p q = d}
        (distance w (Equiv.refl _) Fin.revPerm) ∧
      ∃ l : List (Fin n), l.length = (n+1).choose 2 ∧ run (Equiv.refl _) l=Fin.revPerm ∧
        IsLeast (costs w (Equiv.refl _) Fin.revPerm) (cost w l)) ∧
    distance (![2,1] : Fin 2 → ℝ) (Equiv.refl _) Fin.revPerm = 4 := by
  sorry
end OMA.S_mo_275692

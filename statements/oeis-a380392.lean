import Mathlib

/-!
# Mean number of South-East paths of ones in a binary matrix

John Tyler Rascoe's conjecture concerns all positive square sizes m+1.
A binary matrix is specified by the set of its cells containing ones.
-/
namespace OMA.S_oeis_a380392
open Finset

def grid (m : ℕ) := range (m+1) ×ˢ range (m+1)

/-- A path takes 2m steps, m of them South. The set gives the indices
of its South steps, counting from zero. -/
def paths (m : ℕ) := (range (2*m)).powersetCard m

/-- Cell after t steps. The two coordinates count South and East steps. -/
def cell (s : Finset ℕ) (t : ℕ) : ℕ × ℕ :=
  ((range t ∩ s).card, (range t \ s).card)

def cells (m : ℕ) (s : Finset ℕ) := (range (2*m+1)).image (cell s)

def pathCount (m : ℕ) (M : Finset (ℕ × ℕ)) :=
  ((paths m).filter (fun s=>cells m s ⊆ M)).card

/-- A001790 is the odd part of the central binomial coefficient. -/
def A001790 (m : ℕ) := m.centralBinom / 2^padicValNat 2 m.centralBinom

/-- A101926 is two raised to A005187(m)+1, where A005187(m) is twice m
minus the number of ones in its binary expansion. -/
def A101926 (m : ℕ) := 2^(2*m-(Nat.digits 2 m).sum+1)

theorem main : ∀ m : ℕ,
    (∑ M ∈ (grid m).powerset, (pathCount m M : ℚ)) / ((grid m).powerset.card : ℚ) =
      (A001790 m : ℚ) / A101926 m := by
  sorry

end OMA.S_oeis_a380392

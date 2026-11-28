import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Pi

/-!
# Limiting maximum density of a stable binary grid

Source: https://oeis.org/A179004
Credit: @LDJAI

R. H. Hardin proposed the limiting density on January 3, 2011. The table
maximizes the number of ones among all arrays in which no cell agrees with
a strict majority of its horizontal and vertical neighbors. Boundary cells
use just their neighbors in the rectangle. Both side lengths tend to infinity.
-/

namespace GridAnti
abbrev Cell (n m : ℕ) := Fin n × Fin m

def Adj {n m : ℕ} (v w : Cell n m) : Prop :=
  (v.1 = w.1 ∧ (v.2.val+1=w.2.val ∨ w.2.val+1=v.2.val)) ∨
  (v.2 = w.2 ∧ (v.1.val+1=w.1.val ∨ w.1.val+1=v.1.val))

instance {n m : ℕ} (v w : Cell n m) : Decidable (Adj v w) := by unfold Adj; infer_instance

def neighbors {n m : ℕ} (v : Cell n m) : Finset (Cell n m) :=
  Finset.univ.filter (Adj v)
def opp {n m : ℕ} (c : Cell n m → Bool) (v : Cell n m) : ℕ :=
  ((neighbors v).filter fun w => c w ≠ c v).card
def Happy {n m : ℕ} (c : Cell n m → Bool) : Prop :=
  ∀ v, (neighbors v).card ≤ 2 * opp c v
def ones {n m : ℕ} (c : Cell n m → Bool) : ℕ :=
  (Finset.univ.filter fun v => c v = true).card

/-- Greatest number of ones in a configuration meeting the local constraint. -/
noncomputable def best (n m : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun c : Cell n m → Bool => Happy c).sup ones

end GridAnti

namespace OMA.S_oeis_a179004

theorem main : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧
    ∀ n m : ℕ, N ≤ n → N ≤ m →
    |(GridAnti.best n m : ℝ) / ((n : ℝ) * (m : ℝ)) - 2 / 3| < ε := by
  sorry

end OMA.S_oeis_a179004

import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.GCDMonoid.Multiset
import Mathlib.Data.Rat.Defs

/-!
# Zieve's conjecture for three branch points

M. E. Zieve's conjecture, in the formulation of X. Liu, T. Sun, B. Xu, Y. Ye,
and Y. Zhou, "Reduction of Zieve's Conjecture on the Hurwitz problem to Three
Branch Points", Definitions 1.1 and 1.2. https://arxiv.org/abs/2609.23663
Credit: @pmaster
-/

namespace OMA.S_aist_zieve_conjecture_three_branch_points

/-- A nonidentity branch partition of d, with gcd of its parts equal to one. -/
def Branch (d : ℕ) (l : Multiset ℕ) : Prop :=
  (∀ n ∈ l, 0 < n) ∧ l.sum = d ∧ (∃ n ∈ l, 1 < n) ∧ l.gcd = 1

/-- Mathlib's cycle type omits fixed points. Ramification partitions include them. -/
def fullCycleType {d : ℕ} (p : Equiv.Perm (Fin d)) : Multiset ℕ :=
  p.cycleType + Multiset.replicate (d - p.cycleType.sum) 1

/-- The generated monodromy group acts transitively on the sheets. -/
def Transitive {d : ℕ} (x y z : Equiv.Perm (Fin d)) : Prop :=
  ∀ i j : Fin d, ∃ g ∈ Subgroup.closure ({x, y, z} : Set (Equiv.Perm (Fin d))), g i = j

theorem main : ∀ (d : ℕ), 2 ≤ d → ∀ a b c : Multiset ℕ,
    Branch d a → Branch d b → Branch d c →
    (∃ h : ℕ, (d - a.card) + (d - b.card) + (d - c.card) = 2 * (d + h - 1)) →
    ((1 - 1 / (a.lcm : ℚ)) + (1 - 1 / (b.lcm : ℚ)) + (1 - 1 / (c.lcm : ℚ)) ≠ 2) →
    ∃ x y z : Equiv.Perm (Fin d), fullCycleType x = a ∧ fullCycleType y = b ∧
      fullCycleType z = c ∧ x * y * z = 1 ∧ Transitive x y z := by
  sorry

end OMA.S_aist_zieve_conjecture_three_branch_points

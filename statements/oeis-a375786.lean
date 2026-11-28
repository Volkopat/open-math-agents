import Mathlib

/-!
# Minimum-volume integer cuboids having the surface area of a cube

Felix Huber's conjecture in OEIS A375786 chooses the least possible
shortest edge and, among ties, the least possible second shortest edge.
All edges are positive integers and are listed in nondecreasing order.
-/
namespace OMA.S_oeis_a375786

def admissible (n a b c : ℕ) : Prop :=
  0 < a ∧ a ≤ b ∧ b ≤ c ∧ 2*(a*b+a*c+b*c)=6*n^2

def leastSides (n a b : ℕ) : Prop :=
  ∀ x y z : ℕ, admissible n x y z → a < x ∨ (a = x ∧ b ≤ y)

theorem main : ∀ n : ℕ, 0 < n →
    (∃ a b c : ℕ, admissible n a b c ∧ leastSides n a b) ∧
    (∀ a b c : ℕ, admissible n a b c → leastSides n a b →
      ∀ x y z : ℕ, admissible n x y z → a*b*c ≤ x*y*z) := by
  sorry

end OMA.S_oeis_a375786

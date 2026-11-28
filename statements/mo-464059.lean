import Mathlib

/-!
# Which inner products determine the remaining entries?

Source: https://mathoverflow.net/questions/464059 (Robert A. Vandermeulen, CC BY-SA 4.0).
Credit: @connoranderson

The planar criterion concerns the actual four edge values. The graph statements
use uniqueness for every configuration, as the question assumes no genericity.
For unknown lengths, determining all inner products includes the diagonal entries.
The one-dimensional unknown-length criterion also follows from Singer and Cucuringu,
Proposition 5.4, https://arxiv.org/abs/0902.3846.
-/

namespace OMA.S_mo_464059
open Matrix

abbrev Plane := ℝ × ℝ
def ip (u v : Plane) : ℝ := u.1*v.1 + u.2*v.2
def unit (u : Plane) : Prop := ip u u = 1

def possible (a b c d t : ℝ) : Prop := ∃ u v w z : Plane,
  unit u ∧ unit v ∧ unit w ∧ unit z ∧ ip u v = a ∧ ip v w = b ∧
  ip w z = c ∧ ip z u = d ∧ ip u w = t

def determinant (a b t : ℝ) : ℝ := 1 + 2*a*b*t - a^2 - b^2 - t^2

def determines {V : Type*} (G : SimpleGraph V) (d : ℕ) (h : (Fin d → ℝ) → Prop) : Prop :=
  ∀ x y : V → Fin d → ℝ, (∀ i, h (x i)) → (∀ i, h (y i)) →
    (∀ i j, G.Adj i j → dotProduct (x i) (x j) = dotProduct (y i) (y j)) →
    ∀ i j, dotProduct (x i) (x j) = dotProduct (y i) (y j)

def isUnit {d : ℕ} (x : Fin d → ℝ) : Prop := dotProduct x x = 1

theorem main :
    (∀ a b c d t : ℝ, possible a b c d t ↔
      a^2 ≤ 1 ∧ d^2 ≤ 1 ∧ t^2 ≤ 1 ∧ determinant a b t = 0 ∧ determinant d c t = 0) ∧
    (∀ a b c d t : ℝ, possible a b c d t → a*b ≠ c*d →
      t = (a^2+b^2-c^2-d^2)/(2*(a*b-c*d))) ∧
    (possible 0 (3/5) 0 (3/5) (4/5) ∧ possible 0 (3/5) 0 (3/5) (-4/5)) ∧
    (∀ n d : ℕ, ∀ G : SimpleGraph (Fin n), determines G (d+2) isUnit ↔ G = ⊤) ∧
    (∀ n : ℕ, ∀ G : SimpleGraph (Fin n), determines G 1 isUnit ↔ G.Preconnected) ∧
    (∀ n d : ℕ, ∀ G : SimpleGraph (Fin (n+1)), ¬ determines G (d+2) (fun x => x ≠ 0)) ∧
    (∀ n : ℕ, ∀ G : SimpleGraph (Fin (n+1)), determines G 1 (fun x => x ≠ 0) ↔
      G.Preconnected ∧ ¬ G.Colorable 2) := by
  sorry
end OMA.S_mo_464059

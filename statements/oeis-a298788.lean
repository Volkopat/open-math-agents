import Mathlib

/-!
# A298788. Coordination sequence of the bey net at a trivalent vertex

Source: https://oeis.org/A298788
Credit: @Aryan-Poonacha

Rémy Sigrist's adjacency program uses horizontal lines of ordinates
6j, 6j+2, 6j+3, 6j+5. Number them consecutively 4j through 4j+3.
An edge joins consecutive columns on every line. Vertical edges across an
odd-numbered line are unrestricted. Above line 2j they occur precisely
at columns congruent to j modulo 2. The root is Sigrist's vertex (1,0).
Here coordinates are (line, column minus 1), so the root is (0,0).
-/

namespace OMA.S_oeis_a298788

abbrev Vertex := ℤ × ℤ

def vertical (r u : ℤ) : Prop := r % 2 = 1 ∨ (u+1) % 2 = (r/2) % 2

instance (r u : ℤ) : Decidable (vertical r u) := by unfold vertical; infer_instance

def neighbors (v : Vertex) : Finset Vertex :=
  let (r,u) := v
  {(r,u-1),(r,u+1)} ∪
    (if vertical r u then {(r+1,u)} else ∅) ∪
    (if vertical (r-1) u then {(r-1,u)} else ∅)

def ball : ℕ → Finset Vertex
  | 0 => {(0,0)}
  | n+1 => ball n ∪ (ball n).biUnion neighbors

def a : ℕ → ℤ
  | 0 => 1
  | n+1 => ((ball (n+1)).card : ℤ) - (ball n).card

/-- Colin Barker's two conjectures of January 29, 2018. -/
def conjecture : Prop :=
  let A := PowerSeries.mk a
  let X : PowerSeries ℤ := PowerSeries.X
  A*((1-X)^2*(1+X+X^2)^2) = (1+X)^2*(1+X+4*X^2+X^3+X^4) ∧
    ∀ n : ℕ, 6 < n → a n = 2*a (n-3)-a (n-6)

theorem main : conjecture := by sorry

end OMA.S_oeis_a298788

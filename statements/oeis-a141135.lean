import Mathlib

/-!
# A141135, the minimum edge count of a packing of regular pentagons

Use coordinates in the basis (1, ζ), where ζ = exp(2πi/5). Then ζ² = tζ − 1
and t = 2 cos(2π/5). The five powers of ζ form the model pentagon.
Fixing circumradius one gives the same edge counts as fixing side length one
by a single similarity. A translate of any rotated model pentagon is allowed.
Reflection gives no additional pentagon shapes. Convex polygon interiors are
disjoint exactly when a nonzero linear functional weakly separates them.
The two endpoints identify an entire edge, independently of its orientation.

Barker's first claim is coefficientwise. After cancellation the denominator
is (1−x)(1−x³). The last claim uses A121149, the minimum vertex counts
of connected polyhexes, together with its exceptional initial value 1.

Sources: https://oeis.org/A141135 and https://oeis.org/A121149
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a141135

noncomputable section
abbrev Point := ℝ × ℝ
def t : ℝ := (Real.sqrt 5 - 1) / 2

def vertex (j : Fin 5) : Point :=
  [((1,0) : Point), (0,1), (-1,t), (-t,-t), (t,-1)].getD j.val (0,0)

def regular (f : Fin 5 → Point) : Prop :=
  ∃ c : Point, ∃ r s : ℝ, r^2 + t*r*s + s^2 = 1 ∧ ∀ j,
    f j = (c.1 + r*(vertex j).1 - s*(vertex j).2,
      c.2 + r*(vertex j).2 + s*(vertex j).1 + t*s*(vertex j).2)

def dot (u v : Point) : ℝ := u.1*v.1 + u.2*v.2

def separated (f g : Fin 5 → Point) : Prop :=
  ∃ u : Point, u ≠ (0,0) ∧ ∀ k l, dot u (f k) ≤ dot u (g l)

def packing {n : ℕ} (f : Fin n → Fin 5 → Point) : Prop :=
  (∀ i, regular (f i)) ∧ ∀ i j, i ≠ j → separated (f i) (f j)

def edges {n : ℕ} (f : Fin n → Fin 5 → Point) : Finset (Finset Point) := by
  classical
  exact Finset.univ.biUnion fun i => Finset.univ.image fun j => {f i j, f i (j + 1)}

def minimum (n : ℕ) : ℕ :=
  sInf {e : ℕ | ∃ f : Fin n → Fin 5 → Point, packing f ∧ (edges f).card = e}

def coeff (n d : ℕ) : ℤ := if d ≤ n then ((1 + (n-d)/3 : ℕ) : ℤ) else 0

def barker (n : ℕ) : ℤ :=
  5*coeff n 1 + 4*coeff n 2 + 4*coeff n 3 - coeff n 4 - coeff n 6 + coeff n 9 - coeff n 10

abbrev Hex := ℤ × ℤ

def hexSteps : Finset Hex := {(1,0), (-1,0), (0,1), (0,-1), (1,-1), (-1,1)}

def connected (cells : Finset Hex) : Prop := ∀ a ∈ cells, ∀ b ∈ cells,
  Relation.ReflTransGen (fun p q : Hex => p ∈ cells ∧ q ∈ cells ∧
    (q.1-p.1,q.2-p.2) ∈ hexSteps) a b

def corners (h : Hex) : Finset Hex :=
  ({(2,-1), (1,1), (-1,2), (-2,1), (-1,-1), (1,-2)} : Finset Hex).image
    fun p => (3*h.1+p.1,3*h.2+p.2)

def hexMinimum (n : ℕ) : ℕ :=
  sInf {v : ℕ | ∃ cells : Finset Hex, cells.card = n ∧ connected cells ∧
    (cells.biUnion corners).card = v}

def inA121149 (v : ℕ) : Prop := v = 1 ∨ ∃ k : ℕ, 0 < k ∧ hexMinimum k = v

theorem main :
    (∀ n : ℕ, 1 ≤ n → (minimum n : ℤ) = barker n) ∧
    (∀ m : ℕ, (minimum (m+11) : ℤ) =
      minimum (m+10) + (minimum (m+8) : ℤ) - minimum (m+7)) ∧
    (∀ n : ℕ, 2 ≤ n →
      (inA121149 n → minimum n = minimum (n-1) + 3) ∧
      (¬ inA121149 n → minimum n = minimum (n-1) + 4)) := by
  sorry

end
end OMA.S_oeis_a141135

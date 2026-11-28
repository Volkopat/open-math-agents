import Mathlib

/-!
# Explicit grid formula for the surface area cut out by a linear box

Source: https://mathoverflow.net/questions/296712 (user253775, CC BY-SA 3.0).
Credit: @connoranderson

For radius r>0, pull directions back to the unit sphere equipped with
Lebesgue surface measure, and multiply by r^(n-1). The unit-ball cone over
the accepted directions has volume equal to their surface area divided by
n. Cover the cone by equal grid cubes in [-2,2)^n. A finite inequality
test on the lower corner retains all cubes hitting the cone. Counting the
retained cubes gives rigorous upper bounds. Contracting the tests after
relaxing redundant rows gives lower bounds. Both converge to the exact
area, so their difference certifies the error even at tangencies.
All inputs to the count are elementary expressions
in the rows, widths, radius, and grid resolution. The formula works for
arbitrary real matrices, in particular positive-definite ones.
-/

namespace OMA.S_mo_296712
open MeasureTheory Metric Filter Finset
open scoped Pointwise Topology ENNReal RealInnerProductSpace
noncomputable section

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev M (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
def row {n : ℕ} (A : M n) (i : Fin n) : E n := WithLp.toLp 2 (A i)
def directions {n : ℕ} (A : M n) (a : Fin n → ℝ) (r : ℝ) : Set (sphere (0 : E n) 1) :=
  {u | ∀ i, r * |inner ℝ (row A i) (u : E n)| ≤ a i}
def area {n : ℕ} (A : M n) (a : Fin n → ℝ) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal r ^ (n-1) * (volume : Measure (E n)).toSphere (directions A a r)
def relaxed {n : ℕ} (A : M n) (a : Fin n → ℝ) (r e : ℝ) : Set (E n) :=
  {x | ‖x‖ ≤ 1+e ∧ ∀ i, r*|inner ℝ (row A i) x| ≤ a i*‖x‖ + (r*‖row A i‖+a i)*e}
def step (m : ℕ) : ℝ := ((m:ℝ)+1)⁻¹
def err (n m : ℕ) : ℝ := n * step m
abbrev Grid (n m : ℕ) := Fin n → Fin (4*(m+1))
def low {m : ℕ} (j : Fin (4*(m+1))) : ℝ := j.val * step m - 2
def corner {n m : ℕ} (g : Grid n m) : E n := WithLp.toLp 2 fun i => low (g i)
def kept {n : ℕ} (A : M n) (a : Fin n → ℝ) (r : ℝ) (m : ℕ) : Finset (Grid n m) :=
  by classical exact univ.filter fun g => corner g ∈ relaxed A a r (err n m)
def upper {n : ℕ} (A : M n) (a : Fin n → ℝ) (r : ℝ) (m : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal r ^ (n-1) * n * ((kept A a r m).card * ENNReal.ofReal (step m)^n)
def padded {n : ℕ} (A : M n) (a : Fin n → ℝ) (r : ℝ) (i : Fin n) : ℝ :=
  if r*‖row A i‖≤a i then a i+1 else a i
def innerKept {n : ℕ} (A : M n) (a : Fin n → ℝ) (r : ℝ) (m : ℕ) : Finset (Grid n m) := by
  classical exact univ.filter fun g => corner g ∈ relaxed A (padded A a r) r (-err n m)
def lower {n : ℕ} (A : M n) (a : Fin n → ℝ) (r : ℝ) (m : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal r ^ (n-1) * n * ((innerKept A a r m).card * ENNReal.ofReal (step m)^n)

theorem main : ∀ n : ℕ, 0<n → ∀ (A : M n) (a : Fin n → ℝ) (r : ℝ), 0<r → (∀ i, 0≤a i) →
    (directions A a r=Set.univ ↔ ∀ i, r*‖row A i‖≤a i) ∧
    (∀ m, lower A a r m ≤ area A a r ∧ area A a r ≤ upper A a r m) ∧
    Tendsto (upper A a r) atTop (𝓝 (area A a r)) ∧
    Tendsto (lower A a r) atTop (𝓝 (area A a r)) := by
  sorry
end
end OMA.S_mo_296712

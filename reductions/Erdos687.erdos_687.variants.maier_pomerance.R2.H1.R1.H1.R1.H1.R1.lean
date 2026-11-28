import OMAReductions.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1
import Mathlib

-- Reduction Erdos687.erdos_687.variants.maier_pomerance.R2.H1.R1.H1.R1.H1.R1 of step Erdos687.erdos_687.variants.maier_pomerance.R2.H1.R1.H1.R1.H1
-- Credit: @carterleffen

/-!
# Decomposition of the reference-tree margin into boundary integrals, tail, and scaling limit

Splits the reference-tree lower bound `1 / (50 * B^2) <= R` (Prop. 6.3 of *A quadratic bound
for Jacobsthal's function*, 2026) into four pure-Mathlib hypotheses:

* `H1`: Nested ordered boundary integrals `1 + L_2 + L_3 < 43/20`.
* `H2`: Factorial-series tail bound `F < 37/100`.
* `H3`: Omitted-mass gate-iterate sum `sum_n d_n <= 1 + L_2 + L_3 + F`.
* `H4`: Discrete-to-continuous scaling limit `B(z)^2 * R(z) -> exp(gamma) * (-1/100 + 2 * I / M)`
  with `0 < M <= 8` and `I = 8/3 - sum_n d_n`.

Together `H1`-`H3` give `I > 11/75`, so `2 * I / M > 3/100`, whence the limit exceeds `1/50`.
-/

open Filter Finset MeasureTheory
open scoped Classical Topology
namespace OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1_H1_R1
private theorem finish {b r : ℝ} (h : 1/50 < b^2*r) : 1/(50*b^2) ≤ r := by
  by_cases hz : b = 0
  · norm_num [hz] at h
  · apply (div_le_iff₀ (mul_pos (by norm_num) (sq_pos_of_ne_zero hz))).mpr
    linarith [show r*(50*b^2)=50*(b^2*r) by ring]


def H1 : Prop :=
  let A := ∫ t : ℝ in 1..2, ∫ x : ℝ in t..2,
    ((((x+2*t)^3-8)/12)-(x+2*t-2))/(x*t^2)
  let D := ∫ t : ℝ in 1..2, ∫ u : ℝ in t..2, ∫ x : ℝ in u..2,
    ((x+u+2*t)^3-8*x^3)/(12*x*u*t^2)
  1 + A + D < 43/20

def H2 : Prop :=
  let l := Real.log 2
  let f := fun n : ℕ => ((n : ℝ) + 5)^2 * (l^(n+4) / ((n+4).factorial : ℝ))
  Summable f ∧ (1/2 : ℝ) * (3/l - 2) * (∑' n, f n) < 37/100

def H3 : Prop :=
  let U := fun (i : Bool) (r b : ℝ) =>
    if i then max 1 (min (min 2 b) ((r-2)/2)) else max 1 (min 2 b)
  let g := fun (i : Bool) (r b : ℝ) =>
    if i then (U true r b)⁻¹ - (U false r b)⁻¹ else 0
  let K := fun (v : Bool → ℝ → ℝ → ℝ) (i : Bool) (r b : ℝ) =>
    ∫ x : ℝ in 1..U i r b, v (!i) (r-x) x / max 1 x
  let d := fun n : ℕ =>
    (∫ y in Set.Ioi (1:ℝ), 2*(y^2-1)*(K^[n] g) false (2*y+2) 2) +
     ∫ y in Set.Ioi (0:ℝ), 2*y^2*(K^[n] g) true (2*y+2) 2
  let A := ∫ t : ℝ in 1..2, ∫ x : ℝ in t..2,
    ((((x+2*t)^3-8)/12)-(x+2*t-2))/(x*t^2)
  let D := ∫ t : ℝ in 1..2, ∫ u : ℝ in t..2, ∫ x : ℝ in u..2,
    ((x+u+2*t)^3-8*x^3)/(12*x*u*t^2)
  let l := Real.log 2
  let f := fun n : ℕ => ((n : ℝ) + 5)^2 * (l^(n+4) / ((n+4).factorial : ℝ))
  let F := (1/2 : ℝ) * (3/l - 2) * (∑' n, f n)
  Summable d ∧ (∑' n, d n) ≤ 1 + A + D + F

def H4 : Prop :=
  let U := fun (i : Bool) (r b : ℝ) =>
    if i then max 1 (min (min 2 b) ((r-2)/2)) else max 1 (min 2 b)
  let g := fun (i : Bool) (r b : ℝ) =>
    if i then (U true r b)⁻¹ - (U false r b)⁻¹ else 0
  let K := fun (v : Bool → ℝ → ℝ → ℝ) (i : Bool) (r b : ℝ) =>
    ∫ x : ℝ in 1..U i r b, v (!i) (r-x) x / max 1 x
  let d := fun n : ℕ =>
    (∫ y in Set.Ioi (1:ℝ), 2*(y^2-1)*(K^[n] g) false (2*y+2) 2) +
     ∫ y in Set.Ioi (0:ℝ), 2*y^2*(K^[n] g) true (2*y+2) 2
  let I := (8/3 : ℝ) - ∑' n, d n
  let S := fun z : ℝ =>
    let L := Real.log z
    let Y := ⌊z ^ 2 / L ^ 2⌋₊
    let w := L / (Real.log L) ^ 2
    let B := L / Real.log w
    let P := (Finset.Icc (⌊w⌋₊ + 1) ⌊z⌋₊).filter Nat.Prime
    let e := fun p : ℕ => Real.log (p : ℝ) / Real.log w
    let T := P.powerset.filter fun d => ∀ p ∈ d,
      let A := d.filter fun q => p ≤ q
      Even A.card → max (2 * e p) (e p + 2) ≤
        Real.log ((Y : ℝ) / (∏ q ∈ A, (q : ℝ))) / Real.log w + 2 - 1/100
    let R := ∑ d ∈ T, (-1 : ℝ) ^ d.card / (∏ p ∈ d, (p : ℝ))
    B^2 * R
  ∃ M : ℝ, 0 < M ∧ M ≤ 8 ∧
    Tendsto S atTop (𝓝 (Real.exp Real.eulerMascheroniConstant * (-(1:ℝ)/100 + 2*I/M)))

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1.H1 := by
  intro a t c b
  let A := ∫ t : ℝ in 1..2, ∫ x : ℝ in t..2,
    ((((x+2*t)^3-8)/12)-(x+2*t-2))/(x*t^2)
  let D := ∫ t : ℝ in 1..2, ∫ u : ℝ in t..2, ∫ x : ℝ in u..2,
    ((x+u+2*t)^3-8*x^3)/(12*x*u*t^2)
  let l := Real.log 2
  let f := fun n : ℕ => ((n : ℝ) + 5)^2 * (l^(n+4) / ((n+4).factorial : ℝ))
  let F := (1/2 : ℝ) * (3/l - 2) * (∑' n, f n)
  let U := fun (i : Bool) (r b : ℝ) =>
    if i then max 1 (min (min 2 b) ((r-2)/2)) else max 1 (min 2 b)
  let g := fun (i : Bool) (r b : ℝ) =>
    if i then (U true r b)⁻¹ - (U false r b)⁻¹ else 0
  let K := fun (v : Bool → ℝ → ℝ → ℝ) (i : Bool) (r b : ℝ) =>
    ∫ x : ℝ in 1..U i r b, v (!i) (r-x) x / max 1 x
  let d := fun n : ℕ =>
    (∫ y in Set.Ioi (1:ℝ), 2*(y^2-1)*(K^[n] g) false (2*y+2) 2) +
     ∫ y in Set.Ioi (0:ℝ), 2*y^2*(K^[n] g) true (2*y+2) 2
  change 1 + A + D < 43/20 at a
  change Summable f ∧ F < 37/100 at t
  change Summable d ∧ (∑' n, d n) ≤ 1 + A + D + F at c
  let I := (8/3 : ℝ) - ∑' n, d n
  have hi : (11:ℝ)/75 < I := by
    dsimp only [I]
    linarith [t.2,c.2]
  obtain ⟨M, hM, h8, conv⟩ := b
  have ratio : (3:ℝ)/100 < 2*I/M := (lt_div_iff₀ hM).mpr (by linarith)
  have hl : (1:ℝ)/50 < -(1:ℝ)/100 + 2*I/M := by linarith
  have heg : (1:ℝ) ≤ Real.exp Real.eulerMascheroniConstant :=
    Real.one_le_exp (by linarith [Real.one_half_lt_eulerMascheroniConstant])
  have bound : (1:ℝ)/50 < Real.exp Real.eulerMascheroniConstant * (-(1:ℝ)/100 + 2*I/M) :=
    hl.trans_le (le_mul_of_one_le_left (by linarith) heg)
  have he := conv.eventually (Ioi_mem_nhds bound)
  filter_upwards [he] with z hz
  apply finish
  exact hz
end OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1_H1_R1_H1_R1

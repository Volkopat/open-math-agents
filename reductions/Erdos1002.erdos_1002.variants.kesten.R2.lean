import FormalConjectures.ErdosProblems.«1002»

-- Reduction of the Kesten variant to a finite count and a discretization estimate.
-- Credit: @sumkr95
namespace OMA.R_Erdos1002_erdos_1002_variants_kesten_R2

open Filter MeasureTheory Real Set Topology
open scoped BigOperators Classical

-- Limiting distribution of the finite modular counts.
def H1 : Prop :=
  let grid := fun (n : ℕ) (c : ℝ) =>
    let q := n ^ 3
    let pairs := (Finset.range q).product (Finset.range q)
    let good := pairs.filter fun ab =>
      (1 / Real.log (n : ℝ)) *
        ((n : ℝ) / 2 - (∑ k ∈ Finset.Icc 1 n,
          (((ab.2 + k * ab.1) % q : ℕ) : ℝ)) / (q : ℝ)) ≤ c
    (good.card : ℝ) / (q : ℝ) ^ 2
  ∃ ρ : ℝ, 0 < ρ ∧ ∀ c : ℝ,
    Tendsto (fun n => grid n c) atTop
      (𝓝 ((1 / π) * ∫ t in Iic (ρ * c), 1 / (1 + t ^ 2)))

-- The continuous and finite distribution functions differ by a quantity tending to zero.
-- A bound uniform in c for n ≥ 3 is (1 + 1/n) * n*(n+3)/(2*n^3).
-- In a cell write α=(a+u)/q and β=(b+v)/q. The continuous unnormalized sum
-- equals the grid sum minus D=∑(v+k*u)/q plus the number of wraps. Here
-- D ≤ B=n*(n+3)/(2*q). For fixed a,u,v, uniform b makes each residue
-- uniform and bounds the probability of any wrap by B. For fixed α the
-- continuous sum has slope -n on at most n+1 intervals in β, so it falls
-- in any interval of length B with probability at most (1+1/n)*B.
def H2 : Prop :=
  let grid := fun (n : ℕ) (c : ℝ) =>
    let q := n ^ 3
    let pairs := (Finset.range q).product (Finset.range q)
    let good := pairs.filter fun ab =>
      (1 / Real.log (n : ℝ)) *
        ((n : ℝ) / 2 - (∑ k ∈ Finset.Icc 1 n,
          (((ab.2 + k * ab.1) % q : ℕ) : ℝ)) / (q : ℝ)) ≤ c
    (good.card : ℝ) / (q : ℝ) ^ 2
  let source := fun (n : ℕ) (c : ℝ) =>
    (volume {p : ℝ × ℝ |
      let ⟨α, β⟩ := p
      α ∈ Icc (0 : ℝ) 1 ∧ β ∈ Icc (0 : ℝ) 1 ∧
        (1 / Real.log (n : ℝ)) * ∑ k ∈ Finset.Icc (1 : ℕ) n,
          (1 / 2 - Int.fract (β + α * k)) ≤ c}).toReal
  ∀ c : ℝ, Tendsto (fun n => source n c - grid n c) atTop (𝓝 0)

theorem main : H1 → H2 → type_of% @Erdos1002.erdos_1002.variants.kesten := by
  intro hgrid herr
  obtain ⟨ρ, hρ, hlim⟩ := hgrid
  refine ⟨ρ, hρ, ?_⟩
  intro g c
  have h := (herr c).add (hlim c)
  simpa only [Pi.add_apply, sub_add_cancel, zero_add] using h

end OMA.R_Erdos1002_erdos_1002_variants_kesten_R2

import OMAReductions.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R1_H2_R2

-- Reduction Arxiv.2610.08796.exists_isPolyTime_bayesNash.R1.H2.R2.H1.R1 of step R1.H2.R2.H1
-- Credit: @paynebrowning
-- Each H becomes its own step once this file is accepted. Proving all of them closes R1.H2.R2.H1.

/-!
Khachiyan's modular 3-part reduction of exact rational LP feasibility (`R1.H2.R2.H1`, for PR #13521):

Given a rational linear inequality system `(d, cons)` in `d.length` variables (dimension given in
unary via `d : List Bool`), Khachiyan's polynomial-time algorithm splits cleanly into:

* `H1` (Perturbation + Exact Vertex Rounding): polynomial-time `perturb` and `round` maps.
  `perturb (d, cons)` pads/truncates rows to length `d.length`, clears row denominators, and
  relaxes RHS entries by a Hadamard-scale `ε = poly(input)^{-1}` (yielding positive rational radii
  `δ, R` and a row-length-normalized system `(d', cons')`) so that whenever `(d, cons)` is
  feasible, the perturbed system contains an interior `ℓ∞` box
  `x₀ + [-δ, δ]^{d'.length} ⊆ [-R, R]^{d'.length}`. Conversely, `round ((d, cons), y)` purifies
  any `y ∈ [-R, R]^{d'.length}` satisfying `cons'` to a vertex of the bounded perturbed polytope
  and solves the unperturbed integer basis system to recover an exact feasible point of `(d, cons)`.
* `H2` (Bounded Full-Dimensional Rational Ellipsoid): given a row-normalized system `(d, cons)`
  and positive rational radii `δ, R` whose feasible set contains an interior `ℓ∞` box
  `x₀ + [-δ, δ]^{d.length} ⊆ [-R, R]^{d.length}`, a polynomial-time ellipsoid solver returns a
  feasible rational point `y ∈ [-R, R]^{d.length}` in `O(d.length² log(d.length * R / δ))`
  iterations.
* `H3` (`IsPolyTime` Composition): closure of `IsPolyTime` under `z ↦ round (z, ellip (perturb z))`.
-/

namespace OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R1_H2_R2_H1_R1

open ComplexityTheory Arxiv.«2610.08796»

/-- Khachiyan perturbation and exact basis/vertex rounding for unary-dimension rational LP
systems `(d, cons)`: polynomial-time maps `perturb` and `round` reducing feasibility to finding
a bounded point in a row-normalized system containing an interior `ℓ∞` box
`x₀ + [-δ, δ]^{d'.length} ⊆ [-R, R]^{d'.length}` whenever the original system is feasible. -/
def H1 : Prop :=
  ∃ (perturb : (List Bool × List (List ℚ × ℚ)) → (List Bool × List (List ℚ × ℚ)) × (ℚ × ℚ))
    (round : (List Bool × List (List ℚ × ℚ)) × List ℚ → List ℚ),
    IsPolyTime perturb ∧ IsPolyTime round ∧
    ∀ (d : List Bool) (cons : List (List ℚ × ℚ)),
      let p := perturb (d, cons)
      let d' := p.1.1
      let cons' := p.1.2
      let δ := p.2.1
      let R := p.2.2
      0 < δ ∧ 0 < R ∧
      (∀ r ∈ cons', r.1.length = d'.length) ∧
      ((∃ x : List ℚ, x.length = d.length ∧
        ∀ r ∈ cons, (∑ j : Fin d.length, r.1[j.val]?.getD 0 * x[j.val]?.getD 0) ≤ r.2) →
        ∃ x₀ : List ℚ, x₀.length = d'.length ∧
          (∀ j : Fin d'.length, |x₀[j.val]?.getD 0| + δ ≤ R) ∧
          ∀ y : List ℚ, y.length = d'.length →
            (∀ j : Fin d'.length, |y[j.val]?.getD 0 - x₀[j.val]?.getD 0| ≤ δ) →
            ∀ r ∈ cons', (∑ j : Fin d'.length, r.1[j.val]?.getD 0 * y[j.val]?.getD 0) ≤ r.2) ∧
      (∀ y : List ℚ, y.length = d'.length →
        (∀ j : Fin d'.length, |y[j.val]?.getD 0| ≤ R) →
        (∀ r ∈ cons', (∑ j : Fin d'.length, r.1[j.val]?.getD 0 * y[j.val]?.getD 0) ≤ r.2) →
        (round ((d, cons), y)).length = d.length ∧
        ∀ r ∈ cons,
          (∑ j : Fin d.length, r.1[j.val]?.getD 0 * (round ((d, cons), y))[j.val]?.getD 0) ≤ r.2)

/-- Bounded full-dimensional rational ellipsoid method: given a row-normalized rational linear
inequality system `(d, cons)` and positive radii `(δ, R)` such that an interior `ℓ∞` box
`x₀ + [-δ, δ]^{d.length} ⊆ [-R, R]^{d.length}` is feasible, compute in polynomial time a feasible
point `y ∈ [-R, R]^{d.length}`. -/
def H2 : Prop :=
  ∃ ellip : (List Bool × List (List ℚ × ℚ)) × (ℚ × ℚ) → List ℚ,
    IsPolyTime ellip ∧
    ∀ (d : List Bool) (cons : List (List ℚ × ℚ)) (δ R : ℚ),
      0 < δ → 0 < R →
      (∀ r ∈ cons, r.1.length = d.length) →
      (∃ x₀ : List ℚ, x₀.length = d.length ∧
        (∀ j : Fin d.length, |x₀[j.val]?.getD 0| + δ ≤ R) ∧
        ∀ y : List ℚ, y.length = d.length →
          (∀ j : Fin d.length, |y[j.val]?.getD 0 - x₀[j.val]?.getD 0| ≤ δ) →
          ∀ r ∈ cons, (∑ j : Fin d.length, r.1[j.val]?.getD 0 * y[j.val]?.getD 0) ≤ r.2) →
      (ellip ((d, cons), (δ, R))).length = d.length ∧
      (∀ j : Fin d.length, |(ellip ((d, cons), (δ, R)))[j.val]?.getD 0| ≤ R) ∧
      ∀ r ∈ cons,
        (∑ j : Fin d.length, r.1[j.val]?.getD 0 * (ellip ((d, cons), (δ, R)))[j.val]?.getD 0) ≤ r.2

/-- Polynomial-time closure under the pipeline `z ↦ round (z, ellip (perturb z))`. -/
def H3 : Prop :=
  ∀ (perturb : (List Bool × List (List ℚ × ℚ)) → (List Bool × List (List ℚ × ℚ)) × (ℚ × ℚ))
    (ellip : (List Bool × List (List ℚ × ℚ)) × (ℚ × ℚ) → List ℚ)
    (round : (List Bool × List (List ℚ × ℚ)) × List ℚ → List ℚ),
    IsPolyTime perturb → IsPolyTime ellip → IsPolyTime round →
    IsPolyTime (fun z : List Bool × List (List ℚ × ℚ) => round (z, ellip (perturb z)))

theorem main : H1 → H2 → H3 →
    OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R1_H2_R2.H1 := by
  intro h1 h2 h3
  obtain ⟨perturb, round, hpt, hrd, hspec⟩ := h1
  obtain ⟨ellip, hell, hespec⟩ := h2
  refine ⟨fun z => round (z, ellip (perturb z)), h3 perturb ellip round hpt hell hrd, ?_⟩
  intro d cons hfeas
  obtain ⟨hδ, hR, hrows', hcomp, hsound⟩ := hspec d cons
  obtain ⟨hlen, hbd, hsat⟩ := hespec (perturb (d, cons)).1.1 (perturb (d, cons)).1.2
    (perturb (d, cons)).2.1 (perturb (d, cons)).2.2 hδ hR hrows' (hcomp hfeas)
  exact hsound (ellip (perturb (d, cons))) hlen hbd hsat

end OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R1_H2_R2_H1_R1

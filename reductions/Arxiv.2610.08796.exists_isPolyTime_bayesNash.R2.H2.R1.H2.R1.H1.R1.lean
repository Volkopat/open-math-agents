import OMAReductions.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R2_H2_R1_H2_R1

-- Reduction Arxiv.2610.08796.exists_isPolyTime_bayesNash.R2.H2.R1.H2.R1.H1.R1 of step R2.H2.R1.H2.R1.H1
-- Credit: @paynebrowning
-- Each H becomes its own step once this file is accepted. Proving all of them closes R2.H2.R1.H2.R1.H1.

/-!
Khachiyan's modular 3-part reduction of exact rational LP feasibility (`R2.H2.R1.H2.R1.H1`):

Given a well-formed rational linear inequality system `(n, cons)` (`∀ r ∈ cons, r.1.length = n`
and `n = 0 ∨ cons ≠ []`, ensuring `n` is bounded by the bit-length of the input), Khachiyan's
polynomial-time algorithm splits cleanly into:

* `H1` (Perturbation + Exact Vertex Rounding): polynomial-time `perturb` and `round` maps.
  `perturb (n, cons)` clears row denominators and relaxes RHS entries by a Hadamard-scale
  `ε = poly(input)^{-1}` (yielding positive rational radii `δ, R` and a well-formed system
  `(n', cons')`) so that whenever `(n, cons)` is feasible, the perturbed system contains an
  interior `ℓ∞` box `x₀ + [-δ, δ]^{n'} ⊆ [-R, R]^{n'}`. Conversely, `round ((n, cons), y)`
  purifies any `y ∈ [-R, R]^{n'}` satisfying `cons'` to a vertex of the bounded perturbed
  polytope and solves the unperturbed integer basis system to recover an exact feasible point
  of `(n, cons)`.
* `H2` (Bounded Full-Dimensional Rational Ellipsoid): given a well-formed system `(n, cons)`
  and positive rational radii `δ, R` whose feasible set contains an interior `ℓ∞` box
  `x₀ + [-δ, δ]^n ⊆ [-R, R]^n`, a polynomial-time ellipsoid solver returns a feasible rational
  point `y ∈ [-R, R]^n` in `O(n² log(n R / δ))` iterations.
* `H3` (`IsPolyTime` Composition): closure of `IsPolyTime` under `z ↦ round (z, ellip (perturb z))`.
-/

namespace OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R2_H2_R1_H2_R1_H1_R1

open ComplexityTheory Arxiv.«2610.08796»

/-- Khachiyan perturbation and exact basis/vertex rounding: polynomial-time maps `perturb` and
`round` reducing arbitrary well-formed rational LP feasibility to finding a bounded point in a
well-formed system guaranteed to contain an interior `ℓ∞` box `x₀ + [-δ, δ]^{n'} ⊆ [-R, R]^{n'}`
whenever the original system is feasible. -/
def H1 : Prop :=
  ∃ (perturb : (ℕ × List (List ℚ × ℚ)) → (ℕ × List (List ℚ × ℚ)) × (ℚ × ℚ))
    (round : (ℕ × List (List ℚ × ℚ)) × List ℚ → List ℚ),
    IsPolyTime perturb ∧ IsPolyTime round ∧
    ∀ (n : ℕ) (cons : List (List ℚ × ℚ)),
      (∀ r ∈ cons, r.1.length = n) → (n = 0 ∨ cons ≠ []) →
      let p := perturb (n, cons)
      let n' := p.1.1
      let cons' := p.1.2
      let δ := p.2.1
      let R := p.2.2
      0 < δ ∧ 0 < R ∧
      (∀ r ∈ cons', r.1.length = n') ∧ (n' = 0 ∨ cons' ≠ []) ∧
      ((∃ x : List ℚ, x.length = n ∧
        ∀ r ∈ cons, (∑ j : Fin n, r.1[j.val]?.getD 0 * x[j.val]?.getD 0) ≤ r.2) →
        ∃ x₀ : List ℚ, x₀.length = n' ∧
          (∀ j : Fin n', |x₀[j.val]?.getD 0| + δ ≤ R) ∧
          ∀ y : List ℚ, y.length = n' →
            (∀ j : Fin n', |y[j.val]?.getD 0 - x₀[j.val]?.getD 0| ≤ δ) →
            ∀ r ∈ cons', (∑ j : Fin n', r.1[j.val]?.getD 0 * y[j.val]?.getD 0) ≤ r.2) ∧
      (∀ y : List ℚ, y.length = n' →
        (∀ j : Fin n', |y[j.val]?.getD 0| ≤ R) →
        (∀ r ∈ cons', (∑ j : Fin n', r.1[j.val]?.getD 0 * y[j.val]?.getD 0) ≤ r.2) →
        (round ((n, cons), y)).length = n ∧
        ∀ r ∈ cons,
          (∑ j : Fin n, r.1[j.val]?.getD 0 * (round ((n, cons), y))[j.val]?.getD 0) ≤ r.2)

/-- Bounded full-dimensional rational ellipsoid method: given a well-formed rational linear
inequality system `(n, cons)` and positive radii `(δ, R)` such that an interior `ℓ∞` box
`x₀ + [-δ, δ]^n ⊆ [-R, R]^n` is feasible, compute in polynomial time a feasible point
`y ∈ [-R, R]^n`. -/
def H2 : Prop :=
  ∃ ellip : (ℕ × List (List ℚ × ℚ)) × (ℚ × ℚ) → List ℚ,
    IsPolyTime ellip ∧
    ∀ (n : ℕ) (cons : List (List ℚ × ℚ)) (δ R : ℚ),
      0 < δ → 0 < R →
      (∀ r ∈ cons, r.1.length = n) → (n = 0 ∨ cons ≠ []) →
      (∃ x₀ : List ℚ, x₀.length = n ∧
        (∀ j : Fin n, |x₀[j.val]?.getD 0| + δ ≤ R) ∧
        ∀ y : List ℚ, y.length = n →
          (∀ j : Fin n, |y[j.val]?.getD 0 - x₀[j.val]?.getD 0| ≤ δ) →
          ∀ r ∈ cons, (∑ j : Fin n, r.1[j.val]?.getD 0 * y[j.val]?.getD 0) ≤ r.2) →
      (ellip ((n, cons), (δ, R))).length = n ∧
      (∀ j : Fin n, |(ellip ((n, cons), (δ, R)))[j.val]?.getD 0| ≤ R) ∧
      ∀ r ∈ cons,
        (∑ j : Fin n, r.1[j.val]?.getD 0 * (ellip ((n, cons), (δ, R)))[j.val]?.getD 0) ≤ r.2

/-- Polynomial-time closure under the pipeline `z ↦ round (z, ellip (perturb z))`. -/
def H3 : Prop :=
  ∀ (perturb : (ℕ × List (List ℚ × ℚ)) → (ℕ × List (List ℚ × ℚ)) × (ℚ × ℚ))
    (ellip : (ℕ × List (List ℚ × ℚ)) × (ℚ × ℚ) → List ℚ)
    (round : (ℕ × List (List ℚ × ℚ)) × List ℚ → List ℚ),
    IsPolyTime perturb → IsPolyTime ellip → IsPolyTime round →
    IsPolyTime (fun z : ℕ × List (List ℚ × ℚ) => round (z, ellip (perturb z)))

theorem main : H1 → H2 → H3 →
    OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R2_H2_R1_H2_R1.H1 := by
  intro h1 h2 h3
  obtain ⟨perturb, round, hpt, hrd, hspec⟩ := h1
  obtain ⟨ellip, hell, hespec⟩ := h2
  refine ⟨fun z => round (z, ellip (perturb z)), h3 perturb ellip round hpt hell hrd, ?_⟩
  intro n cons hrows hne hfeas
  obtain ⟨hδ, hR, hrows', hne', hcomp, hsound⟩ := hspec n cons hrows hne
  obtain ⟨hlen, hbd, hsat⟩ := hespec (perturb (n, cons)).1.1 (perturb (n, cons)).1.2
    (perturb (n, cons)).2.1 (perturb (n, cons)).2.2 hδ hR hrows' hne' (hcomp hfeas)
  exact hsound (ellip (perturb (n, cons))) hlen hbd hsat

end OMA.R_Arxiv_2610_08796_exists_isPolyTime_bayesNash_R2_H2_R1_H2_R1_H1_R1

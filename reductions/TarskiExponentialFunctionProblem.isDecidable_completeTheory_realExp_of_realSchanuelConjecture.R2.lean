import FormalConjectures.Wikipedia.TarskiExponentialFunctionProblem
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Convex.Extrema

/-!
# Testing exponential polynomials at regular zeros
Credit: @yuka30240

An integer polynomial in the coordinates and their exponentials is a list of
monomials. Each factor is tagged as a coordinate (false) or its exponential
(true). Coordinates beyond the length of a tuple are set to zero. A list of
n polynomials specifies a square system in n variables.

The two model-theoretic inputs are the existential axiomatization relative to
a recursive base and the existence of witnesses in exponential algebraic
closure. The arithmetic input is the weak Schanuel separation bound. See
Macintyre and Wilkie, On the decidability of the real exponential field
(1996), sections 2 and 5, and Berarducci and Gallinaro, arXiv:2603.08365v3,
Conjecture 13.4 and the proof of Theorem 14.2.
-/

namespace OMA.R_TarskiExponentialFunctionProblem_isDecidable_completeTheory_realExp_of_realSchanuelConjecture_R2

open FirstOrder Filter Metric Set
open scoped Topology

/-- A smaller residual inside the ball forces a regular zero. At an interior
minimum the inverse function theorem makes the residual norm locally minimal
in the entire target, where its only minimum is zero. -/
theorem zero_of_boundary_gap {n : ℕ} {F : (Fin n → ℝ) → (Fin n → ℝ)}
    (hF : ContDiff ℝ 1 F) {a b : Fin n → ℝ} {r : ℝ}
    (hb : b ∈ ball a r)
    (hboundary : ∀ z ∈ sphere a r, ‖F b‖ < ‖F z‖)
    (hinv : ∀ z ∈ closedBall a r, IsUnit (fderiv ℝ F z)) :
    ∃ x ∈ closedBall a r, F x = 0 ∧ IsUnit (fderiv ℝ F x) := by
  obtain ⟨x, hx, hmin⟩ := (isCompact_closedBall a r).exists_isMinOn
    ⟨b, ball_subset_closedBall hb⟩ hF.continuous.norm.continuousOn
  have hxi : x ∈ ball a r := by
    refine lt_of_le_of_ne (mem_closedBall.mp hx) ?_
    intro he
    exact (hboundary x (mem_sphere.mpr he)).not_ge (hmin (ball_subset_closedBall hb))
  have hsurj := (ContinuousLinearMap.isUnit_iff_bijective.mp (hinv x hx)).2
  have hopen := (hF.contDiffAt.hasStrictFDerivAt (by norm_num)).map_nhds_eq_of_surj
    (LinearMap.range_eq_top.mpr hsurj)
  have hm : IsLocalMin norm (F x) := by
    change ∀ᶠ y in 𝓝 (F x), ‖F x‖ ≤ ‖y‖
    rw [← hopen, Filter.eventually_map]
    exact Filter.mem_of_superset (closedBall_mem_nhds_of_mem hxi) fun y hy => hmin hy
  have hzero := IsMinOn.of_isLocalMin_of_convex_univ hm (convexOn_norm convex_univ) 0
  exact ⟨x, hx, norm_le_zero_iff.mp (by simpa using hzero), hinv x hx⟩

/-- Every regular zero admits a rational box on which the Jacobian stays
invertible and a prescribed open condition holds. A second rational point
in the box witnesses the strict boundary gap. -/
theorem rational_box_at_zero {n : ℕ} {F : (Fin n → ℝ) → (Fin n → ℝ)}
    (hF : ContDiff ℝ 1 F) {x : Fin n → ℝ} (hx : F x = 0)
    (hi : IsUnit (fderiv ℝ F x)) {U : Set (Fin n → ℝ)} (hU : U ∈ 𝓝 x) :
    ∃ (a b : Fin n → ℚ) (r : ℚ), 0 < r ∧
      (fun i => (b i : ℝ)) ∈ ball (fun i => (a i : ℝ)) (r : ℝ) ∧
      (∀ z ∈ closedBall (fun i => (a i : ℝ)) (r : ℝ), z ∈ U ∧ IsUnit (fderiv ℝ F z)) ∧
      ∀ z ∈ sphere (fun i => (a i : ℝ)) (r : ℝ), ‖F (fun i => (b i : ℝ))‖ < ‖F z‖ := by
  let e := ContinuousLinearEquiv.ofBijective (fderiv ℝ F x)
    (LinearMap.ker_eq_bot.mpr (ContinuousLinearMap.isUnit_iff_bijective.mp hi).1)
    (LinearMap.range_eq_top.mpr (ContinuousLinearMap.isUnit_iff_bijective.mp hi).2)
  have hd : HasStrictFDerivAt F (e : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) x :=
    hF.contDiffAt.hasStrictFDerivAt (by norm_num)
  let chart := hd.toOpenPartialHomeomorph F
  have hchart : chart.source ∈ 𝓝 x := chart.open_source.mem_nhds hd.mem_toOpenPartialHomeomorph_source
  have hreg : ∀ᶠ z in 𝓝 x, IsUnit (fderiv ℝ F z) :=
    (hF.continuous_fderiv (by norm_num)).continuousAt (Units.isOpen.mem_nhds hi)
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hU (inter_mem hchart hreg))
  obtain ⟨r, hr, hrδ⟩ := exists_rat_btwn (show (0 : ℝ) < δ / 2 by positivity)
  have dense : DenseRange (fun a : Fin n → ℚ => fun i => (a i : ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  obtain ⟨a, ha⟩ := dense.exists_mem_open isOpen_ball ⟨x, mem_ball_self hr⟩
  let c : Fin n → ℝ := fun i => a i
  have hc : dist c x < (r : ℝ) := ha
  have hinside : x ∈ ball c (r : ℝ) := by rwa [mem_ball, dist_comm]
  have hball : closedBall c (r : ℝ) ⊆ ball x δ := by
    intro z hz
    have := dist_triangle z c x
    have := mem_closedBall.mp hz
    change dist z x < δ
    linarith
  have hbdata := hball.trans hsub
  refine ⟨a, ?_⟩
  have hchoose (V : Set (Fin n → ℝ)) (hV : V ∈ 𝓝 x) :
      ∃ b : Fin n → ℚ, (fun i => (b i : ℝ)) ∈ ball c (r : ℝ) ∩ V :=
    dense.mem_nhds (inter_mem (isOpen_ball.mem_nhds hinside) hV)
  by_cases hs : (sphere c (r : ℝ)).Nonempty
  · obtain ⟨z, hz, hmin⟩ := (isCompact_sphere c (r : ℝ)).exists_isMinOn hs
      hF.continuous.norm.continuousOn
    have hz_ne : F z ≠ 0 := by
      intro h
      have hzx : z = x := chart.injOn (hbdata (sphere_subset_closedBall hz)).2.1
        hd.mem_toOpenPartialHomeomorph_source (h.trans hx.symm)
      exact (mem_sphere.mp hz).not_lt (hzx ▸ hinside)
    have hpos : ‖F x‖ < ‖F z‖ := by simpa [hx] using norm_pos_iff.mpr hz_ne
    obtain ⟨b, hb, hsmall⟩ := hchoose _ (hF.continuous.norm.continuousAt.eventually_lt
      continuousAt_const hpos)
    exact ⟨b, r, by exact_mod_cast hr, hb, fun y hy => ⟨(hbdata hy).1, (hbdata hy).2.2⟩,
      fun y hy => lt_of_lt_of_le hsmall (hmin hy)⟩
  · obtain ⟨b, hb, -⟩ := hchoose univ univ_mem
    exact ⟨b, r, by exact_mod_cast hr, hb, fun y hy => ⟨(hbdata hy).1, (hbdata hy).2.2⟩,
      fun z hz => (hs ⟨z, hz⟩).elim⟩

/-- The recursive base of Macintyre and Wilkie, together with effective
proof search, reduces the full theory to enumerating soluble equations. -/
def H1 : Prop :=
  let P := List (ℤ × List (Bool × ℕ))
  let val := fun (p : P) {n : ℕ} (x : Fin n → ℝ) =>
    (p.map fun t => (t.1 : ℝ) * (t.2.map fun v =>
      let u := if h : v.2 < n then x ⟨v.2, h⟩ else 0
      if v.1 then Real.exp u else u).prod).sum
  (∃ test : P × (List P × ℕ) → Bool, Computable test ∧ ∀ p,
    (∃ w, test (p, w) = true) ↔ ∃ (n : ℕ) (x : Fin n → ℝ), val p x = 0) →
    (Language.orderedExpField.completeTheory ℝ).IsDecidable

/-- Exponential-algebraic witnesses. A nonempty zero set has a point
that can be extended to a nonsingular square system. -/
def H2 : Prop :=
  let P := List (ℤ × List (Bool × ℕ))
  let val := fun (p : P) {n : ℕ} (x : Fin n → ℝ) =>
    (p.map fun t => (t.1 : ℝ) * (t.2.map fun v =>
      let u := if h : v.2 < n then x ⟨v.2, h⟩ else 0
      if v.1 then Real.exp u else u).prod).sum
  let sys := fun (s : List P) (x : Fin s.length → ℝ) (j : Fin s.length) => val (s.get j) x
  ∀ p : P, (∃ (n : ℕ) (x : Fin n → ℝ), val p x = 0) →
    ∃ (s : List P) (x : Fin s.length → ℝ),
      sys s x = 0 ∧ IsUnit (fderiv ℝ (sys s) x) ∧ val p x = 0

/-- Effective verification of strict inequalities on compact rational boxes.
The witness t can encode the box, the interior sample and finite interval
enclosures for the values and the Jacobian determinant. -/
def H3 : Prop :=
  let P := List (ℤ × List (Bool × ℕ))
  let val := fun (p : P) {n : ℕ} (x : Fin n → ℝ) =>
    (p.map fun t => (t.1 : ℝ) * (t.2.map fun v =>
      let u := if h : v.2 < n then x ⟨v.2, h⟩ else 0
      if v.1 then Real.exp u else u).prod).sum
  let sys := fun (s : List P) (x : Fin s.length → ℝ) (j : Fin s.length) => val (s.get j) x
  ∃ check : ((P × List P) × ℕ) × ℕ → Bool, Computable check ∧ ∀ p s k,
    (∃ t, check (((p, s), k), t) = true) ↔
      ∃ (a b : Fin s.length → ℚ) (r : ℚ), 0 < r ∧
        (fun i => (b i : ℝ)) ∈ ball (fun i => (a i : ℝ)) (r : ℝ) ∧
        (∀ z ∈ closedBall (fun i => (a i : ℝ)) (r : ℝ),
          |val p z| < 1 / ((k : ℝ) + 1) ∧ IsUnit (fderiv ℝ (sys s) z)) ∧
        ∀ z ∈ sphere (fun i => (a i : ℝ)) (r : ℝ),
          ‖sys s (fun i => (b i : ℝ))‖ < ‖sys s z‖

/-- The weak Schanuel bound for the total exponential, in reciprocal
integer precision, under the real Schanuel conjecture. -/
def H4 : Prop :=
  let P := List (ℤ × List (Bool × ℕ))
  let val := fun (p : P) {n : ℕ} (x : Fin n → ℝ) =>
    (p.map fun t => (t.1 : ℝ) * (t.2.map fun v =>
      let u := if h : v.2 < n then x ⟨v.2, h⟩ else 0
      if v.1 then Real.exp u else u).prod).sum
  let sys := fun (s : List P) (x : Fin s.length → ℝ) (j : Fin s.length) => val (s.get j) x
  TarskiExponentialFunctionProblem.RealSchanuelConjecture →
    ∃ precision : P × List P → ℕ, Computable precision ∧ ∀ p s (x : Fin s.length → ℝ),
      sys s x = 0 → IsUnit (fderiv ℝ (sys s) x) →
      val p x = 0 ∨ 1 / ((precision (p, s) : ℝ) + 1) ≤ |val p x|

theorem main : H1 → H2 → H3 → H4 → type_of% @TarskiExponentialFunctionProblem.isDecidable_completeTheory_realExp_of_realSchanuelConjecture := by
  intro hLogic hWitness hBoxes hGap hSC
  let P := List (ℤ × List (Bool × ℕ))
  let val := fun (p : P) {n : ℕ} (x : Fin n → ℝ) =>
    (p.map fun t => (t.1 : ℝ) * (t.2.map fun v =>
      let u := if h : v.2 < n then x ⟨v.2, h⟩ else 0
      if v.1 then Real.exp u else u).prod).sum
  let sys := fun (s : List P) (x : Fin s.length → ℝ) (j : Fin s.length) => val (s.get j) x
  have hval (p : P) (n : ℕ) : ContDiff ℝ 1 (fun x : Fin n → ℝ => val p x) := by
    let factor := fun (v : Bool × ℕ) (x : Fin n → ℝ) =>
      let u := if h : v.2 < n then x ⟨v.2, h⟩ else 0
      if v.1 then Real.exp u else u
    have hfac (v : Bool × ℕ) : ContDiff ℝ 1 (factor v) := by
      rcases v with ⟨b, i⟩
      by_cases hi : i < n <;> cases b <;> simp [factor, hi] <;> fun_prop
    have hprod (l : List (Bool × ℕ)) :
        ContDiff ℝ 1 (fun x => (l.map (fun v => factor v x)).prod) := by
      induction l with
      | nil => simpa using (contDiff_const (c := (1 : ℝ)) : ContDiff ℝ 1 (fun _ : Fin n → ℝ => (1 : ℝ)))
      | cons v l ih => simpa using (hfac v).mul ih
    induction p with
    | nil => simpa [val] using (contDiff_const (c := (0 : ℝ)) : ContDiff ℝ 1 (fun _ : Fin n → ℝ => (0 : ℝ)))
    | cons t p ih =>
      simpa [val, factor] using ((contDiff_const (c := (t.1 : ℝ))).mul (hprod t.2)).add ih
  have hsys (s : List P) : ContDiff ℝ 1 (sys s) := contDiff_pi.mpr fun j => hval (s.get j) _
  obtain ⟨check, hc, hcheck⟩ := hBoxes
  obtain ⟨precision, hp, hprec⟩ := hGap hSC
  let test := fun w : P × (List P × ℕ) =>
    check (((w.1, w.2.1), precision (w.1, w.2.1)), w.2.2)
  have hpair : Computable (fun w : P × (List P × ℕ) => (w.1, w.2.1)) :=
    Computable.fst.pair (Computable.fst.comp Computable.snd)
  apply hLogic
  refine ⟨test, hc.comp ((hpair.pair (hp.comp hpair)).pair (Computable.snd.comp Computable.snd)), ?_⟩
  intro p
  constructor
  · rintro ⟨⟨s, t⟩, ht⟩
    obtain ⟨a, b, r, _, hb, hball, hboundary⟩ := (hcheck p s _).mp ⟨t, ht⟩
    obtain ⟨x, hx, hzero, hunit⟩ := zero_of_boundary_gap (hsys s) hb hboundary
      (fun z hz => (hball z hz).2)
    refine ⟨s.length, x, (hprec p s x hzero hunit).resolve_right ?_⟩
    exact (hball x hx).1.not_ge
  · intro h
    obtain ⟨s, x, hx, hi, hpx⟩ := hWitness p h
    let k := precision (p, s)
    have hopen : {z : Fin s.length → ℝ | |val p z| < 1 / ((k : ℝ) + 1)} ∈ 𝓝 x := by
      apply (isOpen_lt (hval p _).continuous.abs continuous_const).mem_nhds
      change |val p x| < 1 / ((k : ℝ) + 1)
      change val p x = 0 at hpx
      rw [hpx, abs_zero]
      positivity
    obtain ⟨t, ht⟩ := (hcheck p s k).mpr (rational_box_at_zero (hsys s) hx hi hopen)
    exact ⟨(s, t), ht⟩

end OMA.R_TarskiExponentialFunctionProblem_isDecidable_completeTheory_realExp_of_realSchanuelConjecture_R2

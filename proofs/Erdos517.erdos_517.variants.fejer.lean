import FormalConjectures.ErdosProblems.«517»
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Asymptotic
import Mathlib.Analysis.Complex.Polynomial.GaussLucas
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic

/-!
# The Fejér-gap case of Erdős problem 517

Reflect exterior polynomial roots into the closed unit disk to prove Mahler's derivative
inequality. Padded reversal then gives a contraction that eliminates one coefficient.
Applying the contraction down a sparse polynomial yields a geometric-mean lower bound
for each positive exponent. Jensen's formula gives a conflicting upper bound for finite fibers.

Reference: M. Biernacki, Sur les équations algébriques contenant des paramètres arbitraires
(1928), chapter I, §3. The formal statement is from formal-conjectures 9097e2f90e66.
-/

open Filter Polynomial Real
open scoped BigOperators Polynomial ComplexConjugate

namespace Fejer517

noncomputable section

/-- Eliminate the coefficient in positive degree m. -/
def peel (m : ℕ) (P : Polynomial ℂ) : Polynomial ℂ :=
  P - C (m : ℂ)⁻¹ * (X * P.derivative)

theorem coeff_peel (m j : ℕ) (P : Polynomial ℂ) :
    (peel m P).coeff j = (1 - (j : ℂ) / m) * P.coeff j := by
  cases j with
  | zero => simp [peel]
  | succ j =>
    simp only [peel, coeff_sub, coeff_C_mul, coeff_X_mul,
      coeff_derivative, Nat.cast_add, Nat.cast_one, div_eq_mul_inv]
    ring

theorem coeff_peel_self {m : ℕ} (hm : 0 < m) (P : Polynomial ℂ) :
    (peel m P).coeff m = 0 := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  simp [coeff_peel, hm']

/-- A descending list contains every exponent above p which occurs in P.
    The contraction hypothesis, applied only in valid degrees, yields the
    sparse coefficient bound without assumptions on the lower coefficients. -/
theorem sparseCoefficient
    (contract : ∀ (m : ℕ) (Q : Polynomial ℂ), 0 < m → Q.natDegree ≤ m →
      (peel m Q).mahlerMeasure ≤ Q.mahlerMeasure)
    (p : ℕ) : ∀ (ds : List ℕ) (P : Polynomial ℂ),
      ds.Pairwise (fun i j => j < i) →
      (∀ m ∈ ds, p < m) →
      (∀ j, p < j → j ∉ ds → P.coeff j = 0) →
      ‖P.coeff p‖ * (ds.map (fun m : ℕ => 1 - (p : ℝ) / m)).prod ≤ P.mahlerMeasure := by
  intro ds
  induction ds with
  | nil =>
    intro P _ _ cover
    have hdeg : P.natDegree ≤ p :=
      natDegree_le_iff_coeff_eq_zero.mpr (fun j hj => cover j hj (by simp))
    simp only [List.map_nil, List.prod_nil, mul_one]
    rcases lt_or_eq_of_le hdeg with hlt | heq
    · simpa [coeff_eq_zero_of_natDegree_lt hlt] using P.mahlerMeasure_nonneg
    · simpa [← heq, coeff_natDegree] using P.leadingCoeff_le_mahlerMeasure
  | cons m ms ih =>
    intro P horder hgt cover
    obtain ⟨hmax, horder'⟩ := List.pairwise_cons.mp horder
    have hpm : p < m := hgt m (by simp)
    have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) hpm
    have hdeg : P.natDegree ≤ m := by
      apply natDegree_le_iff_coeff_eq_zero.mpr
      intro j hj
      apply cover j (hpm.trans hj)
      rw [List.mem_cons, not_or]
      exact ⟨hj.ne', fun h => (not_lt_of_ge hj.le) (hmax j h)⟩
    have tailCover : ∀ j, p < j → j ∉ ms → (peel m P).coeff j = 0 := by
      intro j hj hjms
      by_cases e : j = m
      · subst j
        exact coeff_peel_self hm P
      · rw [coeff_peel, cover j hj (by simpa only [List.mem_cons, not_or] using And.intro e hjms),
          mul_zero]
    have hr := ih (peel m P) horder'
      (fun j hj => hgt j (List.mem_cons_of_mem _ hj)) tailCover
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hpR : (p : ℝ) ≤ m := by exact_mod_cast hpm.le
    have hpos : 0 ≤ 1 - (p : ℝ) / m :=
      sub_nonneg.mpr ((div_le_one hmR).mpr hpR)
    have hcast : ((1 - (p : ℝ) / m : ℝ) : ℂ) = 1 - (p : ℂ) / m := by push_cast; rfl
    rw [coeff_peel, norm_mul, ← hcast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hpos] at hr
    simp only [List.map_cons, List.prod_cons]
    calc
      _ = ((1 - (p : ℝ) / m) * ‖P.coeff p‖) *
            (ms.map (fun j : ℕ => 1 - (p : ℝ) / j)).prod := by ring
      _ ≤ (peel m P).mahlerMeasure := hr
      _ ≤ P.mahlerMeasure := contract m P hm hdeg

/-- A uniform upper bound on the reciprocal of the coefficient-loss factor.
    The bound remains valid if the sequence starts with exponent zero. -/
theorem tailProductBound {n : ℕ → ℕ} (hn : HasFejerGaps n)
    (p : ℕ) (s : Finset ℕ) (hs : ∀ i ∈ s, p < n i) :
    (∏ i ∈ s, (n i : ℝ) / ((n i : ℝ) - p)) ≤
      Real.exp (((p : ℝ) * (p + 1)) * ∑' i, (n i : ℝ)⁻¹) := by
  let A : ℝ := (p : ℝ) * ((p : ℝ) + 1)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have factor : ∀ i ∈ s, (n i : ℝ) / ((n i : ℝ) - p) ≤
      1 + A * (n i : ℝ)⁻¹ := by
    intro i hi
    have hgap : (p : ℝ) + 1 ≤ n i := by exact_mod_cast Nat.succ_le_of_lt (hs i hi)
    have hd : 0 < (n i : ℝ) - p := by linarith
    have hN : 0 < (n i : ℝ) := by
      exact_mod_cast lt_of_le_of_lt (Nat.zero_le p) (hs i hi)
    have hfac : (n i : ℝ) ≤ ((p : ℝ) + 1) * ((n i : ℝ) - p) := by
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) p) (sub_nonneg.mpr hgap)]
    have hp : (p : ℝ) / ((n i : ℝ) - p) ≤ A / n i := by
      apply (div_le_div_iff₀ hd hN).mpr
      dsimp [A]
      nlinarith [mul_le_mul_of_nonneg_left hfac (Nat.cast_nonneg (α := ℝ) p)]
    have he : (n i : ℝ) / ((n i : ℝ) - p) = 1 + p / ((n i : ℝ) - p) := by
      field_simp [hd.ne']
      ring
    rw [he, ← div_eq_mul_inv]
    linarith
  calc
    _ ≤ ∏ i ∈ s, (1 + A * (n i : ℝ)⁻¹) := by
      apply Finset.prod_le_prod _ factor
      intro i hi
      have hi' : (p : ℝ) < n i := by exact_mod_cast hs i hi
      exact div_nonneg (by positivity) (sub_nonneg.mpr hi'.le)
    _ ≤ Real.exp (∑ i ∈ s, A * (n i : ℝ)⁻¹) :=
      Real.prod_one_add_le_exp_sum s (fun i => mul_nonneg hA (by positivity))
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hA
      exact hn.2.sum_le_tsum s (fun i _ => by positivity)

/-- Reflecting an exterior root preserves the boundary norm and increases
    the exterior norm. This identity also handles points on the unit circle. -/
theorem reflection_identity (a z : ℂ) :
    ‖1 - conj a * z‖ ^ 2 - ‖z - a‖ ^ 2 =
      (‖a‖ ^ 2 - 1) * (‖z‖ ^ 2 - 1) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  ring

theorem reflection_on_circle (a z : ℂ) (hz : ‖z‖ = 1) :
    ‖1 - conj a * z‖ = ‖z - a‖ := by
  have h := reflection_identity a z
  rw [hz] at h
  nlinarith [norm_nonneg (1 - conj a * z), norm_nonneg (z - a)]

theorem reflection_outside (a z : ℂ) (ha : 1 ≤ ‖a‖) (hz : 1 ≤ ‖z‖) :
    ‖z - a‖ ≤ ‖1 - conj a * z‖ := by
  have ha' : 0 ≤ ‖a‖ ^ 2 - 1 := by nlinarith [sq_nonneg (‖a‖ - 1)]
  have hz' : 0 ≤ ‖z‖ ^ 2 - 1 := by nlinarith [sq_nonneg (‖z‖ - 1)]
  apply le_of_sq_le_sq _ (norm_nonneg _)
  linarith [reflection_identity a z, mul_nonneg ha' hz']

/-- An exterior point cannot be a critical point if all roots are in the disk. -/
theorem exterior_derivative_ne {Q : Polynomial ℂ} (hdeg : 0 < Q.degree)
    (hroot : ∀ w : ℂ, 1 < ‖w‖ → Q.eval w ≠ 0) {z : ℂ} (hz : 1 < ‖z‖) :
    Q.derivative.eval z ≠ 0 := by
  intro heval
  have hball : Q.rootSet ℂ ⊆ Metric.closedBall (0 : ℂ) 1 := by
    intro w hw
    rw [mem_rootSet, coe_aeval_eq_eval] at hw
    change dist w 0 ≤ 1
    rw [dist_zero_right]
    exact le_of_not_gt (fun hout => hroot w hout hw.2)
  have hcrit : z ∈ Q.derivative.rootSet ℂ := by
    rw [mem_rootSet, coe_aeval_eq_eval]
    exact ⟨derivative_ne_zero.mpr (natDegree_pos_iff_degree_pos.mpr hdeg).ne', heval⟩
  have hmem := (convexHull_min hball (convex_closedBall (0 : ℂ) 1))
    (rootSet_derivative_subset_convexHull_rootSet hdeg hcrit)
  have : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hmem
  exact hz.not_ge this

/-- If an exterior-zero-free G dominates P outside the disk, its derivative
    dominates there too, provided no leading term cancels in the comparison
    family cG-P for |c| > 1. -/
theorem derivative_domination {P G : Polynomial ℂ} (hdeg : 0 < G.degree)
    (hG : ∀ w : ℂ, 1 < ‖w‖ → G.eval w ≠ 0)
    (hfamily : ∀ c : ℂ, 1 < ‖c‖ → 0 < (C c * G - P).degree)
    (hdom : ∀ w : ℂ, 1 < ‖w‖ → ‖P.eval w‖ ≤ ‖G.eval w‖)
    {z : ℂ} (hz : 1 < ‖z‖) : ‖P.derivative.eval z‖ ≤ ‖G.derivative.eval z‖ := by
  by_contra! hbad
  have hG' := exterior_derivative_ne hdeg hG hz
  let c : ℂ := P.derivative.eval z / G.derivative.eval z
  have hc : 1 < ‖c‖ := by
    dsimp [c]
    rw [norm_div, one_lt_div (norm_pos_iff.mpr hG')]
    exact hbad
  have hout : ∀ w : ℂ, 1 < ‖w‖ → (C c * G - P).eval w ≠ 0 := by
    intro w hw heq
    rw [eval_sub, eval_mul, eval_C, sub_eq_zero] at heq
    have hlt : ‖G.eval w‖ < ‖c * G.eval w‖ := by
      rw [norm_mul]
      simpa only [one_mul] using mul_lt_mul_of_pos_right hc (norm_pos_iff.mpr (hG w hw))
    rw [heq] at hlt
    exact (hdom w hw).not_gt hlt
  apply exterior_derivative_ne (hfamily c hc) hout hz
  rw [derivative_sub, derivative_C_mul, eval_sub, eval_mul, eval_C, sub_eq_zero]
  exact div_mul_cancel₀ _ hG'

/-- Pointwise domination on the unit circle passes to Mahler measure. -/
theorem mahler_mono_disk {P Q : ℂ[X]} (hQ : Q ≠ 0)
    (h : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ ‖Q.eval z‖) :
    P.mahlerMeasure ≤ Q.mahlerMeasure := by
  classical
  by_cases hP : P = 0
  · simpa [hP] using Q.mahlerMeasure_nonneg
  have hf : {z | P.eval z = 0}.Finite := by
    apply P.roots.toFinset.finite_toSet.subset
    intro z hz
    simpa [mem_roots hP, IsRoot] using hz
  let u := fun z : ℂ => Real.log ‖P.eval z‖
  let v := fun z : ℂ => Real.log ‖Q.eval z‖
  let t := fun z => min (u z) (v z)
  let S := Metric.sphere (0 : ℂ) |(1 : ℝ)|
  have hu : CircleIntegrable u 0 1 := P.intervalIntegrable_mahlerMeasure
  have hv : CircleIntegrable v 0 1 := Q.intervalIntegrable_mahlerMeasure
  have heq : u =ᶠ[codiscreteWithin S] t := by
    filter_upwards [compl_finite_mem_codiscreteWithin (s := S) hf, self_mem_codiscreteWithin S]
      with z hz hS
    have hn : P.eval z ≠ 0 := hz
    have hz1 : ‖z‖ = 1 := by simpa [S, Metric.mem_sphere] using hS
    exact (min_eq_left (Real.log_le_log (norm_pos_iff.mpr hn) (h z hz1))).symm
  have ht := (circleIntegrable_congr_codiscreteWithin heq).mp hu
  unfold Polynomial.mahlerMeasure
  simp only [hQ, hP, ne_eq, not_false_eq_true, if_true]
  apply Real.exp_le_exp.mpr
  change Real.circleAverage u 0 1 ≤ Real.circleAverage v 0 1
  rw [Real.circleAverage_congr_codiscreteWithin heq one_ne_zero]
  exact Real.circleAverage_mono ht hv (fun z _ => min_le_right _ _)

/-- The root-product formula collapses for polynomials with roots in the unit disk. -/
theorem mahler_eq_leading_of_roots_inside {P : ℂ[X]}
    (h : ∀ z : ℂ, 1 < ‖z‖ → P.eval z ≠ 0) :
    P.mahlerMeasure = ‖P.leadingCoeff‖ := by
  rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots]
  suffices (P.roots.map (fun a => max 1 ‖a‖)).prod = 1 by rw [this, mul_one]
  apply Multiset.prod_eq_one
  intro x hx
  obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hx
  apply max_eq_left
  exact le_of_not_gt (fun hout => h z hout (isRoot_of_mem_roots hz))

private structure DiskComparison (P G : ℂ[X]) : Prop where
  nonzero : P ≠ 0
  nonzeroG : G ≠ 0
  degree_eq : G.natDegree = P.natDegree
  zeroFree : ∀ z : ℂ, 1 < ‖z‖ → G.eval z ≠ 0
  dominates : ∀ z : ℂ, 1 < ‖z‖ → ‖P.eval z‖ ≤ ‖G.eval z‖
  boundary : ∀ z : ℂ, ‖z‖ = 1 → ‖G.eval z‖ = ‖P.eval z‖

private theorem DiskComparison.mul {P G Q H : ℂ[X]} (a : DiskComparison P G)
    (b : DiskComparison Q H) : DiskComparison (P * Q) (G * H) where
  nonzero := mul_ne_zero a.nonzero b.nonzero
  nonzeroG := mul_ne_zero a.nonzeroG b.nonzeroG
  degree_eq := by rw [natDegree_mul a.nonzeroG b.nonzeroG, natDegree_mul a.nonzero b.nonzero,
    a.degree_eq, b.degree_eq]
  zeroFree z hz := by simpa using mul_ne_zero (a.zeroFree z hz) (b.zeroFree z hz)
  dominates z hz := by
    simpa only [eval_mul, norm_mul] using
      mul_le_mul (a.dominates z hz) (b.dominates z hz) (norm_nonneg _) (norm_nonneg _)
  boundary z hz := by simp only [eval_mul, norm_mul, a.boundary z hz, b.boundary z hz]

private theorem compare_factor (a : ℂ) : ∃ G, DiskComparison (X - C a) G := by
  by_cases ha : ‖a‖ ≤ 1
  · refine ⟨_, X_sub_C_ne_zero a, X_sub_C_ne_zero a, rfl, ?_, fun _ _ => le_rfl,
      fun _ _ => rfl⟩
    intro z hz
    simpa [sub_ne_zero] using (fun h : z = a => hz.not_ge (h ▸ ha))
  have ha1 := lt_of_not_ge ha
  have hca : conj a ≠ 0 := by
    intro h
    have := congrArg norm h
    simp at this
    simp_all
  let G : ℂ[X] := C (-conj a) * (X - C (conj a)⁻¹)
  have hG : G ≠ 0 := mul_ne_zero (by simpa using hca) (X_sub_C_ne_zero _)
  have hev (z : ℂ) : G.eval z = 1 - conj a * z := by
    simp [G]
    field_simp
    ring
  refine ⟨G, X_sub_C_ne_zero _, hG, ?_, ?_, ?_, ?_⟩
  · exact (natDegree_C_mul (neg_ne_zero.mpr hca)).trans
      ((natDegree_X_sub_C _).trans (natDegree_X_sub_C a).symm)
  · intro z hz
    have hz' : z ≠ (conj a)⁻¹ := by
      intro he
      rw [he, norm_inv, Complex.norm_conj] at hz
      exact hz.not_ge (inv_le_one_of_one_le₀ ha1.le)
    simpa [G, hca, sub_ne_zero] using hz'
  · intro z hz
    simpa only [hev, eval_sub, eval_X, eval_C] using reflection_outside a z ha1.le hz.le
  · intro z hz
    simpa only [hev, eval_sub, eval_X, eval_C] using reflection_on_circle a z hz

private theorem disk_comparison {P : ℂ[X]} (hP : P ≠ 0) : ∃ G, DiskComparison P G := by
  classical
  have cons (c : ℂ) (hc : c ≠ 0) : DiskComparison (C c) (C c) :=
    ⟨by simpa, by simpa, rfl, fun z _ => by simpa, fun _ _ => le_rfl, fun _ _ => rfl⟩
  have factors (s : Multiset ℂ) : ∃ G, DiskComparison ((s.map (X - C ·)).prod) G := by
    induction s using Multiset.induction_on with
    | empty => simpa using (show ∃ G, DiskComparison (C (1 : ℂ)) G from ⟨_, cons 1 one_ne_zero⟩)
    | cons a s ih =>
      obtain ⟨G, hG⟩ := ih
      obtain ⟨H, hH⟩ := compare_factor a
      exact ⟨_, by simpa using hH.mul hG⟩
  obtain ⟨G, hG⟩ := factors P.roots
  have h := (cons P.leadingCoeff (leadingCoeff_ne_zero.mpr hP)).mul hG
  rw [← (IsAlgClosed.splits P).eq_prod_roots] at h
  exact ⟨_, h⟩

/-- The reversal has the same geometric mean on the unit circle. -/
theorem mahler_reflect (d : ℕ) (P : ℂ[X]) (hd : P.natDegree ≤ d) :
    (P.reflect d).mahlerMeasure = P.mahlerMeasure := by
  by_cases hP : P = 0
  · simp [hP, reflect_zero]
  have hH : P.reflect d ≠ 0 := mt reflect_eq_zero_iff.mp hP
  have hlog : (P.reflect d).logMahlerMeasure = P.logMahlerMeasure := by
    unfold Polynomial.logMahlerMeasure
    rw [← Real.circleAverage_zero_one_congr_inv (f := fun z => Real.log ‖(P.reflect d).eval z‖)]
    apply Real.circleAverage_congr_sphere
    intro z hz
    have hz1 : ‖z‖ = 1 := by simpa [Metric.mem_sphere] using hz
    have hz0 : z ≠ 0 := by intro e; simp [e] at hz1
    let := invertibleOfNonzero hz0
    have he := eval₂_reflect_mul_pow (RingHom.id ℂ) z d P hd
    have hn := congrArg norm he
    simp only [invOf_eq_inv, eval₂_id, norm_mul, norm_pow, hz1, one_pow, mul_one] at hn
    exact congrArg Real.log hn
  simp [Polynomial.mahlerMeasure, hP, hH, hlog]

/-- Differentiating the padded reversal gives the reflected elimination operator. -/
theorem reflected_peel {d : ℕ} (P : ℂ[X]) (hd : P.natDegree ≤ d + 1) :
    (P.reflect (d + 1)).derivative =
      C ((d + 1 : ℕ) : ℂ) * (peel (d + 1) P).reflect d := by
  ext j
  rw [coeff_derivative, coeff_C_mul, coeff_reflect, coeff_reflect, coeff_peel]
  by_cases hj : j ≤ d
  · rw [revAt_le hj, revAt_le (Nat.succ_le_succ hj), Nat.succ_sub_succ_eq_sub]
    have hcast : ((d - j : ℕ) : ℂ) = d - j := Nat.cast_sub hj
    simp only [Nat.cast_add, Nat.cast_one, hcast]
    have hne : ((d : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero d
    field_simp
    ring
  · have hj' : d < j := Nat.lt_of_not_ge hj
    rw [revAt_eq_self_of_lt hj', revAt_eq_self_of_lt (Nat.succ_lt_succ hj')]
    rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hd (by omega)), zero_mul]
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hj') with e | he
    · subst j
      have hne : ((d : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero d
      simp [hne]
    · simp [coeff_eq_zero_of_natDegree_lt (hd.trans_lt he)]

/-- Mahler's derivative inequality. -/
theorem mahler_derivative_le (P : ℂ[X]) :
    P.derivative.mahlerMeasure ≤ (P.natDegree : ℝ) * P.mahlerMeasure := by
  by_cases h0 : P.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero h0]
    simp
  have hP : P ≠ 0 := fun e => h0 (by simp [e])
  obtain ⟨G, hc⟩ := disk_comparison hP
  have hm : G.mahlerMeasure = P.mahlerMeasure :=
    le_antisymm (mahler_mono_disk hP (fun z hz => (hc.boundary z hz).le))
      (mahler_mono_disk hc.nonzeroG (fun z hz => (hc.boundary z hz).ge))
  have hlc : ‖P.leadingCoeff‖ ≤ ‖G.leadingCoeff‖ := by
    rw [← mahler_eq_leading_of_roots_inside hc.zeroFree, hm]
    exact P.leadingCoeff_le_mahlerMeasure
  have hgd : 0 < G.degree :=
    natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero (hc.degree_eq ▸ h0))
  have family (c : ℂ) (hh : 1 < ‖c‖) : 0 < (C c * G - P).degree := by
    apply natDegree_pos_iff_degree_pos.mp
    apply (Nat.pos_of_ne_zero h0).trans_le
    apply le_natDegree_of_ne_zero
    rw [coeff_sub, coeff_C_mul, ← hc.degree_eq, coeff_natDegree, hc.degree_eq, coeff_natDegree]
    intro eqn
    have bad := congrArg norm (sub_eq_zero.mp eqn)
    rw [norm_mul] at bad
    have hh' := mul_lt_mul_of_pos_right hh (norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hc.nonzeroG))
    rw [one_mul, bad] at hh'
    exact hlc.not_gt hh'
  have outside : (Metric.closedBall (0 : ℂ) 1)ᶜ ⊆
      {z | ‖P.derivative.eval z‖ ≤ ‖G.derivative.eval z‖} := by
    intro z hz
    apply derivative_domination hgd hc.zeroFree family hc.dominates
    simpa [Metric.mem_closedBall] using hz
  have hclosed := closure_minimal outside
    (isClosed_le P.derivative.continuous.norm G.derivative.continuous.norm)
  have hG' := derivative_ne_zero.mpr (natDegree_pos_iff_degree_pos.mpr hgd).ne'
  calc
    _ ≤ G.derivative.mahlerMeasure := mahler_mono_disk hG' (by
      intro z hz
      apply hclosed
      rw [closure_compl, interior_closedBall (0 : ℂ) one_ne_zero]
      simp [Metric.mem_ball, hz])
    _ = ‖G.leadingCoeff‖ * (G.natDegree : ℝ) := by
      rw [mahler_eq_leading_of_roots_inside (fun z hz => exterior_derivative_ne hgd hc.zeroFree hz),
        leadingCoeff_derivative, norm_mul, Complex.norm_natCast]
    _ = _ := by rw [← mahler_eq_leading_of_roots_inside hc.zeroFree, hm, hc.degree_eq, mul_comm]

/-- Eliminating the highest allowed exponent contracts Mahler measure. -/
theorem peel_contract (m : ℕ) (P : ℂ[X]) (hm : 0 < m) (hp : P.natDegree ≤ m) :
    (peel m P).mahlerMeasure ≤ P.mahlerMeasure := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have hdeg : (peel (d + 1) P).natDegree ≤ d := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hj) with he | he
    · subst j
      exact coeff_peel_self hm P
    · rw [coeff_peel, coeff_eq_zero_of_natDegree_lt (hp.trans_lt he), mul_zero]
  have hH : (P.reflect (d+1)).natDegree ≤ d+1 :=
    natDegree_reflect_le.trans (max_le (le_refl _) hp)
  have h := (mahler_derivative_le (P.reflect (d+1))).trans
    (mul_le_mul_of_nonneg_right (show ((P.reflect (d+1)).natDegree : ℝ) ≤ (d+1 : ℕ) by
      exact_mod_cast hH) (P.reflect (d+1)).mahlerMeasure_nonneg)
  rw [reflected_peel P hp, mahlerMeasure_mul, mahlerMeasure_const, Complex.norm_natCast,
    mahler_reflect d _ hdeg, mahler_reflect _ P hp] at h
  exact (mul_le_mul_iff_right₀ (show (0:ℝ) < (d+1:ℕ) by positivity)).mp h

/-- Partial sum evaluated on a rescaled circle. -/
def trunc (a : ℕ → ℂ) (n : ℕ → ℕ) (w : ℂ) (r : ℝ) (N : ℕ) : ℂ[X] :=
  (∑ i ∈ Finset.range N, monomial (n i) (a i * (r : ℂ) ^ n i)) - C w

theorem eval_trunc (a : ℕ → ℂ) (n : ℕ → ℕ) (w : ℂ) (r : ℝ) (N : ℕ) (z : ℂ) :
    (trunc a n w r N).eval z = (∑ i ∈ Finset.range N, a i * ((r : ℂ) * z) ^ n i) - w := by
  simp [trunc, eval_finsetSum, eval_monomial, mul_pow, mul_assoc]

private def loss (p : ℕ) (n : ℕ → ℕ) : ℝ :=
  Real.exp (((p : ℝ) * (p + 1)) * ∑' i, (n i : ℝ)⁻¹)

/-- Every truncation containing the selected positive exponent satisfies the same lower bound. -/
theorem trunc_lower {a : ℕ → ℂ} {n : ℕ → ℕ} (hn : HasFejerGaps n) (s N : ℕ)
    (hp : 0 < n s) (hN : s < N) (w : ℂ) (r : ℝ) (hr : 0 ≤ r) :
    ‖a s‖ / loss (n s) n * r ^ n s ≤ (trunc a n w r N).mahlerMeasure := by
  classical
  let I := Finset.Ioo s N
  let L := I.sort (· ≥ ·)
  let P := trunc a n w r N
  let F := fun i => 1 - (n s : ℝ) / n i
  have hi (i : ℕ) (hi : i ∈ I) : n s < n i := hn.1 (Finset.mem_Ioo.mp hi).1
  have hm (i : ℕ) : i ∈ L ↔ i ∈ I := Finset.mem_sort _
  have hgt : ∀ j ∈ L.map n, n s < j := by
    intro j hj
    obtain ⟨i, h, rfl⟩ := List.mem_map.mp hj
    exact hi i ((hm i).mp h)
  have horder : (L.map n).Pairwise (fun i j => j < i) := by
    rw [List.pairwise_map]
    exact (I.sortedGT_sort.pairwise).imp (fun h => hn.1 h)
  have hcov (j : ℕ) (hj : n s < j) (hmiss : j ∉ L.map n) : P.coeff j = 0 := by
    have hj0 := (hp.trans hj).ne'
    have hzero (i : ℕ) (hiN : i ∈ Finset.range N) : n i ≠ j := by
      intro e
      have hsi : s < i := hn.1.lt_iff_lt.mp (e.symm ▸ hj)
      exact hmiss (List.mem_map.mpr
        ⟨i, (hm i).mpr (Finset.mem_Ioo.mpr ⟨hsi, Finset.mem_range.mp hiN⟩), e⟩)
    simp only [P, trunc, coeff_sub, finsetSum_coeff, coeff_C, hj0, if_false, sub_zero]
    exact Finset.sum_eq_zero fun i hiN => by simp [coeff_monomial, hzero i hiN]
  have hcoeff : P.coeff (n s) = a s * (r : ℂ) ^ n s := by
    simp [P, trunc, finsetSum_coeff, coeff_monomial, hn.1.injective.eq_iff, coeff_C,
      hp.ne', Finset.mem_range.mpr hN]
  have hprod : ((L.map n).map (fun j : ℕ => 1 - (n s : ℝ) / j)).prod = ∏ i ∈ I, F i := by
    rw [List.map_map]
    exact ((I.sort_perm_toList (· ≥ ·)).map F).prod_eq.trans (I.prod_map_toList F)
  have hmain := sparseCoefficient peel_contract (n s) (L.map n) P horder hgt hcov
  rw [hcoeff, hprod, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr] at hmain
  have hF (i : ℕ) (h : i ∈ I) : 0 < F i := by
    have h' : (n s : ℝ) < n i := by exact_mod_cast hi i h
    have hN' : 0 < (n i : ℝ) := lt_of_le_of_lt (Nat.cast_nonneg _) h'
    exact sub_pos.mpr ((div_lt_one hN').mpr h')
  have hprodpos := Finset.prod_pos hF
  have hrec : (∏ i ∈ I, F i)⁻¹ ≤ loss (n s) n := by
    rw [← Finset.prod_inv_distrib]
    refine le_trans (le_of_eq (Finset.prod_congr rfl ?_)) (tailProductBound hn (n s) I hi)
    intro i hiI
    have hi0 : (n i : ℝ) ≠ 0 := by exact_mod_cast (hp.trans (hi i hiI)).ne'
    dsimp [F]
    rw [show 1 - (n s : ℝ) / n i = ((n i : ℝ) - n s) / n i by
      rw [sub_div, div_self hi0], inv_div]
  have hloss : 0 < loss (n s) n := Real.exp_pos _
  have hfac : 1 / loss (n s) n ≤ ∏ i ∈ I, F i := by
    apply (div_le_iff₀ hloss).mpr
    have hx := (inv_le_iff_one_le_mul₀ hprodpos).mp hrec
    simpa [mul_comm] using hx
  calc
    _ = (‖a s‖ * r ^ n s) * (1 / loss (n s) n) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hfac (mul_nonneg (norm_nonneg _) (pow_nonneg hr _))).trans hmain

theorem disk_majorant {a : ℕ → ℂ} {n : ℕ → ℕ} {f : ℂ → ℂ}
    (hf : ∀ z, HasSum (fun k => a k * z ^ n k) (f z)) (r : ℝ) (hr : 0 ≤ r) :
    Summable (fun k => ‖a k‖ * r ^ n k) := by
  have h := summable_norm_iff.mpr (hf (r : ℂ)).summable
  simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr] using h

theorem uniform_on_disk {a : ℕ → ℂ} {n : ℕ → ℕ} {f : ℂ → ℂ}
    (hf : ∀ z, HasSum (fun k => a k * z ^ n k) (f z)) (r : ℝ) (hr : 0 ≤ r) :
    TendstoUniformlyOn (fun N z => ∑ k ∈ Finset.range N, a k * z ^ n k)
      f atTop (Metric.closedBall 0 r) := by
  have hsum : (fun z : ℂ => ∑' k, a k * z ^ n k) = f :=
    funext fun z => (hf z).tsum_eq
  rw [← hsum]
  apply tendstoUniformlyOn_tsum_nat (disk_majorant hf r hr)
  intro k z hz
  have hz' : ‖z‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz' _) (norm_nonneg _)

theorem entire {a : ℕ → ℂ} {n : ℕ → ℕ} {f : ℂ → ℂ}
    (hf : ∀ z, HasSum (fun k => a k * z ^ n k) (f z)) : Differentiable ℂ f := by
  intro z
  let r := ‖z‖ + 1
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hmem : z ∈ Metric.ball (0 : ℂ) r := by
    simp [Metric.mem_ball, r]
  have hsum : (fun w : ℂ => ∑' k, a k * w ^ n k) = f :=
    funext fun w => (hf w).tsum_eq
  rw [← hsum]
  apply DifferentiableOn.differentiableAt _ (Metric.isOpen_ball.mem_nhds hmem)
  apply Complex.differentiableOn_tsum_of_summable_norm (disk_majorant hf r hr)
  · intro i
    fun_prop
  · exact Metric.isOpen_ball
  · intro k w hw
    have hw' : ‖w‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hw
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hw'.le _) (norm_nonneg _)

/-- The geometric mean of the modulus on a circle (used only beyond the zeros). -/
def circleMean (g : ℂ → ℂ) (r : ℝ) : ℝ :=
  Real.exp (circleAverage (fun z => Real.log ‖g z‖) 0 r)

/-- Jensen's formula gives polynomial growth of the geometric mean whenever the zero set
is finite, including functions that vanish at the center of the circles. -/
theorem finite_zeros_upper {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hfin : {z | g z = 0}.Finite) :
    ∃ (m : ℕ) (C : ℝ), ∀ᶠ r : ℝ in atTop, circleMean g r ≤ C * r ^ m := by
  let D := MeromorphicOn.divisor g Set.univ
  have ha : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
  have hs : D.support.Finite := by
    apply hfin.subset
    intro z hz
    by_contra hne
    change g z ≠ 0 at hne
    change D z ≠ 0 at hz
    apply hz
    change MeromorphicOn.divisor g Set.univ z = 0
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply ha (Set.mem_univ z), (hg.analyticAt z).analyticOrderAt_eq_zero.mpr hne]
    simp
  obtain ⟨K, hK⟩ := Asymptotics.isBigO_iff.mp
    (Function.locallyFinsuppWithin.logCounting_isBigO_log_of_finite_support hs)
  obtain ⟨m, hm⟩ := exists_nat_gt K
  let b := Real.log ‖meromorphicTrailingCoeffAt g 0‖
  refine ⟨m, Real.exp b, ?_⟩
  filter_upwards [hK, eventually_ge_atTop (1 : ℝ)] with r hNr hr
  have hpos := lt_of_lt_of_le zero_lt_one hr
  have hj := Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const
    (f := g) (fun z => (hg.analyticAt z).meromorphicAt) hpos.ne'
  change Function.locallyFinsuppWithin.logCounting D r =
    circleAverage (fun z => Real.log ‖g z‖) 0 r - b at hj
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hr)] at hNr
  have hbound := (le_abs_self _).trans (hNr.trans
    (mul_le_mul_of_nonneg_right hm.le (Real.log_nonneg hr)))
  unfold circleMean
  calc
    _ ≤ Real.exp (b + (m : ℝ) * Real.log r) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp b * r ^ m := by
      rw [Real.exp_add, ← Real.log_pow, Real.exp_log (pow_pos hpos _)]

/-- On a zero-free circle, sufficiently late truncations have geometric mean at most
twice that of the limit. A fixed factor suffices for the growth argument. -/
theorem trunc_upper_on_circle {a : ℕ → ℂ} {n : ℕ → ℕ} {f : ℂ → ℂ}
    (hf : ∀ z, HasSum (fun k => a k * z ^ n k) (f z))
    (w : ℂ) {r : ℝ} (hr : 0 < r) (hnz : ∀ z : ℂ, ‖z‖ = r → f z ≠ w) :
    ∀ᶠ N : ℕ in atTop,
      (trunc a n w r N).mahlerMeasure ≤ 2 * circleMean (fun z => f z - w) r := by
  let G := fun z : ℂ => f ((r : ℂ) * z) - w
  let S := Metric.sphere (0 : ℂ) 1
  have hc : Continuous G := ((entire hf).continuous.comp (continuous_const.mul continuous_id)).sub
    continuous_const
  have rnorm {z : ℂ} (hz : z ∈ S) : ‖(r : ℂ) * z‖ = r := by
    have : ‖z‖ = 1 := by simpa [S, Metric.mem_sphere] using hz
    simp [this, Real.norm_eq_abs, abs_of_pos hr]
  have hnzG (z : ℂ) (hz : z ∈ S) : G z ≠ 0 := sub_ne_zero.mpr (hnz _ (rnorm hz))
  have hne : S.Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_sphere (0 : ℂ) 1).exists_isMinOn hne hc.norm.continuousOn
  have hnear := Metric.tendstoUniformlyOn_iff.mp (uniform_on_disk hf r hr.le)
    ‖G z₀‖ (norm_pos_iff.mpr (hnzG z₀ hz₀))
  filter_upwards [hnear] with N hN
  let P := trunc a n w r N
  have hdist (z : ℂ) (hz : z ∈ S) : dist (G z) (P.eval z) < ‖G z‖ := by
    have hm : (r : ℂ) * z ∈ Metric.closedBall 0 r := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (rnorm hz).le
    simpa only [P, G, eval_trunc, dist_sub_right] using
      (hN _ hm).trans_le (isMinOn_iff.mp hmin z hz)
  have hpn (z : ℂ) (hz : z ∈ S) : P.eval z ≠ 0 := by
    intro eqn
    simpa [eqn] using hdist z hz
  have hP : P ≠ 0 := fun eqn => hpn z₀ hz₀ (by simp [eqn])
  have hint : CircleIntegrable (fun z => Real.log ‖G z‖) 0 1 :=
    ContinuousOn.circleIntegrable zero_le_one
      (hc.norm.continuousOn.log (fun z hz => (norm_ne_zero_iff.mpr (hnzG z hz))))
  have hm : P.logMahlerMeasure ≤ Real.log 2 +
      Real.circleAverage (fun z => Real.log ‖G z‖) 0 1 := by
    rw [← Real.circleAverage_const (Real.log 2) 0 1, ← Real.circleAverage_fun_add
      (circleIntegrable_const _ _ _) hint]
    apply Real.circleAverage_mono (show CircleIntegrable (fun z => Real.log ‖P.eval z‖) 0 1 from
      P.intervalIntegrable_mahlerMeasure)
      ((circleIntegrable_const _ _ _).add hint)
    intro z hz
    have hs : z ∈ S := by simpa [S] using hz
    have hh := norm_le_norm_add_const_of_dist_le (dist_comm (G z) (P.eval z) ▸ (hdist z hs).le)
    change Real.log ‖P.eval z‖ ≤ Real.log 2 + Real.log ‖G z‖
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (norm_ne_zero_iff.mpr (hnzG z hs))]
    apply Real.log_le_log (norm_pos_iff.mpr (hpn z hs))
    linarith
  have hchange : Real.circleAverage (fun z => Real.log ‖G z‖) 0 1 =
      Real.circleAverage (fun z => Real.log ‖f z - w‖) 0 r := by
    rw [Real.circleAverage_eq_circleAverage_zero_one (f := fun z => Real.log ‖f z - w‖)
      (c := 0) (R := r)]
    simp [G]
  change P.mahlerMeasure ≤ _
  rw [Polynomial.mahlerMeasure, if_pos hP]
  convert Real.exp_le_exp.mpr hm using 1
  rw [Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 2), hchange]
  rfl

/-- Once the two circle-mean estimates have been established, a finite fiber
    is impossible. The high exponent is selected using only strict increase. -/
theorem infinite_of_circle_growth {S : Set ℂ} {n : ℕ → ℕ} (hn : StrictMono n)
    (M : ℝ → ℝ)
    (lower : ∀ k, 0 < n k → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ r : ℝ in atTop, c * r ^ n k ≤ M r)
    (upper : S.Finite → ∃ (m : ℕ) (C : ℝ), ∀ᶠ r : ℝ in atTop, M r ≤ C * r ^ m) :
    S.Infinite := by
  intro hs
  obtain ⟨m, C, hupper⟩ := upper hs
  have hbig : m < n (m + 1) := lt_of_lt_of_le (Nat.lt_succ_self m) (hn.id_le (m + 1))
  obtain ⟨c, hc, hlower⟩ := lower (m + 1) (lt_of_le_of_lt (Nat.zero_le m) hbig)
  have he : n (m + 1) = m + (n (m + 1) - (m + 1)) + 1 := by omega
  have impossible : ∀ᶠ r : ℝ in atTop, False := by
    filter_upwards [hupper, hlower, eventually_ge_atTop (1 : ℝ), eventually_gt_atTop (C / c)]
      with r hU hL hr hrC
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
    have hCr : C < r * c := (div_lt_iff₀ hc).mp hrC
    have hpow : (1 : ℝ) ≤ r ^ (n (m + 1) - (m + 1)) := one_le_pow₀ hr
    have hlarge : C * r ^ m < c * r ^ n (m + 1) := by
      calc
        C * r ^ m < (r * c) * r ^ m := mul_lt_mul_of_pos_right hCr (pow_pos hrpos _)
        _ ≤ ((r * c) * r ^ m) * r ^ (n (m + 1) - (m + 1)) := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hpow (mul_nonneg (mul_nonneg hrpos.le hc.le) (pow_nonneg hrpos.le m))
        _ = c * r ^ n (m + 1) := by
          conv_rhs => rw [he, pow_succ, pow_add]
          ring
    exact (hL.trans hU).not_gt hlarge
  exact impossible.exists.elim (fun _ h => h)

/-- Fejér's gap condition forces every fiber of the entire function to be infinite. -/
theorem fejer {f : ℂ → ℂ} {n : ℕ → ℕ} (hn : HasFejerGaps n) {a : ℕ → ℂ}
    (ha : ∀ k, a k ≠ 0) (hf : ∀ z, HasSum (fun k => a k * z ^ n k) (f z)) (w : ℂ) :
    {x : ℂ | f x = w}.Infinite := by
  by_contra hfin
  change ¬ ¬ Set.Finite {x : ℂ | f x = w} at hfin
  have hS := Classical.not_not.mp hfin
  obtain ⟨R, hR⟩ := hS.isBounded.exists_norm_le
  let g := fun z : ℂ => f z - w
  have hg : Differentiable ℂ g := (entire hf).sub (differentiable_const w)
  have hZ : {z | g z = 0}.Finite := by simpa [g, sub_eq_zero] using hS
  apply (infinite_of_circle_growth (S := {x : ℂ | f x = w}) hn.1 (circleMean g) ?_
    (fun _ => finite_zeros_upper hg hZ)) hS
  intro s hp
  let c := ‖a s‖ / loss (n s) n
  have hc : 0 < c := div_pos (norm_pos_iff.mpr (ha s)) (Real.exp_pos _)
  refine ⟨c / 2, by positivity, ?_⟩
  filter_upwards [eventually_gt_atTop (max R 0)] with r hr
  have hr0 := (le_max_right R 0).trans_lt hr
  have hgood (z : ℂ) (hz : ‖z‖ = r) : f z ≠ w :=
    fun eqn => (le_max_left R 0).trans_lt hr |>.not_ge (hz ▸ hR z eqn)
  obtain ⟨N, hhigh, hupper⟩ :=
    ((eventually_gt_atTop s).and (trunc_upper_on_circle hf w hr0 hgood)).exists
  have hlow := trunc_lower (a := a) hn s N hp hhigh w r hr0.le
  change c * r ^ n s ≤ _ at hlow
  change _ ≤ 2 * circleMean g r at hupper
  linarith [hlow.trans hupper]

end
end Fejer517

theorem OMA.solution : type_of% @Erdos517.erdos_517.variants.fejer :=
  @Fejer517.fejer

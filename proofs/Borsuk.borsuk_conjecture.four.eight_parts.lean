import FormalConjectures.Wikipedia.BorsukConjecture
import Mathlib.Analysis.Matrix.Order
import Mathlib

/-! # Eight smaller parts in four dimensions

Complete proof of the 4-dimensional 8-part Borsuk bound: every bounded nontrivial subset
of Euclidean 4-space can be covered by 8 sets of strictly smaller diameter.

Credits and attributions:
- The three-regime decomposition (small, middle, large circumradius) and small/large-radius
  assembly follow @Deldor14 (reduction R1).
- The high-circumradius regime (R > 627/1000) adapts Logan R. Chalmers,
  Lean formalisation of the four-dimensional six-part theorem (2026),
  https://doi.org/10.5281/zenodo.23966881, distributed under CC BY 4.0
  (https://creativecommons.org/licenses/by/4.0/), as adapted to Lean 4.33 by @Deldor14 (R1.H2).
- The middle-circumradius regime (4/7 < R <= 627/1000) is proved algebraically using two obtuse
  contact points p_0, p_1 (<p_0, p_1> <= -R^2 / 4), a polar cap along p_0, two circular cones
  aligned with p_1, five algebraic pentagonal sectors (zero trigonometry), and exact rational
  Bernstein polynomial certificates.
-/


noncomputable section
namespace BorsukSix.Support
theorem inner_eq_sum {ι : Type*} [Fintype ι]
    (n x : EuclideanSpace ℝ ι) : inner ℝ n x = ∑ i, n i * x i := by
  simp [PiLp.inner_apply, mul_comm]

theorem norm_smul_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : ℝ) (x : E) : ‖D • x‖ ^ 2 = D ^ 2 * ‖x‖ ^ 2 := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]


end BorsukSix.Support

section









namespace BorsukSix.CompactNormalization
open scoped Pointwise

abbrev E4 := EuclideanSpace ℝ (Fin 4)

/-- Closing a bounded positive-diameter set and dividing by its diameter gives
an actual compact diameter-one set, with no finiteness assumption on the input. -/
theorem compact_diameter_one_normalization {S : Set E4}
    (hS : Bornology.IsBounded S) (hD : 0 < Metric.diam S) :
    IsCompact ((Metric.diam S)⁻¹ • closure S) ∧
      Metric.diam ((Metric.diam S)⁻¹ • closure S) = 1 := by
  constructor
  · exact (Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨isClosed_closure, hS.closure⟩).image (continuous_const_smul ((Metric.diam S)⁻¹))
  · rw [diam_smul₀, Metric.diam_closure, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hD), inv_mul_cancel₀ hD.ne']

/-- The maximum distance from a proposed enclosing-ball center. Its supremum is
shown below to be attained whenever the point set is nonempty and compact. -/
noncomputable def radiusAt {E : Type*} [PseudoMetricSpace E] (K : Set E) (c : E) : ℝ :=
  sSup ((fun x => dist x c) '' K)

theorem radiusAt_attained {E : Type*} [PseudoMetricSpace E] {K : Set E}
    (hK : IsCompact K) (hne : K.Nonempty) (c : E) :
    ∃ x ∈ K, radiusAt K c = dist x c ∧ ∀ y ∈ K, dist y c ≤ radiusAt K c := by
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne
    (continuous_id.dist continuous_const).continuousOn
  have hg : IsGreatest ((fun y => dist y c) '' K) (dist x c) := by
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmax hy
  have hr : radiusAt K c = dist x c := hg.csSup_eq
  exact ⟨x, hx, hr, fun y hy => hr ▸ hmax hy⟩

theorem dist_le_radiusAt {E : Type*} [PseudoMetricSpace E] {K : Set E}
    (hK : IsCompact K) (hne : K.Nonempty) {x : E} (hx : x ∈ K) (c : E) :
    dist x c ≤ radiusAt K c := (radiusAt_attained hK hne c).choose_spec.2.2 x hx

theorem radiusAt_nonneg {E : Type*} [PseudoMetricSpace E] {K : Set E}
    (hK : IsCompact K) (hne : K.Nonempty) (c : E) : 0 ≤ radiusAt K c := by
  obtain ⟨x, hx⟩ := hne
  exact dist_nonneg.trans (dist_le_radiusAt hK ⟨x, hx⟩ hx c)

theorem radiusAt_lipschitz {E : Type*} [PseudoMetricSpace E] {K : Set E}
    (hK : IsCompact K) (hne : K.Nonempty) : LipschitzWith 1 (radiusAt K) := by
  apply LipschitzWith.of_le_add
  intro c d
  obtain ⟨x, hx, hr, _⟩ := radiusAt_attained hK hne c
  rw [hr]
  exact (dist_triangle_right x c d).trans
    (add_le_add (dist_le_radiusAt hK hne hx d) le_rfl)

/-- Every nonempty compact set in a proper metric space admits a minimum-radius
enclosing ball. The proof minimizes a proved-continuous maximum-distance function
on a compact ball; centers outside that ball cannot improve the result. -/
theorem exists_minimum_center {E : Type*} [MetricSpace E] [ProperSpace E]
    {K : Set E} (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ c : E, ∀ d : E, radiusAt K c ≤ radiusAt K d := by
  obtain ⟨p, hp⟩ := hne
  have hpball : p ∈ Metric.closedBall p (radiusAt K p) := by
    simpa using radiusAt_nonneg hK ⟨p, hp⟩ p
  obtain ⟨c, hc, hmin⟩ := (isCompact_closedBall p (radiusAt K p)).exists_isMinOn
    ⟨p, hpball⟩ (radiusAt_lipschitz hK ⟨p, hp⟩).continuous.continuousOn
  refine ⟨c, fun d => ?_⟩
  by_cases hd : d ∈ Metric.closedBall p (radiusAt K p)
  · exact hmin hd
  · have hout : radiusAt K p < dist p d := by
      simpa only [Metric.mem_closedBall, not_le, dist_comm] using hd
    exact (hmin hpball).trans (hout.le.trans (dist_le_radiusAt hK ⟨p, hp⟩ hp d))

/-- Translation preserves the exact maximum-distance radius after translating
the proposed center by the same amount. -/
theorem radiusAt_translate (K : Set E4) (c d : E4) :
    radiusAt ((fun x => x - c) '' K) d = radiusAt K (d + c) := by
  unfold radiusAt
  congr 1
  rw [Set.image_image]
  congr 1
  funext x
  simp only [Function.comp_apply, dist_eq_norm]
  congr 1
  abel

theorem subtract_isometry (c : E4) : Isometry (fun x : E4 => x - c) := by
  apply Isometry.of_dist_eq
  intro x y
  simp only [dist_eq_norm]
  congr 1
  abel

/-- A compact diameter-one set may be translated so that zero is a minimum
enclosing-ball center. This retains its diameter and all its points. -/
theorem compact_centered_diameter_one {K : Set E4}
    (hK : IsCompact K) (hdiam : Metric.diam K = 1) :
    ∃ c : E4, IsCompact ((fun x => x - c) '' K) ∧
      Metric.diam ((fun x => x - c) '' K) = 1 ∧
      ∀ d : E4, radiusAt ((fun x => x - c) '' K) 0 ≤
        radiusAt ((fun x => x - c) '' K) d := by
  have hne : K.Nonempty := by
    by_contra h
    have he : K = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    simp [he] at hdiam
  obtain ⟨c, hc⟩ := exists_minimum_center hK hne
  refine ⟨c, hK.image (subtract_isometry c).continuous,
    (subtract_isometry c).diam_image K |>.trans hdiam, ?_⟩
  intro d
  rw [radiusAt_translate, radiusAt_translate, zero_add]
  exact hc (d + c)

/-- Complete closure/scaling/translation normalization, before the contact-simplex
and geometric selection arguments. The original set need not be closed or finite. -/
theorem exists_compact_centered_normalization {S : Set E4}
    (hS : Bornology.IsBounded S) (hD : 0 < Metric.diam S) :
    ∃ c : E4, let K := (fun x => x - c) '' ((Metric.diam S)⁻¹ • closure S)
      IsCompact K ∧ Metric.diam K = 1 ∧
        ∀ d : E4, radiusAt K 0 ≤ radiusAt K d := by
  obtain ⟨hcompact, hdiam⟩ := compact_diameter_one_normalization hS hD
  exact compact_centered_diameter_one hcompact hdiam


end BorsukSix.CompactNormalization

end

section










namespace BorsukSix.ContactSimplex
open scoped BigOperators
open CompactNormalization

/-- Convex combinations of exactly `n` (not necessarily distinct) points. -/
def combinations (n : ℕ) (K : Set E4) : Set E4 :=
  (fun wz : (Fin n → ℝ) × (Fin n → E4) => ∑ i, wz.1 i • wz.2 i) ''
    (stdSimplex ℝ (Fin n) ×ˢ {z : Fin n → E4 | ∀ i, z i ∈ K})

theorem combinations_isCompact (n : ℕ) {K : Set E4} (hK : IsCompact K) :
    IsCompact (combinations n K) := by
  apply ((isCompact_stdSimplex ℝ (Fin n)).prod
    (isCompact_pi_infinite (fun _ => hK))).image
  fun_prop

theorem combinations_subset_hull (n : ℕ) (K : Set E4) :
    combinations n K ⊆ convexHull ℝ K := by
  rintro _ ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
  exact (convex_convexHull ℝ K).sum_mem (fun i _ => hw.1 i) hw.2
    (fun i _ => subset_convexHull ℝ K (hz i))

theorem affineIndependent_card_le_five {ι : Type} [Fintype ι] {z : ι → E4}
    (hz : AffineIndependent ℝ z) : Fintype.card ι ≤ 5 := by
  have h := hz.card_le_finrank_succ
  have hdim := Submodule.finrank_le (vectorSpan ℝ (Set.range z))
  have he : Module.finrank ℝ E4 = 4 := finrank_euclideanSpace_fin
  omega

/-- Finite-dimensional Carathéodory with explicit uniform arity: at most five
points suffice in Euclidean four-space. This includes empty input sets. -/
theorem convexHull_eq_five_combinations (K : Set E4) :
    convexHull ℝ K = ⋃ n : Fin 6, combinations n.val K := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨ι, hι, z, w, hzK, hz, hwpos, hwsum, hwz⟩ :=
      eq_pos_convex_span_of_mem_convexHull hx
    letI := hι
    let n : Fin 6 := ⟨Fintype.card ι, by have := affineIndependent_card_le_five hz; omega⟩
    let e : Fin n.val ≃ ι := (Fintype.equivFin ι).symm
    apply Set.mem_iUnion.mpr
    refine ⟨n, ⟨(w ∘ e, z ∘ e), ⟨?_, ?_⟩, ?_⟩⟩
    · exact ⟨fun i => (hwpos (e i)).le, (e.sum_comp w).trans hwsum⟩
    · intro i
      exact hzK ⟨e i, rfl⟩
    · exact (e.sum_comp (fun i => w i • z i)).trans hwz
  · apply Set.iUnion_subset
    intro n
    exact combinations_subset_hull n.val K

/-- Compactness of the convex hull of an arbitrary compact subset of E4.
This is not restricted to finite contact sets. -/
theorem convexHull_isCompact {K : Set E4} (hK : IsCompact K) :
    IsCompact (convexHull ℝ K) := by
  rw [convexHull_eq_five_combinations]
  exact isCompact_iUnion (fun n => combinations_isCompact n.val hK)

/-- Active contacts of the enclosing ball centered at zero. -/
def contacts (K : Set E4) : Set E4 :=
  {x | x ∈ K ∧ ‖x‖ = radiusAt K 0}

theorem contacts_isCompact {K : Set E4} (hK : IsCompact K) :
    IsCompact (contacts K) :=
  hK.inter_right (isClosed_eq continuous_norm continuous_const)

theorem contacts_nonempty {K : Set E4} (hK : IsCompact K) (hne : K.Nonempty) :
    (contacts K).Nonempty := by
  obtain ⟨x, hx, hr, _⟩ := radiusAt_attained hK hne 0
  exact ⟨x, hx, by simpa using hr.symm⟩

/-- If one direction has a uniformly positive inner product with all active
contacts, shifting the center slightly in that direction strictly reduces radius.
Compactness controls inactive points; no finiteness of the contact set is assumed. -/
theorem exists_improved_center_of_contact_direction {K : Set E4}
    (hK : IsCompact K) (hne : K.Nonempty) (v : E4) (a : ℝ) (ha : 0 < a)
    (hcontact : ∀ x ∈ contacts K, a < inner ℝ v x) :
    ∃ c : E4, radiusAt K c < radiusAt K 0 := by
  let R := radiusAt K 0
  have hnorm (x : E4) (hx : x ∈ K) : ‖x‖ ≤ R := by
    simpa [R] using dist_le_radiusAt hK hne hx 0
  have hR : 0 < R := by
    by_contra hn
    have hrzero : R = 0 := le_antisymm (le_of_not_gt hn) (radiusAt_nonneg hK hne 0)
    obtain ⟨x, hx⟩ := contacts_nonempty hK hne
    have hxzero : x = 0 := norm_eq_zero.mp (hx.2.trans hrzero)
    have := hcontact x hx
    simp only [hxzero, inner_zero_right] at this
    linarith
  let B : Set E4 := {x | x ∈ K ∧ inner ℝ v x ≤ a / 2}
  have hB : IsCompact B := by
    change IsCompact (K ∩ {x : E4 | inner ℝ v x ≤ a / 2})
    exact hK.inter_right (isClosed_le
      (show Continuous (fun x : E4 => inner ℝ v x) by fun_prop) continuous_const)
  have hbad : ∃ r : ℝ, 0 ≤ r ∧ r < R ∧
      ∀ x ∈ K, inner ℝ v x ≤ a / 2 → ‖x‖ ≤ r := by
    rcases B.eq_empty_or_nonempty with he | hneB
    · refine ⟨0, le_rfl, hR, ?_⟩
      intro x hx hv
      have : x ∈ B := ⟨hx, hv⟩
      simpa [he] using this
    · obtain ⟨z, hz, hmax⟩ := hB.exists_isMaxOn hneB continuous_norm.continuousOn
      have hlt : ‖z‖ < R := by
        apply lt_of_le_of_ne (hnorm z hz.1)
        intro he
        have hc := hcontact z ⟨hz.1, he⟩
        linarith [hz.2]
      exact ⟨‖z‖, norm_nonneg _, hlt, fun x hx hv => hmax ⟨hx, hv⟩⟩
  obtain ⟨r, hr0, hrR, hbad⟩ := hbad
  have hdena : 0 < ‖v‖ ^ 2 + 1 := by positivity
  have hdenb : 0 < ‖v‖ + 1 := by positivity
  obtain ⟨t, ht, htmin⟩ := exists_between (lt_min
    (div_pos ha hdena) (div_pos (sub_pos.mpr hrR) hdenb))
  have hta : t * (‖v‖ ^ 2 + 1) < a := (lt_div_iff₀ hdena).mp (lt_min_iff.mp htmin).1
  have htb : t * (‖v‖ + 1) < R - r := (lt_div_iff₀ hdenb).mp (lt_min_iff.mp htmin).2
  have himprove : ∀ x ∈ K, dist x (t • v) < R := by
    intro x hx
    rw [dist_eq_norm]
    by_cases hb : inner ℝ v x ≤ a / 2
    · calc
        ‖x - t • v‖ ≤ ‖x‖ + ‖t • v‖ := norm_sub_le _ _
        _ ≤ r + t * ‖v‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
          exact add_le_add (hbad x hx hb) le_rfl
        _ < R := by nlinarith
    · have hxn : ‖x‖ ^ 2 ≤ R ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) hR.le).mpr (hnorm x hx)
      have hdir : t * (t * ‖v‖ ^ 2) < t * (2 * inner ℝ v x) := by
        apply mul_lt_mul_of_pos_left _ ht
        nlinarith
      have hs : ‖x - t • v‖ ^ 2 < R ^ 2 := by
        rw [norm_sub_sq_real, real_inner_smul_right, ← real_inner_comm x v,
          norm_smul, Real.norm_eq_abs, abs_of_pos ht]
        nlinarith
      nlinarith [norm_nonneg (x - t • v)]
  obtain ⟨x, hx, he, _⟩ := radiusAt_attained hK hne (t • v)
  exact ⟨t • v, he ▸ himprove x hx⟩

/-- The minimum enclosing-ball optimality condition for an arbitrary nonempty
compact E4 set: the origin lies in the convex hull of its active contact points. -/
theorem zero_mem_convexHull_contacts {K : Set E4} (hK : IsCompact K)
    (hne : K.Nonempty) (hmin : ∀ c : E4, radiusAt K 0 ≤ radiusAt K c) :
    (0 : E4) ∈ convexHull ℝ (contacts K) := by
  by_contra hout
  obtain ⟨f, a, ha, hsep⟩ := geometric_hahn_banach_point_closed
    (convex_convexHull ℝ (contacts K))
    (convexHull_isCompact (contacts_isCompact hK)).isClosed hout
  have ha0 : 0 < a := by simpa using ha
  let v := (InnerProductSpace.toDual ℝ E4).symm f
  have hdir : ∀ x ∈ contacts K, a < inner ℝ v x := by
    intro x hx
    simpa [v] using hsep x (subset_convexHull ℝ (contacts K) hx)
  obtain ⟨c, hc⟩ := exists_improved_center_of_contact_direction hK hne v a ha0 hdir
  exact (not_lt_of_ge (hmin c)) hc

/-- A minimum enclosing ball in E4 has a positive, affinely independent contact
simplex with at most five vertices whose weighted barycenter is its center. -/
theorem exists_positive_contact_simplex {K : Set E4} (hK : IsCompact K)
    (hne : K.Nonempty) (hmin : ∀ c : E4, radiusAt K 0 ≤ radiusAt K c) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ 5 ∧ ∃ (p : Fin n → E4) (w : Fin n → ℝ),
      (∀ i, p i ∈ K ∧ ‖p i‖ = radiusAt K 0) ∧ AffineIndependent ℝ p ∧
      (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧ (∑ i, w i • p i) = 0 := by
  obtain ⟨ι, hι, z, w, hzK, hz, hwpos, hwsum, hwz⟩ :=
    eq_pos_convex_span_of_mem_convexHull (zero_mem_convexHull_contacts hK hne hmin)
  letI := hι
  have hn : 1 ≤ Fintype.card ι := by
    by_contra h
    have he : Fintype.card ι = 0 := by omega
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp he
    simp at hwsum
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, hn, affineIndependent_card_le_five hz,
    z ∘ e, w ∘ e, ?_, hz.comp_embedding e.toEmbedding, ?_, ?_, ?_⟩
  · intro i
    exact hzK ⟨e i, rfl⟩
  · intro i
    exact hwpos (e i)
  · exact (e.sum_comp w).trans hwsum
  · exact (e.sum_comp (fun i => w i • z i)).trans hwz

/-- The contact barycenter identity in Euclidean space. -/
theorem contact_weighted_distance_identity {n : ℕ} (p : Fin n → E4) (w : Fin n → ℝ)
    (R : ℝ) (hnorm : ∀ i, ‖p i‖ = R) (hw : ∑ i, w i = 1)
    (hbary : ∑ i, w i • p i = 0) (c : E4) :
    (∑ i, w i * ‖p i - c‖ ^ 2) = R ^ 2 + ‖c‖ ^ 2 := by
  have hi : (∑ i, w i * inner ℝ (p i) c) = 0 := by
    simp only [← real_inner_smul_left, ← sum_inner, hbary, inner_zero_left]
  calc
    (∑ i, w i * ‖p i - c‖ ^ 2) =
      (∑ i, w i * R ^ 2) - 2 * (∑ i, w i * inner ℝ (p i) c) +
        (∑ i, w i * ‖c‖ ^ 2) := by
      simp only [norm_sub_sq_real, hnorm, mul_add, mul_sub,
        Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
      congr 2
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul, hw, hi]; ring

/-- The exact weighted pair-variance identity for a contact simplex. -/
theorem contact_pair_variance {n : ℕ} (p : Fin n → E4) (w : Fin n → ℝ)
    (R : ℝ) (hnorm : ∀ i, ‖p i‖ = R) (hw : ∑ i, w i = 1)
    (hbary : ∑ i, w i • p i = 0) :
    (∑ i, ∑ j, w i * w j * dist (p i) (p j) ^ 2) = 2 * R ^ 2 := by
  have hrow (i : Fin n) : (∑ j, w j * dist (p i) (p j) ^ 2) = 2 * R ^ 2 := by
    simp_rw [dist_comm (p i), dist_eq_norm]
    rw [contact_weighted_distance_identity p w R hnorm hw hbary, hnorm i]
    ring
  calc
    (∑ i, ∑ j, w i * w j * dist (p i) (p j) ^ 2) =
        ∑ i, w i * (∑ j, w j * dist (p i) (p j) ^ 2) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ i, w i * (2 * R ^ 2) := by simp_rw [hrow]
    _ = 2 * R ^ 2 := by rw [← Finset.sum_mul, hw, one_mul]

/-- Diameter one, diagonal zero, and positive contact weights give the sharp
finite-contact upper estimate before Cauchy--Schwarz is applied. -/
theorem contact_radius_sq_le_weight_bound {n : ℕ}
    (p : Fin n → E4) (w : Fin n → ℝ) (R : ℝ)
    (hnorm : ∀ i, ‖p i‖ = R) (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1)
    (hbary : ∑ i, w i • p i = 0) (hd : ∀ i j, dist (p i) (p j) ≤ 1) :
    2 * R ^ 2 ≤ 1 - ∑ i, w i ^ 2 := by
  have hrow (i : Fin n) : (∑ j, w j * dist (p i) (p j) ^ 2) ≤ 1 - w i := by
    calc
      (∑ j, w j * dist (p i) (p j) ^ 2) ≤
          ∑ j, (w j - if j = i then w i else 0) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hji : j = i
        · simp [hji]
        · simp only [hji, ↓reduceIte, sub_zero]
          have hs : dist (p i) (p j) ^ 2 ≤ 1 := by
            nlinarith [hd i j, dist_nonneg (x := p i) (y := p j)]
          simpa using mul_le_mul_of_nonneg_left hs (hw0 j)
      _ = 1 - w i := by simp [Finset.sum_sub_distrib, hw]
  rw [← contact_pair_variance p w R hnorm hw hbary]
  calc
    (∑ i, ∑ j, w i * w j * dist (p i) (p j) ^ 2) =
        ∑ i, w i * (∑ j, w j * dist (p i) (p j) ^ 2) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ ≤ ∑ i, w i * (1 - w i) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hrow i) (hw0 i))
    _ = 1 - ∑ i, w i ^ 2 := by simp [mul_sub, Finset.sum_sub_distrib, hw, pow_two]

/-- Jung's finite-contact bound: `R² ≤ (n−1)/(2n)`, with real subtraction.
The ambient dimension only enters later through the at-most-five contact bound. -/
theorem contact_jung_bound {n : ℕ} (hn : 0 < n)
    (p : Fin n → E4) (w : Fin n → ℝ) (R : ℝ)
    (hnorm : ∀ i, ‖p i‖ = R) (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1)
    (hbary : ∑ i, w i • p i = 0) (hd : ∀ i j, dist (p i) (p j) ≤ 1) :
    R ^ 2 ≤ ((n : ℝ) - 1) / (2 * (n : ℝ)) := by
  have hweight := contact_radius_sq_le_weight_bound p w R hnorm hw0 hw hbary hd
  have hcs : 1 ≤ (n : ℝ) * ∑ i, w i ^ 2 := by
    simpa [hw] using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := w))
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  apply (le_div_iff₀ (mul_pos (by norm_num) hnreal)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hweight hnreal.le]

theorem contact_radius_sq_le_two_fifths {n : ℕ} (hn : 0 < n) (hn5 : n ≤ 5)
    (p : Fin n → E4) (w : Fin n → ℝ) (R : ℝ)
    (hnorm : ∀ i, ‖p i‖ = R) (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1)
    (hbary : ∑ i, w i • p i = 0) (hd : ∀ i j, dist (p i) (p j) ≤ 1) :
    R ^ 2 ≤ 2 / 5 := by
  apply (contact_jung_bound hn p w R hnorm hw0 hw hbary hd).trans
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hn5real : (n : ℝ) ≤ 5 := by exact_mod_cast hn5
  apply (div_le_iff₀ (mul_pos (by norm_num) hnreal)).mpr
  nlinarith

theorem contact_radius_sq_le_quarter_of_at_most_two {n : ℕ}
    (hn : 0 < n) (hn2 : n ≤ 2)
    (p : Fin n → E4) (w : Fin n → ℝ) (R : ℝ)
    (hnorm : ∀ i, ‖p i‖ = R) (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1)
    (hbary : ∑ i, w i • p i = 0) (hd : ∀ i j, dist (p i) (p j) ≤ 1) :
    R ^ 2 ≤ 1 / 4 := by
  apply (contact_jung_bound hn p w R hnorm hw0 hw hbary hd).trans
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hn2real : (n : ℝ) ≤ 2 := by exact_mod_cast hn2
  apply (div_le_iff₀ (mul_pos (by norm_num) hnreal)).mpr
  nlinarith

/-- Jung's `R² ≤ 2/5` bound for arbitrary compact diameter-at-most-one subsets
of real Euclidean four-space, derived from minimum-ball contacts. -/
theorem minimum_center_jung_bound {K : Set E4} (hK : IsCompact K)
    (hne : K.Nonempty) (hdiam : Metric.diam K ≤ 1)
    (hmin : ∀ c : E4, radiusAt K 0 ≤ radiusAt K c) :
    radiusAt K 0 ^ 2 ≤ 2 / 5 := by
  obtain ⟨n, hn, hn5, p, w, hp, _, hwpos, hw, hbary⟩ :=
    exists_positive_contact_simplex hK hne hmin
  apply contact_radius_sq_le_two_fifths hn hn5 p w _
    (fun i => (hp i).2) (fun i => (hwpos i).le) hw hbary
  intro i j
  exact (Metric.dist_le_diam_of_mem hK.isBounded (hp i).1 (hp j).1).trans hdiam

/-- In the middle/high radius regime, one or two contact points are impossible;
the positive affinely independent selector simplex has three, four, or five points. -/
theorem exists_three_to_five_contact_simplex {K : Set E4} (hK : IsCompact K)
    (hne : K.Nonempty) (hdiam : Metric.diam K ≤ 1)
    (hmin : ∀ c : E4, radiusAt K 0 ≤ radiusAt K c)
    (hR : 1 / 4 < radiusAt K 0 ^ 2) :
    ∃ n : ℕ, 3 ≤ n ∧ n ≤ 5 ∧ ∃ (p : Fin n → E4) (w : Fin n → ℝ),
      (∀ i, p i ∈ K ∧ ‖p i‖ = radiusAt K 0) ∧ AffineIndependent ℝ p ∧
      (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧ (∑ i, w i • p i) = 0 := by
  obtain ⟨n, hn, hn5, p, w, hp, haff, hwpos, hw, hbary⟩ :=
    exists_positive_contact_simplex hK hne hmin
  have hn3 : 3 ≤ n := by
    by_contra hn3
    have hn2 : n ≤ 2 := by omega
    have hq := contact_radius_sq_le_quarter_of_at_most_two hn hn2 p w _
      (fun i => (hp i).2) (fun i => (hwpos i).le) hw hbary (fun i j =>
        (Metric.dist_le_diam_of_mem hK.isBounded (hp i).1 (hp j).1).trans hdiam)
    exact (not_lt_of_ge hq) hR
  exact ⟨n, hn3, hn5, p, w, hp, haff, hwpos, hw, hbary⟩









end BorsukSix.ContactSimplex

end

section




/- Exact scalar contradiction for the high-radius residual argument. Geometry
must supply both covariance bounds; this file alone is not the high-tail theorem. -/

namespace BorsukSix.HighRadiusTailScalar

def alpha : ℝ := 2 / 5
def rho : ℝ := 9999 / 20000
def sigma : ℝ := rho ^ 2
def U (r : ℝ) : ℝ := 1 / 2 - r
def kappa (r : ℝ) : ℝ := (2 - 5 * r) / 2
def eta (r : ℝ) : ℝ := (3 * r - 1) / 2
def A (r : ℝ) : ℝ := alpha ^ 2 * r - sigma
def V (Q D r : ℝ) : ℝ :=
  ((1 - r) * (Q + 2 * A r) - (Q ^ 2 + D ^ 2) / 2 - A r * Q) / (4 * alpha)
def G0 (Q r : ℝ) : ℝ := U r * Q - kappa r - V Q 0 r
def B (r : ℝ) : ℝ := -22 * r / 25 - 179980001 / 200000000
def C (r : ℝ) : ℝ := 16 * r ^ 2 / 25 + 636019999 * r / 100000000 - 220019999 / 100000000
def delta (r : ℝ) : ℝ := 279 * r ^ 2 / 625 + 29821219939 * r / 5000000000 -
  384424799159960001 / 160000000000000000

lemma G0_identity (Q r : ℝ) : 8 * alpha * G0 Q r = Q ^ 2 + B r * Q + C r := by
  unfold G0 U kappa V A sigma rho B C alpha
  ring
lemma delta_identity (r : ℝ) : delta r = C r - (B r) ^ 2 / 4 := by
  unfold delta B C
  ring
lemma delta_endpoint : delta (1957 / 5000) = 21741731067199 / 160000000000000000 := by
  norm_num [delta]
lemma delta_pos {r : ℝ} (hr : 1957 / 5000 ≤ r) : 0 < delta r := by
  have hr0 : 0 ≤ r := by linarith
  have hrsq : (1957 / 5000 : ℝ) ^ 2 ≤ r ^ 2 := by nlinarith
  have hd : delta (1957 / 5000) ≤ delta r := by unfold delta; nlinarith
  rw [delta_endpoint] at hd
  linarith
lemma G0_pos (Q : ℝ) {r : ℝ} (hr : 1957 / 5000 ≤ r) : 0 < G0 Q r := by
  have hd := delta_pos hr
  rw [delta_identity] at hd
  have hg := G0_identity Q r
  unfold alpha at hg
  nlinarith [sq_nonneg (Q + B r / 2)]

lemma sqrt_tangent (a D : ℝ) (ha : 0 < a) :
    Real.sqrt (a ^ 2 + D ^ 2) ≤ a + D ^ 2 / (2 * a) := by
  have ht : 0 ≤ D ^ 2 / (2 * a) := by positivity
  have hid : 2 * a * (D ^ 2 / (2 * a)) = D ^ 2 := by field_simp
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · nlinarith [sq_nonneg (D ^ 2 / (2 * a))]

/-- A real number cannot obey both geometric covariance estimates on the actual
high-tail radius interval. The imbalance D may be arbitrary. -/
theorem covariance_bounds_incompatible (r Q D P : ℝ)
    (hrlo : 1957 / 5000 ≤ r) (hrhi : r ≤ 2 / 5) (hQ : Q ≤ 2 * r)
    (hupper : P ≤ V Q D r)
    (hlower : eta r * Q - kappa r * Real.sqrt (D ^ 2 + (1 - Q) ^ 2) ≤ P) : False := by
  have ha : 0 < 1 - Q := by linarith
  have hk : 0 ≤ kappa r := by unfold kappa; linarith
  have hcoef : 4 * alpha * kappa r ≤ 1 - Q := by
    unfold alpha kappa
    nlinarith
  have hroot := sqrt_tangent (1 - Q) D ha
  rw [add_comm ((1-Q)^2)] at hroot
  have hmul := mul_le_mul_of_nonneg_left hroot hk
  have hsmall : eta r * Q - kappa r * ((1 - Q) + D ^ 2 / (2 * (1 - Q))) ≤ P := by linarith
  have hpos := G0_pos Q hrlo
  have hden : 0 < 2 * (1 - Q) := by linarith
  have hid :
      2 * (1 - Q) *
        (eta r * Q - kappa r * ((1 - Q) + D ^ 2 / (2 * (1 - Q))) - V Q D r) =
      2 * (1 - Q) * G0 Q r +
        D ^ 2 * ((1 - Q) / (4 * alpha) - kappa r) := by
    unfold eta G0 U V
    field_simp
    unfold alpha kappa
    ring
  have hcoef' : 0 ≤ (1 - Q) / (4 * alpha) - kappa r := by
    unfold alpha at *
    norm_num at hcoef ⊢
    linarith
  have hrest := mul_nonneg (sq_nonneg D) hcoef'
  have hstrict := mul_pos hden hpos
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos hden.le (show
      eta r * Q - kappa r * ((1 - Q) + D ^ 2 / (2 * (1 - Q))) - V Q D r ≤ 0 by linarith)
  linarith


end BorsukSix.HighRadiusTailScalar

end

section





/- Joint two-point covariance estimate. The spectral bound is derived from a
real Gram identity and positive-semidefinite trace duality; no eigenvalue
ordering assumption is supplied by a certificate. -/

namespace BorsukSix.HighRadiusTailSpectral
open scoped BigOperators MatrixOrder
open Matrix
abbrev E4 := EuclideanSpace ℝ (Fin 4)

def gramTop (q t s : ℝ) : ℝ := (q + t + Real.sqrt ((q - t) ^ 2 + 4 * s ^ 2)) / 2

lemma gram_quadratic_bound (q t s a b : ℝ) :
    q * a ^ 2 + 2 * s * a * b + t * b ^ 2 ≤ gramTop q t s * (a ^ 2 + b ^ 2) := by
  let R := Real.sqrt ((q - t) ^ 2 + 4 * s ^ 2)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = (q - t) ^ 2 + 4 * s ^ 2 := Real.sq_sqrt (by positivity)
  have hid : (R * (a ^ 2 + b ^ 2)) ^ 2 -
      ((q - t) * (a ^ 2 - b ^ 2) + 4 * s * a * b) ^ 2 =
      (2 * s * (a ^ 2 - b ^ 2) - 2 * (q - t) * a * b) ^ 2 := by
    rw [mul_pow, hR2]
    ring
  have hleft : (q - t) * (a ^ 2 - b ^ 2) + 4 * s * a * b ≤ R * (a ^ 2 + b ^ 2) := by
    have hnn : 0 ≤ R * (a ^ 2 + b ^ 2) := by positivity
    nlinarith only [hid, hnn, sq_nonneg (2 * s * (a ^ 2 - b ^ 2) - 2 * (q - t) * a * b)]
  change q * a ^ 2 + 2 * s * a * b + t * b ^ 2 ≤ ((q+t+R)/2)*(a^2+b^2)
  nlinarith only [hleft]

lemma gram_pair_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y z : E) :
    (inner ℝ x z) ^ 2 + (inner ℝ y z) ^ 2 ≤
      gramTop (‖x‖ ^ 2) (‖y‖ ^ 2) (inner ℝ x y) * ‖z‖ ^ 2 := by
  let a := inner ℝ x z
  let b := inner ℝ y z
  let w := a • x + b • y
  have hi : inner ℝ w z = a ^ 2 + b ^ 2 := by
    simp [w, a, b, inner_add_left, inner_smul_left, pow_two]
  have hn : ‖w‖ ^ 2 = ‖x‖ ^ 2 * a ^ 2 + 2 * inner ℝ x y * a * b + ‖y‖ ^ 2 * b ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    change inner ℝ (a • x + b • y) (a • x + b • y) = _
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      conj_trivial, real_inner_self_eq_norm_sq, real_inner_comm y x]
    ring
  have hcs := real_inner_mul_inner_self_le w z
  rw [hi, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hn] at hcs
  have hg := gram_quadratic_bound (‖x‖ ^ 2) (‖y‖ ^ 2) (inner ℝ x y) a b
  have hmul := mul_le_mul_of_nonneg_right hg (sq_nonneg ‖z‖)
  have htop : 0 ≤ gramTop (‖x‖ ^ 2) (‖y‖ ^ 2) (inner ℝ x y) := by unfold gramTop; positivity
  have hprod : 0 ≤ gramTop (‖x‖ ^ 2) (‖y‖ ^ 2) (inner ℝ x y) * ‖z‖ ^ 2 := by positivity
  change a^2+b^2 ≤ _
  nlinarith only [hcs, hmul, hprod, sq_nonneg a, sq_nonneg b]

lemma trace_mul_nonneg {N T : Matrix (Fin 4) (Fin 4) ℝ}
    (hN : N.PosSemidef) (hT : T.PosSemidef) : 0 ≤ (N * T).trace := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hN.nonneg
  have h := (hT.mul_mul_conjTranspose_same B).trace_nonneg
  rw [trace_mul_cycle] at h
  simpa only [star_eq_conjTranspose] using h

/-- Coordinate covariance quadratic form, using the Euclidean L2 coordinates. -/
def quad (N : Matrix (Fin 4) (Fin 4) ℝ) (x : E4) : ℝ := x.ofLp ⬝ᵥ (N *ᵥ x.ofLp)
def pairMatrix (x y : E4) : Matrix (Fin 4) (Fin 4) ℝ :=
  vecMulVec x.ofLp x.ofLp + vecMulVec y.ofLp y.ofLp

lemma quad_pairMatrix (x y z : E4) : quad (pairMatrix x y) z =
    (inner ℝ x z) ^ 2 + (inner ℝ y z) ^ 2 := by
  simp [quad, pairMatrix, Matrix.mulVec, dotProduct, vecMulVec, Fin.sum_univ_succ, Support.inner_eq_sum]
  ring

lemma quad_identity (x : E4) : quad (1 : Matrix (Fin 4) (Fin 4) ℝ) x = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [quad, dotProduct, pow_two]

lemma pairMatrix_upper (x y : E4) :
    (gramTop (‖x‖ ^ 2) (‖y‖ ^ 2) (inner ℝ x y) • (1 : Matrix (Fin 4) (Fin 4) ℝ) -
      pairMatrix x y).PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · apply IsHermitian.sub
    · exact IsHermitian.smul isHermitian_one (IsSelfAdjoint.all _)
    · apply IsHermitian.add <;> apply isHermitian_iff_isSymm.mpr <;> ext i j <;>
        simp [vecMulVec, transpose_apply, mul_comm]
  · intro z
    have h := gram_pair_bound x y (WithLp.toLp 2 z)
    rw [← quad_pairMatrix, ← quad_identity (WithLp.toLp 2 z)] at h
    simpa [quad, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul] using sub_nonneg.mpr h

lemma trace_mul_pairMatrix (N : Matrix (Fin 4) (Fin 4) ℝ) (x y : E4) :
    (N * pairMatrix x y).trace = quad N x + quad N y := by
  simp [pairMatrix, Matrix.mul_add, trace_add, mul_vecMulVec, trace_vecMulVec, quad, dotProduct_comm]

/-- Positive trace duality bounds the covariance defect on a pair jointly. -/
theorem joint_quad_bound (N : Matrix (Fin 4) (Fin 4) ℝ) (hN : N.PosSemidef) (x y : E4) :
    quad N x + quad N y ≤ N.trace * gramTop (‖x‖ ^ 2) (‖y‖ ^ 2) (inner ℝ x y) := by
  have h := trace_mul_nonneg hN (pairMatrix_upper x y)
  rw [Matrix.mul_sub, trace_sub, Matrix.mul_smul, Matrix.mul_one, trace_smul,
    trace_mul_pairMatrix] at h
  simpa only [smul_eq_mul, mul_comm, sub_nonneg] using h


end BorsukSix.HighRadiusTailSpectral

end

section




/- Covariance inequalities derived from physical contact data. -/

namespace BorsukSix.HighRadiusTailCovariance
open scoped BigOperators MatrixOrder
open BorsukSix.HighRadiusTailSpectral BorsukSix.HighRadiusTailScalar
open Matrix

lemma sum_mul_separated {ι : Type*} [Fintype ι] (f g : ι → ℝ) :
    (∑ i, ∑ j, f i * g j) = (∑ i, f i) * ∑ j, g j := by
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]

lemma scalar_covariance_identity {ι : Type*} [Fintype ι]
    (w a : ι → ℝ) (t : ι → ι → ℝ) (C : ℝ)
    (hw : ∑ i, w i = 1) (ha : ∑ i, w i * a i = 0)
    (ht : ∀ i j, t i j = t j i) (hrow : ∀ i, ∑ j, w j * t i j = 0) :
    (∑ i, ∑ j, w i * w j * (C + 2 * t i j) * (a i - a j) ^ 2) =
      2 * C * (∑ i, w i * a i ^ 2) -
      4 * ∑ i, ∑ j, (w i * a i) * (w j * a j) * t i j := by
  have hrow' : (∑ i, ∑ j, (w i * a i ^ 2) * (w j * t i j)) = 0 := by
    simp_rw [← Finset.mul_sum, hrow, mul_zero, Finset.sum_const_zero]
  have hcol' : (∑ i, ∑ j, (w j * a j ^ 2) * (w i * t i j)) = 0 := by
    rw [Finset.sum_comm]
    simpa only [ht] using hrow'
  calc
    _ = ∑ i, ∑ j,
      (C * ((w i * a i ^ 2) * w j) + C * (w i * (w j * a j ^ 2)) -
        (2 * C) * ((w i * a i) * (w j * a j)) +
        2 * ((w i * a i ^ 2) * (w j * t i j)) +
        2 * ((w j * a j ^ 2) * (w i * t i j)) -
        4 * ((w i * a i) * (w j * a j) * t i j)) := by
      apply Finset.sum_congr rfl; intro i hi
      apply Finset.sum_congr rfl; intro j hj
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [hcol']
      simp only [hw, ha, hrow, mul_one, mul_zero, Finset.sum_const_zero, ← Finset.sum_mul]
      ring

def Phi (w : Fin 5 → ℝ) (p : Fin 5 → E4) (v : E4) : ℝ :=
  ∑ i, w i * (inner ℝ v (p i)) ^ 2

def covVec (w : Fin 5 → ℝ) (p : Fin 5 → E4) (v : E4) : E4 :=
  ∑ i, (w i * inner ℝ v (p i)) • p i

def covariance (w : Fin 5 → ℝ) (p : Fin 5 → E4) : Matrix (Fin 4) (Fin 4) ℝ :=
  ∑ i, w i • vecMulVec (p i).ofLp (p i).ofLp

lemma weighted_inner_zero (w : Fin 5 → ℝ) (p : Fin 5 → E4)
    (hp : ∑ i, w i • p i = 0) (v : E4) : ∑ i, w i * inner ℝ v (p i) = 0 := by
  have h := congrArg (inner ℝ v) hp
  simpa only [inner_sum, inner_smul_right, inner_zero_right] using h

lemma inner_covVec (w : Fin 5 → ℝ) (p : Fin 5 → E4) (v : E4) :
    inner ℝ v (covVec w p v) = Phi w p v := by
  simp only [covVec, Phi, inner_sum, inner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma covVec_norm_sq (w : Fin 5 → ℝ) (p : Fin 5 → E4) (v : E4) :
    ‖covVec w p v‖ ^ 2 =
      ∑ i, ∑ j, (w i * inner ℝ v (p i)) * (w j * inner ℝ v (p j)) * inner ℝ (p i) (p j) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [covVec, sum_inner, inner_sum, inner_smul_left, inner_smul_right, conj_trivial]
  apply Finset.sum_congr rfl; intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j hj
  rw [real_inner_comm (p j) (p i)]
  ring

lemma contact_covariance_identity (w : Fin 5 → ℝ) (p : Fin 5 → E4) (r : ℝ)
    (hw : ∑ i, w i = 1) (hp : ∑ i, w i • p i = 0)
    (hr : ∀ i, ‖p i‖ ^ 2 = r) (v : E4) :
    (∑ i, ∑ j, w i * w j * (1 - dist (p i) (p j) ^ 2) *
      (inner ℝ v (p i) - inner ℝ v (p j)) ^ 2) =
      4 * U r * Phi w p v - 4 * ‖covVec w p v‖ ^ 2 := by
  have hdist (i j : Fin 5) : 1 - dist (p i) (p j) ^ 2 = 1 - 2*r + 2*inner ℝ (p i) (p j) := by
    rw [dist_eq_norm, norm_sub_sq_real, hr i, hr j]
    ring
  simp_rw [hdist]
  rw [scalar_covariance_identity w (fun i => inner ℝ v (p i))
    (fun i j => inner ℝ (p i) (p j)) (1-2*r) hw (weighted_inner_zero w p hp v)
    (fun i j => real_inner_comm _ _) (fun i => weighted_inner_zero w p hp (p i))]
  rw [← covVec_norm_sq]
  unfold Phi U
  ring

/-- The upper covariance inequality follows solely from diameter-one contacts,
common radius, normalized nonnegative weights, and their zero barycenter. -/
theorem Phi_le_U_norm_sq (w : Fin 5 → ℝ) (p : Fin 5 → E4) (r : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1) (hp : ∑ i, w i • p i = 0)
    (hr : ∀ i, ‖p i‖ ^ 2 = r) (hrhi : r ≤ 1 / 2)
    (hdiam : ∀ i j, dist (p i) (p j) ≤ 1) (v : E4) :
    Phi w p v ≤ U r * ‖v‖ ^ 2 := by
  have hsum : 0 ≤ ∑ i, ∑ j, w i * w j * (1 - dist (p i) (p j) ^ 2) *
      (inner ℝ v (p i) - inner ℝ v (p j)) ^ 2 := by
    apply Finset.sum_nonneg; intro i hi
    apply Finset.sum_nonneg; intro j hj
    have hd : 0 ≤ 1 - dist (p i) (p j) ^ 2 := by nlinarith [hdiam i j, dist_nonneg (x:=p i) (y:=p j)]
    exact mul_nonneg (mul_nonneg (mul_nonneg (hw0 i) (hw0 j)) hd) (sq_nonneg _)
  rw [contact_covariance_identity w p r hw hp hr v] at hsum
  have hPhi0 : 0 ≤ Phi w p v := Finset.sum_nonneg fun i _ => mul_nonneg (hw0 i) (sq_nonneg _)
  have hcs := real_inner_mul_inner_self_le v (covVec w p v)
  rw [inner_covVec, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hcs
  have hmul := mul_le_mul_of_nonneg_left (show ‖covVec w p v‖ ^ 2 ≤ U r * Phi w p v by linarith) (sq_nonneg ‖v‖)
  by_cases hzero : Phi w p v = 0
  · rw [hzero]
    exact mul_nonneg (by unfold U; linarith) (sq_nonneg _)
  · have hpos : 0 < Phi w p v := lt_of_le_of_ne hPhi0 (Ne.symm hzero)
    apply (mul_le_mul_iff_left₀ hpos).mp
    calc
      _ ≤ ‖v‖ ^ 2 * (U r * Phi w p v) := hcs.trans hmul
      _ = _ := by ring

lemma quad_add (M N : Matrix (Fin 4) (Fin 4) ℝ) (x : E4) :
    quad (M+N) x = quad M x + quad N x := by simp [quad, add_mulVec, dotProduct_add]
lemma quad_sub (M N : Matrix (Fin 4) (Fin 4) ℝ) (x : E4) :
    quad (M-N) x = quad M x - quad N x := by simp [quad, sub_mulVec, dotProduct_sub]
lemma quad_smul (a : ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) (x : E4) :
    quad (a • M) x = a * quad M x := by simp [quad, smul_mulVec, dotProduct_smul]
lemma quad_rank_one (p x : E4) :
    quad (vecMulVec p.ofLp p.ofLp) x = (inner ℝ x p) ^ 2 := by
  simp [quad, Matrix.mulVec, dotProduct, vecMulVec, Fin.sum_univ_succ, Support.inner_eq_sum]
  ring

lemma quad_covariance (w : Fin 5 → ℝ) (p : Fin 5 → E4) (x : E4) :
    quad (covariance w p) x = Phi w p x := by
  simp [covariance, Phi, Fin.sum_univ_succ, quad_add, quad_smul, quad_rank_one]

lemma covariance_isHermitian (w : Fin 5 → ℝ) (p : Fin 5 → E4) :
    (covariance w p).IsHermitian := by
  apply isHermitian_iff_isSymm.mpr
  ext k l
  simp only [covariance, transpose_apply, Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma trace_covariance (w : Fin 5 → ℝ) (p : Fin 5 → E4) (r : ℝ)
    (hw : ∑ i, w i = 1) (hr : ∀ i, ‖p i‖ ^ 2 = r) : (covariance w p).trace = r := by
  have hnorm (i : Fin 5) : (p i).ofLp ⬝ᵥ (p i).ofLp = r := by
    rw [← hr i, EuclideanSpace.real_norm_sq_eq]
    simp only [dotProduct, pow_two]
  simp only [covariance, trace_sum, trace_smul, trace_vecMulVec, hnorm, smul_eq_mul,
    ← Finset.sum_mul, hw, one_mul]

def defect (w : Fin 5 → ℝ) (p : Fin 5 → E4) (r : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  U r • 1 - covariance w p

lemma quad_defect (w : Fin 5 → ℝ) (p : Fin 5 → E4) (r : ℝ) (x : E4) :
    quad (defect w p r) x = U r * ‖x‖ ^ 2 - Phi w p x := by
  rw [defect, quad_sub, quad_smul, quad_identity, quad_covariance]

lemma defect_posSemidef (w : Fin 5 → ℝ) (p : Fin 5 → E4) (r : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1) (hp : ∑ i, w i • p i = 0)
    (hr : ∀ i, ‖p i‖ ^ 2 = r) (hrhi : r ≤ 1 / 2)
    (hdiam : ∀ i j, dist (p i) (p j) ≤ 1) : (defect w p r).PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (isHermitian_one.smul (IsSelfAdjoint.all _)).sub (covariance_isHermitian w p)
  · intro v
    have h := Phi_le_U_norm_sq w p r hw0 hw hp hr hrhi hdiam (WithLp.toLp 2 v)
    have hnonneg := sub_nonneg.mpr h
    rw [← quad_defect] at hnonneg
    simpa [quad] using hnonneg

lemma trace_defect (w : Fin 5 → ℝ) (p : Fin 5 → E4) (r : ℝ)
    (hw : ∑ i, w i = 1) (hr : ∀ i, ‖p i‖ ^ 2 = r) : (defect w p r).trace = 2-5*r := by
  rw [defect, trace_sub, trace_smul, trace_one, trace_covariance w p r hw hr]
  norm_num [U]
  ring

/-- Lower covariance estimate for an actual unit-distance pair, proved jointly
rather than by a separate minimum-eigenvalue estimate for each point. -/
theorem pair_lower_covariance (w : Fin 5 → ℝ) (p : Fin 5 → E4) (r : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1) (hp : ∑ i, w i • p i = 0)
    (hr : ∀ i, ‖p i‖ ^ 2 = r) (hrhi : r ≤ 1 / 2)
    (hdiam : ∀ i j, dist (p i) (p j) ≤ 1) (x y : E4) (hxy : dist x y = 1) :
    eta r * (‖x‖ ^ 2 + ‖y‖ ^ 2) - kappa r *
      Real.sqrt ((‖x‖ ^ 2 - ‖y‖ ^ 2) ^ 2 + (1 - (‖x‖ ^ 2 + ‖y‖ ^ 2)) ^ 2) ≤
      Phi w p x + Phi w p y := by
  have h := joint_quad_bound (defect w p r)
    (defect_posSemidef w p r hw0 hw hp hr hrhi hdiam) x y
  rw [quad_defect, quad_defect, trace_defect w p r hw hr] at h
  have hi : inner ℝ x y = (‖x‖ ^ 2 + ‖y‖ ^ 2 - 1) / 2 := by
    have hdist : ‖x-y‖ ^ 2 = 1 := by rw [← dist_eq_norm, hxy]; norm_num
    rw [norm_sub_sq_real] at hdist
    linarith
  have hg : gramTop (‖x‖ ^ 2) (‖y‖ ^ 2) (inner ℝ x y) =
      ((‖x‖ ^ 2 + ‖y‖ ^ 2) + Real.sqrt ((‖x‖ ^ 2 - ‖y‖ ^ 2) ^ 2 +
        (1 - (‖x‖ ^ 2 + ‖y‖ ^ 2)) ^ 2)) / 2 := by
    rw [gramTop, hi]
    congr 3
    ring
  rw [hg] at h
  unfold eta kappa U at *
  nlinarith only [h]



end BorsukSix.HighRadiusTailCovariance

end

section




namespace BorsukSix.HighRadiusTailMissed
open scoped BigOperators
open BorsukSix.HighRadiusTailSpectral BorsukSix.HighRadiusTailScalar
open BorsukSix.HighRadiusTailCovariance

lemma weighted_variance_le (w a : Fin 5 → ℝ) (l u : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1) (ha : ∑ i, w i * a i = 0)
    (hl : ∀ i, l ≤ a i) (hu : ∀ i, a i ≤ u) :
    (∑ i, w i * a i ^ 2) ≤ -l*u := by
  have hnonneg : 0 ≤ ∑ i, w i * (a i-l) * (u-a i) := by
    apply Finset.sum_nonneg; intro i hi
    exact mul_nonneg (mul_nonneg (hw0 i) (sub_nonneg.mpr (hl i))) (sub_nonneg.mpr (hu i))
  have hid : (∑ i, w i * (a i-l) * (u-a i)) =
      (u+l)*(∑ i, w i*a i) - (∑ i, w i*a i^2) - (l*u)*(∑ i, w i) := by
    calc
      _ = ∑ i, ((u+l)*(w i*a i) - w i*a i^2 - (l*u)*w i) := by
        apply Finset.sum_congr rfl; intro i hi; ring
      _ = _ := by simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hid,hw,ha] at hnonneg
  linarith

/-- Outside every one of the five open contact balls, with the accepted fixed
radius rho=9999/20000 and scale alpha=2/5. -/
def Missed (p : Fin 5 → E4) (x : E4) : Prop := ∀ i, rho ≤ dist x (alpha • p i)

lemma contact_inner_lower (p x : E4) (r : ℝ) (hr : ‖p‖ ^ 2 = r) (hxp : dist x p ≤ 1) :
    -(1-r-‖x‖^2)/2 ≤ inner ℝ x p := by
  have hd : dist x p ^ 2 ≤ 1 := by nlinarith [dist_nonneg (x:=x) (y:=p)]
  rw [dist_eq_norm, norm_sub_sq_real, hr] at hd
  linarith

lemma missed_inner_upper (p x : E4) (r : ℝ) (hr : ‖p‖ ^ 2 = r)
    (hmiss : rho ≤ dist x (alpha • p)) : inner ℝ x p ≤ (‖x‖^2 + A r)/(2*alpha) := by
  have hrho : 0 ≤ rho := by norm_num [rho]
  have hd : sigma ≤ dist x (alpha • p) ^ 2 := by unfold sigma; nlinarith
  rw [dist_eq_norm, norm_sub_sq_real, Support.norm_smul_sq, hr, inner_smul_right] at hd
  unfold A alpha sigma rho at *
  norm_num at hd ⊢
  linarith

/-- Missed-ball covariance upper estimate, derived from actual contact distances. -/
theorem missed_covariance_upper (w : Fin 5 → ℝ) (p : Fin 5 → E4) (r : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1) (hp : ∑ i, w i • p i = 0)
    (hr : ∀ i, ‖p i‖ ^ 2 = r) (x : E4)
    (hxp : ∀ i, dist x (p i) ≤ 1) (hmiss : Missed p x) :
    Phi w p x ≤ (1-r-‖x‖^2)*(‖x‖^2+A r)/(4*alpha) := by
  have h := weighted_variance_le w (fun i => inner ℝ x (p i))
    (-(1-r-‖x‖^2)/2) ((‖x‖^2+A r)/(2*alpha)) hw0 hw (weighted_inner_zero w p hp x)
    (fun i => contact_inner_lower (p i) x r (hr i) (hxp i))
    (fun i => missed_inner_upper (p i) x r (hr i) (hmiss i))
  change Phi w p x ≤ _ at h
  convert h using 1
  ring

lemma pair_upper_covariance (w : Fin 5 → ℝ) (p : Fin 5 → E4) (r : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1) (hp : ∑ i, w i • p i = 0)
    (hr : ∀ i, ‖p i‖ ^ 2 = r) (x y : E4)
    (hxp : ∀ i, dist x (p i) ≤ 1) (hyp : ∀ i, dist y (p i) ≤ 1)
    (hxmiss : Missed p x) (hymiss : Missed p y) :
    Phi w p x + Phi w p y ≤ V (‖x‖^2+‖y‖^2) (‖x‖^2-‖y‖^2) r := by
  have hx := missed_covariance_upper w p r hw0 hw hp hr x hxp hxmiss
  have hy := missed_covariance_upper w p r hw0 hw hp hr y hyp hymiss
  exact (add_le_add hx hy).trans_eq (by unfold V; ring)

/-- There is no unit-distance pair of actual missed points in the high-radius
range. This uses contact constraints, not merely outer-ball membership. -/
theorem missed_pair_ne_one (w : Fin 5 → ℝ) (p : Fin 5 → E4) (r : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1) (hp : ∑ i, w i • p i = 0)
    (hr : ∀ i, ‖p i‖ ^ 2 = r) (hrlo : 1957/5000 ≤ r) (hrhi : r ≤ 2/5)
    (hdiam : ∀ i j, dist (p i) (p j) ≤ 1) (x y : E4)
    (hx : ‖x‖^2 ≤ r) (hy : ‖y‖^2 ≤ r)
    (hxp : ∀ i, dist x (p i) ≤ 1) (hyp : ∀ i, dist y (p i) ≤ 1)
    (hxmiss : Missed p x) (hymiss : Missed p y) : dist x y ≠ 1 := by
  intro hxy
  exact covariance_bounds_incompatible r (‖x‖^2+‖y‖^2) (‖x‖^2-‖y‖^2)
    (Phi w p x + Phi w p y) hrlo hrhi (by linarith)
    (pair_upper_covariance w p r hw0 hw hp hr x y hxp hyp hxmiss hymiss)
    (pair_lower_covariance w p r hw0 hw hp hr (by linarith) hdiam x y hxy)


end BorsukSix.HighRadiusTailMissed

end

open Metric Bornology BorsukSix.CompactNormalization BorsukSix.ContactSimplex
open BorsukSix.HighRadiusTailMissed BorsukSix.HighRadiusTailScalar
open scoped Pointwise

private theorem change_center (D : ℝ) (hD : 0 < D)
    (c x z : EuclideanSpace ℝ (Fin 4)) :
    dist x (D • (c+z)) = D * dist (D⁻¹ • x - c) z := by
  calc
    _ = dist (D • (D⁻¹ • x)) (D • (c+z)) := by rw [smul_smul, mul_inv_cancel₀ hD.ne', one_smul]
    _ = _ := by
      rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hD,dist_eq_norm,dist_eq_norm]
      congr 2
      abel

private theorem hit_five {K : Set (EuclideanSpace ℝ (Fin 4))} (hK : IsCompact K)
    (hnt : K.Nontrivial)
    (high : ∀ c, ∃ x ∈ K, (627/1000 : ℝ)*diam K < dist x c) :
    ∃ (c : Fin 5 → EuclideanSpace ℝ (Fin 4)) (r : ℝ), 0 < r ∧ 2*r < diam K ∧
      ∀ x ∈ K, ∀ y ∈ K, dist x y = diam K →
        ∃ i, x ∈ ball (c i) r ∨ y ∈ ball (c i) r := by
  classical
  let D := diam K
  have hD : 0 < D := diam_pos hnt hK.isBounded
  obtain ⟨c, hc⟩ := exists_compact_centered_normalization hK.isBounded hD
  let f (x : EuclideanSpace ℝ (Fin 4)) := D⁻¹ • x - c
  let S := f '' K
  have hset : (fun x => x-c) '' ((diam K)⁻¹ • closure K) = S := by
    rw [hK.isClosed.closure_eq, ← Set.image_smul, Set.image_image]
  dsimp only at hc
  rw [hset] at hc
  obtain ⟨hs, hd, hmin⟩ := hc
  have hne : S.Nonempty := hnt.nonempty.image f
  have within (x) (hx : x ∈ S) (y) (hy : y ∈ S) : dist x y ≤ 1 :=
    (dist_le_diam_of_mem hs.isBounded hx hy).trans_eq hd
  let R := radiusAt S 0
  have hR : (627 / 1000 : ℝ) < R := by
    obtain ⟨x, hx, hfar⟩ := high (D • (c+0))
    rw [change_center D hD] at hfar
    have hsmall := dist_le_radiusAt hs hne (show f x ∈ S from ⟨x,hx,rfl⟩) 0
    change 627 / 1000 * D < D * dist (f x) 0 at hfar
    exact (lt_of_mul_lt_mul_left (by simpa [mul_comm] using hfar) hD.le).trans_le hsmall
  have hRhi : R^2 ≤ 2/5 := minimum_center_jung_bound hs hne hd.le hmin
  have hRlo : 1957/5000 ≤ R^2 := by nlinarith [sq_nonneg (R-627/1000)]
  obtain ⟨n, hn, hn5, p, w, hp, _, hwpos, hw, hbary⟩ := exists_positive_contact_simplex hs hne hmin
  have hj := contact_jung_bound hn p w R (fun i => (hp i).2) (fun i => (hwpos i).le)
    hw hbary (fun i j => within _ (hp i).1 _ (hp j).1)
  have hn_eq : n = 5 := by
    by_contra hn'
    have nt : (n : ℝ) ≤ 4 := by exact_mod_cast (show n ≤ 4 by omega)
    have np : 0 < (n : ℝ) := by exact_mod_cast hn
    have hz := (le_div_iff₀ (by positivity : 0 < 2*(n : ℝ))).mp hj
    nlinarith [mul_pos np (show 0 < R^2-3/8 by linarith)]
  subst n
  refine ⟨fun i => D • (c + alpha • p i), D*rho, mul_pos hD (by norm_num [rho]), ?_, ?_⟩
  · change 2*(D*rho) < D
    dsimp [rho]
    linarith
  · intro x hx y hy hxy
    by_contra! nohit
    have miss (v : EuclideanSpace ℝ (Fin 4))
        (hv : ∀ i, v ∉ ball (D • (c + alpha • p i)) (D*rho)) : Missed p (f v) := by
      intro i
      have h := hv i
      rw [mem_ball, change_center D hD] at h
      exact le_of_not_gt (fun hh => h (mul_lt_mul_of_pos_left hh hD))
    have fx : f x ∈ S := ⟨x,hx,rfl⟩
    have fy : f y ∈ S := ⟨y,hy,rfl⟩
    have mass (z) (hz : z ∈ S) : ‖z‖^2 ≤ R^2 := by
      exact pow_le_pow_left₀ (norm_nonneg z)
        (by simpa [R] using dist_le_radiusAt hs hne hz 0) 2
    apply missed_pair_ne_one w p (R^2) (fun i => (hwpos i).le) hw hbary
      (fun i => by rw [(hp i).2]) hRlo hRhi (fun i j => within _ (hp i).1 _ (hp j).1)
      (f x) (f y) (mass _ fx) (mass _ fy) (fun i => within _ fx _ (hp i).1)
      (fun i => within _ fy _ (hp i).1) (miss x (fun i => (nohit i).1)) (miss y (fun i => (nohit i).2))
    dsimp only [f]
    rw [dist_sub_right, dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hD), hxy]
    exact inv_mul_cancel₀ hD.ne'


section BorsukEightMid


-- Helper geometric & algebraic lemmas for Borsuk 4D H1 (4/7 < R <= 627/1000)

private lemma convex_quad_lt {A B C a b z M : ℝ} (hA : 0 ≤ A) (ha : a ≤ z) (hb : z ≤ b)
    (hfa : A * a ^ 2 + B * a + C < M) (hfb : A * b ^ 2 + B * b + C < M) :
    A * z ^ 2 + B * z + C < M := by
  by_cases hab : a = b
  · subst hab
    have hza : z = a := le_antisymm hb ha
    subst hza
    exact hfa
  · have hlt : 0 < b - a := sub_pos.mpr (lt_of_le_of_ne (ha.trans hb) hab)
    have h1 : 0 ≤ A * (b - a) * (b - z) * (z - a) := by
      have hbz : 0 ≤ b - z := sub_nonneg.mpr hb
      have hza : 0 ≤ z - a := sub_nonneg.mpr ha
      positivity
    have hid : (b - a) * (M - (A * z ^ 2 + B * z + C)) =
        (b - z) * (M - (A * a ^ 2 + B * a + C)) +
        (z - a) * (M - (A * b ^ 2 + B * b + C)) +
        A * (b - a) * (b - z) * (z - a) := by ring
    have hsum : 0 < (b - z) * (M - (A * a ^ 2 + B * a + C)) +
        (z - a) * (M - (A * b ^ 2 + B * b + C)) := by
      by_cases hza : a = z
      · subst hza
        have : 0 < (b - a) * (M - (A * a ^ 2 + B * a + C)) := mul_pos hlt (sub_pos.mpr hfa)
        linarith
      · have hzpos : 0 < z - a := sub_pos.mpr (lt_of_le_of_ne ha hza)
        have hterm1 : 0 ≤ (b - z) * (M - (A * a ^ 2 + B * a + C)) :=
          mul_nonneg (sub_nonneg.mpr hb) (sub_pos.mpr hfa).le
        have hterm2 : 0 < (z - a) * (M - (A * b ^ 2 + B * b + C)) :=
          mul_pos hzpos (sub_pos.mpr hfb)
        linarith
    have hpos : 0 < (b - a) * (M - (A * z ^ 2 + B * z + C)) := by linarith
    have hdiff : 0 < M - (A * z ^ 2 + B * z + C) := pos_of_mul_pos_right hpos hlt.le
    linarith

private lemma convex_2d_lt {Ax Bx Ay By C D x0 x1 y0 y1 x y M : ℝ}
    (hAx : 0 ≤ Ax) (hAy : 0 ≤ Ay)
    (hx0 : x0 ≤ x) (hx1 : x ≤ x1) (hy0 : y0 ≤ y) (hy1 : y ≤ y1)
    (h00 : Ax * x0 ^ 2 + Bx * x0 + Ay * y0 ^ 2 + By * y0 + C + D * x0 * y0 < M)
    (h01 : Ax * x0 ^ 2 + Bx * x0 + Ay * y1 ^ 2 + By * y1 + C + D * x0 * y1 < M)
    (h10 : Ax * x1 ^ 2 + Bx * x1 + Ay * y0 ^ 2 + By * y0 + C + D * x1 * y0 < M)
    (h11 : Ax * x1 ^ 2 + Bx * x1 + Ay * y1 ^ 2 + By * y1 + C + D * x1 * y1 < M) :
    Ax * x ^ 2 + Bx * x + Ay * y ^ 2 + By * y + C + D * x * y < M := by
  have hx0_y : Ax * x0 ^ 2 + Bx * x0 + Ay * y ^ 2 + By * y + C + D * x0 * y < M := by
    have := convex_quad_lt (A := Ay) (B := By + D * x0) (C := Ax * x0 ^ 2 + Bx * x0 + C)
      hAy hy0 hy1 (by linarith) (by linarith)
    linarith
  have hx1_y : Ax * x1 ^ 2 + Bx * x1 + Ay * y ^ 2 + By * y + C + D * x1 * y < M := by
    have := convex_quad_lt (A := Ay) (B := By + D * x1) (C := Ax * x1 ^ 2 + Bx * x1 + C)
      hAy hy0 hy1 (by linarith) (by linarith)
    linarith
  have := convex_quad_lt (A := Ax) (B := Bx + D * y) (C := Ay * y ^ 2 + By * y + C)
    hAx hx0 hx1 (by linarith) (by linarith)
  linarith

private lemma u_sq_le_U_sq {u b rhs A U : ℝ} (hu : 0 ≤ u) (hA : 0 < A)
    (h : u ^ 2 + 2 * b * u ≤ rhs) (hU : (rhs + (A - b) ^ 2) / (2 * A) ≤ U) :
    u ^ 2 ≤ U ^ 2 := by
  have h1 : 2 * A * (u + b) ≤ (u + b) ^ 2 + A ^ 2 := by nlinarith [sq_nonneg (u + b - A)]
  have h2 : (u + b) ^ 2 ≤ rhs + b ^ 2 := by linarith
  have h3 : u ≤ (rhs + (A - b) ^ 2) / (2 * A) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  have h4 : u ≤ U := h3.trans hU
  nlinarith

private lemma u_sq_le_div_p1 {u R s r1R rhs : ℝ} (hu : 0 ≤ u) (huR : u ≤ R) (_hR : 0 < R)
    (hs : 0 ≤ s) (hr : 0 ≤ r1R) (h : u ^ 2 + 2 * s * (r1R * R) * u ≤ rhs) :
    u ^ 2 ≤ rhs / (1 + 2 * s * r1R) := by
  have hden : 0 < 1 + 2 * s * r1R := by nlinarith
  rw [le_div_iff₀ hden]
  have hu2 : u ^ 2 ≤ R * u := by nlinarith
  have hsr : 0 ≤ 2 * s * r1R := by positivity
  have hmul : (2 * s * r1R) * u ^ 2 ≤ (2 * s * r1R) * (R * u) := mul_le_mul_of_nonneg_left hu2 hsr
  linarith

-- Five exact algebraic pentagonal sectors in R^2 (zero trigonometry)
private def c5 : ℝ := (Real.sqrt 5 - 1) / 4
private def s5 : ℝ := Real.sqrt ((5 + Real.sqrt 5) / 8)
private def c5_2 : ℝ := -(Real.sqrt 5 + 1) / 4
private def s5_2 : ℝ := 2 * s5 * c5

private lemma sqrt5_gt_two : (2 : ℝ) < Real.sqrt 5 := by
  rw [show (2 : ℝ) = Real.sqrt 4 by norm_num]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

private lemma sqrt5_lt_22361 : Real.sqrt 5 < 22361 / 10000 := by
  rw [Real.sqrt_lt' (by norm_num)]
  norm_num

private lemma c5_pos : 0 < c5 := by
  unfold c5; linarith [sqrt5_gt_two]

private lemma c5_sq_add_s5_sq : c5 ^ 2 + s5 ^ 2 = 1 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : 0 ≤ (5 + Real.sqrt 5) / 8 := by linarith [Real.sqrt_nonneg 5]
  unfold c5 s5
  rw [Real.sq_sqrt hpos]
  nlinarith

private lemma s5_pos : 0 < s5 := by
  unfold s5
  apply Real.sqrt_pos.mpr
  linarith [Real.sqrt_nonneg 5]

private lemma c5_2_eq : c5_2 = 2 * c5 ^ 2 - 1 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  unfold c5 c5_2
  nlinarith

private lemma c5_mul_c5_2 : c5 * c5_2 = -1 / 4 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  unfold c5 c5_2
  nlinarith

private lemma c5_2_sq_add_s5_2_sq : c5_2 ^ 2 + s5_2 ^ 2 = 1 := by
  have h1 := c5_sq_add_s5_sq
  have h2 := c5_2_eq
  unfold s5_2
  nlinarith

private def rayX : Fin 5 → ℝ
  | 0 => 1
  | 1 => c5
  | 2 => c5_2
  | 3 => c5_2
  | 4 => c5

private def rayY : Fin 5 → ℝ
  | 0 => 0
  | 1 => s5
  | 2 => s5_2
  | 3 => -s5_2
  | 4 => -s5

private lemma ray_norm_sq (k : Fin 5) : rayX k ^ 2 + rayY k ^ 2 = 1 := by
  fin_cases k
  · norm_num [rayX, rayY]
  · exact c5_sq_add_s5_sq
  · exact c5_2_sq_add_s5_2_sq
  · simp only [rayX, rayY, neg_sq]; exact c5_2_sq_add_s5_2_sq
  · simp only [rayX, rayY, neg_sq]; exact c5_sq_add_s5_sq

private lemma ray_adj_dot (k : Fin 5) :
    rayX k * rayX (k + 1) + rayY k * rayY (k + 1) = c5 := by
  have h1 := c5_sq_add_s5_sq
  have h2 := c5_2_eq
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  fin_cases k
  · change rayX 0 * rayX 1 + rayY 0 * rayY 1 = c5; simp [rayX, rayY]
  · change rayX 1 * rayX 2 + rayY 1 * rayY 2 = c5; simp only [rayX, rayY, s5_2]; linear_combination 2 * c5 * h1 + c5 * h2
  · change rayX 2 * rayX 3 + rayY 2 * rayY 3 = c5; simp only [rayX, rayY, s5_2]; unfold c5 c5_2 at *; nlinarith
  · change rayX 3 * rayX 4 + rayY 3 * rayY 4 = c5; simp only [rayX, rayY, s5_2]; linear_combination 2 * c5 * h1 + c5 * h2
  · change rayX 4 * rayX 0 + rayY 4 * rayY 0 = c5; simp [rayX, rayY]

private lemma ray_adj_det (k : Fin 5) :
    rayX k * rayY (k + 1) - rayY k * rayX (k + 1) = s5 := by
  have h2 := c5_2_eq
  have h3 := c5_mul_c5_2
  fin_cases k
  · change rayX 0 * rayY 1 - rayY 0 * rayX 1 = s5; simp [rayX, rayY]
  · change rayX 1 * rayY 2 - rayY 1 * rayX 2 = s5; simp only [rayX, rayY, s5_2]; linear_combination -s5 * h2
  · change rayX 2 * rayY 3 - rayY 2 * rayX 3 = s5; simp only [rayX, rayY, s5_2]; linear_combination -4 * s5 * h3
  · change rayX 3 * rayY 4 - rayY 3 * rayX 4 = s5; simp only [rayX, rayY, s5_2]; linear_combination -s5 * h2
  · change rayX 4 * rayY 0 - rayY 4 * rayX 0 = s5; simp [rayX, rayY]

private lemma ray_sum_X : ∑ k : Fin 5, rayX k = 0 := by
  simp only [Fin.sum_univ_five, rayX, c5, c5_2]
  ring

private lemma ray_sum_Y : ∑ k : Fin 5, rayY k = 0 := by
  simp only [Fin.sum_univ_five, rayY]
  ring

private def inSector (k : Fin 5) (a b : ℝ) : Prop :=
  0 ≤ rayX k * b - rayY k * a ∧ rayX (k + 1) * b - rayY (k + 1) * a ≤ 0

private lemma exists_inSector (a b : ℝ) : ∃ k : Fin 5, inSector k a b := by
  let d (k : Fin 5) : ℝ := rayX k * b - rayY k * a
  have hsum : d 0 + d 1 + d 2 + d 3 + d 4 = 0 := by
    have hX := ray_sum_X
    have hY := ray_sum_Y
    simp only [Fin.sum_univ_five] at hX hY
    dsimp only [d]
    linear_combination b * hX - a * hY
  by_contra! h
  have hstep : ∀ k : Fin 5, 0 ≤ d k → 0 < d (k + 1) := by
    intro k hk
    by_contra hle
    exact h k ⟨hk, le_of_not_gt hle⟩
  by_cases h0 : 0 ≤ d 0
  · have h1 : 0 < d 1 := hstep 0 h0
    have h2 : 0 < d 2 := hstep 1 h1.le
    have h3 : 0 < d 3 := hstep 2 h2.le
    have h4 : 0 < d 4 := hstep 3 h3.le
    linarith
  · have h0lt : d 0 < 0 := lt_of_not_ge h0
    have h4lt : d 4 < 0 := by by_contra h4; exact h 4 ⟨le_of_not_gt h4, h0lt.le⟩
    have h3lt : d 3 < 0 := by by_contra h3; exact h 3 ⟨le_of_not_gt h3, h4lt.le⟩
    have h2lt : d 2 < 0 := by by_contra h2; exact h 2 ⟨le_of_not_gt h2, h3lt.le⟩
    have h1lt : d 1 < 0 := by by_contra h1; exact h 1 ⟨le_of_not_gt h1, h2lt.le⟩
    linarith

private lemma sector_dot_ge {k : Fin 5} {a1 b1 a2 b2 : ℝ}
    (h1 : inSector k a1 b1) (h2 : inSector k a2 b2) :
    c5 * Real.sqrt (a1 ^ 2 + b1 ^ 2) * Real.sqrt (a2 ^ 2 + b2 ^ 2) ≤ a1 * a2 + b1 * b2 := by
  have hs := s5_pos
  have hc := c5_pos
  have hdet := ray_adj_det k
  have hdot := ray_adj_dot k
  have hn1 := ray_norm_sq k
  have hn2 := ray_norm_sq (k + 1)
  let ux := rayX k
  let uy := rayY k
  let vx := rayX (k + 1)
  let vy := rayY (k + 1)
  let α1 := (a1 * vy - b1 * vx) / s5
  let β1 := (ux * b1 - uy * a1) / s5
  let α2 := (a2 * vy - b2 * vx) / s5
  let β2 := (ux * b2 - uy * a2) / s5
  have hα1 : 0 ≤ α1 := div_nonneg (by linarith [h1.2]) hs.le
  have hβ1 : 0 ≤ β1 := div_nonneg h1.1 hs.le
  have hα2 : 0 ≤ α2 := div_nonneg (by linarith [h2.2]) hs.le
  have hβ2 : 0 ≤ β2 := div_nonneg h2.1 hs.le
  have ha1 : a1 = α1 * ux + β1 * vx := by
    dsimp only [α1, β1]
    field_simp
    linear_combination -a1 * hdet
  have hb1 : b1 = α1 * uy + β1 * vy := by
    dsimp only [α1, β1]
    field_simp
    linear_combination -b1 * hdet
  have ha2 : a2 = α2 * ux + β2 * vx := by
    dsimp only [α2, β2]
    field_simp
    linear_combination -a2 * hdet
  have hb2 : b2 = α2 * uy + β2 * vy := by
    dsimp only [α2, β2]
    field_simp
    linear_combination -b2 * hdet
  have hpair : a1 * a2 + b1 * b2 = α1 * α2 + β1 * β2 + c5 * (α1 * β2 + β1 * α2) := by
    rw [ha1, hb1, ha2, hb2]
    linear_combination (α1 * α2) * hn1 + (β1 * β2) * hn2 + (α1 * β2 + β1 * α2) * hdot
  have hsq1 : a1 ^ 2 + b1 ^ 2 = α1 ^ 2 + β1 ^ 2 + 2 * c5 * α1 * β1 := by
    rw [ha1, hb1]
    linear_combination (α1 ^ 2) * hn1 + (β1 ^ 2) * hn2 + (2 * α1 * β1) * hdot
  have hsq2 : a2 ^ 2 + b2 ^ 2 = α2 ^ 2 + β2 ^ 2 + 2 * c5 * α2 * β2 := by
    rw [ha2, hb2]
    linear_combination (α2 ^ 2) * hn1 + (β2 ^ 2) * hn2 + (2 * α2 * β2) * hdot
  have hnonneg : 0 ≤ a1 * a2 + b1 * b2 := by rw [hpair]; positivity
  have hc1 : 0 ≤ 1 - c5 ^ 2 := by nlinarith [c5_sq_add_s5_sq, sq_nonneg s5]
  have hdiff : (a1 * a2 + b1 * b2) ^ 2 - c5 ^ 2 * (a1 ^ 2 + b1 ^ 2) * (a2 ^ 2 + b2 ^ 2) =
      (1 - c5 ^ 2) * ((α1 * α2 + β1 * β2) ^ 2 +
        2 * c5 * (α1 * α2 + β1 * β2) * (α1 * β2 + β1 * α2) +
        4 * c5 ^ 2 * α1 * β1 * α2 * β2) := by
    rw [hpair, hsq1, hsq2]; ring
  have hdiff_nn : 0 ≤ (a1 * a2 + b1 * b2) ^ 2 - c5 ^ 2 * (a1 ^ 2 + b1 ^ 2) * (a2 ^ 2 + b2 ^ 2) := by
    rw [hdiff]; positivity
  have hprod_sq : (c5 * Real.sqrt (a1 ^ 2 + b1 ^ 2) * Real.sqrt (a2 ^ 2 + b2 ^ 2)) ^ 2 =
      c5 ^ 2 * (a1 ^ 2 + b1 ^ 2) * (a2 ^ 2 + b2 ^ 2) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  nlinarith [Real.sqrt_nonneg (a1 ^ 2 + b1 ^ 2), Real.sqrt_nonneg (a2 ^ 2 + b2 ^ 2)]

private lemma bc_le_c5_prod :
    (469 / 2500 : ℝ) ≤ c5 * Real.sqrt (1 - (29 / 50 : ℝ) ^ 2) * (Real.sqrt 5 / 3) := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5hi := sqrt5_lt_22361
  have h1659 : (4073 / 5000 : ℝ) ≤ Real.sqrt (1 - (29 / 50 : ℝ) ^ 2) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hmul : (27639 / 120000 : ℝ) ≤ c5 * (Real.sqrt 5 / 3) := by
    unfold c5
    nlinarith
  have hnn : (0 : ℝ) ≤ c5 * (Real.sqrt 5 / 3) := by
    have := c5_pos; positivity
  nlinarith


private lemma r1R_lo_bound {R : ℝ} (hlo : (4 / 7 : ℝ) ≤ R) (hhi : R ≤ (121 / 200 : ℝ)) :
    0 < 4 * R ^ 2 - 1 - 4 * R ^ 4 * ((245 / 100 : ℝ) * R - 554 / 1000) ^ 2 := by
  have hR : (0 : ℝ) < R := by linarith
  set t : ℝ := R - (4 / 7 : ℝ)
  set u : ℝ := (121 / 200 : ℝ) - R
  have ht : 0 ≤ t := sub_nonneg.mpr hlo
  have hu : 0 ≤ u := sub_nonneg.mpr hhi
  have hid : (26948038322500 : ℝ) * (4 * R ^ 2 - 1 - 4 * R ^ 4 * ((245 / 100 : ℝ) * R - 554 / 1000) ^ 2) = (10779215329 : ℝ) + (8987901440000000000 : ℝ) * u ^ 6 + (475273263718400000000 : ℝ) * t * u ^ 5 + (1890549188598784000000 : ℝ) * t ^ 2 * u ^ 4 + (2948660824350295040000 : ℝ) * t ^ 3 * u ^ 3 + (2118502033074520318400 : ℝ) * t ^ 4 * u ^ 2 + (630722074777258707600 : ℝ) * t ^ 5 * u + (36616392710249305975 : ℝ) * t ^ 6 := by dsimp only [t, u]; ring
  clear_value t u
  have hpos : 0 < (26948038322500 : ℝ) * (4 * R ^ 2 - 1 - 4 * R ^ 4 * ((245 / 100 : ℝ) * R - 554 / 1000) ^ 2) := by rw [hid]; positivity
  have hfin : 0 < 4 * R ^ 2 - 1 - 4 * R ^ 4 * ((245 / 100 : ℝ) * R - 554 / 1000) ^ 2 := pos_of_mul_pos_right hpos (by positivity)
  linarith

private lemma r1R_hi_bound {R : ℝ} (hlo : (121 / 200 : ℝ) ≤ R) (hhi : R ≤ (627 / 1000 : ℝ)) :
    0 < 4 * R ^ 2 - 1 - 4 * R ^ 4 * ((145 / 100 : ℝ) * R + 52 / 1000) ^ 2 := by
  have hR : (0 : ℝ) < R := by linarith
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  have ht : 0 ≤ t := sub_nonneg.mpr hlo
  have hu : 0 ≤ u := sub_nonneg.mpr hhi
  have hid : (283449760000 : ℝ) * (4 * R ^ 2 - 1 - 4 * R ^ 4 * ((145 / 100 : ℝ) * R + 52 / 1000) ^ 2) = (170069856 : ℝ) + (1874461782652734375 : ℝ) * u ^ 6 + (29745760307041093750 : ℝ) * t * u ^ 5 + (103356828818159515625 : ℝ) * t ^ 2 * u ^ 4 + (152407960772433912500 : ℝ) * t ^ 3 * u ^ 3 + (106395469426248975625 : ℝ) * t ^ 4 * u ^ 2 + (31511939867808693750 : ℝ) * t ^ 5 * u + (2038898536409992775 : ℝ) * t ^ 6 := by dsimp only [t, u]; ring
  clear_value t u
  have hpos : 0 < (283449760000 : ℝ) * (4 * R ^ 2 - 1 - 4 * R ^ 4 * ((145 / 100 : ℝ) * R + 52 / 1000) ^ 2) := by rw [hid]; positivity
  have hfin : 0 < 4 * R ^ 2 - 1 - 4 * R ^ 4 * ((145 / 100 : ℝ) * R + 52 / 1000) ^ 2 := pos_of_mul_pos_right hpos (by positivity)
  linarith

private lemma north_c_b0_0 {R : ℝ} (hlo : (4 / 7 : ℝ) ≤ R) (hhi : R ≤ (627 / 1000 : ℝ)) :
    ((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (-1 / 5 : ℝ) * ((R - 1 / (2 * R))) + (-1 / 5 : ℝ) ^ 2)) + ((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (7 / 20 : ℝ) * (0) + (7 / 20 : ℝ) ^ 2)) - 2 * ((R - 1 / (2 * R))) * (0) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  set t : ℝ := R - (4 / 7 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  have ht : 0 ≤ t := sub_nonneg.mpr hlo
  have hu : 0 ≤ u := sub_nonneg.mpr hhi
  have hden : (0 : ℝ) < 2 * R := by positivity
  have hid : (52977482100 : ℝ) * ((2 * R) * (1 - (((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (-1 / 5 : ℝ) * ((R - 1 / (2 * R))) + (-1 / 5 : ℝ) ^ 2)) + ((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (7 / 20 : ℝ) * (0) + (7 / 20 : ℝ) ^ 2)) - 2 * ((R - 1 / (2 * R))) * (0)))) = (3708423747 : ℝ) + (73581000000000 : ℝ) * u ^ 3 + (178002597500000 : ℝ) * t * u ^ 2 + (127914047240000 : ℝ) * t ^ 2 * u + (23256994264000 : ℝ) * t ^ 3 := by
    field_simp [hR.ne']; dsimp only [t, u]; ring
  clear_value t u
  have hpos : 0 < (52977482100 : ℝ) * ((2 * R) * (1 - (((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (-1 / 5 : ℝ) * ((R - 1 / (2 * R))) + (-1 / 5 : ℝ) ^ 2)) + ((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (7 / 20 : ℝ) * (0) + (7 / 20 : ℝ) ^ 2)) - 2 * ((R - 1 / (2 * R))) * (0)))) := by rw [hid]; positivity
  have hfin : 0 < (2 * R) * (1 - (((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (-1 / 5 : ℝ) * ((R - 1 / (2 * R))) + (-1 / 5 : ℝ) ^ 2)) + ((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (7 / 20 : ℝ) * (0) + (7 / 20 : ℝ) ^ 2)) - 2 * ((R - 1 / (2 * R))) * (0))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (-1 / 5 : ℝ) * ((R - 1 / (2 * R))) + (-1 / 5 : ℝ) ^ 2)) + ((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (7 / 20 : ℝ) * (0) + (7 / 20 : ℝ) ^ 2)) - 2 * ((R - 1 / (2 * R))) * (0)) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma north_c_b0_tau {R : ℝ} (hlo : (4 / 7 : ℝ) ≤ R) (hhi : R ≤ (627 / 1000 : ℝ)) :
    ((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (-1 / 5 : ℝ) * ((R - 1 / (2 * R))) + (-1 / 5 : ℝ) ^ 2)) + ((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (7 / 20 : ℝ) * (((37 / 20 : ℝ) * R - 389 / 500)) + (7 / 20 : ℝ) ^ 2)) - 2 * ((R - 1 / (2 * R))) * (((37 / 20 : ℝ) * R - 389 / 500)) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  set t : ℝ := R - (4 / 7 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  have ht : 0 ≤ t := sub_nonneg.mpr hlo
  have hu : 0 ≤ u := sub_nonneg.mpr hhi
  have hden : (0 : ℝ) < 2 * R := by positivity
  have hid : (529774821000 : ℝ) * ((2 * R) * (1 - (((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (-1 / 5 : ℝ) * ((R - 1 / (2 * R))) + (-1 / 5 : ℝ) ^ 2)) + ((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (7 / 20 : ℝ) * (((37 / 20 : ℝ) * R - 389 / 500)) + (7 / 20 : ℝ) ^ 2)) - 2 * ((R - 1 / (2 * R))) * (((37 / 20 : ℝ) * R - 389 / 500))))) = (4767973389 : ℝ) + (402789800000000 : ℝ) * u ^ 3 + (815322321800000 : ℝ) * t * u ^ 2 + (442805568954000 : ℝ) * t ^ 2 * u + (31838826069400 : ℝ) * t ^ 3 := by
    field_simp [hR.ne']; dsimp only [t, u]; ring
  clear_value t u
  have hpos : 0 < (529774821000 : ℝ) * ((2 * R) * (1 - (((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (-1 / 5 : ℝ) * ((R - 1 / (2 * R))) + (-1 / 5 : ℝ) ^ 2)) + ((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (7 / 20 : ℝ) * (((37 / 20 : ℝ) * R - 389 / 500)) + (7 / 20 : ℝ) ^ 2)) - 2 * ((R - 1 / (2 * R))) * (((37 / 20 : ℝ) * R - 389 / 500))))) := by rw [hid]; positivity
  have hfin : 0 < (2 * R) * (1 - (((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (-1 / 5 : ℝ) * ((R - 1 / (2 * R))) + (-1 / 5 : ℝ) ^ 2)) + ((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (7 / 20 : ℝ) * (((37 / 20 : ℝ) * R - 389 / 500)) + (7 / 20 : ℝ) ^ 2)) - 2 * ((R - 1 / (2 * R))) * (((37 / 20 : ℝ) * R - 389 / 500)))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (-1 / 5 : ℝ) * ((R - 1 / (2 * R))) + (-1 / 5 : ℝ) ^ 2)) + ((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (7 / 20 : ℝ) * (((37 / 20 : ℝ) * R - 389 / 500)) + (7 / 20 : ℝ) ^ 2)) - 2 * ((R - 1 / (2 * R))) * (((37 / 20 : ℝ) * R - 389 / 500))) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma north_c_0_0 {R : ℝ} (hlo : (4 / 7 : ℝ) ≤ R) (hhi : R ≤ (627 / 1000 : ℝ)) :
    ((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (-1 / 5 : ℝ) * (0) + (-1 / 5 : ℝ) ^ 2)) + ((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (7 / 20 : ℝ) * (0) + (7 / 20 : ℝ) ^ 2)) - 2 * (0) * (0) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  set t : ℝ := R - (4 / 7 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  have ht : 0 ≤ t := sub_nonneg.mpr hlo
  have hu : 0 ≤ u := sub_nonneg.mpr hhi
  have hid : (27237780 : ℝ) * (1 - (((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (-1 / 5 : ℝ) * (0) + (-1 / 5 : ℝ) ^ 2)) + ((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (7 / 20 : ℝ) * (0) + (7 / 20 : ℝ) ^ 2)) - 2 * (0) * (0))) = (1361889 : ℝ) + (1819750000 : ℝ) * u ^ 2 + (2394700000 : ℝ) * t * u + (514421600 : ℝ) * t ^ 2 := by dsimp only [t, u]; ring
  clear_value t u
  have hpos : 0 < (27237780 : ℝ) * (1 - (((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (-1 / 5 : ℝ) * (0) + (-1 / 5 : ℝ) ^ 2)) + ((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (7 / 20 : ℝ) * (0) + (7 / 20 : ℝ) ^ 2)) - 2 * (0) * (0))) := by rw [hid]; positivity
  have hfin : 0 < 1 - (((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (-1 / 5 : ℝ) * (0) + (-1 / 5 : ℝ) ^ 2)) + ((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (7 / 20 : ℝ) * (0) + (7 / 20 : ℝ) ^ 2)) - 2 * (0) * (0)) := pos_of_mul_pos_right hpos (by positivity)
  linarith

private lemma north_c_0_tau {R : ℝ} (hlo : (4 / 7 : ℝ) ≤ R) (hhi : R ≤ (627 / 1000 : ℝ)) :
    ((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (-1 / 5 : ℝ) * (0) + (-1 / 5 : ℝ) ^ 2)) + ((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (7 / 20 : ℝ) * (((37 / 20 : ℝ) * R - 389 / 500)) + (7 / 20 : ℝ) ^ 2)) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500)) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  set t : ℝ := R - (4 / 7 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  have ht : 0 ≤ t := sub_nonneg.mpr hlo
  have hu : 0 ≤ u := sub_nonneg.mpr hhi
  have hid : (68094450 : ℝ) * (1 - (((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (-1 / 5 : ℝ) * (0) + (-1 / 5 : ℝ) ^ 2)) + ((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (7 / 20 : ℝ) * (((37 / 20 : ℝ) * R - 389 / 500)) + (7 / 20 : ℝ) ^ 2)) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500)))) = (4085667 : ℝ) + (4807605000 : ℝ) * u ^ 2 + (6679524250 : ℝ) * t * u + (1720598250 : ℝ) * t ^ 2 := by dsimp only [t, u]; ring
  clear_value t u
  have hpos : 0 < (68094450 : ℝ) * (1 - (((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (-1 / 5 : ℝ) * (0) + (-1 / 5 : ℝ) ^ 2)) + ((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (7 / 20 : ℝ) * (((37 / 20 : ℝ) * R - 389 / 500)) + (7 / 20 : ℝ) ^ 2)) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500)))) := by rw [hid]; positivity
  have hfin : 0 < 1 - (((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (-1 / 5 : ℝ) * (0) + (-1 / 5 : ℝ) ^ 2)) + ((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (7 / 20 : ℝ) * (((37 / 20 : ℝ) * R - 389 / 500)) + (7 / 20 : ℝ) ^ 2)) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500))) := pos_of_mul_pos_right hpos (by positivity)
  linarith

private lemma north_c_mR_0 {R : ℝ} (hlo : (4 / 7 : ℝ) ≤ R) (hhi : R ≤ (627 / 1000 : ℝ)) :
    ((10 / 9 : ℝ) * (1 - R ^ 2 + 2 * R * ((-R))) + (1 / 9 : ℝ) * (-2 * (-1 / 5 : ℝ) * ((-R)) + (-1 / 5 : ℝ) ^ 2)) + ((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (7 / 20 : ℝ) * (0) + (7 / 20 : ℝ) ^ 2)) - 2 * ((-R)) * (0) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  set t : ℝ := R - (4 / 7 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  have ht : 0 ≤ t := sub_nonneg.mpr hlo
  have hu : 0 ≤ u := sub_nonneg.mpr hhi
  have hid : (13618890 : ℝ) * (1 - (((10 / 9 : ℝ) * (1 - R ^ 2 + 2 * R * ((-R))) + (1 / 9 : ℝ) * (-2 * (-1 / 5 : ℝ) * ((-R)) + (-1 / 5 : ℝ) ^ 2)) + ((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (7 / 20 : ℝ) * (0) + (7 / 20 : ℝ) ^ 2)) - 2 * ((-R)) * (0))) = (4085667 : ℝ) + (1419375000 : ℝ) * u ^ 2 + (3472042000 : ℝ) * t * u + (2082931200 : ℝ) * t ^ 2 := by dsimp only [t, u]; ring
  clear_value t u
  have hpos : 0 < (13618890 : ℝ) * (1 - (((10 / 9 : ℝ) * (1 - R ^ 2 + 2 * R * ((-R))) + (1 / 9 : ℝ) * (-2 * (-1 / 5 : ℝ) * ((-R)) + (-1 / 5 : ℝ) ^ 2)) + ((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (7 / 20 : ℝ) * (0) + (7 / 20 : ℝ) ^ 2)) - 2 * ((-R)) * (0))) := by rw [hid]; positivity
  have hfin : 0 < 1 - (((10 / 9 : ℝ) * (1 - R ^ 2 + 2 * R * ((-R))) + (1 / 9 : ℝ) * (-2 * (-1 / 5 : ℝ) * ((-R)) + (-1 / 5 : ℝ) ^ 2)) + ((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (7 / 20 : ℝ) * (0) + (7 / 20 : ℝ) ^ 2)) - 2 * ((-R)) * (0)) := pos_of_mul_pos_right hpos (by positivity)
  linarith

private lemma north_c_mR_tau {R : ℝ} (hlo : (4 / 7 : ℝ) ≤ R) (hhi : R ≤ (627 / 1000 : ℝ)) :
    ((10 / 9 : ℝ) * (1 - R ^ 2 + 2 * R * ((-R))) + (1 / 9 : ℝ) * (-2 * (-1 / 5 : ℝ) * ((-R)) + (-1 / 5 : ℝ) ^ 2)) + ((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (7 / 20 : ℝ) * (((37 / 20 : ℝ) * R - 389 / 500)) + (7 / 20 : ℝ) ^ 2)) - 2 * ((-R)) * (((37 / 20 : ℝ) * R - 389 / 500)) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  set t : ℝ := R - (4 / 7 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  have ht : 0 ≤ t := sub_nonneg.mpr hlo
  have hu : 0 ≤ u := sub_nonneg.mpr hhi
  have hid : (13618890 : ℝ) * (1 - (((10 / 9 : ℝ) * (1 - R ^ 2 + 2 * R * ((-R))) + (1 / 9 : ℝ) * (-2 * (-1 / 5 : ℝ) * ((-R)) + (-1 / 5 : ℝ) ^ 2)) + ((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (7 / 20 : ℝ) * (((37 / 20 : ℝ) * R - 389 / 500)) + (7 / 20 : ℝ) ^ 2)) - 2 * ((-R)) * (((37 / 20 : ℝ) * R - 389 / 500)))) = (1361889 : ℝ) + (990241000 : ℝ) * u ^ 2 + (1994069770 : ℝ) * t * u + (983703077 : ℝ) * t ^ 2 := by dsimp only [t, u]; ring
  clear_value t u
  have hpos : 0 < (13618890 : ℝ) * (1 - (((10 / 9 : ℝ) * (1 - R ^ 2 + 2 * R * ((-R))) + (1 / 9 : ℝ) * (-2 * (-1 / 5 : ℝ) * ((-R)) + (-1 / 5 : ℝ) ^ 2)) + ((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (7 / 20 : ℝ) * (((37 / 20 : ℝ) * R - 389 / 500)) + (7 / 20 : ℝ) ^ 2)) - 2 * ((-R)) * (((37 / 20 : ℝ) * R - 389 / 500)))) := by rw [hid]; positivity
  have hfin : 0 < 1 - (((10 / 9 : ℝ) * (1 - R ^ 2 + 2 * R * ((-R))) + (1 / 9 : ℝ) * (-2 * (-1 / 5 : ℝ) * ((-R)) + (-1 / 5 : ℝ) ^ 2)) + ((10 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * (-2 * (7 / 20 : ℝ) * (((37 / 20 : ℝ) * R - 389 / 500)) + (7 / 20 : ℝ) ^ 2)) - 2 * ((-R)) * (((37 / 20 : ℝ) * R - 389 / 500))) := pos_of_mul_pos_right hpos (by positivity)
  linarith

private lemma south_lo_pp_0_0 {R : ℝ} (hlo : (4 / 7 : ℝ) ≤ R) (hhi : R ≤ (121 / 200 : ℝ)) :
    ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) - 2 * (0) * (0) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hD_pos : (0 : ℝ) < (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) := by linarith
  set t : ℝ := R - (4 / 7 : ℝ)
  set u : ℝ := (121 / 200 : ℝ) - R
  have ht : 0 ≤ t := sub_nonneg.mpr hlo
  have hu : 0 ≤ u := sub_nonneg.mpr hhi
  have hden : (0 : ℝ) < (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) := by positivity
  have hid : (5522500 : ℝ) * (((1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) - 2 * (0) * (0)))) = (497025 : ℝ) + (508144000 : ℝ) * u ^ 2 + (1982824200 : ℝ) * t * u + (1489339124 : ℝ) * t ^ 2 := by
    set D_var : ℝ := (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))
    have h_D_var : D_var ≠ 0 := (hD_pos).ne'
    field_simp [hR.ne', h_D_var]
    dsimp only [D_var, t, u]; ring
  clear_value t u
  have hpos : 0 < (5522500 : ℝ) * (((1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) - 2 * (0) * (0)))) := by rw [hid]; positivity
  have hfin : 0 < ((1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) - 2 * (0) * (0))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) - 2 * (0) * (0)) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma south_lo_pp_0_tau {R : ℝ} (hlo : (4 / 7 : ℝ) ≤ R) (hhi : R ≤ (121 / 200 : ℝ)) :
    ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500)) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hD_pos : (0 : ℝ) < (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) := by linarith
  set t : ℝ := R - (4 / 7 : ℝ)
  set u : ℝ := (121 / 200 : ℝ) - R
  have ht : 0 ≤ t := sub_nonneg.mpr hlo
  have hu : 0 ≤ u := sub_nonneg.mpr hhi
  have hden : (0 : ℝ) < (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) := by positivity
  have hid : (20764600000 : ℝ) * (((1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500))))) = (2076460000 : ℝ) + (81541362979328 : ℝ) * u ^ 3 + (352685884838336 : ℝ) * t * u ^ 2 + (459948490180760 : ℝ) * t ^ 2 * u + (188601996352525 : ℝ) * t ^ 3 := by
    set D_var : ℝ := (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))
    have h_D_var : D_var ≠ 0 := (hD_pos).ne'
    field_simp [hR.ne', h_D_var]
    dsimp only [D_var, t, u]; ring
  clear_value t u
  have hpos : 0 < (20764600000 : ℝ) * (((1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500))))) := by rw [hid]; positivity
  have hfin : 0 < ((1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500)))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500))) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma south_lo_pp_tau_tau {R : ℝ} (hlo : (4 / 7 : ℝ) ≤ R) (hhi : R ≤ (121 / 200 : ℝ)) :
    ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * (((37 / 20 : ℝ) * R - 389 / 500)) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hD_pos : (0 : ℝ) < (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) := by linarith
  set t : ℝ := R - (4 / 7 : ℝ)
  set u : ℝ := (121 / 200 : ℝ) - R
  have ht : 0 ≤ t := sub_nonneg.mpr hlo
  have hu : 0 ≤ u := sub_nonneg.mpr hhi
  have hden : (0 : ℝ) < (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) := by positivity
  have hid : (552250000 : ℝ) * (((1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * (((37 / 20 : ℝ) * R - 389 / 500))))) = (165675000 : ℝ) + (152996423104 : ℝ) * u ^ 2 + (476919179520 : ℝ) * t * u + (331761616025 : ℝ) * t ^ 2 := by
    set D_var : ℝ := (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))
    have h_D_var : D_var ≠ 0 := (hD_pos).ne'
    field_simp [hR.ne', h_D_var]
    dsimp only [D_var, t, u]; ring
  clear_value t u
  have hpos : 0 < (552250000 : ℝ) * (((1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * (((37 / 20 : ℝ) * R - 389 / 500))))) := by rw [hid]; positivity
  have hfin : 0 < ((1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * (((37 / 20 : ℝ) * R - 389 / 500)))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * (((37 / 20 : ℝ) * R - 389 / 500))) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma south_lo_op0_xmin_0 {R : ℝ} (hlo : (4 / 7 : ℝ) ≤ R) (hhi : R ≤ (121 / 200 : ℝ)) :
    ((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) - ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (0)) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))))) ^ 2 + (0) ^ 2) - 2 * ((R - 1)) * (0) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hr1_pos : (0 : ℝ) < ((245 / 100 : ℝ) * R - 554 / 1000) := by linarith
  have hA_pos : (0 : ℝ) < ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) := by positivity
  set t : ℝ := R - (4 / 7 : ℝ)
  set u : ℝ := (121 / 200 : ℝ) - R
  have ht : 0 ≤ t := sub_nonneg.mpr hlo
  have hu : 0 ≤ u := sub_nonneg.mpr hhi
  have hden : (0 : ℝ) < (4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2) := by positivity
  have hid : (1488205416360062500 : ℝ) * (((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) - ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (0)) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))))) ^ 2 + (0) ^ 2) - 2 * ((R - 1)) * (0)))) = (595282166544025000 : ℝ) + (428042090461998599372800000000 : ℝ) * u ^ 8 + (4019634816508235850612736000000 : ℝ) * t * u ^ 7 + (16251145261505288458234408960000 : ℝ) * t ^ 2 * u ^ 6 + (37072094578875707380341864652800 : ℝ) * t ^ 3 * u ^ 5 + (52317820743188034621653320730112 : ℝ) * t ^ 4 * u ^ 4 + (46856383503490901975184868865792 : ℝ) * t ^ 5 * u ^ 3 + (26043145405709647183268726278720 : ℝ) * t ^ 6 * u ^ 2 + (8221714951842579379313437569120 : ℝ) * t ^ 7 * u + (1129674349804374996633470175479 : ℝ) * t ^ 8 := by
    set A_var : ℝ := ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R)))
    have h_A_var : A_var ≠ 0 := (hA_pos).ne'
    field_simp [hR.ne', h_A_var]
    dsimp only [A_var, t, u]; ring
  clear_value t u
  have hpos : 0 < (1488205416360062500 : ℝ) * (((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) - ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (0)) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))))) ^ 2 + (0) ^ 2) - 2 * ((R - 1)) * (0)))) := by rw [hid]; positivity
  have hfin : 0 < ((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) - ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (0)) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))))) ^ 2 + (0) ^ 2) - 2 * ((R - 1)) * (0))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) - ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (0)) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))))) ^ 2 + (0) ^ 2) - 2 * ((R - 1)) * (0)) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma south_lo_op0_xmin_tau {R : ℝ} (hlo : (4 / 7 : ℝ) ≤ R) (hhi : R ≤ (121 / 200 : ℝ)) :
    ((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) - ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (((37 / 20 : ℝ) * R - 389 / 500))) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))))) ^ 2 + (((37 / 20 : ℝ) * R - 389 / 500)) ^ 2) - 2 * ((R - 1)) * (((37 / 20 : ℝ) * R - 389 / 500)) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hr1_pos : (0 : ℝ) < ((245 / 100 : ℝ) * R - 554 / 1000) := by linarith
  have hA_pos : (0 : ℝ) < ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) := by positivity
  set t : ℝ := R - (4 / 7 : ℝ)
  set u : ℝ := (121 / 200 : ℝ) - R
  have ht : 0 ≤ t := sub_nonneg.mpr hlo
  have hu : 0 ≤ u := sub_nonneg.mpr hhi
  have hden : (0 : ℝ) < (4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2) := by positivity
  have hid : (595282166544025000000 : ℝ) * (((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) - ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (((37 / 20 : ℝ) * R - 389 / 500))) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))))) ^ 2 + (((37 / 20 : ℝ) * R - 389 / 500)) ^ 2) - 2 * ((R - 1)) * (((37 / 20 : ℝ) * R - 389 / 500))))) = (119056433308805000000 : ℝ) + (97396547839022569462169600000000 : ℝ) * u ^ 8 + (907921721601109103181561856000000 : ℝ) * t * u ^ 7 + (3638413954607516595413374402560000 : ℝ) * t ^ 2 * u ^ 6 + (8217512033822933399441102035353600 : ℝ) * t ^ 3 * u ^ 5 + (11470713559516874429813189303136256 : ℝ) * t ^ 4 * u ^ 4 + (10152952232278567452354174397476864 : ℝ) * t ^ 5 * u ^ 3 + (5572738991277472219677285665809664 : ℝ) * t ^ 6 * u ^ 2 + (1736119411434399342100928634580320 : ℝ) * t ^ 7 * u + (235242345882228152813885659261975 : ℝ) * t ^ 8 := by
    set A_var : ℝ := ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R)))
    have h_A_var : A_var ≠ 0 := (hA_pos).ne'
    field_simp [hR.ne', h_A_var]
    dsimp only [A_var, t, u]; ring
  clear_value t u
  have hpos : 0 < (595282166544025000000 : ℝ) * (((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) - ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (((37 / 20 : ℝ) * R - 389 / 500))) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))))) ^ 2 + (((37 / 20 : ℝ) * R - 389 / 500)) ^ 2) - 2 * ((R - 1)) * (((37 / 20 : ℝ) * R - 389 / 500))))) := by rw [hid]; positivity
  have hfin : 0 < ((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) - ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (((37 / 20 : ℝ) * R - 389 / 500))) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))))) ^ 2 + (((37 / 20 : ℝ) * R - 389 / 500)) ^ 2) - 2 * ((R - 1)) * (((37 / 20 : ℝ) * R - 389 / 500)))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) - ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (((37 / 20 : ℝ) * R - 389 / 500))) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))))) ^ 2 + (((37 / 20 : ℝ) * R - 389 / 500)) ^ 2) - 2 * ((R - 1)) * (((37 / 20 : ℝ) * R - 389 / 500))) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma south_lo_op0_tlo_0 {R : ℝ} (hlo : (4 / 7 : ℝ) ≤ R) (hhi : R ≤ (121 / 200 : ℝ)) :
    ((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1 / (2 * R)))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) - ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (0)) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))))) ^ 2 + (0) ^ 2) - 2 * ((R - 1 / (2 * R))) * (0) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hr1_pos : (0 : ℝ) < ((245 / 100 : ℝ) * R - 554 / 1000) := by linarith
  have hA_pos : (0 : ℝ) < ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) := by positivity
  set t : ℝ := R - (4 / 7 : ℝ)
  set u : ℝ := (121 / 200 : ℝ) - R
  have ht : 0 ≤ t := sub_nonneg.mpr hlo
  have hu : 0 ≤ u := sub_nonneg.mpr hhi
  have hden : (0 : ℝ) < (4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2) := by positivity
  have hid : (1488205416360062500 : ℝ) * (((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1 / (2 * R)))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) - ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (0)) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))))) ^ 2 + (0) ^ 2) - 2 * ((R - 1 / (2 * R))) * (0)))) = (148820541636006250 : ℝ) + (142671238225760878592000000000 : ℝ) * u ^ 8 + (1320895271672960876118016000000 : ℝ) * t * u ^ 7 + (5261797792386256126172876800000 : ℝ) * t ^ 2 * u ^ 6 + (11819563884157428204086259507200 : ℝ) * t ^ 3 * u ^ 5 + (16414911156233754106621436774912 : ℝ) * t ^ 4 * u ^ 4 + (14458200275165952978194293140992 : ℝ) * t ^ 5 * u ^ 3 + (7897811397026405777208269038720 : ℝ) * t ^ 6 * u ^ 2 + (2448736923603662748279067178320 : ℝ) * t ^ 7 * u + (330204770679747191792872269479 : ℝ) * t ^ 8 := by
    set A_var : ℝ := ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R)))
    have h_A_var : A_var ≠ 0 := (hA_pos).ne'
    field_simp [hR.ne', h_A_var]
    dsimp only [A_var, t, u]; ring
  clear_value t u
  have hpos : 0 < (1488205416360062500 : ℝ) * (((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1 / (2 * R)))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) - ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (0)) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))))) ^ 2 + (0) ^ 2) - 2 * ((R - 1 / (2 * R))) * (0)))) := by rw [hid]; positivity
  have hfin : 0 < ((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1 / (2 * R)))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) - ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (0)) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))))) ^ 2 + (0) ^ 2) - 2 * ((R - 1 / (2 * R))) * (0))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1 / (2 * R)))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) - ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (0)) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))))) ^ 2 + (0) ^ 2) - 2 * ((R - 1 / (2 * R))) * (0)) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma south_lo_op0_tlo_tau {R : ℝ} (hlo : (4 / 7 : ℝ) ≤ R) (hhi : R ≤ (121 / 200 : ℝ)) :
    ((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1 / (2 * R)))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) - ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (((37 / 20 : ℝ) * R - 389 / 500))) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))))) ^ 2 + (((37 / 20 : ℝ) * R - 389 / 500)) ^ 2) - 2 * ((R - 1 / (2 * R))) * (((37 / 20 : ℝ) * R - 389 / 500)) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hr1_pos : (0 : ℝ) < ((245 / 100 : ℝ) * R - 554 / 1000) := by linarith
  have hA_pos : (0 : ℝ) < ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) := by positivity
  set t : ℝ := R - (4 / 7 : ℝ)
  set u : ℝ := (121 / 200 : ℝ) - R
  have ht : 0 ≤ t := sub_nonneg.mpr hlo
  have hu : 0 ≤ u := sub_nonneg.mpr hhi
  have hden : (0 : ℝ) < (4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2) := by positivity
  have hid : (595282166544025000000 : ℝ) * (((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1 / (2 * R)))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) - ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (((37 / 20 : ℝ) * R - 389 / 500))) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))))) ^ 2 + (((37 / 20 : ℝ) * R - 389 / 500)) ^ 2) - 2 * ((R - 1 / (2 * R))) * (((37 / 20 : ℝ) * R - 389 / 500))))) = (11905643330880500000 : ℝ) + (12144992829298787850649600000000 : ℝ) * u ^ 8 + (128575390635526277398265856000000 : ℝ) * t * u ^ 7 + (556750072275186655248258498560000 : ℝ) * t ^ 2 * u ^ 6 + (1319287898940574786849695177113600 : ℝ) * t ^ 3 * u ^ 5 + (1895073656500338610925908433760256 : ℝ) * t ^ 4 * u ^ 4 + (1702394057205129926453115692836864 : ℝ) * t ^ 5 * u ^ 3 + (938391454838158506557293325361664 : ℝ) * t ^ 6 * u ^ 2 + (291088509782934623492508268316320 : ℝ) * t ^ 7 * u + (38985680107287723713612843941975 : ℝ) * t ^ 8 := by
    set A_var : ℝ := ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R)))
    have h_A_var : A_var ≠ 0 := (hA_pos).ne'
    field_simp [hR.ne', h_A_var]
    dsimp only [A_var, t, u]; ring
  clear_value t u
  have hpos : 0 < (595282166544025000000 : ℝ) * (((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1 / (2 * R)))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) - ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (((37 / 20 : ℝ) * R - 389 / 500))) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))))) ^ 2 + (((37 / 20 : ℝ) * R - 389 / 500)) ^ 2) - 2 * ((R - 1 / (2 * R))) * (((37 / 20 : ℝ) * R - 389 / 500))))) := by rw [hid]; positivity
  have hfin : 0 < ((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1 / (2 * R)))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) - ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (((37 / 20 : ℝ) * R - 389 / 500))) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))))) ^ 2 + (((37 / 20 : ℝ) * R - 389 / 500)) ^ 2) - 2 * ((R - 1 / (2 * R))) * (((37 / 20 : ℝ) * R - 389 / 500)))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1 / (2 * R)))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) - ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (((37 / 20 : ℝ) * R - 389 / 500))) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))))) ^ 2 + (((37 / 20 : ℝ) * R - 389 / 500)) ^ 2) - 2 * ((R - 1 / (2 * R))) * (((37 / 20 : ℝ) * R - 389 / 500))) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma south_lo_ob_0_0 {R : ℝ} (hlo : (4 / 7 : ℝ) ≤ R) (hhi : R ≤ (121 / 200 : ℝ)) :
    ((1659 / 1250 : ℝ) * R ^ 2 + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) - ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (0)) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))))) ^ 2 + (0) ^ 2) - 2 * (0) * (0) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hr1_pos : (0 : ℝ) < ((245 / 100 : ℝ) * R - 554 / 1000) := by linarith
  have hA_pos : (0 : ℝ) < ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) := by positivity
  set t : ℝ := R - (4 / 7 : ℝ)
  set u : ℝ := (121 / 200 : ℝ) - R
  have ht : 0 ≤ t := sub_nonneg.mpr hlo
  have hu : 0 ≤ u := sub_nonneg.mpr hhi
  have hden : (0 : ℝ) < (4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2) := by positivity
  have hid : (465064192612519531250 : ℝ) * (((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * R ^ 2 + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) - ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (0)) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))))) ^ 2 + (0) ^ 2) - 2 * (0) * (0)))) = (18602567704500781250 : ℝ) + (12479460272594997248000000000000 : ℝ) * u ^ 8 + (168333259889269729085440000000000 : ℝ) * t * u ^ 7 + (833875897198826859192928000000000 : ℝ) * t ^ 2 * u ^ 6 + (2166270964819991353194036544000000 : ℝ) * t ^ 3 * u ^ 5 + (3341183488027405184637577571040000 : ℝ) * t ^ 4 * u ^ 4 + (3186719917314309639020075507795200 : ℝ) * t ^ 5 * u ^ 3 + (1853203337978725452622200665969728 : ℝ) * t ^ 6 * u ^ 2 + (604384294289282455210240225541392 : ℝ) * t ^ 7 * u + (84966252810442947317062492588547 : ℝ) * t ^ 8 := by
    set A_var : ℝ := ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R)))
    have h_A_var : A_var ≠ 0 := (hA_pos).ne'
    field_simp [hR.ne', h_A_var]
    dsimp only [A_var, t, u]; ring
  clear_value t u
  have hpos : 0 < (465064192612519531250 : ℝ) * (((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * R ^ 2 + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) - ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (0)) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))))) ^ 2 + (0) ^ 2) - 2 * (0) * (0)))) := by rw [hid]; positivity
  have hfin : 0 < ((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * R ^ 2 + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) - ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (0)) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))))) ^ 2 + (0) ^ 2) - 2 * (0) * (0))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1659 / 1250 : ℝ) * R ^ 2 + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) - ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (0)) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))))) ^ 2 + (0) ^ 2) - 2 * (0) * (0)) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma south_lo_ob_0_tau {R : ℝ} (hlo : (4 / 7 : ℝ) ≤ R) (hhi : R ≤ (121 / 200 : ℝ)) :
    ((1659 / 1250 : ℝ) * R ^ 2 + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) - ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (((37 / 20 : ℝ) * R - 389 / 500))) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))))) ^ 2 + (((37 / 20 : ℝ) * R - 389 / 500)) ^ 2) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500)) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hr1_pos : (0 : ℝ) < ((245 / 100 : ℝ) * R - 554 / 1000) := by linarith
  have hA_pos : (0 : ℝ) < ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) := by positivity
  set t : ℝ := R - (4 / 7 : ℝ)
  set u : ℝ := (121 / 200 : ℝ) - R
  have ht : 0 ≤ t := sub_nonneg.mpr hlo
  have hu : 0 ≤ u := sub_nonneg.mpr hhi
  have hden : (0 : ℝ) < (4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2) := by positivity
  have hid : (14882054163600625000000 : ℝ) * (((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * R ^ 2 + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) - ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (((37 / 20 : ℝ) * R - 389 / 500))) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))))) ^ 2 + (((37 / 20 : ℝ) * R - 389 / 500)) ^ 2) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500))))) = (1488205416360062500000 : ℝ) + (2427431809630444443402240000000000 : ℝ) * u ^ 8 + (21718743511325532842059366400000000 : ℝ) * t * u ^ 7 + (83902320548126350692953022464000000 : ℝ) * t ^ 2 * u ^ 6 + (183155820730912235299071375523840000 : ℝ) * t ^ 3 * u ^ 5 + (247468478342608472352940811992166400 : ℝ) * t ^ 4 * u ^ 4 + (212141625520322805623076107648000000 : ℝ) * t ^ 5 * u ^ 3 + (112762908451128117420226363838960896 : ℝ) * t ^ 6 * u ^ 2 + (33997922903530612282803809717320544 : ℝ) * t ^ 7 * u + (4452973512156790744462024678507879 : ℝ) * t ^ 8 := by
    set A_var : ℝ := ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R)))
    have h_A_var : A_var ≠ 0 := (hA_pos).ne'
    field_simp [hR.ne', h_A_var]
    dsimp only [A_var, t, u]; ring
  clear_value t u
  have hpos : 0 < (14882054163600625000000 : ℝ) * (((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * R ^ 2 + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) - ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (((37 / 20 : ℝ) * R - 389 / 500))) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))))) ^ 2 + (((37 / 20 : ℝ) * R - 389 / 500)) ^ 2) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500))))) := by rw [hid]; positivity
  have hfin : 0 < ((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * R ^ 2 + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) - ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (((37 / 20 : ℝ) * R - 389 / 500))) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))))) ^ 2 + (((37 / 20 : ℝ) * R - 389 / 500)) ^ 2) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500)))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1659 / 1250 : ℝ) * R ^ 2 + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) - ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (((37 / 20 : ℝ) * R - 389 / 500))) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((245 / 100 : ℝ) * R - 554 / 1000) * R))))) ^ 2 + (((37 / 20 : ℝ) * R - 389 / 500)) ^ 2) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500))) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma south_hi_pp_0_0 {R : ℝ} (hlo : (121 / 200 : ℝ) ≤ R) (hhi : R ≤ (627 / 1000 : ℝ)) :
    ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) - 2 * (0) * (0) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hD_pos : (0 : ℝ) < (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) := by linarith
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  have ht : 0 ≤ t := sub_nonneg.mpr hlo
  have hu : 0 ≤ u := sub_nonneg.mpr hhi
  have hden : (0 : ℝ) < (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) := by positivity
  have hid : (302500 : ℝ) * (((1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) - 2 * (0) * (0)))) = (30250 : ℝ) + (184441725 : ℝ) * u ^ 2 + (436173530 : ℝ) * t * u + (252534761 : ℝ) * t ^ 2 := by
    set D_var : ℝ := (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))
    have h_D_var : D_var ≠ 0 := (hD_pos).ne'
    field_simp [hR.ne', h_D_var]
    dsimp only [D_var, t, u]; ring
  clear_value t u
  have hpos : 0 < (302500 : ℝ) * (((1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) - 2 * (0) * (0)))) := by rw [hid]; positivity
  have hfin : 0 < ((1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) - 2 * (0) * (0))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) - 2 * (0) * (0)) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma south_hi_pp_0_tau {R : ℝ} (hlo : (121 / 200 : ℝ) ≤ R) (hhi : R ≤ (627 / 1000 : ℝ)) :
    ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500)) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hD_pos : (0 : ℝ) < (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) := by linarith
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  have ht : 0 ≤ t := sub_nonneg.mpr hlo
  have hu : 0 ≤ u := sub_nonneg.mpr hhi
  have hden : (0 : ℝ) < (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) := by positivity
  have hid : (2129600000 : ℝ) * (((1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500))))) = (425920000 : ℝ) + (48937489196875 : ℝ) * u ^ 3 + (167577166735375 : ℝ) * t * u ^ 2 + (188263356368385 : ℝ) * t ^ 2 * u + (69611419478693 : ℝ) * t ^ 3 := by
    set D_var : ℝ := (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))
    have h_D_var : D_var ≠ 0 := (hD_pos).ne'
    field_simp [hR.ne', h_D_var]
    dsimp only [D_var, t, u]; ring
  clear_value t u
  have hpos : 0 < (2129600000 : ℝ) * (((1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500))))) := by rw [hid]; positivity
  have hfin : 0 < ((1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500)))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500))) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma south_hi_pp_tau_tau {R : ℝ} (hlo : (121 / 200 : ℝ) ≤ R) (hhi : R ≤ (627 / 1000 : ℝ)) :
    ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * (((37 / 20 : ℝ) * R - 389 / 500)) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hD_pos : (0 : ℝ) < (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) := by linarith
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  have ht : 0 ≤ t := sub_nonneg.mpr hlo
  have hu : 0 ≤ u := sub_nonneg.mpr hhi
  have hden : (0 : ℝ) < (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) := by positivity
  have hid : (121000000 : ℝ) * (((1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * (((37 / 20 : ℝ) * R - 389 / 500))))) = (48400000 : ℝ) + (144556130625 : ℝ) * u ^ 2 + (345122673950 : ℝ) * t * u + (202284066209 : ℝ) * t ^ 2 := by
    set D_var : ℝ := (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))
    have h_D_var : D_var ≠ 0 := (hD_pos).ne'
    field_simp [hR.ne', h_D_var]
    dsimp only [D_var, t, u]; ring
  clear_value t u
  have hpos : 0 < (121000000 : ℝ) * (((1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * (((37 / 20 : ℝ) * R - 389 / 500))))) := by rw [hid]; positivity
  have hfin : 0 < ((1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * (((37 / 20 : ℝ) * R - 389 / 500)))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * (((37 / 20 : ℝ) * R - 389 / 500))) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma south_hi_op0_xmin_0 {R : ℝ} (hlo : (121 / 200 : ℝ) ≤ R) (hhi : R ≤ (627 / 1000 : ℝ)) :
    ((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (0)) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (0) ^ 2) - 2 * ((R - 1)) * (0) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hr1_pos : (0 : ℝ) < ((145 / 100 : ℝ) * R + 52 / 1000) := by linarith
  have hA_pos : (0 : ℝ) < ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) := by positivity
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  have ht : 0 ≤ t := sub_nonneg.mpr hlo
  have hu : 0 ≤ u := sub_nonneg.mpr hhi
  have hden : (0 : ℝ) < (4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2) := by positivity
  have hid : (3429742096000000 : ℝ) * (((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (0)) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (0) ^ 2) - 2 * ((R - 1)) * (0)))) = (2743793676800000 : ℝ) + (51720675695834303297187109375 : ℝ) * u ^ 8 + (446199033092374915244300625000 : ℝ) * t * u ^ 7 + (1678077067178526124054592562500 : ℝ) * t ^ 2 * u ^ 6 + (3594749623310140167307083775000 : ℝ) * t ^ 3 * u ^ 5 + (4799112723912856857586583236250 : ℝ) * t ^ 4 * u ^ 4 + (4089887682885304216265382599000 : ℝ) * t ^ 5 * u ^ 3 + (2173327705455203370662424477700 : ℝ) * t ^ 6 * u ^ 2 + (658529718337934143866320625320 : ℝ) * t ^ 7 * u + (87127885383293974419589822879 : ℝ) * t ^ 8 := by
    set A_var : ℝ := ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R)))
    have h_A_var : A_var ≠ 0 := (hA_pos).ne'
    field_simp [hR.ne', h_A_var]
    dsimp only [A_var, t, u]; ring
  clear_value t u
  have hpos : 0 < (3429742096000000 : ℝ) * (((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (0)) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (0) ^ 2) - 2 * ((R - 1)) * (0)))) := by rw [hid]; positivity
  have hfin : 0 < ((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (0)) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (0) ^ 2) - 2 * ((R - 1)) * (0))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (0)) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (0) ^ 2) - 2 * ((R - 1)) * (0)) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma south_hi_op0_xmin_tau {R : ℝ} (hlo : (121 / 200 : ℝ) ≤ R) (hhi : R ≤ (627 / 1000 : ℝ)) :
    ((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (((37 / 20 : ℝ) * R - 389 / 500))) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (((37 / 20 : ℝ) * R - 389 / 500)) ^ 2) - 2 * ((R - 1)) * (((37 / 20 : ℝ) * R - 389 / 500)) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hr1_pos : (0 : ℝ) < ((145 / 100 : ℝ) * R + 52 / 1000) := by linarith
  have hA_pos : (0 : ℝ) < ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) := by positivity
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  have ht : 0 ≤ t := sub_nonneg.mpr hlo
  have hu : 0 ≤ u := sub_nonneg.mpr hhi
  have hden : (0 : ℝ) < (4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2) := by positivity
  have hid : (1371896838400000000 : ℝ) * (((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (((37 / 20 : ℝ) * R - 389 / 500))) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (((37 / 20 : ℝ) * R - 389 / 500)) ^ 2) - 2 * ((R - 1)) * (((37 / 20 : ℝ) * R - 389 / 500))))) = (548758735360000000 : ℝ) + (10977394534202423108162099609375 : ℝ) * u ^ 8 + (93477418071905456749235840625000 : ℝ) * t * u ^ 7 + (347091540288578152116687970562500 : ℝ) * t ^ 2 * u ^ 6 + (734231320804451247833546150175000 : ℝ) * t ^ 3 * u ^ 5 + (968073739824642982652556319196250 : ℝ) * t ^ 4 * u ^ 4 + (814836972018861342325421800999000 : ℝ) * t ^ 5 * u ^ 3 + (427667312787933459101801792096900 : ℝ) * t ^ 6 * u ^ 2 + (127988536293608077484494159205800 : ℝ) * t ^ 7 * u + (16724259753457890553966459426751 : ℝ) * t ^ 8 := by
    set A_var : ℝ := ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R)))
    have h_A_var : A_var ≠ 0 := (hA_pos).ne'
    field_simp [hR.ne', h_A_var]
    dsimp only [A_var, t, u]; ring
  clear_value t u
  have hpos : 0 < (1371896838400000000 : ℝ) * (((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (((37 / 20 : ℝ) * R - 389 / 500))) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (((37 / 20 : ℝ) * R - 389 / 500)) ^ 2) - 2 * ((R - 1)) * (((37 / 20 : ℝ) * R - 389 / 500))))) := by rw [hid]; positivity
  have hfin : 0 < ((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (((37 / 20 : ℝ) * R - 389 / 500))) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (((37 / 20 : ℝ) * R - 389 / 500)) ^ 2) - 2 * ((R - 1)) * (((37 / 20 : ℝ) * R - 389 / 500)))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (((37 / 20 : ℝ) * R - 389 / 500))) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (((37 / 20 : ℝ) * R - 389 / 500)) ^ 2) - 2 * ((R - 1)) * (((37 / 20 : ℝ) * R - 389 / 500))) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma south_hi_op0_tlo_0 {R : ℝ} (hlo : (121 / 200 : ℝ) ≤ R) (hhi : R ≤ (627 / 1000 : ℝ)) :
    ((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1 / (2 * R)))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (0)) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (0) ^ 2) - 2 * ((R - 1 / (2 * R))) * (0) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hr1_pos : (0 : ℝ) < ((145 / 100 : ℝ) * R + 52 / 1000) := by linarith
  have hA_pos : (0 : ℝ) < ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) := by positivity
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  have ht : 0 ≤ t := sub_nonneg.mpr hlo
  have hu : 0 ≤ u := sub_nonneg.mpr hhi
  have hden : (0 : ℝ) < (4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2) := by positivity
  have hid : (3429742096000000 : ℝ) * (((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1 / (2 * R)))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (0)) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (0) ^ 2) - 2 * ((R - 1 / (2 * R))) * (0)))) = (685948419200000 : ℝ) + (16235111292438337521405859375 : ℝ) * u ^ 8 + (136028815646050775664738125000 : ℝ) * t * u ^ 7 + (497485938817945684170905062500 : ℝ) * t ^ 2 * u ^ 6 + (1037417520826900108518971275000 : ℝ) * t ^ 3 * u ^ 5 + (1349345714383088900074809236250 : ℝ) * t ^ 4 * u ^ 4 + (1121084010269923228880514299000 : ℝ) * t ^ 5 * u ^ 3 + (581085881370592805796455337700 : ℝ) * t ^ 6 * u ^ 2 + (171809799042074627848251189320 : ℝ) * t ^ 7 * u + (22187499920844200686188976879 : ℝ) * t ^ 8 := by
    set A_var : ℝ := ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R)))
    have h_A_var : A_var ≠ 0 := (hA_pos).ne'
    field_simp [hR.ne', h_A_var]
    dsimp only [A_var, t, u]; ring
  clear_value t u
  have hpos : 0 < (3429742096000000 : ℝ) * (((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1 / (2 * R)))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (0)) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (0) ^ 2) - 2 * ((R - 1 / (2 * R))) * (0)))) := by rw [hid]; positivity
  have hfin : 0 < ((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1 / (2 * R)))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (0)) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (0) ^ 2) - 2 * ((R - 1 / (2 * R))) * (0))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1 / (2 * R)))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (0)) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (0) ^ 2) - 2 * ((R - 1 / (2 * R))) * (0)) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma south_hi_op0_tlo_tau {R : ℝ} (hlo : (121 / 200 : ℝ) ≤ R) (hhi : R ≤ (627 / 1000 : ℝ)) :
    ((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1 / (2 * R)))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (((37 / 20 : ℝ) * R - 389 / 500))) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (((37 / 20 : ℝ) * R - 389 / 500)) ^ 2) - 2 * ((R - 1 / (2 * R))) * (((37 / 20 : ℝ) * R - 389 / 500)) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hr1_pos : (0 : ℝ) < ((145 / 100 : ℝ) * R + 52 / 1000) := by linarith
  have hA_pos : (0 : ℝ) < ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) := by positivity
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  have ht : 0 ≤ t := sub_nonneg.mpr hlo
  have hu : 0 ≤ u := sub_nonneg.mpr hhi
  have hden : (0 : ℝ) < (4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2) := by positivity
  have hid : (1371896838400000000 : ℝ) * (((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1 / (2 * R)))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (((37 / 20 : ℝ) * R - 389 / 500))) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (((37 / 20 : ℝ) * R - 389 / 500)) ^ 2) - 2 * ((R - 1 / (2 * R))) * (((37 / 20 : ℝ) * R - 389 / 500))))) = (82313810304000000 : ℝ) + (1663542381233835889052724609375 : ℝ) * u ^ 8 + (13750093150952261838927090625000 : ℝ) * t * u ^ 7 + (49467580350547486545293720562500 : ℝ) * t ^ 2 * u ^ 6 + (101186101381857551521602000175000 : ℝ) * t ^ 3 * u ^ 5 + (128720923865543141052375879196250 : ℝ) * t ^ 4 * u ^ 4 + (104279375542855626632570526999000 : ℝ) * t ^ 5 * u ^ 3 + (52532661163555470804100074096900 : ℝ) * t ^ 6 * u ^ 2 + (15043553345377700437704404245800 : ℝ) * t ^ 7 * u + (1874415660151989280458313466751 : ℝ) * t ^ 8 := by
    set A_var : ℝ := ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R)))
    have h_A_var : A_var ≠ 0 := (hA_pos).ne'
    field_simp [hR.ne', h_A_var]
    dsimp only [A_var, t, u]; ring
  clear_value t u
  have hpos : 0 < (1371896838400000000 : ℝ) * (((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1 / (2 * R)))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (((37 / 20 : ℝ) * R - 389 / 500))) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (((37 / 20 : ℝ) * R - 389 / 500)) ^ 2) - 2 * ((R - 1 / (2 * R))) * (((37 / 20 : ℝ) * R - 389 / 500))))) := by rw [hid]; positivity
  have hfin : 0 < ((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1 / (2 * R)))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (((37 / 20 : ℝ) * R - 389 / 500))) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (((37 / 20 : ℝ) * R - 389 / 500)) ^ 2) - 2 * ((R - 1 / (2 * R))) * (((37 / 20 : ℝ) * R - 389 / 500)))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1 / (2 * R)))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (((37 / 20 : ℝ) * R - 389 / 500))) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (((37 / 20 : ℝ) * R - 389 / 500)) ^ 2) - 2 * ((R - 1 / (2 * R))) * (((37 / 20 : ℝ) * R - 389 / 500))) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma south_hi_ob_0_0 {R : ℝ} (hlo : (121 / 200 : ℝ) ≤ R) (hhi : R ≤ (627 / 1000 : ℝ)) :
    ((1659 / 1250 : ℝ) * R ^ 2 + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (0)) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (0) ^ 2) - 2 * (0) * (0) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hr1_pos : (0 : ℝ) < ((145 / 100 : ℝ) * R + 52 / 1000) := by linarith
  have hA_pos : (0 : ℝ) < ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) := by positivity
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  have ht : 0 ≤ t := sub_nonneg.mpr hlo
  have hu : 0 ≤ u := sub_nonneg.mpr hhi
  have hden : (0 : ℝ) < (4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2) := by positivity
  have hid : (1071794405000000000 : ℝ) * (((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * R ^ 2 + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (0)) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (0) ^ 2) - 2 * (0) * (0)))) = (107179440500000000 : ℝ) + (4617856623501441017402854296875 : ℝ) * u ^ 8 + (39579533498855532443894790625000 : ℝ) * t * u ^ 7 + (147725184949323083925970961312500 : ℝ) * t ^ 2 * u ^ 6 + (313754367681371651617666847575000 : ℝ) * t ^ 3 * u ^ 5 + (414926054486762391598582487381250 : ℝ) * t ^ 4 * u ^ 4 + (349980488274791050031537462663000 : ℝ) * t ^ 5 * u ^ 3 + (183921257716068168708403745648500 : ℝ) * t ^ 6 * u ^ 2 + (55070658333700565624504987713640 : ℝ) * t ^ 7 * u + (7194694013043648320622755064043 : ℝ) * t ^ 8 := by
    set A_var : ℝ := ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R)))
    have h_A_var : A_var ≠ 0 := (hA_pos).ne'
    field_simp [hR.ne', h_A_var]
    dsimp only [A_var, t, u]; ring
  clear_value t u
  have hpos : 0 < (1071794405000000000 : ℝ) * (((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * R ^ 2 + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (0)) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (0) ^ 2) - 2 * (0) * (0)))) := by rw [hid]; positivity
  have hfin : 0 < ((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * R ^ 2 + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (0)) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (0) ^ 2) - 2 * (0) * (0))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1659 / 1250 : ℝ) * R ^ 2 + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (0)) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (0) ^ 2) - 2 * (0) * (0)) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma south_hi_ob_0_tau {R : ℝ} (hlo : (121 / 200 : ℝ) ≤ R) (hhi : R ≤ (627 / 1000 : ℝ)) :
    ((1659 / 1250 : ℝ) * R ^ 2 + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (((37 / 20 : ℝ) * R - 389 / 500))) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (((37 / 20 : ℝ) * R - 389 / 500)) ^ 2) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500)) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hr1_pos : (0 : ℝ) < ((145 / 100 : ℝ) * R + 52 / 1000) := by linarith
  have hA_pos : (0 : ℝ) < ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) := by positivity
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  have ht : 0 ≤ t := sub_nonneg.mpr hlo
  have hu : 0 ≤ u := sub_nonneg.mpr hhi
  have hden : (0 : ℝ) < (4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2) := by positivity
  have hid : (34297420960000000000 : ℝ) * (((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * R ^ 2 + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (((37 / 20 : ℝ) * R - 389 / 500))) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (((37 / 20 : ℝ) * R - 389 / 500)) ^ 2) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500))))) = (6859484192000000000 : ℝ) + (240029228602323713912945780859375 : ℝ) * u ^ 8 + (1974973559888559787132756190625000 : ℝ) * t * u ^ 7 + (7087963234844030230918335213562500 : ℝ) * t ^ 2 * u ^ 6 + (14492416409167134858214643201775000 : ℝ) * t ^ 3 * u ^ 5 + (18464516598211593402573170394856250 : ℝ) * t ^ 4 * u ^ 4 + (15010724991910893747986537955191000 : ℝ) * t ^ 5 * u ^ 3 + (7603417245451392333675121237874500 : ℝ) * t ^ 6 * u ^ 2 + (2193842180284108706248714327901480 : ℝ) * t ^ 7 * u + (276030834139386938429933957931151 : ℝ) * t ^ 8 := by
    set A_var : ℝ := ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R)))
    have h_A_var : A_var ≠ 0 := (hA_pos).ne'
    field_simp [hR.ne', h_A_var]
    dsimp only [A_var, t, u]; ring
  clear_value t u
  have hpos : 0 < (34297420960000000000 : ℝ) * (((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * R ^ 2 + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (((37 / 20 : ℝ) * R - 389 / 500))) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (((37 / 20 : ℝ) * R - 389 / 500)) ^ 2) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500))))) := by rw [hid]; positivity
  have hfin : 0 < ((4 * R ^ 2) * (4 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2)) * (1 - (((1659 / 1250 : ℝ) * R ^ 2 + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (((37 / 20 : ℝ) * R - 389 / 500))) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (((37 / 20 : ℝ) * R - 389 / 500)) ^ 2) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500)))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1659 / 1250 : ℝ) * R ^ 2 + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * (((37 / 20 : ℝ) * R - 389 / 500))) / (2 * ((4 / 5 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (((37 / 20 : ℝ) * R - 389 / 500)) ^ 2) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500))) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma south_hi_bn_p0_xmin {R : ℝ} (hlo : (121 / 200 : ℝ) ≤ R) (hhi : R ≤ (627 / 1000 : ℝ)) :
    2 * ((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1))) + (409 / 1250 : ℝ) * (-2 * (-21 / 100 : ℝ) * ((R - 1)) + (-21 / 100 : ℝ) ^ 2)) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  have ht : 0 ≤ t := sub_nonneg.mpr hlo
  have hu : 0 ≤ u := sub_nonneg.mpr hhi
  have hid : (302500 : ℝ) * (1 - (2 * ((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1))) + (409 / 1250 : ℝ) * (-2 * (-21 / 100 : ℝ) * ((R - 1)) + (-21 / 100 : ℝ) ^ 2)))) = (90750 : ℝ) + (228470725 : ℝ) * u ^ 2 + (481995710 : ℝ) * t * u + (252722029 : ℝ) * t ^ 2 := by dsimp only [t, u]; ring
  clear_value t u
  have hpos : 0 < (302500 : ℝ) * (1 - (2 * ((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1))) + (409 / 1250 : ℝ) * (-2 * (-21 / 100 : ℝ) * ((R - 1)) + (-21 / 100 : ℝ) ^ 2)))) := by rw [hid]; positivity
  have hfin : 0 < 1 - (2 * ((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((R - 1))) + (409 / 1250 : ℝ) * (-2 * (-21 / 100 : ℝ) * ((R - 1)) + (-21 / 100 : ℝ) ^ 2))) := pos_of_mul_pos_right hpos (by positivity)
  linarith

private lemma south_hi_bn_p0_xm {R : ℝ} (hlo : (121 / 200 : ℝ) ≤ R) (hhi : R ≤ (627 / 1000 : ℝ)) :
    2 * ((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((-21 / 100 : ℝ))) + (409 / 1250 : ℝ) * (-2 * (-21 / 100 : ℝ) * ((-21 / 100 : ℝ)) + (-21 / 100 : ℝ) ^ 2)) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  have ht : 0 ≤ t := sub_nonneg.mpr hlo
  have hu : 0 ≤ u := sub_nonneg.mpr hhi
  have hid : (302500 : ℝ) * (1 - (2 * ((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((-21 / 100 : ℝ))) + (409 / 1250 : ℝ) * (-2 * (-21 / 100 : ℝ) * ((-21 / 100 : ℝ)) + (-21 / 100 : ℝ) ^ 2)))) = (3025 : ℝ) + (6574275 : ℝ) * u ^ 2 + (72640290 : ℝ) * t * u + (66868971 : ℝ) * t ^ 2 := by dsimp only [t, u]; ring
  clear_value t u
  have hpos : 0 < (302500 : ℝ) * (1 - (2 * ((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((-21 / 100 : ℝ))) + (409 / 1250 : ℝ) * (-2 * (-21 / 100 : ℝ) * ((-21 / 100 : ℝ)) + (-21 / 100 : ℝ) ^ 2)))) := by rw [hid]; positivity
  have hfin : 0 < 1 - (2 * ((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * ((-21 / 100 : ℝ))) + (409 / 1250 : ℝ) * (-2 * (-21 / 100 : ℝ) * ((-21 / 100 : ℝ)) + (-21 / 100 : ℝ) ^ 2))) := pos_of_mul_pos_right hpos (by positivity)
  linarith

private lemma south_hi_bn_U_xm {R : ℝ} (hlo : (121 / 200 : ℝ) ≤ R) (hhi : R ≤ (627 / 1000 : ℝ)) :
    2 * ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + (-21 / 100 : ℝ) ^ 2 + (((17 / 20 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 + 2 * ((R - 1 / (2 * R)) - (-21 / 100 : ℝ)) * ((-21 / 100 : ℝ))) / (2 * ((17 / 20 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + ((-21 / 100 : ℝ)) ^ 2) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hr1_pos : (0 : ℝ) < ((145 / 100 : ℝ) * R + 52 / 1000) := by linarith
  have hA_pos : (0 : ℝ) < ((17 / 20 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) := by positivity
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  have ht : 0 ≤ t := sub_nonneg.mpr hlo
  have hu : 0 ≤ u := sub_nonneg.mpr hhi
  have hden : (0 : ℝ) < (4 * R ^ 2) * (4 * ((17 / 20 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2) := by positivity
  have hid : (70862440000000000 : ℝ) * (((4 * R ^ 2) * (4 * ((17 / 20 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2)) * (1 - (2 * ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + (-21 / 100 : ℝ) ^ 2 + (((17 / 20 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 + 2 * ((R - 1 / (2 * R)) - (-21 / 100 : ℝ)) * ((-21 / 100 : ℝ))) / (2 * ((17 / 20 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + ((-21 / 100 : ℝ)) ^ 2)))) = (7086244000000000 : ℝ) + (114356013609223145029171875 : ℝ) * u ^ 6 + (1067786081235164771747068750 : ℝ) * t * u ^ 5 + (3655173534040633549801958125 : ℝ) * t ^ 2 * u ^ 4 + (6231006975786160918676090500 : ℝ) * t ^ 3 * u ^ 3 + (5724518642913560704905998925 : ℝ) * t ^ 4 * u ^ 2 + (2723916342791112110749260750 : ℝ) * t ^ 5 * u + (528661209922267400948261507 : ℝ) * t ^ 6 := by
    set A_var : ℝ := ((17 / 20 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R)))
    have h_A_var : A_var ≠ 0 := (hA_pos).ne'
    field_simp [hR.ne', h_A_var]
    dsimp only [A_var, t, u]; ring
  clear_value t u
  have hpos : 0 < (70862440000000000 : ℝ) * (((4 * R ^ 2) * (4 * ((17 / 20 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2)) * (1 - (2 * ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + (-21 / 100 : ℝ) ^ 2 + (((17 / 20 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 + 2 * ((R - 1 / (2 * R)) - (-21 / 100 : ℝ)) * ((-21 / 100 : ℝ))) / (2 * ((17 / 20 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + ((-21 / 100 : ℝ)) ^ 2)))) := by rw [hid]; positivity
  have hfin : 0 < ((4 * R ^ 2) * (4 * ((17 / 20 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2)) * (1 - (2 * ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + (-21 / 100 : ℝ) ^ 2 + (((17 / 20 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 + 2 * ((R - 1 / (2 * R)) - (-21 / 100 : ℝ)) * ((-21 / 100 : ℝ))) / (2 * ((17 / 20 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + ((-21 / 100 : ℝ)) ^ 2))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (2 * ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + (-21 / 100 : ℝ) ^ 2 + (((17 / 20 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 + 2 * ((R - 1 / (2 * R)) - (-21 / 100 : ℝ)) * ((-21 / 100 : ℝ))) / (2 * ((17 / 20 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + ((-21 / 100 : ℝ)) ^ 2)) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma south_hi_bn_U_0 {R : ℝ} (hlo : (121 / 200 : ℝ) ≤ R) (hhi : R ≤ (627 / 1000 : ℝ)) :
    2 * ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + (-21 / 100 : ℝ) ^ 2 + (((17 / 20 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 + 2 * ((R - 1 / (2 * R)) - (-21 / 100 : ℝ)) * (0)) / (2 * ((17 / 20 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (0) ^ 2) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hr1_pos : (0 : ℝ) < ((145 / 100 : ℝ) * R + 52 / 1000) := by linarith
  have hA_pos : (0 : ℝ) < ((17 / 20 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) := by positivity
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  have ht : 0 ≤ t := sub_nonneg.mpr hlo
  have hu : 0 ≤ u := sub_nonneg.mpr hhi
  have hden : (0 : ℝ) < 4 * ((17 / 20 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 := by positivity
  have hid : (23425600000000 : ℝ) * ((4 * ((17 / 20 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2) * (1 - (2 * ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + (-21 / 100 : ℝ) ^ 2 + (((17 / 20 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 + 2 * ((R - 1 / (2 * R)) - (-21 / 100 : ℝ)) * (0)) / (2 * ((17 / 20 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (0) ^ 2)))) = (4685120000000 : ℝ) + (26651599940667213125 : ℝ) * u ^ 4 + (138370100462646483500 : ℝ) * t * u ^ 3 + (256224317092813904350 : ℝ) * t ^ 2 * u ^ 2 + (203957801420974860460 : ℝ) * t ^ 3 * u + (59452046335748496901 : ℝ) * t ^ 4 := by
    set A_var : ℝ := ((17 / 20 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R)))
    have h_A_var : A_var ≠ 0 := (hA_pos).ne'
    field_simp [hR.ne', h_A_var]
    dsimp only [A_var, t, u]; ring
  clear_value t u
  have hpos : 0 < (23425600000000 : ℝ) * ((4 * ((17 / 20 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2) * (1 - (2 * ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + (-21 / 100 : ℝ) ^ 2 + (((17 / 20 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 + 2 * ((R - 1 / (2 * R)) - (-21 / 100 : ℝ)) * (0)) / (2 * ((17 / 20 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (0) ^ 2)))) := by rw [hid]; positivity
  have hfin : 0 < (4 * ((17 / 20 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2) * (1 - (2 * ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + (-21 / 100 : ℝ) ^ 2 + (((17 / 20 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 + 2 * ((R - 1 / (2 * R)) - (-21 / 100 : ℝ)) * (0)) / (2 * ((17 / 20 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (0) ^ 2))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (2 * ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + (-21 / 100 : ℝ) ^ 2 + (((17 / 20 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 + 2 * ((R - 1 / (2 * R)) - (-21 / 100 : ℝ)) * (0)) / (2 * ((17 / 20 : ℝ) * R + ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (0) ^ 2)) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma wpn_lo_b_0_tlo {R s : ℝ} (hRlo : (4 / 7 : ℝ) ≤ R) (hRhi : R ≤ (121 / 200 : ℝ))
    (hslo : (7 / 25 : ℝ) ≤ s) (hshi : s ≤ (29 / 50 : ℝ)) :
    ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) - 2 * (0) * ((R - 1 / (2 * R))) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hs : (0 : ℝ) < s := by linarith
  have hr1_pos : (0 : ℝ) < ((245 / 100 : ℝ) * R - 554 / 1000) := by linarith
  have hD_pos : (0 : ℝ) < (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) := by positivity
  set t : ℝ := R - (4 / 7 : ℝ)
  set u : ℝ := (121 / 200 : ℝ) - R
  set p : ℝ := s - (7 / 25 : ℝ)
  set q : ℝ := (29 / 50 : ℝ) - s
  have ht : 0 ≤ t := sub_nonneg.mpr hRlo
  have hu : 0 ≤ u := sub_nonneg.mpr hRhi
  have hp : 0 ≤ p := sub_nonneg.mpr hslo
  have hq : 0 ≤ q := sub_nonneg.mpr hshi
  have hden : (0 : ℝ) < (4 * R ^ 2) * (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) := by positivity
  have hid : (30961575945 : ℝ) * (((4 * R ^ 2) * (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) - 2 * (0) * ((R - 1 / (2 * R)))))) = (6192315189 : ℝ) + u ^ 5 * ((1758500753049600000 : ℝ) * q ^ 2 + (4973079996595200000 : ℝ) * p * q + (2963865451545600000 : ℝ) * p ^ 2) + t * u ^ 4 * ((9325070352771532800 : ℝ) * q ^ 2 + (26025883816698393600 : ℝ) * p * q + (15297178370870860800 : ℝ) * p ^ 2) + t ^ 2 * u ^ 3 * ((19718602401306059776 : ℝ) * q ^ 2 + (54367808896333517312 : ℝ) * p * q + (31525891888423937536 : ℝ) * p ^ 2) + t ^ 3 * u ^ 2 * ((20787462643673088384 : ℝ) * q ^ 2 + (56670150460764700608 : ℝ) * p * q + (32427057673823932224 : ℝ) * p ^ 2) + t ^ 4 * u * ((10926747729400222496 : ℝ) * q ^ 2 + (29474563184183112352 : ℝ) * p * q + (16645527575834089856 : ℝ) * p ^ 2) + t ^ 5 * ((2291315999343163464 : ℝ) * q ^ 2 + (6119412000889578468 : ℝ) * p * q + (3411044960317775004 : ℝ) * p ^ 2) := by
    set D_var : ℝ := (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))
    have h_D_var : D_var ≠ 0 := (hD_pos).ne'
    field_simp [hR.ne', h_D_var]
    dsimp only [D_var, t, u, p, q]; ring
  clear_value t u p q
  have hpos : 0 < (30961575945 : ℝ) * (((4 * R ^ 2) * (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) - 2 * (0) * ((R - 1 / (2 * R)))))) := by rw [hid]; positivity
  have hfin : 0 < ((4 * R ^ 2) * (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) - 2 * (0) * ((R - 1 / (2 * R))))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) - 2 * (0) * ((R - 1 / (2 * R)))) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma wpn_lo_b_0_0 {R s : ℝ} (hRlo : (4 / 7 : ℝ) ≤ R) (hRhi : R ≤ (121 / 200 : ℝ))
    (hslo : (7 / 25 : ℝ) ≤ s) (hshi : s ≤ (29 / 50 : ℝ)) :
    ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) - 2 * (0) * (0) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hs : (0 : ℝ) < s := by linarith
  have hr1_pos : (0 : ℝ) < ((245 / 100 : ℝ) * R - 554 / 1000) := by linarith
  have hD_pos : (0 : ℝ) < (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) := by positivity
  set t : ℝ := R - (4 / 7 : ℝ)
  set u : ℝ := (121 / 200 : ℝ) - R
  set p : ℝ := s - (7 / 25 : ℝ)
  set q : ℝ := (29 / 50 : ℝ) - s
  have ht : 0 ≤ t := sub_nonneg.mpr hRlo
  have hu : 0 ≤ u := sub_nonneg.mpr hRhi
  have hp : 0 ≤ p := sub_nonneg.mpr hslo
  have hq : 0 ≤ q := sub_nonneg.mpr hshi
  have hden : (0 : ℝ) < (4 * R ^ 2) * (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) := by positivity
  have hid : (19350984965625 : ℝ) * (((4 * R ^ 2) * (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) - 2 * (0) * (0)))) = (3870196993125 : ℝ) + u ^ 5 * ((1100732563884800000000 : ℝ) * q ^ 2 + (2754319256617600000000 : ℝ) * p * q + (1373665596732800000000 : ℝ) * p ^ 2) + t * u ^ 4 * ((5835830567603680000000 : ℝ) * q ^ 2 + (14642406549994160000000 : ℝ) * p * q + (7355707893790480000000 : ℝ) * p ^ 2) + t ^ 2 * u ^ 3 * ((12338113854829723520000 : ℝ) * q ^ 2 + (31015517679567682240000 : ℝ) * p * q + (15664069966607558720000 : ℝ) * p ^ 2) + t ^ 3 * u ^ 2 * ((13004859236872794972800 : ℝ) * q ^ 2 + (32728410079507404673600 : ℝ) * p * q + (16588537953130253700800 : ℝ) * p ^ 2) + t ^ 4 * u * ((6834944080773699253888 : ℝ) * q ^ 2 + (17207971467703445196656 : ℝ) * p * q + (8739096675338339182768 : ℝ) * p ^ 2) + t ^ 5 * ((1433099517234316233316 : ℝ) * q ^ 2 + (3606987684935884256042 : ℝ) * p * q + (1832582974378376827726 : ℝ) * p ^ 2) := by
    set D_var : ℝ := (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))
    have h_D_var : D_var ≠ 0 := (hD_pos).ne'
    field_simp [hR.ne', h_D_var]
    dsimp only [D_var, t, u, p, q]; ring
  clear_value t u p q
  have hpos : 0 < (19350984965625 : ℝ) * (((4 * R ^ 2) * (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) - 2 * (0) * (0)))) := by rw [hid]; positivity
  have hfin : 0 < ((4 * R ^ 2) * (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) - 2 * (0) * (0))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) - 2 * (0) * (0)) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma wpn_lo_p0_0_ymin {R s : ℝ} (hRlo : (4 / 7 : ℝ) ≤ R) (hRhi : R ≤ (121 / 200 : ℝ))
    (hslo : (7 / 25 : ℝ) ≤ s) (hshi : s ≤ (29 / 50 : ℝ)) :
    ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) - 2 * (0) * (R - 1) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hs : (0 : ℝ) < s := by linarith
  have hr1_pos : (0 : ℝ) < ((245 / 100 : ℝ) * R - 554 / 1000) := by linarith
  have hD_pos : (0 : ℝ) < (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) := by positivity
  set t : ℝ := R - (4 / 7 : ℝ)
  set u : ℝ := (121 / 200 : ℝ) - R
  set p : ℝ := s - (7 / 25 : ℝ)
  set q : ℝ := (29 / 50 : ℝ) - s
  have ht : 0 ≤ t := sub_nonneg.mpr hRlo
  have hu : 0 ≤ u := sub_nonneg.mpr hRhi
  have hp : 0 ≤ p := sub_nonneg.mpr hslo
  have hq : 0 ≤ q := sub_nonneg.mpr hshi
  have hden : (0 : ℝ) < (4 * R ^ 2) * (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) := by positivity
  have hid : (61923151890 : ℝ) * (((4 * R ^ 2) * (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) - 2 * (0) * (R - 1)))) = (18576945567 : ℝ) + u ^ 5 * ((6334031423713280000 : ℝ) * q ^ 2 + (18464979228559360000 : ℝ) * p * q + (12097519299246080000 : ℝ) * p ^ 2) + t * u ^ 4 * ((35477423452512563200 : ℝ) * q ^ 2 + (101856351262310758400 : ℝ) * p * q + (66177112492934195200 : ℝ) * p ^ 2) + t ^ 2 * u ^ 3 * ((78917748667270295552 : ℝ) * q ^ 2 + (223645996291205146624 : ℝ) * p * q + (144244832061607811072 : ℝ) * p ^ 2) + t ^ 3 * u ^ 2 * ((87238493642033178368 : ℝ) * q ^ 2 + (244473991807771820416 : ℝ) * p * q + (156661140400355282048 : ℝ) * p ^ 2) + t ^ 4 * u * ((47963206923397865792 : ℝ) * q ^ 2 + (133110301900032474304 : ℝ) * p * q + (84808507393393008512 : ℝ) * p ^ 2) + t ^ 5 * ((10499066143899504528 : ℝ) * q ^ 2 + (28890922752196088136 : ℝ) * p * q + (18312598039375303608 : ℝ) * p ^ 2) := by
    set D_var : ℝ := (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))
    have h_D_var : D_var ≠ 0 := (hD_pos).ne'
    field_simp [hR.ne', h_D_var]
    dsimp only [D_var, t, u, p, q]; ring
  clear_value t u p q
  have hpos : 0 < (61923151890 : ℝ) * (((4 * R ^ 2) * (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) - 2 * (0) * (R - 1)))) := by rw [hid]; positivity
  have hfin : 0 < ((4 * R ^ 2) * (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) - 2 * (0) * (R - 1))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) - 2 * (0) * (R - 1)) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma wpn_lo_b_tau_tlo {R s : ℝ} (hRlo : (4 / 7 : ℝ) ≤ R) (hRhi : R ≤ (121 / 200 : ℝ))
    (hslo : (7 / 25 : ℝ) ≤ s) (hshi : s ≤ (29 / 50 : ℝ)) :
    ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * ((R - 1 / (2 * R))) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hs : (0 : ℝ) < s := by linarith
  have hr1_pos : (0 : ℝ) < ((245 / 100 : ℝ) * R - 554 / 1000) := by linarith
  have hD_pos : (0 : ℝ) < (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) := by positivity
  set t : ℝ := R - (4 / 7 : ℝ)
  set u : ℝ := (121 / 200 : ℝ) - R
  set p : ℝ := s - (7 / 25 : ℝ)
  set q : ℝ := (29 / 50 : ℝ) - s
  have ht : 0 ≤ t := sub_nonneg.mpr hRlo
  have hu : 0 ≤ u := sub_nonneg.mpr hRhi
  have hp : 0 ≤ p := sub_nonneg.mpr hslo
  have hq : 0 ≤ q := sub_nonneg.mpr hshi
  have hden : (0 : ℝ) < (4 * R ^ 2) * (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) := by positivity
  have hid : (3096157594500 / 7 : ℝ) * (((4 * R ^ 2) * (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * ((R - 1 / (2 * R)))))) = (30961575945 : ℝ) + u ^ 5 * ((8932336180961280000 : ℝ) * q ^ 2 + (24509352008847360000 : ℝ) * p * q + (11995390227886080000 : ℝ) * p ^ 2) + t * u ^ 4 * ((49946913340215910400 : ℝ) * q ^ 2 + (130791732915131084800 : ℝ) * p * q + (60792889674115174400 : ℝ) * p ^ 2) + t ^ 2 * u ^ 3 * ((112237516292964167168 : ℝ) * q ^ 2 + (281512878209683273216 : ℝ) * p * q + (124656581822383106048 : ℝ) * p ^ 2) + t ^ 3 * u ^ 2 * ((126487612634124708736 : ℝ) * q ^ 2 + (305156214316276404032 : ℝ) * p * q + (129302456778327695296 : ℝ) * p ^ 2) + t ^ 4 * u * ((71390889535163024680 : ℝ) * q ^ 2 + (166398575460403957160 : ℝ) * p * q + (67832144797400932480 : ℝ) * p ^ 2) + t ^ 5 * ((16126196548219987950 : ℝ) * q ^ 2 + (36472798596048659775 : ℝ) * p * q + (14388730030276671825 : ℝ) * p ^ 2) := by
    set D_var : ℝ := (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))
    have h_D_var : D_var ≠ 0 := (hD_pos).ne'
    field_simp [hR.ne', h_D_var]
    dsimp only [D_var, t, u, p, q]; ring
  clear_value t u p q
  have hpos : 0 < (3096157594500 / 7 : ℝ) * (((4 * R ^ 2) * (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * ((R - 1 / (2 * R)))))) := by rw [hid]; positivity
  have hfin : 0 < ((4 * R ^ 2) * (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * ((R - 1 / (2 * R))))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * ((R - 1 / (2 * R)))) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma wpn_lo_b_tau_0 {R s : ℝ} (hRlo : (4 / 7 : ℝ) ≤ R) (hRhi : R ≤ (121 / 200 : ℝ))
    (hslo : (7 / 25 : ℝ) ≤ s) (hshi : s ≤ (29 / 50 : ℝ)) :
    ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * (0) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hs : (0 : ℝ) < s := by linarith
  have hr1_pos : (0 : ℝ) < ((245 / 100 : ℝ) * R - 554 / 1000) := by linarith
  have hD_pos : (0 : ℝ) < (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) := by positivity
  set t : ℝ := R - (4 / 7 : ℝ)
  set u : ℝ := (121 / 200 : ℝ) - R
  set p : ℝ := s - (7 / 25 : ℝ)
  set q : ℝ := (29 / 50 : ℝ) - s
  have ht : 0 ≤ t := sub_nonneg.mpr hRlo
  have hu : 0 ≤ u := sub_nonneg.mpr hRhi
  have hp : 0 ≤ p := sub_nonneg.mpr hslo
  have hq : 0 ≤ q := sub_nonneg.mpr hshi
  have hden : (0 : ℝ) < (4 * R ^ 2) * (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) := by positivity
  have hid : (77403939862500 : ℝ) * (((4 * R ^ 2) * (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * (0)))) = (15480787972500 : ℝ) + u ^ 5 * ((5527545545575424000000 : ℝ) * q ^ 2 + (13055310112434688000000 : ℝ) * p * q + (6408080182859264000000 : ℝ) * p ^ 2) + t * u ^ 4 * ((29160742067035192320000 : ℝ) * q ^ 2 + (68859583633556835840000 : ℝ) * p * q + (33895369212121643520000 : ℝ) * p ^ 2) + t ^ 2 * u ^ 3 * ((61324304387043536294400 : ℝ) * q ^ 2 + (144635618291589057292800 : ℝ) * p * q + (71257978472023920998400 : ℝ) * p ^ 2) + t ^ 3 * u ^ 2 * ((64264765538518553232000 : ℝ) * q ^ 2 + (151236914954318925144000 : ℝ) * p * q + (74432097857782947912000 : ℝ) * p ^ 2) + t ^ 4 * u * ((33560722425830458158552 : ℝ) * q ^ 2 + (78725089198815627177624 : ℝ) * p * q + (38628643926619541979072 : ℝ) * p ^ 2) + t ^ 5 * ((6987043887858911334514 : ℝ) * q ^ 2 + (16319453041525460479793 : ℝ) * p * q + (7967188380373784365279 : ℝ) * p ^ 2) := by
    set D_var : ℝ := (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))
    have h_D_var : D_var ≠ 0 := (hD_pos).ne'
    field_simp [hR.ne', h_D_var]
    dsimp only [D_var, t, u, p, q]; ring
  clear_value t u p q
  have hpos : 0 < (77403939862500 : ℝ) * (((4 * R ^ 2) * (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * (0)))) := by rw [hid]; positivity
  have hfin : 0 < ((4 * R ^ 2) * (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * (0))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * (0)) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma wpn_lo_p0_tau_ymin {R s : ℝ} (hRlo : (4 / 7 : ℝ) ≤ R) (hRhi : R ≤ (121 / 200 : ℝ))
    (hslo : (7 / 25 : ℝ) ≤ s) (hshi : s ≤ (29 / 50 : ℝ)) :
    ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * (R - 1) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hs : (0 : ℝ) < s := by linarith
  have hr1_pos : (0 : ℝ) < ((245 / 100 : ℝ) * R - 554 / 1000) := by linarith
  have hD_pos : (0 : ℝ) < (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) := by positivity
  set t : ℝ := R - (4 / 7 : ℝ)
  set u : ℝ := (121 / 200 : ℝ) - R
  set p : ℝ := s - (7 / 25 : ℝ)
  set q : ℝ := (29 / 50 : ℝ) - s
  have ht : 0 ≤ t := sub_nonneg.mpr hRlo
  have hu : 0 ≤ u := sub_nonneg.mpr hRhi
  have hp : 0 ≤ p := sub_nonneg.mpr hslo
  have hq : 0 ≤ q := sub_nonneg.mpr hshi
  have hden : (0 : ℝ) < (4 * R ^ 2) * (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) := by positivity
  have hid : (3096157594500 : ℝ) * (((4 * R ^ 2) * (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * (R - 1)))) = (309615759450 : ℝ) + u ^ 5 * ((151479481178152960000 : ℝ) * q ^ 2 + (456384375639019520000 : ℝ) * p * q + (303233469180866560000 : ℝ) * p ^ 2) + t * u ^ 4 * ((846701717791029452800 : ℝ) * q ^ 2 + (2498893908910534553600 : ℝ) * p * q + (1642101425276305100800 : ℝ) * p ^ 2) + t ^ 2 * u ^ 3 * ((1883224530240631026176 : ℝ) * q ^ 2 + (5455100706563677184512 : ℝ) * p * q + (3547705398206694158336 : ℝ) * p ^ 2) + t ^ 3 * u ^ 2 * ((2084799325967509569152 : ℝ) * q ^ 2 + (5936724948323650124224 : ℝ) * p * q + (3823207734086972555072 : ℝ) * p ^ 2) + t ^ 4 * u * ((1149340650965631044760 : ℝ) * q ^ 2 + (3221804439358255164120 : ℝ) * p * q + (2055534409230544119360 : ℝ) * p ^ 2) + t ^ 5 * ((252543482220180955650 : ℝ) * q ^ 2 + (697670245366418098425 : ℝ) * p * q + (441163834700173142775 : ℝ) * p ^ 2) := by
    set D_var : ℝ := (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))
    have h_D_var : D_var ≠ 0 := (hD_pos).ne'
    field_simp [hR.ne', h_D_var]
    dsimp only [D_var, t, u, p, q]; ring
  clear_value t u p q
  have hpos : 0 < (3096157594500 : ℝ) * (((4 * R ^ 2) * (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * (R - 1)))) := by rw [hid]; positivity
  have hfin : 0 < ((4 * R ^ 2) * (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * (R - 1))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((245 / 100 : ℝ) * R - 554 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * (R - 1)) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma wpn_hi_b_0_tlo {R s : ℝ} (hRlo : (121 / 200 : ℝ) ≤ R) (hRhi : R ≤ (627 / 1000 : ℝ))
    (hslo : (7 / 25 : ℝ) ≤ s) (hshi : s ≤ (29 / 50 : ℝ)) :
    ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) - 2 * (0) * ((R - 1 / (2 * R))) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hs : (0 : ℝ) < s := by linarith
  have hr1_pos : (0 : ℝ) < ((145 / 100 : ℝ) * R + 52 / 1000) := by linarith
  have hD_pos : (0 : ℝ) < (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) := by positivity
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  set p : ℝ := s - (7 / 25 : ℝ)
  set q : ℝ := (29 / 50 : ℝ) - s
  have ht : 0 ≤ t := sub_nonneg.mpr hRlo
  have hu : 0 ≤ u := sub_nonneg.mpr hRhi
  have hp : 0 ≤ p := sub_nonneg.mpr hslo
  have hq : 0 ≤ q := sub_nonneg.mpr hshi
  have hden : (0 : ℝ) < (4 * R ^ 2) * (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) := by positivity
  have hid : (173935080 : ℝ) * (((4 * R ^ 2) * (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) - 2 * (0) * ((R - 1 / (2 * R)))))) = (34787016 : ℝ) + u ^ 5 * ((106703648315568750 : ℝ) * q ^ 2 + (285031826757684375 : ℝ) * p * q + (158921256817115625 : ℝ) * p ^ 2) + t * u ^ 4 * ((545373493672106250 : ℝ) * q ^ 2 + (1446617659988728125 : ℝ) * p * q + (799090748341621875 : ℝ) * p ^ 2) + t ^ 2 * u ^ 3 * ((1114197607730559500 : ℝ) * q ^ 2 + (2935164560147707750 : ℝ) * p * q + (1606188688467148250 : ℝ) * p ^ 2) + t ^ 3 * u ^ 2 * ((1137352693306166100 : ℝ) * q ^ 2 + (2976001663808739450 : ℝ) * p * q + (1613162691124573350 : ℝ) * p ^ 2) + t ^ 4 * u * ((580087422866455270 : ℝ) * q ^ 2 + (1507818540570064115 : ℝ) * p * q + (809514287022608845 : ℝ) * p ^ 2) + t ^ 5 * ((118262485657187394 : ℝ) * q ^ 2 + (305395584398251353 : ℝ) * p * q + (162370779838063959 : ℝ) * p ^ 2) := by
    set D_var : ℝ := (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))
    have h_D_var : D_var ≠ 0 := (hD_pos).ne'
    field_simp [hR.ne', h_D_var]
    dsimp only [D_var, t, u, p, q]; ring
  clear_value t u p q
  have hpos : 0 < (173935080 : ℝ) * (((4 * R ^ 2) * (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) - 2 * (0) * ((R - 1 / (2 * R)))))) := by rw [hid]; positivity
  have hfin : 0 < ((4 * R ^ 2) * (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) - 2 * (0) * ((R - 1 / (2 * R))))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) - 2 * (0) * ((R - 1 / (2 * R)))) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma wpn_hi_b_0_0 {R s : ℝ} (hRlo : (121 / 200 : ℝ) ≤ R) (hRhi : R ≤ (627 / 1000 : ℝ))
    (hslo : (7 / 25 : ℝ) ≤ s) (hshi : s ≤ (29 / 50 : ℝ)) :
    ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) - 2 * (0) * (0) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hs : (0 : ℝ) < s := by linarith
  have hr1_pos : (0 : ℝ) < ((145 / 100 : ℝ) * R + 52 / 1000) := by linarith
  have hD_pos : (0 : ℝ) < (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) := by positivity
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  set p : ℝ := s - (7 / 25 : ℝ)
  set q : ℝ := (29 / 50 : ℝ) - s
  have ht : 0 ≤ t := sub_nonneg.mpr hRlo
  have hu : 0 ≤ u := sub_nonneg.mpr hRhi
  have hp : 0 ≤ p := sub_nonneg.mpr hslo
  have hq : 0 ≤ q := sub_nonneg.mpr hshi
  have hden : (0 : ℝ) < (4 * R ^ 2) * (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) := by positivity
  have hid : (217418850000 : ℝ) * (((4 * R ^ 2) * (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) - 2 * (0) * (0)))) = (43483770000 : ℝ) + u ^ 5 * ((133475074546355768750 : ℝ) * q ^ 2 + (336048520201689146875 : ℝ) * p * q + (170809069201481815625 : ℝ) * p ^ 2) + t * u ^ 4 * ((682157603974736676250 : ℝ) * q ^ 2 + (1714872347438396755625 : ℝ) * p * q + (870219368278142891875 : ℝ) * p ^ 2) + t ^ 2 * u ^ 3 * ((1393557450422363799500 : ℝ) * q ^ 2 + (3497210756773289812750 : ℝ) * p * q + (1770883611956670388250 : ℝ) * p ^ 2) + t ^ 3 * u ^ 2 * ((1422433082439840859700 : ℝ) * q ^ 2 + (3562716278423138597650 : ℝ) * p * q + (1799280039552019362950 : ℝ) * p ^ 2) + t ^ 4 * u * ((725447767556465498470 : ℝ) * q ^ 2 + (1813043204846366591015 : ℝ) * p * q + (912738121278288880045 : ℝ) * p ^ 2) + t ^ 5 * ((147889598278849432914 : ℝ) * q ^ 2 + (368713828766562723093 : ℝ) * p * q + (184931371882044572679 : ℝ) * p ^ 2) := by
    set D_var : ℝ := (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))
    have h_D_var : D_var ≠ 0 := (hD_pos).ne'
    field_simp [hR.ne', h_D_var]
    dsimp only [D_var, t, u, p, q]; ring
  clear_value t u p q
  have hpos : 0 < (217418850000 : ℝ) * (((4 * R ^ 2) * (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) - 2 * (0) * (0)))) := by rw [hid]; positivity
  have hfin : 0 < ((4 * R ^ 2) * (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) - 2 * (0) * (0))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) - 2 * (0) * (0)) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma wpn_hi_p0_0_ymin {R s : ℝ} (hRlo : (121 / 200 : ℝ) ≤ R) (hRhi : R ≤ (627 / 1000 : ℝ))
    (hslo : (7 / 25 : ℝ) ≤ s) (hshi : s ≤ (29 / 50 : ℝ)) :
    ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) - 2 * (0) * (R - 1) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hs : (0 : ℝ) < s := by linarith
  have hr1_pos : (0 : ℝ) < ((145 / 100 : ℝ) * R + 52 / 1000) := by linarith
  have hD_pos : (0 : ℝ) < (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) := by positivity
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  set p : ℝ := s - (7 / 25 : ℝ)
  set q : ℝ := (29 / 50 : ℝ) - s
  have ht : 0 ≤ t := sub_nonneg.mpr hRlo
  have hu : 0 ≤ u := sub_nonneg.mpr hRhi
  have hp : 0 ≤ p := sub_nonneg.mpr hslo
  have hq : 0 ≤ q := sub_nonneg.mpr hshi
  have hden : (0 : ℝ) < (4 * R ^ 2) * (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) := by positivity
  have hid : (173935080 : ℝ) * (((4 * R ^ 2) * (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) - 2 * (0) * (R - 1)))) = (69574032 : ℝ) + u ^ 5 * ((206776735648068750 : ℝ) * q ^ 2 + (597272341778934375 : ℝ) * p * q + (388651509505865625 : ℝ) * p ^ 2) + t * u ^ 4 * ((1097226808182606250 : ℝ) * q ^ 2 + (3141724351770978125 : ℝ) * p * q + (2034440990613371875 : ℝ) * p ^ 2) + t ^ 2 * u ^ 3 * ((2324363772659559500 : ℝ) * q ^ 2 + (6601958497258207750 : ℝ) * p * q + (4255701994648648250 : ℝ) * p ^ 2) + t ^ 3 * u ^ 2 * ((2457544850538206100 : ℝ) * q ^ 2 + (6928368182935719450 : ℝ) * p * q + (4447040715019513350 : ℝ) * p ^ 2) + t ^ 4 * u * ((1297021634570651270 : ℝ) * q ^ 2 + (3631395712218666115 : ℝ) * p * q + (2321481303967014845 : ℝ) * p ^ 2) + t ^ 5 * ((273390477880343394 : ℝ) * q ^ 2 + (760533997269373353 : ℝ) * p * q + (484353089486029959 : ℝ) * p ^ 2) := by
    set D_var : ℝ := (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))
    have h_D_var : D_var ≠ 0 := (hD_pos).ne'
    field_simp [hR.ne', h_D_var]
    dsimp only [D_var, t, u, p, q]; ring
  clear_value t u p q
  have hpos : 0 < (173935080 : ℝ) * (((4 * R ^ 2) * (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) - 2 * (0) * (R - 1)))) := by rw [hid]; positivity
  have hfin : 0 < ((4 * R ^ 2) * (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) - 2 * (0) * (R - 1))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (0)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (0))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) - 2 * (0) * (R - 1)) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma wpn_hi_b_tau_tlo {R s : ℝ} (hRlo : (121 / 200 : ℝ) ≤ R) (hRhi : R ≤ (627 / 1000 : ℝ))
    (hslo : (7 / 25 : ℝ) ≤ s) (hshi : s ≤ (29 / 50 : ℝ)) :
    ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * ((R - 1 / (2 * R))) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hs : (0 : ℝ) < s := by linarith
  have hr1_pos : (0 : ℝ) < ((145 / 100 : ℝ) * R + 52 / 1000) := by linarith
  have hD_pos : (0 : ℝ) < (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) := by positivity
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  set p : ℝ := s - (7 / 25 : ℝ)
  set q : ℝ := (29 / 50 : ℝ) - s
  have ht : 0 ≤ t := sub_nonneg.mpr hRlo
  have hu : 0 ≤ u := sub_nonneg.mpr hRhi
  have hp : 0 ≤ p := sub_nonneg.mpr hslo
  have hq : 0 ≤ q := sub_nonneg.mpr hshi
  have hden : (0 : ℝ) < (4 * R ^ 2) * (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) := by positivity
  have hid : (69574032000 : ℝ) * (((4 * R ^ 2) * (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * ((R - 1 / (2 * R)))))) = (6261662880 : ℝ) + u ^ 5 * ((18034002568789218750 : ℝ) * q ^ 2 + (41601556503101484375 : ℝ) * p * q + (15804785284312265625 : ℝ) * p ^ 2) + t * u ^ 4 * ((97057748488645756250 : ℝ) * q ^ 2 + (218743764152431028125 : ℝ) * p * q + (80824648473785271875 : ℝ) * p ^ 2) + t ^ 2 * u ^ 3 * ((209140266419692659500 : ℝ) * q ^ 2 + (461480907662009107750 : ℝ) * p * q + (166429335662316448250 : ℝ) * p ^ 2) + t ^ 3 * u ^ 2 * ((225468617994527763700 : ℝ) * q ^ 2 + (488110516488957750650 : ℝ) * p * q + (172447386743229986950 : ℝ) * p ^ 2) + t ^ 4 * u * ((121577965752877496950 : ℝ) * q ^ 2 + (258746721539883996275 : ℝ) * p * q + (89882023514606499325 : ℝ) * p ^ 2) + t ^ 5 * ((26225866444097083986 : ℝ) * q ^ 2 + (54974899491761726457 : ℝ) * p * q + (18844105486464642471 : ℝ) * p ^ 2) := by
    set D_var : ℝ := (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))
    have h_D_var : D_var ≠ 0 := (hD_pos).ne'
    field_simp [hR.ne', h_D_var]
    dsimp only [D_var, t, u, p, q]; ring
  clear_value t u p q
  have hpos : 0 < (69574032000 : ℝ) * (((4 * R ^ 2) * (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * ((R - 1 / (2 * R)))))) := by rw [hid]; positivity
  have hfin : 0 < ((4 * R ^ 2) * (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * ((R - 1 / (2 * R))))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * ((R - 1 / (2 * R)))) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma wpn_hi_b_tau_0 {R s : ℝ} (hRlo : (121 / 200 : ℝ) ≤ R) (hRhi : R ≤ (627 / 1000 : ℝ))
    (hslo : (7 / 25 : ℝ) ≤ s) (hshi : s ≤ (29 / 50 : ℝ)) :
    ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * (0) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hs : (0 : ℝ) < s := by linarith
  have hr1_pos : (0 : ℝ) < ((145 / 100 : ℝ) * R + 52 / 1000) := by linarith
  have hD_pos : (0 : ℝ) < (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) := by positivity
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  set p : ℝ := s - (7 / 25 : ℝ)
  set q : ℝ := (29 / 50 : ℝ) - s
  have ht : 0 ≤ t := sub_nonneg.mpr hRlo
  have hu : 0 ≤ u := sub_nonneg.mpr hRhi
  have hp : 0 ≤ p := sub_nonneg.mpr hslo
  have hq : 0 ≤ q := sub_nonneg.mpr hshi
  have hden : (0 : ℝ) < (4 * R ^ 2) * (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) := by positivity
  have hid : (1739350800000 : ℝ) * (((4 * R ^ 2) * (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * (0)))) = (347870160000 : ℝ) + u ^ 5 * ((1300724411037357868750 : ℝ) * q ^ 2 + (3038983863951253409375 : ℝ) * p * q + (1484144441283083040625 : ℝ) * p ^ 2) + t * u ^ 4 * ((6636015902946471066250 : ℝ) * q ^ 2 + (15442721004478014123125 : ℝ) * p * q + (7506742100047405556875 : ℝ) * p ^ 2) + t ^ 2 * u ^ 3 * ((13529335906828239383500 : ℝ) * q ^ 2 + (31347481772324977445750 : ℝ) * p * q + (15155988310342693062250 : ℝ) * p ^ 2) + t ^ 3 * u ^ 2 * ((13778270756127726070100 : ℝ) * q ^ 2 + (31772907916789232497450 : ℝ) * p * q + (15266611909211279427350 : ℝ) * p ^ 2) + t ^ 4 * u * ((7008948194005924781510 : ℝ) * q ^ 2 + (16079247200534933699995 : ℝ) * p * q + (7671440478436111218485 : ℝ) * p ^ 2) + t ^ 5 * ((1424721575308698880962 : ℝ) * q ^ 2 + (3250083038148928637169 : ℝ) * p * q + (1538218593994880016207 : ℝ) * p ^ 2) := by
    set D_var : ℝ := (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))
    have h_D_var : D_var ≠ 0 := (hD_pos).ne'
    field_simp [hR.ne', h_D_var]
    dsimp only [D_var, t, u, p, q]; ring
  clear_value t u p q
  have hpos : 0 < (1739350800000 : ℝ) * (((4 * R ^ 2) * (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * (0)))) := by rw [hid]; positivity
  have hfin : 0 < ((4 * R ^ 2) * (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * (0))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * (0)) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma wpn_hi_p0_tau_ymin {R s : ℝ} (hRlo : (121 / 200 : ℝ) ≤ R) (hRhi : R ≤ (627 / 1000 : ℝ))
    (hslo : (7 / 25 : ℝ) ≤ s) (hshi : s ≤ (29 / 50 : ℝ)) :
    ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * (R - 1) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hs : (0 : ℝ) < s := by linarith
  have hr1_pos : (0 : ℝ) < ((145 / 100 : ℝ) * R + 52 / 1000) := by linarith
  have hD_pos : (0 : ℝ) < (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) := by positivity
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  set p : ℝ := s - (7 / 25 : ℝ)
  set q : ℝ := (29 / 50 : ℝ) - s
  have ht : 0 ≤ t := sub_nonneg.mpr hRlo
  have hu : 0 ≤ u := sub_nonneg.mpr hRhi
  have hp : 0 ≤ p := sub_nonneg.mpr hslo
  have hq : 0 ≤ q := sub_nonneg.mpr hshi
  have hden : (0 : ℝ) < (4 * R ^ 2) * (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) := by positivity
  have hid : (69574032000 : ℝ) * (((4 * R ^ 2) * (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * (R - 1)))) = (13914806400 : ℝ) + u ^ 5 * ((32012851376539218750 : ℝ) * q ^ 2 + (99893170305476484375 : ℝ) * p * q + (67142680278937265625 : ℝ) * p ^ 2) + t * u ^ 4 * ((172640423604515756250 : ℝ) * q ^ 2 + (528156001429746028125 : ℝ) * p * q + (351492956635230271875 : ℝ) * p ^ 2) + t ^ 2 * u ^ 3 * ((371445096643864659500 : ℝ) * q ^ 2 + (1115743198924823107750 : ℝ) * p * q + (735541010300958448250 : ℝ) * p ^ 2) + t ^ 3 * u ^ 2 * ((398655508217003763700 : ℝ) * q ^ 2 + (1177290196609419750650 : ℝ) * p * q + (769121641441215986950 : ℝ) * p ^ 2) + t ^ 4 * u * ((213473517929854056950 : ℝ) * q ^ 2 + (620509492170597716275 : ℝ) * p * q + (401878864768343659325 : ℝ) * p ^ 2) + t ^ 5 * ((45635532314649643986 : ℝ) * q ^ 2 + (130699657789887446457 : ℝ) * p * q + (83947953514037802471 : ℝ) * p ^ 2) := by
    set D_var : ℝ := (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))
    have h_D_var : D_var ≠ 0 := (hD_pos).ne'
    field_simp [hR.ne', h_D_var]
    dsimp only [D_var, t, u, p, q]; ring
  clear_value t u p q
  have hpos : 0 < (69574032000 : ℝ) * (((4 * R ^ 2) * (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * (R - 1)))) := by rw [hid]; positivity
  have hfin : 0 < ((4 * R ^ 2) * (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * (R - 1))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * (((37 / 20 : ℝ) * R - 389 / 500))) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000)) + (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * ((145 / 100 : ℝ) * R + 52 / 1000))) * (((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)))) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) - 2 * (((37 / 20 : ℝ) * R - 389 / 500)) * (R - 1)) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma wnp_Rlo_b_tlo_0 {R s : ℝ} (hRlo : (4 / 7 : ℝ) ≤ R) (hRhi : R ≤ (121 / 200 : ℝ))
    (hslo : (7 / 25 : ℝ) ≤ s) (hshi : s ≤ (29 / 50 : ℝ)) :
    ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * ((R - 1 / (2 * R))) * (0) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hs : (0 : ℝ) < s := by linarith
  set t : ℝ := R - (4 / 7 : ℝ)
  set u : ℝ := (121 / 200 : ℝ) - R
  set p : ℝ := s - (7 / 25 : ℝ)
  set q : ℝ := (29 / 50 : ℝ) - s
  have ht : 0 ≤ t := sub_nonneg.mpr hRlo
  have hu : 0 ≤ u := sub_nonneg.mpr hRhi
  have hp : 0 ≤ p := sub_nonneg.mpr hslo
  have hq : 0 ≤ q := sub_nonneg.mpr hshi
  have hden : (0 : ℝ) < 4 * R ^ 2 := by positivity
  have hid : (1097928225000 : ℝ) * ((4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * ((R - 1 / (2 * R))) * (0)))) = (76854975750 : ℝ) + u ^ 4 * ((1106159762554880000 : ℝ) * q + (625353500794880000 : ℝ) * p) + t * u ^ 3 * ((4290115206854758400 : ℝ) * q + (2187713737977958400 : ℝ) * p) + t ^ 2 * u ^ 2 * ((6195545281772385728 : ℝ) * q + (2759319187689729728 : ℝ) * p) + t ^ 3 * u * ((3943393534098324880 : ℝ) * q + (1454290170171564880 : ℝ) * p) + t ^ 4 * ((931774478964907375 : ℝ) * q + (257289053770469875 : ℝ) * p) := by
    field_simp [hR.ne']; dsimp only [t, u, p, q]; ring
  clear_value t u p q
  have hpos : 0 < (1097928225000 : ℝ) * ((4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * ((R - 1 / (2 * R))) * (0)))) := by rw [hid]; positivity
  have hfin : 0 < (4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * ((R - 1 / (2 * R))) * (0))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * ((R - 1 / (2 * R))) * (0)) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma wnp_Rlo_b_0_0 {R s : ℝ} (hRlo : (4 / 7 : ℝ) ≤ R) (hRhi : R ≤ (121 / 200 : ℝ))
    (hslo : (7 / 25 : ℝ) ≤ s) (hshi : s ≤ (29 / 50 : ℝ)) :
    ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (0) * (0) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hs : (0 : ℝ) < s := by linarith
  set t : ℝ := R - (4 / 7 : ℝ)
  set u : ℝ := (121 / 200 : ℝ) - R
  set p : ℝ := s - (7 / 25 : ℝ)
  set q : ℝ := (29 / 50 : ℝ) - s
  have ht : 0 ≤ t := sub_nonneg.mpr hRlo
  have hu : 0 ≤ u := sub_nonneg.mpr hRhi
  have hp : 0 ≤ p := sub_nonneg.mpr hslo
  have hq : 0 ≤ q := sub_nonneg.mpr hshi
  have hden : (0 : ℝ) < 4 * R ^ 2 := by positivity
  have hid : (1097928225000 : ℝ) * ((4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (0) * (0)))) = (65875693500 : ℝ) + u ^ 4 * ((1135619122554880000 : ℝ) * q + (516092860794880000 : ℝ) * p) + t * u ^ 3 * ((4407666285254758400 : ℝ) * q + (1811748016377958400 : ℝ) * p) + t ^ 2 * u ^ 2 * ((6371465613324385728 : ℝ) * q + (2282025615241729728 : ℝ) * p) + t ^ 3 * u * ((4060420262510484880 : ℝ) * q + (1190160810263724880 : ℝ) * p) + t ^ 4 * ((960972621551280975 : ℝ) * q + (203742356419643475 : ℝ) * p) := by
    field_simp [hR.ne']; dsimp only [t, u, p, q]; ring
  clear_value t u p q
  have hpos : 0 < (1097928225000 : ℝ) * ((4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (0) * (0)))) := by rw [hid]; positivity
  have hfin : 0 < (4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (0) * (0))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (0) * (0)) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma wnp_Rlo_p0_xmin_0 {R s : ℝ} (hRlo : (4 / 7 : ℝ) ≤ R) (hRhi : R ≤ (121 / 200 : ℝ))
    (hslo : (7 / 25 : ℝ) ≤ s) (hshi : s ≤ (29 / 50 : ℝ)) :
    ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (R - 1) * (0) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hs : (0 : ℝ) < s := by linarith
  set t : ℝ := R - (4 / 7 : ℝ)
  set u : ℝ := (121 / 200 : ℝ) - R
  set p : ℝ := s - (7 / 25 : ℝ)
  set q : ℝ := (29 / 50 : ℝ) - s
  have ht : 0 ≤ t := sub_nonneg.mpr hRlo
  have hu : 0 ≤ u := sub_nonneg.mpr hRhi
  have hp : 0 ≤ p := sub_nonneg.mpr hslo
  have hq : 0 ≤ q := sub_nonneg.mpr hshi
  have hden : (0 : ℝ) < 4 * R ^ 2 := by positivity
  have hid : (1097928225000 : ℝ) * ((4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (R - 1) * (0)))) = (219585645000 : ℝ) + u ^ 4 * ((1268435442554880000 : ℝ) * q + (952269180794880000 : ℝ) * p) + t * u ^ 3 * ((5254696816454758400 : ℝ) * q + (3888236147577958400 : ℝ) * p) + t ^ 2 * u ^ 2 * ((8147180550572385728 : ℝ) * q + (5930936856489729728 : ℝ) * p) + t ^ 3 * u * ((5602894076098324880 : ℝ) * q + (4004493112171564880 : ℝ) * p) + t ^ 4 * ((1441945681764907375 : ℝ) * q + (1009481056570469875 : ℝ) * p) := by
    field_simp [hR.ne']; dsimp only [t, u, p, q]; ring
  clear_value t u p q
  have hpos : 0 < (1097928225000 : ℝ) * ((4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (R - 1) * (0)))) := by rw [hid]; positivity
  have hfin : 0 < (4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (R - 1) * (0))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (R - 1) * (0)) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma wnp_Rlo_b_tlo_tau {R s : ℝ} (hRlo : (4 / 7 : ℝ) ≤ R) (hRhi : R ≤ (121 / 200 : ℝ))
    (hslo : (7 / 25 : ℝ) ≤ s) (hshi : s ≤ (29 / 50 : ℝ)) :
    ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * ((R - 1 / (2 * R))) * (((37 / 20 : ℝ) * R - 389 / 500)) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hs : (0 : ℝ) < s := by linarith
  set t : ℝ := R - (4 / 7 : ℝ)
  set u : ℝ := (121 / 200 : ℝ) - R
  set p : ℝ := s - (7 / 25 : ℝ)
  set q : ℝ := (29 / 50 : ℝ) - s
  have ht : 0 ≤ t := sub_nonneg.mpr hRlo
  have hu : 0 ≤ u := sub_nonneg.mpr hRhi
  have hp : 0 ≤ p := sub_nonneg.mpr hslo
  have hq : 0 ≤ q := sub_nonneg.mpr hshi
  have hden : (0 : ℝ) < 4 * R ^ 2 := by positivity
  have hid : (1097928225000 : ℝ) * ((4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * ((R - 1 / (2 * R))) * (((37 / 20 : ℝ) * R - 389 / 500))))) = (2195856450 : ℝ) + u ^ 4 * ((663748397445120000 : ℝ) * q + (300234659205120000 : ℝ) * p) + t * u ^ 3 * ((2481852725945241600 : ℝ) * q + (914596594822041600 : ℝ) * p) + t ^ 2 * u ^ 2 * ((3460648322627614272 : ℝ) * q + (938446976710270272 : ℝ) * p) + t ^ 3 * u * ((2131746862500235120 : ℝ) * q + (335289466106995120 : ℝ) * p) + t ^ 4 * ((489227721646966225 : ℝ) * q + (11236370904203725 : ℝ) * p) := by
    field_simp [hR.ne']; dsimp only [t, u, p, q]; ring
  clear_value t u p q
  have hpos : 0 < (1097928225000 : ℝ) * ((4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * ((R - 1 / (2 * R))) * (((37 / 20 : ℝ) * R - 389 / 500))))) := by rw [hid]; positivity
  have hfin : 0 < (4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * ((R - 1 / (2 * R))) * (((37 / 20 : ℝ) * R - 389 / 500)))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * ((R - 1 / (2 * R))) * (((37 / 20 : ℝ) * R - 389 / 500))) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma wnp_Rlo_b_0_tau {R s : ℝ} (hRlo : (4 / 7 : ℝ) ≤ R) (hRhi : R ≤ (121 / 200 : ℝ))
    (hslo : (7 / 25 : ℝ) ≤ s) (hshi : s ≤ (29 / 50 : ℝ)) :
    ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500)) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hs : (0 : ℝ) < s := by linarith
  set t : ℝ := R - (4 / 7 : ℝ)
  set u : ℝ := (121 / 200 : ℝ) - R
  set p : ℝ := s - (7 / 25 : ℝ)
  set q : ℝ := (29 / 50 : ℝ) - s
  have ht : 0 ≤ t := sub_nonneg.mpr hRlo
  have hu : 0 ≤ u := sub_nonneg.mpr hRhi
  have hp : 0 ≤ p := sub_nonneg.mpr hslo
  have hq : 0 ≤ q := sub_nonneg.mpr hshi
  have hden : (0 : ℝ) < 4 * R ^ 2 := by positivity
  have hid : (1097928225000 : ℝ) * ((4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500))))) = (98813540250 : ℝ) + u ^ 4 * ((1048635757445120000 : ℝ) * q + (546402019205120000 : ℝ) * p) + t * u ^ 3 * ((4059424940345241600 : ℝ) * q + (1998652009222041600 : ℝ) * p) + t ^ 2 * u ^ 2 * ((5848584164499614272 : ℝ) * q + (2673168914582270272 : ℝ) * p) + t ^ 3 * u * ((3711443914661995120 : ℝ) * q + (1533830429948755120 : ℝ) * p) + t ^ 4 * ((873619649203839825 : ℝ) * q + (312883458523877325 : ℝ) * p) := by
    field_simp [hR.ne']; dsimp only [t, u, p, q]; ring
  clear_value t u p q
  have hpos : 0 < (1097928225000 : ℝ) * ((4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500))))) := by rw [hid]; positivity
  have hfin : 0 < (4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500)))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500))) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma wnp_Rlo_p0_xmin_tau {R s : ℝ} (hRlo : (4 / 7 : ℝ) ≤ R) (hRhi : R ≤ (121 / 200 : ℝ))
    (hslo : (7 / 25 : ℝ) ≤ s) (hshi : s ≤ (29 / 50 : ℝ)) :
    ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (R - 1) * (((37 / 20 : ℝ) * R - 389 / 500)) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hs : (0 : ℝ) < s := by linarith
  set t : ℝ := R - (4 / 7 : ℝ)
  set u : ℝ := (121 / 200 : ℝ) - R
  set p : ℝ := s - (7 / 25 : ℝ)
  set q : ℝ := (29 / 50 : ℝ) - s
  have ht : 0 ≤ t := sub_nonneg.mpr hRlo
  have hu : 0 ≤ u := sub_nonneg.mpr hRhi
  have hp : 0 ≤ p := sub_nonneg.mpr hslo
  have hq : 0 ≤ q := sub_nonneg.mpr hshi
  have hden : (0 : ℝ) < 4 * R ^ 2 := by positivity
  have hid : (1097928225000 : ℝ) * ((4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (R - 1) * (((37 / 20 : ℝ) * R - 389 / 500))))) = (109792822500 : ℝ) + u ^ 4 * ((655604877445120000 : ℝ) * q + (456731139205120000 : ℝ) * p) + t * u ^ 3 * ((2567468079545241600 : ℝ) * q + (1736152748422041600 : ℝ) * p) + t ^ 2 * u ^ 2 * ((3759753420947614272 : ℝ) * q + (2457534475030270272 : ℝ) * p) + t ^ 3 * u * ((2439795622120235120 : ℝ) * q + (1534040625726995120 : ℝ) * p) + t ^ 4 * ((591930256546966225 : ℝ) * q + (355959705804203725 : ℝ) * p) := by
    field_simp [hR.ne']; dsimp only [t, u, p, q]; ring
  clear_value t u p q
  have hpos : 0 < (1097928225000 : ℝ) * ((4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (R - 1) * (((37 / 20 : ℝ) * R - 389 / 500))))) := by rw [hid]; positivity
  have hfin : 0 < (4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (R - 1) * (((37 / 20 : ℝ) * R - 389 / 500)))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (R - 1) * (((37 / 20 : ℝ) * R - 389 / 500))) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma wnp_slo_b_tlo_0 {R s : ℝ} (hRlo : (121 / 200 : ℝ) ≤ R) (hRhi : R ≤ (627 / 1000 : ℝ))
    (hslo : (7 / 25 : ℝ) ≤ s) (hshi : s ≤ (9 / 20 : ℝ)) :
    ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * ((R - 1 / (2 * R))) * (0) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hs : (0 : ℝ) < s := by linarith
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  set p : ℝ := s - (7 / 25 : ℝ)
  set q : ℝ := (9 / 20 : ℝ) - s
  have ht : 0 ≤ t := sub_nonneg.mpr hRlo
  have hu : 0 ≤ u := sub_nonneg.mpr hRhi
  have hp : 0 ≤ p := sub_nonneg.mpr hslo
  have hq : 0 ≤ q := sub_nonneg.mpr hshi
  have hden : (0 : ℝ) < 4 * R ^ 2 := by positivity
  have hid : (29867640000 : ℝ) * ((4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * ((R - 1 / (2 * R))) * (0)))) = (2389411200 : ℝ) + u ^ 4 * ((235048542004609375 : ℝ) * q + (135556557516328125 : ℝ) * p) + t * u ^ 3 * ((903297390513542500 : ℝ) * q + (485142135297667500 : ℝ) * p) + t ^ 2 * u ^ 2 * ((1294683557279889050 : ℝ) * q + (636167018293361550 : ℝ) * p) + t ^ 3 * u * ((819514735340981540 : ℝ) * q + (358951160221794540 : ℝ) * p) + t ^ 4 * ((193078623934817663 : ℝ) * q + (72367964835530013 : ℝ) * p) := by
    field_simp [hR.ne']; dsimp only [t, u, p, q]; ring
  clear_value t u p q
  have hpos : 0 < (29867640000 : ℝ) * ((4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * ((R - 1 / (2 * R))) * (0)))) := by rw [hid]; positivity
  have hfin : 0 < (4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * ((R - 1 / (2 * R))) * (0))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * ((R - 1 / (2 * R))) * (0)) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma wnp_slo_b_0_0 {R s : ℝ} (hRlo : (121 / 200 : ℝ) ≤ R) (hRhi : R ≤ (627 / 1000 : ℝ))
    (hslo : (7 / 25 : ℝ) ≤ s) (hshi : s ≤ (9 / 20 : ℝ)) :
    ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (0) * (0) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hs : (0 : ℝ) < s := by linarith
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  set p : ℝ := s - (7 / 25 : ℝ)
  set q : ℝ := (9 / 20 : ℝ) - s
  have ht : 0 ≤ t := sub_nonneg.mpr hRlo
  have hu : 0 ≤ u := sub_nonneg.mpr hRhi
  have hp : 0 ≤ p := sub_nonneg.mpr hslo
  have hq : 0 ≤ q := sub_nonneg.mpr hshi
  have hden : (0 : ℝ) < 4 * R ^ 2 := by positivity
  have hid : (29867640000 : ℝ) * ((4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (0) * (0)))) = (2389411200 : ℝ) + u ^ 4 * ((235149058088109375 : ℝ) * q + (123451549174828125 : ℝ) * p) + t * u ^ 3 * ((903659511005142500 : ℝ) * q + (441532481809267500 : ℝ) * p) + t ^ 2 * u ^ 2 * ((1295170064298649050 : ℝ) * q + (577577673034121550 : ℝ) * p) + t ^ 3 * u * ((819803596539397540 : ℝ) * q + (324164018755410540 : ℝ) * p) + t ^ 4 * ((193142583834407263 : ℝ) * q + (64665365499239613 : ℝ) * p) := by
    field_simp [hR.ne']; dsimp only [t, u, p, q]; ring
  clear_value t u p q
  have hpos : 0 < (29867640000 : ℝ) * ((4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (0) * (0)))) := by rw [hid]; positivity
  have hfin : 0 < (4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (0) * (0))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (0) * (0)) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma wnp_slo_p0_xmin_0 {R s : ℝ} (hRlo : (121 / 200 : ℝ) ≤ R) (hRhi : R ≤ (627 / 1000 : ℝ))
    (hslo : (7 / 25 : ℝ) ≤ s) (hshi : s ≤ (9 / 20 : ℝ)) :
    ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (R - 1) * (0) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hs : (0 : ℝ) < s := by linarith
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  set p : ℝ := s - (7 / 25 : ℝ)
  set q : ℝ := (9 / 20 : ℝ) - s
  have ht : 0 ≤ t := sub_nonneg.mpr hRlo
  have hu : 0 ≤ u := sub_nonneg.mpr hRhi
  have hp : 0 ≤ p := sub_nonneg.mpr hslo
  have hq : 0 ≤ q := sub_nonneg.mpr hshi
  have hden : (0 : ℝ) < 4 * R ^ 2 := by positivity
  have hid : (29867640000 : ℝ) * ((4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (R - 1) * (0)))) = (8960292000 : ℝ) + u ^ 4 * ((300350292004609375 : ℝ) * q + (236558307516328125 : ℝ) * p) + t * u ^ 3 * ((1229528690513542500 : ℝ) * q + (961653435297667500 : ℝ) * p) + t ^ 2 * u ^ 2 * ((1885385717279889050 : ℝ) * q + (1463509178293361550 : ℝ) * p) + t ^ 3 * u * ((1283496043340981540 : ℝ) * q + (988172468221794540 : ℝ) * p) + t ^ 4 * ((327287321934817663 : ℝ) * q + (249756662835530013 : ℝ) * p) := by
    field_simp [hR.ne']; dsimp only [t, u, p, q]; ring
  clear_value t u p q
  have hpos : 0 < (29867640000 : ℝ) * ((4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (R - 1) * (0)))) := by rw [hid]; positivity
  have hfin : 0 < (4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (R - 1) * (0))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (R - 1) * (0)) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma wnp_slo_b_tlo_tau {R s : ℝ} (hRlo : (121 / 200 : ℝ) ≤ R) (hRhi : R ≤ (627 / 1000 : ℝ))
    (hslo : (7 / 25 : ℝ) ≤ s) (hshi : s ≤ (9 / 20 : ℝ)) :
    ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * ((R - 1 / (2 * R))) * (((37 / 20 : ℝ) * R - 389 / 500)) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hs : (0 : ℝ) < s := by linarith
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  set p : ℝ := s - (7 / 25 : ℝ)
  set q : ℝ := (9 / 20 : ℝ) - s
  have ht : 0 ≤ t := sub_nonneg.mpr hRlo
  have hu : 0 ≤ u := sub_nonneg.mpr hRhi
  have hp : 0 ≤ p := sub_nonneg.mpr hslo
  have hq : 0 ≤ q := sub_nonneg.mpr hshi
  have hden : (0 : ℝ) < 4 * R ^ 2 := by positivity
  have hid : (29867640000 : ℝ) * ((4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * ((R - 1 / (2 * R))) * (((37 / 20 : ℝ) * R - 389 / 500))))) = (298676400 : ℝ) + u ^ 4 * ((121349990016390625 : ℝ) * q + (50842450079671875 : ℝ) * p) + t * u ^ 3 * ((455575573628057500 : ℝ) * q + (162379854863932500 : ℝ) * p) + t ^ 2 * u ^ 2 * ((638713311643870950 : ℝ) * q + (182122158352398450 : ℝ) * p) + t ^ 3 * u * ((396181486259434460 : ℝ) * q + (80566978713821460 : ℝ) * p) + t ^ 4 * ((91694951343871937 : ℝ) * q + (9983611207279587 : ℝ) * p) := by
    field_simp [hR.ne']; dsimp only [t, u, p, q]; ring
  clear_value t u p q
  have hpos : 0 < (29867640000 : ℝ) * ((4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * ((R - 1 / (2 * R))) * (((37 / 20 : ℝ) * R - 389 / 500))))) := by rw [hid]; positivity
  have hfin : 0 < (4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * ((R - 1 / (2 * R))) * (((37 / 20 : ℝ) * R - 389 / 500)))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1 / (2 * R))) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * ((R - 1 / (2 * R))) * (((37 / 20 : ℝ) * R - 389 / 500))) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma wnp_slo_b_0_tau {R s : ℝ} (hRlo : (121 / 200 : ℝ) ≤ R) (hRhi : R ≤ (627 / 1000 : ℝ))
    (hslo : (7 / 25 : ℝ) ≤ s) (hshi : s ≤ (9 / 20 : ℝ)) :
    ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500)) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hs : (0 : ℝ) < s := by linarith
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  set p : ℝ := s - (7 / 25 : ℝ)
  set q : ℝ := (9 / 20 : ℝ) - s
  have ht : 0 ≤ t := sub_nonneg.mpr hRlo
  have hu : 0 ≤ u := sub_nonneg.mpr hRhi
  have hp : 0 ≤ p := sub_nonneg.mpr hslo
  have hq : 0 ≤ q := sub_nonneg.mpr hshi
  have hden : (0 : ℝ) < 4 * R ^ 2 := by positivity
  have hid : (29867640000 : ℝ) * ((4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500))))) = (2986764000 : ℝ) + u ^ 4 * ((219910362662390625 : ℝ) * q + (137197298300671875 : ℝ) * p) + t * u ^ 3 * ((842630432469657500 : ℝ) * q + (505462939725532500 : ℝ) * p) + t ^ 2 * u ^ 2 * ((1203507149357630950 : ℝ) * q + (687840143788158450 : ℝ) * p) + t ^ 3 * u * ((758609898335850460 : ℝ) * q + (407919388125437460 : ℝ) * p) + t ^ 4 * ((177821412972361537 : ℝ) * q + (88343513599889187 : ℝ) * p) := by
    field_simp [hR.ne']; dsimp only [t, u, p, q]; ring
  clear_value t u p q
  have hpos : 0 < (29867640000 : ℝ) * ((4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500))))) := by rw [hid]; positivity
  have hfin : 0 < (4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500)))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (0) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500))) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma wnp_slo_p0_xmin_tau {R s : ℝ} (hRlo : (121 / 200 : ℝ) ≤ R) (hRhi : R ≤ (627 / 1000 : ℝ))
    (hslo : (7 / 25 : ℝ) ≤ s) (hshi : s ≤ (9 / 20 : ℝ)) :
    ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (R - 1) * (((37 / 20 : ℝ) * R - 389 / 500)) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hs : (0 : ℝ) < s := by linarith
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  set p : ℝ := s - (7 / 25 : ℝ)
  set q : ℝ := (9 / 20 : ℝ) - s
  have ht : 0 ≤ t := sub_nonneg.mpr hRlo
  have hu : 0 ≤ u := sub_nonneg.mpr hRhi
  have hp : 0 ≤ p := sub_nonneg.mpr hslo
  have hq : 0 ≤ q := sub_nonneg.mpr hshi
  have hden : (0 : ℝ) < 4 * R ^ 2 := by positivity
  have hid : (29867640000 : ℝ) * ((4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (R - 1) * (((37 / 20 : ℝ) * R - 389 / 500))))) = (2986764000 : ℝ) + u ^ 4 * ((154084302516390625 : ℝ) * q + (119276762579671875 : ℝ) * p) + t * u ^ 3 * ((604042368628057500 : ℝ) * q + (461126649863932500 : ℝ) * p) + t ^ 2 * u ^ 2 * ((886721187643870950 : ℝ) * q + (666770034352398450 : ℝ) * p) + t ^ 3 * u * ((577679798459434460 : ℝ) * q + (427305290913821460 : ℝ) * p) + t ^ 4 * ((140917870043871937 : ℝ) * q + (102386529907279587 : ℝ) * p) := by
    field_simp [hR.ne']; dsimp only [t, u, p, q]; ring
  clear_value t u p q
  have hpos : 0 < (29867640000 : ℝ) * ((4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (R - 1) * (((37 / 20 : ℝ) * R - 389 / 500))))) := by rw [hid]; positivity
  have hfin : 0 < (4 * R ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (R - 1) * (((37 / 20 : ℝ) * R - 389 / 500)))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * ((R - 1)) + (R - 1 / (2 * R)) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (R - 1) * (((37 / 20 : ℝ) * R - 389 / 500))) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma wnp_hi_U_xm_0 {R s : ℝ} (hRlo : (121 / 200 : ℝ) ≤ R) (hRhi : R ≤ (627 / 1000 : ℝ))
    (hslo : (9 / 20 : ℝ) ≤ s) (hshi : s ≤ (29 / 50 : ℝ)) :
    ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * ((1 - R ^ 2 + ((-37 / 100 : ℝ) * R) ^ 2 + (((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 + 2 * ((R - 1 / (2 * R)) - ((-37 / 100 : ℝ) * R)) * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))))) / (2 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) ^ 2) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) * (0) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hs : (0 : ℝ) < s := by linarith
  have hr1_pos : (0 : ℝ) < ((145 / 100 : ℝ) * R + 52 / 1000) := by linarith
  have hA_pos : (0 : ℝ) < ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) := by positivity
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  set p : ℝ := s - (9 / 20 : ℝ)
  set q : ℝ := (29 / 50 : ℝ) - s
  have ht : 0 ≤ t := sub_nonneg.mpr hRlo
  have hu : 0 ≤ u := sub_nonneg.mpr hRhi
  have hp : 0 ≤ p := sub_nonneg.mpr hslo
  have hq : 0 ≤ q := sub_nonneg.mpr hshi
  have hden : (0 : ℝ) < (4 * R ^ 2) * (4 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2) := by positivity
  have hid : (5877411840231360000 : ℝ) * (((4 * R ^ 2) * (4 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2)) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * ((1 - R ^ 2 + ((-37 / 100 : ℝ) * R) ^ 2 + (((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 + 2 * ((R - 1 / (2 * R)) - ((-37 / 100 : ℝ) * R)) * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))))) / (2 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) ^ 2) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) * (0)))) = (1175482368046272000 : ℝ) + u ^ 8 * ((102374627699291616683477867431640625 : ℝ) * q ^ 4 + (425794140030528192039219245556640625 : ℝ) * p * q ^ 3 + (653105213799429837309474549257812500 : ℝ) * p ^ 2 * q ^ 2 + (437280248927146048709700081914062500 : ℝ) * p ^ 3 * q + (107576705036939392902130012343750000 : ℝ) * p ^ 4) + t * u ^ 7 * ((882192638475641651422873731796875000 : ℝ) * q ^ 4 + (3660638054006978127244319252078125000 : ℝ) * p * q ^ 3 + (5605459226805593072479481172993750000 : ℝ) * p ^ 2 * q ^ 2 + (3749127063075733003926194168737500000 : ℝ) * p ^ 3 * q + (921966692147548089436851159775000000 : ℝ) * p ^ 4) + t ^ 2 * u ^ 6 * ((3309631782202385016576789932235937500 : ℝ) * q ^ 4 + (13703378558525334366677687882087187500 : ℝ) * p * q ^ 3 + (20949553751371442103322707989619000000 : ℝ) * p ^ 2 * q ^ 2 + (13996225035799340791386472977971750000 : ℝ) * p ^ 3 * q + (3439891390219156436808678834454000000 : ℝ) * p ^ 4) + t ^ 3 * u ^ 5 * ((7064317174384290839275190180758125000 : ℝ) * q ^ 4 + (29189464828616022632748353819208375000 : ℝ) * p * q ^ 3 + (44553332519035576289505429587408550000 : ℝ) * p ^ 2 * q ^ 2 + (29730905541036794589139765178480100000 : ℝ) * p ^ 3 * q + (7301639213933234384075991949771800000 : ℝ) * p ^ 4) + t ^ 4 * u ^ 4 * ((9387600394835822983534081694508843750 : ℝ) * q ^ 4 + (38713265957380703852488601269450293750 : ℝ) * p * q ^ 3 + (58996859352507787764648677694439965000 : ℝ) * p ^ 2 * q ^ 2 + (39320829023054363294221384850688455000 : ℝ) * p ^ 3 * q + (9648247360788062115348495675964940000 : ℝ) * p ^ 4) + t ^ 5 * u ^ 3 * ((7956101533880502731996686976544525000 : ℝ) * q ^ 4 + (32748123281377031250566773252633395000 : ℝ) * p * q ^ 3 + (49828000564998998676067097025383154000 : ℝ) * p ^ 2 * q ^ 2 + (33167003844115541055209365102468548000 : ℝ) * p ^ 3 * q + (8129885162011373743880408242224264000 : ℝ) * p ^ 4) + t ^ 6 * u ^ 2 * ((4200953065177038929355897766296577500 : ℝ) * q ^ 4 + (17259907172494056208114654980415639500 : ℝ) * p * q ^ 3 + (26220562192273400525678850485863250400 : ℝ) * p ^ 2 * q ^ 2 + (17429538558077957859967913864333074800 : ℝ) * p ^ 3 * q + (4267345383198909368702161056934886400 : ℝ) * p ^ 4) + t ^ 7 * u * ((1263856481536120506302484905624235000 : ℝ) * q ^ 4 + (5183342280283564192072917485954073000 : ℝ) * p * q ^ 3 + (7861847134749885338534369898011499600 : ℝ) * p ^ 2 * q ^ 2 + (5218556735029584313996411014940015200 : ℝ) * p ^ 3 * q + (1276023790283146512332156820400353600 : ℝ) * p ^ 4) + t ^ 8 * ((165907958361788641392518280810306225 : ℝ) * q ^ 4 + (679222615851873641713645362360828705 : ℝ) * p * q ^ 3 + (1028558935636014452448701187689856516 : ℝ) * p ^ 2 * q ^ 2 + (681720317397268756507583175415059492 : ℝ) * p ^ 3 * q + (166454019131766497519143038534225456 : ℝ) * p ^ 4) := by
    set A_var : ℝ := ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R)))
    have h_A_var : A_var ≠ 0 := (hA_pos).ne'
    field_simp [hR.ne', h_A_var]
    dsimp only [A_var, t, u, p, q]; ring
  clear_value t u p q
  have hpos : 0 < (5877411840231360000 : ℝ) * (((4 * R ^ 2) * (4 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2)) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * ((1 - R ^ 2 + ((-37 / 100 : ℝ) * R) ^ 2 + (((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 + 2 * ((R - 1 / (2 * R)) - ((-37 / 100 : ℝ) * R)) * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))))) / (2 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) ^ 2) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) * (0)))) := by rw [hid]; positivity
  have hfin : 0 < ((4 * R ^ 2) * (4 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2)) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * ((1 - R ^ 2 + ((-37 / 100 : ℝ) * R) ^ 2 + (((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 + 2 * ((R - 1 / (2 * R)) - ((-37 / 100 : ℝ) * R)) * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))))) / (2 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) ^ 2) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) * (0))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * ((1 - R ^ 2 + ((-37 / 100 : ℝ) * R) ^ 2 + (((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 + 2 * ((R - 1 / (2 * R)) - ((-37 / 100 : ℝ) * R)) * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))))) / (2 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) ^ 2) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) * (0)) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma wnp_hi_U_xm_tau {R s : ℝ} (hRlo : (121 / 200 : ℝ) ≤ R) (hRhi : R ≤ (627 / 1000 : ℝ))
    (hslo : (9 / 20 : ℝ) ≤ s) (hshi : s ≤ (29 / 50 : ℝ)) :
    ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * ((1 - R ^ 2 + ((-37 / 100 : ℝ) * R) ^ 2 + (((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 + 2 * ((R - 1 / (2 * R)) - ((-37 / 100 : ℝ) * R)) * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))))) / (2 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) ^ 2) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) * (((37 / 20 : ℝ) * R - 389 / 500)) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hs : (0 : ℝ) < s := by linarith
  have hr1_pos : (0 : ℝ) < ((145 / 100 : ℝ) * R + 52 / 1000) := by linarith
  have hA_pos : (0 : ℝ) < ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) := by positivity
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  set p : ℝ := s - (9 / 20 : ℝ)
  set q : ℝ := (29 / 50 : ℝ) - s
  have ht : 0 ≤ t := sub_nonneg.mpr hRlo
  have hu : 0 ≤ u := sub_nonneg.mpr hRhi
  have hp : 0 ≤ p := sub_nonneg.mpr hslo
  have hq : 0 ≤ q := sub_nonneg.mpr hshi
  have hden : (0 : ℝ) < (4 * R ^ 2) * (4 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2) := by positivity
  have hid : (5877411840231360000 : ℝ) * (((4 * R ^ 2) * (4 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2)) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * ((1 - R ^ 2 + ((-37 / 100 : ℝ) * R) ^ 2 + (((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 + 2 * ((R - 1 / (2 * R)) - ((-37 / 100 : ℝ) * R)) * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))))) / (2 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) ^ 2) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) * (((37 / 20 : ℝ) * R - 389 / 500))))) = (58774118402313600 : ℝ) + u ^ 8 * ((36861234595964603707158534667968750 : ℝ) * q ^ 4 + (129688793902856134559931354541015625 : ℝ) * p * q ^ 3 + (155074129357274379581515659287109375 : ℝ) * p ^ 2 * q ^ 2 + (67405087436111608946183427656250000 : ℝ) * p ^ 3 * q + (5140674963715366363603689804687500 : ℝ) * p ^ 4) + t * u ^ 7 * ((315608638850399098462787181093750000 : ℝ) * q ^ 4 + (1114303170732556965211106572140625000 : ℝ) * p * q ^ 3 + (1343290647160196284942934068959375000 : ℝ) * p ^ 2 * q ^ 2 + (596857970745061969228928808450000000 : ℝ) * p ^ 3 * q + (52115295813095233203006774287500000 : ℝ) * p ^ 4) + t ^ 2 * u ^ 6 * ((1172712706694854302004403231240625000 : ℝ) * q ^ 4 + (4148712768950296922774411970647187500 : ℝ) * p * q ^ 3 + (5026735238126424126029970282451312500 : ℝ) * p ^ 2 * q ^ 2 + (2264823872311444751982635705747000000 : ℝ) * p ^ 3 * q + (213562025908771645366690058952250000 : ℝ) * p ^ 4) + t ^ 3 * u ^ 5 * ((2471978723921769859135753470101250000 : ℝ) * q ^ 4 + (8751258295110635498741993934322875000 : ℝ) * p * q ^ 3 + (10630228226828624830536207065438325000 : ℝ) * p ^ 2 * q ^ 2 + (4825839144552554291564256999932400000 : ℝ) * p ^ 3 * q + (473809026613079391602783118965700000 : ℝ) * p ^ 4) + t ^ 4 * u ^ 4 * ((3235178959958746839485448612901312500 : ℝ) * q ^ 4 + (11447823796020235528966463581385643750 : ℝ) * p * q ^ 3 + (13909820417059599857726904976967066250 : ℝ) * p ^ 2 * q ^ 2 + (6328313626090360817604126113983420000 : ℝ) * p ^ 3 * q + (629750172788855366179505050275685000 : ℝ) * p ^ 4) + t ^ 5 * u ^ 3 * ((2693108468539022316001554076859850000 : ℝ) * q ^ 4 + (9514924610310189557830621162017855000 : ℝ) * p * q ^ 3 + (11540675540224883666665014198926721000 : ℝ) * p ^ 2 * q ^ 2 + (5235991273243320882024185691611952000 : ℝ) * p ^ 3 * q + (515992010187907303356292466893236000 : ℝ) * p ^ 4) + t ^ 6 * u ^ 2 * ((1393015117241443664400047930762985000 : ℝ) * q ^ 4 + (4908802764513897270553192751998735500 : ℝ) * p * q ^ 3 + (5931385680549695066170238458929662100 : ℝ) * p ^ 2 * q ^ 2 + (2670800287848694398705958011052075200 : ℝ) * p ^ 3 * q + (254617164648787694343204837704163600 : ℝ) * p ^ 4) + t ^ 7 * u * ((409432693970581753568402194167390000 : ℝ) * q ^ 4 + (1437500175957907635346162851928677000 : ℝ) * p * q ^ 3 + (1726855207254243658342667642709425400 : ℝ) * p ^ 2 * q ^ 2 + (767863675156017864802402136953564800 : ℝ) * p ^ 3 * q + (68904341145103939337178275147426400 : ℝ) * p ^ 4) + t ^ 8 * ((52360506790453612995689475129003150 : ℝ) * q ^ 4 + (182958128722614099529013716267387545 : ℝ) * p * q ^ 3 + (218034156372637068962727597181477359 : ℝ) * p ^ 2 * q ^ 2 + (95209190008639086530300671884037008 : ℝ) * p ^ 3 * q + (7750635448589697240031285099444044 : ℝ) * p ^ 4) := by
    set A_var : ℝ := ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R)))
    have h_A_var : A_var ≠ 0 := (hA_pos).ne'
    field_simp [hR.ne', h_A_var]
    dsimp only [A_var, t, u, p, q]; ring
  clear_value t u p q
  have hpos : 0 < (5877411840231360000 : ℝ) * (((4 * R ^ 2) * (4 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2)) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * ((1 - R ^ 2 + ((-37 / 100 : ℝ) * R) ^ 2 + (((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 + 2 * ((R - 1 / (2 * R)) - ((-37 / 100 : ℝ) * R)) * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))))) / (2 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) ^ 2) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) * (((37 / 20 : ℝ) * R - 389 / 500))))) := by rw [hid]; positivity
  have hfin : 0 < ((4 * R ^ 2) * (4 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2)) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * ((1 - R ^ 2 + ((-37 / 100 : ℝ) * R) ^ 2 + (((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 + 2 * ((R - 1 / (2 * R)) - ((-37 / 100 : ℝ) * R)) * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))))) / (2 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) ^ 2) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) * (((37 / 20 : ℝ) * R - 389 / 500)))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * ((1 - R ^ 2 + ((-37 / 100 : ℝ) * R) ^ 2 + (((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 + 2 * ((R - 1 / (2 * R)) - ((-37 / 100 : ℝ) * R)) * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))))) / (2 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) ^ 2) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) * (((37 / 20 : ℝ) * R - 389 / 500))) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma wnp_hi_U_0_0 {R s : ℝ} (hRlo : (121 / 200 : ℝ) ≤ R) (hRhi : R ≤ (627 / 1000 : ℝ))
    (hslo : (9 / 20 : ℝ) ≤ s) (hshi : s ≤ (29 / 50 : ℝ)) :
    ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * ((1 - R ^ 2 + ((-37 / 100 : ℝ) * R) ^ 2 + (((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 + 2 * ((R - 1 / (2 * R)) - ((-37 / 100 : ℝ) * R)) * (0)) / (2 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (0) ^ 2) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (0) * (0) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hs : (0 : ℝ) < s := by linarith
  have hr1_pos : (0 : ℝ) < ((145 / 100 : ℝ) * R + 52 / 1000) := by linarith
  have hA_pos : (0 : ℝ) < ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) := by positivity
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  set p : ℝ := s - (9 / 20 : ℝ)
  set q : ℝ := (29 / 50 : ℝ) - s
  have ht : 0 ≤ t := sub_nonneg.mpr hRlo
  have hu : 0 ≤ u := sub_nonneg.mpr hRhi
  have hp : 0 ≤ p := sub_nonneg.mpr hslo
  have hq : 0 ≤ q := sub_nonneg.mpr hshi
  have hden : (0 : ℝ) < 4 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 := by positivity
  have hid : (747286947264000000 : ℝ) * ((4 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * ((1 - R ^ 2 + ((-37 / 100 : ℝ) * R) ^ 2 + (((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 + 2 * ((R - 1 / (2 * R)) - ((-37 / 100 : ℝ) * R)) * (0)) / (2 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (0) ^ 2) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (0) * (0)))) = (149457389452800000 : ℝ) + u ^ 6 * ((615787352790825372660908203125 : ℝ) * q ^ 3 + (2089215230915976532181787109375 : ℝ) * p * q ^ 2 + (2309736994256869708406375000000 : ℝ) * p ^ 2 * q + (833628885576048271803367187500 : ℝ) * p ^ 3) + t * u ^ 5 * ((3872302985486588433664000781250 : ℝ) * q ^ 3 + (13052469664876956373835687343750 : ℝ) * p * q ^ 2 + (14349703973543653917774162000000 : ℝ) * p ^ 2 * q + (5152774779218943102841348875000 : ℝ) * p ^ 3) + t ^ 2 * u ^ 4 * ((10109109883095753263171565046875 : ℝ) * q ^ 3 + (33869194873608152237844470240625 : ℝ) * p * q ^ 2 + (37038005725012654497203960520000 : ℝ) * p ^ 2 * q + (13234236916875997341970877732500 : ℝ) * p ^ 3) + t ^ 3 * u ^ 3 * ((14028043757988600483018140737500 : ℝ) * q ^ 3 + (46732516673856649630272137652500 : ℝ) * p * q ^ 2 + (50845236095377461178118296288000 : ℝ) * p ^ 2 * q + (18080044028418228840466603898000 : ℝ) * p ^ 3) + t ^ 4 * u ^ 2 * ((10915666152477192486161624806875 : ℝ) * q ^ 3 + (36168758493224580119843885648625 : ℝ) * p * q ^ 2 + (39158551415382879593318173185600 : ℝ) * p ^ 2 * q + (13857982689478538776241642430100 : ℝ) * p ^ 3) + t ^ 5 * u * ((4516849506543911510763287117250 : ℝ) * q ^ 3 + (14889688612575265344213498812550 : ℝ) * p * q ^ 2 + (16043318427932221100791886636160 : ℝ) * p ^ 2 * q + (5650679923131634873554928026360 : ℝ) * p ^ 3) + t ^ 6 * ((776632860788115900494677415925 : ℝ) * q ^ 3 + (2547506350235442440266877599615 : ℝ) * p * q ^ 2 + (2731964357952477675731382373568 : ℝ) * p ^ 2 * q + (957650237028744977004087594028 : ℝ) * p ^ 3) := by
    set A_var : ℝ := ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R)))
    have h_A_var : A_var ≠ 0 := (hA_pos).ne'
    field_simp [hR.ne', h_A_var]
    dsimp only [A_var, t, u, p, q]; ring
  clear_value t u p q
  have hpos : 0 < (747286947264000000 : ℝ) * ((4 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * ((1 - R ^ 2 + ((-37 / 100 : ℝ) * R) ^ 2 + (((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 + 2 * ((R - 1 / (2 * R)) - ((-37 / 100 : ℝ) * R)) * (0)) / (2 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (0) ^ 2) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (0) * (0)))) := by rw [hid]; positivity
  have hfin : 0 < (4 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * ((1 - R ^ 2 + ((-37 / 100 : ℝ) * R) ^ 2 + (((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 + 2 * ((R - 1 / (2 * R)) - ((-37 / 100 : ℝ) * R)) * (0)) / (2 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (0) ^ 2) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (0) * (0))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * ((1 - R ^ 2 + ((-37 / 100 : ℝ) * R) ^ 2 + (((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 + 2 * ((R - 1 / (2 * R)) - ((-37 / 100 : ℝ) * R)) * (0)) / (2 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (0) ^ 2) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (0) * (0)) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma wnp_hi_U_0_tau {R s : ℝ} (hRlo : (121 / 200 : ℝ) ≤ R) (hRhi : R ≤ (627 / 1000 : ℝ))
    (hslo : (9 / 20 : ℝ) ≤ s) (hshi : s ≤ (29 / 50 : ℝ)) :
    ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * ((1 - R ^ 2 + ((-37 / 100 : ℝ) * R) ^ 2 + (((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 + 2 * ((R - 1 / (2 * R)) - ((-37 / 100 : ℝ) * R)) * (0)) / (2 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (0) ^ 2) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500)) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hs : (0 : ℝ) < s := by linarith
  have hr1_pos : (0 : ℝ) < ((145 / 100 : ℝ) * R + 52 / 1000) := by linarith
  have hA_pos : (0 : ℝ) < ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) := by positivity
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  set p : ℝ := s - (9 / 20 : ℝ)
  set q : ℝ := (29 / 50 : ℝ) - s
  have ht : 0 ≤ t := sub_nonneg.mpr hRlo
  have hu : 0 ≤ u := sub_nonneg.mpr hRhi
  have hp : 0 ≤ p := sub_nonneg.mpr hslo
  have hq : 0 ≤ q := sub_nonneg.mpr hshi
  have hden : (0 : ℝ) < 4 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 := by positivity
  have hid : (747286947264000000 : ℝ) * ((4 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * ((1 - R ^ 2 + ((-37 / 100 : ℝ) * R) ^ 2 + (((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 + 2 * ((R - 1 / (2 * R)) - ((-37 / 100 : ℝ) * R)) * (0)) / (2 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (0) ^ 2) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500))))) = (149457389452800000 : ℝ) + u ^ 6 * ((815576331611576138259404296875 : ℝ) * q ^ 3 + (2879249778597127594303650390625 : ℝ) * p * q ^ 2 + (3320352549528096197641025000000 : ℝ) * p ^ 2 * q + (1255292684206273399570782812500 : ℝ) * p ^ 3) + t * u ^ 5 * ((5137575057504399789348124218750 : ℝ) * q ^ 3 + (18056650247342436498132087656250 : ℝ) * p * q ^ 2 + (20752432187202525379097118000000 : ℝ) * p ^ 2 * q + (7824848900355462855927031125000 : ℝ) * p ^ 3) + t ^ 2 * u ^ 4 * ((13446585762662229058127122453125 : ℝ) * q ^ 3 + (47071293915268199857466612259375 : ℝ) * p * q ^ 2 + (53933421353465320360862943480000 : ℝ) * p ^ 2 * q + (20286966023640269336412956267500 : ℝ) * p ^ 3) + t ^ 3 * u ^ 3 * ((18721426352771645215707609262500 : ℝ) * q ^ 3 + (65301490808663490808481224347500 : ℝ) * p * q ^ 2 + (74614142667256169702947566112000 : ℝ) * p ^ 2 * q + (28004442830247214560260866502000 : ℝ) * p ^ 3) + t ^ 4 * u ^ 2 * ((14626855108880964971410582693125 : ℝ) * q ^ 3 + (50854416894257463588544320051375 : ℝ) * p * q ^ 2 + (57960883061362034660033707454400 : ℝ) * p ^ 2 * q + (21710613548688616376693357009900 : ℝ) * p ^ 3) + t ^ 5 * u * ((6081356779938424446785349882750 : ℝ) * q ^ 3 + (21081784029524323011343844187450 : ℝ) * p * q ^ 2 + (23972977440803563332016007763840 : ℝ) * p ^ 2 * q + (8963274147285920482364530373640 : ℝ) * p ^ 3) + t ^ 6 * ((1051340986638160728798152844075 : ℝ) * q ^ 3 + (3634964496020904989821921308385 : ℝ) * p * q ^ 2 + (4124895329433401623728952692032 : ℝ) * p ^ 2 * q + (1539693620855198710066881503572 : ℝ) * p ^ 3) := by
    set A_var : ℝ := ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R)))
    have h_A_var : A_var ≠ 0 := (hA_pos).ne'
    field_simp [hR.ne', h_A_var]
    dsimp only [A_var, t, u, p, q]; ring
  clear_value t u p q
  have hpos : 0 < (747286947264000000 : ℝ) * ((4 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * ((1 - R ^ 2 + ((-37 / 100 : ℝ) * R) ^ 2 + (((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 + 2 * ((R - 1 / (2 * R)) - ((-37 / 100 : ℝ) * R)) * (0)) / (2 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (0) ^ 2) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500))))) := by rw [hid]; positivity
  have hfin : 0 < (4 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * ((1 - R ^ 2 + ((-37 / 100 : ℝ) * R) ^ 2 + (((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 + 2 * ((R - 1 / (2 * R)) - ((-37 / 100 : ℝ) * R)) * (0)) / (2 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (0) ^ 2) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500)))) := pos_of_mul_pos_right hpos (by positivity)
  have hfin2 : 0 < 1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * ((1 - R ^ 2 + ((-37 / 100 : ℝ) * R) ^ 2 + (((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) - (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))) ^ 2 + 2 * ((R - 1 / (2 * R)) - ((-37 / 100 : ℝ) * R)) * (0)) / (2 * ((9 / 10 : ℝ) * R + (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R))))) ^ 2 + (0) ^ 2) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (0) * (((37 / 20 : ℝ) * R - 389 / 500))) := pos_of_mul_pos_right hfin hden.le
  linarith

private lemma wnp_hi_p0_xmin_0 {R s : ℝ} (hRlo : (121 / 200 : ℝ) ≤ R) (hRhi : R ≤ (627 / 1000 : ℝ))
    (hslo : (9 / 20 : ℝ) ≤ s) (hshi : s ≤ (29 / 50 : ℝ)) :
    ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))) * ((R - 1)) + ((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * ((R - 1)) * (0) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hs : (0 : ℝ) < s := by linarith
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  set p : ℝ := s - (9 / 20 : ℝ)
  set q : ℝ := (29 / 50 : ℝ) - s
  have ht : 0 ≤ t := sub_nonneg.mpr hRlo
  have hu : 0 ≤ u := sub_nonneg.mpr hRhi
  have hp : 0 ≤ p := sub_nonneg.mpr hslo
  have hq : 0 ≤ q := sub_nonneg.mpr hshi
  have hid : (319004400 : ℝ) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))) * ((R - 1)) + ((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * ((R - 1)) * (0))) = (31900440 : ℝ) + u ^ 2 * ((95583532773825 : ℝ) * q ^ 3 + (273585358958225 : ℝ) * p * q ^ 2 + (260801150374975 : ℝ) * p ^ 2 * q + (82759778190575 : ℝ) * p ^ 3) + t * u * ((186992500373310 : ℝ) * q ^ 3 + (533486582741630 : ℝ) * p * q ^ 2 + (506696825083330 : ℝ) * p ^ 2 * q + (160123650715010 : ℝ) * p ^ 3) + t ^ 2 * ((91015981550337 : ℝ) * q ^ 3 + (258643166072561 : ℝ) * p * q ^ 2 + (244558517434111 : ℝ) * p ^ 2 * q + (76891786911887 : ℝ) * p ^ 3) := by dsimp only [t, u, p, q]; ring
  clear_value t u p q
  have hpos : 0 < (319004400 : ℝ) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))) * ((R - 1)) + ((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * ((R - 1)) * (0))) := by rw [hid]; positivity
  have hfin : 0 < 1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))) * ((R - 1)) + ((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * ((R - 1)) * (0)) := pos_of_mul_pos_right hpos (by positivity)
  linarith

private lemma wnp_hi_p0_xmin_tau {R s : ℝ} (hRlo : (121 / 200 : ℝ) ≤ R) (hRhi : R ≤ (627 / 1000 : ℝ))
    (hslo : (9 / 20 : ℝ) ≤ s) (hshi : s ≤ (29 / 50 : ℝ)) :
    ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))) * ((R - 1)) + ((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * ((R - 1)) * (((37 / 20 : ℝ) * R - 389 / 500)) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hs : (0 : ℝ) < s := by linarith
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  set p : ℝ := s - (9 / 20 : ℝ)
  set q : ℝ := (29 / 50 : ℝ) - s
  have ht : 0 ≤ t := sub_nonneg.mpr hRlo
  have hu : 0 ≤ u := sub_nonneg.mpr hRhi
  have hp : 0 ≤ p := sub_nonneg.mpr hslo
  have hq : 0 ≤ q := sub_nonneg.mpr hshi
  have hid : (319004400 : ℝ) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))) * ((R - 1)) + ((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * ((R - 1)) * (((37 / 20 : ℝ) * R - 389 / 500)))) = (19140264 : ℝ) + u ^ 2 * ((34560776148825 : ℝ) * q ^ 3 + (96572570333225 : ℝ) * p * q ^ 2 + (89843842999975 : ℝ) * p ^ 2 * q + (27792502815575 : ℝ) * p ^ 3) + t * u * ((61678918583310 : ℝ) * q ^ 3 + (171101242871630 : ℝ) * p * q ^ 2 + (157866890713330 : ℝ) * p ^ 2 * q + (48365474425010 : ℝ) * p ^ 3) + t ^ 2 * ((27374110070937 : ℝ) * q ^ 3 + (75303613364361 : ℝ) * p * q ^ 2 + (68805026455911 : ℝ) * p ^ 2 * q + (20835977162487 : ℝ) * p ^ 3) := by dsimp only [t, u, p, q]; ring
  clear_value t u p q
  have hpos : 0 < (319004400 : ℝ) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))) * ((R - 1)) + ((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * ((R - 1)) * (((37 / 20 : ℝ) * R - 389 / 500)))) := by rw [hid]; positivity
  have hfin : 0 < 1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * ((R - 1))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))) * ((R - 1)) + ((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * ((R - 1)) * (((37 / 20 : ℝ) * R - 389 / 500))) := pos_of_mul_pos_right hpos (by positivity)
  linarith

private lemma wnp_hi_p0_xm_0 {R s : ℝ} (hRlo : (121 / 200 : ℝ) ≤ R) (hRhi : R ≤ (627 / 1000 : ℝ))
    (hslo : (9 / 20 : ℝ) ≤ s) (hshi : s ≤ (29 / 50 : ℝ)) :
    ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))) * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) + ((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) * (0) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hs : (0 : ℝ) < s := by linarith
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  set p : ℝ := s - (9 / 20 : ℝ)
  set q : ℝ := (29 / 50 : ℝ) - s
  have ht : 0 ≤ t := sub_nonneg.mpr hRlo
  have hu : 0 ≤ u := sub_nonneg.mpr hRhi
  have hp : 0 ≤ p := sub_nonneg.mpr hslo
  have hq : 0 ≤ q := sub_nonneg.mpr hshi
  have hid : (319004400 : ℝ) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))) * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) + ((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) * (0))) = (15950220 : ℝ) + u ^ 2 * ((21889200851175 : ℝ) * q ^ 3 + (59446120666775 : ℝ) * p * q ^ 2 + (54871608000025 : ℝ) * p ^ 2 * q + (17354234184425 : ℝ) * p ^ 3) + t * u * ((48852585816690 : ℝ) * q ^ 3 + (134522910328370 : ℝ) * p * q ^ 2 + (125842902486670 : ℝ) * p ^ 2 * q + (40251669974990 : ℝ) * p ^ 3) + t ^ 2 * ((27027612369063 : ℝ) * q ^ 3 + (75237265955639 : ℝ) * p * q ^ 2 + (71099564864089 : ℝ) * p ^ 2 * q + (22929457277513 : ℝ) * p ^ 3) := by dsimp only [t, u, p, q]; ring
  clear_value t u p q
  have hpos : 0 < (319004400 : ℝ) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))) * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) + ((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) * (0))) := by rw [hid]; positivity
  have hfin : 0 < 1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))) * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) + ((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (0) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) * (0)) := pos_of_mul_pos_right hpos (by positivity)
  linarith

private lemma wnp_hi_p0_xm_tau {R s : ℝ} (hRlo : (121 / 200 : ℝ) ≤ R) (hRhi : R ≤ (627 / 1000 : ℝ))
    (hslo : (9 / 20 : ℝ) ≤ s) (hshi : s ≤ (29 / 50 : ℝ)) :
    ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))) * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) + ((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) * (((37 / 20 : ℝ) * R - 389 / 500)) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have hs : (0 : ℝ) < s := by linarith
  set t : ℝ := R - (121 / 200 : ℝ)
  set u : ℝ := (627 / 1000 : ℝ) - R
  set p : ℝ := s - (9 / 20 : ℝ)
  set q : ℝ := (29 / 50 : ℝ) - s
  have ht : 0 ≤ t := sub_nonneg.mpr hRlo
  have hu : 0 ≤ u := sub_nonneg.mpr hRhi
  have hp : 0 ≤ p := sub_nonneg.mpr hslo
  have hq : 0 ≤ q := sub_nonneg.mpr hshi
  have hid : (1595022000 : ℝ) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))) * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) + ((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) * (((37 / 20 : ℝ) * R - 389 / 500)))) = (1595022 : ℝ) + u ^ 2 * ((36070127380875 : ℝ) * q ^ 3 + (67454128958875 : ℝ) * p * q ^ 2 + (34932721875125 : ℝ) * p ^ 2 * q + (3746450297125 : ℝ) * p ^ 3) + t * u * ((76456287633450 : ℝ) * q ^ 3 + (152357254791850 : ℝ) * p * q ^ 2 + (92119843083350 : ℝ) * p ^ 2 * q + (16614335924950 : ℝ) * p ^ 3) + t ^ 2 * ((40285402698315 : ℝ) * q ^ 3 + (84870510987195 : ℝ) * p * q ^ 2 + (57424164179445 : ℝ) * p ^ 2 * q + (13036785890565 : ℝ) * p ^ 3) := by dsimp only [t, u, p, q]; ring
  clear_value t u p q
  have hpos : 0 < (1595022000 : ℝ) * (1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))) * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) + ((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) * (((37 / 20 : ℝ) * R - 389 / 500)))) := by rw [hid]; positivity
  have hfin : 0 < 1 - (((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))))) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))) * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) + ((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ))) ^ 2)) + ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * (((37 / 20 : ℝ) * R - 389 / 500)) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (((-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - (29 / 50 : ℝ)))) * (((37 / 20 : ℝ) * R - 389 / 500))) := pos_of_mul_pos_right hpos (by positivity)
  linarith

-- Main geometric assembly for Borsuk 4D H1 (4/7 < R <= 627/1000)

private lemma r1_lower_lo {R t1 r1 : ℝ} (hlo : (4 / 7 : ℝ) ≤ R) (hhi : R ≤ 121 / 200)
    (hr1 : 0 ≤ r1) (hsq : r1 ^ 2 + t1 ^ 2 = R ^ 2)
    (ht1_hi : t1 ≤ -R / 4) (ht1_lo : R - 1 / (2 * R) ≤ t1) :
    ((245 / 100 : ℝ) * R - 554 / 1000) * R ≤ r1 := by
  have hR : (0 : ℝ) < R := by linarith
  have ht1_neg : t1 ≤ 0 := by linarith
  have htsq : t1 ^ 2 ≤ (R - 1 / (2 * R)) ^ 2 := by nlinarith only [ht1_neg, ht1_lo]
  have hr1_sq : 1 - 1 / (4 * R ^ 2) ≤ r1 ^ 2 := by
    have h1 : R ^ 2 - (R - 1 / (2 * R)) ^ 2 = 1 - 1 / (4 * R ^ 2) := by field_simp; ring
    linarith only [hsq, htsq, h1]
  have hpoly := r1R_lo_bound hlo hhi
  have hcmp : (((245 / 100 : ℝ) * R - 554 / 1000) * R) ^ 2 < 1 - 1 / (4 * R ^ 2) := by
    have hden : (0 : ℝ) < 4 * R ^ 2 := by positivity
    have hmul : (4 * R ^ 2) * (1 - 1 / (4 * R ^ 2) - (((245 / 100 : ℝ) * R - 554 / 1000) * R) ^ 2) =
        4 * R ^ 2 - 1 - 4 * R ^ 4 * ((245 / 100 : ℝ) * R - 554 / 1000) ^ 2 := by field_simp
    have hpos : 0 < 1 - 1 / (4 * R ^ 2) - (((245 / 100 : ℝ) * R - 554 / 1000) * R) ^ 2 :=
      pos_of_mul_pos_right (hmul.symm ▸ hpoly) hden.le
    linarith only [hpos]
  have hnn : 0 ≤ ((245 / 100 : ℝ) * R - 554 / 1000) * R := by nlinarith only [hlo, hR]
  nlinarith only [hr1, hr1_sq, hcmp, hnn]

private lemma r1_lower_hi {R t1 r1 : ℝ} (hlo : (121 / 200 : ℝ) ≤ R) (hhi : R ≤ 627 / 1000)
    (hr1 : 0 ≤ r1) (hsq : r1 ^ 2 + t1 ^ 2 = R ^ 2)
    (ht1_hi : t1 ≤ -R / 4) (ht1_lo : R - 1 / (2 * R) ≤ t1) :
    ((145 / 100 : ℝ) * R + 52 / 1000) * R ≤ r1 := by
  have hR : (0 : ℝ) < R := by linarith
  have ht1_neg : t1 ≤ 0 := by linarith
  have htsq : t1 ^ 2 ≤ (R - 1 / (2 * R)) ^ 2 := by nlinarith only [ht1_neg, ht1_lo]
  have hr1_sq : 1 - 1 / (4 * R ^ 2) ≤ r1 ^ 2 := by
    have h1 : R ^ 2 - (R - 1 / (2 * R)) ^ 2 = 1 - 1 / (4 * R ^ 2) := by field_simp; ring
    linarith only [hsq, htsq, h1]
  have hpoly := r1R_hi_bound hlo hhi
  have hcmp : (((145 / 100 : ℝ) * R + 52 / 1000) * R) ^ 2 < 1 - 1 / (4 * R ^ 2) := by
    have hden : (0 : ℝ) < 4 * R ^ 2 := by positivity
    have hmul : (4 * R ^ 2) * (1 - 1 / (4 * R ^ 2) - (((145 / 100 : ℝ) * R + 52 / 1000) * R) ^ 2) =
        4 * R ^ 2 - 1 - 4 * R ^ 4 * ((145 / 100 : ℝ) * R + 52 / 1000) ^ 2 := by field_simp
    have hpos : 0 < 1 - 1 / (4 * R ^ 2) - (((145 / 100 : ℝ) * R + 52 / 1000) * R) ^ 2 :=
      pos_of_mul_pos_right (hmul.symm ▸ hpoly) hden.le
    linarith only [hpos]
  have hnn : 0 ≤ ((145 / 100 : ℝ) * R + 52 / 1000) * R := by nlinarith only [hlo, hR]
  nlinarith only [hr1, hr1_sq, hcmp, hnn]

private lemma cap_rad_sq_lt_quarter {R : ℝ} :
    R ^ 2 - ((37 / 20 : ℝ) * R - 389 / 500) ^ 2 < 1 / 4 := by
  have hid : (1 / 4 : ℝ) - (R ^ 2 - ((37 / 20 : ℝ) * R - 389 / 500) ^ 2) =
      (969 / 400 : ℝ) * (R - 14393 / 24225) ^ 2 + 341 / 2422500 := by ring
  nlinarith only [hid, sq_nonneg (R - 14393 / 24225)]

private lemma north_opp_lt_one {R x3 y3 nx2 ny2 : ℝ}
    (hRlo : (4 / 7 : ℝ) ≤ R) (hRhi : R ≤ 627 / 1000)
    (hx_lo : -R ≤ x3) (hx_hi : x3 ≤ 0) (hy_lo : 0 ≤ y3) (hy_hi : y3 ≤ (37 / 20 : ℝ) * R - 389 / 500)
    (hbx : nx2 ≤ R ^ 2) (hby : ny2 ≤ R ^ 2) (hp0x : nx2 ≤ 1 - R ^ 2 + 2 * R * x3) :
    (10 / 9 : ℝ) * (nx2 + ny2) - 2 * x3 * y3 - (1 / 9 : ℝ) * (x3 ^ 2 + y3 ^ 2) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have htx : -x3 ^ 2 ≤ -2 * (-1 / 5 : ℝ) * x3 + (-1 / 5 : ℝ) ^ 2 := by nlinarith only [sq_nonneg (x3 - (-1 / 5 : ℝ))]
  have hty : -y3 ^ 2 ≤ -2 * (7 / 20 : ℝ) * y3 + (7 / 20 : ℝ) ^ 2 := by nlinarith only [sq_nonneg (y3 - (7 / 20 : ℝ))]
  let b0 : ℝ := R - 1 / (2 * R)
  by_cases hsplit : b0 ≤ x3
  · have hbound : (10 / 9 : ℝ) * (nx2 + ny2) - 2 * x3 * y3 - (1 / 9 : ℝ) * (x3 ^ 2 + y3 ^ 2) ≤
        0 * x3 ^ 2 + ((1 / 9 : ℝ) * (-2 * (-1 / 5 : ℝ))) * x3 +
        0 * y3 ^ 2 + ((1 / 9 : ℝ) * (-2 * (7 / 20 : ℝ))) * y3 +
        ((20 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * ((-1 / 5 : ℝ) ^ 2 + (7 / 20 : ℝ) ^ 2)) + (-2) * x3 * y3 := by
      linarith only [hbx, hby, htx, hty]
    have hlt := convex_2d_lt (Ax := 0) (Ay := 0)
      (Bx := (1 / 9 : ℝ) * (-2 * (-1 / 5 : ℝ)))
      (By := (1 / 9 : ℝ) * (-2 * (7 / 20 : ℝ)))
      (C := (20 / 9 : ℝ) * R ^ 2 + (1 / 9 : ℝ) * ((-1 / 5 : ℝ) ^ 2 + (7 / 20 : ℝ) ^ 2))
      (D := -2) le_rfl le_rfl hsplit hx_hi hy_lo hy_hi
      (by convert north_c_b0_0 hRlo hRhi using 1; dsimp only [b0]; ring)
      (by convert north_c_b0_tau hRlo hRhi using 1; dsimp only [b0]; ring)
      (by convert north_c_0_0 hRlo hRhi using 1; ring)
      (by convert north_c_0_tau hRlo hRhi using 1; ring)
    linarith only [hbound, hlt]
  · have hx_le_b0 : x3 ≤ b0 := le_of_not_ge hsplit
    have hbound : (10 / 9 : ℝ) * (nx2 + ny2) - 2 * x3 * y3 - (1 / 9 : ℝ) * (x3 ^ 2 + y3 ^ 2) ≤
        0 * x3 ^ 2 + ((20 / 9 : ℝ) * R + (1 / 9 : ℝ) * (-2 * (-1 / 5 : ℝ))) * x3 +
        0 * y3 ^ 2 + ((1 / 9 : ℝ) * (-2 * (7 / 20 : ℝ))) * y3 +
        ((10 / 9 : ℝ) + (1 / 9 : ℝ) * ((-1 / 5 : ℝ) ^ 2 + (7 / 20 : ℝ) ^ 2)) + (-2) * x3 * y3 := by
      linarith only [hp0x, hby, htx, hty]
    have hb0_eq : 1 - R ^ 2 + 2 * R * b0 = R ^ 2 := by dsimp only [b0]; field_simp [hR.ne']; ring
    have hlt := convex_2d_lt (Ax := 0) (Ay := 0)
      (Bx := (20 / 9 : ℝ) * R + (1 / 9 : ℝ) * (-2 * (-1 / 5 : ℝ)))
      (By := (1 / 9 : ℝ) * (-2 * (7 / 20 : ℝ)))
      (C := (10 / 9 : ℝ) + (1 / 9 : ℝ) * ((-1 / 5 : ℝ) ^ 2 + (7 / 20 : ℝ) ^ 2))
      (D := -2) le_rfl le_rfl hx_lo hx_le_b0 hy_lo hy_hi
      (by convert north_c_mR_0 hRlo hRhi using 1; ring)
      (by convert north_c_mR_tau hRlo hRhi using 1; ring)
      (by convert north_c_b0_0 hRlo hRhi using 1; dsimp only [b0]; field_simp [hR.ne']; ring)
      (by convert north_c_b0_tau hRlo hRhi using 1; dsimp only [b0]; field_simp [hR.ne']; ring)
    linarith only [hbound, hlt]

private lemma south_pp_lt_one {R x3 y3 u v r1R : ℝ}
    (hRlo : (4 / 7 : ℝ) ≤ R) (_hRhi : R ≤ 627 / 1000)
    (hx0 : 0 ≤ x3) (hx1 : x3 ≤ (37 / 20 : ℝ) * R - 389 / 500)
    (hy0 : 0 ≤ y3) (hy1 : y3 ≤ (37 / 20 : ℝ) * R - 389 / 500)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huR : u ≤ R) (hvR : v ≤ R)
    (hr1R : 0 < r1R)
    (hp1x : u ^ 2 + 2 * (29 / 50 : ℝ) * (r1R * R) * u ≤ 1 - R ^ 2 - (1 / 2 : ℝ) * R * x3 - x3 ^ 2)
    (hp1y : v ^ 2 + 2 * (29 / 50 : ℝ) * (r1R * R) * v ≤ 1 - R ^ 2 - (1 / 2 : ℝ) * R * y3 - y3 ^ 2)
    (hD_big : (1659 / 1250 : ℝ) ≤ 1 + 2 * (29 / 50 : ℝ) * r1R)
    (h00 : ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * 0) / (1 + 2 * (29 / 50 : ℝ) * r1R) +
        (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * r1R)) * (((37 / 20 : ℝ) * R - 389 / 500) * 0)) +
      ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * 0) / (1 + 2 * (29 / 50 : ℝ) * r1R) +
        (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * r1R)) * (((37 / 20 : ℝ) * R - 389 / 500) * 0)) -
      2 * 0 * 0 < 1)
    (h01 : ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * 0) / (1 + 2 * (29 / 50 : ℝ) * r1R) +
        (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * r1R)) * (((37 / 20 : ℝ) * R - 389 / 500) * 0)) +
      ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * ((37 / 20 : ℝ) * R - 389 / 500)) / (1 + 2 * (29 / 50 : ℝ) * r1R) +
        (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * r1R)) * (((37 / 20 : ℝ) * R - 389 / 500) * ((37 / 20 : ℝ) * R - 389 / 500))) -
      2 * 0 * ((37 / 20 : ℝ) * R - 389 / 500) < 1)
    (h11 : ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * ((37 / 20 : ℝ) * R - 389 / 500)) / (1 + 2 * (29 / 50 : ℝ) * r1R) +
        (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * r1R)) * (((37 / 20 : ℝ) * R - 389 / 500) * ((37 / 20 : ℝ) * R - 389 / 500))) +
      ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * ((37 / 20 : ℝ) * R - 389 / 500)) / (1 + 2 * (29 / 50 : ℝ) * r1R) +
        (1 - (1659 / 1250 : ℝ) / (1 + 2 * (29 / 50 : ℝ) * r1R)) * (((37 / 20 : ℝ) * R - 389 / 500) * ((37 / 20 : ℝ) * R - 389 / 500))) -
      2 * ((37 / 20 : ℝ) * R - 389 / 500) * ((37 / 20 : ℝ) * R - 389 / 500) < 1) :
    (x3 - y3) ^ 2 + (1659 / 1250 : ℝ) * (u ^ 2 + v ^ 2) < 1 := by
  have hR : (0 : ℝ) < R := by linarith only [hRlo]
  let D : ℝ := 1 + 2 * (29 / 50 : ℝ) * r1R
  have hD : 0 < D := by dsimp only [D]; positivity
  let τ : ℝ := (37 / 20 : ℝ) * R - 389 / 500
  have hu2 := u_sq_le_div_p1 hu huR hR (by norm_num) hr1R.le hp1x
  have hv2 := u_sq_le_div_p1 hv hvR hR (by norm_num) hr1R.le hp1y
  have hcx : 0 ≤ 1 - (1659 / 1250 : ℝ) / D := by
    rw [sub_nonneg, div_le_one hD]; exact hD_big
  have hx2 : x3 ^ 2 ≤ τ * x3 := by dsimp only [τ]; nlinarith only [hx0, hx1]
  have hy2 : y3 ^ 2 ≤ τ * y3 := by dsimp only [τ]; nlinarith only [hy0, hy1]
  have hfx : (1659 / 1250 : ℝ) * u ^ 2 + x3 ^ 2 ≤
      (1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * x3) / D + (1 - (1659 / 1250 : ℝ) / D) * (τ * x3) := by
    have h1 : (1659 / 1250 : ℝ) * u ^ 2 ≤ (1659 / 1250 : ℝ) * ((1 - R ^ 2 - (1 / 2 : ℝ) * R * x3 - x3 ^ 2) / D) :=
      mul_le_mul_of_nonneg_left hu2 (by norm_num)
    have h2 : (1659 / 1250 : ℝ) * ((1 - R ^ 2 - (1 / 2 : ℝ) * R * x3 - x3 ^ 2) / D) + x3 ^ 2 =
        (1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * x3) / D + (1 - (1659 / 1250 : ℝ) / D) * x3 ^ 2 := by
      field_simp [hD.ne']; ring
    have h3 : (1 - (1659 / 1250 : ℝ) / D) * x3 ^ 2 ≤ (1 - (1659 / 1250 : ℝ) / D) * (τ * x3) :=
      mul_le_mul_of_nonneg_left hx2 hcx
    linarith only [h1, h2, h3]
  have hfy : (1659 / 1250 : ℝ) * v ^ 2 + y3 ^ 2 ≤
      (1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * y3) / D + (1 - (1659 / 1250 : ℝ) / D) * (τ * y3) := by
    have h1 : (1659 / 1250 : ℝ) * v ^ 2 ≤ (1659 / 1250 : ℝ) * ((1 - R ^ 2 - (1 / 2 : ℝ) * R * y3 - y3 ^ 2) / D) :=
      mul_le_mul_of_nonneg_left hv2 (by norm_num)
    have h2 : (1659 / 1250 : ℝ) * ((1 - R ^ 2 - (1 / 2 : ℝ) * R * y3 - y3 ^ 2) / D) + y3 ^ 2 =
        (1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * y3) / D + (1 - (1659 / 1250 : ℝ) / D) * y3 ^ 2 := by
      field_simp [hD.ne']; ring
    have h3 : (1 - (1659 / 1250 : ℝ) / D) * y3 ^ 2 ≤ (1 - (1659 / 1250 : ℝ) / D) * (τ * y3) :=
      mul_le_mul_of_nonneg_left hy2 hcx
    linarith only [h1, h2, h3]
  have hlt := convex_2d_lt (Ax := 0) (Ay := 0)
    (Bx := -(1659 / 1250 : ℝ) * ((1 / 2 : ℝ) * R) / D + (1 - (1659 / 1250 : ℝ) / D) * τ)
    (By := -(1659 / 1250 : ℝ) * ((1 / 2 : ℝ) * R) / D + (1 - (1659 / 1250 : ℝ) / D) * τ)
    (C := 2 * ((1659 / 1250 : ℝ) * (1 - R ^ 2) / D))
    (D := -2) le_rfl le_rfl hx0 hx1 hy0 hy1
    (by convert h00 using 1; dsimp only [D, τ]; ring)
    (by convert h01 using 1; dsimp only [D, τ]; ring)
    (by convert h01 using 1; dsimp only [D, τ]; ring)
    (by convert h11 using 1; dsimp only [D, τ]; ring)
  have hsum : (x3 - y3) ^ 2 + (1659 / 1250 : ℝ) * (u ^ 2 + v ^ 2) =
      ((1659 / 1250 : ℝ) * u ^ 2 + x3 ^ 2) + ((1659 / 1250 : ℝ) * v ^ 2 + y3 ^ 2) - 2 * x3 * y3 := by ring
  have hlin : ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * x3) / D + (1 - (1659 / 1250 : ℝ) / D) * (τ * x3)) +
      ((1659 / 1250 : ℝ) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * y3) / D + (1 - (1659 / 1250 : ℝ) / D) * (τ * y3)) -
      2 * x3 * y3 =
      0 * x3 ^ 2 + (-(1659 / 1250 : ℝ) * ((1 / 2 : ℝ) * R) / D + (1 - (1659 / 1250 : ℝ) / D) * τ) * x3 +
      0 * y3 ^ 2 + (-(1659 / 1250 : ℝ) * ((1 / 2 : ℝ) * R) / D + (1 - (1659 / 1250 : ℝ) / D) * τ) * y3 +
      2 * ((1659 / 1250 : ℝ) * (1 - R ^ 2) / D) + (-2) * x3 * y3 := by ring
  linarith only [hsum, hfx, hfy, hlin, hlt]

private lemma south_opp_lt_one {R x3 y3 u v r1R : ℝ}
    (hRlo : (4 / 7 : ℝ) ≤ R) (_hRhi : R ≤ 627 / 1000)
    (hx_lo : R - 1 ≤ x3) (hx_hi : x3 ≤ 0)
    (hy_lo : 0 ≤ y3) (hy_hi : y3 ≤ (37 / 20 : ℝ) * R - 389 / 500)
    (_hu : 0 ≤ u) (hv : 0 ≤ v)
    (hbx : u ^ 2 + x3 ^ 2 ≤ R ^ 2)
    (hp0x : u ^ 2 + x3 ^ 2 ≤ 1 - R ^ 2 + 2 * R * x3)
    (hr1R : 0 < r1R)
    (hp1y : v ^ 2 + 2 * ((29 / 50 : ℝ) * (r1R * R)) * v ≤ 1 - R ^ 2 - (1 / 2 : ℝ) * R * y3 - y3 ^ 2)
    (h_p0_0 : ((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * (R - 1)) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * (R - 1) + (R - 1 / (2 * R)) ^ 2)) +
      ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + (29 / 50 : ℝ) * (r1R * R)) - (29 / 50 : ℝ) * (r1R * R)) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * 0) / (2 * ((4 / 5 : ℝ) * R + (29 / 50 : ℝ) * (r1R * R)))) ^ 2 + 0 ^ 2) - 2 * (R - 1) * 0 < 1)
    (h_p0_t : ((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * (R - 1)) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * (R - 1) + (R - 1 / (2 * R)) ^ 2)) +
      ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + (29 / 50 : ℝ) * (r1R * R)) - (29 / 50 : ℝ) * (r1R * R)) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * ((37 / 20 : ℝ) * R - 389 / 500)) / (2 * ((4 / 5 : ℝ) * R + (29 / 50 : ℝ) * (r1R * R)))) ^ 2 + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2) - 2 * (R - 1) * ((37 / 20 : ℝ) * R - 389 / 500) < 1)
    (h_tl_0 : ((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * (R - 1 / (2 * R))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * (R - 1 / (2 * R)) + (R - 1 / (2 * R)) ^ 2)) +
      ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + (29 / 50 : ℝ) * (r1R * R)) - (29 / 50 : ℝ) * (r1R * R)) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * 0) / (2 * ((4 / 5 : ℝ) * R + (29 / 50 : ℝ) * (r1R * R)))) ^ 2 + 0 ^ 2) - 2 * (R - 1 / (2 * R)) * 0 < 1)
    (h_tl_t : ((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * (R - 1 / (2 * R))) + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * (R - 1 / (2 * R)) + (R - 1 / (2 * R)) ^ 2)) +
      ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + (29 / 50 : ℝ) * (r1R * R)) - (29 / 50 : ℝ) * (r1R * R)) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * ((37 / 20 : ℝ) * R - 389 / 500)) / (2 * ((4 / 5 : ℝ) * R + (29 / 50 : ℝ) * (r1R * R)))) ^ 2 + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2) - 2 * (R - 1 / (2 * R)) * ((37 / 20 : ℝ) * R - 389 / 500) < 1)
    (h_b0_0 : ((1659 / 1250 : ℝ) * R ^ 2 + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * 0 + (R - 1 / (2 * R)) ^ 2)) +
      ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + (29 / 50 : ℝ) * (r1R * R)) - (29 / 50 : ℝ) * (r1R * R)) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * 0) / (2 * ((4 / 5 : ℝ) * R + (29 / 50 : ℝ) * (r1R * R)))) ^ 2 + 0 ^ 2) - 2 * 0 * 0 < 1)
    (h_b0_t : ((1659 / 1250 : ℝ) * R ^ 2 + (409 / 1250 : ℝ) * (-2 * (R - 1 / (2 * R)) * 0 + (R - 1 / (2 * R)) ^ 2)) +
      ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + ((3 / 10 : ℝ) * R) ^ 2 + (((4 / 5 : ℝ) * R + (29 / 50 : ℝ) * (r1R * R)) - (29 / 50 : ℝ) * (r1R * R)) ^ 2 - ((1 / 2 : ℝ) * R + 2 * ((3 / 10 : ℝ) * R)) * ((37 / 20 : ℝ) * R - 389 / 500)) / (2 * ((4 / 5 : ℝ) * R + (29 / 50 : ℝ) * (r1R * R)))) ^ 2 + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2) - 2 * 0 * ((37 / 20 : ℝ) * R - 389 / 500) < 1) :
    (x3 - y3) ^ 2 + (1659 / 1250 : ℝ) * (u ^ 2 + v ^ 2) < 1 := by
  have hR : (0 : ℝ) < R := by linarith only [hRlo]
  let b : ℝ := (29 / 50 : ℝ) * (r1R * R)
  let Ap : ℝ := (4 / 5 : ℝ) * R + b
  let y0 : ℝ := (3 / 10 : ℝ) * R
  let τ : ℝ := (37 / 20 : ℝ) * R - 389 / 500
  let tlo : ℝ := R - 1 / (2 * R)
  have hAp : 0 < Ap := by dsimp only [Ap, b]; positivity
  let U0 : ℝ := (1 - R ^ 2 + y0 ^ 2 + (Ap - b) ^ 2) / (2 * Ap)
  let U1 : ℝ := -((1 / 2 : ℝ) * R + 2 * y0) / (2 * Ap)
  have hv2 : v ^ 2 ≤ (U0 + U1 * y3) ^ 2 := by
    apply u_sq_le_U_sq hv hAp hp1y
    have htan : -y3 ^ 2 ≤ -2 * y0 * y3 + y0 ^ 2 := by nlinarith only [sq_nonneg (y3 - y0)]
    have heq : U0 + U1 * y3 = (1 - R ^ 2 + y0 ^ 2 + (Ap - b) ^ 2 - ((1 / 2 : ℝ) * R + 2 * y0) * y3) / (2 * Ap) := by
      dsimp only [U0, U1]; ring
    rw [heq]
    exact div_le_div_of_nonneg_right (by dsimp only [b]; linarith only [htan]) (by positivity)
  have hAy : (0 : ℝ) ≤ (1659 / 1250 : ℝ) * U1 ^ 2 + 1 := by positivity
  have htx : -x3 ^ 2 ≤ -2 * tlo * x3 + tlo ^ 2 := by nlinarith only [sq_nonneg (x3 - tlo)]
  have htlo_eq : 1 - R ^ 2 + 2 * R * tlo = R ^ 2 := by dsimp only [tlo]; field_simp [hR.ne']; ring
  have htlo_eq' : 1 - R ^ 2 + 2 * R * (R - 1 / (2 * R)) = R ^ 2 := htlo_eq
  have hsum : (x3 - y3) ^ 2 + (1659 / 1250 : ℝ) * (u ^ 2 + v ^ 2) =
      ((1659 / 1250 : ℝ) * (u ^ 2 + x3 ^ 2) - (409 / 1250 : ℝ) * x3 ^ 2) +
      ((1659 / 1250 : ℝ) * v ^ 2 + y3 ^ 2) - 2 * x3 * y3 := by ring
  have hfy : (1659 / 1250 : ℝ) * v ^ 2 + y3 ^ 2 ≤
      ((1659 / 1250 : ℝ) * U1 ^ 2 + 1) * y3 ^ 2 + (2 * (1659 / 1250 : ℝ) * U0 * U1) * y3 +
      (1659 / 1250 : ℝ) * U0 ^ 2 := by
    have h1 : (1659 / 1250 : ℝ) * v ^ 2 ≤ (1659 / 1250 : ℝ) * (U0 + U1 * y3) ^ 2 :=
      mul_le_mul_of_nonneg_left hv2 (by norm_num)
    have h2 : (1659 / 1250 : ℝ) * (U0 + U1 * y3) ^ 2 + y3 ^ 2 =
        ((1659 / 1250 : ℝ) * U1 ^ 2 + 1) * y3 ^ 2 + (2 * (1659 / 1250 : ℝ) * U0 * U1) * y3 +
        (1659 / 1250 : ℝ) * U0 ^ 2 := by ring
    linarith only [h1, h2]
  by_cases hsplit : tlo ≤ x3
  · have hfx : (1659 / 1250 : ℝ) * (u ^ 2 + x3 ^ 2) - (409 / 1250 : ℝ) * x3 ^ 2 ≤
        (1659 / 1250 : ℝ) * R ^ 2 + (409 / 1250 : ℝ) * (-2 * tlo * x3 + tlo ^ 2) := by
      linarith only [hbx, htx]
    have hlt := convex_2d_lt (Ax := 0) (Ay := (1659 / 1250 : ℝ) * U1 ^ 2 + 1)
      (Bx := (409 / 1250 : ℝ) * (-2 * tlo))
      (By := 2 * (1659 / 1250 : ℝ) * U0 * U1)
      (C := (1659 / 1250 : ℝ) * R ^ 2 + (409 / 1250 : ℝ) * tlo ^ 2 + (1659 / 1250 : ℝ) * U0 ^ 2)
      (D := -2) le_rfl hAy hsplit hx_hi hy_lo hy_hi
      (by convert h_tl_0 using 1; rw [htlo_eq']; dsimp only [U0, U1, Ap, b, y0, τ, tlo]; ring)
      (by convert h_tl_t using 1; rw [htlo_eq']; dsimp only [U0, U1, Ap, b, y0, τ, tlo]; ring)
      (by convert h_b0_0 using 1; dsimp only [U0, U1, Ap, b, y0, τ, tlo]; ring)
      (by convert h_b0_t using 1; dsimp only [U0, U1, Ap, b, y0, τ, tlo]; ring)
    have hlin : ((1659 / 1250 : ℝ) * R ^ 2 + (409 / 1250 : ℝ) * (-2 * tlo * x3 + tlo ^ 2)) +
        (((1659 / 1250 : ℝ) * U1 ^ 2 + 1) * y3 ^ 2 + (2 * (1659 / 1250 : ℝ) * U0 * U1) * y3 +
          (1659 / 1250 : ℝ) * U0 ^ 2) - 2 * x3 * y3 =
        0 * x3 ^ 2 + ((409 / 1250 : ℝ) * (-2 * tlo)) * x3 +
        ((1659 / 1250 : ℝ) * U1 ^ 2 + 1) * y3 ^ 2 + (2 * (1659 / 1250 : ℝ) * U0 * U1) * y3 +
        ((1659 / 1250 : ℝ) * R ^ 2 + (409 / 1250 : ℝ) * tlo ^ 2 + (1659 / 1250 : ℝ) * U0 ^ 2) +
        (-2) * x3 * y3 := by ring
    linarith only [hsum, hfx, hfy, hlin, hlt]
  · have hx_le_tlo : x3 ≤ tlo := le_of_not_ge hsplit
    have hfx : (1659 / 1250 : ℝ) * (u ^ 2 + x3 ^ 2) - (409 / 1250 : ℝ) * x3 ^ 2 ≤
        (1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * x3) + (409 / 1250 : ℝ) * (-2 * tlo * x3 + tlo ^ 2) := by
      linarith only [hp0x, htx]
    have hlt := convex_2d_lt (Ax := 0) (Ay := (1659 / 1250 : ℝ) * U1 ^ 2 + 1)
      (Bx := (1659 / 1250 : ℝ) * (2 * R) + (409 / 1250 : ℝ) * (-2 * tlo))
      (By := 2 * (1659 / 1250 : ℝ) * U0 * U1)
      (C := (1659 / 1250 : ℝ) * (1 - R ^ 2) + (409 / 1250 : ℝ) * tlo ^ 2 + (1659 / 1250 : ℝ) * U0 ^ 2)
      (D := -2) le_rfl hAy hx_lo hx_le_tlo hy_lo hy_hi
      (by convert h_p0_0 using 1; dsimp only [U0, U1, Ap, b, y0, τ, tlo]; ring)
      (by convert h_p0_t using 1; dsimp only [U0, U1, Ap, b, y0, τ, tlo]; ring)
      (by convert h_tl_0 using 1; dsimp only [U0, U1, Ap, b, y0, τ, tlo]; ring)
      (by convert h_tl_t using 1; dsimp only [U0, U1, Ap, b, y0, τ, tlo]; ring)
    have hlin : ((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * x3) + (409 / 1250 : ℝ) * (-2 * tlo * x3 + tlo ^ 2)) +
        (((1659 / 1250 : ℝ) * U1 ^ 2 + 1) * y3 ^ 2 + (2 * (1659 / 1250 : ℝ) * U0 * U1) * y3 +
          (1659 / 1250 : ℝ) * U0 ^ 2) - 2 * x3 * y3 =
        0 * x3 ^ 2 + ((1659 / 1250 : ℝ) * (2 * R) + (409 / 1250 : ℝ) * (-2 * tlo)) * x3 +
        ((1659 / 1250 : ℝ) * U1 ^ 2 + 1) * y3 ^ 2 + (2 * (1659 / 1250 : ℝ) * U0 * U1) * y3 +
        ((1659 / 1250 : ℝ) * (1 - R ^ 2) + (409 / 1250 : ℝ) * tlo ^ 2 + (1659 / 1250 : ℝ) * U0 ^ 2) +
        (-2) * x3 * y3 := by ring
    linarith only [hsum, hfx, hfy, hlin, hlt]
-- Remaining cell lemmas for Borsuk 4D H1

private lemma south_hi_bn_half_lt_half {R x3 u : ℝ}
    (hRlo : (121 / 200 : ℝ) ≤ R) (hRhi : R ≤ 627 / 1000)
    (hx_lo : R - 1 ≤ x3) (hx_hi : x3 ≤ 0) (hu : 0 ≤ u)
    (hp0x : u ^ 2 + x3 ^ 2 ≤ 1 - R ^ 2 + 2 * R * x3)
    (hp1x : u ^ 2 + 2 * ((29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R)) * u ≤
      1 - R ^ 2 + 2 * (R - 1 / (2 * R)) * x3 - x3 ^ 2) :
    2 * ((1659 / 1250 : ℝ) * u ^ 2 + x3 ^ 2) < 1 := by
  have hR : (0 : ℝ) < R := by linarith only [hRlo]
  let r1R : ℝ := (145 / 100 : ℝ) * R + 52 / 1000
  let bS : ℝ := (29 / 50 : ℝ) * (r1R * R)
  let AS : ℝ := (17 / 20 : ℝ) * R + bS
  let xm : ℝ := (-21 / 100 : ℝ)
  let tlo : ℝ := R - 1 / (2 * R)
  have hr1 : 0 < r1R := by dsimp only [r1R]; linarith only [hRlo]
  have hAS : 0 < AS := by dsimp only [AS, bS]; positivity
  by_cases hsplit : xm ≤ x3
  · let U0 : ℝ := (1 - R ^ 2 + xm ^ 2 + (AS - bS) ^ 2) / (2 * AS)
    let U1 : ℝ := (2 * (tlo - xm)) / (2 * AS)
    have hu2 : u ^ 2 ≤ (U0 + U1 * x3) ^ 2 := by
      apply u_sq_le_U_sq hu hAS hp1x
      have htan : -x3 ^ 2 ≤ -2 * xm * x3 + xm ^ 2 := by nlinarith only [sq_nonneg (x3 - xm)]
      have heq : U0 + U1 * x3 = (1 - R ^ 2 + xm ^ 2 + (AS - bS) ^ 2 + 2 * (tlo - xm) * x3) / (2 * AS) := by
        dsimp only [U0, U1]; ring
      rw [heq]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      have hrw1 : 1 - R ^ 2 + 2 * (R - 1 / (2 * R)) * x3 - x3 ^ 2 +
            (AS - (29 / 50 : ℝ) * (((145 / 100 : ℝ) * R + 52 / 1000) * R)) ^ 2 =
          (1 - R ^ 2 + 2 * tlo * x3) + (-x3 ^ 2) + (AS - bS) ^ 2 := by
        dsimp only [tlo, bS, r1R]; ring
      have hrw2 : 1 - R ^ 2 + xm ^ 2 + (AS - bS) ^ 2 + 2 * (tlo - xm) * x3 =
          (1 - R ^ 2 + 2 * tlo * x3) + (-2 * xm * x3 + xm ^ 2) + (AS - bS) ^ 2 := by ring
      rw [hrw1, hrw2]
      exact add_le_add_left (add_le_add_right htan _) _
    have hAx : (0 : ℝ) ≤ 2 * ((1659 / 1250 : ℝ) * U1 ^ 2 + 1) := by positivity
    have hUeq (z : ℝ) : 2 * ((1659 / 1250 : ℝ) * U1 ^ 2 + 1) * z ^ 2 +
        (4 * (1659 / 1250 : ℝ) * U0 * U1) * z + 2 * (1659 / 1250 : ℝ) * U0 ^ 2 =
        2 * ((1659 / 1250 : ℝ) * ((1 - R ^ 2 + xm ^ 2 + (AS - bS) ^ 2 + 2 * (tlo - xm) * z) / (2 * AS)) ^ 2 + z ^ 2) := by
      dsimp only [U0, U1]; ring
    have hlt := convex_quad_lt hAx hsplit hx_hi
      (by rw [hUeq xm]; exact south_hi_bn_U_xm hRlo hRhi)
      (by rw [hUeq 0]; exact south_hi_bn_U_0 hRlo hRhi)
    have h1 : 2 * ((1659 / 1250 : ℝ) * u ^ 2 + x3 ^ 2) ≤ 2 * ((1659 / 1250 : ℝ) * (U0 + U1 * x3) ^ 2 + x3 ^ 2) := by
      linarith only [hu2]
    have h2 : 2 * ((1659 / 1250 : ℝ) * (U0 + U1 * x3) ^ 2 + x3 ^ 2) =
        2 * ((1659 / 1250 : ℝ) * U1 ^ 2 + 1) * x3 ^ 2 +
        (4 * (1659 / 1250 : ℝ) * U0 * U1) * x3 + 2 * (1659 / 1250 : ℝ) * U0 ^ 2 := by ring
    linarith only [h1, h2, hlt]
  · have hx_le : x3 ≤ xm := le_of_not_ge hsplit
    have htan : -x3 ^ 2 ≤ -2 * xm * x3 + xm ^ 2 := by nlinarith only [sq_nonneg (x3 - xm)]
    have hbound : 2 * ((1659 / 1250 : ℝ) * u ^ 2 + x3 ^ 2) ≤
        0 * x3 ^ 2 + (2 * ((1659 / 1250 : ℝ) * (2 * R) + (409 / 1250 : ℝ) * (-2 * xm))) * x3 +
        (2 * ((1659 / 1250 : ℝ) * (1 - R ^ 2) + (409 / 1250 : ℝ) * xm ^ 2)) := by
      have h1a : (1659 / 1250 : ℝ) * (u ^ 2 + x3 ^ 2) ≤ (1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * x3) :=
        mul_le_mul_of_nonneg_left hp0x (by norm_num)
      have h1b : (409 / 1250 : ℝ) * (-x3 ^ 2) ≤ (409 / 1250 : ℝ) * (-2 * xm * x3 + xm ^ 2) :=
        mul_le_mul_of_nonneg_left htan (by norm_num)
      have h1c : 2 * ((1659 / 1250 : ℝ) * u ^ 2 + x3 ^ 2) =
          2 * ((1659 / 1250 : ℝ) * (u ^ 2 + x3 ^ 2)) + 2 * ((409 / 1250 : ℝ) * (-x3 ^ 2)) := by ring
      have h2 : 2 * ((1659 / 1250 : ℝ) * (1 - R ^ 2 + 2 * R * x3)) +
            2 * ((409 / 1250 : ℝ) * (-2 * xm * x3 + xm ^ 2)) =
          0 * x3 ^ 2 + (2 * ((1659 / 1250 : ℝ) * (2 * R) + (409 / 1250 : ℝ) * (-2 * xm))) * x3 +
          (2 * ((1659 / 1250 : ℝ) * (1 - R ^ 2) + (409 / 1250 : ℝ) * xm ^ 2)) := by ring
      linarith only [h1a, h1b, h1c, h2]
    have hlt := convex_quad_lt (A := 0)
      (B := 2 * ((1659 / 1250 : ℝ) * (2 * R) + (409 / 1250 : ℝ) * (-2 * xm)))
      (C := 2 * ((1659 / 1250 : ℝ) * (1 - R ^ 2) + (409 / 1250 : ℝ) * xm ^ 2))
      le_rfl hx_lo hx_le
      (by convert south_hi_bn_p0_xmin hRlo hRhi using 1; dsimp only [xm]; ring)
      (by convert south_hi_bn_p0_xm hRlo hRhi using 1; dsimp only [xm]; ring)
    linarith only [hbound, hlt]

private lemma wpn_core_lt_one {R s x3 y3 u v r1R : ℝ}
    (hRlo : (4 / 7 : ℝ) ≤ R) (_hRhi : R ≤ 627 / 1000)
    (hslo : (7 / 25 : ℝ) ≤ s) (_hshi : s ≤ 29 / 50)
    (hx0 : 0 ≤ x3) (hx1 : x3 ≤ (37 / 20 : ℝ) * R - 389 / 500)
    (hy0 : R - 1 ≤ y3) (hy1 : y3 ≤ 0)
    (hu : 0 ≤ u) (huR : u ≤ R) (hr1R : 0 < r1R)
    (hp1x : u ^ 2 + 2 * s * (r1R * R) * u ≤ 1 - R ^ 2 - (1 / 2 : ℝ) * R * x3 - x3 ^ 2)
    (hby : v ^ 2 + y3 ^ 2 ≤ R ^ 2)
    (hp0y : v ^ 2 + y3 ^ 2 ≤ 1 - R ^ 2 + 2 * R * y3)
    (hD_big : 1 + ((2 / 3 : ℝ) * s - 469 / 2500) ≤ 1 + 2 * s * r1R)
    (hks_nn : 0 ≤ (2 / 3 : ℝ) * s - 469 / 2500)
    (hb_0_tlo : ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * 0) / (1 + 2 * s * r1R) +
        (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * r1R)) * (((37 / 20 : ℝ) * R - 389 / 500) * 0)) +
      ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (R - 1 / (2 * R)) + (R - 1 / (2 * R)) ^ 2)) -
      2 * 0 * (R - 1 / (2 * R)) < 1)
    (hb_0_0 : ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * 0) / (1 + 2 * s * r1R) +
        (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * r1R)) * (((37 / 20 : ℝ) * R - 389 / 500) * 0)) +
      ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * 0 + (R - 1 / (2 * R)) ^ 2)) -
      2 * 0 * 0 < 1)
    (hb_t_tlo : ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * ((37 / 20 : ℝ) * R - 389 / 500)) / (1 + 2 * s * r1R) +
        (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * r1R)) * (((37 / 20 : ℝ) * R - 389 / 500) * ((37 / 20 : ℝ) * R - 389 / 500))) +
      ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (R - 1 / (2 * R)) + (R - 1 / (2 * R)) ^ 2)) -
      2 * ((37 / 20 : ℝ) * R - 389 / 500) * (R - 1 / (2 * R)) < 1)
    (hb_t_0 : ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * ((37 / 20 : ℝ) * R - 389 / 500)) / (1 + 2 * s * r1R) +
        (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * r1R)) * (((37 / 20 : ℝ) * R - 389 / 500) * ((37 / 20 : ℝ) * R - 389 / 500))) +
      ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * 0 + (R - 1 / (2 * R)) ^ 2)) -
      2 * ((37 / 20 : ℝ) * R - 389 / 500) * 0 < 1)
    (hp0_0_ym : ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * 0) / (1 + 2 * s * r1R) +
        (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * r1R)) * (((37 / 20 : ℝ) * R - 389 / 500) * 0)) +
      ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * (R - 1)) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (R - 1) + (R - 1 / (2 * R)) ^ 2)) -
      2 * 0 * (R - 1) < 1)
    (hp0_t_ym : ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * ((37 / 20 : ℝ) * R - 389 / 500)) / (1 + 2 * s * r1R) +
        (1 - (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) / (1 + 2 * s * r1R)) * (((37 / 20 : ℝ) * R - 389 / 500) * ((37 / 20 : ℝ) * R - 389 / 500))) +
      ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * (R - 1)) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (R - 1) + (R - 1 / (2 * R)) ^ 2)) -
      2 * ((37 / 20 : ℝ) * R - 389 / 500) * (R - 1) < 1) :
    (x3 - y3) ^ 2 + (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (u ^ 2 + v ^ 2) < 1 := by
  have hR : (0 : ℝ) < R := by linarith only [hRlo]
  have hs : (0 : ℝ) < s := by linarith only [hslo]
  let ks : ℝ := (2 / 3 : ℝ) * s - 469 / 2500
  have hks_nn' : 0 ≤ ks := hks_nn
  let D : ℝ := 1 + 2 * s * r1R
  let τ : ℝ := (37 / 20 : ℝ) * R - 389 / 500
  let tlo : ℝ := R - 1 / (2 * R)
  have hD : 0 < D := by dsimp only [D]; positivity
  have hu2 := u_sq_le_div_p1 hu huR hR hs.le hr1R.le hp1x
  have hcx : 0 ≤ 1 - (1 + ks) / D := by rw [sub_nonneg, div_le_one hD]; exact hD_big
  have hx2 : x3 ^ 2 ≤ τ * x3 := by dsimp only [τ]; nlinarith only [hx0, hx1]
  have hfx : (1 + ks) * u ^ 2 + x3 ^ 2 ≤
      (1 + ks) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * x3) / D + (1 - (1 + ks) / D) * (τ * x3) := by
    have h1 : (1 + ks) * u ^ 2 ≤ (1 + ks) * ((1 - R ^ 2 - (1 / 2 : ℝ) * R * x3 - x3 ^ 2) / D) :=
      mul_le_mul_of_nonneg_left hu2 (by linarith only [hks_nn'])
    have h2 : (1 + ks) * ((1 - R ^ 2 - (1 / 2 : ℝ) * R * x3 - x3 ^ 2) / D) + x3 ^ 2 =
        (1 + ks) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * x3) / D + (1 - (1 + ks) / D) * x3 ^ 2 := by
      field_simp [hD.ne']; ring
    have h3 : (1 - (1 + ks) / D) * x3 ^ 2 ≤ (1 - (1 + ks) / D) * (τ * x3) :=
      mul_le_mul_of_nonneg_left hx2 hcx
    linarith only [h1, h2, h3]
  have hty : -y3 ^ 2 ≤ -2 * tlo * y3 + tlo ^ 2 := by nlinarith only [sq_nonneg (y3 - tlo)]
  have htlo_eq : 1 - R ^ 2 + 2 * R * tlo = R ^ 2 := by dsimp only [tlo]; field_simp [hR.ne']; ring
  have hsum : (x3 - y3) ^ 2 + (1 + ks) * (u ^ 2 + v ^ 2) =
      ((1 + ks) * u ^ 2 + x3 ^ 2) + ((1 + ks) * (v ^ 2 + y3 ^ 2) - ks * y3 ^ 2) - 2 * x3 * y3 := by ring
  by_cases hsplit : tlo ≤ y3
  · have hfy : (1 + ks) * (v ^ 2 + y3 ^ 2) - ks * y3 ^ 2 ≤
        (1 + ks) * R ^ 2 + ks * (-2 * tlo * y3 + tlo ^ 2) := by
      have h1 := mul_le_mul_of_nonneg_left hby (show 0 ≤ 1 + ks by linarith only [hks_nn'])
      have h2 := mul_le_mul_of_nonneg_left hty hks_nn'
      linarith only [h1, h2]
    have hlt := convex_2d_lt (Ax := 0) (Ay := 0)
      (Bx := -(1 + ks) * ((1 / 2 : ℝ) * R) / D + (1 - (1 + ks) / D) * τ)
      (By := ks * (-2 * tlo))
      (C := (1 + ks) * (1 - R ^ 2) / D + (1 + ks) * R ^ 2 + ks * tlo ^ 2)
      (D := -2) le_rfl le_rfl hx0 hx1 hsplit hy1
      (by convert hb_0_tlo using 1; dsimp only [ks, D, τ, tlo]; ring)
      (by convert hb_0_0 using 1; dsimp only [ks, D, τ, tlo]; ring)
      (by convert hb_t_tlo using 1; dsimp only [ks, D, τ, tlo]; ring)
      (by convert hb_t_0 using 1; dsimp only [ks, D, τ, tlo]; ring)
    have hlin : ((1 + ks) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * x3) / D + (1 - (1 + ks) / D) * (τ * x3)) +
        ((1 + ks) * R ^ 2 + ks * (-2 * tlo * y3 + tlo ^ 2)) - 2 * x3 * y3 =
        0 * x3 ^ 2 + (-(1 + ks) * ((1 / 2 : ℝ) * R) / D + (1 - (1 + ks) / D) * τ) * x3 +
        0 * y3 ^ 2 + (ks * (-2 * tlo)) * y3 +
        ((1 + ks) * (1 - R ^ 2) / D + (1 + ks) * R ^ 2 + ks * tlo ^ 2) + (-2) * x3 * y3 := by ring
    change (x3 - y3) ^ 2 + (1 + ks) * (u ^ 2 + v ^ 2) < 1
    linarith only [hsum, hfx, hfy, hlin, hlt]
  · have hy_le : y3 ≤ tlo := le_of_not_ge hsplit
    have hfy : (1 + ks) * (v ^ 2 + y3 ^ 2) - ks * y3 ^ 2 ≤
        (1 + ks) * (1 - R ^ 2 + 2 * R * y3) + ks * (-2 * tlo * y3 + tlo ^ 2) := by
      have h1 := mul_le_mul_of_nonneg_left hp0y (show 0 ≤ 1 + ks by linarith only [hks_nn'])
      have h2 := mul_le_mul_of_nonneg_left hty hks_nn'
      linarith only [h1, h2]
    have hlt := convex_2d_lt (Ax := 0) (Ay := 0)
      (Bx := -(1 + ks) * ((1 / 2 : ℝ) * R) / D + (1 - (1 + ks) / D) * τ)
      (By := (1 + ks) * (2 * R) + ks * (-2 * tlo))
      (C := (1 + ks) * (1 - R ^ 2) / D + (1 + ks) * (1 - R ^ 2) + ks * tlo ^ 2)
      (D := -2) le_rfl le_rfl hx0 hx1 hy0 hy_le
      (by convert hp0_0_ym using 1; dsimp only [ks, D, τ, tlo]; ring)
      (by have h1 : (1 + ks) * (1 - R ^ 2 + 2 * R * tlo) = (1 + ks) * R ^ 2 := by rw [htlo_eq]
          have h2 : 0 * (0 : ℝ) ^ 2 + (-(1 + ks) * ((1 / 2 : ℝ) * R) / D + (1 - (1 + ks) / D) * τ) * 0 +
            0 * tlo ^ 2 + ((1 + ks) * (2 * R) + ks * (-2 * tlo)) * tlo +
            ((1 + ks) * (1 - R ^ 2) / D + (1 + ks) * (1 - R ^ 2) + ks * tlo ^ 2) + (-2) * 0 * tlo =
            ((1 + ks) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * 0) / D + (1 - (1 + ks) / D) * (τ * 0)) +
            ((1 + ks) * (1 - R ^ 2 + 2 * R * tlo) + ks * (-2 * tlo * tlo + tlo ^ 2)) - 2 * 0 * tlo := by ring
          rw [h2, h1]; exact hb_0_tlo)
      (by convert hp0_t_ym using 1; dsimp only [ks, D, τ, tlo]; ring)
      (by have h1 : (1 + ks) * (1 - R ^ 2 + 2 * R * tlo) = (1 + ks) * R ^ 2 := by rw [htlo_eq]
          have h2 : 0 * τ ^ 2 + (-(1 + ks) * ((1 / 2 : ℝ) * R) / D + (1 - (1 + ks) / D) * τ) * τ +
            0 * tlo ^ 2 + ((1 + ks) * (2 * R) + ks * (-2 * tlo)) * tlo +
            ((1 + ks) * (1 - R ^ 2) / D + (1 + ks) * (1 - R ^ 2) + ks * tlo ^ 2) + (-2) * τ * tlo =
            ((1 + ks) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * τ) / D + (1 - (1 + ks) / D) * (τ * τ)) +
            ((1 + ks) * (1 - R ^ 2 + 2 * R * tlo) + ks * (-2 * tlo * tlo + tlo ^ 2)) - 2 * τ * tlo := by ring
          rw [h2, h1]; exact hb_t_tlo)
    have hlin : ((1 + ks) * (1 - R ^ 2 - (1 / 2 : ℝ) * R * x3) / D + (1 - (1 + ks) / D) * (τ * x3)) +
        ((1 + ks) * (1 - R ^ 2 + 2 * R * y3) + ks * (-2 * tlo * y3 + tlo ^ 2)) - 2 * x3 * y3 =
        0 * x3 ^ 2 + (-(1 + ks) * ((1 / 2 : ℝ) * R) / D + (1 - (1 + ks) / D) * τ) * x3 +
        0 * y3 ^ 2 + ((1 + ks) * (2 * R) + ks * (-2 * tlo)) * y3 +
        ((1 + ks) * (1 - R ^ 2) / D + (1 + ks) * (1 - R ^ 2) + ks * tlo ^ 2) + (-2) * x3 * y3 := by ring
    change (x3 - y3) ^ 2 + (1 + ks) * (u ^ 2 + v ^ 2) < 1
    linarith only [hsum, hfx, hfy, hlin, hlt]

private lemma wnp_ball_core_lt_one {R s x3 y3 u v : ℝ}
    (hRlo : (4 / 7 : ℝ) ≤ R) (_hRhi : R ≤ 627 / 1000)
    (hks_nn : 0 ≤ (2 / 3 : ℝ) * s - 469 / 2500)
    (hx0 : R - 1 ≤ x3) (hx1 : x3 ≤ 0)
    (hy0 : 0 ≤ y3) (hy1 : y3 ≤ (37 / 20 : ℝ) * R - 389 / 500)
    (hbx : u ^ 2 + x3 ^ 2 ≤ R ^ 2)
    (hp0x : u ^ 2 + x3 ^ 2 ≤ 1 - R ^ 2 + 2 * R * x3)
    (hby : v ^ 2 + y3 ^ 2 ≤ R ^ 2)
    (hb_tlo_0 : ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (R - 1 / (2 * R)) + (R - 1 / (2 * R)) ^ 2)) +
      ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * 0 + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (R - 1 / (2 * R)) * 0 < 1)
    (hb_tlo_t : ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (R - 1 / (2 * R)) + (R - 1 / (2 * R)) ^ 2)) +
      ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * ((37 / 20 : ℝ) * R - 389 / 500) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (R - 1 / (2 * R)) * ((37 / 20 : ℝ) * R - 389 / 500) < 1)
    (hb_0_0 : ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * 0 + (R - 1 / (2 * R)) ^ 2)) +
      ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * 0 + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * 0 * 0 < 1)
    (hb_0_t : ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * 0 + (R - 1 / (2 * R)) ^ 2)) +
      ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * ((37 / 20 : ℝ) * R - 389 / 500) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * 0 * ((37 / 20 : ℝ) * R - 389 / 500) < 1)
    (hp0_xm_0 : ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * (R - 1)) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (R - 1) + (R - 1 / (2 * R)) ^ 2)) +
      ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * 0 + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (R - 1) * 0 < 1)
    (hp0_xm_t : ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (1 - R ^ 2 + 2 * R * (R - 1)) + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * (R - 1 / (2 * R)) * (R - 1) + (R - 1 / (2 * R)) ^ 2)) +
      ((1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * R ^ 2 + ((2 / 3 : ℝ) * s - 469 / 2500) * (-2 * ((37 / 20 : ℝ) * R - 389 / 500) * ((37 / 20 : ℝ) * R - 389 / 500) + ((37 / 20 : ℝ) * R - 389 / 500) ^ 2)) - 2 * (R - 1) * ((37 / 20 : ℝ) * R - 389 / 500) < 1) :
    (x3 - y3) ^ 2 + (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (u ^ 2 + v ^ 2) < 1 := by
  have hR : (0 : ℝ) < R := by linarith only [hRlo]
  let ks : ℝ := (2 / 3 : ℝ) * s - 469 / 2500
  have hks_nn' : 0 ≤ ks := hks_nn
  let τ : ℝ := (37 / 20 : ℝ) * R - 389 / 500
  let tlo : ℝ := R - 1 / (2 * R)
  have htx : -x3 ^ 2 ≤ -2 * tlo * x3 + tlo ^ 2 := by nlinarith only [sq_nonneg (x3 - tlo)]
  have hty : -y3 ^ 2 ≤ -2 * τ * y3 + τ ^ 2 := by nlinarith only [sq_nonneg (y3 - τ)]
  have htlo_eq : 1 - R ^ 2 + 2 * R * tlo = R ^ 2 := by dsimp only [tlo]; field_simp [hR.ne']; ring
  have hsum : (x3 - y3) ^ 2 + (1 + ks) * (u ^ 2 + v ^ 2) =
      ((1 + ks) * (u ^ 2 + x3 ^ 2) - ks * x3 ^ 2) +
      ((1 + ks) * (v ^ 2 + y3 ^ 2) - ks * y3 ^ 2) - 2 * x3 * y3 := by ring
  have hfy : (1 + ks) * (v ^ 2 + y3 ^ 2) - ks * y3 ^ 2 ≤
      (1 + ks) * R ^ 2 + ks * (-2 * τ * y3 + τ ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_left hby (show 0 ≤ 1 + ks by linarith only [hks_nn'])
    have h2 := mul_le_mul_of_nonneg_left hty hks_nn'
    linarith only [h1, h2]
  by_cases hsplit : tlo ≤ x3
  · have hfx : (1 + ks) * (u ^ 2 + x3 ^ 2) - ks * x3 ^ 2 ≤
        (1 + ks) * R ^ 2 + ks * (-2 * tlo * x3 + tlo ^ 2) := by
      have h1 := mul_le_mul_of_nonneg_left hbx (show 0 ≤ 1 + ks by linarith only [hks_nn'])
      have h2 := mul_le_mul_of_nonneg_left htx hks_nn'
      linarith only [h1, h2]
    have hlt := convex_2d_lt (Ax := 0) (Ay := 0)
      (Bx := ks * (-2 * tlo)) (By := ks * (-2 * τ))
      (C := 2 * (1 + ks) * R ^ 2 + ks * (tlo ^ 2 + τ ^ 2)) (D := -2)
      le_rfl le_rfl hsplit hx1 hy0 hy1
      (by convert hb_tlo_0 using 1; dsimp only [ks, τ, tlo]; ring)
      (by convert hb_tlo_t using 1; dsimp only [ks, τ, tlo]; ring)
      (by convert hb_0_0 using 1; dsimp only [ks, τ, tlo]; ring)
      (by convert hb_0_t using 1; dsimp only [ks, τ, tlo]; ring)
    have hlin : ((1 + ks) * R ^ 2 + ks * (-2 * tlo * x3 + tlo ^ 2)) +
        ((1 + ks) * R ^ 2 + ks * (-2 * τ * y3 + τ ^ 2)) - 2 * x3 * y3 =
        0 * x3 ^ 2 + (ks * (-2 * tlo)) * x3 + 0 * y3 ^ 2 + (ks * (-2 * τ)) * y3 +
        (2 * (1 + ks) * R ^ 2 + ks * (tlo ^ 2 + τ ^ 2)) + (-2) * x3 * y3 := by ring
    change (x3 - y3) ^ 2 + (1 + ks) * (u ^ 2 + v ^ 2) < 1
    linarith only [hsum, hfx, hfy, hlin, hlt]
  · have hx_le : x3 ≤ tlo := le_of_not_ge hsplit
    have hfx : (1 + ks) * (u ^ 2 + x3 ^ 2) - ks * x3 ^ 2 ≤
        (1 + ks) * (1 - R ^ 2 + 2 * R * x3) + ks * (-2 * tlo * x3 + tlo ^ 2) := by
      have h1 := mul_le_mul_of_nonneg_left hp0x (show 0 ≤ 1 + ks by linarith only [hks_nn'])
      have h2 := mul_le_mul_of_nonneg_left htx hks_nn'
      linarith only [h1, h2]
    have hlt := convex_2d_lt (Ax := 0) (Ay := 0)
      (Bx := (1 + ks) * (2 * R) + ks * (-2 * tlo)) (By := ks * (-2 * τ))
      (C := (1 + ks) * (1 - R ^ 2) + (1 + ks) * R ^ 2 + ks * (tlo ^ 2 + τ ^ 2)) (D := -2)
      le_rfl le_rfl hx0 hx_le hy0 hy1
      (by convert hp0_xm_0 using 1; dsimp only [ks, τ, tlo]; ring)
      (by convert hp0_xm_t using 1; dsimp only [ks, τ, tlo]; ring)
      (by have h1 : (1 + ks) * (1 - R ^ 2 + 2 * R * tlo) = (1 + ks) * R ^ 2 := by rw [htlo_eq]
          have h2 : 0 * tlo ^ 2 + ((1 + ks) * (2 * R) + ks * (-2 * tlo)) * tlo + 0 * (0 : ℝ) ^ 2 +
            (ks * (-2 * τ)) * 0 + ((1 + ks) * (1 - R ^ 2) + (1 + ks) * R ^ 2 + ks * (tlo ^ 2 + τ ^ 2)) + (-2) * tlo * 0 =
            ((1 + ks) * (1 - R ^ 2 + 2 * R * tlo) + ks * (-2 * tlo * tlo + tlo ^ 2)) +
            ((1 + ks) * R ^ 2 + ks * (-2 * τ * 0 + τ ^ 2)) - 2 * tlo * 0 := by ring
          rw [h2, h1]; exact hb_tlo_0)
      (by have h1 : (1 + ks) * (1 - R ^ 2 + 2 * R * tlo) = (1 + ks) * R ^ 2 := by rw [htlo_eq]
          have h2 : 0 * tlo ^ 2 + ((1 + ks) * (2 * R) + ks * (-2 * tlo)) * tlo + 0 * τ ^ 2 +
            (ks * (-2 * τ)) * τ + ((1 + ks) * (1 - R ^ 2) + (1 + ks) * R ^ 2 + ks * (tlo ^ 2 + τ ^ 2)) + (-2) * tlo * τ =
            ((1 + ks) * (1 - R ^ 2 + 2 * R * tlo) + ks * (-2 * tlo * tlo + tlo ^ 2)) +
            ((1 + ks) * R ^ 2 + ks * (-2 * τ * τ + τ ^ 2)) - 2 * tlo * τ := by ring
          rw [h2, h1]; exact hb_tlo_t)
    have hlin : ((1 + ks) * (1 - R ^ 2 + 2 * R * x3) + ks * (-2 * tlo * x3 + tlo ^ 2)) +
        ((1 + ks) * R ^ 2 + ks * (-2 * τ * y3 + τ ^ 2)) - 2 * x3 * y3 =
        0 * x3 ^ 2 + ((1 + ks) * (2 * R) + ks * (-2 * tlo)) * x3 + 0 * y3 ^ 2 + (ks * (-2 * τ)) * y3 +
        ((1 + ks) * (1 - R ^ 2) + (1 + ks) * R ^ 2 + ks * (tlo ^ 2 + τ ^ 2)) + (-2) * x3 * y3 := by ring
    change (x3 - y3) ^ 2 + (1 + ks) * (u ^ 2 + v ^ 2) < 1
    linarith only [hsum, hfx, hfy, hlin, hlt]

private lemma wnp_hi_lt_one {R s x3 y3 u v : ℝ}
    (hRlo : (121 / 200 : ℝ) ≤ R) (hRhi : R ≤ 627 / 1000)
    (hslo : (9 / 20 : ℝ) ≤ s) (hshi : s ≤ 29 / 50)
    (hx0 : R - 1 ≤ x3) (hx1 : x3 ≤ 0)
    (hy0 : 0 ≤ y3) (hy1 : y3 ≤ (37 / 20 : ℝ) * R - 389 / 500)
    (hu : 0 ≤ u)
    (hp0x : u ^ 2 + x3 ^ 2 ≤ 1 - R ^ 2 + 2 * R * x3)
    (hp1x : u ^ 2 + 2 * (s * (((145 / 100 : ℝ) * R + 52 / 1000) * R)) * u ≤
      1 - R ^ 2 + 2 * (R - 1 / (2 * R)) * x3 - x3 ^ 2)
    (hby : v ^ 2 + y3 ^ 2 ≤ R ^ 2) :
    (x3 - y3) ^ 2 + (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (u ^ 2 + v ^ 2) < 1 := by
  have hR : (0 : ℝ) < R := by linarith only [hRlo]
  have hs : (0 : ℝ) < s := by linarith only [hslo]
  let ks : ℝ := (2 / 3 : ℝ) * s - 469 / 2500
  have hks_nn : 0 ≤ ks := by dsimp only [ks]; linarith only [hslo]
  let τ : ℝ := (37 / 20 : ℝ) * R - 389 / 500
  let tlo : ℝ := R - 1 / (2 * R)
  let r1R : ℝ := (145 / 100 : ℝ) * R + 52 / 1000
  let bW : ℝ := s * (r1R * R)
  let AW : ℝ := (9 / 10 : ℝ) * R + bW
  let x0 : ℝ := (-37 / 100 : ℝ) * R
  let xm : ℝ := (-365 / 1000 : ℝ) * R - (3 / 10 : ℝ) * (s - 29 / 50)
  have hr1 : 0 < r1R := by dsimp only [r1R]; linarith only [hRlo]
  have hAW : 0 < AW := by dsimp only [AW, bW]; positivity
  have hty : -y3 ^ 2 ≤ -2 * τ * y3 + τ ^ 2 := by nlinarith only [sq_nonneg (y3 - τ)]
  have hfy : (1 + ks) * (v ^ 2 + y3 ^ 2) - ks * y3 ^ 2 ≤
      (1 + ks) * R ^ 2 + ks * (-2 * τ * y3 + τ ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_left hby (show 0 ≤ 1 + ks by linarith only [hks_nn])
    have h2 := mul_le_mul_of_nonneg_left hty hks_nn
    linarith only [h1, h2]
  by_cases hsplit : xm ≤ x3
  · let U0 : ℝ := (1 - R ^ 2 + x0 ^ 2 + (AW - bW) ^ 2) / (2 * AW)
    let U1 : ℝ := (2 * (tlo - x0)) / (2 * AW)
    have hu2 : u ^ 2 ≤ (U0 + U1 * x3) ^ 2 := by
      apply u_sq_le_U_sq hu hAW hp1x
      have htan : -x3 ^ 2 ≤ -2 * x0 * x3 + x0 ^ 2 := by nlinarith only [sq_nonneg (x3 - x0)]
      have heq : U0 + U1 * x3 = (1 - R ^ 2 + x0 ^ 2 + (AW - bW) ^ 2 + 2 * (tlo - x0) * x3) / (2 * AW) := by
        dsimp only [U0, U1]; ring
      rw [heq]
      exact div_le_div_of_nonneg_right (by dsimp only [tlo, bW, r1R]; linarith only [htan]) (by positivity)
    have hAx : 0 ≤ (1 + ks) * U1 ^ 2 + 1 := by positivity
    have hlt := convex_2d_lt (Ax := (1 + ks) * U1 ^ 2 + 1) (Ay := 0)
      (Bx := 2 * (1 + ks) * U0 * U1) (By := ks * (-2 * τ))
      (C := (1 + ks) * U0 ^ 2 + (1 + ks) * R ^ 2 + ks * τ ^ 2) (D := -2)
      hAx le_rfl hsplit hx1 hy0 hy1
      (by convert wnp_hi_U_xm_0 hRlo hRhi hslo hshi using 1; dsimp only [U0, U1, ks, τ, tlo, r1R, bW, AW, x0, xm]; ring)
      (by convert wnp_hi_U_xm_tau hRlo hRhi hslo hshi using 1; dsimp only [U0, U1, ks, τ, tlo, r1R, bW, AW, x0, xm]; ring)
      (by convert wnp_hi_U_0_0 hRlo hRhi hslo hshi using 1; dsimp only [U0, U1, ks, τ, tlo, r1R, bW, AW, x0, xm]; ring)
      (by convert wnp_hi_U_0_tau hRlo hRhi hslo hshi using 1; dsimp only [U0, U1, ks, τ, tlo, r1R, bW, AW, x0, xm]; ring)
    have hsum : (x3 - y3) ^ 2 + (1 + ks) * (u ^ 2 + v ^ 2) =
        ((1 + ks) * u ^ 2 + x3 ^ 2) + ((1 + ks) * (v ^ 2 + y3 ^ 2) - ks * y3 ^ 2) - 2 * x3 * y3 := by ring
    have hfx : (1 + ks) * u ^ 2 + x3 ^ 2 ≤
        ((1 + ks) * U1 ^ 2 + 1) * x3 ^ 2 + (2 * (1 + ks) * U0 * U1) * x3 + (1 + ks) * U0 ^ 2 := by
      have h1 := mul_le_mul_of_nonneg_left hu2 (show 0 ≤ 1 + ks by linarith only [hks_nn])
      have h2 : (1 + ks) * (U0 + U1 * x3) ^ 2 + x3 ^ 2 =
          ((1 + ks) * U1 ^ 2 + 1) * x3 ^ 2 + (2 * (1 + ks) * U0 * U1) * x3 + (1 + ks) * U0 ^ 2 := by ring
      linarith only [h1, h2]
    have hlin : (((1 + ks) * U1 ^ 2 + 1) * x3 ^ 2 + (2 * (1 + ks) * U0 * U1) * x3 + (1 + ks) * U0 ^ 2) +
        ((1 + ks) * R ^ 2 + ks * (-2 * τ * y3 + τ ^ 2)) - 2 * x3 * y3 =
        ((1 + ks) * U1 ^ 2 + 1) * x3 ^ 2 + (2 * (1 + ks) * U0 * U1) * x3 +
        0 * y3 ^ 2 + (ks * (-2 * τ)) * y3 +
        ((1 + ks) * U0 ^ 2 + (1 + ks) * R ^ 2 + ks * τ ^ 2) + (-2) * x3 * y3 := by ring
    change (x3 - y3) ^ 2 + (1 + ks) * (u ^ 2 + v ^ 2) < 1
    linarith only [hsum, hfx, hfy, hlin, hlt]
  · have hx_le : x3 ≤ xm := le_of_not_ge hsplit
    have htx : -x3 ^ 2 ≤ -2 * xm * x3 + xm ^ 2 := by nlinarith only [sq_nonneg (x3 - xm)]
    have hfx : (1 + ks) * (u ^ 2 + x3 ^ 2) - ks * x3 ^ 2 ≤
        (1 + ks) * (1 - R ^ 2 + 2 * R * x3) + ks * (-2 * xm * x3 + xm ^ 2) := by
      have h1 := mul_le_mul_of_nonneg_left hp0x (show 0 ≤ 1 + ks by linarith only [hks_nn])
      have h2 := mul_le_mul_of_nonneg_left htx hks_nn
      linarith only [h1, h2]
    have hsum : (x3 - y3) ^ 2 + (1 + ks) * (u ^ 2 + v ^ 2) =
        ((1 + ks) * (u ^ 2 + x3 ^ 2) - ks * x3 ^ 2) +
        ((1 + ks) * (v ^ 2 + y3 ^ 2) - ks * y3 ^ 2) - 2 * x3 * y3 := by ring
    have hlt := convex_2d_lt (Ax := 0) (Ay := 0)
      (Bx := (1 + ks) * (2 * R) + ks * (-2 * xm)) (By := ks * (-2 * τ))
      (C := (1 + ks) * (1 - R ^ 2) + (1 + ks) * R ^ 2 + ks * (xm ^ 2 + τ ^ 2)) (D := -2)
      le_rfl le_rfl hx0 hx_le hy0 hy1
      (by convert wnp_hi_p0_xmin_0 hRlo hRhi hslo hshi using 1; dsimp only [ks, τ, xm]; ring)
      (by convert wnp_hi_p0_xmin_tau hRlo hRhi hslo hshi using 1; dsimp only [ks, τ, xm]; ring)
      (by convert wnp_hi_p0_xm_0 hRlo hRhi hslo hshi using 1; dsimp only [ks, τ, xm]; ring)
      (by convert wnp_hi_p0_xm_tau hRlo hRhi hslo hshi using 1; dsimp only [ks, τ, xm]; ring)
    have hlin : ((1 + ks) * (1 - R ^ 2 + 2 * R * x3) + ks * (-2 * xm * x3 + xm ^ 2)) +
        ((1 + ks) * R ^ 2 + ks * (-2 * τ * y3 + τ ^ 2)) - 2 * x3 * y3 =
        0 * x3 ^ 2 + ((1 + ks) * (2 * R) + ks * (-2 * xm)) * x3 + 0 * y3 ^ 2 + (ks * (-2 * τ)) * y3 +
        ((1 + ks) * (1 - R ^ 2) + (1 + ks) * R ^ 2 + ks * (xm ^ 2 + τ ^ 2)) + (-2) * x3 * y3 := by ring
    change (x3 - y3) ^ 2 + (1 + ks) * (u ^ 2 + v ^ 2) < 1
    linarith only [hsum, hfx, hfy, hlin, hlt]
-- Final geometric glue for Borsuk 4D H1 (4/7 < R <= 627/1000)

private lemma exists_two_obtuse_contacts {S : Set E4} (hS : IsCompact S) (hne : S.Nonempty)
    (hd : Metric.diam S ≤ 1) (hmin : ∀ c : E4, radiusAt S 0 ≤ radiusAt S c)
    (hR : (1 / 4 : ℝ) < radiusAt S 0 ^ 2) :
    ∃ p0 p1 : E4, p0 ∈ S ∧ p1 ∈ S ∧
      ‖p0‖ = radiusAt S 0 ∧ ‖p1‖ = radiusAt S 0 ∧
      inner ℝ p0 p1 ≤ -(1 / 4 : ℝ) * radiusAt S 0 ^ 2 := by
  let R := radiusAt S 0
  obtain ⟨n, hn3, hn5, p, w, hp, _, hwpos, hwsum, hbary⟩ :=
    exists_three_to_five_contact_simplex hS hne hd hmin hR
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨i0, _, hi0max⟩ := Finset.exists_max_image Finset.univ w Finset.univ_nonempty
  have hw0_ge : (1 : ℝ) ≤ (n : ℝ) * w i0 := by
    calc (1 : ℝ) = ∑ j : Fin n, w j := hwsum.symm
      _ ≤ ∑ _j : Fin n, w i0 := Finset.sum_le_sum (fun j _ => hi0max j (Finset.mem_univ j))
      _ = (n : ℝ) * w i0 := by simp
  have hn_le : (n : ℝ) ≤ 5 := by exact_mod_cast hn5
  have h5w : 1 - w i0 ≤ 4 * w i0 := by nlinarith [hwpos i0]
  have hsum_inner : ∑ j : Fin n, w j * inner ℝ (p i0) (p j) = 0 := by
    have h := congrArg (inner ℝ (p i0)) hbary
    simpa only [inner_sum, inner_smul_right, inner_zero_right] using h
  have hsplit := Finset.add_sum_erase Finset.univ (fun j => w j * inner ℝ (p i0) (p j)) (Finset.mem_univ i0)
  have hself : inner ℝ (p i0) (p i0) = R ^ 2 := by
    rw [real_inner_self_eq_norm_sq, (hp i0).2]
  have herase_sum : ∑ j ∈ Finset.univ.erase i0, w j * inner ℝ (p i0) (p j) = -(w i0 * R ^ 2) := by
    rw [hself] at hsplit; linarith
  have hw_erase : ∑ j ∈ Finset.univ.erase i0, w j = 1 - w i0 := by
    have h := Finset.add_sum_erase Finset.univ w (Finset.mem_univ i0)
    linarith
  by_contra! hgt
  have hstrict : ∑ j ∈ Finset.univ.erase i0, w j * (-(1 / 4 : ℝ) * R ^ 2) <
      ∑ j ∈ Finset.univ.erase i0, w j * inner ℝ (p i0) (p j) := by
    apply Finset.sum_lt_sum_of_nonempty
    · have hcard : 1 < Fintype.card (Fin n) := by simp; omega
      obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card hcard i0
      exact ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩⟩
    · intro j hj
      have hjne : j ≠ i0 := (Finset.mem_erase.mp hj).1
      have := hgt (p i0) (p j) (hp i0).1 (hp j).1 (hp i0).2 (hp j).2
      exact mul_lt_mul_of_pos_left this (hwpos j)
  rw [← Finset.sum_mul, hw_erase, herase_sum] at hstrict
  nlinarith [sq_nonneg R]

private lemma nine_parts_pair_lt_one {R x3 y3 nx2 ny2 : ℝ}
    (hRhi : R ≤ 627 / 1000)
    (hx_hi : x3 ≤ (37 / 20 : ℝ) * R - 389 / 500)
    (hy_hi : y3 ≤ (37 / 20 : ℝ) * R - 389 / 500)
    (hbx : nx2 ≤ R ^ 2) (hby : ny2 ≤ R ^ 2)
    (hp0x : nx2 ≤ 1 - R ^ 2 + 2 * R * x3)
    (hp0y : ny2 ≤ 1 - R ^ 2 + 2 * R * y3) :
    nx2 + ny2 - 2 * x3 * y3 < 1 := by
  have htau_lt : (37 / 20 : ℝ) * R - 389 / 500 < R := by linarith
  by_cases hsign : 0 ≤ x3 * y3
  · nlinarith
  · by_cases hxneg : x3 < 0
    · nlinarith [mul_neg_of_neg_of_pos hxneg (show 0 < R - y3 by linarith)]
    · have hyneg : y3 < 0 := by
        by_contra! hy
        exact hsign (mul_nonneg (le_of_not_gt hxneg) hy)
      nlinarith [mul_neg_of_neg_of_pos hyneg (show 0 < R - x3 by linarith)]

private lemma south_cell_lt_one {R t1 r1 x3 y3 u v : ℝ}
    (hRlo : (4 / 7 : ℝ) ≤ R) (hRhi : R ≤ 627 / 1000)
    (hr1 : 0 ≤ r1) (hr1sq : r1 ^ 2 + t1 ^ 2 = R ^ 2)
    (ht1_hi : t1 ≤ -R / 4) (ht1_lo : R - 1 / (2 * R) ≤ t1)
    (hx_lo : R - 1 ≤ x3) (hx_hi : x3 ≤ (37 / 20 : ℝ) * R - 389 / 500)
    (hy_lo : R - 1 ≤ y3) (hy_hi : y3 ≤ (37 / 20 : ℝ) * R - 389 / 500)
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hbx : u ^ 2 + x3 ^ 2 ≤ R ^ 2) (hby : v ^ 2 + y3 ^ 2 ≤ R ^ 2)
    (hp0x : u ^ 2 + x3 ^ 2 ≤ 1 - R ^ 2 + 2 * R * x3)
    (hp0y : v ^ 2 + y3 ^ 2 ≤ 1 - R ^ 2 + 2 * R * y3)
    (hp1x : u ^ 2 + 2 * ((29 / 50 : ℝ) * r1) * u ≤ 1 - R ^ 2 + 2 * t1 * x3 - x3 ^ 2)
    (hp1y : v ^ 2 + 2 * ((29 / 50 : ℝ) * r1) * v ≤ 1 - R ^ 2 + 2 * t1 * y3 - y3 ^ 2) :
    (x3 - y3) ^ 2 + (1659 / 1250 : ℝ) * (u ^ 2 + v ^ 2) < 1 := by
  have hR : (0 : ℝ) < R := by linarith
  have huR : u ≤ R := by nlinarith [sq_nonneg x3]
  have hvR : v ≤ R := by nlinarith [sq_nonneg y3]
  by_cases hRmid : R ≤ 121 / 200
  · have hr1_lb := r1_lower_lo hRlo hRmid hr1 hr1sq ht1_hi ht1_lo
    let r1R : ℝ := (245 / 100 : ℝ) * R - 554 / 1000
    have hr1R_pos : 0 < r1R := by dsimp only [r1R]; linarith only [hRlo]
    have hD_big : (1659 / 1250 : ℝ) ≤ 1 + 2 * (29 / 50 : ℝ) * r1R := by dsimp only [r1R]; linarith only [hRlo]
    by_cases hx0 : 0 ≤ x3
    · by_cases hy0 : 0 ≤ y3
      · apply south_pp_lt_one hRlo hRhi hx0 hx_hi hy0 hy_hi hu hv huR hvR hr1R_pos
          (by dsimp only [r1R]; nlinarith only [hp1x, hr1_lb, ht1_hi, hu, hx0])
          (by dsimp only [r1R]; nlinarith only [hp1y, hr1_lb, ht1_hi, hv, hy0]) hD_big
          (south_lo_pp_0_0 hRlo hRmid) (south_lo_pp_0_tau hRlo hRmid) (south_lo_pp_tau_tau hRlo hRmid)
      · have hy_neg : y3 ≤ 0 := le_of_not_ge hy0
        have h := south_opp_lt_one hRlo hRhi hy_lo hy_neg hx0 hx_hi hv hu hby hp0y hr1R_pos
          (by dsimp only [r1R]; nlinarith only [hp1x, hr1_lb, ht1_hi, hu, hx0])
          (south_lo_op0_xmin_0 hRlo hRmid) (south_lo_op0_xmin_tau hRlo hRmid)
          (south_lo_op0_tlo_0 hRlo hRmid) (south_lo_op0_tlo_tau hRlo hRmid)
          (south_lo_ob_0_0 hRlo hRmid) (south_lo_ob_0_tau hRlo hRmid)
        linarith only [h, show (x3 - y3) ^ 2 = (y3 - x3) ^ 2 by ring]
    · have hx_neg : x3 ≤ 0 := le_of_not_ge hx0
      by_cases hy0 : 0 ≤ y3
      · exact south_opp_lt_one hRlo hRhi hx_lo hx_neg hy0 hy_hi hu hv hbx hp0x hr1R_pos
          (by dsimp only [r1R]; nlinarith only [hp1y, hr1_lb, ht1_hi, hv, hy0])
          (south_lo_op0_xmin_0 hRlo hRmid) (south_lo_op0_xmin_tau hRlo hRmid)
          (south_lo_op0_tlo_0 hRlo hRmid) (south_lo_op0_tlo_tau hRlo hRmid)
          (south_lo_ob_0_0 hRlo hRmid) (south_lo_ob_0_tau hRlo hRmid)
      · have hy_neg : y3 ≤ 0 := le_of_not_ge hy0
        have hxy : 0 ≤ x3 * y3 := mul_nonneg_of_nonpos_of_nonpos hx_neg hy_neg
        nlinarith only [hbx, hby, hRmid, hR, hxy, sq_nonneg x3, sq_nonneg y3]
  · have hRmid_ge : (121 / 200 : ℝ) ≤ R := le_of_not_ge hRmid
    have hr1_lb := r1_lower_hi hRmid_ge hRhi hr1 hr1sq ht1_hi ht1_lo
    let r1R : ℝ := (145 / 100 : ℝ) * R + 52 / 1000
    have hr1R_pos : 0 < r1R := by dsimp only [r1R]; linarith only [hRmid_ge]
    have hD_big : (1659 / 1250 : ℝ) ≤ 1 + 2 * (29 / 50 : ℝ) * r1R := by dsimp only [r1R]; linarith only [hRmid_ge]
    by_cases hx0 : 0 ≤ x3
    · by_cases hy0 : 0 ≤ y3
      · apply south_pp_lt_one hRlo hRhi hx0 hx_hi hy0 hy_hi hu hv huR hvR hr1R_pos
          (by dsimp only [r1R]; nlinarith only [hp1x, hr1_lb, ht1_hi, hu, hx0])
          (by dsimp only [r1R]; nlinarith only [hp1y, hr1_lb, ht1_hi, hv, hy0]) hD_big
          (south_hi_pp_0_0 hRmid_ge hRhi) (south_hi_pp_0_tau hRmid_ge hRhi) (south_hi_pp_tau_tau hRmid_ge hRhi)
      · have hy_neg : y3 ≤ 0 := le_of_not_ge hy0
        have h := south_opp_lt_one hRlo hRhi hy_lo hy_neg hx0 hx_hi hv hu hby hp0y hr1R_pos
          (by dsimp only [r1R]; nlinarith only [hp1x, hr1_lb, ht1_hi, hu, hx0])
          (south_hi_op0_xmin_0 hRmid_ge hRhi) (south_hi_op0_xmin_tau hRmid_ge hRhi)
          (south_hi_op0_tlo_0 hRmid_ge hRhi) (south_hi_op0_tlo_tau hRmid_ge hRhi)
          (south_hi_ob_0_0 hRmid_ge hRhi) (south_hi_ob_0_tau hRmid_ge hRhi)
        linarith only [h, show (x3 - y3) ^ 2 = (y3 - x3) ^ 2 by ring]
    · have hx_neg : x3 ≤ 0 := le_of_not_ge hx0
      by_cases hy0 : 0 ≤ y3
      · exact south_opp_lt_one hRlo hRhi hx_lo hx_neg hy0 hy_hi hu hv hbx hp0x hr1R_pos
          (by dsimp only [r1R]; nlinarith only [hp1y, hr1_lb, ht1_hi, hv, hy0])
          (south_hi_op0_xmin_0 hRmid_ge hRhi) (south_hi_op0_xmin_tau hRmid_ge hRhi)
          (south_hi_op0_tlo_0 hRmid_ge hRhi) (south_hi_op0_tlo_tau hRmid_ge hRhi)
          (south_hi_ob_0_0 hRmid_ge hRhi) (south_hi_ob_0_tau hRmid_ge hRhi)
      · have hy_neg : y3 ≤ 0 := le_of_not_ge hy0
        have hx_half := south_hi_bn_half_lt_half hRmid_ge hRhi hx_lo hx_neg hu hp0x
          (by nlinarith only [hp1x, hr1_lb, ht1_lo, hu, hx_neg])
        have hy_half := south_hi_bn_half_lt_half hRmid_ge hRhi hy_lo hy_neg hv hp0y
          (by nlinarith only [hp1y, hr1_lb, ht1_lo, hv, hy_neg])
        have hxy : 0 ≤ x3 * y3 := mul_nonneg_of_nonpos_of_nonpos hx_neg hy_neg
        nlinarith only [hx_half, hy_half, hxy]

private lemma wedge_opp_lt_one {R t1 r1 s x3 y3 u v : ℝ}
    (hRlo : (4 / 7 : ℝ) ≤ R) (hRhi : R ≤ 627 / 1000)
    (hr1 : 0 ≤ r1) (hr1sq : r1 ^ 2 + t1 ^ 2 = R ^ 2)
    (ht1_hi : t1 ≤ -R / 4) (ht1_lo : R - 1 / (2 * R) ≤ t1)
    (hslo : (7 / 25 : ℝ) ≤ s) (hshi : s ≤ 29 / 50)
    (hks_nn : 0 ≤ (2 / 3 : ℝ) * s - 469 / 2500)
    (hx_lo : R - 1 ≤ x3) (hx_hi : x3 ≤ (37 / 20 : ℝ) * R - 389 / 500)
    (hy_lo : R - 1 ≤ y3) (hy_hi : y3 ≤ (37 / 20 : ℝ) * R - 389 / 500)
    (hu : 0 ≤ u) (_hv : 0 ≤ v)
    (hbx : u ^ 2 + x3 ^ 2 ≤ R ^ 2) (hby : v ^ 2 + y3 ^ 2 ≤ R ^ 2)
    (hp0x : u ^ 2 + x3 ^ 2 ≤ 1 - R ^ 2 + 2 * R * x3)
    (hp0y : v ^ 2 + y3 ^ 2 ≤ 1 - R ^ 2 + 2 * R * y3)
    (hp1x : u ^ 2 + 2 * (s * r1) * u ≤ 1 - R ^ 2 + 2 * t1 * x3 - x3 ^ 2) :
    (x3 - y3) ^ 2 + (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (u ^ 2 + v ^ 2) < 1 := by
  have hR : (0 : ℝ) < R := by linarith only [hRlo]
  have huR : u ≤ R := by nlinarith only [hbx, hu, hR, sq_nonneg x3]
  by_cases hsign : 0 ≤ x3 * y3
  · have hks_hi : (2 / 3 : ℝ) * s - 469 / 2500 ≤ 200 / 1000 := by linarith only [hshi]
    have hsum_uv : u ^ 2 + v ^ 2 ≤ 2 * R ^ 2 - x3 ^ 2 - y3 ^ 2 := by linarith only [hbx, hby]
    have h1 : (1 + ((2 / 3 : ℝ) * s - 469 / 2500)) * (u ^ 2 + v ^ 2) ≤
        (1 + (200 / 1000 : ℝ)) * (2 * R ^ 2 - x3 ^ 2 - y3 ^ 2) := by
      have hnn : 0 ≤ u ^ 2 + v ^ 2 := by positivity
      nlinarith only [hks_hi, hsum_uv, hnn]
    nlinarith only [h1, hsign, hRhi, hR, sq_nonneg x3, sq_nonneg y3]
  · by_cases hx0 : 0 ≤ x3
    · have hy_neg : y3 ≤ 0 := by
        by_contra! hy
        exact hsign (mul_nonneg hx0 hy.le)
      by_cases hRmid : R ≤ 121 / 200
      · have hr1_lb := r1_lower_lo hRlo hRmid hr1 hr1sq ht1_hi ht1_lo
        let r1R : ℝ := (245 / 100 : ℝ) * R - 554 / 1000
        have hr1R_pos : 0 < r1R := by dsimp only [r1R]; linarith only [hRlo]
        have hD_big : 1 + ((2 / 3 : ℝ) * s - 469 / 2500) ≤ 1 + 2 * s * r1R := by
          dsimp only [r1R]; nlinarith only [hRlo, hslo]
        exact wpn_core_lt_one hRlo hRhi hslo hshi hx0 hx_hi hy_lo hy_neg hu huR hr1R_pos
          (by have hsr : s * (r1R * R) ≤ s * r1 := mul_le_mul_of_nonneg_left hr1_lb (by linarith only [hslo])
              nlinarith only [hp1x, hsr, ht1_hi, hu, hx0]) hby hp0y hD_big hks_nn
          (wpn_lo_b_0_tlo hRlo hRmid hslo hshi) (wpn_lo_b_0_0 hRlo hRmid hslo hshi)
          (wpn_lo_b_tau_tlo hRlo hRmid hslo hshi) (wpn_lo_b_tau_0 hRlo hRmid hslo hshi)
          (wpn_lo_p0_0_ymin hRlo hRmid hslo hshi) (wpn_lo_p0_tau_ymin hRlo hRmid hslo hshi)
      · have hRmid_ge : (121 / 200 : ℝ) ≤ R := le_of_not_ge hRmid
        have hr1_lb := r1_lower_hi hRmid_ge hRhi hr1 hr1sq ht1_hi ht1_lo
        let r1R : ℝ := (145 / 100 : ℝ) * R + 52 / 1000
        have hr1R_pos : 0 < r1R := by dsimp only [r1R]; linarith only [hRmid_ge]
        have hD_big : 1 + ((2 / 3 : ℝ) * s - 469 / 2500) ≤ 1 + 2 * s * r1R := by
          dsimp only [r1R]; nlinarith only [hRmid_ge, hslo]
        exact wpn_core_lt_one hRlo hRhi hslo hshi hx0 hx_hi hy_lo hy_neg hu huR hr1R_pos
          (by have hsr : s * (r1R * R) ≤ s * r1 := mul_le_mul_of_nonneg_left hr1_lb (by linarith only [hslo])
              nlinarith only [hp1x, hsr, ht1_hi, hu, hx0]) hby hp0y hD_big hks_nn
          (wpn_hi_b_0_tlo hRmid_ge hRhi hslo hshi) (wpn_hi_b_0_0 hRmid_ge hRhi hslo hshi)
          (wpn_hi_b_tau_tlo hRmid_ge hRhi hslo hshi) (wpn_hi_b_tau_0 hRmid_ge hRhi hslo hshi)
          (wpn_hi_p0_0_ymin hRmid_ge hRhi hslo hshi) (wpn_hi_p0_tau_ymin hRmid_ge hRhi hslo hshi)
    · have hx_neg : x3 ≤ 0 := le_of_not_ge hx0
      have hy0 : 0 ≤ y3 := by
        by_contra! hy
        exact hsign (mul_nonneg_of_nonpos_of_nonpos hx_neg hy.le)
      by_cases hRmid : R ≤ 121 / 200
      · exact wnp_ball_core_lt_one hRlo hRhi hks_nn hx_lo hx_neg hy0 hy_hi hbx hp0x hby
          (wnp_Rlo_b_tlo_0 hRlo hRmid hslo hshi) (wnp_Rlo_b_tlo_tau hRlo hRmid hslo hshi)
          (wnp_Rlo_b_0_0 hRlo hRmid hslo hshi) (wnp_Rlo_b_0_tau hRlo hRmid hslo hshi)
          (wnp_Rlo_p0_xmin_0 hRlo hRmid hslo hshi) (wnp_Rlo_p0_xmin_tau hRlo hRmid hslo hshi)
      · have hRmid_ge : (121 / 200 : ℝ) ≤ R := le_of_not_ge hRmid
        by_cases hsmid : s ≤ 9 / 20
        · exact wnp_ball_core_lt_one hRlo hRhi hks_nn hx_lo hx_neg hy0 hy_hi hbx hp0x hby
            (wnp_slo_b_tlo_0 hRmid_ge hRhi hslo hsmid) (wnp_slo_b_tlo_tau hRmid_ge hRhi hslo hsmid)
            (wnp_slo_b_0_0 hRmid_ge hRhi hslo hsmid) (wnp_slo_b_0_tau hRmid_ge hRhi hslo hsmid)
            (wnp_slo_p0_xmin_0 hRmid_ge hRhi hslo hsmid) (wnp_slo_p0_xmin_tau hRmid_ge hRhi hslo hsmid)
        · have hsmid_ge : (9 / 20 : ℝ) ≤ s := le_of_not_ge hsmid
          have hr1_lb := r1_lower_hi hRmid_ge hRhi hr1 hr1sq ht1_hi ht1_lo
          exact wnp_hi_lt_one hRmid_ge hRhi hsmid_ge hshi hx_lo hx_neg hy0 hy_hi hu hp0x
            (by have hsr : s * (((145 / 100 : ℝ) * R + 52 / 1000) * R) ≤ s * r1 :=
                  mul_le_mul_of_nonneg_left hr1_lb (by linarith only [hsmid_ge])
                nlinarith only [hp1x, hsr, ht1_lo, hu, hx_neg]) hby

private lemma wedge_opp_coords_lt_one {R t1 r1 a0 a1 a2 a3 b0 b1 b2 b3 : ℝ}
    (hRlo : (4 / 7 : ℝ) < R) (hRhi : R ≤ 627 / 1000)
    (hr1_pos : 0 < r1) (hr1sq : r1 ^ 2 + t1 ^ 2 = R ^ 2)
    (ht1_hi : t1 ≤ -R / 4) (ht1_lo : R - 1 / (2 * R) ≤ t1)
    (ha_ball : a0 ^ 2 + a1 ^ 2 + a2 ^ 2 + a3 ^ 2 ≤ R ^ 2)
    (hb_ball : b0 ^ 2 + b1 ^ 2 + b2 ^ 2 + b3 ^ 2 ≤ R ^ 2)
    (ha_p0 : a0 ^ 2 + a1 ^ 2 + a2 ^ 2 + a3 ^ 2 ≤ 1 - R ^ 2 + 2 * R * a3)
    (hb_p0 : b0 ^ 2 + b1 ^ 2 + b2 ^ 2 + b3 ^ 2 ≤ 1 - R ^ 2 + 2 * R * b3)
    (ha_p1 : a0 ^ 2 + a1 ^ 2 + a2 ^ 2 + a3 ^ 2 ≤ 1 - R ^ 2 + 2 * r1 * a2 + 2 * t1 * a3)
    (ha3_ge : R - 1 ≤ a3) (hb3_ge : R - 1 ≤ b3)
    (haτ : a3 ≤ (37 / 20 : ℝ) * R - 389 / 500) (hbτ : b3 ≤ (37 / 20 : ℝ) * R - 389 / 500)
    (ha2 : a2 ≤ 0) (hb2 : 0 ≤ b2)
    (haCone : a2 ^ 2 ≤ (841 / 2500 : ℝ) * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2))
    (hbCone : b2 ^ 2 ≤ (4 / 9 : ℝ) * (b0 ^ 2 + b1 ^ 2 + b2 ^ 2))
    (hab_sec : c5 * Real.sqrt (a0 ^ 2 + a1 ^ 2) * Real.sqrt (b0 ^ 2 + b1 ^ 2) ≤ a0 * b0 + a1 * b1) :
    (a0 ^ 2 + a1 ^ 2 + a2 ^ 2 + a3 ^ 2) + (b0 ^ 2 + b1 ^ 2 + b2 ^ 2 + b3 ^ 2) - 2 * a3 * b3 -
      2 * (a2 * b2 + (a0 * b0 + a1 * b1)) < 1 := by
  let ua := Real.sqrt (a0 ^ 2 + a1 ^ 2 + a2 ^ 2)
  let vb := Real.sqrt (b0 ^ 2 + b1 ^ 2 + b2 ^ 2)
  have hua_nn : 0 ≤ ua := Real.sqrt_nonneg _
  have hvb_nn : 0 ≤ vb := Real.sqrt_nonneg _
  have hua_sq : ua ^ 2 = a0 ^ 2 + a1 ^ 2 + a2 ^ 2 := Real.sq_sqrt (by positivity)
  have hvb_sq : vb ^ 2 = b0 ^ 2 + b1 ^ 2 + b2 ^ 2 := Real.sq_sqrt (by positivity)
  have hba : ua ^ 2 + a3 ^ 2 ≤ R ^ 2 := by rw [hua_sq]; exact ha_ball
  have hbb : vb ^ 2 + b3 ^ 2 ≤ R ^ 2 := by rw [hvb_sq]; exact hb_ball
  have hp0a : ua ^ 2 + a3 ^ 2 ≤ 1 - R ^ 2 + 2 * R * a3 := by rw [hua_sq]; exact ha_p0
  have hp0b : vb ^ 2 + b3 ^ 2 ≤ 1 - R ^ 2 + 2 * R * b3 := by rw [hvb_sq]; exact hb_p0
  have hrhoa : Real.sqrt (1 - (29 / 50 : ℝ) ^ 2) * ua ≤ Real.sqrt (a0 ^ 2 + a1 ^ 2) := by
    rw [← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    linarith only [haCone]
  have hrhob : (Real.sqrt 5 / 3) * vb ≤ Real.sqrt (b0 ^ 2 + b1 ^ 2) := by
    have h1 : ((Real.sqrt 5 / 3) * vb) ^ 2 ≤ b0 ^ 2 + b1 ^ 2 := by
      rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num), hvb_sq]
      linarith only [hbCone]
    exact Real.le_sqrt_of_sq_le h1
  have hbc_prod : (469 / 2500 : ℝ) * (ua * vb) ≤ a0 * b0 + a1 * b1 := by
    have h1 : c5 * (Real.sqrt (1 - (29 / 50 : ℝ) ^ 2) * ua) * ((Real.sqrt 5 / 3) * vb) ≤
        c5 * Real.sqrt (a0 ^ 2 + a1 ^ 2) * Real.sqrt (b0 ^ 2 + b1 ^ 2) := by
      have hc := c5_pos
      have hmul := mul_le_mul hrhoa hrhob (by positivity) (Real.sqrt_nonneg _)
      have hmul2 := mul_le_mul_of_nonneg_left hmul hc.le
      linarith only [hmul2]
    have h2 := bc_le_c5_prod
    have h3 : (469 / 2500 : ℝ) * (ua * vb) ≤
        (c5 * Real.sqrt (1 - (29 / 50 : ℝ) ^ 2) * (Real.sqrt 5 / 3)) * (ua * vb) :=
      mul_le_mul_of_nonneg_right h2 (mul_nonneg hua_nn hvb_nn)
    linarith only [h1, h3, hab_sec]
  have hb2_le : b2 ≤ (2 / 3 : ℝ) * vb := by
    have : b2 ^ 2 ≤ ((2 / 3 : ℝ) * vb) ^ 2 := by rw [mul_pow, hvb_sq]; linarith only [hbCone]
    nlinarith only [this, hb2, hvb_nn]
  by_cases hua0 : ua = 0
  · have hf2a0 : a2 = 0 := by
      rw [hua0] at hua_sq
      nlinarith only [hua_sq, sq_nonneg a0, sq_nonneg a1]
    have hdot_nn : 0 ≤ a2 * b2 + (a0 * b0 + a1 * b1) := by
      rw [hf2a0, zero_mul, zero_add]; linarith only [hbc_prod, mul_nonneg hua_nn hvb_nn]
    have hnine := nine_parts_pair_lt_one hRhi haτ hbτ ha_ball hb_ball ha_p0 hb_p0
    linarith only [hdot_nn, hnine]
  · have hua_pos : 0 < ua := lt_of_le_of_ne hua_nn (Ne.symm hua0)
    let s : ℝ := (-a2) / ua
    have hs_nn : 0 ≤ s := div_nonneg (by linarith only [ha2]) hua_pos.le
    have hs_hi : s ≤ 29 / 50 := by
      rw [div_le_iff₀ hua_pos]
      have : (-a2) ^ 2 ≤ ((29 / 50 : ℝ) * ua) ^ 2 := by rw [mul_pow, hua_sq]; linarith only [haCone]
      nlinarith only [this, ha2, hua_nn]
    have hf2a_eq : a2 = -(s * ua) := by dsimp only [s]; field_simp [hua_pos.ne']
    by_cases hks : (2 / 3 : ℝ) * s - 469 / 2500 ≤ 0
    · have hdot_nn : 0 ≤ a2 * b2 + (a0 * b0 + a1 * b1) := by
        have h1 : (-a2) * b2 ≤ (s * ua) * ((2 / 3 : ℝ) * vb) := by
          rw [hf2a_eq, neg_neg]
          exact mul_le_mul_of_nonneg_left hb2_le (by positivity)
        have h2 : (s * ua) * ((2 / 3 : ℝ) * vb) ≤ (469 / 2500 : ℝ) * (ua * vb) := by
          have := mul_le_mul_of_nonneg_right hks (mul_nonneg hua_nn hvb_nn)
          linarith only [this]
        linarith only [h1, h2, hbc_prod]
      have hnine := nine_parts_pair_lt_one hRhi haτ hbτ ha_ball hb_ball ha_p0 hb_p0
      linarith only [hdot_nn, hnine]
    · have hks_pos : 0 < (2 / 3 : ℝ) * s - 469 / 2500 := lt_of_not_ge hks
      have hs_lo : (7 / 25 : ℝ) ≤ s := by linarith only [hks_pos]
      have hcross : -(a2 * b2 + (a0 * b0 + a1 * b1)) ≤ ((2 / 3 : ℝ) * s - 469 / 2500) * (ua * vb) := by
        have h1 : (-a2) * b2 ≤ (s * ua) * ((2 / 3 : ℝ) * vb) := by
          rw [hf2a_eq, neg_neg]
          exact mul_le_mul_of_nonneg_left hb2_le (by positivity)
        linarith only [h1, hbc_prod]
      have hamgm : 2 * (((2 / 3 : ℝ) * s - 469 / 2500) * (ua * vb)) ≤
          ((2 / 3 : ℝ) * s - 469 / 2500) * (ua ^ 2 + vb ^ 2) := by
        nlinarith only [hks_pos, sq_nonneg (ua - vb)]
      have hp1a : ua ^ 2 + 2 * (s * r1) * ua ≤ 1 - R ^ 2 + 2 * t1 * a3 - a3 ^ 2 := by
        have h := ha_p1
        rw [← hua_sq, hf2a_eq] at h
        linarith only [h]
      have hw := wedge_opp_lt_one hRlo.le hRhi hr1_pos.le hr1sq ht1_hi ht1_lo
        hs_lo hs_hi hks_pos.le ha3_ge haτ hb3_ge hbτ
        hua_nn hvb_nn hba hbb hp0a hp0b hp1a
      have hident : (a0 ^ 2 + a1 ^ 2 + a2 ^ 2 + a3 ^ 2) + (b0 ^ 2 + b1 ^ 2 + b2 ^ 2 + b3 ^ 2) - 2 * a3 * b3 =
          (a3 - b3) ^ 2 + ua ^ 2 + vb ^ 2 := by rw [← hua_sq, ← hvb_sq]; ring
      linarith only [hident, hcross, hamgm, hw]

private lemma north_coords_lt_one {R x0 x1 x2 x3 y0 y1 y2 y3 : ℝ}
    (hRlo : (4 / 7 : ℝ) < R) (hRhi : R ≤ 627 / 1000)
    (hx_ball : x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 ≤ R ^ 2)
    (hy_ball : y0 ^ 2 + y1 ^ 2 + y2 ^ 2 + y3 ^ 2 ≤ R ^ 2)
    (hx_p0 : x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 ≤ 1 - R ^ 2 + 2 * R * x3)
    (hy_p0 : y0 ^ 2 + y1 ^ 2 + y2 ^ 2 + y3 ^ 2 ≤ 1 - R ^ 2 + 2 * R * y3)
    (hx3_mR : -R ≤ x3) (hy3_mR : -R ≤ y3)
    (hxτ : x3 ≤ (37 / 20 : ℝ) * R - 389 / 500) (hyτ : y3 ≤ (37 / 20 : ℝ) * R - 389 / 500)
    (hx2 : 0 ≤ x2) (hy2 : 0 ≤ y2)
    (hxCone : (4 / 9 : ℝ) * (x0 ^ 2 + x1 ^ 2 + x2 ^ 2) ≤ x2 ^ 2)
    (hyCone : (4 / 9 : ℝ) * (y0 ^ 2 + y1 ^ 2 + y2 ^ 2) ≤ y2 ^ 2) :
    (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2) + (y0 ^ 2 + y1 ^ 2 + y2 ^ 2 + y3 ^ 2) -
      2 * (x0 * y0 + x1 * y1 + x2 * y2 + x3 * y3) < 1 := by
  have hR_pos : (0 : ℝ) < R := by linarith only [hRlo]
  let ux := Real.sqrt (x0 ^ 2 + x1 ^ 2 + x2 ^ 2)
  let vy := Real.sqrt (y0 ^ 2 + y1 ^ 2 + y2 ^ 2)
  have hux_nn : 0 ≤ ux := Real.sqrt_nonneg _
  have hvy_nn : 0 ≤ vy := Real.sqrt_nonneg _
  have hux_sq : ux ^ 2 = x0 ^ 2 + x1 ^ 2 + x2 ^ 2 := Real.sq_sqrt (by positivity)
  have hvy_sq : vy ^ 2 = y0 ^ 2 + y1 ^ 2 + y2 ^ 2 := Real.sq_sqrt (by positivity)
  have hcs : -(x0 * y0 + x1 * y1) ≤ Real.sqrt (x0 ^ 2 + x1 ^ 2) * Real.sqrt (y0 ^ 2 + y1 ^ 2) := by
    have h1 : (x0 * y0 + x1 * y1) ^ 2 ≤ (x0 ^ 2 + x1 ^ 2) * (y0 ^ 2 + y1 ^ 2) := by
      nlinarith only [sq_nonneg (x0 * y1 - x1 * y0)]
    have h2 : (Real.sqrt (x0 ^ 2 + x1 ^ 2) * Real.sqrt (y0 ^ 2 + y1 ^ 2)) ^ 2 =
        (x0 ^ 2 + x1 ^ 2) * (y0 ^ 2 + y1 ^ 2) := by
      rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    nlinarith only [h1, h2, mul_nonneg (Real.sqrt_nonneg (x0 ^ 2 + x1 ^ 2)) (Real.sqrt_nonneg (y0 ^ 2 + y1 ^ 2))]
  have hr2x : x0 ^ 2 + x1 ^ 2 ≤ (5 / 9 : ℝ) * ux ^ 2 := by rw [hux_sq]; linarith only [hxCone]
  have hr2y : y0 ^ 2 + y1 ^ 2 ≤ (5 / 9 : ℝ) * vy ^ 2 := by rw [hvy_sq]; linarith only [hyCone]
  have hprod_rho : Real.sqrt (x0 ^ 2 + x1 ^ 2) * Real.sqrt (y0 ^ 2 + y1 ^ 2) ≤ (5 / 9 : ℝ) * (ux * vy) := by
    have h1 : (Real.sqrt (x0 ^ 2 + x1 ^ 2) * Real.sqrt (y0 ^ 2 + y1 ^ 2)) ^ 2 ≤ ((5 / 9 : ℝ) * (ux * vy)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      have hm := mul_le_mul hr2x hr2y (by positivity) (by positivity)
      nlinarith only [hm]
    nlinarith only [h1, mul_nonneg (Real.sqrt_nonneg (x0 ^ 2 + x1 ^ 2)) (Real.sqrt_nonneg (y0 ^ 2 + y1 ^ 2)),
      mul_nonneg hux_nn hvy_nn]
  have hprod_x2 : (4 / 9 : ℝ) * (ux * vy) ≤ x2 * y2 := by
    have hx2' : (2 / 3 : ℝ) * ux ≤ x2 := by nlinarith only [hx2, hxCone, hux_nn, hux_sq]
    have hy2' : (2 / 3 : ℝ) * vy ≤ y2 := by nlinarith only [hy2, hyCone, hvy_nn, hvy_sq]
    have hm := mul_le_mul hx2' hy2' (by positivity) hx2
    linarith only [hm]
  have hdist_le : (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2) + (y0 ^ 2 + y1 ^ 2 + y2 ^ 2 + y3 ^ 2) -
      2 * (x0 * y0 + x1 * y1 + x2 * y2 + x3 * y3) ≤
      (10 / 9 : ℝ) * ((x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2) + (y0 ^ 2 + y1 ^ 2 + y2 ^ 2 + y3 ^ 2)) -
        2 * x3 * y3 - (1 / 9 : ℝ) * (x3 ^ 2 + y3 ^ 2) := by
    nlinarith only [hux_sq, hvy_sq, hcs, hprod_rho, hprod_x2, sq_nonneg (ux - vy)]
  by_cases hsign : 0 ≤ x3 * y3
  · nlinarith only [hdist_le, hsign, hx_ball, hy_ball, hRhi, hR_pos, sq_nonneg x3, sq_nonneg y3]
  · by_cases hxneg : x3 ≤ 0
    · have hypos : 0 ≤ y3 := by by_contra! hy; exact hsign (mul_nonneg_of_nonpos_of_nonpos hxneg hy.le)
      have h := north_opp_lt_one hRlo.le hRhi hx3_mR hxneg hypos hyτ hx_ball hy_ball hx_p0
      linarith only [hdist_le, h]
    · have hxpos : 0 ≤ x3 := le_of_not_ge hxneg
      have hyneg : y3 ≤ 0 := by by_contra! hy; exact hsign (mul_nonneg hxpos hy.le)
      have h := north_opp_lt_one hRlo.le hRhi hy3_mR hyneg hxpos hxτ hy_ball hx_ball hy_p0
      linarith only [hdist_le, h, show x3 * y3 = y3 * x3 by ring]

private lemma south_coords_lt_one {R t1 r1 x0 x1 x2 x3 y0 y1 y2 y3 : ℝ}
    (hRlo : (4 / 7 : ℝ) < R) (hRhi : R ≤ 627 / 1000)
    (hr1_pos : 0 < r1) (hr1sq : r1 ^ 2 + t1 ^ 2 = R ^ 2)
    (ht1_hi : t1 ≤ -R / 4) (ht1_lo : R - 1 / (2 * R) ≤ t1)
    (hx_ball : x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 ≤ R ^ 2)
    (hy_ball : y0 ^ 2 + y1 ^ 2 + y2 ^ 2 + y3 ^ 2 ≤ R ^ 2)
    (hx_p0 : x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 ≤ 1 - R ^ 2 + 2 * R * x3)
    (hy_p0 : y0 ^ 2 + y1 ^ 2 + y2 ^ 2 + y3 ^ 2 ≤ 1 - R ^ 2 + 2 * R * y3)
    (hx_p1 : x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 ≤ 1 - R ^ 2 + 2 * r1 * x2 + 2 * t1 * x3)
    (hy_p1 : y0 ^ 2 + y1 ^ 2 + y2 ^ 2 + y3 ^ 2 ≤ 1 - R ^ 2 + 2 * r1 * y2 + 2 * t1 * y3)
    (hx3_ge : R - 1 ≤ x3) (hy3_ge : R - 1 ≤ y3)
    (hxτ : x3 ≤ (37 / 20 : ℝ) * R - 389 / 500) (hyτ : y3 ≤ (37 / 20 : ℝ) * R - 389 / 500)
    (hx2 : x2 ≤ 0) (hy2 : y2 ≤ 0)
    (hxCone : (841 / 2500 : ℝ) * (x0 ^ 2 + x1 ^ 2 + x2 ^ 2) ≤ x2 ^ 2)
    (hyCone : (841 / 2500 : ℝ) * (y0 ^ 2 + y1 ^ 2 + y2 ^ 2) ≤ y2 ^ 2) :
    (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2) + (y0 ^ 2 + y1 ^ 2 + y2 ^ 2 + y3 ^ 2) -
      2 * (x0 * y0 + x1 * y1 + x2 * y2 + x3 * y3) < 1 := by
  let ux := Real.sqrt (x0 ^ 2 + x1 ^ 2 + x2 ^ 2)
  let vy := Real.sqrt (y0 ^ 2 + y1 ^ 2 + y2 ^ 2)
  have hux_nn : 0 ≤ ux := Real.sqrt_nonneg _
  have hvy_nn : 0 ≤ vy := Real.sqrt_nonneg _
  have hux_sq : ux ^ 2 = x0 ^ 2 + x1 ^ 2 + x2 ^ 2 := Real.sq_sqrt (by positivity)
  have hvy_sq : vy ^ 2 = y0 ^ 2 + y1 ^ 2 + y2 ^ 2 := Real.sq_sqrt (by positivity)
  have hcs : -(x0 * y0 + x1 * y1) ≤ Real.sqrt (x0 ^ 2 + x1 ^ 2) * Real.sqrt (y0 ^ 2 + y1 ^ 2) := by
    have h1 : (x0 * y0 + x1 * y1) ^ 2 ≤ (x0 ^ 2 + x1 ^ 2) * (y0 ^ 2 + y1 ^ 2) := by
      nlinarith only [sq_nonneg (x0 * y1 - x1 * y0)]
    have h2 : (Real.sqrt (x0 ^ 2 + x1 ^ 2) * Real.sqrt (y0 ^ 2 + y1 ^ 2)) ^ 2 =
        (x0 ^ 2 + x1 ^ 2) * (y0 ^ 2 + y1 ^ 2) := by
      rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    nlinarith only [h1, h2, mul_nonneg (Real.sqrt_nonneg (x0 ^ 2 + x1 ^ 2)) (Real.sqrt_nonneg (y0 ^ 2 + y1 ^ 2))]
  have hr2x : x0 ^ 2 + x1 ^ 2 ≤ (1659 / 2500 : ℝ) * ux ^ 2 := by rw [hux_sq]; linarith only [hxCone]
  have hr2y : y0 ^ 2 + y1 ^ 2 ≤ (1659 / 2500 : ℝ) * vy ^ 2 := by rw [hvy_sq]; linarith only [hyCone]
  have hprod_rho : Real.sqrt (x0 ^ 2 + x1 ^ 2) * Real.sqrt (y0 ^ 2 + y1 ^ 2) ≤ (1659 / 2500 : ℝ) * (ux * vy) := by
    have h1 : (Real.sqrt (x0 ^ 2 + x1 ^ 2) * Real.sqrt (y0 ^ 2 + y1 ^ 2)) ^ 2 ≤ ((1659 / 2500 : ℝ) * (ux * vy)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      have hm := mul_le_mul hr2x hr2y (by positivity) (by positivity)
      nlinarith only [hm]
    nlinarith only [h1, mul_nonneg (Real.sqrt_nonneg (x0 ^ 2 + x1 ^ 2)) (Real.sqrt_nonneg (y0 ^ 2 + y1 ^ 2)),
      mul_nonneg hux_nn hvy_nn]
  have hx2_le : (29 / 50 : ℝ) * ux ≤ -x2 := by nlinarith only [hx2, hxCone, hux_nn, hux_sq]
  have hy2_le : (29 / 50 : ℝ) * vy ≤ -y2 := by nlinarith only [hy2, hyCone, hvy_nn, hvy_sq]
  have hprod_x2 : (841 / 2500 : ℝ) * (ux * vy) ≤ x2 * y2 := by
    have hm := mul_le_mul hx2_le hy2_le (by positivity) (by linarith only [hx2])
    linarith only [hm]
  have hdist_le : (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2) + (y0 ^ 2 + y1 ^ 2 + y2 ^ 2 + y3 ^ 2) -
      2 * (x0 * y0 + x1 * y1 + x2 * y2 + x3 * y3) ≤ (x3 - y3) ^ 2 + (1659 / 1250 : ℝ) * (ux ^ 2 + vy ^ 2) := by
    nlinarith only [hux_sq, hvy_sq, hcs, hprod_rho, hprod_x2, sq_nonneg (ux - vy)]
  have hp1x' : ux ^ 2 + 2 * ((29 / 50 : ℝ) * r1) * ux ≤ 1 - R ^ 2 + 2 * t1 * x3 - x3 ^ 2 := by
    nlinarith only [hx_p1, hux_sq, hx2_le, hr1_pos]
  have hp1y' : vy ^ 2 + 2 * ((29 / 50 : ℝ) * r1) * vy ≤ 1 - R ^ 2 + 2 * t1 * y3 - y3 ^ 2 := by
    nlinarith only [hy_p1, hvy_sq, hy2_le, hr1_pos]
  have hs := south_cell_lt_one hRlo.le hRhi hr1_pos.le hr1sq ht1_hi ht1_lo
    hx3_ge hxτ hy3_ge hyτ hux_nn hvy_nn
    (by rw [hux_sq]; exact hx_ball) (by rw [hvy_sq]; exact hy_ball)
    (by rw [hux_sq]; exact hx_p0) (by rw [hvy_sq]; exact hy_p0)
    hp1x' hp1y'
  linarith only [hdist_le, hs]

private theorem mid_case_normalized {S : Set E4} (hS : IsCompact S) (hne : S.Nonempty)
    (hd : Metric.diam S = 1) (hmin : ∀ c : E4, radiusAt S 0 ≤ radiusAt S c)
    (hRlo : (4 / 7 : ℝ) < radiusAt S 0) (hRhi : radiusAt S 0 ≤ 627 / 1000) :
    ∃ C : Fin 8 → Set E4, (∀ i, IsClosed (C i)) ∧ S ⊆ ⋃ i, C i ∧
      ∀ i, ∀ x ∈ S ∩ C i, ∀ y ∈ S ∩ C i, dist x y ≠ 1 := by
  classical
  let R := radiusAt S 0
  have hR_pos : (0 : ℝ) < R := by linarith
  have hRsq : (1 / 4 : ℝ) < R ^ 2 := by nlinarith
  have hwithin : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 1 := fun x hx y hy =>
    (Metric.dist_le_diam_of_mem hS.isBounded hx hy).trans_eq hd
  obtain ⟨p0, p1, hp0S, hp1S, hp0n, hp1n, hobt⟩ :=
    exists_two_obtuse_contacts hS hne hd.le hmin hRsq
  let e3 : E4 := R⁻¹ • p0
  have he3n : ‖e3‖ = 1 := by
    dsimp only [e3]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR_pos), hp0n, inv_mul_cancel₀ hR_pos.ne']
  have hp0_eq : p0 = R • e3 := by
    dsimp only [e3]; rw [smul_smul, mul_inv_cancel₀ hR_pos.ne', one_smul]
  let t1 : ℝ := inner ℝ p1 e3
  have ht1_hi : t1 ≤ -R / 4 := by
    have h : R * t1 = inner ℝ p0 p1 := by
      rw [hp0_eq, inner_smul_left]
      simp [t1, real_inner_comm]
    nlinarith only [h, hobt, hR_pos]
  have ht1_lo : R - 1 / (2 * R) ≤ t1 := by
    have hdist : ‖p0 - p1‖ ^ 2 ≤ 1 := by
      have := hwithin p0 hp0S p1 hp1S
      rw [dist_eq_norm] at this
      nlinarith only [this, norm_nonneg (p0 - p1)]
    rw [norm_sub_sq_real, hp0n, hp1n] at hdist
    have h : inner ℝ p0 p1 = R * t1 := by
      rw [hp0_eq, inner_smul_left]; simp [t1, real_inner_comm]
    rw [h] at hdist
    rw [sub_le_iff_le_add]
    have hmul : 2 * R * (R - t1) ≤ 1 := by linarith only [hdist]
    have : R - t1 ≤ 1 / (2 * R) := (le_div_iff₀ (by positivity)).mpr (by linarith only [hmul])
    linarith only [this]
  let q : E4 := p1 - t1 • e3
  have hq_orth : inner ℝ q e3 = 0 := by
    simp [q, inner_sub_left, inner_smul_left, he3n, t1]
  let r1 : ℝ := ‖q‖
  have hr1sq : r1 ^ 2 + t1 ^ 2 = R ^ 2 := by
    have h1 : ‖p1‖ ^ 2 = ‖q‖ ^ 2 + t1 ^ 2 := by
      have hp1q : p1 = q + t1 • e3 := by simp [q]
      rw [hp1q, norm_add_sq_real, inner_smul_right, hq_orth, norm_smul, Real.norm_eq_abs, he3n]
      nlinarith only [sq_abs t1]
    rw [hp1n] at h1
    dsimp only [r1]
    linarith only [h1]
  have hr1_pos : 0 < r1 := by
    have htsq : t1 ^ 2 < R ^ 2 := by
      have h1 : R - 1 / (2 * R) > -R := by
        have : 1 / (2 * R) < 2 * R := by rw [div_lt_iff₀ (by positivity)]; nlinarith only [hRsq]
        linarith only [this]
      nlinarith only [h1, ht1_lo, ht1_hi, hR_pos]
    have : 0 < r1 ^ 2 := by linarith only [hr1sq, htsq]
    nlinarith only [this, norm_nonneg q]
  let e2 : E4 := r1⁻¹ • q
  have he2n : ‖e2‖ = 1 := by
    simp [e2, norm_smul, r1, hr1_pos.ne']
  have he23 : inner ℝ e2 e3 = 0 := by
    simp [e2, inner_smul_left, hq_orth]
  have hp1_eq : p1 = r1 • e2 + t1 • e3 := by
    dsimp only [e2, q]; rw [smul_smul, mul_inv_cancel₀ hr1_pos.ne', one_smul, sub_add_cancel]
  -- Extend {e2, e3} at indices 2, 3 to an orthonormal basis b : OrthonormalBasis (Fin 4) ℝ E4
  let idxSet : Set (Fin 4) := {(2 : Fin 4), (3 : Fin 4)}
  let v0 : Fin 4 → E4 := fun i => if i = 2 then e2 else e3
  have horth : Orthonormal ℝ (idxSet.domRestrict v0) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi := i.property
    have hj := j.property
    simp only [idxSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · have hij : i = j := Subtype.ext (hi.trans hj.symm)
      subst hij
      simp only [↓reduceIte, Set.domRestrict, v0, hi, real_inner_self_eq_norm_sq, he2n, one_pow]
    · have hij : i ≠ j := fun h => by have := congrArg Subtype.val h; rw [hi, hj] at this; exact absurd this (by decide)
      simp only [hij, ↓reduceIte, Set.domRestrict, v0, hi, hj, show (3 : Fin 4) ≠ 2 by decide, he23]
    · have hij : i ≠ j := fun h => by have := congrArg Subtype.val h; rw [hi, hj] at this; exact absurd this (by decide)
      simp only [hij, ↓reduceIte, Set.domRestrict, v0, hi, hj, show (3 : Fin 4) ≠ 2 by decide]
      rw [real_inner_comm, he23]
    · have hij : i = j := Subtype.ext (hi.trans hj.symm)
      subst hij
      simp only [↓reduceIte, Set.domRestrict, v0, hi, show (3 : Fin 4) ≠ 2 by decide,
        real_inner_self_eq_norm_sq, he3n, one_pow]
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq
    (show Module.finrank ℝ E4 = Fintype.card (Fin 4) by simp [E4])
  have hb2 : b 2 = e2 := by
    have := hb 2 (by simp [idxSet])
    simpa [v0] using this
  have hb3 : b 3 = e3 := by
    have := hb 3 (by simp [idxSet])
    simpa [v0] using this
  let f (k : Fin 4) (x : E4) : ℝ := b.repr x k
  have hf_cont (k : Fin 4) : Continuous (f k) :=
    (PiLp.continuous_apply 2 _ k).comp b.repr.continuous
  have hnorm_eq (x : E4) : ‖x‖ ^ 2 = f 0 x ^ 2 + f 1 x ^ 2 + f 2 x ^ 2 + f 3 x ^ 2 := by
    have h1 : ‖b.repr x‖ ^ 2 = ‖x‖ ^ 2 := by rw [b.repr.norm_map]
    rw [← h1, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
  have hinner_eq (x y : E4) : inner ℝ x y = f 0 x * f 0 y + f 1 x * f 1 y + f 2 x * f 2 y + f 3 x * f 3 y := by
    have hi (k : Fin 4) : inner ℝ x (b k) * inner ℝ (b k) y = f k x * f k y := by
      simp only [f, b.repr_apply_apply, real_inner_comm (b k) x]
    have hsum : ∑ k : Fin 4, f k x * f k y = inner ℝ x y := by
      simpa only [hi] using b.sum_inner_mul_inner x y
    rw [← hsum, Fin.sum_univ_four]
  have hinner_p0 (x : E4) : inner ℝ x p0 = R * f 3 x := by
    rw [hp0_eq, ← hb3, inner_smul_right, real_inner_comm (b 3) x, ← b.repr_apply_apply]
  have hinner_p1 (x : E4) : inner ℝ x p1 = r1 * f 2 x + t1 * f 3 x := by
    rw [hp1_eq, ← hb2, ← hb3, inner_add_right, inner_smul_right, inner_smul_right,
      real_inner_comm (b 2) x, real_inner_comm (b 3) x, ← b.repr_apply_apply, ← b.repr_apply_apply]
  have hball (x : E4) (hx : x ∈ S) : ‖x‖ ^ 2 ≤ R ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg x) (by simpa [R] using dist_le_radiusAt hS hne hx 0) 2
  have hp0_bound (x : E4) (hx : x ∈ S) : ‖x‖ ^ 2 ≤ 1 - R ^ 2 + 2 * R * f 3 x := by
    have h := pow_le_pow_left₀ dist_nonneg (hwithin x hx p0 hp0S) 2
    rw [dist_eq_norm, norm_sub_sq_real, hp0n, hinner_p0] at h
    linarith
  have hp1_bound (x : E4) (hx : x ∈ S) : ‖x‖ ^ 2 ≤ 1 - R ^ 2 + 2 * r1 * f 2 x + 2 * t1 * f 3 x := by
    have h := pow_le_pow_left₀ dist_nonneg (hwithin x hx p1 hp1S) 2
    rw [dist_eq_norm, norm_sub_sq_real, hp1n, hinner_p1] at h
    linarith
  have hx3_ge (x : E4) (hx : x ∈ S) : R - 1 ≤ f 3 x := by
    have h1 := hp0_bound x hx
    have h2 := hnorm_eq x
    nlinarith [sq_nonneg (f 0 x), sq_nonneg (f 1 x), sq_nonneg (f 2 x)]
  have hx3_ge_mR (x : E4) (hx : x ∈ S) : -R ≤ f 3 x := by
    have h1 := hball x hx
    have h2 := hnorm_eq x
    nlinarith [sq_nonneg (f 0 x), sq_nonneg (f 1 x), sq_nonneg (f 2 x)]
  -- Define the 8 closed sets
  let τ : ℝ := (37 / 20 : ℝ) * R - 389 / 500
  let r3sq (x : E4) : ℝ := f 0 x ^ 2 + f 1 x ^ 2 + f 2 x ^ 2
  have hr3_cont : Continuous r3sq := by
    dsimp only [r3sq]
    exact (((hf_cont 0).pow 2).add ((hf_cont 1).pow 2)).add ((hf_cont 2).pow 2)
  let C : Fin 8 → Set E4
    | 0 => {x | τ ≤ f 3 x}
    | 1 => {x | f 3 x ≤ τ ∧ 0 ≤ f 2 x ∧ (4 / 9 : ℝ) * r3sq x ≤ f 2 x ^ 2}
    | 2 => {x | f 3 x ≤ τ ∧ f 2 x ≤ 0 ∧ (841 / 2500 : ℝ) * r3sq x ≤ f 2 x ^ 2}
    | 3 => {x | f 3 x ≤ τ ∧ (f 2 x ≤ 0 ∨ f 2 x ^ 2 ≤ (4 / 9 : ℝ) * r3sq x) ∧
        (0 ≤ f 2 x ∨ f 2 x ^ 2 ≤ (841 / 2500 : ℝ) * r3sq x) ∧ inSector 0 (f 0 x) (f 1 x)}
    | 4 => {x | f 3 x ≤ τ ∧ (f 2 x ≤ 0 ∨ f 2 x ^ 2 ≤ (4 / 9 : ℝ) * r3sq x) ∧
        (0 ≤ f 2 x ∨ f 2 x ^ 2 ≤ (841 / 2500 : ℝ) * r3sq x) ∧ inSector 1 (f 0 x) (f 1 x)}
    | 5 => {x | f 3 x ≤ τ ∧ (f 2 x ≤ 0 ∨ f 2 x ^ 2 ≤ (4 / 9 : ℝ) * r3sq x) ∧
        (0 ≤ f 2 x ∨ f 2 x ^ 2 ≤ (841 / 2500 : ℝ) * r3sq x) ∧ inSector 2 (f 0 x) (f 1 x)}
    | 6 => {x | f 3 x ≤ τ ∧ (f 2 x ≤ 0 ∨ f 2 x ^ 2 ≤ (4 / 9 : ℝ) * r3sq x) ∧
        (0 ≤ f 2 x ∨ f 2 x ^ 2 ≤ (841 / 2500 : ℝ) * r3sq x) ∧ inSector 3 (f 0 x) (f 1 x)}
    | 7 => {x | f 3 x ≤ τ ∧ (f 2 x ≤ 0 ∨ f 2 x ^ 2 ≤ (4 / 9 : ℝ) * r3sq x) ∧
        (0 ≤ f 2 x ∨ f 2 x ^ 2 ≤ (841 / 2500 : ℝ) * r3sq x) ∧ inSector 4 (f 0 x) (f 1 x)}
  have hsec_closed (k : Fin 5) : IsClosed {x : E4 | inSector k (f 0 x) (f 1 x)} := by
    apply IsClosed.inter
    · exact isClosed_le continuous_const
        ((continuous_const.mul (hf_cont 1)).sub (continuous_const.mul (hf_cont 0)))
    · exact isClosed_le
        ((continuous_const.mul (hf_cont 1)).sub (continuous_const.mul (hf_cont 0)))
        continuous_const
  have hW_closed (k : Fin 5) : IsClosed {x : E4 | f 3 x ≤ τ ∧
      (f 2 x ≤ 0 ∨ f 2 x ^ 2 ≤ (4 / 9 : ℝ) * r3sq x) ∧
      (0 ≤ f 2 x ∨ f 2 x ^ 2 ≤ (841 / 2500 : ℝ) * r3sq x) ∧ inSector k (f 0 x) (f 1 x)} := by
    refine (isClosed_le (hf_cont 3) continuous_const).inter ?_
    refine ((isClosed_le (hf_cont 2) continuous_const).union
      (isClosed_le ((hf_cont 2).pow 2) (continuous_const.mul hr3_cont))).inter ?_
    refine ((isClosed_le continuous_const (hf_cont 2)).union
      (isClosed_le ((hf_cont 2).pow 2) (continuous_const.mul hr3_cont))).inter ?_
    exact hsec_closed k
  refine ⟨C, ?_, ?_, ?_⟩
  · -- Closedness of all 8 sets
    intro i
    fin_cases i
    · exact isClosed_le continuous_const (hf_cont 3)
    · exact (isClosed_le (hf_cont 3) continuous_const).inter
        ((isClosed_le continuous_const (hf_cont 2)).inter
          (isClosed_le (continuous_const.mul hr3_cont) ((hf_cont 2).pow 2)))
    · exact (isClosed_le (hf_cont 3) continuous_const).inter
        ((isClosed_le (hf_cont 2) continuous_const).inter
          (isClosed_le (continuous_const.mul hr3_cont) ((hf_cont 2).pow 2)))
    · exact hW_closed 0
    · exact hW_closed 1
    · exact hW_closed 2
    · exact hW_closed 3
    · exact hW_closed 4
  · -- Covering
    intro x _
    apply Set.mem_iUnion.mpr
    by_cases hτ : τ ≤ f 3 x
    · exact ⟨0, hτ⟩
    · have hτle : f 3 x ≤ τ := le_of_not_ge hτ
      by_cases hN : 0 ≤ f 2 x ∧ (4 / 9 : ℝ) * r3sq x ≤ f 2 x ^ 2
      · exact ⟨1, hτle, hN.1, hN.2⟩
      · by_cases hS_cone : f 2 x ≤ 0 ∧ (841 / 2500 : ℝ) * r3sq x ≤ f 2 x ^ 2
        · exact ⟨2, hτle, hS_cone.1, hS_cone.2⟩
        · have hN' : f 2 x ≤ 0 ∨ f 2 x ^ 2 ≤ (4 / 9 : ℝ) * r3sq x := by
            by_cases h2 : 0 ≤ f 2 x
            · right; exact le_of_not_ge (fun h => hN ⟨h2, h⟩)
            · left; exact le_of_not_ge h2
          have hS' : 0 ≤ f 2 x ∨ f 2 x ^ 2 ≤ (841 / 2500 : ℝ) * r3sq x := by
            by_cases h2 : f 2 x ≤ 0
            · right; exact le_of_not_ge (fun h => hS_cone ⟨h2, h⟩)
            · left; exact le_of_not_ge h2
          obtain ⟨k, hk⟩ := exists_inSector (f 0 x) (f 1 x)
          fin_cases k
          · exact ⟨3, hτle, hN', hS', hk⟩
          · exact ⟨4, hτle, hN', hS', hk⟩
          · exact ⟨5, hτle, hN', hS', hk⟩
          · exact ⟨6, hτle, hN', hS', hk⟩
          · exact ⟨7, hτle, hN', hS', hk⟩
  · -- No diametral pair in any of the 8 cells
    -- Helper for all 5 wedge cells
    have hwedge_nodiam (k : Fin 5) (x y : E4) (hxS : x ∈ S) (hyS : y ∈ S)
        (hxτ : f 3 x ≤ τ) (hyτ : f 3 y ≤ τ)
        (hxN : f 2 x ≤ 0 ∨ f 2 x ^ 2 ≤ (4 / 9 : ℝ) * r3sq x)
        (hxS' : 0 ≤ f 2 x ∨ f 2 x ^ 2 ≤ (841 / 2500 : ℝ) * r3sq x)
        (hyN : f 2 y ≤ 0 ∨ f 2 y ^ 2 ≤ (4 / 9 : ℝ) * r3sq y)
        (hyS' : 0 ≤ f 2 y ∨ f 2 y ^ 2 ≤ (841 / 2500 : ℝ) * r3sq y)
        (hxk : inSector k (f 0 x) (f 1 x)) (hyk : inSector k (f 0 y) (f 1 y)) :
        dist x y ≠ 1 := by
      have hsec := sector_dot_ge hxk hyk
      have hdist_sq : dist x y ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * f 3 x * f 3 y -
          2 * (f 2 x * f 2 y + (f 0 x * f 0 y + f 1 x * f 1 y)) := by
        rw [dist_eq_norm, norm_sub_sq_real, hinner_eq]; ring
      suffices hlt : dist x y ^ 2 < 1 by intro he; rw [he] at hlt; norm_num at hlt
      -- Helper for the opposite-sign hemisphere case (a has f 2 a ≤ 0, b has 0 ≤ f 2 b)
      have hopp (a b : E4) (haS : a ∈ S) (hbS : b ∈ S)
          (haτ : f 3 a ≤ τ) (hbτ : f 3 b ≤ τ)
          (ha2 : f 2 a ≤ 0) (hb2 : 0 ≤ f 2 b)
          (haCone : f 2 a ^ 2 ≤ (841 / 2500 : ℝ) * r3sq a)
          (hbCone : f 2 b ^ 2 ≤ (4 / 9 : ℝ) * r3sq b)
          (hab_sec : c5 * Real.sqrt (f 0 a ^ 2 + f 1 a ^ 2) * Real.sqrt (f 0 b ^ 2 + f 1 b ^ 2) ≤
            f 0 a * f 0 b + f 1 a * f 1 b) :
          ‖a‖ ^ 2 + ‖b‖ ^ 2 - 2 * f 3 a * f 3 b -
            2 * (f 2 a * f 2 b + (f 0 a * f 0 b + f 1 a * f 1 b)) < 1 := by
        rw [hnorm_eq a, hnorm_eq b]
        exact wedge_opp_coords_lt_one hRlo hRhi hr1_pos hr1sq ht1_hi ht1_lo
          (hnorm_eq a ▸ hball a haS) (hnorm_eq b ▸ hball b hbS)
          (hnorm_eq a ▸ hp0_bound a haS) (hnorm_eq b ▸ hp0_bound b hbS)
          (hnorm_eq a ▸ hp1_bound a haS) (hx3_ge a haS) (hx3_ge b hbS)
          haτ hbτ ha2 hb2 haCone hbCone hab_sec
      by_cases hsame : 0 ≤ f 2 x * f 2 y
      · have hdot_nn : 0 ≤ f 2 x * f 2 y + (f 0 x * f 0 y + f 1 x * f 1 y) := by
          have hc5nn : 0 ≤ c5 * Real.sqrt (f 0 x ^ 2 + f 1 x ^ 2) * Real.sqrt (f 0 y ^ 2 + f 1 y ^ 2) := by
            have := c5_pos; positivity
          linarith only [hsame, hsec, hc5nn]
        have hnine := nine_parts_pair_lt_one hRhi hxτ hyτ (hball x hxS) (hball y hyS) (hp0_bound x hxS) (hp0_bound y hyS)
        linarith only [hdist_sq, hdot_nn, hnine]
      · by_cases hx2 : f 2 x ≤ 0
        · have hy2 : 0 ≤ f 2 y := by
            by_contra! hy
            exact hsame (mul_nonneg_of_nonpos_of_nonpos hx2 hy.le)
          have hxCone : f 2 x ^ 2 ≤ (841 / 2500 : ℝ) * r3sq x := by
            rcases hxS' with h | h
            · have : f 2 x = 0 := le_antisymm hx2 h
              rw [this]; simp only [zero_pow (by decide : 2 ≠ 0)]; dsimp only [r3sq]; positivity
            · exact h
          have hyCone : f 2 y ^ 2 ≤ (4 / 9 : ℝ) * r3sq y := by
            rcases hyN with h | h
            · have : f 2 y = 0 := le_antisymm h hy2
              rw [this]; simp only [zero_pow (by decide : 2 ≠ 0)]; dsimp only [r3sq]; positivity
            · exact h
          rw [hdist_sq]
          exact hopp x y hxS hyS hxτ hyτ hx2 hy2 hxCone hyCone hsec
        · have hx2' : 0 ≤ f 2 x := le_of_not_ge hx2
          have hy2 : f 2 y ≤ 0 := by
            by_contra! hy
            exact hsame (mul_nonneg hx2' hy.le)
          have hyCone : f 2 y ^ 2 ≤ (841 / 2500 : ℝ) * r3sq y := by
            rcases hyS' with h | h
            · have : f 2 y = 0 := le_antisymm hy2 h
              rw [this]; simp only [zero_pow (by decide : 2 ≠ 0)]; dsimp only [r3sq]; positivity
            · exact h
          have hxCone : f 2 x ^ 2 ≤ (4 / 9 : ℝ) * r3sq x := by
            rcases hxN with h | h
            · have : f 2 x = 0 := le_antisymm h hx2'
              rw [this]; simp only [zero_pow (by decide : 2 ≠ 0)]; dsimp only [r3sq]; positivity
            · exact h
          have hsec' : c5 * Real.sqrt (f 0 y ^ 2 + f 1 y ^ 2) * Real.sqrt (f 0 x ^ 2 + f 1 x ^ 2) ≤
              f 0 y * f 0 x + f 1 y * f 1 x := by
            linarith only [hsec,
              show c5 * Real.sqrt (f 0 y ^ 2 + f 1 y ^ 2) * Real.sqrt (f 0 x ^ 2 + f 1 x ^ 2) =
                c5 * Real.sqrt (f 0 x ^ 2 + f 1 x ^ 2) * Real.sqrt (f 0 y ^ 2 + f 1 y ^ 2) by ring,
              show f 0 y * f 0 x + f 1 y * f 1 x = f 0 x * f 0 y + f 1 x * f 1 y by ring]
          have h := hopp y x hyS hxS hyτ hxτ hy2 hx2' hyCone hxCone hsec'
          rw [hdist_sq]
          linarith only [h, show f 3 x * f 3 y = f 3 y * f 3 x by ring,
            show f 2 x * f 2 y = f 2 y * f 2 x by ring,
            show f 0 x * f 0 y + f 1 x * f 1 y = f 0 y * f 0 x + f 1 y * f 1 x by ring]
    intro i x hx y hy
    fin_cases i
    · -- Cell 0: Polar cap τ ≤ f 3 x
      have hxC : τ ≤ f 3 x := hx.2
      have hyC : τ ≤ f 3 y := hy.2
      have hτpos : 0 ≤ τ := by dsimp only [τ]; linarith only [hRlo]
      have hdx : dist x (τ • b 3) ^ 2 < 1 / 4 := by
        rw [dist_eq_norm, norm_sub_sq_real, inner_smul_right, real_inner_comm (b 3) x,
          ← b.repr_apply_apply, norm_smul, Real.norm_eq_abs, hb3, he3n]
        have h1 := hball x hx.1
        have h2 : R ^ 2 - τ ^ 2 < 1 / 4 := cap_rad_sq_lt_quarter (R := R)
        have h3 : τ ^ 2 ≤ τ * f 3 x := by nlinarith only [hxC, hτpos]
        change ‖x‖ ^ 2 - 2 * (τ * f 3 x) + (|τ| * 1) ^ 2 < 1 / 4
        nlinarith only [h1, h2, h3, sq_abs τ]
      have hdy : dist y (τ • b 3) ^ 2 < 1 / 4 := by
        rw [dist_eq_norm, norm_sub_sq_real, inner_smul_right, real_inner_comm (b 3) y,
          ← b.repr_apply_apply, norm_smul, Real.norm_eq_abs, hb3, he3n]
        have h1 := hball y hy.1
        have h2 : R ^ 2 - τ ^ 2 < 1 / 4 := cap_rad_sq_lt_quarter (R := R)
        have h3 : τ ^ 2 ≤ τ * f 3 y := by nlinarith only [hyC, hτpos]
        change ‖y‖ ^ 2 - 2 * (τ * f 3 y) + (|τ| * 1) ^ 2 < 1 / 4
        nlinarith only [h1, h2, h3, sq_abs τ]
      have hdx' : dist x (τ • b 3) < 1 / 2 := by nlinarith only [hdx, dist_nonneg (x := x) (y := τ • b 3)]
      have hdy' : dist y (τ • b 3) < 1 / 2 := by nlinarith only [hdy, dist_nonneg (x := y) (y := τ • b 3)]
      exact ((dist_triangle_right x y (τ • b 3)).trans_lt (by linarith only [hdx', hdy'])).ne
    · -- Cell 1: North cone
      have hxC : f 3 x ≤ τ ∧ 0 ≤ f 2 x ∧ (4 / 9 : ℝ) * r3sq x ≤ f 2 x ^ 2 := hx.2
      have hyC : f 3 y ≤ τ ∧ 0 ≤ f 2 y ∧ (4 / 9 : ℝ) * r3sq y ≤ f 2 y ^ 2 := hy.2
      suffices hlt : dist x y ^ 2 < 1 by intro he; rw [he] at hlt; norm_num at hlt
      rw [dist_eq_norm, norm_sub_sq_real, hinner_eq, hnorm_eq x, hnorm_eq y]
      have h := north_coords_lt_one hRlo hRhi
        (hnorm_eq x ▸ hball x hx.1) (hnorm_eq y ▸ hball y hy.1)
        (hnorm_eq x ▸ hp0_bound x hx.1) (hnorm_eq y ▸ hp0_bound y hy.1)
        (hx3_ge_mR x hx.1) (hx3_ge_mR y hy.1) hxC.1 hyC.1 hxC.2.1 hyC.2.1 hxC.2.2 hyC.2.2
      linarith only [h]
    · -- Cell 2: South cone
      have hxC : f 3 x ≤ τ ∧ f 2 x ≤ 0 ∧ (841 / 2500 : ℝ) * r3sq x ≤ f 2 x ^ 2 := hx.2
      have hyC : f 3 y ≤ τ ∧ f 2 y ≤ 0 ∧ (841 / 2500 : ℝ) * r3sq y ≤ f 2 y ^ 2 := hy.2
      suffices hlt : dist x y ^ 2 < 1 by intro he; rw [he] at hlt; norm_num at hlt
      rw [dist_eq_norm, norm_sub_sq_real, hinner_eq, hnorm_eq x, hnorm_eq y]
      have h := south_coords_lt_one hRlo hRhi hr1_pos hr1sq ht1_hi ht1_lo
        (hnorm_eq x ▸ hball x hx.1) (hnorm_eq y ▸ hball y hy.1)
        (hnorm_eq x ▸ hp0_bound x hx.1) (hnorm_eq y ▸ hp0_bound y hy.1)
        (hnorm_eq x ▸ hp1_bound x hx.1) (hnorm_eq y ▸ hp1_bound y hy.1)
        (hx3_ge x hx.1) (hx3_ge y hy.1) hxC.1 hyC.1 hxC.2.1 hyC.2.1 hxC.2.2 hyC.2.2
      linarith only [h]
    · exact hwedge_nodiam 0 x y hx.1 hy.1 hx.2.1 hy.2.1 hx.2.2.1 hx.2.2.2.1 hy.2.2.1 hy.2.2.2.1 hx.2.2.2.2 hy.2.2.2.2
    · exact hwedge_nodiam 1 x y hx.1 hy.1 hx.2.1 hy.2.1 hx.2.2.1 hx.2.2.2.1 hy.2.2.1 hy.2.2.2.1 hx.2.2.2.2 hy.2.2.2.2
    · exact hwedge_nodiam 2 x y hx.1 hy.1 hx.2.1 hy.2.1 hx.2.2.1 hx.2.2.2.1 hy.2.2.1 hy.2.2.2.1 hx.2.2.2.2 hy.2.2.2.2
    · exact hwedge_nodiam 3 x y hx.1 hy.1 hx.2.1 hy.2.1 hx.2.2.1 hx.2.2.2.1 hy.2.2.1 hy.2.2.2.1 hx.2.2.2.2 hy.2.2.2.2
    · exact hwedge_nodiam 4 x y hx.1 hy.1 hx.2.1 hy.2.1 hx.2.2.1 hx.2.2.2.1 hy.2.2.1 hy.2.2.2.1 hx.2.2.2.2 hy.2.2.2.2

private theorem mid_case {K : Set E4} (hK : IsCompact K) (hnt : K.Nontrivial)
    (hlo : ∀ c, ∃ x ∈ K, (4 / 7 : ℝ) * Metric.diam K < dist x c)
    (hhi : ∃ c, ∀ x ∈ K, dist x c ≤ (627 / 1000 : ℝ) * Metric.diam K) :
    ∃ C : Fin 8 → Set E4, (∀ i, IsClosed (C i)) ∧ K ⊆ ⋃ i, C i ∧
      ∀ i, ∀ x ∈ K ∩ C i, ∀ y ∈ K ∩ C i, dist x y ≠ Metric.diam K := by
  classical
  let D := Metric.diam K
  have hD : 0 < D := Metric.diam_pos hnt hK.isBounded
  obtain ⟨c, hc⟩ := exists_compact_centered_normalization hK.isBounded hD
  let g (x : E4) : E4 := D⁻¹ • x - c
  let S := g '' K
  have hset : (fun x => x - c) '' ((Metric.diam K)⁻¹ • closure K) = S := by
    rw [hK.isClosed.closure_eq, ← Set.image_smul, Set.image_image]
  dsimp only at hc
  rw [hset] at hc
  obtain ⟨hS, hdS, hmin⟩ := hc
  have hne : S.Nonempty := hnt.nonempty.image g
  have hRlo : (4 / 7 : ℝ) < radiusAt S 0 := by
    obtain ⟨x, hx, hfar⟩ := hlo (D • (c + 0))
    rw [change_center D hD] at hfar
    have hsmall := dist_le_radiusAt hS hne (show g x ∈ S from ⟨x, hx, rfl⟩) 0
    change (4 / 7 : ℝ) * D < D * dist (g x) 0 at hfar
    exact (lt_of_mul_lt_mul_left (by simpa [mul_comm] using hfar) hD.le).trans_le hsmall
  have hRhi : radiusAt S 0 ≤ 627 / 1000 := by
    obtain ⟨c1, hc1⟩ := hhi
    let d1 : E4 := g c1
    have hrad : radiusAt S d1 ≤ 627 / 1000 := by
      obtain ⟨y, hy, hry, _⟩ := radiusAt_attained hS hne d1
      rw [hry]
      obtain ⟨x, hx, rfl⟩ := hy
      have hdist : dist (g x) (g c1) = D⁻¹ * dist x c1 := by
        dsimp only [g]
        rw [dist_sub_right, dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hD)]
      rw [hdist]
      have hxc := hc1 x hx
      have : D⁻¹ * dist x c1 ≤ D⁻¹ * ((627 / 1000 : ℝ) * D) :=
        mul_le_mul_of_nonneg_left hxc (inv_pos.mpr hD).le
      have hsimp : D⁻¹ * ((627 / 1000 : ℝ) * D) = 627 / 1000 := by field_simp
      linarith
    exact (hmin d1).trans hrad
  obtain ⟨C, hCclosed, hCcov, hCnod⟩ := mid_case_normalized hS hne hdS hmin hRlo hRhi
  have hg_cont : Continuous g := (continuous_const_smul D⁻¹).sub continuous_const
  refine ⟨fun i => g ⁻¹' C i, fun i => (hCclosed i).preimage hg_cont, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hCcov ⟨x, hx, rfl⟩)
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  · intro i x hx y hy hxy
    apply hCnod i (g x) ⟨⟨x, hx.1, rfl⟩, hx.2⟩ (g y) ⟨⟨y, hy.1, rfl⟩, hy.2⟩
    dsimp only [g]
    rw [dist_sub_right, dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hD), hxy]
    exact inv_mul_cancel₀ hD.ne'

end BorsukEightMid



section BorsukEightFinal
open Metric Bornology Borsuk
open scoped EuclideanGeometry

open Metric Bornology Borsuk
open scoped EuclideanGeometry

private theorem four_axis (x : EuclideanSpace ℝ (Fin 4)) :
    ∃ i, ‖x‖ ≤ 2 * |x i| := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin 4 => |x i|) Finset.univ_nonempty
  have hsq : ‖x‖ ^ 2 ≤ 4 * |x i| ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      ∑ j, (x j)^2 ≤ ∑ _j : Fin 4, |x i| ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        rw [← sq_abs (x j)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hi j hj) 2
      _ = _ := by simp
  exact ⟨i, by nlinarith [norm_nonneg x, abs_nonneg (x i)]⟩

private theorem near_axis (x : EuclideanSpace ℝ (Fin 4)) (R : ℝ) (hR : ‖x‖ ≤ R) :
    ∃ i : Fin 4, ∃ a : Fin 2,
      ‖x - EuclideanSpace.single i (if a = 0 then R / 2 else -(R / 2))‖ ≤ (13/15 : ℝ)*R := by
  obtain ⟨i, hi⟩ := four_axis x
  have hpos : 0 ≤ R := (norm_nonneg x).trans hR
  have half : 0 ≤ (R - ‖x‖) * (R/2 + ‖x‖) := mul_nonneg (by linarith) (by positivity)
  have prod := mul_le_mul_of_nonneg_left hi hpos
  by_cases h : 0 ≤ x i
  · refine ⟨i, 0, ?_⟩
    change ‖x - EuclideanSpace.single i (R/2)‖ ≤ (13/15 : ℝ)*R
    rw [abs_of_nonneg h] at prod
    have sq := norm_sub_sq_real x (EuclideanSpace.single i (R/2))
    rw [EuclideanSpace.inner_single_right] at sq
    simp [Real.norm_eq_abs, abs_of_nonneg hpos] at sq
    nlinarith [sq_nonneg R, norm_nonneg (x - EuclideanSpace.single i (R/2))]
  · refine ⟨i, 1, ?_⟩
    change ‖x - EuclideanSpace.single i (-(R/2))‖ ≤ (13/15 : ℝ)*R
    rw [abs_of_neg (lt_of_not_ge h)] at prod
    have sq := norm_sub_sq_real x (EuclideanSpace.single i (-(R/2)))
    rw [EuclideanSpace.inner_single_right] at sq
    simp [Real.norm_eq_abs, abs_of_nonneg hpos] at sq
    nlinarith [sq_nonneg R, norm_nonneg (x - EuclideanSpace.single i (-(R/2)))]

private theorem ofReal_diam' {K : Set (EuclideanSpace ℝ (Fin 4))} (hb : IsBounded K) :
    ENNReal.ofReal (diam K) = ediam K :=
  ENNReal.ofReal_toReal (isBounded_iff_ediam_ne_top.mp hb)

private theorem ball_bound (c : EuclideanSpace ℝ (Fin 4)) (r : ℝ) :
    ediam (closedBall c r) ≤ ENNReal.ofReal (2*r) := by
  apply ediam_le_of_forall_dist_le
  intro x hx y hy
  exact (dist_triangle_right x y c).trans (by linarith [mem_closedBall.mp hx, mem_closedBall.mp hy])

private theorem small_case {K : Set (EuclideanSpace ℝ (Fin 4))} (hb : IsBounded K)
    (hnt : K.Nontrivial) {c : EuclideanSpace ℝ (Fin 4)}
    (hc : ∀ x ∈ K, dist x c ≤ (4/7 : ℝ)*diam K) : HasBorsukCover 8 K := by
  classical
  let R := (4/7 : ℝ) * diam K
  let center (i : Fin 4 × Fin 2) := c +
    EuclideanSpace.single i.1 (if i.2 = 0 then R/2 else -(R/2))
  let e : Fin 4 × Fin 2 ≃ Fin 8 := finProdFinEquiv
  refine ⟨fun j => closedBall (center (e.symm j)) ((13/15 : ℝ)*R), ?_, ?_⟩
  · intro x hx
    obtain ⟨i, a, hz⟩ := near_axis (x-c) R (by simpa [dist_eq_norm] using hc x hx)
    apply Set.mem_iUnion.mpr
    refine ⟨e (i,a), ?_⟩
    rw [e.symm_apply_apply]
    change dist x (c + _) ≤ _
    rw [dist_eq_norm, ← sub_sub]
    exact hz
  · intro j
    apply (ball_bound _ _).trans_lt
    rw [← ofReal_diam' hb]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).2 (by
      dsimp [R]
      linarith [diam_pos hnt hb])

private theorem compact_strict {K T : Set (EuclideanSpace ℝ (Fin 4))}
    (hK : IsCompact K) (hnt : K.Nontrivial) (hT : IsCompact T) (hsub : T ⊆ K)
    (hnod : ∀ x ∈ T, ∀ y ∈ T, dist x y ≠ diam K) : ediam T < ediam K := by
  rcases T.eq_empty_or_nonempty with rfl | hne
  · simpa using ediam_pos_iff.mpr hnt
  obtain ⟨⟨x,y⟩, hxy, hmax⟩ := (hT.prod hT).exists_isMaxOn (hne.prod hne)
    (continuous_fst.dist continuous_snd).continuousOn
  have ltD := (dist_le_diam_of_mem hK.isBounded (hsub hxy.1) (hsub hxy.2)).lt_of_ne
    (hnod x hxy.1 y hxy.2)
  have hb : ediam T ≤ ENNReal.ofReal (dist x y) := by
    apply ediam_le_of_forall_dist_le
    intro a ha b hb
    exact (isMaxOn_iff.mp hmax) (a,b) ⟨ha,hb⟩
  apply hb.trans_lt
  rw [← ofReal_diam' hK.isBounded]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).2 ltD

private theorem eight_of_seven_and_one {K : Set (EuclideanSpace ℝ (Fin 4))}
    (A : Fin 7 → Set (EuclideanSpace ℝ (Fin 4))) (T : Set (EuclideanSpace ℝ (Fin 4)))
    (hA : ∀ i, ediam (A i) < ediam K) (hT : ediam T < ediam K)
    (hall : ∀ x ∈ K, x ∈ T ∨ ∃ i, x ∈ A i) : HasBorsukCover 8 K := by
  classical
  refine ⟨Fin.cons T A, ?_, ?_⟩
  · intro x hx
    apply Set.mem_iUnion.mpr
    rcases hall x hx with h | ⟨i, hi⟩
    · exact ⟨0, by simpa using h⟩
    · exact ⟨i.succ, by simpa using hi⟩
  · exact Fin.cases (by simpa using hT) fun i => by simpa using hA i

private theorem large_case {K : Set (EuclideanSpace ℝ (Fin 4))}
    (hK : IsCompact K) (hnt : K.Nontrivial)
    {c : Fin 5 → EuclideanSpace ℝ (Fin 4)} {r : ℝ} (hr : 0 < r) (hrD : 2*r < diam K)
    (hit : ∀ x ∈ K, ∀ y ∈ K, dist x y = diam K →
      ∃ i, x ∈ ball (c i) r ∨ y ∈ ball (c i) r) : HasBorsukCover 8 K := by
  classical
  let U := ⋃ i, ball (c i) r
  let T := K \ U
  have hcomp : IsCompact T := hK.diff (isOpen_iUnion fun _ => isOpen_ball)
  have hT : ediam T < ediam K := by
    apply compact_strict hK hnt hcomp Set.sdiff_subset
    intro x hx y hy hd
    obtain ⟨i, hi⟩ := hit x hx.1 y hy.1 hd
    rcases hi with hi | hi
    · exact hx.2 (Set.mem_iUnion.mpr ⟨i,hi⟩)
    · exact hy.2 (Set.mem_iUnion.mpr ⟨i,hi⟩)
  let A (j : Fin 7) := if h : j.val < 5 then ball (c ⟨j.val,h⟩) r else ∅
  apply eight_of_seven_and_one A T _ hT
  · intro x hx
    by_cases hu : x ∈ U
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hu
      right
      exact ⟨⟨i.val, by have := i.isLt; omega⟩, by simpa [A, i.isLt] using hi⟩
    · exact Or.inl ⟨hx,hu⟩
  · intro j
    dsimp only [A]
    split
    · apply (ediam_mono ball_subset_closedBall).trans_lt
      apply (ball_bound _ _).trans_lt
      rw [← ofReal_diam' hK.isBounded]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).2 hrD
    · simpa using ediam_pos_iff.mpr hnt


end BorsukEightFinal

theorem OMA.solution : type_of% @Borsuk.borsuk_conjecture.four.eight_parts := by
  classical
  intro s hs hnt
  let K := closure s
  have hK : IsCompact K := hs.isCompact_closure
  have hntK : K.Nontrivial := hnt.mono subset_closure
  suffices cov : Borsuk.HasBorsukCover 8 K by
    obtain ⟨C, hC, hsmall⟩ := cov
    exact ⟨C, subset_closure.trans hC, fun i => by simpa [K, ediam_closure] using hsmall i⟩
  by_cases small : ∃ c, ∀ x ∈ K, dist x c ≤ (4 / 7 : ℝ) * Metric.diam K
  · obtain ⟨c, hc⟩ := small
    exact small_case hK.isBounded hntK hc
  push Not at small
  by_cases mid : ∃ c, ∀ x ∈ K, dist x c ≤ (627 / 1000 : ℝ) * Metric.diam K
  · obtain ⟨C, hclosed, hcover, hdist⟩ := mid_case hK hntK small mid
    refine ⟨fun j => K ∩ C j, ?_, fun j => compact_strict hK hntK
      (hK.inter_right (hclosed j)) Set.inter_subset_left (hdist j)⟩
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hx)
    exact Set.mem_iUnion.mpr ⟨i, hx, hi⟩
  · push Not at mid
    obtain ⟨c, r, hr, hrD, hit⟩ := hit_five hK hntK mid
    exact large_case hK hntK hr hrD hit

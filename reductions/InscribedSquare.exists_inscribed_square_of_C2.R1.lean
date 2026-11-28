import FormalConjectures.Wikipedia.InscribedSquare
import Mathlib

/-!
# From simple polygons to squares on regular curves

The first step is the square peg theorem for simple polygons, as in section 5.6
of Igor Pak's Lectures on Discrete and Polyhedral Geometry. The second step
asks for polygonal approximation with uniformly controlled local distortion.
An arc nearly isometric to a line cannot contain three corners of a square.
This prevents the limiting square from shrinking to a single point.
-/

namespace OMA.R_InscribedSquare_exists_inscribed_square_of_C2_R1

open Filter Topology Set Manifold ContDiff InscribedSquare
open scoped EuclideanGeometry

/-- A polygonal Jordan loop has a square whose corners lie on its image. -/
def H1 : Prop := ∀ p : Circle → ℝ², IsEmbedding p →
  (∃ (m : ℕ) (u v : Fin m → ℝ²), range p = ⋃ i, segment ℝ (u i) (v i)) →
  ∃ a b c d : Circle, IsRectangle (p a) (p b) (p c) (p d) 1

/-- The loops converge uniformly. Around each parameter there is a short arc
which, eventually, admits a real coordinate with distortion at most 9/8.
The neighborhood and the starting index can both depend on the parameter. -/
def H2 : Prop := ∀ γ : Circle → ℝ², IsSmoothEmbedding (𝓡 1) (𝓡 2) 2 γ →
  ∃ p : ℕ → Circle → ℝ²,
    (∀ n, IsEmbedding (p n) ∧
      ∃ (m : ℕ) (u v : Fin m → ℝ²), range (p n) = ⋃ i, segment ℝ (u i) (v i)) ∧
    (∀ n t, dist (γ t) (p n t) ≤ 1 / ((n : ℝ) + 1)) ∧
    ∀ t : Circle, ∃ U ∈ 𝓝 t, ∀ᶠ n in atTop, ∃ f : Circle → ℝ, ∀ v ∈ U, ∀ w ∈ U,
      |f v - f w| ≤ dist (p n v) (p n w) ∧ dist (p n v) (p n w) ≤ 9/8 * |f v - f w|

lemma line_perimeter (u v w D : ℝ) (huv : |u-v| ≤ D) (hvw : |v-w| ≤ D)
    (huw : |u-w| ≤ D) : |u-v| + |v-w| + |u-w| ≤ 2*D := by
  rcases le_total u v with h | h <;> rcases le_total v w with j | j <;>
    rcases le_total u w with k | k <;>
    simp only [abs_of_nonneg (sub_nonneg.mpr h),abs_of_nonpos (sub_nonpos.mpr h),
      abs_of_nonneg (sub_nonneg.mpr j),abs_of_nonpos (sub_nonpos.mpr j),
      abs_of_nonneg (sub_nonneg.mpr k),abs_of_nonpos (sub_nonpos.mpr k)] at * <;> linarith

lemma square_lengths {a b c d : ℝ²} (h : IsRectangle a b c d 1) :
    dist a b = dist b c ∧ dist a c ^ 2 = 2 * dist a b ^ 2 := by
  have hab := dist_pos.mpr h.a_ne_b
  have hbc := dist_pos.mpr h.b_ne_c
  have hs := (div_eq_iff hbc.ne').mp h.has_ratio
  rw [one_mul] at hs
  refine ⟨hs,?_⟩
  let u := a-b
  let v := c-b
  have hd : u+v = d-b := by
    calc _ = (a+c) - (b+b) := by dsimp [u,v]; abel
         _ = d-b := by rw [h.diagonal_midpoints_eq]; abel
  have he : u-v = a-c := by dsimp [u,v]; abel
  have hn : ‖u+v‖ = ‖u-v‖ := by
    rw [hd,he,←dist_eq_norm,←dist_eq_norm,dist_comm d b,h.diagonal_lengths_eq]
  have hsum := norm_add_sq_real u v
  have hsub := norm_sub_sq_real u v
  have hsame : ‖v‖ = ‖u‖ := by
    change ‖c-b‖ = ‖a-b‖
    rw [←dist_eq_norm,←dist_eq_norm,dist_comm c b,hs]
  rw [dist_eq_norm,←he]
  change ‖u-v‖^2 = 2*‖u‖^2
  rw [hn] at hsum
  rw [hsame] at hsum hsub
  linarith

lemma square_not_in_chart {p : Circle → ℝ²} {a b c d : Circle}
    (h : IsRectangle (p a) (p b) (p c) (p d) 1) {U : Set Circle} {f : Circle → ℝ}
    (hc : ∀ v ∈ U, ∀ w ∈ U,
      |f v - f w| ≤ dist (p v) (p w) ∧ dist (p v) (p w) ≤ 9/8 * |f v - f w|)
    (ha : a ∈ U) (hb : b ∈ U) (hz : c ∈ U) : False := by
  obtain ⟨eqs,eqd⟩ := square_lengths h
  have ab := dist_pos.mpr h.a_ne_b
  have ac : 0 ≤ dist (p a) (p c) := dist_nonneg
  have hlow : dist (p a) (p b) ≤ dist (p a) (p c) := by nlinarith
  have ab' := hc a ha b hb
  have bc' := hc b hb c hz
  have ac' := hc a ha c hz
  have hl := line_perimeter (f a) (f b) (f c) (dist (p a) (p c))
    (ab'.1.trans hlow) (bc'.1.trans (eqs ▸ hlow)) ac'.1
  have hi : dist (p a) (p c) ≤ 3/2 * dist (p a) (p b) := by nlinarith
  linarith [ab'.2,bc'.2,ac'.2]

theorem main : H1 → H2 → type_of% @InscribedSquare.exists_inscribed_square_of_C2 := by
  intro poly approx γ hγ
  obtain ⟨p,hp,near,chart⟩ := approx γ hγ
  choose a b c d sq using fun n => poly (p n) (hp n).1 (hp n).2
  let t (n : ℕ) : Fin 4 → Circle := ![a n,b n,c n,d n]
  obtain ⟨q,φ,hφ,ht⟩ := CompactSpace.tendsto_subseq t
  have lim (i : Fin 4) : Tendsto (fun n => p (φ n) (t (φ n) i)) atTop (𝓝 (γ (q i))) := by
    have ec : Continuous (fun w : Fin 4 → Circle => γ (w i)) := hγ.isEmbedding.continuous.comp (continuous_apply i)
    have el : Tendsto (fun n => γ (t (φ n) i)) atTop (𝓝 (γ (q i))) := ec.continuousAt.tendsto.comp ht
    apply el.congr_dist
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => near (φ n) (t (φ n) i))
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
  have ha : Tendsto (fun n => p (φ n) (a (φ n))) atTop (𝓝 (γ (q 0))) := lim 0
  have hb : Tendsto (fun n => p (φ n) (b (φ n))) atTop (𝓝 (γ (q 1))) := lim 1
  have hc : Tendsto (fun n => p (φ n) (c (φ n))) atTop (𝓝 (γ (q 2))) := lim 2
  have hd : Tendsto (fun n => p (φ n) (d (φ n))) atTop (𝓝 (γ (q 3))) := lim 3
  have mid := tendsto_nhds_unique (ha.add hc) ((hb.add hd).congr (fun n => (sq (φ n)).diagonal_midpoints_eq.symm))
  have diag := tendsto_nhds_unique (ha.dist hc) ((hb.dist hd).congr (fun n => (sq (φ n)).diagonal_lengths_eq.symm))
  have sides := tendsto_nhds_unique (ha.dist hb) ((hb.dist hc).congr (fun n => (square_lengths (sq (φ n))).1.symm))
  have ab : 0 < dist (γ (q 0)) (γ (q 1)) := by
    apply dist_pos.mpr
    intro collapse
    have eq01 : q 0 = q 1 := hγ.isEmbedding.injective collapse
    have eq21 : q 2 = q 1 := by
      apply hγ.isEmbedding.injective
      rw [collapse,dist_self] at sides
      exact (dist_eq_zero.mp sides.symm).symm
    obtain ⟨U,hU,hchart⟩ := chart (q 1)
    have coords (i : Fin 4) : Tendsto (fun n => t (φ n) i) atTop (𝓝 (q i)) :=
      (continuous_apply i).continuousAt.tendsto.comp ht
    have e0 : ∀ᶠ n : ℕ in atTop, a (φ n) ∈ U := (eq01 ▸ coords 0) hU
    have e1 : ∀ᶠ n : ℕ in atTop, b (φ n) ∈ U := coords 1 hU
    have e2 : ∀ᶠ n : ℕ in atTop, c (φ n) ∈ U := (eq21 ▸ coords 2) hU
    have impossible : ∀ᶠ _ : ℕ in atTop, False := by
      filter_upwards [e0,e1,e2,hφ.tendsto_atTop hchart] with n h0 h1 h2 hh
      obtain ⟨f,hf⟩ := hh
      exact square_not_in_chart (sq (φ n)) hf h0 h1 h2
    exact impossible.exists.elim (fun _ h => h)
  have bc : 0 < dist (γ (q 1)) (γ (q 2)) := sides ▸ ab
  exact ⟨q 0,q 1,q 2,q 3,mid,diag,dist_pos.mp ab,dist_pos.mp bc,by rw [sides,div_self bc.ne']⟩

end OMA.R_InscribedSquare_exists_inscribed_square_of_C2_R1

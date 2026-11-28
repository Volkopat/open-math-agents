import OMAReductions.R_wp_banach_s_problem_is_there_an_ergodic_system_with_simple_lebesgue_spectrum_R1
import Mathlib
-- Adapted from OpenAI, openai/math @3344da59991ed94f9ba711217b29c1d760badfa6 (Apache-2.0).
noncomputable section
open MeasureTheory Set Function Filter OMA.S_wp_banach_s_problem_is_there_an_ergodic_system_with_simple_lebesgue_spectrum
open scoped Topology ComplexConjugate
namespace OuterErg
abbrev TripleTorus := UnitAddCircle × UnitAddCircle × UnitAddCircle
abbrev slowVolume : Measure (UnitAddCircle × UnitAddCircle) :=
  AddCircle.haarAddCircle.prod AddCircle.haarAddCircle
abbrev tripleVolume : Measure TripleTorus := AddCircle.haarAddCircle.prod slowVolume
abbrev PhysicalL2 := Lp ℂ 2 tripleVolume
lemma coeff_iter (A : PhysicalL2 →ₗᵢ[ℂ] PhysicalL2) {g : PhysicalL2} (hg : A g = g)
    (f : PhysicalL2) (n : ℕ) : inner ℂ ((⇑A)^[n] f) g = inner ℂ f g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ← hg, A.inner_map_map, hg, ih]
end OuterErg
open OuterErg
theorem OMA.solution : OMA.R_wp_banach_s_problem_is_there_an_ergodic_system_with_simple_lebesgue_spectrum_R1.H3 := by
  intro T hT f ho hd
  refine { hT with aeconst_set := ?_ }
  intro s hs hTs
  classical
  let q : TripleTorus → ℂ := s.indicator (fun _ => 1)
  have hq : MemLp q 2 tripleVolume := (memLp_const (1 : ℂ)).indicator hs
  let c : ℂ := ∫ x, q x ∂tripleVolume
  let g₀ : PhysicalL2 := hq.toLp q - Lp.const 2 tripleVolume c
  have hge : g₀ =ᵐ[tripleVolume] fun x => q x - c := by
    filter_upwards [Lp.coeFn_sub (hq.toLp q) (Lp.const 2 tripleVolume c),
      hq.coeFn_toLp, Lp.coeFn_const 2 tripleVolume c] with x hx hy hz
    simpa only [g₀, Pi.sub_apply, hy, hz, Function.const_apply] using hx
  have hgc : g₀ ∈ L2zero tripleVolume := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    rw [L2.inner_def]
    calc _ = ∫ x, q x - c ∂tripleVolume := integral_congr_ae (by
           filter_upwards [(memLp_const (μ := tripleVolume) (p := 2) (1:ℂ)).coeFn_toLp, hge] with x hx hy
           simp [hy])
         _ = 0 := by rw [integral_sub (hq.integrable (by norm_num)) (integrable_const c)]; simp [c]
  have hqinvar (x : TripleTorus) : q (T x) = q x := by
    have hx : T x ∈ s ↔ x ∈ s := by
      change x ∈ T ⁻¹' s ↔ x ∈ s
      rw [hTs]
    simp only [q, indicator_apply, hx]
  have fixed (e : TripleTorus ≃ᵐ TripleTorus) (he : MeasurePreserving e tripleVolume tripleVolume)
      (hq' : ∀ x, q (e x) = q x) : Lp.compMeasurePreserving e he g₀ = g₀ := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving g₀ he, hge, he.quasiMeasurePreserving.ae hge] with x hx hy hz
    exact hx.trans ((hz.trans (by rw [hq'])).trans hy.symm)
  have heq (i : ℤ) : inner ℂ (orbit T hT f i) g₀ = inner ℂ f g₀ := by
    cases i with
    | ofNat n => exact coeff_iter (Lp.compMeasurePreservingₗᵢ ℂ T hT) (fixed T hT hqinvar) f n
    | negSucc n => exact coeff_iter (Lp.compMeasurePreservingₗᵢ ℂ T.symm (hT.symm T)) (fixed T.symm (hT.symm T) (fun x => by simpa using (hqinvar (T.symm x)).symm)) f (n+1)
  have hsumm := ho.inner_products_summable g₀
  simp only [heq] at hsumm
  have hzero : inner ℂ f g₀ = 0 := by
    by_contra h
    have : Finite ℤ := Finite.of_summable_const (pow_pos (norm_pos_iff.mpr h) 2) hsumm
    exact _root_.not_finite ℤ
  have hspan : (Submodule.span ℂ (Set.range (orbit T hT f))).topologicalClosure ≤
      (Submodule.span ℂ {g₀})ᗮ := by
    apply Submodule.topologicalClosure_minimal _ _ (Submodule.isClosed_orthogonal _)
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.mpr ((heq i).trans hzero)
  rw [hd] at hspan
  have hgzero : g₀ = 0 := inner_self_eq_zero.mp (Submodule.mem_orthogonal_singleton_iff_inner_left.mp (hspan hgc))
  have hqc : q =ᵐ[tripleVolume] fun _ => c := by
    filter_upwards [hge, Lp.coeFn_zero ℂ 2 tripleVolume] with x hx hz
    rw [hgzero, hz] at hx
    exact sub_eq_zero.mp hx.symm
  apply Filter.eventuallyConst_set.mpr
  by_cases hc : c = 0
  · right
    filter_upwards [hqc] with x hx
    intro hxs
    simp [q, hxs, hc] at hx
  · left
    filter_upwards [hqc] with x hx
    by_contra hxs
    exact hc (by simpa [q, hxs] using hx.symm)

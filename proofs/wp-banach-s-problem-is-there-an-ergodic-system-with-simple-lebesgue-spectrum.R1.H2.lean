import OMAReductions.R_wp_banach_s_problem_is_there_an_ergodic_system_with_simple_lebesgue_spectrum_R1
import Mathlib
-- Adapted from OpenAI, openai/math @3344da59991ed94f9ba711217b29c1d760badfa6 (Apache-2.0).
noncomputable section
open MeasureTheory Set Function Filter OMA.S_wp_banach_s_problem_is_there_an_ergodic_system_with_simple_lebesgue_spectrum
open scoped Topology ComplexConjugate
namespace OuterTests
abbrev TripleTorus := UnitAddCircle × UnitAddCircle × UnitAddCircle
abbrev slowVolume : Measure (UnitAddCircle × UnitAddCircle) :=
  AddCircle.haarAddCircle.prod AddCircle.haarAddCircle
abbrev tripleVolume : Measure TripleTorus := AddCircle.haarAddCircle.prod slowVolume
abbrev PhysicalL2 := Lp ℂ 2 tripleVolume
instance tripleVolume_regular : tripleVolume.Regular :=
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure tripleVolume
lemma continuous_triple_memLp {f : TripleTorus → ℂ} (hf : Continuous f) : MemLp f 2 tripleVolume :=
  hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
def physicalIntegral : PhysicalL2 →L[ℂ] ℂ := innerSL ℂ (Lp.const 2 tripleVolume (1:ℂ))
lemma physicalIntegral_apply (f : PhysicalL2) : physicalIntegral f=∫ x, f x ∂tripleVolume := by
  change inner ℂ (Lp.const 2 tripleVolume (1:ℂ)) f = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 tripleVolume (1:ℂ)] with x hx
  simp only [hx,Function.const_apply,RCLike.inner_apply,map_one,mul_one]
def physicalMeanZero : Submodule ℂ PhysicalL2 := physicalIntegral.ker
lemma mem_physicalMeanZero (f : PhysicalL2) : f ∈ physicalMeanZero ↔ ∫ x, f x ∂tripleVolume=0 := by
  change physicalIntegral f=0 ↔ _
  rw [physicalIntegral_apply]
lemma physicalMeanZero_closed : IsClosed (physicalMeanZero : Set PhysicalL2) := physicalIntegral.isClosed_ker
def physicalCenter (f : PhysicalL2) : PhysicalL2 :=
  f - physicalIntegral f • Lp.const 2 tripleVolume (1:ℂ)
lemma continuous_physicalCenter : Continuous physicalCenter :=
  continuous_id.sub (physicalIntegral.continuous.smul continuous_const)
lemma physicalCenter_ae (f : PhysicalL2) : physicalCenter f =ᵐ[tripleVolume]
    fun x => f x-physicalIntegral f := by
  filter_upwards [Lp.coeFn_sub f (physicalIntegral f • Lp.const 2 tripleVolume (1:ℂ)),
    Lp.coeFn_smul (physicalIntegral f) (Lp.const 2 tripleVolume (1:ℂ)),
    Lp.coeFn_const 2 tripleVolume (1:ℂ)] with x hx hy hz
  simpa only [physicalCenter,Pi.sub_apply,Pi.smul_apply,hy,hz,Function.const_apply,smul_eq_mul,mul_one] using hx
lemma physicalCenter_eq_self {f : PhysicalL2} (hf : f ∈ physicalMeanZero) : physicalCenter f=f := by
  change physicalIntegral f=0 at hf
  simp only [physicalCenter,hf,zero_smul,sub_zero]
def continuousCenter (g : C(TripleTorus,ℂ)) : C(TripleTorus,ℂ) :=
  g - ContinuousMap.const _ (∫ x, g x ∂tripleVolume)
lemma continuousCenter_centered (g : C(TripleTorus,ℂ)) :
    ∫ x, continuousCenter g x ∂tripleVolume=0 := by
  change (∫ x, g x-(∫ y, g y ∂tripleVolume) ∂tripleVolume)=0
  rw [integral_sub ((continuous_triple_memLp g.continuous).integrable (by norm_num)) (integrable_const _)]
  simp
lemma toLp_continuousCenter (g : C(TripleTorus,ℂ)) :
    ContinuousMap.toLp 2 tripleVolume ℂ (continuousCenter g)=
      physicalCenter (ContinuousMap.toLp 2 tripleVolume ℂ g) := by
  apply Lp.ext
  have hg := ContinuousMap.coeFn_toLp tripleVolume (𝕜 := ℂ) (p := 2) g
  have hi : physicalIntegral (ContinuousMap.toLp 2 tripleVolume ℂ g)=∫ x, g x ∂tripleVolume := by
    rw [physicalIntegral_apply,integral_congr_ae hg]
  filter_upwards [ContinuousMap.coeFn_toLp tripleVolume (𝕜 := ℂ) (p := 2) (continuousCenter g),
    physicalCenter_ae (ContinuousMap.toLp 2 tripleVolume ℂ g),hg] with x hx hy hz
  rw [hx,hy]
  change g x - (∫ y, g y ∂tripleVolume)=_
  rw [hi,hz]
structure PhysicalTest where
  fn : C(TripleTorus,ℂ)
  real : ∀ x, conj (fn x)=fn x
  centered : ∫ x, fn x ∂tripleVolume=0
  bound : ∀ x, ‖fn x‖ ≤ 1
namespace PhysicalTest
variable (h : PhysicalTest)
lemma memLp : MemLp h.fn 2 tripleVolume := continuous_triple_memLp h.fn.continuous
def vec : PhysicalL2 := h.memLp.toLp h.fn
lemma vec_ae : h.vec =ᵐ[tripleVolume] h.fn := MemLp.coeFn_toLp _
end PhysicalTest
namespace PhysicalTest
instance : TopologicalSpace PhysicalTest := TopologicalSpace.induced PhysicalTest.fn ContinuousMap.compactOpen
instance : SecondCountableTopology PhysicalTest :=
  (Topology.IsInducing.induced PhysicalTest.fn).secondCountableTopology
instance : Nonempty PhysicalTest := ⟨{
  fn := 0, real := by simp, centered := by simp, bound := by simp }⟩
lemma vec_eq_toLp (h : PhysicalTest) : h.vec=ContinuousMap.toLp 2 tripleVolume ℂ h.fn := by
  apply Lp.ext
  exact h.vec_ae.trans (ContinuousMap.coeFn_toLp tripleVolume h.fn).symm
lemma continuous_vec : Continuous (fun h : PhysicalTest => h.vec) := by
  have hh : Continuous (fun h : PhysicalTest => ContinuousMap.toLp 2 tripleVolume ℂ h.fn) :=
    (ContinuousMap.toLp 2 tripleVolume ℂ).continuous.comp
      (continuous_induced_dom : Continuous PhysicalTest.fn)
  convert hh using 1
  exact funext vec_eq_toLp
end PhysicalTest
lemma continuous_real_mem_of_tests (K : Submodule ℂ PhysicalL2)
    (hK : ∀ h : PhysicalTest, h.vec ∈ K)
    (g : C(TripleTorus,ℂ)) (hg : ∀ x, conj (g x)=g x)
    (hgc : ∫ x, g x ∂tripleVolume=0) : ContinuousMap.toLp 2 tripleVolume ℂ g ∈ K := by
  let M : ℝ := ‖g‖+1
  have hM : 0 < M := by dsimp [M]; positivity
  have hMc : (M:ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  let h : PhysicalTest := {
    fn := (M:ℂ)⁻¹ • g,
    real := by
      intro x
      simp only [ContinuousMap.smul_apply,smul_eq_mul,map_mul,map_inv₀,Complex.conj_ofReal,hg],
    centered := by
      change (∫ x, (M:ℂ)⁻¹ • g x ∂tripleVolume)=0
      rw [integral_smul,hgc,smul_zero],
    bound := by
      intro x
      simp only [ContinuousMap.smul_apply,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hM]
      have hx := g.norm_coe_le_norm x
      rw [inv_mul_eq_div]
      exact (div_le_one hM).mpr (hx.trans (by dsimp [M]; linarith)) }
  have hh : h.vec=(M:ℂ)⁻¹ • ContinuousMap.toLp 2 tripleVolume ℂ g := by
    rw [PhysicalTest.vec_eq_toLp]
    exact map_smul (ContinuousMap.toLp 2 tripleVolume ℂ) _ _
  have hm := K.smul_mem (M:ℂ) (hK h)
  rw [hh,smul_smul,mul_inv_cancel₀ hMc,one_smul] at hm
  exact hm
lemma continuous_centered_mem_of_tests (K : Submodule ℂ PhysicalL2)
    (hK : ∀ h : PhysicalTest, h.vec ∈ K)
    (g : C(TripleTorus,ℂ)) (hgc : ∫ x, g x ∂tripleVolume=0) :
    ContinuousMap.toLp 2 tripleVolume ℂ g ∈ K := by
  let r : C(TripleTorus,ℂ) := ⟨fun x => ((g x).re:ℂ),
    Complex.continuous_ofReal.comp (Complex.continuous_re.comp g.continuous)⟩
  let j : C(TripleTorus,ℂ) := ⟨fun x => ((g x).im:ℂ),
    Complex.continuous_ofReal.comp (Complex.continuous_im.comp g.continuous)⟩
  have hi : Integrable g tripleVolume := (continuous_triple_memLp g.continuous).integrable (by norm_num)
  have hr : ∫ x, r x ∂tripleVolume=0 := by
    change (∫ x, ((g x).re:ℂ) ∂tripleVolume)=0
    rw [integral_complex_ofReal]
    have hh := integral_re hi
    change (∫ x, (g x).re ∂tripleVolume)=(∫ x, g x ∂tripleVolume).re at hh
    rw [hh,hgc]
    simp
  have hj : ∫ x, j x ∂tripleVolume=0 := by
    change (∫ x, ((g x).im:ℂ) ∂tripleVolume)=0
    rw [integral_complex_ofReal]
    have hh := integral_im hi
    change (∫ x, (g x).im ∂tripleVolume)=(∫ x, g x ∂tripleVolume).im at hh
    rw [hh,hgc]
    simp
  have he : g=r+Complex.I • j := by
    ext x
    change g x=((g x).re:ℂ)+Complex.I*((g x).im:ℂ)
    simpa only [mul_comm] using (Complex.re_add_im (g x)).symm
  rw [he,map_add,map_smul]
  exact K.add_mem (continuous_real_mem_of_tests K hK r (by intro x; exact Complex.conj_ofReal _) hr)
    (K.smul_mem Complex.I (continuous_real_mem_of_tests K hK j (by intro x; exact Complex.conj_ofReal _) hj))
lemma physical_tests_total (K : Submodule ℂ PhysicalL2) (hclosed : IsClosed (K : Set PhysicalL2))
    (hK : ∀ h : PhysicalTest, h.vec ∈ K) {f : PhysicalL2} (hf : f ∈ physicalMeanZero) : f ∈ K := by
  have hd : DenseRange (ContinuousMap.toLp 2 tripleVolume ℂ : C(TripleTorus,ℂ) →L[ℂ] PhysicalL2) :=
    ContinuousMap.toLp_denseRange ℂ tripleVolume ℂ (p := 2) (by norm_num)
  have hh : physicalCenter f ∈ K := by
    apply hd.induction_on (p := fun x => physicalCenter x ∈ K) f (hclosed.preimage continuous_physicalCenter)
    intro g
    rw [← toLp_continuousCenter]
    exact continuous_centered_mem_of_tests K hK _ (continuousCenter_centered g)
  rwa [physicalCenter_eq_self hf] at hh
theorem exists_total_physical_tests : ∃ test : ℕ → PhysicalTest,
    ∀ K : Submodule ℂ PhysicalL2, IsClosed (K : Set PhysicalL2) →
      (∀ n, (test n).vec ∈ K) → ∀ f ∈ physicalMeanZero, f ∈ K := by
  obtain ⟨test,htest⟩ := TopologicalSpace.exists_dense_seq PhysicalTest
  refine ⟨test,fun K hclosed hK f hf => physical_tests_total K hclosed ?_ hf⟩
  intro h
  exact htest.induction_on h (hclosed.preimage PhysicalTest.continuous_vec) hK
end OuterTests
open OuterTests
theorem OMA.solution : OMA.R_wp_banach_s_problem_is_there_an_ergodic_system_with_simple_lebesgue_spectrum_R1.H2 := by
  obtain ⟨a, ha⟩ := exists_total_physical_tests
  refine ⟨fun i => (a i).fn, ⟨fun i => (a i).real, fun i => (a i).centered, fun i => (a i).bound⟩, ?_⟩
  intro K hK hA f hf
  apply ha K hK (fun i => (PhysicalTest.vec_eq_toLp _).symm ▸ hA i) f
  change inner ℂ (Lp.const 2 tripleVolume (1:ℂ)) f = 0
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp hf

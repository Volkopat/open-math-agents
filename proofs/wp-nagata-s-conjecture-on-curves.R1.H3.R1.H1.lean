import OMAReductions.R_wp_nagata_s_conjecture_on_curves_R1_H3_R1
import Mathlib
-- Adapted from OpenAI openai/math 3344da59991ed94f9ba711217b29c1d760badfa6.
section
namespace OAI
section
noncomputable section
open scoped BigOperators
open Polynomial
namespace Nagata.W01.RL
variable {F : Type*} [Field F]
local instance : DecidableEq F := Classical.decEq F
end Nagata.W01.RL
end
end
section
noncomputable section
open scoped BigOperators
open Polynomial
namespace Nagata.W01
abbrev Plane := ℂ × ℂ
def monomial (b l : ℕ) : Plane → ℂ := fun z => z.1 ^ b * z.2 ^ l
def pE (p : MvPolynomial (Fin 2) ℂ) : Plane → ℂ :=
  fun z => MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z.1 else z.2) p
end Nagata.W01
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W09
noncomputable def tI (U : ℝ) (n : ℤ) : Finset ℤ :=
  Finset.Ioc ⌊U⌋ (⌊U⌋ + n)
theorem mtIi {U : ℝ} {n K : ℤ}
    (hU : U ∉ Set.range (Int.cast : ℤ → ℝ)) :
    K ∈ tI U n ↔ U < (K : ℝ) ∧ (K : ℝ) < U + (n : ℝ) := by
  rw [tI, Finset.mem_Ioc]
  constructor
  · rintro ⟨hK, hKn⟩
    refine ⟨Int.floor_lt.mp hK, ?_⟩
    have hfloor : (⌊U⌋ : ℝ) < U := Int.floor_lt_self_iff.mpr hU
    have hcast : (K : ℝ) ≤ (⌊U⌋ : ℝ) + (n : ℝ) := by
      simpa only [Int.cast_add] using
        (show (K : ℝ) ≤ ((⌊U⌋ + n : ℤ) : ℝ) from Int.cast_le.mpr hKn)
    linarith
  · rintro ⟨hK, hKn⟩
    refine ⟨Int.floor_lt.mpr hK, ?_⟩
    have hle : K ≤ ⌊U + (n : ℝ)⌋ := Int.le_floor.mpr hKn.le
    simpa only [Int.floor_add_intCast] using hle
theorem ctI (U : ℝ) (n : ℤ) :
    (tI U n).card = n.toNat := by
  simp only [tI, Int.card_Ioc, add_sub_cancel_left]
end Nagata.W09
end
section
namespace Nagata.W09
theorem tIri {U : ℝ} {n a b : ℤ}
    (ha : a ∈ tI U n) (hb : b ∈ tI U n)
    (hab : a % n = b % n) : a = b := by
  simp only [tI, Finset.mem_Ioc] at ha hb
  have ha0 : 0 ≤ a - (⌊U⌋ + 1) := by omega
  have han : a - (⌊U⌋ + 1) < n := by omega
  have hb0 : 0 ≤ b - (⌊U⌋ + 1) := by omega
  have hbn : b - (⌊U⌋ + 1) < n := by omega
  have h : (a - (⌊U⌋ + 1)) % n = (b - (⌊U⌋ + 1)) % n := by
    conv_lhs => rw [Int.sub_emod]
    conv_rhs => rw [Int.sub_emod]
    rw [hab]
  rw [Int.emod_eq_of_lt ha0 han, Int.emod_eq_of_lt hb0 hbn] at h
  omega
theorem etImE (U : ℝ) {n : ℤ} (hn : 0 < n) (z : ℤ) :
    ∃ K ∈ tI U n, K % n = z % n := by
  let a := ⌊U⌋ + 1
  refine ⟨a + (z - a) % n, ?_, ?_⟩
  · simp only [tI, Finset.mem_Ioc]
    have h0 := Int.emod_nonneg (z - a) (ne_of_gt hn)
    have hlt := Int.emod_lt_of_pos (z - a) hn
    dsimp [a] at *
    omega
  · have h : (a + (z - a) % n) % n = (a + (z - a)) % n := by
      simp only [Int.add_emod, Int.emod_emod]
    have hz : a + (z - a) = z := by omega
    rw [hz] at h
    exact h
end Nagata.W09
end
end OAI
end
section
namespace OAI
section
namespace Nagata.FE
noncomputable def oII (U V : ℝ) : Finset ℤ :=
  Finset.Ioo ⌊U⌋ ⌈V⌉
def cD (d m : ℤ) : ℤ := 3 * (d - 3 * m)
def sD (d j : ℤ) : ℤ := 3 * (d - 3 * j)
noncomputable def fL (d m j : ℤ) (a Δ : ℝ) : ℝ :=
  (cD d m : ℝ) / 9 * (a - Δ) + ((m : ℝ) - (j : ℝ)) * a
noncomputable def sL (d j : ℤ) (a Δ : ℝ) : ℝ :=
  (sD d j : ℝ) / 9 * (a - Δ)
def lR (j : ℤ) (s : Finset ℤ) : Finset (ℤ × ℤ) :=
  s.image (fun K => (j, K))
noncomputable def eS (d m : ℤ) (a Δ : ℝ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc 0 m).biUnion fun j =>
    lR j (oII (fL d m j a Δ)
      (fL d m j a Δ + (cD d m : ℝ)))) ∪
  ((Finset.Ioc m (d / 3)).biUnion fun j =>
    if 0 < d - 3 * j then
      lR j (oII (sL d j a Δ)
        (sL d j a Δ + (sD d j : ℝ)))
    else ∅) ∪
  (((Finset.Ioc m (d / 3)).filter fun j => d - 3 * j = 0).image fun j => (j, 0))
noncomputable def Column (d m : ℤ) (a Δ : ℝ) :=
  {p : ℤ × ℤ // p ∈ eS d m a Δ}
noncomputable instance columnFintype (d m : ℤ) (a Δ : ℝ) :
    Fintype (Column d m a Δ) := by
  unfold Column
  infer_instance
end Nagata.FE
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Nagata.Workers.W10
section
open Nagata.FE
def CF (d m : ℤ) (a Δ : ℝ) (j : ℤ) :=
  {K : ℤ // (j, K) ∈ eS d m a Δ}
instance columnFiberDecidableEq (d m : ℤ) (a Δ : ℝ) (j : ℤ) :
    DecidableEq (CF d m a Δ j) := by
  unfold CF
  infer_instance
instance columnFiberFintype (d m : ℤ) (a Δ : ℝ) (j : ℤ) :
    Fintype (CF d m a Δ j) := by
  classical
  apply Fintype.ofInjective
    (fun K : CF d m a Δ j => (⟨(j, K.val), K.property⟩ : Column d m a Δ))
  intro K L h
  apply Subtype.ext
  exact congrArg (fun c : Column d m a Δ => c.val.2) h
end
end Nagata.Workers.W10
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology
variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
theorem ccezb
    (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F)
    (m : ℕ) (hq : ∀ n < m, q n = 0) :
    ∀ n < m, (q.comp p) n = 0 := by
  intro n hn
  ext v
  simp only [FormalMultilinearSeries.comp, sum_apply,
    FormalMultilinearSeries.compAlongComposition_apply,
    zero_apply]
  apply Finset.sum_eq_zero
  intro c hc
  rw [hq c.length (lt_of_le_of_lt c.length_le hn)]
  rfl
def HAOAL (f : E → F) (x : E) (m : ℕ) : Prop :=
  ∃ p : FormalMultilinearSeries 𝕜 E F,
    HasFPowerSeriesAt f p x ∧ ∀ n < m, p n = 0
theorem HAOAL.comp {g : F → G} {f : E → F} {x : E} {m : ℕ}
    (hg : HAOAL (𝕜 := 𝕜) g (f x) m)
    (hf : AnalyticAt 𝕜 f x) :
    HAOAL (𝕜 := 𝕜) (g ∘ f) x m := by
  obtain ⟨q, hq, hzero⟩ := hg
  obtain ⟨p, hp⟩ := hf
  exact ⟨q.comp p, hq.comp hp, ccezb q p m hzero⟩
theorem HAOAL.congr {f g : E → F} {x : E} {m : ℕ}
    (hf : HAOAL (𝕜 := 𝕜) f x m)
    (hfg : f =ᶠ[𝓝 x] g) : HAOAL (𝕜 := 𝕜) g x m := by
  obtain ⟨p, hp, hzero⟩ := hf
  exact ⟨p, hp.congr hfg, hzero⟩
theorem aoclc
    (e : OpenPartialHomeomorph E F) (x : E) (hx : x ∈ e.source)
    (he : AnalyticAt 𝕜 e x) (hei : AnalyticAt 𝕜 e.symm (e x))
    (f : F → G) (m : ℕ) :
    HAOAL (𝕜 := 𝕜) (f ∘ e) x m ↔
      HAOAL (𝕜 := 𝕜) f (e x) m := by
  constructor
  · intro h
    have hcenter : HAOAL (𝕜 := 𝕜) (f ∘ e) (e.symm (e x)) m := by
      simpa only [e.left_inv hx] using h
    have hc := hcenter.comp hei
    apply hc.congr
    exact (e.eventually_right_inverse' hx).mono fun y hy => by
      change f (e (e.symm y)) = f y
      rw [hy]
  · intro h
    exact h.comp he
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology
theorem neavl
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (G : E → ℂ) (L : E →L[ℂ] ℂ) (p V : E)
    (hG : HasFDerivAt G L p) (hp : G p = 0) :
    Filter.Tendsto (fun s : ℂ => s⁻¹ * G (p + s • V)) (𝓝[≠] 0) (𝓝 (L V)) := by
  have hm : HasDerivAt (fun s : ℂ => p + s • V) V 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const V).const_add p
  have hd : HasDerivAt (fun s : ℂ => G (p + s • V)) (L V) 0 := by
    have hh : HasFDerivAt G L (p + (0 : ℂ) • V) := by simpa using hG
    exact hh.comp_hasDerivAt 0 hm
  simpa only [zero_add, zero_smul, add_zero, hp, sub_zero, smul_eq_mul] using
    hd.tendsto_slope_zero
end Nagata.Workers.W28
end
end
section
namespace Nagata.VUO
open scoped Topology
open Nagata.Workers.W28
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
theorem bszs (b : ℂ →L[ℂ] ℂ →L[ℂ] ℂ) (a : ℂ)
    (n : ℕ) (v : Fin n → ℂ × ℂ) (hv : ∀ i, (v i).2 = 0) :
    b.fpowerSeriesBilinear (a, 0) n v = 0 := by
  rcases n with _ | _ | _ | n
  · simp [ContinuousLinearMap.fpowerSeriesBilinear]
  · simp [ContinuousLinearMap.fpowerSeriesBilinear, ContinuousLinearMap.coe_deriv₂, hv]
  · simp [ContinuousLinearMap.fpowerSeriesBilinear, hv]
  · rfl
theorem pscz (b : ℂ →L[ℂ] ℂ →L[ℂ] ℂ) (a : ℂ)
    (p q : FormalMultilinearSeries ℂ E ℂ) (m : ℕ)
    (hq : ∀ n < m, q n = 0) :
    ∀ n < m, ((b.fpowerSeriesBilinear (a, 0)).comp (p.prod q)) n = 0 := by
  intro n hn
  ext v
  simp only [FormalMultilinearSeries.comp, sum_apply,
    FormalMultilinearSeries.compAlongComposition_apply, zero_apply]
  apply Finset.sum_eq_zero
  intro c hc
  apply bszs
  intro i
  change q (c.blocksFun i) (v ∘ c.embedding i) = 0
  rw [hq _ (lt_of_le_of_lt (c.blocksFun_le i) hn)]
  rfl
theorem aoml {u f : E → ℂ} {x : E} {m : ℕ}
    (hu : AnalyticAt ℂ u x)
    (hf : HAOAL (𝕜 := ℂ) f x m) :
    HAOAL (𝕜 := ℂ) (fun y => u y * f y) x m := by
  obtain ⟨p, hp⟩ := hu
  obtain ⟨q, hq, hqzero⟩ := hf
  by_cases hm : m = 0
  · subst m
    obtain ⟨r, hr⟩ := hp.analyticAt.mul hq.analyticAt
    exact ⟨r, hr, by intro n hn; omega⟩
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hfx : f x = 0 := by
      rw [← hq.coeff_zero (fun i => Fin.elim0 i), hqzero 0 hmpos]
      rfl
    let b : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := ContinuousLinearMap.mul ℂ ℂ
    have hb := b.hasFPowerSeriesAt_bilinear (u x, f x)
    have hc := hb.comp (f := fun y : E => (u y, f y)) (hp.prod hq)
    rw [hfx] at hc
    exact ⟨(b.fpowerSeriesBilinear (u x, 0)).comp (p.prod q), hc,
      pscz b (u x) p q m hqzero⟩
theorem aoumi {u f : E → ℂ} {x : E} (m : ℕ)
    (hu : AnalyticAt ℂ u x) (hu0 : u x ≠ 0) :
    HAOAL (𝕜 := ℂ) (fun y => u y * f y) x m ↔
      HAOAL (𝕜 := ℂ) f x m := by
  constructor
  · intro h
    have hi := aoml (hu.inv hu0) h
    apply hi.congr
    filter_upwards [hu.continuousAt.eventually_ne hu0] with y hy
    simp [hy]
  · exact aoml hu
end Nagata.VUO
end
section
noncomputable section
namespace Nagata.Workers.W28
def aNS (s : ℂ) (x : ℂ × ℂ) : ℂ × ℂ := (x.1, s * x.2)
theorem aNSaA (s : ℂ) (x : ℂ × ℂ) :
    AnalyticAt ℂ (aNS s) x := by
  have hh := ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt x).const_smul (c := s)
  exact ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt x).prod (by
    simpa only [Pi.smul_def, smul_eq_mul, ContinuousLinearMap.coe_snd'] using hh)
end Nagata.Workers.W28
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.AM
variable {σ K : Type*} [CommRing K]
noncomputable def pointIdeal (p : σ → K) : Ideal (MvPolynomial σ K) :=
  RingHom.ker (MvPolynomial.eval p)
def oAL (p : σ → K) (m : ℕ) (f : MvPolynomial σ K) : Prop :=
  f ∈ pointIdeal p ^ m
theorem pImi (p : σ → K) (f : MvPolynomial σ K) :
    f ∈ pointIdeal p ↔ MvPolynomial.eval p f = 0 := by
  exact RingHom.mem_ker
theorem cdm (p : σ → K) (i : σ) :
    MvPolynomial.X i - MvPolynomial.C (p i) ∈ pointIdeal p := by
  rw [pImi]
  simp
@[simp] theorem oALz (p : σ → K) (f : MvPolynomial σ K) :
    oAL p 0 f := by
  simp [oAL]
theorem oALm {p : σ → K} {m n : ℕ} {f g : MvPolynomial σ K}
    (hf : oAL p m f) (hg : oAL p n g) :
    oAL p (m + n) (f * g) := by
  change f * g ∈ pointIdeal p ^ (m + n)
  rw [pow_add]
  exact Ideal.mul_mem_mul hf hg
theorem oALp {p : σ → K} {m : ℕ} {f : MvPolynomial σ K}
    (hf : oAL p m f) (N : ℕ) : oAL p (m * N) (f ^ N) := by
  change f ^ N ∈ pointIdeal p ^ (m * N)
  rw [pow_mul]
  exact Ideal.pow_mem_pow hf N
theorem pImoe {τ : Type*}
    (p : σ → K) (q : τ → K)
    (e : MvPolynomial σ K ≃+* MvPolynomial τ K)
    (h : ∀ f, MvPolynomial.eval q (e f) = MvPolynomial.eval p f) :
    Ideal.map e (pointIdeal p) = pointIdeal q := by
  ext g
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨f, hf, rfl⟩
    rw [pImi, h]
    exact (pImi p f).mp hf
  · intro hg
    refine ⟨e.symm g, ?_, e.apply_symm_apply g⟩
    rw [pImi, ← h, e.apply_symm_apply]
    exact (pImi q g).mp hg
theorem oALei {τ : Type*}
    (p : σ → K) (q : τ → K)
    (e : MvPolynomial σ K ≃+* MvPolynomial τ K)
    (h : ∀ f, MvPolynomial.eval q (e f) = MvPolynomial.eval p f)
    (m : ℕ) (f : MvPolynomial σ K) :
    oAL q m (e f) ↔ oAL p m f := by
  unfold oAL
  rw [← pImoe p q e h, ← Ideal.map_pow]
  exact Ideal.apply_mem_of_equiv_iff
section Field
variable {F : Type*} [Field F]
theorem pIiM (p : σ → F) : (pointIdeal p).IsMaximal := by
  apply RingHom.ker_isMaximal_of_surjective (MvPolynomial.eval p)
  intro a
  exact ⟨MvPolynomial.C a, MvPolynomial.eval_C a⟩
end Field
end Nagata.AM
end
section
namespace Nagata.AM
section MaximalIdeal
variable {R : Type*} [CommRing R] (I : Ideal R) (hI : I.IsMaximal)
include hI
theorem mIpr {m : ℕ} (hm : m ≠ 0) :
    (I ^ m).radical = I := by
  rw [Ideal.radical_pow I hm, hI.isPrime.radical]
theorem mIpiP {m : ℕ} (hm : m ≠ 0) :
    (I ^ m).IsPrimary := by
  apply Ideal.isPrimary_of_isMaximal_radical
  rwa [mIpr I hI hm]
theorem mIpcm
    [I.IsPrime] (S : Type*) [CommRing S] [Algebra R S]
    [IsLocalization.AtPrime S I] (m : ℕ) :
    Ideal.comap (algebraMap R S) (Ideal.map (algebraMap R S) (I ^ m)) = I ^ m := by
  by_cases hm : m = 0
  · simp [hm, Ideal.map_top]
  apply IsLocalization.under_map_of_isPrimary_disjoint I.primeCompl S
    (mIpiP I hI hm)
  apply Set.disjoint_left.mpr
  intro x hx hxm
  exact hx (Ideal.pow_le_self hm hxm)
theorem mIpli
    [I.IsPrime] (S : Type*) [CommRing S] [Algebra R S]
    [IsLocalization.AtPrime S I] [IsLocalRing S] (m : ℕ) (f : R) :
    algebraMap R S f ∈ IsLocalRing.maximalIdeal S ^ m ↔ f ∈ I ^ m := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal I S, ← Ideal.map_pow]
  change f ∈ Ideal.comap (algebraMap R S) (Ideal.map (algebraMap R S) (I ^ m)) ↔ _
  rw [mIpcm I hI S m]
end MaximalIdeal
section AffinePoint
variable {σ F : Type*} [Field F]
instance pointIdeal_isPrime (p : σ → F) : (pointIdeal p).IsPrime :=
  (pIiM p).isPrime
abbrev PLR (p : σ → F) := Localization.AtPrime (pointIdeal p)
noncomputable def rE (p : σ → F) : PLR p →+* F :=
  IsLocalization.lift (M := (pointIdeal p).primeCompl)
    (S := PLR p) (g := MvPolynomial.eval p) (fun s => by
      apply isUnit_iff_ne_zero.mpr
      intro hs
      exact s.property ((pImi p s).mpr hs))
@[simp] theorem rEaM (p : σ → F) (f : MvPolynomial σ F) :
    rE p (algebraMap (MvPolynomial σ F) (PLR p) f) =
      MvPolynomial.eval p f := by
  exact IsLocalization.lift_eq _ f
theorem rEs (p : σ → F) : Function.Surjective (rE p) := by
  intro a
  refine ⟨algebraMap (MvPolynomial σ F) (PLR p) (MvPolynomial.C a), ?_⟩
  simp
theorem krE (p : σ → F) :
    RingHom.ker (rE p) = IsLocalRing.maximalIdeal (PLR p) :=
  IsLocalRing.ker_eq_maximalIdeal (rE p) (rEs p)
theorem rEiU (p : σ → F) (x : PLR p) :
    IsUnit x ↔ rE p x ≠ 0 := by
  have h : rE p x = 0 ↔ ¬ IsUnit x := by
    rw [← RingHom.mem_ker, krE, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff]
  simpa only [not_not] using (not_congr h).symm
def lOAL (p : σ → F) (m : ℕ) (f : MvPolynomial σ F) : Prop :=
  algebraMap (MvPolynomial σ F) (PLR p) f ∈
    IsLocalRing.maximalIdeal (PLR p) ^ m
theorem lOALi (p : σ → F) (m : ℕ) (f : MvPolynomial σ F) :
    lOAL p m f ↔ oAL p m f :=
  mIpli (pointIdeal p) (pIiM p)
    (PLR p) m f
end AffinePoint
end Nagata.AM
end
end OAI
end
section
namespace OAI
section
namespace Nagata.Workers.W30
open MvPolynomial
open scoped Pointwise
variable {σ R : Type*} [CommRing R]
theorem mmsi {p : MvPolynomial σ R} {s : Set (σ →₀ ℕ)} :
    p ∈ Ideal.span ((fun a => monomial a (1 : R)) '' s) ↔
      ∀ a ∈ p.support, ∃ g ∈ s, g ≤ a := by
  classical
  let J : Ideal (MvPolynomial σ R) :=
    { carrier := {f | ∀ a ∈ f.support, ∃ g ∈ s, g ≤ a}
      add_mem' {x y} hx hy a ha :=
        (Finset.mem_union.mp (Finsupp.support_add ha)).elim (hx a) (hy a)
      zero_mem' := by simp
      smul_mem' x y hy a ha := by
        change a ∈ (x*y).support at ha
        obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp (support_mul x y ha)
        obtain ⟨g,hg,hgv⟩ := hy v hv
        exact ⟨g,hg,hgv.trans (le_add_of_nonneg_left zero_le)⟩ }
  change _ ↔ p ∈ J
  constructor
  · suffices Ideal.span ((fun a => monomial a (1 : R)) '' s) ≤ J from @this p
    rw [Ideal.span_le]
    rintro _ ⟨g,hg,rfl⟩ a ha
    have heq : a = g := Finset.mem_singleton.mp (support_monomial_subset ha)
    exact ⟨g,hg,heq ▸ le_rfl⟩
  · intro hp
    rw [p.as_sum]
    apply Submodule.sum_mem _
    intro a ha
    obtain ⟨g,hg,hga⟩ := hp a ha
    obtain ⟨c,hc⟩ := le_iff_exists_add.mp hga
    have hgen : monomial g (1:R) ∈ Ideal.span ((fun a => monomial a (1:R)) '' s) :=
      Ideal.subset_span ⟨g,hg,rfl⟩
    have hprod := Ideal.mul_mem_left _ (monomial c (p.coeff a)) hgen
    simpa [monomial_mul, hc, add_comm] using hprod
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
def GD (q m ell b : Nat) : Prop :=
  ∃ k : Nat, k ≤ m ∧ q * (m - k) ≤ ell ∧ k ≤ b
theorem gDi {q m ell b : Nat} :
    GD q m ell b ↔ m ≤ b ∨ q * (m - b) ≤ ell := by
  constructor
  · rintro ⟨k, hkm, hell, hkb⟩
    right
    have hsub : m - b ≤ m - k := by omega
    exact Nat.le_trans (Nat.mul_le_mul_left q hsub) hell
  · rintro (hmb | hell)
    · exact ⟨m, Nat.le_refl m, by simp, hmb⟩
    · by_cases hbm : b ≤ m
      · exact ⟨b, hbm, hell, Nat.le_refl b⟩
      · exact ⟨m, Nat.le_refl m, by simp, by omega⟩
theorem ngDi {q m ell b : Nat} :
    ¬ GD q m ell b ↔ b < m ∧ ell < q * (m - b) := by
  rw [gDi]
  omega
theorem GD.add {q m ell b c d : Nat}
    (h : GD q m ell b) : GD q m (ell + c) (b + d) := by
  rcases h with ⟨k, hkm, hell, hkb⟩
  exact ⟨k, hkm, by omega, by omega⟩
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
open scoped Pointwise
variable {A : Type*} [CommRing A]
theorem psp (x y : A) (m : ℕ) :
    ({x,y} : Set A) ^ m = {z | ∃ k ≤ m, z = x ^ (m - k) * y ^ k} := by
  induction m with
  | zero =>
    ext z
    simp
  | succ m ih =>
    rw [pow_succ, ih]
    ext z
    simp only [Set.mem_mul, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨a, ⟨k, hk, rfl⟩, c, hc, rfl⟩
      rcases hc with rfl | rfl
      · refine ⟨k, by omega, ?_⟩
        have hsub : m + 1 - k = (m - k) + 1 := by omega
        rw [hsub, pow_succ]
        ac_rfl
      · refine ⟨k + 1, by omega, ?_⟩
        rw [Nat.add_sub_add_right, pow_succ]
        ac_rfl
    · rintro ⟨k, hk, rfl⟩
      cases k with
      | zero =>
        refine ⟨x ^ m * y ^ 0, ⟨0, Nat.zero_le m, by simp⟩, x, Or.inl rfl, ?_⟩
        simp [pow_succ]
      | succ k =>
        refine ⟨x ^ (m - k) * y ^ k, ⟨k, by omega, rfl⟩, y, Or.inr rfl, ?_⟩
        rw [Nat.add_sub_add_right, pow_succ]
        ac_rfl
theorem pip (x y : A) (m : ℕ) :
    (Ideal.span {x,y}) ^ m =
      Ideal.span {z | ∃ k ≤ m, z = x ^ (m - k) * y ^ k} := by
  rw [Ideal.span, Submodule.span_pow, psp]
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
noncomputable def eP (ell b : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 ell + Finsupp.single 1 b
@[simp] theorem ePz (ell b : ℕ) : eP ell b 0 = ell := by
  simp [eP]
@[simp] theorem ePo (ell b : ℕ) : eP ell b 1 = b := by
  simp [eP]
lemma ePe (a : Fin 2 →₀ ℕ) : eP (a 0) (a 1) = a := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simp
lemma ePli {ell b : ℕ} {a : Fin 2 →₀ ℕ} :
    eP ell b ≤ a ↔ ell ≤ a 0 ∧ b ≤ a 1 := by
  constructor
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1⟩
  · rintro ⟨h0,h1⟩ i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using h0
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simpa using h1
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
open MvPolynomial
variable {R : Type*} [CommRing R]
abbrev Biv (R : Type*) [CommRing R] := MvPolynomial (Fin 2) R
noncomputable def cI (R : Type*) [CommRing R] (q m : ℕ) : Ideal (Biv R) :=
  (Ideal.span {X (0 : Fin 2) ^ q, X (1 : Fin 2)}) ^ m
lemma meP (ell b : ℕ) :
    (monomial (eP ell b) 1 : Biv R) = X 0 ^ ell * X 1 ^ b := by
  rw [eP, monomial_add_single, ← X_pow_eq_monomial]
def cG (q m : ℕ) : Set (Fin 2 →₀ ℕ) :=
  {a | ∃ k ≤ m, a = eP (q * (m - k)) k}
theorem cIems (q m : ℕ) :
    cI R q m =
      Ideal.span ((fun a => monomial a (1 : R)) '' cG q m) := by
  rw [cI, pip]
  congr 1
  ext p
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨eP (q * (m-k)) k, ⟨k,hk,rfl⟩, ?_⟩
    simp only [meP, pow_mul]
  · rintro ⟨a, ⟨k,hk,rfl⟩, rfl⟩
    exact ⟨k,hk, by simp only [meP, pow_mul]⟩
lemma ecGli (q m : ℕ) (a : Fin 2 →₀ ℕ) :
    (∃ g ∈ cG q m, g ≤ a) ↔ GD q m (a 0) (a 1) := by
  constructor
  · rintro ⟨g, ⟨k,hk,rfl⟩, hle⟩
    exact ⟨k,hk,(ePli.mp hle).1,(ePli.mp hle).2⟩
  · rintro ⟨k,hk,h0,h1⟩
    exact ⟨eP (q*(m-k)) k, ⟨k,hk,rfl⟩, ePli.mpr ⟨h0,h1⟩⟩
theorem mcIis (q m : ℕ) (p : Biv R) :
    p ∈ cI R q m ↔
      ∀ a ∈ p.support, GD q m (a 0) (a 1) := by
  rw [cIems, mmsi]
  simp only [ecGli]
theorem mcIic (q m : ℕ) (p : Biv R) :
    p ∈ cI R q m ↔
      ∀ b < m, ∀ ell < q * (m-b), p.coeff (eP ell b) = 0 := by
  rw [mcIis]
  constructor
  · intro h b hb ell hell
    by_contra hne
    have hm := h (eP ell b) (mem_support_iff.mpr hne)
    exact (ngDi.mpr ⟨hb,hell⟩) (by simpa using hm)
  · intro h a ha
    by_contra hn
    obtain ⟨hb,hell⟩ := ngDi.mp hn
    have heq := h (a 1) hb (a 0) hell
    rw [ePe] at heq
    exact (mem_support_iff.mp ha) heq
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
open MvPolynomial
variable {R : Type*} [CommRing R]
lemma rXft :
    Set.range (X : Fin 2 → Biv R) = {X 0, X 1} := by
  ext p
  constructor
  · rintro ⟨i,rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Or.inl rfl
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
theorem moIpi (m : ℕ) (p : Biv R) :
    p ∈ (Ideal.span (Set.range (X : Fin 2 → Biv R))) ^ m ↔
      ∀ ell b : ℕ, ell + b < m → p.coeff (eP ell b) = 0 := by
  have hbase := mcIic (R := R) 1 m p
  simp only [cI, pow_one, Nat.one_mul, rXft] at hbase ⊢
  rw [hbase]
  constructor
  · intro h ell b hlt
    exact h b (by omega) ell (by omega)
  · intro h b hb ell hell
    exact h ell b (by omega)
end Nagata.Workers.W30
end
end OAI
end
section
namespace OAI
section
namespace Nagata.AM
variable {σ R : Type*} [CommRing R]
noncomputable def tH (p : σ → R) : MvPolynomial σ R →+* MvPolynomial σ R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => MvPolynomial.X i + MvPolynomial.C (p i))
@[simp] theorem tHC (p : σ → R) (a : R) :
    tH p (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [tH]
@[simp] theorem tHX (p : σ → R) (i : σ) :
    tH p (MvPolynomial.X i) = MvPolynomial.X i + MvPolynomial.C (p i) := by
  simp [tH]
theorem tHnc (p : σ → R) :
    (tH (-p)).comp (tH p) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro a; simp
  · intro i; simp [add_assoc]
theorem tHcn (p : σ → R) :
    (tH p).comp (tH (-p)) = RingHom.id _ := by
  simpa only [neg_neg] using tHnc (-p)
noncomputable def tE1 (p : σ → R) : MvPolynomial σ R ≃+* MvPolynomial σ R :=
  { tH p with
    invFun := tH (-p)
    left_inv := fun f => RingHom.congr_fun (tHnc p) f
    right_inv := fun f => RingHom.congr_fun (tHcn p) f }
theorem ezt (p : σ → R) (f : MvPolynomial σ R) :
    MvPolynomial.eval (0 : σ → R) (tH p f) = MvPolynomial.eval p f := by
  have h : (MvPolynomial.eval (0 : σ → R)).comp (tH p) =
      MvPolynomial.eval p := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro i; simp
  exact RingHom.congr_fun h f
end Nagata.AM
end
section
namespace Nagata.AM
variable {σ R : Type*} [CommRing R]
theorem et1 (p x : σ → R) (f : MvPolynomial σ R) :
    MvPolynomial.eval x (tH p f) = MvPolynomial.eval (x + p) f := by
  have h : (MvPolynomial.eval x).comp (tH p) =
      MvPolynomial.eval (x + p) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro i; simp
  exact RingHom.congr_fun h f
end Nagata.AM
end
section
namespace Nagata.AM
variable {R : Type*} [CommRing R]
theorem pIfTz :
    pointIdeal (0 : Fin 2 → R) =
      Ideal.span (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) R)) := by
  ext f
  rw [pImi, MvPolynomial.eval_zero]
  change f.coeff 0 = 0 ↔ _
  have h := Nagata.Workers.W30.moIpi 1 f
  simp only [pow_one] at h
  rw [h]
  constructor
  · intro hf ell b hlt
    have he : ell = 0 := by omega
    have hb : b = 0 := by omega
    subst ell
    subst b
    simpa [Nagata.Workers.W30.eP] using hf
  · intro hf
    simpa [Nagata.Workers.W30.eP] using hf 0 0 (by decide)
theorem oALfT
    (p : Fin 2 → R) (m : ℕ) (f : MvPolynomial (Fin 2) R) :
    oAL p m f ↔ ∀ ell b : ℕ, ell + b < m →
      (tH p f).coeff (Nagata.Workers.W30.eP ell b) = 0 := by
  have h := oALei p (0 : Fin 2 → R) (tE1 p)
    (fun g => ezt p g) m f
  rw [← h]
  unfold oAL
  rw [pIfTz]
  exact Nagata.Workers.W30.moIpi m (tH p f)
end Nagata.AM
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W28
open scoped BigOperators
private theorem aoz (m : ℕ) :
    HAOAL (𝕜 := ℂ) (fun _ : ℂ × ℂ => (0 : ℂ)) 0 m := by
  refine ⟨constFormalMultilinearSeries ℂ (ℂ × ℂ) 0, hasFPowerSeriesAt_const, ?_⟩
  intro n hn
  cases n <;> ext v <;> rfl
private theorem aoa {f g : ℂ × ℂ → ℂ} {m : ℕ}
    (hf : HAOAL (𝕜 := ℂ) f 0 m)
    (hg : HAOAL (𝕜 := ℂ) g 0 m) :
    HAOAL (𝕜 := ℂ) (f + g) 0 m := by
  obtain ⟨p, hp, hz⟩ := hf
  obtain ⟨q, hq, hqz⟩ := hg
  refine ⟨p + q, hp.add hq, ?_⟩
  intro n hn
  simp [hz n hn, hqz n hn]
theorem aocs {f : ℂ × ℂ → ℂ} {m : ℕ}
    (hf : HAOAL (𝕜 := ℂ) f 0 m) (c : ℂ) :
    HAOAL (𝕜 := ℂ) (c • f) 0 m := by
  obtain ⟨p, hp, hz⟩ := hf
  refine ⟨c • p, hp.const_smul, ?_⟩
  intro n hn
  simp [hz n hn]
theorem mhAOA (a b m : ℕ) (hm : m ≤ a + b) :
    HAOAL (𝕜 := ℂ)
      (fun x : ℂ × ℂ => x.1 ^ a * x.2 ^ b) 0 m := by
  let q := ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin (a + b)) ℂ
  let u : (ℂ × ℂ) →L[ℂ] (Fin (a + b) → ℂ) :=
    ContinuousLinearMap.pi (fun i =>
      if i.val < a then ContinuousLinearMap.fst ℂ ℂ ℂ else ContinuousLinearMap.snd ℂ ℂ ℂ)
  have hq : HasFPowerSeriesAt q q.toFormalMultilinearSeries (u 0) := by
    simpa only [map_zero] using q.hasFiniteFPowerSeriesOnBall.toHasFPowerSeriesOnBall.hasFPowerSeriesAt
  have hfun : (q ∘ u) = (fun x : ℂ × ℂ => x.1 ^ a * x.2 ^ b) := by
    funext x
    simp only [q, u, Function.comp_apply, ContinuousMultilinearMap.mkPiAlgebra_apply,
      ContinuousLinearMap.pi_apply]
    rw [Fin.prod_univ_add]
    simp
  refine ⟨q.toFormalMultilinearSeries.compContinuousLinearMap u, ?_, ?_⟩
  · rw [← hfun]
    exact hq.compContinuousLinearMap
  · intro n hn
    have hne : a + b ≠ n := by omega
    ext v
    simp [FormalMultilinearSeries.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.toFormalMultilinearSeries, hne]
theorem aofs {ι : Type*} (s : Finset ι)
    (f : ι → ℂ × ℂ → ℂ) (m : ℕ)
    (hf : ∀ i ∈ s, HAOAL (𝕜 := ℂ) (f i) 0 m) :
    HAOAL (𝕜 := ℂ) (fun x => ∑ i ∈ s, f i x) 0 m := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using aoz m
  | @insert i s hi ih =>
      have hsum := aoa (hf i (Finset.mem_insert_self i s))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
      simpa only [Finset.sum_insert hi, Pi.add_def] using hsum
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped BigOperators
theorem ehAOA
    (P : MvPolynomial (Fin 2) ℂ) (m : ℕ)
    (hcoeff : ∀ ell b, ell + b < m → P.coeff (Nagata.Workers.W30.eP ell b) = 0) :
    HAOAL (𝕜 := ℂ)
      (fun x : ℂ × ℂ => MvPolynomial.eval (fun i => if i = 0 then x.1 else x.2) P) 0 m := by
  have hterm (d : Fin 2 →₀ ℕ) (hd : d ∈ P.support) :
      HAOAL (𝕜 := ℂ)
        (fun x : ℂ × ℂ => P.coeff d * (x.1 ^ d 0 * x.2 ^ d 1)) 0 m := by
    have hdegree : m ≤ d 0 + d 1 := by
      have hnonzero : P.coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
      have hnot : ¬d 0 + d 1 < m := by
        intro h
        apply hnonzero
        simpa only [Nagata.Workers.W30.ePe] using hcoeff (d 0) (d 1) h
      omega
    simpa only [Pi.smul_def, smul_eq_mul] using
      aocs (mhAOA (d 0) (d 1) m hdegree) (P.coeff d)
  have hsum := aofs P.support
    (fun d (x : ℂ × ℂ) => P.coeff d * (x.1 ^ d 0 * x.2 ^ d 1)) m hterm
  convert hsum using 1
  funext x
  rw [MvPolynomial.eval_eq']
  simp [Fin.prod_univ_two]
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
theorem poiao
    (P : MvPolynomial (Fin 2) ℂ) (p : ℂ × ℂ) (m : ℕ)
    (hP : Nagata.AM.oAL
      (fun i : Fin 2 => if i = 0 then p.1 else p.2) m P) :
    HAOAL (𝕜 := ℂ)
      (fun x : ℂ × ℂ => MvPolynomial.eval (fun i => if i = 0 then x.1 else x.2) P) p m := by
  let pv : Fin 2 → ℂ := fun i => if i = 0 then p.1 else p.2
  have hc := (Nagata.AM.oALfT pv m P).mp hP
  obtain ⟨q, hq, hz⟩ := ehAOA
    (Nagata.AM.tH pv P) m hc
  refine ⟨q, ?_, hz⟩
  have hs := hq.comp_sub p
  simp only [zero_add] at hs
  apply hs.congr
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [Nagata.AM.et1]
    apply congrArg (fun v : Fin 2 → ℂ => MvPolynomial.eval v P)
    funext i
    by_cases hi : i = 0 <;> simp [pv, hi]
end Nagata.Workers.W28
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W08
open Filter Topology
noncomputable def aS (τ : ℂ) (n : ℤ) (γ : ℂ) :
    Submodule ℂ (ℂ → ℂ) where
  carrier := {f | f 0 = 0 ∧ (∀ z, z ≠ 0 → DifferentiableAt ℂ f z) ∧
    (∀ z, z ≠ 0 → f (τ * z) = γ * z ^ (-n) * f z)}
  zero_mem' := by
    refine ⟨rfl, ?_, ?_⟩
    · intro z _
      exact differentiableAt_const 0
    · intro z _
      simp
  add_mem' := by
    intro f g hf hg
    refine ⟨?_, ?_, ?_⟩
    · change f 0 + g 0 = 0
      rw [hf.1, hg.1, add_zero]
    · intro z hz
      exact (hf.2.1 z hz).add (hg.2.1 z hz)
    · intro z hz
      change f (τ * z) + g (τ * z) = γ * z ^ (-n) * (f z + g z)
      rw [hf.2.2 z hz, hg.2.2 z hz, mul_add]
  smul_mem' := by
    intro a f hf
    refine ⟨?_, ?_, ?_⟩
    · change a * f 0 = 0
      rw [hf.1, mul_zero]
    · intro z hz
      exact (hf.2.1 z hz).const_smul a
    · intro z hz
      change a * f (τ * z) = γ * z ^ (-n) * (a * f z)
      rw [hf.2.2 z hz]
      ac_rfl
theorem aSe {τ γ : ℂ} {n : ℤ}
    (f g : aS τ n γ)
    (h : ∀ z, z ≠ 0 → f.val z = g.val z) : f = g := by
  apply Subtype.ext
  funext z
  by_cases hz : z = 0
  · subst z
    exact f.property.1.trans g.property.1.symm
  · exact h z hz
noncomputable def nAZ (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z = 0 then 0 else f z
@[simp] theorem nAZz (f : ℂ → ℂ) : nAZ f 0 = 0 := by
  simp [nAZ]
@[simp] theorem nAZon (f : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0) :
    nAZ f z = f z := by
  simp [nAZ, hz]
theorem nAZeE (f : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0) :
    nAZ f =ᶠ[𝓝 z] f :=
  (eventually_ne_nhds hz).mono fun point hpoint ↦ nAZon f (z := point) hpoint
theorem nAZdA (f : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℂ (nAZ f) z ↔ DifferentiableAt ℂ f z :=
  (nAZeE f hz).differentiableAt_iff
theorem nAZma {τ γ : ℂ} {n : ℤ}
    (hτ : τ ≠ 0) (f : ℂ → ℂ)
    (hf : ∀ z, z ≠ 0 → DifferentiableAt ℂ f z)
    (he : ∀ z, z ≠ 0 → f (τ * z) = γ * z ^ (-n) * f z) :
    nAZ f ∈ aS τ n γ := by
  refine ⟨nAZz f, ?_, ?_⟩
  · intro z hz
    exact (nAZdA f hz).mpr (hf z hz)
  · intro z hz
    rw [nAZon f (mul_ne_zero hτ hz), nAZon f hz]
    exact he z hz
noncomputable def sOF {τ γ : ℂ} {n : ℤ}
    (hτ : τ ≠ 0) (f : ℂ → ℂ)
    (hf : ∀ z, z ≠ 0 → DifferentiableAt ℂ f z)
    (he : ∀ z, z ≠ 0 → f (τ * z) = γ * z ^ (-n) * f z) :
    aS τ n γ :=
  ⟨nAZ f, nAZma hτ f hf he⟩
end Nagata.W08
end
section
universe u
namespace Nagata.W08
def tri (p : Int) : Int := p * (p - 1) / 2
@[simp] theorem tz : tri 0 = 0 := by decide
theorem tao (p : Int) : tri (p + 1) = tri p + p := by
  unfold tri
  have h : (p + 1) * (p + 1 - 1) = p * (p - 1) + 2 * p := by
    simp only [Int.add_sub_cancel, Int.add_mul, Int.one_mul, Int.mul_sub, Int.mul_one]
    omega
  rw [h]
  omega
def lE (n K p : Int) : Int := p * K + n * tri p
@[simp] theorem lEz (n K : Int) : lE n K 0 = 0 := by
  simp [lE]
theorem lEao (n K p : Int) :
    lE n K (p + 1) = lE n K p + (K + n * p) := by
  simp only [lE, tao, Int.add_mul, Int.one_mul, Int.mul_add]
  omega
theorem bIu {α : Type u} (step : Int → α → α)
    (injective_step : ∀ p x y, step p x = step p y → x = y)
    (a b : Int → α) (ha : ∀ p, a (p + 1) = step p (a p))
    (hb : ∀ p, b (p + 1) = step p (b p)) (hzero : a 0 = b 0) : a = b := by
  have hnat : ∀ k : Nat, a (k : Int) = b (k : Int) := by
    intro k
    induction k with
    | zero => exact hzero
    | succ k ih =>
      have hindex : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
      rw [hindex, ha, hb, ih]
  have hneg : ∀ k : Nat, a (-(k : Int)) = b (-(k : Int)) := by
    intro k
    induction k with
    | zero => exact hzero
    | succ k ih =>
      apply injective_step (-((k + 1 : Nat) : Int))
      rw [← ha, ← hb]
      have hindex : -((k + 1 : Nat) : Int) + 1 = -(k : Int) := by omega
      rw [hindex]
      exact ih
  funext p
  cases p with
  | ofNat k => exact hnat k
  | negSucc k =>
    have hindex : Int.negSucc k = -((k + 1 : Nat) : Int) := by omega
    rw [hindex]
    exact hneg (k + 1)
theorem tmt (p : Int) : 2 * tri p = p * (p - 1) := by
  have heq : (fun p : Int => 2 * tri p) = (fun p : Int => p * (p - 1)) := by
    apply bIu (fun p x => x + 2 * p)
    · intro p x y h
      omega
    · intro p
      rw [tao, Int.mul_add]
    · intro p
      simp only [Int.add_sub_cancel, Int.add_mul, Int.one_mul, Int.mul_sub, Int.mul_one]
      omega
    · decide
  exact congrFun heq p
end Nagata.W08
end
section
noncomputable section
namespace Nagata.W08
open Filter Topology
theorem peoee (F : ℂ → ℂ)
    (hperiod : ∀ x (k : ℤ), F (x + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = F x)
    {x y : ℂ} (hxy : Complex.exp x = Complex.exp y) : F x = F y := by
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hxy
  rw [hk, hperiod]
theorem plelL (F : ℂ → ℂ)
    (hperiod : ∀ x (k : ℤ), F (x + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = F x)
    {z z₀ : ℂ} (hz : z ≠ 0) (hz₀ : z₀ ≠ 0) :
    F (Complex.log z) = F (Complex.log (z / z₀) + Complex.log z₀) := by
  apply peoee F hperiod
  rw [Complex.exp_log hz, Complex.exp_add, Complex.exp_log (div_ne_zero hz hz₀),
    Complex.exp_log hz₀, div_mul_cancel₀ _ hz₀]
theorem pldA (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hperiod : ∀ x (k : ℤ), F (x + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = F x)
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    DifferentiableAt ℂ (fun z ↦ F (Complex.log z)) z₀ := by
  have hdiv : DifferentiableAt ℂ (fun z : ℂ ↦ z / z₀) z₀ := by
    simp only [div_eq_mul_inv]
    exact differentiableAt_id.mul_const _
  have hslit : z₀ / z₀ ∈ Complex.slitPlane := by
    simp [div_self hz₀]
  have hlocal : DifferentiableAt ℂ
      (fun z : ℂ ↦ Complex.log (z / z₀) + Complex.log z₀) z₀ :=
    ((Complex.differentiableAt_log hslit).comp z₀ (f := fun z : ℂ ↦ z / z₀) hdiv).add
      (differentiableAt_const (Complex.log z₀))
  have hg := (hF (Complex.log (z₀ / z₀) + Complex.log z₀)).comp z₀ hlocal
  apply hg.congr_of_eventuallyEq
  exact (eventually_ne_nhds hz₀).mono fun z hz ↦
    plelL F hperiod hz hz₀
theorem pla (F : ℂ → ℂ)
    (hperiod : ∀ x (k : ℤ), F (x + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = F x)
    {τ γ : ℂ} {n : ℤ} (hτ : τ ≠ 0)
    (hshift : ∀ x, F (x + Complex.log τ) =
      γ * Complex.exp (((-n : ℤ) : ℂ) * x) * F x)
    {z : ℂ} (hz : z ≠ 0) :
    F (Complex.log (τ * z)) = γ * z ^ (-n) * F (Complex.log z) := by
  have heq : F (Complex.log (τ * z)) = F (Complex.log z + Complex.log τ) := by
    apply peoee F hperiod
    rw [Complex.exp_log (mul_ne_zero hτ hz), Complex.exp_add,
      Complex.exp_log hz, Complex.exp_log hτ, mul_comm]
  rw [heq, hshift, Complex.exp_int_mul, Complex.exp_log hz]
def aSOPF (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hperiod : ∀ x (k : ℤ), F (x + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = F x)
    {τ γ : ℂ} {n : ℤ} (hτ : τ ≠ 0)
    (hshift : ∀ x, F (x + Complex.log τ) =
      γ * Complex.exp (((-n : ℤ) : ℂ) * x) * F x) :
    aS τ n γ :=
  sOF hτ (fun z ↦ F (Complex.log z))
    (fun _ hz ↦ pldA F hF hperiod hz)
    (fun _ hz ↦ pla F hperiod hτ hshift hz)
theorem aSOPF1 (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hperiod : ∀ x (k : ℤ), F (x + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = F x)
    {τ γ : ℂ} {n : ℤ} (hτ : τ ≠ 0)
    (hshift : ∀ x, F (x + Complex.log τ) =
      γ * Complex.exp (((-n : ℤ) : ℂ) * x) * F x) (x : ℂ) :
    (aSOPF F hF hperiod hτ hshift).val (Complex.exp x) = F x := by
  change nAZ (fun z ↦ F (Complex.log z)) (Complex.exp x) = F x
  rw [nAZon _ (Complex.exp_ne_zero x)]
  apply peoee F hperiod
  exact Complex.exp_log (Complex.exp_ne_zero x)
end Nagata.W08
end
end
section
namespace Nagata.W08
variable {F : Type*} [CommGroupWithZero F]
def oV (τ γ : F) (n K : ℤ) (c₀ : F) (p : ℤ) : F :=
  γ ^ (-p) * τ ^ (lE n K p) * c₀
@[simp] theorem oVz (τ γ : F) (n K : ℤ) (c₀ : F) :
    oV τ γ n K c₀ 0 = c₀ := by
  simp [oV]
theorem oVao (τ γ : F) (hτ : τ ≠ 0) (hγ : γ ≠ 0)
    (n K : ℤ) (c₀ : F) (p : ℤ) :
    oV τ γ n K c₀ (p + 1) =
      (γ⁻¹ * τ ^ (K + n * p)) * oV τ γ n K c₀ p := by
  unfold oV
  rw [show -(p + 1) = -1 + -p by omega, zpow_add₀ hγ, zpow_neg_one,
    lEao, zpow_add₀ hτ]
  ac_rfl
theorem lrai (τ γ : F) (hτ : τ ≠ 0) (hγ : γ ≠ 0)
    (n : ℤ) (c : ℤ → F)
    (hc : ∀ K, c (K + n) = γ⁻¹ * τ ^ K * c K) (K p : ℤ) :
    c (K + n * p) = c K * γ ^ (-p) * τ ^ (p * K + n * (p * (p - 1) / 2)) := by
  have horbit : (fun p : ℤ => c (K + n * p)) = oV τ γ n K (c K) := by
    apply bIu (fun p x => (γ⁻¹ * τ ^ (K + n * p)) * x)
    · intro p
      exact fun _ _ h => mul_left_cancel₀
        (mul_ne_zero (inv_ne_zero hγ) (zpow_ne_zero _ hτ)) h
    · intro p
      have hindex : K + n * (p + 1) = K + n * p + n := by
        simp only [Int.mul_add, Int.mul_one]
        omega
      rw [hindex, hc]
    · exact oVao τ γ hτ hγ n K (c K)
    · simp
  have hvalue := congrFun horbit p
  simpa only [oV, lE, tri, mul_assoc, mul_comm, mul_left_comm]
    using hvalue
theorem rocb (τ γ : F) (hγ : γ ≠ 0)
    (n : ℤ) (c : ℤ → F)
    (hbalance : ∀ K, τ ^ K * c K = γ * c (K + n)) :
    ∀ K, c (K + n) = γ⁻¹ * τ ^ K * c K := by
  intro K
  calc
    c (K + n) = γ⁻¹ * (γ * c (K + n)) := (inv_mul_cancel_left₀ hγ _).symm
    _ = γ⁻¹ * (τ ^ K * c K) := by rw [← hbalance]
    _ = γ⁻¹ * τ ^ K * c K := (mul_assoc _ _ _).symm
end Nagata.W08
end
end OAI
end
section
namespace OAI
section
namespace Nagata.CS
noncomputable def mP2 (P : ℂ → ℂ) (e : ℕ) :
    (ℂ → ℂ) →ₗ[ℂ] (ℂ → ℂ) where
  toFun f z := P z ^ e * f z
  map_add' f g := by funext z; simp [mul_add]
  map_smul' a f := by funext z; simp; ring
theorem mPms {τ γ δ : ℂ} {n s : ℤ} {P f : ℂ → ℂ}
    (hP : P ∈ Nagata.W08.aS τ s δ)
    (hf : f ∈ Nagata.W08.aS τ n γ) (e : ℕ) :
    mP2 P e f ∈ Nagata.W08.aS τ
      (n + (e : ℤ) * s) (γ * δ ^ e) := by
  refine ⟨?_, ?_, ?_⟩
  · change P 0 ^ e * f 0 = 0
    rw [hf.1, mul_zero]
  · intro z hz
    exact ((hP.2.1 z hz).pow e).mul (hf.2.1 z hz)
  · intro z hz
    change P (τ * z) ^ e * f (τ * z) =
      (γ * δ ^ e) * z ^ (-(n + (e : ℤ) * s)) * (P z ^ e * f z)
    rw [hP.2.2 z hz, hf.2.2 z hz]
    have he : -(n + (e : ℤ) * s) = -n + (-s) * (e : ℤ) := by ring
    rw [he, zpow_add₀ hz, zpow_mul, zpow_natCast]
    simp only [mul_pow]
    ring
noncomputable def nMMM (γL γP : ℂ) : ℂ := γL ^ 3 / γP
noncomputable def cS (τ γL γP : ℂ) (d m j : ℤ) (P : ℂ → ℂ) :
    Submodule ℂ (ℂ → ℂ) :=
  if j ≤ m then
    Nagata.W08.aS τ (3 * (d - 3 * m))
      (γL ^ (d - 3 * m) * nMMM γL γP ^ (m - j))
  else
    (Nagata.W08.aS τ (3 * (d - 3 * j)) (γL ^ (d - 3 * j))).map
      (mP2 P (j - m).toNat)
theorem mcSs {τ γL γP : ℂ} {d m j : ℤ} {P g : ℂ → ℂ}
    (hj : m < j) :
    g ∈ cS τ γL γP d m j P ↔
      ∃ f ∈ Nagata.W08.aS τ (3 * (d - 3 * j))
        (γL ^ (d - 3 * j)), mP2 P (j - m).toNat f = g := by
  rw [cS, if_neg (not_le.mpr hj)]
  exact Submodule.mem_map
noncomputable def pS (τ γL γP : ℂ) (d m : ℤ) (P : ℂ → ℂ) :
    Submodule ℂ (Polynomial (ℂ → ℂ)) where
  carrier := {F | (∀ j : ℕ, (d / 3).toNat < j → F.coeff j = 0) ∧
    ∀ j : ℕ, F.coeff j ∈ cS τ γL γP d m (j : ℤ) P}
  zero_mem' := by
    constructor
    · intro j _; simp
    · intro j; simp
  add_mem' := by
    intro F G hF hG
    constructor
    · intro j hj
      simp only [Polynomial.coeff_add, hF.1 j hj, hG.1 j hj, add_zero]
    · intro j
      simpa only [Polynomial.coeff_add] using
        (cS τ γL γP d m (j : ℤ) P).add_mem (hF.2 j) (hG.2 j)
  smul_mem' := by
    intro a F hF
    constructor
    · intro j hj
      simp only [Polynomial.coeff_smul, hF.1 j hj, smul_zero]
    · intro j
      simpa only [Polynomial.coeff_smul] using
        (cS τ γL γP d m (j : ℤ) P).smul_mem a (hF.2 j)
noncomputable def sE (F : Polynomial (ℂ → ℂ)) (z v : ℂ) : ℂ :=
  F.sum fun j f => f z * v ^ j
end Nagata.CS
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W19
theorem pPeer : {z : ℂ | z ≠ 0} = Set.range Complex.exp := by
  ext z
  constructor
  · intro hz
    exact ⟨Complex.log z, Complex.exp_log hz⟩
  · rintro ⟨w, rfl⟩
    exact Complex.exp_ne_zero w
theorem pPiC : IsConnected {z : ℂ | z ≠ 0} := by
  rw [pPeer]
  exact isConnected_range Complex.continuous_exp
theorem hpmz (f g : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f {z : ℂ | z ≠ 0})
    (hg : DifferentiableOn ℂ g {z : ℂ | z ≠ 0})
    (hfg : ∀ z, z ≠ 0 → f z * g z = 0) :
    (∀ z, z ≠ 0 → f z = 0) ∨ (∀ z, z ≠ 0 → g z = 0) := by
  have ho : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne
  exact (hf.analyticOnNhd ho).eq_zero_or_eq_zero_of_mul_eq_zero
    (hg.analyticOnNhd ho) hfg pPiC.isPreconnected
end Nagata.W19
end
section
namespace Nagata.W19
theorem dOpe {σ : Type*} {U : Set ℂ}
    (s : σ → ℂ → ℂ) (hs : ∀ i, DifferentiableOn ℂ (s i) U)
    (P : MvPolynomial σ ℂ) :
    DifferentiableOn ℂ (fun z => MvPolynomial.eval (fun i => s i z) P) U := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa only [MvPolynomial.eval_C] using differentiableOn_const a
  | add P Q hP hQ =>
    simp only [map_add]
    exact hP.add hQ
  | mul_X P i hP =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hP.mul (hs i)
theorem pepmz {σ : Type*}
    (s : σ → ℂ → ℂ) (hs : ∀ i, DifferentiableOn ℂ (s i) {z : ℂ | z ≠ 0})
    (P Q : MvPolynomial σ ℂ)
    (hPQ : ∀ z, z ≠ 0 → MvPolynomial.eval (fun i => s i z) (P * Q) = 0) :
    (∀ z, z ≠ 0 → MvPolynomial.eval (fun i => s i z) P = 0) ∨
      (∀ z, z ≠ 0 → MvPolynomial.eval (fun i => s i z) Q = 0) := by
  apply hpmz
    (fun z => MvPolynomial.eval (fun i => s i z) P)
    (fun z => MvPolynomial.eval (fun i => s i z) Q)
    (dOpe s hs P) (dOpe s hs Q)
  intro z hz
  simpa only [map_mul] using hPQ z hz
end Nagata.W19
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W19
open scoped Topology
open Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
theorem ddtv
    {H : E → ℂ} {p : E} (hH : AnalyticAt ℂ H p) (v : E) (m : ℕ)
    (hvan : ∀ n < m, iteratedFDeriv ℂ n H p = 0) :
    ∀ n, n + 1 < m →
      iteratedFDeriv ℂ n (fun z => fderiv ℂ H z v) p = 0 := by
  intro n hn
  have hz : iteratedFDeriv ℂ n (fderiv ℂ H) p = 0 := by
    apply norm_eq_zero.mp
    rw [norm_iteratedFDeriv_fderiv, hvan (n + 1) hn, norm_zero]
  change iteratedFDeriv ℂ n ((ContinuousLinearMap.apply ℂ ℂ v) ∘ fderiv ℂ H) p = 0
  rw [(ContinuousLinearMap.apply ℂ ℂ v).iteratedFDeriv_comp_left
    (hH.fderiv.contDiffAt (n := (n : WithTop ℕ∞))) le_rfl, hz]
  ext w
  simp
noncomputable def dI (v : E) : ℕ → (E → ℂ) → E → ℂ
  | 0, H => H
  | b + 1, H => dI v b (fun z => fderiv ℂ H z v)
theorem dIaA {H : E → ℂ} {p : E}
    (hH : AnalyticAt ℂ H p) (v : E) (b : ℕ) :
    AnalyticAt ℂ (dI v b H) p := by
  induction b generalizing H with
  | zero => exact hH
  | succ b ih =>
    apply ih
    exact ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp hH.fderiv
theorem dItv {H : E → ℂ} {p : E}
    (hH : AnalyticAt ℂ H p) (v : E) (m b : ℕ)
    (hvan : ∀ n < m, iteratedFDeriv ℂ n H p = 0) :
    ∀ n, n + b < m → iteratedFDeriv ℂ n (dI v b H) p = 0 := by
  induction b generalizing H m with
  | zero => simpa [dI] using hvan
  | succ b ih =>
    have ha : AnalyticAt ℂ (fun z => fderiv ℂ H z v) p :=
      ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp hH.fderiv
    have hv : ∀ n < m - 1, iteratedFDeriv ℂ n (fun z => fderiv ℂ H z v) p = 0 := by
      intro n hn
      exact ddtv hH v m hvan n (by omega)
    intro n hn
    exact ih ha (m - 1) hv n (by omega)
theorem aptv
    [CompleteSpace E]
    {H : E → ℂ} {p : ℂ} {γ : ℂ → E}
    (hH : AnalyticAt ℂ H (γ p)) (hγ : AnalyticAt ℂ γ p)
    (m : ℕ) (hvan : ∀ n < m, iteratedFDeriv ℂ n H (γ p) = 0) :
    ∀ n < m, iteratedFDeriv ℂ n (H ∘ γ) p = 0 := by
  intro n hn
  rw [iteratedFDeriv_comp (hH.contDiffAt (n := (n : WithTop ℕ∞)))
    (hγ.contDiffAt (n := (n : WithTop ℕ∞))) le_rfl]
  unfold FormalMultilinearSeries.taylorComp
  apply Finset.sum_eq_zero
  intro c _
  ext
  simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply, ftaylorSeries]
  rw [hvan c.length (lt_of_le_of_lt c.length_le hn)]
  simp
theorem troot
    {H : (ℂ × ℂ) → ℂ} (ξ : ℂ)
    (hH : AnalyticAt ℂ H (ξ, 0)) (m b : ℕ)
    (hvan : ∀ n < m, iteratedFDeriv ℂ n H (ξ, 0) = 0) :
    (m - b : ℕ) ≤ analyticOrderAt
      (fun x => dI (0, 1) b H (x, 0)) ξ := by
  let G := dI (0, 1) b H
  have hG : AnalyticAt ℂ G (ξ, 0) := dIaA hH (0, 1) b
  have hγ : AnalyticAt ℂ (fun x : ℂ => (x, (0 : ℂ))) ξ := by fun_prop
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hG.comp (f := fun x : ℂ => (x, (0 : ℂ))) (x := ξ) hγ)).mpr
  intro n hn
  rw [iteratedDeriv_eq_iteratedFDeriv]
  have hv : ∀ j < m - b, iteratedFDeriv ℂ j G (ξ, 0) = 0 := by
    intro j hj
    exact dItv hH (0, 1) m b hvan j (by omega)
  have hz := aptv (γ := fun x : ℂ => (x, (0 : ℂ))) (p := ξ) hG hγ (m - b) hv n hn
  simpa only [Function.comp_def, zero_apply] using congrArg (fun L => L (fun _ => (1 : ℂ))) hz
theorem dIvei
    {H : (ℂ × ℂ) → ℂ} {x y : ℂ} (hH : AnalyticAt ℂ H (x, y)) (b : ℕ) :
    dI (0, 1) b H (x, y) =
      iteratedDeriv b (fun t => H (x, t)) y := by
  induction b generalizing H with
  | zero => simp [dI]
  | succ b ih =>
    let G : (ℂ × ℂ) → ℂ := fun z => fderiv ℂ H z (0, 1)
    have hG : AnalyticAt ℂ G (x, y) := by
      change AnalyticAt ℂ ((ContinuousLinearMap.apply ℂ ℂ ((0, 1) : ℂ × ℂ)) ∘
        fderiv ℂ H) (x, y)
      exact ((ContinuousLinearMap.apply ℂ ℂ ((0, 1) : ℂ × ℂ)).analyticAt _).comp hH.fderiv
    have hc : ContinuousAt (fun t : ℂ => (x, t)) y := by fun_prop
    have hev : ∀ᶠ t in 𝓝 y, AnalyticAt ℂ H (x, t) :=
      hc.tendsto.eventually hH.eventually_analyticAt
    have heq : (fun t => deriv (fun u => H (x, u)) t) =ᶠ[𝓝 y]
        (fun t => G (x, t)) := by
      filter_upwards [hev] with t ht
      have hline : HasDerivAt (fun u : ℂ => (x, u)) (0, 1) t :=
        by simpa using ((hasFDerivAt_const (𝕜 := ℂ) x t).prodMk
          (hasFDerivAt_id t)).hasDerivAt
      exact (ht.differentiableAt.hasFDerivAt.comp_hasDerivAt t hline).deriv
    change dI (0, 1) b G (x, y) = _
    rw [ih hG, iteratedDeriv_succ']
    exact (Filter.EventuallyEq.iteratedDeriv_eq b heq).symm
theorem tiDoo1
    {H : (ℂ × ℂ) → ℂ} (ξ : ℂ)
    (hH : AnalyticAt ℂ H (ξ, 0)) (m b : ℕ)
    (hvan : ∀ n < m, iteratedFDeriv ℂ n H (ξ, 0) = 0) :
    (m - b : ℕ) ≤ analyticOrderAt
      (fun x => iteratedDeriv b (fun y => H (x, y)) 0) ξ := by
  have hc : ContinuousAt (fun x : ℂ => (x, (0 : ℂ))) ξ := by fun_prop
  have hev : ∀ᶠ x in 𝓝 ξ, AnalyticAt ℂ H (x, 0) :=
    hc.tendsto.eventually hH.eventually_analyticAt
  have heq : (fun x => dI (0, 1) b H (x, 0)) =ᶠ[𝓝 ξ]
      (fun x => iteratedDeriv b (fun y => H (x, y)) 0) := by
    filter_upwards [hev] with x hx
    exact dIvei hx b
  rw [← analyticOrderAt_congr heq]
  exact troot ξ hH m b hvan
end Nagata.W19
end
section
namespace Nagata.W19
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
private theorem dScz
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (P : FormalMultilinearSeries ℂ E F) (n : ℕ) (hzero : P (n + 1) = 0) :
    P.derivSeries n = 0 := by
  have hz' : ∀ j, j = n + 1 → P j = 0 := by
    intro j hj
    subst j
    exact hzero
  have hz : P (1 + n) = 0 := hz' (1 + n) (Nat.add_comm 1 n)
  ext v w
  simp [FormalMultilinearSeries.derivSeries,
    ContinuousLinearMap.compFormalMultilinearSeries_apply,
    FormalMultilinearSeries.changeOriginSeries,
    FormalMultilinearSeries.changeOriginSeriesTerm, hz]
private theorem iFDzo (n : ℕ) :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
      {H : E → F} {p : E} {P : FormalMultilinearSeries ℂ E F},
      HasFPowerSeriesAt H P p → P n = 0 → iteratedFDeriv ℂ n H p = 0 := by
  induction n with
  | zero =>
    intro F _ _ _ H p P hP hzero
    ext v
    simpa [hzero] using (hP.coeff_zero v).symm
  | succ n ih =>
    intro F _ _ _ H p P hP hzero
    obtain ⟨r, hr⟩ := hP
    have hd : P.derivSeries n = 0 := dScz P n hzero
    have hi := ih (F := E →L[ℂ] F) hr.fderiv.hasFPowerSeriesAt hd
    apply norm_eq_zero.mp
    rw [← norm_iteratedFDeriv_fderiv, hi, norm_zero]
theorem ttvop
    {H : E → ℂ} {p : E} {P : FormalMultilinearSeries ℂ E ℂ}
    (hP : HasFPowerSeriesAt H P p) (m : ℕ) (hzero : ∀ n < m, P n = 0) :
    ∀ n < m, iteratedFDeriv ℂ n H p = 0 := by
  intro n hn
  exact iFDzo n hP (hzero n hn)
theorem tiDoo
    {H : (ℂ × ℂ) → ℂ} {P : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ}
    (ξ : ℂ) (hP : HasFPowerSeriesAt H P (ξ, 0))
    (m b : ℕ) (hzero : ∀ n < m, P n = 0) :
    (m - b : ℕ) ≤ analyticOrderAt
      (fun x => iteratedDeriv b (fun y => H (x, y)) 0) ξ := by
  apply tiDoo1 ξ ⟨P, hP⟩ m b
  exact ttvop hP m hzero
end Nagata.W19
end
section
namespace Nagata.W19
open scoped Topology
open Filter
theorem aAtiD
    {H : (ℂ × ℂ) → ℂ} (ξ : ℂ) (hH : AnalyticAt ℂ H (ξ, 0)) (b : ℕ) :
    AnalyticAt ℂ (fun x => iteratedDeriv b (fun y => H (x, y)) 0) ξ := by
  have hγ : AnalyticAt ℂ (fun x : ℂ => (x, (0 : ℂ))) ξ := by fun_prop
  have hG := (dIaA hH (0, 1) b).comp
    (f := fun x : ℂ => (x, (0 : ℂ))) (x := ξ) hγ
  apply hG.congr
  have hev : ∀ᶠ x in 𝓝 ξ, AnalyticAt ℂ H (x, 0) :=
    hγ.continuousAt.tendsto.eventually hH.eventually_analyticAt
  filter_upwards [hev] with x hx
  exact dIvei hx b
end Nagata.W19
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W20
open scoped Topology BigOperators
open Nagata.CS
noncomputable section
abbrev AS (τ γL γP : ℂ) (d : ℤ) (m : ℕ) (P : ℂ → ℂ) :=
  pS τ γL γP d (m : ℤ) P
def lS1 {τ γL γP : ℂ} {d : ℤ} {m : ℕ} {P : ℂ → ℂ}
    (F : AS τ γL γP d m P) (z₀ x y : ℂ) : ℂ :=
  sE F.val (z₀ * Complex.exp x) (Complex.exp y)
end
end Nagata.W20
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W09
open Complex Real Metric
open scoped Topology
noncomputable def aLC (r : ℝ) (f : ℂ → ℂ) (k : ℤ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    ∮ z in C(0, r), z ^ (-k - 1) * f z
theorem dAlI {f : ℂ → ℂ}
    (hf : ∀ z, z ≠ 0 → DifferentiableAt ℂ f z) (k : ℤ) {z : ℂ} (hz : z ≠ 0) :
    DifferentiableAt ℂ (fun w => w ^ (-k - 1) * f w) z :=
  (differentiableAt_zpow.mpr (Or.inl hz)).mul (hf z hz)
theorem cIlI {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : ∀ z, z ≠ 0 → DifferentiableAt ℂ f z) (k : ℤ) :
    CircleIntegrable (fun z => z ^ (-k - 1) * f z) 0 r := by
  apply ContinuousOn.circleIntegrable hr.le
  intro z hz
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    exact hr.ne (by simpa [Metric.mem_sphere] using hz)
  exact (dAlI hf k hz0).continuousAt.continuousWithinAt
theorem aLCa {r : ℝ} (hr : 0 < r) {f g : ℂ → ℂ}
    (hf : ∀ z, z ≠ 0 → DifferentiableAt ℂ f z)
    (hg : ∀ z, z ≠ 0 → DifferentiableAt ℂ g z) (k : ℤ) :
    aLC r (f + g) k = aLC r f k + aLC r g k := by
  unfold aLC
  simp only [Pi.add_apply, mul_add]
  rw [circleIntegral.integral_add (cIlI hr hf k)
    (cIlI hr hg k), mul_add]
theorem aLCs (r : ℝ) (a : ℂ) (f : ℂ → ℂ) (k : ℤ) :
    aLC r (a • f) k = a * aLC r f k := by
  unfold aLC
  simp only [Pi.smul_apply, smul_eq_mul]
  have heq : (fun z : ℂ => z ^ (-k - 1) * (a * f z)) =
      (fun z => a * (z ^ (-k - 1) * f z)) := by
    funext z
    ring
  rw [heq, circleIntegral.integral_const_mul]
  ring
noncomputable def lCM (τ : ℂ) (n : ℤ) (γ : ℂ) :
    Nagata.W08.aS τ n γ →ₗ[ℂ] (ℤ → ℂ) where
  toFun f k := aLC 1 f.val k
  map_add' f g := by
    funext k
    exact aLCa zero_lt_one f.property.2.1 g.property.2.1 k
  map_smul' a f := by
    funext k
    exact aLCs 1 a f.val k
end Nagata.W09
end
section
namespace Nagata.W09
open Complex Metric MeasureTheory Filter
open scoped Topology
theorem hScIo
    {ι : Type*} [Countable ι] {r : ℝ} (hr : 0 < r)
    (F : ι → ℂ → ℂ) (f : ℂ → ℂ) (B : ι → ℝ)
    (hB : Summable B)
    (hcont : ∀ i, ContinuousOn (F i) (sphere 0 r))
    (hbound : ∀ i z, z ∈ sphere 0 r → ‖F i z‖ ≤ B i)
    (hsum : ∀ z, z ∈ sphere 0 r → HasSum (fun i => F i z) (f z)) :
    HasSum (fun i => ∮ z in C(0, r), F i z) (∮ z in C(0, r), f z) := by
  unfold circleIntegral
  apply intervalIntegral.hasSum_integral_of_dominated_convergence (fun i _ => r * B i)
  · intro i
    exact ((hcont i).circleIntegrable hr.le).out.aestronglyMeasurable_restrict_uIoc
  · intro i
    exact ae_of_all _ fun θ _ => by
      simp only [norm_smul, deriv_circleMap, norm_mul, Complex.norm_I,
        mul_one, norm_circleMap_zero, abs_of_pos hr]
      exact mul_le_mul_of_nonneg_left (hbound i _ (circleMap_mem_sphere 0 hr.le θ)) hr.le
  · exact ae_of_all _ fun _ _ => hB.mul_left r
  · exact intervalIntegrable_const
  · exact ae_of_all _ fun θ _ =>
      (hsum _ (circleMap_mem_sphere 0 hr.le θ)).const_smul _
theorem hSaLC2
    {ι : Type*} [Countable ι] {r : ℝ} (hr : 0 < r)
    (F : ι → ℂ → ℂ) (f : ℂ → ℂ) (k : ℤ) (B : ι → ℝ)
    (hB : Summable B)
    (hcont : ∀ i, ContinuousOn (F i) (sphere 0 r))
    (hbound : ∀ i z, z ∈ sphere 0 r → ‖z ^ (-k - 1) * F i z‖ ≤ B i)
    (hsum : ∀ z, z ∈ sphere 0 r → HasSum (fun i => F i z) (f z)) :
    HasSum (fun i => aLC r (F i) k) (aLC r f k) := by
  have hpow : ContinuousOn (fun z : ℂ => z ^ (-k - 1)) (sphere 0 r) := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      subst z
      exact hr.ne (by simpa [Metric.mem_sphere] using hz)
    exact (differentiableAt_zpow.mpr (Or.inl hz0)).continuousAt.continuousWithinAt
  exact (hScIo hr
    (fun i z => z ^ (-k - 1) * F i z) (fun z => z ^ (-k - 1) * f z) B hB
    (fun i => hpow.mul (hcont i)) hbound
    (fun z hz => (hsum z hz).mul_left _)).mul_left _
theorem hSaLC1
    {ι : Type*} [Countable ι] {r : ℝ} (hr : 0 < r)
    (F : ι → ℂ → ℂ) (f : ℂ → ℂ) (k : ℤ) (B : ι → ℝ)
    (hB : Summable B)
    (hcont : ∀ i, ContinuousOn (F i) (sphere 0 r))
    (hbound : ∀ i z, z ∈ sphere 0 r → ‖F i z‖ ≤ B i)
    (hsum : ∀ z, z ∈ sphere 0 r → HasSum (fun i => F i z) (f z)) :
    HasSum (fun i => aLC r (F i) k) (aLC r f k) := by
  apply hSaLC2 hr F f k
    (fun i => r ^ (-k - 1) * B i) (hB.mul_left _) hcont
  · intro i z hz
    have hnorm : ‖z‖ = r := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
    rw [norm_mul, norm_zpow, hnorm]
    exact mul_le_mul_of_nonneg_left (hbound i z hz) (zpow_pos hr _).le
  · exact hsum
theorem ecaom {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : z ∈ sphere 0 r) :
    ∃ θ ∈ Set.Ioc (0 : ℝ) (2 * Real.pi), circleMap 0 r θ = z := by
  have hmem : z ∈ circleMap 0 r '' Set.Ioc (0 : ℝ) (2 * Real.pi) := by
    rw [image_circleMap_Ioc, abs_of_pos hr]
    exact hz
  exact hmem
end Nagata.W09
end
section
namespace Nagata.W09
open Complex Real Metric
theorem aLCc {r : ℝ} (hr : 0 ≤ r) {f g : ℂ → ℂ}
    (h : Set.EqOn f g (Metric.sphere 0 r)) (k : ℤ) :
    aLC r f k = aLC r g k := by
  unfold aLC
  congr 1
  apply circleIntegral.integral_congr hr
  intro z hz
  dsimp only
  rw [h hz]
theorem cIsr (a r : ℝ) (f : ℂ → ℂ) :
    (∮ z in C(0, a * r), f z) =
      (a : ℂ) * ∮ z in C(0, r), f ((a : ℂ) * z) := by
  unfold circleIntegral
  calc
    _ = ∫ θ in (0 : ℝ)..2 * Real.pi,
        (a : ℂ) * (deriv (circleMap 0 r) θ * f ((a : ℂ) * circleMap 0 r θ)) := by
      apply intervalIntegral.integral_congr
      intro θ _
      simp only [deriv_circleMap, circleMap, zero_add,
        Complex.ofReal_mul, smul_eq_mul, mul_assoc]
    _ = _ := by
      simpa only [smul_eq_mul] using intervalIntegral.integral_const_mul (a : ℂ)
        (fun θ => deriv (circleMap 0 r) θ * f ((a : ℂ) * circleMap 0 r θ))
theorem aLCzm {r : ℝ} (hr : 0 < r)
    (f : ℂ → ℂ) (n k : ℤ) :
    aLC r (fun z => z ^ (-n) * f z) k =
      aLC r f (k + n) := by
  unfold aLC
  congr 1
  apply circleIntegral.integral_congr hr.le
  intro z hz
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    exact hr.ne (by simpa [Metric.mem_sphere] using hz)
  dsimp only
  rw [← mul_assoc, ← zpow_add₀ hz0]
  congr 2
  omega
theorem aLCcp {a : ℝ} (ha : 0 < a)
    (r : ℝ) (f : ℂ → ℂ) (k : ℤ) :
    aLC r (fun z => f ((a : ℂ) * z)) k =
      (a : ℂ) ^ k * aLC (a * r) f k := by
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  unfold aLC
  rw [cIsr]
  have hfun : (fun z : ℂ => ((a : ℂ) * z) ^ (-k - 1) * f ((a : ℂ) * z)) =
      fun z => (a : ℂ) ^ (-k - 1) * (z ^ (-k - 1) * f ((a : ℂ) * z)) := by
    funext z
    rw [mul_zpow]
    ring
  rw [hfun, circleIntegral.integral_const_mul]
  have hpow : (a : ℂ) ^ k * (a : ℂ) * (a : ℂ) ^ (-k - 1) = 1 := by
    have hp : (a : ℂ) ^ k * (a : ℂ) = (a : ℂ) ^ (k + 1) := by
      rw [zpow_add₀ ha0, zpow_one]
    rw [hp, ← zpow_add₀ ha0]
    simp only [show k + 1 + (-k - 1) = 0 by omega, zpow_zero]
  calc
    _ = ((a : ℂ) ^ k * (a : ℂ) * (a : ℂ) ^ (-k - 1)) *
        ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ∮ z in C(0, r), z ^ (-k - 1) * f ((a : ℂ) * z)) := by rw [hpow, one_mul]
    _ = _ := by ring
end Nagata.W09
end
section
namespace Nagata.W09
open Complex Metric Set
theorem cIreo
    {r R : ℝ} (hr : 0 < r) (hle : r ≤ R) {f : ℂ → ℂ}
    (hf : ∀ z, z ≠ 0 → DifferentiableAt ℂ f z) :
    (∮ z in C(0, R), f z) = ∮ z in C(0, r), f z := by
  apply Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hle
    Set.countable_empty
  · intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      subst z
      exact hz.2 (by simpa using hr)
    exact (hf z hz0).continuousAt.continuousWithinAt
  · intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      subst z
      exact hz.1.2 (by simpa using hr.le)
    exact hf z hz0
theorem aLCri
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) {f : ℂ → ℂ}
    (hf : ∀ z, z ≠ 0 → DifferentiableAt ℂ f z) (k : ℤ) :
    aLC r f k = aLC s f k := by
  unfold aLC
  congr 1
  rcases le_total r s with hrs | hsr
  · exact (cIreo hr hrs
      (fun z hz => dAlI hf k hz)).symm
  · exact cIreo hs hsr
      (fun z hz => dAlI hf k hz)
end Nagata.W09
end
section
namespace Nagata.W09
open Nagata.W08
variable {F : Type*} [CommGroupWithZero F]
noncomputable def sOC (τ γ : F) (n K : ℤ) (c₀ : F) (k : ℤ) : F :=
  if n ∣ k - K then oV τ γ n K c₀ ((k - K) / n) else 0
@[simp] theorem sOCi (τ γ : F) (n K : ℤ) (c₀ : F) :
    sOC τ γ n K c₀ K = c₀ := by
  simp [sOC]
theorem sOCs (τ γ : F) (n K : ℤ) (c₀ : F) (k : ℤ)
    (h : sOC τ γ n K c₀ k ≠ 0) : n ∣ k - K := by
  by_contra hdiv
  simp [sOC, hdiv] at h
theorem sOCr (τ γ : F) (n K : ℤ) (c₀ : F) (k : ℤ)
    (h : sOC τ γ n K c₀ k ≠ 0) : k % n = K % n :=
  Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    (Int.emod_eq_zero_of_dvd (sOCs τ γ n K c₀ k h))
theorem sOCoo (τ γ : F) {n : ℤ} (hn : n ≠ 0)
    (K : ℤ) (c₀ : F) (p : ℤ) :
    sOC τ γ n K c₀ (K + n * p) = oV τ γ n K c₀ p := by
  have hdiff : K + n * p - K = n * p := by omega
  simp [sOC, hdiff, Int.mul_ediv_cancel_left p hn]
end Nagata.W09
end
section
namespace Nagata.W09
open Complex Metric
theorem aLCbp {τ : ℝ} (hτ : 0 < τ)
    (n : ℤ) (γ : ℂ) (f : Nagata.W08.aS (τ : ℂ) n γ) (k : ℤ) :
    (τ : ℂ) ^ k * aLC 1 f.val k =
      γ * aLC 1 f.val (k + n) := by
  have hcomp : aLC 1 (fun z => f.val ((τ : ℂ) * z)) k =
      γ * aLC 1 f.val (k + n) := by
    calc
      _ = aLC 1 (γ • (fun z => z ^ (-n) * f.val z)) k := by
        apply aLCc (by norm_num)
        intro z hz
        have hz0 : z ≠ 0 := by
          intro h
          subst z
          simp at hz
        simpa only [Pi.smul_apply, smul_eq_mul, mul_assoc] using f.property.2.2 z hz0
      _ = γ * aLC 1 (fun z => z ^ (-n) * f.val z) k :=
        aLCs 1 γ _ k
      _ = γ * aLC 1 f.val (k + n) := by
        rw [aLCzm zero_lt_one]
  have hdilate := aLCcp hτ 1 f.val k
  rw [mul_one, aLCri hτ zero_lt_one f.property.2.1 k] at hdilate
  exact hdilate.symm.trans hcomp
theorem lCMrp {τ : ℝ} (hτ : 0 < τ)
    (n : ℤ) (γ : ℂ) (hγ : γ ≠ 0)
    (f : Nagata.W08.aS (τ : ℂ) n γ) (k : ℤ) :
    lCM (τ : ℂ) n γ f (k + n) =
      γ⁻¹ * (τ : ℂ) ^ k * lCM (τ : ℂ) n γ f k := by
  exact Nagata.W08.rocb (τ : ℂ) γ hγ n
    (fun j => aLC 1 f.val j)
    (aLCbp hτ n γ f) k
end Nagata.W09
end
section
namespace Nagata.W09
open Complex Metric
theorem aLCm {r : ℝ} (hr : 0 < r) (j k : ℤ) :
    aLC r (fun z => z ^ j) k = if j = k then 1 else 0 := by
  unfold aLC
  have hi : (∮ z in C(0, r), z ^ (-k - 1) * z ^ j) =
      ∮ z in C(0, r), z ^ (j - k - 1) := by
    apply circleIntegral.integral_congr hr.le
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      subst z
      exact hr.ne (by simpa [Metric.mem_sphere] using hz)
    dsimp only
    rw [← zpow_add₀ hz0]
    congr 1
    omega
  rw [hi]
  by_cases hjk : j = k
  · subst j
    simp only [sub_self, zero_sub, zpow_neg_one]
    have hcircle : (∮ z in C(0, r), z⁻¹) = 2 * (Real.pi : ℂ) * Complex.I := by
      simpa only [sub_zero] using circleIntegral.integral_sub_center_inv (0 : ℂ) hr.ne'
    have hconst : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
    rw [hcircle, inv_mul_cancel₀ hconst]
    simp
  · rw [if_neg hjk]
    have hne : j - k - 1 ≠ -1 := by omega
    have hcircle : (∮ z in C(0, r), z ^ (j - k - 1)) = 0 := by
      simpa only [sub_zero] using circleIntegral.integral_sub_zpow_of_ne hne (0 : ℂ) 0 r
    rw [hcircle, mul_zero]
theorem aLCsm {r : ℝ} (hr : 0 < r)
    (a : ℂ) (j k : ℤ) :
    aLC r (fun z => a * z ^ j) k = if j = k then a else 0 := by
  change aLC r (a • (fun z : ℂ => z ^ j)) k = _
  rw [aLCs, aLCm hr]
  split <;> simp
end Nagata.W09
end
section
namespace Nagata.W09
theorem lreot
    {F : Type*} [CommGroupWithZero F] (τ γ : F) (hτ : τ ≠ 0) (hγ : γ ≠ 0)
    (U : ℝ) {n : ℤ} (hn : 0 < n) (c d : ℤ → F)
    (hc : ∀ k, c (k + n) = γ⁻¹ * τ ^ k * c k)
    (hd : ∀ k, d (k + n) = γ⁻¹ * τ ^ k * d k)
    (hinitial : ∀ K ∈ tI U n, c K = d K) : c = d := by
  funext k
  obtain ⟨K, hK, hres⟩ := etImE U hn k
  have hdiv : n ∣ k - K := Int.dvd_of_emod_eq_zero
    (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hres.symm)
  let p := (k - K) / n
  have hp : n * p = k - K := Int.mul_ediv_cancel_of_dvd hdiv
  have hkp : k = K + n * p := by omega
  rw [hkp, Nagata.W08.lrai τ γ hτ hγ n c hc,
    Nagata.W08.lrai τ γ hτ hγ n d hd, hinitial K hK]
end Nagata.W09
end
section
namespace Nagata.W09
open Complex Metric
private theorem cOsmc {r : ℝ} (hr : 0 < r)
    (a : ℂ) (j : ℤ) : ContinuousOn (fun z : ℂ => a * z ^ j) (sphere 0 r) := by
  intro z hz
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    exact hr.ne (by simpa [Metric.mem_sphere] using hz)
  exact ((differentiableAt_const a).mul
    (differentiableAt_zpow.mpr (Or.inl hz0))).continuousAt.continuousWithinAt
theorem hSaLC
    {ι : Type*} [Countable ι] {r : ℝ} (hr : 0 < r)
    (a : ι → ℂ) (N : ι → ℤ) (f : ℂ → ℂ) (B : ι → ℝ)
    (hB : Summable B)
    (hbound : ∀ i z, z ∈ sphere 0 r → ‖a i * z ^ N i‖ ≤ B i)
    (hsum : ∀ z, z ∈ sphere 0 r → HasSum (fun i => a i * z ^ N i) (f z)) (k : ℤ) :
    HasSum (fun i => if N i = k then a i else 0) (aLC r f k) := by
  simpa only [aLCsm hr] using
    hSaLC1 hr (fun i z => a i * z ^ N i) f k B hB
      (fun i => cOsmc hr (a i) (N i)) hbound hsum
theorem aLCms
    {ι : Type*} [Countable ι] {r : ℝ} (hr : 0 < r)
    (a : ι → ℂ) (N : ι → ℤ) (hN : Function.Injective N)
    (f : ℂ → ℂ) (B : ι → ℝ) (hB : Summable B)
    (hbound : ∀ i z, z ∈ sphere 0 r → ‖a i * z ^ N i‖ ≤ B i)
    (hsum : ∀ z, z ∈ sphere 0 r → HasSum (fun i => a i * z ^ N i) (f z)) (i₀ : ι) :
    aLC r f (N i₀) = a i₀ := by
  have h := hSaLC hr a N f B hB hbound hsum (N i₀)
  have hs : HasSum (fun i => if N i = N i₀ then a i else 0) (a i₀) := by
    have hz : ∀ i, i ≠ i₀ → (if N i = N i₀ then a i else 0) = 0 := by
      intro i hi
      exact if_neg (fun heq => hi (hN heq))
    simpa only [ite_true] using hasSum_single i₀ hz
  exact h.unique hs
theorem aLCms1
    {ι : Type*} [Countable ι] {r : ℝ} (hr : 0 < r)
    (a : ι → ℂ) (N : ι → ℤ) (f : ℂ → ℂ) (B : ι → ℝ) (hB : Summable B)
    (hbound : ∀ i z, z ∈ sphere 0 r → ‖a i * z ^ N i‖ ≤ B i)
    (hsum : ∀ z, z ∈ sphere 0 r → HasSum (fun i => a i * z ^ N i) (f z))
    (k : ℤ) (hk : k ∉ Set.range N) : aLC r f k = 0 := by
  have h := hSaLC hr a N f B hB hbound hsum k
  have hz : (fun i => if N i = k then a i else 0) = fun _ => (0 : ℂ) := by
    funext i
    exact if_neg (fun heq => hk ⟨i, heq⟩)
  rw [hz] at h
  exact h.unique hasSum_zero
end Nagata.W09
end
end OAI
end
section
namespace OAI
section
noncomputable section
open scoped BigOperators
open Module
namespace Nagata.Workers.W10
variable {R V I : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
  [Fintype I] [DecidableEq I]
theorem cMs (c : V →ₗ[R] (I → R)) (v : I → V)
    (hv : ∀ i, c (v i) = Pi.single i 1) : Function.Surjective c := by
  intro a
  refine ⟨∑ i, a i • v i, ?_⟩
  ext j
  simp [map_sum, hv, Pi.single_apply]
def cE1 (c : V →ₗ[R] (I → R)) (hc : Function.Injective c)
    (v : I → V) (hv : ∀ i, c (v i) = Pi.single i 1) : V ≃ₗ[R] (I → R) :=
  LinearEquiv.ofBijective c ⟨hc, cMs c v hv⟩
def bFC (c : V →ₗ[R] (I → R)) (hc : Function.Injective c)
    (v : I → V) (hv : ∀ i, c (v i) = Pi.single i 1) : Basis I R V :=
  (Pi.basisFun R I).map (cE1 c hc v hv).symm
end Nagata.Workers.W10
end
end
section
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.W08 Nagata.W09
def rCM {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (C : V →ₗ[ℂ] (ℤ → ℂ)) (U : ℝ) (n : ℤ) :
    V →ₗ[ℂ] (tI U n → ℂ) where
  toFun f K := C f K.val
  map_add' f g := by ext K; simp
  map_smul' a f := by ext K; simp
theorem rCMi {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (C : V →ₗ[ℂ] (ℤ → ℂ)) (hC : Function.Injective C)
    (τ γ : ℂ) (hτ : τ ≠ 0) (hγ : γ ≠ 0) (U : ℝ) {n : ℤ} (hn : 0 < n)
    (hrec : ∀ f k, C f (k + n) = γ⁻¹ * τ ^ k * C f k) :
    Function.Injective (rCM C U n) := by
  intro f g h
  apply hC
  apply lreot τ γ hτ hγ U hn
    (C f) (C g) (hrec f) (hrec g)
  intro K hK
  exact congrFun h ⟨K, hK⟩
end Nagata.Workers.W10
end
end
section
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.W09
variable {V : Type*} [AddCommMonoid V] [Module ℂ V]
def nRM (C : V →ₗ[ℂ] (ℤ → ℂ)) (U : ℝ) (n : ℤ)
    (a : tI U n → ℂ) : V →ₗ[ℂ] (tI U n → ℂ) where
  toFun f K := (a K)⁻¹ * C f K.val
  map_add' f g := by ext K; simp [mul_add]
  map_smul' b f := by ext K; simp [mul_left_comm]
theorem nRMi (C : V →ₗ[ℂ] (ℤ → ℂ))
    (U : ℝ) (n : ℤ) (a : tI U n → ℂ)
    (ha : ∀ K, a K ≠ 0)
    (hc : Function.Injective (rCM C U n)) :
    Function.Injective (nRM C U n a) := by
  intro f g h
  apply hc
  ext K
  have he := congrFun h K
  change (a K)⁻¹ * C f K.val = (a K)⁻¹ * C g K.val at he
  exact mul_left_cancel₀ (inv_ne_zero (ha K)) he
theorem nRMd (C : V →ₗ[ℂ] (ℤ → ℂ))
    (τ γ : ℂ) (U : ℝ) (n : ℤ) (a : tI U n → ℂ)
    (ha : ∀ K, a K ≠ 0) (theta : tI U n → V)
    (hcoeff : ∀ K k, C (theta K) k = sOC τ γ n K.val (a K) k)
    (K : tI U n) :
    nRM C U n a (theta K) = Pi.single K 1 := by
  classical
  ext L
  change (a L)⁻¹ * C (theta K) L.val = _
  rw [hcoeff]
  by_cases hLK : L = K
  · subst L
    simp [sOCi, ha]
  · have hz : sOC τ γ n K.val (a K) L.val = 0 := by
      by_contra hne
      have he := tIri L.property K.property
        (sOCr τ γ n K.val (a K) L.val hne)
      exact hLK (Subtype.ext he)
    simp [hz, hLK]
def bFSO (C : V →ₗ[ℂ] (ℤ → ℂ))
    (τ γ : ℂ) (U : ℝ) (n : ℤ) (a : tI U n → ℂ)
    (ha : ∀ K, a K ≠ 0)
    (hc : Function.Injective (rCM C U n))
    (theta : tI U n → V)
    (hcoeff : ∀ K k, C (theta K) k = sOC τ γ n K.val (a K) k) :
    Basis (tI U n) ℂ V :=
  bFC (nRM C U n a)
    (nRMi C U n a ha hc) theta
    (nRMd C τ γ U n a ha theta hcoeff)
end Nagata.Workers.W10
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
open scoped BigOperators
open Module
namespace Nagata.Workers.W10
variable {R A : Type*} [Semiring R] [Semiring A] [Module R A]
def bCP (u : ℕ) (S : ℕ → Submodule R A) :
    Submodule R (Polynomial A) where
  carrier := {F | (∀ j, u < j → F.coeff j = 0) ∧ ∀ j, F.coeff j ∈ S j}
  zero_mem' := by constructor <;> simp
  add_mem' := by
    intro F G hF hG
    constructor
    · intro j hj; simp [Polynomial.coeff_add, hF.1 j hj, hG.1 j hj]
    · intro j; simpa using (S j).add_mem (hF.2 j) (hG.2 j)
  smul_mem' := by
    intro a F hF
    constructor
    · intro j hj; simp [Polynomial.coeff_smul, hF.1 j hj]
    · intro j; simpa using (S j).smul_mem a (hF.2 j)
def bPC1 (u : ℕ) (S : ℕ → Submodule R A) :
    bCP u S →ₗ[R] ((j : Fin (u + 1)) → S j.val) where
  toFun F j := ⟨F.val.coeff j.val, F.property.2 j.val⟩
  map_add' F G := by ext j; simp
  map_smul' a F := by ext j; simp
theorem bPCi (u : ℕ) (S : ℕ → Submodule R A) :
    Function.Injective (bPC1 u S) := by
  intro F G h
  apply Subtype.ext
  apply Polynomial.ext
  intro j
  by_cases hj : j ≤ u
  · exact congrArg Subtype.val (congrFun h ⟨j, by omega⟩)
  · rw [F.property.1 j (by omega), G.property.1 j (by omega)]
def fCP (u : ℕ) (S : ℕ → Submodule R A)
    (a : (j : Fin (u + 1)) → S j.val) : Polynomial A :=
  ∑ j, Polynomial.monomial j.val (a j).val
@[simp] theorem fCPc (u : ℕ) (S : ℕ → Submodule R A)
    (a : (j : Fin (u + 1)) → S j.val) (j : Fin (u + 1)) :
    (fCP u S a).coeff j.val = (a j).val := by
  classical
  simp [fCP, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial, Fin.val_inj]
theorem fCPca (u : ℕ) (S : ℕ → Submodule R A)
    (a : (j : Fin (u + 1)) → S j.val) (k : ℕ) (hk : u < k) :
    (fCP u S a).coeff k = 0 := by
  classical
  rw [fCP, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro j hj
  apply Polynomial.coeff_monomial_of_ne
  omega
theorem bPCs (u : ℕ) (S : ℕ → Submodule R A) :
    Function.Surjective (bPC1 u S) := by
  intro a
  have hmem : fCP u S a ∈ bCP u S := by
    constructor
    · exact fCPca u S a
    · intro k
      by_cases hk : k ≤ u
      · have he := fCPc u S a ⟨k, by omega⟩
        rw [he]
        exact (a ⟨k, by omega⟩).property
      · rw [fCPca u S a k (by omega)]
        exact (S k).zero_mem
  refine ⟨⟨fCP u S a, hmem⟩, ?_⟩
  ext j
  exact fCPc u S a j
def bPE (u : ℕ) (S : ℕ → Submodule R A) :
    bCP u S ≃ₗ[R] ((j : Fin (u + 1)) → S j.val) :=
  LinearEquiv.ofBijective (bPC1 u S)
    ⟨bPCi u S, bPCs u S⟩
end Nagata.Workers.W10
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W07
def tE (n a p : ℝ) : ℝ := p * a + n * p * (p - 1) / 2
def tM (n a : ℝ) : ℝ := min a (n - a)
theorem tMp {n a : ℝ} (ha : 0 < a) (han : a < n) :
    0 < tM n a := by
  exact lt_min ha (sub_pos.mpr han)
theorem tEql (n a p : ℝ) :
    tM n a * |p| + n * |p| * (|p| - 1) / 2 ≤
      tE n a p := by
  by_cases hp : 0 ≤ p
  · rw [abs_of_nonneg hp]
    have h := mul_le_mul_of_nonneg_right (min_le_left a (n - a)) hp
    unfold tM tE
    nlinarith
  · have hp' : p ≤ 0 := le_of_lt (lt_of_not_ge hp)
    rw [abs_of_nonpos hp']
    have h := mul_le_mul_of_nonneg_right (min_le_right a (n - a))
      (neg_nonneg.mpr hp')
    unfold tM tE
    nlinarith
theorem tEil {n a : ℝ} (hn : 0 ≤ n) (p : ℤ) :
    tM n a * |(p : ℝ)| ≤ tE n a (p : ℝ) := by
  by_cases hp : p = 0
  · subst p
    simp [tE]
  · have habs : 1 ≤ |(p : ℝ)| := by
      rcases Int.cast_le_neg_one_or_one_le_cast_of_ne_zero (R := ℝ) hp with h | h
      · rw [abs_of_nonpos (by linarith : (p : ℝ) ≤ 0)]
        linarith
      · rw [abs_of_nonneg (by linarith : 0 ≤ (p : ℝ))]
        exact h
    have hquad : 0 ≤ n * |(p : ℝ)| * (|(p : ℝ)| - 1) / 2 :=
      div_nonneg (mul_nonneg (mul_nonneg hn (abs_nonneg _))
        (sub_nonneg.mpr habs)) (by norm_num)
    exact le_trans (by linarith) (tEql n a (p : ℝ))
end Nagata.W07
end
end
section
noncomputable section
namespace Nagata.W07
theorem lEcr (n K p : ℤ) :
    (Nagata.W08.lE n K p : ℝ) =
      (p : ℝ) * (K : ℝ) + (n : ℝ) * (p : ℝ) * ((p : ℝ) - 1) / 2 := by
  have ht : (2 : ℝ) * (Nagata.W08.tri p : ℝ) = (p : ℝ) * ((p : ℝ) - 1) := by
    exact_mod_cast Nagata.W08.tmt p
  have ht' : (Nagata.W08.tri p : ℝ) = (p : ℝ) * ((p : ℝ) - 1) / 2 := by
    linarith
  simp only [Nagata.W08.lE, Int.cast_add, Int.cast_mul, ht']
  ring
theorem nei (n K p : ℤ) (σ x₀ : ℝ) :
    -x₀ * (K : ℝ) + (-σ * (p : ℝ) + (Nagata.W08.lE n K p : ℝ)) +
      x₀ * ((K + n * p : ℤ) : ℝ) =
      tE (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ)) (p : ℝ) := by
  rw [lEcr]
  simp only [Int.cast_add, Int.cast_mul, tE]
  ring
end Nagata.W07
end
end
section
noncomputable section
namespace Nagata.W07
def nTT (n a K : ℝ) (ε : ℂ) (τ : ℝ) (p : ℤ) (x : ℂ) : ℂ :=
  ε ^ (-p) * ((τ ^ tE n a (p : ℝ) : ℝ) : ℂ) *
    Complex.exp (((K + n * (p : ℝ) : ℝ) : ℂ) * x)
def nTDT (n a K : ℝ) (ε : ℂ) (τ : ℝ)
    (c : ℕ) (p : ℤ) (x : ℂ) : ℂ :=
  (((K + n * (p : ℝ) : ℝ) : ℂ) ^ c) * nTT n a K ε τ p x
@[simp] theorem nTDTz
    (n a K : ℝ) (ε : ℂ) (τ : ℝ) (p : ℤ) (x : ℂ) :
    nTDT n a K ε τ 0 p x =
      nTT n a K ε τ p x := by
  simp [nTDT]
theorem nAr (p : ℤ) : (p.natAbs : ℝ) = |(p : ℝ)| := by
  rw [Nat.cast_natAbs, Int.cast_abs]
theorem tplg {n a τ : ℝ} (hn : 0 ≤ n)
    (hτ : 0 < τ) (hτone : τ ≤ 1) (p : ℤ) :
    τ ^ tE n a (p : ℝ) ≤ (τ ^ tM n a) ^ p.natAbs := by
  have h := Real.rpow_le_rpow_of_exponent_ge hτ hτone
    (tEil (a := a) hn p)
  calc
    _ ≤ τ ^ (tM n a * |(p : ℝ)|) := h
    _ = (τ ^ tM n a) ^ p.natAbs := by
      rw [← nAr p, Real.rpow_mul_natCast hτ.le]
theorem tfl {n : ℝ} (hn : 0 ≤ n) (K : ℝ) (p : ℤ) :
    |K + n * (p : ℝ)| ≤ |K| + n * (p.natAbs : ℝ) := by
  calc
    _ ≤ |K| + |n * (p : ℝ)| := abs_add_le _ _
    _ = _ := by rw [abs_mul, abs_of_nonneg hn, nAr]
end Nagata.W07
end
end
section
noncomputable section
namespace Nagata.W07
theorem crz {τ : ℝ} (hτ : 0 ≤ τ) (s : ℝ) (p : ℤ) :
    (((τ ^ s : ℝ) : ℂ) ^ p) = ((τ ^ (s * (p : ℝ)) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_zpow, ← Real.rpow_mul_intCast hτ]
def nLC (τ σ x₀ : ℝ) (ε : ℂ) (n K p : ℤ) : ℂ :=
  ((τ ^ (-x₀ * (K : ℝ)) : ℝ) : ℂ) * ε ^ (-p) *
    ((τ ^ (-σ * (p : ℝ) + (Nagata.W08.lE n K p : ℝ)) : ℝ) : ℂ)
theorem nLCeo {τ : ℝ} (hτ : 0 < τ)
    (σ x₀ : ℝ) (ε : ℂ) (n K p : ℤ) :
    nLC τ σ x₀ ε n K p =
      Nagata.W08.oV (τ : ℂ) (ε * ((τ ^ σ : ℝ) : ℂ)) n K
        ((τ ^ (-x₀ * (K : ℝ)) : ℝ) : ℂ) p := by
  unfold Nagata.W08.oV
  rw [mul_zpow, crz hτ.le, ← Complex.ofReal_zpow, ← Real.rpow_intCast]
  simp only [nLC, Real.rpow_add hτ, Complex.ofReal_mul,
    Int.cast_neg, mul_neg, neg_mul]
  ring
theorem nLCe {τ : ℝ} (hτ : 0 < τ)
    (σ x₀ : ℝ) (ε x : ℂ) (n K p : ℤ) :
    nLC τ σ x₀ ε n K p *
        (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) ^ (K + n * p) =
      nTT (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ))
        (K : ℝ) ε τ p x := by
  have hscalar : τ ^ (-x₀ * (K : ℝ)) *
      τ ^ (-σ * (p : ℝ) + (Nagata.W08.lE n K p : ℝ)) *
        τ ^ (x₀ * ((K + n * p : ℤ) : ℝ)) =
      τ ^ tE (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ)) (p : ℝ) := by
    rw [← Real.rpow_add hτ, ← Real.rpow_add hτ, nei]
  calc
    _ = ε ^ (-p) *
        ((τ ^ (-x₀ * (K : ℝ)) *
          τ ^ (-σ * (p : ℝ) + (Nagata.W08.lE n K p : ℝ)) *
            τ ^ (x₀ * ((K + n * p : ℤ) : ℝ)) : ℝ) : ℂ) *
          Complex.exp (((K + n * p : ℤ) : ℂ) * x) := by
      simp only [nLC, mul_zpow, crz hτ.le,
        ← Complex.exp_int_mul, Complex.ofReal_mul]
      ring
    _ = _ := by
      rw [hscalar]
      simp only [nTT, Int.cast_add, Int.cast_mul, Complex.ofReal_add,
        Complex.ofReal_mul, Complex.ofReal_intCast]
theorem nTTs {τ : ℝ} (hτ : 0 < τ)
    (n a K x₀ : ℝ) (ε x : ℂ) (p : ℤ) :
    ((τ ^ (-x₀ * K) : ℝ) : ℂ) *
        nTT n a K ε τ p (((x₀ * Real.log τ : ℝ) : ℂ) + x) =
      nTT n (a + x₀ * n) K ε τ p x := by
  have hexp : Complex.exp (((K + n * (p : ℝ) : ℝ) : ℂ) *
      (((x₀ * Real.log τ : ℝ) : ℂ) + x)) =
      ((τ ^ (x₀ * (K + n * (p : ℝ))) : ℝ) : ℂ) *
        Complex.exp (((K + n * (p : ℝ) : ℝ) : ℂ) * x) := by
    rw [mul_add, Complex.exp_add, Real.rpow_def_of_pos hτ, Complex.ofReal_exp]
    congr 2
    push_cast
    ring
  have hpowers : τ ^ (-x₀ * K) * τ ^ tE n a (p : ℝ) *
      τ ^ (x₀ * (K + n * (p : ℝ))) =
      τ ^ tE n (a + x₀ * n) (p : ℝ) := by
    rw [← Real.rpow_add hτ, ← Real.rpow_add hτ]
    congr 1
    unfold tE
    ring
  calc
    _ = ε ^ (-p) *
        ((τ ^ (-x₀ * K) * τ ^ tE n a (p : ℝ) *
          τ ^ (x₀ * (K + n * (p : ℝ))) : ℝ) : ℂ) *
          Complex.exp (((K + n * (p : ℝ) : ℝ) : ℂ) * x) := by
      unfold nTT
      rw [hexp]
      simp only [Complex.ofReal_mul]
      ring
    _ = _ := by rw [hpowers]; rfl
theorem nsp {τ : ℝ} (hτ : 0 < τ) (x₀ : ℝ) (K : ℤ) :
    0 < τ ^ (-x₀ * (K : ℝ)) := Real.rpow_pos_of_pos hτ _
theorem nsnz {τ : ℝ} (hτ : 0 < τ) (x₀ : ℝ) (K : ℤ) :
    ((τ ^ (-x₀ * (K : ℝ)) : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (nsp hτ x₀ K).ne'
end Nagata.W07
end
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Nagata.W22
section
open Filter Topology
open Nagata.W07
def nTS1 (n a K : ℝ) (ε : ℂ) (τ : ℝ) (x : ℂ) : ℂ :=
  ∑' p : ℤ, nTT n a K ε τ p x
def nTDS (n a K : ℝ) (ε : ℂ) (τ : ℝ)
    (c : ℕ) (x : ℂ) : ℂ :=
  ∑' p : ℤ, nTDT n a K ε τ c p x
@[simp] theorem nTDSz (n a K : ℝ) (ε : ℂ)
    (τ : ℝ) (x : ℂ) :
    nTDS n a K ε τ 0 x = nTS1 n a K ε τ x := by
  simp [nTDS, nTS1]
end
open Filter Topology
end Nagata.W22
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W02
def gC (c C : ℝ) : ℝ := (C + 1) ^ 2 / (4 * c)
theorem gel1 (c C t : ℝ) (hc : 0 < c) :
    -c * t ^ 2 + C * t ≤ gC c C - t := by
  have hid : c * gC c C = (C + 1) ^ 2 / 4 := by
    unfold gC
    field_simp
  apply le_of_mul_le_mul_left (a := c) _ hc
  nlinarith [sq_nonneg (c * t - (C + 1) / 2)]
theorem gel (c C t : ℝ) (hc : 0 < c) :
    Real.exp (-c * t ^ 2 + C * t) ≤
      Real.exp (gC c C) * Real.exp (-t) := by
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by simpa [sub_eq_add_neg] using gel1 c C t hc)
theorem spmg (c C : ℝ) (N : ℕ) (hc : 0 < c) :
    Summable (fun t : ℕ => (t : ℝ) ^ N * Real.exp (-c * (t : ℝ) ^ 2 + C * t)) := by
  have hsum := (Real.summable_pow_mul_exp_neg_nat_mul N (show (0 : ℝ) < 1 by norm_num)).mul_left
    (Real.exp (gC c C))
  apply hsum.of_nonneg_of_le
  · intro t
    positivity
  · intro t
    have hb := mul_le_mul_of_nonneg_left (gel c C (t : ℝ) hc)
      (pow_nonneg (Nat.cast_nonneg t) N)
    simpa only [one_mul, neg_mul, mul_neg_one, neg_one_mul, mul_comm, mul_left_comm, mul_assoc] using hb
end Nagata.W02
end
end
section
noncomputable section
namespace Nagata.W02
open Nagata.W07
def tGD (n τ : ℝ) : ℝ := -Real.log τ * n / 2
def tGL (n a τ R : ℝ) (ε : ℂ) : ℝ :=
  Real.log τ * (tM n a - n / 2) + n * R + |Real.log ‖ε‖|
def tGM (n a K τ R : ℝ) (ε : ℂ) (N : ℕ) (p : ℤ) : ℝ :=
  Real.exp (|K| * R) * (|K| + n) ^ N *
    Real.exp (-tGD n τ * (p.natAbs : ℝ) ^ 2 +
      (tGL n a τ R ε + N) * (p.natAbs : ℝ))
theorem tGDp {n τ : ℝ} (hn : 0 < n) (hτ : 0 < τ) (hτ1 : τ < 1) :
    0 < tGD n τ := by
  have hl : Real.log τ < 0 := Real.log_neg hτ hτ1
  exact div_pos (mul_pos (neg_pos.mpr hl) hn) (by norm_num)
theorem nzlen (ε : ℂ) (hε : ε ≠ 0) (p : ℤ) :
    ‖ε ^ (-p)‖ ≤ Real.exp (|Real.log ‖ε‖| * (p.natAbs : ℝ)) := by
  rw [norm_zpow, ← Real.rpow_intCast, Real.rpow_def_of_pos (norm_pos_iff.mpr hε)]
  apply Real.exp_le_exp.mpr
  rw [Int.cast_neg, nAr]
  calc
    Real.log ‖ε‖ * -(p : ℝ) ≤ |Real.log ‖ε‖ * -(p : ℝ)| := le_abs_self _
    _ = |Real.log ‖ε‖| * |(p : ℝ)| := by rw [abs_mul, abs_neg]
theorem afpl (A n t : ℝ) (N : ℕ)
    (hA : 0 ≤ A) (hn : 0 ≤ n) (ht : 0 ≤ t) :
    (A + n * t) ^ N ≤ (A + n) ^ N * Real.exp ((N : ℝ) * t) := by
  have hbase : A + n * t ≤ (A + n) * Real.exp t := by
    calc
      A + n * t ≤ (A + n) * (t + 1) := by nlinarith
      _ ≤ (A + n) * Real.exp t :=
        mul_le_mul_of_nonneg_left (Real.add_one_le_exp t) (add_nonneg hA hn)
  have hp := pow_le_pow_left₀ (add_nonneg hA (mul_nonneg hn ht)) hbase N
  simpa only [mul_pow, ← Real.exp_nat_mul] using hp
theorem nnTDT
    {n a K τ R : ℝ} {ε x : ℂ} (hn : 0 < n) (hτ : 0 < τ) (hτ1 : τ < 1)
    (hε : ε ≠ 0) (hR : 0 ≤ R) (hx : ‖x‖ ≤ R) (N : ℕ) (p : ℤ) :
    ‖nTDT n a K ε τ N p x‖ ≤
      tGM n a K τ R ε N p := by
  let t : ℝ := p.natAbs
  let A : ℝ := |K| + n * t
  let Q : ℝ := tM n a * t + n * t * (t - 1) / 2
  have ht : 0 ≤ t := Nat.cast_nonneg _
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hfreq : |K + n * (p : ℝ)| ≤ A := tfl hn.le K p
  have hεbound := nzlen ε hε p
  have hlog : Real.log τ < 0 := Real.log_neg hτ hτ1
  have hquad : Q ≤ tE n a (p : ℝ) := by
    simpa only [Q, t, nAr] using tEql n a (p : ℝ)
  have hpower : τ ^ tE n a (p : ℝ) ≤ Real.exp (Real.log τ * Q) := by
    rw [Real.rpow_def_of_pos hτ]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hquad hlog.le)
  have hexp : ‖Complex.exp (((K + n * (p : ℝ) : ℝ) : ℂ) * x)‖ ≤ Real.exp (A * R) := by
    apply (Complex.norm_exp_le_exp_norm _).trans
    apply Real.exp_le_exp.mpr
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left hx (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hfreq hR)
  have hfreqpow := pow_le_pow_left₀ (abs_nonneg _) hfreq N
  have hnorm : ‖nTDT n a K ε τ N p x‖ =
      |K + n * (p : ℝ)| ^ N * ‖ε ^ (-p)‖ * τ ^ tE n a (p : ℝ) *
        ‖Complex.exp (((K + n * (p : ℝ) : ℝ) : ℂ) * x)‖ := by
    simp only [nTDT, nTT, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hτ.le _), mul_assoc]
  have hmain : ‖nTDT n a K ε τ N p x‖ ≤
      A ^ N * Real.exp (|Real.log ‖ε‖| * t) * Real.exp (Real.log τ * Q) *
        Real.exp (A * R) := by
    rw [hnorm]
    gcongr
  have hfreq2 := afpl |K| n t N (abs_nonneg K) hn.le ht
  calc
    _ ≤ A ^ N * Real.exp (|Real.log ‖ε‖| * t) * Real.exp (Real.log τ * Q) *
        Real.exp (A * R) := hmain
    _ ≤ ((|K| + n) ^ N * Real.exp ((N : ℝ) * t)) *
        Real.exp (|Real.log ‖ε‖| * t) * Real.exp (Real.log τ * Q) *
        Real.exp (A * R) := by gcongr
    _ = tGM n a K τ R ε N p := by
      unfold tGM tGD tGL
      rw [mul_comm (Real.exp (|K| * R)) ((|K| + n) ^ N)]
      simp only [mul_assoc, ← Real.exp_add]
      congr 2
      dsimp [Q, A, t]
      ring
end Nagata.W02
end
end
section
noncomputable section
open Filter Topology
namespace Nagata.W02
open Nagata.W07 Nagata.W22
theorem snA {f : ℕ → ℝ} (hf : Summable f) :
    Summable (fun p : ℤ => f p.natAbs) := by
  have hp : Summable (fun t : ℕ => f (t : ℤ).natAbs) := by simpa using hf
  have hm : Summable (fun t : ℕ => f (-(t + 1 : ℤ)).natAbs) := by
    have hh := (summable_nat_add_iff (f := f) 1).mpr hf
    simpa only [Int.natAbs_neg, ← Nat.cast_one (R := ℤ), ← Nat.cast_add,
      Int.natAbs_natCast] using hh
  exact hp.of_nat_of_neg_add_one hm
theorem stGM {n τ : ℝ} (hn : 0 < n)
    (hτ : 0 < τ) (hτ1 : τ < 1) (a K R : ℝ) (ε : ℂ) (N : ℕ) :
    Summable (tGM n a K τ R ε N) := by
  have hc := tGDp hn hτ hτ1
  have hs : Summable (fun t : ℕ => Real.exp (-tGD n τ * (t : ℝ) ^ 2 +
      (tGL n a τ R ε + N) * (t : ℝ))) := by
    simpa using spmg (tGD n τ)
      (tGL n a τ R ε + N) 0 hc
  exact (snA hs).mul_left (Real.exp (|K| * R) * (|K| + n) ^ N)
theorem tUOnT
    {n a K τ R : ℝ} {ε : ℂ} (hn : 0 < n) (hτ : 0 < τ) (hτ1 : τ < 1)
    (hε : ε ≠ 0) (hR : 0 ≤ R) (N : ℕ) :
    TendstoUniformlyOn
      (fun S : Finset ℤ => fun x => ∑ p ∈ S, nTDT n a K ε τ N p x)
      (nTDS n a K ε τ N) atTop {x : ℂ | ‖x‖ ≤ R} := by
  apply tendstoUniformlyOn_tsum (stGM hn hτ hτ1 a K R ε N)
  intro p x hx
  exact nnTDT hn hτ hτ1 hε hR hx N p
theorem dnTDS
    {n a K τ : ℝ} {ε : ℂ} (hn : 0 < n) (hτ : 0 < τ) (hτ1 : τ < 1)
    (hε : ε ≠ 0) (N : ℕ) :
    Differentiable ℂ (nTDS n a K ε τ N) := by
  intro x
  let R : ℝ := ‖x‖ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hu := tUOnT
    (a := a) (K := K) hn hτ hτ1 hε hR N
  have hlocal := (hu.mono (show {z : ℂ | ‖z‖ < R} ⊆ {z : ℂ | ‖z‖ ≤ R}
    from fun z hz => (show ‖z‖ < R from hz).le)).tendstoLocallyUniformlyOn
  have hfinite : ∀ S : Finset ℤ, DifferentiableOn ℂ
      (fun z => ∑ p ∈ S, nTDT n a K ε τ N p z)
      {z : ℂ | ‖z‖ < R} := by
    intro S
    apply DifferentiableOn.fun_sum
    intro p hp
    have hd : Differentiable ℂ (nTDT n a K ε τ N p) := by
      unfold nTDT nTT
      exact (differentiable_const _).mul
        ((differentiable_const _).mul ((differentiable_const _).mul differentiable_id).cexp)
    exact hd.differentiableOn
  have hU : IsOpen {z : ℂ | ‖z‖ < R} := isOpen_lt continuous_norm continuous_const
  have hdiff := hlocal.differentiableOn (Eventually.of_forall hfinite) hU
  exact hdiff.differentiableAt (hU.mem_nhds (by dsimp [R]; simp))
theorem dnTSa
    {n a K τ : ℝ} {ε : ℂ} (hn : 0 < n) (hτ : 0 < τ) (hτ1 : τ < 1)
    (hε : ε ≠ 0) : Differentiable ℂ (nTS1 n a K ε τ) := by
  have he : nTDS n a K ε τ 0 = nTS1 n a K ε τ := by
    funext x
    exact nTDSz n a K ε τ x
  rw [← he]
  exact dnTDS (a := a) (K := K) hn hτ hτ1 hε 0
end Nagata.W02
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W08
open Nagata.W07
theorem nTTiP (n K k : ℤ) (a : ℝ) (ε : ℂ) (τ : ℝ)
    (p : ℤ) (x : ℂ) :
    nTT (n : ℝ) a (K : ℝ) ε τ p
        (x + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) =
      nTT (n : ℝ) a (K : ℝ) ε τ p x := by
  have hfreq : (((K : ℝ) + (n : ℝ) * (p : ℝ) : ℝ) : ℂ) =
      ((K + n * p : ℤ) : ℂ) := by push_cast; rfl
  unfold nTT
  rw [hfreq, mul_add, Complex.exp_add]
  have hexp : Complex.exp (((K + n * p : ℤ) : ℂ) *
      ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))) = 1 := by
    rw [← mul_assoc, ← Int.cast_mul]
    exact Complex.exp_int_mul_two_pi_mul_I ((K + n * p) * k)
  rw [hexp, mul_one]
theorem nTSiP (n K k : ℤ) (a : ℝ) (ε : ℂ) (τ : ℝ)
    (x : ℂ) :
    (∑' p : ℤ, nTT (n : ℝ) a (K : ℝ) ε τ p
      (x + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))) =
    (∑' p : ℤ, nTT (n : ℝ) a (K : ℝ) ε τ p x) :=
  tsum_congr fun p ↦ nTTiP n K k a ε τ p x
theorem nTTes (n a K : ℝ) {ε : ℂ} (hε : ε ≠ 0)
    {τ : ℝ} (hτ : 0 < τ) (p : ℤ) (x : ℂ) :
    nTT n a K ε τ p x =
      Complex.exp (((-p : ℤ) : ℂ) * Complex.log ε +
        ((Real.log τ * tE n a (p : ℝ) : ℝ) : ℂ) +
        (((K + n * (p : ℝ) : ℝ) : ℂ) * x)) := by
  have heps : ε ^ (-p) = Complex.exp (((-p : ℤ) : ℂ) * Complex.log ε) := by
    rw [Complex.exp_int_mul, Complex.exp_log hε]
  unfold nTT
  rw [heps, Real.rpow_def_of_pos hτ, Complex.ofReal_exp,
    ← Complex.exp_add, ← Complex.exp_add]
theorem nTTrS (n a K : ℝ) {ε : ℂ} (hε : ε ≠ 0)
    {τ : ℝ} (hτ : 0 < τ) (p : ℤ) (x : ℂ) :
    nTT n a K ε τ p (x + (Real.log τ : ℂ)) =
      ((ε * ((τ ^ (K - a) : ℝ) : ℂ)) * Complex.exp (-(n : ℂ) * x)) *
        nTT n a K ε τ (p + 1) x := by
  have hscalar : ε * ((τ ^ (K - a) : ℝ) : ℂ) =
      Complex.exp (Complex.log ε + ((Real.log τ * (K - a) : ℝ) : ℂ)) := by
    rw [Complex.exp_add, Complex.exp_log hε, Real.rpow_def_of_pos hτ, Complex.ofReal_exp]
  rw [nTTes n a K hε hτ,
    nTTes n a K hε hτ, hscalar,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  unfold tE
  push_cast
  ring
theorem nTSrS (n a K : ℝ) {ε : ℂ} (hε : ε ≠ 0)
    {τ : ℝ} (hτ : 0 < τ) (x : ℂ) :
    (∑' p : ℤ, nTT n a K ε τ p (x + (Real.log τ : ℂ))) =
      (ε * ((τ ^ (K - a) : ℝ) : ℂ)) * Complex.exp (-(n : ℂ) * x) *
        (∑' p : ℤ, nTT n a K ε τ p x) := by
  simp_rw [nTTrS n a K hε hτ]
  rw [tsum_mul_left]
  congr 1
  exact (Equiv.addRight (1 : ℤ)).tsum_eq (fun p : ℤ ↦ nTT n a K ε τ p x)
end Nagata.W08
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W21
abbrev MLC (R : Type*) [CommMonoid R] := Rˣ × R
def mS1 {R : Type*} [CommMonoid R] (τ γ : Rˣ) (n : ℤ) :
    Equiv.Perm (MLC R) where
  toFun p := (τ * p.1, (γ * p.1 ^ (-n)) • p.2)
  invFun p := (τ⁻¹ * p.1, (γ * (τ⁻¹ * p.1) ^ (-n))⁻¹ • p.2)
  left_inv := by
    rintro ⟨z, t⟩
    change (τ⁻¹ * (τ * z), (γ * (τ⁻¹ * (τ * z)) ^ (-n))⁻¹ •
      ((γ * z ^ (-n)) • t)) = (z, t)
    rw [inv_mul_cancel_left, inv_smul_smul]
  right_inv := by
    rintro ⟨z, t⟩
    change (τ * (τ⁻¹ * z), (γ * (τ⁻¹ * z) ^ (-n)) •
      ((γ * (τ⁻¹ * z) ^ (-n))⁻¹ • t)) = (z, t)
    rw [mul_inv_cancel_left, smul_inv_smul]
def mI {R : Type*} [CommMonoid R] (τ γ : Rˣ) (n k : ℤ) :
    Equiv.Perm (MLC R) := mS1 τ γ n ^ k
@[simp] theorem mIz {R : Type*} [CommMonoid R]
    (τ γ : Rˣ) (n : ℤ) (p : MLC R) :
    mI τ γ n 0 p = p := by simp [mI]
theorem mIa {R : Type*} [CommMonoid R]
    (τ γ : Rˣ) (n k l : ℤ) (p : MLC R) :
    mI τ γ n (k + l) p =
      mI τ γ n k (mI τ γ n l p) := by
  simp only [mI, zpow_add, Equiv.Perm.mul_apply]
def mOS {R : Type*} [CommMonoid R] (τ γ : Rˣ) (n : ℤ) :
    Setoid (MLC R) where
  r p q := ∃ k : ℤ, mI τ γ n k p = q
  iseqv := {
    refl := fun p ↦ ⟨0, mIz τ γ n p⟩
    symm := by
      intro p q h
      obtain ⟨k, hk⟩ := h
      refine ⟨-k, ?_⟩
      calc
        mI τ γ n (-k) q =
            mI τ γ n (-k) (mI τ γ n k p) := by rw [hk]
        _ = mI τ γ n (-k + k) p :=
          (mIa τ γ n (-k) k p).symm
        _ = p := by rw [Int.add_left_neg, mIz]
    trans := by
      intro p q r hp hq
      obtain ⟨k, hk⟩ := hp
      obtain ⟨l, hl⟩ := hq
      refine ⟨l + k, ?_⟩
      rw [mIa, hk, hl] }
def MQ {R : Type*} [CommMonoid R] (τ γ : Rˣ) (n : ℤ) : Type _ :=
  Quotient (mOS τ γ n)
instance {R : Type*} [CommMonoid R] (τ γ : Rˣ) (n : ℤ) :
    Nonempty (MQ τ γ n) :=
  ⟨Quotient.mk _ (1, 1)⟩
end Nagata.W21
end
section
namespace Nagata.W21
def tOS {G : Type*} [CommGroup G] (τ : G) : Setoid G where
  r z z' := ∃ k : ℤ, τ ^ k * z = z'
  iseqv := {
    refl := fun z ↦ ⟨0, by rw [zpow_zero, one_mul]⟩
    symm := by
      intro z z' h
      obtain ⟨k, hk⟩ := h
      refine ⟨-k, ?_⟩
      rw [← hk, ← mul_assoc, ← zpow_add, Int.add_left_neg, zpow_zero, one_mul]
    trans := by
      intro z z' z'' h h'
      obtain ⟨k, hk⟩ := h
      obtain ⟨l, hl⟩ := h'
      exact ⟨l + k, by rw [zpow_add, mul_assoc, hk, hl]⟩ }
def TP1 {G : Type*} [CommGroup G] (τ : G) : Type _ :=
  Quotient (tOS τ)
def tPM {G : Type*} [CommGroup G] (τ z : G) : TP1 τ :=
  Quotient.mk _ z
instance {G : Type*} [CommGroup G] (τ : G) : Nonempty (TP1 τ) :=
  ⟨tPM τ 1⟩
theorem tPMei {G : Type*} [CommGroup G] (τ z z' : G) :
    tPM τ z = tPM τ z' ↔ ∃ k : ℤ, τ ^ k * z = z' := by
  constructor
  · exact Quotient.exact
  · intro h
    exact Quotient.sound (s := tOS τ) h
theorem tOSic {R : Type*} [CommGroupWithZero R] (τ z z' : Rˣ) :
    tOS τ z z' ↔ ∃ k : ℤ, (z' : R) = (τ : R) ^ k * (z : R) := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    simpa only [Units.val_mul, Units.val_zpow_eq_zpow_val] using
      (congrArg (fun u : Rˣ ↦ (u : R)) hk).symm
  · rintro ⟨k, hk⟩
    refine ⟨k, Units.ext ?_⟩
    simpa only [Units.val_mul, Units.val_zpow_eq_zpow_val] using hk.symm
end Nagata.W21
end
section
namespace Nagata.W21
instance torusPointTopologicalSpace {G : Type*} [CommGroup G] [TopologicalSpace G]
    (τ : G) : TopologicalSpace (TP1 τ) :=
  inferInstanceAs (TopologicalSpace (Quotient (tOS τ)))
instance multiplierQuotientTopologicalSpace {R : Type*} [CommMonoid R]
    [TopologicalSpace R] [TopologicalSpace Rˣ] (τ γ : Rˣ) (n : ℤ) :
    TopologicalSpace (MQ τ γ n) :=
  inferInstanceAs (TopologicalSpace (Quotient (mOS τ γ n)))
end Nagata.W21
end
section
namespace Nagata.W21
section TopologicalAction
variable {R : Type*} [CommMonoid R] [TopologicalSpace R] [TopologicalSpace Rˣ]
  [IsTopologicalGroup Rˣ] [ContinuousSMul Rˣ R]
 theorem cmS (τ γ : Rˣ) (n : ℤ) :
    Continuous (mS1 τ γ n) := by
  change Continuous (fun p : MLC R ↦
    (τ * p.1, (γ * p.1 ^ (-n)) • p.2))
  exact (continuous_const.mul continuous_fst).prodMk
    ((continuous_const.mul (continuous_fst.zpow (-n))).smul continuous_snd)
 theorem cmSi (τ γ : Rˣ) (n : ℤ) :
    Continuous ((mS1 τ γ n)⁻¹ : Equiv.Perm (MLC R)) := by
  change Continuous (fun p : MLC R ↦
    (τ⁻¹ * p.1, (γ * (τ⁻¹ * p.1) ^ (-n))⁻¹ • p.2))
  exact (continuous_const.mul continuous_fst).prodMk
    ((continuous_const.mul ((continuous_const.mul continuous_fst).zpow (-n))).inv.smul
      continuous_snd)
end TopologicalAction
end Nagata.W21
end
end OAI
end
section
namespace OAI
section
namespace Nagata.LD
open Filter Topology
theorem eaqas {f P : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hP : AnalyticAt ℂ P z₀)
    (hP0 : P z₀ = 0) (hP' : deriv P z₀ ≠ 0) (k : ℕ)
    (horder : (k : ℕ∞) ≤ analyticOrderAt f z₀) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧
      ∀ᶠ z in 𝓝 z₀, f z = P z ^ k * g z := by
  have hPo : analyticOrderAt P z₀ = (1 : ℕ) :=
    hP.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hP0 hP'
  obtain ⟨u, hu, hu0, hPu⟩ := hP.analyticOrderAt_eq_natCast.mp hPo
  obtain ⟨v, hv, hfv⟩ := (natCast_le_analyticOrderAt hf).mp horder
  refine ⟨fun z => v z / u z ^ k, hv.div (hu.pow k) (pow_ne_zero k hu0), ?_⟩
  have hune : ∀ᶠ z in 𝓝 z₀, u z ≠ 0 := hu.continuousAt.eventually_ne hu0
  filter_upwards [hPu, hfv, hune] with z hPu hfv hu
  simp only [pow_one, smul_eq_mul] at hPu hfv
  rw [hPu, hfv, mul_pow]
  field_simp
theorem aqan {f P : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hP : AnalyticAt ℂ P z₀)
    (hP0 : P z₀ ≠ 0) (k : ℕ) :
    AnalyticAt ℂ (fun z => f z / P z ^ k) z₀ :=
  hf.div (hP.pow k) (pow_ne_zero k hP0)
theorem eaq1 {f P : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hP : AnalyticAt ℂ P z₀) (k : ℕ)
    (hzero : P z₀ = 0 → deriv P z₀ ≠ 0 ∧
      (k : ℕ∞) ≤ analyticOrderAt f z₀) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧
      ∀ᶠ z in 𝓝 z₀, f z = P z ^ k * g z := by
  by_cases hP0 : P z₀ = 0
  · exact eaqas hf hP hP0 (hzero hP0).1 k
      (hzero hP0).2
  · refine ⟨fun z => f z / P z ^ k, aqan hf hP hP0 k, ?_⟩
    have hPne : ∀ᶠ z in 𝓝 z₀, P z ≠ 0 := hP.continuousAt.eventually_ne hP0
    filter_upwards [hPne] with z hz
    field_simp
end Nagata.LD
end
section
namespace Nagata.LD
open Filter Topology
theorem aqgu {f P g h : ℂ → ℂ} {z₀ : ℂ} (k : ℕ)
    (hP : AnalyticAt ℂ P z₀) (hPfin : analyticOrderAt P z₀ ≠ ⊤)
    (hg : AnalyticAt ℂ g z₀) (hh : AnalyticAt ℂ h z₀)
    (hfg : ∀ᶠ z in 𝓝 z₀, f z = P z ^ k * g z)
    (hfh : ∀ᶠ z in 𝓝 z₀, f z = P z ^ k * h z) :
    g =ᶠ[𝓝 z₀] h := by
  have hPn : ∀ᶠ z in 𝓝[≠] z₀, P z ≠ 0 :=
    hP.eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (fun hz => hPfin (analyticOrderAt_eq_top.mpr hz))
  have heq : g =ᶠ[𝓝[≠] z₀] h := by
    filter_upwards [hPn, hfg.filter_mono nhdsWithin_le_nhds,
      hfh.filter_mono nhdsWithin_le_nhds] with z hz hfg hfh
    exact mul_left_cancel₀ (pow_ne_zero k hz) (hfg.symm.trans hfh)
  exact (hg.frequently_eq_iff_eventually_eq hh).mp heq.frequently
theorem ceaoe {P g h : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ}
    (hU : IsOpen U) (hz₀ : z₀ ∈ U) (hP : AnalyticAt ℂ P z₀)
    (hPfin : analyticOrderAt P z₀ ≠ ⊤) (hg : ContinuousAt g z₀)
    (hh : ContinuousAt h z₀)
    (heq : ∀ z ∈ U, P z ≠ 0 → g z = h z) : g z₀ = h z₀ := by
  have hPn : ∀ᶠ z in 𝓝[≠] z₀, P z ≠ 0 :=
    hP.eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (fun hz => hPfin (analyticOrderAt_eq_top.mpr hz))
  have hlocal : g =ᶠ[𝓝[≠] z₀] h := by
    filter_upwards [hPn, (show ∀ᶠ z in 𝓝 z₀, z ∈ U from hU.mem_nhds hz₀).filter_mono nhdsWithin_le_nhds]
      with z hz hzu
    exact heq z hzu hz
  exact tendsto_nhds_unique_of_eventuallyEq
    (hg.tendsto.mono_left nhdsWithin_le_nhds)
    (hh.tendsto.mono_left nhdsWithin_le_nhds) hlocal
theorem mpio {P f g : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (k : ℕ) (hP : AnalyticOnNhd ℂ P U)
    (hPfin : ∀ z ∈ U, analyticOrderAt P z ≠ ⊤)
    (hf : ∀ z ∈ U, ContinuousAt f z) (hg : ∀ z ∈ U, ContinuousAt g z)
    (hmul : ∀ z ∈ U, P z ^ k * f z = P z ^ k * g z) :
    Set.EqOn f g U := by
  intro z hz
  apply ceaoe hU hz (hP z hz) (hPfin z hz)
    (hf z hz) (hg z hz)
  intro w hw hPw
  exact mul_left_cancel₀ (pow_ne_zero k hPw) (hmul w hw)
theorem gaq {f P : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (k : ℕ) (hP : AnalyticOnNhd ℂ P U)
    (hPfin : ∀ z ∈ U, analyticOrderAt P z ≠ ⊤)
    (hlocal : ∀ z ∈ U, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧
      ∀ᶠ w in 𝓝 z, f w = P w ^ k * g w) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G U ∧
      (∀ z ∈ U, f z = P z ^ k * G z) ∧ (∀ z ∉ U, G z = 0) := by
  classical
  choose g hg hfg using hlocal
  let G : ℂ → ℂ := fun z => if hz : z ∈ U then g z hz z else 0
  refine ⟨G, ?_, ?_, ?_⟩
  · intro z hz
    have heq : G =ᶠ[𝓝 z] g z hz := by
      filter_upwards [hU.mem_nhds hz, (hg z hz).eventually_analyticAt,
        (hfg z hz).eventually_nhds] with w hw hgw hfw
      have huniq := aqgu k (hP w hw) (hPfin w hw)
        hgw (hg w hw) hfw (hfg w hw)
      simp only [G, dif_pos hw]
      exact huniq.self_of_nhds.symm
    exact (hg z hz).congr heq.symm
  · intro z hz
    simpa only [G, dif_pos hz] using (hfg z hz).self_of_nhds
  · intro z hz
    simp only [G, dif_neg hz]
theorem egaq {f P : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U) (hP : AnalyticOnNhd ℂ P U)
    (k : ℕ) (hzero : ∀ z ∈ U, P z = 0 → deriv P z ≠ 0 ∧
      (k : ℕ∞) ≤ analyticOrderAt f z) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G U ∧
      (∀ z ∈ U, f z = P z ^ k * G z) ∧ (∀ z ∉ U, G z = 0) := by
  apply gaq hU k hP
  · intro z hz
    by_cases hPz : P z = 0
    · rw [(hP z hz).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hPz (hzero z hz hPz).1]
      simp
    · rw [(hP z hz).analyticOrderAt_eq_zero.mpr hPz]
      simp
  · intro z hz
    exact eaq1 (hf z hz) (hP z hz) k (hzero z hz)
end Nagata.LD
end
section
namespace Nagata.FCC
open Nagata.Workers.W28
noncomputable def fC (P : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hP : AnalyticOnNhd ℂ P U) (hne : ∀ z ∈ U, P z ≠ 0) :
    OpenPartialHomeomorph (ℂ × ℂ) (ℂ × ℂ) where
  toFun x := (x.1, P x.1 * x.2)
  invFun x := (x.1, x.2 / P x.1)
  source := {x | x.1 ∈ U}
  target := {x | x.1 ∈ U}
  map_source' := by intro x hx; exact hx
  map_target' := by intro x hx; exact hx
  left_inv' := by
    intro x hx
    ext
    · rfl
    · field_simp [hne x.1 hx]
  right_inv' := by
    intro x hx
    ext
    · rfl
    · field_simp [hne x.1 hx]
  open_source := hU.preimage continuous_fst
  open_target := hU.preimage continuous_fst
  continuousOn_toFun := by
    intro x hx
    exact (continuousAt_fst.prodMk
      (((hP x.1 hx).continuousAt.comp continuousAt_fst).mul continuousAt_snd)).continuousWithinAt
  continuousOn_invFun := by
    intro x hx
    exact (continuousAt_fst.prodMk
      (continuousAt_snd.div ((hP x.1 hx).continuousAt.comp continuousAt_fst)
        (hne x.1 hx))).continuousWithinAt
theorem fCaA (P : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hP : AnalyticOnNhd ℂ P U) (hne : ∀ z ∈ U, P z ≠ 0)
    (x : ℂ × ℂ) (hx : x.1 ∈ U) :
    AnalyticAt ℂ (fC P U hU hP hne) x := by
  have hf := (ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt x
  have hs := (ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt x
  exact hf.prod (((hP x.1 hx).comp hf).mul hs)
theorem fCsaA (P : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hP : AnalyticOnNhd ℂ P U) (hne : ∀ z ∈ U, P z ≠ 0)
    (x : ℂ × ℂ) (hx : x.1 ∈ U) :
    AnalyticAt ℂ (fC P U hU hP hne).symm x := by
  have hf := (ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt x
  have hs := (ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt x
  exact hf.prod (hs.div ((hP x.1 hx).comp hf) (hne x.1 hx))
theorem opbfs
    (P : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hP : AnalyticOnNhd ℂ P U) (hne : ∀ z ∈ U, P z ≠ 0)
    (F : (ℂ × ℂ) → ℂ) (x : ℂ × ℂ) (hx : x.1 ∈ U) (m : ℕ) :
    HAOAL (𝕜 := ℂ)
      (fun y : ℂ × ℂ => (P y.1 ^ m)⁻¹ * F (y.1, P y.1 * y.2)) x m ↔
    HAOAL (𝕜 := ℂ) F (x.1, P x.1 * x.2) m := by
  have hbase := (hP x.1 hx).comp ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt x)
  have hunit := (hbase.pow m).inv (pow_ne_zero m (hne x.1 hx))
  have hunitne : (P x.1 ^ m)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero m (hne x.1 hx))
  have hunit' : AnalyticAt ℂ (fun y : ℂ × ℂ => (P y.1 ^ m)⁻¹) x := hunit
  apply (Nagata.VUO.aoumi
    (f := fun y : ℂ × ℂ => F (y.1, P y.1 * y.2)) m hunit' hunitne).trans
  exact aoclc (fC P U hU hP hne) x hx
    (fCaA P U hU hP hne x hx)
    (fCsaA P U hU hP hne (x.1, P x.1 * x.2) hx) F m
end Nagata.FCC
end
section
namespace Nagata.LD
theorem qtoz {T : ℂ → ℂ} {f P G A B : ℂ → ℂ}
    (k : ℕ) (z : ℂ) (hP : P z ≠ 0) (hB : B z ≠ 0)
    (hfz : f z = P z ^ k * G z) (hfT : f (T z) = P (T z) ^ k * G (T z))
    (htf : f (T z) = A z * f z) (htP : P (T z) = B z * P z) :
    G (T z) = (A z / B z ^ k) * G z := by
  have heq : P (T z) ^ k * G (T z) = A z * (P z ^ k * G z) := by
    rw [← hfT, htf, hfz]
  rw [htP, mul_pow] at heq
  have hcancel : B z ^ k * G (T z) = A z * G z := by
    apply mul_left_cancel₀ (pow_ne_zero k hP)
    calc
      P z ^ k * (B z ^ k * G (T z)) = (B z ^ k * P z ^ k) * G (T z) := by ring
      _ = A z * (P z ^ k * G z) := heq
      _ = P z ^ k * (A z * G z) := by ring
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (pow_ne_zero k hB)).mpr
  rw [mul_comm]
  exact hcancel
theorem qtg {T : ℂ → ℂ} {f P G A B : ℂ → ℂ}
    {U : Set ℂ} (hU : IsOpen U) (k : ℕ)
    (hP : AnalyticOnNhd ℂ P U) (hPfin : ∀ z ∈ U, analyticOrderAt P z ≠ ⊤)
    (hTU : Set.MapsTo T U U) (hB : ∀ z ∈ U, B z ≠ 0)
    (hfactor : ∀ z ∈ U, f z = P z ^ k * G z)
    (htf : ∀ z ∈ U, f (T z) = A z * f z)
    (htP : ∀ z ∈ U, P (T z) = B z * P z)
    (hleft : ∀ z ∈ U, ContinuousAt (fun w => G (T w)) z)
    (hright : ∀ z ∈ U, ContinuousAt (fun w => (A w / B w ^ k) * G w) z) :
    ∀ z ∈ U, G (T z) = (A z / B z ^ k) * G z := by
  intro z hz
  apply ceaoe hU hz (hP z hz) (hPfin z hz)
    (hleft z hz) (hright z hz)
  intro w hw hPw
  exact qtoz k w hPw (hB w hw) (hfactor w hw)
    (hfactor (T w) (hTU hw)) (htf w hw) (htP w hw)
end Nagata.LD
end
section
namespace Nagata.CS
noncomputable def mS2 (τ γ : ℂ) (n : ℤ) (P : ℂ → ℂ) (k : ℕ) :
    Nagata.W08.aS τ n γ →ₗ[ℂ] (ℂ → ℂ) :=
  (mP2 P k).comp (Nagata.W08.aS τ n γ).subtype
theorem mSi (τ γ : ℂ) (n : ℤ) (P : ℂ → ℂ) (k : ℕ)
    (hP : AnalyticOnNhd ℂ P {z | z ≠ 0})
    (hPfin : ∀ z ≠ 0, analyticOrderAt P z ≠ ⊤) :
    Function.Injective (mS2 τ γ n P k) := by
  intro f g heq
  have hoff : Set.EqOn f.val g.val {z | z ≠ 0} := by
    apply Nagata.LD.mpio
      isOpen_ne k hP hPfin
      (fun z hz => (f.property.2.1 z hz).continuousAt)
      (fun z hz => (g.property.2.1 z hz).continuousAt)
    intro z hz
    exact congrFun heq z
  apply Nagata.W08.aSe
  exact hoff
end Nagata.CS
end
section
namespace Nagata.CS
theorem qmi {γ δ z : ℂ} (hδ : δ ≠ 0) (hz : z ≠ 0)
    (n s : ℤ) (k : ℕ) :
    (γ * z ^ (-n)) / (δ * z ^ (-s)) ^ k =
      (γ / δ ^ k) * z ^ (-(n - (k : ℤ) * s)) := by
  have he : -(n - (k : ℤ) * s) = -n - (-s) * (k : ℤ) := by ring
  rw [he, zpow_sub₀ hz, zpow_mul, zpow_natCast, mul_pow]
  field_simp
theorem eaq {τ γ δ : ℂ} {n s : ℤ}
    (hτ : τ ≠ 0) (hδ : δ ≠ 0)
    (f : Nagata.W08.aS τ n γ)
    (P : Nagata.W08.aS τ s δ)
    (hf : AnalyticOnNhd ℂ f.val {z | z ≠ 0})
    (hP : AnalyticOnNhd ℂ P.val {z | z ≠ 0}) (k : ℕ)
    (hzero : ∀ z ≠ 0, P.val z = 0 → deriv P.val z ≠ 0 ∧
      (k : ℕ∞) ≤ analyticOrderAt f.val z) :
    ∃ G : Nagata.W08.aS τ (n - (k : ℤ) * s) (γ / δ ^ k),
      ∀ z ≠ 0, f.val z = P.val z ^ k * G.val z := by
  obtain ⟨G, hG, hfactor, hGoutside⟩ :=
    Nagata.LD.egaq isOpen_ne hf hP k hzero
  have hPfin : ∀ z ≠ 0, analyticOrderAt P.val z ≠ ⊤ := by
    intro z hz
    by_cases hPz : P.val z = 0
    · rw [(hP z hz).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hPz (hzero z hz hPz).1]
      simp
    · rw [(hP z hz).analyticOrderAt_eq_zero.mpr hPz]
      simp
  have heq : ∀ z ≠ 0, G (τ * z) =
      ((γ * z ^ (-n)) / (δ * z ^ (-s)) ^ k) * G z := by
    apply Nagata.LD.qtg isOpen_ne k hP hPfin
      (fun z hz => mul_ne_zero hτ hz)
      (fun z hz => mul_ne_zero hδ (zpow_ne_zero _ hz)) hfactor
      (fun z hz => f.property.2.2 z hz) (fun z hz => P.property.2.2 z hz)
    · intro z hz
      exact (hG (τ * z) (mul_ne_zero hτ hz)).continuousAt.comp
        (continuousAt_const.mul continuousAt_id)
    · intro z hz
      have hA : ContinuousAt (fun w : ℂ => γ * w ^ (-n)) z :=
        continuousAt_const.mul (continuousAt_zpow₀ z (-n) (Or.inl hz))
      have hB : ContinuousAt (fun w : ℂ => δ * w ^ (-s)) z :=
        continuousAt_const.mul (continuousAt_zpow₀ z (-s) (Or.inl hz))
      exact (hA.div (hB.pow k) (pow_ne_zero k
        (mul_ne_zero hδ (zpow_ne_zero _ hz)))).mul (hG z hz).continuousAt
  refine ⟨⟨G, ?_⟩, hfactor⟩
  refine ⟨hGoutside 0 (by simp), ?_, ?_⟩
  · intro z hz
    exact (hG z hz).differentiableAt
  · intro z hz
    rw [heq z hz, qmi hδ hz]
end Nagata.CS
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W02
def mS (τ : ℝ) (γ : ℂ) : ℝ := Real.log ‖γ‖ / Real.log τ
def mP4 (γ : ℂ) : ℂ := γ / (‖γ‖ : ℂ)
theorem rmS {τ : ℝ} {γ : ℂ}
    (hτ : 0 < τ) (hτ1 : τ < 1) (hγ : γ ≠ 0) :
    τ ^ mS τ γ = ‖γ‖ := by
  have hl : Real.log τ ≠ 0 := ne_of_lt (Real.log_neg hτ hτ1)
  rw [Real.rpow_def_of_pos hτ, mS]
  have hm : Real.log τ * (Real.log ‖γ‖ / Real.log τ) = Real.log ‖γ‖ :=
    mul_div_cancel₀ _ hl
  rw [hm, Real.exp_log (norm_pos_iff.mpr hγ)]
theorem nmP {γ : ℂ} (hγ : γ ≠ 0) : ‖mP4 γ‖ = 1 := by
  unfold mP4
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
    div_self (norm_ne_zero_iff.mpr hγ)]
theorem mf {τ : ℝ} {γ : ℂ}
    (hτ : 0 < τ) (hτ1 : τ < 1) (hγ : γ ≠ 0) :
    γ = mP4 γ * ((τ ^ mS τ γ : ℝ) : ℂ) := by
  rw [rmS hτ hτ1 hγ]
  unfold mP4
  have hnorm : (‖γ‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hγ)
  exact (div_mul_cancel₀ γ hnorm).symm
def tFC (n σ : ℝ) : ℝ := (σ - 1 / 2) / n
theorem tFCe {n : ℝ} (hn : 0 < n) (σ : ℝ) :
    σ - tFC n σ * n = 1 / 2 := by
  unfold tFC
  rw [div_mul_cancel₀ _ (ne_of_gt hn)]
  ring
theorem hni : (1 / 2 : ℝ) ∉ Set.range (Int.cast : ℤ → ℝ) := by
  rintro ⟨z, hz⟩
  have hz0 : (0 : ℤ) < z := by
    exact_mod_cast (show (0 : ℝ) < (z : ℝ) by rw [hz]; norm_num)
  have hz1 : z < (1 : ℤ) := by
    exact_mod_cast (show (z : ℝ) < 1 by rw [hz]; norm_num)
  omega
theorem tFCn {n : ℝ} (hn : 0 < n) (σ : ℝ) :
    σ - tFC n σ * n ∉ Set.range (Int.cast : ℤ → ℝ) := by
  rw [tFCe hn]
  exact hni
theorem enmf {n τ : ℝ} {γ : ℂ}
    (hn : 0 < n) (hτ : 0 < τ) (hτ1 : τ < 1) (hγ : γ ≠ 0) :
    ∃ (σ x0 : ℝ) (ε : ℂ), ‖ε‖ = 1 ∧
      γ = ε * ((τ ^ σ : ℝ) : ℂ) ∧
      σ - x0 * n = 1 / 2 ∧
      σ - x0 * n ∉ Set.range (Int.cast : ℤ → ℝ) := by
  exact ⟨mS τ γ, tFC n (mS τ γ), mP4 γ,
    nmP hγ, mf hτ hτ1 hγ,
    tFCe hn _, tFCn hn _⟩
end Nagata.W02
end
end
section
namespace Nagata.CS
theorem cmi {L Q : ℂ} (hL : L ≠ 0) (d m j : ℤ) :
    L ^ (d - 3 * j) * Q ^ (j - m) =
      L ^ (d - 3 * m) * nMMM L Q ^ (m - j) := by
  have hLpow : L ^ (d - 3 * m) * (L ^ (3 : ℕ)) ^ (m - j) = L ^ (d - 3 * j) := by
    rw [← zpow_natCast L 3, ← zpow_mul, ← zpow_add₀ hL]
    congr 1
    ring
  have hQpow : (Q ^ (m - j))⁻¹ = Q ^ (j - m) := by
    rw [← zpow_neg]
    congr 1
    ring
  rw [nMMM, div_zpow, div_eq_mul_inv, ← mul_assoc, hLpow, hQpow]
theorem qcm {L Q : ℂ} (hL : L ≠ 0) (d m j : ℤ) :
    L ^ (d - 3 * j) / Q ^ (m - j) =
      L ^ (d - 3 * m) * nMMM L Q ^ (m - j) := by
  rw [div_eq_mul_inv, ← zpow_neg]
  have he : -(m - j) = j - m := by ring
  rw [he]
  exact cmi hL d m j
end Nagata.CS
end
section
namespace Nagata.CS
theorem elc {τ L Q : ℂ} (hτ : τ ≠ 0) (hL : L ≠ 0) (hQ : Q ≠ 0)
    (d m j : ℤ) (hj : j ≤ m)
    (P : Nagata.W08.aS τ 9 Q)
    (f : Nagata.W08.aS τ (3 * (d - 3 * j)) (L ^ (d - 3 * j)))
    (hP : AnalyticOnNhd ℂ P.val {z | z ≠ 0})
    (hf : AnalyticOnNhd ℂ f.val {z | z ≠ 0})
    (hzero : ∀ z ≠ 0, P.val z = 0 → deriv P.val z ≠ 0 ∧
      ((m - j).toNat : ℕ∞) ≤ analyticOrderAt f.val z) :
    ∃ g ∈ cS τ L Q d m j P.val,
      ∀ z ≠ 0, f.val z = P.val z ^ (m - j).toNat * g z := by
  obtain ⟨G, hfactor⟩ := eaq hτ hQ f P hf hP (m - j).toNat hzero
  have he : ((m - j).toNat : ℤ) = m - j := Int.toNat_of_nonneg (sub_nonneg.mpr hj)
  have hdeg : 3 * (d - 3 * j) - ((m - j).toNat : ℤ) * 9 = 3 * (d - 3 * m) := by
    rw [he]
    ring
  have hgam : L ^ (d - 3 * j) / Q ^ (m - j).toNat =
      L ^ (d - 3 * m) * nMMM L Q ^ (m - j) := by
    rw [← zpow_natCast Q (m - j).toNat, he]
    exact qcm hL d m j
  refine ⟨G.val, ?_, hfactor⟩
  rw [cS, if_pos hj]
  simpa only [hdeg, hgam] using G.property
end Nagata.CS
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W04.Dim
open Polynomial
open scoped nonZeroDivisors
variable {R : Type*} [CommRing R] [IsDomain R]
section
local instance oaiLocInst12 {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] : Algebra (Polynomial R) (Polynomial A) := Polynomial.algebra R A
noncomputable local instance oaiLocInst13 {R : Type*} [CommSemiring R] {S : Submonoid R} {A : Type*} [CommSemiring A] [Algebra R A] [IsLocalization S A] : IsLocalization (S.map Polynomial.C) (Polynomial A) := Polynomial.isLocalization S A
theorem phlo (I : Ideal R[X]) [I.IsPrime]
    (hC : I.comap Polynomial.C = ⊥) : I.height ≤ 1 := by
  let K := FractionRing R
  let M : Submonoid R[X] := (nonZeroDivisors R).map Polynomial.C
  have hd : Disjoint (M : Set R[X]) (I : Set R[X]) := by
    refine Set.disjoint_left.mpr ?_
    rintro p ⟨r, hr, rfl⟩ hp
    have hr0 : r = 0 := by
      have : r ∈ I.comap Polynomial.C := hp
      simpa [hC] using this
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hr) hr0
  let J : Ideal K[X] := I.map (algebraMap R[X] K[X])
  have : J.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M K[X] I inferInstance hd
  have he : J.height = I.height := IsLocalization.height_map_of_disjoint M I hd
  rw [← he]
  apply (Ideal.height_le_iff (n := 1)).mpr
  intro Q hQ hQJ
  have : Q.IsPrime := hQ
  have hQ0 : Q = ⊥ := by
    by_contra hQ0
    have : Q.IsMaximal := IsPrime.to_maximal_ideal hQ0
    exact hQJ.ne (Ideal.IsMaximal.eq_of_le inferInstance Ideal.IsPrime.ne_top' hQJ.le)
  simp [hQ0]
end
end Nagata.W04.Dim
end
end
section
noncomputable section
namespace Nagata.W04.Dim
open MvPolynomial
variable (K : Type*) [Field K] (n : ℕ)
def lVE : MvPolynomial (Fin (n + 1)) K ≃ₐ[K]
    Polynomial (MvPolynomial (Fin n) K) :=
  (MvPolynomial.renameEquiv K finSuccEquivLast).trans
    (MvPolynomial.optionEquivLeft K (Fin n))
theorem lVEsC (p : MvPolynomial (Fin n) K) :
    (lVE K n).symm (Polynomial.C p) =
      MvPolynomial.rename Fin.castSucc p := by
  have h : (lVE K n).symm.toAlgHom.comp Polynomial.CAlgHom =
      MvPolynomial.rename (R := K) Fin.castSucc := by
    ext i
    simp [lVE, MvPolynomial.optionEquivLeft_symm_C_X]
  exact DFunLike.congr_fun h p
variable {K n}
theorem hlooi
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    (hind : AlgebraicIndependent K
      (fun i : Fin n => Ideal.Quotient.mk I (MvPolynomial.X i.castSucc))) :
    I.height ≤ 1 := by
  let e := lVE K n
  let J := I.comap e.symm.toRingEquiv.toRingHom
  have : J.IsPrime := Ideal.comap_isPrime _ I
  have hmap : (Ideal.Quotient.mkₐ K I).comp
      (MvPolynomial.rename Fin.castSucc) =
      MvPolynomial.aeval (fun i : Fin n => Ideal.Quotient.mk I
        (MvPolynomial.X i.castSucc)) := by
    ext i
    simp
  have hC : J.comap Polynomial.C = ⊥ := by
    apply bot_unique
    intro p hp
    have hzero : Ideal.Quotient.mk I (MvPolynomial.rename Fin.castSucc p) = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      change e.symm (Polynomial.C p) ∈ I at hp
      simpa [e, lVEsC] using hp
    have hp0 : p = 0 := hind (by
      rw [← hmap]
      simpa using hzero)
    simpa using hp0
  have hheight : J.height = I.height := e.symm.toRingEquiv.height_comap I
  rw [← hheight]
  exact phlo J hC
end Nagata.W04.Dim
end
end
section
noncomputable section
namespace Nagata.W04.RS
open Polynomial
def mT {K : Type*} [CommSemiring K] (k : ℕ) : K[X] :=
  ∏ j ∈ Finset.range (k - 1), (X + C ((j + 2 : ℕ) : K))
def fM (k i : ℕ) : ℕ := if i = 0 then k + 1 else 1
def mP3 {K : Type*} [CommSemiring K] (k i : ℕ) : K[X] :=
  (X + C ((fM k i : ℕ) : K)) * mT k
variable {K : Type*} [Field K]
 theorem mTm (k : ℕ) : (mT k : K[X]).Monic := by
  exact monic_prod_of_monic _ _ (fun j _ => monic_X_add_C _)
 theorem mTnD (k : ℕ) : (mT k : K[X]).natDegree = k - 1 := by
  unfold mT
  rw [natDegree_prod_of_monic _ _ (fun j _ => monic_X_add_C _)]
  simp_rw [natDegree_X_add_C]
  simp
 theorem mPm (k i : ℕ) : (mP3 k i : K[X]).Monic :=
  (monic_X_add_C _).mul (mTm k)
 theorem mPnD (k i : ℕ) (hk : 0 < k) :
    (mP3 k i : K[X]).natDegree = k := by
  unfold mP3
  rw [(monic_X_add_C _).natDegree_mul (mTm k), natDegree_X_add_C,
    mTnD]
  omega
variable [CharZero K]
 theorem mTenn (k n : ℕ) : (mT k : K[X]).eval (n : K) ≠ 0 := by
  unfold mT
  rw [eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  simp only [eval_add, eval_X, eval_C]
  exact_mod_cast (show n + (j + 2) ≠ 0 by omega)
 theorem fMp (k i : ℕ) : 0 < fM k i := by
  unfold fM
  split <;> omega
 theorem mPenn (k i n : ℕ) :
    (mP3 k i : K[X]).eval (n : K) ≠ 0 := by
  unfold mP3
  rw [eval_mul, eval_add, eval_X, eval_C]
  apply mul_ne_zero _ (mTenn k n)
  exact_mod_cast (show n + fM k i ≠ 0 by have := fMp k i; omega)
 theorem mlfc (u v : ℕ) (huv : u ≠ v) :
    IsCoprime (X + C (u : K)) (X + C (v : K)) := by
  have huv' : -(u : K) ≠ -(v : K) := by
    intro h
    have h' : (u : K) = (v : K) := neg_injective h
    exact huv (Nat.cast_injective h')
  simpa only [C_neg, sub_neg_eq_add] using
    (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr huv').isUnit)
 theorem fMnt (k i j : ℕ) (hj : j < k - 1) : fM k i ≠ j + 2 := by
  unfold fM
  split <;> omega
end Nagata.W04.RS
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.PG
open scoped BigOperators
abbrev PP := Projectivization ℂ (Fin 3 → ℂ)
abbrev ODP (r : ℕ) :=
  {p : Fin r → PP // Function.Injective p}
def aPV (z : Fin 2 → ℂ) : Fin 3 → ℂ :=
  fun j => if j = 0 then 1 else if j = 1 then z 0 else z 1
theorem aPVnz (z : Fin 2 → ℂ) : aPV z ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [aPV] at h0
def aPP (z : Fin 2 → ℂ) : PP :=
  Projectivization.mk ℂ (aPV z) (aPVnz z)
theorem aPPi : Function.Injective aPP := by
  intro z w h
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff' ℂ (aPV z) (aPV w)
      (aPVnz z) (aPVnz w)).mp h
  have ha1 : a = 1 := by
    have h0 := congrFun ha 0
    simpa [aPV] using h0
  have hzero : w 0 = z 0 := by
    have h1 := congrFun ha 1
    simpa [aPV, ha1] using h1
  have hone : w 1 = z 1 := by
    have h2 := congrFun ha 2
    simpa [aPV, ha1] using h2
  funext i
  refine Fin.cases hzero.symm ?_ i
  intro j
  have hj : j = 0 := Subsingleton.elim j 0
  subst j
  exact hone.symm
structure ME (r : ℕ) where
  polynomial : MvPolynomial (Fin r × Fin 3) ℂ
  multidegree : Fin r → ℕ
  homogeneous : ∀ a ∈ polynomial.support, ∀ i,
    (∑ j : Fin 3, a (i, j)) = multidegree i
def eV {r : ℕ} (F : ME r)
    (p : Fin r → PP) : Prop :=
  ∀ (v : Fin r → Fin 3 → ℂ) (hv : ∀ i, v i ≠ 0),
    (∀ i, Projectivization.mk ℂ (v i) (hv i) = p i) →
    MvPolynomial.eval (fun ij => v ij.1 ij.2) F.polynomial = 0
def IPZC {r : ℕ} (S : Set (Fin r → PP)) : Prop :=
  ∃ equations : Set (ME r),
    ∀ p, p ∈ S ↔ ∀ F ∈ equations, eV F p
def ICZC {r : ℕ}
    (S : Set (ODP r)) : Prop :=
  ∃ T : Set (Fin r → PP), IPZC T ∧
    ∀ p, p ∈ S ↔ p.val ∈ T
theorem eVr {r : ℕ} (F : ME r)
    (p : Fin r → PP) (h : eV F p) :
    MvPolynomial.eval (fun ij => (p ij.1).rep ij.2) F.polynomial = 0 := by
  exact h (fun i => (p i).rep) (fun i => (p i).rep_nonzero)
    (fun i => Projectivization.mk_rep (p i))
abbrev CV (c : Fin 3) := {j : Fin 3 // j ≠ c}
def deh (c : Fin 3) (F : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial (CV c) ℂ :=
  MvPolynomial.eval₂ MvPolynomial.C
    (fun j => if h : j = c then 1 else MvPolynomial.X ⟨j, h⟩) F
def cC (c : Fin 3) (p : PP) : CV c → ℂ :=
  fun j => p.rep j.val / p.rep c
theorem cCm (c : Fin 3) (v : Fin 3 → ℂ) (hv : v ≠ 0) :
    cC c (Projectivization.mk ℂ v hv) =
      fun j : CV c => v j.val / v c := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  funext j
  simp only [cC, ← ha, Pi.smul_apply, Units.smul_def, smul_eq_mul]
  exact mul_div_mul_left _ _ a.ne_zero
theorem mrcnz (v : Fin 3 → ℂ) (hv : v ≠ 0) (c : Fin 3) :
    (Projectivization.mk ℂ v hv).rep c ≠ 0 ↔ v c ≠ 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  rw [← ha]
  simp [Units.smul_def, smul_eq_mul, a.ne_zero]
def mAL (F : MvPolynomial (Fin 3) ℂ)
    (p : PP) (m : ℕ) : Prop :=
  ∀ c : Fin 3, p.rep c ≠ 0 →
    AM.oAL (cC c p) m (deh c F)
theorem ce1 (p : PP) : ∃ c : Fin 3, p.rep c ≠ 0 := by
  by_contra h
  apply p.rep_nonzero
  funext c
  exact Classical.not_not.mp (fun hc => h ⟨c, hc⟩)
theorem dm (c : Fin 3) (F G : MvPolynomial (Fin 3) ℂ) :
    deh c (F * G) = deh c F * deh c G := by
  exact MvPolynomial.eval₂_mul _ _
theorem dp (c : Fin 3) (F : MvPolynomial (Fin 3) ℂ) (N : ℕ) :
    deh c (F ^ N) = deh c F ^ N := by
  exact MvPolynomial.eval₂_pow _ _
theorem mALz (F : MvPolynomial (Fin 3) ℂ)
    (p : PP) : mAL F p 0 := by
  intro c hc
  exact AM.oALz _ _
theorem mALm {F G : MvPolynomial (Fin 3) ℂ}
    {p : PP} {m n : ℕ} (hF : mAL F p m)
    (hG : mAL G p n) : mAL (F * G) p (m + n) := by
  intro c hc
  rw [dm]
  exact AM.oALm (hF c hc) (hG c hc)
theorem mALp {F : MvPolynomial (Fin 3) ℂ}
    {p : PP} {m : ℕ} (hF : mAL F p m) (N : ℕ) :
    mAL (F ^ N) p (m * N) := by
  intro c hc
  rw [dp]
  exact AM.oALp (hF c hc) N
end Nagata.PG
end
end
section
noncomputable section
namespace Nagata.PG
def cIE (c : Fin 3) : Fin 2 ≃ CV c :=
  Equiv.ofBijective (fun j => ⟨c.succAbove j, Fin.succAbove_ne c j⟩) (by
    constructor
    · intro i j h
      exact Fin.succAbove_right_injective (congrArg Subtype.val h)
    · intro j
      obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq j.property
      exact ⟨i, Subtype.ext hi⟩)
@[simp] theorem cIEv (c : Fin 3) (j : Fin 2) :
    (cIE c j).val = c.succAbove j := rfl
@[simp] theorem cIEss (c : Fin 3) (j : Fin 2) :
    (cIE c).symm ⟨c.succAbove j, Fin.succAbove_ne c j⟩ = j :=
  (cIE c).symm_apply_apply j
def cC1 (c : Fin 3) (p : PP) : Fin 2 → ℂ :=
  fun j => cC c p (cIE c j)
def cD1 (c : Fin 3) (F : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.rename (cIE c).symm (deh c F)
theorem cDeei (c : Fin 3)
    (F : MvPolynomial (Fin 3) ℂ) :
    cD1 c F =
      MvPolynomial.eval₂ MvPolynomial.C (c.insertNth 1 MvPolynomial.X) F := by
  let e : MvPolynomial (Fin 3) ℂ →+* MvPolynomial (Fin 2) ℂ :=
    (MvPolynomial.rename (cIE c).symm).toRingHom.comp
      (MvPolynomial.eval₂Hom MvPolynomial.C
        (fun j => if h : j = c then 1 else MvPolynomial.X ⟨j, h⟩))
  have he : e = MvPolynomial.eval₂Hom MvPolynomial.C (c.insertNth 1 MvPolynomial.X) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [e]
    · intro j
      by_cases hj : j = c
      · subst j
        simp [e]
      · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
        simp [e]
  exact RingHom.congr_fun he F
theorem oALcD (c : Fin 3) (p : PP)
    (F : MvPolynomial (Fin 3) ℂ) (m : ℕ) :
    AM.oAL (cC1 c p) m (cD1 c F) ↔
      AM.oAL (cC c p) m (deh c F) := by
  let e := (MvPolynomial.renameEquiv ℂ (cIE c).symm).toRingEquiv
  have he : ∀ f, MvPolynomial.eval (cC1 c p) (e f) =
      MvPolynomial.eval (cC c p) f := by
    intro f
    change MvPolynomial.eval (cC1 c p)
      (MvPolynomial.rename (cIE c).symm f) = _
    rw [MvPolynomial.eval_rename]
    have hcoords : cC1 c p ∘ (cIE c).symm =
        cC c p := by
      funext j
      simp [cC1]
    rw [hcoords]
  exact AM.oALei
    (cC c p) (cC1 c p) e he m (deh c F)
def cV (c : Fin 3) (z : Fin 2 → ℂ) : Fin 3 → ℂ := c.insertNth 1 z
theorem cVnz (c : Fin 3) (z : Fin 2 → ℂ) : cV c z ≠ 0 := by
  intro h
  have hc := congrFun h c
  simp [cV] at hc
def cP (c : Fin 3) (z : Fin 2 → ℂ) : PP :=
  Projectivization.mk ℂ (cV c z) (cVnz c z)
theorem cPcnz (c : Fin 3) (z : Fin 2 → ℂ) :
    (cP c z).rep c ≠ 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ
    (cV c z) (cVnz c z)
  have hcoord : (cP c z).rep c = (a : ℂ) := by
    change (Projectivization.mk ℂ (cV c z) (cVnz c z)).rep c = _
    rw [← ha]
    simp [cV, Units.smul_def]
  rw [hcoord]
  exact a.ne_zero
theorem cCcP (c : Fin 3) (z : Fin 2 → ℂ) :
    cC1 c (cP c z) = z := by
  funext j
  change cC c (Projectivization.mk ℂ (cV c z)
    (cVnz c z)) (cIE c j) = z j
  rw [cCm]
  simp [cV]
theorem cPcC (c : Fin 3) (p : PP)
    (hc : p.rep c ≠ 0) : cP c (cC1 c p) = p := by
  apply Eq.trans ?_ (Projectivization.mk_rep p)
  apply (Projectivization.mk_eq_mk_iff' ℂ
    (cV c (cC1 c p)) p.rep
    (cVnz c (cC1 c p)) p.rep_nonzero).mpr
  refine ⟨(p.rep c)⁻¹, ?_⟩
  funext j
  by_cases hj : j = c
  · subst j
    simp [cV, hc]
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    simp [cV, cC1, cC, div_eq_mul_inv, mul_comm]
abbrev CC (r : ℕ) := Fin r → Fin 3
def ICC {r : ℕ} (c : CC r)
    (p : Fin r → PP) : Prop := ∀ i, (p i).rep (c i) ≠ 0
def cCC {r : ℕ} (c : CC r)
    (p : Fin r → PP) : Fin r × Fin 2 → ℂ :=
  fun ij => (p ij.1).rep ((c ij.1).succAbove ij.2) / (p ij.1).rep (c ij.1)
def cCE {r : ℕ} (c : CC r)
    (z : Fin r × Fin 2 → ℂ) : Fin r → PP :=
  fun i => cP (c i) (fun j => z (i, j))
theorem cCc {r : ℕ} (p : Fin r → PP) :
    ∃ c : CC r, ICC c p := by
  let c : Fin r → Fin 3 := fun i => Classical.choose (ce1 (p i))
  exact ⟨c, fun i => Classical.choose_spec (ce1 (p i))⟩
end Nagata.PG
end
end
section
noncomputable section
namespace Nagata.PG
open scoped BigOperators
theorem mes {r : ℕ} (F : ME r)
    (a : Fin r → ℂ) (v : Fin r × Fin 3 → ℂ) :
    MvPolynomial.eval (fun ij => a ij.1 * v ij) F.polynomial =
      (∏ i : Fin r, a i ^ F.multidegree i) * MvPolynomial.eval v F.polynomial := by
  classical
  simp only [MvPolynomial.eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [mul_pow, Finset.prod_mul_distrib]
  have hprod : (∏ ij : Fin r × Fin 3, a ij.1 ^ u ij) =
      ∏ i : Fin r, a i ^ F.multidegree i := by
    rw [Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro i hi
    change (∏ j : Fin 3, a i ^ u (i, j)) = a i ^ F.multidegree i
    rw [Finset.prod_pow_eq_pow_sum, F.homogeneous u hu i]
  rw [hprod]
  ac_rfl
theorem eVier {r : ℕ} (F : ME r)
    (p : Fin r → PP) :
    eV F p ↔
      MvPolynomial.eval (fun ij => (p ij.1).rep ij.2) F.polynomial = 0 := by
  constructor
  · exact eVr F p
  · intro hrep v hv hp
    have hex : ∀ i : Fin r, ∃ a : ℂ, a • (p i).rep = v i := by
      intro i
      apply (Projectivization.mk_eq_mk_iff' ℂ (v i) (p i).rep
        (hv i) (p i).rep_nonzero).mp
      exact (hp i).trans (Projectivization.mk_rep (p i)).symm
    let a : Fin r → ℂ := fun i => Classical.choose (hex i)
    have ha : ∀ i, a i • (p i).rep = v i := fun i => Classical.choose_spec (hex i)
    have hv_eq : (fun ij : Fin r × Fin 3 => v ij.1 ij.2) =
        fun ij => a ij.1 * (p ij.1).rep ij.2 := by
      funext ij
      simpa only [Pi.smul_apply, smul_eq_mul] using (congrFun (ha ij.1) ij.2).symm
    rw [hv_eq, mes, hrep, mul_zero]
end Nagata.PG
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.Workers.W25
open MvPolynomial
theorem ecnef (K : Type*) [CommRing K] [IsDomain K]
    [Uncountable K] (n : ℕ) {ι : Type*} [Countable ι] :
    ∀ p : ι → MvPolynomial (Fin n) K, (∀ i, p i ≠ 0) →
      ∃ x : Fin n → K, ∀ i, eval x (p i) ≠ 0 := by
  classical
  induction n with
  | zero =>
      intro p hp
      refine ⟨Fin.elim0, fun i hi => hp i ?_⟩
      apply (isEmptyRingEquiv K (Fin 0)).injective
      rw [map_zero, isEmptyRingEquiv_eq_coeff_zero]
      rw [(p i).eq_C_of_isEmpty, eval_C] at hi
      exact hi
  | succ n ih =>
      intro p hp
      let Q : ι → Polynomial (MvPolynomial (Fin n) K) :=
        fun i => finSuccEquiv K n (p i)
      have hQ : ∀ i, Q i ≠ 0 := by
        intro i hi
        apply hp i
        apply (finSuccEquiv K n).injective
        simpa only [map_zero] using hi
      have hcoeff : ∀ i, ∃ d, (Q i).coeff d ≠ 0 := by
        intro i
        by_contra h
        apply hQ i
        apply Polynomial.ext
        intro d
        simp only [Polynomial.coeff_zero]
        exact Classical.not_not.mp (fun hd => h ⟨d, hd⟩)
      let k : ι → ℕ := fun i => Classical.choose (hcoeff i)
      have hk : ∀ i, (Q i).coeff (k i) ≠ 0 :=
        fun i => Classical.choose_spec (hcoeff i)
      obtain ⟨x, hx⟩ := ih (fun i => (Q i).coeff (k i)) hk
      let q : ι → Polynomial K := fun i => Polynomial.map (eval x) (Q i)
      have hq : ∀ i, q i ≠ 0 := by
        intro i hi
        apply hx i
        have h := congrArg (fun P : Polynomial K => P.coeff (k i)) hi
        simpa only [q, Polynomial.coeff_map, Polynomial.coeff_zero] using h
      let B : Set K := ⋃ i, {y | (q i).IsRoot y}
      have hB : B.Countable := Set.countable_iUnion fun i =>
        (Polynomial.finite_setOfPred_isRoot (hq i)).countable
      have hex : ∃ y : K, y ∉ B := by
        by_contra h
        have hBu : B = Set.univ := Set.eq_univ_of_forall fun y =>
          Classical.not_not.mp (fun hy => h ⟨y, hy⟩)
        exact Set.not_countable_univ (hBu ▸ hB)
      obtain ⟨y, hy⟩ := hex
      refine ⟨Fin.cons y x, fun i hi => hy ?_⟩
      apply Set.mem_iUnion.mpr
      refine ⟨i, ?_⟩
      change Polynomial.eval y (q i) = 0
      simpa only [eval_eq_eval_mv_eval', q, Q] using hi
theorem ecne (K : Type*) [CommRing K] [IsDomain K]
    [Uncountable K] {σ ι : Type*} [Fintype σ] [Countable ι]
    (p : ι → MvPolynomial σ K) (hp : ∀ i, p i ≠ 0) :
    ∃ x : σ → K, ∀ i, eval x (p i) ≠ 0 := by
  classical
  let e := Fintype.equivFin σ
  have hq : ∀ i, rename e (p i) ≠ 0 := by
    intro i hi
    apply hp i
    apply rename_injective e e.injective
    simpa only [map_zero] using hi
  obtain ⟨x, hx⟩ := ecnef K (Fintype.card σ)
    (fun i => rename e (p i)) hq
  refine ⟨x ∘ e, fun i => ?_⟩
  simpa only [eval_rename] using hx i
end Nagata.Workers.W25
end
section
namespace Nagata.Workers.W25
theorem ecpad {σ ι : Type*} [Fintype σ] [Countable ι]
    (p : ι → MvPolynomial σ ℂ) (hp : ∀ i, p i ≠ 0) :
    ∃ x : σ → ℂ, ∀ i, MvPolynomial.eval x (p i) ≠ 0 := by
  let : Uncountable ℂ := Cardinal.aleph0_lt_mk_iff.mp (by
    rw [Cardinal.mk_complex]
    exact Cardinal.cantor Cardinal.aleph0)
  exact ecne ℂ p hp
end Nagata.Workers.W25
end
section
namespace Nagata.Workers.W25
theorem cpf {σ : Type*} [Fintype σ]
    {p q : MvPolynomial σ ℂ}
    (h : ∀ x : σ → ℂ, MvPolynomial.eval x p = MvPolynomial.eval x q) : p = q := by
  apply sub_eq_zero.mp
  by_contra hne
  obtain ⟨x, hx⟩ := ecpad
    (fun _ : Unit => p - q) (fun _ => hne)
  apply hx ()
  rw [map_sub, h x, sub_self]
end Nagata.Workers.W25
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W16
abbrev PP1 := MvPolynomial (Fin 3) ℂ
theorem hes1 {σ K R : Type*} [CommSemiring K] [CommSemiring R]
    {F : MvPolynomial σ K} {d : ℕ} (hF : F.IsHomogeneous d)
    (k : K →+* R) (x : σ → R) (a : R) :
    MvPolynomial.eval₂ k (fun i => a * x i) F =
      a ^ d * MvPolynomial.eval₂ k x F := by
  classical
  simp only [MvPolynomial.eval₂_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hF.degree_eq_sum_deg_support hu]
  ac_rfl
theorem hes {σ K : Type*} [CommSemiring K]
    {F : MvPolynomial σ K} {d : ℕ} (hF : F.IsHomogeneous d)
    (x : σ → K) (a : K) :
    MvPolynomial.eval (fun i => a * x i) F = a ^ d * MvPolynomial.eval x F := by
  classical
  simp only [MvPolynomial.eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hF.degree_eq_sum_deg_support hu]
  ac_rfl
structure NHF (d : ℕ) where
  polynomial : PP1
  homogeneous : polynomial.IsHomogeneous d
  nonzero : polynomial ≠ 0
namespace NHF
theorem tDe {d : ℕ} (F : NHF d) :
    F.polynomial.totalDegree = d :=
  F.homogeneous.totalDegree F.nonzero
end NHF
open scoped BigOperators
theorem fpf {ι : Type*} (s : Finset ι)
    (F : ι → PP1) (d : ι → ℕ)
    (hhom : ∀ i ∈ s, (F i).IsHomogeneous (d i))
    (hne : ∀ i ∈ s, F i ≠ 0) :
    (∏ i ∈ s, F i) ≠ 0 ∧
      (∏ i ∈ s, F i).IsHomogeneous (∑ i ∈ s, d i) ∧
      (∏ i ∈ s, F i).totalDegree = ∑ i ∈ s, d i := by
  classical
  have hp : (∏ i ∈ s, F i) ≠ 0 := Finset.prod_ne_zero_iff.mpr hne
  have hh := MvPolynomial.IsHomogeneous.prod s F d hhom
  exact ⟨hp, hh, hh.totalDegree hp⟩
end Nagata.W16
end
end
section
noncomputable section
namespace Nagata.W16
open scoped BigOperators
def bA (F : MvPolynomial (Fin 2) ℂ) : Polynomial ℂ :=
  MvPolynomial.eval₂ Polynomial.C (fun i => if i = 0 then Polynomial.X else 1) F
theorem bAes (F : MvPolynomial (Fin 2) ℂ) :
    bA F = ∑ u ∈ F.support, Polynomial.C (F.coeff u) * Polynomial.X ^ u 0 := by
  classical
  rw [bA, MvPolynomial.eval₂_eq']
  apply Finset.sum_congr rfl
  intro u _
  simp
theorem bAe (F : MvPolynomial (Fin 2) ℂ) (z : ℂ) :
    (bA F).eval z = MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z else 1) F := by
  classical
  simp [bAes, MvPolynomial.eval_eq', Polynomial.eval_finsetSum]
theorem bAn {F : MvPolynomial (Fin 2) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) (x : Fin 2 → ℂ) (hc : x 1 ≠ 0) :
    (bA F).eval (x 0 / x 1) = (x 1)⁻¹ ^ d * MvPolynomial.eval x F := by
  rw [bAe]
  have hcoords : (fun i : Fin 2 => if i = 0 then x 0 / x 1 else 1) =
      fun i => (x 1)⁻¹ * x i := by
    funext i
    fin_cases i <;> simp [hc, div_eq_mul_inv, mul_comm]
  rw [hcoords]
  exact hes hF x (x 1)⁻¹
theorem bAezi {F : MvPolynomial (Fin 2) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) (hf : bA F = 0) : F = 0 := by
  have hmul : MvPolynomial.X 1 * F = 0 := by
    apply ((MvPolynomial.isHomogeneous_X ℂ (1 : Fin 2)).mul hF).eq_zero_of_forall_eval_eq_zero
    intro x
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_X]
    by_cases hc : x 1 = 0
    · simp [hc]
    · have hval := bAn hF x hc
      rw [hf, Polynomial.eval_zero] at hval
      have hz : MvPolynomial.eval x F = 0 :=
        (mul_eq_zero.mp hval.symm).resolve_left (pow_ne_zero d (inv_ne_zero hc))
      rw [hz, mul_zero]
  exact (mul_eq_zero.mp hmul).resolve_left (MvPolynomial.X_ne_zero 1)
theorem bAnz {F : MvPolynomial (Fin 2) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) (hf : F ≠ 0) : bA F ≠ 0 := by
  intro hz
  exact hf (bAezi hF hz)
theorem bAnDl {F : MvPolynomial (Fin 2) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) : (bA F).natDegree ≤ d := by
  classical
  rw [bAes]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro u hu
  apply (Polynomial.natDegree_C_mul_X_pow_le (F.coeff u) (u 0)).trans
  rw [hF.degree_eq_sum_deg_support hu]
  by_cases hz : u 0 = 0
  · simp [hz]
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr hz)
end Nagata.W16
end
end
section
noncomputable section
namespace Nagata.W16
open Nagata.PG
open scoped BigOperators
def bD {r : ℕ} (F : ME r) :
    MvPolynomial (Fin r × Fin 2) ℂ :=
  MvPolynomial.eval₂ MvPolynomial.C
    (fun ij => if ij.2 = 0 then 1 else
      if ij.2 = 1 then MvPolynomial.X (ij.1, 0) else MvPolynomial.X (ij.1, 1))
    F.polynomial
theorem mes {r : ℕ} (F : ME r)
    (x : Fin r × Fin 3 → ℂ) (a : Fin r → ℂ) :
    MvPolynomial.eval (fun ij => a ij.1 * x ij) F.polynomial =
      (∏ i, a i ^ F.multidegree i) * MvPolynomial.eval x F.polynomial := by
  classical
  simp only [MvPolynomial.eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [mul_pow, Finset.prod_mul_distrib]
  have hdegrees : (∏ ij : Fin r × Fin 3, a ij.1 ^ u ij) =
      ∏ i, a i ^ F.multidegree i := by
    rw [Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro i _
    change (∏ y : Fin 3, a i ^ u (i, y)) = a i ^ F.multidegree i
    rw [Finset.prod_pow_eq_pow_sum, F.homogeneous u hu i]
  rw [hdegrees]
  ac_rfl
theorem ebD {r : ℕ} (F : ME r)
    (x : Fin r × Fin 2 → ℂ) :
    MvPolynomial.eval x (bD F) =
      MvPolynomial.eval
        (fun ij => aPV (fun j => x (ij.1, j)) ij.2) F.polynomial := by
  classical
  unfold bD
  rw [← MvPolynomial.eval_assoc]
  apply congrArg (fun z : Fin r × Fin 3 → ℂ => MvPolynomial.eval z F.polynomial)
  funext ij
  rcases ij with ⟨i, j⟩
  fin_cases j <;> simp [aPV, Function.comp_apply]
theorem ebDn {r : ℕ} (F : ME r)
    (x : Fin r × Fin 3 → ℂ) (hc : ∀ i, x (i, 0) ≠ 0) :
    MvPolynomial.eval (fun ij : Fin r × Fin 2 => x (ij.1, ij.2.succ) / x (ij.1, 0))
        (bD F) =
      (∏ i, (x (i, 0))⁻¹ ^ F.multidegree i) * MvPolynomial.eval x F.polynomial := by
  classical
  rw [ebD]
  have hcoords :
      (fun ij : Fin r × Fin 3 =>
        aPV (fun j => x (ij.1, j.succ) / x (ij.1, 0)) ij.2) =
      fun ij => (x (ij.1, 0))⁻¹ * x ij := by
    funext ij
    rcases ij with ⟨i, j⟩
    fin_cases j <;> simp [aPV, hc i, div_eq_mul_inv] <;> ac_rfl
  rw [hcoords]
  exact mes F x (fun i => (x (i, 0))⁻¹)
theorem ezobD {r : ℕ}
    (F : ME r) (hchart : bD F = 0) :
    F.polynomial = 0 := by
  classical
  let Q : MvPolynomial (Fin r × Fin 3) ℂ := ∏ i : Fin r, MvPolynomial.X (i, 0)
  have hQ : Q ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact MvPolynomial.X_ne_zero (i, 0)
  have hmul : Q * F.polynomial = 0 := by
    apply Nagata.Workers.W25.cpf
    intro x
    rw [map_mul, map_zero]
    by_cases hc : ∀ i : Fin r, x (i, 0) ≠ 0
    · have hz := congrArg
        (MvPolynomial.eval (fun ij : Fin r × Fin 2 => x (ij.1, ij.2.succ) / x (ij.1, 0)))
        hchart
      rw [ebDn F x hc, map_zero] at hz
      have hn : (∏ i, (x (i, 0))⁻¹ ^ F.multidegree i) ≠ 0 := by
        apply Finset.prod_ne_zero_iff.mpr
        intro i _
        exact pow_ne_zero _ (inv_ne_zero (hc i))
      rw [(mul_eq_zero.mp hz).resolve_left hn, mul_zero]
    · obtain ⟨i, hi⟩ := Classical.not_forall.mp hc
      have hi0 : x (i, 0) = 0 := Classical.not_not.mp hi
      have heval : MvPolynomial.eval x Q = ∏ i : Fin r, x (i, 0) := by
        simp [Q]
      rw [heval, Finset.prod_eq_zero (Finset.mem_univ i) hi0, zero_mul]
  exact (mul_eq_zero.mp hmul).resolve_left hQ
theorem bDnz {r : ℕ} (F : ME r)
    (hne : F.polynomial ≠ 0) : bD F ≠ 0 := by
  intro hz
  exact hne (ezobD F hz)
end Nagata.W16
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W02
def DE (k : ℕ) := {d : Fin 3 →₀ ℕ // d.degree = k}
instance degreeExponentFintype (k : ℕ) : Fintype (DE k) :=
  ((Finsupp.finite_of_degree_le (σ := Fin 3) k).subset
    (fun _ h => le_of_eq h)).fintype
def hCE (R : Type*) [CommRing R] (k : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin 3) R k ≃ₗ[R] (DE k →₀ R) :=
  (LinearEquiv.ofEq _ _
    (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (Fin 3) R k)).trans
      (AddMonoidAlgebra.supportedEquivFinsupp {d : Fin 3 →₀ ℕ | d.degree = k})
@[simp] theorem hCEss (R : Type*) [CommRing R]
    (k : ℕ) (e : DE k) (c : R) :
    (((hCE R k).symm (Finsupp.single e c)) :
      MvPolynomial (Fin 3) R) = MvPolynomial.monomial e.val c := by
  apply AddMonoidAlgebra.coeff_injective
  change (((Finsupp.supportedEquivFinsupp (R := R)
    {d : Fin 3 →₀ ℕ | d.degree = k}).symm (Finsupp.single e c)) :
      (Fin 3 →₀ ℕ) →₀ R) = Finsupp.single e.val c
  exact Finsupp.supportedEquivFinsupp_symm_single _ e c
end Nagata.W02
end
end
section
noncomputable section
namespace Nagata.W02
def dEE (k : ℕ) :
    DE k ≃ ↥(Finset.finsuppAntidiag (Finset.univ : Finset (Fin 3)) k) where
  toFun d := ⟨d.val, by
    rw [Finset.mem_finsuppAntidiag]
    exact ⟨by simpa only [← Finsupp.degree_eq_sum] using d.property,
      Finset.subset_univ _⟩⟩
  invFun d := ⟨d.val, by
    have hd := (Finset.mem_finsuppAntidiag.mp d.property).1
    simpa only [← Finsupp.degree_eq_sum] using hd⟩
  left_inv _ := rfl
  right_inv _ := rfl
theorem cdE (k : ℕ) :
    Fintype.card (DE k) = (k + 2).choose 2 := by
  rw [Fintype.card_congr (dEE k), Fintype.card_coe,
    Finset.card_finsuppAntidiag_nat_eq_choose]
  simp only [Finset.card_univ, Fintype.card_fin]
  have he : 3 + k - 1 = k + 2 := by omega
  rw [he]
  exact Nat.choose_symm_add
instance homogeneousFiniteDimensional (K : Type*) [Field K] (k : ℕ) :
    FiniteDimensional K (MvPolynomial.homogeneousSubmodule (Fin 3) K k) :=
  (hCE K k).symm.finiteDimensional
end Nagata.W02
end
end
section
noncomputable section
namespace Nagata.W02
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]
theorem ahCEs (d : ℕ) (s : Fin 3 → A)
    (c : DE d →₀ K) :
    MvPolynomial.aeval s
      (((hCE K d).symm c) : MvPolynomial (Fin 3) K) =
    Finsupp.linearCombination K
      (fun e : DE d => MvPolynomial.aeval s (MvPolynomial.monomial e.val (1 : K))) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c c' hc hc' => simp only [map_add, Submodule.coe_add, hc, hc']
  | single e a =>
    rw [hCEss, Finsupp.linearCombination_single]
    simp [MvPolynomial.aeval_monomial, Algebra.smul_def]
end Nagata.W02
end
end
section
noncomputable section
namespace Nagata.W02
open MvPolynomial
abbrev BF := MvPolynomial (Fin 2) ℂ
def bL (r : ℂ) : BF := X 0 - C r * X 1
def bRP (s : Multiset ℂ) : BF := (s.map bL).prod
def bAH : BF →+* Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i => if i = 0 then Polynomial.X else 1)
theorem bLh (r : ℂ) : (bL r).IsHomogeneous 1 := by
  exact (isHomogeneous_X ℂ (0 : Fin 2)).sub ((isHomogeneous_X ℂ (1 : Fin 2)).C_mul r)
theorem bRPh (s : Multiset ℂ) :
    (bRP s).IsHomogeneous s.card := by
  induction s using Multiset.induction_on with
  | empty => simpa [bRP] using (isHomogeneous_one (Fin 2) ℂ)
  | @cons r s ih =>
    simpa [bRP, Nat.add_comm] using (bLh r).mul ih
@[simp] theorem bAHl (r : ℂ) :
    bAH (bL r) = Polynomial.X - Polynomial.C r := by
  rw [bL, map_sub, map_mul]
  simp [bAH]
@[simp] theorem bAHrP (s : Multiset ℂ) :
    bAH (bRP s) = (s.map (fun r => Polynomial.X - Polynomial.C r)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [bRP]
  | @cons r s ih =>
    simp only [bRP, Multiset.map_cons, Multiset.prod_cons] at *
    rw [map_mul, bAHl, ih]
theorem bhf {F : BF} {d : ℕ}
    (hF : F.IsHomogeneous d) (hF0 : F ≠ 0) :
    ∃ (c : ℂ) (e : ℕ) (s : Multiset ℂ), c ≠ 0 ∧ e + s.card = d ∧
      F = C c * ((X 1 : BF) ^ e * bRP s) := by
  let q := Nagata.W16.bA F
  have hq : q ≠ 0 := Nagata.W16.bAnz hF hF0
  have hqd : q.natDegree ≤ d := Nagata.W16.bAnDl hF
  have hroots : q.roots.card = q.natDegree := (IsAlgClosed.splits q).natDegree_eq_card_roots.symm
  let G : BF := C q.leadingCoeff * (X 1 ^ (d - q.natDegree) * bRP q.roots)
  have hG : G.IsHomogeneous d := by
    have hp := ((isHomogeneous_X ℂ (1 : Fin 2)).pow (d - q.natDegree)).mul
      (bRPh q.roots)
    have hh := hp.C_mul q.leadingCoeff
    simpa only [one_mul, hroots, Nat.sub_add_cancel hqd] using hh
  have heval : bAH G = q := by
    change bAH (C q.leadingCoeff * (X 1 ^ (d - q.natDegree) * bRP q.roots)) = q
    rw [map_mul, map_mul, map_pow, bAHrP]
    have hC : bAH (C q.leadingCoeff) = Polynomial.C q.leadingCoeff := by
      simp [bAH]
    have hX : bAH (X 1) = (1 : Polynomial ℂ) := by simp [bAH]
    rw [hC, hX, one_pow, one_mul]
    exact (IsAlgClosed.splits q).eq_prod_roots.symm
  have hzero : Nagata.W16.bA (F - G) = 0 := by
    change bAH (F - G) = 0
    rw [map_sub, heval]
    change q - q = 0
    exact sub_self q
  have heq : F = G := sub_eq_zero.mp (Nagata.W16.bAezi (hF.sub hG) hzero)
  exact ⟨q.leadingCoeff, d - q.natDegree, q.roots, Polynomial.leadingCoeff_ne_zero.mpr hq,
    by omega, heq⟩
end Nagata.W02
end
end
section
noncomputable section
namespace Nagata.W02
open MvPolynomial
noncomputable local instance oaiLocInst1 {σ R : Type*} [CommSemiring R] : GradedAlgebra (MvPolynomial.homogeneousSubmodule σ R) := MvPolynomial.gradedAlgebra
theorem bhnM {J : Ideal BF} (hJ : J.IsPrime)
    (hlin : ∀ a b : ℂ, C a * X 0 + C b * X 1 ∈ J → a = 0 ∧ b = 0)
    {F : BF} {d : ℕ} (hF : F.IsHomogeneous d) (hF0 : F ≠ 0) : F ∉ J := by
  let := hJ
  have hX : (X 1 : BF) ∉ J := by
    intro h
    have := (hlin 0 1 (by simpa using h)).2
    exact one_ne_zero this
  have hL (r : ℂ) : bL r ∉ J := by
    intro h
    have := (hlin 1 (-r) (by simpa [bL, sub_eq_add_neg] using h)).1
    exact one_ne_zero this
  have hpow (e : ℕ) : (X 1 : BF) ^ e ∉ J := by
    induction e with
    | zero => simpa using hJ.one_notMem
    | succ e ih => simpa only [pow_succ, hJ.mul_mem_iff_mem_or_mem, not_or] using And.intro ih hX
  have hprod (s : Multiset ℂ) : bRP s ∉ J := by
    induction s using Multiset.induction_on with
    | empty => simpa [bRP] using hJ.one_notMem
    | @cons r s ih =>
      simpa only [bRP, Multiset.map_cons, Multiset.prod_cons,
        hJ.mul_mem_iff_mem_or_mem, not_or] using And.intro (hL r) ih
  obtain ⟨c, e, s, hc, _, heq⟩ := bhf hF hF0
  rw [heq, hJ.mul_mem_iff_mem_or_mem, not_or]
  refine ⟨Ideal.notMem_of_isUnit J ((isUnit_iff_ne_zero.mpr hc).map C), ?_⟩
  rw [hJ.mul_mem_iff_mem_or_mem, not_or]
  exact ⟨hpow e, hprod s⟩
theorem bezom {J : Ideal BF} (hJ : J.IsPrime)
    (hcomp : ∀ F ∈ J, ∀ d, homogeneousComponent d F ∈ J)
    (hlin : ∀ a b : ℂ, C a * X 0 + C b * X 1 ∈ J → a = 0 ∧ b = 0)
    {F : BF} (hF : F ∈ J) : F = 0 := by
  have hz (d : ℕ) : homogeneousComponent d F = 0 := by
    by_contra hn
    exact bhnM hJ hlin (homogeneousComponent_isHomogeneous d F) hn
      (hcomp F hF d)
  rw [← sum_homogeneousComponent F]
  simp only [hz, Finset.sum_const_zero]
theorem hCr {σ ι : Type*} (e : σ → ι)
    (F : MvPolynomial σ ℂ) (d : ℕ) :
    homogeneousComponent d (rename e F) = rename e (homogeneousComponent d F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial u a =>
    have h := isHomogeneous_monomial a (show u.degree = u.degree from rfl)
    rw [homogeneousComponent_of_mem (h.rename_isHomogeneous (f := e)), homogeneousComponent_of_mem h]
    split_ifs <;> simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
theorem cmoiH {σ : Type*} {I : Ideal (MvPolynomial σ ℂ)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ ℂ)) {P : MvPolynomial σ ℂ}
    (hP : P ∈ I) (n : ℕ) : homogeneousComponent n P ∈ I := by
  have hh := hI n hP
  have hcomp (D : DirectSum.Decomposition (homogeneousSubmodule σ ℂ)) :
      (D.decompose' P n : MvPolynomial σ ℂ) = homogeneousComponent n P := by
    rw [Subsingleton.elim D MvPolynomial.decomposition,
      MvPolynomial.decomposition.decompose'_apply]
  rwa [← DirectSum.Decomposition.decompose'_eq, hcomp] at hh
theorem brezo {σ : Type*} (e : Fin 2 → σ)
    {I : Ideal (MvPolynomial σ ℂ)} (hI : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule σ ℂ))
    (hlin : ∀ a b : ℂ, C a * X (e 0) + C b * X (e 1) ∈ I → a = 0 ∧ b = 0)
    {F : BF} (hF : rename e F ∈ I) : F = 0 := by
  let J : Ideal BF := Ideal.comap (rename e).toRingHom I
  have hJ : J.IsPrime := hI.comap _
  apply bezom hJ (J := J) ?_ ?_ hF
  · intro P hP d
    change rename e (homogeneousComponent d P) ∈ I
    rw [← hCr]
    exact cmoiH hhom hP d
  · intro a b hab
    exact hlin a b (by simpa [J, Ideal.mem_comap] using hab)
theorem aIqon {σ : Type*}
    (e : Fin 2 → σ) {I : Ideal (MvPolynomial σ ℂ)} (hI : I.IsPrime)
    (hhom : I.IsHomogeneous (homogeneousSubmodule σ ℂ))
    (hlin : ∀ a b : ℂ, C a * X (e 0) + C b * X (e 1) ∈ I → a = 0 ∧ b = 0) :
    AlgebraicIndependent ℂ (fun i : Fin 2 => Ideal.Quotient.mk I (X (e i))) := by
  rw [algebraicIndependent_iff]
  intro F hF
  apply brezo e hI hhom hlin
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have heq : (Ideal.Quotient.mkₐ ℂ I).comp (rename e) =
      aeval (fun i : Fin 2 => Ideal.Quotient.mk I (X (e i))) := by
    ext i
    simp
  exact (congrArg (fun f : BF →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ I) => f F) heq).trans hF
end Nagata.W02
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.Workers.W11
variable {ρ κ K : Type*} [Fintype ρ] [Fintype κ] [DecidableEq κ]
theorem dmezo [CommRing K]
    (A : Matrix ρ κ K) (C : Matrix κ ρ K)
    (hA : ∀ s : κ → ρ, Matrix.det (fun i j => A (s i) j) = 0) :
    (C * A).det = 0 := by
  classical
  let D : MultilinearMap K (fun _ : κ => κ → K) K :=
    Matrix.detRowAlternating.toMultilinearMap
  have hmul : C * A = fun i => ∑ r, C i r • A r := by
    funext i j
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change D (C * A) = 0
  rw [hmul, D.map_sum]
  apply Finset.sum_eq_zero
  intro s _
  rw [D.map_smul_univ]
  change (∏ i, C i (s i)) • Matrix.det (fun i j => A (s i) j) = 0
  rw [hA s, smul_zero]
theorem enkoa [Field K]
    (A : Matrix ρ κ K)
    (hA : ∀ s : κ → ρ, Matrix.det (fun i j => A (s i) j) = 0) :
    ∃ c : κ → K, c ≠ 0 ∧ A.mulVec c = 0 := by
  classical
  by_contra hkernel
  have hker : LinearMap.ker (Matrix.toLin' A) = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro c hc
    by_contra hc0
    exact hkernel ⟨c, hc0, hc⟩
  obtain ⟨g, hg⟩ := (Matrix.toLin' A).exists_leftInverse_of_injective hker
  have hC : LinearMap.toMatrix' g * A = 1 := by
    simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_id] using congrArg LinearMap.toMatrix' hg
  have hdet := dmezo A (LinearMap.toMatrix' g) hA
  rw [hC, Matrix.det_one] at hdet
  exact one_ne_zero hdet
theorem enkco [Field K]
    (A : Matrix ρ κ K)
    (hA : ∀ s : κ → ρ, Matrix.det (fun i j => A (s i) j) = 0) :
    ∃ c : κ → K, c ≠ 0 ∧ ∀ i, ∑ j, A i j * c j = 0 := by
  obtain ⟨c, hc, hAc⟩ := enkoa A hA
  exact ⟨c, hc, fun i => congrFun hAc i⟩
end Nagata.Workers.W11
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W27
noncomputable section
open MvPolynomial
abbrev PJ (r : ℕ) (m : Fin r → ℕ) :=
  (i : Fin r) × {ab : Fin (m i) × Fin (m i) // ab.1.val + ab.2.val < m i}
end
end Nagata.W27
end
section
noncomputable section
namespace Nagata.W27
open scoped BigOperators
open MvPolynomial
section LinearEquations
variable {R : Type*} [CommRing R]
variable {σ κ ρ : Type*} [Fintype κ]
def cE (A : Matrix ρ κ (MvPolynomial σ R))
    (p : σ → R) (c : κ → R) (row : ρ) : R :=
  ∑ col, eval p (A row col) * c col
theorem cEa (A : Matrix ρ κ (MvPolynomial σ R))
    (p : σ → R) (c c' : κ → R) (row : ρ) :
    cE A p (c + c') row =
      cE A p c row + cE A p c' row := by
  simp [cE, mul_add, Finset.sum_add_distrib]
theorem cEs (A : Matrix ρ κ (MvPolynomial σ R))
    (p : σ → R) (a : R) (c : κ → R) (row : ρ) :
    cE A p (a • c) row = a * cE A p c row := by
  simp only [cE, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro col _
  exact mul_left_comm _ _ _
def cLM (A : Matrix ρ κ (MvPolynomial σ R)) (p : σ → R) :
    (κ → R) →ₗ[R] (ρ → R) where
  toFun c row := cE A p c row
  map_add' c c' := funext (cEa A p c c')
  map_smul' a c := funext (cEs A p a c)
def pZS {τ : Type*} (f : τ → MvPolynomial σ R) : Set (σ → R) :=
  {p | ∀ t, eval p (f t) = 0}
end LinearEquations
end Nagata.W27
end
end
section
noncomputable section
namespace Nagata.W27
open MvPolynomial
open Classical
abbrev HM (d : ℕ) := Nagata.W02.DE d
variable {R : Type*} [CommRing R]
def hC1 (d : ℕ) :
    homogeneousSubmodule (Fin 3) R d ≃ₗ[R] (HM d → R) :=
  (Nagata.W02.hCE R d).trans
    (Finsupp.linearEquivFunOnFinite R R (HM d))
theorem hCnzi (d : ℕ)
    (F : homogeneousSubmodule (Fin 3) R d) :
    hC1 d F ≠ 0 ↔ F.val ≠ 0 := by
  constructor
  · intro h hz
    apply h
    have hF : F = 0 := Subtype.ext hz
    rw [hF, map_zero]
  · intro h hz
    apply h
    have hF : F = 0 := (hC1 d).injective
      (hz.trans (map_zero (hC1 d)).symm)
    exact congrArg Subtype.val hF
theorem hCsnz (d : ℕ)
    (c : HM d → R) :
    ((hC1 d).symm c).val ≠ 0 ↔ c ≠ 0 := by
  rw [← hCnzi]
  rw [LinearEquiv.apply_symm_apply]
end Nagata.W27
end
end
section
noncomputable section
namespace Nagata.W27
open MvPolynomial
variable {ι R : Type*} [CommRing R]
def uT (i : ι) :
    MvPolynomial (Fin 2) R →+*
      MvPolynomial (Fin 2) (MvPolynomial (ι × Fin 2) R) :=
  eval₂Hom (C.comp C) (fun j => X j + C (X (i, j)))
def uJC (i : ι) (s : Fin 2 →₀ ℕ)
    (f : MvPolynomial (Fin 2) R) : MvPolynomial (ι × Fin 2) R :=
  (uT i f).coeff s
theorem muT (p : ι × Fin 2 → R) (i : ι)
    (f : MvPolynomial (Fin 2) R) :
    MvPolynomial.map (eval p) (uT i f) =
      eval₂Hom C (fun j => X j + C (p (i, j))) f := by
  have h : (MvPolynomial.map (eval p)).comp (uT i) =
      eval₂Hom C (fun j => X j + C (p (i, j))) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [uT]
    · intro j
      simp [uT]
  exact RingHom.congr_fun h f
theorem euJC (p : ι × Fin 2 → R) (i : ι)
    (s : Fin 2 →₀ ℕ) (f : MvPolynomial (Fin 2) R) :
    eval p (uJC i s f) =
      (eval₂Hom C (fun j => X j + C (p (i, j))) f).coeff s := by
  rw [uJC, ← coeff_map, muT]
theorem uJCa (i : ι) (s : Fin 2 →₀ ℕ)
    (f g : MvPolynomial (Fin 2) R) :
    uJC i s (f + g) =
      uJC i s f + uJC i s g := by
  simp [uJC]
theorem uJCCm (i : ι) (s : Fin 2 →₀ ℕ)
    (a : R) (f : MvPolynomial (Fin 2) R) :
    uJC i s (C a * f) =
      C a * uJC i s f := by
  simp [uJC, uT, coeff_C_mul]
end Nagata.W27
end
end
section
namespace Nagata.W27
noncomputable section
open scoped BigOperators
open MvPolynomial
section Determinants
variable {R : Type*} [CommRing R]
variable {σ κ ρ : Type*} [Fintype κ] [DecidableEq κ]
def mP (A : Matrix ρ κ (MvPolynomial σ R)) (s : κ → ρ) :
    MvPolynomial σ R :=
  Matrix.det (fun i j => A (s i) j)
theorem emP (A : Matrix ρ κ (MvPolynomial σ R))
    (s : κ → ρ) (p : σ → R) :
    eval p (mP A s) = Matrix.det (fun i j => eval p (A (s i) j)) := by
  exact (eval p).map_det _
theorem mzSi (A : Matrix ρ κ (MvPolynomial σ R)) (p : σ → R) :
    p ∈ pZS (mP A) ↔
      ∀ s : κ → ρ, Matrix.det (fun i j => eval p (A (s i) j)) = 0 := by
  simp only [pZS, Set.mem_ofPred_eq, emP]
theorem mezon [IsDomain R]
    (A : Matrix ρ κ (MvPolynomial σ R)) (p : σ → R)
    (c : κ → R) (hc : cLM A p c = 0) (hcne : c ≠ 0)
    (s : κ → ρ) : eval p (mP A s) = 0 := by
  rw [emP]
  apply Matrix.det_eq_zero_of_not_linearIndependent_cols
  intro hli
  have hz : (∑ col, c col • (fun i => eval p (A (s i) col))) = 0 := by
    funext i
    have hrow : cE A p c (s i) = 0 := congrFun hc (s i)
    simpa only [cE, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply, mul_comm] using hrow
  have hc0 : ∀ col, c col = 0 := Fintype.linearIndependent_iff.mp hli c hz
  exact hcne (funext hc0)
theorem mmzSo [IsDomain R]
    (A : Matrix ρ κ (MvPolynomial σ R)) (p : σ → R)
    (c : κ → R) (hc : cLM A p c = 0) (hcne : c ≠ 0) :
    p ∈ pZS (mP A) :=
  fun s => mezon A p c hc hcne s
end Determinants
end
end Nagata.W27
end
section
noncomputable section
namespace Nagata.W27
open scoped BigOperators
open MvPolynomial
variable {R : Type*} [CommRing R]
def dCH (c : Fin 3) : MvPolynomial (Fin 3) R →+* MvPolynomial (Fin 2) R :=
  eval₂Hom C (Fin.insertNth (α := fun _ : Fin 3 => MvPolynomial (Fin 2) R) c 1 X)
def dCLM (c : Fin 3) :
    MvPolynomial (Fin 3) R →ₗ[R] MvPolynomial (Fin 2) R where
  toFun := dCH c
  map_add' := (dCH c).map_add
  map_smul' a f := by simp [smul_eq_C_mul, dCH]
def uJLM {ι : Type*} (i : ι) (s : Fin 2 →₀ ℕ) :
    MvPolynomial (Fin 2) R →ₗ[R] MvPolynomial (ι × Fin 2) R where
  toFun := uJC i s
  map_add' := uJCa i s
  map_smul' a f := by
    simp only [smul_eq_C_mul, uJCCm, RingHom.id_apply]
theorem lMesb {κ M : Type*} [Fintype κ] [DecidableEq κ]
    [AddCommMonoid M] [Module R M] (L : (κ → R) →ₗ[R] M) (x : κ → R) :
    L x = ∑ j, x j • L (Pi.single j 1) := by
  classical
  have hx : x = ∑ j, x j • (Pi.single j (1 : R) : κ → R) := by
    funext j
    simp [Pi.single_apply]
  conv_lhs => rw [hx]
  simp only [map_sum, map_smul]
end Nagata.W27
end
end
section
noncomputable section
namespace Nagata.W27
open MvPolynomial
variable {σ ρ κ K : Type*} [Field K]
variable [Fintype ρ] [Fintype κ] [DecidableEq κ]
theorem nkimz
    (A : Matrix ρ κ (MvPolynomial σ K)) (p : σ → K) :
    (∃ c : κ → K, c ≠ 0 ∧ cLM A p c = 0) ↔
      p ∈ pZS (mP A) := by
  constructor
  · rintro ⟨c, hc, hAc⟩
    exact mmzSo A p c hAc hc
  · intro h
    obtain ⟨c, hc, hAc⟩ :=
      Nagata.Workers.W11.enkco
        (fun i j => eval p (A i j)) ((mzSi A p).mp h)
    exact ⟨c, hc, funext hAc⟩
end Nagata.W27
end
end
section
noncomputable section
namespace Nagata.W27
open MvPolynomial
variable {r : ℕ} {R : Type*} [CommRing R]
def pJE {m : Fin r → ℕ} (row : PJ r m) : Fin 2 →₀ ℕ :=
  Nagata.Workers.W30.eP row.2.val.1.val row.2.val.2.val
theorem aoiuj (p : Fin r × Fin 2 → R)
    (m : Fin r → ℕ) (f : Fin r → MvPolynomial (Fin 2) R) :
    (∀ i, Nagata.AM.oAL (fun j => p (i, j)) (m i) (f i)) ↔
      ∀ row : PJ r m,
        eval p (uJC row.1 (pJE row) (f row.1)) = 0 := by
  constructor
  · intro h row
    rw [euJC]
    exact (Nagata.AM.oALfT
      _ _ _).mp (h row.1) row.2.val.1.val row.2.val.2.val row.2.property
  · intro h i
    apply (Nagata.AM.oALfT _ _ _).mpr
    intro u v huv
    have hu : u < m i := by omega
    have hv : v < m i := by omega
    let row : PJ r m := ⟨i, ⟨(⟨u, hu⟩, ⟨v, hv⟩), huv⟩⟩
    have hr := h row
    rw [euJC] at hr
    exact hr
end Nagata.W27
end
end
section
noncomputable section
namespace Nagata.W27
open scoped BigOperators
open MvPolynomial
open Classical
variable {R : Type*} [CommRing R]
variable {r : ℕ}
def cJPM (c : Fin r → Fin 3) (d : ℕ) (m : Fin r → ℕ)
    (row : PJ r m) :
    homogeneousSubmodule (Fin 3) R d →ₗ[R] MvPolynomial (Fin r × Fin 2) R :=
  (uJLM row.1 (pJE row)).comp
    ((dCLM (c row.1)).comp (homogeneousSubmodule (Fin 3) R d).subtype)
def cPJM (c : Fin r → Fin 3) (d : ℕ) (m : Fin r → ℕ) :
    Matrix (PJ r m) (HM d) (MvPolynomial (Fin r × Fin 2) R) :=
  fun row col => cJPM c d m row
    ((hC1 d).symm (Pi.single col 1))
theorem cEcPJ (c : Fin r → Fin 3)
    (d : ℕ) (m : Fin r → ℕ) (p : Fin r × Fin 2 → R)
    (F : homogeneousSubmodule (Fin 3) R d) (row : PJ r m) :
    cE (cPJM c d m) p (hC1 d F) row =
      eval p (uJC row.1 (pJE row)
        (dCH (c row.1) F.val)) := by
  classical
  have h := lMesb
    ((cJPM c d m row).comp (hC1 d).symm.toLinearMap)
    (hC1 d F)
  have he := congrArg (eval p) h
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, map_sum, smul_eval,
    cPJM, cJPM, uJLM,
    dCLM, Submodule.coe_subtype, LinearMap.coe_mk,
    AddHom.coe_mk, cE, mul_comm] using he.symm
theorem coik (c : Fin r → Fin 3)
    (d : ℕ) (m : Fin r → ℕ) (p : Fin r × Fin 2 → R)
    (F : homogeneousSubmodule (Fin 3) R d) :
    (∀ i, Nagata.AM.oAL (fun j => p (i, j)) (m i)
      (dCH (c i) F.val)) ↔
      cLM (cPJM c d m) p (hC1 d F) = 0 := by
  rw [aoiuj]
  change (∀ row, _) ↔ (fun row => cE _ _ _ row) = (fun _ => 0)
  rw [funext_iff]
  exact forall_congr' fun row => by rw [cEcPJ]
theorem enfic (c : Fin r → Fin 3)
    (d : ℕ) (m : Fin r → ℕ) (p : Fin r × Fin 2 → R) :
    (∃ F : homogeneousSubmodule (Fin 3) R d, F.val ≠ 0 ∧
      ∀ i, Nagata.AM.oAL (fun j => p (i, j)) (m i)
        (dCH (c i) F.val)) ↔
      ∃ v : HM d → R, v ≠ 0 ∧
        cLM (cPJM c d m) p v = 0 := by
  constructor
  · rintro ⟨F, hF, horder⟩
    exact ⟨hC1 d F,
      (hCnzi d F).mpr hF,
      (coik c d m p F).mp horder⟩
  · rintro ⟨v, hv, hker⟩
    refine ⟨(hC1 d).symm v,
      (hCsnz d v).mpr hv, ?_⟩
    apply (coik c d m p _).mpr
    simpa only [LinearEquiv.apply_symm_apply] using hker
end Nagata.W27
end
end
section
noncomputable section
namespace Nagata.W27
open MvPolynomial
open Classical
variable {r : ℕ} {K : Type*} [Field K]
theorem enfic1 (c : Fin r → Fin 3)
    (d : ℕ) (m : Fin r → ℕ) (p : Fin r × Fin 2 → K) :
    (∃ F : homogeneousSubmodule (Fin 3) K d, F.val ≠ 0 ∧
      ∀ i, Nagata.AM.oAL (fun j => p (i, j)) (m i)
        (dCH (c i) F.val)) ↔
      p ∈ pZS (mP (cPJM c d m)) := by
  classical
  exact (enfic c d m p).trans
    (nkimz (cPJM c d m) p)
end Nagata.W27
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.Workers.W30
open UniqueFactorizationMonoid
noncomputable section
abbrev TP := MvPolynomial (Fin 3) ℂ
local instance : DecidableEq (Associates TP) := Classical.decEq _
def eM1 (F : TP) : Associates TP →₀ ℕ :=
  factorization (Associates.mk F)
theorem eMei {F G : TP} (hF : F ≠ 0) (hG : G ≠ 0) :
    eM1 F = eM1 G ↔ Associated F G := by
  constructor
  · intro h
    have ha := associated_of_factorization_eq (Associates.mk F) (Associates.mk G)
      (Associates.mk_ne_zero.mpr hF) (Associates.mk_ne_zero.mpr hG) h
    exact Associates.mk_eq_mk_iff_associated.mp (associated_iff_eq.mp ha)
  · intro h
    unfold eM1
    rw [Associates.mk_eq_mk_iff_associated.mpr h]
def aPI (a : Associates TP) : Ideal TP :=
  (Ideal.associatesEquivIsPrincipal TP a).val
theorem aPIi : Function.Injective aPI := by
  intro a b h
  apply (Ideal.associatesEquivIsPrincipal TP).injective
  exact Subtype.ext h
@[simp] theorem aPIm (F : TP) :
    aPI (Associates.mk F) = Ideal.span {F} := rfl
def eIC (F : TP) : Ideal TP →₀ ℕ :=
  (eM1 F).mapDomain aPI
theorem eICei {F G : TP} (hF : F ≠ 0) (hG : G ≠ 0) :
    eIC F = eIC G ↔ Associated F G := by
  change Finsupp.mapDomain aPI (eM1 F) =
    Finsupp.mapDomain aPI (eM1 G) ↔ _
  rw [(Finsupp.mapDomain_injective aPIi).eq_iff,
    eMei hF hG]
theorem eMsp (F : TP)
    {a : Associates TP} (ha : a ∈ (eM1 F).support) :
    Prime a := by
  apply prime_of_normalized_factor a
  simpa only [eM1, support_factorization, Multiset.mem_toFinset] using ha
theorem eICs (F : TP)
    {I : Ideal TP} (hI : I ∈ (eIC F).support) :
    I.IsPrime ∧ I ≠ ⊥ ∧ I.IsPrincipal := by
  classical
  rw [eIC,
    Finsupp.mapDomain_support_of_injective aPIi] at hI
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hI
  have hprime := eMsp F ha
  obtain ⟨P, rfl⟩ := Associates.mk_surjective a
  have hP : Prime P := Associates.prime_mk.mp hprime
  rw [aPIm]
  exact ⟨(Ideal.span_singleton_prime hP.ne_zero).mpr hP,
    fun h => hP.ne_zero (Ideal.span_singleton_eq_bot.mp h), inferInstance⟩
theorem eICc (F : TP)
    (a : Associates TP) :
    eIC F (aPI a) = eM1 F a := by
  exact Finsupp.mapDomain_apply aPIi _ _
end
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
open UniqueFactorizationMonoid
variable {R : Type*} [CommRing R] [IsDomain R]
theorem npeol {I P : Ideal R} [I.IsPrime] [P.IsPrime]
    (hI : I ≠ ⊥) (hIP : I ≤ P) (hP : P.height ≤ 1) : I = P := by
  by_contra hne
  have hlt : I < P := lt_of_le_of_ne hIP hne
  have hIheight : I.height < 1 :=
    (Ideal.height_le_iff (n := 1)).mp hP I inferInstance hlt
  have hzero : I.height = 0 := Order.lt_one_iff.mp hIheight
  have hbad : (⊥ : Ideal R).height < (0 : ℕ∞) :=
    (Ideal.height_le_iff (n := 0)).mp (by simp [hzero]) ⊥ inferInstance
      (bot_lt_iff_ne_bot.mpr hI)
  exact (not_lt_of_ge bot_le) hbad
variable [UniqueFactorizationMonoid R]
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
open MvPolynomial
open scoped BigOperators
variable {σ K : Type*} [Field K]
lemma tHCnz {p : MvPolynomial σ K} (hp : p ≠ 0) :
    homogeneousComponent p.totalDegree p ≠ 0 := by
  classical
  obtain ⟨a,ha,hdeg⟩ := Finset.exists_mem_eq_sup p.support
    (support_nonempty.mpr hp) (fun a => a.sum fun _ e => e)
  intro hz
  have hz' := congrArg (fun polynomial : MvPolynomial σ K => polynomial.coeff a) hz
  have heq : a.degree = p.totalDegree := hdeg.symm
  have hc : p.coeff a = 0 := by
    simpa [coeff_homogeneousComponent, heq] using hz'
  exact (mem_support_iff.mp ha) hc
lemma tHCm (p q : MvPolynomial σ K) :
    homogeneousComponent (p.totalDegree + q.totalDegree) (p*q) =
      homogeneousComponent p.totalDegree p * homogeneousComponent q.totalDegree q := by
  classical
  have hdecomp : p*q =
      (∑ i ∈ Finset.range (p.totalDegree+1), homogeneousComponent i p) *
      (∑ j ∈ Finset.range (q.totalDegree+1), homogeneousComponent j q) := by
    rw [sum_homogeneousComponent, sum_homogeneousComponent]
  rw [hdecomp]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum, map_sum]
  rw [Finset.sum_eq_single p.totalDegree]
  · rw [Finset.sum_eq_single q.totalDegree]
    · rw [homogeneousComponent_of_mem
        ((homogeneousComponent_isHomogeneous p.totalDegree p).mul
          (homogeneousComponent_isHomogeneous q.totalDegree q))]
      simp
    · intro j hj hne
      rw [homogeneousComponent_of_mem
        ((homogeneousComponent_isHomogeneous p.totalDegree p).mul
          (homogeneousComponent_isHomogeneous j q))]
      simp only [ite_eq_right_iff]
      intro h
      exfalso
      apply hne
      omega
    · simp
  · intro i hi hne
    apply Finset.sum_eq_zero
    intro j hj
    rw [homogeneousComponent_of_mem
      ((homogeneousComponent_isHomogeneous i p).mul
        (homogeneousComponent_isHomogeneous j q))]
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    have hne' : p.totalDegree + q.totalDegree ≠ i+j := by omega
    simp [hne']
  · simp
lemma dponn {p : MvPolynomial σ K} (hp : p ≠ 0)
    (hu : ¬ IsUnit p) : 0 < p.totalDegree := by
  by_contra hn
  have hz : p.totalDegree = 0 := by omega
  have heq := totalDegree_eq_zero_iff_eq_C.mp hz
  have hc : p.coeff 0 ≠ 0 := by
    intro hc
    apply hp
    rw [heq,hc,C_0]
  apply hu
  rw [heq]
  exact (isUnit_iff_ne_zero.mpr hc).map C
theorem ehif (p : MvPolynomial σ K) {d : ℕ}
    (hp : p ≠ 0) (hhom : p.IsHomogeneous d) :
    ∃ L : Multiset (MvPolynomial σ K),
      (∀ P ∈ L, Irreducible P ∧ P.IsHomogeneous P.totalDegree) ∧ Associated L.prod p := by
  classical
  suffices H : ∀ n (p : MvPolynomial σ K), p.totalDegree = n → p ≠ 0 →
      p.IsHomogeneous n → ∃ L : Multiset (MvPolynomial σ K),
      (∀ P ∈ L, Irreducible P ∧ P.IsHomogeneous P.totalDegree) ∧ Associated L.prod p from
    H d p (hhom.totalDegree hp) hp hhom
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p hdeg hp hhom
    by_cases hu : IsUnit p
    · refine ⟨0, by simp, ?_⟩
      simpa using (associated_one_iff_isUnit.mpr hu).symm
    rcases irreducible_or_factor hu with hirr | ⟨a,b,hau,hbu,hab⟩
    · refine ⟨{p}, ?_, ?_⟩
      · intro P hP
        have heq : P = p := Multiset.mem_singleton.mp hP
        subst P
        exact ⟨hirr, by simpa only [hdeg] using hhom⟩
      · simp
    · have ha : a ≠ 0 := by intro h; simp [h] at hab; exact hp hab
      have hb : b ≠ 0 := by intro h; simp [h] at hab; exact hp hab
      have hsum : a.totalDegree+b.totalDegree = n := by
        rw [← totalDegree_mul_of_isDomain ha hb, ← hab, hdeg]
      have hapos := dponn ha hau
      have hbpos := dponn hb hbu
      let A := homogeneousComponent a.totalDegree a
      let B := homogeneousComponent b.totalDegree b
      have hA : A ≠ 0 := tHCnz ha
      have hB : B ≠ 0 := tHCnz hb
      have hAh : A.IsHomogeneous a.totalDegree := homogeneousComponent_isHomogeneous _ _
      have hBh : B.IsHomogeneous b.totalDegree := homogeneousComponent_isHomogeneous _ _
      have hprod : A*B = p := by
        change homogeneousComponent a.totalDegree a * homogeneousComponent b.totalDegree b = p
        rw [← tHCm, ← hab, hsum,
          homogeneousComponent_of_mem hhom]
        simp
      obtain ⟨L,hL,hLp⟩ := ih a.totalDegree (by omega) A (hAh.totalDegree hA) hA hAh
      obtain ⟨M,hM,hMp⟩ := ih b.totalDegree (by omega) B (hBh.totalDegree hB) hB hBh
      refine ⟨L+M, ?_, ?_⟩
      · intro P hP
        exact (Multiset.mem_add.mp hP).elim (hL P) (hM P)
      · rw [Multiset.prod_add, ← hprod]
        exact hLp.mul_mul hMp
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
open MvPolynomial UniqueFactorizationMonoid
variable {σ K : Type*} [Field K]
lemma uptD (u : (MvPolynomial σ K)ˣ) :
    (u : MvPolynomial σ K).totalDegree = 0 := by
  have h := totalDegree_mul_of_isDomain u.ne_zero (u⁻¹).ne_zero
  simp only [← Units.val_mul, mul_inv_cancel, Units.val_one, totalDegree_one] at h
  omega
lemma hoa {p q : MvPolynomial σ K} {d : ℕ}
    (hp : p.IsHomogeneous d) (h : Associated p q) : q.IsHomogeneous d := by
  obtain ⟨u,rfl⟩ := h
  have hu : (u : MvPolynomial σ K).IsHomogeneous 0 :=
    (totalDegree_zero_iff_isHomogeneous σ).mp (uptD u)
  simpa only [add_zero] using hp.mul hu
theorem fh {p : MvPolynomial σ K} {d : ℕ}
    (hp : p ≠ 0) (hhom : p.IsHomogeneous d) :
    ∀ f ∈ factors p, f.IsHomogeneous f.totalDegree := by
  classical
  obtain ⟨L,hL,hprod⟩ := ehif p hp hhom
  have hrel : Multiset.Rel Associated (factors p) L :=
    factors_unique irreducible_of_factor (fun f hf => (hL f hf).1)
      ((factors_prod hp).trans hprod.symm)
  intro f hf
  obtain ⟨g,hg,hfg⟩ := Multiset.exists_mem_of_rel_of_mem hrel hf
  have hgHom := hoa (hL g hg).2 hfg.symm
  have hf0 : f ≠ 0 := (prime_of_factor f hf).ne_zero
  simpa only [hgHom.totalDegree hf0] using hgHom
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
open MvPolynomial
noncomputable local instance oaiLocInst2 {σ R : Type*} [CommSemiring R] : GradedAlgebra (MvPolynomial.homogeneousSubmodule σ R) := MvPolynomial.gradedAlgebra
variable {σ K : Type*} [Field K]
theorem hpfii (P : Ideal (MvPolynomial σ K)) [hP : P.IsPrime]
    {x : MvPolynomial σ K} {d : ℕ} (hx : x ∈ P) (hx0 : x ≠ 0)
    (hhom : x.IsHomogeneous d) :
    ∃ f : MvPolynomial σ K, f ∈ P ∧ Irreducible f ∧ f.IsHomogeneous f.totalDegree := by
  obtain ⟨L,hL,hprod⟩ := ehif x hx0 hhom
  have hmem : L.prod ∈ P := P.mem_of_dvd hprod.dvd' hx
  obtain ⟨f,hf,hfP⟩ := (hP.multiset_prod_mem_iff_exists_mem L).mp hmem
  exact ⟨f,hfP,hL f hf⟩
theorem hhopg (P : Ideal (MvPolynomial σ K))
    [hP : P.IsPrime] (hP0 : P ≠ ⊥) (hheight : P.height ≤ 1)
    (hhom : P.IsHomogeneous (homogeneousSubmodule σ K)) :
    ∃ f : MvPolynomial σ K, Prime f ∧ f.IsHomogeneous f.totalDegree ∧
      0 < f.totalDegree ∧ P = Ideal.span {f} := by
  obtain ⟨x,hx,hx0⟩ := P.ne_bot_iff.mp hP0
  have hcompEq (D : DirectSum.Decomposition (homogeneousSubmodule σ K)) :
      (D.decompose' x x.totalDegree : MvPolynomial σ K) = homogeneousComponent x.totalDegree x := by
    rw [Subsingleton.elim D MvPolynomial.decomposition,
      MvPolynomial.decomposition.decompose'_apply]
  have hcomp := (hhom.mem_iff.mp hx) x.totalDegree
  rw [← DirectSum.Decomposition.decompose'_eq, hcompEq] at hcomp
  obtain ⟨f,hf,hfirr,hfhom⟩ := hpfii P hcomp
    (tHCnz hx0) (homogeneousComponent_isHomogeneous _ _)
  have hfprime : Prime f := UniqueFactorizationMonoid.irreducible_iff_prime.mp hfirr
  let : (Ideal.span ({f} : Set (MvPolynomial σ K))).IsPrime :=
    (Ideal.span_singleton_prime hfprime.ne_zero).mpr hfprime
  refine ⟨f,hfprime,hfhom,dponn hfprime.ne_zero hfprime.not_isUnit,?_⟩
  exact (npeol
    (fun h => hfprime.ne_zero (Ideal.span_singleton_eq_bot.mp h))
    ((Ideal.span_singleton_le_iff_mem P).mpr hf) hheight).symm
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
open MvPolynomial UniqueFactorizationMonoid
variable {σ K : Type*} [Field K]
lemma hmp (L : Multiset (MvPolynomial σ K))
    (hL : ∀ f ∈ L, f.IsHomogeneous f.totalDegree) :
    L.prod.IsHomogeneous (L.map MvPolynomial.totalDegree).sum := by
  induction L using Multiset.induction_on with
  | empty => simpa using (isHomogeneous_one σ K)
  | @cons f L ih =>
    simpa only [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons] using
      (hL f (Multiset.mem_cons_self _ _)).mul
        (ih (fun g hg => hL g (Multiset.mem_cons_of_mem hg)))
theorem hod {p f : MvPolynomial σ K} {d : ℕ}
    (hp : p ≠ 0) (hhom : p.IsHomogeneous d) (hf : f ∣ p) :
    f.IsHomogeneous f.totalDegree := by
  classical
  have hf0 : f ≠ 0 := by rintro rfl; exact hp (by simpa using hf)
  have hfac : ∀ a ∈ factors f, a.IsHomogeneous a.totalDegree := by
    intro a ha
    have hairr : Irreducible a := irreducible_of_factor a ha
    have hadvd : a ∣ p :=
      (Multiset.dvd_prod ha).trans ((factors_prod hf0).dvd.trans hf)
    obtain ⟨b,hb,hab⟩ := exists_mem_factors_of_dvd hp hairr hadvd
    have hah := hoa (fh hp hhom b hb) hab.symm
    simpa only [hah.totalDegree hairr.ne_zero] using hah
  have hprod := hmp (factors f) hfac
  have hfh := hoa hprod (factors_prod hf0)
  simpa only [hfh.totalDegree hf0] using hfh
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
open MvPolynomial
noncomputable local instance oaiLocInst3 {σ R : Type*} [CommSemiring R] : GradedAlgebra (MvPolynomial.homogeneousSubmodule σ R) := MvPolynomial.gradedAlgebra
variable {σ K : Type*} [Field K]
theorem shoh {f : MvPolynomial σ K} {d : ℕ}
    (hf : f.IsHomogeneous d) :
    (Ideal.span ({f} : Set (MvPolynomial σ K))).IsHomogeneous (homogeneousSubmodule σ K) := by
  apply Ideal.homogeneous_span
  intro x hx
  have heq : x = f := Set.mem_singleton_iff.mp hx
  subst x
  exact ⟨d,hf⟩
end Nagata.Workers.W30
end
end OAI
end
section
namespace OAI
section
namespace Nagata.Workers.W30
open UniqueFactorizationMonoid
noncomputable section
local instance cycleAssociateDecidableEq : DecidableEq (Associates TP) := Classical.decEq _
end
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
@[simp] theorem eICo : eIC (1 : TP) = 0 := by
  simp only [eIC, eM1, Associates.mk_one,
    factorization_one, Finsupp.mapDomain_zero]
theorem eICzi {F : TP} (hF : F ≠ 0) :
    eIC F = 0 ↔ IsUnit F := by
  rw [← eICo, eICei hF one_ne_zero,
    associated_one_iff_isUnit]
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
open UniqueFactorizationMonoid
noncomputable section
local instance supportAssociateDecidableEq : DecidableEq (Associates TP) := Classical.decEq _
theorem smeIC (F f : TP) (hF : F ≠ 0) :
    Ideal.span ({f} : Set TP) ∈ (eIC F).support ↔
      Prime f ∧ f ∣ F := by
  classical
  rw [Finsupp.mem_support_iff, ← aPIm,
    eICc, ← Finsupp.mem_support_iff]
  change Associates.mk f ∈ (factorization (Associates.mk F)).support ↔ _
  rw [support_factorization, Multiset.mem_toFinset,
    mem_normalizedFactors_iff (Associates.mk_ne_zero.mpr hF),
    Associates.prime_mk, Associates.mk_dvd_mk]
end
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
open MvPolynomial UniqueFactorizationMonoid
noncomputable local instance oaiLocInst4 {σ R : Type*} [CommSemiring R] : GradedAlgebra (MvPolynomial.homogeneousSubmodule σ R) := MvPolynomial.gradedAlgebra
noncomputable section
theorem eICh {F : TP} {d : ℕ}
    (hF : F ≠ 0) (hhom : F.IsHomogeneous d) {I : Ideal TP}
    (hI : I ∈ (eIC F).support) :
    I.IsHomogeneous (homogeneousSubmodule (Fin 3) ℂ) := by
  classical
  rw [eIC,
    Finsupp.mapDomain_support_of_injective aPIi] at hI
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hI
  obtain ⟨f,rfl⟩ := Associates.mk_surjective a
  have hs : Ideal.span ({f} : Set TP) ∈ (eIC F).support := by
    rw [eIC,
      Finsupp.mapDomain_support_of_injective aPIi]
    exact Finset.mem_image.mpr ⟨Associates.mk f,ha,rfl⟩
  have hdiv := ((smeIC F f hF).mp hs).2
  rw [aPIm]
  exact shoh (hod hF hhom hdiv)
end
end Nagata.Workers.W30
end
section
namespace Nagata.Workers.W30
open MvPolynomial
noncomputable local instance oaiLocInst5 {σ R : Type*} [CommSemiring R] : GradedAlgebra (MvPolynomial.homogeneousSubmodule σ R) := MvPolynomial.gradedAlgebra
end Nagata.Workers.W30
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.PG
abbrev CLR (b : Fin 3) (p : PP) :=
  AM.PLR (cC b p)
def lHC (b : Fin 3) (p : PP) :
    Fin 3 → CLR b p :=
  fun j => if h : j = b then 1 else
    algebraMap (MvPolynomial (CV b) ℂ) (CLR b p)
      (MvPolynomial.X ⟨j, h⟩)
theorem lHCiU (b c : Fin 3) (p : PP)
    (hb : p.rep b ≠ 0) (hc : p.rep c ≠ 0) :
    IsUnit (lHC b p c) := by
  by_cases hcb : c = b
  · simp [lHC, hcb]
  · simp only [lHC, dif_neg hcb]
    apply (AM.rEiU (cC b p) _).mpr
    simpa [cC] using div_ne_zero hc hb
def lCDU (b c : Fin 3) (p : PP)
    (hb : p.rep b ≠ 0) (hc : p.rep c ≠ 0) : (CLR b p)ˣ :=
  (lHCiU b c p hb hc).unit
theorem lCDUv (b c : Fin 3) (p : PP)
    (hb : p.rep b ≠ 0) (hc : p.rep c ≠ 0) :
    (lCDU b c p hb hc : CLR b p) =
      lHC b p c :=
  (lHCiU b c p hb hc).unit_spec
def cTTLR (b c : Fin 3) (p : PP)
    (hb : p.rep b ≠ 0) (hc : p.rep c ≠ 0) :
    MvPolynomial (CV c) ℂ →+* CLR b p :=
  MvPolynomial.eval₂Hom
    ((algebraMap (MvPolynomial (CV b) ℂ) (CLR b p)).comp
      MvPolynomial.C)
    (fun j => (↑((lCDU b c p hb hc)⁻¹) : CLR b p) *
      lHC b p j.val)
theorem ed {R : Type*} [CommSemiring R]
    (k : ℂ →+* R) (x : Fin 3 → R) (c : Fin 3) (hc : x c = 1)
    (F : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial.eval₂ k (fun j : CV c => x j.val) (deh c F) =
      MvPolynomial.eval₂ k x F := by
  rw [deh, ← MvPolynomial.eval₂_assoc]
  congr 1
  funext j
  by_cases hj : j = c
  · subst j
    simp [hc]
  · simp [hj]
theorem elHC (b : Fin 3) (p : PP)
    (F : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial.eval₂
      ((algebraMap (MvPolynomial (CV b) ℂ) (CLR b p)).comp
        MvPolynomial.C)
      (lHC b p) F =
    algebraMap (MvPolynomial (CV b) ℂ) (CLR b p)
      (deh b F) := by
  rw [deh, MvPolynomial.eval₂_comp_left]
  congr 1
  funext j
  by_cases hj : j = b
  · simp [lHC, hj]
  · simp [lHC, hj]
theorem cTd {F : MvPolynomial (Fin 3) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) (b c : Fin 3) (p : PP)
    (hb : p.rep b ≠ 0) (hc : p.rep c ≠ 0) :
    cTTLR b c p hb hc (deh c F) =
      (↑((lCDU b c p hb hc)⁻¹) : CLR b p) ^ d *
        algebraMap (MvPolynomial (CV b) ℂ) (CLR b p)
          (deh b F) := by
  let u := lCDU b c p hb hc
  have hu : (↑(u⁻¹) : CLR b p) * lHC b p c = 1 := by
    rw [← lCDUv b c p hb hc]
    exact Units.inv_mul u
  change MvPolynomial.eval₂ _
    (fun j : CV c => (↑(u⁻¹) : CLR b p) *
      lHC b p j.val) (deh c F) = _
  rw [ed _
    (fun j : Fin 3 => (↑(u⁻¹) : CLR b p) * lHC b p j) c hu]
  rw [W16.hes1 hF]
  rw [elHC]
theorem rElHC (b : Fin 3) (p : PP)
    (hb : p.rep b ≠ 0) (j : Fin 3) :
    AM.rE (cC b p)
      (lHC b p j) = p.rep j / p.rep b := by
  by_cases hj : j = b
  · subst j
    simp [lHC, hb]
  · simp [lHC, hj, cC]
theorem cTrE (b c : Fin 3) (p : PP)
    (hb : p.rep b ≠ 0) (hc : p.rep c ≠ 0)
    (f : MvPolynomial (CV c) ℂ) :
    AM.rE (cC b p)
      (cTTLR b c p hb hc f) =
        MvPolynomial.eval (cC c p) f := by
  let ρ := AM.rE (cC b p)
  let e := cTTLR b c p hb hc
  let u := lCDU b c p hb hc
  have hu : ρ (↑u : CLR b p) = p.rep c / p.rep b := by
    rw [lCDUv]
    exact rElHC b p hb c
  have he : ρ.comp e = MvPolynomial.eval (cC c p) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [ρ, e, cTTLR]
    · intro j
      simp only [RingHom.comp_apply, e, cTTLR,
        MvPolynomial.eval₂Hom_X', MvPolynomial.eval_X]
      change ρ ((↑(u⁻¹) : CLR b p) *
        lHC b p j.val) = p.rep j.val / p.rep c
      rw [map_mul, map_units_inv, hu,
        rElHC b p hb j.val]
      rw [mul_comm, ← div_eq_mul_inv, div_div_div_cancel_right₀ hb]
  exact RingHom.congr_fun he f
theorem oALmi {σ K R : Type*} [CommRing K] [CommRing R]
    (p : σ → K) (e : MvPolynomial σ K →+* R) (ρ : R →+* K)
    (he : ∀ f, ρ (e f) = MvPolynomial.eval p f)
    (m : ℕ) (f : MvPolynomial σ K)
    (hf : AM.oAL p m f) :
    e f ∈ (RingHom.ker ρ) ^ m := by
  have hle : AM.pointIdeal p ≤ Ideal.comap e (RingHom.ker ρ) := by
    intro g hg
    change ρ (e g) = 0
    rw [he]
    exact (AM.pImi p g).mp hg
  have hp : f ∈ (Ideal.comap e (RingHom.ker ρ)) ^ m :=
    Ideal.pow_right_mono hle m hf
  exact Ideal.le_comap_pow e m hp
theorem cotvr {F : MvPolynomial (Fin 3) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) (b c : Fin 3) (p : PP)
    (hb : p.rep b ≠ 0) (hc : p.rep c ≠ 0) (m : ℕ)
    (ρ : CLR b p →+* ℂ)
    (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal (CLR b p))
    (heval : ∀ f, ρ (cTTLR b c p hb hc f) =
      MvPolynomial.eval (cC c p) f)
    (hf : AM.oAL (cC c p) m (deh c F)) :
    AM.oAL (cC b p) m (deh b F) := by
  have hmap := oALmi (cC c p)
    (cTTLR b c p hb hc) ρ heval m (deh c F) hf
  rw [hker, cTd hF b c p hb hc] at hmap
  have hunit : IsUnit ((↑((lCDU b c p hb hc)⁻¹) :
      CLR b p) ^ d) :=
    ((lCDU b c p hb hc)⁻¹).isUnit.pow d
  have hbare := (Ideal.unit_mul_mem_iff_mem
    (IsLocalRing.maximalIdeal (CLR b p) ^ m) hunit).mp hmap
  exact (AM.lOALi (cC b p) m
    (deh b F)).mp hbare
theorem cot {F : MvPolynomial (Fin 3) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) (b c : Fin 3) (p : PP)
    (hb : p.rep b ≠ 0) (hc : p.rep c ≠ 0) (m : ℕ)
    (hf : AM.oAL (cC c p) m (deh c F)) :
    AM.oAL (cC b p) m (deh b F) :=
  cotvr hF b c p hb hc m
    (AM.rE (cC b p))
    (AM.krE (cC b p))
    (cTrE b c p hb hc) hf
theorem mALic {F : MvPolynomial (Fin 3) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) (p : PP) (c : Fin 3) (hc : p.rep c ≠ 0) (m : ℕ) :
    mAL F p m ↔
      AM.oAL (cC c p) m (deh c F) := by
  constructor
  · intro h
    exact h c hc
  · intro h b hb
    exact cot hF b c p hb hc m h
end Nagata.PG
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W16
open Nagata.PG
abbrev HFS (d : ℕ) :=
  ↥(MvPolynomial.homogeneousSubmodule (Fin 3) ℂ d)
abbrev PEC (d : ℕ) := Projectivization ℂ (HFS d)
structure PPE where
  degree : ℕ
  degree_pos : 0 < degree
  equationClass : PEC degree
def fV {d : ℕ} (F : NHF d) : HFS d :=
  ⟨F.polynomial, F.homogeneous⟩
theorem fVnz {d : ℕ} (F : NHF d) : fV F ≠ 0 := by
  intro h
  exact F.nonzero (congrArg Subtype.val h)
def cOF {d : ℕ} (F : NHF d) : PEC d :=
  Projectivization.mk ℂ (fV F) (fVnz F)
def cR {d : ℕ} (C : PEC d) : NHF d where
  polynomial := C.rep.val
  homogeneous := C.rep.property
  nonzero := by
    intro h
    apply C.rep_nonzero
    exact Subtype.ext h
theorem rtD {d : ℕ} (C : PEC d) :
    (cR C).polynomial.totalDegree = d :=
  (cR C).tDe
end Nagata.W16
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W10
open Nagata.Workers.W30 Nagata.W16 MvPolynomial
noncomputable local instance oaiLocInst6 {σ R : Type*} [CommSemiring R] : GradedAlgebra (MvPolynomial.homogeneousSubmodule σ R) := MvPolynomial.gradedAlgebra
def EPC := {D : Ideal TP →₀ ℕ //
  D ≠ 0 ∧ ∀ I ∈ D.support, I.IsPrime ∧ I ≠ ⊥ ∧ I.IsPrincipal ∧
    I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)}
def cOE (E : PPE) : EPC :=
  ⟨eIC (cR E.equationClass).polynomial, by
    constructor
    · intro hzero
      obtain ⟨u, hu⟩ := (eICzi (cR E.equationClass).nonzero).mp hzero
      have hd0 : (cR E.equationClass).polynomial.totalDegree = 0 := by
        rw [← hu]
        exact uptD u
      exact (Nat.ne_of_gt E.degree_pos) ((rtD E.equationClass).symm.trans hd0)
    · intro I hI
      have hp := eICs _ hI
      exact ⟨hp.1, hp.2.1, hp.2.2,
        eICh (cR E.equationClass).nonzero
          (cR E.equationClass).homogeneous hI⟩⟩
end Nagata.Workers.W10
end
end
section
noncomputable section
namespace Nagata.Workers.W10
open Nagata.Workers.W30 Nagata.W16
def cOF1 {d : ℕ} (F : NHF d) (hd : 0 < d) : EPC :=
  cOE ⟨d, hd, cOF F⟩
end Nagata.Workers.W10
end
end
section
noncomputable section
namespace Nagata.Workers.W10
open Nagata.W16
def cLF : NHF 1 :=
  ⟨MvPolynomial.X (0 : Fin 3), MvPolynomial.isHomogeneous_X ℂ _, MvPolynomial.X_ne_zero (0 : Fin 3)⟩
def cLC : EPC := cOF1 cLF zero_lt_one
instance effectivePlaneCurveNonempty : Nonempty EPC := ⟨cLC⟩
end Nagata.Workers.W10
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
open scoped BigOperators
namespace Nagata.W15
open Nagata.Workers.W10 Nagata.Workers.W30 Nagata.PG
noncomputable local instance oaiLocInst7 {σ R : Type*} [CommSemiring R] : GradedAlgebra (MvPolynomial.homogeneousSubmodule σ R) := MvPolynomial.gradedAlgebra
end Nagata.W15
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W28
abbrev CP := ℂ × ℂ
def pPE (G : MvPolynomial (Fin 2) ℂ) (z : CP) : ℂ :=
  MvPolynomial.eval (fun i => if i = 0 then z.1 else z.2) G
def pNC (G : MvPolynomial (Fin 2) ℂ)
    (z : CP) : CP := (z.1, pPE G z)
theorem pPEaA (G : MvPolynomial (Fin 2) ℂ)
    (p : CP) : AnalyticAt ℂ (pPE G) p := by
  obtain ⟨q, hq, hz⟩ := poiao G p 0
    (Nagata.AM.oALz _ _)
  exact hq.analyticAt
theorem pNCaA (G : MvPolynomial (Fin 2) ℂ)
    (p : CP) : AnalyticAt ℂ (pNC G) p := by
  exact ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt p).prod
    (pPEaA G p)
theorem eanc
    (G : MvPolynomial (Fin 2) ℂ) (p : CP)
    (hdet : (fderiv ℂ (pNC G) p).det ≠ 0) :
    ∃ e : OpenPartialHomeomorph CP CP,
      (e : CP → CP) = pNC G ∧
      p ∈ e.source ∧
      AnalyticAt ℂ e.symm (pNC G p) := by
  let D := fderiv ℂ (pNC G) p
  let L : CP ≃L[ℂ] CP :=
    D.toContinuousLinearEquivOfDetNeZero hdet
  have hL : (L : CP →L[ℂ] CP) = D :=
    D.coe_toContinuousLinearEquivOfDetNeZero hdet
  have ha := pNCaA G p
  have hd : HasStrictFDerivAt (pNC G)
      (L : CP →L[ℂ] CP) p := by
    rw [hL]
    exact ha.hasStrictFDerivAt
  let e := hd.toOpenPartialHomeomorph (pNC G)
  have he : (e : CP → CP) = pNC G := rfl
  have hp : p ∈ e.source := hd.mem_toOpenPartialHomeomorph_source
  refine ⟨e, he, hp, ?_⟩
  have hi : AnalyticAt ℂ e.symm (e p) :=
    e.analyticAt_symm' hp (by simpa only [he] using ha) (by simpa only [he] using hL.symm)
  simpa only [he] using hi
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology
theorem poiri
    (P : MvPolynomial (Fin 2) ℂ)
    (e : OpenPartialHomeomorph CP CP)
    (s : ℂ) (q : CP) (m : ℕ)
    (he : AnalyticAt ℂ e.symm (aNS s q))
    (hP : Nagata.AM.oAL
      (fun i : Fin 2 => if i = 0 then (e.symm (aNS s q)).1
        else (e.symm (aNS s q)).2) m P) :
    HAOAL (𝕜 := ℂ)
      ((pPE P ∘ e.symm) ∘ aNS s) q m := by
  have h := poiao P (e.symm (aNS s q)) m hP
  exact (h.comp he).comp (aNSaA s q)
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
def pG (G : MvPolynomial (Fin 2) ℂ) (p : CP) :
    CP →L[ℂ] ℂ :=
  pPE (MvPolynomial.pderiv 0 G) p • ContinuousLinearMap.fst ℂ ℂ ℂ +
  pPE (MvPolynomial.pderiv 1 G) p • ContinuousLinearMap.snd ℂ ℂ ℂ
theorem pPEhF (G : MvPolynomial (Fin 2) ℂ)
    (p : CP) :
    HasFDerivAt (pPE G) (pG G p) p := by
  induction G using MvPolynomial.induction_on with
  | C a =>
      have hf : pPE (MvPolynomial.C a) = fun _ : CP => a := by
        funext z
        simp [pPE]
      have hg : pG (MvPolynomial.C a) p = 0 := by
        apply ContinuousLinearMap.ext
        intro z
        simp [pG, pPE]
      rw [hf, hg]
      exact hasFDerivAt_const (𝕜 := ℂ) a p
  | add P Q hP hQ =>
      have hf : pPE (P + Q) = fun z => pPE P z + pPE Q z := by
        funext z
        simp [pPE]
      have hg : pG (P + Q) p = pG P p + pG Q p := by
        apply ContinuousLinearMap.ext
        intro z
        simp [pG, pPE]
        ring
      rw [hf, hg]
      exact hP.add hQ
  | mul_X P i hP =>
      fin_cases i
      · have hf : pPE (P * MvPolynomial.X 0) = fun z => pPE P z * z.1 := by
          funext z
          simp [pPE]
        have hg : pG (P * MvPolynomial.X 0) p =
            pPE P p • ContinuousLinearMap.fst ℂ ℂ ℂ +
              p.1 • pG P p := by
          apply ContinuousLinearMap.ext
          intro z
          simp [pG, pPE]
          ring
        change HasFDerivAt (pPE (P * MvPolynomial.X (0 : Fin 2))) (pG (P * MvPolynomial.X (0 : Fin 2)) p) p
        rw [hf, hg]
        exact hP.mul ((ContinuousLinearMap.fst ℂ ℂ ℂ).hasFDerivAt (x := p))
      · have hf : pPE (P * MvPolynomial.X 1) = fun z => pPE P z * z.2 := by
          funext z
          simp [pPE]
        have hg : pG (P * MvPolynomial.X 1) p =
            pPE P p • ContinuousLinearMap.snd ℂ ℂ ℂ +
              p.2 • pG P p := by
          apply ContinuousLinearMap.ext
          intro z
          simp [pG, pPE]
          ring
        change HasFDerivAt (pPE (P * MvPolynomial.X (1 : Fin 2))) (pG (P * MvPolynomial.X (1 : Fin 2)) p) p
        rw [hf, hg]
        exact hP.mul ((ContinuousLinearMap.snd ℂ ℂ ℂ).hasFDerivAt (x := p))
theorem pNChF
    (G : MvPolynomial (Fin 2) ℂ) (p : CP) :
    HasFDerivAt (pNC G)
      ((ContinuousLinearMap.fst ℂ ℂ ℂ).prod (pG G p)) p :=
  ((ContinuousLinearMap.fst ℂ ℂ ℂ).hasFDerivAt).prodMk
    (pPEhF G p)
theorem pNCd
    (G : MvPolynomial (Fin 2) ℂ) (p : CP) :
    (fderiv ℂ (pNC G) p).det =
      pPE (MvPolynomial.pderiv 1 G) p := by
  rw [(pNChF G p).fderiv]
  change LinearMap.det
    (((ContinuousLinearMap.fst ℂ ℂ ℂ).prod (pG G p)).toLinearMap) = _
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℂ)]
  rw [Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, pG,
    Module.Basis.coe_finTwoProd_repr]
theorem eanco
    (G : MvPolynomial (Fin 2) ℂ) (p : CP)
    (hpartial : pPE (MvPolynomial.pderiv 1 G) p ≠ 0) :
    ∃ e : OpenPartialHomeomorph CP CP,
      (e : CP → CP) = pNC G ∧
      p ∈ e.source ∧
      AnalyticAt ℂ e.symm (pNC G p) := by
  apply eanc G p
  rwa [pNCd]
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
theorem ince
    (G : MvPolynomial (Fin 2) ℂ)
    (e : OpenPartialHomeomorph CP CP)
    (he : (e : CP → CP) = pNC G)
    (q : CP) (hq : q ∈ e.target) : pPE G (e.symm q) = q.2 := by
  have h := congrArg Prod.snd (e.right_inv hq)
  simpa only [he, pNC] using h
theorem rince
    (G : MvPolynomial (Fin 2) ℂ)
    (e : OpenPartialHomeomorph CP CP)
    (he : (e : CP → CP) = pNC G)
    (s : ℂ) (q : CP) (hq : aNS s q ∈ e.target) :
    pPE G (e.symm (aNS s q)) = s * q.2 :=
  ince G e he (aNS s q) hq
end Nagata.Workers.W28
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W18
open scoped BigOperators
theorem eiod (s : Finset ℕ) (j : ℕ → ℕ) (u : ℕ)
    (hweight : ∀ a ∈ s, a + j a = u) :
    Set.InjOn j (↑s : Set ℕ) := by
  intro a ha b hb hab
  apply @Nat.add_right_cancel a (j a) b
  calc
    a + j a = u := hweight a ha
    _ = b + j b := (hweight b hb).symm
    _ = b + j a := congrArg (fun n => b + n) hab.symm
theorem coims {R : Type*} [Semiring R]
    (s : Finset ℕ) (j : ℕ → ℕ) (c : ℕ → R)
    (hinj : Set.InjOn j (↑s : Set ℕ)) (a : ℕ) (ha : a ∈ s) :
    (∑ b ∈ s, Polynomial.monomial (j b) (c b)).coeff (j a) = c a := by
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single a]
  · exact Polynomial.coeff_monomial_same _ _
  · intro b hb hba
    apply Polynomial.coeff_monomial_of_ne
    intro hab
    exact hba (hinj hb ha hab.symm)
  · intro h
    exact (h ha).elim
theorem imsnz {R : Type*} [Semiring R]
    (s : Finset ℕ) (j : ℕ → ℕ) (c : ℕ → R)
    (hinj : Set.InjOn j (↑s : Set ℕ))
    (hcoeff : ∃ a ∈ s, c a ≠ 0) :
    (∑ b ∈ s, Polynomial.monomial (j b) (c b)) ≠ 0 := by
  obtain ⟨a, ha, hca⟩ := hcoeff
  intro hz
  apply hca
  calc
    c a = (∑ b ∈ s, Polynomial.monomial (j b) (c b)).coeff (j a) :=
      (coims s j c hinj a ha).symm
    _ = 0 := by rw [hz, Polynomial.coeff_zero]
theorem dmsnz {R : Type*} [Semiring R]
    (s : Finset ℕ) (j : ℕ → ℕ) (c : ℕ → R) (u : ℕ)
    (hweight : ∀ a ∈ s, a + j a = u)
    (hne : s.Nonempty) (hcoeff : ∀ a ∈ s, c a ≠ 0) :
    (∑ b ∈ s, Polynomial.monomial (j b) (c b)) ≠ 0 := by
  obtain ⟨a, ha⟩ := hne
  exact imsnz s j c
    (eiod s j u hweight) ⟨a, ha, hcoeff a ha⟩
theorem elwp {R : Type*} [Semiring R]
    (s : Finset ℕ) (j : ℕ → ℕ) (c : ℕ → R)
    (hne : s.Nonempty) (hcoeff : ∀ a ∈ s, c a ≠ 0) :
    ∃ u : ℕ,
      (∀ a ∈ s, u ≤ a + j a) ∧
      (s.filter (fun a => a + j a = u)).Nonempty ∧
      (∑ b ∈ s.filter (fun a => a + j a = u),
        Polynomial.monomial (j b) (c b)) ≠ 0 := by
  obtain ⟨a, ha, hmin⟩ := s.exists_min_image (fun b => b + j b) hne
  let u := a + j a
  have hselected : (s.filter (fun b => b + j b = u)).Nonempty :=
    ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
  refine ⟨u, hmin, hselected, ?_⟩
  apply dmsnz _ j c u
  · intro b hb
    exact (Finset.mem_filter.mp hb).2
  · exact hselected
  · intro b hb
    exact hcoeff b (Finset.mem_filter.mp hb).1
end Nagata.W18
end
section
noncomputable section
namespace Nagata.W18
theorem npv {K ι : Type*} [Field K]
    (p : ι → Polynomial K) (hp : p ≠ 0) :
    ∃ n : ℕ, ∃ q : ι → Polynomial K,
      (∀ i, p i = Polynomial.X ^ n * q i) ∧
      ∃ i, (q i).coeff 0 ≠ 0 := by
  classical
  have hex : ∃ n : ℕ, ∃ i, (p i).coeff n ≠ 0 := by
    by_contra h
    apply hp
    funext i
    apply Polynomial.ext
    intro n
    have hn : (p i).coeff n = 0 := by
      by_contra hn
      exact h ⟨n, i, hn⟩
    simpa only [Pi.zero_apply, Polynomial.coeff_zero] using hn
  let n := Nat.find hex
  have hsmall : ∀ k < n, ∀ i, (p i).coeff k = 0 := by
    intro k hk i
    by_contra hki
    exact (Nat.find_min hex hk) ⟨i, hki⟩
  have hdiv : ∀ i, Polynomial.X ^ n ∣ p i := by
    intro i
    exact Polynomial.X_pow_dvd_iff.mpr (fun k hk => hsmall k hk i)
  choose q hq using hdiv
  refine ⟨n, q, hq, ?_⟩
  obtain ⟨i, hi⟩ := Nat.find_spec hex
  refine ⟨i, ?_⟩
  intro hzero
  obtain ⟨r, hr⟩ := Polynomial.X_dvd_iff.mpr hzero
  have hdivsucc : Polynomial.X ^ (n + 1) ∣ p i := by
    refine ⟨r, ?_⟩
    rw [hq i, hr, pow_succ, mul_assoc]
  exact hi (Polynomial.X_pow_dvd_iff.mp hdivsucc n (Nat.lt_succ_self n))
theorem npk {K ι κ : Type*} [Field K] [Fintype ι]
    (A : Matrix κ ι (Polynomial K)) (p : ι → Polynomial K)
    (hp : p ≠ 0) (hAp : A.mulVec p = 0) :
    ∃ n : ℕ, ∃ q : ι → Polynomial K,
      (∀ i, p i = Polynomial.X ^ n * q i) ∧
      (∃ i, (q i).coeff 0 ≠ 0) ∧ A.mulVec q = 0 := by
  obtain ⟨n, q, hq, hqzero⟩ := npv p hp
  refine ⟨n, q, hq, hqzero, ?_⟩
  have hpeq : p = (Polynomial.X : Polynomial K) ^ n • q := by
    funext i
    exact hq i
  rw [hpeq, Matrix.mulVec_smul] at hAp
  funext k
  exact (mul_eq_zero.mp (congrFun hAp k)).resolve_left
    (pow_ne_zero n Polynomial.X_ne_zero)
end Nagata.W18
end
end
section
noncomputable section
open scoped BigOperators
namespace Nagata.W18
theorem cfd {R : Type*} [CommRing R] [IsDomain R]
    {ι : Type*} [Finite ι] (v : ι → FractionRing R) :
    ∃ d : R, d ≠ 0 ∧ ∃ p : ι → R,
      ∀ i, algebraMap R (FractionRing R) (p i) =
        algebraMap R (FractionRing R) d * v i := by
  classical
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors R) v
  choose p hp using hd
  refine ⟨d, nonZeroDivisors.coe_ne_zero d, p, ?_⟩
  intro i
  simpa only [Algebra.smul_def] using hp i
theorem msi {R K : Type*} [CommRing R] [CommRing K]
    {ι : Type*} [DecidableEq ι] (f : R →+* K) (d : R) :
    (d • (1 : Matrix ι ι R)).map f = f d • (1 : Matrix ι ι K) := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.map_apply, h, smul_eq_mul]
theorem psli {R : Type*} [CommRing R] [IsDomain R]
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix κ ι R)
    (hinj : Function.Injective (A.map (algebraMap R (FractionRing R))).mulVec) :
    ∃ d : R, d ≠ 0 ∧ ∃ D : Matrix ι κ R, D * A = d • (1 : Matrix ι ι R) := by
  classical
  let f := algebraMap R (FractionRing R)
  obtain ⟨g, hg⟩ := (Matrix.toLin' (A.map f)).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hinj)
  let C := LinearMap.toMatrix' g
  have hC : C * A.map f = 1 := by
    simpa only [C, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_id] using congrArg LinearMap.toMatrix' hg
  obtain ⟨d, hd, p, hp⟩ := cfd (fun z : ι × κ => C z.1 z.2)
  let D : Matrix ι κ R := fun i k => p (i, k)
  have hD : D.map f = f d • C := by
    ext i k
    exact hp (i, k)
  refine ⟨d, hd, D, ?_⟩
  apply Matrix.map_injective (IsFractionRing.injective R (FractionRing R))
  change (D * A).map f = (d • (1 : Matrix ι ι R)).map f
  rw [Matrix.map_mul, hD, Matrix.smul_mul, hC, msi]
theorem cfk {R : Type*} [CommRing R] [IsDomain R]
    {ι κ : Type*} [Fintype ι] (A : Matrix κ ι R)
    (v : ι → FractionRing R) (hv : v ≠ 0)
    (hAv : (A.map (algebraMap R (FractionRing R))).mulVec v = 0) :
    ∃ p : ι → R, p ≠ 0 ∧ A.mulVec p = 0 := by
  classical
  let f := algebraMap R (FractionRing R)
  obtain ⟨d, hd, p, hp⟩ := cfd v
  have hfd : f d ≠ 0 := by
    intro hz
    exact hd (IsFractionRing.injective R (FractionRing R) (by simpa [f] using hz))
  have hmap : f ∘ p = f d • v := by
    funext i
    exact hp i
  refine ⟨p, ?_, ?_⟩
  · intro hpzero
    apply hv
    funext i
    have hi : f d * v i = 0 := by
      rw [← hp i, hpzero]
      exact map_zero f
    exact (mul_eq_zero.mp hi).resolve_left hfd
  · funext k
    apply IsFractionRing.injective R (FractionRing R)
    change f ((A.mulVec p) k) = f 0
    rw [RingHom.map_mulVec, hmap, Matrix.mulVec_smul, hAv]
    simp
theorem spk {K ι κ : Type*} [Field K] [Fintype ι]
    (A : Matrix κ ι (Polynomial K)) (p : ι → Polynomial K)
    (hp : A.mulVec p = 0) (s : K) :
    (A.map (Polynomial.evalRingHom s)).mulVec (fun i => (p i).eval s) = 0 := by
  funext k
  have h := RingHom.map_mulVec (Polynomial.evalRingHom s) A p k
  rw [hp] at h
  simpa only [Pi.zero_apply, map_zero, Polynomial.coe_evalRingHom,
    Function.comp_def] using h.symm
theorem epar {K : Type*} [Field K] [Infinite K]
    (E : Finset K) (d : Polynomial K) (hd : d ≠ 0) :
    ∃ s : K, s ∉ E ∧ d.eval s ≠ 0 := by
  obtain ⟨s, hs⟩ := (E.finite_toSet.union (Polynomial.finite_setOfPred_isRoot hd)).exists_notMem
  exact ⟨s, fun h => hs (Or.inl h), fun h => hs (Or.inr h)⟩
theorem rkogs
    {K : Type*} [Field K] [Infinite K]
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix κ ι (Polynomial K)) (E : Finset K)
    (hkernel : ∀ s ∉ E, ∃ v : ι → K, v ≠ 0 ∧
      (A.map (Polynomial.evalRingHom s)).mulVec v = 0) :
    ∃ v : ι → FractionRing (Polynomial K), v ≠ 0 ∧
      (A.map (algebraMap (Polynomial K) (FractionRing (Polynomial K)))).mulVec v = 0 := by
  classical
  by_contra hnone
  have hinj : Function.Injective
      (A.map (algebraMap (Polynomial K) (FractionRing (Polynomial K)))).mulVec := by
    have hker : LinearMap.ker
        (Matrix.mulVecLin (A.map (algebraMap (Polynomial K)
          (FractionRing (Polynomial K))))) = ⊥ := by
      apply Matrix.ker_mulVecLin_eq_bot_iff.mpr
      intro v hv
      by_contra hne
      exact hnone ⟨v, hne, hv⟩
    exact LinearMap.ker_eq_bot.mp hker
  obtain ⟨d, hd, D, hDA⟩ := psli A hinj
  obtain ⟨s, hsE, hds⟩ := epar E d hd
  obtain ⟨v, hv, hAv⟩ := hkernel s hsE
  let ev := Polynomial.evalRingHom s
  have hDAeval : D.map ev * A.map ev = d.eval s • (1 : Matrix ι ι K) := by
    have h := congrArg (fun M : Matrix ι ι (Polynomial K) => M.map ev) hDA
    change (D * A).map ev = (d • (1 : Matrix ι ι (Polynomial K))).map ev at h
    rw [Matrix.map_mul (f := ev), msi] at h
    exact h
  have hscalar : d.eval s • v = 0 := by
    calc
      d.eval s • v = (d.eval s • (1 : Matrix ι ι K)).mulVec v := by
        rw [Matrix.smul_mulVec, Matrix.one_mulVec]
      _ = (D.map ev * A.map ev).mulVec v := by rw [hDAeval]
      _ = (D.map ev).mulVec ((A.map ev).mulVec v) :=
        (Matrix.mulVec_mulVec _ _ _).symm
      _ = 0 := by rw [hAv, Matrix.mulVec_zero]
  apply hv
  funext i
  exact (mul_eq_zero.mp (congrFun hscalar i)).resolve_left hds
theorem pkogs
    {K : Type*} [Field K] [Infinite K]
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix κ ι (Polynomial K)) (E : Finset K)
    (hkernel : ∀ s ∉ E, ∃ v : ι → K, v ≠ 0 ∧
      (A.map (Polynomial.evalRingHom s)).mulVec v = 0) :
    ∃ p : ι → Polynomial K, p ≠ 0 ∧ A.mulVec p = 0 := by
  obtain ⟨v, hv, hAv⟩ := rkogs A E hkernel
  exact cfk A v hv hAv
end Nagata.W18
end
end
section
namespace Nagata.W18
theorem nkogs
    {K : Type*} [Field K] [Infinite K]
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix κ ι (Polynomial K)) (E : Finset K)
    (hkernel : ∀ s ∉ E, ∃ v : ι → K, v ≠ 0 ∧
      (A.map (Polynomial.evalRingHom s)).mulVec v = 0) :
    ∃ q : ι → Polynomial K, (∃ i, (q i).coeff 0 ≠ 0) ∧ A.mulVec q = 0 := by
  obtain ⟨p, hp, hAp⟩ := pkogs A E hkernel
  obtain ⟨n, q, _, hqzero, hAq⟩ := npk A p hp hAp
  exact ⟨q, hqzero, hAq⟩
end Nagata.W18
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W18
variable {K : Type*} [CommRing K]
def bTN : MvPolynomial (Fin 2) K →+* Polynomial (Polynomial K) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp Polynomial.C)
    ![Polynomial.C Polynomial.X, Polynomial.X]
def nTB : Polynomial (Polynomial K) →+* MvPolynomial (Fin 2) K :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0))
    (MvPolynomial.X 1)
theorem bTNcn :
    (bTN (K := K)).comp nTB = RingHom.id _ := by
  apply Polynomial.ringHom_ext
  · intro p
    have h : bTN.comp
        (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (0 : Fin 2))) =
        (Polynomial.C : Polynomial K →+* Polynomial (Polynomial K)) := by
      apply Polynomial.ringHom_ext
      · intro r
        simp [bTN]
      · simp [bTN]
    simpa [nTB] using RingHom.congr_fun h p
  · simp [nTB, bTN]
theorem ebTN (a c : K) (F : MvPolynomial (Fin 2) K) :
    ((bTN F).eval (Polynomial.C c)).eval a =
      MvPolynomial.eval ![a, c] F := by
  have h : (Polynomial.evalRingHom a).comp
      ((Polynomial.evalRingHom (Polynomial.C c)).comp bTN) =
      MvPolynomial.eval ![a, c] := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [bTN]
    · intro i
      fin_cases i <;> simp [bTN]
  exact RingHom.congr_fun h F
end Nagata.W18
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W06.LA
open Polynomial
open scoped BigOperators
def pE {K : Type*} [CommRing K] (P : Polynomial (Polynomial K)) (U Y : K) : K :=
  P.eval₂ (Polynomial.evalRingHom U) Y
variable {K : Type*} [Field K]
variable [CharZero K]
end Nagata.W06.LA
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W06
theorem eosei {x y : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (hy0 : 0 < y) (hy1 : y < 1) (k : ℤ) (hk : x - y = k) : x = y := by
  have hlo : (-1 : ℝ) < (k : ℝ) := by linarith
  have hhi : (k : ℝ) < 1 := by linarith
  have hklo : (-1 : ℤ) < k := by exact_mod_cast hlo
  have hkhi : k < (1 : ℤ) := by exact_mod_cast hhi
  have hk_nonneg : 0 ≤ k := by simpa using Int.add_one_le_iff.mpr hklo
  have hk_nonpos : k ≤ 0 := Int.lt_add_one_iff.mp hkhi
  have hkzero : k = 0 := le_antisymm hk_nonpos hk_nonneg
  rw [hkzero, Int.cast_zero] at hk
  linarith
end Nagata.W06
end
end OAI
end
section
namespace OAI
section
namespace Nagata.Workers.W05
open Filter
open scoped Topology
theorem igl {a δ : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hδa : δ ≤ a) (hδ1 : δ ≤ 1 - a) (k : ℤ) : δ ≤ |(k : ℝ) - a| := by
  by_cases hk : k ≤ 0
  · have hkR : (k : ℝ) ≤ 0 := by exact_mod_cast hk
    rw [abs_of_nonpos (by linarith : (k : ℝ) - a ≤ 0)]
    linarith
  · have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
    rw [abs_of_nonneg (by linarith : 0 ≤ (k : ℝ) - a)]
    linarith
theorem ims {R L : ℝ} (hR : 0 < R) (hL : 2 * R < |L|)
    (k : ℤ) (hk : |(k : ℝ) * L| < 2 * R) : k = 0 := by
  rw [abs_mul] at hk
  have habs : |(k : ℝ)| < 1 := by
    by_contra hh
    have hge : 1 ≤ |(k : ℝ)| := le_of_not_gt hh
    nlinarith [abs_nonneg (k : ℝ)]
  have hkI : |k| < 1 := by exact_mod_cast habs
  have hkIbound := abs_lt.mp hkI
  omega
theorem ddb {R : ℝ} {x y : ℂ} (hx : ‖x‖ < R) (hy : ‖y‖ < R) :
    |(y - x).re| < 2 * R ∧ |(y - x).im| < 2 * R := by
  have hnorm : ‖y - x‖ < 2 * R := lt_of_le_of_lt (norm_sub_le y x) (by linarith)
  exact ⟨(Complex.abs_re_le_norm _).trans_lt hnorm,
    (Complex.abs_im_le_norm _).trans_lt hnorm⟩
theorem cdlu {R L : ℝ} (hR : 0 < R)
    (hRpi : R < Real.pi / 2) (hL : 2 * R < |L|) {x y : ℂ}
    (hx : ‖x‖ < R) (hy : ‖y‖ < R) (a b : ℤ)
    (hxy : y - x = (a : ℂ) * (L : ℂ) + (b : ℂ) * (2 * Real.pi * Complex.I)) :
    a = 0 ∧ b = 0 ∧ y = x := by
  obtain ⟨hre, him⟩ := ddb hx hy
  have heqre : (y - x).re = (a : ℝ) * L := by
    simpa using congrArg Complex.re hxy
  have heqim : (y - x).im = (b : ℝ) * (2 * Real.pi) := by
    simpa using congrArg Complex.im hxy
  have ha : a = 0 := ims hR hL a (heqre ▸ hre)
  have hpiper : 2 * R < |2 * Real.pi| := by
    rw [abs_of_pos (mul_pos (by norm_num) Real.pi_pos : 0 < 2 * Real.pi)]
    linarith [Real.pi_pos]
  have hb : b = 0 := ims hR hpiper b (heqim ▸ him)
  refine ⟨ha, hb, ?_⟩
  apply sub_eq_zero.mp
  simpa [ha, hb] using hxy
noncomputable def pP (τ : ℝ) (hτ : 0 < τ) : ℂˣ :=
  Units.mk0 (τ : ℂ) (by exact_mod_cast ne_of_gt hτ)
noncomputable def rP (τ s : ℝ) : ℂˣ :=
  Units.mk0 (Complex.exp ((s * Real.log τ : ℝ) : ℂ)) (Complex.exp_ne_zero _)
noncomputable def cP2 (τ x0 : ℝ) (x : ℂ) : ℂˣ :=
  Units.mk0 (Complex.exp ((x0 * Real.log τ : ℝ) : ℂ) * Complex.exp x)
    (mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _))
noncomputable def tC (τ : ℝ) (hτ : 0 < τ) (x0 : ℝ) (x : ℂ) :
    Nagata.W21.TP1 (pP τ hτ) :=
  Nagata.W21.tPM (pP τ hτ) (cP2 τ x0 x)
theorem eol {τ : ℝ} (hτ : 0 < τ) (x y : ℂ) (a : ℤ)
    (h : Complex.exp y = (τ : ℂ) ^ a * Complex.exp x) :
    ∃ b : ℤ, y - x = (a : ℂ) * (Real.log τ : ℂ) +
      (b : ℂ) * (2 * Real.pi * Complex.I) := by
  have hexp : Complex.exp y = Complex.exp ((a : ℂ) * (Real.log τ : ℂ) + x) := by
    rw [Complex.exp_add, Complex.exp_int_mul, ← Complex.ofReal_exp, Real.exp_log hτ]
    exact h
  obtain ⟨b, hb⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  refine ⟨b, ?_⟩
  rw [hb]
  ring
theorem tCiod {τ R : ℝ} (hτ : 0 < τ) (hR : 0 < R)
    (hRpi : R < Real.pi / 2) (hlog : 2 * R < |Real.log τ|) (x0 : ℝ) :
    Set.InjOn (tC τ hτ x0) {x : ℂ | ‖x‖ < R} := by
  intro x hx y hy hxy
  have horbit : Nagata.W21.tOS (pP τ hτ)
      (cP2 τ x0 x) (cP2 τ x0 y) := Quotient.exact hxy
  obtain ⟨a, ha⟩ := (Nagata.W21.tOSic _ _ _).mp horbit
  have he : Complex.exp y = (τ : ℂ) ^ a * Complex.exp x := by
    apply mul_left_cancel₀ (Complex.exp_ne_zero ((x0 * Real.log τ : ℝ) : ℂ))
    simpa only [cP2, pP, Units.val_mk0, mul_assoc, mul_left_comm] using ha
  obtain ⟨b, hb⟩ := eol hτ x y a he
  exact (cdlu hR hRpi hlog hx hy a b hb).2.2.symm
theorem tCam {τ R δ x0 xi : ℝ} (hτ : 0 < τ)
    (ha0 : 0 < x0 - xi) (ha1 : x0 - xi < 1)
    (hδa : δ ≤ x0 - xi) (hδ1 : δ ≤ 1 - (x0 - xi))
    (hmargin : R < δ * |Real.log τ|) {x : ℂ} (hx : ‖x‖ < R) :
    tC τ hτ x0 x ≠
      Nagata.W21.tPM (pP τ hτ) (rP τ xi) := by
  intro hq
  have horbit : Nagata.W21.tOS (pP τ hτ)
      (cP2 τ x0 x) (rP τ xi) := Quotient.exact hq
  obtain ⟨a, ha⟩ := (Nagata.W21.tOSic _ _ _).mp horbit
  have hexp : Complex.exp ((xi * Real.log τ : ℝ) : ℂ) =
      (τ : ℂ) ^ a * Complex.exp (((x0 * Real.log τ : ℝ) : ℂ) + x) := by
    simpa only [cP2, pP, rP, Units.val_mk0, Complex.exp_add] using ha
  obtain ⟨b, hb⟩ := eol hτ
    (((x0 * Real.log τ : ℝ) : ℂ) + x) ((xi * Real.log τ : ℝ) : ℂ) a hexp
  have hre : xi * Real.log τ - (x0 * Real.log τ + x.re) = (a : ℝ) * Real.log τ := by
    simpa using congrArg Complex.re hb
  have hxre : x.re = ((-a : ℤ) - (x0 - xi)) * Real.log τ := by
    push_cast
    nlinarith [hre]
  have hgap := igl ha0 ha1 hδa hδ1 (-a)
  have habs : δ * |Real.log τ| ≤ |x.re| := by
    rw [hxre, abs_mul]
    exact mul_le_mul_of_nonneg_right hgap (abs_nonneg _)
  have hsmall := (Complex.abs_re_le_norm x).trans_lt hx
  linarith
noncomputable def mGV (x0 : ℝ) (xi : Fin 9 → ℝ) : Finset ℝ := by
  classical
  exact Finset.univ.image (fun i => min (x0 - xi i) (1 - (x0 - xi i)))
theorem mGVn (x0 : ℝ) (xi : Fin 9 → ℝ) :
    (mGV x0 xi).Nonempty := by
  classical
  exact ⟨_, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
noncomputable def mG (x0 : ℝ) (xi : Fin 9 → ℝ) : ℝ :=
  (mGV x0 xi).min' (mGVn x0 xi)
theorem mGp (x0 : ℝ) (xi : Fin 9 → ℝ)
    (h : ∀ i, 0 < x0 - xi i ∧ x0 - xi i < 1) : 0 < mG x0 xi := by
  classical
  have hmem := Finset.min'_mem (mGV x0 xi) (mGVn x0 xi)
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
  change 0 < (mGV x0 xi).min' _
  rw [← hi]
  exact lt_min (h i).1 (by linarith [(h i).2])
theorem mGl (x0 : ℝ) (xi : Fin 9 → ℝ) (i : Fin 9) :
    mG x0 xi ≤ x0 - xi i ∧ mG x0 xi ≤ 1 - (x0 - xi i) := by
  classical
  have hi : min (x0 - xi i) (1 - (x0 - xi i)) ∈ mGV x0 xi :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hmin : mG x0 xi ≤ min (x0 - xi i) (1 - (x0 - xi i)) :=
    Finset.min'_le _ _ hi
  exact ⟨hmin.trans (min_le_left _ _), hmin.trans (min_le_right _ _)⟩
end Nagata.Workers.W05
end
section
namespace Nagata.Workers.W05
theorem rPerr {τ : ℝ} (hτ : 0 < τ) (s : ℝ) :
    (rP τ s : ℂ) = ((τ ^ s : ℝ) : ℂ) := by
  simp only [rP, Units.val_mk0, Real.rpow_def_of_pos hτ, Complex.ofReal_exp]
  congr 2
  ring
theorem cPerr {τ : ℝ} (hτ : 0 < τ) (x0 : ℝ) (x : ℂ) :
    (cP2 τ x0 x : ℂ) = ((τ ^ x0 : ℝ) : ℂ) * Complex.exp x := by
  change (rP τ x0 : ℂ) * Complex.exp x = _
  rw [rPerr hτ]
end Nagata.Workers.W05
end
section
namespace Nagata.W21
variable {R : Type*} [CommMonoid R]
section Topological
variable [TopologicalSpace R] [TopologicalSpace Rˣ]
  [IsTopologicalGroup Rˣ] [ContinuousSMul Rˣ R]
end Topological
end Nagata.W21
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W06.TC
open Nagata.Workers.W05
open Nagata.W21
open Filter
open scoped Topology
theorem rTPio {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) :
    Set.InjOn (fun s : ℝ => tPM (pP τ hτ) (rP τ s))
      (Set.Ioo 0 1) := by
  intro x hx y hy heq
  have horbit : tOS (pP τ hτ) (rP τ x) (rP τ y) :=
    Quotient.exact heq
  obtain ⟨a, ha⟩ := (tOSic _ _ _).mp horbit
  have he : Complex.exp ((y * Real.log τ : ℝ) : ℂ) =
      (τ : ℂ) ^ a * Complex.exp ((x * Real.log τ : ℝ) : ℂ) := by
    simpa only [pP, rP, Units.val_mk0] using ha
  obtain ⟨b, hb⟩ := eol hτ
    ((x * Real.log τ : ℝ) : ℂ) ((y * Real.log τ : ℝ) : ℂ) a he
  have hre : y * Real.log τ - x * Real.log τ = (a : ℝ) * Real.log τ := by
    simpa using congrArg Complex.re hb
  have hlog : Real.log τ ≠ 0 := ne_of_lt (Real.log_neg hτ hτ1)
  have hdiff : y - x = (a : ℝ) := by
    apply mul_right_cancel₀ hlog
    nlinarith [hre]
  exact (Nagata.W06.eosei hy.1 hy.2 hx.1 hx.2 a hdiff).symm
def cT (τ x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ) :
    Fin (9 + q) → ℂˣ :=
  fun t => Sum.elim (fun i => rP τ (xi i)) (fun j => cP2 τ x0 (ξ j))
    ((finSumFinEquiv : Fin 9 ⊕ Fin q ≃ Fin (9 + q)).symm t)
def tT (τ : ℝ) (hτ : 0 < τ) (x0 : ℝ) (xi : Fin 9 → ℝ)
    {q : ℕ} (ξ : Fin q → ℂ) : Fin (9 + q) → TP1 (pP τ hτ) :=
  fun t => tPM (pP τ hτ) (cT τ x0 xi ξ t)
@[simp] theorem cTl (τ x0 : ℝ) (xi : Fin 9 → ℝ)
    {q : ℕ} (ξ : Fin q → ℂ) (i : Fin 9) :
    cT τ x0 xi ξ (finSumFinEquiv (Sum.inl i)) = rP τ (xi i) := by
  simp [cT]
@[simp] theorem cTr (τ x0 : ℝ) (xi : Fin 9 → ℝ)
    {q : ℕ} (ξ : Fin q → ℂ) (i : Fin q) :
    cT τ x0 xi ξ (finSumFinEquiv (Sum.inr i)) = cP2 τ x0 (ξ i) := by
  simp [cT]
@[simp] theorem tTl (τ : ℝ) (hτ : 0 < τ) (x0 : ℝ) (xi : Fin 9 → ℝ)
    {q : ℕ} (ξ : Fin q → ℂ) (i : Fin 9) :
    tT τ hτ x0 xi ξ (finSumFinEquiv (Sum.inl i)) =
      tPM (pP τ hτ) (rP τ (xi i)) := by
  unfold tT
  rw [cTl]
@[simp] theorem tTr (τ : ℝ) (hτ : 0 < τ) (x0 : ℝ) (xi : Fin 9 → ℝ)
    {q : ℕ} (ξ : Fin q → ℂ) (i : Fin q) :
    tT τ hτ x0 xi ξ (finSumFinEquiv (Sum.inr i)) = tC τ hτ x0 (ξ i) := by
  unfold tT tC
  rw [cTr]
theorem tTes (τ : ℝ) (hτ : 0 < τ) (x0 : ℝ) (xi : Fin 9 → ℝ)
    {q : ℕ} (ξ : Fin q → ℂ) (t : Fin (9 + q)) :
    tT τ hτ x0 xi ξ t =
      Sum.elim (fun i : Fin 9 => tPM (pP τ hτ) (rP τ (xi i)))
        (fun j : Fin q => tC τ hτ x0 (ξ j))
        ((finSumFinEquiv : Fin 9 ⊕ Fin q ≃ Fin (9 + q)).symm t) := by
  unfold tT cT
  cases (finSumFinEquiv : Fin 9 ⊕ Fin q ≃ Fin (9 + q)).symm t <;> rfl
theorem tTi {τ R : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    (xi : Fin 9 → ℝ) (hxi : Function.Injective xi)
    (hxi_bounds : ∀ i, 0 < xi i ∧ xi i < 1 / 2)
    (hR : 0 < R) (hRpi : R < Real.pi / 2) (hlog : 2 * R < |Real.log τ|)
    (hmargin : R < mG (1 / 2) xi * |Real.log τ|)
    {q : ℕ} (ξ : Fin q → ℂ) (hξ : Function.Injective ξ) (hξR : ∀ j, ‖ξ j‖ < R) :
    Function.Injective (tT τ hτ (1 / 2) xi ξ) := by
  have hfixed : Function.Injective (fun i : Fin 9 =>
      tPM (pP τ hτ) (rP τ (xi i))) := by
    intro i j hij
    apply hxi
    exact rTPio hτ hτ1
      ⟨(hxi_bounds i).1, by linarith [(hxi_bounds i).2]⟩
      ⟨(hxi_bounds j).1, by linarith [(hxi_bounds j).2]⟩ hij
  have hmoving : Function.Injective (fun j : Fin q => tC τ hτ (1 / 2) (ξ j)) := by
    intro i j hij
    exact hξ (tCiod hτ hR hRpi hlog (1 / 2) (hξR i) (hξR j) hij)
  have hcross : ∀ i : Fin 9, ∀ j : Fin q,
      tC τ hτ (1 / 2) (ξ j) ≠
        tPM (pP τ hτ) (rP τ (xi i)) := by
    intro i j
    have hb := hxi_bounds i
    exact tCam hτ (by linarith) (by linarith)
      (mGl (1 / 2) xi i).1 (mGl (1 / 2) xi i).2 hmargin (hξR j)
  have hsum : Function.Injective (Sum.elim
      (fun i : Fin 9 => tPM (pP τ hτ) (rP τ (xi i)))
      (fun j : Fin q => tC τ hτ (1 / 2) (ξ j))) := by
    intro a b hab
    cases a with
    | inl i =>
      cases b with
      | inl j => exact congrArg Sum.inl (hfixed hab)
      | inr j => exact False.elim (hcross i j hab.symm)
    | inr i =>
      cases b with
      | inl j => exact False.elim (hcross j i hab)
      | inr j => exact congrArg Sum.inr (hmoving hab)
  intro a b hab
  apply (finSumFinEquiv : Fin 9 ⊕ Fin q ≃ Fin (9 + q)).symm.injective
  apply hsum
  simpa only [tTes] using hab
end Nagata.W06.TC
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W08
theorem aSaA {τ γ : ℂ} {n : ℤ}
    (f : aS τ n γ) {z : ℂ} (hz : z ≠ 0) :
    AnalyticAt ℂ f.val z := by
  have hd : DifferentiableOn ℂ f.val {w : ℂ | w ≠ 0} :=
    fun w hw ↦ (f.property.2.1 w hw).differentiableWithinAt
  exact hd.analyticAt (isOpen_ne.mem_nhds hz)
theorem aSaON {τ γ : ℂ} {n : ℤ}
    (f : aS τ n γ) :
    AnalyticOnNhd ℂ f.val {z : ℂ | z ≠ 0} :=
  fun _ hz ↦ aSaA f hz
end Nagata.W08
end
section
namespace Nagata.CS
theorem ehq {τ γ δ : ℂ} {n s : ℤ}
    (hτ : τ ≠ 0) (hδ : δ ≠ 0)
    (f : Nagata.W08.aS τ n γ)
    (P : Nagata.W08.aS τ s δ) (k : ℕ)
    (hzero : ∀ z ≠ 0, P.val z = 0 → deriv P.val z ≠ 0 ∧
      (k : ℕ∞) ≤ analyticOrderAt f.val z) :
    ∃ G : Nagata.W08.aS τ (n - (k : ℤ) * s) (γ / δ ^ k),
      ∀ z ≠ 0, f.val z = P.val z ^ k * G.val z :=
  eaq hτ hδ f P
    (Nagata.W08.aSaON f)
    (Nagata.W08.aSaON P) k hzero
theorem elhc {τ L Q : ℂ}
    (hτ : τ ≠ 0) (hL : L ≠ 0) (hQ : Q ≠ 0)
    (d m j : ℤ) (hj : j ≤ m)
    (P : Nagata.W08.aS τ 9 Q)
    (f : Nagata.W08.aS τ (3 * (d - 3 * j)) (L ^ (d - 3 * j)))
    (hzero : ∀ z ≠ 0, P.val z = 0 → deriv P.val z ≠ 0 ∧
      ((m - j).toNat : ℕ∞) ≤ analyticOrderAt f.val z) :
    ∃ g ∈ cS τ L Q d m j P.val,
      ∀ z ≠ 0, f.val z = P.val z ^ (m - j).toNat * g z :=
  elc hτ hL hQ d m j hj P f
    (Nagata.W08.aSaON P)
    (Nagata.W08.aSaON f) hzero
end Nagata.CS
end
section
noncomputable section
namespace Nagata.W08
open Nagata.W21 Nagata.Workers.W05
theorem pPnlo {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) :
    ‖((pP τ hτ : ℂˣ) : ℂ)‖ < 1 := by
  change ‖(τ : ℂ)‖ < 1
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ] using hτone
end Nagata.W08
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W21
open Filter Topology
open scoped BigOperators
noncomputable def tP2 (τ z : ℂ) : ℂ :=
  ∏' n : ℕ, (1 - τ ^ n * z)
noncomputable def tP (τ z : ℂ) : ℂ :=
  tP2 τ z * tP2 τ (τ * z⁻¹)
theorem tPm {τ : ℂ} (hτ : ‖τ‖ < 1) (z : ℂ) :
    Multipliable (fun n : ℕ ↦ 1 - τ ^ n * z) := by
  simpa only [mul_neg, sub_eq_add_neg] using
    Complex.multipliable_one_add_of_summable
      ((summable_geometric_of_norm_lt_one hτ).mul_right (-z))
theorem tPs {τ : ℂ} (hτ : ‖τ‖ < 1) (z : ℂ) :
    tP2 τ z = (1 - z) * tP2 τ (τ * z) := by
  have hm : Multipliable (fun n : ℕ ↦ 1 - τ ^ (n + 1) * z) := by
    simpa only [pow_succ, mul_assoc] using tPm hτ (τ * z)
  simpa only [tP2, pow_zero, one_mul, pow_succ, mul_assoc] using
    tprod_eq_zero_mul' (f := fun n : ℕ ↦ 1 - τ ^ n * z) hm
theorem tPa {τ z : ℂ} (hτ : ‖τ‖ < 1)
    (hτ0 : τ ≠ 0) (hz : z ≠ 0) :
    tP τ (τ * z) = -z⁻¹ * tP τ z := by
  have hc : τ * (τ * z)⁻¹ = z⁻¹ := by
    rw [mul_inv_rev]
    calc
      τ * (z⁻¹ * τ⁻¹) = (τ * τ⁻¹) * z⁻¹ := by ac_rfl
      _ = z⁻¹ := by rw [mul_inv_cancel₀ hτ0, one_mul]
  have hb : 1 - z⁻¹ = -z⁻¹ * (1 - z) := by
    symm
    rw [mul_sub, mul_one, neg_mul, sub_neg_eq_add, inv_mul_cancel₀ hz, add_comm]
    exact (sub_eq_add_neg 1 z⁻¹).symm
  unfold tP
  rw [hc, tPs hτ z⁻¹, hb]
  calc
    tP2 τ (τ * z) * ((-z⁻¹ * (1 - z)) * tP2 τ (τ * z⁻¹)) =
        -z⁻¹ * (((1 - z) * tP2 τ (τ * z)) *
          tP2 τ (τ * z⁻¹)) := by ac_rfl
    _ = -z⁻¹ * (tP2 τ z * tP2 τ (τ * z⁻¹)) := by
      rw [← tPs hτ z]
theorem tPsa {τ a z : ℂ} (hτ : ‖τ‖ < 1)
    (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hz : z ≠ 0) :
    tP τ ((τ * z) / a) = (-a) * z⁻¹ * tP τ (z / a) := by
  simpa only [div_eq_mul_inv, mul_assoc, mul_inv_rev, inv_inv, neg_mul] using
    tPa hτ hτ0 (div_ne_zero hz ha)
theorem tPnz1 {τ : ℂ} (hτ : ‖τ‖ < 1) (z : ℂ)
    (hz : ∀ n : ℕ, 1 - τ ^ n * z ≠ 0) : tP2 τ z ≠ 0 := by
  have hn : Summable (fun n : ℕ ↦ ‖-(τ ^ n * z)‖) := by
    simpa only [norm_neg, norm_mul, norm_pow] using
      (summable_geometric_of_lt_one (norm_nonneg τ) hτ).mul_right ‖z‖
  have hf : ∀ n : ℕ, 1 + -(τ ^ n * z) ≠ 0 := by
    simpa only [sub_eq_add_neg] using hz
  simpa only [tP2, sub_eq_add_neg] using
    tprod_one_add_ne_zero_of_summable hf hn
theorem tPezi1 {τ : ℂ} (hτ : ‖τ‖ < 1) (z : ℂ) :
    tP2 τ z = 0 ↔ ∃ n : ℕ, τ ^ n * z = 1 := by
  classical
  constructor
  · intro hp
    by_contra hf
    have hn : ∀ n : ℕ, 1 - τ ^ n * z ≠ 0 := by
      intro n hn
      apply hf
      exact ⟨n, (sub_eq_zero.mp hn).symm⟩
    exact tPnz1 hτ z hn hp
  · rintro ⟨n, hn⟩
    exact tprod_of_exists_eq_zero (f := fun n : ℕ ↦ 1 - τ ^ n * z)
      ⟨n, by change 1 - τ ^ n * z = 0; rw [hn, sub_self]⟩
theorem tPezi2 {τ : ℂ} (hτ : ‖τ‖ < 1) (z : ℂ) :
    tP τ z = 0 ↔
      (∃ n : ℕ, τ ^ n * z = 1) ∨ (∃ n : ℕ, τ ^ n * (τ * z⁻¹) = 1) := by
  rw [tP, mul_eq_zero, tPezi1 hτ z,
    tPezi1 hτ (τ * z⁻¹)]
end Nagata.W21
end
section
namespace Nagata.W21
open Filter Topology
open scoped BigOperators
theorem tPhPU {α : Type*} [TopologicalSpace α]
    {τ : ℂ} (hτ : ‖τ‖ < 1) {K : Set α} (hK : IsCompact K)
    (g : α → ℂ) (hg : ContinuousOn g K) (R : ℝ)
    (hR : ∀ x ∈ K, ‖g x‖ ≤ R) :
    HasProdUniformlyOn (fun (n : ℕ) x ↦ 1 - τ ^ n * g x)
      (fun x ↦ tP2 τ (g x)) K := by
  have hu : Summable (fun n : ℕ ↦ ‖τ‖ ^ n * R) :=
    (summable_geometric_of_lt_one (norm_nonneg τ) hτ).mul_right R
  have hb : ∀ᶠ n : ℕ in atTop, ∀ x ∈ K, ‖-(τ ^ n * g x)‖ ≤ ‖τ‖ ^ n * R := by
    exact Eventually.of_forall fun n x hx ↦ by
      rw [norm_neg, norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (hR x hx) (pow_nonneg (norm_nonneg τ) n)
  have hc : ∀ n : ℕ, ContinuousOn (fun x ↦ -(τ ^ n * g x)) K :=
    fun n ↦ (continuousOn_const.mul hg).neg
  simpa only [sub_eq_add_neg, tP2] using
    Summable.hasProdUniformlyOn_nat_one_add hK hu hb hc
theorem tPhPL {τ : ℂ} (hτ : ‖τ‖ < 1) :
    HasProdLocallyUniformlyOn (fun (n : ℕ) (z : ℂ) ↦ 1 - τ ^ n * z)
      (tP2 τ) Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  exact tPhPU hτ hK (fun z ↦ z)
    continuousOn_id R hR
theorem tPd {τ : ℂ} (hτ : ‖τ‖ < 1) :
    Differentiable ℂ (tP2 τ) := by
  have hlim := (tPhPL hτ).tendstoLocallyUniformlyOn_finsetRange
  have hd : ∀ N : ℕ, DifferentiableOn ℂ
      (fun z ↦ ∏ n ∈ Finset.range N, (1 - τ ^ n * z)) Set.univ := by
    intro N
    exact DifferentiableOn.fun_finsetProd fun n _ ↦
      (differentiableOn_const (1 : ℂ)).sub ((differentiableOn_const (τ ^ n)).mul differentiableOn_id)
  exact differentiableOn_univ.mp
    (hlim.differentiableOn (Eventually.of_forall hd) isOpen_univ)
theorem tPdA {τ z : ℂ} (hτ : ‖τ‖ < 1) (hz : z ≠ 0) :
    DifferentiableAt ℂ (tP τ) z := by
  have hp := tPd hτ
  exact (hp z).mul ((hp (τ * z⁻¹)).fun_comp' z
    ((differentiableAt_const τ).mul (differentiableAt_inv hz)))
theorem tPpnz {τ : ℂ} (hτ : ‖τ‖ < 1) :
    tP2 τ τ ≠ 0 := by
  apply tPnz1 hτ τ
  intro n hn
  have he : τ ^ (n + 1) = 1 := by
    simpa only [pow_succ] using (sub_eq_zero.mp hn).symm
  have hlt : ‖τ ^ (n + 1)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg τ) hτ (Nat.succ_ne_zero n)
  rw [he, norm_one] at hlt
  exact (lt_irrefl (1 : ℝ)) hlt
theorem tPo {τ : ℂ} (hτ : ‖τ‖ < 1) : tP τ 1 = 0 := by
  rw [tP, tPs hτ 1]
  simp
theorem tPhDA {τ : ℂ} (hτ : ‖τ‖ < 1) :
    HasDerivAt (tP τ) (-(tP2 τ τ) ^ 2) 1 := by
  have hp := tPd hτ
  have hg : DifferentiableAt ℂ
      (fun z : ℂ ↦ tP2 τ (τ * z) * tP2 τ (τ * z⁻¹)) 1 :=
    ((hp (τ * 1)).fun_comp' 1 ((differentiableAt_const τ).mul differentiableAt_id)).mul
      ((hp (τ * (1 : ℂ)⁻¹)).fun_comp' 1
        ((differentiableAt_const τ).mul (differentiableAt_inv one_ne_zero)))
  have heq : tP τ = fun z : ℂ ↦
      (1 - z) * (tP2 τ (τ * z) * tP2 τ (τ * z⁻¹)) := by
    funext z
    rw [tP, tPs hτ z]
    exact mul_assoc _ _ _
  rw [heq]
  apply (((hasDerivAt_id' (x := (1 : ℂ))).const_sub 1).mul hg.hasDerivAt).congr_deriv
  simp [pow_two]
theorem tPdon {τ : ℂ} (hτ : ‖τ‖ < 1) :
    deriv (tP τ) 1 ≠ 0 := by
  rw [(tPhDA hτ).deriv]
  exact neg_ne_zero.mpr (pow_ne_zero 2 (tPpnz hτ))
end Nagata.W21
end
section
namespace Nagata.W21
theorem tPezi3 {τ z : ℂ} (hτ : ‖τ‖ < 1)
    (hτ0 : τ ≠ 0) (hz : z ≠ 0) :
    tP τ z = 0 ↔
      (∃ n : ℕ, z = (τ ^ n)⁻¹) ∨ (∃ n : ℕ, z = τ ^ (n + 1)) := by
  rw [tPezi2 hτ z]
  constructor
  · rintro (⟨n, hn⟩ | ⟨n, hn⟩)
    · exact Or.inl ⟨n, ((mul_eq_one_iff_inv_eq₀ (pow_ne_zero n hτ0)).mp hn).symm⟩
    · have he : τ ^ (n + 1) * z⁻¹ = 1 := by
        simpa only [pow_succ, mul_assoc] using hn
      exact Or.inr ⟨n, ((mul_inv_eq_one₀ hz).mp he).symm⟩
  · rintro (⟨n, hn⟩ | ⟨n, hn⟩)
    · exact Or.inl ⟨n, (mul_eq_one_iff_inv_eq₀ (pow_ne_zero n hτ0)).mpr hn.symm⟩
    · right
      refine ⟨n, ?_⟩
      have he : τ ^ (n + 1) * z⁻¹ = 1 := (mul_inv_eq_one₀ hz).mpr hn.symm
      simpa only [pow_succ, mul_assoc] using he
theorem tPezi {τ z : ℂ} (hτ : ‖τ‖ < 1)
    (hτ0 : τ ≠ 0) (hz : z ≠ 0) :
    tP τ z = 0 ↔ ∃ k : ℤ, z = τ ^ k := by
  rw [tPezi3 hτ hτ0 hz]
  constructor
  · rintro (⟨n, hn⟩ | ⟨n, hn⟩)
    · exact ⟨-(n : ℤ), by simpa only [zpow_neg, zpow_natCast] using hn⟩
    · exact ⟨((n + 1 : ℕ) : ℤ), by simpa only [zpow_natCast] using hn⟩
  · rintro ⟨k, rfl⟩
    cases k with
    | ofNat n =>
      cases n with
      | zero => exact Or.inl ⟨0, by simp⟩
      | succ n => exact Or.inr ⟨n, zpow_natCast τ (n + 1)⟩
    | negSucc n => exact Or.inl ⟨n + 1, by simp only [zpow_negSucc]⟩
theorem tPsez {τ a z : ℂ} (hτ : ‖τ‖ < 1)
    (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hz : z ≠ 0) :
    tP τ (z / a) = 0 ↔ ∃ k : ℤ, z = a * τ ^ k := by
  rw [tPezi hτ hτ0 (div_ne_zero hz ha)]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by simpa only [mul_comm] using (div_eq_iff ha).mp hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, (div_eq_iff ha).mpr (by simpa only [mul_comm] using hk)⟩
end Nagata.W21
end
section
namespace Nagata.W21
open Filter Topology
theorem tPzez {τ : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0)
    (k : ℤ) : tP τ (τ ^ k) = 0 :=
  (tPezi hτ hτ0 (zpow_ne_zero k hτ0)).mpr ⟨k, rfl⟩
theorem tPdma {τ z : ℂ} (hτ : ‖τ‖ < 1)
    (hτ0 : τ ≠ 0) (hz : z ≠ 0) (hzero : tP τ z = 0) :
    deriv (tP τ) (τ * z) * τ = -z⁻¹ * deriv (tP τ) z := by
  have hl := (tPdA hτ (mul_ne_zero hτ0 hz)).hasDerivAt.comp z
    (hasDerivAt_const_mul τ (x := z))
  have hr := (hasDerivAt_inv hz).neg.mul
    (tPdA hτ hz).hasDerivAt
  have heq : (fun w : ℂ ↦ tP τ (τ * w)) =ᶠ[𝓝 z]
      (fun w : ℂ ↦ -w⁻¹ * tP τ w) :=
    Filter.Eventually.mono (isOpen_ne.mem_nhds hz) fun w hw ↦
      tPa hτ hτ0 hw
  have he := (hl.congr_of_eventuallyEq heq.symm).unique hr
  simpa only [hzero, mul_zero, zero_add, Pi.neg_apply] using he
theorem tPdmn {τ z : ℂ} (hτ : ‖τ‖ < 1)
    (hτ0 : τ ≠ 0) (hz : z ≠ 0) (hzero : tP τ z = 0) :
    deriv (tP τ) (τ * z) ≠ 0 ↔ deriv (tP τ) z ≠ 0 := by
  have he := tPdma hτ hτ0 hz hzero
  constructor
  · intro hmul hd
    have hbad : deriv (tP τ) (τ * z) * τ = 0 := by
      rw [he, hd, mul_zero]
    exact (mul_ne_zero hmul hτ0) hbad
  · intro hd hmul
    have hbad : -z⁻¹ * deriv (tP τ) z = 0 := by
      rw [← he, hmul, zero_mul]
    exact (mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero hz)) hd) hbad
theorem tPdpn {τ : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0)
    (n : ℕ) : deriv (tP τ) (τ ^ n) ≠ 0 := by
  induction n with
  | zero => simpa only [pow_zero] using tPdon hτ
  | succ n ih =>
    have hz : tP τ (τ ^ n) = 0 := by
      simpa only [zpow_natCast] using tPzez hτ hτ0 (n : ℤ)
    have hd := (tPdmn hτ hτ0 (pow_ne_zero n hτ0) hz).mpr ih
    simpa only [pow_succ', Nat.succ_eq_add_one] using hd
theorem tPdip {τ : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0)
    (n : ℕ) : deriv (tP τ) ((τ ^ n)⁻¹) ≠ 0 := by
  induction n with
  | zero => simpa only [pow_zero, inv_one] using tPdon hτ
  | succ n ih =>
    have hz : tP τ ((τ ^ (n + 1))⁻¹) = 0 := by
      simpa only [zpow_neg, zpow_natCast] using
        tPzez hτ hτ0 (-((n + 1 : ℕ) : ℤ))
    have hm : τ * (τ ^ (n + 1))⁻¹ = (τ ^ n)⁻¹ := by
      rw [pow_succ, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hτ0, one_mul]
    have hd : deriv (tP τ) (τ * (τ ^ (n + 1))⁻¹) ≠ 0 := by
      rwa [hm]
    exact (tPdmn hτ hτ0
      (inv_ne_zero (pow_ne_zero (n + 1) hτ0)) hz).mp hd
theorem tPzhn {τ z : ℂ} (hτ : ‖τ‖ < 1)
    (hτ0 : τ ≠ 0) (hz : z ≠ 0) (hzero : tP τ z = 0) :
    deriv (tP τ) z ≠ 0 := by
  obtain ⟨k, rfl⟩ := (tPezi hτ hτ0 hz).mp hzero
  cases k with
  | ofNat n =>
    simpa only [Int.ofNat_eq_natCast, zpow_natCast] using tPdpn hτ hτ0 n
  | negSucc n =>
    simpa only [zpow_negSucc] using tPdip hτ hτ0 (n + 1)
end Nagata.W21
end
section
namespace Nagata.W21
open scoped BigOperators
noncomputable def mTP {ι : Type*} [Fintype ι] (τ : ℂ) (a : ι → ℂ)
    (z : ℂ) : ℂ := ∏ i, tP τ (z / a i)
theorem tPsdA {τ a z : ℂ} (hτ : ‖τ‖ < 1)
    (ha : a ≠ 0) (hz : z ≠ 0) : DifferentiableAt ℂ (fun w ↦ tP τ (w / a)) z :=
  (tPdA (τ := τ) (z := z / a) hτ (div_ne_zero hz ha)).fun_comp' z
    ((differentiableAt_id (𝕜 := ℂ) (x := z)).div_const a)
theorem mTPdA {ι : Type*} [Fintype ι]
    {τ : ℂ} {a : ι → ℂ} {z : ℂ} (hτ : ‖τ‖ < 1) (ha : ∀ i, a i ≠ 0)
    (hz : z ≠ 0) : DifferentiableAt ℂ (mTP τ a) z := by
  classical
  exact DifferentiableAt.fun_finsetProd fun i _ ↦
    tPsdA hτ (ha i) hz
theorem mTPez {ι : Type*} [Fintype ι]
    {τ : ℂ} {a : ι → ℂ} {z : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0)
    (ha : ∀ i, a i ≠ 0) (hz : z ≠ 0) :
    mTP τ a z = 0 ↔ ∃ i, ∃ k : ℤ, z = a i * τ ^ k := by
  classical
  simp only [mTP, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and,
    tPsez hτ hτ0 (ha _) hz]
theorem tPszh {τ a z : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hz : z ≠ 0)
    (hf : tP τ (z / a) = 0) :
    deriv (fun w ↦ tP τ (w / a)) z ≠ 0 := by
  have hd := (tPdA hτ (div_ne_zero hz ha)).hasDerivAt.comp z
    ((hasDerivAt_id z).div_const a)
  change HasDerivAt (fun w ↦ tP τ (w / a))
    (deriv (tP τ) (z / a) * (1 / a)) z at hd
  rw [hd.deriv]
  exact mul_ne_zero (tPzhn hτ hτ0 (div_ne_zero hz ha) hf)
    (div_ne_zero one_ne_zero ha)
theorem fPzhn {ι : Type*} [Fintype ι]
    (f : ι → ℂ → ℂ) (z : ℂ) (hf : ∀ i, DifferentiableAt ℂ (f i) z)
    (i : ι) (hi : f i z = 0) (hdi : deriv (f i) z ≠ 0)
    (hother : ∀ j, j ≠ i → f j z ≠ 0) :
    deriv (fun w ↦ ∏ j, f j w) z ≠ 0 := by
  classical
  let g : ℂ → ℂ := fun w ↦ ∏ j ∈ Finset.univ.erase i, f j w
  have hg : DifferentiableAt ℂ g z :=
    DifferentiableAt.fun_finsetProd fun j _ ↦ hf j
  have hgz : g z ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j hj ↦
    hother j (Finset.mem_erase.mp hj).1
  have heq : (fun w ↦ ∏ j, f j w) = (fun w ↦ f i w * g w) := by
    funext w
    exact (Finset.mul_prod_erase Finset.univ (fun j ↦ f j w) (Finset.mem_univ i)).symm
  rw [heq, deriv_fun_mul (hf i) hg, hi, zero_mul, add_zero]
  exact mul_ne_zero hdi hgz
theorem mTFuz {ι : Type*} {τ : ℂ} {a : ι → ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : ∀ i, a i ≠ 0)
    (hdisjoint : Pairwise (fun i j ↦ ∀ k : ℤ, a i ≠ a j * τ ^ k))
    {z : ℂ} (hz : z ≠ 0) {i j : ι} (hij : i ≠ j)
    (hi : tP τ (z / a i) = 0) : tP τ (z / a j) ≠ 0 := by
  intro hj
  obtain ⟨k, hk⟩ := (tPsez hτ hτ0 (ha i) hz).mp hi
  obtain ⟨l, hl⟩ := (tPsez hτ hτ0 (ha j) hz).mp hj
  apply hdisjoint hij (l - k)
  apply mul_right_cancel₀ (zpow_ne_zero k hτ0)
  rw [← hk, mul_assoc, ← zpow_add₀ hτ0, sub_add_cancel, ← hl]
theorem mTPzh {ι : Type*} [Fintype ι]
    {τ : ℂ} {a : ι → ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0)
    (ha : ∀ i, a i ≠ 0)
    (hdisjoint : Pairwise (fun i j ↦ ∀ k : ℤ, a i ≠ a j * τ ^ k))
    {z : ℂ} (hz : z ≠ 0) (hzero : mTP τ a z = 0) :
    deriv (mTP τ a) z ≠ 0 := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hzero
  exact fPzhn (fun j w ↦ tP τ (w / a j)) z
    (fun j ↦ tPsdA hτ (ha j) hz) i hi
    (tPszh hτ hτ0 (ha i) hz hi)
    (fun j hj ↦ mTFuz hτ hτ0 ha hdisjoint hz hj.symm hi)
end Nagata.W21
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W08
theorem ecn {ι : Type*} [Countable ι]
    (p : ι → Polynomial ℂ) (hp : ∀ i, p i ≠ 0) :
    ∃ b : ℂ, ∀ i, (p i).eval b ≠ 0 := by
  let : Uncountable ℂ := Cardinal.aleph0_lt_mk_iff.mp (by
    rw [Cardinal.mk_complex]
    exact Cardinal.cantor Cardinal.aleph0)
  let B : Set ℂ := ⋃ i, {b | (p i).IsRoot b}
  have hB : B.Countable := Set.countable_iUnion fun i =>
    (Polynomial.finite_setOfPred_isRoot (hp i)).countable
  have hex : ∃ b : ℂ, b ∉ B := by
    by_contra h
    have hu : B = Set.univ := Set.eq_univ_of_forall fun b =>
      Classical.not_not.mp (fun hb => h ⟨b, hb⟩)
    exact Set.not_countable_univ (hu ▸ hB)
  obtain ⟨b, hb⟩ := hex
  exact ⟨b, fun i hi => hb (Set.mem_iUnion.mpr ⟨i, hi⟩)⟩
open Polynomial in
theorem ecsm {τ a γ : ℂ} (hτ : τ ≠ 0) (ha : a ≠ 0) :
    ∃ b : ℂ, b ≠ 0 ∧
      (∀ k : ℤ, b ≠ a * τ ^ k) ∧
      (∀ k : ℤ, a ^ 2 * b * τ ^ k + γ ≠ 0) ∧
      (∀ k : ℤ, a * b ^ 2 * τ ^ k + γ ≠ 0) := by
  let p : Fin 4 × ℤ → Polynomial ℂ := fun i =>
    if i.1 = 0 then X else if i.1 = 1 then X - C (a * τ ^ i.2)
    else if i.1 = 2 then C (a ^ 2 * τ ^ i.2) * X + C γ
    else C (a * τ ^ i.2) * X ^ 2 + C γ
  have hp : ∀ i, p i ≠ 0 := by
    rintro ⟨j, k⟩ he
    fin_cases j
    · have hc := congrArg (fun q : Polynomial ℂ => q.coeff 1) he
      norm_num [p] at hc
    · have hc := congrArg (fun q : Polynomial ℂ => q.coeff 1) he
      norm_num [p] at hc
    · have hc := congrArg (fun q : Polynomial ℂ => q.coeff 1) he
      change (C (a ^ 2 * τ ^ k) * X + C γ).coeff 1 = (0 : Polynomial ℂ).coeff 1 at hc
      simp only [coeff_add, coeff_C_mul_X, coeff_C, coeff_zero] at hc
      norm_num [ha, zpow_ne_zero k hτ] at hc
    · have hc := congrArg (fun q : Polynomial ℂ => q.coeff 2) he
      change (C (a * τ ^ k) * X ^ 2 + C γ).coeff 2 = (0 : Polynomial ℂ).coeff 2 at hc
      simp only [coeff_add, coeff_C_mul_X_pow, coeff_C, coeff_zero] at hc
      norm_num [ha, zpow_ne_zero k hτ] at hc
  obtain ⟨b, hb⟩ := ecn p hp
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · simpa [p] using hb (0, 0)
  · intro k
    simpa [p, sub_ne_zero] using hb (1, k)
  · intro k
    simpa [p, mul_assoc, mul_left_comm, mul_comm] using hb (2, k)
  · intro k
    simpa [p, mul_assoc, mul_left_comm, mul_comm] using hb (3, k)
end Nagata.W08
end
end
section
noncomputable section
namespace Nagata.W08
open Nagata.W21
def tPS {τ a : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) :
    aS τ 1 (-a) :=
  sOF hτ0 (fun z ↦ tP τ (z / a))
    (fun z hz ↦ by
      have hd := tPdA hτ (div_ne_zero hz ha)
      have hc : DifferentiableAt ℂ (fun z : ℂ ↦ z / a) z := by
        simp only [div_eq_mul_inv]
        exact differentiableAt_id.mul_const _
      exact hd.comp z hc)
    (fun z hz ↦ by
      simpa only [zpow_neg_one] using tPsa hτ hτ0 ha hz)
@[simp] theorem tPSa {τ a z : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hz : z ≠ 0) :
    (tPS hτ hτ0 ha).val z = tP τ (z / a) := by
  change nAZ (fun w ↦ tP τ (w / a)) z = tP τ (z / a)
  exact nAZon _ hz
end Nagata.W08
end
end
section
noncomputable section
namespace Nagata.W08
theorem oas {τ x y : ℂ} (hτ : τ ≠ 0)
    (h : ∀ k : ℤ, x ≠ y * τ ^ k) : ∀ k : ℤ, y ≠ x * τ ^ k := by
  intro k he
  apply h (-k)
  rw [he, mul_assoc, ← zpow_add₀ hτ]
  simp
theorem etdom {τ a γ : ℂ}
    (hτ : τ ≠ 0) (ha : a ≠ 0) (hγ : γ ≠ 0) :
    ∃ m : Fin 3 → ℂ, m 0 = a ∧ (∀ i, m i ≠ 0) ∧
      Pairwise (fun i j => ∀ k : ℤ, m i ≠ m j * τ ^ k) ∧
      (∏ i, -m i) = γ := by
  obtain ⟨b, hb, hba, hlinear, hquadratic⟩ := ecsm (γ := γ) hτ ha
  let c : ℂ := -γ / (a * b)
  have hc : c ≠ 0 := div_ne_zero (neg_ne_zero.mpr hγ) (mul_ne_zero ha hb)
  have hca : ∀ k : ℤ, c ≠ a * τ ^ k := by
    intro k he
    have heq : -γ = (a * τ ^ k) * (a * b) :=
      (div_eq_iff (mul_ne_zero ha hb)).mp he
    apply hlinear k
    calc a ^ 2 * b * τ ^ k + γ = (a * τ ^ k) * (a * b) + γ := by ring
      _ = 0 := by rw [← heq]; ring
  have hcb : ∀ k : ℤ, c ≠ b * τ ^ k := by
    intro k he
    have heq : -γ = (b * τ ^ k) * (a * b) :=
      (div_eq_iff (mul_ne_zero ha hb)).mp he
    apply hquadratic k
    calc a * b ^ 2 * τ ^ k + γ = (b * τ ^ k) * (a * b) + γ := by ring
      _ = 0 := by rw [← heq]; ring
  have hab := oas hτ hba
  have hac := oas hτ hca
  have hbc := oas hτ hcb
  refine ⟨![a, b, c], rfl, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact ha
    · exact hb
    · exact hc
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · simp only [Fin.prod_univ_succ, Fin.prod_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ, mul_one]
    dsimp [c]
    field_simp [ha, hb]
end Nagata.W08
end
end
section
noncomputable section
namespace Nagata.W08
open Nagata.W21
open scoped BigOperators
theorem mTPa {ι : Type*} [Fintype ι]
    {τ : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    {z : ℂ} (hz : z ≠ 0) :
    mTP τ a (τ * z) =
      (∏ i, -a i) * z ^ (-(Fintype.card ι : ℤ)) * mTP τ a z := by
  classical
  unfold mTP
  simp_rw [tPsa hτ hτ0 (ha _) hz]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, zpow_neg, zpow_natCast, inv_pow]
def mTS {ι : Type*} [Fintype ι]
    {τ : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (a : ι → ℂ) (ha : ∀ i, a i ≠ 0) :
    aS τ (Fintype.card ι : ℤ) (∏ i, -a i) :=
  sOF hτ0 (mTP τ a)
    (fun _ hz ↦ mTPdA hτ ha hz)
    (fun _ hz ↦ mTPa hτ hτ0 a ha hz)
@[simp] theorem mTSa {ι : Type*} [Fintype ι]
    {τ : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    {z : ℂ} (hz : z ≠ 0) :
    (mTS hτ hτ0 a ha).val z = mTP τ a z := by
  change nAZ (mTP τ a) z = mTP τ a z
  exact nAZon _ hz
end Nagata.W08
end
end
section
noncomputable section
namespace Nagata.W08
open Nagata.W07
theorem nTSd {n τ : ℝ} (hn : 0 < n)
    (hτ : 0 < τ) (hτone : τ < 1) (a K : ℝ) {ε : ℂ} (hε : ε ≠ 0) :
    Differentiable ℂ (fun x : ℂ ↦ ∑' p : ℤ, nTT n a K ε τ p x) :=
  Nagata.W02.dnTSa hn hτ hτone hε
end Nagata.W08
end
end
section
namespace Nagata.W08
open Nagata.W21 Filter Topology
theorem tPSzi {τ a z : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hz : z ≠ 0) :
    (tPS hτ hτ0 ha).val z = 0 ↔ ∃ k : ℤ, z = a * τ ^ k := by
  rw [tPSa hτ hτ0 ha hz]
  exact tPsez hτ hτ0 ha hz
@[simp] theorem tPSam {τ a : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) :
    (tPS hτ hτ0 ha).val a = 0 := by
  rw [tPSa hτ hτ0 ha ha, div_self ha]
  exact tPo hτ
theorem tPSd {τ a z : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hz : z ≠ 0) :
    deriv (tPS hτ hτ0 ha).val z =
      deriv (fun w ↦ tP τ (w / a)) z := by
  apply Filter.EventuallyEq.deriv_eq
  exact nAZeE (fun w ↦ tP τ (w / a)) hz
theorem tPSzh {τ a z : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hz : z ≠ 0)
    (hf : (tPS hτ hτ0 ha).val z = 0) :
    deriv (tPS hτ hτ0 ha).val z ≠ 0 := by
  rw [tPSd hτ hτ0 ha hz]
  apply tPszh hτ hτ0 ha hz
  simpa only [tPSa hτ hτ0 ha hz] using hf
end Nagata.W08
end
section
namespace Nagata.W08
open Nagata.W21 Filter Topology
theorem mTSzi {ι : Type*} [Fintype ι]
    {τ : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    {z : ℂ} (hz : z ≠ 0) :
    (mTS hτ hτ0 a ha).val z = 0 ↔ ∃ i, ∃ k : ℤ, z = a i * τ ^ k := by
  rw [mTSa hτ hτ0 a ha hz]
  exact mTPez hτ hτ0 ha hz
@[simp] theorem mTSam {ι : Type*} [Fintype ι]
    {τ : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    (i : ι) : (mTS hτ hτ0 a ha).val (a i) = 0 :=
  (mTSzi hτ hτ0 a ha (ha i)).mpr ⟨i, 0, by simp⟩
theorem mTSd {ι : Type*} [Fintype ι]
    {τ : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    {z : ℂ} (hz : z ≠ 0) :
    deriv (mTS hτ hτ0 a ha).val z = deriv (mTP τ a) z := by
  apply Filter.EventuallyEq.deriv_eq
  exact nAZeE (mTP τ a) hz
theorem mTSzh {ι : Type*} [Fintype ι]
    {τ : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    (hdisjoint : Pairwise (fun i j ↦ ∀ k : ℤ, a i ≠ a j * τ ^ k))
    {z : ℂ} (hz : z ≠ 0) (hzero : (mTS hτ hτ0 a ha).val z = 0) :
    deriv (mTS hτ hτ0 a ha).val z ≠ 0 := by
  rw [mTSd hτ hτ0 a ha hz]
  apply mTPzh hτ hτ0 ha hdisjoint hz
  simpa only [mTSa hτ hτ0 a ha hz] using hzero
theorem mTSnz {ι : Type*} [Fintype ι] [Nonempty ι]
    {τ : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    (hdisjoint : Pairwise (fun i j ↦ ∀ k : ℤ, a i ≠ a j * τ ^ k)) :
    mTS hτ hτ0 a ha ≠ 0 := by
  classical
  intro hzero
  let i : ι := Classical.arbitrary ι
  have hd := mTSzh hτ hτ0 a ha hdisjoint (ha i)
    (mTSam hτ hτ0 a ha i)
  have hfun : (mTS hτ hτ0 a ha).val = (fun _ : ℂ ↦ 0) :=
    congrArg Subtype.val hzero
  apply hd
  rw [hfun, deriv_const]
end Nagata.W08
end
section
noncomputable section
namespace Nagata.W08
open Nagata.W07
def nTS2 (n K : ℤ) (hn : 0 < n) (a : ℝ)
    {ε : ℂ} (hε : ε ≠ 0) {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) :
    aS (τ : ℂ) n (ε * ((τ ^ ((K : ℝ) - a) : ℝ) : ℂ)) :=
  aSOPF
    (fun x ↦ ∑' p : ℤ, nTT (n : ℝ) a (K : ℝ) ε τ p x)
    (nTSd (by exact_mod_cast hn) hτ hτone a (K : ℝ) hε)
    (fun x k ↦ nTSiP n K k a ε τ x)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt hτ))
    (fun x ↦ by
      rw [← Complex.ofReal_log hτ.le]
      simpa using nTSrS (n : ℝ) a (K : ℝ) hε hτ x)
theorem nTSe (n K : ℤ) (hn : 0 < n) (a : ℝ)
    {ε : ℂ} (hε : ε ≠ 0) {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (x : ℂ) :
    (nTS2 n K hn a hε hτ hτone).val (Complex.exp x) =
      ∑' p : ℤ, nTT (n : ℝ) a (K : ℝ) ε τ p x := by
  apply aSOPF1
end Nagata.W08
end
end
section
noncomputable section
namespace Nagata.W08
open Nagata.W07
theorem nTSc (n K : ℤ) (hn : 0 < n) (a x₀ : ℝ)
    {ε : ℂ} (hε : ε ≠ 0) {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (x : ℂ) :
    ((τ ^ (-x₀ * (K : ℝ)) : ℝ) : ℂ) *
      (nTS2 n K hn a hε hτ hτone).val
        (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) =
      ∑' p : ℤ, nTT (n : ℝ) (a + x₀ * (n : ℝ)) (K : ℝ) ε τ p x := by
  have he : Complex.exp (((x₀ * Real.log τ : ℝ) : ℂ)) = ((τ ^ x₀ : ℝ) : ℂ) := by
    rw [Real.rpow_def_of_pos hτ, Complex.ofReal_exp]
    congr 1
    rw [mul_comm x₀ (Real.log τ)]
  have hcenter : Complex.exp (((x₀ * Real.log τ : ℝ) : ℂ) + x) =
      ((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x := by
    rw [Complex.exp_add, he]
  rw [← hcenter, nTSe, ← tsum_mul_left]
  exact tsum_congr fun p ↦ nTTs hτ (n : ℝ) a (K : ℝ) x₀ ε x p
end Nagata.W08
end
end
section
noncomputable section
namespace Nagata.W08
theorem ectsz {τ γ a : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (hγ : γ ≠ 0) (ha : a ≠ 0) :
    ∃ (m : Fin 3 → ℂ) (s : aS τ 3 γ),
      m 0 = a ∧ (∀ i, m i ≠ 0) ∧
      Pairwise (fun i j => ∀ k : ℤ, m i ≠ m j * τ ^ k) ∧
      (∏ i, -m i) = γ ∧ s ≠ 0 ∧ s.val a = 0 ∧
      (∀ z : ℂ, z ≠ 0 → (s.val z = 0 ↔ ∃ i, ∃ k : ℤ, z = m i * τ ^ k)) ∧
      (∀ z : ℂ, z ≠ 0 → s.val z = 0 → deriv s.val z ≠ 0) := by
  obtain ⟨m, hm0, hm, hdisjoint, hprod⟩ := etdom hτ0 ha hγ
  let f := mTS hτ hτ0 m hm
  have hf : f.val ∈ aS τ 3 γ := by
    simpa only [Fintype.card_fin, Nat.cast_ofNat, hprod] using f.property
  let s : aS τ 3 γ := ⟨f.val, hf⟩
  have hs : s ≠ 0 := by
    intro he
    apply mTSnz hτ hτ0 m hm hdisjoint
    apply Subtype.ext
    exact congrArg (fun v : aS τ 3 γ => v.val) he
  refine ⟨m, s, hm0, hm, hdisjoint, hprod, hs, ?_, ?_, ?_⟩
  · rw [← hm0]
    exact mTSam hτ hτ0 m hm 0
  · intro z hz
    exact mTSzi hτ hτ0 m hm hz
  · intro z hz hzero
    exact mTSzh hτ hτ0 m hm hdisjoint hz hzero
theorem ectsz1 {τ : ℝ} {γ a : ℂ}
    (hτ : 0 < τ) (hτone : τ < 1) (hγ : γ ≠ 0) (ha : a ≠ 0) :
    ∃ (m : Fin 3 → ℂ) (s : aS (τ : ℂ) 3 γ),
      m 0 = a ∧ (∀ i, m i ≠ 0) ∧
      Pairwise (fun i j => ∀ k : ℤ, m i ≠ m j * (τ : ℂ) ^ k) ∧
      (∏ i, -m i) = γ ∧ s ≠ 0 ∧ s.val a = 0 ∧
      (∀ z : ℂ, z ≠ 0 → (s.val z = 0 ↔ ∃ i, ∃ k : ℤ, z = m i * (τ : ℂ) ^ k)) ∧
      (∀ z : ℂ, z ≠ 0 → s.val z = 0 → deriv s.val z ≠ 0) :=
  ectsz (pPnlo hτ hτone)
    (Complex.ofReal_ne_zero.mpr hτ.ne') hγ ha
end Nagata.W08
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W09
open Nagata.W07 Complex Metric
theorem nnTTi {n a K τ : ℝ} {ε : ℂ}
    (hτ : 0 < τ) (hε : ‖ε‖ = 1) (p : ℤ) (θ : ℝ) :
    ‖nTT n a K ε τ p ((θ : ℂ) * Complex.I)‖ =
      τ ^ tE n a (p : ℝ) := by
  simp [nTT, hε, Complex.norm_exp,
    Complex.mul_re, Complex.mul_im, abs_of_nonneg (Real.rpow_nonneg hτ.le _)]
theorem sgnA {q : ℝ} (hq : 0 ≤ q) (hqone : q < 1) :
    Summable (fun p : ℤ => q ^ p.natAbs) := by
  have hs := summable_geometric_of_lt_one hq hqone
  have hp : Summable (fun t : ℕ => q ^ (t : ℤ).natAbs) := by simpa using hs
  have hnat (t : ℕ) : ((t : ℤ) + 1).natAbs = t + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Int.natAbs_natCast (t + 1)
  have hm : Summable (fun t : ℕ => q ^ (-(t + 1 : ℤ)).natAbs) := by
    simpa only [Int.natAbs_neg, hnat] using
      (summable_nat_add_iff (f := fun t : ℕ => q ^ t) 1).2 hs
  exact hp.of_nat_of_neg_add_one hm
noncomputable def tIM (τ n a : ℝ) (p : ℤ) : ℝ :=
  (τ ^ tM n a) ^ p.natAbs
theorem tIMs {τ n a : ℝ}
    (hτ : 0 < τ) (hτone : τ < 1) (ha : 0 < a) (han : a < n) :
    Summable (tIM τ n a) :=
  sgnA (Real.rpow_nonneg hτ.le _)
    (Real.rpow_lt_one hτ.le hτone (tMp ha han))
theorem nLMcs {τ : ℝ}
    (hτ : 0 < τ) (hτone : τ ≤ 1) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ‖ε‖ = 1) {n : ℤ} (hn : 0 ≤ n)
    (K p : ℤ) {z : ℂ} (hz : z ∈ sphere 0 (τ ^ x₀)) :
    ‖nLC τ σ x₀ ε n K p * z ^ (K + n * p)‖ ≤
      tIM τ (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ)) p := by
  obtain ⟨θ, _, rfl⟩ := ecaom (Real.rpow_pos_of_pos hτ _) hz
  have heval : circleMap 0 (τ ^ x₀) θ = ((τ ^ x₀ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    simp only [circleMap, zero_add]
  rw [heval, nLCe hτ,
    nnTTi hτ hε]
  exact tplg (by exact_mod_cast hn) hτ hτone p
theorem nTThS {τ n a K : ℝ}
    (hτ : 0 < τ) (hτone : τ < 1) (hn : 0 ≤ n) (ha : 0 < a) (han : a < n)
    {ε : ℂ} (hε : ‖ε‖ = 1) (θ : ℝ) :
    HasSum (fun p : ℤ => nTT n a K ε τ p ((θ : ℂ) * Complex.I))
      (∑' p : ℤ, nTT n a K ε τ p ((θ : ℂ) * Complex.I)) := by
  apply Summable.hasSum
  apply Summable.of_norm
  apply (tIMs hτ hτone ha han).of_nonneg_of_le
  · intro p; exact norm_nonneg _
  · intro p
    rw [nnTTi hτ hε]
    exact tplg hn hτ hτone.le p
end Nagata.W09
end
end
section
noncomputable section
namespace Nagata.W09
open Nagata.W07
def nSTS (n K : ℤ) (hn : 0 < n) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ε ≠ 0) {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) :
    Nagata.W08.aS (τ : ℂ) n (ε * ((τ ^ σ : ℝ) : ℂ)) := by
  let g := Nagata.W08.nTS2 n K hn ((K : ℝ) - σ) hε hτ hτone
  let c : ℂ := ((τ ^ (-x₀ * (K : ℝ)) : ℝ) : ℂ)
  refine ⟨fun z => c * g.val z, ?_, ?_, ?_⟩
  · change c * g.val 0 = 0
    rw [g.property.1, mul_zero]
  · intro z hz
    exact (differentiableAt_const c).mul (g.property.2.1 z hz)
  · intro z hz
    change c * g.val ((τ : ℂ) * z) = _
    rw [g.property.2.2 z hz]
    have hσ : (K : ℝ) - ((K : ℝ) - σ) = σ := by ring
    calc
      _ = (ε * ((τ ^ ((K : ℝ) - ((K : ℝ) - σ)) : ℝ) : ℂ)) *
          z ^ (-n) * (c * g.val z) := by ring
      _ = _ := congrArg (fun t : ℝ => (ε * (t : ℂ)) * z ^ (-n) * (c * g.val z))
        (congrArg (fun t : ℝ => τ ^ t) hσ)
theorem nSTSc
    (n K : ℤ) (hn : 0 < n) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ε ≠ 0) {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (x : ℂ) :
    (nSTS n K hn σ x₀ hε hτ hτone).val
      (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) =
      ∑' p : ℤ, nTT (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ))
        (K : ℝ) ε τ p x :=
  Nagata.W08.nTSc n K hn ((K : ℝ) - σ) x₀ hε hτ hτone x
end Nagata.W09
end
end
section
namespace Nagata.W09
open Complex Metric Nagata.W07
theorem nLMhS
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ‖ε‖ = 1) {n : ℤ} (hn : 0 ≤ n) (K : ℤ)
    (ha : 0 < (K : ℝ) - σ + x₀ * (n : ℝ))
    (han : (K : ℝ) - σ + x₀ * (n : ℝ) < (n : ℝ))
    (f : ℂ → ℂ)
    (hlocal : ∀ x : ℂ, f (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) =
      ∑' p : ℤ, nTT (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ))
        (K : ℝ) ε τ p x)
    {z : ℂ} (hz : z ∈ sphere 0 (τ ^ x₀)) :
    HasSum (fun p : ℤ => nLC τ σ x₀ ε n K p * z ^ (K + n * p)) (f z) := by
  obtain ⟨θ, hθ, rfl⟩ := ecaom (Real.rpow_pos_of_pos hτ _) hz
  have heval : circleMap 0 (τ ^ x₀) θ = ((τ ^ x₀ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    simp only [circleMap, zero_add]
  rw [heval, hlocal]
  simpa only [nLCe hτ] using
    nTThS hτ hτone (by exact_mod_cast hn) ha han hε θ
theorem aLCol
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ‖ε‖ = 1) {n : ℤ} (hn : 0 < n) (K : ℤ)
    (ha : 0 < (K : ℝ) - σ + x₀ * (n : ℝ))
    (han : (K : ℝ) - σ + x₀ * (n : ℝ) < (n : ℝ))
    (f : ℂ → ℂ)
    (hlocal : ∀ x : ℂ, f (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) =
      ∑' p : ℤ, nTT (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ))
        (K : ℝ) ε τ p x) (p : ℤ) :
    aLC (τ ^ x₀) f (K + n * p) = nLC τ σ x₀ ε n K p := by
  refine aLCms (Real.rpow_pos_of_pos hτ _)
    (nLC τ σ x₀ ε n K) (fun p : ℤ => K + n * p)
    ?_ f (tIM τ (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ)))
    (tIMs hτ hτone ha han) ?_ ?_ p
  · intro a b hab
    exact mul_left_cancel₀ hn.ne' (add_left_cancel hab)
  · intro i z hz
    exact nLMcs hτ hτone.le σ x₀ hε hn.le K i hz
  · intro z hz
    exact nLMhS hτ hτone σ x₀ hε hn.le K ha han f hlocal hz
theorem aLClt1
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ‖ε‖ = 1) {n : ℤ} (hn : 0 ≤ n) (K : ℤ)
    (ha : 0 < (K : ℝ) - σ + x₀ * (n : ℝ))
    (han : (K : ℝ) - σ + x₀ * (n : ℝ) < (n : ℝ))
    (f : ℂ → ℂ)
    (hlocal : ∀ x : ℂ, f (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) =
      ∑' p : ℤ, nTT (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ))
        (K : ℝ) ε τ p x) (k : ℤ) (hk : k % n ≠ K % n) :
    aLC (τ ^ x₀) f k = 0 := by
  refine aLCms1 (Real.rpow_pos_of_pos hτ _)
    (nLC τ σ x₀ ε n K) (fun p : ℤ => K + n * p)
    f (tIM τ (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ)))
    (tIMs hτ hτone ha han) ?_ ?_ k ?_
  · intro i z hz
    exact nLMcs hτ hτone.le σ x₀ hε hn K i hz
  · intro z hz
    exact nLMhS hτ hτone σ x₀ hε hn K ha han f hlocal hz
  · rintro ⟨p, hp⟩
    apply hk
    rw [← hp]
    simp
theorem aLClt
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ‖ε‖ = 1) {n : ℤ} (hn : 0 < n) (K : ℤ)
    (ha : 0 < (K : ℝ) - σ + x₀ * (n : ℝ))
    (han : (K : ℝ) - σ + x₀ * (n : ℝ) < (n : ℝ))
    (f : ℂ → ℂ)
    (hlocal : ∀ x : ℂ, f (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) =
      ∑' p : ℤ, nTT (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ))
        (K : ℝ) ε τ p x) (k : ℤ) :
    aLC (τ ^ x₀) f k =
      sOC (τ : ℂ) (ε * ((τ ^ σ : ℝ) : ℂ)) n K
        ((τ ^ (-x₀ * (K : ℝ)) : ℝ) : ℂ) k := by
  by_cases hdiv : n ∣ k - K
  · let p := (k - K) / n
    have hp : n * p = k - K := Int.mul_ediv_cancel_of_dvd hdiv
    have hk : k = K + n * p := by omega
    rw [hk, aLCol hτ hτone σ x₀ hε hn K ha han f hlocal,
      sOCoo _ _ hn.ne', nLCeo hτ]
  · have hres : k % n ≠ K % n := by
      intro heq
      exact hdiv (Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp heq))
    rw [aLClt1 hτ hτone σ x₀ hε hn.le K ha han f hlocal k hres]
    simp only [sOC, if_neg hdiv]
end Nagata.W09
end
section
noncomputable section
namespace Nagata.W09
open Nagata.W07
theorem lCMnS
    (n K : ℤ) (hn : 0 < n) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ε ≠ 0) (hunit : ‖ε‖ = 1)
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (ha : 0 < (K : ℝ) - σ + x₀ * (n : ℝ))
    (han : (K : ℝ) - σ + x₀ * (n : ℝ) < (n : ℝ)) (k : ℤ) :
    lCM (τ : ℂ) n (ε * ((τ ^ σ : ℝ) : ℂ))
      (nSTS n K hn σ x₀ hε hτ hτone) k =
      sOC (τ : ℂ) (ε * ((τ ^ σ : ℝ) : ℂ)) n K
        ((τ ^ (-x₀ * (K : ℝ)) : ℝ) : ℂ) k := by
  let f := nSTS n K hn σ x₀ hε hτ hτone
  change aLC 1 f.val k = _
  rw [← aLCri (Real.rpow_pos_of_pos hτ x₀)
    zero_lt_one f.property.2.1 k]
  exact aLClt hτ hτone σ x₀ hunit hn K ha han
    f.val (nSTSc n K hn σ x₀ hε hτ hτone) k
end Nagata.W09
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.CS
def pSC (τ γL γP : ℂ) (d m : ℤ) (P : ℂ → ℂ) :
    pS τ γL γP d m P ≃ₗ[ℂ]
      ((j : Fin ((d / 3).toNat + 1)) → cS τ γL γP d m (j.val : ℤ) P) :=
  bPE (d / 3).toNat
    (fun j => cS τ γL γP d m (j : ℤ) P)
end Nagata.Workers.W10
end
end
section
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.W07 Nagata.W08 Nagata.W09
variable (n : ℤ) (hn : 0 < n) (σ x₀ : ℝ)
  {ε : ℂ} (hε : ε ≠ 0) (hunit : ‖ε‖ = 1)
  {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
  (hC : Function.Injective (lCM (τ : ℂ) n (ε * ((τ ^ σ : ℝ) : ℂ))))
  (hU : σ - x₀ * (n : ℝ) ∉ Set.range (Int.cast : ℤ → ℝ))
def cTSB :
    Basis (tI (σ - x₀ * (n : ℝ)) n) ℂ
      (aS (τ : ℂ) n (ε * ((τ ^ σ : ℝ) : ℂ))) := by
  have hγ : ε * ((τ ^ σ : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero hε (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos hτ σ)))
  apply bFSO (lCM (τ : ℂ) n (ε * ((τ ^ σ : ℝ) : ℂ)))
    (τ : ℂ) (ε * ((τ ^ σ : ℝ) : ℂ)) (σ - x₀ * (n : ℝ)) n
    (fun K => ((τ ^ (-x₀ * (K.val : ℝ)) : ℝ) : ℂ))
    (fun K => nsnz hτ x₀ K.val)
    (rCMi _ hC (τ : ℂ) (ε * ((τ ^ σ : ℝ) : ℂ))
      (Complex.ofReal_ne_zero.mpr (ne_of_gt hτ)) hγ _ hn
      (lCMrp hτ n _ hγ))
    (fun K => nSTS n K.val hn σ x₀ hε hτ hτone)
  intro K k
  have hmem := (mtIi hU).mp K.property
  exact lCMnS n K.val hn σ x₀ hε hunit
    hτ hτone (by linarith [hmem.1]) (by linarith [hmem.2]) k
end Nagata.Workers.W10
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.CS Nagata.FE Nagata.W08
def sB (τ γL γP : ℂ) (d m j : ℤ) : Submodule ℂ (ℂ → ℂ) :=
  if j ≤ m then
    aS τ (3 * (d - 3 * m))
      (γL ^ (d - 3 * m) * nMMM γL γP ^ (m - j))
  else aS τ (3 * (d - 3 * j)) (γL ^ (d - 3 * j))
end Nagata.Workers.W10
end
end
section
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.CS Nagata.FE
variable (τ γL γP : ℂ) (d : ℤ) (m : ℕ) (a Δ : ℝ) (P : ℂ → ℂ)
  (hd : 3 * (m : ℤ) < d)
  (hP : AnalyticOnNhd ℂ P {z | z ≠ 0})
  (hPfin : ∀ z ≠ 0, analyticOrderAt P z ≠ ⊤)
  (c : ∀ j : Fin ((d / 3).toNat + 1), sB τ γL γP d (m : ℤ) (j.val : ℤ) →ₗ[ℂ]
    (CF d (m : ℤ) a Δ (j.val : ℤ) → ℂ))
  (hc : ∀ j, Function.Injective (c j))
  (theta : ∀ j : Fin ((d / 3).toNat + 1), CF d (m : ℤ) a Δ (j.val : ℤ) →
    sB τ γL γP d (m : ℤ) (j.val : ℤ))
  (htheta : ∀ j K, c j (theta j K) = Pi.single K 1)
end Nagata.Workers.W10
end
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Nagata.W01
section
abbrev AC := AddCircle (2 * Real.pi)
def cP3 (r : ℝ) (t : AC) : ℂ :=
  (r : ℂ) * (AddCircle.toCircle t : ℂ)
theorem cPnz {r : ℝ} (hr : 0 < r) (t : AC) :
    cP3 r t ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') (AddCircle.toCircle t).coe_ne_zero
theorem ccP (r : ℝ) : Continuous (cP3 r) :=
  continuous_const.mul (continuous_subtype_val.comp AddCircle.continuous_toCircle)
theorem cPc (r θ : ℝ) :
    cP3 r (θ : AC) = circleMap 0 r θ := by
  simp [cP3, AddCircle.toCircle_apply_mk, Real.two_pi_pos.ne', Circle.coe_exp, circleMap]
theorem cPa (z : ℂ) :
    cP3 ‖z‖ (Complex.arg z : AC) = z := by
  rw [cPc]
  simp [circleMap]
def cT1 (r : ℝ) (f : ℂ → ℂ) : AC → ℂ :=
  fun t => f (cP3 r t)
@[simp] theorem cTc (r : ℝ) (f : ℂ → ℂ) (θ : ℝ) :
    cT1 r f (θ : AC) = f (circleMap 0 r θ) := by
  rw [cT1, cPc]
theorem ccT {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : ∀ z, z ≠ 0 → ContinuousAt f z) : Continuous (cT1 r f) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (hf _ (cPnz hr t)).comp (ccP r).continuousAt
def cTM1 (r : ℝ) (hr : 0 < r) (f : ℂ → ℂ)
    (hf : ∀ z, z ≠ 0 → ContinuousAt f z) : C(AC, ℂ) :=
  ⟨cT1 r f, ccT hr hf⟩
theorem pezoc {f : ℂ → ℂ}
    (h : ∀ r : ℝ, 0 < r → ∀ t : AC, cT1 r f t = 0) :
    ∀ z : ℂ, z ≠ 0 → f z = 0 := by
  intro z hz
  have hh := h ‖z‖ (norm_pos_iff.mpr hz) (Complex.arg z : AC)
  simpa [cT1, cPa] using hh
variable {T : ℝ} [Fact (0 < T)]
theorem cczof (f : C(AddCircle T, ℂ))
    (h : ∀ k : ℤ, fourierCoeff f k = 0) : f = 0 := by
  have hs : Summable (fourierCoeff f) := by
    simpa only [show fourierCoeff f = (fun _ : ℤ => (0 : ℂ)) from funext h]
      using (summable_zero : Summable (fun _ : ℤ => (0 : ℂ)))
  ext x
  have hsum := has_pointwise_sum_fourier_series_of_summable hs x
  simp only [h, zero_smul] at hsum
  exact hsum.unique hasSum_zero
end
open Complex
theorem lti (z w : ℂ) (hz : z ≠ 0) (k : ℤ) :
    (z * I) * (z ^ (-k - 1) * w) = I * z ^ (-k) * w := by
  have hpow : z * z ^ (-k - 1) = z ^ (-k) := by
    conv_lhs => lhs; rw [← zpow_one z]
    rw [← zpow_add₀ hz]
    congr 1
    omega
  calc
    _ = I * (z * z ^ (-k - 1)) * w := by ring
    _ = _ := by rw [hpow]
theorem lrfnz {r : ℝ} (hr : 0 < r) (k : ℤ) :
    (r : ℂ) ^ (-k) ≠ 0 :=
  zpow_ne_zero _ (Complex.ofReal_ne_zero.mpr hr.ne')
end Nagata.W01
section
open Complex Real
namespace Nagata.W01
local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
theorem fecz (k : ℤ) (t : AC) :
    fourier k t = (AddCircle.toCircle t : ℂ) ^ k := by
  rw [fourier_apply, AddCircle.toCircle_zsmul, Circle.coe_zpow]
theorem cMzf (r θ : ℝ) (k : ℤ) :
    circleMap 0 r θ ^ k = (r : ℂ) ^ k * fourier k (θ : AC) := by
  rw [← cPc, cP3, mul_zpow, fecz]
theorem lip {r : ℝ} (hr : 0 < r)
    (f : ℂ → ℂ) (k : ℤ) (θ : ℝ) :
    (circleMap 0 r θ * I) * ((circleMap 0 r θ) ^ (-k - 1) * f (circleMap 0 r θ)) =
      (I * (r : ℂ) ^ (-k)) * (fourier (-k) (θ : AC) * f (circleMap 0 r θ)) := by
  have hz : circleMap 0 r θ ≠ 0 := by
    simpa [cPc] using cPnz hr (θ : AC)
  rw [lti _ _ hz, cMzf]
  ring
theorem aLCef {r : ℝ} (hr : 0 < r)
    (f : ℂ → ℂ) (k : ℤ) :
    Nagata.W09.aLC r f k =
      (r : ℂ) ^ (-k) * fourierCoeff (cT1 r f) k := by
  unfold Nagata.W09.aLC circleIntegral
  simp only [deriv_circleMap, smul_eq_mul]
  have hi : (fun θ : ℝ => (circleMap 0 r θ * I) *
      ((circleMap 0 r θ) ^ (-k - 1) * f (circleMap 0 r θ))) =
      (fun θ : ℝ => (I * (r : ℂ) ^ (-k)) *
        (fourier (-k) (θ : AC) * f (circleMap 0 r θ))) :=
    funext (lip hr f k)
  rw [hi, intervalIntegral.integral_const_mul (a := 0) (b := 2 * Real.pi)
    (μ := MeasureTheory.volume) (I * (r : ℂ) ^ (-k))
    (fun θ : ℝ => fourier (-k) (θ : AC) * f (circleMap 0 r θ))]
  rw [fourierCoeff_eq_intervalIntegral _ _ 0]
  simp only [zero_add, smul_eq_mul, cTc, Complex.real_smul,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hπ, Complex.I_ne_zero]
theorem cTzol {r : ℝ} (hr : 0 < r) (f : ℂ → ℂ)
    (hf : ∀ z, z ≠ 0 → ContinuousAt f z)
    (hc : ∀ k : ℤ, Nagata.W09.aLC r f k = 0) :
    ∀ t : AC, cT1 r f t = 0 := by
  have hz : cTM1 r hr f hf = 0 := by
    apply cczof
    intro k
    have h := hc k
    rw [aLCef hr] at h
    exact (mul_eq_zero.mp h).resolve_left (lrfnz hr k)
  intro t
  exact congrArg (fun g : C(AC, ℂ) => g t) hz
theorem pzoal (f : ℂ → ℂ)
    (hf : ∀ z, z ≠ 0 → ContinuousAt f z)
    (hc : ∀ r : ℝ, 0 < r → ∀ k : ℤ, Nagata.W09.aLC r f k = 0) :
    ∀ z : ℂ, z ≠ 0 → f z = 0 := by
  apply pezoc
  intro r hr
  exact cTzol hr f hf (hc r hr)
end Nagata.W01
end
namespace Nagata.W01
theorem pzoro (f : ℂ → ℂ)
    (hf : ∀ z, z ≠ 0 → DifferentiableAt ℂ f z)
    (hc : ∀ k : ℤ, Nagata.W09.aLC 1 f k = 0) :
    ∀ z : ℂ, z ≠ 0 → f z = 0 := by
  apply pzoal f (fun z hz => (hf z hz).continuousAt)
  intro r hr k
  rw [Nagata.W09.aLCri hr zero_lt_one hf k]
  exact hc k
theorem lCMi (τ : ℂ) (n : ℤ) (γ : ℂ) :
    Function.Injective (Nagata.W09.lCM τ n γ) := by
  intro f g hfg
  have hzero : Nagata.W09.lCM τ n γ (f - g) = 0 := by
    rw [map_sub, hfg, sub_self]
  have hz := pzoro (f - g).val
    (f - g).property.2.1 (fun k => congrFun hzero k)
  apply Nagata.W08.aSe
  intro z hzne
  have h := hz z hzne
  change f.val z - g.val z = 0 at h
  exact sub_eq_zero.mp h
end Nagata.W01
end
end OAI
end
section
namespace OAI
section
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.W08 Nagata.W09
theorem pSBe {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (hC : ∀ (n : ℤ) (γ : ℂ), Function.Injective (lCM (τ : ℂ) n γ))
    {n : ℤ} (hn : 0 < n) {γ : ℂ} (hγ : γ ≠ 0) :
    Nonempty (Basis (Fin n.toNat) ℂ (aS (τ : ℂ) n γ)) := by
  obtain ⟨σ, x₀, ε, heps, hgamma, _, hU⟩ :=
    Nagata.W02.enmf (show (0 : ℝ) < (n : ℝ) by exact_mod_cast hn) hτ hτone hγ
  have heps0 : ε ≠ 0 := by intro hz; simp [hz] at heps
  let b := cTSB n hn σ x₀ heps0 heps hτ hτone (hC _ _) hU
  have hc : Fintype.card (tI (σ - x₀ * (n : ℝ)) n) = n.toNat := by
    rw [Fintype.card_coe, ctI]
  let e : tI (σ - x₀ * (n : ℝ)) n ≃ Fin n.toNat :=
    (Fintype.equivFin _).trans (finCongr hc)
  let E : aS (τ : ℂ) n (ε * ((τ ^ σ : ℝ) : ℂ)) ≃ₗ[ℂ]
      aS (τ : ℂ) n γ := LinearEquiv.ofEq _ _ (by rw [hgamma])
  exact ⟨(b.map E).reindex e⟩
def pSBF {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (hC : ∀ (n : ℤ) (γ : ℂ), Function.Injective (lCM (τ : ℂ) n γ))
    {n : ℤ} (hn : 0 < n) {γ : ℂ} (hγ : γ ≠ 0) :
    Basis (Fin n.toNat) ℂ (aS (τ : ℂ) n γ) :=
  Classical.choice (pSBe hτ hτone hC hn hγ)
theorem pSf1 {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (hC : ∀ (n : ℤ) (γ : ℂ), Function.Injective (lCM (τ : ℂ) n γ))
    {n : ℤ} (hn : 0 < n) {γ : ℂ} (hγ : γ ≠ 0) :
    Module.Finite ℂ (aS (τ : ℂ) n γ) :=
  Module.Finite.of_basis (pSBF hτ hτone hC hn hγ)
theorem pSf {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (hC : ∀ (n : ℤ) (γ : ℂ), Function.Injective (lCM (τ : ℂ) n γ))
    {n : ℤ} (hn : 0 < n) {γ : ℂ} (hγ : γ ≠ 0) :
    Module.finrank ℂ (aS (τ : ℂ) n γ) = n.toNat := by
  rw [Module.finrank_eq_card_basis (pSBF hτ hτone hC hn hγ), Fintype.card_fin]
end Nagata.Workers.W10
end
end
section
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.W08
theorem aSf {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {n : ℤ} (hn : 0 < n) {γ : ℂ} (hγ : γ ≠ 0) :
    Module.Finite ℂ (aS (τ : ℂ) n γ) :=
  pSf1 hτ hτone (Nagata.W01.lCMi (τ : ℂ)) hn hγ
theorem aSf1 {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {n : ℤ} (hn : 0 < n) {γ : ℂ} (hγ : γ ≠ 0) :
    Module.finrank ℂ (aS (τ : ℂ) n γ) = n.toNat :=
  pSf hτ hτone (Nagata.W01.lCMi (τ : ℂ)) hn hγ
end Nagata.Workers.W10
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W10
open Nagata.CS Nagata.FE
abbrev tP1 (τ s : ℝ) : ℂ := ((τ ^ s : ℝ) : ℂ)
theorem tPnz {τ : ℝ} (hτ : 0 < τ) (s : ℝ) : tP1 τ s ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos hτ s))
end Nagata.Workers.W10
end
end
section
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.CS Nagata.FE
variable (τ γL γP : ℂ) (d : ℤ) (m : ℕ) (a Δ : ℝ) (P : ℂ → ℂ)
  (hd : 3 * (m : ℤ) < d)
  (hP : AnalyticOnNhd ℂ P {z | z ≠ 0})
  (hPfin : ∀ z ≠ 0, analyticOrderAt P z ≠ ⊤)
  (b : ∀ j : Fin ((d / 3).toNat + 1),
    Basis (CF d (m : ℤ) a Δ (j.val : ℤ)) ℂ
      (sB τ γL γP d (m : ℤ) (j.val : ℤ)))
end Nagata.Workers.W10
end
end
section
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.FE Nagata.W08 Nagata.W09
variable {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
  (hC : ∀ (n : ℤ) (γ : ℂ), Function.Injective (lCM (τ : ℂ) n γ))
  (s ρ Δ x₀ : ℝ) (d m j : ℤ) (hs : s = 9 * x₀ - Δ)
end Nagata.Workers.W10
end
end
section
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.FE Nagata.W09
variable {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
  (hC : ∀ (n : ℤ) (γ : ℂ), Function.Injective (lCM (τ : ℂ) n γ))
  (s ρ Δ x₀ : ℝ) (d : ℤ) (m : ℕ) (hs : s = 9 * x₀ - Δ)
  (hd : 3 * (m : ℤ) < d)
  (hUfirst : ∀ j : ℤ, 0 ≤ j → j ≤ (m : ℤ) →
    fL d (m : ℤ) j ρ Δ ∉ Set.range (Int.cast : ℤ → ℝ))
  (hUsecond : ∀ j : ℤ, (m : ℤ) < j → j ≤ d / 3 → 0 < d - 3 * j →
    sL d j ρ Δ ∉ Set.range (Int.cast : ℤ → ℝ))
end Nagata.Workers.W10
end
end
section
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.FE
variable {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
  (s ρ Δ x₀ : ℝ) (d : ℤ) (m : ℕ) (hs : s = 9 * x₀ - Δ)
  (hd : 3 * (m : ℤ) < d)
  (hUfirst : ∀ j : ℤ, 0 ≤ j → j ≤ (m : ℤ) →
    fL d (m : ℤ) j ρ Δ ∉ Set.range (Int.cast : ℤ → ℝ))
  (hUsecond : ∀ j : ℤ, (m : ℤ) < j → j ≤ d / 3 → 0 < d - 3 * j →
    sL d j ρ Δ ∉ Set.range (Int.cast : ℤ → ℝ))
end Nagata.Workers.W10
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.Workers.W14
theorem nlFs {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (L : V →ₗ[K] K) (hL : L ≠ 0) :
    Function.Surjective L := by
  classical
  obtain ⟨v, hv⟩ : ∃ v, L v ≠ 0 := by
    by_contra hn
    apply hL
    apply LinearMap.ext
    intro v
    exact Classical.not_not.mp (fun h => hn ⟨v, h⟩)
  intro c
  refine ⟨(c / L v) • v, ?_⟩
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ c hv]
end Nagata.Workers.W14
end
section
noncomputable section
namespace Nagata.Workers.W14
theorem esoam {K ι : Type*} [Field K]
    (u v : ι → K) (hv : v ≠ 0)
    (hminor : ∀ a b, u a * v b - u b * v a = 0) :
    ∃ c : K, c • v = u := by
  classical
  obtain ⟨b, hb⟩ : ∃ b, v b ≠ 0 := by
    by_contra hnone
    apply hv
    funext b
    exact Classical.not_not.mp (fun hb => hnone ⟨b, hb⟩)
  refine ⟨u b / v b, ?_⟩
  funext a
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [div_mul_eq_mul_div]
  exact (div_eq_iff hb).2 (sub_eq_zero.mp (hminor b a))
theorem mzos {K ι : Type*} [Field K]
    (u v : ι → K) (c : K) (hc : c • v = u) (a b : ι) :
    u a * v b - u b * v a = 0 := by
  have ha : c * v a = u a := congrFun hc a
  have hb : c * v b = u b := congrFun hc b
  rw [← ha, ← hb]
  ring
end Nagata.Workers.W14
end
end
section
noncomputable section
namespace Nagata.Workers.W14
open scoped BigOperators
 theorem hoes {K : Type*} [Field K]
    (L : MvPolynomial (Fin 3) K) (hL : L.IsHomogeneous 1) :
    L = ∑ i : Fin 3, MvPolynomial.monomial (Finsupp.single i 1)
      (L.coeff (Finsupp.single i 1)) := by
  classical
  ext e
  by_cases he : e.degree = 1
  · have hr : e ∈ Set.range (fun i : Fin 3 => Finsupp.single i (1 : ℕ)) := by
      rw [Finsupp.range_single_one]
      exact he
    obtain ⟨i,rfl⟩ := hr
    rw [MvPolynomial.coeff_sum]
    simp [MvPolynomial.coeff_monomial, Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)]
  · have hcoeff : L.coeff e = 0 := by
      by_contra hc
      exact he (by simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hL hc)
    rw [hcoeff, MvPolynomial.coeff_sum]
    symm
    apply Finset.sum_eq_zero
    intro i _
    have hne : Finsupp.single i 1 ≠ e := by
      intro hi
      apply he
      rw [← hi]
      simp
    simp [MvPolynomial.coeff_monomial, hne]
 def hLM {K : Type*} [Field K] (L : MvPolynomial (Fin 3) K) :
    (Fin 3 → K) →ₗ[K] K :=
  ∑ i : Fin 3, L.coeff (Finsupp.single i 1) • LinearMap.proj i
 theorem hLMa {K : Type*} [Field K]
    (L : MvPolynomial (Fin 3) K) (hL : L.IsHomogeneous 1) (v : Fin 3 → K) :
    hLM L v = MvPolynomial.eval v L := by
  conv_rhs => rw [hoes L hL]
  simp [hLM, MvPolynomial.eval_monomial]
 theorem hLMnz (L : MvPolynomial (Fin 3) ℂ)
    (hL : L.IsHomogeneous 1) (hne : L ≠ 0) : hLM L ≠ 0 := by
  intro hz
  apply hne
  apply hL.eq_zero_of_forall_eval_eq_zero
  intro v
  rw [← hLMa L hL, hz]
  rfl
end Nagata.Workers.W14
end
end
section
noncomputable section
namespace Nagata.Workers.W14
theorem emnzo {K ι : Type*} [Field K]
    (u v : ι → K) (hu : u ≠ 0) (hv : v ≠ 0)
    (h : Projectivization.mk K u hu ≠ Projectivization.mk K v hv) :
    ∃ a b, u a * v b - u b * v a ≠ 0 := by
  classical
  by_contra hn
  have hminor : ∀ a b, u a * v b - u b * v a = 0 := by
    intro a b
    exact Classical.not_not.mp (fun hh => hn ⟨a, b, hh⟩)
  apply h
  exact (Projectivization.mk_eq_mk_iff' K u v hu hv).2
    (esoam u v hv hminor)
theorem pnomn {K ι : Type*} [Field K]
    (u v : ι → K) (hu : u ≠ 0) (hv : v ≠ 0) (a b : ι)
    (hminor : u a * v b - u b * v a ≠ 0) :
    Projectivization.mk K u hu ≠ Projectivization.mk K v hv := by
  intro heq
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' K u v hu hv).1 heq
  exact hminor (mzos u v c hc a b)
end Nagata.Workers.W14
end
end
section
noncomputable section
namespace Nagata.Workers.W14
 def cLR : MvPolynomial (Fin 3) ℂ →+* MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.eval₂Hom MvPolynomial.C ![MvPolynomial.X 0,MvPolynomial.X 1,0]
 theorem cLRe (Q : MvPolynomial (Fin 3) ℂ) (v : Fin 2 → ℂ) :
    MvPolynomial.eval v (cLR Q) =
      MvPolynomial.eval ![v 0,v 1,0] Q := by
  have h : (MvPolynomial.eval v).comp cLR =
      MvPolynomial.eval ![v 0,v 1,0] := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [cLR]
    · intro i
      fin_cases i <;> simp [cLR]
  exact RingHom.congr_fun h Q
 theorem cLRh {Q : MvPolynomial (Fin 3) ℂ} {d : ℕ}
    (hQ : Q.IsHomogeneous d) : (cLR Q).IsHomogeneous d := by
  have hcoords : ∀ i : Fin 3,
      (![MvPolynomial.X 0,MvPolynomial.X 1,0] i : MvPolynomial (Fin 2) ℂ).IsHomogeneous 1 := by
    intro i
    fin_cases i
    · exact MvPolynomial.isHomogeneous_X ℂ 0
    · exact MvPolynomial.isHomogeneous_X ℂ 1
    · exact MvPolynomial.isHomogeneous_zero (Fin 2) ℂ 1
  simpa only [cLR, MvPolynomial.coe_eval₂Hom, one_mul] using hQ.eval₂ MvPolynomial.C
    ![MvPolynomial.X 0,MvPolynomial.X 1,0]
    (fun c => MvPolynomial.isHomogeneous_C (Fin 2) c) hcoords
 def pILC : MvPolynomial (Fin 3) ℂ ≃ₐ[ℂ]
    Polynomial (MvPolynomial (Fin 2) ℂ) :=
  (MvPolynomial.renameEquiv ℂ (Equiv.swap (0 : Fin 3) 2)).trans
    (MvPolynomial.finSuccEquiv ℂ 2)
 theorem pILCX : pILC (MvPolynomial.X 2) =
    Polynomial.X := by
  simp [pILC, MvPolynomial.renameEquiv_apply,
    MvPolynomial.finSuccEquiv_apply]
 theorem pILCe (Q : MvPolynomial (Fin 3) ℂ) :
    (pILC Q).eval 0 =
      MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) (cLR Q) := by
  have h : (Polynomial.evalRingHom (0 : MvPolynomial (Fin 2) ℂ)).comp
      pILC.toRingHom =
      (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1)).toRingHom.comp cLR := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [pILC, cLR,
        MvPolynomial.renameEquiv_apply, MvPolynomial.finSuccEquiv_apply]
    · intro i
      fin_cases i <;> simp [pILC, cLR,
        MvPolynomial.renameEquiv_apply, MvPolynomial.finSuccEquiv_apply, Equiv.swap_apply_def]
      all_goals
        change Polynomial.eval 0 (Polynomial.C _) = _
        simp
  exact RingHom.congr_fun h Q
 theorem cLdor (Q : MvPolynomial (Fin 3) ℂ)
    (hQ : cLR Q = 0) : MvPolynomial.X 2 ∣ Q := by
  rw [← map_dvd_iff pILC, pILCX]
  apply Polynomial.X_dvd_iff.mpr
  rw [Polynomial.coeff_zero_eq_eval_zero,pILCe,hQ]
  simp
end Nagata.Workers.W14
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W29
open Nagata.Workers.W28
theorem aPGs (G : MvPolynomial (Fin 2) ℂ)
    (p : CP)
    (hgradient : pPE (MvPolynomial.pderiv 0 G) p ≠ 0 ∨
      pPE (MvPolynomial.pderiv 1 G) p ≠ 0) :
    Function.Surjective (pG G p) := by
  apply Nagata.Workers.W14.nlFs
    (pG G p).toLinearMap
  intro hz
  rcases hgradient with h0 | h1
  · have h := LinearMap.congr_fun hz (1, 0)
    apply h0
    simpa [pG] using h
  · have h := LinearMap.congr_fun hz (0, 1)
    apply h1
    simpa [pG] using h
end Nagata.W29
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
open Filter Topology
namespace Nagata.W03
variable {α β R : Type*} [TopologicalSpace β] [NormedCommRing R]
  {l : Filter α} {s : Set β}
end Nagata.W03
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
open Filter Topology
namespace Nagata.W22
open Nagata.W21
def sTP (a : ℝ) (τ : ℝ) (x : ℂ) : ℂ :=
  tP (τ : ℂ) (((τ ^ a : ℝ) : ℂ) * Complex.exp x)
end Nagata.W22
end
end
section
noncomputable section
open Filter Topology
namespace Nagata.W22
def mP1 (a : Fin 9 → ℝ) (τ : ℝ) (x : ℂ) : ℂ :=
  ∏ i : Fin 9, sTP (a i) τ x
end Nagata.W22
end
end
section
noncomputable section
namespace Nagata.W22
def rMS {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (ξ : Fin 9 → ℝ) :=
  Nagata.W08.mTS
    (τ := (τ : ℂ))
    (by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ] using hτone)
    (Complex.ofReal_ne_zero.mpr hτ.ne')
    (fun i => ((τ ^ ξ i : ℝ) : ℂ))
    (fun i => Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hτ (ξ i)).ne')
end Nagata.W22
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.Workers.W17
open Filter
open scoped Topology
variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜]
    [TopologicalSpace V] [T2Space V] [Zero V]
theorem cvzoe
    (f : 𝕜 → V) (x : 𝕜) (exceptional : Finset 𝕜)
    (hf : ContinuousAt f x)
    (hzero : ∀ᶠ s in 𝓝 x, s ∉ exceptional → f s = 0) : f x = 0 := by
  have he : ∀ᶠ s in 𝓝[≠] x, s ∉ exceptional :=
    exceptional.eventually_cofinite_notMem.filter_mono (nhdsNE_le_cofinite x)
  have hlocal : ∀ᶠ s in 𝓝[≠] x, s ∉ exceptional → f s = 0 :=
    hzero.filter_mono nhdsWithin_le_nhds
  have hz : f =ᶠ[𝓝[≠] x] fun _ => 0 :=
    (he.and hlocal).mono fun s hs => hs.2 hs.1
  exact tendsto_nhds_unique_of_eventuallyEq
    (hf.mono_left nhdsWithin_le_nhds) tendsto_const_nhds hz
variable {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
theorem lcmdj
    (family : 𝕜 → E → F) (center : 𝕜 → E) (x : 𝕜)
    (exceptional : Finset 𝕜) (m : Nat)
    (hcontinuous : ∀ n < m,
      ContinuousAt (fun s => iteratedFDeriv 𝕜 n (family s) (center s)) x)
    (hjets : ∀ᶠ s in 𝓝 x, s ∉ exceptional → ∀ n < m,
      iteratedFDeriv 𝕜 n (family s) (center s) = 0) :
    ∀ n < m, iteratedFDeriv 𝕜 n (family x) (center x) = 0 := by
  intro n hn
  exact cvzoe
    (fun s => iteratedFDeriv 𝕜 n (family s) (center s)) x exceptional
    (hcontinuous n hn) (hjets.mono fun s hs hE => hs hE n hn)
end Nagata.Workers.W17
end
section
noncomputable section
namespace Nagata.Workers.W17
open Nagata.Workers.W28
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
theorem pSdzo
    {f : E → F} {x : E} {p : FormalMultilinearSeries 𝕜 E F} {n : ℕ}
    (hp : HasFPowerSeriesAt f p x) (hn : iteratedFDeriv 𝕜 n f x = 0) (v : E) :
    p n (fun _ => v) = 0 := by
  obtain ⟨r, hr⟩ := hp
  have he := hr.iteratedFDeriv_eq_sum_of_completeSpace (fun _ : Fin n => v)
  have hz : n.factorial • p n (fun _ => v) = 0 := by
    simpa only [hn, zero_apply, Finset.sum_const,
      Finset.card_univ, Fintype.card_perm, Fintype.card_fin] using he.symm
  have hz' : (n.factorial : 𝕜) • p n (fun _ => v) = 0 := by
    simpa only [Nat.cast_smul_eq_nsmul] using hz
  exact (smul_eq_zero.mp hz').resolve_left (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
theorem aooiF
    {f : E → F} {x : E} (hf : AnalyticAt 𝕜 f x) (m : ℕ)
    (hz : ∀ n < m, iteratedFDeriv 𝕜 n f x = 0) :
    HAOAL (𝕜 := 𝕜) f x m := by
  obtain ⟨p, r, hp⟩ := hf
  let q : FormalMultilinearSeries 𝕜 E F := fun n => if n < m then 0 else p n
  have hnorm : ∀ n, ‖q n‖ ≤ ‖p n‖ := by
    intro n
    by_cases hn : n < m
    · simp [q, hn]
    · simp [q, hn]
  have hdiag : ∀ n v, q n (fun _ => v) = p n (fun _ => v) := by
    intro n v
    by_cases hn : n < m
    · simp [q, hn, pSdzo
        hp.hasFPowerSeriesAt (hz n hn) v]
    · simp [q, hn]
  refine ⟨q, ⟨r, ?_⟩, ?_⟩
  · refine ⟨hp.r_le.trans (FormalMultilinearSeries.radius_le_of_le hnorm), hp.r_pos, ?_⟩
    intro y hy
    simpa only [hdiag] using hp.hasSum hy
  · intro n hn
    simp [q, hn]
end Nagata.Workers.W17
end
end
section
namespace Nagata.Workers.W17
open Nagata.Workers.W28
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
theorem aocs {f : E → F} {x : E} {m : Nat}
    (hf : HAOAL (𝕜 := 𝕜) f x m) (c : 𝕜) :
    HAOAL (𝕜 := 𝕜) (c • f) x m := by
  obtain ⟨p, hp, hz⟩ := hf
  refine ⟨c • p, hp.const_smul, ?_⟩
  intro n hn
  simp [hz n hn]
theorem aocsi (f : E → F) (x : E) (m : Nat)
    (c : 𝕜) (hc : c ≠ 0) :
    HAOAL (𝕜 := 𝕜) (c • f) x m ↔
      HAOAL (𝕜 := 𝕜) f x m := by
  constructor
  · intro h
    have hi := aocs h c⁻¹
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hi
  · intro h
    exact aocs h c
theorem aocmi (f : E → 𝕜) (x : E) (m : Nat)
    (c : 𝕜) (hc : c ≠ 0) :
    HAOAL (𝕜 := 𝕜) (fun y => c * f y) x m ↔
      HAOAL (𝕜 := 𝕜) f x m :=
  aocsi f x m c hc
end Nagata.Workers.W17
end
section
namespace Nagata.Workers.W17
open scoped ContDiff
variable {𝕜 P E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup P] [NormedSpace 𝕜 P]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
theorem cDApi
    (family : P → E → F) (p : P × E)
    (hf : ContDiffAt 𝕜 ∞ (Function.uncurry family) p) (n : Nat) :
    ContDiffAt 𝕜 ∞ (fun q : P × E => iteratedFDeriv 𝕜 n (family q.1) q.2) p := by
  induction n with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def,
      LinearIsometryEquiv.coe_coe'', Function.uncurry_def] using
      hf.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 𝕜 E F).symm :
          F →L[𝕜] E [×0]→L[𝕜] F)
  | succ n ih =>
    have hprojection : ContDiffAt 𝕜 ∞
        (fun q : (P × E) × E => (q.1.1, q.2)) (p, p.2) :=
      contDiffAt_fst.fst.prodMk contDiffAt_snd
    have hjoint : ContDiffAt 𝕜 ∞
        (fun q : (P × E) × E => iteratedFDeriv 𝕜 n (family q.1.1) q.2) (p, p.2) :=
      by
        have ih' : ContDiffAt 𝕜 ∞
            (fun q : P × E => iteratedFDeriv 𝕜 n (family q.1) q.2) (p.1, p.2) := by
          simpa only [Prod.eta] using ih
        simpa only [Function.comp_def] using ih'.comp (p, p.2) hprojection
    have hd : ContDiffAt 𝕜 ∞
        (fun q : P × E => fderiv 𝕜 (iteratedFDeriv 𝕜 n (family q.1)) q.2) p :=
      hjoint.fderiv contDiffAt_snd (by simp)
    simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def] using
      (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) F).symm.contDiff.contDiffAt.comp
        p hd
theorem amdcA [CompleteSpace F]
    (family : P → E → F) (center : P → E) (s₀ : P)
    (hf : AnalyticAt 𝕜 (Function.uncurry family) (s₀, center s₀))
    (hc : ContinuousAt center s₀) (n : Nat) :
    ContinuousAt (fun s => iteratedFDeriv 𝕜 n (family s) (center s)) s₀ := by
  have hpartial : ContinuousAt
      (fun q : P × E => iteratedFDeriv 𝕜 n (family q.1) q.2) (s₀, center s₀) :=
    (cDApi family (s₀, center s₀) hf.contDiffAt n).continuousAt
  have hcurve : ContinuousAt (fun s : P => (s, center s)) s₀ :=
    continuousAt_id.prodMk hc
  simpa only [Function.comp_def] using hpartial.comp (f := fun s : P => (s, center s)) hcurve
theorem alcmd [CompleteSpace F]
    (family : 𝕜 → E → F) (center : 𝕜 → E) (s₀ : 𝕜)
    (exceptional : Finset 𝕜) (m : Nat)
    (hf : AnalyticAt 𝕜 (Function.uncurry family) (s₀, center s₀))
    (hc : ContinuousAt center s₀)
    (hjets : ∀ᶠ s in nhds s₀, s ∉ exceptional → ∀ n < m,
      iteratedFDeriv 𝕜 n (family s) (center s) = 0) :
    ∀ n < m, iteratedFDeriv 𝕜 n (family s₀) (center s₀) = 0 := by
  exact lcmdj family center s₀ exceptional m
    (fun n _ => amdcA family center s₀ hf hc n) hjets
end Nagata.Workers.W17
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W28
open scoped BigOperators
def nFA (z : ℂ × CP) : CP := (z.2.1, z.1 * z.2.2)
def dAF (I : Finset ℕ) (j : ℕ → ℕ)
    (R : ℕ → MvPolynomial (Fin 2) ℂ) (u : ℕ) (κ : CP → CP)
    (z : ℂ × CP) : ℂ :=
  ∑ α ∈ I, z.1 ^ (α + j α - u) * z.2.2 ^ j α *
    pPE (R α) (κ (nFA z))
theorem nFAaA (z : ℂ × CP) :
    AnalyticAt ℂ nFA z := by
  have hs := (ContinuousLinearMap.fst ℂ ℂ CP).analyticAt z
  have hq := (ContinuousLinearMap.snd ℂ ℂ CP).analyticAt z
  have hu := ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt z.2).comp hq
  have hw := ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt z.2).comp hq
  exact hu.prod (hs.mul hw)
theorem dAFaA
    (I : Finset ℕ) (j : ℕ → ℕ) (R : ℕ → MvPolynomial (Fin 2) ℂ)
    (u : ℕ) (κ : CP → CP) (z : ℂ × CP)
    (hκ : AnalyticAt ℂ κ (nFA z)) :
    AnalyticAt ℂ (dAF I j R u κ) z := by
  have hs := (ContinuousLinearMap.fst ℂ ℂ CP).analyticAt z
  have hq := (ContinuousLinearMap.snd ℂ ℂ CP).analyticAt z
  have hw := ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt z.2).comp hq
  have hc := hκ.comp (nFAaA z)
  apply I.analyticAt_fun_sum
  intro α hα
  exact ((hs.pow (α + j α - u)).mul (hw.pow (j α))).mul
    ((pPEaA (R α) (κ (nFA z))).comp (f := κ ∘ nFA) hc)
theorem oFepm
    (I : Finset ℕ) (j : ℕ → ℕ) (R : ℕ → MvPolynomial (Fin 2) ℂ)
    (u : ℕ) (hmin : ∀ α ∈ I, u ≤ α + j α)
    (G : MvPolynomial (Fin 2) ℂ) (κ : CP → CP)
    (z : ℂ × CP)
    (hG : pPE G (κ (nFA z)) = z.1 * z.2.2) :
    (∑ α ∈ I, z.1 ^ α * pPE G (κ (nFA z)) ^ j α *
      pPE (R α) (κ (nFA z))) =
      z.1 ^ u * dAF I j R u κ z := by
  classical
  unfold dAF
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α hα
  have hw : u + (α + j α - u) = α + j α := Nat.add_sub_of_le (hmin α hα)
  rw [hG, mul_pow]
  simp only [← mul_assoc, ← pow_add, hw]
theorem dAFz
    (I : Finset ℕ) (j : ℕ → ℕ) (R : ℕ → MvPolynomial (Fin 2) ℂ)
    (u : ℕ) (hmin : ∀ α ∈ I, u ≤ α + j α)
    (κ : CP → CP) (q : CP) :
    dAF I j R u κ (0, q) =
      ∑ α ∈ I.filter (fun α => α + j α = u),
        q.2 ^ j α * pPE (R α) (κ (q.1, 0)) := by
  classical
  unfold dAF
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro α hα
  by_cases heq : α + j α = u
  · simp [heq, nFA]
  · have hpos : 0 < α + j α - u := Nat.sub_pos_of_lt
      (lt_of_le_of_ne (hmin α hα) (Ne.symm heq))
    simp [heq, zero_pow (Nat.ne_of_gt hpos)]
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology
def dNC1 (G : CP → ℂ) (L : CP →L[ℂ] ℂ)
    (p V : CP) : ℂ → ℂ :=
  Function.update (fun s : ℂ => s⁻¹ * G (p + s • V)) 0 (L V)
def dNC (G : CP → ℂ) (L : CP →L[ℂ] ℂ)
    (p V : CP) (s : ℂ) : CP :=
  ((p + s • V).1, dNC1 G L p V s)
theorem dNCz (G : CP → ℂ)
    (L : CP →L[ℂ] ℂ) (p V : CP) :
    dNC G L p V 0 = (p.1, L V) := by
  simp [dNC, dNC1]
theorem dNCcA
    (G : CP → ℂ) (L : CP →L[ℂ] ℂ) (p V : CP)
    (hG : HasFDerivAt G L p) (hp : G p = 0) :
    ContinuousAt (dNC G L p V) 0 := by
  have hn : ContinuousAt (dNC1 G L p V) 0 :=
    continuousAt_update_same.mpr (neavl G L p V hG hp)
  exact ((continuous_const.add (continuous_id.smul continuous_const)).fst.continuousAt).prodMk hn
theorem sdNC
    (G : MvPolynomial (Fin 2) ℂ) (L : CP →L[ℂ] ℂ)
    (p V : CP) (s : ℂ) (hs : s ≠ 0) :
    aNS s (dNC (pPE G) L p V s) =
      pNC G (p + s • V) := by
  ext <;> simp [aNS, dNC, dNC1,
    pNC, hs]
theorem iadNC
    (G : MvPolynomial (Fin 2) ℂ)
    (e : OpenPartialHomeomorph CP CP)
    (he : (e : CP → CP) = pNC G)
    (L : CP →L[ℂ] ℂ) (p V : CP) (s : ℂ) (hs : s ≠ 0)
    (hsource : p + s • V ∈ e.source) :
    e.symm (aNS s (dNC (pPE G) L p V s)) =
      p + s • V := by
  rw [sdNC G L p V s hs, ← he]
  exact e.left_inv hsource
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology
theorem edccc
    (G : MvPolynomial (Fin 2) ℂ)
    (e : OpenPartialHomeomorph CP CP)
    (he : (e : CP → CP) = pNC G)
    (L : CP →L[ℂ] ℂ) (p V : CP)
    (hp : p ∈ e.source) (hi : AnalyticAt ℂ e.symm (e p)) :
    ∀ᶠ s : ℂ in 𝓝 0, s ≠ 0 →
      p + s • V ∈ e.source ∧
      aNS s (dNC (pPE G) L p V s) ∈ e.target ∧
      AnalyticAt ℂ e.symm
        (aNS s (dNC (pPE G) L p V s)) := by
  have hm : ContinuousAt (fun s : ℂ => p + s • V) 0 :=
    (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
  have hs : ∀ᶠ s : ℂ in 𝓝 0, p + s • V ∈ e.source := by
    apply hm.preimage_mem_nhds
    simpa only [zero_smul, add_zero] using e.open_source.mem_nhds hp
  have hec : ContinuousAt e p := e.continuousAt hp
  have hm' : ContinuousAt (fun s : ℂ => e (p + s • V)) 0 := by
    have hh : ContinuousAt e (p + (0 : ℂ) • V) := by simpa using hec
    exact hh.comp (f := fun s : ℂ => p + s • V) hm
  have hinv : ∀ᶠ s : ℂ in 𝓝 0, AnalyticAt ℂ e.symm (e (p + s • V)) := by
    have hlocal : ∀ᶠ y in 𝓝 (e (p + (0 : ℂ) • V)), AnalyticAt ℂ e.symm y := by
      simpa only [zero_smul, add_zero] using hi.eventually_analyticAt
    exact hm'.tendsto.eventually hlocal
  filter_upwards [hs, hinv] with s hs hi hs0
  refine ⟨hs, ?_, ?_⟩
  · rw [sdNC G L p V s hs0, ← he]
    exact e.map_source hs
  · rwa [sdNC G L p V s hs0, ← he]
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators
def fPF (I : Finset ℕ) (j : ℕ → ℕ)
    (R : ℕ → MvPolynomial (Fin 2) ℂ) (G : MvPolynomial (Fin 2) ℂ)
    (s : ℂ) : MvPolynomial (Fin 2) ℂ :=
  ∑ α ∈ I, MvPolynomial.C (s ^ α) * (G ^ j α * R α)
theorem efPF (I : Finset ℕ) (j : ℕ → ℕ)
    (R : ℕ → MvPolynomial (Fin 2) ℂ) (G : MvPolynomial (Fin 2) ℂ)
    (s : ℂ) (p : CP) :
    pPE (fPF I j R G s) p =
      ∑ α ∈ I, s ^ α * pPE G p ^ j α * pPE (R α) p := by
  simp [fPF, pPE, mul_assoc]
theorem ffoid
    (I : Finset ℕ) (j : ℕ → ℕ) (R : ℕ → MvPolynomial (Fin 2) ℂ)
    (u : ℕ) (hmin : ∀ α ∈ I, u ≤ α + j α)
    (G : MvPolynomial (Fin 2) ℂ)
    (e : OpenPartialHomeomorph CP CP)
    (he : (e : CP → CP) = pNC G)
    (s : ℂ) (hs : s ≠ 0) (q : CP) (m : ℕ)
    (htarget : aNS s q ∈ e.target)
    (hei : AnalyticAt ℂ e.symm (aNS s q))
    (hP : Nagata.AM.oAL
      (fun i : Fin 2 => if i = 0 then (e.symm (aNS s q)).1
        else (e.symm (aNS s q)).2)
      m (fPF I j R G s)) :
    HAOAL (𝕜 := ℂ)
      (fun x => dAF I j R u e.symm (s, x)) q m := by
  have h := poiri
    (fPF I j R G s) e s q m hei hP
  apply (Nagata.Workers.W17.aocmi
    (fun x => dAF I j R u e.symm (s, x)) q m
    (s ^ u) (pow_ne_zero _ hs)).mp
  apply h.congr
  have ht : ∀ᶠ x in 𝓝 q, aNS s x ∈ e.target :=
    (aNSaA s q).continuousAt.preimage_mem_nhds
      (e.open_target.mem_nhds htarget)
  exact ht.mono fun x hx => by
    change pPE (fPF I j R G s)
      (e.symm (aNS s x)) = _
    rw [efPF]
    apply oFepm I j R u hmin G e.symm (s, x)
    exact rince G e he s x hx
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators
theorem nscj
    (I : Finset ℕ) (j : ℕ → ℕ) (R : ℕ → MvPolynomial (Fin 2) ℂ)
    (u : ℕ) (hmin : ∀ α ∈ I, u ≤ α + j α)
    (G : MvPolynomial (Fin 2) ℂ)
    (e : OpenPartialHomeomorph CP CP)
    (he : (e : CP → CP) = pNC G)
    (L : CP →L[ℂ] ℂ) (p V : CP)
    (hsource : p ∈ e.source) (hi : AnalyticAt ℂ e.symm (e p))
    (hG : HasFDerivAt (pPE G) L p)
    (hp : pPE G p = 0)
    (exceptional : Finset ℂ) (m : ℕ)
    (horders : ∀ᶠ s : ℂ in 𝓝 0, s ∉ exceptional →
      Nagata.AM.oAL
        (fun i : Fin 2 => if i = 0 then (p + s • V).1 else (p + s • V).2)
        m (fPF I j R G s)) :
    ∀ n < m, iteratedFDeriv ℂ n
      (fun q : CP =>
        ∑ α ∈ I.filter (fun α => α + j α = u),
          q.2 ^ j α * pPE (R α) (e.symm (q.1, 0)))
      (p.1, L V) = 0 := by
  classical
  let center := dNC (pPE G) L p V
  let family : ℂ → CP → ℂ := fun s q => dAF I j R u e.symm (s, q)
  have hc : ContinuousAt center 0 := dNCcA _ L p V hG hp
  have hc0 : center 0 = (p.1, L V) := dNCz _ L p V
  have harg : nFA (0, center 0) = e p := by
    rw [hc0, he]
    simp [nFA, pNC, hp]
  have hf : AnalyticAt ℂ (Function.uncurry family) (0, center 0) := by
    apply dAFaA
    rwa [harg]
  have hchart := edccc G e he L p V hsource hi
  have hjets : ∀ᶠ s : ℂ in 𝓝 0, s ∉ insert 0 exceptional → ∀ n < m,
      iteratedFDeriv ℂ n (family s) (center s) = 0 := by
    filter_upwards [hchart, horders] with s hs ho hex
    have hs0 : s ≠ 0 := fun hz => hex (hz ▸ Finset.mem_insert_self _ _)
    have hexc : s ∉ exceptional := fun h => hex (Finset.mem_insert_of_mem h)
    obtain ⟨hsour, htar, hainv⟩ := hs hs0
    have hpoint := iadNC G e he L p V s hs0 hsour
    have hord : Nagata.AM.oAL
        (fun i : Fin 2 => if i = 0 then (e.symm (aNS s (center s))).1
          else (e.symm (aNS s (center s))).2)
        m (fPF I j R G s) := by
      simpa only [center, hpoint] using ho hexc
    obtain ⟨P, hP, hz⟩ := ffoid
      I j R u hmin G e he s hs0 (center s) m htar hainv hord
    exact Nagata.W19.ttvop hP m hz
  have hlim := Nagata.Workers.W17.alcmd
    family center 0 (insert 0 exceptional) m hf hc hjets
  intro n hn
  have hh := hlim n hn
  simp only [family, hc0] at hh
  simpa only [dAFz I j R u hmin] using hh
end Nagata.Workers.W28
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W16.AB
open Nagata.PG
variable {n : ℕ} (G : NHF n)
structure BV (k : ℕ) where
  x : Fin 3 → ℂ
  x_ne_zero : x ≠ 0
  on_curve : MvPolynomial.eval x G.polynomial = 0
  w : ℂ
variable {G}
def Equ {k : ℕ} (a b : BV G k) : Prop :=
  ∃ u : ℂˣ, a.x = (u : ℂ) • b.x ∧ a.w = (u : ℂ) ^ k * b.w
theorem er {k : ℕ} (a : BV G k) : Equ a a := by
  exact ⟨1, by simp, by simp⟩
theorem es {k : ℕ} {a b : BV G k}
    (h : Equ a b) : Equ b a := by
  obtain ⟨u, hx, hw⟩ := h
  refine ⟨u⁻¹, ?_, ?_⟩
  · rw [hx, smul_smul]
    simp
  · rw [hw, ← mul_assoc, ← mul_pow]
    simp
theorem et {k : ℕ} {a b c : BV G k}
    (hab : Equ a b) (hbc : Equ b c) : Equ a c := by
  obtain ⟨u, hux, huw⟩ := hab
  obtain ⟨v, hvx, hvw⟩ := hbc
  refine ⟨u * v, ?_, ?_⟩
  · rw [hux, hvx, smul_smul]
    rfl
  · rw [huw, hvw]
    simp [mul_pow, mul_assoc]
def bS (G : NHF n) (k : ℕ) : Setoid (BV G k) where
  r := Equ
  iseqv := ⟨er, es, et⟩
def TS (G : NHF n) (k : ℕ) := Quotient (bS G k)
def mk {k : ℕ} (a : BV G k) : TS G k := Quotient.mk _ a
open scoped BigOperators
def wE (s : Finset ℕ) (T : ℕ → PP1) (j : ℕ → ℕ)
    (x : Fin 3 → ℂ) (w : ℂ) : ℂ :=
  ∑ a ∈ s, MvPolynomial.eval x (T a) * w ^ j a
theorem wEs (s : Finset ℕ) (T : ℕ → PP1) (j : ℕ → ℕ)
    (d k : ℕ) (hdeg : ∀ a ∈ s, (T a).IsHomogeneous (d - k * j a))
    (hkj : ∀ a ∈ s, k * j a ≤ d) (x : Fin 3 → ℂ) (w u : ℂ) :
    wE s T j (u • x) (u ^ k * w) = u ^ d * wE s T j x w := by
  unfold wE
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  change MvPolynomial.eval (fun i => u * x i) (T a) * (u ^ k * w) ^ j a = _
  rw [hes (hdeg a ha), mul_pow, ← pow_mul]
  calc
    (u ^ (d - k * j a) * MvPolynomial.eval x (T a)) *
        (u ^ (k * j a) * w ^ j a) =
      (u ^ (d - k * j a) * u ^ (k * j a)) *
        (MvPolynomial.eval x (T a) * w ^ j a) := by ac_rfl
    _ = u ^ d * (MvPolynomial.eval x (T a) * w ^ j a) := by
      rw [← pow_add, Nat.sub_add_cancel (hkj a ha)]
end Nagata.W16.AB
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W07
open Nagata.W08
def sE1 (τ : ℂ) (n : ℤ) (γ z : ℂ) :
    aS τ n γ →ₗ[ℂ] ℂ where
  toFun f := f.val z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def sTE (τ : ℂ) (n : ℤ) (γ z w : ℂ) :
    aS τ n γ →ₗ[ℂ] ℂ × ℂ :=
  (sE1 τ n γ z).prod (sE1 τ n γ w)
@[simp] theorem msTEk (τ : ℂ) (n : ℤ) (γ z w : ℂ)
    (f : aS τ n γ) :
    f ∈ LinearMap.ker (sTE τ n γ z w) ↔ f.val z = 0 ∧ f.val w = 0 := by
  change (f.val z, f.val w) = (0, 0) ↔ _
  simp only [Prod.mk.injEq]
theorem lMsok
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (L : V →ₗ[ℂ] W)
    (hdim : Module.finrank ℂ (LinearMap.ker L) + Module.finrank ℂ W =
      Module.finrank ℂ V) : Function.Surjective L := by
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  have hr := L.finrank_range_add_finrank_ker
  omega
theorem ces (τ γ z : ℂ)
    (h3 : Module.finrank ℂ (aS τ 3 γ) = 3)
    (hker : Module.finrank ℂ (LinearMap.ker (sE1 τ 3 γ z)) = 2) :
    Function.Surjective (sE1 τ 3 γ z) := by
  let : FiniteDimensional ℂ (aS τ 3 γ) :=
    FiniteDimensional.of_finrank_pos (by omega)
  apply lMsok
  simp [h3, hker]
theorem ceseo (τ γ z : ℂ)
    (h3 : Module.finrank ℂ (aS τ 3 γ) = 3)
    (hker : Module.finrank ℂ (LinearMap.ker (sE1 τ 3 γ z)) = 2) :
    ∃ f : aS τ 3 γ, f.val z = 1 :=
  ces τ γ z h3 hker 1
theorem ctEs (τ γ z w : ℂ)
    (h3 : Module.finrank ℂ (aS τ 3 γ) = 3)
    (hker : Module.finrank ℂ (LinearMap.ker (sTE τ 3 γ z w)) = 1) :
    Function.Surjective (sTE τ 3 γ z w) := by
  let : FiniteDimensional ℂ (aS τ 3 γ) :=
    FiniteDimensional.of_finrank_pos (by omega)
  apply lMsok
  simp [Module.finrank_prod, h3, hker]
theorem cess (τ γ z w : ℂ)
    (h3 : Module.finrank ℂ (aS τ 3 γ) = 3)
    (hker : Module.finrank ℂ (LinearMap.ker (sTE τ 3 γ z w)) = 1) :
    ∃ f : aS τ 3 γ, f.val z = 1 ∧ f.val w = 0 := by
  obtain ⟨f, hf⟩ := ctEs τ γ z w h3 hker (1, 0)
  exact ⟨f, Prod.mk.inj hf⟩
end Nagata.W07
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W07
open Nagata.W08 Filter Topology
theorem szmi {τ γ z : ℂ} {n : ℤ} (hγ : γ ≠ 0) (hz : z ≠ 0)
    (f : aS τ n γ) : f.val (τ * z) = 0 ↔ f.val z = 0 := by
  rw [f.property.2.2 z hz]
  simp only [mul_eq_zero, hγ, zpow_ne_zero _ hz, false_or]
theorem iz {G α : Type*} [CommGroup G] (τ : G) (F : G → α)
    (hstep : ∀ z, F (τ * z) = F z) (z : G) (k : ℤ) : F (τ ^ k * z) = F z := by
  have he : (fun k : ℤ => F (τ ^ k * z)) = (fun _ : ℤ => F z) := by
    apply Nagata.W08.bIu (fun _ x => x)
    · intro _ _ _ h
      exact h
    · intro j
      rw [zpow_add, zpow_one, mul_comm (τ ^ j) τ, mul_assoc]
      exact hstep (τ ^ j * z)
    · intro _
      rfl
    · simp
  exact congrFun he k
theorem szoi {τ γ a : ℂ} {n : ℤ}
    (hτ : τ ≠ 0) (hγ : γ ≠ 0) (ha : a ≠ 0)
    (f : aS τ n γ) (k : ℤ) :
    f.val (τ ^ k * a) = 0 ↔ f.val a = 0 := by
  let τu : ℂˣ := Units.mk0 τ hτ
  let au : ℂˣ := Units.mk0 a ha
  have h := iz τu (fun z : ℂˣ => f.val (z : ℂ) = 0)
    (fun z => propext (szmi hγ z.ne_zero f)) au k
  simpa [τu, au] using Iff.of_eq h
theorem sooi {τ γ z : ℂ} {n : ℤ}
    (f : aS τ n γ) (hz : z ≠ 0) :
    (1 : ℕ∞) ≤ analyticOrderAt f.val z ↔ f.val z = 0 := by
  have h := natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    (n := 1) (aSaA f hz)
  simpa using h
end Nagata.W07
end
end
section
noncomputable section
namespace Nagata.W07
open Nagata.W08 Nagata.CS
def pTM {τ a : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0)
    (n : ℤ) (γ : ℂ) (k : ℕ) :
    aS τ (n - (k : ℤ)) (γ / (-a) ^ k) →ₗ[ℂ]
      aS τ n γ :=
  LinearMap.codRestrict (aS τ n γ)
    (mS2 τ (γ / (-a) ^ k) (n - (k : ℤ))
      (tPS hτ hτ0 ha).val k) (by
    intro G
    change mP2 (tPS hτ hτ0 ha).val k G.val ∈
      aS τ n γ
    have h := mPms (tPS hτ hτ0 ha).property G.property k
    have hdeg : n - (k : ℤ) + (k : ℤ) * 1 = n := by ring
    have hgam : (γ / (-a) ^ k) * (-a) ^ k = γ :=
      div_mul_cancel₀ γ (pow_ne_zero k (neg_ne_zero.mpr ha))
    simpa only [hdeg, hgam] using h)
theorem pTont {τ a z : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hz : z ≠ 0) :
    analyticOrderAt (tPS hτ hτ0 ha).val z ≠ ⊤ := by
  by_cases hP : (tPS hτ hτ0 ha).val z = 0
  · rw [(aSaA _ hz).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
      hP (tPSzh hτ hτ0 ha hz hP)]
    simp
  · rw [(aSaA _ hz).analyticOrderAt_eq_zero.mpr hP]
    simp
theorem pTMi {τ a : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (n : ℤ) (γ : ℂ) (k : ℕ) :
    Function.Injective (pTM hτ hτ0 ha n γ k) := by
  have hinj := mSi τ (γ / (-a) ^ k) (n - (k : ℤ))
    (tPS hτ hτ0 ha).val k
    (aSaON _) (fun z hz => pTont hτ hτ0 ha hz)
  intro f g hfg
  apply hinj
  exact congrArg Subtype.val hfg
theorem pTMre {τ a γ : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hγ : γ ≠ 0) (n : ℤ) :
    LinearMap.range (pTM hτ hτ0 ha n γ 1) =
      LinearMap.ker (sE1 τ n γ a) := by
  ext f
  constructor
  · rintro ⟨G, rfl⟩
    change (tPS hτ hτ0 ha).val a ^ 1 * G.val a = 0
    simp
  · intro hf
    have hfa : f.val a = 0 := hf
    have hzero : ∀ z ≠ 0, (tPS hτ hτ0 ha).val z = 0 →
        deriv (tPS hτ hτ0 ha).val z ≠ 0 ∧
          (1 : ℕ∞) ≤ analyticOrderAt f.val z := by
      intro z hz hP
      refine ⟨tPSzh hτ hτ0 ha hz hP, ?_⟩
      apply (sooi f hz).mpr
      obtain ⟨k, hk⟩ := (tPSzi hτ hτ0 ha hz).mp hP
      rw [hk, mul_comm a]
      exact (szoi hτ0 hγ ha f k).mpr hfa
    obtain ⟨G, hG⟩ : ∃ G : aS τ (n - (1 : ℤ)) (γ / (-a) ^ 1),
        ∀ z ≠ 0, f.val z = (tPS hτ hτ0 ha).val z ^ 1 * G.val z := by
      obtain ⟨G, hG⟩ := ehq hτ0 (neg_ne_zero.mpr ha)
        f (tPS hτ hτ0 ha) 1 hzero
      refine ⟨⟨G.val, ?_⟩, hG⟩
      simpa only [Nat.cast_one, mul_one] using G.property
    refine ⟨G, aSe _ _ ?_⟩
    intro z hz
    exact (hG z hz).symm
theorem sEkf {τ a γ : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hγ : γ ≠ 0) (n : ℤ) :
    Module.finrank ℂ (LinearMap.ker (sE1 τ n γ a)) =
      Module.finrank ℂ (aS τ (n - 1) (γ / (-a))) := by
  rw [← pTMre hτ hτ0 ha hγ n,
    LinearMap.finrank_range_of_inj (pTMi hτ hτ0 ha n γ 1)]
  rw [pow_one]
  rfl
end Nagata.W07
end
end
section
noncomputable section
namespace Nagata.W07
open Nagata.W08
def tPTM {τ a : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0)
    (n : ℤ) (γ b : ℂ) :
    LinearMap.ker (sE1 τ (n - (1 : ℤ)) (γ / (-a) ^ 1) b) →ₗ[ℂ]
      aS τ n γ :=
  (pTM hτ hτ0 ha n γ 1).comp
    (LinearMap.ker (sE1 τ (n - (1 : ℤ)) (γ / (-a) ^ 1) b)).subtype
theorem tPTMi {τ a : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (n : ℤ) (γ b : ℂ) :
    Function.Injective (tPTM hτ hτ0 ha n γ b) :=
  (pTMi hτ hτ0 ha n γ 1).comp Subtype.val_injective
theorem tPTMr {τ a b γ : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hγ : γ ≠ 0) (hab : ¬ ∃ k : ℤ, b = a * τ ^ k) (n : ℤ) :
    LinearMap.range (tPTM hτ hτ0 ha n γ b) =
      LinearMap.ker (sTE τ n γ a b) := by
  have hPb : (tPS hτ hτ0 ha).val b ≠ 0 := by
    intro hz
    exact hab ((tPSzi hτ hτ0 ha hb).mp hz)
  ext f
  constructor
  · rintro ⟨G, rfl⟩
    apply (msTEk τ n γ a b _).mpr
    constructor
    · change (tPS hτ hτ0 ha).val a ^ 1 * G.val.val a = 0
      simp
    · have hGb : G.val.val b = 0 := G.property
      change (tPS hτ hτ0 ha).val b ^ 1 * G.val.val b = 0
      rw [hGb, mul_zero]
  · intro hf
    obtain ⟨hfa, hfb⟩ := (msTEk τ n γ a b f).mp hf
    have hfrange : f ∈ LinearMap.range (pTM hτ hτ0 ha n γ 1) := by
      rw [pTMre hτ hτ0 ha hγ n]
      exact hfa
    obtain ⟨G, hG⟩ := hfrange
    have hGb : G.val b = 0 := by
      have he := congrArg (fun F : aS τ n γ => F.val b) hG
      change (tPS hτ hτ0 ha).val b ^ 1 * G.val b = f.val b at he
      rw [pow_one, hfb] at he
      exact (mul_eq_zero.mp he).resolve_left hPb
    exact ⟨⟨G, hGb⟩, hG⟩
theorem sTEkf {τ a b γ : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hγ : γ ≠ 0) (hab : ¬ ∃ k : ℤ, b = a * τ ^ k) (n : ℤ) :
    Module.finrank ℂ (LinearMap.ker (sTE τ n γ a b)) =
      Module.finrank ℂ (aS τ (n - 2) ((γ / (-a)) / (-b))) := by
  rw [← tPTMr hτ hτ0 ha hb hγ hab n,
    LinearMap.finrank_range_of_inj (tPTMi hτ hτ0 ha n γ b)]
  rw [sEkf hτ hτ0 hb
    (div_ne_zero hγ (pow_ne_zero 1 (neg_ne_zero.mpr ha))) (n - 1)]
  rw [pow_one, show n - (1 : ℤ) - 1 = n - 2 by ring]
end Nagata.W07
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W07
open Nagata.W08 Nagata.W21
def cEV {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (aS τ 3 γ)) (z : ℂ) : Fin 3 → ℂ :=
  fun i => (b i).val z
theorem cbf {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (aS τ 3 γ)) :
    Module.finrank ℂ (aS τ 3 γ) = 3 := by
  simpa using Module.finrank_eq_card_basis b
theorem cEVnz {τ γ z : ℂ}
    (b : Module.Basis (Fin 3) ℂ (aS τ 3 γ))
    (hker : Module.finrank ℂ (LinearMap.ker (sE1 τ 3 γ z)) = 2) :
    cEV b z ≠ 0 := by
  intro hv
  obtain ⟨f, hf⟩ := ceseo τ γ z (cbf b) hker
  have heval : sE1 τ 3 γ z = 0 := by
    apply b.ext
    intro i
    exact congrFun hv i
  have hf0 : f.val z = 0 := congrArg (fun L : aS τ 3 γ →ₗ[ℂ] ℂ => L f) heval
  exact one_ne_zero (hf.symm.trans hf0)
def cCM {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (aS τ 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sE1 τ 3 γ z)) = 2)
    (z : ℂˣ) : Projectivization ℂ (Fin 3 → ℂ) :=
  Projectivization.mk ℂ (cEV b (z : ℂ))
    (cEVnz b (hbase z z.ne_zero))
theorem cCMno {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (aS τ 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sE1 τ 3 γ z)) = 2)
    (z w : ℂˣ)
    (hker : Module.finrank ℂ (LinearMap.ker (sTE τ 3 γ z w)) = 1) :
    cCM b hbase z ≠ cCM b hbase w := by
  intro he
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp he
  have hev : sE1 τ 3 γ z = a • sE1 τ 3 γ w := by
    apply b.ext
    intro i
    exact (congrFun ha i).symm
  obtain ⟨f, hfz, hfw⟩ := cess τ γ z w
    (cbf b) hker
  have heq := congrArg (fun L : aS τ 3 γ →ₗ[ℂ] ℂ => L f) hev
  change f.val z = a * f.val w at heq
  rw [hfz, hfw, mul_zero] at heq
  exact one_ne_zero heq
theorem cCMp (τ : ℂˣ) {γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (aS (τ : ℂ) 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sE1 τ 3 γ z)) = 2)
    (z : ℂˣ) : cCM b hbase (τ * z) = cCM b hbase z := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨γ * (z : ℂ) ^ (-3 : ℤ), ?_⟩
  funext i
  exact ((b i).property.2.2 (z : ℂ) z.ne_zero).symm
theorem cCMz (τ : ℂˣ) {γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (aS (τ : ℂ) 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sE1 τ 3 γ z)) = 2)
    (z : ℂˣ) (k : ℤ) :
    cCM b hbase (τ ^ k * z) = cCM b hbase z := by
  have he : (fun k : ℤ => cCM b hbase (τ ^ k * z)) =
      (fun _ : ℤ => cCM b hbase z) := by
    apply Nagata.W08.bIu (fun _ x => x)
    · intro _ _ _ h
      exact h
    · intro j
      rw [zpow_add, zpow_one, mul_comm (τ ^ j) τ, mul_assoc]
      exact cCMp τ b hbase (τ ^ j * z)
    · intro _
      rfl
    · simp
  exact congrFun he k
def cTM (τ : ℂˣ) {γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (aS (τ : ℂ) 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sE1 τ 3 γ z)) = 2) :
    TP1 τ → Projectivization ℂ (Fin 3 → ℂ) :=
  Quotient.lift (cCM b hbase) (by
    intro z w h
    obtain ⟨k, rfl⟩ := h
    exact (cCMz τ b hbase z k).symm)
theorem cTMi (τ : ℂˣ) {γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (aS (τ : ℂ) 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sE1 τ 3 γ z)) = 2)
    (hsep : ∀ z w : ℂˣ, ¬ tOS τ z w →
      Module.finrank ℂ (LinearMap.ker (sTE τ 3 γ z w)) = 1) :
    Function.Injective (cTM τ b hbase) := by
  intro p q
  refine Quotient.inductionOn₂ p q ?_
  intro z w hmap
  apply Quotient.sound
  by_contra hrel
  exact (cCMno b hbase z w (hsep z w hrel)) hmap
end Nagata.W07
end
end
section
noncomputable section
namespace Nagata.W07
open Nagata.W08 Nagata.W21
theorem cekd {τ γ z : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (hγ : γ ≠ 0) (hz : z ≠ 0)
    (h2 : ∀ δ : ℂ, δ ≠ 0 → Module.finrank ℂ (aS τ 2 δ) = 2) :
    Module.finrank ℂ (LinearMap.ker (sE1 τ 3 γ z)) = 2 := by
  rw [sEkf hτ hτ0 hz hγ 3]
  exact h2 _ (div_ne_zero hγ (neg_ne_zero.mpr hz))
theorem ctEkd {τ γ z w : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (hγ : γ ≠ 0) (hz : z ≠ 0) (hw : w ≠ 0)
    (hzw : ¬ ∃ k : ℤ, w = z * τ ^ k)
    (h1 : ∀ δ : ℂ, δ ≠ 0 → Module.finrank ℂ (aS τ 1 δ) = 1) :
    Module.finrank ℂ (LinearMap.ker (sTE τ 3 γ z w)) = 1 := by
  rw [sTEkf hτ hτ0 hz hw hγ hzw 3]
  exact h1 _ (div_ne_zero (div_ne_zero hγ (neg_ne_zero.mpr hz)) (neg_ne_zero.mpr hw))
end Nagata.W07
end
end
section
noncomputable section
namespace Nagata.W07
open Nagata.W08 Nagata.W21 Nagata.PG
def cP1 {τ : ℝ} (hτ : 0 < τ) : ℂˣ :=
  Units.mk0 (τ : ℂ) (by exact_mod_cast ne_of_gt hτ)
@[simp] theorem cPv {τ : ℝ} (hτ : 0 < τ) :
    ((cP1 hτ : ℂˣ) : ℂ) = (τ : ℂ) := rfl
theorem rPnlo {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) :
    ‖(τ : ℂ)‖ < 1 := by
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ] using hτone
theorem aPSf {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {n : ℤ} (hn : 0 < n) {γ : ℂ} (hγ : γ ≠ 0) :
    Module.finrank ℂ (aS (τ : ℂ) n γ) = n.toNat :=
  Nagata.Workers.W10.pSf hτ hτone
    (fun n γ => Nagata.W01.lCMi _ n γ) hn hγ
def aCB {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {γ : ℂ} (hγ : γ ≠ 0) :
    Module.Basis (Fin 3) ℂ (aS (τ : ℂ) 3 γ) :=
  Nagata.Workers.W10.pSBF hτ hτone
    (fun n γ => Nagata.W01.lCMi _ n γ)
    (show (0 : ℤ) < 3 by decide) hγ
theorem aCekd {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {γ : ℂ} (hγ : γ ≠ 0) {z : ℂ} (hz : z ≠ 0) :
    Module.finrank ℂ (LinearMap.ker (sE1 (τ : ℂ) 3 γ z)) = 2 :=
  cekd (rPnlo hτ hτone)
    (cP1 hτ).ne_zero hγ hz
    (fun _ hd => aPSf hτ hτone (by decide) hd)
def aCM {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {γ : ℂ} (hγ : γ ≠ 0) : TP1 (cP1 hτ) → PP :=
  cTM (cP1 hτ) (aCB hτ hτone hγ)
    (fun _ hz => aCekd hτ hτone hγ hz)
theorem aCMi {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {γ : ℂ} (hγ : γ ≠ 0) : Function.Injective (aCM hτ hτone hγ) := by
  apply cTMi
  intro z w hrel
  apply ctEkd (rPnlo hτ hτone)
    (cP1 hτ).ne_zero hγ z.ne_zero w.ne_zero
  · rintro ⟨k, hk⟩
    apply hrel
    refine ⟨k, Units.ext ?_⟩
    simpa only [Units.val_mul, Units.val_zpow_eq_zpow_val, cPv, mul_comm]
      using hk.symm
  · intro δ hδ
    exact aPSf hτ hτone (by decide) hδ
end Nagata.W07
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W02
theorem enlR {K V I : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Module.Finite K V] [Fintype I]
    (v : I → V) (hdim : Module.finrank K V < Fintype.card I) :
    ∃ c : I →₀ K, c ≠ 0 ∧ Finsupp.linearCombination K v c = 0 := by
  have hdep : ¬ LinearIndependent K v := by
    intro h
    exact (not_le_of_gt hdim) h.fintype_card_le_finrank
  obtain ⟨c, hc, hne⟩ := not_linearIndependent_iff_linearCombination.mp hdep
  exact ⟨c, hne, hc⟩
end Nagata.W02
end
end
section
noncomputable section
namespace Nagata.W02
theorem cEs1 (e : DE 3) : ∑ i, e.val i = 3 := by
  simpa only [← Finsupp.degree_eq_sum] using e.property
theorem acMf {K X : Type*} [Field K]
    (s : Fin 3 → X → K) (e : DE 3) :
    MvPolynomial.aeval s (MvPolynomial.monomial e.val (1 : K)) =
      fun z => ∏ i, s i z ^ e.val i := by
  rw [MvPolynomial.aeval_monomial, map_one, one_mul]
  rw [Finsupp.prod_pow]
  funext z
  simp
end Nagata.W02
end
end
section
noncomputable section
namespace Nagata.W02
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]
theorem ccE : Fintype.card (DE 3) = 10 := by
  rw [cdE]
  decide
theorem enhCr (s : Fin 3 → A)
    (W : Submodule K A) [Module.Finite K W]
    (hdim : Module.finrank K W ≤ 9)
    (hmon : ∀ e : DE 3,
      MvPolynomial.aeval s (MvPolynomial.monomial e.val (1 : K)) ∈ W) :
    ∃ P : MvPolynomial (Fin 3) K,
      P ≠ 0 ∧ P.IsHomogeneous 3 ∧ MvPolynomial.aeval s P = 0 := by
  let v : DE 3 → W := fun e => ⟨_, hmon e⟩
  have hd : Module.finrank K W < Fintype.card (DE 3) := by
    rw [ccE]
    omega
  obtain ⟨c, hcne, hc⟩ := enlR v hd
  let F := (hCE K 3).symm c
  have hFne : F ≠ 0 := by
    intro hz
    apply hcne
    have h := congrArg (hCE K 3) hz
    simpa only [F, LinearEquiv.apply_symm_apply, map_zero] using h
  refine ⟨F.val, ?_, F.property, ?_⟩
  · intro hz
    exact hFne (Subtype.ext hz)
  · change MvPolynomial.aeval s
      (((hCE K 3).symm c) : MvPolynomial (Fin 3) K) = 0
    rw [ahCEs]
    have hambient := congrArg (fun x : W => (x : A)) hc
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum, Submodule.coe_sum,
      Submodule.coe_smul, Submodule.coe_zero, v] using hambient
end Nagata.W02
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W21
instance projectivizationTopologicalSpace (K V : Type*) [DivisionRing K]
    [AddCommGroup V] [Module K V] [TopologicalSpace V] :
    TopologicalSpace (Projectivization K V) :=
  inferInstanceAs (TopologicalSpace (Quotient (projectivizationSetoid K V)))
theorem cpm (K V : Type*) [DivisionRing K]
    [AddCommGroup V] [Module K V] [TopologicalSpace V] :
    Continuous (Projectivization.mk' K : {v : V // v ≠ 0} → Projectivization K V) :=
  continuous_quotient_mk'
theorem iQMpm (K V : Type*) [DivisionRing K]
    [AddCommGroup V] [Module K V] [TopologicalSpace V] :
    Topology.IsQuotientMap (Projectivization.mk' K : {v : V // v ≠ 0} → Projectivization K V) :=
  isQuotientMap_quotient_mk'
end Nagata.W21
end
section
noncomputable section
open Topology Set
namespace Nagata.Workers.W11
variable {ι : Type*}
theorem pmeim
    (v w : {x : ι → ℂ // x ≠ 0}) :
    Projectivization.mk' ℂ v = Projectivization.mk' ℂ w ↔
      ∀ i j, v.val i * w.val j = v.val j * w.val i := by
  rw [Projectivization.mk'_eq_mk, Projectivization.mk'_eq_mk,
    Projectivization.mk_eq_mk_iff']
  constructor
  · rintro ⟨a, ha⟩ i j
    have hi := congrFun ha i
    have hj := congrFun ha j
    change a * w.val i = v.val i at hi
    change a * w.val j = v.val j at hj
    rw [← hi, ← hj]
    ring
  · intro h
    have hn : ∃ i, w.val i ≠ 0 := by
      by_contra hn
      apply w.property
      funext i
      exact not_not.mp (fun hi => hn ⟨i, hi⟩)
    obtain ⟨i, hi⟩ := hn
    refine ⟨v.val i / w.val i, ?_⟩
    funext j
    change v.val i / w.val i * w.val j = v.val j
    rw [div_mul_eq_mul_div, div_eq_iff hi]
    exact h i j
theorem iCpr :
    IsClosed {p : {x : ι → ℂ // x ≠ 0} × {x : ι → ℂ // x ≠ 0} |
      Projectivization.mk' ℂ p.1 = Projectivization.mk' ℂ p.2} := by
  have heq : {p : {x : ι → ℂ // x ≠ 0} × {x : ι → ℂ // x ≠ 0} |
      Projectivization.mk' ℂ p.1 = Projectivization.mk' ℂ p.2} =
      ⋂ i, ⋂ j, {p | p.1.val i * p.2.val j = p.1.val j * p.2.val i} := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter]
    exact pmeim p.1 p.2
  rw [heq]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  apply isClosed_eq
  · exact (((continuous_apply i).comp continuous_subtype_val).comp continuous_fst).mul
      (((continuous_apply j).comp continuous_subtype_val).comp continuous_snd)
  · exact (((continuous_apply j).comp continuous_subtype_val).comp continuous_fst).mul
      (((continuous_apply i).comp continuous_subtype_val).comp continuous_snd)
def sNV (a : ℂˣ) (v : {x : ι → ℂ // x ≠ 0}) :
    {x : ι → ℂ // x ≠ 0} :=
  ⟨(a : ℂ) • v.val, smul_ne_zero (Units.ne_zero a) v.property⟩
theorem csNV (a : ℂˣ) :
    Continuous (sNV (ι := ι) a) := by
  exact (continuous_const_smul (a : ℂ)).comp continuous_subtype_val |>.subtype_mk _
theorem iOMpm :
    IsOpenMap (Projectivization.mk' ℂ : {x : ι → ℂ // x ≠ 0} →
      Projectivization ℂ (ι → ℂ)) := by
  intro U hU
  apply (Nagata.W21.iQMpm ℂ (ι → ℂ)).isOpen_preimage.mp
  have heq : (Projectivization.mk' ℂ) ⁻¹' (Projectivization.mk' ℂ '' U) =
      ⋃ a : ℂˣ, sNV a ⁻¹' U := by
    ext v
    constructor
    · rintro ⟨u, hu, huv⟩
      obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℂ u.val v.val
        u.property v.property).mp huv
      apply mem_iUnion.mpr
      refine ⟨a, ?_⟩
      have hs : sNV a v = u := Subtype.ext ha
      simpa only [mem_preimage, hs] using hu
    · intro hv
      obtain ⟨a, ha⟩ := mem_iUnion.mp hv
      refine ⟨sNV a v, ha, ?_⟩
      apply (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mpr
      exact ⟨a, rfl⟩
  rw [heq]
  exact isOpen_iUnion fun a => hU.preimage (csNV a)
theorem iOQMp :
    IsOpenQuotientMap (Projectivization.mk' ℂ : {x : ι → ℂ // x ≠ 0} →
      Projectivization ℂ (ι → ℂ)) :=
  ⟨(Nagata.W21.iQMpm ℂ (ι → ℂ)).surjective,
    Nagata.W21.cpm ℂ (ι → ℂ),
    iOMpm⟩
instance complexProjectivizationT2Space (ι : Type*) :
    T2Space (Projectivization ℂ (ι → ℂ)) :=
  (t2Space_iff_of_isOpenQuotientMap
    (iOQMp (ι := ι))).mpr
      iCpr
end Nagata.Workers.W11
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W21
open scoped BigOperators
open Nagata.W08
theorem cSPm {τ γ : ℂ}
    (b : Fin 3 → aS τ 3 γ) (e : Fin 3 → ℕ)
    (he : ∑ i, e i = 3) :
    (fun z ↦ ∏ i, (b i).val z ^ e i) ∈ aS τ 9 (γ ^ 3) := by
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [(b _).property.1]
    rw [Finset.prod_pow_eq_pow_sum, he]
    exact zero_pow (by decide)
  · intro z hz
    exact DifferentiableAt.fun_finsetProd fun i _ ↦ ((b i).property.2.1 z hz).pow (e i)
  · intro z hz
    change (∏ i, (b i).val (τ * z) ^ e i) =
      γ ^ 3 * z ^ (-9 : ℤ) * ∏ i, (b i).val z ^ e i
    simp_rw [(b _).property.2.2 z hz, mul_pow]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, he]
    have hp : (z ^ (-3 : ℤ)) ^ (3 : ℕ) = z ^ (-9 : ℤ) := by
      rw [← zpow_natCast, ← zpow_mul]
      rfl
    rw [hp]
end Nagata.W21
end
section
namespace Nagata.W21
open Nagata.W08
theorem ecRod {τ γ : ℂ}
    (b : Fin 3 → aS τ 3 γ)
    [Module.Finite ℂ (aS τ 9 (γ ^ 3))]
    (hdim : Module.finrank ℂ (aS τ 9 (γ ^ 3)) ≤ 9) :
    ∃ P : MvPolynomial (Fin 3) ℂ,
      P ≠ 0 ∧ P.IsHomogeneous 3 ∧
      MvPolynomial.aeval (fun i ↦ (b i).val) P = 0 := by
  apply Nagata.W02.enhCr
    (fun i ↦ (b i).val) (aS τ 9 (γ ^ 3)) hdim
  intro e
  rw [Nagata.W02.acMf]
  exact cSPm b e.val (Nagata.W02.cEs1 e)
theorem ecEod {τ γ : ℂ}
    (b : Fin 3 → aS τ 3 γ)
    [Module.Finite ℂ (aS τ 9 (γ ^ 3))]
    (hdim : Module.finrank ℂ (aS τ 9 (γ ^ 3)) ≤ 9) :
    ∃ P : MvPolynomial (Fin 3) ℂ,
      P ≠ 0 ∧ P.IsHomogeneous 3 ∧ ∀ z : ℂ,
      MvPolynomial.aeval (fun i ↦ (b i).val z) P = 0 := by
  obtain ⟨P, hP, hhom, he⟩ := ecRod b hdim
  refine ⟨P, hP, hhom, ?_⟩
  intro z
  have h := congrArg (Pi.evalAlgHom ℂ (fun _ : ℂ ↦ ℂ) z) he
  simpa only [MvPolynomial.comp_aeval_apply, map_zero, Pi.evalAlgHom_apply] using h
end Nagata.W21
end
section
namespace Nagata.W21
open Nagata.W07 Nagata.W08
 theorem ccEV {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (aS τ 3 γ)) :
    Continuous (fun z : ℂˣ ↦ cEV b (z : ℂ)) := by
  apply continuous_pi
  intro i
  apply continuous_iff_continuousAt.mpr
  intro z
  exact ((b i).property.2.1 (z : ℂ) z.ne_zero).continuousAt.comp
    Units.continuous_val.continuousAt
theorem ccCM {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (aS τ 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sE1 τ 3 γ z)) = 2) :
    Continuous (cCM b hbase) := by
  have hc : Continuous (fun z : ℂˣ ↦
      (⟨cEV b (z : ℂ),
        cEVnz b (hbase z z.ne_zero)⟩ :
        {v : Fin 3 → ℂ // v ≠ 0})) :=
    (ccEV b).subtype_mk _
  exact (cpm ℂ (Fin 3 → ℂ)).comp hc
theorem ccTM (τ : ℂˣ) {γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (aS (τ : ℂ) 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sE1 τ 3 γ z)) = 2) :
    Continuous (cTM τ b hbase) :=
  (ccCM b hbase).quotient_lift _
end Nagata.W21
end
section
namespace Nagata.W21
open Nagata.W07 Nagata.W08 Nagata.W16
theorem cTMoc (τ : ℂˣ) {γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (aS (τ : ℂ) 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sE1 τ 3 γ z)) = 2)
    {d : ℕ} (G : NHF d)
    (hG : ∀ z : ℂ, z ≠ 0 → MvPolynomial.eval (cEV b z) G.polynomial = 0)
    (q : TP1 τ) : MvPolynomial.eval (cTM τ b hbase q).rep G.polynomial = 0 := by
  refine Quotient.inductionOn q ?_
  intro z
  change MvPolynomial.eval (Projectivization.mk ℂ (cEV b z)
    (cEVnz b (hbase z z.ne_zero))).rep G.polynomial = 0
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep ℂ (cEV b z)
    (cEVnz b (hbase z z.ne_zero))
  rw [← hu]
  change MvPolynomial.eval (fun i ↦ (u : ℂ) * cEV b z i) G.polynomial = 0
  rw [hes G.homogeneous, hG z z.ne_zero, mul_zero]
end Nagata.W21
end
section
noncomputable section
namespace Nagata.W21
open Nagata.W07 Nagata.W08 Nagata.W16
open scoped BigOperators
def sLP1 {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (aS τ 3 γ))
    (f : aS τ 3 γ) : MvPolynomial (Fin 3) ℂ :=
  ∑ i, MvPolynomial.C ((b.repr f) i) * MvPolynomial.X i
theorem sLPh {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (aS τ 3 γ))
    (f : aS τ 3 γ) : (sLP1 b f).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  exact MvPolynomial.isHomogeneous_C_mul_X _ _
theorem sLPe {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (aS τ 3 γ))
    (f : aS τ 3 γ) (z : ℂ) :
    MvPolynomial.eval (cEV b z) (sLP1 b f) = f.val z := by
  have he := congrArg (fun s : aS τ 3 γ ↦ s.val z) (b.sum_repr f)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at he
  simpa only [sLP1, map_sum, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, cEV] using he
theorem sLPnz {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (aS τ 3 γ))
    {f : aS τ 3 γ} (hf : f ≠ 0) : sLP1 b f ≠ 0 := by
  intro hL
  apply hf
  apply Subtype.ext
  funext z
  have he := sLPe b f z
  rw [hL, map_zero] at he
  exact he.symm
theorem sLPva (τ : ℂˣ) {γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (aS (τ : ℂ) 3 γ))
    (hbase : ∀ z : ℂ, z ≠ 0 →
      Module.finrank ℂ (LinearMap.ker (sE1 τ 3 γ z)) = 2)
    (f : aS (τ : ℂ) 3 γ) (z : ℂˣ) (hz : f.val z = 0) :
    MvPolynomial.eval (cCM b hbase z).rep (sLP1 b f) = 0 := by
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep ℂ (cEV b z)
    (cEVnz b (hbase z z.ne_zero))
  change MvPolynomial.eval (Projectivization.mk ℂ (cEV b z)
    (cEVnz b (hbase z z.ne_zero))).rep _ = 0
  rw [← hu]
  change MvPolynomial.eval (fun i ↦ (u : ℂ) * cEV b z i) _ = 0
  rw [hes (sLPh b f),
    sLPe, hz, mul_zero]
end Nagata.W21
end
end
section
noncomputable section
namespace Nagata.W21
open Nagata.W07 Nagata.W08 Nagata.W16
 theorem caCM {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {γ : ℂ} (hγ : γ ≠ 0) : Continuous (aCM hτ hτone hγ) :=
  ccTM _ _ _
end Nagata.W21
end
end
section
namespace Nagata.W21
open Nagata.W07 Nagata.W08 Nagata.W16
 theorem cgsi (G : MvPolynomial (Fin 3) ℂ)
    (hG : G.IsHomogeneous 3) (x : Fin 3 → ℂ) (u : ℂ) (hu : u ≠ 0) :
    (∃ i, MvPolynomial.eval (u • x) (MvPolynomial.pderiv i G) ≠ 0) ↔
      ∃ i, MvPolynomial.eval x (MvPolynomial.pderiv i G) ≠ 0 := by
  have he (i : Fin 3) :
      MvPolynomial.eval (u • x) (MvPolynomial.pderiv i G) =
        u ^ 2 * MvPolynomial.eval x (MvPolynomial.pderiv i G) := by
    exact hes (show (MvPolynomial.pderiv i G).IsHomogeneous 2 from hG.pderiv) x u
  simp only [he, ne_eq, mul_eq_zero, pow_eq_zero_iff (by decide : 2 ≠ 0), hu,
    false_or]
 theorem cgmri (G : MvPolynomial (Fin 3) ℂ)
    (hG : G.IsHomogeneous 3) (x : Fin 3 → ℂ) (hx : x ≠ 0) :
    (∃ i, MvPolynomial.eval (Projectivization.mk ℂ x hx).rep
      (MvPolynomial.pderiv i G) ≠ 0) ↔
      ∃ i, MvPolynomial.eval x (MvPolynomial.pderiv i G) ≠ 0 := by
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep ℂ x hx
  rw [← hu]
  exact cgsi G hG x (u : ℂ) u.ne_zero
 theorem aCMgi {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {γ : ℂ} (hγ : γ ≠ 0) (G : MvPolynomial (Fin 3) ℂ)
    (hG : G.IsHomogeneous 3) (z : ℂˣ) :
    (∃ i, MvPolynomial.eval
      (aCM hτ hτone hγ (tPM (cP1 hτ) z)).rep
      (MvPolynomial.pderiv i G) ≠ 0) ↔
      ∃ i, MvPolynomial.eval (cEV (aCB hτ hτone hγ) z)
        (MvPolynomial.pderiv i G) ≠ 0 :=
  cgmri G hG _ _
end Nagata.W21
end
section
noncomputable section
namespace Nagata.W21
open Nagata.W07 Nagata.W08 Nagata.PG
theorem etPLt {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    {γ : ℂ} (hγ : γ ≠ 0) (q : TP1 (cP1 hτ)) :
    ∃ (L : MvPolynomial (Fin 3) ℂ) (p : Fin 3 → PP),
      L ≠ 0 ∧ L.IsHomogeneous 1 ∧ Function.Injective p ∧
      p 0 = aCM hτ hτone hγ q ∧
      (∀ i, p i ∈ Set.range (aCM hτ hτone hγ)) ∧
      (∀ i, MvPolynomial.eval (p i).rep L = 0) ∧
      ∃ z : ℂ, z ≠ 0 ∧
        MvPolynomial.eval (cEV (aCB hτ hτone hγ) z) L ≠ 0 := by
  refine Quotient.inductionOn q ?_
  intro a
  obtain ⟨m, s, hm0, hm, hd, _, hs, _, hz, _⟩ :=
    ectsz1 hτ hτone hγ a.ne_zero
  let b := aCB hτ hτone hγ
  let u : Fin 3 → ℂˣ := fun i ↦ Units.mk0 (m i) (hm i)
  let p : Fin 3 → PP := fun i ↦ aCM hτ hτone hγ
    (tPM (cP1 hτ) (u i))
  refine ⟨sLP1 b s, p, sLPnz b hs,
    sLPh b s, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    by_contra hne
    have he := aCMi hτ hτone hγ hij
    obtain ⟨k, hk⟩ := (tPMei (cP1 hτ) (u j) (u i)).mp he.symm
    have hc := congrArg (fun v : ℂˣ ↦ (v : ℂ)) hk
    apply hd hne k
    simpa only [Units.val_mul, Units.val_zpow_eq_zpow_val, cPv,
      u, Units.val_mk0, mul_comm] using hc.symm
  · change aCM hτ hτone hγ (tPM (cP1 hτ) (u 0)) =
      aCM hτ hτone hγ (tPM (cP1 hτ) a)
    congr 2
    apply Units.ext
    exact hm0
  · intro i
    exact ⟨tPM (cP1 hτ) (u i), rfl⟩
  · intro i
    apply sLPva (cP1 hτ) b
      (fun _ hw ↦ aCekd hτ hτone hγ hw) s (u i)
    exact (hz (m i) (hm i)).mpr ⟨i, 0, by simp⟩
  · by_contra h
    apply hs
    apply aSe
    intro z hzne
    change s.val z = 0
    rw [← sLPe b s z]
    exact not_ne_iff.mp (fun hne ↦ h ⟨z, hzne, hne⟩)
end Nagata.W21
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W25
def pRI (s : Fin 3 → ℂ → ℂ) :
    Ideal (MvPolynomial (Fin 3) ℂ) :=
  ⨅ z : {z : ℂ // z ≠ 0}, RingHom.ker (MvPolynomial.eval (fun i => s i z.val))
@[simp] theorem mpRI (s : Fin 3 → ℂ → ℂ)
    (P : MvPolynomial (Fin 3) ℂ) :
    P ∈ pRI s ↔
      ∀ z : ℂ, z ≠ 0 → MvPolynomial.eval (fun i => s i z) P = 0 := by
  simp only [pRI, Ideal.mem_iInf, RingHom.mem_ker]
  exact ⟨fun h z hz => h ⟨z, hz⟩, fun h z => h z.val z.property⟩
theorem onmpR (s : Fin 3 → ℂ → ℂ) :
    (1 : MvPolynomial (Fin 3) ℂ) ∉ pRI s := by
  intro h
  have hz := (mpRI s 1).mp h 1 one_ne_zero
  simp at hz
theorem pRInt (s : Fin 3 → ℂ → ℂ) :
    pRI s ≠ ⊤ := by
  intro h
  exact onmpR s (h ▸ trivial)
end Nagata.Workers.W25
end
end
section
namespace Nagata.Workers.W25
theorem rgdi (s : Fin 3 → ℂ → ℂ)
    (G : MvPolynomial (Fin 3) ℂ)
    (hI : pRI s = Ideal.span ({G} : Set (MvPolynomial (Fin 3) ℂ)))
    (P : MvPolynomial (Fin 3) ℂ) :
    G ∣ P ↔ ∀ z : ℂ, z ≠ 0 → MvPolynomial.eval (fun i => s i z) P = 0 := by
  rw [← mpRI s P, hI, Ideal.mem_span_singleton]
theorem eenzo (s : Fin 3 → ℂ → ℂ)
    (G : MvPolynomial (Fin 3) ℂ)
    (hI : pRI s = Ideal.span ({G} : Set (MvPolynomial (Fin 3) ℂ)))
    (P : MvPolynomial (Fin 3) ℂ) (hP : ¬ G ∣ P) :
    ∃ z : ℂ, z ≠ 0 ∧ MvPolynomial.eval (fun i => s i z) P ≠ 0 := by
  classical
  by_contra h
  apply hP
  apply (rgdi s G hI P).mpr
  intro z hz
  by_contra he
  exact h ⟨z, hz, he⟩
end Nagata.Workers.W25
end
section
namespace Nagata.Workers.W25
theorem pRIiP (s : Fin 3 → ℂ → ℂ)
    (hs : ∀ i, DifferentiableOn ℂ (s i) {z : ℂ | z ≠ 0}) :
    (pRI s).IsPrime := by
  refine Ideal.isPrime_iff.mpr ⟨pRInt s, ?_⟩
  intro P Q hPQ
  simpa only [mpRI] using
    Nagata.W19.pepmz s hs P Q
      ((mpRI s (P * Q)).mp hPQ)
theorem cSRIi1 {τ γ : ℂ}
    (b : Fin 3 → Nagata.W08.aS τ 3 γ) :
    (pRI (fun i => (b i).val)).IsPrime :=
  pRIiP _
    (fun i z hz => ((b i).property.2.1 z hz).differentiableWithinAt)
theorem ecmrI {τ γ : ℂ}
    (b : Fin 3 → Nagata.W08.aS τ 3 γ)
    [Module.Finite ℂ (Nagata.W08.aS τ 9 (γ ^ 3))]
    (hdim : Module.finrank ℂ (Nagata.W08.aS τ 9 (γ ^ 3)) ≤ 9) :
    ∃ P : MvPolynomial (Fin 3) ℂ, P ≠ 0 ∧ P.IsHomogeneous 3 ∧
      P ∈ pRI (fun i => (b i).val) := by
  obtain ⟨P, hP, hhom, heval⟩ :=
    Nagata.W21.ecEod b hdim
  refine ⟨P, hP, hhom, (mpRI _ P).mpr ?_⟩
  intro z _
  exact heval z
end Nagata.Workers.W25
end
section
namespace Nagata.Workers.W25
theorem bplrt {τ γ : ℂ}
    (b : Module.Basis (Fin 3) ℂ (Nagata.W08.aS τ 3 γ))
    (i j : Fin 3) (hij : i ≠ j) (a c : ℂ)
    (hrel : MvPolynomial.C a * MvPolynomial.X i + MvPolynomial.C c * MvPolynomial.X j ∈
      pRI (fun k => (b k).val)) : a = 0 ∧ c = 0 := by
  have hsec : a • b i + c • b j = 0 := by
    apply Subtype.ext
    funext z
    by_cases hz : z = 0
    · subst z
      change a * (b i).val 0 + c * (b j).val 0 = 0
      rw [(b i).property.1, (b j).property.1, mul_zero, mul_zero, add_zero]
    · have heval := (mpRI _ _).mp hrel z hz
      change a * (b i).val z + c * (b j).val z = 0
      simpa only [map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X] using heval
  constructor
  · have h := congrArg (fun f => b.repr f i) hsec
    simpa [hij, Ne.symm hij] using h
  · have h := congrArg (fun f => b.repr f j) hsec
    simpa [hij, Ne.symm hij] using h
end Nagata.Workers.W25
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W17
theorem dAmPs
    {σ : Type*} {τ L : ℂ} {N : ℤ}
    (X : σ → Nagata.W08.aS τ N L)
    (T : MvPolynomial σ ℂ) (z : ℂ) (hz : z ≠ 0) :
    DifferentiableAt ℂ (fun w => MvPolynomial.eval (fun i => (X i).val w) T) z := by
  induction T using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ =>
      simp only [map_add]
      exact hP.add hQ
  | mul_X P i hP =>
      simp only [map_mul, MvPolynomial.eval_X]
      exact hP.mul ((X i).property.2.1 z hz)
theorem hsea
    {σ : Type*} {τ L : ℂ} {N : ℤ}
    (X : σ → Nagata.W08.aS τ N L)
    (T : MvPolynomial σ ℂ) (n : ℕ) (hT : T.IsHomogeneous n)
    (z : ℂ) (hz : z ≠ 0) :
    MvPolynomial.eval (fun i => (X i).val (τ*z)) T =
      L^n * z^(-(N*(n:ℤ))) * MvPolynomial.eval (fun i => (X i).val z) T := by
  have hcoord : (fun i => (X i).val (τ*z)) =
      fun i => (L*z^(-N)) * (X i).val z := by
    funext i
    exact (X i).property.2.2 z hz
  rw [hcoord, Nagata.W16.hes hT, mul_pow]
  have hp : (z^(-N))^n = z^(-(N*(n:ℤ))) := by
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  rw [hp]
theorem hemaS
    {σ : Type*} {τ L : ℂ} {N : ℤ} (hτ : τ ≠ 0)
    (X : σ → Nagata.W08.aS τ N L)
    (T : MvPolynomial σ ℂ) (n : ℕ) (hT : T.IsHomogeneous n) :
    Nagata.W08.nAZ (fun z => MvPolynomial.eval (fun i => (X i).val z) T) ∈
      Nagata.W08.aS τ (N*(n:ℤ)) (L^n) := by
  apply Nagata.W08.nAZma hτ
  · intro z hz
    exact dAmPs X T z hz
  · intro z hz
    exact hsea X T n hT z hz
end Nagata.Workers.W17
end
end
section
noncomputable section
namespace Nagata.Workers.W17
variable {σ : Type*}
def rC (X : σ → ℂ → ℂ) (T : MvPolynomial σ ℂ) : ℂ → ℂ :=
  Nagata.W08.nAZ (fun z => MvPolynomial.eval (fun i => X i z) T)
@[simp] theorem rCz (X : σ → ℂ → ℂ) :
    rC X 0 = 0 := by
  funext z
  simp [rC, Nagata.W08.nAZ]
def rNP (X : σ → ℂ → ℂ)
    (F : Polynomial (MvPolynomial σ ℂ)) : Polynomial (ℂ → ℂ) :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff
    (F.toFinsupp.coeff.mapRange (rC X) (rCz X)))
@[simp] theorem rNPc
    (X : σ → ℂ → ℂ) (F : Polynomial (MvPolynomial σ ℂ)) (j : ℕ) :
    (rNP X F).coeff j = rC X (F.coeff j) := rfl
theorem rNPb
    (X : σ → ℂ → ℂ) (F : Polynomial (MvPolynomial σ ℂ)) (N : ℕ)
    (hF : ∀ j, N < j → F.coeff j = 0) :
    ∀ j, N < j → (rNP X F).coeff j = 0 := by
  intro j hj
  simp only [rNPc, hF j hj, rCz]
def fE (z : ℂ) : (ℂ → ℂ) →+* ℂ where
  toFun f := f z
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
theorem rNPme
    (X : σ → ℂ → ℂ) (F : Polynomial (MvPolynomial σ ℂ)) (z : ℂ) (hz : z ≠ 0) :
    (rNP X F).map (fE z) =
      F.map (MvPolynomial.eval (fun i => X i z)) := by
  ext j
  simp only [Polynomial.coeff_map, rNPc]
  change Nagata.W08.nAZ (fun z => MvPolynomial.eval (fun i => X i z) (F.coeff j)) z = _
  exact Nagata.W08.nAZon _ hz
theorem rNPsE
    (X : σ → ℂ → ℂ) (F : Polynomial (MvPolynomial σ ℂ))
    (z w : ℂ) (hz : z ≠ 0) :
    Nagata.CS.sE (rNP X F) z w =
      (F.map (MvPolynomial.eval (fun i => X i z))).eval w := by
  have he : Nagata.CS.sE (rNP X F) z w =
      Polynomial.eval₂ (fE z) w (rNP X F) := by
    rw [Polynomial.eval₂_eq_sum]
    rfl
  rw [he, Polynomial.eval₂_eq_eval_map, rNPme X F z hz]
theorem rNPss
    {τ L : ℂ} (hτ : τ ≠ 0)
    (X : σ → Nagata.W08.aS τ 3 L)
    (F : Polynomial (MvPolynomial σ ℂ)) (d : ℕ)
    (hhom : ∀ j, (F.coeff j).IsHomogeneous (d-3*j))
    (hbound : ∀ j, d/3 < j → F.coeff j = 0) :
    ∀ j : ℕ, (rNP (fun i => (X i).val) F).coeff j ∈
      Nagata.W08.aS τ (3*((d:ℤ)-3*(j:ℤ))) (L^((d:ℤ)-3*(j:ℤ))) := by
  intro j
  by_cases hj : j ≤ d/3
  · have hle : 3*j ≤ d := by omega
    have he : ((d-3*j:ℕ):ℤ) = (d:ℤ)-3*(j:ℤ) := by omega
    rw [rNPc, ← he, zpow_natCast]
    exact hemaS hτ X (F.coeff j) (d-3*j) (hhom j)
  · rw [rNPc, hbound j (Nat.lt_of_not_ge hj), rCz]
    exact Submodule.zero_mem _
end Nagata.Workers.W17
end
end
section
noncomputable section
namespace Nagata.Workers.W17
open scoped BigOperators
theorem edCH (c : Fin 3) (T : MvPolynomial (Fin 3) ℂ)
    (v : Fin 2 → ℂ) :
    MvPolynomial.eval v (Nagata.W27.dCH c T) =
      MvPolynomial.eval (Fin.insertNth (α := fun _ : Fin 3 => ℂ) c 1 v) T := by
  have he : (MvPolynomial.eval v).comp (Nagata.W27.dCH c) =
      MvPolynomial.eval (Fin.insertNth (α := fun _ : Fin 3 => ℂ) c 1 v) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [Nagata.W27.dCH]
    · intro a
      by_cases ha : a = c
      · subst a
        simp [Nagata.W27.dCH]
      · obtain ⟨b,rfl⟩ := Fin.exists_succAbove_eq ha
        simp [Nagata.W27.dCH]
  exact RingHom.congr_fun he T
theorem scv (c : Fin 3) (x : Fin 3 → ℂ) (hx : x c ≠ 0) :
    (x c) • Fin.insertNth (α := fun _ : Fin 3 => ℂ) c 1 (fun b => x (c.succAbove b) / x c) = x := by
  funext a
  by_cases ha : a = c
  · subst a
    simp
  · obtain ⟨b,rfl⟩ := Fin.exists_succAbove_eq ha
    simp [smul_eq_mul, mul_div_cancel₀ _ hx]
theorem npfi
    (I : Finset ℕ) (j : ℕ → ℕ) (T : ℕ → MvPolynomial (Fin 3) ℂ)
    (d k : ℕ) (hhom : ∀ α ∈ I, (T α).IsHomogeneous (d-k*j α))
    (hbound : ∀ α ∈ I, k*j α ≤ d)
    (c : Fin 3) (x : Fin 3 → ℂ) (hx : x c ≠ 0) (w : ℂ) :
    (∑ α ∈ I, w^j α * MvPolynomial.eval x (T α)) =
      (x c)^d * ∑ α ∈ I, (w/(x c)^k)^j α *
        MvPolynomial.eval (fun b => x (c.succAbove b)/x c)
          (Nagata.W27.dCH c (T α)) := by
  have he := Nagata.W16.AB.wEs I T j d k hhom hbound
    (Fin.insertNth (α := fun _ : Fin 3 => ℂ) c 1 (fun b => x (c.succAbove b)/x c)) (w/(x c)^k) (x c)
  rw [scv c x hx, mul_div_cancel₀ w (pow_ne_zero k hx)] at he
  simpa only [Nagata.W16.AB.wE, edCH,
    mul_comm] using he
end Nagata.Workers.W17
end
end
section
namespace Nagata.Workers.W17
theorem rNPnz
    (X : Fin 3 → ℂ → ℂ) (G : MvPolynomial (Fin 3) ℂ)
    (hrelations : Nagata.Workers.W25.pRI X = Ideal.span ({G} : Set _))
    (F : Polynomial (MvPolynomial (Fin 3) ℂ))
    (hF : F.map (Ideal.Quotient.mk (Ideal.span ({G} : Set (MvPolynomial (Fin 3) ℂ)))) ≠ 0) :
    rNP X F ≠ 0 := by
  intro hz
  apply hF
  ext j
  rw [Polynomial.coeff_map, Polynomial.coeff_zero]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [← hrelations, Nagata.Workers.W25.mpRI]
  intro z hz0
  have hc := congrArg (fun P : Polynomial (ℂ → ℂ) => P.coeff j z) hz
  simpa only [rNPc, rC,
    Nagata.W08.nAZon _ hz0, Polynomial.coeff_zero, Pi.zero_apply] using hc
end Nagata.Workers.W17
end
section
noncomputable section
namespace Nagata.Workers.W17
open Nagata.Workers.W28
def aS1 : MvPolynomial (Fin 2) ℂ ≃+* MvPolynomial (Fin 2) ℂ :=
  (MvPolynomial.renameEquiv ℂ (Equiv.swap (0 : Fin 2) 1)).toRingEquiv
theorem eaS (P : MvPolynomial (Fin 2) ℂ) (p : CP) :
    pPE (aS1 P) p = pPE P p.swap := by
  change MvPolynomial.eval (fun i : Fin 2 => if i = 0 then p.1 else p.2)
    (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) P) = _
  rw [MvPolynomial.eval_rename]
  apply congrArg (fun v : Fin 2 → ℂ => MvPolynomial.eval v P)
  funext i
  fin_cases i <;> simp
theorem oaSi (P : MvPolynomial (Fin 2) ℂ) (p : CP) (m : ℕ) :
    Nagata.AM.oAL
      (fun i : Fin 2 => if i = 0 then p.2 else p.1) m (aS1 P) ↔
    Nagata.AM.oAL
      (fun i : Fin 2 => if i = 0 then p.1 else p.2) m P := by
  apply Nagata.AM.oALei _ _ aS1
  intro Q
  exact eaS Q p.swap
theorem aSfPF
    (I : Finset ℕ) (j : ℕ → ℕ) (R : ℕ → MvPolynomial (Fin 2) ℂ)
    (G : MvPolynomial (Fin 2) ℂ) (s : ℂ) :
    aS1 (fPF I j R G s) =
      fPF I j (fun α => aS1 (R α)) (aS1 G) s := by
  simp [fPF, aS1, map_sum, map_mul, map_pow]
theorem pYaS (G : MvPolynomial (Fin 2) ℂ) (p : CP) :
    pPE (MvPolynomial.pderiv 1 (aS1 G)) p.swap =
      pPE (MvPolynomial.pderiv 0 G) p := by
  have hd := MvPolynomial.pderiv_rename (Equiv.swap (0 : Fin 2) 1).injective (0 : Fin 2) G
  have hd' : MvPolynomial.pderiv 1 (aS1 G) = aS1 (MvPolynomial.pderiv 0 G) := by
    simpa [aS1] using hd
  rw [hd', eaS]
  rfl
theorem pXaS (G : MvPolynomial (Fin 2) ℂ) (p : CP) :
    pPE (MvPolynomial.pderiv 0 (aS1 G)) p.swap =
      pPE (MvPolynomial.pderiv 1 G) p := by
  have hd := MvPolynomial.pderiv_rename (Equiv.swap (0 : Fin 2) 1).injective (1 : Fin 2) G
  have hd' : MvPolynomial.pderiv 0 (aS1 G) = aS1 (MvPolynomial.pderiv 1 G) := by
    simpa [aS1] using hd
  rw [hd', eaS]
  rfl
theorem pGaS (G : MvPolynomial (Fin 2) ℂ) (p V : CP) :
    pG (aS1 G) p.swap V.swap = pG G p V := by
  change pPE (MvPolynomial.pderiv 0 (aS1 G)) p.swap * V.2 +
      pPE (MvPolynomial.pderiv 1 (aS1 G)) p.swap * V.1 =
    pPE (MvPolynomial.pderiv 0 G) p * V.1 +
      pPE (MvPolynomial.pderiv 1 G) p * V.2
  rw [pXaS, pYaS, add_comm]
end Nagata.Workers.W17
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.CS
open Nagata.Workers.W28
noncomputable def lP {q : ℕ} (z₀ : ℂ) (ξ : Fin q → ℂ) : Fin q → ℂ × ℂ :=
  fun i => (z₀ * Complex.exp (ξ i), 1)
theorem lSooc {τ γL γP : ℂ} {d : ℤ} {m : ℕ} {P : ℂ → ℂ}
    (F : Nagata.W20.AS τ γL γP d m P) (z₀ ξ : ℂ)
    (horder : HAOAL (𝕜 := ℂ)
      (fun y : ℂ × ℂ => sE F.val y.1 y.2) (z₀ * Complex.exp ξ, 1) m) :
    HAOAL (𝕜 := ℂ)
      (fun y : ℂ × ℂ => Nagata.W20.lS1 F z₀ y.1 y.2) (ξ, 0) m := by
  have hmap : AnalyticAt ℂ
      (fun y : ℂ × ℂ => (z₀ * Complex.exp y.1, Complex.exp y.2)) (ξ, 0) := by
    have hf := (ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt (ξ, 0)
    have hs := (ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt (ξ, 0)
    exact (analyticAt_const.mul hf.cexp').prod hs.cexp'
  have hp : HAOAL (𝕜 := ℂ)
      (fun y : ℂ × ℂ => sE F.val y.1 y.2)
      (z₀ * Complex.exp ξ, Complex.exp 0) m := by
    simpa only [Complex.exp_zero] using horder
  exact hp.comp (f := fun y : ℂ × ℂ => (z₀ * Complex.exp y.1, Complex.exp y.2)) hmap
end Nagata.CS
end
section
namespace Nagata.CS
open Nagata.Workers.W17 Nagata.Workers.W28 Filter Topology
noncomputable def aNS1 {σ : Type*} (X : σ → ℂ → ℂ)
    (F : Polynomial (MvPolynomial σ ℂ)) (y : ℂ × ℂ) : ℂ :=
  (F.map (MvPolynomial.eval (fun i => X i y.1))).eval y.2
theorem rNPoi {σ : Type*} (X : σ → ℂ → ℂ)
    (F : Polynomial (MvPolynomial σ ℂ)) (x : ℂ × ℂ) (hx : x.1 ≠ 0) (m : ℕ) :
    HAOAL (𝕜 := ℂ)
      (fun y : ℂ × ℂ => sE (rNP X F) y.1 y.2) x m ↔
      HAOAL (𝕜 := ℂ) (aNS1 X F) x m := by
  have he : (fun y : ℂ × ℂ => sE (rNP X F) y.1 y.2)
      =ᶠ[𝓝 x] aNS1 X F := by
    filter_upwards [continuousAt_fst.eventually_ne hx] with y hy
    exact rNPsE X F y.1 y.2 hy
  exact ⟨fun h => h.congr he, fun h => h.congr he.symm⟩
end Nagata.CS
end
section
namespace Nagata.CS
open Filter Topology
theorem aop {τ γ : ℂ} {n : ℤ}
    (hτ : τ ≠ 0) (hγ : γ ≠ 0)
    (f : Nagata.W08.aS τ n γ) {z : ℂ} (hz : z ≠ 0) :
    analyticOrderAt f.val (τ * z) = analyticOrderAt f.val z := by
  have hscale : AnalyticAt ℂ (fun w : ℂ => τ * w) z := by fun_prop
  have hd : deriv (fun w : ℂ => τ * w) z ≠ 0 := by
    have he : deriv (fun w : ℂ => τ * w) z = τ := by
       simp
    rw [he]
    exact hτ
  have hu : AnalyticAt ℂ (fun w : ℂ => γ * w ^ (-n)) z :=
    analyticAt_const.mul (analyticAt_id.zpow hz)
  have hu0 : γ * z ^ (-n) ≠ 0 := mul_ne_zero hγ (zpow_ne_zero _ hz)
  have he : (f.val ∘ fun w : ℂ => τ * w) =ᶠ[𝓝 z]
      (fun w : ℂ => γ * w ^ (-n)) * f.val := by
    filter_upwards [isOpen_ne_fun continuous_id continuous_const |>.mem_nhds hz] with w hw
    exact f.property.2.2 w hw
  rw [← analyticOrderAt_comp_of_deriv_ne_zero hscale hd, analyticOrderAt_congr he,
    analyticOrderAt_mul hu (Nagata.W08.aSaA f hz),
    hu.analyticOrderAt_eq_zero.mpr hu0, zero_add]
theorem aoo {τ γ : ℂ} {n : ℤ}
    (hτ : τ ≠ 0) (hγ : γ ≠ 0)
    (f : Nagata.W08.aS τ n γ) {a : ℂ} (ha : a ≠ 0) (k : ℤ) :
    analyticOrderAt f.val (a * τ ^ k) = analyticOrderAt f.val a := by
  have hstep (l : ℤ) : analyticOrderAt f.val (a * τ ^ (l + 1)) =
      analyticOrderAt f.val (a * τ ^ l) := by
    rw [zpow_add₀ hτ]
    simpa only [zpow_one, mul_assoc, mul_left_comm, mul_comm] using
      aop hτ hγ f (mul_ne_zero ha (zpow_ne_zero _ hτ))
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih => exact (hstep k).trans ih
  | pred k ih =>
      have hs := hstep (-(k : ℤ) - 1)
      convert hs.symm.trans (by simpa using ih) using 1
end Nagata.CS
end
section
namespace Nagata.CS
open scoped BigOperators
theorem rMM {τ : ℝ} (hτ : 0 < τ) (ξ : Fin 9 → ℝ) :
    (∏ i, -((τ ^ ξ i : ℝ) : ℂ)) =
      -Nagata.Workers.W10.tP1 τ (∑ i, ξ i) := by
  rw [Finset.prod_neg]
  norm_num
  rw [Nagata.Workers.W10.tP1, Real.rpow_sum_of_pos hτ, Complex.ofReal_prod]
end Nagata.CS
end
end OAI
end
section
namespace OAI
section
noncomputable section
open Module Filter Topology
namespace Nagata.Workers.W12
open Nagata.Workers.W10 Nagata.W20 Nagata.Workers.W11 Nagata.FE Nagata.W22
variable (τ : ℝ) (γL γP : ℂ) (d : ℤ) (m : ℕ) (a delta : ℝ)
  (marks : Fin 9 → ℝ) (P : ℂ → ℂ) (z0 : ℂ)
  (hd : 3 * (m : ℤ) < d)
  (hP : AnalyticOnNhd ℂ P {z | z ≠ 0})
  (hPfin : ∀ z ≠ 0, analyticOrderAt P z ≠ ⊤)
  (b : ∀ j : Fin ((d / 3).toNat + 1),
    Basis (CF d (m : ℤ) a delta (j.val : ℤ)) ℂ
      (sB (τ : ℂ) γL γP d (m : ℤ) (j.val : ℤ)))
  (hblock : ∀ (j : Fin ((d / 3).toNat + 1))
      (K : CF d (m : ℤ) a delta (j.val : ℤ)) (x : ℂ),
    (b j K).val (z0 * Complex.exp x) =
      if (j.val : ℤ) ≤ (m : ℤ) then
        nTS1 (cD d (m : ℤ) : ℝ)
          ((K.val : ℝ) - fL d (m : ℤ) (j.val : ℤ) a delta)
          (K.val : ℝ) ((-1 : ℂ) ^ ((m : ℤ) - (j.val : ℤ))) τ x
      else if 0 < d - 3 * (j.val : ℤ) then
        nTS1 (sD d (j.val : ℤ) : ℝ)
          ((K.val : ℝ) - sL d (j.val : ℤ) a delta) (K.val : ℝ) 1 τ x
      else 1)
  (hPi : ∀ x : ℂ, P (z0 * Complex.exp x) = mP1 marks τ x)
include hblock hPi
end Nagata.Workers.W12
end
end
section
noncomputable section
open Module Filter Topology
open scoped BigOperators
namespace Nagata.Workers.W12
open Nagata.Workers.W10 Nagata.W20 Nagata.Workers.W11 Nagata.FE
open Nagata.W22 Nagata.CS
variable {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
  (ξ : Fin 9 → ℝ) (a delta x0 : ℝ) (d : ℤ) (m : ℕ)
  (hs : (∑ i, ξ i) = 9 * x0 - delta)
  (hd : 3 * (m : ℤ) < d)
  (hfirst : ∀ j : ℤ, 0 ≤ j → j ≤ (m : ℤ) →
    fL d (m : ℤ) j a delta ∉ Set.range (Int.cast : ℤ → ℝ))
  (hsecond : ∀ j : ℤ, (m : ℤ) < j → j ≤ d / 3 → 0 < d - 3 * j →
    sL d j a delta ∉ Set.range (Int.cast : ℤ → ℝ))
def gSS :=
  AS (τ : ℂ) (tP1 τ (((∑ i, ξ i) + a) / 3))
    (-tP1 τ (∑ i, ξ i)) d m (rMS hτ hτone ξ).val
include hs hd hfirst hsecond
end Nagata.Workers.W12
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W06.TC
open Nagata.Workers.W05
open Nagata.W21
open scoped BigOperators
def mP1 (τ : ℝ) (xi : Fin 9 → ℝ) (z : ℂ) : ℂ :=
  mTP (τ : ℂ) (fun i => (rP τ (xi i) : ℂ)) z
theorem cPnlo {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) : ‖(τ : ℂ)‖ < 1 := by
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ] using hτ1
theorem mPnzo {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    (xi : Fin 9 → ℝ) (z : ℂˣ)
    (havoid : ∀ i, tPM (pP τ hτ) z ≠
      tPM (pP τ hτ) (rP τ (xi i))) :
    mP1 τ xi (z : ℂ) ≠ 0 := by
  intro hz
  obtain ⟨i, k, hk⟩ := (mTPez (cPnlo hτ hτ1)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt hτ))
    (fun i : Fin 9 => (rP τ (xi i)).ne_zero) z.ne_zero).mp hz
  apply havoid i
  apply Eq.symm
  apply Quotient.sound
  apply (tOSic (pP τ hτ) (rP τ (xi i)) z).mpr
  exact ⟨k, by simpa only [pP, Units.val_mk0, mul_comm] using hk⟩
theorem mafot {τ : ℝ} (hτ : 0 < τ)
    (x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ)
    (hinj : Function.Injective (tT τ hτ x0 xi ξ)) (i : Fin 9) (j : Fin q) :
    tC τ hτ x0 (ξ j) ≠ tPM (pP τ hτ) (rP τ (xi i)) := by
  intro h
  have hi : (finSumFinEquiv : Fin 9 ⊕ Fin q ≃ Fin (9 + q)) (Sum.inr j) =
      finSumFinEquiv (Sum.inl i) := by
    apply hinj
    rw [tTr, tTl]
    exact h
  have hs := (finSumFinEquiv : Fin 9 ⊕ Fin q ≃ Fin (9 + q)).injective hi
  cases hs
theorem mPnzm {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    (x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ)
    (hinj : Function.Injective (tT τ hτ x0 xi ξ)) (j : Fin q) :
    mP1 τ xi (cP2 τ x0 (ξ j) : ℂ) ≠ 0 :=
  mPnzo hτ hτ1 xi (cP2 τ x0 (ξ j))
    (fun i => mafot hτ x0 xi ξ hinj i j)
end Nagata.W06.TC
end
end
section
noncomputable section
namespace Nagata.W06.TC
open Nagata.Workers.W05 Nagata.W21
theorem edffp {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    (xi : Fin 9 → ℝ) (hxi : Function.Injective xi)
    (hxi_bounds : ∀ i, 0 < xi i ∧ xi i < 1 / 2) :
    ∃ R : ℝ, 0 < R ∧ ∀ (q : ℕ) (ξ : Fin q → ℂ),
      Function.Injective ξ → (∀ j, ‖ξ j‖ < R) →
      Function.Injective (tT τ hτ (1 / 2) xi ξ) ∧
        ∀ j, mP1 τ xi (cP2 τ (1 / 2) (ξ j) : ℂ) ≠ 0 := by
  have hlogpos : 0 < |Real.log τ| := abs_pos.mpr (ne_of_lt (Real.log_neg hτ hτ1))
  have hgap : 0 < mG (1 / 2) xi := by
    apply mGp
    intro i
    have h := hxi_bounds i
    constructor <;> linarith
  let R := min (Real.pi / 4) (min (|Real.log τ| / 4)
    (mG (1 / 2) xi * |Real.log τ| / 2))
  have hR : 0 < R := lt_min (div_pos Real.pi_pos (by norm_num))
    (lt_min (div_pos hlogpos (by norm_num))
      (div_pos (mul_pos hgap hlogpos) (by norm_num)))
  have hRpi : R < Real.pi / 2 :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith [Real.pi_pos])
  have hRlog : R ≤ |Real.log τ| / 4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hRgap : R ≤ mG (1 / 2) xi * |Real.log τ| / 2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨R, hR, ?_⟩
  intro q ξ hξ hξR
  have hinj := tTi hτ hτ1 xi hxi hxi_bounds hR hRpi
    (by linarith) (by nlinarith [mul_pos hgap hlogpos]) ξ hξ hξR
  exact ⟨hinj, fun j => mPnzm hτ hτ1 (1 / 2) xi ξ hinj j⟩
end Nagata.W06.TC
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.Workers.W17
variable {K σ : Type*} [CommRing K] [IsDomain K]
noncomputable local instance oaiLocInst8 {σ R : Type*} [CommSemiring R] : GradedAlgebra (MvPolynomial.homogeneousSubmodule σ R) := MvPolynomial.gradedAlgebra
theorem hfd1 {P Q : MvPolynomial σ K} {k d : Nat}
    (hP : P.IsHomogeneous k) (hPQ : (P * Q).IsHomogeneous d)
    (hne : P * Q ≠ 0) :
    k ≤ d ∧ Q.IsHomogeneous (d - k) := by
  let H := MvPolynomial.homogeneousSubmodule σ K
  have hsame : (DirectSum.decompose H (P * Q) d : MvPolynomial σ K) = P * Q :=
    DirectSum.decompose_of_mem_same H hPQ
  have hkd : k ≤ d := by
    by_contra hk
    have hzero : (DirectSum.decompose H (P * Q) d : MvPolynomial σ K) = 0 :=
      DirectSum.coe_decompose_mul_of_left_mem_of_not_le H hP hk
    exact hne (hsame.symm.trans hzero)
  have hpart : (DirectSum.decompose H (P * Q) d : MvPolynomial σ K) =
      P * (DirectSum.decompose H Q (d - k) : MvPolynomial σ K) :=
    DirectSum.coe_decompose_mul_of_left_mem_of_le H hP hkd
  have hQ : Q = (DirectSum.decompose H Q (d - k) : MvPolynomial σ K) :=
    mul_left_cancel₀ (left_ne_zero_of_mul hne) (hsame.symm.trans hpart)
  refine ⟨hkd, ?_⟩
  change Q ∈ H (d - k)
  rw [hQ]
  exact (DirectSum.decompose H Q (d - k)).property
theorem hpr {S G T : MvPolynomial σ K} {d k j : Nat}
    (hS : S.IsHomogeneous d) (hG : G.IsHomogeneous k)
    (hne : S ≠ 0) (hfactor : S = G ^ j * T) :
    k * j ≤ d ∧ T.IsHomogeneous (d - k * j) := by
  apply hfd1 (hG.pow j)
  · rwa [← hfactor]
  · rwa [← hfactor]
theorem hpeb {S G T : MvPolynomial σ K} {d k j : Nat}
    (hS : S.IsHomogeneous d) (hG : G.IsHomogeneous k)
    (hne : S ≠ 0) (hfactor : S = G ^ j * T) (hk : 0 < k) :
    j ≤ d / k := by
  apply (Nat.le_div_iff_mul_le hk).mpr
  simpa [Nat.mul_comm] using (hpr hS hG hne hfactor).1
end Nagata.Workers.W17
end
section
namespace Nagata.Workers.W17
theorem phniU {K σ : Type*} [CommRing K] [Nontrivial K]
    {G : MvPolynomial σ K} {k : ℕ} (hG : G.IsHomogeneous k) (hk : 0 < k) :
    ¬IsUnit G := by
  have hzero : MvPolynomial.eval (0 : σ → K) G = 0 := by
    rw [MvPolynomial.eval_zero]
    exact hG.coeff_eq_zero (by simpa using Nat.ne_of_lt hk)
  intro hu
  have hi := hu.map (MvPolynomial.eval (0 : σ → K))
  rw [hzero] at hi
  exact not_isUnit_zero hi
end Nagata.Workers.W17
end
section
namespace Nagata.Workers.W17
open scoped BigOperators
variable {A : Type*} [CommRing A] [WfDvdMonoid A]
theorem efc (S : Polynomial A) (G : A)
    (hG : ¬IsUnit G) :
    ∃ (j : Nat → Nat) (T : Nat → A),
      (∀ α, S.coeff α = G ^ j α * T α) ∧
      (∀ α, S.coeff α ≠ 0 → ¬G ∣ T α) := by
  classical
  have hfactor : ∀ α : Nat, ∃ n : Nat, ∃ t : A,
      S.coeff α = G ^ n * t ∧ (S.coeff α ≠ 0 → ¬G ∣ t) := by
    intro α
    by_cases hα : S.coeff α = 0
    · exact ⟨0, 0, by simp [hα], fun hn => (hn hα).elim⟩
    · obtain ⟨n, t, hnot, heq⟩ := WfDvdMonoid.max_power_factor' hα hG
      exact ⟨n, t, heq, fun _ => hnot⟩
  choose j T hfac hnot using hfactor
  exact ⟨j, T, hfac, hnot⟩
theorem enni
    (S : Polynomial A) (G : A) (hS : S ≠ 0) (hG : ¬IsUnit G) :
    ∃ (j : Nat → Nat) (T : Nat → A) (u : Nat),
      (∀ α, S.coeff α = G ^ j α * T α) ∧
      (∀ α ∈ S.support, ¬G ∣ T α) ∧
      (∀ α ∈ S.support, u ≤ α + j α) ∧
      (S.support.filter (fun α => α + j α = u)).Nonempty ∧
      (∑ α ∈ S.support.filter (fun α => α + j α = u),
        Polynomial.monomial (j α)
          (Ideal.Quotient.mk (Ideal.span ({G} : Set A)) (T α))) ≠ 0 := by
  classical
  obtain ⟨j, T, hfactor, hnot⟩ := efc S G hG
  have hnonzero : ∀ α ∈ S.support,
      Ideal.Quotient.mk (Ideal.span ({G} : Set A)) (T α) ≠ 0 := by
    intro α hα hz
    exact hnot α (Polynomial.mem_support_iff.mp hα)
      ((Ideal.Quotient.eq_zero_iff_dvd G (T α)).mp hz)
  obtain ⟨u, hmin, hselected, hinitial⟩ :=
    Nagata.W18.elwp S.support j
      (fun α => Ideal.Quotient.mk (Ideal.span ({G} : Set A)) (T α))
      (Polynomial.support_nonempty.mpr hS) hnonzero
  exact ⟨j, T, u, hfactor, fun α hα => hnot α (Polynomial.mem_support_iff.mp hα),
    hmin, hselected, hinitial⟩
omit [WfDvdMonoid A] in
theorem iwbfc (S : Polynomial A)
    (j : Nat → Nat) (u : Nat) (hzero : S.coeff 0 ≠ 0)
    (hmin : ∀ α ∈ S.support, u ≤ α + j α) : u ≤ j 0 := by
  simpa using hmin 0 (Polynomial.mem_support_iff.mpr hzero)
end Nagata.Workers.W17
end
section
namespace Nagata.Workers.W17
open scoped BigOperators
variable {A : Type*} [CommRing A]
noncomputable def lNP
    (indices : Finset Nat) (j : Nat → Nat) (T : Nat → A) : Polynomial A :=
  ∑ α ∈ indices, Polynomial.monomial (j α) (T α)
theorem clNP
    (indices : Finset Nat) (j : Nat → Nat) (T : Nat → A) (n : Nat) :
    (lNP indices j T).coeff n =
      ∑ α ∈ indices.filter (fun α => j α = n), T α := by
  classical
  simp only [lNP, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial, Finset.sum_filter]
theorem mlNP {B : Type*} [CommRing B]
    (indices : Finset Nat) (j : Nat → Nat) (T : Nat → A) (f : A →+* B) :
    (lNP indices j T).map f =
      ∑ α ∈ indices, Polynomial.monomial (j α) (f (T α)) := by
  simp only [lNP, Polynomial.map_sum, Polynomial.map_monomial]
theorem clNPe
    (indices : Finset Nat) (j : Nat → Nat) (T : Nat → A) (bound n : Nat)
    (hbound : ∀ α ∈ indices, j α ≤ bound) (hn : bound < n) :
    (lNP indices j T).coeff n = 0 := by
  classical
  have hempty : indices.filter (fun α => j α = n) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro α hα heq
    have hle : n ≤ bound := heq ▸ hbound α hα
    exact (Nat.not_lt_of_ge hle) hn
  rw [clNP, hempty, Finset.sum_empty]
end Nagata.Workers.W17
end
section
namespace Nagata.Workers.W17
open scoped BigOperators
open Nagata.W27
variable {K : Type*} [CommRing K]
noncomputable def iPF (d : Nat)
    (q : HM d → Polynomial K) : Polynomial (MvPolynomial (Fin 3) K) :=
  ∑ ν : HM d, (q ν).map MvPolynomial.C *
    Polynomial.C (MvPolynomial.monomial ν.val (1 : K))
theorem ciPF (d : Nat)
    (q : HM d → Polynomial K) (α : Nat) :
    (iPF d q).coeff α =
      ∑ ν : HM d, MvPolynomial.monomial ν.val ((q ν).coeff α) := by
  classical
  unfold iPF
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro ν hν
  rw [Polynomial.coeff_mul_C, Polynomial.coeff_map, MvPolynomial.C_mul_monomial, mul_one]
theorem mciPF (d : Nat)
    (q : HM d → Polynomial K) (α : Nat) (ν : HM d) :
    ((iPF d q).coeff α).coeff ν.val = (q ν).coeff α := by
  classical
  rw [ciPF, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single ν]
  · simp
  · intro b hb hne
    simp only [ite_eq_right_iff]
    intro he
    exact (hne (Subtype.ext he)).elim
  · simp
theorem iPFh (d : Nat)
    (q : HM d → Polynomial K) (α : Nat) :
    ((iPF d q).coeff α).IsHomogeneous d := by
  rw [ciPF]
  apply MvPolynomial.IsHomogeneous.sum
  intro ν hν
  exact MvPolynomial.isHomogeneous_monomial _ ν.property
theorem iPFcn (d : Nat)
    (q : HM d → Polynomial K)
    (hq : ∃ ν, (q ν).coeff 0 ≠ 0) :
    (iPF d q).coeff 0 ≠ 0 := by
  obtain ⟨ν, hν⟩ := hq
  intro hz
  have h := mciPF d q 0 ν
  rw [hz, MvPolynomial.coeff_zero] at h
  exact hν h.symm
theorem eiPF (d : Nat)
    (q : HM d → Polynomial K) (s : K) :
    (iPF d q).eval (MvPolynomial.C s) =
      ∑ ν : HM d, MvPolynomial.monomial ν.val ((q ν).eval s) := by
  classical
  unfold iPF
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro ν hν
  rw [Polynomial.eval_mul, Polynomial.eval_map_apply, Polynomial.eval_C,
    MvPolynomial.C_mul_monomial, mul_one]
theorem eiPFe (d : Nat)
    (q : HM d → Polynomial K) (s : K) :
    (iPF d q).eval (MvPolynomial.C s) =
      ((hC1 d).symm (fun ν => (q ν).eval s)).val := by
  classical
  rw [eiPF]
  let F : MvPolynomial.homogeneousSubmodule (Fin 3) K d :=
    ⟨∑ ν : HM d, MvPolynomial.monomial ν.val ((q ν).eval s),
      MvPolynomial.IsHomogeneous.sum _ _ _
        (fun ν _ => MvPolynomial.isHomogeneous_monomial _ ν.property)⟩
  have hcoord : hC1 d F = fun ν => (q ν).eval s := by
    funext ν
    change F.val.coeff ν.val = (q ν).eval s
    dsimp only [F]
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    rw [Finset.sum_eq_single ν]
    · simp
    · intro b hb hne
      simp only [ite_eq_right_iff]
      intro he
      exact (hne (Subtype.ext he)).elim
    · simp
  have hF : F = (hC1 d).symm (fun ν => (q ν).eval s) := by
    apply (hC1 d).injective
    rw [LinearEquiv.apply_symm_apply]
    exact hcoord
  exact congrArg Subtype.val hF
end Nagata.Workers.W17
end
section
namespace Nagata.Workers.W17
open scoped BigOperators
variable {K : Type*} [Field K]
theorem edbpi
    (S : Polynomial (MvPolynomial (Fin 3) K))
    (G : MvPolynomial (Fin 3) K) (d k : Nat)
    (hcoeff : ∀ α, (S.coeff α).IsHomogeneous d)
    (hG : G.IsHomogeneous k) (hunit : ¬IsUnit G) (hk : 0 < k)
    (hzero : S.coeff 0 ≠ 0) :
    ∃ (j : Nat → Nat) (T : Nat → MvPolynomial (Fin 3) K) (u : Nat),
      (∀ α, S.coeff α = G ^ j α * T α) ∧
      (∀ α ∈ S.support, ¬G ∣ T α) ∧
      (∀ α ∈ S.support, j α ≤ d / k ∧ (T α).IsHomogeneous (d - k * j α)) ∧
      (∀ α ∈ S.support, u ≤ α + j α) ∧
      u ≤ d / k ∧
      (S.support.filter (fun α => α + j α = u)).Nonempty ∧
      (∑ α ∈ S.support.filter (fun α => α + j α = u),
        Polynomial.monomial (j α)
          (Ideal.Quotient.mk
            (Ideal.span ({G} : Set (MvPolynomial (Fin 3) K))) (T α))) ≠ 0 := by
  classical
  have hS : S ≠ 0 := by
    intro hS
    apply hzero
    rw [hS, Polynomial.coeff_zero]
  obtain ⟨j, T, u, hfactor, hnot, hmin, hselected, hinitial⟩ :=
    enni S G hS hunit
  have hdegree : ∀ α ∈ S.support,
      j α ≤ d / k ∧ (T α).IsHomogeneous (d - k * j α) := by
    intro α hα
    have hn : S.coeff α ≠ 0 := Polynomial.mem_support_iff.mp hα
    exact ⟨hpeb (hcoeff α) hG hn (hfactor α) hk,
      (hpr (hcoeff α) hG hn (hfactor α)).2⟩
  have hu : u ≤ d / k :=
    (iwbfc S j u hzero hmin).trans
      (hdegree 0 (Polynomial.mem_support_iff.mpr hzero)).1
  exact ⟨j, T, u, hfactor, hnot, hdegree, hmin, hu, hselected, hinitial⟩
end Nagata.Workers.W17
end
section
namespace Nagata.Workers.W17
variable {K σ : Type*} [CommRing K]
theorem hclNP
    (indices : Finset Nat) (j : Nat → Nat) (T : Nat → MvPolynomial σ K)
    (d k : Nat) (hT : ∀ α ∈ indices, (T α).IsHomogeneous (d - k * j α))
    (n : Nat) :
    ((lNP indices j T).coeff n).IsHomogeneous (d - k * n) := by
  rw [clNP]
  apply MvPolynomial.IsHomogeneous.sum
  intro α hα
  have hmem := (Finset.mem_filter.mp hα).1
  have heq := (Finset.mem_filter.mp hα).2
  simpa only [heq] using hT α hmem
theorem nclNP
    (indices : Finset Nat) (j : Nat → Nat) (T : Nat → MvPolynomial σ K)
    (bound n : Nat) (hbound : ∀ α ∈ indices, j α ≤ bound)
    (hne : (lNP indices j T).coeff n ≠ 0) : n ≤ bound := by
  apply Nat.le_of_not_gt
  intro hn
  exact hne (clNPe indices j T bound n hbound hn)
end Nagata.Workers.W17
end
section
namespace Nagata.Workers.W17
open scoped BigOperators
theorem dCff
    (S : Polynomial (MvPolynomial (Fin 3) ℂ))
    (G : MvPolynomial (Fin 3) ℂ) (j : ℕ → ℕ)
    (T : ℕ → MvPolynomial (Fin 3) ℂ)
    (hfactor : ∀ α, S.coeff α = G ^ j α * T α)
    (c : Fin 3) (s : ℂ) :
    Nagata.W27.dCH c (S.eval (MvPolynomial.C s)) =
      Nagata.Workers.W28.fPF S.support j
        (fun α => Nagata.W27.dCH c (T α))
        (Nagata.W27.dCH c G) s := by
  classical
  rw [Polynomial.eval_eq_sum]
  unfold Polynomial.sum Nagata.Workers.W28.fPF
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro α hα
  rw [hfactor, map_mul, map_mul, map_pow, map_pow]
  simp only [Nagata.W27.dCH, MvPolynomial.eval₂Hom_C, map_pow]
  ring
end Nagata.Workers.W17
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W18
open Nagata.CS
theorem sEiDz
    (F : Polynomial (ℂ → ℂ)) (j : ℕ) (z : ℂ) :
    iteratedDeriv j (fun w => sE F z w) 0 =
      (j.factorial : ℂ) * F.coeff j z := by
  classical
  simp only [sE, Polynomial.sum_def]
  rw [iteratedDeriv_fun_sum (fun k _ =>
    contDiffAt_const.mul (contDiffAt_id.pow k))]
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
  rw [Finset.sum_eq_single j]
  · simp [mul_comm]
  · intro k hk hkj
    simp [Ne.symm hkj]
  · intro hj
    have hc : F.coeff j = 0 := by
      simpa only [Polynomial.mem_support_iff, not_not] using hj
    simp [hc]
theorem aOAnc
    (f : ℂ → ℂ) (a c : ℂ) (hc : c ≠ 0) (hf : AnalyticAt ℂ f a) :
    analyticOrderAt (fun z => c * f z) a = analyticOrderAt f a := by
  have hconst : AnalyticAt ℂ (fun _ : ℂ => c) a := analyticAt_const
  change analyticOrderAt ((fun _ : ℂ => c) * f) a = _
  rw [analyticOrderAt_mul hconst hf, hconst.analyticOrderAt_eq_zero.mpr hc, zero_add]
theorem scaA
    (F : Polynomial (ℂ → ℂ)) (a : ℂ) (j : ℕ)
    (hF : AnalyticAt ℂ (fun p : ℂ × ℂ => sE F p.1 p.2) (a, 0)) :
    AnalyticAt ℂ (F.coeff j) a := by
  have hd := Nagata.W19.aAtiD a hF j
  have he : (fun x => iteratedDeriv j (fun y => sE F x y) 0) =
      (fun x => (j.factorial : ℂ) * F.coeff j x) := by
    funext x
    exact sEiDz F j x
  rw [he] at hd
  have hc : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hh := (analyticAt_const (v := (j.factorial : ℂ)⁻¹)).mul hd
  change AnalyticAt ℂ (fun x => (j.factorial : ℂ)⁻¹ *
    ((j.factorial : ℂ) * F.coeff j x)) a at hh
  simpa only [← mul_assoc, inv_mul_cancel₀ hc, one_mul] using hh
theorem sco
    (F : Polynomial (ℂ → ℂ)) (a : ℂ) (m j : ℕ)
    (hF : Nagata.Workers.W28.HAOAL (𝕜 := ℂ)
      (fun p : ℂ × ℂ => sE F p.1 p.2) (a, 0) m) :
    ((m - j : ℕ) : ℕ∞) ≤ analyticOrderAt (F.coeff j) a := by
  obtain ⟨P, hP, hzero⟩ := hF
  have ho := Nagata.W19.tiDoo a hP m j hzero
  have he : (fun x => iteratedDeriv j (fun y => sE F x y) 0) =
      (fun x => (j.factorial : ℂ) * F.coeff j x) := by
    funext x
    exact sEiDz F j x
  rw [he] at ho
  rw [aOAnc (F.coeff j) a (j.factorial : ℂ)
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j))
    (scaA F a j ⟨P, hP⟩)] at ho
  exact ho
end Nagata.W18
end
end
section
noncomputable section
namespace Nagata.W18
open Nagata.Workers.W28
theorem nEepE
    (H : Polynomial (Polynomial ℂ)) (z : ℂ × ℂ) :
    (H.eval (Polynomial.C z.2)).eval z.1 =
      MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z.1 else z.2)
        (nTB H) := by
  have h := ebTN z.1 z.2 (nTB H)
  have hinv : bTN (nTB H) = H :=
    RingHom.congr_fun bTNcn H
  rw [hinv] at h
  have hcoords : ![z.1, z.2] = (fun i : Fin 2 => if i = 0 then z.1 else z.2) := by
    funext i
    fin_cases i <;> rfl
  simpa only [hcoords] using h
end Nagata.W18
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators
theorem ceaA
    (I : Finset ℕ) (j : ℕ → ℕ) (R : ℕ → MvPolynomial (Fin 2) ℂ) (u : ℕ)
    (κ : CP → CP) (ξ c : ℂ)
    (hκ : AnalyticAt ℂ κ (ξ, 0)) :
    AnalyticAt ℂ
      (fun q : CP => ∑ α ∈ I.filter (fun α => α + j α = u),
        q.2 ^ j α * pPE (R α) (κ (q.1, 0))) (ξ, c) := by
  have hf := (ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt (ξ, c)
  have hw := (ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt (ξ, c)
  have harg : AnalyticAt ℂ (fun q : CP => (q.1, (0 : ℂ))) (ξ, c) :=
    hf.prod analyticAt_const
  have hc := hκ.comp (f := fun q : CP => (q.1, (0 : ℂ))) harg
  apply Finset.analyticAt_fun_sum
  intro α hα
  have hr : AnalyticAt ℂ (fun q : CP => pPE (R α) (κ (q.1, 0))) (ξ, c) :=
    AnalyticAt.comp (g := pPE (R α))
      (f := fun q : CP => κ (q.1, 0))
      (pPEaA (R α) (κ (ξ, 0))) hc
  exact (hw.pow (j α)).mul hr
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators
theorem incep
    (G : MvPolynomial (Fin 2) ℂ)
    (e : OpenPartialHomeomorph CP CP)
    (he : (e : CP → CP) = pNC G)
    (p : ℂ → CP) (z₀ : ℂ) (hp : ContinuousAt p z₀)
    (hsource : p z₀ ∈ e.source)
    (hG : ∀ᶠ z in 𝓝 z₀, pPE G (p z) = 0) :
    ∀ᶠ z in 𝓝 z₀, e.symm ((p z).1, 0) = p z := by
  have hs : ∀ᶠ z in 𝓝 z₀, p z ∈ e.source :=
    hp.preimage_mem_nhds (e.open_source.mem_nhds hsource)
  filter_upwards [hs, hG] with z hz hg
  have hh := e.left_inv hz
  simpa only [he, pNC, hg] using hh
def cNP (p : ℂ → CP) (a : ℂ → ℂ) (k : ℕ)
    (q : CP) : CP := ((p q.1).1, q.2 / a q.1 ^ k)
theorem cNPaA
    (p : ℂ → CP) (a : ℂ → ℂ) (k : ℕ) (z₀ w₀ : ℂ)
    (hp : AnalyticAt ℂ p z₀) (ha : AnalyticAt ℂ a z₀) (ha0 : a z₀ ≠ 0) :
    AnalyticAt ℂ (cNP p a k) (z₀, w₀) := by
  have hf := (ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt (z₀, w₀)
  have hw := (ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt (z₀, w₀)
  have hpc := hp.comp (f := Prod.fst) hf
  have ht := ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt (p z₀)).comp (f := fun q : CP => p q.1) hpc
  have hac := ha.comp (f := Prod.fst) hf
  exact ht.prod (hw.div (hac.pow k) (pow_ne_zero k ha0))
theorem pfooc
    (I : Finset ℕ) (j : ℕ → ℕ) (R : ℕ → MvPolynomial (Fin 2) ℂ)
    (G : MvPolynomial (Fin 2) ℂ)
    (e : OpenPartialHomeomorph CP CP)
    (he : (e : CP → CP) = pNC G)
    (p : ℂ → CP) (a : ℂ → ℂ) (d k : ℕ) (z₀ w₀ : ℂ)
    (hp : AnalyticAt ℂ p z₀) (ha : AnalyticAt ℂ a z₀) (ha0 : a z₀ ≠ 0)
    (hsource : p z₀ ∈ e.source)
    (hG : ∀ᶠ z in 𝓝 z₀, pPE G (p z) = 0)
    (m : ℕ)
    (horder : HAOAL (𝕜 := ℂ)
      (fun q : CP => ∑ α ∈ I,
        q.2 ^ j α * pPE (R α) (e.symm (q.1, 0)))
      ((p z₀).1, w₀ / a z₀ ^ k) m) :
    HAOAL (𝕜 := ℂ)
      (fun q : CP => a q.1 ^ d * ∑ α ∈ I,
        (q.2 / a q.1 ^ k) ^ j α * pPE (R α) (p q.1)) (z₀, w₀) m := by
  have hc := horder.comp (f := cNP p a k) (cNPaA p a k z₀ w₀ hp ha ha0)
  have hg := incep G e he p z₀ hp.continuousAt hsource hG
  have hf := (ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt (z₀, w₀)
  have hge := hf.continuousAt.tendsto.eventually hg
  have hlocal : HAOAL (𝕜 := ℂ)
      (fun q : CP => ∑ α ∈ I,
        (q.2 / a q.1 ^ k) ^ j α * pPE (R α) (p q.1)) (z₀, w₀) m := by
    apply hc.congr
    exact hge.mono fun q hq => by
      change e.symm ((p q.1).1, 0) = p q.1 at hq
      simp only [Function.comp_apply, cNP, hq]
  exact Nagata.VUO.aoml
    ((ha.comp (f := Prod.fst) hf).pow d) hlocal
end Nagata.Workers.W28
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology
def nCP (X : Fin 3 → ℂ → ℂ) (c : Fin 3) (z : ℂ) : CP :=
  (X (c.succAbove 0) z / X c z, X (c.succAbove 1) z / X c z)
theorem nCPaA
    (X : Fin 3 → ℂ → ℂ) (c : Fin 3) (z₀ : ℂ)
    (hX : ∀ i, AnalyticAt ℂ (X i) z₀) (hc : X c z₀ ≠ 0) :
    AnalyticAt ℂ (nCP X c) z₀ :=
  ((hX (c.succAbove 0)).div (hX c) hc).prod
    ((hX (c.succAbove 1)).div (hX c) hc)
theorem nCPe
    (G : MvPolynomial (Fin 3) ℂ) (k : ℕ) (hG : G.IsHomogeneous k)
    (X : Fin 3 → ℂ → ℂ) (c : Fin 3) (z : ℂ)
    (hc : X c z ≠ 0) (hzero : MvPolynomial.eval (fun a => X a z) G = 0) :
    pPE (Nagata.W27.dCH c G) (nCP X c z) = 0 := by
  let x : Fin 3 → ℂ := fun a => X a z
  let v : Fin 2 → ℂ := fun a => x (c.succAbove a) / x c
  let y : Fin 3 → ℂ := Fin.insertNth (α := fun _ : Fin 3 => ℂ) c 1 v
  have hy : (fun a => x c * y a) = x := by
    exact Nagata.Workers.W17.scv c x hc
  have hh := Nagata.W16.hes hG y (x c)
  rw [hy, hzero] at hh
  have hz : MvPolynomial.eval y G = 0 :=
    (mul_eq_zero.mp hh.symm).resolve_left (pow_ne_zero k hc)
  have he : pPE (Nagata.W27.dCH c G) (nCP X c z) =
      MvPolynomial.eval v (Nagata.W27.dCH c G) := by
    apply congrArg (fun a : Fin 2 → ℂ => MvPolynomial.eval a (Nagata.W27.dCH c G))
    funext a
    fin_cases a <;> rfl
  rw [he, Nagata.Workers.W17.edCH]
  exact hz
theorem nCPel
    (G : MvPolynomial (Fin 3) ℂ) (k : ℕ) (hG : G.IsHomogeneous k)
    (X : Fin 3 → ℂ → ℂ) (c : Fin 3) (z₀ : ℂ)
    (ha : ContinuousAt (X c) z₀) (hc : X c z₀ ≠ 0)
    (hzero : ∀ᶠ z in 𝓝 z₀, MvPolynomial.eval (fun a => X a z) G = 0) :
    ∀ᶠ z in 𝓝 z₀, pPE (Nagata.W27.dCH c G)
      (nCP X c z) = 0 := by
  filter_upwards [ha.eventually_ne hc, hzero] with z hcz hz
  exact nCPe G k hG X c z hcz hz
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators
theorem hnfip
    (I : Finset ℕ) (j : ℕ → ℕ) (T : ℕ → MvPolynomial (Fin 3) ℂ)
    (d k : ℕ) (hhom : ∀ α ∈ I, (T α).IsHomogeneous (d-k*j α))
    (hbound : ∀ α ∈ I, k*j α ≤ d)
    (X : Fin 3 → ℂ → ℂ) (c : Fin 3) (z w : ℂ) (hc : X c z ≠ 0) :
    (∑ α ∈ I, w ^ j α * MvPolynomial.eval (fun a => X a z) (T α)) =
      (X c z)^d * ∑ α ∈ I, (w/(X c z)^k)^j α *
        pPE (Nagata.W27.dCH c (T α)) (nCP X c z) := by
  rw [Nagata.Workers.W17.npfi I j T d k hhom hbound c (fun a => X a z) hc w]
  congr 1
  apply Finset.sum_congr rfl
  intro α hα
  congr 1
  apply congrArg (fun v : Fin 2 → ℂ => MvPolynomial.eval v (Nagata.W27.dCH c (T α)))
  funext a
  fin_cases a <;> rfl
theorem hnooc
    (I : Finset ℕ) (j : ℕ → ℕ) (T : ℕ → MvPolynomial (Fin 3) ℂ)
    (d k : ℕ) (hhom : ∀ α ∈ I, (T α).IsHomogeneous (d-k*j α))
    (hbound : ∀ α ∈ I, k*j α ≤ d)
    (G : MvPolynomial (Fin 3) ℂ) (hG : G.IsHomogeneous k)
    (X : Fin 3 → ℂ → ℂ) (c : Fin 3) (z₀ w₀ : ℂ)
    (hX : ∀ a, AnalyticAt ℂ (X a) z₀) (hc : X c z₀ ≠ 0)
    (hzero : ∀ᶠ z in 𝓝 z₀, MvPolynomial.eval (fun a => X a z) G = 0)
    (e : OpenPartialHomeomorph CP CP)
    (he : (e : CP → CP) = pNC (Nagata.W27.dCH c G))
    (hsource : nCP X c z₀ ∈ e.source) (m : ℕ)
    (horder : HAOAL (𝕜 := ℂ)
      (fun q : CP => ∑ α ∈ I,
        q.2 ^ j α * pPE (Nagata.W27.dCH c (T α)) (e.symm (q.1, 0)))
      ((nCP X c z₀).1, w₀ / X c z₀ ^ k) m) :
    HAOAL (𝕜 := ℂ)
      (fun q : CP => ∑ α ∈ I,
        q.2 ^ j α * MvPolynomial.eval (fun a => X a q.1) (T α)) (z₀, w₀) m := by
  have hp := nCPaA X c z₀ hX hc
  have hcurve := nCPel G k hG X c z₀ (hX c).continuousAt hc hzero
  have h := pfooc I j
    (fun α => Nagata.W27.dCH c (T α)) (Nagata.W27.dCH c G)
    e he (nCP X c) (X c) d k z₀ w₀ hp (hX c) hc hsource hcurve m horder
  apply h.congr
  have hne := (hX c).continuousAt.eventually_ne hc
  have hf : ContinuousAt (Prod.fst : CP → ℂ) (z₀, w₀) := continuousAt_fst
  exact (hf.tendsto.eventually hne).mono fun q hq => by
    exact (hnfip I j T d k hhom hbound X c q.1 q.2 hq).symm
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators
theorem aAcs (p : ℂ → CP) (z₀ : ℂ)
    (hp : AnalyticAt ℂ p z₀) : AnalyticAt ℂ (fun z => (p z).swap) z₀ := by
  exact (((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt (p z₀)).comp (f := p) hp).prod
    (((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt (p z₀)).comp (f := p) hp)
theorem hnoos
    (I : Finset ℕ) (j : ℕ → ℕ) (T : ℕ → MvPolynomial (Fin 3) ℂ)
    (d k : ℕ) (hhom : ∀ α ∈ I, (T α).IsHomogeneous (d-k*j α))
    (hbound : ∀ α ∈ I, k*j α ≤ d)
    (G : MvPolynomial (Fin 3) ℂ) (hG : G.IsHomogeneous k)
    (X : Fin 3 → ℂ → ℂ) (c : Fin 3) (z₀ w₀ : ℂ)
    (hX : ∀ a, AnalyticAt ℂ (X a) z₀) (hc : X c z₀ ≠ 0)
    (hzero : ∀ᶠ z in 𝓝 z₀, MvPolynomial.eval (fun a => X a z) G = 0)
    (e : OpenPartialHomeomorph CP CP)
    (he : (e : CP → CP) = pNC
      (Nagata.Workers.W17.aS1 (Nagata.W27.dCH c G)))
    (hsource : (nCP X c z₀).swap ∈ e.source) (m : ℕ)
    (horder : HAOAL (𝕜 := ℂ)
      (fun q : CP => ∑ α ∈ I,
        q.2 ^ j α * pPE
          (Nagata.Workers.W17.aS1 (Nagata.W27.dCH c (T α))) (e.symm (q.1, 0)))
      ((nCP X c z₀).2, w₀ / X c z₀ ^ k) m) :
    HAOAL (𝕜 := ℂ)
      (fun q : CP => ∑ α ∈ I,
        q.2 ^ j α * MvPolynomial.eval (fun a => X a q.1) (T α)) (z₀, w₀) m := by
  have hp := aAcs (nCP X c) z₀
    (nCPaA X c z₀ hX hc)
  have hcurve : ∀ᶠ z in 𝓝 z₀,
      pPE (Nagata.Workers.W17.aS1 (Nagata.W27.dCH c G))
        (nCP X c z).swap = 0 := by
    simpa only [Nagata.Workers.W17.eaS, Prod.swap_swap] using
      nCPel G k hG X c z₀ (hX c).continuousAt hc hzero
  have h := pfooc I j
    (fun α => Nagata.Workers.W17.aS1 (Nagata.W27.dCH c (T α)))
    (Nagata.Workers.W17.aS1 (Nagata.W27.dCH c G))
    e he (fun z => (nCP X c z).swap) (X c) d k z₀ w₀
    hp (hX c) hc hsource hcurve m horder
  simp only [Nagata.Workers.W17.eaS, Prod.swap_swap] at h
  apply h.congr
  have hne := (hX c).continuousAt.eventually_ne hc
  have hf : ContinuousAt (Prod.fst : CP → ℂ) (z₀, w₀) := continuousAt_fst
  exact (hf.tendsto.eventually hne).mono fun q hq => by
    exact (hnfip I j T d k hhom hbound X c q.1 q.2 hq).symm
end Nagata.Workers.W28
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators
theorem pGnzo
    (G : MvPolynomial (Fin 2) ℂ) (p : CP)
    (hpartial : pPE (MvPolynomial.pderiv 1 G) p ≠ 0) :
    pG G p ≠ 0 := by
  intro h
  have hh := congrArg (fun L : CP →L[ℂ] ℂ => L (0, 1)) h
  apply hpartial
  simpa [pG] using hh
theorem ensfp
    (I : Finset ℕ) (j : ℕ → ℕ) (R : ℕ → MvPolynomial (Fin 2) ℂ)
    (u : ℕ) (hmin : ∀ α ∈ I, u ≤ α + j α)
    (G : MvPolynomial (Fin 2) ℂ) (p V : CP)
    (hp : pPE G p = 0)
    (hpartial : pPE (MvPolynomial.pderiv 1 G) p ≠ 0)
    (exceptional : Finset ℂ) (m : ℕ)
    (horders : ∀ᶠ s : ℂ in 𝓝 0, s ∉ exceptional →
      Nagata.AM.oAL
        (fun i : Fin 2 => if i = 0 then (p + s • V).1 else (p + s • V).2)
        m (fPF I j R G s)) :
    ∃ e : OpenPartialHomeomorph CP CP,
      (e : CP → CP) = pNC G ∧
      p ∈ e.source ∧ AnalyticAt ℂ e.symm (e p) ∧
      ∀ n < m, iteratedFDeriv ℂ n
        (fun q : CP =>
          ∑ α ∈ I.filter (fun α => α + j α = u),
            q.2 ^ j α * pPE (R α) (e.symm (q.1, 0)))
        (p.1, pG G p V) = 0 := by
  obtain ⟨e, he, hsource, hi⟩ := eanco G p hpartial
  have hi' : AnalyticAt ℂ e.symm (e p) := by simpa only [he] using hi
  refine ⟨e, he, hsource, hi', ?_⟩
  exact nscj I j R u hmin G e he
    (pG G p) p V hsource hi' (pPEhF G p)
    hp exceptional m horders
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators
theorem hns
    (I : Finset ℕ) (j : ℕ → ℕ) (T : ℕ → MvPolynomial (Fin 3) ℂ)
    (u : ℕ) (hmin : ∀ α ∈ I, u ≤ α + j α)
    (d k : ℕ) (hhom : ∀ α ∈ I, (T α).IsHomogeneous (d-k*j α))
    (hbound : ∀ α ∈ I, k*j α ≤ d)
    (G : MvPolynomial (Fin 3) ℂ) (hG : G.IsHomogeneous k)
    (X : Fin 3 → ℂ → ℂ) (c : Fin 3) (z₀ w₀ : ℂ)
    (hX : ∀ a, AnalyticAt ℂ (X a) z₀) (hc : X c z₀ ≠ 0)
    (hzero : ∀ᶠ z in 𝓝 z₀, MvPolynomial.eval (fun a => X a z) G = 0)
    (hpartial : pPE (MvPolynomial.pderiv 1 (Nagata.W27.dCH c G))
      (nCP X c z₀) ≠ 0)
    (V : CP)
    (hvelocity : pG (Nagata.W27.dCH c G)
      (nCP X c z₀) V = w₀ / X c z₀ ^ k)
    (exceptional : Finset ℂ) (m : ℕ)
    (horders : ∀ᶠ s : ℂ in 𝓝 0, s ∉ exceptional →
      Nagata.AM.oAL
        (fun a : Fin 2 => if a = 0 then (nCP X c z₀ + s • V).1
          else (nCP X c z₀ + s • V).2)
        m (fPF I j (fun α => Nagata.W27.dCH c (T α))
          (Nagata.W27.dCH c G) s)) :
    HAOAL (𝕜 := ℂ)
      (fun q : CP => ∑ α ∈ I.filter (fun α => α + j α = u),
        q.2 ^ j α * MvPolynomial.eval (fun a => X a q.1) (T α)) (z₀, w₀) m := by
  let p := nCP X c z₀
  let A := Nagata.W27.dCH c G
  let R : ℕ → MvPolynomial (Fin 2) ℂ := fun α => Nagata.W27.dCH c (T α)
  have hp : pPE A p = 0 :=
    nCPe G k hG X c z₀ hc hzero.self_of_nhds
  obtain ⟨e, he, hs, hi, hjets⟩ := ensfp
    I j R u hmin A p V hp hpartial exceptional m horders
  have hi' : AnalyticAt ℂ e.symm (p.1, 0) := by
    have hep : e p = (p.1, (0 : ℂ)) := by
      rw [he]
      change (p.1, pPE A p) = (p.1, 0)
      rw [hp]
    rwa [hep] at hi
  have hcentral : HAOAL (𝕜 := ℂ)
      (fun q : CP => ∑ α ∈ I.filter (fun α => α + j α = u),
        q.2 ^ j α * pPE (R α) (e.symm (q.1, 0)))
      (p.1, w₀ / X c z₀ ^ k) m := by
    rw [← hvelocity]
    exact Nagata.Workers.W17.aooiF
      (ceaA I j R u e.symm p.1 (pG A p V) hi') m hjets
  exact hnooc (I.filter (fun α => α + j α = u)) j T d k
    (fun α hα => hhom α (Finset.mem_filter.mp hα).1)
    (fun α hα => hbound α (Finset.mem_filter.mp hα).1) G hG X c z₀ w₀ hX hc hzero
    e he hs m hcentral
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators
theorem hnsop
    (I : Finset ℕ) (j : ℕ → ℕ) (T : ℕ → MvPolynomial (Fin 3) ℂ)
    (u : ℕ) (hmin : ∀ α ∈ I, u ≤ α + j α)
    (d k : ℕ) (hhom : ∀ α ∈ I, (T α).IsHomogeneous (d-k*j α))
    (hbound : ∀ α ∈ I, k*j α ≤ d)
    (G : MvPolynomial (Fin 3) ℂ) (hG : G.IsHomogeneous k)
    (X : Fin 3 → ℂ → ℂ) (c : Fin 3) (z₀ w₀ : ℂ)
    (hX : ∀ a, AnalyticAt ℂ (X a) z₀) (hc : X c z₀ ≠ 0)
    (hzero : ∀ᶠ z in 𝓝 z₀, MvPolynomial.eval (fun a => X a z) G = 0)
    (hpartial : pPE (MvPolynomial.pderiv 0 (Nagata.W27.dCH c G))
      (nCP X c z₀) ≠ 0)
    (V : CP)
    (hvelocity : pG (Nagata.W27.dCH c G)
      (nCP X c z₀) V = w₀ / X c z₀ ^ k)
    (exceptional : Finset ℂ) (m : ℕ)
    (horders : ∀ᶠ s : ℂ in 𝓝 0, s ∉ exceptional →
      Nagata.AM.oAL
        (fun a : Fin 2 => if a = 0 then (nCP X c z₀ + s • V).1
          else (nCP X c z₀ + s • V).2)
        m (fPF I j (fun α => Nagata.W27.dCH c (T α))
          (Nagata.W27.dCH c G) s)) :
    HAOAL (𝕜 := ℂ)
      (fun q : CP => ∑ α ∈ I.filter (fun α => α + j α = u),
        q.2 ^ j α * MvPolynomial.eval (fun a => X a q.1) (T α)) (z₀, w₀) m := by
  let p := nCP X c z₀
  let A := Nagata.W27.dCH c G
  let R : ℕ → MvPolynomial (Fin 2) ℂ := fun α => Nagata.W27.dCH c (T α)
  have hp : pPE A p = 0 :=
    nCPe G k hG X c z₀ hc hzero.self_of_nhds
  have hps : pPE (Nagata.Workers.W17.aS1 A) p.swap = 0 := by
    simpa only [Nagata.Workers.W17.eaS, Prod.swap_swap] using hp
  have hpartialS : pPE
      (MvPolynomial.pderiv 1 (Nagata.Workers.W17.aS1 A)) p.swap ≠ 0 := by
    rwa [Nagata.Workers.W17.pYaS]
  have hvelocityS : pG (Nagata.Workers.W17.aS1 A) p.swap V.swap =
      w₀ / X c z₀ ^ k := by
    rw [Nagata.Workers.W17.pGaS]
    exact hvelocity
  have hordersS : ∀ᶠ s : ℂ in 𝓝 0, s ∉ exceptional →
      Nagata.AM.oAL
        (fun a : Fin 2 => if a = 0 then (p.swap + s • V.swap).1 else (p.swap + s • V.swap).2)
        m (fPF I j (fun α => Nagata.Workers.W17.aS1 (R α))
          (Nagata.Workers.W17.aS1 A) s) := by
    filter_upwards [horders] with s hs hex
    rw [← Nagata.Workers.W17.aSfPF]
    exact (Nagata.Workers.W17.oaSi
      (fPF I j R A s) (p + s • V) m).mpr (hs hex)
  obtain ⟨e, he, hs, hi, hjets⟩ := ensfp
    I j (fun α => Nagata.Workers.W17.aS1 (R α)) u hmin
    (Nagata.Workers.W17.aS1 A) p.swap V.swap hps hpartialS exceptional m hordersS
  have hi' : AnalyticAt ℂ e.symm (p.2, 0) := by
    have hep : e p.swap = (p.2, (0 : ℂ)) := by
      rw [he]
      change (p.2, pPE (Nagata.Workers.W17.aS1 A) p.swap) = (p.2, 0)
      rw [hps]
    rwa [hep] at hi
  have hcentral : HAOAL (𝕜 := ℂ)
      (fun q : CP => ∑ α ∈ I.filter (fun α => α + j α = u),
        q.2 ^ j α * pPE (Nagata.Workers.W17.aS1 (R α)) (e.symm (q.1, 0)))
      (p.2, w₀ / X c z₀ ^ k) m := by
    rw [← hvelocityS]
    exact Nagata.Workers.W17.aooiF
      (ceaA I j (fun α => Nagata.Workers.W17.aS1 (R α)) u e.symm
        p.2 (pG (Nagata.Workers.W17.aS1 A) p.swap V.swap) hi') m hjets
  exact hnoos (I.filter (fun α => α + j α = u)) j T d k
    (fun α hα => hhom α (Finset.mem_filter.mp hα).1)
    (fun α hα => hbound α (Finset.mem_filter.mp hα).1) G hG X c z₀ w₀ hX hc hzero
    e he hs m hcentral
end Nagata.Workers.W28
end
end
section
noncomputable section
namespace Nagata.Workers.W28
open scoped Topology BigOperators
theorem pGnzi
    (G : MvPolynomial (Fin 2) ℂ) (p : CP) :
    pG G p ≠ 0 ↔
      pPE (MvPolynomial.pderiv 0 G) p ≠ 0 ∨
      pPE (MvPolynomial.pderiv 1 G) p ≠ 0 := by
  constructor
  · intro h
    by_cases h0 : pPE (MvPolynomial.pderiv 0 G) p ≠ 0
    · exact Or.inl h0
    · right
      intro h1
      apply h
      apply ContinuousLinearMap.ext
      intro z
      simp [pG, not_ne_iff.mp h0, h1]
  · intro h
    rcases h with h0 | h1
    · intro hz
      have hh := congrArg (fun L : CP →L[ℂ] ℂ => L (1, 0)) hz
      apply h0
      simpa [pG] using hh
    · exact pGnzo G p h1
theorem hnsog
    (I : Finset ℕ) (j : ℕ → ℕ) (T : ℕ → MvPolynomial (Fin 3) ℂ)
    (u : ℕ) (hmin : ∀ α ∈ I, u ≤ α + j α)
    (d k : ℕ) (hhom : ∀ α ∈ I, (T α).IsHomogeneous (d-k*j α))
    (hbound : ∀ α ∈ I, k*j α ≤ d)
    (G : MvPolynomial (Fin 3) ℂ) (hG : G.IsHomogeneous k)
    (X : Fin 3 → ℂ → ℂ) (c : Fin 3) (z₀ w₀ : ℂ)
    (hX : ∀ a, AnalyticAt ℂ (X a) z₀) (hc : X c z₀ ≠ 0)
    (hzero : ∀ᶠ z in 𝓝 z₀, MvPolynomial.eval (fun a => X a z) G = 0)
    (hgradient : pPE (MvPolynomial.pderiv 0 (Nagata.W27.dCH c G))
      (nCP X c z₀) ≠ 0 ∨
      pPE (MvPolynomial.pderiv 1 (Nagata.W27.dCH c G))
      (nCP X c z₀) ≠ 0)
    (V : CP)
    (hvelocity : pG (Nagata.W27.dCH c G)
      (nCP X c z₀) V = w₀ / X c z₀ ^ k)
    (exceptional : Finset ℂ) (m : ℕ)
    (horders : ∀ᶠ s : ℂ in 𝓝 0, s ∉ exceptional →
      Nagata.AM.oAL
        (fun a : Fin 2 => if a = 0 then (nCP X c z₀ + s • V).1
          else (nCP X c z₀ + s • V).2)
        m (fPF I j (fun α => Nagata.W27.dCH c (T α))
          (Nagata.W27.dCH c G) s)) :
    HAOAL (𝕜 := ℂ)
      (fun q : CP => ∑ α ∈ I.filter (fun α => α + j α = u),
        q.2 ^ j α * MvPolynomial.eval (fun a => X a q.1) (T α)) (z₀, w₀) m := by
  rcases hgradient with h0 | h1
  · exact hnsop I j T u hmin d k hhom hbound
      G hG X c z₀ w₀ hX hc hzero h0 V hvelocity exceptional m horders
  · exact hns I j T u hmin d k hhom hbound
      G hG X c z₀ w₀ hX hc hzero h1 V hvelocity exceptional m horders
theorem hnson
    (I : Finset ℕ) (j : ℕ → ℕ) (T : ℕ → MvPolynomial (Fin 3) ℂ)
    (u : ℕ) (hmin : ∀ α ∈ I, u ≤ α + j α)
    (d k : ℕ) (hhom : ∀ α ∈ I, (T α).IsHomogeneous (d-k*j α))
    (hbound : ∀ α ∈ I, k*j α ≤ d)
    (G : MvPolynomial (Fin 3) ℂ) (hG : G.IsHomogeneous k)
    (X : Fin 3 → ℂ → ℂ) (c : Fin 3) (z₀ w₀ : ℂ)
    (hX : ∀ a, AnalyticAt ℂ (X a) z₀) (hc : X c z₀ ≠ 0)
    (hzero : ∀ᶠ z in 𝓝 z₀, MvPolynomial.eval (fun a => X a z) G = 0)
    (hdifferential : pG (Nagata.W27.dCH c G)
      (nCP X c z₀) ≠ 0)
    (V : CP)
    (hvelocity : pG (Nagata.W27.dCH c G)
      (nCP X c z₀) V = w₀ / X c z₀ ^ k)
    (exceptional : Finset ℂ) (m : ℕ)
    (horders : ∀ᶠ s : ℂ in 𝓝 0, s ∉ exceptional →
      Nagata.AM.oAL
        (fun a : Fin 2 => if a = 0 then (nCP X c z₀ + s • V).1
          else (nCP X c z₀ + s • V).2)
        m (fPF I j (fun α => Nagata.W27.dCH c (T α))
          (Nagata.W27.dCH c G) s)) :
    HAOAL (𝕜 := ℂ)
      (fun q : CP => ∑ α ∈ I.filter (fun α => α + j α = u),
        q.2 ^ j α * MvPolynomial.eval (fun a => X a q.1) (T α)) (z₀, w₀) m := by
  exact hnsog I j T u hmin d k hhom hbound
    G hG X c z₀ w₀ hX hc hzero
    ((pGnzi _ _).mp hdifferential)
    V hvelocity exceptional m horders
end Nagata.Workers.W28
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
open Module
namespace Nagata.W01
variable {K : Type*} [Field K]
abbrev PPV (K : Type*) := Fin 3 → K
theorem prpi
    (p q : Projectivization K (PPV K)) (hpq : p ≠ q) :
    LinearIndependent K ![p.rep, q.rep] := by
  rw [linearIndependent_fin2]
  refine ⟨q.rep_nonzero, ?_⟩
  intro a ha
  apply hpq
  rw [← Projectivization.mk_rep p, ← Projectivization.mk_rep q]
  exact (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨a, ha⟩
theorem eplb
    (L : PPV K →ₗ[K] K) (hL : L ≠ 0)
    (p q : Projectivization K (PPV K))
    (hpq : p ≠ q) (hp : L p.rep = 0) (hq : L q.rep = 0) :
    ∃ b : Basis (Fin 3) K (PPV K),
      b 0 = p.rep ∧ b 1 = q.rep ∧ L (b 2) = 1 := by
  classical
  obtain ⟨w, hw⟩ := Nagata.Workers.W14.nlFs L hL 1
  have hspan : Submodule.span K (Set.range ![p.rep, q.rep]) ≤ LinearMap.ker L := by
    apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    fin_cases i <;> simpa [LinearMap.mem_ker] using (by assumption : L _ = 0)
  have hwspan : w ∉ Submodule.span K (Set.range ![p.rep, q.rep]) := by
    intro h
    have hz : L w = 0 := hspan h
    exact one_ne_zero (hw.symm.trans hz)
  have hli : LinearIndependent K (Fin.snoc ![p.rep, q.rep] w) :=
    linearIndependent_finSnoc.mpr
      ⟨prpi p q hpq, hwspan⟩
  let b := basisOfPiSpaceOfLinearIndependent hli
  have hb : (b : Fin 3 → PPV K) = Fin.snoc ![p.rep, q.rep] w :=
    coe_basisOfPiSpaceOfLinearIndependent hli
  refine ⟨b, ?_, ?_, ?_⟩
  · change (b : Fin 3 → PPV K) 0 = _
    rw [hb]
    rfl
  · change (b : Fin 3 → PPV K) 1 = _
    rw [hb]
    rfl
  · change L ((b : Fin 3 → PPV K) 2) = _
    rw [hb]
    exact hw
theorem abtc
    (L : PPV K →ₗ[K] K)
    (b : Basis (Fin 3) K (PPV K))
    (h0 : L (b 0) = 0) (h1 : L (b 1) = 0) (h2 : L (b 2) = 1)
    (v : PPV K) : b.repr v 2 = L v := by
  have h := congrArg L (b.sum_repr v)
  rw [Fin.sum_univ_three] at h
  simpa only [map_add, map_smul, h0, h1, h2, smul_eq_mul, mul_zero, mul_one, zero_add] using h
theorem etpzb
    (L : PPV K →ₗ[K] K) (hL : L ≠ 0)
    (p₀ p₁ p₂ : Projectivization K (PPV K))
    (h01 : p₀ ≠ p₁) (h20 : p₂ ≠ p₀) (h21 : p₂ ≠ p₁)
    (h0 : L p₀.rep = 0) (h1 : L p₁.rep = 0) (h2 : L p₂.rep = 0) :
    ∃ (b : Basis (Fin 3) K (PPV K)) (a c : K),
      b 0 = p₀.rep ∧ b 1 = p₁.rep ∧ L (b 2) = 1 ∧
      a ≠ 0 ∧ c ≠ 0 ∧ p₂.rep = a • b 0 + c • b 1 := by
  obtain ⟨b, hb0, hb1, hb2⟩ := eplb L hL p₀ p₁ h01 h0 h1
  have hL0 : L (b 0) = 0 := hb0 ▸ h0
  have hL1 : L (b 1) = 0 := hb1 ▸ h1
  have hz : b.repr p₂.rep 2 = 0 := by
    rw [abtc L b hL0 hL1 hb2, h2]
  have hex : p₂.rep = (b.repr p₂.rep 0) • b 0 + (b.repr p₂.rep 1) • b 1 := by
    have he := (b.sum_repr p₂.rep).symm
    rw [Fin.sum_univ_three] at he
    simpa only [hz, zero_smul, add_zero] using he
  have ha : b.repr p₂.rep 0 ≠ 0 := by
    intro ha
    have he : (b.repr p₂.rep 1) • p₁.rep = p₂.rep := by
      simpa [ha, hb1] using hex.symm
    apply h21
    rw [← Projectivization.mk_rep p₂, ← Projectivization.mk_rep p₁]
    exact (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨_, he⟩
  have hc : b.repr p₂.rep 1 ≠ 0 := by
    intro hc
    have he : (b.repr p₂.rep 0) • p₀.rep = p₂.rep := by
      simpa [hc, hb0] using hex.symm
    apply h20
    rw [← Projectivization.mk_rep p₂, ← Projectivization.mk_rep p₀]
    exact (Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr ⟨_, he⟩
  exact ⟨b, _, _, hb0, hb1, hb2, ha, hc, hex⟩
end Nagata.W01
end
end
section
noncomputable section
open Module MvPolynomial
open scoped BigOperators
namespace Nagata.W01
abbrev PP1 := MvPolynomial (Fin 3) ℂ
abbrev CPV := Fin 3 → ℂ
def lC (T : CPV →ₗ[ℂ] CPV) (j : Fin 3) :
    PP1 := ∑ i : Fin 3, C (T (Pi.single i 1) j) * X i
def lS (T : CPV →ₗ[ℂ] CPV) :
    PP1 →ₐ[ℂ] PP1 := aeval (lC T)
@[simp] theorem lSX
    (T : CPV →ₗ[ℂ] CPV) (j : Fin 3) :
    lS T (X j) = lC T j := aeval_X _ _
theorem elC (T : CPV →ₗ[ℂ] CPV)
    (v : CPV) (j : Fin 3) :
    eval v (lC T j) = T v j := by
  have hv : v = ∑ i : Fin 3, v i • (Pi.single i (1 : ℂ) : CPV) := by
    ext k
    simp [Pi.single_apply]
  conv_rhs => rw [hv, map_sum]
  simp only [lC, map_sum, map_mul, eval_C, eval_X,
    Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _
theorem elS (T : CPV →ₗ[ℂ] CPV)
    (P : PP1) (v : CPV) :
    eval v (lS T P) = eval (T v) P := by
  change aeval v (aeval (lC T) P) = aeval (T v) P
  rw [comp_aeval_apply]
  have hg : (fun j => aeval v (lC T j)) = T v := by
    funext j
    exact elC T v j
  rw [hg]
theorem lSi
    (e : CPV ≃ₗ[ℂ] CPV) (P : PP1) :
    lS e.symm.toLinearMap (lS e.toLinearMap P) = P := by
  let : Infinite ℂ := Infinite.of_injective (fun n : ℕ => (n : ℂ)) Nat.cast_injective
  apply MvPolynomial.funext
  intro v
  rw [elS, elS]
  simp
def pCE (e : CPV ≃ₗ[ℂ] CPV) :
    PP1 ≃ₐ[ℂ] PP1 :=
  AlgEquiv.ofAlgHom (lS e.toLinearMap) (lS e.symm.toLinearMap)
    (by
      apply DFunLike.ext
      intro P
      exact lSi e.symm P)
    (by
      apply DFunLike.ext
      intro P
      exact lSi e P)
@[simp] theorem pCEa
    (e : CPV ≃ₗ[ℂ] CPV) (P : PP1) :
    pCE e P = lS e.toLinearMap P := rfl
theorem lCh
    (T : CPV →ₗ[ℂ] CPV) (j : Fin 3) :
    (lC T j).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  exact isHomogeneous_C_mul_X _ _
theorem lSh
    (T : CPV →ₗ[ℂ] CPV) {P : PP1} {d : ℕ}
    (hP : P.IsHomogeneous d) : (lS T P).IsHomogeneous d := by
  simpa only [lS, aeval_def, algebraMap_eq, one_mul] using
    hP.eval₂ (C : ℂ →+* PP1) (lC T)
      (fun r => isHomogeneous_C _ r) (lCh T)
theorem pCEhi
    (e : CPV ≃ₗ[ℂ] CPV) (P : PP1) (d : ℕ) :
    (pCE e P).IsHomogeneous d ↔ P.IsHomogeneous d := by
  constructor
  · intro h
    have hh := lSh e.symm.toLinearMap h
    simpa only [pCEa, lSi] using hh
  · exact lSh e.toLinearMap
theorem pCEdi
    (e : CPV ≃ₗ[ℂ] CPV) (P Q : PP1) :
    pCE e P ∣ pCE e Q ↔ P ∣ Q := by
  constructor
  · intro h
    have hh := map_dvd (pCE e).symm h
    simpa only [AlgEquiv.symm_apply_apply] using hh
  · exact map_dvd (pCE e)
def bPC (b : Basis (Fin 3) ℂ CPV) :
    PP1 ≃ₐ[ℂ] PP1 := pCE b.equivFun.symm
@[simp] theorem bPCe
    (b : Basis (Fin 3) ℂ CPV) (P : PP1) (v : CPV) :
    eval v (bPC b P) = eval (b.equivFun.symm v) P :=
  elS _ _ _
theorem bPCX
    (b : Basis (Fin 3) ℂ CPV) (j : Fin 3) :
    bPC b (X j) = ∑ i : Fin 3, C (b i j) * X i := by
  rw [bPC, pCEa, lSX]
  unfold lC
  apply Finset.sum_congr rfl
  intro i _
  have hi : b.equivFun.symm (Pi.single i 1) = b i := by
    rw [b.equivFun_symm_apply]
    simp [Pi.single_apply]
  rw [show b.equivFun.symm.toLinearMap (Pi.single i 1) = b i from hi]
end Nagata.W01
end
end
section
noncomputable section
open Module MvPolynomial
open scoped BigOperators
namespace Nagata.W01
@[simp] theorem bPChi
    (b : Basis (Fin 3) ℂ CPV) (P : PP1) (d : ℕ) :
    (bPC b P).IsHomogeneous d ↔ P.IsHomogeneous d :=
  pCEhi b.equivFun.symm P d
@[simp] theorem bPCdi
    (b : Basis (Fin 3) ℂ CPV) (P Q : PP1) :
    bPC b P ∣ bPC b Q ↔ P ∣ Q :=
  pCEdi b.equivFun.symm P Q
theorem bPCee
    (b : Basis (Fin 3) ℂ CPV) (P : PP1) :
    bPC b P =
      eval₂ C (fun j => ∑ i : Fin 3, C (b i j) * X i) P := by
  have hh : (bPC b).toAlgHom =
      aeval (fun j => ∑ i : Fin 3, C (b i j) * X i) := by
    apply MvPolynomial.algHom_ext
    intro j
    simpa only [AlgEquiv.coe_toAlgHom, aeval_X] using bPCX b j
  exact DFunLike.congr_fun hh P
theorem beFv (b : Basis (Fin 3) ℂ CPV) (i : Fin 3) :
    b.equivFun (b i) = Pi.single i 1 := by
  ext j
  simp [Pi.single_apply, eq_comm]
theorem etpzc
    (L : CPV →ₗ[ℂ] ℂ) (hL : L ≠ 0)
    (p₀ p₁ p₂ : Projectivization ℂ CPV)
    (h01 : p₀ ≠ p₁) (h20 : p₂ ≠ p₀) (h21 : p₂ ≠ p₁)
    (h0 : L p₀.rep = 0) (h1 : L p₁.rep = 0) (h2 : L p₂.rep = 0) :
    ∃ (b : Basis (Fin 3) ℂ CPV) (a c : ℂ),
      b 0 = p₀.rep ∧ b 1 = p₁.rep ∧ L (b 2) = 1 ∧ a ≠ 0 ∧ c ≠ 0 ∧
      b.equivFun p₀.rep = ![1, 0, 0] ∧
      b.equivFun p₁.rep = ![0, 1, 0] ∧ b.equivFun p₂.rep = ![a, c, 0] := by
  obtain ⟨b, a, c, hb0, hb1, hb2, ha, hc, hp2⟩ :=
    etpzb L hL p₀ p₁ p₂ h01 h20 h21 h0 h1 h2
  refine ⟨b, a, c, hb0, hb1, hb2, ha, hc, ?_, ?_, ?_⟩
  · rw [← hb0, beFv]
    ext i
    fin_cases i <;> simp
  · rw [← hb1, beFv]
    ext i
    fin_cases i <;> simp
  · rw [hp2, map_add, map_smul, map_smul, beFv, beFv]
    ext i
    fin_cases i <;> simp
theorem bPCea
    (b : Basis (Fin 3) ℂ CPV) (P : PP1)
    (p : Projectivization ℂ CPV) (v : CPV)
    (hv : b.equivFun p.rep = v) :
    eval v (bPC b P) = eval p.rep P := by
  rw [bPCe, ← hv, LinearEquiv.symm_apply_apply]
theorem bPClF
    (b : Basis (Fin 3) ℂ CPV)
    (L : CPV →ₗ[ℂ] ℂ) (P : PP1)
    (hP : ∀ v, eval v P = L v)
    (h0 : L (b 0) = 0) (h1 : L (b 1) = 0) (h2 : L (b 2) = 1) :
    bPC b P = X 2 := by
  let : Infinite ℂ := Infinite.of_injective (fun n : ℕ => (n : ℂ)) Nat.cast_injective
  apply MvPolynomial.funext
  intro v
  rw [bPCe, hP, eval_X]
  rw [← abtc L b h0 h1 h2]
  change b.equivFun (b.equivFun.symm v) 2 = v 2
  rw [LinearEquiv.apply_symm_apply]
end Nagata.W01
end
end
section
noncomputable section
open Module MvPolynomial
namespace Nagata.W01
theorem ehln
    (P : PP1) (hP : P.IsHomogeneous 1) (hne : P ≠ 0)
    (p₀ p₁ p₂ : Projectivization ℂ CPV)
    (h01 : p₀ ≠ p₁) (h20 : p₂ ≠ p₀) (h21 : p₂ ≠ p₁)
    (h0 : eval p₀.rep P = 0) (h1 : eval p₁.rep P = 0) (h2 : eval p₂.rep P = 0) :
    ∃ (b : Basis (Fin 3) ℂ CPV) (a c : ℂ),
      b 0 = p₀.rep ∧ b 1 = p₁.rep ∧ a ≠ 0 ∧ c ≠ 0 ∧
      b.equivFun p₀.rep = ![1, 0, 0] ∧ b.equivFun p₁.rep = ![0, 1, 0] ∧
      b.equivFun p₂.rep = ![a, c, 0] ∧ bPC b P = X 2 := by
  let L := Nagata.Workers.W14.hLM P
  have hL : L ≠ 0 := Nagata.Workers.W14.hLMnz P hP hne
  have hLeval : ∀ v, L v = eval v P :=
    Nagata.Workers.W14.hLMa P hP
  obtain ⟨b, a, c, hb0, hb1, hb2, ha, hc, hp0, hp1, hp2⟩ :=
    etpzc L hL p₀ p₁ p₂ h01 h20 h21
      ((hLeval _).trans h0) ((hLeval _).trans h1) ((hLeval _).trans h2)
  refine ⟨b, a, c, hb0, hb1, ha, hc, hp0, hp1, hp2, ?_⟩
  apply bPClF b L P (fun v => (hLeval v).symm)
  · rw [hb0, hLeval, h0]
  · rw [hb1, hLeval, h1]
  · exact hb2
end Nagata.W01
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W14
theorem fpe {K ι : Type*} [Field K] [Fintype ι]
    (P : ι → Polynomial K) (hP : ∀ i, (P i).eval 0 ≠ 0) :
    ∃ E : Finset K, 0 ∉ E ∧ ∀ s ∉ E, ∀ i, (P i).eval s ≠ 0 := by
  classical
  have hne : ∀ i, P i ≠ 0 := by
    intro i hi
    exact hP i (by simp [hi])
  let E : Finset K := Finset.univ.biUnion (fun i => (P i).roots.toFinset)
  have hmem : ∀ s, s ∈ E ↔ ∃ i, (P i).eval s = 0 := by
    intro s
    constructor
    · intro hs
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hs
      exact ⟨i, (Polynomial.mem_roots (hne i)).mp (Multiset.mem_toFinset.mp hi)⟩
    · rintro ⟨i, hi⟩
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
        Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (hne i)).mpr hi)⟩
  refine ⟨E, ?_, ?_⟩
  · intro hz
    obtain ⟨i, hi⟩ := (hmem 0).1 hz
    exact hP i hi
  · intro s hs i hi
    exact hs ((hmem s).2 ⟨i, hi⟩)
end Nagata.Workers.W14
end
end
section
noncomputable section
namespace Nagata.Workers.W14
def eM {K : Type*} [Field K] {r n : ℕ}
    (P : Fin r → Fin n → Polynomial K) (s : K) (i : Fin r) : Fin n → K :=
  fun c => (P i c).eval s
theorem pmsc {K : Type*} [Field K] {r n : ℕ}
    (P : Fin r → Fin n → Polynomial K)
    (hzero : ∀ i, eM P 0 i ≠ 0)
    (hsep : ∀ i j, i ≠ j → ∃ a b,
      eM P 0 i a * eM P 0 j b -
        eM P 0 i b * eM P 0 j a ≠ 0) :
    ∃ E : Finset K, 0 ∉ E ∧
      (∀ s ∉ E, ∀ i, eM P s i ≠ 0) ∧
      ∀ s ∉ E, ∀ i j, i ≠ j → ∃ a b,
        eM P s i a * eM P s j b -
          eM P s i b * eM P s j a ≠ 0 := by
  classical
  have hcoord : ∀ i, ∃ c, eM P 0 i c ≠ 0 := by
    intro i
    by_contra hn
    apply hzero i
    funext c
    exact Classical.not_not.mp (fun hc => hn ⟨c, hc⟩)
  choose c hc using hcoord
  let Pairs := {z : Fin r × Fin r // z.1 ≠ z.2}
  have hpairs : ∀ z : Pairs, ∃ a b,
      eM P 0 z.val.1 a * eM P 0 z.val.2 b -
        eM P 0 z.val.1 b * eM P 0 z.val.2 a ≠ 0 :=
    fun z => hsep z.val.1 z.val.2 z.property
  choose a b hab using hpairs
  let tests : Fin r ⊕ Pairs → Polynomial K := Sum.elim
    (fun i => P i (c i))
    (fun z => P z.val.1 (a z) * P z.val.2 (b z) -
      P z.val.1 (b z) * P z.val.2 (a z))
  have htests : ∀ z, (tests z).eval 0 ≠ 0 := by
    intro z
    cases z with
    | inl i => exact hc i
    | inr z => simpa [tests, eM] using hab z
  obtain ⟨E, hE0, hE⟩ := fpe tests htests
  refine ⟨E, hE0, ?_, ?_⟩
  · intro s hs i hz
    apply hE s hs (Sum.inl i)
    exact congrFun hz (c i)
  · intro s hs i j hne
    let z : Pairs := ⟨(i, j), hne⟩
    refine ⟨a z, b z, ?_⟩
    simpa [tests, eM, z] using hE s hs (Sum.inr z)
end Nagata.Workers.W14
end
end
section
noncomputable section
namespace Nagata.Workers.W14
theorem ppmc {K : Type*} [Field K] {r n : ℕ}
    (P : Fin r → Fin n → Polynomial K)
    (hzero : ∀ i, eM P 0 i ≠ 0)
    (hinj : Function.Injective
      (fun i => Projectivization.mk K (eM P 0 i) (hzero i))) :
    ∃ E : Finset K, 0 ∉ E ∧
      ∃ hvalid : ∀ s ∉ E, ∀ i, eM P s i ≠ 0,
        ∀ s (hs : s ∉ E), Function.Injective
          (fun i => Projectivization.mk K (eM P s i) (hvalid s hs i)) := by
  have hsep : ∀ i j, i ≠ j → ∃ a b,
      eM P 0 i a * eM P 0 j b -
        eM P 0 i b * eM P 0 j a ≠ 0 := by
    intro i j hne
    exact emnzo _ _ (hzero i) (hzero j)
      (fun he => hne (hinj he))
  obtain ⟨E, hE0, hvalid, hseparated⟩ :=
    pmsc P hzero hsep
  refine ⟨E, hE0, hvalid, ?_⟩
  intro s hs i j hij
  by_contra hne
  obtain ⟨a, b, hm⟩ := hseparated s hs i j hne
  exact pnomn (eM P s i)
    (eM P s j) (hvalid s hs i) (hvalid s hs j) a b hm hij
end Nagata.Workers.W14
end
end
section
noncomputable section
namespace Nagata.Workers.W14
open scoped BigOperators
 theorem pps {K : Type*} [Field K]
    (f : Fin 3 → MvPolynomial (Fin 2) K) (Q : MvPolynomial (Fin 3) K) (j : Fin 2) :
    MvPolynomial.pderiv j (MvPolynomial.eval₂ MvPolynomial.C f Q) =
      ∑ i : Fin 3, MvPolynomial.eval₂ MvPolynomial.C f (MvPolynomial.pderiv i Q) *
        MvPolynomial.pderiv j (f i) := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ =>
    simp only [MvPolynomial.eval₂_add, map_add, hP,hQ, add_mul, Finset.sum_add_distrib]
  | mul_X P k hP =>
    fin_cases k <;> simp_all [Pi.single_apply,
      Fin.sum_univ_succ] <;> ring
 theorem epsez {K : Type*} [Field K]
    (f : Fin 3 → MvPolynomial (Fin 2) K) (Q : MvPolynomial (Fin 3) K)
    (v : Fin 2 → K) (j : Fin 2)
    (hsing : ∀ i, MvPolynomial.eval (fun k => MvPolynomial.eval v (f k))
      (MvPolynomial.pderiv i Q) = 0) :
    MvPolynomial.eval v (MvPolynomial.pderiv j
      (MvPolynomial.eval₂ MvPolynomial.C f Q)) = 0 := by
  rw [pps,map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_mul]
  have hi : MvPolynomial.eval v (MvPolynomial.eval₂ MvPolynomial.C f
      (MvPolynomial.pderiv i Q)) = 0 := by
    change MvPolynomial.eval v ((MvPolynomial.eval₂Hom MvPolynomial.C f) _) = 0
    rw [MvPolynomial.map_eval₂Hom]
    have hC : (MvPolynomial.eval v).comp MvPolynomial.C = RingHom.id K := by
      ext c
      simp
    rw [hC]
    exact hsing i
  rw [hi,zero_mul]
end Nagata.Workers.W14
end
end
section
noncomputable section
namespace Nagata.Workers.W14
open Nagata.PG
def cPR {r : ℕ} (c : Fin r → Fin 3)
    (p : Fin r × Fin 2 → Polynomial ℂ) : Fin r → Fin 3 → Polynomial ℂ :=
  fun i => (c i).insertNth 1 (fun j => p (i, j))
theorem ecPR {r : ℕ} (c : Fin r → Fin 3)
    (p : Fin r × Fin 2 → Polynomial ℂ) (s : ℂ) (i : Fin r) :
    eM (cPR c p) s i =
      cV (c i) (fun j => (p (i, j)).eval s) := by
  funext j
  by_cases hj : j = c i
  · subst j
    simp [eM, cPR, cV]
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    simp [eM, cPR, cV]
theorem cpmc {r : ℕ} (c : Fin r → Fin 3)
    (p : Fin r × Fin 2 → Polynomial ℂ)
    (hbase : Function.Injective
      (cCE c (fun ij => (p ij).eval 0))) :
    ∃ E : Finset ℂ, 0 ∉ E ∧ ∀ s ∉ E, Function.Injective
      (cCE c (fun ij => (p ij).eval s)) := by
  let P := cPR c p
  have hzero : ∀ i, eM P 0 i ≠ 0 := by
    intro i
    rw [ecPR]
    exact cVnz _ _
  have hinj : Function.Injective
      (fun i => Projectivization.mk ℂ (eM P 0 i) (hzero i)) := by
    unfold cCE cP at hbase
    simpa only [P, ecPR] using hbase
  obtain ⟨E, hE0, hvalid, hdistinct⟩ := ppmc P hzero hinj
  refine ⟨E, hE0, ?_⟩
  intro s hs
  unfold cCE cP
  simpa only [P, ecPR] using hdistinct s hs
theorem odCom {F : MvPolynomial (Fin 3) ℂ}
    (c : Fin 3) (z : Fin 2 → ℂ) (m : ℕ)
    (h : mAL F (cP c z) m) :
    Nagata.AM.oAL z m (Nagata.W27.dCH c F) := by
  have hchart := h c (cPcnz c z)
  have htwo := (oALcD c (cP c z) F m).2 hchart
  rw [cCcP, cDeei] at htwo
  exact htwo
end Nagata.Workers.W14
end
end
section
noncomputable section
namespace Nagata.Workers.W14
open Module
open scoped BigOperators
 theorem cLRbC (b : Basis (Fin 3) ℂ (Fin 3 → ℂ))
    (Q : MvPolynomial (Fin 3) ℂ) :
    cLR (Nagata.W01.bPC b Q) =
      MvPolynomial.eval₂ MvPolynomial.C
        (fun i => MvPolynomial.C (b 0 i) * MvPolynomial.X 0 +
          MvPolynomial.C (b 1 i) * MvPolynomial.X 1) Q := by
  have h : cLR.comp (Nagata.W01.bPC b).toRingHom =
      MvPolynomial.eval₂Hom MvPolynomial.C
        (fun i => MvPolynomial.C (b 0 i) * MvPolynomial.X 0 +
          MvPolynomial.C (b 1 i) * MvPolynomial.X 1) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [cLR, Nagata.W01.bPCee]
    · intro i
      simp [Nagata.W01.bPCX, cLR,
        Fin.sum_univ_succ]
  exact RingHom.congr_fun h Q
 theorem blpzo (b : Basis (Fin 3) ℂ (Fin 3 → ℂ))
    (Q : MvPolynomial (Fin 3) ℂ)
    (hsing : ∀ i, MvPolynomial.eval (b 0) (MvPolynomial.pderiv i Q) = 0) :
    MvPolynomial.eval ![1,0] (MvPolynomial.pderiv 1
      (cLR (Nagata.W01.bPC b Q))) = 0 := by
  rw [cLRbC]
  apply epsez
  intro i
  simpa using hsing i
end Nagata.Workers.W14
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.Workers.W14
theorem msp {r d s : ℕ} (hr : 0 < r) (hd : 0 < d)
    (h : (d : ℝ) * Real.sqrt r ≤ s) : 0 < s := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hs' : (0 : ℝ) < s :=
    lt_of_lt_of_le (mul_pos hd' (Real.sqrt_pos.2 hr')) h
  exact_mod_cast hs'
theorem srl {r d s : ℕ} (hs : 0 < s)
    (h : (d : ℝ) * Real.sqrt r ≤ s) :
    (r : ℝ) * d / s ≤ Real.sqrt r := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  apply (div_le_iff₀ hs').2
  calc
    (r : ℝ) * d = Real.sqrt r * ((d : ℝ) * Real.sqrt r) := by
      calc
        (r : ℝ) * d = (d : ℝ) * (Real.sqrt r * Real.sqrt r) := by
          rw [Real.mul_self_sqrt (Nat.cast_nonneg r)]
          exact mul_comm _ _
        _ = _ := by ac_rfl
    _ ≤ Real.sqrt r * s := mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)
theorem fre {r d s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    ((r.factorial * d : ℕ) : ℝ) / (((r - 1).factorial * s : ℕ) : ℝ) =
      (r : ℝ) * d / s := by
  have hf : ((r - 1).factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero (r - 1))
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [← Nat.mul_factorial_pred hr.ne']
  push_cast
  apply (div_eq_div_iff (mul_ne_zero hf hs') hs').2
  simp only [mul_assoc, mul_comm, mul_left_comm]
theorem fs {r d s : ℕ} (hr : 0 < r) (hd : 0 < d)
    (h : (d : ℝ) * Real.sqrt r ≤ s) :
    0 < r.factorial * d ∧ 0 < (r - 1).factorial * s ∧
      ((r.factorial * d : ℕ) : ℝ) / (((r - 1).factorial * s : ℕ) : ℝ) ≤
        Real.sqrt r := by
  have hs := msp hr hd h
  refine ⟨Nat.mul_pos (Nat.factorial_pos _) hd,
    Nat.mul_pos (Nat.factorial_pos _) hs, ?_⟩
  rw [fre hr hs]
  exact srl hs h
end Nagata.Workers.W14
end
section
namespace Nagata.Workers.W14
theorem rnson (r d m : ℕ) (hr : ¬ IsSquare r) :
    (d : ℝ) / m ≠ Real.sqrt r := by
  intro heq
  apply hr
  apply Rat.isSquare_natCast_iff.mp
  refine ⟨(d : ℚ) / m, ?_⟩
  apply Rat.cast_injective (α := ℝ)
  push_cast
  rw [heq]
  exact (Real.mul_self_sqrt (Nat.cast_nonneg r)).symm
theorem rlson {r d m : ℕ} (hr : ¬ IsSquare r)
    (h : (d : ℝ) / m ≤ Real.sqrt r) : (d : ℝ) / m < Real.sqrt r :=
  lt_of_le_of_ne h (rnson r d m hr)
end Nagata.Workers.W14
end
end OAI
end
section
namespace OAI
section
namespace Nagata.Workers.W25
abbrev II (r : ℕ) := {d : ℕ // 0 < d} × (Fin r → ℕ)
instance incidenceIndex_countable (r : ℕ) : Countable (II r) := by
  infer_instance
end Nagata.Workers.W25
end
section
noncomputable section
namespace Nagata.Workers.W25
open Nagata.PG
theorem eneop {r : ℕ}
    (S : Set (ODP r)) (hclosed : ICZC S)
    (hproper : S ≠ Set.univ) :
    ∃ F : ME r, F.polynomial ≠ 0 ∧
      ∀ P ∈ S, eV F P.val := by
  classical
  obtain ⟨T, ⟨E, hE⟩, hST⟩ := hclosed
  have hex : ∃ P : ODP r, P ∉ S := by
    by_contra h
    apply hproper
    ext P
    simp only [Set.mem_univ, iff_true]
    by_contra hp
    exact h ⟨P, hp⟩
  obtain ⟨P, hP⟩ := hex
  have hnot : ¬ ∀ F ∈ E, eV F P.val := by
    intro h
    exact hP ((hST P).mpr ((hE P.val).mpr h))
  push Not at hnot
  obtain ⟨F, hFE, hF⟩ := hnot
  refine ⟨F, ?_, fun Q hQ => (hE Q.val).mp ((hST Q).mp hQ) F hFE⟩
  intro hzero
  apply hF
  intro v hv hrep
  simp [hzero]
end Nagata.Workers.W25
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W13
open scoped BigOperators
theorem psi {α : Type*} [Fintype α] [DecidableEq α]
    (m : α → ℕ) (i j : α) :
    (∑ σ : Equiv.Perm α, m (σ i)) = ∑ σ : Equiv.Perm α, m (σ j) := by
  apply Fintype.sum_equiv (Equiv.mulRight (Equiv.swap i j))
  intro σ
  simp [Equiv.Perm.mul_apply]
theorem cmps {α : Type*} [Fintype α] [DecidableEq α]
    (m : α → ℕ) (i : α) :
    Fintype.card α * (∑ σ : Equiv.Perm α, m (σ i)) =
      (Fintype.card α).factorial * ∑ j, m j := by
  calc
    Fintype.card α * (∑ σ : Equiv.Perm α, m (σ i)) =
        ∑ j : α, ∑ σ : Equiv.Perm α, m (σ j) := by
      simp_rw [← psi m i]
      simp
    _ = ∑ σ : Equiv.Perm α, ∑ j : α, m (σ j) := Finset.sum_comm
    _ = ∑ _σ : Equiv.Perm α, ∑ j : α, m j := by
      apply Finset.sum_congr rfl
      intro σ _
      exact Equiv.sum_comp σ m
    _ = (Fintype.card α).factorial * ∑ j, m j := by
      simp [Fintype.card_perm]
theorem psm {r : ℕ} (hr : 0 < r)
    (m : Fin r → ℕ) (i : Fin r) :
    (∑ σ : Equiv.Perm (Fin r), m (σ i)) =
      (r - 1).factorial * ∑ j, m j := by
  apply Nat.eq_of_mul_eq_mul_left hr
  have h := cmps m i
  simp only [Fintype.card_fin] at h
  have hfac := Nat.factorial_succ (r - 1)
  rw [Nat.sub_add_cancel hr] at hfac
  rw [h, ← Nat.mul_assoc, ← hfac]
end Nagata.W13
end
section
noncomputable section
namespace Nagata.W13
open PG
open scoped BigOperators
def US (r d : ℕ) (m : Fin r → ℕ) : Prop :=
  ∀ p : ODP r,
    ∃ F : MvPolynomial (Fin 3) ℂ,
      F ≠ 0 ∧ F.IsHomogeneous d ∧
      ∀ i, mAL F (p.val i) (m i)
theorem mALp1 {ι : Type*} (s : Finset ι)
    (p : PP) (m : ι → ℕ) (F : ι → MvPolynomial (Fin 3) ℂ)
    (h : ∀ i ∈ s, mAL (F i) p (m i)) :
    mAL (∏ i ∈ s, F i) p (∑ i ∈ s, m i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using mALz (1 : MvPolynomial (Fin 3) ℂ) p
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, Finset.prod_insert ha]
      exact mALm (h a (Finset.mem_insert_self a s))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
theorem uSp1 {r d : ℕ} {m : Fin r → ℕ}
    (h : US r d m) (σ : Equiv.Perm (Fin r)) :
    US r d (fun i => m (σ i)) := by
  intro p
  obtain ⟨F, hne, hhom, hm⟩ := h
    ⟨fun j => p.val (σ.symm j), p.property.comp σ.symm.injective⟩
  refine ⟨F, hne, hhom, ?_⟩
  intro i
  simpa using hm (σ i)
theorem uSs {r d : ℕ} (hr : 0 < r)
    {m : Fin r → ℕ} (h : US r d m) :
    US r (r.factorial * d)
      (fun _ => (r - 1).factorial * ∑ i, m i) := by
  classical
  intro p
  have hs : ∀ σ : Equiv.Perm (Fin r),
      ∃ F : MvPolynomial (Fin 3) ℂ,
        F ≠ 0 ∧ F.IsHomogeneous d ∧
          ∀ i, mAL F (p.val i) (m (σ i)) :=
    fun σ => uSp1 h σ p
  let F := fun σ => Classical.choose (hs σ)
  have hne : ∀ σ, F σ ≠ 0 := fun σ => (Classical.choose_spec (hs σ)).1
  have hhom : ∀ σ, (F σ).IsHomogeneous d :=
    fun σ => (Classical.choose_spec (hs σ)).2.1
  have hm : ∀ σ i, mAL (F σ) (p.val i) (m (σ i)) :=
    fun σ => (Classical.choose_spec (hs σ)).2.2
  have hp := W16.fpf Finset.univ F (fun _ => d)
    (fun σ _ => hhom σ) (fun σ _ => hne σ)
  refine ⟨∏ σ, F σ, hp.1, ?_, ?_⟩
  · simpa [Fintype.card_perm] using hp.2.1
  · intro i
    have hi := mALp1 Finset.univ (p.val i)
      (fun σ => m (σ i)) F (fun σ _ => hm σ i)
    rw [psm hr m i] at hi
    exact hi
theorem uSp {r d : ℕ} {m : Fin r → ℕ}
    (h : US r d m) (N : ℕ) :
    US r (d * N) (fun i => m i * N) := by
  intro p
  obtain ⟨F, hne, hhom, hm⟩ := h p
  exact ⟨F ^ N, pow_ne_zero N hne, hhom.pow N,
    fun i => mALp (hm i) N⟩
end Nagata.W13
end
end
section
noncomputable section
namespace Nagata.W13
open PG
open scoped BigOperators
def sL1 (r : ℕ) (i : Workers.W25.II r) :
    Set (ODP r) :=
  {p | ∃ F : MvPolynomial (Fin 3) ℂ,
    F ≠ 0 ∧ F.IsHomogeneous i.1.val ∧
      ∀ j, mAL F (p.val j) (i.2 j)}
end Nagata.W13
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W14
def pM {K σ ρ κ : Type*} [CommRing K]
    (A : Matrix ρ κ (MvPolynomial σ K)) (p : σ → Polynomial K) :
    Matrix ρ κ (Polynomial K) :=
  fun row col => MvPolynomial.eval₂ Polynomial.C p (A row col)
theorem spM {K σ ρ κ : Type*} [CommRing K]
    (A : Matrix ρ κ (MvPolynomial σ K)) (p : σ → Polynomial K) (s : K) :
    (pM A p).map (Polynomial.evalRingHom s) =
      A.map (MvPolynomial.eval (fun j => (p j).eval s)) := by
  have hc : (Polynomial.evalRingHom s).comp (Polynomial.C : K →+* Polynomial K) =
      RingHom.id K := by
    ext x
    simp
  funext row col
  change (Polynomial.evalRingHom s)
      (MvPolynomial.eval₂Hom Polynomial.C p (A row col)) = _
  rw [MvPolynomial.map_eval₂Hom, hc]
  rfl
theorem pMmV {K σ ρ κ : Type*} [CommRing K] [Fintype κ]
    (A : Matrix ρ κ (MvPolynomial σ K)) (p : σ → Polynomial K)
    (s : K) (v : κ → K) :
    ((pM A p).map (Polynomial.evalRingHom s)).mulVec v =
      Nagata.W27.cLM A (fun j => (p j).eval s) v := by
  rw [spM]
  rfl
theorem nkope
    {K σ ρ κ : Type*} [Field K] [Infinite K]
    [Fintype κ] [Fintype ρ] [DecidableEq κ] [DecidableEq ρ]
    (A : Matrix ρ κ (MvPolynomial σ K)) (p : σ → Polynomial K) (E : Finset K)
    (hkernel : ∀ s ∉ E, ∃ v : κ → K, v ≠ 0 ∧
      Nagata.W27.cLM A (fun j => (p j).eval s) v = 0) :
    ∃ q : κ → Polynomial K, (∃ i, (q i).coeff 0 ≠ 0) ∧
      (pM A p).mulVec q = 0 := by
  apply Nagata.W18.nkogs (pM A p) E
  intro s hs
  obtain ⟨v, hv, heq⟩ := hkernel s hs
  exact ⟨v, hv, by rw [pMmV]; exact heq⟩
end Nagata.Workers.W14
end
end
section
noncomputable section
namespace Nagata.Workers.W14
open Nagata.PG
theorem uSgck {r d : ℕ} {m : Fin r → ℕ}
    (hU : Nagata.W13.US r d m)
    (c : Fin r → Fin 3) (p : Fin r × Fin 2 → Polynomial ℂ)
    (hbase : Function.Injective
      (cCE c (fun ij => (p ij).eval 0))) :
    ∃ E : Finset ℂ, 0 ∉ E ∧ ∀ s ∉ E,
      ∃ v : Nagata.W27.HM d → ℂ, v ≠ 0 ∧
        Nagata.W27.cLM (Nagata.W27.cPJM c d m)
          (fun ij => (p ij).eval s) v = 0 := by
  obtain ⟨E, hE0, hE⟩ := cpmc c p hbase
  refine ⟨E, hE0, ?_⟩
  intro s hs
  obtain ⟨F, hF, hhom, hmult⟩ := hU
    ⟨cCE c (fun ij => (p ij).eval s), hE s hs⟩
  apply (Nagata.W27.enfic c d m
    (fun ij => (p ij).eval s)).1
  refine ⟨⟨F, hhom⟩, hF, ?_⟩
  intro i
  exact odCom (c i) (fun j => (p (i, j)).eval s) (m i) (hmult i)
theorem uSnpf {r d : ℕ} {m : Fin r → ℕ}
    (hU : Nagata.W13.US r d m)
    (c : Fin r → Fin 3) (p : Fin r × Fin 2 → Polynomial ℂ)
    (hbase : Function.Injective
      (cCE c (fun ij => (p ij).eval 0))) :
    ∃ q : Nagata.W27.HM d → Polynomial ℂ,
      (∃ i, (q i).coeff 0 ≠ 0) ∧
      (pM (Nagata.W27.cPJM c d m) p).mulVec q = 0 := by
  classical
  obtain ⟨E, _, hE⟩ := uSgck hU c p hbase
  exact nkope
    (Nagata.W27.cPJM c d m) p E hE
end Nagata.Workers.W14
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.Workers.W17
open Nagata.W27 Nagata.Workers.W14 Nagata.PG
theorem iPFco {r d : ℕ} (m : Fin r → ℕ)
    (c : Fin r → Fin 3) (p : Fin r × Fin 2 → Polynomial ℂ)
    (q : HM d → Polynomial ℂ)
    (hq : (pM (cPJM c d m) p).mulVec q = 0)
    (s : ℂ) :
    ∀ i, Nagata.AM.oAL (fun j => (p (i,j)).eval s) (m i)
      (dCH (c i) ((iPF d q).eval (MvPolynomial.C s))) := by
  have hspec := Nagata.W18.spk
    (pM (cPJM c d m) p) q hq s
  rw [pMmV] at hspec
  let F := (hC1 (R := ℂ) d).symm (fun ν => (q ν).eval s)
  have hcoord : hC1 d F = fun ν => (q ν).eval s :=
    (hC1 d).apply_symm_apply _
  have horders := (coik c d m (fun ij => (p ij).eval s) F).mpr
    (by rw [hcoord]; exact hspec)
  simpa only [eiPFe, F] using horders
theorem uSpf {r d : ℕ} {m : Fin r → ℕ}
    (hU : Nagata.W13.US r d m)
    (c : Fin r → Fin 3) (p : Fin r × Fin 2 → Polynomial ℂ)
    (hbase : Function.Injective
      (cCE c (fun ij => (p ij).eval 0))) :
    ∃ S : Polynomial (MvPolynomial (Fin 3) ℂ),
      S.coeff 0 ≠ 0 ∧ (∀ α, (S.coeff α).IsHomogeneous d) ∧
      ∀ s i, Nagata.AM.oAL (fun j => (p (i,j)).eval s) (m i)
        (dCH (c i) (S.eval (MvPolynomial.C s))) := by
  obtain ⟨q, hzero, hq⟩ := uSnpf hU c p hbase
  exact ⟨iPF d q, iPFcn d q hzero,
    iPFh d q, iPFco m c p q hq⟩
end Nagata.Workers.W17
end
section
namespace Nagata.Workers.W17
open scoped BigOperators
open Nagata.PG
theorem uSdbn {r d : ℕ} {m : Fin r → ℕ}
    (hU : Nagata.W13.US r d m)
    (c : Fin r → Fin 3) (p : Fin r × Fin 2 → Polynomial ℂ)
    (hbase : Function.Injective
      (cCE c (fun ij => (p ij).eval 0)))
    (G : MvPolynomial (Fin 3) ℂ) (k : ℕ)
    (hG : G.IsHomogeneous k) (hunit : ¬IsUnit G) (hk : 0 < k) :
    ∃ (I : Finset ℕ) (j : ℕ → ℕ) (T : ℕ → MvPolynomial (Fin 3) ℂ) (u : ℕ),
      (∀ α ∈ I, ¬G ∣ T α) ∧
      (∀ α ∈ I, j α ≤ d / k ∧ (T α).IsHomogeneous (d - k * j α)) ∧
      (∀ α ∈ I, u ≤ α + j α) ∧ u ≤ d / k ∧
      (I.filter (fun α => α + j α = u)).Nonempty ∧
      ((lNP (I.filter (fun α => α + j α = u)) j T).map
        (Ideal.Quotient.mk (Ideal.span ({G} : Set (MvPolynomial (Fin 3) ℂ))))) ≠ 0 ∧
      ∀ s i, Nagata.AM.oAL (fun z => (p (i,z)).eval s) (m i)
        (Nagata.Workers.W28.fPF I j
          (fun α => Nagata.W27.dCH (c i) (T α))
          (Nagata.W27.dCH (c i) G) s) := by
  classical
  obtain ⟨S, hzero, hcoeff, horders⟩ := uSpf hU c p hbase
  obtain ⟨j, T, u, hfactor, hnot, hdeg, hmin, hu, hsel, hinit⟩ :=
    edbpi S G d k hcoeff hG hunit hk hzero
  refine ⟨S.support, j, T, u, hnot, hdeg, hmin, hu, hsel, ?_, ?_⟩
  · simpa only [mlNP] using hinit
  · intro s i
    rw [← dCff S G j T hfactor (c i) s]
    exact horders s i
end Nagata.Workers.W17
end
section
noncomputable section
namespace Nagata.Workers.W17
open Nagata.Workers.W28 Nagata.PG
def pC (p : CP) (a : Fin 2) : ℂ := if a = 0 then p.1 else p.2
def aCM1 (p V : CP) (a : Fin 2) : Polynomial ℂ :=
  Polynomial.C (pC p a) + Polynomial.X * Polynomial.C (pC V a)
@[simp] theorem aCMe (p V : CP) (a : Fin 2) (s : ℂ) :
    (aCM1 p V a).eval s = pC (p+s • V) a := by
  simp only [aCM1, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_X]
  dsimp only [pC]
  split_ifs <;> simp
theorem cMbi {r : ℕ}
    (c : Fin r → Fin 3) (p V : Fin r → CP)
    (hbase : Function.Injective (fun b => cP (c b) (pC (p b)))) :
    Function.Injective (cCE c
      (fun ba => (aCM1 (p ba.1) (V ba.1) ba.2).eval 0)) := by
  change Function.Injective (fun index => cP (c index)
    (fun coordinate => (aCM1 (p index) (V index) coordinate).eval 0))
  simpa only [aCMe, zero_smul, add_zero] using hbase
end Nagata.Workers.W17
end
end
section
noncomputable section
namespace Nagata.Workers.W17
open scoped Topology BigOperators
open Nagata.Workers.W28 Nagata.PG
theorem uSscn {r d : ℕ} {m : Fin r → ℕ}
    (hU : Nagata.W13.US r d m)
    (G : MvPolynomial (Fin 3) ℂ) (k : ℕ)
    (hG : G.IsHomogeneous k) (hk : 0 < k)
    (X : Fin 3 → ℂ → ℂ) (chart : Fin r → Fin 3) (z w : Fin r → ℂ)
    (hz : ∀ b, z b ≠ 0) (hc : ∀ b, X (chart b) (z b) ≠ 0)
    (hX : ∀ b a, AnalyticAt ℂ (X a) (z b))
    (hzero : ∀ t : ℂ, t ≠ 0 → MvPolynomial.eval (fun a => X a t) G = 0)
    (hbase : Function.Injective (fun b => cP (chart b)
      (pC (nCP X (chart b) (z b)))))
    (hdifferential : ∀ b, pG (Nagata.W27.dCH (chart b) G)
      (nCP X (chart b) (z b)) ≠ 0) :
    ∃ F : Polynomial (MvPolynomial (Fin 3) ℂ),
      (∀ n, (F.coeff n).IsHomogeneous (d-k*n)) ∧
      (∀ n, F.coeff n ≠ 0 → k*n ≤ d) ∧
      F.map (Ideal.Quotient.mk (Ideal.span ({G} : Set (MvPolynomial (Fin 3) ℂ)))) ≠ 0 ∧
      ∀ b, HAOAL (𝕜 := ℂ)
        (Nagata.CS.aNS1 X F)
        (z b,w b) (m b) := by
  classical
  let point : Fin r → CP := fun b => nCP X (chart b) (z b)
  have hvelocity : ∀ b, ∃ V : CP,
      pG (Nagata.W27.dCH (chart b) G) (point b) V =
        w b / X (chart b) (z b) ^ k := by
    intro b
    exact Nagata.W29.aPGs _ _
      ((pGnzi _ _).mp (hdifferential b)) _
  choose V hV using hvelocity
  let motion : Fin r × Fin 2 → Polynomial ℂ := fun ba =>
    aCM1 (point ba.1) (V ba.1) ba.2
  have hb := cMbi chart point V hbase
  obtain ⟨I,j,T,u,hnot,hdeg,hmin,hu,hsel,hne,horders⟩ :=
    uSdbn hU chart motion hb G k hG
      (phniU hG hk) hk
  let selected := I.filter (fun α => α+j α=u)
  let F := lNP selected j T
  have hhom : ∀ α ∈ selected, (T α).IsHomogeneous (d-k*j α) :=
    fun α hα => (hdeg α (Finset.mem_filter.mp hα).1).2
  have hbound : ∀ α ∈ selected, j α ≤ d/k :=
    fun α hα => (hdeg α (Finset.mem_filter.mp hα).1).1
  refine ⟨F, hclNP selected j T d k hhom, ?_, hne, ?_⟩
  · intro n hn
    have hb := nclNP selected j T (d/k) n hbound hn
    have hh := (Nat.le_div_iff_mul_le hk).mp hb
    simpa only [Nat.mul_comm] using hh
  · intro b
    have hcurve : ∀ᶠ t in 𝓝 (z b), MvPolynomial.eval (fun a => X a t) G = 0 :=
      (eventually_ne_nhds (hz b)).mono fun t ht => hzero t ht
    have ho : ∀ᶠ s : ℂ in 𝓝 0, s ∉ (∅ : Finset ℂ) →
        Nagata.AM.oAL (pC (point b+s • V b)) (m b)
          (fPF I j (fun α => Nagata.W27.dCH (chart b) (T α))
            (Nagata.W27.dCH (chart b) G) s) := by
      exact Filter.Eventually.of_forall fun s _ => by
        simpa only [motion, aCMe] using horders s b
    have h := hnson I j T u hmin d k
      (fun α hα => (hdeg α hα).2)
      (fun α hα => by
        have hh := (Nat.le_div_iff_mul_le hk).mp (hdeg α hα).1
        simpa only [Nat.mul_comm] using hh)
      G hG X (chart b) (z b) (w b) (hX b) (hc b) hcurve (hdifferential b) (V b) (hV b)
      ∅ (m b) ho
    apply h.congr
    exact Filter.Eventually.of_forall fun q => by
      simp [Nagata.CS.aNS1, F, lNP, selected,
        Polynomial.map_sum, Polynomial.eval_finsetSum, mul_comm]
end Nagata.Workers.W17
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.CS
theorem etc {τ L Q : ℂ}
    (hτ : τ ≠ 0) (hL : L ≠ 0) (hQ : Q ≠ 0) (d : ℤ) (m j : ℕ)
    (P : Nagata.W08.aS τ 9 Q)
    (f : Nagata.W08.aS τ (3 * (d - 3 * (j : ℤ)))
      (L ^ (d - 3 * (j : ℤ))))
    (hzero : j ≤ m → ∀ z ≠ 0, P.val z = 0 → deriv P.val z ≠ 0 ∧
      ((m - j : ℕ) : ℕ∞) ≤ analyticOrderAt f.val z) :
    ∃ g ∈ cS τ L Q d (m : ℤ) (j : ℤ) P.val,
      ∀ z ≠ 0, P.val z ^ m * g z = P.val z ^ j * f.val z := by
  by_cases hj : j ≤ m
  · have hjZ : (j : ℤ) ≤ (m : ℤ) := by exact_mod_cast hj
    have he : ((m : ℤ) - (j : ℤ)).toNat = m - j := by omega
    obtain ⟨g, hg, hf⟩ := elhc hτ hL hQ d (m : ℤ)
      (j : ℤ) hjZ P f (by simpa only [he] using hzero hj)
    refine ⟨g, hg, ?_⟩
    intro z hz
    rw [hf z hz, he, ← mul_assoc, ← pow_add]
    rw [Nat.add_sub_of_le hj]
  · have hjZ : (m : ℤ) < (j : ℤ) := by exact_mod_cast (lt_of_not_ge hj)
    have he : ((j : ℤ) - (m : ℤ)).toNat = j - m := by omega
    refine ⟨mP2 P.val (j - m) f.val, ?_, ?_⟩
    · apply (mcSs hjZ).mpr
      exact ⟨f.val, f.property, by rw [he]⟩
    · intro z hz
      change P.val z ^ m * (P.val z ^ (j - m) * f.val z) = P.val z ^ j * f.val z
      rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le (le_of_lt (lt_of_not_ge hj))]
theorem tcn {τ L Q : ℂ} (d : ℤ) (m j : ℕ)
    (P : Nagata.W08.aS τ 9 Q)
    (hPfin : ∀ z ≠ 0, analyticOrderAt P.val z ≠ ⊤)
    (f : Nagata.W08.aS τ (3 * (d - 3 * (j : ℤ)))
      (L ^ (d - 3 * (j : ℤ)))) (g : ℂ → ℂ)
    (hfactor : ∀ z ≠ 0, P.val z ^ m * g z = P.val z ^ j * f.val z)
    (hf : f ≠ 0) : g ≠ 0 := by
  intro hg
  apply hf
  apply mSi τ (L ^ (d - 3 * (j : ℤ)))
    (3 * (d - 3 * (j : ℤ))) P.val j
    (Nagata.W08.aSaON P) hPfin
  funext z
  change P.val z ^ j * f.val z = P.val z ^ j * 0
  by_cases hz : z = 0
  · subst z
    rw [f.property.1]
  · rw [← hfactor z hz, hg]
    simp
end Nagata.CS
end
section
namespace Nagata.CS
open scoped BigOperators
theorem etp {τ L Q : ℂ}
    (hτ : τ ≠ 0) (hL : L ≠ 0) (hQ : Q ≠ 0) (d : ℤ) (m : ℕ)
    (P : Nagata.W08.aS τ 9 Q)
    (hPsimple : ∀ z ≠ 0, P.val z = 0 → deriv P.val z ≠ 0)
    (F : Polynomial (ℂ → ℂ))
    (hbound : ∀ j : ℕ, (d / 3).toNat < j → F.coeff j = 0)
    (hsource : ∀ j : ℕ, F.coeff j ∈ Nagata.W08.aS τ
      (3 * (d - 3 * (j : ℤ))) (L ^ (d - 3 * (j : ℤ))))
    (hzero : ∀ j : ℕ, j ≤ (d / 3).toNat → j ≤ m → ∀ z ≠ 0,
      P.val z = 0 → ((m - j : ℕ) : ℕ∞) ≤ analyticOrderAt (F.coeff j) z) :
    ∃ G : pS τ L Q d (m : ℤ) P.val,
      (∀ j : ℕ, ∀ z ≠ 0, P.val z ^ m * G.val.coeff j z =
        P.val z ^ j * F.coeff j z) ∧ (F ≠ 0 → G ≠ 0) := by
  classical
  let N := (d / 3).toNat
  have hex : ∀ j : Fin (N + 1), ∃ g ∈ cS τ L Q d (m : ℤ) (j.val : ℤ) P.val,
      ∀ z ≠ 0, P.val z ^ m * g z = P.val z ^ j.val * F.coeff j.val z := by
    intro j
    exact etc hτ hL hQ d m j.val P
      ⟨F.coeff j.val, hsource j.val⟩ (fun hj z hz hPz =>
        ⟨hPsimple z hz hPz, hzero j.val (Nat.le_of_lt_succ j.isLt) hj z hz hPz⟩)
  choose g hg hfactor using hex
  let c : (j : Fin (N + 1)) → cS τ L Q d (m : ℤ) (j.val : ℤ) P.val :=
    fun j => ⟨g j, hg j⟩
  let e := Nagata.Workers.W10.pSC τ L Q d (m : ℤ) P.val
  let G := e.symm c
  have hcoeff (j : Fin (N + 1)) : G.val.coeff j.val = g j := by
    have hh := congrArg (fun v => (v j).val) (e.apply_symm_apply c)
    exact hh
  have hfact : ∀ j : ℕ, ∀ z ≠ 0, P.val z ^ m * G.val.coeff j z =
      P.val z ^ j * F.coeff j z := by
    intro j z hz
    by_cases hj : j ≤ N
    · let ji : Fin (N + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
      rw [hcoeff ji]
      exact hfactor ji z hz
    · have hj' : N < j := lt_of_not_ge hj
      rw [G.property.1 j hj', hbound j hj']
      simp
  refine ⟨G, hfact, ?_⟩
  intro hF hG
  apply hF
  apply Polynomial.ext
  intro j
  by_cases hj : j ≤ N
  · by_contra hfj
    let f : Nagata.W08.aS τ (3 * (d - 3 * (j : ℤ)))
        (L ^ (d - 3 * (j : ℤ))) := ⟨F.coeff j, hsource j⟩
    have hf : f ≠ 0 := by
      intro hf0
      apply hfj
      exact congrArg Subtype.val hf0
    have hPfin : ∀ z ≠ 0, analyticOrderAt P.val z ≠ ⊤ := by
      intro z hz
      have hp := Nagata.W08.aSaA P hz
      by_cases hPz : P.val z = 0
      · rw [hp.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hPz (hPsimple z hz hPz)]
        simp
      · rw [hp.analyticOrderAt_eq_zero.mpr hPz]
        simp
    have hg := tcn d m j P hPfin f (G.val.coeff j)
      (hfact j) hf
    apply hg
    have hGval := congrArg Subtype.val hG
    rw [hGval]
    rfl
  · exact hbound j (lt_of_not_ge hj)
theorem sEer (F : Polynomial (ℂ → ℂ)) (N : ℕ)
    (hbound : ∀ j, N < j → F.coeff j = 0) (z v : ℂ) :
    sE F z v = ∑ j ∈ Finset.range (N + 1), F.coeff j z * v ^ j := by
  apply Polynomial.sum_eq_of_subset
  · intro j
    simp
  · intro j hj
    apply Finset.mem_range.mpr
    have hne := Polynomial.mem_support_iff.mp hj
    by_contra h
    exact hne (hbound j (by omega))
theorem sEt (F G : Polynomial (ℂ → ℂ)) (N m : ℕ)
    (hF : ∀ j, N < j → F.coeff j = 0) (hG : ∀ j, N < j → G.coeff j = 0)
    (P : ℂ → ℂ) (z v : ℂ)
    (hfactor : ∀ j, P z ^ m * G.coeff j z = P z ^ j * F.coeff j z) :
    P z ^ m * sE G z v = sE F z (P z * v) := by
  rw [sEer G N hG, sEer F N hF,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← mul_assoc, hfactor j, mul_pow]
  ring
end Nagata.CS
end
section
namespace Nagata.CS
open scoped BigOperators
noncomputable def nTS {τ : ℂ} (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0)
    (a : Fin 9 → ℂ) (ha : ∀ i, a i ≠ 0) :
    Nagata.W08.aS τ 9 (∏ i, -a i) := by
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using
    Nagata.W08.mTS hτ hτ0 a ha
theorem emtp {τ L : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (hL : L ≠ 0)
    (a : Fin 9 → ℂ) (ha : ∀ i, a i ≠ 0)
    (hdisjoint : Pairwise (fun i j => ∀ k : ℤ, a i ≠ a j * τ ^ k))
    (d : ℤ) (m : ℕ) (F : Polynomial (ℂ → ℂ))
    (hbound : ∀ j : ℕ, (d / 3).toNat < j → F.coeff j = 0)
    (hsource : ∀ j : ℕ, F.coeff j ∈ Nagata.W08.aS τ
      (3 * (d - 3 * (j : ℤ))) (L ^ (d - 3 * (j : ℤ))))
    (hmarked : ∀ j : ℕ, j ≤ (d / 3).toNat → j ≤ m → ∀ i : Fin 9,
      ((m - j : ℕ) : ℕ∞) ≤ analyticOrderAt (F.coeff j) (a i)) :
    ∃ G : pS τ L (∏ i, -a i) d (m : ℤ)
        (nTS hτ hτ0 a ha).val,
      (∀ j : ℕ, ∀ z ≠ 0, (nTS hτ hτ0 a ha).val z ^ m *
        G.val.coeff j z = (nTS hτ hτ0 a ha).val z ^ j * F.coeff j z) ∧
      (F ≠ 0 → G ≠ 0) := by
  have hQ : (∏ i, -a i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => neg_ne_zero.mpr (ha i))
  refine etp hτ0 hL hQ d m
    (nTS hτ hτ0 a ha) ?_ F hbound hsource ?_
  · intro z hz hzero
    exact Nagata.W08.mTSzh hτ hτ0 a ha hdisjoint hz hzero
  · intro j hj hjm z hz hzero
    obtain ⟨i, k, rfl⟩ := (Nagata.W08.mTSzi hτ hτ0 a ha hz).mp hzero
    rw [aoo hτ0 (zpow_ne_zero _ hL)
      (⟨F.coeff j, hsource j⟩ : Nagata.W08.aS τ
        (3 * (d - 3 * (j : ℤ))) (L ^ (d - 3 * (j : ℤ)))) (ha i) k]
    exact hmarked j hj hjm i
end Nagata.CS
end
end OAI
end
section
namespace OAI
section
namespace Nagata.CS
open Nagata.Workers.W28 Filter Topology
theorem tpoi
    (F G : Polynomial (ℂ → ℂ)) (N m : ℕ)
    (hF : ∀ j, N < j → F.coeff j = 0) (hG : ∀ j, N < j → G.coeff j = 0)
    (P : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hP : AnalyticOnNhd ℂ P U) (hne : ∀ z ∈ U, P z ≠ 0)
    (hfactor : ∀ j, ∀ z ∈ U, P z ^ m * G.coeff j z = P z ^ j * F.coeff j z)
    (x : ℂ × ℂ) (hx : x.1 ∈ U) :
    HAOAL (𝕜 := ℂ) (fun y : ℂ × ℂ => sE G y.1 y.2) x m ↔
    HAOAL (𝕜 := ℂ) (fun y : ℂ × ℂ => sE F y.1 y.2)
      (x.1, P x.1 * x.2) m := by
  have he : (fun y : ℂ × ℂ => sE G y.1 y.2) =ᶠ[𝓝 x]
      (fun y : ℂ × ℂ => (P y.1 ^ m)⁻¹ * sE F y.1 (P y.1 * y.2)) := by
    filter_upwards [(hU.preimage continuous_fst).mem_nhds hx] with y hy
    have hs := sEt F G N m hF hG P y.1 y.2
      (fun j => hfactor j y.1 hy)
    rw [← hs, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero m (hne y.1 hy)), one_mul]
  have hc := Nagata.FCC.opbfs
    P U hU hP hne (fun y : ℂ × ℂ => sE F y.1 y.2) x hx m
  constructor
  · intro h
    exact hc.mp (h.congr he)
  · intro h
    exact (hc.mpr h).congr he.symm
end Nagata.CS
end
section
namespace Nagata.CS
open scoped BigOperators
open Nagata.Workers.W28
theorem nWonp {ι : Type*} {τ L : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (hL : L ≠ 0)
    (a : Fin 9 → ℂ) (ha : ∀ i, a i ≠ 0)
    (hdisjoint : Pairwise (fun i j => ∀ k : ℤ, a i ≠ a j * τ ^ k))
    (d : ℤ) (m : ℕ) (F : Polynomial (ℂ → ℂ)) (hneF : F ≠ 0)
    (hbound : ∀ j : ℕ, (d / 3).toNat < j → F.coeff j = 0)
    (hsource : ∀ j : ℕ, F.coeff j ∈ Nagata.W08.aS τ
      (3 * (d - 3 * (j : ℤ))) (L ^ (d - 3 * (j : ℤ))))
    (hmarked : ∀ j : ℕ, j ≤ (d / 3).toNat → j ≤ m → ∀ i : Fin 9,
      ((m - j : ℕ) : ℕ∞) ≤ analyticOrderAt (F.coeff j) (a i))
    (U : Set ℂ) (hU : IsOpen U) (hU0 : ∀ z ∈ U, z ≠ 0)
    (hUP : ∀ z ∈ U, (nTS hτ hτ0 a ha).val z ≠ 0)
    (p : ι → ℂ × ℂ) (hp : ∀ i, (p i).1 ∈ U)
    (hmoving : ∀ i, HAOAL (𝕜 := ℂ)
      (fun y : ℂ × ℂ => sE F y.1 y.2)
      ((p i).1, (nTS hτ hτ0 a ha).val (p i).1 * (p i).2) m) :
    ∃ G : pS τ L (∏ i, -a i) d (m : ℤ)
        (nTS hτ hτ0 a ha).val,
      G ≠ 0 ∧ ∀ i, HAOAL (𝕜 := ℂ)
        (fun y : ℂ × ℂ => sE G.val y.1 y.2) (p i) m := by
  obtain ⟨G, hfactor, hne⟩ := emtp hτ hτ0 hL a ha
    hdisjoint d m F hbound hsource hmarked
  refine ⟨G, hne hneF, ?_⟩
  intro i
  apply (tpoi F G.val ((d / 3).toNat) m hbound G.property.1
    (nTS hτ hτ0 a ha).val U hU
    (fun z hz => Nagata.W08.aSaA _ (hU0 z hz)) hUP
    (fun j z hz => hfactor j z (hU0 z hz)) (p i) (hp i)).mpr
  exact hmoving i
end Nagata.CS
end
section
namespace Nagata.CS
theorem nTSre {τ : ℝ} (hpos : 0 < τ) (hlt : τ < 1)
    (hτ : ‖(τ : ℂ)‖ < 1) (hτ0 : (τ : ℂ) ≠ 0) (ξ : Fin 9 → ℝ)
    (ha : ∀ i, ((τ ^ ξ i : ℝ) : ℂ) ≠ 0) :
    (nTS hτ hτ0 (fun i => ((τ ^ ξ i : ℝ) : ℂ)) ha).val =
      (Nagata.W22.rMS hpos hlt ξ).val := rfl
end Nagata.CS
end
section
namespace Nagata.CS
open Filter Topology
def sNL {τ γ : ℂ} {n : ℤ}
    (P : Nagata.W08.aS τ n γ) : Set ℂ := {z | z ≠ 0 ∧ P.val z ≠ 0}
theorem iOsNL {τ γ : ℂ} {n : ℤ}
    (P : Nagata.W08.aS τ n γ) : IsOpen (sNL P) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  exact (eventually_ne_nhds hz.1).and
    ((P.property.2.1 z hz.1).continuousAt.eventually_ne hz.2)
end Nagata.CS
end
end OAI
end
section
namespace OAI
section
namespace Nagata.CS
open scoped BigOperators
open Nagata.Workers.W28
theorem nWanp {ι : Type*} {τ L : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (hL : L ≠ 0)
    (a : Fin 9 → ℂ) (ha : ∀ i, a i ≠ 0)
    (hdisjoint : Pairwise (fun i j => ∀ k : ℤ, a i ≠ a j * τ ^ k))
    (d : ℤ) (m : ℕ) (F : Polynomial (ℂ → ℂ)) (hneF : F ≠ 0)
    (hbound : ∀ j : ℕ, (d / 3).toNat < j → F.coeff j = 0)
    (hsource : ∀ j : ℕ, F.coeff j ∈ Nagata.W08.aS τ
      (3 * (d - 3 * (j : ℤ))) (L ^ (d - 3 * (j : ℤ))))
    (hmarked : ∀ j : ℕ, j ≤ (d / 3).toNat → j ≤ m → ∀ i : Fin 9,
      ((m - j : ℕ) : ℕ∞) ≤ analyticOrderAt (F.coeff j) (a i))
    (p : ι → ℂ × ℂ) (hp0 : ∀ i, (p i).1 ≠ 0)
    (hpP : ∀ i, (nTS hτ hτ0 a ha).val (p i).1 ≠ 0)
    (hmoving : ∀ i, HAOAL (𝕜 := ℂ)
      (fun y : ℂ × ℂ => sE F y.1 y.2)
      ((p i).1, (nTS hτ hτ0 a ha).val (p i).1 * (p i).2) m) :
    ∃ G : pS τ L (∏ i, -a i) d (m : ℤ)
        (nTS hτ hτ0 a ha).val,
      G ≠ 0 ∧ ∀ i, HAOAL (𝕜 := ℂ)
        (fun y : ℂ × ℂ => sE G.val y.1 y.2) (p i) m := by
  exact nWonp hτ hτ0 hL a ha hdisjoint d m F hneF
    hbound hsource hmarked (sNL (nTS hτ hτ0 a ha))
    (iOsNL _) (fun _ hz => hz.1) (fun _ hz => hz.2)
    p (fun i => ⟨hp0 i, hpP i⟩) hmoving
end Nagata.CS
end
section
namespace Nagata.CS
open scoped BigOperators
open Nagata.Workers.W28
theorem nWonT {ι : Type*} {τ L : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (hL : L ≠ 0)
    (a : Fin 9 → ℂ) (ha : ∀ i, a i ≠ 0)
    (hdisjoint : Pairwise (fun i j => ∀ k : ℤ, a i ≠ a j * τ ^ k))
    (d : ℤ) (m : ℕ) (F : Polynomial (ℂ → ℂ)) (hneF : F ≠ 0)
    (hbound : ∀ j : ℕ, (d / 3).toNat < j → F.coeff j = 0)
    (hsource : ∀ j : ℕ, F.coeff j ∈ Nagata.W08.aS τ
      (3 * (d - 3 * (j : ℤ))) (L ^ (d - 3 * (j : ℤ))))
    (hfixed : ∀ i : Fin 9, HAOAL (𝕜 := ℂ)
      (fun y : ℂ × ℂ => sE F y.1 y.2) (a i, 0) m)
    (p : ι → ℂ × ℂ) (hp0 : ∀ i, (p i).1 ≠ 0)
    (hpP : ∀ i, (nTS hτ hτ0 a ha).val (p i).1 ≠ 0)
    (hmoving : ∀ i, HAOAL (𝕜 := ℂ)
      (fun y : ℂ × ℂ => sE F y.1 y.2)
      ((p i).1, (nTS hτ hτ0 a ha).val (p i).1 * (p i).2) m) :
    ∃ G : pS τ L (∏ i, -a i) d (m : ℤ)
        (nTS hτ hτ0 a ha).val,
      G ≠ 0 ∧ ∀ i, HAOAL (𝕜 := ℂ)
        (fun y : ℂ × ℂ => sE G.val y.1 y.2) (p i) m := by
  exact nWanp hτ hτ0 hL a ha hdisjoint d m F hneF hbound
    hsource (fun j _ _ i => Nagata.W18.sco F (a i) m j (hfixed i))
    p hp0 hpP hmoving
end Nagata.CS
end
section
namespace Nagata.CS
open scoped BigOperators
open Nagata.Workers.W17 Nagata.Workers.W28
theorem nWona {ι σ : Type*} {τ L : ℂ}
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (hL : L ≠ 0)
    (a : Fin 9 → ℂ) (ha : ∀ i, a i ≠ 0)
    (hdisjoint : Pairwise (fun i j => ∀ k : ℤ, a i ≠ a j * τ ^ k))
    (d m : ℕ) (X : σ → Nagata.W08.aS τ 3 L)
    (F : Polynomial (MvPolynomial σ ℂ))
    (hhom : ∀ j, (F.coeff j).IsHomogeneous (d - 3 * j))
    (hbound : ∀ j, d / 3 < j → F.coeff j = 0)
    (hneF : rNP (fun i => (X i).val) F ≠ 0)
    (hfixed : ∀ i : Fin 9, HAOAL (𝕜 := ℂ)
      (aNS1 (fun i => (X i).val) F) (a i, 0) m)
    (p : ι → ℂ × ℂ) (hp0 : ∀ i, (p i).1 ≠ 0)
    (hpP : ∀ i, (nTS hτ hτ0 a ha).val (p i).1 ≠ 0)
    (hmoving : ∀ i, HAOAL (𝕜 := ℂ)
      (aNS1 (fun i => (X i).val) F)
      ((p i).1, (nTS hτ hτ0 a ha).val (p i).1 * (p i).2) m) :
    ∃ G : pS τ L (∏ i, -a i) (d : ℤ) (m : ℤ)
        (nTS hτ hτ0 a ha).val,
      G ≠ 0 ∧ ∀ i, HAOAL (𝕜 := ℂ)
        (fun y : ℂ × ℂ => sE G.val y.1 y.2) (p i) m := by
  have hd : ((d : ℤ) / 3).toNat = d / 3 := by omega
  refine nWonT hτ hτ0 hL a ha hdisjoint (d : ℤ) m
    (rNP (fun i => (X i).val) F)
    hneF ?_
    (rNPss hτ0 X F d hhom hbound) ?_ p hp0 hpP ?_
  · rw [hd]
    exact rNPb _ F _ hbound
  · intro i
    exact (rNPoi _ F (a i, 0) (ha i) m).mpr (hfixed i)
  · intro i
    exact (rNPoi _ F
      ((p i).1, (nTS hτ hτ0 a ha).val (p i).1 * (p i).2) (hp0 i) m).mpr (hmoving i)
end Nagata.CS
end
section
namespace Nagata.CS
open scoped BigOperators
open Nagata.Workers.W17 Nagata.Workers.W28 Nagata.PG
def mNB {q : ℕ} (a : Fin 9 → ℂ) (p : Fin q → ℂ × ℂ) : Fin (9 + q) → ℂ :=
  Fin.addCases a (fun i => (p i).1)
def mNF {q : ℕ} (P : ℂ → ℂ) (p : Fin q → ℂ × ℂ) : Fin (9 + q) → ℂ :=
  Fin.addCases (fun _ => 0) (fun i => P (p i).1 * (p i).2)
end Nagata.CS
end
section
namespace Nagata.Workers.W17
open Nagata.Workers.W28 Nagata.PG
theorem uSnpo
    {r d : ℕ} {m : Fin r → ℕ} {τ L : ℂ}
    (hU : Nagata.W13.US r d m)
    (G : MvPolynomial (Fin 3) ℂ) (hG : G.IsHomogeneous 3)
    (X : Fin 3 → Nagata.W08.aS τ 3 L)
    (hrelations : Nagata.Workers.W25.pRI (fun a => (X a).val) =
      Ideal.span ({G} : Set _))
    (chart : Fin r → Fin 3) (z w : Fin r → ℂ)
    (hz : ∀ b, z b ≠ 0) (hc : ∀ b, (X (chart b)).val (z b) ≠ 0)
    (hbase : Function.Injective (fun b => cP (chart b)
      (pC (nCP (fun a => (X a).val) (chart b) (z b)))))
    (hdifferential : ∀ b, pG (Nagata.W27.dCH (chart b) G)
      (nCP (fun a => (X a).val) (chart b) (z b)) ≠ 0) :
    ∃ F : Polynomial (MvPolynomial (Fin 3) ℂ),
      (∀ n, (F.coeff n).IsHomogeneous (d-3*n)) ∧
      (∀ n, d/3 < n → F.coeff n = 0) ∧
      rNP (fun a => (X a).val) F ≠ 0 ∧
      ∀ b, HAOAL (𝕜 := ℂ)
        (Nagata.CS.aNS1 (fun a => (X a).val) F)
        (z b,w b) (m b) := by
  have hmem : G ∈ Nagata.Workers.W25.pRI (fun a => (X a).val) := by
    rw [hrelations]
    exact Ideal.subset_span (by simp)
  have heq := (Nagata.Workers.W25.mpRI _ G).mp hmem
  obtain ⟨F,hhom,hweight,hne,horder⟩ :=
    uSscn hU G 3 hG (by decide)
      (fun a => (X a).val) chart z w hz hc
      (fun b a => Nagata.W08.aSaA (X a) (hz b)) heq hbase hdifferential
  refine ⟨F,hhom,?_,rNPnz
    (fun a => (X a).val) G hrelations F hne,horder⟩
  intro n hn
  by_contra hh
  have hw := hweight n hh
  omega
end Nagata.Workers.W17
end
section
namespace Nagata.CS
open scoped BigOperators
open Nagata.Workers.W17 Nagata.Workers.W28 Nagata.PG
theorem uSnWs {q d m : ℕ} {τ L : ℂ}
    (hU : Nagata.W13.US (9 + q) d (fun _ => m))
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (hL : L ≠ 0)
    (a : Fin 9 → ℂ) (ha : ∀ i, a i ≠ 0)
    (hdisjoint : Pairwise (fun i j => ∀ k : ℤ, a i ≠ a j * τ ^ k))
    (p : Fin q → ℂ × ℂ) (hp0 : ∀ i, (p i).1 ≠ 0)
    (hpP : ∀ i, (nTS hτ hτ0 a ha).val (p i).1 ≠ 0)
    (C : MvPolynomial (Fin 3) ℂ) (hC : C.IsHomogeneous 3)
    (X : Fin 3 → Nagata.W08.aS τ 3 L)
    (hrelations : Nagata.Workers.W25.pRI (fun i => (X i).val) =
      Ideal.span ({C} : Set _))
    (chart : Fin (9 + q) → Fin 3)
    (hc : ∀ b, (X (chart b)).val (mNB a p b) ≠ 0)
    (hbase : Function.Injective (fun b => cP (chart b)
      (pC (nCP (fun i => (X i).val) (chart b)
        (mNB a p b)))))
    (hdifferential : ∀ b, pG (Nagata.W27.dCH (chart b) C)
      (nCP (fun i => (X i).val) (chart b) (mNB a p b)) ≠ 0) :
    ∃ G : pS τ L (∏ i, -a i) (d : ℤ) (m : ℤ)
        (nTS hτ hτ0 a ha).val,
      G ≠ 0 ∧ ∀ i, HAOAL (𝕜 := ℂ)
        (fun y : ℂ × ℂ => sE G.val y.1 y.2) (p i) m := by
  have hz : ∀ b, mNB a p b ≠ 0 := by
    intro b
    refine Fin.addCases ?_ ?_ b
    · intro i
      simpa only [mNB, Fin.addCases_left] using ha i
    · intro i
      simpa only [mNB, Fin.addCases_right] using hp0 i
  obtain ⟨F,hhom,hbound,hne,horders⟩ := uSnpo
    hU C hC X hrelations chart (mNB a p)
    (mNF (nTS hτ hτ0 a ha).val p) hz hc hbase hdifferential
  refine nWona hτ hτ0 hL a ha hdisjoint d m X F
    hhom hbound hne ?_ p hp0 hpP ?_
  · intro i
    simpa only [mNB, mNF, Fin.addCases_left] using
      horders (Fin.castAdd q i)
  · intro i
    simpa only [mNB, mNF, Fin.addCases_right] using
      horders (Fin.natAdd 9 i)
end Nagata.CS
end
section
namespace Nagata.CS
open scoped BigOperators
open Nagata.Workers.W17 Nagata.Workers.W28 Nagata.PG
theorem uSnWs1 {q d m : ℕ} {τ L : ℂ}
    (hU : Nagata.W13.US (9 + q) d (fun _ => m))
    (hτ : ‖τ‖ < 1) (hτ0 : τ ≠ 0) (hL : L ≠ 0)
    (a : Fin 9 → ℂ) (ha : ∀ i, a i ≠ 0)
    (hdisjoint : Pairwise (fun i j => ∀ k : ℤ, a i ≠ a j * τ ^ k))
    (z₀ : ℂ) (hz₀ : z₀ ≠ 0) (ξ : Fin q → ℂ)
    (hpP : ∀ i, (nTS hτ hτ0 a ha).val ((lP z₀ ξ) i).1 ≠ 0)
    (C : MvPolynomial (Fin 3) ℂ) (hC : C.IsHomogeneous 3)
    (X : Fin 3 → Nagata.W08.aS τ 3 L)
    (hrelations : Nagata.Workers.W25.pRI (fun i => (X i).val) =
      Ideal.span ({C} : Set _))
    (chart : Fin (9 + q) → Fin 3)
    (hc : ∀ b, (X (chart b)).val (mNB a (lP z₀ ξ) b) ≠ 0)
    (hbase : Function.Injective (fun b => cP (chart b)
      (pC (nCP (fun i => (X i).val) (chart b)
        (mNB a (lP z₀ ξ) b)))))
    (hdifferential : ∀ b, pG (Nagata.W27.dCH (chart b) C)
      (nCP (fun i => (X i).val) (chart b) (mNB a (lP z₀ ξ) b)) ≠ 0) :
    ∃ G : pS τ L (∏ i, -a i) (d : ℤ) (m : ℤ)
        (nTS hτ hτ0 a ha).val,
      G ≠ 0 ∧ ∀ i, HAOAL (𝕜 := ℂ)
        (fun y : ℂ × ℂ => Nagata.W20.lS1 G z₀ y.1 y.2) (ξ i, 0) m := by
  obtain ⟨G,hG,horder⟩ := uSnWs hU hτ hτ0 hL a ha hdisjoint
    (lP z₀ ξ) (fun i => mul_ne_zero hz₀ (Complex.exp_ne_zero (ξ i)))
    hpP C hC X hrelations chart hc hbase hdifferential
  refine ⟨G,hG,fun i => ?_⟩
  exact lSooc G z₀ (ξ i) (horder i)
end Nagata.CS
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W20
open scoped BigOperators Topology
open Nagata.Workers.W12 Nagata.Workers.W10 Nagata.CS
open Nagata.Workers.W17 Nagata.Workers.W28 Nagata.PG
open Nagata.FE
theorem smPce {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (marks : Fin 9 → ℝ) (x0 : ℝ) (x : ℂ) :
    (Nagata.W22.rMS hτ hτone marks).val
      (tP1 τ x0 * Complex.exp x) =
    Nagata.W06.TC.mP1 τ marks
      (Nagata.Workers.W05.cP2 τ x0 x : ℂ) := by
  have hz : tP1 τ x0 * Complex.exp x ≠ 0 :=
    mul_ne_zero (tPnz hτ x0) (Complex.exp_ne_zero x)
  unfold Nagata.W22.rMS
  rw [Nagata.W08.mTSa _ _ _ _ hz]
  unfold Nagata.W06.TC.mP1
  simp only [Nagata.Workers.W05.cPerr hτ,
    Nagata.Workers.W05.rPerr hτ, tP1]
theorem smod {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (marks : Fin 9 → ℝ) (hinj : Function.Injective marks)
    (hb : ∀ i, 0 < marks i ∧ marks i < 1 / 2) :
    Pairwise (fun i j => ∀ k : ℤ,
      ((τ ^ marks i : ℝ) : ℂ) ≠ ((τ ^ marks j : ℝ) : ℂ) * (τ : ℂ) ^ k) := by
  intro i j hij k he
  apply hij
  apply hinj
  have heq : Nagata.W21.tPM (Nagata.Workers.W05.pP τ hτ)
      (Nagata.Workers.W05.rP τ (marks j)) =
      Nagata.W21.tPM (Nagata.Workers.W05.pP τ hτ)
        (Nagata.Workers.W05.rP τ (marks i)) := by
    apply Quotient.sound
    apply (Nagata.W21.tOSic _ _ _).mpr
    refine ⟨k, ?_⟩
    simpa only [Nagata.Workers.W05.rPerr hτ,
      Nagata.Workers.W05.pP, Units.val_mk0, mul_comm] using he
  have hj : marks j ∈ Set.Ioo (0 : ℝ) 1 := ⟨(hb j).1, by linarith [(hb j).2]⟩
  have hi : marks i ∈ Set.Ioo (0 : ℝ) 1 := ⟨(hb i).1, by linarith [(hb i).2]⟩
  exact (Nagata.W06.TC.rTPio
    hτ hτone hj hi heq).symm
end Nagata.W20
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W25
open scoped BigOperators
theorem pdCH (c : Fin 3) (G : MvPolynomial (Fin 3) ℂ) (i : Fin 2) :
    MvPolynomial.pderiv i (Nagata.W27.dCH c G) =
      Nagata.W27.dCH c (MvPolynomial.pderiv (c.succAbove i) G) := by
  classical
  let f := Fin.insertNth (α := fun _ : Fin 3 => MvPolynomial (Fin 2) ℂ) c 1 MvPolynomial.X
  have hderiv (j : Fin 3) : MvPolynomial.pderiv i (f j) =
      if j = c.succAbove i then 1 else 0 := by
    by_cases hj : j = c
    · subst j
      simp [f]
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
      simp [f, MvPolynomial.pderiv_X, Pi.single_apply, eq_comm]
  change MvPolynomial.pderiv i (MvPolynomial.eval₂ MvPolynomial.C f G) =
    MvPolynomial.eval₂ MvPolynomial.C f (MvPolynomial.pderiv (c.succAbove i) G)
  rw [Nagata.Workers.W14.pps]
  simp_rw [hderiv, mul_ite, mul_one, mul_zero]
  simp
theorem epdCH {G : MvPolynomial (Fin 3) ℂ} {d : ℕ}
    (hG : G.IsHomogeneous d) (c : Fin 3) (x : Fin 3 → ℂ) (hc : x c ≠ 0) (i : Fin 2) :
    MvPolynomial.eval x (MvPolynomial.pderiv (c.succAbove i) G) =
      (x c) ^ (d - 1) * MvPolynomial.eval (fun j => x (c.succAbove j) / x c)
        (MvPolynomial.pderiv i (Nagata.W27.dCH c G)) := by
  rw [pdCH, Nagata.Workers.W17.edCH]
  have hscale := Nagata.W16.hes (hG.pderiv (i := c.succAbove i))
    (Fin.insertNth (α := fun _ : Fin 3 => ℂ) c 1 (fun j => x (c.succAbove j) / x c)) (x c)
  have hnorm : (fun a => x c * Fin.insertNth (α := fun _ : Fin 3 => ℂ) c 1
      (fun j => x (c.succAbove j) / x c) a) = x :=
    Nagata.Workers.W17.scv c x hc
  rw [hnorm] at hscale
  exact hscale
theorem enpdC {G : MvPolynomial (Fin 3) ℂ} {d : ℕ}
    (hG : G.IsHomogeneous d) (c : Fin 3) (x : Fin 3 → ℂ)
    (hc : x c ≠ 0) (hzero : MvPolynomial.eval x G = 0)
    (hgrad : ∃ j : Fin 3, MvPolynomial.eval x (MvPolynomial.pderiv j G) ≠ 0) :
    ∃ i : Fin 2, MvPolynomial.eval (fun j => x (c.succAbove j) / x c)
      (MvPolynomial.pderiv i (Nagata.W27.dCH c G)) ≠ 0 := by
  classical
  by_contra h
  have haff (i : Fin 2) : MvPolynomial.eval (fun j => x (c.succAbove j) / x c)
      (MvPolynomial.pderiv i (Nagata.W27.dCH c G)) = 0 := by
    by_contra hi
    exact h ⟨i, hi⟩
  have hamb (i : Fin 2) : MvPolynomial.eval x (MvPolynomial.pderiv (c.succAbove i) G) = 0 := by
    rw [epdCH hG c x hc i, haff, mul_zero]
  have heuler := congrArg (MvPolynomial.eval x) hG.sum_X_mul_pderiv
  simp only [map_sum, map_mul, MvPolynomial.eval_X, map_nsmul, hzero, nsmul_zero] at heuler
  have hsum : (∑ j : Fin 3, x j * MvPolynomial.eval x (MvPolynomial.pderiv j G)) =
      x c * MvPolynomial.eval x (MvPolynomial.pderiv c G) := by
    apply Finset.sum_eq_single c
    · intro j _ hj
      obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hj
      rw [hamb, mul_zero]
    · simp
  have hcderiv : MvPolynomial.eval x (MvPolynomial.pderiv c G) = 0 :=
    (mul_eq_zero.mp (hsum.symm.trans heuler)).resolve_left hc
  obtain ⟨j, hj⟩ := hgrad
  by_cases hjc : j = c
  · subst j
    exact hj hcderiv
  · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hjc
    exact hj (hamb i)
end Nagata.Workers.W25
end
end
section
namespace Nagata.Workers.W25
open Nagata.Workers.W28
theorem pPEnC (P : MvPolynomial (Fin 2) ℂ)
    (X : Fin 3 → ℂ → ℂ) (c : Fin 3) (z : ℂ) :
    pPE P (nCP X c z) =
      MvPolynomial.eval (fun i => X (c.succAbove i) z / X c z) P := by
  apply congrArg (fun v : Fin 2 → ℂ => MvPolynomial.eval v P)
  funext i
  fin_cases i <;> rfl
theorem nCPgn
    {G : MvPolynomial (Fin 3) ℂ} {d : ℕ} (hG : G.IsHomogeneous d)
    (c : Fin 3) (X : Fin 3 → ℂ → ℂ) (z : ℂ) (hc : X c z ≠ 0)
    (hzero : MvPolynomial.eval (fun j => X j z) G = 0)
    (hgrad : ∃ j : Fin 3, MvPolynomial.eval (fun i => X i z) (MvPolynomial.pderiv j G) ≠ 0) :
    pG (Nagata.W27.dCH c G) (nCP X c z) ≠ 0 := by
  obtain ⟨i, hi⟩ := enpdC hG c (fun j => X j z) hc hzero hgrad
  apply (pGnzi _ _).mpr
  fin_cases i
  · left
    rwa [pPEnC]
  · right
    rwa [pPEnC]
end Nagata.Workers.W25
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W25
open scoped BigOperators
def sLP {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℂ) (x : σ → ℂ) : Polynomial ℂ :=
  ∑ n ∈ Finset.range (P.totalDegree + 1),
    Polynomial.monomial n (MvPolynomial.eval x (MvPolynomial.homogeneousComponent n P))
theorem esLP {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℂ) (x : σ → ℂ) (t : ℂ) :
    (sLP P x).eval t = MvPolynomial.eval (fun i => t * x i) P := by
  classical
  unfold sLP
  rw [Polynomial.eval_finsetSum]
  conv_rhs => rw [← MvPolynomial.sum_homogeneousComponent P]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Polynomial.eval_monomial,
    Nagata.W16.hes (MvPolynomial.homogeneousComponent_isHomogeneous n P)]
  exact mul_comm _ _
theorem csLP {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℂ) (x : σ → ℂ) (n : ℕ) :
    (sLP P x).coeff n =
      MvPolynomial.eval x (MvPolynomial.homogeneousComponent n P) := by
  classical
  by_cases hn : n < P.totalDegree + 1
  · simp [sLP, Polynomial.coeff_monomial, hn]
  · have hdeg : P.totalDegree < n := by omega
    simp [sLP, Polynomial.coeff_monomial, hn,
      MvPolynomial.homogeneousComponent_eq_zero n P hdeg]
theorem hCezo {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℂ) (x : σ → ℂ) (S : Set ℂ) (hS : S.Infinite)
    (hP : ∀ t ∈ S, MvPolynomial.eval (fun i => t * x i) P = 0) (n : ℕ) :
    MvPolynomial.eval x (MvPolynomial.homogeneousComponent n P) = 0 := by
  have hzero : sLP P x = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot _ (hS.mono (fun t ht => by
      change (sLP P x).eval t = 0
      rw [esLP]
      exact hP t ht))
  rw [← csLP, hzero, Polynomial.coeff_zero]
end Nagata.Workers.W25
end
end
section
noncomputable section
namespace Nagata.Workers.W25
theorem iroim (a b : ℕ → ℂ)
    (ha : ∀ n, a n ≠ 0) (hb : Function.Injective b)
    (hab : ∀ n, a (n + 1) = b n * a n) : (Set.range a).Infinite := by
  intro hfinite
  have hinj : Function.Injective (fun n => (a n, a (n + 1))) := by
    intro n m h
    have h0 : a n = a m := congrArg Prod.fst h
    have h1 : a (n + 1) = a (m + 1) := congrArg Prod.snd h
    apply hb
    apply mul_right_cancel₀ (ha n)
    rw [← hab n, h0, ← hab m]
    exact h1
  have hpair : (Set.range (fun n => (a n, a (n + 1)))).Finite :=
    (hfinite.prod hfinite).subset (by rintro _ ⟨n, rfl⟩; exact ⟨⟨n, rfl⟩, ⟨n+1, rfl⟩⟩)
  exact (Set.infinite_range_of_injective hinj) hpair
def cOS (τ γ z : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => γ * (τ ^ n * z) ^ (-3 : ℤ) * cOS τ γ z n
theorem cOSnz {τ γ z : ℂ}
    (hτ : τ ≠ 0) (hγ : γ ≠ 0) (hz : z ≠ 0) (n : ℕ) :
    cOS τ γ z n ≠ 0 := by
  induction n with
  | zero => exact one_ne_zero
  | succ n ih => exact mul_ne_zero (mul_ne_zero hγ (zpow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hτ) hz))) ih
theorem csepi {τ γ z : ℂ}
    (hτ : τ ≠ 0) (hz : z ≠ 0) (s : Nagata.W08.aS τ 3 γ) (n : ℕ) :
    s.val (τ ^ n * z) = cOS τ γ z n * s.val z := by
  induction n with
  | zero => simp [cOS]
  | succ n ih =>
    rw [pow_succ, mul_comm (τ ^ n) τ, mul_assoc,
      s.property.2.2 _ (mul_ne_zero (pow_ne_zero _ hτ) hz), ih]
    simp only [cOS, mul_assoc]
theorem cpmi {τ γ z : ℂ}
    (hτ : τ ≠ 0) (hτnorm : ‖τ‖ < 1) (hγ : γ ≠ 0) (hz : z ≠ 0) :
    Function.Injective (fun n : ℕ => γ * (τ ^ n * z) ^ (-3 : ℤ)) := by
  intro n m h
  have hnorm := congrArg norm h
  simp only [norm_mul, norm_zpow, norm_pow] at hnorm
  have hp := mul_left_cancel₀ (norm_ne_zero_iff.mpr hγ) hnorm
  have hb := (zpow_left_inj₀
    (mul_nonneg (pow_nonneg (norm_nonneg τ) n) (norm_nonneg z))
    (mul_nonneg (pow_nonneg (norm_nonneg τ) m) (norm_nonneg z))
    (by decide : (-3 : ℤ) ≠ 0)).mp hp
  have he := mul_right_cancel₀ (norm_ne_zero_iff.mpr hz) hb
  exact (pow_right_injective₀ (norm_pos_iff.mpr hτ) (ne_of_lt hτnorm)) he
theorem cOSi {τ γ z : ℂ}
    (hτ : τ ≠ 0) (hτnorm : ‖τ‖ < 1) (hγ : γ ≠ 0) (hz : z ≠ 0) :
    (Set.range (cOS τ γ z)).Infinite :=
  iroim _ _
    (cOSnz hτ hγ hz)
    (cpmi hτ hτnorm hγ hz) (fun _ => rfl)
end Nagata.Workers.W25
end
end
section
namespace Nagata.Workers.W25
theorem hCmcS {τ γ : ℂ}
    (hτ : τ ≠ 0) (hτnorm : ‖τ‖ < 1) (hγ : γ ≠ 0)
    (b : Fin 3 → Nagata.W08.aS τ 3 γ)
    (P : MvPolynomial (Fin 3) ℂ)
    (hP : P ∈ pRI (fun i => (b i).val)) (n : ℕ) :
    MvPolynomial.homogeneousComponent n P ∈
      pRI (fun i => (b i).val) := by
  apply (mpRI _ _).mpr
  intro z hz
  apply hCezo P (fun i => (b i).val z)
    (Set.range (cOS τ γ z)) (cOSi hτ hτnorm hγ hz)
  rintro t ⟨k, rfl⟩
  have heval := (mpRI _ P).mp hP
    (τ ^ k * z) (mul_ne_zero (pow_ne_zero _ hτ) hz)
  have hfun : (fun i => cOS τ γ z k * (b i).val z) =
      (fun i => (b i).val (τ ^ k * z)) :=
    funext (fun i => (csepi hτ hz (b i) k).symm)
  rw [hfun]
  exact heval
end Nagata.Workers.W25
end
section
namespace Nagata.Workers.W25
noncomputable local instance oaiLocInst9 {σ R : Type*} [CommSemiring R] : GradedAlgebra (MvPolynomial.homogeneousSubmodule σ R) := MvPolynomial.gradedAlgebra
theorem cSRIi {τ γ : ℂ}
    (hτ : τ ≠ 0) (hτnorm : ‖τ‖ < 1) (hγ : γ ≠ 0)
    (b : Fin 3 → Nagata.W08.aS τ 3 γ) :
    (pRI (fun i => (b i).val)).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ) := by
  intro n P hP
  have hcomp (D : DirectSum.Decomposition
      (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)) :
      (D.decompose' P n : MvPolynomial (Fin 3) ℂ) = MvPolynomial.homogeneousComponent n P := by
    rw [Subsingleton.elim D MvPolynomial.decomposition,
      MvPolynomial.decomposition.decompose'_apply]
  rw [← DirectSum.Decomposition.decompose'_eq, hcomp]
  exact hCmcS hτ hτnorm hγ b P hP n
end Nagata.Workers.W25
end
section
namespace Nagata.Workers.W25
theorem eacmr {τ : ℝ}
    (hτ : 0 < τ) (hτone : τ < 1) {γ : ℂ} (hγ : γ ≠ 0)
    (b : Fin 3 → Nagata.W08.aS (τ : ℂ) 3 γ) :
    ∃ P : MvPolynomial (Fin 3) ℂ, P ≠ 0 ∧ P.IsHomogeneous 3 ∧
      P ∈ pRI (fun i => (b i).val) := by
  let := Nagata.Workers.W10.aSf hτ hτone
    (show (0 : ℤ) < 9 by decide) (pow_ne_zero 3 hγ)
  apply ecmrI b
  rw [Nagata.Workers.W10.aSf1 hτ hτone
    (show (0 : ℤ) < 9 by decide) (pow_ne_zero 3 hγ)]
  decide
theorem aCSRI {τ : ℝ}
    (hτ : 0 < τ) (hτone : τ < 1) {γ : ℂ} (hγ : γ ≠ 0)
    (b : Fin 3 → Nagata.W08.aS (τ : ℂ) 3 γ) :
    pRI (fun i => (b i).val) ≠ ⊥ := by
  obtain ⟨P, hP, _, hmem⟩ := eacmr hτ hτone hγ b
  intro hzero
  rw [hzero, Ideal.mem_bot] at hmem
  exact hP hmem
end Nagata.Workers.W25
end
section
namespace Nagata.Workers.W25
noncomputable local instance oaiLocInst10 {σ R : Type*} [CommSemiring R] : GradedAlgebra (MvPolynomial.homogeneousSubmodule σ R) := MvPolynomial.gradedAlgebra
theorem ergoi {τ : ℝ}
    (hτ : 0 < τ) (hτone : τ < 1) {γ : ℂ} (hγ : γ ≠ 0)
    (b : Fin 3 → Nagata.W08.aS (τ : ℂ) 3 γ)
    (hind : AlgebraicIndependent ℂ (fun i : Fin 2 =>
      Ideal.Quotient.mk (pRI (fun j => (b j).val))
        (MvPolynomial.X i.castSucc))) :
    ∃ G : MvPolynomial (Fin 3) ℂ,
      Prime G ∧ G.IsHomogeneous G.totalDegree ∧
      0 < G.totalDegree ∧ G.totalDegree ≤ 3 ∧
      pRI (fun i => (b i).val) = Ideal.span {G} := by
  let I := pRI (fun i => (b i).val)
  let : I.IsPrime := cSRIi1 b
  have hheight : I.height ≤ 1 :=
    Nagata.W04.Dim.hlooi I hind
  have hτne : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hτ)
  have hτnorm : ‖(τ : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ] using hτone
  obtain ⟨G, hprime, hhom, hpos, hI⟩ :=
    Nagata.Workers.W30.hhopg I
      (aCSRI hτ hτone hγ b) hheight
      (cSRIi hτne hτnorm hγ b)
  obtain ⟨P, hP, hPdegree, hPmem⟩ := eacmr hτ hτone hγ b
  have hdvd : G ∣ P := Ideal.mem_span_singleton.mp (hI ▸ hPmem)
  have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdvd hP
  rw [hPdegree.totalDegree hP] at hle
  exact ⟨G, hprime, hhom, hpos, hle, hI⟩
end Nagata.Workers.W25
end
section
namespace Nagata.Workers.W25
noncomputable local instance oaiLocInst11 {σ R : Type*} [CommSemiring R] : GradedAlgebra (MvPolynomial.homogeneousSubmodule σ R) := MvPolynomial.gradedAlgebra
theorem aBbCa {τ γ : ℂ}
    (hτ : τ ≠ 0) (hτnorm : ‖τ‖ < 1) (hγ : γ ≠ 0)
    (b : Module.Basis (Fin 3) ℂ (Nagata.W08.aS τ 3 γ)) :
    AlgebraicIndependent ℂ (fun i : Fin 2 =>
      Ideal.Quotient.mk (pRI (fun j => (b j).val))
        (MvPolynomial.X i.castSucc)) := by
  apply Nagata.W02.aIqon Fin.castSucc
    (cSRIi1 b)
    (cSRIi hτ hτnorm hγ b)
  intro a c hrel
  exact bplrt b 0 1 (by decide) a c hrel
theorem earg {τ : ℝ}
    (hτ : 0 < τ) (hτone : τ < 1) {γ : ℂ} (hγ : γ ≠ 0)
    (b : Module.Basis (Fin 3) ℂ (Nagata.W08.aS (τ : ℂ) 3 γ)) :
    ∃ G : MvPolynomial (Fin 3) ℂ,
      Prime G ∧ G.IsHomogeneous G.totalDegree ∧
      0 < G.totalDegree ∧ G.totalDegree ≤ 3 ∧
      pRI (fun i => (b i).val) = Ideal.span {G} := by
  apply ergoi hτ hτone hγ b
  apply aBbCa
    (Complex.ofReal_ne_zero.mpr (ne_of_gt hτ)) _ hγ b
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ] using hτone
theorem eargw {τ : ℝ}
    (hτ : 0 < τ) (hτone : τ < 1) {γ : ℂ} (hγ : γ ≠ 0)
    (b : Module.Basis (Fin 3) ℂ (Nagata.W08.aS (τ : ℂ) 3 γ)) :
    ∃ G : MvPolynomial (Fin 3) ℂ,
      Prime G ∧ G.IsHomogeneous G.totalDegree ∧
      0 < G.totalDegree ∧ G.totalDegree ≤ 3 ∧
      pRI (fun i => (b i).val) = Ideal.span {G} ∧
      ∀ P : MvPolynomial (Fin 3) ℂ, ¬ G ∣ P →
        ∃ z : ℂ, z ≠ 0 ∧ MvPolynomial.eval (fun i => (b i).val z) P ≠ 0 := by
  obtain ⟨G, hG, hhom, hpos, hle, hI⟩ := earg hτ hτone hγ b
  exact ⟨G, hG, hhom, hpos, hle, hI,
    fun P hP => eenzo _ G hI P hP⟩
end Nagata.Workers.W25
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W14
 theorem pzotr1 {K : Type*} [Field K]
    (P : Polynomial K) (z : Fin 3 → K) (hz : Function.Injective z)
    (hdeg : P.natDegree ≤ 2) (hzero : ∀ i, P.eval (z i) = 0) : P = 0 := by
  exact Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P hz hzero
    (by simpa using Nat.lt_succ_of_le hdeg)
 theorem pzotr {K : Type*} [Field K]
    (P : Polynomial K) {t : K} (ht : t ≠ 0)
    (hdeg : P.natDegree ≤ 1) (hzero : P.eval 0 = 0) (htzero : P.eval t = 0) : P = 0 := by
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
    (f := ![0,t])
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i <;> assumption
  · simpa using Nat.lt_succ_of_le hdeg
 theorem pzodz {K : Type*} [Field K]
    (P : Polynomial K) {t : K} (ht : t ≠ 0) (hdeg : P.natDegree ≤ 2)
    (hzero : P.eval 0 = 0) (hderiv : P.derivative.eval 0 = 0)
    (htzero : P.eval t = 0) : P = 0 := by
  obtain ⟨Q,rfl⟩ := (Polynomial.X_dvd_iff (f := P)).mpr (by rw [Polynomial.coeff_zero_eq_eval_zero]; exact hzero)
  by_cases hQ : Q = 0
  · simp [hQ]
  have hqdeg : Q.natDegree ≤ 1 := by
    rw [Polynomial.natDegree_X_mul hQ] at hdeg
    omega
  have hqzero : Q.eval 0 = 0 := by
    simpa [Polynomial.derivative_mul] using hderiv
  have hqt : Q.eval t = 0 := by
    simpa [ht] using htzero
  have := pzotr Q ht hqdeg hqzero hqt
  exact False.elim (hQ this)
end Nagata.Workers.W14
end
end
section
noncomputable section
namespace Nagata.Workers.W14
open scoped BigOperators
 def bAO (F : MvPolynomial (Fin 2) ℂ) : Polynomial ℂ :=
  MvPolynomial.eval₂ Polynomial.C (fun i => if i = 0 then 1 else Polynomial.X) F
 theorem bAOes (F : MvPolynomial (Fin 2) ℂ) :
    bAO F = ∑ u ∈ F.support, Polynomial.C (F.coeff u) * Polynomial.X ^ u 1 := by
  classical
  rw [bAO, MvPolynomial.eval₂_eq']
  apply Finset.sum_congr rfl
  intro u _
  simp
 theorem bAOe (F : MvPolynomial (Fin 2) ℂ) (t : ℂ) :
    (bAO F).eval t = MvPolynomial.eval ![1,t] F := by
  simp [bAOes, MvPolynomial.eval_eq', Polynomial.eval_finsetSum]
 theorem bAOnD {F : MvPolynomial (Fin 2) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) : (bAO F).natDegree ≤ d := by
  classical
  rw [bAOes]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro u hu
  apply (Polynomial.natDegree_C_mul_X_pow_le (F.coeff u) (u 1)).trans
  rw [hF.degree_eq_sum_deg_support hu]
  by_cases hz : u 1 = 0
  · simp [hz]
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr hz)
 theorem bAOcd {F : MvPolynomial (Fin 2) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) :
    (bAO F).coeff d = MvPolynomial.eval ![0,1] F := by
  classical
  rw [bAOes, Polynomial.finsetSum_coeff, MvPolynomial.eval_eq']
  apply Finset.sum_congr rfl
  intro u hu
  have hu' : u 0 + u 1 = d := by
    have hh := hF.degree_eq_sum_deg_support hu
    change d = u.sum (fun _ n => n) at hh
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hh
    simpa [Fin.sum_univ_two] using hh.symm
  by_cases h0 : u 0 = 0
  · have h1 : u 1 = d := by omega
    simp [h0,h1]
  · have h1 : u 1 ≠ d := by omega
    simp [h0,Ne.symm h1]
 theorem bAOez {F : MvPolynomial (Fin 2) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) (hzero : bAO F = 0) : F = 0 := by
  have hmul : MvPolynomial.X 0 * F = 0 := by
    apply ((MvPolynomial.isHomogeneous_X ℂ (0 : Fin 2)).mul hF).eq_zero_of_forall_eval_eq_zero
    intro x
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_X]
    by_cases hx : x 0 = 0
    · simp [hx]
    · have hcoords : ![1, x 1 / x 0] = fun i : Fin 2 => (x 0)⁻¹ * x i := by
        funext i
        fin_cases i <;> simp [hx,div_eq_mul_inv,mul_comm]
      have hval := bAOe F (x 1 / x 0)
      rw [hzero, Polynomial.eval_zero, hcoords,
        Nagata.W16.hes hF] at hval
      have hz := (mul_eq_zero.mp hval.symm).resolve_left (pow_ne_zero d (inv_ne_zero hx))
      rw [hz,mul_zero]
  exact (mul_eq_zero.mp hmul).resolve_left (MvPolynomial.X_ne_zero 0)
 theorem bAOnz {F : MvPolynomial (Fin 2) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) {a b : ℂ} (ha : a ≠ 0)
    (hz : MvPolynomial.eval ![a,b] F = 0) : (bAO F).eval (b/a) = 0 := by
  rw [bAOe]
  have hcoords : ![1,b/a] = fun i : Fin 2 => a⁻¹ * ![a,b] i := by
    funext i
    fin_cases i <;> simp [ha,div_eq_mul_inv,mul_comm]
  rw [hcoords,Nagata.W16.hes hF, hz,mul_zero]
 theorem bAOd (F : MvPolynomial (Fin 2) ℂ) :
    (bAO F).derivative = bAO (MvPolynomial.pderiv 1 F) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [bAO]
  | add P Q hP hQ => simpa [bAO] using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
    fin_cases i <;> simp_all [bAO, Polynomial.derivative_mul]
    ring
 theorem bzotp {F : MvPolynomial (Fin 2) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) (hd : d ≤ 2) {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h0 : MvPolynomial.eval ![1,0] F = 0)
    (hinfty : MvPolynomial.eval ![0,1] F = 0)
    (hab : MvPolynomial.eval ![a,b] F = 0) : F = 0 := by
  apply bAOez hF
  apply pzotr (bAO F) (div_ne_zero hb ha)
  · have hdeg := Polynomial.natDegree_le_pred (bAOnD hF)
      ((bAOcd hF).trans hinfty)
    omega
  · simpa only [bAOe] using h0
  · exact bAOnz hF ha hab
 theorem bczos {F : MvPolynomial (Fin 2) ℂ}
    (hF : F.IsHomogeneous 3) {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h0 : MvPolynomial.eval ![1,0] F = 0)
    (hinfty : MvPolynomial.eval ![0,1] F = 0)
    (hab : MvPolynomial.eval ![a,b] F = 0)
    (hsing : MvPolynomial.eval ![1,0] (MvPolynomial.pderiv 1 F) = 0) : F = 0 := by
  apply bAOez hF
  apply pzodz (bAO F) (div_ne_zero hb ha)
  · exact Polynomial.natDegree_le_pred (bAOnD hF)
      ((bAOcd hF).trans hinfty)
  · simpa only [bAOe] using h0
  · simpa only [bAOd,bAOe] using hsing
  · exact bAOnz hF ha hab
end Nagata.Workers.W14
end
end
section
noncomputable section
namespace Nagata.Workers.W14
open Nagata.PG Nagata.W01
theorem hldot
    (L Q : MvPolynomial (Fin 3) ℂ) {d : ℕ}
    (hL : L.IsHomogeneous 1) (hne : L ≠ 0) (hQ : Q.IsHomogeneous d) (hd : d ≤ 2)
    (p : Fin 3 → PP) (hinj : Function.Injective p)
    (hLzero : ∀ i, MvPolynomial.eval (p i).rep L = 0)
    (hQzero : ∀ i, MvPolynomial.eval (p i).rep Q = 0) : L ∣ Q := by
  obtain ⟨b,a,c,hb0,hb1,ha,hc,hp0,hp1,hp2,hchange⟩ :=
    ehln L hL hne (p 0) (p 1) (p 2)
      (fun h => (by decide : (0 : Fin 3) ≠ 1) (hinj h))
      (fun h => (by decide : (2 : Fin 3) ≠ 0) (hinj h))
      (fun h => (by decide : (2 : Fin 3) ≠ 1) (hinj h))
      (hLzero 0) (hLzero 1) (hLzero 2)
  rw [← bPCdi b L Q, hchange]
  apply cLdor
  apply bzotp
    (cLRh ((bPChi b Q d).mpr hQ))
    hd ha hc
  · rw [cLRe]
    change MvPolynomial.eval ![1,0,0] (bPC b Q) = 0
    rw [bPCea b Q (p 0) _ hp0]
    exact hQzero 0
  · rw [cLRe]
    change MvPolynomial.eval ![0,1,0] (bPC b Q) = 0
    rw [bPCea b Q (p 1) _ hp1]
    exact hQzero 1
  · rw [cLRe]
    change MvPolynomial.eval ![a,c,0] (bPC b Q) = 0
    rw [bPCea b Q (p 2) _ hp2]
    exact hQzero 2
end Nagata.Workers.W14
end
end
section
noncomputable section
namespace Nagata.Workers.W14
open Nagata.PG Nagata.W01
theorem hldco
    (L Q : MvPolynomial (Fin 3) ℂ)
    (hL : L.IsHomogeneous 1) (hne : L ≠ 0) (hQ : Q.IsHomogeneous 3)
    (p : Fin 3 → PP) (hinj : Function.Injective p)
    (hLzero : ∀ i, MvPolynomial.eval (p i).rep L = 0)
    (hQzero : ∀ i, MvPolynomial.eval (p i).rep Q = 0)
    (hsing : ∀ j, MvPolynomial.eval (p 0).rep (MvPolynomial.pderiv j Q) = 0) : L ∣ Q := by
  obtain ⟨b,a,c,hb0,hb1,ha,hc,hp0,hp1,hp2,hchange⟩ :=
    ehln L hL hne (p 0) (p 1) (p 2)
      (fun h => (by decide : (0 : Fin 3) ≠ 1) (hinj h))
      (fun h => (by decide : (2 : Fin 3) ≠ 0) (hinj h))
      (fun h => (by decide : (2 : Fin 3) ≠ 1) (hinj h))
      (hLzero 0) (hLzero 1) (hLzero 2)
  rw [← bPCdi b L Q, hchange]
  apply cLdor
  apply bczos
    (cLRh ((bPChi b Q 3).mpr hQ))
    ha hc
  · rw [cLRe]
    change MvPolynomial.eval ![1,0,0] (bPC b Q) = 0
    rw [bPCea b Q (p 0) _ hp0]
    exact hQzero 0
  · rw [cLRe]
    change MvPolynomial.eval ![0,1,0] (bPC b Q) = 0
    rw [bPCea b Q (p 1) _ hp1]
    exact hQzero 1
  · rw [cLRe]
    change MvPolynomial.eval ![a,c,0] (bPC b Q) = 0
    rw [bPCea b Q (p 2) _ hp2]
    exact hQzero 2
  · apply blpzo
    intro i
    rw [hb0]
    exact hsing i
end Nagata.Workers.W14
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.Workers.W14
open Nagata.W18
 theorem poiP {K : Type*} [CommRing K] (P : Polynomial K) :
    MvPolynomial.pderiv (1 : Fin 2)
      (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (0 : Fin 2)) P) = 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp [hP, hQ]
  | monomial n a =>
    simp [Polynomial.eval₂_monomial]
 theorem ponTB {K : Type*} [CommRing K]
    (H : Polynomial (Polynomial K)) :
    MvPolynomial.pderiv (1 : Fin 2) (nTB H) =
      nTB H.derivative := by
  induction H using Polynomial.induction_on' with
  | add P Q hP hQ => simp [hP, hQ]
  | monomial n a =>
    simp [nTB, Polynomial.eval₂_monomial, Polynomial.derivative_monomial,
      poiP]
    ring
 theorem pPEnT
    (H : Polynomial (Polynomial ℂ)) (p : ℂ × ℂ) :
    Nagata.Workers.W28.pPE (nTB H) p =
      Nagata.W06.LA.pE H p.1 p.2 := by
  unfold Nagata.Workers.W28.pPE
  rw [← Nagata.W18.nEepE]
  change (Polynomial.evalRingHom p.1) (H.eval (Polynomial.C p.2)) =
    H.eval₂ (Polynomial.evalRingHom p.1) p.2
  simpa using
    (Polynomial.eval₂_at_apply (p := H) (Polynomial.evalRingHom p.1) (Polynomial.C p.2)).symm
 theorem pPEpo
    (H : Polynomial (Polynomial ℂ)) (p : ℂ × ℂ) :
    Nagata.Workers.W28.pPE
      (MvPolynomial.pderiv 1 (nTB H)) p =
      Nagata.W06.LA.pE H.derivative p.1 p.2 := by
  rw [ponTB, pPEnT]
end Nagata.Workers.W14
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.W03
open Nagata.Workers.W25
theorem pniUo
    (L : MvPolynomial (Fin 3) ℂ) (v : Fin 3 → ℂ)
    (hv : MvPolynomial.eval v L = 0) : ¬ IsUnit L := by
  intro hL
  exact (hL.map (MvPolynomial.eval v)).ne_zero hv
theorem prdm
    (s : Fin 3 → ℂ → ℂ) (G L : MvPolynomial (Fin 3) ℂ)
    (hG : Prime G) (hrel : G ∈ pRI s)
    (hL : ¬ IsUnit L) (hdiv : L ∣ G) : L ∈ pRI s := by
  have hassoc : Associated G L := (hG.irreducible.dvd_iff.mp hdiv).resolve_left hL
  obtain ⟨Q, hQ⟩ := hassoc.dvd
  rw [hQ]
  exact Ideal.mul_mem_right _ _ hrel
theorem prndo
    (s : Fin 3 → ℂ → ℂ) (G L : MvPolynomial (Fin 3) ℂ)
    (hG : Prime G) (hrel : G ∈ pRI s)
    (v : Fin 3 → ℂ) (hv : MvPolynomial.eval v L = 0)
    (hw : ∃ z : ℂ, z ≠ 0 ∧ MvPolynomial.eval (fun i => s i z) L ≠ 0) :
    ¬ L ∣ G := by
  intro hdiv
  have hmem := prdm s G L hG hrel
    (pniUo L v hv) hdiv
  obtain ⟨z, hz, hwz⟩ := hw
  exact hwz ((mpRI s L).mp hmem z hz)
end Nagata.W03
end
section
noncomputable section
namespace Nagata.W03
open Nagata.Workers.W25 Nagata.W07 Nagata.W08 Nagata.W21 Nagata.W16
open Nagata.PG
theorem aprtP {τ : ℝ}
    (hτ : 0 < τ) (hτone : τ < 1) {γ : ℂ} (hγ : γ ≠ 0)
    (G : MvPolynomial (Fin 3) ℂ) (hG : Prime G)
    (hhom : G.IsHomogeneous G.totalDegree)
    (hrel : G ∈ pRI
      (fun i => (aCB hτ hτone hγ i).val))
    (q : TP1 (cP1 hτ)) :
    ∃ (L : MvPolynomial (Fin 3) ℂ) (p : Fin 3 → PP),
      L ≠ 0 ∧ L.IsHomogeneous 1 ∧ Function.Injective p ∧
      p 0 = aCM hτ hτone hγ q ∧
      (∀ i, MvPolynomial.eval (p i).rep L = 0) ∧
      (∀ i, MvPolynomial.eval (p i).rep G = 0) ∧ ¬ L ∣ G := by
  obtain ⟨L, p, hL, hLhom, hinj, hp0, himg, hLzero, hw⟩ :=
    etPLt hτ hτone hγ q
  refine ⟨L, p, hL, hLhom, hinj, hp0, hLzero, ?_, ?_⟩
  · intro i
    obtain ⟨qi, hqi⟩ := himg i
    rw [← hqi]
    exact cTMoc (cP1 hτ) (aCB hτ hτone hγ)
      (fun _ hz => aCekd hτ hτone hγ hz)
      ⟨G, hhom, hG.ne_zero⟩ ((mpRI _ _).mp hrel) qi
  · exact prndo _ G L hG hrel
      (p 0).rep (hLzero 0) hw
end Nagata.W03
end
end
section
noncomputable section
namespace Nagata.W03
open Nagata.Workers.W25 Nagata.W07 Nagata.W08 Nagata.W21
theorem aprtD {τ : ℝ}
    (hτ : 0 < τ) (hτone : τ < 1) {γ : ℂ} (hγ : γ ≠ 0)
    (G : MvPolynomial (Fin 3) ℂ) (hG : Prime G)
    (hhom : G.IsHomogeneous G.totalDegree) (hle : G.totalDegree ≤ 3)
    (hrel : G ∈ pRI
      (fun i => (aCB hτ hτone hγ i).val)) :
    G.totalDegree = 3 := by
  by_contra hne
  have hsmall : G.totalDegree ≤ 2 := by omega
  obtain ⟨L, p, hL, hLhom, hinj, _, hLzero, hGzero, hnotdiv⟩ :=
    aprtP hτ hτone hγ G hG hhom hrel
      (tPM (cP1 hτ) 1)
  exact hnotdiv (Nagata.Workers.W14.hldot
    L G hLhom hL hhom hsmall p hinj hLzero hGzero)
theorem eapcg {τ : ℝ}
    (hτ : 0 < τ) (hτone : τ < 1) {γ : ℂ} (hγ : γ ≠ 0) :
    ∃ G : MvPolynomial (Fin 3) ℂ,
      Prime G ∧ G.IsHomogeneous 3 ∧ G.totalDegree = 3 ∧
      pRI
        (fun i => (aCB hτ hτone hγ i).val) = Ideal.span {G} ∧
      (∀ z : ℂ, z ≠ 0 →
        MvPolynomial.eval (cEV (aCB hτ hτone hγ) z) G = 0) ∧
      (∀ P : MvPolynomial (Fin 3) ℂ, ¬ G ∣ P →
        ∃ z : ℂ, z ≠ 0 ∧
          MvPolynomial.eval (cEV (aCB hτ hτone hγ) z) P ≠ 0) := by
  obtain ⟨G, hG, hhom, _, hle, hI, hnoncancel⟩ :=
    eargw hτ hτone hγ
      (aCB hτ hτone hγ)
  have hrel : G ∈ pRI
      (fun i => (aCB hτ hτone hγ i).val) := by
    rw [hI]
    exact Ideal.subset_span (Set.mem_singleton G)
  have hdegree := aprtD hτ hτone hγ G hG hhom hle hrel
  have hhom3 : G.IsHomogeneous 3 := by simpa only [hdegree] using hhom
  exact ⟨G, hG, hhom3, hdegree, hI,
    (mpRI _ _).mp hrel, hnoncancel⟩
end Nagata.W03
end
end
section
namespace Nagata.W21
open Nagata.W03 Nagata.Workers.W25 Nagata.W07 Nagata.W08
 theorem apcra {τ : ℝ}
    (hτ : 0 < τ) (hτone : τ < 1) {γ : ℂ} (hγ : γ ≠ 0)
    (G : MvPolynomial (Fin 3) ℂ) (hG : Prime G)
    (hhom : G.IsHomogeneous 3) (hdegree : G.totalDegree = 3)
    (hrel : G ∈ pRI
      (fun i => (aCB hτ hτone hγ i).val))
    (q : TP1 (cP1 hτ)) :
    ∃ j, MvPolynomial.eval (aCM hτ hτone hγ q).rep
      (MvPolynomial.pderiv j G) ≠ 0 := by
  by_contra hsing
  push Not at hsing
  obtain ⟨L,p,hL,hLhom,hinj,hp0,hLzero,hGzero,hnotdiv⟩ :=
    aprtP hτ hτone hγ G hG
      (by simpa only [hdegree] using hhom) hrel q
  apply hnotdiv
  apply Nagata.Workers.W14.hldco
    L G hLhom hL hhom p hinj hLzero hGzero
  intro j
  rw [hp0]
  exact hsing j
 theorem earpc {τ : ℝ}
    (hτ : 0 < τ) (hτone : τ < 1) {γ : ℂ} (hγ : γ ≠ 0) :
    ∃ G : MvPolynomial (Fin 3) ℂ,
      Prime G ∧ G.IsHomogeneous 3 ∧ G.totalDegree = 3 ∧
      pRI
        (fun i => (aCB hτ hτone hγ i).val) = Ideal.span {G} ∧
      (∀ z : ℂ, z ≠ 0 →
        MvPolynomial.eval (cEV (aCB hτ hτone hγ) z) G = 0) ∧
      (∀ z : ℂ, z ≠ 0 → ∃ j,
        MvPolynomial.eval (cEV (aCB hτ hτone hγ) z)
          (MvPolynomial.pderiv j G) ≠ 0) ∧
      (∀ P : MvPolynomial (Fin 3) ℂ, ¬ G ∣ P → ∃ z : ℂ, z ≠ 0 ∧
        MvPolynomial.eval (cEV (aCB hτ hτone hγ) z) P ≠ 0) := by
  obtain ⟨G,hG,hhom,hdegree,hI,hzero,hnoncancel⟩ :=
    eapcg hτ hτone hγ
  refine ⟨G,hG,hhom,hdegree,hI,hzero,?_,hnoncancel⟩
  intro z hz
  apply (aCMgi hτ hτone hγ G hhom (Units.mk0 z hz)).mp
  apply apcra hτ hτone hγ G hG hhom hdegree
  rw [hI]
  exact Ideal.subset_span (Set.mem_singleton G)
end Nagata.W21
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W06.TC
open Nagata.Workers.W05 Nagata.W07 Nagata.W21 Nagata.PG Nagata.W16
def aMV {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (η x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ) (t : Fin (9 + q)) : Fin 3 → ℂ :=
  cEV (aCB hτ hτone (rP τ η).ne_zero)
    (cT τ x0 xi ξ t : ℂ)
theorem aMVnz {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (η x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ) (t : Fin (9 + q)) :
    aMV hτ hτone η x0 xi ξ t ≠ 0 :=
  cEVnz _ (aCekd hτ hτone
    (rP τ η).ne_zero (cT τ x0 xi ξ t).ne_zero)
def aMP {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (η x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ) (t : Fin (9 + q)) : PP :=
  aCM hτ hτone (rP τ η).ne_zero (tT τ hτ x0 xi ξ t)
theorem aMPem {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (η x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ) (t : Fin (9 + q)) :
    aMP hτ hτone η x0 xi ξ t =
      Projectivization.mk ℂ (aMV hτ hτone η x0 xi ξ t)
        (aMVnz hτ hτone η x0 xi ξ t) := rfl
theorem aMPi {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (η x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ)
    (hinj : Function.Injective (tT τ hτ x0 xi ξ)) :
    Function.Injective (aMP hτ hτone η x0 xi ξ) :=
  (aCMi hτ hτone (rP τ η).ne_zero).comp hinj
end Nagata.W06.TC
end
end
section
noncomputable section
namespace Nagata.W06.TC
open Nagata.Workers.W05 Nagata.W07 Nagata.W08 Nagata.W21 Nagata.PG
open Nagata.Workers.W17 Nagata.Workers.W28
def aCS {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (η : ℝ) :
    Fin 3 → aS (τ : ℂ) 3 (rP τ η : ℂ) :=
  aCB hτ hτone (rP τ η).ne_zero
def aCF {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (η : ℝ) :
    Fin 3 → ℂ → ℂ := fun a => (aCS hτ hτone η a).val
theorem eaMC {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (η x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ) (t : Fin (9 + q)) :
    ∃ c : Fin 3, aCF hτ hτone η c (cT τ x0 xi ξ t : ℂ) ≠ 0 := by
  by_contra! h
  apply aMVnz hτ hτone η x0 xi ξ t
  funext a
  exact h a
def aMC {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (η x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ) (t : Fin (9 + q)) : Fin 3 :=
  Classical.choose (eaMC hτ hτone η x0 xi ξ t)
theorem aMCn {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (η x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ) (t : Fin (9 + q)) :
    aCF hτ hτone η (aMC hτ hτone η x0 xi ξ t)
      (cT τ x0 xi ξ t : ℂ) ≠ 0 :=
  Classical.choose_spec (eaMC hτ hτone η x0 xi ξ t)
theorem aNPc {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (η x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ) (t : Fin (9 + q)) (c : Fin 3) :
    pC (nCP (aCF hτ hτone η) c
      (cT τ x0 xi ξ t : ℂ)) =
      cC1 c (aMP hτ hτone η x0 xi ξ t) := by
  funext a
  rw [aMPem]
  change (if a = 0 then _ else _) =
    cC c (Projectivization.mk ℂ _ _) (cIE c a)
  rw [cCm]
  fin_cases a <;> rfl
theorem aNPe {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (η x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ) (t : Fin (9 + q)) (c : Fin 3)
    (hc : aCF hτ hτone η c (cT τ x0 xi ξ t : ℂ) ≠ 0) :
    cP c (pC (nCP (aCF hτ hτone η) c
      (cT τ x0 xi ξ t : ℂ))) = aMP hτ hτone η x0 xi ξ t := by
  rw [aNPc]
  apply cPcC
  rw [aMPem]
  exact (mrcnz _ _ c).mpr hc
theorem aNCi {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (η x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ)
    (hinj : Function.Injective (tT τ hτ x0 xi ξ))
    (chart : Fin (9 + q) → Fin 3)
    (hc : ∀ t, aCF hτ hτone η (chart t) (cT τ x0 xi ξ t : ℂ) ≠ 0) :
    Function.Injective (fun t => cP (chart t)
      (pC (nCP (aCF hτ hτone η) (chart t)
        (cT τ x0 xi ξ t : ℂ)))) := by
  simpa only [aNPe hτ hτone η x0 xi ξ _ _ (hc _)] using
    aMPi hτ hτone η x0 xi ξ hinj
end Nagata.W06.TC
end
end
section
noncomputable section
namespace Nagata.W06.TC
open Nagata.Workers.W05 Nagata.Workers.W17 Nagata.Workers.W28 Nagata.PG
theorem aMCg {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (η x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ)
    (G : MvPolynomial (Fin 3) ℂ) (hG : G.IsHomogeneous 3)
    (hzero : ∀ z : ℂ, z ≠ 0 → MvPolynomial.eval
      (fun i => aCF hτ hτone η i z) G = 0)
    (hgrad : ∀ z : ℂ, z ≠ 0 → ∃ j, MvPolynomial.eval
      (fun i => aCF hτ hτone η i z) (MvPolynomial.pderiv j G) ≠ 0)
    (t : Fin (9 + q)) :
    pG (Nagata.W27.dCH (aMC hτ hτone η x0 xi ξ t) G)
      (nCP (aCF hτ hτone η)
        (aMC hτ hτone η x0 xi ξ t) (cT τ x0 xi ξ t : ℂ)) ≠ 0 :=
  Nagata.Workers.W25.nCPgn hG
    (aMC hτ hτone η x0 xi ξ t) (aCF hτ hτone η)
    (cT τ x0 xi ξ t : ℂ) (aMCn hτ hτone η x0 xi ξ t)
    (hzero _ (cT τ x0 xi ξ t).ne_zero)
    (hgrad _ (cT τ x0 xi ξ t).ne_zero)
theorem aMscd {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (η x0 : ℝ) (xi : Fin 9 → ℝ) {q : ℕ} (ξ : Fin q → ℂ)
    (hinj : Function.Injective (tT τ hτ x0 xi ξ))
    (G : MvPolynomial (Fin 3) ℂ) (hG : G.IsHomogeneous 3)
    (hzero : ∀ z : ℂ, z ≠ 0 → MvPolynomial.eval
      (fun i => aCF hτ hτone η i z) G = 0)
    (hgrad : ∀ z : ℂ, z ≠ 0 → ∃ j, MvPolynomial.eval
      (fun i => aCF hτ hτone η i z) (MvPolynomial.pderiv j G) ≠ 0) :
    (∀ t, aCF hτ hτone η (aMC hτ hτone η x0 xi ξ t)
      (cT τ x0 xi ξ t : ℂ) ≠ 0) ∧
    Function.Injective (fun t => cP (aMC hτ hτone η x0 xi ξ t)
      (pC (nCP (aCF hτ hτone η)
        (aMC hτ hτone η x0 xi ξ t) (cT τ x0 xi ξ t : ℂ)))) ∧
    (∀ t, pG
      (Nagata.W27.dCH (aMC hτ hτone η x0 xi ξ t) G)
      (nCP (aCF hτ hτone η)
        (aMC hτ hτone η x0 xi ξ t) (cT τ x0 xi ξ t : ℂ)) ≠ 0) := by
  refine ⟨aMCn hτ hτone η x0 xi ξ, ?_, ?_⟩
  · exact aNCi hτ hτone η x0 xi ξ hinj
      (aMC hτ hτone η x0 xi ξ) (aMCn hτ hτone η x0 xi ξ)
  · exact aMCg hτ hτone η x0 xi ξ G hG hzero hgrad
end Nagata.W06.TC
end
end
section
noncomputable section
namespace Nagata.W06.TC
open Nagata.Workers.W05 Nagata.Workers.W10 Nagata.W08 Nagata.CS
open scoped BigOperators
def sCS {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (marks : Fin 9 → ℝ) (a : ℝ) :
    Fin 3 → aS (τ : ℂ) 3 (tP1 τ (((∑ i, marks i) + a) / 3)) :=
  fun i => ⟨(aCS hτ hτone (((∑ i, marks i) + a) / 3) i).val,
    by simpa only [rPerr hτ, tP1] using
      (aCS hτ hτone (((∑ i, marks i) + a) / 3) i).property⟩
@[simp] theorem sCSv {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (marks : Fin 9 → ℝ) (a : ℝ) (i : Fin 3) :
    (sCS hτ hτone marks a i).val =
      aCF hτ hτone (((∑ j, marks j) + a) / 3) i := rfl
theorem mNBec {τ : ℝ} (hτ : 0 < τ)
    (marks : Fin 9 → ℝ) (x0 : ℝ) {q : ℕ} (ξ : Fin q → ℂ) (b : Fin (9 + q)) :
    mNB (fun i => ((τ ^ marks i : ℝ) : ℂ))
      (lP (tP1 τ x0) ξ) b = (cT τ x0 marks ξ b : ℂ) := by
  refine Fin.addCases ?_ ?_ b
  · intro i
    have he := cTl τ x0 marks ξ i
    rw [finSumFinEquiv_apply_left] at he
    rw [he]
    simp only [mNB, Fin.addCases_left, rPerr hτ]
  · intro j
    have he := cTr τ x0 marks ξ j
    rw [finSumFinEquiv_apply_right] at he
    rw [he]
    simp only [mNB, Fin.addCases_right, lP,
      cPerr hτ, tP1]
end Nagata.W06.TC
end
end
section
noncomputable section
namespace Nagata.W06.TC
open Nagata.Workers.W05 Nagata.Workers.W10 Nagata.Workers.W17 Nagata.Workers.W28
open Nagata.W07 Nagata.W21 Nagata.PG Nagata.CS
open scoped BigOperators
theorem eassg {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (marks : Fin 9 → ℝ) (a : ℝ) :
    ∃ C : MvPolynomial (Fin 3) ℂ, Prime C ∧ C.IsHomogeneous 3 ∧
      ∃ X : Fin 3 → Nagata.W08.aS (τ : ℂ) 3
          (tP1 τ (((∑ i, marks i) + a) / 3)),
        Nagata.Workers.W25.pRI (fun i => (X i).val) = Ideal.span ({C} : Set _) ∧
        ∀ (q : ℕ) (ξ : Fin q → ℂ),
          Function.Injective (tT τ hτ (1 / 2) marks ξ) →
          ∃ chart : Fin (9 + q) → Fin 3,
            (∀ b, (X (chart b)).val
              (mNB (fun i => ((τ ^ marks i : ℝ) : ℂ))
                (lP (tP1 τ (1 / 2)) ξ) b) ≠ 0) ∧
            Function.Injective (fun b => cP (chart b)
              (pC (nCP (fun i => (X i).val) (chart b)
                (mNB (fun i => ((τ ^ marks i : ℝ) : ℂ))
                  (lP (tP1 τ (1 / 2)) ξ) b)))) ∧
            (∀ b, pG (Nagata.W27.dCH (chart b) C)
              (nCP (fun i => (X i).val) (chart b)
                (mNB (fun i => ((τ ^ marks i : ℝ) : ℂ))
                  (lP (tP1 τ (1 / 2)) ξ) b)) ≠ 0) := by
  let η : ℝ := ((∑ i, marks i) + a) / 3
  obtain ⟨C, hCprime, hChom, hCdegree, hrel, hzero, hgrad, hnoncancel⟩ :=
    earpc hτ hτone (rP τ η).ne_zero
  refine ⟨C, hCprime, hChom, sCS hτ hτone marks a, ?_, ?_⟩
  · exact hrel
  · intro q ξ hinj
    refine ⟨aMC hτ hτone η (1 / 2) marks ξ, ?_⟩
    have hdata := aMscd hτ hτone η (1 / 2) marks ξ hinj C hChom hzero hgrad
    simpa only [sCSv, mNBec hτ,
      η] using hdata
end Nagata.W06.TC
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.CS
open scoped BigOperators Topology
open Nagata.W20 Nagata.Workers.W12 Nagata.Workers.W10 Nagata.CS
open Nagata.Workers.W17 Nagata.Workers.W28 Nagata.PG
theorem snWos {q d m : ℕ} {τ : ℝ}
    (hτ : 0 < τ) (hτone : τ < 1)
    (hUniversal : Nagata.W13.US (9 + q) d (fun _ => m))
    (marks : Fin 9 → ℝ) (a x0 : ℝ)
    (hdisjoint : Pairwise (fun i j => ∀ k : ℤ,
      ((τ ^ marks i : ℝ) : ℂ) ≠ ((τ ^ marks j : ℝ) : ℂ) * (τ : ℂ) ^ k))
    (ξ : Fin q → ℂ)
    (hpP : ∀ i, (Nagata.W22.rMS hτ hτone marks).val
      (tP1 τ x0 * Complex.exp (ξ i)) ≠ 0)
    (C : MvPolynomial (Fin 3) ℂ) (hC : C.IsHomogeneous 3)
    (X : Fin 3 → Nagata.W08.aS (τ : ℂ) 3
      (tP1 τ (((∑ i, marks i) + a) / 3)))
    (hrelations : Nagata.Workers.W25.pRI (fun i => (X i).val) =
      Ideal.span ({C} : Set _))
    (chart : Fin (9 + q) → Fin 3)
    (hc : ∀ b, (X (chart b)).val
      (mNB (fun i => ((τ ^ marks i : ℝ) : ℂ))
        (lP (tP1 τ x0) ξ) b) ≠ 0)
    (hbase : Function.Injective (fun b => cP (chart b)
      (pC (nCP (fun i => (X i).val) (chart b)
        (mNB (fun i => ((τ ^ marks i : ℝ) : ℂ))
          (lP (tP1 τ x0) ξ) b)))))
    (hdifferential : ∀ b, pG (Nagata.W27.dCH (chart b) C)
      (nCP (fun i => (X i).val) (chart b)
        (mNB (fun i => ((τ ^ marks i : ℝ) : ℂ))
          (lP (tP1 τ x0) ξ) b)) ≠ 0) :
    ∃ F : gSS hτ hτone marks a (d : ℤ) m, F ≠ 0 ∧
      ∀ i, HAOAL (𝕜 := ℂ)
        (fun x : ℂ × ℂ => lS1 F (tP1 τ x0) x.1 x.2) (ξ i, 0) m := by
  have ht : ‖(τ : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ] using hτone
  have ht0 : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ.ne'
  have hm : ∀ i, ((τ ^ marks i : ℝ) : ℂ) ≠ 0 :=
    fun i => Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hτ (marks i)).ne'
  have heq := nTSre hτ hτone ht ht0 marks hm
  have hp : ∀ i, (nTS ht ht0 (fun i => ((τ ^ marks i : ℝ) : ℂ)) hm).val
      ((lP (tP1 τ x0) ξ) i).1 ≠ 0 := by
    simpa only [heq, lP] using hpP
  have hW := uSnWs1 hUniversal ht ht0
    (tPnz hτ (((∑ i, marks i) + a) / 3))
    (fun i => ((τ ^ marks i : ℝ) : ℂ)) hm hdisjoint
    (tP1 τ x0) (tPnz hτ x0) ξ hp C hC X hrelations chart hc hbase hdifferential
  change ∃ F : AS (τ : ℂ)
    (tP1 τ (((∑ i, marks i) + a) / 3)) (∏ i, -((τ ^ marks i : ℝ) : ℂ))
    (d : ℤ) m (Nagata.W22.rMS hτ hτone marks).val, F ≠ 0 ∧
    ∀ i, HAOAL (𝕜 := ℂ)
      (fun x : ℂ × ℂ => lS1 F (tP1 τ x0) x.1 x.2) (ξ i, 0) m at hW
  exact Eq.mp (congrArg (fun γ : ℂ =>
    ∃ F : AS (τ : ℂ) (tP1 τ (((∑ i, marks i) + a) / 3)) γ
      (d : ℤ) m (Nagata.W22.rMS hτ hτone marks).val, F ≠ 0 ∧
      ∀ i, HAOAL (𝕜 := ℂ)
        (fun x : ℂ × ℂ => lS1 F (tP1 τ x0) x.1 x.2) (ξ i, 0) m)
    (rMM hτ marks)) hW
end Nagata.CS
end
end
section
noncomputable section
namespace Nagata.CS
open scoped BigOperators Topology
open Nagata.Workers.W12 Nagata.Workers.W10 Nagata.W20
open Nagata.Workers.W17 Nagata.Workers.W28 Nagata.PG
theorem sfnW {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (marks : Fin 9 → ℝ) (hmarks : Function.Injective marks)
    (hmbounds : ∀ i, 0 < marks i ∧ marks i < 1 / 2)
    (a : ℝ) (d m q : ℕ)
    (hUniversal : Nagata.W13.US (9 + q) d (fun _ => m)) :
    ∃ U : Set ℂ, IsOpen U ∧ (0 : ℂ) ∈ U ∧
      ∀ ξ : Fin q → ℂ, Function.Injective ξ → (∀ i, ξ i ∈ U) →
        ∃ F : gSS hτ hτone marks a (d : ℤ) m, F ≠ 0 ∧
          ∀ i, HAOAL (𝕜 := ℂ)
            (fun x : ℂ × ℂ => lS1 F (tP1 τ (1 / 2)) x.1 x.2) (ξ i, 0) m := by
  obtain ⟨C, _hprime, hC, X, hrelations, hcharts⟩ :=
    Nagata.W06.TC.eassg hτ hτone marks a
  obtain ⟨R, hR, hcfg⟩ := Nagata.W06.TC.edffp
    hτ hτone marks hmarks hmbounds
  refine ⟨Metric.ball 0 R, Metric.isOpen_ball, Metric.mem_ball_self hR, ?_⟩
  intro ξ hξ hξU
  have hnorm : ∀ i, ‖ξ i‖ < R := by
    intro i
    simpa only [Metric.mem_ball, dist_zero_right] using hξU i
  obtain ⟨hinj,hPi⟩ := hcfg q ξ hξ hnorm
  obtain ⟨chart,hc,hbase,hdifferential⟩ := hcharts q ξ hinj
  apply snWos hτ hτone hUniversal marks a (1 / 2)
    (smod hτ hτone marks hmarks hmbounds) ξ ?_
    C hC X hrelations chart hc hbase hdifferential
  intro i
  rw [smPce]
  exact hPi i
end Nagata.CS
end
end
section
noncomputable section
namespace Nagata.CS
open Filter Topology
open Nagata.Workers.W12 Nagata.Workers.W10 Nagata.W20 Nagata.Workers.W28
theorem sfsc {r d m : ℕ} (hr : 9 ≤ r)
    (hUniversal : Nagata.W13.US r d (fun _ => m))
    (n : ℕ) (marks : Fin 9 → ℝ) (hmarks : Function.Injective marks)
    (hmbounds : ∀ i, 0 < marks i ∧ marks i < 1 / 2) (a : ℝ) :
    ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
      ∃ (hτ : 0 < τ) (hτone : τ < 1) (U : Set ℂ),
        IsOpen U ∧ (0 : ℂ) ∈ U ∧
        ∀ ξ : Fin (r - 9) → ℂ, Function.Injective ξ → (∀ i, ξ i ∈ U) →
          ∃ F : gSS hτ hτone marks a ((n * d : ℕ) : ℤ) (n * m),
            F ≠ 0 ∧ ∀ i, HAOAL (𝕜 := ℂ)
              (fun x : ℂ × ℂ => lS1 F (tP1 τ (1 / 2)) x.1 x.2)
              (ξ i, 0) (n * m) := by
  have hrEq : r = 9 + (r - 9) := by omega
  have hscaled : Nagata.W13.US (9 + (r - 9)) (n * d) (fun _ => n * m) := by
    have hu : Nagata.W13.US r (n * d) (fun _ => n * m) := by
      simpa only [Nat.mul_comm] using Nagata.W13.uSp hUniversal n
    exact Eq.mp (congrArg (fun R : ℕ =>
      Nagata.W13.US R (n * d) (fun _ => n * m)) hrEq) hu
  have hone : ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ), τ < 1 :=
    mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [self_mem_nhdsWithin, hone] with τ hτ hτone
  obtain ⟨U,hU,h0,hEvery⟩ := sfnW hτ hτone marks hmarks hmbounds
    a (n * d) (n * m) (r - 9) hscaled
  exact ⟨hτ,hτone,U,hU,h0,hEvery⟩
end Nagata.CS
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Nagata.W27
open scoped BigOperators
open MvPolynomial
variable {r : ℕ} {R : Type*} [CommRing R]
def bO (a : (Fin r × Fin 2) →₀ ℕ) (i : Fin r) : ℕ :=
  a (i, 0) + a (i, 1)
def bDB (f : MvPolynomial (Fin r × Fin 2) R) (i : Fin r) : ℕ :=
  f.support.sup (fun a => bO a i)
theorem bOlb (f : MvPolynomial (Fin r × Fin 2) R)
    (a : (Fin r × Fin 2) →₀ ℕ) (ha : a ∈ f.support) (i : Fin r) :
    bO a i ≤ bDB f i := by
  exact Finset.le_sup (f := fun a => bO a i) ha
def gE (c : Fin r → Fin 3) (D : Fin r → ℕ)
    (a : (Fin r × Fin 2) →₀ ℕ) : (Fin r × Fin 3) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun ij : Fin r × Fin 3 =>
    Fin.insertNth (α := fun _ : Fin 3 => ℕ) (c ij.1)
      (D ij.1 - bO a ij.1 + 1)
      (fun j => a (ij.1, j)) ij.2
@[simp] theorem gEs (c : Fin r → Fin 3) (D : Fin r → ℕ)
    (a : (Fin r × Fin 2) →₀ ℕ) (i : Fin r) :
    gE c D a (i, c i) = D i - bO a i + 1 := by
  simp [gE]
@[simp] theorem gEo (c : Fin r → Fin 3) (D : Fin r → ℕ)
    (a : (Fin r × Fin 2) →₀ ℕ) (i : Fin r) (j : Fin 2) :
    gE c D a (i, (c i).succAbove j) = a (i, j) := by
  simp [gE]
theorem gEbs (c : Fin r → Fin 3) (D : Fin r → ℕ)
    (a : (Fin r × Fin 2) →₀ ℕ) (i : Fin r) (ha : bO a i ≤ D i) :
    (∑ j : Fin 3, gE c D a (i, j)) = D i + 1 := by
  rw [Fin.sum_univ_succAbove _ (c i)]
  simp only [gEs, gEo, Fin.sum_univ_two]
  unfold bO at *
  omega
def gH (c : Fin r → Fin 3)
    (f : MvPolynomial (Fin r × Fin 2) R) : MvPolynomial (Fin r × Fin 3) R :=
  ∑ a ∈ f.support, monomial (gE c (bDB f) a) (f.coeff a)
theorem gHh (c : Fin r → Fin 3)
    (f : MvPolynomial (Fin r × Fin 2) R)
    (b : (Fin r × Fin 3) →₀ ℕ) (hb : b ∈ (gH c f).support)
    (i : Fin r) : (∑ j : Fin 3, b (i, j)) = bDB f i + 1 := by
  classical
  have hcoeff : (gH c f).coeff b ≠ 0 := mem_support_iff.mp hb
  simp only [gH, coeff_sum] at hcoeff
  obtain ⟨a, ha, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcoeff
  have heq : gE c (bDB f) a = b := by
    by_contra hne
    exact hterm (by simp [coeff_monomial, hne])
  rw [← heq]
  exact gEbs c _ a i (bOlb f a ha i)
theorem egHz (c : Fin r → Fin 3)
    (f : MvPolynomial (Fin r × Fin 2) R) (v : Fin r × Fin 3 → R)
    (i : Fin r) (hi : v (i, c i) = 0) :
    eval v (gH c f) = 0 := by
  classical
  simp only [gH, map_sum]
  apply Finset.sum_eq_zero
  intro a ha
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  apply mul_eq_zero_of_right
  apply Finset.prod_eq_zero (Finset.mem_univ (i, c i))
  rw [gEs, hi]
  exact zero_pow (by omega)
theorem egHn (c : Fin r → Fin 3)
    (f : MvPolynomial (Fin r × Fin 2) R) (v : Fin r × Fin 3 → R)
    (hv : ∀ i, v (i, c i) = 1) :
    eval v (gH c f) =
      eval (fun ij => v (ij.1, (c ij.1).succAbove ij.2)) f := by
  classical
  rw [eval_eq' _ f]
  simp only [gH, map_sum, eval_monomial]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_prod_type, Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Fin.prod_univ_succAbove _ (c i)]
  simp only [gEs, gEo, hv, one_pow, one_mul]
theorem egHs (c : Fin r → Fin 3)
    (f : MvPolynomial (Fin r × Fin 2) R)
    (a : Fin r → R) (v : Fin r × Fin 3 → R) :
    eval (fun ij => a ij.1 * v ij) (gH c f) =
      (∏ i, a i ^ (bDB f i + 1)) * eval v (gH c f) := by
  classical
  simp only [eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [mul_pow, Finset.prod_mul_distrib]
  have hprod : (∏ ij : Fin r × Fin 3, a ij.1 ^ b ij) =
      ∏ i, a i ^ (bDB f i + 1) := by
    rw [Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro i hi
    change (∏ j : Fin 3, a i ^ b (i, j)) = a i ^ (bDB f i + 1)
    rw [Finset.prod_pow_eq_pow_sum, gHh c f b hb i]
  rw [hprod]
  ac_rfl
theorem egHc {K : Type*} [Field K]
    (c : Fin r → Fin 3) (f : MvPolynomial (Fin r × Fin 2) K)
    (v : Fin r × Fin 3 → K) (hv : ∀ i, v (i, c i) ≠ 0) :
    eval v (gH c f) =
      (∏ i, v (i, c i) ^ (bDB f i + 1)) *
        eval (fun ij => v (ij.1, (c ij.1).succAbove ij.2) / v (ij.1, c ij.1)) f := by
  have h := egHs c f
    (fun i => v (i, c i)) (fun ij => v ij / v (ij.1, c ij.1))
  have heq : (fun ij : Fin r × Fin 3 =>
      v (ij.1, c ij.1) * (v ij / v (ij.1, c ij.1))) = v := by
    funext ij
    exact mul_div_cancel₀ _ (hv ij.1)
  rw [heq] at h
  rw [egHn c f
    (fun ij => v ij / v (ij.1, c ij.1)) (fun i => div_self (hv i))] at h
  exact h
theorem egHez {K : Type*} [Field K]
    (c : Fin r → Fin 3) (f : MvPolynomial (Fin r × Fin 2) K)
    (v : Fin r × Fin 3 → K) (hv : ∀ i, v (i, c i) ≠ 0) :
    eval v (gH c f) = 0 ↔
      eval (fun ij => v (ij.1, (c ij.1).succAbove ij.2) / v (ij.1, c ij.1)) f = 0 := by
  rw [egHc c f v hv]
  have hfactor : (∏ i, v (i, c i) ^ (bDB f i + 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (hv i)
  exact mul_eq_zero.trans (or_iff_right hfactor)
end Nagata.W27
end
end
end OAI
end
section
namespace OAI
section
namespace Nagata.Workers.W25
theorem gcg {C X : Type*} {I : C → Type*}
    (U : C → X → Prop) (Z : (c : C) → I c → X → Prop) (S : X → Prop)
    (hcover : ∀ x, ∃ c, U c x)
    (houtside : ∀ c e x, ¬ U c x → Z c e x)
    (hlocal : ∀ c x, U c x → (S x ↔ ∀ e, Z c e x)) :
    ∀ x, S x ↔ ∀ c e, Z c e x := by
  intro x
  constructor
  · intro hS c e
    by_cases hU : U c x
    · exact (hlocal c x hU).mp hS e
    · exact houtside c e x hU
  · intro hZ
    obtain ⟨c, hc⟩ := hcover x
    exact (hlocal c x hc).mpr (hZ c)
end Nagata.Workers.W25
end
section
noncomputable section
namespace Nagata.PG
open scoped BigOperators
def gE1 {r : ℕ} (c : CC r)
    (f : MvPolynomial (Fin r × Fin 2) ℂ) : ME r where
  polynomial := W27.gH c f
  multidegree := fun i => W27.bDB f i + 1
  homogeneous := W27.gHh c f
theorem gEvo {r : ℕ} (c : CC r)
    (f : MvPolynomial (Fin r × Fin 2) ℂ) (p : Fin r → PP)
    (hp : ¬ ICC c p) : eV (gE1 c f) p := by
  rw [eVier]
  obtain ⟨i, hi⟩ := Classical.not_forall.mp hp
  exact W27.egHz c f (fun ij => (p ij.1).rep ij.2) i
    (Classical.not_not.mp hi)
theorem gEvi {r : ℕ} (c : CC r)
    (f : MvPolynomial (Fin r × Fin 2) ℂ) (p : Fin r → PP)
    (hp : ICC c p) :
    eV (gE1 c f) p ↔
      MvPolynomial.eval (cCC c p) f = 0 := by
  rw [eVier]
  exact W27.egHez c f
    (fun ij => (p ij.1).rep ij.2) hp
def pCZL {r : ℕ} {ι : Type*}
    (F : ι → ME r) : Set (Fin r → PP) :=
  {p | ∀ i, eV (F i) p}
theorem iPZCc {r : ℕ} {ι : Type*}
    (F : ι → ME r) :
    IPZC (pCZL F) := by
  refine ⟨Set.range F, ?_⟩
  intro p
  constructor
  · intro hp G hG
    obtain ⟨i, rfl⟩ := hG
    exact hp i
  · intro hp i
    exact hp (F i) ⟨i, rfl⟩
theorem cCoge {r : ℕ}
    {I : CC r → Type*}
    (G : (c : CC r) → I c → ME r)
    (S : Set (ODP r))
    (houtside : ∀ c e (p : ODP r),
      ¬ ICC c p.val → eV (G c e) p.val)
    (hlocal : ∀ c p, ICC c p.val →
      (p ∈ S ↔ ∀ e, eV (G c e) p.val)) :
    ICZC S := by
  let F : (Σ c, I c) → ME r := fun ce => G ce.1 ce.2
  refine ⟨pCZL F, iPZCc F, ?_⟩
  intro p
  have hglue := Workers.W25.gcg
    (fun c (q : ODP r) => ICC c q.val)
    (fun c e (q : ODP r) => eV (G c e) q.val)
    (fun q => q ∈ S)
    (fun q => cCc q.val) houtside hlocal p
  constructor
  · intro hp ce
    exact hglue.mp hp ce.1 ce.2
  · intro hp
    exact hglue.mpr (fun c e => hp ⟨c, e⟩)
theorem cCocp {r : ℕ}
    {I : CC r → Type*}
    (f : (c : CC r) → I c → MvPolynomial (Fin r × Fin 2) ℂ)
    (S : Set (ODP r))
    (hlocal : ∀ c p, ICC c p.val →
      (p ∈ S ↔ ∀ e, MvPolynomial.eval (cCC c p.val) (f c e) = 0)) :
    ICZC S := by
  apply cCoge (fun c e => gE1 c (f c e)) S
  · intro c e p hp
    exact gEvo c (f c e) p.val hp
  · intro c p hp
    exact (hlocal c p hp).trans
      (forall_congr' fun e => (gEvi c (f c e) p.val hp).symm)
end Nagata.PG
end
end
section
noncomputable section
open Classical
namespace Nagata.PG
theorem mALid {F : MvPolynomial (Fin 3) ℂ} {d : ℕ}
    (hF : F.IsHomogeneous d) (p : PP) (c : Fin 3) (hc : p.rep c ≠ 0) (m : ℕ) :
    mAL F p m ↔
      AM.oAL (cC1 c p) m (W27.dCH c F) := by
  apply (mALic hF p c hc m).trans
  simpa only [cDeei, W27.dCH,
    MvPolynomial.coe_eval₂Hom] using
    (oALcD c p F m).symm
theorem sLicm (r : ℕ) (index : Workers.W25.II r)
    (c : CC r) (p : ODP r)
    (hp : ICC c p.val) :
    p ∈ W13.sL1 r index ↔
      ∀ s : W27.HM index.1.val → W27.PJ r index.2,
        MvPolynomial.eval (cCC c p.val)
          (W27.mP (W27.cPJM (R := ℂ) c index.1.val index.2) s) = 0 := by
  classical
  have hforms : p ∈ W13.sL1 r index ↔
      ∃ F : MvPolynomial.homogeneousSubmodule (Fin 3) ℂ index.1.val,
        F.val ≠ 0 ∧ ∀ i,
          AM.oAL
            (fun j => cCC c p.val (i, j)) (index.2 i)
            (W27.dCH (c i) F.val) := by
    constructor
    · rintro ⟨F, hFne, hFhom, hForder⟩
      refine ⟨⟨F, hFhom⟩, hFne, ?_⟩
      intro i
      exact (mALid hFhom (p.val i) (c i) (hp i)
        (index.2 i)).mp (hForder i)
    · rintro ⟨F, hFne, hForder⟩
      refine ⟨F.val, hFne, F.property, ?_⟩
      intro i
      exact (mALid F.property (p.val i) (c i) (hp i)
        (index.2 i)).mpr (hForder i)
  exact hforms.trans (W27.enfic1 c index.1.val index.2
    (cCC c p.val))
theorem sLiCZ (r : ℕ)
    (index : Workers.W25.II r) :
    ICZC (W13.sL1 r index) := by
  classical
  apply cCocp
    (fun c s => W27.mP
      (W27.cPJM (R := ℂ) c index.1.val index.2) s)
    (W13.sL1 r index)
  intro c p hp
  exact sLicm r index c p hp
end Nagata.PG
end
end
end OAI
end
namespace OAI.Nagata.W13
open PG Workers.W14
theorem pu {r d e : ℕ} {m : Fin r → ℕ} (hle : d ≤ e)
    (h : US r d m) : US r e m := by
  intro p
  obtain ⟨F, hn, hh, hm⟩ := h p
  let G : MvPolynomial (Fin 3) ℂ := MvPolynomial.X 0 ^ (e - d)
  have hg : G.IsHomogeneous (e - d) := by
    simpa [G] using (MvPolynomial.isHomogeneous_X ℂ (0 : Fin 3)).pow (e-d)
  refine ⟨F * G, mul_ne_zero hn (pow_ne_zero _ (MvPolynomial.X_ne_zero _)), ?_, ?_⟩
  · simpa [Nat.add_sub_of_le hle] using hh.mul hg
  · intro i
    simpa using mALm (hm i) (mALz G (p.val i))
theorem ouou {r d : ℕ} (hr : 10 ≤ r) (sq : ¬ IsSquare r) (hd : 0 < d) (m : Fin r → ℕ)
    (hbad : (d : ℝ)*Real.sqrt r ≤ ∑ i, (m i : ℝ)) (hu : US r d m) :
    ∃ D M : ℕ, 0 < M ∧ 3 < (D : ℝ)/M ∧ (D : ℝ)/M < Real.sqrt r ∧ US r D (fun _ => M) := by
  have hr0 : 0 < r := by omega
  let D := r.factorial*d
  let M := (r-1).factorial * ∑ i, m i
  have har := fs hr0 hd (s := ∑ i, m i) (by simpa using hbad)
  have hm : 0 < M := har.2.1
  have hs : (D : ℝ)/M ≤ Real.sqrt r := har.2.2
  have u : US r D (fun _ => M) := uSs hr0 hu
  have hstrict := rlson sq hs
  by_cases low : 3 < (D : ℝ)/M
  · exact ⟨D, M, hm, low, hstrict, u⟩
  · have hm' : (0:ℝ) < M := by exact_mod_cast hm
    have hd3 : D ≤ 3*M := by exact_mod_cast (div_le_iff₀ hm').mp (le_of_not_gt low)
    have up := uSp u 10
    have v : US r (30*M+1) (fun _ => M*10) := pu (by omega) up
    have hsqr := Real.sq_sqrt (Nat.cast_nonneg r)
    have hr' : (10:ℝ) ≤ r := by exact_mod_cast hr
    have h31 : (31/10:ℝ) < Real.sqrt r := by nlinarith [Real.sqrt_nonneg (r:ℝ)]
    have hm1 : (1:ℝ) ≤ M := by exact_mod_cast hm
    refine ⟨30*M+1, M*10, by positivity, ?_, ?_, v⟩
    · apply (lt_div_iff₀ (by positivity)).2
      push_cast; linarith
    · apply (div_lt_iff₀ (by positivity)).2
      push_cast; nlinarith [mul_lt_mul_of_pos_right h31 hm']
end OAI.Nagata.W13
namespace OMA.H3R1H1
open OAI.Nagata OAI.Nagata.PG MvPolynomial OMA.S_wp_nagata_s_conjecture_on_curves
theorem aob (p : Fin 2 → ℂ) (m : ℕ) (F : PlanePoly)
    (h : F ∈ pointIdeal p ^ m) : OAI.Nagata.AM.oAL p m F := by
  have hle : pointIdeal p ≤ OAI.Nagata.AM.pointIdeal p := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact OAI.Nagata.AM.cdm p i
  exact (Ideal.pow_right_mono hle m) h
theorem ahl (F : PlanePoly) : ∃ G : MvPolynomial (Fin 3) ℂ,
    G.IsHomogeneous F.totalDegree ∧ W27.dCH 0 G = F := by
  classical
  let term (a : Fin 2 →₀ ℕ) : MvPolynomial (Fin 3) ℂ :=
    C (coeff a F) * X 0 ^ (F.totalDegree - (a 0 + a 1)) * X 1 ^ a 0 * X 2 ^ a 1
  refine ⟨∑ a ∈ F.support, term a, IsHomogeneous.sum _ _ _ ?_, ?_⟩
  · intro a ha
    have le := le_totalDegree ha
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at le
    have hh := (((isHomogeneous_C (Fin 3) (coeff a F)).mul
      ((isHomogeneous_X ℂ (0 : Fin 3)).pow (F.totalDegree - (a 0 + a 1)))).mul
      ((isHomogeneous_X ℂ (1 : Fin 3)).pow (a 0))).mul ((isHomogeneous_X ℂ (2 : Fin 3)).pow (a 1))
    convert hh using 1; omega
  · rw [map_sum]
    conv_rhs => rw [F.as_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp [term, W27.dCH, monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two, mul_assoc]
    exact Or.inl rfl
theorem uone {r : ℕ} (d : ℕ) (m : Fin r → ℕ) (hd : 0 < d)
    (hn : ¬ ∃ q : MvPolynomial (Fin r × Fin 2) ℂ, q ≠ 0 ∧
      ∀ p : Fin r → Fin 2 → ℂ, Function.Injective p → ∀ F : PlanePoly, F ≠ 0 →
      F.totalDegree = d → (∀ i, F ∈ pointIdeal (p i) ^ m i) →
      MvPolynomial.eval (fun ij => p ij.1 ij.2) q = 0) : W13.US r d m := by
  by_contra hU
  apply hn
  let t : Workers.W25.II r := (⟨d, hd⟩, m)
  have prop : W13.sL1 r t ≠ Set.univ := by
    intro h
    apply hU
    intro P
    exact Set.eq_univ_iff_forall.mp h P
  obtain ⟨Q, hn, hv⟩ := Workers.W25.eneop _
    (sLiCZ r t) prop
  refine ⟨W16.bD Q, W16.bDnz Q hn, ?_⟩
  intro p hp F hF hdeg hm
  let P : ODP r := ⟨aPP ∘ p, aPPi.comp hp⟩
  obtain ⟨G, hg, he⟩ := ahl F
  have hP : P ∈ W13.sL1 r t := by
    refine ⟨G, fun hz => hF (by simpa [hz] using he.symm), by change G.IsHomogeneous d; rwa [← hdeg], ?_⟩
    intro i
    have hc : (aPP (p i)).rep 0 ≠ 0 :=
      (mrcnz _ _ _).mpr (by simp [aPV])
    apply (mALid hg _ 0 hc _).mpr
    have hz : cC1 0 (aPP (p i)) = p i := by
      funext j
      change cC 0 (Projectivization.mk ℂ _ _) _ = _
      rw [cCm]
      fin_cases j <;> simp [aPV]
    rw [he, hz]
    exact aob _ _ _ (hm i)
  rw [W16.ebD]
  exact hv P hP (fun i => aPV (p i)) (fun i => aPVnz _) (fun _ => rfl)
end OMA.H3R1H1
open Filter Topology OAI.Nagata OAI.Nagata.Workers.W12 OAI.Nagata.CS
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2400000 in
theorem OMA.solution : OMA.R_wp_nagata_s_conjecture_on_curves_R1_H3_R1.H1 := by
  intro r hr hs d m hd hb hn
  obtain ⟨D, M, hm, hl, hu, u⟩ := OAI.Nagata.W13.ouou hr hs hd m hb
    (OMA.H3R1H1.uone d m hd hn)
  refine ⟨D, M, hm, hl, hu, ?_⟩
  intro n x hx hbx
  apply (sfsc (by omega) u n x hx hbx (3*(Real.sqrt r-3))).mono
  rintro t ⟨ht,ht1,U,hU,h0,h⟩
  refine ⟨ht,ht1,U,hU,h0,?_⟩
  intro p hp hpu
  obtain ⟨F,hF,hv⟩ := h p hp hpu
  refine ⟨F.val, fun hz => hF (Subtype.ext hz), F.property.1, ?_, hv⟩
  intro j
  have hc := F.property.2 j
  unfold cS at hc
  split <;> rename_i hj
  · rw [if_pos hj] at hc; exact hc
  · rw [if_neg hj] at hc; exact hc

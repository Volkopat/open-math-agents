import OMAReductions.R_Erdos114_erdos_114_variants_large_n_R1
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.Normed.Module.Connected

/-! The analytic steps are Lemmas 4–6 of Eremenko and Hayman, arXiv:0805.2295.
The translation and rotation in Tao's Proposition 1.2 are proved below.
Connectedness follows by lifting a radial homotopy over exterior regular values,
then using properness and openness to pass to the unit level. The existence
of a maximizer follows by compactness after translating one root to the origin.
With a distant root and one at zero, the level set lies in small disks around
the roots. The intersection count is proved by restricting a polynomial to a line. -/

namespace OMA.R_Erdos114_erdos_114_variants_large_n_R1_H1_R1

open Set Topology Polynomial Metric Filter Erdos114 MeasureTheory
open scoped unitInterval ENNReal

-- Upper semicontinuity of Hausdorff length as the list of roots varies.
def H1 : Prop :=
  ∀ n : ℕ, 0 < n →
    UpperSemicontinuous fun z : Fin n → ℂ => lemniscateLength (∏ i, (X - C (z i)))

-- A local length bound from the number of intersections with each line.
def H2 : Prop :=
  ∀ p : ℂ[X], 0 < p.natDegree →
    (∀ a b : ℂ, b ≠ 0 →
      {t : ℝ | ‖p.eval (a + (t : ℂ) * b)‖ = 1}.ncard ≤ 2 * p.natDegree) →
    ∀ a : ℂ, ∀ r : ℝ, 0 < r →
      μH[1] (lemniscate p ∩ closedBall a r) ≤ ENNReal.ofReal (16 * p.natDegree * r)

-- Deform an extremizer at constant length until all critical values are on the unit circle.
def H3 : Prop :=
  ∀ p : ℂ[X], p.Monic → 1 ≤ p.natDegree →
    (∀ r : ℂ[X], r.Monic → r.natDegree = p.natDegree →
      lemniscateLength r ≤ lemniscateLength p) →
    ∃ q : ℂ[X], q.Monic ∧ q.natDegree = p.natDegree ∧
      lemniscateLength q = lemniscateLength p ∧
      ∀ z : ℂ, q.derivative.eval z = 0 → z ∈ lemniscate q

private lemma exterior_connected {R : ℝ} (hR : 0 ≤ R) :
    IsConnected {z : ℂ | R < ‖z‖} := by
  let f : ℝ × ℝ → ℂ := fun p => p.1 • Complex.exp ((p.2 : ℂ) * Complex.I)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hConn := (isConnected_Ioi (a := R)).prod (isConnected_univ (α := ℝ))
  have hImage : f '' (Ioi R ×ˢ (univ : Set ℝ)) = {z : ℂ | R < ‖z‖} := by
    ext z
    constructor
    · rintro ⟨⟨r,t⟩, ⟨hr,-⟩, rfl⟩
      change R < ‖r • Complex.exp ((t : ℂ) * Complex.I)‖
      rwa [norm_smul, Real.norm_of_nonneg (hR.trans hr.le), Complex.norm_exp_ofReal_mul_I,
        mul_one]
    · intro hz
      exact ⟨(‖z‖, z.arg), ⟨hz, mem_univ _⟩, by
        simpa [f, Complex.real_smul] using Complex.norm_mul_exp_arg_mul_I z⟩
  exact hImage ▸ hConn.image f hf.continuousOn

private lemma closure_component_inter {U : Set ℂ} {x : ℂ} (hx : x ∈ U)
    :
    closure (connectedComponentIn U x) ∩ U ⊆ connectedComponentIn U x := by
  rw [connectedComponentIn_eq_image hx]
  intro z hz
  obtain ⟨hz₁, hz₂⟩ := hz
  refine ⟨⟨z, hz₂⟩, ?_, rfl⟩
  have hv : Continuous (Subtype.val : U → ℂ) := continuous_subtype_val
  have hcl := (IsInducing.subtypeVal : IsInducing (Subtype.val : U → ℂ)).closure_eq_preimage_closure_image
    (connectedComponent (⟨x, hx⟩ : U))
  rw [← isClosed_connectedComponent.closure_eq, hcl]
  exact hz₁

lemma polynomial_exterior_connected {p : ℂ[X]} (hp : 1 ≤ p.natDegree) :
    IsConnected {z : ℂ | 1 < ‖p.eval z‖} := by
  let V : Set ℂ := {w | 1 < ‖w‖}
  let U := p.eval ⁻¹' V
  have hV : IsConnected V := exterior_connected zero_le_one
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_norm).preimage p.continuous
  have hdeg : 0 < p.degree := by
    rw [degree_eq_natDegree (by intro h; simp [h] at hp)]
    exact_mod_cast (Nat.zero_lt_of_lt (by omega : 0 < p.natDegree))
  have hproper := p.isProperMap_eval hdeg
  have hmap := (p.isOpenQuotientMap_eval (by omega)).isOpenMap
  have hcpt := hproper.isCompact_preimage (isCompact_closedBall (0 : ℂ) 1)
  obtain ⟨R, hR⟩ := hcpt.isBounded.subset_closedBall (0 : ℂ)
  let T : Set ℂ := {z | max R 0 < ‖z‖}
  have hT : IsConnected T := exterior_connected (le_max_right _ _)
  have hTU : T ⊆ U := by
    intro z hz
    by_contra nh
    have hb : p.eval z ∈ closedBall (0 : ℂ) 1 := by
      simpa [U,V,dist_zero_right,not_lt] using nh
    have hc : z ∈ closedBall (0 : ℂ) R := hR hb
    have hd : ‖z‖ ≤ R := by simpa [dist_zero_right] using hc
    exact (not_lt_of_ge (hd.trans (le_max_left _ _))) hz
  obtain ⟨t, ht⟩ := hT.nonempty
  suffices hAll : U ⊆ connectedComponentIn U t by
    change IsConnected U
    rw [Subset.antisymm hAll (connectedComponentIn_subset U t)]
    exact isConnected_connectedComponentIn_iff.mpr (hTU ht)
  intro z hz
  let C := connectedComponentIn U z
  have hCU : C ⊆ U := connectedComponentIn_subset U z
  have hCOpen : IsOpen C := hU.connectedComponentIn
  have hCimg : p.eval '' C = p.eval '' closure C ∩ V := by
    ext w
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, subset_closure ha, rfl⟩, hCU ha⟩
    · rintro ⟨⟨a, ha, rfl⟩, hw⟩
      exact ⟨a, closure_component_inter hz ⟨ha, hw⟩, rfl⟩
  have hcl : IsClosed (p.eval '' closure C) := hproper.isClosedMap _ isClosed_closure
  have hCV : p.eval '' C = V := by
    have hs : V ⊆ p.eval '' C ∪ (p.eval '' closure C)ᶜ := by
      intro w hw
      by_cases h : w ∈ p.eval '' closure C
      · exact Or.inl (hCimg.symm ▸ ⟨h, hw⟩)
      · exact Or.inr h
    by_contra hne
    have ⟨w, hw, hw'⟩ := not_subset.mp (fun hs' => hne (Subset.antisymm (image_subset_iff.mpr hCU) hs'))
    obtain ⟨q, -, hqC, hq'⟩ := hV.isPreconnected _ _ (hmap _ hCOpen) hcl.isOpen_compl hs
      ⟨p.eval z, hz, ⟨z, mem_connectedComponentIn hz, rfl⟩⟩
      ⟨w, hw, fun h => hw' (hCimg.symm ▸ ⟨h, hw⟩)⟩
    exact hq' ((hCimg ▸ hqC).1)
  have hBound : Bornology.IsBounded (p.eval '' closedBall 0 (max R 0)) :=
    (isCompact_closedBall _ _).image p.continuous |>.isBounded
  obtain ⟨B, hB⟩ := hBound.subset_closedBall 0
  obtain ⟨w, hw⟩ := NormedField.exists_lt_norm ℂ (max B 1)
  have hwV : w ∈ V := lt_of_le_of_lt (le_max_right _ _) hw
  obtain ⟨a, ha, rfl⟩ := hCV.symm ▸ hwV
  have haT : a ∈ T := by
    by_contra nh
    have hb : a ∈ closedBall 0 (max R 0) := by
      rw [mem_closedBall, dist_zero_right]
      exact le_of_not_gt nh
    have hc : p.eval a ∈ closedBall 0 B := hB ⟨a, hb, rfl⟩
    rw [mem_closedBall, dist_zero_right] at hc
    exact hw.not_ge (hc.trans (le_max_left _ _))
  have htC : t ∈ C := by
    have hi := hT.isPreconnected.subset_connectedComponentIn haT hTU ht
    rw [← connectedComponentIn_eq ha] at hi
    exact hi
  rw [← connectedComponentIn_eq htC]
  exact mem_connectedComponentIn hz

lemma polynomial_level_connected {p : ℂ[X]} (hp : 1 ≤ p.natDegree)
    (hc : ∀ z : ℂ, p.derivative.eval z = 0 → ‖p.eval z‖ = 1)
    {r : ℝ} (hr : 1 < r) :
    IsConnected {z : ℂ | ‖p.eval z‖ = r} := by
  let V : Set ℂ := {w | 1 < ‖w‖}
  let U := p.eval ⁻¹' V
  let F : U → V := fun z => ⟨p.eval z, z.2⟩
  have hcover : IsCoveringMap F := by
    apply (p.isCoveringMapOn_eval.mono ?_).isCoveringMap_restrictPreimage
    intro w hw h
    obtain ⟨z, hz, rfl⟩ := h
    exact (ne_of_gt hw) (hc z hz)
  have hU : ConnectedSpace U :=
    isConnected_iff_connectedSpace.mp (polynomial_exterior_connected hp)
  let α (x : I × U) : ℝ := (1 - (x.1 : ℝ)) + (x.1 : ℝ) * r / ‖p.eval (x.2 : ℂ)‖
  let g (x : I × U) : ℂ := α x • p.eval (x.2 : ℂ)
  have hnorm (x : I × U) : ‖g x‖ =
      (1 - (x.1 : ℝ)) * ‖p.eval (x.2 : ℂ)‖ + (x.1 : ℝ) * r := by
    have hz : 0 < ‖p.eval (x.2 : ℂ)‖ := zero_lt_one.trans x.2.2
    have ha : 0 ≤ α x := add_nonneg (sub_nonneg.mpr x.1.2.2)
      (div_nonneg (mul_nonneg x.1.2.1 (zero_le_one.trans hr.le)) hz.le)
    change ‖α x • p.eval (x.2 : ℂ)‖ = _
    rw [norm_smul, Real.norm_of_nonneg ha]
    dsimp [α]
    field_simp
  have hg (x : I × U) : g x ∈ V := by
    have hx : 1 < ‖p.eval (x.2 : ℂ)‖ := x.2.2
    have hmin : 1 < min ‖p.eval (x.2 : ℂ)‖ r := lt_min hx hr
    change 1 < ‖g x‖
    rw [hnorm]
    refine hmin.trans_le ?_
    have h₁ := mul_le_mul_of_nonneg_left (min_le_left ‖p.eval (x.2 : ℂ)‖ r) (sub_nonneg.mpr x.1.2.2)
    have h₂ := mul_le_mul_of_nonneg_left (min_le_right ‖p.eval (x.2 : ℂ)‖ r) x.1.2.1
    linarith only [h₁, h₂]
  have hi : Continuous (fun x : I × U => (x.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have heval : Continuous (fun x : I × U => p.eval (x.2 : ℂ)) :=
    p.continuous.comp (continuous_subtype_val.comp continuous_snd)
  have hα : Continuous α :=
    (continuous_const.sub hi).add ((hi.mul_const r).div heval.norm
      fun x => (zero_lt_one.trans x.2.2).ne')
  let H : C(I × U, V) := ⟨fun x => ⟨g x, hg x⟩, (hα.smul heval).subtype_mk hg⟩
  have h0 (z : U) : H (0, z) = F ((ContinuousMap.id U) z) := by
    apply Subtype.ext
    change g (0,z) = p.eval (z : ℂ)
    simp [g, α]
  let L := hcover.liftHomotopy H (ContinuousMap.id U) h0
  have hL (t : I) (z : U) : F (L (t,z)) = H (t,z) :=
    congr_fun (hcover.liftHomotopy_lifts H (ContinuousMap.id U) h0) (t,z)
  have hL0 (z : U) : L (0,z) = z :=
    hcover.liftHomotopy_zero H (ContinuousMap.id U) h0 z
  let e (z : U) : ℂ := (L (1,z) : ℂ)
  have he : Continuous e := continuous_subtype_val.comp
    (L.continuous.comp (continuous_const.prodMk continuous_id))
  have hImage : Set.range e = {z : ℂ | ‖p.eval z‖ = r} := by
    ext z
    constructor
    · rintro ⟨w,rfl⟩
      have hh : p.eval (e w) = g (1,w) := congrArg Subtype.val (hL 1 w)
      change ‖p.eval (e w)‖ = r
      rw [hh, hnorm]
      simp
    · intro hz
      let w : U := ⟨z, by change 1 < ‖p.eval z‖; rwa [hz]⟩
      have hfixed (t : I) : H (t,w) = F w := by
        apply Subtype.ext
        change α (t,w) • p.eval z = p.eval z
        have ha : α (t,w) = 1 := by
          dsimp [α,w]
          rw [show ‖p.eval z‖ = r from hz]
          field_simp
          ring
        rw [ha, one_smul]
      have hconst : L (1,w) = L (0,w) :=
        hcover.const_of_comp (L.continuous.comp (continuous_id.prodMk continuous_const))
          (fun t₁ t₂ => (hL t₁ w).trans ((hfixed t₁).trans ((hfixed t₂).symm.trans (hL t₂ w).symm))) 1 0
      exact ⟨w, congrArg Subtype.val (hconst.trans (hL0 w))⟩
  exact hImage ▸ isConnected_range he

theorem polynomial_lemniscate_connected {p : ℂ[X]} (hp : 1 ≤ p.natDegree)
    (hc : ∀ z : ℂ, p.derivative.eval z = 0 → z ∈ Erdos114.lemniscate p) :
    IsConnected (Erdos114.lemniscate p) := by
  let S : Set ℂ := {z | ‖p.eval z‖ = 1}
  change IsConnected S
  have hopen := p.isOpenQuotientMap_eval (by omega)
  have hS : IsClosed S := isClosed_eq p.continuous.norm continuous_const
  have hdeg : 0 < p.degree := by
    rw [degree_eq_natDegree (by intro h; simp [h] at hp)]
    exact_mod_cast (show 0 < p.natDegree by omega)
  refine ⟨?_, ?_⟩
  · obtain ⟨z, hz⟩ := hopen.surjective 1
    exact ⟨z, by simp [S, hz]⟩
  intro u v hu hv huv hsu hsv
  by_contra hbad
  have hduv : Disjoint (S \ v) (S \ u) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact (huv hx.1).elim hy.2 hx.2
  obtain ⟨A, B, hA, hB, hSA, hSB, hab⟩ :=
    normal_separation (hS.sdiff hv) (hS.sdiff hu) hduv
  have hCover : S ⊆ A ∪ B := by
    intro z hz
    by_cases h : z ∈ v
    · have h' : z ∉ u := fun h' => hbad ⟨z, hz, h', h⟩
      exact Or.inr (hSB ⟨hz, h'⟩)
    · exact Or.inl (hSA ⟨hz, h⟩)
  obtain ⟨a, ha, hau⟩ := hsu
  obtain ⟨b, hb, hbv⟩ := hsv
  have haA : a ∈ A := hSA ⟨ha, fun hav => hbad ⟨a, ha, hau, hav⟩⟩
  have hbB : b ∈ B := hSB ⟨hb, fun hbu => hbad ⟨b, hb, hbu, hbv⟩⟩
  have hHit (D : Set ℂ) (hD : IsOpen D) {z : ℂ} (hz : z ∈ S) (hzD : z ∈ D) :
      ∀ᶠ r : ℝ in 𝓝[>] 1, ∃ w ∈ D, ‖p.eval w‖ = r := by
    have hmem : p.eval '' D ∈ 𝓝 (p.eval z) :=
      (hopen.isOpenMap D hD).mem_nhds (mem_image_of_mem _ hzD)
    have hpath : Tendsto (fun r : ℝ => r • p.eval z) (𝓝 1) (𝓝 (p.eval z)) := by
      have hcont : Continuous (fun r : ℝ => r • p.eval z) :=
        continuous_id.smul continuous_const
      have h := hcont.continuousAt (x := (1 : ℝ))
      unfold ContinuousAt at h
      simpa only [one_smul] using h
    have he : ∀ᶠ r : ℝ in 𝓝[>] 1, r • p.eval z ∈ p.eval '' D :=
      nhdsWithin_le_nhds (hpath.eventually hmem)
    filter_upwards [he, self_mem_nhdsWithin] with r hr hr'
    obtain ⟨w, hw, heq⟩ := hr
    refine ⟨w, hw, ?_⟩
    change p.eval w = r • p.eval z at heq
    have hr₁ : 1 < r := hr'
    rw [heq, norm_smul, Real.norm_of_nonneg (zero_le_one.trans hr₁.le),
      show ‖p.eval z‖ = 1 from hz, mul_one]
  let K := (p.eval ⁻¹' closedBall (0 : ℂ) 2) ∩ (A ∪ B)ᶜ
  let E := (fun z => ‖p.eval z‖) '' K
  have hKc : IsCompact K :=
    ((p.isProperMap_eval hdeg).isCompact_preimage (isCompact_closedBall _ _)).inter_right
      ((hA.union hB).isClosed_compl)
  have hEc : IsClosed E := (hKc.image p.continuous.norm).isClosed
  have h1 : (1 : ℝ) ∉ E := by
    rintro ⟨x, hx, heq⟩
    exact hx.2 (hCover heq)
  have hAvoid : ∀ᶠ r : ℝ in 𝓝[>] 1, r ∉ E :=
    nhdsWithin_le_nhds (hEc.isOpen_compl.mem_nhds h1)
  have hI : ∀ᶠ r : ℝ in 𝓝[>] 1, r ∈ Ioo 1 2 := Ioo_mem_nhdsGT (by norm_num)
  obtain ⟨r, ⟨hr, hr2⟩, hnot, ⟨x,hx,hxr⟩, ⟨y,hy,hyr⟩⟩ :=
    (hI.and (hAvoid.and ((hHit A hA ha haA).and (hHit B hB hb hbB)))).exists
  let Sr : Set ℂ := {z | ‖p.eval z‖ = r}
  have hSr : IsConnected Sr := polynomial_level_connected hp hc hr
  have hrCover : Sr ⊆ A ∪ B := by
    intro z hz
    by_contra hn
    have hzb : p.eval z ∈ closedBall (0 : ℂ) 2 := by
      rw [mem_closedBall, dist_zero_right, show ‖p.eval z‖ = r from hz]
      exact hr2.le
    exact hnot ⟨z, ⟨hzb, hn⟩, hz⟩
  obtain ⟨w, -, hwA, hwB⟩ := hSr.isPreconnected _ _ hA hB hrCover ⟨x,hxr,hx⟩ ⟨y,hyr,hy⟩
  exact disjoint_left.mp hab hwA hwB


lemma penultimate_taylor {p : ℂ[X]} (hp : p.Monic) (hn : 1 ≤ p.natDegree) (b : ℂ) :
    (p.taylor b).coeff (p.natDegree - 1) =
      p.coeff (p.natDegree - 1) + (p.natDegree : ℂ) * b := by
  let n := p.natDegree - 1
  have hn' : 1 + n = p.natDegree := by dsimp [n]; omega
  have hchoose : p.natDegree.choose n = p.natDegree := by
    rw [← hn', Nat.add_comm 1 n, Nat.choose_succ_self_right]
  have h : hasseDeriv n p = C (p.coeff n) + C (p.natDegree : ℂ) * X := by
    ext i
    rw [hasseDeriv_coeff, coeff_add, coeff_C_mul]
    rcases i with _ | i
    · simp
    rcases i with _ | i
    · rw [hn', hchoose, coeff_natDegree, hp.leadingCoeff]
      simp
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_X, if_neg (by omega)]
      simp
  change (p.taylor b).coeff n = p.coeff n + (p.natDegree : ℂ) * b
  rw [taylor_coeff, h]
  simp

lemma taylor_geometry (p : ℂ[X]) (b : ℂ) :
    lemniscateLength (p.taylor b) = lemniscateLength p ∧
    (IsConnected (lemniscate p) → IsConnected (lemniscate (p.taylor b))) ∧
    ((∀ z : ℂ, p.derivative.eval z = 0 → z ∈ lemniscate p) →
      (∀ z : ℂ, (p.taylor b).derivative.eval z = 0 → z ∈ lemniscate (p.taylor b))) := by
  let e := IsometryEquiv.addRight b
  have hset : lemniscate (p.taylor b) = e ⁻¹' lemniscate p := by
    ext z
    simp [lemniscate, taylor_apply, e, eval_comp]
  refine ⟨?_, ?_, ?_⟩
  · rw [lemniscateLength, hset, e.hausdorffMeasure_preimage]
    rfl
  · intro h
    rw [hset]
    exact e.toHomeomorph.isConnected_preimage.mpr h
  · intro h z hz
    have hv : p.derivative.eval (z + b) = 0 := by
      simpa [taylor_apply, derivative_comp, eval_comp] using hz
    rw [hset]
    exact h _ hv

lemma derivative_scale (p : ℂ[X]) (a : ℂ) :
    (p.scaleRoots a).derivative = p.derivative.scaleRoots a := by
  ext i
  rw [coeff_derivative, coeff_scaleRoots, coeff_scaleRoots, coeff_derivative, natDegree_derivative]
  rw [show p.natDegree - (i + 1) = p.natDegree - 1 - i by omega]
  ring

lemma scale_geometry (p : ℂ[X]) (a : ℂ) (ha : ‖a‖ = 1) :
    lemniscateLength (p.scaleRoots a) = lemniscateLength p ∧
    (IsConnected (lemniscate p) → IsConnected (lemniscate (p.scaleRoots a))) ∧
    ((∀ z : ℂ, p.derivative.eval z = 0 → z ∈ lemniscate p) →
      (∀ z : ℂ, (p.scaleRoots a).derivative.eval z = 0 → z ∈ lemniscate (p.scaleRoots a))) := by
  have ha₀ : a ≠ 0 := by
    intro h
    simp [h] at ha
  let e : ℂ ≃ᵢ ℂ :=
    ⟨Equiv.mulLeft₀ a ha₀, Isometry.of_dist_eq fun x y => by
      change dist (a * x) (a * y) = dist x y
      rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul, ha, one_mul]⟩
  have hset : e ⁻¹' lemniscate (p.scaleRoots a) = lemniscate p := by
    ext z
    change ‖(p.scaleRoots a).eval (a * z)‖ = 1 ↔ ‖p.eval z‖ = 1
    rw [scaleRoots_eval_mul, norm_mul, norm_pow, ha, one_pow, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · have hm := e.hausdorffMeasure_preimage 1 (lemniscate (p.scaleRoots a))
    rw [hset] at hm
    exact hm.symm
  · intro hc
    exact e.toHomeomorph.isConnected_preimage.mp (hset.symm ▸ hc)
  · intro hc z hz
    obtain ⟨w, rfl⟩ := e.surjective z
    change (p.scaleRoots a).derivative.eval (a * w) = 0 at hz
    rw [derivative_scale, scaleRoots_eval_mul] at hz
    have hroot := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ ha₀)
    have hw : w ∈ e ⁻¹' lemniscate (p.scaleRoots a) := hset.symm ▸ hc _ hroot
    exact hw

lemma unit_root_rotate (z : ℂ) {n : ℕ} (hn : 0 < n) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ a ^ n * z = - (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · exact ⟨1, by simp, by simp [hz]⟩
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (- (‖z‖ : ℂ) / z) hn
  have hpow : ‖a‖ ^ n = (1 : ℝ) ^ n := by
    rw [← norm_pow, ha]
    simp [norm_ne_zero_iff.mpr hz]
  exact ⟨a, (pow_left_inj₀ (norm_nonneg _) zero_le_one hn.ne').mp hpow,
    ((div_eq_iff hz).mp ha.symm).symm⟩

lemma normalize (p : ℂ[X]) (hp : p.Monic) (hn : 1 ≤ p.natDegree) :
    ∃ q : ℂ[X], q.Monic ∧ q.natDegree = p.natDegree ∧ q.coeff (p.natDegree - 1) = 0 ∧
    (q.eval 0).im = 0 ∧ (q.eval 0).re ≤ 0 ∧ lemniscateLength q = lemniscateLength p ∧
    (IsConnected (lemniscate p) → IsConnected (lemniscate q)) ∧
    ((∀ z : ℂ, p.derivative.eval z = 0 → z ∈ lemniscate p) →
      (∀ z : ℂ, q.derivative.eval z = 0 → z ∈ lemniscate q)) := by
  let b : ℂ := -p.coeff (p.natDegree - 1) / (p.natDegree : ℂ)
  let t := p.taylor b
  have htdeg : t.natDegree = p.natDegree := natDegree_taylor p b
  have htmonic : t.Monic := by unfold Monic; simpa [t] using hp.leadingCoeff
  have htc : t.coeff (p.natDegree - 1) = 0 := by
    have hn₀ : (p.natDegree : ℂ) ≠ 0 := by exact_mod_cast (show p.natDegree ≠ 0 by omega)
    dsimp [t]
    rw [penultimate_taylor hp hn]
    dsimp [b]
    field_simp
    ring
  obtain ⟨a, ha, ha0⟩ := unit_root_rotate (t.eval 0) (n := t.natDegree) (htdeg.symm ▸ hn)
  let q := t.scaleRoots a
  have hq0 : q.eval 0 = - (‖t.eval 0‖ : ℂ) := by
    simpa [q] using (scaleRoots_eval_mul t 0 a).trans ha0
  obtain ⟨htlen, htconn, htcrit⟩ := taylor_geometry p b
  obtain ⟨hqlen, hqconn, hqcrit⟩ := scale_geometry t a ha
  exact ⟨q, (monic_scaleRoots_iff _).mpr htmonic, (natDegree_scaleRoots _ _).trans htdeg,
    by simp [q, htc], by simp [hq0], by simp [hq0], hqlen.trans htlen,
    hqconn ∘ htconn, hqcrit ∘ htcrit⟩


private lemma roots_as_vector {p : ℂ[X]} (hp : p.Monic) {n : ℕ} (hd : p.natDegree = n) :
    ∃ z : Fin n → ℂ, p = ∏ i, (X - C (z i)) := by
  have hs : p.Splits := IsAlgClosed.splits p
  obtain ⟨l, hl⟩ := Quotient.exists_rep p.roots
  have hl' : (l : Multiset ℂ) = p.roots := hl
  have hlen : l.length = n := by
    rw [← hd, hs.natDegree_eq_card_roots, ← hl', Multiset.coe_card]
  let e : Fin n ≃ Fin l.length := finCongr hlen.symm
  refine ⟨fun i => l.get (e i), ?_⟩
  calc
    p = ∏ i : Fin l.length, (X - C (l.get i)) := by
      rw [hs.eq_prod_roots_of_monic hp, ← hl', Multiset.map_coe, Multiset.prod_coe,
        ← List.prod_ofFn]
      congr 1
      conv_lhs => rw [← List.ofFn_get l, List.map_ofFn]
      rfl
    _ = ∏ i : Fin n, (X - C (l.get (e i))) := (e.prod_comp _).symm

private lemma shift_roots {n : ℕ} (z : Fin n → ℂ) (b : ℂ) :
    (∏ i, (X - C (z i))).taylor b = ∏ i, (X - C (z i - b)) := by
  rw [taylor_apply, prod_comp]
  apply Finset.prod_congr rfl
  intro i _
  simp only [sub_comp, X_comp, C_comp, map_sub]
  ring

theorem exists_maximizer {n : ℕ} (hn : 0 < n)
    (hCont : UpperSemicontinuous fun z : Fin n → ℂ => lemniscateLength (∏ i, (X - C (z i))))
    (hDecay : ∀ ε : ℝ≥0∞, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧ ∀ z : Fin n → ℂ,
      z ⟨0, hn⟩ = 0 → (∃ i, R < ‖z i‖) →
      lemniscateLength (∏ i, (X - C (z i))) ≤ ε) :
    ∃ p : ℂ[X], p.Monic ∧ p.natDegree = n ∧
      ∀ q : ℂ[X], q.Monic → q.natDegree = n → lemniscateLength q ≤ lemniscateLength p := by
  let j : Fin n := ⟨0, hn⟩
  let P (z : Fin n → ℂ) : ℂ[X] := ∏ i, (X - C (z i))
  let L (z : Fin n → ℂ) := lemniscateLength (P z)
  have hmonic (z : Fin n → ℂ) : (P z).Monic :=
    monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)
  have hdegree (z : Fin n → ℂ) : (P z).natDegree = n := by
    unfold P
    rw [natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
    simp
  have hsurj (p : ℂ[X]) (hp : p.Monic) (hd : p.natDegree = n) :
      ∃ w : Fin n → ℂ, w j = 0 ∧ L w = lemniscateLength p := by
    obtain ⟨z, rfl⟩ := roots_as_vector hp hd
    refine ⟨fun i => z i - z j, sub_self _, ?_⟩
    dsimp only [L, P]
    rw [← shift_roots]
    exact (taylor_geometry _ _).1
  suffices h : ∃ z, ∀ w : Fin n → ℂ, w j = 0 → L w ≤ L z by
    obtain ⟨z, hz⟩ := h
    refine ⟨P z, hmonic z, hdegree z, ?_⟩
    intro p hp hd
    obtain ⟨w, hw, hwL⟩ := hsurj p hp hd
    rw [← hwL]
    exact hz w hw
  by_cases hpos : ∃ z : Fin n → ℂ, z j = 0 ∧ 0 < L z
  · obtain ⟨z, hz, hzpos⟩ := hpos
    obtain ⟨R, hR, hbound⟩ := hDecay (L z) hzpos
    let K := (Set.pi univ fun _ : Fin n => closedBall (0 : ℂ) R) ∪ {z}
    have hK : IsCompact K :=
      (isCompact_univ_pi fun _ : Fin n => isCompact_closedBall (0 : ℂ) R).union isCompact_singleton
    have hzK : z ∈ K := Or.inr rfl
    obtain ⟨a, ha, hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn ⟨z, hzK⟩ hK (hCont.upperSemicontinuousOn K)
    refine ⟨a, fun w hw => ?_⟩
    by_cases hwK : w ∈ K
    · exact hmax hwK
    · refine (hbound w hw ?_).trans (hmax hzK)
      by_contra! h
      exact hwK (Or.inl fun i _ => by simpa [dist_zero_right] using h i)
  · refine ⟨fun _ => 0, fun w hw => ?_⟩
    have hz : ¬ 0 < L w := fun h => hpos ⟨w, hw, h⟩
    exact (le_of_not_gt hz).trans bot_le


theorem ncard_level_line {p : ℂ[X]} {a b : ℂ}
    (hp : 0 < p.natDegree) (hb : b ≠ 0) :
    {t : ℝ | ‖p.eval (a + (t : ℂ) * b)‖ = 1}.ncard ≤ 2 * p.natDegree := by
  let q := p.comp (C b * X + C a)
  let c := starRingEnd ℂ
  let f := q * q.map c - 1
  have hq : q.natDegree = p.natDegree := by
    simp [q, natDegree_comp, natDegree_C_mul_X _ hb]
  have hq' : (q.map c).natDegree = q.natDegree :=
    natDegree_map_eq_of_injective c.injective q
  have hq₀ : q ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hq
    omega
  have hqc₀ : q.map c ≠ 0 := by
    intro h
    rw [h, natDegree_zero, hq] at hq'
    omega
  have hf : f.natDegree = 2 * p.natDegree := by
    dsimp [f]
    rw [← C_1, natDegree_sub_C, natDegree_mul hq₀ hqc₀, hq', hq]
    omega
  have hf₀ : f ≠ 0 := by
    intro he
    rw [he, natDegree_zero] at hf
    omega
  let S : Set ℝ := {t | ‖p.eval (a + (t : ℂ) * b)‖ = 1}
  have hMaps (t : ℝ) (ht : t ∈ S) : (t : ℂ) ∈ (f.roots.toFinset : Set ℂ) := by
    apply Finset.mem_coe.mpr
    rw [Multiset.mem_toFinset, mem_roots hf₀]
    change f.eval (t : ℂ) = 0
    have htEval : q.eval (t : ℂ) = p.eval (a + (t : ℂ) * b) := by
      simp [q, eval_comp, mul_comm b, add_comm a]
    have hc : c (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
    have hqEval : (q.map c).eval (t : ℂ) = c (q.eval (t : ℂ)) := by
      simpa only [hc] using eval_map_apply (p := q) (f := c) (t : ℂ)
    change ‖p.eval (a + (t : ℂ) * b)‖ = 1 at ht
    simp only [f, eval_sub, eval_mul, eval_one, hqEval]
    change q.eval (t : ℂ) * (starRingEnd ℂ) (q.eval (t : ℂ)) - 1 = 0
    rw [Complex.mul_conj, ← Complex.sq_norm, htEval, ht]
    norm_num
  calc
    S.ncard ≤ (f.roots.toFinset : Set ℂ).ncard :=
      ncard_le_ncard_of_injOn (fun t : ℝ => (t : ℂ)) hMaps Complex.ofReal_injective.injOn
        f.roots.toFinset.finite_toSet
    _ = f.roots.toFinset.card := ncard_coe_finset _
    _ ≤ f.roots.card := Multiset.toFinset_card_le _
    _ ≤ f.natDegree := card_roots' _
    _ = 2 * p.natDegree := hf


private lemma small_disk_cover {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ)
    (z : Fin n → ℂ) (hzero : z ⟨0, hn⟩ = 0) {k : Fin n}
    (hk : 2 / δ ^ (n - 1) < ‖z k‖) :
    lemniscate (∏ i, (X - C (z i))) ⊆ ⋃ i, closedBall (z i) δ := by
  intro x hx
  by_contra hx'
  have hdist (i : Fin n) : δ < dist x (z i) :=
    lt_of_not_ge fun hi => hx' (mem_iUnion.mpr ⟨i, mem_closedBall.mpr hi⟩)
  let q := 1 / δ ^ (n - 1)
  have hpair : q < dist x (z ⟨0, hn⟩) ∨ q < dist x (z k) := by
    by_contra! h
    have htri := dist_triangle (z ⟨0, hn⟩) x (z k)
    rw [hzero, dist_comm 0 (z k), dist_zero_right, dist_comm 0 x, ← hzero] at htri
    have he : 2 / δ ^ (n - 1) = q + q := by dsimp [q]; ring
    linarith only [h.1, h.2, htri, hk, he]
  obtain ⟨i, hi⟩ : ∃ i : Fin n, q < dist x (z i) :=
    hpair.elim (fun h => ⟨_, h⟩) (fun h => ⟨_, h⟩)
  let otherRoots := (Finset.univ : Finset (Fin n)).erase i
  have hI : otherRoots.card = n - 1 := by simp [otherRoots]
  have hprod : δ ^ (n - 1) ≤ ∏ j ∈ otherRoots, dist x (z j) := by
    rw [← hI, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => hδ.le) fun j _ => (hdist j).le
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq' : q * δ ^ (n - 1) = 1 := by
    dsimp [q]
    field_simp
  have hlen : (∏ j, dist x (z j)) = 1 := by
    change ‖(∏ j, (X - C (z j))).eval x‖ = 1 at hx
    simpa only [eval_prod, eval_sub, eval_X, eval_C, norm_prod, dist_eq_norm] using hx
  have hlt : 1 < ∏ j, dist x (z j) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    calc
      1 = q * δ ^ (n - 1) := hq'.symm
      _ ≤ q * (∏ j ∈ otherRoots, dist x (z j)) := mul_le_mul_of_nonneg_left hprod hq
      _ < dist x (z i) * (∏ j ∈ otherRoots, dist x (z j)) :=
        mul_lt_mul_of_pos_right hi (lt_of_lt_of_le (by positivity) hprod)
  exact (not_lt_of_ge hlen.le) hlt

theorem decay_of_disk_bound
    (disk : ∀ p : ℂ[X], 0 < p.natDegree → ∀ a : ℂ, ∀ r : ℝ, 0 < r →
      μH[1] (lemniscate p ∩ closedBall a r) ≤ ENNReal.ofReal (16 * p.natDegree * r))
    (n : ℕ) (hn : 0 < n) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ z : Fin n → ℂ, z ⟨0, hn⟩ = 0 →
      (∃ i, R < ‖z i‖) → lemniscateLength (∏ i, (X - C (z i))) ≤ ε := by
  by_cases htop : ε = ⊤
  · exact ⟨0, le_rfl, fun _ _ _ => htop.symm ▸ le_top⟩
  have hεR : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
  let δ := ε.toReal / (16 * (n : ℝ)^2)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let R := 2 / δ ^ (n-1)
  refine ⟨R, by dsimp [R]; positivity, ?_⟩
  intro z hz hfar
  obtain ⟨i, hi⟩ := hfar
  let p : ℂ[X] := ∏ j, (X - C (z j))
  have hp : p.natDegree = n := by
    unfold p
    rw [natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
    simp
  have hcover := small_disk_cover hn hδ z hz hi
  have hsub : lemniscate p ⊆ ⋃ j, lemniscate p ∩ closedBall (z j) δ := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hx)
    exact mem_iUnion.mpr ⟨j, hx, hj⟩
  calc
    lemniscateLength p ≤ μH[1] (⋃ j, lemniscate p ∩ closedBall (z j) δ) :=
      measure_mono hsub
    _ ≤ ∑' j, μH[1] (lemniscate p ∩ closedBall (z j) δ) := measure_iUnion_le _
    _ ≤ ∑' _ : Fin n, ENNReal.ofReal (16 * (n : ℝ) * δ) := by
      apply ENNReal.tsum_le_tsum
      intro j
      simpa [hp] using disk p (hp.symm ▸ hn) (z j) δ hδ
    _ = ε := by
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      have hEq : (n : ℝ) * (16 * (n : ℝ) * δ) = ε.toReal := by
        dsimp [δ]
        field_simp
      rw [hEq, ENNReal.ofReal_toReal htop]


theorem main : H1 → H2 → H3 → OMA.R_Erdos114_erdos_114_variants_large_n_R1.H1 := by
  intro hContinuous hDisk hDeform n hn
  have hDecay := decay_of_disk_bound
    (fun p hp => hDisk p hp (fun _ _ hb => ncard_level_line hp hb)) n hn
  obtain ⟨p, hp, hpdeg, hpmax⟩ := exists_maximizer hn (hContinuous n hn) hDecay
  obtain ⟨q, hq, hqdeg, hqlen, hqcrit⟩ :=
    hDeform p hp (hpdeg.symm ▸ hn) (fun r hr hd => hpmax r hr (hd.trans hpdeg))
  have hqn : q.natDegree = n := hqdeg.trans hpdeg
  have hqpos : 1 ≤ q.natDegree := hqn.symm ▸ hn
  obtain ⟨r, hr, hrdeg, hcoeff, him, hre, hrlen, hconn, hcrit⟩ :=
    normalize q hq hqpos
  refine ⟨r, hr, hrdeg.trans hqn, hqn ▸ hcoeff, him, hre,
    hconn (polynomial_lemniscate_connected hqpos hqcrit), hcrit hqcrit, ?_⟩
  rw [hrlen, hqlen]
  exact hpmax

end OMA.R_Erdos114_erdos_114_variants_large_n_R1_H1_R1

import FormalConjectures.Mathoverflow.«235893»

/-!
A planar counterexample to inverse preservation of connectedness.

The recurrent tube and gate argument are adapted from Peter Lim,
*Recurrent tubes and connectedness-preserving bijections of Euclidean spaces*
(https://hub.valency.io/works/W_886e5r9q). Here each pair of successive extensions
visits two basis opens. The lateral arc joining their sections lets each track
meet both sides of any proposed separation.
-/

open Set Function Metric Mathoverflow235893
open scoped NNReal

namespace OMA.Recurrent

abbrev Plane := ℝ × ℝ

-- A Lipschitz perturbation of the identity moves a point with support in a closed ball.
theorem moveInBall (a b : Plane) {r : ℝ} (hr : 0 < r) (hb : b ∈ ball a r) :
    ∃ e : Plane ≃ₜ Plane, e a = b ∧ ∀ x ∉ ball a r, e x = x := by
  let c : ℝ≥0 := ‖b - a‖₊ * ⟨r⁻¹, inv_nonneg.mpr hr.le⟩
  let bump (x : Plane) := max 0 (1 - dist x a * r⁻¹)
  let g (x : Plane) := bump x • (b - a)
  have hbump : LipschitzWith (⟨r⁻¹, inv_nonneg.mpr hr.le⟩ : ℝ≥0) bump := by
    have h : LipschitzWith (⟨r⁻¹, inv_nonneg.mpr hr.le⟩ : ℝ≥0)
        (fun x : Plane => 1 - dist x a * r⁻¹) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [Real.dist_eq, show 1 - dist x a * r⁻¹ - (1 - dist y a * r⁻¹) =
        (dist y a - dist x a) * r⁻¹ by ring, abs_mul, abs_of_pos (inv_pos.mpr hr), mul_comm]
      exact mul_le_mul_of_nonneg_left (dist_comm y x ▸ abs_dist_sub_le y x a) (inv_nonneg.mpr hr.le)
    have hconst := (LipschitzWith.const (α := Plane) (0 : ℝ)).max h
    have hmax : max (0 : ℝ≥0) ⟨r⁻¹, inv_nonneg.mpr hr.le⟩ =
        ⟨r⁻¹, inv_nonneg.mpr hr.le⟩ := max_eq_right zero_le
    rw [hmax] at hconst
    exact hconst
  have hg : LipschitzWith c g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, show g x - g y = (bump x - bump y) • (b - a) by
      simp [g, sub_smul], norm_smul, Real.norm_eq_abs]
    have h := hbump.dist_le_mul x y
    rw [Real.dist_eq] at h
    change |bump x - bump y| * ‖b - a‖ ≤ (‖b - a‖ * r⁻¹) * dist x y
    calc
      _ ≤ (r⁻¹ * dist x y) * ‖b - a‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
      _ = _ := by ring
  let idL := ContinuousLinearEquiv.refl ℝ Plane
  have happrox : ApproximatesLinearOn (fun x => x + g x) idL.toContinuousLinearMap univ c := by
    intro x _ y _
    change ‖x + g x - (y + g y) - (x - y)‖ ≤ (c : ℝ) * ‖x - y‖
    rw [show x + g x - (y + g y) - (x - y) = g x - g y by abel, ← dist_eq_norm, ← dist_eq_norm]
    exact hg.dist_le_mul x y
  have hc : c < 1 := by
    change ‖b - a‖ * r⁻¹ < 1
    rw [← dist_eq_norm, ← div_eq_mul_inv, div_lt_one hr]
    exact hb
  have hnorm : ‖idL.symm.toContinuousLinearMap‖₊ = 1 := ContinuousLinearMap.nnnorm_id
  let e := happrox.toHomeomorph (fun x => x + g x) (Or.inr (by simpa [hnorm] using hc))
  refine ⟨e, ?_, ?_⟩
  · change a + g a = b
    simp [g, bump]
  · intro x hx
    change x + g x = x
    have hxr : r ≤ dist x a := le_of_not_gt hx
    have hmul : 1 ≤ dist x a * r⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hr, one_mul]
      exact hxr
    simp [g, bump, max_eq_left (sub_nonpos.mpr hmul)]

theorem moveOutside {K : Set Plane} (ho : IsOpen Kᶜ) (hc : IsPreconnected Kᶜ)
    {a b : Plane} (ha : a ∈ Kᶜ) (hb : b ∈ Kᶜ) :
    ∃ e : Plane ≃ₜ Plane, e a = b ∧ ∀ x ∈ K, e x = x := by
  let O : Set Plane := {p | ∃ e : Plane ≃ₜ Plane, e a = p ∧ ∀ x ∈ K, e x = x}
  have hO : O ⊆ Kᶜ := by
    rintro p ⟨e, rfl, he⟩ hp
    exact ha (show a ∈ K from e.injective (he _ hp) ▸ hp)
  have extend {p q : Plane} {r : ℝ} (hr : 0 < r) (hball : ball p r ⊆ Kᶜ)
      (hq : q ∈ ball p r) :
      ∃ e : Plane ≃ₜ Plane, e p = q ∧ ∀ x ∈ K, e x = x := by
    obtain ⟨e, he, hfix⟩ := moveInBall p q hr hq
    exact ⟨e, he, fun x hx => hfix x (fun hx' => hball hx' hx)⟩
  have hopen : IsOpen O := by
    apply Metric.isOpen_iff.mpr
    intro p hp
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp ho p (hO hp)
    refine ⟨r, hr, fun q hq => ?_⟩
    obtain ⟨e, he, hfix⟩ := hp
    obtain ⟨d, hd, hdfix⟩ := extend hr hball hq
    exact ⟨e.trans d, by simp [he, hd], fun x hx => by simp [hfix x hx, hdfix x hx]⟩
  have hother : IsOpen (Kᶜ \ O) := by
    apply Metric.isOpen_iff.mpr
    intro p hp
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp ho p hp.1
    refine ⟨r, hr, fun q hq => ⟨hball hq, ?_⟩⟩
    rintro ⟨e, he, hfix⟩
    obtain ⟨d, hd, hdfix⟩ := extend hr hball hq
    apply hp.2
    refine ⟨e.trans d.symm, ?_, fun x hx => ?_⟩
    · change d.symm (e a) = p
      rw [he, ← hd, d.symm_apply_apply]
    · change d.symm (e x) = x
      apply d.injective
      simpa only [d.apply_symm_apply, hfix x hx] using (hdfix x hx).symm
  by_contra h
  have hmem : a ∈ O := ⟨Homeomorph.refl _, rfl, fun _ _ => rfl⟩
  have hcover : Kᶜ ⊆ O ∪ (Kᶜ \ O) := by
    intro x hx
    by_cases hxo : x ∈ O
    · exact Or.inl hxo
    · exact Or.inr ⟨hx, hxo⟩
  obtain ⟨x, _, hleft, _, hright⟩ := hc O (Kᶜ \ O) hopen hother hcover
    ⟨a, ha, hmem⟩ ⟨b, hb, hb, h⟩
  exact hright hleft

def tubePrefix (k : ℝ) : Set Plane := Iic k ×ˢ Icc (-1) 1

def strip : Set Plane := univ ×ˢ Ioo (-1) 1

theorem isClosed_tubePrefix (k : ℝ) : IsClosed (tubePrefix k) := isClosed_Iic.prod isClosed_Icc

theorem preconnected_tubePrefix_compl (k : ℝ) : IsPreconnected (tubePrefix k)ᶜ := by
  let R : Set Plane := Ioi k ×ˢ univ
  let T : Set Plane := univ ×ˢ Ioi 1
  let B : Set Plane := univ ×ˢ Iio (-1)
  have hR : IsConnected R := isConnected_Ioi.prod isConnected_univ
  have hT : IsConnected T := isConnected_univ.prod isConnected_Ioi
  have hB : IsConnected B := isConnected_univ.prod isConnected_Iio
  have hRT : (R ∩ T).Nonempty := ⟨(k+1, 2), by norm_num [R, T]⟩
  have hRB : ((R ∪ T) ∩ B).Nonempty := ⟨(k+1, -2), by
    refine ⟨Or.inl ?_, ?_⟩ <;> norm_num [R, B]⟩
  have heq : (tubePrefix k)ᶜ = (R ∪ T) ∪ B := by
    ext p
    simp only [tubePrefix, R, T, B, mem_compl_iff, mem_prod, mem_Iic, mem_Icc, mem_union,
      mem_Ioi, mem_Iio, mem_univ, and_true, true_and]
    constructor
    · intro h
      by_contra! hn
      exact h ⟨hn.1.1, hn.2, hn.1.2⟩
    · rintro ((h | h) | h) h'
      · exact (not_lt_of_ge h'.1) h
      · exact (not_lt_of_ge h'.2.2) h
      · exact (not_lt_of_ge h'.2.1) h
  rw [heq]
  exact (IsConnected.union hRB (IsConnected.union hRT hR hT) hB).isPreconnected

def width (c ρ x : ℝ) : ℝ := min 1 (ρ + |x - c|)

theorem width_pos {ρ : ℝ} (hρ : 0 < ρ) (c x : ℝ) : 0 < width c ρ x :=
  lt_min (by norm_num) (lt_of_lt_of_le hρ (le_add_of_nonneg_right (abs_nonneg _)))

noncomputable def squeeze (c ρ : ℝ) (hρ : 0 < ρ) : Plane ≃ₜ Plane where
  toFun p := (p.1, width c ρ p.1 * p.2)
  invFun p := (p.1, p.2 / width c ρ p.1)
  left_inv p := by
    ext <;> simp [ne_of_gt (width_pos hρ c p.1)]
  right_inv p := by
    ext
    · rfl
    · change width c ρ p.1 * (p.2 / width c ρ p.1) = p.2
      field_simp [ne_of_gt (width_pos hρ c p.1)]
  continuous_toFun := by
    apply continuous_fst.prodMk
    exact ((continuous_const.min ((continuous_const.add
      (continuous_fst.sub continuous_const).abs))) : Continuous (fun p : Plane => width c ρ p.1)).mul
      continuous_snd
  continuous_invFun := by
    apply continuous_fst.prodMk
    exact continuous_snd.div
      ((continuous_const.min (continuous_const.add
        (continuous_fst.sub continuous_const).abs)) : Continuous (fun p : Plane => width c ρ p.1))
      (fun p => ne_of_gt (width_pos hρ c p.1))

theorem squeeze_fix (k ρ : ℝ) (hρ : 0 < ρ) {p : Plane} (hp : p ∈ tubePrefix k) :
    squeeze (k+1) ρ hρ p = p := by
  have hx : p.1 ≤ k := hp.1
  have hc : p.1 - (k+1) ≤ 0 := by linarith
  have hw : width (k+1) ρ p.1 = 1 := by
    rw [width, abs_of_nonpos hc, min_eq_left]
    linarith
  change (p.1, width (k+1) ρ p.1 * p.2) = p
  simp [hw]

def sectionAt (x : ℝ) : Set Plane := {x} ×ˢ Icc (-1) 1

theorem extendStage (e : Plane ≃ₜ Plane) (k : ℝ) {U : Set Plane} (hU : IsOpen U) :
    ∃ d : Plane ≃ₜ Plane, EqOn d e (tubePrefix k) ∧
      ((U \ (e '' tubePrefix k)).Nonempty → d '' sectionAt (k+1) ⊆ U) := by
  classical
  by_cases h : (U \ (e '' tubePrefix k)).Nonempty
  · obtain ⟨p, hpU, hp⟩ := h
    have hcomp : (e '' tubePrefix k)ᶜ = e '' (tubePrefix k)ᶜ :=
      (e.toEquiv.image_compl _).symm
    have ha : e (k+1, 0) ∈ (e '' tubePrefix k)ᶜ := by
      rw [hcomp]
      apply mem_image_of_mem
      intro hh
      have hk : k+1 ≤ k := hh.1
      linarith
    obtain ⟨g, hg, hfix⟩ := moveOutside ((e.isClosedMap _ (isClosed_tubePrefix k)).isOpen_compl)
      (hcomp ▸ (preconnected_tubePrefix_compl k).image e e.continuous.continuousOn) ha hp
    let q := e.trans g
    have hqp : q (k+1, 0) = p := hg
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hU.preimage q.continuous)
      (k+1, 0) (show q (k+1, 0) ∈ U from hqp ▸ hpU)
    let ρ := min (1 : ℝ) (r / 2)
    have hρ : 0 < ρ := lt_min (by norm_num) (by linarith)
    have hρ₁ : ρ ≤ 1 := min_le_left ..
    have hρr : ρ < r := (min_le_right _ _).trans_lt (by linarith)
    let d := (squeeze (k+1) ρ hρ).trans q
    refine ⟨d, ?_, fun _ => ?_⟩
    · intro x hx
      change q (squeeze (k+1) ρ hρ x) = e x
      rw [squeeze_fix k ρ hρ hx]
      exact hfix (e x) (mem_image_of_mem _ hx)
    · rintro _ ⟨⟨x,y⟩, hx, rfl⟩
      have hx' : x = k+1 := hx.1
      subst x
      change q (squeeze (k+1) ρ hρ (k+1,y)) ∈ U
      apply hball
      have hy : |y| ≤ 1 := abs_le.mpr hx.2
      have hwidth : width (k+1) ρ (k+1) = ρ := by simp [width, min_eq_right hρ₁]
      change dist ((k+1), width (k+1) ρ (k+1) * y) ((k+1), 0) < r
      rw [hwidth, Prod.dist_eq, dist_self, Real.dist_eq, sub_zero, abs_mul, abs_of_pos hρ,
        max_eq_right (mul_nonneg hρ.le (abs_nonneg _))]
      exact (mul_le_of_le_one_right hρ.le hy).trans_lt hρr
  · exact ⟨e, fun _ _ => rfl, fun hn => (h hn).elim⟩

noncomputable def tubeStage (U : ℕ → Set Plane) (hU : ∀ i, IsOpen (U i)) :
    ℕ → Plane ≃ₜ Plane
  | 0 => Homeomorph.refl Plane
  | n+1 => (extendStage (tubeStage U hU n) n (hU n)).choose

theorem tubeStage_fix (U : ℕ → Set Plane) (hU : ∀ i, IsOpen (U i)) (n : ℕ) :
    EqOn (tubeStage U hU (n+1)) (tubeStage U hU n) (tubePrefix n) :=
  (extendStage (tubeStage U hU n) n (hU n)).choose_spec.1

theorem tubeStage_hits (U : ℕ → Set Plane) (hU : ∀ i, IsOpen (U i)) (n : ℕ)
    (hn : (U n \ (tubeStage U hU n '' tubePrefix n)).Nonempty) :
    tubeStage U hU (n+1) '' sectionAt ((n : ℝ)+1) ⊆ U n :=
  (extendStage (tubeStage U hU n) n (hU n)).choose_spec.2 hn

theorem tubeStage_agree (U : ℕ → Set Plane) (hU : ∀ i, IsOpen (U i))
    {n m : ℕ} (hnm : n ≤ m) :
    EqOn (tubeStage U hU m) (tubeStage U hU n) (tubePrefix n) := by
  induction m, hnm using Nat.le_induction with
  | base => exact fun _ _ => rfl
  | succ m hnm ih =>
    intro p hp
    have hp' : p ∈ tubePrefix m := ⟨mem_Iic.mpr ((mem_Iic.mp hp.1).trans (Nat.cast_le.mpr hnm)), hp.2⟩
    exact (tubeStage_fix U hU m hp').trans (ih hp)

noncomputable def tubeMap (U : ℕ → Set Plane) (hU : ∀ i, IsOpen (U i)) (p : Plane) : Plane :=
  tubeStage U hU ((exists_nat_gt p.1).choose) p

theorem tubeMap_eq (U : ℕ → Set Plane) (hU : ∀ i, IsOpen (U i)) (n : ℕ) :
    EqOn (tubeMap U hU) (tubeStage U hU n) (tubePrefix n) := by
  intro p hp
  let m := (exists_nat_gt p.1).choose
  have hm : p.1 < (m : ℝ) := (exists_nat_gt p.1).choose_spec
  change tubeStage U hU m p = tubeStage U hU n p
  rcases le_total n m with h | h
  · exact tubeStage_agree U hU h hp
  · exact (tubeStage_agree U hU h ⟨hm.le, hp.2⟩).symm

theorem tubeMap_inj (U : ℕ → Set Plane) (hU : ∀ i, IsOpen (U i)) :
    InjOn (tubeMap U hU) (univ ×ˢ Icc (-1) 1) := by
  intro p hp q hq he
  obtain ⟨n, hn⟩ := exists_nat_gt (max p.1 q.1)
  have hp' : p ∈ tubePrefix n := ⟨(le_max_left _ _).trans hn.le, hp.2⟩
  have hq' : q ∈ tubePrefix n := ⟨(le_max_right _ _).trans hn.le, hq.2⟩
  exact (tubeStage U hU n).injective
    ((tubeMap_eq U hU n hp').symm.trans (he.trans (tubeMap_eq U hU n hq')))

theorem tubeMap_cont (U : ℕ → Set Plane) (hU : ∀ i, IsOpen (U i)) :
    ContinuousOn (tubeMap U hU) strip := by
  intro p hp
  obtain ⟨n, hn⟩ := exists_nat_gt p.1
  let S : Set Plane := Iio (n : ℝ) ×ˢ Ioo (-1) 1
  have hS : IsOpen S := isOpen_Iio.prod isOpen_Ioo
  have hmem : p ∈ S := ⟨hn, hp.2⟩
  have hEq : tubeMap U hU =ᶠ[nhds p] tubeStage U hU n := by
    filter_upwards [hS.mem_nhds hmem] with q (hq : q ∈ S)
    exact tubeMap_eq U hU n ⟨mem_Iic.mpr ((mem_Iio.mp hq.1).le), Ioo_subset_Icc_self hq.2⟩
  exact ((tubeStage U hU n).continuous.continuousAt.congr_of_eventuallyEq hEq).continuousWithinAt

def tubeComplement (g : Plane → Plane) : Set Plane := (g '' strip)ᶜ

theorem tube_lateral (U : ℕ → Set Plane) (hU : ∀ i, IsOpen (U i)) (x : ℝ) :
    tubeMap U hU (x, 1) ∈ tubeComplement (tubeMap U hU) := by
  rintro ⟨p, hp, he⟩
  have hp' : p ∈ univ ×ˢ Icc (-1 : ℝ) 1 := ⟨trivial, Ioo_subset_Icc_self hp.2⟩
  have hx' : (x, (1 : ℝ)) ∈ univ ×ˢ Icc (-1 : ℝ) 1 := by simp
  have heq := tubeMap_inj U hU hp' hx' he
  have hlt : p.2 < 1 := hp.2.2
  rw [heq] at hlt
  exact (lt_irrefl _ hlt)

theorem tubeMap_hits (U : ℕ → Set Plane) (hU : ∀ i, IsOpen (U i)) (n : ℕ)
    (hn : (U n ∩ tubeComplement (tubeMap U hU)).Nonempty) :
    tubeMap U hU '' sectionAt ((n : ℝ)+1) ⊆ U n := by
  have hsub : interior (tubeStage U hU n '' tubePrefix n) ⊆ tubeMap U hU '' strip := by
    rw [← Homeomorph.image_interior, tubePrefix, interior_prod_eq, interior_Iic, interior_Icc]
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨p, ⟨trivial, hp.2⟩, tubeMap_eq U hU n ⟨mem_Iic.mpr ((mem_Iio.mp hp.1).le), Ioo_subset_Icc_self hp.2⟩⟩
  obtain ⟨p, hpU, hpL⟩ := hn
  have hp' : p ∈ closure ((tubeStage U hU n '' tubePrefix n)ᶜ) := by
    rw [closure_compl]
    exact fun h => hpL (hsub h)
  have hnon := mem_closure_iff.mp hp' (U n) (hU n) hpU
  have hh := tubeStage_hits U hU n (show (U n \ (tubeStage U hU n '' tubePrefix n)).Nonempty from hnon)
  rintro _ ⟨q, hq, rfl⟩
  have hq' : q ∈ tubePrefix (↑(n+1 : ℕ)) := by
    refine ⟨?_, hq.2⟩
    have he : q.1 = (n : ℝ)+1 := hq.1
    simp [he]
  rw [tubeMap_eq U hU (n+1) hq']
  exact hh (mem_image_of_mem _ hq)

def lateralArc (g : Plane → Plane) (a b : ℝ) : Set Plane :=
  (fun x : ℝ => g (x, 1)) '' Icc a b

private theorem lateralArc_eq_stage (U : ℕ → Set Plane) (hU : ∀ i, IsOpen (U i))
    {a b : ℝ} {n : ℕ} (hn : b ≤ n) :
    lateralArc (tubeMap U hU) a b =
      (fun x : ℝ => tubeStage U hU n (x, 1)) '' Icc a b := by
  apply image_congr
  intro x hx
  exact tubeMap_eq U hU n ⟨hx.2.trans hn, by norm_num⟩

theorem lateralArc_connected (U : ℕ → Set Plane) (hU : ∀ i, IsOpen (U i))
    {a b : ℝ} (hab : a ≤ b) :
    IsConnected (lateralArc (tubeMap U hU) a b) := by
  obtain ⟨n, hn⟩ := exists_nat_gt b
  rw [lateralArc_eq_stage U hU hn.le]
  exact (isConnected_Icc hab).image _
    ((tubeStage U hU n).continuous.comp (continuous_id.prodMk continuous_const)).continuousOn

theorem lateralArc_closed (U : ℕ → Set Plane) (hU : ∀ i, IsOpen (U i)) (a b : ℝ) :
    IsClosed (lateralArc (tubeMap U hU) a b) := by
  obtain ⟨n, hn⟩ := exists_nat_gt b
  rw [lateralArc_eq_stage U hU hn.le]
  exact (isCompact_Icc.image
    ((tubeStage U hU n).continuous.comp (continuous_id.prodMk continuous_const))).isClosed

open TopologicalSpace

abbrev PlaneBasis := countableBasis Plane

noncomputable def tubeRequest (j : ℕ) : ℕ × (Set Plane × Set Plane) :=
  match Encodable.decode (α := ℕ × PlaneBasis × PlaneBasis) (Nat.unpair j).1 with
  | some (m, B, C) => (m, B.1, C.1)
  | none => (0, ∅, ∅)

theorem tubeRequest_onto (m : ℕ) (B C : PlaneBasis) (M : ℕ) :
    ∃ j ≥ M, tubeRequest j = (m, B.1, C.1) := by
  refine ⟨Nat.pair (Encodable.encode (m, B, C)) M, Nat.right_le_pair _ _, ?_⟩
  simp [tubeRequest, Nat.unpair_pair, Encodable.encodek]

noncomputable def scheduled (n : ℕ) : Set Plane :=
  if n % 2 = 0 then (tubeRequest (n / 2)).2.1 else (tubeRequest (n / 2)).2.2

theorem scheduled_open (n : ℕ) : IsOpen (scheduled n) := by
  unfold scheduled tubeRequest
  split <;> split
  all_goals first | exact isOpen_empty | exact isOpen_of_mem_countableBasis (Subtype.property _)

theorem scheduled_even (j : ℕ) : scheduled (2*j) = (tubeRequest j).2.1 := by
  simp [scheduled, show (2*j) % 2 = 0 by omega, show (2*j) / 2 = j by omega]

theorem scheduled_odd (j : ℕ) : scheduled (2*j+1) = (tubeRequest j).2.2 := by
  simp [scheduled, show (2*j+1) / 2 = j by omega]

noncomputable abbrev recurrentMap := tubeMap scheduled scheduled_open

noncomputable abbrev residual : Set Plane := tubeComplement recurrentMap

noncomputable def stageArc (j : ℕ) : Set Plane :=
  lateralArc recurrentMap (2*(j : ℝ)+1) (2*(j : ℝ)+2)

noncomputable def track (m : ℕ) : Set Plane :=
  ⋃ j : ℕ, ⋃ (_ : (tubeRequest j).1 = m), stageArc j

theorem arc_subset_track {j m : ℕ} (hj : (tubeRequest j).1 = m) :
    stageArc j ⊆ track m := by
  intro p hp
  exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hj, hp⟩⟩

theorem track_subset_residual (m : ℕ) : track m ⊆ residual := by
  intro p hp
  obtain ⟨j, hj⟩ := mem_iUnion.mp hp
  obtain ⟨_, z, _, rfl⟩ := mem_iUnion.mp hj
  exact tube_lateral scheduled scheduled_open z

theorem lateral_injective : Injective (fun x : ℝ => recurrentMap (x, 1)) := by
  intro x y he
  have h := tubeMap_inj scheduled scheduled_open
    (show (x, 1) ∈ univ ×ˢ Icc (-1 : ℝ) 1 by simp)
    (show (y, 1) ∈ univ ×ˢ Icc (-1 : ℝ) 1 by simp) he
  exact congrArg Prod.fst h

theorem tracks_disjoint : Pairwise (Disjoint on track) := by
  intro m k hmk
  apply Set.disjoint_left.mpr
  intro p hpm hpk
  obtain ⟨j, hj⟩ := mem_iUnion.mp hpm
  obtain ⟨i, hi⟩ := mem_iUnion.mp hpk
  obtain ⟨hjm, x, hx, hex⟩ := mem_iUnion.mp hj
  obtain ⟨hik, y, hy, hey⟩ := mem_iUnion.mp hi
  have hxy := lateral_injective (hex.trans hey.symm)
  subst y
  have ji : j = i := by
    have h₁ : 2*(j : ℝ)+1 ≤ x ∧ x ≤ 2*(j : ℝ)+2 := hx
    have h₂ : 2*(i : ℝ)+1 ≤ x ∧ x ≤ 2*(i : ℝ)+2 := hy
    rcases lt_trichotomy j i with h | h | h
    · have hh : (j : ℝ)+1 ≤ i := by exact_mod_cast h
      exfalso
      linarith [h₁.2, h₂.1]
    · exact h
    · have hh : (i : ℝ)+1 ≤ j := by exact_mod_cast h
      exfalso
      linarith [h₂.2, h₁.1]
  exact hmk (hjm.symm.trans (ji ▸ hik))

theorem find_arc (m : ℕ) {U V : Set Plane} (hU : IsOpen U) (hV : IsOpen V)
    (hu : (residual ∩ U).Nonempty) (hv : (residual ∩ V).Nonempty) :
    ∃ j, (tubeRequest j).1 = m ∧ (stageArc j ∩ U).Nonempty ∧
      (stageArc j ∩ V).Nonempty := by
  obtain ⟨u, huL, huU⟩ := hu
  obtain ⟨v, hvL, hvV⟩ := hv
  obtain ⟨B, hB, huB, hBU⟩ := (isBasis_countableBasis Plane).exists_subset_of_mem_open huU hU
  obtain ⟨C, hC, hvC, hCV⟩ := (isBasis_countableBasis Plane).exists_subset_of_mem_open hvV hV
  obtain ⟨j, -, hj⟩ := tubeRequest_onto m ⟨B, hB⟩ ⟨C, hC⟩ 0
  have h₁ : scheduled (2*j) = B := by simp [scheduled_even, hj]
  have h₂ : scheduled (2*j+1) = C := by simp [scheduled_odd, hj]
  have hB' : (scheduled (2*j) ∩ residual).Nonempty := ⟨u, h₁.symm ▸ huB, huL⟩
  have hC' : (scheduled (2*j+1) ∩ residual).Nonempty := ⟨v, h₂.symm ▸ hvC, hvL⟩
  have hvisitB := tubeMap_hits scheduled scheduled_open (2*j) hB'
  have hvisitC := tubeMap_hits scheduled scheduled_open (2*j+1) hC'
  refine ⟨j, congrArg Prod.fst hj, ?_, ?_⟩
  · let p : Plane := (2*(j : ℝ)+1, 1)
    refine ⟨recurrentMap p, ⟨p.1, by simp [p], rfl⟩, hBU ?_⟩
    rw [← h₁]
    apply hvisitB
    refine mem_image_of_mem _ ⟨?_, by norm_num⟩
    simp [p]
  · let p : Plane := (2*(j : ℝ)+2, 1)
    refine ⟨recurrentMap p, ⟨p.1, by simp [p], rfl⟩, hCV ?_⟩
    rw [← h₂]
    apply hvisitC
    refine mem_image_of_mem _ ⟨?_, by norm_num⟩
    simp [p]
    ring

theorem residual_nonempty : residual.Nonempty :=
  ⟨recurrentMap (0, 1), tube_lateral scheduled scheduled_open 0⟩

theorem track_dense (m : ℕ) : residual ⊆ closure (track m) := by
  intro p hp
  apply _root_.mem_closure_iff.mpr
  intro U hU hpU
  obtain ⟨j, hj, h, _⟩ := find_arc m hU hU ⟨p, hp, hpU⟩ ⟨p, hp, hpU⟩
  rw [inter_comm]
  exact h.mono (inter_subset_inter_left _ (arc_subset_track hj))

theorem track_connected (m : ℕ) : IsConnected (track m) := by
  have hR : (residual ∩ univ).Nonempty := by simpa using residual_nonempty
  obtain ⟨j, hj, hex, _⟩ := find_arc m isOpen_univ isOpen_univ hR hR
  refine ⟨hex.mono (inter_subset_left.trans (arc_subset_track hj)), ?_⟩
  intro U V hU hV hcover hu hv
  obtain ⟨k, hk, hku, hkv⟩ := find_arc m hU hV
    (hu.mono (inter_subset_inter_left _ (track_subset_residual m)))
    (hv.mono (inter_subset_inter_left _ (track_subset_residual m)))
  have hc : IsConnected (stageArc k) :=
    lateralArc_connected scheduled scheduled_open (by linarith)
  exact (hc.isPreconnected U V hU hV ((arc_subset_track hk).trans hcover) hku hkv).mono
    (inter_subset_inter_left _ (arc_subset_track hk))

theorem recurrent_sections {U : Set Plane} (hU : IsOpen U)
    (h : (U ∩ residual).Nonempty) (T : ℝ) :
    ∃ t > T, recurrentMap '' sectionAt t ⊆ U := by
  obtain ⟨p, hpU, hpL⟩ := h
  obtain ⟨B, hB, hpB, hBU⟩ := (isBasis_countableBasis Plane).exists_subset_of_mem_open hpU hU
  obtain ⟨M, hM⟩ := exists_nat_gt T
  obtain ⟨j, hjM, hj⟩ := tubeRequest_onto 0 ⟨B,hB⟩ ⟨B,hB⟩ M
  have h₁ : scheduled (2*j) = B := by simp [scheduled_even, hj]
  have hB' : (scheduled (2*j) ∩ residual).Nonempty := ⟨p, h₁.symm ▸ hpB, hpL⟩
  refine ⟨((2*j : ℕ) : ℝ) + 1, ?_, (tubeMap_hits scheduled scheduled_open (2*j) hB').trans ?_⟩
  · have hMj : (M : ℝ) ≤ j := by exact_mod_cast hjM
    push_cast
    linarith [show (0 : ℝ) ≤ j by positivity]
  · rwa [h₁]

-- Square-root coordinates on the slit plane turn parabolas into strip sections.
def ray : Set Plane := Ici (0 : ℝ) ×ˢ ({0} : Set ℝ)

theorem ray_closed : IsClosed ray := isClosed_Ici.prod isClosed_singleton

noncomputable def depth (p : Plane) : ℝ :=
  Real.sqrt ((Real.sqrt (p.1^2 + p.2^2) - p.1) / 2)

theorem depth_pos {p : Plane} (hp : p ∈ rayᶜ) : 0 < depth p := by
  have hsq := Real.sq_sqrt (show 0 ≤ p.1^2 + p.2^2 by positivity)
  have hs := Real.sqrt_nonneg (p.1^2 + p.2^2)
  apply Real.sqrt_pos.2
  have hlt : p.1 < Real.sqrt (p.1^2 + p.2^2) := by
    by_contra! h
    have hx : 0 ≤ p.1 := hs.trans h
    have hy : p.2 = 0 := by
      have hsq' := mul_self_le_mul_self hs h
      nlinarith
    exact hp ⟨hx, hy⟩
  linarith

theorem depth_cont : Continuous depth := by
  unfold depth
  fun_prop

noncomputable def rootReal (p : Plane) : ℝ := p.2 / (2 * depth p)

noncomputable abbrev squash := orderIsoIooNegOneOne ℝ

noncomputable def cutChart (p : Plane) : Plane :=
  (-Real.log (depth p), (squash (rootReal p) : ℝ))

theorem cutChart_cont : ContinuousOn cutChart rayᶜ := by
  have hn (p : Plane) (hp : p ∈ rayᶜ) : depth p ≠ 0 := (depth_pos hp).ne'
  have ha : ContinuousOn rootReal rayᶜ :=
    continuous_snd.continuousOn.div (continuous_const.mul depth_cont).continuousOn
      (fun p hp => mul_ne_zero (by norm_num) (hn p hp))
  have ht := Real.continuousOn_log.comp depth_cont.continuousOn hn
  exact ht.neg.prodMk ((continuous_subtype_val.comp squash.toHomeomorph.continuous).continuousOn.comp
    ha (mapsTo_univ _ _))

def quadratic (a b : ℝ) : Plane := (a^2-b^2, 2*a*b)

theorem quadratic_offRay (a : ℝ) {b : ℝ} (hb : 0 < b) : quadratic a b ∈ rayᶜ := by
  rintro ⟨hx, hy⟩
  change 0 ≤ a^2-b^2 at hx
  change 2*a*b = 0 at hy
  have ha : a = 0 := by
    rcases (mul_eq_zero.mp hy) with h | h
    · exact (mul_eq_zero.mp h).resolve_left (by norm_num)
    · exact (hb.ne' h).elim
  nlinarith

theorem depth_quadratic (a : ℝ) {b : ℝ} (hb : 0 < b) : depth (quadratic a b) = b := by
  change Real.sqrt ((Real.sqrt ((a^2-b^2)^2+(2*a*b)^2) - (a^2-b^2)) / 2) = b
  rw [show (a^2-b^2)^2+(2*a*b)^2 = (a^2+b^2)^2 by ring,
    Real.sqrt_sq (by positivity : 0 ≤ a^2+b^2)]
  rw [show ((a^2+b^2)-(a^2-b^2))/2 = b^2 by ring, Real.sqrt_sq hb.le]

theorem rootReal_quadratic (a : ℝ) {b : ℝ} (hb : 0 < b) : rootReal (quadratic a b) = a := by
  unfold rootReal
  rw [depth_quadratic a hb]
  change 2*a*b/(2*b) = a
  field_simp

theorem quadratic_coordinates {p : Plane} (hp : p ∈ rayᶜ) :
    quadratic (rootReal p) (depth p) = p := by
  have hb := depth_pos hp
  have hs := Real.sq_sqrt (show 0 ≤ p.1^2+p.2^2 by positivity)
  have hsq := Real.sq_sqrt (show 0 ≤ (Real.sqrt (p.1^2+p.2^2) - p.1) / 2 by
    exact Real.sqrt_pos.mp hb |>.le)
  change depth p ^ 2 = _ at hsq
  have he : Real.sqrt (p.1^2 + p.2^2) = p.1 + 2*(depth p)^2 := by linarith
  rw [he] at hs
  have hy : p.2^2 = 4*(depth p)^2*(p.1+(depth p)^2) := by nlinarith
  apply Prod.ext
  · change (p.2/(2*depth p))^2-(depth p)^2 = p.1
    rw [sub_eq_iff_eq_add, div_pow, div_eq_iff (pow_ne_zero _ (mul_ne_zero (by norm_num) hb.ne'))]
    calc
      _ = _ := hy
      _ = _ := by ring
  · change 2*(p.2/(2*depth p))*depth p = p.2
    field_simp

theorem cutChart_bij : BijOn cutChart rayᶜ strip := by
  refine ⟨fun p _ => ⟨trivial, (squash (rootReal p)).property⟩, ?_, ?_⟩
  · intro p hp q hq he
    have hfst := congrArg Prod.fst he
    change -Real.log (depth p) = -Real.log (depth q) at hfst
    have hd : depth p = depth q := by
      have hlog := congrArg Real.exp (neg_injective hfst)
      simpa only [Real.exp_log (depth_pos hp), Real.exp_log (depth_pos hq)] using hlog
    have hsnd := congrArg Prod.snd he
    have ha : rootReal p = rootReal q := squash.injective (Subtype.ext hsnd)
    rw [← quadratic_coordinates hp, ← quadratic_coordinates hq, hd, ha]
  · intro p hp
    let a := squash.symm ⟨p.2, hp.2⟩
    let b := Real.exp (-p.1)
    have hb : 0 < b := Real.exp_pos _
    refine ⟨quadratic a b, quadratic_offRay a hb, ?_⟩
    apply Prod.ext
    · change -Real.log (depth (quadratic a b)) = p.1
      simp [depth_quadratic a hb, b]
    · change (squash (rootReal (quadratic a b)) : ℝ) = p.2
      simp [rootReal_quadratic a hb, a]

noncomputable def parabola (t y : ℝ) : ℝ :=
  (y / (2 * Real.exp (-t)))^2 - (Real.exp (-t))^2

theorem parabola_cont (t : ℝ) : Continuous (parabola t) := by
  unfold parabola
  fun_prop

theorem ray_right (t : ℝ) {p : Plane} (hp : p ∈ ray) : parabola t p.2 < p.1 := by
  have h := Real.exp_pos (-t)
  have hp₂ : p.2 = 0 := hp.2
  have hp₁ : 0 ≤ p.1 := hp.1
  rw [hp₂]
  simp only [parabola, zero_div, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_sub]
  nlinarith

theorem parabola_compare {p : Plane} (hp : p ∈ rayᶜ) (t : ℝ) :
    p.1 - parabola t p.2 =
      ((Real.exp (-t))^2-(depth p)^2) *
      (1 + (rootReal p)^2/(Real.exp (-t))^2) := by
  have h := quadratic_coordinates hp
  have hx : (rootReal p)^2-(depth p)^2 = p.1 := congrArg Prod.fst h
  have hy : 2*(rootReal p)*(depth p) = p.2 := congrArg Prod.snd h
  unfold parabola
  rw [← hx, ← hy]
  field_simp [(Real.exp_pos (-t)).ne']
  ring

theorem gate_left {p : Plane} (hp : p ∈ rayᶜ) {t : ℝ} (ht : (cutChart p).1 < t) :
    p.1 < parabola t p.2 := by
  change -Real.log (depth p) < t at ht
  have hb := depth_pos hp
  have he : Real.exp (-t) < depth p := by
    rw [← Real.exp_log hb]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hdiff : (Real.exp (-t))^2 - (depth p)^2 < 0 := by
    nlinarith [sq_nonneg (depth p - Real.exp (-t)), Real.exp_pos (-t)]
  have hfac : 0 < 1 + (rootReal p)^2 / (Real.exp (-t))^2 := by positivity
  have := mul_neg_of_neg_of_pos hdiff hfac
  rw [← parabola_compare hp t] at this
  linarith

theorem gate_middle {p : Plane} {t : ℝ} (hp : p.1 = parabola t p.2) :
    p ∈ rayᶜ ∧ (cutChart p).1 = t := by
  have hpc : p ∈ rayᶜ := fun hr => (ray_right t hr).ne' hp
  refine ⟨hpc, ?_⟩
  have he := parabola_compare hpc t
  rw [sub_eq_zero.mpr hp] at he
  have hfac : 0 < 1 + (rootReal p)^2 / (Real.exp (-t))^2 := by positivity
  have hh : (Real.exp (-t))^2 - (depth p)^2 = 0 :=
    (mul_eq_zero.mp he.symm).resolve_right hfac.ne'
  have hd : depth p = Real.exp (-t) := by
    nlinarith [depth_pos hpc, Real.exp_pos (-t)]
  change -Real.log (depth p) = t
  simp [hd]

-- A proposed separation pulls back to disjoint open pieces after cutting at a gate.
theorem gate_preserves {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {E : Set X} {f : X → Y} (hE : IsClosed E) (hcont : ContinuousOn f Eᶜ)
    (hon : ∀ C ⊆ E, IsConnected C → IsConnected (f '' C))
    (hgate : ∀ x ∈ E, ∀ z ∈ Eᶜ, ∀ U, IsOpen U → f x ∈ U →
      ∃ N M : Set X, IsOpen N ∧ IsOpen M ∧ E ⊆ N ∧ z ∈ M ∧ Disjoint N M ∧
        f '' (N ∪ M)ᶜ ⊆ U) : IsConnectedMap f := by
  classical
  intro C hc
  by_cases hCE : C ⊆ E
  · exact hon C hCE hc
  by_cases hCc : C ⊆ Eᶜ
  · exact hc.image _ (hcont.mono hCc)
  obtain ⟨x, hx, hxE'⟩ := not_subset.mp hCc
  have hxE : x ∈ E := by simpa using hxE'
  obtain ⟨z, hz, hzE⟩ := not_subset.mp hCE
  refine ⟨hc.nonempty.image _, ?_⟩
  intro U V hU hV hcover hu hv
  by_contra hnon
  have cover (p : X) (hp : p ∈ C) : f p ∈ U ∨ f p ∈ V :=
    hcover (mem_image_of_mem _ hp)
  have prevent {U₁ V₁ : Set Y} (hU₁ : IsOpen U₁) (hV₁ : IsOpen V₁)
      (hcover₁ : ∀ p ∈ C, f p ∈ U₁ ∨ f p ∈ V₁)
      (hdis : ∀ p ∈ C, f p ∈ U₁ → f p ∈ V₁ → False)
      {a b : X} (ha : a ∈ C) (haE : a ∈ E) (haU : f a ∈ U₁)
      (hb : b ∈ C) (hbE : b ∈ Eᶜ) (hbV : f b ∈ V₁) : False := by
    obtain ⟨N, M, hN, hM, hEN, hbM, hNM, hrest⟩ := hgate a haE b hbE U₁ hU₁ haU
    let P := N ∪ (Eᶜ ∩ f ⁻¹' U₁)
    let Q := M ∩ f ⁻¹' V₁
    have hMc : M ⊆ Eᶜ := fun _ hm he => Set.disjoint_left.mp hNM (hEN he) hm
    have hP : IsOpen P := hN.union (hcont.isOpen_inter_preimage hE.isOpen_compl hU₁)
    have hQ : IsOpen Q := (hcont.mono hMc).isOpen_inter_preimage hM hV₁
    have hcoverPQ : C ⊆ P ∪ Q := by
      intro p hp
      by_cases hpN : p ∈ N
      · exact Or.inl (Or.inl hpN)
      have hpE : p ∈ Eᶜ := fun he => hpN (hEN he)
      rcases hcover₁ p hp with hpU | hpV
      · exact Or.inl (Or.inr ⟨hpE, hpU⟩)
      · by_cases hpM : p ∈ M
        · exact Or.inr ⟨hpM, hpV⟩
        · exact (hdis p hp (hrest (mem_image_of_mem _ (show p ∈ (N ∪ M)ᶜ from
            fun h => h.elim hpN hpM))) hpV).elim
    obtain ⟨p, hp, hpP, hpQ⟩ := hc.isPreconnected P Q hP hQ hcoverPQ
      ⟨a, ha, Or.inl (hEN haE)⟩ ⟨b, hb, hbM, hbV⟩
    rcases hpP with hn | ⟨_, hpu⟩
    · exact Set.disjoint_left.mp hNM hn hpQ.1
    · exact hdis p hp hpu hpQ.2
  have hdis (p : X) (hp : p ∈ C) (hpU : f p ∈ U) (hpV : f p ∈ V) : False :=
    hnon ⟨f p, mem_image_of_mem _ hp, hpU, hpV⟩
  have left {a b : X} (ha : a ∈ C) (haE : a ∈ E) (haU : f a ∈ U)
      (hb : b ∈ C) (hbE : b ∈ Eᶜ) (hbV : f b ∈ V) : False :=
    prevent hU hV cover hdis ha haE haU hb hbE hbV
  have right {a b : X} (ha : a ∈ C) (haE : a ∈ E) (haV : f a ∈ V)
      (hb : b ∈ C) (hbE : b ∈ Eᶜ) (hbU : f b ∈ U) : False :=
    prevent hV hU (fun p hp => (cover p hp).symm) (fun p hp h₁ h₂ => hdis p hp h₂ h₁)
      ha haE haV hb hbE hbU
  rcases cover x hx with hxU | hxV
  · rcases cover z hz with hzU | hzV
    · obtain ⟨_, ⟨b, hb, rfl⟩, hbV⟩ := hv
      by_cases hbE : b ∈ E
      · exact right hb hbE hbV hz hzE hzU
      · exact left hx hxE hxU hb hbE hbV
    · exact left hx hxE hxU hz hzE hzV
  · rcases cover z hz with hzU | hzV
    · exact right hx hxE hxV hz hzE hzU
    · obtain ⟨_, ⟨b, hb, rfl⟩, hbU⟩ := hu
      by_cases hbE : b ∈ E
      · exact left hb hbE hbU hz hzE hzV
      · exact right hx hxE hxV hb hbE hbU

open Cardinal
open scoped Cardinal

-- The fresh representative and reserve argument is adapted from the checked
-- sibling proof of Gro-Tsen's MathOverflow 260589 example by MrSeizy.
theorem freshPoint {α β : Type} (s : Set β) (g : α → β)
    (h : #α < #s) : ∃ x ∈ s, x ∉ range g := by
  by_contra! hn
  exact h.not_ge ((mk_le_mk_of_subset hn).trans mk_range_le)

theorem distinctRepresentatives {ι β : Type} (S : ι → Set β) (h : ∀ i, #ι ≤ #(S i)) :
    ∃ f : ι → β, Injective f ∧ ∀ i, f i ∈ S i := by
  classical
  obtain ⟨ord, wf, ho⟩ := exists_ord_eq_type_lt ι
  have step (i : ι) (g : ∀ j : ι, j < i → β) :
      ∃ x ∈ S i, x ∉ range (fun j : Iio i => g j.1 j.2) :=
    freshPoint _ _ ((mk_Iio_lt i ho).trans_le (h i))
  let choosePoint (i : ι) (g : ∀ j : ι, j < i → β) := (step i g).choose
  let f := wellFounded_lt.fix choosePoint
  have spec (i : ι) : f i ∈ S i ∧ f i ∉ range (fun j : Iio i => f j.1) := by
    have eqn : f i = choosePoint i (fun j _ => f j) := WellFounded.fix_eq _ _ _
    exact eqn ▸ (step i (fun j _ => f j)).choose_spec
  have ne_of_before {i j : ι} (hij : i < j) : f i ≠ f j := fun he =>
    (spec j).2 ⟨⟨i, hij⟩, he⟩
  refine ⟨f, ?_, fun i => (spec i).1⟩
  intro i j he
  rcases lt_trichotomy i j with hij | hij | hij
  · exact (ne_of_before hij he).elim
  · exact hij
  · exact (ne_of_before hij he.symm).elim

theorem reserveRepresentatives {ι β : Type} (S : ι → Set β) (hi : #ι ≤ 𝔠)
    (hb : #β = 𝔠) (h : ∀ i, 𝔠 ≤ #(S i)) :
    ∃ f : ι → β, Injective f ∧ (∀ i, f i ∈ S i) ∧ #((range f)ᶜ : Set β) = 𝔠 := by
  classical
  let T : ι ⊕ ℝ → Set β := Sum.elim S (fun _ => Set.univ)
  have hc : #(ι ⊕ ℝ) ≤ 𝔠 := by
    simpa only [mk_sum, lift_id, mk_real, continuum_add_self] using
      (add_le_add hi (le_refl 𝔠))
  obtain ⟨g, hg, hgT⟩ := distinctRepresentatives T (fun i => hc.trans (by
    cases i with
    | inl i => exact h i
    | inr r => simp [T, hb]))
  let f (i : ι) := g (Sum.inl i)
  have hr (r : ℝ) : g (Sum.inr r) ∉ range f := by
    rintro ⟨i, he⟩
    cases hg he
  let k (r : ℝ) : ((range f)ᶜ : Set β) := ⟨g (Sum.inr r), hr r⟩
  have hk : Injective k := fun _ _ he => Sum.inr.inj (hg (congrArg Subtype.val he))
  exact ⟨f, hg.comp Sum.inl_injective, fun i => hgT (.inl i),
    (mk_set_le _ |>.trans_eq hb).antisymm (mk_real ▸ mk_le_of_injective hk)⟩

theorem completeRepresentatives {α β : Type} {S : Set β} (A : S → Set α)
    (hα : #α = 𝔠) (hS : #S ≤ 𝔠) (hSc : #(Sᶜ : Set β) = 𝔠)
    (hA : ∀ s, 𝔠 ≤ #(A s)) :
    ∃ b : α ≃ β, ∀ s : S, b.symm s ∈ A s := by
  classical
  obtain ⟨a, hai, ha, hac⟩ := reserveRepresentatives A hS hα hA
  let ea := Equiv.ofInjective a hai
  let ec := (Cardinal.eq.mp (hac.trans hSc.symm)).some
  let b := (Equiv.Set.sumCompl (range a)).symm.trans
    ((Equiv.sumCongr ea.symm ec).trans (Equiv.Set.sumCompl S))
  refine ⟨b, fun s => ?_⟩
  have he : b (a s) = (s : β) := by
    have hsplit : (Equiv.Set.sumCompl (range a)).symm (a s) = Sum.inl (ea s) :=
      Equiv.Set.sumCompl_symm_apply_of_mem (mem_range_self s)
    simp only [b, Equiv.trans_apply, hsplit, Equiv.sumCongr_apply, Sum.map_inl,
      Equiv.symm_apply_apply, Equiv.Set.sumCompl_apply_inl]
  rw [← he, b.symm_apply_apply]
  exact ha s

abbrev RayInterval := {q : ℚ × ℚ // 0 ≤ q.1 ∧ q.1 < q.2}

def rayIntervalSet (i : RayInterval) : Set ray :=
  {p | (p.1.1 : ℝ) ∈ Ioo (i.1.1 : ℝ) (i.1.2 : ℝ)}

theorem rayInterval_lower (i : RayInterval) : 𝔠 ≤ #(rayIntervalSet i) := by
  let a : ℝ := i.1.1
  let b : ℝ := i.1.2
  have ha : 0 ≤ a := by
    dsimp [a]
    exact_mod_cast i.2.1
  have hab : a < b := by
    dsimp [a, b]
    exact_mod_cast i.2.2
  let f (x : Ioo a b) : rayIntervalSet i :=
    ⟨⟨(x, 0), ⟨ha.trans x.2.1.le, rfl⟩⟩, x.2⟩
  have hf : Injective f := by
    intro x y he
    exact Subtype.ext (congrArg (fun p : rayIntervalSet i => p.1.1.1) he)
  exact (mk_Ioo_real hab).symm.le.trans (mk_le_of_injective hf)

theorem ray_card : #ray = 𝔠 := by
  have hp : #Plane = 𝔠 := by simp [Plane, mk_prod, mk_real]
  let i : RayInterval := ⟨(0,1), by norm_num⟩
  exact ((mk_set_le ray).trans_eq hp).antisymm
    ((rayInterval_lower i).trans (mk_set_le _))

theorem arcCardLower {a b : ℝ} (hab : a < b) :
    𝔠 ≤ #(lateralArc recurrentMap a b) := by
  let f (x : Ioo a b) : lateralArc recurrentMap a b :=
    ⟨recurrentMap (x, 1), ⟨x, Ioo_subset_Icc_self x.2, rfl⟩⟩
  have hi : Injective f := fun x y he =>
    Subtype.ext (lateral_injective (congrArg Subtype.val he))
  exact (mk_Ioo_real hab).symm.le.trans (mk_le_of_injective hi)

noncomputable def assigned : Set residual :=
  {p | ∃ i : RayInterval, p.1 ∈ track (Encodable.encode i + 1)}

theorem assigned_compl_card : #((assignedᶜ : Set residual)) = 𝔠 := by
  have hp : #Plane = 𝔠 := by simp [Plane, mk_prod, mk_real]
  apply le_antisymm (((mk_set_le _).trans (mk_set_le residual)).trans_eq hp)
  have hR : (residual ∩ Set.univ).Nonempty := by simpa using residual_nonempty
  obtain ⟨j, hj, _, _⟩ := find_arc 0 isOpen_univ isOpen_univ hR hR
  let f (p : stageArc j) : (assignedᶜ : Set residual) :=
    ⟨⟨p, track_subset_residual 0 (arc_subset_track hj p.2)⟩, by
      rintro ⟨i, hi⟩
      exact Set.disjoint_left.mp (tracks_disjoint (show 0 ≠ Encodable.encode i + 1 by omega))
        (arc_subset_track hj p.2) hi⟩
  have hf : Injective f := fun p q he =>
    Subtype.ext (congrArg (fun r : (assignedᶜ : Set residual) => r.1.1) he)
  exact (arcCardLower (a := 2*(j : ℝ)+1) (b := 2*(j : ℝ)+2) (by linarith)).trans
    (mk_le_of_injective hf)

theorem ray_matching :
    ∃ b : ray ≃ residual, ∀ i : RayInterval, ∀ p : residual,
      p.1 ∈ track (Encodable.encode i + 1) → b.symm p ∈ rayIntervalSet i := by
  classical
  have hp : #Plane = 𝔠 := by simp [Plane, mk_prod, mk_real]
  have hS : #assigned ≤ 𝔠 := ((mk_set_le _).trans (mk_set_le residual)).trans_eq hp
  let iOf (p : assigned) : RayInterval := p.2.choose
  obtain ⟨b, hb⟩ := completeRepresentatives (fun p : assigned => rayIntervalSet (iOf p))
    ray_card hS assigned_compl_card (fun p => rayInterval_lower (iOf p))
  refine ⟨b, fun i p hp => ?_⟩
  let y : assigned := ⟨p, ⟨i, hp⟩⟩
  have hiy : iOf y = i := by
    by_contra h
    have hne : Encodable.encode (iOf y) + 1 ≠ Encodable.encode i + 1 := by
      intro heq
      exact h (Encodable.encode_injective (Nat.add_right_cancel heq))
    exact Set.disjoint_left.mp (tracks_disjoint hne) (show p.1 ∈ track
      (Encodable.encode (iOf y) + 1) from y.2.choose_spec) hp
  have h := hb y
  rw [hiy] at h
  exact h

theorem containsInterval {C : Set Plane} (hC : C ⊆ ray) (hc : IsConnected C)
    (hn : C.Nontrivial) :
    ∃ i : RayInterval, ∀ p ∈ rayIntervalSet i, (p : Plane) ∈ C := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hn
  have hx0 : x.2 = 0 := (hC hx).2
  have hy0 : y.2 = 0 := (hC hy).2
  have hxy' : x.1 ≠ y.1 := fun h => hxy (Prod.ext h (hx0.trans hy0.symm))
  let a : ℝ := min x.1 y.1
  let b : ℝ := max x.1 y.1
  have hab : a < b := min_lt_max.mpr hxy'
  have ha : 0 ≤ a := le_min (hC hx).1 (hC hy).1
  obtain ⟨q, haq, hqb⟩ := exists_rat_btwn hab
  obtain ⟨r, hqr, hrb⟩ := exists_rat_btwn hqb
  have hq : (0 : ℚ) ≤ q := by exact_mod_cast (ha.trans haq.le)
  have hqr' : q < r := by exact_mod_cast hqr
  let i : RayInterval := ⟨(q,r), hq, hqr'⟩
  refine ⟨i, fun p hp => ?_⟩
  have hproj : IsConnected (Prod.fst '' C) := hc.image _ continuous_fst.continuousOn
  have ham : a ∈ Prod.fst '' C := by
    rcases le_total x.1 y.1 with h | h
    · simpa [a, min_eq_left h] using mem_image_of_mem Prod.fst hx
    · simpa [a, min_eq_right h] using mem_image_of_mem Prod.fst hy
  have hbm : b ∈ Prod.fst '' C := by
    rcases le_total x.1 y.1 with h | h
    · simpa [b, max_eq_right h] using mem_image_of_mem Prod.fst hy
    · simpa [b, max_eq_left h] using mem_image_of_mem Prod.fst hx
  obtain ⟨z, hz, hzp⟩ := hproj.isPreconnected.ordConnected.out ham hbm
    (show (p : Plane).1 ∈ Icc a b from ⟨haq.le.trans hp.1.le, hp.2.le.trans hrb.le⟩)
  have hz0 : z.2 = 0 := (hC hz).2
  have hp0 : (p : Plane).2 = 0 := p.2.2
  exact Prod.ext hzp (hz0.trans hp0.symm) ▸ hz

theorem plane_counterexample : ∃ f : Plane ≃ Plane, IsConnectedMap f ∧ ¬ IsConnectedMap f.symm := by
  classical
  obtain ⟨b, hb⟩ := ray_matching
  have hTube : BijOn recurrentMap strip (recurrentMap '' strip) :=
    ⟨fun _ hp => mem_image_of_mem _ hp,
      (tubeMap_inj scheduled scheduled_open).mono
        (show strip ⊆ Set.univ ×ˢ Icc (-1 : ℝ) 1 from fun _ hp =>
          ⟨trivial, Ioo_subset_Icc_self hp.2⟩),
      fun _ hp => hp⟩
  have hd : BijOn (recurrentMap ∘ cutChart) rayᶜ residualᶜ := by
    change BijOn (recurrentMap ∘ cutChart) rayᶜ (recurrentMap '' strip)ᶜᶜ
    rw [compl_compl]
    exact hTube.comp cutChart_bij
  let d := Set.BijOn.equiv (recurrentMap ∘ cutChart) hd
  let f := (Equiv.Set.sumCompl ray).symm.trans
    ((Equiv.sumCongr b d).trans (Equiv.Set.sumCompl residual))
  have hfr (p : Plane) (hp : p ∈ ray) : f p = (b ⟨p, hp⟩ : Plane) := by
    simp only [f, Equiv.trans_apply, Equiv.Set.sumCompl_symm_apply_of_mem hp,
      Equiv.sumCongr_apply, Sum.map_inl, Equiv.Set.sumCompl_apply_inl]
  have hfo (p : Plane) (hp : p ∈ rayᶜ) : f p = recurrentMap (cutChart p) := by
    simp only [f, Equiv.trans_apply, Equiv.Set.sumCompl_symm_apply_of_notMem hp,
      Equiv.sumCongr_apply, Sum.map_inr, Equiv.Set.sumCompl_apply_inr]
    rfl
  have hcont : ContinuousOn f rayᶜ :=
    ((tubeMap_cont scheduled scheduled_open).comp cutChart_cont cutChart_bij.1).congr hfo
  have image_ray {C : Set Plane} (hC : C ⊆ ray) : f '' C ⊆ residual := by
    rintro _ ⟨p, hp, rfl⟩
    rw [hfr p (hC hp)]
    exact (b ⟨p, hC hp⟩).2
  have track_in_image {C : Set Plane} (hC : C ⊆ ray) (hc : IsConnected C)
      (hn : C.Nontrivial) : ∃ m, track m ⊆ f '' C := by
    obtain ⟨i, hi⟩ := containsInterval hC hc hn
    refine ⟨Encodable.encode i + 1, ?_⟩
    intro p hp
    let q : residual := ⟨p, track_subset_residual _ hp⟩
    let x := b.symm q
    refine ⟨x, hi x (hb i q hp), ?_⟩
    rw [hfr (x : Plane) x.2]
    exact congrArg Subtype.val (b.apply_symm_apply q)
  have hf : IsConnectedMap f := by
    apply gate_preserves ray_closed hcont
    · intro C hC hc
      rcases C.subsingleton_or_nontrivial with hs | hn
      · exact ⟨hc.nonempty.image _, (hs.image f).isPreconnected⟩
      obtain ⟨m, hm⟩ := track_in_image hC hc hn
      exact (track_connected m).subset_closure hm ((image_ray hC).trans (track_dense m))
    · intro x hx z hz U hU hxU
      have hxL : f x ∈ residual := by
        rw [hfr x hx]
        exact (b ⟨x, hx⟩).2
      obtain ⟨t, htz, htU⟩ := recurrent_sections hU ⟨f x, hxU, hxL⟩ (cutChart z).1
      let N : Set Plane := {p | parabola t p.2 < p.1}
      let M : Set Plane := {p | p.1 < parabola t p.2}
      have hpcont := (parabola_cont t).comp (continuous_snd : Continuous (Prod.snd : Plane → ℝ))
      refine ⟨N, M, isOpen_lt hpcont continuous_fst, isOpen_lt continuous_fst hpcont,
        fun _ hp => ray_right t hp, gate_left hz htz,
        Set.disjoint_left.mpr (fun p hp hn => (show parabola t p.2 < p.1 from hp).not_gt hn), ?_⟩
      rintro _ ⟨p, hp, rfl⟩
      have heq : p.1 = parabola t p.2 := le_antisymm
        (le_of_not_gt (fun h => hp (Or.inl h))) (le_of_not_gt (fun h => hp (Or.inr h)))
      obtain ⟨hpc, hpt⟩ := gate_middle heq
      rw [hfo p hpc]
      apply htU
      exact mem_image_of_mem _ ⟨hpt, Ioo_subset_Icc_self (cutChart_bij.1 hpc).2⟩
  refine ⟨f, hf, ?_⟩
  intro hinv
  -- Every nondegenerate connected subset of the ray has dense image in the residual set.
  let T := lateralArc recurrentMap 0 1
  have hT : IsConnected T := lateralArc_connected scheduled scheduled_open (by norm_num)
  have hTclosed : IsClosed T := lateralArc_closed scheduled scheduled_open 0 1
  have hTr : T ⊆ residual := by
    rintro _ ⟨x, _, rfl⟩
    exact tube_lateral scheduled scheduled_open x
  let C := f ⁻¹' T
  have hC : IsConnected C := by
    change IsConnected (f ⁻¹' T)
    rw [← Equiv.image_symm_eq_preimage]
    exact hinv hT
  have hCr : C ⊆ ray := by
    intro p hp
    by_contra h
    have hpL := hTr hp
    rw [hfo p h] at hpL
    exact hpL (mem_image_of_mem _ (cutChart_bij.1 h))
  have hn : C.Nontrivial := by
    let u := recurrentMap (0, 1)
    let v := recurrentMap (1, 1)
    have hu : u ∈ T := ⟨0, by simp, rfl⟩
    have hv : v ∈ T := ⟨1, by simp, rfl⟩
    refine ⟨f.symm u, by simpa [C] using hu, f.symm v, by simpa [C] using hv, ?_⟩
    intro h
    have huv := f.symm.injective h
    exact zero_ne_one (lateral_injective huv)
  obtain ⟨m, hm⟩ := track_in_image hCr hC hn
  have hsub : track m ⊆ T := hm.trans (image_preimage_subset _ _)
  have hall : residual ⊆ T := (track_dense m).trans (closure_minimal hsub hTclosed)
  obtain ⟨x, hx, he⟩ := hall (tube_lateral scheduled scheduled_open 2)
  have hxe : x = 2 := lateral_injective he
  have hxle : x ≤ 1 := hx.2
  linarith

end OMA.Recurrent

open OMA.Recurrent Mathoverflow235893
open scoped EuclideanGeometry

-- Credit: @MrSeizy
theorem OMA.disproof : ¬ (type_of% @Mathoverflow235893.mathoverflow_235893) := by
  intro h
  obtain ⟨f, hf, hnf⟩ := plane_counterexample
  let e : (ℝ^2) ≃ₜ Plane :=
    (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans Homeomorph.finTwoArrow
  let F := e.toEquiv.trans (f.trans e.symm.toEquiv)
  have hF : IsConnectedMap F := by
    change IsConnectedMap (e.symm ∘ f ∘ e)
    exact isConnectedMap_comp (isConnectedMap_comp (isConnectedMap_homeomorph e) hf)
      (isConnectedMap_homeomorph e.symm)
  have hFs := h 2 (by decide) F hF
  have hback := isConnectedMap_comp
    (isConnectedMap_comp (isConnectedMap_homeomorph e.symm) hFs) (isConnectedMap_homeomorph e)
  apply hnf
  have heq : (⇑e ∘ ⇑F.symm ∘ ⇑e.symm) = (f.symm : Plane → Plane) := by
    funext p
    change e (e.symm (f.symm (e (e.symm p)))) = f.symm p
    simp
  rwa [heq] at hback

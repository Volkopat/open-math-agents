import OMAStatements.S_mo_474511

-- Split the curve into a central part and a part with compact tail.
-- The cluster points of the compact part determine the commuting approximation.

open Filter Set
open scoped Topology NNReal Matrix.Norms.Elementwise

namespace OMA.AsymptoticMatrices

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ


private def bracketRight {n : ℕ} (Y : Mat n) : Mat n →ₗ[ℝ] Mat n where
  toFun X := X * Y - Y * X
  map_add' X X' := by
    simp only [add_mul, mul_add]
    abel
  map_smul' c X := by
    simp [smul_sub]

private theorem norm_le_of_ker_eq_bot {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →ₗ[ℝ] F) (hL : L.ker = ⊥) :
    ∃ C : ℝ≥0, ∀ x, ‖L x‖ ≤ 1 → ‖x‖ ≤ (C : ℝ) := by
  obtain ⟨C, -, hC⟩ := L.exists_antilipschitzWith hL
  refine ⟨C, fun x hx => ?_⟩
  have h : ‖x‖ ≤ (C : ℝ) * ‖L x‖ := by simpa using hC.le_mul_dist x 0
  exact h.trans (by simpa using mul_le_mul_of_nonneg_left hx C.coe_nonneg)

set_option maxHeartbeats 500000 in
theorem tailComponents {n : ℕ} (A : ℝ≥0 → Mat n)
    (hA : Tendsto (fun p : ℝ≥0 × ℝ≥0 => A p.1 * A p.2 - A p.2 * A p.1)
      (atTop ×ˢ atTop) (𝓝 0)) :
    ∃ (Z : Submodule ℝ (Mat n)) (P R : ℝ≥0 → Mat n) (K : Set (Mat n)),
      (∀ᶠ t in atTop, A t = P t + R t ∧ P t ∈ Z ∧ R t ∈ K) ∧
      IsCompact K ∧ (∀ z ∈ Z, ∀ w ∈ Z, Commute z w) ∧
      (∀ z ∈ Z, ∀ᶠ t in atTop, Commute z (R t)) ∧
      Tendsto (fun p : ℝ≥0 × ℝ≥0 => R p.1 * R p.2 - R p.2 * R p.1)
        (atTop ×ˢ atTop) (𝓝 0) := by
  classical
  have hsmall : ∀ᶠ p : ℝ≥0 × ℝ≥0 in atTop ×ˢ atTop,
      ‖A p.1 * A p.2 - A p.2 * A p.1‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using
      hA.eventually (Metric.ball_mem_nhds (0 : Mat n) zero_lt_one)
  obtain ⟨a, ha, b, hb, hab⟩ := eventually_prod_iff.mp hsmall
  obtain ⟨a₀, ha₀⟩ := eventually_atTop.mp ha
  obtain ⟨b₀, hb₀⟩ := eventually_atTop.mp hb
  let t₀ := max a₀ b₀
  have hbound {t s : ℝ≥0} (ht : t₀ ≤ t) (hs : t₀ ≤ s) :
      ‖A t * A s - A s * A t‖ ≤ 1 :=
    (hab (ha₀ _ ((le_max_left _ _).trans ht)) (hb₀ _ ((le_max_right _ _).trans hs))).le
  let S := A '' Ici t₀
  let V := Submodule.span ℝ S
  obtain ⟨T, hT, -, hTV, -⟩ := Submodule.exists_finset_span_eq_linearIndepOn ℝ S
  let F : V →ₗ[ℝ] (↥T → Mat n) :=
    LinearMap.pi (fun Y : ↥T => (bracketRight (Y : Mat n)).comp V.subtype)
  let Z₀ := F.ker
  let Z := Z₀.map V.subtype
  obtain ⟨W, hZW⟩ := Submodule.exists_isCompl Z₀
  let decomp := (Z₀.prodEquivOfIsCompl W hZW).symm
  let A₀ (t : ℝ≥0) : V :=
    if ht : t₀ ≤ t then ⟨A t, Submodule.subset_span ⟨t, ht, rfl⟩⟩ else 0
  let p := fun t => (decomp (A₀ t)).1
  let r := fun t => (decomp (A₀ t)).2
  let P : ℝ≥0 → Mat n := fun t => ((p t : V) : Mat n)
  let R : ℝ≥0 → Mat n := fun t => ((r t : V) : Mat n)
  have hdecomp₀ (t : ℝ≥0) : A₀ t = (p t : V) + (r t : V) := by
    simpa only [decomp, p, r, Submodule.coe_prodEquivOfIsCompl'] using
      ((Z₀.prodEquivOfIsCompl W hZW).apply_symm_apply (A₀ t)).symm
  have hdecomp {t : ℝ≥0} (ht : t₀ ≤ t) : A t = P t + R t := by
    have he := congrArg (fun x : V => (x : Mat n)) (hdecomp₀ t)
    change (A₀ t : Mat n) = P t + R t at he
    simpa [A₀, ht] using he
  have hP (t : ℝ≥0) : P t ∈ Z := ⟨(p t : V), (p t).property, rfl⟩
  have hRV (t : ℝ≥0) : R t ∈ V := (r t : V).property
  have hcentral {z x : Mat n} (hz : z ∈ Z) (hx : x ∈ V) : Commute z x := by
    obtain ⟨z₀, hz₀, rfl⟩ := hz
    have hz₀' : F z₀ = 0 := hz₀
    have hspan : V ≤ (bracketRight (z₀ : Mat n)).ker := by
      change Submodule.span ℝ S ≤ _
      rw [← hTV]
      apply Submodule.span_le.mpr
      intro y hy
      have h := congrFun hz₀' (⟨y, hy⟩ : ↥T)
      change (z₀ : Mat n) * y - y * (z₀ : Mat n) = 0 at h
      change y * (z₀ : Mat n) - (z₀ : Mat n) * y = 0
      exact sub_eq_zero.mpr (sub_eq_zero.mp h).symm
    exact (sub_eq_zero.mp (hspan hx)).symm
  let G : W →ₗ[ℝ] (↥T → Mat n) := F.comp W.subtype
  have hG : G.ker = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have hXZ : (x : V) ∈ Z₀ := hx
    have h0 : (x : V) = 0 := Submodule.disjoint_def.mp hZW.disjoint (x : V) hXZ x.property
    exact (Submodule.mem_bot (R := ℝ)).mpr (Subtype.ext h0)
  obtain ⟨C, hC⟩ := norm_le_of_ker_eq_bot (E := ↥W) (F := ↥T → Mat n) G hG
  have hFsmall {t : ℝ≥0} (ht : t₀ ≤ t) : ‖F (A₀ t)‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro Y
    obtain ⟨s, hs, heq⟩ := hT Y.property
    change ‖(A₀ t : Mat n) * (Y : Mat n) - (Y : Mat n) * (A₀ t : Mat n)‖ ≤ 1
    simpa [A₀, ht, ← heq] using hbound ht hs
  have hRsmall {t : ℝ≥0} (ht : t₀ ≤ t) : ‖R t‖ ≤ (C : ℝ) := by
    have hzero : F (p t : V) = 0 := (p t).property
    have hGval : G (r t) = F (A₀ t) := by
      conv_rhs => rw [hdecomp₀ t, map_add, hzero, zero_add]
      rfl
    have h := hC (r t) (hGval ▸ hFsmall ht)
    exact h
  refine ⟨Z, P, R, Metric.closedBall 0 C, ?_, isCompact_closedBall _ _, ?_, ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop t₀] with t ht
    exact ⟨hdecomp ht, hP t, by simpa [Metric.mem_closedBall, dist_zero_right] using hRsmall ht⟩
  · intro z hz w hw
    obtain ⟨w₀, -, rfl⟩ := hw
    exact hcentral hz w₀.property
  · intro z hz
    exact Eventually.of_forall fun t => hcentral hz (hRV t)
  · refine hA.congr' ?_
    refine eventually_prod_iff.mpr ⟨_, eventually_ge_atTop t₀, _, eventually_ge_atTop t₀, ?_⟩
    intro t ht s hs
    simp only [hdecomp ht, hdecomp hs, add_mul, mul_add]
    rw [(hcentral (hP t) (p s : V).property).eq,
      (hcentral (hP t) (hRV s)).eq, (hcentral (hP s) (hRV t)).eq]
    abel

theorem compactCommutingSpan {n : ℕ} (R : ℝ≥0 → Mat n) (K : Set (Mat n))
    (hK : IsCompact K) (hR : ∀ᶠ t in atTop, R t ∈ K)
    (hcomm : Tendsto (fun p : ℝ≥0 × ℝ≥0 => R p.1 * R p.2 - R p.2 * R p.1)
      (atTop ×ˢ atTop) (𝓝 0)) :
    ∃ S : Submodule ℝ (Mat n), (∀ z ∈ S, ∀ w ∈ S, Commute z w) ∧
      (∀ z : Mat n, (∀ᶠ t in atTop, Commute z (R t)) → ∀ s ∈ S, Commute z s) ∧
      (∀ L : Mat n → Mat n, Continuous L → (∀ s ∈ S, L s = 0) →
        Tendsto (fun t => L (R t)) atTop (𝓝 0)) := by
  let C : Set (Mat n) := {z | MapClusterPt z atTop R}
  have clusterCommute : ∀ a ∈ C, ∀ b ∈ C, Commute a b := by
    intro a ha b hb
    have ha' : MapClusterPt a atTop R := ha
    have hb' : MapClusterPt b atTop R := hb
    let commutator : Mat n × Mat n → Mat n := fun p => p.1 * p.2 - p.2 * p.1
    have hc : Continuous commutator :=
      (continuous_fst.mul continuous_snd).sub (continuous_snd.mul continuous_fst)
    have hpoint := (ha'.prodMap hb').continuousAt_comp (hc.continuousAt (x := (a, b)))
    exact sub_eq_zero.mp (eq_of_nhds_neBot (hpoint.clusterPt.mono hcomm))
  refine ⟨Submodule.span ℝ C, ?_, ?_, ?_⟩
  · intro a ha
    exact Commute.span_right (fun b hb =>
      Commute.span_left (fun x hx => clusterCommute x hx b hb) a ha)
  · intro z hz
    have hclosed : IsClosed {s : Mat n | Commute z s} :=
      isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)
    exact Commute.span_right (fun s hs => hclosed.mem_of_mapClusterPt hs hz)
  · intro L hL hzero
    have hcluster : Tendsto R atTop (𝓝ˢ C) :=
      hK.tendsto_nhdsSet_of_mapClusterPt hR (fun _ _ hx => hx)
    have hlimit : Tendsto L (𝓝ˢ C) (𝓝 0) := by
      rw [Tendsto, map_le_iff_le_comap, nhdsSet_le]
      intro x hx
      rw [← map_le_iff_le_comap]
      simpa only [Tendsto, hzero x (Submodule.subset_span hx)] using hL.tendsto x
    exact hlimit.comp hcluster

theorem projectToCommuting {n : ℕ} (A P R : ℝ≥0 → Mat n)
    (Z S : Submodule ℝ (Mat n)) (hA : Continuous A)
    (hP : ∀ᶠ t in atTop, A t = P t + R t ∧ P t ∈ Z)
    (hZZ : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z)
    (hSS : ∀ s ∈ S, ∀ s' ∈ S, s * s' = s' * s)
    (hZS : ∀ z ∈ Z, ∀ s ∈ S, z * s = s * z)
    (hR : ∀ L : Mat n → Mat n, Continuous L → (∀ s ∈ S, L s = 0) →
      Tendsto (fun t => L (R t)) atTop (𝓝 0)) :
    ∃ B : ℝ≥0 → Mat n, Continuous B ∧
      (∀ t s, B t * B s = B s * B t) ∧
      Tendsto (fun t => A t - B t) atTop (𝓝 0) := by
  classical
  have hcomm (U V : Mat n) (hU : U ∈ Z ⊔ S) (hV : V ∈ Z ⊔ S) : U * V = V * U := by
    obtain ⟨uZ, huZ, uS, huS, rfl⟩ := Submodule.mem_sup.mp hU
    obtain ⟨vZ, hvZ, vS, hvS, rfl⟩ := Submodule.mem_sup.mp hV
    simp only [add_mul, mul_add]
    rw [hZZ uZ huZ vZ hvZ, hSS uS huS vS hvS, hZS uZ huZ vS hvS,
      ← hZS vZ hvZ uS huS]
    abel
  obtain ⟨T, hT⟩ := (Z ⊔ S).exists_isCompl
  let Q : Mat n →ₗ[ℝ] Mat n := (Z ⊔ S).projection T hT
  have hQ : Continuous Q := Q.continuous_of_finiteDimensional
  have hfix (X : Mat n) (hX : X ∈ Z ⊔ S) : Q X = X :=
    Submodule.projection_apply_of_mem_left hT hX
  have hmem (X : Mat n) : Q X ∈ Z ⊔ S := Submodule.projection_apply_mem hT X
  refine ⟨fun t => Q (A t), hQ.comp hA, fun t s => hcomm _ _ (hmem _) (hmem _), ?_⟩
  have hlim := hR (fun X => X - Q X) (continuous_id.sub hQ) (fun X hX => by
    rw [hfix X (Submodule.mem_sup_right hX), sub_self])
  apply hlim.congr'
  filter_upwards [hP] with t ht
  rw [ht.1, map_add, hfix _ (Submodule.mem_sup_left ht.2)]
  abel

end OMA.AsymptoticMatrices

open Filter
open scoped NNReal Topology

theorem OMA.solution : type_of% @OMA.S_mo_474511.main := by
  intro n A hA hcomm
  obtain ⟨Z, P, R, K, hsplit, hK, hZ, hZR, hR⟩ :=
    OMA.AsymptoticMatrices.tailComponents A hcomm
  obtain ⟨S, hS, hcentral, hlimit⟩ :=
    OMA.AsymptoticMatrices.compactCommutingSpan R K hK
      (hsplit.mono fun _ h => h.2.2) hR
  exact OMA.AsymptoticMatrices.projectToCommuting A P R Z S hA
    (hsplit.mono fun _ h => ⟨h.1, h.2.1⟩) hZ hS
    (fun z hz => hcentral z (hZR z hz)) hlimit

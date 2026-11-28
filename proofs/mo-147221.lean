import OMAStatements.S_mo_147221

namespace OMA.S_mo_147221
open Metric Set InnerProductGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private lemma chord_le_angle {u v : E} (hu : ‖u‖=1) (hv : ‖v‖=1) :
    dist u v ≤ angle u v := by
  let t := angle u v / 2
  have ht : 0 ≤ t := by dsimp [t]; positivity [angle_nonneg u v]
  have hπ : t ≤ Real.pi := by
    dsimp [t]
    linarith [angle_le_pi u v, Real.pi_pos]
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi ht hπ
  have hcos : Real.cos (angle u v) = inner ℝ u v := by simpa [hu,hv] using cos_angle u v
  have htwo : 2*t=angle u v := by dsimp [t]; ring
  have hsq := norm_sub_sq_real u v
  rw [hu,hv,← hcos,← htwo,Real.cos_two_mul] at hsq
  have hn : ‖u-v‖ = 2*Real.sin t := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1
    nlinarith [Real.sin_sq_add_cos_sq t]
  rw [dist_eq_norm,hn,← htwo]
  exact mul_le_mul_of_nonneg_left (Real.sin_le ht) (by norm_num)

private lemma quantitative {K : Set E} (hcl : IsClosed K) (hc : Convex ℝ K)
    {r R : ℝ} (hr : 0<r) (hR : 0<R) (hin : ball 0 r ⊆ K) (hout : K ⊆ closedBall 0 R) :
    (∀ u : E, ‖u‖ = 1 → r ≤ radial K u ∧ radial K u ≤ R ∧ radial K u • u ∈ K) ∧
    ∀ u v : E, ‖u‖ = 1 → ‖v‖ = 1 →
      |radial K u - radial K v| ≤ R^2/r * dist u v ∧
      |radial K u - radial K v| ≤ R^2/r * angle u v := by
  have hnb : K ∈ nhds (0:E) := Filter.mem_of_superset (Metric.ball_mem_nhds _ hr) hin
  have hab : Absorbent ℝ K := absorbent_nhds_zero hnb
  have hlower (u : E) (h : ‖u‖=1) : 1/R ≤ gauge K u := by
    simpa only [h] using le_gauge_of_subset_closedBall (x:=u) hab hR.le hout
  have hpos (u : E) (h : ‖u‖=1) : 0 < gauge K u := lt_of_lt_of_le (by positivity) (hlower u h)
  have hmax (u : E) (h : ‖u‖=1) : IsGreatest {t : ℝ | 0<t ∧ t • u ∈ K} (gauge K u)⁻¹ := by
    have hg := hpos u h
    have he (t : ℝ) (ht : 0≤t) : t • u ∈ K ↔ t * gauge K u ≤ 1 := by
      rw [← hcl.closure_eq, ← gauge_le_one_iff_mem_closure hc hnb, gauge_smul_of_nonneg ht]
      simp
    constructor
    · exact ⟨inv_pos.mpr hg, (he _ (inv_nonneg.mpr hg.le)).2 (by rw [inv_mul_cancel₀ hg.ne'])⟩
    · intro t ht
      exact (le_div_iff₀ hg).2 ((he _ ht.1.le).1 ht.2) |> (by simpa only [one_div] using ·)
  have hrad (u : E) (h : ‖u‖=1) : radial K u = (gauge K u)⁻¹ := (hmax u h).csSup_eq
  have hlim (u : E) (h : ‖u‖=1) : r ≤ radial K u ∧ radial K u ≤ R ∧ radial K u • u ∈ K := by
    rw [hrad u h, ← one_div]
    refine ⟨(le_div_iff₀ (hpos u h)).2 (by simpa only [h] using mul_gauge_le_norm (x:=u) hin),
      (div_le_iff₀ (hpos u h)).2 ?_, by simpa [one_div] using (hmax u h).1.2⟩
    simpa [mul_comm] using (div_le_iff₀ hR).1 (hlower u h)
  refine ⟨hlim, ?_⟩
  intro u v hu hv
  let ρ : NNReal := ⟨r,hr.le⟩
  have hlip := (hc.lipschitzWith_gauge (r:=ρ) hr hin).dist_le_mul u v
  change dist (gauge K u) (gauge K v) ≤ (↑(ρ⁻¹) : ℝ) * dist u v at hlip
  rw [Real.dist_eq, NNReal.coe_inv] at hlip
  have he : radial K u - radial K v = (gauge K v - gauge K u)*(radial K u*radial K v) := by
    rw [hrad u hu,hrad v hv]
    field_simp [(hpos u hu).ne', (hpos v hv).ne']
  have hmn := (hlim u hu)
  have hmx := (hlim v hv)
  have hp : 0 ≤ radial K u * radial K v := mul_nonneg (hr.le.trans hmn.1) (hr.le.trans hmx.1)
  have hq : radial K u * radial K v ≤ R^2 := by
    rw [pow_two]; exact mul_le_mul hmn.2.1 hmx.2.1 (hr.le.trans hmx.1) hR.le
  have hch : |radial K u-radial K v| ≤ R^2/r*dist u v := calc
    _ = |gauge K u-gauge K v| * (radial K u*radial K v) := by rw [he,abs_mul,abs_of_nonneg hp,abs_sub_comm]
    _ ≤ (r⁻¹*dist u v)*R^2 := mul_le_mul hlip hq hp (by positivity)
    _ = _ := by ring
  exact ⟨hch,hch.trans (mul_le_mul_of_nonneg_left (chord_le_angle hu hv) (by positivity))⟩

end OMA.S_mo_147221
open OMA.S_mo_147221
theorem OMA.solution : type_of% @OMA.S_mo_147221.main := by
  intro E _ _ K hcl hc
  refine ⟨fun _ _ hr hR hin hout => quantitative hcl hc hr hR hin hout, ?_⟩
  intro hi hb
  obtain ⟨r,hr,hin⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hi)
  obtain ⟨R,hR,hout⟩ := hb.subset_closedBall_lt 0 0
  obtain ⟨_,hl⟩ := quantitative hcl hc hr hR hin hout
  let c : NNReal := ⟨R^2/r,by positivity⟩
  have hLip : LipschitzOnWith c (radial K) (Metric.sphere 0 1) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro u hu v hv
    exact (hl _ _ (by simpa using hu) (by simpa using hv)).1
  exact ⟨hLip.continuousOn, R^2/r, by positivity, fun u v hu hv => (hl u v hu hv).2⟩

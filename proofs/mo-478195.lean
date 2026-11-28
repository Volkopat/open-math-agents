import OMAStatements.S_mo_478195

namespace OMA.S_mo_478195
open Set Metric
open scoped InnerProductSpace

private lemma support {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : Set E} {p : E} (hc : Convex ℝ K) (hp : Nearest K p) (z : E) (hz : z∈K) :
    0 ≤ ⟪p,z-p⟫_ℝ := by
  let : Nonempty K := ⟨⟨p,hp.1⟩⟩
  have hi : ‖(0:E)-p‖ = ⨅ w : K, ‖(0:E)-w.val‖ := by
    simp only [zero_sub,norm_neg]
    apply le_antisymm
    · exact le_ciInf fun w => hp.2 _ w.2
    · exact ciInf_le ⟨0,by rintro x ⟨w,rfl⟩; exact norm_nonneg _⟩ (⟨p,hp.1⟩ : K)
  simpa using (norm_eq_iInf_iff_real_inner_le_zero hc hp.1).mp hi z hz

private lemma upper {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K L : Set E) (p q : E) (hK : IsCompact K) (hL : IsCompact L) (cK : Convex ℝ K)
    (cL : Convex ℝ L) (hp : Nearest K p) (hq : Nearest L q) :
    dist p q ^2 ≤ (‖p‖+‖q‖)*hausdorffDist K L := by
  have oneSide {S T : Set E} {a b : E} (hS : IsCompact S) (hT : IsCompact T)
      (hconv : Convex ℝ S) (ha : Nearest S a) (hb : b∈T) :
      ⟪a,a-b⟫_ℝ ≤ ‖a‖*hausdorffDist S T := by
    obtain ⟨w,hw,hdis⟩ := hS.exists_infDist_eq_dist ⟨a,ha.1⟩ b
    have hfin := hausdorffEDist_ne_top_of_nonempty_of_bounded ⟨b,hb⟩ ⟨a,ha.1⟩ hT.isBounded hS.isBounded
    have hh := infDist_le_hausdorffDist_of_mem hb hfin
    rw [hdis,hausdorffDist_comm,dist_comm,dist_eq_norm] at hh
    have hs := support hconv ha w hw
    have he := real_inner_le_norm a (w-b)
    simp only [inner_sub_right] at *
    linarith [mul_le_mul_of_nonneg_left hh (norm_nonneg a)]
  have h1 := oneSide hK hL cK hp hq.1
  have h2 := oneSide hL hK cL hq hp.1
  rw [hausdorffDist_comm] at h2
  rw [dist_eq_norm,norm_sub_sq_real,←real_inner_self_eq_norm_sq,←real_inner_self_eq_norm_sq]
  simp only [inner_sub_right] at h1 h2
  rw [real_inner_comm p q] at h2
  linarith

private def strip (a t : ℝ) : Set ℂ :=
  {z | a≤z.re ∧ z.re≤1/2 ∧ 0≤z.im ∧ z.im≤1/2 ∧ a^2+t^2≤a*z.re+t*z.im}
private def point (a t : ℝ) : ℂ := ⟨a,t⟩

private lemma strip_closed (a t : ℝ) : IsClosed (strip a t) :=
  (isClosed_le continuous_const Complex.continuous_re).inter
    ((isClosed_le Complex.continuous_re continuous_const).inter
    ((isClosed_le continuous_const Complex.continuous_im).inter
    ((isClosed_le Complex.continuous_im continuous_const).inter
    (isClosed_le continuous_const ((continuous_const.mul Complex.continuous_re).add
      (continuous_const.mul Complex.continuous_im))))))

private lemma strip_convex (a t : ℝ) : Convex ℝ (strip a t) := by
  let f := a • Complex.reCLM + t • Complex.imCLM
  exact (convex_halfSpace_ge Complex.reCLM.toLinearMap.isLinear _).inter
    ((convex_halfSpace_le Complex.reCLM.toLinearMap.isLinear _).inter
    ((convex_halfSpace_ge Complex.imCLM.toLinearMap.isLinear _).inter
    ((convex_halfSpace_le Complex.imCLM.toLinearMap.isLinear _).inter
    (convex_halfSpace_ge f.toLinearMap.isLinear _))))

private lemma strip_ball {a t : ℝ} (ha : 0≤a) : strip a t ⊆ ball 0 1 := by
  intro z hz
  obtain ⟨h1,h2,h3,h4,-⟩ := hz
  rw [mem_ball,dist_zero_right]
  have hRe := mul_self_le_mul_self (ha.trans h1) h2
  have hIm := mul_self_le_mul_self h3 h4
  have hs := Complex.sq_norm z
  rw [Complex.normSq_apply] at hs
  nlinarith

private lemma strip_nearest {a t : ℝ} (ha : a≤1/2) (ht : 0≤t) (ht' : t≤1/2) :
    Nearest (strip a t) (point a t) := by
  refine ⟨⟨le_rfl,ha,ht,ht',by dsimp [point]; ring_nf; rfl⟩,?_⟩
  intro z hz
  have hh := hz.2.2.2.2
  have h1 := Complex.sq_norm z
  have h2 := Complex.sq_norm (point a t)
  simp only [Complex.normSq_apply,point] at h1 h2
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖(⟨a,t⟩:ℂ)‖^2 ≤ ‖z‖^2
  nlinarith [sq_nonneg (z.re-a),sq_nonneg (z.im-t)]

private lemma examples (t : ℝ) (ht : 0<t) (ht' : t<1/4) : ∃ (K L : Set ℂ) (p q : ℂ),
    Body K ∧ Body L ∧ Nearest K p ∧ Nearest L q ∧ hausdorffDist K L ≤ 4*t^2 ∧ t≤dist p q := by
  let a := 1/2-4*t^2
  let K := strip (1/2) 0
  let L := strip a t
  have hat : 1/4 ≤ a := by dsimp [a]; nlinarith [mul_self_lt_mul_self ht.le ht']
  have hal : a≤1/2 := by dsimp [a]; nlinarith [sq_nonneg t]
  have ha : 0≤a := by linarith
  have hmin : a^2+t^2 ≤ a*(1/2) := by
    have hh : a*((1/2)-a) = 4*a*t^2 := by dsimp [a]; ring
    nlinarith [mul_nonneg (show 0≤4*a-1 by linarith) (sq_nonneg t)]
  have hk (y : ℝ) (hy : 0≤y) (hy' : y≤1/2) : point (1/2) y ∈ K :=
    ⟨le_rfl,le_rfl,hy,hy',by dsimp [point]; norm_num⟩
  have hinc : K ⊆ L := by
    intro z hz
    obtain ⟨h1,h2,h3,h4,-⟩ := hz
    have he := le_antisymm h2 h1
    refine ⟨hal.trans h1,h2,h3,h4,?_⟩
    rw [he]
    linarith [mul_nonneg ht.le h3]
  have body {u v : ℝ} (hu : 0≤u) (hi : K ⊆ strip u v) : Body (strip u v) := by
    have hball := strip_ball (t:=v) hu
    have hbd := (isBounded_ball (x:=(0:ℂ)) (r:=1)).subset hball
    refine ⟨(isCompact_iff_isClosed_bounded.mpr ⟨strip_closed u v,hbd⟩), strip_convex u v,hball,?_⟩
    have hm := dist_le_diam_of_mem hbd (hi (hk 0 le_rfl (by norm_num))) (hi (hk (1/2) (by norm_num) le_rfl))
    have hh := Complex.abs_im_le_norm (point (1/2) 0-point (1/2) (1/2))
    rw [dist_eq_norm] at hm
    norm_num [point] at hh
    exact hh.trans hm
  refine ⟨K,L,point (1/2) 0,point a t,body (by norm_num) (fun _ z => z),body ha hinc,
    strip_nearest le_rfl le_rfl (by norm_num),strip_nearest hal ht.le (by linarith),?_,?_⟩
  · apply hausdorffDist_le_of_mem_dist (by positivity)
    · intro x hx; exact ⟨x,hinc hx,by simp; positivity⟩
    · intro z hz
      refine ⟨point (1/2) z.im,hk _ hz.2.2.1 hz.2.2.2.1,?_⟩
      rw [dist_eq_norm]
      have he : z-point (1/2) z.im = ((z.re-1/2:ℝ):ℂ) := by apply Complex.ext <;> simp [point]
      rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hz.2.1)]
      have hh := hz.1
      dsimp [a] at hh
      linarith
  · have hh := Complex.abs_im_le_norm (point (1/2) 0-point a t)
    simpa [dist_eq_norm,point,abs_of_pos ht] using hh

private lemma unbounded_ratio (C : ℝ) (hC : 0≤C) : ∃ (K L : Set ℂ) (p q : ℂ),
    Body K ∧ Body L ∧ Nearest K p ∧ Nearest L q ∧ C*hausdorffDist K L < dist p q := by
  let t : ℝ := 1/(8*(C+1))
  have ht : 0<t := by dsimp [t]; positivity
  have he : t*(8*(C+1))=1 := by dsimp [t]; field_simp
  have hp : t<1/4 := by nlinarith [mul_nonneg ht.le hC]
  obtain ⟨K,L,p,q,hK,hL,hp',hq,hD,hd⟩ := examples t ht hp
  refine ⟨K,L,p,q,hK,hL,hp',hq,?_⟩
  have hu : 4*C*t < 1 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hD hC,mul_lt_mul_of_pos_right hu ht]

end OMA.S_mo_478195

theorem OMA.solution : type_of% @OMA.S_mo_478195.main :=
  ⟨fun _ _ _ => OMA.S_mo_478195.upper,OMA.S_mo_478195.examples,OMA.S_mo_478195.unbounded_ratio⟩

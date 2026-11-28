import OMAReductions.R_Hilbert5_hilbert_smith_conjecture_variants_dimension_three_R1

/-!
# Localization of the p-adic obstruction in three dimensions

Following §4.1 of John Pardon's *The Hilbert–Smith conjecture for three-manifolds*
(2013, arXiv:1112.2324), separate Newman's local-to-global theorem for periodic
actions from the geometric obstruction on a connected Euclidean domain between
concentric balls of radii r and r(1 + 2⁻¹⁰), with all motion at most r/1024.
The localization uses a connected open neighborhood whose translates have a
common point and a closed-kernel argument using density of the natural numbers.

Credit: @AlfredMelson
-/

open Set Filter Topology Metric

namespace OMA.R_Hilbert5_hilbert_smith_conjecture_variants_dimension_three_R1_H3_R1

private theorem powers_in_nhds {p : ℕ} [Fact p.Prime] {s : Set ℤ_[p]} (hs : s ∈ 𝓝 0) :
    ∃ k : ℕ, ∀ z : ℤ_[p],(p:ℤ_[p])^k*z ∈ s := by
  obtain ⟨ε,he,sub⟩ := Metric.mem_nhds_iff.mp hs
  obtain ⟨k,hk⟩ := PadicInt.exists_pow_neg_lt (p:=p) he
  refine ⟨k,fun z => sub ?_⟩
  rw [Metric.mem_ball,dist_zero_right,norm_mul,PadicInt.norm_p_pow]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one z)) hk

private theorem open_kernel {p : ℕ} [Fact p.Prime] {X : Type*} [TopologicalSpace X]
    [T2Space X] [AddAction ℤ_[p] X] [ContinuousVAdd ℤ_[p] X]
    (h : ¬ FaithfulVAdd ℤ_[p] X) :
    ∃ k : ℕ, ∀ z : ℤ_[p], ∀ x : X, ((p:ℤ_[p])^k*z) +ᵥ x=x := by
  obtain ⟨a,b,hab,he⟩ : ∃ a b : ℤ_[p], a ≠ b ∧ ∀ x : X, a +ᵥ x=b +ᵥ x := by
    by_contra! contra
    exact h ⟨fun {a b} he => by
      by_contra hn
      obtain ⟨x,hx⟩ := contra a b hn
      exact hx (he x)⟩
  let w := a-b
  have hw : w ≠ 0 := sub_ne_zero.mpr hab
  have fix (x : X) : w +ᵥ x=x := by
    dsimp [w]
    rw [sub_eq_add_neg,add_vadd,he,← add_vadd,add_neg_cancel,zero_vadd]
  have mult (r : ℤ_[p]) (x : X) : (r*w) +ᵥ x=x := by
    refine DenseRange.induction_on (PadicInt.denseRange_natCast (p:=p)) (p:=fun r => (r*w) +ᵥ x=x) r ?_ ?_
    · exact isClosed_eq (by fun_prop) continuous_const
    · intro n; induction n with
      | zero => simp
      | succ n ih => rw [Nat.cast_succ,add_mul,one_mul,add_vadd,fix,ih]
  refine ⟨w.valuation,fun z x => ?_⟩
  let u := PadicInt.unitCoeff hw
  have hw' : w=(u:ℤ_[p])*(p:ℤ_[p])^w.valuation := PadicInt.unitCoeff_spec hw
  have e : (z*(↑u⁻¹:ℤ_[p]))*w=(p:ℤ_[p])^w.valuation*z := by
    calc
      _ = z * (((↑u⁻¹:ℤ_[p])*(u:ℤ_[p]))*(p:ℤ_[p])^w.valuation) := by
        calc
          _ = (z*↑u⁻¹)*((u:ℤ_[p])*(p:ℤ_[p])^w.valuation) := congrArg ((z*↑u⁻¹) * ·) hw'
          _ = _ := by ring
      _ = _ := by simp [mul_comm]
  rw [← e]; exact mult _ _

private theorem uniform_chart {p : ℕ} [Fact p.Prime] {X E : Type*} [TopologicalSpace X]
    [PseudoMetricSpace E] [AddAction ℤ_[p] X] [ContinuousVAdd ℤ_[p] X]
    (e : OpenPartialHomeomorph X E) (K : Set X) (hc : IsCompact K)
    (sub : K ⊆ e.source) {ε : ℝ} (hp : 0 < ε) :
    ∃ k : ℕ, ∀ z : ℤ_[p], ∀ y ∈ K,
      ((p:ℤ_[p])^k*z) +ᵥ y ∈ e.source ∧ dist (e (((p:ℤ_[p])^k*z) +ᵥ y)) (e y)<ε := by
  let W : Set (ℤ_[p] × X) := {t | t.2 ∈ e.source ∧ t.1 +ᵥ t.2 ∈ e.source ∧
    dist (e (t.1 +ᵥ t.2)) (e t.2)<ε}
  have op : IsOpen W := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ⟨h1,h2,h3⟩
    have c1 := (e.continuousAt h1).comp (continuous_snd.continuousAt (x:=t))
    have c2 := (e.continuousAt h2).comp (f:=fun s : ℤ_[p] × X => s.1 +ᵥ s.2) (continuous_vadd.continuousAt (x:=t))
    exact inter_mem (continuous_snd.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds h1))
      (inter_mem (continuous_vadd.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds h2))
        ((c2.dist c1) (Iio_mem_nhds h3)))
  have subset : ({0}:Set ℤ_[p]) ×ˢ K ⊆ W := by
    rintro ⟨g,y⟩ ⟨hg,hy⟩
    obtain rfl : g=0 := hg
    exact ⟨sub hy,by simpa using sub hy,by simpa using hp⟩
  obtain ⟨N,T,hN,_,hn,ht,hnt⟩ := generalized_tube_lemma isCompact_singleton hc op subset
  obtain ⟨k,hk⟩ := powers_in_nhds (hN.mem_nhds (hn rfl))
  exact ⟨k,fun z y hy => (@hnt ((p:ℤ_[p])^k*z,y) ⟨hk z,ht hy⟩).2⟩

private theorem chart_ball {p : ℕ} [Fact p.Prime] {X : Type*} [TopologicalSpace X]
    [AddAction ℤ_[p] X] [ContinuousVAdd ℤ_[p] X]
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 3))) (x : X) (hx : x ∈ e.source) :
    ∃ r : ℝ, 0 < r ∧ ∃ k : ℕ, ∃ V : Set X,
      IsOpen V ∧ IsConnected V ∧ x ∈ V ∧ V ⊆ e.source ∧
      ball (e x) r ⊆ e '' V ∧ e '' V ⊆ ball (e x) (r+r/1024) ∧
      ∀ z : ℤ_[p], ∀ y ∈ V, ((p:ℤ_[p])^k*z) +ᵥ y ∈ V ∧
        dist (e (((p:ℤ_[p])^k*z) +ᵥ y)) (e y) ≤ r/1024 := by
  obtain ⟨r,hr,rb⟩ := nhds_basis_closedBall.mem_iff.mp (e.open_target.mem_nhds (e.map_source hx))
  let D := ball (e x) r
  have dt : D ⊆ e.target := ball_subset_closedBall.trans rb
  let T := e.symm '' D
  let K := e.symm '' closedBall (e x) r
  have tk : T ⊆ K := image_mono ball_subset_closedBall
  have ks : K ⊆ e.source := by rintro _ ⟨b,hb,rfl⟩; exact e.map_target (rb hb)
  have kc : IsCompact K := (isCompact_closedBall _ _).image_of_continuousOn (e.symm.continuousOn.mono rb)
  have opT : IsOpen T := e.isOpen_image_symm_of_subset_target isOpen_ball dt
  have ct : IsConnected T := (isConnected_ball hr).image e.symm (e.symm.continuousOn.mono dt)
  have xt : x ∈ T := ⟨e x,mem_ball_self hr,e.left_inv hx⟩
  have td : T = e.source ∩ e ⁻¹' D := e.symm_image_eq_source_inter_preimage dt
  obtain ⟨k,hk⟩ := uniform_chart (p:=p) e K kc ks (ε:=r/2048) (by positivity)
  let f (z : ℤ_[p]) (y : X) := ((p:ℤ_[p])^k*z) +ᵥ y
  have motion (z : ℤ_[p]) {y} (hy : y ∈ T) :
      f z y ∈ e.source ∧ dist (e (f z y)) (e y)<r/2048 := hk z y (tk hy)
  let V := ⋃ z : ℤ_[p], f z '' T
  have incl : T ⊆ V := fun y hy => mem_iUnion.mpr ⟨0,y,hy,by simp [f]⟩
  have each (z : ℤ_[p]) : x ∈ f z '' T := by
    have h := motion (-z) xt
    refine ⟨f (-z) x,?_,by simp [f,← add_vadd]⟩
    rw [td]
    exact ⟨h.1,show dist (e (f (-z) x)) (e x)<r by linarith [h.2]⟩
  refine ⟨r,hr,k,V,isOpen_iUnion (fun z => isOpenMap_vadd _ T opT),⟨⟨x,incl xt⟩,?_⟩,incl xt,?_,?_,?_,?_⟩
  · apply isPreconnected_iUnion ⟨x,mem_iInter.mpr each⟩
    intro z; exact ct.isPreconnected.image _ (by fun_prop : Continuous (f z)).continuousOn
  · intro y hy; obtain ⟨z,t,ht,rfl⟩ := mem_iUnion.mp hy
    exact (motion z ht).1
  · intro y hy
    exact ⟨e.symm y,incl ⟨y,hy,rfl⟩,e.right_inv (dt hy)⟩
  · rintro _ ⟨y,hy,rfl⟩
    obtain ⟨z,t,ht,rfl⟩ := mem_iUnion.mp hy
    have d1 := (motion z ht).2
    rw [td] at ht
    have d2 : dist (e t) (e x)<r := ht.2
    exact show dist (e (f z t)) (e x)<r+r/1024 by linarith [dist_triangle (e (f z t)) (e t) (e x)]
  · intro z y hy
    obtain ⟨q,t,ht,rfl⟩ := mem_iUnion.mp hy
    have law : ((p:ℤ_[p])^k*z) +ᵥ f q t=f (z+q) t := by simp [f,mul_add,add_vadd]
    rw [law]
    refine ⟨mem_iUnion.mpr ⟨z+q,t,ht,rfl⟩,?_⟩
    have h1 := (motion (z+q) ht).2
    have h2 := (motion q ht).2
    linarith [dist_triangle_right (e (f (z+q) t)) (e (f q t)) (e t)]

/-- Newman's local-to-global assertion: a p-adic action locally killed by powers of p
is killed by a single power on the whole connected manifold. For each point, its
closed stabilizer contains all p-adic multiples of any generator that fixes it. -/
def H1 : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] (p : ℕ) [Fact p.Prime]
    [AddAction ℤ_[p] X] [ContinuousVAdd ℤ_[p] X],
    (∀ x : X, ∃ V ∈ 𝓝 x, ∃ k : ℕ, ∀ y ∈ V, (p:ℤ_[p])^k +ᵥ y = y) →
    ∃ m : ℕ, ∀ y : X, (p:ℤ_[p])^m +ᵥ y = y

/-- Pardon's local Euclidean problem (§4.1, conditions i–iii) with an arbitrary
center and length scale. In a faithful action with displacement at most 2⁻¹⁰
times the inner radius, some power must fix a neighborhood of the center. -/
def H2 : Prop :=
  ∀ (Y : Type) [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y]
    (e : Y → EuclideanSpace ℝ (Fin 3)), IsOpenEmbedding e → ∀ (y₀ : Y) (r : ℝ), 0 < r →
    Metric.ball (e y₀) r ⊆ range e → range e ⊆ Metric.ball (e y₀) (r+r/1024) →
    ∀ (p : ℕ) [Fact p.Prime] [AddAction ℤ_[p] Y] [ContinuousVAdd ℤ_[p] Y],
      (∀ (z : ℤ_[p]) (y : Y), dist (e (z +ᵥ y)) (e y) ≤ r/1024) →
      FaithfulVAdd ℤ_[p] Y →
      ∃ W : Set Y, IsOpen W ∧ y₀ ∈ W ∧ ∃ m : ℕ, ∀ y ∈ W, (p:ℤ_[p])^m +ᵥ y=y

theorem main : H1 → H2 → OMA.R_Hilbert5_hilbert_smith_conjecture_variants_dimension_three_R1.H3 := by
  intro global localOb X _ _ _ _ p _ _ _ faith
  let E := EuclideanSpace ℝ (Fin 3)
  obtain ⟨m,hm⟩ := global X p (by
    intro x
    let e := chartAt E x
    have hx : x ∈ e.source := mem_chart_source E x
    obtain ⟨r,hr,k,V,vo,vc,xv,inc,inner,outer,stable⟩ := chart_ball (p:=p) e x hx
    let : ConnectedSpace V := isConnected_iff_connectedSpace.mp vc
    let : AddAction ℤ_[p] V := {
      vadd z y := ⟨((p:ℤ_[p])^k*z) +ᵥ (y:X), (stable z _ y.property).1⟩
      zero_vadd y := Subtype.ext (by change ((p:ℤ_[p])^k*0) +ᵥ (y:X) = y; simp)
      add_vadd z r y := Subtype.ext (by
        change ((p:ℤ_[p])^k*(z+r)) +ᵥ (y:X) = ((p:ℤ_[p])^k*z) +ᵥ (((p:ℤ_[p])^k*r) +ᵥ (y:X))
        simp [mul_add,add_vadd]) }
    let : ContinuousVAdd ℤ_[p] V := ⟨by
      apply Continuous.subtype_mk
      exact (show Continuous (fun t : ℤ_[p] × V => ((p:ℤ_[p])^k*t.1) +ᵥ (t.2:X)) by fun_prop)⟩
    have emb := e.isOpenEmbedding_restrict.comp
      (Topology.IsOpenEmbedding.inclusion inc (vo.preimage continuous_subtype_val))
    let f : V → E := fun y => e (y:X)
    let y₀ : V := ⟨x,xv⟩
    have image : range f = e '' V := by ext y; simp [f]
    by_cases honest : FaithfulVAdd ℤ_[p] V
    · obtain ⟨W,opW,memW,l,hl⟩ := localOb V f emb y₀ r hr (by rw [image]; exact inner)
        (by rw [image]; exact outer) p (fun z y => (stable z _ y.property).2) honest
      have op := vo.isOpenMap_subtype_val W opW
      refine ⟨Subtype.val '' W,op.mem_nhds ⟨y₀,memW,rfl⟩,k+l,?_⟩
      rintro _ ⟨y,hy,rfl⟩
      have eq := congrArg Subtype.val (hl y hy)
      change ((p:ℤ_[p])^k*(p:ℤ_[p])^l) +ᵥ (y:X)=(y:X) at eq
      simpa [pow_add] using eq
    · obtain ⟨l,hl⟩ := open_kernel honest
      refine ⟨V,vo.mem_nhds xv,k+l,?_⟩
      intro y hy
      have eq := congrArg Subtype.val (hl 1 ⟨y,hy⟩)
      change ((p:ℤ_[p])^k*((p:ℤ_[p])^l*1)) +ᵥ y=y at eq
      simpa [pow_add] using eq)
  apply pow_ne_zero m (show (p:ℤ_[p]) ≠ 0 by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)
  exact faith.eq_of_vadd_eq_vadd (fun y => by simpa using hm y)

end OMA.R_Hilbert5_hilbert_smith_conjecture_variants_dimension_three_R1_H3_R1

import OMAStatements.S_mo_486704
/-!
Credited port of the complete proof by @connoranderson, companion to statement PR #26657
and desk DONE #121788, pinned at:
https://github.com/connoranderson/open-math-agents/blob/d0737db4a9c33695504d37c12b3ae9fe3936de97/proofs/mo-486704.lean
Source question by kd202149 and geometric/gradient-flow arguments by Pietro Majer:
https://mathoverflow.net/questions/486704 (CC BY-SA 4.0). Mathematical source unchanged.

The supporting hyperplanes at a minimizer and at the exterior point provide the
two endpoint tilts. For each intermediate tilt, minimize on both sides of the
distance level, inside a common compact ball. Continuity of the minimum values
and convexity of the objective force a common minimizer on the distance level.
The set of gradients of bounded norm over this level is compact by the global
supporting-hyperplane characterization.
-/
namespace OMA.S_mo_486704
open Set Metric Filter
open scoped Topology

private theorem supporting {d : ℕ} {f : E d → ℝ} (hc : ConvexOn ℝ univ f)
    (hf : Differentiable ℝ f) (x y : E d) :
    (fderiv ℝ f x) (y-x) ≤ f y - f x := by
  let l : ℝ →ᵃ[ℝ] E d := AffineMap.lineMap x y
  have hconv : ConvexOn ℝ univ (f ∘ l) := by simpa [l] using hc.comp_affineMap l
  have hh := (hf (l 0)).hasFDerivAt.comp_hasDerivAt 0
    (show HasDerivAt (fun t : ℝ => l t) (y-x) 0 from AffineMap.hasDerivAt_lineMap)
  have hh' : HasDerivAt (f ∘ l) (fderiv ℝ f x (y-x)) 0 := by simpa [l] using hh
  simpa [slope, l] using hconv.le_slope_of_hasDerivAt (Set.mem_univ (0:ℝ))
    (Set.mem_univ (1:ℝ)) zero_lt_one hh'

private theorem supporting_unique {d : ℕ} {f : E d → ℝ} (hf : Differentiable ℝ f)
    (x : E d) (L : E d →L[ℝ] ℝ) (h : ∀ y, L (y-x) ≤ f y-f x) :
    L = fderiv ℝ f x := by
  have hmin : IsMinOn (fun y => f y - L y) univ x := isMinOn_univ_iff.mpr fun y => by
    have := h y
    rw [map_sub] at this
    linarith
  have hzero := (hmin.isLocalMin univ_mem).fderiv_eq_zero
  have deriv := ((hf x).hasFDerivAt.sub (L.hasFDerivAt (x := x))).fderiv
  change fderiv ℝ (f - ⇑L) x = 0 at hzero
  rw [deriv] at hzero
  exact (sub_eq_zero.mp hzero).symm

private theorem level_bounded {d : ℕ} {f : E d → ℝ}
    (hf : Continuous f) (hne : (minimizers f).Nonempty)
    (hb : Bornology.IsBounded (minimizers f)) (δ : ℝ) :
    Bornology.IsBounded {x | infDist x (minimizers f) ≤ δ} := by
  have hclosed : IsClosed (minimizers f) := by
    change IsClosed {x | ∀ y, f x ≤ f y}
    simp only [ofPred_forall]
    exact isClosed_iInter fun y => isClosed_le hf continuous_const
  obtain ⟨R,hR⟩ := hb.subset_ball (0 : E d)
  refine (isBounded_closedBall (x := (0:E d)) (r := R+δ)).subset ?_
  intro x hx
  obtain ⟨p,hp,he⟩ := hclosed.exists_infDist_eq_dist hne x
  have hpx := hR hp
  change dist p 0 < R at hpx
  change infDist x (minimizers f) ≤ δ at hx
  change dist x 0 ≤ R+δ
  linarith [dist_triangle x p 0]
private theorem crossing {d : ℕ} (K : Set (E d)) (hK : IsCompact K)
    (F : ℝ → E d → ℝ) (hF : Continuous ↿F) (hc : ∀ t, ConvexOn ℝ K (F t))
    (D : E d → ℝ) (hD : Continuous D) (δ : ℝ) (a b : E d)
    (ha : a ∈ K) (hb : b ∈ K) (haD : D a ≤ δ) (hbD : δ ≤ D b)
    (haMin : ∀ x ∈ K, F 0 a ≤ F 0 x) (hbMin : ∀ x ∈ K, F 1 b ≤ F 1 x) :
    ∃ t ∈ Icc (0:ℝ) 1, ∃ z ∈ K, D z = δ ∧ ∀ x ∈ K, F t z ≤ F t x := by
  let A := K ∩ {x | D x ≤ δ}
  let B := K ∩ {x | δ ≤ D x}
  have hA : IsCompact A := hK.inter_right (isClosed_le hD continuous_const)
  have hB : IsCompact B := hK.inter_right (isClosed_le continuous_const hD)
  have haA : a ∈ A := ⟨ha,haD⟩
  have hbB : b ∈ B := ⟨hb,hbD⟩
  let va (t : ℝ) := sInf (F t '' A)
  let vb (t : ℝ) := sInf (F t '' B)
  have hvA : Continuous va := hA.continuous_sInf hF
  have hvB : Continuous vb := hB.continuous_sInf hF
  have amin (t : ℝ) : ∃ x ∈ A, va t = F t x ∧ ∀ w ∈ A, F t x ≤ F t w :=
    hA.exists_sInf_image_eq_and_le ⟨a,haA⟩ (hF.comp (Continuous.prodMk_right t)).continuousOn
  have bmin (t : ℝ) : ∃ x ∈ B, vb t = F t x ∧ ∀ w ∈ B, F t x ≤ F t w :=
    hB.exists_sInf_image_eq_and_le ⟨b,hbB⟩ (hF.comp (Continuous.prodMk_right t)).continuousOn
  have h0 : va 0 ≤ vb 0 := by
    obtain ⟨x,_,hx,hxm⟩ := amin 0
    obtain ⟨y,hy,hy',_⟩ := bmin 0
    rw [hx,hy']
    exact (hxm a haA).trans (haMin y hy.1)
  have h1 : vb 1 ≤ va 1 := by
    obtain ⟨x,hx,hx',_⟩ := amin 1
    obtain ⟨y,_,hy,hym⟩ := bmin 1
    rw [hx',hy]
    exact (hym b hbB).trans (hbMin x hx.1)
  obtain ⟨t,ht,he⟩ := isPreconnected_Icc.intermediate_value₂
    (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
    hvA.continuousOn hvB.continuousOn h0 h1
  obtain ⟨x,hx,hx',hxm⟩ := amin t
  obtain ⟨y,hy,hy',hym⟩ := bmin t
  let C := {z ∈ K | F t z ≤ va t}
  have hC : Convex ℝ C := (hc t).convex_le _
  have hxC : x ∈ C := ⟨hx.1,hx'.ge⟩
  have hyC : y ∈ C := ⟨hy.1,(he.trans hy').ge⟩
  obtain ⟨z,hz,hzδ⟩ := hC.isPreconnected.intermediate_value hxC hyC hD.continuousOn
    (show δ ∈ Icc (D x) (D y) from ⟨hx.2,hy.2⟩)
  refine ⟨t,ht,z,hz.1,hzδ,fun w hw => hz.2.trans ?_⟩
  rcases le_total (D w) δ with hwD | hwD
  · exact hx'.trans_le (hxm w ⟨hw,hwD⟩)
  · exact (he.trans hy').trans_le (hym w ⟨hw,hwD⟩)
private theorem boundary_tilt {d : ℕ} {f : E d → ℝ} (hc : ConvexOn ℝ univ f)
    (hf : Differentiable ℝ f) (hne : (minimizers f).Nonempty)
    (hb : Bornology.IsBounded (minimizers f)) (δ : ℝ) (hδ : 0 < δ)
    (y : E d) (hy : δ ≤ infDist y (minimizers f)) :
    ∃ z : E d, infDist z (minimizers f) = δ ∧
      ∃ t ∈ Icc (0:ℝ) 1, fderiv ℝ f z = t • fderiv ℝ f y := by
  let D := fun x => infDist x (minimizers f)
  let a := hne.choose
  have ha := hne.choose_spec
  have haD : D a ≤ δ := (infDist_zero_of_mem ha).trans_le hδ.le
  obtain ⟨R,hR⟩ := (level_bounded hf.continuous hne hb δ).subset_ball (0:E d)
  let r := max R (‖y‖ + 1)
  let K := closedBall (0:E d) r
  have hA (x : E d) (hx : D x ≤ δ) : x ∈ ball (0:E d) r :=
    lt_of_lt_of_le (show dist x 0 < R from hR hx) (le_max_left _ _)
  have hK : Convex ℝ K := convex_closedBall _ _
  have hyK : y ∈ K := by
    change dist y 0 ≤ max R (‖y‖+1)
    rw [dist_zero_right]
    exact (by linarith : ‖y‖ ≤ ‖y‖+1).trans (le_max_right _ _)
  let L := fderiv ℝ f y
  let F := fun (t : ℝ) (x : E d) => f x - t * L x
  have hF : Continuous ↿F := by
    exact (hf.continuous.comp continuous_snd).sub
      (continuous_fst.mul (L.continuous.comp continuous_snd))
  have hC (t : ℝ) : ConvexOn ℝ K (F t) :=
    (hc.subset (subset_univ _) hK).sub ((t • L).toLinearMap.concaveOn hK)
  have h0 (x : E d) (_ : x ∈ K) : F 0 a ≤ F 0 x := by simpa [F] using ha x
  have h1 (x : E d) (_ : x ∈ K) : F 1 y ≤ F 1 x := by
    have h := supporting hc hf y x
    change L (x - y) ≤ _ at h
    rw [map_sub] at h
    simp only [F,one_mul]
    linarith
  obtain ⟨t,ht,z,_,hz,hmin⟩ := crossing K (isCompact_closedBall _ _) F hF hC D
    (continuous_infDist_pt _) δ a y (ball_subset_closedBall (hA a haD)) hyK haD hy h0 h1
  have hloc : IsLocalMin (F t) z := (isMinOn_iff.mpr hmin).isLocalMin
    (mem_of_superset (isOpen_ball.mem_nhds (hA z hz.le)) ball_subset_closedBall)
  have hderiv : HasFDerivAt (F t) (fderiv ℝ f z - t • L) z :=
    (hf z).hasFDerivAt.sub ((t • L).hasFDerivAt (x := z))
  exact ⟨z,hz,t,ht,sub_eq_zero.mp (hderiv.fderiv.symm.trans hloc.fderiv_eq_zero)⟩
private theorem boundary_min {d : ℕ} {f : E d → ℝ} (hc : ConvexOn ℝ univ f)
    (hf : Differentiable ℝ f) (hne : (minimizers f).Nonempty)
    (hb : Bornology.IsBounded (minimizers f)) (δ : ℝ) (w : E d)
    (hw : infDist w (minimizers f) = δ) :
    ∃ z : E d, infDist z (minimizers f) = δ ∧
      ∀ x : E d, infDist x (minimizers f) = δ → ‖fderiv ℝ f z‖ ≤ ‖fderiv ℝ f x‖ := by
  let X := {x | infDist x (minimizers f) = δ}
  have hX : IsCompact X := isCompact_of_isClosed_isBounded
    (isClosed_eq (continuous_infDist_pt _) continuous_const)
    ((level_bounded hf.continuous hne hb δ).subset fun _ hx => (show _ = _ from hx).le)
  let D := E d →L[ℝ] ℝ
  let M := ‖fderiv ℝ f w‖
  let C : Set (E d × D) := {p | ∀ y, p.2 (y-p.1) ≤ f y - f p.1}
  have hC : IsClosed C := by
    simp only [C,ofPred_forall]
    exact isClosed_iInter fun y => isClosed_le
      (continuous_snd.clm_apply (continuous_const.sub continuous_fst))
      (continuous_const.sub (hf.continuous.comp continuous_fst))
  let K : Set (E d × D) := (X ×ˢ closedBall 0 M) ∩ C
  have hK : IsCompact K := (hX.prod (isCompact_closedBall _ _)).inter_right hC
  have mem (x : E d) (hx : x ∈ X) (hn : ‖fderiv ℝ f x‖ ≤ M) :
      (x,fderiv ℝ f x) ∈ K := ⟨⟨hx, by simpa [mem_closedBall] using hn⟩,supporting hc hf x⟩
  obtain ⟨p,hp,hmin⟩ := hK.exists_isMinOn ⟨_,mem w hw le_rfl⟩
    (f := fun p : E d × D => ‖p.2‖) continuous_snd.norm.continuousOn
  have hpD := supporting_unique hf p.1 p.2 hp.2
  refine ⟨p.1,hp.1.1,fun x hx => ?_⟩
  rw [← hpD]
  by_cases hn : ‖fderiv ℝ f x‖ ≤ M
  · exact hmin (mem x hx hn)
  · exact (show ‖p.2‖ ≤ M by simpa [mem_closedBall] using hp.1.2).trans (le_of_not_ge hn)

end OMA.S_mo_486704

open Set Metric OMA.S_mo_486704 in
theorem OMA.solution : type_of% @OMA.S_mo_486704.main := by
  intro d hd f hc hf hne hb δ hδ
  have npos : NeZero d := ⟨hd.ne'⟩
  have tilt := boundary_tilt hc hf hne hb δ hδ
  obtain ⟨R,hR⟩ := (level_bounded hf.continuous hne hb δ).subset_ball (0 : E d)
  obtain ⟨y,hy⟩ := NormedSpace.exists_lt_norm ℝ (E d) R
  have hdist : δ < infDist y (minimizers f) := by
    by_contra! h
    have := hR h
    simp only [mem_ball,dist_zero_right] at this
    linarith
  obtain ⟨w,hw,_⟩ := tilt y hdist.le
  obtain ⟨z,hz,hmin⟩ := boundary_min hc hf hne hb δ w hw
  have eqnorm (x : E d) : ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by simp [gradient]
  refine ⟨⟨z,hz,fun x hx => ?_⟩,fun x hx => ?_⟩
  · obtain ⟨v,hv,t,ht,he⟩ := tilt x hx
    simp only [eqnorm]
    calc
      _ ≤ ‖fderiv ℝ f v‖ := hmin v hv
      _ = t*‖fderiv ℝ f x‖ := by rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
      _ ≤ _ := mul_le_of_le_one_left (norm_nonneg _) ht.2
  · obtain ⟨v,hv,t,ht,he⟩ := tilt x hx.le
    exact ⟨v,hv,t,ht,by simp [gradient,he]⟩


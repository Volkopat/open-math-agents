import OMAStatements.S_mo_404448

namespace OMA.S_mo_404448
open Set MeasureTheory
/-- A closed relation with nonempty compact-metric target fibers admits a
Borel selection. Code the target by the real Cantor set and choose the least
code in each fiber. Closedness of the sublevel sets follows by projecting
a closed subset along the compact Cantor coordinate. -/
lemma select_closed {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [MetricSpace Y] [CompactSpace Y] [Nonempty Y] [MeasurableSpace Y] [BorelSpace Y]
    (S : Set (X × Y)) (hc : IsClosed S) (hn : ∀ x, ∃ y, (x,y)∈S) :
    ∃ g : X → Y, Measurable g ∧ ∀ x, (x,g x)∈S := by
  classical
  let _ : CompactSpace cantorSet := isCompact_iff_compactSpace.mp isCompact_cantorSet
  obtain ⟨f,hf,hs⟩ := exists_nat_bool_continuous_surjective_of_compact Y
  let h : cantorSet → Y := f ∘ cantorSetHomeomorphNatToBool
  have hcont : Continuous h := hf.comp cantorSetHomeomorphNatToBool.continuous
  have hsur : Function.Surjective h := hs.comp cantorSetHomeomorphNatToBool.surjective
  let fiber := fun x : X => {a : cantorSet | (x,h a)∈S}
  have hne (x : X) : (fiber x).Nonempty := by
    obtain ⟨y,hy⟩ := hn x
    obtain ⟨a,rfl⟩ := hsur y
    exact ⟨a,hy⟩
  have hcomp (x : X) : IsCompact (fiber x) :=
    (hc.preimage (continuous_const.prodMk hcont)).isCompact
  choose a ha hmin using fun x => (hcomp x).exists_isMinOn (hne x) (f:=fun u : cantorSet => (u:ℝ))
    continuous_subtype_val.continuousOn
  let t : X → ℝ := fun x => a x
  have hm : Measurable t := by
    apply measurable_of_Iic
    intro r
    let B := {z : X × cantorSet | (z.1,h z.2) ∈ S ∧ (z.2:ℝ) ≤ r}
    have hB : IsClosed B := (hc.preimage (continuous_fst.prodMk (hcont.comp continuous_snd))).inter
      (isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const)
    have hpre : t ⁻¹' Iic r = Prod.fst '' B := by
      ext x
      constructor
      · intro hx
        exact ⟨(x,a x),⟨ha x,hx⟩,rfl⟩
      · rintro ⟨⟨x,u⟩,⟨hu,hr⟩,rfl⟩
        exact ((isMinOn_iff.mp (hmin x)) u hu).trans hr
    rw [hpre]
    exact (isClosedMap_fst_of_compactSpace B hB).measurableSet
  have ham : Measurable a := hm.subtype_mk
  exact ⟨fun x => h (a x),hcont.measurable.comp ham,ha⟩
end OMA.S_mo_404448

namespace OMA.S_mo_404448
open Matrix Set

private lemma svd_exists_tall {n m : ℕ} (hmn : m ≤ n) (A : Rect n m) :
    ∃ q : Pair n m, diagOK (middle A q) := by
  classical
  let H := (isHermitian_conjTranspose_mul_self A)
  let V : U m := H.eigenvectorUnitary
  let B : Rect n m := A * (V : Rect m m)
  let b (j : Fin m) : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (Bᵀ j)
  have hgram : Bᴴ * B = Matrix.diagonal (RCLike.ofReal ∘ H.eigenvalues) := by
    simpa only [B, V, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose, Matrix.mul_assoc,
      Unitary.conjStarAlgAut_star_apply] using H.conjStarAlgAut_star_eigenvectorUnitary
  have horth (i j : Fin m) (hij : i ≠ j) : inner ℂ (b i) (b j) = 0 := by
    change inner ℂ (WithLp.toLp 2 (Bᵀ i)) (WithLp.toLp 2 (Bᵀ j)) = 0
    rw [inner_matrix_col_col, hgram, Matrix.diagonal_apply_ne _ hij]
  let v (j : Fin m) := (‖b j‖⁻¹ : ℝ) • b j
  let f : Fin n → EuclideanSpace ℂ (Fin n) := Function.extend (Fin.castLE hmn) v 0
  let s : Set (Fin n) := (Fin.castLE hmn) '' {j | b j ≠ 0}
  have hf (j : Fin m) : f (Fin.castLE hmn j) = v j :=
    (Fin.castLE_injective hmn).extend_apply v 0 j
  have ho : Orthonormal ℂ (s.domRestrict f) := by
    constructor
    · rintro ⟨_,j,hj,rfl⟩
      change ‖f (Fin.castLE hmn j)‖ = 1
      rw [hf]; dsimp only [v]; rw [norm_smul_of_nonneg (by positivity), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hj)]
    · rintro ⟨_,i,hi,rfl⟩ ⟨_,j,hj,rfl⟩ hne
      have hij : i ≠ j := by
        rintro rfl
        exact hne rfl
      change inner ℂ (f (Fin.castLE hmn i)) (f (Fin.castLE hmn j)) = 0
      rw [hf, hf]; dsimp only [v]; rw [inner_smul_left_eq_smul, inner_smul_right_eq_smul, horth i j hij]
      simp
  obtain ⟨u,hu⟩ := ho.exists_orthonormalBasis_extension_of_card_eq (by simp)
  let W : U n := ⟨(EuclideanSpace.basisFun (Fin n) ℂ).toBasis.toMatrix u.toBasis,
    (EuclideanSpace.basisFun (Fin n) ℂ).toMatrix_orthonormalBasis_mem_unitary u⟩
  let D : Rect n m := fun i j => if i = Fin.castLE hmn j then (‖b j‖ : ℂ) else 0
  have hcol (j : Fin m) : (‖b j‖ : ℝ) • u (Fin.castLE hmn j) = b j := by
    by_cases hj : b j = 0
    · simp [hj]
    · rw [hu _ ⟨j,hj,rfl⟩, hf]; dsimp only [v]; rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hj), one_smul]
  have hfac : (W : Rect n n) * D = B := by
    ext i j
    rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.castLE hmn j)]
    · simp only [D, if_pos rfl]
      have hx := congrArg (fun x : EuclideanSpace ℂ (Fin n) => x i) (hcol j)
      change u (Fin.castLE hmn j) i * (‖b j‖ : ℂ) = B i j
      simpa [b, PiLp.smul_apply, Complex.real_smul, mul_comm] using hx
    · intro k _ hkj
      simp [D,hkj]
    · simp
  refine ⟨(W,V), ?_⟩
  have hmid : middle A (W,V) = D := by
    change (star (W : Rect n n)) * A * (V : Rect m m) = D
    rw [Matrix.mul_assoc, ← show B = A*(V:Rect m m) from rfl, ← hfac, ← Matrix.mul_assoc,
      Unitary.coe_star_mul_self, Matrix.one_mul]
  rw [hmid]
  constructor
  · intro i j h
    exact if_neg (fun e => h (congrArg Fin.val e))
  · intro i j
    by_cases h : i = Fin.castLE hmn j <;> simp [D, h]

lemma svd_exists {n m : ℕ} (A : Rect n m) : ∃ q : Pair n m, diagOK (middle A q) := by
  rcases le_total m n with h | h
  · exact svd_exists_tall h A
  · obtain ⟨⟨V,W⟩,hoff,hpos⟩ := svd_exists_tall h Aᴴ
    have hmid : middle A (W,V) = (middle Aᴴ (V,W))ᴴ := by
      simp [middle, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    refine ⟨(W,V), ?_⟩
    rw [hmid]
    constructor
    · intro i j h
      simp [Matrix.conjTranspose_apply, hoff j i (Ne.symm h)]
    · intro i j
      simpa [Matrix.conjTranspose_apply, (hpos j i).1] using (hpos j i).2

end OMA.S_mo_404448

namespace OMA.S_mo_404448
open Matrix
open scoped Matrix.Norms.L2Operator

private theorem compact_unitaries (n : ℕ) :
    CompactSpace (unitary (Matrix (Fin n) (Fin n) ℂ)) := by
  let M := Matrix (Fin n) (Fin n) ℂ
  change CompactSpace (unitary M)
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0:M) ‖(1:M)‖).of_isClosed_subset isClosed_unitary
  intro U hU
  rw [Metric.mem_closedBall,dist_zero_right]
  have h := CStarRing.norm_mem_unitary_mul (1:M) hU
  simpa using h.le

end OMA.S_mo_404448
namespace OMA.S_mo_404448
open Matrix Set
open scoped Matrix.Norms.L2Operator

private lemma continuous_middle (n m : ℕ) :
    Continuous (fun p : Rect n m × Pair n m => middle p.1 p.2) := by
  unfold middle
  fun_prop

private lemma diag_closed (n m : ℕ) : IsClosed {D : Rect n m | diagOK D} := by
  change IsClosed ({D : Rect n m | ∀ i j, i.val ≠ j.val → D i j = 0} ∩
    {D : Rect n m | ∀ i j, (D i j).im = 0 ∧ 0 ≤ (D i j).re})
  simp only [Set.ofPred_forall]
  apply IsClosed.inter
  · apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro j
    apply isClosed_iInter
    intro _
    exact isClosed_eq (by fun_prop) continuous_const
  · apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro j
    have h : Continuous (fun D : Rect n m => D i j) := by fun_prop
    exact (isClosed_eq (Complex.continuous_im.comp h) continuous_const).inter
      (isClosed_le continuous_const (Complex.continuous_re.comp h))

lemma measurable_svd (n m : ℕ) :
    ∃ F : Rect n m → U n × SigmaMat n m × U m, Measurable F ∧
      ∀ A, A = ((F A).1 : Rect n n) * ((F A).2.1 : Rect n m) * ((F A).2.2 : Rect m m)ᴴ := by
  let _ : CompactSpace (U n) := compact_unitaries n
  let _ : CompactSpace (U m) := compact_unitaries m
  let S := {p : Rect n m × Pair n m | diagOK (middle p.1 p.2)}
  have hs : IsClosed S := (diag_closed n m).preimage (continuous_middle n m)
  obtain ⟨g,hg,hok⟩ := select_closed S hs (svd_exists (n:=n) (m:=m))
  let d : Rect n m → SigmaMat n m := fun A => ⟨middle A (g A), hok A⟩
  have hd : Measurable d :=
    ((continuous_middle n m).measurable.comp (measurable_id.prodMk hg)).subtype_mk
  refine ⟨fun A => ((g A).1,d A,(g A).2),hg.fst.prodMk (hd.prodMk hg.snd),?_⟩
  intro A
  change A = ((g A).1 : Rect n n) * (((g A).1 : Rect n n)ᴴ * A * ((g A).2 : Rect m m)) *
    ((g A).2 : Rect m m)ᴴ
  have hleft : ((g A).1 : Rect n n) * ((g A).1 : Rect n n)ᴴ = 1 :=
    Unitary.mul_star_self_of_mem (g A).1.property
  have hright : ((g A).2 : Rect m m) * ((g A).2 : Rect m m)ᴴ = 1 :=
    Unitary.mul_star_self_of_mem (g A).2.property
  rw [←Matrix.mul_assoc,←Matrix.mul_assoc,hleft,Matrix.one_mul,Matrix.mul_assoc,hright,Matrix.mul_one]

end OMA.S_mo_404448

open OMA.S_mo_404448
theorem OMA.solution : type_of% @OMA.S_mo_404448.main := measurable_svd

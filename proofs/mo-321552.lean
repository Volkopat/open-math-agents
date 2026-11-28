import OMAStatements.S_mo_321552

namespace OMA.S_mo_321552
open Matrix Unitary
variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}

lemma word_conjugate {A B X : Mat 𝕜 n} {u v : ℝ} (h : Word A B u v X)
    (V : unitary (Mat 𝕜 n)) :
    let F := conjStarAlgAut 𝕜 _ V
    Word (F A) (F B) u v (F X) := by
  let F := conjStarAlgAut 𝕜 _ V
  change Word (F A) (F B) u v (F X)
  induction h with
  | left => exact .left
  | right => exact .right
  | sandwich _ _ ih jh => simpa only [map_mul] using Word.sandwich ih jh
  | power _ hp ih =>
    apply Word.power ih
    obtain ⟨U,d,hd,hx,hy⟩ := hp
    refine ⟨V*U,d,hd,?_,?_⟩
    · rw [hx]
      exact (conjStarAlgAut_mul_apply (S:=𝕜) V U _).symm
    · rw [hy]
      exact (conjStarAlgAut_mul_apply (S:=𝕜) V U _).symm

lemma compact_conjugate_iff (V : unitary (Mat 𝕜 n)) (A B : Mat 𝕜 n) :
    let F := conjStarAlgAut 𝕜 _ V
    IsCompact (spanSet (F A) (F B)) ↔ IsCompact (spanSet A B) := by
  let F := conjStarAlgAut 𝕜 _ V
  have hp (W : unitary (Mat 𝕜 n)) (C D : Mat 𝕜 n) :
      (conjStarAlgAut 𝕜 _ W) '' spanSet C D =
      spanSet (conjStarAlgAut 𝕜 _ W C) (conjStarAlgAut 𝕜 _ W D) := by
    let g := conjStarAlgAut 𝕜 _ W
    ext Y
    constructor
    · rintro ⟨X,⟨u,v,hu,hv,hs,hw⟩,rfl⟩
      exact ⟨u,v,hu,hv,hs,word_conjugate hw W⟩
    · rintro ⟨u,v,hu,hv,hs,hw⟩
      refine ⟨g.symm Y,⟨u,v,hu,hv,hs,?_⟩,g.apply_symm_apply Y⟩
      have H := word_conjugate hw (star W)
      dsimp only at H
      rw [←conjStarAlgAut_symm] at H
      simpa only [StarAlgEquiv.symm_apply_apply] using H
  have hcont (W : unitary (Mat 𝕜 n)) : Continuous (conjStarAlgAut 𝕜 _ W : Mat 𝕜 n → Mat 𝕜 n) :=
    (continuous_const.mul continuous_id).mul continuous_const
  constructor
  · intro h
    have k := h.image (hcont (star V))
    rw [hp] at k
    rw [←conjStarAlgAut_symm] at k
    simpa only [StarAlgEquiv.symm_apply_apply] using k
  · intro h
    rw [←hp]
    exact h.image (hcont V)

end OMA.S_mo_321552
namespace OMA.S_mo_321552
open Matrix Unitary Module.End
open scoped ComplexOrder
variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}

set_option maxHeartbeats 800000 in
lemma simultaneous_diagonal (A B : Mat 𝕜 n) (ha : A.PosDef) (hb : B.PosDef)
    (hc : Commute A B) :
    ∃ (U : unitary (Mat 𝕜 n)) (a b : Fin n → ℝ),
      (∀ i,0<a i) ∧ (∀ i,0<b i) ∧
      A=(U:Mat 𝕜 n)*diagR 𝕜 a*(U:Mat 𝕜 n)ᴴ ∧ B=(U:Mat 𝕜 n)*diagR 𝕜 b*(U:Mat 𝕜 n)ᴴ := by
  classical
  let E := EuclideanSpace 𝕜 (Fin n)
  let f := A.toEuclideanLin
  let g := B.toEuclideanLin
  have hf := Matrix.isSymmetric_toEuclideanLin_iff.mpr ha.1
  have hg := Matrix.isSymmetric_toEuclideanLin_iff.mpr hb.1
  have hfg : Commute f g := hc.map (Matrix.toLinAlgEquiv (EuclideanSpace.basisFun (Fin n) 𝕜).toBasis)
  let I := Eigenvalues g × Eigenvalues f
  let emb (q : I) : 𝕜 × 𝕜 := (q.1.val,q.2.val)
  have hin : Function.Injective emb := fun _ _ h => Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  let V (q : I) := eigenspace f (emb q).2 ⊓ eigenspace g (emb q).1
  have O := (hf.orthogonalFamily_eigenspace_inf_eigenspace hg).comp hin
  have H : DirectSum.IsInternal V := by
    apply O.isInternal_iff.mpr
    rw [Submodule.orthogonal_eq_bot_iff]
    apply top_unique
    rw [←hf.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute hg hfg]
    refine iSup_le (fun a => iSup_le (fun b => ?_))
    by_cases ha' : HasEigenvalue f a
    · by_cases hb' : HasEigenvalue g b
      · exact le_iSup V (⟨b,hb'⟩,⟨a,ha'⟩)
      · have hb0 : eigenspace g b=⊥ := not_ne_iff.mp hb'
        exact inf_le_right.trans (hb0.le.trans bot_le)
    · have ha0 : eigenspace f a=⊥ := not_ne_iff.mp ha'
      exact inf_le_left.trans (ha0.le.trans bot_le)
  have hn : Module.finrank 𝕜 E=n := by simp [E]
  let e := H.subordinateOrthonormalBasis hn O
  let ind (i : Fin n) := emb (H.subordinateOrthonormalBasisIndex hn i O)
  have he (i : Fin n) : e i ∈ eigenspace f (ind i).2 ⊓ eigenspace g (ind i).1 :=
    H.subordinateOrthonormalBasis_subordinate hn i O
  let U : unitary (Mat 𝕜 n) :=
    ⟨(EuclideanSpace.basisFun (Fin n) 𝕜).toBasis.toMatrix e.toBasis,
      (EuclideanSpace.basisFun (Fin n) 𝕜).toMatrix_orthonormalBasis_mem_unitary e⟩
  have one (M : Mat 𝕜 n) (hm : M.PosDef) (l : Fin n → 𝕜)
      (hl : ∀ i,e i∈eigenspace M.toEuclideanLin (l i)) :
      ∃ d : Fin n → ℝ, (∀ i,0<d i) ∧ M=(U:Mat 𝕜 n)*diagR 𝕜 d*(U:Mat 𝕜 n)ᴴ := by
    have hx (i : Fin n) : ∃ k : Fin n, (hm.1.eigenvalues k : 𝕜)=l i := by
      have hv := hasEigenvalue_of_hasEigenvector
        (show HasEigenvector M.toEuclideanLin (l i) (e i) from ⟨hl i,e.orthonormal.ne_zero i⟩)
      have hmem := hv.mem_spectrum
      rw [Matrix.spectrum_toLpLin,hm.1.spectrum_eq_image_range] at hmem
      rcases hmem with ⟨_,⟨k,rfl⟩,hk⟩
      exact ⟨k,hk⟩
    choose idx hidx using hx
    let d (i : Fin n) := hm.1.eigenvalues (idx i)
    refine ⟨d,fun i => hm.eigenvalues_pos _,?_⟩
    have hMU : M*(U:Mat 𝕜 n)=(U:Mat 𝕜 n)*diagR 𝕜 d := by
      ext i j
      rw [show diagR 𝕜 d=diagonal (fun k => (d k:𝕜)) from rfl,Matrix.mul_diagonal]
      have hev := congrArg (fun w : E => w i) (mem_eigenspace_iff.mp (hl j))
      change (M *ᵥ (e j)) i = l j*(e j i) at hev
      change (M *ᵥ (e j)) i=e j i*(d j:𝕜)
      rw [hev,hidx,mul_comm]
    rw [←hMU,Matrix.mul_assoc,show (U:Mat 𝕜 n)*(U:Mat 𝕜 n)ᴴ=1 from Unitary.mul_star_self_of_mem U.property,mul_one]
  obtain ⟨a,hap,hA⟩ := one A ha _ (fun i => (he i).1)
  obtain ⟨b,hbp,hB⟩ := one B hb _ (fun i => (he i).2)
  exact ⟨U,a,b,hap,hbp,hA,hB⟩

end OMA.S_mo_321552

namespace OMA.S_mo_321552
open Matrix Set
variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}

private lemma diag_power_iff {a : Fin n → ℝ} (ha : ∀ i,0<a i) {t : ℝ} {Y : Mat 𝕜 n} :
    powerRel (diagR 𝕜 a) t Y ↔ Y=diagR 𝕜 (fun i => (a i)^t) := by
  constructor
  · rintro ⟨U,d,_,hA,hY⟩
    have hUU : (U:Mat 𝕜 n)ᴴ*(U:Mat 𝕜 n)=1 := U.2.1
    have hUU' : (U:Mat 𝕜 n)*(U:Mat 𝕜 n)ᴴ=1 := U.2.2
    have he : diagR 𝕜 a*(U:Mat 𝕜 n)=(U:Mat 𝕜 n)*diagR 𝕜 d := by
      rw [hA,Matrix.mul_assoc,hUU,mul_one]
    have he' : diagR 𝕜 (fun i => (a i)^t)*(U:Mat 𝕜 n)=
        (U:Mat 𝕜 n)*diagR 𝕜 (fun i => (d i)^t) := by
      ext i j
      have h := congrFun (congrFun he i) j
      simp only [diagR, Matrix.mul_diagonal, Matrix.diagonal_mul] at h ⊢
      by_cases hij : (U:Mat 𝕜 n) i j=0
      · simp [hij]
      · have haij : (a i:𝕜)=(d j:𝕜) :=
          mul_right_cancel₀ hij (h.trans (mul_comm _ _))
        have hij' : a i=d j := RCLike.ofReal_injective haij
        rw [hij',mul_comm]
    rw [hY,← he',Matrix.mul_assoc,hUU',mul_one]
  · rintro rfl
    exact ⟨1,a,ha,by simp,by simp⟩

private lemma word_diag {a b : Fin n → ℝ} (ha : ∀ i,0<a i) (hb : ∀ i,0<b i)
    {u v : ℝ} {X : Mat 𝕜 n} (h : Word (diagR 𝕜 a) (diagR 𝕜 b) u v X) :
    X=diagR 𝕜 (fun i => (a i)^u*(b i)^v) := by
  induction h with
  | left => simp
  | right => simp
  | @sandwich u v p q X Y _ _ hX hY =>
    rw [hX,hY]
    unfold diagR
    rw [diagonal_mul_diagonal,diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Real.rpow_add (ha i),Real.rpow_add (hb i)]
    rw [show 2*u=u+u by ring,show 2*v=v+v by ring, Real.rpow_add (ha i),Real.rpow_add (hb i)]
    push_cast
    ring
  | @power u v X t Y _ hpow ih =>
    rw [ih] at hpow
    rw [(diag_power_iff (fun i => mul_pos (Real.rpow_pos_of_pos (ha i) _) (Real.rpow_pos_of_pos (hb i) _))).mp hpow]
    congr 1
    funext i
    rw [Real.mul_rpow (Real.rpow_nonneg (ha i).le _) (Real.rpow_nonneg (hb i).le _),
      ← Real.rpow_mul (ha i).le, ← Real.rpow_mul (hb i).le,mul_comm t u,mul_comm t v]

lemma commuting_span {a b : Fin n → ℝ} (ha : ∀ i,0<a i) (hb : ∀ i,0<b i) :
    spanSet (diagR 𝕜 a) (diagR 𝕜 b) =
      (fun t : ℝ => diagR 𝕜 (fun i => (a i)^t*(b i)^(1-t))) '' Set.Icc 0 1 := by
  ext X
  constructor
  · rintro ⟨u,v,hu,hv,huv,hw⟩
    exact ⟨u,⟨hu,by linarith⟩,by dsimp only;rw [show 1-u=v by linarith];exact (word_diag ha hb hw).symm⟩
  · rintro ⟨t,ht,rfl⟩
    let A := diagR 𝕜 a
    let B := diagR 𝕜 b
    let C := diagR 𝕜 (fun i => (a i)^(t/2))
    let D := diagR 𝕜 (fun i => (b i)^(1-t))
    have hc : Word A B ((t/2)*1) ((t/2)*0) C :=
      Word.power Word.left ((diag_power_iff ha).2 rfl)
    have hd : Word A B ((1-t)*0) ((1-t)*1) D :=
      Word.power Word.right ((diag_power_iff hb).2 rfl)
    have hw := Word.sandwich hc hd
    ring_nf at hw
    have he := word_diag ha hb hw
    refine ⟨t,1-t,ht.1,sub_nonneg.mpr ht.2,by ring,?_⟩
    change Word A B t (1-t) (diagR 𝕜 (fun i => (a i)^t*(b i)^(1-t)))
    rw [← he]
    exact hw

lemma commuting_compact {a b : Fin n → ℝ} (ha : ∀ i,0<a i) (hb : ∀ i,0<b i) :
    IsCompact (spanSet (diagR 𝕜 a) (diagR 𝕜 b)) := by
  rw [commuting_span ha hb]
  apply isCompact_Icc.image
  change Continuous (fun t : ℝ => diagonal (fun i : Fin n => ((a i^t*b i^(1-t):ℝ) : 𝕜)))
  apply continuous_matrix
  intro i j
  by_cases h : i=j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
    fun_prop (disch := positivity [ha i,hb i])
  · simp only [Matrix.diagonal_apply_ne _ h,continuous_const]
end OMA.S_mo_321552

namespace OMA.S_mo_321552
open Matrix Unitary
open scoped ComplexOrder
variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
private lemma root_word (B : Mat 𝕜 n) (hB : B.PosDef) (q : ℕ) (hq : 0<q) :
    ∃ H : Mat 𝕜 n, powerRel B (q:ℝ)⁻¹ H ∧ H.IsHermitian ∧ H^q=B := by
  let d := hB.1.eigenvalues
  let U := hB.1.eigenvectorUnitary
  let f := conjStarAlgAut 𝕜 _ U
  let e (i : Fin n) : ℝ := d i ^ (q:ℝ)⁻¹
  have hd (i) : 0<d i := hB.eigenvalues_pos i
  have hb : B=f (diagR 𝕜 d) := hB.1.spectral_theorem
  refine ⟨f (diagR 𝕜 e),⟨U,d,hd,hb,rfl⟩,?_,?_⟩
  · change ((U:Mat 𝕜 n)*diagR 𝕜 e*(U:Mat 𝕜 n)ᴴ).IsHermitian
    apply isHermitian_mul_mul_conjTranspose
    exact isHermitian_diagonal_of_self_adjoint _ (funext fun i => by simp)
  · rw [← map_pow, hb]
    apply congrArg f
    rw [diagR, Matrix.diagonal_pow]
    apply congrArg diagonal
    funext i
    simp only [Pi.pow_apply,← RCLike.ofReal_pow]
    congr 1
    change (d i ^ (q:ℝ)⁻¹)^q=d i
    rw [← Real.rpow_natCast,← Real.rpow_mul (hd i).le,inv_mul_cancel₀ (by exact_mod_cast hq.ne'),Real.rpow_one]
private lemma unequal_entry (a : Fin n → ℝ) (H : Mat 𝕜 n) (hh : H.IsHermitian)
    (hn : ¬Commute (diagR 𝕜 a) H) : ∃ i j, a j<a i ∧ H i j≠0 := by
  by_contra! h
  apply hn
  ext i j
  simp only [diagR,diagonal_mul,mul_diagonal]
  rcases lt_trichotomy (a i) (a j) with hl|he|hr
  · have hz : H i j=0 := by rw [←hh.apply i j,h j i hl,star_zero]
    rw [hz,mul_zero,zero_mul]
  · rw [he,mul_comm]
  · rw [h i j hr,mul_zero,zero_mul]
end OMA.S_mo_321552

namespace OMA.S_mo_321552
open Matrix Finset
open scoped ComplexOrder
variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
private lemma escape_family (a : Fin n → ℝ) (ha : ∀ i,0<a i) (B H : Mat 𝕜 n)
    (u v : ℝ) (hroot : powerRel B (v/2) H) (hH : H.IsHermitian)
    (i j : Fin n) (hij : a j<a i) (hne : H i j≠0) :
    ∀ b : ℝ, ∃ X : Mat 𝕜 n, Word (diagR 𝕜 a) B u v X ∧ b<RCLike.re (X i i) := by
  let D (s : ℝ) := diagR 𝕜 fun l => (a l)^s
  have hD (s : ℝ) : Word (diagR 𝕜 a) B s 0 (D s) := by
    have hp : powerRel (diagR 𝕜 a) s (D s) :=
      ⟨1,a,ha,by simp,by simp [D]⟩
    simpa using Word.power (Word.left (A:=diagR 𝕜 a) (B:=B)) hp
  have hh : Word (diagR 𝕜 a) B 0 (v/2) H := by simpa using Word.power Word.right hroot
  let W (t : ℝ) := D t*(H*D (u-2*t)*H)*D t
  have hw (t : ℝ) : Word (diagR 𝕜 a) B u v (W t) := by
    have h := Word.sandwich (hD t) (Word.sandwich hh (hD (u-2*t)))
    convert h using 1 <;> ring
  have he (t : ℝ) : RCLike.re (W t i i) =
      ∑ l,(a i^t)^2*(a l^(u-2*t))*‖H i l‖^2 := by
    have hc : W t i i = ((∑ l,(a i^t)^2*(a l^(u-2*t))*‖H i l‖^2:ℝ):𝕜) := by
      change (D t*(H*D (u-2*t)*H)*D t) i i = _
      simp only [D,diagR,mul_diagonal,diagonal_mul]
      rw [Matrix.mul_apply]
      simp only [mul_diagonal,RCLike.ofReal_sum,Finset.mul_sum,Finset.sum_mul]
      apply sum_congr rfl
      intro l _
      have hs : H l i=star (H i l) := (hH.apply l i).symm
      rw [hs]
      push_cast
      rw [show (‖H i l‖:𝕜)^2=H i l*star (H i l) from (RCLike.mul_conj _).symm]
      ring
    rw [hc,RCLike.ofReal_re]
  have ratio : 1 < a i/a j := (one_lt_div (ha j)).mpr hij
  let c := (a j)^u*‖H i j‖^2
  have hc : 0<c := mul_pos (Real.rpow_pos_of_pos (ha j) u) (sq_pos_of_pos (norm_pos_iff.mpr hne))
  intro b
  obtain ⟨m,hm⟩ := pow_unbounded_of_one_lt (b/c) ratio
  let t : ℝ := (m:ℝ)/2
  refine ⟨W t,hw t,?_⟩
  rw [he]
  apply lt_of_lt_of_le _ (single_le_sum (f:=fun l => (a i^t)^2*(a l^(u-2*t))*‖H i l‖^2)
    (fun l _ => mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (ha l).le _)) (sq_nonneg _)) (mem_univ j))
  have ht : 2*t=(m:ℝ) := by dsimp [t]; ring
  have hi : (a i^t)^2=(a i)^m := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (ha i).le]
    push_cast
    rw [mul_comm,ht,Real.rpow_natCast]
  rw [hi,ht,Real.rpow_sub (ha j),Real.rpow_natCast]
  have h := (div_lt_iff₀ hc).mp hm
  rw [div_pow] at h
  simpa [c,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using h
end OMA.S_mo_321552

namespace OMA.S_mo_321552
open Matrix Set
open scoped ComplexOrder
variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
lemma escaping_chart (a : Fin n → ℝ) (ha : ∀ i,0<a i)
    (B : Mat 𝕜 n) (hB : B.PosDef) (hn : ¬Commute (diagR 𝕜 a) B) (u : ℝ) (q : ℕ) (hq : 0<q) :
    ∀ K : Set (Mat 𝕜 n), IsCompact K →
      ∃ X : Mat 𝕜 n, Word (diagR 𝕜 a) B u (2/(q:ℝ)) X ∧ X∉K := by
  obtain ⟨H,hr,hH,hpow⟩ := root_word B hB q hq
  have hnc : ¬Commute (diagR 𝕜 a) H := fun h => hn (hpow ▸ h.pow_right q)
  obtain ⟨i,j,hij,hne⟩ := unequal_entry a H hH hnc
  have hr' : powerRel B ((2/(q:ℝ))/2) H := by convert hr using 1; ring
  intro K hK
  let F : Mat 𝕜 n → ℝ := fun X => RCLike.re (X i i)
  have hF : Continuous F := by dsimp [F]; fun_prop
  obtain ⟨b,hb⟩ := (hK.image hF).bddAbove
  obtain ⟨X,hX,hval⟩ := escape_family a ha B H u (2/(q:ℝ)) hr' hH i j hij hne b
  exact ⟨X,hX,fun hx => (not_lt_of_ge (hb (mem_image_of_mem F hx))) hval⟩
end OMA.S_mo_321552

namespace OMA.S_mo_321552
open Matrix Unitary Set
open scoped ComplexOrder
variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
lemma escaping_pair (A B : Mat 𝕜 n) (ha : A.PosDef) (hb : B.PosDef) (hn : ¬Commute A B)
    (u : ℝ) (q : ℕ) (hq : 0<q) (S : Set (Mat 𝕜 n)) (hS : IsCompact S) :
    ∃ X, Word A B u (2/(q:ℝ)) X ∧ X∉S := by
  let U := ha.1.eigenvectorUnitary
  let a := ha.1.eigenvalues
  let F := conjStarAlgAut 𝕜 _ U
  let C := F.symm B
  have hA : A=F (diagR 𝕜 a) := ha.1.spectral_theorem
  have hB : B=F C := (F.apply_symm_apply B).symm
  have hc : C.PosDef := by
    change ((U:Mat 𝕜 n)ᴴ*B*(U:Mat 𝕜 n)).PosDef
    exact hb.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit Unitary.isUnit_coe)
  have hn' : ¬Commute (diagR 𝕜 a) C := fun h => hn (hA ▸ hB ▸ h.map F)
  have hcont : Continuous (F.symm : Mat 𝕜 n → Mat 𝕜 n) :=
    (continuous_const.mul continuous_id).mul continuous_const
  obtain ⟨Y,hY,hs⟩ := escaping_chart a (fun i => ha.eigenvalues_pos i) C hc hn' u q hq
    (F.symm '' S) (hS.image hcont)
  refine ⟨F Y,?_,?_⟩
  · rw [hA,hB]
    exact word_conjugate hY U
  · intro h
    exact hs ⟨F Y,h,F.symm_apply_apply Y⟩
lemma compact_iff_pair (A B : Mat 𝕜 n) (ha : A.PosDef) (hb : B.PosDef) :
    IsCompact (spanSet A B) ↔ Commute A B := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨X,hw,hout⟩ := escaping_pair A B ha hb hn (1/2) 4 (by decide) _ h
    apply hout
    exact ⟨1/2,2/(4:ℝ),by norm_num,by norm_num,by norm_num,hw⟩
  · intro h
    obtain ⟨U,a,b,h₁,h₂,hA,hB⟩ := simultaneous_diagonal A B ha hb h
    rw [hA,hB]
    exact (compact_conjugate_iff U (diagR 𝕜 a) (diagR 𝕜 b)).2 (commuting_compact h₁ h₂)
end OMA.S_mo_321552

namespace OMA.S_mo_321552
open Matrix Set
private def evalFive {𝕜 : Type} [RCLike 𝕜] (M : Mat 𝕜 5) : ℝ :=
  9*RCLike.re (M 0 0)-30*RCLike.re (M 1 1)+37*RCLike.re (M 2 2)
    -20*RCLike.re (M 3 3)+4*RCLike.re (M 4 4)

private lemma evalFive_linear (𝕜 : Type) [RCLike 𝕜] :
    IsLinearMap ℝ (evalFive (𝕜:=𝕜)) := by
  constructor
  · intro A B
    simp only [evalFive,Matrix.add_apply,map_add]
    ring
  · intro c A
    simp only [evalFive,Matrix.smul_apply,RCLike.smul_re,smul_eq_mul]
    ring

private lemma evalFive_diag (𝕜 : Type) [RCLike 𝕜] (d : Fin 5 → ℝ) :
    evalFive (diagR 𝕜 d) = 9*d 0-30*d 1+37*d 2-20*d 3+4*d 4 := by
  simp [evalFive,diagR]

private lemma evalFive_sqrt :
    9-30*Real.sqrt (3/2)+37*Real.sqrt (5/2)-20*Real.sqrt (9/2)+4*Real.sqrt (17/2)<0 := by
  have h₁ : 122474/100000 ≤ Real.sqrt (3/2) := by
    apply Real.le_sqrt_of_sq_le; norm_num
  have h₂ : Real.sqrt (5/2) ≤ 158114/100000 := by
    apply Real.sqrt_le_iff.mpr; norm_num
  have h₃ : 212132/100000 ≤ Real.sqrt (9/2) := by
    apply Real.le_sqrt_of_sq_le; norm_num
  have h₄ : Real.sqrt (17/2) ≤ 291548/100000 := by
    apply Real.sqrt_le_iff.mpr; norm_num
  linarith

lemma augmented_midpoint (𝕜 : Type) [RCLike 𝕜] :
    let A := diagR 𝕜 (fun _ : Fin 5 => 1)
    let B := diagR 𝕜 (fun i : Fin 5 => (2:ℝ)^i.val)
    let Y := diagR 𝕜 (fun i : Fin 5 => Real.sqrt ((1+(2:ℝ)^i.val)/2))
    powerRel ((1/2:ℝ) • (A+B)) (1/2) Y ∧ Y ∉ convexHull ℝ (spanSet A B) := by
  dsimp only
  let d (i : Fin 5) := (1+(2:ℝ)^i.val)/2
  have hd (i : Fin 5) : 0<d i := by dsimp [d]; positivity
  constructor
  · refine ⟨1,d,hd,?_,?_⟩
    · simp only [OneMemClass.coe_one,conjTranspose_one,one_mul,mul_one]
      ext i j
      by_cases hij : i=j
      · subst j
        simp [d,diagR,Algebra.smul_def,div_eq_mul_inv,add_mul,mul_comm]
      · simp [diagR,hij]
    · simp [d,Real.sqrt_eq_rpow]
  · have hset : spanSet (diagR 𝕜 (fun _ : Fin 5 => 1))
          (diagR 𝕜 (fun i : Fin 5 => (2:ℝ)^i.val)) ⊆ {X | 0 ≤ evalFive X} := by
      rw [commuting_span (fun _ => zero_lt_one) (fun _ => by positivity)]
      rintro X ⟨t,_,rfl⟩
      change 0 ≤ evalFive _
      rw [evalFive_diag]
      simp only [Real.one_rpow,one_mul,← Real.rpow_pow_comm (by norm_num : (0:ℝ)≤2)]
      let x : ℝ := (2:ℝ)^(1-t)
      change 0 ≤ 9*x^0-30*x^1+37*x^2-20*x^3+4*x^4
      nlinarith [sq_nonneg (3-5*x+2*x^2)]
    have hsep := convexHull_min hset (convex_halfSpace_ge (evalFive_linear 𝕜) 0)
    intro hm
    have hh := hsep hm
    change 0 ≤ evalFive _ at hh
    rw [evalFive_diag] at hh
    have hbad := evalFive_sqrt
    norm_num [Fin.reduceFinMk] at hh hbad
    exact (not_lt_of_ge hh) hbad
end OMA.S_mo_321552

open OMA.S_mo_321552
theorem OMA.solution : type_of% @OMA.S_mo_321552.main := by
  refine ⟨fun _ _ _ A B ha hb => ⟨compact_iff_pair A B ha hb,escaping_pair A B ha hb⟩,?_,augmented_midpoint⟩
  intro K _ m a b ha hb
  exact commuting_span ha hb

import OMAStatements.S_mo_299752

namespace OMA.S_mo_299752
open Matrix Finset
open scoped MatrixOrder Matrix.Norms.L2Operator

private lemma cyclic_spec {n : ℕ} (A B : Mat n) : spectrum ℝ (A*B)=spectrum ℝ (B*A) := by
  ext r
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly,Matrix.mem_spectrum_iff_isRoot_charpoly,Matrix.charpoly_mul_comm]

private lemma shifted_nonneg {n : ℕ} (A : Mat n) (ha : A.IsHermitian) (t : ℝ)
    (hb : ∀ z ∈ spectrum ℝ A, t ≤ z) : (A-t • (1:Mat n)).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  apply (StarOrderedRing.nonneg_iff_spectrum_nonneg (R:=ℝ) _ (ha.sub (Matrix.isHermitian_one.smul (IsSelfAdjoint.all t)))).mpr
  intro z hz
  have he : z+t ∈ spectrum ℝ A := by
    rw [spectrum.mem_iff,Algebra.algebraMap_eq_smul_one,add_smul]
    rwa [spectrum.mem_iff,Algebra.algebraMap_eq_smul_one,sub_sub_eq_add_sub] at hz
  linarith [hb _ he]

private lemma min_product {n : ℕ} [Nonempty (Fin n)] (A D : Mat n) (ha : A.IsHermitian) (hd : D.PosDef) :
    ∃ l : ℝ, IsLeast (spectrum ℝ (D⁻¹*A)) l ∧ (A - l • D).PosSemidef := by
  let T := CFC.sqrt D
  have ht : T.PosSemidef := (CFC.sqrt_nonneg D).posSemidef
  have hT : T*T=D := CFC.sqrt_mul_sqrt_self D hd.posSemidef.nonneg
  have hu : IsUnit T := (CFC.isUnit_sqrt_iff D hd.posSemidef.nonneg).mpr hd.isUnit
  have hi := T.isUnit_iff_isUnit_det.mp hu
  let C := T⁻¹*A*T⁻¹
  have hs : C.IsHermitian := by
    have he := isHermitian_mul_mul_conjTranspose T⁻¹ ha
    simpa only [ht.inv.1.eq] using he
  have hspec : spectrum ℝ C = spectrum ℝ (D⁻¹*A) := by
    rw [show C = (T⁻¹*A)*T⁻¹ from rfl,cyclic_spec,← Matrix.mul_assoc,← Matrix.mul_inv_rev T T, hT]
  obtain ⟨l,hl⟩ : ∃ l, IsLeast (spectrum ℝ C) l := by
    rw [hs.spectrum_real_eq_range_eigenvalues]
    let s := univ.image hs.eigenvalues
    have he : (s : Set ℝ) = Set.range hs.eigenvalues := by simp [s]
    have hs' : s.Nonempty := univ_nonempty.image _
    exact ⟨s.min' hs',he ▸ Finset.isLeast_min' _ _⟩
  have hc := shifted_nonneg C hs l hl.2
  have hcon := hc.mul_mul_conjTranspose_same T
  rw [ht.1.eq,mul_sub,sub_mul, Matrix.mul_smul,Matrix.mul_one, Matrix.smul_mul,hT] at hcon
  have hc' : T*C*T=A := by
    change T*(T⁻¹*A*T⁻¹)*T=A
    rw [←Matrix.mul_assoc,←Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hi,one_mul,
      Matrix.mul_assoc,Matrix.nonsing_inv_mul _ hi,mul_one]
  rw [hc'] at hcon
  exact ⟨l,hspec ▸ hl,hcon⟩

private lemma spectral_vec {n : ℕ} {A : Mat n} {z : ℝ} (hz : z∈spectrum ℝ A) :
    ∃ v : (Fin n → ℝ), v≠0 ∧ A *ᵥ v=z • v := by
  rw [←Matrix.spectrum_toLin'] at hz
  obtain ⟨v,hv⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hz).exists_hasEigenvector
  exact ⟨v,hv.2,Module.End.mem_eigenspace_iff.mp hv.1⟩

private lemma spectral_of_vec {n : ℕ} (A : Mat n) (v : (Fin n → ℝ)) (hv : v≠0) (z : ℝ) (hz : A*ᵥv=z•v) :
    z∈spectrum ℝ A := by
  rw [←Matrix.spectrum_toLin',←Module.End.hasEigenvalue_iff_mem_spectrum]
  exact Module.End.hasEigenvalue_of_hasEigenvector (show Module.End.HasEigenvector A.toLin' z v from
    ⟨Module.End.mem_eigenspace_iff.mpr hz,hv⟩)

end OMA.S_mo_299752

namespace OMA.S_mo_299752
open Matrix Finset

private lemma extreme_bounds {n : ℕ} [Nonempty (Fin n)] (M : Mat n) (hm : M.IsHermitian) :
    IsLeast (spectrum ℝ M) (low M) ∧ IsGreatest (spectrum ℝ M) (high M) := by
  let s := univ.image hm.eigenvalues
  have he : (s : Set ℝ)=spectrum ℝ M := by simp [s,hm.spectrum_real_eq_range_eigenvalues]
  have hne : s.Nonempty := univ_nonempty.image _
  have hl : IsLeast (spectrum ℝ M) (s.min' hne) := he ▸ Finset.isLeast_min' s hne
  have hu : IsGreatest (spectrum ℝ M) (s.max' hne) := he ▸ Finset.isGreatest_max' s hne
  simpa only [low,high,hl.csInf_eq,hu.csSup_eq] using And.intro hl hu

private lemma extremes_pos {n : ℕ} [Nonempty (Fin n)] {M : Mat n} (hm : M.PosDef) :
    0 < low M ∧ 0 < high M := by
  have h (z : ℝ) (hz : z ∈ spectrum ℝ M) : 0 < z := by
    rw [hm.1.spectrum_real_eq_range_eigenvalues] at hz
    obtain ⟨i,rfl⟩ := hz
    exact hm.eigenvalues_pos _
  obtain ⟨hl,hu⟩ := extreme_bounds M hm.1
  exact ⟨h _ hl.1,h _ hu.1⟩

private lemma floor_psd {n : ℕ} [Nonempty (Fin n)] {M : Mat n} (hm : M.IsHermitian) :
    (M - low M • (1:Mat n)).PosSemidef :=
  shifted_nonneg M hm _ (extreme_bounds M hm).1.2

private lemma ceil_psd {n : ℕ} [Nonempty (Fin n)] {M : Mat n} (hm : M.IsHermitian) :
    (high M • (1:Mat n) - M).PosSemidef := by
  have h : ∀ z ∈ spectrum ℝ (-M), -high M ≤ z := by
    intro z hz
    obtain ⟨v,hv,he⟩ := spectral_vec hz
    rw [neg_mulVec] at he
    have he' : M*ᵥv=(-z) • v := by rw [neg_smul,←he,neg_neg]
    linarith [(extreme_bounds M hm).2.2 (spectral_of_vec _ _ hv _ he')]
  simpa only [neg_smul,sub_neg_eq_add,sub_eq_add_neg,neg_neg,add_comm] using shifted_nonneg (-M) hm.neg _ h

private lemma lower_of_psd {n : ℕ} [Nonempty (Fin n)] {M : Mat n} (hm : M.IsHermitian)
    {t : ℝ} (h : (M-t • (1:Mat n)).PosSemidef) : t ≤ low M := by
  obtain ⟨v,hv,ev⟩ := spectral_vec (extreme_bounds M hm).1.1
  have hh := h.dotProduct_mulVec_nonneg v
  have hn : 0 < v ⬝ᵥ v := by simpa using (Matrix.PosDef.one (n:=Fin n) (R:=ℝ)).dotProduct_mulVec_pos hv
  simp only [star_trivial,sub_mulVec,ev,smul_mulVec,one_mulVec,dotProduct_sub,dotProduct_smul,smul_eq_mul] at hh
  exact (mul_le_mul_iff_of_pos_right hn).mp (sub_nonneg.mp hh)

private lemma upper_of_psd {n : ℕ} [Nonempty (Fin n)] {M : Mat n} (hm : M.IsHermitian)
    {t : ℝ} (h : (t • (1:Mat n)-M).PosSemidef) : high M ≤ t := by
  obtain ⟨v,hv,ev⟩ := spectral_vec (extreme_bounds M hm).2.1
  have hh := h.dotProduct_mulVec_nonneg v
  have hn : 0 < v ⬝ᵥ v := by simpa using (Matrix.PosDef.one (n:=Fin n) (R:=ℝ)).dotProduct_mulVec_pos hv
  simp only [star_trivial,sub_mulVec,ev,smul_mulVec,one_mulVec,dotProduct_sub,dotProduct_smul,smul_eq_mul] at hh
  exact (mul_le_mul_iff_of_pos_right hn).mp (sub_nonneg.mp hh)

private lemma low_one {n : ℕ} [Nonempty (Fin n)] : low (1:Mat n)=1 := by
  rw [low,spectrum.one_eq,csInf_singleton]
end OMA.S_mo_299752

namespace OMA.S_mo_299752
open Matrix
private lemma lyap_sub {n : ℕ} (A H S : Mat n) :
    lyap A (H-S)=lyap A H-lyap A S := by
  simp only [lyap,mul_sub,sub_mul]
  abel
private lemma lyap_smul {n : ℕ} (A H : Mat n) (q : ℝ) :
    lyap A (q • H)=q • lyap A H := by simp only [lyap,Matrix.mul_smul,Matrix.smul_mul,smul_add,smul_neg]
private lemma lyap_add {n : ℕ} (A H S : Mat n) :
    lyap A (H+S)=lyap A H+lyap A S := by
  simp only [lyap,mul_add,add_mul]
  abel

private lemma lyap_form {n : ℕ} (A H : Mat n) (hh : H.IsHermitian) (v : Fin n → ℝ) :
    v ⬝ᵥ (lyap A H *ᵥ v) = -2 *((Aᵀ *ᵥ v) ⬝ᵥ (H *ᵥ v)) := by
  have h1 : v ⬝ᵥ (A*ᵥ(H*ᵥv))=(Aᵀ*ᵥv)⬝ᵥ(H*ᵥv) := by
    rw [dotProduct_comm (Aᵀ*ᵥv) _,dotProduct_transpose_mulVec]
  have h2 : v ⬝ᵥ (H*ᵥ(Aᵀ*ᵥv))=(Aᵀ*ᵥv)⬝ᵥ(H*ᵥv) := by
    rw [←dotProduct_transpose_mulVec,show Hᵀ=H from hh,dotProduct_comm]
  rw [lyap,neg_mulVec,add_mulVec,←mulVec_mulVec,←mulVec_mulVec,dotProduct_neg,dotProduct_add,h1,h2]
  ring

private lemma solution_psd {n : ℕ} [Nonempty (Fin n)] (A S H : Mat n) (hs : S.PosDef)
    (hI : lyap A S=1) (hh : H.IsHermitian) (hL : (lyap A H).PosSemidef) : H.PosSemidef := by
  obtain ⟨t,ht,he⟩ := min_product H S hh hs
  obtain ⟨v,hv,ev⟩ := spectral_vec ht.1
  have heig := congrArg (fun w => S *ᵥ w) ev
  simp only [mulVec_mulVec,←Matrix.mul_assoc,mul_nonsing_inv _ (S.isUnit_iff_isUnit_det.mp hs.isUnit),one_mul,mulVec_smul] at heig
  have hop : v ⬝ᵥ(lyap A H *ᵥ v) = t * (v ⬝ᵥ (lyap A S *ᵥ v)) := by
    rw [lyap_form _ _ hh,lyap_form _ _ hs.1,heig,dotProduct_smul,smul_eq_mul]
    ring
  have hp := hL.dotProduct_mulVec_nonneg v
  simp only [star_trivial,hop,hI,one_mulVec] at hp
  have hn : 0 < v ⬝ᵥ v := by simpa using (Matrix.PosDef.one (n:=Fin n) (R:=ℝ)).dotProduct_mulVec_pos hv
  have ht0 : 0 ≤ t := nonneg_of_mul_nonneg_left hp hn
  simpa using he.add (hs.posSemidef.smul ht0)

private lemma compare_solution {n : ℕ} [Nonempty (Fin n)] (A S P Q : Mat n)
    (hs : S.PosDef) (hi : lyap A S=1) (hp : P.PosDef) (hq : Q.PosDef) (he : lyap A P=Q) :
    (P-low Q • S).PosSemidef := by
  apply solution_psd A S _ hs hi (hp.1.sub (hs.1.smul (IsSelfAdjoint.all _)))
  rw [lyap_sub,lyap_smul,he,hi]
  exact floor_psd hq.1
end OMA.S_mo_299752

namespace OMA.S_mo_299752
open Matrix

private lemma scale_upper {n : ℕ} [Nonempty (Fin n)] {S : Mat n} (hs : S.IsHermitian) {p q : ℝ}
    (h : (p • (1:Mat n)-q • S).PosSemidef) : q*high S ≤ p := by
  obtain ⟨v,hv,he⟩ := spectral_vec (extreme_bounds S hs).2.1
  have hn : 0 < v ⬝ᵥ v := by simpa using (Matrix.PosDef.one (n:=Fin n) (R:=ℝ)).dotProduct_mulVec_pos hv
  have hh := h.dotProduct_mulVec_nonneg v
  simp only [star_trivial,sub_mulVec,smul_mulVec,one_mulVec,he,dotProduct_sub,dotProduct_smul,smul_eq_mul] at hh
  apply (mul_le_mul_iff_of_pos_right hn).mp
  linarith only [hh]

private lemma ratio_bound {n : ℕ} [Nonempty (Fin n)] (A S : Mat n) (hs : S.PosDef) (hi : lyap A S=1)
    (P Q : Mat n) (hp : P.PosDef) (hq : Q.PosDef) (he : lyap A P=Q) :
    low Q/high P ≤ (high S)⁻¹ := by
  have hcomp := compare_solution A S P Q hs hi hp hq he
  have hh := (ceil_psd hp.1).add hcomp
  have hh' : (high P • (1:Mat n)-low Q • S).PosSemidef := by
    convert hh using 1
    abel
  have h := scale_upper hs.1 hh'
  rw [←one_div,div_le_div_iff₀ (extremes_pos hp).2 (extremes_pos hs).2,one_mul]
  exact h

private lemma solve (n : ℕ) (A S : Mat (n+1)) (hs : S.PosDef) (hi : lyap A S=1) :
    IsGreatest (ratios A) (high S)⁻¹ ∧ optimal A (high S)⁻¹ = parameters A S := by
  have htop := (extremes_pos hs).2
  constructor
  · refine ⟨⟨S,1,hs,Matrix.PosDef.one,hi,by rw [low_one,one_div]⟩,?_⟩
    rintro _ ⟨P,Q,hp,hq,he,rfl⟩
    exact ratio_bound A S hs hi P Q hp hq he
  ext ⟨P,Q⟩
  constructor
  · rintro ⟨hp,hq,he,hopt⟩
    let q := low Q
    let H := q⁻¹ • P-S
    have hq' : 0 < q := (extremes_pos hq).1
    have hqp : 0 < high P := (extremes_pos hp).2
    have hm : q*high S=high P := by
      change q/high P=(high S)⁻¹ at hopt
      rwa [←one_div,div_eq_div_iff hqp.ne' htop.ne',one_mul] at hopt
    have hlow := (compare_solution A S P Q hs hi hp hq he).smul (inv_nonneg.mpr hq'.le)
    have hH : H.PosSemidef := by
      simpa only [H,smul_sub,smul_smul,inv_mul_cancel₀ hq'.ne',one_smul,q] using hlow
    have hcap := (ceil_psd hp.1).smul (inv_nonneg.mpr hq'.le)
    have hcap' : (high S • (1:Mat (n+1))-S-H).PosSemidef := by
      rw [smul_sub,smul_smul,←hm,inv_mul_cancel_left₀ hq'.ne'] at hcap
      convert hcap using 1
      dsimp [H]
      abel
    have hLH : lyap A H=q⁻¹ • Q-1 := by rw [show H=q⁻¹ • P-S from rfl,lyap_sub,lyap_smul,he,hi]
    have hL := (floor_psd hq.1).smul (inv_nonneg.mpr hq'.le)
    have hL' : (lyap A H).PosSemidef := by
      rw [hLH]
      simpa only [smul_sub,smul_smul,q,inv_mul_cancel₀ (show low Q ≠ 0 from hq'.ne'),one_smul] using hL
    refine ⟨q,H,hq',hH,hcap',hL',?_,?_⟩
    · change P=q • (S+(q⁻¹ • P-S))
      rw [←add_sub_assoc,add_sub_cancel_left,smul_smul,mul_inv_cancel₀ hq'.ne',one_smul]
    · change Q=q • (1+lyap A H)
      rw [hLH,←add_sub_assoc,add_sub_cancel_left,smul_smul,mul_inv_cancel₀ hq'.ne',one_smul]
  · rintro ⟨q,H,hq,hH,hcap,hL,rfl,rfl⟩
    have hp := (hs.add_posSemidef hH).smul hq
    have hq' := (Matrix.PosDef.one.add_posSemidef hL).smul hq
    have he : lyap A (q • (S+H))=q • (1+lyap A H) := by rw [lyap_smul,lyap_add,hi]
    refine ⟨hp,hq',he,le_antisymm (ratio_bound A S hs hi _ _ hp hq' he) ?_⟩
    have hupper : high (q • (S+H)) ≤ q*high S := by
      apply upper_of_psd hp.1
      have h := hcap.smul hq.le
      rw [smul_sub,smul_sub,smul_smul] at h
      rw [smul_add]
      convert h using 1
      abel
    have hlower : q ≤ low (q • (1+lyap A H)) := by
      apply lower_of_psd hq'.1
      simpa only [smul_add,add_sub_cancel_left] using hL.smul hq.le
    rw [←one_div,div_le_div_iff₀ htop (extremes_pos hp).2,one_mul]
    exact hupper.trans (mul_le_mul_of_nonneg_right hlower htop.le)
end OMA.S_mo_299752

open OMA.S_mo_299752 in
theorem OMA.solution : type_of% @OMA.S_mo_299752.main := solve

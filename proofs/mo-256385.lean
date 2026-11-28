import OMAStatements.S_mo_256385

namespace OMA.S_mo_256385
open Matrix Finset
open scoped MatrixOrder Matrix.Norms.L2Operator
private lemma shifted_nonneg {n : ℕ} (A : Rect n n) (ha : A.IsHermitian) (t : ℝ)
    (hb : ∀ z ∈ spectrum ℝ A, t ≤ z) : (A-t • (1:Rect n n)).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  apply (StarOrderedRing.nonneg_iff_spectrum_nonneg (R:=ℝ) _ (ha.sub (Matrix.isHermitian_one.smul (IsSelfAdjoint.all t)))).mpr
  intro z hz
  have he : z+t ∈ spectrum ℝ A := by
    rw [spectrum.mem_iff,Algebra.algebraMap_eq_smul_one,add_smul]
    rwa [spectrum.mem_iff,Algebra.algebraMap_eq_smul_one,sub_sub_eq_add_sub] at hz
  linarith [hb _ he]

private lemma spectral_vec {n : ℕ} {A : Rect n n} {z : ℝ} (hz : z∈spectrum ℝ A) :
    ∃ v : (Fin n → ℝ), v≠0 ∧ A *ᵥ v=z • v := by
  rw [←Matrix.spectrum_toLin'] at hz
  obtain ⟨v,hv⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hz).exists_hasEigenvector
  exact ⟨v,hv.2,Module.End.mem_eigenspace_iff.mp hv.1⟩

private lemma spectral_of_vec {n : ℕ} (A : Rect n n) (v : (Fin n → ℝ)) (hv : v≠0) (z : ℝ) (hz : A*ᵥv=z•v) :
    z∈spectrum ℝ A := by
  rw [←Matrix.spectrum_toLin',←Module.End.hasEigenvalue_iff_mem_spectrum]
  exact Module.End.hasEigenvalue_of_hasEigenvector (show Module.End.HasEigenvector A.toLin' z v from
    ⟨Module.End.mem_eigenspace_iff.mpr hz,hv⟩)



private lemma extreme_bounds {n : ℕ} [Nonempty (Fin n)] (M : Rect n n) (hm : M.IsHermitian) :
    IsLeast (spectrum ℝ M) (low M) ∧ IsGreatest (spectrum ℝ M) (high M) := by
  let s := univ.image hm.eigenvalues
  have he : (s : Set ℝ)=spectrum ℝ M := by simp [s,hm.spectrum_real_eq_range_eigenvalues]
  have hne : s.Nonempty := univ_nonempty.image _
  have hl : IsLeast (spectrum ℝ M) (s.min' hne) := he ▸ Finset.isLeast_min' s hne
  have hu : IsGreatest (spectrum ℝ M) (s.max' hne) := he ▸ Finset.isGreatest_max' s hne
  simpa only [low,high,hl.csInf_eq,hu.csSup_eq] using And.intro hl hu

private lemma floor_psd {n : ℕ} [Nonempty (Fin n)] {M : Rect n n} (hm : M.IsHermitian) :
    (M - low M • (1:Rect n n)).PosSemidef :=
  shifted_nonneg M hm _ (extreme_bounds M hm).1.2

private lemma ceil_psd {n : ℕ} [Nonempty (Fin n)] {M : Rect n n} (hm : M.IsHermitian) :
    (high M • (1:Rect n n) - M).PosSemidef := by
  have h : ∀ z ∈ spectrum ℝ (-M), -high M ≤ z := by
    intro z hz
    obtain ⟨v,hv,he⟩ := spectral_vec hz
    rw [neg_mulVec] at he
    have he' : M*ᵥv=(-z) • v := by rw [neg_smul,←he,neg_neg]
    linarith [(extreme_bounds M hm).2.2 (spectral_of_vec _ _ hv _ he')]
  simpa only [neg_smul,sub_neg_eq_add,sub_eq_add_neg,neg_neg,add_comm] using shifted_nonneg (-M) hm.neg _ h

end OMA.S_mo_256385

namespace OMA.S_mo_256385
open Matrix Finset Unitary
private theorem gramHerm {m n : ℕ} (A : Rect m n) : (gram A).IsHermitian := by
  simpa [gram] using isHermitian_conjTranspose_mul_self A

private lemma frame_direction {m n k b : ℕ} (A : Rect m n) (p : Fin k → Fin n)
    (hp : Function.Injective p) (r : Fin b → Fin m) (hb : b<k) :
    ∃ (z : Fin k → ℝ) (v : Fin n → ℝ), z ≠ 0 ∧ v ⬝ᵥ v = z ⬝ᵥ z ∧
      (∀ i, (A*ᵥv) (r i) = 0) ∧
      (A*ᵥv) ⬝ᵥ (A*ᵥv) = ∑ i, ordered A (p i)*(z i)^2 := by
  classical
  let H := gram A
  let hs := gramHerm A
  let U := hs.eigenvectorUnitary
  let E := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))
  let q (i : Fin k) : Fin n := E ⟨(p i).val,by simp⟩
  have hq : Function.Injective q := by
    intro u v h
    apply hp
    apply Fin.ext
    exact congrArg (fun x : Fin (Fintype.card (Fin n)) => x.val) (E.injective h)
  have eqv (i : Fin k) : hs.eigenvalues (q i) = ordered A (p i) := by
    simp [q,ordered,E,Matrix.IsHermitian.eigenvalues]
  let J : Rect n k := (U : Rect n n).submatrix id q
  have hUU : (U : Rect n n)ᵀ*(U : Rect n n)=1 := U.2.1
  have hJ : Jᵀ*J=1 := by
    have he : Jᵀ*J = ((U : Rect n n)ᵀ*(U : Rect n n)).submatrix q q := by ext i j; rfl
    rw [he,hUU]
    ext i j
    simp [Matrix.one_apply,hq.eq_iff]
  have hspec : H=(U:Rect n n)*diagonal hs.eigenvalues*star (U : Rect n n) := by
    simpa [U,conjStarAlgAut_apply] using hs.spectral_theorem
  have hHU : H*(U : Rect n n)=(U : Rect n n)*diagonal hs.eigenvalues := by
    rw [hspec,Matrix.mul_assoc,Unitary.coe_star_mul_self,Matrix.mul_one]
  have hHJ : H*J=J*diagonal (fun i => ordered A (p i)) := by
    have he : H*J=(H*(U : Rect n n)).submatrix id q := by ext i j; rfl
    rw [he,hHU]
    ext i j
    simp [J,Matrix.mul_diagonal,eqv]
  let C : Rect b k := (A*J).submatrix r id
  have hker : ¬ Function.Injective C.toLin' := by
    intro h
    have hdim := LinearMap.finrank_le_finrank_of_injective h
    simp at hdim
    omega
  rw [←LinearMap.ker_eq_bot] at hker
  obtain ⟨z,hz,hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  let v := J*ᵥz
  have hnorm : v ⬝ᵥ v = z ⬝ᵥ z := by
    change (J*ᵥz) ⬝ᵥ (J*ᵥz) = _
    rw [← dotProduct_transpose_mulVec, mulVec_mulVec,hJ,one_mulVec]
  refine ⟨z,v,hne,hnorm,?_,?_⟩
  · intro i
    have hC : C*ᵥz=0 := hz
    have h := congrFun hC i
    change ((A*J)*ᵥz) (r i)=0 at h
    simpa only [v,mulVec_mulVec] using h
  · change (A*ᵥ(J*ᵥz)) ⬝ᵥ (A*ᵥ(J*ᵥz)) = _
    rw [←dotProduct_transpose_mulVec,mulVec_mulVec]
    change (J*ᵥz) ⬝ᵥ (H*ᵥ(J*ᵥz)) = _
    rw [mulVec_mulVec,hHJ,←mulVec_mulVec,←dotProduct_transpose_mulVec,mulVec_mulVec,hJ,
      one_mulVec]
    apply sum_congr rfl
    intro i _
    simp only [mulVec_diagonal]
    ring
end OMA.S_mo_256385

namespace OMA.S_mo_256385
open Matrix Finset
private lemma dot_pos {n : ℕ} {v : Fin n → ℝ} (hv : v≠0) : 0 < v ⬝ᵥ v := by
  simpa using (Matrix.PosDef.one (n:=Fin n) (R:=ℝ)).dotProduct_mulVec_pos hv

private lemma rayleigh {n : ℕ} [Nonempty (Fin n)] (M : Rect n n) (hm : M.IsHermitian) (v : Fin n → ℝ) :
    low M*(v ⬝ᵥ v) ≤ v ⬝ᵥ (M*ᵥv) ∧ v ⬝ᵥ (M*ᵥv) ≤ high M*(v ⬝ᵥ v) := by
  have h1 := (floor_psd hm).dotProduct_mulVec_nonneg v
  have h2 := (ceil_psd hm).dotProduct_mulVec_nonneg v
  simp only [star_trivial,sub_mulVec,smul_mulVec,one_mulVec,dotProduct_sub,dotProduct_smul,smul_eq_mul,sub_nonneg] at h1 h2
  exact ⟨h1,h2⟩

private lemma wHerm {m n : ℕ} (A : Rect m n) (d : Fin m → ℝ) : (weighted A d).IsHermitian := by
  simpa [weighted] using isHermitian_conjTranspose_mul_mul A (Matrix.isHermitian_diagonal d)

private lemma wquad {m n : ℕ} (A : Rect m n) (d : Fin m → ℝ) (v : Fin n → ℝ) :
    v ⬝ᵥ (weighted A d *ᵥ v) = ∑ j, d j * ((A*ᵥv) j)^2 := by
  rw [weighted,←mulVec_mulVec,←mulVec_mulVec,dotProduct_transpose_mulVec]
  apply sum_congr rfl
  intro i _
  simp only [mulVec_diagonal]
  ring

private lemma gquad {m n : ℕ} (A : Rect m n) (v : Fin n → ℝ) :
    v ⬝ᵥ (gram A *ᵥ v) = ∑ j, ((A*ᵥv) j)^2 := by
  rw [gram,←mulVec_mulVec,dotProduct_transpose_mulVec]
  simp [dotProduct,pow_two]

private lemma endpoints {m n : ℕ} (A : Rect (m+1) (n+1)) (d : Fin (m+1) → ℝ)
    (hd : Antitone d) (hp : ∀ j, 0 ≤ d j) :
    d (Fin.last m)*low (gram A) ≤ low (weighted A d) ∧ high (weighted A d) ≤ d 0*high (gram A) := by
  let T := weighted A d
  have hh := extreme_bounds T (wHerm A d)
  have hL (z : ℝ) (hz : z ∈ spectrum ℝ T) :
      d (Fin.last m)*low (gram A) ≤ z ∧ z ≤ d 0*high (gram A) := by
    obtain ⟨v,hv,he⟩ := spectral_vec hz
    have hex : z*(v ⬝ᵥ v) = ∑ j, d j * ((A*ᵥv) j)^2 := by
      rw [←wquad]
      change _ = v ⬝ᵥ (T*ᵥv)
      rw [he,dotProduct_smul,smul_eq_mul]
    have hg := rayleigh (gram A) (gramHerm A) v
    rw [gquad] at hg
    constructor
    · apply (mul_le_mul_iff_of_pos_right (dot_pos hv)).mp
      rw [mul_assoc,hex]
      refine (mul_le_mul_of_nonneg_left hg.1 (hp _)).trans ?_
      rw [mul_sum]
      exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hd (Fin.le_last j)) (sq_nonneg _)
    · apply (mul_le_mul_iff_of_pos_right (dot_pos hv)).mp
      rw [hex,mul_assoc]
      refine le_trans ?_ (mul_le_mul_of_nonneg_left hg.2 (hp 0))
      rw [mul_sum]
      exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hd (Fin.zero_le j)) (sq_nonneg _)
  exact ⟨(hL _ hh.1.1).1,(hL _ hh.2.1).2⟩
end OMA.S_mo_256385

namespace OMA.S_mo_256385
open Matrix Finset

private lemma ordered_anti {m n : ℕ} (A : Rect m n) : Antitone (ordered A) := by
  intro i j hij
  apply (gramHerm A).eigenvalues₀_antitone
  exact hij

private lemma uslice {m n : ℕ} (h : n+1 ≤ m+1) (A : Rect (m+1) (n+1)) (d : Fin (m+1) → ℝ)
    (hd : Antitone d) (hp : ∀ j, 0 ≤ d j) (i : Fin (n+1)) :
    low (weighted A d) ≤ d (reverseTop h i)*ordered A i := by
  let b := n-i.val
  let p (j : Fin (b+1)) : Fin (n+1) := ⟨i.val+j.val,by dsimp [b] at *; omega⟩
  let r (j : Fin b) : Fin (m+1) := ⟨j.val,by dsimp [b] at *; omega⟩
  let a := reverseTop h i
  have ha : a.val=b := by simp [a,b,reverseTop]
  have hpi : Function.Injective p := fun j k he => Fin.ext (by
    have he' := congrArg Fin.val he
    change i.val+j.val=i.val+k.val at he'
    omega)
  obtain ⟨z,v,hz,hn,hkill,hen⟩ := frame_direction A p hpi r (Nat.lt_succ_self b)
  have hnorm : 0 < v ⬝ᵥ v := hn ▸ dot_pos hz
  apply (mul_le_mul_iff_of_pos_right hnorm).mp
  have h1 := (rayleigh _ (wHerm A d) v).1
  rw [wquad] at h1
  have h2 : ∑ j, d j*((A*ᵥv) j)^2 ≤ ∑ j, d a*((A*ᵥv) j)^2 := by
    apply sum_le_sum
    intro j _
    by_cases hj : j.val<b
    · have hh : (A*ᵥv) j=0 := hkill ⟨j.val,hj⟩
      simp [hh]
    · apply mul_le_mul_of_nonneg_right (hd _) (sq_nonneg _)
      change a.val ≤ j.val
      omega
  have h3 : ∑ j, ordered A (p j)*(z j)^2 ≤ ordered A i*(z ⬝ᵥ z) := by
    simp only [dotProduct,Finset.mul_sum]
    apply sum_le_sum
    intro j _
    rw [←pow_two]
    apply mul_le_mul_of_nonneg_right (ordered_anti A _) (sq_nonneg _)
    change i.val ≤ i.val+j.val
    omega
  rw [←mul_sum] at h2
  rw [show (∑ j,((A*ᵥv) j)^2) = (A*ᵥv) ⬝ᵥ (A*ᵥv) by simp [dotProduct,pow_two],hen] at h2
  rw [mul_assoc,hn]
  simpa only [hn] using (h1.trans h2).trans (mul_le_mul_of_nonneg_left h3 (hp a))

private lemma lslice {m n : ℕ} (h : n+1 ≤ m+1) (A : Rect (m+1) (n+1)) (d : Fin (m+1) → ℝ)
    (hd : Antitone d) (hp : ∀ j, 0 ≤ d j) (i : Fin (n+1)) :
    d (reverseBottom h i)*ordered A i ≤ high (weighted A d) := by
  let p (j : Fin (i.val+1)) : Fin (n+1) := ⟨j.val,by omega⟩
  let r (j : Fin i.val) : Fin (m+1) := ⟨m-j.val,by omega⟩
  let a := reverseBottom h i
  have ha : a.val=m-i.val := by simp [a,reverseBottom]
  have hpi : Function.Injective p := fun j k he => Fin.ext (congrArg (fun a : Fin (n+1) => a.val) he)
  obtain ⟨z,v,hz,hn,hkill,hen⟩ := frame_direction A p hpi r (Nat.lt_succ_self i.val)
  have hnorm : 0 < v ⬝ᵥ v := hn ▸ dot_pos hz
  apply (mul_le_mul_iff_of_pos_right hnorm).mp
  have h1 := (rayleigh _ (wHerm A d) v).2
  rw [wquad] at h1
  have h2 : ∑ j, d a*((A*ᵥv) j)^2 ≤ ∑ j, d j*((A*ᵥv) j)^2 := by
    apply sum_le_sum
    intro j _
    by_cases hj : j.val≤a.val
    · exact mul_le_mul_of_nonneg_right (hd (show j ≤ a from hj)) (sq_nonneg _)
    · have ht : m - j.val < i.val := by omega
      have he : r ⟨m-j.val,ht⟩=j := Fin.ext (by change m-(m-j.val)=j.val; omega)
      have hh := hkill ⟨m-j.val,ht⟩
      rw [he] at hh
      simp [hh]
  have h3 : ordered A i*(z ⬝ᵥ z) ≤ ∑ j, ordered A (p j)*(z j)^2 := by
    simp only [dotProduct,Finset.mul_sum]
    apply sum_le_sum
    intro j _
    rw [←pow_two]
    apply mul_le_mul_of_nonneg_right (ordered_anti A _) (sq_nonneg _)
    change j.val ≤ i.val
    omega
  rw [←mul_sum] at h2
  rw [show (∑ j,((A*ᵥv) j)^2) = (A*ᵥv) ⬝ᵥ (A*ᵥv) by simp [dotProduct,pow_two],hen] at h2
  rw [mul_assoc,hn]
  exact (mul_le_mul_of_nonneg_left h3 (hp a)).trans (h2.trans (by simpa [hn] using h1))
end OMA.S_mo_256385

namespace OMA.S_mo_256385
open Matrix Finset
private lemma aligned {m n : ℕ} (p : Fin n → Fin m) (hp : Function.Injective p)
    (e : Fin n → ℝ) (he : ∀ i, 0 ≤ e i) (d : Fin m → ℝ) :
    ∃ A : Rect m n, gram A=diagonal e ∧ weighted A d=diagonal (fun i => d (p i)*e i) := by
  classical
  let A : Rect m n := Matrix.of fun i j => if i=p j then Real.sqrt (e j) else 0
  have h (w : Fin m → ℝ) : weighted A w = diagonal (fun j => w (p j)*e j) := by
    ext i j
    simp only [weighted,Matrix.mul_apply,Matrix.transpose_apply,
      Matrix.diagonal_apply,A,Matrix.of_apply,ite_mul,zero_mul,mul_ite,mul_zero,Finset.sum_ite_eq',
      mem_univ,if_true]
    by_cases hij : i=j
    · subst j
      simpa [mul_assoc,mul_comm,mul_left_comm] using congrArg (fun y : ℝ => w (p i)*y) (Real.mul_self_sqrt (he i))
    · simp [hij,Ne.symm hij,hp.eq_iff]
  refine ⟨A,?_,h d⟩
  simpa [weighted,gram,Matrix.diagonal_one] using h (fun _ => 1)

private lemma attainment {m n : ℕ} (h : n+1 ≤ m+1) (e : Fin (n+1) → ℝ) (d : Fin (m+1) → ℝ)
    (he : ∀ i, 0 ≤ e i) : ∃ L H : Rect (m+1) (n+1), gram L = diagonal e ∧ gram H = diagonal e ∧
        low (weighted L d) = sInf (Set.range fun i => d (reverseTop h i)*e i) ∧
        high (weighted H d) = sSup (Set.range fun i => d (reverseBottom h i)*e i) := by
  have ht : Function.Injective (reverseTop h) := by
    intro i j hij
    have hh := congrArg Fin.val hij
    apply Fin.ext
    simp [reverseTop] at hh
    omega
  have hb : Function.Injective (reverseBottom h) := by
    intro i j hij
    have hh := congrArg Fin.val hij
    apply Fin.ext
    simp [reverseBottom] at hh
    omega
  obtain ⟨L,hgL,hwL⟩ := aligned _ ht e he d
  obtain ⟨H,hgH,hwH⟩ := aligned _ hb e he d
  exact ⟨L,H,hgL,hgH,by simp [low,hwL],by simp [high,hwH]⟩
end OMA.S_mo_256385

namespace OMA.S_mo_256385
open Matrix
private lemma example_exact (t : ℝ) (ht : 1 ≤ t) :
    ∃ A : Rect 2 2, A 0 1=1 ∧ gram A=diagonal ![t^2,1] ∧ weighted A ![1,(t^2)⁻¹]=1 := by
  let A : Rect 2 2 := !![0,1;t,0]
  have ht' : t ≠ 0 := by linarith
  refine ⟨A,rfl,?_,?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [gram,A,Matrix.mul_apply,Fin.sum_univ_two,pow_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [weighted,A,Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.diagonal_apply,ht',pow_two]
end OMA.S_mo_256385

namespace OMA.S_mo_256385
open Matrix
lemma solve :
    (∀ {m n : ℕ} (h : n+1 ≤ m+1) (A : Rect (m+1) (n+1)) (d : Fin (m+1) → ℝ),
      Antitone d → (∀ j, 0 ≤ d j) → ∀ i : Fin (n+1),
      d (Fin.last m)*low (gram A) ≤ low (weighted A d) ∧
      low (weighted A d) ≤ d (reverseTop h i)*ordered A i ∧
      d (reverseBottom h i)*ordered A i ≤ high (weighted A d) ∧
      high (weighted A d) ≤ d 0*high (gram A)) ∧
    (∀ {m n : ℕ} (h : n+1 ≤ m+1) (e : Fin (n+1) → ℝ) (d : Fin (m+1) → ℝ),
      (∀ i, 0 ≤ e i) → ∃ L H : Rect (m+1) (n+1), gram L = diagonal e ∧ gram H = diagonal e ∧
        low (weighted L d) = sInf (Set.range fun i => d (reverseTop h i)*e i) ∧
        high (weighted H d) = sSup (Set.range fun i => d (reverseBottom h i)*e i)) ∧
    (∀ t : ℝ, 1 ≤ t → ∃ A : Rect 2 2, A 0 1=1 ∧ gram A=diagonal ![t^2,1] ∧
      weighted A ![1,(t^2)⁻¹]=1) := by
  refine ⟨?_,attainment,example_exact⟩
  intro m n h A d hd hp i
  obtain ⟨hl,hu⟩ := endpoints A d hd hp
  exact ⟨hl,uslice h A d hd hp i,lslice h A d hd hp i,hu⟩
end OMA.S_mo_256385

open OMA.S_mo_256385 in
theorem OMA.solution : type_of% @OMA.S_mo_256385.main := solve

import OMAStatements.S_mo_284895

namespace OMA.S_mo_284895
open Matrix Finset
open scoped ComplexOrder Polynomial
private def moments {R : Type*} [CommRing R] {n : ℕ} (G : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) R := Matrix.of fun i j => (G^(i.val+j.val)).trace
private noncomputable def cert {n : ℕ} (M : Mat n) := (moments (Mᴴ*M)).det

private lemma moment_diag {n : ℕ} {G : Mat n} (u : Fin n → ℂ)
    (h : ∀ k : ℕ,(G^k).trace=∑ i,u i^k) :
    moments G=(vandermonde u)ᵀ*vandermonde u := by
  ext i j
  change (G^(i.val+j.val)).trace=_
  rw [h]
  simp only [Matrix.mul_apply,transpose_apply,vandermonde_apply,pow_add]

private lemma cert_nonzero {n : ℕ} (M : Mat n) : cert M≠0 ↔ simple M := by
  let G := Mᴴ*M
  have hp : G.PosSemidef := posSemidef_conjTranspose_mul_self _
  let u (i : Fin n) : ℂ := (hp.1.eigenvalues i:ℂ)
  have htr (k : ℕ) : (G^k).trace=∑ i,u i^k := by
    nth_rw 1 [hp.1.spectral_theorem]
    rw [←map_pow,Unitary.conjStarAlgAut_apply,Matrix.trace_mul_cycle,Unitary.coe_star_mul_self,one_mul,
      Matrix.diagonal_pow,Matrix.trace_diagonal]
    rfl
  have hv := moment_diag u htr
  change (moments G).det≠0 ↔ Function.Injective (singular M)
  rw [hv,Matrix.det_mul,Matrix.det_transpose,mul_self_ne_zero,det_vandermonde_ne_zero_iff]
  have hi (i : Fin n) : singular M i^2 = hp.1.eigenvalues i := Real.sq_sqrt (hp.eigenvalues_nonneg i)
  constructor
  · intro h i j hij
    apply h
    dsimp [u]
    rw [←hi,←hi,hij]
  · intro h i j hij
    apply h
    exact congrArg Real.sqrt (Complex.ofReal_injective hij)

private lemma direction_regular (n : ℕ) : cert (direction n) ≠ 0 := by
  let u (i : Fin n) : ℂ := (i.val+1:ℂ)^2
  have hgram : (direction n)ᴴ*direction n=diagonal u := by
    simp [direction,u,Matrix.diagonal_mul_diagonal,sq]
  have htr (k : ℕ) : ((diagonal u)^k).trace=∑ i,u i^k := by simp [Matrix.diagonal_pow]
  rw [cert,hgram,moment_diag u htr,Matrix.det_mul,Matrix.det_transpose,mul_self_ne_zero,det_vandermonde_ne_zero_iff]
  intro i j h
  apply Fin.ext
  dsimp [u] at h
  have hh : (i.val+1)^2=(j.val+1)^2 := by exact_mod_cast h
  nlinarith only [hh]

private lemma cert_scaled {n : ℕ} (M : Mat n) {r : ℝ} (hr : r≠0) :
    cert ((r:ℂ) • M)≠0 ↔ cert M≠0 := by
  let q : ℂ := (r:ℂ)^2
  let d := diagonal (fun i : Fin n => q^i.val)
  have hg : ((r:ℂ) • M)ᴴ*((r:ℂ) • M)=q • (Mᴴ*M) := by
    simp only [conjTranspose_smul,Complex.star_def,Complex.conj_ofReal,Matrix.mul_smul,Matrix.smul_mul,smul_smul,q,sq]
  have h : moments (q • (Mᴴ*M))=d*moments (Mᴴ*M)*d := by
    ext i j
    simp only [moments,of_apply,d,Matrix.mul_diagonal,Matrix.diagonal_mul,smul_pow,Matrix.trace_smul,smul_eq_mul]
    rw [pow_add q]
    ring
  have hq : q≠0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hr)
  have hd : d.det≠0 := by
    rw [show d=diagonal _ from rfl,det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun _ _ => pow_ne_zero _ hq)
  rw [cert,cert,hg,h,Matrix.det_mul,Matrix.det_mul]
  exact ⟨fun h => right_ne_zero_of_mul (left_ne_zero_of_mul h),fun h => mul_ne_zero (mul_ne_zero hd h) hd⟩
end OMA.S_mo_284895

namespace OMA.S_mo_284895
open Matrix Polynomial Finset
open scoped ComplexOrder Polynomial Matrix.Norms.L2Operator

private lemma cert_polynomial {n : ℕ} (A B : Mat n) :
    ∃ p : ℂ[X], ∀ t : ℝ,p.eval (t:ℂ)=cert ((t:ℂ) • A+B) := by
  let pencil (U V : Mat n) : Matrix (Fin n) (Fin n) ℂ[X] :=
    Matrix.of fun i j => X * C (U i j) + C (V i j)
  let G := pencil Aᴴ Bᴴ * pencil A B
  refine ⟨(moments G).det,?_⟩
  intro t
  let e := Polynomial.evalRingHom (t:ℂ)
  have he (U V : Mat n) : e.mapMatrix (pencil U V)=(t:ℂ) • U+V := by
    ext i j
    change (X*C (U i j)+C (V i j)).eval (t:ℂ)=(t:ℂ)*U i j+V i j
    simp only [eval_add,eval_mul,eval_X,eval_C]
  have hg : e.mapMatrix G=((t:ℂ) • A+B)ᴴ*((t:ℂ) • A+B) := by
    dsimp only [G]
    rw [map_mul,he,he,conjTranspose_add,conjTranspose_smul]
    simp
  change e (moments G).det=_
  rw [e.map_det]
  apply congrArg Matrix.det
  ext i j
  change e (G^(i.val+j.val)).trace=_
  rw [AddMonoidHom.map_trace]
  change (e.mapMatrix (G^(i.val+j.val))).trace=_
  rw [map_pow,hg]
  rfl

private lemma finite_bad {n : ℕ} (A : Mat n) : {t : ℝ | ¬simple (A+(t:ℂ) • direction n)}.Finite := by
  obtain ⟨p,hp⟩ := cert_polynomial A (direction n)
  have hp0 : p≠0 := by
    intro h
    have e := hp 0
    rw [h] at e
    apply direction_regular n
    simpa using e.symm
  let bad : Set ℝ := {s | p.eval (s:ℂ)=0}
  have hb : bad.Finite := (Polynomial.finite_setOfPred_isRoot hp0).preimage Complex.ofReal_injective.injOn
  apply ((hb.image (fun s : ℝ => s⁻¹)).insert 0).subset
  intro t ht
  rcases eq_or_ne t 0 with rfl | hn
  · exact Set.mem_insert ..
  apply Set.mem_insert_of_mem
  refine ⟨t⁻¹,?_,inv_inv t⟩
  change p.eval _=0
  rw [hp]
  have hx : (t⁻¹:ℝ) • (A+(t:ℂ) • direction n) = ((t⁻¹:ℝ):ℂ) • A+direction n := by
    rw [←Complex.coe_smul,smul_add,smul_smul,←Complex.ofReal_mul,inv_mul_cancel₀ hn,Complex.ofReal_one,one_smul]
  have hh := (cert_scaled (A+(t:ℂ) • direction n) (inv_ne_zero hn)).not.mpr
    ((cert_nonzero _).not.mpr ht)
  rw [←Complex.coe_smul] at hx
  simpa only [hx,not_ne_iff] using hh

private theorem solve (n : ℕ) (A : Mat n) :
    {t : ℝ | ¬ simple (A+(t:ℂ) • direction n)}.Finite ∧
    ∀ ε : ℝ, 0 < ε → ∃ (t : ℝ) (S : Mat n), 0 < t ∧ S=(t:ℂ) • direction n ∧ Sᵀ=S ∧
      ‖S‖ < ε ∧ simple (A+S) := by
  have hf := finite_bad A
  refine ⟨hf,?_⟩
  intro ε hε
  let r := ε/(1+‖direction n‖)
  have hr : 0 < r := div_pos hε (by positivity)
  obtain ⟨t,ht,hn⟩ := (Set.Ioo_infinite hr).exists_notMem_finset hf.toFinset
  have hs : simple (A+(t:ℂ) • direction n) := by simpa using hn
  refine ⟨t,(t:ℂ) • direction n,ht.1,rfl,by simp [direction],?_,hs⟩
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht.1]
  have := (lt_div_iff₀ (by positivity : 0 < 1+‖direction n‖)).mp ht.2
  linarith [ht.1]
end OMA.S_mo_284895

open OMA.S_mo_284895 in
theorem OMA.solution : type_of% @OMA.S_mo_284895.main := solve

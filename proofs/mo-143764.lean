import OMAStatements.S_mo_143764

/-!
Complete proof by @connoranderson, linked from statement PR #24580 and desk DONE #112690.
Pinned source: https://github.com/connoranderson/open-math-agents/blob/c62fb638d00b4affe6f2f5c682a9b0bae73f9c3b/proofs/mo-143764.lean
All mathematical source unchanged; this port adds provenance and current-checker validation.
Source: Binzhou Xia, https://mathoverflow.net/questions/143764 (CC BY-SA 3.0).
Port and validation: @rodolfoquint. No new mathematical discovery is claimed.
-/

open Polynomial
namespace OMA.S_mo_143764
variable {R k : Type*} [CommRing R] [IsDomain R] [Field k] {n : ℕ}

private lemma rem_lift (j : Fin n) (e : ℕ) (hn : 0<n) (he : e=j.val ∨ e=j.val+n) :
    ((X:k[X])^e %ₘ (X^n-1)) = X^j.val := by
  have hm : ((X:k[X])^n-1).Monic := by simpa using monic_X_pow_sub_C (1:k) hn.ne'
  have hd : ((X:k[X])^j.val).degree < (X^n-1 : k[X]).degree := by
    rw [show (X^n-1:k[X]).degree = n by simpa only [C_1] using degree_X_pow_sub_C hn (1:k), degree_X_pow]
    exact_mod_cast j.isLt
  rcases he with rfl|rfl
  · exact (modByMonic_eq_self_iff hm).2 hd
  · exact (div_modByMonic_unique (X^j.val) (X^j.val) hm ⟨by rw [pow_add];ring,hd⟩).2

lemma lift_vandermonde (φ : R →+* k) (a : Fin n → R) (ha : Function.Injective a)
    (hn : 0<n) (hred : (∏ i, (X-C (a i) : R[X])).map φ = X^n-1)
    (e : Fin n → ℕ) (he : ∀ j, e j=j.val ∨ e j=j.val+n) :
    (Matrix.of fun i j : Fin n => a i ^ e j).det ≠ 0 := by
  classical
  let P : R[X] := ∏ i, (X-C (a i))
  let B : Matrix (Fin n) (Fin n) R := .of fun i j => ((X^e j : R[X]) %ₘ P).coeff i.val
  have hP : P.Monic := monic_prod_X_sub_C _ _
  have hd : P.natDegree = n := by simp [P,natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (a i))]
  have hP1 : P ≠ 1 := by intro h;have := hd;rw [h,natDegree_one] at this;omega
  have hroot (i : Fin n) : P.eval (a i) = 0 := by
    simp only [P,eval_prod,eval_sub,eval_C,eval_X]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
  have hfac : Matrix.vandermonde a * B = Matrix.of fun i j : Fin n => a i ^ e j := by
    ext i j
    have hm := natDegree_modByMonic_lt (X^e j : R[X]) hP hP1
    rw [hd] at hm
    have hs := eval_eq_sum_range' hm (a i)
    rw [Finset.sum_range] at hs
    have hcalc : ((X^e j : R[X]) %ₘ P).eval (a i) = (a i)^e j := by
      rw [modByMonic_eq_sub_mul_div,eval_sub,eval_mul,hroot]
      simp
    simpa only [Matrix.mul_apply,Matrix.vandermonde_apply,Matrix.of_apply,B,mul_comm] using
      hs.symm.trans hcalc
  have hB : B.map φ = 1 := by
    ext i j
    change φ (((X^e j : R[X]) %ₘ P).coeff i.val) = _
    rw [←coeff_map,map_modByMonic _ hP,hred]
    simp only [Polynomial.map_pow,Polynomial.map_X,rem_lift j _ hn (he j),coeff_X_pow,Matrix.one_apply]
    simp [Fin.ext_iff]
  have hnB : B.det ≠ 0 := by
    intro hz
    have hh := φ.map_det B
    simp [hB,hz] at hh
  rw [←hfac,Matrix.det_mul]
  exact mul_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr ha) hnB
end OMA.S_mo_143764

open Polynomial
namespace OMA.S_mo_143764
variable {R k : Type*} [CommRing R] [IsDomain R] [Field k] [CharP k 2] {n : ℕ}

lemma reduction_nodes (φ : R →+* k) (z : R) (hz : IsPrimitiveRoot z (2*n)) (hn : 0<n) :
    (∏ i : Fin n, (X-C ((φ z)^i.val) : k[X])) = X^n-1 := by
  have hs : IsPrimitiveRoot (z^2) n := by
    simpa using hz.pow_of_dvd (p := 2) (by decide) (dvd_mul_right 2 n)
  have hP : (X^n-1 : R[X]) = ∏ i : Fin n, (X - C ((z^2)^i.val)) := by
    simpa only [C_1,mul_one,Finset.prod_range] using X_pow_sub_C_eq_prod hs hn (one_pow n : (1:R)^n=1)
  let g : R[X] →+* k[X] := Polynomial.eval₂RingHom (C.comp φ) (X^2)
  have hX : g X = X^2 := by simp [g,coe_eval₂RingHom]
  have hC (a : R) : g (C a) = C (φ a) := by simp [g,coe_eval₂RingHom]
  have h := congrArg g hP
  simp only [map_sub,map_one,map_pow,map_prod,hX,hC] at h
  apply CharTwo.sq_injective
  dsimp only
  rw [←Finset.prod_pow]
  simp only [CharTwo.sub_eq_add,CharTwo.add_sq,one_pow,Polynomial.C_pow] at *
  simpa only [←pow_mul,mul_comm] using h.symm

lemma odd_injective (_hn : 0<n) (hodd : Odd n) (z : k)
    (hred : (∏ i : Fin n, (X-C (z^i.val) : k[X])) = X^n-1) :
    Function.Injective (fun i : Fin n => z^i.val) := by
  classical
  have hs : ((X:k[X])^n-1).Separable := by
    simpa only [C_1] using separable_X_pow_sub_C' 2 n (1:k)
      (by obtain ⟨k,hk⟩ := hodd; omega) one_ne_zero
  have hroot := nodup_roots hs
  rw [←hred] at hroot
  let f (i : Fin n) := z^i.val
  have he : (∏ i : Fin n, (X-C (z^i.val) : k[X])).roots = Finset.univ.val.map f := by
    convert! roots_multiset_prod_X_sub_C (Finset.univ.val.map f) using 2
    simp [f,Finset.prod,Function.comp_def]
  rw [he] at hroot
  have hi := (Multiset.nodup_map_iff_inj_on Finset.univ.nodup).mp hroot
  exact fun i j hij => hi i (Finset.mem_univ i) j (Finset.mem_univ j) hij
end OMA.S_mo_143764

namespace OMA.S_mo_143764
open Polynomial

lemma solver {R k : Type*} [CommRing R] [IsDomain R] [Field k] [CharP k 2]
    (φ : R →+* k) {n : ℕ} (hn : 0<n) (z : R) (hz : IsPrimitiveRoot z (2*n))
    (A B : Fin n → Bool) : (signedMatrix z A B).det ≠ 0 := by
  classical
  have hsign (b : Bool) : φ (sign b) = 1 := by cases b <;> simp [sign,CharTwo.neg_eq]
  have hred := reduction_nodes φ z hz hn
  have hs : IsPrimitiveRoot (z^2) n := by
    simpa using hz.pow_of_dvd (p := 2) (by decide) (dvd_mul_right 2 n)
  by_cases hn2 : Even n
  · let a (i : Fin n) : R := sign (A i)*z^i.val
    have ha2 (i : Fin n) : (a i)^2=(z^2)^i.val := by
      cases hi : A i <;> simp [a,hi,sign,←pow_mul,Nat.mul_comm]
    have hinj : Function.Injective a := by
      intro i j he
      exact Fin.ext (hs.pow_inj i.isLt j.isLt (by rw [←ha2,←ha2,he]))
    have hzn : z^n = -1 := by
      apply IsPrimitiveRoot.eq_neg_one_of_two_right
      simpa only [show 2*n/n=2 by rw [Nat.mul_comm, Nat.mul_div_cancel_left _ hn]] using hz.pow_of_dvd hn.ne' (dvd_mul_left n 2)
    have han (i : Fin n) : (a i)^n=(-1:R)^i.val := by
      have hsg : (sign (A i):R)^n=1 := by
        cases hi : A i <;> simp [sign,hn2.neg_one_pow]
      dsimp only [a]
      rw [mul_pow,hsg,one_mul,←pow_mul,Nat.mul_comm,pow_mul,hzn]
    let e (j : Fin n) : ℕ := if B j then j.val+n else j.val
    have hm : signedMatrix z A B = Matrix.of fun i j : Fin n => a i ^ e j := by
      ext i j
      have hex : a i ^ j.val = (sign (A i) : R)^j.val * z^(i.val*j.val) := by
        simp only [a,mul_pow,pow_mul]
      cases hj : B j
      · simp only [signedMatrix,Matrix.of_apply,e,hj,Bool.false_eq_true,if_false,hex]
        simp [sign]
      · simp only [signedMatrix,Matrix.of_apply,e,hj,if_true,pow_add,han,hex]
        rw [show (sign true:R) = -1 by rfl]
        ring
    rw [hm]
    refine lift_vandermonde φ a hinj hn ?_ e ?_
    · simpa [Polynomial.map_prod,a,hsign] using hred
    · intro j
      cases hj : B j <;> simp [e,hj]
  · have hi := odd_injective hn (Nat.not_even_iff_odd.mp hn2) (φ z) hred
    have hM : (signedMatrix z A B).map φ = Matrix.vandermonde (fun i : Fin n => (φ z)^i.val) := by
      ext i j
      simp [signedMatrix,Matrix.vandermonde_apply,hsign,pow_mul]
    intro h
    have hh := φ.map_det (signedMatrix z A B)
    change φ (signedMatrix z A B).det = ((signedMatrix z A B).map φ).det at hh
    rw [h,map_zero,hM] at hh
    exact (Matrix.det_vandermonde_ne_zero_iff.mpr hi) hh.symm
end OMA.S_mo_143764

namespace OMA.S_mo_143764

lemma complex_solver {n : ℕ} (hn : 0<n) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (2*n))
    (A B : Fin n → Bool) : (signedMatrix ζ A B).det ≠ 0 := by
  classical
  let R := integralClosure ℤ ℂ
  let z : R := ⟨ζ,hζ.isIntegral (by omega)⟩
  let incl : R →+* ℂ := (integralClosure ℤ ℂ).val.toRingHom
  have hz : IsPrimitiveRoot z (2*n) := hζ.of_map_of_injective (f := incl) Subtype.val_injective
  let P : Ideal ℤ := Ideal.span {(2:ℤ)}
  have : P.IsMaximal := ((Ideal.span_singleton_prime (by norm_num : (2:ℤ)≠0)).mpr
    (by norm_num : Prime (2:ℤ))).isMaximal (by simp)
  obtain ⟨Q,hQ,hcom⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := R) P
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective ℤ R)]; exact bot_le)
  let : Field (R ⧸ Q) := Ideal.Quotient.field Q
  let φ := Ideal.Quotient.mk Q
  have htwo : (2:R) ∈ Q := by
    have hx : (2:ℤ) ∈ P := Ideal.subset_span (by simp)
    rw [←hcom,Ideal.mem_comap] at hx
    simpa using hx
  have : CharP (R ⧸ Q) 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (by
    have hh := Ideal.Quotient.eq_zero_iff_mem.mpr htwo
    exact (map_natCast (Ideal.Quotient.mk Q) 2).symm.trans hh)
  have H := solver φ hn z hz A B
  have hM : (signedMatrix z A B).map incl = signedMatrix ζ A B := by
    ext i j
    cases ha : A i <;> cases hb : B j <;> simp [signedMatrix,ha,hb,sign,incl,z]
  intro h
  apply H
  apply Subtype.val_injective
  change incl (signedMatrix z A B).det = 0
  rw [incl.map_det]
  change ((signedMatrix z A B).map incl).det = 0
  rw [hM,h]
end OMA.S_mo_143764

theorem OMA.solution : type_of% @OMA.S_mo_143764.main := by
  intro n hn ζ hζ A B
  exact OMA.S_mo_143764.complex_solver hn ζ hζ A B

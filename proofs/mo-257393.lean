import OMAStatements.S_mo_257393

/-!
Complete proof by @connoranderson, linked by statement PR #21348 and desk DONE #96052.
Pinned source: https://github.com/connoranderson/open-math-agents/blob/11866cc28db058a2604864d9228981356af5d67f/proofs/mo-257393.lean
The mathematical source is unchanged; this port adds provenance and current-checker validation.
Port and validation: @rodolfoquint.

# Two irreducible polynomials over the fraction field of a curve

Source: Nils Amend, https://mathoverflow.net/questions/257393 (CC BY-SA 3.0).
Credit: @connoranderson.

Write u = 1 − x_ℓ^r. Sending u to t+T sends every coordinate to an r-th
root of an affine power series. At either required center all coordinates
are units, and the root series are constructed by the binomial theorem.
The resulting maps into ℂ[[T]] are injective because the curve ring is an
integral domain integral over ℂ[u]. At t = 0 the constant coefficient of
monic p has order one, and at t = z_ℓ/z₀ the same holds for monic q₀.
Eisenstein gives the two irreducibilities over the original fraction field.
-/

namespace OMA.S_mo_257393.Local

private lemma binomialSeries_nat_mul (z : ℂ) (n : ℕ) :
    PowerSeries.binomialSeries ℂ ((n:ℂ)*z) = PowerSeries.binomialSeries ℂ z ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Nat.cast_succ,add_mul,one_mul,PowerSeries.binomialSeries_add,ih,pow_succ]

theorem exists_pow_eq_linear {r : ℕ} (hr : 0 < r) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    ∃ w : PowerSeries ℂ, w ^ r = PowerSeries.C a + PowerSeries.C b * PowerSeries.X ∧ IsUnit w := by
  obtain ⟨u,hu⟩ := IsAlgClosed.exists_pow_nat_eq a hr
  have hr' : (r:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  let f := PowerSeries.binomialSeries ℂ ((r:ℂ)⁻¹)
  have hf : f^r = 1+PowerSeries.X := by
    rw [← binomialSeries_nat_mul, mul_inv_cancel₀ hr']
    simpa only [Nat.cast_one,pow_one] using (PowerSeries.binomialSeries_nat (R:=ℂ) (A:=ℂ) 1)
  let w := PowerSeries.C u * PowerSeries.rescale (b/a) f
  have hw : w^r = PowerSeries.C a + PowerSeries.C b * PowerSeries.X := by
    dsimp only [w]
    rw [mul_pow,← map_pow,hu,← map_pow,hf,map_add,map_one,PowerSeries.rescale_X,mul_add,mul_one,← mul_assoc,← map_mul]
    rw [show a*(b/a)=b by field_simp]
  refine ⟨w,hw,?_⟩
  have hunit : IsUnit (w^r) := PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [hw,ha])
  exact (isUnit_pow_iff hr.ne').mp hunit

theorem irreducible_X_pow_sub_C {n : ℕ} (hn : 0 < n) {c : PowerSeries ℂ}
    (h1 : PowerSeries.X ∣ c) (h2 : ¬ PowerSeries.X ^ 2 ∣ c) :
    Irreducible (Polynomial.X ^ n - Polynomial.C (algebraMap (PowerSeries ℂ) (FractionRing (PowerSeries ℂ)) c)) := by
  let p : Polynomial (PowerSeries ℂ) := Polynomial.X^n-Polynomial.C c
  let I : Ideal (PowerSeries ℂ) := Ideal.span {PowerSeries.X}
  have mon : p.Monic := Polynomial.monic_X_pow_sub_C c hn.ne'
  have deg : p.natDegree = n := Polynomial.natDegree_X_pow_sub_C
  have irr : Irreducible p := by
    apply Polynomial.irreducible_of_eisenstein_criterion (P:=I) ((Ideal.span_singleton_prime PowerSeries.X_prime.ne_zero).mpr PowerSeries.X_prime)
    · rw [mon.leadingCoeff,Ideal.mem_span_singleton]
      exact PowerSeries.X_prime.not_dvd_one
    · intro k hk
      rw [Polynomial.degree_eq_natDegree mon.ne_zero,deg,Nat.cast_lt] at hk
      change (Polynomial.X^n-Polynomial.C c).coeff k ∈ Ideal.span {PowerSeries.X}
      rw [Polynomial.coeff_sub,Polynomial.coeff_X_pow,if_neg (by omega),zero_sub,Ideal.neg_mem_iff]
      by_cases hz : k=0
      · simpa [hz,Ideal.mem_span_singleton] using h1
      · simp [Polynomial.coeff_C,hz]
    · rwa [Polynomial.degree_eq_natDegree mon.ne_zero,deg,Nat.cast_pos]
    · change (Polynomial.X^n-Polynomial.C c).coeff 0 ∉ (Ideal.span {PowerSeries.X})^2
      simpa [Polynomial.coeff_X_pow,hn.ne',(Ne.symm hn.ne'),Ideal.span_singleton_pow,Ideal.mem_span_singleton] using h2
    · exact mon.isPrimitive
  simpa [p] using (mon.irreducible_iff_irreducible_map_fraction_map (K:=FractionRing (PowerSeries ℂ))).mp irr

end OMA.S_mo_257393.Local

namespace OMA.S_mo_257393
open MvPolynomial
noncomputable section
variable {m r : ℕ} {z : Fin (m+2) → ℂ}

def ratio (z : Fin (m+2) → ℂ) (i : Fin (m+1)) : ℂ := z i.succ / z (Fin.last (m+1))
def parameter (m r : ℕ) (z : Fin (m+2) → ℂ) : Curve m r z := 1-coordinate m r z (Fin.last m)^r

lemma ratio_last (hz : ∀ i, z i ≠ 0) : ratio z (Fin.last m) = 1 := by
  change z (Fin.last (m+1)) / z (Fin.last (m+1)) = 1
  exact div_self (hz _)

private lemma mk_constant (a : ℂ) : Ideal.Quotient.mk (relations m r z) (MvPolynomial.C a) =
    algebraMap ℂ (Curve m r z) a := rfl

lemma coordinate_power (hz : ∀ i, z i ≠ 0) (i : Fin (m+1)) :
    coordinate m r z i ^ r = 1 - algebraMap ℂ (Curve m r z) (ratio z i) * parameter m r z := by
  induction i using Fin.lastCases with
  | last => rw [ratio_last hz,map_one,one_mul,parameter]; ring
  | cast i =>
    have he := Ideal.Quotient.eq_zero_iff_mem.mpr
      (show relation m r z i ∈ relations m r z from Ideal.subset_span ⟨i,rfl⟩)
    simp only [relation,map_sub,map_mul,map_pow,mk_constant] at he
    let l := z (Fin.last (m+1))
    let c := z i.castSucc.succ
    let A := algebraMap ℂ (Curve m r z)
    change A l * coordinate m r z i.castSucc ^ r - A c * coordinate m r z (Fin.last m)^r -
      (A l-A c)=0 at he
    change coordinate m r z i.castSucc ^ r = 1 - A (c/l) * (1-coordinate m r z (Fin.last m)^r)
    have hl : l≠0 := hz _
    have cancel : A l * A l⁻¹ = 1 := by rw [← map_mul,mul_inv_cancel₀ hl,map_one]
    rw [div_eq_mul_inv,map_mul]
    linear_combination (A l⁻¹) * he + (1-coordinate m r z i.castSucc ^ r) * (cancel)

private lemma translated_injective (t : ℂ) :
    Function.Injective (Polynomial.aeval (R:=ℂ) (PowerSeries.X + PowerSeries.C t : PowerSeries ℂ)) := by
  let E := Polynomial.algEquivAevalXAddC t
  let J := Polynomial.coeToPowerSeries.algHom ℂ (R:=ℂ)
  have he : Polynomial.aeval (R:=ℂ) (PowerSeries.X + PowerSeries.C t : PowerSeries ℂ) = J.comp E.toAlgHom := by
    apply Polynomial.algHom_ext
    simp [E,J,Polynomial.coeToPowerSeries.algHom_apply,Polynomial.algEquivAevalXAddC_apply]
  rw [he]
  have hJ : Function.Injective J := by
    intro p q h
    apply Polynomial.coe_injective ℂ
    simpa [J,Polynomial.coeToPowerSeries.algHom_apply] using h
  intro f g h
  exact E.injective (hJ h)

lemma specialization_injective [(relations m r z).IsPrime] (hr : 0<r) (hz : ∀ i, z i≠0)
    (t : ℂ) (φ : Curve m r z →ₐ[ℂ] PowerSeries ℂ)
    (hφ : φ (parameter m r z) = PowerSeries.X + PowerSeries.C t) :
    Function.Injective φ := by
  let β : Polynomial ℂ →ₐ[ℂ] Curve m r z := Polynomial.aeval (parameter m r z)
  let : Algebra (Polynomial ℂ) (Curve m r z) := β.toRingHom.toAlgebra
  have hC (a : ℂ) : IsIntegral (Polynomial ℂ) (algebraMap ℂ (Curve m r z) a) := by
    have h : algebraMap (Polynomial ℂ) (Curve m r z) (Polynomial.C a) = algebraMap ℂ (Curve m r z) a :=
      Polynomial.aeval_C _ _
    rw [← h]
    exact isIntegral_algebraMap
  have hU : IsIntegral (Polynomial ℂ) (parameter m r z) := by
    have h : algebraMap (Polynomial ℂ) (Curve m r z) Polynomial.X = parameter m r z :=
      Polynomial.aeval_X _
    rw [← h]
    exact isIntegral_algebraMap
  have hX (i : Fin (m+1)) : IsIntegral (Polynomial ℂ) (coordinate m r z i) := by
    apply IsIntegral.of_pow hr
    rw [coordinate_power hz]
    exact isIntegral_one.sub ((hC _).mul hU)
  have : Algebra.IsIntegral (Polynomial ℂ) (Curve m r z) := ⟨by
    intro a
    obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective a
    induction f using MvPolynomial.induction_on with
    | C c => exact hC c
    | add f g hf hg => rw [map_add];exact hf.add hg
    | mul_X f i hf => rw [map_mul];exact hf.mul (hX i)⟩
  have comp : φ.comp β = Polynomial.aeval (R:=ℂ) (PowerSeries.X + PowerSeries.C t) := by
    apply Polynomial.algHom_ext
    simpa [β] using hφ
  apply (RingHom.injective_iff_ker_eq_bot φ.toRingHom).mpr
  apply Ideal.eq_bot_of_comap_eq_bot (R:=Polynomial ℂ)
  change RingHom.ker (φ.comp β).toRingHom = ⊥
  rw [comp]
  exact (RingHom.injective_iff_ker_eq_bot _).mp (translated_injective t)

end
end OMA.S_mo_257393

namespace OMA.S_mo_257393
open MvPolynomial
noncomputable section
variable {m r : ℕ} {z : Fin (m+2) → ℂ}
abbrev S := PowerSeries ℂ
abbrev L := FractionRing S

private lemma local_ring (hr : 0<r) (hz : ∀ i, z i≠0) (t : ℂ)
    (ht : ∀ i : Fin (m+1), 1-ratio z i*t≠0) :
    ∃ (e : Curve m r z →ₐ[ℂ] S) (w : Fin (m+1) → S),
      (∀ i, IsUnit (w i)) ∧ (∀ i, e (coordinate m r z i) = w i) ∧
      e (parameter m r z) = PowerSeries.X + PowerSeries.C t := by
  choose w hw hu using fun i => Local.exists_pow_eq_linear hr (ht i) (-(ratio z i))
  let T : S := PowerSeries.X + PowerSeries.C t
  have pw (i : Fin (m+1)) : w i ^ r = 1-PowerSeries.C (ratio z i)*T := by
    rw [hw]
    simp only [map_sub,map_one,map_mul,map_neg,T]
    ring
  let a : Raw m →ₐ[ℂ] S := MvPolynomial.aeval w
  have ann (i : Fin m) : a (relation m r z i) = 0 := by
    let l := z (Fin.last (m+1))
    let c := z i.castSucc.succ
    have hc : l * ratio z i.castSucc = c := by
      change l*(c/l)=c
      field_simp [l,hz]
    have hd := congrArg (PowerSeries.C (R:=ℂ)) hc
    change PowerSeries.C (l*ratio z i.castSucc) = PowerSeries.C c at hd
    rw [map_mul] at hd
    simp only [relation,map_sub,map_mul,map_pow,a,MvPolynomial.aeval_X,MvPolynomial.aeval_C]
    change PowerSeries.C l * w i.castSucc ^ r - PowerSeries.C c * w (Fin.last m)^r -
      (PowerSeries.C l-PowerSeries.C c) = 0
    rw [pw,pw,ratio_last hz,map_one,one_mul]
    linear_combination -T * hd
  have ker : relations m r z ≤ RingHom.ker a.toRingHom :=
    Ideal.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact ann i)
  let e := Ideal.Quotient.liftₐ (relations m r z) a (fun f hf => ker hf)
  have he (i : Fin (m+1)) : e (coordinate m r z i) = w i := by
    change a (MvPolynomial.X i) = w i
    exact MvPolynomial.aeval_X _ _
  refine ⟨e,w,hu,he,?_⟩
  rw [parameter,map_sub,map_one,map_pow,he,pw,ratio_last hz,map_one,one_mul]
  change 1-(1-T)=T
  ring

lemma local_field [(relations m r z).IsPrime] (hr : 0<r) (hz : ∀ i, z i≠0) (t : ℂ)
    (ht : ∀ i : Fin (m+1), 1-ratio z i*t≠0) :
    ∃ (φ : F m r z →ₐ[ℂ] L) (w : Fin (m+1) → S), (∀ i, IsUnit (w i)) ∧
      (∀ i, φ (x m r z i) = algebraMap S L (w i)) ∧
      1-φ (x m r z (Fin.last m))^r = algebraMap S L (PowerSeries.X + PowerSeries.C t) := by
  obtain ⟨e,w,hu,he,hT⟩ := local_ring hr hz t ht
  let g := (IsScalarTower.toAlgHom ℂ S L).comp e
  have hg : Function.Injective g :=
    (IsFractionRing.injective S L).comp (specialization_injective hr hz t e hT)
  let φ : F m r z →ₐ[ℂ] L := IsFractionRing.liftAlgHom hg
  have hφ (y : Curve m r z) : φ (algebraMap (Curve m r z) (F m r z) y) = algebraMap S L (e y) :=
    IsFractionRing.lift_algebraMap hg y
  have hx (i : Fin (m+1)) : φ (x m r z i) = algebraMap S L (w i) := by
    rw [x,hφ,he]
  refine ⟨φ,w,hu,hx,?_⟩
  rw [x,hφ,← map_pow,← map_one (algebraMap S L),← map_sub]
  apply congrArg (algebraMap S L)
  simpa only [parameter,map_sub,map_one,map_pow] using hT

end
end OMA.S_mo_257393

namespace OMA.S_mo_257393
noncomputable section

private lemma scaled_binomial {K : Type*} [Field K] (φ : K →+* L)
    {a v : K} (ha : a ≠ 0) {n : ℕ} (hn : 0 < n) (u : S) (hu : IsUnit u)
    (hφ : φ (v/a) = algebraMap S L (u * PowerSeries.X)) :
    Irreducible (Polynomial.C a * Polynomial.X ^ n - Polynomial.C v) := by
  have h2 : ¬ PowerSeries.X^2 ∣ u*PowerSeries.X := by
    rw [pow_two,mul_dvd_mul_iff_right PowerSeries.X_prime.ne_zero]
    exact fun h => PowerSeries.X_prime.not_isUnit (isUnit_of_dvd_unit h hu)
  have hir := Local.irreducible_X_pow_sub_C hn (dvd_mul_left _ u) h2
  have mon : (Polynomial.X ^ n - Polynomial.C (v/a)).Monic := Polynomial.monic_X_pow_sub_C _ hn.ne'
  have norm : Irreducible (Polynomial.X ^ n - Polynomial.C (v/a)) := by
    apply Polynomial.Monic.irreducible_of_irreducible_map φ _ mon
    simpa [Polynomial.map_sub,Polynomial.map_pow,Polynomial.map_X,Polynomial.map_C,hφ] using hir
  have fac : Polynomial.C a * Polynomial.X ^ n - Polynomial.C v =
      Polynomial.C a * (Polynomial.X ^ n - Polynomial.C (v/a)) := by
    rw [mul_sub,← map_mul]; congr 2; field_simp
  rw [fac,irreducible_isUnit_mul (ha.isUnit.map Polynomial.C)]
  exact norm

private lemma map_powerSeries_C (u : ℂ) :
    algebraMap S L (PowerSeries.C u) = algebraMap ℂ L u :=
  (IsScalarTower.algebraMap_apply ℂ S L u).symm

private theorem irreducible_p {m r k : ℕ} {z : Fin (m+2) → ℂ} [(relations m r z).IsPrime]
    (hr : 0 < r) (hz : ∀ i, z i ≠ 0) : Irreducible (p m r k z) := by
  obtain ⟨φ,w,hw,hx,hparam⟩ := local_field hr hz 0 (by simp)
  let last := Fin.last (m+1)
  let t := Finset.univ.filter (fun i : Fin (m+1) => i.val < k)
  let u : S := PowerSeries.C (z last)⁻¹ * ∏ i ∈ t, w i
  have hu : IsUnit u := ((inv_ne_zero (hz last)).isUnit.map PowerSeries.C).mul
    (IsUnit.prod_iff.mpr fun i _ => hw i)
  apply scaled_binomial φ.toRingHom ((map_ne_zero (algebraMap ℂ (F m r z))).mpr (hz last)) (by omega) u hu
  change φ (((∏ i ∈ t, x m r z i) * (1-x m r z (Fin.last m)^r)) /
    (algebraMap ℂ (F m r z) (z last))) = _
  simp only [map_div₀,map_mul,map_sub,map_one,map_pow,map_prod,AlgHom.commutes,hx] at *
  simp only [map_zero,add_zero] at hparam
  rw [hparam]
  simp only [u,map_mul,map_prod,map_powerSeries_C,map_inv₀,div_eq_mul_inv]
  ring

private theorem irreducible_q {m r : ℕ} {z : Fin (m+2) → ℂ} [(relations m r z).IsPrime]
    (hr : 0 < r) (hz : ∀ i, z i ≠ 0) (hinj : Function.Injective z) : Irreducible (q₀ m r z) := by
  let last := Fin.last (m+1)
  let t := z last / z 0
  have ht (i : Fin (m+1)) : 1-ratio z i*t ≠ 0 := by
    have hi : z i.succ ≠ z 0 := hinj.ne (Fin.succ_ne_zero _)
    dsimp [ratio,t,last]
    intro e
    field_simp [hz] at e
    apply hi
    linear_combination -e
  obtain ⟨φ,w,_,_,hparam⟩ := local_field hr hz t ht
  let u : S := PowerSeries.C (-z 0/z last)
  have hu : IsUnit u := (div_ne_zero (neg_ne_zero.mpr (hz 0)) (hz last)).isUnit.map PowerSeries.C
  apply scaled_binomial φ.toRingHom ((map_ne_zero (algebraMap ℂ (F m r z))).mpr (hz last)) hr u hu
  change φ ((algebraMap ℂ (F m r z) (z 0)*x m r z (Fin.last m)^r+
    algebraMap ℂ (F m r z) (z last-z 0))/(algebraMap ℂ (F m r z) (z last))) = _
  simp only [map_div₀,map_add,map_sub,map_mul,map_pow,AlgHom.commutes]
  rw [show φ (x m r z (Fin.last m))^r=1-algebraMap S L (PowerSeries.X+PowerSeries.C t) by linear_combination -hparam]
  simp only [u,t,map_add,map_powerSeries_C,map_div₀,map_neg]
  field_simp [hz]
  ring

end
end OMA.S_mo_257393

theorem OMA.solution : type_of% @OMA.S_mo_257393.main := by
  intro m r k z _ hr _ _ hz hinj hprime
  let _ := hprime
  exact ⟨OMA.S_mo_257393.irreducible_p (by omega) hz, OMA.S_mo_257393.irreducible_q (by omega) hz hinj⟩

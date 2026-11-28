import OMAReductions.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H2_R1_H2_R1
import Mathlib

/-! A characteristic-p jet reduction of the weighted Kummer congruence.
The parent formulation follows Hanan Beer and Brasca et al. (KummerCriterion,
Apache-2.0).  The two interfaces here separate reduction of integral units
modulo p from the finite polynomial logarithmic-coefficient computation. -/
namespace OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H2_R1_H2_R1_H1_R1
open NumberField
open scoped NumberField BigOperators

/-- A cyclotomic power relation becomes constant modulo (zeta - 1)^(p-1).
Clear negative exponents so the equality needs no inverses in the jet ring. -/
def H1 : Prop := ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p →
  let K := CyclotomicField p ℚ
  let L := maximalRealSubfield K
  let _ : IsCyclotomicExtension {p} ℚ K := CyclotomicField.isCyclotomicExtension p ℚ
  let z := IsCyclotomicExtension.zeta p ℚ K
  let m := (p - 3) / 2
  let R := AdjoinRoot ((Polynomial.X : Polynomial (ZMod p)) ^ (p - 1))
  let t : R := 1 + AdjoinRoot.root _
  let G : Fin m → R := fun a =>
    (∑ i ∈ Finset.range (a.val + 2), t ^ i) *
    (∑ i ∈ Finset.range (a.val + 2), (t ^ (p - 1)) ^ i)
  ∀ g : Fin m → (𝓞 L)ˣ,
    (∀ a, algebraMap (𝓞 L) K (g a : 𝓞 L) =
      (∑ i ∈ Finset.range (a.val + 2), z ^ i) *
        (∑ i ∈ Finset.range (a.val + 2), (z⁻¹) ^ i)) →
    ∀ (s : ℤ) (e : Fin m → ℤ) (u : (𝓞 L)ˣ),
      u ^ p = (-1) ^ s * ∏ a, g a ^ e a →
      ∃ c : ZMod p, (∏ a, G a ^ (e a).toNat) =
        (algebraMap (ZMod p) R c) * ∏ a, G a ^ (-e a).toNat

/-- Finite jet identity: constancy of the signed product kills every even
logarithmic coefficient. In exponential coordinates those coefficients are
Bernoulli multiples of the even moments of the exponents. -/
def H2 : Prop := ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p →
  let m := (p - 3) / 2
  let R := AdjoinRoot ((Polynomial.X : Polynomial (ZMod p)) ^ (p - 1))
  let t : R := 1 + AdjoinRoot.root _
  let G : Fin m → R := fun a =>
    (∑ i ∈ Finset.range (a.val + 2), t ^ i) *
    (∑ i ∈ Finset.range (a.val + 2), (t ^ (p - 1)) ^ i)
  ∀ e : Fin m → ℤ,
    (∃ c : ZMod p, (∏ a, G a ^ (e a).toNat) =
        (algebraMap (ZMod p) R c) * ∏ a, G a ^ (-e a).toNat) → ∀ j : Fin m,
      ((bernoulli (2 * (j.val + 1))).num : ZMod p) *
        (∑ a : Fin m, (((a.val + 2 : ℕ) : ZMod p) ^ (2 * (j.val + 1)) - 1) *
          (e a : ZMod p)) = 0

theorem main : H1 → H2 → OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H2_R1_H2_R1.H1 := by
  intro hj hc p hp h5
  dsimp only
  intro g hg s e u hu
  exact hc p h5 e (hj p h5 g hg s e u hu)

end OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H2_R1_H2_R1_H1_R1

section

/-! Direct integral specialization proof for the Kummer jet formulation of the
parent reduction (following Hanan Beer and Brasca et al., KummerCriterion). -/
open NumberField Polynomial
open scoped NumberField BigOperators
noncomputable section
namespace KummerJetProof
variable (p : ℕ) [Fact p.Prime]
private abbrev F := (X : (ZMod p)[X]) ^ (p-1)
private abbrev J := AdjoinRoot (F p)
private abbrev x : J p := AdjoinRoot.root _
private theorem nilp : x p ^ (p-1) = 0 := by
  simpa only [F, map_pow, AdjoinRoot.mk_X] using (AdjoinRoot.mk_self (f:=F p))
private theorem nilp' : x p ^ p = 0 := by
  exact pow_eq_zero_of_le (Nat.sub_le ..) (nilp p)
private instance : CharP (J p) p :=
  charP_of_injective_ringHom (AdjoinRoot.of.injective_of_degree_ne_zero (f:=F p) (by
    have hp := (Fact.out : Nat.Prime p).two_le
    simp [F, show p-1 ≠ 0 by omega])) p
private theorem constant (a : J p) : ∃ c : ZMod p, a ^ p = algebraMap _ _ c := by
  obtain ⟨f,rfl⟩ := AdjoinRoot.mk_surjective a
  induction f using Polynomial.induction_on' with
  | add f g ih jh =>
    obtain ⟨c,hc⟩ := ih
    obtain ⟨d,hd⟩ := jh
    exact ⟨c+d, by rw [map_add, add_pow_char, hc, hd, map_add]⟩
  | monomial n c =>
    cases n with
    | zero => exact ⟨c^p, by rw [monomial_zero_left, AdjoinRoot.mk_C, map_pow]; rfl⟩
    | succ n => refine ⟨0, ?_⟩; simp [← C_mul_X_pow_eq_monomial, pow_succ, mul_pow, AdjoinRoot.mk_X, show AdjoinRoot.root (F p) ^ p = 0 from nilp' p] 
private theorem specialize {K : Type*} [Field K] [CharZero K] [IsCyclotomicExtension {p} ℚ K]
    {z : K} (hz : IsPrimitiveRoot z p) : ∃ q : 𝓞 K →+* J p, q hz.toInteger = 1 + x p := by
  let b := hz.integralPowerBasis
  have hm : minpoly ℤ b.gen = cyclotomic p ℤ := by
    rw [show b.gen = _ from hz.integralPowerBasis_gen, cyclotomic_eq_minpoly hz (Fact.out : Nat.Prime p).pos]
    exact (minpoly.algHom_eq (IsScalarTower.toAlgHom ℤ (𝓞 K) K) Subtype.val_injective hz.toInteger).symm
  have he : aeval (1 + x p) (minpoly ℤ b.gen) = 0 := by
    rw [hm, ← aeval_map_algebraMap (ZMod p)]
    change aeval (1 + x p) (Polynomial.map (Int.castRingHom (ZMod p)) (cyclotomic p ℤ)) = 0
    rw [map_cyclotomic_int]
    have heq := cyclotomic_mul_prime_eq_pow_of_not_dvd (ZMod p) (n:=1) (p:=p) (Nat.Prime.not_dvd_one Fact.out)
    rw [one_mul, cyclotomic_one] at heq
    simp [heq, nilp]
  exact ⟨(b.lift _ he).toRingHom, by change b.lift _ he _ = _; rw [← hz.integralPowerBasis_gen]; exact b.lift_gen _ he⟩
theorem solution : OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H2_R1_H2_R1_H1_R1.H1 := by
  classical
  intro p hp h5
  let K := CyclotomicField p ℚ
  let L := maximalRealSubfield K
  let _ : IsCyclotomicExtension {p} ℚ K := CyclotomicField.isCyclotomicExtension p ℚ
  let z := IsCyclotomicExtension.zeta p ℚ K
  have hz : IsPrimitiveRoot z p := IsCyclotomicExtension.zeta_spec p ℚ K
  let m := (p-3)/2
  let t := 1 + x p
  let G (a : Fin m) := (∑ i ∈ Finset.range (a.val + 2), t ^ i) *
    (∑ i ∈ Finset.range (a.val + 2), (t ^ (p - 1)) ^ i)
  dsimp only
  intro g hg s e u hu
  obtain ⟨q,hq⟩ := specialize p hz
  let f := q.comp (algebraMap (𝓞 L) (𝓞 K))
  have hinv : z ^ (p-1) = z⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, show p-1+1=p by omega, hz.pow_eq_one]
  have hg' (a : Fin m) : f (g a) = G a := by
    have hint : algebraMap (𝓞 L) (𝓞 K) (g a) =
        (∑ i ∈ Finset.range (a.val+2), hz.toInteger ^ i) *
        (∑ i ∈ Finset.range (a.val+2), (hz.toInteger ^ (p-1)) ^ i) := by
      apply (IsFractionRing.injective (𝓞 K) K)
      rw [← IsScalarTower.algebraMap_apply, map_mul, map_sum, map_sum]
      simpa only [map_pow, show algebraMap (𝓞 K) K hz.toInteger = z from rfl, hinv] using hg a
    change q _ = _
    rw [hint, map_mul, map_sum, map_sum]
    simp only [map_pow, hq, G, t]
  let P := ∏ a, g a ^ (e a).toNat
  let N := ∏ a, g a ^ (-e a).toNat
  have hc : (∏ a, g a ^ e a) * N = P := by
    rw [show N = _ from rfl, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro a _
    rw [← zpow_natCast, ← zpow_add, ← zpow_natCast]; congr 1; omega
  have hclear : P = (-1)^(-s) * u^p * N := by
    rw [hu, ← hc]; group
  obtain ⟨c, hc'⟩ := constant p (f u)
  have heq := congrArg (fun v : (𝓞 L)ˣ => f (v : 𝓞 L)) hclear
  by_cases hs : Even (-s)
  · refine ⟨c, ?_⟩
    simpa [P, N, hs.neg_one_zpow, hg', hc', G, t] using heq
  · refine ⟨-c, ?_⟩
    have hsign : (-1 : (𝓞 L)ˣ)^(-s) = -1 := by rw [neg_one_zpow_eq_ite, if_neg hs]
    simpa [P, N, hsign, hg', hc', G, t] using heq

end KummerJetProof

theorem CombinedJetH1 : OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H2_R1_H2_R1_H1_R1.H1 := KummerJetProof.solution

end

end

section

/-! Finite exponential jets for the weighted Kummer congruence. The target formulation
follows Hanan Beer and Brasca et al.; the proof uses Mathlib’s Bernoulli generating series. -/
namespace KJet
open Polynomial
open scoped BigOperators
variable {K S : Type*} [Field K] [CommRing S] [Algebra K S]
noncomputable def geom (k : ℕ) (t : S) : S := ∑ i ∈ Finset.range k, t ^ i
noncomputable def pair (k b : ℕ) (t : S) : S := geom k t * geom k (t ^ b)
noncomputable def side {m : ℕ} (b : ℕ) (e : Fin m → ℤ) (t : S) : S :=
  ∏ a, pair (a.val+2) b t ^ (e a).toNat
lemma map_side {T : Type*} [CommRing T] (f : S →+* T) {m : ℕ} (b : ℕ) (e : Fin m → ℤ) (t : S) :
    f (side b e t) = side b e (f t) := by simp [side, pair, geom]
lemma poly_rel {m N b : ℕ} (e : Fin m → ℤ) (c : K)
    (h : let f := (X : K[X]) ^ N
         let t := 1 + AdjoinRoot.root f
         side b e t = algebraMap K (AdjoinRoot f) c * side b (-e) t) :
    X ^ N ∣ side b e (1 + X : K[X]) - C c * side b (-e) (1 + X) := by
  apply AdjoinRoot.mk_eq_zero.mp
  simpa [map_side, AdjoinRoot.mk_X, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq, sub_eq_zero] using h
lemma subst_rel {m N b : ℕ} (e : Fin m → ℤ) (c : K) (t : S)
    (h : X ^ N ∣ side b e (1 + X : K[X]) - C c * side b (-e) (1 + X)) :
    (t - 1) ^ N ∣ side b e t - algebraMap K S c * side b (-e) t := by
  have H := map_dvd (aeval (t - 1) : K[X] →ₐ[K] S).toRingHom h
  simpa [side, pair, geom] using H
end KJet
namespace KJet
open PowerSeries
open scoped PowerSeries BigOperators
variable {R : Type*} [CommRing R]
noncomputable def ed (f : R⟦X⟧) := X * (d⁄dX R f)
lemma ed_mul (f g : R⟦X⟧) : ed (f*g) = ed f * g + f * ed g := by
  simp only [ed, Derivation.leibniz, smul_eq_mul]; ring
lemma ed_sub (f g : R⟦X⟧) : ed (f-g) = ed f - ed g := by simp [ed,mul_sub]
lemma ed_dvd {N : ℕ} {f : R⟦X⟧} (h : X ^ N ∣ f) : X ^ N ∣ ed f := by
  obtain ⟨s,rfl⟩ := h
  rw [ed_mul]; apply dvd_add
  · cases N with
    | zero => simp
    | succ n =>
      use (n+1 : ℕ) * s
      rw [ed, derivative_pow, derivative_X, Nat.add_sub_cancel, mul_one, pow_succ]; ring
  · exact dvd_mul_right ..
lemma ed_pow (f L : R⟦X⟧) (hf : ed f = f * L) (n : ℕ) :
    ed (f^n) = f^n * (n*L) := by
  induction n with
  | zero => simp [ed]
  | succ n ih => rw [pow_succ, ed_mul, ih, hf, Nat.cast_succ]; ring
lemma ed_prod {ι : Type*} (s : Finset ι) (f L : ι → R⟦X⟧) (h : ∀ i, ed (f i) = f i * L i) :
    ed (∏ i ∈ s, f i) = (∏ i ∈ s, f i) * ∑ i ∈ s, L i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ed]
  | insert i s hi ih => simp only [Finset.prod_insert hi, Finset.sum_insert hi, ed_mul, ih, h]; ring
lemma signed_dvd {N : ℕ} {a b U V : R⟦X⟧} {c : R} (ha : IsUnit a)
    (da : ed a = a * U) (db : ed b = b * V) (h : X ^ N ∣ a - C c * b) :
    X ^ N ∣ U - V := by
  apply ha.dvd_mul_left.mp
  have H := ed_dvd h
  rw [ed_sub, ed_mul, da, db, show ed (C c) = 0 by simp [ed], zero_mul, zero_add] at H
  convert dvd_sub H (dvd_mul_of_dvd_left h V) using 1; ring
end KJet

namespace KJet
open PowerSeries
open scoped PowerSeries BigOperators
variable {K : Type*} [Field K]
noncomputable def eld (f : K⟦X⟧) := ed f * f⁻¹
lemma ed_fac {f : K⟦X⟧} (h : constantCoeff f ≠ 0) : ed f = f * eld f := by
  unfold eld; rw [mul_left_comm, PowerSeries.mul_inv_cancel f h, mul_one]
lemma logsum {m N : ℕ} (f L : Fin m → K⟦X⟧) (hL : ∀ i, ed (f i) = f i * L i)
    (hf : ∀ i, constantCoeff (f i) ≠ 0) (e : Fin m → ℤ) (c : K)
    (h : X ^ N ∣ (∏ i, f i ^ (e i).toNat) - C c * ∏ i, f i ^ (-e i).toNat)
    {n : ℕ} (hn : n < N) : ∑ i, (e i : K) * coeff n (L i) = 0 := by
  have aux (a : Fin m → ℕ) := ed_prod Finset.univ (fun i => f i ^ a i)
    (fun i => a i * L i) (fun i => ed_pow _ _ (hL i) _)
  have hu : IsUnit (∏ i, f i ^ (e i).toNat) := by
    apply isUnit_iff_constantCoeff.mpr; rw [isUnit_iff_ne_zero, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => by simp [hf i]
  have H := X_pow_dvd_iff.mp (signed_dvd hu (aux _) (aux _) h) n hn
  simp only [map_sum,
    ← Finset.sum_sub_distrib, ← sub_mul] at H
  convert H using 2 with i
  have J := congrArg (fun x : ℤ => (x : K)) (Int.toNat_sub_toNat_neg (e i))
  push_cast at J
  rw [sub_mul, map_sub, ← nsmul_eq_mul, ← nsmul_eq_mul, map_nsmul, map_nsmul]
  simp only [nsmul_eq_mul, ← sub_mul, J]
end KJet
namespace KJet
open PowerSeries
open scoped PowerSeries BigOperators
noncomputable def E (p : ℕ) [Fact p.Prime] : (ZMod p)⟦X⟧ := mk fun i => ((i.factorial : ZMod p)⁻¹)
theorem wrap (hc : ∀ (p : ℕ) [Fact p.Prime] (b k n : ℕ), 0 < b → 0 < k → k < p → 1 < n → n < p →
    coeff n (eld (geom k ((E p)^b))) * (n.factorial * ((bernoulli n).den : ZMod p)) =
      (b : ZMod p)^n * ((k : ZMod p)^n - 1) * (bernoulli n).num) : OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H2_R1_H2_R1_H1_R1.H2 := by
  intro p hp h5
  dsimp only
  intro e ⟨c,h⟩ j
  let m := (p-3)/2
  let n := 2*(j.val+1)
  have hn : n < p-1 := by dsimp [n]; have := j.isLt; omega
  have hn' : 1 < n := by dsimp [n]; omega
  let F (a : Fin m) (b : ℕ) := geom (a.val+2) ((E p)^b)
  have hE : constantCoeff (E p) = 1 := by simp [E, constantCoeff_mk]
  have hk (a : Fin m) : a.val+2 < p := by have := a.isLt; dsimp [m] at this; omega
  have hF (a : Fin m) (b : ℕ) : constantCoeff (F a b) ≠ 0 := by
    simpa [F, geom, hE] using (ZMod.natCast_eq_zero_iff (a.val+2) p).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by omega) (hk a))
  have heq := subst_rel e c (E p) (poly_rel (N:=p-1) (b:=p-1) e c h)
  have xd : X ∣ E p - 1 := X_dvd_iff.mpr (by simp [hE])
  have hd := dvd_trans (pow_dvd_pow_of_dvd xd (p-1)) heq
  let L (a : Fin m) := eld (F a 1) + eld (F a (p-1))
  have H := logsum (N:=p-1) (fun a => F a 1 * F a (p-1)) L (fun a => by
    rw [ed_mul, ed_fac (hF a 1), ed_fac (hF a (p-1))]; dsimp [L]; ring)
    (fun a => by simp [hF a 1, hF a (p-1)]) e c (by simpa [side,pair,F] using hd) hn
  let V : ZMod p := n.factorial * ((bernoulli n).den : ZMod p)
  have hpow : ((p-1 : ℕ) : ZMod p)^n = 1 := by
    rw [Nat.cast_pred (by omega), ZMod.natCast_self, zero_sub, (even_two_mul _).neg_pow, one_pow]
  have hrow (a : Fin m) : coeff n (L a) * V =
      2 * (bernoulli n).num * (((a.val+2 : ℕ) : ZMod p)^n - 1) := by
    dsimp only [L]; rw [map_add, add_mul]
    have c1 := hc p 1 (a.val+2) n (by omega) (by omega) (hk a) hn' (by omega)
    have c2 := hc p (p-1) (a.val+2) n (by omega) (by omega) (hk a) hn' (by omega)
    change _ + _ = _
    rw [show coeff n (eld (F a 1)) * V = _ from c1, show coeff n (eld (F a (p-1))) * V = _ from c2, hpow]; push_cast; ring
  have result : 2 * ((bernoulli n).num : ZMod p) *
      (∑ a : Fin m, (((a.val+2 : ℕ) : ZMod p)^n - 1) * (e a : ZMod p)) = 0 := by
    rw [Finset.mul_sum]
    calc
      _ = (∑ a, (e a : ZMod p) * coeff n (L a)) * V := by
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro a _
        rw [mul_assoc (e a : ZMod p), hrow]; ring
      _ = 0 := by rw [H,zero_mul]
  have htwo : (2 : ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff 2 p).not.mpr
    (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  rw [mul_assoc] at result
  exact (mul_eq_zero.mp result).resolve_left htwo
end KJet

open PowerSeries
open scoped PowerSeries
namespace KummerRatGeom
noncomputable section

private abbrev E (a : ℕ) := exp ℚ ^ a
private abbrev B (a : ℕ) := rescale (a : ℚ) (bernoulli'PowerSeries ℚ)

private lemma bern_id (a : ℕ) : B a * (E a - 1) = X * (a : PowerSeries ℚ) * E a := by
  have h := congrArg (rescale (a : ℚ)) (bernoulli'PowerSeries_mul_exp_sub_one ℚ)
  simpa [B, E, exp_pow_eq_rescale_exp, rescale_X, mul_comm, mul_left_comm] using h

private lemma deriv_E (a : ℕ) : derivative ℚ (E a) = a * E a := by
  cases a with
  | zero => simp [E]
  | succ a => rw [E, derivative_pow, derivative_exp]; simp [pow_succ, mul_assoc]

private lemma ne_one_E {b : ℕ} (hb : 0 < b) : E b - 1 ≠ 0 := by
  intro h
  have hh := congrArg (coeff (R := ℚ) 1) (sub_eq_zero.mp h)
  simp [E, exp_pow_eq_rescale_exp, coeff_rescale, coeff_exp, hb.ne'] at hh

/-- The geometric factor evaluated at the formal exponential. -/
def geom (k b : ℕ) : PowerSeries ℚ := ∑ i ∈ Finset.range k, (exp ℚ ^ b)^i

private lemma geom_eq (k b : ℕ) : geom k b * (E b - 1) = E (b*k) - 1 := by
  simpa [geom, E, pow_mul] using geom_sum_mul (exp ℚ ^ b) k

private lemma geom_cc (k b : ℕ) : constantCoeff (geom k b) = (k : ℚ) := by simp [geom]

private lemma series_eq (k b : ℕ) (hk : 0 < k) (hb : 0 < b) :
    X * derivative ℚ (geom k b) * (geom k b)⁻¹ = B (b*k) - B b := by
  let G := geom k b
  have hG : G * G⁻¹ = 1 := PowerSeries.mul_inv_cancel G (by rw [show G = geom k b from rfl, geom_cc]; positivity)
  have h := geom_eq k b
  change G * _ = _ at h
  have hd := congrArg (derivative ℚ) h
  simp only [Derivation.leibniz, map_sub, Derivation.map_one_eq_zero, sub_zero, smul_eq_mul, deriv_E] at hd
  have hb' := bern_id b
  have hbk := bern_id (b*k)
  rw [← h] at hbk
  have key : X * derivative ℚ G = (B (b*k) - B b) * G := by
    apply mul_right_cancel₀ (ne_one_E hb)
    linear_combination X * hd - hbk + G * hb'
  change X * derivative ℚ G * G⁻¹ = _
  rw [key, mul_assoc, hG, mul_one]

/-- Bernoulli coefficient of the Euler logarithmic derivative in degrees above one. -/
theorem coeff_euler_geom (k b n : ℕ) (hk : 0 < k) (hb : 0 < b) (hn : 1 < n) :
    coeff n (X * derivative ℚ (geom k b) * (geom k b)⁻¹) =
      (b : ℚ)^n * ((k : ℚ)^n - 1) * bernoulli n / n.factorial := by
  rw [series_eq k b hk hb]
  simp only [map_sub, B, coeff_rescale, bernoulli'PowerSeries, coeff_mk, Algebra.algebraMap_self_apply,
    Nat.cast_mul, mul_pow, ← bernoulli_eq_bernoulli'_of_ne_one (by omega : n ≠ 1)]
  ring

end
end KummerRatGeom

namespace KummerH2Transfer
open PowerSeries
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- A common fractional representative with denominator invertible modulo `p`. -/
private def Rel (q : ℚ) (z : ZMod p) : Prop :=
  ∃ a b : ℤ, (b : ZMod p) ≠ 0 ∧ q * (b : ℚ) = a ∧ z * (b : ZMod p) = a

private theorem relInt (a : ℤ) : Rel (a : ℚ) (a : ZMod p) :=
  ⟨a, 1, by simp, by simp, by simp⟩
private theorem relNat (a : ℕ) : Rel (a : ℚ) (a : ZMod p) := by exact_mod_cast relInt (p := p) (a : ℤ)
private theorem relZero : Rel 0 (0 : ZMod p) := by simpa using relNat (p := p) 0
private theorem relOne : Rel 1 (1 : ZMod p) := by simpa using relNat (p := p) 1

private theorem relAdd {q r : ℚ} {z w : ZMod p} (h : Rel q z) (j : Rel r w) : Rel (q+r) (z+w) := by
  obtain ⟨a,b,hb,hab,hab'⟩ := h
  obtain ⟨c,d,hd,hcd,hcd'⟩ := j
  refine ⟨a*d+c*b,b*d,by simpa using mul_ne_zero hb hd, ?_, ?_⟩ <;> push_cast
  · linear_combination (d:ℚ)*hab + (b:ℚ)*hcd
  · linear_combination (d:ZMod p)*hab' + (b:ZMod p)*hcd'
private theorem relMul {q r : ℚ} {z w : ZMod p} (h : Rel q z) (j : Rel r w) : Rel (q*r) (z*w) := by
  obtain ⟨a,b,hb,hab,hab'⟩ := h
  obtain ⟨c,d,hd,hcd,hcd'⟩ := j
  refine ⟨a*c,b*d,by simpa using mul_ne_zero hb hd, ?_, ?_⟩ <;> push_cast
  · rw [← hab, ← hcd]; ring
  · rw [← hab', ← hcd']; ring
private theorem relNeg {q : ℚ} {z : ZMod p} (h : Rel q z) : Rel (-q) (-z) := by
  obtain ⟨a,b,hb,hab,hab'⟩ := h
  exact ⟨-a,b,hb,by simp [hab],by simp [hab']⟩
private theorem relInv {q : ℚ} {z : ZMod p} (h : Rel q z) (hz : z ≠ 0) : Rel q⁻¹ z⁻¹ := by
  obtain ⟨a,b,hb,hab,hab'⟩ := h
  have ha : (a : ZMod p) ≠ 0 := hab' ▸ mul_ne_zero hz hb
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast (show a ≠ 0 from fun e => ha (by simp [e]))
  have hq : q ≠ 0 := fun e => ha' (by simpa [e] using hab.symm)
  exact ⟨b,a,ha,by rw [← hab, inv_mul_cancel_left₀ hq],by rw [← hab',inv_mul_cancel_left₀ hz]⟩

private theorem relClear {q : ℚ} {z : ZMod p} (h : Rel q z) (u v : ℤ)
    (e : q * (v : ℚ) = u) : z * (v : ZMod p) = u := by
  obtain ⟨a,b,hb,hab,hab'⟩ := h
  have he : (a:ℚ) * v = (u:ℚ) * b := by rw [← hab, ← e]; ring
  have hi : a * v = u * b := by exact_mod_cast he
  have hf := congrArg (fun x : ℤ => (x : ZMod p)) hi
  push_cast at hf
  apply mul_right_cancel₀ hb
  linear_combination (v : ZMod p) * hab' + hf

private theorem relSum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (g : ι → ZMod p)
    (h : ∀ i ∈ s, Rel (f i) (g i)) : Rel (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (relZero (p := p))
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact relAdd (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))

private def SeriesRel (f : PowerSeries ℚ) (g : PowerSeries (ZMod p)) :=
  ∀ n < p, Rel (coeff n f) (coeff n g)

private theorem seriesMul {f f' : PowerSeries ℚ} {g g' : PowerSeries (ZMod p)}
    (h : SeriesRel f g) (h' : SeriesRel f' g') : SeriesRel (f*f') (g*g') := by
  intro n hn
  simp only [coeff_mul]
  apply relSum
  intro i hi
  have e := Finset.HasAntidiagonal.mem_antidiagonal.mp hi
  exact relMul (h _ (by omega)) (h' _ (by omega))

private theorem seriesPow {f : PowerSeries ℚ} {g : PowerSeries (ZMod p)}
    (h : SeriesRel f g) (k : ℕ) : SeriesRel (f^k) (g^k) := by
  induction k with
  | zero =>
    intro n _
    simp only [pow_zero, coeff_one]; split <;> first | exact relZero | exact relOne
  | succ k ih => simpa only [pow_succ] using seriesMul ih h

def geom {R : Type*} [CommSemiring R] (b k : ℕ) (E : PowerSeries R) : PowerSeries R :=
  ∑ i ∈ Finset.range k, (E^b)^i

def E_F (p : ℕ) : PowerSeries (ZMod p) := mk (fun n => ((n.factorial : ZMod p)⁻¹))

def elog {R : Type*} [Field R] (G : PowerSeries R) := X * derivative R G * G⁻¹

private theorem seriesExp : SeriesRel (exp ℚ) (E_F p) := by
  intro i hi
  have hn : (i.factorial : ZMod p) ≠ 0 := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [Nat.factorial_succ, Nat.cast_mul]
      exact mul_ne_zero (fun e => (Nat.not_dvd_of_pos_of_lt (by omega) hi) ((ZMod.natCast_eq_zero_iff _ _).mp e)) (ih (by omega))
  simpa [E_F, coeff_exp, one_div] using relInv (relNat i.factorial) hn

private theorem seriesGeom (b k : ℕ) : SeriesRel (geom b k (exp ℚ)) (geom b k (E_F p)) := by
  intro n hn
  simp only [geom, map_sum]
  exact relSum _ _ _ (fun i _ => seriesPow (seriesPow seriesExp b) i n hn)

private theorem seriesInv {f : PowerSeries ℚ} {g : PowerSeries (ZMod p)}
    (h : SeriesRel f g) (hg : constantCoeff g ≠ 0) : SeriesRel f⁻¹ g⁻¹ := by
  have h0 : Rel (constantCoeff f) (constantCoeff g) := by
    simpa only [coeff_zero_eq_constantCoeff_apply] using h 0 (Fact.out : p.Prime).pos
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    rw [coeff_inv, coeff_inv]
    split
    · exact relInv h0 hg
    · apply relMul (relNeg (relInv h0 hg))
      apply relSum
      intro x hx
      have e := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
      split
      · rename_i hl; exact relMul (h _ (by omega)) (ih _ hl (by omega))
      · exact relZero

private theorem coeffEuler {R : Type*} [Field R] (f : PowerSeries R) (n : ℕ) :
    coeff n (X * derivative R f) = coeff n f * (n : R) := by
  cases n with
  | zero => simp [coeff_zero_eq_constantCoeff_apply]
  | succ i =>
    rw [mul_comm, ← pow_one (X : PowerSeries R), coeff_mul_X_pow, coeff_derivative, Nat.cast_succ]

private theorem seriesElog {f : PowerSeries ℚ} {g : PowerSeries (ZMod p)}
    (h : SeriesRel f g) (hg : constantCoeff g ≠ 0) : SeriesRel (elog f) (elog g) := by
  apply seriesMul _ (seriesInv h hg)
  intro n hn
  simp only [coeffEuler]
  exact relMul (h _ hn) (relNat n)

/-- Transfer a cleared rational coefficient identity; `V` need not be a unit modulo `p`. -/
theorem transfer_int (b k n : ℕ) (hn : n < p) (hk : k % p ≠ 0) (U V : ℤ)
    (h : coeff n (elog (geom b k (exp ℚ))) * (V : ℚ) = U) :
    coeff n (elog (geom b k (E_F p))) * (V : ZMod p) = U := by
  apply relClear _ U V h
  apply seriesElog (seriesGeom b k) _ n hn
  have hk' : (k : ZMod p) ≠ 0 := fun h0 => hk (Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).mp h0))
  simpa [geom, E_F, constantCoeff_mk] using hk'

/-- The canonical numerator/denominator form of coefficient transfer. -/
theorem transfer (b k n : ℕ) (hn : n < p) (hk : k % p ≠ 0) (q : ℚ)
    (hq : coeff n (elog (geom b k (exp ℚ))) = q) :
    coeff n (elog (geom b k (E_F p))) * (q.den : ZMod p) = (q.num : ZMod p) := by
  simpa only [Int.cast_natCast] using transfer_int b k n hn hk q.num (q.den : ℤ) (by
    rw [hq, Int.cast_natCast, Rat.mul_den_eq_num])

end
end KummerH2Transfer
theorem CombinedJetH2 : OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H2_R1_H2_R1_H1_R1.H2 := by
  apply KJet.wrap
  intro p hp b k n hb hk hkp hn hnp
  let U : ℤ := (b:ℤ)^n * ((k:ℤ)^n - 1) * (bernoulli n).num
  let V : ℤ := (n.factorial:ℤ) * (bernoulli n).den
  have hQ : PowerSeries.coeff n (KummerH2Transfer.elog (KummerH2Transfer.geom b k (PowerSeries.exp ℚ))) * (V:ℚ) = U := by
    change PowerSeries.coeff n (PowerSeries.X * PowerSeries.derivative ℚ (KummerRatGeom.geom k b) * (KummerRatGeom.geom k b)⁻¹) * _ = _
    rw [KummerRatGeom.coeff_euler_geom k b n hk hb hn]; dsimp only [V,U]; push_cast
    rw [← Rat.mul_den_eq_num (bernoulli n)]; field_simp
  have hF := KummerH2Transfer.transfer_int (p:=p) b k n hnp (by rw [Nat.mod_eq_of_lt hkp]; omega) U V hQ
  dsimp only [U,V] at hF; push_cast at hF; exact hF

end

theorem OMA.solution : OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H2_R1_H2_R1.H1 := OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H2_R1_H2_R1_H1_R1.main CombinedJetH1 CombinedJetH2

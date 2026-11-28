import OMAStatements.S_mo_341448

/-!
# Irreducibility of the triangular sum

Question by MarkoR, https://mathoverflow.net/questions/341448 (CC BY-SA 4.0).
Felipe Voloch pointed to Theorem 1 of F. Rodríguez Villegas, J. F. Voloch and
D. Zagier, "Constructions of plane curves with many points", Acta Arith. 99 (2001).

The formal proof obtains projective smoothness by Newton interpolation with
repeated nodes, derives intersection of factors from Krull's height theorem and
the Nullstellensatz, and descends from complex homogeneous polynomials to
integer bivariate polynomials.
Credit: @connoranderson
-/

namespace PlaneCurve
open PowerSeries

noncomputable def geom {R : Type*} [CommRing R] (a : R) : PowerSeries R :=
  PowerSeries.mk fun n => a^n

noncomputable def three {R : Type*} [CommRing R] (x y z : R) : PowerSeries R :=
  geom x * geom y * geom z

noncomputable def four {R : Type*} [CommRing R] (v x y z : R) : PowerSeries R :=
  geom v * three x y z

private lemma geom_eq {R : Type*} [CommRing R] (a : R) :
    geom a = 1 + PowerSeries.C a * geom a * PowerSeries.X := by
  ext n
  cases n with
  | zero => simp [geom]
  | succ n =>
    rw [map_add, coeff_one, if_neg (Nat.succ_ne_zero _), zero_add, coeff_succ_mul_X,
      coeff_C_mul]
    simp [geom, pow_succ, mul_comm]

private lemma geom_pair {R : Type*} [CommRing R] (a b : R) :
    geom a = geom b + C (a-b) * geom a * geom b * X := by
  rw [map_sub]
  linear_combination (geom b) * (geom_eq a) - (geom a) * (geom_eq b)

private lemma geom_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a : R) :
    PowerSeries.map f (geom a) = geom (f a) := by
  ext k
  simp [geom]

private lemma three_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x y z : R) :
    PowerSeries.map f (three x y z) = three (f x) (f y) (f z) := by
  simp [three, geom_map]

private lemma four_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (v x y z : R) :
    PowerSeries.map f (four v x y z) = four (f v) (f x) (f y) (f z) := by
  simp [four, geom_map, three_map]

private lemma convolution {R : Type*} [CommRing R] (f g : PowerSeries R) (k : ℕ) :
    coeff k (f*g) = ∑ i ∈ Finset.range (k+1), coeff i f * coeff (k-i) g := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

theorem three_explicit {R : Type*} [CommRing R] (x y z : R) (n : ℕ) :
    coeff n (three x y z) =
      ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n-a+1), x^a*y^b*z^(n-a-b) := by
  simp only [three, mul_assoc, convolution, geom, coeff_mk, Finset.mul_sum]

theorem three_equal {R : Type*} [Field R] [CharZero R] {a : R} (ha : a ≠ 0) (n : ℕ) :
    coeff n (three a a a) ≠ 0 := by
  rw [three_explicit]
  have h : (∑ i ∈ Finset.range (n+1), ∑ j ∈ Finset.range (n-i+1),
      a^i*a^j*a^(n-i-j)) =
      (∑ i ∈ Finset.range (n+1), (n-i+1 : ℕ) : ℕ) * (a^n) := by
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    calc
      _ = ∑ _j ∈ Finset.range (n-i+1), a^n := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' := Finset.mem_range.mp hj
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      _ = _ := by simp [nsmul_eq_mul]
  rw [h]
  apply mul_ne_zero _ (pow_ne_zero _ ha)
  have hn : 0 < ∑ i ∈ Finset.range (n+1), (n-i+1) :=
    Finset.sum_pos (fun i _ => Nat.succ_pos (n-i)) ⟨0, Finset.mem_range.mpr (by omega)⟩
  exact_mod_cast hn.ne'

end PlaneCurve

namespace PlaneCurve
open PowerSeries

private abbrev MR := MvPolynomial (Fin 3) ℂ

private noncomputable def partialSeries (i : Fin 3) (S : PowerSeries MR) : PowerSeries MR :=
  PowerSeries.mk fun n => MvPolynomial.pderiv i (coeff n S)

private lemma partial_mul (i : Fin 3) (S T : PowerSeries MR) :
    partialSeries i (S*T) = partialSeries i S*T+S*partialSeries i T := by
  ext n
  simp only [partialSeries, map_add, coeff_mk, convolution, map_sum, MvPolynomial.pderiv_mul,
    Finset.sum_add_distrib]

private lemma partial_geom (i j : Fin 3) :
    partialSeries i (geom (MvPolynomial.X j : MR)) =
      if j = i then (geom (MvPolynomial.X j : MR))^2*X else 0 := by
  ext n
  by_cases e : j = i
  · subst j
    cases n with
    | zero => simp [partialSeries, geom]
    | succ n =>
      rw [if_pos rfl, coeff_succ_mul_X, pow_two, convolution]
      simp only [partialSeries, geom, coeff_mk, MvPolynomial.pderiv_pow,
        MvPolynomial.pderiv_X_self, mul_one, Nat.add_sub_cancel]
      have eqn : (∑ k ∈ Finset.range (n+1), (MvPolynomial.X i : MR)^k * MvPolynomial.X i^(n-k)) =
          ∑ _k ∈ Finset.range (n+1), (MvPolynomial.X i : MR)^n := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
      rw [eqn]
      simp [nsmul_eq_mul]
  · simp [e, partialSeries, geom, MvPolynomial.pderiv_X_of_ne e]

private lemma partial_three (i : Fin 3) :
    partialSeries i (three (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)) =
      four (MvPolynomial.X i) (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) * X := by
  simp only [three, four, partial_mul, partial_geom]
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  fin_cases i <;> simp [h20,h21,h20.symm,h21.symm] <;> ring

private lemma gradient (i : Fin 3) (n : ℕ) :
    MvPolynomial.pderiv i (coeff (n+1) (three (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2))) =
      coeff n (four (MvPolynomial.X i : MR) (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)) := by
  have e := congrArg (coeff (n+1)) (partial_three i)
  simpa only [partialSeries, coeff_mk, coeff_succ_mul_X] using e

end PlaneCurve

namespace PlaneCurve
open PowerSeries

private lemma series_interpolation {R : Type*} [CommRing R] (T x y z : R) :
    geom T = geom x +
      (C (T-x) * (geom x*geom y)) * X +
      (C ((T-x)*(T-y)) * three x y z) * X^2 +
      (C ((T-x)*(T-y)*(T-z)) * four T x y z) * X^3 := by
  simp only [map_mul, three, four]
  linear_combination (geom_pair T x) + C (T-x)*geom x*X*(geom_pair T y) +
    C (T-x)*C (T-y)*geom x*geom y*X^2*(geom_pair T z)

private lemma interpolation {R : Type*} [CommRing R] (n : ℕ) (T x y z : R) :
    T^(n+3) = x^(n+3) + (T-x)*coeff (n+2) (geom x*geom y) +
      (T-x)*(T-y)*coeff (n+1) (three x y z) +
      (T-x)*(T-y)*(T-z)*coeff n (four T x y z) := by
  have e := congrArg (coeff (n+3)) (series_interpolation T x y z)
  simp only [map_add, coeff_succ_mul_X, show n+3=(n+1)+2 by omega, coeff_mul_X_pow,
    coeff_C_mul, geom, coeff_mk] at e
  rw [coeff_mul_X_pow _ 3 n, coeff_C_mul] at e
  exact e

private lemma tangent_values {R : Type*} [Field R] [CharZero R] (x : Fin 3 → R) (n : ℕ)
    (hz : coeff (n+1) (three (x 0) (x 1) (x 2)) = 0)
    (hd : ∀ i, coeff n (four (x i) (x 0) (x 1) (x 2)) = 0) :
    ∀ i, x i = x 0 := by
  let b := coeff (n+2) (geom (x 0)*geom (x 1))
  let A := (Polynomial.X - Polynomial.C (x 0)) * (Polynomial.X - Polynomial.C (x 1)) *
    (Polynomial.X - Polynomial.C (x 2))
  let Q := coeff n (four Polynomial.X (Polynomial.C (x 0)) (Polynomial.C (x 1))
    (Polynomial.C (x 2)))
  have hmap := fun (f : R →+* Polynomial R) => three_map f (x 0) (x 1) (x 2)
  have hb : Polynomial.C b = coeff (n+2) (geom (Polynomial.C (x 0))*geom (Polynomial.C (x 1))) := by
    rw [← geom_map Polynomial.C (x 0), ← geom_map Polynomial.C (x 1), ← map_mul, coeff_map]
  have hh : coeff (n+1) (three (Polynomial.C (x 0)) (Polynomial.C (x 1)) (Polynomial.C (x 2))) = 0 := by
    rw [← hmap Polynomial.C, coeff_map, hz, map_zero]
  have epi : Polynomial.X^(n+3) = Polynomial.C ((x 0)^(n+3)) +
      (Polynomial.X-Polynomial.C (x 0))*Polynomial.C b+A*Q := by
    have e := interpolation n Polynomial.X (Polynomial.C (x 0)) (Polynomial.C (x 1)) (Polynomial.C (x 2))
    rw [hh, mul_zero, add_zero, ← hb, ← map_pow] at e
    exact e
  have evA (i : Fin 3) : Polynomial.eval (x i) A = 0 := by fin_cases i <;> simp [A]
  have evQ (i : Fin 3) : Polynomial.eval (x i) Q = 0 := by
    change Polynomial.evalRingHom _ _ = 0
    rw [show Q = coeff n (four Polynomial.X (Polynomial.C (x 0)) (Polynomial.C (x 1))
      (Polynomial.C (x 2))) from rfl, ← coeff_map, four_map]
    simpa using hd i
  have vals (i : Fin 3) : (x i)^(n+3) = (x 0)^(n+3) + (x i-x 0)*b := by
    have e := congrArg (Polynomial.eval (x i)) epi
    simpa [evA, evQ] using e
  have ders (i : Fin 3) : ((n: R)+3)*(x i)^(n+2) = b := by
    have e := congrArg (fun p : Polynomial R => Polynomial.eval (x i) p.derivative) epi
    simp [Polynomial.derivative_mul, Polynomial.derivative_pow, evA, evQ, mul_comm] at e
    simpa [mul_comm] using e
  intro i
  have hc : (n:R)+3 ≠ 0 := by exact_mod_cast (show n+3 ≠ 0 by omega)
  have hdif : (x i)^(n+2) = (x 0)^(n+2) := mul_left_cancel₀ hc ((ders i).trans (ders 0).symm)
  by_cases hzero : x 0 = 0
  · simpa [hzero] using hdif
  · have hpow : (x 0)^(n+2) ≠ 0 := pow_ne_zero _ hzero
    have e := vals i
    rw [pow_succ (x i) (n+2), pow_succ (x 0) (n+2), hdif, ← ders 0] at e
    have hfactor : (((n:R)+2)*(x 0)^(n+2))*(x i-x 0) = 0 := by linear_combination -e
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left (mul_ne_zero
      (by exact_mod_cast (show n+2 ≠ 0 by omega)) hpow))
end PlaneCurve

namespace OMA.S_mo_341448
open MvPolynomial

private abbrev R := MvPolynomial (Fin 3) ℂ

private noncomputable def kill (k : ℕ) : R →ₐ[ℂ] R :=
  aeval (fun i : Fin 3 => if i.val < k then 0 else X i)

private noncomputable def coordinateIdeal (k : ℕ) : Ideal R :=
  RingHom.ker (kill k).toRingHom

private instance coord_prime (k : ℕ) : (coordinateIdeal k).IsPrime :=
  RingHom.ker_isPrime _

private theorem coord_lt (k : ℕ) (hk : k<3) : coordinateIdeal k < coordinateIdeal (k+1) := by
  have hcomp : (kill (k+1)).comp (kill k)=kill (k+1) := by
    ext i
    by_cases h : i.val < k
    · simp [kill,h,h.le]
    · simp [kill,h]
  apply lt_of_le_of_ne
  · intro f hf
    change kill k f=0 at hf
    change kill (k+1) f=0
    rw [← hcomp,AlgHom.comp_apply,hf,map_zero]
  · intro heq
    let i : Fin 3 := ⟨k,hk⟩
    have h1 : X i ∈ coordinateIdeal (k+1) := by
      change kill (k+1) (X i)=0
      simp [kill,i]
    rw [← heq] at h1
    change kill k (X i)=0 at h1
    simp [kill,i] at h1

private theorem coord_three : coordinateIdeal 3 = vanishingIdeal ℂ ({0} : Set (Fin 3 → ℂ)) := by
  have h : (Algebra.ofId ℂ R).comp (aeval (0 : Fin 3 → ℂ)) = kill 3 := by
    ext i
    simp [kill]
  ext f
  rw [mem_vanishingIdeal_singleton_iff]
  change kill 3 f=0 ↔ _
  rw [← h,AlgHom.comp_apply]
  exact (map_eq_zero_iff _ (algebraMap ℂ R).injective)

theorem common_nonzero_zero {f g : MvPolynomial (Fin 3) ℂ}
    (hf : aeval (0 : Fin 3 → ℂ) f=0) (hg : aeval (0 : Fin 3 → ℂ) g=0) :
    ∃ x : Fin 3 → ℂ, x ≠ 0 ∧ aeval x f=0 ∧ aeval x g=0 := by
  classical
  let s : Finset R := {f,g}
  let I := Ideal.span (s : Set R)
  by_contra! hn
  have hz : zeroLocus ℂ I = ({0} : Set (Fin 3 → ℂ)) := by
    ext x
    rw [show I=Ideal.span (s : Set R) from rfl,zeroLocus_span]
    simp only [s,Finset.coe_insert,Finset.coe_singleton, Set.mem_ofPred_eq,
      Set.mem_insert_iff,Set.mem_singleton_iff]
    constructor
    · intro hx
      by_contra h
      exact hn x h (hx f (Or.inl rfl)) (hx g (Or.inr rfl))
    · rintro rfl
      rintro _ (rfl|rfl) <;> assumption
  have hrad : I.radical=coordinateIdeal 3 := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := ℂ),hz,coord_three]
  have hmin : coordinateIdeal 3 ∈ I.minimalPrimes := by
    rw [← Ideal.radical_minimalPrimes,hrad,Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  have hu := Ideal.height_le_card_of_mem_minimalPrimes_span_finset (s := s) hmin
  have hc : s.card ≤ 2 := by dsimp [s]; exact (Finset.card_insert_le _ _).trans (by simp)
  have h01 := Ideal.height_add_one_le_of_lt_of_isPrime (coord_lt 0 (by decide))
  have h12 := Ideal.height_add_one_le_of_lt_of_isPrime (coord_lt 1 (by decide))
  have h23 := Ideal.height_add_one_le_of_lt_of_isPrime (coord_lt 2 (by decide))
  have hh : (3:ℕ∞) ≤ (coordinateIdeal 3).height := by
    calc
      (3:ℕ∞) = 0+1+1+1 := by norm_num
      _ ≤ (coordinateIdeal 0).height+1+1+1 := by gcongr; exact bot_le
      _ ≤ (coordinateIdeal 1).height+1+1 := by gcongr
      _ ≤ (coordinateIdeal 2).height+1 := by gcongr
      _ ≤ _ := h23
  have h := hh.trans (hu.trans (Nat.cast_le.mpr hc))
  norm_num at h

end OMA.S_mo_341448



namespace OMA.S_mo_341448
open MvPolynomial

private abbrev P := MvPolynomial (Fin 3) ℂ

private noncomputable def ray (x : Fin 3 → ℂ) : P →ₐ[ℂ] Polynomial ℂ :=
  aeval (fun i => Polynomial.C (x i) * Polynomial.X)

private lemma eval_ray (x : Fin 3 → ℂ) (t : ℂ) (F : P) :
    (ray x F).eval t=aeval (fun i => x i*t) F := by
  have h : (Polynomial.aeval t).comp (ray x)=aeval (fun i => x i*t) := by
    ext1 i
    simp [ray]
  exact DFunLike.congr_fun h F

private lemma ray_homogeneous (x : Fin 3 → ℂ) {F : P} {n : ℕ} (hf : F.IsHomogeneous n) :
    ray x F = Polynomial.C (aeval x F)*Polynomial.X^n := by
  classical
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  rw [map_sum,map_sum,map_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg := hf.degree_eq_sum_deg_support hd
  simp only [ray,aeval_monomial,Algebra.algebraMap_self_apply,Finsupp.prod,
    mul_pow,Finset.prod_mul_distrib,← map_pow,← map_prod,Finset.prod_pow_eq_pow_sum]
  rw [hdeg]
  simp [Polynomial.algebraMap_eq]; ring

theorem homogeneous_vanish_at_origin {F : MvPolynomial (Fin 3) ℂ} {n : ℕ}
    (h : F.IsHomogeneous n) (hn : 0 < n) : aeval (0 : Fin 3 → ℂ) F=0 := by
  have e := eval_ray (0 : Fin 3 → ℂ) 0 F
  rw [ray_homogeneous _ h] at e
  simpa [hn.ne'] using e.symm

theorem projective_plane_curves_intersect {f g : MvPolynomial (Fin 3) ℂ} {m n : ℕ}
    (hf : f.IsHomogeneous m) (hg : g.IsHomogeneous n) (hm : 0 < m) (hn : 0 < n) :
    ∃ x : Fin 3 → ℂ, x ≠ 0 ∧ aeval x f=0 ∧ aeval x g=0 :=
  common_nonzero_zero (homogeneous_vanish_at_origin hf hm) (homogeneous_vanish_at_origin hg hn)

private lemma nonunit_has_root {a : P} (ha : ¬IsUnit a) :
    ∃ x : Fin 3 → ℂ, aeval x a=0 := by
  have hI : Ideal.span ({a} : Set P) ≠ ⊤ := by rwa [ne_eq,Ideal.span_singleton_eq_top]
  obtain ⟨M,hM,hle⟩ := Ideal.exists_le_maximal _ hI
  obtain ⟨x,hx⟩ := eq_vanishingIdeal_singleton_of_isMaximal ℂ hM
  refine ⟨x,(mem_vanishingIdeal_singleton_iff x a).mp ?_⟩
  rw [← hx]
  exact hle (Ideal.subset_span rfl)

private lemma crossing_of_nonzero_constant {F a b : P} {n : ℕ} (hf : F.IsHomogeneous n)
    (he : F=a*b) (ha : ¬IsUnit a) (h0 : aeval (0 : Fin 3 → ℂ) a ≠ 0) :
    ∃ x : Fin 3 → ℂ, x ≠ 0 ∧ aeval x a=0 ∧ aeval x b=0 := by
  obtain ⟨x,hx⟩ := nonunit_has_root ha
  have hA : ray x a ≠ 0 := by
    intro h
    have hh := eval_ray x 0 a
    simp [h] at hh
    exact h0 (by simpa using hh.symm)
  have hF : ray x F=0 := by
    rw [ray_homogeneous x hf,he,map_mul,hx]; simp
  rw [he,map_mul] at hF
  have hB := (mul_eq_zero.mp hF).resolve_left hA
  have hh := eval_ray x 1 b
  simp [hB] at hh
  exact ⟨x,fun e => h0 (e ▸ hx),hx,hh.symm⟩

theorem irreducible_of_projective_smooth {F : MvPolynomial (Fin 3) ℂ} {n : ℕ}
    (hn : 0 < n) (hF : F ≠ 0) (hf : F.IsHomogeneous n)
    (hs : ∀ x : Fin 3 → ℂ, x ≠ 0 → aeval x F=0 →
      ∃ i : Fin 3, aeval x (pderiv i F) ≠ 0) : Irreducible F := by
  refine ⟨fun h => ?_,fun {a b} hab => ?_⟩
  · have hh := (isUnit_iff_totalDegree_of_isReduced.mp h).2
    rw [hf.totalDegree hF] at hh
    omega
  · by_contra! h
    have hcross : ∃ x : Fin 3 → ℂ, x ≠ 0 ∧ aeval x a=0 ∧ aeval x b=0 := by
      by_cases ha : aeval (0 : Fin 3 → ℂ) a=0
      · by_cases hb : aeval (0 : Fin 3 → ℂ) b=0
        · exact common_nonzero_zero ha hb
        · obtain ⟨x,hx,hb',ha'⟩ := crossing_of_nonzero_constant hf (hab.trans (mul_comm _ _)) h.2 hb
          exact ⟨x,hx,ha',hb'⟩
      · exact crossing_of_nonzero_constant hf hab h.1 ha
    obtain ⟨x,hx,ha,hb⟩ := hcross
    obtain ⟨i,hi⟩ := hs x hx (by rw [hab,map_mul,ha,zero_mul])
    exact hi (by rw [hab,pderiv_mul,map_add,map_mul,map_mul,ha,hb]; ring)

end OMA.S_mo_341448

namespace OMA.S_mo_341448
noncomputable section
open MvPolynomial

def triangularHom (n : ℕ) : MvPolynomial (Fin 3) ℂ :=
  ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n-a+1),
    X 0 ^ a * X 1 ^ b * X 2 ^ (n-a-b)

private def homogenizeTo (p : MvPolynomial (Fin 2) ℤ) (d : ℕ) : MvPolynomial (Fin 3) ℂ :=
  ∑ e ∈ p.support, C ((Int.castRingHom ℂ) (p.coeff e)) * X 0 ^ e 0 * X 1 ^ e 1 * X 2 ^ (d-(e 0+e 1))

private lemma clear_two (u v z c : ℂ) (hz : z ≠ 0) {a b d : ℕ} (h : a+b ≤ d) :
    c*u^a*v^b*z^(d-(a+b)) = z^d*(c*((u/z)^a*(v/z)^b)) := by
  rw [div_pow,div_pow]
  nth_rw 2 [show d = (d-(a+b))+(a+b) by omega]
  rw [pow_add,pow_add]
  field_simp

private lemma eval_homogenizeTo (p : MvPolynomial (Fin 2) ℤ) (d : ℕ) (hd : p.totalDegree ≤ d)
    (x : Fin 3 → ℂ) (hz : x 2 ≠ 0) :
    eval x (homogenizeTo p d) =
      x 2 ^ d * p.eval₂ (Int.castRingHom ℂ) ![x 0 / x 2,x 1 / x 2] := by
  classical
  rw [eval₂_eq',Finset.mul_sum]
  simp only [homogenizeTo,map_sum,map_mul,map_pow,eval_C,eval_X]
  apply Finset.sum_congr rfl
  intro e he
  have hb := (le_totalDegree he).trans hd
  rw [e.sum_fintype (fun _ t => t) (fun _ => rfl), Fin.sum_univ_two] at hb
  simpa [Fin.prod_univ_two] using clear_two (x 0) (x 1) (x 2) ((Int.castRingHom ℂ) (p.coeff e)) hz hb

private lemma eval_triangularHom (n : ℕ) (x : Fin 3 → ℂ) (hz : x 2 ≠ 0) :
    eval x (triangularHom n) =
      x 2 ^ n * (triangular n).eval₂ (Int.castRingHom ℂ) ![x 0 / x 2,x 1 / x 2] := by
  classical
  simp only [triangularHom,triangular,map_sum,map_mul,map_pow,eval_X,eval₂_sum,eval₂_mul,
    eval₂_pow,eval₂_X,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [Finset.mem_range] at ha hb
  simpa [Nat.sub_sub,one_mul] using clear_two (x 0) (x 1) (x 2) 1 hz (show a+b≤n by omega)

private theorem triangular_degree_le (n : ℕ) : (triangular n).totalDegree ≤ n := by
  apply totalDegree_finsetSum_le
  intro a ha
  apply totalDegree_finsetSum_le
  intro b hb
  refine (totalDegree_mul _ _).trans ?_
  simp only [totalDegree_X_pow]
  simp only [Finset.mem_range] at ha hb
  omega

private theorem triangular_constant (n : ℕ) : constantCoeff (triangular n) = 1 := by
  classical
  simp [triangular, zero_pow_eq, mul_ite, Finset.sum_ite_eq']

private theorem triangular_eval_one_zero (n : ℕ) : eval ![(1 : ℤ),0] (triangular n) = (n+1 : ℕ) := by
  classical
  simp [triangular, zero_pow_eq, Finset.sum_ite_eq']

private lemma unit_factor_of_homogenize (p : MvPolynomial (Fin 2) ℤ) (d : ℕ) (hd : p.totalDegree≤d)
    (hc : IsUnit (constantCoeff p)) (hu : IsUnit (homogenizeTo p d)) : IsUnit p := by
  classical
  obtain ⟨r,_,he⟩ := isUnit_iff_eq_C_of_isReduced.mp hu
  have hp : map (Int.castRingHom ℂ) p = C r := by
    apply MvPolynomial.funext
    intro v
    have hv := eval_homogenizeTo p d ![v 0,v 1,1] (hd := hd) (by simp)
    rw [he,eval_C] at hv
    rw [← eval₂_eq_eval_map, eval_C]
    have eta : ![v 0,v 1] = v := by funext i; fin_cases i <;> rfl
    simpa [eta] using hv.symm
  have hdeg : (map (Int.castRingHom ℂ) p).totalDegree = 0 := by rw [hp,totalDegree_C]
  have hsame : (map (Int.castRingHom ℂ) p).totalDegree = p.totalDegree := by
    simp only [totalDegree,support_map_of_injective p (f := Int.castRingHom ℂ) (Int.cast_injective (α:=ℂ))]
  exact isUnit_iff_totalDegree_of_isReduced.mpr ⟨hc,hsame ▸ hdeg⟩

theorem irreducible_triangular_of_hom (n : ℕ) (hn : 0<n) (hh : Irreducible (triangularHom n)) :
    Irreducible (triangular n) := by
  classical
  constructor
  · intro hu
    have h := hu.map (eval ![(1:ℤ),0])
    rw [triangular_eval_one_zero,Int.isUnit_iff] at h
    omega
  · intro p q h
    have hc : constantCoeff p * constantCoeff q = 1 := by
      rw [← map_mul,← h,triangular_constant]
    have hp0 : p ≠ 0 := fun hz => by simp [hz] at hc
    have hq0 : q ≠ 0 := fun hz => by simp [hz] at hc
    have hsum : p.totalDegree + q.totalDegree ≤ n := by
      rw [← totalDegree_mul_of_isDomain hp0 hq0,← h]
      exact triangular_degree_le n
    let d := p.totalDegree
    let e := n-d
    have ep : q.totalDegree ≤ e := by dsimp [d,e]; omega
    have de : d+e=n := by dsimp [d,e]; omega
    have hf : triangularHom n = homogenizeTo p d * homogenizeTo q e := by
      apply MvPolynomial.funext_set (fun _ => ({0} : Set ℂ)ᶜ)
        (fun _ => (Set.finite_singleton _).infinite_compl)
      intro x hx
      have hz : x 2 ≠ 0 := hx 2 (Set.mem_univ _)
      rw [map_mul,eval_homogenizeTo p d le_rfl x hz,eval_homogenizeTo q e ep x hz,
        eval_triangularHom n x hz,h,eval₂_mul]
      rw [← de,pow_add]
      ring
    have hu : IsUnit (constantCoeff p * constantCoeff q) := hc.symm ▸ isUnit_one
    have fac := hh.isUnit_or_isUnit hf
    rcases fac with unit | unit
    · exact Or.inl (unit_factor_of_homogenize p d le_rfl (isUnit_of_mul_isUnit_left hu) unit)
    · exact Or.inr (unit_factor_of_homogenize q e ep (isUnit_of_mul_isUnit_right hu) unit)

end
end OMA.S_mo_341448

namespace OMA.S_mo_341448

open PlaneCurve MvPolynomial

private lemma hom_series (n : ℕ) : triangularHom n =
    PowerSeries.coeff n (three (X 0) (X 1) (X 2)) :=
  (three_explicit _ _ _ n).symm

private lemma hom_evaluated (x : Fin 3 → ℂ) (n : ℕ) :
    aeval x (triangularHom n) = PowerSeries.coeff n (three (x 0) (x 1) (x 2)) := by
  rw [hom_series]
  change (aeval x).toRingHom _ = _
  rw [← PowerSeries.coeff_map, three_map]
  simp

private lemma deriv_evaluated (x : Fin 3 → ℂ) (i : Fin 3) (n : ℕ) :
    aeval x (pderiv i (triangularHom (n+1))) =
      PowerSeries.coeff n (four (x i) (x 0) (x 1) (x 2)) := by
  rw [hom_series, gradient]
  change (aeval x).toRingHom _ = _
  rw [← PowerSeries.coeff_map, four_map]
  simp

private lemma hom_smooth (n : ℕ) (hn : 0 < n) (x : Fin 3 → ℂ) (hx : x ≠ 0)
    (hz : aeval x (triangularHom n) = 0) :
    ∃ i : Fin 3, aeval x (pderiv i (triangularHom n)) ≠ 0 := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  by_contra! hg
  rw [hom_evaluated] at hz
  have hd (i) := (deriv_evaluated x i m).symm.trans (hg i)
  have h := tangent_values x m hz hd
  have hx0 : x 0 ≠ 0 := fun e => hx (funext fun i => (h i).trans e)
  exact three_equal hx0 (m+1) (by simpa only [h 1,h 2] using hz)

private lemma hom_nonzero (n : ℕ) : triangularHom n ≠ 0 := by
  intro hz
  have e := hom_evaluated (fun _ => 1) n
  rw [hz,map_zero] at e
  exact three_equal one_ne_zero n e.symm

private lemma hom_homogeneous (n : ℕ) : (triangularHom n).IsHomogeneous n := by
  classical
  unfold triangularHom
  apply IsHomogeneous.sum
  intro a ha
  apply IsHomogeneous.sum
  intro b hb
  simp only [Finset.mem_range] at ha hb
  have h := ((isHomogeneous_X_pow (R := ℂ) (0 : Fin 3) a).mul
    (isHomogeneous_X_pow 1 b)).mul (isHomogeneous_X_pow 2 (n-a-b))
  rwa [show a+b+(n-a-b)=n by omega] at h

end OMA.S_mo_341448

theorem OMA.solution : type_of% @OMA.S_mo_341448.main := by
  intro n hn
  apply OMA.S_mo_341448.irreducible_triangular_of_hom n hn
  exact OMA.S_mo_341448.irreducible_of_projective_smooth hn (OMA.S_mo_341448.hom_nonzero n)
    (OMA.S_mo_341448.hom_homogeneous n) (OMA.S_mo_341448.hom_smooth n hn)

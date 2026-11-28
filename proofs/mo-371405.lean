import OMAStatements.S_mo_371405

/-!
# Irreducibility of the palindromic polynomial for every positive index

Max Alekseyev observed the squared-geometric-sum presentation on MathOverflow.
Sil suggested reduction to a trace polynomial by a criterion of Cafure and
Cesaratto, Irreducibility criteria for reciprocal polynomials and applications,
Theorem 11. The proof below supplies the irreducibility of that trace polynomial.

For a monic integer polynomial f with distinct real roots, factor f + √(-2)
over the norm-Euclidean quadratic integers. At every root of f, the product
of the imaginary coefficients of the two factors has absolute value less
than one. All its conjugates satisfy the same bound, so the product vanishes.
The degree bound forces one imaginary coefficient to vanish identically.
This proves f² + 2 irreducible. The rescaled Chebyshev polynomial of the
second kind supplies f for the trace of the original palindromic polynomial.

Credit: @connoranderson
-/

section

namespace OMA.S_mo_371405

open Polynomial

abbrev TraceRing := QuadraticAlgebra ℤ[X] (-1) X

noncomputable def evalOmega : ℤ[X] →+* TraceRing :=
  eval₂RingHom (Int.castRingHom TraceRing) QuadraticAlgebra.omega

end OMA.S_mo_371405
end

section

namespace OMA.S_mo_371405
open Polynomial
open scoped QuadraticAlgebra

noncomputable def traceSpecialize {R : Type*} [CommRing R] (y u : R)
    (hu : u*u = -1+y*u) : TraceRing →+* R := by
  let e : ℤ[X] →+* R := eval₂RingHom (Int.castRingHom R) y
  have hex : e X = y := by simp [e]
  exact {
    toFun := fun a => e a.re + e a.im * u
    map_zero' := by simp
    map_one' := by simp
    map_add' := by intro a b; simp; ring
    map_mul' := by
      intro a b
      simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, map_add, map_mul, map_neg,
        map_one, hex]
      linear_combination -(e a.im * e b.im) * hu }

theorem traceSpecialize_evalOmega {R : Type*} [CommRing R] (y u : R)
    (hu : u*u = -1+y*u) (g : ℤ[X]) :
    traceSpecialize y u hu (evalOmega g) = g.eval₂ (Int.castRingHom R) u := by
  change (traceSpecialize y u hu |>.comp evalOmega) g = (eval₂RingHom _ u) g
  apply RingHom.congr_fun _ g
  apply Polynomial.ringHom_ext
  · intro a
    simp [evalOmega,traceSpecialize]
  · simp [evalOmega,traceSpecialize]

private theorem traceNorm_minus_two (g : ℤ[X]) :
    ((evalOmega g).norm).eval (-2) = g.eval (-1) ^ 2 := by
  have h := traceSpecialize_evalOmega (-2 : ℤ) (-1) (by norm_num) g
  change (evalOmega g).re.eval (-2) + (evalOmega g).im.eval (-2) * (-1) = _ at h
  have h' : (evalOmega g).re.eval (-2) - (evalOmega g).im.eval (-2) = g.eval (-1) := by
    simpa [sub_eq_add_neg] using h
  rw [← h', QuadraticAlgebra.norm_def]
  simp
  ring

private theorem of_norm_unit {g : ℤ[X]} (hg0 : IsUnit (g.coeff 0)) (hn : IsUnit (evalOmega g).norm) :
    IsUnit g := by
  by_cases hd : g.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero hd]
    exact isUnit_C.mpr hg0
  have hu : IsUnit (evalOmega g) := by
    have hm := hn.map (algebraMap ℤ[X] TraceRing)
    rw [QuadraticAlgebra.algebraMap_norm_eq_mul_star] at hm
    exact isUnit_of_mul_isUnit_left hm
  let e : ℤ →+* ℂ := Int.castRingHom ℂ
  have hei : Function.Injective e := Int.cast_injective
  have hdeg : (g.map e).degree ≠ 0 := by
    rw [degree_map_eq_of_injective hei]
    exact (natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hd)).ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (g.map e) hdeg
  have hz0 : z ≠ 0 := by
    rintro rfl
    have hc : e (g.coeff 0) = 0 := by simpa [Polynomial.IsRoot, coeff_zero_eq_eval_zero] using hz
    exact hg0.ne_zero (hei (by simpa using hc))
  have heq : z*z = -1 + (z+z⁻¹)*z := by field_simp; ring
  have hzero : g.eval₂ e z = 0 := by simpa [Polynomial.IsRoot, eval_map] using hz
  have hsp := hu.map (traceSpecialize (z+z⁻¹) z heq)
  rw [traceSpecialize_evalOmega] at hsp
  exact (hsp.ne_zero hzero).elim

private theorem norm_ne_associate {q g v : ℤ[X]} (hv : IsUnit v)
    (hsq : ¬ IsSquare (q.eval (-2)).natAbs) :
    (evalOmega g).norm ≠ q * v := by
  intro hz
  have he := congrArg (fun w : ℤ[X] => (w.eval (-2)).natAbs) hz
  have hv' := Int.isUnit_iff_natAbs_eq.mp (hv.map (evalRingHom (-2 : ℤ)))
  simp only [traceNorm_minus_two, eval_mul, Int.natAbs_mul, Int.natAbs_pow] at he
  change (v.eval (-2)).natAbs = 1 at hv'
  rw [hv', mul_one] at he
  exact hsq ⟨(g.eval (-1)).natAbs, by rw [← he, pow_two]⟩

private theorem norm_factor {q g h : ℤ[X]} (hq : Irreducible q)
    (hsq : ¬ IsSquare (q.eval (-2)).natAbs)
    (hp : (evalOmega g).norm * (evalOmega h).norm = q^2)
    (hg : q ∣ (evalOmega g).norm) : IsUnit (evalOmega h).norm := by
  obtain ⟨v, hv⟩ := hg
  have he : q = v * (evalOmega h).norm := by
    apply mul_left_cancel₀ hq.ne_zero
    rw [← mul_assoc, ← hv, hp, pow_two]
  exact (hq.isUnit_or_isUnit he).resolve_left (fun hu => norm_ne_associate hu hsq hv)

theorem irreducible_of_trace {f q : ℤ[X]} {n : ℕ} (hf0 : f.coeff 0 = 1)
    (hq : Irreducible q) (hsq : ¬ IsSquare (q.eval (-2)).natAbs)
    (htrace : evalOmega f = (QuadraticAlgebra.omega : TraceRing)^n * algebraMap ℤ[X] TraceRing q) :
    Irreducible f := by
  have hnorm : (evalOmega f).norm = q^2 := by
    rw [htrace, map_mul, map_pow, QuadraticAlgebra.norm_algebraMap]
    simp [QuadraticAlgebra.norm_def]
  constructor
  · intro hf
    have hu := (hf.map evalOmega).map QuadraticAlgebra.norm
    rw [hnorm] at hu
    rw [pow_two] at hu
    exact hq.not_isUnit (isUnit_of_mul_isUnit_left hu)
  · intro g h hgh
    have hprod : (evalOmega g).norm * (evalOmega h).norm = q^2 := by
      simpa only [hgh, map_mul] using hnorm
    have hc : IsUnit (g.coeff 0 * h.coeff 0) := by
      rw [← mul_coeff_zero, ← hgh, hf0]
      exact isUnit_one
    have hd : q ∣ (evalOmega g).norm * (evalOmega h).norm := by
      rw [hprod, pow_two]
      exact dvd_mul_right _ _
    rcases hq.prime.dvd_mul.mp hd with hg | hh
    · exact Or.inr (of_norm_unit (isUnit_of_mul_isUnit_right hc) (norm_factor hq hsq hprod hg))
    · rw [mul_comm] at hprod
      exact Or.inl (of_norm_unit (isUnit_of_mul_isUnit_left hc) (norm_factor hq hsq hprod hh))

end OMA.S_mo_371405
end

section

namespace OMA.S_mo_371405
open Polynomial

theorem natAbs_trace_neg_two {f q : ℤ[X]} {n : ℕ}
    (htrace : evalOmega f = (QuadraticAlgebra.omega : TraceRing)^n * algebraMap ℤ[X] TraceRing q) :
    (q.eval (-2)).natAbs = (f.eval (-1)).natAbs := by
  let sp := traceSpecialize (-2 : ℤ) (-1) (by norm_num)
  have he := congrArg sp htrace
  have hs : sp (evalOmega f) = f.eval (-1) := traceSpecialize_evalOmega _ _ _ _
  have hw : sp QuadraticAlgebra.omega = -1 := by simp [sp, traceSpecialize]
  have hq : sp (algebraMap ℤ[X] TraceRing q) = q.eval (-2) := by simp [sp, traceSpecialize]
  rw [hs, map_mul, map_pow, hw, hq] at he
  simp [he, Int.natAbs_mul]

theorem nonsquare_palindromic_trace {q : ℤ[X]} {n : ℕ}
    (htrace : evalOmega (palindromic n) =
      (QuadraticAlgebra.omega : TraceRing)^n * algebraMap ℤ[X] TraceRing q) :
    ¬ IsSquare (q.eval (-2)).natAbs := by
  rw [natAbs_trace_neg_two htrace]
  have hea : (geometric n).eval (-1) = if Even (n+1) then 0 else 1 := by
    simp [geometric, neg_one_geom_sum]
  by_cases h : Even n
  · simp [palindromic, hea, Nat.even_add_one, h, h.neg_one_pow]
    rintro ⟨k,hk⟩
    have hk' : k ≤ 1 := by
      by_contra! hgt
      nlinarith [Nat.mul_self_le_mul_self (show 2 ≤ k by omega)]
    interval_cases k <;> norm_num at hk
  · have ho := Nat.not_even_iff_odd.mp h
    simp [palindromic, hea, Nat.even_add_one, h, ho.neg_one_pow]
    rintro ⟨k,hk⟩
    have hk' : k ≤ 1 := by
      by_contra! hgt
      nlinarith [Nat.mul_self_le_mul_self (show 2 ≤ k by omega)]
    interval_cases k <;> norm_num at hk

theorem palindromic_irreducible_of_trace {q : ℤ[X]} {n : ℕ} (hn : 0 < n) (hq : Irreducible q)
    (htrace : evalOmega (palindromic n) =
      (QuadraticAlgebra.omega : TraceRing)^n * algebraMap ℤ[X] TraceRing q) : Irreducible (palindromic n) := by
  apply irreducible_of_trace _ hq (nonsquare_palindromic_trace htrace) htrace
  simp [coeff_zero_eq_eval_zero,geometric,palindromic,hn.ne']


end OMA.S_mo_371405
end

section

/-! Norm descent for ℤ[√−2]. The Euclidean-domain construction rounds both
coordinates in the basis (1, √−2), following the construction for Gaussian
integers in Mathlib.NumberTheory.Zsqrtd.GaussianInt (Chris Hughes, Apache 2.0).
A real polynomial divisible by f+√−2 is divisible by f²+2, by comparing
its two integral coordinates. -/

namespace OMA.S_mo_371405.Descent
open Polynomial Zsqrtd

abbrev S := Zsqrtd (-2)

private noncomputable def quot (x y : S) : S :=
  ⟨round ((x * star y).re / (y.norm : ℚ)), round ((x * star y).im / (y.norm : ℚ))⟩

private lemma roundBound (a d : ℤ) (hd : 0 < d) :
    4 * (a - d * round (a / (d : ℚ))) ^ 2 ≤ d ^ 2 := by
  let q : ℚ := a / (d : ℚ)
  have hr := abs_sub_round q
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  have h : |(a : ℚ) - d * round q| ≤ (d : ℚ)/2 := by
    have he : (a : ℚ) - d * round q = (q - round q) * d := by
      dsimp [q]
      field_simp
    rw [he, abs_mul, abs_of_pos hd']
    nlinarith [mul_le_mul_of_nonneg_right hr hd'.le]
  have h' : ((a : ℚ) - d * round q)^2 ≤ ((d : ℚ)/2)^2 := by
    apply sq_le_sq.mpr
    rw [abs_of_nonneg (by positivity : (0 : ℚ) ≤ d/2)]
    exact h
  change 4 * (a - d * round q)^2 ≤ d^2
  generalize round q = t at *
  exact_mod_cast (show 4 * ((a : ℚ) - d * t)^2 ≤ (d : ℚ)^2 by linarith)

private lemma norm_pos {x : S} (hx : x ≠ 0) : 0 < x.norm :=
  lt_of_le_of_ne (Zsqrtd.norm_nonneg (by decide) x) (Ne.symm (mt (Zsqrtd.norm_eq_zero_iff (by decide) x).mp hx))

private lemma remainder_lt (x y : S) (hy : y ≠ 0) :
    (x - y * quot x y).norm.natAbs < y.norm.natAbs := by
  have hy' := norm_pos hy
  let v := x * star y
  let q := quot x y
  have h1 := roundBound v.re y.norm hy'
  have h2 := roundBound v.im y.norm hy'
  have hmul : (x - y * q) * star y = v - (y.norm : S) * q := by
    rw [norm_eq_mul_conj]
    dsimp [v]
    ring
  have hnorm := congrArg Zsqrtd.norm hmul
  rw [norm_mul, norm_conj] at hnorm
  have hh : (v - (y.norm : S) * q).norm < y.norm ^ 2 := by
    rw [Zsqrtd.norm_def (v - (y.norm : S) * q)]
    simp only [sub_eq_add_neg, re_add, im_add, re_neg, im_neg, re_mul, im_mul,
      re_intCast, im_intCast, zero_mul, mul_zero, add_zero] 
    change (v.re + -(y.norm * round ((v.re : ℚ) / y.norm))) * _ + _ < y.norm ^ 2
    dsimp only [q, quot] 
    change 4 * (v.re - y.norm * round ((v.re : ℚ) / y.norm)) ^ 2 ≤ y.norm ^ 2 at h1
    change 4 * (v.im - y.norm * round ((v.im : ℚ) / y.norm)) ^ 2 ≤ y.norm ^ 2 at h2
    nlinarith [sq_pos_of_pos hy']
  have hh' : (x - y * q).norm < y.norm := by
    rw [← hnorm] at hh
    rw [pow_two] at hh
    exact lt_of_mul_lt_mul_right hh hy'.le
  apply Int.ofNat_lt.mp
  rw [Int.natAbs_of_nonneg (Zsqrtd.norm_nonneg (show (-2:ℤ) ≤ 0 by decide) _),
    Int.natAbs_of_nonneg (Zsqrtd.norm_nonneg (show (-2:ℤ) ≤ 0 by decide) _)]
  exact hh' 

noncomputable abbrev euclidean : EuclideanDomain S :=
  { Zsqrtd.commRing, Zsqrtd.nontrivial with
    quotient := quot
    quotient_zero := by intro a; simp [quot]; rfl
    remainder := fun a b => a - b * quot a b
    quotient_mul_add_remainder_eq := by intros; ring
    r := fun a b => a.norm.natAbs < b.norm.natAbs
    r_wellFounded := (measure (Int.natAbs ∘ Zsqrtd.norm)).wf
    remainder_lt := remainder_lt
    mul_left_not_lt := by
      intro a b hb
      have hh : 1 ≤ b.norm.natAbs := Nat.one_le_iff_ne_zero.mpr
        (by simpa using (norm_pos hb).ne')
      simpa [Function.comp_apply, Zsqrtd.norm_mul, Int.natAbs_mul] using
        not_lt_of_ge (Nat.le_mul_of_pos_right a.norm.natAbs hh) }


abbrev rad : S := Zsqrtd.sqrtd

noncomputable def pack (A B : ℤ[X]) : S[X] :=
  A.map (Int.castRingHom S) + C rad * B.map (Int.castRingHom S)

private lemma coeff_pack (A B : ℤ[X]) (k : ℕ) :
    (pack A B).coeff k = ⟨A.coeff k, B.coeff k⟩ := by
  ext <;> simp [pack, coeff_C_mul, rad]

theorem pack_injective {A B C D : ℤ[X]} (h : pack A B = pack C D) : A = C ∧ B = D := by
  constructor
  · ext k
    simpa only [coeff_pack] using congrArg (fun p : S[X] => (p.coeff k).re) h
  · ext k
    simpa only [coeff_pack] using congrArg (fun p : S[X] => (p.coeff k).im) h

private lemma rad_sq : rad^2 = -2 := by
  apply Zsqrtd.ext <;> norm_num [rad, pow_two]

theorem pack_mul (A B C D : ℤ[X]) :
    pack A B * pack C D = pack (A*C-2*B*D) (A*D+B*C) := by
  have h : (Polynomial.C rad)^2 = (-2 : S[X]) := by rw [← map_pow, rad_sq, map_neg, Polynomial.C_ofNat]
  simp only [pack, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_ofNat]
  linear_combination B.map (Int.castRingHom S) * D.map (Int.castRingHom S) * h

noncomputable def realPart (p : S[X]) : ℤ[X] :=
  ⟨.ofCoeff (p.toFinsupp.coeff.mapRange Zsqrtd.re rfl)⟩

noncomputable def imagPart (p : S[X]) : ℤ[X] :=
  ⟨.ofCoeff (p.toFinsupp.coeff.mapRange Zsqrtd.im rfl)⟩

theorem repack (p : S[X]) : pack (realPart p) (imagPart p) = p := by
  apply Polynomial.ext
  intro k
  rw [coeff_pack]
  rfl

theorem imag_degree_lt {p : S[X]} (hp : p.Monic) (hpd : 0 < p.natDegree) :
    (imagPart p).natDegree < p.natDegree := by
  by_contra! h
  have hz : (imagPart p).coeff (imagPart p).natDegree = 0 := by
    change (p.coeff (imagPart p).natDegree).im = 0
    rcases h.eq_or_lt with he|hg
    · rw [← he, hp.coeff_natDegree, im_one]
    · rw [coeff_eq_zero_of_natDegree_lt hg, im_zero]
  have he := leadingCoeff_eq_zero.mp hz
  simp [he] at h
  omega

theorem real_degree {p : S[X]} (hp : p.Monic) : (realPart p).natDegree = p.natDegree := by
  apply _root_.le_antisymm
  · by_contra! h
    have hz : (realPart p).coeff (realPart p).natDegree = 0 := by
      change (p.coeff (realPart p).natDegree).re = 0
      rw [coeff_eq_zero_of_natDegree_lt h, re_zero]
    have he := leadingCoeff_eq_zero.mp hz
    simp [he] at h
  · apply le_natDegree_of_ne_zero
    change (p.coeff p.natDegree).re ≠ 0
    rw [hp.coeff_natDegree, re_one]
    decide

theorem real_monic {p : S[X]} (hp : p.Monic) : (realPart p).Monic := by
  change (p.coeff (realPart p).natDegree).re = 1
  rw [real_degree hp, hp.coeff_natDegree, re_one]

private lemma pack_zero (a : ℤ[X]) : pack a 0 = a.map (Int.castRingHom S) := by
  simp [pack]

private lemma pack_one (a : ℤ[X]) : pack a 1 = a.map (Int.castRingHom S) + C rad := by
  simp [pack]

private lemma divides_real {f g : ℤ[X]} (h : pack f 1 ∣ pack g 0) :
    f^2 + 2 ∣ g := by
  obtain ⟨t, ht⟩ := h
  rw [← repack t, pack_mul] at ht
  obtain ⟨hre, him⟩ := pack_injective ht
  refine ⟨-imagPart t, ?_⟩
  linear_combination hre - f * him


private lemma shifted_irreducible (f : ℤ[X]) (hf : f.Monic) (hpos : 0 < f.natDegree)
    (hvan : ∀ a b c d : ℤ[X], (b*d).natDegree < f.natDegree →
      a*c - 2*b*d = f → a*d+b*c = 1 → b*d = 0) :
    Irreducible (pack f 1) := by
  let _ : EuclideanDomain S := euclidean
  have hdeg : (pack f 1).natDegree = f.natDegree := by
    rw [pack_one, natDegree_add_C, hf.natDegree_map]
  have hm : (pack f 1).Monic := by
    rw [pack_one]
    apply (hf.map _).add_of_left
    exact lt_of_le_of_lt degree_C_le (natDegree_pos_iff_degree_pos.mp (by rwa [hf.natDegree_map]))
  apply hm.irreducible_iff_natDegree.mpr
  refine ⟨fun h => ?_, ?_⟩
  · rw [h, natDegree_one] at hdeg
    omega
  · intro g t hg ht hprod
    by_contra! hn
    have hgpos : 0 < g.natDegree := Nat.pos_of_ne_zero hn.1
    have htpos : 0 < t.natDegree := Nat.pos_of_ne_zero hn.2
    have hds : g.natDegree + t.natDegree = f.natDegree := by
      rw [← hdeg, ← hprod, hg.natDegree_mul ht]
    have hd : (imagPart g * imagPart t).natDegree < f.natDegree := by
      apply lt_of_le_of_lt natDegree_mul_le
      have := imag_degree_lt hg hgpos
      have := imag_degree_lt ht htpos
      omega
    have he := hprod
    rw [← repack g, ← repack t, pack_mul] at he
    obtain ⟨hr, hi⟩ := pack_injective he
    rcases mul_eq_zero.mp (hvan _ _ _ _ hd hr hi) with hb|hd
    · rw [hb, zero_mul, add_zero] at hi
      have hz := natDegree_eq_zero_of_isUnit (IsUnit.of_mul_eq_one _ hi)
      rw [real_degree hg] at hz
      omega
    · rw [hd, mul_zero, zero_add] at hi
      have hz := natDegree_eq_zero_of_isUnit (IsUnit.of_mul_eq_one _ (mul_comm _ _ |>.trans hi))
      rw [real_degree ht] at hz
      omega

theorem irreducible_sq_add_two (f : ℤ[X]) (hf : f.Monic) (hpos : 0 < f.natDegree)
    (hvan : ∀ a b c d : ℤ[X], (b*d).natDegree < f.natDegree →
      a*c - 2*b*d = f → a*d+b*c = 1 → b*d = 0) :
    Irreducible (f^2 + 2) := by
  let _ : EuclideanDomain S := euclidean
  have hpr := (shifted_irreducible f hf hpos hvan).prime
  have fact : pack f 1 * pack f (-1) = pack (f^2+2) 0 := by
    rw [pack_mul]
    congr 1 <;> ring
  have hdeg : (f^2+2).natDegree = f.natDegree * 2 := by
    change (f^2 + C (2:ℤ)).natDegree = _
    rw [natDegree_add_C, natDegree_pow]; omega
  have hN : f^2 + 2 ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  refine irreducible_iff.mpr ⟨not_isUnit_of_natDegree_pos _ (by omega), ?_⟩
  intro a b hab
  have hx : pack f 1 ∣ pack a 0 * pack b 0 := by
    rw [pack_zero,pack_zero, ← Polynomial.map_mul, ← hab, ← pack_zero, ← fact]
    exact dvd_mul_right .. 
  have hcancel (u v : ℤ[X]) (huv : f^2 + 2 = u*v) (hu : f^2+2 ∣ u) : IsUnit v := by
    obtain ⟨z,hz⟩ := hu
    have hh : (f^2 + 2) * 1 = (f^2+2)*(z*v) := by
      calc
        _ = f^2+2 := mul_one _
        _ = u*v := huv
        _ = _ := by rw [hz]; ring
    have hv : v*z = 1 := by rw [mul_comm]; exact (mul_left_cancel₀ hN hh).symm
    exact IsUnit.of_mul_eq_one _ hv
  rcases hpr.dvd_or_dvd hx with ha|hb
  · exact Or.inr (hcancel a b hab (divides_real ha))
  · exact Or.inl (hcancel b a (hab.trans (mul_comm _ _)) (divides_real hb))

end OMA.S_mo_371405.Descent
end

section

namespace OMA.S_mo_371405
open Polynomial Finset NumberField IntermediateField
open scoped NumberField

private theorem int_aeval_hom {K L : Type*} [CommRing K] [CommRing L]
    (φ : K →+* L) (x : K) (f : ℤ[X]) : aeval (φ x) f = φ (aeval x f) :=
  aeval_algHom_apply φ.toIntAlgHom x f

/-- An integral polynomial value at a real algebraic integer vanishes if every
complex conjugate has modulus strictly less than one. -/
theorem small_value_at_root (f g : ℤ[X]) (hf : f.Monic) (r : ℝ) (hr : aeval r f = 0)
    (hsmall : ∀ z : ℂ, aeval z f = 0 → ‖aeval z g‖ < 1) : aeval r g = 0 := by
  classical
  let K := ℚ⟮r⟯
  have hi : IsIntegral ℤ r := ⟨f,hf,hr⟩
  let : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional (hi.tower_top (A := ℚ))
  let : NumberField K := {}
  let x : K := ⟨r,IntermediateField.mem_adjoin_simple_self ℚ r⟩
  let ι : K →+* ℝ := (algebraMap K ℝ)
  have hx : ι x = r := rfl
  have hxf : aeval x f = 0 := by
    apply ι.injective
    rw [map_zero,← int_aeval_hom,hx,hr]
  let u : 𝓞 K := ⟨x,show IsIntegral ℤ x from ⟨f,hf,hxf⟩⟩
  let v : 𝓞 K := aeval u g
  let j : 𝓞 K →+* K := algebraMap (𝓞 K) K
  have hev : j v = aeval x g := (int_aeval_hom j u g).symm
  suffices hv : v = 0 by
    rw [← hx,int_aeval_hom,← hev,hv,map_zero,map_zero]
  by_contra hne
  obtain ⟨σ,hσ⟩ := NumberField.exists_conjugate_one_le_norm (K := K) hne
  have hroot : aeval (σ x) f = 0 := by rw [int_aeval_hom,hxf,map_zero]
  have h := hsmall (σ x) hroot
  change 1 ≤ ‖σ (j v)‖ at hσ
  rw [hev,← int_aeval_hom] at hσ
  exact h.not_ge hσ

theorem complex_roots_exhausted (f : ℤ[X]) (hf : f.Monic) (r : Fin f.natDegree → ℝ)
    (hinj : Function.Injective r) (hr : ∀ i, aeval (r i) f = 0) :
    ∀ z : ℂ, aeval z f = 0 → ∃ i, (r i : ℂ) = z := by
  classical
  let p := f.map (algebraMap ℤ ℂ)
  let c : Fin f.natDegree → ℂ := fun i => (r i : ℂ)
  have hci : Function.Injective c := Complex.ofReal_injective.comp hinj
  have hp : p ≠ 0 := (hf.map _).ne_zero
  have he (i) : p.eval (c i) = 0 := by
    rw [show p.eval (c i) = aeval (Complex.ofRealHom (r i)) f from eval_map_algebraMap ..,
      int_aeval_hom,hr,map_zero]
  let s := univ.image c
  have hcard : p.natDegree ≤ s.card := by simp [s,p,hf.natDegree_map,card_image_of_injective _ hci]
  have hs : p.roots = s.val := roots_eq_of_natDegree_le_card_of_ne_zero
    (fun z hz => by obtain ⟨i,_,rfl⟩ := mem_image.mp hz; exact he i) hcard hp
  intro z hz
  have hz' : z ∈ p.roots := (mem_roots hp).mpr (by change (f.map (algebraMap ℤ ℂ)).eval z = 0; rw [eval_map_algebraMap]; exact hz)
  rw [hs] at hz'
  obtain ⟨i,_,e⟩ := mem_image.mp (show z ∈ s from hz')
  exact ⟨i,e⟩

theorem small_polynomial_zero (f g : ℤ[X]) (hf : f.Monic) (r : Fin f.natDegree → ℝ)
    (hinj : Function.Injective r) (hr : ∀ i, aeval (r i) f = 0) (hdeg : g.natDegree < f.natDegree)
    (hsmall : ∀ i, |aeval (r i) g| < 1) : g = 0 := by
  have hh (z : ℂ) (hz : aeval z f = 0) : ‖aeval z g‖ < 1 := by
    obtain ⟨i,rfl⟩ := complex_roots_exhausted f hf r hinj hr z hz
    rw [show aeval ((r i : ℝ) : ℂ) g = Complex.ofRealHom (aeval (r i) g) from
      int_aeval_hom Complex.ofRealHom (r i) g]
    simpa using hsmall i
  have ha : g.map (algebraMap ℤ ℝ) = 0 :=
    eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hinj
      (fun i => (eval_map_algebraMap ..).trans (small_value_at_root f g hf _ (hr i) hh))
      (by rw [natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective ℤ ℝ),Fintype.card_fin]; exact hdeg)
  by_contra h
  exact (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective ℤ ℝ)).mpr h ha

/-- Imaginary parts of two monic factors over the integers with √(-2)
cannot both be nonzero. At each real zero their product has square at most one half. -/
theorem imag_product_zero (f a b c d : ℤ[X]) (hf : f.Monic) (r : Fin f.natDegree → ℝ)
    (hinj : Function.Injective r) (hr : ∀ i, aeval (r i) f = 0)
    (hd : (b*d).natDegree < f.natDegree)
    (hre : a*c-2*b*d = f) (him : a*d+b*c = 1) : b*d = 0 := by
  apply small_polynomial_zero f (b*d) hf r hinj hr hd
  intro i
  let v := aeval (r i) (R := ℤ)
  have he := congrArg v hre
  have hi := congrArg v him
  simp only [v,map_sub,map_mul,map_add,map_ofNat,map_one,hr] at he hi
  rw [map_mul,abs_lt]
  have H : (aeval (r i) a * aeval (r i) d - aeval (r i) b * aeval (r i) c)^2 +
      8*(aeval (r i) b * aeval (r i) d)^2 = 1 := by
    linear_combination (aeval (r i) a * aeval (r i) d + aeval (r i) b * aeval (r i) c + 1)*hi -
      4 * aeval (r i) b * aeval (r i) d * he
  constructor <;> nlinarith [sq_nonneg (aeval (r i) a * aeval (r i) d - aeval (r i) b * aeval (r i) c),
    sq_nonneg (aeval (r i) b * aeval (r i) d - 1),sq_nonneg (aeval (r i) b * aeval (r i) d + 1)]

end OMA.S_mo_371405
end

section

namespace OMA.S_mo_371405
open Polynomial

theorem irreducible_of_comp_nonconstant {p q : ℤ[X]} (hq : 0 < q.natDegree)
    (h : Irreducible (p.comp q)) : Irreducible p := by
  let φ := Polynomial.eval₂RingHom C q
  have reflect (f : ℤ[X]) (hf : IsUnit (f.comp q)) : IsUnit f := by
    have hdeg := natDegree_eq_zero_of_isUnit hf
    rw [natDegree_comp] at hdeg
    have hz : f.natDegree = 0 := (Nat.mul_eq_zero.mp hdeg).resolve_right hq.ne'
    have hf' := eq_C_of_natDegree_eq_zero hz
    rw [hf',C_comp] at hf
    rw [hf']
    exact hf
  refine ⟨fun hu => h.not_isUnit (hu.map φ),?_⟩
  intro a b he
  obtain h₁|h₂ := h.isUnit_or_isUnit (show p.comp q=a.comp q*b.comp q by rw [he,mul_comp])
  · exact Or.inl (reflect a h₁)
  · exact Or.inr (reflect b h₂)

theorem trace_square_irreducible {q f : ℤ[X]} (he : q.comp (X^2-2) = f^2+2)
    (hi : Irreducible (f^2+2)) : Irreducible q := by
  apply irreducible_of_comp_nonconstant (q := X^2-2) _ (he ▸ hi)
  have hd : (X^2-2 : ℤ[X]).natDegree = 2 := by compute_degree; norm_num
  omega

end OMA.S_mo_371405
end

section

namespace OMA.S_mo_371405
open Polynomial Finset

noncomputable def F (n : ℕ) : ℤ[X] := Chebyshev.S ℤ n

noncomputable def traceBase : ℕ → ℤ[X]
  | 0 => 1
  | 1 => X+2
  | n+2 => X*traceBase (n+1)-traceBase n+2

noncomputable def Q (n : ℕ) : ℤ[X] := traceBase n+2

private theorem f_rec (n : ℕ) : F (n+2) = X*F (n+1)-F n := by
  simpa only [F,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using Chebyshev.S_add_two ℤ n

theorem F_monic_degree (n : ℕ) : (F n).Monic ∧ (F n).natDegree=n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [F]
  | one => simp [F]
  | more n ih ih' =>
    have hh : (X*F (n+1)).Monic := monic_X.mul ih'.1
    have hd : (X*F (n+1)).natDegree=n+2 := by rw [natDegree_mul monic_X.ne_zero ih'.1.ne_zero,natDegree_X,ih'.2]; omega
    have hlt : (F n).natDegree < (X*F (n+1)).natDegree := by rw [ih.2,hd]; omega
    exact f_rec n ▸ ⟨hh.sub_of_left (degree_lt_degree hlt),(natDegree_sub_eq_left_of_natDegree_lt hlt).trans hd⟩

theorem Q_comp (n : ℕ) : (Q n).comp (X^2-2)=(F n)^2+2 := by
  have hb (k : ℕ) : (traceBase k).comp (X^2-2)=(F k)^2 := by
    induction k using Nat.twoStepInduction with
    | zero => simp [traceBase,F]
    | one => simp [traceBase,F]
    | more k h0 h1 =>
      change (X*traceBase (k+1)-traceBase k+2).comp _=_
      simp only [add_comp,sub_comp,mul_comp,X_comp,ofNat_comp,h0,h1,f_rec]
      have hc : (F k)^2+(F (k+1))^2-X*F k*F (k+1)=1 := by
        simpa only [F,Nat.cast_add,Nat.cast_one] using Chebyshev.S_sq_add_S_sq ℤ k
      linear_combination -2*hc
  simp [Q,hb]

theorem Q_monic_degree (n : ℕ) : (Q n).natDegree=n ∧ (0<n → (Q n).Monic) := by
  have hm := (F_monic_degree n).1
  have hd := (F_monic_degree n).2
  cases n with
  | zero => norm_num [Q,traceBase]
  | succ n =>
    have hq := Q_comp (n+1)
    have hm' : ((F (n+1))^2+2).Monic := (hm.pow 2).add_of_left (by
      have hh : (2:ℤ[X]).natDegree<((F (n+1))^2).natDegree := by rw [natDegree_pow,hd]; simp
      exact degree_lt_degree hh)
    have harg : ((X:ℤ[X])^2-2).Monic := (monic_X.pow 2).sub_of_left (degree_lt_degree (by norm_num))
    have hargd : ((X:ℤ[X])^2-2).natDegree=2 := by
      rw [natDegree_sub_eq_left_of_natDegree_lt (by norm_num)]; norm_num
    have hdeg := congrArg natDegree hq
    simp only [natDegree_comp,hargd] at hdeg
    have hsmall : (2:ℤ[X]).natDegree<((F (n+1))^2).natDegree := by rw [natDegree_pow,hd]; simp
    rw [natDegree_add_eq_left_of_natDegree_lt hsmall,natDegree_pow,hd] at hdeg
    refine ⟨by omega,fun _ => ?_⟩
    have hh := congrArg leadingCoeff hq
    rw [leadingCoeff_comp (by omega : (X^2-2:ℤ[X]).natDegree≠0),harg.leadingCoeff,one_pow,mul_one,hm'.leadingCoeff] at hh
    exact hh

private def gs {A : Type*} [CommRing A] (x : A) (n : ℕ) := ∑ k ∈ range (n+1),x^k

private lemma gs_first {A : Type*} [CommRing A] (x : A) (n : ℕ) :
    gs x (n+1)=x*gs x n+1 := by simp [gs,sum_range_succ' (fun k => x^k) (n+1),pow_succ',mul_sum]

private lemma gs_last {A : Type*} [CommRing A] (x : A) (n : ℕ) :
    gs x (n+1)=gs x n+x^(n+1) := sum_range_succ _ _

private lemma gs_sq {A : Type*} [CommRing A] (x : A) (n : ℕ) :
    (gs x (n+2))^2=(x^2+1)*(gs x (n+1))^2-x^2*(gs x n)^2+2*x^(n+2) := by
  rw [gs_first x (n+1),pow_succ x (n+1)]
  linear_combination -(gs x (n+1)+x*gs x n+1)*(gs_first x n) + 2*x*(gs_last x n)

theorem trace_geom {A : Type*} [CommRing A] (x y : A) (hxy : x*y=x^2+1) (n : ℕ) :
    x^n * (traceBase n).eval₂ (Int.castRingHom A) y = (gs x n)^2 := by
  induction n using Nat.twoStepInduction with
  | zero => simp [traceBase,gs]
  | one => simp [traceBase,gs,sum_range_succ]; linear_combination hxy
  | more n ih ih' =>
    change x^(n+2) * (X*traceBase (n+1)-traceBase n+2).eval₂ _ y=_
    rw [gs_sq]; simp only [eval₂_add,eval₂_sub,eval₂_mul,eval₂_X,eval₂_ofNat]
    rw [← ih,← ih',show x^(n+2)=x^(n+1)*x by ring,show x^(n+1)=x^n*x by ring]
    linear_combination x^n*x*(traceBase (n+1)).eval₂ (Int.castRingHom A) y * hxy

theorem evalOmega_palindromic (n : ℕ) : evalOmega (palindromic n) =
    (QuadraticAlgebra.omega : TraceRing)^n * algebraMap ℤ[X] TraceRing (Q n) := by
  let x : TraceRing := QuadraticAlgebra.omega
  let y : TraceRing := algebraMap ℤ[X] TraceRing X
  have hxy : x*y = x^2+1 := by
    rw [pow_two,QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
    simp [x,y]; ring
  have he : evalOmega (geometric n)=gs x n := by
    simp [evalOmega,geometric,gs,x]
  have hf : (traceBase n).eval₂ (Int.castRingHom TraceRing) y = algebraMap ℤ[X] TraceRing (traceBase n) := by
    let h1 := eval₂RingHom (Int.castRingHom TraceRing) y
    have e : h1=algebraMap ℤ[X] TraceRing := by
      apply Polynomial.ringHom_ext
      · intro a; simp [h1]
      · simp [h1,y]
    exact DFunLike.congr_fun e _
  have h := trace_geom x y hxy n
  rw [hf] at h
  simp only [palindromic,map_add,map_pow,map_mul,he,Q,map_ofNat]
  rw [show evalOmega X = x by simp [evalOmega,x]]
  change (gs x n)^2 + 2*x^n = x^n*(algebraMap ℤ[X] TraceRing (traceBase n)+2)
  rw [← h]; ring

noncomputable def realRoot (n : ℕ) (i : Fin n) : ℝ :=
  2 * Real.cos (((i:ℝ)+1)*Real.pi/(n+1))

theorem realRoot_injective (n : ℕ) : Function.Injective (realRoot n) := by
  intro i j h
  apply Fin.ext
  apply (range n).nodup_map_iff_injOn.mp (Chebyshev.roots_U_real_nodup n)
    (Finset.mem_range.mpr i.isLt) (Finset.mem_range.mpr j.isLt)
  unfold realRoot at h
  linarith

theorem F_aeval_root (n : ℕ) (i : Fin n) : aeval (realRoot n i) (F n) = 0 := by
  unfold F realRoot
  rw [Chebyshev.aeval_S]
  have hθ : 0 < ((i:ℝ)+1)*Real.pi/(n+1) := by positivity
  have hθ' : ((i:ℝ)+1)*Real.pi/(n+1) < Real.pi := by
    rw [div_lt_iff₀ (by positivity)]
    have hi : (i:ℝ)<n := by exact_mod_cast i.isLt
    nlinarith [mul_pos (sub_pos.mpr hi) Real.pi_pos]
  apply (mul_eq_zero_iff_right (Real.sin_pos_of_pos_of_lt_pi hθ hθ').ne').mp
  rw [Chebyshev.S_two_mul_real_cos, Real.sin_eq_zero_iff]
  use (i:ℤ)+1
  push_cast
  field_simp

end OMA.S_mo_371405
end

namespace OMA.S_mo_371405
open Polynomial

/-- The square of a monic positive-degree integer polynomial plus two is
irreducible when the polynomial has as many distinct real zeros as its degree. -/
theorem irreducible_square_add_two_of_real_roots (f : ℤ[X]) (hf : f.Monic)
    (hn : 0 < f.natDegree) (r : Fin f.natDegree → ℝ) (hinj : Function.Injective r)
    (hr : ∀ i, aeval (r i) f = 0) : Irreducible (f^2+2) := by
  apply Descent.irreducible_sq_add_two f hf hn
  intro a b c d hd hre him
  exact imag_product_zero f a b c d hf r hinj hr hd hre him

end OMA.S_mo_371405

open OMA.S_mo_371405 in
theorem OMA.solution : type_of% @OMA.S_mo_371405.main := by
  intro n hn
  apply palindromic_irreducible_of_trace hn _ (evalOmega_palindromic n)
  apply trace_square_irreducible (Q_comp n)
  obtain ⟨hmon,hdeg⟩ := F_monic_degree n
  let e := finCongr hdeg
  apply irreducible_square_add_two_of_real_roots (F n) hmon (by rw [hdeg]; exact hn)
    (fun i => realRoot n (e i)) ((realRoot_injective n).comp e.injective)
  exact fun i => F_aeval_root n (e i)

import OMAStatements.S_oeis_a023871

/- Product -/
section

namespace BalaProduct

open PowerSeries

noncomputable def geom (R : Type*) [CommRing R] (k : ℕ) : PowerSeries R :=
  if hk : k ≠ 0 then expand k hk (mk 1) else 1

theorem coeff_geom (R : Type*) [CommRing R] (k i : ℕ) (hk : k ≠ 0) :
    coeff i (geom R k) = if k ∣ i then 1 else 0 := by
  simp [geom, hk, coeff_expand]

theorem geom_mul (R : Type*) [CommRing R] {k : ℕ} (hk : k ≠ 0) :
    geom R k * (1 - X ^ k) = 1 := by
  simpa [geom, hk] using congrArg (expand k hk) (mk_one_mul_one_sub_eq_one R)

theorem map_geom (R S : Type*) [CommRing R] [CommRing S] (f : R →+* S) (k : ℕ) :
    map f (geom R k) = geom S k := by
  ext i
  by_cases hk : k = 0
  · simp [geom, hk]
  · simp [coeff_map, coeff_geom, hk, apply_ite f]

theorem geom_rat (k : ℕ) (hk : k ≠ 0) : geom ℚ k = (1 - X ^ k : PowerSeries ℚ)⁻¹ := by
  apply (eq_inv_iff_mul_eq_one (by simp [hk])).2
  exact geom_mul ℚ hk

noncomputable def finiteProduct (R : Type*) [CommRing R] (N : ℕ) : PowerSeries R :=
  ∏ k ∈ Finset.Icc 1 N, (geom R k) ^ (k ^ 2)

theorem map_finite (R S : Type*) [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) :
    map f (finiteProduct R N) = finiteProduct S N := by
  simp [finiteProduct, map_geom]

theorem finite_rat (N : ℕ) : finiteProduct ℚ N = OMA.S_oeis_a023871.A N := by
  apply Finset.prod_congr rfl
  intro k hk
  rw [geom_rat k (by have := (Finset.mem_Icc.mp hk).1; omega)]

theorem u_eq_int (n : ℕ) :
    OMA.S_oeis_a023871.u n = ((coeff n (finiteProduct ℤ n ^ n) : ℤ) : ℚ) := by
  rw [OMA.S_oeis_a023871.u, ← finite_rat, ← map_finite ℤ ℚ (Int.castRingHom ℚ), ← map_pow,
    coeff_map]
  rfl

theorem trunc_geom_large {R : Type*} [CommRing R] {n k : ℕ} (hn : n < k) :
    trunc (n+1) (geom R k) = 1 := by
  ext i
  rw [coeff_trunc, Polynomial.coeff_one]
  rcases i with _|i
  · simp [coeff_geom, Nat.ne_zero_of_lt hn]
  · by_cases hi : i+1 < n+1
    · have hd : ¬ k ∣ i+1 := by
        intro h
        have := Nat.le_of_dvd (Nat.succ_pos i) h
        omega
      simp [hi, coeff_geom, Nat.ne_zero_of_lt hn, hd]
    · simp [hi]

theorem trunc_mult_right_one {R : Type*} [CommRing R] {n : ℕ} {f g : PowerSeries R}
    (h : trunc n g = 1) : trunc n (f * g) = trunc n f := by
  rw [← trunc_mul_trunc, h]
  simp

theorem trunc_geom_pow {R : Type*} [CommRing R] {n k : ℕ} (hn : n < k) (b : ℕ) :
    trunc (n+1) (geom R k ^ b) = 1 := by
  rw [← trunc_trunc_pow (geom R k), trunc_geom_large hn]
  simp [trunc_one]

theorem finite_succ (R : Type*) [CommRing R] (N : ℕ) :
    finiteProduct R (N+1) = finiteProduct R N * geom R (N+1) ^ ((N+1)^2) := by
  dsimp [finiteProduct]
  rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ N+1)]

theorem trunc_finite {R : Type*} [CommRing R] {n M : ℕ} (h : n ≤ M) :
    trunc (n+1) (finiteProduct R M) = trunc (n+1) (finiteProduct R n) := by
  induction M, h using Nat.le_induction with
  | base => rfl
  | succ M h ih =>
    rw [finite_succ, trunc_mult_right_one (trunc_geom_pow (R := R) (n := n) (k := M+1) (by omega) ((M+1)^2))]; exact ih

noncomputable def G (R : Type*) [CommRing R] : PowerSeries R :=
  mk fun n => coeff n (finiteProduct R n)

theorem coeff_finite {R : Type*} [CommRing R] {n M : ℕ} (h : n ≤ M) :
    coeff n (finiteProduct R M) = coeff n (G R) := by
  have e := congrArg (Polynomial.coeff · n) (trunc_finite (R := R) h)
  simpa [coeff_trunc, G] using e

theorem trunc_G_eq (R : Type*) [CommRing R] (N : ℕ) :
    trunc (N+1) (G R) = trunc (N+1) (finiteProduct R N) := by
  ext i
  simp only [coeff_trunc]
  split_ifs with hi
  · exact (coeff_finite (by omega)).symm
  · rfl

theorem coeff_finite_pow {R : Type*} [CommRing R] {n N : ℕ} (hn : n ≤ N) (k : ℕ) :
    coeff n (G R ^ k) = coeff n (finiteProduct R N ^ k) := by
  have ht : trunc (N+1) (G R ^ k) = trunc (N+1) (finiteProduct R N ^ k) := by
    rw [← trunc_trunc_pow (G R), trunc_G_eq, trunc_trunc_pow]
  have e := congrArg (Polynomial.coeff · n) ht
  simpa [coeff_trunc, show n < N+1 by omega] using e

theorem u_eq_G (n : ℕ) : OMA.S_oeis_a023871.u n = ((coeff n (G ℤ ^ n) : ℤ) : ℚ) := by
  rw [u_eq_int, coeff_finite_pow (le_refl n)]

theorem map_G (R S : Type*) [CommRing R] [CommRing S] (f : R →+* S) :
    map f (G R) = G S := by
  ext i
  simp only [coeff_map, G, coeff_mk]
  rw [← coeff_map, map_finite]


noncomputable def E (H : PowerSeries ℚ) : PowerSeries ℚ := (exp ℚ).subst H

theorem E_der (H : PowerSeries ℚ) (h : constantCoeff H = 0) :
    derivative ℚ (E H) = E H * derivative ℚ H := by
  rw [E, derivative_subst (HasSubst.of_constantCoeff_zero' h), derivative_exp]

theorem E_const (H : PowerSeries ℚ) (h : constantCoeff H = 0) : constantCoeff (E H) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, E, coeff_subst' (HasSubst.of_constantCoeff_zero' h),
    finsum_eq_single _ 0]
  · simp
  · intro n hn
    simp [coeff_zero_eq_constantCoeff, h, zero_pow hn]

theorem eq_of_ode {F G L : PowerSeries ℚ} (hc : constantCoeff F = 1)
    (hd : constantCoeff G = 1) (hf : derivative ℚ F = F * L) (hg : derivative ℚ G = G * L) :
    F = G := by
  have hu := PowerSeries.mul_inv_cancel G (by rw [hd]; norm_num)
  have hzero : derivative ℚ (F * G⁻¹) = 0 := by
    rw [Derivation.leibniz, derivative_inv', hf, hg]
    simp only [smul_eq_mul]
    linear_combination -(F*G⁻¹*L) * hu
  have h1 : F * G⁻¹ = 1 := derivative.ext (by simpa [derivative_one] using hzero) (by simp [hc,hd])
  simpa [mul_assoc, mul_comm G⁻¹ G, hu] using congrArg (· * G) h1

theorem E_add (H K : PowerSeries ℚ) (h : constantCoeff H = 0) (k : constantCoeff K = 0) :
    E (H+K) = E H * E K := by
  have hs : constantCoeff (H+K) = 0 := by simp [h,k]
  refine eq_of_ode (E_const _ hs) (by simp [E_const _ h,E_const _ k])
    (E_der _ hs) ?_
  rw [Derivation.leibniz, map_add, E_der H h, E_der K k]
  simp only [smul_eq_mul]
  ring

theorem E_zero : E 0 = 1 := by
  rw [E, subst_zero_eq_C_constantCoeff]
  simp [constantCoeff_exp]

theorem E_nsmul (H : PowerSeries ℚ) (h : constantCoeff H = 0) (n : ℕ) :
    E (n • H) = (E H)^n := by
  induction n with
  | zero => simp [E_zero]
  | succ n ih =>
    rw [succ_nsmul, E_add _ _ (by simp [h]) h, ih, pow_succ]

theorem E_expand {p : ℕ} (hp : p ≠ 0) (H : PowerSeries ℚ) (h : constantCoeff H = 0) :
    E (expand p hp H) = expand p hp (E H) := by
  exact (expand_subst p hp (HasSubst.of_constantCoeff_zero' h) (exp ℚ)).symm

noncomputable def harmonic : PowerSeries ℚ := mk fun j => (j : ℚ)⁻¹

theorem harmonic_zero : constantCoeff harmonic = 0 := by
  simp [harmonic, ← coeff_zero_eq_constantCoeff_apply]

theorem harmonic_der : derivative ℚ harmonic = mk 1 := by
  ext n
  rw [coeff_derivative, harmonic, coeff_mk, coeff_mk]
  simp [inv_mul_cancel₀ (by positivity : (n:ℚ)+1 ≠ 0)]

theorem E_harmonic : E harmonic = mk 1 := by
  refine eq_of_ode (E_const _ harmonic_zero) (by simp) (E_der _ harmonic_zero) ?_
  rw [harmonic_der]
  have hi : (mk 1 : PowerSeries ℚ) = ((1-X : PowerSeries ℚ)⁻¹) :=
    (eq_inv_iff_mul_eq_one (by simp)).2 (mk_one_mul_one_sub_eq_one ℚ)
  rw [hi, derivative_inv', map_sub, derivative_one, derivative_X]
  ring

noncomputable def logFactor (k : ℕ) : PowerSeries ℚ :=
  if hk : k ≠ 0 then (k ^ 2) • expand k hk harmonic else 0

theorem logFactor_zero (k : ℕ) : constantCoeff (logFactor k) = 0 := by
  by_cases h : k = 0 <;> simp [logFactor, h, harmonic_zero]

theorem E_logFactor (k : ℕ) : E (logFactor k) = geom ℚ k ^ (k^2) := by
  by_cases h : k = 0
  · simp [logFactor, geom, h, E_zero]
  · rw [logFactor, dif_pos h, E_nsmul _ (by simp [harmonic_zero]), E_expand h _ harmonic_zero,
      E_harmonic, geom, dif_pos h]

noncomputable def finiteLog (N : ℕ) : PowerSeries ℚ := ∑ k ∈ Finset.Icc 1 N, logFactor k

theorem finiteLog_const (N : ℕ) : constantCoeff (finiteLog N) = 0 := by
  simp [finiteLog, logFactor_zero]

theorem E_finiteLog (N : ℕ) : E (finiteLog N) = finiteProduct ℚ N := by
  induction N with
  | zero => simp [finiteLog, finiteProduct, E_zero]
  | succ N ih =>
    have hs : finiteLog (N+1) = finiteLog N + logFactor (N+1) :=
      Finset.sum_Icc_succ_top (by omega) _
    rw [hs, E_add _ _ (finiteLog_const _) (logFactor_zero _), ih, E_logFactor, finite_succ]

noncomputable def H : PowerSeries ℚ :=
  mk fun n => ∑ k ∈ n.divisors, ((k : ℚ)^2 / (n / k : ℕ))

theorem coeff_logFactor {k : ℕ} (hk : k ≠ 0) (n : ℕ) :
    coeff n (logFactor k) = if k ∣ n then (k:ℚ)^2/(n/k : ℕ) else 0 := by
  rw [logFactor, dif_pos hk, map_nsmul, coeff_expand]
  split_ifs <;> simp [harmonic, div_eq_mul_inv]

theorem coeff_finiteLog (N i : ℕ) (hi : i ≤ N) :
    coeff i (finiteLog N) = coeff i H := by
  rcases i with _|i
  · rw [coeff_zero_eq_constantCoeff, finiteLog_const, H, ← coeff_zero_eq_constantCoeff_apply, coeff_mk]; simp
  dsimp [finiteLog, H]
  rw [map_sum, coeff_mk]
  have hs : i.succ.divisors = (Finset.Icc 1 N).filter (· ∣ i+1) := by
    ext a
    rw [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
    constructor
    · intro ⟨hd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega), (Nat.le_of_dvd (by omega) hd).trans hi⟩,hd⟩
    · intro ha; exact ⟨ha.2, by omega⟩
  rw [hs, Finset.sum_filter]
  exact Finset.sum_congr rfl fun k hk => coeff_logFactor (by have := (Finset.mem_Icc.mp hk).1; omega) _

theorem trunc_H (N : ℕ) : trunc (N+1) H = trunc (N+1) (finiteLog N) := by
  ext i
  simp only [coeff_trunc]
  split_ifs with hi
  · exact (coeff_finiteLog _ _ (by omega)).symm
  · rfl

theorem H_zero : constantCoeff H = 0 := by
  simp [H, ← coeff_zero_eq_constantCoeff_apply]

theorem E_eq_of_trunc {n : ℕ} {H K : PowerSeries ℚ} (hH : constantCoeff H = 0)
    (hK : constantCoeff K = 0) (h : trunc (n+1) H = trunc (n+1) K) :
    coeff n (E H) = coeff n (E K) := by
  rw [E, E, coeff_subst' (HasSubst.of_constantCoeff_zero' hH),
    coeff_subst' (HasSubst.of_constantCoeff_zero' hK)]
  apply finsum_congr
  intro j
  have hp : trunc (n+1) (H^j) = trunc (n+1) (K^j) := by
    rw [← trunc_trunc_pow H, h, trunc_trunc_pow]
  have he := congrArg (Polynomial.coeff · n) hp
  simpa [coeff_trunc] using congrArg (fun x : ℚ => coeff j (exp ℚ) • x) he

theorem E_H : E H = G ℚ := by
  ext n
  rw [E_eq_of_trunc H_zero (finiteLog_const n) (trunc_H n), E_finiteLog, coeff_finite (le_refl n)]

noncomputable def delta (p : ℕ) (hp : p ≠ 0) : PowerSeries ℚ :=
  H - (p : ℚ)⁻¹ • expand p hp H

theorem delta_const {p : ℕ} (hp : p ≠ 0) : constantCoeff (delta p hp) = 0 := by
  simp [delta, H_zero, smul_eq_C_mul]

theorem frob_exp {p : ℕ} (hp : p ≠ 0) (m : ℕ) :
    (G ℚ)^(p*m) = (expand p hp (G ℚ))^m * E ((p*m) • delta p hp) := by
  have hc : (p*m) • H = m • expand p hp H + (p*m) • delta p hp := by
    simp only [delta, nsmul_eq_mul, smul_eq_C_mul, Nat.cast_mul]
    have hi : (p : PowerSeries ℚ) * C (p : ℚ)⁻¹ = 1 := by
      rw [← map_natCast C p, ← map_mul, mul_inv_cancel₀ (by exact_mod_cast hp), map_one]
    linear_combination (m : PowerSeries ℚ) * expand p hp H * hi
  rw [← E_H, ← E_nsmul _ H_zero, hc, E_add _ _ (by simp [H_zero])
    (by simp [delta_const hp]), E_nsmul _ (by simp [H_zero]), E_expand hp _ H_zero]

theorem coeff_H_div (n : ℕ) :
    coeff n H = ∑ x ∈ n.divisors, ((n/x : ℕ):ℚ)^2/(x:ℚ) := by
  rw [H, coeff_mk]
  conv_rhs => rw [← Nat.sum_div_divisors n (fun x => ((n / x : ℕ):ℚ)^2/(x:ℚ))]
  apply Finset.sum_congr rfl
  intro x hx
  simp [Nat.div_div_self (Nat.dvd_of_mem_divisors hx) (Nat.ne_zero_of_mem_divisors hx)]

theorem coeff_delta {p : ℕ} (hp : p ≠ 0) (n : ℕ) :
    coeff n (delta p hp) =
      ∑ x ∈ n.divisors, if ¬p ∣ x then ((n/x : ℕ):ℚ)^2/(x:ℚ) else 0 := by
  classical
  rw [delta, map_sub, coeff_smul, coeff_expand, coeff_H_div]
  by_cases hd : p ∣ n
  · obtain ⟨m,rfl⟩ := hd
    simp only [dvd_mul_right, if_true, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp),
      coeff_H_div, smul_eq_mul]
    let f : ℕ → ℚ := fun x => ((p*m / x : ℕ):ℚ)^2/(x:ℚ)
    have hs : ((p*m).divisors.filter (p ∣ ·)) = m.divisors.image (p * ·) := by
      ext x
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image]
      constructor
      · rintro ⟨⟨hx, hm⟩, ⟨k, rfl⟩⟩
        exact ⟨k, ⟨(Nat.mul_dvd_mul_iff_left hp.bot_lt).mp hx, (mul_ne_zero_iff.mp hm).2⟩, rfl⟩
      · rintro ⟨k, ⟨hk, hm⟩, rfl⟩
        exact ⟨⟨Nat.mul_dvd_mul_left p hk, mul_ne_zero hp hm⟩, dvd_mul_right p k⟩
    have hk : ∑ x ∈ (p*m).divisors.filter (p ∣ ·), f x =
        (p:ℚ)⁻¹ * ∑ k ∈ m.divisors, ((m/k : ℕ):ℚ)^2/(k:ℚ) := by
      rw [hs, Finset.sum_image (by intro x hx y hy h; exact Nat.eq_of_mul_eq_mul_left hp.bot_lt h),
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      dsimp [f]
      rw [Nat.mul_div_mul_left _ _ hp.bot_lt, Nat.cast_mul]
      ring
    change (∑ x ∈ (p*m).divisors, f x) - _ = ∑ x ∈ (p*m).divisors, _
    rw [← hk, ← Finset.sum_filter]
    apply sub_eq_of_eq_add
    simpa using (Finset.sum_filter_add_sum_filter_not (s := (p*m).divisors) (p := fun x => ¬p ∣ x) (f := f)).symm
  · rw [if_neg hd, smul_zero, sub_zero]
    apply Finset.sum_congr rfl
    intro x hx
    rw [if_pos (fun h => hd (h.trans (Nat.dvd_of_mem_divisors hx)))]

theorem rescale_subst_E (a : ℚ) (Z : PowerSeries ℚ) (hz : constantCoeff Z = 0) :
    (rescale a (exp ℚ)).subst Z = E (a • Z) := by
  ext n
  have h : constantCoeff (a • Z) = 0 := by simp [smul_eq_C_mul, hz]
  rw [E, coeff_subst' (HasSubst.of_constantCoeff_zero' hz),
    coeff_subst' (HasSubst.of_constantCoeff_zero' h)]
  apply finsum_congr
  intro k
  rw [coeff_rescale, smul_pow, coeff_smul]
  simp [smul_eq_mul]; ring

end BalaProduct

end

/- Local -/
section

namespace BalaFrob

def localRing (p : ℕ) [Fact p.Prime] : Subring ℚ where
  carrier := {z | padicNorm p z ≤ 1}
  add_mem' := fun a b => padicNorm.nonarchimedean.trans (max_le a b)
  zero_mem' := by simp
  neg_mem' := fun a => by simpa using a
  one_mem' := (padicNorm.one (p := p)).le
  mul_mem' := fun {a b} ha hb => by
    change padicNorm p (a*b) ≤ 1
    rw [padicNorm.mul]
    exact mul_le_one₀ ha (padicNorm.nonneg b) hb

variable {p : ℕ} [hp : Fact p.Prime]

lemma mem_local_iff {z : ℚ} (hz : z ≠ 0) :
    z ∈ localRing p ↔ 0 ≤ padicValRat p z := by
  change padicNorm p z ≤ 1 ↔ _
  rw [padicNorm.eq_zpow_of_nonzero hz, zpow_le_one_iff_right₀ (by exact_mod_cast hp.out.one_lt), neg_nonpos]

lemma unit_divisor_mem (a b : ℕ) (hb : ¬p ∣ b) : (a : ℚ) / b ∈ localRing p := by
  have hn : (padicNorm p (b : ℚ)) = 1 := by
    exact_mod_cast (padicNorm.int_eq_one_iff (p := p) (b : ℤ)).mpr (by exact_mod_cast hb)
  change padicNorm p ((a : ℚ) / b) ≤ 1
  rw [padicNorm.div, hn, div_one]
  exact_mod_cast (padicNorm.of_int (p := p) (a : ℤ))

lemma factorial_bound {k j : ℕ} (hp7 : 7 ≤ p) (hj : j ≤ 3) (hjk : j ≤ k) :
    padicValNat p k.factorial ≤ k - j := by
  by_cases hk : k = 0
  · simp [hk]
  have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p hk
  have hs : 6 * padicValNat p k.factorial ≤ (p-1) * padicValNat p k.factorial :=
    Nat.mul_le_mul_right _ (by omega)
  omega

lemma divided_exp_tail_mem {k j : ℕ} (hp7 : 7 ≤ p) (hj : j ≤ 3) (hjk : j ≤ k) :
    (p : ℚ)^(k-j) / (k.factorial : ℚ) ∈ localRing p := by
  have hf : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hpp : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [mem_local_iff (div_ne_zero (pow_ne_zero _ hpp) hf),
    padicValRat.div (pow_ne_zero _ hpp) hf, padicValRat.pow,
    padicValRat.self hp.out.one_lt, mul_one, padicValRat.of_nat]
  have h := factorial_bound hp7 hj hjk
  exact sub_nonneg.mpr (by exact_mod_cast h)

lemma integral_of_local_divisibility (e : ℕ) (z : ℤ)
    (h : (p : localRing p)^e ∣ (z : localRing p)) : (p : ℤ)^e ∣ z := by
  by_cases hz : z = 0
  · simp [hz]
  obtain ⟨w, hw⟩ := h
  have he : (z : ℚ) = (p : ℚ)^e * (w : ℚ) := by exact_mod_cast congrArg Subtype.val hw
  have hpp : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hwz : (w : ℚ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at he
    exact hz (by exact_mod_cast he)
  have hν := (mem_local_iff hwz).mp w.property
  apply (padicValInt_dvd_iff _ _).mpr
  right
  have hcount := congrArg (padicValRat p) he
  rw [padicValRat.mul (pow_ne_zero _ hpp) hwz, padicValRat.pow, padicValRat.self hp.out.one_lt,
    mul_one, padicValRat.of_int] at hcount
  omega

end BalaFrob

end

/- Frobenius -/
section

namespace BalaFrob

open PowerSeries

variable {R : Type*} [CommRing R]

noncomputable def theta (f : PowerSeries R) : PowerSeries R :=
  derivative R f * X

lemma coeff_theta (f : PowerSeries R) (n : ℕ) :
    coeff n (theta f) = (n : R) * coeff n f := by
  cases n with
  | zero => simp [theta]
  | succ n =>
    rw [theta, coeff_succ_mul_X, coeff_derivative]
    push_cast
    ring

lemma theta_mul (f g : PowerSeries R) :
    theta (f * g) = f * theta g + g * theta f := by
  simp only [theta, Derivation.leibniz, smul_eq_mul]
  ring

lemma theta_pow (f : PowerSeries R) (n : ℕ) :
    theta (f ^ n) = C (n : R) * (f ^ (n-1) * theta f) := by
  simp only [theta, derivative_pow, map_natCast]
  ring

lemma weighted_derivative_coeff (f b : PowerSeries R) (n : ℕ) :
    coeff n (f ^ n * theta b) =
    (n : R) * (coeff n (f ^ n * b) - coeff n (b * f ^ (n-1) * theta f)) := by
  have h := congrArg (coeff (R := R) n) (theta_mul (f ^ n) b)
  rw [coeff_theta, map_add, theta_pow] at h
  have eq : b * (C (n : R) * (f ^ (n-1) * theta f)) =
      C (n : R) * (b * f ^ (n-1) * theta f) := by ring
  rw [eq, coeff_C_mul] at h
  linear_combination -h

lemma weighted_square (f b q : PowerSeries R) (p n : ℕ)
    (h : q = C (p : R) * theta b) :
    (p : R) * n ∣ coeff n (f ^ n * q) := by
  refine ⟨coeff n (f ^ n * b) - coeff n (b * f ^ (n-1) * theta f), ?_⟩
  rw [h, show f^n * (C (p : R) * theta b) = C (p : R) * (f^n * theta b) by ring,
    coeff_C_mul, weighted_derivative_coeff]
  ring


lemma linear_moment_dvd (p : ℕ) (M Q : ℕ → R)
    (hQ : ∀ n : ℕ, (p : R) * n ∣ Q n)
    (hM : ∀ n : ℕ, ∃ a : R,
      M (p*n) = (p : R)^2 * M n + (p*n : ℕ) * Q n +
        ((p*n : ℕ) : R)^2 * a)
    (n e : ℕ) : (p : R)^(2*e) ∣ M (n*p^e) := by
  induction e with
  | zero => simp
  | succ e ih =>
    obtain ⟨t, ht⟩ := ih
    obtain ⟨q, hq⟩ := hQ (n*p^e)
    obtain ⟨a, ha⟩ := hM (n*p^e)
    refine ⟨t + (n : R)^2*q + (n : R)^2*a, ?_⟩
    rw [show n*p^(e+1) = p*(n*p^e) by ring, ha, ht, hq]
    push_cast
    rw [show 2*(e+1) = 2*e+2 by omega, pow_add, pow_mul']
    ring

lemma cubic_from_moments (p : ℕ) (u M Q : ℕ → R)
    (hQ : ∀ n : ℕ, (p : R) * n ∣ Q n)
    (hM : ∀ n : ℕ, ∃ a : R,
      M (p*n) = (p : R)^2 * M n + (p*n : ℕ) * Q n +
        ((p*n : ℕ) : R)^2 * a)
    (hu : ∀ n : ℕ, ∃ a b : R,
      u (p*n) - u n = (p : R)^3 * n * M n +
        ((p*n : ℕ) : R)^2 * a * Q n + ((p*n : ℕ) : R)^3 * b)
    (n e : ℕ) :
    (p : R)^(3*(e+1)) ∣ u (n*p^(e+1)) - u (n*p^e) := by
  obtain ⟨t, ht⟩ := linear_moment_dvd p M Q hQ hM n e
  obtain ⟨q, hq⟩ := hQ (n*p^e)
  obtain ⟨a,b, h⟩ := hu (n*p^e)
  refine ⟨(n : R)*t + (n : R)^3*a*q + (n : R)^3*b, ?_⟩
  rw [show n*p^(e+1) = p*(n*p^e) by ring, h, ht, hq]
  push_cast
  rw [show 3*(e+1) = 3*e+3 by omega, pow_add, pow_mul', pow_mul']
  ring

end BalaFrob

end

/- Core -/
section

namespace Bala

structure Quad where
  a : ℕ
  b : ℕ
  x : ℕ
  y : ℕ
  deriving DecidableEq, Repr

protected theorem Quad.ext {u v : Quad} (ha : u.a = v.a) (hb : u.b = v.b)
    (hx : u.x = v.x) (hy : u.y = v.y) : u = v := by
  cases u
  cases v
  simp_all

/-- The positive solutions of `a*x+b*y=N`. -/
def quadSet (N : ℕ) : Finset Quad :=
  let s := Finset.Icc 1 N
  ((s ×ˢ s ×ˢ s ×ˢ s).image
    (fun t : ℕ × ℕ × ℕ × ℕ => Quad.mk t.1 t.2.1 t.2.2.1 t.2.2.2)).filter
    (fun u => u.a * u.x + u.b * u.y = N)

@[simp] theorem mem_quadSet {u : Quad} {N : ℕ} :
    u ∈ quadSet N ↔ 0 < u.a ∧ 0 < u.b ∧ 0 < u.x ∧ 0 < u.y ∧
      u.a * u.x + u.b * u.y = N := by
  rcases u with ⟨a,b,x,y⟩
  simp only [quadSet, Finset.mem_filter, Finset.mem_image, Finset.mem_product,
    Finset.mem_Icc, Prod.exists, Quad.mk.injEq]
  constructor
  · rintro ⟨⟨a',b',x',y',⟨ha,hb,hx,hy⟩,rfl,rfl,rfl,rfl⟩,he⟩
    exact ⟨ha.1, hb.1, hx.1, hy.1, he⟩
  · rintro ⟨ha,hb,hx,hy,he⟩
    have ha' : a ≤ a*x := Nat.le_mul_of_pos_right a hx
    have hb' : b ≤ b*y := Nat.le_mul_of_pos_right b hy
    have hx' : x ≤ a*x := Nat.le_mul_of_pos_left x ha
    have hy' : y ≤ b*y := Nat.le_mul_of_pos_left y hb
    exact ⟨⟨a,b,x,y,⟨⟨ha,by omega⟩,⟨hb,by omega⟩,⟨hx,by omega⟩,⟨hy,by omega⟩⟩,
      rfl,rfl,rfl,rfl⟩,he⟩

end Bala

end

/- Slope -/
section

namespace BalaSlope
open Bala

def slope (p s : ℕ) (u : Quad) : ZMod (p ^ s) :=
  if ¬p ∣ u.y then u.a * (u.y : ZMod (p ^ s))⁻¹
  else if ¬p ∣ u.x then -(u.b : ZMod (p ^ s)) * (u.x : ZMod (p ^ s))⁻¹
  else 0

def compatible {q : ℕ} (u : Quad) (t : ZMod q) : Prop :=
  t * u.y = u.a ∧ t * u.x = - (u.b : ZMod q)

theorem slope_unique {p s : ℕ} {u : Quad} (hp : p.Prime)
    (hu : ¬p ∣ u.y ∨ ¬p ∣ u.x) {t : ZMod (p^s)} (ht : compatible u t) :
    slope p s u = t := by
  obtain ⟨ha,hb⟩ := ht
  unfold slope
  by_cases hy : ¬p ∣ u.y
  · rw [if_pos hy, ← ha, mul_assoc, ZMod.coe_mul_inv_eq_one _ (hp.coprime_pow_of_not_dvd hy), mul_one]
  · have hx : ¬p ∣ u.x := hu.resolve_left hy
    rw [if_neg hy, if_pos hx, ← hb, mul_assoc, ZMod.coe_mul_inv_eq_one _ (hp.coprime_pow_of_not_dvd hx), mul_one]

theorem slope_compatible {p s N : ℕ} (hp : p.Prime) (hN : p^s ∣ N)
    {u : Quad} (hdet : u.a*u.x+u.b*u.y=N)
    (hu : ¬p ∣ u.y ∨ ¬p ∣ u.x) : compatible u (slope p s u) := by
  have hzero : ((u.a : ZMod (p^s))*u.x+(u.b: ZMod (p^s))*u.y) = 0 := by
    exact_mod_cast (show ((u.a*u.x+u.b*u.y : ℕ) : ZMod (p^s))=0 by
      rw [hdet]; exact (ZMod.natCast_eq_zero_iff ..).mpr hN)
  unfold compatible slope
  by_cases hy : ¬p ∣ u.y
  · rw [if_pos hy]
    have hi := ZMod.coe_mul_inv_eq_one u.y (hp.coprime_pow_of_not_dvd (m:=s) hy)
    constructor
    · calc _ = u.a * ((u.y : ZMod (p^s)) * (u.y : ZMod (p^s))⁻¹) := by ring
           _ = _ := by rw [hi,mul_one]
    · linear_combination (u.y : ZMod (p^s))⁻¹ * hzero - (u.b : ZMod (p^s)) * hi
  · have hx : ¬p ∣ u.x := hu.resolve_left hy
    rw [if_neg hy, if_pos hx]
    have hi := ZMod.coe_mul_inv_eq_one u.x (hp.coprime_pow_of_not_dvd (m:=s) hx)
    constructor
    · linear_combination -(u.x : ZMod (p^s))⁻¹ * hzero + (u.a : ZMod (p^s)) * hi
    · calc _ = -(u.b : ZMod (p^s)) * ((u.x : ZMod (p^s)) * (u.x : ZMod (p^s))⁻¹) := by ring
           _ = _ := by rw [hi,mul_one]

theorem square_weight {q : ℕ} (u : Quad) {t : ZMod q} (ht : compatible u t)
    (hx : Nat.Coprime u.x q) (hy : Nat.Coprime u.y q) :
    t^4*u.x*u.y = (u.a:ZMod q)^2*u.b^2*(u.x:ZMod q)⁻¹*(u.y:ZMod q)⁻¹ := by
  obtain ⟨ha,hb⟩ := ht
  have hb' : (u.b:ZMod q) = -(t*u.x) := by rw [hb,neg_neg]
  rw [←ha,hb']
  have hxi := ZMod.coe_mul_inv_eq_one u.x hx
  have hyi := ZMod.coe_mul_inv_eq_one u.y hy
  calc _ = (t^4*u.x*u.y) * (((u.x:ZMod q)*(u.x:ZMod q)⁻¹)*((u.y:ZMod q)*(u.y:ZMod q)⁻¹)) := by rw [hxi,hyi,one_mul,mul_one]
       _ = _ := by ring

def weight (p s : ℕ) (u : Quad) : ℤ :=
  ((slope p s u).val : ℤ)^4 * u.x * u.y

lemma weight_cast (p s : ℕ) [NeZero (p^s)] (u : Quad) :
    (weight p s u : ZMod (p^s)) = (slope p s u)^4 * u.x * u.y := by
  simp [weight, ZMod.natCast_zmod_val]

lemma slope_swap {p s N : ℕ} (hp : p.Prime) (hn : p^s ∣ N) {u : Quad}
    (he : u.a*u.x+u.b*u.y=N) (hu : ¬p ∣ u.y ∨ ¬p ∣ u.x) :
    slope p s ⟨u.b,u.a,u.y,u.x⟩ = -slope p s u := by
  have ⟨hl,hr⟩ := slope_compatible hp hn he hu
  apply slope_unique hp hu.symm
  constructor <;> dsimp
  · rw [neg_mul,hr,neg_neg]
  · rw [neg_mul,hl]

lemma slope_up {p s : ℕ} (hp : p.Prime) {u : Quad} (hy : ¬p ∣ u.y) :
    let φ := ZMod.castHom (pow_dvd_pow p (Nat.le_succ s)) (ZMod (p^s))
    φ (slope p (s+1) ⟨u.a,p*u.b,p*u.x,u.y⟩) = slope p s u := by
  let φ := ZMod.castHom (pow_dvd_pow p (Nat.le_succ s)) (ZMod (p^s))
  change φ (slope p (s+1) _) = _
  simp only [slope,if_pos hy,map_mul,map_natCast]
  congr 1
  symm
  apply ZMod.inv_eq_of_mul_eq_one
  have h := congrArg φ (ZMod.coe_mul_inv_eq_one u.y (hp.coprime_pow_of_not_dvd (m:=s+1) hy))
  simpa only [map_one,map_mul,map_natCast] using h

end BalaSlope

end

/- Chain -/
section

namespace BalaChain

open Bala

private theorem mem_coords {n : ℕ} {x : Quad} : x ∈ quadSet n ↔
    0 < x.x ∧ 0 < x.y ∧ 0 < x.a ∧ 0 < x.b ∧ x.x*x.a + x.y*x.b = n := by
  rw [mem_quadSet]
  simp only [mul_comm x.x x.a, mul_comm x.y x.b]
  tauto

def step (x : Quad) : Quad :=
  if x.b < x.a then ⟨x.a - x.b, x.b, x.x, x.x + x.y⟩
  else ⟨x.a, x.b - x.a, x.x + x.y, x.y⟩

def previous (x : Quad) : Quad :=
  if x.x < x.y then ⟨x.a + x.b, x.b, x.x, x.y - x.x⟩
  else ⟨x.a, x.b + x.a, x.x - x.y, x.y⟩

theorem mem_step {n : ℕ} {x : Quad} (hx : x ∈ quadSet n) (hkl : x.a ≠ x.b) :
    step x ∈ quadSet n ∧ (step x).x ≠ (step x).y := by
  rcases x with ⟨k,l,a,b⟩
  obtain ⟨ha,hb,hk,hl,e⟩ := mem_coords.mp hx
  dsimp at *
  by_cases h' : l < k
  · simp only [step,if_pos h',mem_coords]
    refine ⟨⟨ha,by omega,by omega,hl,?_⟩,by omega⟩
    have : k = (k-l)+l := by omega
    calc a * (k-l) + (a+b) * l = a * ((k-l)+l) + b * l := by ring
         _ = n := by rw [←this,e]
  · simp only [step,if_neg h',mem_coords]
    refine ⟨⟨by omega,hb,hk,by omega,?_⟩,by omega⟩
    have : l = (l-k)+k := by omega
    calc (a+b)*k + b*(l-k) = a*k + b*((l-k)+k) := by ring
         _ = n := by rw [←this,e]

theorem mem_previous {n : ℕ} {x : Quad} (hx : x ∈ quadSet n) (hab : x.x ≠ x.y) :
    previous x ∈ quadSet n ∧ (previous x).a ≠ (previous x).b := by
  rcases x with ⟨k,l,a,b⟩
  obtain ⟨ha,hb,hk,hl,e⟩ := mem_coords.mp hx
  dsimp at *
  by_cases h' : a < b
  · simp only [previous,if_pos h',mem_coords]
    refine ⟨⟨ha,by omega,by omega,hl,?_⟩,by omega⟩
    have : b = b-a+a := by omega
    calc a*(k+l)+(b-a)*l = a*k+((b-a)+a)*l := by ring
         _ = n := by rw [←this,e]
  · have hba : b ≤ a := by omega
    simp only [previous,if_neg h',mem_coords]
    refine ⟨⟨by omega,hb,hk,by omega,?_⟩,by omega⟩
    have : a = a-b+b := by omega
    calc (a-b)*k+b*(l+k) = ((a-b)+b)*k+b*l := by ring
         _ = n := by rw [←this,e]

theorem previous_step {n : ℕ} {x : Quad} (hx : x ∈ quadSet n) (hkl : x.a ≠ x.b) :
    previous (step x) = x := by
  rcases x with ⟨k,l,a,b⟩
  obtain ⟨ha,hb,hk,hl,_⟩ := mem_coords.mp hx
  dsimp at *
  by_cases h : l < k
  · simp [step,previous,h,show a < a+b by omega,Nat.sub_add_cancel h.le]
  · simp [step,previous,h,show ¬a+b<b by omega,Nat.sub_add_cancel (show k≤l by omega)]

theorem step_previous {n : ℕ} {x : Quad} (hx : x ∈ quadSet n) (hab : x.x ≠ x.y) :
    step (previous x) = x := by
  rcases x with ⟨k,l,a,b⟩
  obtain ⟨ha,hb,hk,hl,_⟩ := mem_coords.mp hx
  dsimp at *
  by_cases h : a < b
  · simp [step,previous,h,show l < k+l by omega,Nat.add_sub_of_le h.le]
  · simp [step,previous,h,show ¬l+k<k by omega,Nat.sub_add_cancel (show b≤a by omega)]

theorem internal_sum {R : Type*} [AddCommMonoid R] (n : ℕ) (f : Quad → R) :
    ∑ x ∈ (quadSet n).filter (fun x => x.a ≠ x.b), f (step x) =
      ∑ x ∈ (quadSet n).filter (fun x => x.x ≠ x.y), f x := by
  apply Finset.sum_nbij' step previous
  · intro x hx
    obtain ⟨h₁,h₂⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr (mem_step h₁ h₂)
  · intro x hx
    obtain ⟨h₁,h₂⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr (mem_previous h₁ h₂)
  · intro x hx
    obtain ⟨h₁,h₂⟩ := Finset.mem_filter.mp hx
    exact previous_step h₁ h₂
  · intro x hx
    obtain ⟨h₁,h₂⟩ := Finset.mem_filter.mp hx
    exact step_previous h₁ h₂
  · intros; rfl

def quadratic {R : Type*} [CommRing R] (z : Quad) : R :=
  (z.x : R)^2 - (z.x : R) * z.y + (z.y : R)^2

theorem quadratic_step {R : Type*} [CommRing R] (z : Quad) :
    quadratic (R := R) (step z) = quadratic z + 2 * z.x * z.y := by
  by_cases h : z.b < z.a <;> simp [step, quadratic, h, Nat.cast_add] <;> ring

theorem telescope {R : Type*} [CommRing R] (n : ℕ) (w : Quad → R)
    (hw : ∀ z ∈ quadSet n, z.a ≠ z.b → w (step z) = w z) :
    (∑ z ∈ quadSet n, w z * (2 * (z.x : R) * z.y)) +
      (∑ z ∈ (quadSet n).filter (fun z => z.x = z.y), w z * quadratic z) =
      ∑ z ∈ (quadSet n).filter (fun z => z.a = z.b), w z * quadratic (step z) := by
  classical
  have hS := internal_sum n (fun z => w z * quadratic (R := R) z)
  have hmove :
      (∑ z ∈ (quadSet n).filter (fun z => z.a ≠ z.b), w z * quadratic (step z)) =
      ∑ z ∈ (quadSet n).filter (fun z => z.x ≠ z.y), w z * quadratic z := by
    rw [←hS]
    apply Finset.sum_congr rfl
    intro z hz
    obtain ⟨hm, h⟩ := Finset.mem_filter.mp hz
    rw [hw z hm h]
  have h₁ := Finset.sum_filter_add_sum_filter_not (s := quadSet n)
    (fun z => z.a = z.b) (fun z => w z * quadratic (step z))
  have h₂ := Finset.sum_filter_add_sum_filter_not (s := quadSet n)
    (fun z => z.x = z.y) (fun z => w z * quadratic z)
  have ht : (∑ z ∈ quadSet n, w z * quadratic (step z)) =
      (∑ z ∈ quadSet n, w z * quadratic z) + (∑ z ∈ quadSet n, w z * (2*(z.x : R)*z.y)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z hz
    rw [quadratic_step,mul_add]
  rw [hmove] at h₁
  linear_combination h₂ - h₁ - ht

private def roots (n : ℕ) := (quadSet n).filter (fun z => z.x = z.y)

private def rootPairs (n : ℕ) : Finset ((_g : ℕ) × ℕ) :=
  n.divisors.sigma (fun g => Finset.Ioo 0 (n/g))

private def rootPoint (n : ℕ) (t : (_g : ℕ) × ℕ) : Quad :=
  ⟨t.2, n / t.1 - t.2, t.1, t.1⟩

private def rootIndex (z : Quad) : (_g : ℕ) × ℕ := ⟨z.x,z.a⟩

private theorem root_mem {n : ℕ} {t : (_g : ℕ) × ℕ} (ht : t ∈ rootPairs n) :
    rootPoint n t ∈ roots n := by
  obtain ⟨hg,hi⟩ := Finset.mem_sigma.mp ht
  obtain ⟨hd,hn⟩ := Nat.mem_divisors.mp hg
  obtain ⟨hp,hlt⟩ := Finset.mem_Ioo.mp hi
  have hgpos := Nat.pos_of_mem_divisors hg
  apply Finset.mem_filter.mpr
  refine ⟨mem_quadSet.mpr ⟨hp,by dsimp [rootPoint]; omega,hgpos,hgpos,?_⟩,rfl⟩
  change t.2*t.1 + (n/t.1-t.2)*t.1 = n
  rw [←Nat.add_mul,Nat.add_sub_of_le hlt.le,Nat.div_mul_cancel hd]

private theorem root_decomp {n : ℕ} {z : Quad} (hz : z ∈ roots n) :
    z.x ∈ n.divisors ∧ z.a + z.b = n/z.x := by
  obtain ⟨hz,hxy⟩ := Finset.mem_filter.mp hz
  obtain ⟨ha,hb,hx,_,he⟩ := mem_quadSet.mp hz
  change z.x = z.y at hxy
  rw [← hxy, ← Nat.add_mul] at he
  have hn : n ≠ 0 := by rw [←he]; positivity
  refine ⟨Nat.mem_divisors.mpr ⟨⟨z.a+z.b,he.symm.trans (Nat.mul_comm _ _)⟩,hn⟩,?_⟩
  rw [←he,Nat.mul_div_cancel _ hx]

theorem sum_roots {R : Type*} [AddCommMonoid R] (n : ℕ) (f : Quad → R) :
    (∑ z ∈ (quadSet n).filter (fun z => z.x = z.y), f z) =
      ∑ g ∈ n.divisors, ∑ i ∈ Finset.Ioo 0 (n / g), f ⟨i,n/g-i,g,g⟩ := by
  classical
  change (∑ z ∈ roots n, f z) = _
  rw [Finset.sum_sigma']
  apply Finset.sum_nbij' rootIndex (rootPoint n)
  · intro z hz
    obtain ⟨hg,hd⟩ := root_decomp hz
    obtain ⟨hm,_⟩ := Finset.mem_filter.mp hz
    obtain ⟨ha,hb,_,_,_⟩ := mem_quadSet.mp hm
    exact Finset.mem_sigma.mpr ⟨hg,Finset.mem_Ioo.mpr ⟨ha,by dsimp [rootIndex]; omega⟩⟩
  · intro t ht; exact root_mem ht
  · intro z hz
    obtain ⟨hg,hd⟩ := root_decomp hz
    obtain ⟨hm,hxy⟩ := Finset.mem_filter.mp hz
    change z.x = z.y at hxy
    apply Quad.ext <;> dsimp [rootPoint,rootIndex] <;> omega
  · intro t _; rfl
  · intro z hz
    obtain ⟨_,hd⟩ := root_decomp hz
    obtain ⟨_,hxy⟩ := Finset.mem_filter.mp hz
    change z.x = z.y at hxy
    congr 1
    apply Quad.ext <;> dsimp [rootIndex] <;> omega

private def transpose (z : Quad) : Quad := ⟨z.x,z.y,z.a,z.b⟩

private theorem transpose_mem {n : ℕ} {z : Quad} (hz : z ∈ quadSet n) :
    transpose z ∈ quadSet n := by
  obtain ⟨ha,hb,hx,hy,he⟩ := mem_quadSet.mp hz
  refine mem_quadSet.mpr ⟨hx,hy,ha,hb,?_⟩
  simpa only [transpose,mul_comm z.x z.a,mul_comm z.y z.b] using he

theorem sum_leaves {R : Type*} [AddCommMonoid R] (n : ℕ) (f : Quad → R) :
    (∑ z ∈ (quadSet n).filter (fun z => z.a = z.b), f z) =
      ∑ g ∈ n.divisors, ∑ i ∈ Finset.Ioo 0 (n / g), f ⟨g,g,i,n/g-i⟩ := by
  classical
  calc
    _ = ∑ z ∈ (quadSet n).filter (fun z => z.x = z.y), f (transpose z) := by
      apply Finset.sum_nbij' transpose transpose
      · intro z hz
        obtain ⟨hm,he⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr ⟨transpose_mem hm,he⟩
      · intro z hz
        obtain ⟨hm,he⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr ⟨transpose_mem hm,he⟩
      · intros; rfl
      · intros; rfl
      · intros; rfl
    _ = _ := sum_roots n (fun z => f (transpose z))

end BalaChain

end

/- Filter -/
section

namespace BalaFilter
open Bala

def swap (u : Quad) : Quad := ⟨u.b, u.a, u.y, u.x⟩
def up (p : ℕ) (u : Quad) : Quad := ⟨u.a, p*u.b, p*u.x, u.y⟩
def down (p : ℕ) (u : Quad) : Quad := ⟨u.a, u.b/p, u.x/p, u.y⟩

def primitive (p N : ℕ) : Finset Quad :=
  (quadSet N).filter (fun u => ¬ (p ∣ u.x ∧ p ∣ u.y))
def badX (p N : ℕ) : Finset Quad :=
  (primitive p N).filter (fun u => p ∣ u.x)
def keepY (p N : ℕ) : Finset Quad :=
  (primitive p N).filter (fun u => ¬ p ∣ u.y)
def good (p N : ℕ) : Finset Quad :=
  (keepY p N).filter (fun u => ¬ p ∣ u.x)

@[simp] theorem mem_badX {u : Quad} {p N : ℕ} :
    u ∈ badX p N ↔ u ∈ quadSet N ∧ p ∣ u.x ∧ ¬p ∣ u.y := by
  simp only [badX, primitive, Finset.mem_filter]; tauto

@[simp] theorem mem_keepY {u : Quad} {p N : ℕ} :
    u ∈ keepY p N ↔ u ∈ quadSet N ∧ ¬p ∣ u.y := by
  simp only [keepY, primitive, Finset.mem_filter]; tauto

@[simp] theorem mem_good {u : Quad} {p N : ℕ} :
    u ∈ good p N ↔ u ∈ quadSet N ∧ ¬ p ∣ u.x ∧ ¬p ∣ u.y := by
  simp only [good, Finset.mem_filter, mem_keepY]; tauto

theorem badX_divides_b {u : Quad} {p N : ℕ} (hp : p.Prime)
    (h : u ∈ badX p (p*N)) : p ∣ u.b := by
  obtain ⟨hu,hx,hy⟩ := mem_badX.mp h
  obtain ⟨_,_,_,_,he⟩ := mem_quadSet.mp hu
  have hsum : p ∣ u.a*u.x + u.b*u.y := by rw [he]; exact dvd_mul_right p N
  have hax : p ∣ u.a*u.x := dvd_mul_of_dvd_right hx u.a
  exact (hp.dvd_mul.mp ((Nat.dvd_add_iff_right hax).mpr hsum)).resolve_right hy

theorem down_mem {u : Quad} {p N : ℕ} (hp : p.Prime)
    (h : u ∈ badX p (p*N)) : down p u ∈ keepY p N := by
  obtain ⟨vb,hvb⟩ := badX_divides_b hp h
  obtain ⟨hu,⟨vx,hvx⟩,hy⟩ := mem_badX.mp h
  obtain ⟨ha,hb,hx,hypos,he⟩ := mem_quadSet.mp hu
  apply mem_keepY.mpr
  refine ⟨mem_quadSet.mpr ?_,hy⟩
  simp only [down, hvb, hvx, Nat.mul_div_cancel_left _ hp.pos]
  refine ⟨ha,Nat.pos_of_ne_zero (fun hv => (Nat.ne_of_gt hb) (hvb.trans (by rw [hv,mul_zero]))),
    Nat.pos_of_ne_zero (fun hv => (Nat.ne_of_gt hx) (hvx.trans (by rw [hv,mul_zero]))),hypos,?_⟩
  apply Nat.eq_of_mul_eq_mul_left hp.pos
  calc p*(u.a*vx + vb*u.y) = u.a*(p*vx) + (p*vb)*u.y := by ring
       _ = p*N := by simpa only [hvb, hvx] using he

theorem up_mem {u : Quad} {p N : ℕ} (hp : p.Prime)
    (h : u ∈ keepY p N) : up p u ∈ badX p (p*N) := by
  obtain ⟨hu,hy⟩ := mem_keepY.mp h
  obtain ⟨ha,hb,hx,hyp,he⟩ := mem_quadSet.mp hu
  apply mem_badX.mpr
  refine ⟨mem_quadSet.mpr ?_, dvd_mul_right p u.x, hy⟩
  exact ⟨ha,Nat.mul_pos hp.pos hb,Nat.mul_pos hp.pos hx,hyp,
    by simp only [up]; rw [←he]; ring⟩

theorem up_down {u : Quad} {p N : ℕ} (hp : p.Prime)
    (h : u ∈ badX p (p*N)) : up p (down p u) = u := by
  obtain ⟨_,hx,_⟩ := mem_badX.mp h
  have hb := badX_divides_b hp h
  apply Quad.ext <;> simp [up, down, Nat.mul_div_cancel' hb, Nat.mul_div_cancel' hx]

theorem down_up (u : Quad) {p : ℕ} (hp : p.Prime) : down p (up p u) = u := by
  apply Quad.ext <;> simp [up, down, Nat.mul_div_cancel_left _ hp.pos]

theorem sum_badX_up {R : Type*} [AddCommMonoid R] {p N : ℕ}
    (hp : p.Prime) (w : Quad → R) :
    ∑ u ∈ badX p (p*N), w u = ∑ v ∈ keepY p N, w (up p v) := by
  apply Finset.sum_nbij' (down p) (up p)
  · exact fun _ h => down_mem hp h
  · exact fun _ h => up_mem hp h
  · exact fun _ h => up_down hp h
  · exact fun u _ => down_up u hp
  · exact fun _ h => congrArg w (up_down hp h).symm


theorem primitive_swap {p N : ℕ} {u : Quad} :
    swap u ∈ primitive p N ↔ u ∈ primitive p N := by
  simp only [primitive, Finset.mem_filter, mem_quadSet, swap, add_comm (u.b * u.y)]
  tauto

theorem sum_keepY_add_badX {p N : ℕ} (w : Quad → ℤ) {q : ℤ}
    (hswap : ∀ u ∈ primitive p N, w (swap u) ≡ w u [ZMOD q]) :
    (∑ u ∈ keepY p N, w u) + (∑ u ∈ badX p N, w u) ≡
    (∑ u ∈ primitive p N, w u) [ZMOD q] := by
  let badY := (primitive p N).filter (fun u => p ∣ u.y)
  have heq : ∑ u ∈ badX p N, w (swap u) = ∑ u ∈ badY, w u := by
    apply Finset.sum_nbij' swap swap
    · intro u h
      change swap u ∈ (primitive p N).filter _
      obtain ⟨hprim,hx⟩ := Finset.mem_filter.mp h
      exact Finset.mem_filter.mpr ⟨primitive_swap.mpr hprim,hx⟩
    · intro u h
      obtain ⟨hprim,hy⟩ := Finset.mem_filter.mp h
      exact Finset.mem_filter.mpr ⟨primitive_swap.mpr hprim,hy⟩
    · intro _ _; rfl
    · intro _ _; rfl
    · intro _ _; rfl
  have hmod : (∑ u ∈ badX p N, w u) ≡ (∑ u ∈ badY, w u) [ZMOD q] := by
    rw [←heq]
    exact Int.ModEq.sum fun u hu => (hswap u (Finset.mem_filter.mp hu).1).symm
  have hpart : (∑ u ∈ keepY p N,w u) + (∑ u ∈ badY,w u) = ∑ u ∈ primitive p N,w u := by
    rw [add_comm]; exact Finset.sum_filter_add_sum_filter_not _ _ _
  rw [←hpart]
  exact Int.ModEq.rfl.add hmod

theorem sum_good_add_badX {p N : ℕ} (w : Quad → ℤ) :
    (∑ u ∈ good p N, w u) + (∑ u ∈ badX p N, w u) = ∑ u ∈ keepY p N, w u := by
  have heq : badX p N = (keepY p N).filter (fun u => p ∣ u.x) := by
    ext u; simp only [mem_badX, Finset.mem_filter, mem_keepY]; tauto
  rw [heq, add_comm]
  exact Finset.sum_filter_add_sum_filter_not _ _ _

/-- Remove both exceptional residue axes, using determinant-preserving column scaling.
The weight is represented in integers so successive prime-power moduli can be compared. -/
theorem weighted_filter {p t : ℕ} (hp : p.Prime) (w : ℕ → Quad → ℤ)
    (hfull : ∀ s, (∑ u ∈ primitive p (p^s*t), w s u) ≡ 0 [ZMOD (p:ℤ)^s])
    (hswap : ∀ s u, u ∈ primitive p (p^s*t) →
      w s (swap u) ≡ w s u [ZMOD (p:ℤ)^s])
    (hscale : ∀ s u, u ∈ keepY p (p^s*t) →
      w (s+1) (up p u) ≡ (p:ℤ)*w s u [ZMOD (p:ℤ)^(s+1)]) (s : ℕ) :
    (∑ u ∈ good p (p^s*t), w s u) ≡ 0 [ZMOD (p:ℤ)^s] := by
  have hkeep (k : ℕ) (hb : (∑ u ∈ badX p (p^k*t), w k u) ≡ 0 [ZMOD (p:ℤ)^k]) :
      (∑ u ∈ keepY p (p^k*t), w k u) ≡ 0 [ZMOD (p:ℤ)^k] := by
    have h := (sum_keepY_add_badX (w k) (hswap k)).trans (hfull k)
    simpa using h.sub hb
  have hbad (k : ℕ) : (∑ u ∈ badX p (p^k*t), w k u) ≡ 0 [ZMOD (p:ℤ)^k] := by
    induction k with
    | zero => simp [Int.ModEq]
    | succ k ih =>
      have hN : p^(k+1)*t = p*(p^k*t) := by ring
      rw [hN, sum_badX_up hp (w (k+1))]
      have hh := Int.ModEq.sum (fun u hu => hscale k u hu)
      have hpk : p * (p:ℤ)^k = (p:ℤ)^(k+1) := by ring
      rw [← Finset.mul_sum] at hh
      exact hh.trans (by simpa only [hpk,mul_zero] using (hkeep k ih).mul_left' (c := (p:ℤ)))
  have h := (hkeep s (hbad s)).sub (hbad s)
  rwa [←sum_good_add_badX, add_sub_cancel_right, sub_zero] at h

end BalaFilter

end

/- SlopeBridge -/
section

namespace BalaSlope
open Bala

theorem weight_swap_congr {p s N : ℕ} (hp : p.Prime) (hn : p^s ∣ N)
    {u : Quad} (hu : u ∈ BalaFilter.primitive p N) :
    weight p s (BalaFilter.swap u) ≡ weight p s u [ZMOD (p : ℤ)^s] := by
  have : NeZero (p^s) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨hq,hu'⟩ := Finset.mem_filter.mp hu
  have he := (mem_quadSet.mp hq).2.2.2.2
  have hprim : ¬p ∣ u.y ∨ ¬p ∣ u.x := by tauto
  rw [←Nat.cast_pow, ←ZMod.intCast_eq_intCast_iff]
  rw [weight_cast, weight_cast]
  dsimp [BalaFilter.swap]
  rw [slope_swap hp hn he hprim]
  ring

theorem weight_up_congr {p s : ℕ} (hp : p.Prime) {u : Quad} (hy : ¬p ∣ u.y) :
    weight p (s+1) (BalaFilter.up p u) ≡
      (p : ℤ)*weight p s u [ZMOD (p:ℤ)^(s+1)] := by
  have : NeZero (p^s) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have : NeZero (p^(s+1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have h := slope_up (s:=s) hp hy
  let v := BalaFilter.up p u
  have hv : (((slope p (s+1) v).val : ℤ) : ZMod (p^s)) =
      (((slope p s u).val : ℤ) : ZMod (p^s)) := by
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val, ZMod.castHom_apply,
      ← ZMod.natCast_val, v, BalaFilter.up] using h
  have he := (ZMod.intCast_eq_intCast_iff ..).mp hv
  have he' := ((he.pow 4).mul_right (u.x : ℤ)).mul_right (u.y : ℤ)
  have hmul := he'.mul_left' (c := (p : ℤ))
  convert hmul using 1 <;> try dsimp [weight,BalaFilter.up,v] <;> push_cast <;> ring

theorem slope_step {p s N : ℕ} (hp : p.Prime) (hn : p^s ∣ N)
    {u : Quad} (hq : u ∈ quadSet N) (_hne : u.a ≠ u.b) :
    slope p s (BalaChain.step u) = slope p s u := by
  have he := (mem_quadSet.mp hq).2.2.2.2
  by_cases h : p ∣ u.x ∧ p ∣ u.y
  · obtain ⟨hx,hy⟩ := h
    unfold BalaChain.step
    split <;> simp [slope,hx,hy,dvd_add hx hy]
  have hprim : ¬p ∣ u.y ∨ ¬p ∣ u.x := by tauto
  obtain ⟨ha,hb⟩ := slope_compatible hp hn he hprim
  by_cases hlt : u.b < u.a
  · simp only [BalaChain.step, if_pos hlt]
    apply slope_unique hp
    · change ¬p ∣ u.x+u.y ∨ ¬p ∣ u.x
      by_cases hx : p ∣ u.x
      · left; intro hz; exact h ⟨hx,(Nat.dvd_add_iff_right hx).mpr hz⟩
      · exact Or.inr hx
    · constructor
      · change _ * ((u.x+u.y:ℕ):ZMod (p^s)) = ((u.a-u.b:ℕ):ZMod (p^s))
        rw [Nat.cast_add,Nat.cast_sub hlt.le,mul_add,ha,hb]; ring
      · exact hb
  · simp only [BalaChain.step, if_neg hlt]
    apply slope_unique hp
    · change ¬p ∣ u.y ∨ ¬p ∣ u.x+u.y
      by_cases hy : p ∣ u.y
      · right; intro hz; exact h ⟨(Nat.dvd_add_iff_left hy).mpr hz,hy⟩
      · exact Or.inl hy
    · constructor
      · exact ha
      · change _ * ((u.x+u.y:ℕ):ZMod (p^s)) = -((u.b-u.a:ℕ):ZMod (p^s))
        rw [Nat.cast_add,Nat.cast_sub (by omega : u.a ≤ u.b),mul_add,ha,hb]; ring

end BalaSlope

end

/- Terminal -/
section

namespace BalaTerminal

open Finset

/-- Reindex a residue sum by multiplication by a unit. The multiplier on the
summand can be cancelled if its difference from one is also a unit. -/
private theorem sum_dilation {q : ℕ} [NeZero q]
    (F : ZMod q → ZMod q) (u : (ZMod q)ˣ) (c : ZMod q) (hc : IsUnit (c - 1))
    (h : ∀ x, c * F ((u : ZMod q) * x) = F x) :
    ∑ x : ZMod q, F x = 0 := by
  have eq₁ := Equiv.sum_comp u.mulLeft F
  change (∑ x : ZMod q, F ((u : ZMod q) * x)) = ∑ x : ZMod q, F x at eq₁
  have eq₂ : c * (∑ x : ZMod q, F x) = ∑ x : ZMod q, F x := by
    calc
      _ = c * (∑ x : ZMod q, F ((u : ZMod q) * x)) := by rw [eq₁]
      _ = _ := by simp only [mul_sum, h]
  have hc0 : (c - 1) * (∑ x : ZMod q, F x) = 0 := by rw [sub_mul, one_mul, eq₂, sub_self]
  simpa using (hc.mul_right_eq_zero.mp hc0)

private theorem range_to_residues (q : ℕ) [NeZero q] (F : ZMod q → ZMod q) :
    (∑ x ∈ range q, F x) = ∑ x : ZMod q, F x := by
  rw [← Fin.sum_univ_eq_sum_range]
  convert (ZMod.finEquiv q).toEquiv.sum_comp F using 1
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q => exact Fin.natCast_eq_mk _

/-- A full residue block with sum zero contributes zero at any multiple. -/
theorem multiple_blocks {q D : ℕ} [NeZero q] (hq : q ∣ D) (F : ZMod q → ZMod q)
    (hz : (∑ x : ZMod q, F x) = 0) : (∑ x ∈ range D, F x) = 0 := by
  obtain ⟨k, rfl⟩ := hq
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, sum_range_add, ih, zero_add]
    simpa using (range_to_residues q F).trans hz

noncomputable def invSq {q : ℕ} (x : ZMod q) : ZMod q := by
  classical exact if IsUnit x then x⁻¹ ^ 2 else 0

/-- The complete inverse-square sum over units vanishes at every p-power, p≥7. -/
theorem sum_invSq {p l : ℕ} (hp : Nat.Prime p) (h7 : 7 ≤ p) (hl : 0 < l) :
    letI : NeZero (p ^ l) := ⟨pow_ne_zero _ hp.ne_zero⟩
    (∑ x : ZMod (p ^ l), invSq x) = 0 := by
  letI : NeZero (p ^ l) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hu : Nat.Coprime 2 (p ^ l) := hp.coprime_pow_of_not_dvd
    (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
  let u := ZMod.unitOfCoprime 2 hu
  apply sum_dilation invSq u 4
  · norm_num
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp hl (a := 3)).2
      (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
  intro x
  classical
  by_cases hx : IsUnit x
  · obtain ⟨v, rfl⟩ := hx
    have huv : IsUnit ((u : ZMod (p ^ l)) * v) := u.isUnit.mul v.isUnit
    simp only [invSq, if_pos huv, if_pos v.isUnit]
    rw [← Units.val_mul, ZMod.inv_coe_unit, ZMod.inv_coe_unit, mul_inv_rev]
    simp only [Units.val_mul]
    have hh : (4 : ZMod (p ^ l)) = (↑u : ZMod (p ^ l)) ^ 2 := by
      dsimp [u, ZMod.coe_unitOfCoprime]
      norm_num
    rw [hh]
    calc
      _ = ((u : ZMod (p ^ l)) * ↑u⁻¹) ^ 2 * (↑v⁻¹ : ZMod (p ^ l)) ^ 2 := by ring
      _ = _ := by simp
  · have hux : ¬ IsUnit ((u : ZMod (p ^ l)) * x) := by
      intro h
      exact hx (isUnit_of_mul_isUnit_right h)
    simp [invSq, hx, hux]

/-- Same sum over the original natural indices, including 0 with contribution 0. -/
theorem sum_invSq_range {p l D : ℕ} (hp : Nat.Prime p) (h7 : 7 ≤ p)
    (hl : 0 < l) (hD : p ^ l ∣ D) :
    (∑ x ∈ range D, if p ∣ x then 0 else ((x : ZMod (p ^ l))⁻¹) ^ 2) = 0 := by
  classical
  letI : NeZero (p ^ l) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have H := multiple_blocks hD invSq (sum_invSq hp h7 hl)
  convert H using 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : p ∣ x <;> simp [invSq, ZMod.isUnit_natCast_iff_not_dvd_pow hp hl, h]

/-- The initial endpoint involves a fourth power over a complete period. -/
theorem sum_fourth_range {p l D : ℕ} (hp : Nat.Prime p) (h7 : 7 ≤ p)
    (hl : 0 < l) (hD : p ^ l ∣ D) :
    (∑ x ∈ range D, (x : ZMod (p ^ l)) ^ 4) = 0 := by
  letI : NeZero (p ^ l) := ⟨pow_ne_zero _ hp.ne_zero⟩
  apply multiple_blocks hD (fun x => x ^ 4)
  have hu : Nat.Coprime 2 (p ^ l) := hp.coprime_pow_of_not_dvd
    (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
  let u := ZMod.unitOfCoprime 2 hu
  apply sum_dilation _ u⁻¹ 16
  · norm_num
    apply (ZMod.isUnit_natCast_iff_not_dvd_pow hp hl (a := 15)).2
    change ¬p ∣ 3 * 5
    exact fun h => (hp.dvd_mul.mp h).elim
      (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
      (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
  · intro x
    have hh : (16 : ZMod (p ^ l)) = (↑u : ZMod (p ^ l)) ^ 4 := by
      dsimp [u, ZMod.coe_unitOfCoprime]
      norm_num
    rw [hh]
    calc
      _ = ((u : ZMod (p ^ l)) * ↑u⁻¹) ^ 4 * x ^ 4 := by ring
      _ = _ := by simp

private def recipSum (p s D : ℕ) : ZMod (p^s) :=
  ∑ x ∈ range D, if p ∣ x then 0 else ((x : ZMod (p^s))⁻¹)^2

private theorem recipSum_reduce {p s D : ℕ} (hp : p.Prime)
    (f : ZMod (p^(s+1)) →+* ZMod (p^s)) :
    f (recipSum p (s+1) D) = recipSum p s D := by
  unfold recipSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : p ∣ x
  · simp [hx]
  simp only [hx, if_false, map_pow]
  congr 1
  symm
  apply ZMod.inv_eq_of_mul_eq_one
  have he := congrArg f (ZMod.coe_mul_inv_eq_one x
    (hp.coprime_pow_of_not_dvd hx : Nat.Coprime x (p^(s+1))))
  simpa using he

private theorem weightedAux {p s D g : ℕ} (hp : p.Prime) (h7 : 7 ≤ p)
    (hD : p^s ∣ g*D) : (g : ZMod (p^s)) * recipSum p s D = 0 := by
  induction s generalizing g with
  | zero =>
    letI : Subsingleton (ZMod (p^0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  | succ s ih =>
    by_cases hg : p ∣ g
    · obtain ⟨k,rfl⟩ := hg
      have hlow : p^s ∣ k*D := Nat.dvd_of_mul_dvd_mul_left hp.pos
        (by simpa only [pow_succ', Nat.mul_assoc] using hD)
      let f := ZMod.castHom (pow_dvd_pow p (Nat.le_succ s)) (ZMod (p^s))
      let z : ZMod (p^(s+1)) := (k : ZMod (p^(s+1))) * recipSum p (s+1) D
      have hmap : f z = 0 := by
        simp only [z, map_mul, map_natCast, recipSum_reduce hp f]
        exact ih hlow
      letI : NeZero (p^(s+1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
      have hd : p^s ∣ z.val := (ZMod.natCast_eq_zero_iff _ _).mp (by
        have eqv := congrArg f (ZMod.natCast_zmod_val z)
        rwa [map_natCast, hmap] at eqv)
      have hpz : (p : ZMod (p^(s+1))) * z = 0 := by
        rw [← ZMod.natCast_zmod_val z, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
        exact (pow_succ' p s).dvd.trans (Nat.mul_dvd_mul_left p hd)
      simpa only [Nat.cast_mul, mul_assoc, z] using hpz
    · have hq := (hp.coprime_pow_of_not_dvd (m := s+1) hg).symm.dvd_of_dvd_mul_left hD
      change _ * (∑ x ∈ range D, if p ∣ x then 0 else ((x : ZMod (p^(s+1)))⁻¹)^2) = _
      rw [sum_invSq_range hp h7 (Nat.zero_lt_succ _) hq, mul_zero]

/-- Multiplying by g supplies any powers of p missing from the block length. -/
theorem weighted_invSq_range {p s D g : ℕ} (hp : p.Prime) (h7 : 7 ≤ p)
    (hD : p^s ∣ g * D) :
    (g : ZMod (p^s)) * (∑ x ∈ range D, if p ∣ x then 0 else ((x : ZMod (p^s))⁻¹)^2) = 0 :=
  weightedAux hp h7 hD

private theorem sum_Ioo_eq_range {A : Type*} [AddCommMonoid A] (f : ℕ → A)
    (D : ℕ) (hf : f 0 = 0) : (∑ x ∈ Ioo 0 D, f x) = ∑ x ∈ range D, f x := by
  apply Finset.sum_subset
  · intro x hx
    exact mem_range.mpr (mem_Ioo.mp hx).2
  · intro x hx h
    have hx0 : x = 0 := by
      by_contra ht
      exact h (mem_Ioo.mpr ⟨Nat.pos_of_ne_zero ht, mem_range.mp hx⟩)
    simpa [hx0] using hf

theorem weighted_invSq_Ioo {p s D g : ℕ} (hp : p.Prime) (h7 : 7 ≤ p)
    (hD : p^s ∣ g * D) :
    (g : ZMod (p^s)) * (∑ x ∈ Ioo 0 D, if p ∣ x then 0 else ((x : ZMod (p^s))⁻¹)^2) = 0 := by
  rw [sum_Ioo_eq_range _ D (by simp)]
  exact weighted_invSq_range hp h7 hD

theorem sum_fourth_Ioo {p l D : ℕ} (hp : p.Prime) (h7 : 7 ≤ p)
    (hl : 0 < l) (hD : p ^ l ∣ D) :
    (∑ x ∈ Ioo 0 D, (x : ZMod (p ^ l)) ^ 4) = 0 := by
  rw [sum_Ioo_eq_range _ D (by simp)]
  exact sum_fourth_range hp h7 hl hD

end BalaTerminal

end

/- Boundary -/
section

namespace BalaBoundary

open Bala BalaChain BalaSlope BalaTerminal

theorem initial {p s n : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (hs : 0 < s)
    (hn : p^s ∣ n) :
    (∑ z ∈ (quadSet n).filter (fun z => z.x = z.y),
      (BalaSlope.slope p s z)^4 * quadratic z) = 0 := by
  rw [sum_roots]
  apply Finset.sum_eq_zero
  intro g hg
  have hgd := Nat.dvd_of_mem_divisors hg
  have hprod : p^s ∣ g * (n/g) := by rw [Nat.mul_div_cancel' hgd]; exact hn
  by_cases hpu : p ∣ g
  · simp [BalaSlope.slope,hpu]
  · have hd := (hp.coprime_pow_of_not_dvd (m:=s) hpu).symm.dvd_of_dvd_mul_left hprod
    calc
      _ = (∑ i ∈ Finset.Ioo 0 (n/g), (i : ZMod (p^s))^4) *
            ((g : ZMod (p^s))⁻¹^4 * g^2) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [BalaSlope.slope,if_pos hpu,quadratic]
        ring
      _ = 0 := by rw [sum_fourth_Ioo hp h7 hs hd,zero_mul]

private theorem weighted_quadratic {R : Type*} [CommRing R] (g D i j : R)
    (hD : g*D=0) (hij : i*j=1) :
    (-g*j)^4 * (D^2-D*(D-i)+(D-i)^2) = g^4*j^2 := by
  calc _ = (g*D)*(g^3*j^4)*(D-i) + g^4*j^2*(i*j)^2 := by ring
       _ = _ := by rw [hD,hij]; ring

private theorem leaf_value {p s g D i : ℕ} (hp : p.Prime) (hi : i < D)
    (hD : p^s ∣ g*D) :
    (BalaSlope.slope p s ⟨g,g,i,D-i⟩)^4 * quadratic (step ⟨g,g,i,D-i⟩) =
      (g : ZMod (p^s))^4 * (if p ∣ i then 0 else ((i : ZMod (p^s))⁻¹)^2) := by
  have hsum : i + (D-i) = D := Nat.add_sub_of_le hi.le
  have hzero : (g : ZMod (p^s)) * (D : ZMod (p^s))=0 := by
    rw [←Nat.cast_mul]
    exact (ZMod.natCast_eq_zero_iff ..).mpr hD
  by_cases hpi : p ∣ i
  · by_cases hpy : p ∣ D-i
    · simp [BalaSlope.slope,hpi,hpy]
    · have hnD : ¬p ∣ D := by
        intro hh
        rw [← hsum] at hh
        exact hpy ((Nat.dvd_add_right hpi).mp hh)
      have hg := (hp.coprime_pow_of_not_dvd (m:=s) hnD).symm.dvd_of_dvd_mul_right hD
      have hgz : (g : ZMod (p^s)) = 0 := (ZMod.natCast_eq_zero_iff ..).mpr hg
      simp [BalaSlope.slope,hpi,hpy,hgz]
  · have he : g*i + g*(D-i) = g*D := by rw [←Nat.mul_add, hsum]
    have hcompat := slope_compatible (u:=⟨g,g,i,D-i⟩) hp hD he (Or.inr hpi)
    have hiunit := ZMod.coe_mul_inv_eq_one i (hp.coprime_pow_of_not_dvd (m:=s) hpi)
    have hsl : BalaSlope.slope p s ⟨g,g,i,D-i⟩ = -(g : ZMod (p^s)) * (i : ZMod (p^s))⁻¹ := by
      calc _ = BalaSlope.slope p s ⟨g,g,i,D-i⟩ * ((i : ZMod (p^s)) * (i : ZMod (p^s))⁻¹) := by rw [hiunit,mul_one]
           _ = _ := by rw [←mul_assoc, hcompat.2]
    rw [hsl,if_neg hpi]
    simp only [step, lt_self_iff_false, if_false, quadratic, hsum, Nat.cast_sub hi.le]
    exact weighted_quadratic _ _ _ _ hzero hiunit

theorem terminal {p s n : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (hn : p^s ∣ n) :
    (∑ z ∈ (quadSet n).filter (fun z => z.a = z.b),
      (BalaSlope.slope p s z)^4 * quadratic (step z)) = 0 := by
  rw [sum_leaves]
  apply Finset.sum_eq_zero
  intro g hg
  have hgd := Nat.dvd_of_mem_divisors hg
  have hD : p^s ∣ g*(n/g) := by rw [Nat.mul_div_cancel' hgd]; exact hn
  calc
    _ = (g : ZMod (p^s))^4 * ∑ i ∈ Finset.Ioo 0 (n/g),
        if p ∣ i then 0 else ((i : ZMod (p^s))⁻¹)^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact leaf_value hp (Finset.mem_Ioo.mp hi).2 hD
    _ = (g : ZMod (p^s))^3 * ((g : ZMod (p^s)) * ∑ i ∈ Finset.Ioo 0 (n/g),
        if p ∣ i then 0 else ((i : ZMod (p^s))⁻¹)^2) := by ring
    _ = 0 := by rw [weighted_invSq_Ioo hp h7 hD,mul_zero]

end BalaBoundary

end

/- Estimate -/
section

namespace BalaEstimate

open Bala BalaSlope BalaFilter

theorem primitive_sum {p s N : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (hn : p^s ∣ N) :
    (∑ u ∈ primitive p N, weight p s u) ≡ 0 [ZMOD (p:ℤ)^s] := by
  cases s with
  | zero => simp [Int.ModEq]
  | succ k =>
    let s := k+1
    have : NeZero (p^s) := ⟨pow_ne_zero _ hp.ne_zero⟩
    change (∑ u ∈ primitive p N, weight p s u) ≡ 0 [ZMOD (p:ℤ)^s]
    rw [← Nat.cast_pow, ← ZMod.intCast_eq_intCast_iff]
    push_cast
    simp only [weight_cast]
    have hT := BalaChain.telescope (R:=ZMod (p^s)) N (fun u => (BalaSlope.slope p s u)^4)
      (fun u hu h => congrArg (fun t : ZMod (p^s) => t^4) (slope_step hp hn hu h))
    rw [BalaBoundary.initial hp h7 (Nat.succ_pos k) hn,add_zero,
      BalaBoundary.terminal hp h7 hn] at hT
    have htot : (2 : ZMod (p^s)) * ∑ u ∈ quadSet N, (BalaSlope.slope p s u)^4*u.x*u.y = 0 := by
      rw [Finset.mul_sum]
      convert hT using 1
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    have ht : IsUnit (2 : ZMod (p^s)) := by
      have hcop := hp.coprime_pow_of_not_dvd (m:=s) (show ¬p ∣ 2 by
        intro h; have := Nat.le_of_dvd (by decide : 0 < 2) h; omega)
      exact (ZMod.isUnit_iff_coprime 2 (p^s)).2 hcop
    have hall := ht.mul_left_cancel (show (2 : ZMod (p^s)) *
      (∑ u ∈ quadSet N, (BalaSlope.slope p s u)^4*u.x*u.y) = 2*0 by simpa using htot)
    rw [←hall]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro u hu hnot
    have hh : p ∣ u.x ∧ p ∣ u.y := by
      by_contra h; exact hnot (Finset.mem_filter.mpr ⟨hu,h⟩)
    simp [BalaSlope.slope,hh.1,hh.2]

theorem good_sum {p s N : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (hn : p^s ∣ N) :
    (∑ u ∈ good p N, weight p s u) ≡ 0 [ZMOD (p:ℤ)^s] := by
  obtain ⟨t,rfl⟩ := hn
  apply weighted_filter hp
  · intro j; exact primitive_sum hp h7 (dvd_mul_right _ _)
  · intro j u hu; exact weight_swap_congr hp (dvd_mul_right _ _) hu
  · intro j u hu; exact weight_up_congr hp (mem_keepY.mp hu).2

end BalaEstimate

end

/- Cartier -/
section

namespace BalaFrob

open PowerSeries Finset

noncomputable def cartier {R : Type*} [CommRing R] (p : ℕ) (f : PowerSeries R) :
    PowerSeries R := mk fun n => coeff (p*n) f

lemma coeff_cartier {R : Type*} [CommRing R] (p : ℕ) (f : PowerSeries R) (n : ℕ) :
    coeff n (cartier p f) = coeff (p*n) f := coeff_mk _ _

lemma cartier_expand_mul {R : Type*} [CommRing R] (p : ℕ) (hp : p ≠ 0)
    (f b : PowerSeries R) : cartier p (expand p hp f * b) = f * cartier p b := by
  classical
  ext n
  rw [coeff_cartier, coeff_mul, coeff_mul]
  let big := Finset.HasAntidiagonal.antidiagonal (p*n)
  let hit := big.filter (fun t : ℕ × ℕ => p ∣ t.1)
  let F := fun t : ℕ × ℕ => coeff t.1 (expand p hp f) * coeff t.2 b
  change ∑ t ∈ big, F t = _
  calc
    _ = ∑ t ∈ hit, F t := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro t ht hnone
      have hnd : ¬p ∣ t.1 := fun h => hnone (Finset.mem_filter.mpr ⟨ht, h⟩)
      simp [F, coeff_expand_of_not_dvd _ _ _ hnd]
    _ = _ := by
      symm
      refine Finset.sum_bij' (fun t _ => (p*t.1,p*t.2)) (fun t _ => (t.1/p,t.2/p))
        (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_)
        (fun t ht => ?_)
      · have ha := Finset.HasAntidiagonal.mem_antidiagonal.mp ht
        exact Finset.mem_filter.mpr ⟨Finset.HasAntidiagonal.mem_antidiagonal.mpr (by rw [← Nat.mul_add, ha]),
          dvd_mul_right _ _⟩
      · obtain ⟨hbig, h1⟩ := Finset.mem_filter.mp ht
        have ha := Finset.HasAntidiagonal.mem_antidiagonal.mp hbig
        have h2 : p ∣ t.2 := (Nat.dvd_add_iff_right h1).mpr (ha ▸ dvd_mul_right _ _)
        apply Finset.HasAntidiagonal.mem_antidiagonal.mpr
        apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp)
        rw [Nat.mul_add, Nat.mul_div_cancel' h1, Nat.mul_div_cancel' h2, ha]
      · simp [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp)]
      · obtain ⟨hbig, h1⟩ := Finset.mem_filter.mp ht
        have ha := Finset.HasAntidiagonal.mem_antidiagonal.mp hbig
        have h2 : p ∣ t.2 := (Nat.dvd_add_iff_right h1).mpr (ha ▸ dvd_mul_right _ _)
        simp [Nat.mul_div_cancel' h1, Nat.mul_div_cancel' h2]
      · simp [F, coeff_cartier, coeff_expand_mul]

end BalaFrob

end

/- Convolution -/
section

namespace BalaConv

open Bala PowerSeries

noncomputable def term (p a x : ℕ) : ℚ :=
  if ¬p ∣ x then (a : ℚ)^2 / (x : ℚ) else 0

noncomputable def L (p : ℕ) : PowerSeries ℚ :=
  mk (fun n => ∑ x ∈ n.divisors, term p (n/x) x)

theorem coeff_L (p n : ℕ) : coeff n (L p) =
    ∑ x ∈ n.divisors, (if ¬p ∣ x then ((n/x : ℕ) : ℚ)^2 / (x : ℚ) else 0) := by
  simp [L, term]

theorem coeff_L_anti (p n : ℕ) : coeff n (L p) =
    ∑ d ∈ n.divisorsAntidiagonal, term p d.1 d.2 := by
  rw [← Nat.map_div_left_divisors, Finset.sum_map]
  simp only [L,coeff_mk]
  rfl

abbrev QuadIndex := (_i : ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))

def idxSet (N : ℕ) : Finset QuadIndex :=
  (Finset.HasAntidiagonal.antidiagonal N).sigma (fun i : ℕ × ℕ =>
    i.1.divisorsAntidiagonal ×ˢ i.2.divisorsAntidiagonal)

def toQuad (t : QuadIndex) : Quad := ⟨t.2.1.1,t.2.2.1,t.2.1.2,t.2.2.2⟩
def ofQuad (u : Quad) : QuadIndex := ⟨(u.a*u.x,u.b*u.y),((u.a,u.x),(u.b,u.y))⟩

lemma toQuad_mem {N} {t : QuadIndex} (ht : t ∈ idxSet N) : toQuad t ∈ quadSet N := by
  rcases t with ⟨⟨i,j⟩,⟨a,x⟩,⟨b,y⟩⟩
  obtain ⟨hij, hm⟩ := Finset.mem_sigma.mp ht
  obtain ⟨hx,hy⟩ := Finset.mem_product.mp hm
  obtain ⟨hax,hi⟩ := Nat.mem_divisorsAntidiagonal.mp hx
  obtain ⟨hby,hj⟩ := Nat.mem_divisorsAntidiagonal.mp hy
  have hpos := Nat.ne_zero_of_mem_divisorsAntidiagonal hx
  have hpos' := Nat.ne_zero_of_mem_divisorsAntidiagonal hy
  simpa [toQuad,hax,hby, Nat.pos_of_ne_zero hpos.1, Nat.pos_of_ne_zero hpos.2,
    Nat.pos_of_ne_zero hpos'.1, Nat.pos_of_ne_zero hpos'.2] using Finset.HasAntidiagonal.mem_antidiagonal.mp hij

lemma ofQuad_mem {N} {u : Quad} (hu : u ∈ quadSet N) : ofQuad u ∈ idxSet N := by
  obtain ⟨ha,hb,hx,hy,eq⟩ := mem_quadSet.mp hu
  exact Finset.mem_sigma.mpr ⟨Finset.HasAntidiagonal.mem_antidiagonal.mpr eq,
    Finset.mem_product.mpr ⟨Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, (Nat.mul_pos ha hx).ne'⟩,
      Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, (Nat.mul_pos hb hy).ne'⟩⟩⟩

lemma ofQuad_toQuad {N} {t : QuadIndex} (ht : t ∈ idxSet N) : ofQuad (toQuad t) = t := by
  rcases t with ⟨⟨i,j⟩,⟨a,x⟩,⟨b,y⟩⟩
  obtain ⟨hx,hy⟩ := Finset.mem_product.mp (Finset.mem_sigma.mp ht).2
  have e1 : a*x=i := (Nat.mem_divisorsAntidiagonal.mp hx).1
  have e2 : b*y=j := (Nat.mem_divisorsAntidiagonal.mp hy).1
  subst i; subst j; rfl

theorem L_sq_coeff_raw (p N : ℕ) : coeff N (L p ^ 2) =
    ∑ u ∈ quadSet N, term p u.a u.x * term p u.b u.y := by
  rw [pow_two, coeff_mul]
  simp_rw [coeff_L_anti, Finset.sum_mul_sum]
  calc
    _ = ∑ t ∈ idxSet N, term p (toQuad t).a (toQuad t).x *
          term p (toQuad t).b (toQuad t).y := by
        rw [idxSet, Finset.sum_sigma]
        apply Finset.sum_congr rfl
        intro i hi
        exact (Finset.sum_product i.1.divisorsAntidiagonal i.2.divisorsAntidiagonal
          (fun axy : (ℕ × ℕ) × (ℕ × ℕ) => term p axy.1.1 axy.1.2 * term p axy.2.1 axy.2.2)).symm
    _ = _ := by
      apply Finset.sum_nbij' toQuad ofQuad
      · exact fun i hi => toQuad_mem hi
      · exact fun u hu => ofQuad_mem hu
      · exact fun i hi => ofQuad_toQuad hi
      · intro u hu; rfl
      · intro u hu; rfl

theorem L_sq_coeff (p N : ℕ) : coeff N (L p ^ 2) =
    ∑ u ∈ (quadSet N).filter (fun u => ¬p ∣ u.x ∧ ¬p ∣ u.y),
      (u.a : ℚ)^2 * (u.b : ℚ)^2 / ((u.x : ℚ) * (u.y : ℚ)) := by
  rw [L_sq_coeff_raw, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hx : p ∣ u.x <;> by_cases hy : p ∣ u.y <;> simp [term, hx, hy, div_eq_mul_inv]
  ring

end BalaConv

end

/- LocalLog -/
section

namespace BalaConv

open PowerSeries BalaFrob

lemma coeff_L_local (p n : ℕ) [hp : Fact p.Prime] : coeff n (L p) ∈ localRing p := by
  rw [coeff_L]
  apply (localRing p).sum_mem
  intro x hx
  by_cases ht : p ∣ x
  · simp [ht]
  · rw [if_pos ht]
    have hCast : (((n/x)^2 : ℕ) : ℚ) = ((n/x : ℕ) : ℚ)^2 := Nat.cast_pow ..
    rw [← hCast]
    exact unit_divisor_mem _ _ ht

noncomputable def localL (p : ℕ) [Fact p.Prime] : PowerSeries (localRing p) :=
  mk fun n => ⟨coeff n (L p), coeff_L_local p n⟩

theorem map_localL (p : ℕ) [Fact p.Prime] :
    PowerSeries.map (localRing p).subtype (localL p) = L p := by
  ext n
  rw [coeff_map]
  simp only [localL, coeff_mk, Subring.subtype_apply]

end BalaConv

end

/- RationalLift -/
section

namespace BalaConv

open BalaFrob

/-- Simultaneously clear all rational denominators and every residue denominator. -/
lemma common_fraction {α : Type*} [DecidableEq α] {p s : ℕ} (hp : p.Prime)
    (T : Finset α) (a b : α → ℕ) (z : α → ZMod (p^s))
    (hu : ∀ i ∈ T, ¬p ∣ b i)
    (hz : ∀ i ∈ T, z i * (b i : ZMod (p^s)) = (a i : ZMod (p^s))) :
    ∃ A B : ℕ, ¬p ∣ B ∧
      (∑ i ∈ T, (a i : ℚ)/(b i : ℚ)) = (A : ℚ)/(B : ℚ) ∧
      (∑ i ∈ T, z i) * (B : ZMod (p^s)) = (A : ZMod (p^s)) := by
  classical
  induction T using Finset.induction with
  | empty => exact ⟨0,1,hp.not_dvd_one,by simp,by simp⟩
  | @insert i T hi ih =>
    have hTu : ∀ j ∈ T, ¬p ∣ b j := fun j hj => hu j (Finset.mem_insert_of_mem hj)
    have hTz : ∀ j ∈ T, z j * (b j : ZMod (p^s)) = (a j : ZMod (p^s)) :=
      fun j hj => hz j (Finset.mem_insert_of_mem hj)
    obtain ⟨A,B,hB,hR,hZ⟩ := ih hTu hTz
    have hbi := hu i (Finset.mem_insert_self _ _)
    have hzi := hz i (Finset.mem_insert_self _ _)
    refine ⟨a i * B + A * b i, b i * B, fun h => (hp.dvd_mul.mp h).elim hbi hB, ?_, ?_⟩
    · have hbi0 : (b i : ℚ) ≠ 0 := by exact_mod_cast (fun (he : b i = 0) => hbi (he ▸ dvd_zero p))
      have hB0 : (B : ℚ) ≠ 0 := by exact_mod_cast (fun (he : B = 0) => hB (he ▸ dvd_zero p))
      rw [Finset.sum_insert hi, hR]
      push_cast
      field_simp
    · rw [Finset.sum_insert hi]
      push_cast
      calc
        _ = (z i * (b i : ZMod (p^s))) * B +
            ((∑ j ∈ T, z j) * B) * b i := by ring
        _ = _ := by rw [hzi,hZ]

lemma local_of_residue_sum_zero {α : Type*} [DecidableEq α] {p s : ℕ}
    [hp : Fact p.Prime] (T : Finset α) (a b : α → ℕ) (z : α → ZMod (p^s))
    (hu : ∀ i ∈ T, ¬p ∣ b i)
    (hz : ∀ i ∈ T, z i * (b i : ZMod (p^s)) = (a i : ZMod (p^s)))
    (h : (∑ i ∈ T, z i) = 0) :
    (∑ i ∈ T, (a i : ℚ)/(b i : ℚ)) / (p : ℚ)^s ∈ localRing p := by
  obtain ⟨A,B,hB,hR,hZ⟩ := common_fraction hp.out T a b z hu hz
  rw [h,zero_mul] at hZ
  obtain ⟨k,hk⟩ := (ZMod.natCast_eq_zero_iff ..).mp hZ.symm
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [hR, hk]
  push_cast
  convert unit_divisor_mem k B hB using 1
  field_simp

end BalaConv

end

/- SquareLocal -/
section

namespace BalaConv

open PowerSeries Bala BalaFrob BalaSlope BalaFilter

lemma L_sq_coeff_good (p N : ℕ) :
    coeff N (L p ^ 2) =
    ∑ u ∈ good p N, (((u.a^2*u.b^2 : ℕ) : ℚ) / ((u.x*u.y : ℕ) : ℚ)) := by
  rw [L_sq_coeff]
  have he : (quadSet N).filter (fun u => ¬p ∣ u.x ∧ ¬p ∣ u.y) = good p N := by
    ext; simp only [Finset.mem_filter, mem_good]
  rw [he]
  push_cast
  rfl

lemma square_coefficient_local {p s N : ℕ} [hp : Fact p.Prime] (hN : p^s ∣ N)
    (h : (∑ u ∈ good p N, weight p s u) ≡ 0 [ZMOD (p:ℤ)^s]) :
    coeff N (L p ^ 2) / (p : ℚ)^s ∈ localRing p := by
  let _ : NeZero (p^s) := ⟨pow_ne_zero s hp.out.ne_zero⟩
  rw [L_sq_coeff_good]
  apply local_of_residue_sum_zero (good p N) (fun u => u.a^2*u.b^2) (fun u => u.x*u.y)
      (fun u => (weight p s u : ZMod (p^s)))
  · intro u hu hd
    obtain ⟨_,hx,hy⟩ := mem_good.mp hu
    exact (hp.out.dvd_mul.mp hd).elim hx hy
  · intro u hu
    obtain ⟨hz,hx,hy⟩ := mem_good.mp hu
    have he := (mem_quadSet.mp hz).2.2.2.2
    obtain ⟨h1,h2⟩ := slope_compatible hp.out hN he (Or.inl hy)
    rw [weight_cast]
    push_cast
    calc
      _ = ((slope p s u)*u.y)^2 * ((slope p s u)*u.x)^2 := by ring
      _ = _ := by rw [h1,h2]; ring
  · rw [← Nat.cast_pow, ← ZMod.intCast_eq_intCast_iff] at h
    simpa using h

/-- The Cartier square is p times the Euler derivative of a p-integral series. -/
lemma square_euler_coefficient {p n : ℕ} [hp : Fact p.Prime]
    (h : ∀ s t, (∑ u ∈ good p (p^s*t), weight p s u) ≡ 0 [ZMOD (p:ℤ)^s]) :
    coeff (p*n) (L p ^ 2) / ((p : ℚ)*n) ∈ localRing p := by
  by_cases h0 : n = 0
  · simp [h0]
  obtain ⟨e,m,hu,hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd h0 p hp.out.ne_one
  have hN : p*n = p^(e+1)*m := by rw [hn]; ring
  have hv := square_coefficient_local (N:=p^(e+1)*m) (dvd_mul_right _ _) (h (e+1) m)
  have hd := (localRing p).mul_mem hv (unit_divisor_mem 1 m hu)
  rw [hN, hn]
  convert hd using 1
  push_cast
  simp only [pow_succ, div_eq_mul_inv, mul_inv_rev, one_mul, mul_assoc, mul_left_comm, mul_comm]

theorem cartier_square_primitive {p : ℕ} [hp : Fact p.Prime]
    (h : ∀ s t, (∑ u ∈ good p (p^s*t), weight p s u) ≡ 0 [ZMOD (p:ℤ)^s]) :
    ∃ b : PowerSeries (localRing p),
      cartier p (localL p^2) = C (p : localRing p) * theta b := by
  let b : PowerSeries (localRing p) := mk fun n =>
    ⟨coeff (p*n) (L p ^ 2) / ((p : ℚ)*n), square_euler_coefficient h⟩
  refine ⟨b,?_⟩
  ext n
  rw [coeff_cartier, coeff_C_mul, coeff_theta]
  have hm := congrArg (coeff (p*n)) (congrArg (fun f : PowerSeries ℚ => f^2) (map_localL p))
  rw [← map_pow, coeff_map] at hm
  change ((coeff (p*n) (localL p^2) : localRing p) : ℚ) =
    (p : ℚ) * ((n : ℚ) * ((coeff n b : localRing p) : ℚ))
  rw [show ((coeff (p*n) (localL p^2) : localRing p) : ℚ) = coeff (p*n) (L p^2) from hm]
  simp only [b, coeff_mk]
  by_cases hn : n = 0
  · simp only [hn,mul_zero,Nat.cast_zero,zero_mul,mul_zero]
    rw [coeff_zero_eq_constantCoeff_apply,map_pow,← coeff_zero_eq_constantCoeff_apply,coeff_L]
    simp
  · have hnp : (n : ℚ) ≠ 0 := by exact_mod_cast hn
    have hpp : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    field_simp

end BalaConv

end

/- LambdaEigen -/
section

namespace BalaConv
open PowerSeries BalaFrob

private lemma coeff_L_units (p n : ℕ) : coeff n (L p) =
    ∑ x ∈ n.divisors.filter (fun x => ¬ p ∣ x), ((n/x : ℕ):ℚ)^2/(x:ℚ) := by
  rw [coeff_L, Finset.sum_filter]

private lemma unit_divisors_mul {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (p*n).divisors.filter (fun x => ¬ p ∣ x) =
    n.divisors.filter (fun x => ¬ p ∣ x) := by
  ext x
  simp only [Finset.mem_filter,Nat.mem_divisors,mul_ne_zero_iff]
  constructor
  · rintro ⟨⟨hd,hn⟩,hu⟩
    have hc : x.Coprime p := (hp.coprime_iff_not_dvd.mpr hu).symm
    exact ⟨⟨hc.dvd_of_dvd_mul_left hd, hn.2⟩,hu⟩
  · rintro ⟨⟨hd,hn⟩,hu⟩
    exact ⟨⟨dvd_mul_of_dvd_right hd p, ⟨hp.ne_zero,hn⟩⟩,hu⟩

theorem L_eigen {p : ℕ} (hp : p.Prime) :
    cartier p (L p) = C ((p:ℚ)^2) * L p := by
  ext n
  rw [coeff_cartier,coeff_C_mul,coeff_L_units,coeff_L_units,unit_divisors_mul hp,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have hd : x ∣ n := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hx).1
  rw [Nat.mul_div_assoc _ hd, Nat.cast_mul]
  ring

theorem L_zero (p : ℕ) : constantCoeff (L p) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply,coeff_L]
  simp

end BalaConv

end

/- Eigen -/
section

namespace BalaConv

open PowerSeries BalaFrob

theorem cartier_localL {p : ℕ} [hp : Fact p.Prime] :
    cartier p (localL p) = C ((p : localRing p)^2) * localL p := by
  ext n
  rw [coeff_cartier,coeff_C_mul]
  simp only [localL,coeff_mk,Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast]
  have h := congrArg (coeff n) (L_eigen hp.out)
  simpa only [coeff_cartier, coeff_C_mul] using h

theorem localL_zero (p : ℕ) [Fact p.Prime] : constantCoeff (localL p) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  apply Subtype.ext
  simp only [localL,coeff_mk,Subring.coe_zero]
  rw [coeff_zero_eq_constantCoeff_apply,L_zero]

end BalaConv

end

/- SeriesCubic -/
section

namespace BalaFrob

open PowerSeries

variable {R : Type*} [CommRing R]

lemma coeff_expand_mul_cartier (p : ℕ) (hp : p ≠ 0) (g b : PowerSeries R) (n : ℕ) :
    coeff (p*n) (expand p hp g * b) = coeff n (g * cartier p b) := by
  rw [← cartier_expand_mul p hp, coeff_cartier]

theorem series_cubic (p : ℕ) (hp : p ≠ 0) (g l b : PowerSeries R) (c : R)
    (hL : cartier p l = C ((p : R)^2) * l)
    (hS : cartier p (l^2) = C (p : R) * theta b)
    (hG : ∀ n : ℕ, ∃ t : PowerSeries R, g^(p*n) = expand p hp (g^n) *
      (1 + C ((p*n : ℕ) : R)*l + C (((p*n : ℕ) : R)^2)*C c*l^2 +
        C (((p*n : ℕ) : R)^3)*t))
    (n e : ℕ) : (p : R)^(3*(e+1)) ∣
    coeff (n*p^(e+1)) (g^(n*p^(e+1))) - coeff (n*p^e) (g^(n*p^e)) := by
  let M (n : ℕ) := coeff n (g^n * l)
  let Q (n : ℕ) := coeff n (g^n * cartier p (l^2))
  have hlin (k : ℕ) : coeff (p*k) (expand p hp (g^k) * l) = (p : R)^2 * M k := by
    rw [coeff_expand_mul_cartier, hL, mul_left_comm, coeff_C_mul]
  have hquad (k : ℕ) : coeff (p*k) (expand p hp (g^k) * l^2) = Q k :=
    coeff_expand_mul_cartier p hp _ _ _
  apply cubic_from_moments p (fun k => coeff k (g^k)) M Q
  · intro k
    exact weighted_square g b _ p k hS
  · intro k
    obtain ⟨t,ht⟩ := hG k
    let a : R := ↑(p*k)
    let f := expand p hp (g^k)
    let tail := f * (C c*l^3 + C a*(t*l))
    use coeff (p*k) tail
    have he : g^(p*k) * l = f*l + C a * (f*l^2) + C (a^2)*tail := by
      rw [ht]
      dsimp [tail, f, a]
      simp only [map_pow]
      ring
    dsimp only [M] at ⊢
    rw [he, map_add, map_add, coeff_C_mul, coeff_C_mul, hlin, hquad]
  · intro k
    obtain ⟨t,ht⟩ := hG k
    let a : R := ↑(p*k)
    let f := expand p hp (g^k)
    use c, coeff (p*k) (f*t)
    have he : g^(p*k) = f + C a*(f*l) + C (a^2*c)*(f*l^2) + C (a^3)*(f*t) := by
      rw [ht]
      dsimp [f, a]
      simp only [map_mul, map_pow]
      ring
    rw [he, map_add, map_add, map_add, coeff_C_mul, coeff_C_mul, coeff_C_mul,
      hlin, hquad, show coeff (p*k) f = coeff k (g^k) from coeff_expand_mul _ _ _ _]
    dsimp [a]
    push_cast
    ring

end BalaFrob

end

/- Taylor -/
section

namespace BalaFrob

open PowerSeries

variable {p : ℕ} [Fact p.Prime]

lemma divided_exp_scalar_mem (hp7 : 7 ≤ p) (n k j : ℕ) (hj : j ≤ 3) (hjk : j ≤ k) :
    ((p*n : ℕ) : ℚ)^(k-j) / (k.factorial : ℚ) ∈ localRing p := by
  have h1 := divided_exp_tail_mem hp7 hj hjk
  have h2 : (n : ℚ)^(k-j) ∈ localRing p := (localRing p).pow_mem (natCast_mem (localRing p) n) _
  convert (localRing p).mul_mem h1 h2 using 1
  push_cast
  rw [mul_pow]
  ring

noncomputable def expScaled (hp7 : 7 ≤ p) (n : ℕ) : PowerSeries (localRing p) :=
  mk fun k => ⟨((p*n : ℕ) : ℚ)^k / (k.factorial : ℚ),
    by simpa using divided_exp_scalar_mem hp7 n k 0 (by omega) (by omega)⟩

noncomputable def expTail (hp7 : 7 ≤ p) (n : ℕ) : PowerSeries (localRing p) :=
  mk fun k => if hk : 3 ≤ k then ⟨_, divided_exp_scalar_mem hp7 n k 3 (le_refl 3) hk⟩ else 0

noncomputable def halfLocal (hp7 : 7 ≤ p) : localRing p :=
  ⟨1/2, by
    have hb : ¬p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
    simpa using unit_divisor_mem (p := p) 1 2 hb⟩

lemma expScaled_taylor (hp7 : 7 ≤ p) (n : ℕ) :
    let a : localRing p := ↑(p*n)
    expScaled hp7 n = 1 + C a*X + C (a^2 * halfLocal hp7)*X^2 + C (a^3)*expTail hp7 n := by
  dsimp only
  ext k
  simp only [expScaled, expTail, coeff_mk, map_add, coeff_C_mul, coeff_X, coeff_X_pow,
    coeff_one]
  rcases k with _ | _ | _ | k
  · norm_num
  · norm_num
  · norm_num [halfLocal]
    ring
  · simp
    rw [show k+1+1+1 = k+3 by omega, pow_add]
    ring

lemma expScaled_map (hp7 : 7 ≤ p) (n : ℕ) :
    map (localRing p).subtype (expScaled hp7 n) = rescale ((p*n : ℕ) : ℚ) (exp ℚ) := by
  ext k
  simp [coeff_map, coeff_rescale, expScaled, div_eq_mul_inv, mul_comm]

lemma expScaled_subst_taylor (hp7 : 7 ≤ p) (n : ℕ) (l : PowerSeries (localRing p))
    (hl : HasSubst l) :
    let a : localRing p := ↑(p*n)
    (expScaled hp7 n).subst l =
    1 + C a*l + C (a^2)*C (halfLocal hp7)*l^2 + C (a^3)*(expTail hp7 n).subst l := by
  dsimp only
  rw [expScaled_taylor hp7 n]
  simp only [subst_add hl, subst_mul hl, subst_pow hl, subst_X hl, subst_C, map_mul]
  rw [← coe_substAlgHom hl, map_one]
  rfl

end BalaFrob

end

/- ProductTaylor -/
section

namespace BalaFrob

open PowerSeries BalaProduct

lemma product_taylor {p : ℕ} [hp : Fact p.Prime] (hp7 : 7 ≤ p)
    (l : PowerSeries (localRing p)) (hzero : constantCoeff l = 0)
    (hmap : map (localRing p).subtype l = delta p hp.out.ne_zero)
    (n : ℕ) :
    ∃ t : PowerSeries (localRing p),
      G (localRing p) ^ (p*n) = expand p hp.out.ne_zero (G (localRing p)^n) *
      (1 + C ((p*n : ℕ) : localRing p)*l +
       C (((p*n : ℕ) : localRing p)^2)*C (halfLocal hp7)*l^2 +
       C (((p*n : ℕ) : localRing p)^3)*t) := by
  have hl := HasSubst.of_constantCoeff_zero hzero
  refine ⟨(expTail hp7 n).subst l, ?_⟩
  rw [← expScaled_subst_taylor hp7 n l hl]
  apply map_injective (localRing p).subtype Subtype.val_injective
  have hm : map (localRing p).subtype ((expScaled hp7 n).subst l) =
      (map (localRing p).subtype (expScaled hp7 n)).subst (map (localRing p).subtype l) :=
    map_subst (h := (localRing p).subtype) hl _
  simp only [map_pow, map_G, map_mul, map_expand, hm, expScaled_map, hmap]
  rw [frob_exp hp.out.ne_zero n, rescale_subst_E _ _ (delta_const hp.out.ne_zero)] <;>
    congr 2 <;> simp [nsmul_eq_mul, smul_eq_C_mul]

end BalaFrob

end

/- Main -/
section

namespace BalaMain
open BalaProduct BalaFrob PowerSeries

/-- The integral and local sequences are the same coefficient after base change. -/
noncomputable def seq (R : Type*) [CommRing R] (m : ℕ) : R :=
  coeff m (G R ^ m)

theorem seq_cast (R : Type*) [CommRing R] (m : ℕ) :
    (seq ℤ m : R) = seq R m := by
  change (Int.castRingHom R) (coeff m (G ℤ ^ m)) = coeff m (G R ^ m)
  rw [← coeff_map, map_pow, map_G]

theorem target_from_local {p n r : ℕ} (hr : 0 < r)
    [Fact p.Prime]
    (h : ∀ e : ℕ, (p : localRing p)^(3*(e+1)) ∣
      seq (localRing p) (n*p^(e+1)) - seq (localRing p) (n*p^e)) :
    ∃ m : ℤ, OMA.S_oeis_a023871.u (n*p^r) - OMA.S_oeis_a023871.u (n*p^(r-1)) =
      (p : ℚ)^(3*r) * m := by
  obtain ⟨e,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  simp only [Nat.succ_sub_one]
  have hz : (p : localRing p)^(3*(e+1)) ∣
      ((seq ℤ (n*p^(e+1)) - seq ℤ (n*p^e) : ℤ) : localRing p) := by
    simpa only [Int.cast_sub,seq_cast] using h e
  obtain ⟨m,hm⟩ := integral_of_local_divisibility _ _ hz
  refine ⟨m,?_⟩
  rw [u_eq_G,u_eq_G]
  change (seq ℤ (n*p^(e+1)) : ℚ) - (seq ℤ (n*p^e) : ℚ) = _
  exact_mod_cast hm

/-- The entire local congruence, assembled from the Cartier and Taylor estimates. -/
theorem local_cubic {p : ℕ} [hp : Fact p.Prime] (h7 : 7 ≤ p) (n e : ℕ) :
    (p : localRing p)^(3*(e+1)) ∣
    seq (localRing p) (n*p^(e+1)) - seq (localRing p) (n*p^e) := by
  have hmap : PowerSeries.map (localRing p).subtype (BalaConv.localL p) =
      delta p hp.out.ne_zero := by
    rw [BalaConv.map_localL]
    ext j
    rw [BalaConv.coeff_L, coeff_delta]
  obtain ⟨b,hb⟩ := BalaConv.cartier_square_primitive (p := p)
    (fun s t => BalaEstimate.good_sum hp.out h7 (dvd_mul_right (p^s) t))
  exact series_cubic p hp.out.ne_zero (G (localRing p)) (BalaConv.localL p) b
    (halfLocal h7) BalaConv.cartier_localL hb
    (product_taylor h7 _ (BalaConv.localL_zero p) hmap) n e

end BalaMain

theorem OMA.solution : type_of% @OMA.S_oeis_a023871.main := by
  intro p n r hp h7 _ hr
  letI : Fact p.Prime := ⟨hp⟩
  apply BalaMain.target_from_local hr
  exact fun e => BalaMain.local_cubic h7 n e

end

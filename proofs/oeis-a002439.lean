import OMAStatements.S_oeis_a002439

/- The arithmetic period lemmas were developed by a collaborating Codex agent. -/

namespace GlaisherArithmetic

/-- Once m reaches q, a multiple of φ(q) is a period for powers of any base modulo q. -/
theorem nat_pow_period (q : ℕ) (hq : 0 < q) (b m t : ℕ) (hm : q ≤ m)
    (ht : q.totient ∣ t) : b^(m+t) ≡ b^m [MOD q] := by
  induction q using Nat.recOnPrimeCoprime generalizing m t with
  | zero => omega
  | prime_pow p e hp =>
    by_cases he : e = 0
    · simp [he, Nat.ModEq, Nat.mod_one]
    by_cases hpb : p ∣ b
    · have hem : e ≤ m := by
        have hpow : e ≤ p^e := Nat.le_of_lt (Nat.lt_pow_self hp.one_lt)
        exact hpow.trans hm
      have hdvd (j : ℕ) (hj : e ≤ j) : p^e ∣ b^j :=
        (pow_dvd_pow _ hj).trans (pow_dvd_pow_of_dvd hpb _)
      exact (Nat.modEq_zero_iff_dvd.mpr (hdvd (m+t) (by omega))).trans
        (Nat.modEq_zero_iff_dvd.mpr (hdvd m hem)).symm
    · have hcop : b.Coprime (p^e) :=
        ((hp.coprime_iff_not_dvd.mpr hpb).pow_left e).symm
      obtain ⟨j, rfl⟩ := ht
      rw [pow_add, pow_mul]
      simpa using ((Nat.ModEq.pow_totient hcop).pow j).mul_left (b^m)
  | coprime u v hu hv huv ihu ihv =>
    rw [Nat.totient_mul huv] at ht
    have hub : u ≤ u*v := by
      simpa using Nat.mul_le_mul_left u (show 1 ≤ v by omega)
    have hvb : v ≤ u*v := by
      simpa using Nat.mul_le_mul_right v (show 1 ≤ u by omega)
    apply (Nat.modEq_and_modEq_iff_modEq_mul huv).mp
    exact ⟨ihu (by omega) m t (hub.trans hm) ((dvd_mul_right _ _).trans ht),
      ihv (by omega) m t (hvb.trans hm) ((dvd_mul_left _ _).trans ht)⟩

/-- The eventual period is valid for every residue, with no unit assumption. -/
theorem int_pow_period {q : ℕ} (hq : 0 < q) (b : ℤ) {m t : ℕ} (hm : q ≤ m)
    (ht : q.totient ∣ t) : b^(m+t) ≡ b^m [ZMOD q] := by
  let : NeZero q := ⟨hq.ne'⟩
  apply (ZMod.intCast_eq_intCast_iff _ _ q).mp
  have h := (ZMod.natCast_eq_natCast_iff _ _ q).mpr
    (nat_pow_period q hq (b : ZMod q).val m t hm ht)
  simpa only [Nat.cast_pow, ZMod.natCast_zmod_val, Int.cast_pow] using h

theorem totient_two_mul_dvd (k : ℕ) : (2*k).totient ∣ 2*k.totient := by
  rcases Nat.even_or_odd k with h | h
  · simp [Nat.totient_two_mul_of_even h]
  · simpa only [Nat.totient_two_mul_of_odd h] using dvd_mul_left k.totient 2

/-- The doubled modulus absorbs the single factor of two in Glaisher's generating function. -/
theorem int_pow_period_doubled {k : ℕ} (hk : 0 < k) (b : ℤ) {m : ℕ} (hm : 2*k ≤ m) :
    b^(m+2*k.totient) ≡ b^m [ZMOD (2*k)] :=
  int_pow_period (q := 2*k) (by positivity) b hm (totient_two_mul_dvd k)

/-- The sign converting hyperbolic coefficients to trigonometric ones preserves the period. -/
theorem signed_period {k n : ℕ} (hk : 0 < k) {u v : ℤ} (h : u ≡ v [ZMOD k]) :
    (-1 : ℤ)^(n+k.totient)*u ≡ (-1 : ℤ)^n*v [ZMOD k] := by
  have hpow : (-1 : ℤ)^k.totient ≡ 1 [ZMOD k] := by
    by_cases hbig : 2 < k
    · rw [(Nat.totient_even hbig).neg_one_pow]
    · rcases (show k = 1 ∨ k = 2 by omega) with rfl | rfl <;> decide
  simpa [pow_add, mul_assoc] using (hpow.mul h).mul_left ((-1 : ℤ)^n)

end GlaisherArithmetic

namespace A002439

open PowerSeries Finset
open scoped BigOperators

private abbrev PS := PowerSeries ℚ

private noncomputable def mom (f : PS) (n : ℕ) : ℚ := (n.factorial : ℚ) * coeff n f

private noncomputable def E (b : ℤ) : PS := rescale (b : ℚ) (exp ℚ)

private theorem mom_E (b : ℤ) (n : ℕ) : mom (E b) n = (b : ℚ) ^ n := by
  simp [mom, E, coeff_rescale, coeff_exp]
  have h : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

private theorem E_add (a b : ℤ) : E a * E b = E (a + b) := by
  simpa [E] using exp_mul_exp_eq_exp_add (a : ℚ) (b : ℚ)

private theorem constant_E (b : ℤ) : constantCoeff (E b) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, E, coeff_rescale]
  simp

private theorem E_zero : E 0 = 1 := by simp [E]

private theorem E_pow (b : ℤ) (j : ℕ) : E b ^ j = E (b * j) := by
  induction j with
  | zero => simp [E_zero]
  | succ j ih => rw [pow_succ, ih, E_add]; congr 1; push_cast; ring

private theorem mom_add (f g : PS) (n : ℕ) :
    mom (f + g) n = mom f n + mom g n := by simp [mom, mul_add]

private theorem mom_sub (f g : PS) (n : ℕ) :
    mom (f - g) n = mom f n - mom g n := by simp [mom, mul_sub]

private theorem mom_C (q : ℚ) (f : PS) (n : ℕ) :
    mom (C q * f) n = q * mom f n := by simp [mom, coeff_C_mul]; ring

private theorem mom_mul (f g : PS) (n : ℕ) :
    mom (f * g) n = ∑ i ∈ range (n + 1),
      (n.choose i : ℚ) * mom f i * mom g (n - i) := by
  rw [mom, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_sum]
  apply sum_congr rfl
  intro i hi
  have h : i ≤ n := by simpa using (mem_range.mp hi)
  have hcast : (n.choose i : ℚ) * (i.factorial : ℚ) * ((n - i).factorial : ℚ) =
      (n.factorial : ℚ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial h
  rw [← hcast]
  unfold mom
  push_cast
  ring

private def IntMom (f : PS) : Prop := ∀ n, ∃ z : ℤ, mom f n = z

private theorem intMom_E (b : ℤ) : IntMom (E b) := by
  intro n
  exact ⟨b ^ n, by simp [mom_E]⟩

private theorem intMom_sub {f g : PS} (hf : IntMom f) (hg : IntMom g) : IntMom (f - g) := by
  intro n
  obtain ⟨x, hx⟩ := hf n
  obtain ⟨y, hy⟩ := hg n
  exact ⟨x-y, by simp [mom_sub, hx, hy]⟩

private theorem intMom_add {f g : PS} (hf : IntMom f) (hg : IntMom g) : IntMom (f + g) := by
  intro n
  obtain ⟨x, hx⟩ := hf n
  obtain ⟨y, hy⟩ := hg n
  exact ⟨x+y, by simp [mom_add, hx, hy]⟩

private theorem intMom_mul {f g : PS} (hf : IntMom f) (hg : IntMom g) : IntMom (f * g) := by
  intro n
  choose x hx using hf
  choose y hy using hg
  refine ⟨∑ i ∈ range (n+1), (n.choose i : ℤ) * x i * y (n-i), ?_⟩
  simp [mom_mul, hx, hy]

private theorem intMom_one : IntMom 1 := E_zero ▸ intMom_E 0

private theorem intMom_of_product {D f : PS}
    (hD : IntMom D) (h0 : constantCoeff D = 1) (hf : IntMom (f * D)) : IntMom f := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    choose x hx using hD
    choose y hy using fun i : Fin n => ih i i.isLt
    obtain ⟨z, hz⟩ := hf n
    refine ⟨z - ∑ i : Fin n, (n.choose i : ℤ) * y i * x (n-i), ?_⟩
    rw [mom_mul, sum_range_succ] at hz
    have hterm : (n.choose n : ℚ) * mom f n * mom D (n - n) = mom f n := by
      simp [mom, coeff_zero_eq_constantCoeff_apply, h0]
    rw [hterm, ← Fin.sum_univ_eq_sum_range] at hz
    simp_rw [hy, hx] at hz
    push_cast
    linarith

private noncomputable def U : PS := E 2 - 1
private noncomputable def D : PS := 1 + U + U ^ 2

private noncomputable def halfU : PS := C (1/2 : ℚ) * U

private theorem halfU_eq : C (2 : ℚ) * halfU = U := by
  rw [halfU, ← mul_assoc, ← map_mul]
  norm_num

private theorem intMom_halfU : IntMom halfU := by
  rw [halfU]
  intro n
  cases n with
  | zero =>
    exact ⟨0, by rw [mom_C, U, mom_sub, mom_E]; simp [mom]⟩
  | succ n =>
    refine ⟨(2 : ℤ) ^ n, ?_⟩
    rw [mom_C, U, mom_sub, mom_E]
    simp [mom, coeff_one, pow_succ]
    ring

private noncomputable def twist (f : PS) : PS :=
  PowerSeries.mk fun n => (-1 : ℚ) ^ (n / 2) * coeff n f

private theorem coeff_twist (f : PS) (n : ℕ) :
    coeff n (twist f) = (-1 : ℚ) ^ (n / 2) * coeff n f := by simp [twist]

private theorem twist_mul_even (f g : PS) (h : ∀ j, ¬ Even j → coeff j g = 0) :
    twist (f * g) = twist f * twist g := by
  ext n
  rw [coeff_twist, coeff_mul, coeff_mul, mul_sum]
  apply sum_congr rfl
  rintro ⟨i,j⟩ hij
  have hij' : i + j = n := HasAntidiagonal.mem_antidiagonal.mp hij
  simp only [coeff_twist]
  by_cases hpar : Even j
  · obtain ⟨b, rfl⟩ := hpar
    have hsplit : n / 2 = i / 2 + (b+b)/2 := by omega
    rw [hsplit, pow_add]
    ring
  · simp [h j hpar]

private theorem negOneSquare (n : ℕ) : (-1 : ℚ)^n * (-1 : ℚ)^n = 1 := by
  rw [← mul_pow]
  norm_num

private theorem twist_sin :
    twist (rescale (2 : ℚ) (sin ℚ)) = C (1/2 : ℚ) * (E 2 - E (-2)) := by
  ext n
  simp only [coeff_twist, coeff_rescale, sin, coeff_mk, E, coeff_C_mul, map_sub, coeff_exp,
    Algebra.algebraMap_self, RingHom.id_apply, Int.cast_ofNat, Int.cast_neg]
  by_cases h : Even n
  · simp [h, h.neg_pow]
  · rw [if_neg h, (Nat.not_even_iff_odd.mp h).neg_pow]
    linear_combination ((2 : ℚ)^n / n.factorial) * negOneSquare (n/2)

private theorem twist_cos :
    twist (C (2 : ℚ) * rescale (3 : ℚ) (cos ℚ)) = E 3 + E (-3) := by
  ext n
  simp only [coeff_twist, coeff_rescale, cos, coeff_mk, E, coeff_C_mul, map_add, coeff_exp,
    Algebra.algebraMap_self, RingHom.id_apply, Int.cast_ofNat, Int.cast_neg]
  by_cases h : Even n
  · rw [if_pos h, h.neg_pow]
    linear_combination (2 * (3 : ℚ)^n / n.factorial) * negOneSquare (n/2)
  · simp [h, (Nat.not_even_iff_odd.mp h).neg_pow]

private noncomputable def F : PS := twist OMA.S_oeis_a002439.egf

private theorem D_factor : D * (E 2 + 1) = E 6 + 1 := by
  have he : E 2 ^ 3 = E 6 := by rw [E_pow]; norm_num
  rw [← he, D, U]
  ring

private theorem F_eq : F * D = E 1 * halfU := by
  let g : PS := C (2 : ℚ) * rescale (3 : ℚ) (cos ℚ)
  have h0 : constantCoeff g ≠ 0 := by
    simp [g, ← coeff_zero_eq_constantCoeff_apply, coeff_rescale, cos]
  have hmul : OMA.S_oeis_a002439.egf * g = rescale (2 : ℚ) (sin ℚ) := by
    rw [OMA.S_oeis_a002439.egf]
    change _ * g⁻¹ * g = _
    rw [mul_assoc, PowerSeries.inv_mul_cancel _ h0, mul_one]
  have heven : ∀ j, ¬ Even j → coeff j g = 0 := by
    intro j hj
    simp [g, coeff_C_mul, coeff_rescale, cos, hj]
  have htw : F * (E 3 + E (-3)) = C (1/2 : ℚ) * (E 2 - E (-2)) := by
    rw [← twist_cos]
    change twist (OMA.S_oeis_a002439.egf) * twist g = _
    rw [← twist_mul_even _ _ heven, hmul, twist_sin]
  have ht := congrArg (fun p : PS => p * E 3) htw
  rw [mul_assoc, add_mul, mul_assoc, sub_mul, E_add, E_add, E_add, E_add] at ht
  norm_num at ht
  have hfac2 : E 5 - E 1 = E 1 * U * (E 2 + 1) := by
    have he : E 1 * E 2 ^ 2 = E 5 := by rw [E_pow, E_add]; norm_num
    rw [← he, U]
    ring
  rw [E_zero, ← D_factor, hfac2] at ht
  have hne : E 2 + 1 ≠ 0 := by
    intro h
    have := congrArg constantCoeff h
    simp [constant_E] at this
  apply mul_right_cancel₀ hne
  rw [halfU]
  linear_combination ht

private theorem intMom_F : IntMom F := by
  apply intMom_of_product (D := D)
  · have hU := intMom_sub (intMom_E 2) intMom_one
    exact intMom_add (intMom_add intMom_one hU) (by rw [pow_two]; exact intMom_mul hU hU)
  · simp [D, U, constant_E]
  · rw [F_eq]
    exact intMom_mul (intMom_E 1) intMom_halfU

private theorem a_sign (n : ℕ) :
    OMA.S_oeis_a002439.a n = (-1 : ℚ)^n * mom F (2*n+1) := by
  have he : (2*n+1)/2 = n := by omega
  simp only [OMA.S_oeis_a002439.a, mom, F, coeff_twist, he]
  linear_combination -((2*n+1).factorial : ℚ) *
    coeff (2*n+1) OMA.S_oeis_a002439.egf * negOneSquare n


private def multiple (q : ℕ) (f : PS) : Prop :=
  ∃ g : PS, IntMom g ∧ f = C (q : ℚ) * g

private theorem multiple_of_mom (q : ℕ) (f : PS)
    (h : ∀ n, ∃ z : ℤ, mom f n = (q : ℚ) * z) : multiple q f := by
  choose z hz using h
  let g : PS := PowerSeries.mk fun n => (z n : ℚ) / n.factorial
  have hg (n : ℕ) : mom g n = z n := by
    simp only [mom, g, coeff_mk]
    have hf : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    field_simp
  refine ⟨g, fun n => ⟨z n, hg n⟩, ?_⟩
  ext n
  apply mul_left_cancel₀ (by positivity : (n.factorial : ℚ) ≠ 0)
  change mom f n = mom (C (q : ℚ) * g) n
  rw [mom_C, hg, hz]

private theorem multiple_mul {q r : ℕ} {f g : PS}
    (hf : multiple q f) (hg : multiple r g) : multiple (q*r) (f*g) := by
  obtain ⟨f', hf', rfl⟩ := hf
  obtain ⟨g', hg', rfl⟩ := hg
  refine ⟨f' * g', intMom_mul hf' hg', ?_⟩
  push_cast
  rw [map_mul]
  ring

private theorem multiple_mul_int {q : ℕ} {f g : PS}
    (hf : multiple q f) (hg : IntMom g) : multiple q (f*g) := by
  obtain ⟨f', hf', rfl⟩ := hf
  exact ⟨f' * g, intMom_mul hf' hg, by ring⟩

private theorem multiple_neg {q : ℕ} {f : PS} (hf : multiple q f) : multiple q (-f) := by
  obtain ⟨f', hf', rfl⟩ := hf
  refine ⟨-f', ?_, by ring⟩
  simpa using intMom_sub (f := 0) (by intro n; exact ⟨0, by simp [mom]⟩) hf'

private theorem multiple_exponential (q : ℕ) (b : ℤ) :
    multiple q (E ((q : ℤ)*b) - 1) := by
  apply multiple_of_mom
  intro n
  cases n with
  | zero => exact ⟨0, by rw [mom_sub, mom_E]; simp [mom]⟩
  | succ n =>
    refine ⟨b * ((q : ℤ) * b)^n, ?_⟩
    rw [mom_sub, mom_E]
    simp [mom, coeff_one, pow_succ]
    ring

private theorem multiple_D_two : multiple 2 (D - 1) := by
  have hU : IntMom U := intMom_sub (intMom_E 2) intMom_one
  refine ⟨halfU * (1+U), intMom_mul intMom_halfU (intMom_add intMom_one hU), ?_⟩
  change D - 1 = C (2 : ℚ) * (halfU * (1+U))
  rw [← mul_assoc, halfU_eq, D]
  ring

private noncomputable def expMonoid : Submonoid PS where
  carrier := Set.range E
  one_mem' := ⟨0, E_zero⟩
  mul_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a+b, (E_add a b).symm⟩

private noncomputable def expPoly : Subalgebra ℤ PS := Algebra.adjoin ℤ (expMonoid : Set PS)

private theorem expPoly_E (b : ℤ) : E b ∈ expPoly := Algebra.subset_adjoin ⟨b, rfl⟩

private theorem expPoly_U : U ∈ expPoly := sub_mem (expPoly_E 2) (one_mem _)

private theorem expPoly_D : D ∈ expPoly :=
  add_mem (add_mem (one_mem _) expPoly_U) (pow_mem expPoly_U _)

private theorem expPoly_C (z : ℤ) : C (z : ℚ) ∈ expPoly := by
  rw [map_intCast]
  exact expPoly.intCast_mem z

private theorem inverse_approx_odd {q : ℕ} (hq : Odd q) :
    ∃ P ∈ expPoly, multiple q (D*P-1) := by
  let S : PS := ∑ j ∈ range q, (-E 6)^j
  have hS : S ∈ expPoly := sum_mem fun j _ => pow_mem (neg_mem (expPoly_E 6)) _
  let t : ℤ := ((q+1)/2 : ℕ)
  have ht : 2*t = (q : ℤ)+1 := by obtain ⟨s, hs⟩ := hq; dsimp [t]; omega
  let P : PS := C (t : ℚ) * (E 2 + 1) * S
  have hP : P ∈ expPoly :=
    mul_mem (mul_mem (expPoly_C t) (add_mem (expPoly_E 2) (one_mem _))) hS
  refine ⟨P, hP, ?_⟩
  have hgeom : (E 6 + 1)*S = E (6*q) + 1 := by
    dsimp [S]
    have hg := geom_sum_mul_neg (-E 6) q
    rw [hq.neg_pow, E_pow] at hg
    linear_combination hg
  obtain ⟨G, hG, hG_eq⟩ := multiple_exponential q 6
  rw [mul_comm (q : ℤ) 6] at hG_eq
  have htex : C (t : ℚ) * C (2 : ℚ) = C (q : ℚ) + 1 := by
    rw [← map_mul, ← map_one C, ← map_add]
    congr 1
    exact_mod_cast (mul_comm t 2 ▸ ht)
  have hC : IntMom (C (t : ℚ)) := by
    intro n
    by_cases hn : n = 0
    · subst n; exact ⟨t, by simp [mom]⟩
    · exact ⟨0, by unfold mom; rw [coeff_C_of_ne_zero hn]; simp⟩
  refine ⟨C (t : ℚ)*G + 1, intMom_add (intMom_mul hC hG) intMom_one, ?_⟩
  calc
    D*P - 1 = C (t : ℚ) * ((D * (E 2 + 1))*S) - 1 := by dsimp [P]; ring
    _ = C (t : ℚ) * (E (6*q)+1) - 1 := by rw [D_factor, hgeom]
    _ = C (t : ℚ)*(E (6*q)-1) + C (t : ℚ)*C (2 : ℚ) - 1 := by
      rw [map_ofNat C 2]
      ring
    _ = C (q : ℚ) * (C (t : ℚ)*G + 1) := by rw [htex, hG_eq]; ring

private theorem inverse_approx (q : ℕ) (hq : 0 < q) :
    ∃ P ∈ expPoly, multiple q (D*P-1) := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    by_cases h : Odd q
    · exact inverse_approx_odd h
    · have he : Even q := Nat.not_odd_iff_even.mp h
      have hq' : q = (q/2) * 2 := by obtain ⟨t, ht⟩ := he; omega
      obtain ⟨P, hP, hmod⟩ := ih (q/2) (by omega) (by omega)
      refine ⟨P + 1 - D*P, sub_mem (add_mem hP (one_mem _)) (mul_mem expPoly_D hP), ?_⟩
      have hp := multiple_neg (multiple_mul hmod multiple_D_two)
      rw [← hq'] at hp
      convert hp using 2
      ring

private theorem twice_F_eq : (C (2 : ℚ) * F)*D = E 1*U := by
  rw [mul_assoc, F_eq, ← mul_left_comm, halfU_eq]

private theorem approximate (q : ℕ) (hq : 0 < q) :
    ∃ P ∈ expPoly, multiple q (C (2 : ℚ)*F - P) := by
  obtain ⟨A, hA, hAp⟩ := inverse_approx q hq
  refine ⟨(E 1 * U)*A, mul_mem (mul_mem (expPoly_E 1) expPoly_U) hA, ?_⟩
  have hi : IntMom (C (2 : ℚ)*F) := by
    intro n
    obtain ⟨z, hz⟩ := intMom_F n
    exact ⟨2*z, by simp [mom_C, hz]⟩
  have he := multiple_neg (multiple_mul_int hAp hi)
  rwa [show -((D*A-1)*(C (2 : ℚ)*F)) =
      C (2 : ℚ)*F - ((C (2 : ℚ)*F)*D)*A by ring, twice_F_eq] at he

private def Period (k : ℕ) (f : PS) : Prop :=
  ∀ n : ℕ, 2*k ≤ n → ∃ z : ℤ,
    mom f (n + 2*k.totient) - mom f n = ((2*k : ℕ) : ℚ) * z

private theorem expPoly_period (k : ℕ) (hk : 0 < k) {P : PS} (hP : P ∈ expPoly) : Period k P := by
  have hs : P ∈ Submodule.span ℤ (expMonoid : Set PS) := by
    change P ∈ expPoly.toSubmodule at hP
    rwa [expPoly, Algebra.adjoin_eq_span, Submonoid.closure_eq] at hP
  clear hP
  induction hs using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨b, rfl⟩ := hf
    intro n hn
    have he := GlaisherArithmetic.int_pow_period_doubled hk b hn
    obtain ⟨z, hz⟩ := Int.modEq_iff_dvd.mp he.symm
    refine ⟨z, ?_⟩
    rw [mom_E, mom_E]
    exact_mod_cast hz
  | zero => intro n hn; exact ⟨0, by simp [mom]⟩
  | add f g hf hg hf' hg' =>
    intro n hn
    obtain ⟨u, hu⟩ := hf' n hn
    obtain ⟨v, hv⟩ := hg' n hn
    refine ⟨u+v, ?_⟩
    rw [mom_add, mom_add, Int.cast_add]
    linear_combination hu + hv
  | smul c f hf hper =>
    intro n hn
    obtain ⟨u, hu⟩ := hper n hn
    have hc : c • f = C (c : ℚ) * f := by
      rw [zsmul_eq_mul, map_intCast]
    refine ⟨c*u, ?_⟩
    rw [hc, mom_C, mom_C, Int.cast_mul]
    linear_combination (c : ℚ) * hu

private theorem F_period (k : ℕ) (hk : 0 < k) (m : ℕ) (hm : 2*k ≤ m) :
    ∃ z : ℤ, mom F (m + 2*k.totient) - mom F m = (k : ℚ) * z := by
  obtain ⟨P, hP, hmod⟩ := approximate (2*k) (by positivity)
  obtain ⟨R, hR, hEq⟩ := hmod
  obtain ⟨z, hz⟩ := expPoly_period k hk hP m hm
  obtain ⟨u, hu⟩ := hR (m + 2*k.totient)
  obtain ⟨v, hv⟩ := hR m
  have get_eq (j : ℕ) :
      2 * mom F j - mom P j = ((2*k : ℕ) : ℚ) * mom R j := by
    have h := congrArg (fun f => mom f j) hEq
    simpa only [mom_sub, mom_C] using h
  refine ⟨z+u-v, ?_⟩
  have h₁ := get_eq (m + 2*k.totient)
  have h₂ := get_eq m
  rw [hu] at h₁
  rw [hv] at h₂
  push_cast at h₁ h₂ hz ⊢
  linear_combination (h₁ - h₂ + hz)/2

theorem main :
    ∀ k : ℕ, 0 < k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ z : ℤ, OMA.S_oeis_a002439.a (n + Nat.totient k) - OMA.S_oeis_a002439.a n =
        (k : ℚ) * z := by
  intro k hk
  refine ⟨k, fun n hn => ?_⟩
  have hidx : 2*(n+k.totient)+1 = (2*n+1)+2*k.totient := by omega
  obtain ⟨z,hz⟩ := F_period k hk (2*n+1) (by omega)
  obtain ⟨u,hu⟩ := intMom_F (2*(n+k.totient)+1)
  obtain ⟨v,hv⟩ := intMom_F (2*n+1)
  rw [← hidx, hu, hv] at hz
  have hp : u ≡ v [ZMOD k] := by
    apply Int.ModEq.symm
    exact Int.modEq_iff_dvd.mpr ⟨z, by exact_mod_cast hz⟩
  have hsign := GlaisherArithmetic.signed_period (n := n) hk hp
  obtain ⟨t,ht⟩ := Int.modEq_iff_dvd.mp hsign.symm
  refine ⟨t, ?_⟩
  rw [a_sign, a_sign, hu, hv]
  exact_mod_cast ht

end A002439

theorem OMA.solution : type_of% @OMA.S_oeis_a002439.main := A002439.main

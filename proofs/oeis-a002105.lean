import OMAStatements.S_oeis_a002105

/-!
Divisibility by powers of two follows from von Staudt–Clausen.
For odd moduli, a finite exponential sum reproduces the factorial-weighted
coefficients of `(exp (2X) - 1) / (exp (2X) + 1)` modulo the modulus.
The moment operations and exponential approximation adapt the proof of A002439.
-/
namespace ReducedTangentArithmetic

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

end ReducedTangentArithmetic

namespace ReducedTangent

open PowerSeries Finset
open scoped BigOperators
open OMA.S_oeis_a002105
private abbrev PS := PowerSeries ℚ

private noncomputable def mom (f : PS) (n : ℕ) : ℚ := (n.factorial : ℚ) * coeff n f

private noncomputable def E (b : ℤ) : PS := rescale (b : ℚ) (exp ℚ)

private theorem mom_E (b : ℤ) (n : ℕ) : mom (E b) n = (b : ℚ) ^ n := by
  simp [mom, E, coeff_rescale, coeff_exp]
  have h : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

private theorem E_add (a b : ℤ) : E a * E b = E (a + b) := by
  simpa [E] using exp_mul_exp_eq_exp_add (a : ℚ) (b : ℚ)

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

private noncomputable def B (b : ℤ) : PS := rescale (b : ℚ) (bernoulliPowerSeries ℚ)

private noncomputable def F : PS :=
  1 + PowerSeries.mk (fun i => coeff (i + 1) (B 4 - B 2))

private theorem B_mul (b : ℤ) : B b * (E b - 1) = C (b : ℚ) * X := by
  have h := congrArg (rescale (b : ℚ)) (bernoulliPowerSeries_mul_exp_sub_one ℚ)
  simpa only [map_mul, map_sub, map_one, rescale_X, B, E] using h

private theorem X_F_sub : X * (F - 1) = B 4 - B 2 := by
  rw [F, add_sub_cancel_left]
  ext n
  cases n with
  | zero =>
    rw [coeff_zero_X_mul, map_sub]
    simp [B, bernoulliPowerSeries, coeff_rescale]
  | succ n => rw [coeff_succ_X_mul, coeff_mk]

private theorem F_mul : F * (E 2 + 1) = E 2 - 1 := by
  have h4 : E 2 * E 2 = E 4 := E_add 2 2
  have hprod : (E 2 + 1) * (E 2 - 1) = E 4 - 1 := by
    rw [← h4]
    ring
  have hEnz : E 2 - 1 ≠ 0 := by
    intro h
    have he := congrArg (fun P : PS => mom P 1) h
    rw [mom_sub, mom_E] at he
    norm_num [mom, coeff_one] at he
  have hB4 := B_mul 4
  have hB2 := B_mul 2
  rw [← hprod] at hB4
  simp only [Int.cast_ofNat, map_ofNat] at hB2 hB4
  have h : X * ((F - 1) * (E 2 + 1)) * (E 2 - 1) =
      X * (-(2 : PS)) * (E 2 - 1) := by
    linear_combination (E 2 + 1) * (E 2 - 1) * X_F_sub + hB4 - (E 2 + 1) * hB2
  have H := mul_left_cancel₀ (X_ne_zero (R := ℚ)) (mul_right_cancel₀ hEnz h)
  linear_combination H

private theorem moment_zero : mom F 0 = 0 := by
  norm_num [mom, F, B, coeff_rescale, bernoulliPowerSeries, bernoulli_one]

private theorem moment_positive {r : ℕ} (hr : 0 < r) :
    mom F r = ((4 : ℚ) ^ (r + 1) - (2 : ℚ) ^ (r + 1)) * bernoulli (r + 1) / (r + 1) := by
  rw [mom, F, map_add, coeff_one, if_neg hr.ne', zero_add, coeff_mk, map_sub]
  simp only [B, coeff_rescale, bernoulliPowerSeries, coeff_mk, Algebra.algebraMap_self_apply]
  push_cast
  rw [Nat.factorial_succ]
  push_cast
  have hn : (r.factorial : ℚ) ≠ 0 := by exact_mod_cast r.factorial_ne_zero
  field_simp

private theorem moment_even {r : ℕ} (hr : Even r) : mom F r = 0 := by
  rcases eq_or_ne r 0 with rfl | hn
  · exact moment_zero
  rw [moment_positive (by omega), bernoulli_eq_zero_of_odd (hr.add_one) (by omega)]
  ring

private theorem moment_scaled (r : ℕ) :
    ∃ z : ℤ, mom F r = (2 : ℚ) ^ (r / 2) * z := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    by_cases he : Even r
    · exact ⟨0, by simp [moment_even he]⟩
    have hro := Nat.odd_iff.1 (Nat.not_even_iff_odd.1 he)
    have hr : 0 < r := by omega
    have hs := congrArg (fun P => mom P r) F_mul
    rw [mom_mul, sum_range_succ, mom_sub, mom_E] at hs
    have hlast : (r.choose r : ℚ) * mom F r * mom (E 2 + 1) (r - r) = 2 * mom F r := by
      rw [Nat.sub_self, Nat.choose_self, mom_add, mom_E]
      norm_num [mom]
      ring
    rw [hlast] at hs
    have h1 : mom (1 : PS) r = 0 := by simp [mom, coeff_one, hr.ne']
    rw [h1, sub_zero] at hs
    have hterm : ∀ i ∈ range r, ∃ z : ℤ,
        (r.choose i : ℚ) * mom F i * mom (E 2 + 1) (r - i) =
          (2 : ℚ) ^ (r / 2 + 1) * z := by
      intro i hi
      have hi' := mem_range.1 hi
      by_cases he' : Even i
      · exact ⟨0, by simp [moment_even he']⟩
      obtain ⟨z, hz⟩ := ih i hi'
      have hh : r / 2 + 1 ≤ i / 2 + (r - i) := by
        have hio := Nat.odd_iff.1 (Nat.not_even_iff_odd.1 he')
        omega
      have ht : mom (E 2 + 1) (r - i) = (2 : ℚ) ^ (r - i) := by
        rw [mom_add, mom_E]
        simp [mom, coeff_one, show r - i ≠ 0 by omega]
      refine ⟨(r.choose i : ℤ) * z * 2 ^ (i / 2 + (r - i) - (r / 2 + 1)), ?_⟩
      rw [hz, ht]
      push_cast
      have hpow : (2 : ℚ) ^ (i / 2) * 2 ^ (r - i) =
          2 ^ (r / 2 + 1) * 2 ^ (i / 2 + (r - i) - (r / 2 + 1)) := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      linear_combination ((r.choose i : ℚ) * z) * hpow
    choose z hz using hterm
    have hsum :
        (∑ i ∈ range r, (r.choose i : ℚ) * mom F i * mom (E 2 + 1) (r - i)) =
          (2 : ℚ) ^ (r / 2 + 1) * (↑(∑ i : Fin r, z i (mem_range.mpr i.isLt)) : ℚ) := by
      rw [Int.cast_sum, mul_sum, ← Fin.sum_univ_eq_sum_range]
      exact sum_congr rfl fun i _ => hz i (mem_range.mpr i.isLt)
    rw [hsum] at hs
    have htwo : (2 : ℚ) ^ r = (2 : ℚ) ^ (r / 2 + 1) * 2 ^ (r - (r / 2 + 1)) := by
      rw [← pow_add, Nat.add_sub_of_le (by omega)]
    norm_num only [Int.cast_ofNat] at hs
    rw [htwo, pow_succ] at hs
    refine ⟨(2 : ℤ) ^ (r - (r / 2 + 1)) - ∑ i : Fin r, z i (mem_range.mpr i.isLt), ?_⟩
    simp only [Int.cast_sub, Int.cast_pow, Int.cast_ofNat]
    linear_combination hs/2

private theorem intMom_F : IntMom F := by
  intro r
  obtain ⟨z, hz⟩ := moment_scaled r
  exact ⟨(2 : ℤ) ^ (r / 2) * z, by exact_mod_cast hz⟩

private theorem abs_bernoulli {n : ℕ} (hn : n ≠ 0) :
    |bernoulli (2 * n)| = (-1 : ℚ) ^ (n - 1) * bernoulli (2 * n) := by
  have h := hasSum_zeta_nat hn
  have hnnonneg : 0 ≤ (-1 : ℝ) ^ (n + 1) * (2 : ℝ) ^ (2 * n - 1) * Real.pi ^ (2 * n) *
      (bernoulli (2 * n) : ℝ) / (2 * n).factorial := by
    rw [← h.tsum_eq]
    exact tsum_nonneg fun _ => by positivity
  have hfpos : 0 < (2 : ℝ) ^ (2 * n - 1) * Real.pi ^ (2 * n) / (2 * n).factorial := by positivity
  have hsign : 0 ≤ (-1 : ℝ) ^ (n + 1) * (bernoulli (2 * n) : ℝ) := by
    apply nonneg_of_mul_nonneg_left _ hfpos
    linear_combination hnnonneg
  have he : (-1 : ℚ) ^ (n + 1) = (-1 : ℚ) ^ (n - 1) := by
    rw [show n + 1 = n - 1 + 2 by omega, pow_add]
    norm_num
  have hsign' : 0 ≤ (-1 : ℚ) ^ (n - 1) * bernoulli (2 * n) := by
    rw [← he]
    exact_mod_cast hsign
  have hsame := abs_of_nonneg hsign'
  simpa [abs_mul, abs_pow] using hsame

private theorem a_moment {n : ℕ} (hn : 1 ≤ n) :
    (2 : ℚ) ^ (n - 1) * a n = (-1 : ℚ) ^ (n - 1) * mom F (2 * n - 1) := by
  have hm : mom F (2 * n - 1) =
      ((4 : ℚ) ^ (2 * n) - (2 : ℚ) ^ (2 * n)) * bernoulli (2 * n) / (↑(2 * n : ℕ) : ℚ) := by
    have hidx : 2 * n - 1 + 1 = 2 * n := by omega
    have hcast : (↑(2 * n - 1 : ℕ) : ℚ) + 1 = (↑(2 * n : ℕ) : ℚ) := by exact_mod_cast hidx
    rw [moment_positive (r := 2 * n - 1) (by omega), hidx, hcast]
  have h4 : (4 : ℚ) ^ (2 * n) = ((2 : ℚ) ^ (2 * n)) ^ 2 := by
    rw [show (4 : ℚ) = 2 * 2 by norm_num, mul_pow, pow_two]
  have hscale : (2 : ℚ) ^ (n - 1) * 2 ^ n = 2 ^ (2 * n) / 2 := by
    apply (eq_div_iff (by norm_num)).2
    rw [← pow_add, ← pow_succ]
    congr 1
    omega
  rw [hm, a, abs_bernoulli (by omega), h4]
  push_cast
  calc
    _ = ((2 : ℚ) ^ (n - 1) * 2 ^ n) * (2 ^ (2 * n) - 1) *
        ((-1 : ℚ) ^ (n - 1) * bernoulli (2 * n)) / (n : ℚ) := by ring
    _ = _ := by rw [hscale]; ring

private theorem a_integer {n : ℕ} (hn : 1 ≤ n) : ∃ z : ℤ, a n = z := by
  obtain ⟨z, hz⟩ := moment_scaled (2 * n - 1)
  rw [show (2 * n - 1) / 2 = n - 1 by omega] at hz
  have hm := a_moment hn
  rw [hz] at hm
  refine ⟨(-1 : ℤ) ^ (n - 1) * z, ?_⟩
  push_cast
  apply mul_left_cancel₀ (by positivity : (2 : ℚ) ^ (n - 1) ≠ 0)
  linear_combination hm
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

private noncomputable def expMonoid : Submonoid PS where
  carrier := Set.range E
  one_mem' := ⟨0, E_zero⟩
  mul_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a+b, (E_add a b).symm⟩

private noncomputable def expPoly : Subalgebra ℤ PS := Algebra.adjoin ℤ (expMonoid : Set PS)

private theorem expPoly_E (b : ℤ) : E b ∈ expPoly := Algebra.subset_adjoin ⟨b, rfl⟩

private theorem expPoly_C (z : ℤ) : C (z : ℚ) ∈ expPoly := by
  rw [map_intCast]
  exact expPoly.intCast_mem z


private theorem odd_approx {q : ℕ} (hq : Odd q) :
    ∃ P ∈ expPoly, multiple q (P - F) := by
  let S : PS := ∑ j ∈ range q, (-E 2)^j
  have hS : S ∈ expPoly := sum_mem fun j _ => pow_mem (neg_mem (expPoly_E 2)) _
  let t : ℤ := ((q + 1) / 2 : ℕ)
  have ht : 2 * t = (q : ℤ) + 1 := by obtain ⟨w, hw⟩ := hq; dsimp [t]; omega
  let P : PS := C (t : ℚ) * (E 2 - 1) * S
  have hP : P ∈ expPoly := mul_mem (mul_mem (expPoly_C t) (sub_mem (expPoly_E 2) (one_mem _))) hS
  have hgeom : (E 2 + 1) * S = E (2 * q) + 1 := by
    dsimp [S]
    have hg := geom_sum_mul_neg (-E 2) q
    rw [hq.neg_pow, E_pow] at hg
    linear_combination hg
  obtain ⟨G, hG, hGe⟩ := multiple_exponential q 2
  rw [mul_comm (q : ℤ) 2] at hGe
  have htc : C (t : ℚ) * C (2 : ℚ) = C (q : ℚ) + 1 := by
    rw [← map_mul, ← map_one C, ← map_add]
    congr 1
    exact_mod_cast (mul_comm t 2 ▸ ht)
  have hC : IntMom (C (t : ℚ)) := by
    intro n
    by_cases hn : n = 0
    · subst n; exact ⟨t, by simp [mom]⟩
    · exact ⟨0, by unfold mom; rw [coeff_C_of_ne_zero hn]; simp⟩
  refine ⟨P, hP, F + C (t : ℚ) * F * G,
    intMom_add intMom_F (intMom_mul (intMom_mul hC intMom_F) hG), ?_⟩
  calc
    P - F = C (t : ℚ) * F * ((E 2 + 1) * S) - F := by
      dsimp [P]
      rw [← F_mul]
      ring
    _ = C (t : ℚ) * F * (E (2 * q) + 1) - F := by rw [hgeom]
    _ = C (t : ℚ) * F * (E (2 * q) - 1) + C (t : ℚ) * C (2 : ℚ) * F - F := by
      rw [map_ofNat C 2]
      ring
    _ = C (q : ℚ) * (F + C (t : ℚ) * F * G) := by rw [hGe, htc]; ring

private def Period (q t : ℕ) (f : PS) : Prop :=
  ∀ n : ℕ, q ≤ n → ∃ z : ℤ, mom f (n + t) - mom f n = (q : ℚ) * z

private theorem expPoly_period (q t : ℕ) (hq : 0 < q) (ht : q.totient ∣ t)
    {P : PS} (hP : P ∈ expPoly) : Period q t P := by
  have hs : P ∈ Submodule.span ℤ (expMonoid : Set PS) := by
    change P ∈ expPoly.toSubmodule at hP
    rwa [expPoly, Algebra.adjoin_eq_span, Submonoid.closure_eq] at hP
  clear hP
  induction hs using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨b, rfl⟩ := hf
    intro n hn
    have he := ReducedTangentArithmetic.int_pow_period hq b hn ht
    obtain ⟨z, hz⟩ := Int.modEq_iff_dvd.mp he.symm
    refine ⟨z, ?_⟩
    rw [mom_E, mom_E]
    exact_mod_cast hz
  | zero => intro n _; exact ⟨0, by simp [mom]⟩
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
    have hc : c • f = C (c : ℚ) * f := by rw [zsmul_eq_mul, map_intCast]
    refine ⟨c*u, ?_⟩
    rw [hc, mom_C, mom_C, Int.cast_mul]
    linear_combination (c : ℚ) * hu

private theorem raw_period {q t : ℕ} (hq : Odd q) (ht : q.totient ∣ t) : Period q t F := by
  intro n hn
  obtain ⟨P, hP, G, hG, hEq⟩ := odd_approx hq
  have hp : 0 < q := hq.pos
  obtain ⟨z, hz⟩ := expPoly_period q t hp ht hP n hn
  obtain ⟨u, hu⟩ := hG (n+t)
  obtain ⟨v, hv⟩ := hG n
  have hnew := congrArg (fun f => mom f (n+t)) hEq
  have hold := congrArg (fun f => mom f n) hEq
  rw [mom_sub, mom_C, hu] at hnew
  rw [mom_sub, mom_C, hv] at hold
  refine ⟨z - u + v, ?_⟩
  push_cast
  linear_combination hz - hnew + hold

private theorem odd_period {q t n : ℕ} (hq : Odd q) (ht : q.totient ∣ t)
    (hn : 1 ≤ n) (hnq : q ≤ n) {u v : ℤ}
    (hu : a (n + t) = u) (hv : a n = v) : u ≡ v [ZMOD q] := by
  rcases eq_or_ne q 1 with rfl | hq1
  · simp [Int.ModEq]
  have hq2 : 2 < q := by have hh := Nat.odd_iff.1 hq; omega
  have hqi := Nat.coprime_two_left.2 hq
  have hb : IsUnit (2 : ZMod q) := (ZMod.isUnit_iff_coprime 2 q).2 hqi
  have hbpow : (2 : ZMod q) ^ t = 1 := by
    obtain ⟨d, rfl⟩ := ht
    rw [pow_mul]
    have h := (ZMod.natCast_eq_natCast_iff _ _ q).2 (Nat.ModEq.pow_totient hqi)
    push_cast at h
    rw [h, one_pow]
  have hs : (-1 : ZMod q) ^ t = 1 := by
    obtain ⟨d, rfl⟩ := ht
    rw [pow_mul, (Nat.totient_even hq2).neg_one_pow, one_pow]
  have ht₂ : q.totient ∣ 2 * t := ht.trans (dvd_mul_left t 2)
  obtain ⟨f, hf⟩ := intMom_F (2 * (n + t) - 1)
  obtain ⟨g, hg⟩ := intMom_F (2 * n - 1)
  obtain ⟨w, hw⟩ := raw_period hq ht₂ (2 * n - 1) (by omega)
  rw [show 2 * n - 1 + 2 * t = 2 * (n + t) - 1 by omega, hf, hg] at hw
  have hw' : f - g = (q : ℤ) * w := by exact_mod_cast hw
  have hm : (f : ZMod q) = (g : ZMod q) := by
    apply (ZMod.intCast_eq_intCast_iff _ _ q).2
    exact (Int.modEq_iff_dvd.2 ⟨w, hw'⟩).symm
  have h₁ := a_moment (n := n + t) (by omega)
  have h₂ := a_moment hn
  rw [hu, hf] at h₁
  rw [hv, hg] at h₂
  have h₁' : (2 : ℤ) ^ (n + t - 1) * u = (-1 : ℤ) ^ (n + t - 1) * f := by exact_mod_cast h₁
  have h₂' : (2 : ℤ) ^ (n - 1) * v = (-1 : ℤ) ^ (n - 1) * g := by exact_mod_cast h₂
  have h₁'' := congrArg (fun z : ℤ => (z : ZMod q)) h₁'
  have h₂'' := congrArg (fun z : ℤ => (z : ZMod q)) h₂'
  push_cast at h₁'' h₂''
  rw [show n + t - 1 = (n - 1) + t by omega, pow_add, pow_add, hbpow, hs, mul_one,
    mul_one, hm] at h₁''
  apply (ZMod.intCast_eq_intCast_iff _ _ q).mp
  exact (hb.pow (n - 1)).mul_right_injective (h₁''.trans h₂''.symm)

private theorem odd_den_of_dvd {d e : ℕ} (hd : d ∣ e) (he : Odd e) : Odd d :=
  Nat.coprime_two_left.mp (he.coprime_two_left.coprime_dvd_right hd)

private theorem odd_den_add {x y : ℚ} (hx : Odd x.den) (hy : Odd y.den) :
    Odd (x + y).den := odd_den_of_dvd (Rat.add_den_dvd x y) (hx.mul hy)

private theorem odd_den_sub {x y : ℚ} (hx : Odd x.den) (hy : Odd y.den) :
    Odd (x - y).den := odd_den_of_dvd (Rat.sub_den_dvd x y) (hx.mul hy)

private theorem odd_den_sum {ι : Type*} (S : Finset ι) (f : ι → ℚ)
    (h : ∀ i ∈ S, Odd (f i).den) : Odd (∑ i ∈ S, f i).den := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons a S ha ih =>
    rw [sum_cons]
    exact odd_den_add (h _ (by simp)) (ih fun i hi => h i (by simp [hi]))

/-- The factor 2 removes the entire even part of a positive even-index Bernoulli
denominator. -/
private theorem odd_den_two_bernoulli {n : ℕ} (hn : 0 < n) :
    Odd ((2 : ℚ) * bernoulli (2 * n)).den := by
  let P := (range (2 * n + 2)).filter (fun p => p.Prime ∧ (p - 1) ∣ 2 * n)
  have h2 : 2 ∈ P := by simpa [P, Nat.prime_two] using hn
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen n
  change (z : ℚ) = bernoulli (2 * n) + ∑ p ∈ P, (1 : ℚ) / p at hz
  rw [← sum_erase_add P (fun p : ℕ => (1 : ℚ) / p) h2] at hz
  have hs : Odd (∑ p ∈ P.erase 2, (2 : ℚ) / p).den := by
    apply odd_den_sum
    intro p hp
    have hprime := (mem_filter.mp (mem_of_mem_erase hp)).2.1
    have hpodd : Odd p := hprime.odd_of_ne_two (ne_of_mem_erase hp)
    rw [div_eq_mul_inv]
    apply odd_den_of_dvd (Rat.mul_den_dvd _ _)
    rw [Rat.inv_natCast_den_of_pos hprime.pos]
    simpa using hpodd
  have hmul : (∑ p ∈ P.erase 2, (2 : ℚ) / p) = 2 * ∑ p ∈ P.erase 2, (1 : ℚ) / p := by
    rw [mul_sum]
    exact sum_congr rfl fun p _ => by ring
  have H : (2 : ℚ) * bernoulli (2 * n) =
      ((2 * z - 1 : ℤ) : ℚ) - ∑ p ∈ P.erase 2, (2 : ℚ) / p := by
    push_cast
    rw [hmul]
    push_cast at hz
    linear_combination -2 * hz
  rw [H]
  apply odd_den_sub _ hs
  rw [Rat.den_intCast]
  decide

private theorem twice_le_two_pow (e : ℕ) : 2 * e ≤ 2 ^ e := by
  induction e with
  | zero => norm_num
  | succ e ih =>
    have hp : 1 ≤ (2 : ℕ) ^ e := Nat.one_le_pow _ _ (by decide)
    rw [pow_succ]
    omega

private theorem two_pow_coprime {e n : ℕ} (h : Odd n) :
    IsCoprime ((2 : ℤ)^e) (n : ℤ) :=
  (Int.isCoprime_two_left.2 (by exact_mod_cast h)).pow_left

/-- A sufficiently late reduced tangent number vanishes modulo each fixed power
of two. -/
private theorem dyadic_dvd {L n : ℕ} (hn : 2 * (L + 1) ≤ n) {b : ℤ} (hb : a n = b) :
    (2 : ℤ) ^ L ∣ b := by
  let x := (2 : ℚ) * bernoulli (2 * n)
  obtain ⟨e, u, hu, hnu⟩ := Nat.exists_eq_two_pow_mul_odd (show n ≠ 0 by omega)
  have hp : 2 ^ e ≤ n := by
    rw [hnu]
    simpa using Nat.mul_le_mul_left (2 ^ e) hu.pos
  have he : e + L ≤ n - 1 := by
    have := (twice_le_two_pow e).trans hp
    omega
  have hd := odd_den_two_bernoulli (show 0 < n by omega)
  change Odd x.den at hd
  have hxd' : 2 * |bernoulli (2 * n)| * (x.den : ℚ) = (|x.num| : ℚ) := by
    have h := congrArg (fun z : ℚ => |z|) x.mul_den_eq_num
    rw [abs_mul, abs_of_nonneg (show 0 ≤ (x.den : ℚ) by positivity), ← Int.cast_abs] at h
    simpa [x, abs_mul] using h
  have hR : (b : ℚ) * (n : ℚ) * (x.den : ℚ) =
      (2 : ℚ) ^ (n - 1) * ((2 : ℚ) ^ (2 * n) - 1) * (|x.num| : ℚ) := by
    rw [← hb, a, div_mul_cancel₀ _ (by exact_mod_cast (show n ≠ 0 by omega)),
      show n = n - 1 + 1 by omega, pow_succ]
    -- Keep the original index within the Bernoulli number and the remaining power.
    simp only [show n - 1 + 1 = n by omega]
    linear_combination ((2 : ℚ) ^ (n - 1) * ((2 : ℚ) ^ (2 * n) - 1)) * hxd'
  have hI : b * (n : ℤ) * (x.den : ℤ) =
      (2 : ℤ) ^ (n - 1) * ((2 : ℤ) ^ (2 * n) - 1) * |x.num| := by exact_mod_cast hR
  have hD : (2 : ℤ) ^ (e + L) ∣ b * (n : ℤ) * (x.den : ℤ) := by
    rw [hI]
    exact (pow_dvd_pow _ he).trans (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)
  rw [hnu, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add,
    show b * ((2 : ℤ)^e * u) * x.den = (2 : ℤ)^e * (b * u * x.den) by ring] at hD
  have h := (mul_dvd_mul_iff_left (by positivity : (2 : ℤ)^e ≠ 0)).mp hD
  exact (two_pow_coprime hu).dvd_of_dvd_mul_right ((two_pow_coprime hd).dvd_of_dvd_mul_right h)

theorem main : type_of% @OMA.S_oeis_a002105.main := by
  intro k hk
  obtain ⟨e, q, hq, hkq⟩ := Nat.exists_eq_two_pow_mul_odd (show k ≠ 0 by omega)
  refine ⟨max q (2 * (e + 1)), ?_⟩
  intro n hn hn1
  let t := k.totient
  have ht : q.totient ∣ t := Nat.totient_dvd_of_dvd (by rw [hkq]; exact dvd_mul_left _ _)
  have hnq : q ≤ n := (le_max_left _ _).trans hn
  have hne : 2 * (e + 1) ≤ n := (le_max_right _ _).trans hn
  obtain ⟨u, hu⟩ := a_integer (n := n + t) (by omega)
  obtain ⟨v, hv⟩ := a_integer hn1
  have ho : (q : ℤ) ∣ u - v := Int.modEq_iff_dvd.mp (odd_period hq ht hn1 hnq hu hv).symm
  have htwo : (2 : ℤ) ^ e ∣ u - v :=
    dvd_sub (dyadic_dvd (hne.trans (Nat.le_add_right _ _)) hu) (dyadic_dvd hne hv)
  have hcrt' : (k : ℤ) ∣ u - v := by
    rw [hkq, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    exact (two_pow_coprime hq).mul_dvd htwo ho
  obtain ⟨z, hz⟩ := hcrt'
  refine ⟨z, ?_⟩
  rw [hu, hv]
  exact_mod_cast hz

end ReducedTangent

theorem OMA.solution : type_of% @OMA.S_oeis_a002105.main := ReducedTangent.main

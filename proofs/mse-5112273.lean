import OMAStatements.S_mse_5112273
import Mathlib

open scoped BigOperators

namespace OMA.SineRatio

open Complex Polynomial

private noncomputable def phase (p : ℚ) : ℂ :=
  Complex.exp ((p : ℂ) * (Real.pi : ℂ) * I)

private noncomputable def chord (p : ℚ) : ℂ :=
  phase p - phase (-p)

private theorem phase_period (p : ℚ) : (phase p) ^ (2 * p.den) = 1 := by
  unfold phase
  rw [← Complex.exp_nat_mul]
  have hd : (p.den : ℂ) ≠ 0 := by exact_mod_cast p.den_nz
  convert Complex.exp_int_mul_two_pi_mul_I p.num using 2
  rw [Rat.cast_def]
  push_cast
  field_simp


private theorem phase_integral (p : ℚ) : IsIntegral ℤ (phase p) := by
  apply IsIntegral.of_pow (n := 2 * p.den)
  · have := p.den_pos
    omega
  · rw [phase_period]
    exact isIntegral_one

private theorem chord_integral (p : ℚ) : IsIntegral ℤ (chord p) :=
  (phase_integral p).sub (phase_integral (-p))

private theorem chord_eq_sine (p : ℚ) :
    chord p = 2 * ((Real.sin ((p : ℝ) * Real.pi) : ℝ) : ℂ) * I := by
  unfold chord phase
  rw [Rat.cast_neg, neg_mul, neg_mul, ← Complex.two_sinh, Complex.sinh_mul_I,
    ← mul_assoc, Complex.ofReal_sin]
  push_cast
  rfl

private theorem phase_mul_chord (p : ℚ) : phase p * chord p = phase p ^ 2 - 1 := by
  have h : phase p * phase (-p) = 1 := by
    unfold phase
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 2
    push_cast
    ring
  rw [chord, mul_sub, h, pow_two]

private theorem phase_order (p : ℚ) (hp : 0 < (p : ℝ)) (hp' : (p : ℝ) < 1/2) :
    3 ≤ orderOf ((phase p)^2) := by
  set ζ := (phase p)^2
  let n := orderOf ζ
  have hn : 0 < n := orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr
    ⟨p.den, p.den_pos, by
      change (phase p ^ 2) ^ p.den = 1
      rw [← pow_mul, phase_period]⟩)
  change 3 ≤ n
  by_contra! hn'
  have he : Complex.exp (((n : ℂ) * (p : ℂ)) * (2 * (Real.pi : ℂ) * I)) = 1 := by
    have h : (phase p ^ 2) ^ n = 1 := (IsPrimitiveRoot.orderOf ζ).pow_eq_one
    rw [← pow_mul, phase, ← Complex.exp_nat_mul] at h
    convert h using 2
    push_cast
    ring
  obtain ⟨j,hj⟩ := Complex.exp_eq_one_iff.mp he
  have ht : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  have hc : (n : ℂ) * (p : ℂ) = (j : ℂ) := mul_right_cancel₀ ht hj
  have hr : (n : ℝ) * (p : ℝ) = (j : ℝ) := by
    simpa [Complex.mul_re] using congrArg Complex.re hc
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn2 : (n : ℝ) ≤ 2 := by exact_mod_cast (show n ≤ 2 by omega)
  have hjpos : (0 : ℝ) < j := hr ▸ mul_pos hnR hp
  have hjlt : (j : ℝ) < 1 := by nlinarith
  have hji : 0 < j := by exact_mod_cast hjpos
  have hji' : j < 1 := by exact_mod_cast hjlt
  omega

private theorem bezout_integral {u v : ℂ} (hu : IsIntegral ℤ u) (hv : IsIntegral ℤ v)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (h : (b : ℂ) * u = (a : ℂ) * v) :
    IsIntegral ℤ (u / (a : ℂ)) ∧ IsIntegral ℤ (v / (b : ℂ)) := by
  let c := Nat.gcdA a b
  let d := Nat.gcdB a b
  have hi : (a : ℤ)*c + (b : ℤ)*d = 1 := by
    simpa only [c, d, hab.gcd_eq_one, Int.natCast_one] using (Nat.gcd_eq_gcd_ab a b).symm
  have hiC : (a : ℂ)*(c : ℂ) + (b : ℂ)*(d : ℂ) = 1 := by exact_mod_cast hi
  have hic : IsIntegral ℤ (c : ℂ) := isIntegral_algebraMap
  have hid : IsIntegral ℤ (d : ℂ) := isIntegral_algebraMap
  have hsum := (hic.mul hu).add (hid.mul hv)
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbC : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hx : u / (a : ℂ) = (c : ℂ)*u + (d : ℂ)*v := by
    rw [div_eq_iff haC]
    linear_combination -u * hiC + d * h
  have hy : v / (b : ℂ) = (c : ℂ)*u + (d : ℂ)*v := by
    rw [div_eq_iff hbC]
    linear_combination -v * hiC - c * h
  exact ⟨hx ▸ hsum, hy ▸ hsum⟩

private theorem root_product_integral {ζ : ℂ} {n a : ℕ}
    (hζ : IsPrimitiveRoot ζ n) (hn : 0 < n) (hi : IsIntegral ℤ ζ)
    (ha : IsIntegral ℤ ((1 - ζ) / (a : ℂ))) :
    IsIntegral ℤ ((n : ℂ) / (a : ℂ) ^ (n-1)) := by
  classical
  let P : ℂ[X] := X^n - 1
  have hP : P.roots = (Multiset.range n).map (ζ ^ ·) := by
    simpa [P, nthRoots] using hζ.nthRoots_eq (show (1 : ℂ)^n = 1 by simp)
  have h1 : 1 ∈ P.roots := by
    rw [hP]
    exact Multiset.mem_map.mpr ⟨0, by simpa using hn, pow_zero ζ⟩
  have hm : P.Monic := by
    exact monic_X_pow_sub_C 1 hn.ne'
  let s := P.roots.erase 1
  have hs : s.card = n-1 := by
    change (P.roots.erase (1 : ℂ)).card = n-1
    rw [Multiset.card_erase_of_mem h1, hP, Multiset.card_map, Multiset.card_range,
      Nat.pred_eq_sub_one]
  have hprod : (s.map (fun z => 1-z)).prod = (n : ℂ) := by
    rw [← (IsAlgClosed.splits P).eval_root_derivative hm h1]
    simp [P, derivative_X_pow]
  have hintegral (k : ℕ) : IsIntegral ℤ ((1 - ζ^k) / (a : ℂ)) := by
    have hgeom : 1 - ζ^k = (∑ j ∈ Finset.range k, ζ^j) * (1-ζ) := by
      linear_combination geom_sum_mul ζ k
    rw [hgeom, mul_div_assoc]
    exact (IsIntegral.sum _ (fun j _ => hi.pow j)).mul ha
  have hwhole : IsIntegral ℤ ((s.map fun z => (1-z)/(a : ℂ)).prod) := by
    apply IsIntegral.multiset_prod
    intro x hx
    obtain ⟨z,hz,rfl⟩ := Multiset.mem_map.mp hx
    have hz' : z ∈ P.roots := Multiset.mem_of_mem_erase hz
    rw [hP] at hz'
    obtain ⟨k,_,rfl⟩ := Multiset.mem_map.mp hz'
    exact hintegral k
  simpa only [Multiset.prod_map_div, hprod, Multiset.map_const', Multiset.prod_replicate, hs]
    using hwhole

private theorem power_exceeds (k : ℕ) (hk : 2 ≤ k) : k+1 < 2^k := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction j with
  | zero => decide
  | succ j ih =>
    have he : 2 + (j + 1) = (2 + j) + 1 := by omega
    rw [he, pow_succ]
    omega

private theorem denominator_one (p : ℚ) (hp : 0 < (p : ℝ))
    (hp' : (p : ℝ) < 1/2) {a : ℕ} (ha : 0 < a)
    (hi : IsIntegral ℤ (chord p / (a : ℂ))) : a = 1 := by
  let ζ := phase p ^ 2
  let n := orderOf ζ
  have hn : 3 ≤ n := phase_order p hp hp'
  have hroot : IsPrimitiveRoot ζ n := IsPrimitiveRoot.orderOf ζ
  have hneg : (1 - ζ) / (a : ℂ) = -(phase p * (chord p / (a : ℂ))) := by
    change (1 - phase p ^ 2) / (a : ℂ) = -(phase p * (chord p / (a : ℂ)))
    simp only [div_eq_mul_inv]
    linear_combination ((a : ℂ)⁻¹) * phase_mul_chord p
  have h := root_product_integral hroot (by omega) ((phase_integral p).pow 2)
    (hneg.symm ▸ ((phase_integral p).mul hi).neg)
  have hrat : IsIntegral ℤ ((n : ℚ) / (a : ℚ) ^ (n-1)) :=
    (isIntegral_algebraMap_iff (R := ℤ) (algebraMap ℚ ℂ).injective).mp (by push_cast; exact h)
  obtain ⟨z,hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hrat
  change (z : ℚ) = _ at hz
  have hzpos : (0 : ℚ) < z := hz.symm ▸ (by positivity)
  have hzi : (0 : ℤ) < z := by exact_mod_cast hzpos
  have hz1 : (1 : ℚ) ≤ z := by exact_mod_cast (show (1 : ℤ) ≤ z by omega)
  have hpow : (a : ℚ) ^ (n-1) ≠ 0 := by positivity
  have hle : (a : ℚ) ^ (n-1) ≤ n := calc
    _ = 1 * (a : ℚ) ^ (n-1) := by simp
    _ ≤ (z : ℚ) * (a : ℚ) ^ (n-1) :=
      mul_le_mul_of_nonneg_right hz1 (by positivity)
    _ = n := (eq_div_iff hpow).mp hz
  have hle' : a ^ (n-1) ≤ n := by exact_mod_cast hle
  by_contra hane
  have htwo : 2 ≤ a := by omega
  have hpows : 2 ^ (n-1) ≤ a ^ (n-1) := Nat.pow_le_pow_left htwo _
  have hex := power_exceeds (n-1) (by omega)
  omega

end OMA.SineRatio

open OMA.SineRatio in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_5112273.main) := by
  rintro ⟨p,q,hp,hp',hq,hq',hne,r,hr⟩
  have hpθ : 0 < (p : ℝ) * Real.pi := mul_pos hp Real.pi_pos
  have hqθ : 0 < (q : ℝ) * Real.pi := mul_pos hq Real.pi_pos
  have hpθ' : (p : ℝ) * Real.pi < Real.pi/2 := by nlinarith [mul_lt_mul_of_pos_right hp' Real.pi_pos]
  have hqθ' : (q : ℝ) * Real.pi < Real.pi/2 := by nlinarith [mul_lt_mul_of_pos_right hq' Real.pi_pos]
  have hsP := Real.sin_pos_of_pos_of_lt_pi hpθ (by linarith [Real.pi_pos])
  have hsQ := Real.sin_pos_of_pos_of_lt_pi hqθ (by linarith [Real.pi_pos])
  have hrpos : (0 : ℝ) < r := hr ▸ div_pos hsP hsQ
  let a := r.num.natAbs
  let b := r.den
  have hnump : 0 < r.num := by
    rw [Rat.cast_def] at hrpos
    have hb : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
    exact_mod_cast ((div_pos_iff_of_pos_right hb).mp hrpos)
  have ha : 0 < a := by
    dsimp [a]
    omega
  have hb : 0 < b := r.den_pos
  have hab : a.Coprime b := r.reduced
  have hac : (a : ℤ) = r.num := Int.natAbs_of_nonneg hnump.le
  have hra : (r : ℝ) = (a : ℝ) / (b : ℝ) := by
    rw [Rat.cast_def, ← hac]
    rfl
  rw [hra] at hr
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hs := (div_eq_div_iff hsQ.ne' hbR).mp hr
  have hsc : ((b : ℂ) * (Real.sin ((p : ℝ) * Real.pi) : ℂ)) =
      ((a : ℂ) * (Real.sin ((q : ℝ) * Real.pi) : ℂ)) := by
    exact_mod_cast (by simpa [mul_comm] using hs :
      (b : ℝ) * Real.sin ((p : ℝ) * Real.pi) = (a : ℝ) * Real.sin ((q : ℝ) * Real.pi))
  have hch : (b : ℂ) * chord p = (a : ℂ) * chord q := by
    rw [chord_eq_sine, chord_eq_sine]
    linear_combination 2 * Complex.I * hsc
  obtain ⟨h₁,h₂⟩ := bezout_integral (chord_integral p) (chord_integral q) a b ha hb hab hch
  have ha1 := denominator_one p hp hp' ha h₁
  have hb1 := denominator_one q hq hq' hb h₂
  rw [ha1,hb1] at hs
  simp only [Nat.cast_one, mul_one, one_mul] at hs
  have hang := Real.strictMonoOn_sin.injOn
    (show (p : ℝ) * Real.pi ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) from
      ⟨by linarith [Real.pi_pos], hpθ'.le⟩)
    (show (q : ℝ) * Real.pi ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) from
      ⟨by linarith [Real.pi_pos], hqθ'.le⟩) hs
  exact hne (by exact_mod_cast (mul_right_cancel₀ Real.pi_ne_zero hang))
import OMAStatements.S_oeis_a372314
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic

namespace OMA.P_oeis_a372314

open OMA.S_oeis_a372314

/-- Sum of `quadraticChar (ZMod p)` over all `x : ZMod p` is `0` for odd prime `p`. -/
private lemma sum_quadraticChar_eq_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ∑ x : ZMod p, quadraticChar (ZMod p) x = 0 := by
  have : NeZero (2 : ZMod p) := ⟨by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
    have h2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    have := (Fact.out : p.Prime).two_le
    omega⟩
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  exact quadraticChar_sum_zero hchar

/-- For prime `p ≡ 3 (mod 4)`, `∑ t : ZMod p, χ((1 + 3*t + 2*t^2) * t) = 0`. -/
private lemma sum_cubic_32_eq_zero {p : ℕ} [Fact p.Prime] (hp4 : p % 4 = 3) :
    ∑ t : ZMod p, quadraticChar (ZMod p) ((1 + 3 * t + 2 * t ^ 2) * t) = 0 := by
  let e1 : ZMod p ≃ ZMod p := Equiv.inv (ZMod p)
  have h1 : ∑ t : ZMod p, quadraticChar (ZMod p) ((1 + 3 * t + 2 * t ^ 2) * t) =
      ∑ u : ZMod p, quadraticChar (ZMod p) (u ^ 3 + 3 * u ^ 2 + 2 * u) := by
    rw [← Fintype.sum_equiv e1 (fun u => quadraticChar (ZMod p) ((1 + 3 * u⁻¹ + 2 * (u⁻¹) ^ 2) * u⁻¹))
        (fun t => quadraticChar (ZMod p) ((1 + 3 * t + 2 * t ^ 2) * t)) (fun _ => rfl)]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    by_cases hu : u = 0
    · subst hu; simp
    · have hu2 : u ^ 2 ≠ 0 := pow_ne_zero 2 hu
      have hid : (1 + 3 * u⁻¹ + 2 * (u⁻¹) ^ 2) * u⁻¹ = (u ^ 2)⁻¹ ^ 2 * (u ^ 3 + 3 * u ^ 2 + 2 * u) := by
        field_simp [hu]
      rw [hid, map_mul, map_pow, quadraticChar_sq_one (inv_ne_zero hu2), one_mul]
  rw [h1]
  have h2 : ∑ u : ZMod p, quadraticChar (ZMod p) (u ^ 3 + 3 * u ^ 2 + 2 * u) =
      ∑ w : ZMod p, quadraticChar (ZMod p) (w ^ 3 - w) := by
    refine Fintype.sum_equiv (Equiv.addRight (1 : ZMod p)) _ _ (fun u => ?_)
    congr 1
    change u ^ 3 + 3 * u ^ 2 + 2 * u = (u + 1) ^ 3 - (u + 1)
    ring
  rw [h2]
  have hneg1 : quadraticChar (ZMod p) (-1) = -1 := by
    have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
    rw [quadraticChar_neg_one hchar, ZMod.card p]
    have h3 : (p : ZMod 4) = 3 := by rw [← ZMod.natCast_mod, hp4]; rfl
    rw [h3]; decide
  have hodd : ∑ w : ZMod p, quadraticChar (ZMod p) (w ^ 3 - w) =
      - ∑ w : ZMod p, quadraticChar (ZMod p) (w ^ 3 - w) := by
    rw [← Finset.sum_neg_distrib]
    refine Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ (fun w => ?_)
    simp only [Equiv.neg_apply]
    have hpoly : (-w) ^ 3 - (-w) = (-1) * (w ^ 3 - w) := by ring
    rw [hpoly, map_mul (quadraticChar (ZMod p)) (-1), hneg1]; ring
  linarith

private lemma pow_mod_four_eq_three {p e : ℕ} (hp4 : p % 4 = 3) (he : Odd e) :
    p ^ e % 4 = 3 := by
  obtain ⟨k, rfl⟩ := he
  induction k with
  | zero => simpa using hp4
  | succ k ih =>
    have h1 : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
    have hp2 : p ^ 2 % 4 = 1 := by
      rw [sq, Nat.mul_mod, hp4]
    rw [h1, pow_add, Nat.mul_mod, ih, hp2]

private lemma legendreSym_pow_odd {p : ℕ} [Fact p.Prime] (a : ℤ) {e : ℕ} (he : Odd e) :
    legendreSym p a ^ e = legendreSym p a := by
  obtain ⟨k, rfl⟩ := he
  change (quadraticChar (ZMod p) (a : ZMod p)) ^ (2 * k + 1) = quadraticChar (ZMod p) (a : ZMod p)
  by_cases ha : (a : ZMod p) = 0
  · rw [ha, MulChar.map_zero, zero_pow (by omega)]
  · have hsq : (quadraticChar (ZMod p) (a : ZMod p)) ^ 2 = 1 :=
      quadraticChar_sq_one ha
    rw [pow_succ, pow_mul, hsq, one_pow, one_mul]

private lemma prove_a372314 (n : ℕ) (hn : 1 ≤ n) (hdet : (sunJacobiMatrix (2 * n)).det ≠ 0) :
    ∃ x y : ℕ, x ^ 2 + y ^ 2 = 4 * n + 1 := by
  by_contra hnsq
  set m := 4 * n + 1
  have hm_eq : 2 * (2 * n) + 1 = m := by omega
  have hm5 : 5 ≤ m := by omega
  have hm0 : m ≠ 0 := by omega
  have hnsq' : ¬ ∃ x y : ℕ, m = x ^ 2 + y ^ 2 := fun ⟨x, y, h⟩ => hnsq ⟨x, y, h.symm⟩
  -- By Fermat's two-squares theorem, there is a prime `p ≡ 3 (mod 4)` with `Odd (padicValNat p m)`.
  rw [Nat.eq_sq_add_sq_iff] at hnsq'
  push Not at hnsq'
  obtain ⟨p, hp_mem, hp4, hnot_even⟩ := hnsq'
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  have : Fact p.Prime := ⟨hp⟩
  have he_odd : Odd (padicValNat p m) := Nat.not_even_iff_odd.mp hnot_even
  set e := padicValNat p m
  have he_eq : m.factorization p = e := Nat.factorization_def m hp
  have he1 : 1 ≤ e := by obtain ⟨k, hk⟩ := he_odd; omega
  have hpe_dvd : p ^ e ∣ m := by
    rw [← he_eq]; exact Nat.ordProj_dvd m p
  obtain ⟨r, hr⟩ := hpe_dvd
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr
  have hnotp_r : ¬ p ∣ r := by
    intro hpr
    have h1 : p ^ (e + 1) ∣ m := by
      rw [hr, pow_succ]
      obtain ⟨t, rfl⟩ := hpr
      exact ⟨t, by ring⟩
    have h2 := (hp.pow_dvd_iff_le_factorization hm0).mp h1
    omega
  have hr4 : r % 4 = 3 := by
    have hpe4 : p ^ e % 4 = 3 := pow_mod_four_eq_three hp4 he_odd
    have hm4 : m % 4 = 1 := by omega
    rw [hr, Nat.mul_mod, hpe4] at hm4
    omega
  have hr3 : 3 ≤ r := by omega
  have hp3 : 3 ≤ p := by omega
  have hp_le_pe : p ≤ p ^ e := Nat.le_self_pow (by omega) p
  let N := 2 * (2 * n) - 2
  have hN : N = m - 3 := by omega
  let v : Fin N → ℤ := fun j =>
    if r ∣ (j.val + 2) ∧ (j.val + 2) / r < p then
      legendreSym p (((j.val + 2) / r : ℕ) : ℤ)
    else 0
  have hv_ne : v ≠ 0 := by
    intro h0
    have hlt : r - 2 < N := by
      have h1 : p * r ≤ m := by rw [hr]; exact Nat.mul_le_mul_right r hp_le_pe
      have h2 : 3 * r ≤ p * r := Nat.mul_le_mul_right r hp3
      omega
    have h1 := congr_fun h0 ⟨r - 2, hlt⟩
    simp only [v, Pi.zero_apply] at h1
    have hadd : r - 2 + 2 = r := by omega
    rw [hadd, Nat.div_self (by omega)] at h1
    rw [if_pos ⟨dvd_refl r, by omega⟩, Nat.cast_one, legendreSym.at_one] at h1
    omega
  have hmul : (sunJacobiMatrix (2 * n)).mulVec v = 0 := by
    ext i
    simp only [Matrix.mulVec, dotProduct, sunJacobiMatrix, Matrix.of_apply, Pi.zero_apply, v]
    set I : ℕ := i.val + 2
    have hfilt : ∑ j : Fin N,
        jacobiSym ((I : ℤ) ^ 2 + 3 * (I : ℤ) * ((j.val + 2 : ℕ) : ℤ) + 2 * ((j.val + 2 : ℕ) : ℤ) ^ 2) (2 * (2 * n) + 1) *
        (if r ∣ (j.val + 2) ∧ (j.val + 2) / r < p then legendreSym p (((j.val + 2) / r : ℕ) : ℤ) else 0) =
        ∑ k ∈ Finset.Icc 1 (p - 1),
          jacobiSym ((I : ℤ) ^ 2 + 3 * (I : ℤ) * ((k * r : ℕ) : ℤ) + 2 * ((k * r : ℕ) : ℤ) ^ 2) m *
          legendreSym p (k : ℤ) := by
      have h1 : ∑ j : Fin N,
          jacobiSym ((I : ℤ) ^ 2 + 3 * (I : ℤ) * ((j.val + 2 : ℕ) : ℤ) + 2 * ((j.val + 2 : ℕ) : ℤ) ^ 2) (2 * (2 * n) + 1) *
          (if r ∣ (j.val + 2) ∧ (j.val + 2) / r < p then legendreSym p (((j.val + 2) / r : ℕ) : ℤ) else 0) =
          ∑ j ∈ Finset.univ.filter (fun j : Fin N => r ∣ (j.val + 2) ∧ (j.val + 2) / r < p),
            jacobiSym ((I : ℤ) ^ 2 + 3 * (I : ℤ) * ((j.val + 2 : ℕ) : ℤ) + 2 * ((j.val + 2 : ℕ) : ℤ) ^ 2) m *
            legendreSym p (((j.val + 2) / r : ℕ) : ℤ) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hm_eq]; split_ifs <;> simp
      rw [h1]
      refine Finset.sum_bij (fun j _ => (j.val + 2) / r) ?_ ?_ ?_ ?_
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Icc] at hj ⊢
        obtain ⟨⟨k, hk⟩, hlt⟩ := hj
        have hdiv : (j.val + 2) / r = k := by rw [hk, Nat.mul_div_cancel_left k (by omega)]
        rw [hdiv] at hlt ⊢
        have hkpos : 1 ≤ k := by
          rcases Nat.eq_zero_or_pos k with rfl | h
          · simp at hk
          · exact h
        omega
      · intro j1 h1 j2 h2 heq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        have e1 : j1.val + 2 = (j1.val + 2) / r * r := (Nat.div_mul_cancel h1.1).symm
        have e2 : j2.val + 2 = (j2.val + 2) / r * r := (Nat.div_mul_cancel h2.1).symm
        rw [heq] at e1
        exact Fin.ext (by omega)
      · intro k hk
        simp only [Finset.mem_Icc] at hk
        have hkr_ge : 2 ≤ k * r := by nlinarith
        have hpr_le : p * r ≤ m := by rw [hr]; exact Nat.mul_le_mul_right r hp_le_pe
        have hp1r : (p - 1) * r + r = p * r := by
          rw [← Nat.add_one_mul, Nat.sub_add_cancel (by omega)]
        have hkr_le_p1 : k * r ≤ (p - 1) * r := Nat.mul_le_mul_right r (by omega)
        have hkr_lt : k * r - 2 < N := by omega
        refine ⟨⟨k * r - 2, hkr_lt⟩, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have hadd : k * r - 2 + 2 = k * r := by omega
          rw [hadd, Nat.mul_div_cancel k (by omega)]
          exact ⟨dvd_mul_left r k, by omega⟩
        · dsimp
          rw [show k * r - 2 + 2 = k * r by omega, Nat.mul_div_cancel k (by omega)]
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        rw [Nat.div_mul_cancel hj.1]
    rw [hfilt]
    have hfactor : ∑ k ∈ Finset.Icc 1 (p - 1),
        jacobiSym ((I : ℤ) ^ 2 + 3 * (I : ℤ) * ((k * r : ℕ) : ℤ) + 2 * ((k * r : ℕ) : ℤ) ^ 2) m *
        legendreSym p (k : ℤ) =
        jacobiSym ((I : ℤ) ^ 2) r *
        ∑ k ∈ Finset.Icc 1 (p - 1),
          legendreSym p ((I : ℤ) ^ 2 + 3 * (I : ℤ) * ((k * r : ℕ) : ℤ) + 2 * ((k * r : ℕ) : ℤ) ^ 2) *
          legendreSym p (k : ℤ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have hpe0 : p ^ e ≠ 0 := pow_ne_zero e hp.ne_zero
      rw [hr, jacobiSym.mul_right' _ hpe0 hr0, jacobiSym.pow_right, ← jacobiSym.legendreSym.to_jacobiSym,
        legendreSym_pow_odd _ he_odd]
      have hmodr : jacobiSym ((I : ℤ) ^ 2 + 3 * (I : ℤ) * ((k * r : ℕ) : ℤ) + 2 * ((k * r : ℕ) : ℤ) ^ 2) r =
          jacobiSym ((I : ℤ) ^ 2) r := by
        apply jacobiSym.mod_left'
        have hdiv : (r : ℤ) ∣ (((I : ℤ) ^ 2 + 3 * (I : ℤ) * ((k * r : ℕ) : ℤ) + 2 * ((k * r : ℕ) : ℤ) ^ 2) - (I : ℤ) ^ 2) := by
          push_cast
          exact ⟨3 * (I : ℤ) * (k : ℤ) + 2 * (k : ℤ) ^ 2 * (r : ℤ), by ring⟩
        exact Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by simpa [sub_eq_add_neg] using hdiv))
      rw [hmodr]; ring
    rw [hfactor]
    have hinner_zmod : ∑ k ∈ Finset.Icc 1 (p - 1),
        legendreSym p ((I : ℤ) ^ 2 + 3 * (I : ℤ) * ((k * r : ℕ) : ℤ) + 2 * ((k * r : ℕ) : ℤ) ^ 2) *
        legendreSym p (k : ℤ) =
        ∑ y : ZMod p,
          quadraticChar (ZMod p) ((I : ZMod p) ^ 2 + 3 * (I : ZMod p) * ((r : ZMod p) * y) +
            2 * ((r : ZMod p) * y) ^ 2) * quadraticChar (ZMod p) y := by
      have : NeZero p := ⟨hp.ne_zero⟩
      have hdrop : ∑ y : ZMod p,
          quadraticChar (ZMod p) ((I : ZMod p) ^ 2 + 3 * (I : ZMod p) * ((r : ZMod p) * y) +
            2 * ((r : ZMod p) * y) ^ 2) * quadraticChar (ZMod p) y =
          ∑ y ∈ Finset.univ.filter (fun y : ZMod p => y ≠ 0),
          quadraticChar (ZMod p) ((I : ZMod p) ^ 2 + 3 * (I : ZMod p) * ((r : ZMod p) * y) +
            2 * ((r : ZMod p) * y) ^ 2) * quadraticChar (ZMod p) y := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        by_cases hy : y = 0
        · subst hy; simp
        · rw [if_pos hy]
      rw [hdrop]
      refine Finset.sum_bij (fun k _ => (k : ZMod p)) ?_ ?_ ?_ ?_
      · intro k hk
        simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        intro h0
        have hd := (ZMod.natCast_eq_zero_iff k p).mp h0
        have := Nat.le_of_dvd (by omega) hd; omega
      · intro k1 h1 k2 h2 heq
        simp only [Finset.mem_Icc] at h1 h2
        have hv1 : (k1 : ZMod p).val = k1 := ZMod.val_natCast_of_lt (by omega)
        have hv2 : (k2 : ZMod p).val = k2 := ZMod.val_natCast_of_lt (by omega)
        have := congr_arg ZMod.val heq
        omega
      · intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        have hypos : 0 < y.val := Nat.pos_of_ne_zero (fun h0 => hy (by rw [← ZMod.natCast_zmod_val y, h0]; simp))
        have hylt : y.val < p := ZMod.val_lt y
        exact ⟨y.val, Finset.mem_Icc.mpr ⟨hypos, by omega⟩, ZMod.natCast_zmod_val y⟩
      · intro k _
        change quadraticChar (ZMod p) (((I : ℤ) ^ 2 + 3 * (I : ℤ) * ((k * r : ℕ) : ℤ) +
            2 * ((k * r : ℕ) : ℤ) ^ 2 : ℤ) : ZMod p) * quadraticChar (ZMod p) ((k : ℤ) : ZMod p) = _
        push_cast
        congr 2; ring
    rw [hinner_zmod]
    set a : ZMod p := (I : ZMod p)
    set b : ZMod p := (r : ZMod p)
    have hb : b ≠ 0 := by
      intro h0
      exact hnotp_r ((ZMod.natCast_eq_zero_iff r p).mp h0)
    by_cases ha : a = 0
    · rw [ha]
      have hterm : ∀ y : ZMod p,
          quadraticChar (ZMod p) (0 ^ 2 + 3 * 0 * (b * y) + 2 * (b * y) ^ 2) * quadraticChar (ZMod p) y =
          quadraticChar (ZMod p) 2 * quadraticChar (ZMod p) y := by
        intro y
        by_cases hy : y = 0
        · subst hy; simp
        · simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul, zero_add]
          rw [map_mul, map_pow, quadraticChar_sq_one (mul_ne_zero hb hy), mul_one]
      rw [Finset.sum_congr rfl (fun y _ => hterm y), ← Finset.mul_sum,
        sum_quadraticChar_eq_zero (by omega), mul_zero, mul_zero]
    · set c : ZMod p := a * b⁻¹
      have hc : c ≠ 0 := mul_ne_zero ha (inv_ne_zero hb)
      let e1 : ZMod p ≃ ZMod p := Equiv.mulLeft₀ c hc
      have hsub : ∑ y : ZMod p,
          quadraticChar (ZMod p) (a ^ 2 + 3 * a * (b * y) + 2 * (b * y) ^ 2) * quadraticChar (ZMod p) y =
          quadraticChar (ZMod p) c *
            ∑ t : ZMod p, quadraticChar (ZMod p) ((1 + 3 * t + 2 * t ^ 2) * t) := by
        rw [← Fintype.sum_equiv e1 (fun t =>
              quadraticChar (ZMod p) (a ^ 2 + 3 * a * (b * (c * t)) + 2 * (b * (c * t)) ^ 2) *
                quadraticChar (ZMod p) (c * t))
            (fun y => quadraticChar (ZMod p) (a ^ 2 + 3 * a * (b * y) + 2 * (b * y) ^ 2) *
              quadraticChar (ZMod p) y) (fun _ => rfl), Finset.mul_sum]
        refine Finset.sum_congr rfl (fun t _ => ?_)
        have hbc : b * (c * t) = a * t := by
          dsimp [c]; field_simp [hb]
        rw [hbc]
        have hfac : a ^ 2 + 3 * a * (a * t) + 2 * (a * t) ^ 2 = a ^ 2 * (1 + 3 * t + 2 * t ^ 2) := by ring
        rw [hfac, map_mul (quadraticChar (ZMod p)) (a ^ 2), map_pow, quadraticChar_sq_one ha, one_mul,
          map_mul (quadraticChar (ZMod p)) c, map_mul (quadraticChar (ZMod p)) (1 + 3 * t + 2 * t ^ 2)]
        ring
      rw [hsub, sum_cubic_32_eq_zero hp4, mul_zero, mul_zero]
  have hdet_q : ((sunJacobiMatrix (2 * n)).map (Int.castRingHom ℚ)).det ≠ 0 := by
    have hmap : ((sunJacobiMatrix (2 * n)).map (Int.castRingHom ℚ)).det =
        ((sunJacobiMatrix (2 * n)).det : ℚ) := by
      simpa using (RingHom.map_det (Int.castRingHom ℚ) (sunJacobiMatrix (2 * n))).symm
    rw [hmap]
    exact_mod_cast hdet
  have hmul_q : ((sunJacobiMatrix (2 * n)).map (Int.castRingHom ℚ)).mulVec (fun j => (v j : ℚ)) = 0 := by
    ext i
    have hi := congr_fun hmul i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Int.coe_castRingHom, Pi.zero_apply] at hi ⊢
    exact_mod_cast hi
  have hv_q : (fun j => (v j : ℚ)) = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero hdet_q hmul_q
  apply hv_ne
  ext j
  have hj := congr_fun hv_q j
  simp only [Pi.zero_apply] at hj ⊢
  exact_mod_cast hj

end OMA.P_oeis_a372314

theorem OMA.solution : type_of% @OMA.S_oeis_a372314.main :=
  OMA.P_oeis_a372314.prove_a372314

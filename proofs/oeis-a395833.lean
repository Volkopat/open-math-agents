import OMAStatements.S_oeis_a395833
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a395833

open OMA.S_oeis_a395833

private noncomputable def dPS (f : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.derivative ℤ f

private lemma coeff_dPS (m : ℕ) (f : PowerSeries ℤ) :
    PowerSeries.coeff m (dPS f) = PowerSeries.coeff (m + 1) f * ((m + 1 : ℕ) : ℤ) := by
  simpa [dPS] using PowerSeries.coeff_derivative f m

private lemma dPS_pow (f : PowerSeries ℤ) (e : ℕ) :
    dPS (f ^ e) = (e : PowerSeries ℤ) * f ^ (e - 1) * dPS f := by
  induction e with
  | zero =>
    simp [dPS]
  | succ e ih =>
    rw [pow_succ, show dPS (f ^ e * f) = dPS (f ^ e) * f + f ^ e * dPS f from by
      simp [dPS, Derivation.leibniz, smul_eq_mul, mul_comm, add_comm]]
    cases e with
    | zero =>
      simp [dPS]
    | succ e' =>
      rw [ih]
      simp only [Nat.add_sub_cancel]
      push_cast
      rw [pow_succ]
      ring

/-- For any formal power series `B ∈ ℤ⟦X⟧`, any exponent `e ≥ 1`, and any `m ≥ 1`,
`e ∣ m * coeff m (B ^ e)`. -/
private lemma dvd_mul_coeff_pow (B : PowerSeries ℤ) {e m : ℕ} (_he : 1 ≤ e) (hm : 1 ≤ m) :
    (e : ℤ) ∣ (m : ℤ) * PowerSeries.coeff m (B ^ e) := by
  have hd := congrArg (PowerSeries.coeff (m - 1)) (dPS_pow B e)
  rw [coeff_dPS, show m - 1 + 1 = m by omega] at hd
  have heC : (e : PowerSeries ℤ) = PowerSeries.C (e : ℤ) := by
    simp
  rw [heC, mul_assoc, PowerSeries.coeff_C_mul] at hd
  refine ⟨PowerSeries.coeff (m - 1) (B ^ (e - 1) * dPS B), ?_⟩
  linarith

/-- Key divisibility lemma: if `2*k - 1 ∣ a` and `2*n - 1 ∣ (n - k) * C` with `1 ≤ k < n`,
then `2*n - 1 ∣ a * C`. -/
private lemma dvd_mul_of_odd_sub {n k : ℕ} {a C : ℤ} (hk : 1 ≤ k) (hkn : k < n)
    (ha : ((2 * k - 1 : ℕ) : ℤ) ∣ a)
    (hC : ((2 * n - 1 : ℕ) : ℤ) ∣ ((n - k : ℕ) : ℤ) * C) :
    ((2 * n - 1 : ℕ) : ℤ) ∣ a * C := by
  set M := 2 * n - 1
  set m := n - k
  have hm_pos : 0 < m := by omega
  set d := Nat.gcd M m
  have hd_pos : 0 < d := Nat.gcd_pos_of_pos_right M hm_pos
  have hdM : d ∣ M := Nat.gcd_dvd_left M m
  have hdm : d ∣ m := Nat.gcd_dvd_right M m
  set M' := M / d
  set m' := m / d
  have hM_eq : M = d * M' := (Nat.mul_div_cancel' hdM).symm
  have hm_eq : m = d * m' := (Nat.mul_div_cancel' hdm).symm
  have hcop : Nat.Coprime M' m' := Nat.coprime_div_gcd_div_gcd hd_pos
  -- Since 2*k - 1 = M - 2*m, we have d ∣ 2*k - 1, hence d ∣ a!
  have hd_dvd_2k1 : d ∣ 2 * k - 1 := by
    have h2m : 2 * k - 1 = M - 2 * m := by omega
    rw [h2m]
    exact Nat.dvd_sub hdM (dvd_mul_of_dvd_right hdm 2)
  have hd_dvd_a : (d : ℤ) ∣ a := dvd_trans (Int.ofNat_dvd.mpr hd_dvd_2k1) ha
  have hM'_dvd_m'C : (M' : ℤ) ∣ (m' : ℤ) * C := by
    obtain ⟨q, hq⟩ := hC
    rw [hM_eq, hm_eq] at hq
    push_cast at hq
    have hd_ne : (d : ℤ) ≠ 0 := by positivity
    have hmul : (d : ℤ) * ((m' : ℤ) * C) = (d : ℤ) * ((M' : ℤ) * q) := by linarith
    exact ⟨q, mul_left_cancel₀ hd_ne hmul⟩
  have hcop_int : IsCoprime (M' : ℤ) (m' : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  have hM'_dvd_C : (M' : ℤ) ∣ C := hcop_int.dvd_of_dvd_mul_left hM'_dvd_m'C
  rw [hM_eq]
  push_cast
  exact mul_dvd_mul hd_dvd_a hM'_dvd_C

/-- Formal inverse of `(1 + X)` raised to `(d + 1)` over `ZMod 3`. -/
private def invOneAddPow3 (d : ℕ) : PowerSeries (ZMod 3) :=
  PowerSeries.mk fun r => (-1 : ZMod 3) ^ r * ((Nat.choose (d + r) r : ℕ) : ZMod 3)

private lemma one_add_X_mul_invOneAddPow3_zero :
    (1 + (PowerSeries.X : PowerSeries (ZMod 3))) * invOneAddPow3 0 = 1 := by
  ext n
  rw [add_mul, one_mul, map_add]
  cases n with
  | zero =>
    simp [invOneAddPow3, PowerSeries.coeff_zero_eq_constantCoeff]
  | succ n =>
    rw [← pow_one (PowerSeries.X : PowerSeries (ZMod 3)), PowerSeries.coeff_X_pow_mul',
      if_pos (by omega), Nat.add_sub_cancel]
    simp only [invOneAddPow3, PowerSeries.coeff_mk, PowerSeries.coeff_one,
      show n + 1 ≠ 0 by omega, ↓reduceIte, zero_add, Nat.choose_self, Nat.cast_one, mul_one,
      pow_succ]
    ring

private lemma one_add_X_mul_invOneAddPow3_succ (d : ℕ) :
    (1 + (PowerSeries.X : PowerSeries (ZMod 3))) * invOneAddPow3 (d + 1) = invOneAddPow3 d := by
  ext n
  rw [add_mul, one_mul, map_add]
  cases n with
  | zero =>
    simp [invOneAddPow3, PowerSeries.coeff_zero_eq_constantCoeff]
  | succ n =>
    rw [← pow_one (PowerSeries.X : PowerSeries (ZMod 3)), PowerSeries.coeff_X_pow_mul',
      if_pos (by omega), Nat.add_sub_cancel]
    simp only [invOneAddPow3, PowerSeries.coeff_mk]
    have hch : Nat.choose (d + 1 + (n + 1)) (n + 1) =
        Nat.choose (d + (n + 1)) (n + 1) + Nat.choose (d + 1 + n) n := by
      rw [show d + 1 + (n + 1) = (d + 1 + n) + 1 by omega, Nat.choose_succ_succ,
        show d + 1 + n = d + (n + 1) by omega]
      ring
    rw [hch]
    push_cast
    rw [pow_succ]
    ring

private lemma one_add_X_pow_mul_invOneAddPow3 (d : ℕ) :
    (1 + (PowerSeries.X : PowerSeries (ZMod 3))) ^ (d + 1) * invOneAddPow3 d = 1 := by
  induction d with
  | zero => simpa using one_add_X_mul_invOneAddPow3_zero
  | succ d ih =>
    calc (1 + PowerSeries.X) ^ (d + 1 + 1) * invOneAddPow3 (d + 1)
        = (1 + PowerSeries.X) ^ (d + 1) * ((1 + PowerSeries.X) * invOneAddPow3 (d + 1)) := by ring
      _ = (1 + PowerSeries.X) ^ (d + 1) * invOneAddPow3 d := by rw [one_add_X_mul_invOneAddPow3_succ]
      _ = 1 := ih

private lemma three_dvd_choose_three_mul (m : ℕ) (hm : 1 ≤ m) :
    3 ∣ Nat.choose (3 * m) m := by
  have h := Nat.add_one_mul_choose_eq (3 * m - 1) (m - 1)
  rw [show 3 * m - 1 + 1 = 3 * m by omega, show m - 1 + 1 = m by omega] at h
  have hmul : m * Nat.choose (3 * m) m = m * (3 * Nat.choose (3 * m - 1) (m - 1)) := by linarith
  have heq := Nat.eq_of_mul_eq_mul_left (by omega : 0 < m) hmul
  exact ⟨Nat.choose (3 * m - 1) (m - 1), heq⟩

private lemma part1 : ∀ n : ℕ, 1 ≤ n → ((2 * n - 1 : ℕ) : ℤ) ∣ A395833 n := by
  intro n hn
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => omega
    | succ m =>
      cases m with
      | zero => simp [A395833]
      | succ r =>
        conv_rhs => unfold A395833
        rw [dvd_neg]
        refine Finset.dvd_sum fun k _ => ?_
        have hk_ge : 1 ≤ k.1 + 1 := by omega
        have hk_lt : k.1 + 1 < r + 2 := by omega
        have hih := ih (k.1 + 1) hk_lt hk_ge
        set Atrunc : PowerSeries ℤ :=
          PowerSeries.mk fun j => if _ : j < r + 2 then A395833 j else 0
        set B : PowerSeries ℤ := Ring.inverse Atrunc
        have hC0 := dvd_mul_coeff_pow B (e := (2 * (r + 2) - 1) * (k.1 + 1)) (m := r + 1 - k.1)
          (Nat.mul_pos (by omega) (by omega)) (by omega)
        have hC : ((2 * (r + 2) - 1 : ℕ) : ℤ) ∣
            ((r + 2 - (k.1 + 1) : ℕ) : ℤ) * PowerSeries.coeff (r + 1 - k.1) (B ^ ((2 * (r + 2) - 1) * (k.1 + 1))) := by
          have hdvd : ((2 * (r + 2) - 1 : ℕ) : ℤ) ∣ (((2 * (r + 2) - 1) * (k.1 + 1) : ℕ) : ℤ) := by
            push_cast; exact dvd_mul_right _ _
          have hsub : r + 2 - (k.1 + 1) = r + 1 - k.1 := by omega
          rw [hsub]
          exact dvd_trans hdvd hC0
        exact dvd_mul_of_odd_sub hk_ge hk_lt hih hC

private lemma part2 : ∀ n : ℕ, 2 ≤ n → (3 : ℤ) ∣ A395833 n := by
  intro n hn
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ r =>
        conv_rhs => unfold A395833
        rw [dvd_neg]
        set Atrunc : PowerSeries ℤ :=
          PowerSeries.mk fun j => if _ : j < r + 2 then A395833 j else 0
        set B : PowerSeries ℤ := Ring.inverse Atrunc
        -- Work in ZMod 3 via Int.castRingHom (ZMod 3)
        change ((3 : ℕ) : ℤ) ∣ _
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        -- Split off k = 0 (representing k.1 + 1 = 1); all k.1 ≥ 1 have 3 ∣ A395833 (k.1 + 1)!
        rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin (r + 1))]
        · -- k = 0: A395833 1 = 1, need coeff (r + 1) (B^(2*(r+2)-1)) ≡ 0 (mod 3)!
          simp only [Nat.zero_add, Nat.sub_zero, mul_one, A395833, Int.cast_one, one_mul]
          let φ := PowerSeries.map (Int.castRingHom (ZMod 3))
          have hA_mod3 : φ Atrunc = 1 + (PowerSeries.X : PowerSeries (ZMod 3)) := by
            ext j
            rw [PowerSeries.coeff_map, map_add, PowerSeries.coeff_one, PowerSeries.coeff_X]
            simp only [Atrunc, PowerSeries.coeff_mk]
            cases j with
            | zero => simp [A395833]
            | succ j' =>
              cases j' with
              | zero => simp [A395833]
              | succ j'' =>
                simp only [show j'' + 1 + 1 ≠ 0 by omega, show j'' + 1 + 1 ≠ 1 by omega,
                  ↓reduceIte, add_zero]
                split_ifs with hlt
                · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr (ih (j'' + 2) hlt (by omega))
                · simp
          have hA_unit : IsUnit Atrunc := by
            apply PowerSeries.isUnit_iff_constantCoeff.mpr
            rw [← PowerSeries.coeff_zero_eq_constantCoeff]
            simp [Atrunc, A395833]
          have hAB : Atrunc * B = 1 := Ring.mul_inverse_cancel Atrunc hA_unit
          have hφB_mul : (1 + (PowerSeries.X : PowerSeries (ZMod 3))) * φ B = 1 := by
            have h := congrArg φ hAB
            rw [map_mul, map_one, hA_mod3] at h
            exact h
          have hφB_pow : φ (B ^ (2 * (r + 2) - 1)) = invOneAddPow3 (2 * (r + 2) - 2) := by
            have hd : 2 * (r + 2) - 2 + 1 = 2 * (r + 2) - 1 := by omega
            have h1 : (1 + (PowerSeries.X : PowerSeries (ZMod 3))) ^ (2 * (r + 2) - 1) *
                φ (B ^ (2 * (r + 2) - 1)) = 1 := by
              rw [map_pow, ← mul_pow, hφB_mul, one_pow]
            have h2 := one_add_X_pow_mul_invOneAddPow3 (2 * (r + 2) - 2)
            rw [hd] at h2
            calc φ (B ^ (2 * (r + 2) - 1))
                = 1 * φ (B ^ (2 * (r + 2) - 1)) := (one_mul _).symm
              _ = (invOneAddPow3 (2 * (r + 2) - 2) * (1 + PowerSeries.X) ^ (2 * (r + 2) - 1)) *
                    φ (B ^ (2 * (r + 2) - 1)) := by rw [mul_comm (invOneAddPow3 _), h2]
              _ = invOneAddPow3 (2 * (r + 2) - 2) *
                    ((1 + PowerSeries.X) ^ (2 * (r + 2) - 1) * φ (B ^ (2 * (r + 2) - 1))) := by ring
              _ = invOneAddPow3 (2 * (r + 2) - 2) := by rw [h1, mul_one]
          have hc := congrArg (PowerSeries.coeff (r + 1)) hφB_pow
          rw [PowerSeries.coeff_map] at hc
          change (Int.castRingHom (ZMod 3)) (PowerSeries.coeff (r + 1) (B ^ (2 * (r + 2) - 1))) = 0
          rw [hc]
          simp only [invOneAddPow3, PowerSeries.coeff_mk,
            show 2 * (r + 2) - 2 + (r + 1) = 3 * (r + 1) by omega]
          have h3 : ((Nat.choose (3 * (r + 1)) (r + 1) : ℕ) : ZMod 3) = 0 :=
            (ZMod.natCast_eq_zero_iff _ 3).mpr (three_dvd_choose_three_mul (r + 1) (by omega))
          rw [h3, mul_zero]
        · intro k _ hk0
          have hk_ge : 2 ≤ k.1 + 1 := by
            have : k.1 ≠ 0 := fun h => hk0 (Fin.ext h)
            omega
          have h3 : ((A395833 (k.1 + 1) : ℤ) : ZMod 3) = 0 :=
            (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr (ih (k.1 + 1) (by omega) hk_ge)
          rw [h3, zero_mul]
        · intro h; exact absurd (Finset.mem_univ _) h

private theorem prove_main : type_of% @OMA.S_oeis_a395833.main :=
  ⟨part1, part2⟩

end OMA.P_oeis_a395833

theorem OMA.solution : type_of% @OMA.S_oeis_a395833.main :=
  OMA.P_oeis_a395833.prove_main

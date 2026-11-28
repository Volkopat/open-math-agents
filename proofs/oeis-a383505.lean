import OMAStatements.S_oeis_a383505
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a383505

open OMA.S_oeis_a383505

private lemma isUnit_natCast_zmod_sq {p j : ℕ} (hp : p.Prime) (hnd : ¬ p ∣ j) :
    IsUnit (j : ZMod (p ^ 2)) := by
  rw [ZMod.isUnit_iff_coprime]
  exact ((hp.coprime_iff_not_dvd.mpr hnd).symm.pow_right 2)

private lemma mul_inv_cancel_zmod_sq {p j : ℕ} (hp : p.Prime) (hnd : ¬ p ∣ j) :
    (j : ZMod (p ^ 2)) * (j : ZMod (p ^ 2))⁻¹ = 1 :=
  ZMod.mul_inv_of_unit _ (isUnit_natCast_zmod_sq hp hnd)

private lemma inv_mul_cancel_zmod_sq {p j : ℕ} (hp : p.Prime) (hnd : ¬ p ∣ j) :
    (j : ZMod (p ^ 2))⁻¹ * (j : ZMod (p ^ 2)) = 1 := by
  rw [mul_comm]; exact mul_inv_cancel_zmod_sq hp hnd

private lemma factorial_eq_prod_Ico (k : ℕ) : k.factorial = ∏ j ∈ Finset.Ico 1 (k + 1), j := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.factorial_succ, Finset.prod_Ico_succ_top (by omega), ih, mul_comm]

private lemma descFactorial_sub_eq_prod {m k : ℕ} (hk : k ≤ m) :
    (m - 1).descFactorial k = ∏ j ∈ Finset.Ico 1 (k + 1), (m - j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ, Finset.prod_Ico_succ_top (by omega), ih (by omega), mul_comm]
    congr 1; omega

private lemma lower_bound {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : k < p ^ 2 - 1) :
    ¬ (Nat.choose (k * p ^ 2) (k + 1) ≡ p ^ 2 - 1 [MOD p ^ 2]) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hq4 : 4 ≤ p ^ 2 := by nlinarith
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simp only [zero_mul, Nat.choose_zero_succ, Nat.ModEq, Nat.zero_mod]
    have hlt : p ^ 2 - 1 < p ^ 2 := by omega
    rw [Nat.mod_eq_of_lt hlt]
    omega
  · intro hcong
    have hmul : (k + 1) * Nat.choose (k * p ^ 2) (k + 1) =
        k * p ^ 2 * Nat.choose (k * p ^ 2 - 1) k := by
      have h1 := Nat.add_one_mul_choose_eq (k * p ^ 2 - 1) k
      have hkp : 1 ≤ k * p ^ 2 := by nlinarith
      rw [Nat.sub_add_cancel hkp] at h1
      linarith
    have hp2_dvd : p ^ 2 ∣ (k + 1) * Nat.choose (k * p ^ 2) (k + 1) := by
      rw [hmul]
      exact ⟨k * Nat.choose (k * p ^ 2 - 1) k, by ring⟩
    have hp_dvd_c : p ∣ Nat.choose (k * p ^ 2) (k + 1) := by
      by_contra hnd
      have hcop : Nat.Coprime (p ^ 2) (Nat.choose (k * p ^ 2) (k + 1)) :=
        (hp.coprime_iff_not_dvd.mpr hnd).pow_left 2
      have hdvd_k1 : p ^ 2 ∣ (k + 1) := hcop.dvd_of_dvd_mul_right hp2_dvd
      have := Nat.le_of_dvd (by omega) hdvd_k1
      omega
    have hmodp : Nat.choose (k * p ^ 2) (k + 1) ≡ p ^ 2 - 1 [MOD p] :=
      hcong.of_dvd (dvd_pow_self p (by decide : 2 ≠ 0))
    have h0 : Nat.choose (k * p ^ 2) (k + 1) % p = 0 := Nat.mod_eq_zero_of_dvd hp_dvd_c
    rw [Nat.ModEq, h0] at hmodp
    have hp_dvd_m1 : p ∣ p ^ 2 - 1 := Nat.dvd_of_mod_eq_zero hmodp.symm
    have h1 : p ∣ 1 := by
      have hsub := Nat.dvd_sub (dvd_pow_self p (by decide : 2 ≠ 0)) hp_dvd_m1
      rwa [Nat.sub_sub_self (by omega : 1 ≤ p ^ 2)] at hsub
    have := Nat.le_of_dvd (by decide) h1
    omega

private lemma upper_bound_odd {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    Nat.choose ((p ^ 2 - 1) * p ^ 2) (p ^ 2) ≡ p ^ 2 - 1 [MOD p ^ 2] := by
  set q := p ^ 2
  have hq9 : 9 ≤ q := by dsimp [q]; nlinarith
  have hrel : Nat.choose ((q - 1) * q) q = (q - 1) * Nat.choose ((q - 1) * q - 1) (q - 1) := by
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < q)
    have h1 := Nat.add_one_mul_choose_eq ((q - 1) * q - 1) (q - 1)
    have hpos : 1 ≤ (q - 1) * q := Nat.mul_pos (by omega) (by omega)
    rw [Nat.sub_add_cancel hpos, Nat.sub_add_cancel (by omega : 1 ≤ q)] at h1
    linarith
  rw [hrel, ← ZMod.natCast_eq_natCast_iff, Nat.cast_mul]
  suffices hC : (Nat.choose ((q - 1) * q - 1) (q - 1) : ZMod q) = 1 by
    rw [hC, mul_one]
  -- Use `(q - 1)! * C((q - 1) * q - 1, q - 1) = ∏_{j=1}^{q-1} ((q - 1) * q - j)`.
  have hnat : (q - 1).factorial * Nat.choose ((q - 1) * q - 1) (q - 1) =
      ∏ j ∈ Finset.Ico 1 q, ((q - 1) * q - j) := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose,
      descFactorial_sub_eq_prod (by nlinarith : q - 1 ≤ (q - 1) * q),
      show q - 1 + 1 = q by omega]
  set M := (Finset.Ico 1 q).filter (fun j => p ∣ j)
  set U := (Finset.Ico 1 q).filter (fun j => ¬ p ∣ j)
  have hM_bij : ∀ f : ℕ → ℕ, ∏ j ∈ M, f j = ∏ a ∈ Finset.Ico 1 p, f (a * p) := by
    intro f
    refine Finset.prod_bij (fun j _ => j / p) ?_ ?_ ?_ ?_
    · intro j hj
      obtain ⟨hj1, hjd⟩ := Finset.mem_filter.mp hj
      obtain ⟨hjlo, hjhi⟩ := Finset.mem_Ico.mp hj1
      obtain ⟨a, rfl⟩ := hjd
      rw [Nat.mul_div_cancel_left a hp.pos, Finset.mem_Ico]
      exact ⟨Nat.pos_of_ne_zero (fun h0 => by rw [h0, mul_zero] at hjlo; omega),
             by nlinarith [show q = p * p by dsimp [q]; rw [pow_two]]⟩
    · intro j₁ hj₁ j₂ hj₂ hdiv
      obtain ⟨a₁, rfl⟩ := (Finset.mem_filter.mp hj₁).2
      obtain ⟨a₂, rfl⟩ := (Finset.mem_filter.mp hj₂).2
      rw [Nat.mul_div_cancel_left a₁ hp.pos, Nat.mul_div_cancel_left a₂ hp.pos] at hdiv
      rw [hdiv]
    · intro a ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_Ico.mp ha
      refine ⟨a * p, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by nlinarith [hp.pos],
        by nlinarith [show q = p * p by dsimp [q]; rw [pow_two]]⟩, dvd_mul_left p a⟩,
        Nat.mul_div_cancel a hp.pos⟩
    · intro j hj
      obtain ⟨a, rfl⟩ := (Finset.mem_filter.mp hj).2
      rw [Nat.mul_div_cancel_left a hp.pos, mul_comm]
  have hfac : (q - 1).factorial = p ^ (p - 1) * (∏ a ∈ Finset.Ico 1 p, a) * (∏ j ∈ U, j) := by
    rw [factorial_eq_prod_Ico, show q - 1 + 1 = q by omega,
      ← Finset.prod_filter_mul_prod_filter_not (Finset.Ico 1 q) (fun j => p ∣ j) (fun j => j),
      hM_bij (fun j => j), Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico]
    ring
  have hnum : ∏ j ∈ Finset.Ico 1 q, ((q - 1) * q - j) =
      p ^ (p - 1) * (∏ a ∈ Finset.Ico 1 p, ((q - 1) * p - a)) * (∏ j ∈ U, ((q - 1) * q - j)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not (Finset.Ico 1 q) (fun j => p ∣ j) (fun j => (q - 1) * q - j),
      hM_bij (fun j => (q - 1) * q - j)]
    have hM_eq : ∏ a ∈ Finset.Ico 1 p, ((q - 1) * q - a * p) =
        p ^ (p - 1) * ∏ a ∈ Finset.Ico 1 p, ((q - 1) * p - a) := by
      rw [show p ^ (p - 1) = ∏ _a ∈ Finset.Ico 1 p, p by simp, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun a _ => ?_)
      rw [show q = p * p by dsimp [q]; rw [pow_two], show (p * p - 1) * (p * p) = p * ((p * p - 1) * p) by ring,
        mul_comm a p, ← Nat.mul_sub_left_distrib]
    rw [hM_eq]
  have hclean : (∏ a ∈ Finset.Ico 1 p, a) * (∏ j ∈ U, j) * Nat.choose ((q - 1) * q - 1) (q - 1) =
      (∏ a ∈ Finset.Ico 1 p, ((q - 1) * p - a)) * (∏ j ∈ U, ((q - 1) * q - j)) := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos (p - 1))
    calc p ^ (p - 1) * ((∏ a ∈ Finset.Ico 1 p, a) * (∏ j ∈ U, j) * Nat.choose ((q - 1) * q - 1) (q - 1))
        = (q - 1).factorial * Nat.choose ((q - 1) * q - 1) (q - 1) := by rw [hfac]; ring
      _ = ∏ j ∈ Finset.Ico 1 q, ((q - 1) * q - j) := hnat
      _ = p ^ (p - 1) * ((∏ a ∈ Finset.Ico 1 p, ((q - 1) * p - a)) * (∏ j ∈ U, ((q - 1) * q - j))) := by
          rw [hnum]; ring
  have hcast := congr_arg (Nat.cast (R := ZMod q)) hclean
  simp only [Nat.cast_mul, Nat.cast_prod] at hcast
  have hnd_a : ∀ a ∈ Finset.Ico 1 p, ¬ p ∣ a := fun a ha hd =>
    absurd (Nat.le_of_dvd (Finset.mem_Ico.mp ha).1 hd) (by have := (Finset.mem_Ico.mp ha).2; omega)
  have huA : (∏ a ∈ Finset.Ico 1 p, (a : ZMod q)⁻¹) * (∏ a ∈ Finset.Ico 1 p, (a : ZMod q)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one (fun a ha => inv_mul_cancel_zmod_sq hp (hnd_a a ha))
  have huU : (∏ j ∈ U, (j : ZMod q)⁻¹) * (∏ j ∈ U, (j : ZMod q)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one (fun j hj => inv_mul_cancel_zmod_sq hp (Finset.mem_filter.mp hj).2)
  have hC_eq : (Nat.choose ((q - 1) * q - 1) (q - 1) : ZMod q) =
      ((∏ a ∈ Finset.Ico 1 p, (a : ZMod q)⁻¹) * ∏ a ∈ Finset.Ico 1 p, (((q - 1) * p - a : ℕ) : ZMod q)) *
      ((∏ j ∈ U, (j : ZMod q)⁻¹) * ∏ j ∈ U, (((q - 1) * q - j : ℕ) : ZMod q)) := by
    have hm := congr_arg (((∏ a ∈ Finset.Ico 1 p, (a : ZMod q)⁻¹) * (∏ j ∈ U, (j : ZMod q)⁻¹)) * ·) hcast
    have hL : ((∏ a ∈ Finset.Ico 1 p, (a : ZMod q)⁻¹) * (∏ j ∈ U, (j : ZMod q)⁻¹)) *
        ((∏ a ∈ Finset.Ico 1 p, (a : ZMod q)) * (∏ j ∈ U, (j : ZMod q)) *
          (Nat.choose ((q - 1) * q - 1) (q - 1) : ZMod q)) =
        (Nat.choose ((q - 1) * q - 1) (q - 1) : ZMod q) := by
      calc _ = ((∏ a ∈ Finset.Ico 1 p, (a : ZMod q)⁻¹) * (∏ a ∈ Finset.Ico 1 p, (a : ZMod q))) *
               ((∏ j ∈ U, (j : ZMod q)⁻¹) * (∏ j ∈ U, (j : ZMod q))) *
               (Nat.choose ((q - 1) * q - 1) (q - 1) : ZMod q) := by ring
        _ = _ := by rw [huA, huU, one_mul, one_mul]
    rw [hL] at hm
    rw [hm]; ring
  rw [hC_eq]
  -- Evaluate the `U` factor = `(-1)^|U| = 1`.
  have hU_card_even : Even U.card := by
    have hsum : M.card + U.card = (Finset.Ico 1 q).card :=
      Finset.card_filter_add_card_filter_not (fun j => p ∣ j)
    have hM_card : M.card = p - 1 := by
      have hbij : M.card = (Finset.Ico 1 p).card := by
        refine Finset.card_bij (fun j _ => j / p) ?_ ?_ ?_
        · intro j hj
          obtain ⟨hj1, hjd⟩ := Finset.mem_filter.mp hj
          obtain ⟨hjlo, hjhi⟩ := Finset.mem_Ico.mp hj1
          obtain ⟨a, rfl⟩ := hjd
          rw [Nat.mul_div_cancel_left a hp.pos, Finset.mem_Ico]
          exact ⟨Nat.pos_of_ne_zero (fun h0 => by rw [h0, mul_zero] at hjlo; omega),
                 by nlinarith [show q = p * p by dsimp [q]; rw [pow_two]]⟩
        · intro j₁ hj₁ j₂ hj₂ hdiv
          obtain ⟨a₁, rfl⟩ := (Finset.mem_filter.mp hj₁).2
          obtain ⟨a₂, rfl⟩ := (Finset.mem_filter.mp hj₂).2
          rw [Nat.mul_div_cancel_left a₁ hp.pos, Nat.mul_div_cancel_left a₂ hp.pos] at hdiv
          rw [hdiv]
        · intro a ha
          obtain ⟨ha1, ha2⟩ := Finset.mem_Ico.mp ha
          exact ⟨a * p, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by nlinarith [hp.pos],
            by nlinarith [show q = p * p by dsimp [q]; rw [pow_two]]⟩, dvd_mul_left p a⟩,
            Nat.mul_div_cancel a hp.pos⟩
      rw [hbij, Nat.card_Ico]
    rw [Nat.card_Ico, hM_card] at hsum
    obtain ⟨t, ht⟩ := hp.odd_of_ne_two (by omega)
    refine ⟨p * t, ?_⟩
    have hqeq : q = p * p := by dsimp [q]; rw [pow_two]
    have h1 : q - p = 2 * (p * t) := by
      have : p * p = p + 2 * (p * t) := by
        calc p * p = p * (2 * t + 1) := by nth_rw 2 [ht]
          _ = p + 2 * (p * t) := by ring
      omega
    omega
  have hU_val : (∏ j ∈ U, (j : ZMod q)⁻¹) * (∏ j ∈ U, (((q - 1) * q - j : ℕ) : ZMod q)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    have h1 : ∏ j ∈ U, ((j : ZMod q)⁻¹ * (((q - 1) * q - j : ℕ) : ZMod q)) =
        ∏ _j ∈ U, (-1 : ZMod q) := by
      refine Finset.prod_congr rfl (fun j hj => ?_)
      have hj2 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1).2
      have huj := inv_mul_cancel_zmod_sq hp (Finset.mem_filter.mp hj).2
      have hjle : j ≤ (q - 1) * q := by
        have := Nat.le_mul_of_pos_left q (by omega : 0 < q - 1); omega
      rw [Nat.cast_sub hjle, Nat.cast_mul, ZMod.natCast_self,
        mul_zero, zero_sub, mul_neg, huj]
    rw [h1, Finset.prod_const]
    obtain ⟨t, ht⟩ := hU_card_even
    rw [ht, ← two_mul, pow_mul, neg_one_sq, one_pow]
  -- Evaluate the `A` factor = `(-1)^(p - 1) * ∏ (1 + p * a⁻¹) = 1`.
  have hp2_z : (p : ZMod q) ^ 2 = 0 := by dsimp [q]; rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  have hA_val : (∏ a ∈ Finset.Ico 1 p, (a : ZMod q)⁻¹) *
      (∏ a ∈ Finset.Ico 1 p, (((q - 1) * p - a : ℕ) : ZMod q)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    have h1 : ∏ a ∈ Finset.Ico 1 p, ((a : ZMod q)⁻¹ * (((q - 1) * p - a : ℕ) : ZMod q)) =
        ∏ a ∈ Finset.Ico 1 p, (-(1 + (p : ZMod q) * (a : ZMod q)⁻¹)) := by
      refine Finset.prod_congr rfl (fun a ha => ?_)
      have ha2 := (Finset.mem_Ico.mp ha).2
      have hua := inv_mul_cancel_zmod_sq hp (hnd_a a ha)
      have hale : a ≤ (q - 1) * p := by
        have := Nat.le_mul_of_pos_left p (by omega : 0 < q - 1); omega
      rw [Nat.cast_sub hale, Nat.cast_mul,
        Nat.cast_sub (by omega : 1 ≤ q), ZMod.natCast_self, Nat.cast_one, zero_sub]
      linear_combination -hua
    rw [h1]
    have hneg : ∏ a ∈ Finset.Ico 1 p, (-(1 + (p : ZMod q) * (a : ZMod q)⁻¹)) =
        (-1 : ZMod q) ^ (p - 1) * ∏ a ∈ Finset.Ico 1 p, (1 + (p : ZMod q) * (a : ZMod q)⁻¹) := by
      rw [show (-1 : ZMod q) ^ (p - 1) = ∏ _a ∈ Finset.Ico 1 p, (-1 : ZMod q) by simp,
        ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun _ _ => by ring)
    have hpm1_even : (-1 : ZMod q) ^ (p - 1) = 1 := by
      obtain ⟨t, ht⟩ := hp.odd_of_ne_two (by omega)
      rw [show p - 1 = 2 * t by omega, pow_mul, neg_one_sq, one_pow]
    rw [hneg, hpm1_even, one_mul]
    have hexp : ∀ s : Finset ℕ,
        ∏ a ∈ s, (1 + (p : ZMod q) * (a : ZMod q)⁻¹) =
        1 + (p : ZMod q) * ∑ a ∈ s, (a : ZMod q)⁻¹ := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert x s hx ih =>
        rw [Finset.prod_insert hx, Finset.sum_insert hx, ih]
        linear_combination ((x : ZMod q)⁻¹ * ∑ a ∈ s, (a : ZMod q)⁻¹) * hp2_z
    rw [hexp]
    -- Show `p * ∑_{a=1}^{p-1} a⁻¹ = 0` in `ZMod (p ^ 2)` by pairing `a` with `p - a`!
    have hsum0 : (p : ZMod q) * ∑ a ∈ Finset.Ico 1 p, (a : ZMod q)⁻¹ = 0 := by
      have hrefl : ∑ a ∈ Finset.Ico 1 p, ((p - a : ℕ) : ZMod q)⁻¹ =
          ∑ a ∈ Finset.Ico 1 p, (a : ZMod q)⁻¹ := by
        refine Finset.sum_bij (fun a _ => p - a) ?_ ?_ ?_ ?_
        · intro a ha; rw [Finset.mem_Ico] at ha ⊢; omega
        · intro a ha b hb hab; rw [Finset.mem_Ico] at ha hb; omega
        · intro b hb; rw [Finset.mem_Ico] at hb; exact ⟨p - b, Finset.mem_Ico.mpr (by omega), by omega⟩
        · intro _ _; rfl
      have hpair : ∀ a ∈ Finset.Ico 1 p,
          (p : ZMod q) * ((a : ZMod q)⁻¹ + ((p - a : ℕ) : ZMod q)⁻¹) = 0 := by
        intro a ha
        have ha1 := (Finset.mem_Ico.mp ha).1; have ha2 := (Finset.mem_Ico.mp ha).2
        have hnd' : ¬ p ∣ (p - a) := fun hd => absurd (Nat.le_of_dvd (by omega) hd) (by omega)
        have hu := mul_inv_cancel_zmod_sq hp (hnd_a a ha)
        have hu' := mul_inv_cancel_zmod_sq hp hnd'
        have hsub : ((p - a : ℕ) : ZMod q) = (p : ZMod q) - (a : ZMod q) := by
          rw [Nat.cast_sub ha2.le]
        have hmul : ((p - a : ℕ) : ZMod q) * ((p : ZMod q) * ((a : ZMod q)⁻¹ + ((p - a : ℕ) : ZMod q)⁻¹)) = 0 := by
          calc ((p - a : ℕ) : ZMod q) * ((p : ZMod q) * ((a : ZMod q)⁻¹ + ((p - a : ℕ) : ZMod q)⁻¹))
              = (p : ZMod q) * (((p - a : ℕ) : ZMod q) * (a : ZMod q)⁻¹ +
                ((p - a : ℕ) : ZMod q) * ((p - a : ℕ) : ZMod q)⁻¹) := by ring
            _ = (p : ZMod q) * (((p : ZMod q) - (a : ZMod q)) * (a : ZMod q)⁻¹ + 1) := by rw [hu', hsub]
            _ = (p : ZMod q) * ((p : ZMod q) * (a : ZMod q)⁻¹ - 1 + 1) := by rw [sub_mul, hu]
            _ = (p : ZMod q) ^ 2 * (a : ZMod q)⁻¹ := by ring
            _ = 0 := by rw [hp2_z, zero_mul]
        have := congr_arg (((p - a : ℕ) : ZMod q)⁻¹ * ·) hmul
        simpa [← mul_assoc, inv_mul_cancel_zmod_sq hp hnd'] using this
      have h2sum : 2 * ((p : ZMod q) * ∑ a ∈ Finset.Ico 1 p, (a : ZMod q)⁻¹) = 0 := by
        have hs := Finset.sum_congr rfl hpair
        rw [Finset.sum_const_zero, ← Finset.mul_sum, Finset.sum_add_distrib, hrefl] at hs
        linear_combination hs
      have h2nd : ¬ p ∣ 2 := fun hd => absurd (Nat.le_of_dvd (by decide) hd) (by omega)
      have h2u : (2 : ZMod q)⁻¹ * (2 : ZMod q) = 1 := inv_mul_cancel_zmod_sq (j := 2) hp h2nd
      have := congr_arg ((2 : ZMod q)⁻¹ * ·) h2sum
      simpa [← mul_assoc, h2u] using this
    rw [hsum0, add_zero]
  rw [hA_val, hU_val, mul_one]

private lemma prove_a383505 (p : ℕ) (hp : p.Prime) :
    Nat.choose ((p ^ 2 - 1) * p ^ 2) (p ^ 2) ≡ p ^ 2 - 1 [MOD p ^ 2] ∧
    ∀ k < p ^ 2 - 1, ¬ (Nat.choose (k * p ^ 2) (k + 1) ≡ p ^ 2 - 1 [MOD p ^ 2]) := by
  refine ⟨?_, fun k hk => lower_bound hp hk⟩
  rcases hp.eq_two_or_odd with rfl | hodd
  · decide
  · have hp3 : 3 ≤ p := by have := hp.two_le; omega
    exact upper_bound_odd hp hp3

end OMA.P_oeis_a383505

theorem OMA.solution : type_of% @OMA.S_oeis_a383505.main :=
  OMA.P_oeis_a383505.prove_a383505

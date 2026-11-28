import OMAStatements.S_oeis_a292180

/-!
Proof of the OEIS A292180 conjecture.

For any odd `m ≥ 1` and odd `d ≥ 1`:
1. `(1 + X) * invOneSubX = 1 + 2 * (X * invOneSubX)` and
   `(1 - X) * invOneAddX = 1 - 2 * (X * invOneAddX)`.
2. Expanding by the binomial theorem modulo `8`:
   - `j = 0`: `1 - 1 = 0`,
   - `j ≥ 3`: `8 ∣ 2^j`,
   - `j = 2`: `4 * C(m, 2) * ([u^d] (u/(1-u))^2 - [u^d] (u/(1+u))^2) = 4 * C(m, 2) * ((d - 1) - (-1)^d * (d - 1)) = 8 * C(m, 2) * (d - 1) ≡ 0 (mod 8)` (since `d` is odd!),
   - `j = 1`: `2 * m * ([u^d] (u/(1-u)) + [u^d] (u/(1+u))) = 2 * m * (1 + (-1)^(d - 1)) = 4 * m ≡ 4 (mod 8)` (since `m` and `d` are odd!).
3. Hence for every odd `k`, `A292180 k ≡ 4 * k.divisors.card (mod 8)`.
4. For `k = (2 * n - 1) ^ 2`, `k` is odd and a perfect square, so `k.divisors.card` is odd;
   hence `A292180 k ≡ 4 (mod 8)`, i.e., `4 ∣ A292180 k` and `Odd (A292180 k / 4)`.
-/

namespace A292180Proof

open Finset PowerSeries OMA.S_oeis_a292180

private lemma coeff_zero_X_mul (F : PowerSeries ℤ) : (PowerSeries.X * F).coeff 0 = 0 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, PowerSeries.constantCoeff_X, zero_mul]

private lemma one_sub_X_mul_inv : (1 - PowerSeries.X) * invOneSubX = 1 := by
  ext k
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_one]
  unfold invOneSubX
  cases k with
  | zero => simp [coeff_zero_X_mul]
  | succ k => simp [PowerSeries.coeff_succ_X_mul]

private lemma one_add_X_mul_inv : (1 + PowerSeries.X) * invOneAddX = 1 := by
  ext k
  rw [add_mul, one_mul, map_add, PowerSeries.coeff_one]
  unfold invOneAddX
  cases k with
  | zero => simp [coeff_zero_X_mul]
  | succ k =>
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk,
      if_neg (Nat.succ_ne_zero k), pow_succ]
    ring

private lemma one_add_X_mul_invSub :
    (1 + PowerSeries.X) * invOneSubX = 1 + 2 * (PowerSeries.X * invOneSubX) := by
  have h := one_sub_X_mul_inv
  linear_combination h

private lemma one_sub_X_mul_invAdd :
    (1 - PowerSeries.X) * invOneAddX = 1 + (-2) * (PowerSeries.X * invOneAddX) := by
  have h := one_add_X_mul_inv
  linear_combination h

private lemma coeff_X_mul_invOneSub (d : ℕ) (hd : 1 ≤ d) :
    (PowerSeries.X * invOneSubX).coeff d = 1 := by
  cases d with
  | zero => omega
  | succ d' =>
    rw [PowerSeries.coeff_succ_X_mul]
    unfold invOneSubX
    rw [PowerSeries.coeff_mk]

private lemma coeff_X_mul_invOneAdd (d : ℕ) (hd : 1 ≤ d) :
    (PowerSeries.X * invOneAddX).coeff d = (-1 : ℤ) ^ (d - 1) := by
  cases d with
  | zero => omega
  | succ d' =>
    rw [PowerSeries.coeff_succ_X_mul]
    unfold invOneAddX
    rw [PowerSeries.coeff_mk, Nat.add_sub_cancel]

private lemma coeff_sq_X_mul_invOneSub (d : ℕ) :
    ((PowerSeries.X * invOneSubX) ^ 2).coeff d = if 1 ≤ d then ((d - 1 : ℕ) : ℤ) else 0 := by
  rw [sq, PowerSeries.coeff_mul]
  cases d with
  | zero => simp [coeff_zero_X_mul]
  | succ d' =>
    rw [if_pos (by omega), show d' + 1 - 1 = d' by omega]
    have hterm : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal (d' + 1),
        (PowerSeries.X * invOneSubX).coeff p.1 * (PowerSeries.X * invOneSubX).coeff p.2 =
        if p.1 = 0 ∨ p.2 = 0 then 0 else 1 := by
      intro p hp
      simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      by_cases h1 : p.1 = 0
      · rw [if_pos (Or.inl h1), h1, coeff_zero_X_mul, zero_mul]
      · by_cases h2 : p.2 = 0
        · rw [if_pos (Or.inr h2), h2, coeff_zero_X_mul, mul_zero]
        · rw [if_neg (by tauto), coeff_X_mul_invOneSub p.1 (by omega),
            coeff_X_mul_invOneSub p.2 (by omega), mul_one]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite, Finset.sum_const_zero, zero_add]
    have hcard : ((Finset.HasAntidiagonal.antidiagonal (d' + 1)).filter (fun p => ¬ (p.1 = 0 ∨ p.2 = 0))).card = d' := by
      have hbij : ((Finset.HasAntidiagonal.antidiagonal (d' + 1)).filter (fun p => ¬ (p.1 = 0 ∨ p.2 = 0))) =
          (Finset.range d').image (fun i => (i + 1, d' - i)) := by
        ext p
        simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_image, Finset.mem_range]
        constructor
        · rintro ⟨hsum, hne⟩
          refine ⟨p.1 - 1, by omega, Prod.ext (by omega) (by omega)⟩
        · rintro ⟨i, hi, rfl⟩
          exact ⟨by omega, by omega⟩
      rw [hbij, Finset.card_image_of_injective _ (fun a b h => by
        have := (Prod.mk.inj h).1; omega), Finset.card_range]
    rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_one]

private lemma coeff_sq_X_mul_invOneAdd (d : ℕ) :
    ((PowerSeries.X * invOneAddX) ^ 2).coeff d =
      if 1 ≤ d then (-1 : ℤ) ^ d * ((d - 1 : ℕ) : ℤ) else 0 := by
  rw [sq, PowerSeries.coeff_mul]
  cases d with
  | zero => simp [coeff_zero_X_mul]
  | succ d' =>
    rw [if_pos (by omega), show d' + 1 - 1 = d' by omega]
    have hterm : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal (d' + 1),
        (PowerSeries.X * invOneAddX).coeff p.1 * (PowerSeries.X * invOneAddX).coeff p.2 =
        if p.1 = 0 ∨ p.2 = 0 then 0 else (-1 : ℤ) ^ (d' + 1) := by
      intro p hp
      simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      by_cases h1 : p.1 = 0
      · rw [if_pos (Or.inl h1), h1, coeff_zero_X_mul, zero_mul]
      · by_cases h2 : p.2 = 0
        · rw [if_pos (Or.inr h2), h2, coeff_zero_X_mul, mul_zero]
        · rw [if_neg (by tauto), coeff_X_mul_invOneAdd p.1 (by omega),
            coeff_X_mul_invOneAdd p.2 (by omega), ← pow_add]
          have hexp : p.1 - 1 + (p.2 - 1) + 2 = d' + 1 := by omega
          rw [← hexp, pow_add]
          ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite, Finset.sum_const_zero, zero_add]
    have hcard : ((Finset.HasAntidiagonal.antidiagonal (d' + 1)).filter (fun p => ¬ (p.1 = 0 ∨ p.2 = 0))).card = d' := by
      have hbij : ((Finset.HasAntidiagonal.antidiagonal (d' + 1)).filter (fun p => ¬ (p.1 = 0 ∨ p.2 = 0))) =
          (Finset.range d').image (fun i => (i + 1, d' - i)) := by
        ext p
        simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_image, Finset.mem_range]
        constructor
        · rintro ⟨hsum, hne⟩
          refine ⟨p.1 - 1, by omega, Prod.ext (by omega) (by omega)⟩
        · rintro ⟨i, hi, rfl⟩
          exact ⟨by omega, by omega⟩
      rw [hbij, Finset.card_image_of_injective _ (fun a b h => by
        have := (Prod.mk.inj h).1; omega), Finset.card_range]
    rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_comm]

private lemma pairSeries_coeff_mod8 {m d : ℕ} (hm : m % 2 = 1) (hd : d % 2 = 1) :
    (pairSeries m).coeff d % 8 = 4 := by
  unfold pairSeries
  have hodd_m : (-1 : PowerSeries ℤ) ^ m = -1 := by
    have : Odd m := ⟨m / 2, by omega⟩
    exact this.neg_one_pow
  rw [hodd_m, mul_assoc (-1 : PowerSeries ℤ), ← mul_pow, ← mul_pow, one_add_X_mul_invSub, one_sub_X_mul_invAdd]
  rw [add_pow, add_pow]
  have hsub : ((-1 : PowerSeries ℤ) * ∑ i ∈ Finset.range (m + 1),
      (1 : PowerSeries ℤ) ^ i * ((-2) * (PowerSeries.X * invOneAddX)) ^ (m - i) *
      (Nat.choose m i : PowerSeries ℤ)) =
      -(∑ i ∈ Finset.range (m + 1),
        (1 : PowerSeries ℤ) ^ i * ((-2) * (PowerSeries.X * invOneAddX)) ^ (m - i) *
        (Nat.choose m i : PowerSeries ℤ)) := by ring
  rw [hsub, ← sub_eq_add_neg, map_sub, map_sum, map_sum, ← Finset.sum_sub_distrib]
  -- Reindex j = m - i via range_reflect? Easier: write add_comm 1 _ before add_pow!
  have hswap : ∀ (F : PowerSeries ℤ),
      ∑ i ∈ Finset.range (m + 1),
        ((1 : PowerSeries ℤ) ^ i * F ^ (m - i) * (Nat.choose m i : PowerSeries ℤ)).coeff d =
      ∑ j ∈ Finset.range (m + 1),
        (Nat.choose m j : ℤ) * (F ^ j).coeff d := by
    intro F
    rw [← map_sum]
    have h1 : (∑ i ∈ Finset.range (m + 1),
        (1 : PowerSeries ℤ) ^ i * F ^ (m - i) * (Nat.choose m i : PowerSeries ℤ)) =
        (F + 1) ^ m := by rw [← add_pow, add_comm]
    rw [h1, add_pow, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [one_pow]
    have hcast : (Nat.choose m j : PowerSeries ℤ) = PowerSeries.C (Nat.choose m j : ℤ) := by simp
    rw [hcast, mul_comm, PowerSeries.coeff_C_mul, mul_one]
  rw [Finset.sum_sub_distrib, hswap, hswap, ← Finset.sum_sub_distrib]
  -- Split j = 0, j = 1, j = 2, and j ≥ 3
  have hterm0 : (Nat.choose m 0 : ℤ) * ((2 * (PowerSeries.X * invOneSubX)) ^ 0).coeff d -
      (Nat.choose m 0 : ℤ) * (((-2) * (PowerSeries.X * invOneAddX)) ^ 0).coeff d = 0 := by
    simp
  have hterm1 : (Nat.choose m 1 : ℤ) * ((2 * (PowerSeries.X * invOneSubX)) ^ 1).coeff d -
      (Nat.choose m 1 : ℤ) * (((-2) * (PowerSeries.X * invOneAddX)) ^ 1).coeff d = 4 * (m : ℤ) := by
    simp only [Nat.choose_one_right, pow_one]
    have hc1 : ((2 : PowerSeries ℤ) * (PowerSeries.X * invOneSubX)).coeff d = 2 := by
      rw [show (2 : PowerSeries ℤ) = PowerSeries.C 2 from rfl, PowerSeries.coeff_C_mul,
        coeff_X_mul_invOneSub d (by omega), mul_one]
    have hc2 : ((-2 : PowerSeries ℤ) * (PowerSeries.X * invOneAddX)).coeff d = -2 := by
      rw [show (-2 : PowerSeries ℤ) = PowerSeries.C (-2) by simp, PowerSeries.coeff_C_mul,
        coeff_X_mul_invOneAdd d (by omega)]
      have hev : Even (d - 1) := ⟨(d - 1) / 2, by omega⟩
      rw [hev.neg_one_pow, mul_one]
    rw [hc1, hc2]; ring
  have hterm2_dvd : (8 : ℤ) ∣
      ((Nat.choose m 2 : ℤ) * ((2 * (PowerSeries.X * invOneSubX)) ^ 2).coeff d -
       (Nat.choose m 2 : ℤ) * (((-2) * (PowerSeries.X * invOneAddX)) ^ 2).coeff d) := by
    rw [mul_pow (2 : PowerSeries ℤ), mul_pow (-2 : PowerSeries ℤ)]
    have hc1 : ((2 : PowerSeries ℤ) ^ 2 * (PowerSeries.X * invOneSubX) ^ 2).coeff d =
        4 * ((d - 1 : ℕ) : ℤ) := by
      rw [show (2 : PowerSeries ℤ) ^ 2 = PowerSeries.C 4 by norm_num,
        PowerSeries.coeff_C_mul, coeff_sq_X_mul_invOneSub, if_pos (by omega)]
    have hc2 : ((-2 : PowerSeries ℤ) ^ 2 * (PowerSeries.X * invOneAddX) ^ 2).coeff d =
        -4 * ((d - 1 : ℕ) : ℤ) := by
      rw [show (-2 : PowerSeries ℤ) ^ 2 = PowerSeries.C 4 by norm_num,
        PowerSeries.coeff_C_mul, coeff_sq_X_mul_invOneAdd, if_pos (by omega)]
      have hodd_d : Odd d := ⟨d / 2, by omega⟩
      rw [hodd_d.neg_one_pow]; ring
    rw [hc1, hc2]
    exact ⟨(Nat.choose m 2 : ℤ) * ((d - 1 : ℕ) : ℤ), by ring⟩
  have htail_dvd : ∀ j : ℕ, 3 ≤ j →
      (8 : ℤ) ∣ ((Nat.choose m j : ℤ) * ((2 * (PowerSeries.X * invOneSubX)) ^ j).coeff d -
        (Nat.choose m j : ℤ) * (((-2) * (PowerSeries.X * invOneAddX)) ^ j).coeff d) := by
    intro j hj
    have hd1 : (8 : ℤ) ∣ ((2 * (PowerSeries.X * invOneSubX)) ^ j).coeff d := by
      rw [mul_pow, show (2 : PowerSeries ℤ) ^ j = PowerSeries.C ((2 : ℤ) ^ j) by simp,
        PowerSeries.coeff_C_mul]
      have h8 : (8 : ℤ) ∣ (2 : ℤ) ^ j := by
        rw [show j = 3 + (j - 3) by omega, pow_add]; exact dvd_mul_right 8 _
      exact dvd_mul_of_dvd_left h8 _
    have hd2 : (8 : ℤ) ∣ (((-2) * (PowerSeries.X * invOneAddX)) ^ j).coeff d := by
      rw [mul_pow, show (-2 : PowerSeries ℤ) ^ j = PowerSeries.C ((-2 : ℤ) ^ j) by simp,
        PowerSeries.coeff_C_mul]
      have h8 : (8 : ℤ) ∣ (-2 : ℤ) ^ j := by
        rw [show j = 3 + (j - 3) by omega, pow_add]
        exact dvd_mul_of_dvd_left ⟨-1, by norm_num⟩ _
      exact dvd_mul_of_dvd_left h8 _
    exact dvd_sub (dvd_mul_of_dvd_right hd1 _) (dvd_mul_of_dvd_right hd2 _)
  have hsum_dvd : (8 : ℤ) ∣
      ((∑ j ∈ Finset.range (m + 1),
        ((Nat.choose m j : ℤ) * ((2 * (PowerSeries.X * invOneSubX)) ^ j).coeff d -
         (Nat.choose m j : ℤ) * (((-2) * (PowerSeries.X * invOneAddX)) ^ j).coeff d)) -
       4 * (m : ℤ)) := by
    have h1mem : 1 ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
    rw [← Finset.add_sum_erase _ _ h1mem, hterm1, add_sub_cancel_left]
    apply Finset.dvd_sum
    intro j hj
    rw [Finset.mem_erase] at hj
    by_cases hj0 : j = 0
    · subst hj0; rw [hterm0]; exact dvd_zero 8
    · by_cases hj2 : j = 2
      · subst hj2; exact hterm2_dvd
      · exact htail_dvd j (by omega)
  obtain ⟨q, hq⟩ := hsum_dvd
  have h4m : (4 * (m : ℤ)) % 8 = 4 := by omega
  omega

private lemma card_divisors_sq_odd (t : ℕ) (ht : 1 ≤ t) :
    (t ^ 2).divisors.card % 2 = 1 := by
  have ht0 : t ^ 2 ≠ 0 := pow_ne_zero 2 (by omega)
  have htmem : t ∈ (t ^ 2).divisors := Nat.mem_divisors.mpr ⟨by rw [sq]; exact dvd_mul_right t t, ht0⟩
  set S := (t ^ 2).divisors.erase t
  set S_lo := S.filter (fun d => d < t)
  set S_hi := S.filter (fun d => t < d)
  have hunion : S = S_lo ∪ S_hi := by
    ext d
    simp only [S, S_lo, S_hi, Finset.mem_union, Finset.mem_filter, Finset.mem_erase]
    constructor
    · intro ⟨hne, hd⟩
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl ⟨⟨hne, hd⟩, hlt⟩
      · exact Or.inr ⟨⟨hne, hd⟩, hgt⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hdisj : Disjoint S_lo S_hi := by
    rw [Finset.disjoint_left]
    intro d h1 h2
    simp only [S_lo, S_hi, Finset.mem_filter] at h1 h2
    omega
  have hcard_eq : S_lo.card = S_hi.card := by
    apply Finset.card_bij (fun d _ => t ^ 2 / d)
    · intro d hd
      simp only [S_lo, S_hi, S, Finset.mem_filter, Finset.mem_erase, Nat.mem_divisors] at hd ⊢
      have hd_pos : 0 < d := Nat.pos_of_ne_zero (fun h0 => by rw [h0, zero_dvd_iff] at hd; omega)
      have hmul : d * (t ^ 2 / d) = t ^ 2 := Nat.mul_div_cancel' hd.1.2.1
      have hgt : t < t ^ 2 / d := by nlinarith
      exact ⟨⟨by omega, ⟨Nat.div_dvd_of_dvd hd.1.2.1, ht0⟩⟩, hgt⟩
    · intro a ha b hb heq
      simp only [S_lo, S, Finset.mem_filter, Finset.mem_erase, Nat.mem_divisors] at ha hb
      have ha_mul : a * (t ^ 2 / a) = t ^ 2 := Nat.mul_div_cancel' ha.1.2.1
      have hb_mul : b * (t ^ 2 / b) = t ^ 2 := Nat.mul_div_cancel' hb.1.2.1
      have hpos : 0 < t ^ 2 / a := by
        have ha_pos : 0 < a := Nat.pos_of_ne_zero (fun h0 => by
          have hdvd := ha.1.2.1; rw [h0, zero_dvd_iff] at hdvd; omega)
        nlinarith
      rw [heq] at ha_mul
      nlinarith
    · intro d hd
      simp only [S_lo, S_hi, S, Finset.mem_filter, Finset.mem_erase, Nat.mem_divisors] at hd ⊢
      have hd_pos : 0 < d := Nat.pos_of_ne_zero (fun h0 => by
        have hdvd := hd.1.2.1; rw [h0, zero_dvd_iff] at hdvd; omega)
      have hmul : d * (t ^ 2 / d) = t ^ 2 := Nat.mul_div_cancel' hd.1.2.1
      have hlt : t ^ 2 / d < t := by nlinarith
      refine ⟨t ^ 2 / d, ⟨⟨by omega, ⟨Nat.div_dvd_of_dvd hd.1.2.1, ht0⟩⟩, hlt⟩, ?_⟩
      exact Nat.div_div_self hd.1.2.1 ht0
  have htot : (t ^ 2).divisors.card = S.card + 1 := (Finset.card_erase_add_one htmem).symm
  rw [htot, hunion, Finset.card_union_of_disjoint hdisj, hcard_eq]
  omega

theorem solve : type_of% @OMA.S_oeis_a292180.main := by
  intro n hn
  set t := 2 * n - 1
  have ht1 : 1 ≤ t := by omega
  have ht_odd : t % 2 = 1 := by omega
  have hk_odd : t ^ 2 % 2 = 1 := by rw [sq, Nat.mul_mod, ht_odd]
  have hmod8 : A292180 (t ^ 2) % 8 = 4 := by
    unfold A292180
    have hsum_mod : (∑ m ∈ (t ^ 2).divisors, (pairSeries m).coeff (t ^ 2 / m)) ≡
        (∑ _m ∈ (t ^ 2).divisors, (4 : ℤ)) [ZMOD 8] := by
      have hdvd : (8 : ℤ) ∣
          (∑ m ∈ (t ^ 2).divisors, ((pairSeries m).coeff (t ^ 2 / m) - 4)) := by
        apply Finset.dvd_sum
        intro m hm
        rw [Nat.mem_divisors] at hm
        have hm_odd : m % 2 = 1 := by
          obtain ⟨q, hq⟩ := hm.1
          by_contra hne
          have hm0 : m % 2 = 0 := by omega
          have h1 := congrArg (· % 2) hq
          rw [hk_odd, Nat.mul_mod, hm0, zero_mul, Nat.zero_mod] at h1
          omega
        have hq_odd : (t ^ 2 / m) % 2 = 1 := by
          have hmul : m * (t ^ 2 / m) = t ^ 2 := Nat.mul_div_cancel' hm.1
          by_contra hne
          have hq0 : (t ^ 2 / m) % 2 = 0 := by omega
          have h1 := congrArg (· % 2) hmul
          rw [hk_odd, Nat.mul_mod, hq0, mul_zero, Nat.zero_mod] at h1
          omega
        have hm8 := pairSeries_coeff_mod8 hm_odd hq_odd
        omega
      rw [Finset.sum_sub_distrib] at hdvd
      exact Int.modEq_iff_dvd.mpr (by simpa [neg_sub] using hdvd.neg_right)
    have hcard_odd := card_divisors_sq_odd t ht1
    rw [Finset.sum_const, nsmul_eq_mul] at hsum_mod
    have h1 := Int.ModEq.eq hsum_mod
    omega
  exact ⟨by omega, ⟨A292180 (t ^ 2) / 8, by omega⟩⟩

end A292180Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a292180.main :=
  A292180Proof.solve

import OMAStatements.S_oeis_a378578
import Mathlib

namespace OMA.S_oeis_a378578

private lemma removeThrees_mod2 (m : ℤ) : removeThrees m % 2 = m % 2 := by
  unfold removeThrees
  split_ifs with hm
  · subst hm; rfl
  · set k := padicValInt 3 m
    have hdvd : (3 : ℤ) ^ k ∣ m := by
      have h1 : (3 : ℕ) ^ k ∣ m.natAbs := by
        let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        exact pow_padicValNat_dvd
      exact Int.natCast_dvd.mpr h1
    have hmul : (3 : ℤ) ^ k * (m / (3 : ℤ) ^ k) = m := Int.mul_ediv_cancel' hdvd
    have h3odd : ((3 : ℤ) ^ k) % 2 = 1 := by
      induction k with
      | zero => simp
      | succ k' ih =>
        rw [pow_succ, Int.mul_emod, ih]; norm_num
    have h := congr_arg (· % 2) hmul
    rw [Int.mul_emod, h3odd, one_mul, Int.emod_emod] at h
    exact h

-- Fibbinary predicate: no two adjacent 1-bits in binary
private def isFibbin : ℕ → Bool
  | 0 => true
  | 1 => true
  | n + 2 => if (n + 2) % 4 = 3 then false else isFibbin ((n + 2) / 2)

private lemma isFibbin_two_mul (k : ℕ) : isFibbin (2 * k) = isFibbin k := by
  cases k with
  | zero => rfl
  | succ k' =>
    have h2 : 2 * (k' + 1) = (2 * k') + 2 := by omega
    rw [h2]
    simp only [isFibbin]
    have hmod : (2 * k' + 2) % 4 ≠ 3 := by omega
    have hdiv : (2 * k' + 2) / 2 = k' + 1 := by omega
    rw [if_neg hmod, hdiv]

private lemma isFibbin_four_mul_add_one (j : ℕ) : isFibbin (4 * j + 1) = isFibbin j := by
  cases j with
  | zero => simp [isFibbin]
  | succ j' =>
    have h4 : 4 * (j' + 1) + 1 = (4 * j' + 3) + 2 := by omega
    rw [h4]
    simp only [isFibbin]
    have hmod : (4 * j' + 3 + 2) % 4 ≠ 3 := by omega
    have hdiv : (4 * j' + 3 + 2) / 2 = 2 * (j' + 1) := by omega
    rw [if_neg hmod, hdiv, isFibbin_two_mul]

private lemma isFibbin_four_mul_add_three (j : ℕ) : isFibbin (4 * j + 3) = false := by
  have h4 : 4 * j + 3 = (4 * j + 1) + 2 := by omega
  rw [h4]
  simp only [isFibbin]
  have hmod : (4 * j + 1 + 2) % 4 = 3 := by omega
  rw [if_pos hmod]

-- Lucas mod 2: C(3*n, n) % 2 = 1 ↔ isFibbin n = true
private lemma choose_three_mul_mod2 (n : ℕ) :
    Nat.choose (3 * n) n % 2 = if isFibbin n then 1 else 0 := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hnk : n = 2 * k := by omega
      subst hnk
      rw [isFibbin_two_mul]
      cases k with
      | zero => simp [isFibbin]
      | succ k' =>
        have hluc : Nat.choose (3 * (2 * (k' + 1))) (2 * (k' + 1)) ≡
            Nat.choose (3 * (k' + 1)) (k' + 1) * Nat.choose 0 0 [MOD 2] := by
          simpa [show 3 * (2 * (k' + 1)) = 2 * (3 * (k' + 1)) by omega,
            Nat.mul_div_right _ (by omega : 0 < 2), Nat.mul_mod_right] using
            Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 2)
              (n := 3 * (2 * (k' + 1))) (k := 2 * (k' + 1))
        simp only [Nat.choose_self, mul_one, Nat.ModEq] at hluc
        rw [hluc, ih (k' + 1) (by omega)]
    · subst hk
      rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
      · have h4 : 2 * k + 1 = 4 * j + 1 := by omega
        rw [h4, isFibbin_four_mul_add_one]
        have hluc1 : Nat.choose (2 * (6 * j + 1) + 1) (2 * (2 * j) + 1) ≡
            Nat.choose (6 * j + 1) (2 * j) * Nat.choose 1 1 [MOD 2] := by
          simpa [Nat.mul_add_div (by omega : 0 < 2), Nat.mul_add_mod] using
            Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 2)
              (n := 2 * (6 * j + 1) + 1) (k := 2 * (2 * j) + 1)
        have hluc2 : Nat.choose (2 * (3 * j) + 1) (2 * j) ≡
            Nat.choose (3 * j) j * Nat.choose 1 0 [MOD 2] := by
          simpa [Nat.mul_add_div (by omega : 0 < 2), Nat.mul_add_mod,
            Nat.mul_div_right _ (by omega : 0 < 2), Nat.mul_mod_right] using
            Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 2)
              (n := 2 * (3 * j) + 1) (k := 2 * j)
        simp only [Nat.choose_self, Nat.choose_zero_right, mul_one, Nat.ModEq] at hluc1 hluc2
        rw [show 3 * (4 * j + 1) = 2 * (6 * j + 1) + 1 by omega,
          show 4 * j + 1 = 2 * (2 * j) + 1 by omega, hluc1,
          show 6 * j + 1 = 2 * (3 * j) + 1 by omega, hluc2]
        cases j with
        | zero => simp [isFibbin]
        | succ j' => exact ih (j' + 1) (by omega)
      · have h4 : 2 * k + 1 = 4 * j + 3 := by omega
        rw [h4, isFibbin_four_mul_add_three]
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hluc1 : Nat.choose (2 * (6 * j + 4) + 1) (2 * (2 * j + 1) + 1) ≡
            Nat.choose (6 * j + 4) (2 * j + 1) * Nat.choose 1 1 [MOD 2] := by
          simpa [Nat.mul_add_div (by omega : 0 < 2), Nat.mul_add_mod] using
            Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 2)
              (n := 2 * (6 * j + 4) + 1) (k := 2 * (2 * j + 1) + 1)
        have hluc2 : Nat.choose (2 * (3 * j + 2)) (2 * j + 1) ≡
            Nat.choose (3 * j + 2) j * Nat.choose 0 1 [MOD 2] := by
          simpa [Nat.mul_add_div (by omega : 0 < 2), Nat.mul_add_mod,
            Nat.mul_div_right _ (by omega : 0 < 2), Nat.mul_mod_right] using
            Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 2)
              (n := 2 * (3 * j + 2)) (k := 2 * j + 1)
        simp only [Nat.choose_self, Nat.choose_zero_succ, mul_one, mul_zero, Nat.ModEq] at hluc1 hluc2
        rw [show 3 * (4 * j + 3) = 2 * (6 * j + 4) + 1 by omega,
          show 4 * j + 3 = 2 * (2 * j + 1) + 1 by omega, hluc1,
          show 6 * j + 4 = 2 * (3 * j + 2) by omega, hluc2]; rfl

private lemma fuss_catalan_dvd (n : ℕ) : (2 * n + 1) ∣ Nat.choose (3 * n) n := by
  have h1 := Nat.choose_succ_right_eq (3 * n) (2 * n)
  have hsym : Nat.choose (3 * n) (2 * n) = Nat.choose (3 * n) n := by
    have := Nat.choose_symm (show n ≤ 3 * n by omega)
    simpa [show 3 * n - n = 2 * n by omega] using this
  rw [hsym, show 3 * n - 2 * n = n by omega] at h1
  have hcop : Nat.Coprime (2 * n + 1) n := by
    rw [show 2 * n + 1 = n + (n + 1) by omega]
    exact Nat.coprime_self_add_left.mpr (Nat.coprime_self_add_left.mpr (Nat.coprime_one_left n))
  have hdvd : (2 * n + 1) ∣ n * Nat.choose (3 * n) n :=
    ⟨Nat.choose (3 * n) (2 * n + 1), by linarith⟩
  exact hcop.dvd_of_dvd_mul_left hdvd

private lemma fuss_catalan_mod2 (n : ℕ) :
    (Nat.choose (3 * n) n / (2 * n + 1)) % 2 = if isFibbin n then 1 else 0 := by
  have hdvd := fuss_catalan_dvd n
  have hmul : (2 * n + 1) * (Nat.choose (3 * n) n / (2 * n + 1)) = Nat.choose (3 * n) n :=
    Nat.mul_div_cancel' hdvd
  have h := congr_arg (· % 2) hmul
  rw [Nat.mul_mod, show (2 * n + 1) % 2 = 1 by omega, one_mul, Nat.mod_mod,
    choose_three_mul_mod2] at h
  exact h

private lemma coeff_sq_zmod2 (f : PowerSeries (ZMod 2)) (n : ℕ) :
    PowerSeries.coeff n (f ^ 2) =
      if Even n then PowerSeries.coeff (n / 2) f else 0 := by
  have hsq : ∀ x : ZMod 2, x ^ 2 = x := by decide
  have htrunc : PowerSeries.coeff n (f ^ 2) =
      PowerSeries.coeff n ((∑ k ∈ Finset.range (n + 1),
        PowerSeries.C (PowerSeries.coeff k f) * PowerSeries.X ^ k) ^ 2) := by
    set P : PowerSeries (ZMod 2) :=
      ∑ k ∈ Finset.range (n + 1), PowerSeries.C (PowerSeries.coeff k f) * PowerSeries.X ^ k
    have hdiff : ∀ k ≤ n, PowerSeries.coeff k (f - P) = 0 := by
      intro k hk
      rw [map_sub, sub_eq_zero]
      simp only [P, map_sum, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
      rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hjk; rw [if_neg (Ne.symm hjk), mul_zero]
      · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
    have hmul0 : PowerSeries.coeff n ((f - P) * (f + P)) = 0 := by
      rw [PowerSeries.coeff_mul]
      refine Finset.sum_eq_zero fun ab hab => ?_
      have hsum : ab.1 + ab.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
      rw [hdiff ab.1 (by omega), zero_mul]
    have hsub : f ^ 2 - P ^ 2 = (f - P) * (f + P) := by ring
    rw [← hsub, map_sub, sub_eq_zero] at hmul0
    exact hmul0
  rw [htrunc]
  have hadd2 : ∀ a b : PowerSeries (ZMod 2), (a + b) ^ 2 = a ^ 2 + b ^ 2 := by
    intro a b
    have h2 : (2 : PowerSeries (ZMod 2)) = 0 := by
      have : (2 : ZMod 2) = 0 := by decide
      rw [← map_ofNat PowerSeries.C 2, this, map_zero]
    calc (a + b) ^ 2 = a ^ 2 + 2 * (a * b) + b ^ 2 := by ring
      _ = a ^ 2 + b ^ 2 := by rw [h2, zero_mul, add_zero]
  have hfrob : ∀ (s : Finset ℕ) (g : ℕ → PowerSeries (ZMod 2)),
      (∑ k ∈ s, g k) ^ 2 = ∑ k ∈ s, (g k) ^ 2 := by
    intro s g
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons, hadd2, ih]
  rw [hfrob]
  simp only [mul_pow, ← map_pow PowerSeries.C, ← pow_mul, map_sum, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow]
  rcases Nat.even_or_odd n with ⟨q, hq⟩ | ⟨q, hq⟩
  · rw [if_pos ⟨q, hq⟩, show n / 2 = q by omega]
    rw [Finset.sum_eq_single q]
    · simp [hsq, show q * 2 = n by omega]
    · intro k _ hkq; rw [if_neg (by omega), mul_zero]
    · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
  · have hne : ¬ Even n := by rw [Nat.not_even_iff_odd]; exact ⟨q, hq⟩
    rw [if_neg hne]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg (by omega), mul_zero]

private def F_fib : PowerSeries (ZMod 2) :=
  PowerSeries.mk fun n => if isFibbin n then 1 else 0

private lemma F_fib_split : F_fib = F_fib ^ 2 + PowerSeries.X * (F_fib ^ 2) ^ 2 := by
  ext n
  rw [map_add, coeff_sq_zmod2]
  cases n with
  | zero =>
    simp [F_fib, isFibbin]
  | succ m =>
    rw [PowerSeries.coeff_succ_X_mul, coeff_sq_zmod2]
    rcases Nat.even_or_odd (m + 1) with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hne : ¬ Even m := by rw [Nat.not_even_iff_odd]; exact ⟨k - 1, by omega⟩
      rw [if_pos ⟨k, hk⟩, if_neg hne, add_zero, show (m + 1) / 2 = k by omega]
      simp only [F_fib, PowerSeries.coeff_mk, show m + 1 = 2 * k by omega, isFibbin_two_mul]
    · have hne : ¬ Even (m + 1) := by rw [Nat.not_even_iff_odd]; exact ⟨k, hk⟩
      have hev : Even m := ⟨k, by omega⟩
      rw [if_neg hne, zero_add, if_pos hev, show m / 2 = k by omega, coeff_sq_zmod2]
      rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
      · rw [if_pos ⟨j, hj⟩, show k / 2 = j by omega]
        simp only [F_fib, PowerSeries.coeff_mk, show m + 1 = 4 * j + 1 by omega,
          isFibbin_four_mul_add_one]
      · have hne2 : ¬ Even k := by rw [Nat.not_even_iff_odd]; exact ⟨j, hj⟩
        rw [if_neg hne2]
        simp only [F_fib, PowerSeries.coeff_mk, show m + 1 = 4 * j + 3 by omega,
          isFibbin_four_mul_add_three]
        simp

private lemma F_fib_eq : F_fib = 1 + PowerSeries.X * F_fib ^ 3 := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      simp [F_fib, isFibbin]
    | succ m =>
      rw [map_add, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero m), zero_add,
        PowerSeries.coeff_succ_X_mul]
      have hcube : F_fib ^ 3 = (F_fib ^ 2 + PowerSeries.X * (F_fib ^ 2) ^ 2) * F_fib ^ 2 := by
        rw [← F_fib_split]; ring
      rw [hcube, add_mul, map_add, show F_fib ^ 2 * F_fib ^ 2 = (F_fib ^ 2) ^ 2 by ring]
      rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
      · -- m = 2*k, so m+1 = 2*k+1 is odd
        have h1 : PowerSeries.coeff m ((F_fib ^ 2) ^ 2) =
            if Even k then PowerSeries.coeff (k / 2) F_fib else 0 := by
          rw [coeff_sq_zmod2, if_pos ⟨k, hk⟩, show m / 2 = k by omega, coeff_sq_zmod2]
        have h2 : PowerSeries.coeff m (PowerSeries.X * (F_fib ^ 2) ^ 2 * F_fib ^ 2) = 0 := by
          cases m with
          | zero => simp [mul_assoc]
          | succ m' =>
            rw [mul_assoc, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mul]
            refine Finset.sum_eq_zero fun ab hab => ?_
            have hsum : ab.1 + ab.2 = m' := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
            by_cases ha : Even ab.1
            · have hb : ¬ Even ab.2 := by
                rcases ha with ⟨r, hr⟩
                rw [Nat.not_even_iff_odd]; exact ⟨k - 1 - r, by omega⟩
              rw [coeff_sq_zmod2 F_fib ab.2, if_neg hb, mul_zero]
            · rw [coeff_sq_zmod2 (F_fib ^ 2) ab.1, if_neg ha, zero_mul]
        rw [h1, h2, add_zero]
        rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
        · rw [if_pos ⟨j, hj⟩, show k / 2 = j by omega]
          simp only [F_fib, PowerSeries.coeff_mk, show m + 1 = 4 * j + 1 by omega,
            isFibbin_four_mul_add_one]
        · have hnek : ¬ Even k := by rw [Nat.not_even_iff_odd]; exact ⟨j, hj⟩
          rw [if_neg hnek]
          simp only [F_fib, PowerSeries.coeff_mk, show m + 1 = 4 * j + 3 by omega,
            isFibbin_four_mul_add_three]
          simp
      · -- m = 2*k + 1, so m+1 = 2*(k+1) is even
        have h1 : PowerSeries.coeff m ((F_fib ^ 2) ^ 2) = 0 := by
          rw [coeff_sq_zmod2, if_neg (by rw [Nat.not_even_iff_odd]; exact ⟨k, hk⟩)]
        have h2 : PowerSeries.coeff m (PowerSeries.X * (F_fib ^ 2) ^ 2 * F_fib ^ 2) =
            PowerSeries.coeff k (F_fib ^ 2 * F_fib) := by
          rw [mul_assoc, show m = (2 * k) + 1 by omega, PowerSeries.coeff_succ_X_mul]
          rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
          -- Only even pairs (2a, 2b) contribute on LHS, matching (a, b) on RHS!
          have hfilt : ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal (2 * k),
              PowerSeries.coeff ab.1 ((F_fib ^ 2) ^ 2) * PowerSeries.coeff ab.2 (F_fib ^ 2) =
              ∑ ab ∈ (Finset.HasAntidiagonal.antidiagonal (2 * k)).filter (fun ab => Even ab.1),
                PowerSeries.coeff ab.1 ((F_fib ^ 2) ^ 2) * PowerSeries.coeff ab.2 (F_fib ^ 2) := by
            rw [← Finset.sum_subset
              (Finset.filter_subset (fun ab : ℕ × ℕ => Even ab.1)
                (Finset.HasAntidiagonal.antidiagonal (2 * k)))]
            intro ab hab hnot
            simp only [Finset.mem_filter, hab, true_and] at hnot
            rw [coeff_sq_zmod2, if_neg hnot, zero_mul]
          rw [hfilt]
          refine Finset.sum_bij (fun ab _ => (ab.1 / 2, ab.2 / 2)) ?_ ?_ ?_ ?_
          · intro ab hab
            simp only [Finset.mem_filter] at hab
            have hsum : ab.1 + ab.2 = 2 * k := Finset.HasAntidiagonal.mem_antidiagonal.mp hab.1
            rcases hab.2 with ⟨a, ha⟩
            exact Finset.HasAntidiagonal.mem_antidiagonal.mpr (by omega)
          · intro ab1 hab1 ab2 hab2 heq
            simp only [Finset.mem_filter] at hab1 hab2
            have h1 := Finset.HasAntidiagonal.mem_antidiagonal.mp hab1.1
            have h2 := Finset.HasAntidiagonal.mem_antidiagonal.mp hab2.1
            rcases hab1.2 with ⟨a1, ha1⟩; rcases hab2.2 with ⟨a2, ha2⟩
            simp only [Prod.mk.injEq] at heq
            ext <;> omega
          · intro ab hab
            have hsum : ab.1 + ab.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
            refine ⟨(2 * ab.1, 2 * ab.2), ?_, ?_⟩
            · exact Finset.mem_filter.mpr
                ⟨Finset.HasAntidiagonal.mem_antidiagonal.mpr (by omega), ⟨ab.1, by omega⟩⟩
            · ext <;> dsimp <;> omega
          · intro ab hab
            simp only [Finset.mem_filter] at hab
            have hsum : ab.1 + ab.2 = 2 * k := Finset.HasAntidiagonal.mem_antidiagonal.mp hab.1
            rcases hab.2 with ⟨a, ha⟩
            have hb : Even ab.2 := ⟨k - a, by omega⟩
            rw [coeff_sq_zmod2 (F_fib ^ 2) ab.1, if_pos ⟨a, ha⟩,
              coeff_sq_zmod2 F_fib ab.2, if_pos hb]
        rw [h1, zero_add, h2]
        have ihk := ih (k + 1) (by omega)
        rw [map_add, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero k), zero_add,
          PowerSeries.coeff_succ_X_mul, show F_fib ^ 3 = F_fib ^ 2 * F_fib by ring] at ihk
        rw [← ihk]
        simp only [F_fib, PowerSeries.coeff_mk, show m + 1 = 2 * (k + 1) by omega,
          isFibbin_two_mul]

private theorem main_proved :
    ∀ (A : PowerSeries ℤ),
      (∀ n : ℕ, PowerSeries.coeff n A =
        removeThrees (PowerSeries.coeff n (1 + PowerSeries.X * A ^ 3))) →
      ∀ n : ℕ, PowerSeries.coeff n A % 2 = ((Nat.choose (3 * n) n / (2 * n + 1) : ℕ) : ℤ) % 2 := by
  intro A hA
  set φ2 : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2)
  set Φ2 : PowerSeries ℤ →+* PowerSeries (ZMod 2) := PowerSeries.map φ2
  have hA_eq_mod2 : Φ2 A = 1 + PowerSeries.X * (Φ2 A) ^ 3 := by
    ext n
    rw [PowerSeries.coeff_map, hA n]
    have hpar := removeThrees_mod2 (PowerSeries.coeff n (1 + PowerSeries.X * A ^ 3))
    have hcast : φ2 (removeThrees (PowerSeries.coeff n (1 + PowerSeries.X * A ^ 3))) =
        φ2 (PowerSeries.coeff n (1 + PowerSeries.X * A ^ 3)) := by
      simp only [φ2, Int.coe_castRingHom]
      exact (ZMod.intCast_eq_intCast_iff _ _ 2).mpr hpar
    rw [hcast, ← PowerSeries.coeff_map]
    simp only [Φ2, map_add, map_one, map_mul, PowerSeries.map_X, map_pow]
  have hA_eq_F : Φ2 A = F_fib := by
    ext n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rw [hA_eq_mod2, F_fib_eq]
      cases n with
      | zero => simp
      | succ m =>
        rw [map_add, map_add, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero m), zero_add, zero_add,
          PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul,
          show (Φ2 A) ^ 3 = (Φ2 A * Φ2 A) * Φ2 A by ring,
          show F_fib ^ 3 = (F_fib * F_fib) * F_fib by ring,
          PowerSeries.coeff_mul, PowerSeries.coeff_mul]
        refine Finset.sum_congr rfl fun ab hab => ?_
        have hsum : ab.1 + ab.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
        rw [ih ab.2 (by omega), PowerSeries.coeff_mul, PowerSeries.coeff_mul]
        congr 1
        refine Finset.sum_congr rfl fun cd hcd => ?_
        have hsum2 : cd.1 + cd.2 = ab.1 := Finset.HasAntidiagonal.mem_antidiagonal.mp hcd
        rw [ih cd.1 (by omega), ih cd.2 (by omega)]
  intro n
  have hn := congr_arg (PowerSeries.coeff n) hA_eq_F
  rw [PowerSeries.coeff_map, F_fib, PowerSeries.coeff_mk] at hn
  have hfc := fuss_catalan_mod2 n
  have hcast : ((PowerSeries.coeff n A : ℤ) : ZMod 2) =
      (((Nat.choose (3 * n) n / (2 * n + 1) : ℕ) : ℤ) : ZMod 2) := by
    rw [show ((PowerSeries.coeff n A : ℤ) : ZMod 2) = φ2 (PowerSeries.coeff n A) from rfl, hn]
    have hdiv := Nat.mod_add_div (Nat.choose (3 * n) n / (2 * n + 1)) 2
    have h2 : (2 : ZMod 2) = 0 := by decide
    have hnat : ((Nat.choose (3 * n) n / (2 * n + 1) : ℕ) : ZMod 2) =
        if isFibbin n then 1 else 0 := by
      conv_lhs => rw [← hdiv]
      rw [hfc]
      push_cast
      rw [h2, zero_mul, add_zero]
    rw [Int.cast_natCast]
    exact hnat.symm
  have hmod := (ZMod.intCast_eq_intCast_iff _ _ 2).mp hcast
  rw [Int.ModEq] at hmod
  norm_num at hmod
  exact hmod

end OMA.S_oeis_a378578

theorem OMA.solution : type_of% @OMA.S_oeis_a378578.main :=
  OMA.S_oeis_a378578.main_proved

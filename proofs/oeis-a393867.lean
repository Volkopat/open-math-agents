import OMAStatements.S_oeis_a393867

/-!
Credit: @grp06

The positive coefficients of the logarithmic derivative in OEIS A393867 are
odd, and the coefficient in degree n > 1 is divisible by the nth prime.
The prime-indexed recurrence comes from OEIS A393866. Both entries are by
Paul D. Hanna. The formal statement is credited to @wtho704.

https://oeis.org/A393867/internal
https://oeis.org/A393866/internal
-/

open PowerSeries
open OMA.S_oeis_a393867 (primeAt)

private theorem lt_primeAt {n : ℕ} (hn : 0 < n) : n < primeAt n := by
  have h := Nat.add_two_le_nth_prime (n - 1)
  unfold primeAt
  omega

private theorem coeff_prime_pow {p : ℕ} (hp : Nat.Prime p)
    (B : PowerSeries (ZMod p)) {i : ℕ} (hi : ¬ p ∣ i) :
    coeff i (B ^ p) = 0 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have h :
      PowerSeries.map (frobenius (ZMod p) p) (expand p hp.ne_zero B) = B ^ p :=
    MvPowerSeries.map_frobenius_expand p hp.ne_zero (f := B)
  rw [← h, coeff_map, coeff_expand_of_not_dvd p hp.ne_zero B hi, map_zero]

private theorem coeff_one_add_X_mul {R : Type*} [Semiring R]
    (B : PowerSeries R) (i : ℕ) :
    coeff (i + 1) ((1 + X) * B) = coeff (i + 1) B + coeff i B := by
  rw [add_mul, one_mul, map_add, coeff_succ_X_mul]

private theorem derivative_map_int (m : ℕ) (F : PowerSeries ℤ) :
    PowerSeries.map (Int.castRingHom (ZMod m)) (derivative ℤ F) =
      derivative (ZMod m) (PowerSeries.map (Int.castRingHom (ZMod m)) F) := by
  apply PowerSeries.ext
  intro i
  simp only [coeff_map, coeff_derivative, map_mul, map_add, map_natCast, map_one]

theorem OMA.solution : type_of% @OMA.S_oeis_a393867.main := by
  intro F G hF hrec hFG
  constructor
  · intro n hn
    let p := primeAt n
    have hnp : n < p := lt_primeAt (by omega)
    have hp : Nat.Prime p := Nat.prime_nth_prime (n - 1)
    have hpstep : p - 1 + 1 = p := by have := hp.pos; omega
    have hnstep : n - 1 + 1 = n := by omega
    have hpow : F ^ (p - 1) * F = F ^ p := by
      rw [← pow_succ, hpstep]
    have hseries :
        X * derivative ℤ (F ^ p) = (p : PowerSeries ℤ) * (F ^ p * G) := by
      calc
        X * derivative ℤ (F ^ p) =
            (p : PowerSeries ℤ) * F ^ (p - 1) * (X * derivative ℤ F) := by
          rw [derivative_pow]
          ac_rfl
        _ = (p : PowerSeries ℤ) * (F ^ p * G) := by
          rw [← hFG, ← hpow]
          ac_rfl
    have hC : C (p : ℤ) = (p : PowerSeries ℤ) := map_natCast C p
    rw [← hC] at hseries
    have hcoeff := congrArg (fun B : PowerSeries ℤ => coeff n B) hseries
    change coeff n (X * derivative ℤ (F ^ p)) =
      coeff n (C (p : ℤ) * (F ^ p * G)) at hcoeff
    have hx : coeff n (X * derivative ℤ (F ^ p)) = coeff n (F ^ p) * (n : ℤ) := by
      calc
        _ = coeff (n - 1) (derivative ℤ (F ^ p)) := by
          simpa only [hnstep] using coeff_succ_X_mul (n - 1) (derivative ℤ (F ^ p))
        _ = _ := by
          have hcast : ((n - 1 : ℕ) : ℤ) + 1 = (n : ℤ) := by
            exact_mod_cast hnstep
          simp only [coeff_derivative, hnstep, hcast]
    have hr : coeff n (F ^ p) = (p : ℤ) * coeff (n - 1) (F ^ p) :=
      hrec n (by omega)
    rw [hx, coeff_C_mul, hr, mul_assoc] at hcoeff
    have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have heq := mul_left_cancel₀ hpz hcoeff
    let red := PowerSeries.map (Int.castRingHom (ZMod p))
    have hs (i : ℕ) (hi : 0 < i) (hin : i ≤ n) : coeff i ((red F) ^ p) = 0 :=
      coeff_prime_pow hp (red F) (fun hd => (Nat.not_le_of_gt (lt_of_le_of_lt hin hnp))
        (Nat.le_of_dvd hi hd))
    have hc : coeff 0 ((red F) ^ p) = 1 := by
      dsimp only [red]
      rw [← map_pow, coeff_map, coeff_zero_eq_constantCoeff_apply, map_pow, hF, one_pow, map_one]
    have hconv : coeff n ((red F) ^ p * red G) = coeff n (red G) := by
      rw [coeff_mul]
      calc
        _ = coeff 0 ((red F) ^ p) * coeff n (red G) := by
          apply Finset.sum_eq_single (0, n)
          · rintro ⟨i, j⟩ hij hne
            have hij' : i + j = n :=
              (Finset.HasAntidiagonal.mem_antidiagonal (n := n) (a := (i, j))).mp hij
            have hi : 0 < i := by
              by_contra h
              have hi0 : i = 0 := by omega
              have hj : j = n := by omega
              exact hne (by subst i; subst j; rfl)
            change coeff i ((red F) ^ p) * coeff j (red G) = 0
            rw [hs i hi (by omega), zero_mul]
          · intro h
            exact (h ((Finset.HasAntidiagonal.mem_antidiagonal (n := n) (a := (0, n))).mpr
              (Nat.zero_add n))).elim
        _ = _ := by rw [hc, one_mul]
    have heq' := congrArg (Int.castRingHom (ZMod p)) heq
    change Int.castRingHom (ZMod p) (coeff (n - 1) (F ^ p) * (n : ℤ)) =
      Int.castRingHom (ZMod p) (coeff n (F ^ p * G)) at heq'
    rw [map_mul] at heq'
    change ((coeff (n - 1) (F ^ p) : ℤ) : ZMod p) * ((n : ℤ) : ZMod p) =
      ((coeff n (F ^ p * G) : ℤ) : ZMod p) at heq'
    have hz : ((coeff (n - 1) (F ^ p) : ℤ) : ZMod p) = 0 := by
      change Int.castRingHom (ZMod p) (coeff (n - 1) (F ^ p)) = 0
      simpa only [red, ← map_pow, coeff_map] using hs (n - 1) (by omega) (by omega)
    rw [hz, zero_mul] at heq'
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    change coeff n (red G) = 0
    rw [← hconv]
    dsimp only [red]
    rw [← map_pow, ← map_mul, coeff_map]
    change ((coeff n (F ^ p * G) : ℤ) : ZMod p) = 0
    exact heq'.symm
  · let r := Int.castRingHom (ZMod 2)
    let A := PowerSeries.map r F
    let B := PowerSeries.map r G
    let H : PowerSeries (ZMod 2) := (1 + X) * A
    have hA : coeff 0 A = 1 := by
      change coeff 0 (PowerSeries.map r F) = 1
      rw [coeff_map, coeff_zero_eq_constantCoeff_apply, hF, map_one]
    have hF1 : coeff 1 F = 1 := by
      have hr := hrec 1 (by omega)
      change coeff 1 (F ^ primeAt 1) =
        (primeAt 1 : ℤ) * coeff 0 (F ^ primeAt 1) at hr
      have hp1 : primeAt 1 = 2 := Nat.nth_prime_zero_eq_two
      rw [hp1, coeff_one_pow, coeff_zero_eq_constantCoeff_apply, map_pow, hF] at hr
      norm_num at hr
      omega
    have hA1 : coeff 1 A = 1 := by
      change coeff 1 (PowerSeries.map r F) = 1
      rw [coeff_map, hF1, map_one]
    have hH : ∀ n : ℕ, Odd n → coeff n H = 0 := by
      intro n
      induction n using Nat.strongRecOn with
      | ind n ih =>
        intro hn
        by_cases h1 : n = 1
        · subst n
          change coeff (0 + 1) ((1 + X) * A) = 0
          simpa only [coeff_one_add_X_mul, hA1, hA, one_add_one_eq_two] using
            (CharTwo.two_eq_zero : (2 : ZMod 2) = 0)
        have hnmod := Nat.odd_iff.mp hn
        have hnpos : 0 < n := by omega
        have hnstep : n - 1 + 1 = n := by omega
        let p := primeAt n
        have hnp : n < p := lt_primeAt hnpos
        have hp : Nat.Prime p := Nat.prime_nth_prime (n - 1)
        obtain ⟨k, hk⟩ := hp.odd_of_ne_two (by omega)
        have hcast : (p : ZMod 2) = 1 := (show Odd p from ⟨k, hk⟩).natCast_zmod_two
        have hr : coeff n (F ^ p) = (p : ℤ) * coeff (n - 1) (F ^ p) := hrec n hnpos
        have hbar : coeff n (A ^ p) = coeff (n - 1) (A ^ p) := by
          simp only [A, ← map_pow, coeff_map, hr, map_mul, map_natCast]
          change (↑p : ZMod 2) * r (coeff (n - 1) (F ^ p)) = r (coeff (n - 1) (F ^ p))
          rw [hcast, one_mul]
        have hzero : coeff n ((1 + X) * A ^ p) = 0 := by
          calc
            _ = coeff n (A ^ p) + coeff (n - 1) (A ^ p) := by
              simpa only [hnstep] using coeff_one_add_X_mul (A ^ p) (n - 1)
            _ = 0 := by
              rw [← eq_neg_iff_add_eq_zero, ZMod.neg_eq_self_mod_two]
              exact hbar
        let Q := (A ^ k) ^ 2
        have hfactor : (1 + X) * A ^ p = H * Q := by
          have hexp : p = 1 + k * 2 := by omega
          calc
            _ = (1 + X) * (A ^ 1 * A ^ (k * 2)) := by rw [← pow_add, ← hexp]
            _ = _ := by rw [pow_one, pow_mul, ← mul_assoc]
        have hQ0 : coeff 0 Q = 1 := by
          have hcA : constantCoeff A = 1 := (coeff_zero_eq_constantCoeff_apply A).symm.trans hA
          simp [Q, coeff_zero_eq_constantCoeff_apply, hcA]
        have hconv : coeff n (H * Q) = coeff n H := by
          rw [coeff_mul]
          calc
            _ = coeff n H * coeff 0 Q := by
              apply Finset.sum_eq_single (n, 0)
              · rintro ⟨i, j⟩ hij hne
                have hij' : i + j = n :=
                  (Finset.HasAntidiagonal.mem_antidiagonal (n := n) (a := (i, j))).mp hij
                have hj : 0 < j := by
                  by_contra h
                  have hj0 : j = 0 := by omega
                  have hi : i = n := by omega
                  exact hne (by subst i; subst j; rfl)
                change coeff i H * coeff j Q = 0
                by_cases hj2 : 2 ∣ j
                · obtain ⟨d, hd⟩ := hj2
                  have hiodd : Odd i := Nat.odd_iff.mpr (by omega)
                  rw [ih i (by omega) hiodd, zero_mul]
                · exact mul_eq_zero_of_right _ (coeff_prime_pow Nat.prime_two (A ^ k) hj2)
              · intro h
                exact (h ((Finset.HasAntidiagonal.mem_antidiagonal (n := n) (a := (n, 0))).mpr
                  (Nat.add_zero n))).elim
            _ = _ := by rw [hQ0, mul_one]
        rw [hfactor, hconv] at hzero
        exact hzero
    have hdH : derivative (ZMod 2) H = 0 := by
      apply PowerSeries.ext
      intro i
      simp only [coeff_derivative, map_zero]
      by_cases hi : Odd (i + 1)
      · rw [hH _ hi, zero_mul]
      · have he : Even (i + 1) := Nat.even_iff.mpr (by
          rw [Nat.odd_iff] at hi
          omega)
        have hz : ((i : ZMod 2) + 1) = 0 := by
          simpa only [Nat.cast_add, Nat.cast_one] using he.natCast_zmod_two
        rw [hz, mul_zero]
    have hdA : (1 + X) * derivative (ZMod 2) A = A := by
      change derivative (ZMod 2) ((1 + X) * A) = 0 at hdH
      rw [Derivation.leibniz] at hdH
      have hdOneX : derivative (ZMod 2) (1 + X) = 1 := by
        rw [map_add, derivative_one, derivative_X, zero_add]
      simp only [hdOneX, smul_eq_mul, mul_one] at hdH
      apply PowerSeries.ext
      intro i
      have hi := congrArg (fun S : PowerSeries (ZMod 2) => coeff i S) hdH
      change coeff i ((1 + X) * derivative (ZMod 2) A + A) = coeff i 0 at hi
      rw [map_add, map_zero, ← eq_neg_iff_add_eq_zero, ZMod.neg_eq_self_mod_two] at hi
      exact hi
    have hAB : A * B = X * derivative (ZMod 2) A := by
      have hm := congrArg (PowerSeries.map r) hFG
      simpa only [A, B, r, map_mul, map_X, derivative_map_int] using hm
    have hAne : A ≠ 0 := by
      intro he
      rw [he, map_zero] at hA
      exact zero_ne_one hA
    have hB : (1 + X) * B = X := by
      apply mul_left_cancel₀ hAne
      calc
        A * ((1 + X) * B) = (1 + X) * (A * B) := by ac_rfl
        _ = X * ((1 + X) * derivative (ZMod 2) A) := by rw [hAB]; ac_rfl
        _ = A * X := by rw [hdA, mul_comm]
    have hB1 : coeff 1 B = 1 := by
      have hB0 : coeff 0 B = 0 := by
        have hc := congrArg (fun S : PowerSeries (ZMod 2) => coeff 0 S) hB
        simpa [add_mul, coeff_zero_X_mul, coeff_zero_X] using hc
      have hc := congrArg (fun S : PowerSeries (ZMod 2) => coeff 1 S) hB
      change coeff (0 + 1) ((1 + X) * B) = coeff 1 X at hc
      rwa [coeff_one_add_X_mul, hB0, add_zero, coeff_one_X] at hc
    have hBpos (i : ℕ) : coeff (i + 1) B = 1 := by
      induction i with
      | zero => exact hB1
      | succ i ih =>
        have hc := congrArg (fun S : PowerSeries (ZMod 2) => coeff (i + 1 + 1) S) hB
        change coeff (i + 1 + 1) ((1 + X) * B) = coeff (i + 1 + 1) X at hc
        rw [coeff_one_add_X_mul, ih, coeff_X, if_neg (show i + 1 + 1 ≠ 1 by omega),
          ← eq_neg_iff_add_eq_zero, ZMod.neg_eq_self_mod_two] at hc
        exact hc
    intro n hn
    apply ZMod.intCast_eq_one_iff_odd.mp
    change coeff n B = 1
    simpa only [show n - 1 + 1 = n by omega] using hBpos (n - 1)

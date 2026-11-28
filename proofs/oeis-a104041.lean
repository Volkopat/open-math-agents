import OMAStatements.S_oeis_a104041

namespace OMA.P_oeis_a104041

open OMA.S_oeis_a104041

/-! ### Part 1: Falling factorials, Stirling identities, and polynomial representation of `balaT` -/

private noncomputable def fallingPoly (p : Polynomial ℤ) : ℕ → Polynomial ℤ
  | 0 => 1
  | n + 1 => fallingPoly p n * (p - Polynomial.C (n : ℤ))

private lemma stirling1_gt (n k : ℕ) (h : n < k) : stirling1 n k = 0 := by
  induction n generalizing k with
  | zero => cases k with | zero => omega | succ _ => rfl
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k' =>
      simp only [stirling1, ih k' (by omega), ih (k' + 1) (by omega), mul_zero, sub_zero]

private lemma stirling2_gt (n k : ℕ) (h : n < k) : stirling2 n k = 0 := by
  induction n generalizing k with
  | zero => cases k with | zero => omega | succ _ => rfl
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k' =>
      simp only [stirling2, ih (k' + 1) (by omega), ih k' (by omega), mul_zero, add_zero]

private lemma fallingPoly_X_eq_sum_stirling1 (n : ℕ) :
    fallingPoly Polynomial.X n =
      ∑ j ∈ Finset.range (n + 1), Polynomial.C (stirling1 n j) * Polynomial.X ^ j := by
  induction n with
  | zero => simp [fallingPoly, stirling1]
  | succ n ih =>
    simp only [fallingPoly, ih]
    rw [Finset.sum_mul]
    conv_rhs => rw [Finset.sum_range_succ']
    have hs0 : stirling1 (n + 1) 0 = 0 := rfl
    rw [hs0, map_zero, zero_mul, add_zero]
    have h1 : (∑ j ∈ Finset.range (n + 1),
        Polynomial.C (stirling1 n j) * Polynomial.X ^ j * (Polynomial.X - Polynomial.C (n : ℤ))) =
        (∑ j ∈ Finset.range (n + 1), Polynomial.C (stirling1 n j) * Polynomial.X ^ (j + 1)) -
        (∑ j ∈ Finset.range (n + 1), Polynomial.C ((n : ℤ) * stirling1 n j) * Polynomial.X ^ j) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_mul]; ring
    rw [h1]
    have hshift : ∑ j ∈ Finset.range (n + 1), Polynomial.C ((n : ℤ) * stirling1 n j) * Polynomial.X ^ j =
        ∑ j ∈ Finset.range (n + 1), Polynomial.C ((n : ℤ) * stirling1 n (j + 1)) * Polynomial.X ^ (j + 1) := by
      cases n with
      | zero => simp [stirling1]
      | succ n' =>
        conv_lhs => rw [Finset.sum_range_succ']
        conv_rhs => rw [Finset.sum_range_succ]
        have h0 : stirling1 (n' + 1) 0 = 0 := rfl
        have ht : stirling1 (n' + 1) (n' + 1 + 1) = 0 := stirling1_gt _ _ (by omega)
        simp only [h0, ht, mul_zero, map_zero, zero_mul, add_zero]
    rw [hshift, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [stirling1, map_sub]
    ring

private lemma pow_eq_sum_stirling2_falling (p : Polynomial ℤ) (n : ℕ) :
    p ^ n = ∑ i ∈ Finset.range (n + 1), Polynomial.C (stirling2 n i) * fallingPoly p i := by
  induction n with
  | zero => simp [stirling2, fallingPoly]
  | succ n ih =>
    rw [pow_succ, ih, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_range_succ']
    have hs0 : stirling2 (n + 1) 0 = 0 := rfl
    rw [hs0, map_zero, zero_mul, add_zero]
    have h1 : (∑ i ∈ Finset.range (n + 1), Polynomial.C (stirling2 n i) * fallingPoly p i * p) =
        (∑ i ∈ Finset.range (n + 1), Polynomial.C (stirling2 n i) * fallingPoly p (i + 1)) +
        (∑ i ∈ Finset.range (n + 1),
          Polynomial.C (((i : ℕ) : ℤ) * stirling2 n i) * fallingPoly p i) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [fallingPoly, map_mul]
      ring
    rw [h1]
    have hshift : ∑ i ∈ Finset.range (n + 1),
          Polynomial.C (((i : ℕ) : ℤ) * stirling2 n i) * fallingPoly p i =
        ∑ i ∈ Finset.range (n + 1),
          Polynomial.C (((i + 1 : ℕ) : ℤ) * stirling2 n (i + 1)) * fallingPoly p (i + 1) := by
      conv_lhs => rw [Finset.sum_range_succ']
      conv_rhs => rw [Finset.sum_range_succ]
      have ht : stirling2 n (n + 1) = 0 := stirling2_gt n (n + 1) (by omega)
      simp only [Nat.cast_zero, zero_mul, map_zero, add_zero, ht, mul_zero]
    rw [hshift, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [stirling2, map_add]
    ring

private lemma fallingPoly_X_add_two (i : ℕ) :
    fallingPoly Polynomial.X (i + 2) =
      Polynomial.X * (Polynomial.X - 1) * fallingPoly (Polynomial.X - Polynomial.C 2) i := by
  induction i with
  | zero =>
    simp [fallingPoly]
  | succ i ih =>
    have h1 : fallingPoly Polynomial.X (i + 1 + 2) =
        fallingPoly Polynomial.X (i + 2) * (Polynomial.X - Polynomial.C ((i + 2 : ℕ) : ℤ)) := rfl
    rw [h1, ih]
    simp only [fallingPoly]
    have hc : Polynomial.C ((i + 2 : ℕ) : ℤ) = Polynomial.C 2 + Polynomial.C (i : ℤ) := by
      rw [← map_add]; congr 1; push_cast; ring
    rw [hc]
    ring

/-- Key polynomial generating function for rows of `balaT`:
- `rowPoly (2n) = X^n * (X - 2)^n`
- `rowPoly (2n + 1) = X^n * (X - 1) * (X - 2)^n`. -/
private noncomputable def rowPoly (r : ℕ) : Polynomial ℤ :=
  if r % 2 = 0 then
    Polynomial.X ^ (r / 2) * (Polynomial.X - Polynomial.C 2) ^ (r / 2)
  else
    Polynomial.X ^ (r / 2) * (Polynomial.X - 1) * (Polynomial.X - Polynomial.C 2) ^ (r / 2)

private lemma coeff_rowPoly_even (n k : ℕ) :
    (rowPoly (2 * n)).coeff k = balaT (2 * n) k := by
  unfold rowPoly balaT
  rw [if_pos (by omega : (2 * n) % 2 = 0), if_pos (by omega : (2 * n) % 2 = 0)]
  rw [show (2 * n) / 2 = n by omega]
  have hbin : (Polynomial.X - Polynomial.C (2 : ℤ)) ^ n =
      ∑ j ∈ Finset.range (n + 1),
        Polynomial.C (((Nat.choose n j : ℕ) : ℤ) * (-2 : ℤ) ^ (n - j)) * Polynomial.X ^ j := by
    have h := add_pow Polynomial.X (Polynomial.C (-2 : ℤ)) n
    have hsub : Polynomial.X - Polynomial.C (2 : ℤ) = Polynomial.X + Polynomial.C (-2 : ℤ) := by
      rw [map_neg]; ring
    rw [hsub, h]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← map_pow, map_mul, map_natCast]
    ring
  rw [hbin, Finset.mul_sum, Polynomial.finsetSum_coeff]
  by_cases hk : n ≤ k ∧ k ≤ 2 * n
  · rw [if_pos hk, Finset.sum_eq_single (k - n)]
    · have hpow : Polynomial.X ^ n * (Polynomial.C (((Nat.choose n (k - n) : ℕ) : ℤ) * (-2 : ℤ) ^ (n - (k - n))) * Polynomial.X ^ (k - n)) =
          Polynomial.C (((Nat.choose n (k - n) : ℕ) : ℤ) * (-2 : ℤ) ^ (2 * n - k)) * Polynomial.X ^ k := by
        rw [show n - (k - n) = 2 * n - k by omega]
        calc
          _ = Polynomial.C (((Nat.choose n (k - n) : ℕ) : ℤ) * (-2 : ℤ) ^ (2 * n - k)) *
                (Polynomial.X ^ n * Polynomial.X ^ (k - n)) := by ring
          _ = _ := by rw [← pow_add, show n + (k - n) = k by omega]
      rw [hpow, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_self, mul_one]
    · intro j hj hjne
      have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hpow : Polynomial.X ^ n * (Polynomial.C (((Nat.choose n j : ℕ) : ℤ) * (-2 : ℤ) ^ (n - j)) * Polynomial.X ^ j) =
          Polynomial.C (((Nat.choose n j : ℕ) : ℤ) * (-2 : ℤ) ^ (n - j)) * Polynomial.X ^ (n + j) := by
        rw [mul_left_comm, ← pow_add]
      rw [hpow, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
    · intro h; exfalso; exact h (Finset.mem_range.mpr (by omega))
  · rw [if_neg hk]
    refine Finset.sum_eq_zero (fun j hj => ?_)
    have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hpow : Polynomial.X ^ n * (Polynomial.C (((Nat.choose n j : ℕ) : ℤ) * (-2 : ℤ) ^ (n - j)) * Polynomial.X ^ j) =
        Polynomial.C (((Nat.choose n j : ℕ) : ℤ) * (-2 : ℤ) ^ (n - j)) * Polynomial.X ^ (n + j) := by
      rw [mul_left_comm, ← pow_add]
    rw [hpow, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]

private lemma coeff_rowPoly_odd (n k : ℕ) :
    (rowPoly (2 * n + 1)).coeff k = balaT (2 * n + 1) k := by
  unfold rowPoly balaT
  rw [if_neg (by omega : ¬ (2 * n + 1) % 2 = 0), if_neg (by omega : ¬ (2 * n + 1) % 2 = 0)]
  rw [show (2 * n + 1) / 2 = n by omega]
  have hstirl : (Polynomial.X * (Polynomial.X - 1) * (Polynomial.X - Polynomial.C (2 : ℤ)) ^ n : Polynomial ℤ) =
      ∑ i ∈ Finset.range (n + 1), Polynomial.C (stirling2 n i) * fallingPoly Polynomial.X (i + 2) := by
    rw [pow_eq_sum_stirling2_falling (Polynomial.X - Polynomial.C 2) n, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [fallingPoly_X_add_two i]; ring
  have hcoeff_main : ∀ j : ℕ,
      ((Polynomial.X * (Polynomial.X - 1) * (Polynomial.X - Polynomial.C (2 : ℤ)) ^ n : Polynomial ℤ)).coeff j =
        ∑ i ∈ Finset.range (n + 1), stirling2 n i * stirling1 (i + 2) j := by
    intro j
    rw [hstirl, Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Polynomial.coeff_C_mul, fallingPoly_X_eq_sum_stirling1 (i + 2), Polynomial.finsetSum_coeff]
    congr 1
    by_cases hj : j ≤ i + 2
    · rw [Finset.sum_eq_single j]
      · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_self, mul_one]
      · intro r _ hrne
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hrne.symm, mul_zero]
      · intro h; exfalso; exact h (Finset.mem_range.mpr (by omega))
    · rw [stirling1_gt (i + 2) j (by omega)]
      refine Finset.sum_eq_zero (fun r hr => ?_)
      have hrle : r ≤ i + 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
  have hshift : (Polynomial.X ^ n * (Polynomial.X - 1) * (Polynomial.X - Polynomial.C (2 : ℤ)) ^ n * Polynomial.X : Polynomial ℤ) =
      Polynomial.X ^ n * (Polynomial.X * (Polynomial.X - 1) * (Polynomial.X - Polynomial.C (2 : ℤ)) ^ n) := by
    ring
  have hcoeff_shift : ((Polynomial.X ^ n * (Polynomial.X - 1) * (Polynomial.X - Polynomial.C (2 : ℤ)) ^ n : Polynomial ℤ)).coeff k =
      ((Polynomial.X ^ n * (Polynomial.X * (Polynomial.X - 1) * (Polynomial.X - Polynomial.C (2 : ℤ)) ^ n) : Polynomial ℤ)).coeff (k + 1) := by
    rw [← hshift, mul_comm _ Polynomial.X, Polynomial.coeff_X_mul]
  rw [hcoeff_shift, Polynomial.coeff_X_pow_mul']
  by_cases hk : n ≤ k ∧ k ≤ 2 * n + 1
  · rw [if_pos hk, if_pos (by omega : n ≤ k + 1), hcoeff_main (k + 1 - n)]
  · rw [if_neg hk]
    by_cases hkn : n ≤ k + 1
    · rw [if_pos hkn, hcoeff_main (k + 1 - n)]
      by_cases hlow : k < n
      · have hkeq : k + 1 - n = 0 := by omega
        rw [hkeq]
        refine Finset.sum_eq_zero (fun i _ => ?_)
        have hs0 : stirling1 (i + 2) 0 = 0 := rfl
        rw [hs0, mul_zero]
      · refine Finset.sum_eq_zero (fun i hi => ?_)
        have hile : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [stirling1_gt (i + 2) (k + 1 - n) (by omega), mul_zero]
    · rw [if_neg hkn]

private lemma coeff_rowPoly (r k : ℕ) : (rowPoly r).coeff k = balaT r k := by
  rcases Nat.even_or_odd' r with ⟨n, rfl | rfl⟩
  · exact coeff_rowPoly_even n k
  · exact coeff_rowPoly_odd n k

private lemma balaT_diag (r : ℕ) : balaT r r = 1 := by
  rcases Nat.even_or_odd' r with ⟨n, rfl | rfl⟩
  · unfold balaT
    rw [if_pos (by omega), show (2 * n) / 2 = n by omega, if_pos (by omega)]
    simp [show 2 * n - n = n by omega, Nat.choose_self]
  · rw [← coeff_rowPoly_odd]
    unfold rowPoly
    rw [if_neg (by omega), show (2 * n + 1) / 2 = n by omega]
    have hmonic : (Polynomial.X ^ n * (Polynomial.X - 1) * (Polynomial.X - Polynomial.C (2 : ℤ)) ^ n).Monic := by
      refine Polynomial.Monic.mul (Polynomial.Monic.mul (Polynomial.monic_X_pow n) (Polynomial.monic_X_sub_C 1))
        (Polynomial.Monic.pow (Polynomial.monic_X_sub_C 2) n)
    have hdeg : (Polynomial.X ^ n * (Polynomial.X - 1) * (Polynomial.X - Polynomial.C (2 : ℤ)) ^ n).natDegree =
        2 * n + 1 := by
      have h1 : (Polynomial.X - 1 : Polynomial ℤ).Monic := Polynomial.monic_X_sub_C 1
      have h2 : ((Polynomial.X - Polynomial.C (2 : ℤ)) ^ n).Monic :=
        Polynomial.Monic.pow (Polynomial.monic_X_sub_C 2) n
      rw [Polynomial.natDegree_mul (Polynomial.Monic.mul (Polynomial.monic_X_pow n) h1).ne_zero h2.ne_zero,
        Polynomial.natDegree_mul (Polynomial.monic_X_pow n).ne_zero h1.ne_zero,
        Polynomial.natDegree_X_pow, show (1 : Polynomial ℤ) = Polynomial.C 1 from rfl,
        Polynomial.natDegree_X_sub_C, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
      omega
    rw [← hdeg]
    exact hmonic.leadingCoeff

private lemma balaT_of_lt (r k : ℕ) (h : r < k) : balaT r k = 0 := by
  simp only [balaT]
  split_ifs <;> first | rfl | omega

private lemma balaT_of_gt (r k : ℕ) (h : 2 * k + 1 < r) : balaT r k = 0 := by
  simp only [balaT]
  split_ifs <;> first | rfl | omega

private lemma balaT_sign (r k : ℕ) (hk : k ≤ r) : 0 ≤ (-1 : ℤ) ^ (r - k) * balaT r k := by
  rw [← coeff_rowPoly r k]
  rcases Nat.even_or_odd' r with ⟨n, rfl | rfl⟩
  · by_cases hkn : n ≤ k
    · rw [coeff_rowPoly_even]
      unfold balaT
      rw [if_pos (by omega), show (2 * n) / 2 = n by omega, if_pos ⟨hkn, hk⟩]
      have hpow : (-1 : ℤ) ^ (2 * n - k) * (-2 : ℤ) ^ (2 * n - k) = (2 : ℤ) ^ (2 * n - k) := by
        rw [← mul_pow]; norm_num
      calc
        0 ≤ ((Nat.choose n (k - n) : ℕ) : ℤ) * (2 : ℤ) ^ (2 * n - k) := by positivity
        _ = (-1 : ℤ) ^ (2 * n - k) * (((Nat.choose n (k - n) : ℕ) : ℤ) * (-2 : ℤ) ^ (2 * n - k)) := by
              rw [← hpow]; ring
    · rw [coeff_rowPoly_even]
      unfold balaT
      rw [if_pos (by omega), show (2 * n) / 2 = n by omega, if_neg (by omega), mul_zero]
  · -- For odd row r = 2n + 1: X^n * (X - 1) * (X - 2)^n = X^n * X * (X - 2)^n - X^n * (X - 2)^n
    have hsplit : rowPoly (2 * n + 1) = Polynomial.X * rowPoly (2 * n) - rowPoly (2 * n) := by
      unfold rowPoly
      rw [if_neg (by omega), if_pos (by omega), show (2 * n + 1) / 2 = n by omega,
        show (2 * n) / 2 = n by omega]
      ring
    rw [hsplit, Polynomial.coeff_sub, coeff_rowPoly_even]
    have h1 : (Polynomial.X * rowPoly (2 * n)).coeff k =
        if k = 0 then 0 else balaT (2 * n) (k - 1) := by
      cases k with
      | zero => simp
      | succ k' => simp [Polynomial.coeff_X_mul, coeff_rowPoly_even]
    rw [h1]
    have hpos1 : 0 ≤ (-1 : ℤ) ^ (2 * n + 1 - k) * (if k = 0 then 0 else balaT (2 * n) (k - 1)) := by
      by_cases hk0 : k = 0
      · simp [hk0]
      · rw [if_neg hk0]
        by_cases hkn : n ≤ k - 1
        · unfold balaT
          rw [if_pos (by omega), show (2 * n) / 2 = n by omega, if_pos (by omega)]
          have hexp : 2 * n + 1 - k = 2 * n - (k - 1) := by omega
          rw [hexp]
          have hpow : (-1 : ℤ) ^ (2 * n - (k - 1)) * (-2 : ℤ) ^ (2 * n - (k - 1)) = (2 : ℤ) ^ (2 * n - (k - 1)) := by
            rw [← mul_pow]; norm_num
          calc
            0 ≤ ((Nat.choose n (k - 1 - n) : ℕ) : ℤ) * (2 : ℤ) ^ (2 * n - (k - 1)) := by positivity
            _ = _ := by rw [← hpow]; ring
        · unfold balaT
          rw [if_pos (by omega), show (2 * n) / 2 = n by omega, if_neg (by omega), mul_zero]
    have hpos2 : 0 ≤ (-1 : ℤ) ^ (2 * n + 1 - k) * (-balaT (2 * n) k) := by
      by_cases hkn : n ≤ k ∧ k ≤ 2 * n
      · unfold balaT
        rw [if_pos (by omega), show (2 * n) / 2 = n by omega, if_pos hkn]
        have hexp : 2 * n + 1 - k = (2 * n - k) + 1 := by omega
        rw [hexp, pow_succ]
        have hpow : (-1 : ℤ) ^ (2 * n - k) * (-2 : ℤ) ^ (2 * n - k) = (2 : ℤ) ^ (2 * n - k) := by
          rw [← mul_pow]; norm_num
        calc
          0 ≤ ((Nat.choose n (k - n) : ℕ) : ℤ) * (2 : ℤ) ^ (2 * n - k) := by positivity
          _ = _ := by rw [← hpow]; ring
      · unfold balaT
        rw [if_pos (by omega), show (2 * n) / 2 = n by omega, if_neg hkn]; simp
    linarith [mul_sub ((-1 : ℤ) ^ (2 * n + 1 - k)) (if k = 0 then 0 else balaT (2 * n) (k - 1)) (balaT (2 * n) k)]

/-! ### Part 2: Exact matrix inverse `balaT * invFromCols balaT = I` via `PowerSeries ℤ` -/

private lemma coeff_mul_eq_sum_range (f g : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n (f * g) =
      ∑ i ∈ Finset.range (n + 1), PowerSeries.coeff i f * PowerSeries.coeff (n - i) g := by
  rw [PowerSeries.coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i f * PowerSeries.coeff j g) n

private lemma coeff_X_mul_zero (f : PowerSeries ℤ) :
    PowerSeries.coeff 0 (PowerSeries.X * f) = 0 := by
  rw [coeff_mul_eq_sum_range]; simp

private lemma coeff_X_mul_succ (f : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff (n + 1) (PowerSeries.X * f) = PowerSeries.coeff n f := by
  rw [coeff_mul_eq_sum_range, Finset.sum_eq_single 1]
  · simp
  · intro b _ hb; rw [PowerSeries.coeff_X, if_neg hb, zero_mul]
  · intro h; exfalso; exact h (Finset.mem_range.mpr (by omega))

private lemma coeff_X_pow_mul (f : PowerSeries ℤ) (k n : ℕ) :
    PowerSeries.coeff n (PowerSeries.X ^ k * f) =
      if k ≤ n then PowerSeries.coeff (n - k) f else 0 := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc]
    cases n with
    | zero => rw [coeff_X_mul_zero, if_neg (by omega)]
    | succ m =>
      rw [coeff_X_mul_succ, ih m]
      by_cases h : k ≤ m
      · rw [if_pos h, if_pos (by omega), show m + 1 - (k + 1) = m - k by omega]
      · rw [if_neg h, if_neg (by omega)]

/-- Formal power series `inv1m2X = (1 - 2*X)⁻¹ = ∑ 2^n X^n` in `PowerSeries ℤ`. -/
private noncomputable def inv1m2X : PowerSeries ℤ :=
  PowerSeries.mk (fun n => (2 : ℤ) ^ n)

private lemma mul_inv1m2X : (1 - PowerSeries.C 2 * PowerSeries.X) * inv1m2X = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul]
  cases n with
  | zero =>
    rw [coeff_X_mul_zero, mul_zero, sub_zero, PowerSeries.coeff_one, if_pos rfl]
    simp [inv1m2X]
  | succ m =>
    rw [coeff_X_mul_succ, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero m)]
    simp only [inv1m2X, PowerSeries.coeff_mk, pow_succ']
    ring

private lemma coeff_inv1m2X_pow (j n : ℕ) :
    PowerSeries.coeff n (inv1m2X ^ (j + 1)) = ((Nat.choose (n + j) j : ℕ) : ℤ) * (2 : ℤ) ^ n := by
  induction j generalizing n with
  | zero =>
    simp [inv1m2X]
  | succ j ih =>
    rw [pow_succ, coeff_mul_eq_sum_range]
    simp_rw [ih, inv1m2X, PowerSeries.coeff_mk]
    have hpow : ∀ i ∈ Finset.range (n + 1),
        ((Nat.choose (i + j) j : ℕ) : ℤ) * (2 : ℤ) ^ i * (2 : ℤ) ^ (n - i) =
          ((Nat.choose (i + j) j : ℕ) : ℤ) * (2 : ℤ) ^ n := by
      intro i hi
      have hile : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [mul_assoc, ← pow_add, show i + (n - i) = n by omega]
    rw [Finset.sum_congr rfl hpow, ← Finset.sum_mul]
    congr 1
    -- Hockey-stick identity: ∑_{i=0}^n C(i + j, j) = C(n + j + 1, j + 1)
    have hh : ∀ m : ℕ, ∑ i ∈ Finset.range (m + 1), Nat.choose (i + j) j = Nat.choose (m + (j + 1)) (j + 1) := by
      intro m; induction m with
      | zero => simp
      | succ m ihm =>
        rw [Finset.sum_range_succ, ihm, show m + 1 + (j + 1) = (m + (j + 1)) + 1 by omega,
          Nat.choose_succ_succ, show m + (j + 1) = m + 1 + j by omega, add_comm]
    exact_mod_cast hh n

/-- Column generating function `colGF c` of `invFromCols balaT`:
- `colGF (2j) = X^(2j) * (1 - X) * inv1m2X^(j + 1)`
- `colGF (2j + 1) = X^(2j + 1) * inv1m2X^(j + 1)`. -/
private noncomputable def colGF (c : ℕ) : PowerSeries ℤ :=
  if c % 2 = 0 then
    PowerSeries.X ^ c * (1 - PowerSeries.X) * inv1m2X ^ (c / 2 + 1)
  else
    PowerSeries.X ^ c * inv1m2X ^ (c / 2 + 1)

private lemma coeff_colGF (c m : ℕ) :
    PowerSeries.coeff m (colGF c) = invFromCols balaT m c := by
  have habs : ∀ r k : ℕ, k ≤ r → |balaT r k| = (-1 : ℤ) ^ (r - k) * balaT r k := by
    intro r k hk
    have hnn := balaT_sign r k hk
    have hsq : ((-1 : ℤ) ^ (r - k)) * ((-1 : ℤ) ^ (r - k)) = 1 := by
      rw [← mul_pow]; norm_num
    have h1 : |(-1 : ℤ) ^ (r - k) * balaT r k| = |balaT r k| := by
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    rw [← h1, abs_of_nonneg hnn]
  unfold colGF invFromCols
  by_cases hcm : c ≤ m
  · rw [if_pos hcm]
    rcases Nat.even_or_odd' c with ⟨j, rfl | rfl⟩
    · rw [if_pos (by omega : (2 * j) % 2 = 0), show (2 * j) / 2 = j by omega]
      rw [mul_assoc, coeff_X_pow_mul, if_pos hcm]
      cases m with
      | zero =>
        have hj0 : j = 0 := by omega
        subst hj0
        simp [inv1m2X]
      | succ m' =>
        rw [if_neg (Nat.succ_ne_zero m')]
        rw [sub_mul, one_mul, map_sub, coeff_inv1m2X_pow]
        have hodd_row : 2 * (m' + 1) - 1 - 2 * j = 2 * (m' - j) + 1 := by omega
        rw [hodd_row, Nat.add_sub_cancel, habs (2 * (m' - j) + 1) m' (by omega)]
        by_cases hsub0 : m' + 1 - 2 * j = 0
        · rw [hsub0, coeff_X_mul_zero, zero_add, Nat.choose_self, Nat.cast_one, pow_zero,
            mul_one, sub_zero, show 2 * (m' - j) + 1 = m' by omega, Nat.sub_self, pow_zero,
            one_mul, balaT_diag]
        · have hsplit : rowPoly (2 * (m' - j) + 1) =
              Polynomial.X * rowPoly (2 * (m' - j)) - rowPoly (2 * (m' - j)) := by
            unfold rowPoly
            rw [if_neg (by omega), if_pos (by omega), show (2 * (m' - j) + 1) / 2 = m' - j by omega,
              show (2 * (m' - j)) / 2 = m' - j by omega]
            ring
          rw [← coeff_rowPoly_odd, hsplit, Polynomial.coeff_sub, coeff_rowPoly_even]
          have hX : (Polynomial.X * rowPoly (2 * (m' - j))).coeff m' =
              if m' = 0 then 0 else balaT (2 * (m' - j)) (m' - 1) := by
            cases m' with
            | zero => simp
            | succ m'' => simp [Polynomial.coeff_X_mul, coeff_rowPoly_even]
          rw [hX]
          obtain ⟨d, hd⟩ : ∃ d, m' + 1 - 2 * j = d + 1 := ⟨m' - 2 * j, by omega⟩
          rw [hd, coeff_X_mul_succ, coeff_inv1m2X_pow]
          have hev_m : balaT (2 * (m' - j)) m' =
              ((Nat.choose (m' - j) j : ℕ) : ℤ) * (-2 : ℤ) ^ (m' - 2 * j) := by
            unfold balaT
            rw [if_pos (by omega), show (2 * (m' - j)) / 2 = m' - j by omega]
            by_cases hle : m' ≤ 2 * (m' - j)
            · rw [if_pos (by omega), show m' - (m' - j) = j by omega,
                show 2 * (m' - j) - m' = m' - 2 * j by omega]
            · rw [if_neg (by omega)]
              have hgt : m' - j < j := by omega
              rw [Nat.choose_eq_zero_of_lt hgt]; simp
          have hev_m1 : (if m' = 0 then 0 else balaT (2 * (m' - j)) (m' - 1)) =
              if j = 0 then 0 else ((Nat.choose (m' - j) (j - 1) : ℕ) : ℤ) * (-2 : ℤ) ^ (m' + 1 - 2 * j) := by
            by_cases hj0 : j = 0
            · subst hj0
              rw [if_pos rfl]
              by_cases hm0 : m' = 0
              · rw [if_pos hm0]
              · rw [if_neg hm0]
                unfold balaT
                rw [if_pos (by omega), show (2 * (m' - 0)) / 2 = m' by omega, if_neg (by omega)]
            · rw [if_neg hj0, if_neg (by omega : m' ≠ 0)]
              unfold balaT
              rw [if_pos (by omega), show (2 * (m' - j)) / 2 = m' - j by omega]
              by_cases hle : m' - 1 ≤ 2 * (m' - j)
              · rw [if_pos (by omega), show m' - 1 - (m' - j) = j - 1 by omega,
                  show 2 * (m' - j) - (m' - 1) = m' + 1 - 2 * j by omega]
              · rw [if_neg (by omega)]
                have hgt : m' - j < j - 1 := by omega
                rw [Nat.choose_eq_zero_of_lt hgt]; simp
          rw [hev_m, hev_m1]
          have hsub_d : d = m' - 2 * j := by omega
          rw [hsub_d]
          have hexp_all : 2 * (m' - j) + 1 - m' = m' + 1 - 2 * j := by omega
          rw [hexp_all]
          by_cases hj0 : j = 0
          · subst hj0
            simp only [ite_true, zero_sub, Nat.choose_zero_right, Nat.cast_one, one_mul, mul_neg]
            have hpow1 : (-1 : ℤ) ^ (m' + 1) * (-2 : ℤ) ^ m' = -((2 : ℤ) ^ m') := by
              rw [pow_succ']
              have h1 : (-1 : ℤ) ^ m' * (-2 : ℤ) ^ m' = (2 : ℤ) ^ m' := by rw [← mul_pow]; norm_num
              linarith
            have hpow2 : (2 : ℤ) ^ (m' + 1) = 2 * (2 : ℤ) ^ m' := by rw [pow_succ']
            simp only [Nat.mul_zero, Nat.sub_zero]
            linarith
          · rw [if_neg hj0]
            have hpas : Nat.choose (m' - 2 * j + 1 + j) j =
                Nat.choose (m' - 2 * j + j) j + Nat.choose (m' - 2 * j + j) (j - 1) := by
              obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
              rw [show m' - 2 * (j' + 1) + 1 + (j' + 1) = (m' - 2 * (j' + 1) + (j' + 1)) + 1 by omega,
                Nat.choose_succ_succ, Nat.add_sub_cancel, add_comm]
            have hidx1 : m' - 2 * j + j = m' - j := by omega
            rw [hidx1] at hpas
            have hpas_z : ((Nat.choose (m' - 2 * j + 1 + j) j : ℕ) : ℤ) =
                ((Nat.choose (m' - j) j : ℕ) : ℤ) + ((Nat.choose (m' - j) (j - 1) : ℕ) : ℤ) := by
              exact_mod_cast hpas
            rw [hidx1, hpas_z]
            have h2pow : (2 : ℤ) ^ (m' - 2 * j + 1) = 2 * (2 : ℤ) ^ (m' - 2 * j) := by rw [pow_succ']
            have hm1_eq : m' + 1 - 2 * j = m' - 2 * j + 1 := by omega
            rw [hm1_eq, h2pow]
            have hpA : (-1 : ℤ) ^ (m' - 2 * j + 1) * (-2 : ℤ) ^ (m' - 2 * j + 1) =
                2 * (2 : ℤ) ^ (m' - 2 * j) := by
              rw [← mul_pow]; norm_num; rw [pow_succ']
            have hpB : (-1 : ℤ) ^ (m' - 2 * j + 1) * (-2 : ℤ) ^ (m' - 2 * j) =
                -((2 : ℤ) ^ (m' - 2 * j)) := by
              rw [pow_succ']
              have h1 : (-1 : ℤ) ^ (m' - 2 * j) * (-2 : ℤ) ^ (m' - 2 * j) = (2 : ℤ) ^ (m' - 2 * j) := by
                rw [← mul_pow]; norm_num
              linarith
            calc
              (((Nat.choose (m' - j) j : ℕ) : ℤ) + ((Nat.choose (m' - j) (j - 1) : ℕ) : ℤ)) *
                    (2 * (2 : ℤ) ^ (m' - 2 * j)) -
                  ((Nat.choose (m' - j) j : ℕ) : ℤ) * (2 : ℤ) ^ (m' - 2 * j)
                = ((Nat.choose (m' - j) (j - 1) : ℕ) : ℤ) * (2 * (2 : ℤ) ^ (m' - 2 * j)) -
                    ((Nat.choose (m' - j) j : ℕ) : ℤ) * (-((2 : ℤ) ^ (m' - 2 * j))) := by ring
              _ = ((Nat.choose (m' - j) (j - 1) : ℕ) : ℤ) *
                      ((-1 : ℤ) ^ (m' - 2 * j + 1) * (-2 : ℤ) ^ (m' - 2 * j + 1)) -
                    ((Nat.choose (m' - j) j : ℕ) : ℤ) *
                      ((-1 : ℤ) ^ (m' - 2 * j + 1) * (-2 : ℤ) ^ (m' - 2 * j)) := by rw [hpA, hpB]
              _ = (-1 : ℤ) ^ (m' - 2 * j + 1) *
                    (((Nat.choose (m' - j) (j - 1) : ℕ) : ℤ) * (-2 : ℤ) ^ (m' - 2 * j + 1) -
                      ((Nat.choose (m' - j) j : ℕ) : ℤ) * (-2 : ℤ) ^ (m' - 2 * j)) := by ring
    · -- c = 2*j + 1 (odd)
      rw [if_neg (by omega : ¬ (2 * j + 1) % 2 = 0), show (2 * j + 1) / 2 = j by omega]
      rw [coeff_X_pow_mul, if_pos hcm, coeff_inv1m2X_pow, if_neg (by omega : m ≠ 0)]
      have heven_row : 2 * m - 1 - (2 * j + 1) = 2 * (m - 1 - j) := by omega
      rw [heven_row, habs (2 * (m - 1 - j)) (m - 1) (by omega)]
      unfold balaT
      rw [if_pos (by omega), show (2 * (m - 1 - j)) / 2 = m - 1 - j by omega, if_pos (by omega)]
      have hidx1 : m - (2 * j + 1) + j = m - 1 - j := by omega
      have hidx2 : m - 1 - (m - 1 - j) = j := by omega
      have hidx3 : 2 * (m - 1 - j) - (m - 1) = m - (2 * j + 1) := by omega
      rw [hidx1, hidx2, hidx3]
      have hpow : (-1 : ℤ) ^ (m - (2 * j + 1)) * (-2 : ℤ) ^ (m - (2 * j + 1)) = (2 : ℤ) ^ (m - (2 * j + 1)) := by
        rw [← mul_pow]; norm_num
      calc
        ((Nat.choose (m - 1 - j) j : ℕ) : ℤ) * (2 : ℤ) ^ (m - (2 * j + 1))
          = ((Nat.choose (m - 1 - j) j : ℕ) : ℤ) * ((-1 : ℤ) ^ (m - (2 * j + 1)) * (-2 : ℤ) ^ (m - (2 * j + 1))) := by
              rw [hpow]
        _ = (-1 : ℤ) ^ (m - (2 * j + 1)) * (((Nat.choose (m - 1 - j) j : ℕ) : ℤ) * (-2 : ℤ) ^ (m - (2 * j + 1))) := by
              ring
  · rw [if_neg hcm]
    split_ifs
    · rw [mul_assoc, coeff_X_pow_mul, if_neg hcm]
    · rw [coeff_X_pow_mul, if_neg hcm]

/-- Reversed row polynomial in `PowerSeries ℤ`:
`revRowPS (2n) = (1 - 2*X)^n` and `revRowPS (2n + 1) = (1 - X) * (1 - 2*X)^n`.
Its coefficient `coeff i` equals `balaT r (r - i)` for `i ≤ r` (and `0` for `i > r`). -/
private noncomputable def revRowPS (r : ℕ) : PowerSeries ℤ :=
  if r % 2 = 0 then
    (1 - PowerSeries.C 2 * PowerSeries.X) ^ (r / 2)
  else
    (1 - PowerSeries.X) * (1 - PowerSeries.C 2 * PowerSeries.X) ^ (r / 2)

private lemma coeff_revRowPS (r i : ℕ) (hi : i ≤ r) :
    PowerSeries.coeff i (revRowPS r) = balaT r (r - i) := by
  have h1m2 : ∀ (n j : ℕ),
      PowerSeries.coeff j ((1 - PowerSeries.C (2 : ℤ) * PowerSeries.X) ^ n) =
        if j ≤ n then ((Nat.choose n j : ℕ) : ℤ) * (-2 : ℤ) ^ j else 0 := by
    intro n j
    have hbin : (1 - PowerSeries.C (2 : ℤ) * PowerSeries.X) ^ n =
        ∑ t ∈ Finset.range (n + 1),
          PowerSeries.C (((Nat.choose n t : ℕ) : ℤ) * (-2 : ℤ) ^ t) * PowerSeries.X ^ t := by
      have h := add_pow (PowerSeries.C (-2 : ℤ) * PowerSeries.X) (1 : PowerSeries ℤ) n
      have hsub : (1 : PowerSeries ℤ) - PowerSeries.C (2 : ℤ) * PowerSeries.X =
          PowerSeries.C (-2 : ℤ) * PowerSeries.X + 1 := by
        rw [map_neg]; ring
      rw [hsub, h]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [mul_pow, ← map_pow, one_pow, mul_one, map_mul, map_natCast]
      ring
    rw [hbin, map_sum]
    by_cases hj : j ≤ n
    · rw [if_pos hj, Finset.sum_eq_single j]
      · rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_pos rfl, mul_one]
      · intro t _ htne
        rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_neg htne.symm, mul_zero]
      · intro h; exfalso; exact h (Finset.mem_range.mpr (by omega))
    · rw [if_neg hj]
      refine Finset.sum_eq_zero (fun t ht => ?_)
      have htle : t ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_neg (by omega), mul_zero]
  unfold revRowPS
  rcases Nat.even_or_odd' r with ⟨n, rfl | rfl⟩
  · rw [if_pos (by omega), show (2 * n) / 2 = n by omega]
    unfold balaT
    rw [if_pos (by omega), show (2 * n) / 2 = n by omega, h1m2 n i]
    by_cases hin : i ≤ n
    · rw [if_pos hin, if_pos (by omega), show 2 * n - (2 * n - i) = i by omega]
      have hsym : Nat.choose n (2 * n - i - n) = Nat.choose n i := by
        rw [show 2 * n - i - n = n - i by omega, Nat.choose_symm hin]
      rw [hsym]
    · rw [if_neg hin, if_neg (by omega)]
  · rw [if_neg (by omega), show (2 * n + 1) / 2 = n by omega]
    rw [sub_mul, one_mul, map_sub]
    have hsplit : rowPoly (2 * n + 1) = Polynomial.X * rowPoly (2 * n) - rowPoly (2 * n) := by
      unfold rowPoly
      rw [if_neg (by omega), if_pos (by omega), show (2 * n + 1) / 2 = n by omega,
        show (2 * n) / 2 = n by omega]
      ring
    rw [← coeff_rowPoly_odd, hsplit, Polynomial.coeff_sub, coeff_rowPoly_even]
    have h1 : PowerSeries.coeff i ((1 - PowerSeries.C (2 : ℤ) * PowerSeries.X) ^ n) =
        (Polynomial.X * rowPoly (2 * n)).coeff (2 * n + 1 - i) := by
      by_cases htop : i = 2 * n + 1
      · subst htop
        rw [Nat.sub_self, h1m2 n (2 * n + 1), if_neg (by omega), Polynomial.coeff_X_mul_zero]
      · have hpos : 2 * n + 1 - i = (2 * n - i) + 1 := by omega
        rw [hpos, Polynomial.coeff_X_mul, coeff_rowPoly_even]
        unfold balaT
        rw [if_pos (by omega), show (2 * n) / 2 = n by omega, h1m2 n i]
        by_cases hin : i ≤ n
        · rw [if_pos hin, if_pos (by omega), show 2 * n - (2 * n - i) = i by omega,
            show 2 * n - i - n = n - i by omega, Nat.choose_symm hin]
        · rw [if_neg hin, if_neg (by omega)]
    have h2 : PowerSeries.coeff i (PowerSeries.X * (1 - PowerSeries.C (2 : ℤ) * PowerSeries.X) ^ n) =
        balaT (2 * n) (2 * n + 1 - i) := by
      cases i with
      | zero =>
        rw [coeff_X_mul_zero, Nat.sub_zero, balaT_of_lt (2 * n) (2 * n + 1) (by omega)]
      | succ i' =>
        rw [coeff_X_mul_succ]
        unfold balaT
        rw [if_pos (by omega), show (2 * n) / 2 = n by omega, h1m2 n i']
        by_cases hin : i' ≤ n
        · rw [if_pos hin, if_pos (by omega), show 2 * n - (2 * n + 1 - (i' + 1)) = i' by omega,
            show 2 * n + 1 - (i' + 1) - n = n - i' by omega, Nat.choose_symm hin]
        · rw [if_neg hin, if_neg (by omega)]
    rw [h1, h2]

private lemma coeff_poly_zero_of_deg_lt (p : Polynomial ℤ) (k : ℕ) (h : p.natDegree < k) :
    PowerSeries.coeff k (p : PowerSeries ℤ) = 0 := by
  rw [Polynomial.coeff_coe]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt h

private lemma balaT_mul_invFromCols (r c : ℕ) :
    (∑ m ∈ Finset.range (r + 1), balaT r m * invFromCols balaT m c) =
      if r = c then 1 else 0 := by
  have hconv : (∑ m ∈ Finset.range (r + 1), balaT r m * invFromCols balaT m c) =
      PowerSeries.coeff r (revRowPS r * colGF c) := by
    rw [coeff_mul_eq_sum_range]
    symm
    refine Finset.sum_nbij (fun i => r - i) ?_ ?_ ?_ ?_
    · intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
    · intro i1 h1 i2 h2 heq
      simp only [Finset.mem_coe, Finset.mem_range] at h1 h2
      dsimp only at heq; omega
    · intro m hm
      simp only [Finset.mem_coe, Finset.mem_range] at hm
      refine ⟨r - m, by simp only [Finset.mem_coe, Finset.mem_range]; omega, ?_⟩
      dsimp only; omega
    · intro i hi
      have hile : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [coeff_revRowPS r i hile, coeff_colGF c (r - i)]
  rw [hconv]
  -- Helper: (1 - 2*X)^a * inv1m2X^b reduces cleanly!
  have hcancel : ∀ a b : ℕ, b ≤ a →
      (1 - PowerSeries.C (2 : ℤ) * PowerSeries.X) ^ a * inv1m2X ^ b =
        (1 - PowerSeries.C (2 : ℤ) * PowerSeries.X) ^ (a - b) := by
    intro a b hba
    conv_lhs => rw [show a = (a - b) + b by omega]
    rw [pow_add, mul_assoc, ← mul_pow, mul_inv1m2X, one_pow, mul_one]
  -- Helper: coeff of (1 - X)^p * (1 - 2*X)^q * X^c vanishes when p + q + c < r!
  have hdeg_vanish : ∀ (p q s t : ℕ), p + q + s < t →
      PowerSeries.coeff t ((1 - PowerSeries.X : PowerSeries ℤ) ^ p *
        (1 - PowerSeries.C (2 : ℤ) * PowerSeries.X) ^ q * PowerSeries.X ^ s) = 0 := by
    intro p q s t hlt
    have hcoe : ((1 - PowerSeries.X : PowerSeries ℤ) ^ p *
        (1 - PowerSeries.C (2 : ℤ) * PowerSeries.X) ^ q * PowerSeries.X ^ s) =
        (((1 - Polynomial.X : Polynomial ℤ) ^ p *
          (1 - Polynomial.C (2 : ℤ) * Polynomial.X) ^ q * Polynomial.X ^ s : Polynomial ℤ) : PowerSeries ℤ) := by
      simp only [Polynomial.coe_pow, Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_one,
        Polynomial.coe_X, Polynomial.coe_C]
    rw [hcoe]
    apply coeff_poly_zero_of_deg_lt
    have hd1 : ((1 - Polynomial.X : Polynomial ℤ) ^ p).natDegree ≤ p := by
      refine le_trans Polynomial.natDegree_pow_le ?_
      have : (1 - Polynomial.X : Polynomial ℤ).natDegree ≤ 1 := by
        refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
        simp
      nlinarith
    have hd2 : ((1 - Polynomial.C (2 : ℤ) * Polynomial.X : Polynomial ℤ) ^ q).natDegree ≤ q := by
      refine le_trans Polynomial.natDegree_pow_le ?_
      have : (1 - Polynomial.C (2 : ℤ) * Polynomial.X : Polynomial ℤ).natDegree ≤ 1 := by
        refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
        simp
      nlinarith
    have hd3 : (Polynomial.X ^ s : Polynomial ℤ).natDegree ≤ s := by simp
    have hd12 : ((1 - Polynomial.X : Polynomial ℤ) ^ p *
        (1 - Polynomial.C (2 : ℤ) * Polynomial.X) ^ q).natDegree ≤ p + q :=
      le_trans Polynomial.natDegree_mul_le (add_le_add hd1 hd2)
    have hd123 : ((1 - Polynomial.X : Polynomial ℤ) ^ p *
        (1 - Polynomial.C (2 : ℤ) * Polynomial.X) ^ q * Polynomial.X ^ s).natDegree ≤ p + q + s :=
      le_trans Polynomial.natDegree_mul_le (add_le_add hd12 hd3)
    omega
  by_cases hrc : r < c
  · rw [if_neg (by omega : r ≠ c)]
    unfold colGF
    split_ifs
    · have h : revRowPS r * (PowerSeries.X ^ c * (1 - PowerSeries.X) * inv1m2X ^ (c / 2 + 1)) =
          PowerSeries.X ^ c * (revRowPS r * (1 - PowerSeries.X) * inv1m2X ^ (c / 2 + 1)) := by ring
      rw [h, coeff_X_pow_mul, if_neg (by omega)]
    · have h : revRowPS r * (PowerSeries.X ^ c * inv1m2X ^ (c / 2 + 1)) =
          PowerSeries.X ^ c * (revRowPS r * inv1m2X ^ (c / 2 + 1)) := by ring
      rw [h, coeff_X_pow_mul, if_neg (by omega)]
  · rcases Nat.even_or_odd' r with ⟨n, rfl | rfl⟩
    · rcases Nat.even_or_odd' c with ⟨j, rfl | rfl⟩
      · unfold revRowPS colGF
        rw [if_pos (by omega), if_pos (by omega), show (2 * n) / 2 = n by omega,
          show (2 * j) / 2 = j by omega]
        by_cases hjn : j = n
        · rw [hjn]
          rw [if_pos rfl]
          have h1 : (1 - PowerSeries.C (2 : ℤ) * PowerSeries.X) ^ n *
              (PowerSeries.X ^ (2 * n) * (1 - PowerSeries.X) * inv1m2X ^ (n + 1)) =
              PowerSeries.X ^ (2 * n) * ((1 - PowerSeries.X) * inv1m2X) := by
            rw [pow_succ inv1m2X n]
            calc
              _ = PowerSeries.X ^ (2 * n) * ((1 - PowerSeries.X) * inv1m2X) *
                    ((1 - PowerSeries.C (2 : ℤ) * PowerSeries.X) ^ n * inv1m2X ^ n) := by ring
              _ = PowerSeries.X ^ (2 * n) * ((1 - PowerSeries.X) * inv1m2X) * 1 := by
                    rw [hcancel n n le_rfl, Nat.sub_self, pow_zero]
              _ = _ := mul_one _
          rw [h1, coeff_X_pow_mul, if_pos le_rfl, Nat.sub_self]
          rw [sub_mul, one_mul, map_sub, coeff_X_mul_zero, sub_zero]
          simp [inv1m2X]
        · rw [if_neg (by omega : 2 * n ≠ 2 * j)]
          have hjlt : j + 1 ≤ n := by omega
          have h1 : (1 - PowerSeries.C (2 : ℤ) * PowerSeries.X) ^ n *
              (PowerSeries.X ^ (2 * j) * (1 - PowerSeries.X) * inv1m2X ^ (j + 1)) =
              (1 - PowerSeries.X) ^ 1 * (1 - PowerSeries.C (2 : ℤ) * PowerSeries.X) ^ (n - (j + 1)) *
                PowerSeries.X ^ (2 * j) := by
            rw [pow_one, ← hcancel n (j + 1) hjlt]; ring
          rw [h1]
          exact hdeg_vanish 1 (n - (j + 1)) (2 * j) (2 * n) (by omega)
      · unfold revRowPS colGF
        rw [if_pos (by omega), if_neg (by omega), show (2 * n) / 2 = n by omega,
          show (2 * j + 1) / 2 = j by omega, if_neg (by omega : 2 * n ≠ 2 * j + 1)]
        have hjlt : j + 1 ≤ n := by omega
        have h1 : (1 - PowerSeries.C (2 : ℤ) * PowerSeries.X) ^ n *
            (PowerSeries.X ^ (2 * j + 1) * inv1m2X ^ (j + 1)) =
            (1 - PowerSeries.X) ^ 0 * (1 - PowerSeries.C (2 : ℤ) * PowerSeries.X) ^ (n - (j + 1)) *
              PowerSeries.X ^ (2 * j + 1) := by
          rw [pow_zero, one_mul, ← hcancel n (j + 1) hjlt]; ring
        rw [h1]
        exact hdeg_vanish 0 (n - (j + 1)) (2 * j + 1) (2 * n) (by omega)
    · rcases Nat.even_or_odd' c with ⟨j, rfl | rfl⟩
      · unfold revRowPS colGF
        rw [if_neg (by omega), if_pos (by omega), show (2 * n + 1) / 2 = n by omega,
          show (2 * j) / 2 = j by omega, if_neg (by omega : 2 * n + 1 ≠ 2 * j)]
        by_cases hjn : j = n
        · rw [hjn]
          have h1 : (1 - PowerSeries.X) * (1 - PowerSeries.C (2 : ℤ) * PowerSeries.X) ^ n *
              (PowerSeries.X ^ (2 * n) * (1 - PowerSeries.X) * inv1m2X ^ (n + 1)) =
              PowerSeries.X ^ (2 * n) * ((1 - PowerSeries.X) ^ 2 * inv1m2X) := by
            rw [pow_succ inv1m2X n]
            calc
              _ = PowerSeries.X ^ (2 * n) * ((1 - PowerSeries.X) ^ 2 * inv1m2X) *
                    ((1 - PowerSeries.C (2 : ℤ) * PowerSeries.X) ^ n * inv1m2X ^ n) := by ring
              _ = PowerSeries.X ^ (2 * n) * ((1 - PowerSeries.X) ^ 2 * inv1m2X) * 1 := by
                    rw [hcancel n n le_rfl, Nat.sub_self, pow_zero]
              _ = _ := mul_one _
          rw [h1, coeff_X_pow_mul, if_pos (by omega), show 2 * n + 1 - 2 * n = 1 by omega]
          have hsq : (1 - PowerSeries.X : PowerSeries ℤ) ^ 2 * inv1m2X =
              inv1m2X - PowerSeries.C 2 * (PowerSeries.X * inv1m2X) + PowerSeries.X * (PowerSeries.X * inv1m2X) := by
            have hc2 : PowerSeries.C (2 : ℤ) = 1 + 1 := by rw [← map_one PowerSeries.C, ← map_add]; norm_num
            rw [hc2]; ring
          rw [hsq, map_add, map_sub, PowerSeries.coeff_C_mul, coeff_X_mul_succ, coeff_X_mul_succ,
            coeff_X_mul_zero]
          simp [inv1m2X]
        · have hjlt : j + 1 ≤ n := by omega
          have h1 : (1 - PowerSeries.X) * (1 - PowerSeries.C (2 : ℤ) * PowerSeries.X) ^ n *
              (PowerSeries.X ^ (2 * j) * (1 - PowerSeries.X) * inv1m2X ^ (j + 1)) =
              (1 - PowerSeries.X) ^ 2 * (1 - PowerSeries.C (2 : ℤ) * PowerSeries.X) ^ (n - (j + 1)) *
                PowerSeries.X ^ (2 * j) := by
            rw [← hcancel n (j + 1) hjlt]; ring
          rw [h1]
          exact hdeg_vanish 2 (n - (j + 1)) (2 * j) (2 * n + 1) (by omega)
      · unfold revRowPS colGF
        rw [if_neg (by omega), if_neg (by omega), show (2 * n + 1) / 2 = n by omega,
          show (2 * j + 1) / 2 = j by omega]
        by_cases hjn : j = n
        · rw [hjn]
          rw [if_pos rfl]
          have h1 : (1 - PowerSeries.X) * (1 - PowerSeries.C (2 : ℤ) * PowerSeries.X) ^ n *
              (PowerSeries.X ^ (2 * n + 1) * inv1m2X ^ (n + 1)) =
              PowerSeries.X ^ (2 * n + 1) * ((1 - PowerSeries.X) * inv1m2X) := by
            rw [pow_succ inv1m2X n]
            calc
              _ = PowerSeries.X ^ (2 * n + 1) * ((1 - PowerSeries.X) * inv1m2X) *
                    ((1 - PowerSeries.C (2 : ℤ) * PowerSeries.X) ^ n * inv1m2X ^ n) := by ring
              _ = PowerSeries.X ^ (2 * n + 1) * ((1 - PowerSeries.X) * inv1m2X) * 1 := by
                    rw [hcancel n n le_rfl, Nat.sub_self, pow_zero]
              _ = _ := mul_one _
          rw [h1, coeff_X_pow_mul, if_pos le_rfl, Nat.sub_self]
          rw [sub_mul, one_mul, map_sub, coeff_X_mul_zero, sub_zero]
          simp [inv1m2X]
        · rw [if_neg (by omega : 2 * n + 1 ≠ 2 * j + 1)]
          have hjlt : j + 1 ≤ n := by omega
          have h1 : (1 - PowerSeries.X) * (1 - PowerSeries.C (2 : ℤ) * PowerSeries.X) ^ n *
              (PowerSeries.X ^ (2 * j + 1) * inv1m2X ^ (j + 1)) =
              (1 - PowerSeries.X) ^ 1 * (1 - PowerSeries.C (2 : ℤ) * PowerSeries.X) ^ (n - (j + 1)) *
                PowerSeries.X ^ (2 * j + 1) := by
            rw [pow_one, ← hcancel n (j + 1) hjlt]; ring
          rw [h1]
          exact hdeg_vanish 1 (n - (j + 1)) (2 * j + 1) (2 * n + 1) (by omega)

/-! ### Part 3: Subdiagonal formula and uniqueness of any matrix `T` satisfying OEIS A104041 -/

private lemma balaT_subdiag (n : ℕ) : balaT (n + 1) n = -((n + 1 : ℕ) : ℤ) := by
  rcases Nat.even_or_odd' (n + 1) with ⟨m, hm | hm⟩
  · have hm1 : 1 ≤ m := by omega
    have hn : n = 2 * m - 1 := by omega
    rw [hm, hn]
    unfold balaT
    rw [if_pos (by omega), show (2 * m) / 2 = m by omega, if_pos (by omega)]
    rw [show 2 * m - (2 * m - 1) = 1 by omega, show 2 * m - 1 - m = m - 1 by omega,
      show m - 1 = m - 1 by rfl]
    have hch : Nat.choose m (m - 1) = m := by
      rw [← Nat.choose_symm (by omega : m - 1 ≤ m), show m - (m - 1) = 1 by omega, Nat.choose_one_right]
    rw [hch, pow_one]
    push_cast
    linarith [show (2 * m : ℤ) = (n : ℤ) + 1 by exact_mod_cast hm.symm]
  · have hn : n = 2 * m := by omega
    rw [hm, hn, ← coeff_rowPoly_odd]
    have hsplit : rowPoly (2 * m + 1) = Polynomial.X * rowPoly (2 * m) - rowPoly (2 * m) := by
      unfold rowPoly
      rw [if_neg (by omega), if_pos (by omega), show (2 * m + 1) / 2 = m by omega,
        show (2 * m) / 2 = m by omega]
      ring
    rw [hsplit, Polynomial.coeff_sub, coeff_rowPoly_even, balaT_diag (2 * m)]
    cases m with
    | zero =>
      simp
    | succ m' =>
      have hX : (Polynomial.X * rowPoly (2 * (m' + 1))).coeff (2 * (m' + 1)) =
          balaT (2 * (m' + 1)) (2 * (m' + 1) - 1) := by
        conv_lhs => arg 2; rw [show 2 * (m' + 1) = (2 * (m' + 1) - 1) + 1 by omega]
        rw [Polynomial.coeff_X_mul, coeff_rowPoly_even]
      rw [hX]
      unfold balaT
      rw [if_pos (by omega), show (2 * (m' + 1)) / 2 = m' + 1 by omega, if_pos (by omega)]
      rw [show 2 * (m' + 1) - (2 * (m' + 1) - 1) = 1 by omega,
        show 2 * (m' + 1) - 1 - (m' + 1) = m' by omega]
      have hch : Nat.choose (m' + 1) m' = m' + 1 := by
        rw [← Nat.choose_symm (by omega : m' ≤ m' + 1), Nat.add_sub_cancel_left, Nat.choose_one_right]
      rw [hch, pow_one]
      push_cast; ring

private lemma eq_of_abs_and_sign (a b : ℤ) (s : ℕ)
    (habs : |a| = |b|)
    (ha : 0 ≤ (-1 : ℤ) ^ s * a)
    (hb : 0 ≤ (-1 : ℤ) ^ s * b) : a = b := by
  have h1 : (-1 : ℤ) ^ s * a = |a| := by
    have h := abs_of_nonneg ha
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at h
    exact h.symm
  have h2 : (-1 : ℤ) ^ s * b = |b| := by
    have h := abs_of_nonneg hb
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at h
    exact h.symm
  have heq : (-1 : ℤ) ^ s * a = (-1 : ℤ) ^ s * b := by rw [h1, h2, habs]
  have hsq : (-1 : ℤ) ^ s * (-1 : ℤ) ^ s = 1 := by rw [← mul_pow]; norm_num
  calc
    a = 1 * a := (one_mul a).symm
    _ = ((-1 : ℤ) ^ s * (-1 : ℤ) ^ s) * a := by rw [hsq]
    _ = (-1 : ℤ) ^ s * ((-1 : ℤ) ^ s * a) := by ring
    _ = (-1 : ℤ) ^ s * ((-1 : ℤ) ^ s * b) := by rw [heq]
    _ = ((-1 : ℤ) ^ s * (-1 : ℤ) ^ s) * b := by ring
    _ = 1 * b := by rw [hsq]
    _ = b := one_mul b

private lemma uniqueness_of_A104041
    (T : ℕ → ℕ → ℤ)
    (hdiag : ∀ r : ℕ, T r r = 1)
    (hsub : ∀ n : ℕ, T (n + 1) n = -((n + 1 : ℕ) : ℤ))
    (hlt : ∀ r k : ℕ, r < k → T r k = 0)
    (hgt : ∀ r k : ℕ, 2 * k + 1 < r → T r k = 0)
    (hsign : ∀ r k : ℕ, k ≤ r → 0 ≤ (-1 : ℤ) ^ (r - k) * T r k)
    (hinv : ∀ r c : ℕ,
      (∑ m ∈ Finset.range (r + 1), T r m * invFromCols T m c) = if r = c then 1 else 0) :
    ∀ k r : ℕ, T r k = balaT r k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro r
    by_cases hrlt : r < k
    · rw [hlt r k hrlt, balaT_of_lt r k hrlt]
    · by_cases hreq : r = k
      · subst hreq; rw [hdiag r, balaT_diag r]
      · by_cases hr1 : r = k + 1
        · subst hr1; rw [hsub k, balaT_subdiag k]
        · by_cases hrgt : 2 * k + 1 < r
          · rw [hgt r k hrgt, balaT_of_gt r k hrgt]
          · -- Main case: k + 2 ≤ r ≤ 2 * k + 1, so c = 2 * k + 1 - r satisfies c < k!
            set c : ℕ := 2 * k + 1 - r
            have hck : c < k := by dsimp only [c]; omega
            have hinv_eq_lt : ∀ m ≤ k, invFromCols T m c = invFromCols balaT m c := by
              intro m hm
              unfold invFromCols
              by_cases hcm : c ≤ m
              · rw [if_pos hcm, if_pos hcm]
                cases m with
                | zero => simp
                | succ m' =>
                  rw [if_neg (Nat.succ_ne_zero m'), if_neg (Nat.succ_ne_zero m')]
                  rw [Nat.add_sub_cancel, ih m' (by omega)]
              · rw [if_neg hcm, if_neg hcm]
            have hsum_T := hinv (k + 1) c
            have hsum_B := balaT_mul_invFromCols (k + 1) c
            rw [if_neg (by omega : k + 1 ≠ c)] at hsum_T hsum_B
            rw [Finset.sum_range_succ, Finset.sum_range_succ] at hsum_T hsum_B
            have hpart : ∑ m ∈ Finset.range k, T (k + 1) m * invFromCols T m c =
                ∑ m ∈ Finset.range k, balaT (k + 1) m * invFromCols balaT m c := by
              refine Finset.sum_congr rfl (fun m hm => ?_)
              have hmlt : m < k := Finset.mem_range.mp hm
              rw [ih m hmlt (k + 1), hinv_eq_lt m (by omega)]
            rw [hpart, hsub k, hinv_eq_lt k le_rfl, hdiag (k + 1), one_mul] at hsum_T
            rw [balaT_subdiag k, balaT_diag (k + 1), one_mul] at hsum_B
            have hinv_k1 : invFromCols T (k + 1) c = invFromCols balaT (k + 1) c := by linarith
            unfold invFromCols at hinv_k1
            rw [if_pos (by omega : c ≤ k + 1), if_pos (by omega : c ≤ k + 1),
              if_neg (Nat.succ_ne_zero k), if_neg (Nat.succ_ne_zero k)] at hinv_k1
            have hidx : 2 * (k + 1) - 1 - c = r := by dsimp only [c]; omega
            rw [hidx, Nat.add_sub_cancel] at hinv_k1
            exact eq_of_abs_and_sign (T r k) (balaT r k) (r - k) hinv_k1
              (hsign r k (by omega)) (balaT_sign r k (by omega))

theorem solution :
    (∀ r : ℕ, balaT r r = 1) ∧
    (∀ n : ℕ, balaT (n + 1) n = -((n + 1 : ℕ) : ℤ)) ∧
    (∀ r k : ℕ, r < k → balaT r k = 0) ∧
    (∀ r k : ℕ, 2 * k + 1 < r → balaT r k = 0) ∧
    (∀ r c : ℕ,
      (∑ m ∈ Finset.range (r + 1), balaT r m * invFromCols balaT m c) = if r = c then 1 else 0) ∧
    (∀ (T : ℕ → ℕ → ℤ),
      (∀ r : ℕ, T r r = 1) →
      (∀ n : ℕ, T (n + 1) n = -((n + 1 : ℕ) : ℤ)) →
      (∀ r k : ℕ, r < k → T r k = 0) →
      (∀ r k : ℕ, 2 * k + 1 < r → T r k = 0) →
      (∀ r k : ℕ, k ≤ r → 0 ≤ (-1 : ℤ) ^ (r - k) * T r k) →
      (∀ r c : ℕ,
        (∑ m ∈ Finset.range (r + 1), T r m * invFromCols T m c) = if r = c then 1 else 0) →
      ∀ r k : ℕ, T r k = balaT r k) :=
  ⟨balaT_diag, balaT_subdiag, balaT_of_lt, balaT_of_gt, balaT_mul_invFromCols,
    fun T h1 h2 h3 h4 h5 h6 r k => uniqueness_of_A104041 T h1 h2 h3 h4 h5 h6 k r⟩

end OMA.P_oeis_a104041

theorem OMA.solution : type_of% @OMA.S_oeis_a104041.main :=
  OMA.P_oeis_a104041.solution

import OMAStatements.S_oeis_a396805
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

namespace OeisA396805Disproof

open OMA.S_oeis_a396805

/-! ### Generic Hurwitz (EGF) operations over `ZMod 5` -/

private def divPow5 (G : ℕ → ZMod 5) : ℕ → ℕ → ZMod 5
  | 0, n => if n = 0 then 1 else 0
  | _ + 1, 0 => 0
  | k + 1, n + 1 =>
    ∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ZMod 5) * G (j + 1) * divPow5 G k (n - j)

private def comp5 (F G : ℕ → ZMod 5) (n : ℕ) : ZMod 5 :=
  ∑ k ∈ Finset.range (n + 1), F k * divPow5 G k n

private def iter5 (F : ℕ → ZMod 5) : ℕ → ℕ → ZMod 5
  | 0 => fun n => if n = 1 then 1 else 0
  | k + 1 => comp5 (iter5 F k) F

private def exp5 (F : ℕ → ZMod 5) : ℕ → ZMod 5
  | 0 => 1
  | n + 1 =>
    ∑ j : Fin (n + 1), (Nat.choose n j.1 : ZMod 5) * F (j.1 + 1) * exp5 F (n - j.1)
termination_by n => n

private lemma egfDivPow_cast5 (G : ℕ → ℤ) (k n : ℕ) :
    (egfDivPow G k n : ZMod 5) = divPow5 (fun m => (G m : ZMod 5)) k n := by
  induction k generalizing n with
  | zero =>
    simp only [egfDivPow, divPow5]
    split_ifs <;> simp
  | succ k ih =>
    cases n with
    | zero => simp [egfDivPow, divPow5]
    | succ n =>
      simp only [egfDivPow, divPow5, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
      apply Finset.sum_congr rfl
      intro j _
      rw [ih]

private lemma egfComp_cast5 (F G : ℕ → ℤ) (n : ℕ) :
    (egfComp F G n : ZMod 5) = comp5 (fun m => (F m : ZMod 5)) (fun m => (G m : ZMod 5)) n := by
  simp only [egfComp, comp5, Int.cast_sum, Int.cast_mul, egfDivPow_cast5]

private lemma egfIter_cast5 (F : ℕ → ℤ) (k n : ℕ) :
    (egfIter F k n : ZMod 5) = iter5 (fun m => (F m : ZMod 5)) k n := by
  induction k generalizing n with
  | zero =>
    simp only [egfIter, iter5]
    split_ifs <;> simp
  | succ k ih =>
    simp only [egfIter, iter5, egfComp_cast5, comp5]
    apply Finset.sum_congr rfl
    intro j _
    rw [ih j]

private lemma egfExp_cast5 (F : ℕ → ℤ) :
    ∀ n : ℕ, (egfExp F n : ZMod 5) = exp5 (fun m => (F m : ZMod 5)) n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => rw [egfExp, exp5]; simp
    | succ n =>
      rw [egfExp, exp5]
      simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast]
      apply Finset.sum_congr rfl
      intro j _
      rw [ih (n - j.1) (by omega)]

private lemma divPow5_congr {G1 G2 : ℕ → ZMod 5} {N : ℕ}
    (hG : ∀ m ≤ N, G1 m = G2 m) (k : ℕ) :
    ∀ n ≤ N, divPow5 G1 k n = divPow5 G2 k n := by
  induction k with
  | zero => intro n _; rfl
  | succ k ih =>
    intro n hn
    cases n with
    | zero => rfl
    | succ n =>
      simp only [divPow5]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      rw [hG (j + 1) (by omega), ih (n - j) (by omega)]

private lemma comp5_congr {F1 F2 G1 G2 : ℕ → ZMod 5} {N : ℕ}
    (hF : ∀ m ≤ N, F1 m = F2 m) (hG : ∀ m ≤ N, G1 m = G2 m) :
    ∀ n ≤ N, comp5 F1 G1 n = comp5 F2 G2 n := by
  intro n hn
  unfold comp5
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [hF k (by omega), divPow5_congr hG k n hn]

private lemma iter5_congr {F1 F2 : ℕ → ZMod 5} {N : ℕ}
    (hF : ∀ m ≤ N, F1 m = F2 m) (k : ℕ) :
    ∀ n ≤ N, iter5 F1 k n = iter5 F2 k n := by
  induction k with
  | zero => intro n _; rfl
  | succ k ih =>
    intro n hn
    exact comp5_congr ih hF n hn

private lemma exp5_congr {F1 F2 : ℕ → ZMod 5} {N : ℕ}
    (hF : ∀ m ≤ N, F1 m = F2 m) :
    ∀ n ≤ N, exp5 F1 n = exp5 F2 n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero => rw [exp5, exp5]
    | succ n =>
      rw [exp5, exp5]
      apply Finset.sum_congr rfl
      intro j _
      rw [hF (j.1 + 1) (by omega), ih (n - j.1) (by omega) (by omega)]

/-! ### Closed form for divided powers of `g(m) = (m : ZMod 5)` -/

private lemma sum_choose_mul_pow_nat (m k : ℕ) :
    ∑ j ∈ Finset.range (m + 1), Nat.choose m j * (j + 1) * k ^ (m - j) =
      (k + 1) ^ m + m * (k + 1) ^ (m - 1) := by
  cases m with
  | zero => simp
  | succ m =>
    have h1 : ∑ j ∈ Finset.range (m + 2), Nat.choose (m + 1) j * k ^ (m + 1 - j) = (k + 1) ^ (m + 1) := by
      have h := add_pow (1 : ℕ) k (m + 1)
      rw [add_comm 1 k] at h
      rw [h]
      apply Finset.sum_congr rfl
      intro j _; simp [mul_comm]
    have h2 : ∑ j ∈ Finset.range (m + 2), Nat.choose (m + 1) j * j * k ^ (m + 1 - j) =
        (m + 1) * (k + 1) ^ m := by
      rw [Finset.sum_range_succ']
      simp only [mul_zero, zero_mul, add_zero]
      have hterm :
          ∑ j ∈ Finset.range (m + 1),
            Nat.choose (m + 1) (j + 1) * (j + 1) * k ^ (m + 1 - (j + 1)) =
          (m + 1) * ∑ j ∈ Finset.range (m + 1), Nat.choose m j * k ^ (m - j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        have hch : Nat.choose (m + 1) (j + 1) * (j + 1) = (m + 1) * Nat.choose m j := by
          have := Nat.add_one_mul_choose_eq m j; linarith
        have hsub : m + 1 - (j + 1) = m - j := by omega
        rw [hch, hsub, mul_assoc]
      rw [hterm]
      congr 1
      have h := add_pow (1 : ℕ) k m
      rw [add_comm 1 k] at h
      rw [h]
      apply Finset.sum_congr rfl
      intro j _; simp [mul_comm]
    have hsplit :
        ∑ j ∈ Finset.range (m + 2), Nat.choose (m + 1) j * (j + 1) * k ^ (m + 1 - j) =
        (∑ j ∈ Finset.range (m + 2), Nat.choose (m + 1) j * k ^ (m + 1 - j)) +
        (∑ j ∈ Finset.range (m + 2), Nat.choose (m + 1) j * j * k ^ (m + 1 - j)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _; ring
    rw [hsplit, h1, h2]
    simp

private lemma divPow5_id (k n : ℕ) :
    divPow5 (fun m => (m : ZMod 5)) k n = (Nat.choose n k : ZMod 5) * (k : ZMod 5) ^ (n - k) := by
  induction k generalizing n with
  | zero =>
    cases n with
    | zero => simp [divPow5]
    | succ n => simp [divPow5]
  | succ k ih =>
    cases n with
    | zero => simp [divPow5]
    | succ n =>
      simp only [divPow5]
      simp_rw [ih]
      by_cases hkn : k ≤ n
      · have hnat :
            ∑ j ∈ Finset.range (n + 1),
              Nat.choose n j * (j + 1) * (Nat.choose (n - j) k * k ^ (n - j - k)) =
            Nat.choose (n + 1) (k + 1) * (k + 1) ^ (n - k) := by
          have hcut :
              ∑ j ∈ Finset.range (n + 1),
                Nat.choose n j * (j + 1) * (Nat.choose (n - j) k * k ^ (n - j - k)) =
              ∑ j ∈ Finset.range (n - k + 1),
                Nat.choose n k * (Nat.choose (n - k) j * (j + 1) * k ^ (n - k - j)) := by
            have hle : n - k + 1 ≤ n + 1 := by omega
            rw [← Finset.sum_subset (Finset.range_mono hle)]
            · apply Finset.sum_congr rfl
              intro j hj
              rw [Finset.mem_range] at hj
              have hch : Nat.choose n j * Nat.choose (n - j) k =
                  Nat.choose n k * Nat.choose (n - k) j := by
                have hpos : 0 < j.factorial * k.factorial * (n - j - k).factorial := by positivity
                apply Nat.eq_of_mul_eq_mul_right hpos
                have h1 := Nat.choose_mul_factorial_mul_factorial (by omega : j ≤ n)
                have h2 := Nat.choose_mul_factorial_mul_factorial (by omega : k ≤ n - j)
                have h3 := Nat.choose_mul_factorial_mul_factorial (by omega : k ≤ n)
                have h4 := Nat.choose_mul_factorial_mul_factorial (by omega : j ≤ n - k)
                have hsub : n - j - k = n - k - j := by omega
                calc Nat.choose n j * Nat.choose (n - j) k * (j.factorial * k.factorial * (n - j - k).factorial)
                    = Nat.choose n j * j.factorial * (Nat.choose (n - j) k * k.factorial * (n - j - k).factorial) := by ring
                  _ = Nat.choose n j * j.factorial * (n - j).factorial := by rw [h2]
                  _ = n.factorial := h1
                  _ = Nat.choose n k * k.factorial * (n - k).factorial := h3.symm
                  _ = Nat.choose n k * k.factorial * (Nat.choose (n - k) j * j.factorial * (n - k - j).factorial) := by rw [← h4]
                  _ = Nat.choose n k * Nat.choose (n - k) j * (j.factorial * k.factorial * (n - j - k).factorial) := by rw [hsub]; ring
              have hsub : n - j - k = n - k - j := by omega
              rw [hsub]
              calc Nat.choose n j * (j + 1) * (Nat.choose (n - j) k * k ^ (n - k - j))
                  = (Nat.choose n j * Nat.choose (n - j) k) * ((j + 1) * k ^ (n - k - j)) := by ring
                _ = (Nat.choose n k * Nat.choose (n - k) j) * ((j + 1) * k ^ (n - k - j)) := by rw [hch]
                _ = Nat.choose n k * (Nat.choose (n - k) j * (j + 1) * k ^ (n - k - j)) := by ring
            · intro j hj hnot
              rw [Finset.mem_range] at hj hnot
              rw [Nat.choose_eq_zero_of_lt (by omega : n - j < k)]
              simp
          rw [hcut, ← Finset.mul_sum, sum_choose_mul_pow_nat (n - k) k]
          cases hnk : n - k with
          | zero =>
            have heq : n = k := by omega
            subst heq; simp
          | succ m =>
            have hpow : (k + 1) ^ (m + 1) + (m + 1) * (k + 1) ^ m = (n + 1) * (k + 1) ^ m := by
              rw [pow_succ]
              have hsum : k + 1 + (m + 1) = n + 1 := by omega
              calc (k + 1) ^ m * (k + 1) + (m + 1) * (k + 1) ^ m
                  = (k + 1 + (m + 1)) * (k + 1) ^ m := by ring
                _ = (n + 1) * (k + 1) ^ m := by rw [hsum]
            rw [Nat.add_sub_cancel, hpow]
            have hch : Nat.choose n k * (n + 1) = Nat.choose (n + 1) (k + 1) * (k + 1) := by
              have := Nat.add_one_mul_choose_eq n k; linarith
            calc Nat.choose n k * ((n + 1) * (k + 1) ^ m)
                = (Nat.choose n k * (n + 1)) * (k + 1) ^ m := by ring
              _ = (Nat.choose (n + 1) (k + 1) * (k + 1)) * (k + 1) ^ m := by rw [hch]
              _ = Nat.choose (n + 1) (k + 1) * ((k + 1) ^ m * (k + 1)) := by ring
              _ = Nat.choose (n + 1) (k + 1) * (k + 1) ^ (m + 1) := by rw [← pow_succ]
        have hcast :
            (∑ j ∈ Finset.range (n + 1),
              (Nat.choose n j : ZMod 5) * ((j + 1 : ℕ) : ZMod 5) *
                ((Nat.choose (n - j) k : ZMod 5) * (k : ZMod 5) ^ (n - j - k))) =
            (Nat.choose (n + 1) (k + 1) : ZMod 5) * ((k + 1 : ℕ) : ZMod 5) ^ (n - k) := by
          have h := congrArg (Nat.cast : ℕ → ZMod 5) hnat
          simpa [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow] using h
        simpa [Nat.add_sub_add_right] using hcast
      · have hzero : Nat.choose (n + 1) (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        rw [hzero, Nat.cast_zero, zero_mul]
        apply Finset.sum_eq_zero
        intro j hj
        rw [Finset.mem_range] at hj
        rw [Nat.choose_eq_zero_of_lt (by omega : n - j < k)]
        simp

/-! ### Lucas's theorem mod 5 for fast `O(1)` binomial evaluation on `n < 25` -/

private lemma lucas_mod5 (n k : ℕ) :
    (Nat.choose n k : ZMod 5) =
      (Nat.choose (n / 5) (k / 5) : ZMod 5) * (Nat.choose (n % 5) (k % 5) : ZMod 5) := by
  have h5 : (1 + Polynomial.X : Polynomial (ZMod 5)) ^ 5 = 1 + Polynomial.X ^ 5 := by
    have h5z : (5 : Polynomial (ZMod 5)) = 0 := by
      change ((5 : ℕ) : Polynomial (ZMod 5)) = 0
      rw [← Polynomial.C_eq_natCast, show ((5 : ℕ) : ZMod 5) = 0 by decide, map_zero]
    have h10z : (10 : Polynomial (ZMod 5)) = 0 := by
      change ((10 : ℕ) : Polynomial (ZMod 5)) = 0
      rw [← Polynomial.C_eq_natCast, show ((10 : ℕ) : ZMod 5) = 0 by decide, map_zero]
    calc (1 + Polynomial.X : Polynomial (ZMod 5)) ^ 5
        = 1 + 5 * (Polynomial.X + Polynomial.X ^ 4) +
            10 * (Polynomial.X ^ 2 + Polynomial.X ^ 3) + Polynomial.X ^ 5 := by ring
      _ = 1 + Polynomial.X ^ 5 := by rw [h5z, h10z]; ring
  have hpoly : (1 + Polynomial.X : Polynomial (ZMod 5)) ^ n =
      (1 + Polynomial.X ^ 5 : Polynomial (ZMod 5)) ^ (n / 5) *
        (1 + Polynomial.X : Polynomial (ZMod 5)) ^ (n % 5) := by
    conv_lhs => rw [show n = 5 * (n / 5) + n % 5 by omega, pow_add, pow_mul, h5]
  have hcoeff_pow : ∀ m r : ℕ, ((1 + Polynomial.X : Polynomial (ZMod 5)) ^ m).coeff r =
      (Nat.choose m r : ZMod 5) := by
    intro m r
    rw [add_comm, add_pow, Polynomial.finsetSum_coeff]
    by_cases hrm : r ≤ m
    · rw [Finset.sum_eq_single r]
      · simp [Polynomial.coeff_X_pow]
      · intro i _ hne; simp [Polynomial.coeff_X_pow, Ne.symm hne]
      · intro hm; exact absurd (Finset.mem_range.mpr (by omega)) hm
    · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_range] at hi
      simp [Polynomial.coeff_X_pow, show r ≠ i by omega]
  have hcoeff_pow5 : ∀ m r : ℕ, ((1 + Polynomial.X ^ 5 : Polynomial (ZMod 5)) ^ m).coeff r =
      if r % 5 = 0 then (Nat.choose m (r / 5) : ZMod 5) else 0 := by
    intro m r
    rw [add_comm, add_pow, Polynomial.finsetSum_coeff]
    split_ifs with h0
    · by_cases hrm : r / 5 ≤ m
      · rw [Finset.sum_eq_single (r / 5)]
        · rw [← pow_mul, one_pow, mul_one, Polynomial.coeff_X_pow_mul']
          have hr5 : 5 * (r / 5) = r := by omega
          simp [hr5]
        · intro i _ hne
          rw [← pow_mul, one_pow, mul_one, Polynomial.coeff_X_pow_mul']
          by_cases hle : 5 * i ≤ r
          · rw [if_pos hle, Polynomial.coeff_natCast_ite, if_neg (by omega), Nat.cast_zero]
          · rw [if_neg hle]
        · intro hm; exact absurd (Finset.mem_range.mpr (by omega)) hm
      · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
        apply Finset.sum_eq_zero
        intro i hi
        rw [Finset.mem_range] at hi
        rw [← pow_mul, one_pow, mul_one, Polynomial.coeff_X_pow_mul']
        by_cases hle : 5 * i ≤ r
        · rw [if_pos hle, Polynomial.coeff_natCast_ite, if_neg (by omega), Nat.cast_zero]
        · rw [if_neg hle]
    · apply Finset.sum_eq_zero
      intro i _
      rw [← pow_mul, one_pow, mul_one, Polynomial.coeff_X_pow_mul']
      by_cases hle : 5 * i ≤ r
      · rw [if_pos hle, Polynomial.coeff_natCast_ite, if_neg (by omega), Nat.cast_zero]
      · rw [if_neg hle]
  rw [← hcoeff_pow n k, hpoly, Polynomial.coeff_mul]
  rw [Finset.sum_eq_single (5 * (k / 5), k % 5)]
  · rw [hcoeff_pow5, if_pos (by omega), show 5 * (k / 5) / 5 = k / 5 by omega, hcoeff_pow]
  · intro x hx hne
    have hx' : x.1 + x.2 = k := by simpa using hx
    rw [hcoeff_pow5, hcoeff_pow]
    split_ifs with h0
    · by_cases hlt : x.2 < 5
      · exfalso
        apply hne
        ext
        · dsimp only; omega
        · dsimp only; omega
      · rw [Nat.choose_eq_zero_of_lt (by omega : n % 5 < x.2), Nat.cast_zero, mul_zero]
    · rw [zero_mul]
  · intro hnot
    exfalso; apply hnot
    rw [Finset.mem_antidiagonal]
    omega

/-! ### Explicit verification of `iter5 g 5` on `0..22` -/

private def V1 : Fin 23 → ZMod 5 :=
  ![0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2, 3, 4, 0, 1, 2]

private def V2 : Fin 23 → ZMod 5 :=
  ![0, 1, 4, 3, 2, 0, 2, 0, 4, 1, 0, 4, 1, 3, 4, 0, 3, 0, 0, 2, 0, 1, 4]

private def V3 : Fin 23 → ZMod 5 :=
  ![0, 1, 1, 0, 3, 0, 3, 4, 0, 4, 0, 4, 0, 3, 1, 0, 2, 2, 0, 3, 0, 1, 4]

private def V4 : Fin 23 → ZMod 5 :=
  ![0, 1, 3, 4, 1, 0, 4, 4, 3, 1, 0, 1, 2, 1, 1, 0, 4, 1, 2, 1, 0, 1, 1]

private def V5 : Fin 23 → ZMod 5 :=
  ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3]

private def step5 (U : Fin 23 → ZMod 5) (n : Fin 23) : ZMod 5 :=
  ∑ j : Fin 23,
    if j.1 ≤ n.1 then
      U j * ((Nat.choose (n.1 / 5) (j.1 / 5) : ZMod 5) * (Nat.choose (n.1 % 5) (j.1 % 5) : ZMod 5)) *
        (j.1 : ZMod 5) ^ (n.1 - j.1)
    else 0

private lemma comp5_eq_step5 (F : ℕ → ZMod 5) (U : Fin 23 → ZMod 5)
    (hFU : ∀ j : Fin 23, F j.1 = U j) (n : Fin 23) :
    comp5 F (fun m => (m : ZMod 5)) n.1 = step5 U n := by
  unfold comp5 step5
  simp_rw [divPow5_id]
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun j _ => j.1)
  · intro j hj
    rw [Finset.mem_filter] at hj
    rw [Finset.mem_range]; omega
  · intro j1 _ j2 _ h; exact Fin.ext h
  · intro k hk
    rw [Finset.mem_range] at hk
    refine ⟨⟨k, by omega⟩, ?_, rfl⟩
    rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, by simp only; omega⟩
  · intro j _
    rw [hFU j, lucas_mod5 n.1 j.1]; ring

private lemma step5_V1 : ∀ n : Fin 23, step5 V1 n = V2 n := by decide
private lemma step5_V2 : ∀ n : Fin 23, step5 V2 n = V3 n := by decide
private lemma step5_V3 : ∀ n : Fin 23, step5 V3 n = V4 n := by decide
private lemma step5_V4 : ∀ n : Fin 23, step5 V4 n = V5 n := by decide

private lemma iter5_g_one (n : Fin 23) : iter5 (fun m => (m : ZMod 5)) 1 n.1 = V1 n := by
  simp only [iter5, comp5]
  rw [Finset.sum_eq_single 1]
  · simp only [↓reduceIte, one_mul, divPow5_id, Nat.choose_one_right]
    fin_cases n <;> decide
  · intro k _ hne; simp [hne]
  · intro h
    have hn0 : n.1 = 0 := by
      by_contra hne; exact h (Finset.mem_range.mpr (by omega))
    have : n = 0 := Fin.ext hn0
    subst this; decide

private lemma iter5_g_five (n : Fin 23) : iter5 (fun m => (m : ZMod 5)) 5 n.1 = V5 n := by
  have h2 : ∀ m : Fin 23, iter5 (fun j => (j : ZMod 5)) 2 m.1 = V2 m := fun m => by
    change comp5 (iter5 (fun j => (j : ZMod 5)) 1) (fun j => (j : ZMod 5)) m.1 = V2 m
    rw [comp5_eq_step5 _ V1 iter5_g_one m, step5_V1 m]
  have h3 : ∀ m : Fin 23, iter5 (fun j => (j : ZMod 5)) 3 m.1 = V3 m := fun m => by
    change comp5 (iter5 (fun j => (j : ZMod 5)) 2) (fun j => (j : ZMod 5)) m.1 = V3 m
    rw [comp5_eq_step5 _ V2 h2 m, step5_V2 m]
  have h4 : ∀ m : Fin 23, iter5 (fun j => (j : ZMod 5)) 4 m.1 = V4 m := fun m => by
    change comp5 (iter5 (fun j => (j : ZMod 5)) 3) (fun j => (j : ZMod 5)) m.1 = V4 m
    rw [comp5_eq_step5 _ V3 h3 m, step5_V3 m]
  change comp5 (iter5 (fun j => (j : ZMod 5)) 4) (fun j => (j : ZMod 5)) n.1 = V5 n
  rw [comp5_eq_step5 _ V4 h4 n, step5_V4 n]

private lemma exp5_x_eq_one :
    ∀ n : ℕ, exp5 (fun m => if m = 1 then (1 : ZMod 5) else 0) n = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => rw [exp5]
    | succ n =>
      rw [exp5, Fin.sum_univ_succ]
      simp only [Fin.val_zero, Nat.choose_zero_right, Nat.cast_one, ↓reduceIte, one_mul,
        Nat.sub_zero, ih n (by omega)]
      have hrest : ∑ j : Fin n,
          (Nat.choose n j.succ.1 : ZMod 5) * (if j.succ.1 + 1 = 1 then (1 : ZMod 5) else 0) *
            exp5 (fun m => if m = 1 then (1 : ZMod 5) else 0) (n - j.succ.1) = 0 := by
        apply Finset.sum_eq_zero; intro j _; simp
      rw [hrest, add_zero]

private lemma iter5_g_five_lt22 (m : ℕ) (hm : m ≤ 21) :
    iter5 (fun j => (j : ZMod 5)) 5 m = if m = 1 then 1 else 0 := by
  have h := iter5_g_five ⟨m, by omega⟩
  rw [h]
  have : ∀ x : Fin 23, x.1 ≤ 21 → V5 x = if x.1 = 1 then 1 else 0 := by decide
  exact this ⟨m, by omega⟩ hm

private lemma a_mod5_le22 : ∀ n : ℕ, n ≤ 22 → (a n : ZMod 5) = (n : ZMod 5) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero => rw [a]; simp
    | succ n =>
      conv_lhs => rw [a]
      rw [Int.cast_mul, Int.cast_natCast, egfExp_cast5]
      have heq_iter :
          ∀ m ≤ n, (egfIter (fun j => if _h : j < n + 1 then a j else 0) 5 m : ZMod 5) =
            iter5 (fun j => (j : ZMod 5)) 5 m := by
        intro m hm
        rw [egfIter_cast5]
        apply iter5_congr _ 5 m hm
        intro j hj
        have hlt : j < n + 1 := by omega
        simp only [dif_pos hlt]
        exact ih j hlt (by omega)
      rw [exp5_congr heq_iter n (le_refl n)]
      have hsmall : ∀ m ≤ n, iter5 (fun j => (j : ZMod 5)) 5 m = if m = 1 then 1 else 0 :=
        fun m hm => iter5_g_five_lt22 m (by omega)
      rw [exp5_congr hsmall n (le_refl n), exp5_x_eq_one n, mul_one]

theorem a_23_mod5 : (a 23 : ZMod 5) = 2 := by
  conv_lhs => rw [a]
  rw [Int.cast_mul, Int.cast_natCast, egfExp_cast5]
  have heq_iter :
      ∀ m ≤ 22, (egfIter (fun j => if _h : j < 23 then a j else 0) 5 m : ZMod 5) =
        iter5 (fun j => (j : ZMod 5)) 5 m := by
    intro m hm
    rw [egfIter_cast5]
    apply iter5_congr _ 5 m hm
    intro j hj
    have hlt : j < 23 := by omega
    simp only [dif_pos hlt]
    exact a_mod5_le22 j (by omega)
  rw [exp5_congr heq_iter 22 (le_refl 22)]
  have hexp22 : exp5 (iter5 (fun j => (j : ZMod 5)) 5) 22 = 4 := by
    rw [exp5]
    have hsplit :
        ∑ j : Fin 22,
          (Nat.choose 21 j.1 : ZMod 5) * iter5 (fun i => (i : ZMod 5)) 5 (j.1 + 1) *
            exp5 (iter5 (fun i => (i : ZMod 5)) 5) (21 - j.1) =
        (Nat.choose 21 0 : ZMod 5) * iter5 (fun i => (i : ZMod 5)) 5 1 *
          exp5 (iter5 (fun i => (i : ZMod 5)) 5) 21 +
        (Nat.choose 21 21 : ZMod 5) * iter5 (fun i => (i : ZMod 5)) 5 22 *
          exp5 (iter5 (fun i => (i : ZMod 5)) 5) 0 := by
      have hsub : ∀ j : Fin 22, j ≠ ⟨0, by omega⟩ → j ≠ ⟨21, by omega⟩ →
          (Nat.choose 21 j.1 : ZMod 5) * iter5 (fun i => (i : ZMod 5)) 5 (j.1 + 1) *
            exp5 (iter5 (fun i => (i : ZMod 5)) 5) (21 - j.1) = 0 := by
        intro j hne0 hne21
        have hlt : j.1 + 1 ≤ 21 := by
          have := j.2
          have h1 : j.1 ≠ 21 := fun heq => hne21 (Fin.ext heq)
          omega
        have hne1 : j.1 + 1 ≠ 1 := by
          have h0 : j.1 ≠ 0 := fun heq => hne0 (Fin.ext heq)
          omega
        rw [iter5_g_five_lt22 (j.1 + 1) hlt, if_neg hne1, mul_zero, zero_mul]
      rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
      have hmid : ∑ x : Fin 20,
          (Nat.choose 21 x.castSucc.succ.1 : ZMod 5) *
            iter5 (fun i => (i : ZMod 5)) 5 (x.castSucc.succ.1 + 1) *
            exp5 (iter5 (fun i => (i : ZMod 5)) 5) (21 - x.castSucc.succ.1) = 0 := by
        apply Finset.sum_eq_zero
        intro x _
        exact hsub x.castSucc.succ (by intro h; have := congrArg Fin.val h; simp at this)
          (by intro h; have := congrArg Fin.val h; simp at this; omega)
      rw [hmid, zero_add]
      simp
    rw [hsplit]
    have he21 : exp5 (iter5 (fun i => (i : ZMod 5)) 5) 21 = 1 := by
      rw [exp5_congr (fun m hm => iter5_g_five_lt22 m (by omega)) 21 (le_refl 21), exp5_x_eq_one 21]
    have he0 : exp5 (iter5 (fun i => (i : ZMod 5)) 5) 0 = 1 := by rw [exp5]
    have hi1 : iter5 (fun i => (i : ZMod 5)) 5 1 = 1 :=
      (iter5_g_five ⟨1, by omega⟩).trans (by decide)
    have hi22 : iter5 (fun i => (i : ZMod 5)) 5 22 = 3 :=
      (iter5_g_five ⟨22, by omega⟩).trans (by decide)
    rw [he21, he0, hi1, hi22]
    simp only [Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, one_mul, mul_one]
    decide
  rw [hexp22]
  decide

end OeisA396805Disproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a396805.main) := by
  intro h
  have h23 : OMA.S_oeis_a396805.a 23 ≡ (23 : ℤ) [ZMOD ((5 : ℕ) : ℤ)] := h 23 (by omega)
  rw [← ZMod.intCast_eq_intCast_iff, OeisA396805Disproof.a_23_mod5] at h23
  exact absurd h23 (by decide)

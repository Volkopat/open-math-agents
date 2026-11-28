import OMAStatements.S_oeis_a350759
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic

namespace OeisA350759Proof

open OMA.S_oeis_a350759

private def hMul (f g : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℤ) * f j * g (n - j)

private def hShift (f : ℕ → ℤ) (n : ℕ) : ℤ :=
  f (n + 1)

private def egfPow (G : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0, n => if n = 0 then 1 else 0
  | k + 1, n => hMul G (egfPow G k) n

private def egfDivPow (G : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0, n => if n = 0 then 1 else 0
  | _ + 1, 0 => 0
  | k + 1, n + 1 =>
    ∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℤ) * G (j + 1) * egfDivPow G k (n - j)

private lemma hMul_smul_right (c : ℤ) (f g : ℕ → ℤ) (n : ℕ) :
    hMul f (fun m => c * g m) n = c * hMul f g n := by
  unfold hMul
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _; ring

private lemma hShift_hMul (f g : ℕ → ℤ) (n : ℕ) :
    hShift (hMul f g) n = hMul (hShift f) g n + hMul f (hShift g) n := by
  unfold hShift hMul
  rw [Finset.sum_range_succ']
  have h1 :
      (∑ k ∈ Finset.range (n + 1),
        (Nat.choose (n + 1) (k + 1) : ℤ) * f (k + 1) * g (n + 1 - (k + 1))) =
      (∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℤ) * f (k + 1) * g (n - k)) +
      (∑ k ∈ Finset.range (n + 1), (Nat.choose n (k + 1) : ℤ) * f (k + 1) * g (n - k)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.choose_succ_succ, Nat.cast_add, Nat.add_sub_add_right]
    ring
  rw [h1]
  have h2 :
      (∑ k ∈ Finset.range (n + 1), (Nat.choose n (k + 1) : ℤ) * f (k + 1) * g (n - k)) +
        (Nat.choose (n + 1) 0 : ℤ) * f 0 * g (n + 1 - 0) =
      ∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℤ) * f j * g (n - j + 1) := by
    rw [Finset.sum_range_succ (fun k => (Nat.choose n (k + 1) : ℤ) * f (k + 1) * g (n - k)) n]
    simp only [Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero, Nat.choose_zero_right,
      Nat.cast_one, one_mul, Nat.sub_zero]
    rw [Finset.sum_range_succ' (fun j => (Nat.choose n j : ℤ) * f j * g (n - j + 1)) n]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    have hsub : n - (k + 1) + 1 = n - k := by omega
    rw [hsub]
  rw [add_assoc, h2]

private lemma hShift_egfPow (G : ℕ → ℤ) :
    ∀ k n : ℕ, hShift (egfPow G (k + 1)) n =
      ((k + 1 : ℕ) : ℤ) * hMul (hShift G) (egfPow G k) n := by
  intro k
  induction k with
  | zero =>
    intro n
    change ∑ j ∈ Finset.range (n + 1 + 1), (Nat.choose (n + 1) j : ℤ) * G j * (if n + 1 - j = 0 then 1 else 0) =
      ((0 + 1 : ℕ) : ℤ) * ∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℤ) * G (j + 1) * (if n - j = 0 then 1 else 0)
    have hL : (∑ j ∈ Finset.range (n + 1 + 1), (Nat.choose (n + 1) j : ℤ) * G j * (if n + 1 - j = 0 then 1 else 0)) = G (n + 1) := by
      rw [Finset.sum_eq_single (n + 1)]
      · simp
      · intro j hj hne; rw [Finset.mem_range] at hj; simp [show n + 1 - j ≠ 0 by omega]
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    have hR : (∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℤ) * G (j + 1) * (if n - j = 0 then 1 else 0)) = G (n + 1) := by
      rw [Finset.sum_eq_single n]
      · simp
      · intro j hj hne; rw [Finset.mem_range] at hj; simp [show n - j ≠ 0 by omega]
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    rw [hL, hR]; simp
  | succ k ih =>
    intro n
    change hShift (hMul G (egfPow G (k + 1))) n = _
    rw [hShift_hMul, show hShift (egfPow G (k + 1)) = fun m => ((k + 1 : ℕ) : ℤ) * hMul (hShift G) (egfPow G k) m from funext ih]
    rw [hMul_smul_right]
    have hassoc : ∀ a b c : ℕ → ℤ, ∀ m : ℕ, hMul a (hMul b c) m = hMul b (hMul a c) m := by
      intro a b c m
      unfold hMul
      simp_rw [Finset.mul_sum]
      have h1 : ∀ f1 f2 : ℕ → ℤ,
          ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m - i + 1),
            (Nat.choose m i : ℤ) * f1 i * ((Nat.choose (m - i) j : ℤ) * f2 j * c (m - i - j)) =
          ∑ p ∈ (Finset.range (m + 1) ×ˢ Finset.range (m + 1)).filter (fun p => p.1 + p.2 ≤ m),
            (Nat.choose m p.1 : ℤ) * (Nat.choose (m - p.1) p.2 : ℤ) * f1 p.1 * f2 p.2 * c (m - p.1 - p.2) := by
        intro f1 f2
        rw [Finset.sum_sigma']
        apply Finset.sum_bij (fun x _ => (x.1, x.2))
        · intro x hx
          simp only [Finset.mem_sigma, Finset.mem_range] at hx
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
          omega
        · intro x1 _ x2 _ h
          cases x1; cases x2; simp only [Prod.mk.injEq] at h; rcases h with ⟨rfl, rfl⟩; rfl
        · intro p hp
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
          exact ⟨⟨p.1, p.2⟩, by simp only [Finset.mem_sigma, Finset.mem_range]; omega, rfl⟩
        · intro x _; ring
      rw [h1 a b, h1 b a]
      apply Finset.sum_bij (fun p _ => (p.2, p.1))
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢; omega
      · intro p1 _ p2 _ h
        cases p1; cases p2; simp only [Prod.mk.injEq] at h; rcases h with ⟨rfl, rfl⟩; rfl
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
        exact ⟨(p.2, p.1), by simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]; omega, rfl⟩
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
        have hch : Nat.choose m p.1 * Nat.choose (m - p.1) p.2 =
            Nat.choose m p.2 * Nat.choose (m - p.2) p.1 := by
          have hL := @Nat.choose_mul m (p.1 + p.2) p.1 (by omega)
          have hR := @Nat.choose_mul m (p.2 + p.1) p.2 (by omega)
          rw [Nat.add_sub_cancel_left] at hL hR
          rw [add_comm p.2 p.1] at hR
          have hsym : Nat.choose (p.1 + p.2) p.1 = Nat.choose (p.1 + p.2) p.2 := by
            rw [← Nat.choose_symm (by omega : p.1 ≤ p.1 + p.2), Nat.add_sub_cancel_left]
          rw [← hL, hsym, hR]
        have hchZ : (Nat.choose m p.1 : ℤ) * (Nat.choose (m - p.1) p.2 : ℤ) =
            (Nat.choose m p.2 : ℤ) * (Nat.choose (m - p.2) p.1 : ℤ) := by exact_mod_cast hch
        have hsub : m - p.1 - p.2 = m - p.2 - p.1 := by omega
        rw [hsub]
        calc (Nat.choose m p.1 : ℤ) * (Nat.choose (m - p.1) p.2 : ℤ) * a p.1 * b p.2 * c (m - p.2 - p.1)
            = ((Nat.choose m p.1 : ℤ) * (Nat.choose (m - p.1) p.2 : ℤ)) * (a p.1 * b p.2 * c (m - p.2 - p.1)) := by ring
          _ = ((Nat.choose m p.2 : ℤ) * (Nat.choose (m - p.2) p.1 : ℤ)) * (a p.1 * b p.2 * c (m - p.2 - p.1)) := by rw [hchZ]
          _ = _ := by ring
    rw [hassoc G (hShift G) (egfPow G k) n]
    change hMul (hShift G) (egfPow G (k + 1)) n + ((k + 1 : ℕ) : ℤ) * hMul (hShift G) (egfPow G (k + 1)) n = _
    push_cast; ring

private lemma egfPow_zero_of_pos (G : ℕ → ℤ) (hG0 : G 0 = 0) :
    ∀ k : ℕ, 1 ≤ k → egfPow G k 0 = 0 := by
  intro k hk
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0) with ⟨m, rfl⟩
  simp [egfPow, hMul, hG0]

private lemma egfPow_eq_factorial_mul_divPow (G : ℕ → ℤ) (hG0 : G 0 = 0) :
    ∀ k n : ℕ, egfPow G k n = (k.factorial : ℤ) * egfDivPow G k n := by
  intro k
  induction k with
  | zero => intro n; simp [egfPow, egfDivPow]
  | succ k ih =>
    intro n
    cases n with
    | zero =>
      rw [egfPow_zero_of_pos G hG0 (k + 1) (by omega)]
      simp [egfDivPow]
    | succ n =>
      change hShift (egfPow G (k + 1)) n = _
      rw [hShift_egfPow G k n]
      unfold hMul hShift egfDivPow
      simp_rw [ih]
      rw [Nat.factorial_succ, Nat.cast_mul, mul_assoc, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _; ring

private lemma egfDivPow_zero_of_gt (G : ℕ → ℤ) :
    ∀ k n : ℕ, n < k → egfDivPow G k n = 0 := by
  intro k
  induction k with
  | zero => intro n hn; omega
  | succ k ih =>
    intro n hn
    cases n with
    | zero => rfl
    | succ n =>
      unfold egfDivPow
      apply Finset.sum_eq_zero
      intro j hj
      rw [Finset.mem_range] at hj
      rw [ih (n - j) (by omega), mul_zero]

private lemma egfExp_eq_sum_divPow (G : ℕ → ℤ) :
    ∀ n : ℕ, egfExp G n = ∑ k ∈ Finset.range (n + 1), egfDivPow G k n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [egfExp, egfDivPow]
    | succ n =>
      rw [egfExp, Finset.sum_range_succ']
      simp only [egfDivPow, Nat.succ_ne_zero, ↓reduceIte, add_zero]
      rw [Finset.sum_comm]
      rw [Fin.sum_univ_eq_sum_range (fun j => (Nat.choose n j : ℤ) * G (j + 1) * egfExp G (n - j)) (n + 1)]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      rw [← Finset.mul_sum, ih (n - j) (by omega)]
      congr 1
      apply Finset.sum_subset (fun k hk => by rw [Finset.mem_range] at hk ⊢; omega)
      intro k hk hnot
      rw [Finset.mem_range] at hk hnot
      exact egfDivPow_zero_of_gt G k (n - j) (by omega)

private lemma egfDivPow_one (G : ℕ → ℤ) (n : ℕ) (hn : 1 ≤ n) :
    egfDivPow G 1 n = G n := by
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0) with ⟨m, rfl⟩
  unfold egfDivPow
  rw [Finset.sum_eq_single m]
  · simp [egfDivPow]
  · intro j hj hne
    rw [Finset.mem_range] at hj
    simp [egfDivPow, show m - j ≠ 0 by omega]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

private lemma egfDivPow_F_zero_of_two_mul_gt :
    ∀ k n : ℕ, n < 2 * k → egfDivPow F k n = 0 := by
  intro k
  induction k with
  | zero => intro n hn; omega
  | succ k ih =>
    intro n hn
    cases n with
    | zero => rfl
    | succ n =>
      unfold egfDivPow
      apply Finset.sum_eq_zero
      intro j hj
      rw [Finset.mem_range] at hj
      by_cases hj0 : j = 0
      · subst hj0
        have hF1 : F 1 = 0 := by simp [F]
        rw [hF1, mul_zero, zero_mul]
      · rw [ih (n - j) (by omega), mul_zero]

private lemma prime_dvd_egfPow_of_ge2 (G : ℕ → ℤ) (hG0 : G 0 = 0) {p k : ℕ}
    (hp : p.Prime) (hk2 : 2 ≤ k) :
    (p : ℤ) ∣ egfPow G k p := by
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0) with ⟨m, rfl⟩
  unfold egfPow hMul
  apply Finset.dvd_sum
  intro j hj
  rw [Finset.mem_range] at hj
  by_cases hj0 : j = 0
  · subst hj0; rw [hG0, mul_zero, zero_mul]; exact dvd_zero _
  · by_cases hjp : j = p
    · subst hjp
      rw [Nat.sub_self, egfPow_zero_of_pos G hG0 m (by omega), mul_zero]
      exact dvd_zero _
    · have hch : p ∣ Nat.choose p j := hp.dvd_choose_self hj0 (by omega)
      have hchZ : (p : ℤ) ∣ (Nat.choose p j : ℤ) := Int.natCast_dvd_natCast.mpr hch
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hchZ _) _

private lemma b_prime_modEq_neg_one {p : ℕ} (hp : p.Prime) :
    b p ≡ -1 [ZMOD (p : ℤ)] := by
  have hp2 : 2 ≤ p := hp.two_le
  have hF0 : F 0 = 0 := rfl
  unfold b
  rw [egfExp_eq_sum_divPow F p]
  have hmem1 : 1 ∈ Finset.range (p + 1) := Finset.mem_range.mpr (by omega)
  rw [← Finset.add_sum_erase _ _ hmem1, egfDivPow_one F p (by omega)]
  have hrest : (p : ℤ) ∣ ∑ k ∈ (Finset.range (p + 1)).erase 1, egfDivPow F k p := by
    apply Finset.dvd_sum
    intro k hk
    rw [Finset.mem_erase, Finset.mem_range] at hk
    by_cases hk0 : k = 0
    · subst hk0
      simp only [egfDivPow, show p ≠ 0 by omega, ↓reduceIte]
      exact dvd_zero _
    · by_cases hkp : k = p
      · rw [hkp, egfDivPow_F_zero_of_two_mul_gt p p (by omega)]
        exact dvd_zero _
      · have hk2 : 2 ≤ k := by omega
        have hdvd_pow : (p : ℤ) ∣ (k.factorial : ℤ) * egfDivPow F k p := by
          rw [← egfPow_eq_factorial_mul_divPow F hF0 k p]
          exact prime_dvd_egfPow_of_ge2 F hF0 hp hk2
        have hcop_nat : Nat.Coprime p k.factorial := by
          rw [hp.coprime_iff_not_dvd]
          intro hd
          have := hp.dvd_factorial.mp hd
          omega
        have hcop_int : IsCoprime (p : ℤ) (k.factorial : ℤ) :=
          Int.isCoprime_iff_nat_coprime.mpr (by simpa using hcop_nat)
        exact hcop_int.dvd_of_dvd_mul_left hdvd_pow
  have hFp : F p ≡ -1 [ZMOD (p : ℤ)] := by
    unfold F
    rw [if_neg (by omega : p ≠ 0)]
    rw [Int.modEq_iff_dvd]
    by_cases hp_eq2 : p = 2
    · subst hp_eq2; norm_num
    · have hodd : Odd p := hp.odd_of_ne_two hp_eq2
      have hneg1 : (-1 : ℤ) ^ p = -1 := Odd.neg_one_pow hodd
      rw [hneg1]
      refine ⟨-1, ?_⟩; ring
  have hsum0 : (∑ k ∈ (Finset.range (p + 1)).erase 1, egfDivPow F k p) ≡ 0 [ZMOD (p : ℤ)] :=
    Int.modEq_zero_iff_dvd.mpr hrest
  simpa using hFp.add hsum0

private lemma b_prime_succ_dvd {p : ℕ} (hp : p.Prime) :
    (p : ℤ) ∣ b (p + 1) := by
  unfold b
  rw [egfExp, Fin.sum_univ_eq_sum_range (fun j => (Nat.choose p j : ℤ) * F (j + 1) * egfExp F (p - j)) (p + 1)]
  apply Finset.dvd_sum
  intro j hj
  rw [Finset.mem_range] at hj
  by_cases hj0 : j = 0
  · subst hj0
    have hF1 : F 1 = 0 := by simp [F]
    rw [hF1, mul_zero, zero_mul]; exact dvd_zero _
  · by_cases hjp : j = p
    · rw [hjp]
      have hFp1 : F (p + 1) = (-1 : ℤ) ^ (p + 1) * (-(p : ℤ)) := by
        unfold F; rw [if_neg (by omega)]; push_cast; ring
      rw [hFp1]
      exact ⟨(Nat.choose p p : ℤ) * (-1 : ℤ) ^ (p + 1) * (-1) * egfExp F (p - p), by ring⟩
    · have hch : p ∣ Nat.choose p j := hp.dvd_choose_self hj0 (by omega)
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hch) _) _

private lemma b_one : b 1 = 0 := by
  simp [b, egfExp, F]

private lemma b_two : b 2 = -1 := by
  unfold b
  rw [egfExp, Fin.sum_univ_two]
  simp [egfExp, F]

private lemma stirling1_zero_of_lt : ∀ n k : ℕ, n < k → stirling1 n k = 0 := by
  intro n
  induction n with
  | zero =>
    intro k hk
    cases k with
    | zero => omega
    | succ k => rfl
  | succ n ih =>
    intro k hk
    cases k with
    | zero => omega
    | succ k =>
      unfold stirling1
      rw [ih k (by omega), ih (k + 1) (by omega)]
      ring

private lemma stirling1_self : ∀ n : ℕ, stirling1 n n = 1 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold stirling1
    rw [ih, stirling1_zero_of_lt n (n + 1) (by omega)]
    ring

private lemma poly_falling_eq_stirling1 (p : ℕ) :
    ∀ n : ℕ,
      ∏ i ∈ Finset.range n, (Polynomial.X - Polynomial.C (i : ZMod p)) =
      ∑ k ∈ Finset.range (n + 1), Polynomial.C (stirling1 n k : ZMod p) * Polynomial.X ^ k := by
  intro n
  induction n with
  | zero => simp [stirling1]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, mul_sub, Finset.sum_mul, Finset.sum_mul]
    have hX :
        (∑ k ∈ Finset.range (n + 1), Polynomial.C (stirling1 n k : ZMod p) * Polynomial.X ^ k * Polynomial.X) =
        ∑ k ∈ Finset.range (n + 2), Polynomial.C (if k = 0 then 0 else (stirling1 n (k - 1) : ZMod p)) * Polynomial.X ^ k := by
      conv_rhs => rw [Finset.sum_range_succ']
      simp only [↓reduceIte, map_zero, zero_mul, add_zero, Nat.succ_ne_zero, Nat.add_sub_cancel]
      apply Finset.sum_congr rfl
      intro k _; rw [pow_succ]; ring
    have hC :
        (∑ k ∈ Finset.range (n + 1), Polynomial.C (stirling1 n k : ZMod p) * Polynomial.X ^ k * Polynomial.C (n : ZMod p)) =
        ∑ k ∈ Finset.range (n + 2), Polynomial.C ((n : ZMod p) * (stirling1 n k : ZMod p)) * Polynomial.X ^ k := by
      rw [Finset.sum_range_succ _ (n + 1)]
      rw [stirling1_zero_of_lt n (n + 1) (by omega)]
      simp only [Int.cast_zero, mul_zero, map_zero, zero_mul, add_zero]
      apply Finset.sum_congr rfl
      intro k _; rw [map_mul]; ring
    rw [hX, hC, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    cases k with
    | zero =>
      cases n with
      | zero => simp [stirling1]
      | succ n => simp [stirling1]
    | succ k =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, stirling1, Int.cast_sub,
        Int.cast_mul, Int.cast_natCast, map_sub, map_mul]
      ring

private lemma stirling1_prime_mod {p : ℕ} (hp : p.Prime) (k : ℕ) (hk : k ≤ p) :
    (stirling1 p k : ZMod p) = if k = p then 1 else if k = 1 then -1 else 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hprod : ∏ i ∈ Finset.range p, (Polynomial.X - Polynomial.C (i : ZMod p)) =
      Polynomial.X ^ p - Polynomial.X := by
    have hbij : ∏ i ∈ Finset.range p, (Polynomial.X - Polynomial.C (i : ZMod p)) =
        ∏ a : ZMod p, (Polynomial.X - Polynomial.C a) := by
      rw [← Fin.prod_univ_eq_prod_range (fun i => Polynomial.X - Polynomial.C (i : ZMod p)) p]
      apply Finset.prod_bij (fun (i : Fin p) _ => (i.1 : ZMod p))
      · intro _ _; exact Finset.mem_univ _
      · intro a _ b _ h
        ext
        have ha : a.1 < p := a.2
        have hb : b.1 < p := b.2
        have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
        rw [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hmod
        exact hmod
      · intro a _
        exact ⟨⟨a.val, ZMod.val_lt a⟩, Finset.mem_univ _, ZMod.natCast_zmod_val a⟩
      · intro _ _; rfl
    rw [hbij]
    have hmonic : (Polynomial.X ^ p - Polynomial.X : Polynomial (ZMod p)).Monic := by
      apply Polynomial.Monic.sub_of_left (Polynomial.monic_X_pow p)
      rw [Polynomial.degree_X_pow, Polynomial.degree_X]
      exact_mod_cast hp.one_lt
    have hroots : (Polynomial.X ^ p - Polynomial.X : Polynomial (ZMod p)).roots = Finset.univ.val := by
      simpa [ZMod.card] using FiniteField.roots_X_pow_card_sub_X (ZMod p)
    have hdeg : (Polynomial.X ^ p - Polynomial.X : Polynomial (ZMod p)).natDegree = p :=
      FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) hp.one_lt
    have hcard : Multiset.card (Polynomial.X ^ p - Polynomial.X : Polynomial (ZMod p)).roots =
        (Polynomial.X ^ p - Polynomial.X : Polynomial (ZMod p)).natDegree := by
      rw [hroots, Finset.card_val, Finset.card_univ, ZMod.card, hdeg]
    have hfac := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic hcard
    rw [hroots] at hfac
    exact hfac
  have hpoly := (poly_falling_eq_stirling1 p p).symm.trans hprod
  have hc := congrArg (fun f => Polynomial.coeff f k) hpoly
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_sub, Polynomial.coeff_X] at hc
  rw [Finset.sum_eq_single k] at hc
  · simp only [↓reduceIte, mul_one] at hc
    rw [hc]
    have hp2 : 2 ≤ p := hp.two_le
    by_cases hkp : k = p
    · rw [hkp]; simp [show 1 ≠ p by omega]
    · rw [if_neg hkp]
      by_cases hk1 : k = 1
      · rw [hk1]; simp [show 1 ≠ p by omega]
      · simp [hk1, Ne.symm hk1, hkp]
  · intro j _ hne; simp [Ne.symm hne]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

private lemma a_prime_mod {p : ℕ} (hp : p.Prime) :
    (a p : ZMod p) = 1 := by
  have hp2 : 2 ≤ p := hp.two_le
  unfold a
  rw [Int.cast_sum]
  rw [Finset.sum_eq_single p]
  · rw [stirling1_self, mul_one, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
    have hbp : (b p : ZMod p) = -1 := by
      have h := (ZMod.intCast_eq_intCast_iff (b p) (-1) p).mpr (b_prime_modEq_neg_one hp)
      simpa using h
    rw [hbp]
    by_cases hp_eq2 : p = 2
    · subst hp_eq2; decide
    · have hodd : Odd p := hp.odd_of_ne_two hp_eq2
      rw [hodd.neg_one_pow]; ring
  · intro k hk hne
    rw [Finset.mem_range] at hk
    rw [Int.cast_mul, Int.cast_mul, stirling1_prime_mod hp k (by omega)]
    rw [if_neg hne]
    by_cases hk1 : k = 1
    · subst hk1; simp [b_one]
    · simp [hk1]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

private lemma a_prime_succ_mod {p : ℕ} (hp : p.Prime) :
    (a (p + 1) : ZMod p) = 1 := by
  have hp2 : 2 ≤ p := hp.two_le
  unfold a
  rw [Int.cast_sum]
  rw [Finset.sum_eq_single 2]
  · rw [Int.cast_mul, Int.cast_mul, b_two]
    have hs2 : (stirling1 (p + 1) 2 : ZMod p) = -1 := by
      unfold stirling1
      rw [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, sub_zero]
      rw [stirling1_prime_mod hp 1 (by omega)]
      rw [if_neg (by omega : 1 ≠ p), if_pos rfl]
    rw [hs2]; norm_num
  · intro k hk hne
    rw [Finset.mem_range] at hk
    rw [Int.cast_mul, Int.cast_mul]
    cases k with
    | zero => simp [stirling1]
    | succ k =>
      by_cases hk0 : k = 0
      · subst hk0; simp [b_one]
      · by_cases hkp : k = p
        · rw [hkp]
          have hb0 : (b (p + 1) : ZMod p) = 0 :=
            (ZMod.intCast_zmod_eq_zero_iff_dvd (b (p + 1)) p).mpr (b_prime_succ_dvd hp)
          rw [hb0, mul_zero, zero_mul]
        · have hs0 : (stirling1 (p + 1) (k + 1) : ZMod p) = 0 := by
            unfold stirling1
            rw [Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, sub_zero]
            rw [stirling1_prime_mod hp k (by omega)]
            rw [if_neg hkp, if_neg (by omega : k ≠ 1)]
          rw [hs0, mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

end OeisA350759Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a350759.main := by
  intro p hp
  rw [← ZMod.intCast_eq_intCast_iff]
  simp only [Int.cast_sub, Int.cast_add, Int.cast_ofNat, Int.cast_zero,
    OeisA350759Proof.a_prime_mod hp, OeisA350759Proof.a_prime_succ_mod hp]
  ring

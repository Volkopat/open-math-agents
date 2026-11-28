import OMAStatements.S_oeis_a081798

-- Problem: A081798: a(n) = Sum_{k = 0..n} C(n,k) C(n+k,k) C(n+2k,k).
-- Upstream: statements/oeis-a081798.lean (declaration OMA.S_oeis_a081798.main)
-- Credit: @advancedsuperintelligence

namespace A081798Proof

open Finset

private def F (n k : ℕ) : ℚ :=
  (n.choose k : ℚ) * ((n + k).choose k : ℚ) * ((n + 2 * k).choose k : ℚ)

private lemma F_eq_zero_of_lt {n k : ℕ} (h : n < k) : F n k = 0 := by
  simp [F, Nat.choose_eq_zero_of_lt h]

private lemma a_cast_eq_sum (m n : ℕ) (hmn : m ≤ n) :
    (OMA.S_oeis_a081798.a m : ℚ) = ∑ k ∈ Finset.range (n + 1), F m k := by
  unfold OMA.S_oeis_a081798.a
  push_cast
  change (∑ k ∈ Finset.range (m + 1), F m k) = ∑ k ∈ Finset.range (n + 1), F m k
  have hsub : Finset.range (m + 1) ⊆ Finset.range (n + 1) :=
    Finset.range_mono (Nat.succ_le_succ hmn)
  apply Finset.sum_subset hsub
  intro k _ hk
  rw [Finset.mem_range] at hk
  exact F_eq_zero_of_lt (by omega)

private lemma F_eq_fact {n k : ℕ} (hk : k ≤ n) :
    F n k = ((n + 2 * k).factorial : ℚ) /
      (((k.factorial : ℚ) ^ 3) * ((n - k).factorial : ℚ)) := by
  have h1 : (n.choose k : ℚ) * (k.factorial : ℚ) * ((n - k).factorial : ℚ) =
      (n.factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have h2 : ((n + k).choose k : ℚ) * (k.factorial : ℚ) * (n.factorial : ℚ) =
      ((n + k).factorial : ℚ) := by
    have := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left k n)
    rw [Nat.add_sub_cancel] at this
    exact_mod_cast this
  have h3 : ((n + 2 * k).choose k : ℚ) * (k.factorial : ℚ) * ((n + k).factorial : ℚ) =
      ((n + 2 * k).factorial : ℚ) := by
    have hle : k ≤ n + 2 * k := by omega
    have hsub : n + 2 * k - k = n + k := by omega
    have := Nat.choose_mul_factorial_mul_factorial hle
    rw [hsub] at this
    exact_mod_cast this
  have hkf : (k.factorial : ℚ) ≠ 0 := by positivity
  have hnf : (n.factorial : ℚ) ≠ 0 := by positivity
  have hnkf : ((n + k).factorial : ℚ) ≠ 0 := by positivity
  have hnmkf : ((n - k).factorial : ℚ) ≠ 0 := by positivity
  unfold F
  rw [eq_div_iff (by positivity)]
  have hprod :
      (n.choose k : ℚ) * ((n + k).choose k : ℚ) * ((n + 2 * k).choose k : ℚ) *
        ((k.factorial : ℚ) ^ 3 * ((n - k).factorial : ℚ)) *
        ((n.factorial : ℚ) * ((n + k).factorial : ℚ)) =
      ((n + 2 * k).factorial : ℚ) * ((n.factorial : ℚ) * ((n + k).factorial : ℚ)) := by
    calc
      (n.choose k : ℚ) * ((n + k).choose k : ℚ) * ((n + 2 * k).choose k : ℚ) *
          ((k.factorial : ℚ) ^ 3 * ((n - k).factorial : ℚ)) *
          ((n.factorial : ℚ) * ((n + k).factorial : ℚ))
        = ((n.choose k : ℚ) * (k.factorial : ℚ) * ((n - k).factorial : ℚ)) *
          (((n + k).choose k : ℚ) * (k.factorial : ℚ) * (n.factorial : ℚ)) *
          (((n + 2 * k).choose k : ℚ) * (k.factorial : ℚ) * ((n + k).factorial : ℚ)) := by ring
      _ = (n.factorial : ℚ) * ((n + k).factorial : ℚ) * ((n + 2 * k).factorial : ℚ) := by
          rw [h1, h2, h3]
      _ = ((n + 2 * k).factorial : ℚ) * ((n.factorial : ℚ) * ((n + k).factorial : ℚ)) := by ring
  exact mul_right_cancel₀ (mul_ne_zero hnf hnkf) hprod

private def H (n k : ℕ) : ℚ :=
  if 1 ≤ k ∧ k ≤ n then
    -3 * (3 * (n : ℚ) - 4) * (3 * (n : ℚ) - 2) * (3 * (n : ℚ) - 1) *
      (((n + 2 * k - 3).factorial : ℚ) /
        ((((k - 1).factorial : ℚ) ^ 3) * ((n - k).factorial : ℚ)))
  else 0

private lemma fact_succ_q (m : ℕ) :
    ((m + 1).factorial : ℚ) = ((m : ℚ) + 1) * (m.factorial : ℚ) := by
  rw [Nat.factorial_succ]
  push_cast
  ring

private lemma fact_step2 (m : ℕ) :
    ((m + 2).factorial : ℚ) = ((m : ℚ) + 2) * ((m : ℚ) + 1) * (m.factorial : ℚ) := by
  rw [fact_succ_q (m + 1), fact_succ_q m]
  push_cast
  ring

private lemma fact_step3 (m : ℕ) :
    ((m + 3).factorial : ℚ) =
      ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * (m.factorial : ℚ) := by
  rw [fact_succ_q (m + 2), fact_step2 m]
  push_cast
  ring

private lemma fact_eq_mul_pred {k : ℕ} (hk : 1 ≤ k) :
    (k.factorial : ℚ) = (k : ℚ) * ((k - 1).factorial : ℚ) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [Nat.factorial_succ, Nat.add_sub_cancel]
  push_cast
  ring

private lemma tele (n k : ℕ) (hn : 3 ≤ n) (hk : k ≤ n) :
    (n : ℚ) ^ 2 * (3 * (n : ℚ) - 4) * F n k
      - (3 * (n : ℚ) - 2) * (30 * (n : ℚ) ^ 2 - 50 * (n : ℚ) + 13) * F (n - 1) k
      + (9 * (n : ℚ) ^ 3 - 30 * (n : ℚ) ^ 2 + 29 * (n : ℚ) - 6) * F (n - 2) k
      - (3 * (n : ℚ) - 1) * ((n : ℚ) - 2) ^ 2 * F (n - 3) k
    = H n (k + 1) - H n k := by
  by_cases hk0 : k = 0
  · subst hk0
    have hF0 : ∀ m, F m 0 = 1 := fun m => by simp [F]
    rw [hF0, hF0, hF0, hF0]
    have hH0 : H n 0 = 0 := by simp [H]
    have hH1 : H n 1 = -3 * (3 * (n : ℚ) - 4) * (3 * (n : ℚ) - 2) * (3 * (n : ℚ) - 1) := by
      have h1 : 1 ≤ 1 ∧ 1 ≤ n := ⟨le_rfl, by omega⟩
      simp only [H, h1, and_self, ↓reduceIte, Nat.sub_self, Nat.factorial_zero, Nat.cast_one]
      have heq : n + 2 * 1 - 3 = n - 1 := by omega
      rw [heq]
      have hne : ((n - 1).factorial : ℚ) ≠ 0 := by positivity
      field_simp [hne]
    rw [hH0, hH1]
    ring
  · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
    by_cases hkn : k = n
    · subst k
      have hF1 : F (n - 1) n = 0 := F_eq_zero_of_lt (by omega)
      have hF2 : F (n - 2) n = 0 := F_eq_zero_of_lt (by omega)
      have hF3 : F (n - 3) n = 0 := F_eq_zero_of_lt (by omega)
      have hHn1 : H n (n + 1) = 0 := by simp [H]
      have hHn : H n n =
          -3 * (3 * (n : ℚ) - 4) * (3 * (n : ℚ) - 2) * (3 * (n : ℚ) - 1) *
            (((3 * n - 3).factorial : ℚ) / ((((n - 1).factorial : ℚ) ^ 3) * 1)) := by
        have hcond : 1 ≤ n ∧ n ≤ n := ⟨hk1, le_rfl⟩
        simp only [H, hcond, and_self, ↓reduceIte, Nat.sub_self, Nat.factorial_zero, Nat.cast_one]
        have heq : n + 2 * n - 3 = 3 * n - 3 := by omega
        rw [heq]
      rw [hF1, hF2, hF3, hHn1, hHn, F_eq_fact le_rfl]
      simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one]
      have h3n : n + 2 * n = (3 * n - 3) + 3 := by omega
      rw [h3n, fact_step3 (3 * n - 3), fact_eq_mul_pred hk1]
      have hc1 : ((3 * n - 3 : ℕ) : ℚ) = 3 * (n : ℚ) - 3 := by
        have : 3 ≤ 3 * n := by omega
        rw [Nat.cast_sub this]; push_cast; ring
      rw [hc1]
      have hnf : ((n - 1).factorial : ℚ) ≠ 0 := by positivity
      have hn0 : (n : ℚ) ≠ 0 := by positivity
      field_simp [hnf, hn0]
      ring
    · by_cases hkn1 : k = n - 1
      · have hF2 : F (n - 2) k = 0 := F_eq_zero_of_lt (by omega)
        have hF3 : F (n - 3) k = 0 := F_eq_zero_of_lt (by omega)
        rw [hF2, hF3, F_eq_fact hk, F_eq_fact (by omega : k ≤ n - 1)]
        have hH1 : H n (k + 1) =
            -3 * (3 * (n : ℚ) - 4) * (3 * (n : ℚ) - 2) * (3 * (n : ℚ) - 1) *
              (((n + 2 * (k + 1) - 3).factorial : ℚ) /
                (((k.factorial : ℚ) ^ 3) * ((n - (k + 1)).factorial : ℚ))) := by
          have hc : 1 ≤ k + 1 ∧ k + 1 ≤ n := ⟨by omega, by omega⟩
          simp only [H, hc, and_self, ↓reduceIte, Nat.add_sub_cancel]
        have hH0 : H n k =
            -3 * (3 * (n : ℚ) - 4) * (3 * (n : ℚ) - 2) * (3 * (n : ℚ) - 1) *
              (((n + 2 * k - 3).factorial : ℚ) /
                ((((k - 1).factorial : ℚ) ^ 3) * ((n - k).factorial : ℚ))) := by
          have hc : 1 ≤ k ∧ k ≤ n := ⟨hk1, hk⟩
          simp only [H, hc, and_self, ↓reduceIte]
        rw [hH1, hH0]
        set B := n + 2 * k - 3
        have hB0 : n + 2 * k = B + 3 := by omega
        have hB1 : n - 1 + 2 * k = B + 2 := by omega
        have hB2 : n + 2 * (k + 1) - 3 = B + 2 := by omega
        have hnk : n - k = 1 := by omega
        have hnk1 : n - 1 - k = 0 := by omega
        have hnk2 : n - (k + 1) = 0 := by omega
        rw [hB0, hB1, hB2, hnk, hnk1, hnk2, fact_step3 B, fact_step2 B, fact_eq_mul_pred hk1]
        simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one]
        have hBc : (B : ℚ) = 3 * (n : ℚ) - 5 := by
          have : B = 3 * n - 5 := by omega
          rw [this, Nat.cast_sub (by omega : 5 ≤ 3 * n)]; push_cast; ring
        have hkc : (k : ℚ) = (n : ℚ) - 1 := by
          rw [hkn1, Nat.cast_sub (by omega : 1 ≤ n)]; push_cast; ring
        rw [hBc, hkc]
        have hkf : ((k - 1).factorial : ℚ) ≠ 0 := by positivity
        have hn1 : (n : ℚ) - 1 ≠ 0 := by
          have : (3 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
          linarith
        field_simp [hkf, hn1]
        ring
      · by_cases hkn2 : k = n - 2
        · have hF3 : F (n - 3) k = 0 := F_eq_zero_of_lt (by omega)
          rw [hF3, F_eq_fact hk, F_eq_fact (by omega : k ≤ n - 1),
              F_eq_fact (by omega : k ≤ n - 2)]
          have hH1 : H n (k + 1) =
              -3 * (3 * (n : ℚ) - 4) * (3 * (n : ℚ) - 2) * (3 * (n : ℚ) - 1) *
                (((n + 2 * (k + 1) - 3).factorial : ℚ) /
                  (((k.factorial : ℚ) ^ 3) * ((n - (k + 1)).factorial : ℚ))) := by
            have hc : 1 ≤ k + 1 ∧ k + 1 ≤ n := ⟨by omega, by omega⟩
            simp only [H, hc, and_self, ↓reduceIte, Nat.add_sub_cancel]
          have hH0 : H n k =
              -3 * (3 * (n : ℚ) - 4) * (3 * (n : ℚ) - 2) * (3 * (n : ℚ) - 1) *
                (((n + 2 * k - 3).factorial : ℚ) /
                  ((((k - 1).factorial : ℚ) ^ 3) * ((n - k).factorial : ℚ))) := by
            have hc : 1 ≤ k ∧ k ≤ n := ⟨hk1, hk⟩
            simp only [H, hc, and_self, ↓reduceIte]
          rw [hH1, hH0]
          set B := n + 2 * k - 3
          have hB0 : n + 2 * k = B + 3 := by omega
          have hB1 : n - 1 + 2 * k = B + 2 := by omega
          have hB2 : n - 2 + 2 * k = B + 1 := by omega
          have hB3 : n + 2 * (k + 1) - 3 = B + 2 := by omega
          have hnk0 : n - k = 2 := by omega
          have hnk1 : n - 1 - k = 1 := by omega
          have hnk2 : n - 2 - k = 0 := by omega
          have hnk3 : n - (k + 1) = 1 := by omega
          rw [hB0, hB1, hB2, hB3, hnk0, hnk1, hnk2, hnk3,
              fact_step3 B, fact_step2 B, fact_succ_q B, fact_eq_mul_pred hk1]
          simp only [Nat.factorial_zero, Nat.factorial_one, Nat.factorial_two,
                     Nat.cast_one, Nat.cast_ofNat]
          have hBc : (B : ℚ) = 3 * (n : ℚ) - 7 := by
            have : B = 3 * n - 7 := by omega
            rw [this, Nat.cast_sub (by omega : 7 ≤ 3 * n)]; push_cast; ring
          have hkc : (k : ℚ) = (n : ℚ) - 2 := by
            rw [hkn2, Nat.cast_sub (by omega : 2 ≤ n)]; push_cast; ring
          rw [hBc, hkc]
          have hkf : ((k - 1).factorial : ℚ) ≠ 0 := by positivity
          have hn2 : (n : ℚ) - 2 ≠ 0 := by
            have : (3 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
            linarith
          field_simp [hkf, hn2]
          ring
        · have hkle3 : k ≤ n - 3 := by omega
          rw [F_eq_fact hk, F_eq_fact (by omega : k ≤ n - 1),
              F_eq_fact (by omega : k ≤ n - 2), F_eq_fact hkle3]
          have hH1 : H n (k + 1) =
              -3 * (3 * (n : ℚ) - 4) * (3 * (n : ℚ) - 2) * (3 * (n : ℚ) - 1) *
                (((n + 2 * (k + 1) - 3).factorial : ℚ) /
                  (((k.factorial : ℚ) ^ 3) * ((n - (k + 1)).factorial : ℚ))) := by
            have hc : 1 ≤ k + 1 ∧ k + 1 ≤ n := ⟨by omega, by omega⟩
            simp only [H, hc, and_self, ↓reduceIte, Nat.add_sub_cancel]
          have hH0 : H n k =
              -3 * (3 * (n : ℚ) - 4) * (3 * (n : ℚ) - 2) * (3 * (n : ℚ) - 1) *
                (((n + 2 * k - 3).factorial : ℚ) /
                  ((((k - 1).factorial : ℚ) ^ 3) * ((n - k).factorial : ℚ))) := by
            have hc : 1 ≤ k ∧ k ≤ n := ⟨hk1, hk⟩
            simp only [H, hc, and_self, ↓reduceIte]
          rw [hH1, hH0]
          set B := n + 2 * k - 3
          set D := n - 3 - k
          have hB0 : n + 2 * k = B + 3 := by omega
          have hB1 : n - 1 + 2 * k = B + 2 := by omega
          have hB2 : n - 2 + 2 * k = B + 1 := by omega
          have hB3 : n - 3 + 2 * k = B := by omega
          have hB4 : n + 2 * (k + 1) - 3 = B + 2 := by omega
          have hD0 : n - k = D + 3 := by omega
          have hD1 : n - 1 - k = D + 2 := by omega
          have hD2 : n - 2 - k = D + 1 := by omega
          have hD3 : n - (k + 1) = D + 2 := by omega
          rw [hB0, hB1, hB2, hB3, hB4, hD0, hD1, hD2, hD3,
              fact_step3 B, fact_step2 B, fact_succ_q B,
              fact_step3 D, fact_step2 D, fact_succ_q D, fact_eq_mul_pred hk1]
          have hBc : (B : ℚ) = (n : ℚ) + 2 * (k : ℚ) - 3 := by
            have : 3 ≤ n + 2 * k := by omega
            rw [Nat.cast_sub this]; push_cast; ring
          have hDc : (D : ℚ) = (n : ℚ) - 3 - (k : ℚ) := by
            have : k ≤ n - 3 := hkle3
            rw [Nat.cast_sub this, Nat.cast_sub (by omega : 3 ≤ n)]; push_cast; ring
          rw [hBc, hDc]
          have hkf : ((k - 1).factorial : ℚ) ≠ 0 := by positivity
          have hDf : (D.factorial : ℚ) ≠ 0 := by positivity
          have hk0q : (k : ℚ) ≠ 0 := by positivity
          have hnk0 : (n : ℚ) - 3 - (k : ℚ) + 3 ≠ 0 := by
            have : (k : ℚ) + 3 ≤ (n : ℚ) := by exact_mod_cast (by omega : k + 3 ≤ n)
            linarith
          have hnk1 : (n : ℚ) - 3 - (k : ℚ) + 2 ≠ 0 := by
            have : (k : ℚ) + 3 ≤ (n : ℚ) := by exact_mod_cast (by omega : k + 3 ≤ n)
            linarith
          have hnk2 : (n : ℚ) - 3 - (k : ℚ) + 1 ≠ 0 := by
            have : (k : ℚ) + 3 ≤ (n : ℚ) := by exact_mod_cast (by omega : k + 3 ≤ n)
            linarith
          field_simp [hkf, hDf, hk0q, hnk0, hnk1, hnk2]
          ring

private lemma rec1_rat (n : ℕ) (hn : 3 ≤ n) :
    (n : ℚ) ^ 2 * (3 * (n : ℚ) - 4) * (OMA.S_oeis_a081798.a n : ℚ)
      - (3 * (n : ℚ) - 2) * (30 * (n : ℚ) ^ 2 - 50 * (n : ℚ) + 13) * (OMA.S_oeis_a081798.a (n - 1) : ℚ)
      + (9 * (n : ℚ) ^ 3 - 30 * (n : ℚ) ^ 2 + 29 * (n : ℚ) - 6) * (OMA.S_oeis_a081798.a (n - 2) : ℚ)
      - (3 * (n : ℚ) - 1) * ((n : ℚ) - 2) ^ 2 * (OMA.S_oeis_a081798.a (n - 3) : ℚ) = 0 := by
  rw [a_cast_eq_sum n n le_rfl,
      a_cast_eq_sum (n - 1) n (by omega),
      a_cast_eq_sum (n - 2) n (by omega),
      a_cast_eq_sum (n - 3) n (by omega)]
  have hsum :
      (n : ℚ) ^ 2 * (3 * (n : ℚ) - 4) * (∑ k ∈ Finset.range (n + 1), F n k)
        - (3 * (n : ℚ) - 2) * (30 * (n : ℚ) ^ 2 - 50 * (n : ℚ) + 13) *
            (∑ k ∈ Finset.range (n + 1), F (n - 1) k)
        + (9 * (n : ℚ) ^ 3 - 30 * (n : ℚ) ^ 2 + 29 * (n : ℚ) - 6) *
            (∑ k ∈ Finset.range (n + 1), F (n - 2) k)
        - (3 * (n : ℚ) - 1) * ((n : ℚ) - 2) ^ 2 *
            (∑ k ∈ Finset.range (n + 1), F (n - 3) k) =
      ∑ k ∈ Finset.range (n + 1), (H n (k + 1) - H n k) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    exact tele n k hn (by omega)
  rw [hsum, Finset.sum_range_sub (fun k => H n k) (n + 1)]
  simp [H]

private lemma rec1 (n : ℕ) (hn : 3 ≤ n) :
    (n : ℤ) ^ 2 * (3 * n - 4) * OMA.S_oeis_a081798.a n
      - (3 * (n : ℤ) - 2) * (30 * (n : ℤ) ^ 2 - 50 * n + 13) * OMA.S_oeis_a081798.a (n - 1)
      + (9 * (n : ℤ) ^ 3 - 30 * (n : ℤ) ^ 2 + 29 * n - 6) * OMA.S_oeis_a081798.a (n - 2)
      - (3 * (n : ℤ) - 1) * ((n : ℤ) - 2) ^ 2 * OMA.S_oeis_a081798.a (n - 3) = 0 := by
  have h := rec1_rat n hn
  exact_mod_cast h

private lemma rec2 (n : ℕ) (hn : 4 ≤ n) :
    (n : ℤ) ^ 2 * OMA.S_oeis_a081798.a n
      + (-28 * (n : ℤ) ^ 2 + 24 * n - 3) * OMA.S_oeis_a081798.a (n - 1)
      + 3 * (-19 * (n : ℤ) ^ 2 + 78 * n - 77) * OMA.S_oeis_a081798.a (n - 2)
      + (5 * (n : ℤ) - 12) * ((n : ℤ) - 3) * OMA.S_oeis_a081798.a (n - 3)
      - 2 * ((n : ℤ) - 3) ^ 2 * OMA.S_oeis_a081798.a (n - 4) = 0 := by
  have h1 := rec1 n (by omega)
  have h2 := rec1 (n - 1) (by omega)
  have hn1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  have heq1 : n - 1 - 1 = n - 2 := by omega
  have heq2 : n - 1 - 2 = n - 3 := by omega
  have heq3 : n - 1 - 3 = n - 4 := by omega
  rw [hn1, heq1, heq2, heq3] at h2
  have hmul :
      (3 * (n : ℤ) - 4) *
        ((n : ℤ) ^ 2 * OMA.S_oeis_a081798.a n
          + (-28 * (n : ℤ) ^ 2 + 24 * n - 3) * OMA.S_oeis_a081798.a (n - 1)
          + 3 * (-19 * (n : ℤ) ^ 2 + 78 * n - 77) * OMA.S_oeis_a081798.a (n - 2)
          + (5 * (n : ℤ) - 12) * ((n : ℤ) - 3) * OMA.S_oeis_a081798.a (n - 3)
          - 2 * ((n : ℤ) - 3) ^ 2 * OMA.S_oeis_a081798.a (n - 4)) = 0 := by
    linear_combination h1 + 2 * h2
  have hne : (3 * (n : ℤ) - 4) ≠ 0 := by omega
  exact (mul_eq_zero.mp hmul).resolve_left hne

end A081798Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a081798.main :=
  ⟨A081798Proof.rec1, A081798Proof.rec2⟩

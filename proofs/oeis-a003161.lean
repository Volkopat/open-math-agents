import OMAStatements.S_oeis_a003161

/-!
Proof of Peter Bala's March 2023 supercongruence conjecture on OEIS A003161:
for every prime p >= 5 and all positive integers n, k,
  b (n * p ^ k) == b (n * p ^ (k - 1)) [ZMOD p ^ (3 * k)].
-/

namespace OMA.S_oeis_a003161.Proof

open Finset BigOperators Polynomial

-- ============================================================================
-- Block A: Exact Combinatorial Reduction (Lemma 1)
-- ============================================================================

private def H (n : ℕ) : ℤ :=
  ∑ r ∈ range n, ((Nat.choose (n - 1 + r) r : ℤ) ^ 2)

/-- Absorption identity in Z: for x >= 1 and any j,
    x * C(j, x) = (j + 1 - x) * C(j, x - 1). -/
private lemma choose_absorb_int (j x : ℕ) (hx : 1 ≤ x) :
    (x : ℤ) * (Nat.choose j x : ℤ) =
      ((j : ℤ) + 1 - (x : ℤ)) * (Nat.choose j (x - 1) : ℤ) := by
  obtain ⟨y, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : x ≠ 0)
  simp only [Nat.succ_sub_one]
  by_cases hj : j < y
  · have h1 : Nat.choose j (y + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h2 : Nat.choose j y = 0 := Nat.choose_eq_zero_of_lt hj
    simp [h1, h2]
  · have hj' : y ≤ j := Nat.le_of_not_lt hj
    have hnat : (y + 1) * Nat.choose j (y + 1) = (j - y) * Nat.choose j y := by
      have h2 := Nat.choose_succ_right_eq j y
      linarith
    have hcast : ((y + 1 : ℕ) : ℤ) * (Nat.choose j (y + 1) : ℤ) =
        ((j - y : ℕ) : ℤ) * (Nat.choose j y : ℤ) := by exact_mod_cast hnat
    have hsub : ((j - y : ℕ) : ℤ) = (j : ℤ) - (y : ℤ) := Int.ofNat_sub hj'
    rw [hsub] at hcast
    push_cast at hcast ⊢
    linarith

/-- L1.1: Pascal bilinear telescoping identity. -/
private lemma pascal_telescope (a b j : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (b : ℤ) * (Nat.choose j a : ℤ) * (Nat.choose j (b - 1) : ℤ) -
      (a : ℤ) * (Nat.choose j (a - 1) : ℤ) * (Nat.choose j b : ℤ) =
    ((b : ℤ) - (a : ℤ)) *
      ((Nat.choose (j + 1) a : ℤ) * (Nat.choose (j + 1) b : ℤ) -
       (Nat.choose j a : ℤ) * (Nat.choose j b : ℤ)) := by
  obtain ⟨a', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
  obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  have hpa : (Nat.choose (j + 1) (a' + 1) : ℤ) =
      (Nat.choose j a' : ℤ) + (Nat.choose j (a' + 1) : ℤ) := by
    exact_mod_cast Nat.choose_succ_succ j a'
  have hpb : (Nat.choose (j + 1) (b' + 1) : ℤ) =
      (Nat.choose j b' : ℤ) + (Nat.choose j (b' + 1) : ℤ) := by
    exact_mod_cast Nat.choose_succ_succ j b'
  have habA := choose_absorb_int j (a' + 1) (by omega)
  have habB := choose_absorb_int j (b' + 1) (by omega)
  simp only [Nat.succ_sub_one] at habA habB ⊢
  rw [hpa, hpb]
  have hdiff :
      ((b' + 1 : ℕ) : ℤ) * (Nat.choose j (a' + 1) : ℤ) * (Nat.choose j b' : ℤ) -
        ((a' + 1 : ℕ) : ℤ) * (Nat.choose j a' : ℤ) * (Nat.choose j (b' + 1) : ℤ) -
      (((b' + 1 : ℕ) : ℤ) - ((a' + 1 : ℕ) : ℤ)) *
        (((Nat.choose j a' : ℤ) + (Nat.choose j (a' + 1) : ℤ)) *
         ((Nat.choose j b' : ℤ) + (Nat.choose j (b' + 1) : ℤ)) -
         (Nat.choose j (a' + 1) : ℤ) * (Nat.choose j (b' + 1) : ℤ)) =
      (((a' + 1 : ℕ) : ℤ) * (Nat.choose j (a' + 1) : ℤ)) * (Nat.choose j b' : ℤ) -
        (((b' + 1 : ℕ) : ℤ) * (Nat.choose j (b' + 1) : ℤ)) * (Nat.choose j a' : ℤ) -
        (((b' + 1 : ℕ) : ℤ) - ((a' + 1 : ℕ) : ℤ)) * (Nat.choose j a' : ℤ) * (Nat.choose j b' : ℤ) := by
    ring
  rw [habA, habB] at hdiff
  linarith

/-- L1.2: Ohtsuka-Tauraso cubic binomial identity. -/
private lemma ohtsuka_tauraso (m n : ℕ) (hnm : n < m) :
    ∑ k ∈ range (n + 1), ((m : ℤ) - 2 * (k : ℤ)) * (Nat.choose m k : ℤ) ^ 3 =
      ((m : ℤ) - (n : ℤ)) * (Nat.choose m n : ℤ) *
        ∑ j ∈ range m, (Nat.choose j n : ℤ) * (Nat.choose j (m - n - 1) : ℤ) := by
  induction n with
  | zero =>
    simp only [Nat.reduceAdd, range_one, sum_singleton, Nat.cast_zero, mul_zero, sub_zero,
      Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, one_pow, mul_one, one_mul]
    have hsum : ∑ j ∈ range m, (Nat.choose j (m - 1) : ℤ) = 1 := by
      have hmem : m - 1 ∈ range m := mem_range.mpr (by omega)
      rw [Finset.sum_eq_single (m - 1)]
      · simp
      · intro j hj hne
        have hlt : j < m - 1 := by
          have := mem_range.mp hj
          omega
        simp [Nat.choose_eq_zero_of_lt hlt]
      · intro h; exact absurd hmem h
    rw [hsum, mul_one]
  | succ n ih =>
    have ih' := ih (by omega)
    rw [sum_range_succ, ih']
    have hstep_choose : ((m : ℤ) - (n : ℤ)) * (Nat.choose m n : ℤ) =
        ((n + 1 : ℕ) : ℤ) * (Nat.choose m (n + 1) : ℤ) := by
      have h := choose_absorb_int m (n + 1) (by omega)
      simp only [Nat.succ_sub_one] at h
      push_cast at h ⊢
      linarith
    have htele :
        ∑ j ∈ range m,
          (((m : ℤ) - ((n + 1 : ℕ) : ℤ)) * (Nat.choose j (n + 1) : ℤ) *
              (Nat.choose j (m - (n + 1) - 1) : ℤ) -
            ((n + 1 : ℕ) : ℤ) * (Nat.choose j n : ℤ) *
              (Nat.choose j (m - n - 1) : ℤ)) =
        ((m : ℤ) - 2 * ((n + 1 : ℕ) : ℤ)) * (Nat.choose m (n + 1) : ℤ) ^ 2 := by
      have ha : 1 ≤ n + 1 := by omega
      have hb : 1 ≤ m - n - 1 := by omega
      have hsub_eq : m - (n + 1) - 1 = (m - n - 1) - 1 := by omega
      have hcast_b : ((m - n - 1 : ℕ) : ℤ) = (m : ℤ) - ((n + 1 : ℕ) : ℤ) := by omega
      have hrew : ∀ j ∈ range m,
          ((m : ℤ) - ((n + 1 : ℕ) : ℤ)) * (Nat.choose j (n + 1) : ℤ) *
              (Nat.choose j (m - (n + 1) - 1) : ℤ) -
            ((n + 1 : ℕ) : ℤ) * (Nat.choose j n : ℤ) *
              (Nat.choose j (m - n - 1) : ℤ) =
          (((m - n - 1 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ)) *
            ((Nat.choose (j + 1) (n + 1) : ℤ) * (Nat.choose (j + 1) (m - n - 1) : ℤ) -
             (Nat.choose j (n + 1) : ℤ) * (Nat.choose j (m - n - 1) : ℤ)) := by
        intro j _
        rw [hsub_eq, ← hcast_b]
        exact pascal_telescope (n + 1) (m - n - 1) j ha hb
      rw [Finset.sum_congr rfl hrew, ← Finset.mul_sum]
      rw [Finset.sum_range_sub (fun j => (Nat.choose j (n + 1) : ℤ) * (Nat.choose j (m - n - 1) : ℤ)) m]
      have h0 : Nat.choose 0 (n + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      have hsym : Nat.choose m (m - n - 1) = Nat.choose m (n + 1) := by
        rw [show m - n - 1 = m - (n + 1) by omega]
        exact Nat.choose_symm (by omega : n + 1 ≤ m)
      rw [h0, hsym]
      simp only [Nat.cast_zero, zero_mul, sub_zero]
      rw [hcast_b]
      ring
    have hcomb :
        ((m : ℤ) - ((n + 1 : ℕ) : ℤ)) * (Nat.choose m (n + 1) : ℤ) *
          (∑ j ∈ range m, (Nat.choose j (n + 1) : ℤ) * (Nat.choose j (m - (n + 1) - 1) : ℤ)) -
        ((m : ℤ) - (n : ℤ)) * (Nat.choose m n : ℤ) *
          (∑ j ∈ range m, (Nat.choose j n : ℤ) * (Nat.choose j (m - n - 1) : ℤ)) =
        (Nat.choose m (n + 1) : ℤ) *
          ∑ j ∈ range m,
            (((m : ℤ) - ((n + 1 : ℕ) : ℤ)) * (Nat.choose j (n + 1) : ℤ) *
                (Nat.choose j (m - (n + 1) - 1) : ℤ) -
              ((n + 1 : ℕ) : ℤ) * (Nat.choose j n : ℤ) *
                (Nat.choose j (m - n - 1) : ℤ)) := by
      rw [hstep_choose, Finset.sum_sub_distrib]
      have h1 : ∑ x ∈ range m,
          ((m : ℤ) - ((n + 1 : ℕ) : ℤ)) * (Nat.choose x (n + 1) : ℤ) *
            (Nat.choose x (m - (n + 1) - 1) : ℤ) =
          ((m : ℤ) - ((n + 1 : ℕ) : ℤ)) *
            ∑ x ∈ range m, (Nat.choose x (n + 1) : ℤ) * (Nat.choose x (m - (n + 1) - 1) : ℤ) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => by ring
      have h2 : ∑ x ∈ range m,
          ((n + 1 : ℕ) : ℤ) * (Nat.choose x n : ℤ) * (Nat.choose x (m - n - 1) : ℤ) =
          ((n + 1 : ℕ) : ℤ) *
            ∑ x ∈ range m, (Nat.choose x n : ℤ) * (Nat.choose x (m - n - 1) : ℤ) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => by ring
      rw [h1, h2]
      ring
    rw [htele] at hcomb
    linarith

/-- L1.3: Miana-Ohtsuka-Romero cubic ballot reduction for b(n). -/
private lemma miana_cube_sum (n : ℕ) (hn : 0 < n) :
    b n = 4 * (Nat.choose (2 * n - 1) (n - 1) : ℤ) ^ 3 -
      3 * (Nat.choose (2 * n - 1) (n - 1) : ℤ) *
        ∑ j ∈ range (2 * n), (Nat.choose j (n - 1) : ℤ) * (Nat.choose j n : ℤ) := by
  have hm_pos : (2 * n : ℤ) ≠ 0 := by positivity
  have hm3_pos : ((2 * n : ℤ) ^ 3) ≠ 0 := pow_ne_zero 3 hm_pos
  apply mul_left_cancel₀ hm3_pos
  have hdiv : (2 * n - 1) / 2 + 1 = n := by omega
  have hb_def : b n = ∑ k ∈ range n,
      ((Nat.choose (2 * n - 1) k : ℤ) -
        (if k = 0 then 0 else (Nat.choose (2 * n - 1) (k - 1) : ℤ))) ^ 3 := by
    simp only [b, a, hdiv]
  have hterm : ∀ k ∈ range n,
      (2 * n : ℤ) * ((Nat.choose (2 * n - 1) k : ℤ) -
        (if k = 0 then 0 else (Nat.choose (2 * n - 1) (k - 1) : ℤ))) =
      ((2 * n : ℤ) - 2 * (k : ℤ)) * (Nat.choose (2 * n) k : ℤ) := by
    intro k hk
    have hkn : k < n := mem_range.mp hk
    have h1 : (2 * n : ℤ) * (Nat.choose (2 * n - 1) k : ℤ) =
        ((2 * n : ℤ) - (k : ℤ)) * (Nat.choose (2 * n) k : ℤ) := by
      have hnat : (2 * n) * Nat.choose (2 * n - 1) k = (2 * n - k) * Nat.choose (2 * n) k := by
        have h2 := Nat.add_one_mul_choose_eq (2 * n - 1) (2 * n - 1 - k)
        have hsym1 : Nat.choose (2 * n - 1) (2 * n - 1 - k) = Nat.choose (2 * n - 1) k :=
          Nat.choose_symm (by omega)
        have hsym2 : Nat.choose (2 * n) (2 * n - k) = Nat.choose (2 * n) k :=
          Nat.choose_symm (by omega)
        have hsub1 : 2 * n - 1 + 1 = 2 * n := by omega
        have hsub2 : 2 * n - 1 - k + 1 = 2 * n - k := by omega
        rw [hsub1, hsub2, hsym1, hsym2] at h2
        linarith
      have hc : ((2 * n : ℕ) : ℤ) * (Nat.choose (2 * n - 1) k : ℤ) =
          ((2 * n - k : ℕ) : ℤ) * (Nat.choose (2 * n) k : ℤ) := by exact_mod_cast hnat
      have hsub : ((2 * n - k : ℕ) : ℤ) = (2 * n : ℤ) - (k : ℤ) := by omega
      rw [hsub] at hc
      push_cast at hc ⊢
      exact hc
    by_cases hk0 : k = 0
    · subst hk0; simp
    · simp only [hk0, ↓reduceIte]
      have h2 : (2 * n : ℤ) * (Nat.choose (2 * n - 1) (k - 1) : ℤ) =
          (k : ℤ) * (Nat.choose (2 * n) k : ℤ) := by
        have hnat : (2 * n) * Nat.choose (2 * n - 1) (k - 1) = k * Nat.choose (2 * n) k := by
          have h := Nat.add_one_mul_choose_eq (2 * n - 1) (k - 1)
          have hsub1 : 2 * n - 1 + 1 = 2 * n := by omega
          have hsub2 : k - 1 + 1 = k := by omega
          rw [hsub1, hsub2] at h
          linarith
        exact_mod_cast hnat
      linarith
  have hot := ohtsuka_tauraso (2 * n) (n - 1) (by omega)
  have hn1 : n - 1 + 1 = n := by omega
  have hmn1 : 2 * n - (n - 1) - 1 = n := by omega
  rw [hn1, hmn1] at hot
  have hcho : ((2 * n : ℕ) - (n - 1 : ℕ) : ℤ) * (Nat.choose (2 * n) (n - 1) : ℤ) =
      (2 * n : ℤ) * (Nat.choose (2 * n - 1) (n - 1) : ℤ) := by
    have hnat : (2 * n - (n - 1)) * Nat.choose (2 * n) (n - 1) =
        (2 * n) * Nat.choose (2 * n - 1) (n - 1) := by
      have h := Nat.add_one_mul_choose_eq (2 * n - 1) (2 * n - 1 - (n - 1))
      have hsub1 : 2 * n - 1 + 1 = 2 * n := by omega
      have hsub2 : 2 * n - 1 - (n - 1) + 1 = 2 * n - (n - 1) := by omega
      have hsym1 : Nat.choose (2 * n - 1) (2 * n - 1 - (n - 1)) = Nat.choose (2 * n - 1) (n - 1) :=
        Nat.choose_symm (by omega)
      have hsym2 : Nat.choose (2 * n) (2 * n - (n - 1)) = Nat.choose (2 * n) (n - 1) :=
        Nat.choose_symm (by omega)
      rw [hsub1, hsub2, hsym1, hsym2] at h
      linarith
    have hc : ((2 * n - (n - 1) : ℕ) : ℤ) * (Nat.choose (2 * n) (n - 1) : ℤ) =
        ((2 * n : ℕ) : ℤ) * (Nat.choose (2 * n - 1) (n - 1) : ℤ) := by exact_mod_cast hnat
    have hsub : ((2 * n - (n - 1) : ℕ) : ℤ) = ((2 * n : ℕ) : ℤ) - ((n - 1 : ℕ) : ℤ) := by omega
    rw [hsub] at hc
    push_cast at hc ⊢
    exact hc
  rw [hcho] at hot
  have hsum_lhs : (2 * n : ℤ) ^ 3 * b n =
      ∑ k ∈ range n, ((2 * n : ℤ) - 2 * (k : ℤ)) ^ 3 * (Nat.choose (2 * n) k : ℤ) ^ 3 := by
    rw [hb_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have ht := hterm k hk
    calc (2 * n : ℤ) ^ 3 *
          ((Nat.choose (2 * n - 1) k : ℤ) -
            (if k = 0 then 0 else (Nat.choose (2 * n - 1) (k - 1) : ℤ))) ^ 3
        = ((2 * n : ℤ) * ((Nat.choose (2 * n - 1) k : ℤ) -
            (if k = 0 then 0 else (Nat.choose (2 * n - 1) (k - 1) : ℤ)))) ^ 3 := by ring
      _ = (((2 * n : ℤ) - 2 * (k : ℤ)) * (Nat.choose (2 * n) k : ℤ)) ^ 3 := by rw [ht]
      _ = ((2 * n : ℤ) - 2 * (k : ℤ)) ^ 3 * (Nat.choose (2 * n) k : ℤ) ^ 3 := by ring
  have hsum_add :
      (2 * n : ℤ) ^ 3 * b n +
        3 * (2 * n : ℤ) ^ 3 * (Nat.choose (2 * n - 1) (n - 1) : ℤ) *
          ∑ j ∈ range (2 * n), (Nat.choose j (n - 1) : ℤ) * (Nat.choose j n : ℤ) =
      4 * (2 * n : ℤ) ^ 3 * (Nat.choose (2 * n - 1) (n - 1) : ℤ) ^ 3 := by
    have hot3 :
        3 * (2 * n : ℤ) ^ 3 * (Nat.choose (2 * n - 1) (n - 1) : ℤ) *
          ∑ j ∈ range (2 * n), (Nat.choose j (n - 1) : ℤ) * (Nat.choose j n : ℤ) =
        ∑ k ∈ range n, 3 * (2 * n : ℤ) ^ 2 * ((2 * n : ℤ) - 2 * (k : ℤ)) *
          (Nat.choose (2 * n) k : ℤ) ^ 3 := by
      have hmul := congrArg (fun x : ℤ => 3 * (2 * n : ℤ) ^ 2 * x) hot
      push_cast at hmul
      calc 3 * (2 * n : ℤ) ^ 3 * (Nat.choose (2 * n - 1) (n - 1) : ℤ) *
            ∑ j ∈ range (2 * n), (Nat.choose j (n - 1) : ℤ) * (Nat.choose j n : ℤ)
          = 3 * (2 * n : ℤ) ^ 2 * ((2 * n : ℤ) * (Nat.choose (2 * n - 1) (n - 1) : ℤ) *
            ∑ j ∈ range (2 * n), (Nat.choose j (n - 1) : ℤ) * (Nat.choose j n : ℤ)) := by ring
        _ = 3 * (2 * n : ℤ) ^ 2 *
            ∑ k ∈ range n, ((2 * n : ℤ) - 2 * (k : ℤ)) * (Nat.choose (2 * n) k : ℤ) ^ 3 := hmul.symm
        _ = ∑ k ∈ range n, 3 * (2 * n : ℤ) ^ 2 * ((2 * n : ℤ) - 2 * (k : ℤ)) *
            (Nat.choose (2 * n) k : ℤ) ^ 3 := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
    rw [hsum_lhs, hot3, ← Finset.sum_add_distrib]
    have htele2 :
        ∑ k ∈ range n,
          (((2 * n : ℤ) - 2 * (k : ℤ)) ^ 3 * (Nat.choose (2 * n) k : ℤ) ^ 3 +
            3 * (2 * n : ℤ) ^ 2 * ((2 * n : ℤ) - 2 * (k : ℤ)) * (Nat.choose (2 * n) k : ℤ) ^ 3) =
        4 * (2 * n : ℤ) ^ 3 * ∑ k ∈ range n,
          ((Nat.choose (2 * n - 1) k : ℤ) ^ 3 -
            (if k = 0 then 0 else (Nat.choose (2 * n - 1) (k - 1) : ℤ) ^ 3)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkn : k < n := mem_range.mp hk
      have hA : ((2 * n : ℤ) - (k : ℤ)) * (Nat.choose (2 * n) k : ℤ) =
          (2 * n : ℤ) * (Nat.choose (2 * n - 1) k : ℤ) := by
        have hnat : (2 * n - k) * Nat.choose (2 * n) k = (2 * n) * Nat.choose (2 * n - 1) k := by
          have h := Nat.add_one_mul_choose_eq (2 * n - 1) (2 * n - 1 - k)
          have hsub1 : 2 * n - 1 + 1 = 2 * n := by omega
          have hsub2 : 2 * n - 1 - k + 1 = 2 * n - k := by omega
          have hsym1 : Nat.choose (2 * n - 1) (2 * n - 1 - k) = Nat.choose (2 * n - 1) k :=
            Nat.choose_symm (by omega)
          have hsym2 : Nat.choose (2 * n) (2 * n - k) = Nat.choose (2 * n) k :=
            Nat.choose_symm (by omega)
          rw [hsub1, hsub2, hsym1, hsym2] at h
          linarith
        have hc : ((2 * n - k : ℕ) : ℤ) * (Nat.choose (2 * n) k : ℤ) =
            ((2 * n : ℕ) : ℤ) * (Nat.choose (2 * n - 1) k : ℤ) := by exact_mod_cast hnat
        have hsub : ((2 * n - k : ℕ) : ℤ) = (2 * n : ℤ) - (k : ℤ) := by omega
        rw [hsub] at hc; push_cast at hc ⊢; exact hc
      have hB : (k : ℤ) * (Nat.choose (2 * n) k : ℤ) =
          (2 * n : ℤ) * (if k = 0 then 0 else (Nat.choose (2 * n - 1) (k - 1) : ℤ)) := by
        by_cases hk0 : k = 0
        · subst hk0; simp
        · simp only [hk0, ↓reduceIte]
          have hnat : k * Nat.choose (2 * n) k = (2 * n) * Nat.choose (2 * n - 1) (k - 1) := by
            have h := Nat.add_one_mul_choose_eq (2 * n - 1) (k - 1)
            have hsub1 : 2 * n - 1 + 1 = 2 * n := by omega
            have hsub2 : k - 1 + 1 = k := by omega
            rw [hsub1, hsub2] at h; linarith
          exact_mod_cast hnat
      have halg :
          ((2 * n : ℤ) - 2 * (k : ℤ)) ^ 3 * (Nat.choose (2 * n) k : ℤ) ^ 3 +
            3 * (2 * n : ℤ) ^ 2 * ((2 * n : ℤ) - 2 * (k : ℤ)) * (Nat.choose (2 * n) k : ℤ) ^ 3 =
          4 * ((((2 * n : ℤ) - (k : ℤ)) * (Nat.choose (2 * n) k : ℤ)) ^ 3 -
               ((k : ℤ) * (Nat.choose (2 * n) k : ℤ)) ^ 3) := by ring
      rw [halg, hA, hB]
      split_ifs <;> ring
    rw [htele2]
    have htele3 :
        ∑ k ∈ range n,
          ((Nat.choose (2 * n - 1) k : ℤ) ^ 3 -
            (if k = 0 then 0 else (Nat.choose (2 * n - 1) (k - 1) : ℤ) ^ 3)) =
        (Nat.choose (2 * n - 1) (n - 1) : ℤ) ^ 3 := by
      have hstep : ∀ m : ℕ, 0 < m →
          ∑ k ∈ range m,
            ((Nat.choose (2 * n - 1) k : ℤ) ^ 3 -
              (if k = 0 then 0 else (Nat.choose (2 * n - 1) (k - 1) : ℤ) ^ 3)) =
          (Nat.choose (2 * n - 1) (m - 1) : ℤ) ^ 3 := by
        intro m hm
        obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
        induction m' with
        | zero => simp
        | succ m' ihm =>
          rw [sum_range_succ, ihm (by omega)]
          simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]
          ring
      exact hstep n hn
    rw [htele3]
  linarith

/-- L1.4: Weighted square-binomial telescoping identity. -/
private lemma square_moment_telescope (n M : ℕ) (hn : 0 < n) :
    ∑ r ∈ range (M + 1), ((n : ℤ) + 2 * (r : ℤ)) * (Nat.choose (n - 1 + r) r : ℤ) ^ 2 =
      (n : ℤ) * (Nat.choose (n + M) M : ℤ) ^ 2 := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ, ih]
    have h1 : ((M + 1 : ℕ) : ℤ) * (Nat.choose (n + M) (M + 1) : ℤ) =
        (n : ℤ) * (Nat.choose (n + M) M : ℤ) := by
      have hnat : (M + 1) * Nat.choose (n + M) (M + 1) = n * Nat.choose (n + M) M := by
        have h := Nat.choose_succ_right_eq (n + M) M
        have hsub : n + M - M = n := by omega
        rw [hsub] at h; linarith
      exact_mod_cast hnat
    have h2 : ((M + 1 : ℕ) : ℤ) * (Nat.choose (n + M + 1) (M + 1) : ℤ) =
        ((n + M + 1 : ℕ) : ℤ) * (Nat.choose (n + M) M : ℤ) := by
      have hnat : (M + 1) * Nat.choose (n + M + 1) (M + 1) =
          (n + M + 1) * Nat.choose (n + M) M := by
        have h := Nat.add_one_mul_choose_eq (n + M) M
        linarith
      exact_mod_cast hnat
    have hne : ((M + 1 : ℕ) : ℤ) ^ 2 ≠ 0 := by positivity
    apply mul_left_cancel₀ hne
    have heq1 : n - 1 + (M + 1) = n + M := by omega
    have heq2 : n + (M + 1) = n + M + 1 := by omega
    rw [heq1, heq2]
    calc ((M + 1 : ℕ) : ℤ) ^ 2 *
          ((n : ℤ) * (Nat.choose (n + M) M : ℤ) ^ 2 +
            ((n : ℤ) + 2 * ((M + 1 : ℕ) : ℤ)) * (Nat.choose (n + M) (M + 1) : ℤ) ^ 2)
        = (n : ℤ) * ((M + 1 : ℕ) : ℤ) ^ 2 * (Nat.choose (n + M) M : ℤ) ^ 2 +
          ((n : ℤ) + 2 * ((M + 1 : ℕ) : ℤ)) *
            (((M + 1 : ℕ) : ℤ) * (Nat.choose (n + M) (M + 1) : ℤ)) ^ 2 := by ring
      _ = (n : ℤ) * ((M + 1 : ℕ) : ℤ) ^ 2 * (Nat.choose (n + M) M : ℤ) ^ 2 +
          ((n : ℤ) + 2 * ((M + 1 : ℕ) : ℤ)) * ((n : ℤ) * (Nat.choose (n + M) M : ℤ)) ^ 2 := by
            rw [h1]
      _ = (n : ℤ) * (((n + M + 1 : ℕ) : ℤ) * (Nat.choose (n + M) M : ℤ)) ^ 2 := by
            push_cast; ring
      _ = (n : ℤ) * (((M + 1 : ℕ) : ℤ) * (Nat.choose (n + M + 1) (M + 1) : ℤ)) ^ 2 := by
            rw [h2]
      _ = ((M + 1 : ℕ) : ℤ) ^ 2 * ((n : ℤ) * (Nat.choose (n + M + 1) (M + 1) : ℤ) ^ 2) := by
            ring

/-- L1.5: Exact algebraic reduction of 2*b(n) to C(2n-1, n-1) and H(n). -/
private lemma two_mul_b_eq (n : ℕ) (hn : 0 < n) :
    2 * b n = (Nat.choose (2 * n - 1) (n - 1) : ℤ) *
      (3 * H n - (Nat.choose (2 * n - 1) (n - 1) : ℤ) ^ 2) := by
  have hmiana := miana_cube_sum n hn
  -- Reindex sum_{j < 2n} C(j, n-1) C(j, n) into r = 0..n
  have hsum_j : (n : ℤ) * ∑ j ∈ range (2 * n), (Nat.choose j (n - 1) : ℤ) * (Nat.choose j n : ℤ) =
      (n : ℤ) * (Nat.choose (2 * n - 1) (n - 1) : ℤ) ^ 2 +
        ∑ r ∈ range n, (r : ℤ) * (Nat.choose (n - 1 + r) r : ℤ) ^ 2 := by
    have hsplit : ∑ j ∈ range (2 * n), (Nat.choose j (n - 1) : ℤ) * (Nat.choose j n : ℤ) =
        ∑ r ∈ range (n + 1), (Nat.choose (n - 1 + r) (n - 1) : ℤ) * (Nat.choose (n - 1 + r) n : ℤ) := by
      have h2n : 2 * n = (n - 1) + (n + 1) := by omega
      rw [h2n, Finset.sum_range_add]
      have hzero : ∑ j ∈ range (n - 1), (Nat.choose j (n - 1) : ℤ) * (Nat.choose j n : ℤ) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        have hlt : j < n - 1 := mem_range.mp hj
        simp [Nat.choose_eq_zero_of_lt hlt]
      rw [hzero, zero_add]
    rw [hsplit, Finset.mul_sum, Finset.sum_range_succ]
    have hlast : (n : ℤ) *
        ((Nat.choose (n - 1 + n) (n - 1) : ℤ) * (Nat.choose (n - 1 + n) n : ℤ)) =
        (n : ℤ) * (Nat.choose (2 * n - 1) (n - 1) : ℤ) ^ 2 := by
      have heq : n - 1 + n = 2 * n - 1 := by omega
      have hsym : Nat.choose (2 * n - 1) n = Nat.choose (2 * n - 1) (n - 1) := by
        have h := Nat.choose_symm (by omega : n - 1 ≤ 2 * n - 1)
        rwa [show 2 * n - 1 - (n - 1) = n by omega] at h
      rw [heq, hsym]; ring
    rw [hlast, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    have hab : (n : ℤ) * (Nat.choose (n - 1 + r) n : ℤ) =
        (r : ℤ) * (Nat.choose (n - 1 + r) (n - 1) : ℤ) := by
      have h := choose_absorb_int (n - 1 + r) n hn
      have hsub : ((n - 1 + r : ℕ) : ℤ) + 1 - (n : ℤ) = (r : ℤ) := by omega
      rw [hsub] at h; exact h
    have hsym : Nat.choose (n - 1 + r) (n - 1) = Nat.choose (n - 1 + r) r := by
      have h := Nat.choose_symm (by omega : r ≤ n - 1 + r)
      rwa [show n - 1 + r - r = n - 1 by omega] at h
    calc (n : ℤ) * ((Nat.choose (n - 1 + r) (n - 1) : ℤ) * (Nat.choose (n - 1 + r) n : ℤ))
        = (Nat.choose (n - 1 + r) (n - 1) : ℤ) * ((n : ℤ) * (Nat.choose (n - 1 + r) n : ℤ)) := by ring
      _ = (Nat.choose (n - 1 + r) (n - 1) : ℤ) * ((r : ℤ) * (Nat.choose (n - 1 + r) (n - 1) : ℤ)) := by rw [hab]
      _ = (r : ℤ) * (Nat.choose (n - 1 + r) r : ℤ) ^ 2 := by rw [hsym]; ring
  have htel := square_moment_telescope n (n - 1) hn
  have htel1 : n - 1 + 1 = n := by omega
  have htel2 : n + (n - 1) = 2 * n - 1 := by omega
  rw [htel1, htel2] at htel
  have h2r : 2 * ∑ r ∈ range n, (r : ℤ) * (Nat.choose (n - 1 + r) r : ℤ) ^ 2 =
      (n : ℤ) * (Nat.choose (2 * n - 1) (n - 1) : ℤ) ^ 2 - (n : ℤ) * H n := by
    have hexp : ∑ r ∈ range n, ((n : ℤ) + 2 * (r : ℤ)) * (Nat.choose (n - 1 + r) r : ℤ) ^ 2 =
        (n : ℤ) * H n + 2 * ∑ r ∈ range n, (r : ℤ) * (Nat.choose (n - 1 + r) r : ℤ) ^ 2 := by
      simp only [H, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ => by ring
    linarith
  have hn_ne : (n : ℤ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hn_ne
  calc (n : ℤ) * (2 * b n)
      = 8 * (n : ℤ) * (Nat.choose (2 * n - 1) (n - 1) : ℤ) ^ 3 -
        6 * (Nat.choose (2 * n - 1) (n - 1) : ℤ) *
          ((n : ℤ) * ∑ j ∈ range (2 * n), (Nat.choose j (n - 1) : ℤ) * (Nat.choose j n : ℤ)) := by
          rw [hmiana]; ring
    _ = 8 * (n : ℤ) * (Nat.choose (2 * n - 1) (n - 1) : ℤ) ^ 3 -
        6 * (Nat.choose (2 * n - 1) (n - 1) : ℤ) *
          ((n : ℤ) * (Nat.choose (2 * n - 1) (n - 1) : ℤ) ^ 2 +
            ∑ r ∈ range n, (r : ℤ) * (Nat.choose (n - 1 + r) r : ℤ) ^ 2) := by
          rw [hsum_j]
    _ = 2 * (n : ℤ) * (Nat.choose (2 * n - 1) (n - 1) : ℤ) ^ 3 -
        3 * (Nat.choose (2 * n - 1) (n - 1) : ℤ) *
          (2 * ∑ r ∈ range n, (r : ℤ) * (Nat.choose (n - 1 + r) r : ℤ) ^ 2) := by ring
    _ = 2 * (n : ℤ) * (Nat.choose (2 * n - 1) (n - 1) : ℤ) ^ 3 -
        3 * (Nat.choose (2 * n - 1) (n - 1) : ℤ) *
          ((n : ℤ) * (Nat.choose (2 * n - 1) (n - 1) : ℤ) ^ 2 - (n : ℤ) * H n) := by
          rw [h2r]
    _ = (n : ℤ) * ((Nat.choose (2 * n - 1) (n - 1) : ℤ) *
          (3 * H n - (Nat.choose (2 * n - 1) (n - 1) : ℤ) ^ 2)) := by ring

-- ============================================================================
-- Block B: p-Local Valuation Library, Wolstenholme, and Kazandzidis (Lemma 2)
-- ============================================================================

/-- Elementary p-local predicate: q lies in p^e * Z_(p). -/
private def PVal (p e : ℕ) (q : ℚ) : Prop :=
  ∃ (a : ℤ) (d : ℕ), ¬ p ∣ d ∧ q = (p : ℚ) ^ e * (a : ℚ) / (d : ℚ)

/-- Elementary p-adic valuation on natural numbers. -/
private noncomputable def vp (p n : ℕ) : ℕ := n.factorization p

private lemma vp_dvd {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) : p ^ vp p n ∣ n :=
  (hp.pow_dvd_iff_le_factorization hn).mpr le_rfl

private lemma vp_succ_not_dvd {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    ¬ p ^ (vp p n + 1) ∣ n := by
  intro h
  have hle := (hp.pow_dvd_iff_le_factorization hn).mp h
  dsimp [vp] at hle
  omega

private lemma vp_le_of_dvd {p n k : ℕ} (hp : p.Prime) (hn : n ≠ 0) (h : p ^ k ∣ n) :
    k ≤ vp p n :=
  (hp.pow_dvd_iff_le_factorization hn).mp h

private lemma pow_vp_le {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) : p ^ vp p n ≤ n :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (vp_dvd hp hn)

private lemma vp_split {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    ∃ m : ℕ, ¬ p ∣ m ∧ n = p ^ vp p n * m := by
  obtain ⟨m, hm⟩ := vp_dvd hp hn
  refine ⟨m, ?_, hm⟩
  intro ⟨k, hk⟩
  apply vp_succ_not_dvd hp hn
  refine ⟨k, ?_⟩
  calc n = p ^ vp p n * m := hm
    _ = p ^ vp p n * (p * k) := by rw [hk]
    _ = p ^ (vp p n + 1) * k := by rw [pow_succ]; ring

private lemma vp_add_of_lt {p a b : ℕ} (hp : p.Prime) (ha : a ≠ 0) (hb : b ≠ 0)
    (hlt : vp p a < vp p b) : vp p (a + b) = vp p a := by
  have hab : a + b ≠ 0 := by omega
  have h1 : p ^ vp p a ∣ a + b := by
    have ha1 := vp_dvd hp ha
    have hb1 : p ^ vp p a ∣ b := dvd_trans (Nat.pow_dvd_pow p (Nat.le_of_lt hlt)) (vp_dvd hp hb)
    exact dvd_add ha1 hb1
  have hle : vp p a ≤ vp p (a + b) := vp_le_of_dvd hp hab h1
  have hlt2 : ¬ vp p a + 1 ≤ vp p (a + b) := by
    intro hge
    have hdab : p ^ (vp p a + 1) ∣ a + b :=
      dvd_trans (Nat.pow_dvd_pow p hge) (vp_dvd hp hab)
    have hdb : p ^ (vp p a + 1) ∣ b :=
      dvd_trans (Nat.pow_dvd_pow p hlt) (vp_dvd hp hb)
    have hda : p ^ (vp p a + 1) ∣ a := (Nat.dvd_add_left hdb).mp hdab
    exact vp_succ_not_dvd hp ha hda
  omega

private lemma vp_mul_two {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : n ≠ 0) :
    vp p (2 * n) = vp p n := by
  have h2n : 2 * n ≠ 0 := by omega
  have hcop : Nat.Coprime p 2 := hp.coprime_iff_not_dvd.mpr (by intro h; have := Nat.le_of_dvd (by decide) h; omega)
  apply le_antisymm
  · apply vp_le_of_dvd hp hn
    have h1 := vp_dvd hp h2n
    exact (hcop.pow_left _).dvd_of_dvd_mul_left h1
  · exact vp_le_of_dvd hp h2n (dvd_mul_of_dvd_right (vp_dvd hp hn) 2)

private lemma PVal.zero {p e : ℕ} (hp : p.Prime) : PVal p e 0 :=
  ⟨0, 1, hp.not_dvd_one, by simp⟩

private lemma PVal.int {p : ℕ} (hp : p.Prime) (a : ℤ) : PVal p 0 (a : ℚ) :=
  ⟨a, 1, hp.not_dvd_one, by simp⟩

private lemma PVal.nat {p : ℕ} (hp : p.Prime) (a : ℕ) : PVal p 0 (a : ℚ) :=
  ⟨(a : ℤ), 1, hp.not_dvd_one, by simp⟩

private lemma PVal.of_dvd_int {p e : ℕ} (hp : p.Prime) {z : ℤ} (h : (p : ℤ) ^ e ∣ z) :
    PVal p e (z : ℚ) := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨c, 1, hp.not_dvd_one, by push_cast; ring⟩

private lemma PVal.of_dvd_nat {p e : ℕ} (hp : p.Prime) {n : ℕ} (h : p ^ e ∣ n) :
    PVal p e (n : ℚ) := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨(c : ℤ), 1, hp.not_dvd_one, by push_cast; ring⟩

private lemma PVal.of_pow_p {p e : ℕ} (hp : p.Prime) : PVal p e ((p : ℚ) ^ e) :=
  ⟨1, 1, hp.not_dvd_one, by simp⟩

private lemma PVal.mono {p e₁ e₂ : ℕ} {q : ℚ} (hle : e₁ ≤ e₂) (hq : PVal p e₂ q) :
    PVal p e₁ q := by
  obtain ⟨a, d, hd, rfl⟩ := hq
  refine ⟨(p : ℤ) ^ (e₂ - e₁) * a, d, hd, ?_⟩
  have hadd : e₁ + (e₂ - e₁) = e₂ := by omega
  push_cast
  rw [← mul_assoc, ← pow_add, hadd]

private lemma PVal.neg {p e : ℕ} {q : ℚ} (hq : PVal p e q) : PVal p e (-q) := by
  obtain ⟨a, d, hd, rfl⟩ := hq
  exact ⟨-a, d, hd, by push_cast; ring⟩

private lemma PVal.add {p e : ℕ} (hp : p.Prime) {q₁ q₂ : ℚ}
    (h1 : PVal p e q₁) (h2 : PVal p e q₂) : PVal p e (q₁ + q₂) := by
  obtain ⟨a₁, d₁, hd₁, rfl⟩ := h1
  obtain ⟨a₂, d₂, hd₂, rfl⟩ := h2
  have hd₁0 : (d₁ : ℚ) ≠ 0 := by
    exact_mod_cast (show d₁ ≠ 0 by intro h; subst h; exact hd₁ (dvd_zero p))
  have hd₂0 : (d₂ : ℚ) ≠ 0 := by
    exact_mod_cast (show d₂ ≠ 0 by intro h; subst h; exact hd₂ (dvd_zero p))
  refine ⟨a₁ * (d₂ : ℤ) + a₂ * (d₁ : ℤ), d₁ * d₂, ?_, ?_⟩
  · intro h
    rcases hp.dvd_mul.mp h with h | h
    · exact hd₁ h
    · exact hd₂ h
  · push_cast
    field_simp [hd₁0, hd₂0]

private lemma PVal.sub {p e : ℕ} (hp : p.Prime) {q₁ q₂ : ℚ}
    (h1 : PVal p e q₁) (h2 : PVal p e q₂) : PVal p e (q₁ - q₂) := by
  rw [sub_eq_add_neg]
  exact h1.add hp h2.neg

private lemma PVal.mul {p e₁ e₂ : ℕ} (hp : p.Prime) {q₁ q₂ : ℚ}
    (h1 : PVal p e₁ q₁) (h2 : PVal p e₂ q₂) : PVal p (e₁ + e₂) (q₁ * q₂) := by
  obtain ⟨a₁, d₁, hd₁, rfl⟩ := h1
  obtain ⟨a₂, d₂, hd₂, rfl⟩ := h2
  refine ⟨a₁ * a₂, d₁ * d₂, ?_, ?_⟩
  · intro h
    rcases hp.dvd_mul.mp h with h | h
    · exact hd₁ h
    · exact hd₂ h
  · push_cast
    rw [pow_add]
    ring

private lemma PVal.mul_zero {p e : ℕ} (hp : p.Prime) {q₁ q₂ : ℚ}
    (h1 : PVal p e q₁) (h2 : PVal p 0 q₂) : PVal p e (q₁ * q₂) := by
  simpa using h1.mul hp h2

private lemma PVal.zero_mul {p e : ℕ} (hp : p.Prime) {q₁ q₂ : ℚ}
    (h1 : PVal p 0 q₁) (h2 : PVal p e q₂) : PVal p e (q₁ * q₂) := by
  simpa using h1.mul hp h2

private lemma PVal.inv_nat {p d : ℕ} (hd : ¬ p ∣ d) : PVal p 0 ((d : ℚ)⁻¹) :=
  ⟨1, d, hd, by simp [div_eq_mul_inv]⟩

private lemma PVal.div_nat {p e : ℕ} (hp : p.Prime) {q : ℚ} {d : ℕ}
    (hq : PVal p e q) (hd : ¬ p ∣ d) : PVal p e (q / (d : ℚ)) := by
  rw [div_eq_mul_inv]
  exact hq.mul_zero hp (PVal.inv_nat hd)

private lemma PVal.div_int {p e : ℕ} (hp : p.Prime) {q : ℚ} {m : ℤ}
    (hq : PVal p e q) (hm : ¬ (p : ℤ) ∣ m) : PVal p e (q / (m : ℚ)) := by
  have hna : ¬ p ∣ m.natAbs := by
    intro h
    apply hm
    exact Int.natCast_dvd.mpr h
  rcases Int.natAbs_eq m with h | h
  · have hq' : (m : ℚ) = (m.natAbs : ℚ) := by
      have := congrArg (Int.cast : ℤ → ℚ) h; simpa using this
    rw [hq']
    exact hq.div_nat hp hna
  · have hq' : (m : ℚ) = - (m.natAbs : ℚ) := by
      have := congrArg (Int.cast : ℤ → ℚ) h; simpa using this
    rw [hq', div_neg]
    exact (hq.div_nat hp hna).neg

private lemma PVal.div_pow_p {p e m : ℕ} (hp : p.Prime) {q : ℚ}
    (hq : PVal p (e + m) q) : PVal p e (q / (p : ℚ) ^ m) := by
  obtain ⟨a, d, hd, rfl⟩ := hq
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  refine ⟨a, d, hd, ?_⟩
  rw [pow_add]
  field_simp [hp0]

private lemma PVal.div_nat_vp {p e m : ℕ} (hp : p.Prime) {q : ℚ} {d : ℕ}
    (hd0 : d ≠ 0) (hm : vp p d ≤ m) (hq : PVal p (e + m) q) :
    PVal p e (q / (d : ℚ)) := by
  obtain ⟨u, hu, hdu⟩ := vp_split hp hd0
  have hq' : PVal p (e + vp p d) q := hq.mono (by omega)
  have h1 : PVal p e (q / (p : ℚ) ^ vp p d) := hq'.div_pow_p hp
  have h2 : PVal p e ((q / (p : ℚ) ^ vp p d) / (u : ℚ)) := h1.div_nat hp hu
  have heq : q / (d : ℚ) = (q / (p : ℚ) ^ vp p d) / (u : ℚ) := by
    conv_lhs => rw [hdu]
    push_cast; rw [div_div]
  rwa [heq]

private lemma PVal.sum {ι : Type*} {s : Finset ι} {p e : ℕ} (hp : p.Prime) {f : ι → ℚ}
    (h : ∀ i ∈ s, PVal p e (f i)) : PVal p e (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PVal.zero hp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (mem_insert_self a s)).add hp (ih fun i hi => h i (mem_insert_of_mem hi))

private lemma PVal.prod_zero {ι : Type*} {s : Finset ι} {p : ℕ} (hp : p.Prime) {f : ι → ℚ}
    (h : ∀ i ∈ s, PVal p 0 (f i)) : PVal p 0 (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PVal.nat hp 1
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (mem_insert_self a s)).mul_zero hp (ih fun i hi => h i (mem_insert_of_mem hi))

private lemma PVal.pow {p e : ℕ} (hp : p.Prime) {q : ℚ} (hq : PVal p e q) (m : ℕ) :
    PVal p (m * e) (q ^ m) := by
  induction m with
  | zero => simpa using PVal.nat hp 1
  | succ m ih =>
    rw [pow_succ, show (m + 1) * e = m * e + e by ring]
    exact ih.mul hp hq

private lemma PVal.prod_one_add {ι : Type*} {s : Finset ι} {p e : ℕ} (hp : p.Prime) {f : ι → ℚ}
    (h : ∀ i ∈ s, PVal p e (f i)) : PVal p e ((∏ i ∈ s, (1 + f i)) - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PVal.zero hp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hfa : PVal p e (f a) := h a (mem_insert_self a s)
    have hP : PVal p e ((∏ i ∈ s, (1 + f i)) - 1) := ih fun i hi => h i (mem_insert_of_mem hi)
    have heq : (1 + f a) * (∏ i ∈ s, (1 + f i)) - 1 =
        f a * ((∏ i ∈ s, (1 + f i)) - 1) + f a + ((∏ i ∈ s, (1 + f i)) - 1) := by ring
    rw [heq]
    have hmul : PVal p e (f a * ((∏ i ∈ s, (1 + f i)) - 1)) :=
      (hfa.mul hp hP).mono (by omega)
    exact (hmul.add hp hfa).add hp hP

private lemma PVal.one_add_ne_zero {p e : ℕ} (_hp : p.Prime) (he : 1 ≤ e) {z : ℚ}
    (hz : PVal p e z) : 1 + z ≠ 0 := by
  obtain ⟨a, d, hd, rfl⟩ := hz
  have hd0 : (d : ℚ) ≠ 0 := by
    exact_mod_cast (show d ≠ 0 by intro h; subst h; exact hd (dvd_zero p))
  intro h0
  have hm : ((d : ℤ) + (p : ℤ) ^ e * a : ℚ) = 0 := by
    have : (1 + (p : ℚ) ^ e * (a : ℚ) / (d : ℚ)) * (d : ℚ) = 0 := by simp [h0]
    have h2 : (d : ℚ) + (p : ℚ) ^ e * (a : ℚ) = 0 := by
      have h3 : (1 + (p : ℚ) ^ e * (a : ℚ) / (d : ℚ)) * (d : ℚ) = (d : ℚ) + (p : ℚ) ^ e * (a : ℚ) := by
        field_simp [hd0]
      linarith
    exact_mod_cast h2
  have hmi : (d : ℤ) + (p : ℤ) ^ e * a = 0 := by exact_mod_cast hm
  have hpd : (p : ℤ) ∣ (d : ℤ) := by
    have hpe : (p : ℤ) ∣ (p : ℤ) ^ e := dvd_pow_self (p : ℤ) (by omega)
    have h1 : (p : ℤ) ∣ (p : ℤ) ^ e * a := dvd_mul_of_dvd_left hpe a
    have h2 : (d : ℤ) = -((p : ℤ) ^ e * a) := by linarith
    rw [h2]; exact dvd_neg.mpr h1
  exact hd (Int.natCast_dvd_natCast.mp hpd)

private lemma PVal.inv_one_add {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) {z : ℚ}
    (hz : PVal p e z) : PVal p e ((1 + z)⁻¹ - 1) := by
  obtain ⟨a, d, hd, rfl⟩ := hz
  have hd0 : (d : ℚ) ≠ 0 := by
    exact_mod_cast (show d ≠ 0 by intro h; subst h; exact hd (dvd_zero p))
  set m : ℤ := (d : ℤ) + (p : ℤ) ^ e * a
  have hpm : ¬ (p : ℤ) ∣ m := by
    intro hm
    have hpe : (p : ℤ) ∣ (p : ℤ) ^ e * a := dvd_mul_of_dvd_left (dvd_pow_self (p : ℤ) (by omega)) a
    have hpd : (p : ℤ) ∣ (d : ℤ) := by
      have : (d : ℤ) = m - (p : ℤ) ^ e * a := by simp [m]
      rw [this]; exact dvd_sub hm hpe
    exact hd (Int.natCast_dvd_natCast.mp hpd)
  have hm0 : (m : ℚ) ≠ 0 := by
    intro h
    have : m = 0 := by exact_mod_cast h
    rw [this] at hpm; exact hpm (dvd_zero _)
  have heq : (1 + (p : ℚ) ^ e * (a : ℚ) / (d : ℚ))⁻¹ - 1 =
      (-((p : ℚ) ^ e * (a : ℚ))) / (m : ℚ) := by
    have h1 : 1 + (p : ℚ) ^ e * (a : ℚ) / (d : ℚ) = (m : ℚ) / (d : ℚ) := by
      simp only [m]; push_cast; field_simp [hd0]
    rw [h1, inv_div]
    field_simp [hm0]
    simp only [m]; push_cast; ring
  rw [heq]
  have hnum : PVal p e (-((p : ℚ) ^ e * (a : ℚ))) :=
    (PVal.of_pow_p hp |>.mul_zero hp (PVal.int hp a)).neg
  exact hnum.div_int hp hpm

private lemma PVal.int_dvd {p e : ℕ} (hp : p.Prime) {z : ℤ} (h : PVal p e (z : ℚ)) :
    (p : ℤ) ^ e ∣ z := by
  obtain ⟨a, d, hd, hq⟩ := h
  have hd0 : (d : ℚ) ≠ 0 := by
    exact_mod_cast (show d ≠ 0 by intro h0; subst h0; exact hd (dvd_zero p))
  have hmul_q : (z : ℚ) * (d : ℚ) = (p : ℚ) ^ e * (a : ℚ) := by
    rw [hq]; field_simp [hd0]
  have hmul : z * (d : ℤ) = (p : ℤ) ^ e * a := by exact_mod_cast hmul_q
  have hdvd : (p : ℤ) ^ e ∣ z * (d : ℤ) := ⟨a, hmul⟩
  have hcop_nat : Nat.Coprime (p ^ e) d := (hp.coprime_iff_not_dvd.mpr hd).pow_left e
  have hcop : IsCoprime ((p : ℤ) ^ e) (d : ℤ) := by
    have h := (Nat.coprime_iff_gcd_eq_one.mp hcop_nat)
    exact_mod_cast Nat.Coprime.isCoprime hcop_nat
  exact hcop.dvd_of_dvd_mul_right hdvd

private lemma PVal.modEq_of_sub {p e : ℕ} (hp : p.Prime) {x y : ℤ}
    (h : PVal p e ((x : ℚ) - (y : ℚ))) : x ≡ y [ZMOD (p : ℤ) ^ e] := by
  have h' : PVal p e (((y - x : ℤ) : ℚ)) := by
    have : ((y - x : ℤ) : ℚ) = -((x : ℚ) - (y : ℚ)) := by push_cast; ring
    rw [this]; exact h.neg
  exact Int.modEq_iff_dvd.mpr (PVal.int_dvd hp h')

/-- L2.1(a): For every prime p >= 5, sum_{i=1}^{p-1} i^{-2} lies in p * Z_(p). -/
private lemma sum_inv_sq_mod_p (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    PVal p 1 (∑ i ∈ Ico 1 p, ((i : ℚ) ^ 2)⁻¹) := by
  have : Fact p.Prime := ⟨hp⟩
  -- Work in ZMod p via the bijection i |-> (2 * i) % p on Ico 1 p
  set S : ZMod p := ∑ i ∈ Ico 1 p, ((i : ZMod p) ^ 2)⁻¹
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by decide) hd
    omega
  have h3ne : (3 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by decide) hd
    omega
  have hbij : S = ∑ i ∈ Ico 1 p, ((((2 * i) % p : ℕ) : ZMod p) ^ 2)⁻¹ := by
    symm
    refine Finset.sum_bij (fun i _ => (2 * i) % p) ?_ ?_ ?_ ?_
    · intro i hi
      rw [mem_Ico] at hi ⊢
      refine ⟨?_, Nat.mod_lt _ hp.pos⟩
      by_contra hlt
      have h0 : (2 * i) % p = 0 := by omega
      have hd : p ∣ 2 * i := Nat.dvd_of_mod_eq_zero h0
      rcases hp.dvd_mul.mp hd with h2 | hi'
      · have := Nat.le_of_dvd (by decide) h2; omega
      · have := Nat.le_of_dvd (by omega) hi'; omega
    · intro i hi j hj heq
      rw [mem_Ico] at hi hj
      have hmod : ((2 * i : ℕ) : ZMod p) = ((2 * j : ℕ) : ZMod p) := by
        rw [← ZMod.natCast_mod (2 * i) p, ← ZMod.natCast_mod (2 * j) p, heq]
      push_cast at hmod
      have hij : (i : ZMod p) = (j : ZMod p) := mul_left_cancel₀ h2ne hmod
      have hval : i % p = j % p := by
        have h1 := congrArg ZMod.val hij
        simpa [ZMod.val_natCast] using h1
      rwa [Nat.mod_eq_of_lt hi.2, Nat.mod_eq_of_lt hj.2] at hval
    · intro b hb
      rw [mem_Ico] at hb
      have hinv_ne : ((2 : ZMod p)⁻¹ * (b : ZMod p)).val ≠ 0 := by
        intro h0
        have hz : (2 : ZMod p)⁻¹ * (b : ZMod p) = 0 := by
          rw [← ZMod.natCast_zmod_val ((2 : ZMod p)⁻¹ * (b : ZMod p)), h0]; simp
        have hb0 : (b : ZMod p) = 0 := by
          have h := congrArg (fun x => (2 : ZMod p) * x) hz
          rw [← mul_assoc, mul_inv_cancel₀ h2ne, one_mul, mul_zero] at h
          exact h
        have hd : p ∣ b := (ZMod.natCast_eq_zero_iff b p).mp hb0
        have := Nat.le_of_dvd (by omega) hd
        omega
      refine ⟨((2 : ZMod p)⁻¹ * (b : ZMod p)).val, ?_, ?_⟩
      · rw [mem_Ico]
        exact ⟨Nat.pos_of_ne_zero hinv_ne, ZMod.val_lt _⟩
      · have hcast : (((2 * ((2 : ZMod p)⁻¹ * (b : ZMod p)).val) % p : ℕ) : ZMod p) = (b : ZMod p) := by
          rw [ZMod.natCast_mod]; push_cast; rw [ZMod.natCast_zmod_val]
          rw [← mul_assoc, mul_inv_cancel₀ h2ne, one_mul]
        have hv := congrArg ZMod.val hcast
        rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (Nat.mod_lt _ hp.pos),
          Nat.mod_eq_of_lt hb.2] at hv
        exact hv
    · intro i _; rfl
  have hS_scale : S = ((2 : ZMod p) ^ 2)⁻¹ * S := by
    calc S = ∑ i ∈ Ico 1 p, ((((2 * i) % p : ℕ) : ZMod p) ^ 2)⁻¹ := hbij
      _ = ∑ i ∈ Ico 1 p, (((2 : ZMod p) * (i : ZMod p)) ^ 2)⁻¹ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [ZMod.natCast_mod]; push_cast; rfl
      _ = ∑ i ∈ Ico 1 p, ((2 : ZMod p) ^ 2)⁻¹ * ((i : ZMod p) ^ 2)⁻¹ := by
          refine Finset.sum_congr rfl fun i _ => by rw [mul_pow, mul_inv]
      _ = ((2 : ZMod p) ^ 2)⁻¹ * S := by rw [← Finset.mul_sum]
  have hS0 : S = 0 := by
    have h4 : (2 : ZMod p) ^ 2 * S = S := by
      have h := congrArg (fun x => (2 : ZMod p) ^ 2 * x) hS_scale
      have h22 : (2 : ZMod p) ^ 2 ≠ 0 := pow_ne_zero 2 h2ne
      rw [← mul_assoc, mul_inv_cancel₀ h22, one_mul] at h
      exact h
    have h3 : (3 : ZMod p) * S = 0 := by
      have : ((2 : ZMod p) ^ 2 - 1) * S = 0 := by rw [sub_mul, one_mul, h4, sub_self]
      have h21 : (2 : ZMod p) ^ 2 - 1 = (3 : ZMod p) := by ring
      rwa [h21] at this
    exact (mul_eq_zero.mp h3).resolve_left h3ne
  -- Lift S = 0 in ZMod p to PVal p 1 in Q via common denominator ((p - 1)!)^2
  set F : ℕ := (p - 1).factorial ^ 2
  set N : ℕ := ∑ i ∈ Ico 1 p, F / i ^ 2
  have hF_ndvd : ¬ p ∣ F := by
    intro h
    have hf : p ∣ (p - 1).factorial := hp.dvd_of_dvd_pow h
    have hle := hp.dvd_factorial.mp hf
    omega
  have hi_dvd : ∀ i ∈ Ico 1 p, i ^ 2 ∣ F := by
    intro i hi
    rw [mem_Ico] at hi
    exact pow_dvd_pow_of_dvd (Nat.dvd_factorial hi.1 (by omega)) 2
  have hN_zmod : (N : ZMod p) = 0 := by
    have hsum_z : (N : ZMod p) = (F : ZMod p) * S := by
      simp only [N, S, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [mem_Ico] at hi
      have hine : (i : ZMod p) ≠ 0 := by
        intro h0
        have hd := (ZMod.natCast_eq_zero_iff i p).mp h0
        have := Nat.le_of_dvd hi.1 hd
        omega
      have hi2ne : (i : ZMod p) ^ 2 ≠ 0 := pow_ne_zero 2 hine
      have hmul : (F / i ^ 2) * i ^ 2 = F := Nat.div_mul_cancel (hi_dvd i (mem_Ico.mpr hi))
      have hmul_z : ((F / i ^ 2 : ℕ) : ZMod p) * (i : ZMod p) ^ 2 = (F : ZMod p) := by
        have h := congrArg (Nat.cast : ℕ → ZMod p) hmul; push_cast at h; exact h
      rw [← hmul_z, mul_assoc, mul_inv_cancel₀ hi2ne, mul_one]
    rw [hsum_z, hS0, mul_zero]
  have hpN : p ∣ N := (ZMod.natCast_eq_zero_iff N p).mp hN_zmod
  have hq : ∑ i ∈ Ico 1 p, ((i : ℚ) ^ 2)⁻¹ = (N : ℚ) / (F : ℚ) := by
    have hF0 : (F : ℚ) ≠ 0 := by
      exact_mod_cast (show F ≠ 0 by intro h; rw [h] at hF_ndvd; exact hF_ndvd (dvd_zero p))
    rw [eq_div_iff hF0, Finset.sum_mul]
    simp only [N, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [mem_Ico] at hi
    have hi0 : (i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hi20 : ((i : ℚ) ^ 2) ≠ 0 := pow_ne_zero 2 hi0
    have hmul : ((F / i ^ 2 : ℕ) : ℚ) * (i : ℚ) ^ 2 = (F : ℚ) := by
      exact_mod_cast Nat.div_mul_cancel (hi_dvd i (mem_Ico.mpr hi))
    rw [← hmul, mul_comm (((F / i ^ 2 : ℕ) : ℚ)), ← mul_assoc, inv_mul_cancel₀ hi20, one_mul]
  rw [hq]
  exact (PVal.of_dvd_nat hp (by simpa using hpN)).div_nat hp hF_ndvd

/-- L2.1(b): Paired inverse sum sum_{i=1}^{(p-1)/2} 1 / (i * (p - i)) lies in p * Z_(p). -/
private lemma sum_pair_inv_mod_p (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    PVal p 1 (∑ i ∈ Ico 1 ((p - 1) / 2 + 1),
      (1 : ℚ) / ((i : ℚ) * ((p : ℚ) - (i : ℚ)))) := by
  set m := (p - 1) / 2
  obtain ⟨m', hm'⟩ := hp.odd_of_ne_two (by omega)
  have hm2 : 2 * m + 1 = p := by omega
  have hfull : 2 * ∑ i ∈ Ico 1 (m + 1), (1 : ℚ) / ((i : ℚ) * ((p : ℚ) - (i : ℚ))) =
      ∑ i ∈ Ico 1 p, (1 : ℚ) / ((i : ℚ) * ((p : ℚ) - (i : ℚ))) := by
    have hunion : Ico 1 p = Ico 1 (m + 1) ∪ Ico (m + 1) p := by
      rw [Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
    have hdisj : Disjoint (Ico 1 (m + 1)) (Ico (m + 1) p) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2; rw [mem_Ico] at hx1 hx2; omega
    rw [hunion, Finset.sum_union hdisj]
    have hsym : ∑ i ∈ Ico (m + 1) p, (1 : ℚ) / ((i : ℚ) * ((p : ℚ) - (i : ℚ))) =
        ∑ i ∈ Ico 1 (m + 1), (1 : ℚ) / ((i : ℚ) * ((p : ℚ) - (i : ℚ))) := by
      refine Finset.sum_bij (fun i _ => p - i) ?_ ?_ ?_ ?_
      · intro i hi; rw [mem_Ico] at hi ⊢; omega
      · intro i hi j hj heq; rw [mem_Ico] at hi hj; omega
      · intro b hb; rw [mem_Ico] at hb; exact ⟨p - b, by rw [mem_Ico]; omega, by omega⟩
      · intro i hi
        rw [mem_Ico] at hi
        have hsub : ((p - i : ℕ) : ℚ) = (p : ℚ) - (i : ℚ) := by
          rw [Nat.cast_sub (by omega)]
        rw [hsub]; ring
    rw [hsym]; ring
  have hdiff : PVal p 1
      (∑ i ∈ Ico 1 p, ((1 : ℚ) / ((i : ℚ) * ((p : ℚ) - (i : ℚ))) + ((i : ℚ) ^ 2)⁻¹)) := by
    refine PVal.sum hp fun i hi => ?_
    rw [mem_Ico] at hi
    have hi0 : (i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hpi0 : (p : ℚ) - (i : ℚ) ≠ 0 := by
      have : (i : ℚ) < (p : ℚ) := by exact_mod_cast hi.2
      linarith
    have heq : (1 : ℚ) / ((i : ℚ) * ((p : ℚ) - (i : ℚ))) + ((i : ℚ) ^ 2)⁻¹ =
        (p : ℚ) / (((i ^ 2 * (p - i) : ℕ) : ℚ)) := by
      push_cast
      rw [Nat.cast_sub (by omega)]
      field_simp [hi0, hpi0]
      ring
    rw [heq]
    have hnd : ¬ p ∣ i ^ 2 * (p - i) := by
      intro h
      rcases hp.dvd_mul.mp h with h1 | h2
      · have := Nat.le_of_dvd hi.1 (hp.dvd_of_dvd_pow h1); omega
      · have := Nat.le_of_dvd (by omega) h2; omega
    have hp1 : PVal p 1 (p : ℚ) := by simpa using PVal.of_pow_p (e := 1) hp
    exact hp1.div_nat hp hnd
  have hsum_full : PVal p 1 (∑ i ∈ Ico 1 p, (1 : ℚ) / ((i : ℚ) * ((p : ℚ) - (i : ℚ)))) := by
    rw [Finset.sum_add_distrib] at hdiff
    have hinv := sum_inv_sq_mod_p p hp hp5
    have hsub := hdiff.sub hp hinv
    simpa using hsub
  have hnd2 : ¬ p ∣ 2 := by
    intro h; have := Nat.le_of_dvd (by decide) h; omega
  have hres := (hsum_full.div_nat hp hnd2)
  rw [← hfull] at hres
  have h2ne : (2 : ℚ) ≠ 0 := by norm_num
  simpa [mul_div_cancel_left₀ _ h2ne] using hres

/-- L2.2: Factor u(x) = prod_{i=1}^{p-1} (x*p + i)/i and its paired form. -/
private def uFactor (p x : ℕ) : ℚ :=
  ∏ i ∈ Ico 1 p, ((x : ℚ) * (p : ℚ) + (i : ℚ)) / (i : ℚ)

private lemma uFactor_pair (p x : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    uFactor p x = ∏ i ∈ Ico 1 ((p - 1) / 2 + 1),
      (1 + (p : ℚ) ^ 2 * ((x : ℚ) * ((x : ℚ) + 1)) / ((i : ℚ) * ((p : ℚ) - (i : ℚ)))) := by
  set m := (p - 1) / 2
  obtain ⟨m', hm'⟩ := hp.odd_of_ne_two (by omega)
  have hm2 : 2 * m + 1 = p := by omega
  unfold uFactor
  have hunion : Ico 1 p = Ico 1 (m + 1) ∪ Ico (m + 1) p := by
    rw [Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
  have hdisj : Disjoint (Ico 1 (m + 1)) (Ico (m + 1) p) := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2; rw [mem_Ico] at ha1 ha2; omega
  rw [hunion, Finset.prod_union hdisj]
  have hsecond : ∏ i ∈ Ico (m + 1) p, ((x : ℚ) * (p : ℚ) + (i : ℚ)) / (i : ℚ) =
      ∏ i ∈ Ico 1 (m + 1), ((x : ℚ) * (p : ℚ) + ((p : ℚ) - (i : ℚ))) / ((p : ℚ) - (i : ℚ)) := by
    refine Finset.prod_bij (fun i _ => p - i) ?_ ?_ ?_ ?_
    · intro i hi; rw [mem_Ico] at hi ⊢; omega
    · intro i hi j hj heq; rw [mem_Ico] at hi hj; omega
    · intro b hb; rw [mem_Ico] at hb; exact ⟨p - b, by rw [mem_Ico]; omega, by omega⟩
    · intro i hi
      rw [mem_Ico] at hi
      have hsub : ((p - i : ℕ) : ℚ) = (p : ℚ) - (i : ℚ) := Nat.cast_sub (by omega)
      rw [hsub]; ring
  rw [hsecond, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [mem_Ico] at hi
  have hi0 : (i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpi0 : (p : ℚ) - (i : ℚ) ≠ 0 := by
    have : (i : ℚ) < (p : ℚ) := by exact_mod_cast (show i < p by omega)
    linarith
  field_simp [hi0, hpi0]
  ring

private lemma uFactor_sub_one_pval (p x : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    PVal p 2 (uFactor p x - 1) := by
  rw [uFactor_pair p x hp hp5]
  refine PVal.prod_one_add hp fun i hi => ?_
  rw [mem_Ico] at hi
  have hnd : ¬ p ∣ i * (p - i) := by
    intro h
    rcases hp.dvd_mul.mp h with h1 | h2
    · have := Nat.le_of_dvd hi.1 h1; omega
    · have := Nat.le_of_dvd (by omega) h2; omega
  have heq : (p : ℚ) ^ 2 * ((x : ℚ) * ((x : ℚ) + 1)) / ((i : ℚ) * ((p : ℚ) - (i : ℚ))) =
      ((p : ℚ) ^ 2 * ((x * (x + 1) : ℕ) : ℚ)) / (((i * (p - i) : ℕ) : ℚ)) := by
    push_cast; rw [Nat.cast_sub (by omega)]
  rw [heq]
  exact ((PVal.of_pow_p hp).mul_zero hp (PVal.nat hp _)).div_nat hp hnd

/-- L2.3: Truncated logarithm Log_E(1 + z) = sum_{r=0}^{E-1} (-1)^r * z^(r+1) / (r+1). -/
private def truncLog (E : ℕ) (z : ℚ) : ℚ :=
  ∑ r ∈ range E, (-1 : ℚ) ^ r * z ^ (r + 1) / ((r + 1 : ℕ) : ℚ)

private noncomputable def logPoly (E : ℕ) : ℚ[X] :=
  ∑ r ∈ range E, C ((-1 : ℚ) ^ r / ((r + 1 : ℕ) : ℚ)) * X ^ (r + 1)

private lemma logPoly_eval (E : ℕ) (z : ℚ) : (logPoly E).eval z = truncLog E z := by
  simp only [logPoly, truncLog, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  refine Finset.sum_congr rfl fun r _ => by ring

private lemma logPoly_derivative (E : ℕ) :
    Polynomial.derivative (logPoly E) = ∑ r ∈ range E, (-X : ℚ[X]) ^ r := by
  simp only [logPoly, map_sum, derivative_mul, derivative_C, zero_mul, zero_add, derivative_X_pow]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hr : ((r + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  rw [← mul_assoc, ← C_mul, Nat.add_sub_cancel]
  have hc : (-1 : ℚ) ^ r / ((r + 1 : ℕ) : ℚ) * ((r + 1 : ℕ) : ℚ) = (-1 : ℚ) ^ r := by
    field_simp [hr]
  rw [hc]
  have hneg : (-X : ℚ[X]) ^ r = C ((-1 : ℚ) ^ r) * X ^ r := by
    rw [show (-X : ℚ[X]) = C (-1 : ℚ) * X by simp, mul_pow, ← map_pow]
  rw [hneg]

private lemma vp_lt_self {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) : vp p n < n := by
  have hle := pow_vp_le hp hn
  have h2 : vp p n < 2 ^ vp p n := Nat.lt_two_pow_self
  have hp2 : 2 ^ vp p n ≤ p ^ vp p n := Nat.pow_le_pow_left hp.two_le _
  omega

/-- L2.3(a): Additivity of truncLog modulo p^E for z1, z2 in p^2 Z_(p). -/
private lemma truncLog_mul_sub (p E : ℕ) (hp : p.Prime) {z₁ z₂ : ℚ}
    (hz₁ : PVal p 2 z₁) (hz₂ : PVal p 2 z₂) :
    PVal p E (truncLog E (z₁ + z₂ + z₁ * z₂) - truncLog E z₁ - truncLog E z₂) := by
  cases E with
  | zero =>
    simp only [truncLog, range_zero, sum_empty, sub_self]
    exact PVal.zero hp
  | succ E' =>
    set E := E' + 1
    set U : ℚ[X] := C z₂ + C (1 + z₂) * X
    set Q : ℚ[X] := (logPoly E).comp U - logPoly E - C (truncLog E z₂)
    have hU_eq : U = X + C z₂ + C z₂ * X := by
      simp only [U, map_add, map_one]; ring
    have hQ_eval : Q.eval z₁ = truncLog E (z₁ + z₂ + z₁ * z₂) - truncLog E z₁ - truncLog E z₂ := by
      simp only [Q, eval_sub, eval_comp, eval_C, logPoly_eval]
      have hU_ev : U.eval z₁ = z₁ + z₂ + z₁ * z₂ := by
        simp only [U, eval_add, eval_mul, eval_C, eval_X]; ring
      rw [hU_ev]
    have hQ0 : Q.eval 0 = 0 := by
      simp only [Q, eval_sub, eval_comp, eval_C, logPoly_eval]
      have hU0 : U.eval 0 = z₂ := by simp [U]
      have hl0 : truncLog E 0 = 0 := by
        simp [truncLog]
      rw [hU0, hl0]; ring
    have hQcoeff0 : Q.coeff 0 = 0 := by
      rw [coeff_zero_eq_eval_zero, hQ0]
    -- Compute derivative Q explicitly via (1 + X) * derivative Q = (-X)^E - (-U)^E
    set R : ℚ[X] := C z₂ * ∑ t ∈ range E, (-X : ℚ[X]) ^ t * (-U) ^ (E - 1 - t)
    have hderiv : Polynomial.derivative Q = R := by
      have h1X_ne : (1 + X : ℚ[X]) ≠ 0 := by
        intro h
        have := congrArg (fun P : ℚ[X] => P.eval 0) h
        simp at this
      apply mul_left_cancel₀ h1X_ne
      have hU_der : Polynomial.derivative U = C (1 + z₂) := by
        simp [U, derivative_add, derivative_mul, derivative_C, derivative_X]
      have hdQ : Polynomial.derivative Q =
          (∑ r ∈ range E, (-U) ^ r) * C (1 + z₂) - ∑ r ∈ range E, (-X : ℚ[X]) ^ r := by
        simp only [Q, derivative_sub, derivative_C, sub_zero, derivative_comp, logPoly_derivative, hU_der]
        congr 1
        rw [mul_comm]
        congr 1
        simp only [Polynomial.sum_comp, Polynomial.pow_comp, Polynomial.neg_comp, Polynomial.X_comp]
      have h1U : (1 + X : ℚ[X]) * C (1 + z₂) = 1 + U := by
        simp only [U, map_add, map_one]; ring
      have hg1 : (1 + U) * ∑ r ∈ range E, (-U) ^ r = 1 - (-U) ^ E := by
        have h := geom_sum_mul (-U) E
        -- (∑ r < E, (-U)^r) * (-U - 1) = (-U)^E - 1
        have h2 : (1 + U) = -((-U) - 1) := by ring
        rw [h2, neg_mul, mul_comm _ (∑ r ∈ range E, (-U) ^ r), h]; ring
      have hg2 : (1 + X : ℚ[X]) * ∑ r ∈ range E, (-X : ℚ[X]) ^ r = 1 - (-X : ℚ[X]) ^ E := by
        have h := geom_sum_mul (-X : ℚ[X]) E
        have h2 : (1 + X : ℚ[X]) = -((-X : ℚ[X]) - 1) := by ring
        rw [h2, neg_mul, mul_comm _ (∑ r ∈ range E, (-X : ℚ[X]) ^ r), h]; ring
      have hLHS : (1 + X : ℚ[X]) * Polynomial.derivative Q = (-X : ℚ[X]) ^ E - (-U) ^ E := by
        rw [hdQ, mul_sub]
        have hpart : (1 + X : ℚ[X]) * ((∑ r ∈ range E, (-U) ^ r) * C (1 + z₂)) =
            (1 + U) * ∑ r ∈ range E, (-U) ^ r := by
          calc (1 + X : ℚ[X]) * ((∑ r ∈ range E, (-U) ^ r) * C (1 + z₂))
              = ((1 + X : ℚ[X]) * C (1 + z₂)) * ∑ r ∈ range E, (-U) ^ r := by ring
            _ = (1 + U) * ∑ r ∈ range E, (-U) ^ r := by rw [h1U]
        rw [hpart, hg1, hg2]; ring
      have hRHS : (1 + X : ℚ[X]) * R = (-X : ℚ[X]) ^ E - (-U) ^ E := by
        have hsub : (-X : ℚ[X]) - (-U) = (1 + X : ℚ[X]) * C z₂ := by
          rw [hU_eq]; ring
        have hg := geom_sum₂_mul (-X : ℚ[X]) (-U) E
        -- (∑ t < E, (-X)^t * (-U)^(E-1-t)) * (-X - -U) = (-X)^E - (-U)^E
        calc (1 + X : ℚ[X]) * R
            = (∑ t ∈ range E, (-X : ℚ[X]) ^ t * (-U) ^ (E - 1 - t)) * ((1 + X : ℚ[X]) * C z₂) := by
                simp only [R]; ring
          _ = (∑ t ∈ range E, (-X : ℚ[X]) ^ t * (-U) ^ (E - 1 - t)) * ((-X : ℚ[X]) - (-U)) := by
                rw [hsub]
          _ = (-X : ℚ[X]) ^ E - (-U) ^ E := hg
      rw [hLHS, hRHS]
    -- Show R.coeff k = 0 for k >= E and PVal p (2 * (E - k)) (R.coeff k) for k < E
    have hR_coeff : ∀ k : ℕ,
        (E ≤ k → R.coeff k = 0) ∧ (k < E → PVal p (2 * (E - k)) (R.coeff k)) := by
      intro k
      have hR_form : R.coeff k =
          z₂ * ∑ t ∈ range E, (-1 : ℚ) ^ (E - 1) * (X ^ t * U ^ (E - 1 - t)).coeff k := by
        simp only [R, coeff_C_mul, finsetSum_coeff]
        congr 1
        refine Finset.sum_congr rfl fun t ht => ?_
        have htE : t < E := mem_range.mp ht
        have hneg1 : (-X : ℚ[X]) ^ t * (-U) ^ (E - 1 - t) =
            C ((-1 : ℚ) ^ (E - 1)) * (X ^ t * U ^ (E - 1 - t)) := by
          rw [show (-X : ℚ[X]) = C (-1 : ℚ) * X by simp,
              show (-U : ℚ[X]) = C (-1 : ℚ) * U by simp,
              mul_pow, mul_pow, ← map_pow, ← map_pow]
          have hexp : t + (E - 1 - t) = E - 1 := by omega
          calc C ((-1 : ℚ) ^ t) * X ^ t * (C ((-1 : ℚ) ^ (E - 1 - t)) * U ^ (E - 1 - t))
              = (C ((-1 : ℚ) ^ t) * C ((-1 : ℚ) ^ (E - 1 - t))) * (X ^ t * U ^ (E - 1 - t)) := by ring
            _ = C ((-1 : ℚ) ^ (t + (E - 1 - t))) * (X ^ t * U ^ (E - 1 - t)) := by
                rw [← C_mul, ← pow_add]
            _ = C ((-1 : ℚ) ^ (E - 1)) * (X ^ t * U ^ (E - 1 - t)) := by rw [hexp]
        rw [hneg1, coeff_C_mul]
      have hterm_coeff : ∀ t ∈ range E,
          (X ^ t * U ^ (E - 1 - t)).coeff k =
            if t ≤ k ∧ k < E then
              ((Nat.choose (E - 1 - t) (k - t) : ℚ) * (1 + z₂) ^ (k - t) * z₂ ^ (E - 1 - k))
            else 0 := by
        intro t ht
        have htE : t < E := mem_range.mp ht
        set m := E - 1 - t
        have hpow : U ^ m = ∑ j ∈ range (m + 1),
            C ((Nat.choose m j : ℚ) * (1 + z₂) ^ j * z₂ ^ (m - j)) * X ^ j := by
          have hadd := add_pow (C (1 + z₂) * X) (C z₂) m
          have hU' : U = C (1 + z₂) * X + C z₂ := by simp only [U]; ring
          rw [hU', hadd]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [map_mul, map_pow, map_natCast, mul_pow]
          ring
        rw [hpow, Finset.mul_sum, finsetSum_coeff]
        by_cases hcond : t ≤ k ∧ k < E
        · simp only [hcond, and_self, ↓reduceIte]
          have hkt : k - t ∈ range (m + 1) := by rw [mem_range]; omega
          rw [Finset.sum_eq_single (k - t)]
          · have hre : X ^ t * (C ((Nat.choose m (k - t) : ℚ) * (1 + z₂) ^ (k - t) * z₂ ^ (m - (k - t))) * X ^ (k - t)) =
                C ((Nat.choose m (k - t) : ℚ) * (1 + z₂) ^ (k - t) * z₂ ^ (m - (k - t))) * X ^ k := by
              have hX : (X : ℚ[X]) ^ t * X ^ (k - t) = X ^ k := by
                rw [← pow_add, Nat.add_sub_of_le hcond.1]
              rw [← hX]; ring
            rw [hre, coeff_C_mul, coeff_X_pow_self, mul_one]
            rw [show m - (k - t) = E - 1 - k by omega]
          · intro j hj hne
            have hre : X ^ t * (C ((Nat.choose m j : ℚ) * (1 + z₂) ^ j * z₂ ^ (m - j)) * X ^ j) =
                C ((Nat.choose m j : ℚ) * (1 + z₂) ^ j * z₂ ^ (m - j)) * X ^ (t + j) := by
              rw [pow_add]; ring
            rw [hre, coeff_C_mul, coeff_X_pow]
            have hneq : k ≠ t + j := by omega
            simp [hneq]
          · intro h; exact absurd hkt h
        · simp only [hcond, ↓reduceIte]
          refine Finset.sum_eq_zero fun j hj => ?_
          have hjm : j < m + 1 := mem_range.mp hj
          have hre : X ^ t * (C ((Nat.choose m j : ℚ) * (1 + z₂) ^ j * z₂ ^ (m - j)) * X ^ j) =
              C ((Nat.choose m j : ℚ) * (1 + z₂) ^ j * z₂ ^ (m - j)) * X ^ (t + j) := by
            rw [pow_add]; ring
          rw [hre, coeff_C_mul, coeff_X_pow]
          have hneq : k ≠ t + j := by omega
          simp [hneq]
      constructor
      · intro hEk
        rw [hR_form]
        have hzero : ∀ t ∈ range E, (-1 : ℚ) ^ (E - 1) * (X ^ t * U ^ (E - 1 - t)).coeff k = 0 := by
          intro t ht
          rw [hterm_coeff t ht]
          have : ¬ (t ≤ k ∧ k < E) := by omega
          simp [this]
        rw [Finset.sum_eq_zero hzero, mul_zero]
      · intro hkE
        rw [hR_form]
        have hz2_pow : PVal p (2 * (E - 1 - k)) (z₂ ^ (E - 1 - k)) := by
          simpa [mul_comm] using hz₂.pow hp (E - 1 - k)
        have hsum_pv : PVal p (2 * (E - 1 - k))
            (∑ t ∈ range E, (-1 : ℚ) ^ (E - 1) * (X ^ t * U ^ (E - 1 - t)).coeff k) := by
          refine PVal.sum hp fun t ht => ?_
          rw [hterm_coeff t ht]
          split_ifs with hcond
          · have h1z : PVal p 0 (1 + z₂) := (PVal.nat hp 1).add hp (hz₂.mono (by omega))
            have hcoef : PVal p 0
                ((-1 : ℚ) ^ (E - 1) * ((Nat.choose (E - 1 - t) (k - t) : ℚ) * (1 + z₂) ^ (k - t))) := by
              have hm1 : PVal p 0 ((-1 : ℚ) ^ (E - 1)) := by
                simpa using (PVal.int hp (-1)).pow hp (E - 1)
              have hch : PVal p 0 (Nat.choose (E - 1 - t) (k - t) : ℚ) := PVal.nat hp _
              have hp1z : PVal p 0 ((1 + z₂) ^ (k - t)) := by simpa using h1z.pow hp (k - t)
              exact hm1.mul_zero hp (hch.mul_zero hp hp1z)
            have hre : (-1 : ℚ) ^ (E - 1) *
                ((Nat.choose (E - 1 - t) (k - t) : ℚ) * (1 + z₂) ^ (k - t) * z₂ ^ (E - 1 - k)) =
                ((-1 : ℚ) ^ (E - 1) * ((Nat.choose (E - 1 - t) (k - t) : ℚ) * (1 + z₂) ^ (k - t))) *
                  z₂ ^ (E - 1 - k) := by ring
            rw [hre]
            exact hcoef.zero_mul hp hz2_pow
          · rw [mul_zero]; exact PVal.zero hp
        have hmul := hz₂.mul hp hsum_pv
        have hexp : 2 + 2 * (E - 1 - k) = 2 * (E - k) := by omega
        rwa [hexp] at hmul
    -- Relate Q.eval z₁ to sum of Q.coeff (k + 1) * z₁^(k + 1) for k < E
    have hQ_coeff : ∀ k : ℕ, Q.coeff (k + 1) = R.coeff k / ((k + 1 : ℕ) : ℚ) := by
      intro k
      have hd := Polynomial.coeff_derivative Q k
      rw [hderiv] at hd
      have hk0 : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      rw [eq_div_iff hk0]
      push_cast; exact hd.symm
    have hQ_deg : ∀ m : ℕ, E < m → Q.coeff m = 0 := by
      intro m hm
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      rw [hQ_coeff k, (hR_coeff k).1 (by omega), zero_div]
    have hQ_expand : Q.eval z₁ = ∑ k ∈ range E, Q.coeff (k + 1) * z₁ ^ (k + 1) := by
      rw [Polynomial.eval_eq_sum_range' (n := E + 1)]
      · rw [Finset.sum_range_succ', hQcoeff0, zero_mul, add_zero]
      · by_contra hge
        have hlt : E < Q.natDegree := by omega
        have hne : Q ≠ 0 := by
          intro h0; rw [h0, natDegree_zero] at hlt; omega
        exact (Polynomial.leadingCoeff_ne_zero.mpr hne) (by rw [Polynomial.leadingCoeff]; exact hQ_deg Q.natDegree hlt)
    rw [← hQ_eval, hQ_expand]
    refine PVal.sum hp fun k hk => ?_
    have hkE : k < E := mem_range.mp hk
    rw [hQ_coeff k]
    have hRk : PVal p (2 * (E - k)) (R.coeff k) := (hR_coeff k).2 hkE
    have hz1k : PVal p (2 * (k + 1)) (z₁ ^ (k + 1)) := by
      simpa [mul_comm] using hz₁.pow hp (k + 1)
    have hnum : PVal p (2 * E + 2) (R.coeff k * z₁ ^ (k + 1)) := by
      have hm := hRk.mul hp hz1k
      have hexp : 2 * (E - k) + 2 * (k + 1) = 2 * E + 2 := by omega
      rwa [hexp] at hm
    have hre : R.coeff k / ((k + 1 : ℕ) : ℚ) * z₁ ^ (k + 1) =
        (R.coeff k * z₁ ^ (k + 1)) / ((k + 1 : ℕ) : ℚ) := by ring
    rw [hre]
    have hvp : vp p (k + 1) ≤ E := by
      have := vp_lt_self hp (by omega : k + 1 ≠ 0)
      omega
    exact (hnum.mono (by omega : E + E ≤ 2 * E + 2)).div_nat_vp hp (by omega : k + 1 ≠ 0) hvp

private lemma truncLog_inv_add (p E : ℕ) (hp : p.Prime) {z : ℚ} (hz : PVal p 2 z) :
    PVal p E (truncLog E ((1 + z)⁻¹ - 1) + truncLog E z) := by
  have h1z : 1 + z ≠ 0 := hz.one_add_ne_zero hp (by omega)
  have hinv : PVal p 2 ((1 + z)⁻¹ - 1) := hz.inv_one_add hp (by omega)
  have hmul := truncLog_mul_sub p E hp hz hinv
  have hcomb : z + ((1 + z)⁻¹ - 1) + z * ((1 + z)⁻¹ - 1) = 0 := by
    have : z + ((1 + z)⁻¹ - 1) + z * ((1 + z)⁻¹ - 1) = (1 + z) * (1 + z)⁻¹ - 1 := by ring
    rw [this, mul_inv_cancel₀ h1z, sub_self]
  have h0 : truncLog E 0 = 0 := by simp [truncLog]
  rw [hcomb, h0] at hmul
  have heq : truncLog E ((1 + z)⁻¹ - 1) + truncLog E z =
      -(0 - truncLog E z - truncLog E ((1 + z)⁻¹ - 1)) := by ring
  rw [heq]
  exact hmul.neg

private lemma truncLog_prod {ι : Type*} (s : Finset ι) (p E : ℕ) (hp : p.Prime) (f : ι → ℚ)
    (hf : ∀ i ∈ s, PVal p 2 (f i)) :
    PVal p E (truncLog E ((∏ i ∈ s, (1 + f i)) - 1) - ∑ i ∈ s, truncLog E (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [prod_empty, sub_self, sum_empty, sub_zero]
    have h0 : truncLog E 0 = 0 := by simp [truncLog]
    rw [h0]; exact PVal.zero hp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hfa : PVal p 2 (f a) := hf a (mem_insert_self a s)
    have hPs : PVal p 2 ((∏ i ∈ s, (1 + f i)) - 1) :=
      PVal.prod_one_add hp fun i hi => hf i (mem_insert_of_mem hi)
    have hih := ih fun i hi => hf i (mem_insert_of_mem hi)
    have hmul := truncLog_mul_sub p E hp hfa hPs
    have hcomb : f a + ((∏ i ∈ s, (1 + f i)) - 1) + f a * ((∏ i ∈ s, (1 + f i)) - 1) =
        (1 + f a) * (∏ i ∈ s, (1 + f i)) - 1 := by ring
    rw [hcomb] at hmul
    have hadd := hmul.add hp hih
    have heq : (truncLog E ((1 + f a) * (∏ i ∈ s, (1 + f i)) - 1) - truncLog E (f a) -
          truncLog E ((∏ i ∈ s, (1 + f i)) - 1)) +
        (truncLog E ((∏ i ∈ s, (1 + f i)) - 1) - ∑ i ∈ s, truncLog E (f i)) =
        truncLog E ((1 + f a) * (∏ i ∈ s, (1 + f i)) - 1) - (truncLog E (f a) + ∑ i ∈ s, truncLog E (f i)) := by
      ring
    rwa [heq] at hadd

private lemma truncLog_div_sub (p E : ℕ) (hp : p.Prime) {A B : ℚ}
    (hA : PVal p 2 (A - 1)) (hB : PVal p 2 (B - 1)) :
    PVal p E (truncLog E (A / B - 1) - (truncLog E (A - 1) - truncLog E (B - 1))) := by
  have hB0 : B ≠ 0 := by
    have := hB.one_add_ne_zero hp (by omega)
    simpa using this
  have hBinv : PVal p 2 (B⁻¹ - 1) := by
    have := hB.inv_one_add hp (by omega)
    simpa using this
  have h1 := truncLog_mul_sub p E hp hA hBinv
  have h2 := truncLog_inv_add p E hp hB
  have hcomb : (A - 1) + (B⁻¹ - 1) + (A - 1) * (B⁻¹ - 1) = A / B - 1 := by
    rw [div_eq_mul_inv]; ring
  rw [hcomb] at h1
  have h2' : PVal p E (truncLog E (B⁻¹ - 1) + truncLog E (B - 1)) := by simpa using h2
  have h3 := h1.add hp h2'
  have heq : (truncLog E (A / B - 1) - truncLog E (A - 1) - truncLog E (B⁻¹ - 1)) +
      (truncLog E (B⁻¹ - 1) + truncLog E (B - 1)) =
      truncLog E (A / B - 1) - (truncLog E (A - 1) - truncLog E (B - 1)) := by ring
  rwa [heq] at h3

/-- L2.3(b): Valuation preservation (injectivity) of truncLog on p^2 Z_(p). -/
private lemma truncLog_inj (p E : ℕ) (hp : p.Prime) {z : ℚ}
    (hz : PVal p 2 z) (hlog : PVal p E (truncLog E z)) : PVal p E z := by
  have hstep : ∀ v : ℕ, 2 ≤ v → v ≤ E → PVal p v z := by
    intro v hv hvE
    induction v with
    | zero => omega
    | succ v ih =>
      by_cases hv2 : v < 2
      · have heq : v + 1 = 2 := by omega
        rw [heq]; exact hz
      · have ihv : PVal p v z := ih (by omega) (by omega)
        have hEpos : 1 ≤ E := by omega
        have hlogv : PVal p (v + 1) (truncLog E z) := hlog.mono hvE
        have hsplit : truncLog E z = z + ∑ r ∈ range (E - 1),
            (-1 : ℚ) ^ (r + 1) * z ^ (r + 2) / ((r + 2 : ℕ) : ℚ) := by
          unfold truncLog
          rw [show E = (E - 1) + 1 by omega, Finset.sum_range_succ', add_comm]
          simp only [pow_zero, one_mul, zero_add, pow_one, Nat.cast_one, div_one]
          congr 1
        have htail : PVal p (v + 1)
            (∑ r ∈ range (E - 1), (-1 : ℚ) ^ (r + 1) * z ^ (r + 2) / ((r + 2 : ℕ) : ℚ)) := by
          refine PVal.sum hp fun r _ => ?_
          have hpow : PVal p ((r + 2) * v) (z ^ (r + 2)) := ihv.pow hp (r + 2)
          have hsign : PVal p 0 ((-1 : ℚ) ^ (r + 1)) := by
            simpa using (PVal.int hp (-1)).pow hp (r + 1)
          have hnum : PVal p ((r + 2) * v) ((-1 : ℚ) ^ (r + 1) * z ^ (r + 2)) :=
            hsign.zero_mul hp hpow
          have hvp : vp p (r + 2) ≤ r + 1 := by
            have := vp_lt_self hp (by omega : r + 2 ≠ 0)
            omega
          have hge : (v + 1) + (r + 1) ≤ (r + 2) * v := by
            have hv2' : 2 ≤ v := by omega
            nlinarith
          exact (hnum.mono hge).div_nat_vp hp (by omega : r + 2 ≠ 0) hvp
        have hz' : z = truncLog E z -
            ∑ r ∈ range (E - 1), (-1 : ℚ) ^ (r + 1) * z ^ (r + 2) / ((r + 2 : ℕ) : ℚ) := by
          linarith
        rw [hz']
        exact hlogv.sub hp htail
  by_cases hE2 : E ≤ 2
  · exact hz.mono hE2
  · exact hstep E (by omega) le_rfl

/-- L2.4: Falling-factorial polynomial basis and oddness/denominator bound for F_r(N). -/
private noncomputable def fallPoly (m : ℕ) : ℤ[X] :=
  ∏ i ∈ range m, (X - C (i : ℤ))

private lemma fallPoly_monic (m : ℕ) : (fallPoly m).Monic := by
  unfold fallPoly
  exact Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C (i : ℤ)

private lemma fallPoly_natDegree (m : ℕ) : (fallPoly m).natDegree = m := by
  induction m with
  | zero => simp [fallPoly]
  | succ m ih =>
    have hstep : fallPoly (m + 1) = fallPoly m * (X - C (m : ℤ)) := by
      unfold fallPoly; rw [Finset.prod_range_succ]
    rw [hstep]
    have hmon1 : (fallPoly m).Monic := fallPoly_monic m
    have hmon2 : (X - C (m : ℤ)).Monic := Polynomial.monic_X_sub_C (m : ℤ)
    rw [Polynomial.Monic.natDegree_mul hmon1 hmon2, ih, Polynomial.natDegree_X_sub_C]

private lemma poly_eq_sum_fallPoly :
    ∀ (d : ℕ) (P : ℤ[X]), P.natDegree ≤ d →
      ∃ c : ℕ → ℤ, P = ∑ m ∈ range (d + 1), C (c m) * fallPoly m := by
  intro d
  induction d with
  | zero =>
    intro P hP
    refine ⟨fun _ => P.coeff 0, ?_⟩
    simp only [Nat.reduceAdd, range_one, sum_singleton, fallPoly, range_zero, prod_empty, mul_one]
    exact Polynomial.eq_C_of_natDegree_eq_zero (Nat.le_zero.mp hP)
  | succ d ih =>
    intro P hP
    set a := P.coeff (d + 1)
    set P' := P - C a * fallPoly (d + 1)
    have hdeg' : P'.natDegree ≤ d := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro k hk
      simp only [P', coeff_sub, coeff_C_mul]
      by_cases hk1 : k = d + 1
      · subst hk1
        have hlc : (fallPoly (d + 1)).coeff (d + 1) = 1 := by
          simpa [Polynomial.leadingCoeff, fallPoly_natDegree] using (fallPoly_monic (d + 1)).leadingCoeff
        rw [hlc, mul_one, sub_self]
      · have hgt : d + 1 < k := by omega
        have h1 : P.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        have h2 : (fallPoly (d + 1)).coeff k = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [fallPoly_natDegree]; omega)
        rw [h1, h2, mul_zero, sub_zero]
    obtain ⟨c', hc'⟩ := ih P' hdeg'
    refine ⟨fun m => if m = d + 1 then a else c' m, ?_⟩
    rw [Finset.sum_range_succ]
    simp only [↓reduceIte]
    have hsum' : ∑ m ∈ range (d + 1), C (if m = d + 1 then a else c' m) * fallPoly m =
        ∑ m ∈ range (d + 1), C (c' m) * fallPoly m := by
      refine Finset.sum_congr rfl fun m hm => ?_
      have hne : m ≠ d + 1 := by rw [mem_range] at hm; omega
      simp [hne]
    rw [hsum', ← hc']
    simp [P']

private lemma fallPoly_diff (m : ℕ) :
    (fallPoly (m + 1)).comp (X + 1) - fallPoly (m + 1) = C ((m + 1 : ℕ) : ℤ) * fallPoly m := by
  have h1 : (fallPoly (m + 1)).comp (X + 1) = (X + 1) * fallPoly m := by
    unfold fallPoly
    rw [Polynomial.prod_comp, Finset.prod_range_succ']
    simp only [Nat.cast_zero, map_zero, sub_zero, Polynomial.sub_comp, Polynomial.X_comp,
      Polynomial.C_comp, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_one]; ring
  have h2 : fallPoly (m + 1) = fallPoly m * (X - C (m : ℤ)) := by
    unfold fallPoly
    rw [Finset.prod_range_succ]
  rw [h1, h2]
  have hsub : (X + 1 : ℤ[X]) - (X - C (m : ℤ)) = C ((m + 1 : ℕ) : ℤ) := by
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_one]; ring
  calc (X + 1) * fallPoly m - fallPoly m * (X - C (m : ℤ))
      = ((X + 1) - (X - C (m : ℤ))) * fallPoly m := by ring
    _ = C ((m + 1 : ℕ) : ℤ) * fallPoly m := by rw [hsub]

private lemma fallPoly_eval_zero (m : ℕ) : (fallPoly (m + 1)).eval 0 = 0 := by
  unfold fallPoly
  rw [Polynomial.eval_prod, Finset.prod_range_succ']
  simp

private lemma two_mul_add_one_lt_five_pow (r : ℕ) (hr : 1 ≤ r) : 2 * r + 1 < 5 ^ r := by
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases hr0 : r = 0
    · subst hr0; decide
    · have ih' := ih (by omega)
      rw [pow_succ]; omega

private lemma lt_five_pow_sub_one (r : ℕ) (hr : 2 ≤ r) : r < 5 ^ (r - 1) := by
  obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  simp only [Nat.succ_sub_one]
  have h := two_mul_add_one_lt_five_pow r' (by omega)
  omega

private lemma poly_eq_zero_of_eval_nat (G : ℚ[X]) (hG : ∀ N : ℕ, G.eval (N : ℚ) = 0) : G = 0 := by
  by_contra hne
  set S : Finset ℚ := (range (G.natDegree + 1)).image (fun n : ℕ => (n : ℚ))
  have hcardS : S.card = G.natDegree + 1 := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  have hsub : S ⊆ G.roots.toFinset := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨n, _, rfl⟩ := hq
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot.def]
    exact hG n
  have h1 : S.card ≤ G.roots.toFinset.card := Finset.card_le_card hsub
  have h2 : G.roots.toFinset.card ≤ G.roots.card := Multiset.toFinset_card_le _
  have h3 : G.roots.card ≤ G.natDegree := Polynomial.card_roots' G
  omega

private lemma coeff_comp_neg_X_q (P : ℚ[X]) (t : ℕ) :
    (P.comp (-X)).coeff t = (-1 : ℚ) ^ t * P.coeff t := by
  conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow P]
  rw [Polynomial.sum_comp, Polynomial.finsetSum_coeff]
  have hterm : ∀ i : ℕ, ((C (P.coeff i) * X ^ i).comp (-X)).coeff t =
      if t = i then (-1 : ℚ) ^ t * P.coeff t else 0 := by
    intro i
    rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp]
    rw [show (-X : ℚ[X]) = C (-1 : ℚ) * X by simp, mul_pow, ← map_pow, ← mul_assoc, ← C_mul]
    rw [coeff_C_mul, coeff_X_pow]
    split_ifs with h
    · subst h; ring
    · ring
  simp_rw [hterm]
  by_cases ht : t ∈ range (P.natDegree + 1)
  · rw [Finset.sum_eq_single t]
    · simp
    · intro i _ hne; simp [Ne.symm hne]
    · intro h; exact absurd ht h
  · rw [Finset.sum_eq_zero]
    · have hlt : P.natDegree < t := by rw [mem_range] at ht; omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, mul_zero]
    · intro i hi
      have hne : t ≠ i := by intro h; subst h; exact ht hi
      simp [hne]

private lemma power_sum_odd_poly (r : ℕ) (hr : 1 ≤ r) :
    ∃ F : ℚ[X],
      (∀ N : ℕ, F.eval (N : ℚ) = ∑ j ∈ range N, ((j : ℚ) * ((j : ℚ) + 1)) ^ r) ∧
      (∀ t : ℕ, Even t → F.coeff t = 0) ∧
      (∀ t : ℕ, 2 * r + 1 < t → F.coeff t = 0) ∧
      (∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ t : ℕ,
        PVal p 0 ((p : ℚ) ^ (r - 1) * F.coeff t)) := by
  set P : ℤ[X] := (X * (X + 1)) ^ r
  have hdegP : P.natDegree ≤ 2 * r := by
    have h1 : (X * (X + 1) : ℤ[X]).natDegree ≤ 2 := by
      calc (X * (X + 1) : ℤ[X]).natDegree
          ≤ (X : ℤ[X]).natDegree + (X + 1 : ℤ[X]).natDegree := Polynomial.natDegree_mul_le
        _ ≤ 1 + 1 := by
            have hX : (X : ℤ[X]).natDegree ≤ 1 := by simp
            have hX1 : (X + 1 : ℤ[X]).natDegree ≤ 1 := by
              calc (X + 1 : ℤ[X]).natDegree
                  ≤ max (X : ℤ[X]).natDegree (1 : ℤ[X]).natDegree := Polynomial.natDegree_add_le _ _
                _ ≤ 1 := by simp
            omega
        _ = 2 := rfl
    calc P.natDegree ≤ r * (X * (X + 1) : ℤ[X]).natDegree := Polynomial.natDegree_pow_le
      _ ≤ r * 2 := Nat.mul_le_mul_left r h1
      _ = 2 * r := by ring
  obtain ⟨c, hc⟩ := poly_eq_sum_fallPoly (2 * r) P hdegP
  set φ : ℤ →+* ℚ := Int.castRingHom ℚ
  set F : ℚ[X] := ∑ m ∈ range (2 * r + 1),
    C ((c m : ℚ) / ((m + 1 : ℕ) : ℚ)) * (fallPoly (m + 1)).map φ
  have hF0 : F.eval 0 = 0 := by
    simp only [F, eval_finsetSum, eval_mul, eval_C]
    refine Finset.sum_eq_zero fun m _ => ?_
    have hm0 : ((fallPoly (m + 1)).map φ).eval 0 = 0 := by
      rw [show (0 : ℚ) = φ 0 by simp, Polynomial.eval_map, Polynomial.eval₂_at_apply,
          fallPoly_eval_zero, map_zero]
    rw [hm0, mul_zero]
  have hF_diff : F.comp (X + 1) - F = (X * (X + 1)) ^ r := by
    simp only [F, Polynomial.sum_comp, Polynomial.mul_comp, Polynomial.C_comp, ← Finset.sum_sub_distrib]
    have hterm : ∀ m ∈ range (2 * r + 1),
        C ((c m : ℚ) / ((m + 1 : ℕ) : ℚ)) * ((fallPoly (m + 1)).map φ).comp (X + 1) -
          C ((c m : ℚ) / ((m + 1 : ℕ) : ℚ)) * (fallPoly (m + 1)).map φ =
        C (c m : ℚ) * (fallPoly m).map φ := by
      intro m _
      rw [← mul_sub]
      have hmap_diff : ((fallPoly (m + 1)).map φ).comp (X + 1) - (fallPoly (m + 1)).map φ =
          C ((m + 1 : ℕ) : ℚ) * (fallPoly m).map φ := by
        have h := congrArg (Polynomial.map φ) (fallPoly_diff m)
        rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C] at h
        have hcomp : ((fallPoly (m + 1)).comp (X + 1)).map φ =
            ((fallPoly (m + 1)).map φ).comp (X + 1) := by
          rw [Polynomial.map_comp, Polynomial.map_add, Polynomial.map_X, Polynomial.map_one]
        rw [hcomp] at h
        simpa [φ] using h
      rw [hmap_diff, ← mul_assoc, ← C_mul]
      have hm0 : ((m + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      congr 2
      field_simp [hm0]
    rw [Finset.sum_congr rfl hterm]
    have hmapP := congrArg (Polynomial.map φ) hc
    simp only [P, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_X,
      Polynomial.map_one, Polynomial.map_sum, Polynomial.map_C] at hmapP
    simpa [φ] using hmapP.symm
  have hF_eval : ∀ N : ℕ, F.eval (N : ℚ) = ∑ j ∈ range N, ((j : ℚ) * ((j : ℚ) + 1)) ^ r := by
    intro N
    induction N with
    | zero => simpa using hF0
    | succ N ih =>
      rw [Finset.sum_range_succ, ← ih]
      have hstep := congrArg (fun Q : ℚ[X] => Q.eval (N : ℚ)) hF_diff
      simp only [eval_sub, eval_comp, eval_add, eval_X, eval_one, eval_pow, eval_mul] at hstep
      push_cast
      linarith
  -- Oddness: G = F + F.comp (-X) has G(X+1) - G(X) = 0 and G(0) = 0
  have hF_odd : F.comp (-X) = -F := by
    set G : ℚ[X] := F + F.comp (-X)
    have hG_diff : G.comp (X + 1) - G = 0 := by
      have h1 : F.comp (X + 1) - F = (X * (X + 1)) ^ r := hF_diff
      have h2 := congrArg (fun Q : ℚ[X] => Q.comp (-X - 1)) hF_diff
      simp only [Polynomial.sub_comp, Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.X_comp,
        Polynomial.one_comp, Polynomial.pow_comp, Polynomial.mul_comp] at h2
      have hsim1 : (-X - 1 + 1 : ℚ[X]) = -X := by ring
      have hsim2 : ((-X - 1) * (-X) : ℚ[X]) = X * (X + 1) := by ring
      rw [hsim1, hsim2] at h2
      have hsim3 : (-(X + 1) : ℚ[X]) = -X - 1 := by ring
      calc G.comp (X + 1) - G
          = (F.comp (X + 1) - F) + (F.comp (-X - 1) - F.comp (-X)) := by
              simp only [G, Polynomial.add_comp, Polynomial.comp_assoc, Polynomial.neg_comp,
                Polynomial.X_comp, hsim3]; ring
        _ = (X * (X + 1)) ^ r - (F.comp (-X) - F.comp (-X - 1)) := by rw [h1]; ring
        _ = (X * (X + 1)) ^ r - (X * (X + 1)) ^ r := by rw [h2]
        _ = 0 := sub_self _
    have hG_nat : ∀ N : ℕ, G.eval (N : ℚ) = 0 := by
      intro N
      induction N with
      | zero =>
        simp only [G, Nat.cast_zero, eval_add, eval_comp, eval_neg, eval_X, neg_zero, hF0, add_zero]
      | succ N ih =>
        have hstep := congrArg (fun Q : ℚ[X] => Q.eval (N : ℚ)) hG_diff
        simp only [eval_sub, eval_comp, eval_add, eval_X, eval_one, eval_zero] at hstep
        push_cast; linarith
    have hG0 : G = 0 := poly_eq_zero_of_eval_nat G hG_nat
    exact eq_neg_of_add_eq_zero_right hG0
  refine ⟨F, hF_eval, ?_, ?_, ?_⟩
  · intro t ht
    have h := congrArg (fun Q : ℚ[X] => Q.coeff t) hF_odd
    rw [coeff_comp_neg_X_q, Polynomial.coeff_neg] at h
    rcases ht with ⟨k, rfl⟩
    have hpow : (-1 : ℚ) ^ (k + k) = 1 := by
      rw [show k + k = 2 * k by ring, pow_mul]; norm_num
    rw [hpow, one_mul] at h
    linarith
  · intro t ht
    simp only [F, finsetSum_coeff, coeff_C_mul]
    refine Finset.sum_eq_zero fun m hm => ?_
    have hm' : m < 2 * r + 1 := mem_range.mp hm
    have hdegm : ((fallPoly (m + 1)).map φ).natDegree ≤ m + 1 :=
      le_trans Polynomial.natDegree_map_le (by rw [fallPoly_natDegree])
    have hc0 : ((fallPoly (m + 1)).map φ).coeff t = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hc0, mul_zero]
  · intro p hp hp5 t
    simp only [F, finsetSum_coeff, coeff_C_mul, Finset.mul_sum]
    refine PVal.sum hp fun m hm => ?_
    have hm' : m < 2 * r + 1 := mem_range.mp hm
    have hre : (p : ℚ) ^ (r - 1) * ((c m : ℚ) / ((m + 1 : ℕ) : ℚ) *
        ((fallPoly (m + 1)).map φ).coeff t) =
        ((p : ℚ) ^ (r - 1) * ((c m : ℚ) * ((fallPoly (m + 1)).coeff t : ℚ))) /
          ((m + 1 : ℕ) : ℚ) := by
      rw [Polynomial.coeff_map]; simp only [φ, Int.coe_castRingHom]; ring
    rw [hre]
    have hvp_le : vp p (m + 1) ≤ r - 1 := by
      have h1 : p ^ vp p (m + 1) ≤ m + 1 := pow_vp_le hp (Nat.succ_ne_zero m)
      have h2 : m + 1 ≤ 2 * r + 1 := by omega
      have h3 : 2 * r + 1 < 5 ^ r := two_mul_add_one_lt_five_pow r hr
      have h4 : 5 ^ r ≤ p ^ r := Nat.pow_le_pow_left hp5 r
      have hlt : p ^ vp p (m + 1) < p ^ r := by omega
      have hlt' : vp p (m + 1) < r := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
      omega
    have hnum : PVal p (0 + (r - 1))
        ((p : ℚ) ^ (r - 1) * ((c m : ℚ) * ((fallPoly (m + 1)).coeff t : ℚ))) := by
      rw [zero_add]
      exact (PVal.of_pow_p hp).mul_zero hp ((PVal.int hp (c m)).mul_zero hp (PVal.int hp _))
    exact hnum.div_nat_vp hp (Nat.succ_ne_zero m) hvp_le

/-- L2.5: For every odd t >= 3, b * c * (b + c) divides (b + c)^t - b^t - c^t in Z. -/
private lemma odd_pow_sub_dvd (b c : ℤ) (t : ℕ) (hodd : Odd t) (ht : 3 ≤ t) :
    b * c * (b + c) ∣ (b + c) ^ t - b ^ t - c ^ t := by
  obtain ⟨s, rfl⟩ := hodd
  obtain ⟨s', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
  clear ht
  induction s' with
  | zero =>
    refine ⟨3, ?_⟩
    ring
  | succ s' ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨(b ^ 2 + b * c + c ^ 2) * q + ((b + c) ^ (2 * s' + 2) + b ^ (2 * s' + 2) + c ^ (2 * s' + 2)), ?_⟩
    have hid : (b + c) ^ (2 * (s' + 1 + 1) + 1) - b ^ (2 * (s' + 1 + 1) + 1) - c ^ (2 * (s' + 1 + 1) + 1) =
        (b ^ 2 + b * c + c ^ 2) * ((b + c) ^ (2 * (s' + 1) + 1) - b ^ (2 * (s' + 1) + 1) - c ^ (2 * (s' + 1) + 1)) +
        b * c * (b + c) * ((b + c) ^ (2 * s' + 2) + b ^ (2 * s' + 2) + c ^ (2 * s' + 2)) := by
      have h1 : 2 * (s' + 1 + 1) + 1 = (2 * s' + 2) + 3 := by omega
      have h2 : 2 * (s' + 1) + 1 = (2 * s' + 2) + 1 := by omega
      rw [h1, h2]
      ring
    rw [hid, hq]
    ring

/-- Auxiliary exact factorial factorization of C((b+c)*p, b*p) / C(b+c, b). -/
private lemma factorial_step_uFactor (p a : ℕ) (hp : p.Prime) :
    (((a * p + p).factorial : ℚ) / ((a * p).factorial : ℚ)) =
      ((a + 1 : ℕ) : ℚ) * (p : ℚ) * ((p - 1).factorial : ℚ) * uFactor p a := by
  have hprod : ∀ m : ℕ, ((a * p + m).factorial : ℚ) / ((a * p).factorial : ℚ) =
      ∏ i ∈ range m, ((a * p + 1 + i : ℕ) : ℚ) := by
    intro m
    induction m with
    | zero =>
      have hne : ((a * p).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (a * p)
      simp [div_self hne]
    | succ m ih =>
      rw [Finset.prod_range_succ, ← ih]
      have hfac : (a * p + (m + 1)).factorial = (a * p + m + 1) * (a * p + m).factorial := by
        rw [show a * p + (m + 1) = (a * p + m) + 1 by omega, Nat.factorial_succ]
      rw [hfac]; push_cast; ring
  rw [hprod p]
  have hp1 : 1 ≤ p := hp.one_le
  have hsplit : ∏ i ∈ range p, ((a * p + 1 + i : ℕ) : ℚ) =
      ((a + 1 : ℕ) : ℚ) * (p : ℚ) * ∏ i ∈ Ico 1 p, ((a : ℚ) * (p : ℚ) + (i : ℚ)) := by
    rw [show p = (p - 1) + 1 by omega, Finset.prod_range_succ]
    have hlast : ((a * ((p - 1) + 1) + 1 + (p - 1) : ℕ) : ℚ) = ((a + 1 : ℕ) : ℚ) * (((p - 1) + 1 : ℕ) : ℚ) := by
      have : a * ((p - 1) + 1) + 1 + (p - 1) = (a + 1) * ((p - 1) + 1) := by ring
      exact_mod_cast this
    rw [hlast, mul_comm]
    congr 1
    refine Finset.prod_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
    · intro i hi; rw [mem_range] at hi; rw [mem_Ico]; omega
    · intro i _ j _ heq; omega
    · intro b hb; rw [mem_Ico] at hb; refine ⟨b - 1, ?_, by omega⟩; rw [mem_range]; omega
    · intro i _; push_cast; ring
  have hfac_prod : ((p - 1).factorial : ℚ) = ∏ i ∈ Ico 1 p, (i : ℚ) := by
    have h : ∀ m : ℕ, (m.factorial : ℚ) = ∏ i ∈ Ico 1 (m + 1), (i : ℚ) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Nat.factorial_succ, Nat.cast_mul, ih]
        have hunion : Ico 1 (m + 1 + 1) = insert (m + 1) (Ico 1 (m + 1)) := by
          ext x; simp only [mem_Ico, mem_insert]; omega
        rw [hunion, Finset.prod_insert (by simp)]
    simpa [Nat.sub_add_cancel hp1] using h (p - 1)
  rw [hsplit, hfac_prod]
  unfold uFactor
  rw [Finset.prod_div_distrib]
  have hne : (∏ i ∈ Ico 1 p, (i : ℚ)) ≠ 0 := by
    rw [← hfac_prod]
    exact_mod_cast Nat.factorial_ne_zero (p - 1)
  field_simp [hne]

private lemma choose_mul_p_ratio (p b c : ℕ) (hp : p.Prime) :
    (Nat.choose ((b + c) * p) (b * p) : ℚ) / (Nat.choose (b + c) b : ℚ) =
      ∏ j ∈ range b, (uFactor p (c + j) / uFactor p j) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.prod_range_succ, ← ih]
    have hch_ne1 : (Nat.choose (b + c) b : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega : b ≤ b + c)).ne'
    have hch_ne2 : (Nat.choose ((b + c) * p) (b * p) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (Nat.mul_le_mul_right p (by omega : b ≤ b + c))).ne'
    have hch_ne3 : (Nat.choose (b + 1 + c) (b + 1) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega : b + 1 ≤ b + 1 + c)).ne'
    have hstep_base : (Nat.choose (b + 1 + c) (b + 1) : ℚ) / (Nat.choose (b + c) b : ℚ) =
        ((b + 1 + c : ℕ) : ℚ) / ((b + 1 : ℕ) : ℚ) := by
      have hnat : (b + 1) * Nat.choose (b + 1 + c) (b + 1) = (b + 1 + c) * Nat.choose (b + c) b := by
        have h := Nat.add_one_mul_choose_eq (b + c) b
        rw [show b + c + 1 = b + 1 + c by omega] at h
        linarith
      have hq : ((b + 1 : ℕ) : ℚ) * (Nat.choose (b + 1 + c) (b + 1) : ℚ) =
          ((b + 1 + c : ℕ) : ℚ) * (Nat.choose (b + c) b : ℚ) := by exact_mod_cast hnat
      have hb1 : ((b + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      rw [div_eq_div_iff hch_ne1 hb1]
      linarith
    have hstep_p : (Nat.choose ((b + 1 + c) * p) ((b + 1) * p) : ℚ) /
        (Nat.choose ((b + c) * p) (b * p) : ℚ) =
        (((b + c + 1 : ℕ) : ℚ) / ((b + 1 : ℕ) : ℚ)) * (uFactor p (c + b) / uFactor p b) := by
      have hf1 : (Nat.choose ((b + 1 + c) * p) ((b + 1) * p) : ℚ) *
          (((b + 1) * p).factorial : ℚ) * ((c * p).factorial : ℚ) =
          (((b + 1 + c) * p).factorial : ℚ) := by
        have h := Nat.choose_mul_factorial_mul_factorial (Nat.mul_le_mul_right p (by omega : b + 1 ≤ b + 1 + c))
        rw [show (b + 1 + c) * p - (b + 1) * p = c * p by
          rw [← Nat.sub_mul]; congr 1; omega] at h
        exact_mod_cast h
      have hf2 : (Nat.choose ((b + c) * p) (b * p) : ℚ) *
          ((b * p).factorial : ℚ) * ((c * p).factorial : ℚ) =
          (((b + c) * p).factorial : ℚ) := by
        have h := Nat.choose_mul_factorial_mul_factorial (Nat.mul_le_mul_right p (by omega : b ≤ b + c))
        rw [show (b + c) * p - b * p = c * p by
          rw [← Nat.sub_mul]; congr 1; omega] at h
        exact_mod_cast h
      have hfac1 := factorial_step_uFactor p (c + b) hp
      have hfac2 := factorial_step_uFactor p b hp
      have heq1 : (c + b) * p + p = (b + 1 + c) * p := by ring
      have heq2 : (c + b) * p = (b + c) * p := by ring
      have heq3 : b * p + p = (b + 1) * p := by ring
      rw [heq1, heq2] at hfac1
      rw [heq3] at hfac2
      have hfa : ((b * p).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have hfb : (((b + 1) * p).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have hfc : ((c * p).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have hfd : (((b + c) * p).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hpm1 : ((p - 1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have hub : uFactor p b ≠ 0 := by
        unfold uFactor
        rw [Finset.prod_ne_zero_iff]
        intro i hi; rw [mem_Ico] at hi
        have hi0 : (0 : ℚ) < (i : ℚ) := by exact_mod_cast hi.1
        exact div_ne_zero (by positivity) (by positivity)
      have hb1 : ((b + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      have hratio : (Nat.choose ((b + 1 + c) * p) ((b + 1) * p) : ℚ) /
          (Nat.choose ((b + c) * p) (b * p) : ℚ) =
          ((((b + 1 + c) * p).factorial : ℚ) / (((b + c) * p).factorial : ℚ)) /
          ((((b + 1) * p).factorial : ℚ) / ((b * p).factorial : ℚ)) := by
        have h1 : (Nat.choose ((b + 1 + c) * p) ((b + 1) * p) : ℚ) =
            (((b + 1 + c) * p).factorial : ℚ) / ((((b + 1) * p).factorial : ℚ) * ((c * p).factorial : ℚ)) := by
          rw [eq_div_iff (mul_ne_zero hfb hfc)]; linarith
        have h2 : (Nat.choose ((b + c) * p) (b * p) : ℚ) =
            (((b + c) * p).factorial : ℚ) / (((b * p).factorial : ℚ) * ((c * p).factorial : ℚ)) := by
          rw [eq_div_iff (mul_ne_zero hfa hfc)]; linarith
        rw [h1, h2]; field_simp [hfa, hfb, hfc, hfd]
      rw [hratio, hfac1, hfac2]
      have hcb : ((c + b + 1 : ℕ) : ℚ) = ((b + c + 1 : ℕ) : ℚ) := by push_cast; ring
      rw [hcb]
      field_simp [hp0, hpm1, hub, hb1]
    have hcb2 : ((b + 1 + c : ℕ) : ℚ) = ((b + c + 1 : ℕ) : ℚ) := by push_cast; ring
    have hb1 : ((b + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hcbne : ((b + c + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hLHS : (Nat.choose ((b + 1 + c) * p) ((b + 1) * p) : ℚ) / (Nat.choose (b + 1 + c) (b + 1) : ℚ) =
        ((Nat.choose ((b + c) * p) (b * p) : ℚ) / (Nat.choose (b + c) b : ℚ)) *
        (((Nat.choose ((b + 1 + c) * p) ((b + 1) * p) : ℚ) / (Nat.choose ((b + c) * p) (b * p) : ℚ)) /
         ((Nat.choose (b + 1 + c) (b + 1) : ℚ) / (Nat.choose (b + c) b : ℚ))) := by
      field_simp [hch_ne1, hch_ne2, hch_ne3]
    rw [hLHS, hstep_p, hstep_base, hcb2]
    field_simp [hb1, hcbne]

/-- L2.6: Kazandzidis ratio supercongruence for prime p >= 5 and b, c >= 1. -/
private lemma kazandzidis_ratio (p b c : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hb : 1 ≤ b) (hc : 1 ≤ c) :
    PVal p (3 + vp p b + vp p c + vp p (b + c))
      ((Nat.choose ((b + c) * p) (b * p) : ℚ) / (Nat.choose (b + c) b : ℚ) - 1) := by
  set E := 3 + vp p b + vp p c + vp p (b + c)
  set R := (Nat.choose ((b + c) * p) (b * p) : ℚ) / (Nat.choose (b + c) b : ℚ)
  have hR_eq : R = ∏ j ∈ range b, (uFactor p (c + j) / uFactor p j) := choose_mul_p_ratio p b c hp
  have hu_pv : ∀ x : ℕ, PVal p 2 (uFactor p x - 1) := fun x => uFactor_sub_one_pval p x hp hp5
  have hdiv_pv : ∀ j : ℕ, PVal p 2 (uFactor p (c + j) / uFactor p j - 1) := by
    intro j
    have h1 := hu_pv (c + j)
    have h2 := hu_pv j
    have h2inv : PVal p 2 ((uFactor p j)⁻¹ - 1) := by
      simpa using h2.inv_one_add hp (by omega)
    have heq : uFactor p (c + j) / uFactor p j - 1 =
        (uFactor p (c + j) - 1) * ((uFactor p j)⁻¹ - 1) +
        (uFactor p (c + j) - 1) + ((uFactor p j)⁻¹ - 1) := by
      rw [div_eq_mul_inv]; ring
    rw [heq]
    exact (((h1.mul hp h2inv).mono (by omega)).add hp h1).add hp h2inv
  have hR_pv2 : PVal p 2 (R - 1) := by
    rw [hR_eq]
    have h := PVal.prod_one_add hp (s := range b) (f := fun j => uFactor p (c + j) / uFactor p j - 1)
      (fun j _ => hdiv_pv j)
    simpa using h
  -- Apply truncLog_inj: it suffices to show PVal p E (truncLog E (R - 1))
  refine truncLog_inj p E hp hR_pv2 ?_
  -- Step 1: truncLog E (R - 1) == sum_{j < b} (truncLog E (u(c+j)-1) - truncLog E (u(j)-1))
  have hlogR : PVal p E (truncLog E (R - 1) -
      ∑ j ∈ range b, (truncLog E (uFactor p (c + j) - 1) - truncLog E (uFactor p j - 1))) := by
    have hprod := truncLog_prod (range b) p E hp
      (fun j => uFactor p (c + j) / uFactor p j - 1) (fun j _ => hdiv_pv j)
    have hprod' : PVal p E (truncLog E (R - 1) -
        ∑ j ∈ range b, truncLog E (uFactor p (c + j) / uFactor p j - 1)) := by
      simpa [hR_eq] using hprod
    have hterm : PVal p E (∑ j ∈ range b,
        (truncLog E (uFactor p (c + j) / uFactor p j - 1) -
          (truncLog E (uFactor p (c + j) - 1) - truncLog E (uFactor p j - 1)))) :=
      PVal.sum hp fun j _ => truncLog_div_sub p E hp (hu_pv (c + j)) (hu_pv j)
    rw [Finset.sum_sub_distrib] at hterm
    have hadd := hprod'.add hp hterm
    have heq : (truncLog E (R - 1) - ∑ j ∈ range b, truncLog E (uFactor p (c + j) / uFactor p j - 1)) +
        (∑ j ∈ range b, truncLog E (uFactor p (c + j) / uFactor p j - 1) -
          ∑ j ∈ range b, (truncLog E (uFactor p (c + j) - 1) - truncLog E (uFactor p j - 1))) =
        truncLog E (R - 1) -
          ∑ j ∈ range b, (truncLog E (uFactor p (c + j) - 1) - truncLog E (uFactor p j - 1)) := by
      ring
    rwa [heq] at hadd
  -- Step 2: Expand each truncLog E (u(x) - 1) into sum over i in Ico 1 (m + 1)
  set m := (p - 1) / 2
  set g : ℕ → ℕ → ℚ := fun x i =>
    (p : ℚ) ^ 2 * ((x : ℚ) * ((x : ℚ) + 1)) / ((i : ℚ) * ((p : ℚ) - (i : ℚ)))
  have hg_pv2 : ∀ x : ℕ, ∀ i ∈ Ico 1 (m + 1), PVal p 2 (g x i) := by
    intro x i hi
    rw [mem_Ico] at hi
    have hnd : ¬ p ∣ i * (p - i) := by
      intro h
      rcases hp.dvd_mul.mp h with h1 | h2
      · have := Nat.le_of_dvd hi.1 h1; omega
      · have := Nat.le_of_dvd (by omega) h2; omega
    have heq : g x i = ((p : ℚ) ^ 2 * ((x * (x + 1) : ℕ) : ℚ)) / (((i * (p - i) : ℕ) : ℚ)) := by
      simp only [g]; push_cast; rw [Nat.cast_sub (by omega)]
    rw [heq]
    exact ((PVal.of_pow_p hp).mul_zero hp (PVal.nat hp _)).div_nat hp hnd
  have hlog_u : ∀ x : ℕ, PVal p E (truncLog E (uFactor p x - 1) -
      ∑ i ∈ Ico 1 (m + 1), truncLog E (g x i)) := by
    intro x
    have h := truncLog_prod (Ico 1 (m + 1)) p E hp (g x) (hg_pv2 x)
    rwa [← uFactor_pair p x hp hp5] at h
  -- Define double sum L(x) = sum_{i=1}^m truncLog E (g x i)
  set L : ℕ → ℚ := fun x => ∑ i ∈ Ico 1 (m + 1), truncLog E (g x i)
  have hlogR2 : PVal p E (truncLog E (R - 1) - ∑ j ∈ range b, (L (c + j) - L j)) := by
    have hdiff : PVal p E (∑ j ∈ range b,
        ((truncLog E (uFactor p (c + j) - 1) - L (c + j)) -
         (truncLog E (uFactor p j - 1) - L j))) :=
      PVal.sum hp fun j _ => (hlog_u (c + j)).sub hp (hlog_u j)
    have hcomb := hlogR.add hp hdiff
    have heq : (truncLog E (R - 1) -
          ∑ j ∈ range b, (truncLog E (uFactor p (c + j) - 1) - truncLog E (uFactor p j - 1))) +
        ∑ j ∈ range b, ((truncLog E (uFactor p (c + j) - 1) - L (c + j)) -
          (truncLog E (uFactor p j - 1) - L j)) =
        truncLog E (R - 1) - ∑ j ∈ range b, (L (c + j) - L j) := by
      have hsub : ∑ j ∈ range b, ((truncLog E (uFactor p (c + j) - 1) - L (c + j)) -
            (truncLog E (uFactor p j - 1) - L j)) -
          ∑ j ∈ range b, (truncLog E (uFactor p (c + j) - 1) - truncLog E (uFactor p j - 1)) =
          -(∑ j ∈ range b, (L (c + j) - L j)) := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => by ring
      linarith
    rwa [heq] at hcomb
  -- Step 3: Show sum_{j < b} (L(c+j) - L(j)) lies in PVal p E
  have hsumL_eq : ∑ j ∈ range b, (L (c + j) - L j) =
      ∑ r ∈ range E,
        ((-1 : ℚ) ^ r / ((r + 1 : ℕ) : ℚ)) * (p : ℚ) ^ (2 * (r + 1)) *
        (∑ i ∈ Ico 1 (m + 1), (1 : ℚ) / (((i : ℚ) * ((p : ℚ) - (i : ℚ))) ^ (r + 1))) *
        ((∑ j ∈ range (b + c), ((j : ℚ) * ((j : ℚ) + 1)) ^ (r + 1)) -
         (∑ j ∈ range b, ((j : ℚ) * ((j : ℚ) + 1)) ^ (r + 1)) -
         (∑ j ∈ range c, ((j : ℚ) * ((j : ℚ) + 1)) ^ (r + 1))) := by
    have hL_exp : ∀ x : ℕ, L x = ∑ r ∈ range E,
        ((-1 : ℚ) ^ r / ((r + 1 : ℕ) : ℚ)) * (p : ℚ) ^ (2 * (r + 1)) *
        (∑ i ∈ Ico 1 (m + 1), (1 : ℚ) / (((i : ℚ) * ((p : ℚ) - (i : ℚ))) ^ (r + 1))) *
        (((x : ℚ) * ((x : ℚ) + 1)) ^ (r + 1)) := by
      intro x
      simp only [L, truncLog]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [g, div_pow, mul_pow, ← pow_mul]
      ring
    simp only [hL_exp, ← Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hinner : ∑ j ∈ range b,
        ((((c + j : ℕ) : ℚ) * (((c + j : ℕ) : ℚ) + 1)) ^ (r + 1) -
          ((j : ℚ) * ((j : ℚ) + 1)) ^ (r + 1)) =
        (∑ j ∈ range (b + c), ((j : ℚ) * ((j : ℚ) + 1)) ^ (r + 1)) -
        (∑ j ∈ range b, ((j : ℚ) * ((j : ℚ) + 1)) ^ (r + 1)) -
        (∑ j ∈ range c, ((j : ℚ) * ((j : ℚ) + 1)) ^ (r + 1)) := by
      rw [Finset.sum_sub_distrib, show b + c = c + b by omega, Finset.sum_range_add]
      ring
    rw [← hinner]
    rw [Finset.mul_sum (s := range b)]
    refine Finset.sum_congr rfl fun j _ => by ring
  have hsumL_pv : PVal p E (∑ j ∈ range b, (L (c + j) - L j)) := by
    rw [hsumL_eq]
    refine PVal.sum hp fun r _ => ?_
    set r1 := r + 1
    obtain ⟨F, hFeval, hFeven, hFdeg, hFden⟩ := power_sum_odd_poly r1 (by omega)
    have hFdiff_eq : (∑ j ∈ range (b + c), ((j : ℚ) * ((j : ℚ) + 1)) ^ r1) -
        (∑ j ∈ range b, ((j : ℚ) * ((j : ℚ) + 1)) ^ r1) -
        (∑ j ∈ range c, ((j : ℚ) * ((j : ℚ) + 1)) ^ r1) =
        F.eval ((b + c : ℕ) : ℚ) - F.eval (b : ℚ) - F.eval (c : ℚ) := by
      rw [hFeval (b + c), hFeval b, hFeval c]
    rw [hFdiff_eq]
    -- Show (p^(r1 - 1)) * (F(b+c) - F(b) - F(c)) has PVal p (vp b + vp c + vp (b+c))
    set V := vp p b + vp p c + vp p (b + c)
    have hFdiff_pv : PVal p V
        ((p : ℚ) ^ (r1 - 1) * (F.eval ((b + c : ℕ) : ℚ) - F.eval (b : ℚ) - F.eval (c : ℚ))) := by
      have hexpF : ∀ x : ℚ, F.eval x = ∑ t ∈ range (2 * r1 + 2), F.coeff t * x ^ t := by
        intro x
        rw [Polynomial.eval_eq_sum_range' (n := 2 * r1 + 2)]
        by_contra hge
        have hlt : 2 * r1 + 1 < F.natDegree := by omega
        have hne : F ≠ 0 := by intro h0; rw [h0, natDegree_zero] at hlt; omega
        exact (Polynomial.leadingCoeff_ne_zero.mpr hne) (by rw [Polynomial.leadingCoeff]; exact hFdeg _ hlt)
      rw [hexpF, hexpF, hexpF, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine PVal.sum hp fun t _ => ?_
      have hre : (p : ℚ) ^ (r1 - 1) *
          (F.coeff t * ((b + c : ℕ) : ℚ) ^ t - F.coeff t * (b : ℚ) ^ t - F.coeff t * (c : ℚ) ^ t) =
          ((p : ℚ) ^ (r1 - 1) * F.coeff t) *
            ((((b : ℤ) + (c : ℤ)) ^ t - (b : ℤ) ^ t - (c : ℤ) ^ t : ℤ) : ℚ) := by
        push_cast; ring
      rw [hre]
      by_cases hev : Even t
      · rw [hFeven t hev, mul_zero, zero_mul]; exact PVal.zero hp
      · have hodd : Odd t := Nat.not_even_iff_odd.mp hev
        by_cases ht1 : t = 1
        · subst ht1
          have : (((b : ℤ) + (c : ℤ)) ^ 1 - (b : ℤ) ^ 1 - (c : ℤ) ^ 1 : ℤ) = 0 := by ring
          rw [this, Int.cast_zero, mul_zero]; exact PVal.zero hp
        · have ht3 : 3 ≤ t := by rcases hodd with ⟨k, rfl⟩; omega
          have hdvd1 : (b : ℤ) * (c : ℤ) * ((b : ℤ) + (c : ℤ)) ∣
              ((b : ℤ) + (c : ℤ)) ^ t - (b : ℤ) ^ t - (c : ℤ) ^ t :=
            odd_pow_sub_dvd (b : ℤ) (c : ℤ) t hodd ht3
          have hdvd_p : (p : ℤ) ^ V ∣ (b : ℤ) * (c : ℤ) * ((b : ℤ) + (c : ℤ)) := by
            have hb' : (p : ℤ) ^ vp p b ∣ (b : ℤ) := by exact_mod_cast vp_dvd hp (by omega)
            have hc' : (p : ℤ) ^ vp p c ∣ (c : ℤ) := by exact_mod_cast vp_dvd hp (by omega)
            have hbc' : (p : ℤ) ^ vp p (b + c) ∣ ((b + c : ℕ) : ℤ) := by
              exact_mod_cast vp_dvd hp (by omega)
            rw [Nat.cast_add] at hbc'
            have h1 := mul_dvd_mul (mul_dvd_mul hb' hc') hbc'
            simpa [V, pow_add] using h1
          exact (hFden p hp hp5 t).zero_mul hp (PVal.of_dvd_int hp (dvd_trans hdvd_p hdvd1))
    -- Now separate r = 0 (r1 = 1) vs r >= 1 (r1 >= 2)
    have hE_eq : E = 3 + V := by simp only [E, V]; ring
    rw [hE_eq]
    by_cases hr0 : r = 0
    · subst hr0
      have hpair := sum_pair_inv_mod_p p hp hp5
      have hre : ((-1 : ℚ) ^ 0 / ((0 + 1 : ℕ) : ℚ)) * (p : ℚ) ^ (2 * (0 + 1)) *
          (∑ i ∈ Ico 1 (m + 1), (1 : ℚ) / (((i : ℚ) * ((p : ℚ) - (i : ℚ))) ^ (0 + 1))) *
          (F.eval ((b + c : ℕ) : ℚ) - F.eval (b : ℚ) - F.eval (c : ℚ)) =
          ((p : ℚ) ^ 2 * (∑ i ∈ Ico 1 (m + 1), (1 : ℚ) / ((i : ℚ) * ((p : ℚ) - (i : ℚ))))) *
          ((p : ℚ) ^ (1 - 1) * (F.eval ((b + c : ℕ) : ℚ) - F.eval (b : ℚ) - F.eval (c : ℚ))) := by
        simp [pow_one]
      rw [hre]
      have hleft : PVal p 3
          ((p : ℚ) ^ 2 * (∑ i ∈ Ico 1 (m + 1), (1 : ℚ) / ((i : ℚ) * ((p : ℚ) - (i : ℚ))))) :=
        (PVal.of_pow_p hp).mul hp hpair
      exact hleft.mul hp hFdiff_pv
    · have hr2 : 2 ≤ r1 := by omega
      have hp_ne : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hexp : 2 * r1 = 3 + (r1 - 2) + (r1 - 1) := by omega
      have hre : ((-1 : ℚ) ^ r / ((r1 : ℕ) : ℚ)) * (p : ℚ) ^ (2 * r1) *
          (∑ i ∈ Ico 1 (m + 1), (1 : ℚ) / (((i : ℚ) * ((p : ℚ) - (i : ℚ))) ^ r1)) *
          (F.eval ((b + c : ℕ) : ℚ) - F.eval (b : ℚ) - F.eval (c : ℚ)) =
          ((p : ℚ) ^ 3 * (((-1 : ℚ) ^ r * (p : ℚ) ^ (r1 - 2)) / ((r1 : ℕ) : ℚ)) *
            (∑ i ∈ Ico 1 (m + 1), (1 : ℚ) / (((i : ℚ) * ((p : ℚ) - (i : ℚ))) ^ r1))) *
          ((p : ℚ) ^ (r1 - 1) * (F.eval ((b + c : ℕ) : ℚ) - F.eval (b : ℚ) - F.eval (c : ℚ))) := by
        rw [hexp, pow_add, pow_add]; ring
      rw [hre]
      have hvp_r1 : vp p r1 ≤ r1 - 2 := by
        have h1 : p ^ vp p r1 ≤ r1 := pow_vp_le hp (by omega)
        have h2 : r1 < 5 ^ (r1 - 1) := lt_five_pow_sub_one r1 hr2
        have h3 : 5 ^ (r1 - 1) ≤ p ^ (r1 - 1) := Nat.pow_le_pow_left hp5 (r1 - 1)
        have hlt : vp p r1 < r1 - 1 := (Nat.pow_lt_pow_iff_right hp.one_lt).mp (by omega)
        omega
      have hfrac : PVal p 0 (((-1 : ℚ) ^ r * (p : ℚ) ^ (r1 - 2)) / ((r1 : ℕ) : ℚ)) := by
        have hnum : PVal p (0 + (r1 - 2)) ((-1 : ℚ) ^ r * (p : ℚ) ^ (r1 - 2)) := by
          rw [zero_add]
          have hs : PVal p 0 ((-1 : ℚ) ^ r) := by simpa using (PVal.int hp (-1)).pow hp r
          exact hs.zero_mul hp (PVal.of_pow_p hp)
        exact hnum.div_nat_vp hp (by omega) hvp_r1
      have hpair_r1 : PVal p 0
          (∑ i ∈ Ico 1 (m + 1), (1 : ℚ) / (((i : ℚ) * ((p : ℚ) - (i : ℚ))) ^ r1)) := by
        refine PVal.sum hp fun i hi => ?_
        rw [mem_Ico] at hi
        have hnd : ¬ p ∣ (i * (p - i)) ^ r1 := by
          intro h
          have h1 := hp.dvd_of_dvd_pow h
          rcases hp.dvd_mul.mp h1 with h2 | h3
          · have := Nat.le_of_dvd hi.1 h2; omega
          · have := Nat.le_of_dvd (by omega) h3; omega
        have heq : (1 : ℚ) / (((i : ℚ) * ((p : ℚ) - (i : ℚ))) ^ r1) =
            (1 : ℚ) / ((((i * (p - i)) ^ r1 : ℕ) : ℚ)) := by
          push_cast; rw [Nat.cast_sub (by omega)]
        rw [heq]
        exact (PVal.nat hp 1).div_nat hp hnd
      have hleft : PVal p 3
          ((p : ℚ) ^ 3 * (((-1 : ℚ) ^ r * (p : ℚ) ^ (r1 - 2)) / ((r1 : ℕ) : ℚ)) *
            (∑ i ∈ Ico 1 (m + 1), (1 : ℚ) / (((i : ℚ) * ((p : ℚ) - (i : ℚ))) ^ r1))) :=
        ((PVal.of_pow_p hp).mul_zero hp hfrac).mul_zero hp hpair_r1
      exact hleft.mul hp hFdiff_pv
  have hfin := hlogR2.add hp hsumL_pv
  simpa using hfin

/-- L2.7: Central binomial supercongruence C(2*n*p^k - 1, n*p^k - 1) == C(2*n*p^(k-1) - 1, n*p^(k-1) - 1) mod p^(3*k). -/
private lemma central_choose_supercong (p n k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hn : 0 < n) (hk : 0 < k) :
    (Nat.choose (2 * (n * p ^ k) - 1) (n * p ^ k - 1) : ℤ) ≡
      (Nat.choose (2 * (n * p ^ (k - 1)) - 1) (n * p ^ (k - 1) - 1) : ℤ) [ZMOD (p : ℤ) ^ (3 * k)] := by
  set M := n * p ^ (k - 1)
  have hMpos : 1 ≤ M := Nat.mul_pos hn (Nat.pow_pos hp.pos)
  have hMp : n * p ^ k = M * p := by
    simp only [M, mul_assoc, ← pow_succ]
    rw [Nat.sub_add_cancel hk]
  rw [hMp]
  have hvpM : k - 1 ≤ vp p M := vp_le_of_dvd hp (by omega) ⟨n, by simp [M, mul_comm]⟩
  have hvp2M : vp p (M + M) = vp p M := by
    rw [show M + M = 2 * M by ring]
    exact vp_mul_two hp hp5 (by omega)
  have hkaz := kazandzidis_ratio p M M hp hp5 hMpos hMpos
  have hEge : 3 * k ≤ 3 + vp p M + vp p M + vp p (M + M) := by rw [hvp2M]; omega
  have hkaz' : PVal p (3 * k)
      ((Nat.choose ((M + M) * p) (M * p) : ℚ) / (Nat.choose (M + M) M : ℚ) - 1) :=
    hkaz.mono hEge
  have hmul := hkaz'.mul_zero hp (PVal.nat hp (Nat.choose (M + M) M))
  have hch_ne : (Nat.choose (M + M) M : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : M ≤ M + M)).ne'
  have hsimp : ((Nat.choose ((M + M) * p) (M * p) : ℚ) / (Nat.choose (M + M) M : ℚ) - 1) *
      (Nat.choose (M + M) M : ℚ) =
      (Nat.choose (2 * (M * p)) (M * p) : ℚ) - (Nat.choose (2 * M) M : ℚ) := by
    rw [show (M + M) * p = 2 * (M * p) by ring, show M + M = 2 * M by ring]
    rw [show M + M = 2 * M by ring] at hch_ne
    field_simp [hch_ne]
  rw [hsimp] at hmul
  have htwo : ∀ m : ℕ, 1 ≤ m → (Nat.choose (2 * m) m : ℚ) = 2 * (Nat.choose (2 * m - 1) (m - 1) : ℚ) := by
    intro m hm
    have hnat : m * Nat.choose (2 * m) m = (2 * m) * Nat.choose (2 * m - 1) (m - 1) := by
      have h := Nat.add_one_mul_choose_eq (2 * m - 1) (m - 1)
      rw [show 2 * m - 1 + 1 = 2 * m by omega, show m - 1 + 1 = m by omega] at h
      linarith
    have hq : (m : ℚ) * (Nat.choose (2 * m) m : ℚ) = (m : ℚ) * (2 * (Nat.choose (2 * m - 1) (m - 1) : ℚ)) := by
      have hq' : (m : ℚ) * (Nat.choose (2 * m) m : ℚ) = (2 * (m : ℚ)) * (Nat.choose (2 * m - 1) (m - 1) : ℚ) := by
        exact_mod_cast hnat
      linarith
    exact mul_left_cancel₀ (by positivity : (m : ℚ) ≠ 0) hq
  rw [htwo (M * p) (Nat.mul_pos hMpos hp.pos), htwo M hMpos] at hmul
  have hnd2 : ¬ p ∣ 2 := by intro h; have := Nat.le_of_dvd (by decide) h; omega
  have hdiv2 := hmul.div_nat hp hnd2
  have hfin : (2 * (Nat.choose (2 * (M * p) - 1) (M * p - 1) : ℚ) -
      2 * (Nat.choose (2 * M - 1) (M - 1) : ℚ)) / ((2 : ℕ) : ℚ) =
      ((Nat.choose (2 * (M * p) - 1) (M * p - 1) : ℤ) : ℚ) -
      ((Nat.choose (2 * M - 1) (M - 1) : ℤ) : ℚ) := by
    push_cast; ring
  rw [hfin] at hdiv2
  exact PVal.modEq_of_sub hp hdiv2

/-- L2.8: Term-by-term congruence for divisible-index terms of H(n*p^k). -/
private lemma H_div_term_supercong (p n k r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hn : 0 < n) (hk : 0 < k) :
    (Nat.choose (n * p ^ k - 1 + p * r) (p * r) : ℤ) ^ 2 ≡
      (Nat.choose (n * p ^ (k - 1) - 1 + r) r : ℤ) ^ 2 [ZMOD (p : ℤ) ^ (3 * k)] := by
  by_cases hr0 : r = 0
  · subst hr0; simp
  · set M := n * p ^ (k - 1)
    have hMpos : 1 ≤ M := Nat.mul_pos hn (Nat.pow_pos hp.pos)
    have hrpos : 1 ≤ r := by omega
    have hMp : n * p ^ k = M * p := by
      simp only [M, mul_assoc, ← pow_succ]
      rw [Nat.sub_add_cancel hk]
    rw [hMp]
    set A := Nat.choose (M * p - 1 + p * r) (p * r)
    set B := Nat.choose (M - 1 + r) r
    have hMrel : ∀ x y : ℕ, 1 ≤ x →
        ((x + y : ℕ) : ℚ) * (Nat.choose (x - 1 + y) y : ℚ) =
        (x : ℚ) * (Nat.choose (x + y) y : ℚ) := by
      intro x y hx
      have hnat : (x + y) * Nat.choose (x - 1 + y) y = x * Nat.choose (x + y) y := by
        have h := Nat.add_one_mul_choose_eq (x - 1 + y) (x - 1)
        have h1 : x - 1 + y + 1 = x + y := by omega
        have h2 : x - 1 + 1 = x := by omega
        have hs1 : Nat.choose (x - 1 + y) (x - 1) = Nat.choose (x - 1 + y) y := by
          have hs := Nat.choose_symm (by omega : y ≤ x - 1 + y)
          rwa [show x - 1 + y - y = x - 1 by omega] at hs
        have hs2 : Nat.choose (x + y) x = Nat.choose (x + y) y := by
          have hs := Nat.choose_symm (by omega : y ≤ x + y)
          rwa [show x + y - y = x by omega] at hs
        rw [h1, h2, hs1, hs2] at h
        linarith
      exact_mod_cast hnat
    have hB_eq : (B : ℚ) = ((M : ℚ) / ((M + r : ℕ) : ℚ)) * (Nat.choose (r + M) r : ℚ) := by
      have h := hMrel M r hMpos
      have hMr : ((M + r : ℕ) : ℚ) ≠ 0 := by positivity
      rw [show r + M = M + r by omega]
      field_simp [hMr]
      simpa [B, mul_comm] using h
    have hA_eq : (A : ℚ) = ((M : ℚ) / ((M + r : ℕ) : ℚ)) * (Nat.choose ((r + M) * p) (r * p) : ℚ) := by
      have h := hMrel (M * p) (p * r) (Nat.mul_pos hMpos hp.pos)
      have hMr : ((M + r : ℕ) : ℚ) ≠ 0 := by positivity
      have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have h1 : M * p + p * r = (r + M) * p := by ring
      have h2 : p * r = r * p := by ring
      rw [h1, h2] at h
      have h3 : (((M + r : ℕ) : ℚ) * (p : ℚ)) * (A : ℚ) =
          ((M : ℚ) * (p : ℚ)) * (Nat.choose ((r + M) * p) (r * p) : ℚ) := by
        simpa [A, h2, Nat.cast_mul, Nat.cast_add, add_comm] using h
      have h4 : ((M + r : ℕ) : ℚ) * (A : ℚ) = (M : ℚ) * (Nat.choose ((r + M) * p) (r * p) : ℚ) := by
        apply mul_right_cancel₀ hp0
        linarith
      field_simp [hMr]
      linarith
    have hch_ne : (Nat.choose (r + M) r : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega : r ≤ r + M)).ne'
    have hAB_sub : (A : ℚ) - (B : ℚ) =
        ((M : ℚ) * (Nat.choose (r + M) r : ℚ) *
          ((Nat.choose ((r + M) * p) (r * p) : ℚ) / (Nat.choose (r + M) r : ℚ) - 1)) /
        ((M + r : ℕ) : ℚ) := by
      rw [hA_eq, hB_eq]
      field_simp [hch_ne]
    have hkaz := kazandzidis_ratio p r M hp hp5 hrpos hMpos
    have hvpM : k - 1 ≤ vp p M := vp_le_of_dvd hp (by omega) ⟨n, by simp [M, mul_comm]⟩
    have hM_pv : PVal p (vp p M) (M : ℚ) := PVal.of_dvd_nat hp (vp_dvd hp (by omega))
    have hAB_pv : PVal p (3 + 2 * vp p M + vp p r) ((A : ℚ) - (B : ℚ)) := by
      rw [hAB_sub]
      have hnum : PVal p ((3 + 2 * vp p M + vp p r) + vp p (M + r))
          ((M : ℚ) * (Nat.choose (r + M) r : ℚ) *
            ((Nat.choose ((r + M) * p) (r * p) : ℚ) / (Nat.choose (r + M) r : ℚ) - 1)) := by
        have h1 := (hM_pv.mul_zero hp (PVal.nat hp (Nat.choose (r + M) r))).mul hp hkaz
        have hexp : vp p M + (3 + vp p r + vp p M + vp p (r + M)) =
            (3 + 2 * vp p M + vp p r) + vp p (M + r) := by
          rw [show r + M = M + r by omega]; ring
        rwa [hexp] at h1
      exact hnum.div_nat_vp hp (by omega) le_rfl
    have hsq_pv : PVal p (3 * k) (((A : ℤ) ^ 2 : ℚ) - ((B : ℤ) ^ 2 : ℚ)) := by
      have hfac : ((A : ℤ) ^ 2 : ℚ) - ((B : ℤ) ^ 2 : ℚ) = ((A : ℚ) - (B : ℚ)) * ((A : ℚ) + (B : ℚ)) := by
        push_cast; ring
      rw [hfac]
      by_cases hcmp : vp p M ≤ vp p r
      · have h1 : PVal p (3 * k) ((A : ℚ) - (B : ℚ)) := hAB_pv.mono (by omega)
        have h2 : PVal p 0 ((A : ℚ) + (B : ℚ)) := (PVal.nat hp A).add hp (PVal.nat hp B)
        exact h1.mul_zero hp h2
      · have hlt : vp p r < vp p M := by omega
        have hvpMr : vp p (M + r) = vp p r := by
          rw [show M + r = r + M by omega]
          exact vp_add_of_lt hp (by omega) (by omega) hlt
        have hB_pv : PVal p (vp p M - vp p r) (B : ℚ) := by
          rw [hB_eq, div_mul_eq_mul_div]
          have hnum : PVal p ((vp p M - vp p r) + vp p (M + r))
              ((M : ℚ) * (Nat.choose (r + M) r : ℚ)) := by
            have h1 := hM_pv.mul_zero hp (PVal.nat hp (Nat.choose (r + M) r))
            have hexp : vp p M = (vp p M - vp p r) + vp p (M + r) := by rw [hvpMr]; omega
            rwa [← hexp]
          exact hnum.div_nat_vp hp (by omega) le_rfl
        have hA_pv : PVal p (vp p M - vp p r) (A : ℚ) := by
          have h1 := (hAB_pv.mono (by omega : vp p M - vp p r ≤ 3 + 2 * vp p M + vp p r)).add hp hB_pv
          simpa using h1
        have hsum_pv : PVal p (vp p M - vp p r) ((A : ℚ) + (B : ℚ)) := hA_pv.add hp hB_pv
        have hmul := hAB_pv.mul hp hsum_pv
        exact hmul.mono (by omega)
    exact PVal.modEq_of_sub hp (by simpa [A, B] using hsq_pv)

-- ============================================================================
-- Block C: Elementary Non-Divisible Supercongruence (Lemma 3)
-- ============================================================================

/-- L3.1: Exact p-adic factorization of C(M' * p + L, L) by induction on L. -/
private lemma choose_p_shift_general (p M' L : ℕ) (hp : p.Prime) :
    (Nat.choose (M' * p + L) L : ℚ) =
      (Nat.choose (M' + L / p) (L / p) : ℚ) *
      ∏ i ∈ (Ico 1 (L + 1)).filter (fun i => ¬ p ∣ i),
        (1 + (M' * p : ℚ) / (i : ℚ)) := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hstep_lhs : (Nat.choose (M' * p + (L + 1)) (L + 1) : ℚ) =
        (Nat.choose (M' * p + L) L : ℚ) * (1 + (M' * p : ℚ) / ((L + 1 : ℕ) : ℚ)) := by
      have hnat : (L + 1) * Nat.choose (M' * p + L + 1) (L + 1) =
          (M' * p + L + 1) * Nat.choose (M' * p + L) L := by
        have h := Nat.add_one_mul_choose_eq (M' * p + L) L
        linarith
      have hq : ((L + 1 : ℕ) : ℚ) * (Nat.choose (M' * p + (L + 1)) (L + 1) : ℚ) =
          ((M' * p + L + 1 : ℕ) : ℚ) * (Nat.choose (M' * p + L) L : ℚ) := by
        rw [show M' * p + (L + 1) = M' * p + L + 1 by omega]
        exact_mod_cast hnat
      have hL1 : ((L + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      field_simp [hL1]
      push_cast at hq ⊢
      linarith
    have hunion : Ico 1 (L + 1 + 1) = insert (L + 1) (Ico 1 (L + 1)) := by
      ext x; simp only [mem_Ico, mem_insert]; omega
    have hnotmem : L + 1 ∉ Ico 1 (L + 1) := by simp
    rw [hstep_lhs, ih, hunion, Finset.filter_insert]
    by_cases hdiv : p ∣ L + 1
    · simp only [hdiv, not_true_eq_false, ↓reduceIte]
      obtain ⟨q1, hq1⟩ := hdiv
      have hq1_pos : 1 ≤ q1 := by
        by_contra h0
        have : q1 = 0 := by omega
        subst this; omega
      obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q1 ≠ 0)
      have hdiv1 : (L + 1) / p = q' + 1 := by
        rw [hq1, Nat.mul_div_cancel_left (q' + 1) hp.pos]
      have hdiv0 : L / p = q' := by
        have hL : L = p * q' + (p - 1) := by
          have hp1 := hp.pos
          have hq1' : L + 1 = p * q' + p := by simpa [Nat.mul_succ] using hq1
          omega
        rw [hL, Nat.mul_add_div hp.pos, Nat.div_eq_of_lt (by have := hp.pos; omega), add_zero]
      have hstep_q : (Nat.choose (M' + (q' + 1)) (q' + 1) : ℚ) =
          (Nat.choose (M' + q') q' : ℚ) * (1 + (M' * p : ℚ) / ((L + 1 : ℕ) : ℚ)) := by
        have hnat : (q' + 1) * Nat.choose (M' + (q' + 1)) (q' + 1) =
            (M' + (q' + 1)) * Nat.choose (M' + q') q' := by
          have h := Nat.add_one_mul_choose_eq (M' + q') q'
          rw [show M' + q' + 1 = M' + (q' + 1) by omega] at h
          linarith
        have hq : ((q' + 1 : ℕ) : ℚ) * (Nat.choose (M' + (q' + 1)) (q' + 1) : ℚ) =
            ((M' + (q' + 1) : ℕ) : ℚ) * (Nat.choose (M' + q') q' : ℚ) := by
          exact_mod_cast hnat
        have hL1 : ((L + 1 : ℕ) : ℚ) = (p : ℚ) * ((q' + 1 : ℕ) : ℚ) := by exact_mod_cast hq1
        have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
        have hq10 : ((q' + 1 : ℕ) : ℚ) ≠ 0 := by positivity
        rw [hL1]
        field_simp [hp0, hq10]
        push_cast at hq ⊢
        linarith
      rw [hdiv1, hdiv0, hstep_q]
      ring
    · simp only [hdiv, not_false_eq_true, ↓reduceIte]
      have hnotmem_f : L + 1 ∉ (Ico 1 (L + 1)).filter (fun i => ¬ p ∣ i) := by
        intro h; exact hnotmem (Finset.mem_filter.mp h).1
      rw [Finset.prod_insert hnotmem_f]
      have hdiv_eq : (L + 1) / p = L / p := by
        have hmod : L % p + 1 < p := by
          have hlt := Nat.mod_lt L hp.pos
          by_contra hge
          have heq : L % p + 1 = p := by omega
          apply hdiv
          have hdm := Nat.div_add_mod L p
          exact ⟨L / p + 1, by rw [mul_add, mul_one]; omega⟩
        have hL : L + 1 = p * (L / p) + (L % p + 1) := by
          have hdm := Nat.div_add_mod L p
          omega
        conv_lhs => rw [hL]
        rw [Nat.mul_add_div hp.pos, Nat.div_eq_of_lt hmod, add_zero]
      rw [hdiv_eq]
      ring

/-- L3.1(b): Congruence C(M'*p + (a*p + b), a*p + b) == C(M' + a, a) mod p^m when p^m | M'*p. -/
private lemma choose_shift_mod_pow (p M' m a b : ℕ) (hp : p.Prime)
    (hM : p ^ m ∣ M' * p) (hb : b < p) :
    (Nat.choose (M' * p + (a * p + b)) (a * p + b) : ℤ) ≡
      (Nat.choose (M' + a) a : ℤ) [ZMOD (p : ℤ) ^ m] := by
  have hfac := choose_p_shift_general p M' (a * p + b) hp
  have hdiv : (a * p + b) / p = a := by
    rw [mul_comm a p, Nat.mul_add_div hp.pos, Nat.div_eq_of_lt hb, add_zero]
  rw [hdiv] at hfac
  have hprod : PVal p m ((∏ i ∈ (Ico 1 (a * p + b + 1)).filter (fun i => ¬ p ∣ i),
      (1 + (M' * p : ℚ) / (i : ℚ))) - 1) := by
    refine PVal.prod_one_add hp fun i hi => ?_
    have hnd : ¬ p ∣ i := (Finset.mem_filter.mp hi).2
    have hMp : PVal p m ((M' * p : ℚ)) := by
      simpa [Nat.cast_mul] using PVal.of_dvd_nat hp hM
    exact hMp.div_nat hp hnd
  have hdiff : PVal p m
      (((Nat.choose (M' * p + (a * p + b)) (a * p + b) : ℤ) : ℚ) -
       ((Nat.choose (M' + a) a : ℤ) : ℚ)) := by
    have heq : ((Nat.choose (M' * p + (a * p + b)) (a * p + b) : ℤ) : ℚ) -
        ((Nat.choose (M' + a) a : ℤ) : ℚ) =
        (Nat.choose (M' + a) a : ℚ) *
          ((∏ i ∈ (Ico 1 (a * p + b + 1)).filter (fun i => ¬ p ∣ i),
            (1 + (M' * p : ℚ) / (i : ℚ))) - 1) := by
      push_cast; rw [hfac]; ring
    rw [heq]
    exact (PVal.nat hp _).zero_mul hp hprod
  exact PVal.modEq_of_sub hp hdiff

/-- L3.1(a): Exact square approximation for C(M*p - 1 + (q*p + s), q*p + s)^2 mod p^(3*k). -/
private lemma choose_pred_sq_pval (p M k q s : ℕ) (hp : p.Prime) (hMpos : 1 ≤ M)
    (hMk : p ^ k ∣ M * p) (hs1 : 1 ≤ s) (hsp : s < p) :
    PVal p (3 * k)
      ((Nat.choose (M * p - 1 + (q * p + s)) (q * p + s) : ℚ) ^ 2 -
       (M * p : ℚ) ^ 2 * (Nat.choose (M + q) q : ℚ) ^ 2 * (((q * p + s : ℕ) : ℚ) ^ 2)⁻¹) := by
  set N := M * p
  set j := q * p + s
  have hNpos : 1 ≤ N := Nat.mul_pos hMpos hp.pos
  have hjpos : 1 ≤ j := by omega
  have hndj : ¬ p ∣ j := by
    intro h
    have hs : p ∣ s := (Nat.dvd_add_right (dvd_mul_left p q)).mp h
    have := Nat.le_of_dvd hs1 hs
    omega
  have hrel : ((N + j : ℕ) : ℚ) * (Nat.choose (N - 1 + j) j : ℚ) =
      (N : ℚ) * (Nat.choose (N + j) j : ℚ) := by
    have hnat : (N + j) * Nat.choose (N - 1 + j) j = N * Nat.choose (N + j) j := by
      have h := Nat.add_one_mul_choose_eq (N - 1 + j) (N - 1)
      have h1 : N - 1 + j + 1 = N + j := by omega
      have h2 : N - 1 + 1 = N := by omega
      have hs1' : Nat.choose (N - 1 + j) (N - 1) = Nat.choose (N - 1 + j) j := by
        have hs := Nat.choose_symm (by omega : j ≤ N - 1 + j)
        rwa [show N - 1 + j - j = N - 1 by omega] at hs
      have hs2' : Nat.choose (N + j) N = Nat.choose (N + j) j := by
        have hs := Nat.choose_symm (by omega : j ≤ N + j)
        rwa [show N + j - j = N by omega] at hs
      rw [h1, h2, hs1', hs2'] at h
      linarith
    exact_mod_cast hnat
  have hshift := choose_p_shift_general p M j hp
  have hdiv : j / p = q := by
    simp only [j, mul_comm q p, Nat.mul_add_div hp.pos, Nat.div_eq_of_lt hsp, add_zero]
  rw [hdiv] at hshift
  have hunion : Ico 1 (j + 1) = insert j (Ico 1 j) := by
    ext x; simp only [mem_Ico, mem_insert]; omega
  have hnotmem : j ∉ (Ico 1 j).filter (fun i => ¬ p ∣ i) := by
    intro h; have := (mem_Ico.mp (Finset.mem_filter.mp h).1).2; omega
  set P : ℚ := ∏ i ∈ (Ico 1 j).filter (fun i => ¬ p ∣ i), (1 + (N : ℚ) / (i : ℚ))
  have hshift' : (Nat.choose (N + j) j : ℚ) =
      (Nat.choose (M + q) q : ℚ) * (1 + (N : ℚ) / (j : ℚ)) * P := by
    rw [hshift, hunion, Finset.filter_insert]
    simp only [hndj, not_false_eq_true, ↓reduceIte, Finset.prod_insert hnotmem]
    simp only [N, P, Nat.cast_mul]; ring
  have hpred : (Nat.choose (N - 1 + j) j : ℚ) =
      ((N : ℚ) / (j : ℚ)) * (Nat.choose (M + q) q : ℚ) * P := by
    have hNj : ((N + j : ℕ) : ℚ) ≠ 0 := by positivity
    have hj0 : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    apply mul_left_cancel₀ hNj
    rw [hrel, hshift']
    push_cast
    field_simp [hj0]
    ring
  have hP_sub : PVal p k (P - 1) := by
    refine PVal.prod_one_add hp fun i hi => ?_
    have hnd : ¬ p ∣ i := (Finset.mem_filter.mp hi).2
    have hNk : PVal p k (N : ℚ) := PVal.of_dvd_nat hp hMk
    exact hNk.div_nat hp hnd
  have hP2_sub : PVal p k (P ^ 2 - 1) := by
    have heq : P ^ 2 - 1 = (P - 1) * ((P - 1) + 2) := by ring
    rw [heq]
    have hP0 : PVal p 0 ((P - 1) + 2) := (hP_sub.mono (by omega)).add hp (PVal.nat hp 2)
    exact hP_sub.mul_zero hp hP0
  have hbase : PVal p (2 * k) ((N : ℚ) ^ 2 * (Nat.choose (M + q) q : ℚ) ^ 2 * ((j : ℚ) ^ 2)⁻¹) := by
    have hN2 : PVal p (2 * k) ((N : ℚ) ^ 2) := by
      simpa [mul_comm] using (PVal.of_dvd_nat hp hMk).pow hp 2
    have hch2 : PVal p 0 ((Nat.choose (M + q) q : ℚ) ^ 2) := by
      simpa using (PVal.nat hp (Nat.choose (M + q) q)).pow hp 2
    have hj2_nd : ¬ p ∣ j ^ 2 := fun h => hndj (hp.dvd_of_dvd_pow h)
    have hj2_inv : PVal p 0 (((j : ℚ) ^ 2)⁻¹) := by
      simpa [Nat.cast_pow] using PVal.inv_nat hj2_nd
    exact (hN2.mul_zero hp hch2).mul_zero hp hj2_inv
  have hcomb : (Nat.choose (N - 1 + j) j : ℚ) ^ 2 -
      (N : ℚ) ^ 2 * (Nat.choose (M + q) q : ℚ) ^ 2 * ((j : ℚ) ^ 2)⁻¹ =
      ((N : ℚ) ^ 2 * (Nat.choose (M + q) q : ℚ) ^ 2 * ((j : ℚ) ^ 2)⁻¹) * (P ^ 2 - 1) := by
    rw [hpred]; ring
  have hmul := hbase.mul hp hP2_sub
  have hexp : 2 * k + k = 3 * k := by omega
  rw [hexp, ← hcomb] at hmul
  simpa [N, j, Nat.cast_mul] using hmul

/-- Helper: partition sum over range (M * p) into double sum over a < M, b < p. -/
private lemma sum_range_mul_eq {α : Type*} [AddCommMonoid α] (M p : ℕ) (f : ℕ → α) :
    ∑ q ∈ range (M * p), f q = ∑ a ∈ range M, ∑ b ∈ range p, f (a * p + b) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show (M + 1) * p = M * p + p by ring, Finset.sum_range_add, Finset.sum_range_succ, ih]

/-- Helper: for odd p, p divides sum_{b < p} b in Z. -/
private lemma p_dvd_sum_range_id (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (p : ℤ) ∣ ∑ b ∈ range p, (b : ℤ) := by
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two (by omega)
  have h2sum : 2 * ∑ b ∈ range p, (b : ℤ) = (p : ℤ) * ((p : ℤ) - 1) := by
    clear hm hp hp5
    induction p with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      push_cast; ring
  refine ⟨(m : ℤ), ?_⟩
  have hm_z : (p : ℤ) - 1 = 2 * (m : ℤ) := by omega
  rw [hm_z] at h2sum
  linarith

/-- L3.2: Induction on m for power-weighted binomial-square sums. -/
private lemma moment_sum_dvd (p n m : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ((p : ℤ) ^ m ∣ ∑ q ∈ range (n * p ^ m), (Nat.choose (n * p ^ m + q) q : ℤ) ^ 2) ∧
    (∀ d : ℕ, 1 ≤ d →
      (p : ℤ) ^ (m + 1) ∣ (p : ℤ) ^ d * ∑ q ∈ range (n * p ^ m),
        (Nat.choose (n * p ^ m + q) q : ℤ) ^ 2 * (q : ℤ) ^ d) := by
  induction m with
  | zero =>
    constructor
    · simp
    · intro d hd
      rw [zero_add, pow_one]
      exact dvd_mul_of_dvd_left (dvd_pow_self (p : ℤ) (by omega)) _
  | succ m ih =>
    set M' := n * p ^ m
    set M := n * p ^ (m + 1)
    have hMM' : M = M' * p := by simp only [M, M', pow_succ, mul_assoc]
    have hMdvd : p ^ (m + 1) ∣ M' * p := ⟨n, by rw [← hMM']; simp [M, mul_comm]⟩
    have hch_cong : ∀ a b : ℕ, b < p →
        (Nat.choose (M + (a * p + b)) (a * p + b) : ℤ) ^ 2 ≡
          (Nat.choose (M' + a) a : ℤ) ^ 2 [ZMOD (p : ℤ) ^ (m + 1)] := by
      intro a b hb
      rw [hMM']
      exact (choose_shift_mod_pow p M' (m + 1) a b hp hMdvd hb).pow 2
    constructor
    · -- Clause 1: p^(m+1) | sum_{q < M} C(M+q, q)^2
      have hcong : ∑ q ∈ range M, (Nat.choose (M + q) q : ℤ) ^ 2 ≡
          (p : ℤ) * ∑ a ∈ range M', (Nat.choose (M' + a) a : ℤ) ^ 2 [ZMOD (p : ℤ) ^ (m + 1)] := by
        rw [hMM', sum_range_mul_eq M' p]
        have hstep1 : ∑ a ∈ range M', ∑ b ∈ range p,
              (Nat.choose (M' * p + (a * p + b)) (a * p + b) : ℤ) ^ 2 ≡
            ∑ a ∈ range M', ∑ b ∈ range p,
              (Nat.choose (M' + a) a : ℤ) ^ 2 [ZMOD (p : ℤ) ^ (m + 1)] := by
          refine Int.ModEq.sum fun a _ => Int.ModEq.sum fun b hb => ?_
          rw [← hMM']
          exact hch_cong a b (mem_range.mp hb)
        have hstep2 : ∑ a ∈ range M', ∑ _b ∈ range p, (Nat.choose (M' + a) a : ℤ) ^ 2 =
            (p : ℤ) * ∑ a ∈ range M', (Nat.choose (M' + a) a : ℤ) ^ 2 := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.mul_sum]
        rwa [hstep2] at hstep1
      have hdvd_rhs : (p : ℤ) ^ (m + 1) ∣
          (p : ℤ) * ∑ a ∈ range M', (Nat.choose (M' + a) a : ℤ) ^ 2 := by
        rw [pow_succ']
        exact mul_dvd_mul_left (p : ℤ) ih.1
      have hdiff : (p : ℤ) ^ (m + 1) ∣
          ((p : ℤ) * ∑ a ∈ range M', (Nat.choose (M' + a) a : ℤ) ^ 2) -
          (∑ q ∈ range M, (Nat.choose (M + q) q : ℤ) ^ 2) :=
        Int.modEq_iff_dvd.mp hcong
      have : ∑ q ∈ range M, (Nat.choose (M + q) q : ℤ) ^ 2 =
          ((p : ℤ) * ∑ a ∈ range M', (Nat.choose (M' + a) a : ℤ) ^ 2) -
          (((p : ℤ) * ∑ a ∈ range M', (Nat.choose (M' + a) a : ℤ) ^ 2) -
            (∑ q ∈ range M, (Nat.choose (M + q) q : ℤ) ^ 2)) := by ring
      rw [this]
      exact dvd_sub hdvd_rhs hdiff
    · -- Clause 2: for d >= 1, p^(m+2) | p^d * sum_{q < M} C(M+q, q)^2 * q^d
      intro d hd
      have hcong : (p : ℤ) ^ d * ∑ q ∈ range M, (Nat.choose (M + q) q : ℤ) ^ 2 * (q : ℤ) ^ d ≡
          (p : ℤ) ^ d * ∑ a ∈ range M', ∑ b ∈ range p,
            (Nat.choose (M' + a) a : ℤ) ^ 2 * ((a * p + b : ℕ) : ℤ) ^ d
          [ZMOD (p : ℤ) ^ (m + 2)] := by
        rw [hMM', sum_range_mul_eq M' p]
        have hinner : ∑ a ∈ range M', ∑ b ∈ range p,
              (Nat.choose (M' * p + (a * p + b)) (a * p + b) : ℤ) ^ 2 * ((a * p + b : ℕ) : ℤ) ^ d ≡
            ∑ a ∈ range M', ∑ b ∈ range p,
              (Nat.choose (M' + a) a : ℤ) ^ 2 * ((a * p + b : ℕ) : ℤ) ^ d
            [ZMOD (p : ℤ) ^ (m + 1)] := by
          refine Int.ModEq.sum fun a _ => Int.ModEq.sum fun b hb => ?_
          rw [← hMM']
          exact (hch_cong a b (mem_range.mp hb)).mul_right _
        obtain ⟨c, hc⟩ := Int.modEq_iff_dvd.mp hinner
        rw [Int.modEq_iff_dvd]
        refine ⟨(p : ℤ) ^ (d - 1) * c, ?_⟩
        have hd1 : d = (d - 1) + 1 := by omega
        calc (p : ℤ) ^ d * ∑ a ∈ range M', ∑ b ∈ range p,
                (Nat.choose (M' + a) a : ℤ) ^ 2 * ((a * p + b : ℕ) : ℤ) ^ d -
              (p : ℤ) ^ d * ∑ a ∈ range M', ∑ b ∈ range p,
                (Nat.choose (M' * p + (a * p + b)) (a * p + b) : ℤ) ^ 2 * ((a * p + b : ℕ) : ℤ) ^ d
            = (p : ℤ) ^ d * ((∑ a ∈ range M', ∑ b ∈ range p,
                  (Nat.choose (M' + a) a : ℤ) ^ 2 * ((a * p + b : ℕ) : ℤ) ^ d) -
                (∑ a ∈ range M', ∑ b ∈ range p,
                  (Nat.choose (M' * p + (a * p + b)) (a * p + b) : ℤ) ^ 2 * ((a * p + b : ℕ) : ℤ) ^ d)) := by
                ring
          _ = (p : ℤ) ^ d * ((p : ℤ) ^ (m + 1) * c) := by rw [hc]
          _ = (p : ℤ) ^ (m + 2) * ((p : ℤ) ^ (d - 1) * c) := by
                conv_lhs => rw [hd1]
                rw [pow_succ, show m + 2 = (m + 1) + 1 by omega, pow_succ]
                ring
      have hbin : (p : ℤ) ^ d * ∑ a ∈ range M', ∑ b ∈ range p,
            (Nat.choose (M' + a) a : ℤ) ^ 2 * ((a * p + b : ℕ) : ℤ) ^ d =
          ∑ j ∈ range (d + 1),
            (Nat.choose d j : ℤ) * (p : ℤ) ^ d *
            (∑ b ∈ range p, (b : ℤ) ^ (d - j)) *
            ((p : ℤ) ^ j * ∑ a ∈ range M', (Nat.choose (M' + a) a : ℤ) ^ 2 * (a : ℤ) ^ j) := by
        have hexp : ∀ a b : ℕ,
            (Nat.choose (M' + a) a : ℤ) ^ 2 * ((a * p + b : ℕ) : ℤ) ^ d =
            ∑ j ∈ range (d + 1),
              (Nat.choose d j : ℤ) * (b : ℤ) ^ (d - j) *
              ((p : ℤ) ^ j * ((Nat.choose (M' + a) a : ℤ) ^ 2 * (a : ℤ) ^ j)) := by
          intro a b
          push_cast
          rw [add_pow, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [mul_pow]; ring
        simp_rw [hexp]
        have hswap : ∀ a ∈ range M',
            (∑ b ∈ range p, ∑ j ∈ range (d + 1),
              (Nat.choose d j : ℤ) * (b : ℤ) ^ (d - j) *
              ((p : ℤ) ^ j * ((Nat.choose (M' + a) a : ℤ) ^ 2 * (a : ℤ) ^ j))) =
            ∑ j ∈ range (d + 1), ∑ b ∈ range p,
              (Nat.choose d j : ℤ) * (b : ℤ) ^ (d - j) *
              ((p : ℤ) ^ j * ((Nat.choose (M' + a) a : ℤ) ^ 2 * (a : ℤ) ^ j)) :=
          fun _ _ => Finset.sum_comm
        rw [Finset.sum_congr rfl hswap]
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum (s := range M')]
        symm
        calc (Nat.choose d j : ℤ) * (p : ℤ) ^ d * (∑ b ∈ range p, (b : ℤ) ^ (d - j)) *
              ((p : ℤ) ^ j * ∑ a ∈ range M', (Nat.choose (M' + a) a : ℤ) ^ 2 * (a : ℤ) ^ j)
            = ∑ a ∈ range M',
                (Nat.choose d j : ℤ) * (p : ℤ) ^ d * (∑ b ∈ range p, (b : ℤ) ^ (d - j)) *
                  ((p : ℤ) ^ j * ((Nat.choose (M' + a) a : ℤ) ^ 2 * (a : ℤ) ^ j)) := by
                rw [Finset.mul_sum (s := range M'), Finset.mul_sum (s := range M')]
          _ = ∑ a ∈ range M', (p : ℤ) ^ d * ∑ b ∈ range p,
                (Nat.choose d j : ℤ) * (b : ℤ) ^ (d - j) *
                  ((p : ℤ) ^ j * ((Nat.choose (M' + a) a : ℤ) ^ 2 * (a : ℤ) ^ j)) := by
                refine Finset.sum_congr rfl fun a _ => ?_
                rw [Finset.mul_sum (s := range p), Finset.sum_mul, Finset.mul_sum (s := range p)]
                refine Finset.sum_congr rfl fun b _ => by ring
      have hdvd_rhs : (p : ℤ) ^ (m + 2) ∣
          (p : ℤ) ^ d * ∑ a ∈ range M', ∑ b ∈ range p,
            (Nat.choose (M' + a) a : ℤ) ^ 2 * ((a * p + b : ℕ) : ℤ) ^ d := by
        rw [hbin]
        refine Finset.dvd_sum fun j _ => ?_
        by_cases hj : 1 ≤ j
        · have h1 : (p : ℤ) ^ 1 ∣ (p : ℤ) ^ d := pow_dvd_pow (p : ℤ) hd
          have h2 : (p : ℤ) ^ (m + 1) ∣
              (p : ℤ) ^ j * ∑ a ∈ range M', (Nat.choose (M' + a) a : ℤ) ^ 2 * (a : ℤ) ^ j :=
            ih.2 j hj
          have h3 : (p : ℤ) ^ (m + 2) ∣
              (p : ℤ) ^ d * ((p : ℤ) ^ j * ∑ a ∈ range M', (Nat.choose (M' + a) a : ℤ) ^ 2 * (a : ℤ) ^ j) := by
            rw [show m + 2 = 1 + (m + 1) by omega, pow_add]
            exact mul_dvd_mul h1 h2
          have hre : (Nat.choose d j : ℤ) * (p : ℤ) ^ d * (∑ b ∈ range p, (b : ℤ) ^ (d - j)) *
              ((p : ℤ) ^ j * ∑ a ∈ range M', (Nat.choose (M' + a) a : ℤ) ^ 2 * (a : ℤ) ^ j) =
              ((Nat.choose d j : ℤ) * (∑ b ∈ range p, (b : ℤ) ^ (d - j))) *
              ((p : ℤ) ^ d * ((p : ℤ) ^ j * ∑ a ∈ range M', (Nat.choose (M' + a) a : ℤ) ^ 2 * (a : ℤ) ^ j)) := by
            ring
          rw [hre]
          exact dvd_mul_of_dvd_right h3 _
        · have hj0 : j = 0 := by omega
          subst hj0
          simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero, pow_zero, mul_one]
          by_cases hd2 : 2 ≤ d
          · have h1 : (p : ℤ) ^ 2 ∣ (p : ℤ) ^ d := pow_dvd_pow (p : ℤ) hd2
            have h2 : (p : ℤ) ^ m ∣ ∑ a ∈ range M', (Nat.choose (M' + a) a : ℤ) ^ 2 := ih.1
            have h3 : (p : ℤ) ^ (m + 2) ∣
                (p : ℤ) ^ d * ∑ a ∈ range M', (Nat.choose (M' + a) a : ℤ) ^ 2 := by
              rw [show m + 2 = 2 + m by omega, pow_add]
              exact mul_dvd_mul h1 h2
            have hre : (p : ℤ) ^ d * (∑ b ∈ range p, (b : ℤ) ^ d) *
                ∑ a ∈ range M', (Nat.choose (M' + a) a : ℤ) ^ 2 =
                (∑ b ∈ range p, (b : ℤ) ^ d) *
                ((p : ℤ) ^ d * ∑ a ∈ range M', (Nat.choose (M' + a) a : ℤ) ^ 2) := by ring
            rw [hre]
            exact dvd_mul_of_dvd_right h3 _
          · have hd1 : d = 1 := by omega
            subst hd1
            simp only [pow_one]
            have hb : (p : ℤ) ∣ ∑ b ∈ range p, (b : ℤ) := p_dvd_sum_range_id p hp hp5
            have h1 : (p : ℤ) ^ 2 ∣ (p : ℤ) * ∑ b ∈ range p, (b : ℤ) := by
              rw [pow_two]; exact mul_dvd_mul_left (p : ℤ) hb
            rw [show m + 2 = 2 + m by omega, pow_add]
            exact mul_dvd_mul h1 ih.1
      have hdiff := Int.modEq_iff_dvd.mp hcong
      have : (p : ℤ) ^ d * ∑ q ∈ range M, (Nat.choose (M + q) q : ℤ) ^ 2 * (q : ℤ) ^ d =
          ((p : ℤ) ^ d * ∑ a ∈ range M', ∑ b ∈ range p,
            (Nat.choose (M' + a) a : ℤ) ^ 2 * ((a * p + b : ℕ) : ℤ) ^ d) -
          (((p : ℤ) ^ d * ∑ a ∈ range M', ∑ b ∈ range p,
            (Nat.choose (M' + a) a : ℤ) ^ 2 * ((a * p + b : ℕ) : ℤ) ^ d) -
            ((p : ℤ) ^ d * ∑ q ∈ range M, (Nat.choose (M + q) q : ℤ) ^ 2 * (q : ℤ) ^ d)) := by ring
      rw [this]
      exact dvd_sub hdvd_rhs hdiff

/-- L3.3: Truncated binomial expansion of (q*p + s)^(-2) modulo p^k. -/
private lemma inv_sq_geom_series (p k q s : ℕ) (hp : p.Prime)
    (hs1 : 1 ≤ s) (hsp : s < p) :
    PVal p k ((((q * p + s : ℕ) : ℚ) ^ 2)⁻¹ -
      ∑ d ∈ range k, (-1 : ℚ) ^ d * ((d + 1 : ℕ) : ℚ) * (p : ℚ) ^ d * (q : ℚ) ^ d / (s : ℚ) ^ (d + 2)) := by
  set u : ℚ := (q : ℚ) * (p : ℚ) / (s : ℚ)
  have hgeom : ∀ m : ℕ,
      (1 + u) ^ 2 * ∑ d ∈ range m, (-1 : ℚ) ^ d * ((d + 1 : ℕ) : ℚ) * u ^ d =
      1 - (-1 : ℚ) ^ m * (((m + 1 : ℕ) : ℚ) * u ^ m + (m : ℚ) * u ^ (m + 1)) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      push_cast; ring
  have hs0 : (s : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hqps0 : ((q * p + s : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h1u : (s : ℚ) * (1 + u) = ((q * p + s : ℕ) : ℚ) := by
    simp only [u]; push_cast; field_simp [hs0]; ring
  have hsum_eq : ∑ d ∈ range k,
        (-1 : ℚ) ^ d * ((d + 1 : ℕ) : ℚ) * (p : ℚ) ^ d * (q : ℚ) ^ d / (s : ℚ) ^ (d + 2) =
      ((s : ℚ) ^ 2)⁻¹ * ∑ d ∈ range k, (-1 : ℚ) ^ d * ((d + 1 : ℕ) : ℚ) * u ^ d := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [u, div_pow, mul_pow, pow_add]
    field_simp [hs0]
  have hdiff_eq : (((q * p + s : ℕ) : ℚ) ^ 2)⁻¹ -
      ∑ d ∈ range k, (-1 : ℚ) ^ d * ((d + 1 : ℕ) : ℚ) * (p : ℚ) ^ d * (q : ℚ) ^ d / (s : ℚ) ^ (d + 2) =
      ((-1 : ℚ) ^ k * (((k + 1 : ℕ) : ℚ) * u ^ k + (k : ℚ) * u ^ (k + 1))) /
        (((q * p + s) ^ 2 : ℕ) : ℚ) := by
    rw [hsum_eq]
    have hsq : ((q * p + s : ℕ) : ℚ) ^ 2 = (s : ℚ) ^ 2 * (1 + u) ^ 2 := by
      rw [← h1u, mul_pow]
    have hqps2 : ((q * p + s : ℕ) : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hqps0
    have hs2 : (s : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hs0
    have hg := hgeom k
    rw [Nat.cast_pow, eq_div_iff hqps2, sub_mul, inv_mul_cancel₀ hqps2]
    calc 1 - ((s : ℚ) ^ 2)⁻¹ * (∑ d ∈ range k, (-1 : ℚ) ^ d * ((d + 1 : ℕ) : ℚ) * u ^ d) *
            ((q * p + s : ℕ) : ℚ) ^ 2
        = 1 - ((s : ℚ) ^ 2)⁻¹ * (∑ d ∈ range k, (-1 : ℚ) ^ d * ((d + 1 : ℕ) : ℚ) * u ^ d) *
            ((s : ℚ) ^ 2 * (1 + u) ^ 2) := by rw [hsq]
      _ = 1 - (1 + u) ^ 2 * ∑ d ∈ range k, (-1 : ℚ) ^ d * ((d + 1 : ℕ) : ℚ) * u ^ d := by
            field_simp [hs2]
      _ = (-1 : ℚ) ^ k * (((k + 1 : ℕ) : ℚ) * u ^ k + (k : ℚ) * u ^ (k + 1)) := by
            rw [hg]; ring
  rw [hdiff_eq]
  have hnds : ¬ p ∣ s := fun h => by have := Nat.le_of_dvd hs1 h; omega
  have hu_pv : PVal p 1 u := by
    have hnum : PVal p 1 ((q : ℚ) * (p : ℚ)) := by
      rw [mul_comm]
      simpa using (PVal.of_pow_p (e := 1) hp).mul_zero hp (PVal.nat hp q)
    exact hnum.div_nat hp hnds
  have huk : PVal p k (u ^ k) := by simpa using hu_pv.pow hp k
  have huk1 : PVal p k (u ^ (k + 1)) := (hu_pv.pow hp (k + 1)).mono (by omega)
  have hnum_pv : PVal p k ((-1 : ℚ) ^ k * (((k + 1 : ℕ) : ℚ) * u ^ k + (k : ℚ) * u ^ (k + 1))) := by
    have hs : PVal p 0 ((-1 : ℚ) ^ k) := by simpa using (PVal.int hp (-1)).pow hp k
    have ht1 : PVal p k (((k + 1 : ℕ) : ℚ) * u ^ k) := (PVal.nat hp _).zero_mul hp huk
    have ht2 : PVal p k ((k : ℚ) * u ^ (k + 1)) := (PVal.nat hp _).zero_mul hp huk1
    exact hs.zero_mul hp (ht1.add hp ht2)
  have hndqps2 : ¬ p ∣ (q * p + s) ^ 2 := by
    intro h
    have h1 := hp.dvd_of_dvd_pow h
    exact hnds ((Nat.dvd_add_right (dvd_mul_left p q)).mp h1)
  exact hnum_pv.div_nat hp hndqps2

/-- Helper: partition filter (not p | j) on range (M * p) into q < M, 1 <= s < p. -/
private lemma sum_filter_not_dvd_range_mul {α : Type*} [AddCommMonoid α] (M p : ℕ)
    (hp : p.Prime) (f : ℕ → α) :
    ∑ j ∈ (range (M * p)).filter (fun j => ¬ p ∣ j), f j =
      ∑ q ∈ range M, ∑ s ∈ Ico 1 p, f (q * p + s) := by
  rw [Finset.sum_filter, sum_range_mul_eq M p]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hp1 : 1 ≤ p := hp.one_le
  have hsplit : range p = insert 0 (Ico 1 p) := by
    ext x; simp only [mem_range, mem_insert, mem_Ico]; omega
  rw [hsplit, Finset.sum_insert (by simp)]
  have h0 : p ∣ q * p + 0 := by simp
  simp only [h0, not_true_eq_false, ↓reduceIte, zero_add]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [mem_Ico] at hs
  have hnd : ¬ p ∣ q * p + s := by
    intro h
    have hps := (Nat.dvd_add_right (dvd_mul_left p q)).mp h
    have := Nat.le_of_dvd hs.1 hps
    omega
  simp [hnd]

/-- Helper: partition filter (p | j) on range (M * p) into r < M with j = p * r. -/
private lemma sum_filter_dvd_range_mul {α : Type*} [AddCommMonoid α] (M p : ℕ)
    (hp : p.Prime) (f : ℕ → α) :
    ∑ j ∈ (range (M * p)).filter (fun j => p ∣ j), f j =
      ∑ r ∈ range M, f (p * r) := by
  rw [Finset.sum_filter, sum_range_mul_eq M p]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hp1 : 1 ≤ p := hp.one_le
  have hsplit : range p = insert 0 (Ico 1 p) := by
    ext x; simp only [mem_range, mem_insert, mem_Ico]; omega
  rw [hsplit, Finset.sum_insert (by simp)]
  have h0 : p ∣ r * p + 0 := by simp
  have hrest : ∑ s ∈ Ico 1 p, (if p ∣ r * p + s then f (r * p + s) else 0) = 0 := by
    refine Finset.sum_eq_zero fun s hs => ?_
    rw [mem_Ico] at hs
    have hnd : ¬ p ∣ r * p + s := by
      intro h
      have hps := (Nat.dvd_add_right (dvd_mul_left p r)).mp h
      have := Nat.le_of_dvd hs.1 hps
      omega
    simp [hnd]
  rw [hrest, add_zero]
  simp [mul_comm]

/-- L3.4: Non-divisible terms of H(n * p^k) vanish modulo p^(3*k). -/
private lemma H_ndiv_supercong (p n k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hn : 0 < n) (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ ∑ j ∈ (range (n * p ^ k)).filter (fun j => ¬ p ∣ j),
      (Nat.choose (n * p ^ k - 1 + j) j : ℤ) ^ 2 := by
  set M := n * p ^ (k - 1)
  set N := n * p ^ k
  have hMpos : 1 ≤ M := Nat.mul_pos hn (Nat.pow_pos hp.pos)
  have hMp : N = M * p := by
    simp only [N, M, mul_assoc, ← pow_succ]
    rw [Nat.sub_add_cancel hk]
  have hNk : p ^ k ∣ M * p := ⟨n, by rw [← hMp]; simp [N, mul_comm]⟩
  apply PVal.int_dvd hp
  rw [Int.cast_sum, hMp, sum_filter_not_dvd_range_mul M p hp]
  -- Approximate each term (q, s) mod p^(3*k) using L3.1(a) and L3.3
  set approx : ℕ → ℕ → ℚ := fun q s =>
    (M * p : ℚ) ^ 2 * (Nat.choose (M + q) q : ℚ) ^ 2 *
      ∑ d ∈ range k, (-1 : ℚ) ^ d * ((d + 1 : ℕ) : ℚ) * (p : ℚ) ^ d * (q : ℚ) ^ d / (s : ℚ) ^ (d + 2)
  have hdiff : PVal p (3 * k)
      (∑ q ∈ range M, ∑ s ∈ Ico 1 p,
        ((((Nat.choose (M * p - 1 + (q * p + s)) (q * p + s) : ℤ) ^ 2 : ℤ) : ℚ) - approx q s)) := by
    refine PVal.sum hp fun q _ => PVal.sum hp fun s hs => ?_
    rw [mem_Ico] at hs
    have h1 := choose_pred_sq_pval p M k q s hp hMpos hNk hs.1 hs.2
    have h2 := inv_sq_geom_series p k q s hp hs.1 hs.2
    have hN2 : PVal p (2 * k) ((M * p : ℚ) ^ 2 * (Nat.choose (M + q) q : ℚ) ^ 2) := by
      have hNp : PVal p (2 * k) ((M * p : ℚ) ^ 2) := by
        have hN1 : PVal p k ((M * p : ℚ)) := by simpa [Nat.cast_mul] using PVal.of_dvd_nat hp hNk
        simpa [mul_comm] using hN1.pow hp 2
      have hch : PVal p 0 ((Nat.choose (M + q) q : ℚ) ^ 2) := by
        simpa using (PVal.nat hp (Nat.choose (M + q) q)).pow hp 2
      exact hNp.mul_zero hp hch
    have h2' : PVal p (3 * k)
        (((M * p : ℚ) ^ 2 * (Nat.choose (M + q) q : ℚ) ^ 2) *
          ((((q * p + s : ℕ) : ℚ) ^ 2)⁻¹ -
            ∑ d ∈ range k, (-1 : ℚ) ^ d * ((d + 1 : ℕ) : ℚ) * (p : ℚ) ^ d * (q : ℚ) ^ d / (s : ℚ) ^ (d + 2))) := by
      have hm := hN2.mul hp h2
      rwa [show 2 * k + k = 3 * k by omega] at hm
    have hadd := h1.add hp h2'
    have heq : ((Nat.choose (M * p - 1 + (q * p + s)) (q * p + s) : ℚ) ^ 2 -
          (M * p : ℚ) ^ 2 * (Nat.choose (M + q) q : ℚ) ^ 2 * (((q * p + s : ℕ) : ℚ) ^ 2)⁻¹) +
        (M * p : ℚ) ^ 2 * (Nat.choose (M + q) q : ℚ) ^ 2 *
          ((((q * p + s : ℕ) : ℚ) ^ 2)⁻¹ -
            ∑ d ∈ range k, (-1 : ℚ) ^ d * ((d + 1 : ℕ) : ℚ) * (p : ℚ) ^ d * (q : ℚ) ^ d / (s : ℚ) ^ (d + 2)) =
        (((Nat.choose (M * p - 1 + (q * p + s)) (q * p + s) : ℤ) ^ 2 : ℤ) : ℚ) - approx q s := by
      simp only [approx]; push_cast; ring
    rwa [heq] at hadd
  -- Swap sums in approx and apply L3.2 + L2.1(a)
  have hmain_eq : ∑ q ∈ range M, ∑ s ∈ Ico 1 p, approx q s =
      ∑ d ∈ range k,
        (-1 : ℚ) ^ d * ((d + 1 : ℕ) : ℚ) * (M * p : ℚ) ^ 2 *
        (∑ s ∈ Ico 1 p, ((s : ℚ) ^ (d + 2))⁻¹) *
        ((p : ℚ) ^ d * ∑ q ∈ range M, (Nat.choose (M + q) q : ℚ) ^ 2 * (q : ℚ) ^ d) := by
    have hstep1 : ∀ q : ℕ, ∑ s ∈ Ico 1 p, approx q s =
        ∑ d ∈ range k,
          (-1 : ℚ) ^ d * ((d + 1 : ℕ) : ℚ) * (M * p : ℚ) ^ 2 *
          (∑ s ∈ Ico 1 p, ((s : ℚ) ^ (d + 2))⁻¹) *
          ((p : ℚ) ^ d * ((Nat.choose (M + q) q : ℚ) ^ 2 * (q : ℚ) ^ d)) := by
      intro q
      simp only [approx, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => by rw [div_eq_mul_inv]; ring
    simp_rw [hstep1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum (s := range M), Finset.mul_sum (s := range M)]
  have hmain_pv : PVal p (3 * k) (∑ q ∈ range M, ∑ s ∈ Ico 1 p, approx q s) := by
    rw [hmain_eq]
    have hmom := moment_sum_dvd p n (k - 1) hp hp5
    refine PVal.sum hp fun d _ => ?_
    have hN2 : PVal p (2 * k) ((M * p : ℚ) ^ 2) := by
      have hN1 : PVal p k ((M * p : ℚ)) := by simpa [Nat.cast_mul] using PVal.of_dvd_nat hp hNk
      simpa [mul_comm] using hN1.pow hp 2
    have hcoef : PVal p 0 ((-1 : ℚ) ^ d * ((d + 1 : ℕ) : ℚ)) :=
      (by simpa using (PVal.int hp (-1)).pow hp d : PVal p 0 ((-1 : ℚ) ^ d)).mul_zero hp (PVal.nat hp _)
    have hN2c : PVal p (2 * k) ((-1 : ℚ) ^ d * ((d + 1 : ℕ) : ℚ) * (M * p : ℚ) ^ 2) :=
      hcoef.zero_mul hp hN2
    by_cases hd0 : d = 0
    · subst hd0
      have hs_pv : PVal p 1 (∑ s ∈ Ico 1 p, ((s : ℚ) ^ (0 + 2))⁻¹) := by
        simpa using sum_inv_sq_mod_p p hp hp5
      have hq_pv : PVal p (k - 1)
          ((p : ℚ) ^ 0 * ∑ q ∈ range M, (Nat.choose (M + q) q : ℚ) ^ 2 * (q : ℚ) ^ 0) := by
        have hq_cast : ((p : ℚ) ^ 0 * ∑ q ∈ range M, (Nat.choose (M + q) q : ℚ) ^ 2 * (q : ℚ) ^ 0) =
            ((∑ q ∈ range (n * p ^ (k - 1)), (Nat.choose (n * p ^ (k - 1) + q) q : ℤ) ^ 2 : ℤ) : ℚ) := by
          simp [M]
        rw [hq_cast]
        exact PVal.of_dvd_int hp hmom.1
      have hm := (hN2c.mul hp hs_pv).mul hp hq_pv
      rwa [show 2 * k + 1 + (k - 1) = 3 * k by omega] at hm
    · have hd1 : 1 ≤ d := by omega
      have hs_pv : PVal p 0 (∑ s ∈ Ico 1 p, ((s : ℚ) ^ (d + 2))⁻¹) := by
        refine PVal.sum hp fun s hs => ?_
        rw [mem_Ico] at hs
        have hnd : ¬ p ∣ s ^ (d + 2) := fun h => by
          have := Nat.le_of_dvd hs.1 (hp.dvd_of_dvd_pow h); omega
        simpa [Nat.cast_pow] using PVal.inv_nat hnd
      have hq_pv : PVal p k
          ((p : ℚ) ^ d * ∑ q ∈ range M, (Nat.choose (M + q) q : ℚ) ^ 2 * (q : ℚ) ^ d) := by
        have hq_cast : (p : ℚ) ^ d * ∑ q ∈ range M, (Nat.choose (M + q) q : ℚ) ^ 2 * (q : ℚ) ^ d =
            (((p : ℤ) ^ d * ∑ q ∈ range (n * p ^ (k - 1)),
              (Nat.choose (n * p ^ (k - 1) + q) q : ℤ) ^ 2 * (q : ℤ) ^ d : ℤ) : ℚ) := by
          simp [M]
        rw [hq_cast]
        have hdvd := hmom.2 d hd1
        rw [Nat.sub_add_cancel hk] at hdvd
        exact PVal.of_dvd_int hp hdvd
      have hm := (hN2c.mul_zero hp hs_pv).mul hp hq_pv
      rwa [show 2 * k + k = 3 * k by omega] at hm
  have hfin := hdiff.add hp hmain_pv
  have heq : (∑ q ∈ range M, ∑ s ∈ Ico 1 p,
        ((((Nat.choose (M * p - 1 + (q * p + s)) (q * p + s) : ℤ) ^ 2 : ℤ) : ℚ) - approx q s)) +
      ∑ q ∈ range M, ∑ s ∈ Ico 1 p, approx q s =
      ∑ q ∈ range M, ∑ s ∈ Ico 1 p,
        (((Nat.choose (M * p - 1 + (q * p + s)) (q * p + s) : ℤ) ^ 2 : ℤ) : ℚ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => by ring
  rwa [heq] at hfin

-- ============================================================================
-- Block D: Assembly of H Supercongruence and Main Theorem
-- ============================================================================

/-- Block D(1): Supercongruence H(n * p^k) == H(n * p^(k-1)) mod p^(3*k). -/
private lemma H_supercong (p n k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hn : 0 < n) (hk : 0 < k) :
    H (n * p ^ k) ≡ H (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ (3 * k)] := by
  set M := n * p ^ (k - 1)
  have hMp : n * p ^ k = M * p := by
    simp only [M, mul_assoc, ← pow_succ]
    rw [Nat.sub_add_cancel hk]
  unfold H
  rw [← Finset.sum_filter_add_sum_filter_not (range (n * p ^ k)) (fun j => p ∣ j)]
  have hdiv_part : ∑ j ∈ (range (n * p ^ k)).filter (fun j => p ∣ j),
      (Nat.choose (n * p ^ k - 1 + j) j : ℤ) ^ 2 =
      ∑ r ∈ range M, (Nat.choose (n * p ^ k - 1 + p * r) (p * r) : ℤ) ^ 2 := by
    conv_lhs => rw [hMp]
    rw [sum_filter_dvd_range_mul M p hp]
    simp only [← hMp]
  have hdiv_cong : ∑ j ∈ (range (n * p ^ k)).filter (fun j => p ∣ j),
      (Nat.choose (n * p ^ k - 1 + j) j : ℤ) ^ 2 ≡
      ∑ r ∈ range M, (Nat.choose (M - 1 + r) r : ℤ) ^ 2 [ZMOD (p : ℤ) ^ (3 * k)] := by
    rw [hdiv_part]
    exact Int.ModEq.sum fun r _ => H_div_term_supercong p n k r hp hp5 hn hk
  have hndiv_cong : ∑ j ∈ (range (n * p ^ k)).filter (fun j => ¬ p ∣ j),
      (Nat.choose (n * p ^ k - 1 + j) j : ℤ) ^ 2 ≡ 0 [ZMOD (p : ℤ) ^ (3 * k)] := by
    rw [Int.modEq_zero_iff_dvd]
    exact H_ndiv_supercong p n k hp hp5 hn hk
  simpa using hdiv_cong.add hndiv_cong

/-- Block D(2): Full supercongruence for b(n). -/
private lemma main_proof :
    ∀ p n k : ℕ, p.Prime → 5 ≤ p → 0 < n → 0 < k →
      b (n * p ^ k) ≡ b (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ (3 * k)] := by
  intro p n k hp hp5 hn hk
  have h1 := two_mul_b_eq (n * p ^ k) (Nat.mul_pos hn (Nat.pow_pos hp.pos))
  have h2 := two_mul_b_eq (n * p ^ (k - 1)) (Nat.mul_pos hn (Nat.pow_pos hp.pos))
  have hC := central_choose_supercong p n k hp hp5 hn hk
  have hH := H_supercong p n k hp hp5 hn hk
  have h2b : 2 * b (n * p ^ k) ≡ 2 * b (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ (3 * k)] := by
    rw [h1, h2]
    exact hC.mul ((hH.mul_left 3).sub (hC.pow 2))
  have hdvd2 : (p : ℤ) ^ (3 * k) ∣ 2 * (b (n * p ^ (k - 1)) - b (n * p ^ k)) := by
    have h := Int.modEq_iff_dvd.mp h2b
    have heq : 2 * b (n * p ^ (k - 1)) - 2 * b (n * p ^ k) =
        2 * (b (n * p ^ (k - 1)) - b (n * p ^ k)) := by ring
    rwa [heq] at h
  have hcop_nat : Nat.Coprime (p ^ (3 * k)) 2 :=
    (hp.coprime_iff_not_dvd.mpr fun h => by have := Nat.le_of_dvd (by decide) h; omega).pow_left _
  have hcop : IsCoprime ((p : ℤ) ^ (3 * k)) 2 := by
    exact_mod_cast Nat.Coprime.isCoprime hcop_nat
  exact Int.modEq_iff_dvd.mpr (hcop.dvd_of_dvd_mul_left hdvd2)

end OMA.S_oeis_a003161.Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a003161.main :=
  OMA.S_oeis_a003161.Proof.main_proof

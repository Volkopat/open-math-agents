import OMAReductions.R_Erdos1049_erdos_1049_R1

/-!
Proof of Erdos1049.erdos_1049.R1.H1 (Erdos 1948): for every integer `t >= 2`, the Lambert series
`sum_{n >= 1} 1 / (t^n - 1)` is irrational.

We follow Borwein and Van Assche via shifted little q-Legendre partial fractions.
-/

namespace Erdos1049R1H1

/-- Helper giving `2 * m.choose 2 = m * (m - 1)`. -/
lemma two_mul_choose_two (m : ℕ) : 2 * m.choose 2 = m * (m - 1) := by
  rw [Nat.choose_two_right]
  exact Nat.mul_div_cancel' (Nat.even_mul_pred_self m).two_dvd

lemma choose_two_succ_zero : ∀ m : ℕ, m.choose 2 + m = (m + 1).choose 2
  | 0 => rfl
  | m + 1 => by
      apply Nat.mul_left_cancel (by decide : 0 < 2)
      have h1 := two_mul_choose_two (m + 1)
      have h2 := two_mul_choose_two (m + 2)
      have h1s : m + 1 - 1 = m := by omega
      have h2s : m + 2 - 1 = m + 1 := by omega
      rw [h1s] at h1
      rw [h2s] at h2
      zify at h1 h2 ⊢
      nlinarith

lemma choose_two_succ (m : ℕ) : (m + 1).choose 2 + (m + 1) = (m + 2).choose 2 :=
  choose_two_succ_zero (m + 1)

/-- The `q`-factorial `(b; b)_m` up to sign, defined as `prod_{s=0}^{m-1} (b^(s+1) - 1)`. -/
def qFact (b : ℕ) : ℕ → ℕ
  | 0 => 1
  | m + 1 => qFact b m * (b ^ (m + 1) - 1)

lemma qFact_pos {b : ℕ} (hb : 2 ≤ b) : ∀ m : ℕ, 0 < qFact b m
  | 0 => Nat.one_pos
  | m + 1 => by
      have hpow : 2 ≤ b ^ (m + 1) := by
        calc
          2 ≤ b := hb
          _ = b ^ 1 := (pow_one b).symm
          _ ≤ b ^ (m + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      exact Nat.mul_pos (qFact_pos hb m) (by omega)

lemma qFact_eq_prod (b : ℕ) : ∀ m : ℕ, qFact b m = ∏ s ∈ Finset.range m, (b ^ (s + 1) - 1)
  | 0 => by simp [qFact]
  | m + 1 => by
      rw [qFact, Finset.prod_range_succ, qFact_eq_prod b m]

lemma qFact_le_pow {b : ℕ} (hb : 2 ≤ b) : ∀ m : ℕ, qFact b m ≤ b ^ ((m + 1).choose 2)
  | 0 => by simp [qFact]
  | m + 1 => by
      have hih := qFact_le_pow hb m
      have hstep : qFact b m * (b ^ (m + 1) - 1) ≤ b ^ ((m + 1).choose 2) * b ^ (m + 1) :=
        Nat.mul_le_mul hih (Nat.sub_le _ _)
      rw [← pow_add, choose_two_succ m] at hstep
      exact hstep

lemma dvd_qFact {b n s : ℕ} (hs1 : 1 ≤ s) (hsn : s ≤ n) : b ^ s - 1 ∣ qFact b n := by
  rw [qFact_eq_prod]
  have hmem : s - 1 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  have hsub : b ^ (s - 1 + 1) - 1 = b ^ s - 1 := by
    have : s - 1 + 1 = s := by omega
    rw [this]
  rw [← hsub]
  exact Finset.dvd_prod_of_mem (fun i => b ^ (i + 1) - 1) hmem

lemma qFact_add (b k : ℕ) :
    ∀ n : ℕ, qFact b (n + k) = qFact b k * ∏ i ∈ Finset.range n, (b ^ (k + i + 1) - 1)
  | 0 => by simp
  | n + 1 => by
      have hidx : n + 1 + k = (n + k) + 1 := by omega
      have hidx2 : k + n + 1 = n + k + 1 := by omega
      rw [hidx, qFact, qFact_add b k n, Finset.prod_range_succ, mul_assoc, hidx2]

/-- Gaussian `q`-binomial coefficient `[n choose k]_b` in `ℕ`. -/
def qBinom (b : ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => b ^ (k + 1) * qBinom b n (k + 1) + qBinom b n k

lemma qBinom_eq_zero_of_lt {b : ℕ} : ∀ {n k : ℕ}, n < k → qBinom b n k = 0
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k + 1, h => by
      have h1 : n < k + 1 := by omega
      have h2 : n < k := by omega
      simp [qBinom, qBinom_eq_zero_of_lt h1, qBinom_eq_zero_of_lt h2]

lemma qBinom_self (b : ℕ) : ∀ n : ℕ, qBinom b n n = 1
  | 0 => rfl
  | n + 1 => by
      rw [qBinom, qBinom_eq_zero_of_lt (Nat.lt_succ_self n), qBinom_self b n, mul_zero, zero_add]

lemma qBinom_mul_qFact {b : ℕ} (hb : 2 ≤ b) :
    ∀ {n k : ℕ}, k ≤ n → qBinom b n k * qFact b k * qFact b (n - k) = qFact b n
  | 0, 0, _ => by simp [qBinom, qFact]
  | n + 1, 0, _ => by simp [qBinom, qFact]
  | n + 1, k + 1, hk => by
      by_cases hkn : k = n
      · subst hkn
        simp [qBinom_self, qFact]
      · have hk1 : k + 1 ≤ n := by omega
        have hk0 : k ≤ n := by omega
        set m := n - k - 1
        have hnk : n - k = m + 1 := by omega
        have hn1k1 : n + 1 - (k + 1) = m + 1 := by omega
        have hnk1 : n - (k + 1) = m := by omega
        have ih1 := qBinom_mul_qFact hb hk1
        have ih2 := qBinom_mul_qFact hb hk0
        rw [hnk1] at ih1
        rw [hnk] at ih2
        rw [hn1k1]
        have h1k : 1 ≤ b ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
        have h1m : 1 ≤ b ^ (m + 1) := Nat.one_le_pow _ _ (by omega)
        have h1n : 1 ≤ b ^ (n + 1) := Nat.one_le_pow _ _ (by omega)
        have hexp : k + 1 + (m + 1) = n + 1 := by omega
        zify [h1k, h1m, h1n]
        have ih1z : (qBinom b n (k + 1) : ℤ) * (qFact b (k + 1) : ℤ) * (qFact b m : ℤ) =
            (qFact b n : ℤ) := by exact_mod_cast ih1
        have ih2z : (qBinom b n k : ℤ) * (qFact b k : ℤ) * (qFact b (m + 1) : ℤ) =
            (qFact b n : ℤ) := by exact_mod_cast ih2
        simp only [qBinom, qFact]
        push_cast [h1k, h1m, h1n]
        have hpow : (b : ℤ) ^ (k + 1) * (b : ℤ) ^ (m + 1) = (b : ℤ) ^ (n + 1) := by
          rw [← pow_add, hexp]
        have hfac1 : (qFact b (k + 1) : ℤ) = (qFact b k : ℤ) * ((b : ℤ) ^ (k + 1) - 1) := by
          rw [qFact]; push_cast [h1k]; rfl
        have hfac2 : (qFact b (m + 1) : ℤ) = (qFact b m : ℤ) * ((b : ℤ) ^ (m + 1) - 1) := by
          rw [qFact]; push_cast [h1m]; rfl
        rw [hfac1] at ih1z
        rw [hfac2] at ih2z
        calc
          ((b : ℤ) ^ (k + 1) * (qBinom b n (k + 1) : ℤ) + (qBinom b n k : ℤ)) *
              ((qFact b k : ℤ) * ((b : ℤ) ^ (k + 1) - 1)) *
              ((qFact b m : ℤ) * ((b : ℤ) ^ (m + 1) - 1))
              = (b : ℤ) ^ (k + 1) *
                  ((qBinom b n (k + 1) : ℤ) * ((qFact b k : ℤ) * ((b : ℤ) ^ (k + 1) - 1)) *
                    (qFact b m : ℤ)) * ((b : ℤ) ^ (m + 1) - 1) +
                ((qBinom b n k : ℤ) * (qFact b k : ℤ) *
                    ((qFact b m : ℤ) * ((b : ℤ) ^ (m + 1) - 1))) *
                  ((b : ℤ) ^ (k + 1) - 1) := by ring
          _ = (b : ℤ) ^ (k + 1) * (qFact b n : ℤ) * ((b : ℤ) ^ (m + 1) - 1) +
                (qFact b n : ℤ) * ((b : ℤ) ^ (k + 1) - 1) := by rw [ih1z, ih2z]
          _ = (qFact b n : ℤ) * ((b : ℤ) ^ (k + 1) * (b : ℤ) ^ (m + 1) - 1) := by ring
          _ = (qFact b n : ℤ) * ((b : ℤ) ^ (n + 1) - 1) := by rw [hpow]

lemma qBinom_add_mul_qFact {b : ℕ} (hb : 2 ≤ b) (n k : ℕ) :
    qBinom b (n + k) k * qFact b n = ∏ i ∈ Finset.range n, (b ^ (k + i + 1) - 1) := by
  have h1 := qBinom_mul_qFact hb (n := n + k) (k := k) (Nat.le_add_left k n)
  have hsub : n + k - k = n := by omega
  rw [hsub, qFact_add] at h1
  apply Nat.mul_left_cancel (qFact_pos hb k)
  calc
    qFact b k * (qBinom b (n + k) k * qFact b n) = qBinom b (n + k) k * qFact b k * qFact b n := by
      ring
    _ = qFact b k * ∏ i ∈ Finset.range n, (b ^ (k + i + 1) - 1) := h1

/-- Integer partial-fraction coefficients of the shifted little q-Legendre polynomial. -/
def aCoeff (b n r : ℕ) : ℤ :=
  (-1 : ℤ) ^ (n - r) * (b : ℤ) ^ ((n - r).choose 2) * (qBinom b (n + r) r : ℤ) *
    (qBinom b n r : ℤ)

lemma choose_two_add_mul {n k : ℕ} (hk : k ≤ n) :
    (n - k).choose 2 + k * n = n.choose 2 + (k + 1).choose 2 := by
  rcases eq_or_lt_of_le hk with rfl | hkn
  · rw [Nat.sub_self, ← choose_two_succ_zero k]
    cases k with
    | zero => rfl
    | succ j =>
        have h1 := two_mul_choose_two (j + 1)
        simp only [Nat.add_sub_cancel] at h1
        have h0 : Nat.choose 0 2 = 0 := rfl
        zify at h1 h0 ⊢
        nlinarith
  · set m := n - k - 1
    have hnk : n - k = m + 1 := by omega
    have hn : n = k + m + 1 := by omega
    apply Nat.mul_left_cancel (by decide : 0 < 2)
    have h1 := two_mul_choose_two (m + 1)
    have h2 := two_mul_choose_two (k + m + 1)
    have h3 := two_mul_choose_two (k + 1)
    have h1s : m + 1 - 1 = m := by omega
    have h2s : k + m + 1 - 1 = k + m := by omega
    have h3s : k + 1 - 1 = k := by omega
    rw [h1s] at h1
    rw [h2s] at h2
    rw [h3s] at h3
    rw [hnk, hn]
    zify at h1 h2 h3 ⊢
    nlinarith

noncomputable def polyLHS (b n : ℕ) : Polynomial ℝ :=
  ∑ r ∈ Finset.range (n + 1),
    Polynomial.C (aCoeff b n r : ℝ) *
      ∏ s ∈ (Finset.range (n + 1)).erase r, (Polynomial.C ((b : ℝ) ^ s) * Polynomial.X - 1)

noncomputable def polyRHS (b n : ℕ) : Polynomial ℝ :=
  Polynomial.C ((b : ℝ) ^ (n.choose 2)) *
    ∏ i ∈ Finset.range n, (Polynomial.X - Polynomial.C ((b : ℝ) ^ (i + 1)))

lemma natDegree_polyLHS_le (b n : ℕ) : (polyLHS b n).natDegree ≤ n := by
  unfold polyLHS
  have hlin : ∀ s : ℕ, (Polynomial.C ((b : ℝ) ^ s) * Polynomial.X - 1).natDegree ≤ 1 := by
    intro s
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    rw [Polynomial.natDegree_one, Nat.max_zero]
    refine (Polynomial.natDegree_mul_le).trans ?_
    simp
  have hsum : (∑ r ∈ Finset.range (n + 1), Polynomial.C (aCoeff b n r : ℝ) *
      ∏ s ∈ (Finset.range (n + 1)).erase r,
        (Polynomial.C ((b : ℝ) ^ s) * Polynomial.X - 1)).natDegree ≤
      Finset.fold max 0 (fun r => (Polynomial.C (aCoeff b n r : ℝ) *
        ∏ s ∈ (Finset.range (n + 1)).erase r,
          (Polynomial.C ((b : ℝ) ^ s) * Polynomial.X - 1)).natDegree) (Finset.range (n + 1)) :=
    Polynomial.natDegree_sum_le _ _
  refine hsum.trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le n, fun r hr => ?_⟩
  have hprod : (∏ s ∈ (Finset.range (n + 1)).erase r,
      (Polynomial.C ((b : ℝ) ^ s) * Polynomial.X - 1)).natDegree ≤ n := by
    have hdp := Polynomial.natDegree_prod_le ((Finset.range (n + 1)).erase r)
      (fun s => Polynomial.C ((b : ℝ) ^ s) * Polynomial.X - 1)
    have hsum1 : ∑ s ∈ (Finset.range (n + 1)).erase r,
        (Polynomial.C ((b : ℝ) ^ s) * Polynomial.X - 1).natDegree ≤
        ∑ _s ∈ (Finset.range (n + 1)).erase r, 1 :=
      Finset.sum_le_sum fun s _ => hlin s
    have hcard1 : ∑ _s ∈ (Finset.range (n + 1)).erase r, 1 = n := by
      rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem hr,
        Finset.card_range, Nat.add_sub_cancel]
    exact hdp.trans (hsum1.trans hcard1.le)
  refine (Polynomial.natDegree_mul_le).trans ?_
  simpa using hprod

lemma natDegree_polyRHS_le (b n : ℕ) : (polyRHS b n).natDegree ≤ n := by
  unfold polyRHS
  refine (Polynomial.natDegree_mul_le).trans ?_
  simp only [Polynomial.natDegree_C, zero_add]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc
    ∑ i ∈ Finset.range n, (Polynomial.X - Polynomial.C ((b : ℝ) ^ (i + 1))).natDegree
        ≤ ∑ _i ∈ Finset.range n, 1 := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [Polynomial.natDegree_X_sub_C]
    _ = n := by simp

lemma prod_erase_split (n k : ℕ) (hk : k ≤ n) (f : ℕ → ℝ) :
    ∏ s ∈ (Finset.range (n + 1)).erase k, f s =
      (∏ s ∈ Finset.range k, f s) * ∏ j ∈ Finset.range (n - k), f (k + j + 1) := by
  have hunion : (Finset.range (n + 1)).erase k =
      Finset.range k ∪ (Finset.range (n - k)).image (fun j => k + j + 1) := by
    ext s
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨hne, hlt⟩
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl h
      · exact Or.inr ⟨s - k - 1, by omega, by omega⟩
    · rintro (h | ⟨j, hj, rfl⟩)
      · exact ⟨by omega, by omega⟩
      · exact ⟨by omega, by omega⟩
  have hdisj : Disjoint (Finset.range k) ((Finset.range (n - k)).image (fun j => k + j + 1)) := by
    rw [Finset.disjoint_left]
    intro s hs1 hs2
    rw [Finset.mem_range] at hs1
    rw [Finset.mem_image] at hs2
    rcases hs2 with ⟨j, _, rfl⟩
    omega
  rw [hunion, Finset.prod_union hdisj, Finset.prod_image (fun a _ b _ h => by omega)]

lemma prod_range_factor_lt {b : ℕ} (hb : 2 ≤ b) :
    ∀ k : ℕ, ∏ s ∈ Finset.range k, ((b : ℝ) ^ s * ((b : ℝ) ^ k)⁻¹ - 1) =
      (-1 : ℝ) ^ k * (qFact b k : ℝ) * ((b : ℝ) ^ ((k + 1).choose 2))⁻¹
  | 0 => by simp [qFact]
  | k + 1 => by
      have hb0 : (b : ℝ) ≠ 0 := by positivity
      have hcongr : ∏ s ∈ Finset.range k, ((b : ℝ) ^ (s + 1) * ((b : ℝ) ^ (k + 1))⁻¹ - 1) =
          ∏ s ∈ Finset.range k, ((b : ℝ) ^ s * ((b : ℝ) ^ k)⁻¹ - 1) := by
        refine Finset.prod_congr rfl fun s _ => ?_
        rw [pow_succ, pow_succ, mul_inv,
          show (b : ℝ) ^ s * (b : ℝ) * (((b : ℝ) ^ k)⁻¹ * (b : ℝ)⁻¹) =
            (b : ℝ) ^ s * ((b : ℝ) ^ k)⁻¹ by field_simp]
      have hpow : (b : ℝ) ^ ((k + 1).choose 2) * (b : ℝ) ^ (k + 1) =
          (b : ℝ) ^ ((k + 2).choose 2) := by
        rw [← pow_add, choose_two_succ k]
      have h1b : 1 ≤ b ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
      rw [Finset.prod_range_succ', pow_zero, one_mul, hcongr, prod_range_factor_lt hb k, qFact]
      push_cast [h1b]
      have hterm : ((b : ℝ) ^ (k + 1))⁻¹ - 1 =
          (-1 : ℝ) * ((b : ℝ) ^ (k + 1) - 1) * ((b : ℝ) ^ (k + 1))⁻¹ := by
        field_simp
        ring
      rw [hterm]
      calc
        (-1 : ℝ) ^ k * (qFact b k : ℝ) * ((b : ℝ) ^ ((k + 1).choose 2))⁻¹ *
            ((-1 : ℝ) * ((b : ℝ) ^ (k + 1) - 1) * ((b : ℝ) ^ (k + 1))⁻¹)
            = (-1 : ℝ) ^ (k + 1) * ((qFact b k : ℝ) * ((b : ℝ) ^ (k + 1) - 1)) *
                (((b : ℝ) ^ ((k + 1).choose 2)) * (b : ℝ) ^ (k + 1))⁻¹ := by
              rw [pow_succ, mul_inv]
              ring
        _ = (-1 : ℝ) ^ (k + 1) * ((qFact b k : ℝ) * ((b : ℝ) ^ (k + 1) - 1)) *
              ((b : ℝ) ^ ((k + 2).choose 2))⁻¹ := by
            rw [hpow]

lemma prod_range_factor_gt {b : ℕ} (hb : 2 ≤ b) (k m : ℕ) :
    ∏ j ∈ Finset.range m, ((b : ℝ) ^ (k + j + 1) * ((b : ℝ) ^ k)⁻¹ - 1) = (qFact b m : ℝ) := by
  have hb0 : (b : ℝ) ≠ 0 := by positivity
  rw [qFact_eq_prod]
  push_cast
  refine Finset.prod_congr rfl fun j _ => ?_
  have h1j : 1 ≤ b ^ (j + 1) := Nat.one_le_pow _ _ (by omega)
  rw [Nat.cast_sub h1j, Nat.cast_pow, Nat.cast_one]
  rw [show k + j + 1 = k + (j + 1) by omega, pow_add]
  field_simp

lemma eval_polyLHS_inv_pow {b : ℕ} (hb : 2 ≤ b) (n k : ℕ) (hk : k ≤ n) :
    Polynomial.eval (((b : ℝ) ^ k)⁻¹) (polyLHS b n) =
      (aCoeff b n k : ℝ) * (-1 : ℝ) ^ k * (qFact b k : ℝ) *
        ((b : ℝ) ^ ((k + 1).choose 2))⁻¹ * (qFact b (n - k) : ℝ) := by
  have hb0 : (b : ℝ) ≠ 0 := by positivity
  unfold polyLHS
  rw [Polynomial.eval_finsetSum]
  have hkmem : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hzero : ∀ r ∈ Finset.range (n + 1), r ≠ k →
      Polynomial.eval (((b : ℝ) ^ k)⁻¹)
        (Polynomial.C (aCoeff b n r : ℝ) *
          ∏ s ∈ (Finset.range (n + 1)).erase r, (Polynomial.C ((b : ℝ) ^ s) * Polynomial.X - 1)) = 0 := by
    intro r hr hne
    rw [Polynomial.eval_mul, Polynomial.eval_prod]
    have hkill : (∏ s ∈ (Finset.range (n + 1)).erase r,
        Polynomial.eval (((b : ℝ) ^ k)⁻¹) (Polynomial.C ((b : ℝ) ^ s) * Polynomial.X - 1)) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne.symm, hkmem⟩) ?_
      simp [mul_inv_cancel₀ (pow_ne_zero k hb0)]
    rw [hkill, mul_zero]
  rw [Finset.sum_eq_single k hzero (fun hkabs => absurd hkmem hkabs)]
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  have hev : ∀ s, Polynomial.eval (((b : ℝ) ^ k)⁻¹)
      (Polynomial.C ((b : ℝ) ^ s) * Polynomial.X - 1) = (b : ℝ) ^ s * ((b : ℝ) ^ k)⁻¹ - 1 := by
    intro s
    simp
  simp only [hev]
  rw [prod_erase_split n k hk, prod_range_factor_lt hb k, prod_range_factor_gt hb k (n - k)]
  ring

lemma eval_polyRHS_inv_pow {b : ℕ} (hb : 2 ≤ b) (n k : ℕ) :
    Polynomial.eval (((b : ℝ) ^ k)⁻¹) (polyRHS b n) =
      (b : ℝ) ^ (n.choose 2) * (-1 : ℝ) ^ n * ((b : ℝ) ^ (k * n))⁻¹ *
        ∏ i ∈ Finset.range n, ((b : ℝ) ^ (k + i + 1) - 1) := by
  have hb0 : (b : ℝ) ≠ 0 := by positivity
  unfold polyRHS
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  have hev : ∏ i ∈ Finset.range n,
        Polynomial.eval (((b : ℝ) ^ k)⁻¹) (Polynomial.X - Polynomial.C ((b : ℝ) ^ (i + 1))) =
      ∏ i ∈ Finset.range n, ((-1 : ℝ) * ((b : ℝ) ^ k)⁻¹ * ((b : ℝ) ^ (k + i + 1) - 1)) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [show k + i + 1 = k + (i + 1) by omega, pow_add]
    field_simp
    ring
  rw [hev, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
    Finset.card_range, inv_pow, ← pow_mul]
  ring

lemma polyLHS_eq_polyRHS {b : ℕ} (hb : 2 ≤ b) (n : ℕ) : polyLHS b n = polyRHS b n := by
  have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast (show 1 < b by omega)
  have hb0 : (b : ℝ) ≠ 0 := by positivity
  let S : Finset ℝ := (Finset.range (n + 1)).image (fun k : ℕ => ((b : ℝ) ^ k)⁻¹)
  have hinj : Function.Injective (fun k : ℕ => ((b : ℝ) ^ k)⁻¹) := by
    intro i j hij
    have hpow : (b : ℝ) ^ i = (b : ℝ) ^ j := inv_injective hij
    exact (pow_right_injective₀ (by positivity) hb1.ne') hpow
  have hScard : S.card = n + 1 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
  have hdeg : (polyLHS b n - polyRHS b n).natDegree < S.card := by
    rw [hScard]
    refine (Polynomial.natDegree_sub_le _ _).trans_lt ?_
    exact Nat.lt_succ_of_le (max_le (natDegree_polyLHS_le b n) (natDegree_polyRHS_le b n))
  have hzero : ∀ x ∈ S, Polynomial.eval x (polyLHS b n - polyRHS b n) = 0 := by
    intro x hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨k, hk, rfl⟩
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [Polynomial.eval_sub, sub_eq_zero, eval_polyLHS_inv_pow hb n k hkn,
      eval_polyRHS_inv_pow hb n k]
    have ha : (aCoeff b n k : ℝ) = (-1 : ℝ) ^ (n - k) * (b : ℝ) ^ ((n - k).choose 2) *
        (qBinom b (n + k) k : ℝ) * (qBinom b n k : ℝ) := by
      unfold aCoeff
      push_cast
      rfl
    have hsign : (-1 : ℝ) ^ (n - k) * (-1 : ℝ) ^ k = (-1 : ℝ) ^ n := by
      rw [← pow_add, Nat.sub_add_cancel hkn]
    have hq1 : (qBinom b n k : ℝ) * (qFact b k : ℝ) * (qFact b (n - k) : ℝ) = (qFact b n : ℝ) := by
      exact_mod_cast qBinom_mul_qFact hb hkn
    have hq2 : (qBinom b (n + k) k : ℝ) * (qFact b n : ℝ) =
        ∏ i ∈ Finset.range n, ((b : ℝ) ^ (k + i + 1) - 1) := by
      have hnat := qBinom_add_mul_qFact hb n k
      have hcast := congrArg (Nat.cast : ℕ → ℝ) hnat
      push_cast at hcast
      refine hcast.trans (Finset.prod_congr rfl fun i _ => ?_)
      have h1ki : 1 ≤ b ^ (k + i + 1) := Nat.one_le_pow _ _ (by omega)
      rw [Nat.cast_sub h1ki, Nat.cast_pow, Nat.cast_one]
    have hc1 : (b : ℝ) ^ ((k + 1).choose 2) ≠ 0 := pow_ne_zero _ hb0
    have hc2 : (b : ℝ) ^ (k * n) ≠ 0 := pow_ne_zero _ hb0
    have hexp : (b : ℝ) ^ ((n - k).choose 2) * ((b : ℝ) ^ ((k + 1).choose 2))⁻¹ =
        (b : ℝ) ^ (n.choose 2) * ((b : ℝ) ^ (k * n))⁻¹ := by
      field_simp [hc1, hc2]
      rw [← pow_add, ← pow_add, choose_two_add_mul hkn, add_comm (n.choose 2)]
    calc
      (aCoeff b n k : ℝ) * (-1 : ℝ) ^ k * (qFact b k : ℝ) *
          ((b : ℝ) ^ ((k + 1).choose 2))⁻¹ * (qFact b (n - k) : ℝ)
          = ((-1 : ℝ) ^ (n - k) * (-1 : ℝ) ^ k) *
              ((b : ℝ) ^ ((n - k).choose 2) * ((b : ℝ) ^ ((k + 1).choose 2))⁻¹) *
              ((qBinom b (n + k) k : ℝ) * ((qBinom b n k : ℝ) * (qFact b k : ℝ) *
                (qFact b (n - k) : ℝ))) := by
            rw [ha]
            ring
      _ = (-1 : ℝ) ^ n * ((b : ℝ) ^ ((n - k).choose 2) * ((b : ℝ) ^ ((k + 1).choose 2))⁻¹) *
            ((qBinom b (n + k) k : ℝ) * (qFact b n : ℝ)) := by
          rw [hsign, hq1]
      _ = (-1 : ℝ) ^ n * ((b : ℝ) ^ ((n - k).choose 2) * ((b : ℝ) ^ ((k + 1).choose 2))⁻¹) *
            ∏ i ∈ Finset.range n, ((b : ℝ) ^ (k + i + 1) - 1) := by
          rw [hq2]
      _ = (b : ℝ) ^ (n.choose 2) * (-1 : ℝ) ^ n * ((b : ℝ) ^ (k * n))⁻¹ *
            ∏ i ∈ Finset.range n, ((b : ℝ) ^ (k + i + 1) - 1) := by
          rw [hexp]
          ring
  exact sub_eq_zero.mp (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ S hzero hdeg)

lemma partial_fraction_identity {b : ℕ} (hb : 2 ≤ b) (n j : ℕ) :
    ∑ r ∈ Finset.range (n + 1), (aCoeff b n r : ℝ) / ((b : ℝ) ^ (j + 1 + r) - 1) =
      (b : ℝ) ^ (n.choose 2) *
        (∏ i ∈ Finset.range n, ((b : ℝ) ^ (j + 1) - (b : ℝ) ^ (i + 1))) /
        ∏ r ∈ Finset.range (n + 1), ((b : ℝ) ^ (j + 1 + r) - 1) := by
  have hb1 : (1 : ℝ) < (b : ℝ) := by exact_mod_cast (show 1 < b by omega)
  have hden_ne : ∀ r : ℕ, (b : ℝ) ^ (j + 1 + r) - 1 ≠ 0 := by
    intro r
    have hgt : (1 : ℝ) < (b : ℝ) ^ (j + 1 + r) := one_lt_pow₀ hb1 (by omega)
    linarith
  have hprod_ne : (∏ r ∈ Finset.range (n + 1), ((b : ℝ) ^ (j + 1 + r) - 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun r _ => hden_ne r
  have heval := congrArg (Polynomial.eval ((b : ℝ) ^ (j + 1))) (polyLHS_eq_polyRHS hb n)
  unfold polyLHS polyRHS at heval
  rw [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod] at heval
  have hleft :
      ∑ r ∈ Finset.range (n + 1),
        Polynomial.eval ((b : ℝ) ^ (j + 1)) (Polynomial.C (aCoeff b n r : ℝ) *
          ∏ s ∈ (Finset.range (n + 1)).erase r, (Polynomial.C ((b : ℝ) ^ s) * Polynomial.X - 1))
      = (∏ r ∈ Finset.range (n + 1), ((b : ℝ) ^ (j + 1 + r) - 1)) *
          ∑ r ∈ Finset.range (n + 1), (aCoeff b n r : ℝ) / ((b : ℝ) ^ (j + 1 + r) - 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
    have hprod_erase :
        (∏ s ∈ (Finset.range (n + 1)).erase r,
          Polynomial.eval ((b : ℝ) ^ (j + 1)) (Polynomial.C ((b : ℝ) ^ s) * Polynomial.X - 1)) =
        ∏ s ∈ (Finset.range (n + 1)).erase r, ((b : ℝ) ^ (j + 1 + s) - 1) := by
      refine Finset.prod_congr rfl fun s _ => ?_
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        Polynomial.eval_one]
      rw [← pow_add, add_comm s (j + 1)]
    rw [hprod_erase, ← Finset.mul_prod_erase (Finset.range (n + 1))
      (fun s => (b : ℝ) ^ (j + 1 + s) - 1) hr]
    field_simp [hden_ne r]
  have hright :
      (b : ℝ) ^ (n.choose 2) *
          ∏ i ∈ Finset.range n,
            Polynomial.eval ((b : ℝ) ^ (j + 1)) (Polynomial.X - Polynomial.C ((b : ℝ) ^ (i + 1)))
        = (b : ℝ) ^ (n.choose 2) *
            ∏ i ∈ Finset.range n, ((b : ℝ) ^ (j + 1) - (b : ℝ) ^ (i + 1)) := by
    congr 1
    exact Finset.prod_congr rfl fun i _ => by simp
  rw [hleft, hright] at heval
  exact (eq_div_iff_mul_eq hprod_ne).mpr (by linarith)

/-- Target Lambert series shifted to `ℕ`. -/
noncomputable def L (b : ℕ) : ℝ := ∑' k : ℕ, 1 / ((b : ℝ) ^ (k + 1) - 1)

noncomputable def Ptilde (b n : ℕ) (u : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (n + 1), (aCoeff b n r : ℝ) * u ^ r

def PtildeInt (b n : ℕ) : ℤ :=
  ∑ r ∈ Finset.range (n + 1), aCoeff b n r * (b : ℤ) ^ (n * r)

def Aint (b n : ℕ) : ℤ := (qFact b n : ℤ) * PtildeInt b n

def Cint (b n : ℕ) : ℤ :=
  PtildeInt b n * (∑ s ∈ Finset.range n, ((qFact b n / (b ^ (s + 1) - 1) : ℕ) : ℤ)) +
    ∑ r ∈ Finset.range (n + 1), aCoeff b n r *
      ∑ i ∈ Finset.range r, (b : ℤ) ^ (n * (r - 1 - i)) * ((qFact b n / (b ^ (i + 1) - 1) : ℕ) : ℤ)

noncomputable def Rtilde (b n : ℕ) : ℝ :=
  ∑' k : ℕ, Ptilde b n (((b : ℝ) ^ (k + 1))⁻¹) / ((b : ℝ) ^ (n + k + 1) - 1)

lemma PtildeInt_cast (b n : ℕ) : (PtildeInt b n : ℝ) = Ptilde b n ((b : ℝ) ^ n) := by
  unfold PtildeInt Ptilde
  push_cast
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← pow_mul]

lemma inv_pow_sub_one_le {b : ℕ} (hb : 2 ≤ b) (k : ℕ) :
    1 / ((b : ℝ) ^ (k + 1) - 1) ≤ ((b : ℝ)⁻¹) ^ k := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hk0 : (0 : ℝ) < (b : ℝ) ^ k := by positivity
  have h1 : (b : ℝ) ^ k ≤ (b : ℝ) ^ (k + 1) - 1 := by
    have hpow : (b : ℝ) ^ (k + 1) = (b : ℝ) ^ k * (b : ℝ) := pow_succ (b : ℝ) k
    have hbk1 : (1 : ℝ) ≤ (b : ℝ) ^ k := one_le_pow₀ (by linarith)
    nlinarith
  rw [one_div, inv_pow]
  exact inv_anti₀ hk0 h1

lemma summable_inv_pow_sub_one {b : ℕ} (hb : 2 ≤ b) :
    Summable (fun k : ℕ => 1 / ((b : ℝ) ^ (k + 1) - 1)) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hgeom : Summable (fun k : ℕ => ((b : ℝ)⁻¹) ^ k) :=
    summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ (by linarith))
  refine Summable.of_nonneg_of_le (fun k => ?_) (inv_pow_sub_one_le hb) hgeom
  have hgt : (1 : ℝ) < (b : ℝ) ^ (k + 1) := one_lt_pow₀ (by linarith) (by omega)
  positivity

lemma tsum_inv_pow_succ {b m : ℕ} (hb : 2 ≤ b) (hm : 1 ≤ m) :
    ∑' k : ℕ, (((b : ℝ) ^ m)⁻¹) ^ (k + 1) = 1 / ((b : ℝ) ^ m - 1) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hbm1 : (1 : ℝ) < (b : ℝ) ^ m := one_lt_pow₀ (by linarith) (by omega)
  have hr0 : 0 ≤ ((b : ℝ) ^ m)⁻¹ := by positivity
  have hr1 : ((b : ℝ) ^ m)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hbm1
  have hsum : (∑' k : ℕ, (((b : ℝ) ^ m)⁻¹) ^ (k + 1)) =
      ((b : ℝ) ^ m)⁻¹ * ∑' k : ℕ, (((b : ℝ) ^ m)⁻¹) ^ k := by
    simp_rw [pow_succ']
    exact tsum_mul_left
  rw [hsum, tsum_geometric_of_lt_one hr0 hr1]
  have hbm0 : (b : ℝ) ^ m ≠ 0 := by positivity
  have hsub : (b : ℝ) ^ m - 1 ≠ 0 := by linarith
  field_simp

lemma summable_Rtilde {b : ℕ} (hb : 2 ≤ b) (n : ℕ) :
    Summable (fun k : ℕ => Ptilde b n (((b : ℝ) ^ (k + 1))⁻¹) / ((b : ℝ) ^ (n + k + 1) - 1)) := by
  let M : ℝ := ∑ r ∈ Finset.range (n + 1), |(aCoeff b n r : ℝ)|
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hgeom : Summable (fun k : ℕ => M * ((b : ℝ)⁻¹) ^ k) :=
    (summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ (by linarith))).mul_left M
  refine Summable.of_norm_bounded hgeom fun k => ?_
  have hP : ‖Ptilde b n (((b : ℝ) ^ (k + 1))⁻¹)‖ ≤ M := by
    unfold Ptilde
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_inv, abs_pow]
    have hle1 : |(b : ℝ)| ^ (k + 1) ≥ 1 := by
      rw [abs_of_nonneg (by positivity)]
      exact one_le_pow₀ (by linarith)
    have hinv1 : ((|(b : ℝ)| ^ (k + 1))⁻¹) ^ r ≤ 1 :=
      pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hle1)
    exact mul_le_of_le_one_right (abs_nonneg _) hinv1
  have hden : 0 < (b : ℝ) ^ (n + k + 1) - 1 := by
    have : (1 : ℝ) < (b : ℝ) ^ (n + k + 1) := one_lt_pow₀ (by linarith) (by omega)
    linarith
  have hden_le : ((b : ℝ) ^ (n + k + 1) - 1)⁻¹ ≤ ((b : ℝ)⁻¹) ^ k := by
    have hpow : (b : ℝ) ^ (k + 1) ≤ (b : ℝ) ^ (n + k + 1) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have hinv : ((b : ℝ) ^ (n + k + 1) - 1)⁻¹ ≤ ((b : ℝ) ^ (k + 1) - 1)⁻¹ :=
      inv_anti₀ (by
        have : (1 : ℝ) < (b : ℝ) ^ (k + 1) := one_lt_pow₀ (by linarith) (by omega)
        linarith) (by linarith)
    have hk_le := inv_pow_sub_one_le hb k
    rw [one_div] at hk_le
    exact hinv.trans hk_le
  rw [norm_div, Real.norm_of_nonneg hden.le, div_eq_mul_inv]
  exact mul_le_mul hP hden_le (by positivity) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

lemma telescope_term {b : ℕ} (hb : 2 ≤ b) (n r k : ℕ) :
    ((b : ℝ) ^ (n * r) - (((b : ℝ) ^ (k + 1))⁻¹) ^ r) / ((b : ℝ) ^ (n + k + 1) - 1) =
      ∑ i ∈ Finset.range r, (b : ℝ) ^ (n * (r - 1 - i)) * (((b : ℝ) ^ (i + 1))⁻¹) ^ (k + 1) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb0 : (b : ℝ) ≠ 0 := by positivity
  have hden : (b : ℝ) ^ (n + k + 1) - 1 ≠ 0 := by
    have : (1 : ℝ) < (b : ℝ) ^ (n + k + 1) := one_lt_pow₀ (by linarith) (by omega)
    linarith
  rw [div_eq_iff hden]
  let f : ℕ → ℝ := fun i => (b : ℝ) ^ (n * (r - i)) * (((b : ℝ) ^ (k + 1))⁻¹) ^ i
  have hstep : ∀ i ∈ Finset.range r,
      (b : ℝ) ^ (n * (r - 1 - i)) * (((b : ℝ) ^ (i + 1))⁻¹) ^ (k + 1) *
          ((b : ℝ) ^ (n + k + 1) - 1) = f i - f (i + 1) := by
    intro i hi
    rw [Finset.mem_range] at hi
    dsimp [f]
    have hexp1 : n * (r - i) = n * (r - 1 - i) + n := by
      have : r - i = (r - 1 - i) + 1 := by omega
      rw [this, mul_add, mul_one]
    have hexp2 : r - (i + 1) = r - 1 - i := by omega
    have hsub1 : (((b : ℝ) ^ (i + 1))⁻¹) ^ (k + 1) =
        (((b : ℝ) ^ (k + 1))⁻¹) ^ (i + 1) := by
      rw [inv_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm (i + 1) (k + 1)]
    have hsub2 : (((b : ℝ) ^ (k + 1))⁻¹) ^ (i + 1) * (b : ℝ) ^ (n + k + 1) =
        (b : ℝ) ^ n * (((b : ℝ) ^ (k + 1))⁻¹) ^ i := by
      rw [pow_succ (((b : ℝ) ^ (k + 1))⁻¹) i, show n + k + 1 = (k + 1) + n by omega,
        pow_add (b : ℝ) (k + 1) n]
      field_simp
    rw [hsub1, mul_sub, mul_one, mul_assoc, hsub2, hexp1, hexp2,
      pow_add (b : ℝ) (n * (r - 1 - i)) n, pow_succ (((b : ℝ) ^ (k + 1))⁻¹) i]
    ring
  rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl hstep, Finset.sum_range_sub' f r]
  simp [f]

lemma linear_form_eq {b : ℕ} (hb : 2 ≤ b) (n : ℕ) :
    (qFact b n : ℝ) * Rtilde b n = (Aint b n : ℝ) * L b - (Cint b n : ℝ) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hLsum : Summable (fun k : ℕ => 1 / ((b : ℝ) ^ (k + 1) - 1)) := summable_inv_pow_sub_one hb
  have htail : Summable (fun k : ℕ => 1 / ((b : ℝ) ^ (n + k + 1) - 1)) := by
    have hshift := (summable_nat_add_iff n).mpr hLsum
    refine hshift.congr fun k => ?_
    rw [show k + n + 1 = n + k + 1 by omega]
  have hsum_split : ∑' k : ℕ, 1 / ((b : ℝ) ^ (n + k + 1) - 1) =
      L b - ∑ s ∈ Finset.range n, 1 / ((b : ℝ) ^ (s + 1) - 1) := by
    have h1 := hLsum.sum_add_tsum_nat_add n
    have hcongr : (∑' k : ℕ, 1 / ((b : ℝ) ^ (k + n + 1) - 1)) =
        ∑' k : ℕ, 1 / ((b : ℝ) ^ (n + k + 1) - 1) := by
      congr 1
      ext k
      rw [show k + n + 1 = n + k + 1 by omega]
    unfold L
    linarith
  have hLHS_eval : (∑' k : ℕ,
      (Ptilde b n ((b : ℝ) ^ n) - Ptilde b n (((b : ℝ) ^ (k + 1))⁻¹)) /
        ((b : ℝ) ^ (n + k + 1) - 1)) =
      Ptilde b n ((b : ℝ) ^ n) * (L b - ∑ s ∈ Finset.range n, 1 / ((b : ℝ) ^ (s + 1) - 1)) -
        Rtilde b n := by
    have heq : (fun k : ℕ => (Ptilde b n ((b : ℝ) ^ n) - Ptilde b n (((b : ℝ) ^ (k + 1))⁻¹)) /
          ((b : ℝ) ^ (n + k + 1) - 1)) =
        (fun k : ℕ => Ptilde b n ((b : ℝ) ^ n) * (1 / ((b : ℝ) ^ (n + k + 1) - 1)) -
          Ptilde b n (((b : ℝ) ^ (k + 1))⁻¹) / ((b : ℝ) ^ (n + k + 1) - 1)) := by
      ext k
      ring
    rw [heq, Summable.tsum_sub (htail.mul_left _) (summable_Rtilde hb n), tsum_mul_left, hsum_split]
    rfl
  have hpoint : ∀ k : ℕ,
      (Ptilde b n ((b : ℝ) ^ n) - Ptilde b n (((b : ℝ) ^ (k + 1))⁻¹)) /
          ((b : ℝ) ^ (n + k + 1) - 1) =
        ∑ r ∈ Finset.range (n + 1), ∑ i ∈ Finset.range r,
          (aCoeff b n r : ℝ) * (b : ℝ) ^ (n * (r - 1 - i)) *
            (((b : ℝ) ^ (i + 1))⁻¹) ^ (k + 1) := by
    intro k
    unfold Ptilde
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hpow : ((b : ℝ) ^ n) ^ r = (b : ℝ) ^ (n * r) := (pow_mul _ n r).symm
    rw [← mul_sub, mul_div_assoc, hpow, telescope_term hb n r k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hterm_sum : ∀ r i : ℕ, Summable (fun k : ℕ =>
      (aCoeff b n r : ℝ) * (b : ℝ) ^ (n * (r - 1 - i)) * (((b : ℝ) ^ (i + 1))⁻¹) ^ (k + 1)) := by
    intro r i
    have hi1 : (1 : ℝ) < (b : ℝ) ^ (i + 1) := one_lt_pow₀ (by linarith) (by omega)
    have hgeom : Summable (fun k : ℕ => (((b : ℝ) ^ (i + 1))⁻¹) ^ k) :=
      summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hi1)
    have hgeom1 : Summable (fun k : ℕ => (((b : ℝ) ^ (i + 1))⁻¹) ^ (k + 1)) := by
      have heq : (fun k : ℕ => (((b : ℝ) ^ (i + 1))⁻¹) ^ (k + 1)) =
          fun k : ℕ => ((b : ℝ) ^ (i + 1))⁻¹ * (((b : ℝ) ^ (i + 1))⁻¹) ^ k :=
        funext fun k => pow_succ' _ k
      rw [heq]
      exact hgeom.mul_left _
    exact hgeom1.mul_left _
  have hRHS_eval : (∑' k : ℕ, ∑ r ∈ Finset.range (n + 1), ∑ i ∈ Finset.range r,
      (aCoeff b n r : ℝ) * (b : ℝ) ^ (n * (r - 1 - i)) * (((b : ℝ) ^ (i + 1))⁻¹) ^ (k + 1)) =
      ∑ r ∈ Finset.range (n + 1), (aCoeff b n r : ℝ) * ∑ i ∈ Finset.range r,
        (b : ℝ) ^ (n * (r - 1 - i)) / ((b : ℝ) ^ (i + 1) - 1) := by
    rw [Summable.tsum_finsetSum (fun r _ =>
        summable_sum fun i _ => hterm_sum r i)]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Summable.tsum_finsetSum (fun i _ => hterm_sum r i), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [tsum_mul_left, tsum_inv_pow_succ hb (m := i + 1) (by omega)]
    ring
  have hcomb : Ptilde b n ((b : ℝ) ^ n) * (L b - ∑ s ∈ Finset.range n, 1 / ((b : ℝ) ^ (s + 1) - 1)) -
      Rtilde b n =
      ∑ r ∈ Finset.range (n + 1), (aCoeff b n r : ℝ) * ∑ i ∈ Finset.range r,
        (b : ℝ) ^ (n * (r - 1 - i)) / ((b : ℝ) ^ (i + 1) - 1) := by
    rw [← hLHS_eval, ← hRHS_eval]
    congr 1
    ext k
    exact hpoint k
  have hdiv_cast : ∀ {s : ℕ}, 1 ≤ s → s ≤ n →
      (qFact b n : ℝ) / ((b : ℝ) ^ s - 1) = ((qFact b n / (b ^ s - 1) : ℕ) : ℝ) := by
    intro s hs1 hsn
    have hdvd := dvd_qFact (b := b) hs1 hsn
    have hmul : (qFact b n / (b ^ s - 1)) * (b ^ s - 1) = qFact b n :=
      Nat.div_mul_cancel hdvd
    have h1s : 1 ≤ b ^ s := Nat.one_le_pow _ _ (by omega)
    have hne : (b : ℝ) ^ s - 1 ≠ 0 := by
      have : (1 : ℝ) < (b : ℝ) ^ s := one_lt_pow₀ (by linarith) (by omega)
      linarith
    have hcast := congrArg (Nat.cast : ℕ → ℝ) hmul
    push_cast [h1s] at hcast
    exact div_eq_of_eq_mul hne hcast.symm
  have hmain := congrArg (fun x : ℝ => (qFact b n : ℝ) * x) hcomb
  have hA : (Aint b n : ℝ) = (qFact b n : ℝ) * Ptilde b n ((b : ℝ) ^ n) := by
    unfold Aint
    rw [Int.cast_mul, Int.cast_natCast, PtildeInt_cast]
  have hC1 : (qFact b n : ℝ) * (Ptilde b n ((b : ℝ) ^ n) *
      ∑ s ∈ Finset.range n, 1 / ((b : ℝ) ^ (s + 1) - 1)) =
      (PtildeInt b n : ℝ) * ∑ s ∈ Finset.range n, ((qFact b n / (b ^ (s + 1) - 1) : ℕ) : ℝ) := by
    rw [PtildeInt_cast, mul_left_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finset.mem_range] at hs
    rw [mul_one_div, hdiv_cast (Nat.succ_pos s) (by omega)]
  have hC2 : (qFact b n : ℝ) * (∑ r ∈ Finset.range (n + 1), (aCoeff b n r : ℝ) *
      ∑ i ∈ Finset.range r, (b : ℝ) ^ (n * (r - 1 - i)) / ((b : ℝ) ^ (i + 1) - 1)) =
      ∑ r ∈ Finset.range (n + 1), (aCoeff b n r : ℝ) *
        ∑ i ∈ Finset.range r, (b : ℝ) ^ (n * (r - 1 - i)) *
          ((qFact b n / (b ^ (i + 1) - 1) : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hrn : r ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    rw [mul_left_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [mul_comm ((qFact b n : ℝ)) _, div_mul_eq_mul_div, mul_div_assoc,
      hdiv_cast (s := i + 1) (by omega) (by omega)]
  have hC : (Cint b n : ℝ) =
      (PtildeInt b n : ℝ) * ∑ s ∈ Finset.range n, ((qFact b n / (b ^ (s + 1) - 1) : ℕ) : ℝ) +
      ∑ r ∈ Finset.range (n + 1), (aCoeff b n r : ℝ) *
        ∑ i ∈ Finset.range r, (b : ℝ) ^ (n * (r - 1 - i)) *
          ((qFact b n / (b ^ (i + 1) - 1) : ℕ) : ℝ) := by
    unfold Cint
    push_cast
    rfl
  rw [mul_sub, mul_sub, mul_sub] at hmain
  rw [hC2, hC1, ← mul_assoc, ← hA] at hmain
  linarith

noncomputable def W (b n j : ℕ) : ℝ :=
  (((b : ℝ) ^ n)⁻¹) ^ (j + 1) *
    ((b : ℝ) ^ (n.choose 2) * (∏ i ∈ Finset.range n, ((b : ℝ) ^ (j + 1) - (b : ℝ) ^ (i + 1))) /
      ∏ r ∈ Finset.range (n + 1), ((b : ℝ) ^ (j + 1 + r) - 1))

lemma Rtilde_eq_tsum_W {b : ℕ} (hb : 2 ≤ b) {n : ℕ} (hn : 1 ≤ n) :
    Rtilde b n = ∑' j : ℕ, W b n j ∧ Summable (W b n) := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  let g : ℕ → ℕ → ℝ := fun k j =>
    Ptilde b n (((b : ℝ) ^ (k + 1))⁻¹) * (((b : ℝ) ^ n)⁻¹) ^ (j + 1) *
      (((b : ℝ) ^ (j + 1))⁻¹) ^ (k + 1)
  have hrow : ∀ k : ℕ, ∑' j : ℕ, g k j =
      Ptilde b n (((b : ℝ) ^ (k + 1))⁻¹) / ((b : ℝ) ^ (n + k + 1) - 1) := by
    intro k
    have hcongr : (fun j : ℕ => g k j) = fun j : ℕ =>
        Ptilde b n (((b : ℝ) ^ (k + 1))⁻¹) * (((b : ℝ) ^ (n + k + 1))⁻¹) ^ (j + 1) := by
      ext j
      dsimp [g]
      have h1 : (((b : ℝ) ^ n)⁻¹) ^ (j + 1) * (((b : ℝ) ^ (j + 1))⁻¹) ^ (k + 1) =
          (((b : ℝ) ^ (n + k + 1))⁻¹) ^ (j + 1) := by
        rw [inv_pow, inv_pow, inv_pow, ← mul_inv, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]
        congr 2
        ring
      rw [mul_assoc, h1]
    rw [hcongr, tsum_mul_left, tsum_inv_pow_succ hb (by omega), mul_one_div]
  have hcol : ∀ j : ℕ, ∑' k : ℕ, g k j = W b n j := by
    intro j
    have hcongr : (fun k : ℕ => g k j) = fun k : ℕ =>
        (((b : ℝ) ^ n)⁻¹) ^ (j + 1) *
          ∑ r ∈ Finset.range (n + 1), (aCoeff b n r : ℝ) *
            (((b : ℝ) ^ (j + 1 + r))⁻¹) ^ (k + 1) := by
      ext k
      dsimp [g, Ptilde]
      rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      have h1 : (((((b : ℝ) ^ (k + 1))⁻¹) ^ r) * (((b : ℝ) ^ (j + 1))⁻¹) ^ (k + 1)) =
          (((b : ℝ) ^ (j + 1 + r))⁻¹) ^ (k + 1) := by
        rw [inv_pow, inv_pow, inv_pow, ← mul_inv, ← pow_mul, ← pow_mul, ← pow_mul,
          ← pow_add]
        congr 2
        ring
      calc
        (aCoeff b n r : ℝ) * (((b : ℝ) ^ (k + 1))⁻¹) ^ r * (((b : ℝ) ^ n)⁻¹) ^ (j + 1) *
            (((b : ℝ) ^ (j + 1))⁻¹) ^ (k + 1)
            = (((b : ℝ) ^ n)⁻¹) ^ (j + 1) * ((aCoeff b n r : ℝ) *
                (((((b : ℝ) ^ (k + 1))⁻¹) ^ r) * (((b : ℝ) ^ (j + 1))⁻¹) ^ (k + 1))) := by ring
        _ = (((b : ℝ) ^ n)⁻¹) ^ (j + 1) *
              ((aCoeff b n r : ℝ) * (((b : ℝ) ^ (j + 1 + r))⁻¹) ^ (k + 1)) := by
            rw [h1]
    have hterm : ∀ r : ℕ, Summable (fun k : ℕ =>
        (aCoeff b n r : ℝ) * (((b : ℝ) ^ (j + 1 + r))⁻¹) ^ (k + 1)) := by
      intro r
      have hlt : ((b : ℝ) ^ (j + 1 + r))⁻¹ < 1 :=
        inv_lt_one_of_one_lt₀ (one_lt_pow₀ (by linarith) (by omega))
      have hgeom : Summable (fun k : ℕ => (((b : ℝ) ^ (j + 1 + r))⁻¹) ^ (k + 1)) := by
        simp_rw [pow_succ']
        exact (summable_geometric_of_lt_one (by positivity) hlt).mul_left _
      exact hgeom.mul_left _
    rw [hcongr, tsum_mul_left, Summable.tsum_finsetSum (fun r _ => hterm r)]
    have hsum_eval : (∑ r ∈ Finset.range (n + 1),
        ∑' k : ℕ, (aCoeff b n r : ℝ) * (((b : ℝ) ^ (j + 1 + r))⁻¹) ^ (k + 1)) =
        ∑ r ∈ Finset.range (n + 1), (aCoeff b n r : ℝ) / ((b : ℝ) ^ (j + 1 + r) - 1) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [tsum_mul_left, tsum_inv_pow_succ hb (by omega), mul_one_div]
    rw [hsum_eval, partial_fraction_identity hb n j]
    rfl
  let M : ℝ := ∑ r ∈ Finset.range (n + 1), |(aCoeff b n r : ℝ)|
  have hg_unc : Summable (Function.uncurry g) := by
    have hs1 : Summable (fun k : ℕ => M * ((b : ℝ)⁻¹) ^ (k + 1)) := by
      simp_rw [pow_succ']
      exact ((summable_geometric_of_lt_one (by positivity)
        (inv_lt_one_of_one_lt₀ (by linarith))).mul_left _).mul_left M
    have hs2 : Summable (fun j : ℕ => (((b : ℝ) ^ n)⁻¹) ^ (j + 1)) := by
      have hlt : ((b : ℝ) ^ n)⁻¹ < 1 :=
        inv_lt_one_of_one_lt₀ (one_lt_pow₀ (by linarith) (by omega))
      simp_rw [pow_succ']
      exact (summable_geometric_of_lt_one (by positivity) hlt).mul_left _
    have hprod := Summable.mul_of_nonneg hs1 hs2 (fun k => by positivity) (fun j => by positivity)
    refine Summable.of_norm_bounded hprod fun p => ?_
    dsimp [Function.uncurry, g]
    have hP : |Ptilde b n (((b : ℝ) ^ (p.1 + 1))⁻¹)| ≤ M := by
      unfold Ptilde
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
      rw [abs_mul, abs_pow, abs_inv, abs_pow]
      have hle1 : 1 ≤ |(b : ℝ)| ^ (p.1 + 1) := by
        rw [abs_of_nonneg (by positivity)]
        exact one_le_pow₀ (by linarith)
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (by positivity)
        (inv_le_one_of_one_le₀ hle1))
    have hpow_le : (((b : ℝ) ^ (p.2 + 1))⁻¹) ^ (p.1 + 1) ≤ ((b : ℝ)⁻¹) ^ (p.1 + 1) := by
      refine pow_le_pow_left₀ (by positivity) ?_ (p.1 + 1)
      exact inv_anti₀ (by positivity) (le_self_pow₀ (by linarith) (by omega))
    have hnn1 : 0 ≤ (((b : ℝ) ^ n)⁻¹) ^ (p.2 + 1) :=
      pow_nonneg (inv_nonneg.mpr (pow_nonneg (by positivity : (0 : ℝ) ≤ b) n)) (p.2 + 1)
    have hnn2 : 0 ≤ (((b : ℝ) ^ (p.2 + 1))⁻¹) ^ (p.1 + 1) :=
      pow_nonneg (inv_nonneg.mpr (pow_nonneg (by positivity : (0 : ℝ) ≤ b) (p.2 + 1))) (p.1 + 1)
    change |Ptilde b n (((b : ℝ) ^ (p.1 + 1))⁻¹) * (((b : ℝ) ^ n)⁻¹) ^ (p.2 + 1) *
        (((b : ℝ) ^ (p.2 + 1))⁻¹) ^ (p.1 + 1)| ≤ _
    rw [abs_mul, abs_mul, abs_of_nonneg hnn1, abs_of_nonneg hnn2]
    calc
      |Ptilde b n (((b : ℝ) ^ (p.1 + 1))⁻¹)| * (((b : ℝ) ^ n)⁻¹) ^ (p.2 + 1) *
          (((b : ℝ) ^ (p.2 + 1))⁻¹) ^ (p.1 + 1)
          ≤ M * (((b : ℝ) ^ n)⁻¹) ^ (p.2 + 1) * ((b : ℝ)⁻¹) ^ (p.1 + 1) := by
            have h1 : |Ptilde b n (((b : ℝ) ^ (p.1 + 1))⁻¹)| * (((b : ℝ) ^ n)⁻¹) ^ (p.2 + 1) ≤
                M * (((b : ℝ) ^ n)⁻¹) ^ (p.2 + 1) :=
              mul_le_mul_of_nonneg_right hP (by positivity)
            exact mul_le_mul h1 hpow_le (by positivity) (by positivity)
      _ = M * ((b : ℝ)⁻¹) ^ (p.1 + 1) * (((b : ℝ) ^ n)⁻¹) ^ (p.2 + 1) := by ring
  have hrow_sum : ∀ k : ℕ, Summable (fun j => g k j) := fun k => hg_unc.prod_factor k
  have hcol_sum : ∀ j : ℕ, Summable (fun k => g k j) := by
    intro j
    exact hg_unc.comp_injective (i := fun k : ℕ => (k, j)) fun _ _ h => (Prod.mk.inj h).1
  have hcomm := Summable.tsum_comm' hg_unc hrow_sum hcol_sum
  have hW_sum : Summable (W b n) := by
    have hbound : Summable (fun j : ℕ =>
        (M * (∑' k : ℕ, ((b : ℝ)⁻¹) ^ (k + 1))) * (((b : ℝ) ^ n)⁻¹) ^ (j + 1)) := by
      have hlt : ((b : ℝ) ^ n)⁻¹ < 1 :=
        inv_lt_one_of_one_lt₀ (one_lt_pow₀ (by linarith) (by omega))
      have hs2 : Summable (fun j : ℕ => (((b : ℝ) ^ n)⁻¹) ^ (j + 1)) := by
        have heq : (fun j : ℕ => (((b : ℝ) ^ n)⁻¹) ^ (j + 1)) =
            fun j : ℕ => ((b : ℝ) ^ n)⁻¹ * (((b : ℝ) ^ n)⁻¹) ^ j :=
          funext fun j => pow_succ' _ j
        rw [heq]
        exact (summable_geometric_of_lt_one (by positivity) hlt).mul_left _
      exact hs2.mul_left _
    refine Summable.of_norm_bounded hbound fun j => ?_
    rw [← hcol j]
    have hgn_sum : Summable (fun k : ℕ => ‖g k j‖) := (hcol_sum j).norm
    have hmaj : ∀ k : ℕ, ‖g k j‖ ≤ (M * ((b : ℝ)⁻¹) ^ (k + 1)) * (((b : ℝ) ^ n)⁻¹) ^ (j + 1) := by
      intro k
      have hP : ‖Ptilde b n (((b : ℝ) ^ (k + 1))⁻¹)‖ ≤ M := by
        unfold Ptilde
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_inv, abs_pow]
        have hle1 : 1 ≤ |(b : ℝ)| ^ (k + 1) := by
          rw [abs_of_nonneg (by positivity)]
          exact one_le_pow₀ (by linarith)
        exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (by positivity)
          (inv_le_one_of_one_le₀ hle1))
      have hpow_le : (((b : ℝ) ^ (j + 1))⁻¹) ^ (k + 1) ≤ ((b : ℝ)⁻¹) ^ (k + 1) := by
        refine pow_le_pow_left₀ (by positivity) ?_ (k + 1)
        exact inv_anti₀ (by positivity) (le_self_pow₀ (by linarith) (by omega))
      have hnn1 : 0 ≤ (((b : ℝ) ^ n)⁻¹) ^ (j + 1) :=
        pow_nonneg (inv_nonneg.mpr (pow_nonneg (by positivity : (0 : ℝ) ≤ b) n)) (j + 1)
      have hnn2 : 0 ≤ (((b : ℝ) ^ (j + 1))⁻¹) ^ (k + 1) :=
        pow_nonneg (inv_nonneg.mpr (pow_nonneg (by positivity : (0 : ℝ) ≤ b) (j + 1))) (k + 1)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hnn1, abs_of_nonneg hnn2]
      calc
        |Ptilde b n (((b : ℝ) ^ (k + 1))⁻¹)| * (((b : ℝ) ^ n)⁻¹) ^ (j + 1) *
            (((b : ℝ) ^ (j + 1))⁻¹) ^ (k + 1)
            ≤ M * (((b : ℝ) ^ n)⁻¹) ^ (j + 1) * ((b : ℝ)⁻¹) ^ (k + 1) := by
              have h1 : |Ptilde b n (((b : ℝ) ^ (k + 1))⁻¹)| * (((b : ℝ) ^ n)⁻¹) ^ (j + 1) ≤
                  M * (((b : ℝ) ^ n)⁻¹) ^ (j + 1) :=
                mul_le_mul_of_nonneg_right hP (by positivity)
              exact mul_le_mul h1 hpow_le (by positivity) (by positivity)
        _ = (M * ((b : ℝ)⁻¹) ^ (k + 1)) * (((b : ℝ) ^ n)⁻¹) ^ (j + 1) := by ring
    have hs_maj : Summable (fun k : ℕ =>
        (M * ((b : ℝ)⁻¹) ^ (k + 1)) * (((b : ℝ) ^ n)⁻¹) ^ (j + 1)) := by
      have hg1 : Summable (fun k : ℕ => ((b : ℝ)⁻¹) ^ (k + 1)) := by
        have heq : (fun k : ℕ => ((b : ℝ)⁻¹) ^ (k + 1)) =
            fun k : ℕ => (b : ℝ)⁻¹ * ((b : ℝ)⁻¹) ^ k := funext fun k => pow_succ' _ k
        rw [heq]
        exact (summable_geometric_of_lt_one (by positivity)
          (inv_lt_one_of_one_lt₀ (by linarith))).mul_left _
      exact (hg1.mul_left M).mul_right _
    have htsum_eq : (∑' k : ℕ, (M * ((b : ℝ)⁻¹) ^ (k + 1)) * (((b : ℝ) ^ n)⁻¹) ^ (j + 1)) =
        (M * ∑' k : ℕ, ((b : ℝ)⁻¹) ^ (k + 1)) * (((b : ℝ) ^ n)⁻¹) ^ (j + 1) := by
      rw [tsum_mul_right]
      congr 1
      exact tsum_mul_left
    exact (norm_tsum_le_tsum_norm hgn_sum).trans
      ((Summable.tsum_le_tsum hmaj hgn_sum hs_maj).trans htsum_eq.le)
  refine ⟨?_, hW_sum⟩
  calc
    Rtilde b n = ∑' k : ℕ, ∑' j : ℕ, g k j := by
        unfold Rtilde
        congr 1
        ext k
        exact (hrow k).symm
    _ = ∑' j : ℕ, ∑' k : ℕ, g k j := hcomm.symm
    _ = ∑' j : ℕ, W b n j := by
        congr 1
        ext j
        exact hcol j

lemma W_eq_zero_of_lt (b n j : ℕ) (hjn : j < n) : W b n j = 0 := by
  unfold W
  have hprod : ∏ i ∈ Finset.range n, ((b : ℝ) ^ (j + 1) - (b : ℝ) ^ (i + 1)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_range.mpr hjn) (sub_self _)
  rw [hprod, mul_zero, zero_div, mul_zero]

lemma W_pos {b : ℕ} (hb : 2 ≤ b) {n j : ℕ} (hnj : n ≤ j) : 0 < W b n j := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  unfold W
  have hpref : 0 < (((b : ℝ) ^ n)⁻¹) ^ (j + 1) := by positivity
  have hnum : 0 < (b : ℝ) ^ (n.choose 2) *
      ∏ i ∈ Finset.range n, ((b : ℝ) ^ (j + 1) - (b : ℝ) ^ (i + 1)) := by
    refine mul_pos (by positivity) (Finset.prod_pos fun i hi => ?_)
    rw [Finset.mem_range] at hi
    have hlt : i + 1 < j + 1 := by omega
    have hpow : (b : ℝ) ^ (i + 1) < (b : ℝ) ^ (j + 1) :=
      pow_lt_pow_right₀ (by linarith) hlt
    linarith
  have hden : 0 < ∏ r ∈ Finset.range (n + 1), ((b : ℝ) ^ (j + 1 + r) - 1) := by
    refine Finset.prod_pos fun r _ => ?_
    have hgt : (1 : ℝ) < (b : ℝ) ^ (j + 1 + r) := one_lt_pow₀ (by linarith) (by omega)
    linarith
  exact mul_pos hpref (div_pos hnum hden)

lemma W_nonneg {b : ℕ} (hb : 2 ≤ b) (n j : ℕ) : 0 ≤ W b n j := by
  by_cases h : j < n
  · rw [W_eq_zero_of_lt b n j h]
  · exact (W_pos hb (not_lt.mp h)).le

lemma prod_pow_add_range (a : ℝ) (j : ℕ) :
    ∀ m : ℕ, ∏ r ∈ Finset.range m, a ^ (j + r) = a ^ (m * j + m.choose 2)
  | 0 => by simp
  | m + 1 => by
      rw [Finset.prod_range_succ, prod_pow_add_range a j m, ← pow_add]
      congr 1
      have h := choose_two_succ_zero m
      rw [Nat.succ_mul]
      omega

lemma W_le {b : ℕ} (hb : 2 ≤ b) {n j : ℕ} (hnj : n ≤ j) :
    W b n j ≤ ((b : ℝ) ^ (n + (n + 1) * j))⁻¹ := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb0 : (b : ℝ) ≠ 0 := by positivity
  have hnum_le : ∏ i ∈ Finset.range n, ((b : ℝ) ^ (j + 1) - (b : ℝ) ^ (i + 1)) ≤
      (b : ℝ) ^ (n * (j + 1)) := by
    calc
      ∏ i ∈ Finset.range n, ((b : ℝ) ^ (j + 1) - (b : ℝ) ^ (i + 1))
          ≤ ∏ _i ∈ Finset.range n, (b : ℝ) ^ (j + 1) := by
            refine Finset.prod_le_prod (fun i hi => ?_) (fun i _ => ?_)
            · rw [Finset.mem_range] at hi
              have hlt : i + 1 < j + 1 := by omega
              have hpow : (b : ℝ) ^ (i + 1) < (b : ℝ) ^ (j + 1) :=
                pow_lt_pow_right₀ (by linarith) hlt
              linarith
            · have : 0 ≤ (b : ℝ) ^ (i + 1) := by positivity
              linarith
      _ = (b : ℝ) ^ (n * (j + 1)) := by
          rw [Finset.prod_const, Finset.card_range, ← pow_mul, mul_comm]
  have hden_ge : (b : ℝ) ^ ((n + 1) * j + (n + 1).choose 2) ≤
      ∏ r ∈ Finset.range (n + 1), ((b : ℝ) ^ (j + 1 + r) - 1) := by
    rw [← prod_pow_add_range (b : ℝ) j (n + 1)]
    refine Finset.prod_le_prod (fun _ _ => by positivity) fun r _ => ?_
    have hpow : (b : ℝ) ^ (j + 1 + r) = (b : ℝ) ^ (j + r) * (b : ℝ) := by
      rw [show j + 1 + r = (j + r) + 1 by omega, pow_succ]
    have hge1 : (1 : ℝ) ≤ (b : ℝ) ^ (j + r) := one_le_pow₀ (by linarith)
    nlinarith
  have hden_pos : 0 < (b : ℝ) ^ ((n + 1) * j + (n + 1).choose 2) := by positivity
  have hch : (n + 1).choose 2 = n.choose 2 + n := (choose_two_succ_zero n).symm
  unfold W
  have h1 : (b : ℝ) ^ (n.choose 2) *
        (∏ i ∈ Finset.range n, ((b : ℝ) ^ (j + 1) - (b : ℝ) ^ (i + 1))) /
        (∏ r ∈ Finset.range (n + 1), ((b : ℝ) ^ (j + 1 + r) - 1)) ≤
      ((b : ℝ) ^ (n.choose 2) * (b : ℝ) ^ (n * (j + 1))) /
        (b : ℝ) ^ ((n + 1) * j + (n + 1).choose 2) := by
    refine div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_left hnum_le (by positivity)) hden_pos hden_ge
  have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ (((b : ℝ) ^ n)⁻¹) ^ (j + 1) by positivity)
  refine h2.trans_eq ?_
  rw [hch, inv_pow, ← pow_mul]
  have hexp : (n + 1) * j + (n.choose 2 + n) = n.choose 2 + (n + (n + 1) * j) := by ring
  rw [hexp, pow_add]
  have hne1 : (b : ℝ) ^ (n.choose 2) ≠ 0 := pow_ne_zero _ hb0
  have hne2 : (b : ℝ) ^ (n + (n + 1) * j) ≠ 0 := pow_ne_zero _ hb0
  have hne3 : (b : ℝ) ^ (n * (j + 1)) ≠ 0 := pow_ne_zero _ hb0
  field_simp [hne1, hne2, hne3]

lemma Rtilde_pos {b : ℕ} (hb : 2 ≤ b) {n : ℕ} (hn : 1 ≤ n) : 0 < Rtilde b n := by
  obtain ⟨hEq, hW_sum⟩ := Rtilde_eq_tsum_W hb hn
  rw [hEq]
  exact hW_sum.tsum_pos (W_nonneg hb n) n (W_pos hb le_rfl)

lemma Rtilde_le {b : ℕ} (hb : 2 ≤ b) {n : ℕ} (hn : 1 ≤ n) :
    Rtilde b n ≤ 2 * ((b : ℝ) ^ (n ^ 2 + 2 * n))⁻¹ := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  obtain ⟨hEq, hW_sum⟩ := Rtilde_eq_tsum_W hb hn
  have hsplit := hW_sum.sum_add_tsum_nat_add n
  have hzero : ∑ i ∈ Finset.range n, W b n i = 0 :=
    Finset.sum_eq_zero fun i hi => W_eq_zero_of_lt b n i (Finset.mem_range.mp hi)
  rw [hzero, zero_add, ← hEq] at hsplit
  let r : ℝ := ((b : ℝ) ^ (n + 1))⁻¹
  have hr0 : 0 ≤ r := by positivity
  have hr_half : r ≤ 1 / 2 := by
    have hbn : (2 : ℝ) ≤ (b : ℝ) ^ (n + 1) := by
      have : (b : ℝ) ^ (1 : ℕ) ≤ (b : ℝ) ^ (n + 1) := pow_le_pow_right₀ (by linarith) (by omega)
      linarith [pow_one (b : ℝ)]
    have : r ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by positivity) hbn
    linarith
  have hr1 : r < 1 := by linarith
  have hterm : ∀ m : ℕ, W b n (m + n) ≤ ((b : ℝ) ^ (n ^ 2 + 2 * n))⁻¹ * r ^ m := by
    intro m
    have hm_le := W_le hb (n := n) (j := m + n) (by omega)
    have hexp : n + (n + 1) * (m + n) = (n ^ 2 + 2 * n) + (n + 1) * m := by ring
    refine hm_le.trans_eq ?_
    rw [hexp, pow_add, mul_inv]
    congr 1
    dsimp [r]
    rw [inv_pow, pow_mul]
  have hs_shift : Summable (fun m : ℕ => W b n (m + n)) :=
    (summable_nat_add_iff n).mpr hW_sum
  have hs_geom : Summable (fun m : ℕ => ((b : ℝ) ^ (n ^ 2 + 2 * n))⁻¹ * r ^ m) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have htsum_le := Summable.tsum_le_tsum hterm hs_shift hs_geom
  rw [hsplit, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1] at htsum_le
  have hinv_le : (1 - r)⁻¹ ≤ 2 := by
    have hpos : 0 < (1 - r : ℝ) := by linarith
    have : (1 / 2 : ℝ) ≤ 1 - r := by linarith
    have := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) this
    linarith
  calc
    Rtilde b n ≤ ((b : ℝ) ^ (n ^ 2 + 2 * n))⁻¹ * (1 - r)⁻¹ := htsum_le
    _ ≤ ((b : ℝ) ^ (n ^ 2 + 2 * n))⁻¹ * 2 :=
        mul_le_mul_of_nonneg_left hinv_le (by positivity)
    _ = 2 * ((b : ℝ) ^ (n ^ 2 + 2 * n))⁻¹ := by ring

lemma choose_add_le_sq (n : ℕ) : (n + 1).choose 2 + n ≤ n ^ 2 + 2 * n := by
  apply Nat.le_of_mul_le_mul_left _ (by decide : 0 < 2)
  have h := two_mul_choose_two (n + 1)
  simp only [Nat.add_sub_cancel] at h
  zify
  nlinarith

lemma qFact_mul_Rtilde_le {b : ℕ} (hb : 2 ≤ b) {n : ℕ} (hn : 1 ≤ n) :
    (qFact b n : ℝ) * Rtilde b n ≤ 2 / (2 : ℝ) ^ n := by
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hq : (qFact b n : ℝ) ≤ (b : ℝ) ^ ((n + 1).choose 2) := by
    exact_mod_cast qFact_le_pow hb n
  have hR := Rtilde_le hb hn
  have hprod : (qFact b n : ℝ) * Rtilde b n ≤
      2 * ((b : ℝ) ^ ((n + 1).choose 2) * ((b : ℝ) ^ (n ^ 2 + 2 * n))⁻¹) := by
    calc
      (qFact b n : ℝ) * Rtilde b n
          ≤ (b : ℝ) ^ ((n + 1).choose 2) * (2 * ((b : ℝ) ^ (n ^ 2 + 2 * n))⁻¹) :=
            mul_le_mul hq hR (Rtilde_pos hb hn).le (by positivity)
      _ = 2 * ((b : ℝ) ^ ((n + 1).choose 2) * ((b : ℝ) ^ (n ^ 2 + 2 * n))⁻¹) := by ring
  have hexp := choose_add_le_sq n
  have hpow_le : (b : ℝ) ^ ((n + 1).choose 2 + n) ≤ (b : ℝ) ^ (n ^ 2 + 2 * n) :=
    pow_le_pow_right₀ (by linarith) hexp
  have hb0 : (b : ℝ) ≠ 0 := by positivity
  have hratio : (b : ℝ) ^ ((n + 1).choose 2) * ((b : ℝ) ^ (n ^ 2 + 2 * n))⁻¹ ≤ ((b : ℝ) ^ n)⁻¹ := by
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    calc
      (b : ℝ) ^ ((n + 1).choose 2)
          = (b : ℝ) ^ ((n + 1).choose 2) * ((b : ℝ) ^ n * ((b : ℝ) ^ n)⁻¹) := by
            rw [mul_inv_cancel₀ (pow_ne_zero n hb0), mul_one]
      _ = ((b : ℝ) ^ ((n + 1).choose 2 + n)) * ((b : ℝ) ^ n)⁻¹ := by
          rw [pow_add]; ring
      _ ≤ (b : ℝ) ^ (n ^ 2 + 2 * n) * ((b : ℝ) ^ n)⁻¹ :=
          mul_le_mul_of_nonneg_right hpow_le (by positivity)
      _ = ((b : ℝ) ^ n)⁻¹ * (b : ℝ) ^ (n ^ 2 + 2 * n) := by ring
  have htwo : ((b : ℝ) ^ n)⁻¹ ≤ ((2 : ℝ) ^ n)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) hb2 n)
  calc
    (qFact b n : ℝ) * Rtilde b n
        ≤ 2 * ((b : ℝ) ^ ((n + 1).choose 2) * ((b : ℝ) ^ (n ^ 2 + 2 * n))⁻¹) := hprod
    _ ≤ 2 * ((b : ℝ) ^ n)⁻¹ := by linarith
    _ ≤ 2 * ((2 : ℝ) ^ n)⁻¹ := by linarith
    _ = 2 / (2 : ℝ) ^ n := by rw [div_eq_mul_inv]

lemma pnat_sum_eq_L (t : ℤ) (ht : 2 ≤ t) :
    (∑' n : ℕ+, 1 / ((t : ℝ) ^ (n : ℕ) - 1)) = L t.toNat := by
  have htb : (t : ℝ) = (t.toNat : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg (by omega)).symm
  rw [htb]
  rw [← Equiv.pnatEquivNat.symm.tsum_eq]
  unfold L
  refine tsum_congr fun k => ?_
  rfl

lemma L_irrational {b : ℕ} (hb : 2 ≤ b) : Irrational (L b) := by
  rw [irrational_iff_ne_rational]
  intro p q hq hLq
  let n : ℕ := q.natAbs + 2
  have hn : 1 ≤ n := by omega
  let z : ℤ := Aint b n * p - Cint b n * q
  have hlin := linear_form_eq hb n
  have hq0 : (q : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hq
  have hz : (z : ℝ) = (q : ℝ) * ((qFact b n : ℝ) * Rtilde b n) := by
    dsimp [z]
    push_cast
    rw [hlin, hLq]
    field_simp
  have hprod_pos : 0 < (qFact b n : ℝ) * Rtilde b n :=
    mul_pos (by exact_mod_cast qFact_pos hb n) (Rtilde_pos hb hn)
  have hz_ne : z ≠ 0 := by
    intro hz0
    rw [hz0, Int.cast_zero] at hz
    rcases mul_eq_zero.mp hz.symm with h1 | h2
    · exact hq0 h1
    · exact hprod_pos.ne' h2
  have hz_ge : (1 : ℝ) ≤ |(z : ℝ)| := by
    exact_mod_cast Int.one_le_abs hz_ne
  have hz_abs : |(z : ℝ)| = (q.natAbs : ℝ) * ((qFact b n : ℝ) * Rtilde b n) := by
    rw [hz, abs_mul, abs_of_pos hprod_pos]
    congr 1
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
  have hbound : |(z : ℝ)| ≤ (q.natAbs : ℝ) * (2 / (2 : ℝ) ^ n) := by
    rw [hz_abs]
    exact mul_le_mul_of_nonneg_left (qFact_mul_Rtilde_le hb hn) (by positivity)
  have hlt1 : (q.natAbs : ℝ) * (2 / (2 : ℝ) ^ n) < 1 := by
    have hpow_nat : 2 * q.natAbs < 2 ^ n := by
      have h1 : q.natAbs < 2 ^ q.natAbs := Nat.lt_two_pow_self
      change 2 * q.natAbs < 2 ^ (q.natAbs + 2)
      rw [pow_add]
      omega
    have hpow_real : (q.natAbs : ℝ) * 2 < (2 : ℝ) ^ n := by
      exact_mod_cast (show q.natAbs * 2 < 2 ^ n by omega)
    rw [mul_div_assoc', div_lt_one (by positivity)]
    exact hpow_real
  linarith

end Erdos1049R1H1

theorem OMA.solution : OMA.R_Erdos1049_erdos_1049_R1.H1 := by
  intro t ht
  rw [Erdos1049R1H1.pnat_sum_eq_L t ht]
  exact Erdos1049R1H1.L_irrational (by omega)

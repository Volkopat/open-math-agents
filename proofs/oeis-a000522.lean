import OMAStatements.S_oeis_a000522

-- Problem: A000522: Total number of ordered k-tuples (k=0..n) of distinct elements from an n-element set: a(n) = Sum_{k=0..n} n!/k!.
-- Upstream: formal-conjectures statements/oeis-a000522.lean:0 (declaration OMA.S_oeis_a000522.main)
-- Credit: @Chihiro-g (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.S_oeis_a000522_Proof

open OMA.S_oeis_a000522 PowerSeries

/-- Linear functional sending X^i to i!. -/
private def L (p : Polynomial ℚ) : ℚ :=
  p.sum fun i c => c * (i.factorial : ℚ)

private lemma L_zero : L 0 = 0 := by
  simp [L]

private lemma L_add (p q : Polynomial ℚ) : L (p + q) = L p + L q := by
  unfold L
  rw [Polynomial.sum_add_index]
  · intro i; simp
  · intro i a b; ring

private lemma L_sub (p q : Polynomial ℚ) : L (p - q) = L p - L q := by
  have h := L_add (p - q) q
  rw [sub_add_cancel] at h
  linarith

private lemma L_C_mul (r : ℚ) (p : Polynomial ℚ) : L (Polynomial.C r * p) = r * L p := by
  unfold L
  rw [← Polynomial.smul_eq_C_mul, Polynomial.sum_smul_index']
  · simp only [smul_eq_mul, Polynomial.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · intro i; simp

private lemma L_monomial (i : ℕ) (c : ℚ) : L (Polynomial.monomial i c) = c * (i.factorial : ℚ) := by
  unfold L
  rw [Polynomial.sum_monomial_index]
  simp

private lemma L_X_pow (i : ℕ) : L (Polynomial.X ^ i) = (i.factorial : ℚ) := by
  have h : (Polynomial.X : Polynomial ℚ) ^ i = Polynomial.monomial i 1 := by
    rw [Polynomial.monomial_one_right_eq_X_pow]
  rw [h, L_monomial, one_mul]

private lemma L_sum {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℚ) :
    L (∑ i ∈ s, f i) = ∑ i ∈ s, L (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [L_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, L_add, ih, Finset.sum_insert ha]

/-- Coefficients of the monic Laguerre polynomial P_k. -/
private def lagCoeff (k j : ℕ) : ℚ :=
  if j ≤ k then
    (-1 : ℚ) ^ (k - j) * ((k.factorial : ℚ) ^ 2) /
      (((j.factorial : ℚ) ^ 2) * ((k - j).factorial : ℚ))
  else 0

/-- Monic Laguerre polynomial P_k of degree k. -/
private noncomputable def P (k : ℕ) : Polynomial ℚ :=
  ∑ j ∈ Finset.range (k + 1), Polynomial.monomial j (lagCoeff k j)

private lemma coeff_P (k j : ℕ) : (P k).coeff j = lagCoeff k j := by
  unfold P
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  by_cases h : j ≤ k
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hbj; simp [hbj]
    · intro hj; exfalso; exact hj (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
  · rw [Finset.sum_eq_zero]
    · simp [lagCoeff, h]
    · intro b hb
      have hb' : b ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
      have hne : b ≠ j := fun heq => h (heq ▸ hb')
      simp [hne]

private lemma P_zero : P 0 = 1 := by
  ext j
  rw [coeff_P]
  cases j with
  | zero => simp [lagCoeff]
  | succ j => simp [lagCoeff, Polynomial.coeff_one]

private lemma P_one : P 1 = Polynomial.X - 1 := by
  ext j
  rw [coeff_P]
  match j with
  | 0 => simp [lagCoeff, Polynomial.coeff_one, Polynomial.coeff_X]
  | 1 => simp [lagCoeff, Polynomial.coeff_one, Polynomial.coeff_X]
  | j + 2 => simp [lagCoeff, Polynomial.coeff_one, Polynomial.coeff_X]

private lemma fact_pos_q (n : ℕ) : (n.factorial : ℚ) ≠ 0 := by
  exact_mod_cast Nat.factorial_ne_zero n

/-- Coefficientwise 3-term recurrence for lagCoeff. -/
private lemma lagCoeff_rec (k j : ℕ) :
    (if j = 0 then (0 : ℚ) else lagCoeff (k + 1) (j - 1)) + lagCoeff (k + 1) j =
      lagCoeff (k + 2) j + 2 * ((k + 2 : ℕ) : ℚ) * lagCoeff (k + 1) j +
        ((k + 1 : ℕ) : ℚ) ^ 2 * lagCoeff k j := by
  match j with
  | 0 =>
    simp only [↓reduceIte, zero_add]
    unfold lagCoeff
    simp only [Nat.zero_le, ↓reduceIte, Nat.sub_zero, Nat.factorial_zero,
      Nat.cast_one, one_pow, one_mul]
    have h1 : ((k + 1).factorial : ℚ) = ((k + 1 : ℕ) : ℚ) * (k.factorial : ℚ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have h2 : ((k + 2).factorial : ℚ) = ((k + 2 : ℕ) : ℚ) * ((k + 1).factorial : ℚ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hk : (k.factorial : ℚ) ≠ 0 := fact_pos_q k
    have hk1 : ((k + 1).factorial : ℚ) ≠ 0 := fact_pos_q (k + 1)
    have hk2 : ((k + 2).factorial : ℚ) ≠ 0 := fact_pos_q (k + 2)
    have hpow1 : (-1 : ℚ) ^ (k + 1) = -((-1 : ℚ) ^ k) := by rw [pow_succ]; ring
    have hpow2 : (-1 : ℚ) ^ (k + 2) = (-1 : ℚ) ^ k := by rw [pow_succ, pow_succ]; ring
    rw [hpow2, hpow1]
    field_simp [hk, hk1, hk2]
    rw [h2, h1]
    push_cast
    ring
  | j + 1 =>
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
    by_cases hjk : j + 1 ≤ k
    · have h1 : j ≤ k + 1 := by omega
      have h2 : j + 1 ≤ k + 1 := by omega
      have h3 : j + 1 ≤ k + 2 := by omega
      simp only [lagCoeff, hjk, h1, h2, h3, ↓reduceIte]
      have hd1 : k + 1 - j = (k - (j + 1)) + 2 := by omega
      have hd2 : k + 1 - (j + 1) = (k - (j + 1)) + 1 := by omega
      have hd3 : k + 2 - (j + 1) = (k - (j + 1)) + 2 := by omega
      set d := k - (j + 1)
      have hkd : (k : ℚ) = (j : ℚ) + 1 + (d : ℚ) := by
        have : k = j + 1 + d := by omega
        exact_mod_cast this
      rw [hd1, hd2, hd3]
      have hf_k1 : ((k + 1).factorial : ℚ) = ((k + 1 : ℕ) : ℚ) * (k.factorial : ℚ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hf_k2 : ((k + 2).factorial : ℚ) = ((k + 2 : ℕ) : ℚ) * ((k + 1).factorial : ℚ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hf_j1 : ((j + 1).factorial : ℚ) = ((j + 1 : ℕ) : ℚ) * (j.factorial : ℚ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hf_d1 : ((d + 1).factorial : ℚ) = ((d + 1 : ℕ) : ℚ) * (d.factorial : ℚ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hf_d2 : ((d + 2).factorial : ℚ) = ((d + 2 : ℕ) : ℚ) * ((d + 1).factorial : ℚ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hp1 : (-1 : ℚ) ^ (d + 1) = -((-1 : ℚ) ^ d) := by rw [pow_succ]; ring
      have hp2 : (-1 : ℚ) ^ (d + 2) = (-1 : ℚ) ^ d := by rw [pow_succ, pow_succ]; ring
      rw [hp2, hp1]
      have hnz1 := fact_pos_q j
      have hnz2 := fact_pos_q (j + 1)
      have hnz3 := fact_pos_q d
      have hnz4 := fact_pos_q (d + 1)
      have hnz5 := fact_pos_q (d + 2)
      field_simp [hnz1, hnz2, hnz3, hnz4, hnz5]
      rw [hf_k2, hf_k1, hf_j1, hf_d2, hf_d1]
      push_cast
      rw [hkd]
      ring
    · by_cases hjk1 : j + 1 = k + 1
      · have hj_eq : j = k := by omega
        rw [hj_eq]
        have h1 : k ≤ k + 1 := by omega
        have h2 : k + 1 ≤ k + 1 := le_rfl
        have h3 : k + 1 ≤ k + 2 := by omega
        have h4 : ¬ k + 1 ≤ k := by omega
        simp only [lagCoeff, h1, h2, h3, h4, ↓reduceIte, Nat.sub_self, mul_zero, add_zero]
        have hs1 : k + 1 - k = 1 := by omega
        have hs2 : k + 2 - (k + 1) = 1 := by omega
        rw [hs1, hs2]
        have hf_k1 : ((k + 1).factorial : ℚ) = ((k + 1 : ℕ) : ℚ) * (k.factorial : ℚ) := by
          rw [Nat.factorial_succ]; push_cast; ring
        have hf_k2 : ((k + 2).factorial : ℚ) = ((k + 2 : ℕ) : ℚ) * ((k + 1).factorial : ℚ) := by
          rw [Nat.factorial_succ]; push_cast; ring
        have hnz1 := fact_pos_q k
        have hnz2 := fact_pos_q (k + 1)
        field_simp [hnz1, hnz2]
        rw [hf_k2, hf_k1]
        push_cast
        ring
      · by_cases hjk2 : j + 1 = k + 2
        · have hj_eq : j = k + 1 := by omega
          subst hj_eq
          have h1 : k + 1 ≤ k + 1 := le_rfl
          have h2 : ¬ k + 2 ≤ k + 1 := by omega
          have h3 : k + 2 ≤ k + 2 := le_rfl
          have h4 : ¬ k + 2 ≤ k := by omega
          simp only [lagCoeff, h1, h2, h3, h4, ↓reduceIte, Nat.sub_self, mul_zero, add_zero]
          have hnz1 := fact_pos_q (k + 1)
          have hnz2 := fact_pos_q (k + 2)
          field_simp [hnz1, hnz2]
        · have h1 : ¬ j ≤ k + 1 := by omega
          have h2 : ¬ j + 1 ≤ k + 1 := by omega
          have h3 : ¬ j + 1 ≤ k + 2 := by omega
          have h4 : ¬ j + 1 ≤ k := by omega
          simp [lagCoeff, h1, h2, h3, h4]

private lemma P_rec_zero :
    (Polynomial.X + 1) * P 0 = P 1 + Polynomial.C 2 * P 0 := by
  rw [P_zero, P_one, map_ofNat]
  ring

private lemma P_rec_succ (k : ℕ) :
    (Polynomial.X + 1) * P (k + 1) =
      P (k + 2) + Polynomial.C (2 * ((k + 2 : ℕ) : ℚ)) * P (k + 1) +
        Polynomial.C (((k + 1 : ℕ) : ℚ) ^ 2) * P k := by
  ext j
  have hlhs : ((Polynomial.X + 1) * P (k + 1)).coeff j =
      (if j = 0 then (0 : ℚ) else (P (k + 1)).coeff (j - 1)) + (P (k + 1)).coeff j := by
    rw [add_mul, one_mul, Polynomial.coeff_add]
    cases j with
    | zero => simp
    | succ j => simp [Polynomial.coeff_X_mul]
  rw [hlhs, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul, coeff_P, coeff_P, coeff_P, coeff_P]
  have hrec := lagCoeff_rec k j
  by_cases hj : j = 0
  · simp only [hj, ↓reduceIte, zero_add] at hrec ⊢
    exact hrec
  · simp only [hj, ↓reduceIte] at hrec ⊢
    exact hrec

/-- Polynomial coefficient identity for orthogonality:
    ∑_{j=0}^k (-1)^(k-j) C(k, j) C(j+m, m) = coeff m ((1+X)^m * X^k). -/
private lemma binom_orth_identity (k m : ℕ) :
    ∑ j ∈ Finset.range (k + 1),
      (-1 : ℚ) ^ (k - j) * (k.choose j : ℚ) * ((j + m).choose m : ℚ) =
    (((1 + Polynomial.X : Polynomial ℚ) ^ m) * Polynomial.X ^ k).coeff m := by
  have hXk : (Polynomial.X : Polynomial ℚ) ^ k =
      ∑ j ∈ Finset.range (k + 1),
        Polynomial.C ((-1 : ℚ) ^ (k - j) * (k.choose j : ℚ)) * (1 + Polynomial.X) ^ j := by
    have h1 : (Polynomial.X : Polynomial ℚ) = (1 + Polynomial.X) + (-1) := by ring
    conv_lhs => rw [h1, add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg, map_one,
      Polynomial.C_eq_natCast]
    ring
  have hprod : ((1 + Polynomial.X : Polynomial ℚ) ^ m) * Polynomial.X ^ k =
      ∑ j ∈ Finset.range (k + 1),
        Polynomial.C ((-1 : ℚ) ^ (k - j) * (k.choose j : ℚ)) * (1 + Polynomial.X) ^ (j + m) := by
    rw [hXk, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add]
    ring
  rw [hprod, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.coeff_C_mul, add_comm (1 : Polynomial ℚ) Polynomial.X,
    Polynomial.coeff_X_add_one_pow]

private lemma L_P_mul_X_pow (k m : ℕ) :
    L (P k * Polynomial.X ^ m) =
      (k.factorial : ℚ) * (m.factorial : ℚ) *
        (((1 + Polynomial.X : Polynomial ℚ) ^ m) * Polynomial.X ^ k).coeff m := by
  rw [← binom_orth_identity]
  unfold P
  rw [Finset.sum_mul, L_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hmon : Polynomial.monomial j (lagCoeff k j) * (Polynomial.X : Polynomial ℚ) ^ m =
      Polynomial.monomial (j + m) (lagCoeff k j) := by
    rw [← Polynomial.monomial_one_right_eq_X_pow, Polynomial.monomial_mul_monomial, mul_one]
  rw [hmon, L_monomial]
  simp only [lagCoeff, hjk, ↓reduceIte]
  have hch1 : (k.choose j : ℚ) * (j.factorial : ℚ) * ((k - j).factorial : ℚ) =
      (k.factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjk
  have hjm : m ≤ j + m := Nat.le_add_left m j
  have hch2 : ((j + m).choose m : ℚ) * (m.factorial : ℚ) * (j.factorial : ℚ) =
      ((j + m).factorial : ℚ) := by
    have h := Nat.choose_mul_factorial_mul_factorial hjm
    rw [Nat.add_sub_cancel] at h
    exact_mod_cast h
  have hjf := fact_pos_q j
  have hkjf := fact_pos_q (k - j)
  have hmf := fact_pos_q m
  have hch1' : (k.choose j : ℚ) = (k.factorial : ℚ) / ((j.factorial : ℚ) * ((k - j).factorial : ℚ)) := by
    rw [eq_div_iff (mul_ne_zero hjf hkjf)]
    linarith
  have hch2' : ((j + m).choose m : ℚ) = ((j + m).factorial : ℚ) / ((m.factorial : ℚ) * (j.factorial : ℚ)) := by
    rw [eq_div_iff (mul_ne_zero hmf hjf)]
    linarith
  rw [hch1', hch2']
  field_simp [hjf, hkjf, hmf]

private lemma L_P_mul_X_pow_of_lt {k m : ℕ} (h : m < k) :
    L (P k * Polynomial.X ^ m) = 0 := by
  rw [L_P_mul_X_pow, Polynomial.coeff_mul_X_pow', if_neg (not_le.mpr h), mul_zero]

private lemma L_P_mul_X_pow_self (k : ℕ) :
    L (P k * Polynomial.X ^ k) = (k.factorial : ℚ) ^ 2 := by
  rw [L_P_mul_X_pow, Polynomial.coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self,
    add_comm (1 : Polynomial ℚ) Polynomial.X, Polynomial.coeff_X_add_one_pow,
    Nat.choose_zero_right, Nat.cast_one, mul_one, sq]

private lemma L_X_add_one_pow_mul_P_of_lt {k n : ℕ} (h : n < k) :
    L ((Polynomial.X + 1) ^ n * P k) = 0 := by
  rw [add_pow, Finset.sum_mul, L_sum]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hterm : (Polynomial.X : Polynomial ℚ) ^ j * 1 ^ (n - j) * (n.choose j : Polynomial ℚ) * P k =
      Polynomial.C (n.choose j : ℚ) * (P k * Polynomial.X ^ j) := by
    rw [one_pow, mul_one, Polynomial.C_eq_natCast]
    ring
  rw [hterm, L_C_mul, L_P_mul_X_pow_of_lt (lt_of_le_of_lt hjn h), mul_zero]

private lemma L_X_add_one_pow_mul_P_self (k : ℕ) :
    L ((Polynomial.X + 1) ^ k * P k) = (k.factorial : ℚ) ^ 2 := by
  rw [add_pow, Finset.sum_mul, L_sum, Finset.sum_eq_single k]
  · have hterm : (Polynomial.X : Polynomial ℚ) ^ k * 1 ^ (k - k) * (k.choose k : Polynomial ℚ) * P k =
        P k * Polynomial.X ^ k := by
      simp [mul_comm]
    rw [hterm, L_P_mul_X_pow_self]
  · intro j hj hjk
    have hjlt : j < k := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hjk
    have hterm : (Polynomial.X : Polynomial ℚ) ^ j * 1 ^ (k - j) * (k.choose j : Polynomial ℚ) * P k =
        Polynomial.C (k.choose j : ℚ) * (P k * Polynomial.X ^ j) := by
      rw [one_pow, mul_one, Polynomial.C_eq_natCast]
      ring
    rw [hterm, L_C_mul, L_P_mul_X_pow_of_lt hjlt, mul_zero]
  · intro hk; exfalso; exact hk (Finset.mem_range.mpr (Nat.lt_succ_self k))

private lemma L_X_add_one_pow_eq_a (n : ℕ) :
    L ((Polynomial.X + 1) ^ n) = (a n : ℚ) := by
  rw [add_pow, L_sum]
  have h1 : ∀ j ∈ Finset.range (n + 1),
      L ((Polynomial.X : Polynomial ℚ) ^ j * 1 ^ (n - j) * (n.choose j : Polynomial ℚ)) =
        ((n.choose j * j.factorial : ℕ) : ℚ) := by
    intro j _
    have hterm : (Polynomial.X : Polynomial ℚ) ^ j * 1 ^ (n - j) * (n.choose j : Polynomial ℚ) =
        Polynomial.C (n.choose j : ℚ) * Polynomial.X ^ j := by
      rw [one_pow, mul_one, Polynomial.C_eq_natCast]
      ring
    rw [hterm, L_C_mul, L_X_pow]
    push_cast
    ring
  rw [Finset.sum_congr rfl h1]
  have hnat : ∑ j ∈ Finset.range (n + 1), n.choose j * j.factorial = a n := by
    unfold a
    rw [← Finset.sum_range_reflect (fun j => n.choose j * j.factorial) (n + 1)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hsub : n + 1 - 1 - k = n - k := by omega
    rw [hsub]
    have hmul := Nat.choose_mul_factorial_mul_factorial hkn
    rw [← Nat.choose_symm hkn] at hmul
    have hpos : 0 < k.factorial := Nat.factorial_pos k
    have hmul' : n.choose (n - k) * (n - k).factorial * k.factorial = n.factorial := by
      rw [mul_right_comm]; exact hmul
    exact Nat.eq_div_of_mul_eq_left (Nat.ne_of_gt hpos) hmul'
  rw [← Nat.cast_sum]
  exact_mod_cast hnat

/-- Shifted moment power series Htilde k = sum_n L((X+1)^(n+k) * P k) * X^n. -/
private noncomputable def Htilde (k : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => L ((Polynomial.X + 1) ^ (n + k) * P k)

private lemma constantCoeff_Htilde (k : ℕ) :
    PowerSeries.constantCoeff (Htilde k) = (k.factorial : ℚ) ^ 2 := by
  simp [Htilde, L_X_add_one_pow_mul_P_self]

private lemma isUnit_Htilde (k : ℕ) : IsUnit (Htilde k) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_Htilde]
  exact isUnit_iff_ne_zero.mpr (pow_ne_zero 2 (fact_pos_q k))

private lemma coeff_Htilde_zero (n : ℕ) :
    PowerSeries.coeff n (Htilde 0) = (a n : ℚ) := by
  simp [Htilde, P_zero, L_X_add_one_pow_eq_a]

private lemma coeff_one_sub_C_mul_X_mul (c : ℚ) (F : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n ((1 - PowerSeries.C c * PowerSeries.X) * F) =
      PowerSeries.coeff n F - if n = 0 then 0 else c * PowerSeries.coeff (n - 1) F := by
  rw [sub_mul, one_mul, map_sub]
  congr 1
  rw [mul_assoc, PowerSeries.coeff_C_mul]
  cases n with
  | zero => simp
  | succ n => simp

private lemma coeff_X_sq_mul (F : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.X ^ 2 * F) =
      if n < 2 then 0 else PowerSeries.coeff (n - 2) F := by
  match n with
  | 0 => simp [pow_two, mul_assoc]
  | 1 => simp [pow_two, mul_assoc]
  | n + 2 => simp [pow_two, mul_assoc]

private lemma Htilde_rec_zero :
    (1 - PowerSeries.C 2 * PowerSeries.X) * Htilde 0 - PowerSeries.X ^ 2 * Htilde 1 = 1 := by
  ext n
  rw [map_sub, coeff_one_sub_C_mul_X_mul, coeff_X_sq_mul]
  match n with
  | 0 =>
    simp [Htilde, P_zero, L_X_add_one_pow_eq_a, a]
  | 1 =>
    simp only [Nat.one_ne_zero, ↓reduceIte, Nat.sub_self, (by omega : 1 < 2), sub_zero,
      PowerSeries.coeff_one, Htilde, zero_add, PowerSeries.coeff_mk]
    have h1 : (Polynomial.X + 1 : Polynomial ℚ) ^ 1 * P 0 =
        P 1 + Polynomial.C 2 * P 0 := by
      rw [pow_one, P_rec_zero]
    rw [h1, L_add, L_C_mul]
    have hL1 : L (P 1) = 0 := by
      have h := L_X_add_one_pow_mul_P_of_lt (k := 1) (n := 0) (by omega)
      simpa using h
    rw [hL1, pow_zero, one_mul]
    ring
  | n + 2 =>
    have hsub1 : n + 2 - 1 = n + 1 := by omega
    have hsub2 : n + 2 - 2 = n := by omega
    simp only [Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, ↓reduceIte,
      hsub1, hsub2, not_lt_of_ge (Nat.le_add_left 2 n), PowerSeries.coeff_one,
      Htilde, add_zero, PowerSeries.coeff_mk]
    have hstep : (Polynomial.X + 1 : Polynomial ℚ) ^ (n + 2) * P 0 =
        (Polynomial.X + 1) ^ (n + 1) * P 1 +
          Polynomial.C 2 * ((Polynomial.X + 1) ^ (n + 1) * P 0) := by
      have hpow : (Polynomial.X + 1 : Polynomial ℚ) ^ (n + 2) * P 0 =
          (Polynomial.X + 1) ^ (n + 1) * ((Polynomial.X + 1) * P 0) := by
        rw [pow_succ]; ring
      rw [hpow, P_rec_zero]
      ring
    rw [hstep, L_add, L_C_mul]
    ring

private lemma Htilde_rec_succ (k : ℕ) :
    (1 - PowerSeries.C (2 * ((k + 2 : ℕ) : ℚ)) * PowerSeries.X) * Htilde (k + 1) -
      PowerSeries.X ^ 2 * Htilde (k + 2) =
        PowerSeries.C (((k + 1 : ℕ) : ℚ) ^ 2) * Htilde k := by
  ext n
  rw [map_sub, coeff_one_sub_C_mul_X_mul, coeff_X_sq_mul, PowerSeries.coeff_C_mul]
  match n with
  | 0 =>
    simp only [↓reduceIte, sub_zero, (by omega : 0 < 2), Htilde, zero_add, PowerSeries.coeff_mk,
      L_X_add_one_pow_mul_P_self]
    rw [Nat.factorial_succ]
    push_cast
    ring
  | 1 =>
    simp only [Nat.one_ne_zero, ↓reduceIte, Nat.sub_self, Nat.one_lt_ofNat, sub_zero,
      Htilde, zero_add, PowerSeries.coeff_mk]
    have hstep : (Polynomial.X + 1 : Polynomial ℚ) ^ (1 + (k + 1)) * P (k + 1) =
        (Polynomial.X + 1) ^ (k + 1) * P (k + 2) +
          Polynomial.C (2 * ((k + 2 : ℕ) : ℚ)) * ((Polynomial.X + 1) ^ (k + 1) * P (k + 1)) +
          Polynomial.C (((k + 1 : ℕ) : ℚ) ^ 2) * ((Polynomial.X + 1) ^ (1 + k) * P k) := by
      have h1 : 1 + (k + 1) = (k + 1) + 1 := by omega
      have h2 : 1 + k = k + 1 := by omega
      rw [h1, h2, pow_succ, mul_assoc, P_rec_succ]
      ring
    rw [hstep, L_add, L_add, L_C_mul, L_C_mul,
      L_X_add_one_pow_mul_P_of_lt (k := k + 2) (n := k + 1) (by omega)]
    ring
  | n + 2 =>
    simp only [Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, ↓reduceIte,
      not_lt_of_ge (Nat.le_add_left 2 n), Htilde, PowerSeries.coeff_mk]
    have hstep : (Polynomial.X + 1 : Polynomial ℚ) ^ (n + 2 + (k + 1)) * P (k + 1) =
        (Polynomial.X + 1) ^ (n + (k + 2)) * P (k + 2) +
          Polynomial.C (2 * ((k + 2 : ℕ) : ℚ)) *
            ((Polynomial.X + 1) ^ (n + 2 - 1 + (k + 1)) * P (k + 1)) +
          Polynomial.C (((k + 1 : ℕ) : ℚ) ^ 2) *
            ((Polynomial.X + 1) ^ (n + 2 + k) * P k) := by
      have e1 : n + 2 + (k + 1) = (n + k + 2) + 1 := by omega
      have e2 : n + (k + 2) = n + k + 2 := by omega
      have e3 : n + 2 - 1 + (k + 1) = n + k + 2 := by omega
      have e4 : n + 2 + k = n + k + 2 := by omega
      rw [e1, e2, e3, e4, pow_succ, mul_assoc, P_rec_succ]
      ring
    have e5 : n + 2 - 2 + (k + 2) = n + (k + 2) := by omega
    rw [e5, hstep, L_add, L_add, L_C_mul, L_C_mul]
    ring

/-- The Jacobi continued fraction tails S_k. -/
private noncomputable def S : ℕ → PowerSeries ℚ
  | 0 => Htilde 0
  | k + 1 =>
    PowerSeries.C ((((k + 1 : ℕ) : ℚ) ^ 2)⁻¹) * Htilde (k + 1) * Ring.inverse (Htilde k)

private lemma isUnit_S (k : ℕ) : IsUnit (S k) := by
  cases k with
  | zero => exact isUnit_Htilde 0
  | succ k =>
    unfold S
    have hc : IsUnit (PowerSeries.C ((((k + 1 : ℕ) : ℚ) ^ 2)⁻¹)) := by
      rw [PowerSeries.isUnit_iff_constantCoeff]
      simp only [PowerSeries.constantCoeff_C, isUnit_iff_ne_zero]
      exact inv_ne_zero (pow_ne_zero 2 (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)))
    have hinv : IsUnit (Ring.inverse (Htilde k)) :=
      isUnit_iff_exists_inv.mpr ⟨Htilde k, Ring.inverse_mul_cancel _ (isUnit_Htilde k)⟩
    exact (hc.mul (isUnit_Htilde (k + 1))).mul hinv

private lemma constantCoeff_S (k : ℕ) : PowerSeries.constantCoeff (S k) = 1 := by
  cases k with
  | zero => simp [S, constantCoeff_Htilde]
  | succ k =>
    unfold S
    have hinv : PowerSeries.constantCoeff (Ring.inverse (Htilde k)) =
        ((k.factorial : ℚ) ^ 2)⁻¹ := by
      have hmul := congrArg PowerSeries.constantCoeff (Ring.mul_inverse_cancel (Htilde k) (isUnit_Htilde k))
      rw [map_mul, map_one, constantCoeff_Htilde] at hmul
      have hne : (k.factorial : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 (fact_pos_q k)
      exact eq_inv_of_mul_eq_one_right hmul
    rw [map_mul, map_mul, PowerSeries.constantCoeff_C, constantCoeff_Htilde, hinv,
      Nat.factorial_succ]
    have h1 : ((k + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
    have h2 : (k.factorial : ℚ) ≠ 0 := fact_pos_q k
    push_cast
    field_simp [h1, h2]

/-- Core J-fraction identity: (1 - 2(k+1)X - (k+1)^2 X^2 S_{k+1}) * S_k = 1. -/
private lemma S_jfrac (k : ℕ) :
    (1 - PowerSeries.C (2 * ((k + 1 : ℕ) : ℚ)) * PowerSeries.X -
      PowerSeries.C (((k + 1 : ℕ) : ℚ) ^ 2) * PowerSeries.X ^ 2 * S (k + 1)) * S k = 1 := by
  cases k with
  | zero =>
    have hS1 : PowerSeries.C (((0 + 1 : ℕ) : ℚ) ^ 2) * PowerSeries.X ^ 2 * S 1 * S 0 =
        PowerSeries.X ^ 2 * Htilde 1 := by
      unfold S
      have hinv := Ring.inverse_mul_cancel (Htilde 0) (isUnit_Htilde 0)
      calc
        PowerSeries.C (((0 + 1 : ℕ) : ℚ) ^ 2) * PowerSeries.X ^ 2 *
            (PowerSeries.C ((((0 + 1 : ℕ) : ℚ) ^ 2)⁻¹) * Htilde 1 * Ring.inverse (Htilde 0)) *
            Htilde 0
            = PowerSeries.X ^ 2 * Htilde 1 * (Ring.inverse (Htilde 0) * Htilde 0) := by
              simp only [zero_add, Nat.cast_one, one_pow, inv_one, map_one, one_mul]
              ring
        _ = PowerSeries.X ^ 2 * Htilde 1 := by rw [hinv, mul_one]
    rw [sub_mul, hS1]
    simpa [S] using Htilde_rec_zero
  | succ k =>
    have hc_ne : ((k + 1 : ℕ) : ℚ) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k))
    have hc2_ne : ((k + 2 : ℕ) : ℚ) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero (k + 1)))
    have h1 : PowerSeries.C (((k + 2 : ℕ) : ℚ) ^ 2) *
        PowerSeries.C ((((k + 2 : ℕ) : ℚ) ^ 2)⁻¹) = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hc2_ne, map_one]
    have h2 : PowerSeries.C ((((k + 1 : ℕ) : ℚ) ^ 2)⁻¹) *
        PowerSeries.C (((k + 1 : ℕ) : ℚ) ^ 2) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hc_ne, map_one]
    have hinv_k1 : Ring.inverse (Htilde (k + 1)) * Htilde (k + 1) = 1 :=
      Ring.inverse_mul_cancel _ (isUnit_Htilde (k + 1))
    have hinv_k : Htilde k * Ring.inverse (Htilde k) = 1 :=
      Ring.mul_inverse_cancel _ (isUnit_Htilde k)
    have hterm2 :
        PowerSeries.C (((k + 2 : ℕ) : ℚ) ^ 2) * PowerSeries.X ^ 2 * S (k + 2) * S (k + 1) =
          PowerSeries.C ((((k + 1 : ℕ) : ℚ) ^ 2)⁻¹) *
            (PowerSeries.X ^ 2 * Htilde (k + 2)) * Ring.inverse (Htilde k) := by
      unfold S
      calc
        PowerSeries.C (((k + 2 : ℕ) : ℚ) ^ 2) * PowerSeries.X ^ 2 *
            (PowerSeries.C ((((k + 2 : ℕ) : ℚ) ^ 2)⁻¹) * Htilde (k + 2) *
              Ring.inverse (Htilde (k + 1))) *
            (PowerSeries.C ((((k + 1 : ℕ) : ℚ) ^ 2)⁻¹) * Htilde (k + 1) *
              Ring.inverse (Htilde k))
            = (PowerSeries.C (((k + 2 : ℕ) : ℚ) ^ 2) *
                PowerSeries.C ((((k + 2 : ℕ) : ℚ) ^ 2)⁻¹)) *
              (Ring.inverse (Htilde (k + 1)) * Htilde (k + 1)) *
              (PowerSeries.C ((((k + 1 : ℕ) : ℚ) ^ 2)⁻¹) *
                (PowerSeries.X ^ 2 * Htilde (k + 2)) * Ring.inverse (Htilde k)) := by ring
        _ = PowerSeries.C ((((k + 1 : ℕ) : ℚ) ^ 2)⁻¹) *
              (PowerSeries.X ^ 2 * Htilde (k + 2)) * Ring.inverse (Htilde k) := by
            rw [h1, hinv_k1, one_mul, one_mul]
    rw [sub_mul, hterm2]
    have hterm1 :
        (1 - PowerSeries.C (2 * ((k + 2 : ℕ) : ℚ)) * PowerSeries.X) * S (k + 1) =
          PowerSeries.C ((((k + 1 : ℕ) : ℚ) ^ 2)⁻¹) *
            ((1 - PowerSeries.C (2 * ((k + 2 : ℕ) : ℚ)) * PowerSeries.X) * Htilde (k + 1)) *
            Ring.inverse (Htilde k) := by
      unfold S
      ring
    rw [hterm1]
    calc
      PowerSeries.C ((((k + 1 : ℕ) : ℚ) ^ 2)⁻¹) *
          ((1 - PowerSeries.C (2 * ((k + 2 : ℕ) : ℚ)) * PowerSeries.X) * Htilde (k + 1)) *
          Ring.inverse (Htilde k) -
        PowerSeries.C ((((k + 1 : ℕ) : ℚ) ^ 2)⁻¹) *
          (PowerSeries.X ^ 2 * Htilde (k + 2)) * Ring.inverse (Htilde k)
          = PowerSeries.C ((((k + 1 : ℕ) : ℚ) ^ 2)⁻¹) *
              ((1 - PowerSeries.C (2 * ((k + 2 : ℕ) : ℚ)) * PowerSeries.X) * Htilde (k + 1) -
                PowerSeries.X ^ 2 * Htilde (k + 2)) *
              Ring.inverse (Htilde k) := by ring
      _ = PowerSeries.C ((((k + 1 : ℕ) : ℚ) ^ 2)⁻¹) *
            (PowerSeries.C (((k + 1 : ℕ) : ℚ) ^ 2) * Htilde k) *
            Ring.inverse (Htilde k) := by rw [Htilde_rec_succ]
      _ = (PowerSeries.C ((((k + 1 : ℕ) : ℚ) ^ 2)⁻¹) *
            PowerSeries.C (((k + 1 : ℕ) : ℚ) ^ 2)) *
            (Htilde k * Ring.inverse (Htilde k)) := by ring
      _ = 1 := by rw [h2, hinv_k, one_mul]

/-- The exact formal power series T_k = (1 - 2(k+1)X) * S_k. -/
private noncomputable def T (k : ℕ) : PowerSeries ℚ :=
  (1 - PowerSeries.C (2 * ((k + 1 : ℕ) : ℚ)) * PowerSeries.X) * S k

private lemma isUnit_lin (c : ℚ) :
    IsUnit (1 - PowerSeries.C c * PowerSeries.X) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp

private lemma constantCoeff_T (k : ℕ) : PowerSeries.constantCoeff (T k) = 1 := by
  simp [T, constantCoeff_S]

private lemma isUnit_T (k : ℕ) : IsUnit (T k) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_T]
  exact isUnit_one

/-- Exact fixed-point equation for T matching the recurrence of cfT. -/
private lemma T_rec (k : ℕ) :
    let x := (PowerSeries.X : PowerSeries ℚ)
    let c1 := PowerSeries.C (((k + 1 : ℕ) : ℚ) ^ 2) * x ^ 2
    let lin1 := 1 - PowerSeries.C (2 * ((k + 1 : ℕ) : ℚ)) * x
    let lin2 := 1 - PowerSeries.C (2 * ((k + 2 : ℕ) : ℚ)) * x
    T k = 1 - c1 * Ring.inverse (c1 - lin1 * lin2 * Ring.inverse (T (k + 1))) := by
  dsimp only
  set x := (PowerSeries.X : PowerSeries ℚ)
  set c1 := PowerSeries.C (((k + 1 : ℕ) : ℚ) ^ 2) * x ^ 2
  set lin1 := 1 - PowerSeries.C (2 * ((k + 1 : ℕ) : ℚ)) * x
  set lin2 := 1 - PowerSeries.C (2 * ((k + 2 : ℕ) : ℚ)) * x
  set D := c1 - lin1 * lin2 * Ring.inverse (T (k + 1))
  have hD_unit : IsUnit D := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have hinvT : PowerSeries.constantCoeff (Ring.inverse (T (k + 1))) = 1 := by
      have hm := congrArg PowerSeries.constantCoeff (Ring.mul_inverse_cancel (T (k + 1)) (isUnit_T (k + 1)))
      rw [map_mul, map_one, constantCoeff_T, one_mul] at hm
      exact hm
    simp [D, c1, lin1, lin2, x, hinvT]
  have hlin1_u : IsUnit lin1 := isUnit_lin _
  have hlin2_u : IsUnit lin2 := isUnit_lin _
  have hT_u : IsUnit (T (k + 1)) := isUnit_T (k + 1)
  have hmul : (T k - (1 - c1 * Ring.inverse D)) * (D * T (k + 1)) = 0 := by
    have hD_inv : Ring.inverse D * D = 1 := Ring.inverse_mul_cancel D hD_unit
    have hT_inv : Ring.inverse (T (k + 1)) * T (k + 1) = 1 := Ring.inverse_mul_cancel _ hT_u
    have hDT : D * T (k + 1) = c1 * T (k + 1) - lin1 * lin2 := by
      calc
        D * T (k + 1) = c1 * T (k + 1) - lin1 * lin2 * (Ring.inverse (T (k + 1)) * T (k + 1)) := by
          simp only [D]; ring
        _ = c1 * T (k + 1) - lin1 * lin2 := by rw [hT_inv, mul_one]
    have hDT_eq : T k * (D * T (k + 1)) = -lin1 * lin2 := by
      rw [hDT]
      have hj := S_jfrac k
      have hj' : (lin1 - c1 * S (k + 1)) * S k = 1 := hj
      have hTk : T k = lin1 * S k := rfl
      have hTk1 : T (k + 1) = lin2 * S (k + 1) := rfl
      rw [hTk, hTk1]
      calc
        lin1 * S k * (c1 * (lin2 * S (k + 1)) - lin1 * lin2)
            = -(lin1 * lin2) * ((lin1 - c1 * S (k + 1)) * S k) := by ring
        _ = -(lin1 * lin2) * 1 := by rw [hj']
        _ = -lin1 * lin2 := by ring
    calc
      (T k - (1 - c1 * Ring.inverse D)) * (D * T (k + 1))
          = T k * (D * T (k + 1)) - D * T (k + 1) + c1 * (Ring.inverse D * D) * T (k + 1) := by ring
      _ = -lin1 * lin2 - (c1 * T (k + 1) - lin1 * lin2) + c1 * 1 * T (k + 1) := by
          rw [hDT_eq, hDT, hD_inv]
      _ = 0 := by ring
  have hunit : IsUnit (D * T (k + 1)) := hD_unit.mul hT_u
  have hzero : T k - (1 - c1 * Ring.inverse D) = 0 := by
    have := congrArg (· * Ring.inverse (D * T (k + 1))) hmul
    rw [mul_assoc, Ring.mul_inverse_cancel _ hunit, mul_one, zero_mul] at this
    exact this
  exact sub_eq_zero.mp hzero

/-- Coefficientwise agreement below degree d. -/
private def Agree (d : ℕ) (f g : PowerSeries ℚ) : Prop :=
  ∀ j < d, PowerSeries.coeff j f = PowerSeries.coeff j g

private lemma agree_zero_iff (d : ℕ) (f g : PowerSeries ℚ) :
    Agree d f g ↔ ∀ j < d, PowerSeries.coeff j (f - g) = 0 := by
  constructor
  · intro h j hj; rw [map_sub, h j hj, sub_self]
  · intro h j hj; exact sub_eq_zero.mp (by simpa [map_sub] using h j hj)

private lemma agree_mul_zero_left {d : ℕ} {u v : PowerSeries ℚ}
    (hu : ∀ j < d, PowerSeries.coeff j u = 0) :
    ∀ j < d, PowerSeries.coeff j (u * v) = 0 := by
  intro j hj
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp1 : p.1 < d := lt_of_le_of_lt (Finset.HasAntidiagonal.antidiagonal.fst_le hp) hj
  rw [hu p.1 hp1, zero_mul]

private lemma agree_sub {d : ℕ} {f1 f2 g1 g2 : PowerSeries ℚ}
    (hf : Agree d f1 f2) (hg : Agree d g1 g2) : Agree d (f1 - g1) (f2 - g2) := by
  intro j hj
  rw [map_sub, map_sub, hf j hj, hg j hj]

private lemma agree_mul {d : ℕ} {f1 f2 g1 g2 : PowerSeries ℚ}
    (hf : Agree d f1 f2) (hg : Agree d g1 g2) : Agree d (f1 * g1) (f2 * g2) := by
  intro j hj
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp1 : p.1 < d := lt_of_le_of_lt (Finset.HasAntidiagonal.antidiagonal.fst_le hp) hj
  have hp2 : p.2 < d := lt_of_le_of_lt (Finset.HasAntidiagonal.antidiagonal.snd_le hp) hj
  rw [hf p.1 hp1, hg p.2 hp2]

private lemma agree_inv {d : ℕ} {f g : PowerSeries ℚ}
    (hf : IsUnit f) (hg : IsUnit g) (h : Agree d f g) :
    Agree d (Ring.inverse f) (Ring.inverse g) := by
  rw [agree_zero_iff]
  have heq : Ring.inverse f - Ring.inverse g = (g - f) * (Ring.inverse f * Ring.inverse g) := by
    have h1 := Ring.inverse_mul_cancel f hf
    have h2 := Ring.mul_inverse_cancel g hg
    symm
    calc
      (g - f) * (Ring.inverse f * Ring.inverse g)
          = Ring.inverse f * (g * Ring.inverse g) - (Ring.inverse f * f) * Ring.inverse g := by ring
      _ = Ring.inverse f * 1 - 1 * Ring.inverse g := by rw [h2, h1]
      _ = Ring.inverse f - Ring.inverse g := by ring
  rw [heq]
  apply agree_mul_zero_left
  intro j hj
  rw [map_sub, h j hj, sub_self]

private lemma agree_mul_C_X_sq {d : ℕ} (c : ℚ) {f g : PowerSeries ℚ} (h : Agree d f g) :
    Agree (d + 2) (PowerSeries.C c * PowerSeries.X ^ 2 * f)
      (PowerSeries.C c * PowerSeries.X ^ 2 * g) := by
  intro j hj
  rw [mul_assoc, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    coeff_X_sq_mul, coeff_X_sq_mul]
  split_ifs with hlt
  · rfl
  · congr 1
    exact h (j - 2) (by omega)

private lemma constantCoeff_cfT (k m : ℕ) : PowerSeries.constantCoeff (cfT k m) = 1 := by
  induction m generalizing k with
  | zero => simp [cfT]
  | succ m ih =>
    simp [cfT]

private lemma isUnit_cfT (k m : ℕ) : IsUnit (cfT k m) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_cfT]
  exact isUnit_one

private lemma cfT_agree_T (m k : ℕ) : Agree (2 * m) (cfT k m) (T k) := by
  induction m generalizing k with
  | zero =>
    intro j hj
    omega
  | succ m ih =>
    have hih : Agree (2 * m) (cfT (k + 1) m) (T (k + 1)) := ih (k + 1)
    set x := (PowerSeries.X : PowerSeries ℚ)
    set c1 := PowerSeries.C (((k + 1 : ℕ) : ℚ) ^ 2) * x ^ 2
    set lin1 := 1 - PowerSeries.C (2 * ((k + 1 : ℕ) : ℚ)) * x
    set lin2 := 1 - PowerSeries.C (2 * ((k + 2 : ℕ) : ℚ)) * x
    set D1 := c1 - lin1 * lin2 * Ring.inverse (cfT (k + 1) m)
    set D2 := c1 - lin1 * lin2 * Ring.inverse (T (k + 1))
    have hD1_u : IsUnit D1 := by
      rw [PowerSeries.isUnit_iff_constantCoeff]
      have hinv : PowerSeries.constantCoeff (Ring.inverse (cfT (k + 1) m)) = 1 := by
        have hm := congrArg PowerSeries.constantCoeff
          (Ring.mul_inverse_cancel (cfT (k + 1) m) (isUnit_cfT (k + 1) m))
        rw [map_mul, map_one, constantCoeff_cfT, one_mul] at hm
        exact hm
      simp [D1, c1, lin1, lin2, x, hinv]
    have hD2_u : IsUnit D2 := by
      rw [PowerSeries.isUnit_iff_constantCoeff]
      have hinv : PowerSeries.constantCoeff (Ring.inverse (T (k + 1))) = 1 := by
        have hm := congrArg PowerSeries.constantCoeff
          (Ring.mul_inverse_cancel (T (k + 1)) (isUnit_T (k + 1)))
        rw [map_mul, map_one, constantCoeff_T, one_mul] at hm
        exact hm
      simp [D2, c1, lin1, lin2, x, hinv]
    have hinv_ag : Agree (2 * m) (Ring.inverse (cfT (k + 1) m)) (Ring.inverse (T (k + 1))) :=
      agree_inv (isUnit_cfT (k + 1) m) (isUnit_T (k + 1)) hih
    have hD_ag : Agree (2 * m) D1 D2 :=
      agree_sub (fun _ _ => rfl) (agree_mul (fun _ _ => rfl) hinv_ag)
    have hDinv_ag : Agree (2 * m) (Ring.inverse D1) (Ring.inverse D2) :=
      agree_inv hD1_u hD2_u hD_ag
    have hshift : Agree (2 * m + 2) (c1 * Ring.inverse D1) (c1 * Ring.inverse D2) :=
      agree_mul_C_X_sq (((k + 1 : ℕ) : ℚ) ^ 2) hDinv_ag
    have hfinal : Agree (2 * (m + 1)) (1 - c1 * Ring.inverse D1) (1 - c1 * Ring.inverse D2) := by
      simpa [Nat.mul_add] using agree_sub (fun _ _ => rfl) hshift
    rw [T_rec k]
    exact hfinal

end OMA.S_oeis_a000522_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a000522.main := by
  intro n
  refine ⟨n + 1, fun m hm => ?_⟩
  have hag : OMA.S_oeis_a000522_Proof.Agree (2 * m)
      (OMA.S_oeis_a000522.cfT 0 m) (OMA.S_oeis_a000522_Proof.T 0) :=
    OMA.S_oeis_a000522_Proof.cfT_agree_T m 0
  have hmul : OMA.S_oeis_a000522_Proof.Agree (2 * m)
      (OMA.S_oeis_a000522.cfT 0 m * Ring.inverse (1 - PowerSeries.C 2 * PowerSeries.X))
      (OMA.S_oeis_a000522_Proof.T 0 * Ring.inverse (1 - PowerSeries.C 2 * PowerSeries.X)) :=
    OMA.S_oeis_a000522_Proof.agree_mul hag (fun _ _ => rfl)
  have hlt : n < 2 * m := by omega
  rw [hmul n hlt]
  have hT0 : OMA.S_oeis_a000522_Proof.T 0 *
      Ring.inverse (1 - PowerSeries.C 2 * PowerSeries.X) =
      OMA.S_oeis_a000522_Proof.Htilde 0 := by
    have hinv := Ring.mul_inverse_cancel (1 - PowerSeries.C 2 * PowerSeries.X)
      (OMA.S_oeis_a000522_Proof.isUnit_lin 2)
    calc
      OMA.S_oeis_a000522_Proof.T 0 * Ring.inverse (1 - PowerSeries.C 2 * PowerSeries.X)
          = (1 - PowerSeries.C 2 * PowerSeries.X) * OMA.S_oeis_a000522_Proof.Htilde 0 *
              Ring.inverse (1 - PowerSeries.C 2 * PowerSeries.X) := by
            simp [OMA.S_oeis_a000522_Proof.T, OMA.S_oeis_a000522_Proof.S]
      _ = ((1 - PowerSeries.C 2 * PowerSeries.X) *
            Ring.inverse (1 - PowerSeries.C 2 * PowerSeries.X)) *
            OMA.S_oeis_a000522_Proof.Htilde 0 := by ring
      _ = OMA.S_oeis_a000522_Proof.Htilde 0 := by rw [hinv, one_mul]
  rw [hT0, OMA.S_oeis_a000522_Proof.coeff_Htilde_zero]

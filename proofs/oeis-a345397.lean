import OMAStatements.S_oeis_a345397

/-!
Proof of OEIS A345397: for every n >= 1, there exists k > 0 such that k, k^2, ..., k^n
are all digitally balanced in base 2.
-/

namespace OMA.S_oeis_a345397.Proof

open scoped BigOperators

/-! ### Section 1: Binary digits and popcount lemmas -/

private def c1 (m : ℕ) : ℕ := (Nat.digits 2 m).count 1

private def c0 (m : ℕ) : ℕ := (Nat.digits 2 m).count 0

private lemma count_zero_add_count_one_of_lt_two :
    ∀ l : List ℕ, (∀ d ∈ l, d < 2) → l.count 0 + l.count 1 = l.length
  | [], _ => by simp
  | a :: l, h => by
    have ha : a < 2 := h a (by simp)
    have hl : ∀ d ∈ l, d < 2 := fun d hd => h d (by simp [hd])
    have ih := count_zero_add_count_one_of_lt_two l hl
    rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;>
      simp [List.count_cons, ih] <;> omega

private lemma c0_add_c1 (m : ℕ) : c0 m + c1 m = (Nat.digits 2 m).length := by
  apply count_zero_add_count_one_of_lt_two
  intro d hd
  exact Nat.digits_lt_base (by norm_num) hd

private lemma isDigitallyBalanced_iff (m : ℕ) :
    OMA.S_oeis_a345397.IsDigitallyBalanced m ↔ 0 < m ∧ 2 * c1 m = (Nat.digits 2 m).length := by
  unfold OMA.S_oeis_a345397.IsDigitallyBalanced
  have h := c0_add_c1 m
  change (0 < m ∧ c0 m = c1 m) ↔ 0 < m ∧ 2 * c1 m = (Nat.digits 2 m).length
  omega

private lemma digits_two_bit (q b : ℕ) (hb : b < 2) (hq : 0 < q ∨ 0 < b) :
    Nat.digits 2 (b + 2 * q) = b :: Nat.digits 2 q := by
  have hne : b + 2 * q ≠ 0 := by omega
  rw [Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero hne)]
  have hmod : (b + 2 * q) % 2 = b := by omega
  have hdiv : (b + 2 * q) / 2 = q := by omega
  rw [hmod, hdiv]

private lemma c1_two_mul (q : ℕ) : c1 (2 * q) = c1 q := by
  by_cases hq : q = 0
  · subst hq; simp [c1]
  · unfold c1
    have h := digits_two_bit q 0 (by norm_num) (Or.inl (Nat.pos_of_ne_zero hq))
    simpa [Nat.zero_add] using congrArg (fun l => l.count 1) h

private lemma c1_two_mul_add_one (q : ℕ) : c1 (2 * q + 1) = c1 q + 1 := by
  unfold c1
  have h := digits_two_bit q 1 (by norm_num) (Or.inr (by norm_num))
  rw [show 2 * q + 1 = 1 + 2 * q by omega, h]
  simp [List.count_cons]

private lemma c1_mul_pow_two (a e : ℕ) : c1 (a * 2 ^ e) = c1 a := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, ← mul_assoc, mul_comm (a * 2 ^ e) 2, c1_two_mul, ih]

private lemma c1_mul_pow_two_sub_one (a e : ℕ) (ha : 1 ≤ a) :
    c1 (a * 2 ^ e - 1) = c1 (a - 1) + e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have h1 : 1 ≤ a * 2 ^ e := Nat.mul_pos ha (Nat.pos_of_ne_zero (by positivity))
    have hrew : a * 2 ^ (e + 1) - 1 = 2 * (a * 2 ^ e - 1) + 1 := by
      have : a * 2 ^ (e + 1) = 2 * (a * 2 ^ e) := by ring
      omega
    rw [hrew, c1_two_mul_add_one, ih]
    omega

private lemma digits_add_mul_pow_two_c1_len (L : ℕ) :
    ∀ a b : ℕ, a < 2 ^ L → 0 < b →
      c1 (a + b * 2 ^ L) = c1 a + c1 b ∧
      (Nat.digits 2 (a + b * 2 ^ L)).length = L + (Nat.digits 2 b).length := by
  induction L with
  | zero =>
    intro a b ha _
    have ha0 : a = 0 := by omega
    subst ha0
    simp [c1]
  | succ L ih =>
    intro a b ha hb
    have hq : a / 2 < 2 ^ L := by
      rw [pow_succ] at ha; omega
    have hrem : a % 2 < 2 := Nat.mod_lt a (by norm_num)
    have hdecomp : a + b * 2 ^ (L + 1) = a % 2 + 2 * (a / 2 + b * 2 ^ L) := by
      have : b * 2 ^ (L + 1) = 2 * (b * 2 ^ L) := by ring
      omega
    have hpos : 0 < a / 2 + b * 2 ^ L := by
      have : 0 < b * 2 ^ L := Nat.mul_pos hb (by positivity)
      omega
    have hdig := digits_two_bit (a / 2 + b * 2 ^ L) (a % 2) hrem (Or.inl hpos)
    have ⟨ih1, ih2⟩ := ih (a / 2) b hq hb
    constructor
    · unfold c1
      rw [hdecomp, hdig]
      rcases (by omega : a % 2 = 0 ∨ a % 2 = 1) with hm | hm
      · have ha_eq : a = 2 * (a / 2) := by omega
        have hc1a : c1 a = c1 (a / 2) := by conv_lhs => rw [ha_eq]; exact c1_two_mul (a / 2)
        simp only [hm, List.count_cons, beq_iff_eq, zero_ne_one, ↓reduceIte, add_zero]
        change c1 (a / 2 + b * 2 ^ L) = c1 a + c1 b
        rw [ih1, hc1a]
      · have ha_eq : a = 2 * (a / 2) + 1 := by omega
        have hc1a : c1 a = c1 (a / 2) + 1 := by conv_lhs => rw [ha_eq]; exact c1_two_mul_add_one (a / 2)
        simp only [hm, List.count_cons, beq_self_eq_true, ↓reduceIte]
        change c1 (a / 2 + b * 2 ^ L) + 1 = c1 a + c1 b
        rw [ih1, hc1a]; omega
    · rw [hdecomp, hdig, List.length_cons, ih2]
      omega

private lemma c1_add_mul_pow_two (a b L : ℕ) (ha : a < 2 ^ L) :
    c1 (a + b * 2 ^ L) = c1 a + c1 b := by
  by_cases hb : b = 0
  · subst hb; simp [c1]
  · exact (digits_add_mul_pow_two_c1_len L a b ha (Nat.pos_of_ne_zero hb)).1

private lemma len_add_mul_pow_two (a b L : ℕ) (ha : a < 2 ^ L) (hb : 0 < b) :
    (Nat.digits 2 (a + b * 2 ^ L)).length = L + (Nat.digits 2 b).length :=
  (digits_add_mul_pow_two_c1_len L a b ha hb).2

private lemma c1_pow_two_sub (L : ℕ) :
    ∀ a : ℕ, 1 ≤ a → a ≤ 2 ^ L → c1 (2 ^ L - a) + c1 (a - 1) = L := by
  induction L with
  | zero =>
    intro a ha1 ha2
    have : a = 1 := by omega
    subst this; simp [c1]
  | succ L ih =>
    intro a ha1 ha2
    rcases Nat.even_or_odd' a with ⟨q, rfl | rfl⟩
    · have hq1 : 1 ≤ q := by omega
      have hq2 : q ≤ 2 ^ L := by rw [pow_succ] at ha2; omega
      have hsub : 2 ^ (L + 1) - 2 * q = 2 * (2 ^ L - q) := by rw [pow_succ]; omega
      have hsub1 : 2 * q - 1 = 2 * (q - 1) + 1 := by omega
      rw [hsub, hsub1, c1_two_mul, c1_two_mul_add_one]
      have := ih q hq1 hq2
      omega
    · have hq1 : 1 ≤ q + 1 := by omega
      have hq2 : q + 1 ≤ 2 ^ L := by rw [pow_succ] at ha2; omega
      have hsub : 2 ^ (L + 1) - (2 * q + 1) = 2 * (2 ^ L - (q + 1)) + 1 := by
        rw [pow_succ]; omega
      have hsub1 : 2 * q + 1 - 1 = 2 * q := by omega
      rw [hsub, hsub1, c1_two_mul_add_one, c1_two_mul]
      have := ih (q + 1) hq1 hq2
      simp only [Nat.add_sub_cancel] at this
      omega

private lemma digits_len_of_bounds (m k : ℕ) (hlo : 2 ^ k ≤ m) (hhi : m < 2 ^ (k + 1)) :
    (Nat.digits 2 m).length = k + 1 := by
  have hm : m ≠ 0 := by
    have : 0 < 2 ^ k := by positivity
    omega
  rw [Nat.digits_len 2 m (by norm_num) hm]
  have hlog : Nat.log 2 m = k := by
    apply (Nat.log_eq_iff (Or.inr ⟨by norm_num, hm⟩)).mpr
    exact ⟨hlo, hhi⟩
  rw [hlog]

/-! ### Section 1b: Alternating block decomposition -/

private def altBlockVal (d L top : ℕ) (A : ℕ → ℕ) : ℕ :=
  A 0 +
  (∑ t ∈ Finset.range (d - 1),
    ((2 ^ L - A (2 * t + 1)) * 2 ^ ((2 * t + 1) * L) +
     (A (2 * t + 2) - 1) * 2 ^ ((2 * t + 2) * L))) +
  (2 ^ (L + top) - A (2 * d - 1)) * 2 ^ ((2 * d - 1) * L)

private lemma altBlock_lower_spec (m L : ℕ) (A : ℕ → ℕ)
    (hpos : ∀ s ≤ 2 * m, 1 ≤ A s) (hlt : ∀ s ≤ 2 * m, A s < 2 ^ L) :
    let val := A 0 + ∑ t ∈ Finset.range m,
      ((2 ^ L - A (2 * t + 1)) * 2 ^ ((2 * t + 1) * L) +
       (A (2 * t + 2) - 1) * 2 ^ ((2 * t + 2) * L))
    val < 2 ^ ((2 * m + 1) * L) ∧
    (c1 val : ℤ) =
      (m : ℤ) * L + c1 (A 0) +
      (∑ t ∈ Finset.range m, (c1 (A (2 * t + 2) - 1) : ℤ)) -
      (∑ t ∈ Finset.range m, (c1 (A (2 * t + 1) - 1) : ℤ)) := by
  induction m with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, add_zero, zero_mul, Nat.zero_add, one_mul,
      Nat.cast_zero, sub_zero]
    exact ⟨by simpa using hlt 0 (by omega), by simp⟩
  | succ m ih =>
    have ⟨ih_lt, ih_c1⟩ := ih (fun s hs => hpos s (by omega)) (fun s hs => hlt s (by omega))
    set prev := A 0 + ∑ t ∈ Finset.range m,
      ((2 ^ L - A (2 * t + 1)) * 2 ^ ((2 * t + 1) * L) +
       (A (2 * t + 2) - 1) * 2 ^ ((2 * t + 2) * L))
    have hstep :
        A 0 + ∑ t ∈ Finset.range (m + 1),
          ((2 ^ L - A (2 * t + 1)) * 2 ^ ((2 * t + 1) * L) +
           (A (2 * t + 2) - 1) * 2 ^ ((2 * t + 2) * L)) =
        (prev + (2 ^ L - A (2 * m + 1)) * 2 ^ ((2 * m + 1) * L)) +
          (A (2 * m + 2) - 1) * 2 ^ ((2 * m + 2) * L) := by
      rw [Finset.sum_range_succ]; ring
    rw [hstep]
    have hA1_pos : 1 ≤ A (2 * m + 1) := hpos (2 * m + 1) (by omega)
    have hA1_lt : A (2 * m + 1) < 2 ^ L := hlt (2 * m + 1) (by omega)
    have hA2_lt : A (2 * m + 2) < 2 ^ L := hlt (2 * m + 2) (by omega)
    have hmid_lt : prev + (2 ^ L - A (2 * m + 1)) * 2 ^ ((2 * m + 1) * L) <
        2 ^ ((2 * m + 2) * L) := by
      have h1 : 2 ^ L - A (2 * m + 1) ≤ 2 ^ L - 1 := by omega
      have h2 : (2 ^ L - A (2 * m + 1)) * 2 ^ ((2 * m + 1) * L) ≤
          (2 ^ L - 1) * 2 ^ ((2 * m + 1) * L) := Nat.mul_le_mul_right _ h1
      have h3 : (2 ^ L - 1) * 2 ^ ((2 * m + 1) * L) + 2 ^ ((2 * m + 1) * L) =
          2 ^ ((2 * m + 2) * L) := by
        have hposL : 1 ≤ 2 ^ L := Nat.one_le_pow L 2 (by norm_num)
        rw [show (2 * m + 2) * L = L + (2 * m + 1) * L by ring, pow_add]
        zify [hposL]; ring
      omega
    have hfull_lt :
        (prev + (2 ^ L - A (2 * m + 1)) * 2 ^ ((2 * m + 1) * L)) +
          (A (2 * m + 2) - 1) * 2 ^ ((2 * m + 2) * L) <
        2 ^ ((2 * (m + 1) + 1) * L) := by
      have h1 : A (2 * m + 2) - 1 ≤ 2 ^ L - 1 := by omega
      have h2 : (A (2 * m + 2) - 1) * 2 ^ ((2 * m + 2) * L) ≤
          (2 ^ L - 1) * 2 ^ ((2 * m + 2) * L) := Nat.mul_le_mul_right _ h1
      have h3 : (2 ^ L - 1) * 2 ^ ((2 * m + 2) * L) + 2 ^ ((2 * m + 2) * L) =
          2 ^ ((2 * (m + 1) + 1) * L) := by
        have hposL : 1 ≤ 2 ^ L := Nat.one_le_pow L 2 (by norm_num)
        rw [show (2 * (m + 1) + 1) * L = L + (2 * m + 2) * L by ring, pow_add]
        zify [hposL]; ring
      omega
    refine ⟨hfull_lt, ?_⟩
    rw [c1_add_mul_pow_two _ _ _ hmid_lt, c1_add_mul_pow_two _ _ _ ih_lt]
    have hsub := c1_pow_two_sub L (A (2 * m + 1)) hA1_pos (le_of_lt hA1_lt)
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    push_cast
    linarith [ih_c1,
      (by exact_mod_cast hsub : (c1 (2 ^ L - A (2 * m + 1)) : ℤ) + c1 (A (2 * m + 1) - 1) = L)]

private lemma altBlockVal_spec (d L top : ℕ) (hd : 1 ≤ d) (hL : 1 ≤ L) (A : ℕ → ℕ)
    (hpos : ∀ s < 2 * d, 1 ≤ A s)
    (hlt : ∀ s < 2 * d - 1, A s < 2 ^ L)
    (htop_lt : A (2 * d - 1) < 2 ^ (L + top - 1)) :
    0 < altBlockVal d L top A ∧
    (2 * (c1 (altBlockVal d L top A) : ℤ) - ((Nat.digits 2 (altBlockVal d L top A)).length : ℤ)) =
      (top : ℤ) + 2 * (c1 (A 0) : ℤ) +
      2 * (∑ s ∈ Finset.Ico 1 (2 * d), (-1 : ℤ) ^ s * (c1 (A s - 1) : ℤ)) := by
  have h2d1 : 2 * (d - 1) + 1 = 2 * d - 1 := by omega
  have ⟨hlow_lt, hlow_c1⟩ := altBlock_lower_spec (d - 1) L A
    (fun s hs => hpos s (by omega)) (fun s hs => hlt s (by omega))
  rw [h2d1] at hlow_lt
  set low := A 0 + ∑ t ∈ Finset.range (d - 1),
    ((2 ^ L - A (2 * t + 1)) * 2 ^ ((2 * t + 1) * L) +
     (A (2 * t + 2) - 1) * 2 ^ ((2 * t + 2) * L))
  have hval_eq : altBlockVal d L top A =
      low + (2 ^ (L + top) - A (2 * d - 1)) * 2 ^ ((2 * d - 1) * L) := rfl
  have htop_ge : 2 ^ (L + top - 1) ≤ 2 ^ (L + top) - A (2 * d - 1) := by
    have hpow : 2 ^ (L + top) = 2 * 2 ^ (L + top - 1) := by
      conv_lhs => rw [show L + top = (L + top - 1) + 1 by omega]
      rw [pow_succ, mul_comm]
    omega
  have htop_pos : 0 < 2 ^ (L + top) - A (2 * d - 1) := by
    have : 0 < 2 ^ (L + top - 1) := by positivity
    omega
  have htop_hi : 2 ^ (L + top) - A (2 * d - 1) < 2 ^ (L + top) := by
    have := hpos (2 * d - 1) (by omega)
    omega
  have htop_len : (Nat.digits 2 (2 ^ (L + top) - A (2 * d - 1))).length = L + top := by
    have h := digits_len_of_bounds (2 ^ (L + top) - A (2 * d - 1)) (L + top - 1) htop_ge
      (by rwa [show L + top - 1 + 1 = L + top by omega])
    omega
  have hval_pos : 0 < altBlockVal d L top A := by
    rw [hval_eq]
    have : 0 < 2 ^ ((2 * d - 1) * L) := by positivity
    nlinarith
  refine ⟨hval_pos, ?_⟩
  rw [hval_eq, c1_add_mul_pow_two _ _ _ hlow_lt, len_add_mul_pow_two _ _ _ hlow_lt htop_pos, htop_len]
  have hsub := c1_pow_two_sub (L + top) (A (2 * d - 1)) (hpos (2 * d - 1) (by omega)) (by
    have h1 : 2 ^ (L + top - 1) ≤ 2 ^ (L + top) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega)
  have hIco :
      ∑ s ∈ Finset.Ico 1 (2 * d), (-1 : ℤ) ^ s * (c1 (A s - 1) : ℤ) =
      (∑ t ∈ Finset.range (d - 1), (c1 (A (2 * t + 2) - 1) : ℤ)) -
      (∑ t ∈ Finset.range (d - 1), (c1 (A (2 * t + 1) - 1) : ℤ)) -
      (c1 (A (2 * d - 1) - 1) : ℤ) := by
    have hsplit : ∀ k : ℕ, 1 ≤ k →
        ∑ s ∈ Finset.Ico 1 (2 * k), (-1 : ℤ) ^ s * (c1 (A s - 1) : ℤ) =
        (∑ t ∈ Finset.range (k - 1), (c1 (A (2 * t + 2) - 1) : ℤ)) -
        (∑ t ∈ Finset.range (k - 1), (c1 (A (2 * t + 1) - 1) : ℤ)) -
        (c1 (A (2 * k - 1) - 1) : ℤ) := by
      intro k hk
      induction k with
      | zero => omega
      | succ k ihk =>
        by_cases hk0 : k = 0
        · subst hk0
          have h12 : Finset.Ico 1 (2 * (0 + 1)) = {1} := by
            ext x; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
          rw [h12]; simp
        · have hk1 : 1 ≤ k := by omega
          have ih' := ihk hk1
          have hIco_step : Finset.Ico 1 (2 * (k + 1)) =
              insert (2 * k + 1) (insert (2 * k) (Finset.Ico 1 (2 * k))) := by
            ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
          rw [hIco_step, Finset.sum_insert (by simp), Finset.sum_insert (by simp), ih']
          have hpar1 : (-1 : ℤ) ^ (2 * k + 1) = -1 := by
            rw [pow_succ, pow_mul]; norm_num
          have hpar0 : (-1 : ℤ) ^ (2 * k) = 1 := by
            rw [pow_mul]; norm_num
          rw [hpar1, hpar0, show k + 1 - 1 = (k - 1) + 1 by omega,
            Finset.sum_range_succ, Finset.sum_range_succ,
            show 2 * (k - 1) + 2 = 2 * k by omega,
            show 2 * (k - 1) + 1 = 2 * k - 1 by omega,
            show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
          ring
    exact hsplit d hd
  rw [hIco]
  have hd_cast : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
  have h2d1_cast : ((2 * d - 1 : ℕ) : ℤ) = 2 * (d : ℤ) - 1 := by omega
  have hsub_z : (c1 (2 ^ (L + top) - A (2 * d - 1)) : ℤ) + c1 (A (2 * d - 1) - 1) = L + top := by
    exact_mod_cast hsub
  push_cast at hlow_c1 ⊢
  rw [hd_cast] at hlow_c1
  rw [h2d1_cast]
  linarith

private lemma altBlockVal_cast_eq (d L top : ℕ) (hd : 1 ≤ d) (A : ℕ → ℕ)
    (hpos : ∀ s < 2 * d, 1 ≤ A s)
    (hlt : ∀ s < 2 * d - 1, A s < 2 ^ L)
    (htop_lt : A (2 * d - 1) < 2 ^ (L + top))
    (hA_top : A (2 * d) = 2 ^ top) :
    (altBlockVal d L top A : ℤ) =
      ∑ s ∈ Finset.range (2 * d + 1), (-1 : ℤ) ^ s * (A s : ℤ) * (2 ^ L : ℤ) ^ s := by
  have hlow_z : ∀ m : ℕ, m ≤ d - 1 →
      (A 0 : ℤ) +
      (∑ t ∈ Finset.range m,
        (((2 ^ L - A (2 * t + 1) : ℕ) : ℤ) * (2 ^ ((2 * t + 1) * L) : ℤ) +
         ((A (2 * t + 2) - 1 : ℕ) : ℤ) * (2 ^ ((2 * t + 2) * L) : ℤ))) =
      ∑ s ∈ Finset.range (2 * m + 1), (-1 : ℤ) ^ s * (A s : ℤ) * (2 ^ L : ℤ) ^ s := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ihm =>
      rw [Finset.sum_range_succ, ← add_assoc, ihm (by omega)]
      have h1 : A (2 * m + 1) ≤ 2 ^ L := le_of_lt (hlt (2 * m + 1) (by omega))
      have h2 : 1 ≤ A (2 * m + 2) := hpos (2 * m + 2) (by omega)
      rw [Nat.cast_sub h1, Nat.cast_sub h2]
      conv_rhs =>
        rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 by omega,
          Finset.sum_range_succ, Finset.sum_range_succ, show 2 * m + 1 + 1 = 2 * m + 2 by omega]
      have hp1 : (-1 : ℤ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
      have hp2 : (-1 : ℤ) ^ (2 * m + 2) = 1 := by
        rw [show 2 * m + 2 = 2 * (m + 1) by omega, pow_mul]; norm_num
      rw [hp1, hp2]
      have he1 : (2 ^ ((2 * m + 1) * L) : ℤ) = (2 ^ L : ℤ) ^ (2 * m + 1) := by
        push_cast; rw [← pow_mul, mul_comm]
      have he2 : (2 ^ ((2 * m + 2) * L) : ℤ) = (2 ^ L : ℤ) ^ (2 * m + 2) := by
        push_cast; rw [← pow_mul, mul_comm]
      rw [he1, he2, pow_succ (2 ^ L : ℤ) (2 * m + 1)]
      push_cast; ring
  unfold altBlockVal
  push_cast
  rw [hlow_z (d - 1) (le_refl _)]
  have h2d1 : 2 * (d - 1) + 1 = 2 * d - 1 := by omega
  rw [h2d1]
  have hsub_top : A (2 * d - 1) ≤ 2 ^ (L + top) := le_of_lt htop_lt
  rw [Nat.cast_sub hsub_top]
  rw [show 2 * d + 1 = (2 * d - 1) + 1 + 1 by omega,
    Finset.sum_range_succ, Finset.sum_range_succ]
  rw [show 2 * d - 1 + 1 = 2 * d by omega, hA_top]
  have hp1 : (-1 : ℤ) ^ (2 * d - 1) = -1 := by
    rw [show 2 * d - 1 = 2 * (d - 1) + 1 by omega, pow_succ, pow_mul]; norm_num
  have hp2 : (-1 : ℤ) ^ (2 * d) = 1 := by rw [pow_mul]; norm_num
  rw [hp1, hp2]
  have he1 : (2 ^ ((2 * d - 1) * L) : ℤ) = (2 ^ L : ℤ) ^ (2 * d - 1) := by
    push_cast; rw [← pow_mul, mul_comm]
  have he2 : (2 ^ L : ℤ) ^ (2 * d) = (2 ^ L : ℤ) * (2 ^ L : ℤ) ^ (2 * d - 1) := by
    conv_lhs => rw [show 2 * d = (2 * d - 1) + 1 by omega]
    rw [pow_succ, mul_comm]
  rw [he1, he2]
  push_cast [pow_add]
  ring

/-! ### Section 1c: Separated sum of powers of 2 -/

private lemma c1_separated_sum :
    ∀ k : ℕ, ∀ (W : Finset ℕ) (cnt E : ℕ → ℕ), W.card = k →
      (∀ a ∈ W, ∀ b ∈ W, a < b → cnt a < 2 ^ (E b - E a) ∧ E a ≤ E b) →
      c1 (∑ w ∈ W, cnt w * 2 ^ E w) = ∑ w ∈ W, c1 (cnt w)
  | 0, W, cnt, E, hk, _ => by
    rw [Finset.card_eq_zero.mp hk]; simp [c1]
  | k + 1, W, cnt, E, hk, hsep => by
    have hW : W.Nonempty := Finset.card_pos.mp (by omega)
    set m := W.min' hW
    have hm : m ∈ W := Finset.min'_mem W hW
    set W' := W.erase m
    have hcard' : W'.card = k := by
      rw [Finset.card_erase_of_mem hm, hk]; omega
    have hsum_split : ∑ w ∈ W, cnt w * 2 ^ E w =
        (cnt m + ∑ w ∈ W', cnt w * 2 ^ (E w - E m)) * 2 ^ E m := by
      rw [← Finset.add_sum_erase W _ hm, add_mul, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro w hw
      have hmw : m < w := lt_of_le_of_ne (Finset.min'_le W w (Finset.mem_of_mem_erase hw))
        (Ne.symm (Finset.ne_of_mem_erase hw))
      have hle : E m ≤ E w := (hsep m hm w (Finset.mem_of_mem_erase hw) hmw).2
      rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    rw [hsum_split, c1_mul_pow_two, ← Finset.add_sum_erase W (fun w => c1 (cnt w)) hm]
    by_cases hW' : W'.Nonempty
    · set m' := W'.min' hW'
      have hm' : m' ∈ W' := Finset.min'_mem W' hW'
      have hm'W : m' ∈ W := Finset.mem_of_mem_erase hm'
      have hmm' : m < m' := lt_of_le_of_ne (Finset.min'_le W m' hm'W)
        (Ne.symm (Finset.ne_of_mem_erase hm'))
      have hEm' : E m ≤ E m' := (hsep m hm m' hm'W hmm').2
      have hcnt_lt : cnt m < 2 ^ (E m' - E m) := (hsep m hm m' hm'W hmm').1
      have hshift : ∑ w ∈ W', cnt w * 2 ^ (E w - E m) =
          (∑ w ∈ W', cnt w * 2 ^ (E w - E m')) * 2 ^ (E m' - E m) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro w hw
        have hle' : E m' ≤ E w := by
          by_cases heq : w = m'
          · subst heq; exact le_refl _
          · have hlt' : m' < w := lt_of_le_of_ne (Finset.min'_le W' w hw) (Ne.symm heq)
            exact (hsep m' hm'W w (Finset.mem_of_mem_erase hw) hlt').2
        rw [mul_assoc, ← pow_add]
        congr 2; omega
      rw [hshift, c1_add_mul_pow_two _ _ _ hcnt_lt]
      congr 1
      apply c1_separated_sum k W' cnt (fun w => E w - E m') hcard'
      intro a ha b hb hab
      have haW := Finset.mem_of_mem_erase ha
      have hbW := Finset.mem_of_mem_erase hb
      have h1 := hsep a haW b hbW hab
      have ha_ge : E m' ≤ E a := by
        by_cases heq : a = m'
        · subst heq; exact le_refl _
        · exact (hsep m' hm'W a haW (lt_of_le_of_ne (Finset.min'_le W' a ha) (Ne.symm heq))).2
      have hb_ge : E m' ≤ E b := le_trans ha_ge h1.2
      refine ⟨?_, by omega⟩
      rw [show E b - E m' - (E a - E m') = E b - E a by omega]
      exact h1.1
    · rw [show W.erase m = W' from rfl, Finset.not_nonempty_iff_eq_empty.mp hW']
      simp

private lemma c1_separated_sum_sub_one (W : Finset ℕ) (hW : W.Nonempty) (cnt E : ℕ → ℕ)
    (hcnt_pos : ∀ w ∈ W, 1 ≤ cnt w)
    (hsep : ∀ a ∈ W, ∀ b ∈ W, a < b → cnt a < 2 ^ (E b - E a) ∧ E a ≤ E b) :
    let m := W.min' hW
    c1 ((∑ w ∈ W, cnt w * 2 ^ E w) - 1) =
      E m + c1 (cnt m - 1) + ∑ w ∈ W.erase m, c1 (cnt w) := by
  dsimp only
  set m := W.min' hW
  have hm : m ∈ W := Finset.min'_mem W hW
  set W' := W.erase m
  have hsum_split : ∑ w ∈ W, cnt w * 2 ^ E w =
      (cnt m + ∑ w ∈ W', cnt w * 2 ^ (E w - E m)) * 2 ^ E m := by
    rw [← Finset.add_sum_erase W _ hm, add_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro w hw
    have hmw : m < w := lt_of_le_of_ne (Finset.min'_le W w (Finset.mem_of_mem_erase hw))
      (Ne.symm (Finset.ne_of_mem_erase hw))
    have hle : E m ≤ E w := (hsep m hm w (Finset.mem_of_mem_erase hw) hmw).2
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  have hQ_pos : 1 ≤ cnt m + ∑ w ∈ W', cnt w * 2 ^ (E w - E m) := by
    have := hcnt_pos m hm; omega
  rw [hsum_split, c1_mul_pow_two_sub_one _ _ hQ_pos]
  have hsub_add : cnt m + ∑ w ∈ W', cnt w * 2 ^ (E w - E m) - 1 =
      (cnt m - 1) + ∑ w ∈ W', cnt w * 2 ^ (E w - E m) := by
    have := hcnt_pos m hm; omega
  rw [hsub_add]
  by_cases hW' : W'.Nonempty
  · set m' := W'.min' hW'
    have hm' : m' ∈ W' := Finset.min'_mem W' hW'
    have hm'W : m' ∈ W := Finset.mem_of_mem_erase hm'
    have hmm' : m < m' := lt_of_le_of_ne (Finset.min'_le W m' hm'W)
      (Ne.symm (Finset.ne_of_mem_erase hm'))
    have hcnt_lt : cnt m - 1 < 2 ^ (E m' - E m) := by
      have := (hsep m hm m' hm'W hmm').1; omega
    have hshift : ∑ w ∈ W', cnt w * 2 ^ (E w - E m) =
        (∑ w ∈ W', cnt w * 2 ^ (E w - E m')) * 2 ^ (E m' - E m) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro w hw
      have hle' : E m' ≤ E w := by
        by_cases heq : w = m'
        · subst heq; exact le_refl _
        · exact (hsep m' hm'W w (Finset.mem_of_mem_erase hw)
            (lt_of_le_of_ne (Finset.min'_le W' w hw) (Ne.symm heq))).2
      have hEm' : E m ≤ E m' := (hsep m hm m' hm'W hmm').2
      rw [mul_assoc, ← pow_add]; congr 2; omega
    rw [hshift, c1_add_mul_pow_two _ _ _ hcnt_lt]
    have hrec := c1_separated_sum W'.card W' cnt (fun w => E w - E m') rfl (by
      intro a ha b hb hab
      have haW := Finset.mem_of_mem_erase ha
      have hbW := Finset.mem_of_mem_erase hb
      have h1 := hsep a haW b hbW hab
      have ha_ge : E m' ≤ E a := by
        by_cases heq : a = m'
        · subst heq; exact le_refl _
        · exact (hsep m' hm'W a haW (lt_of_le_of_ne (Finset.min'_le W' a ha) (Ne.symm heq))).2
      have hb_ge : E m' ≤ E b := le_trans ha_ge h1.2
      refine ⟨?_, by omega⟩
      rw [show E b - E m' - (E a - E m') = E b - E a by omega]
      exact h1.1)
    rw [hrec]
    ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hW']
    simp [add_comm]

/-! ### Section 2: Tuple expansion of powers -/

private def tupleSet (N i S : ℕ) : Finset (Fin i → Fin (N + 1)) :=
  Finset.univ.filter (fun f => (∑ a : Fin i, (f a : ℕ)) = S)

private def polyCoeff (N i : ℕ) (x : Fin (N + 1) → ℕ) (S : ℕ) : ℕ :=
  ∑ f ∈ tupleSet N i S, 2 ^ (∑ a : Fin i, x (f a))

private lemma tupleSet_nonempty (N : ℕ) :
    ∀ i S : ℕ, S ≤ i * N → (tupleSet N i S).Nonempty
  | 0, S, hS => by
    have h0 : S = 0 := by omega
    subst h0
    exact ⟨Fin.elim0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩⟩
  | i + 1, S, hS => by
    set last := min S N
    have hlast_le : last ≤ N := min_le_right S N
    have hrem : S - last ≤ i * N := by
      by_cases h : S ≤ N
      · have : last = S := min_eq_left h; omega
      · have : last = N := min_eq_right (by omega)
        rw [Nat.succ_mul] at hS; omega
    obtain ⟨f, hf⟩ := tupleSet_nonempty N i (S - last) hrem
    rw [tupleSet, Finset.mem_filter] at hf
    refine ⟨Fin.snoc f ⟨last, by omega⟩, ?_⟩
    rw [tupleSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, hf.2]
    have : last ≤ S := min_le_left S N
    omega

private lemma polyCoeff_pos (N i S : ℕ) (x : Fin (N + 1) → ℕ) (hS : S ≤ i * N) :
    1 ≤ polyCoeff N i x S := by
  obtain ⟨f, hf⟩ := tupleSet_nonempty N i S hS
  have hterm : 1 ≤ 2 ^ (∑ a : Fin i, x (f a)) := Nat.one_le_pow _ 2 (by norm_num)
  calc 1 ≤ 2 ^ (∑ a : Fin i, x (f a)) := hterm
    _ ≤ polyCoeff N i x S := Finset.single_le_sum (f := fun g => 2 ^ (∑ a : Fin i, x (g a)))
        (fun _ _ => Nat.zero_le _) hf

private lemma tupleSet_zero (N i : ℕ) :
    tupleSet N i 0 = {fun _ => ⟨0, Nat.succ_pos N⟩} := by
  ext f
  simp only [tupleSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    funext a
    apply Fin.ext
    have hle : (f a : ℕ) ≤ ∑ b : Fin i, (f b : ℕ) :=
      Finset.single_le_sum (f := fun b => (f b : ℕ)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
    simp only [Fin.val_mk]; omega
  · intro h; subst h; simp

private lemma tupleSet_top (N i : ℕ) :
    tupleSet N i (i * N) = {fun _ => ⟨N, Nat.lt_succ_self N⟩} := by
  ext f
  simp only [tupleSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    funext a
    apply Fin.ext
    by_contra hne
    have hlt : (f a : ℕ) < N := lt_of_le_of_ne (Nat.lt_succ_iff.mp (f a).isLt) hne
    have hsum_lt : ∑ b : Fin i, (f b : ℕ) < ∑ _b : Fin i, N := by
      apply Finset.sum_lt_sum
      · intro b _; exact Nat.lt_succ_iff.mp (f b).isLt
      · exact ⟨a, Finset.mem_univ a, hlt⟩
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum_lt
    omega
  · intro h; subst h
    simp [Finset.sum_const, smul_eq_mul]

private lemma polyCoeff_zero (N i : ℕ) (x : Fin (N + 1) → ℕ) (hx0 : x ⟨0, Nat.succ_pos N⟩ = 0) :
    polyCoeff N i x 0 = 1 := by
  unfold polyCoeff
  rw [tupleSet_zero, Finset.sum_singleton]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hx0, mul_zero, pow_zero]

private lemma polyCoeff_top (N i : ℕ) (x : Fin (N + 1) → ℕ) :
    polyCoeff N i x (i * N) = 2 ^ (i * x ⟨N, Nat.lt_succ_self N⟩) := by
  simp [polyCoeff, tupleSet_top, Finset.sum_const, smul_eq_mul]

private lemma polyCoeff_le (N i S B : ℕ) (x : Fin (N + 1) → ℕ)
    (hx : ∀ j, x j ≤ B) :
    polyCoeff N i x S ≤ (N + 1) ^ i * 2 ^ (i * B) := by
  unfold polyCoeff
  calc ∑ f ∈ tupleSet N i S, 2 ^ (∑ a : Fin i, x (f a))
      ≤ ∑ _f ∈ tupleSet N i S, 2 ^ (i * B) := by
        apply Finset.sum_le_sum
        intro f _
        apply Nat.pow_le_pow_right (by norm_num)
        calc ∑ a : Fin i, x (f a) ≤ ∑ _a : Fin i, B := Finset.sum_le_sum (fun a _ => hx (f a))
          _ = i * B := by simp [Finset.sum_const, smul_eq_mul]
    _ = (tupleSet N i S).card * 2 ^ (i * B) := by simp [Finset.sum_const, smul_eq_mul]
    _ ≤ (N + 1) ^ i * 2 ^ (i * B) := by
        apply Nat.mul_le_mul_right
        calc (tupleSet N i S).card ≤ (Finset.univ : Finset (Fin i → Fin (N + 1))).card :=
              Finset.card_le_card (Finset.filter_subset _ _)
          _ = (N + 1) ^ i := by simp [Fintype.card_pi, Finset.prod_const]

private lemma signed_sum_pow (N L i : ℕ) (x : Fin (N + 1) → ℕ) :
    (∑ j : Fin (N + 1), (-1 : ℤ) ^ (j : ℕ) * (2 ^ x j : ℤ) * (2 ^ L : ℤ) ^ (j : ℕ)) ^ i =
    ∑ S ∈ Finset.range (i * N + 1),
      (-1 : ℤ) ^ S * (polyCoeff N i x S : ℤ) * (2 ^ L : ℤ) ^ S := by
  rw [Fintype.sum_pow]
  have hprod : ∀ f : Fin i → Fin (N + 1),
      ∏ a : Fin i, ((-1 : ℤ) ^ (f a : ℕ) * (2 ^ x (f a) : ℤ) * (2 ^ L : ℤ) ^ (f a : ℕ)) =
      (-1 : ℤ) ^ (∑ a : Fin i, (f a : ℕ)) * (2 ^ (∑ a : Fin i, x (f a)) : ℤ) *
        (2 ^ L : ℤ) ^ (∑ a : Fin i, (f a : ℕ)) := by
    intro f
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum]
  simp_rw [hprod]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.range (i * N + 1))
    (g := fun f : Fin i → Fin (N + 1) => ∑ a : Fin i, (f a : ℕ))]
  · apply Finset.sum_congr rfl
    intro S _
    change ∑ f ∈ tupleSet N i S,
        (-1 : ℤ) ^ (∑ a : Fin i, (f a : ℕ)) * (2 ^ (∑ a : Fin i, x (f a)) : ℤ) *
          (2 ^ L : ℤ) ^ (∑ a : Fin i, (f a : ℕ)) =
      (-1 : ℤ) ^ S * (polyCoeff N i x S : ℤ) * (2 ^ L : ℤ) ^ S
    unfold polyCoeff
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro f hf
    rw [tupleSet, Finset.mem_filter] at hf
    rw [hf.2]
  · intro f _
    rw [Finset.mem_range, Nat.lt_succ_iff]
    calc ∑ a : Fin i, (f a : ℕ) ≤ ∑ _a : Fin i, N :=
          Finset.sum_le_sum (fun a _ => Nat.lt_succ_iff.mp (f a).isLt)
      _ = i * N := by simp [Finset.sum_const, smul_eq_mul]

/-! ### Section 3: Unified Bridge Sumset Lemma -/

private def isCheap (r s j : ℕ) : Bool :=
  (j ≤ s) || (j == 2 * r + s) || (4 * r + 2 ≤ j && j ≤ 4 * r + 4)

private def bridgeH (r s u H j : ℕ) : ℕ :=
  if j == 0 || j == 4 * r + 4 then 0
  else if isCheap r s j then 1
  else if j == s + 1 then u
  else H

private lemma bridgeH_le_one_of_cheap (r s u H j : ℕ) (hc : isCheap r s j = true) :
    bridgeH r s u H j ≤ 1 := by
  unfold bridgeH
  split_ifs <;> simp_all

private lemma isCheap_special_false (r s : ℕ) (hr : 1 ≤ r) (hs : s = 3 ∨ s = 4) :
    isCheap r s (s + 1) = false := by
  unfold isCheap
  rcases hs with rfl | rfl <;> simp <;> omega

private lemma bridgeH_special (r s u H : ℕ) (hr : 1 ≤ r) (hs : s = 3 ∨ s = 4) :
    bridgeH r s u H (s + 1) = u := by
  have hc := isCheap_special_false r s hr hs
  have hne1 : (s + 1 == 0) = false := by simp
  have hne2 : (s + 1 == 4 * r + 4) = false := by
    simp only [beq_eq_false_iff_ne]; rcases hs with rfl | rfl <;> omega
  unfold bridgeH
  simp [hc, hne1, hne2]

private lemma exists_tuple_in_interval (g a b c p s S : ℕ)
    (hp : p ≤ g) (hs_le : s ≤ g) (hg2 : 2 ≤ g)
    (hlo : b * (g - 2) + c * p ≤ S)
    (hhi : S ≤ b * g + c * p + a * s) :
    ∃ f : Fin (a + b + c) → Fin (g + 1),
      (∑ k, (f k : ℕ)) = S ∧
      ∀ k, ((f k : ℕ) ≤ s ∨ (f k : ℕ) = p ∨ (g - 2 ≤ (f k : ℕ) ∧ (f k : ℕ) ≤ g)) := by
  -- Express S - c * p as S_b + S_a with b*(g-2) <= S_b <= b*g and 0 <= S_a <= a*s
  set rem := S - c * p
  have hrem_lo : b * (g - 2) ≤ rem := by omega
  have hrem_hi : rem ≤ b * g + a * s := by omega
  set Sb := min rem (b * g)
  set Sa := rem - Sb
  have hSb_lo : b * (g - 2) ≤ Sb := le_min hrem_lo (Nat.mul_le_mul_left b (by omega))
  have hSb_hi : Sb ≤ b * g := min_le_right _ _
  have hSa_hi : Sa ≤ a * s := by
    by_cases h : rem ≤ b * g
    · have : Sb = rem := min_eq_left h; omega
    · have : Sb = b * g := min_eq_right (by omega); omega
  have hSb_add_Sa : Sb + Sa + c * p = S := by
    have : Sb ≤ rem := min_le_left _ _
    omega
  -- Tuple for Sa in [0, a*s] using {0..s}
  obtain ⟨fa, hfa⟩ := tupleSet_nonempty s a Sa hSa_hi
  rw [tupleSet, Finset.mem_filter] at hfa
  -- Tuple for Sb - b*(g-2) in [0, b*2] using {0, 1, 2}
  have hdb_hi : Sb - b * (g - 2) ≤ b * 2 := by
    have : b * g = b * (g - 2) + b * 2 := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hg2]
    omega
  obtain ⟨fb, hfb⟩ := tupleSet_nonempty 2 b (Sb - b * (g - 2)) hdb_hi
  rw [tupleSet, Finset.mem_filter] at hfb
  let f1 : Fin (a + b) → Fin (g + 1) := Fin.addCases
    (fun k => ⟨(fa k : ℕ), by have := (fa k).isLt; omega⟩)
    (fun k => ⟨(g - 2) + (fb k : ℕ), by have := (fb k).isLt; omega⟩)
  let f : Fin (a + b + c) → Fin (g + 1) := Fin.addCases f1 (fun _ => ⟨p, by omega⟩)
  refine ⟨f, ?_, ?_⟩
  · rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [f, f1, Fin.addCases_left, Fin.addCases_right]
    rw [Finset.sum_add_distrib, hfa.2, hfb.2]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  · intro k
    refine Fin.addCases (m := a + b) (n := c) ?_ ?_ k
    · intro k1
      simp only [f, Fin.addCases_left]
      refine Fin.addCases (m := a) (n := b) ?_ ?_ k1
      · intro ka
        simp only [f1, Fin.addCases_left]
        left; exact Nat.lt_succ_iff.mp (fa ka).isLt
      · intro kb
        simp only [f1, Fin.addCases_right]
        right; right; have := (fb kb).isLt; omega
    · intro kc
      simp only [f, Fin.addCases_right]
      right; left; simp

private lemma bridge_cover (r s i S : ℕ) (hr : 1 ≤ r) (hs : s = 3 ∨ s = 4)
    (hi : r ≤ i) (hS : S ≤ i * (4 * r + 4))
    (hne : ¬ (i = r ∧ S = (r - 1) * (4 * r + 4) + s + 1)) :
    ∃ f ∈ tupleSet (4 * r + 4) i S, ∀ a, isCheap r s (f a) = true := by
  set g := 4 * r + 4
  set p := 2 * r + s
  have hp_le : p ≤ g := by rcases hs with rfl | rfl <;> omega
  have hs_le : s ≤ g := by rcases hs with rfl | rfl <;> omega
  have hg2 : 2 ≤ g := by omega
  -- Helper: from (a, b, c) with a + b + c = i and interval bounds, build the Fin i tuple
  have mk_from : ∀ a b c : ℕ, a + b + c = i →
      b * (g - 2) + c * p ≤ S → S ≤ b * g + c * p + a * s →
      ∃ f ∈ tupleSet g i S, ∀ k, isCheap r s (f k) = true := by
    intro a b c habc hlo hhi
    obtain ⟨f0, hf0_sum, hf0_mem⟩ := exists_tuple_in_interval g a b c p s S hp_le hs_le hg2 hlo hhi
    let e : Fin i ≃ Fin (a + b + c) := finCongr habc.symm
    refine ⟨f0 ∘ e, ?_, ?_⟩
    · rw [tupleSet, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      change ∑ k : Fin i, (f0 (e k) : ℕ) = S
      rw [Equiv.sum_comp e (fun k => (f0 k : ℕ))]
      exact hf0_sum
    · intro k
      rcases hf0_mem (e k) with h1 | h2 | h3
      · unfold isCheap; simp [h1]
      · unfold isCheap; simp [h2, p]
      · have hg_eq : g = 4 * r + 4 := rfl
        unfold isCheap
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        right
        change 4 * r + 2 ≤ (f0 (e k) : ℕ) ∧ (f0 (e k) : ℕ) ≤ 4 * r + 4
        dsimp only [g] at h3
        omega
  -- Find b = min (S / (g - 2)) i
  by_cases htop : i * (g - 2) ≤ S
  · exact mk_from 0 i 0 (by omega) (by simpa using htop) (by simpa using hS)
  · -- So S < i * (g - 2). Take b = S / (g - 2) < i.
    set b := S / (g - 2)
    have hb_lt : b < i := by
      have : 0 < g - 2 := by omega
      exact (Nat.div_lt_iff_lt_mul this).mpr (by omega)
    have hSb_lo : b * (g - 2) ≤ S := by
      have := Nat.div_mul_le_self S (g - 2); omega
    have hSb_hi : S < (b + 1) * (g - 2) := by
      have h := Nat.lt_div_mul_add (a := S) (b := g - 2) (by omega)
      change S < b * (g - 2) + (g - 2) at h
      have : (b + 1) * (g - 2) = b * (g - 2) + (g - 2) := by ring
      omega
    -- Check if S lies in I(b, 0) or I(b, 1)!
    by_cases hI0 : S ≤ b * g + (i - b) * s
    · exact mk_from (i - b) b 0 (by omega) (by simpa using hSb_lo) (by simpa using hI0)
    · -- S > b * g + (i - b) * s. Show it lies in I(b, 1)!
      have hgm2 : g - 2 = 4 * r + 2 := by omega
      have hbg : b * g = b * (g - 2) + 2 * b := by zify [hg2]; ring
      have hS_gt : b * g + (i - b) * s < S := by omega
      have hs3 : 3 ≤ s := by rcases hs with rfl | rfl <;> omega
      have hlo1 : b * (g - 2) + p ≤ S := by
        by_cases hlast : b = i - 1
        · have hib : i - b = 1 := by omega
          rw [hib, one_mul] at hS_gt
          by_cases hir : i = r
          · have hb_eq : b = r - 1 := by omega
            have hS_ne : S ≠ b * g + s + 1 := by
              rw [hb_eq]; intro h; exact hne ⟨hir, h⟩
            have h2b : 2 * b + 2 = 2 * r := by omega
            dsimp only [p]; omega
          · have h2b : 2 * r ≤ 2 * b := by omega
            dsimp only [p]; omega
        · have hib2 : 2 ≤ i - b := by omega
          have h2 : 2 * r + s ≤ 2 * b + (i - b) * s + 1 := by
            rcases hs with rfl | rfl <;> omega
          dsimp only [p]; omega
      have hhi1 : S ≤ b * g + p + (i - b - 1) * s := by
        have hstep : (b + 1) * (g - 2) = b * (g - 2) + (4 * r + 2) := by rw [hgm2]; ring
        have h2 : 4 * r + 1 ≤ 2 * b + (2 * r + s) + (i - b - 1) * s := by
          rcases hs with rfl | rfl <;> omega
        dsimp only [p]; omega
      exact mk_from (i - b - 1) b 1 (by omega) (by simpa using hlo1) (by simpa using hhi1)

private lemma bridge_miss (r s : ℕ) (hr : 1 ≤ r) (hs : s = 3 ∨ s = 4) :
    ¬ ∃ f ∈ tupleSet (4 * r + 4) r ((r - 1) * (4 * r + 4) + s + 1),
      ∀ a, isCheap r s (f a) = true := by
  rintro ⟨f, hf, hcheap⟩
  rw [tupleSet, Finset.mem_filter] at hf
  let g := 4 * r + 4
  let p := 2 * r + s
  let S := (r - 1) * g + s + 1
  -- Partition Fin r into R (g-2 <= f a <= g), P (f a = p and not in R), L (f a <= s)
  let R := Finset.univ.filter (fun a : Fin r => g - 2 ≤ (f a : ℕ))
  let P := Finset.univ.filter (fun a : Fin r => (f a : ℕ) < g - 2 ∧ (f a : ℕ) = p)
  let L := Finset.univ.filter (fun a : Fin r => (f a : ℕ) < g - 2 ∧ (f a : ℕ) ≠ p)
  have hpart : ∀ a : Fin r, (f a : ℕ) ≤ s ∨ (f a : ℕ) = p ∨ g - 2 ≤ (f a : ℕ) := by
    intro a
    have hc := hcheap a
    unfold isCheap at hc
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    rcases hc with (h1 | h2) | h3
    · left; exact h1
    · right; left; exact h2
    · right; right; dsimp only [g]; omega
  have hL_le : ∀ a ∈ L, (f a : ℕ) ≤ s := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rcases hpart a with h1 | h2 | h3 <;> omega
  have hdisj1 : Disjoint R (P ∪ L) := by
    rw [Finset.disjoint_left]; intro a ha hpl
    rw [Finset.mem_filter] at ha
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at hpl
    omega
  have hdisj2 : Disjoint P L := by
    rw [Finset.disjoint_left]; intro a ha hl
    rw [Finset.mem_filter] at ha hl; omega
  have hunion : R ∪ (P ∪ L) = Finset.univ := by
    ext a
    simp only [R, P, L, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    by_cases h1 : g - 2 ≤ (f a : ℕ)
    · exact Or.inl h1
    · by_cases h2 : (f a : ℕ) = p
      · exact Or.inr (Or.inl ⟨by omega, h2⟩)
      · exact Or.inr (Or.inr ⟨by omega, h2⟩)
  have hcard : R.card + P.card + L.card = r := by
    have := congrArg Finset.card hunion
    rw [Finset.card_union_of_disjoint hdisj1, Finset.card_union_of_disjoint hdisj2,
      Finset.card_univ, Fintype.card_fin] at this
    omega
  have hsum_split : S = (∑ a ∈ R, (f a : ℕ)) + (∑ a ∈ P, (f a : ℕ)) + (∑ a ∈ L, (f a : ℕ)) := by
    have hsum_u : ∑ a : Fin r, (f a : ℕ) =
        (∑ a ∈ R, (f a : ℕ)) + (∑ a ∈ P, (f a : ℕ)) + (∑ a ∈ L, (f a : ℕ)) := by
      conv_lhs => rw [← hunion]
      rw [Finset.sum_union hdisj1, Finset.sum_union hdisj2]
      exact (add_assoc _ _ _).symm
    change (r - 1) * (4 * r + 4) + s + 1 = _
    rw [← hf.2]
    exact hsum_u
  have hR_lo : R.card * (g - 2) ≤ ∑ a ∈ R, (f a : ℕ) := by
    calc R.card * (g - 2) = ∑ _a ∈ R, (g - 2) := by simp [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ a ∈ R, (f a : ℕ) := Finset.sum_le_sum (fun a ha => (Finset.mem_filter.mp ha).2)
  have hR_hi : ∑ a ∈ R, (f a : ℕ) ≤ R.card * g := by
    calc ∑ a ∈ R, (f a : ℕ) ≤ ∑ _a ∈ R, g := Finset.sum_le_sum (fun a _ => Nat.lt_succ_iff.mp (f a).isLt)
      _ = R.card * g := by simp [Finset.sum_const, smul_eq_mul]
  have hP_eq : ∑ a ∈ P, (f a : ℕ) = P.card * p := by
    calc ∑ a ∈ P, (f a : ℕ) = ∑ _a ∈ P, p := Finset.sum_congr rfl (fun a ha => (Finset.mem_filter.mp ha).2.2)
      _ = P.card * p := by simp [Finset.sum_const, smul_eq_mul]
  have hL_hi : ∑ a ∈ L, (f a : ℕ) ≤ L.card * s := by
    calc ∑ a ∈ L, (f a : ℕ) ≤ ∑ _a ∈ L, s := Finset.sum_le_sum hL_le
      _ = L.card * s := by simp [Finset.sum_const, smul_eq_mul]
  set b := R.card
  set c := P.card
  set a := L.card
  have hlo : b * (g - 2) + c * p ≤ S := by omega
  have hhi : S ≤ b * g + c * p + a * s := by omega
  have hg_eq : (g : ℤ) = 4 * (r : ℤ) + 4 := by exact_mod_cast (rfl : g = 4 * r + 4)
  have hgm2_eq : ((g - 2 : ℕ) : ℤ) = 4 * (r : ℤ) + 2 := by
    have : g - 2 = 4 * r + 2 := by dsimp only [g]; omega
    exact_mod_cast this
  have hp_eq : (p : ℤ) = 2 * (r : ℤ) + (s : ℤ) := by exact_mod_cast (rfl : p = 2 * r + s)
  have hS_eq : (S : ℤ) = ((r : ℤ) - 1) * (4 * (r : ℤ) + 4) + (s : ℤ) + 1 := by
    have hr1 : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by omega
    have h1 : (S : ℤ) = ((r - 1 : ℕ) : ℤ) * (g : ℤ) + (s : ℤ) + 1 := by
      exact_mod_cast (rfl : S = (r - 1) * g + s + 1)
    rw [h1, hr1, hg_eq]
  have hlo_z : (b : ℤ) * (4 * (r : ℤ) + 2) + (c : ℤ) * (2 * (r : ℤ) + (s : ℤ)) ≤ (S : ℤ) := by
    have : ((b * (g - 2) + c * p : ℕ) : ℤ) ≤ (S : ℤ) := by exact_mod_cast hlo
    push_cast at this; rw [hgm2_eq, hp_eq] at this; exact this
  have hhi_z : (S : ℤ) ≤ (b : ℤ) * (4 * (r : ℤ) + 4) + (c : ℤ) * (2 * (r : ℤ) + (s : ℤ)) + (a : ℤ) * (s : ℤ) := by
    have : (S : ℤ) ≤ ((b * g + c * p + a * s : ℕ) : ℤ) := by exact_mod_cast hhi
    push_cast at this; rw [hg_eq, hp_eq] at this; exact this
  have hcard_z : (b : ℤ) + (c : ℤ) + (a : ℤ) = (r : ℤ) := by exact_mod_cast hcard
  rw [hS_eq] at hlo_z hhi_z
  have hr_z : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
  suffices ∀ (b c a : ℕ),
      (b : ℤ) + (c : ℤ) + (a : ℤ) = (r : ℤ) →
      (b : ℤ) * (4 * (r : ℤ) + 2) + (c : ℤ) * (2 * (r : ℤ) + (s : ℤ)) ≤
        ((r : ℤ) - 1) * (4 * (r : ℤ) + 4) + (s : ℤ) + 1 →
      ((r : ℤ) - 1) * (4 * (r : ℤ) + 4) + (s : ℤ) + 1 ≤
        (b : ℤ) * (4 * (r : ℤ) + 4) + (c : ℤ) * (2 * (r : ℤ) + (s : ℤ)) + (a : ℤ) * (s : ℤ) →
      False from this b c a hcard_z hlo_z hhi_z
  clear f hf hcheap R P L b c a hpart hL_le hdisj1 hdisj2 hunion hcard hsum_split hR_lo hR_hi hP_eq hL_hi hlo hhi hg_eq hgm2_eq hp_eq hS_eq hlo_z hhi_z hcard_z
  intro b c a hcard_z hlo_z hhi_z
  have ha_z : (0 : ℤ) ≤ (a : ℤ) := Nat.cast_nonneg _
  have hb_z0 : (0 : ℤ) ≤ (b : ℤ) := Nat.cast_nonneg _
  have hc_z0 : (0 : ℤ) ≤ (c : ℤ) := Nat.cast_nonneg _
  rcases hs with rfl | rfl
  · push_cast at hlo_z hhi_z
    by_cases hb1 : b = r
    · have hb_z : (b : ℤ) = r := by exact_mod_cast hb1
      nlinarith
    · by_cases hb2 : b = r - 1
      · have hb_z : (b : ℤ) = (r : ℤ) - 1 := by omega
        by_cases hc0 : c = 0
        · have hc_z : (c : ℤ) = 0 := by exact_mod_cast hc0
          nlinarith
        · have hc_z : (1 : ℤ) ≤ (c : ℤ) := by omega
          nlinarith
      · have hb_z : (b : ℤ) ≤ (r : ℤ) - 2 := by omega
        have h1 : (c : ℤ) * (2 * (r : ℤ) + 3) + (a : ℤ) * 3 ≤ ((r : ℤ) - (b : ℤ)) * (2 * (r : ℤ) + 3) := by nlinarith
        nlinarith
  · push_cast at hlo_z hhi_z
    by_cases hb1 : b = r
    · have hb_z : (b : ℤ) = r := by exact_mod_cast hb1
      nlinarith
    · by_cases hb2 : b = r - 1
      · have hb_z : (b : ℤ) = (r : ℤ) - 1 := by omega
        by_cases hc0 : c = 0
        · have hc_z : (c : ℤ) = 0 := by exact_mod_cast hc0
          nlinarith
        · have hc_z : (1 : ℤ) ≤ (c : ℤ) := by omega
          nlinarith
      · have hb_z : (b : ℤ) ≤ (r : ℤ) - 2 := by omega
        have h1 : (c : ℤ) * (2 * (r : ℤ) + 4) + (a : ℤ) * 4 ≤ ((r : ℤ) - (b : ℤ)) * (2 * (r : ℤ) + 4) := by nlinarith
        nlinarith

/-! ### Section 3b: Bridge minimum and alternating sum -/

private def minWeight {N : ℕ} (w : Fin (N + 1) → ℕ) (i S : ℕ) (hS : S ≤ i * N) : ℕ :=
  ((tupleSet N i S).image (fun f => ∑ a : Fin i, w (f a))).min'
    ((tupleSet_nonempty N i S hS).image _)

private lemma minWeight_le {N : ℕ} (w : Fin (N + 1) → ℕ) (i S : ℕ) (hS : S ≤ i * N)
    {f : Fin i → Fin (N + 1)} (hf : f ∈ tupleSet N i S) :
    minWeight w i S hS ≤ ∑ a : Fin i, w (f a) :=
  Finset.min'_le _ _ (Finset.mem_image_of_mem _ hf)

private lemma exists_minWeight {N : ℕ} (w : Fin (N + 1) → ℕ) (i S : ℕ) (hS : S ≤ i * N) :
    ∃ f ∈ tupleSet N i S, ∑ a : Fin i, w (f a) = minWeight w i S hS := by
  have hmem := Finset.min'_mem ((tupleSet N i S).image (fun f => ∑ a : Fin i, w (f a)))
    ((tupleSet_nonempty N i S hS).image _)
  rw [Finset.mem_image] at hmem
  exact hmem

private lemma le_minWeight {N : ℕ} (w : Fin (N + 1) → ℕ) (i S : ℕ) (hS : S ≤ i * N) (m : ℕ)
    (hm : ∀ f ∈ tupleSet N i S, m ≤ ∑ a : Fin i, w (f a)) :
    m ≤ minWeight w i S hS := by
  obtain ⟨f, hf, hfeq⟩ := exists_minWeight w i S hS
  rw [← hfeq]
  exact hm f hf

private def bridgeMin (r s u H i S : ℕ) : ℕ :=
  if h : S ≤ i * (4 * r + 4) then
    minWeight (fun j : Fin (4 * r + 4 + 1) => bridgeH r s u H j) i S h
  else 0

private def bridgeAlt (r s u H i : ℕ) : ℤ :=
  ∑ S ∈ Finset.range (i * (4 * r + 4) + 1), (-1 : ℤ) ^ S * (bridgeMin r s u H i S : ℤ)

private lemma bridgeMin_cheap_eq (r s u1 H1 u2 H2 i S : ℕ)
    (hS : S ≤ i * (4 * r + 4))
    (hu1 : i < u1) (hH1 : i < H1) (hu2 : i < u2) (hH2 : i < H2)
    (hcov : ∃ f ∈ tupleSet (4 * r + 4) i S, ∀ a, isCheap r s (f a) = true) :
    bridgeMin r s u1 H1 i S = bridgeMin r s u2 H2 i S ∧
    (∀ f ∈ tupleSet (4 * r + 4) i S,
      (∑ a : Fin i, bridgeH r s u1 H1 (f a)) = bridgeMin r s u1 H1 i S →
      ∀ a, isCheap r s (f a) = true) := by
  have hle_i : ∀ u H, bridgeMin r s u H i S ≤ i := by
    intro u H
    obtain ⟨f, hf, hfc⟩ := hcov
    rw [bridgeMin, dif_pos hS]
    calc minWeight _ i S hS ≤ ∑ a : Fin i, bridgeH r s u H (f a) := minWeight_le _ i S hS hf
      _ ≤ ∑ _a : Fin i, 1 := Finset.sum_le_sum (fun a _ => bridgeH_le_one_of_cheap _ _ _ _ _ (hfc a))
      _ = i := by simp
  have hmin_cheap : ∀ u H, i < u → i < H →
      ∀ f ∈ tupleSet (4 * r + 4) i S,
        (∑ a : Fin i, bridgeH r s u H (f a)) = bridgeMin r s u H i S →
        ∀ a, isCheap r s (f a) = true := by
    intro u H hu hH f hf hfeq a
    by_contra hnc
    have hnot : isCheap r s (f a) = false := Bool.eq_false_iff.mpr hnc
    have hbig : i < bridgeH r s u H (f a) := by
      unfold bridgeH
      have h0 : (f a : ℕ) ≠ 0 := by
        intro h0; rw [h0] at hnot; unfold isCheap at hnot; simp at hnot
      have hg : (f a : ℕ) ≠ 4 * r + 4 := by
        intro hg; rw [hg] at hnot; unfold isCheap at hnot; simp at hnot
      simp only [beq_iff_eq, Bool.or_eq_true, h0, hg, or_self, ↓reduceIte, hnot, Bool.false_eq_true]
      split_ifs <;> omega
    have hle_sum : bridgeH r s u H (f a) ≤ ∑ b : Fin i, bridgeH r s u H (f b) :=
      Finset.single_le_sum (f := fun b : Fin i => bridgeH r s u H (f b))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
    have hbm := hle_i u H
    omega
  have hcheap_same : ∀ j, isCheap r s j = true → bridgeH r s u1 H1 j = bridgeH r s u2 H2 j := by
    intro j hj; unfold bridgeH; simp [hj]
  refine ⟨?_, hmin_cheap u1 H1 hu1 hH1⟩
  apply le_antisymm
  · rw [bridgeMin, dif_pos hS]
    obtain ⟨f, hf, hfeq⟩ := exists_minWeight (fun j : Fin (4 * r + 4 + 1) => bridgeH r s u2 H2 j) i S hS
    have hfc := hmin_cheap u2 H2 hu2 hH2 f hf (by rw [bridgeMin, dif_pos hS]; exact hfeq)
    rw [bridgeMin, dif_pos hS, ← hfeq]
    calc minWeight _ i S hS ≤ ∑ a : Fin i, bridgeH r s u1 H1 (f a) := minWeight_le _ i S hS hf
      _ = ∑ a : Fin i, bridgeH r s u2 H2 (f a) :=
          Finset.sum_congr rfl (fun a _ => hcheap_same (f a) (hfc a))
  · rw [bridgeMin, dif_pos hS]
    obtain ⟨f, hf, hfeq⟩ := exists_minWeight (fun j : Fin (4 * r + 4 + 1) => bridgeH r s u1 H1 j) i S hS
    have hfc := hmin_cheap u1 H1 hu1 hH1 f hf (by rw [bridgeMin, dif_pos hS]; exact hfeq)
    rw [bridgeMin, dif_pos hS, ← hfeq]
    calc minWeight _ i S hS ≤ ∑ a : Fin i, bridgeH r s u2 H2 (f a) := minWeight_le _ i S hS hf
      _ = ∑ a : Fin i, bridgeH r s u1 H1 (f a) :=
          Finset.sum_congr rfl (fun a _ => (hcheap_same (f a) (hfc a)).symm)

private lemma bridgeMin_star (r s u H : ℕ) (hr : 1 ≤ r) (hs : s = 3 ∨ s = 4)
    (hu : 1 ≤ u) (hH : u < H) :
    let Sstar := (r - 1) * (4 * r + 4) + s + 1
    bridgeMin r s u H r Sstar = u ∧
    (∀ f ∈ tupleSet (4 * r + 4) r Sstar,
      (∑ a : Fin r, bridgeH r s u H (f a)) = u →
      (Finset.univ.filter (fun a : Fin r => (f a : ℕ) = s + 1)).card = 1) := by
  let g := 4 * r + 4
  set Sstar := (r - 1) * g + s + 1
  have hSstar_le : Sstar ≤ r * g := by
    have hr1 : (r - 1) * g + g = r * g := by rw [← Nat.add_one_mul, Nat.sub_add_cancel hr]
    rcases hs with rfl | rfl <;> omega
  have hspec_lt : s + 1 < g + 1 := by rcases hs with rfl | rfl <;> omega
  -- Construct the witness tuple: (r-1) copies of g and 1 copy of s+1
  let fstar : Fin r → Fin (g + 1) := fun a =>
    if (a : ℕ) = 0 then ⟨s + 1, hspec_lt⟩ else ⟨g, Nat.lt_succ_self g⟩
  have hfstar_mem : fstar ∈ tupleSet g r Sstar := by
    rw [tupleSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have h0mem : (⟨0, hr⟩ : Fin r) ∈ Finset.univ := Finset.mem_univ _
    rw [← Finset.add_sum_erase Finset.univ _ h0mem]
    have h1 : (fstar ⟨0, hr⟩ : ℕ) = s + 1 := by simp [fstar]
    have h2 : ∑ a ∈ Finset.univ.erase (⟨0, hr⟩ : Fin r), (fstar a : ℕ) = (r - 1) * g := by
      have heq : ∑ a ∈ Finset.univ.erase (⟨0, hr⟩ : Fin r), (fstar a : ℕ) =
          ∑ _a ∈ Finset.univ.erase (⟨0, hr⟩ : Fin r), g := by
        apply Finset.sum_congr rfl
        intro a ha
        have hne : (a : ℕ) ≠ 0 := by
          intro h0; exact (Finset.ne_of_mem_erase ha) (Fin.ext h0)
        simp [fstar, hne]
      rw [heq, Finset.sum_const, Finset.card_erase_of_mem h0mem, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul]
    rw [h1, h2]; omega
  have hfstar_cost : ∑ a : Fin r, bridgeH r s u H (fstar a) = u := by
    have h0mem : (⟨0, hr⟩ : Fin r) ∈ Finset.univ := Finset.mem_univ _
    rw [← Finset.add_sum_erase Finset.univ _ h0mem]
    have h1 : bridgeH r s u H (fstar ⟨0, hr⟩) = u := by
      simp only [fstar, ↓reduceIte]
      exact bridgeH_special r s u H hr hs
    have h2 : ∑ a ∈ Finset.univ.erase (⟨0, hr⟩ : Fin r), bridgeH r s u H (fstar a) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      have hne : (a : ℕ) ≠ 0 := by
        intro h0; exact (Finset.ne_of_mem_erase ha) (Fin.ext h0)
      simp [fstar, hne, bridgeH, g]
    rw [h1, h2, add_zero]
  have hge_u : ∀ f ∈ tupleSet g r Sstar, u ≤ ∑ a : Fin r, bridgeH r s u H (f a) := by
    intro f hf
    by_cases hall : ∀ a, isCheap r s (f a) = true
    · exact False.elim (bridge_miss r s hr hs ⟨f, hf, hall⟩)
    · push_neg at hall
      obtain ⟨a, ha⟩ := hall
      have hnot : isCheap r s (f a) = false := Bool.eq_false_iff.mpr ha
      have hbig : u ≤ bridgeH r s u H (f a) := by
        unfold bridgeH
        have h0 : (f a : ℕ) ≠ 0 := by
          intro h0; rw [h0] at hnot; unfold isCheap at hnot; simp at hnot
        have hg : (f a : ℕ) ≠ 4 * r + 4 := by
          intro hg; rw [hg] at hnot; unfold isCheap at hnot; simp at hnot
        simp only [beq_iff_eq, Bool.or_eq_true, h0, hg, or_self, ↓reduceIte, hnot, Bool.false_eq_true]
        split_ifs <;> omega
      exact le_trans hbig (Finset.single_le_sum (f := fun b : Fin r => bridgeH r s u H (f b))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ a))
  have hbm : bridgeMin r s u H r Sstar = u := by
    rw [bridgeMin, dif_pos hSstar_le]
    apply le_antisymm
    · calc minWeight (fun j : Fin (4 * r + 4 + 1) => bridgeH r s u H j) r Sstar hSstar_le
          ≤ ∑ a : Fin r, bridgeH r s u H (fstar a) :=
            minWeight_le (fun j : Fin (4 * r + 4 + 1) => bridgeH r s u H j) r Sstar hSstar_le hfstar_mem
        _ = u := hfstar_cost
    · exact le_minWeight _ r Sstar hSstar_le u hge_u
  refine ⟨hbm, ?_⟩
  intro f hf hcost
  set M := Finset.univ.filter (fun a : Fin r => (f a : ℕ) = s + 1)
  have hM_le : M.card * u ≤ ∑ a : Fin r, bridgeH r s u H (f a) := by
    calc M.card * u = ∑ _a ∈ M, u := by simp [Finset.sum_const, smul_eq_mul]
      _ = ∑ a ∈ M, bridgeH r s u H (f a) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mem_filter] at ha
          rw [ha.2, bridgeH_special r s u H hr hs]
      _ ≤ ∑ a : Fin r, bridgeH r s u H (f a) :=
          Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  have hM_le1 : M.card ≤ 1 := by nlinarith
  have hM_ge1 : 1 ≤ M.card := by
    by_contra h0
    have hM0 : M.card = 0 := by omega
    have hne_spec : ∀ a : Fin r, (f a : ℕ) ≠ s + 1 := by
      intro a ha
      have : a ∈ M := Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩
      have : 0 < M.card := Finset.card_pos.mpr ⟨a, this⟩
      omega
    by_cases hall : ∀ a, isCheap r s (f a) = true
    · exact bridge_miss r s hr hs ⟨f, hf, hall⟩
    · push_neg at hall
      obtain ⟨a, ha⟩ := hall
      have hnot : isCheap r s (f a) = false := Bool.eq_false_iff.mpr ha
      have hbig : H ≤ bridgeH r s u H (f a) := by
        unfold bridgeH
        have h0' : (f a : ℕ) ≠ 0 := by
          intro h0'; rw [h0'] at hnot; unfold isCheap at hnot; simp at hnot
        have hg' : (f a : ℕ) ≠ 4 * r + 4 := by
          intro hg'; rw [hg'] at hnot; unfold isCheap at hnot; simp at hnot
        simp [h0', hg', hnot, hne_spec a]
      have := Finset.single_le_sum (f := fun b => bridgeH r s u H (f b))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
      omega
  omega

private lemma bridgeAlt_gt (r s u1 H1 u2 H2 i : ℕ) (hr : 1 ≤ r) (hs : s = 3 ∨ s = 4)
    (hlt : r < i) (hu1 : i < u1) (hH1 : i < H1) (hu2 : i < u2) (hH2 : i < H2) :
    bridgeAlt r s u1 H1 i = bridgeAlt r s u2 H2 i := by
  unfold bridgeAlt
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.mem_range, Nat.lt_succ_iff] at hS
  have hcov := bridge_cover r s i S hr hs (le_of_lt hlt) hS (by omega)
  rw [(bridgeMin_cheap_eq r s u1 H1 u2 H2 i S hS hu1 hH1 hu2 hH2 hcov).1]

private lemma bridgeAlt_eq (r s u1 H1 u2 H2 : ℕ) (hr : 1 ≤ r) (hs : s = 3 ∨ s = 4)
    (hu1 : r < u1) (hH1 : u1 < H1) (hu2 : r < u2) (hH2 : u2 < H2) :
    bridgeAlt r s u1 H1 r - (-1 : ℤ) ^ (s + 1) * (u1 : ℤ) =
    bridgeAlt r s u2 H2 r - (-1 : ℤ) ^ (s + 1) * (u2 : ℤ) := by
  set g := 4 * r + 4
  set Sstar := (r - 1) * g + s + 1
  have hSstar_mem : Sstar ∈ Finset.range (r * g + 1) := by
    rw [Finset.mem_range, Nat.lt_succ_iff]
    have hr1 : (r - 1) * g + g = r * g := by rw [← Nat.add_one_mul, Nat.sub_add_cancel hr]
    rcases hs with rfl | rfl <;> omega
  have hpar : (-1 : ℤ) ^ Sstar = (-1 : ℤ) ^ (s + 1) := by
    have h : Sstar = 2 * ((r - 1) * (2 * r + 2)) + (s + 1) := by dsimp only [Sstar, g]; ring
    rw [h, pow_add, pow_mul]; norm_num
  have expand : ∀ u H, r < u → u < H →
      bridgeAlt r s u H r - (-1 : ℤ) ^ (s + 1) * (u : ℤ) =
      ∑ S ∈ (Finset.range (r * g + 1)).erase Sstar, (-1 : ℤ) ^ S * (bridgeMin r s u H r S : ℤ) := by
    intro u H hu hH
    unfold bridgeAlt
    rw [← Finset.add_sum_erase _ _ hSstar_mem]
    rw [(bridgeMin_star r s u H hr hs (by omega) hH).1, hpar]
    ring
  rw [expand u1 H1 hu1 hH1, expand u2 H2 hu2 hH2]
  apply Finset.sum_congr rfl
  intro S hS
  have hne : S ≠ Sstar := Finset.ne_of_mem_erase hS
  have hSle : S ≤ r * g := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_of_mem_erase hS))
  have hcov := bridge_cover r s r S hr hs (le_refl r) hSle (by tauto)
  rw [(bridgeMin_cheap_eq r s u1 H1 u2 H2 r S hSle hu1 (by omega) hu2 (by omega) hcov).1]

/-! ### Section 4: Existential back-substitution for bridge parameters (uP, uM, H) -/

private lemma exists_bridge_params (n : ℕ) (hn : 1 ≤ n) :
    ∀ m ≤ n, ∃ (uP uM H : ℕ → ℕ),
      (∀ r, 1 ≤ r → r ≤ n → n < uP r ∧ n < uM r ∧ n * max (uP r) (uM r) + n < H r) ∧
      (∀ r, n - m < r → r ≤ n →
        ∑ k ∈ Finset.Icc 1 n,
          ((n + 1 : ℤ) * bridgeAlt k 3 (uP k) (H k) r + bridgeAlt k 4 (uM k) (H k) r) = 0) ∧
      (∀ r, n - m < r → r ≤ n →
        ∃ R : ℤ,
          (uM r : ℤ) = (n + 1 : ℤ) * (uP r : ℤ) + R ∧
          (∀ k, r < k → k ≤ n → 4 * n * (H k + R.natAbs + 1) + n < uP r) ∧
          4 * n * (R.natAbs + 2) + n < uP r ∧
          (∀ k, r < k → k ≤ n → 4 * n * max (uP r) (uM r) + 4 * n * H k + n < H r) ∧
          4 * n * max (uP r) (uM r) + 4 * n + n < H r) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨fun _ => n + 1, fun _ => n + 1, fun _ => (n + 1) * (n + 1) + n + 1, ?_, ?_, ?_⟩
    · intro r _ _
      simp only [max_self]
      refine ⟨by omega, by omega, by nlinarith⟩
    · intro r hr1 hr2; omega
    · intro r hr1 hr2; omega
  | succ m ih =>
    intro hm
    obtain ⟨uP, uM, H, hvalid, hzero, hgrow⟩ := ih (by omega)
    set r := n - m
    have hr1 : 1 ≤ r := by omega
    have hrn : r ≤ n := by omega
    have hrm : n - (m + 1) = r - 1 := by omega
    set tot_cur : ℤ := ∑ k ∈ Finset.Icc 1 n,
      ((n + 1 : ℤ) * bridgeAlt k 3 (uP k) (H k) r + bridgeAlt k 4 (uM k) (H k) r)
    set rem : ℤ := tot_cur - (n + 1 : ℤ) * (uP r : ℤ) + (uM r : ℤ)
    set maxH : ℕ := (Finset.Icc 1 n).sup H
    set up_new : ℕ := 4 * n * (maxH + rem.natAbs + 2) + n + 2
    set um_int : ℤ := (n + 1 : ℤ) * (up_new : ℤ) + rem
    have hum_pos : (n : ℤ) < um_int := by
      have hrem_lb : -(rem.natAbs : ℤ) ≤ rem := by rw [← Int.abs_eq_natAbs]; exact neg_abs_le rem
      have hup_ge : (rem.natAbs : ℤ) + (n : ℤ) < (up_new : ℤ) := by
        dsimp only [up_new]
        have h1 : 4 * n * (maxH + rem.natAbs + 2) ≥ rem.natAbs := by
          have : 1 * (maxH + rem.natAbs + 2) ≤ 4 * n * (maxH + rem.natAbs + 2) :=
            Nat.mul_le_mul_right _ (by omega)
          omega
        omega
      have hmul : (up_new : ℤ) ≤ (n + 1 : ℤ) * (up_new : ℤ) := by
        have : (1 : ℤ) ≤ (n + 1 : ℤ) := by omega
        nlinarith
      dsimp only [um_int]
      linarith
    set um_new : ℕ := um_int.toNat
    have hum_cast : (um_new : ℤ) = um_int := Int.toNat_of_nonneg (by omega)
    set H_new : ℕ := 4 * n * max up_new um_new + 4 * n * maxH + 4 * n + n + 2
    have hHnew_valid : n * max up_new um_new + n < H_new := by
      have h1 : n * max up_new um_new ≤ 4 * n * max up_new um_new :=
        Nat.mul_le_mul_right _ (by omega)
      dsimp only [H_new]; omega
    let uP' := Function.update uP r up_new
    let uM' := Function.update uM r um_new
    let H' := Function.update H r H_new
    have hvalid' : ∀ k, 1 ≤ k → k ≤ n → n < uP' k ∧ n < uM' k ∧ n * max (uP' k) (uM' k) + n < H' k := by
      intro k hk1 hkn
      by_cases hkr : k = r
      · subst hkr
        simp only [uP', uM', H', Function.update_self]
        exact ⟨by dsimp only [up_new]; omega, by omega, hHnew_valid⟩
      · simp only [uP', uM', H', Function.update_of_ne hkr]
        exact hvalid k hk1 hkn
    have hlt_of_valid : ∀ a b c : ℕ, n * max a b + n < c → a < c ∧ b < c ∧ n < c := by
      intro a b c h
      have h1 : max a b ≤ n * max a b := Nat.le_mul_of_pos_left _ hn
      have h2 := le_max_left a b
      have h3 := le_max_right a b
      omega
    refine ⟨uP', uM', H', hvalid', ?_, ?_⟩
    · intro i hi1 hin
      by_cases hir : i = r
      · subst hir
        have hsum_eq :
            ∑ k ∈ Finset.Icc 1 n,
              ((n + 1 : ℤ) * bridgeAlt k 3 (uP' k) (H' k) r + bridgeAlt k 4 (uM' k) (H' k) r) =
            tot_cur - ((n + 1 : ℤ) * bridgeAlt r 3 (uP r) (H r) r + bridgeAlt r 4 (uM r) (H r) r) +
              ((n + 1 : ℤ) * bridgeAlt r 3 up_new H_new r + bridgeAlt r 4 um_new H_new r) := by
          have hrmem : r ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hr1, hrn⟩
          have h1 := Finset.add_sum_erase (Finset.Icc 1 n)
            (fun k => (n + 1 : ℤ) * bridgeAlt k 3 (uP' k) (H' k) r + bridgeAlt k 4 (uM' k) (H' k) r) hrmem
          have h2 := Finset.add_sum_erase (Finset.Icc 1 n)
            (fun k => (n + 1 : ℤ) * bridgeAlt k 3 (uP k) (H k) r + bridgeAlt k 4 (uM k) (H k) r) hrmem
          have hrest :
              ∑ k ∈ (Finset.Icc 1 n).erase r,
                ((n + 1 : ℤ) * bridgeAlt k 3 (uP' k) (H' k) r + bridgeAlt k 4 (uM' k) (H' k) r) =
              ∑ k ∈ (Finset.Icc 1 n).erase r,
                ((n + 1 : ℤ) * bridgeAlt k 3 (uP k) (H k) r + bridgeAlt k 4 (uM k) (H k) r) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hne := Finset.ne_of_mem_erase hk
            simp [uP', uM', H', Function.update_of_ne hne]
          simp only [uP', uM', H', Function.update_self] at h1
          change _ = tot_cur - _ + _
          dsimp only [tot_cur]
          linarith
        rw [hsum_eq]
        have ⟨hv1, hv2, hv3⟩ := hvalid r hr1 hrn
        have ⟨hup_lt, hum_lt, _⟩ := hlt_of_valid up_new um_new H_new hHnew_valid
        have ⟨hup0_lt, hum0_lt, _⟩ := hlt_of_valid (uP r) (uM r) (H r) hv3
        have hP := bridgeAlt_eq r 3 up_new H_new (uP r) (H r) hr1 (Or.inl rfl)
          (by dsimp only [up_new]; omega) hup_lt (by omega) hup0_lt
        have hM := bridgeAlt_eq r 4 um_new H_new (uM r) (H r) hr1 (Or.inr rfl)
          (by omega) hum_lt (by omega) hum0_lt
        have hp3 : (-1 : ℤ) ^ (3 + 1) = 1 := by norm_num
        have hp4 : (-1 : ℤ) ^ (4 + 1) = -1 := by norm_num
        rw [hp3] at hP; rw [hp4] at hM
        have hP' : (n + 1 : ℤ) * (bridgeAlt r 3 up_new H_new r - (up_new : ℤ)) =
            (n + 1 : ℤ) * (bridgeAlt r 3 (uP r) (H r) r - (uP r : ℤ)) := by
          have : bridgeAlt r 3 up_new H_new r - (up_new : ℤ) = bridgeAlt r 3 (uP r) (H r) r - (uP r : ℤ) := by linarith
          rw [this]
        have hrem_def : rem = tot_cur - (n + 1 : ℤ) * (uP r : ℤ) + (uM r : ℤ) := rfl
        have hum_def : um_int = (n + 1 : ℤ) * (up_new : ℤ) + rem := rfl
        linarith
      · have hgt : r < i := by omega
        have heq_sum :
            ∑ k ∈ Finset.Icc 1 n,
              ((n + 1 : ℤ) * bridgeAlt k 3 (uP' k) (H' k) i + bridgeAlt k 4 (uM' k) (H' k) i) =
            ∑ k ∈ Finset.Icc 1 n,
              ((n + 1 : ℤ) * bridgeAlt k 3 (uP k) (H k) i + bridgeAlt k 4 (uM k) (H k) i) := by
          apply Finset.sum_congr rfl
          intro k hk
          by_cases hkr : k = r
          · subst hkr
            simp only [uP', uM', H', Function.update_self]
            have ⟨hv1, hv2, hv3⟩ := hvalid r hr1 hrn
            have ⟨_, _, hHnew_gt⟩ := hlt_of_valid up_new um_new H_new hHnew_valid
            have ⟨_, _, hH0_gt⟩ := hlt_of_valid (uP r) (uM r) (H r) hv3
            have hP := bridgeAlt_gt r 3 up_new H_new (uP r) (H r) i hr1 (Or.inl rfl) hgt
              (by dsimp only [up_new]; omega) (by omega) (by omega) (by omega)
            have hM := bridgeAlt_gt r 4 um_new H_new (uM r) (H r) i hr1 (Or.inr rfl) hgt
              (by omega) (by omega) (by omega) (by omega)
            rw [hP, hM]
          · simp [uP', uM', H', Function.update_of_ne hkr]
        rw [heq_sum]
        exact hzero i (by omega) hin
    · intro i hi1 hin
      by_cases hir : i = r
      · subst hir
        refine ⟨rem, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [uP', uM', Function.update_self]; exact hum_cast
        · intro k hkr hkn
          have hne : k ≠ r := by omega
          simp only [uP', H', Function.update_self, Function.update_of_ne hne]
          have hk_le : H k ≤ maxH := Finset.le_sup (f := H) (Finset.mem_Icc.mpr ⟨by omega, hkn⟩)
          have hmul := Nat.mul_le_mul_left (4 * n) (show H k + rem.natAbs + 1 ≤ maxH + rem.natAbs + 2 by omega)
          dsimp only [up_new]; omega
        · simp only [uP', Function.update_self]
          have hmul := Nat.mul_le_mul_left (4 * n) (show rem.natAbs + 2 ≤ maxH + rem.natAbs + 2 by omega)
          dsimp only [up_new]; omega
        · intro k hkr hkn
          have hne : k ≠ r := by omega
          simp only [uP', uM', H', Function.update_self, Function.update_of_ne hne]
          have hk_le : H k ≤ maxH := Finset.le_sup (f := H) (Finset.mem_Icc.mpr ⟨by omega, hkn⟩)
          have hmul := Nat.mul_le_mul_left (4 * n) hk_le
          dsimp only [H_new]; omega
        · simp only [uP', uM', H', Function.update_self]
          dsimp only [H_new]; omega
      · have hgt : r < i := by omega
        obtain ⟨R, hR1, hR2, hR3, hR4, hR5⟩ := hgrow i (by omega) hin
        refine ⟨R, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [uP', uM', Function.update_of_ne hir]; exact hR1
        · intro k hki hkn
          have hkr : k ≠ r := by omega
          simp only [uP', H', Function.update_of_ne hir, Function.update_of_ne hkr]
          exact hR2 k hki hkn
        · simp only [uP', Function.update_of_ne hir]; exact hR3
        · intro k hki hkn
          have hkr : k ≠ r := by omega
          simp only [uP', uM', H', Function.update_of_ne hir, Function.update_of_ne hkr]
          exact hR4 k hki hkn
        · simp only [uP', uM', H', Function.update_of_ne hir]; exact hR5

/-! ### Section 5: Stitching bridges, convex hull decoupling, and separation -/

private def rOf (n t : ℕ) : ℕ := t / (n + 2) + 1

private def sOf (n t : ℕ) : ℕ := if t % (n + 2) = n + 1 then 4 else 3

private def lenOf (n t : ℕ) : ℕ := 4 * rOf n t + 4

private def prefixLen (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => prefixLen n t + lenOf n t

private lemma lenOf_pos (n t : ℕ) : 8 ≤ lenOf n t := by
  unfold lenOf rOf
  have : 0 ≤ t / (n + 2) := Nat.zero_le _
  linarith

private lemma lenOf_even (n t : ℕ) : Even (lenOf n t) := by
  refine ⟨2 * rOf n t + 2, ?_⟩; unfold lenOf; omega

private lemma prefixLen_even (n t : ℕ) : Even (prefixLen n t) := by
  induction t with
  | zero => exact ⟨0, rfl⟩
  | succ t ih =>
    rcases ih with ⟨a, ha⟩
    rcases lenOf_even n t with ⟨b, hb⟩
    exact ⟨a + b, by simp [prefixLen, ha, hb]; omega⟩

private lemma prefixLen_strictMono (n : ℕ) : StrictMono (prefixLen n) := by
  apply strictMono_nat_of_lt_succ
  intro t
  have := lenOf_pos n t
  simp only [prefixLen]; omega

private lemma prefixLen_mono (n : ℕ) : Monotone (prefixLen n) :=
  (prefixLen_strictMono n).monotone

/-- Unique bridge index t such that prefixLen n t <= j < prefixLen n (t + 1). -/
private def bridgeOf (n j : ℕ) : ℕ :=
  ((Finset.range (j + 1)).filter (fun t => prefixLen n t ≤ j)).max' (by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
    simp [prefixLen])

private lemma prefixLen_ge_self (n t : ℕ) : t ≤ prefixLen n t := by
  induction t with
  | zero => simp [prefixLen]
  | succ t ih =>
    have := lenOf_pos n t
    simp only [prefixLen]; omega

private lemma bridgeOf_spec (n j : ℕ) :
    prefixLen n (bridgeOf n j) ≤ j ∧ j < prefixLen n (bridgeOf n j + 1) := by
  set S := (Finset.range (j + 1)).filter (fun t => prefixLen n t ≤ j)
  have hS : S.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by simp [prefixLen]⟩⟩
  have hm := Finset.max'_mem S hS
  rw [Finset.mem_filter] at hm
  refine ⟨hm.2, ?_⟩
  by_contra hle
  push_neg at hle
  have hlt : bridgeOf n j + 1 < j + 1 := by
    have := prefixLen_ge_self n (bridgeOf n j + 1)
    omega
  have hmem : bridgeOf n j + 1 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hle⟩
  have hle_max := Finset.le_max' S (bridgeOf n j + 1) hmem
  change bridgeOf n j + 1 ≤ bridgeOf n j at hle_max
  omega

private lemma bridgeOf_eq_of_bounds (n j t : ℕ)
    (h1 : prefixLen n t ≤ j) (h2 : j < prefixLen n (t + 1)) :
    bridgeOf n j = t := by
  have ⟨hb1, hb2⟩ := bridgeOf_spec n j
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have : prefixLen n (bridgeOf n j + 1) ≤ prefixLen n t := prefixLen_mono n (by omega)
    omega
  · have : prefixLen n (t + 1) ≤ prefixLen n (bridgeOf n j) := prefixLen_mono n (by omega)
    omega

private lemma bridgeOf_mono (n : ℕ) : Monotone (bridgeOf n) := by
  intro a b hab
  have ⟨ha1, ha2⟩ := bridgeOf_spec n a
  have ⟨hb1, hb2⟩ := bridgeOf_spec n b
  by_contra hlt
  push_neg at hlt
  have : prefixLen n (bridgeOf n b + 1) ≤ prefixLen n (bridgeOf n a) := prefixLen_mono n (by omega)
  omega

private def slopeAt (n j : ℕ) : ℕ := bridgeOf n j + 1

private def hullBase (n j : ℕ) : ℕ := ∑ x ∈ Finset.range j, slopeAt n x

private lemma hullBase_step (n j : ℕ) : hullBase n (j + 1) = hullBase n j + slopeAt n j :=
  Finset.sum_range_succ _ j

private lemma hullBase_on_bridge (n t u : ℕ) (hu : u ≤ lenOf n t) :
    hullBase n (prefixLen n t + u) = hullBase n (prefixLen n t) + (t + 1) * u := by
  induction u with
  | zero => simp
  | succ u ih =>
    rw [← add_assoc, hullBase_step, ih (by omega)]
    have hbo : bridgeOf n (prefixLen n t + u) = t := by
      apply bridgeOf_eq_of_bounds
      · omega
      · simp only [prefixLen]; omega
    unfold slopeAt
    rw [hbo]; ring

/-- Excess of hullBase above the tangent line of bridge t: strictly >= 1 outside [P_t, P_{t+1}]. -/
private lemma hullBase_tangent (n t j : ℕ) :
    (hullBase n j : ℤ) - ((hullBase n (prefixLen n t) : ℤ) + (t + 1 : ℤ) * ((j : ℤ) - (prefixLen n t : ℤ))) ≥
      (if prefixLen n t ≤ j ∧ j ≤ prefixLen n (t + 1) then 0 else 1) := by
  set PL := prefixLen n t
  set PR := prefixLen n (t + 1)
  by_cases hin : PL ≤ j ∧ j ≤ PR
  · rw [if_pos hin]
    have hj : j = PL + (j - PL) := by omega
    have hu : j - PL ≤ lenOf n t := by simp only [PR, prefixLen] at hin; omega
    have heq := hullBase_on_bridge n t (j - PL) hu
    rw [← hj] at heq
    have heq_z : (hullBase n j : ℤ) = (hullBase n PL : ℤ) + ((t : ℤ) + 1) * ((j : ℤ) - (PL : ℤ)) := by
      zify [hin.1] at heq; exact heq
    linarith
  · rw [if_neg hin]
    by_cases hlt : j < PL
    · -- j < PL: sum_{x in [j, PL)} slopeAt n x <= t * (PL - j)
      have hdiff : hullBase n PL = hullBase n j + ∑ x ∈ Finset.Ico j PL, slopeAt n x := by
        unfold hullBase
        rw [← Finset.sum_range_add_sum_Ico _ (le_of_lt hlt)]
      have hsum_le : ∑ x ∈ Finset.Ico j PL, slopeAt n x ≤ (PL - j) * t := by
        calc ∑ x ∈ Finset.Ico j PL, slopeAt n x
            ≤ ∑ _x ∈ Finset.Ico j PL, t := by
              apply Finset.sum_le_sum
              intro x hx
              rw [Finset.mem_Ico] at hx
              have ⟨hb1, _⟩ := bridgeOf_spec n x
              have hblt : bridgeOf n x < t := by
                by_contra hge; push_neg at hge
                have := prefixLen_mono n hge; omega
              unfold slopeAt; omega
          _ = (PL - j) * t := by simp [Finset.sum_const, smul_eq_mul]
      zify [le_of_lt hlt] at hdiff hsum_le
      nlinarith
    · -- j > PR: sum_{x in [PR, j)} slopeAt n x >= (t + 2) * (j - PR)
      have hgt : PR < j := by omega
      have hdiff : hullBase n j = hullBase n PR + ∑ x ∈ Finset.Ico PR j, slopeAt n x := by
        unfold hullBase
        rw [← Finset.sum_range_add_sum_Ico _ (le_of_lt hgt)]
      have hPR : hullBase n PR = hullBase n PL + (t + 1) * lenOf n t := by
        simpa [PR, prefixLen] using hullBase_on_bridge n t (lenOf n t) (le_refl _)
      have hsum_ge : (j - PR) * (t + 2) ≤ ∑ x ∈ Finset.Ico PR j, slopeAt n x := by
        calc (j - PR) * (t + 2) = ∑ _x ∈ Finset.Ico PR j, (t + 2) := by
              simp [Finset.sum_const, smul_eq_mul]
          _ ≤ ∑ x ∈ Finset.Ico PR j, slopeAt n x := by
              apply Finset.sum_le_sum
              intro x hx
              rw [Finset.mem_Ico] at hx
              have ⟨_, hb2⟩ := bridgeOf_spec n x
              have hbge : t + 1 ≤ bridgeOf n x := by
                by_contra hlt'; push_neg at hlt'
                have hle_t : bridgeOf n x + 1 ≤ t + 1 := by omega
                have := prefixLen_mono n hle_t; omega
              unfold slopeAt; omega
      have hPR_eq : PR = PL + lenOf n t := rfl
      zify [le_of_lt hgt] at hdiff hPR hsum_ge hPR_eq
      nlinarith

/-- Piecewise-linear convex hull extension at level i. -/
private def hullConv (n i S : ℕ) : ℕ :=
  i * hullBase n (prefixLen n (bridgeOf n (S / i))) +
  (bridgeOf n (S / i) + 1) * (S - i * prefixLen n (bridgeOf n (S / i)))

private lemma hullConv_on_bridge (n i t u : ℕ) (hi : 1 ≤ i) (hu : u ≤ i * lenOf n t) :
    hullConv n i (i * prefixLen n t + u) = i * hullBase n (prefixLen n t) + (t + 1) * u := by
  by_cases hlast : u = i * lenOf n t
  · subst hlast
    have hdiv : (i * prefixLen n t + i * lenOf n t) / i = prefixLen n (t + 1) := by
      rw [← mul_add, Nat.mul_div_cancel_left _ hi]; rfl
    unfold hullConv
    rw [hdiv]
    have hbo : bridgeOf n (prefixLen n (t + 1)) = t + 1 :=
      bridgeOf_eq_of_bounds n _ (t + 1) (le_refl _) (prefixLen_strictMono n (by omega))
    rw [hbo]
    have hsub : i * prefixLen n t + i * lenOf n t - i * prefixLen n (t + 1) = 0 := by
      simp [prefixLen, mul_add]
    rw [hsub, mul_zero, add_zero]
    have hb := hullBase_on_bridge n t (lenOf n t) (le_refl _)
    change i * hullBase n (prefixLen n t + lenOf n t) = _
    rw [hb]; ring
  · have hlt : u < i * lenOf n t := by omega
    have hdiv_ge : prefixLen n t ≤ (i * prefixLen n t + u) / i := by
      rw [Nat.le_div_iff_mul_le hi]; nlinarith
    have hdiv_lt : (i * prefixLen n t + u) / i < prefixLen n (t + 1) := by
      rw [Nat.div_lt_iff_lt_mul hi]
      simp only [prefixLen]; nlinarith
    have hbo : bridgeOf n ((i * prefixLen n t + u) / i) = t :=
      bridgeOf_eq_of_bounds n _ t hdiv_ge hdiv_lt
    unfold hullConv
    rw [hbo]
    have hsub : i * prefixLen n t + u - i * prefixLen n t = u := by omega
    rw [hsub]

/-- Alternating sum identity: LinDiff_i(hullBase) = 0 identically! -/
private lemma linDiff_hullBase_zero (n B i : ℕ) (hi : 1 ≤ i) :
    (i * hullBase n (prefixLen n B) : ℤ) +
    2 * ∑ S ∈ Finset.Ico 1 (i * prefixLen n B), (-1 : ℤ) ^ S * (hullConv n i S : ℤ) = 0 := by
  -- Prove by induction on B!
  induction B with
  | zero =>
    simp [prefixLen, hullBase]
  | succ B ih =>
    set PB := prefixLen n B
    set PB1 := prefixLen n (B + 1)
    set g := lenOf n B
    have hPB1 : PB1 = PB + g := rfl
    have hPB_even : Even PB := prefixLen_even n B
    have hg_even : Even g := lenOf_even n B
    have hiPB_even : Even (i * PB) := hPB_even.mul_left i
    have hig_even : Even (i * g) := hg_even.mul_left i
    have hIco_split :
        ∑ S ∈ Finset.Ico 1 (i * PB1), (-1 : ℤ) ^ S * (hullConv n i S : ℤ) =
        (∑ S ∈ Finset.Ico 1 (i * PB), (-1 : ℤ) ^ S * (hullConv n i S : ℤ)) +
        (∑ S ∈ Finset.Ico (max 1 (i * PB)) (i * PB1), (-1 : ℤ) ^ S * (hullConv n i S : ℤ)) := by
      by_cases hPB0 : i * PB = 0
      · have h1 : max 1 (i * PB) = 1 := by omega
        rw [h1, hPB0]; simp
      · have hle : 1 ≤ i * PB := by omega
        have hle2 : i * PB ≤ i * PB1 := Nat.mul_le_mul_left i (prefixLen_mono n (by omega))
        rw [max_eq_right hle, Finset.sum_Ico_consecutive _ hle hle2]
    -- Compute sum over u in [0, i*g) of (-1)^u * (C + (B+1)*u) = -(B+1) * (i*g / 2)!
    have hseg : ∀ (m : ℕ) (C a : ℤ),
        ∑ u ∈ Finset.range (2 * m), (-1 : ℤ) ^ u * (C + a * (u : ℤ)) = -(m : ℤ) * a := by
      intro m C a
      induction m with
      | zero => simp
      | succ m ihm =>
        rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ, ihm]
        have hp0 : (-1 : ℤ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
        have hp1 : (-1 : ℤ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
        rw [hp0, hp1]; push_cast; ring
    rcases hig_even with ⟨m, hm⟩
    have hm2 : i * g = 2 * m := by omega
    have hseg_sum :
        ∑ u ∈ Finset.range (i * g), (-1 : ℤ) ^ u * (hullConv n i (i * PB + u) : ℤ) =
        -(m : ℤ) * (B + 1 : ℤ) := by
      have hcongr : ∑ u ∈ Finset.range (i * g), (-1 : ℤ) ^ u * (hullConv n i (i * PB + u) : ℤ) =
          ∑ u ∈ Finset.range (2 * m), (-1 : ℤ) ^ u * ((i * hullBase n PB : ℤ) + (B + 1 : ℤ) * (u : ℤ)) := by
        rw [hm2]
        apply Finset.sum_congr rfl
        intro u hu
        rw [Finset.mem_range] at hu
        have hu_le : u ≤ i * lenOf n B := by change u ≤ i * g; omega
        rw [hullConv_on_bridge n i B u hi hu_le]
        push_cast; ring
      rw [hcongr, hseg]
    have hPB1_hull : (hullBase n PB1 : ℤ) = (hullBase n PB : ℤ) + (B + 1 : ℤ) * (g : ℤ) := by
      have := hullBase_on_bridge n B g (le_refl _)
      change hullBase n PB1 = hullBase n PB + (B + 1) * g at this
      exact_mod_cast this
    by_cases hPB0 : i * PB = 0
    · -- B = 0 case!
      have hB0 : PB = 0 := by nlinarith
      have hhb0 : hullBase n PB = 0 := by rw [hB0]; simp [hullBase]
      have hhc0 : hullConv n i 0 = 0 := by
        have h0 := hullConv_on_bridge n i B 0 hi (Nat.zero_le _)
        change hullConv n i (i * PB + 0) = i * hullBase n PB + (B + 1) * 0 at h0
        rw [hhb0, hB0] at h0
        simpa using h0
      have hrange_eq : ∑ S ∈ Finset.Ico 1 (i * PB1), (-1 : ℤ) ^ S * (hullConv n i S : ℤ) =
          ∑ u ∈ Finset.range (i * g), (-1 : ℤ) ^ u * (hullConv n i (i * PB + u) : ℤ) := by
        have hPB1_g : i * PB1 = i * g := by rw [hPB1, hB0, zero_add]
        rw [hPB1_g]
        simp only [hPB0, zero_add]
        have hpos : 0 < i * g := by have := lenOf_pos n B; nlinarith
        have hrg : Finset.range (i * g) = Finset.Ico 0 (i * g) := by ext x; simp
        rw [hrg, Finset.sum_eq_sum_Ico_succ_bot hpos]
        simp [hhc0]
      rw [hrange_eq, hseg_sum, hPB1_hull, hhb0]
      have hmg : (i : ℤ) * (g : ℤ) = 2 * (m : ℤ) := by exact_mod_cast hm2
      push_cast; nlinarith
    · have hle : 1 ≤ i * PB := by omega
      rw [hIco_split, max_eq_right hle]
      have hshift_sum :
          ∑ S ∈ Finset.Ico (i * PB) (i * PB1), (-1 : ℤ) ^ S * (hullConv n i S : ℤ) =
          ∑ u ∈ Finset.range (i * g), (-1 : ℤ) ^ u * (hullConv n i (i * PB + u) : ℤ) := by
        have hlen : i * PB1 = i * PB + i * g := by rw [hPB1, mul_add]
        rw [hlen, Finset.sum_Ico_eq_sum_range]
        rw [show i * PB + i * g - i * PB = i * g by omega]
        apply Finset.sum_congr rfl
        intro u _
        rcases hiPB_even with ⟨q, hq⟩
        have hpar : (-1 : ℤ) ^ (i * PB + u) = (-1 : ℤ) ^ u := by
          rw [pow_add, show i * PB = 2 * q by omega, pow_mul]; norm_num
        rw [hpar]
      rw [hshift_sum, hseg_sum, hPB1_hull]
      have hmg : (i * g : ℤ) = 2 * (m : ℤ) := by exact_mod_cast (by omega : i * g = 2 * m)
      nlinarith

/-- Local bridge height hVal stitched across all B = n * (n + 2) bridges. -/
private def hVal (n : ℕ) (uP uM H : ℕ → ℕ) (j : ℕ) : ℕ :=
  if j = prefixLen n (n * (n + 2)) then 0
  else
    bridgeH (rOf n (bridgeOf n j)) (sOf n (bridgeOf n j))
      (if sOf n (bridgeOf n j) = 3 then uP (rOf n (bridgeOf n j)) else uM (rOf n (bridgeOf n j)))
      (H (rOf n (bridgeOf n j))) (j - prefixLen n (bridgeOf n j))

private lemma hVal_on_bridge (n : ℕ) (uP uM H : ℕ → ℕ) (t loc : ℕ)
    (ht : t < n * (n + 2)) (hloc : loc ≤ lenOf n t) :
    hVal n uP uM H (prefixLen n t + loc) =
      bridgeH (rOf n t) (sOf n t) (if sOf n t = 3 then uP (rOf n t) else uM (rOf n t)) (H (rOf n t)) loc := by
  by_cases hlast : loc = lenOf n t
  · subst hlast
    have hRHS : bridgeH (rOf n t) (sOf n t)
        (if sOf n t = 3 then uP (rOf n t) else uM (rOf n t)) (H (rOf n t)) (lenOf n t) = 0 := by
      unfold bridgeH lenOf; simp
    rw [hRHS]
    unfold hVal
    by_cases htop : prefixLen n t + lenOf n t = prefixLen n (n * (n + 2))
    · rw [if_pos htop]
    · rw [if_neg htop]
      have hbo : bridgeOf n (prefixLen n t + lenOf n t) = t + 1 := by
        apply bridgeOf_eq_of_bounds
        · rfl
        · exact prefixLen_strictMono n (Nat.lt_succ_self (t + 1))
      rw [hbo]
      have hsub : prefixLen n t + lenOf n t - prefixLen n (t + 1) = 0 := by simp [prefixLen]
      rw [hsub]; simp [bridgeH]
  · have hlt : loc < lenOf n t := by omega
    have hne_top : prefixLen n t + loc ≠ prefixLen n (n * (n + 2)) := by
      have h1 : prefixLen n t + loc < prefixLen n (t + 1) := by simp [prefixLen]; omega
      have h2 : prefixLen n (t + 1) ≤ prefixLen n (n * (n + 2)) := prefixLen_mono n (by omega)
      omega
    unfold hVal
    rw [if_neg hne_top]
    have hbo : bridgeOf n (prefixLen n t + loc) = t := by
      apply bridgeOf_eq_of_bounds
      · omega
      · simp [prefixLen]; omega
    rw [hbo, show prefixLen n t + loc - prefixLen n t = loc by omega]

private lemma hVal_le_max (n : ℕ) (uP uM H : ℕ → ℕ) (Hmax : ℕ)
    (huP : ∀ r, 1 ≤ r → r ≤ n → uP r ≤ Hmax)
    (huM : ∀ r, 1 ≤ r → r ≤ n → uM r ≤ Hmax)
    (hH : ∀ r, 1 ≤ r → r ≤ n → H r ≤ Hmax)
    (h1 : 1 ≤ Hmax) (j : ℕ) (hj : j ≤ prefixLen n (n * (n + 2))) :
    hVal n uP uM H j ≤ Hmax := by
  unfold hVal
  by_cases htop : j = prefixLen n (n * (n + 2))
  · rw [if_pos htop]; omega
  · rw [if_neg htop]
    have hlt : j < prefixLen n (n * (n + 2)) := by omega
    have ⟨hb1, _⟩ := bridgeOf_spec n j
    have hbt : bridgeOf n j < n * (n + 2) := by
      by_contra hge; push_neg at hge
      have := prefixLen_mono n hge; omega
    have hr1 : 1 ≤ rOf n (bridgeOf n j) := by unfold rOf; exact Nat.succ_le_succ (Nat.zero_le _)
    have hrn : rOf n (bridgeOf n j) ≤ n := by
      unfold rOf
      have : bridgeOf n j / (n + 2) < n := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
      omega
    unfold bridgeH
    split_ifs <;> first | omega | exact huP _ hr1 hrn | exact huM _ hr1 hrn | exact hH _ hr1 hrn

/-- Full stitched vector v(j) = K * hullBase(j) + hVal(j). -/
private def vFull (n K : ℕ) (uP uM H : ℕ → ℕ) (j : Fin (prefixLen n (n * (n + 2)) + 1)) : ℕ :=
  K * hullBase n j + hVal n uP uM H j

private lemma vFull_zero (n K : ℕ) (uP uM H : ℕ → ℕ) :
    vFull n K uP uM H ⟨0, Nat.succ_pos _⟩ = 0 := by
  have hb0 : bridgeOf n 0 = 0 := bridgeOf_eq_of_bounds n 0 0 (by simp [prefixLen]) (by
    have := lenOf_pos n 0; simp [prefixLen]; omega)
  unfold vFull hullBase hVal
  simp [hb0, prefixLen, bridgeH]

private lemma vFull_top (n K : ℕ) (uP uM H : ℕ → ℕ) :
    vFull n K uP uM H ⟨prefixLen n (n * (n + 2)), Nat.lt_succ_self _⟩ =
      K * hullBase n (prefixLen n (n * (n + 2))) := by
  unfold vFull hVal; simp

/-- Bridge Decoupling Lemma: for K > i * Hmax, every minimal tuple at S in [i*P_t, i*P_{t+1}]
    stays inside bridge t, and minWeight equals K * hullConv + bridgeMin! -/
private lemma bridge_decoupling (n K Hmax : ℕ) (uP uM H : ℕ → ℕ)
    (hh_le : ∀ j ≤ prefixLen n (n * (n + 2)), hVal n uP uM H j ≤ Hmax)
    (i t u : ℕ) (hi : 1 ≤ i) (ht : t < n * (n + 2)) (hu : u ≤ i * lenOf n t)
    (hK : i * Hmax < K) :
    let twoD := prefixLen n (n * (n + 2))
    let S := i * prefixLen n t + u
    have hS : S ≤ i * twoD := by
      have h1 : prefixLen n t + lenOf n t ≤ twoD := by
        change prefixLen n (t + 1) ≤ twoD; exact prefixLen_mono n (by omega)
      have h2 := Nat.mul_le_mul_left i h1
      rw [mul_add] at h2; omega
    minWeight (vFull n K uP uM H) i S hS =
      K * hullConv n i S +
      bridgeMin (rOf n t) (sOf n t) (if sOf n t = 3 then uP (rOf n t) else uM (rOf n t)) (H (rOf n t)) i u ∧
    ∀ f ∈ tupleSet twoD i S,
      (∑ a : Fin i, vFull n K uP uM H (f a)) = minWeight (vFull n K uP uM H) i S hS →
      (∀ a : Fin i, prefixLen n t ≤ (f a : ℕ) ∧ (f a : ℕ) ≤ prefixLen n (t + 1)) ∧
      (∑ a : Fin i, bridgeH (rOf n t) (sOf n t)
          (if sOf n t = 3 then uP (rOf n t) else uM (rOf n t)) (H (rOf n t))
          ((f a : ℕ) - prefixLen n t)) =
        bridgeMin (rOf n t) (sOf n t) (if sOf n t = 3 then uP (rOf n t) else uM (rOf n t)) (H (rOf n t)) i u := by
  set twoD := prefixLen n (n * (n + 2))
  set PL := prefixLen n t
  set PR := prefixLen n (t + 1)
  set g := lenOf n t
  set S := i * PL + u
  set r := rOf n t
  set s := sOf n t
  set ut := if s = 3 then uP r else uM r
  have hPR_le : PR ≤ twoD := prefixLen_mono n (by omega)
  have hS : S ≤ i * twoD := by
    have h1 : PL + g ≤ twoD := hPR_le
    have h2 := Nat.mul_le_mul_left i h1
    rw [mul_add] at h2; omega
  have hhc : hullConv n i S = i * hullBase n PL + (t + 1) * u :=
    hullConv_on_bridge n i t u hi hu
  -- Key lower bound on any tuple f in tupleSet twoD i S:
  have htuple_lb : ∀ f ∈ tupleSet twoD i S,
      ((∑ a : Fin i, hullBase n (f a)) : ℤ) - (hullConv n i S : ℤ) ≥
        ∑ a : Fin i, (if PL ≤ (f a : ℕ) ∧ (f a : ℕ) ≤ PR then (0 : ℤ) else 1) := by
    intro f hf
    rw [tupleSet, Finset.mem_filter] at hf
    have hsum_j : (∑ a : Fin i, ((f a : ℕ) : ℤ)) = (S : ℤ) := by exact_mod_cast hf.2
    have hsum_tang := Finset.sum_le_sum (s := Finset.univ)
      (fun a _ => hullBase_tangent n t (f a : ℕ))
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum_tang
    rw [hsum_j] at hsum_tang
    rw [hhc]
    have hS_z : (S : ℤ) = (i : ℤ) * (PL : ℤ) + (u : ℤ) := by exact_mod_cast (rfl : S = i * PL + u)
    rw [hS_z] at hsum_tang
    push_cast
    linarith
  -- Construct a tuple inside bridge t realizing K * hullConv + bridgeMin!
  have hbm_pos : u ≤ i * (4 * r + 4) := hu
  obtain ⟨floc, hfloc_mem, hfloc_eq⟩ := exists_minWeight (fun j : Fin (4 * r + 4 + 1) => bridgeH r s ut (H r) j) i u hbm_pos
  let fglob : Fin i → Fin (twoD + 1) := fun a =>
    ⟨PL + (floc a : ℕ), by have := (floc a).isLt; simp only [PR, prefixLen, lenOf] at hPR_le; omega⟩
  have hfglob_mem : fglob ∈ tupleSet twoD i S := by
    rw [tupleSet, Finset.mem_filter] at hfloc_mem ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [fglob, Fin.val_mk, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, hfloc_mem.2]
    rfl
  have hfglob_cost : ∑ a : Fin i, vFull n K uP uM H (fglob a) =
      K * hullConv n i S + bridgeMin r s ut (H r) i u := by
    rw [bridgeMin, dif_pos hbm_pos, ← hfloc_eq, hhc]
    simp only [vFull, fglob, Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 : ∑ a : Fin i, hullBase n (PL + (floc a : ℕ)) = i * hullBase n PL + (t + 1) * u := by
      have hcongr : ∑ a : Fin i, hullBase n (PL + (floc a : ℕ)) =
          ∑ a : Fin i, (hullBase n PL + (t + 1) * (floc a : ℕ)) := by
        apply Finset.sum_congr rfl
        intro a _
        exact hullBase_on_bridge n t (floc a : ℕ) (Nat.lt_succ_iff.mp (floc a).isLt)
      rw [hcongr, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul]
      rw [tupleSet, Finset.mem_filter] at hfloc_mem
      rw [hfloc_mem.2]
    have h2 : ∑ a : Fin i, hVal n uP uM H (PL + (floc a : ℕ)) =
        ∑ a : Fin i, bridgeH r s ut (H r) (floc a : ℕ) := by
      apply Finset.sum_congr rfl
      intro a _
      exact hVal_on_bridge n uP uM H t (floc a : ℕ) ht (Nat.lt_succ_iff.mp (floc a).isLt)
    rw [h1, h2]
  have hbm_le_iH : bridgeMin r s ut (H r) i u ≤ i * Hmax := by
    rw [bridgeMin, dif_pos hbm_pos, ← hfloc_eq]
    calc ∑ a : Fin i, bridgeH r s ut (H r) (floc a : ℕ)
        = ∑ a : Fin i, hVal n uP uM H (PL + (floc a : ℕ)) := by
            apply Finset.sum_congr rfl; intro a _
            exact (hVal_on_bridge n uP uM H t (floc a : ℕ) ht (Nat.lt_succ_iff.mp (floc a).isLt)).symm
      _ ≤ ∑ _a : Fin i, Hmax := by
            apply Finset.sum_le_sum; intro a _
            apply hh_le
            have := (floc a).isLt
            simp only [PR, prefixLen, lenOf] at hPR_le; omega
      _ = i * Hmax := by simp [Finset.sum_const, smul_eq_mul]
  -- Now prove every tuple f in tupleSet twoD i S has cost >= K * hullConv + bridgeMin,
  -- and strictly > if any f a falls outside [PL, PR]!
  have hgen_lb : ∀ f ∈ tupleSet twoD i S,
      ((¬ ∀ a : Fin i, PL ≤ (f a : ℕ) ∧ (f a : ℕ) ≤ PR) →
        K * hullConv n i S + bridgeMin r s ut (H r) i u < ∑ a : Fin i, vFull n K uP uM H (f a)) ∧
      ((∀ a : Fin i, PL ≤ (f a : ℕ) ∧ (f a : ℕ) ≤ PR) →
        ∑ a : Fin i, vFull n K uP uM H (f a) =
          K * hullConv n i S + ∑ a : Fin i, bridgeH r s ut (H r) ((f a : ℕ) - PL) ∧
        bridgeMin r s ut (H r) i u ≤ ∑ a : Fin i, bridgeH r s ut (H r) ((f a : ℕ) - PL)) := by
    intro f hf
    constructor
    · intro hout
      push_neg at hout
      obtain ⟨a0, ha0⟩ := hout
      have hbad : ¬ (PL ≤ (f a0 : ℕ) ∧ (f a0 : ℕ) ≤ PR) := by omega
      have h1 : (1 : ℤ) ≤ ∑ a : Fin i, (if PL ≤ (f a : ℕ) ∧ (f a : ℕ) ≤ PR then (0 : ℤ) else 1) := by
        calc (1 : ℤ) = (if PL ≤ (f a0 : ℕ) ∧ (f a0 : ℕ) ≤ PR then (0 : ℤ) else 1) := by simp [hbad]
          _ ≤ _ := Finset.single_le_sum
              (f := fun a : Fin i => if PL ≤ (f a : ℕ) ∧ (f a : ℕ) ≤ PR then (0 : ℤ) else 1)
              (fun a _ => by split_ifs <;> norm_num) (Finset.mem_univ a0)
      have hlb := htuple_lb f hf
      have hge_z : (hullConv n i S : ℤ) + 1 ≤ ((∑ a : Fin i, hullBase n (f a) : ℕ) : ℤ) := by
        push_cast at hlb ⊢; linarith
      have hge : hullConv n i S + 1 ≤ ∑ a : Fin i, hullBase n (f a) := by exact_mod_cast hge_z
      have hcost : K * (hullConv n i S + 1) ≤ ∑ a : Fin i, vFull n K uP uM H (f a) := by
        simp only [vFull, Finset.sum_add_distrib, ← Finset.mul_sum]
        calc K * (hullConv n i S + 1) ≤ K * ∑ a : Fin i, hullBase n (f a) := Nat.mul_le_mul_left K hge
          _ ≤ _ := Nat.le_add_right _ _
      nlinarith
    · intro hin
      have h1 : ∑ a : Fin i, hullBase n (f a) = hullConv n i S := by
        rw [hhc]
        have hcongr : ∑ a : Fin i, hullBase n (f a) =
            ∑ a : Fin i, (hullBase n PL + (t + 1) * ((f a : ℕ) - PL)) := by
          apply Finset.sum_congr rfl
          intro a _
          have ha := hin a
          have hsub : PL + ((f a : ℕ) - PL) = (f a : ℕ) := by omega
          have hle : (f a : ℕ) - PL ≤ g := by simp only [PR, prefixLen] at ha; omega
          have := hullBase_on_bridge n t ((f a : ℕ) - PL) hle
          rwa [hsub] at this
        rw [hcongr, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul]
        rw [tupleSet, Finset.mem_filter] at hf
        have hsum_sub : ∑ a : Fin i, ((f a : ℕ) - PL) = u := by
          have : ∑ a : Fin i, ((f a : ℕ) - PL) + ∑ _a : Fin i, PL = ∑ a : Fin i, (f a : ℕ) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl; intro a _; have := hin a; omega
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
          omega
        rw [hsum_sub]
      have h2 : ∑ a : Fin i, hVal n uP uM H (f a) =
          ∑ a : Fin i, bridgeH r s ut (H r) ((f a : ℕ) - PL) := by
        apply Finset.sum_congr rfl
        intro a _
        have ha := hin a
        have hsub : PL + ((f a : ℕ) - PL) = (f a : ℕ) := by omega
        have hle : (f a : ℕ) - PL ≤ g := by simp only [PR, prefixLen] at ha; omega
        have := hVal_on_bridge n uP uM H t ((f a : ℕ) - PL) ht hle
        rwa [hsub] at this
      have hcost_eq : ∑ a : Fin i, vFull n K uP uM H (f a) =
          K * hullConv n i S + ∑ a : Fin i, bridgeH r s ut (H r) ((f a : ℕ) - PL) := by
        simp only [vFull, Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2]
      refine ⟨hcost_eq, ?_⟩
      let floc' : Fin i → Fin (4 * r + 4 + 1) := fun a =>
        ⟨(f a : ℕ) - PL, by have ha := hin a; simp only [PR, prefixLen, lenOf] at ha; omega⟩
      have hfloc'_mem : floc' ∈ tupleSet (4 * r + 4) i u := by
        rw [tupleSet, Finset.mem_filter] at hf ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        have : ∑ a : Fin i, ((f a : ℕ) - PL) + ∑ _a : Fin i, PL = ∑ a : Fin i, (f a : ℕ) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro a _; have := hin a; omega
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
        change ∑ a : Fin i, ((f a : ℕ) - PL) = u
        omega
      rw [bridgeMin, dif_pos hbm_pos]
      exact minWeight_le (fun j : Fin (4 * r + 4 + 1) => bridgeH r s ut (H r) j) i u hbm_pos hfloc'_mem
  have hmin_eq : minWeight (vFull n K uP uM H) i S hS =
      K * hullConv n i S + bridgeMin r s ut (H r) i u := by
    apply le_antisymm
    · rw [← hfglob_cost]; exact minWeight_le _ i S hS hfglob_mem
    · apply le_minWeight
      intro f hf
      by_cases hin : ∀ a : Fin i, PL ≤ (f a : ℕ) ∧ (f a : ℕ) ≤ PR
      · have ⟨h1, h2⟩ := (hgen_lb f hf).2 hin; omega
      · exact le_of_lt ((hgen_lb f hf).1 hin)
  refine ⟨hmin_eq, ?_⟩
  intro f hf hfeq
  rw [hmin_eq] at hfeq
  have hin : ∀ a : Fin i, PL ≤ (f a : ℕ) ∧ (f a : ℕ) ≤ PR := by
    by_contra hout
    have := (hgen_lb f hf).1 hout
    omega
  refine ⟨hin, ?_⟩
  have ⟨h1, _⟩ := (hgen_lb f hf).2 hin
  have h2 : ∑ a : Fin i, bridgeH r s ut (H r) ((f a : ℕ) - PL) = bridgeMin r s ut (H r) i u := by omega
  exact h2

/-- LinDiff_i(vFull) = 0 for all 1 <= i <= n! -/
private lemma linDiff_vFull_zero (n K Hmax : ℕ) (uP uM H : ℕ → ℕ)
    (hh_le : ∀ j ≤ prefixLen n (n * (n + 2)), hVal n uP uM H j ≤ Hmax)
    (hK : n * Hmax < K)
    (hzero : ∀ i, 1 ≤ i → i ≤ n →
      ∑ r ∈ Finset.Icc 1 n,
        ((n + 1 : ℤ) * bridgeAlt r 3 (uP r) (H r) i + bridgeAlt r 4 (uM r) (H r) i) = 0)
    (i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    let twoD := prefixLen n (n * (n + 2))
    (i * vFull n K uP uM H ⟨twoD, Nat.lt_succ_self twoD⟩ : ℤ) +
    2 * ∑ S ∈ Finset.Ico 1 (i * twoD),
      (-1 : ℤ) ^ S *
        (if h : S ≤ i * twoD then (minWeight (vFull n K uP uM H) i S h : ℤ) else 0) = 0 := by
  dsimp only
  set B := n * (n + 2)
  set twoD := prefixLen n B
  have htop := vFull_top n K uP uM H
  rw [htop]
  -- Split Ico 1 (i * twoD) into the B bridges [i * prefixLen n t, i * prefixLen n (t+1))!
  -- Better: prove for any M <= B by induction on M that the sum over [1, i * prefixLen n M)
  -- equals K * (hull sum) + sum_{t < M} bridgeAlt_t!
  have hsum_bridges : ∀ M ≤ B,
      ∑ S ∈ Finset.Ico 1 (i * prefixLen n M),
        (-1 : ℤ) ^ S *
          (if h : S ≤ i * twoD then (minWeight (vFull n K uP uM H) i S h : ℤ) else 0) =
      (K : ℤ) * (∑ S ∈ Finset.Ico 1 (i * prefixLen n M), (-1 : ℤ) ^ S * (hullConv n i S : ℤ)) +
      ∑ t ∈ Finset.range M,
        bridgeAlt (rOf n t) (sOf n t)
          (if sOf n t = 3 then uP (rOf n t) else uM (rOf n t)) (H (rOf n t)) i := by
    intro M hMB
    induction M with
    | zero => simp [prefixLen]
    | succ M ihM =>
      set PM := prefixLen n M
      set PM1 := prefixLen n (M + 1)
      set g := lenOf n M
      have hPM_even : Even (i * PM) := (prefixLen_even n M).mul_left i
      have hPM1_eq : i * PM1 = i * PM + i * g := by change i * (PM + g) = _; ring
      have hbridge_zero_end :
          bridgeMin (rOf n M) (sOf n M)
            (if sOf n M = 3 then uP (rOf n M) else uM (rOf n M)) (H (rOf n M)) i 0 = 0 ∧
          bridgeMin (rOf n M) (sOf n M)
            (if sOf n M = 3 then uP (rOf n M) else uM (rOf n M)) (H (rOf n M)) i (i * g) = 0 := by
        constructor
        · rw [bridgeMin, dif_pos (Nat.zero_le _)]
          apply Nat.eq_zero_of_le_zero
          have hf0 : (fun _ : Fin i => ⟨0, Nat.succ_pos _⟩) ∈ tupleSet (4 * rOf n M + 4) i 0 := by
            rw [tupleSet_zero]; simp
          calc minWeight _ i 0 _ ≤ ∑ _a : Fin i, bridgeH _ _ _ _ 0 := minWeight_le _ i 0 _ hf0
            _ = 0 := by simp [bridgeH]
        · have hig_eq : i * g = i * (4 * rOf n M + 4) := rfl
          rw [bridgeMin, dif_pos (le_of_eq hig_eq)]
          apply Nat.eq_zero_of_le_zero
          have hfg : (fun _ : Fin i => ⟨4 * rOf n M + 4, Nat.lt_succ_self _⟩) ∈
              tupleSet (4 * rOf n M + 4) i (i * (4 * rOf n M + 4)) := by
            rw [tupleSet_top]; simp
          calc minWeight _ i (i * g) _ ≤ ∑ _a : Fin i, bridgeH _ _ _ _ (4 * rOf n M + 4) :=
                minWeight_le _ i (i * g) _ hfg
            _ = 0 := by simp [bridgeH]
      have hseg :
          ∑ u ∈ Finset.range (i * g),
            (-1 : ℤ) ^ (i * PM + u) *
              (if h : i * PM + u ≤ i * twoD then (minWeight (vFull n K uP uM H) i (i * PM + u) h : ℤ) else 0) =
          (K : ℤ) * (∑ u ∈ Finset.range (i * g), (-1 : ℤ) ^ (i * PM + u) * (hullConv n i (i * PM + u) : ℤ)) +
          bridgeAlt (rOf n M) (sOf n M)
            (if sOf n M = 3 then uP (rOf n M) else uM (rOf n M)) (H (rOf n M)) i := by
        have hba : bridgeAlt (rOf n M) (sOf n M)
            (if sOf n M = 3 then uP (rOf n M) else uM (rOf n M)) (H (rOf n M)) i =
            ∑ u ∈ Finset.range (i * g), (-1 : ℤ) ^ u *
              (bridgeMin (rOf n M) (sOf n M)
                (if sOf n M = 3 then uP (rOf n M) else uM (rOf n M)) (H (rOf n M)) i u : ℤ) := by
          unfold bridgeAlt
          change ∑ u ∈ Finset.range (i * g + 1), _ = _
          rw [Finset.sum_range_succ, hbridge_zero_end.2]
          simp
        rw [hba, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro u hu
        rw [Finset.mem_range] at hu
        have hdec := (bridge_decoupling n K Hmax uP uM H hh_le i M u hi1 (by omega) (le_of_lt hu)
          (by nlinarith)).1
        have hle : i * PM + u ≤ i * twoD := by
          have : PM1 ≤ twoD := prefixLen_mono n (by omega)
          nlinarith
        rw [dif_pos hle, hdec]
        rcases hPM_even with ⟨q, hq⟩
        have hpar : (-1 : ℤ) ^ (i * PM + u) = (-1 : ℤ) ^ u := by
          rw [pow_add, show i * PM = 2 * q by omega, pow_mul]; norm_num
        rw [hpar]; push_cast; ring
      by_cases hM0 : M = 0
      · subst hM0
        simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton]
        have hPM0 : PM = 0 := rfl
        have hpos : 0 < i * g := by have := lenOf_pos n 0; nlinarith
        have h0_min : minWeight (vFull n K uP uM H) i 0 (Nat.zero_le _) = 0 := by
          apply Nat.eq_zero_of_le_zero
          have hf0 : (fun _ : Fin i => ⟨0, Nat.succ_pos _⟩) ∈ tupleSet twoD i 0 := by
            rw [tupleSet_zero]; simp
          calc minWeight _ i 0 _ ≤ ∑ _a : Fin i, vFull n K uP uM H ⟨0, Nat.succ_pos _⟩ :=
                minWeight_le _ i 0 _ hf0
            _ = 0 := by
                have hz : vFull n K uP uM H ⟨0, Nat.succ_pos twoD⟩ = 0 := vFull_zero n K uP uM H
                rw [Finset.sum_const, smul_eq_mul, hz, mul_zero]
        have h0_hc : hullConv n i 0 = 0 := by
          have := hullConv_on_bridge n i 0 0 hi1 (Nat.zero_le _)
          simp [prefixLen, hullBase] at this; exact this
        have hrew1 : ∑ S ∈ Finset.Ico 1 (i * PM1),
            (-1 : ℤ) ^ S * (if h : S ≤ i * twoD then (minWeight (vFull n K uP uM H) i S h : ℤ) else 0) =
            ∑ u ∈ Finset.range (i * g), (-1 : ℤ) ^ (i * PM + u) *
              (if h : i * PM + u ≤ i * twoD then (minWeight (vFull n K uP uM H) i (i * PM + u) h : ℤ) else 0) := by
          rw [hPM1_eq, hPM0, mul_zero, zero_add]
          have hrg : Finset.range (i * g) = Finset.Ico 0 (i * g) := by ext x; simp
          rw [hrg, Finset.sum_eq_sum_Ico_succ_bot hpos]
          simp [h0_min]
        have hrew2 : ∑ S ∈ Finset.Ico 1 (i * PM1), (-1 : ℤ) ^ S * (hullConv n i S : ℤ) =
            ∑ u ∈ Finset.range (i * g), (-1 : ℤ) ^ (i * PM + u) * (hullConv n i (i * PM + u) : ℤ) := by
          rw [hPM1_eq, hPM0, mul_zero, zero_add]
          have hrg : Finset.range (i * g) = Finset.Ico 0 (i * g) := by ext x; simp
          rw [hrg, Finset.sum_eq_sum_Ico_succ_bot hpos]
          simp [h0_hc]
        rw [hrew1, hrew2, hseg]
      · have hPM_pos : 1 ≤ i * PM := by
          have h1 : 1 ≤ PM := le_trans (by omega : 1 ≤ M) (prefixLen_ge_self n M)
          nlinarith
        have hle_PM : i * PM ≤ i * PM1 := by omega
        rw [← Finset.sum_Ico_consecutive _ hPM_pos hle_PM,
            ← Finset.sum_Ico_consecutive (f := fun S => (-1 : ℤ) ^ S * (hullConv n i S : ℤ)) hPM_pos hle_PM]
        rw [ihM (by omega), Finset.sum_range_succ]
        have hshift1 :
            ∑ S ∈ Finset.Ico (i * PM) (i * PM1),
              (-1 : ℤ) ^ S * (if h : S ≤ i * twoD then (minWeight (vFull n K uP uM H) i S h : ℤ) else 0) =
            ∑ u ∈ Finset.range (i * g), (-1 : ℤ) ^ (i * PM + u) *
              (if h : i * PM + u ≤ i * twoD then (minWeight (vFull n K uP uM H) i (i * PM + u) h : ℤ) else 0) := by
          rw [hPM1_eq, Finset.sum_Ico_eq_sum_range, show i * PM + i * g - i * PM = i * g by omega]
        have hshift2 :
            ∑ S ∈ Finset.Ico (i * PM) (i * PM1), (-1 : ℤ) ^ S * (hullConv n i S : ℤ) =
            ∑ u ∈ Finset.range (i * g), (-1 : ℤ) ^ (i * PM + u) * (hullConv n i (i * PM + u) : ℤ) := by
          rw [hPM1_eq, Finset.sum_Ico_eq_sum_range, show i * PM + i * g - i * PM = i * g by omega]
        rw [hshift1, hshift2, hseg]
        ring
  rw [hsum_bridges B (le_refl B)]
  -- Group sum over t in range (n * (n + 2)) by r = t / (n + 2) + 1 in Icc 1 n!
  have hgroup :
      ∑ t ∈ Finset.range B,
        bridgeAlt (rOf n t) (sOf n t)
          (if sOf n t = 3 then uP (rOf n t) else uM (rOf n t)) (H (rOf n t)) i =
      ∑ r ∈ Finset.Icc 1 n,
        ((n + 1 : ℤ) * bridgeAlt r 3 (uP r) (H r) i + bridgeAlt r 4 (uM r) (H r) i) := by
    have hsplit : ∀ m : ℕ,
        ∑ t ∈ Finset.range (m * (n + 2)),
          bridgeAlt (rOf n t) (sOf n t)
            (if sOf n t = 3 then uP (rOf n t) else uM (rOf n t)) (H (rOf n t)) i =
        ∑ r ∈ Finset.Icc 1 m,
          ((n + 1 : ℤ) * bridgeAlt r 3 (uP r) (H r) i + bridgeAlt r 4 (uM r) (H r) i) := by
      intro m
      induction m with
      | zero => simp
      | succ m ihm =>
        rw [Nat.succ_mul, Finset.sum_range_add, ihm]
        have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hIcc, Finset.sum_insert (by simp), add_comm]
        congr 1
        rw [Finset.sum_range_succ]
        have hlast : rOf n (m * (n + 2) + (n + 1)) = m + 1 ∧ sOf n (m * (n + 2) + (n + 1)) = 4 := by
          unfold rOf sOf
          have hdiv : (m * (n + 2) + (n + 1)) / (n + 2) = m := by
            rw [mul_comm m (n + 2), Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega)]; omega
          have hmod : (m * (n + 2) + (n + 1)) % (n + 2) = n + 1 := by
            rw [mul_comm m (n + 2), Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
          simp [hdiv, hmod]
        rw [hlast.1, hlast.2]
        simp only [show (4 : ℕ) ≠ 3 by decide, ↓reduceIte]
        congr 1
        have hfirst : ∀ c ∈ Finset.range (n + 1),
            rOf n (m * (n + 2) + c) = m + 1 ∧ sOf n (m * (n + 2) + c) = 3 := by
          intro c hc
          rw [Finset.mem_range] at hc
          unfold rOf sOf
          have hdiv : (m * (n + 2) + c) / (n + 2) = m := by
            rw [mul_comm m (n + 2), Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega)]; omega
          have hmod : (m * (n + 2) + c) % (n + 2) = c := by
            rw [mul_comm m (n + 2), Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
          have hne : c ≠ n + 1 := by omega
          simp [hdiv, hmod, hne]
        calc ∑ c ∈ Finset.range (n + 1),
              bridgeAlt (rOf n (m * (n + 2) + c)) (sOf n (m * (n + 2) + c))
                (if sOf n (m * (n + 2) + c) = 3 then uP (rOf n (m * (n + 2) + c))
                  else uM (rOf n (m * (n + 2) + c)))
                (H (rOf n (m * (n + 2) + c))) i
            = ∑ _c ∈ Finset.range (n + 1), bridgeAlt (m + 1) 3 (uP (m + 1)) (H (m + 1)) i := by
              apply Finset.sum_congr rfl
              intro c hc
              have ⟨h1, h2⟩ := hfirst c hc
              rw [h1, h2]; simp
          _ = (n + 1 : ℤ) * bridgeAlt (m + 1) 3 (uP (m + 1)) (H (m + 1)) i := by
              simp [Finset.sum_const, smul_eq_mul]
    exact hsplit n
  rw [hgroup, hzero i hi1 hin, add_zero]
  have hhull := linDiff_hullBase_zero n B i hi1
  push_cast
  have : (K : ℤ) * ((i * hullBase n twoD : ℤ) +
      2 * ∑ S ∈ Finset.Ico 1 (i * twoD), (-1 : ℤ) ^ S * (hullConv n i S : ℤ)) = 0 := by
    rw [hhull, mul_zero]
  linarith

/-! ### Section 5b: Separation Lemma on vFull -/

/-- Global index of the special negative point m = 5 inside bridge B_r^-. -/
private def negBridgeIdx (n r : ℕ) : ℕ := (r - 1) * (n + 2) + (n + 1)

private def negSpecPos (n r : ℕ) : ℕ := prefixLen n (negBridgeIdx n r) + 5

private lemma negBridgeIdx_lt (n r : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ n) :
    negBridgeIdx n r < n * (n + 2) := by
  unfold negBridgeIdx
  have h1 : (r - 1) + 1 ≤ n := by omega
  nlinarith

private lemma negBridgeIdx_r_s (n r : ℕ) (hr1 : 1 ≤ r) :
    rOf n (negBridgeIdx n r) = r ∧ sOf n (negBridgeIdx n r) = 4 := by
  unfold negBridgeIdx rOf sOf
  have hdiv : ((r - 1) * (n + 2) + (n + 1)) / (n + 2) = r - 1 := by
    rw [mul_comm (r - 1) (n + 2), Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega)]; omega
  have hmod : ((r - 1) * (n + 2) + (n + 1)) % (n + 2) = n + 1 := by
    rw [mul_comm (r - 1) (n + 2), Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  simp [hdiv, hmod]; omega

private lemma negSpecPos_lt (n r : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ n) :
    negSpecPos n r < prefixLen n (n * (n + 2)) := by
  unfold negSpecPos
  have hlt := negBridgeIdx_lt n r hr1 hrn
  have hlen : 8 ≤ lenOf n (negBridgeIdx n r) := lenOf_pos n _
  have h1 : prefixLen n (negBridgeIdx n r) + 5 < prefixLen n (negBridgeIdx n r + 1) := by
    simp [prefixLen]; omega
  have h2 : prefixLen n (negBridgeIdx n r + 1) ≤ prefixLen n (n * (n + 2)) :=
    prefixLen_mono n (by omega)
  omega

private lemma negSpecPos_injective (n r1 r2 : ℕ) (h1 : 1 ≤ r1) (h2 : 1 ≤ r2)
    (heq : negSpecPos n r1 = negSpecPos n r2) : r1 = r2 := by
  unfold negSpecPos at heq
  have hb1 : bridgeOf n (prefixLen n (negBridgeIdx n r1) + 5) = negBridgeIdx n r1 := by
    apply bridgeOf_eq_of_bounds
    · omega
    · have := lenOf_pos n (negBridgeIdx n r1); simp [prefixLen]; omega
  have hb2 : bridgeOf n (prefixLen n (negBridgeIdx n r2) + 5) = negBridgeIdx n r2 := by
    apply bridgeOf_eq_of_bounds
    · omega
    · have := lenOf_pos n (negBridgeIdx n r2); simp [prefixLen]; omega
  have hbi : negBridgeIdx n r1 = negBridgeIdx n r2 := by rw [← hb1, heq, hb2]
  have h1' := (negBridgeIdx_r_s n r1 h1).1
  have h2' := (negBridgeIdx_r_s n r2 h2).1
  rw [hbi] at h1'
  omega

/-- Classification of each index j into its level r and height category (cheap / uP / uM / H). -/
private def hVal_cat (n : ℕ) (j : ℕ) : ℕ × ℕ :=
  if j = prefixLen n (n * (n + 2)) then (0, 0)
  else if (j - prefixLen n (bridgeOf n j) == 0 ||
           j - prefixLen n (bridgeOf n j) == 4 * rOf n (bridgeOf n j) + 4 ||
           isCheap (rOf n (bridgeOf n j)) (sOf n (bridgeOf n j)) (j - prefixLen n (bridgeOf n j)))
    then (rOf n (bridgeOf n j), 0)
  else if j - prefixLen n (bridgeOf n j) == sOf n (bridgeOf n j) + 1
    then (rOf n (bridgeOf n j), if sOf n (bridgeOf n j) = 3 then 1 else 2)
  else (rOf n (bridgeOf n j), 3)

private lemma hVal_eq_of_cat (n : ℕ) (uP uM H : ℕ → ℕ) (j : ℕ) :
    let (r, cat) := hVal_cat n j
    (cat = 0 → hVal n uP uM H j ≤ 1) ∧
    (cat = 1 → hVal n uP uM H j = uP r) ∧
    (cat = 2 → hVal n uP uM H j = uM r) ∧
    (cat = 3 → hVal n uP uM H j = H r) := by
  dsimp only
  unfold hVal_cat hVal bridgeH
  split_ifs <;> simp_all

private lemma hVal_cat_fst_mem (n j : ℕ) (hj : j ≤ prefixLen n (n * (n + 2)))
    (h2 : (hVal_cat n j).2 ≠ 0) : 1 ≤ (hVal_cat n j).1 ∧ (hVal_cat n j).1 ≤ n := by
  have hne : j ≠ prefixLen n (n * (n + 2)) := by
    intro heq; rw [heq] at h2; unfold hVal_cat at h2; simp at h2
  have hlt : j < prefixLen n (n * (n + 2)) := lt_of_le_of_ne hj hne
  have ⟨hb1, _⟩ := bridgeOf_spec n j
  have hbt : bridgeOf n j < n * (n + 2) := by
    by_contra hge; push_neg at hge
    have := prefixLen_mono n hge; omega
  have hdiv : bridgeOf n j / (n + 2) < n :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < n + 2)).mpr (by omega)
  have hfst : (hVal_cat n j).1 = rOf n (bridgeOf n j) := by
    unfold hVal_cat; rw [if_neg hne]; split_ifs <;> rfl
  rw [hfst]; unfold rOf
  exact ⟨Nat.succ_le_succ (Nat.zero_le _), by omega⟩

private lemma hVal_cat_eq_two_iff (n r : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ n)
    (j : ℕ) (hj : j ≤ prefixLen n (n * (n + 2))) :
    hVal_cat n j = (r, 2) ↔ j = negSpecPos n r := by
  constructor
  · intro h
    unfold hVal_cat at h
    split_ifs at h with htop hc hspec hs3
    · simp at h
    · simp at h
    · simp at h
    · simp only [Prod.mk.injEq, and_true] at h
      have hne_top : j < prefixLen n (n * (n + 2)) := by omega
      have ⟨hb1, hb2⟩ := bridgeOf_spec n j
      have hbt : bridgeOf n j < n * (n + 2) := by
        by_contra hge; push_neg at hge
        have := prefixLen_mono n hge; omega
      have hs4 : sOf n (bridgeOf n j) = 4 := by
        unfold sOf at hs3 ⊢; split_ifs at hs3 ⊢ <;> omega
      have hmod : bridgeOf n j % (n + 2) = n + 1 := by
        unfold sOf at hs4; split_ifs at hs4 with hm; exact hm; omega
      have hdiv : bridgeOf n j / (n + 2) = r - 1 := by
        unfold rOf at h; omega
      have hteq : bridgeOf n j = negBridgeIdx n r := by
        unfold negBridgeIdx
        have := Nat.div_add_mod (bridgeOf n j) (n + 2)
        have hmul : (n + 2) * (bridgeOf n j / (n + 2)) = (r - 1) * (n + 2) := by rw [hdiv, mul_comm]
        omega
      have hloc : j - prefixLen n (bridgeOf n j) = 5 := by
        simp only [beq_iff_eq] at hspec; rw [hs4] at hspec; exact hspec
      unfold negSpecPos
      rw [← hteq]; omega
    · simp at h
  · intro hj_eq
    subst hj_eq
    have hlt := negSpecPos_lt n r hr1 hrn
    have hne : negSpecPos n r ≠ prefixLen n (n * (n + 2)) := by omega
    have hbo : bridgeOf n (negSpecPos n r) = negBridgeIdx n r := by
      apply bridgeOf_eq_of_bounds
      · unfold negSpecPos; omega
      · unfold negSpecPos; have := lenOf_pos n (negBridgeIdx n r); simp [prefixLen]; omega
    have ⟨hr_eq, hs_eq⟩ := negBridgeIdx_r_s n r hr1
    unfold hVal_cat
    rw [if_neg hne, hbo, hr_eq, hs_eq]
    have hsub : negSpecPos n r - prefixLen n (negBridgeIdx n r) = 5 := by unfold negSpecPos; omega
    rw [hsub]
    have hnc : isCheap r 4 5 = false := isCheap_special_false r 4 hr1 (Or.inr rfl)
    have hne_end : (5 : ℕ) ≠ 4 * r + 4 := by omega
    simp [hnc, hne_end]

/-- Separation Lemma: two i-tuples with the same vFull-sum have the exact same count
    on every negSpecPos n r (1 <= r <= n)! -/
private lemma separation_vFull (n K Hmax : ℕ) (uP uM H : ℕ → ℕ)
    (hn : 1 ≤ n)
    (hh_le : ∀ j ≤ prefixLen n (n * (n + 2)), hVal n uP uM H j ≤ Hmax)
    (hK : 2 * n * Hmax < K)
    (hgrow : ∀ r, 1 ≤ r → r ≤ n →
      ∃ R : ℤ,
        (uM r : ℤ) = (n + 1 : ℤ) * (uP r : ℤ) + R ∧
        (∀ k, r < k → k ≤ n → 4 * n * (H k + R.natAbs + 1) + n < uP r) ∧
        4 * n * (R.natAbs + 2) + n < uP r ∧
        (∀ k, r < k → k ≤ n → 4 * n * max (uP r) (uM r) + 4 * n * H k + n < H r) ∧
        4 * n * max (uP r) (uM r) + 4 * n + n < H r)
    (hvalid : ∀ r, 1 ≤ r → r ≤ n → n < uP r ∧ n < uM r ∧ n * max (uP r) (uM r) + n < H r)
    (i : ℕ) (hi : i ≤ n)
    (f g : Fin i → Fin (prefixLen n (n * (n + 2)) + 1))
    (hweq : (∑ a : Fin i, vFull n K uP uM H (f a)) = ∑ a : Fin i, vFull n K uP uM H (g a)) :
    ∀ r, 1 ≤ r → r ≤ n →
      (Finset.univ.filter (fun a : Fin i => (f a : ℕ) = negSpecPos n r)).card =
      (Finset.univ.filter (fun a : Fin i => (g a : ℕ) = negSpecPos n r)).card := by
  -- Step 1: Deduce sum hVal f = sum hVal g by mod K!
  have hh_eq : (∑ a : Fin i, hVal n uP uM H (f a)) = ∑ a : Fin i, hVal n uP uM H (g a) := by
    simp only [vFull, Finset.sum_add_distrib, ← Finset.mul_sum] at hweq
    have hf_le : ∑ a : Fin i, hVal n uP uM H (f a) ≤ i * Hmax := by
      calc _ ≤ ∑ _a : Fin i, Hmax := Finset.sum_le_sum (fun a _ => hh_le _ (Nat.lt_succ_iff.mp (f a).isLt))
        _ = i * Hmax := by simp [Finset.sum_const, smul_eq_mul]
    have hg_le : ∑ a : Fin i, hVal n uP uM H (g a) ≤ i * Hmax := by
      calc _ ≤ ∑ _a : Fin i, Hmax := Finset.sum_le_sum (fun a _ => hh_le _ (Nat.lt_succ_iff.mp (g a).isLt))
        _ = i * Hmax := by simp [Finset.sum_const, smul_eq_mul]
    have hK_gt : i * Hmax < K := by nlinarith
    have hmod := congrArg (· % K) hweq
    rw [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
    exact hmod
  -- Step 2: Count each category (r, cat) for cat in {1, 2, 3}
  let cntF : ℕ → ℕ → ℕ := fun r cat => (Finset.univ.filter (fun a : Fin i => hVal_cat n (f a) = (r, cat))).card
  let cntG : ℕ → ℕ → ℕ := fun r cat => (Finset.univ.filter (fun a : Fin i => hVal_cat n (g a) = (r, cat))).card
  -- Prove by strong induction on r in [1, n] that cntF r cat = cntG r cat for cat in {1, 2, 3}!
  have hall_eq : ∀ r, 1 ≤ r → r ≤ n → cntF r 1 = cntG r 1 ∧ cntF r 2 = cntG r 2 ∧ cntF r 3 = cntG r 3 := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ihr =>
      intro hr1 hrn
      have hprev : ∀ k, 1 ≤ k → k < r →
          cntF k 1 = cntG k 1 ∧ cntF k 2 = cntG k 2 ∧ cntF k 3 = cntG k 3 :=
        fun k hk1 hkr => ihr k hkr hk1 (by omega)
      -- Split ∑ hVal into levels < r, level r (cat 1, 2, 3), and everything else (cat 0 or level > r)!
      have hdecomp : ∀ (p : Fin i → Fin (prefixLen n (n * (n + 2)) + 1)),
          (∑ a : Fin i, (hVal n uP uM H (p a) : ℤ)) =
          (∑ k ∈ Finset.Ico 1 r,
            (((Finset.univ.filter (fun a => hVal_cat n (p a) = (k, 1))).card : ℤ) * (uP k : ℤ) +
             ((Finset.univ.filter (fun a => hVal_cat n (p a) = (k, 2))).card : ℤ) * (uM k : ℤ) +
             ((Finset.univ.filter (fun a => hVal_cat n (p a) = (k, 3))).card : ℤ) * (H k : ℤ))) +
          (((Finset.univ.filter (fun a => hVal_cat n (p a) = (r, 1))).card : ℤ) * (uP r : ℤ) +
           ((Finset.univ.filter (fun a => hVal_cat n (p a) = (r, 2))).card : ℤ) * (uM r : ℤ) +
           ((Finset.univ.filter (fun a => hVal_cat n (p a) = (r, 3))).card : ℤ) * (H r : ℤ)) +
          ∑ a ∈ Finset.univ.filter (fun a => (hVal_cat n (p a)).2 = 0 ∨ r < (hVal_cat n (p a)).1),
            (hVal n uP uM H (p a) : ℤ) := by
        intro p
        -- Partition Fin i by membership in the tail set vs the Icc 1 r sets (cat 1, 2, 3)
        let tail := Finset.univ.filter (fun a : Fin i => (hVal_cat n (p a)).2 = 0 ∨ r < (hVal_cat n (p a)).1)
        let head := Finset.univ.filter (fun a : Fin i => ¬ ((hVal_cat n (p a)).2 = 0 ∨ r < (hVal_cat n (p a)).1))
        have hpart_ht : ∑ a : Fin i, (hVal n uP uM H (p a) : ℤ) =
            (∑ a ∈ head, (hVal n uP uM H (p a) : ℤ)) + (∑ a ∈ tail, (hVal n uP uM H (p a) : ℤ)) := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
            (fun a : Fin i => (hVal_cat n (p a)).2 = 0 ∨ r < (hVal_cat n (p a)).1), add_comm]
        rw [hpart_ht]
        congr 1
        have hcat_range : ∀ a ∈ head, (hVal_cat n (p a)).1 ∈ Finset.Icc 1 r ∧
            ((hVal_cat n (p a)).2 = 1 ∨ (hVal_cat n (p a)).2 = 2 ∨ (hVal_cat n (p a)).2 = 3) := by
          intro a ha
          rw [Finset.mem_filter] at ha
          have hnot := ha.2
          push_neg at hnot
          have hcat_def : ∀ j, (hVal_cat n j).2 ≤ 3 ∧ ((hVal_cat n j).2 ≠ 0 → 1 ≤ (hVal_cat n j).1) := by
            intro j
            unfold hVal_cat
            split_ifs <;> dsimp only
            · exact ⟨by omega, fun h => False.elim (h rfl)⟩
            · exact ⟨by omega, fun h => False.elim (h rfl)⟩
            · exact ⟨by omega, fun _ => by unfold rOf; exact Nat.succ_le_succ (Nat.zero_le _)⟩
            · exact ⟨by omega, fun _ => by unfold rOf; exact Nat.succ_le_succ (Nat.zero_le _)⟩
            · exact ⟨by omega, fun _ => by unfold rOf; exact Nat.succ_le_succ (Nat.zero_le _)⟩
          have ⟨h1, h2⟩ := hcat_def (p a)
          refine ⟨Finset.mem_Icc.mpr ⟨h2 hnot.1, hnot.2⟩, by omega⟩
        -- Group head by k = (hVal_cat n (p a)).1 in Icc 1 r
        rw [← Finset.sum_fiberwise_of_maps_to (s := head) (t := Finset.Icc 1 r)
          (g := fun a => (hVal_cat n (p a)).1) (fun a ha => (hcat_range a ha).1)]
        have hIcc_split : Finset.Icc 1 r = insert r (Finset.Ico 1 r) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]; omega
        rw [hIcc_split, Finset.sum_insert (by simp), add_comm]
        have hfiber : ∀ k ∈ Finset.Icc 1 r,
            ∑ a ∈ head.filter (fun a => (hVal_cat n (p a)).1 = k), (hVal n uP uM H (p a) : ℤ) =
            ((Finset.univ.filter (fun a => hVal_cat n (p a) = (k, 1))).card : ℤ) * (uP k : ℤ) +
            ((Finset.univ.filter (fun a => hVal_cat n (p a) = (k, 2))).card : ℤ) * (uM k : ℤ) +
            ((Finset.univ.filter (fun a => hVal_cat n (p a) = (k, 3))).card : ℤ) * (H k : ℤ) := by
          intro k hk
          rw [Finset.mem_Icc] at hk
          let F1 := Finset.univ.filter (fun a : Fin i => hVal_cat n (p a) = (k, 1))
          let F2 := Finset.univ.filter (fun a : Fin i => hVal_cat n (p a) = (k, 2))
          let F3 := Finset.univ.filter (fun a : Fin i => hVal_cat n (p a) = (k, 3))
          have hset : head.filter (fun a => (hVal_cat n (p a)).1 = k) = F1 ∪ (F2 ∪ F3) := by
            ext a
            simp only [F1, F2, F3, head, Finset.mem_filter, Finset.mem_union, Finset.mem_univ,
              true_and, Prod.ext_iff]
            constructor
            · rintro ⟨hnot, hk_eq⟩
              have hcat_le : (hVal_cat n (p a)).2 ≤ 3 := by unfold hVal_cat; split_ifs <;> simp
              push_neg at hnot
              omega
            · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> refine ⟨?_, h1⟩ <;> omega
          have hd1 : Disjoint F1 (F2 ∪ F3) := by
            rw [Finset.disjoint_left]; intro a h1 h23
            simp only [F1, F2, F3, Finset.mem_union, Finset.mem_filter] at h1 h23
            rcases h23 with h2 | h3
            · rw [h1.2] at h2; simp at h2
            · rw [h1.2] at h3; simp at h3
          have hd2 : Disjoint F2 F3 := by
            rw [Finset.disjoint_left]; intro a h2 h3
            simp only [F2, F3, Finset.mem_filter] at h2 h3
            rw [h2.2] at h3; simp at h3
          rw [hset, Finset.sum_union hd1, Finset.sum_union hd2, ← add_assoc]
          have hs1 : ∑ a ∈ F1, (hVal n uP uM H (p a) : ℤ) = (F1.card : ℤ) * (uP k : ℤ) := by
            have : ∑ a ∈ F1, (hVal n uP uM H (p a) : ℤ) = ∑ _a ∈ F1, (uP k : ℤ) := by
              apply Finset.sum_congr rfl; intro a ha
              have hca := (Finset.mem_filter.mp ha).2
              have hv := hVal_eq_of_cat n uP uM H (p a)
              rw [hca] at hv; exact_mod_cast hv.2.1 rfl
            rw [this, Finset.sum_const, nsmul_eq_mul]
          have hs2 : ∑ a ∈ F2, (hVal n uP uM H (p a) : ℤ) = (F2.card : ℤ) * (uM k : ℤ) := by
            have : ∑ a ∈ F2, (hVal n uP uM H (p a) : ℤ) = ∑ _a ∈ F2, (uM k : ℤ) := by
              apply Finset.sum_congr rfl; intro a ha
              have hca := (Finset.mem_filter.mp ha).2
              have hv := hVal_eq_of_cat n uP uM H (p a)
              rw [hca] at hv; exact_mod_cast hv.2.2.1 rfl
            rw [this, Finset.sum_const, nsmul_eq_mul]
          have hs3 : ∑ a ∈ F3, (hVal n uP uM H (p a) : ℤ) = (F3.card : ℤ) * (H k : ℤ) := by
            have : ∑ a ∈ F3, (hVal n uP uM H (p a) : ℤ) = ∑ _a ∈ F3, (H k : ℤ) := by
              apply Finset.sum_congr rfl; intro a ha
              have hca := (Finset.mem_filter.mp ha).2
              have hv := hVal_eq_of_cat n uP uM H (p a)
              rw [hca] at hv; exact_mod_cast hv.2.2.2 rfl
            rw [this, Finset.sum_const, nsmul_eq_mul]
          rw [hs1, hs2, hs3]
        congr 1
        · apply Finset.sum_congr rfl
          intro k hk
          exact hfiber k (Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hk).1, le_of_lt (Finset.mem_Ico.mp hk).2⟩)
        · exact hfiber r (Finset.mem_Icc.mpr ⟨hr1, le_refl r⟩)
      -- Bound each tail term by maxH_gt = max (1, sup_{k > r} H k)
      set maxH_gt : ℕ := max 1 ((Finset.Ioc r n).sup H)
      have htail_le : ∀ (p : Fin i → Fin (prefixLen n (n * (n + 2)) + 1)),
          ∑ a ∈ Finset.univ.filter (fun a => (hVal_cat n (p a)).2 = 0 ∨ r < (hVal_cat n (p a)).1),
            (hVal n uP uM H (p a) : ℤ) ≤ (n : ℤ) * (maxH_gt : ℤ) := by
        intro p
        have hterm : ∀ a ∈ Finset.univ.filter (fun a : Fin i => (hVal_cat n (p a)).2 = 0 ∨ r < (hVal_cat n (p a)).1),
            (hVal n uP uM H (p a) : ℤ) ≤ (maxH_gt : ℤ) := by
          intro a ha
          rw [Finset.mem_filter] at ha
          have hv := hVal_eq_of_cat n uP uM H (p a)
          rcases ha.2 with hc0 | hgt
          · have h1 := hv.1 hc0
            have : 1 ≤ maxH_gt := le_max_left _ _
            omega
          · have hkn : (hVal_cat n (p a)).1 ≤ n := by
              by_cases htop : (p a : ℕ) = prefixLen n (n * (n + 2))
              · unfold hVal_cat; rw [if_pos htop]; dsimp only; omega
              · have hlt : (p a : ℕ) < prefixLen n (n * (n + 2)) :=
                  lt_of_le_of_ne (Nat.lt_succ_iff.mp (p a).isLt) htop
                have ⟨hb1, _⟩ := bridgeOf_spec n (p a)
                have hbt : bridgeOf n (p a) < n * (n + 2) := by
                  by_contra hge; push_neg at hge
                  have := prefixLen_mono n hge; omega
                have hdiv : bridgeOf n (p a) / (n + 2) < n :=
                  (Nat.div_lt_iff_lt_mul (by omega : 0 < n + 2)).mpr (by omega)
                have hfst : (hVal_cat n (p a)).1 = rOf n (bridgeOf n (p a)) := by
                  unfold hVal_cat; rw [if_neg htop]; split_ifs <;> rfl
                rw [hfst]; unfold rOf; omega
            have hHle : H (hVal_cat n (p a)).1 ≤ maxH_gt :=
              le_trans (Finset.le_sup (f := H) (Finset.mem_Ioc.mpr ⟨hgt, hkn⟩)) (le_max_right _ _)
            have ⟨_, _, hH_gt⟩ := hvalid (hVal_cat n (p a)).1 (by omega) hkn
            have hcat_le : (hVal_cat n (p a)).2 ≤ 3 := by unfold hVal_cat; split_ifs <;> simp
            have hmul_max : max (uP (hVal_cat n (p a)).1) (uM (hVal_cat n (p a)).1) ≤
                n * max (uP (hVal_cat n (p a)).1) (uM (hVal_cat n (p a)).1) :=
              Nat.le_mul_of_pos_left _ hn
            rcases (by omega : (hVal_cat n (p a)).2 = 0 ∨ (hVal_cat n (p a)).2 = 1 ∨
                (hVal_cat n (p a)).2 = 2 ∨ (hVal_cat n (p a)).2 = 3) with h0 | h1 | h2 | h3
            · have := hv.1 h0; have : 1 ≤ maxH_gt := le_max_left _ _; omega
            · have := hv.2.1 h1; have := le_max_left (uP (hVal_cat n (p a)).1) (uM (hVal_cat n (p a)).1); omega
            · have := hv.2.2.1 h2; have := le_max_right (uP (hVal_cat n (p a)).1) (uM (hVal_cat n (p a)).1); omega
            · have := hv.2.2.2 h3; omega
        let Sfilt := Finset.univ.filter (fun a : Fin i => (hVal_cat n (p a)).2 = 0 ∨ r < (hVal_cat n (p a)).1)
        calc ∑ a ∈ Sfilt, (hVal n uP uM H (p a) : ℤ)
            ≤ ∑ _a ∈ Sfilt, (maxH_gt : ℤ) := Finset.sum_le_sum hterm
          _ = (Sfilt.card : ℤ) * (maxH_gt : ℤ) := by simp only [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (n : ℤ) * (maxH_gt : ℤ) := by
              apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
              have hcard_le : Sfilt.card ≤ n := by
                calc Sfilt.card ≤ (Finset.univ : Finset (Fin i)).card := Finset.card_le_card (Finset.filter_subset _ _)
                  _ = i := by simp
                  _ ≤ n := hi
              exact_mod_cast hcard_le
      have htail_nonneg : ∀ (p : Fin i → Fin (prefixLen n (n * (n + 2)) + 1)),
          0 ≤ ∑ a ∈ Finset.univ.filter (fun a => (hVal_cat n (p a)).2 = 0 ∨ r < (hVal_cat n (p a)).1),
            (hVal n uP uM H (p a) : ℤ) := fun p => Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
      -- Subtract hdecomp f and hdecomp g!
      have hheq_z : (∑ a : Fin i, (hVal n uP uM H (f a) : ℤ)) =
          ∑ a : Fin i, (hVal n uP uM H (g a) : ℤ) := by exact_mod_cast hh_eq
      rw [hdecomp f, hdecomp g] at hheq_z
      have hIco_eq :
          ∑ k ∈ Finset.Ico 1 r,
            (((cntF k 1 : ℤ) * (uP k : ℤ) + (cntF k 2 : ℤ) * (uM k : ℤ) + (cntF k 3 : ℤ) * (H k : ℤ))) =
          ∑ k ∈ Finset.Ico 1 r,
            (((cntG k 1 : ℤ) * (uP k : ℤ) + (cntG k 2 : ℤ) * (uM k : ℤ) + (cntG k 3 : ℤ) * (H k : ℤ))) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_Ico] at hk
        have ⟨h1, h2, h3⟩ := hprev k hk.1 hk.2
        rw [h1, h2, h3]
      set c1d : ℤ := (cntF r 1 : ℤ) - (cntG r 1 : ℤ)
      set c2d : ℤ := (cntF r 2 : ℤ) - (cntG r 2 : ℤ)
      set c3d : ℤ := (cntF r 3 : ℤ) - (cntG r 3 : ℤ)
      set tailDiff : ℤ :=
        (∑ a ∈ Finset.univ.filter (fun a => (hVal_cat n (g a)).2 = 0 ∨ r < (hVal_cat n (g a)).1),
          (hVal n uP uM H (g a) : ℤ)) -
        (∑ a ∈ Finset.univ.filter (fun a => (hVal_cat n (f a)).2 = 0 ∨ r < (hVal_cat n (f a)).1),
          (hVal n uP uM H (f a) : ℤ))
      have hbal : c1d * (uP r : ℤ) + c2d * (uM r : ℤ) + c3d * (H r : ℤ) = tailDiff := by
        change _ = _ at hIco_eq
        linarith
      have hc_le : ∀ cat, cntF r cat ≤ n ∧ cntG r cat ≤ n := by
        intro cat
        constructor <;>
        · calc _ ≤ (Finset.univ : Finset (Fin i)).card := Finset.card_le_card (Finset.filter_subset _ _)
            _ = i := by simp
            _ ≤ n := hi
      have hc1_abs : |c1d| ≤ n := by
        have ⟨h1, h2⟩ := hc_le 1; rw [abs_le]; omega
      have hc2_abs : |c2d| ≤ n := by
        have ⟨h1, h2⟩ := hc_le 2; rw [abs_le]; omega
      have htail_abs : |tailDiff| ≤ (n : ℤ) * (maxH_gt : ℤ) := by
        have h1 := htail_le f; have h2 := htail_le g
        have h3 := htail_nonneg f; have h4 := htail_nonneg g
        rw [abs_le]; constructor <;> linarith
      obtain ⟨R, hR_eq, hR_uP, hR_uP0, hR_H, hR_H0⟩ := hgrow r hr1 hrn
      have hmaxH_uP : 4 * n * (maxH_gt + R.natAbs + 1) + n < uP r := by
        by_cases hemp : (Finset.Ioc r n).Nonempty
        · by_cases h1 : 1 ≤ (Finset.Ioc r n).sup H
          · have hmax_eq : maxH_gt = (Finset.Ioc r n).sup H := max_eq_right h1
            obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup (Finset.Ioc r n) hemp H
            rw [Finset.mem_Ioc] at hk
            rw [hmax_eq, hkeq]
            exact hR_uP k hk.1 hk.2
          · have hmax_eq : maxH_gt = 1 := max_eq_left (by omega)
            rw [hmax_eq]
            have : 1 + R.natAbs + 1 = R.natAbs + 2 := by omega
            rw [this]; exact hR_uP0
        · have hemp' : Finset.Ioc r n = ∅ := Finset.not_nonempty_iff_eq_empty.mp hemp
          have hmax_eq : maxH_gt = 1 := by simp [maxH_gt, hemp']
          rw [hmax_eq]
          have : 1 + R.natAbs + 1 = R.natAbs + 2 := by omega
          rw [this]; exact hR_uP0
      have hmaxH_H : 4 * n * max (uP r) (uM r) + 4 * n * maxH_gt + n < H r := by
        by_cases hemp : (Finset.Ioc r n).Nonempty
        · by_cases h1 : 1 ≤ (Finset.Ioc r n).sup H
          · have hmax_eq : maxH_gt = (Finset.Ioc r n).sup H := max_eq_right h1
            obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup (Finset.Ioc r n) hemp H
            rw [Finset.mem_Ioc] at hk
            rw [hmax_eq, hkeq]
            exact hR_H k hk.1 hk.2
          · have hmax_eq : maxH_gt = 1 := max_eq_left (by omega)
            rw [hmax_eq]; simpa using hR_H0
        · have hemp' : Finset.Ioc r n = ∅ := Finset.not_nonempty_iff_eq_empty.mp hemp
          have hmax_eq : maxH_gt = 1 := by simp [maxH_gt, hemp']
          rw [hmax_eq]; simpa using hR_H0
      -- First prove c3d = 0!
      have hc3 : c3d = 0 := by
        by_contra hne
        have h1 : (H r : ℤ) ≤ |c3d * (H r : ℤ)| := by
          rw [abs_mul, abs_of_nonneg (a := (H r : ℤ)) (Nat.cast_nonneg _)]
          have : (1 : ℤ) ≤ |c3d| := Int.one_le_abs hne
          exact le_mul_of_one_le_left (Nat.cast_nonneg _) this
        have h2 : |c3d * (H r : ℤ)| = |tailDiff - c1d * (uP r : ℤ) - c2d * (uM r : ℤ)| := by
          congr 1; linarith
        have h3 : |tailDiff - c1d * (uP r : ℤ) - c2d * (uM r : ℤ)| ≤
            |tailDiff| + |c1d| * (uP r : ℤ) + |c2d| * (uM r : ℤ) := by
          have ha1 := abs_sub (tailDiff - c1d * (uP r : ℤ)) (c2d * (uM r : ℤ))
          have ha2 := abs_sub tailDiff (c1d * (uP r : ℤ))
          rw [abs_mul, abs_of_nonneg (a := (uM r : ℤ)) (Nat.cast_nonneg _)] at ha1
          rw [abs_mul, abs_of_nonneg (a := (uP r : ℤ)) (Nat.cast_nonneg _)] at ha2
          linarith
        have hu1 : (uP r : ℤ) ≤ (max (uP r) (uM r) : ℤ) := by exact_mod_cast le_max_left (uP r) (uM r)
        have hu2 : (uM r : ℤ) ≤ (max (uP r) (uM r) : ℤ) := by exact_mod_cast le_max_right (uP r) (uM r)
        have hm1 : |c1d| * (uP r : ℤ) ≤ (n : ℤ) * (max (uP r) (uM r) : ℤ) :=
          mul_le_mul hc1_abs hu1 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        have hm2 : |c2d| * (uM r : ℤ) ≤ (n : ℤ) * (max (uP r) (uM r) : ℤ) :=
          mul_le_mul hc2_abs hu2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        have hmaxH_H_z : (4 * n * max (uP r) (uM r) + 4 * n * maxH_gt + n : ℤ) < (H r : ℤ) := by
          exact_mod_cast hmaxH_H
        have hnn1 : (0 : ℤ) ≤ (n : ℤ) * (max (uP r) (uM r) : ℤ) := by positivity
        have hnn2 : (0 : ℤ) ≤ (n : ℤ) * (maxH_gt : ℤ) := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        have hnn3 : (0 : ℤ) ≤ (n : ℤ) := Nat.cast_nonneg _
        push_cast at hmaxH_H_z
        linarith
      -- Next prove c2d = 0 and c1d = 0!
      rw [hc3, zero_mul, add_zero, hR_eq] at hbal
      have hbal2 : (c1d + (n + 1 : ℤ) * c2d) * (uP r : ℤ) = tailDiff - c2d * R := by linarith
      have hcomb : c1d + (n + 1 : ℤ) * c2d = 0 := by
        by_contra hne
        have h1 : (uP r : ℤ) ≤ |(c1d + (n + 1 : ℤ) * c2d) * (uP r : ℤ)| := by
          rw [abs_mul, abs_of_nonneg (a := (uP r : ℤ)) (Nat.cast_nonneg _)]
          have : (1 : ℤ) ≤ |c1d + (n + 1 : ℤ) * c2d| := Int.one_le_abs hne
          exact le_mul_of_one_le_left (Nat.cast_nonneg _) this
        rw [hbal2] at h1
        have h2 : |tailDiff - c2d * R| ≤ |tailDiff| + |c2d| * |R| := by
          have := abs_sub tailDiff (c2d * R); rw [abs_mul] at this; linarith
        have hRabs : |R| = (R.natAbs : ℤ) := Int.abs_eq_natAbs R
        have hmR : |c2d| * |R| ≤ (n : ℤ) * (R.natAbs : ℤ) := by
          rw [hRabs]; exact mul_le_mul_of_nonneg_right hc2_abs (Nat.cast_nonneg _)
        have hmaxH_uP_z : (4 * n * (maxH_gt + R.natAbs + 1) + n : ℤ) < (uP r : ℤ) := by
          exact_mod_cast hmaxH_uP
        have hnn1 : (0 : ℤ) ≤ (n : ℤ) * (maxH_gt : ℤ) := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        have hnn2 : (0 : ℤ) ≤ (n : ℤ) * (R.natAbs : ℤ) := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        have hnn3 : (0 : ℤ) ≤ (n : ℤ) := Nat.cast_nonneg _
        push_cast at hmaxH_uP_z
        rw [hRabs] at hmaxH_uP_z
        linarith
      have hc2 : c2d = 0 := by
        by_contra hne
        have h1 : (n + 1 : ℤ) ≤ |(n + 1 : ℤ) * c2d| := by
          rw [abs_mul, abs_of_nonneg (by omega : (0 : ℤ) ≤ n + 1)]
          have : (1 : ℤ) ≤ |c2d| := Int.one_le_abs hne
          exact le_mul_of_one_le_right (by omega) this
        have h2 : (n + 1 : ℤ) * c2d = -c1d := by linarith
        rw [h2, abs_neg] at h1
        omega
      have hc1 : c1d = 0 := by rw [hc2, mul_zero, add_zero] at hcomb; exact hcomb
      exact ⟨by omega, by omega, by omega⟩
  -- Conclude using hVal_cat_eq_two_iff!
  intro r hr1 hrn
  have h2 := (hall_eq r hr1 hrn).2.1
  change (Finset.univ.filter (fun a : Fin i => hVal_cat n (f a) = (r, 2))).card =
         (Finset.univ.filter (fun a : Fin i => hVal_cat n (g a) = (r, 2))).card at h2
  convert h2 using 2
  · ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hVal_cat_eq_two_iff n r hr1 hrn (f a) (Nat.lt_succ_iff.mp (f a).isLt)).symm
  · ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hVal_cat_eq_two_iff n r hr1 hrn (g a) (Nat.lt_succ_iff.mp (g a).isLt)).symm

/-! ### Section 6: Solving delta by back-substitution and proving OMA.solution -/

/-- For a tuple set T = tupleSet twoD i S, compute the M- and delta-independent constant D(T, v). -/
private def constD {N : ℕ} (v : Fin (N + 1) → ℕ) (i S : ℕ) (hS : S ≤ i * N) : ℕ :=
  let T := tupleSet N i S
  let W := T.image (fun f => ∑ a : Fin i, v (f a))
  have hW : W.Nonempty := (tupleSet_nonempty N i S hS).image _
  let m := W.min' hW
  let cnt := fun val => (T.filter (fun f => (∑ a : Fin i, v (f a)) = val)).card
  c1 (cnt m - 1) + ∑ val ∈ W.erase m, c1 (cnt val)

/-- Given delta on negative bridges (delta_r : ℕ → ℤ), define the coordinate perturbation vector. -/
private def deltaVec (n : ℕ) (dvec : ℕ → ℤ) (j : Fin (prefixLen n (n * (n + 2)) + 1)) : ℤ :=
  if hVal_cat n j = ((hVal_cat n j).1, 2) then dvec (hVal_cat n j).1 else 0

private lemma deltaVec_at_negSpecPos (n r : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ n) (dvec : ℕ → ℤ) :
    deltaVec n dvec ⟨negSpecPos n r, Nat.lt_succ_of_lt (negSpecPos_lt n r hr1 hrn)⟩ = dvec r := by
  unfold deltaVec
  have hcat := (hVal_cat_eq_two_iff n r hr1 hrn (negSpecPos n r)
    (le_of_lt (negSpecPos_lt n r hr1 hrn))).mpr rfl
  simp [hcat]

private lemma deltaVec_eq_sum_indicator (n : ℕ) (dvec : ℕ → ℤ)
    (j : Fin (prefixLen n (n * (n + 2)) + 1)) :
    deltaVec n dvec j =
      ∑ r ∈ Finset.Icc 1 n, if (j : ℕ) = negSpecPos n r then dvec r else 0 := by
  unfold deltaVec
  by_cases h2 : (hVal_cat n j).2 = 2
  · set r := (hVal_cat n j).1
    have hcat : hVal_cat n j = (r, 2) := Prod.ext rfl h2
    have hr_bounds : 1 ≤ r ∧ r ≤ n :=
      hVal_cat_fst_mem n j (Nat.lt_succ_iff.mp j.isLt) (by omega)
    have hj_eq : (j : ℕ) = negSpecPos n r :=
      (hVal_cat_eq_two_iff n r hr_bounds.1 hr_bounds.2 j (Nat.lt_succ_iff.mp j.isLt)).mp hcat
    rw [if_pos hcat]
    rw [Finset.sum_eq_single r]
    · simp [hj_eq]
    · intro k hk hne
      rw [Finset.mem_Icc] at hk
      rw [if_neg]
      intro hjk
      exact hne (negSpecPos_injective n k r hk.1 hr_bounds.1 (hjk.symm.trans hj_eq))
    · intro hnot; exact False.elim (hnot (Finset.mem_Icc.mpr hr_bounds))
  · have hne_cat : hVal_cat n j ≠ ((hVal_cat n j).1, 2) := by
      intro h; exact h2 (congrArg Prod.snd h)
    rw [if_neg hne_cat]
    symm
    apply Finset.sum_eq_zero
    intro r hr
    rw [Finset.mem_Icc] at hr
    rw [if_neg]
    intro hjeq
    have hcat := (hVal_cat_eq_two_iff n r hr.1 hr.2 j (Nat.lt_succ_iff.mp j.isLt)).mpr hjeq
    exact h2 (congrArg Prod.snd hcat)

private lemma deltaVec_zero (n : ℕ) (dvec : ℕ → ℤ) :
    deltaVec n dvec ⟨0, Nat.succ_pos _⟩ = 0 := by
  have hcat_snd : (hVal_cat n 0).2 = 0 := by
    unfold hVal_cat
    by_cases h1 : (0 : ℕ) = prefixLen n (n * (n + 2))
    · rw [if_pos h1]
    · rw [if_neg h1]
      have hb0 : bridgeOf n 0 = 0 := bridgeOf_eq_of_bounds n 0 0 (by simp [prefixLen]) (by
        have := lenOf_pos n 0; simp [prefixLen]; omega)
      rw [if_pos (by simp [hb0, prefixLen])]
  unfold deltaVec
  rw [if_neg]
  intro h
  have := congrArg Prod.snd h
  simp [hcat_snd] at this

private lemma deltaVec_top (n : ℕ) (dvec : ℕ → ℤ) :
    deltaVec n dvec ⟨prefixLen n (n * (n + 2)), Nat.lt_succ_self _⟩ = 0 := by
  unfold deltaVec hVal_cat; simp

/-- Main theorem of Section 6: exact formula for c1(polyCoeff(M*v + delta) - 1) for huge M. -/
private lemma polyCoeff_c1_sub_one_of_large_M
    {N : ℕ} (v : Fin (N + 1) → ℕ) (δ : Fin (N + 1) → ℤ)
    (i S M B : ℕ) (hS : S ≤ i * N)
    (hB : ∀ j, |δ j| ≤ B)
    (hnonneg : ∀ j, 0 ≤ (M : ℤ) * (v j : ℤ) + δ j)
    (hsep_δ : ∀ f ∈ tupleSet N i S, ∀ g ∈ tupleSet N i S,
      (∑ a : Fin i, v (f a)) = (∑ a : Fin i, v (g a)) →
      (∑ a : Fin i, δ (f a)) = (∑ a : Fin i, δ (g a)))
    (hM_big : 2 * i * B + (N + 1) ^ i < M) :
    let x : Fin (N + 1) → ℕ := fun j => ((M : ℤ) * (v j : ℤ) + δ j).toNat
    ∀ fmin ∈ tupleSet N i S,
      (∑ a : Fin i, v (fmin a)) = minWeight v i S hS →
      (c1 (polyCoeff N i x S - 1) : ℤ) =
        (M : ℤ) * (minWeight v i S hS : ℤ) +
        (∑ a : Fin i, δ (fmin a)) +
        (constD v i S hS : ℤ) := by
  intro x fmin hfmin hfmin_eq
  set T := tupleSet N i S
  set w : (Fin i → Fin (N + 1)) → ℕ := fun f => ∑ a : Fin i, v (f a)
  set W := T.image w
  have hW : W.Nonempty := (tupleSet_nonempty N i S hS).image _
  set m := W.min' hW
  have hm_eq : m = minWeight v i S hS := rfl
  let cnt : ℕ → ℕ := fun val => (T.filter (fun f => w f = val)).card
  -- For each val in W, pick a representative f_rep val in T with w (f_rep val) = val
  have hex_rep : ∀ val ∈ W, ∃ f ∈ T, w f = val := fun val hval => Finset.mem_image.mp hval
  classical
  let shiftZ : ℕ → ℤ := fun val =>
    if h : val ∈ W then ∑ a : Fin i, δ ((hex_rep val h).choose a) else 0
  let E : ℕ → ℕ := fun val => ((M : ℤ) * (val : ℤ) + shiftZ val).toNat
  have hshift_eq : ∀ f ∈ T, (∑ a : Fin i, δ (f a)) = shiftZ (w f) := by
    intro f hf
    have hw_mem : w f ∈ W := Finset.mem_image_of_mem w hf
    dsimp only [shiftZ]
    rw [dif_pos hw_mem]
    have hrep := (hex_rep (w f) hw_mem).choose_spec
    exact hsep_δ f hf _ hrep.1 hrep.2.symm
  have hx_cast : ∀ j, (x j : ℤ) = (M : ℤ) * (v j : ℤ) + δ j := fun j =>
    Int.toNat_of_nonneg (hnonneg j)
  have hE_cast : ∀ f ∈ T, (∑ a : Fin i, x (f a)) = E (w f) := by
    intro f hf
    have hsum_z : ((∑ a : Fin i, x (f a) : ℕ) : ℤ) = (M : ℤ) * (w f : ℤ) + shiftZ (w f) := by
      rw [← hshift_eq f hf]
      dsimp only [w]
      push_cast
      simp_rw [hx_cast]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have hnn : 0 ≤ (M : ℤ) * (w f : ℤ) + shiftZ (w f) := by
      rw [← hsum_z]; exact Nat.cast_nonneg _
    dsimp only [E]
    apply Nat.cast_injective (R := ℤ)
    rw [Int.toNat_of_nonneg hnn]
    exact hsum_z
  have hpoly_eq : polyCoeff N i x S = ∑ val ∈ W, cnt val * 2 ^ E val := by
    unfold polyCoeff
    rw [← Finset.sum_fiberwise_of_maps_to (s := T) (t := W) (g := w)
      (fun f hf => Finset.mem_image_of_mem w hf)]
    apply Finset.sum_congr rfl
    intro val _
    have hcongr : ∑ f ∈ T.filter (fun f => w f = val), 2 ^ (∑ a : Fin i, x (f a)) =
        ∑ _f ∈ T.filter (fun f => w f = val), 2 ^ E val := by
      apply Finset.sum_congr rfl
      intro f hf
      rw [Finset.mem_filter] at hf
      rw [hE_cast f hf.1, hf.2]
    rw [hcongr, Finset.sum_const, smul_eq_mul]
  have hshift_abs : ∀ val ∈ W, |shiftZ val| ≤ (i : ℤ) * (B : ℤ) := by
    intro val hval
    dsimp only [shiftZ]
    rw [dif_pos hval]
    calc |∑ a : Fin i, δ ((hex_rep val hval).choose a)|
        ≤ ∑ a : Fin i, |δ ((hex_rep val hval).choose a)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : Fin i, (B : ℤ) := Finset.sum_le_sum (fun a _ => hB _)
      _ = (i : ℤ) * (B : ℤ) := by simp [Finset.sum_const, nsmul_eq_mul]
  have hE_z : ∀ val ∈ W, (E val : ℤ) = (M : ℤ) * (val : ℤ) + shiftZ val := by
    intro val hval
    obtain ⟨f, hfT, hfw⟩ := hex_rep val hval
    have h1 := hE_cast f hfT
    rw [hfw] at h1
    have hnn : 0 ≤ (M : ℤ) * (val : ℤ) + shiftZ val := by
      have hsum_z : ((∑ a : Fin i, x (f a) : ℕ) : ℤ) = (M : ℤ) * (val : ℤ) + shiftZ val := by
        rw [← hfw, ← hshift_eq f hfT]
        dsimp only [w]
        push_cast
        simp_rw [hx_cast]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [← hsum_z]; exact Nat.cast_nonneg _
    exact Int.toNat_of_nonneg hnn
  have hcnt_pos : ∀ val ∈ W, 1 ≤ cnt val := by
    intro val hval
    obtain ⟨f, hfT, hfw⟩ := hex_rep val hval
    exact Finset.card_pos.mpr ⟨f, Finset.mem_filter.mpr ⟨hfT, hfw⟩⟩
  have hcnt_le : ∀ val ∈ W, cnt val ≤ (N + 1) ^ i := by
    intro val _
    calc cnt val ≤ T.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ ≤ (Finset.univ : Finset (Fin i → Fin (N + 1))).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = (N + 1) ^ i := by simp [Fintype.card_pi, Finset.prod_const]
  have hsep : ∀ a ∈ W, ∀ b ∈ W, a < b → cnt a < 2 ^ (E b - E a) ∧ E a ≤ E b := by
    intro a ha b hb hab
    have hEa := hE_z a ha
    have hEb := hE_z b hb
    have hsa := abs_le.mp (hshift_abs a ha)
    have hsb := abs_le.mp (hshift_abs b hb)
    have hM_z : (2 * (i : ℤ) * (B : ℤ) + (((N + 1) ^ i : ℕ) : ℤ)) < (M : ℤ) := by exact_mod_cast hM_big
    have hba1 : (1 : ℤ) ≤ (b : ℤ) - (a : ℤ) := by omega
    have hM_mul : (M : ℤ) ≤ (M : ℤ) * ((b : ℤ) - (a : ℤ)) := le_mul_of_one_le_right (Nat.cast_nonneg _) hba1
    have hdiff_z : (((N + 1) ^ i : ℕ) : ℤ) < (E b : ℤ) - (E a : ℤ) := by linarith
    have hEa_le : E a ≤ E b := by omega
    have hdiff_ge : (N + 1) ^ i < E b - E a := by omega
    refine ⟨?_, hEa_le⟩
    have hpow : (N + 1) ^ i < 2 ^ ((N + 1) ^ i) := Nat.lt_two_pow_self
    have hpow2 : 2 ^ ((N + 1) ^ i) ≤ 2 ^ (E b - E a) := Nat.pow_le_pow_right (by norm_num) (le_of_lt hdiff_ge)
    have hca := hcnt_le a ha
    omega
  rw [hpoly_eq]
  have hc1 := c1_separated_sum_sub_one W hW cnt E hcnt_pos hsep
  dsimp only at hc1
  rw [hc1]
  have hD_eq : c1 (cnt m - 1) + ∑ val ∈ W.erase m, c1 (cnt val) = constD v i S hS := rfl
  have hEm : (E m : ℤ) = (M : ℤ) * (m : ℤ) + shiftZ m := hE_z m (Finset.min'_mem W hW)
  have hsm : shiftZ m = ∑ a : Fin i, δ (fmin a) := by
    rw [hm_eq, ← hfmin_eq]
    exact (hshift_eq fmin hfmin).symm
  rw [add_assoc, hD_eq]
  push_cast
  rw [hEm, hsm, hm_eq]

/-- Back-substitution to find delta_1, ..., delta_n cancelling D'_i(v) for all 1 <= i <= n. -/
private lemma exists_delta_solution (n K Hmax : ℕ) (uP uM H : ℕ → ℕ)
    (hn : 1 ≤ n)
    (hvalid : ∀ r, 1 ≤ r → r ≤ n → n < uP r ∧ n < uM r ∧ n * max (uP r) (uM r) + n < H r)
    (hh_le : ∀ j ≤ prefixLen n (n * (n + 2)), hVal n uP uM H j ≤ Hmax)
    (hK : n * Hmax < K)
    (hsep : ∀ i ≤ n, ∀ f g : Fin i → Fin (prefixLen n (n * (n + 2)) + 1),
      (∑ a : Fin i, vFull n K uP uM H (f a)) = (∑ a : Fin i, vFull n K uP uM H (g a)) →
      ∀ r, 1 ≤ r → r ≤ n →
        (Finset.univ.filter (fun a : Fin i => (f a : ℕ) = negSpecPos n r)).card =
        (Finset.univ.filter (fun a : Fin i => (g a : ℕ) = negSpecPos n r)).card) :
    let twoD := prefixLen n (n * (n + 2))
    let v := vFull n K uP uM H
    ∃ dvec : ℕ → ℤ,
      ∀ i, 1 ≤ i → i ≤ n →
        (1 : ℤ) + ∑ S ∈ Finset.Ico 1 (i * twoD),
          (-1 : ℤ) ^ S *
            (if h : S ≤ i * twoD then
              (∑ a : Fin i, deltaVec n dvec ((exists_minWeight v i S h).choose a)) +
              (constD v i S h : ℤ)
            else 0) = 0 := by
  classical
  set B := n * (n + 2)
  set twoD := prefixLen n B
  set v := vFull n K uP uM H
  -- Coefficient of dvec r in the i-th equation:
  let coeff : ℕ → ℕ → ℤ := fun i r =>
    ∑ S ∈ Finset.Ico 1 (i * twoD),
      (-1 : ℤ) ^ S *
        (if h : S ≤ i * twoD then
          ((Finset.univ.filter (fun a : Fin i =>
            ((exists_minWeight v i S h).choose a : ℕ) = negSpecPos n r)).card : ℤ)
        else 0)
  let baseD : ℕ → ℤ := fun i =>
    1 + ∑ S ∈ Finset.Ico 1 (i * twoD),
      (-1 : ℤ) ^ S * (if h : S ≤ i * twoD then (constD v i S h : ℤ) else 0)
  -- Express the i-th equation as baseD i + sum_{r=1}^n coeff i r * dvec r
  have heq_lin : ∀ (dvec : ℕ → ℤ) (i : ℕ), 1 ≤ i → i ≤ n →
      (1 : ℤ) + ∑ S ∈ Finset.Ico 1 (i * twoD),
        (-1 : ℤ) ^ S *
          (if h : S ≤ i * twoD then
            (∑ a : Fin i, deltaVec n dvec ((exists_minWeight v i S h).choose a)) +
            (constD v i S h : ℤ)
          else 0) =
      baseD i + ∑ r ∈ Finset.Icc 1 n, coeff i r * dvec r := by
    intro dvec i hi1 hin
    have hsplit :
        ∑ S ∈ Finset.Ico 1 (i * twoD),
          (-1 : ℤ) ^ S *
            (if h : S ≤ i * twoD then
              (∑ a : Fin i, deltaVec n dvec ((exists_minWeight v i S h).choose a)) +
              (constD v i S h : ℤ)
            else 0) =
        (∑ S ∈ Finset.Ico 1 (i * twoD),
          (-1 : ℤ) ^ S *
            (if h : S ≤ i * twoD then
              ∑ a : Fin i, deltaVec n dvec ((exists_minWeight v i S h).choose a)
            else 0)) +
        (∑ S ∈ Finset.Ico 1 (i * twoD),
          (-1 : ℤ) ^ S * (if h : S ≤ i * twoD then (constD v i S h : ℤ) else 0)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro S _; split_ifs <;> ring
    rw [hsplit]
    dsimp only [baseD]
    have hswap :
        ∑ S ∈ Finset.Ico 1 (i * twoD),
          (-1 : ℤ) ^ S *
            (if h : S ≤ i * twoD then
              ∑ a : Fin i, deltaVec n dvec ((exists_minWeight v i S h).choose a)
            else 0) =
        ∑ r ∈ Finset.Icc 1 n, coeff i r * dvec r := by
      have hinner : ∀ S ∈ Finset.Ico 1 (i * twoD),
          (-1 : ℤ) ^ S *
            (if h : S ≤ i * twoD then
              ∑ a : Fin i, deltaVec n dvec ((exists_minWeight v i S h).choose a)
            else 0) =
          ∑ r ∈ Finset.Icc 1 n,
            (-1 : ℤ) ^ S *
              (if h : S ≤ i * twoD then
                ((Finset.univ.filter (fun a : Fin i =>
                  ((exists_minWeight v i S h).choose a : ℕ) = negSpecPos n r)).card : ℤ)
              else 0) * dvec r := by
        intro S hS
        have hSle : S ≤ i * twoD := le_of_lt (Finset.mem_Ico.mp hS).2
        simp only [dif_pos hSle]
        simp_rw [deltaVec_eq_sum_indicator]
        rw [Finset.sum_comm, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        ring
      rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      dsimp only [coeff]
      rw [Finset.sum_mul]
    rw [hswap]; ring
  -- Helper: bridge lookup for S < i * twoD
  have hS_bridge : ∀ i S : ℕ, 1 ≤ i → S < i * twoD →
      let t := bridgeOf n (S / i)
      t < B ∧ i * prefixLen n t ≤ S ∧ S - i * prefixLen n t < i * lenOf n t := by
    intro i S hi hS
    dsimp only
    set t := bridgeOf n (S / i)
    have hdiv_lt : S / i < twoD := (Nat.div_lt_iff_lt_mul hi).mpr (by rw [mul_comm]; exact hS)
    have ⟨hb1, hb2⟩ := bridgeOf_spec n (S / i)
    change prefixLen n t ≤ S / i at hb1
    change S / i < prefixLen n (t + 1) at hb2
    have ht_lt : t < B := by
      by_contra hge; push_neg at hge
      have h1 : twoD ≤ prefixLen n t := prefixLen_mono n hge
      omega
    have h1 : i * prefixLen n t ≤ S := by
      have hmul := Nat.mul_le_mul_left i hb1
      have hdm : i * (S / i) ≤ S := by rw [mul_comm]; exact Nat.div_mul_le_self S i
      omega
    have h2 : S < i * prefixLen n (t + 1) := by
      have := (Nat.div_lt_iff_lt_mul hi).mp hb2
      rw [mul_comm] at this; exact this
    have h3 : i * prefixLen n (t + 1) = i * prefixLen n t + i * lenOf n t := by
      change i * (prefixLen n t + lenOf n t) = _; ring
    exact ⟨ht_lt, h1, by omega⟩
  -- Key triangularity of coeff i r:
  -- For 1 <= r < i <= n: coeff i r = 0!
  -- For 1 <= r = i <= n: coeff r r = -1!
  have hcoeff_gt : ∀ i r, 1 ≤ r → r < i → i ≤ n → coeff i r = 0 := by
    intro i r hr1 hri hin
    dsimp only [coeff]
    apply Finset.sum_eq_zero
    intro S hS
    have hSlt : S < i * twoD := (Finset.mem_Ico.mp hS).2
    have hSle : S ≤ i * twoD := le_of_lt hSlt
    rw [dif_pos hSle]
    set t := bridgeOf n (S / i)
    obtain ⟨ht_lt, hS_ge, hu_lt⟩ := hS_bridge i S (by omega) hSlt
    change t < B at ht_lt
    change i * prefixLen n t ≤ S at hS_ge
    change S - i * prefixLen n t < i * lenOf n t at hu_lt
    have hu_le : S - i * prefixLen n t ≤ i * lenOf n t := le_of_lt hu_lt
    have hS_eq : i * prefixLen n t + (S - i * prefixLen n t) = S := by omega
    set f := (exists_minWeight v i S hSle).choose
    have hf_spec := (exists_minWeight v i S hSle).choose_spec
    have hK_i : i * Hmax < K := lt_of_le_of_lt (Nat.mul_le_mul_right Hmax hin) hK
    have hdec := (bridge_decoupling n K Hmax uP uM H hh_le i t (S - i * prefixLen n t)
      (by omega) ht_lt hu_le hK_i).2
    have ⟨hin_t, hloc_min⟩ := hdec f (by rw [hS_eq]; exact hf_spec.1) (by
      have heq := hf_spec.2
      convert heq using 2 <;> exact hS_eq)
    have hcard0 : (Finset.univ.filter (fun a : Fin i => (f a : ℕ) = negSpecPos n r)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro a _ ha_eq
      have hfa_in := hin_t a
      rw [ha_eq] at hfa_in
      have ht_eq : t = negBridgeIdx n r := by
        have hbo : bridgeOf n (negSpecPos n r) = negBridgeIdx n r := by
          apply bridgeOf_eq_of_bounds
          · unfold negSpecPos; omega
          · unfold negSpecPos; have := lenOf_pos n (negBridgeIdx n r); simp [prefixLen]; omega
        have hlt_pr : negSpecPos n r < prefixLen n (t + 1) := by
          by_contra hge; push_neg at hge
          have heq_pr : negSpecPos n r = prefixLen n (t + 1) := by omega
          have hbo2 : bridgeOf n (negSpecPos n r) = t + 1 := by
            rw [heq_pr]
            exact bridgeOf_eq_of_bounds n _ (t + 1) (le_refl _) (prefixLen_strictMono n (Nat.lt_succ_self (t + 1)))
          have : negSpecPos n r - prefixLen n (bridgeOf n (negSpecPos n r)) = 0 := by
            rw [hbo2, heq_pr]; simp
          rw [hbo] at this
          unfold negSpecPos at this; omega
        exact (bridgeOf_eq_of_bounds n (negSpecPos n r) t hfa_in.1 hlt_pr).symm.trans hbo
      rw [ht_eq] at hin_t hloc_min hu_le
      have ⟨hr_eq, hs_eq⟩ := negBridgeIdx_r_s n r hr1
      let floc : Fin i → Fin (4 * r + 4 + 1) := fun b =>
        ⟨(f b : ℕ) - prefixLen n (negBridgeIdx n r), by
          have hb := hin_t b
          have hPR : prefixLen n (negBridgeIdx n r + 1) = prefixLen n (negBridgeIdx n r) + (4 * r + 4) := by
            change prefixLen n (negBridgeIdx n r) + lenOf n (negBridgeIdx n r) = _
            unfold lenOf; rw [hr_eq]
          omega⟩
      have hfloc_mem : floc ∈ tupleSet (4 * r + 4) i (S - i * prefixLen n (negBridgeIdx n r)) := by
        rw [tupleSet, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have hf_sum : ∑ b : Fin i, (f b : ℕ) = S := (Finset.mem_filter.mp hf_spec.1).2
        have hadd : ∑ b : Fin i, ((f b : ℕ) - prefixLen n (negBridgeIdx n r)) +
            ∑ _b : Fin i, prefixLen n (negBridgeIdx n r) = ∑ b : Fin i, (f b : ℕ) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro b _; have := hin_t b; omega
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hadd
        change ∑ b : Fin i, ((f b : ℕ) - prefixLen n (negBridgeIdx n r)) = _
        omega
      have ⟨hvuP, hvuM, hvH⟩ := hvalid r hr1 (by omega)
      have hH_gt_i : i < H r := by
        have h1 : max (uP r) (uM r) ≤ n * max (uP r) (uM r) := Nat.le_mul_of_pos_left _ hn
        have h2 := le_max_right (uP r) (uM r)
        omega
      have hu_le' : S - i * prefixLen n (negBridgeIdx n r) ≤ i * (4 * r + 4) := by
        simpa [lenOf, hr_eq] using hu_le
      have hcov := bridge_cover r 4 i (S - i * prefixLen n (negBridgeIdx n r)) hr1 (Or.inr rfl)
        (le_of_lt hri) hu_le' (by omega)
      have hcheap_all := (bridgeMin_cheap_eq r 4 (uM r) (H r) (uM r) (H r) i
        (S - i * prefixLen n (negBridgeIdx n r)) hu_le'
        (by omega) hH_gt_i (by omega) hH_gt_i hcov).2
      have hloc_min' : ∑ b : Fin i, bridgeH r 4 (uM r) (H r) (floc b) =
          bridgeMin r 4 (uM r) (H r) i (S - i * prefixLen n (negBridgeIdx n r)) := by
        simp only [floc, Fin.val_mk]
        rw [hr_eq, hs_eq] at hloc_min
        simpa using hloc_min
      have hca := hcheap_all floc hfloc_mem hloc_min' a
      have hfloc_a : (floc a : ℕ) = 5 := by
        simp only [floc, Fin.val_mk, ha_eq, negSpecPos]; omega
      rw [hfloc_a] at hca
      have hnot := isCheap_special_false r 4 hr1 (Or.inr rfl)
      rw [hnot] at hca; cases hca
    simp [hcard0]
  have hcoeff_eq : ∀ r, 1 ≤ r → r ≤ n → coeff r r = -1 := by
    intro r hr1 hrn
    set t0 := negBridgeIdx n r
    set Sstar_loc := (r - 1) * (4 * r + 4) + 5
    set Sstar := r * prefixLen n t0 + Sstar_loc
    have ht0_lt : t0 < B := negBridgeIdx_lt n r hr1 hrn
    have ⟨hr_eq, hs_eq⟩ := negBridgeIdx_r_s n r hr1
    have hSstar_loc_lt : Sstar_loc < r * lenOf n t0 := by
      have hlen_eq : lenOf n t0 = 4 * r + 4 := by unfold lenOf; rw [hr_eq]
      have hr1' : (r - 1) * (4 * r + 4) + (4 * r + 4) = r * (4 * r + 4) := by
        rw [← Nat.add_one_mul, Nat.sub_add_cancel hr1]
      rw [hlen_eq]; dsimp only [Sstar_loc]; omega
    have hSstar_mem : Sstar ∈ Finset.Ico 1 (r * twoD) := by
      rw [Finset.mem_Ico]
      have h1 : prefixLen n t0 + lenOf n t0 ≤ twoD := by
        change prefixLen n (t0 + 1) ≤ twoD; exact prefixLen_mono n (by omega)
      have h2 := Nat.mul_le_mul_left r h1
      rw [mul_add] at h2
      refine ⟨by dsimp only [Sstar, Sstar_loc]; omega, by omega⟩
    have hSstar_le : Sstar ≤ r * twoD := le_of_lt (Finset.mem_Ico.mp hSstar_mem).2
    dsimp only [coeff]
    rw [Finset.sum_eq_single Sstar]
    · rw [dif_pos hSstar_le]
      have hpar : (-1 : ℤ) ^ Sstar = -1 := by
        rcases (prefixLen_even n t0).mul_left r with ⟨q, hq⟩
        have hodd : Sstar = 2 * (q + (r - 1) * (2 * r + 2) + 2) + 1 := by
          dsimp only [Sstar, Sstar_loc]
          have : r * prefixLen n t0 = 2 * q := by omega
          rw [this]; ring
        rw [hodd, pow_succ, pow_mul]; norm_num
      rw [hpar]
      set f := (exists_minWeight v r Sstar hSstar_le).choose
      have hf_spec := (exists_minWeight v r Sstar hSstar_le).choose_spec
      have hK_r : r * Hmax < K := lt_of_le_of_lt (Nat.mul_le_mul_right Hmax hrn) hK
      have hdec := (bridge_decoupling n K Hmax uP uM H hh_le r t0 Sstar_loc hr1 ht0_lt
        (le_of_lt hSstar_loc_lt) hK_r).2
      have ⟨hin_t, hloc_min⟩ := hdec f hf_spec.1 hf_spec.2
      let floc : Fin r → Fin (4 * r + 4 + 1) := fun b =>
        ⟨(f b : ℕ) - prefixLen n t0, by
          have hb := hin_t b
          have hPR : prefixLen n (t0 + 1) = prefixLen n t0 + (4 * r + 4) := by
            change prefixLen n t0 + lenOf n t0 = _; unfold lenOf; rw [hr_eq]
          omega⟩
      have hfloc_mem : floc ∈ tupleSet (4 * r + 4) r Sstar_loc := by
        rw [tupleSet, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have hf_sum : ∑ b : Fin r, (f b : ℕ) = r * prefixLen n t0 + Sstar_loc :=
          (Finset.mem_filter.mp hf_spec.1).2
        have hadd : ∑ b : Fin r, ((f b : ℕ) - prefixLen n t0) +
            ∑ _b : Fin r, prefixLen n t0 = ∑ b : Fin r, (f b : ℕ) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro b _; have := hin_t b; omega
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hadd
        change ∑ b : Fin r, ((f b : ℕ) - prefixLen n t0) = Sstar_loc
        omega
      have ⟨hvuP, hvuM, hvH⟩ := hvalid r hr1 hrn
      have hH_gt_uM : uM r < H r := by
        have h1 : max (uP r) (uM r) ≤ n * max (uP r) (uM r) := Nat.le_mul_of_pos_left _ hn
        have h2 := le_max_right (uP r) (uM r)
        omega
      have ⟨hbm_star, hcard_star⟩ := bridgeMin_star r 4 (uM r) (H r) hr1 (Or.inr rfl)
        (by omega) hH_gt_uM
      have hloc_min' : ∑ b : Fin r, bridgeH r 4 (uM r) (H r) (floc b) = uM r := by
        have h1 : ∑ b : Fin r, bridgeH r 4 (uM r) (H r) (floc b) =
            bridgeMin r 4 (uM r) (H r) r Sstar_loc := by
          simp only [floc, Fin.val_mk]
          rw [hr_eq, hs_eq] at hloc_min
          simpa using hloc_min
        rw [h1, hbm_star]
      have hcard1 := hcard_star floc hfloc_mem hloc_min'
      have hfilter_eq : Finset.univ.filter (fun a : Fin r => (f a : ℕ) = negSpecPos n r) =
          Finset.univ.filter (fun a : Fin r => (floc a : ℕ) = 4 + 1) := by
        apply Finset.filter_congr
        intro a _
        have hval : (floc a : ℕ) = (f a : ℕ) - prefixLen n (negBridgeIdx n r) := rfl
        have hneg : negSpecPos n r = prefixLen n (negBridgeIdx n r) + 5 := rfl
        have ha : prefixLen n (negBridgeIdx n r) ≤ (f a : ℕ) := (hin_t a).1
        rw [hval, hneg]
        exact ⟨fun h => by omega, fun h => by omega⟩
      rw [hfilter_eq, hcard1]; norm_num
    · -- For any S != Sstar, card = 0!
      intro S hS hSne
      have hSlt : S < r * twoD := (Finset.mem_Ico.mp hS).2
      have hSle : S ≤ r * twoD := le_of_lt hSlt
      rw [dif_pos hSle]
      set t := bridgeOf n (S / r)
      obtain ⟨ht_lt, hS_ge, hu_lt⟩ := hS_bridge r S hr1 hSlt
      change t < B at ht_lt
      change r * prefixLen n t ≤ S at hS_ge
      change S - r * prefixLen n t < r * lenOf n t at hu_lt
      have hu_le : S - r * prefixLen n t ≤ r * lenOf n t := le_of_lt hu_lt
      have hS_eq : r * prefixLen n t + (S - r * prefixLen n t) = S := by omega
      set f := (exists_minWeight v r S hSle).choose
      have hf_spec := (exists_minWeight v r S hSle).choose_spec
      have hK_r : r * Hmax < K := lt_of_le_of_lt (Nat.mul_le_mul_right Hmax hrn) hK
      have hdec := (bridge_decoupling n K Hmax uP uM H hh_le r t (S - r * prefixLen n t)
        hr1 ht_lt hu_le hK_r).2
      have ⟨hin_t, hloc_min⟩ := hdec f (by rw [hS_eq]; exact hf_spec.1) (by
        have heq := hf_spec.2
        convert heq using 2 <;> exact hS_eq)
      have hcard0 : (Finset.univ.filter (fun a : Fin r => (f a : ℕ) = negSpecPos n r)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro a _ ha_eq
        have hfa_in := hin_t a
        rw [ha_eq] at hfa_in
        have ht_eq : t = t0 := by
          have hbo : bridgeOf n (negSpecPos n r) = t0 := by
            apply bridgeOf_eq_of_bounds
            · unfold negSpecPos; dsimp only [t0]; omega
            · unfold negSpecPos; have := lenOf_pos n t0; simp [prefixLen]; dsimp only [t0] at *; omega
          have hlt_pr : negSpecPos n r < prefixLen n (t + 1) := by
            by_contra hge; push_neg at hge
            have heq_pr : negSpecPos n r = prefixLen n (t + 1) := by omega
            have hbo2 : bridgeOf n (negSpecPos n r) = t + 1 := by
              rw [heq_pr]
              exact bridgeOf_eq_of_bounds n _ (t + 1) (le_refl _) (prefixLen_strictMono n (Nat.lt_succ_self (t + 1)))
            have : negSpecPos n r - prefixLen n (bridgeOf n (negSpecPos n r)) = 0 := by
              rw [hbo2, heq_pr]; simp
            rw [hbo] at this; unfold negSpecPos at this; dsimp only [t0] at this; omega
          exact (bridgeOf_eq_of_bounds n (negSpecPos n r) t hfa_in.1 hlt_pr).symm.trans hbo
        rw [ht_eq] at hin_t hloc_min hu_le
        have hloc_ne : S - r * prefixLen n t0 ≠ Sstar_loc := by
          intro h; apply hSne; dsimp only [Sstar]; omega
        let floc : Fin r → Fin (4 * r + 4 + 1) := fun b =>
          ⟨(f b : ℕ) - prefixLen n t0, by
            have hb := hin_t b
            have hPR : prefixLen n (t0 + 1) = prefixLen n t0 + (4 * r + 4) := by
              change prefixLen n t0 + lenOf n t0 = _; unfold lenOf; rw [hr_eq]
            omega⟩
        have hfloc_mem : floc ∈ tupleSet (4 * r + 4) r (S - r * prefixLen n t0) := by
          rw [tupleSet, Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          have hf_sum : ∑ b : Fin r, (f b : ℕ) = S := (Finset.mem_filter.mp hf_spec.1).2
          have hadd : ∑ b : Fin r, ((f b : ℕ) - prefixLen n t0) +
              ∑ _b : Fin r, prefixLen n t0 = ∑ b : Fin r, (f b : ℕ) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl; intro b _; have := hin_t b; omega
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hadd
          change ∑ b : Fin r, ((f b : ℕ) - prefixLen n t0) = _
          omega
        have ⟨hvuP, hvuM, hvH⟩ := hvalid r hr1 hrn
        have hH_gt_r : r < H r := by
          have h1 : max (uP r) (uM r) ≤ n * max (uP r) (uM r) := Nat.le_mul_of_pos_left _ hn
          have h2 := le_max_right (uP r) (uM r)
          omega
        have hu_le' : S - r * prefixLen n t0 ≤ r * (4 * r + 4) := by
          simpa [lenOf, t0, hr_eq] using hu_le
        have hcov := bridge_cover r 4 r (S - r * prefixLen n t0) hr1 (Or.inr rfl)
          (le_refl r) hu_le' (by tauto)
        have hcheap_all := (bridgeMin_cheap_eq r 4 (uM r) (H r) (uM r) (H r) r
          (S - r * prefixLen n t0) hu_le'
          (by omega) hH_gt_r (by omega) hH_gt_r hcov).2
        have hloc_min' : ∑ b : Fin r, bridgeH r 4 (uM r) (H r) (floc b) =
            bridgeMin r 4 (uM r) (H r) r (S - r * prefixLen n t0) := by
          simp only [floc, Fin.val_mk]
          rw [hr_eq, hs_eq] at hloc_min
          simpa using hloc_min
        have hca := hcheap_all floc hfloc_mem hloc_min' a
        have hfloc_a : (floc a : ℕ) = 5 := by
          dsimp only [floc, t0]; rw [ha_eq]; unfold negSpecPos; omega
        rw [hfloc_a] at hca
        have hnot := isCheap_special_false r 4 hr1 (Or.inr rfl)
        rw [hnot] at hca; cases hca
      simp [hcard0]
    · intro hnot; exact False.elim (hnot hSstar_mem)
  -- Back-substitute from m = 0 to n (setting r = n - m)!
  have hback : ∀ m ≤ n, ∃ dvec : ℕ → ℤ,
      ∀ i, n - m < i → i ≤ n → baseD i + ∑ r ∈ Finset.Icc 1 n, coeff i r * dvec r = 0 := by
    intro m
    induction m with
    | zero =>
      intro _; exact ⟨fun _ => 0, fun i h1 h2 => by omega⟩
    | succ m ih =>
      intro hm
      obtain ⟨dvec, hdvec⟩ := ih (by omega)
      set r0 := n - m
      have hr0_1 : 1 ≤ r0 := by omega
      have hr0_n : r0 ≤ n := by omega
      set val_new : ℤ := baseD r0 + ∑ r ∈ (Finset.Icc 1 n).erase r0, coeff r0 r * dvec r
      let dvec' := Function.update dvec r0 val_new
      refine ⟨dvec', ?_⟩
      intro i hi1 hin
      have hr0_mem : r0 ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨hr0_1, hr0_n⟩
      by_cases hir : i = r0
      · subst hir
        rw [← Finset.add_sum_erase _ _ hr0_mem]
        have hrest : ∑ r ∈ (Finset.Icc 1 n).erase r0, coeff r0 r * dvec' r =
            ∑ r ∈ (Finset.Icc 1 n).erase r0, coeff r0 r * dvec r := by
          apply Finset.sum_congr rfl
          intro r hr; simp [dvec', Function.update_of_ne (Finset.ne_of_mem_erase hr)]
        rw [hrest, hcoeff_eq r0 hr0_1 hr0_n]
        simp only [dvec', Function.update_self]
        linarith
      · have hgt : r0 < i := by omega
        have heq_sum : ∑ r ∈ Finset.Icc 1 n, coeff i r * dvec' r =
            ∑ r ∈ Finset.Icc 1 n, coeff i r * dvec r := by
          apply Finset.sum_congr rfl
          intro r hr
          by_cases hrr0 : r = r0
          · subst hrr0
            rw [hcoeff_gt i r0 hr0_1 hgt hin]; simp
          · simp [dvec', Function.update_of_ne hrr0]
        rw [heq_sum]
        exact hdvec i (by omega) hin
  obtain ⟨dvec, hdvec⟩ := hback n (le_refl n)
  refine ⟨dvec, ?_⟩
  intro i hi1 hin
  rw [heq_lin dvec i hi1 hin]
  exact hdvec i (by omega) hin

/-- Main proof for any n >= 1. -/
private theorem main_proof (n : ℕ) (hn : 1 ≤ n) :
    ∃ k : ℕ, ∀ i : ℕ, 1 ≤ i → i ≤ n → OMA.S_oeis_a345397.IsDigitallyBalanced (k ^ i) := by
  classical
  -- Step 1: Obtain bridge parameters (uP, uM, H)
  obtain ⟨uP, uM, H, hvalid, hzero, hgrow⟩ := exists_bridge_params n hn n (le_refl n)
  simp only [Nat.sub_self] at hzero hgrow
  -- Step 2: Bound Hmax and choose slope K
  set B := n * (n + 2)
  set twoD := prefixLen n B
  have htwoD_even : Even twoD := prefixLen_even n B
  rcases htwoD_even with ⟨d, hd_eq⟩
  have htwoD_ge : 8 ≤ twoD := by
    have hB_pos : 1 ≤ B := by dsimp only [B]; nlinarith
    have h1 : prefixLen n 1 ≤ twoD := prefixLen_mono n hB_pos
    have h2 := lenOf_pos n 0
    simp only [prefixLen] at h1; omega
  have hd1 : 1 ≤ d := by omega
  set Hmax : ℕ := max 1 ((Finset.Icc 1 n).sup H)
  have hh_le : ∀ j ≤ twoD, hVal n uP uM H j ≤ Hmax := by
    apply hVal_le_max n uP uM H Hmax
    · intro r hr1 hrn
      have ⟨_, _, hH⟩ := hvalid r hr1 hrn
      have h1 : H r ≤ Hmax := le_trans (Finset.le_sup (f := H) (Finset.mem_Icc.mpr ⟨hr1, hrn⟩)) (le_max_right _ _)
      have := le_max_left (uP r) (uM r); nlinarith
    · intro r hr1 hrn
      have ⟨_, _, hH⟩ := hvalid r hr1 hrn
      have h1 : H r ≤ Hmax := le_trans (Finset.le_sup (f := H) (Finset.mem_Icc.mpr ⟨hr1, hrn⟩)) (le_max_right _ _)
      have := le_max_right (uP r) (uM r); nlinarith
    · intro r hr1 hrn
      exact le_trans (Finset.le_sup (f := H) (Finset.mem_Icc.mpr ⟨hr1, hrn⟩)) (le_max_right _ _)
    · exact le_max_left _ _
  set K : ℕ := 2 * n * Hmax + 1
  have hK_gt : 2 * n * Hmax < K := by omega
  have hK_n : n * Hmax < K := by nlinarith
  set v := vFull n K uP uM H
  -- Step 3: Separation on v
  have hsep_v : ∀ i ≤ n, ∀ f g : Fin i → Fin (twoD + 1),
      (∑ a : Fin i, v (f a)) = (∑ a : Fin i, v (g a)) →
      ∀ r, 1 ≤ r → r ≤ n →
        (Finset.univ.filter (fun a : Fin i => (f a : ℕ) = negSpecPos n r)).card =
        (Finset.univ.filter (fun a : Fin i => (g a : ℕ) = negSpecPos n r)).card :=
    fun i hi f g hweq => separation_vFull n K Hmax uP uM H hn hh_le hK_gt hgrow hvalid i hi f g hweq
  -- Step 4: Obtain delta solution dvec cancelling constD
  obtain ⟨dvec, hdvec_zero⟩ := exists_delta_solution n K Hmax uP uM H hn hvalid hh_le hK_n hsep_v
  set δ := deltaVec n dvec
  -- Step 5: Pick huge M so M*v + delta >= 0 and separated for all 1 <= i <= n
  set Bdelta : ℕ := (Finset.Icc 1 n).sup (fun r => (dvec r).natAbs)
  have hBdelta : ∀ j : Fin (twoD + 1), |δ j| ≤ Bdelta := by
    intro j
    unfold δ deltaVec
    split_ifs with hcat
    · have hr_mem : (hVal_cat n j).1 ∈ Finset.Icc 1 n := by
        have h2 : (hVal_cat n j).2 = 2 := congrArg Prod.snd hcat
        rw [Finset.mem_Icc]
        exact hVal_cat_fst_mem n j (Nat.lt_succ_iff.mp j.isLt) (by omega)
      have hle : (dvec (hVal_cat n j).1).natAbs ≤ Bdelta :=
        Finset.le_sup (f := fun r => (dvec r).natAbs) hr_mem
      rw [Int.abs_eq_natAbs]; exact_mod_cast hle
    · simp
  set M : ℕ := 2 * n * Bdelta + (twoD + 1) ^ n + Bdelta + 2
  have hnonneg : ∀ j : Fin (twoD + 1), 0 ≤ (M : ℤ) * (v j : ℤ) + δ j := by
    intro j
    by_cases hv0 : v j = 0
    · have hδ0 : δ j = 0 := by
        unfold δ deltaVec
        split_ifs with hcat
        · exfalso
          have h2 : (hVal_cat n j).2 = 2 := congrArg Prod.snd hcat
          have hv_ge : hVal n uP uM H j ≤ v j := Nat.le_add_left _ _
          have hcat_eq : hVal n uP uM H j = uM (hVal_cat n j).1 := (hVal_eq_of_cat n uP uM H j).2.2.1 h2
          have hr_mem : 1 ≤ (hVal_cat n j).1 ∧ (hVal_cat n j).1 ≤ n :=
            hVal_cat_fst_mem n j (Nat.lt_succ_iff.mp j.isLt) (by omega)
          have ⟨_, huM_pos, _⟩ := hvalid _ hr_mem.1 hr_mem.2
          rw [hcat_eq, hv0] at hv_ge
          omega
        · rfl
      rw [hv0, hδ0]; simp
    · have hv1 : (1 : ℤ) ≤ (v j : ℤ) := by omega
      have hdb := abs_le.mp (hBdelta j)
      have hM_ge : (Bdelta : ℤ) ≤ (M : ℤ) := by dsimp only [M]; omega
      nlinarith
  let x : Fin (twoD + 1) → ℕ := fun j => ((M : ℤ) * (v j : ℤ) + δ j).toNat
  have hx0 : x ⟨0, Nat.succ_pos twoD⟩ = 0 := by
    dsimp only [x, v, δ]
    rw [vFull_zero, deltaVec_zero]; simp
  have hx_top : x ⟨twoD, Nat.lt_succ_self twoD⟩ = M * v ⟨twoD, Nat.lt_succ_self twoD⟩ := by
    dsimp only [x, v, δ, twoD]
    rw [deltaVec_top, add_zero]
    exact_mod_cast Int.toNat_of_nonneg
      (by positivity : (0 : ℤ) ≤ (M : ℤ) * (vFull n K uP uM H ⟨prefixLen n (n * (n + 2)), Nat.lt_succ_self _⟩ : ℤ))
  -- Step 6: Pick huge L so polyCoeff(x) < 2^(L - 1) for all 1 <= i <= n
  set Xmax : ℕ := Finset.univ.sup x
  set L : ℕ := n * Xmax + (twoD + 1) ^ n + 2
  have hL1 : 1 ≤ L := by dsimp only [L]; omega
  -- Construct k as altBlockVal d L (x twoD) (polyCoeff twoD 1 x)!
  have hcoeff_lt : ∀ i, 1 ≤ i → i ≤ n → ∀ S, polyCoeff twoD i x S < 2 ^ (L - 1) := by
    intro i hi1 hin S
    have hle := polyCoeff_le twoD i S Xmax x (fun j => Finset.le_sup (f := x) (Finset.mem_univ j))
    have h1 : (twoD + 1) ^ i ≤ (twoD + 1) ^ n := Nat.pow_le_pow_right (by omega) hin
    have h2 : (twoD + 1) ^ n < 2 ^ ((twoD + 1) ^ n) := Nat.lt_two_pow_self
    have h3 : i * Xmax ≤ n * Xmax := Nat.mul_le_mul_right Xmax hin
    have h4 : 2 ^ (i * Xmax) ≤ 2 ^ (n * Xmax) := Nat.pow_le_pow_right (by norm_num) h3
    have h5 : (twoD + 1) ^ i * 2 ^ (i * Xmax) < 2 ^ ((twoD + 1) ^ n) * 2 ^ (n * Xmax) := by
      calc (twoD + 1) ^ i * 2 ^ (i * Xmax)
          ≤ (twoD + 1) ^ i * 2 ^ (n * Xmax) := Nat.mul_le_mul_left _ h4
        _ < 2 ^ ((twoD + 1) ^ n) * 2 ^ (n * Xmax) :=
            Nat.mul_lt_mul_of_pos_right (lt_of_le_of_lt h1 h2) (by positivity)
    rw [← pow_add] at h5
    have h6 : 2 ^ ((twoD + 1) ^ n + n * Xmax) ≤ 2 ^ (L - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by dsimp only [L]; omega)
    omega
  -- Define k using altBlockVal at i = 1!
  have htwoD_eq : twoD = 2 * d := by omega
  set k : ℕ := altBlockVal d L (x ⟨twoD, Nat.lt_succ_self twoD⟩) (polyCoeff twoD 1 x)
  have hk_z : (k : ℤ) = ∑ j : Fin (twoD + 1), (-1 : ℤ) ^ (j : ℕ) * (2 ^ x j : ℤ) * (2 ^ L : ℤ) ^ (j : ℕ) := by
    have hcast := altBlockVal_cast_eq d L (x ⟨twoD, Nat.lt_succ_self twoD⟩) hd1 (polyCoeff twoD 1 x)
      (fun s hs => polyCoeff_pos twoD 1 s x (by omega))
      (fun s hs => lt_of_lt_of_le (hcoeff_lt 1 (le_refl 1) hn s)
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
      (lt_of_lt_of_le (hcoeff_lt 1 (le_refl 1) hn (2 * d - 1))
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
      (by
        have := polyCoeff_top twoD 1 x
        simpa [htwoD_eq] using this)
    have hpow1 := signed_sum_pow twoD L 1 x
    simp only [pow_one, one_mul, htwoD_eq] at hpow1
    rw [hcast, ← hpow1]
  refine ⟨k, ?_⟩
  intro i hi1 hin
  rw [isDigitallyBalanced_iff]
  -- Show k^i = altBlockVal (i * d) L (i * x twoD) (polyCoeff twoD i x)!
  have hki_eq : k ^ i = altBlockVal (i * d) L (i * x ⟨twoD, Nat.lt_succ_self twoD⟩) (polyCoeff twoD i x) := by
    apply Nat.cast_injective (R := ℤ)
    push_cast
    rw [hk_z, signed_sum_pow]
    have hid1 : 1 ≤ i * d := Nat.mul_pos hi1 hd1
    have h2id : 2 * (i * d) = i * twoD := by rw [htwoD_eq]; ring
    have hcast := altBlockVal_cast_eq (i * d) L (i * x ⟨twoD, Nat.lt_succ_self twoD⟩) hid1
      (polyCoeff twoD i x)
      (fun s hs => polyCoeff_pos twoD i s x (by omega))
      (fun s hs => lt_of_lt_of_le (hcoeff_lt i hi1 hin s)
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
      (lt_of_lt_of_le (hcoeff_lt i hi1 hin (2 * (i * d) - 1))
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
      (by rw [h2id]; exact polyCoeff_top twoD i x)
    rw [hcast, h2id]
  rw [hki_eq]
  have hid1 : 1 ≤ i * d := Nat.mul_pos hi1 hd1
  have h2id : 2 * (i * d) = i * twoD := by rw [htwoD_eq]; ring
  have ⟨hpos_ki, hdiff_ki⟩ := altBlockVal_spec (i * d) L (i * x ⟨twoD, Nat.lt_succ_self twoD⟩)
    hid1 hL1 (polyCoeff twoD i x)
    (fun s hs => polyCoeff_pos twoD i s x (by omega))
    (fun s hs => lt_of_lt_of_le (hcoeff_lt i hi1 hin s)
      (Nat.pow_le_pow_right (by norm_num) (by omega)))
    (lt_of_lt_of_le (hcoeff_lt i hi1 hin (2 * (i * d) - 1))
      (Nat.pow_le_pow_right (by norm_num) (by omega)))
  refine ⟨hpos_ki, ?_⟩
  -- It suffices to show RHS of hdiff_ki = 0!
  suffices hzero_rhs :
      ((i * x ⟨twoD, Nat.lt_succ_self twoD⟩ : ℕ) : ℤ) +
      2 * (c1 (polyCoeff twoD i x 0) : ℤ) +
      2 * ∑ s ∈ Finset.Ico 1 (2 * (i * d)), (-1 : ℤ) ^ s * (c1 (polyCoeff twoD i x s - 1) : ℤ) = 0 by
    rw [hzero_rhs] at hdiff_ki
    omega
  rw [polyCoeff_zero twoD i x hx0, show c1 1 = 1 by decide, h2id, hx_top]
  -- Separation on δ for all tuples at (i, S):
  have hsep_δ_i : ∀ S, ∀ f ∈ tupleSet twoD i S, ∀ g ∈ tupleSet twoD i S,
      (∑ a : Fin i, v (f a)) = (∑ a : Fin i, v (g a)) →
      (∑ a : Fin i, δ (f a)) = (∑ a : Fin i, δ (g a)) := by
    intro S f _ g _ hweq
    have hcnt := hsep_v i hin f g hweq
    simp_rw [δ, deltaVec_eq_sum_indicator]
    rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mem_Icc] at hr
    rw [← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
      nsmul_eq_mul, nsmul_eq_mul, hcnt r hr.1 hr.2]
  have hM_big_i : 2 * i * Bdelta + (twoD + 1) ^ i < M := by
    have h1 : 2 * i * Bdelta ≤ 2 * n * Bdelta := by nlinarith
    have h2 : (twoD + 1) ^ i ≤ (twoD + 1) ^ n := Nat.pow_le_pow_right (by omega) hin
    dsimp only [M]; omega
  -- Replace each c1(polyCoeff twoD i x S - 1) using polyCoeff_c1_sub_one_of_large_M!
  have hsum_repl :
      ∑ S ∈ Finset.Ico 1 (i * twoD), (-1 : ℤ) ^ S * (c1 (polyCoeff twoD i x S - 1) : ℤ) =
      (M : ℤ) * (∑ S ∈ Finset.Ico 1 (i * twoD),
        (-1 : ℤ) ^ S * (if h : S ≤ i * twoD then (minWeight v i S h : ℤ) else 0)) +
      ∑ S ∈ Finset.Ico 1 (i * twoD),
        (-1 : ℤ) ^ S *
          (if h : S ≤ i * twoD then
            (∑ a : Fin i, δ ((exists_minWeight v i S h).choose a)) + (constD v i S h : ℤ)
          else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro S hS
    have hSle : S ≤ i * twoD := le_of_lt (Finset.mem_Ico.mp hS).2
    rw [dif_pos hSle, dif_pos hSle]
    have hspec := (exists_minWeight v i S hSle).choose_spec
    have hc1 := polyCoeff_c1_sub_one_of_large_M v δ i S M Bdelta hSle hBdelta hnonneg
      (hsep_δ_i S) hM_big_i _ hspec.1 hspec.2
    rw [hc1]; ring
  rw [hsum_repl]
  have hlin := linDiff_vFull_zero n K Hmax uP uM H hh_le hK_n hzero i hi1 hin
  dsimp only at hlin
  have hlinM : (M : ℤ) * ((i * v ⟨twoD, Nat.lt_succ_self twoD⟩ : ℤ) +
      2 * ∑ S ∈ Finset.Ico 1 (i * twoD),
        (-1 : ℤ) ^ S * (if h : S ≤ i * twoD then (minWeight v i S h : ℤ) else 0)) = 0 := by
    rw [hlin, mul_zero]
  have hdel := hdvec_zero i hi1 hin
  push_cast
  linarith

end OMA.S_oeis_a345397.Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a345397.main :=
  OMA.S_oeis_a345397.Proof.main_proof

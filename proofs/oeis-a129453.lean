import OMAStatements.S_oeis_a129453

open scoped BigOperators
open OMA.S_oeis_a129453

lemma tuple_gcd_two {n : ℕ} (v : Fin 2 → Fin n) :
    tupleGCD v = Nat.gcd ((v 0).val + 1) ((v 1).val + 1) := by
  have h : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  simp [tupleGCD, h, gcd_eq_nat_gcd]

lemma gcd_table_two (n : ℕ) :
    table 2 n = ∏ x : Fin n, ∏ y : Fin n, Nat.gcd (x.val+1) (y.val+1) := by
  unfold table
  simp_rw [tuple_gcd_two]
  rw [← Fintype.prod_prod_type']
  exact Fintype.prod_equiv (finTwoArrowEquiv (Fin n)) _ _ (fun _ => rfl)

lemma gcd_table_nonzero (n : ℕ) : table 2 n ≠ 0 := by
  rw [gcd_table_two]
  apply Finset.prod_ne_zero_iff.mpr
  intro x hx
  apply Finset.prod_ne_zero_iff.mpr
  intro y hy
  exact Nat.gcd_ne_zero_left (Nat.succ_ne_zero x.val)


lemma gcd_sum_dvd_fin (n d : ℕ) :
    (∑ x : Fin n, if d ∣ x.val + 1 then 1 else 0) = n / d := by
  rw [Fin.sum_univ_eq_sum_range (fun x : ℕ => if d ∣ x+1 then (1 : ℕ) else 0) n]
  simpa using Nat.card_multiples n d

lemma gcd_sum_pair_dvd (n d : ℕ) :
    (∑ x : Fin n, ∑ y : Fin n,
      if d ∣ x.val + 1 ∧ d ∣ y.val + 1 then 1 else 0) = (n / d)^2 := by
  calc
    _ = ∑ x : Fin n, ∑ y : Fin n,
          (if d ∣ x.val + 1 then 1 else 0) * (if d ∣ y.val + 1 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hx : d ∣ x.val + 1 <;> by_cases hy : d ∣ y.val + 1 <;> simp [hx, hy]
    _ = (∑ x : Fin n, if d ∣ x.val + 1 then 1 else 0) *
          (∑ y : Fin n, if d ∣ y.val + 1 then 1 else 0) := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
    _ = (n / d)^2 := by rw [gcd_sum_dvd_fin]; ring

lemma gcd_factorization_sum {n p b : ℕ} (hp : p.Prime)
    (hb : Nat.log p n < b) (x y : Fin n) :
    (Nat.gcd (x.val+1) (y.val+1)).factorization p =
      ∑ i ∈ Finset.Ico 1 b,
        if p^i ∣ x.val+1 ∧ p^i ∣ y.val+1 then 1 else 0 := by
  have hpos : 0 < Nat.gcd (x.val+1) (y.val+1) := Nat.gcd_pos_of_pos_left _ (by omega)
  have hle : Nat.gcd (x.val+1) (y.val+1) ≤ n :=
    (Nat.gcd_le_left _ (by omega)).trans (by omega)
  rw [Nat.factorization_eq_card_pow_dvd_of_lt hp hpos
    (lt_of_le_of_lt hle (Nat.lt_pow_of_log_lt hp.one_lt hb))]
  simp [Nat.dvd_gcd_iff]

lemma gcd_table_factorization (n p b : ℕ) (hp : p.Prime)
    (hb : Nat.log p n < b) :
    (table 2 n).factorization p = ∑ i ∈ Finset.Ico 1 b, (n / p^i)^2 := by
  rw [gcd_table_two]
  rw [Nat.factorization_prod_apply]
  · simp_rw [Nat.factorization_prod_apply (fun y _ => Nat.gcd_ne_zero_left (Nat.succ_ne_zero _))]
    simp_rw [gcd_factorization_sum hp hb]
    simp_rw [Finset.sum_comm (s := Finset.univ) (t := Finset.Ico 1 b)]
    apply Finset.sum_congr rfl
    intro i hi
    exact gcd_sum_pair_dvd n (p^i)
  · intro x hx
    exact Finset.prod_ne_zero_iff.mpr (fun y _ => Nat.gcd_ne_zero_left (Nat.succ_ne_zero _))

lemma oma_square_bound (a b c : ℕ) (h : a + b ≤ c) :
    a ^ 2 + b ^ 2 + c ≤ c ^ 2 + a + b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have hd : d ≤ d ^ 2 := by
    cases d with
    | zero => simp
    | succ d => nlinarith
  nlinarith [Nat.zero_le (a * b), Nat.zero_le (a * d), Nat.zero_le (b * d)]

lemma oma_sq_mod_two (n : ℕ) : n ^ 2 % 2 = n % 2 := by
  have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases h with h | h <;> simp [Nat.pow_mod, h]

lemma oma_sum_sq_mod_two {α : Type*} (s : Finset α) (f : α → ℕ) :
    (∑ i ∈ s, f i ^ 2) % 2 = (∑ i ∈ s, f i) % 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [Nat.add_mod (f a ^ 2) (∑ i ∈ s, f i ^ 2) 2,
      Nat.add_mod (f a) (∑ i ∈ s, f i) 2, oma_sq_mod_two, ih]

lemma oma_choose_factorization_balance (n k p b : ℕ) (hkn : k ≤ n)
    (hp : p.Prime) (hb : Nat.log p n < b) :
    (n.choose k).factorization p + (∑ i ∈ Finset.Ico 1 b, k / p ^ i) +
      (∑ i ∈ Finset.Ico 1 b, (n-k) / p ^ i) =
      ∑ i ∈ Finset.Ico 1 b, n / p ^ i := by
  have hk0 : n.choose k ≠ 0 := Nat.ne_of_gt (Nat.choose_pos hkn)
  have h := congrArg (fun t : ℕ => t.factorization p)
    (Nat.choose_mul_factorial_mul_factorial hkn)
  simpa only [Nat.factorization_mul hk0 (Nat.factorial_ne_zero k),
    Nat.factorization_mul (mul_ne_zero hk0 (Nat.factorial_ne_zero k))
      (Nat.factorial_ne_zero (n-k)), Finsupp.add_apply,
    Nat.factorization_factorial hp hb,
    Nat.factorization_factorial hp ((Nat.log_mono_right hkn).trans_lt hb),
    Nat.factorization_factorial hp ((Nat.log_mono_right (Nat.sub_le n k)).trans_lt hb)] using h

lemma oma_exponent_bridge (T : ℕ → ℕ) (hT0 : ∀ n, T n ≠ 0)
    (hT : ∀ n p b : ℕ, p.Prime → Nat.log p n < b →
      (T n).factorization p = ∑ i ∈ Finset.Ico 1 b, (n / p ^ i) ^ 2)
    (n k : ℕ) (hkn : k ≤ n) :
    T (n-k) * T k * n.choose k ≠ 0 ∧
      ∀ p : ℕ, p.Prime →
        (T (n-k) * T k * n.choose k).factorization p ≤ (T n).factorization p ∧
        Even ((T n).factorization p -
          (T (n-k) * T k * n.choose k).factorization p) := by
  have hc0 : n.choose k ≠ 0 := Nat.ne_of_gt (Nat.choose_pos hkn)
  refine ⟨mul_ne_zero (mul_ne_zero (hT0 _) (hT0 _)) hc0, ?_⟩
  intro p hp
  let b := Nat.log p n + 1
  have hb : Nat.log p n < b := by dsimp [b]; omega
  have hbk : Nat.log p k < b := (Nat.log_mono_right hkn).trans_lt hb
  have hbm : Nat.log p (n-k) < b := (Nat.log_mono_right (Nat.sub_le n k)).trans_lt hb
  have hchoose := oma_choose_factorization_balance n k p b hkn hp hb
  have hsum :
      (∑ i ∈ Finset.Ico 1 b, ((n-k) / p ^ i) ^ 2) +
      (∑ i ∈ Finset.Ico 1 b, (k / p ^ i) ^ 2) +
      (∑ i ∈ Finset.Ico 1 b, n / p ^ i) ≤
      (∑ i ∈ Finset.Ico 1 b, (n / p ^ i) ^ 2) +
      (∑ i ∈ Finset.Ico 1 b, (n-k) / p ^ i) +
      (∑ i ∈ Finset.Ico 1 b, k / p ^ i) := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    apply oma_square_bound
    have hd := @Nat.div_add_div_le_add_div (n-k) k (p^i)
    simpa only [Nat.sub_add_cancel hkn] using hd
  have hd : (T (n-k) * T k * n.choose k).factorization p =
      (T (n-k)).factorization p + (T k).factorization p +
      (n.choose k).factorization p := by
    simp only [Nat.factorization_mul (hT0 (n-k)) (hT0 k),
      Nat.factorization_mul (mul_ne_zero (hT0 (n-k)) (hT0 k)) hc0,
      Finsupp.add_apply]
  rw [hd, hT n p b hp hb, hT k p b hp hbk, hT (n-k) p b hp hbm]
  have hle :
      (∑ i ∈ Finset.Ico 1 b, ((n-k) / p ^ i) ^ 2) +
      (∑ i ∈ Finset.Ico 1 b, (k / p ^ i) ^ 2) +
      (n.choose k).factorization p ≤
      (∑ i ∈ Finset.Ico 1 b, (n / p ^ i) ^ 2) := by omega
  refine ⟨hle, ?_⟩
  have hnmod := oma_sum_sq_mod_two (Finset.Ico 1 b) (fun i => n / p ^ i)
  have hkmod := oma_sum_sq_mod_two (Finset.Ico 1 b) (fun i => k / p ^ i)
  have hmmod := oma_sum_sq_mod_two (Finset.Ico 1 b) (fun i => (n-k) / p ^ i)
  rw [Nat.even_iff]
  omega

lemma f02_exists_mul_square_of_factorization {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ p : ℕ, p.Prime →
      b.factorization p ≤ a.factorization p ∧
      Even (a.factorization p - b.factorization p)) :
    ∃ z : ℕ, a = b * z ^ 2 := by
  let f := (a.factorization - b.factorization).mapRange (· / 2) (Nat.zero_div 2)
  let z := f.prod (fun p e => p ^ e)
  have hf : ∀ p ∈ f.support, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors
      (Finsupp.support_tsub (Finsupp.support_mapRange hp))
  have hz : z ≠ 0 := by
    change (∏ p ∈ f.support, p ^ f p) ≠ 0
    exact Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (hf p hp).ne_zero
  refine ⟨z, Nat.eq_of_factorization_eq ha (mul_ne_zero hb (pow_ne_zero 2 hz)) ?_⟩
  intro p
  rw [Nat.factorization_mul hb (pow_ne_zero 2 hz), Nat.factorization_pow]
  have hzf : z.factorization = f := Nat.prod_pow_factorization_eq_self hf
  rw [hzf]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, f,
    Finsupp.mapRange_apply, Finsupp.tsub_apply]
  by_cases hp : p.Prime
  · obtain ⟨hle, heven⟩ := h p hp
    rw [Nat.mul_div_cancel' heven.two_dvd]
    omega
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

theorem OMA.solution : type_of% @OMA.S_oeis_a129453.main := by
  intro n k hkn
  obtain ⟨hden, hexponents⟩ :=
    oma_exponent_bridge (table 2) gcd_table_nonzero gcd_table_factorization n k hkn
  exact f02_exists_mul_square_of_factorization (gcd_table_nonzero n) hden hexponents


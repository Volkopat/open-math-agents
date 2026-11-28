import OMAStatements.S_oeis_a178536

namespace OMA.P178536

open OMA.S_oeis_a178536 Finset

def f (d : ℕ) : ℤ := if d = 0 then 1 else (Nat.fib d : ℤ)

def S (n k : ℕ) : ℤ := ∑ m ∈ range (n / k), f (n - (m + 1) * k)

def F (N : ℕ) : ℤ := ∑ r ∈ range (N + 1), f r

lemma F_eq (N : ℕ) : F N = (Nat.fib (N + 2) : ℤ) := by
  induction N with
  | zero => simp [F, f]
  | succ N ih =>
    unfold F at ih ⊢
    have hf : f (N + 1) = (Nat.fib (N + 1) : ℤ) := by simp [f]
    have h2 : Nat.fib (N + 1 + 2) = Nat.fib (N + 1) + Nat.fib (N + 2) := Nat.fib_add_two
    rw [sum_range_succ, ih, hf, h2]
    push_cast
    ring

lemma F_succ (N : ℕ) : F (N + 1) = F N + f (N + 1) := by
  unfold F; rw [sum_range_succ]

lemma S_lt {n k : ℕ} (h : n < k) : S n k = 0 := by
  unfold S; rw [Nat.div_eq_of_lt h]; simp

lemma S_step {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) : S n k = f (n - k) + S (n - k) k := by
  unfold S
  have hq : n / k = (n - k) / k + 1 := by
    have : n = (n - k) + k := by omega
    conv_lhs => rw [this]
    exact Nat.add_div_right _ (by omega)
  rw [hq, sum_range_succ', add_comm]
  congr 1
  · simp
  · apply sum_congr rfl
    intro i _
    congr 1
    have : (i + 1 + 1) * k = k + (i + 1) * k := by ring
    omega

lemma S_self {n : ℕ} (hn : 1 ≤ n) : S n n = 1 := by
  unfold S
  rw [Nat.div_self hn]
  simp [f]

lemma Win : ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, k ≤ n → ∑ i ∈ range k, S (n - i) k = F (n - k) := by
  intro k hk n hkn
  induction n, hkn using Nat.le_induction with
  | base =>
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [sum_range_succ']
    have h0 : ∑ i ∈ range k', S (k' + 1 - (i + 1)) (k' + 1) = 0 := by
      apply sum_eq_zero
      intro i hi
      rw [mem_range] at hi
      exact S_lt (by omega)
    rw [h0, Nat.sub_zero, S_self hk]
    simp [F, f]
  | succ n hn ih =>
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [sum_range_succ] at ih
    rw [sum_range_succ']
    have e1 : ∀ i ∈ range k', S (n + 1 - (i + 1)) (k' + 1) = S (n - i) (k' + 1) := by
      intro i _; congr 1; omega
    rw [sum_congr rfl e1]
    have hs := S_step (n := n + 1) hk (by omega)
    have e3 : n + 1 - (k' + 1) = (n - (k' + 1)) + 1 := by omega
    have e2 : n + 1 - (k' + 1) = n - k' := by omega
    have hF := F_succ (n - (k' + 1))
    rw [← e3, e2] at hF
    rw [e2] at hs
    rw [Nat.sub_zero, e2]
    linarith

lemma T_eq : ∀ n k : ℕ, 1 ≤ k → T n k = S n k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k hk
    by_cases hnk : n < k
    · rw [S_lt hnk]
      unfold T; simp [hnk]
    · rw [not_lt] at hnk
      by_cases hk1 : k = 1
      · subst hk1
        have hn1 : 1 ≤ n := hnk
        have := Win 1 le_rfl n hn1
        simp only [sum_range_one, Nat.sub_zero] at this
        rw [this, F_eq, show n - 1 + 2 = n + 1 by omega]
        unfold T
        simp [show ¬ n < 1 by omega]
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
        have hT : T n (j + 2) = (∑ i ∈ range (j + 1), T (n - (i + 1)) (j + 1)) -
            (∑ i ∈ range (j + 1), T (n - (i + 1)) (j + 2)) := by
          rw [T]
          simp only [show ¬ (j + 2 = 0 ∨ n < j + 2) by omega, if_false,
            show j + 2 ≠ 1 by omega]
          simp
        rw [hT]
        have e1 : ∑ i ∈ range (j + 1), T (n - (i + 1)) (j + 1)
            = ∑ i ∈ range (j + 1), S (n - (i + 1)) (j + 1) :=
          sum_congr rfl (fun i _ => ih _ (by omega) _ (by omega))
        have e2 : ∑ i ∈ range (j + 1), T (n - (i + 1)) (j + 2)
            = ∑ i ∈ range (j + 1), S (n - (i + 1)) (j + 2) :=
          sum_congr rfl (fun i _ => ih _ (by omega) _ (by omega))
        rw [e1, e2]
        -- first sum: window of length j+1 at n-1
        have w1 := Win (j + 1) (by omega) (n - 1) (by omega)
        have w1' : ∑ i ∈ range (j + 1), S (n - (i + 1)) (j + 1) = F (n - (j + 2)) := by
          rw [show n - (j + 2) = n - 1 - (j + 1) by omega, ← w1]
          exact sum_congr rfl (fun i _ => by congr 1; omega)
        rw [w1']
        rcases Nat.eq_or_lt_of_le hnk with h | h
        · subst h
          have hz : ∑ i ∈ range (j + 1), S (j + 2 - (i + 1)) (j + 2) = 0 :=
            sum_eq_zero (fun i hi => S_lt (by rw [mem_range] at hi; omega))
          rw [hz, S_self (by omega)]
          simp [F, f]
        · have w2 := Win (j + 2) (by omega) (n - 1) (by omega)
          rw [sum_range_succ] at w2
          have hs := S_step (n := n) (k := j + 2) (by omega) hnk
          have e5 : n - 1 - (j + 2) + 1 = n - (j + 2) := by omega
          have hF := F_succ (n - 1 - (j + 2))
          rw [e5] at hF
          have e6 : n - 1 - (j + 1) = n - (j + 2) := by omega
          rw [e6] at w2
          have e7 : ∑ i ∈ range (j + 1), S (n - 1 - i) (j + 2)
              = ∑ i ∈ range (j + 1), S (n - (i + 1)) (j + 2) :=
            sum_congr rfl (fun i _ => by congr 1; omega)
          rw [e7] at w2
          linarith

lemma S_filter {n k : ℕ} (hk : 1 ≤ k) :
    S n k = ∑ j ∈ (Icc 1 n).filter (fun j => k ∣ j), f (n - j) := by
  unfold S
  have hset : (Icc 1 n).filter (fun j => k ∣ j) = (range (n / k)).image (fun m => (m + 1) * k) := by
    ext j
    simp only [mem_filter, mem_Icc, mem_image, mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨c, rfl⟩⟩
      have hc : 1 ≤ c := by
        rcases Nat.eq_zero_or_pos c with h | h
        · subst h; simp at h1
        · exact h
      refine ⟨c - 1, ?_, ?_⟩
      · have h3 : (c - 1 + 1) * k ≤ n := by rw [Nat.sub_add_cancel hc, mul_comm]; exact h2
        have := (Nat.le_div_iff_mul_le (by omega : 0 < k)).mpr h3
        omega
      · rw [Nat.sub_add_cancel hc, mul_comm]
    · rintro ⟨m, hm, rfl⟩
      have h3 := (Nat.le_div_iff_mul_le (by omega : 0 < k)).mp (by omega : m + 1 ≤ n / k)
      refine ⟨⟨?_, h3⟩, ⟨m + 1, by ring⟩⟩
      exact Nat.mul_pos (by omega) (by omega)
  rw [hset, sum_image]
  intro x _ y _ h
  have : x + 1 = y + 1 := Nat.eq_of_mul_eq_mul_right (by omega) h
  omega

lemma S_two : ∀ n : ℕ, 2 ≤ n → S n 2 = f (n - 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases h2 : n = 2
    · subst h2; rw [S_self (by omega)]; simp [f]
    by_cases h3 : n = 3
    · subst h3
      rw [S_step (by omega) (by omega), S_lt (by omega : 3 - 2 < 2)]
      simp [f]
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
      rw [S_step (by omega) (by omega), show j + 2 - 2 = j by omega, ih j (by omega) (by omega)]
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have h4 : Nat.fib (i + 1 + 2) = Nat.fib (i + 1) + Nat.fib (i + 2) := Nat.fib_add_two
      simp only [f, show i + 1 - 1 = i by omega, show i + 1 + 2 - 1 = i + 2 by omega,
        show i + 1 ≠ 0 by omega, show i + 2 ≠ 0 by omega, show i + 1 + 1 ≠ 0 by omega]
      have hi : i ≠ 0 := by omega
      have h5 : Nat.fib (i + 2) = Nat.fib i + Nat.fib (i + 1) := Nat.fib_add_two
      rw [if_neg hi]
      simp only [↓reduceIte]
      rw [h5]
      push_cast
      ring

def c (j : ℕ) : ℤ := (if j = 1 then 1 else 0) - (if 2 ∣ j then 1 else 0)

def a0 (n : ℕ) : ℤ := ∑ k ∈ n.divisors, (ArithmeticFunction.moebius (n / k) : ℤ) * c k

lemma a0_div (j : ℕ) (hj : 0 < j) : ∑ d ∈ j.divisors, a0 d = c j := by
  have := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (f := a0) (g := c)).mpr
  apply this _ j hj
  intro n hn
  simp only [Int.cast_id]
  rw [Nat.sum_divisorsAntidiagonal' (f := fun x y => (ArithmeticFunction.moebius x : ℤ) * c y)]
  rfl

lemma conv (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Icc 1 n, T n k * a0 k = if n = 1 then 1 else 0 := by
  have s1 : ∑ k ∈ Icc 1 n, T n k * a0 k = ∑ k ∈ Icc 1 n, S n k * a0 k :=
    sum_congr rfl (fun k hk => by rw [T_eq n k (mem_Icc.mp hk).1])
  have s2 : ∑ k ∈ Icc 1 n, S n k * a0 k
      = ∑ k ∈ Icc 1 n, ∑ j ∈ (Icc 1 n).filter (fun j => k ∣ j), f (n - j) * a0 k := by
    refine sum_congr rfl (fun k hk => ?_)
    rw [S_filter (mem_Icc.mp hk).1, sum_mul]
  have s3 : ∑ k ∈ Icc 1 n, ∑ j ∈ (Icc 1 n).filter (fun j => k ∣ j), f (n - j) * a0 k
      = ∑ j ∈ Icc 1 n, ∑ k ∈ (Icc 1 n).filter (fun k => k ∣ j), f (n - j) * a0 k := by
    apply sum_comm'
    intro k j
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨hk, ⟨hj, hkj⟩⟩
      exact ⟨⟨hk, hkj⟩, hj⟩
    · rintro ⟨⟨hk, hkj⟩, hj⟩
      exact ⟨hk, ⟨hj, hkj⟩⟩
  have s4 : ∀ j ∈ Icc 1 n,
      ∑ k ∈ (Icc 1 n).filter (fun k => k ∣ j), f (n - j) * a0 k = f (n - j) * c j := by
    intro j hj
    rw [mem_Icc] at hj
    have hset : (Icc 1 n).filter (fun k => k ∣ j) = j.divisors := by
      ext k
      simp only [mem_filter, mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨_, h⟩; exact ⟨h, by omega⟩
      · rintro ⟨h, _⟩
        have := Nat.le_of_dvd (by omega) h
        exact ⟨⟨Nat.pos_of_dvd_of_pos h (by omega), by omega⟩, h⟩
    rw [hset, ← mul_sum, a0_div j (by omega)]
  have s5 : ∑ j ∈ Icc 1 n, f (n - j) * c j = f (n - 1) - S n 2 := by
    unfold c
    simp only [mul_sub, sum_sub_distrib, mul_ite, mul_one, mul_zero]
    rw [sum_ite_eq' (Icc 1 n) 1 (fun j => f (n - j)), S_filter (by norm_num), sum_filter]
    simp [mem_Icc, hn]
  rw [s1, s2, s3, sum_congr rfl s4, s5]
  by_cases h1 : n = 1
  · subst h1
    rw [S_lt (by norm_num)]
    simp [f]
  · rw [S_two n (by omega)]
    simp [h1]

theorem main' (a : ℕ → ℤ) (ha : ∀ n : ℕ, 1 ≤ n →
        ∑ k ∈ Finset.Icc 1 n, T n k * a k = if n = 1 then 1 else 0) :
    ∀ n : ℕ, 1 ≤ n → a n = a0 n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h1 := ha (m + 1) hn
    have h2 := conv (m + 1) hn
    rw [sum_Icc_succ_top (by omega)] at h1 h2
    have hd : T (m + 1) (m + 1) = 1 := by rw [T_eq _ _ hn, S_self hn]
    have hs : ∑ k ∈ Icc 1 m, T (m + 1) k * a k = ∑ k ∈ Icc 1 m, T (m + 1) k * a0 k :=
      sum_congr rfl (fun k hk => by
        rw [mem_Icc] at hk
        rw [ih k (by omega) hk.1])
    rw [hd] at h1 h2
    linarith

end OMA.P178536

open OMA.S_oeis_a178536 OMA.P178536 in
theorem OMA.solution : type_of% @OMA.S_oeis_a178536.main := by
  intro a ha n hn
  exact main' a ha n hn

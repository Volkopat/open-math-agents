import OMAStatements.S_oeis_a114890

-- Problem: A114890: First differences of A114889.
-- Upstream: formal-conjectures statements/oeis-a114890.lean:0 (declaration OMA.S_oeis_a114890.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea. Let N k = 1 + 3 + ... + 3^(k-1), so 2 N k + 1 = 3^k and N (k+1) = N k + 3^k.
-- An explicit sequence b: for N k < n <= 3^k, b n = n + N k; for 3^k < n <= N (k+1),
-- b n = 2*3^k + b (n - 3^k). Then b is strictly increasing, b maps the indices in
-- (N k, N (k+1)] into [3^k, 3^(k+1)), and the set R of its values satisfies: for
-- 3^k <= c < 3^(k+1), c is in R iff c <= N (k+1) or (c > 2*3^k and c - 2*3^k is in R).
-- By induction on k: for 0 < c < 3^k exactly one of c and 3^k - c is in R.
-- Hence no two values of b add up to a power of 3 (the only candidate is 3^(k+1) for the
-- larger one in [3^k, 3^(k+1))), and every m strictly between two consecutive values is not in R,
-- so 3^(k+1) - m is a smaller value of b. So b satisfies the greedy rule, the rule determines
-- the sequence on n >= 1, and the three cases of the conjecture follow from the formulas for b.

namespace G15A114890

open OMA.S_oeis_a114890

/-- N k = 1 + 3 + ... + 3^(k-1). -/
def N (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, 3 ^ i

theorem N_zero : N 0 = 0 := by simp [N]

theorem N_one : N 1 = 1 := by simp [N]

theorem N_succ (k : ℕ) : N (k + 1) = N k + 3 ^ k := by
  unfold N
  exact Finset.sum_range_succ _ _

theorem pow3_succ (k : ℕ) : 3 ^ (k + 1) = 3 ^ k * 3 := by ring

theorem two_N (k : ℕ) : 2 * N k + 1 = 3 ^ k := by
  induction k with
  | zero => simp [N_zero]
  | succ k ih =>
    have h1 := N_succ k
    have h2 := pow3_succ k
    omega

theorem N_le_add (k j : ℕ) : N k ≤ N (k + j) := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    have h1 := N_succ (k + j)
    have h2 : 0 < 3 ^ (k + j) := by positivity
    rw [← Nat.add_assoc]
    omega

theorem N_ge (n : ℕ) : n ≤ N n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have h1 := N_succ n
    have h2 : 0 < 3 ^ n := by positivity
    omega

/-- F k n is the explicit sequence at n, correct for n <= N k. -/
def F : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n =>
    if n ≤ N k then F k n else if n ≤ 3 ^ k then n + N k else 2 * 3 ^ k + F k (n - 3 ^ k)

/-- The explicit sequence. -/
def b (n : ℕ) : ℕ := F n n

theorem F_succ (k n : ℕ) : F (k + 1) n =
    if n ≤ N k then F k n else if n ≤ 3 ^ k then n + N k else 2 * 3 ^ k + F k (n - 3 ^ k) :=
  rfl

theorem F_low (k n : ℕ) (h : n ≤ N k) : F (k + 1) n = F k n := by
  rw [F_succ, if_pos h]

theorem F_A (k n : ℕ) (h1 : N k < n) (h2 : n ≤ 3 ^ k) : F (k + 1) n = n + N k := by
  rw [F_succ, if_neg (show ¬ n ≤ N k by omega), if_pos h2]

theorem F_B (k n : ℕ) (h1 : N k < n) (h2 : 3 ^ k < n) :
    F (k + 1) n = 2 * 3 ^ k + F k (n - 3 ^ k) := by
  rw [F_succ, if_neg (show ¬ n ≤ N k by omega), if_neg (show ¬ n ≤ 3 ^ k by omega)]

theorem F_stable (k n : ℕ) (h : n ≤ N k) (j : ℕ) : F (k + j) n = F k n := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← Nat.add_assoc, F_low (k + j) n (le_trans h (N_le_add k j)), ih]

theorem b_eq (k n : ℕ) (h : n ≤ N k) : b n = F k n := by
  unfold b
  rcases le_total n k with hk | hk
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    exact (F_stable n n (N_ge n) j).symm
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    exact F_stable k (k + j) h j

theorem bA (k n : ℕ) (h1 : N k < n) (h2 : n ≤ 3 ^ k) : b n = n + N k := by
  have hs := N_succ k
  rw [b_eq (k + 1) n (by omega), F_A k n h1 h2]

theorem bB (k n : ℕ) (h2 : 3 ^ k < n) (h3 : n ≤ N (k + 1)) :
    b n = 2 * 3 ^ k + b (n - 3 ^ k) := by
  have hN := two_N k
  have hs := N_succ k
  rw [b_eq (k + 1) n h3, F_B k n (by omega) h2, b_eq k (n - 3 ^ k) (by omega)]

theorem b1 : b 1 = 1 := by
  have e := bA 0 1 (by simp [N]) (by norm_num)
  have e0 := N_zero
  omega

theorem b2 : b 2 = 3 := by
  have e := bA 1 2 (by simp [N]) (by norm_num)
  have e1 := N_one
  omega

theorem b_Nsucc (k : ℕ) : b (N k + 1) = 3 ^ k := by
  have hN := two_N k
  have e := bA k (N k + 1) (by omega) (by omega)
  omega

theorem b_lt (k : ℕ) : ∀ n, 1 ≤ n → n ≤ N k → 1 ≤ b n ∧ b n < 3 ^ k := by
  induction k with
  | zero =>
    intro n h1 h2
    rw [N_zero] at h2
    omega
  | succ k ih =>
    intro n h1 h2
    have hN := two_N k
    have hs := N_succ k
    have hp := pow3_succ k
    rcases le_or_gt n (N k) with h3 | h3
    · have h4 := ih n h1 h3
      omega
    · rcases le_or_gt n (3 ^ k) with h4 | h4
      · have e := bA k n h3 h4
        omega
      · have h5 := ih (n - 3 ^ k) (by omega) (by omega)
        have e := bB k n h4 h2
        omega

theorem b_ge (k n : ℕ) (h1 : N k < n) (h2 : n ≤ N (k + 1)) : 3 ^ k ≤ b n := by
  have hN := two_N k
  rcases le_or_gt n (3 ^ k) with h4 | h4
  · have e := bA k n h1 h4
    omega
  · have e := bB k n h4 h2
    omega

theorem level (n : ℕ) (hn : 1 ≤ n) : ∃ k, N k < n ∧ n ≤ N (k + 1) := by
  induction n, hn using Nat.le_induction with
  | base => exact ⟨0, by simp [N], by simp [N]⟩
  | succ n hn ih =>
    obtain ⟨k, h1, h2⟩ := ih
    rcases lt_or_eq_of_le h2 with h3 | h3
    · exact ⟨k, by omega, by omega⟩
    · have h4 := N_succ (k + 1)
      have h5 : 0 < 3 ^ (k + 1) := by positivity
      exact ⟨k + 1, by omega, by omega⟩

theorem b_succ_lt (k : ℕ) : ∀ n, 1 ≤ n → n < N k → b n < b (n + 1) := by
  induction k with
  | zero =>
    intro n h1 h2
    rw [N_zero] at h2
    omega
  | succ k ih =>
    intro n h1 h2
    have hN := two_N k
    have hs := N_succ k
    rcases lt_trichotomy n (N k) with h3 | h3 | h3
    · exact ih n h1 h3
    · subst h3
      have h5 := (b_lt k (N k) h1 le_rfl).2
      have e := bA k (N k + 1) (by omega) (by omega)
      omega
    · rcases lt_trichotomy n (3 ^ k) with h4 | h4 | h4
      · have e1 := bA k n h3 (by omega)
        have e2 := bA k (n + 1) (by omega) (by omega)
        omega
      · have e1 := bA k n h3 (by omega)
        have e2 := bB k (n + 1) (by omega) (by omega)
        rw [show n + 1 - 3 ^ k = 1 by omega, b1] at e2
        omega
      · have h6 := ih (n - 3 ^ k) (by omega) (by omega)
        have e1 := bB k n h4 (by omega)
        have e2 := bB k (n + 1) (by omega) (by omega)
        rw [show n + 1 - 3 ^ k = n - 3 ^ k + 1 by omega] at e2
        omega

theorem b_strict (n : ℕ) (hn : 1 ≤ n) : b n < b (n + 1) := by
  have h := N_ge (n + 1)
  exact b_succ_lt (n + 1) n hn (by omega)

theorem b_mono (i t : ℕ) (hi : 1 ≤ i) : b i < b (i + 1 + t) := by
  induction t with
  | zero => exact b_strict i hi
  | succ t ih =>
    have h := b_strict (i + 1 + t) (by omega)
    rw [show i + 1 + (t + 1) = i + 1 + t + 1 by omega]
    omega

theorem b_lt_of_lt {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) : b i < b j := by
  obtain ⟨t, rfl⟩ : ∃ t, j = i + 1 + t := ⟨j - (i + 1), by omega⟩
  exact b_mono i t hi

theorem b_le_of_le {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) : b i ≤ b j := by
  rcases eq_or_lt_of_le hij with h | h
  · exact le_of_eq (congrArg b h)
  · exact le_of_lt (b_lt_of_lt hi h)

/-- The set of values of b at indices n >= 1. -/
abbrev R (c : ℕ) : Prop := ∃ i, 1 ≤ i ∧ b i = c

theorem idx_level (k i : ℕ) (hi : 1 ≤ i) (h1 : 3 ^ k ≤ b i) (h2 : b i < 3 ^ (k + 1)) :
    N k < i ∧ i ≤ N (k + 1) := by
  constructor
  · by_contra h
    have h3 := (b_lt k i hi (by omega)).2
    omega
  · by_contra h
    have h3 : b (N (k + 1) + 1) ≤ b i := b_le_of_le (by omega) (by omega)
    rw [b_Nsucc (k + 1)] at h3
    omega

theorem R_level (k c : ℕ) (h1 : 3 ^ k ≤ c) (h2 : c < 3 ^ (k + 1)) :
    R c ↔ (c ≤ N (k + 1) ∨ (2 * 3 ^ k < c ∧ R (c - 2 * 3 ^ k))) := by
  have hN := two_N k
  have hs := N_succ k
  have hp := pow3_succ k
  constructor
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨hl1, hl2⟩ := idx_level k i hi h1 h2
    rcases le_or_gt i (3 ^ k) with h3 | h3
    · left
      have e := bA k i hl1 h3
      omega
    · right
      have h4 := (b_lt k (i - 3 ^ k) (by omega) (by omega)).1
      have e := bB k i h3 hl2
      exact ⟨by omega, i - 3 ^ k, by omega, by omega⟩
  · rintro (h3 | ⟨h3, i, hi, hbi⟩)
    · refine ⟨c - N k, by omega, ?_⟩
      have e := bA k (c - N k) (by omega) (by omega)
      omega
    · have h4 : i ≤ N k := by
        by_contra h5
        have h6 : b (N k + 1) ≤ b i := b_le_of_le (by omega) (by omega)
        rw [b_Nsucc k] at h6
        omega
      refine ⟨i + 3 ^ k, by omega, ?_⟩
      have e := bB k (i + 3 ^ k) (by omega) (by omega)
      rw [show i + 3 ^ k - 3 ^ k = i by omega] at e
      omega

theorem CL (k : ℕ) : ∀ c, 0 < c → c < 3 ^ k → (R c ↔ ¬ R (3 ^ k - c)) := by
  induction k with
  | zero =>
    intro c h1 h2
    exfalso
    rw [Nat.pow_zero] at h2
    omega
  | succ k ih =>
    have hN := two_N k
    have hs := N_succ k
    have hp := pow3_succ k
    have big : ∀ c, N (k + 1) < c → c < 3 ^ (k + 1) → (R c ↔ ¬ R (3 ^ (k + 1) - c)) := by
      intro c h1 h2
      rw [R_level k c (by omega) h2]
      rcases le_or_gt c (2 * 3 ^ k) with h3 | h3
      · have hc' : R (3 ^ (k + 1) - c) :=
          (R_level k (3 ^ (k + 1) - c) (by omega) (by omega)).2 (Or.inl (by omega))
        constructor
        · rintro (h | ⟨h, _⟩) _ <;> omega
        · intro h
          exact absurd hc' h
      · have e1 := ih (c - 2 * 3 ^ k) (by omega) (by omega)
        rw [show 3 ^ k - (c - 2 * 3 ^ k) = 3 ^ (k + 1) - c by omega] at e1
        constructor
        · rintro (h | ⟨_, h⟩)
          · exact absurd h (by omega)
          · exact e1.1 h
        · intro h
          exact Or.inr ⟨h3, e1.2 h⟩
    intro c h1 h2
    rcases le_or_gt c (N (k + 1)) with h3 | h3
    · have e := big (3 ^ (k + 1) - c) (by omega) (by omega)
      rw [show 3 ^ (k + 1) - (3 ^ (k + 1) - c) = c by omega] at e
      constructor
      · intro hc hc'
        exact (e.1 hc') hc
      · intro hnc'
        by_contra hnc
        exact hnc' (e.2 hnc)
    · exact big c h3 h2

theorem bracket (m : ℕ) (hm : 1 ≤ m) : ∃ k, 3 ^ k ≤ m ∧ m < 3 ^ (k + 1) := by
  induction m, hm using Nat.le_induction with
  | base => exact ⟨0, by norm_num, by norm_num⟩
  | succ m hm ih =>
    obtain ⟨k, h1, h2⟩ := ih
    rcases lt_or_eq_of_le (show m + 1 ≤ 3 ^ (k + 1) by omega) with h3 | h3
    · exact ⟨k, by omega, h3⟩
    · have h4 := pow3_succ (k + 1)
      exact ⟨k + 1, by omega, by omega⟩

theorem sumfree (n i j : ℕ) (hi : 1 ≤ i) (hin : i < n) : b n + b i ≠ 3 ^ j := by
  intro h
  have hn : 1 ≤ n := by omega
  obtain ⟨k, hk1, hk2⟩ := level n hn
  have hx1 := b_ge k n hk1 hk2
  have hx2 := (b_lt (k + 1) n hn hk2).2
  have hy1 := (b_lt (k + 1) i hi (by omega)).1
  have hyx := b_lt_of_lt hi hin
  have hp := pow3_succ k
  have hp2 := pow3_succ (k + 1)
  have e1 : k < j := by
    by_contra hc
    have h3 := Nat.pow_le_pow_right (show 3 > 0 by norm_num) (show j ≤ k by omega)
    omega
  have e2 : j < k + 2 := by
    by_contra hc
    have h3 := Nat.pow_le_pow_right (show 3 > 0 by norm_num) (show k + 1 + 1 ≤ j by omega)
    omega
  have hj : j = k + 1 := by omega
  subst hj
  have hc := CL (k + 1) (b n) (by omega) hx2
  rw [show 3 ^ (k + 1) - b n = b i by omega] at hc
  exact (hc.1 ⟨n, hn, rfl⟩) ⟨i, hi, rfl⟩

theorem gap (n m : ℕ) (hn : 2 ≤ n) (h1 : b (n - 1) < m) (h2 : m < b n) :
    ∃ i ∈ Finset.Icc 1 (n - 1), ∃ j, m + b i = 3 ^ j := by
  have hnR : ¬ R m := by
    rintro ⟨i, hi, rfl⟩
    rcases le_or_gt i (n - 1) with h3 | h3
    · have h4 := b_le_of_le hi h3
      omega
    · have h4 := b_le_of_le (show 1 ≤ n by omega) (show n ≤ i by omega)
      omega
  obtain ⟨k, hk1, hk2⟩ := bracket m (by omega)
  have hN := two_N (k + 1)
  have hc := CL (k + 1) m (by omega) hk2
  have hR' : R (3 ^ (k + 1) - m) := by
    by_contra h
    exact hnR (hc.2 h)
  have hmN : N (k + 1) < m := by
    by_contra h
    exact hnR ((R_level k m hk1 hk2).2 (Or.inl (by omega)))
  obtain ⟨i, hi, hbi⟩ := hR'
  have hin : i ≤ n - 1 := by
    by_contra h
    have h4 := b_le_of_le (show 1 ≤ n by omega) (show n ≤ i by omega)
    omega
  exact ⟨i, Finset.mem_Icc.mpr ⟨hi, hin⟩, k + 1, by omega⟩

theorem b_spec : IsA114889 b := by
  refine ⟨b1, fun n hn => ⟨⟨?_, ?_⟩, ?_⟩⟩
  · have h := b_strict (n - 1) (by omega)
    rwa [show n - 1 + 1 = n by omega] at h
  · intro i hi j
    have hi' := Finset.mem_Icc.mp hi
    exact sumfree n i j hi'.1 (by omega)
  · intro m hm
    obtain ⟨hm1, hm2⟩ := hm
    by_contra h
    obtain ⟨i, hi, j, hj⟩ := gap n m hn hm1 (by omega)
    exact hm2 i hi j hj

theorem uniq (s : ℕ → ℕ) (hs : IsA114889 s) : ∀ n, 1 ≤ n → s n = b n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases eq_or_lt_of_le hn with h | h
    · rw [← h, hs.1, b1]
    · have hn2 : 2 ≤ n := by omega
      have hA := hs.2 n hn2
      have hB := b_spec.2 n hn2
      have hag : ∀ i, 1 ≤ i → i ≤ n - 1 → s i = b i := fun i hi1 hi2 => ih i (by omega) hi1
      have h1 : b n ∈ {m : ℕ | s (n - 1) < m ∧
          ∀ i ∈ Finset.Icc 1 (n - 1), ∀ j : ℕ, m + s i ≠ 3 ^ j} := by
        obtain ⟨⟨hb1, hb2⟩, _⟩ := hB
        refine ⟨?_, fun i hi j => ?_⟩
        · rw [hag (n - 1) (by omega) le_rfl]
          exact hb1
        · rw [hag i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2]
          exact hb2 i hi j
      have h2 : s n ∈ {m : ℕ | b (n - 1) < m ∧
          ∀ i ∈ Finset.Icc 1 (n - 1), ∀ j : ℕ, m + b i ≠ 3 ^ j} := by
        obtain ⟨⟨ha1, ha2⟩, _⟩ := hA
        refine ⟨?_, fun i hi j => ?_⟩
        · rw [← hag (n - 1) (by omega) le_rfl]
          exact ha1
        · rw [← hag i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2]
          exact ha2 i hi j
      exact le_antisymm (hA.2 h1) (hB.2 h2)

theorem d_eq (s : ℕ → ℕ) (hs : IsA114889 s) (n : ℕ) (hn : 1 ≤ n) : d s n = d b n := by
  unfold d
  rw [uniq s hs n hn, uniq s hs (n + 1) (by omega)]

theorem db_one : d b 1 = 2 := by
  have e2 : b (1 + 1) = 3 := b2
  have e1 := b1
  unfold d
  omega

theorem db_pow (k : ℕ) (hk : 1 ≤ k) : d b (3 ^ k) = ((N k : ℕ) : ℤ) + 2 := by
  have hN := two_N k
  have hs := N_succ k
  have hNk : 1 ≤ N k := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h3 := N_succ j
    have h4 : 0 < 3 ^ j := by positivity
    omega
  have e1 : b (3 ^ k) = 3 ^ k + N k := bA k (3 ^ k) (by omega) le_rfl
  have e2 := bB k (3 ^ k + 1) (by omega) (by omega)
  rw [show 3 ^ k + 1 - 3 ^ k = 1 by omega, b1] at e2
  unfold d
  omega

theorem db_rec (k n : ℕ) (h1 : 3 ^ k < n) (h2 : n < 2 * 3 ^ k - 1) :
    d b n = d b (n - 3 ^ k) := by
  have hN := two_N k
  have hs := N_succ k
  have hp := pow3_succ k
  unfold d
  rcases lt_trichotomy n (N (k + 1)) with h3 | h3 | h3
  · have e1 := bB k (n + 1) (by omega) (by omega)
    have e2 := bB k n h1 (by omega)
    rw [show n + 1 - 3 ^ k = n - 3 ^ k + 1 by omega] at e1
    omega
  · have e1 := bB k n h1 (by omega)
    have e2 := b_Nsucc (k + 1)
    have e3 := b_Nsucc k
    rw [show N (k + 1) + 1 = n + 1 by omega] at e2
    rw [show N k + 1 = n - 3 ^ k + 1 by omega] at e3
    omega
  · have e1 := bA (k + 1) n (by omega) (by omega)
    have e2 := bA (k + 1) (n + 1) (by omega) (by omega)
    have e3 := bA k (n - 3 ^ k + 1) (by omega) (by omega)
    have e4 := bA k (n - 3 ^ k) (by omega) (by omega)
    omega

theorem db_else (n : ℕ) (hn : 1 < n) (h1 : ¬ ∃ k, n = 3 ^ k)
    (h2 : ¬ ∃ k, 3 ^ k < n ∧ n < 2 * 3 ^ k - 1) : d b n = 1 := by
  obtain ⟨k, hk1, hk2⟩ := bracket n (by omega)
  have hN := two_N k
  have hs := N_succ k
  have hp := pow3_succ k
  have h3 : 3 ^ k < n := by
    rcases eq_or_lt_of_le hk1 with h | h
    · exact (h1 ⟨k, h.symm⟩).elim
    · exact h
  have h4 : 2 * 3 ^ k - 1 ≤ n := by
    by_contra h
    exact h2 ⟨k, h3, by omega⟩
  have h5 : N (k + 1) < n := by omega
  have e1 := bA (k + 1) n h5 (by omega)
  have e2 := bA (k + 1) (n + 1) (by omega) (by omega)
  unfold d
  omega

end G15A114890

theorem OMA.solution : type_of% @OMA.S_oeis_a114890.main := by
  refine ⟨⟨G15A114890.b, G15A114890.b_spec⟩, fun s hs => ⟨?_, fun n hn => ⟨?_, ?_, ?_⟩⟩⟩
  · rw [G15A114890.d_eq s hs 1 le_rfl]
    exact G15A114890.db_one
  · intro k hk
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h
        rw [Nat.pow_zero] at hk
        omega
      · exact h
    rw [G15A114890.d_eq s hs n (by omega), hk]
    exact G15A114890.db_pow k hk1
  · intro k h1 h2
    rw [G15A114890.d_eq s hs n (by omega), G15A114890.d_eq s hs (n - 3 ^ k) (by omega)]
    exact G15A114890.db_rec k n h1 h2
  · intro h1 h2
    rw [G15A114890.d_eq s hs n (by omega)]
    exact G15A114890.db_else n hn h1 h2

import OMAStatements.S_oeis_a396981
import Mathlib

namespace OMA.A396981Proof

open OMA.S_oeis_a396981 Finset

theorem exists_tri_ge (k : ℕ) : ∃ s : ℕ, k ≤ s * (s + 1) / 2 := by
  refine ⟨2 * k, ?_⟩
  have h : 2 * k * (2 * k + 1) = 2 * (k * (2 * k + 1)) := by ring
  rw [h, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  nlinarith [Nat.zero_le (k * k)]

theorem f_succ_pos (k : ℕ) : 0 < f (k + 1) := by
  unfold f
  exact (Nat.find_pos _).2 (by simp)

/-- Triangular numbers. -/
def T (j : ℕ) : ℕ := j * (j + 1) / 2

theorem T_zero : T 0 = 0 := by simp [T]

theorem T_succ (j : ℕ) : T (j + 1) = T j + (j + 1) := by
  unfold T
  have h : (j + 1) * (j + 1 + 1) = j * (j + 1) + 2 * (j + 1) := by ring
  rw [h]
  omega

theorem T_pred {j : ℕ} (hj : 1 ≤ j) : T j = T (j - 1) + j := by
  have h := T_succ (j - 1)
  rwa [Nat.sub_add_cancel hj] at h

theorem T_mono {a b : ℕ} (h : a ≤ b) : T a ≤ T b := by
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    subst ha
    exact le_rfl
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with h' | h'
    · have h2 := ih (by omega)
      rw [T_succ]
      omega
    · have ha : a = b + 1 := by omega
      subst ha
      exact le_rfl

theorem T_ge (K : ℕ) : K ≤ T K := by
  rcases K with _ | k
  · exact Nat.zero_le _
  · rw [T_succ]
    omega

theorem f_spec (k : ℕ) : k ≤ T (f k) := Nat.find_spec (exists_tri_ge k)

theorem f_min {k t : ℕ} (h : t < f k) : T t < k := by
  have h' := Nat.find_min (exists_tri_ge k) h
  unfold T
  omega

theorem f_le_of {k s : ℕ} (h : k ≤ T s) : f k ≤ s := Nat.find_min' (exists_tri_ge k) h

theorem f_eq {k s : ℕ} (h1 : k ≤ T s) (h2 : ∀ t, t < s → T t < k) : f k = s := by
  apply le_antisymm (f_le_of h1)
  by_contra hlt
  have h3 := h2 (f k) (by omega)
  have h4 := f_spec k
  omega

theorem f_block (s r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ s + 1) : f (T s + r) = s + 1 := by
  apply f_eq
  · rw [T_succ]
    omega
  · intro t ht
    have h3 := T_mono (show t ≤ s by omega)
    omega

theorem f_tri (j : ℕ) : f (T j) = j := by
  rcases j with _ | j
  · exact f_eq le_rfl (fun t ht => absurd ht (Nat.not_lt_zero _))
  · rw [T_succ]
    exact f_block j (j + 1) (by omega) le_rfl

theorem f_zero : f 0 = 0 := by
  have h := f_tri 0
  rwa [T_zero] at h

theorem f_pos {K : ℕ} (hK : 1 ≤ K) : 1 ≤ f K := by
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  exact f_succ_pos k

theorem f_le (K : ℕ) : f K ≤ K := f_le_of (T_ge K)

/-- Block coordinates: every `K ≥ 1` is `T s + r` with `1 ≤ r ≤ s + 1` (and then `f K = s + 1`). -/
theorem decomp {K : ℕ} (hK : 1 ≤ K) : ∃ s r, 1 ≤ r ∧ r ≤ s + 1 ∧ K = T s + r := by
  have h1 := f_pos hK
  have h2 : T (f K - 1) < K := f_min (by omega)
  have h3 := f_spec K
  have h4 := T_pred h1
  exact ⟨f K - 1, K - T (f K - 1), by omega, by omega, by omega⟩

theorem A_zero (k : ℕ) : A 0 k = 1 := A.eq_1 k

theorem A_succ_zero (n : ℕ) : A (n + 1) 0 = 0 := A.eq_2 n

theorem A_succ_succ (n k : ℕ) :
    A (n + 1) (k + 1) = A (n + 1) (k + 1 - f (k + 1)) + (n + f (k + 1)) * A n (k + 1) :=
  A.eq_3 n k

theorem mul_A_zero (n : ℕ) : n * A n 0 = 0 := by
  rcases n with _ | m
  · simp
  · simp [A_succ_zero]

theorem A_rec_zero (n : ℕ) : A (n + 1) 0 = A (n + 1) (0 - f 0) + (n + f 0) * A n 0 := by
  simp only [f_zero, Nat.sub_self, Nat.add_zero, mul_A_zero]

/-- The recursion holds at every `K`, including `K = 0` (where `f 0 = 0`). -/
theorem A_rec (n K : ℕ) : A (n + 1) K = A (n + 1) (K - f K) + (n + f K) * A n K := by
  rcases K with _ | k
  · exact A_rec_zero n
  · exact A_succ_succ n k

theorem A_one (K : ℕ) : A 1 K = K := by
  induction K using Nat.strong_induction_on with
  | h K ih =>
    rcases Nat.eq_zero_or_pos K with h0 | h0
    · subst h0
      exact A_succ_zero 0
    · have h1 : A 1 K = A 1 (K - f K) + (0 + f K) * A 0 K := A_rec 0 K
      have h2 := f_pos h0
      have h3 := f_le K
      rw [A_zero, ih (K - f K) (by omega)] at h1
      omega

/-- Conjecture 2 in difference form: `A(n+1, K) = A(n+1, K-1) + A(n, K + f K)` for `K ≥ 1`. -/
theorem Q_step (n : ℕ) : ∀ K, 1 ≤ K → A (n + 1) K = A (n + 1) (K - 1) + A n (K + f K) := by
  induction n with
  | zero =>
    intro K hK
    show A 1 K = A 1 (K - 1) + A 0 (K + f K)
    rw [A_one, A_one, A_zero]
    omega
  | succ n ihn =>
    intro K
    induction K using Nat.strong_induction_on with
    | h K ihK =>
      intro hK
      obtain ⟨s, r, hr1, hr2, hKsr⟩ := decomp hK
      have hTs := T_ge s
      have hf : f K = s + 1 := by
        rw [hKsr]
        exact f_block s r hr1 hr2
      have e1 : A (n + 1 + 1) K =
          A (n + 1 + 1) (K - (s + 1)) + (n + 1 + (s + 1)) * A (n + 1) K := by
        have h := A_rec (n + 1) K
        rwa [hf] at h
      have e2 : A (n + 1) K = A (n + 1) (K - 1) + A n (K + (s + 1)) := by
        have h := ihn K hK
        rwa [hf] at h
      have hKs : K + (s + 1) = T (s + 1) + r := by
        rw [T_succ]
        omega
      have hf2 : f (K + (s + 1)) = s + 1 + 1 := by
        rw [hKs]
        exact f_block (s + 1) r hr1 (by omega)
      have e3 : A (n + 1) (K + (s + 1)) =
          A (n + 1) (K - 1) + (n + (s + 1 + 1)) * A n (K + (s + 1)) := by
        have h := A_rec n (K + (s + 1))
        have hc : K + (s + 1) - (s + 1 + 1) = K - 1 := by omega
        rw [hf2, hc] at h
        exact h
      rw [hf]
      rcases Nat.lt_or_ge r 2 with hr | hr
      · have hK1 : K - 1 = T s := by omega
        have hf3 : f (K - 1) = s := by
          rw [hK1]
          exact f_tri s
        have e4 : A (n + 1 + 1) (K - 1) =
            A (n + 1 + 1) (K - (s + 1)) + (n + 1 + s) * A (n + 1) (K - 1) := by
          have h := A_rec (n + 1) (K - 1)
          have hc : K - 1 - s = K - (s + 1) := by omega
          rw [hf3, hc] at h
          exact h
        rw [e1, e2, e3, e4]
        ring
      · have hs : 1 ≤ s := by omega
        have hK1 : K - 1 = T s + (r - 1) := by omega
        have hf3 : f (K - 1) = s + 1 := by
          rw [hK1]
          exact f_block s (r - 1) (by omega) (by omega)
        have e4 : A (n + 1 + 1) (K - 1) =
            A (n + 1 + 1) (K - (s + 1) - 1) + (n + 1 + (s + 1)) * A (n + 1) (K - 1) := by
          have h := A_rec (n + 1) (K - 1)
          have hc : K - 1 - (s + 1) = K - (s + 1) - 1 := by omega
          rw [hf3, hc] at h
          exact h
        have hTp := T_pred hs
        have hf4 : f (K - (s + 1)) = s := by
          have h := f_block (s - 1) (r - 1) (by omega) (by omega)
          have hc1 : T (s - 1) + (r - 1) = K - (s + 1) := by omega
          have hc2 : s - 1 + 1 = s := by omega
          rw [hc1, hc2] at h
          exact h
        have e5 : A (n + 1 + 1) (K - (s + 1)) =
            A (n + 1 + 1) (K - (s + 1) - 1) + A (n + 1) (K - 1) := by
          have h := ihK (K - (s + 1)) (by omega) (by omega)
          have hc : K - (s + 1) + s = K - 1 := by omega
          rw [hf4, hc] at h
          exact h
        rw [e1, e2, e3, e4, e5]
        ring

/-- Conjecture 2. -/
theorem conj2 (n k : ℕ) (hn : 1 ≤ n) : A n k = ∑ j ∈ Icc 1 k, A (n - 1) (j + f j) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  induction k with
  | zero => simp [A_succ_zero]
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (show 1 ≤ k + 1 by omega), ← ih, Q_step m (k + 1) (by omega),
      Nat.add_sub_cancel]

theorem sum_shift (g : ℕ → ℕ) (a b : ℕ) :
    ∑ j ∈ Icc (a + 1) (b + 1), g (j - 1) = ∑ j ∈ Icc a b, g j := by
  rw [← Finset.map_add_right_Icc, Finset.sum_map]
  simp

theorem sum_ite_top (h : ℕ → ℕ) (a b : ℕ) :
    ∑ j ∈ Icc a (b + 1), (if j ≤ b then h j else 0) = ∑ j ∈ Icc a b, h j := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext j
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor <;> intro hj <;> omega

theorem sum_ite_bot (h : ℕ → ℕ) (b : ℕ) :
    ∑ j ∈ Icc 0 b, (if 1 ≤ j then h j else 0) = ∑ j ∈ Icc 1 b, h j := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext j
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor <;> intro hj <;> omega

/-- The sum of Conjecture 3. -/
def S (n k : ℕ) : ℕ := ∑ j ∈ Icc k n, A (n - j) (k + T j)

theorem L0 (n : ℕ) : S (n + 1) 0 = (n + 1) * S n 0 := by
  have key : ∀ j ∈ Icc 0 (n + 1), A (n + 1 - j) (T j) =
      (if 1 ≤ j then A (n - (j - 1)) (T (j - 1)) else 0) +
        n * (if j ≤ n then A (n - j) (T j) else 0) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0
      simp [T_zero, A_succ_zero, mul_A_zero]
    · rw [if_pos (show 1 ≤ j by omega)]
      rcases Nat.lt_or_ge n j with h | h
      · have hj' : j = n + 1 := by omega
        subst hj'
        rw [if_neg (show ¬ (n + 1 ≤ n) by omega), (show n + 1 - (n + 1) = 0 by omega),
          (show n - (n + 1 - 1) = 0 by omega), A_zero, A_zero]
        simp
      · rw [if_pos h]
        have hT := T_pred (show 1 ≤ j by omega)
        have e1 : T j - j = T (j - 1) := by omega
        have e2 : n - j + j = n := by omega
        have e3 : n - j + 1 = n + 1 - j := by omega
        have e4 : n - (j - 1) = n + 1 - j := by omega
        have h1 := A_rec (n - j) (T j)
        rw [f_tri, e1, e2, e3] at h1
        rw [h1, e4]
  unfold S
  simp only [Nat.zero_add]
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, ← Finset.mul_sum, sum_ite_bot, sum_ite_top]
  have hs := sum_shift (fun i => A (n - i) (T i)) 0 n
  simp only [Nat.zero_add] at hs
  rw [hs]
  ring

theorem L1 (n k : ℕ) : S (n + 1) (k + 1) = S n k + (n + 1) * S n (k + 1) := by
  have key : ∀ j ∈ Icc (k + 1) (n + 1), A (n + 1 - j) (k + 1 + T j) =
      A (n - (j - 1)) (k + T (j - 1)) +
        (n + 1) * (if j ≤ n then A (n - j) (k + 1 + T j) else 0) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hT := T_pred (show 1 ≤ j by omega)
    rcases Nat.lt_or_ge n j with h | h
    · have hj' : j = n + 1 := by omega
      subst hj'
      rw [if_neg (show ¬ (n + 1 ≤ n) by omega), (show n + 1 - (n + 1) = 0 by omega),
        (show n - (n + 1 - 1) = 0 by omega), A_zero, A_zero]
      simp
    · rw [if_pos h]
      have hf : f (k + 1 + T j) = j + 1 := by
        rw [(show k + 1 + T j = T j + (k + 1) by omega)]
        exact f_block j (k + 1) (by omega) (by omega)
      have e1 : k + 1 + T j - (j + 1) = k + T (j - 1) := by omega
      have e2 : n - j + (j + 1) = n + 1 := by omega
      have e3 : n - j + 1 = n + 1 - j := by omega
      have e4 : n - (j - 1) = n + 1 - j := by omega
      have h1 := A_rec (n - j) (k + 1 + T j)
      rw [hf, e1, e2, e3] at h1
      rw [h1, e4]
  unfold S
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, ← Finset.mul_sum, sum_ite_top]
  have hs := sum_shift (fun i => A (n - i) (k + T i)) k n
  rw [hs]

/-- Conjecture 3, with the sum written as `S`. -/
theorem conj3 (n k : ℕ) : S n k = Nat.stirlingFirst (n + 1) (k + 1) := by
  induction n generalizing k with
  | zero =>
    rcases k with _ | k
    · have h1 : S 0 0 = 1 := by simp [S, A_zero]
      exact h1.trans (Nat.stirlingFirst_self 1).symm
    · have h1 : S 0 (k + 1) = 0 := by simp [S]
      exact h1.trans (Nat.stirlingFirst_eq_zero_of_lt (by omega)).symm
  | succ n ih =>
    rcases k with _ | k
    · rw [L0, ih 0, Nat.stirlingFirst_succ_succ (n + 1) 0]
      simp
    · rw [L1, ih k, ih (k + 1), Nat.stirlingFirst_succ_succ (n + 1) (k + 1)]
      ring

theorem conj3' (n k : ℕ) :
    ∑ j ∈ Icc k n, A (n - j) (k + j * (j + 1) / 2) = Nat.stirlingFirst (n + 1) (k + 1) :=
  conj3 n k

end OMA.A396981Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a396981.main := by
  exact ⟨fun n k hn => OMA.A396981Proof.conj2 n k hn, fun n k => OMA.A396981Proof.conj3' n k⟩

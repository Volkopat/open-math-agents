import OMAStatements.S_oeis_a000966
import Mathlib

/-!
# A000966: the generating function of the skipped trailing-zero counts is not rational

Sketch. If `A * Q = P` with `Q ≠ 0`, then the coefficients of `A` satisfy a linear
recurrence with the coefficients of `Q` from some index on, and so does the second
difference `b k = a (k+2) - 2 a (k+1) + a k`.  At `n = 5 ^ J` the count of trailing zeros
jumps by `J`, so `J - 1` consecutive numbers are skipped, and `b` vanishes on arbitrarily
long windows arbitrarily far out.  Solving the recurrence through the lowest nonzero
coefficient of `Q` forces `b = 0` from there on, hence `a (k + i) = a k + i` for all `i`,
i.e. every large number is skipped.  But the trailing-zero count of `(5 ^ (a k))!` is at
least `a k` and is attained, a contradiction.
-/

open OMA.S_oeis_a000966

namespace OMA.A000966Proof

theorem tz_succ (n : ℕ) :
    trailingZeros (n + 1) = padicValNat 5 (n + 1) + trailingZeros n := by
  unfold trailingZeros
  rw [Nat.factorial_succ]
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact padicValNat.mul (Nat.succ_ne_zero n) (Nat.factorial_ne_zero n)

theorem tz_mono : Monotone trailingZeros :=
  monotone_nat_of_le_succ (fun n => by rw [tz_succ]; omega)

theorem tz_at_pow (j : ℕ) :
    trailingZeros (5 ^ j - 1 + 1) = j + trailingZeros (5 ^ j - 1) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h : 5 ^ j - 1 + 1 = 5 ^ j := Nat.sub_add_cancel (Nat.one_le_pow _ _ (by norm_num))
  rw [tz_succ, h, padicValNat.prime_pow]

theorem tz_pow (j : ℕ) : j ≤ trailingZeros (5 ^ j) := by
  have h : 5 ^ j - 1 + 1 = 5 ^ j := Nat.sub_add_cancel (Nat.one_le_pow _ _ (by norm_num))
  have h2 := tz_at_pow j
  rw [h] at h2
  omega

theorem skipped_of_gap (n m : ℕ) (h1 : trailingZeros n < m)
    (h2 : m < trailingZeros (n + 1)) : IsSkippedZeroCount m := by
  intro n' h
  rcases Nat.lt_or_ge n n' with h' | h'
  · have h3 : trailingZeros (n + 1) ≤ trailingZeros n' := tz_mono h'
    omega
  · have h3 : trailingZeros n' ≤ trailingZeros n := tz_mono h'
    omega

theorem gap (j : ℕ) :
    ∃ m0, j + 1 ≤ m0 ∧ ∀ i, i + 1 ≤ j → IsSkippedZeroCount (m0 + i) := by
  have h3 := tz_at_pow (j + 1)
  have h4 : j ≤ trailingZeros (5 ^ (j + 1) - 1) := by
    have h5 : 5 ^ j ≤ 5 ^ (j + 1) - 1 := by
      have e : 5 ^ (j + 1) = 5 ^ j * 5 := pow_succ 5 j
      have p : 0 < 5 ^ j := by positivity
      omega
    exact (tz_pow j).trans (tz_mono h5)
  refine ⟨trailingZeros (5 ^ (j + 1) - 1) + 1, by omega, fun i hi => ?_⟩
  exact skipped_of_gap (5 ^ (j + 1) - 1) _ (by omega) (by omega)

theorem skipped_infinite : (setOf IsSkippedZeroCount).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro x
  obtain ⟨m0, h1, h2⟩ := gap (x + 1)
  have h3 : IsSkippedZeroCount (m0 + 0) := h2 0 (by omega)
  exact ⟨m0, h3, by omega⟩

theorem a_mem (k : ℕ) : IsSkippedZeroCount (a k) :=
  Nat.nth_mem_of_infinite skipped_infinite k

theorem a_strictMono : StrictMono a :=
  Nat.nth_strictMono skipped_infinite

theorem a_surj {m : ℕ} (h : IsSkippedZeroCount m) : ∃ k, a k = m := by
  have h1 : m ∈ Set.range (Nat.nth IsSkippedZeroCount) := by
    rw [Nat.range_nth_of_infinite skipped_infinite]
    exact h
  exact h1

theorem a_next {k m : ℕ} (h : a k = m) (h' : IsSkippedZeroCount (m + 1)) :
    a (k + 1) = m + 1 := by
  obtain ⟨k', hk'⟩ := a_surj h'
  have h1 : a k < a (k + 1) := a_strictMono (Nat.lt_succ_self k)
  have h2 : k < k' := by
    apply a_strictMono.lt_iff_lt.mp
    omega
  have h3 : a (k + 1) ≤ a k' := a_strictMono.monotone h2
  omega

theorem window (N L : ℕ) : ∃ k, N ≤ k ∧ ∀ i, i ≤ L → a (k + i) = a k + i := by
  obtain ⟨m0, h1, h2⟩ := gap (L + 1 + a N)
  have h0 : IsSkippedZeroCount (m0 + 0) := h2 0 (by omega)
  obtain ⟨k, hk⟩ := a_surj (m := m0) h0
  refine ⟨k, ?_, ?_⟩
  · apply a_strictMono.le_iff_le.mp
    omega
  · intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      have h4 := ih (by omega)
      have h5 : IsSkippedZeroCount (a k + i + 1) := by
        rw [hk]
        exact h2 (i + 1) (by omega)
      exact a_next h4 h5

theorem rec_zero (q c : ℕ → ℚ) (s d N M : ℕ) (hs : q s ≠ 0)
    (hlow : ∀ i, i < s → q i = 0) (hhigh : ∀ i, d < i → q i = 0)
    (hrec : ∀ n, N ≤ n → ∑ i ∈ Finset.range (n + 1), q i * c (n - i) = 0)
    (hM : N ≤ M) (hwin : ∀ m, M ≤ m → m < M + d → c m = 0) :
    ∀ m, M ≤ m → c m = 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    by_cases h : m < M + d
    · exact hwin m hm h
    · have h1 := hrec (m + s) (by omega)
      rw [Finset.sum_eq_single s] at h1
      · rw [Nat.add_sub_cancel] at h1
        exact (mul_eq_zero.mp h1).resolve_left hs
      · intro i _ his
        rcases Nat.lt_or_ge i s with h2 | h2
        · rw [hlow i h2, zero_mul]
        · by_cases h3 : d < i
          · rw [hhigh i h3, zero_mul]
          · rw [ih (m + s - i) (by omega) (by omega), mul_zero]
      · intro h2
        exact absurd (Finset.mem_range.mpr (by omega)) h2

end OMA.A000966Proof

open OMA.A000966Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a000966.main := by
  rintro ⟨P, Q, hQ, h⟩
  have hs : Q.coeff Q.natTrailingDegree ≠ 0 := by
    have h1 := Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hQ
    exact h1
  have hlow : ∀ i, i < Q.natTrailingDegree → Q.coeff i = 0 :=
    fun i hi => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi
  have hhigh : ∀ i, Q.natDegree < i → Q.coeff i = 0 :=
    fun i hi => Polynomial.coeff_eq_zero_of_natDegree_lt hi
  rw [mul_comm] at h
  have hrecA : ∀ n, P.natDegree < n →
      ∑ i ∈ Finset.range (n + 1), Q.coeff i * (a (n - i) : ℚ) = 0 := by
    intro n hn
    have h1 := congrArg (PowerSeries.coeff n) h
    rw [PowerSeries.coeff_mul, Polynomial.coeff_coe,
      Polynomial.coeff_eq_zero_of_natDegree_lt hn,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h1
    rw [← h1]
    apply Finset.sum_congr rfl
    intro i _
    rw [Polynomial.coeff_coe, PowerSeries.coeff_mk]
  have hrecA' : ∀ n j, P.natDegree < n → Q.natDegree ≤ n →
      ∑ i ∈ Finset.range (n + 1), Q.coeff i * (a (n + j - i) : ℚ) = 0 := by
    intro n j h1 h2
    rw [← hrecA (n + j) (by omega)]
    apply Finset.sum_subset
    · intro i hi
      simp only [Finset.mem_range] at *
      omega
    · intro i _ hi
      simp only [Finset.mem_range] at hi
      rw [hhigh i (by omega), zero_mul]
  have hrecB : ∀ n, max (P.natDegree + 1) Q.natDegree ≤ n →
      ∑ i ∈ Finset.range (n + 1), Q.coeff i *
        (fun k : ℕ => (a (k + 2) : ℚ) - 2 * (a (k + 1) : ℚ) + (a k : ℚ)) (n - i) = 0 := by
    intro n hn
    have e2 := hrecA' n 2 (by omega) (by omega)
    have e1 := hrecA' n 1 (by omega) (by omega)
    have e0 := hrecA' n 0 (by omega) (by omega)
    have key : ∑ i ∈ Finset.range (n + 1), Q.coeff i *
        (fun k : ℕ => (a (k + 2) : ℚ) - 2 * (a (k + 1) : ℚ) + (a k : ℚ)) (n - i)
        = ∑ i ∈ Finset.range (n + 1), Q.coeff i * (a (n + 2 - i) : ℚ)
          - 2 * ∑ i ∈ Finset.range (n + 1), Q.coeff i * (a (n + 1 - i) : ℚ)
          + ∑ i ∈ Finset.range (n + 1), Q.coeff i * (a (n + 0 - i) : ℚ) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < n + 1 := Finset.mem_range.mp hi
      rw [show n + 2 - i = n - i + 2 by omega, show n + 1 - i = n - i + 1 by omega,
        show n + 0 - i = n - i by omega]
      ring
    rw [key, e2, e1, e0]
    ring
  obtain ⟨k, hk, hw⟩ := window (max (P.natDegree + 1) Q.natDegree) (Q.natDegree + 2)
  have hwin : ∀ m, k ≤ m → m < k + Q.natDegree →
      (fun k : ℕ => (a (k + 2) : ℚ) - 2 * (a (k + 1) : ℚ) + (a k : ℚ)) m = 0 := by
    intro m hm hm'
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hm
    have w2 : a (k + i + 2) = a k + (i + 2) := hw (i + 2) (by omega)
    have w1 : a (k + i + 1) = a k + (i + 1) := hw (i + 1) (by omega)
    have w0 : a (k + i) = a k + i := hw i (by omega)
    show (a (k + i + 2) : ℚ) - 2 * (a (k + i + 1) : ℚ) + (a (k + i) : ℚ) = 0
    rw [w2, w1, w0]
    push_cast
    ring
  have hb := rec_zero (fun i => Q.coeff i)
    (fun k : ℕ => (a (k + 2) : ℚ) - 2 * (a (k + 1) : ℚ) + (a k : ℚ))
    Q.natTrailingDegree Q.natDegree (max (P.natDegree + 1) Q.natDegree) k
    hs hlow hhigh hrecB hk hwin
  have hlin : ∀ i : ℕ, (a (k + i) : ℚ) = (a k : ℚ) + i ∧
      (a (k + i + 1) : ℚ) = (a k : ℚ) + i + 1 := by
    intro i
    induction i with
    | zero =>
      have w1 : a (k + 0 + 1) = a k + 1 := hw 1 (by omega)
      refine ⟨by simp, ?_⟩
      rw [w1]
      push_cast
      ring
    | succ i ih =>
      obtain ⟨ih0, ih1⟩ := ih
      have h3 : (a (k + i + 2) : ℚ) - 2 * (a (k + i + 1) : ℚ) + (a (k + i) : ℚ) = 0 :=
        hb (k + i) (by omega)
      have e : k + (i + 1) = k + i + 1 := rfl
      refine ⟨?_, ?_⟩
      · rw [e, ih1]
        push_cast
        ring
      · rw [e]
        push_cast
        linarith
  have hnat : ∀ i : ℕ, a (k + i) = a k + i := by
    intro i
    have h1 := (hlin i).1
    exact_mod_cast h1
  have h5 := tz_pow (a k)
  have h6 := hnat (trailingZeros (5 ^ a k) - a k)
  have h7 := a_mem (k + (trailingZeros (5 ^ a k) - a k)) (5 ^ a k)
  omega

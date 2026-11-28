import OMAStatements.S_oeis_a274100
import Mathlib

/-!
# A274100: Barker's recurrence

P3(N) = Σ_{c ≤ N/3} (floor((N - c)/2) + 1 - c) counts the partitions of N into at most three parts
and satisfies P3(N + 6) = P3(N) + N + 6, hence 12 P3(N) = (N + 3)^2 + 3 for N ≡ 0 (mod 6) and
12 P3(N) + 1 = (N + 3)^2 for N ≡ 2, 4 (mod 6). Removing the smallest part d from each of the four
parts gives P4(N) = Σ_{d ≤ N/4} P3(N - 4d), so P4(N + 12) = P4(N) + P3(N + 4) + P3(N + 8) + P3(N + 12).
Induction on q gives 144 P4(N) = N^3 + 15 N^2 + 72 N + 128 for N = 12q + 4 and
144 P4(N) = N^3 + 15 N^2 + 72 N + 112 for N = 12q + 8. For n ≥ 2, 2^n ≡ 4 (mod 12) for even n and
≡ 8 for odd n, so 144 a(n) = 8^n + 15*4^n + 72*2^n + 120 + 8*(-1)^n, and Barker's recurrence
follows since 8, 4, 2, 1, -1 are the roots of its characteristic polynomial.
-/

namespace PA274100

theorem icc_range' (k X : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.Icc k X, f i = ∑ j ∈ Finset.range (X + 1 - k), f (k + j) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]

/-- Partitions of `N` into at most three parts. -/
def P3 (N : ℕ) : ℕ := ∑ c ∈ Finset.range (N / 3 + 1), ((N - c) / 2 + 1 - c)

/-- Partitions of `N` into at most four parts, sorted by their smallest part `d`. -/
def P4 (N : ℕ) : ℕ := ∑ d ∈ Finset.range (N / 4 + 1), P3 (N - 4 * d)

theorem count_eq (N : ℕ) :
    ∑ d ∈ Finset.range (N / 4 + 1), ∑ c ∈ Finset.Icc d ((N - d) / 3),
      ∑ _b ∈ Finset.Icc c ((N - c - d) / 2), 1 = P4 N := by
  unfold P4
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_range] at hd
  unfold P3
  rw [icc_range', show (N - d) / 3 + 1 - d = (N - 4 * d) / 3 + 1 by omega]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [Finset.mem_range] at hs
  rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul, mul_one]
  omega

theorem P3_six (N : ℕ) : P3 (N + 6) = P3 N + N + 6 := by
  unfold P3
  rw [show (N + 6) / 3 + 1 = N / 3 + 1 + 1 + 1 by omega, Finset.sum_range_succ,
    Finset.sum_range_succ]
  have h : ∑ c ∈ Finset.range (N / 3 + 1), ((N + 6 - c) / 2 + 1 - c) =
      ∑ c ∈ Finset.range (N / 3 + 1), (((N - c) / 2 + 1 - c) + 3) :=
    Finset.sum_congr rfl fun c hc => by
      rw [Finset.mem_range] at hc
      omega
  rw [h, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  omega

theorem P3_even (q : ℕ) : 12 * P3 (6 * q) = (6 * q + 3) ^ 2 + 3 ∧
    12 * P3 (6 * q + 2) + 1 = (6 * q + 5) ^ 2 ∧ 12 * P3 (6 * q + 4) + 1 = (6 * q + 7) ^ 2 := by
  induction q with
  | zero => exact ⟨by decide, by decide, by decide⟩
  | succ q ih =>
    rw [show 6 * (q + 1) = 6 * q + 6 by ring, show 6 * q + 6 + 2 = 6 * q + 2 + 6 by ring,
      show 6 * q + 6 + 4 = 6 * q + 4 + 6 by ring, P3_six, P3_six, P3_six]
    exact ⟨by nlinarith [ih.1], by nlinarith [ih.2.1], by nlinarith [ih.2.2]⟩

theorem P4_twelve (N : ℕ) : P4 (N + 12) = P4 N + P3 (N + 4) + P3 (N + 8) + P3 (N + 12) := by
  unfold P4
  conv_lhs => rw [show (N + 12) / 4 + 1 = N / 4 + 1 + 1 + 1 + 1 by omega, Finset.sum_range_succ',
    Finset.sum_range_succ', Finset.sum_range_succ']
  have h : ∑ d ∈ Finset.range (N / 4 + 1), P3 (N + 12 - 4 * (d + 1 + 1 + 1)) =
      ∑ d ∈ Finset.range (N / 4 + 1), P3 (N - 4 * d) :=
    Finset.sum_congr rfl fun d _ => by rw [show N + 12 - 4 * (d + 1 + 1 + 1) = N - 4 * d by omega]
  rw [h, show N + 12 - 4 * (0 + 1 + 1) = N + 4 by omega, show N + 12 - 4 * (0 + 1) = N + 8 by omega,
    show N + 12 - 4 * 0 = N + 12 by omega]

theorem P4_closed48 (q : ℕ) :
    144 * P4 (12 * q + 4) = (12 * q + 4) ^ 3 + 15 * (12 * q + 4) ^ 2 + 72 * (12 * q + 4) + 128 ∧
    144 * P4 (12 * q + 8) = (12 * q + 8) ^ 3 + 15 * (12 * q + 8) ^ 2 + 72 * (12 * q + 8) + 112 := by
  induction q with
  | zero => exact ⟨by decide, by decide⟩
  | succ q ih =>
    have a1 := (P3_even (2 * q + 1)).2.1
    have a2 := (P3_even (2 * q + 2)).1
    have a3 := (P3_even (2 * q + 2)).2.2
    have b1 := (P3_even (2 * q + 2)).1
    have b2 := (P3_even (2 * q + 2)).2.2
    have b3 := (P3_even (2 * q + 3)).2.1
    rw [show 6 * (2 * q + 1) + 2 = 12 * q + 4 + 4 by ring] at a1
    rw [show 6 * (2 * q + 2) = 12 * q + 4 + 8 by ring] at a2
    rw [show 6 * (2 * q + 2) + 4 = 12 * q + 4 + 12 by ring] at a3
    rw [show 6 * (2 * q + 2) = 12 * q + 8 + 4 by ring] at b1
    rw [show 6 * (2 * q + 2) + 4 = 12 * q + 8 + 8 by ring] at b2
    rw [show 6 * (2 * q + 3) + 2 = 12 * q + 8 + 12 by ring] at b3
    rw [show 12 * (q + 1) + 4 = 12 * q + 4 + 12 by ring, show 12 * (q + 1) + 8 = 12 * q + 8 + 12 by ring,
      P4_twelve, P4_twelve]
    constructor
    · nlinarith [ih.1, a1, a2, a3]
    · nlinarith [ih.2, b1, b2, b3]

theorem pow_mod (n : ℕ) (hn : 2 ≤ n) :
    (2 ^ n % 12 = 4 ∧ (-1 : ℤ) ^ n = 1) ∨ (2 ^ n % 12 = 8 ∧ (-1 : ℤ) ^ n = -1) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      left
      norm_num
    · rw [pow_succ, pow_succ]
      rcases ih h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right
        exact ⟨by omega, by rw [h2]; norm_num⟩
      · left
        exact ⟨by omega, by rw [h2]; norm_num⟩

theorem closed (n : ℕ) (hn : 2 ≤ n) :
    144 * (P4 (2 ^ n) : ℤ) = ((2 : ℤ) ^ n) ^ 3 + 15 * ((2 : ℤ) ^ n) ^ 2 + 72 * (2 : ℤ) ^ n + 120 +
      8 * (-1) ^ n := by
  rcases pow_mod n hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hq := (P4_closed48 (2 ^ n / 12)).1
    rw [show 12 * (2 ^ n / 12) + 4 = 2 ^ n by omega] at hq
    have hz : (144 : ℤ) * (P4 (2 ^ n) : ℤ) =
        ((2 ^ n : ℕ) : ℤ) ^ 3 + 15 * ((2 ^ n : ℕ) : ℤ) ^ 2 + 72 * ((2 ^ n : ℕ) : ℤ) + 128 := by
      exact_mod_cast hq
    push_cast at hz
    rw [h2]
    linear_combination hz
  · have hq := (P4_closed48 (2 ^ n / 12)).2
    rw [show 12 * (2 ^ n / 12) + 8 = 2 ^ n by omega] at hq
    have hz : (144 : ℤ) * (P4 (2 ^ n) : ℤ) =
        ((2 ^ n : ℕ) : ℤ) ^ 3 + 15 * ((2 ^ n : ℕ) : ℤ) ^ 2 + 72 * ((2 ^ n : ℕ) : ℤ) + 112 := by
      exact_mod_cast hq
    push_cast at hz
    rw [h2]
    linear_combination hz

end PA274100

theorem OMA.solution : type_of% @OMA.S_oeis_a274100.main := by
  have aeq : ∀ n, OMA.S_oeis_a274100.a n = PA274100.P4 (2 ^ n) :=
    fun n => PA274100.count_eq (2 ^ n)
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  simp only [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
    show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega, show m + 7 - 5 = m + 2 by omega,
    aeq]
  have h7 := PA274100.closed (m + 7) (by omega)
  have h6 := PA274100.closed (m + 6) (by omega)
  have h5 := PA274100.closed (m + 5) (by omega)
  have h4 := PA274100.closed (m + 4) (by omega)
  have h3 := PA274100.closed (m + 3) (by omega)
  have h2 := PA274100.closed (m + 2) (by omega)
  have key : (144 : ℤ) * ((PA274100.P4 (2 ^ (m + 7)) : ℤ) - 14 * PA274100.P4 (2 ^ (m + 6)) +
      55 * PA274100.P4 (2 ^ (m + 5)) - 50 * PA274100.P4 (2 ^ (m + 4)) -
      56 * PA274100.P4 (2 ^ (m + 3)) + 64 * PA274100.P4 (2 ^ (m + 2))) = 0 := by
    linear_combination h7 - 14 * h6 + 55 * h5 - 50 * h4 - 56 * h3 + 64 * h2
  linarith

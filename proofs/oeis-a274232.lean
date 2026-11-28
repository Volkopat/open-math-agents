import OMAStatements.S_oeis_a274232
import Mathlib

namespace OMA.S_oeis_a274232

lemma a_eq (n : ℕ) : a n = ∑ c ∈ Finset.range (2 ^ n / 3 + 1), ((2 ^ n - c) / 2 + 1 - c) := by
  unfold a
  apply Finset.sum_congr rfl
  intro c _
  simp

def f (N : ℕ) : ℕ := ∑ c ∈ Finset.range (N / 3 + 1), ((N - c) / 2 + 1 - c)

lemma f_step (N : ℕ) : f (N + 6) = f N + 3 * (N / 3 + 1)
    + ((N + 6 - (N / 3 + 1)) / 2 + 1 - (N / 3 + 1))
    + ((N + 6 - (N / 3 + 2)) / 2 + 1 - (N / 3 + 2)) := by
  unfold f
  have h : (N + 6) / 3 + 1 = (N / 3 + 1) + 2 := by omega
  rw [h, Finset.sum_range_succ, Finset.sum_range_succ]
  have h2 : ∑ c ∈ Finset.range (N / 3 + 1), ((N + 6 - c) / 2 + 1 - c)
      = ∑ c ∈ Finset.range (N / 3 + 1), (((N - c) / 2 + 1 - c) + 3) := by
    apply Finset.sum_congr rfl
    intro c hc
    have := Finset.mem_range.mp hc
    omega
  rw [h2, Finset.sum_add_distrib]
  simp
  ring

lemma f_closed : ∀ m : ℕ, (12 * f (6 * m + 2) = (6 * m + 2) ^ 2 + 6 * (6 * m + 2) + 8) ∧
    (12 * f (6 * m + 4) = (6 * m + 4) ^ 2 + 6 * (6 * m + 4) + 8) := by
  intro m
  induction m with
  | zero => constructor <;> decide
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    constructor
    · have e : 6 * (k + 1) + 2 = (6 * k + 2) + 6 := by ring
      rw [e, f_step]
      have a1 : (6 * k + 2) / 3 = 2 * k := by omega
      rw [a1]
      have b1 : (6 * k + 2 + 6 - (2 * k + 1)) / 2 + 1 - (2 * k + 1) = 3 := by omega
      have b2 : (6 * k + 2 + 6 - (2 * k + 2)) / 2 + 1 - (2 * k + 2) = 2 := by omega
      rw [b1, b2]
      nlinarith [h1]
    · have e : 6 * (k + 1) + 4 = (6 * k + 4) + 6 := by ring
      rw [e, f_step]
      have a1 : (6 * k + 4) / 3 = 2 * k + 1 := by omega
      rw [a1]
      have b1 : (6 * k + 4 + 6 - (2 * k + 1 + 1)) / 2 + 1 - (2 * k + 1 + 1) = 3 := by omega
      have b2 : (6 * k + 4 + 6 - (2 * k + 1 + 2)) / 2 + 1 - (2 * k + 1 + 2) = 1 := by omega
      rw [b1, b2]
      nlinarith [h2]

lemma pow_mod6 (n : ℕ) (hn : 0 < n) : 2 ^ n % 6 = 2 ∨ 2 ^ n % 6 = 4 := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · left; decide
    · rcases ih hk with h | h <;> [right; left] <;> omega

lemma closed (n : ℕ) (hn : 0 < n) : 12 * a n = 8 + 3 * 2 ^ (n + 1) + 4 ^ n := by
  rw [a_eq]
  have key : ∀ N, (N % 6 = 2 ∨ N % 6 = 4) → 12 * f N = N ^ 2 + 6 * N + 8 := by
    intro N hN
    obtain ⟨m, hm⟩ : ∃ m, N = 6 * m + 2 ∨ N = 6 * m + 4 := ⟨N / 6, by omega⟩
    rcases hm with rfl | rfl
    · exact (f_closed m).1
    · exact (f_closed m).2
  have := key (2 ^ n) (pow_mod6 n hn)
  unfold f at this
  have e : (4 : ℕ) ^ n = (2 ^ n) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [this, e, pow_succ]
  ring

end OMA.S_oeis_a274232

open OMA.S_oeis_a274232 in
theorem OMA.solution : type_of% @OMA.S_oeis_a274232.main := by
  refine ⟨fun n hn => closed n hn, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hm : 0 < m := by omega
  have h0 := closed m hm
  have h1 := closed (m + 1) (by omega)
  have h2 := closed (m + 2) (by omega)
  have h3 := closed (m + 3) (by omega)
  simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  have e : (4 : ℕ) ^ m = (2 ^ m) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have e1 : (4 : ℕ) ^ (m + 1) = 4 * (2 ^ m) ^ 2 := by rw [pow_succ, e]; ring
  have e2 : (4 : ℕ) ^ (m + 2) = 16 * (2 ^ m) ^ 2 := by rw [pow_add, e]; ring
  have e3 : (4 : ℕ) ^ (m + 3) = 64 * (2 ^ m) ^ 2 := by rw [pow_add, e]; ring
  rw [e] at h0
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  simp only [pow_succ, pow_zero] at h0 h1 h2 h3
  zify at h0 h1 h2 h3 ⊢
  nlinarith [h0, h1, h2, h3]

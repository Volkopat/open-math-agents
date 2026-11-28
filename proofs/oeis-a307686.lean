import OMAStatements.S_oeis_a307686
import Mathlib

namespace OMA.Helpers_a307686

open OMA.S_oeis_a307686 Finset

/-- number of admissible middle sides -/
def f (n k : ℕ) : ℕ := (n - k) / 2 + 1 - max k (n / 2 + 1 - k)

lemma a_eq_range (n : ℕ) : a n = ∑ k ∈ range (n / 3 + 1), k * f n k := by
  unfold a
  have hsub : ∑ k ∈ Icc 1 (n / 3), k * f n k = ∑ k ∈ range (n / 3 + 1), k * f n k :=
    Finset.sum_subset (fun k hk => by simp at hk ⊢; omega)
      (fun k hk hk' => by simp at hk hk'; rw [show k = 0 by omega]; simp)
  rw [← hsub]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : ((Icc k ((n - k) / 2)).filter (fun i => n - i - k < i + k)) =
      Icc (max k (n / 2 + 1 - k)) ((n - k) / 2) := by
    ext i; simp only [mem_filter, mem_Icc]; omega
  rw [this, sum_const, Nat.card_Icc, smul_eq_mul, mul_comm]
  rfl

noncomputable def P1 (K : ℕ) : ℚ := (K : ℚ) * (K + 1) / 2
noncomputable def P2 (K : ℕ) : ℚ := (K : ℚ) * (K + 1) * (2 * K + 1) / 6
noncomputable def F0 (K : ℕ) : ℚ := (P2 K - (((K + 1) / 2 : ℕ) : ℚ) ^ 2) / 2
noncomputable def F1 (K : ℕ) : ℚ := (P2 K + (((K + 1) / 2 : ℕ) : ℚ) ^ 2) / 2

lemma sumP1 (K : ℕ) : ∑ k ∈ range (K + 1), (k : ℚ) = P1 K := by
  induction K with
  | zero => simp [P1]
  | succ K ih => rw [sum_range_succ, ih, P1, P1]; push_cast; ring

lemma sumP2 (K : ℕ) : ∑ k ∈ range (K + 1), (k : ℚ) ^ 2 = P2 K := by
  induction K with
  | zero => simp [P2]
  | succ K ih => rw [sum_range_succ, ih, P2, P2]; push_cast; ring

lemma sumF0 (K : ℕ) : ∑ k ∈ range (K + 1), ((k * (k / 2) : ℕ) : ℚ) = F0 K := by
  induction K with
  | zero => simp [F0, P2]
  | succ K ih =>
    rw [sum_range_succ, ih, F0, F0, P2, P2]
    rcases Nat.even_or_odd' K with ⟨u, rfl | rfl⟩
    · simp only [show (2 * u + 1) / 2 = u by omega, show (2 * u + 1 + 1) / 2 = u + 1 by omega,
        show (2 * u + 1 + 1 + 1) / 2 = u + 1 by omega, show (2 * u) / 2 = u by omega]; push_cast; ring
    · simp only [show (2 * u + 1 + 1) / 2 = u + 1 by omega, show (2 * u + 1 + 1 + 1) / 2 = u + 1 by omega,
        show (2 * u + 1 + 1 + 1 + 1) / 2 = u + 2 by omega, show (2 * u + 1) / 2 = u by omega]; push_cast; ring

lemma sumF1 (K : ℕ) : ∑ k ∈ range (K + 1), ((k * ((k + 1) / 2) : ℕ) : ℚ) = F1 K := by
  induction K with
  | zero => simp [F1, P2]
  | succ K ih =>
    rw [sum_range_succ, ih, F1, F1, P2, P2]
    rcases Nat.even_or_odd' K with ⟨u, rfl | rfl⟩
    · simp only [show (2 * u + 1) / 2 = u by omega, show (2 * u + 1 + 1) / 2 = u + 1 by omega,
        show (2 * u) / 2 = u by omega]
      push_cast; ring
    · simp only [show (2 * u + 1 + 1) / 2 = u + 1 by omega, show (2 * u + 1 + 1 + 1) / 2 = u + 1 by omega,
        show (2 * u + 1 + 1 + 1 + 1) / 2 = u + 2 by omega, show (2 * u + 1) / 2 = u by omega]; push_cast; ring

lemma a_closed (n : ℕ) : (a n : ℚ) =
    if n % 2 = 0 then
      F0 (n / 4) + ((n / 2 : ℕ) + 1 : ℚ) * (P1 (n / 3) - P1 (n / 4)) - (P2 (n / 3) - P2 (n / 4)) -
        (F1 (n / 3) - F1 (n / 4))
    else
      F1 (n / 4) + ((n / 2 : ℕ) + 1 : ℚ) * (P1 (n / 3) - P1 (n / 4)) - (P2 (n / 3) - P2 (n / 4)) -
        (F0 (n / 3) - F0 (n / 4)) := by
  rw [a_eq_range, ← sum_range_add_sum_Ico _ (show n / 4 + 1 ≤ n / 3 + 1 by omega)]
  rcases Nat.mod_two_eq_zero_or_one n with he | he
  · rw [if_pos he]
    have h1 : ∑ k ∈ range (n / 4 + 1), k * f n k = ∑ k ∈ range (n / 4 + 1), k * (k / 2) :=
      sum_congr rfl fun k hk => by simp only [mem_range] at hk; congr 1; unfold f; omega
    have h2 : ∀ k ∈ Ico (n / 4 + 1) (n / 3 + 1), ((k * f n k : ℕ) : ℚ) =
        (k : ℚ) * ((n / 2 : ℕ) + 1) - (k : ℚ) ^ 2 - ((k * ((k + 1) / 2) : ℕ) : ℚ) := by
      intro k hk
      simp only [mem_Ico] at hk
      have : f n k + k + (k + 1) / 2 = n / 2 + 1 := by unfold f; omega
      have h3 : (f n k : ℚ) = (n / 2 : ℕ) + 1 - k - ((k + 1) / 2 : ℕ) := by
        have h4 := congrArg (fun x : ℕ => (x : ℚ)) this
        push_cast at h4; linarith
      push_cast; rw [h3]; ring
    rw [Nat.cast_add, Nat.cast_sum, Nat.cast_sum, sum_congr rfl h2,
      show ∑ k ∈ range (n / 4 + 1), ((k * f n k : ℕ) : ℚ) = ∑ k ∈ range (n / 4 + 1), ((k * (k / 2) : ℕ) : ℚ)
        by rw [← Nat.cast_sum, h1, Nat.cast_sum],
      sumF0, sum_sub_distrib, sum_sub_distrib, ← sum_mul,
      sum_Ico_eq_sub _ (by omega), sum_Ico_eq_sub _ (by omega), sum_Ico_eq_sub _ (by omega),
      sumP1, sumP1, sumP2, sumP2, sumF1, sumF1]
    ring
  · rw [if_neg (by omega)]
    have h1 : ∑ k ∈ range (n / 4 + 1), k * f n k = ∑ k ∈ range (n / 4 + 1), k * ((k + 1) / 2) :=
      sum_congr rfl fun k hk => by simp only [mem_range] at hk; congr 1; unfold f; omega
    have h2 : ∀ k ∈ Ico (n / 4 + 1) (n / 3 + 1), ((k * f n k : ℕ) : ℚ) =
        (k : ℚ) * ((n / 2 : ℕ) + 1) - (k : ℚ) ^ 2 - ((k * (k / 2) : ℕ) : ℚ) := by
      intro k hk
      simp only [mem_Ico] at hk
      have : f n k + k + k / 2 = n / 2 + 1 := by unfold f; omega
      have h3 : (f n k : ℚ) = (n / 2 : ℕ) + 1 - k - (k / 2 : ℕ) := by
        have h4 := congrArg (fun x : ℕ => (x : ℚ)) this
        push_cast at h4; linarith
      push_cast; rw [h3]; ring
    rw [Nat.cast_add, Nat.cast_sum, Nat.cast_sum, sum_congr rfl h2,
      show ∑ k ∈ range (n / 4 + 1), ((k * f n k : ℕ) : ℚ) = ∑ k ∈ range (n / 4 + 1), ((k * ((k + 1) / 2) : ℕ) : ℚ)
        by rw [← Nat.cast_sum, h1, Nat.cast_sum],
      sumF1, sum_sub_distrib, sum_sub_distrib, ← sum_mul,
      sum_Ico_eq_sub _ (by omega), sum_Ico_eq_sub _ (by omega), sum_Ico_eq_sub _ (by omega),
      sumP1, sumP1, sumP2, sumP2, sumF0, sumF0]
    ring

def C2 : ℕ → ℚ
  | 0 => (1/96 : ℚ)
  | 1 => (5/192 : ℚ)
  | 2 => (1/96 : ℚ)
  | 3 => (5/192 : ℚ)
  | 4 => (1/96 : ℚ)
  | 5 => (5/192 : ℚ)
  | 6 => (1/96 : ℚ)
  | 7 => (5/192 : ℚ)
  | 8 => (1/96 : ℚ)
  | 9 => (5/192 : ℚ)
  | 10 => (1/96 : ℚ)
  | 11 => (5/192 : ℚ)
  | _ => 0

def C1 : ℕ → ℚ
  | 0 => (1/24 : ℚ)
  | 1 => (-13/576 : ℚ)
  | 2 => (-1/144 : ℚ)
  | 3 => (29/192 : ℚ)
  | 4 => (-5/72 : ℚ)
  | 5 => (-13/576 : ℚ)
  | 6 => (5/48 : ℚ)
  | 7 => (23/576 : ℚ)
  | 8 => (-5/72 : ℚ)
  | 9 => (17/192 : ℚ)
  | 10 => (-1/144 : ℚ)
  | 11 => (23/576 : ℚ)
  | _ => 0

def C0 : ℕ → ℚ
  | 0 => (0 : ℚ)
  | 1 => (-13/1728 : ℚ)
  | 2 => (-13/216 : ℚ)
  | 3 => (13/64 : ℚ)
  | 4 => (-4/27 : ℚ)
  | 5 => (-77/1728 : ℚ)
  | 6 => (1/8 : ℚ)
  | 7 => (95/1728 : ℚ)
  | 8 => (-5/27 : ℚ)
  | 9 => (9/64 : ℚ)
  | 10 => (-5/216 : ℚ)
  | 11 => (31/1728 : ℚ)
  | _ => 0

noncomputable def Pq (n : ℕ) : ℚ := 7 / 1728 * (n : ℚ) ^ 3 + C2 (n % 12) * (n : ℚ) ^ 2 + C1 (n % 12) * n + C0 (n % 12)

lemma res0 (m : ℕ) : (a (24 * m) : ℚ) = Pq (24 * m) := by
  rw [a_closed, if_pos (by omega)]
  rw [show (24 * m) / 4 = 6 * m + 0 by omega, show (24 * m) / 3 = 8 * m + 0 by omega,
    show (24 * m) / 2 = 12 * m + 0 by omega]
  simp only [F0, F1, P1, P2, Pq]
  rw [show (6 * m + 0 + 1) / 2 = 3 * m + 0 by omega, show (8 * m + 0 + 1) / 2 = 4 * m + 0 by omega,
    show (24 * m) % 12 = 0 by omega]
  simp only [C2, C1, C0]
  push_cast; ring

lemma res1 (m : ℕ) : (a (24 * m + 1) : ℚ) = Pq (24 * m + 1) := by
  rw [a_closed, if_neg (by omega)]
  rw [show (24 * m + 1) / 4 = 6 * m + 0 by omega, show (24 * m + 1) / 3 = 8 * m + 0 by omega,
    show (24 * m + 1) / 2 = 12 * m + 0 by omega]
  simp only [F0, F1, P1, P2, Pq]
  rw [show (6 * m + 0 + 1) / 2 = 3 * m + 0 by omega, show (8 * m + 0 + 1) / 2 = 4 * m + 0 by omega,
    show (24 * m + 1) % 12 = 1 by omega]
  simp only [C2, C1, C0]
  push_cast; ring

lemma res2 (m : ℕ) : (a (24 * m + 2) : ℚ) = Pq (24 * m + 2) := by
  rw [a_closed, if_pos (by omega)]
  rw [show (24 * m + 2) / 4 = 6 * m + 0 by omega, show (24 * m + 2) / 3 = 8 * m + 0 by omega,
    show (24 * m + 2) / 2 = 12 * m + 1 by omega]
  simp only [F0, F1, P1, P2, Pq]
  rw [show (6 * m + 0 + 1) / 2 = 3 * m + 0 by omega, show (8 * m + 0 + 1) / 2 = 4 * m + 0 by omega,
    show (24 * m + 2) % 12 = 2 by omega]
  simp only [C2, C1, C0]
  push_cast; ring

lemma res3 (m : ℕ) : (a (24 * m + 3) : ℚ) = Pq (24 * m + 3) := by
  rw [a_closed, if_neg (by omega)]
  rw [show (24 * m + 3) / 4 = 6 * m + 0 by omega, show (24 * m + 3) / 3 = 8 * m + 1 by omega,
    show (24 * m + 3) / 2 = 12 * m + 1 by omega]
  simp only [F0, F1, P1, P2, Pq]
  rw [show (6 * m + 0 + 1) / 2 = 3 * m + 0 by omega, show (8 * m + 1 + 1) / 2 = 4 * m + 1 by omega,
    show (24 * m + 3) % 12 = 3 by omega]
  simp only [C2, C1, C0]
  push_cast; ring

lemma res4 (m : ℕ) : (a (24 * m + 4) : ℚ) = Pq (24 * m + 4) := by
  rw [a_closed, if_pos (by omega)]
  rw [show (24 * m + 4) / 4 = 6 * m + 1 by omega, show (24 * m + 4) / 3 = 8 * m + 1 by omega,
    show (24 * m + 4) / 2 = 12 * m + 2 by omega]
  simp only [F0, F1, P1, P2, Pq]
  rw [show (6 * m + 1 + 1) / 2 = 3 * m + 1 by omega, show (8 * m + 1 + 1) / 2 = 4 * m + 1 by omega,
    show (24 * m + 4) % 12 = 4 by omega]
  simp only [C2, C1, C0]
  push_cast; ring

lemma res5 (m : ℕ) : (a (24 * m + 5) : ℚ) = Pq (24 * m + 5) := by
  rw [a_closed, if_neg (by omega)]
  rw [show (24 * m + 5) / 4 = 6 * m + 1 by omega, show (24 * m + 5) / 3 = 8 * m + 1 by omega,
    show (24 * m + 5) / 2 = 12 * m + 2 by omega]
  simp only [F0, F1, P1, P2, Pq]
  rw [show (6 * m + 1 + 1) / 2 = 3 * m + 1 by omega, show (8 * m + 1 + 1) / 2 = 4 * m + 1 by omega,
    show (24 * m + 5) % 12 = 5 by omega]
  simp only [C2, C1, C0]
  push_cast; ring

lemma res6 (m : ℕ) : (a (24 * m + 6) : ℚ) = Pq (24 * m + 6) := by
  rw [a_closed, if_pos (by omega)]
  rw [show (24 * m + 6) / 4 = 6 * m + 1 by omega, show (24 * m + 6) / 3 = 8 * m + 2 by omega,
    show (24 * m + 6) / 2 = 12 * m + 3 by omega]
  simp only [F0, F1, P1, P2, Pq]
  rw [show (6 * m + 1 + 1) / 2 = 3 * m + 1 by omega, show (8 * m + 2 + 1) / 2 = 4 * m + 1 by omega,
    show (24 * m + 6) % 12 = 6 by omega]
  simp only [C2, C1, C0]
  push_cast; ring

lemma res7 (m : ℕ) : (a (24 * m + 7) : ℚ) = Pq (24 * m + 7) := by
  rw [a_closed, if_neg (by omega)]
  rw [show (24 * m + 7) / 4 = 6 * m + 1 by omega, show (24 * m + 7) / 3 = 8 * m + 2 by omega,
    show (24 * m + 7) / 2 = 12 * m + 3 by omega]
  simp only [F0, F1, P1, P2, Pq]
  rw [show (6 * m + 1 + 1) / 2 = 3 * m + 1 by omega, show (8 * m + 2 + 1) / 2 = 4 * m + 1 by omega,
    show (24 * m + 7) % 12 = 7 by omega]
  simp only [C2, C1, C0]
  push_cast; ring

lemma res8 (m : ℕ) : (a (24 * m + 8) : ℚ) = Pq (24 * m + 8) := by
  rw [a_closed, if_pos (by omega)]
  rw [show (24 * m + 8) / 4 = 6 * m + 2 by omega, show (24 * m + 8) / 3 = 8 * m + 2 by omega,
    show (24 * m + 8) / 2 = 12 * m + 4 by omega]
  simp only [F0, F1, P1, P2, Pq]
  rw [show (6 * m + 2 + 1) / 2 = 3 * m + 1 by omega, show (8 * m + 2 + 1) / 2 = 4 * m + 1 by omega,
    show (24 * m + 8) % 12 = 8 by omega]
  simp only [C2, C1, C0]
  push_cast; ring

lemma res9 (m : ℕ) : (a (24 * m + 9) : ℚ) = Pq (24 * m + 9) := by
  rw [a_closed, if_neg (by omega)]
  rw [show (24 * m + 9) / 4 = 6 * m + 2 by omega, show (24 * m + 9) / 3 = 8 * m + 3 by omega,
    show (24 * m + 9) / 2 = 12 * m + 4 by omega]
  simp only [F0, F1, P1, P2, Pq]
  rw [show (6 * m + 2 + 1) / 2 = 3 * m + 1 by omega, show (8 * m + 3 + 1) / 2 = 4 * m + 2 by omega,
    show (24 * m + 9) % 12 = 9 by omega]
  simp only [C2, C1, C0]
  push_cast; ring

lemma res10 (m : ℕ) : (a (24 * m + 10) : ℚ) = Pq (24 * m + 10) := by
  rw [a_closed, if_pos (by omega)]
  rw [show (24 * m + 10) / 4 = 6 * m + 2 by omega, show (24 * m + 10) / 3 = 8 * m + 3 by omega,
    show (24 * m + 10) / 2 = 12 * m + 5 by omega]
  simp only [F0, F1, P1, P2, Pq]
  rw [show (6 * m + 2 + 1) / 2 = 3 * m + 1 by omega, show (8 * m + 3 + 1) / 2 = 4 * m + 2 by omega,
    show (24 * m + 10) % 12 = 10 by omega]
  simp only [C2, C1, C0]
  push_cast; ring

lemma res11 (m : ℕ) : (a (24 * m + 11) : ℚ) = Pq (24 * m + 11) := by
  rw [a_closed, if_neg (by omega)]
  rw [show (24 * m + 11) / 4 = 6 * m + 2 by omega, show (24 * m + 11) / 3 = 8 * m + 3 by omega,
    show (24 * m + 11) / 2 = 12 * m + 5 by omega]
  simp only [F0, F1, P1, P2, Pq]
  rw [show (6 * m + 2 + 1) / 2 = 3 * m + 1 by omega, show (8 * m + 3 + 1) / 2 = 4 * m + 2 by omega,
    show (24 * m + 11) % 12 = 11 by omega]
  simp only [C2, C1, C0]
  push_cast; ring

lemma res12 (m : ℕ) : (a (24 * m + 12) : ℚ) = Pq (24 * m + 12) := by
  rw [a_closed, if_pos (by omega)]
  rw [show (24 * m + 12) / 4 = 6 * m + 3 by omega, show (24 * m + 12) / 3 = 8 * m + 4 by omega,
    show (24 * m + 12) / 2 = 12 * m + 6 by omega]
  simp only [F0, F1, P1, P2, Pq]
  rw [show (6 * m + 3 + 1) / 2 = 3 * m + 2 by omega, show (8 * m + 4 + 1) / 2 = 4 * m + 2 by omega,
    show (24 * m + 12) % 12 = 0 by omega]
  simp only [C2, C1, C0]
  push_cast; ring

lemma res13 (m : ℕ) : (a (24 * m + 13) : ℚ) = Pq (24 * m + 13) := by
  rw [a_closed, if_neg (by omega)]
  rw [show (24 * m + 13) / 4 = 6 * m + 3 by omega, show (24 * m + 13) / 3 = 8 * m + 4 by omega,
    show (24 * m + 13) / 2 = 12 * m + 6 by omega]
  simp only [F0, F1, P1, P2, Pq]
  rw [show (6 * m + 3 + 1) / 2 = 3 * m + 2 by omega, show (8 * m + 4 + 1) / 2 = 4 * m + 2 by omega,
    show (24 * m + 13) % 12 = 1 by omega]
  simp only [C2, C1, C0]
  push_cast; ring

lemma res14 (m : ℕ) : (a (24 * m + 14) : ℚ) = Pq (24 * m + 14) := by
  rw [a_closed, if_pos (by omega)]
  rw [show (24 * m + 14) / 4 = 6 * m + 3 by omega, show (24 * m + 14) / 3 = 8 * m + 4 by omega,
    show (24 * m + 14) / 2 = 12 * m + 7 by omega]
  simp only [F0, F1, P1, P2, Pq]
  rw [show (6 * m + 3 + 1) / 2 = 3 * m + 2 by omega, show (8 * m + 4 + 1) / 2 = 4 * m + 2 by omega,
    show (24 * m + 14) % 12 = 2 by omega]
  simp only [C2, C1, C0]
  push_cast; ring

lemma res15 (m : ℕ) : (a (24 * m + 15) : ℚ) = Pq (24 * m + 15) := by
  rw [a_closed, if_neg (by omega)]
  rw [show (24 * m + 15) / 4 = 6 * m + 3 by omega, show (24 * m + 15) / 3 = 8 * m + 5 by omega,
    show (24 * m + 15) / 2 = 12 * m + 7 by omega]
  simp only [F0, F1, P1, P2, Pq]
  rw [show (6 * m + 3 + 1) / 2 = 3 * m + 2 by omega, show (8 * m + 5 + 1) / 2 = 4 * m + 3 by omega,
    show (24 * m + 15) % 12 = 3 by omega]
  simp only [C2, C1, C0]
  push_cast; ring

lemma res16 (m : ℕ) : (a (24 * m + 16) : ℚ) = Pq (24 * m + 16) := by
  rw [a_closed, if_pos (by omega)]
  rw [show (24 * m + 16) / 4 = 6 * m + 4 by omega, show (24 * m + 16) / 3 = 8 * m + 5 by omega,
    show (24 * m + 16) / 2 = 12 * m + 8 by omega]
  simp only [F0, F1, P1, P2, Pq]
  rw [show (6 * m + 4 + 1) / 2 = 3 * m + 2 by omega, show (8 * m + 5 + 1) / 2 = 4 * m + 3 by omega,
    show (24 * m + 16) % 12 = 4 by omega]
  simp only [C2, C1, C0]
  push_cast; ring

lemma res17 (m : ℕ) : (a (24 * m + 17) : ℚ) = Pq (24 * m + 17) := by
  rw [a_closed, if_neg (by omega)]
  rw [show (24 * m + 17) / 4 = 6 * m + 4 by omega, show (24 * m + 17) / 3 = 8 * m + 5 by omega,
    show (24 * m + 17) / 2 = 12 * m + 8 by omega]
  simp only [F0, F1, P1, P2, Pq]
  rw [show (6 * m + 4 + 1) / 2 = 3 * m + 2 by omega, show (8 * m + 5 + 1) / 2 = 4 * m + 3 by omega,
    show (24 * m + 17) % 12 = 5 by omega]
  simp only [C2, C1, C0]
  push_cast; ring

lemma res18 (m : ℕ) : (a (24 * m + 18) : ℚ) = Pq (24 * m + 18) := by
  rw [a_closed, if_pos (by omega)]
  rw [show (24 * m + 18) / 4 = 6 * m + 4 by omega, show (24 * m + 18) / 3 = 8 * m + 6 by omega,
    show (24 * m + 18) / 2 = 12 * m + 9 by omega]
  simp only [F0, F1, P1, P2, Pq]
  rw [show (6 * m + 4 + 1) / 2 = 3 * m + 2 by omega, show (8 * m + 6 + 1) / 2 = 4 * m + 3 by omega,
    show (24 * m + 18) % 12 = 6 by omega]
  simp only [C2, C1, C0]
  push_cast; ring

lemma res19 (m : ℕ) : (a (24 * m + 19) : ℚ) = Pq (24 * m + 19) := by
  rw [a_closed, if_neg (by omega)]
  rw [show (24 * m + 19) / 4 = 6 * m + 4 by omega, show (24 * m + 19) / 3 = 8 * m + 6 by omega,
    show (24 * m + 19) / 2 = 12 * m + 9 by omega]
  simp only [F0, F1, P1, P2, Pq]
  rw [show (6 * m + 4 + 1) / 2 = 3 * m + 2 by omega, show (8 * m + 6 + 1) / 2 = 4 * m + 3 by omega,
    show (24 * m + 19) % 12 = 7 by omega]
  simp only [C2, C1, C0]
  push_cast; ring

lemma res20 (m : ℕ) : (a (24 * m + 20) : ℚ) = Pq (24 * m + 20) := by
  rw [a_closed, if_pos (by omega)]
  rw [show (24 * m + 20) / 4 = 6 * m + 5 by omega, show (24 * m + 20) / 3 = 8 * m + 6 by omega,
    show (24 * m + 20) / 2 = 12 * m + 10 by omega]
  simp only [F0, F1, P1, P2, Pq]
  rw [show (6 * m + 5 + 1) / 2 = 3 * m + 3 by omega, show (8 * m + 6 + 1) / 2 = 4 * m + 3 by omega,
    show (24 * m + 20) % 12 = 8 by omega]
  simp only [C2, C1, C0]
  push_cast; ring

lemma res21 (m : ℕ) : (a (24 * m + 21) : ℚ) = Pq (24 * m + 21) := by
  rw [a_closed, if_neg (by omega)]
  rw [show (24 * m + 21) / 4 = 6 * m + 5 by omega, show (24 * m + 21) / 3 = 8 * m + 7 by omega,
    show (24 * m + 21) / 2 = 12 * m + 10 by omega]
  simp only [F0, F1, P1, P2, Pq]
  rw [show (6 * m + 5 + 1) / 2 = 3 * m + 3 by omega, show (8 * m + 7 + 1) / 2 = 4 * m + 4 by omega,
    show (24 * m + 21) % 12 = 9 by omega]
  simp only [C2, C1, C0]
  push_cast; ring

lemma res22 (m : ℕ) : (a (24 * m + 22) : ℚ) = Pq (24 * m + 22) := by
  rw [a_closed, if_pos (by omega)]
  rw [show (24 * m + 22) / 4 = 6 * m + 5 by omega, show (24 * m + 22) / 3 = 8 * m + 7 by omega,
    show (24 * m + 22) / 2 = 12 * m + 11 by omega]
  simp only [F0, F1, P1, P2, Pq]
  rw [show (6 * m + 5 + 1) / 2 = 3 * m + 3 by omega, show (8 * m + 7 + 1) / 2 = 4 * m + 4 by omega,
    show (24 * m + 22) % 12 = 10 by omega]
  simp only [C2, C1, C0]
  push_cast; ring

lemma res23 (m : ℕ) : (a (24 * m + 23) : ℚ) = Pq (24 * m + 23) := by
  rw [a_closed, if_neg (by omega)]
  rw [show (24 * m + 23) / 4 = 6 * m + 5 by omega, show (24 * m + 23) / 3 = 8 * m + 7 by omega,
    show (24 * m + 23) / 2 = 12 * m + 11 by omega]
  simp only [F0, F1, P1, P2, Pq]
  rw [show (6 * m + 5 + 1) / 2 = 3 * m + 3 by omega, show (8 * m + 7 + 1) / 2 = 4 * m + 4 by omega,
    show (24 * m + 23) % 12 = 11 by omega]
  simp only [C2, C1, C0]
  push_cast; ring

lemma closed (n : ℕ) : (a n : ℚ) = Pq n := by
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < 24 ∧ n = 24 * m + r :=
    ⟨n / 24, n % 24, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 24).symm⟩
  interval_cases r
  · simpa using res0 m
  all_goals first
    | exact res1 m | exact res2 m | exact res3 m | exact res4 m | exact res5 m | exact res6 m
    | exact res7 m | exact res8 m | exact res9 m | exact res10 m | exact res11 m | exact res12 m
    | exact res13 m | exact res14 m | exact res15 m | exact res16 m | exact res17 m | exact res18 m
    | exact res19 m | exact res20 m | exact res21 m | exact res22 m | exact res23 m

lemma Pq_shift (m c : ℕ) : Pq (12 * m + c) = 7 / 1728 * ((12 * m + c : ℕ) : ℚ) ^ 3 +
    C2 (c % 12) * ((12 * m + c : ℕ) : ℚ) ^ 2 + C1 (c % 12) * ((12 * m + c : ℕ) : ℚ) + C0 (c % 12) := by
  unfold Pq; rw [show (12 * m + c) % 12 = c % 12 by omega]

lemma recQ (n : ℕ) (hn : 15 < n) :
    (a n : ℚ) = -(a (n - 1) : ℚ) + 2 * a (n - 3) + 4 * a (n - 4) + 2 * a (n - 5) - a (n - 6)
        - 5 * a (n - 7) - 5 * a (n - 8) - a (n - 9) + 2 * a (n - 10) + 4 * a (n - 11)
        + 2 * a (n - 12) - a (n - 14) - a (n - 15) := by
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < 12 ∧ n = 12 * m + (r + 16) :=
    ⟨(n - 16) / 12, (n - 16) % 12, Nat.mod_lt _ (by norm_num), by omega⟩
  simp only [closed]
  rw [show 12 * m + (r + 16) - 1 = 12 * m + (r + 15) by omega,
    show 12 * m + (r + 16) - 3 = 12 * m + (r + 13) by omega,
    show 12 * m + (r + 16) - 4 = 12 * m + (r + 12) by omega,
    show 12 * m + (r + 16) - 5 = 12 * m + (r + 11) by omega,
    show 12 * m + (r + 16) - 6 = 12 * m + (r + 10) by omega,
    show 12 * m + (r + 16) - 7 = 12 * m + (r + 9) by omega,
    show 12 * m + (r + 16) - 8 = 12 * m + (r + 8) by omega,
    show 12 * m + (r + 16) - 9 = 12 * m + (r + 7) by omega,
    show 12 * m + (r + 16) - 10 = 12 * m + (r + 6) by omega,
    show 12 * m + (r + 16) - 11 = 12 * m + (r + 5) by omega,
    show 12 * m + (r + 16) - 12 = 12 * m + (r + 4) by omega,
    show 12 * m + (r + 16) - 14 = 12 * m + (r + 2) by omega,
    show 12 * m + (r + 16) - 15 = 12 * m + (r + 1) by omega]
  simp only [Pq_shift]
  interval_cases r <;> simp only [C2, C1, C0, Nat.reduceAdd, Nat.reduceMod] <;> push_cast <;> ring

lemma coeff_mk_mul_X_pow (f : ℕ → ℚ) (j k : ℕ) :
    PowerSeries.coeff k (PowerSeries.mk f * PowerSeries.X ^ j) = if j ≤ k then f (k - j) else 0 := by
  rw [PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk]

end OMA.Helpers_a307686

open OMA.Helpers_a307686 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a307686.main := by
  refine ⟨?_, fun n hn => by exact_mod_cast recQ n hn⟩
  set f : ℕ → ℚ := fun n => (OMA.S_oeis_a307686.a n : ℚ) with hf
  have e : PowerSeries.mk f * ((1 - X) ^ 4 * (1 + X) ^ 3 * (1 + X ^ 2) ^ 2 * (1 + X + X ^ 2) ^ 2) =
      PowerSeries.mk f * X ^ 0 + PowerSeries.mk f * X ^ 1 - C 2 * (PowerSeries.mk f * X ^ 3)
      - C 4 * (PowerSeries.mk f * X ^ 4) - C 2 * (PowerSeries.mk f * X ^ 5) + PowerSeries.mk f * X ^ 6
      + C 5 * (PowerSeries.mk f * X ^ 7) + C 5 * (PowerSeries.mk f * X ^ 8) + PowerSeries.mk f * X ^ 9
      - C 2 * (PowerSeries.mk f * X ^ 10) - C 4 * (PowerSeries.mk f * X ^ 11)
      - C 2 * (PowerSeries.mk f * X ^ 12) + PowerSeries.mk f * X ^ 14 + PowerSeries.mk f * X ^ 15 := by
    simp only [map_ofNat]; ring
  have e2 : (X : PowerSeries ℚ) ^ 3 * (1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) =
      X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 8 + X ^ 9 := by ring
  rw [e, e2]
  ext k
  simp only [map_sub, map_add, coeff_C_mul, coeff_mk_mul_X_pow, coeff_X_pow]
  by_cases hk : k ≤ 15
  · interval_cases k <;> simp [hf, closed, Pq, C2, C1, C0] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 16 := ⟨k - 16, by omega⟩
    have hr := recQ (m + 16) (by omega)
    simp only [show m + 16 - 1 = m + 15 from rfl, show m + 16 - 3 = m + 13 from rfl,
      show m + 16 - 4 = m + 12 from rfl, show m + 16 - 5 = m + 11 from rfl,
      show m + 16 - 6 = m + 10 from rfl, show m + 16 - 7 = m + 9 from rfl,
      show m + 16 - 8 = m + 8 from rfl, show m + 16 - 9 = m + 7 from rfl,
      show m + 16 - 10 = m + 6 from rfl, show m + 16 - 11 = m + 5 from rfl,
      show m + 16 - 12 = m + 4 from rfl, show m + 16 - 14 = m + 2 from rfl,
      show m + 16 - 15 = m + 1 from rfl] at hr
    simp only [show 0 ≤ m + 16 by omega, show 1 ≤ m + 16 by omega, show 3 ≤ m + 16 by omega,
      show 4 ≤ m + 16 by omega, show 5 ≤ m + 16 by omega, show 6 ≤ m + 16 by omega,
      show 7 ≤ m + 16 by omega, show 8 ≤ m + 16 by omega, show 9 ≤ m + 16 by omega,
      show 10 ≤ m + 16 by omega, show 11 ≤ m + 16 by omega, show 12 ≤ m + 16 by omega,
      show 14 ≤ m + 16 by omega, show 15 ≤ m + 16 by omega, if_true,
      show m + 16 - 0 = m + 16 from rfl, show m + 16 - 1 = m + 15 from rfl,
      show m + 16 - 3 = m + 13 from rfl, show m + 16 - 4 = m + 12 from rfl,
      show m + 16 - 5 = m + 11 from rfl, show m + 16 - 6 = m + 10 from rfl,
      show m + 16 - 7 = m + 9 from rfl, show m + 16 - 8 = m + 8 from rfl,
      show m + 16 - 9 = m + 7 from rfl, show m + 16 - 10 = m + 6 from rfl,
      show m + 16 - 11 = m + 5 from rfl, show m + 16 - 12 = m + 4 from rfl,
      show m + 16 - 14 = m + 2 from rfl, show m + 16 - 15 = m + 1 from rfl,
      show m + 16 ≠ 3 by omega, show m + 16 ≠ 4 by omega, show m + 16 ≠ 5 by omega,
      show m + 16 ≠ 6 by omega, show m + 16 ≠ 7 by omega, show m + 16 ≠ 8 by omega,
      show m + 16 ≠ 9 by omega, if_false, hf]
    linear_combination hr

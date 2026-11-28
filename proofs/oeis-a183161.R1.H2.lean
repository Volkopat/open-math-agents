import OMAReductions.R_oeis_a183161_R1

/-!
Proof of `OMA.R_oeis_a183161_R1.H2`.
Strong induction on `n`. Writing `d k = a k - b k` and `s k = a k + b k`, the difference of
the two self-convolutions at index `n` equals the sum over `k` of `d k * s (n - k)`. The term
`k = 0` vanishes and the term `k = n` is `2 * d n`. For `0 < k < n` the induction hypothesis
gives `4 ∣ d k` and `2 ∣ s (n - k)`, so these terms are divisible by `8`. Since the whole
difference is divisible by `8`, so is `2 * d n`, hence `4 ∣ d n`.
-/

namespace OMAProof.OeisA183161Lift

open Finset

theorem lift (a b : ℕ → ℤ) (ha : a 0 = 1) (hb : b 0 = 1)
    (h : ∀ n, (∑ k ∈ range (n+1), a k * a (n-k)) ≡
      (∑ k ∈ range (n+1), b k * b (n-k)) [ZMOD 8]) :
    ∀ n, 4 ∣ a n - b n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ha, hb]
  have key : (∑ k ∈ range (n+1), a k * a (n-k)) - (∑ k ∈ range (n+1), b k * b (n-k))
      = ∑ k ∈ range (n+1), (a k - b k) * (a (n-k) + b (n-k)) := by
    have hr : ∑ k ∈ range (n+1), a k * b (n-k) = ∑ k ∈ range (n+1), b k * a (n-k) := by
      rw [← Finset.sum_range_reflect]
      apply Finset.sum_congr rfl
      intro k hk
      have : k < n+1 := mem_range.mp hk
      rw [show n + 1 - 1 - k = n - k by omega, show n - (n - k) = k by omega, mul_comm]
    simp only [sub_mul, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hr]; ring
  have h8 : (8:ℤ) ∣ ∑ k ∈ range (n+1), (a k - b k) * (a (n-k) + b (n-k)) := by
    rw [← key]; exact (h n).symm.dvd
  rw [Finset.sum_range_succ, Nat.sub_self, ha, hb] at h8
  have hsum : (8:ℤ) ∣ ∑ k ∈ range n, (a k - b k) * (a (n-k) + b (n-k)) := by
    apply Finset.dvd_sum
    intro k hk
    have hk' : k < n := mem_range.mp hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp [ha, hb]
    have h1 : (4:ℤ) ∣ a k - b k := ih k hk'
    have h2 : (4:ℤ) ∣ a (n-k) - b (n-k) := ih (n-k) (by omega)
    have h3 : (2:ℤ) ∣ a (n-k) + b (n-k) := by omega
    have := mul_dvd_mul h1 h3
    norm_num at this
    exact this
  have := (dvd_add_right hsum).mp h8
  omega

end OMAProof.OeisA183161Lift

open OMAProof.OeisA183161Lift in
theorem OMA.solution : OMA.R_oeis_a183161_R1.H2 :=
  fun a b ha hb h => lift a b ha hb h

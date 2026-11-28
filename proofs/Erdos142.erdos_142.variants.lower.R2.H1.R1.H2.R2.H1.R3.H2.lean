import OMAReductions.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R3
import Mathlib

namespace E142W2

open Erdos142

theorem r3_mono {a b : ℕ} (h : a ≤ b) : r 3 a ≤ r 3 b :=
  OMA.R_Erdos142_erdos_142_variants_lower_R2.maxCard_monotone 3 h

theorem r3_le (j : ℕ) : r 3 j ≤ j := by
  obtain ⟨S, hS, _, hc⟩ := OMA.R_Erdos142_erdos_142_variants_lower_R2.extremizer
    (k := 3) (by norm_num) j
  rw [← hc]
  exact (Finset.card_mono hS).trans_eq (by simp)

theorem one_le_r3 {j : ℕ} (hj : 0 < j) : 1 ≤ r 3 j := by
  have hS : ({1} : Finset ℕ) ⊆ Finset.Icc 1 j := by
    intro x hx
    simp only [Finset.mem_singleton] at hx
    simp [hx]
    omega
  have hfree : (({1} : Finset ℕ) : Set ℕ).IsAPOfLengthFree (3 : ℕ) := by
    intro t ht hap
    exfalso
    obtain ⟨a, d, hc, _⟩ := hap
    rw [ENat.card_coe_set_eq] at hc
    have h1 : t.encard ≤ 1 := by
      have := Set.encard_le_encard ht
      simpa using this
    rw [hc] at h1
    norm_num at h1
  have := OMA.R_Erdos142_erdos_142_variants_lower_R2.card_le_maxCard hS hfree
  simpa using this

theorem mul_sub (k n : ℕ) : ∀ q : ℕ, r k (q * n) ≤ q * r k n
  | 0 => by
    simp only [zero_mul]
    unfold Erdos142.r Set.IsAPOfLengthFree.maxCard
    apply csSup_le'
    rintro _ ⟨S, hS, _, rfl⟩
    exact (Finset.card_mono hS).trans_eq (by simp)
  | q + 1 => by
    have h := OMA.R_Erdos142_erdos_142_variants_lower_R2.maxCard_add_le k (q * n) n
    have ih := mul_sub k n q
    rw [add_mul, one_mul, add_mul, one_mul]
    exact h.trans (by simpa using ih)

theorem subadd (k N n : ℕ) (hn : 0 < n) (hnN : n ≤ N) : n * r k N ≤ 2 * N * r k n := by
  set q := N / n + 1 with hq
  have hlt : N ≤ q * n := by
    have := Nat.div_add_mod N n
    have := Nat.mod_lt N hn
    have : q * n = n * (N / n) + n := by rw [hq]; ring
    omega
  have h1 : r k N ≤ q * r k n :=
    (OMA.R_Erdos142_erdos_142_variants_lower_R2.maxCard_monotone k hlt).trans (mul_sub k n q)
  have h2 : n * q ≤ 2 * N := by
    have := Nat.mul_div_le N n
    have : n * q = n * (N / n) + n := by rw [hq]; ring
    omega
  calc n * r k N ≤ n * (q * r k n) := Nat.mul_le_mul_left _ h1
    _ = (n * q) * r k n := by ring
    _ ≤ 2 * N * r k n := Nat.mul_le_mul_right _ h2

end E142W2

open Erdos142

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R2_H1_R1_H2_R2_H1_R3.H2 := by
  intro k N hN
  classical
  have hrN := E142W2.one_le_r3 hN
  -- choice of m
  let P : ℕ → Prop := fun m => 2 ^ m * r 3 N ≤ N
  let m := Nat.findGreatest P N
  have hm : P m := Nat.findGreatest_spec (P := P) (Nat.zero_le N) (by simp [P]; exact E142W2.r3_le N)
  have hm' : N < 2 ^ (m + 1) * r 3 N := by
    by_contra hc
    replace hc := Nat.le_of_not_lt hc
    have hle : m + 1 ≤ N := by
      have h1 : m + 1 < 2 ^ (m + 1) := Nat.lt_two_pow_self
      have h2 : 2 ^ (m + 1) ≤ 2 ^ (m + 1) * r 3 N := Nat.le_mul_of_pos_right _ hrN
      omega
    have := Nat.findGreatest_is_greatest (P := P) (Nat.lt_succ_self m) hle
    exact this hc
  -- choice of n
  have hex : ∃ n, 0 < n ∧ 2 ^ m * r 3 n ≤ n := ⟨N, hN, hm⟩
  let n := Nat.find hex
  have hn : 0 < n ∧ 2 ^ m * r 3 n ≤ n := Nat.find_spec hex
  have hnN : n ≤ N := Nat.find_min' hex ⟨hN, hm⟩
  have hmin : ∀ j, 0 < j → j < n → j < 2 ^ m * r 3 j := by
    intro j hj hjn
    have := Nat.find_min hex hjn
    exact Nat.lt_of_not_le (fun h => this ⟨hj, h⟩)
  have hexact : 2 ^ m * r 3 n = n := by
    rcases Nat.lt_or_ge 1 n with h | h
    · have h1 := hmin (n - 1) (by omega) (by omega)
      have h2 : 2 ^ m * r 3 (n - 1) ≤ 2 ^ m * r 3 n :=
        Nat.mul_le_mul_left _ (E142W2.r3_mono (by omega))
      omega
    · have hn1 : n = 1 := by omega
      have h1 := E142W2.one_le_r3 hn.1
      have h2 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      have h3 : 1 ≤ 2 ^ m * r 3 n := Nat.mul_le_mul h2 h1
      omega
  exact ⟨m, n, hn.1, hnN, hexact, hmin, hm', E142W2.subadd k N n hn.1 hnN⟩

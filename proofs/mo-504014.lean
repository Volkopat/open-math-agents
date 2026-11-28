import OMAStatements.S_mo_504014
import Mathlib

open Filter
open scoped Topology

namespace OMA.SignedTail

open OMA.S_mo_504014

private def a (n : ℕ) : ℕ := if n = 0 then 2 else 6

private theorem a_pos (n : ℕ) : 0 < a n := by
  by_cases h : n = 0 <;> norm_num [a, h]

private theorem scaled_limit :
    Tendsto (fun n : ℕ => (a n : ℝ) / (2 : ℝ) ^ (n + 1)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => (2 : ℝ) ^ (n + 1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
      (tendsto_add_atTop_nat 1)
  apply (hpow.const_div_atTop 6).congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn' : n ≠ 0 := by omega
  simp [a, hn']

private theorem ratio_limit :
    Tendsto (fun n : ℕ => (a n : ℝ) / (a (n + 1) : ℝ)) atTop (𝓝 1) := by
  apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn' : n ≠ 0 := by omega
  norm_num [a, hn']

private theorem gcd_zero : tailGcd a 0 = 2 := by
  let D : Set ℕ := {d | ∀ k : ℕ, 0 ≤ k → d ∣ a k}
  change sSup D = 2
  have hmem : 2 ∈ D := by
    intro k _
    by_cases hk : k = 0 <;> norm_num [a, hk]
  have hbound (d : ℕ) (hd : d ∈ D) : d ≤ 2 := by
    have hdiv : d ∣ a 0 := hd 0 (Nat.zero_le 0)
    exact Nat.le_of_dvd (by decide) (by simpa [a] using hdiv)
  exact le_antisymm (csSup_le ⟨2, hmem⟩ hbound) (le_csSup ⟨2, hbound⟩ hmem)

private theorem total (n : ℕ) : (∑ i ∈ Finset.range (n + 1), a i) = 2 + 6 * n := by
  induction n with
  | zero => simp [a]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp [a]
      omega

private theorem signed_repr (e : ℕ → Bool) (n : ℕ) :
    ∃ k : ℤ, (∑ i ∈ Finset.range (n + 1), if e i then (a i : ℤ) else -(a i : ℤ)) =
      (if e 0 then (2 : ℤ) else -2) + 6 * k := by
  induction n with
  | zero => exact ⟨0, by simp [a]⟩
  | succ n ih =>
      obtain ⟨k, hk⟩ := ih
      rw [Finset.sum_range_succ, hk]
      cases he : e (n + 1)
      · refine ⟨k - 1, ?_⟩
        simp [a]
        ring
      · refine ⟨k + 1, ?_⟩
        simp [a]
        ring

private theorem zero_absent (n : ℕ) : (0 : ℤ) ∉ signedSums a (n + 1) := by
  rintro ⟨_, e, he⟩
  obtain ⟨k, hk⟩ := signed_repr e n
  rw [hk] at he
  cases h : e 0 <;> simp [h] at he <;> omega

theorem counterexample : ¬ (type_of% @OMA.S_mo_504014.main) := by
  intro h
  have hc := h a a_pos scaled_limit ⟨1, by norm_num, ratio_limit⟩
    (Or.inr (by rw [gcd_zero]; decide))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hc
  have hleast := hN (2 * N + 2) (by omega)
  have hs : (∑ i ∈ Finset.range (2 * N + 2), a i) = 2 + 6 * (2 * N + 1) :=
    total (2 * N + 1)
  have hres : (∑ i ∈ Finset.range (2 * N + 2), a i) % (2 * tailGcd a 0) = 0 := by
    rw [gcd_zero, hs]
    omega
  have hmem := hleast.1
  rw [hres] at hmem
  exact zero_absent (2 * N + 1) hmem

end OMA.SignedTail

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_504014.main) :=
  OMA.SignedTail.counterexample
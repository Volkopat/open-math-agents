import OMAStatements.S_oeis_a066839
import Mathlib

-- Problem: A066839: a(n) = sum of positive divisors k of n with k <= sqrt(n).
-- Upstream: formal-conjectures statements/oeis-a066839.lean:0 (declaration OMA.S_oeis_a066839.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The sum m + (m+2) + ... + (m + 2(k-1)) is k m + k (k - 1) = k (m + k - 1). So it equals n
exactly when k divides n and m = n/k - k + 1, and m >= 1 means k <= n/k, that is k^2 <= n. This
gives a bijection between the divisors k of n with k^2 <= n and the pairs (k, m), preserving k. -/

namespace A066839Aux

open OMA.S_oeis_a066839

theorem sum_ap (k m : ℕ) : ∑ i ∈ Finset.range k, (m + 2 * i) = k * m + k * (k - 1) := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, ← Finset.mul_sum,
    mul_comm 2, Finset.sum_range_id_mul_two]

theorem eq (n : ℕ) (hn : 1 ≤ n) : a n = totalParts n := by
  unfold a totalParts
  refine Finset.sum_nbij' (fun k => (k, n / k + 1 - k)) (fun p => p.1) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Nat.mem_divisors] at hk
    obtain ⟨⟨hdvd, _⟩, hsq⟩ := hk
    have hkpos : 0 < k := Nat.pos_of_dvd_of_pos hdvd (by omega)
    have hkn : k ≤ n := Nat.le_of_dvd (by omega) hdvd
    have hq : k ≤ n / k := (Nat.le_div_iff_mul_le hkpos).mpr hsq
    have hqn : n / k ≤ n := Nat.div_le_self n k
    obtain ⟨d, hd⟩ : ∃ d, n / k = k + d := ⟨n / k - k, by omega⟩
    have hm : n / k + 1 - k = d + 1 := by omega
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨⟨hkpos, hkn⟩, by omega, by omega⟩, ?_⟩
    rw [sum_ap, hm]
    have hmul : k * (n / k) = n := Nat.mul_div_cancel' hdvd
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [← hmul, hd, Nat.add_sub_cancel]
    ring
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hk1, hkn⟩, hm1, _⟩, hsum⟩ := hp
    rw [sum_ap] at hsum
    simp only [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨⟨p.2 + (p.1 - 1), by rw [← hsum]; ring⟩, by omega⟩, ?_⟩
    have h1 : p.1 * 1 ≤ p.1 * p.2 := Nat.mul_le_mul_left _ hm1
    have h2 : p.1 * p.1 = p.1 * 1 + p.1 * (p.1 - 1) := by
      obtain ⟨j, hj⟩ : ∃ j, p.1 = j + 1 := ⟨p.1 - 1, by omega⟩
      rw [hj, Nat.add_sub_cancel]
      ring
    omega
  · intro k _
    rfl
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hk1, _⟩, hm1, _⟩, hsum⟩ := hp
    rw [sum_ap] at hsum
    have hdiv : n / p.1 = p.2 + (p.1 - 1) := by
      have : n = p.1 * (p.2 + (p.1 - 1)) := by rw [← hsum]; ring
      rw [this, Nat.mul_div_cancel_left _ (by omega)]
    ext
    · rfl
    · simp only
      omega
  · intro k _
    rfl

end A066839Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a066839.main :=
  A066839Aux.eq

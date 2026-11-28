import OMAStatements.S_oeis_a284475
import Mathlib

open OMA.S_oeis_a284475
open PowerSeries

private lemma inv_geom (m : ℕ) (hm : 1 ≤ m) :
    (1 - X ^ m : PowerSeries ℚ)⁻¹ = mk (fun k => if m ∣ k then (1 : ℚ) else 0) := by
  symm
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by simp [zero_pow (show m ≠ 0 by omega)])]
  ext e
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow', coeff_one, coeff_mk]
  by_cases he : m ≤ e
  · rw [if_pos he, coeff_mk]
    have : m ∣ e ↔ m ∣ e - m := by
      conv_lhs => rw [show e = e - m + m by omega]
      exact Nat.dvd_add_self_right
    by_cases h : m ∣ e
    · rw [if_pos h, if_pos (this.1 h), if_neg (by omega)]; simp
    · rw [if_neg h, if_neg (fun h' => h (this.2 h')), if_neg (by omega)]; simp
  · rw [if_neg he]
    rcases Nat.eq_zero_or_pos e with rfl | hpos
    · simp
    · rw [if_neg (fun h => by have := Nat.le_of_dvd hpos h; omega), if_neg (by omega)]; simp

private lemma A_eq (n : ℕ) : A204217 n = ∑ m ∈ Finset.Icc 1 n,
    (if m * (m + 1) / 2 ≤ n ∧ m ∣ n - m * (m + 1) / 2 then (m : ℚ) else 0) := by
  unfold A204217
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Finset.mem_Icc] at hm
  rw [inv_geom m hm.1, mul_assoc, coeff_C_mul, coeff_X_pow_mul', coeff_mk]
  by_cases h1 : m * (m + 1) / 2 ≤ n
  · by_cases h2 : m ∣ n - m * (m + 1) / 2
    · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩, mul_one]
    · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 h.2), mul_zero]
  · rw [if_neg h1, if_neg (fun h => h1 h.1), mul_zero]

private def eqP (n d : ℕ) (hd : d ∣ n) (hd0 : 0 < d) : Nat.Partition n where
  parts := Multiset.replicate (n / d) d
  parts_pos := fun h => by rw [Multiset.eq_of_mem_replicate h]; exact hd0
  parts_sum := by rw [Multiset.sum_replicate, smul_eq_mul, Nat.div_mul_cancel hd]

open Classical in
private lemma E_eq (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ (Finset.univ : Finset (Nat.Partition n)).filter IsEqualParts, (p.parts.card : ℤ) =
      (ArithmeticFunction.sigma 1 n : ℤ) := by
  rw [ArithmeticFunction.sigma_one_apply, ← Nat.sum_div_divisors, Nat.cast_sum]
  symm
  refine Finset.sum_bij (fun d hd => eqP n d (Nat.dvd_of_mem_divisors hd)
      (Nat.pos_of_mem_divisors hd)) ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, IsEqualParts, eqP]
    intro i hi j hj
    rw [Multiset.eq_of_mem_replicate hi, Multiset.eq_of_mem_replicate hj]
  · intro d1 h1 d2 h2 h
    have hp := congrArg Nat.Partition.parts h
    simp only [eqP] at hp
    have hpos : 0 < n / d1 := Nat.div_pos (Nat.divisor_le h1) (Nat.pos_of_mem_divisors h1)
    have hm : d1 ∈ Multiset.replicate (n / d1) d1 := Multiset.mem_replicate.2 ⟨hpos.ne', rfl⟩
    rw [hp] at hm
    exact (Multiset.eq_of_mem_replicate hm)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, IsEqualParts] at hp
    have hne : p.parts ≠ 0 := by
      intro h0; have := p.parts_sum; rw [h0, Multiset.sum_zero] at this; omega
    obtain ⟨d, hd⟩ := Multiset.exists_mem_of_ne_zero hne
    have hrep : p.parts = Multiset.replicate p.parts.card d :=
      Multiset.eq_replicate.2 ⟨rfl, fun b hb => hp b hb d hd⟩
    have hsum := p.parts_sum
    rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hsum
    have hd0 : 0 < d := p.parts_pos hd
    have hdvd : d ∣ n := Dvd.intro_left _ hsum
    have hcard : n / d = p.parts.card := Nat.div_eq_of_eq_mul_left hd0 hsum.symm
    refine ⟨d, Nat.mem_divisors.2 ⟨hdvd, by omega⟩, ?_⟩
    apply Nat.Partition.ext
    simp only [eqP]
    rw [hcard, ← hrep]
  · intro d hd
    simp [eqP]

private lemma tri (m : ℕ) : m * (m + 1) / 2 = (∑ i ∈ Finset.range m, i) + m := by
  have h := Finset.sum_range_id_mul_two m
  have h2 : m * (m + 1) = m * (m - 1) + 2 * m := by
    rcases m with _ | m
    · simp
    · simp only [Nat.add_sub_cancel]; ring
  omega

private lemma msum (a m : ℕ) : ((Multiset.range m).map (fun i => a + i)).sum =
    m * a + ∑ i ∈ Finset.range m, i := by
  rw [show ((Multiset.range m).map (fun i => a + i)).sum = ∑ i ∈ Finset.range m, (a + i) from rfl,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]

private def consP (n m : ℕ) (h : m * (m + 1) / 2 ≤ n ∧ m ∣ n - m * (m + 1) / 2) : Nat.Partition n where
  parts := (Multiset.range m).map (fun i => ((n - m * (m + 1) / 2) / m + 1) + i)
  parts_pos := fun hi => by
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hi
    exact Nat.add_pos_left (Nat.succ_pos _) _
  parts_sum := by
    rw [msum]
    obtain ⟨q, hq⟩ := h.2
    have ht := tri m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp at h ⊢; omega
    · rw [hq, Nat.mul_div_cancel_left _ hm, mul_add, mul_one, ← hq]
      omega

open Classical in
private lemma C_eq (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ (Finset.univ : Finset (Nat.Partition n)).filter IsConsecutive, (p.parts.card : ℤ) =
      ∑ m ∈ (Finset.Icc 1 n).filter (fun m => m * (m + 1) / 2 ≤ n ∧ m ∣ n - m * (m + 1) / 2),
        (m : ℤ) := by
  symm
  refine Finset.sum_bij (fun m hm => consP n m (Finset.mem_filter.1 hm).2) ?_ ?_ ?_ ?_
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, IsConsecutive, consP]
    exact ⟨_, m, rfl⟩
  · intro m1 h1 m2 h2 h
    have hp := congrArg (fun p : Nat.Partition n => p.parts.card) h
    simpa [consP] using hp
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, IsConsecutive] at hp
    obtain ⟨a, m, hpa⟩ := hp
    have hsum := p.parts_sum
    rw [hpa, msum] at hsum
    have ht := tri m
    have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp at hsum; omega
      · exact hm
    have ha : 1 ≤ a := by
      have : a + 0 ∈ p.parts := by
        rw [hpa]; exact Multiset.mem_map.2 ⟨0, Multiset.mem_range.2 (by omega), rfl⟩
      have := p.parts_pos this; omega
    have hma : m ≤ m * a := Nat.le_mul_of_pos_right m ha
    have hT : m * (m + 1) / 2 ≤ n := by omega
    have hdiff : n - m * (m + 1) / 2 = m * (a - 1) := by
      rw [Nat.mul_sub, mul_one]; omega
    have hc : m * (m + 1) / 2 ≤ n ∧ m ∣ n - m * (m + 1) / 2 := ⟨hT, ⟨a - 1, hdiff⟩⟩
    refine ⟨m, Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hm, by omega⟩, hc⟩, ?_⟩
    apply Nat.Partition.ext
    simp only [consP]
    rw [hpa, hdiff, Nat.mul_div_cancel_left _ (by omega), Nat.sub_add_cancel ha]
  · intro m hm
    simp [consP]

theorem OMA.solution : type_of% @OMA.S_oeis_a284475.main := by
  intro n hn
  classical
  unfold a
  rw [A_eq, ← Finset.sum_filter]
  convert congrArg (fun z : ℤ => (z : ℚ)) (congrArg₂ (fun x y : ℤ => x - y) (E_eq n hn) (C_eq n hn))
    using 1
  push_cast; rfl

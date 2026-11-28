import OMAStatements.S_mo_471586
import Mathlib
open OMA.S_mo_471586

/-- `2 m` is a sum of distinct pronic numbers `(k+1)(k+2)`. -/
def PRep (m : ℕ) : Prop :=
  ∃ K : Finset ℕ, (∀ k ∈ K, (k + 1) * (k + 2) ≤ 2 * m) ∧ 2 * m = ∑ k ∈ K, (k + 1) * (k + 2)

lemma rep_base (m : ℕ) (h1 : 34 ≤ m) (h2 : m ≤ 78) : PRep m := by
  interval_cases m
  · exact ⟨{2, 6}, by decide, by decide⟩
  · exact ⟨{0, 2, 6}, by decide, by decide⟩
  · exact ⟨{7}, by decide, by decide⟩
  · exact ⟨{0, 7}, by decide, by decide⟩
  · exact ⟨{3, 6}, by decide, by decide⟩
  · exact ⟨{1, 7}, by decide, by decide⟩
  · exact ⟨{0, 1, 7}, by decide, by decide⟩
  · exact ⟨{1, 3, 6}, by decide, by decide⟩
  · exact ⟨{2, 7}, by decide, by decide⟩
  · exact ⟨{4, 6}, by decide, by decide⟩
  · exact ⟨{0, 4, 6}, by decide, by decide⟩
  · exact ⟨{8}, by decide, by decide⟩
  · exact ⟨{0, 8}, by decide, by decide⟩
  · exact ⟨{0, 3, 7}, by decide, by decide⟩
  · exact ⟨{1, 8}, by decide, by decide⟩
  · exact ⟨{5, 6}, by decide, by decide⟩
  · exact ⟨{0, 5, 6}, by decide, by decide⟩
  · exact ⟨{2, 8}, by decide, by decide⟩
  · exact ⟨{0, 2, 8}, by decide, by decide⟩
  · exact ⟨{3, 4, 6}, by decide, by decide⟩
  · exact ⟨{1, 2, 8}, by decide, by decide⟩
  · exact ⟨{9}, by decide, by decide⟩
  · exact ⟨{0, 9}, by decide, by decide⟩
  · exact ⟨{5, 7}, by decide, by decide⟩
  · exact ⟨{1, 9}, by decide, by decide⟩
  · exact ⟨{0, 1, 9}, by decide, by decide⟩
  · exact ⟨{4, 8}, by decide, by decide⟩
  · exact ⟨{2, 9}, by decide, by decide⟩
  · exact ⟨{0, 2, 9}, by decide, by decide⟩
  · exact ⟨{1, 4, 8}, by decide, by decide⟩
  · exact ⟨{6, 7}, by decide, by decide⟩
  · exact ⟨{3, 9}, by decide, by decide⟩
  · exact ⟨{10}, by decide, by decide⟩
  · exact ⟨{0, 10}, by decide, by decide⟩
  · exact ⟨{1, 3, 9}, by decide, by decide⟩
  · exact ⟨{1, 10}, by decide, by decide⟩
  · exact ⟨{4, 9}, by decide, by decide⟩
  · exact ⟨{0, 4, 9}, by decide, by decide⟩
  · exact ⟨{2, 10}, by decide, by decide⟩
  · exact ⟨{6, 8}, by decide, by decide⟩
  · exact ⟨{0, 6, 8}, by decide, by decide⟩
  · exact ⟨{1, 2, 10}, by decide, by decide⟩
  · exact ⟨{3, 10}, by decide, by decide⟩
  · exact ⟨{0, 3, 10}, by decide, by decide⟩
  · exact ⟨{11}, by decide, by decide⟩

lemma rep_all : ∀ m, 34 ≤ m → PRep m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    by_cases hb : m ≤ 78
    · exact rep_base m hm hb
    rw [not_le] at hb
    have hex : ∃ k, 2 * (m - 34) < (k + 2) * (k + 3) := ⟨m, by
      have : 2 * (m - 34) ≤ 2 * m := by omega
      nlinarith⟩
    set k := Nat.find hex with hk
    have hk1 : 2 * (m - 34) < (k + 2) * (k + 3) := Nat.find_spec hex
    have hk8 : 8 ≤ k := by
      by_contra h
      rw [not_le] at h
      have : (k + 2) * (k + 3) ≤ 90 := by
        have h7 : k + 2 ≤ 9 := by omega
        have h8 : k + 3 ≤ 10 := by omega
        calc (k + 2) * (k + 3) ≤ 9 * 10 := Nat.mul_le_mul h7 h8
          _ = 90 := by norm_num
      omega
    have hk2 : (k + 1) * (k + 2) ≤ 2 * (m - 34) := by
      have := Nat.find_min hex (show k - 1 < k by omega)
      rw [not_lt] at this
      have e1 : k - 1 + 2 = k + 1 := by omega
      have e2 : k - 1 + 3 = k + 2 := by omega
      rw [e1, e2] at this
      exact this
    obtain ⟨t, ht⟩ : ∃ t, (k + 1) * (k + 2) = 2 * t :=
      ⟨(k + 1) * (k + 2) / 2, (Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self (k + 1))).symm⟩
    have e3 : (k + 2) * (k + 3) = (k + 1) * (k + 2) + 2 * (k + 2) := by ring
    have h9 : 9 * (k + 2) ≤ (k + 1) * (k + 2) := Nat.mul_le_mul_right _ (by omega)
    have hm1 : 34 ≤ m - t := by omega
    have hm2 : m - t < m := by omega
    obtain ⟨K, hK1, hK2⟩ := ih (m - t) hm2 hm1
    have hkK : k ∉ K := by
      intro hkm
      have := hK1 k hkm
      omega
    refine ⟨insert k K, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · omega
      · have := hK1 i hi
        omega
    · rw [Finset.sum_insert hkK, ← hK2]
      omega

/-- `Fsum c = 2 + 3 + ... + (c + 2)`. -/
def Fsum (c : ℕ) : ℕ := ∑ k ∈ Finset.range (c + 1), (k + 2)

lemma Fsum_succ (c : ℕ) : Fsum (c + 1) = Fsum c + (c + 3) := by
  unfold Fsum
  rw [Finset.sum_range_succ]

lemma Fsum_two (c : ℕ) : 2 * Fsum c = (c + 1) * (c + 4) := by
  induction c with
  | zero => simp [Fsum]
  | succ c ih => rw [Fsum_succ, mul_add, ih]; ring

lemma build (c : ℕ) (K : Finset ℕ) (hK : K ⊆ Finset.range (c + 1)) :
    ∑ k ∈ Finset.range (c + 1), (k + 2) ^ (if k ∈ K then 2 else 1) =
      Fsum c + ∑ k ∈ K, (k + 1) * (k + 2) := by
  have h1 : ∀ k, (k + 2) ^ (if k ∈ K then 2 else 1) =
      (k + 2) + (if k ∈ K then (k + 1) * (k + 2) else 0) := by
    intro k
    split_ifs <;> ring
  simp only [h1]
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hK]
  rfl

theorem OMA.solution : type_of% @OMA.S_mo_471586.main := by
  refine ⟨300, fun a ha => ?_⟩
  have hex : ∃ c, a < Fsum (c + 1) + 68 := ⟨a, by
    have := Fsum_two (a + 1)
    nlinarith⟩
  set c := Nat.find hex with hc
  have hc1 : a < Fsum (c + 1) + 68 := Nat.find_spec hex
  have hc0 : Fsum c + 68 ≤ a := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [h0]; simp [Fsum]; omega
    · have := Nat.find_min hex (show c - 1 < c by omega)
      rw [not_lt, show c - 1 + 1 = c by omega] at this
      exact this
  have hc10 : 10 ≤ c := by
    by_contra h
    rw [not_le] at h
    have h2 := Fsum_two (c + 1)
    have : (c + 1 + 1) * (c + 1 + 4) ≤ 11 * 14 := Nat.mul_le_mul (by omega) (by omega)
    omega
  -- choose c' with the right parity
  obtain ⟨c', hc'1, hc'2, hc'3, hc'4, hc'5⟩ : ∃ c', c ≤ c' + 2 ∧ c' ≤ c ∧ Fsum c' + 68 ≤ a ∧
      a - Fsum c' < 3 * c + 74 ∧ (a - Fsum c') % 2 = 0 := by
    have f1 := Fsum_succ (c - 1)
    have f2 := Fsum_succ (c - 2)
    rw [show c - 1 + 1 = c by omega] at f1
    rw [show c - 2 + 1 = c - 1 by omega] at f2
    have hF1 := Fsum_succ c
    by_cases p0 : (a - Fsum c) % 2 = 0
    · exact ⟨c, by omega, le_rfl, hc0, by omega, p0⟩
    by_cases p1 : (a - Fsum (c - 1)) % 2 = 0
    · exact ⟨c - 1, by omega, by omega, by omega, by omega, p1⟩
    · exact ⟨c - 2, by omega, by omega, by omega, by omega, by omega⟩
  set m := (a - Fsum c') / 2 with hm
  have hm2 : 2 * m = a - Fsum c' := by omega
  obtain ⟨K, hK1, hK2⟩ := rep_all m (by omega)
  have hbig : 3 * c + 74 ≤ (c' + 2) * (c' + 3) := by
    have : c * (c + 1) ≤ (c' + 2) * (c' + 3) := Nat.mul_le_mul (by omega) (by omega)
    have h10 : 10 * (c + 1) ≤ c * (c + 1) := Nat.mul_le_mul_right _ hc10
    omega
  have hKsub : K ⊆ Finset.range (c' + 1) := by
    intro k hk
    rw [Finset.mem_range]
    by_contra hcon
    rw [not_lt] at hcon
    have h1 := hK1 k hk
    have : (c' + 2) * (c' + 3) ≤ (k + 1) * (k + 2) := Nat.mul_le_mul (by omega) (by omega)
    omega
  refine ⟨c', fun k => if k ∈ K then 2 else 1, ?_, ?_⟩
  · intro k _
    simp only
    split_ifs <;> norm_num
  · rw [build c' K hKsub, ← hK2]
    omega

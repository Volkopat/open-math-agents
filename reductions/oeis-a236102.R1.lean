import OMAStatements.S_oeis_a236102

-- Reduction oeis-a236102.R1 of A236102: Numbers whose divisors are partition numbers.
-- Credit: @PedroFilipeCruz
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_oeis_a236102_R1

open OMA.S_oeis_a236102

-- Open core: if q * b is a partition number with q a prime partition number and b > 1 a partition
-- number, then q * b is one of six values (checked numerically for every p(m) with m up to 12000).
def H1 : Prop :=
  ∀ q b : ℕ, q.Prime → 1 < b → IsPartitionNumber q → IsPartitionNumber b →
    IsPartitionNumber (q * b) → q * b ∈ ({15, 22, 30, 77, 231, 385} : Finset ℕ)

-- p(m) is strictly increasing from m = 1 on.
def H2 : Prop :=
  ∀ m : ℕ, 1 ≤ m → Fintype.card (Nat.Partition m) < Fintype.card (Nat.Partition (m + 1))

-- The first values of p(m) (A000041).
def H3 : Prop :=
  Fintype.card (Nat.Partition 0) = 1 ∧ Fintype.card (Nat.Partition 1) = 1 ∧
  Fintype.card (Nat.Partition 2) = 2 ∧ Fintype.card (Nat.Partition 3) = 3 ∧
  Fintype.card (Nat.Partition 4) = 5 ∧ Fintype.card (Nat.Partition 5) = 7 ∧
  Fintype.card (Nat.Partition 6) = 11 ∧ Fintype.card (Nat.Partition 7) = 15 ∧
  Fintype.card (Nat.Partition 8) = 22 ∧ Fintype.card (Nat.Partition 9) = 30 ∧
  Fintype.card (Nat.Partition 10) = 42 ∧ Fintype.card (Nat.Partition 11) = 56 ∧
  Fintype.card (Nat.Partition 12) = 77

lemma mono_of_H2 (h2 : H2) {k m : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    Fintype.card (Nat.Partition k) ≤ Fintype.card (Nat.Partition m) := by
  induction m, hkm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hkm ih => exact ih.trans (h2 m (hk.trans hkm)).le

lemma not_pn (h2 : H2) (h0 : Fintype.card (Nat.Partition 0) = 1)
    (h1 : Fintype.card (Nat.Partition 1) = 1) {k x : ℕ} (hk : 1 ≤ k)
    (hlo : Fintype.card (Nat.Partition k) < x) (hhi : x < Fintype.card (Nat.Partition (k + 1))) :
    ¬ IsPartitionNumber x := by
  rintro ⟨m, hm⟩
  rcases Nat.lt_or_ge k m with h | h
  · have := mono_of_H2 h2 (by omega : 1 ≤ k + 1) (by omega : k + 1 ≤ m)
    omega
  · rcases Nat.eq_zero_or_pos m with rfl | hm0
    · have := mono_of_H2 h2 (le_refl 1) hk
      omega
    · have := mono_of_H2 h2 hm0 h
      omega

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a236102.main := by
  rintro h1 h2 ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩
  have pn : ∀ m x, Fintype.card (Nat.Partition m) = x → IsPartitionNumber x :=
    fun m x h => ⟨m, h⟩
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hn1, hnp, hterm⟩
    unfold IsTerm at hterm
    have hn0 : n ≠ 0 := by omega
    have hpn : ∀ d, d ∣ n → IsPartitionNumber d :=
      fun d hd => hterm d (Nat.mem_divisors.2 ⟨hd, hn0⟩)
    have hqp : n.minFac.Prime := Nat.minFac_prime (by omega)
    have hqlt : n.minFac < n := (Nat.not_prime_iff_minFac_lt (by omega)).1 hnp
    obtain ⟨b, hb⟩ := Nat.minFac_dvd n
    generalize n.minFac = q at hqp hqlt hb
    have hb1 : 1 < b := by
      by_contra hcon
      have hb' : b ≤ 1 := by omega
      interval_cases b <;> omega
    have hmem := h1 q b hqp hb1 (hpn q ⟨b, hb⟩) (hpn b ⟨q, by rw [hb, mul_comm]⟩)
      (by rw [← hb]; exact hpn n dvd_rfl)
    rw [← hb] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact absurd (hpn 6 (by rw [h]; decide))
        (not_pn h2 p0 p1 (k := 4) (by norm_num) (by norm_num [p4]) (by norm_num [p5]))
    · exact Or.inr (Or.inr h)
    · exact absurd (hpn 21 (by rw [h]; decide))
        (not_pn h2 p0 p1 (k := 7) (by norm_num) (by norm_num [p7]) (by norm_num [p8]))
    · exact absurd (hpn 35 (by rw [h]; decide))
        (not_pn h2 p0 p1 (k := 9) (by norm_num) (by norm_num [p9]) (by norm_num [p10]))
  · rintro (rfl | rfl | rfl)
    · refine ⟨by norm_num, by norm_num, ?_⟩
      unfold IsTerm
      have hd : Nat.divisors 15 = {1, 3, 5, 15} := by decide
      rw [hd]
      intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl | rfl | rfl
      exacts [pn 0 1 p0, pn 3 3 p3, pn 4 5 p4, pn 7 15 p7]
    · refine ⟨by norm_num, by norm_num, ?_⟩
      unfold IsTerm
      have hd : Nat.divisors 22 = {1, 2, 11, 22} := by decide
      rw [hd]
      intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl | rfl | rfl
      exacts [pn 0 1 p0, pn 2 2 p2, pn 6 11 p6, pn 8 22 p8]
    · refine ⟨by norm_num, by norm_num, ?_⟩
      unfold IsTerm
      have hd : Nat.divisors 77 = {1, 7, 11, 77} := by decide
      rw [hd]
      intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl | rfl | rfl
      exacts [pn 0 1 p0, pn 5 7 p5, pn 6 11 p6, pn 12 77 p12]

end OMA.R_oeis_a236102_R1

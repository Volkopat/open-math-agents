import OMAStatements.S_oeis_a259301
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a259301.main := by
  intro a b k ha hb hao hbo hab hk hbdef hk2
  have ha3 : 2 * k + 3 ≤ a := by omega
  have hbig : a + b < a * a := by
    have h1 : (2 * k + 3) * a ≤ a * a := Nat.mul_le_mul ha3 le_rfl
    subst hbdef
    nlinarith
  unfold OMA.S_oeis_a259301.PrimePartitionable
  refine ⟨{a, b}, ?_, ?_⟩
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    have h2 := ha.two_le
    rcases hp with h | h
    · rw [h]
      exact ⟨ha, by omega⟩
    · rw [h]
      exact ⟨hb, by omega⟩
  · intro n1 n2 h1 h2 hsum
    by_cases hex : ∃ p : ℕ, p.Prime ∧ p < a + b ∧ p ∉ ({a, b} : Finset ℕ) ∧ p ∣ n2
    · exact Or.inr hex
    · left
      have hdiv : ∀ p, p.Prime → p ∣ n2 → p = a ∨ p = b := by
        intro p hp hpd
        by_contra hne
        have hple : p ≤ n2 := Nat.le_of_dvd (by omega) hpd
        apply hex
        refine ⟨p, hp, by omega, ?_, hpd⟩
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact hne
      have haS : a ∈ ({a, b} : Finset ℕ) := by simp
      have hbS : b ∈ ({a, b} : Finset ℕ) := by simp
      by_cases hn2 : n2 = 1
      · refine ⟨a, haS, ?_⟩
        have e : a * (2 * k + 1) = 2 * k * a + a := by ring
        exact ⟨2 * k + 1, by omega⟩
      · by_cases hbd : b ∣ n2
        · obtain ⟨c, hc⟩ := hbd
          have hc1 : c = 1 := by
            rcases Nat.lt_trichotomy c 1 with h | h | h
            · have hc0 : c = 0 := by omega
              rw [hc0, Nat.mul_zero] at hc
              omega
            · exact h
            · have h' : 2 ≤ c := by omega
              have hm : b * 2 ≤ b * c := Nat.mul_le_mul le_rfl h'
              omega
          rw [hc1, Nat.mul_one] at hc
          refine ⟨a, haS, ?_⟩
          exact ⟨1, by omega⟩
        · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hn2
          have had : a ∣ n2 := by
            rcases hdiv p hp hpd with h | h
            · rw [← h]
              exact hpd
            · rw [h] at hpd
              exact absurd hpd hbd
          obtain ⟨c, hc⟩ := had
          by_cases hc1 : c = 1
          · rw [hc1, Nat.mul_one] at hc
            refine ⟨b, hbS, ?_⟩
            exact ⟨1, by omega⟩
          · exfalso
            have hc0 : c ≠ 0 := by
              intro hc0
              rw [hc0, Nat.mul_zero] at hc
              omega
            obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hc1
            have hrn : r ∣ n2 := by
              rw [hc]
              exact Dvd.dvd.mul_left hrd a
            rcases hdiv r hr hrn with h | h
            · rw [h] at hrd
              have hca : a ≤ c := Nat.le_of_dvd (Nat.pos_of_ne_zero hc0) hrd
              have hm : a * a ≤ a * c := Nat.mul_le_mul le_rfl hca
              omega
            · rw [h] at hrn
              exact hbd hrn

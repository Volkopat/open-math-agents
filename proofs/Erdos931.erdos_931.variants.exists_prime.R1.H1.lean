import OMAReductions.R_Erdos931_erdos_931_variants_exists_prime_R1
import Mathlib

-- Original proof: @ivillar. Prime-factor membership lemma: @menelikbaye-digitalmethod.

open Finset

private theorem primeFactor_window {q n k : ℕ} (hq : q.Prime) :
    q ∈ (∏ i ∈ Icc 1 k, (n + i)).primeFactors ↔ ∃ i ∈ Icc 1 k, q ∣ n + i := by
  have hpos : 0 < ∏ i ∈ Icc 1 k, (n + i) :=
    Finset.prod_pos fun i hi => by have := (mem_Icc.mp hi).1; omega
  rw [Nat.mem_primeFactors, hq.prime.dvd_finsetProd_iff]
  exact ⟨fun h => h.2.1, fun h => ⟨hq, h, ne_of_gt hpos⟩⟩

theorem OMA.solution : OMA.R_Erdos931_erdos_931_variants_exists_prime_R1.H1 := by
  intro k₁ k₂ n₁ n₂ hle heq
  constructor
  · intro q hq hgt hbound
    have hright := (primeFactor_window (n := n₂) (k := k₂) hq).2
      ⟨q - n₂, mem_Icc.mpr ⟨by omega, by omega⟩, by rw [show n₂ + (q - n₂) = q by omega]⟩
    rw [← heq] at hright
    obtain ⟨i, hi, hd⟩ := (primeFactor_window hq).1 hright
    have := mem_Icc.mp hi
    have := Nat.le_of_dvd (by omega) hd
    omega
  · intro q hleft
    have hq := Nat.prime_of_mem_primeFactors hleft
    obtain ⟨i, hi, hd⟩ := (primeFactor_window hq).1 hleft
    rw [heq] at hleft
    obtain ⟨j, hj, he⟩ := (primeFactor_window hq).1 hleft
    have := mem_Icc.mp hi
    have := mem_Icc.mp hj
    have := Nat.le_of_dvd (by omega) (Nat.dvd_sub he hd)
    omega

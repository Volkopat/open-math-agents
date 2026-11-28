import OMAStatements.S_oeis_a087324
import Mathlib

open OMA.S_oeis_a087324 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a087324.main) := by
  intro h
  obtain ⟨n, hn, hs⟩ := h.2 (0 : Multiset ℕ) (by simp)
  have hcard : n.primeFactors.card = 0 := by
    have he := congrArg Multiset.card hs
    simpa [sig] using he
  have hn1 : n = 1 := by
    by_contra hne
    have hm : n.minFac ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime hne, Nat.minFac_dvd n, by have := hn.1; omega⟩
    have hc := Finset.card_pos.mpr ⟨_, hm⟩
    omega
  subst n
  have hc : sig (comp9 1) = (0 : Multiset ℕ) := hn.2.2.symm.trans hs
  have hcomp : comp9 1 = 8 := by decide
  rw [hcomp] at hc
  have hcard8 : (8 : ℕ).primeFactors.card = 0 := by
    have he := congrArg Multiset.card hc
    simpa [sig] using he
  have hm : 2 ∈ (8 : ℕ).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, by decide, by decide⟩
  have hpos := Finset.card_pos.mpr ⟨_, hm⟩
  omega
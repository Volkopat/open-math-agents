import OMAStatements.S_oeis_a321644
import Mathlib

open OMA.S_oeis_a321644

namespace P321644

theorem sqf_le (n : ℕ) (T : Finset ℕ) (hn : Squarefree n) (hn0 : n ≠ 0)
    (h : ∀ q : ℕ, q.Prime → q ∣ n → q ∈ T) : n ≤ ∏ q ∈ T.filter Nat.Prime, q := by
  have hsub : n.primeFactors ⊆ T.filter Nat.Prime := by
    intro q hq
    rw [Nat.mem_primeFactors] at hq
    simp only [Finset.mem_filter]
    exact ⟨h q hq.1 hq.2.1, hq.1⟩
  have e : ∏ q ∈ n.primeFactors, q = n := Nat.prod_primeFactors_of_squarefree hn
  calc n = ∏ q ∈ n.primeFactors, q := e.symm
    _ ≤ ∏ q ∈ T.filter Nat.Prime, q := by
      apply Finset.prod_le_prod_of_subset_of_one_le' hsub
      intro q hq _
      simp only [Finset.mem_filter] at hq
      exact hq.2.one_lt.le

end P321644

theorem OMA.solution : type_of% @OMA.S_oeis_a321644.main := by
  constructor
  · intro hT
    by_contra hL
    rw [Set.not_infinite] at hL
    have hTw : twinPrimes.Finite := by
      unfold twinPrimes
      exact hL.union (hL.image _)
    obtain ⟨T, hTT⟩ := hTw.exists_finset_coe
    apply hT
    apply Set.Finite.subset (Set.finite_Iic (∏ q ∈ T.filter Nat.Prime, q))
    intro n hn
    obtain ⟨hsq, hodd, h1, -, hq⟩ := hn
    simp only [Set.mem_Iic]
    apply P321644.sqf_le n T hsq (by omega)
    intro q hqp hqd
    have := hq q hqp hqd
    rw [← hTT] at this
    exact_mod_cast this
  · intro hL
    have hL3 : ({p | p.Prime ∧ (p + 2).Prime ∧ 3 ≤ p} : Set ℕ).Infinite := by
      have : ({p | p.Prime ∧ (p + 2).Prime ∧ 3 ≤ p} : Set ℕ) = lowerTwins \ {2} := by
        ext p
        simp only [lowerTwins, Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, by omega⟩
        · rintro ⟨⟨h1, h2⟩, h3⟩
          refine ⟨h1, h2, ?_⟩
          have := h1.two_le
          rcases Nat.lt_or_ge p 3 with h | h
          · exfalso; apply h3; omega
          · exact h
      rw [this]
      exact hL.diff (Set.finite_singleton 2)
    have himg : (fun p => p * (p + 2)) '' {p | p.Prime ∧ (p + 2).Prime ∧ 3 ≤ p} ⊆ terms := by
      rintro n ⟨p, ⟨hp, hp2, hp3⟩, rfl⟩
      have hne : p ≠ p + 2 := by omega
      have hcop : Nat.Coprime p (p + 2) := (Nat.coprime_primes hp hp2).mpr hne
      have hpodd : Odd p := hp.odd_of_ne_two (by omega)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact (Nat.squarefree_mul_iff.mpr ⟨hcop, hp.squarefree, hp2.squarefree⟩)
      · exact hpodd.mul (hpodd.add_even even_two)
      · nlinarith
      · exact Nat.not_prime_mul (by omega) (by omega)
      · intro q hq hqd
        rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
        · have : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp h
          subst this
          left; exact ⟨hp, hp2⟩
        · have : q = p + 2 := (Nat.prime_dvd_prime_iff_eq hq hp2).mp h
          subst this
          right; exact ⟨p, ⟨hp, hp2⟩, rfl⟩
    apply Set.Infinite.mono himg
    apply Set.Infinite.image _ hL3
    intro x _ y _ hxy
    simp only at hxy
    nlinarith

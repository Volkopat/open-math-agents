import OMAReductions.R_Erdos889_erdos_889_variants_general_R1

-- Step Erdos889.erdos_889.variants.general.R1.H2: hypothesis H2 of reduction Erdos889.erdos_889.variants.general.R1
-- Credit: @JamesSlash. A prime factor p of n + k is counted by v n k exactly when k < p. So v (n + l) k and
-- v n (l + k) count prime factors of the same number n + l + k, above k and above l + k respectively, and they
-- differ by primes in Ioc k (l + k), a set with l elements.

theorem v_eq_card (n k : ℕ) :
    Erdos889.v n k = ((n + k).primeFactors.filter (fun p => k < p)).card := by
  unfold Erdos889.v
  congr 1
  apply Finset.filter_congr
  intro p hp
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  constructor
  · intro h
    by_contra hle
    rw [not_lt] at hle
    have hi : k - p ∈ Finset.range k := by
      rw [Finset.mem_range]; have := hpr.pos; omega
    apply h (k - p) hi
    have he : n + (k - p) = n + k - p := by omega
    rw [he]
    exact Nat.dvd_sub hpd (dvd_refl p)
  · intro hlt i hi hdi
    rw [Finset.mem_range] at hi
    have hsub : p ∣ (n + k) - (n + i) := Nat.dvd_sub hpd hdi
    have he : (n + k) - (n + i) = k - i := by omega
    rw [he] at hsub
    have := Nat.le_of_dvd (by omega) hsub
    omega

theorem OMA.solution : OMA.R_Erdos889_erdos_889_variants_general_R1.H2 := by
  intro l n k
  rw [v_eq_card, v_eq_card]
  have hN : n + (l + k) = n + l + k := by ring
  rw [hN]
  set S := (n + l + k).primeFactors
  have hsub : S.filter (fun p => k < p) ⊆ S.filter (fun p => l + k < p) ∪ Finset.Ioc k (l + k) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc]
    by_cases h : l + k < p
    · exact Or.inl ⟨hp.1, h⟩
    · exact Or.inr ⟨hp.2, by omega⟩
  calc (S.filter (fun p => k < p)).card
      ≤ (S.filter (fun p => l + k < p) ∪ Finset.Ioc k (l + k)).card := Finset.card_le_card hsub
    _ ≤ (S.filter (fun p => l + k < p)).card + (Finset.Ioc k (l + k)).card := Finset.card_union_le _ _
    _ = (S.filter (fun p => l + k < p)).card + l := by rw [Nat.card_Ioc]; congr 1; omega

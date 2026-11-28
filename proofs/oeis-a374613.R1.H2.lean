import OMAReductions.R_oeis_a374613_R1

-- Proof of step H2 of reductions/oeis-a374613.R1.lean (elementary; does not use H1).
-- Credit: @m-miyawaki-m

theorem OMA.solution : OMA.R_oeis_a374613_R1.H2 := by
  intro m hm
  have hinf : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOfPred_prime
  have hm0 : Nat.nth Nat.Prime m ≡ 1 [MOD 15] :=
    hm _ (Finset.mem_image.2 ⟨m, Finset.mem_Ico.2 ⟨le_refl _, by omega⟩, rfl⟩)
  have hm1 : Nat.nth Nat.Prime (m + 1) ≡ 1 [MOD 15] :=
    hm _ (Finset.mem_image.2 ⟨m + 1, Finset.mem_Ico.2 ⟨by omega, by omega⟩, rfl⟩)
  have hlt : Nat.nth Nat.Prime m < Nat.nth Nat.Prime (m + 1) :=
    Nat.nth_strictMono hinf (by omega)
  have hge : 2 < Nat.nth Nat.Prime m + Nat.nth Nat.Prime (m + 1) := by
    have := (Nat.nth_mem_of_infinite hinf m).two_le
    omega
  have hdvd : 3 ∣ 2 * (Nat.nth Nat.Prime m + Nat.nth Nat.Prime (m + 1)) - 1 ∧
      5 ∣ 2 * (Nat.nth Nat.Prime m + Nat.nth Nat.Prime (m + 1)) + 1 := by
    unfold Nat.ModEq at hm0 hm1
    omega
  refine ⟨Nat.nth Nat.Prime m, rfl, Nat.nth_mem_of_infinite hinf m, Nat.nth Nat.Prime (m + 1),
    Nat.nth_mem_of_infinite hinf (m + 1), hlt, ?_, ?_, ?_⟩
  · intro r hr1 hr2 hrp
    obtain ⟨n, rfl⟩ := Nat.subset_range_nth hrp
    have hmn : m < n := (Nat.nth_lt_nth hinf).mp hr1
    have hnm : n < m + 1 := (Nat.nth_lt_nth hinf).mp hr2
    omega
  · intro hp
    have := hp.eq_one_or_self_of_dvd 3 hdvd.1
    omega
  · intro hp
    have := hp.eq_one_or_self_of_dvd 5 hdvd.2
    omega

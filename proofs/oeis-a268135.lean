import OMAStatements.S_oeis_a268135

namespace OMA.S_oeis_a268135

/-- If the low block fits in `l` places, its digits add independently of
the higher block. -/
private theorem sumBlocks {l low high : ℕ} (h : (Nat.digits 10 low).length ≤ l) (hp : 0 < high) :
    digitSum (low + 10 ^ l * high) = digitSum low + digitSum high := by
  obtain ⟨z, rfl⟩ := Nat.exists_eq_add_of_le h
  have heq := Nat.digits_append_zeroes_append_digits (b := 10) (k := z) (n := low) (by decide) hp
  simpa [digitSum] using congrArg List.sum heq.symm

private theorem family (k : ℕ) :
    ∃ n ∈ properTerms, ¬ 10 ∣ n ∧ k < n := by
  let B := (10 : ℕ) ^ (12 + k)
  let n := 448999 + B * 448999
  have hn : 0 < n := by dsimp [n]; positivity
  have h6 : (Nat.digits 10 448999).length ≤ 12 + k := by
    have : (Nat.digits 10 448999).length = 6 := by decide +kernel
    omega
  have h12a : (Nat.digits 10 201600102001).length ≤ 12 + k := by
    have : (Nat.digits 10 201600102001).length = 12 := by decide +kernel
    omega
  have h12b : (Nat.digits 10 403200204002).length ≤ 12 + k := by
    have : (Nat.digits 10 403200204002).length = 12 := by decide +kernel
    omega
  have hs : digitSum n = 86 := by
    rw [show n = 448999 + 10 ^ (12+k) * 448999 by rfl, sumBlocks h6 (by decide)]
    decide +kernel
  have hsq : n^2 = 201600102001 + B * (403200204002 + B * 201600102001) := by
    dsimp only [n]
    ring
  have hs2 : digitSum (n^2) = 43 := by
    rw [hsq, show B = 10^(12+k) by rfl, sumBlocks h12a (by positivity),
      sumBlocks h12b (by decide)]
    decide +kernel
  refine ⟨n, ⟨hn, hs2 ▸ hs ▸ (by decide : 43 ∣ 86), hs2 ▸ hs ▸ (by decide : 43 < 86)⟩, ?_, ?_⟩
  · have hmod : n % 10 = 9 := by
      dsimp [n, B]
      rw [pow_add]
      norm_num [Nat.add_mod, Nat.mul_mod]
    exact fun h => by rw [Nat.mod_eq_zero_of_dvd h] at hmod; contradiction
  · have hk : k < (10 : ℕ) ^ k := Nat.lt_pow_self (by decide)
    have hB : 10 ^ k ≤ B := by dsimp [B]; rw [pow_add]; omega
    dsimp only [n]
    omega

end OMA.S_oeis_a268135

open OMA.S_oeis_a268135 in
theorem OMA.solution : type_of% @OMA.S_oeis_a268135.main := by
  have hinf : {n ∈ properTerms | ¬ 10 ∣ n}.Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro k
    obtain ⟨n, h, hlast, hlarge⟩ := family k
    exact ⟨n, ⟨h, hlast⟩, hlarge⟩
  exact ⟨hinf.mono (fun _ h => h.1), hinf⟩

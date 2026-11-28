import OMAReductions.R_RegularPrimes_not_isRegularPrime_37_R1

-- Original table certificate: @VinnyMo.
-- Generate the table from the recurrence and verify its entries in the kernel.

private def bernoulliTable : ℕ → List ℚ
  | 0 => []
  | n + 1 =>
    let row := bernoulliTable n
    row ++ [1 - ∑ k ∈ Finset.range n, n.choose k / (n - k + 1) * row[k]?.getD 0]

private def entry (n : ℕ) : ℚ := (bernoulliTable 33)[n]?.getD 0

private theorem recurrence : ∀ i : Fin 33, entry i = 1 -
    ∑ k ∈ Finset.range i.val, i.val.choose k / (i.val - k + 1) * entry k := by
  decide +kernel

private theorem correct (n : ℕ) (hn : n < 33) : bernoulli' n = entry n := by
  induction n using Nat.strong_induction_on
  rename_i n ih
  rw [bernoulli'_def, recurrence ⟨n, hn⟩]
  congr 1
  exact Finset.sum_congr rfl fun k hk => by
    rw [ih k (Finset.mem_range.mp hk) ((Finset.mem_range.mp hk).trans hn)]

theorem OMA.solution : OMA.R_RegularPrimes_not_isRegularPrime_37_R1.H1 := by
  change (37 : ℤ) ∣ (bernoulli' 32).num
  rw [correct 32 (by decide)]
  decide +kernel

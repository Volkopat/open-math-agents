import OMAReductions.R_Erdos409_erdos_409_variants_sigma_prime_termination_R1

/-! Every start from 2 through 300 reaches a prime within six divisor-sum steps. -/

private def divisorStep (n : ℕ) : ℕ :=
  if n = 0 then 0
  else (∏ p ∈ n.primeFactors, ∑ k ∈ Finset.range (n.factorization p + 1), p ^ k) - 1

private theorem divisorStep_eq : divisorStep = fun n => ArithmeticFunction.sigma 1 n - 1 := by
  funext n
  by_cases h : n = 0
  · subst n
    simp [divisorStep]
  · rw [divisorStep, if_neg h, ArithmeticFunction.sigma_one_apply, Nat.sum_divisors h]

private def reachesPrime : ℕ → ℕ → Bool
  | 0, n => decide n.Prime
  | fuel + 1, n => if n.Prime then true else reachesPrime fuel (divisorStep n)

private theorem reachesPrime_sound (fuel n : ℕ) (h : reachesPrime fuel n = true) :
    ∃ i ≤ fuel, (divisorStep^[i] n).Prime := by
  induction fuel generalizing n with
  | zero =>
      exact ⟨0, Nat.le_refl _, of_decide_eq_true h⟩
  | succ fuel ih =>
      by_cases hn : n.Prime
      · exact ⟨0, Nat.zero_le _, hn⟩
      · simp only [reachesPrime, if_neg hn] at h
        obtain ⟨i, hi, hp⟩ := ih _ h
        exact ⟨i + 1, Nat.succ_le_succ hi, by simpa only [Function.iterate_succ_apply] using hp⟩

-- The thirteen blocks cover all 299 starts from 2 through 300.
set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem checkedBlocks (block : Fin 13) :
    ∀ offset : Fin 23, reachesPrime 6 (2 + 23 * block.val + offset.val) = true := by
  fin_cases block <;> decide +kernel

theorem OMA.solution : OMA.R_Erdos409_erdos_409_variants_sigma_prime_termination_R1.H1 := by
  intro n hn hmax
  let delta := n - 2
  let block : Fin 13 := ⟨delta / 23, by dsimp [delta]; omega⟩
  let offset : Fin 23 := ⟨delta % 23, Nat.mod_lt _ (by decide)⟩
  have hn' : 2 + 23 * block.val + offset.val = n := by
    dsimp [block, offset, delta]
    omega
  obtain ⟨i, _, hi⟩ := reachesPrime_sound 6 n (hn' ▸ checkedBlocks block offset)
  exact ⟨i, by simpa only [divisorStep_eq] using hi⟩

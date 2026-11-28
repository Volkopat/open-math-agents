import OMAReductions.R_OeisA250131_conjecture_1_R1

/-! Verify the tabulated sieve range via a decidable bounded predicate. -/

open OeisA250131 (b sievedIndices)

private def finiteSieve (n : ℕ) : Prop :=
  1 ≤ n ∧ b n ≠ 1 ∧
    ∀ k : Fin n, 1 ≤ k.val → b k.val ≠ 1 → ¬ b k.val ∣ b n

private instance (n : ℕ) : Decidable (finiteSieve n) := by
  unfold finiteSieve
  infer_instance

private lemma finiteSieve_correct {n : ℕ} (hn : n ∈ sievedIndices) : finiteSieve n := by
  obtain ⟨hn, hb, hprev⟩ := hn
  exact ⟨hn, hb, fun k hk hbk => hprev k.val ⟨hk, k.isLt, hbk⟩⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
private lemma prime_check : ∀ i : Fin 80, finiteSieve i.val → (b i.val).Prime := by
  decide +kernel

theorem OMA.solution : OMA.R_OeisA250131_conjecture_1_R1.H1 := by
  intro n hn hs
  exact prime_check ⟨n, by omega⟩ (finiteSieve_correct hs)

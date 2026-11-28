import OMAStatements.S_oeis_a109864

/-! The one-digit counterexample is due to @agchua. Since 5 is an eligible prime,
the least eligible number is itself prime. -/

open OMA.S_oeis_a109864 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a109864.main) := by
  intro h
  have prime : (a 5).Prime := (Nat.sInf_mem
    (s := {p : ℕ | p.Prime ∧ IsPal p ∧ BeginsWith 5 p})
    ⟨5, by decide, by unfold IsPal; decide, List.prefix_refl _⟩).1
  rw [(h 5 (by decide)).2 ⟨by decide, by simp [BeginsWith]⟩] at prime
  exact Nat.not_prime_zero prime

import OMAStatements.S_mo_173510

/-!
Retains @MBimrose's arithmetic-progression counterexample from #29149.
The direct primality certificate replaces the bounded-divisor certificates in that
proof and @Genbox's pending #17817; the witness remains 2344 in 4 + 13ℕ.
-/

set_option maxRecDepth 100000 in
private theorem key : ∀ i : Fin 361,
    ¬ Nat.Prime (4 + i.val * 13) ∨ ¬ Nat.Prime (4 + (360 - i.val) * 13) := by
  simp_rw [Nat.prime_def_le_sqrt]
  decide +kernel

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_173510.main) := by
  intro h
  rcases h 4 13 (by norm_num) (by norm_num) (by norm_num) 180 (by decide) with
    hp | ⟨i, j, hi, hj, hs⟩
  · norm_num at hp
  · have hi' : i < 361 := by omega
    have hj' : j = 360 - i := by omega
    subst hj'
    exact (key ⟨i, hi'⟩).elim (fun hn => hn hi) (fun hn => hn hj)

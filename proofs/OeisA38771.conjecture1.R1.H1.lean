import OMAReductions.R_OeisA38771_conjecture1_R1

/-! Original proof by @ivillar. A smaller prime factor would divide both the primorial
and its sum with the composite. -/
theorem OMA.solution : OMA.R_OeisA38771_conjecture1_R1.H1 := by
  intro n
  let Q := ∏ i ∈ Finset.range n, Nat.nth Nat.Prime i
  let S := {c : ℕ | (1 < c ∧ ¬ c.Prime) ∧ (Q + c).Prime}
  have hn := OeisA38771.a_n_exists n
  change sInf S ≠ 0 at hn
  have hs : S.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h, Nat.sInf_empty] at hn
    exact hn rfl
  obtain ⟨⟨hc, hcomp⟩, hp⟩ := Nat.sInf_mem hs
  change (Nat.nth Nat.Prime n) ^ 2 ≤ sInf S
  let c := sInf S
  have hmin := Nat.minFac_prime (show c ≠ 1 by omega)
  refine (Nat.pow_le_pow_left ?_ 2).trans (Nat.minFac_sq_le_self (by omega) hcomp)
  by_contra! h
  have hi := (Nat.count_le_iff_le_nth Nat.infinite_setOfPred_prime).2 h
  rw [Nat.count_succ, if_pos hmin] at hi
  change Nat.count Nat.Prime c.minFac + 1 ≤ n at hi
  have hd : c.minFac ∣ Q := by
    rw [← Nat.nth_count hmin]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (by omega))
  have he := (Nat.prime_dvd_prime_iff_eq hmin hp).1 (dvd_add hd (Nat.minFac_dvd c))
  have hle := Nat.minFac_le (show 0 < c by omega)
  have hQ : 0 < Q := Finset.prod_pos fun i _ => (Nat.prime_nth_prime i).pos
  omega

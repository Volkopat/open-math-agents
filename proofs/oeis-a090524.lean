import OMAStatements.S_oeis_a090524

-- Proof (as noted in the OEIS entry A090523 by F. T. Adams-Watters): by Bertrand's postulate there
-- is a prime p with n!/4 < p <= 2*(n!/4), and then floor(n!/p) is 2 or 3, so the set defining
-- A090523(n) is nonempty and its infimum is a member.
-- The argument follows the accepted proof of the template entry OEIS A090526 (sInf membership).

namespace OMA.P_a090524

/-- Bertrand: for `N ≥ 4` some prime `p` in `(N/4, N/2]` gives `N / p ∈ {2, 3}`. -/
lemma exists_prime_quot (N : ℕ) (hN : 4 ≤ N) : ∃ p : ℕ, p.Prime ∧ (N / p).Prime := by
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (N / 4) (by omega)
  refine ⟨p, hp, ?_⟩
  have h2 : 2 ≤ N / p := (Nat.le_div_iff_mul_le hp.pos).2 (by omega)
  have h4 : N / p < 4 := (Nat.div_lt_iff_lt_mul hp.pos).2 (by omega)
  interval_cases h : N / p
  · exact Nat.prime_two
  · exact Nat.prime_three

end OMA.P_a090524

theorem OMA.solution : type_of% @OMA.S_oeis_a090524.main := by
  intro n hn
  have hN : 4 ≤ n.factorial :=
    le_trans (by decide : 4 ≤ Nat.factorial 3) (Nat.factorial_le hn)
  obtain ⟨p, hp, hq⟩ := OMA.P_a090524.exists_prime_quot _ hN
  have h : (OMA.S_oeis_a090524.a090523 n).Prime ∧
      (n.factorial / OMA.S_oeis_a090524.a090523 n).Prime :=
    Nat.sInf_mem (s := {p | p.Prime ∧ (n.factorial / p).Prime}) ⟨p, hp, hq⟩
  rw [OMA.S_oeis_a090524.a, if_neg h.1.ne_zero]
  exact h.2.ne_zero

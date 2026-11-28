import OMAReductions.R_Erdos448_erdos_448_variants_erdos_tenenbaum_R1_H2_R1

/-!
Proof of `OMA.R_Erdos448_erdos_448_variants_erdos_tenenbaum_R1_H2_R1.H3`: every `n > 0` is
`d * m` with `d, m` coprime, `m` squarefree and `d` powerful.

Induction over prime powers and coprime products (`Nat.recOnPosPrimePosCoprime`):
`p = 1 * p` and `p ^ k = p ^ k * 1` for `k ≥ 2`; for coprime `a = d₁ m₁`, `b = d₂ m₂`
take `d = d₁ d₂` and `m = m₁ m₂`.
-/

theorem OMA.solution : OMA.R_Erdos448_erdos_448_variants_erdos_tenenbaum_R1_H2_R1.H3 := by
  intro n
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro _
    by_cases hk1 : k = 1
    · subst hk1
      refine ⟨1, p, one_pos, by simp, Nat.coprime_one_left p, hp.squarefree, ?_⟩
      intro q hq hqd
      have := Nat.le_of_dvd one_pos hqd
      have := hq.two_le
      omega
    · refine ⟨p ^ k, 1, pow_pos hp.pos k, by simp, Nat.coprime_one_right _, squarefree_one, ?_⟩
      intro q hq hqd
      have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqd)
      subst hqp
      exact pow_dvd_pow q (by omega)
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | one =>
    intro _
    refine ⟨1, 1, one_pos, by simp, Nat.coprime_one_left 1, squarefree_one, ?_⟩
    intro q hq hqd
    have := Nat.le_of_dvd one_pos hqd
    have := hq.two_le
    omega
  | coprime a b ha hb hab iha ihb =>
    intro _
    obtain ⟨d₁, m₁, hd₁, rfl, hc₁, hs₁, hp₁⟩ := iha (by omega)
    obtain ⟨d₂, m₂, hd₂, rfl, hc₂, hs₂, hp₂⟩ := ihb (by omega)
    have h12 : Nat.Coprime d₁ m₂ :=
      (hab.coprime_dvd_right (dvd_mul_left m₂ d₂)).coprime_dvd_left (dvd_mul_right d₁ m₁)
    have h21 : Nat.Coprime d₂ m₁ :=
      (hab.symm.coprime_dvd_right (dvd_mul_left m₁ d₁)).coprime_dvd_left (dvd_mul_right d₂ m₂)
    have hmm : Nat.Coprime m₁ m₂ :=
      (hab.coprime_dvd_right (dvd_mul_left m₂ d₂)).coprime_dvd_left (dvd_mul_left m₁ d₁)
    refine ⟨d₁ * d₂, m₁ * m₂, Nat.mul_pos hd₁ hd₂, by ring, ?_, ?_, ?_⟩
    · exact Nat.Coprime.mul (Nat.Coprime.mul_right hc₁ h12) (Nat.Coprime.mul_right h21 hc₂)
    · exact (Nat.squarefree_mul hmm).mpr ⟨hs₁, hs₂⟩
    · intro q hq hqd
      rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
      · exact Dvd.dvd.mul_right (hp₁ q hq h) d₂
      · exact Dvd.dvd.mul_left (hp₂ q hq h) d₁

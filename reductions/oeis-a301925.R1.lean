import OMAStatements.S_oeis_a301925

-- Credit: @Pixelstorm44
namespace OMA.R_oeis_a301925_R1

/-- A progression with composite interiors and primitive endpoint forms. -/
def H1 : Prop :=
  ∀ d : ℕ, 0 < d → ∃ M a : ℕ, 0 < M ∧ M.Coprime a ∧ M.Coprime (a + d) ∧
    ∀ t i : ℕ, 0 < i → i < d → ¬ (a + M * t + i).Prime

/-- One occurrence of two simultaneous primes in a primitive progression with gap 4n.
For primes outside the modulus the two forms exclude at most two residues,
and modulo 2 their forbidden residues coincide. -/
def H2 : Prop :=
  ∀ n M a : ℕ, 0 < n → 0 < M → M.Coprime a → M.Coprime (a + 4 * n) →
    ∃ t : ℕ, (a + M * t).Prime ∧ (a + M * t + 4 * n).Prime

/-- Extend the progression one offset at a time. The new factor Q = M*d! + 1
is coprime to every positive difference of offsets up to d. -/
lemma coverPrefix (d k : ℕ) (hk : k < d) :
    ∃ M a : ℕ, 0 < M ∧ 2 ≤ a ∧ M.Coprime a ∧ M.Coprime (a + d) ∧
      ∀ t i : ℕ, 0 < i → i ≤ k → ¬ (a + M * t + i).Prime := by
  induction k with
  | zero => exact ⟨1, 2, by decide, by decide, by simp, by simp, by omega⟩
  | succ k ih =>
    obtain ⟨M, a, hM, ha, hL, hR, hold⟩ := ih (by omega)
    let i := k + 1
    let Q := M * d.factorial + 1
    let s := d.factorial * (a + i)
    let b := a + M * s
    have hi : 0 < i := by dsimp [i]; omega
    have hid : i < d := hk
    have hQ : 1 < Q := by
      have := Nat.mul_pos hM (Nat.factorial_pos d)
      dsimp [Q]; omega
    have hbi : b + i = Q * (a + i) := by dsimp [b, s, Q]; ring
    have hdiv : Q ∣ b + i := ⟨a + i, hbi⟩
    have large : ∀ p, p.Prime → p ∣ Q → d < p := by
      intro p hp hpQ
      by_contra! h
      have hf := Nat.dvd_factorial hp.pos h
      exact hp.not_dvd_one ((Nat.dvd_add_iff_right (dvd_mul_of_dvd_right hf M)).2 hpQ)
    have hQL : Q.Coprime b := by
      apply Nat.coprime_of_dvd
      intro p hp hpQ hpb
      have hpi : p ∣ i := (Nat.dvd_add_iff_right hpb).2 (hpQ.trans hdiv)
      have := Nat.le_of_dvd hi hpi
      have := large p hp hpQ
      omega
    have hQR : Q.Coprime (b + d) := by
      apply Nat.coprime_of_dvd
      intro p hp hpQ hpb
      have hdiff := Nat.dvd_sub hpb (hpQ.trans hdiv)
      rw [show b + d - (b + i) = d - i by omega] at hdiff
      have := Nat.le_of_dvd (by omega : 0 < d - i) hdiff
      have := large p hp hpQ
      omega
    refine ⟨M * Q, b, Nat.mul_pos hM (by omega), by dsimp [b]; omega,
      Nat.coprime_mul_iff_left.mpr ⟨?_, hQL⟩,
      Nat.coprime_mul_iff_left.mpr ⟨?_, hQR⟩, ?_⟩
    · simpa [b] using hL
    · rw [show b + d = (a + d) + M * s by dsimp [b]; omega]
      simpa using hR
    · intro t j hj hjle
      by_cases he : j = i
      · subst j
        have heq : b + M * Q * t + i = Q * (a + i + M * t) := by
          calc
            _ = (b + i) + M * Q * t := by omega
            _ = _ := by rw [hbi]; ring
        rw [heq]
        exact Nat.not_prime_mul (by omega) (by omega)
      · rw [show b + M * Q * t + j = a + M * (s + Q * t) + j by dsimp [b]; ring]
        exact hold _ _ hj (by dsimp [i] at he; omega)

theorem compositeInterior : H1 := by
  intro d hd
  obtain ⟨M, a, hM, _, hL, hR, h⟩ := coverPrefix d (d - 1) (by omega)
  exact ⟨M, a, hM, hL, hR, fun t i hi hid => h t i hi (by omega)⟩

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a301925.main := by
  intro cover pair n hn
  obtain ⟨M, a, hM, hL, hR, h⟩ := cover (4 * n) (by omega)
  obtain ⟨t, hp, hq⟩ := pair n M a hn hM hL hR
  refine ⟨a + M * t, hp, hq, ?_⟩
  intro m hm hm'
  have hc := h t (m - (a + M * t)) (by omega) (by omega)
  rwa [show a + M * t + (m - (a + M * t)) = m by omega] at hc

end OMA.R_oeis_a301925_R1

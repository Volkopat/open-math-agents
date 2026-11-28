import OMAStatements.S_oeis_a144751

namespace OddPrimeFactorCounterexample

open OMA.S_oeis_a144751

private def fast : ℕ → ℕ
  | 0 => 3
  | n + 1 => let x := fast n; 1 + x + x.minFac

private lemma odd_fast (n : ℕ) : Odd (fast n) := by
  induction n with
  | zero => exact ⟨1, by decide⟩
  | succ n ih =>
    have hf : Odd (fast n).minFac := Odd.of_dvd_nat ih (Nat.minFac_dvd _)
    rw [Nat.odd_iff] at ih hf ⊢
    simp only [fast]
    omega

private lemma fast_eq (n : ℕ) : fast n = b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hodd := odd_fast n
    rw [ih] at hodd
    have hnot : ¬ 2 ∣ b n := fun h ↦
      (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h)
    simp only [fast, b, lopf, ih, Nat.factorization_eq_zero_of_not_dvd hnot, pow_zero,
      Nat.div_one]

private lemma witness :
    (fast 42 : ℤ) ≠ 5 * (fast 36 : ℤ) - 4 * (fast 30 : ℤ) := by
  decide +kernel

theorem proof : type_of% @OMA.S_oeis_a144751.main := by
  intro h
  have h43 := h 43 (by decide)
  change (b 42 : ℤ) = 5 * (b 36 : ℤ) - 4 * (b 30 : ℤ) at h43
  rw [← fast_eq 42, ← fast_eq 36, ← fast_eq 30] at h43
  exact witness h43

end OddPrimeFactorCounterexample

theorem OMA.solution : type_of% @OMA.S_oeis_a144751.main := OddPrimeFactorCounterexample.proof

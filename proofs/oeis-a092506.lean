import OMAStatements.S_oeis_a092506
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a092506.main := by
  have E (m : ℕ) (hm : 0 < m) (he : Even m) : 2 * m.totient ≤ m ∧ (2 * m.totient = m → ∃ j, m = 2 ^ j) := by
    induction m using Nat.strong_induction_on with | _ m ih =>
    obtain ⟨r, rfl⟩ := he
    rcases Nat.even_or_odd r with h | h <;> rw [← two_mul]
    · rw [Nat.totient_two_mul_of_even h]
      obtain ⟨b, e⟩ := ih r (by omega) (by omega) h
      exact ⟨by omega, fun h => let ⟨j, hj⟩ := e (by omega); ⟨j + 1, by rw [hj]; ring⟩⟩
    · rw [Nat.totient_two_mul_of_odd h]
      refine ⟨by have := Nat.totient_le r; omega, fun e => ⟨1, ?_⟩⟩
      rcases Nat.lt_or_ge 1 r with h1 | h1
      · have := Nat.totient_lt r h1; omega
      · simp; omega
  ext x
  simp only [Set.mem_ofPred_eq]
  refine ⟨fun ⟨hx, h⟩ => ?_, ?_⟩
  · rcases Nat.lt_or_ge x 3 with hs | hs
    · interval_cases x
      · simp at h
      · exact ⟨Nat.prime_two, 0, rfl⟩
    rcases Nat.even_or_odd' x with ⟨r, rfl | rfl⟩
    · have := (E (2 * r) (by omega) (even_two_mul r)).1
      have := Nat.totient_lt (2 * r - 1) (by omega)
      omega
    · obtain ⟨b, e⟩ := E (2 * r) (by omega) (even_two_mul r)
      simp only [Nat.add_sub_cancel] at h
      have := Nat.totient_lt (2 * r + 1) (by omega)
      obtain ⟨j, hj⟩ := e (by omega)
      exact ⟨(Nat.totient_eq_iff_prime (by omega)).1 (by omega), j, by omega⟩
  · rintro ⟨hp, _ | j, rfl⟩
    · decide
    refine ⟨by simp, ?_⟩
    rw [Nat.totient_prime hp, Nat.add_sub_cancel, Nat.totient_prime_pow_succ Nat.prime_two, pow_succ]
    omega

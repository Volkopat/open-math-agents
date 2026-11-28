import OMAStatements.S_oeis_a045798

open OMA.S_oeis_a045798 in
theorem OMA.solution : type_of% @OMA.S_oeis_a045798.main := by
  let : DecidablePred oddish := fun k => inferInstanceAs (Decidable (_ ∧ _))
  have per (q k : ℕ) : oddish (20 * q + k) ↔ oddish k := by
    unfold oddish
    rw [show 20 * q + k = k + 2 * q * 10 by ring, Nat.coprime_add_mul_right_left,
      show (k + 2 * q * 10) / 10 % 10 % 2 = k / 10 % 10 % 2 by omega]
  have hi : (Set.ofPred oddish).Infinite :=
    Set.infinite_of_forall_exists_gt fun a => ⟨20 * a + 11, (per a 11).2 (by decide), by omega⟩
  have key (m : ℕ) : Nat.nth oddish (m + 4) = Nat.nth oddish m + 20 := by
    rw [show Nat.nth oddish m + 20 = 20 * 1 + Nat.nth oddish m by ring,
      ← Nat.nth_count ((per 1 _).2 (Nat.nth_mem_of_infinite hi m)), Nat.count_add]
    simp only [per, Nat.count_nth_of_infinite hi, show Nat.count oddish (20 * 1) = 4 by decide]
    ring_nf
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  simp only [a, show m + 6 - 1 = m + 1 + 4 by omega, show m + 1 + 4 - 1 = m + 4 by omega,
    show m + 6 - 4 - 1 = m + 1 by omega, show m + 6 - 5 - 1 = m by omega, key]
  push_cast; ring

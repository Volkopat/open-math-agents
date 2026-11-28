import OMAStatements.S_oeis_a131401
theorem OMA.solution : type_of% @OMA.S_oeis_a131401.main := by
  intro n hn
  unfold OMA.S_oeis_a131401.a
  constructor
  · intro h
    have hpos : 0 < Nat.fib n := Nat.fib_pos.2 (by omega)
    by_contra hne
    have hs := Nat.sInf_mem (s := {d : ℕ | d ∣ Nat.fib n ∧ ∀ m : ℕ, 1 ≤ m → m < n → ¬ d ∣ Nat.fib m})
      ⟨_, dvd_rfl, fun m hm1 hmn hdvd => by
        have := Nat.le_of_dvd (Nat.fib_pos.2 (by omega)) hdvd
        have : Nat.fib m < Nat.fib n := by
          rcases Nat.lt_or_ge m 2 with h2 | h2
          · obtain rfl : m = 1 := by omega
            have := Nat.fib_mono (show 3 ≤ n by omega)
            simp_all [Nat.fib_add_two]
          · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
            obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
            exact Nat.fib_add_two_strictMono (by omega)
        omega⟩
    rw [h] at hs
    exact hpos.ne' (zero_dvd_iff.1 hs.1)
  · rintro rfl
    rw [Nat.sInf_eq_zero]
    right
    ext d
    simp
    rintro rfl
    exact ⟨1, by simp⟩

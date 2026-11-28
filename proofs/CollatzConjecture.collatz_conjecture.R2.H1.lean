import OMAReductions.R_CollatzConjecture_collatz_conjecture_R2

open CollatzConjecture OMA.R_CollatzConjecture_collatz_conjecture_R2

def go (t : ℕ) : ℕ → ℕ → Bool
  | 0, x => Nat.blt x t
  | f + 1, x => Nat.blt x t || go t f (if x % 2 = 0 then x / 2 else 3 * x + 1)

lemma go_ok (t : ℕ) : ∀ f x, go t f x = true → ∃ m, collatzStep^[m] x < t
  | 0, x, h => ⟨0, by simpa [go, Nat.blt_eq] using h⟩
  | f + 1, x, h => by
    simp only [go, Bool.or_eq_true, Nat.blt_eq] at h
    rcases h with h | h
    · exact ⟨0, h⟩
    · obtain ⟨m, hm⟩ := go_ok t f _ h
      refine ⟨m + 1, ?_⟩
      rw [Function.iterate_succ_apply]
      by_cases e : x % 2 = 0
      · rw [collatzStep_even e]; simpa [e] using hm
      · rw [collatzStep_odd (by omega)]; simpa [e] using hm

def chk : ℕ → Bool
  | 0 => true
  | k + 1 => go (4 * k + 3) 132 (4 * k + 3) && chk k

lemma chk_ok : ∀ m, chk m = true → ∀ k < m, go (4 * k + 3) 132 (4 * k + 3) = true
  | 0, _, _, hk => by omega
  | m + 1, h, k, hk => by
    simp only [chk, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hk) with rfl | hlt
    · exact h.1
    · exact chk_ok m h.2 k hlt

theorem hall : chk 250 = true := by decide +kernel

theorem OMA.solution : OMA.R_CollatzConjecture_collatz_conjecture_R2.H1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro h0 h1
    rcases Nat.eq_or_lt_of_le h0 with rfl | hgt
    · exact ⟨0, rfl⟩
    · have ⟨m, hm⟩ : ∃ m, collatzStep^[m] n < n := by
        by_cases e : n % 2 = 0
        · exact ⟨1, descent_even hgt e⟩
        · by_cases q : n % 4 = 1
          · exact ⟨3, descent_mod4_1 hgt q⟩
          · have hk : 4 * (n / 4) + 3 = n := by omega
            simpa [hk] using go_ok _ 132 _ (chk_ok 250 hall (n / 4) (by omega))
      obtain ⟨r, hr⟩ := ih _ hm (iterate_pos h0 m) (by omega)
      exact ⟨r + m, by rw [Function.iterate_add_apply, hr]⟩

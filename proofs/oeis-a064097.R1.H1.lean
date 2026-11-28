import OMAReductions.R_oeis_a064097_R1

-- Step oeis-a064097.R1.H1: hypothesis H1 of reduction oeis-a064097.R1
-- Credit: @luciusacarr
-- H1 := ∀ a : ℕ → ℕ, a 1 = 0 → (∀ p : ℕ, p.Prime → a p = 1 + a (p - 1)) →     (∀ n m : ℕ, 1 < n → 1 < m → a (n * m) = a n + a m) →     ∀ n : ℕ, 1 < n → Nat.log 2 n ≤ a n

/-! By strong induction `n ≤ 2 ^ a n` for every `n ≥ 1`: for a prime `p`,
`p ≤ 2 (p - 1) ≤ 2 · 2 ^ a (p-1) = 2 ^ a p`; for `n = d m` with `1 < d, m < n` the bound
multiplies. Hence `n < 2 ^ (a n + 1)` and `Nat.log 2 n ≤ a n`. -/

theorem OMA.solution : OMA.R_oeis_a064097_R1.H1 := by
  intro a h1 hp hmul
  have key : ∀ n : ℕ, 1 ≤ n → n ≤ 2 ^ a n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro hn
    rcases Nat.eq_or_lt_of_le hn with rfl | hn1
    · rw [h1]; norm_num
    by_cases hpr : n.Prime
    · have hpre := ih (n - 1) (by omega) (by omega)
      rw [hp n hpr, pow_add]
      omega
    · obtain ⟨d, hd, hd1, hdn⟩ : ∃ d, d ∣ n ∧ 1 < d ∧ d < n := by
        refine ⟨n.minFac, Nat.minFac_dvd n, (Nat.minFac_prime (by omega)).one_lt, ?_⟩
        exact lt_of_le_of_ne (Nat.minFac_le (by omega))
          (fun h => hpr (h ▸ Nat.minFac_prime (by omega)))
      obtain ⟨m, rfl⟩ := hd
      have hm1 : 1 < m := by
        by_contra h
        push Not at h
        interval_cases m <;> omega
      have hmn : m < d * m := by nlinarith
      rw [hmul d m hd1 hm1, pow_add]
      exact Nat.mul_le_mul (ih d hdn (by omega)) (ih m hmn (by omega))
  intro n hn
  have hlt : n < 2 ^ (a n + 1) := by
    have := key n (by omega)
    rw [pow_succ]
    omega
  have := Nat.log_lt_of_lt_pow (by omega) hlt
  omega

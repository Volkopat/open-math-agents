import OMAStatements.S_oeis_a306362

-- Credit: @VirtualMe64
-- Bruno Berselli gave the factorization argument in OEIS A306362 in 2019.

open OMA.S_oeis_a306362

theorem OMA.solution : type_of% @OMA.S_oeis_a306362.main := by
  intro n hprime hne hlast
  rcases Nat.even_or_odd n with heven | hodd
  · have hform : b n = 1 + (n : ℤ) + 2 * (n : ℤ) ^ 2 := by
      rw [b, heven.neg_one_pow]
      omega
    rw [hform] at hlast
    have hfive : 1 + (n : ℤ) + 2 * (n : ℤ) ^ 2 ≡ 3 [ZMOD 5] :=
      Int.ModEq.of_dvd (by decide : (5 : ℤ) ∣ 10)
        (show 1 + (n : ℤ) + 2 * (n : ℤ) ^ 2 ≡ 3 [ZMOD 10] from hlast)
    have hr := Int.mod_modEq (n : ℤ) 5
    have exclude (r : ℤ) (hr0 : 0 ≤ r) (hr5 : r < 5) :
        ¬ (1 + r + 2 * r ^ 2 ≡ 3 [ZMOD 5]) := by
      interval_cases r <;> decide
    exact exclude _ (by omega) (by omega)
      (((hr.add_left 1).add ((hr.pow 2).mul_left 2)).trans hfive)
  · have hform : b n = (n : ℤ) * (2 * n + 1) := by
      rw [b, hodd.neg_one_pow]
      have hnum : 1 + (-1 : ℤ) + 2 * n + 4 * (n : ℤ) ^ 2 =
          (n * (2 * n + 1) : ℤ) * 2 := by ring
      rw [hnum]
      simp
    have hn1 : n ≠ 1 := by
      rintro rfl
      exact hne (by decide)
    have hn0 := hodd.pos
    rw [hform, prime_mul_iff] at hprime
    rcases hprime with ⟨_, hunit⟩ | ⟨hunit, _⟩ <;>
      rw [Int.isUnit_iff] at hunit <;> omega

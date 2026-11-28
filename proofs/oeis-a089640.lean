import OMAStatements.S_oeis_a089640

namespace OMA.S_oeis_a089640

open PowerSeries



theorem recurrence (n : ℕ) (hn : 5 < n) : a n = a (n - 3) + 2 * a (n - 4) + a (n - 5) := by
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 6 := ⟨n - 6, by omega⟩
  show ways (r + 6 - 1) true = ways (r + 6 - 3 - 1) true + 2 * ways (r + 6 - 4 - 1) true +
    ways (r + 6 - 5 - 1) true
  rw [show r + 6 - 1 = r + 2 + 3 by omega, show r + 6 - 3 - 1 = r + 2 by omega,
    show r + 6 - 4 - 1 = r + 1 by omega, show r + 6 - 5 - 1 = r by omega]
  rw [ways, show r + 2 + 2 = r + 1 + 3 by omega, ways, show r + 2 + 1 = r + 3 by omega, ways]
  ring

theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) *
    (X ^ 5 + 2 * X ^ 4 + X ^ 3 - 1) = X * (-X ^ 2 - X - 1) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (X ^ 5 + 2 * X ^ 4 + X ^ 3 - 1) =
      A * X ^ 5 + C 2 * (A * X ^ 4) + A * X ^ 3 - A := by
    rw [map_ofNat]
    ring
  have e2 : (X : ℤ⟦X⟧) * (-X ^ 2 - X - 1) = -X ^ 3 - X ^ 2 - X ^ 1 := by ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_X_pow, coeff_mul_X_pow', hc]
  rcases Nat.lt_or_ge n 6 with hn | hn
  · interval_cases n <;> decide
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    have h := recurrence (m + 6) (by omega)
    simp only [show m + 6 - 5 = m + 1 by omega, show m + 6 - 4 = m + 2 by omega,
      show m + 6 - 3 = m + 3 by omega, show ¬ m + 6 = 0 by omega, show ¬ m + 1 = 0 by omega,
      show ¬ m + 2 = 0 by omega, show ¬ m + 3 = 0 by omega, show 5 ≤ m + 6 by omega,
      show 4 ≤ m + 6 by omega, show 3 ≤ m + 6 by omega, show ¬ m + 6 = 3 by omega,
      show ¬ m + 6 = 2 by omega, show ¬ m + 6 = 1 by omega, if_true, if_false] at h ⊢
    rw [h]
    push_cast
    ring

/-- Wu's conjectures: the recurrence for n > 5 and the generating function. -/
theorem conjecture :
    (∀ n : ℕ, 5 < n → a n = a (n - 3) + 2 * a (n - 4) + a (n - 5)) ∧
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (X ^ 5 + 2 * X ^ 4 + X ^ 3 - 1) =
        X * (-X ^ 2 - X - 1) :=
  ⟨recurrence, gf⟩

end OMA.S_oeis_a089640

theorem OMA.solution : type_of% @OMA.S_oeis_a089640.main :=
  OMA.S_oeis_a089640.conjecture

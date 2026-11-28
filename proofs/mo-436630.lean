import OMAStatements.S_mo_436630

-- Problem: mo-436630, values of the canonical square root a -> a^((p+1)/4) modulo a prime
-- p = 3 (mod 4) on powers of a primitive root g.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Write p = 4m + 3, so (p + 1)/4 = m + 1 and p - 1 = 4m + 2. Since g has order 4m + 2,
-- g^(4m+2) = 1 and g^(2m+1) = -1 (its square is 1 and it is not 1). Then
--   (g^(4n))^(m+1)   = (g^(4m+2))^n g^(2n)        = g^(2n),
--   (g^(4n+2))^(m+1) = (g^(2m+1))^(2n+1) g^(2n+1) = -g^(2n+1),
--   (g^(2n))^(m+1)   = (g^(2m+1))^n g^n           = (-g)^n.

/-! The shared even-power argument and the order bound follow @etaubman’s
companion to #20883; the merged @ivillar proof #26422 supplies the arithmetic setup. -/

theorem OMA.solution : type_of% @OMA.S_mo_436630.main := by
  intro p _ hp g hg n _ _
  obtain ⟨m, hm⟩ : ∃ m, p = 4 * m + 3 := ⟨p / 4, by omega⟩
  subst hm
  have e1 : (4 * m + 3 + 1) / 4 = m + 1 := by omega
  have e2 : 4 * m + 3 - 1 = 4 * m + 2 := by omega
  rw [e2] at hg
  have hone : g ^ (4 * m + 2) = 1 := by
    rw [← hg]
    exact pow_orderOf_eq_one g
  have hneg : g ^ (2 * m + 1) = -1 := by
    have hsq : g ^ (2 * m + 1) * g ^ (2 * m + 1) = 1 := by
      rw [← pow_add, show 2 * m + 1 + (2 * m + 1) = 4 * m + 2 by omega]
      exact hone
    exact (mul_self_eq_one_iff.mp hsq).resolve_left
      (pow_ne_one_of_lt_orderOf (by omega) (by omega))
  unfold OMA.S_mo_436630.canonicalRoot
  rw [e1]
  have heven (k : ℕ) : (g ^ (2 * k)) ^ (m + 1) = (-g) ^ k := by
    calc (g ^ (2 * k)) ^ (m + 1) = (g ^ (2 * m + 1)) ^ k * g ^ k := by
          rw [← pow_mul, ← pow_mul, ← pow_add]
          congr 1
          ring
      _ = (-g) ^ k := by rw [hneg, neg_pow g k]
  refine ⟨?_, ?_, heven n⟩
  · simpa [show 4 * n = 2 * (2 * n) by omega, pow_mul] using heven (2 * n)
  · simpa [show 4 * n + 2 = 2 * (2 * n + 1) by omega, pow_add, pow_mul]
      using heven (2 * n + 1)

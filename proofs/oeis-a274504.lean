import OMAStatements.S_oeis_a274504

theorem OMA.solution : type_of% @OMA.S_oeis_a274504.main := by
  intro p _
  have hχ : (p : ZMod 8) = ((p % 56 : ℕ) : ZMod 8) := by
    rw [ZMod.natCast_eq_natCast_iff']
    omega
  have hJ : jacobiSym (p : ℤ) 7 = jacobiSym ((p % 56 : ℕ) : ℤ) 7 :=
    jacobiSym.mod_left' (by omega)
  rw [OMA.S_oeis_a274504.kronecker, Nat.factorization_def _ Nat.prime_two,
    show padicValNat 2 14 = 1 by decide +kernel, pow_one]
  change ZMod.χ₈ (p : ZMod 8) * jacobiSym (p : ℤ) 7 ≠ 1 ↔ _
  rw [hχ, hJ]
  have hr := Nat.mod_lt p (by decide : 0 < 56)
  generalize p % 56 = r at hr ⊢
  interval_cases r <;> simp <;> norm_num

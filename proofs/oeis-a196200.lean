import OMAStatements.S_oeis_a196200

-- Use L. Tóth's existing witness, 39270, directly.
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a196200.main) := by
  intro h
  have hi := h 39270 (by decide)
  have hp : OMA.S_oeis_a196200.psi 39270 = 2 ^ 9 * 3 ^ 5 := by decide +kernel
  rw [hp, Nat.totient_mul (by decide), Nat.totient_prime_pow (by decide) (by decide),
    Nat.totient_prime_pow (by decide) (by decide)] at hi
  norm_num at hi

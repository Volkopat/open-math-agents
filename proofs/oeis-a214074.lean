import OMAStatements.S_oeis_a214074

-- Counterexamples to Clark Kimberling's conjecture on OEIS A214074.
-- Credit: @anmolspace. The formal statement is due to @niclorusso.

-- At this counterexample, 487891 divides both powers minus three.
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a214074.main) := by
  intro conjecture
  have coprime : Int.gcd ((2 : ℤ) ^ 3438721 - 3) ((3 : ℤ) ^ 3438721 - 3) = 1 :=
    ((conjecture 3438721 (by decide)).2 ⟨10421, by decide, by decide⟩).1.2
  have h₂ : (2 : ℤ) ^ 3438721 % 487891 = 3 := by decide +kernel
  have h₃ : (3 : ℤ) ^ 3438721 % 487891 = 3 := by decide +kernel
  have factor := Int.dvd_coe_gcd
    (Int.dvd_self_sub_of_emod_eq h₂) (Int.dvd_self_sub_of_emod_eq h₃)
  rw [coprime] at factor
  exact (by decide : ¬ (487891 : ℤ) ∣ (1 : ℤ)) factor

import OMAStatements.S_oeis_a049094

-- Credit: @oh-meh
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a049094.main) := by
  intro h
  -- Vladeta Jovovic's 2005 counterexample in OEIS A049094.
  have coprime : Nat.Coprime 364 (2^364-1) := by decide
  have sqfree := (h 364 (by decide)).mpr coprime
  have hd : 1093*1093 ∣ (2^364-1 : ℕ) := by decide
  have hu : IsUnit (1093 : ℕ) := sqfree 1093 hd
  norm_num at hu

import OMAStatements.S_oeis_a257378

-- Problem: A257378: Smallest odd number k such that k*n*2^n+1 is a prime number.
-- Upstream: formal-conjectures statements/oeis-a257378.lean:0 (declaration OMA.S_oeis_a257378.main)
-- Original Lean proof: @datdzrgb.
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

theorem OMA.solution : type_of% @OMA.S_oeis_a257378.main := by
  intro n hn
  simp only [mul_assoc]
  have hNpos : 0 < n * 2 ^ n := by positivity
  have hNeven : 2 ∣ n * 2 ^ n := Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) n
  generalize n * 2 ^ n = N at hNpos hNeven ⊢
  have : NeZero (2 * N) := ⟨by omega⟩
  have hcop : Nat.Coprime (N + 1) (2 * N) :=
    ((Nat.prime_two.coprime_iff_not_dvd).2 (by omega)).symm.mul_right
      (Nat.coprime_self_add_left.2 (Nat.coprime_one_left N))
  have hu : IsUnit ((N + 1 : ℕ) : ZMod (2 * N)) := (ZMod.isUnit_iff_coprime _ _).mpr hcop
  obtain ⟨p, _, hpp, hmod⟩ := Nat.forall_exists_prime_gt_and_eq_mod hu 0
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (a := N + 1) (by omega)] at hmod
  have h := Nat.div_add_mod p (2 * N)
  rw [hmod] at h
  refine ⟨2 * (p / (2 * N)) + 1, ⟨_, rfl⟩, ?_⟩
  convert hpp using 1
  linarith

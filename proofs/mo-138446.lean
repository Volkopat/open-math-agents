import OMAStatements.S_mo_138446
import Mathlib

-- Problem: Question on x coordinates of Mordell Curves where $y^2=x^3+k$ and $k^2 = 1$ mod $24$
-- Upstream: formal-conjectures statements/mo-138446.lean:0 (declaration OMA.S_mo_138446.main)
-- Credit: @Ezekia1 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-- If `g * m` is squarefree, `g ∣ t` and `t` is coprime to `m`, then
`t ^ (φ (g * m) + 1) ≡ t` modulo `g * m`. -/
lemma OMA.nat_fix_aux (g m t : ℕ) (hsq : Squarefree (g * m)) (hg : g ∣ t)
    (htm : Nat.Coprime t m) : t ^ ((g * m).totient + 1) ≡ t [MOD g * m] := by
  have hcop : Nat.Coprime g m := Nat.coprime_of_squarefree_mul hsq
  have h2 : t ^ (g * m).totient ≡ 1 [MOD m] := by
    rw [Nat.totient_mul hcop, mul_comm, pow_mul]
    have h := (Nat.ModEq.pow_totient htm).pow g.totient
    simpa using h
  have h3 : t ^ ((g * m).totient + 1) ≡ t [MOD m] := by
    rw [pow_succ]
    simpa using h2.mul_right t
  have h4 : t ^ ((g * m).totient + 1) ≡ t [MOD g] := by
    have a1 : t ^ ((g * m).totient + 1) ≡ 0 [MOD g] :=
      (Nat.modEq_zero_iff_dvd).2 (dvd_pow hg (Nat.succ_ne_zero _))
    have a2 : t ≡ 0 [MOD g] := Nat.modEq_zero_iff_dvd.2 hg
    exact a1.trans a2.symm
  exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨h4, h3⟩

/-- For squarefree `n`, every natural `t` satisfies `t ^ (φ n + 1) ≡ t` modulo `n`. -/
lemma OMA.nat_fix (n t : ℕ) (hsq : Squarefree n) : t ^ (n.totient + 1) ≡ t [MOD n] := by
  obtain ⟨m, hm⟩ := Nat.gcd_dvd_right t n
  have hsq' : Squarefree (t.gcd n * m) := by
    rw [← hm]; exact hsq
  have hcop : Nat.Coprime (t.gcd n) m := Nat.coprime_of_squarefree_mul hsq'
  have hmn : m ∣ n := Dvd.intro_left _ hm.symm
  have htm : Nat.Coprime t m := by
    have h1 : Nat.gcd t m ∣ Nat.gcd (t.gcd n) m :=
      Nat.dvd_gcd (Nat.dvd_gcd (Nat.gcd_dvd_left t m) ((Nat.gcd_dvd_right t m).trans hmn))
        (Nat.gcd_dvd_right t m)
    rw [hcop.gcd_eq_one] at h1
    exact Nat.eq_one_of_dvd_one h1
  have key := OMA.nat_fix_aux (t.gcd n) m t hsq' (Nat.gcd_dvd_left t n) htm
  rw [← hm] at key
  exact key

/-- For squarefree `n`, every residue `u` satisfies `u ^ (φ n + 1) = u`. -/
lemma OMA.pow_fix (n : ℕ) (hsq : Squarefree n) (u : ZMod n) : u ^ (n.totient + 1) = u := by
  have : NeZero n := ⟨hsq.ne_zero⟩
  have h := (ZMod.natCast_eq_natCast_iff _ _ _).2 (OMA.nat_fix n u.val hsq)
  push_cast at h
  rw [ZMod.natCast_zmod_val] at h
  exact h

/-- In `ZMod n` with `n` odd and squarefree, `v ^ 2 = u ^ 3` forces `u` to be a square. -/
lemma OMA.key (n : ℕ) (hsq : Squarefree n) (hodd : n % 2 = 1) (u v : ZMod n)
    (h : v ^ 2 = u ^ 3) : IsSquare u := by
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · have h1 : n = 1 := by omega
    subst h1
    exact ⟨0, Subsingleton.elim _ _⟩
  · obtain ⟨j, hj⟩ := Nat.totient_even (show 2 < n by omega)
    have hpos : 0 < n.totient := Nat.totient_pos.2 (by omega)
    have hfix := OMA.pow_fix n hsq u
    refine ⟨v * u ^ (j - 1), ?_⟩
    have hE : n.totient + 1 = 3 + 2 * (j - 1) := by omega
    rw [hE] at hfix
    calc u = u ^ (3 + 2 * (j - 1)) := hfix.symm
      _ = u ^ 3 * (u ^ (j - 1)) ^ 2 := by ring
      _ = v ^ 2 * (u ^ (j - 1)) ^ 2 := by rw [h]
      _ = v * u ^ (j - 1) * (v * u ^ (j - 1)) := by ring

/-- Clearing denominators: `y * x.den ^ 2` is an integer. -/
lemma OMA.int_sq (x y : ℚ) (k : ℤ) (h : y ^ 2 = x ^ 3 + (k : ℚ)) :
    ∃ c : ℤ, c ^ 2 = x.num ^ 3 * (x.den : ℤ) + k * (x.den : ℤ) ^ 4 := by
  have hx : x * (x.den : ℚ) = (x.num : ℚ) := Rat.mul_den_eq_num x
  have hr : (y * (x.den : ℚ) ^ 2) ^ 2
      = ((x.num ^ 3 * (x.den : ℤ) + k * (x.den : ℤ) ^ 4 : ℤ) : ℚ) := by
    push_cast
    rw [← hx, mul_pow, h]
    ring
  by_contra hc
  have hirr : Irrational ((y * (x.den : ℚ) ^ 2 : ℚ) : ℝ) := by
    apply irrational_nrt_of_notint_nrt 2 (x.num ^ 3 * (x.den : ℤ) + k * (x.den : ℤ) ^ 4)
    · exact_mod_cast hr
    · rintro ⟨c, hc'⟩
      apply hc
      refine ⟨c, ?_⟩
      have e : (y * (x.den : ℚ) ^ 2 : ℚ) = (c : ℚ) := by exact_mod_cast hc'
      rw [e] at hr
      exact_mod_cast hr
    · norm_num
  exact Rat.not_irrational _ hirr

theorem OMA.solution : type_of% @OMA.S_mo_138446.main := by
  intro k x y hsq hmod heq hcop
  obtain ⟨c, hc⟩ := OMA.int_sq x y k heq
  have hodd : k.natAbs % 2 = 1 := by
    have h1 : k ^ 2 % 24 = 1 := hmod
    have h2 : k ^ 2 % 2 = 1 := by omega
    have h3 : k % 2 = 1 := by
      by_contra hne
      have h0 : k % 2 = 0 := by omega
      have hd : (2 : ℤ) ∣ k := Int.dvd_of_emod_eq_zero h0
      have hd2 : (2 : ℤ) ∣ k ^ 2 := dvd_pow hd two_ne_zero
      omega
    omega
  apply OMA.key k.natAbs hsq hodd _ ((c : ZMod k.natAbs) * ((x.den : ZMod k.natAbs)⁻¹) ^ 2)
  have hD : (x.den : ZMod k.natAbs) * (x.den : ZMod k.natAbs)⁻¹ = 1 :=
    ZMod.coe_mul_inv_eq_one x.den hcop
  have hk0 : ((k : ℤ) : ZMod k.natAbs) = 0 :=
    (CharP.intCast_eq_zero_iff (ZMod k.natAbs) k.natAbs k).2 (Int.natAbs_dvd.2 dvd_rfl)
  have hC : (c : ZMod k.natAbs) ^ 2
      = (x.num : ZMod k.natAbs) ^ 3 * (x.den : ZMod k.natAbs) := by
    have h5 := congrArg (Int.cast : ℤ → ZMod k.natAbs) hc
    push_cast at h5
    rw [h5, hk0]
    ring
  calc ((c : ZMod k.natAbs) * ((x.den : ZMod k.natAbs)⁻¹) ^ 2) ^ 2
      = (c : ZMod k.natAbs) ^ 2 * ((x.den : ZMod k.natAbs)⁻¹) ^ 4 := by ring
    _ = (x.num : ZMod k.natAbs) ^ 3 * ((x.den : ZMod k.natAbs)⁻¹) ^ 3
          * ((x.den : ZMod k.natAbs) * (x.den : ZMod k.natAbs)⁻¹) := by rw [hC]; ring
    _ = ((x.num : ZMod k.natAbs) * (x.den : ZMod k.natAbs)⁻¹) ^ 3 := by rw [hD]; ring

import OMAStatements.S_oeis_a182532

/-!
The unit-lifting argument is adapted from the accepted proof of A182206
(https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/9731).
-/

namespace A182532Proof

private theorem lift_base (C p g : ℕ) [NeZero C] (hp : p ∣ C) (hg : g.Coprime p)
    (hfermat : ∀ b : ℕ, b.Coprime C → b ^ (C - 1) ≡ 1 [MOD C]) :
    (g : ZMod p) ^ (C - 1) = 1 := by
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective (n := p) hp (ZMod.unitOfCoprime g hg)
  have hmod := (hfermat _ (ZMod.val_coe_unit_coprime u)).of_dvd hp
  rw [← ZMod.natCast_eq_natCast_iff] at hmod
  push_cast at hmod
  have hval : (((u : ZMod C).val : ℕ) : ZMod p) = g := by
    rw [ZMod.natCast_val]
    have h := congrArg (fun v : (ZMod p)ˣ => (v : ZMod p)) hu
    simpa [ZMod.unitsMap] using h
  rwa [hval] at hmod

private theorem dvd_exponent {M d k : ℕ} {g : ZMod M} (hd : 0 < d) (hg : g ^ d = 1)
    (hsmall : ∀ r < d, g ^ r = 1 → r = 0) (hk : g ^ k = 1) : d ∣ k := by
  have h : k = d * (k / d) + k % d := (Nat.div_add_mod k d).symm
  rw [h, pow_add, pow_mul, hg, one_pow, one_mul] at hk
  exact Nat.dvd_of_mod_eq_zero (hsmall _ (Nat.mod_lt _ hd) hk)

end A182532Proof

open A182532Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a182532.main := by
  intro C hC h7 h17
  obtain ⟨hC1, -, hfermat⟩ := hC
  have : NeZero C := ⟨by omega⟩
  have h3₇ : (3 : ZMod 7) ^ (C - 1) = 1 := lift_base C 7 3 h7 (by decide) hfermat
  have h3₁₇ : (3 : ZMod 17) ^ (C - 1) = 1 := lift_base C 17 3 h17 (by decide) hfermat
  have h6 : 6 ∣ C - 1 := dvd_exponent (by decide) (by decide) (by decide) h3₇
  have h16 : 16 ∣ C - 1 := dvd_exponent (by decide) (by decide) (by decide) h3₁₇
  have h48 : 48 ∣ C - 1 := Nat.lcm_dvd h6 h16
  obtain ⟨m, rfl⟩ : 7 * 17 ∣ C := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h7 h17
  have hm24 : m % 24 = 23 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> exact ⟨m / 120, by omega⟩

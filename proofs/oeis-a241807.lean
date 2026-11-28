import OMAStatements.S_oeis_a241807

open OMA.S_oeis_a241807

namespace NumeratorReduction

private def N (n : ℕ) := n^2+n+2
private def D (n : ℕ) := (n+1)*(n+2)*(n+3)
private def G (n : ℕ) := Nat.gcd (N n) (D n)

private theorem gcd_dvd_period (n : ℕ) : G n ∣ 16 := by
  have h₁ : G n ∣ D n * (n+2) := dvd_mul_of_dvd_left (Nat.gcd_dvd_right _ _) _
  have h₂ : G n ∣ D n * (n+2) + 16 := by
    rw [show D n * (n+2) + 16 = ((n+5)*(n+2)+4) * N n by unfold N D; ring]
    exact dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) _
  simpa using Nat.dvd_sub h₂ h₁

private theorem gcd_period (n : ℕ) : G n = G (n % 16) := by
  have hr : n ≡ n % 16 [MOD 16] := (Nat.mod_modEq n 16).symm
  have hN : N n ≡ N (n % 16) [MOD 16] :=
    ((hr.pow 2).add hr).add (Nat.ModEq.refl 2)
  have hD : D n ≡ D (n % 16) [MOD 16] :=
    ((hr.add (Nat.ModEq.refl 1)).mul (hr.add (Nat.ModEq.refl 2))).mul (hr.add (Nat.ModEq.refl 3))
  have transfer {d u v : ℕ} (hd : d ∣ 16) (hm : u ≡ v [MOD 16]) :
      d ∣ u → d ∣ v := fun hu =>
    Nat.modEq_zero_iff_dvd.mp ((hm.of_dvd hd).symm.trans (Nat.modEq_zero_iff_dvd.mpr hu))
  apply Nat.dvd_antisymm
  · exact Nat.dvd_gcd (transfer (gcd_dvd_period n) hN (Nat.gcd_dvd_left _ _))
      (transfer (gcd_dvd_period n) hD (Nat.gcd_dvd_right _ _))
  · exact Nat.dvd_gcd (transfer (gcd_dvd_period _) hN.symm (Nat.gcd_dvd_left _ _))
      (transfer (gcd_dvd_period _) hD.symm (Nat.gcd_dvd_right _ _))

theorem reduced (n : ℕ) : (a n : ℚ) = (A014206 n : ℚ) / (per n : ℚ) := by
  have hg : (G n : ℤ) = per n := by
    rw [gcd_period]
    have h : ∀ r : Fin 16, (G r.val : ℤ) =
        [2,4,4,2,2,16,4,2,2,4,4,2,2,8,4,2].getD r.val 0 := by decide
    exact h ⟨n % 16, Nat.mod_lt _ (by decide)⟩
  have hD : D n ≠ 0 := by unfold D; positivity
  have hc : c n = mkRat (N n : ℤ) (D n) := by
    rw [Rat.mkRat_eq_divInt, Rat.divInt_eq_div]
    simp [c, N, D]
  have hdvd : (G n : ℤ) ∣ (N n : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)
  rw [a, hc, Rat.num_mkRat, if_neg hD, Int.natAbs_natCast, Nat.gcd_comm]
  change (((N n : ℤ) / (G n : ℤ) : ℤ) : ℚ) = _
  rw [Int.cast_div_charZero hdvd, hg]
  congr 1

end NumeratorReduction

theorem OMA.solution : type_of% @OMA.S_oeis_a241807.main := NumeratorReduction.reduced
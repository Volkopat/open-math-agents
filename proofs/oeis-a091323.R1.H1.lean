import OMAReductions.R_oeis_a091323_R1
import Mathlib

theorem OMA.solution : OMA.R_oeis_a091323_R1.H1 := by
  rintro n L _ ⟨G, _, α, β, γ, hL⟩
  have hc : Nat.card G = 2 * n + 1 := by
    simpa using (Nat.card_congr α.symm)
  have hpow (g : G) : (g ^ 2) ^ (n + 1) = g := by
    rw [← pow_mul, show 2 * (n + 1) = Nat.card G + 1 by omega, pow_succ,
      pow_card_eq_one', one_mul]
  refine ⟨α.trans β.symm, ?_⟩
  intro i j hij
  simp only [hL, Equiv.trans_apply, Equiv.apply_symm_apply] at hij
  have hs : (α i)^2 = (α j)^2 := by simpa [pow_two] using γ.injective hij
  exact α.injective ((hpow (α i)).symm.trans ((congrArg (fun x : G => x ^ (n+1)) hs).trans (hpow (α j))))
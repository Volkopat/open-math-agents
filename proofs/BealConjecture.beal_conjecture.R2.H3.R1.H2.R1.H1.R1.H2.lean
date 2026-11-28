import OMAReductions.R_BealConjecture_beal_conjecture_R2_H3_R1_H2_R1_H1_R1

/-!
Proof of `OMA.R_BealConjecture_beal_conjecture_R2_H3_R1_H2_R1_H1_R1.H2`.
For `v ≥ 1` the cube `v ^ 3 + 1` lies strictly between the consecutive cubes `v ^ 3` and
`(v + 1) ^ 3 = v ^ 3 + 3 * v ^ 2 + 3 * v + 1`, so it is not a cube: `u ^ 3 = v ^ 3 + 1`
would force `v < u < v + 1`.
-/

namespace OMAProof.BealCubeGap

theorem not_cube_succ (u v : ℕ) (hv : v ≠ 0) : u ^ 3 ≠ v ^ 3 + 1 := by
  intro h
  have h1 : v < u := by
    by_contra hc
    push Not at hc
    have := Nat.pow_le_pow_left hc 3
    omega
  have h2 : u < v + 1 := by
    by_contra hc
    push Not at hc
    have h3 := Nat.pow_le_pow_left hc 3
    have h4 : (v + 1) ^ 3 = v ^ 3 + (3 * v ^ 2 + 3 * v) + 1 := by ring
    have h5 : 0 < 3 * v ^ 2 + 3 * v := by
      have := Nat.pos_of_ne_zero hv
      positivity
    omega
  omega

end OMAProof.BealCubeGap

open OMAProof.BealCubeGap in
theorem OMA.solution : OMA.R_BealConjecture_beal_conjecture_R2_H3_R1_H2_R1_H1_R1.H2 :=
  fun u v hv => not_cube_succ u v hv

import OMAReductions.R_oeis_a088112_R1

/-!
Proof of `OMA.R_oeis_a088112_R1.H1`.
Take `k = 4`: `4 ^ 2 = 16`, whose decimal reversal is the prime `61`.
-/

namespace OMAProof.OeisA088112Square

theorem rev_sixteen : OMA.S_oeis_a088112.rev (4 ^ 2) = 61 := by
  norm_num [OMA.S_oeis_a088112.rev, Nat.ofDigits_cons]

end OMAProof.OeisA088112Square

open OMAProof.OeisA088112Square in
theorem OMA.solution : OMA.R_oeis_a088112_R1.H1 :=
  ⟨4, by norm_num, by rw [rev_sixteen]; norm_num⟩

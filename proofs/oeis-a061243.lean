import OMAStatements.S_oeis_a061243
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a061243.main := by
  intro n hn
  have h (r : ℕ) : (∏ i ∈ Finset.Icc 1 r, (n + i)) ≡ r.factorial [MOD n] := by
    induction r with
    | zero => rfl
    | succ r ih =>
      rw [Finset.prod_Icc_succ_top (by omega), Nat.factorial_succ, mul_comm (r + 1)]
      exact ih.mul (Nat.add_mod_left n _)
  simp_rw [OMA.S_oeis_a061243.a, OMA.S_oeis_a061243.kempner, (h _).dvd_iff dvd_rfl]

import OMAStatements.S_oeis_a160191
import Mathlib

/-!
Credit: @ivillar
Proof: the Lucas numbers modulo 8 have period 12, so residue(n+12) = residue(n) and
earlierCount r (n+12) = earlierCount r n + c(r), with c(r) = earlierCount r 12. Hence
term(n+12) = term(n) + 8 c(residue n). Moreover c(residue(n+6)) = c(residue n) (checked on one
period). So f(n) = term(n+12) + term(n) - 2 term(n+6) satisfies f(n+12) = f(n), and f vanishes
on 0..11 by direct computation.
-/

namespace OMAA160191Helpers
open OMA.S_oeis_a160191

theorem pair_per (n : ℕ) : (lucasPair (n + 12)).1 % 8 = (lucasPair n).1 % 8 ∧
    (lucasPair (n + 12)).2 % 8 = (lucasPair n).2 % 8 := by
  induction n with
  | zero => decide
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    show (lucasPair (n + 12)).2 % 8 = (lucasPair n).2 % 8 ∧
      ((lucasPair (n + 12)).1 + (lucasPair (n + 12)).2) % 8 =
        ((lucasPair n).1 + (lucasPair n).2) % 8
    refine ⟨h2, ?_⟩
    omega

theorem res_per (n : ℕ) : residue (n + 12) = residue n := (pair_per n).1

theorem res_per' (q i : ℕ) : residue (12 * q + i) = residue i := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show 12 * (q + 1) + i = (12 * q + i) + 12 by ring, res_per, ih]

theorem count_per (r n : ℕ) : earlierCount r (n + 12) = earlierCount r n + earlierCount r 12 := by
  induction n with
  | zero => simp [earlierCount]
  | succ n ih =>
    show earlierCount r (n + 12) + (if residue (n + 12) = r then 1 else 0) =
      earlierCount r n + (if residue n = r then 1 else 0) + earlierCount r 12
    rw [ih, res_per]
    ring

theorem term_per (n : ℕ) : term (n + 12) = term n + 8 * earlierCount (residue n) 12 := by
  unfold term
  rw [res_per, count_per]
  ring

theorem c_half (n : ℕ) : earlierCount (residue (n + 6)) 12 = earlierCount (residue n) 12 := by
  obtain ⟨q, i, hi, rfl⟩ : ∃ q i, i < 12 ∧ n = 12 * q + i :=
    ⟨n / 12, n % 12, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 12).symm⟩
  rw [show 12 * q + i + 6 = 12 * q + (i + 6) by ring, res_per', res_per']
  interval_cases i <;> decide

end OMAA160191Helpers

open OMAA160191Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a160191.main := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 12 with h | h
    · interval_cases n <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
      have hm := ih m (by omega)
      have t1 : OMA.S_oeis_a160191.term (m + 12 + 12) = OMA.S_oeis_a160191.term (m + 12) +
          8 * OMA.S_oeis_a160191.earlierCount (OMA.S_oeis_a160191.residue (m + 12)) 12 :=
        term_per (m + 12)
      have t2 : OMA.S_oeis_a160191.term (m + 12 + 6) = OMA.S_oeis_a160191.term (m + 6) +
          8 * OMA.S_oeis_a160191.earlierCount (OMA.S_oeis_a160191.residue (m + 6)) 12 := by
        rw [show m + 12 + 6 = (m + 6) + 12 by ring]
        exact term_per (m + 6)
      have t3 := term_per m
      have c1 := c_half m
      rw [res_per] at t1
      rw [t1, t2, t3, c1]
      push_cast
      linarith

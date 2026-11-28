import OMAStatements.S_oeis_a294646
import Mathlib

-- Problem: A294646: a(n) = (1/2)^(2*n) mod (2*n+1).
-- Upstream: formal-conjectures statements/oeis-a294646.lean:0 (declaration OMA.S_oeis_a294646.main)
-- Credit: @npnelson (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Disproof. The third clause fails at n = 9814447404 (the counterexample recorded in the site's
-- review of this problem): with m = 2 n + 1 = 19628894809 one has (2 n - 2) * 4 ^ n = 1 mod m.
-- The modular power is evaluated by repeated squaring (reduce_mod_char) in ZMod m.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a294646.main) := by
  intro h
  have h1 := (h 9814447404 (by norm_num)).2.2
  apply h1
  have key : (19628894806 : ZMod 19628894809) * 4 ^ 9814447404 = 1 := by reduce_mod_char
  have h2 : 19628894806 * 4 ^ 9814447404 ≡ 1 [MOD 19628894809] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    exact key
  have e1 : 2 * 9814447404 - 2 = 19628894806 := by norm_num
  have e2 : 2 * 9814447404 + 1 = 19628894809 := by norm_num
  rw [e1, e2]
  exact h2

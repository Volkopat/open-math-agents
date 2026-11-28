import OMAStatements.S_oeis_a377109
import Mathlib

-- The modulus-241 counterexample is from the existing disproof by @zarnab222-dev.
open OMA.S_oeis_a377109

private def residues (v : ℕ × ℕ × ℕ × ℕ) :=
  (v.1 % 241, v.2.1 % 241, v.2.2.1 % 241, v.2.2.2 % 241)

private def step : ℕ × ℕ × ℕ × ℕ → ℕ × ℕ × ℕ × ℕ
  | (a,b,c,d) => ((2*a+2*b+3*c)%241, (a+2*b+3*d)%241,
      (a+2*c+2*d)%241, (b+c+2*d)%241)

private lemma correct (n : ℕ) : step^[n] (1,0,0,0) = residues (coords n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, coords]
    obtain ⟨a,b,c,d⟩ := coords n
    simp [step, residues, Nat.add_mod, Nat.mul_mod]

set_option maxRecDepth 10000 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a377109.main) := by
  intro h
  obtain ⟨k,_,hk,_⟩ := h 241 (by decide)
  have hp : Function.IsPeriodicPt step 240 (1,0,0,0) := by decide +kernel
  have hz : ∀ i : Fin 240, (step^[i.val] (1,0,0,0)).1 ≠ 0 := by decide +kernel
  have hm := hz ⟨k 0 % 240, Nat.mod_lt _ (by decide)⟩
  rw [hp.iterate_mod_apply, correct] at hm
  exact hm (Nat.mod_eq_zero_of_dvd ((hk (k 0)).2 ⟨0,rfl⟩))

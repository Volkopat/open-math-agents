import OMAStatements.S_oeis_a071010
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.ZMod.Basic

open Finset ArithmeticFunction in
theorem OMA.solution : type_of% @OMA.S_oeis_a071010.main := by
  intro n hn
  obtain ⟨p, hp, h4, he⟩ : ∃ p ∈ n.primeFactors, p % 4 = 3 ∧ ¬ Even (padicValNat p n) := by
    by_contra! h; exact hn (Nat.eq_sq_add_sq_iff.2 h)
  obtain ⟨r, hr⟩ := Nat.not_even_iff_odd.1 (Nat.factorization_def n (Nat.prime_of_mem_primeFactors hp) ▸ he)
  rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul (Nat.mem_primeFactors.1 hp).2.2, ← mul_prod_erase _ _ hp,
    hr, ← ZMod.natCast_eq_zero_iff]
  have : (p : ZMod 4) = -1 := by rw [← ZMod.natCast_mod, h4]; rfl
  push_cast
  rw [this]
  simp [neg_one_geom_sum, show Even (2 * r + 1 + 1) from ⟨r + 1, by ring⟩]

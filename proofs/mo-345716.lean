import OMAStatements.S_mo_345716
import Mathlib

-- Problem: mo-345716, for arbitrarily large primes p there are a nonzero quadratic
-- x_1^2 + x_2^2 - c and a nonconstant linear polynomial over Z/p in two variables such that
-- every zero of the quadratic is a zero of the linear polynomial.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Take a prime p = 3 mod 4 above N (Dirichlet), c = 0, and the linear polynomial x_1. Since -1
-- is not a square mod p, the only zero of x_1^2 + x_2^2 is the origin, where x_1 vanishes.

namespace MO345716

theorem zero_of_sq (p : ℕ) [Fact p.Prime] (hp4 : p % 4 = 3) (a b : ZMod p)
    (h : a ^ 2 + b ^ 2 = 0) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · rw [hb] at h
    have ha : a = 0 := by simpa using h
    exact ⟨ha, hb⟩
  · exfalso
    have ha : a ^ 2 = -(b ^ 2) := by linear_combination h
    have hsq : IsSquare (-1 : ZMod p) := by
      refine ⟨a / b, ?_⟩
      rw [div_mul_div_comm, ← pow_two, ← pow_two, ha, neg_div, div_self (pow_ne_zero 2 hb)]
    exact (ZMod.exists_sq_eq_neg_one_iff.mp hsq) hp4

end MO345716

theorem OMA.solution : type_of% @OMA.S_mo_345716.main := by
  intro N
  obtain ⟨p, hpN, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq N (q := 4) (a := 3) (by norm_num) (by norm_num)
  have hp4 : p % 4 = 3 := hmod
  have hfact : Fact p.Prime := ⟨hp⟩
  refine ⟨p, 2, hp, hpN, le_refl 2, rfl, ?_⟩
  refine ⟨0, fun i => if i = 0 then 1 else 0, 0, ?_, ⟨0, by simp⟩, ?_⟩
  · intro h
    have h1 := congrArg
      (MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (1 : ZMod p) else 0)) h
    simp [OMA.S_mo_345716.quadratic, Fin.sum_univ_two] at h1
  · intro x hx
    have hx' : x 0 ^ 2 + x 1 ^ 2 = 0 := by
      simpa [OMA.S_mo_345716.quadratic, Fin.sum_univ_two] using hx
    obtain ⟨h0, h1⟩ := MO345716.zero_of_sq p hp4 (x 0) (x 1) hx'
    simp [OMA.S_mo_345716.linear, Fin.sum_univ_two, h0, h1]

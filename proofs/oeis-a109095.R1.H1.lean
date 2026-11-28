import OMAReductions.R_oeis_a109095_R1
import Mathlib

/-! Step oeis-a109095.R1.H1. From `N! = a! b!` we get `(b+1)(b+2)⋯N = a!`. If `N ≥ 2b` this
product has at least `a` factors, each larger than `a`, so `a! ≤ a^a < (b+1)^a ≤ (b+1)^(N-b)`,
a contradiction. If `N = b + 1` the product is just `N`. -/

namespace OMA.A109095H1

theorem main (N a b : ℕ) (ha : 2 ≤ a) (_haN : a < N) (hb : 2 ≤ b) (hbN : b < N)
    (h : Nat.factorial N = Nat.factorial a * Nat.factorial b) (hab : a ≤ b) :
    N < 2 * b ∧ (N = b + 1 → N = Nat.factorial a) := by
  have hasc : (b + 1).ascFactorial (N - b) = Nat.factorial a := by
    have e := Nat.factorial_mul_ascFactorial b (N - b)
    rw [Nat.add_sub_cancel' hbN.le, h, mul_comm] at e
    exact Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos b) e
  constructor
  · by_contra hge
    push Not at hge
    have h1 : (b + 1) ^ (N - b) ≤ Nat.factorial a := hasc ▸ Nat.pow_succ_le_ascFactorial (b + 1) (N - b)
    have h2 : Nat.factorial a ≤ a ^ a := Nat.factorial_le_pow a
    have h3 : a ^ a < (b + 1) ^ a := Nat.pow_lt_pow_left (by omega) (by omega)
    have h4 : (b + 1) ^ a ≤ (b + 1) ^ (N - b) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · intro hN
    rw [hN, Nat.add_sub_cancel_left] at hasc
    simp [Nat.ascFactorial] at hasc
    omega

end OMA.A109095H1

theorem OMA.solution : OMA.R_oeis_a109095_R1.H1 :=
  fun N a b ha haN hb hbN h hab => OMA.A109095H1.main N a b ha haN hb hbN h hab

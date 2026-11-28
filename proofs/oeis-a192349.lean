import OMAStatements.S_oeis_a192349
import Mathlib

/-!
Credit: @ivillar
Proof: write P_n = P1(n) x + P0(n) and Q_n = Q1(n) x + Q0(n) modulo g = x^2 - x - 1. Since
x (u x + v) = u x^2 + v x is congruent to (u + v) x + u, the recursion gives
P0(n+1) = P1 + Q1 + 3 Q0, P1(n+1) = P0 + P1 + Q0 + Q1 + 3 Q1, Q0(n+1) = P0 + Q1,
Q1(n+1) = P1 + Q0 + Q1 (each step is checked by exhibiting the quotient by g). This linear map
of Z^4 has characteristic polynomial t^4 - 2 t^3 - 8 t^2 - -4 t - -4 (with signs as in
the recurrence), so every coordinate satisfies the recurrence; this is checked by expanding four
steps symbolically.
-/

namespace OMAA192349Helpers
open Polynomial OMA.S_oeis_a192349

/-- One step of the remainders (P0, P1, Q0, Q1). -/
def stepF (s : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ :=
  (s.2.1 + s.2.2.2 + 3 * s.2.2.1, s.1 + s.2.1 + s.2.2.1 + s.2.2.2 + 3 * s.2.2.2,
    s.1 + s.2.2.2, s.2.1 + s.2.2.1 + s.2.2.2)

/-- The remainders (P0, P1, Q0, Q1) of (pq n) modulo x^2 - x - 1. -/
def st : ℕ → ℤ × ℤ × ℤ × ℤ
  | 0 => (1, 0, 0, 0)
  | n + 1 => stepF (st n)

def P0 (n : ℕ) : ℤ := (st n).1

def P1 (n : ℕ) : ℤ := (st n).2.1

def Q0 (n : ℕ) : ℤ := (st n).2.2.1

def Q1 (n : ℕ) : ℤ := (st n).2.2.2

theorem P0_succ (n : ℕ) : P0 (n + 1) = P1 n + Q1 n + 3 * Q0 n := rfl

theorem P1_succ (n : ℕ) : P1 (n + 1) = P0 n + P1 n + Q0 n + Q1 n + 3 * Q1 n := rfl

theorem Q0_succ (n : ℕ) : Q0 (n + 1) = P0 n + Q1 n := rfl

theorem Q1_succ (n : ℕ) : Q1 (n + 1) = P1 n + Q0 n + Q1 n := rfl

theorem hg : (X ^ 2 - X - 1 : ℤ[X]).Monic := by monicity!

theorem hdeg : (X ^ 2 - X - 1 : ℤ[X]).degree = 2 := by compute_degree!

theorem lin_rem (u v : ℤ) : (C v * X + C u) %ₘ (X ^ 2 - X - 1 : ℤ[X]) = C v * X + C u :=
  (modByMonic_eq_self_iff hg).mpr (lt_of_le_of_lt degree_linear_le (by rw [hdeg]; decide))

theorem R (n : ℕ) : (pq n).1 %ₘ (X ^ 2 - X - 1 : ℤ[X]) = C (P1 n) * X + C (P0 n) ∧
    (pq n).2 %ₘ (X ^ 2 - X - 1 : ℤ[X]) = C (Q1 n) * X + C (Q0 n) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · show (1 : ℤ[X]) %ₘ (X ^ 2 - X - 1 : ℤ[X]) = C (P1 0) * X + C (P0 0)
      rw [(modByMonic_eq_self_iff (p := (1 : ℤ[X])) hg).mpr (by rw [hdeg, degree_one]; decide)]
      simp [P0, P1, st]
    · show (0 : ℤ[X]) %ₘ (X ^ 2 - X - 1 : ℤ[X]) = C (Q1 0) * X + C (Q0 0)
      rw [zero_modByMonic]
      simp [Q0, Q1, st]
  | succ n ih =>
    obtain ⟨ihA, ihB⟩ := ih
    have hA := modByMonic_add_div (pq n).1 (X ^ 2 - X - 1 : ℤ[X])
    have hB := modByMonic_add_div (pq n).2 (X ^ 2 - X - 1 : ℤ[X])
    rw [ihA] at hA
    rw [ihB] at hB
    have e0 : C (P0 (n + 1)) = C (P1 n) + C (Q1 n) + 3 * C (Q0 n) := by
      rw [P0_succ]
      simp only [map_add, map_mul, map_ofNat]
    have e1 : C (P1 (n + 1)) = C (P0 n) + C (P1 n) + C (Q0 n) + C (Q1 n) + 3 * C (Q1 n) := by
      rw [P1_succ]
      simp only [map_add, map_mul, map_ofNat]
    have f0 : C (Q0 (n + 1)) = C (P0 n) + C (Q1 n) := by
      rw [Q0_succ]
      simp only [map_add]
    have f1 : C (Q1 (n + 1)) = C (P1 n) + C (Q0 n) + C (Q1 n) := by
      rw [Q1_succ]
      simp only [map_add]
    have dA : (X ^ 2 - X - 1 : ℤ[X]) ∣
        (pq (n + 1)).1 - (C (P1 (n + 1)) * X + C (P0 (n + 1))) := by
      refine ⟨X * ((pq n).1 /ₘ (X ^ 2 - X - 1)) + C (P1 n) +
        (X + 3) * ((pq n).2 /ₘ (X ^ 2 - X - 1)) + C (Q1 n), ?_⟩
      show X * (pq n).1 + (X + 3) * (pq n).2 - (C (P1 (n + 1)) * X + C (P0 (n + 1))) = _
      linear_combination (-X) * hA + (-(X + 3)) * hB + (-X) * e1 - e0
    have dB : (X ^ 2 - X - 1 : ℤ[X]) ∣
        (pq (n + 1)).2 - (C (Q1 (n + 1)) * X + C (Q0 (n + 1))) := by
      refine ⟨(pq n).1 /ₘ (X ^ 2 - X - 1) + X * ((pq n).2 /ₘ (X ^ 2 - X - 1)) + C (Q1 n), ?_⟩
      show (pq n).1 + X * (pq n).2 - (C (Q1 (n + 1)) * X + C (Q0 (n + 1))) = _
      linear_combination (-1 : ℤ[X]) * hA + (-X) * hB + (-X) * f1 - f0
    exact ⟨by rw [modByMonic_eq_of_dvd_sub hg dA, lin_rem],
      by rw [modByMonic_eq_of_dvd_sub hg dB, lin_rem]⟩

theorem iden (s : ℤ × ℤ × ℤ × ℤ) :
    (stepF (stepF (stepF (stepF s)))).2.1 = 2 * (stepF (stepF (stepF s))).2.1 +
      8 * (stepF (stepF s)).2.1 + (-4) * (stepF s).2.1 + (-4) * s.2.1 := by
  obtain ⟨p0, p1, q0, q1⟩ := s
  simp only [stepF]
  ring

theorem rec (m : ℕ) : P1 (m + 4) = 2 * P1 (m + 3) + 8 * P1 (m + 2) +
    (-4) * P1 (m + 1) + (-4) * P1 m :=
  iden (st m)

theorem a_eq (k : ℕ) : a (k + 1) = P1 k := by
  unfold a p
  rw [Nat.add_sub_cancel, (R k).1, coeff_add, coeff_C_mul_X, coeff_C]
  simp

end OMAA192349Helpers

open OMAA192349Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a192349.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  show OMA.S_oeis_a192349.a (m + 4 + 1) = 2 * OMA.S_oeis_a192349.a (m + 3 + 1) + 8 * OMA.S_oeis_a192349.a (m + 2 + 1) -
    4 * OMA.S_oeis_a192349.a (m + 1 + 1) - 4 * OMA.S_oeis_a192349.a (m + 1)
  rw [a_eq, a_eq, a_eq, a_eq, a_eq]
  have h : P1 (m + 4) = 2 * P1 (m + 3) + 8 * P1 (m + 2) +
      (-4) * P1 (m + 1) + (-4) * P1 m := rec m
  rw [h]
  ring

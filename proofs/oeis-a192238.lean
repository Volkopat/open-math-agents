import OMAStatements.S_oeis_a192238
import Mathlib

-- Proof of R. J. Mathar's conjecture in OEIS A192238 (statement by @ivillar).
-- Idea: if p(m-1,x) reduces to c + d*x, then (x+m)*(c + d*x) reduces to (m*c + d) + (c + (m+1)*d)*x
-- (use x^2 = x + 1). Eliminating d from c(m) = m*c(m-1) + d(m-1), d(m) = c(m-1) + (m+1)*d(m-1) gives
-- c(m+1) = 2(m+1)*c(m) - (m(m+1) - 1)*c(m-1) for m ≥ 2, which is the recurrence for n ≥ 4.

namespace OMAA192238Helpers

open Polynomial OMA.S_oeis_a192238

/-- Constant term and x-coefficient of the reduction of p(n,x). -/
def cd : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | 1 => (0, 1)
  | n + 2 => (((n : ℤ) + 2) * (cd (n + 1)).1 + (cd (n + 1)).2,
      (cd (n + 1)).1 + ((n : ℤ) + 3) * (cd (n + 1)).2)

theorem hM : (X ^ 2 - X - 1 : ℤ[X]).Monic := by monicity!

theorem dvd_step : ∀ n : ℕ, (X ^ 2 - X - 1 : ℤ[X]) ∣ p n - (C (cd n).2 * X + C (cd n).1)
  | 0 => by simp [p, cd]
  | 1 => by simp [p, cd]
  | n + 2 => by
    have h1 := dvd_step (n + 1)
    have e : p (n + 2) - (C (cd (n + 2)).2 * X + C (cd (n + 2)).1) =
        (X + ((n + 2 : ℕ) : ℤ[X])) * (p (n + 1) - (C (cd (n + 1)).2 * X + C (cd (n + 1)).1)) +
          (X ^ 2 - X - 1) * C (cd (n + 1)).2 := by
      simp only [p, cd, map_add, map_mul, map_natCast, map_ofNat, Nat.cast_add, Nat.cast_ofNat]
      push_cast
      ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_right h1 _) (dvd_mul_right _ _)

theorem reduce_eq (n : ℕ) : reduce (p n) = C (cd n).2 * X + C (cd n).1 := by
  unfold reduce
  rw [modByMonic_eq_of_dvd_sub hM (dvd_step n), (modByMonic_eq_self_iff hM).mpr]
  have h2 : (X ^ 2 - X - 1 : ℤ[X]).degree = 2 := by compute_degree!
  rw [h2]
  exact degree_linear_lt

theorem a_eq (n : ℕ) : a (n + 1) = (cd n).1 := by
  unfold a
  rw [Nat.add_sub_cancel, reduce_eq, coeff_add, coeff_C_mul, coeff_X_zero, coeff_C]
  simp

theorem rc (n : ℕ) : (cd (n + 2)).1 = ((n : ℤ) + 2) * (cd (n + 1)).1 + (cd (n + 1)).2 := by
  simp [cd]

theorem rd (n : ℕ) : (cd (n + 2)).2 = (cd (n + 1)).1 + ((n : ℤ) + 3) * (cd (n + 1)).2 := by
  simp [cd]

theorem c_rec (k : ℕ) : (cd (k + 3)).1 =
    2 * ((k : ℤ) + 3) * (cd (k + 2)).1 - (((k : ℤ) + 2) * ((k : ℤ) + 3) - 1) * (cd (k + 1)).1 := by
  have e1 : (cd (k + 3)).1 = (((k + 1 : ℕ) : ℤ) + 2) * (cd (k + 2)).1 + (cd (k + 2)).2 := rc (k + 1)
  have e2 := rd k
  have e3 := rc k
  push_cast at e1
  linear_combination e1 + e2 - ((k : ℤ) + 3) * e3

end OMAA192238Helpers

open Polynomial OMA.S_oeis_a192238 OMAA192238Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a192238.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  rw [show k + 4 - 1 = (k + 2) + 1 by omega, show k + 4 - 2 = (k + 1) + 1 by omega,
    show k + 4 = (k + 3) + 1 by omega, a_eq, a_eq, a_eq]
  have h := c_rec k
  push_cast
  linear_combination h

import OMAStatements.S_oeis_a200216
import Mathlib

-- Problem: A200216, the order-5 linear recurrence with coefficients 3461450947505 and
-- 6440022564931157490 for a(n) = 5^5 t(n)^2 - 3000 t(n) + 719.
-- Upstream: formal-conjectures statements/oeis-a200216.lean (declaration OMA.S_oeis_a200216.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the stated recurrence holds for n >= 6).
-- Proof: with u(j) = (-1)^(j+1) E(2j+1), where (682 + 61 sqrt 125)^k = E(k) + F(k) sqrt 125, one has
-- u(j+2) = -1860498 u(j+1) - u(j); a(j+1) is a quadratic in u(j), and the recurrence becomes a
-- polynomial identity in u(j), u(j+1).

namespace OMA.P_oeis_a200216

open OMA.S_oeis_a200216

theorem E_rec (k : ℕ) : (pw (k + 2)).1 = 1364 * (pw (k + 1)).1 + (pw k).1 := by
  have h1 : (pw (k + 2)).1 = 682 * (pw (k + 1)).1 + 125 * 61 * (pw (k + 1)).2 := rfl
  have h2 : (pw (k + 1)).2 = 61 * (pw k).1 + 682 * (pw k).2 := rfl
  have h3 : (pw (k + 1)).1 = 682 * (pw k).1 + 125 * 61 * (pw k).2 := rfl
  linear_combination h1 + 7625 * h2 - 682 * h3

theorem E4 (k : ℕ) : (pw (k + 4)).1 = 1860498 * (pw (k + 2)).1 - (pw k).1 := by
  have h2 : (pw (k + 4)).1 = 1364 * (pw (k + 3)).1 + (pw (k + 2)).1 := E_rec (k + 2)
  have h1 : (pw (k + 3)).1 = 1364 * (pw (k + 2)).1 + (pw (k + 1)).1 := E_rec (k + 1)
  have h0 : (pw (k + 2)).1 = 1364 * (pw (k + 1)).1 + (pw k).1 := E_rec k
  linear_combination h2 + 1364 * h1 - h0

/-- u(j) = (-1)^(j+1) E(2j+1), so that t(j+1) = (u(j) + 57)/125. -/
def u (j : ℕ) : ℚ := (-1) ^ (j + 1) * ((pw (2 * j + 1)).1 : ℚ)

theorem u_rec (j : ℕ) : u (j + 2) = -1860498 * u (j + 1) - u j := by
  have h : (pw (2 * j + 5)).1 = 1860498 * (pw (2 * j + 3)).1 - (pw (2 * j + 1)).1 :=
    E4 (2 * j + 1)
  simp only [u]
  rw [show 2 * (j + 2) + 1 = 2 * j + 5 by ring, show 2 * (j + 1) + 1 = 2 * j + 3 by ring, h]
  push_cast
  ring

theorem a_eq (j : ℕ) :
    a (j + 1) = 5 ^ 5 * ((u j + 57) / 125) ^ 2 - 3000 * ((u j + 57) / 125) + 719 := by
  unfold a t u
  rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega]

theorem main' : ∀ n : ℕ, 6 ≤ n →
    a n = 3461450947505 * a (n - 1) + 6440022564931157490 * a (n - 2)
      - 6440022564931157490 * a (n - 3) - 3461450947505 * a (n - 4) + a (n - 5) := by
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 6 := ⟨n - 6, by omega⟩
  rw [show j + 6 - 1 = j + 4 + 1 by omega, show j + 6 - 2 = j + 3 + 1 by omega,
    show j + 6 - 3 = j + 2 + 1 by omega, show j + 6 - 4 = j + 1 + 1 by omega,
    show j + 6 - 5 = j + 1 by omega, show j + 6 = j + 5 + 1 by omega]
  simp only [a_eq]
  have h2 : u (j + 2) = -1860498 * u (j + 1) - u j := u_rec j
  have h3 : u (j + 3) = -1860498 * u (j + 2) - u (j + 1) := u_rec (j + 1)
  have h4 : u (j + 4) = -1860498 * u (j + 3) - u (j + 2) := u_rec (j + 2)
  have h5 : u (j + 5) = -1860498 * u (j + 4) - u (j + 3) := u_rec (j + 3)
  rw [h5, h4, h3, h2]
  ring

end OMA.P_oeis_a200216

theorem OMA.solution : type_of% @OMA.S_oeis_a200216.main := OMA.P_oeis_a200216.main'

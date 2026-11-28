import OMAStatements.S_oeis_a268553
import Mathlib

/-!
The conditions a + b = a + c = b + c = 2n force a = b = c = n, so diagFactor n = (3n)!/(n!)^3 =: D n,
an exact quotient. From (3n + 3)! = (3n + 3)(3n + 2)(3n + 1)(3n)! and (n + 1)! = (n + 1) n! we get
(n + 1)^2 D(n + 1) = 3(3n + 2)(3n + 1) D(n); squaring gives the recurrence for a = D^2.
-/

namespace R268553
open OMA.S_oeis_a268553

def D (n : ℕ) : ℕ := (3 * n).factorial / (n.factorial * n.factorial * n.factorial)

theorem dvd3 (n : ℕ) : n.factorial * n.factorial * n.factorial ∣ (3 * n).factorial := by
  have h1 : n.factorial * n.factorial ∣ (n + n).factorial :=
    Nat.factorial_mul_factorial_dvd_factorial_add n n
  have h2 : (n + n).factorial * n.factorial ∣ (n + n + n).factorial :=
    Nat.factorial_mul_factorial_dvd_factorial_add (n + n) n
  rw [show 3 * n = n + n + n by ring]
  exact (mul_dvd_mul_right h1 n.factorial).trans h2

theorem diag_eq (n : ℕ) : diagFactor n = D n := by
  have hn : n < 2 * n + 1 := by omega
  have h : ∀ a b c : ℕ, (if a + b = 2 * n ∧ a + c = 2 * n ∧ b + c = 2 * n then
      (a + b + c).factorial / (a.factorial * b.factorial * c.factorial) else 0) =
      if c = n then (if b = n then (if a = n then D n else 0) else 0) else 0 := by
    intro a b c
    by_cases H : a = n ∧ b = n ∧ c = n
    · obtain ⟨ha, hb, hc⟩ := H
      have hc1 : a + b = 2 * n ∧ a + c = 2 * n ∧ b + c = 2 * n := by omega
      rw [if_pos hc1, if_pos hc, if_pos hb, if_pos ha, ha, hb, hc,
        show n + n + n = 3 * n by ring, D]
    · have hc1 : ¬ (a + b = 2 * n ∧ a + c = 2 * n ∧ b + c = 2 * n) := by omega
      rw [if_neg hc1]
      split_ifs <;> first | rfl | (exfalso; omega)
  unfold diagFactor
  simp only [h, Finset.sum_ite_eq', Finset.mem_range, hn, ↓reduceIte]

theorem key (m : ℕ) : (m + 1) ^ 2 * D (m + 1) = 3 * (3 * m + 2) * (3 * m + 1) * D m := by
  have h1 : D m * (m.factorial * m.factorial * m.factorial) = (3 * m).factorial :=
    Nat.div_mul_cancel (dvd3 m)
  have h2 : D (m + 1) * ((m + 1).factorial * (m + 1).factorial * (m + 1).factorial) =
      (3 * (m + 1)).factorial :=
    Nat.div_mul_cancel (dvd3 (m + 1))
  have hpos : 0 < (m + 1) * (m.factorial * m.factorial * m.factorial) := by positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc (m + 1) ^ 2 * D (m + 1) * ((m + 1) * (m.factorial * m.factorial * m.factorial))
      = D (m + 1) * ((m + 1).factorial * (m + 1).factorial * (m + 1).factorial) := by
        rw [Nat.factorial_succ]
        ring
    _ = (3 * (m + 1)).factorial := h2
    _ = (3 * m + 3) * (3 * m + 2) * (3 * m + 1) * (3 * m).factorial := by
        show (3 * m + 1 + 1 + 1).factorial = _
        rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
        ring
    _ = (3 * m + 3) * (3 * m + 2) * (3 * m + 1) *
        (D m * (m.factorial * m.factorial * m.factorial)) := by rw [h1]
    _ = 3 * (3 * m + 2) * (3 * m + 1) * D m *
        ((m + 1) * (m.factorial * m.factorial * m.factorial)) := by ring

end R268553

theorem OMA.solution : type_of% @OMA.S_oeis_a268553.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hd : ∀ k, OMA.S_oeis_a268553.diagFactor k = R268553.D k := R268553.diag_eq
  simp only [OMA.S_oeis_a268553.a268553, hd, Nat.add_sub_cancel]
  rw [show 3 * (m + 1) - 1 = 3 * m + 2 by omega, show 3 * (m + 1) - 2 = 3 * m + 1 by omega]
  have hk := R268553.key m
  calc (m + 1) ^ 4 * (R268553.D (m + 1) * R268553.D (m + 1))
      = ((m + 1) ^ 2 * R268553.D (m + 1)) ^ 2 := by ring
    _ = (3 * (3 * m + 2) * (3 * m + 1) * R268553.D m) ^ 2 := by rw [hk]
    _ = 9 * (3 * m + 2) ^ 2 * (3 * m + 1) ^ 2 * (R268553.D m * R268553.D m) := by ring

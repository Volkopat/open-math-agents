import OMAStatements.S_oeis_a164848
import Mathlib

-- Problem: A164848, the quotient A026741(n)/A051712(n+1) has period 24.
-- Upstream: formal-conjectures statements/oeis-a164848.lean (declaration OMA.S_oeis_a164848.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Proof: b(n+1) - b(n+2) = n / ((n+2)(n+3)(n+4)) and gcd(n, (n+2)(n+3)(n+4)) = gcd(n, 24), so
-- A051712(n+1) = n / gcd(n, 24) and the quotient equals gcd(n, 24) / gcd(n, 2), of period 24.

namespace OMA.P_oeis_a164848

open OMA.S_oeis_a164848

theorem diff_eq (n : ℕ) : b (n + 1) - b (n + 1 + 1) =
    ((n : ℤ) : ℚ) / ((((n + 2) * (n + 3) * (n + 4) : ℕ) : ℤ) : ℚ) := by
  unfold b
  push_cast
  field_simp
  ring

theorem num_eq (u v : ℕ) (hv : 0 < v) :
    ((((u : ℕ) : ℤ) : ℚ) / (((v : ℕ) : ℤ) : ℚ)).num = ((u / Nat.gcd u v : ℕ) : ℤ) := by
  have hg : 0 < Nat.gcd u v := Nat.gcd_pos_of_pos_right u hv
  have e1 : u = Nat.gcd u v * (u / Nat.gcd u v) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left u v)).symm
  have e2 : v = Nat.gcd u v * (v / Nat.gcd u v) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right u v)).symm
  have hcop := Nat.coprime_div_gcd_div_gcd hg
  generalize u / Nat.gcd u v = u' at *
  generalize v / Nat.gcd u v = v' at *
  generalize Nat.gcd u v = g at *
  subst e1 e2
  have hv' : 0 < v' := Nat.pos_of_ne_zero (by rintro rfl; simp at hv)
  have hq : ((((g * u' : ℕ) : ℤ) : ℚ) / (((g * v' : ℕ) : ℤ) : ℚ)) =
      (((u' : ℕ) : ℤ) : ℚ) / (((v' : ℕ) : ℤ) : ℚ) := by
    push_cast
    have : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
    field_simp
  rw [hq]
  exact Rat.num_div_eq_of_coprime (by exact_mod_cast hv') (by simpa using hcop)

theorem gcd24 (n : ℕ) : Nat.gcd n ((n + 2) * (n + 3) * (n + 4)) = Nat.gcd n 24 := by
  rw [show (n + 2) * (n + 3) * (n + 4) = 24 + (n ^ 2 + 9 * n + 26) * n by ring,
    Nat.gcd_add_mul_right_right]

theorem A051712_eq (n : ℕ) : A051712 (n + 1) = ((n / Nat.gcd n 24 : ℕ) : ℤ) := by
  unfold A051712
  rw [diff_eq, num_eq _ _ (by positivity), gcd24]

theorem a_eq (n : ℕ) (hn : 1 ≤ n) :
    a n = ((Nat.gcd n 24 / Nat.gcd n 2 : ℕ) : ℤ) := by
  unfold a A026741
  rw [A051712_eq]
  have h2 : Nat.gcd n 2 ∣ Nat.gcd n 24 :=
    Nat.dvd_gcd (Nat.gcd_dvd_left n 2) ((Nat.gcd_dvd_right n 2).trans (by norm_num))
  obtain ⟨c, hc⟩ := h2
  obtain ⟨u, hu⟩ := Nat.gcd_dvd_left n 24
  have hg2 : 0 < Nat.gcd n 2 := Nat.gcd_pos_of_pos_right n (by norm_num)
  have hg24 : 0 < Nat.gcd n 24 := Nat.gcd_pos_of_pos_right n (by norm_num)
  have hu0 : 0 < u := by
    rcases Nat.eq_zero_or_pos u with h | h
    · rw [h, mul_zero] at hu; omega
    · exact h
  have e1 : n / Nat.gcd n 24 = u :=
    Nat.div_eq_of_eq_mul_left hg24 (by rw [mul_comm]; exact hu)
  have e2 : n / Nat.gcd n 2 = c * u := by
    apply Nat.div_eq_of_eq_mul_left hg2
    calc n = Nat.gcd n 24 * u := hu
      _ = Nat.gcd n 2 * c * u := by rw [hc]
      _ = c * u * Nat.gcd n 2 := by ring
  have e3 : Nat.gcd n 24 / Nat.gcd n 2 = c := by
    rw [hc, Nat.mul_div_cancel_left _ hg2]
  rw [e1, e2, e3]
  push_cast
  exact Int.mul_ediv_cancel _ (by exact_mod_cast hu0.ne')

theorem main' : ∀ n : ℕ, 1 ≤ n → a (n + 24) = a n := by
  intro n hn
  rw [a_eq _ (by omega), a_eq _ hn, show n + 24 = n + 1 * 24 by ring, Nat.gcd_add_mul_right_left,
    show n + 1 * 24 = n + 12 * 2 by ring, Nat.gcd_add_mul_right_left]

end OMA.P_oeis_a164848

theorem OMA.solution : type_of% @OMA.S_oeis_a164848.main := OMA.P_oeis_a164848.main'

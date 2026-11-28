import OMAStatements.S_oeis_a034267

-- Problem: A034267: a(n) = f(n,n) where f is given in A034261.
-- Upstream: formal-conjectures statements/oeis-a034267.lean:0 (declaration OMA.S_oeis_a034267.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! With c(k) the central binomial coefficient binomial(2k, k) one has
(k+1) binomial(2k, k+1) = k c(k), so (k+1)(k+2) a(k) = k (k^2+k+1) c(k), and
(k+1) c(k+1) = 2 (2k+1) c(k). Multiplying the left side of the recurrence by (n-1) n (n+1) (n+2) and
substituting these relations gives zero. -/

namespace A034267Aux

open OMA.S_oeis_a034267

theorem cbQ (k : ℕ) : ((k : ℚ) + 1) * ((k + 1).centralBinom : ℚ) =
    2 * (2 * (k : ℚ) + 1) * (k.centralBinom : ℚ) := by
  have h := Nat.succ_mul_centralBinom_succ k
  exact_mod_cast h

theorem hb (k : ℕ) : (((2 * k).choose (k + 1) : ℕ) : ℚ) * ((k : ℚ) + 1) = (k.centralBinom : ℚ) * (k : ℚ) := by
  have h := Nat.choose_succ_right_eq (2 * k) k
  have e : 2 * k - k = k := by omega
  rw [e] at h
  have e2 : k.centralBinom = (2 * k).choose k := rfl
  rw [e2]
  exact_mod_cast h

theorem E (k : ℕ) : ((k : ℚ) + 1) * ((k : ℚ) + 2) * a k =
    (k : ℚ) * ((k : ℚ) ^ 2 + (k : ℚ) + 1) * (k.centralBinom : ℚ) := by
  have h2 : (k : ℚ) + 2 ≠ 0 := by positivity
  have h3 : a k * ((k : ℚ) + 2) = (((2 * k).choose (k + 1) : ℕ) : ℚ) * ((k : ℚ) ^ 2 + (k : ℚ) + 1) :=
    div_mul_cancel₀ _ h2
  linear_combination ((k : ℚ) + 1) * h3 + ((k : ℚ) ^ 2 + (k : ℚ) + 1) * hb k

end A034267Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a034267.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  have e1 : m + 1 + 1 - 1 = m + 1 := rfl
  have e2 : m + 1 + 1 - 2 = m := rfl
  rw [e1, e2]
  have E2 := A034267Aux.E (m + 1 + 1)
  have E1 := A034267Aux.E (m + 1)
  have E0 := A034267Aux.E m
  have h1 := A034267Aux.cbQ (m + 1)
  have h2 := A034267Aux.cbQ m
  push_cast at E2 E1 E0 h1 h2 ⊢
  have key : (((m : ℚ) + 1) * ((m : ℚ) + 2) * ((m : ℚ) + 3) * ((m : ℚ) + 4)) *
      (-(((m : ℚ) + 1 + 1 + 2) * (11 * ((m : ℚ) + 1 + 1) - 7)) * OMA.S_oeis_a034267.a (m + 1 + 1) +
        2 * (23 * ((m : ℚ) + 1 + 1) ^ 2 + 44 * ((m : ℚ) + 1 + 1) + 30) * OMA.S_oeis_a034267.a (m + 1) -
        4 * ((m : ℚ) + 1 + 1 + 5) * (2 * ((m : ℚ) + 1 + 1) - 3) * OMA.S_oeis_a034267.a m) = 0 := by
    linear_combination (-14 * ((m : ℚ) + 2) + 29 * ((m : ℚ) + 2) ^ 2 - 4 * ((m : ℚ) + 2) ^ 3 - 11 * ((m : ℚ) + 2) ^ 4) * E2 + (-120 - 116 * ((m : ℚ) + 2) + 56 * ((m : ℚ) + 2) ^ 2 + 134 * ((m : ℚ) + 2) ^ 3 + 46 * ((m : ℚ) + 2) ^ 4) * E1 + (120 + 124 * ((m : ℚ) + 2) - 40 * ((m : ℚ) + 2) ^ 2 - 52 * ((m : ℚ) + 2) ^ 3 - 8 * ((m : ℚ) + 2) ^ 4) * E0 +
      (-14 * ((m : ℚ) + 2) + 15 * ((m : ℚ) + 2) ^ 2 + 11 * ((m : ℚ) + 2) ^ 3 + 14 * ((m : ℚ) + 2) ^ 4 - 15 * ((m : ℚ) + 2) ^ 5 - 11 * ((m : ℚ) + 2) ^ 6) * h1 + (-120 - 24 * ((m : ℚ) + 2) + 110 * ((m : ℚ) + 2) ^ 2 - 18 * ((m : ℚ) + 2) ^ 3 - 28 * ((m : ℚ) + 2) ^ 4 + 6 * ((m : ℚ) + 2) ^ 5 + 2 * ((m : ℚ) + 2) ^ 6) * h2
  have hD : (((m : ℚ) + 1) * ((m : ℚ) + 2) * ((m : ℚ) + 3) * ((m : ℚ) + 4)) ≠ 0 := by positivity
  have h := (mul_eq_zero.mp key).resolve_left hD
  linear_combination h

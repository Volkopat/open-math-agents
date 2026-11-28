import OMAStatements.S_oeis_a242429

-- Problem: A242429: Length of longest chain of nonempty proper subsemigroups of the monoid of partial injective order-preserving functions of a chain with n elements.
-- Upstream: formal-conjectures statements/oeis-a242429.lean:0 (declaration OMA.S_oeis_a242429.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: with H(k) = binomial(2k,k)/2, k*H(k) = 2(2k-1)*H(k-1) for k >= 2; the operator kills
-- 3*2^(n-1) - n - 2 identically, and its H-part is a combination of four such relations.

open OMA.S_oeis_a242429 in
theorem OMA.solution : type_of% @OMA.S_oeis_a242429.main := by
  obtain ⟨H, hH⟩ : ∃ H : ℕ → ℤ, ∀ j : ℕ, H j = (((2 * j).choose j / 2 : ℕ) : ℤ) :=
    ⟨_, fun _ => rfl⟩
  have ha : ∀ j : ℕ, a (j + 1) = H (j + 1) + 3 * 2 ^ j - ((j : ℤ) + 1) - 2 := by
    intro j
    unfold a
    rw [← hH, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  have h2H : ∀ j : ℕ, 2 * H (j + 1) = ((2 * (j + 1)).choose (j + 1) : ℤ) := by
    intro j
    rw [hH]
    have hd : 2 ∣ (2 * (j + 1)).choose (j + 1) := by
      have h := Nat.two_dvd_centralBinom_succ j
      rwa [Nat.centralBinom_eq_two_mul_choose] at h
    exact_mod_cast Nat.mul_div_cancel' hd
  have hrel : ∀ j : ℕ, ((j : ℤ) + 2) * H (j + 2) = 2 * (2 * (j : ℤ) + 3) * H (j + 1) := by
    intro j
    have e := Nat.succ_mul_centralBinom_succ (j + 1)
    rw [show j + 1 + 1 = j + 2 by omega, Nat.centralBinom_eq_two_mul_choose,
      Nat.centralBinom_eq_two_mul_choose] at e
    have h1 := h2H j
    have h2 := h2H (j + 1)
    rw [show j + 1 + 1 = j + 2 by omega] at h2
    have e' : ((j : ℤ) + 2) * ((2 * (j + 2)).choose (j + 2) : ℤ)
        = 2 * (2 * ((j : ℤ) + 1) + 1) * ((2 * (j + 1)).choose (j + 1) : ℤ) := by
      exact_mod_cast e
    rw [← h1, ← h2] at e'
    have e'' : (2 : ℤ) * (((j : ℤ) + 2) * H (j + 2)) = 2 * (2 * (2 * (j : ℤ) + 3) * H (j + 1)) := by
      linear_combination e'
    exact mul_left_cancel₀ (by norm_num) e''
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have a5 := ha (m + 4)
  have a4 := ha (m + 3)
  have a3 := ha (m + 2)
  have a2 := ha (m + 1)
  have a1 := ha m
  have r4 := hrel (m + 3)
  have r3 := hrel (m + 2)
  have r2 := hrel (m + 1)
  have r1 := hrel m
  rw [show m + 4 + 1 = m + 5 by omega] at a5
  rw [show m + 3 + 1 = m + 4 by omega] at a4 r4
  rw [show m + 3 + 2 = m + 5 by omega] at r4
  rw [show m + 2 + 1 = m + 3 by omega] at a3 r3
  rw [show m + 2 + 2 = m + 4 by omega] at r3
  rw [show m + 1 + 1 = m + 2 by omega] at a2 r2
  rw [show m + 1 + 2 = m + 3 by omega] at r2
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega, a5, a4, a3, a2, a1]
  push_cast at r2 r3 r4 ⊢
  linear_combination (131 * ((m : ℤ) + 5) - 376) * r4 + 2 * (-301 * ((m : ℤ) + 5) + 809) * r3
    + (889 * ((m : ℤ) + 5) - 2172) * r2 + 2 * (-209 * ((m : ℤ) + 5) + 387) * r1

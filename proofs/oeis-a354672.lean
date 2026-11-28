import OMAStatements.S_oeis_a354672

-- Problem: A354672: Numbers x with property that x is not the smallest possible value in the Pellian equation x^2 - D*y^2 = 1 with D = squarefree part of (x^2 - 1).
-- Upstream: formal-conjectures statements/oeis-a354672.lean:0 (declaration OMA.S_oeis_a354672.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: for a solution a of a Pell equation the x-coordinates of the powers satisfy
-- x(a^(n+2)) = 2 x(a) x(a^(n+1)) - x(a^n), the Chebyshev recurrence, so x(a^n) = T_n(x(a)).
-- If x is a term, Mathlib's Pell theory gives a fundamental solution a1 with x = x(a1^n);
-- n = 0 gives x = 1 and n = 1 gives x = x(a1) <= X < x, so n >= 2 and x = T_n(k), k = x(a1) >= 2.
-- Conversely, if x = T_m(k), take the solution a = (k, 1) for d = k^2 - 1; then x = x(a^m), so
-- x^2 - 1 = (k^2 - 1) y^2; writing k^2 - 1 = t^2 D with D squarefree gives x^2 - 1 = D (t y)^2,
-- k^2 = D t^2 + 1, and the x-coordinates grow, so 1 < k < x.

namespace K11A354672

theorem T_rec (k : ℤ) (n : ℕ) :
    (Polynomial.Chebyshev.T ℤ ((n + 1 + 1 : ℕ) : ℤ)).eval k =
      2 * k * (Polynomial.Chebyshev.T ℤ ((n + 1 : ℕ) : ℤ)).eval k -
        (Polynomial.Chebyshev.T ℤ (n : ℤ)).eval k := by
  rw [show ((n + 1 + 1 : ℕ) : ℤ) = (n : ℤ) + 2 by omega,
    show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by omega, Polynomial.Chebyshev.T_add_two]
  simp

theorem key {d : ℤ} (a : Pell.Solution₁ d) (n : ℕ) :
    (a ^ (n + 1 + 1)).x = 2 * a.x * (a ^ (n + 1)).x - (a ^ n).x := by
  have e1 : a ^ (n + 1 + 1) = a ^ (n + 1) * a := pow_succ a (n + 1)
  have e2 : a ^ n = a ^ (n + 1) * a⁻¹ := by rw [pow_succ, mul_inv_cancel_right]
  rw [e1, e2, Pell.Solution₁.x_mul, Pell.Solution₁.x_mul, Pell.Solution₁.x_inv,
    Pell.Solution₁.y_inv]
  ring

theorem pow_x {d : ℤ} (a : Pell.Solution₁ d) (n : ℕ) :
    (a ^ n).x = (Polynomial.Chebyshev.T ℤ (n : ℤ)).eval a.x := by
  have h2 : ∀ j : ℕ, (a ^ j).x = (Polynomial.Chebyshev.T ℤ (j : ℤ)).eval a.x ∧
      (a ^ (j + 1)).x = (Polynomial.Chebyshev.T ℤ ((j + 1 : ℕ) : ℤ)).eval a.x := by
    intro j
    induction j with
    | zero => constructor <;> simp
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      rw [key a j, T_rec a.x j, ih.1, ih.2]
  exact (h2 n).1

end K11A354672

open OMA.S_oeis_a354672 in
theorem OMA.solution : type_of% @OMA.S_oeis_a354672.main := by
  intro x
  unfold OMA.S_oeis_a354672.IsTerm
  constructor
  · rintro ⟨hx2, D, s, -, hs, X, Y, hX1, hXx, hXY⟩
    have h1 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hxs : x ^ 2 = D * s ^ 2 + 1 := (Nat.sub_eq_iff_eq_add h1).mp hs
    have hc : (X : ℤ) ^ 2 - (D : ℤ) * (Y : ℤ) ^ 2 = 1 := by
      have h : ((X ^ 2 : ℕ) : ℤ) = ((D * Y ^ 2 + 1 : ℕ) : ℤ) := by rw [hXY]
      push_cast at h
      linarith
    have hb : (x : ℤ) ^ 2 - (D : ℤ) * (s : ℤ) ^ 2 = 1 := by
      have h : ((x ^ 2 : ℕ) : ℤ) = ((D * s ^ 2 + 1 : ℕ) : ℤ) := by rw [hxs]
      push_cast at h
      linarith
    have hc1 : 1 < (Pell.Solution₁.mk (X : ℤ) (Y : ℤ) hc).x := by
      rw [Pell.Solution₁.x_mk]
      exact_mod_cast hX1
    obtain ⟨a₁, ha₁⟩ := Pell.IsFundamental.exists_of_not_isSquare
      (Pell.Solution₁.d_pos_of_one_lt_x hc1) (Pell.Solution₁.d_nonsquare_of_one_lt_x hc1)
    have hbx : 0 < (Pell.Solution₁.mk (x : ℤ) (s : ℤ) hb).x := by
      rw [Pell.Solution₁.x_mk]
      exact_mod_cast (show 0 < x by omega)
    have hby : 0 ≤ (Pell.Solution₁.mk (x : ℤ) (s : ℤ) hb).y := by
      rw [Pell.Solution₁.y_mk]
      positivity
    obtain ⟨n, hn⟩ := ha₁.eq_pow_of_nonneg hbx hby
    have hxn : (x : ℤ) = (a₁ ^ n).x := by
      rw [← hn, Pell.Solution₁.x_mk]
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero, Pell.Solution₁.x_one] at hxn
      omega
    have hn1 : n ≠ 1 := by
      rintro rfl
      rw [pow_one] at hxn
      have hle := ha₁.x_le_x hc1
      rw [Pell.Solution₁.x_mk] at hle
      have hXx' : (X : ℤ) < x := by exact_mod_cast hXx
      linarith
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = a₁.x :=
      ⟨a₁.x.toNat, Int.toNat_of_nonneg (by linarith [ha₁.1])⟩
    have hk2 : 2 ≤ k := by
      have h := ha₁.1
      omega
    refine ⟨n, k, by omega, hk2, ?_⟩
    rw [hxn, K11A354672.pow_x, hk]
  · rintro ⟨m, k, hm, hk, hxk⟩
    have hprop : (k : ℤ) ^ 2 - ((k : ℤ) ^ 2 - 1) * 1 ^ 2 = 1 := by ring
    obtain ⟨a, ha⟩ : ∃ a : Pell.Solution₁ ((k : ℤ) ^ 2 - 1), a.x = k ∧ a.y = 1 :=
      ⟨Pell.Solution₁.mk (k : ℤ) 1 hprop, Pell.Solution₁.x_mk _ _ _, Pell.Solution₁.y_mk _ _ _⟩
    have hk' : (2 : ℤ) ≤ k := by exact_mod_cast hk
    have hgrow : ∀ j : ℕ, 1 ≤ (a ^ j).x ∧ (a ^ j).x < (a ^ (j + 1)).x := by
      intro j
      induction j with
      | zero =>
        rw [pow_zero, zero_add, pow_one, Pell.Solution₁.x_one, ha.1]
        constructor
        · exact le_refl _
        · linarith
      | succ j ih =>
        have h := K11A354672.key a j
        rw [ha.1] at h
        have hA : 1 ≤ (a ^ (j + 1)).x := by linarith [ih.1, ih.2]
        have hprod : 2 * (a ^ (j + 1)).x ≤ (k : ℤ) * (a ^ (j + 1)).x :=
          mul_le_mul_of_nonneg_right hk' (by linarith)
        refine ⟨hA, ?_⟩
        rw [h]
        linarith [ih.1, ih.2]
    have hbig : ∀ j : ℕ, (k : ℤ) < (a ^ (j + 2)).x := by
      intro j
      induction j with
      | zero =>
        have h := (hgrow 1).2
        rw [pow_one, ha.1] at h
        simpa using h
      | succ j ih =>
        have h := (hgrow (j + 2)).2
        rw [show j + 1 + 2 = j + 2 + 1 by omega]
        linarith
    have hxm : (a ^ m).x = (x : ℤ) := by
      rw [K11A354672.pow_x, ha.1, hxk]
    have hkx : k < x := by
      have h := hbig (m - 2)
      rw [show m - 2 + 2 = m by omega, hxm] at h
      exact_mod_cast h
    have hp := (a ^ m).prop
    rw [hxm] at hp
    obtain ⟨w, hw⟩ : ∃ w : ℕ, (w : ℤ) ^ 2 = (a ^ m).y ^ 2 :=
      ⟨(a ^ m).y.natAbs, Int.natAbs_pow_two _⟩
    obtain ⟨D, t, hDt, hD⟩ := Nat.sq_mul_squarefree (k ^ 2 - 1)
    have hk1 : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hx1 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hDtZ : (t : ℤ) ^ 2 * D = (k : ℤ) ^ 2 - 1 := by
      have h : ((t ^ 2 * D : ℕ) : ℤ) = ((k ^ 2 - 1 : ℕ) : ℤ) := by rw [hDt]
      rw [Nat.cast_sub hk1] at h
      push_cast at h
      linarith
    have hkt : k ^ 2 = D * t ^ 2 + 1 := by
      have h := (Nat.sub_eq_iff_eq_add hk1).mp hDt.symm
      rw [h]
      ring
    refine ⟨by omega, D, t * w, hD, ?_, k, t, by omega, hkx, hkt⟩
    have hZ : ((x ^ 2 - 1 : ℕ) : ℤ) = ((D * (t * w) ^ 2 : ℕ) : ℤ) := by
      rw [Nat.cast_sub hx1]
      push_cast
      linear_combination hp - (a ^ m).y ^ 2 * hDtZ - (D : ℤ) * (t : ℤ) ^ 2 * hw
    exact Nat.cast_inj.mp hZ

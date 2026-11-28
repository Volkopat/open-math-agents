import OMAStatements.S_oeis_a093726

-- Problem: A093726: Given the infinite continued fraction (1+i)+1/((1+i)+1/((1+i)+...)), where i is the square root of (-1), this is the numerator of the imaginary part of the convergents.
-- Upstream: formal-conjectures statements/oeis-a093726.lean:0 (declaration OMA.S_oeis_a093726.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: let U(0) = 0, U(1) = 1, U(n+2) = (1+i)U(n+1) + U(n) (P. Bala's Lucas sequence in
-- A138573), U(n) = X(n) + Y(n) i. Then c(n) = U(n+1)/U(n) by induction, so
-- Im c(n) = (Y(n+1)X(n) - X(n+1)Y(n))/(X(n)^2 + Y(n)^2). Both quadratic forms satisfy the
-- recurrence t^4 = 2t^3 + 2t^2 + 2t - 1 (a polynomial identity in X(n), Y(n), X(n+1), Y(n+1)),
-- and comparing four initial values gives X(n)^2 + Y(n)^2 = A138573(n) and
-- Y(n+1)X(n) - X(n+1)Y(n) = A317974(n+1). A138573 is nondecreasing with A138573(1) = 1, so
-- U(n) is nonzero for n >= 1.

namespace R10A093726

open OMA.S_oeis_a093726

/-- (X n, Y n), the real and imaginary parts of U n. -/
def P : ℕ → ℤ × ℤ
  | 0 => (0, 0)
  | 1 => (1, 0)
  | (n + 2) => ((P (n + 1)).1 - (P (n + 1)).2 + (P n).1, (P (n + 1)).1 + (P (n + 1)).2 + (P n).2)

def X (n : ℕ) : ℤ := (P n).1

def Y (n : ℕ) : ℤ := (P n).2

theorem X_rec (n : ℕ) : X (n + 2) = X (n + 1) - Y (n + 1) + X n := rfl

theorem Y_rec (n : ℕ) : Y (n + 2) = X (n + 1) + Y (n + 1) + Y n := rfl

theorem N_rec (n : ℕ) :
    X (n + 4) * X (n + 4) + Y (n + 4) * Y (n + 4) =
      2 * (X (n + 3) * X (n + 3) + Y (n + 3) * Y (n + 3))
      + 2 * (X (n + 2) * X (n + 2) + Y (n + 2) * Y (n + 2))
      + 2 * (X (n + 1) * X (n + 1) + Y (n + 1) * Y (n + 1))
      - (X n * X n + Y n * Y n) := by
  have x4 : X (n + 4) = X (n + 3) - Y (n + 3) + X (n + 2) := X_rec (n + 2)
  have y4 : Y (n + 4) = X (n + 3) + Y (n + 3) + Y (n + 2) := Y_rec (n + 2)
  have x3 : X (n + 3) = X (n + 2) - Y (n + 2) + X (n + 1) := X_rec (n + 1)
  have y3 : Y (n + 3) = X (n + 2) + Y (n + 2) + Y (n + 1) := Y_rec (n + 1)
  have x2 : X (n + 2) = X (n + 1) - Y (n + 1) + X n := X_rec n
  have y2 : Y (n + 2) = X (n + 1) + Y (n + 1) + Y n := Y_rec n
  rw [x4, y4, x3, y3, x2, y2]
  ring

theorem K_rec (n : ℕ) :
    Y (n + 5) * X (n + 4) - X (n + 5) * Y (n + 4) =
      2 * ((Y (n + 4) * X (n + 3) - X (n + 4) * Y (n + 3))
        + (Y (n + 3) * X (n + 2) - X (n + 3) * Y (n + 2))
        + (Y (n + 2) * X (n + 1) - X (n + 2) * Y (n + 1)))
      - (Y (n + 1) * X n - X (n + 1) * Y n) := by
  have x5 : X (n + 5) = X (n + 4) - Y (n + 4) + X (n + 3) := X_rec (n + 3)
  have y5 : Y (n + 5) = X (n + 4) + Y (n + 4) + Y (n + 3) := Y_rec (n + 3)
  have x4 : X (n + 4) = X (n + 3) - Y (n + 3) + X (n + 2) := X_rec (n + 2)
  have y4 : Y (n + 4) = X (n + 3) + Y (n + 3) + Y (n + 2) := Y_rec (n + 2)
  have x3 : X (n + 3) = X (n + 2) - Y (n + 2) + X (n + 1) := X_rec (n + 1)
  have y3 : Y (n + 3) = X (n + 2) + Y (n + 2) + Y (n + 1) := Y_rec (n + 1)
  have x2 : X (n + 2) = X (n + 1) - Y (n + 1) + X n := X_rec n
  have y2 : Y (n + 2) = X (n + 1) + Y (n + 1) + Y n := Y_rec n
  rw [x5, y5, x4, y4, x3, y3, x2, y2]
  ring

theorem hN (n : ℕ) : A138573 n = X n * X n + Y n * Y n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 4 with h | h
    · interval_cases n <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have r : A138573 (m + 4) = 2 * A138573 (m + 3) + 2 * A138573 (m + 2)
          + 2 * A138573 (m + 1) - A138573 m := rfl
      rw [r, ih m (by omega), ih (m + 1) (by omega), ih (m + 2) (by omega),
        ih (m + 3) (by omega)]
      exact (N_rec m).symm

theorem hK (n : ℕ) : A317974 (n + 1) = Y (n + 1) * X n - X (n + 1) * Y n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 4 with h | h
    · interval_cases n <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have r : A317974 (m + 5) = 2 * (A317974 (m + 4) + A317974 (m + 3) + A317974 (m + 2))
          - A317974 (m + 1) := rfl
      have i0 : A317974 (m + 1) = Y (m + 1) * X m - X (m + 1) * Y m := ih m (by omega)
      have i1 : A317974 (m + 2) = Y (m + 2) * X (m + 1) - X (m + 2) * Y (m + 1) :=
        ih (m + 1) (by omega)
      have i2 : A317974 (m + 3) = Y (m + 3) * X (m + 2) - X (m + 3) * Y (m + 2) :=
        ih (m + 2) (by omega)
      have i3 : A317974 (m + 4) = Y (m + 4) * X (m + 3) - X (m + 4) * Y (m + 3) :=
        ih (m + 3) (by omega)
      show A317974 (m + 5) = Y (m + 5) * X (m + 4) - X (m + 5) * Y (m + 4)
      rw [r, i0, i1, i2, i3]
      exact (K_rec m).symm

theorem mono (n : ℕ) : 0 ≤ A138573 n ∧ A138573 n ≤ A138573 (n + 1) ∧
    A138573 (n + 1) ≤ A138573 (n + 2) ∧ A138573 (n + 2) ≤ A138573 (n + 3) ∧
    1 ≤ A138573 (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    obtain ⟨h0, h1, h2, h3, h4⟩ := ih
    have r : A138573 (n + 4) = 2 * A138573 (n + 3) + 2 * A138573 (n + 2)
        + 2 * A138573 (n + 1) - A138573 n := rfl
    show 0 ≤ A138573 (n + 1) ∧ A138573 (n + 1) ≤ A138573 (n + 2) ∧
      A138573 (n + 2) ≤ A138573 (n + 3) ∧ A138573 (n + 3) ≤ A138573 (n + 4) ∧
      1 ≤ A138573 (n + 2)
    refine ⟨by linarith, h2, h3, by linarith, by linarith⟩

theorem hpos (n : ℕ) : 0 < A138573 (n + 1) := by
  have h := (mono n).2.2.2.2
  omega

theorem U_re (U : ℕ → ℂ) (hU : ∀ n, U n = (X n : ℂ) + (Y n : ℂ) * Complex.I) (n : ℕ) :
    (U n).re = (X n : ℝ) := by
  rw [hU]
  simp

theorem U_im (U : ℕ → ℂ) (hU : ∀ n, U n = (X n : ℂ) + (Y n : ℂ) * Complex.I) (n : ℕ) :
    (U n).im = (Y n : ℝ) := by
  rw [hU]
  simp

theorem U_rec (U : ℕ → ℂ) (hU : ∀ n, U n = (X n : ℂ) + (Y n : ℂ) * Complex.I) (n : ℕ) :
    U (n + 2) = (1 + Complex.I) * U (n + 1) + U n := by
  simp only [hU]
  rw [X_rec, Y_rec]
  push_cast
  linear_combination (-(Y (n + 1) : ℂ)) * Complex.I_sq

theorem U_ne (U : ℕ → ℂ) (hU : ∀ n, U n = (X n : ℂ) + (Y n : ℂ) * Complex.I) (n : ℕ) :
    U (n + 1) ≠ 0 := by
  intro h
  have h1 : (X (n + 1) : ℝ) = 0 := by rw [← U_re U hU, h, Complex.zero_re]
  have h2 : (Y (n + 1) : ℝ) = 0 := by rw [← U_im U hU, h, Complex.zero_im]
  have hx : X (n + 1) = 0 := by exact_mod_cast h1
  have hy : Y (n + 1) = 0 := by exact_mod_cast h2
  have e := hN (n + 1)
  rw [hx, hy] at e
  have p := hpos n
  linarith

theorem conv_eq (U : ℕ → ℂ) (hU : ∀ n, U n = (X n : ℂ) + (Y n : ℂ) * Complex.I) (m : ℕ) :
    conv (m + 1) = U (m + 2) / U (m + 1) := by
  induction m with
  | zero =>
    have hx1 : X 1 = 1 := by decide
    have hy1 : Y 1 = 0 := by decide
    have hx2 : X 2 = 1 := by decide
    have hy2 : Y 2 = 1 := by decide
    have c1 : conv 1 = 1 + Complex.I := rfl
    show conv 1 = U 2 / U 1
    rw [c1, hU 2, hU 1, hx1, hy1, hx2, hy2]
    simp
  | succ m ih =>
    have c : conv (m + 2) = (1 + Complex.I) + 1 / conv (m + 1) := rfl
    have hne : U (m + 2) ≠ 0 := U_ne U hU (m + 1)
    have h3 : U (m + 3) = (1 + Complex.I) * U (m + 2) + U (m + 1) := U_rec U hU (m + 1)
    have q : U (m + 1) / U (m + 2) * U (m + 2) = U (m + 1) := div_mul_cancel₀ (U (m + 1)) hne
    show conv (m + 2) = U (m + 3) / U (m + 2)
    rw [c, ih, one_div_div, h3, eq_div_iff hne]
    linear_combination q

theorem conv_im (U : ℕ → ℂ) (hU : ∀ n, U n = (X n : ℂ) + (Y n : ℂ) * Complex.I) (m : ℕ) :
    (conv (m + 1)).im = (A317974 (m + 2) : ℝ) / (A138573 (m + 1) : ℝ) := by
  have k : A317974 (m + 2) = Y (m + 2) * X (m + 1) - X (m + 2) * Y (m + 1) := hK (m + 1)
  have nn : A138573 (m + 1) = X (m + 1) * X (m + 1) + Y (m + 1) * Y (m + 1) := hN (m + 1)
  rw [conv_eq U hU m, Complex.div_im, Complex.normSq_apply, k, nn]
  simp only [U_re U hU, U_im U hU]
  push_cast
  ring

end R10A093726

open OMA.S_oeis_a093726 R10A093726 in
theorem OMA.solution : type_of% @OMA.S_oeis_a093726.main := by
  intro n hn _x y d hd h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨U, hU⟩ : ∃ U : ℕ → ℂ, ∀ k, U k = (X k : ℂ) + (Y k : ℂ) * Complex.I :=
    ⟨fun k => (X k : ℂ) + (Y k : ℂ) * Complex.I, fun _ => rfl⟩
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [eq_div_iff hdC] at h
  have h2 : (conv (m + 1)).im * (d : ℝ) = (y : ℝ) := by
    have e := congrArg Complex.im h
    simp at e
    linarith
  rw [show m + 1 + 1 = m + 2 by omega, ← conv_im U hU m, div_eq_iff hdR, h2]

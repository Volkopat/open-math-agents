import OMAStatements.S_oeis_a047098
import Mathlib

open OMA.S_oeis_a047098

private def T (N r : ℕ) : ℚ := ∑ k ∈ Finset.range (r + 1), ((N.choose k : ℕ) : ℚ)

private lemma T_succ (N r : ℕ) : T (N + 1) r = 2 * T N r - (N.choose r : ℚ) := by
  induction r with
  | zero => simp [T]; norm_num
  | succ r ih =>
    have e1 : T (N + 1) (r + 1) = T (N + 1) r + ((N + 1).choose (r + 1) : ℚ) := by
      simp [T, Finset.sum_range_succ]
    have e2 : T N (r + 1) = T N r + (N.choose (r + 1) : ℚ) := by
      simp [T, Finset.sum_range_succ]
    rw [e1, e2, ih, Nat.choose_succ_succ']
    push_cast; ring

private def S (p : ℕ) : ℚ := ∑ k ∈ Finset.range (p + 1), (((3 * p).choose k : ℕ) : ℚ)

private def b (p : ℕ) : ℚ := ((3 * p).choose p : ℚ)

private def rho (x : ℚ) : ℚ :=
  8 * x / (x + 1) - 2 * (3 * x + 1) / (x + 1) - (3 * x + 1) * (3 * x + 2) / ((x + 1) * (2 * x + 1))

private def rb (x : ℚ) : ℚ := 3 * (3 * x + 1) * (3 * x + 2) / (2 * (x + 1) * (2 * x + 1))

private lemma c1 (p : ℕ) : ((3 * p).choose (p + 1) : ℚ) = b p * (2 * p) / (p + 1) := by
  have h := Nat.choose_succ_right_eq (3 * p) p
  rw [show 3 * p - p = 2 * p by omega] at h
  have h' : ((3 * p).choose (p + 1) : ℚ) * ((p : ℚ) + 1) = b p * (2 * p) := by
    unfold b; exact_mod_cast h
  have : ((p : ℚ) + 1) ≠ 0 := by positivity
  field_simp; linarith

private lemma c2 (p : ℕ) : ((3 * p + 1).choose (p + 1) : ℚ) = b p * (3 * p + 1) / (p + 1) := by
  have h := Nat.add_one_mul_choose_eq (3 * p) p
  have h' : ((3 * p + 1).choose (p + 1) : ℚ) * ((p : ℚ) + 1) = b p * (3 * p + 1) := by
    unfold b; have h2 := congrArg (fun x : ℕ => (x : ℚ)) h; push_cast at h2; linarith
  have : ((p : ℚ) + 1) ≠ 0 := by positivity
  field_simp; linarith

private lemma c3 (p : ℕ) : ((3 * p + 2).choose (p + 1) : ℚ) =
    ((3 * p + 1).choose (p + 1) : ℚ) * (3 * p + 2) / (2 * p + 1) := by
  have h := Nat.choose_mul_succ_eq (3 * p + 1) (p + 1)
  rw [show 3 * p + 1 + 1 - (p + 1) = 2 * p + 1 by omega] at h
  have h' : ((3 * p + 2).choose (p + 1) : ℚ) * (2 * (p : ℚ) + 1) =
      ((3 * p + 1).choose (p + 1) : ℚ) * (3 * p + 2) := by
    exact_mod_cast h.symm
  have : (2 * (p : ℚ) + 1) ≠ 0 := by positivity
  field_simp; linarith

private lemma c4 (p : ℕ) : b (p + 1) = ((3 * p + 2).choose (p + 1) : ℚ) * (3 * p + 3) / (2 * p + 2) := by
  have h := Nat.choose_mul_succ_eq (3 * p + 2) (p + 1)
  rw [show 3 * p + 2 + 1 - (p + 1) = 2 * p + 2 by omega] at h
  have h' : b (p + 1) * (2 * (p : ℚ) + 2) = ((3 * p + 2).choose (p + 1) : ℚ) * (3 * p + 3) := by
    unfold b; rw [show 3 * (p + 1) = 3 * p + 2 + 1 by ring]; have h2 := congrArg (fun x : ℕ => (x : ℚ)) h; push_cast at h2; linarith
  have : (2 * (p : ℚ) + 2) ≠ 0 := by positivity
  rw [eq_div_iff this]; exact h'

private lemma hb (p : ℕ) : b (p + 1) = b p * rb p := by
  rw [c4, c3, c2]; unfold rb
  have : ((p : ℚ) + 1) ≠ 0 := by positivity
  have : (2 * (p : ℚ) + 1) ≠ 0 := by positivity
  have : (2 * (p : ℚ) + 2) ≠ 0 := by positivity
  field_simp

private lemma hS (p : ℕ) : S (p + 1) = 8 * S p + b p * rho p := by
  have e0 : S (p + 1) = T (3 * p + 3) (p + 1) := by
    unfold S T; rw [show 3 * (p + 1) = 3 * p + 3 by ring]
  have e1 : T (3 * p) (p + 1) = S p + ((3 * p).choose (p + 1) : ℚ) := by
    unfold S T; rw [Finset.sum_range_succ]
  rw [e0, show 3 * p + 3 = 3 * p + 2 + 1 by ring, T_succ, show 3 * p + 2 = 3 * p + 1 + 1 by ring,
    T_succ, T_succ, e1, c3, c2, c1]
  unfold rho
  have : ((p : ℚ) + 1) ≠ 0 := by positivity
  have : (2 * (p : ℚ) + 1) ≠ 0 := by positivity
  field_simp; ring

theorem OMA.solution : type_of% @OMA.S_oeis_a047098.main := by
  intro n hn
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 3 := ⟨n - 3, by omega⟩
  rw [show p + 3 - 1 = p + 2 by omega, show p + 3 - 2 = p + 1 by omega, show p + 3 - 3 = p by omega]
  have ha : ∀ m, (a m : ℚ) = 2 * b m - S m := by
    intro m; unfold a b S; push_cast; ring
  have key : (2 * ((p + 3 : ℕ) : ℚ) * (2 * ((p + 3 : ℕ) : ℚ) - 1) * a (p + 3)
      + (-71 * ((p + 3 : ℕ) : ℚ) ^ 2 + 112 * ((p + 3 : ℕ) : ℚ) - 48) * a (p + 2)
      + 3 * (131 * ((p + 3 : ℕ) : ℚ) ^ 2 - 391 * ((p + 3 : ℕ) : ℚ) + 296) * a (p + 1)
      - 72 * (3 * ((p + 3 : ℕ) : ℚ) - 7) * (3 * ((p + 3 : ℕ) : ℚ) - 8) * a p) = 0 := by
    rw [ha, ha, ha, ha]
    have s3 := hS (p + 2)
    have s2 := hS (p + 1)
    have s1 := hS p
    have b3 := hb (p + 2)
    have b2 := hb (p + 1)
    have b1 := hb p
    rw [show p + 2 + 1 = p + 3 from rfl] at s3 b3
    rw [show p + 1 + 1 = p + 2 from rfl] at s2 b2
    rw [s3, s2, s1, b3, b2, b1]
    unfold rho rb
    push_cast
    have : ((p : ℚ) + 1) ≠ 0 := by positivity
    have : ((p : ℚ) + 2) ≠ 0 := by positivity
    have : ((p : ℚ) + 1 + 1) ≠ 0 := by positivity
    have : ((p : ℚ) + 2 + 1) ≠ 0 := by positivity
    have : (2 * (p : ℚ) + 1) ≠ 0 := by positivity
    have : (2 * ((p : ℚ) + 1) + 1) ≠ 0 := by positivity
    have : (2 * ((p : ℚ) + 2) + 1) ≠ 0 := by positivity
    have : (2 * ((p : ℚ) + 1 + 1) + 1) ≠ 0 := by positivity
    have : (2 * ((p : ℚ) + 2 + 1) + 1) ≠ 0 := by positivity
    field_simp
    ring
  have : ((2 * ((p + 3 : ℕ) : ℤ) * (2 * ((p + 3 : ℕ) : ℤ) - 1) * a (p + 3)
      + (-71 * ((p + 3 : ℕ) : ℤ) ^ 2 + 112 * ((p + 3 : ℕ) : ℤ) - 48) * a (p + 2)
      + 3 * (131 * ((p + 3 : ℕ) : ℤ) ^ 2 - 391 * ((p + 3 : ℕ) : ℤ) + 296) * a (p + 1)
      - 72 * (3 * ((p + 3 : ℕ) : ℤ) - 7) * (3 * ((p + 3 : ℕ) : ℤ) - 8) * a p : ℤ) : ℚ) = 0 := by
    push_cast at key ⊢; linear_combination key
  exact_mod_cast this

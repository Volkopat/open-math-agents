import OMAStatements.S_oeis_a039598
import Mathlib

-- Problem: oeis-a039598 (Schulte's harmonic identity for the Catalan triangle)
-- Credit: @Aijy0264561
-- T(n,k)/(k+1)^2 = C(2n+2, n-k) / ((n+1)(k+1)), so the claim is g(M) = H_M C(2M,M)/2 with
-- g(M) = sum_{k<M} C(2M, M-1-k)/(k+1). Termwise (M+1) g(M+1) - 2(2M+1) g(M) telescopes to
-- sum_{k<=M} (k+1) C(2M+2, M-k) / (M+1) = C(2M+1, M) (ballot differences), and induction closes it.

open Finset

namespace OMA.A039598proof

open OMA.S_oeis_a039598

/-- `(n+1) C(n,k) = C(n+1,k+1) (k+1)`. -/
lemma succ_choose (n k : ℕ) : ((n + 1).choose (k + 1) : ℚ) * (k + 1) = (n.choose k : ℚ) * (n + 1) := by
  have h1 := Nat.choose_succ_right_eq (n + 1) k
  have h2 := Nat.choose_mul_succ_eq n k
  have h : (n + 1).choose (k + 1) * (k + 1) = n.choose k * (n + 1) := by rw [h1, h2]
  exact_mod_cast h

/-- Ballot form: `(N - j) C(2N, j) = N (C(2N-1, j) - C(2N-1, j-1))` for `1 ≤ j ≤ N`. -/
lemma ballot (N l : ℕ) (hl : l < N) :
    ((N - (l + 1) : ℕ) : ℚ) * ((2 * N).choose (l + 1) : ℚ) =
      N * (((2 * N - 1).choose (l + 1) : ℚ) - ((2 * N - 1).choose l : ℚ)) := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  have e1 : 2 * (N' + 1) = (2 * N' + 1) + 1 := by ring
  have e2 : 2 * (N' + 1) - 1 = 2 * N' + 1 := by omega
  rw [e2, e1, Nat.choose_succ_succ']
  have h := Nat.choose_succ_right_eq (2 * N' + 1) l
  have h' : ((2 * N' + 1).choose (l + 1) : ℚ) * (l + 1) =
      ((2 * N' + 1).choose l : ℚ) * ((2 * N' + 1 - l : ℕ) : ℚ) := by exact_mod_cast h
  rw [Nat.cast_sub (by omega)] at h'
  rw [Nat.cast_sub (by omega)]
  push_cast at h' ⊢
  linear_combination -h'

/-- `∑_{k<N} (k+1) C(2N, N-1-k) = N C(2N-1, N-1)`. -/
lemma weighted (N : ℕ) :
    ∑ k ∈ range N, ((k + 1 : ℕ) : ℚ) * ((2 * N).choose (N - 1 - k) : ℚ) =
      N * ((2 * N - 1).choose (N - 1) : ℚ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hr : ∑ k ∈ range N, ((k + 1 : ℕ) : ℚ) * ((2 * N).choose (N - 1 - k) : ℚ) =
      ∑ j ∈ range N, ((N - j : ℕ) : ℚ) * ((2 * N).choose j : ℚ) := by
    rw [← sum_range_reflect (fun j => ((N - j : ℕ) : ℚ) * ((2 * N).choose j : ℚ)) N]
    apply sum_congr rfl
    intro k hk
    have hk' := mem_range.1 hk
    rw [show N - (N - 1 - k) = k + 1 by omega]
  rw [hr]
  set f : ℕ → ℚ := fun j => if j = 0 then 0 else ((2 * N - 1).choose (j - 1) : ℚ) with hf
  have hterm : ∀ j ∈ range N, ((N - j : ℕ) : ℚ) * ((2 * N).choose j : ℚ) = N * (f (j + 1) - f j) := by
    intro j hj
    have hj' := mem_range.1 hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [hf]
    · obtain ⟨l, rfl⟩ : ∃ l, j = l + 1 := ⟨j - 1, by omega⟩
      rw [ballot N l (by omega)]
      simp [hf]
  rw [sum_congr rfl hterm, ← mul_sum, sum_range_sub f N]
  simp [hf, show N ≠ 0 by omega]

/-- `C(2N, N) = 2 C(2N-1, N-1)` for `N ≥ 1`. -/
lemma central_eq (N : ℕ) (hN : 1 ≤ N) :
    ((2 * N).choose N : ℚ) = 2 * ((2 * N - 1).choose (N - 1) : ℚ) := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  have e1 : 2 * (N' + 1) = (2 * N' + 1) + 1 := by ring
  have e2 : 2 * (N' + 1) - 1 = 2 * N' + 1 := by omega
  rw [e2, e1, Nat.choose_succ_succ', show N' + 1 - 1 = N' by omega,
    Nat.choose_symm_of_eq_add (show 2 * N' + 1 = (N' + 1) + N' by ring)]
  push_cast; ring

/-- The normalized sum `g M = ∑_{k<M} C(2M, M-1-k) / (k+1)`. -/
def g (M : ℕ) : ℚ := ∑ k ∈ range M, ((2 * M).choose (M - 1 - k) : ℚ) / (k + 1)

lemma step (M : ℕ) :
    ((M : ℚ) + 1) * g (M + 1) - 2 * (2 * (M : ℚ) + 1) * g M =
      ((2 * M + 1).choose M : ℚ) := by
  unfold g
  rw [sum_range_succ, mul_add, mul_sum, mul_sum, add_sub_right_comm, ← sum_sub_distrib]
  have hterm : ∀ k ∈ range M,
      ((M : ℚ) + 1) * (((2 * (M + 1)).choose (M + 1 - 1 - k) : ℚ) / (k + 1)) -
        2 * (2 * (M : ℚ) + 1) * (((2 * M).choose (M - 1 - k) : ℚ) / (k + 1)) =
      ((k + 1 : ℕ) : ℚ) * ((2 * (M + 1)).choose ((M + 1) - 1 - k) : ℚ) / ((M : ℚ) + 1) := by
    intro k hk
    have hk' := mem_range.1 hk
    obtain ⟨j, hj⟩ : ∃ j, j = M - 1 - k := ⟨_, rfl⟩
    have i1 : M + 1 - 1 - k = j + 1 := by omega
    have i2 : 2 * (M + 1) = (2 * M + 1) + 1 := by ring
    rw [i1, ← hj, i2]
    -- B (j+1) = (2M+2) C(2M+1, j),  C(2M+1, j) (2M+1-j) = (2M+1) A
    have r1 := succ_choose (2 * M + 1) j
    have r2 := Nat.choose_mul_succ_eq (2 * M) j
    have r2' : ((2 * M).choose j : ℚ) * (2 * M + 1) =
        ((2 * M + 1).choose j : ℚ) * ((2 * M + 1 - j : ℕ) : ℚ) := by exact_mod_cast r2
    rw [Nat.cast_sub (by omega)] at r2'
    have hjk : (j : ℚ) = M - 1 - k := by
      have e : j + k + 1 = M := by omega
      have e' : (j : ℚ) + k + 1 = M := by exact_mod_cast e
      linarith
    set B := ((2 * M + 1 + 1).choose (j + 1) : ℚ)
    set C := ((2 * M + 1).choose j : ℚ)
    set A := ((2 * M).choose j : ℚ)
    push_cast at r1 r2' ⊢
    rw [hjk] at r1 r2'
    have hk1 : (k : ℚ) + 1 ≠ 0 := by positivity
    have hM1 : (M : ℚ) + 1 ≠ 0 := by positivity
    have hMk : (M : ℚ) - k ≠ 0 := by
      have : (k : ℚ) < M := by exact_mod_cast hk'
      linarith
    have hMk2 : (M : ℚ) + 2 + k ≠ 0 := by positivity
    -- solve A and C in terms of B
    have hC : C = B * (M - k) / (2 * M + 2) := by
      rw [eq_div_iff (by positivity)]
      linear_combination -r1
    have hA : A = C * (M + 2 + k) / (2 * M + 1) := by
      rw [eq_div_iff (by positivity)]
      linear_combination r2'
    rw [hA, hC]
    field_simp
    ring
  rw [sum_congr rfl hterm, ← sum_div]
  have hlast : ((M : ℚ) + 1) * (((2 * (M + 1)).choose (M + 1 - 1 - M) : ℚ) / ((M : ℚ) + 1)) =
      ((M + 1 : ℕ) : ℚ) * ((2 * (M + 1)).choose ((M + 1) - 1 - M) : ℚ) / ((M : ℚ) + 1) := by
    push_cast; ring
  rw [hlast, ← add_div]
  have hw := weighted (M + 1)
  rw [sum_range_succ] at hw
  push_cast at hw ⊢
  rw [hw]
  have hM1 : (M : ℚ) + 1 ≠ 0 := by positivity
  field_simp
  rw [show 2 * (M + 1) - 1 = 2 * M + 1 by omega]

lemma g_eq (M : ℕ) : g M = harmonic M * ((2 * M).choose M : ℚ) / 2 := by
  induction M with
  | zero => simp [g]
  | succ M ih =>
    have hs := step M
    have hc := Nat.succ_mul_centralBinom_succ M
    rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at hc
    have hc' : ((M : ℚ) + 1) * ((2 * (M + 1)).choose (M + 1) : ℚ) =
        2 * (2 * M + 1) * ((2 * M).choose M : ℚ) := by exact_mod_cast hc
    have hce := central_eq (M + 1) (by omega)
    rw [show 2 * (M + 1) - 1 = 2 * M + 1 by omega, show M + 1 - 1 = M by omega] at hce
    rw [ih] at hs
    rw [harmonic_succ]
    have hM1 : (M : ℚ) + 1 ≠ 0 := by positivity
    have : g (M + 1) * ((M : ℚ) + 1) =
        ((harmonic M + ((M + 1 : ℕ) : ℚ)⁻¹) * ((2 * (M + 1)).choose (M + 1) : ℚ) / 2) *
          ((M : ℚ) + 1) := by
      have e : ((harmonic M + ((M + 1 : ℕ) : ℚ)⁻¹) * ((2 * (M + 1)).choose (M + 1) : ℚ) / 2) *
          ((M : ℚ) + 1) = harmonic M * ((2 * (M + 1)).choose (M + 1) : ℚ) * ((M : ℚ) + 1) / 2 +
          ((2 * (M + 1)).choose (M + 1) : ℚ) / 2 := by
        push_cast; field_simp
      rw [e]
      linear_combination hs - (harmonic M / 2) * hc' - (1 / 2) * hce
    exact mul_right_cancel₀ hM1 this

theorem a039598 : ∀ n : ℕ,
    (∑ k ∈ range (n + 1), catalanTriangle n k / ((k : ℚ) + 1) ^ 2) =
      harmonic (n + 1) * (catalan n : ℚ) * (2 * (n : ℚ) + 1) / ((n : ℚ) + 1) := by
  intro n
  have hn1 : (n : ℚ) + 1 ≠ 0 := by positivity
  have hterm : ∀ k ∈ range (n + 1), catalanTriangle n k / ((k : ℚ) + 1) ^ 2 =
      ((2 * (n + 1)).choose (n + 1 - 1 - k) : ℚ) / (k + 1) / ((n : ℚ) + 1) := by
    intro k hk
    have hk' := mem_range.1 hk
    unfold catalanTriangle
    rw [if_pos (by omega), show n + 1 - 1 - k = n - k by omega,
      show 2 * (n + 1) = (2 * n + 1) + 1 by ring]
    have r := Nat.choose_mul_succ_eq (2 * n + 1) (n - k)
    have r' : ((2 * n + 1).choose (n - k) : ℚ) * (2 * n + 1 + 1) =
        ((2 * n + 1 + 1).choose (n - k) : ℚ) * ((2 * n + 1 + 1 - (n - k) : ℕ) : ℚ) := by
      exact_mod_cast r
    rw [show 2 * n + 1 + 1 - (n - k) = n + k + 2 by omega] at r'
    push_cast at r' ⊢
    have hk1 : (k : ℚ) + 1 ≠ 0 := by positivity
    have hnk : (n : ℚ) + k + 2 ≠ 0 := by positivity
    have hC : ((2 * n + 1).choose (n - k) : ℚ) =
        ((2 * n + 1 + 1).choose (n - k) : ℚ) * (n + k + 2) / (2 * n + 2) := by
      rw [eq_div_iff (by positivity)]; linear_combination r'
    rw [hC]
    field_simp
  rw [sum_congr rfl hterm, ← sum_div]
  have hg : ∑ k ∈ range (n + 1), ((2 * (n + 1)).choose (n + 1 - 1 - k) : ℚ) / (k + 1) =
      g (n + 1) := by
    unfold g; push_cast; rfl
  rw [hg, g_eq]
  have hcat := succ_mul_catalan_eq_centralBinom n
  have hc := Nat.succ_mul_centralBinom_succ n
  rw [Nat.centralBinom_eq_two_mul_choose] at hcat
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at hc
  have hcat' : ((n : ℚ) + 1) * (catalan n : ℚ) = ((2 * n).choose n : ℚ) := by exact_mod_cast hcat
  have hc' : ((n : ℚ) + 1) * ((2 * (n + 1)).choose (n + 1) : ℚ) =
      2 * (2 * n + 1) * ((2 * n).choose n : ℚ) := by exact_mod_cast hc
  have hcatv : (catalan n : ℚ) = ((2 * n).choose n : ℚ) / (n + 1) := by
    rw [eq_div_iff (by positivity)]; linear_combination hcat'
  have hcv : ((2 * (n + 1)).choose (n + 1) : ℚ) = 2 * (2 * n + 1) * ((2 * n).choose n : ℚ) / (n + 1) := by
    rw [eq_div_iff (by positivity)]; linear_combination hc'
  rw [hcatv, hcv]
  push_cast
  field_simp

end OMA.A039598proof

theorem OMA.solution : type_of% @OMA.S_oeis_a039598.main := OMA.A039598proof.a039598

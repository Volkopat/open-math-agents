import OMAStatements.S_oeis_a102319

/-! The central coefficient of a quadratic power satisfies a three-term recurrence.
For the two weights of the mean binomial transform, eliminating that recurrence gives
both of Mathar's identities. -/

namespace OMA.S_oeis_a102319
open Polynomial

private noncomputable def quad (s : ℚ) : ℚ[X] := X ^ 2 + C (s + 2) * X + 1

/-- In the binomial expansion of `((X+1)^2 + sX)^n`, the `k`th term contributes
the central coefficient of `(X+1)^(2k)`. -/
private lemma central_coeff (s : ℚ) (n : ℕ) :
    ((quad s)^n).coeff n = transform s n := by
  have hd : quad s = (X + 1)^2 + C s * X := by
    simp [quad, map_add, map_ofNat]
    ring
  rw [hd, add_pow, finsetSum_coeff, transform]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hterm : ((X + 1 : ℚ[X]) ^ 2) ^ k * (C s * X) ^ (n - k) * (n.choose k : ℚ[X]) =
      C ((n.choose k : ℚ) * s ^ (n-k)) * ((X + 1) ^ (2*k) * X ^ (n-k)) := by
    rw [← pow_mul, mul_pow, ← map_pow, map_mul, map_natCast]
    ring
  rw [hterm, coeff_C_mul, coeff_mul_X_pow', if_pos (Nat.sub_le _ _),
    Nat.sub_sub_self hk', coeff_X_add_one_pow, Nat.centralBinom]
  ring

private lemma recurrence (s : ℚ) (n : ℕ) :
    ((n : ℚ) + 2) * transform s (n+2)
      - (2*n + 3) * (s + 2) * transform s (n+1)
      + (n+1) * ((s + 2)^2 - 4) * transform s n = 0 := by
  let D := quad s
  let E := (X^2 - 1) * D^(n+1)
  have hd : derivative D = 2*X + C (s+2) := by simp [D, quad, derivative_mul, derivative_sq, map_ofNat]
  -- The degree-`n+2` coefficient of `X E′ - (n+2) E` vanishes coefficientwise.
  have hid : X * derivative E - C ((n : ℚ)+2) * E =
      C ((n : ℚ)+2) * D^(n+2) - C ((2*(n : ℚ)+3)*(s+2)) * (X * D^(n+1))
      + C (((n : ℚ)+1)*((s+2)^2-4)) * (X^2 * D^n) := by
    dsimp only [E]
    rw [derivative_mul, derivative_pow_succ, hd]
    simp only [map_sub, derivative_sq, derivative_X, derivative_one, mul_one, sub_zero,
      map_add, map_mul, map_pow, map_ofNat, map_one, pow_succ D]
    dsimp only [D, quad]
    simp only [map_add, map_ofNat]
    ring
  have h := congrArg (fun p : ℚ[X] => p.coeff (n+2)) hid
  simp only [coeff_sub, coeff_add, coeff_X_mul, coeff_derivative, coeff_C_mul, coeff_X_pow_mul] at h
  simp only [← central_coeff]
  dsimp only [D] at h
  push_cast at h
  linarith only [h]

/- Each recurrence below is a polynomial linear combination of shifts of `recurrence`. -/
private lemma orderSix_plus (n : ℕ) : orderSix (transform 1) (n+6) := by
  have h0 := recurrence 1 n
  have h1 := recurrence 1 (n+1)
  have h2 := recurrence 1 (n+2)
  have h3 := recurrence 1 (n+3)
  have h4 := recurrence 1 (n+4)
  unfold orderSix
  rw [show n+6-1 = n+5 by omega,
    show n+6-2 = n+4 by omega,
    show n+6-3 = n+3 by omega,
    show n+6-4 = n+2 by omega,
    show n+6-5 = n+1 by omega,
    show n+6-6 = n by omega]
  norm_num [Nat.add_assoc] at *
  linear_combination (-21*((n : ℚ) + 2)) * h0 +
    (27 - 2*(n : ℚ)) * h1 +
    (12*(n : ℚ) + 17) * h2 +
    (-6*(n : ℚ) - 23) * h3 +
    ((n : ℚ) + 5) * h4

private lemma orderSix_minus (n : ℕ) : orderSix (transform (-1)) (n+6) := by
  have h0 := recurrence (-1) n
  have h1 := recurrence (-1) (n+1)
  have h2 := recurrence (-1) (n+2)
  have h3 := recurrence (-1) (n+3)
  have h4 := recurrence (-1) (n+4)
  unfold orderSix
  rw [show n+6-1 = n+5 by omega,
    show n+6-2 = n+4 by omega,
    show n+6-3 = n+3 by omega,
    show n+6-4 = n+2 by omega,
    show n+6-5 = n+1 by omega,
    show n+6-6 = n by omega]
  norm_num [Nat.add_assoc] at *
  linear_combination (35*((n : ℚ) + 2)) * h0 +
    (-62*(n : ℚ) - 143) * h1 +
    (36*(n : ℚ) + 121) * h2 +
    (-5*(2*(n : ℚ) + 9)) * h3 +
    ((n : ℚ) + 5) * h4

private lemma orderFour_plus (n : ℕ) : orderFour (transform 1) (n+4) := by
  have h0 := recurrence 1 n
  have h1 := recurrence 1 (n+1)
  have h2 := recurrence 1 (n+2)
  unfold orderFour
  rw [show n+4-1 = n+3 by omega,
    show n+4-2 = n+2 by omega,
    show n+4-3 = n+1 by omega,
    show n+4-4 = n by omega]
  norm_num [Nat.add_assoc] at *
  linear_combination (-3*((n : ℚ) + 2)*(12*(n : ℚ)^2 + 72*(n : ℚ) + 101)) * h0 +
    (-24*(n : ℚ)^3 - 180*(n : ℚ)^2 - 418*(n : ℚ) - 315) * h1 +
    (((n : ℚ) + 3)*(12*(n : ℚ)^2 + 48*(n : ℚ) + 41)) * h2

private lemma orderFour_minus (n : ℕ) : orderFour (transform (-1)) (n+4) := by
  have h0 := recurrence (-1) n
  have h1 := recurrence (-1) (n+1)
  have h2 := recurrence (-1) (n+2)
  unfold orderFour
  rw [show n+4-1 = n+3 by omega,
    show n+4-2 = n+2 by omega,
    show n+4-3 = n+1 by omega,
    show n+4-4 = n by omega]
  norm_num [Nat.add_assoc] at *
  linear_combination (5*((n : ℚ) + 2)*(12*(n : ℚ)^2 + 72*(n : ℚ) + 101)) * h0 +
    (-72*(n : ℚ)^3 - 540*(n : ℚ)^2 - 1254*(n : ℚ) - 889) * h1 +
    (((n : ℚ) + 3)*(12*(n : ℚ)^2 + 48*(n : ℚ) + 41)) * h2

private lemma meanSix (n : ℕ) : orderSix a (n+6) := by
  have hp := orderSix_plus n
  have hm := orderSix_minus n
  unfold orderSix at *
  simp only [a]
  linear_combination hp / 2 + hm / 2

private lemma meanFour (n : ℕ) : orderFour a (n+4) := by
  have hp := orderFour_plus n
  have hm := orderFour_minus n
  unfold orderFour at *
  simp only [a]
  linear_combination hp / 2 + hm / 2

end OMA.S_oeis_a102319

open OMA.S_oeis_a102319

theorem OMA.solution : type_of% @OMA.S_oeis_a102319.main := by
  constructor
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k+6 := ⟨n-6, by omega⟩
    exact meanSix k
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k+4 := ⟨n-4, by omega⟩
    exact meanFour k


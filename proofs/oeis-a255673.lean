import OMAStatements.S_oeis_a255673

/-! Both binomial formulas follow from the coefficient identity for every power of A. The recurrence for A and the differentiated trinomial expansion give the same induction step. -/

open Polynomial

namespace T255673

private theorem derivative_coeff (N j : ℕ) :
    let P : ℚ[X] := 1 + X + X ^ 2
    (P ^ (N + 1)).coeff (j + 1) * (j + 1 : ℚ) =
      (N + 1 : ℚ) * ((P ^ N).coeff j + 2 * (P ^ N * X).coeff j) := by
  intro P
  have hP : derivative P = 1 + C 2 * X := by
    simp only [P, derivative_add, derivative_one, derivative_X, derivative_X_sq, zero_add]
  have h : derivative (P ^ (N + 1)) =
      C (N + 1 : ℚ) * (P ^ N + (P ^ N * X) * C 2) := by
    rw [derivative_pow_succ, hP]
    ring
  have hcoeff := congrArg (fun f : ℚ[X] => f.coeff j) h
  simp only [coeff_derivative, coeff_C_mul, coeff_add, coeff_mul_C] at hcoeff
  linear_combination hcoeff

theorem weighted_coeff (N n : ℕ) :
    let P : ℚ[X] := 1 + X + X ^ 2
    (N + 1 : ℚ) * ((P ^ N).coeff (n + 1) + 2 * (P ^ N).coeff n) =
      (n + 2 : ℚ) * (P ^ (N + 1)).coeff (n + 2) := by
  intro P
  have h := derivative_coeff N (n + 1)
  change (P ^ (N + 1)).coeff (n + 2) * (((n + 1 : ℕ) : ℚ) + 1) =
    (N + 1 : ℚ) * ((P ^ N).coeff (n + 1) + 2 * (P ^ N * X).coeff (n + 1)) at h
  rw [coeff_mul_X, Nat.cast_add_one] at h
  linear_combination -h

end T255673

namespace T255673

private noncomputable abbrev trinomial : Polynomial ℚ := 1 + Polynomial.X + Polynomial.X ^ 2

private lemma trinomial_zero (k : ℕ) : (trinomial ^ k).coeff 0 = 1 := by
  change Polynomial.constantCoeff (trinomial ^ k) = 1
  rw [map_pow]
  suffices h : Polynomial.constantCoeff trinomial = 1 by rw [h, one_pow]
  change (1+Polynomial.X+Polynomial.X^2 : Polynomial ℚ).coeff 0 = 1
  norm_num [Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one]

private lemma trinomial_one (k : ℕ) : (trinomial ^ k).coeff 1 = (k : ℚ) := by
  induction k with
  | zero => norm_num [Polynomial.coeff_one]
  | succ k ih =>
    rw [pow_succ, Polynomial.mul_coeff_one, trinomial_zero, ih]
    norm_num [trinomial, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one]
    ring

private lemma bal_step {d m s a b g u v w c : ℚ}
    (hpos : 0 < d) (hd : d = 3 * m + s)
    (ha : d*a = s*u) (hb : d*b = (s+3)*v) (hg : d*g = (s+6)*w)
    (hc : c = u+v+w) (hder : (d+1)*(v+2*w) = m*c) :
    (d+1)*(a+b+g) = (s+1)*c := by
  apply mul_left_cancel₀ hpos.ne' (b := (d+1)*(a+b+g)) (c := (s+1)*c)
  calc d*((d+1)*(a+b+g)) = (d+1)*(d*a+d*b+d*g) := by ring
       _ = (d+1)*(s*u+(s+3)*v+(s+6)*w) := by rw [ha,hb,hg]
       _ = s*((d+1)*c)+3*((d+1)*(v+2*w)) := by rw [hc]; ring
       _ = d*((s+1)*c) := by rw [hder, hd]; ring

/-- The coefficient of degree n in A^k, multiplied by 3n+k, is k times the
corresponding coefficient of the (3n+k)-th trinomial power. Induct first on
the degree and then on k, using the three terms of the defining equation. -/
private lemma pow_coeff_formula
    (der : ∀ D n : ℕ, (D+1 : ℚ) * ((trinomial^D).coeff (n+1) +
      2*(trinomial^D).coeff n) = (n+2 : ℚ)*(trinomial^(D+1)).coeff (n+2))
    (A : PowerSeries ℚ)
    (eqA : A = 1 + PowerSeries.X*A^3 + PowerSeries.X^2*A^6) (n k : ℕ) :
    (3*(n:ℚ)+k) * PowerSeries.coeff n (A^k) =
      (k:ℚ)*(trinomial^(3*n+k)).coeff n := by
  have hzero : PowerSeries.constantCoeff A = 1 := by
    simpa using congrArg PowerSeries.constantCoeff eqA
  have hone : PowerSeries.coeff 1 A = 1 := by
    simpa [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_zero_eq_constantCoeff_apply, hzero,
      PowerSeries.coeff_one, PowerSeries.coeff_succ_X_mul] using congrArg (PowerSeries.coeff 1) eqA
  induction n using Nat.strong_induction_on generalizing k with
  | h n hn =>
    cases n with
    | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hzero, trinomial_zero]
    | succ t =>
      cases t with
      | zero =>
        simp [PowerSeries.coeff_one_pow, hone, hzero, trinomial_one]
        ring
      | succ t =>
        rw [show ((t+1+1 : ℕ):ℚ) = (t:ℚ)+2 by push_cast; ring]
        change (3*((t:ℚ)+2)+k)*PowerSeries.coeff (t+2) (A^k) =
          (k:ℚ)*(trinomial^(3*(t+2)+k)).coeff (t+2)
        induction k with
        | zero => simp [PowerSeries.coeff_one]
        | succ s ih =>
          let D := 3*(t+2)+s
          have hpow : A^(s+1) = A^s + PowerSeries.X * A^(s+3) +
              PowerSeries.X^2 * A^(s+6) := by
            calc A^(s+1) = A^s*A := pow_succ _ _
                 _ = A^s*(1+PowerSeries.X*A^3+PowerSeries.X^2*A^6) := congrArg (A^s*·) eqA
                 _ = _ := by rw [pow_add, pow_add]; ring
          have ha := congrArg (PowerSeries.coeff (t+2)) hpow
          simp only [map_add, PowerSeries.coeff_X_pow_mul, PowerSeries.coeff_succ_X_mul] at ha
          have hb := hn (t+1) (by omega) (s+3)
          have hg := hn t (by omega) (s+6)
          rw [show 3*(t+1)+(s+3)=D by dsimp [D]; omega] at hb
          rw [show 3*t+(s+6)=D by dsimp [D]; omega] at hg
          have hc : (trinomial^(D+1)).coeff (t+2) = (trinomial^D).coeff (t+2) +
                (trinomial^D).coeff (t+1) + (trinomial^D).coeff t := by
            rw [pow_succ]
            change ((trinomial^D)*(1+Polynomial.X+Polynomial.X^2)).coeff (t+2) = _
            simp only [mul_add, mul_one, Polynomial.coeff_add, Polynomial.coeff_mul_X_pow,
              Polynomial.coeff_mul_X]
          have hd : (D:ℚ) = 3*((t:ℚ)+2)+s := by dsimp [D]; push_cast; ring
          rw [ha]
          push_cast at hb hg
          rw [show 3*((t:ℚ)+1)+((s:ℚ)+3)=(D:ℚ) by rw [hd]; ring] at hb
          rw [show 3*(t:ℚ)+((s:ℚ)+6)=(D:ℚ) by rw [hd]; ring] at hg
          have hh := bal_step (d := (D:ℚ)) (by rw [hd]; positivity) hd (hd.symm ▸ ih)
            hb hg hc (der D t)
          rw [Nat.cast_succ, show 3*((t:ℚ)+2)+((s:ℚ)+1)=(D:ℚ)+1 by rw [hd]; ring]
          exact hh

end T255673

namespace T255673

open Polynomial OMA.S_oeis_a255673

/-- Choose the factors contributing `1 + X`. Each remaining factor contributes `X²`. -/
lemma pos_expansion (n : ℕ) :
    ((1 + X + X ^ 2 : Polynomial ℚ) ^ (3*n + 4)).coeff (n+1) =
      ∑ j ∈ Finset.range (3*n + 5),
        binomZ j (2*(j : ℤ) - 5*n - 7) * ((3*n + 4).choose j : ℚ) := by
  rw [add_pow (1 + X) (X^2), finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [← C_eq_natCast, coeff_mul_C, ← pow_mul, coeff_mul_X_pow',
    coeff_one_add_X_pow, binomZ]
  by_cases h : 2 * (3*n + 4 - j) ≤ n + 1
  · rw [if_pos h, if_pos (by omega)]
    congr 3
    omega
  · rw [if_neg h, if_neg (by omega)]

end T255673

/-! The signed coefficient formula for the trinomial power in A255673. -/

namespace T255673

open Polynomial

theorem signed_expansion (n : ℕ) :
    ((1 + X + X^2 : Polynomial ℚ)^(3*n+1)).coeff n =
      ∑ k ∈ Finset.range (n+1), (-1:ℚ)^k * ((3*n+1).choose k : ℚ) *
        ((6*n+2-2*k).choose (n-k) : ℚ) := by
  have base : (1 + X + X^2 : Polynomial ℚ) = -X + (1+X)^2 := by ring
  rw [base, add_pow, finsetSum_coeff]
  have term (k : ℕ) :
      ((-X)^k * ((1+X)^2)^(3*n+1-k) * ((3*n+1).choose k : Polynomial ℚ)).coeff n =
        (-1:ℚ)^k * ((3*n+1).choose k : ℚ) *
          (if k ≤ n then ((6*n+2-2*k).choose (n-k) : ℚ) else 0) := by
    have expanded : (-X)^k * ((1+X)^2)^(3*n+1-k) * ((3*n+1).choose k : Polynomial ℚ) =
        C ((-1:ℚ)^k * ((3*n+1).choose k : ℚ)) *
          (X^k * (1+X)^(2*(3*n+1-k))) := by
      rw [← neg_one_mul (X : Polynomial ℚ), mul_pow, pow_mul]
      simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
      ring
    rw [expanded, coeff_C_mul, coeff_X_pow_mul', coeff_one_add_X_pow,
      show 2*(3*n+1-k) = 6*n+2-2*k by omega]
  simp_rw [term]
  symm
  apply Finset.sum_subset_zero_on_sdiff (Finset.range_mono (by omega))
  · intro k hk
    have h := (Finset.mem_sdiff.mp hk).2
    simp only [Finset.mem_range] at h
    simp [show ¬ k ≤ n by omega]
  · intro k hk
    simp [show k ≤ n by simpa using hk]

end T255673

namespace T255673

theorem assemble (hcoef : ∀ A : PowerSeries ℚ,
    A = 1 + PowerSeries.X*A^3 + PowerSeries.X^2*A^6 → ∀ n : ℕ,
      (3*(n:ℚ)+1)*PowerSeries.coeff n A =
        ((1+Polynomial.X+Polynomial.X^2 : Polynomial ℚ)^(3*n+1)).coeff n) :
    type_of% @OMA.S_oeis_a255673.main := by
  intro A hA
  constructor
  · intro n
    have h := hcoef A hA (n+1)
    rw [show 3*(n+1)+1 = 3*n+4 by omega, pos_expansion, Nat.cast_add, Nat.cast_one] at h
    apply (eq_div_iff (by positivity)).2
    calc
      _ = (3*((n:ℚ)+1)+1)*PowerSeries.coeff (n+1) A := by ring
      _ = _ := h
  · intro n
    have h := (hcoef A hA n).trans (signed_expansion n)
    rw [← h]
    field_simp [show (3*(n:ℚ)+1) ≠ 0 by positivity]

end T255673

theorem OMA.solution : type_of% @OMA.S_oeis_a255673.main := by
  apply T255673.assemble
  intro A hA n
  simpa only [Nat.cast_one, pow_one, one_mul] using
    T255673.pow_coeff_formula T255673.weighted_coeff A hA n 1

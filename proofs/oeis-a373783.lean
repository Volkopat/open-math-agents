import OMAStatements.S_oeis_a373783
import Mathlib

/-!
# A373783: a recurrence for labeled seating arrangements

Credit: @VestigeClub.
Source: https://oeis.org/A373783 (Enrique Navarrete; recurrence conjectured by
Pontus von Brömssen).

The finite seating sum is the coefficient series
`X * (1 + X + X²)² * F(X³ * (1 + X))`, where
`F = ∑ (k + 1)! X^k`. The two end gaps give the squared factor; each internal
gap contributes either three or four seats. The factorial coefficient counts
the left-to-right orders of the people. We prove this coefficient identity,
substitute into `X² F' + (2X - 1)F + 1 = 0`, and extract the recurrence.
-/


namespace SeatingArrangements
open PowerSeries

noncomputable def factorialSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => ((n + 1).factorial : ℚ)

 theorem factorial_ode :
    X ^ 2 * derivative ℚ factorialSeries + (2 * X - 1) * factorialSeries + 1 = 0 := by
  rw [show (2 * X - 1) * factorialSeries = X * factorialSeries + X * factorialSeries - factorialSeries by ring]
  ext n
  rcases n with _ | n
  · norm_num [factorialSeries]
  rcases n with _ | n
  · norm_num [factorialSeries, coeff_X_pow_mul', coeff_succ_X_mul, coeff_derivative]
  · simp [factorialSeries, coeff_X_pow_mul', coeff_succ_X_mul, coeff_derivative, Nat.factorial_succ]
    ring

end SeatingArrangements

namespace SeatingArrangements
open PowerSeries
noncomputable def S : PowerSeries ℚ := 1 + X + X^2
noncomputable def Q : PowerSeries ℚ := X^3 * (1+X)
noncomputable def G : PowerSeries ℚ := X * S^2 * factorialSeries.subst Q
noncomputable def D : PowerSeries ℚ := X^4 * (1+X)^2 * S
noncomputable def E : PowerSeries ℚ :=
  (2*Q-1)*(3+4*X)*S - X^3*(1+X)^2*(1+3*X+5*X^2)
noncomputable def H : PowerSeries ℚ := X*(3+4*X)*S^3

theorem Q_subst : HasSubst Q := HasSubst.of_constantCoeff_zero' (by simp [Q])
theorem Q_derivative : derivative ℚ Q = X^2*(3+4*X) := by
  simp [Q, Derivation.leibniz, derivative_pow]
  ring

theorem S_derivative : derivative ℚ S = 1+2*X := by
  simp [S, derivative_pow]

theorem substituted_factorial_ode :
    Q^2 * (derivative ℚ factorialSeries).subst Q +
      (2*Q-1)*factorialSeries.subst Q + 1 = 0 := by
  have h := congrArg (substAlgHom Q_subst) factorial_ode
  simpa only [map_add, map_mul, map_sub, map_pow, map_ofNat, map_one, map_zero,
    substAlgHom_X, coe_substAlgHom] using h

theorem G_ode : D * derivative ℚ G + E*G + H = 0 := by
  have hS : S ≠ 0 := by
    intro h
    have := congrArg constantCoeff h
    norm_num [S] at this
  have hX : (X : PowerSeries ℚ) ≠ 0 := X_ne_zero
  apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 3 hX) hS)
  rw [mul_zero]
  calc
    (X^3*S)*(D*derivative ℚ G+E*G+H) =
        X^4*(3+4*X)*S^4 *
          (Q^2 * (derivative ℚ factorialSeries).subst Q +
           (2*Q-1)*factorialSeries.subst Q+1) := by
      simp only [G, Derivation.leibniz, derivative_pow, derivative_X, derivative_subst Q_subst,
        S_derivative, Q_derivative]
      dsimp [D, E, H, Q, S]
      ring
    _ = 0 := by rw [substituted_factorial_ode]; ring

end SeatingArrangements

namespace SeatingArrangements
open PowerSeries

 theorem coeff_binomial (k n : ℕ) :
    coeff n ((1+X : PowerSeries ℚ)^k) = (k.choose n : ℚ) := by
  have h : (1+X : PowerSeries ℚ)^k = (((1 : Polynomial ℚ)+Polynomial.X)^k).toPowerSeries := by simp
  rw [h, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

 theorem Q_power (k : ℕ) : Q^k = X^(3*k)*(1+X)^k := by
  simp [Q, mul_pow, pow_mul]

 theorem coeff_Q_power_zero (k n : ℕ) (h : n < k) : coeff n (Q^k) = 0 := by
  rw [Q_power, coeff_X_pow_mul']
  simp [show ¬ 3*k ≤ n by omega]

 theorem coeff_subst_trunc (n m : ℕ) (hm : m ≤ n) :
    coeff m (factorialSeries.subst Q) =
      ∑ k ∈ Finset.range (n+1), ((k+1).factorial : ℚ) * coeff m (Q^k) := by
  rw [coeff_subst' Q_subst]
  simp only [factorialSeries, coeff_mk, smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro k hk
  apply Finset.mem_range.mpr
  by_contra hn
  have hz := coeff_Q_power_zero k m (by omega)
  exact hk (by simp [hz])

 theorem prefactor_Q_power (k : ℕ) :
    X*S^2*Q^k = ∑ l : Fin 3, ∑ r : Fin 3,
      X^(1+3*k+l.val+r.val)*(1+X)^k := by
  rw [Q_power]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
  simp only [S]
  simp only [pow_add, pow_one, pow_zero]
  ring

 theorem coeff_shift_binomial (n d k : ℕ) :
    coeff n (X^d*(1+X : PowerSeries ℚ)^k) =
      ∑ j ∈ Finset.range (k+1), if n=d+j then (k.choose j : ℚ) else 0 := by
  rw [coeff_X_pow_mul']
  split
  next h =>
    rw [coeff_binomial]
    by_cases hj : n-d < k+1
    · rw [Finset.sum_eq_single (n-d)]
      · rw [if_pos (show n=d+(n-d) by omega)]
      · intro b hb hne
        simp [show n ≠ d+b by omega]
      · intro hn
        exact False.elim (hn (Finset.mem_range.mpr hj))
    · rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp only [Nat.cast_zero]
      symm
      apply Finset.sum_eq_zero
      intro j hj'
      simp [show n ≠ d+j by have := Finset.mem_range.mp hj'; omega]
  next h =>
    symm
    apply Finset.sum_eq_zero
    intro j hj
    simp [show n ≠ d+j by omega]

 theorem coeff_prefactor_Q_power (n k : ℕ) :
    coeff n (X*S^2*Q^k) = ∑ l : Fin 3, ∑ r : Fin 3,
      ∑ j ∈ Finset.range (k+1), if n=1+3*k+l.val+r.val+j then (k.choose j : ℚ) else 0 := by
  rw [prefactor_Q_power]
  simp only [map_sum, coeff_shift_binomial]

end SeatingArrangements

namespace SeatingArrangements
open PowerSeries

def count (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, (k+1).factorial *
    (∑ l : Fin 3, ∑ r : Fin 3, ∑ j ∈ Finset.range (k+1),
      if n=1+3*k+l.val+r.val+j then k.choose j else 0)

theorem coeff_G_trunc (n : ℕ) :
    coeff n G = ∑ k ∈ Finset.range (n+1),
      ((k+1).factorial : ℚ) * coeff n (X*S^2*Q^k) := by
  classical
  have htrunc : coeff n G = coeff n
      (X*S^2*(∑ k ∈ Finset.range (n+1), ((k+1).factorial : ℚ) • Q^k)) := by
    rw [G, coeff_mul, coeff_mul]
    apply Finset.sum_congr rfl
    intro ij hij
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [coeff_subst_trunc n ij.2 (by have := Finset.HasAntidiagonal.mem_antidiagonal.mp hij; omega)]
  rw [htrunc, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_smul_comm, map_smul, smul_eq_mul]

theorem coeff_G (n : ℕ) : coeff n G = (count n : ℚ) := by
  classical
  rw [coeff_G_trunc, Finset.sum_range_succ]
  have hz : coeff n (X*S^2*Q^n) = 0 := by
    rw [coeff_prefactor_Q_power]
    apply Finset.sum_eq_zero
    intro l hl
    apply Finset.sum_eq_zero
    intro r hr
    apply Finset.sum_eq_zero
    intro j hj
    simp [show n ≠ 1+3*n+l.val+r.val+j by omega]
  rw [hz, mul_zero, add_zero]
  simp only [count, Nat.cast_sum, Nat.cast_mul, Nat.cast_ite, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro k hk
  rw [coeff_prefactor_Q_power]

end SeatingArrangements

namespace SeatingArrangements
open PowerSeries

theorem coeff_shift_derivative (f : PowerSeries ℚ) (n d : ℕ) (hd : d ≤ n) (hpos : 1 ≤ d) :
    coeff n (X^d*derivative ℚ f) = coeff (n-(d-1)) f * ((n : ℚ)-d+1) := by
  rw [coeff_X_pow_mul', if_pos hd, coeff_derivative]
  rw [show n-d+1 = n-(d-1) by omega]
  congr 1
  rw [Nat.cast_sub hd]

 theorem H_coeff_zero (n : ℕ) (hn : 9 ≤ n) : coeff n H = 0 := by
  have h : H = (3 : ℚ) • X + (13 : ℚ) • X^2 + (30 : ℚ) • X^3 + (45 : ℚ) • X^4 + (46 : ℚ) • X^5 +
      (33 : ℚ) • X^6 + (15 : ℚ) • X^7 + (4 : ℚ) • X^8 := by
    simp only [H, S, Algebra.smul_def, map_ofNat]
    ring
  rw [h]
  have hs : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 3 ∧ n ≠ 4 ∧ n ≠ 5 ∧ n ≠ 6 ∧ n ≠ 7 ∧ n ≠ 8 := by omega
  simp [map_add, map_smul, coeff_X, coeff_X_pow, hs.1, hs.2.1, hs.2.2.1,
    hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2.1, hs.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.2]

 theorem count_recurrence (n : ℕ) (hn : 9 ≤ n) :
    3 * (count n : ℤ) =
      -7 * count (n-1) - 7 * count (n-2) + ((n : ℤ)-2) * count (n-3) +
      3 * ((n : ℤ)+1) * count (n-4) + 4 * ((n : ℤ)-1) * count (n-5) +
      3 * ((n : ℤ)-3) * count (n-6) + ((n : ℤ)-4) * count (n-7) := by
  have h := G_ode
  have he : D*derivative ℚ G+E*G+H =
      X^4*derivative ℚ G + (3 : ℚ) • (X^5*derivative ℚ G) + (4 : ℚ) • (X^6*derivative ℚ G) +
      (3 : ℚ) • (X^7*derivative ℚ G) + X^8*derivative ℚ G - (3 : ℚ) • G - (7 : ℚ) • (X*G) -
      (7 : ℚ) • (X^2*G) + X^3*G + (15 : ℚ) • (X^4*G) + (16 : ℚ) • (X^5*G) + (9 : ℚ) • (X^6*G) +
      (3 : ℚ) • (X^7*G) + H := by
    simp only [D, E, Q, S, Algebra.smul_def, map_ofNat]
    ring
  rw [he] at h
  have hc := congrArg (coeff n) h
  have h1 : 1 ≤ n := by omega
  have h2 : 2 ≤ n := by omega
  have h3 : 3 ≤ n := by omega
  have h4 : 4 ≤ n := by omega
  have h5 : 5 ≤ n := by omega
  have h6 : 6 ≤ n := by omega
  have h7 : 7 ≤ n := by omega
  have h8 : 8 ≤ n := by omega
  simp only [map_add, map_sub, map_smul, map_zero, smul_eq_mul,
    coeff_shift_derivative G n 4 h4 (by omega), coeff_shift_derivative G n 5 h5 (by omega),
    coeff_shift_derivative G n 6 h6 (by omega), coeff_shift_derivative G n 7 h7 (by omega),
    coeff_shift_derivative G n 8 h8 (by omega),
    show (X : PowerSeries ℚ)*G = X^1*G by simp,
    coeff_X_pow_mul', if_pos h1, if_pos h2, if_pos h3, if_pos h4, if_pos h5,
    if_pos h6, if_pos h7, H_coeff_zero n hn, coeff_G] at hc
  norm_num at hc
  have hr : (3 : ℚ) * count n =
      -7 * count (n-1) - 7 * count (n-2) + ((n : ℚ)-2) * count (n-3) +
      3 * ((n : ℚ)+1) * count (n-4) + 4 * ((n : ℚ)-1) * count (n-5) +
      3 * ((n : ℚ)-3) * count (n-6) + ((n : ℚ)-4) * count (n-7) := by
    linear_combination -hc
  exact_mod_cast hr

end SeatingArrangements

theorem OMA.solution : type_of% @OMA.S_oeis_a373783.main := by
  intro n hn
  exact SeatingArrangements.count_recurrence n hn

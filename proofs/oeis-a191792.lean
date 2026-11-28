import OMAStatements.S_oeis_a191792
import Mathlib

namespace A191792

noncomputable section

open PowerSeries

theorem exc_coeff (n : ℕ) : coeff n excSeries = ((excursions n).length : ℚ) := by
  simp only [excSeries, wordSeries, coeff_mk]

theorem prefix_coeff (n : ℕ) : coeff n prefixSeries = ((prefixes n).length : ℚ) := by
  simp only [prefixSeries, wordSeries, coeff_mk]

private theorem join_coeff (n : ℕ) (left right : ℕ → List Word)
    (join : Word → Word → Word) :
    ((joinWords n (fun i => left i.val) (fun i => right i.val) join).length : ℚ) =
      coeff n (wordSeries left * wordSeries right) := by
  have h : (joinWords n (fun i => left i.val) (fun i => right i.val) join).length =
      ∑ i : Fin (n+1), (left i.val).length * (right (n-i.val)).length := by
    simp [joinWords, List.length_flatMap, Fin.sum_univ_def, List.product]
  rw [h, Nat.cast_sum, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← Fin.sum_univ_eq_sum_range]
  simp [wordSeries, coeff_mk]

private theorem positive_series :
    (wordSeries fun n => if n = 0 then [] else excursions n) = excSeries - 1 := by
  ext n
  cases n with
  | zero =>
    have h0 : excursions 0 = [[]] := by rw [excursions]; rfl
    rw [map_sub, exc_coeff, h0, coeff_zero_one]
    simp [wordSeries, coeff_mk]
  | succ n => simp [wordSeries, exc_coeff, coeff_mk]

private theorem long_coeff (n : ℕ) :
    ((longTail n (fun i => excursions i.val)).length : ℚ) =
      coeff n ((excSeries-1)*excSeries) := by
  unfold longTail
  rw [← positive_series]
  exact join_coeff n (fun i => if i = 0 then [] else excursions i) excursions _

theorem excSeries_eq :
    excSeries = (1+X^2) + X^2 * (excSeries-1) * (1+X^2) * excSeries := by
  calc
    excSeries = (1+X^2) + X^2 * ((excSeries-1)*excSeries) +
        X^4 * ((excSeries-1)*excSeries) := by
      ext n
      simp only [map_add, coeff_X_pow_mul', coeff_one, coeff_X_pow]
      rw [exc_coeff]
      rw [excursions]
      simp only [List.length_append, Nat.cast_add]
      split_ifs <;> simp_all [long_coeff, List.length_map]
    _ = _ := by ring

theorem prefixSeries_eq :
    prefixSeries = excSeries + X * excSeries * prefixSeries := by
  rw [mul_assoc]
  ext n
  simp only [map_add]
  rw [prefix_coeff, exc_coeff]
  rw [prefixes]
  simp only [List.length_append, Nat.cast_add]
  cases n with
  | zero => simp [coeff_zero_X_mul]
  | succ n =>
    have hn : 1 ≤ n + 1 := by omega
    simp only [dif_pos hn, Nat.add_one_sub_one, coeff_succ_X_mul]
    congr 1
    exact join_coeff n excursions prefixes _

end
end A191792

open scoped BigOperators

namespace LatticePathSeries

open PowerSeries

/-- A rational power series is D-finite if it satisfies a homogeneous linear
differential equation over the rational polynomials with nonzero leading coefficient. -/
def DFinite (f : PowerSeries ℚ) : Prop :=
  ∃ (k : ℕ) (p : Fin (k+1) → Polynomial ℚ), p (Fin.last k) ≠ 0 ∧
    ∑ i, (p i : PowerSeries ℚ) * ((PowerSeries.derivative ℚ)^[i.val]) f = 0

theorem dFinite_of_firstOrder (f : PowerSeries ℚ) (A B S : Polynomial ℚ)
    (ha : A ≠ 0) (hs : S ≠ 0)
    (h : (A : PowerSeries ℚ) * PowerSeries.derivative ℚ f + (B : PowerSeries ℚ) * f =
      (S : PowerSeries ℚ)) : DFinite f := by
  let d := PowerSeries.derivative ℚ
  have hd := congrArg d h
  change PowerSeries.derivative ℚ _ = PowerSeries.derivative ℚ _ at hd
  simp only [map_add, Derivation.leibniz, smul_eq_mul, derivative_coe] at hd
  refine ⟨2, ![S * B.derivative - S.derivative * B,
    S * (A.derivative + B) - S.derivative * A, S * A], mul_ne_zero hs ha, ?_⟩
  simp only [Fin.sum_univ_succ, Fin.val_zero, Function.iterate_zero_apply,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_succ,
    Finset.univ_eq_empty, Finset.sum_empty, add_zero, Function.iterate_succ_apply',
    Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_add]
  linear_combination (S : PowerSeries ℚ) * hd - (S.derivative : PowerSeries ℚ) * h

theorem coeff_euler (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.X * (PowerSeries.derivative ℚ) f) =
      (n : ℚ) * PowerSeries.coeff n f := by
  cases n with
  | zero => simp
  | succ n =>
    have h := coeff_X_pow_mul ((PowerSeries.derivative ℚ) f) 1 n
    simpa [PowerSeries.coeff_derivative, mul_comm] using h

end LatticePathSeries

namespace A191792

open PowerSeries
noncomputable section

private abbrev QSeries := PowerSeries ℚ
private abbrev x := (PowerSeries.X : QSeries)
private abbrev D := (PowerSeries.derivative ℚ)

/-- Eliminate the complete-excursion series from the two combinatorial equations. -/
private theorem prefixQuadratic (C G : QSeries)
    (hC : C = (1 + x^2) + x^2 * (C-1) * (1+x^2) * C)
    (hG : G = C + x*C*G) :
    (1-2*x+x^2-2*x^3+x^4) * (G+x*G^2) = 1+x^2 := by
  let t := 1+x*G
  have ht : C*t = G := by dsimp [t]; linear_combination -hG
  have he : C*t*t = (1+x^2)*t^2 + x^2*(C*t-t)*(1+x^2)*(C*t) := by
    linear_combination t^2 * hC
  rw [ht] at he
  dsimp [t] at he
  linear_combination he

/-- The inhomogeneous formal differential equation for avoiding prefixes. -/
theorem prefixODE (C G : QSeries)
    (hC : C = (1 + x^2) + x^2 * (C-1) * (1+x^2) * C)
    (hG : G = C + x*C*G) :
    x * (1-2*x^2-5*x^4-2*x^6+x^8) * D G +
      (1-2*x-2*x^2-4*x^3-5*x^4+4*x^5-2*x^6+2*x^7+x^8)*G =
      1+2*x^2-2*x^4-x^6 := by
  let B := 1-2*x+x^2-2*x^3+x^4
  let E := B+4*x*(1+x^2)
  let Y := 1+2*x*G
  have hQ : B * Y^2 = E := by
    dsimp [E,Y,B]
    linear_combination (4*x) * prefixQuadratic C G hC hG
  have hd : D B*Y^2 + 2*B*Y*D Y = D E := by
    have hh := congrArg D hQ
    simp only [Derivation.leibniz, smul_eq_mul, PowerSeries.derivative_pow] at hh
    norm_num at hh
    linear_combination hh
  have hl : 2*B*E*D Y = (B*D E-D B*E)*Y := by
    linear_combination B*Y*hd - (D B*Y+2*B*D Y)*hQ
  have h₂ : D 2 = 0 := (D).map_natCast 2
  have h₄ : D 4 = 0 := (D).map_natCast 4
  have hdB : D B = -2+2*x-6*x^2+4*x^3 := by
    dsimp [B]
    simp [Derivation.leibniz, smul_eq_mul, h₂]
    ring
  have hdE : D E = D B + 4 + 12*x^2 := by
    dsimp only [E]
    simp [Derivation.leibniz, smul_eq_mul, h₄]
    ring
  have hdY : D Y = 2*G + 2*x*D G := by
    dsimp [Y]
    simp [Derivation.leibniz, smul_eq_mul, h₂]
    ring
  rw [hdY,hdE,hdB] at hl
  dsimp [Y,E,B] at hl
  apply mul_left_cancel₀ (a := (4 : QSeries)) (by
    intro h
    have hh := congrArg (PowerSeries.constantCoeff (R := ℚ)) h
    have hh₄ : (PowerSeries.constantCoeff (R := ℚ)) (4 : QSeries) = 4 :=
      map_natCast _ 4
    rw [hh₄, map_zero] at hh
    norm_num at hh)
  linear_combination hl

/-- The nine terms obtained by taking coefficients of the differential equation. -/
theorem prefixRecurrence (C G : QSeries)
    (hC : C = (1 + x^2) + x^2 * (C-1) * (1+x^2) * C)
    (hG : G = C + x*C*G) (n : ℕ) (hn : 8 ≤ n) :
    ((n:ℚ)+1)*coeff n G - 2*coeff (n-1) G + 2*(1-n)*coeff (n-2) G
      - 4*coeff (n-3) G + 5*(3-n)*coeff (n-4) G + 4*coeff (n-5) G
      + 2*(5-n)*coeff (n-6) G + 2*coeff (n-7) G + (n-7:ℚ)*coeff (n-8) G = 0 := by
  let H := x * D G
  have hEuler (k : ℕ) : coeff k H = (k:ℚ) * coeff k G :=
    LatticePathSeries.coeff_euler G k
  have h :
      (H - (2:ℕ) • (x^2*H) - (5:ℕ) • (x^4*H) - (2:ℕ) • (x^6*H) + x^8*H) +
      (G - (2:ℕ) • (x^1*G) - (2:ℕ) • (x^2*G) - (4:ℕ) • (x^3*G) - (5:ℕ) • (x^4*G)
       + (4:ℕ) • (x^5*G) - (2:ℕ) • (x^6*G) + (2:ℕ) • (x^7*G) + x^8*G)
       = 1 + (2:ℕ) • x^2 - (2:ℕ) • x^4 - x^6 := by
    dsimp only [H]
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    linear_combination prefixODE C G hC hG
  have hc := congrArg (coeff (R:=ℚ) n) h
  simp (disch := omega) only [map_add, map_sub, map_nsmul, coeff_X_pow_mul', if_pos,
    hEuler, coeff_one, coeff_X_pow, if_neg, Nat.cast_ofNat, Nat.cast_sub] at hc
  simp only [nsmul_eq_mul,Nat.cast_ofNat] at hc
  linear_combination hc

/-- The inhomogeneous equation gives a homogeneous equation over rational polynomials. -/
theorem prefixDFinite (C G : QSeries)
    (hC : C = (1 + x^2) + x^2 * (C-1) * (1+x^2) * C)
    (hG : G = C + x*C*G) : LatticePathSeries.DFinite G := by
  let z := (Polynomial.X : Polynomial ℚ)
  let A := z*(1-2*z^2-5*z^4-2*z^6+z^8)
  let B := 1-2*z-2*z^2-4*z^3-5*z^4+4*z^5-2*z^6+2*z^7+z^8
  let S := 1+2*z^2-2*z^4-z^6
  apply LatticePathSeries.dFinite_of_firstOrder G A B S
  · intro h
    have hh := congrArg (Polynomial.eval (1:ℚ)) h
    norm_num [A,z] at hh
  · intro h
    have hh := congrArg (Polynomial.eval (0:ℚ)) h
    norm_num [S,z] at hh
  · have castNum (n : ℕ) [n.AtLeastTwo] :
        ((OfNat.ofNat n : Polynomial ℚ) : QSeries) = OfNat.ofNat n :=
      map_natCast (Polynomial.coeToPowerSeries.ringHom (R := ℚ)) n
    simp only [A,B,S,z,Polynomial.coe_one,Polynomial.coe_mul,Polynomial.coe_pow,
      Polynomial.coe_add,Polynomial.coe_sub,Polynomial.coe_X,castNum]
    exact prefixODE C G hC hG

end
end A191792

theorem OMA.solution : type_of% @OMA.S_oeis_a191792.main := by
  obtain ⟨hc, hg⟩ := And.intro A191792.excSeries_eq A191792.prefixSeries_eq
  refine ⟨A191792.prefixDFinite _ _ hc hg, ?_⟩
  intro n hn
  simpa only [A191792.prefix_coeff, OMA.S_oeis_a191792.a] using
    A191792.prefixRecurrence _ _ hc hg n hn

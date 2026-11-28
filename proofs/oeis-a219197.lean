import OMAStatements.S_oeis_a219197

/-!
# A219197: an integral square root with no coefficient congruent to three modulo four

Credit: @CubeJerry

The original finite binomial sum is a diagonal of Fibonacci-polynomial squares.
An integral Lagrange coefficient formula identifies its generating function using
G = 1 + X * G^3. Normalizing the given integral square root gives B = G^2 * C and
C^2 * (1 - 4 * (G - 1)^2) = 1. Reduction modulo four yields a self-recurrence
under X -> X^2, and strong induction on binary indices excludes residue three.

The related A183161 conjecture has a public proof by Chain.Ren (2026-11-27):
https://github.com/Asakitan/oeis-a183161/blob/c5d741da486316dae89469804fd65b47b905ce38/PROOF.md
That proof concerns A183161/A218622. The present proof treats A219197 directly,
with the exact A199033 finite sum in the registered statement.
-/


open PowerSeries

namespace A219197Ternary

noncomputable def F : PowerSeries ℤ := X * (1 - X) ^ 2

lemma F_zero : constantCoeff F = 0 := by simp [F]

lemma F_one : coeff 1 F = 1 := by
  change coeff (0 + 1) (X * (1 - X) ^ 2 : PowerSeries ℤ) = 1
  rw [coeff_succ_X_mul]
  simp

noncomputable def U : PowerSeries ℤ :=
  F.substInvOfIsUnit (by rw [F_one]; exact isUnit_one)

lemma U_zero : constantCoeff U = 0 := by simp [U]

lemma U_hasSubst : HasSubst U := by
  exact HasSubst.substInvOfIsUnit _ _

lemma F_subst_U : F.subst U = X := by
  exact subst_substInvOfIsUnit_right F F_zero _

lemma U_subst_F : U.subst F = X := by
  exact subst_substInvOfIsUnit_left F F_zero _

lemma U_eq : U * (1 - U) ^ 2 = X := by
  have h := subst_substInvOfIsUnit_right F F_zero
    (show IsUnit (coeff 1 F) by rw [F_one]; exact isUnit_one)
  change F.subst U = X at h
  rw [← coe_substAlgHom U_hasSubst] at h
  change substAlgHom U_hasSubst (X * (1 - X) ^ 2 : PowerSeries ℤ) = X at h
  simpa only [map_mul, map_pow, map_sub, map_one, substAlgHom_X] using h

noncomputable def G : PowerSeries ℤ := (1 - U).invOfUnit 1

lemma G_zero : constantCoeff G = 1 := by simp [G]

lemma G_inverse : (1 - U) * G = 1 := by
  exact mul_invOfUnit _ 1 (by simp [U_zero])

lemma G_eq : G = 1 + X * G ^ 3 := by
  have hx : X * G ^ 3 = U * G := by
    rw [← U_eq]
    calc
      U * (1 - U) ^ 2 * G ^ 3 = U * G * ((1 - U) * G) ^ 2 := by ring
      _ = U * G := by rw [G_inverse]; ring
  rw [hx]
  linear_combination G_inverse

end A219197Ternary

open Finset PowerSeries
namespace A219197Binomial

lemma coeff_X_mul (p : PowerSeries ℤ) (n : ℕ) : coeff (n + 1) (X * p) = coeff n p := by
  simpa only [pow_one] using coeff_X_pow_mul p 1 n

lemma coeff_mul_X (p : PowerSeries ℤ) (n : ℕ) : coeff (n + 1) (p * X) = coeff n p := by
  simpa only [pow_one] using coeff_mul_X_pow p 1 n

noncomputable def fib : ℕ → PowerSeries ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => fib (n + 1) + X * fib n

lemma fib_zero : fib 0 = 1 := rfl
lemma fib_one : fib 1 = 1 := rfl
lemma fib_add_two (n : ℕ) : fib (n + 2) = fib (n + 1) + X * fib n := rfl

lemma fib_coeff (m k : ℕ) : coeff k (fib m) = ((m - k).choose k : ℤ) := by
  induction m using Nat.twoStepInduction generalizing k with
  | zero =>
    cases k <;> simp [fib]
  | one =>
    cases k with
    | zero => simp [fib]
    | succ k => cases k <;> simp [fib]
  | more m ih₀ ih₁ =>
    cases k with
    | zero =>
      rw [fib_add_two, map_add, coeff_zero_X_mul, add_zero, ih₁]
      simp
    | succ k =>
      rw [fib_add_two, map_add, coeff_X_mul, ih₁, ih₀]
      by_cases hk : k ≤ m
      · have h₁ : m + 1 - (k + 1) = m - k := by omega
        have h₂ : m + 2 - (k + 1) = m - k + 1 := by omega
        rw [h₁, h₂, Nat.choose_succ_succ, Nat.cast_add]
        ring
      · have h₁ : m - k = 0 := by omega
        have h₂ : m + 1 - (k + 1) = 0 := by omega
        have h₃ : m + 2 - (k + 1) < k + 1 := by omega
        rw [h₁, h₂, Nat.choose_zero_succ, Nat.choose_eq_zero_of_lt h₃]
        have hk₀ : 0 < k := by omega
        rw [Nat.choose_eq_zero_of_lt hk₀]
        norm_num

lemma fib_add (m n : ℕ) :
    fib (m + n + 2) = fib (m + 1) * fib (n + 1) + X * fib m * fib n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [fib_add_two, fib_zero, fib_one]
  | one =>
    simp only [fib_add_two, fib_one, fib_zero]
    norm_num [fib_one]
    ring
  | more n ih₀ ih₁ =>
    have h : m + (n + 2) + 2 = (m + n + 2) + 2 := by omega
    rw [h, fib_add_two]
    have h' : m + n + 2 + 1 = m + (n + 1) + 2 := by omega
    rw [h', ih₁, ih₀]
    simp only [show n + 1 + 1 = n + 2 from by omega,
      show n + 2 + 1 = (n + 1) + 2 from by omega, fib_add_two]
    ring

noncomputable def geo : PowerSeries ℤ := PowerSeries.mk 1
noncomputable def evenGeo : PowerSeries ℤ := PowerSeries.subst (X ^ 2) geo

lemma geo_mul : geo * (1 - X) = 1 := mk_one_mul_one_sub_eq_one ℤ

lemma evenGeo_mul : evenGeo * (1 - X ^ 2) = 1 := by
  have hx : HasSubst (X ^ 2 : PowerSeries ℤ) := HasSubst.X_pow (by decide)
  have h := congrArg (PowerSeries.substAlgHom (R := ℤ) hx) geo_mul
  simpa only [map_mul, map_sub, map_one, substAlgHom_X, coe_substAlgHom, evenGeo] using h

lemma evenGeo_add : evenGeo * (1 + X) = geo := by
  calc
    evenGeo * (1 + X) = evenGeo * (1 - X ^ 2) * geo := by
      calc
        _ = evenGeo * (1 + X) * (geo * (1 - X)) := by rw [geo_mul, mul_one]
        _ = _ := by ring
    _ = geo := by rw [evenGeo_mul, one_mul]

lemma constant_evenGeo : constantCoeff evenGeo = 1 := by
  have h := congrArg constantCoeff evenGeo_mul
  simpa using h

lemma coeff_geo_pow (q n : ℕ) : coeff n (geo ^ (q + 1)) = ((q + n).choose n : ℤ) := by
  rw [geo, mk_one_pow_eq_mk_choose_add, coeff_mk]
  congr 1
  exact Nat.choose_symm_add

lemma coeff_diagonal (q n : ℕ) :
    coeff n ((fib (q + n)) ^ 2) = coeff n (evenGeo * geo ^ (2 * q)) := by
  induction n with
  | zero =>
    simp only [coeff_zero_eq_constantCoeff_apply, map_pow, map_mul, constant_evenGeo,
      one_mul, Nat.add_zero]
    rw [← coeff_zero_eq_constantCoeff_apply, fib_coeff]
    simp [geo]
  | succ n ih =>
    have h := congrArg (coeff (n + 1)) (fib_add (q + n) (q + n))
    have hi : q + n + (q + n) + 2 = 2 * (q + n + 1) := by omega
    rw [hi, map_add] at h
    simp only [mul_assoc, ← sq, coeff_X_mul, fib_coeff] at h
    have hs : 2 * (q + n + 1) - (n + 1) = 2 * q + n + 1 := by omega
    rw [hs] at h
    have hg : (evenGeo * geo ^ (2 * q)) * (1 + X) = geo ^ (2 * q + 1) := by
      calc
        _ = (evenGeo * (1 + X)) * geo ^ (2 * q) := by ring
        _ = _ := by rw [evenGeo_add, pow_succ']
    have hgc := congrArg (coeff (n + 1)) hg
    rw [mul_add, mul_one, map_add, coeff_mul_X, coeff_geo_pow] at hgc
    rw [ih] at h
    have hn : q + (n + 1) = q + n + 1 := by omega
    rw [hn]
    simp only [Nat.add_assoc] at h hgc ⊢
    linarith

lemma finite_bridge (n : ℕ) :
    coeff n (evenGeo * geo ^ (2 * n + 2)) =
      ((∑ k ∈ range (n + 1), (n + k + 1).choose (n - k) *
        (2 * n - k + 1).choose k : ℕ) : ℤ) := by
  have h := coeff_diagonal (n + 1) n
  have h₁ : n + 1 + n = 2 * n + 1 := by omega
  have h₂ : 2 * (n + 1) = 2 * n + 2 := by omega
  rw [h₁, h₂] at h
  rw [← h, sq, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  push_cast
  apply sum_congr rfl
  intro k hk
  simp only [fib_coeff]
  have hk' : k ≤ n := by simpa only [mem_range, Nat.lt_succ_iff] using hk
  have ha : 2 * n + 1 - (n - k) = n + k + 1 := by omega
  have hb : 2 * n + 1 - k = 2 * n - k + 1 := by omega
  rw [ha, hb]
  ring

end A219197Binomial

open PowerSeries
open scoped PowerSeries

namespace A219197Lagrange

abbrev PS := PowerSeries ℤ

lemma inverse_power_derivative (h : PSˣ) (m : ℕ) :
    derivative ℤ ((↑h⁻¹ : PS) ^ (m + 1)) =
      -((m + 1 : ℕ) : PS) * (↑h⁻¹ : PS) ^ (m + 2) * derivative ℤ (↑h : PS) := by
  rw [derivative_pow, derivative_inv]
  simp only [Nat.add_sub_cancel]
  push_cast
  ring

lemma unit_residue_zero (h : PSˣ) (m : ℕ) :
    coeff (m + 1) ((↑h⁻¹ : PS) ^ (m + 1)) +
      coeff m ((↑h⁻¹ : PS) ^ (m + 2) * derivative ℤ (↑h : PS)) = 0 := by
  have hd := congrArg (coeff m) (inverse_power_derivative h m)
  rw [coeff_derivative] at hd
  have hc : coeff m
      (-((m + 1 : ℕ) : PS) * (↑h⁻¹ : PS) ^ (m + 2) * derivative ℤ (↑h : PS)) =
      -((m + 1 : ℕ) : ℤ) *
        coeff m ((↑h⁻¹ : PS) ^ (m + 2) * derivative ℤ (↑h : PS)) := by
    rw [mul_assoc, ← map_natCast (C (R := ℤ)), ← map_neg, coeff_C_mul]
  rw [hc] at hd
  have hn : ((m + 1 : ℕ) : ℤ) ≠ 0 := by omega
  apply (mul_eq_zero.mp (show ((m + 1 : ℕ) : ℤ) *
      (coeff (m + 1) ((↑h⁻¹ : PS) ^ (m + 1)) +
        coeff m ((↑h⁻¹ : PS) ^ (m + 2) * derivative ℤ (↑h : PS))) = 0 by
    push_cast at hd ⊢
    linear_combination hd)).resolve_left hn

lemma unit_kernel (h : PSˣ) (m : ℕ) :
    coeff m (((↑h : PS) + X * derivative ℤ (↑h : PS)) * (↑h⁻¹ : PS) ^ (m + 1)) =
      if m = 0 then 1 else 0 := by
  have heq : ((↑h : PS) + X * derivative ℤ (↑h : PS)) * (↑h⁻¹ : PS) ^ (m + 1) =
      (↑h⁻¹ : PS) ^ m +
        X * ((↑h⁻¹ : PS) ^ (m + 1) * derivative ℤ (↑h : PS)) := by
    rw [add_mul, pow_succ]
    have hinv : (↑h : PS) * (↑h⁻¹ : PS) = 1 := h.val_inv
    calc
      _ = (↑h⁻¹ : PS) ^ m * ((↑h : PS) * (↑h⁻¹ : PS)) +
          X * ((↑h⁻¹ : PS) ^ m * (↑h⁻¹ : PS) * derivative ℤ (↑h : PS)) := by ring
      _ = _ := by rw [hinv]; ring
  rw [heq]
  cases m with
  | zero => simp
  | succ m =>
    rw [map_add]
    rw [mul_comm X, coeff_succ_mul_X]
    simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.reduceAdd,
      Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false] using unit_residue_zero h m

lemma kernel_monomial (h : PSˣ) (n k : ℕ) :
    coeff n ((X * (↑h : PS)) ^ k * derivative ℤ (X * (↑h : PS)) *
      (↑h⁻¹ : PS) ^ (n + 1)) = if n = k then 1 else 0 := by
  have hd : derivative ℤ (X * (↑h : PS)) = (↑h : PS) + X * derivative ℤ (↑h : PS) := by
    simp only [Derivation.leibniz, derivative_X, smul_eq_mul]
    ring
  rw [hd, mul_pow]
  by_cases hkn : k ≤ n
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkn
    have hp : (↑h : PS)^k * (↑h⁻¹ : PS)^(k + m + 1) = (↑h⁻¹ : PS)^(m+1) := by
      have hinv : (↑h : PS) * (↑h⁻¹ : PS) = 1 := h.val_inv
      rw [Nat.add_assoc, pow_add]
      rw [← mul_assoc, ← mul_pow, hinv, one_pow, one_mul]
    have heq : X^k * (↑h : PS)^k * ((↑h : PS) + X * derivative ℤ (↑h : PS)) *
        (↑h⁻¹ : PS)^(k + m + 1) =
        X^k * (((↑h : PS) + X * derivative ℤ (↑h : PS)) * (↑h⁻¹ : PS)^(m+1)) := by
      calc
        _ = X^k * (((↑h : PS) + X * derivative ℤ (↑h : PS)) *
            ((↑h : PS)^k * (↑h⁻¹ : PS)^(k+m+1))) := by ring
        _ = _ := by rw [hp]
    rw [heq, Nat.add_comm k m, coeff_X_pow_mul, unit_kernel]
    simp only [Nat.add_eq_right]
  · rw [show X^k * (↑h : PS)^k * ((↑h : PS) + X * derivative ℤ (↑h : PS)) *
        (↑h⁻¹ : PS)^(n+1) = X^k *
        ((↑h : PS)^k * ((↑h : PS) + X * derivative ℤ (↑h : PS)) * (↑h⁻¹ : PS)^(n+1)) by ring,
      coeff_X_pow_mul', if_neg hkn, if_neg (by omega)]

lemma coeff_subst_bounded (g H : PS) (n i : ℕ) (hi : i ≤ n) :
    coeff i (g.subst (X * H)) =
      coeff i (∑ k ∈ Finset.range (n+1), C (coeff k g) * (X * H)^k) := by
  have hF : HasSubst (X * H) := PowerSeries.HasSubst.of_constantCoeff_zero
    (show constantCoeff (X * H) = 0 by simp)
  rw [coeff_subst' hF]
  simp only [smul_eq_mul, map_sum, coeff_C_mul]
  apply finsum_eq_sum_of_support_subset
  intro k hk
  change coeff k g * coeff i ((X * H)^k) ≠ 0 at hk
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra hkn
  have hki : ¬ k ≤ i := by omega
  simp [mul_pow, coeff_X_pow_mul', hki] at hk

lemma coeff_mul_congr_bounded (f g K : PS) (n : ℕ)
    (h : ∀ i ≤ n, coeff i f = coeff i g) :
    coeff n (f*K) = coeff n (g*K) := by
  rw [coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  rintro ⟨i,j⟩ hij
  rw [h i (by have := Finset.HasAntidiagonal.mem_antidiagonal.mp hij; omega)]

lemma lagrange_coefficient (g : PS) (h : PSˣ) (n : ℕ) :
    coeff n (g.subst (X * (↑h : PS)) * derivative ℤ (X * (↑h : PS)) *
      (↑h⁻¹ : PS)^(n+1)) = coeff n g := by
  let T : PS := ∑ k ∈ Finset.range (n+1), C (coeff k g) * (X * (↑h : PS))^k
  have ht : coeff n (g.subst (X * (↑h : PS)) *
      (derivative ℤ (X * (↑h : PS)) * (↑h⁻¹ : PS)^(n+1))) =
      coeff n (T * (derivative ℤ (X * (↑h : PS)) * (↑h⁻¹ : PS)^(n+1))) := by
    apply coeff_mul_congr_bounded
    intro i hi
    exact coeff_subst_bounded g (↑h : PS) n i hi
  rw [mul_assoc, ht]
  simp only [T, Finset.sum_mul, map_sum, mul_assoc, coeff_C_mul]
  simp_rw [← mul_assoc ((X * (↑h : PS))^_) (derivative ℤ (X * (↑h : PS)))
      ((↑h⁻¹ : PS)^(n+1)), kernel_monomial]
  simp

theorem lagrange_diagonal (P U : PS) (h : PSˣ)
    (hU : constantCoeff U = 0)
    (hUF : U.subst (X * (↑h : PS)) = X) (n : ℕ) :
    coeff n (P.subst U * derivative ℤ U) =
      coeff n (P * (↑h⁻¹ : PS)^(n+1)) := by
  have hUs : HasSubst U := PowerSeries.HasSubst.of_constantCoeff_zero hU
  have hFs : HasSubst (X * (↑h : PS)) := PowerSeries.HasSubst.of_constantCoeff_zero
    (show constantCoeff (X * (↑h : PS)) = 0 by simp)
  have hdiff : (derivative ℤ U).subst (X * (↑h : PS)) *
      derivative ℤ (X * (↑h : PS)) = 1 := by
    rw [← derivative_subst hFs, hUF, derivative_X]
  have hcomp : PowerSeries.subst ((X : PS) * (↑h : PS))
      ((P.subst U : PS) * derivative ℤ U) *
      derivative ℤ (X * (↑h : PS)) = P := by
    rw [subst_mul hFs, subst_comp_subst_apply hUs hFs, hUF, X_subst,
      mul_assoc, hdiff, mul_one]
  have hlag := lagrange_coefficient (P.subst U * derivative ℤ U) h n
  rw [hcomp] at hlag
  exact hlag.symm

noncomputable def oneMinusXUnit : PSˣ :=
  Units.mkOfMulEqOne (1-X) (PowerSeries.mk 1) (by
    rw [mul_comm]
    exact mk_one_mul_one_sub_eq_one ℤ)

@[simp] lemma oneMinusXUnit_val : (oneMinusXUnit : PS) = 1-X := rfl
@[simp] lemma oneMinusXUnit_inv_val : (↑oneMinusXUnit⁻¹ : PS) = PowerSeries.mk 1 := rfl

noncomputable def evenGeo : PS := (PowerSeries.mk 1 : PS).subst (X^2)

lemma evenGeo_mul (U : PS) (hU : constantCoeff U = 0) :
    evenGeo.subst U * (1-U^2) = 1 := by
  have hUs : HasSubst U := PowerSeries.HasSubst.of_constantCoeff_zero hU
  have hX2 : HasSubst ((X : PS)^2) := .X_pow (by decide)
  have hbase : evenGeo * (1-X^2) = 1 := by
    have hh := congrArg (substAlgHom (R := ℤ) hX2) (mk_one_mul_one_sub_eq_one ℤ)
    simpa only [map_mul, map_sub, map_one, substAlgHom_X, coe_substAlgHom, evenGeo] using hh
  have hh := congrArg (substAlgHom (R := ℤ) hUs) hbase
  simpa only [map_mul, map_sub, map_one, map_pow, substAlgHom_X, coe_substAlgHom] using hh

theorem diagonal_formula (U : PS) (hU : constantCoeff U = 0)
    (hUF : U.subst ((X : PS)*(1-X)^2) = X) (n : ℕ) :
    coeff n (evenGeo.subst U * derivative ℤ U) =
      coeff n (evenGeo * (PowerSeries.mk 1 : PS)^(2*n+2)) := by
  have hh := lagrange_diagonal evenGeo U (oneMinusXUnit^2) hU (by
    simpa only [Units.val_pow_eq_pow_val, oneMinusXUnit_val] using hUF) n
  simpa only [Units.inv_pow_eq_pow_inv, oneMinusXUnit_inv_val,
    ← pow_mul, Nat.mul_add, Nat.mul_one] using hh

theorem diagonal_series_identity (U G D : PS)
    (hU : constantCoeff U = 0)
    (hUF : U.subst ((X : PS)*(1-X)^2) = X)
    (hFU : PowerSeries.subst U ((X : PS)*(1-X)^2) = X)
    (hG : G*(1-U) = 1)
    (hD : ∀ n, coeff n D = coeff n (evenGeo * (PowerSeries.mk 1 : PS)^(2*n+2))) :
    D * (1 - 4*(G-1)^2) = G^4 := by
  have hUs : HasSubst U := PowerSeries.HasSubst.of_constantCoeff_zero hU
  have hseries : D = evenGeo.subst U * derivative ℤ U := by
    ext n
    rw [hD, diagonal_formula U hU hUF]
  have hFder : derivative ℤ ((X : PS)*(1-X)^2) = (1-X)*(1-3*X) := by
    simp only [Derivation.leibniz, map_sub, derivative_one, derivative_X,
      derivative_pow, smul_eq_mul]
    norm_num
    ring
  have hdiff : derivative ℤ U * ((1-U)*(1-3*U)) = 1 := by
    have hh := congrArg (derivative ℤ) hFU
    rw [derivative_subst hUs, hFder, derivative_X] at hh
    have hs : PowerSeries.subst U ((1-X)*(1-3*X) : PS) = (1-U)*(1-3*U) := by
      rw [← coe_substAlgHom hUs]
      simp only [map_mul, map_sub, map_one, map_ofNat, substAlgHom_X]
    rw [hs, mul_comm] at hh
    exact hh
  have hdenom : D * ((1-U)^2*(1+U)*(1-3*U)) = 1 := by
    calc
      _ = (evenGeo.subst U * (1-U^2)) *
          (derivative ℤ U * ((1-U)*(1-3*U))) := by rw [hseries]; ring
      _ = 1 := by rw [evenGeo_mul U hU, hdiff, one_mul]
  have hsmall : (G-1)*(1-U) = U := by linear_combination hG
  have hcancel : (1 - 4*(G-1)^2)*(1-U)^2 = (1+U)*(1-3*U) := by
    calc
      _ = (1-U)^2 - 4*((G-1)*(1-U))^2 := by ring
      _ = _ := by rw [hsmall]; ring
  have hG4 : (1-U)^4*G^4 = 1 := by
    rw [← mul_pow, mul_comm (1-U), hG, one_pow]
  calc
    D * (1 - 4*(G-1)^2) = (D * (1 - 4*(G-1)^2)) * ((1-U)^4*G^4) := by
      rw [hG4, mul_one]
    _ = (D*(1-U)^2*((1-4*(G-1)^2)*(1-U)^2))*G^4 := by ring
    _ = (D*((1-U)^2*(1+U)*(1-3*U)))*G^4 := by rw [hcancel]; ring
    _ = G^4 := by rw [hdenom, one_mul]

end A219197Lagrange

open PowerSeries
namespace A219197Frobenius

noncomputable def red : ZMod 4 →+* ZMod 2 := ZMod.castHom (by norm_num) (ZMod 2)

lemma frobenius_two (f : PowerSeries (ZMod 2)) :
    f ^ 2 = expand 2 (by norm_num) f := by
  have hf : frobenius (ZMod 2) 2 = RingHom.id (ZMod 2) := by
    ext a
    change a ^ 2 = a
    have hall : ∀ a : ZMod 2, a ^ 2 = a := by decide
    exact hall a
  have h := MvPowerSeries.map_frobenius_expand (R := ZMod 2)
    (σ := Unit) 2 (by norm_num) (f := f)
  rw [hf] at h
  simpa only [PowerSeries.expand, MvPowerSeries.map_id, RingHom.id_apply] using h.symm

lemma exists_half (a : ZMod 4) (ha : red a = 0) : ∃ b : ZMod 4, a = 2 * b := by
  have h : ∀ a : ZMod 4, red a = 0 → ∃ b : ZMod 4, a = 2 * b := by decide
  exact h a ha

lemma exists_series_half (f : PowerSeries (ZMod 4))
    (hf : PowerSeries.map red f = 0) : ∃ g : PowerSeries (ZMod 4), f = 2 * g := by
  classical
  have hn (n : ℕ) : ∃ b : ZMod 4, coeff n f = 2 * b := by
    apply exists_half
    have h := congrArg (coeff n) hf
    simpa using h
  choose b hb using hn
  refine ⟨PowerSeries.mk b, ?_⟩
  ext n
  change coeff n f = coeff n (C (2 : ZMod 4) * PowerSeries.mk b)
  simpa only [coeff_C_mul, coeff_mk] using hb n

lemma square_expand_difference (f : PowerSeries (ZMod 4)) :
    ∃ g : PowerSeries (ZMod 4), f ^ 2 - expand 2 (by norm_num) f = 2 * g := by
  apply exists_series_half
  rw [map_sub, map_pow, map_expand, frobenius_two, sub_self]

lemma four_eq_zero : (4 : PowerSeries (ZMod 4)) = 0 := by
  change C (4 : ZMod 4) = 0
  rw [show (4 : ZMod 4) = 0 from by decide, map_zero]

lemma double_square (f : PowerSeries (ZMod 4)) :
    2 * f ^ 2 = 2 * expand 2 (by norm_num) f := by
  obtain ⟨g, hg⟩ := square_expand_difference f
  calc
    2 * f ^ 2 = 2 * expand 2 (by norm_num) f + 2 * (f ^ 2 - expand 2 (by norm_num) f) := by ring
    _ = 2 * expand 2 (by norm_num) f + 4 * g := by rw [hg]; ring
    _ = 2 * expand 2 (by norm_num) f := by rw [four_eq_zero]; ring

lemma fourth_power (f : PowerSeries (ZMod 4)) :
    f ^ 4 = (expand 2 (by norm_num) f) ^ 2 := by
  obtain ⟨g, hg⟩ := square_expand_difference f
  have hsq : f ^ 2 = expand 2 (by norm_num) f + 2 * g := by
    exact sub_eq_iff_eq_add.mp hg |>.trans (add_comm _ _)
  calc
    f ^ 4 = (f ^ 2) ^ 2 := by ring
    _ = (expand 2 (by norm_num) f + 2 * g) ^ 2 := by rw [hsq]
    _ = (expand 2 (by norm_num) f) ^ 2 + 4 * (expand 2 (by norm_num) f * g + g ^ 2) := by ring
    _ = (expand 2 (by norm_num) f) ^ 2 := by rw [four_eq_zero]; ring

end A219197Frobenius

open PowerSeries
namespace A219197SquareShift

abbrev PS := PowerSeries ℤ
abbrev S := PowerSeries (ZMod 4)
noncomputable abbrev map2 : PS →+* PowerSeries (ZMod 2) :=
  PowerSeries.map (Int.castRingHom (ZMod 2))
noncomputable abbrev map4 : PS →+* S :=
  PowerSeries.map (Int.castRingHom (ZMod 4))

lemma four_zero_two : (4 : PowerSeries (ZMod 2)) = 0 := by
  change C (4 : ZMod 2) = 0
  rw [show (4 : ZMod 2) = 0 from by decide, map_zero]

lemma neg_one_two : (-1 : PowerSeries (ZMod 2)) = 1 := by
  have h : (-1 : ZMod 2) = 1 := by decide
  simpa only [map_neg, map_one] using
    congrArg (C : ZMod 2 →+* PowerSeries (ZMod 2)) h

lemma root_mod_two (c y : PS) (h : c ^ 2 * (1 - 4 * y ^ 2) = 1) : map2 c = 1 := by
  let : NoZeroDivisors (ZMod 2) := ⟨by decide⟩
  have hmap := congrArg map2 h
  simp only [map_mul, map_pow, map_sub, map_one, map_ofNat, four_zero_two,
    zero_mul, sub_zero, mul_one] at hmap
  rcases sq_eq_one_iff.mp hmap with hc | hc
  · exact hc
  · exact hc.trans neg_one_two

lemma exists_integral_half (f : PS) (hf : map2 f = 0) : ∃ d : PS, f = 2 * d := by
  classical
  have hn (n : ℕ) : (2 : ℤ) ∣ coeff n f := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (coeff n f) 2).mp
    have hh := congrArg (coeff n) hf
    simpa only [map2, coeff_map, Int.coe_castRingHom, map_zero] using hh
  choose d hd using hn
  refine ⟨PowerSeries.mk d, ?_⟩
  ext n
  change coeff n f = coeff n (C (2 : ℤ) * PowerSeries.mk d)
  simpa only [coeff_C_mul, coeff_mk] using hd n

lemma square_root_split (c y : PS) (h : c ^ 2 * (1 - 4 * y ^ 2) = 1) :
    ∃ d : PS, c = 1 + 2 * d ∧
      d + d ^ 2 - y ^ 2 = 4 * (d + d ^ 2) * y ^ 2 := by
  have hc := root_mod_two c y h
  obtain ⟨d, hd⟩ := exists_integral_half (c - 1) (by
    rw [map_sub, map_one, hc, sub_self])
  have hcd : c = 1 + 2 * d := by linear_combination hd
  refine ⟨d, hcd, ?_⟩
  rw [hcd] at h
  have hh : (4 : PS) * (d + d ^ 2 - y ^ 2 - 4 * (d + d ^ 2) * y ^ 2) = 0 := by
    linear_combination h
  apply sub_eq_zero.mp
  exact (mul_eq_zero.mp hh).resolve_left (by
    intro hz
    have hz0 := congrArg constantCoeff hz
    change (4 : ℤ) = 0 at hz0
    norm_num at hz0)

lemma square_shift (c y : PS) (h : c ^ 2 * (1 - 4 * y ^ 2) = 1) :
    2 * map4 c = 2 ∧
      map4 (expand 2 (by decide) c) = map4 c + 2 * (map4 y) ^ 2 := by
  obtain ⟨d, hcd, hd⟩ := square_root_split c y h
  have h4 := congrArg map4 hd
  simp only [map_add, map_pow, map_sub, map_mul, map_ofNat,
    A219197Frobenius.four_eq_zero, zero_mul] at h4
  have hcd4 := congrArg map4 hcd
  simp only [map_add, map_one, map_mul, map_ofNat] at hcd4
  constructor
  · rw [hcd4]
    calc
      2 * (1 + 2 * map4 d) = 2 + 4 * map4 d := by ring
      _ = 2 := by rw [A219197Frobenius.four_eq_zero]; ring
  · simp only [map_expand, hcd4, map_add, map_one, map_mul, map_ofNat]
    rw [← A219197Frobenius.double_square]
    have hzero : (4 : S) * map4 d = 0 := by rw [A219197Frobenius.four_eq_zero, zero_mul]
    linear_combination 2 * h4 - hzero

lemma double_root (c y : PS) (h : c ^ 2 * (1 - 4 * y ^ 2) = 1) :
    2 * map4 c = 2 := (square_shift c y h).1

lemma square_root_shift (c y : PS) (h : c ^ 2 * (1 - 4 * y ^ 2) = 1) :
    expand 2 (by decide) (map4 c) = map4 c + 2 * (map4 y) ^ 2 := by
  simpa only [map_expand] using (square_shift c y h).2

end A219197SquareShift

/-!
Modulo-four part of Hanna's A219197 conjecture.
The target series has square G^4 / (1 - 4*(G-1)^2), with G = 1 + X*G^3.
-/

namespace A219197Mod4

open PowerSeries

abbrev S := PowerSeries (ZMod 4)

noncomputable abbrev E : S →ₐ[ZMod 4] S := PowerSeries.expand 2 (by decide)

private theorem four_zero : (4 : S) = 0 := by
  change C (4 : ZMod 4) = 0
  rw [show (4 : ZMod 4) = 0 from by decide, map_zero]

private theorem four_mul (a : S) : 4 * a = 0 := by
  rw [four_zero, zero_mul]

theorem root_self_similar (g c : S) (hg : g = 1 + X * g ^ 3)
    (hc2 : 2 * c = 2) (hc : E c = c + 2 * (g - 1) ^ 2)
    (hf2 : ∀ f : S, 2 * f ^ 2 = 2 * E f)
    (hf4 : ∀ f : S, f ^ 4 = (E f) ^ 2) :
    g ^ 2 * c = E (g ^ 2 * c) + X ^ 2 * E (E (g ^ 2 * c)) +
      2 * X * (E g) ^ 3 + 2 * X ^ 2 * (E (E g)) ^ 3 := by
  let q := E g
  let r := E q
  have hq2 : g ^ 4 = q ^ 2 := hf4 g
  have hq4 : q ^ 4 = g ^ 8 := by
    calc
      q ^ 4 = (q ^ 2) ^ 2 := by ring
      _ = (g ^ 4) ^ 2 := by rw [← hq2]
      _ = g ^ 8 := by ring
  have hy : 2 * (g - 1) ^ 2 = 2 * g ^ 2 + 2 := by
    linear_combination -four_mul g
  have hqy : 2 * (q - 1) ^ 2 = 2 * g ^ 4 + 2 := by
    linear_combination -2 * hq2 - four_mul q
  have heb : E (g ^ 2 * c) = g ^ 4 * c + 2 * g ^ 6 + 2 * g ^ 4 := by
    rw [map_mul, map_pow, hc, ← hq2]
    linear_combination g ^ 4 * hy
  have heeb : E (E (g ^ 2 * c)) =
      g ^ 8 * c + 2 * g ^ 10 + 2 * g ^ 12 := by
    have hfirst : E (g ^ 2 * c) = g ^ 4 * (c + 2 * (g - 1) ^ 2) := by
      rw [map_mul, map_pow, hc, ← hq2]
    rw [hfirst, map_mul, map_pow, map_add, map_mul, map_ofNat, map_pow,
      map_sub, map_one, hc, hq4]
    linear_combination g ^ 8 * hy + g ^ 8 * hqy + four_mul (g ^ 8)
  have hq3 : 2 * q ^ 3 = 2 * g ^ 6 := by
    linear_combination -(q ^ 2 + q * g ^ 2 + g ^ 4) * hf2 g
  have hr2 : 2 * r = 2 * g ^ 4 := by
    simpa only [r, ← hq2] using (hf2 q).symm
  have hr3 : 2 * r ^ 3 = 2 * g ^ 12 := by
    linear_combination (r ^ 2 + r * g ^ 4 + g ^ 8) * hr2
  have hxq : 2 * X * q ^ 3 = 2 * X * g ^ 6 := by
    linear_combination X * hq3
  have hxxr : 2 * X ^ 2 * r ^ 3 = 2 * X ^ 2 * g ^ 12 := by
    linear_combination X ^ 2 * hr3
  have hxg : X * g ^ 3 = g - 1 := by linear_combination -hg
  have hxx : X ^ 2 * g ^ 6 = (g - 1) ^ 2 := by
    calc
      X ^ 2 * g ^ 6 = (X * g ^ 3) ^ 2 := by ring
      _ = (g - 1) ^ 2 := by rw [hxg]
  have hprod : g ^ 4 * c + X ^ 2 * g ^ 8 * c =
      g ^ 2 * c + 2 * g ^ 4 - 2 * g ^ 3 := by
    linear_combination g ^ 2 * c * hxx + g ^ 3 * (g - 1) * hc2
  have hx6 : 2 * X * g ^ 6 = 2 * g ^ 4 - 2 * g ^ 3 := by
    linear_combination -2 * g ^ 3 * hg
  have hxx10 : 2 * X ^ 2 * g ^ 10 = 2 * g ^ 6 + 2 * g ^ 4 := by
    linear_combination 2 * g ^ 4 * hxx - four_mul (g ^ 5)
  change g ^ 2 * c = E (g ^ 2 * c) + X ^ 2 * E (E (g ^ 2 * c)) +
    2 * X * q ^ 3 + 2 * X ^ 2 * r ^ 3
  rw [heeb, heb, hxq, hxxr]
  linear_combination -hprod - hx6 - hxx10 -
    four_mul (g ^ 6 + 2 * g ^ 4 - g ^ 3 + X ^ 2 * g ^ 12)

private theorem coeff_two_mul (n : ℕ) (f : S) :
    coeff n (2 * f) = 2 * coeff n f := by
  change coeff n (C (2 : ZMod 4) * f) = _
  exact coeff_C_mul _ _ _

private theorem coeff_E_even (n : ℕ) (f : S) : coeff (2 * n) (E f) = coeff n f :=
  coeff_expand_mul _ _ _ _

private theorem coeff_E_odd (n : ℕ) (f : S) : coeff (2 * n + 1) (E f) = 0 := by
  apply coeff_expand_of_not_dvd
  omega

private theorem coeff_X_E_even (n : ℕ) (f : S) :
    coeff (2 * n) (X * E f) = 0 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, coeff_succ_X_mul,
      coeff_E_odd]

private theorem coeff_X_E_odd (n : ℕ) (f : S) :
    coeff (2 * n + 1) (X * E f) = coeff n f := by
  rw [coeff_succ_X_mul, coeff_E_even]

theorem coefficients_self_similar (b d : S)
    (hb : b = E b + E (X * E b) + 2 * (X * E d) + 2 * E (X * E d)) :
    (∀ n, coeff (2 * n + 1) b = 2 * coeff n d) ∧
    (∀ n, coeff (4 * n) b = coeff (2 * n) b) ∧
    (∀ n, coeff (4 * n + 2) b = coeff n b) := by
  have hodd (n : ℕ) : coeff (2 * n + 1) b = 2 * coeff n d := by
    have h := congrArg (coeff (2 * n + 1)) hb
    simpa only [map_add, coeff_two_mul, coeff_E_odd, coeff_X_E_odd,
      zero_add, mul_zero, add_zero] using h
  refine ⟨hodd, ?_, ?_⟩
  · intro n
    have h := congrArg (coeff (2 * (2 * n))) hb
    simp only [map_add, coeff_two_mul, coeff_E_even, coeff_X_E_even,
      mul_zero, add_zero] at h
    simpa only [show 2 * (2 * n) = 4 * n by omega] using h
  · intro n
    have h := congrArg (coeff (2 * (2 * n + 1))) hb
    simp only [map_add, coeff_two_mul, coeff_E_even, coeff_X_E_even,
      coeff_X_E_odd, hodd, mul_zero, add_zero] at h
    have hz : 4 * coeff n d = 0 := by
      rw [show (4 : ZMod 4) = 0 from by decide, zero_mul]
    have h' : coeff (2 * (2 * n + 1)) b = coeff n b := by
      linear_combination h + hz
    simpa only [show 2 * (2 * n + 1) = 4 * n + 2 by omega] using h'

theorem coefficients_ne_three (b d : S) (hb0 : coeff 0 b = 1)
    (hb : b = E b + E (X * E b) + 2 * (X * E d) + 2 * E (X * E d)) :
    ∀ n, coeff n b ≠ 3 := by
  obtain ⟨hodd, hfour, hfour_add⟩ := coefficients_self_similar b d hb
  have htwice : ∀ z : ZMod 4, 2 * z ≠ 3 := by decide
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      rw [hb0]
      decide
    have hm : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases hm with h0 | h1 | h2 | h3
    · have heq : n = 4 * (n / 4) := by omega
      rw [heq, hfour]
      exact ih (2 * (n / 4)) (by omega)
    · have heq : n = 2 * (n / 2) + 1 := by omega
      rw [heq, hodd]
      exact htwice _
    · have heq : n = 4 * (n / 4) + 2 := by omega
      rw [heq, hfour_add]
      exact ih (n / 4) (by omega)
    · have heq : n = 2 * (n / 2) + 1 := by omega
      rw [heq, hodd]
      exact htwice _

theorem root_coefficients_ne_three (g c : S)
    (hg : g = 1 + X * g ^ 3) (hc2 : 2 * c = 2)
    (hc : E c = c + 2 * (g - 1) ^ 2)
    (h0 : coeff 0 (g ^ 2 * c) = 1)
    (hf2 : ∀ f : S, 2 * f ^ 2 = 2 * E f)
    (hf4 : ∀ f : S, f ^ 4 = (E f) ^ 2) :
    ∀ n, coeff n (g ^ 2 * c) ≠ 3 := by
  apply coefficients_ne_three (g ^ 2 * c) (g ^ 3) h0
  simpa only [map_mul, map_pow, expand_X, mul_assoc] using
    root_self_similar g c hg hc2 hc hf2 hf4

end A219197Mod4

open PowerSeries
open scoped BigOperators

namespace A219197Final

theorem square_eq_of_convolution (a : ℕ → ℤ) (B : PowerSeries ℤ)
    (h : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), a (n - k) * a k = coeff n B) :
    (PowerSeries.mk a) ^ 2 = B := by
  ext n
  rw [sq, coeff_mul]
  simp only [coeff_mk]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simpa only [mul_comm] using h n

theorem integral_root_ne_three (B G H : PowerSeries ℤ)
    (hB0 : constantCoeff B = 1)
    (hG : G = 1 + X * G ^ 3) (hGH : G * H = 1)
    (hB : B ^ 2 * (1 - 4 * (G - 1) ^ 2) = G ^ 4) :
    ∀ n : ℕ, ((coeff n B : ℤ) : ZMod 4) ≠ 3 := by
  let c : PowerSeries ℤ := B * H ^ 2
  have hc : c ^ 2 * (1 - 4 * (G - 1) ^ 2) = 1 := by
    calc
      _ = (B ^ 2 * (1 - 4 * (G - 1) ^ 2)) * H ^ 4 := by dsimp [c]; ring
      _ = G ^ 4 * H ^ 4 := by rw [hB]
      _ = 1 := by rw [← mul_pow, hGH, one_pow]
  have hfactor : G ^ 2 * c = B := by
    calc
      _ = B * (G * H) ^ 2 := by dsimp [c]; ring
      _ = B := by rw [hGH, one_pow, mul_one]
  let m := A219197SquareShift.map4
  have hgm : m G = 1 + X * (m G) ^ 3 := by
    simpa only [map_add, map_one, map_mul, map_pow, m,
      A219197SquareShift.map4, PowerSeries.map_X] using congrArg m hG
  have hcm : A219197Mod4.E (m c) = m c + 2 * (m G - 1) ^ 2 := by
    have hh := A219197SquareShift.square_root_shift c (G - 1) hc
    simpa only [m, A219197SquareShift.map4, PowerSeries.map_expand,
      map_sub, map_one, A219197Mod4.E] using hh
  have hc2 : 2 * m c = 2 := A219197SquareShift.double_root c (G - 1) hc
  have hfacm : m G ^ 2 * m c = m B := by
    rw [← map_pow, ← map_mul, hfactor]
  have hzero : coeff 0 (m G ^ 2 * m c) = 1 := by
    rw [hfacm]
    change ((coeff 0 B : ℤ) : ZMod 4) = 1
    rw [coeff_zero_eq_constantCoeff_apply, hB0]
    rfl
  have hno := A219197Mod4.root_coefficients_ne_three (m G) (m c)
    hgm hc2 hcm hzero A219197Frobenius.double_square A219197Frobenius.fourth_power
  intro n
  simpa only [hfacm, m, A219197SquareShift.map4, coeff_map, Int.coe_castRingHom] using hno n

end A219197Final

-- Credit: @CubeJerry
-- A219197 is distinct from A183161, whose public proof by Chain.Ren is related background.
theorem OMA.solution : type_of% @OMA.S_oeis_a219197.main := by
  intro a ha0 ha n
  let B : PowerSeries ℤ := PowerSeries.mk a
  let D : PowerSeries ℤ := PowerSeries.mk fun k => (OMA.S_oeis_a219197.A199033 k : ℤ)
  have hB0 : constantCoeff B = 1 := ha0
  have hBsq : B ^ 2 = D := by
    apply A219197Final.square_eq_of_convolution
    intro k
    simpa only [D, coeff_mk] using ha k
  have hD : D * (1 - 4 * (A219197Ternary.G - 1) ^ 2) = A219197Ternary.G ^ 4 := by
    apply A219197Lagrange.diagonal_series_identity A219197Ternary.U A219197Ternary.G D
      A219197Ternary.U_zero A219197Ternary.U_subst_F A219197Ternary.F_subst_U
    · simpa only [mul_comm] using A219197Ternary.G_inverse
    · intro k
      simpa only [D, coeff_mk, OMA.S_oeis_a219197.A199033,
        A219197Lagrange.evenGeo, A219197Binomial.evenGeo, A219197Binomial.geo] using
        (A219197Binomial.finite_bridge k).symm
  have hno := A219197Final.integral_root_ne_three B A219197Ternary.G
    (1 - A219197Ternary.U) hB0 A219197Ternary.G_eq
    (by simpa only [mul_comm] using A219197Ternary.G_inverse)
    (by rw [hBsq]; exact hD) n
  intro hn
  apply hno
  simp only [B, coeff_mk]
  exact (ZMod.intCast_eq_intCast_iff' (a n) 3 4).mpr (by simpa using hn)

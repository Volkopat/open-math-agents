import OMAReductions.R_PartitionParity_bellaiche_nicolas_even_R2

/-!
Proof of `PartitionParity.bellaiche_nicolas.even.R2.H1` (Bellaïche–Nicolas 2016, §6, (6.9)).

We establish Euler's pentagonal number theorem and Jacobi's cube identity modulo 2 from a
self-contained finite Jacobi triple product polynomial identity, deduce the characteristic-2
convolution identity for `Δ^k` with `k = (4^t - 1) / 3` via Frobenius and `Nat.Partition.hasProd_genFun`,
and conclude the lower bound on even partition values by double counting over the odd-length
pentagonal intervals.
-/

namespace OMA.PartitionParityBellaicheNicolasEvenR2H1

open Finset Filter Real PowerSeries
open scoped Classical PowerSeries.WithPiTopology

/- ### Section 1: Finite Jacobi triple product over `ℤ[q][z]` -/

private abbrev QPoly := Polynomial ℤ
private abbrev ZPoly := Polynomial QPoly
private noncomputable abbrev qVar : QPoly := Polynomial.X
private noncomputable abbrev zVar : ZPoly := Polynomial.X

private noncomputable def P (N : ℕ) : ZPoly :=
  ∏ k ∈ Finset.range N,
    ((1 + Polynomial.C (qVar ^ (2 * k + 1)) * zVar) *
      (zVar + Polynomial.C (qVar ^ (2 * k + 1))))

private noncomputable def sigma : ZPoly →+* ZPoly :=
  Polynomial.eval₂RingHom Polynomial.C (Polynomial.C (qVar ^ 2) * zVar)

private lemma sigma_C (a : QPoly) : sigma (Polynomial.C a) = Polynomial.C a := by
  simp [sigma]

private lemma sigma_zVar : sigma zVar = Polynomial.C (qVar ^ 2) * zVar := by
  simp [sigma, zVar]

private lemma sigma_coeff (f : ZPoly) (r : ℕ) :
    (sigma f).coeff r = qVar ^ (2 * r) * f.coeff r := by
  induction f using Polynomial.induction_on' with
  | add f₁ f₂ ih₁ ih₂ =>
    rw [map_add, Polynomial.coeff_add, Polynomial.coeff_add, ih₁, ih₂, mul_add]
  | monomial n a =>
    have hmon : Polynomial.monomial n a = Polynomial.C a * zVar ^ n := by
      simp [zVar, Polynomial.C_mul_X_pow_eq_monomial]
    rw [hmon, map_mul, map_pow, sigma_C, sigma_zVar, mul_pow, ← Polynomial.C_pow,
      ← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C_mul_X_pow]
    split_ifs with h
    · subst h; rw [← pow_mul]; ring
    · simp

private lemma P_func_eq (N : ℕ) :
    (Polynomial.C qVar * zVar + Polynomial.C (qVar ^ (2 * N))) * sigma (P N) =
      Polynomial.C (qVar ^ (2 * N)) *
        (1 + Polynomial.C (qVar ^ (2 * N + 1)) * zVar) * P N := by
  induction N with
  | zero =>
    simp [P]
    ring
  | succ N ih =>
    have hP : P (N + 1) = P N * ((1 + Polynomial.C (qVar ^ (2 * N + 1)) * zVar) *
        (zVar + Polynomial.C (qVar ^ (2 * N + 1)))) := by
      unfold P
      rw [Finset.prod_range_succ]
    rw [hP, map_mul, map_mul, map_add, map_add, map_one, map_mul, sigma_C, sigma_zVar]
    have hq2 : Polynomial.C (qVar ^ 2) * zVar + Polynomial.C (qVar ^ (2 * N + 1)) =
        Polynomial.C qVar * (Polynomial.C qVar * zVar + Polynomial.C (qVar ^ (2 * N))) := by
      have h1 : qVar ^ 2 = qVar * qVar := by ring
      have h2 : qVar ^ (2 * N + 1) = qVar * qVar ^ (2 * N) := by ring
      rw [h1, h2, Polynomial.C_mul, Polynomial.C_mul]
      ring
    have hq1 : 1 + Polynomial.C (qVar ^ (2 * N + 1)) * (Polynomial.C (qVar ^ 2) * zVar) =
        1 + Polynomial.C (qVar ^ (2 * (N + 1) + 1)) * zVar := by
      have h1 : qVar ^ (2 * (N + 1) + 1) = qVar ^ (2 * N + 1) * qVar ^ 2 := by ring
      rw [h1, Polynomial.C_mul]
      ring
    have hq3 : (Polynomial.C qVar * zVar + Polynomial.C (qVar ^ (2 * (N + 1)))) * Polynomial.C qVar =
        Polynomial.C (qVar ^ 2) * (zVar + Polynomial.C (qVar ^ (2 * N + 1))) := by
      have h1 : qVar ^ 2 = qVar * qVar := by ring
      have h2 : qVar ^ (2 * (N + 1)) = qVar * qVar ^ (2 * N + 1) := by ring
      rw [h1, h2, Polynomial.C_mul, Polynomial.C_mul]
      ring
    have hq4 : Polynomial.C (qVar ^ (2 * (N + 1))) =
        Polynomial.C (qVar ^ 2) * Polynomial.C (qVar ^ (2 * N)) := by
      have h1 : qVar ^ (2 * (N + 1)) = qVar ^ 2 * qVar ^ (2 * N) := by ring
      rw [h1, Polynomial.C_mul]
    rw [hq1, hq2]
    calc (Polynomial.C qVar * zVar + Polynomial.C (qVar ^ (2 * (N + 1)))) *
            (sigma (P N) * ((1 + Polynomial.C (qVar ^ (2 * (N + 1) + 1)) * zVar) *
              (Polynomial.C qVar * (Polynomial.C qVar * zVar + Polynomial.C (qVar ^ (2 * N))))))
        = ((Polynomial.C qVar * zVar + Polynomial.C (qVar ^ (2 * (N + 1)))) * Polynomial.C qVar) *
            (1 + Polynomial.C (qVar ^ (2 * (N + 1) + 1)) * zVar) *
            ((Polynomial.C qVar * zVar + Polynomial.C (qVar ^ (2 * N))) * sigma (P N)) := by ring
      _ = (Polynomial.C (qVar ^ 2) * (zVar + Polynomial.C (qVar ^ (2 * N + 1)))) *
            (1 + Polynomial.C (qVar ^ (2 * (N + 1) + 1)) * zVar) *
            (Polynomial.C (qVar ^ (2 * N)) * (1 + Polynomial.C (qVar ^ (2 * N + 1)) * zVar) * P N) := by
          rw [hq3, ih]
      _ = Polynomial.C (qVar ^ (2 * (N + 1))) *
            (1 + Polynomial.C (qVar ^ (2 * (N + 1) + 1)) * zVar) *
            (P N * ((1 + Polynomial.C (qVar ^ (2 * N + 1)) * zVar) *
              (zVar + Polynomial.C (qVar ^ (2 * N + 1))))) := by
          rw [hq4]; ring

private lemma P_coeff_of_gt (N : ℕ) : ∀ r : ℕ, 2 * N < r → (P N).coeff r = 0 := by
  induction N with
  | zero =>
    intro r hr
    simp [P, Polynomial.coeff_one, Nat.ne_of_gt hr]
  | succ N ih =>
    intro r hr
    have hP : P (N + 1) = P N * (Polynomial.C (qVar ^ (2 * N + 1)) +
        Polynomial.C (1 + qVar ^ (2 * (2 * N + 1))) * zVar +
        Polynomial.C (qVar ^ (2 * N + 1)) * zVar ^ 2) := by
      unfold P
      rw [Finset.prod_range_succ]
      have hsq : qVar ^ (2 * (2 * N + 1)) = qVar ^ (2 * N + 1) * qVar ^ (2 * N + 1) := by ring
      rw [hsq, map_add, map_one, map_mul]
      ring
    rw [hP, mul_add, mul_add, Polynomial.coeff_add, Polynomial.coeff_add]
    have h0 : (P N * Polynomial.C (qVar ^ (2 * N + 1))).coeff r = 0 := by
      rw [Polynomial.coeff_mul_C, ih r (by omega), zero_mul]
    have h1 : (P N * (Polynomial.C (1 + qVar ^ (2 * (2 * N + 1))) * zVar)).coeff r = 0 := by
      rw [mul_left_comm, Polynomial.coeff_C_mul]
      have hr1 : r = (r - 1) + 1 := by omega
      rw [hr1, Polynomial.coeff_mul_X, ih (r - 1) (by omega), mul_zero]
    have h2 : (P N * (Polynomial.C (qVar ^ (2 * N + 1)) * zVar ^ 2)).coeff r = 0 := by
      rw [mul_left_comm, Polynomial.coeff_C_mul]
      have hr2 : r = (r - 2) + 2 := by omega
      rw [hr2, Polynomial.coeff_mul_X_pow, ih (r - 2) (by omega), mul_zero]
    rw [h0, h1, h2, add_zero, add_zero]

private lemma P_coeff_top (N : ℕ) : (P N).coeff (2 * N) = qVar ^ (N ^ 2) := by
  induction N with
  | zero => simp [P]
  | succ N ih =>
    have hP : P (N + 1) = P N * (Polynomial.C (qVar ^ (2 * N + 1)) +
        Polynomial.C (1 + qVar ^ (2 * (2 * N + 1))) * zVar +
        Polynomial.C (qVar ^ (2 * N + 1)) * zVar ^ 2) := by
      unfold P
      rw [Finset.prod_range_succ]
      have hsq : qVar ^ (2 * (2 * N + 1)) = qVar ^ (2 * N + 1) * qVar ^ (2 * N + 1) := by ring
      rw [hsq, map_add, map_one, map_mul]
      ring
    rw [hP, mul_add, mul_add, Polynomial.coeff_add, Polynomial.coeff_add]
    have h0 : (P N * Polynomial.C (qVar ^ (2 * N + 1))).coeff (2 * (N + 1)) = 0 := by
      rw [Polynomial.coeff_mul_C, P_coeff_of_gt N _ (by omega), zero_mul]
    have h1 : (P N * (Polynomial.C (1 + qVar ^ (2 * (2 * N + 1))) * zVar)).coeff (2 * (N + 1)) = 0 := by
      rw [mul_left_comm, Polynomial.coeff_C_mul, show 2 * (N + 1) = (2 * N + 1) + 1 by omega,
        Polynomial.coeff_mul_X, P_coeff_of_gt N _ (by omega), mul_zero]
    have h2 : (P N * (Polynomial.C (qVar ^ (2 * N + 1)) * zVar ^ 2)).coeff (2 * (N + 1)) =
        qVar ^ ((N + 1) ^ 2) := by
      rw [mul_left_comm, Polynomial.coeff_C_mul, show 2 * (N + 1) = 2 * N + 2 by omega,
        Polynomial.coeff_mul_X_pow, ih, ← pow_add]
      congr 1; ring
    rw [h0, h1, h2, zero_add, zero_add]

private lemma P_coeff_symm (N : ℕ) : ∀ r : ℕ, r ≤ 2 * N → (P N).coeff (2 * N - r) = (P N).coeff r := by
  induction N with
  | zero =>
    intro r hr
    have : r = 0 := by omega
    subst this; rfl
  | succ N ih =>
    intro r hr
    set a : QPoly := qVar ^ (2 * N + 1)
    set b : QPoly := 1 + qVar ^ (2 * (2 * N + 1))
    have hP : P (N + 1) = P N * (Polynomial.C a + Polynomial.C b * zVar + Polynomial.C a * zVar ^ 2) := by
      unfold P
      rw [Finset.prod_range_succ]
      have hsq : qVar ^ (2 * (2 * N + 1)) = qVar ^ (2 * N + 1) * qVar ^ (2 * N + 1) := by ring
      dsimp only [a, b]
      rw [hsq, map_add, map_one, map_mul]
      ring
    have hexpand : ∀ m : ℕ, (P (N + 1)).coeff m =
        a * (P N).coeff m + b * (if 1 ≤ m then (P N).coeff (m - 1) else 0) +
          a * (if 2 ≤ m then (P N).coeff (m - 2) else 0) := by
      intro m
      rw [hP, mul_add, mul_add, Polynomial.coeff_add, Polynomial.coeff_add]
      congr 1
      · congr 1
        · rw [Polynomial.coeff_mul_C, mul_comm]
        · rw [mul_left_comm, Polynomial.coeff_C_mul]
          congr 1
          change (P N * Polynomial.X).coeff m = _
          rcases m with _ | m
          · simp
          · simp
      · rw [mul_left_comm, Polynomial.coeff_C_mul]
        congr 1
        change (P N * Polynomial.X ^ 2).coeff m = _
        rw [Polynomial.coeff_mul_X_pow']
    rw [hexpand (2 * (N + 1) - r), hexpand r]
    have hterm1 : (P N).coeff (2 * (N + 1) - r) = if 2 ≤ r then (P N).coeff (r - 2) else 0 := by
      split_ifs with h2
      · have hle : r - 2 ≤ 2 * N := by omega
        have heq : 2 * (N + 1) - r = 2 * N - (r - 2) := by omega
        rw [heq, ih (r - 2) hle]
      · exact P_coeff_of_gt N _ (by omega)
    have hterm2 : (if 1 ≤ 2 * (N + 1) - r then (P N).coeff (2 * (N + 1) - r - 1) else 0) =
        if 1 ≤ r then (P N).coeff (r - 1) else 0 := by
      split_ifs with h1 h2
      · by_cases hle : r - 1 ≤ 2 * N
        · have heq : 2 * (N + 1) - r - 1 = 2 * N - (r - 1) := by omega
          rw [heq, ih (r - 1) hle]
        · rw [P_coeff_of_gt N (r - 1) (by omega), P_coeff_of_gt N _ (by omega)]
      · exact P_coeff_of_gt N _ (by omega)
      · exact (P_coeff_of_gt N _ (by omega)).symm
      · rfl
    have hterm3 : (if 2 ≤ 2 * (N + 1) - r then (P N).coeff (2 * (N + 1) - r - 2) else 0) =
        (P N).coeff r := by
      split_ifs with h2
      · have hle : r ≤ 2 * N := by omega
        have heq : 2 * (N + 1) - r - 2 = 2 * N - r := by omega
        rw [heq, ih r hle]
      · exact (P_coeff_of_gt N _ (by omega)).symm
    rw [hterm1, hterm2, hterm3]
    ring

private lemma P_coeff_recurrence (N m : ℕ) (hm1 : 1 ≤ m) (hmN : m ≤ N) :
    (P N).coeff (N + m) * (1 - qVar ^ (2 * N + 2 * m)) =
      qVar ^ (2 * m - 1) * (1 - qVar ^ (2 * N - 2 * m + 2)) * (P N).coeff (N + m - 1) := by
  have hfe := congrArg (fun f : ZPoly => f.coeff (N + m)) (P_func_eq N)
  have hsucc : N + m = (N + m - 1) + 1 := by omega
  have hlhs : ((Polynomial.C qVar * zVar + Polynomial.C (qVar ^ (2 * N))) * sigma (P N)).coeff (N + m) =
      qVar * (qVar ^ (2 * (N + m - 1)) * (P N).coeff (N + m - 1)) +
        qVar ^ (2 * N) * (qVar ^ (2 * (N + m)) * (P N).coeff (N + m)) := by
    rw [add_mul, Polynomial.coeff_add, mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
      sigma_coeff (P N) (N + m),
      show (zVar * sigma (P N)).coeff (N + m) = (sigma (P N)).coeff (N + m - 1) by
        nth_rw 1 [hsucc]; rw [Polynomial.coeff_X_mul],
      sigma_coeff (P N) (N + m - 1)]
  have hrhs : (Polynomial.C (qVar ^ (2 * N)) *
      (1 + Polynomial.C (qVar ^ (2 * N + 1)) * zVar) * P N).coeff (N + m) =
      qVar ^ (2 * N) * ((P N).coeff (N + m) + qVar ^ (2 * N + 1) * (P N).coeff (N + m - 1)) := by
    rw [mul_assoc, Polynomial.coeff_C_mul, add_mul, one_mul, Polynomial.coeff_add,
      mul_assoc, Polynomial.coeff_C_mul,
      show (zVar * P N).coeff (N + m) = (P N).coeff (N + m - 1) by
        nth_rw 1 [hsucc]; rw [Polynomial.coeff_X_mul]]
  rw [hlhs, hrhs] at hfe
  have hq_ne : qVar ^ (2 * N) ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
  apply mul_left_cancel₀ hq_ne
  have he1 : qVar * qVar ^ (2 * (N + m - 1)) = qVar ^ (2 * N) * qVar ^ (2 * m - 1) := by
    rw [← pow_succ', ← pow_add]; congr 1; omega
  have he2 : 2 * (N + m) = 2 * N + 2 * m := by omega
  have he3 : qVar ^ (2 * N + 1) = qVar ^ (2 * m - 1) * qVar ^ (2 * N - 2 * m + 2) := by
    rw [← pow_add]; congr 1; omega
  calc qVar ^ (2 * N) * ((P N).coeff (N + m) * (1 - qVar ^ (2 * N + 2 * m)))
      = qVar ^ (2 * N) * (P N).coeff (N + m) -
          qVar ^ (2 * N) * (qVar ^ (2 * (N + m)) * (P N).coeff (N + m)) := by rw [he2]; ring
    _ = qVar * (qVar ^ (2 * (N + m - 1)) * (P N).coeff (N + m - 1)) -
          qVar ^ (2 * N) * (qVar ^ (2 * N + 1) * (P N).coeff (N + m - 1)) := by
        linear_combination -hfe
    _ = (qVar ^ (2 * N) * qVar ^ (2 * m - 1)) * (P N).coeff (N + m - 1) -
          (qVar ^ (2 * N) * (qVar ^ (2 * m - 1) * qVar ^ (2 * N - 2 * m + 2))) *
            (P N).coeff (N + m - 1) := by
        rw [← mul_assoc qVar, he1, he3]; ring
    _ = qVar ^ (2 * N) * (qVar ^ (2 * m - 1) * (1 - qVar ^ (2 * N - 2 * m + 2)) *
          (P N).coeff (N + m - 1)) := by ring

private lemma P_coeff_product (N t : ℕ) (ht : t ≤ N) :
    (P N).coeff (2 * N - t) * (∏ j ∈ Finset.range t, (1 - qVar ^ (2 * (j + 1)))) =
      qVar ^ ((N - t) ^ 2) * (∏ j ∈ Finset.range t, (1 - qVar ^ (4 * N - 2 * j))) := by
  induction t with
  | zero =>
    simpa using P_coeff_top N
  | succ t ih =>
    have ht' : t ≤ N := by omega
    have hrec := P_coeff_recurrence N (N - t) (by omega) (by omega)
    have hidx1 : N + (N - t) = 2 * N - t := by omega
    have hidx2 : 2 * N - t - 1 = 2 * N - (t + 1) := by omega
    have hexp1 : 2 * N + 2 * (N - t) = 4 * N - 2 * t := by omega
    have hexp2 : 2 * N - 2 * (N - t) + 2 = 2 * (t + 1) := by omega
    rw [hidx1, hidx2, hexp1, hexp2] at hrec
    have hsq : (N - t) ^ 2 = (2 * (N - t) - 1) + (N - (t + 1)) ^ 2 := by
      have h1 : N - t = (N - (t + 1)) + 1 := by omega
      have h2 : 2 * (N - t) - 1 = 2 * (N - (t + 1)) + 1 := by omega
      rw [h2, h1]; ring
    have hq_ne : qVar ^ (2 * (N - t) - 1) ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
    apply mul_left_cancel₀ hq_ne
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    calc qVar ^ (2 * (N - t) - 1) *
            ((P N).coeff (2 * N - (t + 1)) *
              ((∏ j ∈ Finset.range t, (1 - qVar ^ (2 * (j + 1)))) * (1 - qVar ^ (2 * (t + 1)))))
        = (qVar ^ (2 * (N - t) - 1) * (1 - qVar ^ (2 * (t + 1))) * (P N).coeff (2 * N - (t + 1))) *
            (∏ j ∈ Finset.range t, (1 - qVar ^ (2 * (j + 1)))) := by ring
      _ = ((P N).coeff (2 * N - t) * (1 - qVar ^ (4 * N - 2 * t))) *
            (∏ j ∈ Finset.range t, (1 - qVar ^ (2 * (j + 1)))) := by rw [← hrec]
      _ = ((P N).coeff (2 * N - t) * (∏ j ∈ Finset.range t, (1 - qVar ^ (2 * (j + 1))))) *
            (1 - qVar ^ (4 * N - 2 * t)) := by ring
      _ = (qVar ^ ((N - t) ^ 2) * (∏ j ∈ Finset.range t, (1 - qVar ^ (4 * N - 2 * j)))) *
            (1 - qVar ^ (4 * N - 2 * t)) := by rw [ih ht']
      _ = qVar ^ (2 * (N - t) - 1) *
            (qVar ^ ((N - (t + 1)) ^ 2) *
              ((∏ j ∈ Finset.range t, (1 - qVar ^ (4 * N - 2 * j))) *
                (1 - qVar ^ (4 * N - 2 * t)))) := by
          rw [hsq, pow_add]; ring

private lemma coeff_mul_prod_one_sub_q_pow {ι : Type*} (s : Finset ι) (e : ι → ℕ) (n : ℕ)
    (he : ∀ i ∈ s, n < e i) (g : QPoly) :
    (g * ∏ i ∈ s, (1 - qVar ^ (e i))).coeff n = g.coeff n := by
  induction s using Finset.induction_on generalizing g with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, ← mul_assoc]
    have hrest : ∀ j ∈ s, n < e j := fun j hj => he j (Finset.mem_insert_of_mem hj)
    rw [ih hrest (g * (1 - qVar ^ e i)), mul_sub, mul_one, Polynomial.coeff_sub]
    have hgt : (g * qVar ^ e i).coeff n = 0 := by
      change (g * Polynomial.X ^ e i).coeff n = 0
      rw [Polynomial.coeff_mul_X_pow']
      rw [if_neg (not_le.mpr (he i (Finset.mem_insert_self i s)))]
    rw [hgt, sub_zero]

/-- Sharp coefficient matching for `(P N).coeff (N + k) * ∏_{j=1}^N (1 - q^{2j})`:
holds whenever either `m < k^2` or `m < 2 * (N - k + 1)`. -/
private lemma P_coeff_mul_even_prod_coeff (N k m : ℕ) (hk : k ≤ N)
    (hcond : m < k ^ 2 ∨ m < 2 * (N - k + 1)) :
    ((P N).coeff (N + k) * (∏ j ∈ Finset.range N, (1 - qVar ^ (2 * (j + 1))))).coeff m =
      (qVar ^ (k ^ 2)).coeff m := by
  have hsplit : Finset.range N = Finset.range (N - k) ∪ Finset.Ico (N - k) N := by
    ext j; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
  have hdisj : Disjoint (Finset.range (N - k)) (Finset.Ico (N - k) N) :=
    Finset.disjoint_left.mpr fun j hj1 hj2 => by
      simp only [Finset.mem_range, Finset.mem_Ico] at hj1 hj2; omega
  rw [hsplit, Finset.prod_union hdisj, ← mul_assoc]
  have hidx : N + k = 2 * N - (N - k) := by omega
  rw [hidx, P_coeff_product N (N - k) (by omega), show N - (N - k) = k by omega]
  rcases hcond with hksq | hsmall
  · have hmul0 : ∀ h : QPoly, (qVar ^ (k ^ 2) * h).coeff m = 0 := by
      intro h
      change (Polynomial.X ^ (k ^ 2) * h).coeff m = 0
      rw [Polynomial.coeff_X_pow_mul']
      rw [if_neg (not_le.mpr hksq)]
    rw [mul_assoc, hmul0]
    change 0 = (Polynomial.X ^ (k ^ 2) : QPoly).coeff m
    rw [Polynomial.coeff_X_pow, if_neg (by omega)]
  · rw [coeff_mul_prod_one_sub_q_pow (Finset.Ico (N - k) N) (fun j => 2 * (j + 1)) m
      (fun j hj => by simp only [Finset.mem_Ico] at hj; omega)]
    rw [coeff_mul_prod_one_sub_q_pow (Finset.range (N - k)) (fun j => 4 * N - 2 * j) m
      (fun j hj => by simp only [Finset.mem_range] at hj; omega)]

private lemma P_coeff_mul_even_prod_coeff_any (N r m : ℕ) (hr : r ≤ 2 * N)
    (hcond : m < ((r : ℤ) - N).natAbs ^ 2 ∨ m < 2 * (N - ((r : ℤ) - N).natAbs + 1)) :
    ((P N).coeff r * (∏ j ∈ Finset.range N, (1 - qVar ^ (2 * (j + 1))))).coeff m =
      (qVar ^ (((r : ℤ) - N).natAbs ^ 2)).coeff m := by
  by_cases hle : N ≤ r
  · set k := r - N
    have hkr : r = N + k := by omega
    have habs : ((r : ℤ) - N).natAbs = k := by omega
    rw [habs] at hcond ⊢
    rw [hkr]
    exact P_coeff_mul_even_prod_coeff N k m (by omega) hcond
  · set k := N - r
    have hkr : r = 2 * N - (N + k) := by omega
    have habs : ((r : ℤ) - N).natAbs = k := by omega
    rw [habs] at hcond ⊢
    rw [hkr, P_coeff_symm N (N + k) (by omega)]
    exact P_coeff_mul_even_prod_coeff N k m (by omega) hcond

/- ### Section 2: Euler's pentagonal theorem and Jacobi's cube identity mod 2 -/

private def pentNat (i : ℕ) : ℕ :=
  if i % 2 = 0 then (i / 2) * (3 * (i / 2) + 1) / 2
  else ((i + 1) / 2) * (3 * ((i + 1) / 2) - 1) / 2

private lemma two_mul_pentNat_even (j : ℕ) : 2 * pentNat (2 * j) = j * (3 * j + 1) := by
  have hev : 2 ∣ j * (3 * j + 1) := by
    rcases Nat.even_or_odd j with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exact ⟨m * (3 * (m + m) + 1), by ring⟩
    · exact ⟨(2 * m + 1) * (3 * m + 2), by ring⟩
  unfold pentNat
  rw [if_pos (by omega), show 2 * j / 2 = j by omega]
  exact Nat.mul_div_cancel' hev

private lemma two_mul_pentNat_odd (j : ℕ) : 2 * pentNat (2 * j + 1) = (j + 1) * (3 * j + 2) := by
  have hev : 2 ∣ (j + 1) * (3 * j + 2) := by
    rcases Nat.even_or_odd j with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exact ⟨(m + m + 1) * (3 * m + 1), by ring⟩
    · exact ⟨(m + 1) * (3 * (2 * m + 1) + 2), by ring⟩
  unfold pentNat
  rw [if_neg (by omega), show (2 * j + 1 + 1) / 2 = j + 1 by omega,
    show 3 * (j + 1) - 1 = 3 * j + 2 by omega]
  exact Nat.mul_div_cancel' hev

private lemma pentNat_step_even (j : ℕ) : pentNat (2 * j + 1) = pentNat (2 * j) + (2 * j + 1) := by
  have h1 := two_mul_pentNat_even j
  have h2 := two_mul_pentNat_odd j
  nlinarith

private lemma pentNat_step_odd (j : ℕ) : pentNat (2 * j + 2) = pentNat (2 * j + 1) + (j + 1) := by
  have h1 := two_mul_pentNat_odd j
  have h2 := two_mul_pentNat_even (j + 1)
  rw [show 2 * (j + 1) = 2 * j + 2 by omega] at h2
  nlinarith

private lemma pentNat_strictMono : StrictMono pentNat := by
  refine strictMono_nat_of_lt_succ fun i => ?_
  rcases Nat.even_or_odd i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [show j + j = 2 * j by omega, pentNat_step_even]; omega
  · rw [show 2 * j + 1 + 1 = 2 * j + 2 by omega, pentNat_step_odd]; omega

private lemma le_pentNat (i : ℕ) : i ≤ pentNat i :=
  pentNat_strictMono.id_le i

private lemma pentNat_zero : pentNat 0 = 0 := by
  have h := two_mul_pentNat_even 0
  simpa using h

private lemma pentNat_iff_int (d : ℕ) :
    (∃ i : ℕ, pentNat i = d) ↔ ∃ k : ℤ, k * (3 * k + 1) = 2 * (d : ℤ) := by
  constructor
  · rintro ⟨i, rfl⟩
    rcases Nat.even_or_odd i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · refine ⟨(j : ℤ), ?_⟩
      have h := two_mul_pentNat_even j
      rw [show j + j = 2 * j by omega]
      exact_mod_cast h.symm
    · refine ⟨-((j + 1 : ℕ) : ℤ), ?_⟩
      have h := two_mul_pentNat_odd j
      have hz : ((j + 1) * (3 * j + 2) : ℤ) = 2 * (pentNat (2 * j + 1) : ℤ) := by
        exact_mod_cast h.symm
      push_cast at hz ⊢
      linarith
  · rintro ⟨k, hk⟩
    by_cases h0 : 0 ≤ k
    · lift k to ℕ using h0
      refine ⟨2 * k, ?_⟩
      have h := two_mul_pentNat_even k
      have hk' : k * (3 * k + 1) = 2 * d := by exact_mod_cast hk
      omega
    · set j : ℕ := (-k).toNat - 1
      have hkj : k = -((j + 1 : ℕ) : ℤ) := by omega
      rw [hkj] at hk
      refine ⟨2 * j + 1, ?_⟩
      have h := two_mul_pentNat_odd j
      have hz : (2 * pentNat (2 * j + 1) : ℤ) = ((j + 1) * (3 * j + 2) : ℤ) := by
        exact_mod_cast h
      push_cast at hk hz
      have : (2 * pentNat (2 * j + 1) : ℤ) = 2 * (d : ℤ) := by linarith
      omega

private noncomputable def eulerPS : PowerSeries (ZMod 2) :=
  PowerSeries.mk fun n => if ∃ i : ℕ, pentNat i = n then 1 else 0

private noncomputable def triPS : PowerSeries (ZMod 2) :=
  PowerSeries.mk fun n => if ∃ m : ℕ, m * (m + 1) / 2 = n then 1 else 0

private noncomputable def partPS : PowerSeries (ZMod 2) :=
  PowerSeries.mk fun n => (Nat.partitionNumber n : ZMod 2)

private lemma coeff_map_int_zmod2 (f : QPoly) (n : ℕ) :
    ((f.map (Int.castRingHom (ZMod 2)) : Polynomial (ZMod 2)).coeff n) = (f.coeff n : ZMod 2) := by
  simp

private lemma coeff_coe_poly_ps {R : Type*} [Semiring R] (f : Polynomial R) (n : ℕ) :
    (f : PowerSeries R).coeff n = f.coeff n := by
  simp

private lemma P_eq_sum (N : ℕ) :
    P N = ∑ r ∈ Finset.range (2 * N + 1), Polynomial.C ((P N).coeff r) * zVar ^ r := by
  apply Polynomial.ext
  intro r
  rw [Polynomial.finsetSum_coeff]
  by_cases hr : r < 2 * N + 1
  · rw [Finset.sum_eq_single r]
    · simp [zVar]
    · intro b _ hb
      change (Polynomial.C ((P N).coeff b) * Polynomial.X ^ b).coeff r = 0
      rw [Polynomial.coeff_C_mul_X_pow, if_neg (Ne.symm hb)]
    · intro h; exact absurd (Finset.mem_range.mpr hr) h
  · rw [P_coeff_of_gt N r (by omega)]
    symm
    refine Finset.sum_eq_zero fun b hb => ?_
    have hbr : r ≠ b := by have := Finset.mem_range.mp hb; omega
    change (Polynomial.C ((P N).coeff b) * Polynomial.X ^ b).coeff r = 0
    rw [Polynomial.coeff_C_mul_X_pow, if_neg hbr]

/-- Finite Euler pentagonal theorem over `ℤ[q]`: for `d : ℕ` and `N = 4 * d + 3`,
the coefficient of `q^d` in `∏_{m=1}^{3N} (1 - q^m)` matches the signed pentagonal indicator. -/
private lemma euler_pentagonal_fin_int (d : ℕ) :
    let N := 4 * d + 3
    ((∏ m ∈ Finset.range (3 * N), (1 - qVar ^ (m + 1))).coeff d : ZMod 2) =
      if ∃ i : ℕ, pentNat i = d then 1 else 0 := by
  intro N
  set φ : ZPoly →+* QPoly :=
    Polynomial.eval₂RingHom (Polynomial.expand ℤ 3) (-qVar)
  have hφ_C (a : QPoly) : φ (Polynomial.C a) = Polynomial.expand ℤ 3 a := by
    simp [φ]
  have hφ_z : φ zVar = -qVar := by
    simp [φ, zVar]
  have hφ_P : φ (P N) = (-qVar) ^ N *
      ∏ k ∈ Finset.range N, ((1 - qVar ^ (6 * k + 4)) * (1 - qVar ^ (6 * k + 2))) := by
    unfold P
    rw [map_prod, show (-qVar : QPoly) ^ N = ∏ _k ∈ Finset.range N, (-qVar) by simp,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_mul, map_add, map_add, map_one, map_mul, hφ_C, hφ_z]
    have hexp : Polynomial.expand ℤ 3 (qVar ^ (2 * k + 1)) = qVar ^ (6 * k + 3) := by
      rw [map_pow, Polynomial.expand_X, ← pow_mul]
      congr 1; ring
    rw [hexp]
    have h1 : qVar ^ (6 * k + 4) = qVar ^ (6 * k + 3) * qVar := by rw [← pow_succ]
    have h2 : qVar ^ (6 * k + 3) = qVar * qVar ^ (6 * k + 2) := by rw [← pow_succ']
    rw [h1, h2]; ring
  set evenProd : QPoly := ∏ j ∈ Finset.range N, (1 - qVar ^ (2 * (j + 1)))
  have hexp_even : Polynomial.expand ℤ 3 evenProd =
      ∏ j ∈ Finset.range N, (1 - qVar ^ (6 * j + 6)) := by
    dsimp only [evenProd]
    rw [map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_sub, map_one, map_pow, Polynomial.expand_X, ← pow_mul]
    congr 2; ring
  have hLHS : Polynomial.expand ℤ 3 evenProd * φ (P N) =
      (-qVar) ^ N * Polynomial.expand ℤ 2 (∏ m ∈ Finset.range (3 * N), (1 - qVar ^ (m + 1))) := by
    rw [hexp_even, hφ_P]
    have hmerge : (∏ j ∈ Finset.range N, (1 - qVar ^ (6 * j + 6))) *
        (∏ k ∈ Finset.range N, ((1 - qVar ^ (6 * k + 4)) * (1 - qVar ^ (6 * k + 2)))) =
        ∏ m ∈ Finset.range (3 * N), (1 - qVar ^ (2 * (m + 1))) := by
      have h3 : ∀ M : ℕ,
          (∏ j ∈ Finset.range M, (1 - qVar ^ (6 * j + 6))) *
          (∏ k ∈ Finset.range M, ((1 - qVar ^ (6 * k + 4)) * (1 - qVar ^ (6 * k + 2)))) =
          ∏ m ∈ Finset.range (3 * M), (1 - qVar ^ (2 * (m + 1))) := by
        intro M
        induction M with
        | zero => simp
        | succ M ih =>
          rw [Finset.prod_range_succ, Finset.prod_range_succ,
            show 3 * (M + 1) = 3 * M + 3 by omega,
            Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ]
          calc _ = ((∏ j ∈ Finset.range M, (1 - qVar ^ (6 * j + 6))) *
                    (∏ k ∈ Finset.range M, ((1 - qVar ^ (6 * k + 4)) * (1 - qVar ^ (6 * k + 2))))) *
                    ((1 - qVar ^ (6 * M + 2)) * (1 - qVar ^ (6 * M + 4)) *
                      (1 - qVar ^ (6 * M + 6))) := by ring
            _ = _ := by
                rw [ih]
                have e1 : 2 * (3 * M + 1) = 6 * M + 2 := by omega
                have e2 : 2 * (3 * M + 1 + 1) = 6 * M + 4 := by omega
                have e3 : 2 * (3 * M + 2 + 1) = 6 * M + 6 := by omega
                rw [e1, e2, e3]; ring
      exact h3 N
    have hexp2 : Polynomial.expand ℤ 2 (∏ m ∈ Finset.range (3 * N), (1 - qVar ^ (m + 1))) =
        ∏ m ∈ Finset.range (3 * N), (1 - qVar ^ (2 * (m + 1))) := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun m _ => ?_
      rw [map_sub, map_one, map_pow, Polynomial.expand_X, ← pow_mul]
    rw [hexp2, ← hmerge]; ring
  have hRHS : Polynomial.expand ℤ 3 evenProd * φ (P N) =
      ∑ r ∈ Finset.range (2 * N + 1),
        Polynomial.expand ℤ 3 ((P N).coeff r * evenProd) * (-qVar) ^ r := by
    conv_lhs => rw [P_eq_sum N]
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_mul, map_pow, hφ_C, hφ_z, map_mul]; ring
  have hcoeff := congrArg (fun f : QPoly => f.coeff (N + 2 * d)) (hLHS.symm.trans hRHS)
  have hLHS_c : ((-qVar) ^ N *
      Polynomial.expand ℤ 2 (∏ m ∈ Finset.range (3 * N), (1 - qVar ^ (m + 1)))).coeff (N + 2 * d) =
      (-1 : ℤ) ^ N * (∏ m ∈ Finset.range (3 * N), (1 - qVar ^ (m + 1))).coeff d := by
    have hpow : (-qVar) ^ N = Polynomial.C ((-1 : ℤ) ^ N) * qVar ^ N := by
      rw [show (-qVar : QPoly) = Polynomial.C (-1 : ℤ) * qVar by simp, mul_pow, map_pow]
    rw [hpow, mul_assoc, Polynomial.coeff_C_mul]
    congr 1
    change (Polynomial.X ^ N * _).coeff (N + 2 * d) = _
    rw [Polynomial.coeff_X_pow_mul']
    rw [if_pos (by omega), show N + 2 * d - N = 2 * d by omega,
      Polynomial.coeff_expand_mul' (by omega)]
  have hRHS_c : (∑ r ∈ Finset.range (2 * N + 1),
      Polynomial.expand ℤ 3 ((P N).coeff r * evenProd) * (-qVar) ^ r).coeff (N + 2 * d) =
      ∑ r ∈ Finset.range (2 * N + 1),
        (-1 : ℤ) ^ r * (if 3 * ((r : ℤ) - N).natAbs ^ 2 + r = N + 2 * d then 1 else 0) := by
    rw [Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hrle : r ≤ 2 * N := by have := Finset.mem_range.mp hr; omega
    have hpow : (-qVar) ^ r = Polynomial.C ((-1 : ℤ) ^ r) * qVar ^ r := by
      rw [show (-qVar : QPoly) = Polynomial.C (-1 : ℤ) * qVar by simp, mul_pow, map_pow]
    rw [hpow, ← mul_assoc, mul_comm _ (Polynomial.C _), mul_assoc, Polynomial.coeff_C_mul]
    congr 1
    change (_ * Polynomial.X ^ r).coeff (N + 2 * d) = _
    rw [Polynomial.coeff_mul_X_pow']
    by_cases hle : r ≤ N + 2 * d
    · rw [if_pos hle]
      rw [Polynomial.coeff_expand (by omega : 0 < 3)]
      by_cases hdvd : 3 ∣ (N + 2 * d - r)
      · rw [if_pos hdvd]
        set m := (N + 2 * d - r) / 3
        have hm3 : 3 * m = N + 2 * d - r := Nat.mul_div_cancel' hdvd
        set k := ((r : ℤ) - N).natAbs
        have hcond : m < k ^ 2 ∨ m < 2 * (N - k + 1) := by
          by_cases hk : k ≤ 2 * d + 1
          · right; omega
          · left
            have hm_le : m ≤ 2 * d + 1 := by omega
            have hk_ge : 2 * d + 2 ≤ k := by omega
            nlinarith
        have hmatch := P_coeff_mul_even_prod_coeff_any N r m hrle hcond
        change ((P N).coeff r * evenProd).coeff m = (Polynomial.X ^ (k ^ 2) : QPoly).coeff m at hmatch
        rw [hmatch, Polynomial.coeff_X_pow]
        split_ifs with h1 h2 h2
        · rfl
        · exfalso; apply h2; omega
        · exfalso; apply h1; omega
        · rfl
      · rw [if_neg hdvd]
        rw [if_neg]
        intro heq
        apply hdvd
        exact ⟨((r : ℤ) - N).natAbs ^ 2, by omega⟩
    · rw [if_neg hle, if_neg (by omega)]
  rw [hLHS_c, hRHS_c] at hcoeff
  have hzmod := congrArg (Int.cast : ℤ → ZMod 2) hcoeff
  have hneg1 : ∀ a : ℕ, (((-1 : ℤ) ^ a : ℤ) : ZMod 2) = 1 := fun a => by
    rw [Int.cast_pow]
    simp [show ((-1 : ℤ) : ZMod 2) = 1 by decide]
  rw [Int.cast_mul, hneg1 N, one_mul, Int.cast_sum] at hzmod
  rw [hzmod]
  have hsimp : (∑ r ∈ Finset.range (2 * N + 1),
      (((-1 : ℤ) ^ r * if 3 * ((r : ℤ) - N).natAbs ^ 2 + r = N + 2 * d then 1 else 0 : ℤ) : ZMod 2)) =
      ∑ r ∈ Finset.range (2 * N + 1),
        (if 3 * ((r : ℤ) - N).natAbs ^ 2 + r = N + 2 * d then (1 : ZMod 2) else 0) := by
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Int.cast_mul, hneg1 r, one_mul]
    split_ifs <;> simp
  rw [hsimp]
  by_cases hex : ∃ i : ℕ, pentNat i = d
  · rw [if_pos hex]
    obtain ⟨k, hk⟩ := (pentNat_iff_int d).mp hex
    have hkbound : k.natAbs ≤ N := by
      have h2 : (k.natAbs : ℤ) ^ 2 = k ^ 2 := Int.natAbs_sq k
      have h0 : (0 : ℤ) ≤ (k.natAbs : ℤ) := Int.natCast_nonneg _
      have hle1 : k ≤ (k.natAbs : ℤ) := Int.le_natAbs
      have hle2 : -k ≤ (k.natAbs : ℤ) := by
        have := Int.le_natAbs (a := -k)
        rwa [Int.natAbs_neg] at this
      have hN : (N : ℤ) = 4 * (d : ℤ) + 3 := by dsimp only [N]; push_cast; ring
      have hbound : (k.natAbs : ℤ) ≤ (N : ℤ) := by nlinarith only [hk, h2, h0, hle1, hle2, hN]
      exact_mod_cast hbound
    set r₀ : ℕ := (N + k).toNat
    have hr₀_eq : (r₀ : ℤ) = (N : ℤ) + k := by omega
    have hr₀_mem : r₀ ∈ Finset.range (2 * N + 1) := by
      rw [Finset.mem_range]; omega
    have hr₀_cond : 3 * ((r₀ : ℤ) - N).natAbs ^ 2 + r₀ = N + 2 * d := by
      have h1 : ((r₀ : ℤ) - N).natAbs = k.natAbs := by
        rw [hr₀_eq]; simp
      rw [h1]
      zify
      rw [sq_abs, hr₀_eq]
      linarith
    rw [Finset.sum_eq_single r₀]
    · rw [if_pos hr₀_cond]
    · intro r hr hne
      rw [if_neg]
      intro hcond
      apply hne
      set k' : ℤ := (r : ℤ) - N
      have hk'_eq : k' * (3 * k' + 1) = 2 * (d : ℤ) := by
        have hz : (3 * k'.natAbs ^ 2 + r : ℤ) = (N + 2 * d : ℤ) := by exact_mod_cast hcond
        dsimp only [k'] at hz ⊢
        nlinarith [Int.natAbs_sq ((r : ℤ) - N)]
      have hdiff : (k' - k) * (3 * (k' + k) + 1) = 0 := by linarith
      rcases mul_eq_zero.mp hdiff with h1 | h2
      · omega
      · omega
    · intro h; exact absurd hr₀_mem h
  · rw [if_neg hex]
    refine Finset.sum_eq_zero fun r hr => ?_
    rw [if_neg]
    intro hcond
    apply hex
    rw [pentNat_iff_int]
    refine ⟨(r : ℤ) - N, ?_⟩
    have hz : (3 * ((r : ℤ) - N).natAbs ^ 2 + r : ℤ) = (N + 2 * d : ℤ) := by
      exact_mod_cast hcond
    nlinarith [Int.natAbs_sq ((r : ℤ) - N)]

/-- Finite Jacobi cube identity over `ℤ[q]`: for `d : ℕ` and `N = 6 * d + 5`,
the coefficient of `q^d` in `(∏_{m=1}^N (1 - q^m))^3` mod 2 is the triangular number indicator. -/
private lemma jacobi_cube_fin_int (d : ℕ) :
    let N := 6 * d + 5
    (((∏ m ∈ Finset.range N, (1 - qVar ^ (m + 1))) ^ 3).coeff d : ZMod 2) =
      if ∃ m : ℕ, m * (m + 1) / 2 = d then 1 else 0 := by
  intro N
  set ψ : ZPoly →+* ZPoly :=
    Polynomial.eval₂RingHom Polynomial.C (Polynomial.C (-qVar) * zVar)
  have hψ_C (a : QPoly) : ψ (Polynomial.C a) = Polynomial.C a := by simp [ψ]
  have hψ_z : ψ zVar = Polynomial.C (-qVar) * zVar := by simp [ψ, zVar]
  set R : ZPoly :=
    Polynomial.C (qVar ^ N) *
      (∏ k ∈ Finset.range N, (1 - Polynomial.C (qVar ^ (2 * k + 2)) * zVar)) *
      (∏ k ∈ Finset.Ico 1 N, (Polynomial.C (qVar ^ (2 * k)) - zVar))
  have hψ_P : ψ (P N) = (1 - zVar) * R := by
    unfold P
    rw [map_prod]
    have hsplit : Finset.range N = insert 0 (Finset.Ico 1 N) := by
      ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
    have h0not : (0 : ℕ) ∉ Finset.Ico 1 N := by simp
    have hfac (k : ℕ) :
        ψ ((1 + Polynomial.C (qVar ^ (2 * k + 1)) * zVar) *
          (zVar + Polynomial.C (qVar ^ (2 * k + 1)))) =
        Polynomial.C qVar * (1 - Polynomial.C (qVar ^ (2 * k + 2)) * zVar) *
          (Polynomial.C (qVar ^ (2 * k)) - zVar) := by
      rw [map_mul, map_add, map_add, map_one, map_mul, hψ_C, hψ_z]
      have h1 : qVar ^ (2 * k + 2) = qVar * qVar * qVar ^ (2 * k) := by
        rw [pow_add, pow_two]; ring
      have h2 : qVar ^ (2 * k + 1) = qVar * qVar ^ (2 * k) := by rw [pow_succ']
      rw [h1, h2]
      simp only [Polynomial.C_mul, Polynomial.C_neg]
      ring
    simp_rw [hfac, Finset.prod_mul_distrib]
    rw [Finset.prod_const, Finset.card_range, ← Polynomial.C_pow]
    conv_lhs =>
      arg 2
      rw [hsplit, Finset.prod_insert h0not]
    simp only [mul_zero, pow_zero, map_one, R]
    ring
  have hderiv_eval1 : (Polynomial.derivative (ψ (P N))).eval 1 = -R.eval 1 := by
    rw [hψ_P, Polynomial.derivative_mul]
    simp [zVar]
  have hR_eval1 : R.eval 1 =
      (-1 : QPoly) ^ (N - 1) * qVar ^ N *
        (∏ j ∈ Finset.range N, (1 - qVar ^ (2 * (j + 1)))) *
        (∏ j ∈ Finset.range (N - 1), (1 - qVar ^ (2 * (j + 1)))) := by
    dsimp only [R]
    rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_prod, Polynomial.eval_prod]
    have h1 : (∏ k ∈ Finset.range N,
        Polynomial.eval 1 (1 - Polynomial.C (qVar ^ (2 * k + 2)) * zVar)) =
        ∏ j ∈ Finset.range N, (1 - qVar ^ (2 * (j + 1))) := by
      refine Finset.prod_congr rfl fun k _ => ?_
      simp [zVar, show 2 * (k + 1) = 2 * k + 2 by omega]
    have h2 : (∏ k ∈ Finset.Ico 1 N, Polynomial.eval 1 (Polynomial.C (qVar ^ (2 * k)) - zVar)) =
        (-1 : QPoly) ^ (N - 1) * ∏ j ∈ Finset.range (N - 1), (1 - qVar ^ (2 * (j + 1))) := by
      have hbij : Finset.Ico 1 N = (Finset.range (N - 1)).image (· + 1) := by
        ext k; simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
        constructor
        · intro ⟨h1, h2⟩; exact ⟨k - 1, by omega, by omega⟩
        · rintro ⟨j, hj, rfl⟩; omega
      rw [hbij, Finset.prod_image (fun a _ b _ h => by omega)]
      have hterm : ∀ j ∈ Finset.range (N - 1),
          Polynomial.eval 1 (Polynomial.C (qVar ^ (2 * (j + 1))) - zVar) =
          (-1 : QPoly) * (1 - qVar ^ (2 * (j + 1))) := by
        intro j _; simp [zVar]
      rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_range]
    rw [h1, h2]; ring
  set evenProd : QPoly := ∏ j ∈ Finset.range N, (1 - qVar ^ (2 * (j + 1)))
  have hRHS_eval1 : (Polynomial.derivative (ψ (P N))).eval 1 =
      ∑ r ∈ Finset.range (2 * N + 1), (r : QPoly) * (P N).coeff r * (-qVar) ^ r := by
    conv_lhs => rw [P_eq_sum N]
    rw [map_sum, map_sum, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_mul, map_pow, hψ_C, hψ_z, mul_pow, ← Polynomial.C_pow, ← mul_assoc,
      ← Polynomial.C_mul, Polynomial.derivative_C_mul_X_pow]
    simp
    ring
  have hEq : evenProd * (-R.eval 1) =
      ∑ r ∈ Finset.range (2 * N + 1), (r : QPoly) * ((P N).coeff r * evenProd) * (-qVar) ^ r := by
    rw [← hderiv_eval1, hRHS_eval1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => by ring
  have hcoeff := congrArg (fun f : QPoly => f.coeff (N + 2 * d)) hEq
  have hLHS_c : (evenProd * (-R.eval 1)).coeff (N + 2 * d) =
      (-1 : ℤ) ^ N * ((∏ m ∈ Finset.range N, (1 - qVar ^ (m + 1))) ^ 3).coeff d := by
    have hN1 : N - 1 + 1 = N := by omega
    have hprod_rel : evenProd * (-R.eval 1) =
        Polynomial.C ((-1 : ℤ) ^ N) * (qVar ^ N *
          (evenProd ^ 2 * ∏ j ∈ Finset.range (N - 1), (1 - qVar ^ (2 * (j + 1))))) := by
      rw [hR_eval1]
      have hneg : -((-1 : QPoly) ^ (N - 1)) = Polynomial.C ((-1 : ℤ) ^ N) := by
        conv_rhs => rw [← hN1]
        rw [map_pow, map_neg, map_one, pow_succ']
        ring
      calc evenProd * -((-1 : QPoly) ^ (N - 1) * qVar ^ N * evenProd *
              ∏ j ∈ Finset.range (N - 1), (1 - qVar ^ (2 * (j + 1))))
          = -((-1 : QPoly) ^ (N - 1)) * (qVar ^ N *
              (evenProd ^ 2 * ∏ j ∈ Finset.range (N - 1), (1 - qVar ^ (2 * (j + 1))))) := by ring
        _ = _ := by rw [hneg]
    rw [hprod_rel, Polynomial.coeff_C_mul]
    congr 1
    change (Polynomial.X ^ N * _).coeff (N + 2 * d) = _
    rw [Polynomial.coeff_X_pow_mul', if_pos (by omega), show N + 2 * d - N = 2 * d by omega]
    have hdrop : (evenProd ^ 2 * ∏ j ∈ Finset.range (N - 1), (1 - qVar ^ (2 * (j + 1)))).coeff (2 * d) =
        (evenProd ^ 3).coeff (2 * d) := by
      have hlast : evenProd =
          (∏ j ∈ Finset.range (N - 1), (1 - qVar ^ (2 * (j + 1)))) * (1 - qVar ^ (2 * N)) := by
        dsimp only [evenProd]
        conv_lhs => rw [← hN1]
        rw [Finset.prod_range_succ, hN1]
      have he3 : evenProd ^ 3 =
          (evenProd ^ 2 * ∏ j ∈ Finset.range (N - 1), (1 - qVar ^ (2 * (j + 1)))) *
            (1 - qVar ^ (2 * N)) := by
        calc evenProd ^ 3 = evenProd ^ 2 * evenProd := by ring
          _ = evenProd ^ 2 * ((∏ j ∈ Finset.range (N - 1), (1 - qVar ^ (2 * (j + 1)))) *
                (1 - qVar ^ (2 * N))) := by rw [hlast]
          _ = _ := by ring
      rw [he3, mul_sub, mul_one, Polynomial.coeff_sub]
      have h0 : ((evenProd ^ 2 * ∏ j ∈ Finset.range (N - 1), (1 - qVar ^ (2 * (j + 1)))) *
          qVar ^ (2 * N)).coeff (2 * d) = 0 := by
        change (_ * Polynomial.X ^ (2 * N)).coeff (2 * d) = 0
        rw [Polynomial.coeff_mul_X_pow', if_neg (by omega)]
      rw [h0, sub_zero]
    rw [hdrop]
    have hexp2 : evenProd ^ 3 =
        Polynomial.expand ℤ 2 ((∏ m ∈ Finset.range N, (1 - qVar ^ (m + 1))) ^ 3) := by
      rw [map_pow, map_prod]
      congr 1
      refine Finset.prod_congr rfl fun m _ => ?_
      rw [map_sub, map_one, map_pow, Polynomial.expand_X, ← pow_mul]
    rw [hexp2, Polynomial.coeff_expand_mul' (by omega)]
  have hRHS_c : (∑ r ∈ Finset.range (2 * N + 1),
      (r : QPoly) * ((P N).coeff r * evenProd) * (-qVar) ^ r).coeff (N + 2 * d) =
      ∑ r ∈ Finset.range (2 * N + 1),
        (r : ℤ) * (-1 : ℤ) ^ r * (if ((r : ℤ) - N).natAbs ^ 2 + r = N + 2 * d then 1 else 0) := by
    rw [Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hrle : r ≤ 2 * N := by have := Finset.mem_range.mp hr; omega
    have hpow : (r : QPoly) * ((P N).coeff r * evenProd) * (-qVar) ^ r =
        Polynomial.C ((r : ℤ) * (-1 : ℤ) ^ r) * (((P N).coeff r * evenProd) * qVar ^ r) := by
      have h1 : (-qVar : QPoly) ^ r = Polynomial.C ((-1 : ℤ) ^ r) * qVar ^ r := by
        rw [show (-qVar : QPoly) = Polynomial.C (-1 : ℤ) * qVar by simp, mul_pow, map_pow]
      rw [h1, map_mul, Polynomial.C_eq_natCast]; ring
    rw [hpow, Polynomial.coeff_C_mul]
    congr 1
    change (_ * Polynomial.X ^ r).coeff (N + 2 * d) = _
    rw [Polynomial.coeff_mul_X_pow']
    by_cases hle : r ≤ N + 2 * d
    · rw [if_pos hle]
      set m := N + 2 * d - r
      set k := ((r : ℤ) - N).natAbs
      have hcond : m < k ^ 2 ∨ m < 2 * (N - k + 1) := by
        by_cases hk : k ≤ 2 * d + 1
        · right; omega
        · left
          have hm_le : m ≤ 2 * d + k := by omega
          have hk_ge : 2 * d + 2 ≤ k := by omega
          nlinarith
      have hmatch := P_coeff_mul_even_prod_coeff_any N r m hrle hcond
      change ((P N).coeff r * evenProd).coeff m = (Polynomial.X ^ (k ^ 2) : QPoly).coeff m at hmatch
      rw [hmatch, Polynomial.coeff_X_pow]
      split_ifs with h1 h2 h2
      · rfl
      · exfalso; apply h2; omega
      · exfalso; apply h1; omega
      · rfl
    · rw [if_neg hle, if_neg (by omega)]
  rw [hLHS_c, hRHS_c] at hcoeff
  have hzmod := congrArg (Int.cast : ℤ → ZMod 2) hcoeff
  have hneg1 : ∀ a : ℕ, (((-1 : ℤ) ^ a : ℤ) : ZMod 2) = 1 := fun a => by
    rw [Int.cast_pow]
    simp [show ((-1 : ℤ) : ZMod 2) = 1 by decide]
  rw [Int.cast_mul, hneg1 N, one_mul, Int.cast_sum] at hzmod
  rw [hzmod]
  have hsimp : (∑ r ∈ Finset.range (2 * N + 1),
      (((r : ℤ) * (-1 : ℤ) ^ r *
        if ((r : ℤ) - N).natAbs ^ 2 + r = N + 2 * d then 1 else 0 : ℤ) : ZMod 2)) =
      ∑ r ∈ Finset.range (2 * N + 1),
        (if ((r : ℤ) - N).natAbs ^ 2 + r = N + 2 * d then (r : ZMod 2) else 0) := by
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Int.cast_mul, Int.cast_mul, hneg1 r, mul_one, Int.cast_natCast]
    split_ifs <;> simp
  rw [hsimp]
  by_cases hex : ∃ m : ℕ, m * (m + 1) / 2 = d
  · rw [if_pos hex]
    obtain ⟨m, hm⟩ := hex
    have hev : 2 * (m * (m + 1) / 2) = m * (m + 1) :=
      Nat.mul_div_cancel' (Nat.even_mul_succ_self m).two_dvd
    have hm2d : m * (m + 1) = 2 * d := by omega
    have hmle : m + 1 ≤ N := by dsimp only [N]; nlinarith only [hm2d]
    set r₁ : ℕ := N + m
    set r₂ : ℕ := N - (m + 1)
    have hr₁_mem : r₁ ∈ Finset.range (2 * N + 1) := by rw [Finset.mem_range]; omega
    have hr₂_mem : r₂ ∈ Finset.range (2 * N + 1) := by rw [Finset.mem_range]; omega
    have hne12 : r₁ ≠ r₂ := by omega
    have hc1 : ((r₁ : ℤ) - N).natAbs ^ 2 + r₁ = N + 2 * d := by
      have ha : ((r₁ : ℤ) - N).natAbs = m := by omega
      rw [ha]; dsimp only [r₁]; nlinarith only [hm2d]
    have hc2 : ((r₂ : ℤ) - N).natAbs ^ 2 + r₂ = N + 2 * d := by
      have ha : ((r₂ : ℤ) - N).natAbs = m + 1 := by omega
      have hr2_add : r₂ + (m + 1) = N := Nat.sub_add_cancel hmle
      rw [ha]; nlinarith only [hm2d, hr2_add]
    have honly : ∀ r ∈ Finset.range (2 * N + 1), r ≠ r₁ → r ≠ r₂ →
        (if ((r : ℤ) - N).natAbs ^ 2 + r = N + 2 * d then (r : ZMod 2) else 0) = 0 := by
      intro r _ h1 h2
      rw [if_neg]
      intro hcond
      set k : ℤ := (r : ℤ) - N
      have hkeq : k * (k + 1) = (m : ℤ) * ((m : ℤ) + 1) := by
        have hz : (k.natAbs : ℤ) ^ 2 + (r : ℤ) = (N : ℤ) + 2 * (d : ℤ) := by exact_mod_cast hcond
        have hm' : (m : ℤ) * ((m : ℤ) + 1) = 2 * (d : ℤ) := by exact_mod_cast hm2d
        have hsq : (k.natAbs : ℤ) ^ 2 = k ^ 2 := Int.natAbs_sq k
        have hkdef : k = (r : ℤ) - (N : ℤ) := rfl
        nlinarith only [hz, hm', hsq, hkdef]
      have hfac : (k - m) * (k + m + 1) = 0 := by linarith only [hkeq]
      rcases mul_eq_zero.mp hfac with ha | hb
      · apply h1; omega
      · apply h2; omega
    have hpair : ∑ r ∈ Finset.range (2 * N + 1),
        (if ((r : ℤ) - N).natAbs ^ 2 + r = N + 2 * d then (r : ZMod 2) else 0) =
        (r₁ : ZMod 2) + (r₂ : ZMod 2) := by
      have hsub : ({r₁, r₂} : Finset ℕ) ⊆ Finset.range (2 * N + 1) := by
        intro r hr
        simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with rfl | rfl <;> assumption
      rw [← Finset.sum_subset hsub]
      · rw [Finset.sum_pair hne12, if_pos hc1, if_pos hc2]
      · intro r hr hnot
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
        exact honly r hr hnot.1 hnot.2
    rw [hpair]
    have hodd : r₁ + r₂ = 2 * (N - 1) + 1 := by omega
    rw [← Nat.cast_add, hodd, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    have h2 : (2 : ZMod 2) = 0 := by decide
    simp [h2]
  · rw [if_neg hex]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [if_neg]
    intro hcond
    apply hex
    set k : ℤ := (r : ℤ) - N
    have hkeq : k * (k + 1) = 2 * (d : ℤ) := by
      have hz : (k.natAbs ^ 2 + r : ℤ) = (N + 2 * d : ℤ) := by exact_mod_cast hcond
      nlinarith [Int.natAbs_sq k]
    by_cases h0 : 0 ≤ k
    · set m : ℕ := k.toNat
      have hkm : k = (m : ℤ) := by omega
      rw [hkm] at hkeq
      refine ⟨m, ?_⟩
      have hm' : m * (m + 1) = 2 * d := by exact_mod_cast hkeq
      omega
    · set m : ℕ := (-k).toNat - 1
      have hkm : k = -((m + 1 : ℕ) : ℤ) := by omega
      rw [hkm] at hkeq
      refine ⟨m, ?_⟩
      have hm' : (m : ℤ) * ((m : ℤ) + 1) = 2 * (d : ℤ) := by push_cast at hkeq; linarith
      have hm'' : m * (m + 1) = 2 * d := by exact_mod_cast hm'
      omega

private lemma eulerPS_eq_prod_coeff (d M : ℕ) (hM : d ≤ M) :
    (∏ m ∈ Finset.range M, (1 - (PowerSeries.X : PowerSeries (ZMod 2)) ^ (m + 1))).coeff d =
      eulerPS.coeff d := by
  set N := 4 * d + 3
  set L := max M (3 * N)
  have hpoly : ∀ K : ℕ,
      (∏ m ∈ Finset.range K, (1 - (PowerSeries.X : PowerSeries (ZMod 2)) ^ (m + 1))) =
      ((∏ m ∈ Finset.range K, (1 - qVar ^ (m + 1))).map (Int.castRingHom (ZMod 2)) :
        PowerSeries (ZMod 2)) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ, Polynomial.map_mul,
        Polynomial.coe_mul, ih]
      simp [qVar]
  have htrim : ∀ K₁ K₂ : ℕ, d ≤ K₁ → K₁ ≤ K₂ →
      ((∏ m ∈ Finset.range K₂, (1 - qVar ^ (m + 1))).coeff d) =
      ((∏ m ∈ Finset.range K₁, (1 - qVar ^ (m + 1))).coeff d) := by
    intro K₁ K₂ hd h12
    have hsplit : Finset.range K₂ = Finset.range K₁ ∪ Finset.Ico K₁ K₂ := by
      ext j; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
    have hdisj : Disjoint (Finset.range K₁) (Finset.Ico K₁ K₂) :=
      Finset.disjoint_left.mpr fun j hj1 hj2 => by
        simp only [Finset.mem_range, Finset.mem_Ico] at hj1 hj2; omega
    rw [hsplit, Finset.prod_union hdisj]
    exact coeff_mul_prod_one_sub_q_pow (Finset.Ico K₁ K₂) (fun m => m + 1) d
      (fun m hm => by simp only [Finset.mem_Ico] at hm; omega) _
  rw [hpoly M, coeff_coe_poly_ps, coeff_map_int_zmod2]
  have h1 := htrim M L hM (le_max_left _ _)
  have h2 := htrim (3 * N) L (by omega) (le_max_right _ _)
  rw [← h1, h2]
  simpa [eulerPS] using euler_pentagonal_fin_int d

private lemma coeff_mul_eq_of_le {R : Type*} [Semiring R] {f f' g g' : PowerSeries R} {d : ℕ}
    (hf : ∀ m ≤ d, f.coeff m = f'.coeff m) (hg : ∀ m ≤ d, g.coeff m = g'.coeff m) :
    (f * g).coeff d = (f' * g').coeff d := by
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [hf p.1 (by omega), hg p.2 (by omega)]

private lemma eulerPS_cube_eq_triPS : eulerPS ^ 3 = triPS := by
  apply PowerSeries.ext
  intro d
  set N := 6 * d + 5
  set P_N : PowerSeries (ZMod 2) :=
    ∏ m ∈ Finset.range N, (1 - (PowerSeries.X : PowerSeries (ZMod 2)) ^ (m + 1))
  have hagree : ∀ m ≤ d, eulerPS.coeff m = P_N.coeff m := fun m hm =>
    (eulerPS_eq_prod_coeff m N (by omega)).symm
  have h2 : ∀ m ≤ d, (eulerPS * eulerPS).coeff m = (P_N * P_N).coeff m := fun m hm =>
    coeff_mul_eq_of_le (fun j hj => hagree j (by omega)) (fun j hj => hagree j (by omega))
  have h3 : (eulerPS ^ 3).coeff d = (P_N ^ 3).coeff d := by
    rw [pow_succ, pow_succ, pow_one, pow_succ, pow_succ, pow_one]
    exact coeff_mul_eq_of_le h2 hagree
  rw [h3]
  have hpoly : P_N ^ 3 =
      (((∏ m ∈ Finset.range N, (1 - qVar ^ (m + 1))) ^ 3).map (Int.castRingHom (ZMod 2)) :
        PowerSeries (ZMod 2)) := by
    have hbase : P_N =
        ((∏ m ∈ Finset.range N, (1 - qVar ^ (m + 1))).map (Int.castRingHom (ZMod 2)) :
          PowerSeries (ZMod 2)) := by
      dsimp only [P_N]
      induction N with
      | zero => simp
      | succ K ih =>
        rw [Finset.prod_range_succ, Finset.prod_range_succ, Polynomial.map_mul,
          Polynomial.coe_mul, ih]
        simp [qVar]
    rw [hbase, Polynomial.map_pow, Polynomial.coe_pow]
  rw [hpoly, coeff_coe_poly_ps, coeff_map_int_zmod2]
  simpa [triPS] using jacobi_cube_fin_int d

private lemma partPS_mul_eulerPS : partPS * eulerPS = 1 := by
  let _ : TopologicalSpace (ZMod 2) := ⊥
  have _ : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  have hgen : partPS = Nat.Partition.genFun (fun _ _ => (1 : ZMod 2)) := by
    apply PowerSeries.ext
    intro n
    simp [partPS, Nat.Partition.coeff_genFun, Nat.partitionNumber]
  let f : ℕ → PowerSeries (ZMod 2) :=
    fun i => 1 + ∑' j, (1 : ZMod 2) • (PowerSeries.X : PowerSeries (ZMod 2)) ^ ((i + 1) * (j + 1))
  have hf_coeff (i m : ℕ) : (f i).coeff m = if (i + 1) ∣ m then 1 else 0 := by
    dsimp only [f]
    rw [map_add, (Nat.Partition.summable_genFun_term (fun _ _ => (1 : ZMod 2)) i).map_tsum _
      (PowerSeries.WithPiTopology.continuous_coeff _ _)]
    rcases m with _ | m
    · simp only [PowerSeries.coeff_one, ↓reduceIte, dvd_zero]
      simp
    · simp only [PowerSeries.coeff_one, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
        zero_add]
      by_cases hd : (i + 1) ∣ (m + 1)
      · rw [if_pos hd]
        obtain ⟨q, hq⟩ := hd
        have hqpos : 1 ≤ q := by
          rcases q with _ | q
          · simp at hq
          · omega
        rw [tsum_eq_single (q - 1)]
        · rw [map_smul, one_smul, PowerSeries.coeff_X_pow, if_pos]
          rw [Nat.sub_add_cancel hqpos, ← hq]
        · intro b hb
          rw [map_smul, one_smul, PowerSeries.coeff_X_pow, if_neg]
          intro heq
          apply hb
          have : (i + 1) * q = (i + 1) * (b + 1) := by omega
          have hqb := Nat.eq_of_mul_eq_mul_left (Nat.succ_pos i) this
          omega
      · rw [if_neg hd]
        have h0 : ∀ j : ℕ, ((1 : ZMod 2) •
            (PowerSeries.X : PowerSeries (ZMod 2)) ^ ((i + 1) * (j + 1))).coeff (m + 1) = 0 := by
          intro j
          rw [map_smul, one_smul, PowerSeries.coeff_X_pow, if_neg]
          intro heq
          exact hd ⟨j + 1, heq⟩
        rw [tsum_congr h0, tsum_zero]
  have hf_inv (i : ℕ) : f i * (1 - (PowerSeries.X : PowerSeries (ZMod 2)) ^ (i + 1)) = 1 := by
    apply PowerSeries.ext
    intro m
    rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_mul_X_pow', hf_coeff]
    by_cases hm : i + 1 ≤ m
    · rw [if_pos hm, hf_coeff]
      have hdvd : (i + 1) ∣ m ↔ (i + 1) ∣ (m - (i + 1)) := by
        constructor
        · rintro ⟨q, hq⟩
          refine ⟨q - 1, ?_⟩
          have hq1 : 1 ≤ q := by
            rcases q with _ | q
            · omega
            · omega
          rw [Nat.mul_sub, mul_one, ← hq]
        · rintro ⟨q, hq⟩
          exact ⟨q + 1, by rw [mul_add, mul_one, ← hq, Nat.sub_add_cancel hm]⟩
      simp only [hdvd, sub_self, PowerSeries.coeff_one, if_neg (by omega : m ≠ 0)]
    · rw [if_neg hm, sub_zero, PowerSeries.coeff_one]
      have hdvd : (i + 1) ∣ m ↔ m = 0 := by
        constructor
        · intro h
          rcases m with _ | m
          · rfl
          · exfalso; exact hm (Nat.le_of_dvd (Nat.succ_pos m) h)
        · rintro rfl; exact dvd_zero _
      simp only [hdvd]
  have hprod := Nat.Partition.hasProd_genFun (fun _ _ => (1 : ZMod 2))
  rw [← hgen] at hprod
  rw [HasProd, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto] at hprod
  apply PowerSeries.ext
  intro d
  have hev : ∀ m ∈ Finset.range (d + 1),
      ∃ s₀ : Finset ℕ, ∀ s : Finset ℕ, s₀ ⊆ s → (∏ i ∈ s, f i).coeff m = partPS.coeff m := by
    intro m _
    have hm := (tendsto_nhds.mp (hprod m)) {partPS.coeff m} (isOpen_discrete _) (Set.mem_singleton _)
    obtain ⟨s₀, hs₀⟩ := Filter.eventually_atTop.mp hm
    exact ⟨s₀, fun s hs => Set.mem_singleton_iff.mp (hs₀ s hs)⟩
  choose s₀ hs₀ using hev
  let S : Finset ℕ := (Finset.range (d + 1)).attach.biUnion (fun m => s₀ m.1 m.2)
  let N : ℕ := max d (S.sup id + 1)
  have hrange : ∀ (m : ℕ) (hm : m ∈ Finset.range (d + 1)), s₀ m hm ⊆ Finset.range N := by
    intro m hm x hx
    rw [Finset.mem_range]
    have hxS : x ∈ S := Finset.mem_biUnion.mpr ⟨⟨m, hm⟩, Finset.mem_attach _ _, hx⟩
    have hxle : x ≤ S.sup id := Finset.le_sup (f := id) hxS
    omega
  have hP_agree : ∀ m ≤ d, partPS.coeff m = (∏ i ∈ Finset.range N, f i).coeff m := by
    intro m hm
    have hm' : m ∈ Finset.range (d + 1) := Finset.mem_range.mpr (by omega)
    exact (hs₀ m hm' (Finset.range N) (hrange m hm')).symm
  have hE_agree : ∀ m ≤ d, eulerPS.coeff m =
      (∏ i ∈ Finset.range N, (1 - (PowerSeries.X : PowerSeries (ZMod 2)) ^ (i + 1))).coeff m := by
    intro m hm
    exact (eulerPS_eq_prod_coeff m N (by omega)).symm
  rw [coeff_mul_eq_of_le hP_agree hE_agree, ← Finset.prod_mul_distrib]
  have hone : ∏ i ∈ Finset.range N, (f i * (1 - (PowerSeries.X : PowerSeries (ZMod 2)) ^ (i + 1))) = 1 :=
    Finset.prod_eq_one fun i _ => hf_inv i
  rw [hone]

/- ### Section 3: Frobenius, expansion, and the mod-2 partition convolution -/

private noncomputable def expandPS (s : ℕ) (f : PowerSeries (ZMod 2)) : PowerSeries (ZMod 2) :=
  PowerSeries.mk fun n => if s ∣ n then f.coeff (n / s) else 0

private lemma coeff_expandPS (s : ℕ) (f : PowerSeries (ZMod 2)) (n : ℕ) :
    (expandPS s f).coeff n = if s ∣ n then f.coeff (n / s) else 0 := by
  simp [expandPS]

private lemma expandPS_one (s : ℕ) (hs : 0 < s) : expandPS s 1 = 1 := by
  apply PowerSeries.ext
  intro n
  rw [coeff_expandPS, PowerSeries.coeff_one, PowerSeries.coeff_one]
  rcases n with _ | n
  · simp
  · rw [if_neg (Nat.succ_ne_zero n)]
    split_ifs with hd hdiv0
    · exfalso
      obtain ⟨q, hq⟩ := hd
      have hqne : q ≠ 0 := by rintro rfl; simp at hq
      have hdiv : (n + 1) / s = q := by rw [hq, Nat.mul_div_cancel_left q hs]
      omega
    · rfl
    · rfl

private lemma expandPS_mul (s : ℕ) (hs : 0 < s) (f g : PowerSeries (ZMod 2)) :
    expandPS s (f * g) = expandPS s f * expandPS s g := by
  apply PowerSeries.ext
  intro n
  rw [coeff_expandPS]
  by_cases hd : s ∣ n
  · rw [if_pos hd, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    obtain ⟨q, rfl⟩ := hd
    rw [Nat.mul_div_cancel_left q hs]
    let emb : ℕ × ℕ → ℕ × ℕ := fun p => (s * p.1, s * p.2)
    have hemb_inj : Function.Injective emb := by
      intro p₁ p₂ h
      have h1 : s * p₁.1 = s * p₂.1 := congrArg Prod.fst h
      have h2 : s * p₁.2 = s * p₂.2 := congrArg Prod.snd h
      exact Prod.ext (Nat.eq_of_mul_eq_mul_left hs h1) (Nat.eq_of_mul_eq_mul_left hs h2)
    have hsub : (Finset.HasAntidiagonal.antidiagonal q).image emb ⊆
        Finset.HasAntidiagonal.antidiagonal (s * q) := by
      intro p hp
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hp
      have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hr
      rw [Finset.HasAntidiagonal.mem_antidiagonal]
      dsimp only [emb]
      rw [← mul_add, hsum]
    symm
    rw [← Finset.sum_subset hsub]
    · rw [Finset.sum_image (fun a _ b _ h => hemb_inj h)]
      refine Finset.sum_congr rfl fun p _ => ?_
      dsimp only [emb]
      rw [coeff_expandPS, coeff_expandPS, if_pos (dvd_mul_right s p.1),
        if_pos (dvd_mul_right s p.2), Nat.mul_div_cancel_left p.1 hs,
        Nat.mul_div_cancel_left p.2 hs]
    · intro p hp hnot
      rw [coeff_expandPS, coeff_expandPS]
      by_cases h1 : s ∣ p.1
      · by_cases h2 : s ∣ p.2
        · exfalso
          apply hnot
          obtain ⟨a, ha⟩ := h1
          obtain ⟨b, hb⟩ := h2
          have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
          have hab : a + b = q := Nat.eq_of_mul_eq_mul_left hs (by rw [mul_add, ← ha, ← hb, hsum])
          exact Finset.mem_image.mpr ⟨(a, b), Finset.HasAntidiagonal.mem_antidiagonal.mpr hab,
            Prod.ext ha.symm hb.symm⟩
        · rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
  · rw [if_neg hd, PowerSeries.coeff_mul]
    symm
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [coeff_expandPS, coeff_expandPS]
    by_cases h1 : s ∣ p.1
    · have h2 : ¬ s ∣ p.2 := by
        intro h2
        apply hd
        rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
        exact dvd_add h1 h2
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

private lemma expandPS_pow (s : ℕ) (hs : 0 < s) (f : PowerSeries (ZMod 2)) (m : ℕ) :
    expandPS s (f ^ m) = (expandPS s f) ^ m := by
  induction m with
  | zero => simp [expandPS_one s hs]
  | succ m ih => rw [pow_succ, pow_succ, expandPS_mul s hs, ih]

private lemma expandPS_comp (r s : ℕ) (hs : 0 < s) (f : PowerSeries (ZMod 2)) :
    expandPS s (expandPS r f) = expandPS (r * s) f := by
  apply PowerSeries.ext
  intro n
  rw [coeff_expandPS, coeff_expandPS, coeff_expandPS]
  by_cases h1 : s ∣ n
  · rw [if_pos h1]
    by_cases h2 : r ∣ n / s
    · rw [if_pos h2]
      have h12 : r * s ∣ n := by
        obtain ⟨a, ha⟩ := h1
        obtain ⟨b, hb⟩ := h2
        rw [ha, Nat.mul_div_cancel_left a hs] at hb
        exact ⟨b, by rw [ha, hb]; ring⟩
      rw [if_pos h12, Nat.div_div_eq_div_mul, mul_comm s r]
    · rw [if_neg h2]
      have hnot : ¬ r * s ∣ n := by
        intro h12
        apply h2
        obtain ⟨c, hc⟩ := h12
        refine ⟨c, ?_⟩
        have : n = s * (r * c) := by rw [hc]; ring
        rw [this, Nat.mul_div_cancel_left _ hs]
      rw [if_neg hnot]
  · rw [if_neg h1]
    have hnot : ¬ r * s ∣ n := fun h => h1 (dvd_of_mul_left_dvd h)
    rw [if_neg hnot]

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> rfl

private lemma zmod2_mul_self (a : ZMod 2) : a * a = a := by
  fin_cases a <;> rfl

private lemma pow_two_eq_expandPS (f : PowerSeries (ZMod 2)) : f ^ 2 = expandPS 2 f := by
  apply PowerSeries.ext
  intro n
  rw [sq, PowerSeries.coeff_mul, coeff_expandPS]
  let S := Finset.HasAntidiagonal.antidiagonal n
  let Slt := S.filter (fun p => p.1 < p.2)
  let Sgt := S.filter (fun p => p.2 < p.1)
  let Seq := S.filter (fun p => p.1 = p.2)
  have hpart : S = (Slt ∪ Sgt) ∪ Seq := by
    ext p
    simp only [Slt, Sgt, Seq, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hp
      rcases lt_trichotomy p.1 p.2 with h | h | h
      · exact Or.inl (Or.inl ⟨hp, h⟩)
      · exact Or.inr ⟨hp, h⟩
      · exact Or.inl (Or.inr ⟨hp, h⟩)
    · rintro ((⟨hp, _⟩ | ⟨hp, _⟩) | ⟨hp, _⟩) <;> exact hp
  have hd1 : Disjoint Slt Sgt := Finset.disjoint_left.mpr fun p h1 h2 => by
    simp only [Slt, Sgt, Finset.mem_filter] at h1 h2; omega
  have hd2 : Disjoint (Slt ∪ Sgt) Seq := Finset.disjoint_left.mpr fun p h1 h2 => by
    simp only [Slt, Sgt, Seq, Finset.mem_union, Finset.mem_filter] at h1 h2
    rcases h1 with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  change (∑ p ∈ S, f.coeff p.1 * f.coeff p.2) = _
  rw [hpart, Finset.sum_union hd2, Finset.sum_union hd1]
  have hswap : (∑ p ∈ Sgt, f.coeff p.1 * f.coeff p.2) = ∑ p ∈ Slt, f.coeff p.1 * f.coeff p.2 := by
    refine Finset.sum_nbij Prod.swap ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Sgt, Slt, S, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal,
        Prod.fst_swap, Prod.snd_swap] at hp ⊢
      exact ⟨by omega, hp.2⟩
    · intro p₁ _ p₂ _ h
      exact Prod.swap_injective h
    · intro p hp
      refine ⟨p.swap, ?_, by simp⟩
      simp only [Finset.mem_coe, Sgt, Slt, S, Finset.mem_filter,
        Finset.HasAntidiagonal.mem_antidiagonal, Prod.fst_swap, Prod.snd_swap] at hp ⊢
      exact ⟨by omega, hp.2⟩
    · intro p _
      simp [mul_comm]
  rw [hswap, zmod2_add_self, zero_add]
  by_cases h2 : 2 ∣ n
  · rw [if_pos h2]
    obtain ⟨q, rfl⟩ := h2
    rw [Nat.mul_div_cancel_left q (by omega)]
    have hseq : Seq = {(q, q)} := by
      ext p
      simp only [Seq, S, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal,
        Finset.mem_singleton, Prod.ext_iff]
      omega
    rw [hseq, Finset.sum_singleton, zmod2_mul_self]
  · rw [if_neg h2]
    have hseq : Seq = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro p hp
      simp only [Seq, S, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp
      exact h2 ⟨p.1, by omega⟩
    rw [hseq, Finset.sum_empty]

private lemma pow_two_pow_eq_expandPS (f : PowerSeries (ZMod 2)) (r : ℕ) :
    f ^ (2 ^ r) = expandPS (2 ^ r) f := by
  induction r with
  | zero =>
    apply PowerSeries.ext
    intro n
    simp [expandPS]
  | succ r ih =>
    rw [pow_succ, pow_mul, ih, pow_two_eq_expandPS, expandPS_comp (2 ^ r) 2 (by omega)]

private noncomputable def deltaPS : PowerSeries (ZMod 2) :=
  PowerSeries.mk fun n => if n % 2 = 1 ∧ n.sqrt ^ 2 = n then 1 else 0

private lemma deltaPS_eq : deltaPS = PowerSeries.X * expandPS 8 (eulerPS ^ 3) := by
  rw [eulerPS_cube_eq_triPS]
  apply PowerSeries.ext
  intro n
  rcases n with _ | n
  · simp [deltaPS]
  · rw [PowerSeries.coeff_succ_X_mul, coeff_expandPS]
    simp only [deltaPS, PowerSeries.coeff_mk, triPS]
    have hiff : ((n + 1) % 2 = 1 ∧ (n + 1).sqrt ^ 2 = n + 1) ↔
        (8 ∣ n ∧ ∃ m : ℕ, m * (m + 1) / 2 = n / 8) := by
      constructor
      · rintro ⟨hodd, hsq⟩
        set s := (n + 1).sqrt
        have hsodd : s % 2 = 1 := by
          by_contra hev
          have h0 : s % 2 = 0 := by omega
          have : s ^ 2 % 2 = 0 := by
            obtain ⟨a, ha⟩ : ∃ a, s = 2 * a := ⟨s / 2, by omega⟩
            rw [ha, show (2 * a) ^ 2 = 2 * (2 * a * a) by ring]; omega
          omega
        set m := s / 2
        have hsm : s = 2 * m + 1 := by omega
        have hn : n = 4 * (m * (m + 1)) := by
          have : (2 * m + 1) ^ 2 = n + 1 := by rwa [← hsm]
          nlinarith
        have hev : 2 * (m * (m + 1) / 2) = m * (m + 1) :=
          Nat.mul_div_cancel' (Nat.even_mul_succ_self m).two_dvd
        have hn8 : n = 8 * (m * (m + 1) / 2) := by omega
        exact ⟨⟨m * (m + 1) / 2, hn8⟩, ⟨m, by rw [hn8, Nat.mul_div_cancel_left _ (by omega)]⟩⟩
      · rintro ⟨h8, m, hm⟩
        have hev : 2 * (m * (m + 1) / 2) = m * (m + 1) :=
          Nat.mul_div_cancel' (Nat.even_mul_succ_self m).two_dvd
        have hn8 : 8 * (n / 8) = n := Nat.mul_div_cancel' h8
        have hn : n + 1 = (2 * m + 1) ^ 2 := by nlinarith
        rw [hn]
        refine ⟨by omega, ?_⟩
        rw [show (2 * m + 1) ^ 2 = (2 * m + 1) * (2 * m + 1) by ring, Nat.sqrt_eq]
        ring
    by_cases h1 : (n + 1) % 2 = 1 ∧ (n + 1).sqrt ^ 2 = n + 1
    · rw [if_pos h1]
      obtain ⟨h8, hm⟩ := hiff.mp h1
      rw [if_pos h8, if_pos hm]
    · rw [if_neg h1]
      by_cases h8 : 8 ∣ n
      · rw [if_pos h8]
        have hnotm : ¬ ∃ m : ℕ, m * (m + 1) / 2 = n / 8 := fun hm => h1 (hiff.mpr ⟨h8, hm⟩)
        rw [if_neg hnotm]
      · rw [if_neg h8]

private lemma deltaPS_pow_eq (t : ℕ) :
    let k := (4 ^ t - 1) / 3
    deltaPS ^ k =
      (PowerSeries.X : PowerSeries (ZMod 2)) ^ k *
        expandPS 8 (partPS * expandPS (4 ^ t) eulerPS) := by
  intro k
  have h3dvd : 3 ∣ 4 ^ t - 1 := by
    induction t with
    | zero => simp
    | succ t ih =>
      have hpos : 1 ≤ 4 ^ t := Nat.one_le_pow t 4 (by omega)
      have heq : 4 ^ (t + 1) - 1 = 4 * (4 ^ t - 1) + 3 := by
        rw [pow_succ]; omega
      rw [heq]
      exact dvd_add (dvd_mul_of_dvd_right ih 4) (dvd_refl 3)
  have h3k : 3 * k + 1 = 4 ^ t := by
    have hpos : 1 ≤ 4 ^ t := Nat.one_le_pow t 4 (by omega)
    have := Nat.mul_div_cancel' h3dvd
    omega
  have hpow4 : (4 : ℕ) ^ t = 2 ^ (2 * t) := by
    rw [pow_mul]; norm_num
  have hstep1 : expandPS 8 eulerPS * deltaPS ^ k =
      (PowerSeries.X : PowerSeries (ZMod 2)) ^ k * expandPS 8 (expandPS (4 ^ t) eulerPS) := by
    rw [deltaPS_eq, expandPS_pow 8 (by omega) eulerPS 3, mul_pow, ← pow_mul, mul_left_comm,
      ← pow_succ', h3k, hpow4, pow_two_pow_eq_expandPS, ← hpow4,
      expandPS_comp 8 (4 ^ t) (by positivity),
      expandPS_comp (4 ^ t) 8 (by omega), mul_comm (4 ^ t) 8]
  have hinv : expandPS 8 partPS * expandPS 8 eulerPS = 1 := by
    rw [← expandPS_mul 8 (by omega), partPS_mul_eulerPS, expandPS_one 8 (by omega)]
  calc deltaPS ^ k
      = 1 * deltaPS ^ k := (one_mul _).symm
    _ = expandPS 8 partPS * (expandPS 8 eulerPS * deltaPS ^ k) := by rw [← hinv, mul_assoc]
    _ = expandPS 8 partPS * ((PowerSeries.X : PowerSeries (ZMod 2)) ^ k *
          expandPS 8 (expandPS (4 ^ t) eulerPS)) := by rw [hstep1]
    _ = (PowerSeries.X : PowerSeries (ZMod 2)) ^ k *
          (expandPS 8 partPS * expandPS 8 (expandPS (4 ^ t) eulerPS)) := by ring
    _ = (PowerSeries.X : PowerSeries (ZMod 2)) ^ k *
          expandPS 8 (partPS * expandPS (4 ^ t) eulerPS) := by
        rw [← expandPS_mul 8 (by omega)]

private def pentIdx (D2 n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun i => D2 * pentNat i ≤ n)

private lemma mem_pentIdx_iff {D2 n i : ℕ} (hD2 : 1 ≤ D2) :
    i ∈ pentIdx D2 n ↔ D2 * pentNat i ≤ n := by
  simp only [pentIdx, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  intro hle
  have hi : i ≤ pentNat i := le_pentNat i
  have h1 : pentNat i ≤ D2 * pentNat i := Nat.le_mul_of_pos_left _ hD2
  omega

private lemma coeff_deltaPS_pow_conv (t n : ℕ) :
    let k := (4 ^ t - 1) / 3
    (deltaPS ^ k).coeff (8 * n + k) =
      ∑ i ∈ pentIdx (4 ^ t) n, (Nat.partitionNumber (n - 4 ^ t * pentNat i) : ZMod 2) := by
  intro k
  have hD2 : 0 < 4 ^ t := by positivity
  rw [deltaPS_pow_eq t, show 8 * n + k = k + 8 * n by omega,
    PowerSeries.coeff_X_pow_mul', if_pos (by omega), show k + 8 * n - k = 8 * n by omega,
    coeff_expandPS, if_pos (dvd_mul_right 8 n), Nat.mul_div_cancel_left n (by omega),
    PowerSeries.coeff_mul]
  let emb : ℕ → ℕ × ℕ := fun i => (n - 4 ^ t * pentNat i, 4 ^ t * pentNat i)
  have hemb_inj : Set.InjOn emb (pentIdx (4 ^ t) n : Set ℕ) := by
    intro i₁ _ i₂ _ h
    have h2 : 4 ^ t * pentNat i₁ = 4 ^ t * pentNat i₂ := congrArg Prod.snd h
    exact pentNat_strictMono.injective (Nat.eq_of_mul_eq_mul_left hD2 h2)
  have hsub : (pentIdx (4 ^ t) n).image emb ⊆ Finset.HasAntidiagonal.antidiagonal n := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    have hle : 4 ^ t * pentNat i ≤ n := (mem_pentIdx_iff hD2).mp hi
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    dsimp only [emb]
    omega
  rw [← Finset.sum_subset hsub]
  · rw [Finset.sum_image hemb_inj]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only [emb]
    rw [coeff_expandPS, if_pos (dvd_mul_right (4 ^ t) (pentNat i)),
      Nat.mul_div_cancel_left _ hD2]
    simp only [partPS, eulerPS, PowerSeries.coeff_mk]
    rw [if_pos ⟨i, rfl⟩, mul_one]
  · intro p hp hnot
    rw [coeff_expandPS]
    by_cases hd : 4 ^ t ∣ p.2
    · rw [if_pos hd]
      simp only [eulerPS, PowerSeries.coeff_mk]
      by_cases hex : ∃ i : ℕ, pentNat i = p.2 / 4 ^ t
      · exfalso
        obtain ⟨i, hi⟩ := hex
        have hp2 : 4 ^ t * pentNat i = p.2 := by
          rw [hi]; exact Nat.mul_div_cancel' hd
        have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
        have hle : 4 ^ t * pentNat i ≤ n := by omega
        apply hnot
        refine Finset.mem_image.mpr ⟨i, (mem_pentIdx_iff hD2).mpr hle, ?_⟩
        exact Prod.ext (by dsimp only [emb]; omega) hp2
      · rw [if_neg hex, mul_zero]
    · rw [if_neg hd, mul_zero]

private lemma exists_even_of_coeff_zero_odd_card {t n : ℕ}
    (hzero : (deltaPS ^ ((4 ^ t - 1) / 3)).coeff (8 * n + (4 ^ t - 1) / 3) = 0)
    (hodd : Odd (pentIdx (4 ^ t) n).card) :
    ∃ i ∈ pentIdx (4 ^ t) n, Even (Nat.partitionNumber (n - 4 ^ t * pentNat i)) := by
  by_contra hno
  push Not at hno
  have hconv := coeff_deltaPS_pow_conv t n
  dsimp only at hconv
  rw [hzero] at hconv
  have hall1 : ∀ i ∈ pentIdx (4 ^ t) n,
      (Nat.partitionNumber (n - 4 ^ t * pentNat i) : ZMod 2) = 1 := by
    intro i hi
    have hodd_p : Odd (Nat.partitionNumber (n - 4 ^ t * pentNat i)) :=
      Nat.not_even_iff_odd.mp (hno i hi)
    obtain ⟨m, hm⟩ := hodd_p
    rw [hm, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    have h2 : (2 : ZMod 2) = 0 := by decide
    simp [h2]
  rw [Finset.sum_congr rfl hall1, Finset.sum_const, nsmul_eq_mul, mul_one] at hconv
  obtain ⟨m, hm⟩ := hodd
  rw [hm, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hconv
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [h2, zero_mul, zero_add] at hconv
  exact zero_ne_one hconv

/- ### Section 4: Odd-length pentagonal intervals and double counting -/

private lemma sum_odd_range (J : ℕ) : (∑ j ∈ Finset.range J, (2 * j + 1)) = J ^ 2 := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    ring

private lemma bellaiche_nicolas_conv_bound (x : ℝ) (t : ℕ) (ht : 0 < t)
    (hD : 16 * (2 : ℝ) ^ t ≤ Real.sqrt x)
    (hsparse : ({n : ℕ | (n : ℝ) ≤ 8 * x + (((4 ^ t - 1) / 3 : ℕ) : ℝ) ∧
      PowerSeries.coeff n (deltaPS ^ ((4 ^ t - 1) / 3)) ≠ 0}.ncard : ℝ) ≤ x / 8) :
    Real.sqrt x * (2 : ℝ) ^ t ≤
      16 * ({n : ℕ | (n : ℝ) ≤ x ∧ Even (Nat.partitionNumber n)}.ncard : ℝ) := by
  set D : ℕ := 2 ^ t
  set D2 : ℕ := 4 ^ t
  set k : ℕ := (4 ^ t - 1) / 3
  have hD_pos : 0 < D := by positivity
  have hD2_pos : 0 < D2 := by positivity
  have hD2_eq : D2 = D * D := by
    dsimp only [D, D2]
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have hD_cast : (D : ℝ) = (2 : ℝ) ^ t := by push_cast [D]; rfl
  have hD2_cast : (D2 : ℝ) = (D : ℝ) ^ 2 := by rw [hD2_eq]; push_cast; ring
  have hsqrt_ge : 32 ≤ Real.sqrt x := by
    have h2t : (2 : ℝ) ≤ (2 : ℝ) ^ t := by
      have : 2 ≤ 2 ^ t := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ t := Nat.pow_le_pow_right (by omega) ht
      exact_mod_cast this
    linarith
  have hx_pos : 0 < x := by
    by_contra hle
    push Not at hle
    have : Real.sqrt x = 0 := Real.sqrt_eq_zero_of_nonpos hle
    linarith
  have hx_ge_256D2 : 256 * (D2 : ℝ) ≤ x := by
    have hsq : (16 * (D : ℝ)) ^ 2 ≤ (Real.sqrt x) ^ 2 := by
      rw [hD_cast]
      exact pow_le_pow_left₀ (by positivity) hD 2
    rw [Real.sq_sqrt hx_pos.le] at hsq
    rw [hD2_cast]
    nlinarith
  set Nx : ℕ := ⌊x⌋₊
  have hNx_le : (Nx : ℝ) ≤ x := Nat.floor_le hx_pos.le
  have hx_lt_Nx1 : x < (Nx : ℝ) + 1 := Nat.lt_floor_add_one x
  have hNx_ge : 256 * D2 ≤ Nx := by
    exact Nat.le_floor (by exact_mod_cast hx_ge_256D2)
  let SJ : Finset ℕ := (Finset.range (Nx + 1)).filter (fun j => D2 * pentNat (2 * j) ≤ Nx)
  have hSJ_ne : SJ.Nonempty := ⟨0, by simp [SJ, pentNat_zero]⟩
  set J : ℕ := SJ.max' hSJ_ne
  have hJ_mem : J ∈ SJ := Finset.max'_mem SJ hSJ_ne
  have hJ_le : D2 * pentNat (2 * J) ≤ Nx := (Finset.mem_filter.mp hJ_mem).2
  have hJ_gt : Nx < D2 * pentNat (2 * (J + 1)) := by
    by_contra hle
    push Not at hle
    have hJ1_mem : J + 1 ∈ SJ := by
      rw [Finset.mem_filter, Finset.mem_range]
      have h1 : J + 1 ≤ pentNat (2 * (J + 1)) := by
        have := le_pentNat (2 * (J + 1)); omega
      have h2 : pentNat (2 * (J + 1)) ≤ D2 * pentNat (2 * (J + 1)) :=
        Nat.le_mul_of_pos_left _ hD2_pos
      exact ⟨by omega, hle⟩
    have hmax := Finset.le_max' SJ (J + 1) hJ1_mem
    omega
  have hJ_ge12 : 12 ≤ J := by
    have h1 : D2 * 256 < D2 * pentNat (2 * (J + 1)) := by omega
    have h2 : 256 < pentNat (2 * (J + 1)) := Nat.lt_of_mul_lt_mul_left h1
    have h3 := two_mul_pentNat_even (J + 1)
    nlinarith
  let B : ℕ → Finset ℕ := fun j =>
    Finset.Ico (D2 * pentNat (2 * j)) (D2 * pentNat (2 * j + 1))
  let O : Finset ℕ := (Finset.range J).biUnion B
  have hB_disj : Set.PairwiseDisjoint (Finset.range J : Set ℕ) B := by
    intro j₁ _ j₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    simp only [B, Finset.mem_Ico] at hn1 hn2
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have hmono : pentNat (2 * j₁ + 1) < pentNat (2 * j₂) :=
        pentNat_strictMono (by omega)
      have : D2 * pentNat (2 * j₁ + 1) < D2 * pentNat (2 * j₂) :=
        Nat.mul_lt_mul_of_pos_left hmono hD2_pos
      omega
    · have hmono : pentNat (2 * j₂ + 1) < pentNat (2 * j₁) :=
        pentNat_strictMono (by omega)
      have : D2 * pentNat (2 * j₂ + 1) < D2 * pentNat (2 * j₁) :=
        Nat.mul_lt_mul_of_pos_left hmono hD2_pos
      omega
  have hO_card : O.card = D2 * J ^ 2 := by
    dsimp only [O]
    rw [Finset.card_biUnion hB_disj]
    have hB_card : ∀ j ∈ Finset.range J, (B j).card = D2 * (2 * j + 1) := by
      intro j _
      dsimp only [B]
      rw [Nat.card_Ico, pentNat_step_even, mul_add]
      omega
    rw [Finset.sum_congr rfl hB_card, ← Finset.mul_sum, sum_odd_range]
  have hO_sub : ∀ n ∈ O, n ≤ Nx ∧ Odd (pentIdx D2 n).card := by
    intro n hn
    obtain ⟨j, hj, hnB⟩ := Finset.mem_biUnion.mp hn
    have hjJ : j < J := Finset.mem_range.mp hj
    simp only [B, Finset.mem_Ico] at hnB
    have hpent_le : pentNat (2 * j + 1) ≤ pentNat (2 * J) :=
      pentNat_strictMono.monotone (by omega)
    have hnNx : n ≤ Nx := by
      have : D2 * pentNat (2 * j + 1) ≤ D2 * pentNat (2 * J) :=
        Nat.mul_le_mul_left D2 hpent_le
      omega
    have hidx_eq : pentIdx D2 n = Finset.range (2 * j + 1) := by
      ext i
      rw [mem_pentIdx_iff hD2_pos, Finset.mem_range]
      constructor
      · intro hle
        by_contra hge
        push Not at hge
        have hmono : pentNat (2 * j + 1) ≤ pentNat i := pentNat_strictMono.monotone hge
        have : D2 * pentNat (2 * j + 1) ≤ D2 * pentNat i := Nat.mul_le_mul_left D2 hmono
        omega
      · intro hlt
        have hmono : pentNat i ≤ pentNat (2 * j) := pentNat_strictMono.monotone (by omega)
        have : D2 * pentNat i ≤ D2 * pentNat (2 * j) := Nat.mul_le_mul_left D2 hmono
        omega
    exact ⟨hnNx, by rw [hidx_eq, Finset.card_range]; exact ⟨j, rfl⟩⟩
  let Bad := O.filter (fun n => PowerSeries.coeff (8 * n + k) (deltaPS ^ k) ≠ 0)
  let Good := O.filter (fun n => PowerSeries.coeff (8 * n + k) (deltaPS ^ k) = 0)
  have hOGB : Good.card + Bad.card = O.card := by
    dsimp only [Good, Bad]
    exact Finset.card_filter_add_card_filter_not _
  have hBad_le : (Bad.card : ℝ) ≤ x / 8 := by
    let SW : Set ℕ := {m : ℕ | (m : ℝ) ≤ 8 * x + (k : ℝ) ∧
      PowerSeries.coeff m (deltaPS ^ k) ≠ 0}
    have hSW_fin : SW.Finite := by
      refine (Set.finite_Iic ⌊8 * x + (k : ℝ)⌋₊).subset fun m hm => ?_
      exact Nat.le_floor hm.1
    let BadImg := Bad.image (fun n => 8 * n + k)
    have hsub : (BadImg : Set ℕ) ⊆ SW := by
      intro m hm
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hm)
      have hnO : n ∈ O := (Finset.mem_filter.mp hn).1
      have hne : PowerSeries.coeff (8 * n + k) (deltaPS ^ k) ≠ 0 := (Finset.mem_filter.mp hn).2
      have hnNx : n ≤ Nx := (hO_sub n hnO).1
      have hnx : (n : ℝ) ≤ x := le_trans (by exact_mod_cast hnNx) hNx_le
      refine ⟨?_, hne⟩
      push_cast; linarith
    have hinj : Function.Injective (fun n : ℕ => 8 * n + k) := fun a b h => by
      dsimp only at h; omega
    have hcard_eq : Bad.card = BadImg.card := (Finset.card_image_of_injective Bad hinj).symm
    have hle_ncard : BadImg.card ≤ SW.ncard := by
      rw [← Set.ncard_coe_finset BadImg]
      exact Set.ncard_le_ncard hsub hSW_fin
    have hle_real : (Bad.card : ℝ) ≤ (SW.ncard : ℝ) := by
      rw [hcard_eq]; exact_mod_cast hle_ncard
    exact hle_real.trans hsparse
  have hO_gt_half : x / 2 ≤ (O.card : ℝ) := by
    rw [hO_card]
    have h1 : Nx + 1 ≤ D2 * pentNat (2 * (J + 1)) := by omega
    have h2 : (2 : ℕ) * pentNat (2 * (J + 1)) = (J + 1) * (3 * (J + 1) + 1) :=
      two_mul_pentNat_even (J + 1)
    have h3 : pentNat (2 * (J + 1)) ≤ 2 * J ^ 2 := by nlinarith
    have h4 : Nx + 1 ≤ 2 * (D2 * J ^ 2) := by
      calc Nx + 1 ≤ D2 * pentNat (2 * (J + 1)) := h1
        _ ≤ D2 * (2 * J ^ 2) := Nat.mul_le_mul_left D2 h3
        _ = 2 * (D2 * J ^ 2) := by ring
    have h4r : (Nx : ℝ) + 1 ≤ 2 * ((D2 * J ^ 2 : ℕ) : ℝ) := by exact_mod_cast h4
    linarith
  have hGood_ge : 3 * x / 8 ≤ (Good.card : ℝ) := by
    have hOGB_r : (Good.card : ℝ) + (Bad.card : ℝ) = (O.card : ℝ) := by exact_mod_cast hOGB
    linarith
  let Ev : Finset ℕ := (Finset.range (Nx + 1)).filter (fun r => Even (Nat.partitionNumber r))
  have hEv_eq : Ev.card = ({n : ℕ | (n : ℝ) ≤ x ∧ Even (Nat.partitionNumber n)}).ncard := by
    rw [← Set.ncard_coe_finset Ev]
    congr 1
    ext n
    simp only [Ev, Finset.mem_coe, Finset.mem_filter, Finset.mem_range, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hn, hev⟩
      have : (n : ℝ) ≤ (Nx : ℝ) := by exact_mod_cast (show n ≤ Nx by omega)
      exact ⟨this.trans hNx_le, hev⟩
    · rintro ⟨hn, hev⟩
      have : n ≤ Nx := Nat.le_floor hn
      exact ⟨by omega, hev⟩
  have hGood_sub : Good ⊆ (Ev ×ˢ pentIdx D2 Nx).image (fun p => p.1 + D2 * pentNat p.2) := by
    intro n hn
    have hnO : n ∈ O := (Finset.mem_filter.mp hn).1
    have hzero : PowerSeries.coeff (8 * n + k) (deltaPS ^ k) = 0 := (Finset.mem_filter.mp hn).2
    obtain ⟨hnNx, hodd⟩ := hO_sub n hnO
    obtain ⟨i, hi, hev⟩ := exists_even_of_coeff_zero_odd_card hzero hodd
    have hile : D2 * pentNat i ≤ n := (mem_pentIdx_iff hD2_pos).mp hi
    have hiNx : i ∈ pentIdx D2 Nx := (mem_pentIdx_iff hD2_pos).mpr (le_trans hile hnNx)
    set r := n - D2 * pentNat i
    have hrEv : r ∈ Ev := by
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hev⟩
    exact Finset.mem_image.mpr ⟨(r, i), Finset.mem_product.mpr ⟨hrEv, hiNx⟩, by
      dsimp only [r]; omega⟩
  have hGood_le : Good.card ≤ Ev.card * (pentIdx D2 Nx).card := by
    calc Good.card
        ≤ ((Ev ×ˢ pentIdx D2 Nx).image (fun p => p.1 + D2 * pentNat p.2)).card :=
          Finset.card_le_card hGood_sub
      _ ≤ (Ev ×ˢ pentIdx D2 Nx).card := Finset.card_image_le
      _ = Ev.card * (pentIdx D2 Nx).card := Finset.card_product _ _
  have hIdx_le : (pentIdx D2 Nx).card ≤ 2 * J + 2 := by
    have hsub : pentIdx D2 Nx ⊆ Finset.range (2 * J + 2) := by
      intro i hi
      rw [Finset.mem_range]
      have hile : D2 * pentNat i ≤ Nx := (mem_pentIdx_iff hD2_pos).mp hi
      have hlt : D2 * pentNat i < D2 * pentNat (2 * (J + 1)) := lt_of_le_of_lt hile hJ_gt
      have hlt2 : pentNat i < pentNat (2 * (J + 1)) := Nat.lt_of_mul_lt_mul_left hlt
      have hlt3 : i < 2 * (J + 1) := pentNat_strictMono.lt_iff_lt.mp hlt2
      omega
    exact (Finset.card_le_card hsub).trans (by rw [Finset.card_range])
  have h2J2_bound : (D : ℝ) * ((2 * J + 2 : ℕ) : ℝ) ≤ 2 * Real.sqrt x := by
    have hsq_nat : (2 * J + 2) ^ 2 ≤ 5 * J ^ 2 := by nlinarith
    have hpent_ge : 3 * J ^ 2 ≤ 2 * pentNat (2 * J) := by
      have := two_mul_pentNat_even J; nlinarith
    have h3 : 3 * (D2 * J ^ 2) ≤ 2 * Nx := by
      calc 3 * (D2 * J ^ 2) = D2 * (3 * J ^ 2) := by ring
        _ ≤ D2 * (2 * pentNat (2 * J)) := Nat.mul_le_mul_left D2 hpent_ge
        _ = 2 * (D2 * pentNat (2 * J)) := by ring
        _ ≤ 2 * Nx := Nat.mul_le_mul_left 2 hJ_le
    have hsq_real : ((D : ℝ) * ((2 * J + 2 : ℕ) : ℝ)) ^ 2 ≤ (2 * Real.sqrt x) ^ 2 := by
      have h1 : ((2 * J + 2 : ℕ) : ℝ) ^ 2 ≤ 5 * (J : ℝ) ^ 2 := by exact_mod_cast hsq_nat
      have h2 : 3 * ((D2 : ℝ) * (J : ℝ) ^ 2) ≤ 2 * (Nx : ℝ) := by exact_mod_cast h3
      rw [mul_pow, ← hD2_cast, mul_pow, Real.sq_sqrt hx_pos.le]
      nlinarith only [h1, h2, hNx_le, hD2_cast, Nat.cast_nonneg (α := ℝ) D2]
    nlinarith only [hsq_real, Real.sqrt_nonneg x, Nat.cast_nonneg (α := ℝ) D,
      Nat.cast_nonneg (α := ℝ) (2 * J + 2)]
  have hGood_le_r : (Good.card : ℝ) ≤ (Ev.card : ℝ) * ((2 * J + 2 : ℕ) : ℝ) := by
    have hnat : Good.card ≤ Ev.card * (2 * J + 2) := hGood_le.trans (Nat.mul_le_mul_left _ hIdx_le)
    exact_mod_cast hnat
  have hmul : (D : ℝ) * (3 * x / 8) ≤ (Ev.card : ℝ) * (2 * Real.sqrt x) := by
    calc (D : ℝ) * (3 * x / 8)
        ≤ (D : ℝ) * (Good.card : ℝ) := by nlinarith only [hGood_ge, Nat.cast_nonneg (α := ℝ) D]
      _ ≤ (D : ℝ) * ((Ev.card : ℝ) * ((2 * J + 2 : ℕ) : ℝ)) := by
            nlinarith only [hGood_le_r, Nat.cast_nonneg (α := ℝ) D]
      _ = (Ev.card : ℝ) * ((D : ℝ) * ((2 * J + 2 : ℕ) : ℝ)) := by ring
      _ ≤ (Ev.card : ℝ) * (2 * Real.sqrt x) := by
            nlinarith only [h2J2_bound, Nat.cast_nonneg (α := ℝ) Ev.card]
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx_pos
  have hx_eq : x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt hx_pos.le).symm
  rw [← hEv_eq, ← hD_cast]
  nlinarith only [hmul, hsqrt_pos, hx_eq, Nat.cast_nonneg (α := ℝ) D,
    Nat.cast_nonneg (α := ℝ) Ev.card]

end OMA.PartitionParityBellaicheNicolasEvenR2H1

/- ### Section 5: Main theorem -/

theorem OMA.solution : OMA.R_PartitionParity_bellaiche_nicolas_even_R2.H1 := by
  refine Filter.eventually_atTop.mpr ⟨1, fun x _ t ht hD hsparse => ?_⟩
  exact OMA.PartitionParityBellaicheNicolasEvenR2H1.bellaiche_nicolas_conv_bound x t ht hD hsparse


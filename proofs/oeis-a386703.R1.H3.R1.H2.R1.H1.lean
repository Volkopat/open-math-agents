import OMAReductions.R_oeis_a386703_R1_H3_R1_H2_R1

/-!
# Support of the Strict Partition Function Modulo Eight

We prove `OMA.R_oeis_a386703_R1_H3_R1_H2_R1.H1`: if `24 * n + 1` is representable neither as
`u ^ 2 + 24 * v ^ 2` nor as `u ^ 2 + 48 * v ^ 2`, then `8 ∣ q n`, where `q n` is the number of
partitions of `n` into distinct parts.

## Proof outline
1. Establish the finite Jacobi triple-product identity in `(ℤ[q])[z]` for
   `P N = ∏_{k < N} (1 + q^{2k+1} z)(z + q^{2k+1})` via its functional equation
   `(q z + q^{2N}) P_N(q^2 z) = q^{2N} (1 + q^{2N+1} z) P_N(z)` and downward induction from the
   leading coefficient `q^{N^2}`.
2. Specialize at `z = -1` and match coefficients up to degree `n` (with `N = 2n + 1`) to obtain
   Gauss's identity `(pentagonalSeries ℤ) ^ 2 = (pentagonalSeries ℤ).expand 2 * theta4` in `ℤ⟦X⟧`,
   where `theta4 = ∑_{v ∈ ℤ} (-1)^v X^{v^2} = 1 + 2 S(X)`.
3. Combine with `A386Series.expanded_product` (`Q * pentagonalSeries = (pentagonalSeries).expand 2`)
   and cancel the unit `pentagonalSeries ℤ` to obtain `Q * theta4 = pentagonalSeries ℤ`.
4. Reduce modulo `8`: since `S(X)^2 ≡ S(X^2) (mod 2)`, we have `4 S(X)^2 = 4 S(X^2)` in
   `(ZMod 8)⟦X⟧`, so `theta4 * (2 * theta4(X^2) - theta4) = 1` in `(ZMod 8)⟦X⟧`, yielding
   `Q = 2 * pentagonalSeries * theta4(X^2) - pentagonalSeries * theta4` in `(ZMod 8)⟦X⟧`.
5. Every nonzero term of `pentagonalSeries * theta4` (resp. `pentagonalSeries * theta4(X^2)`) at
   degree `n` gives a representation `24 * n + 1 = u^2 + 24 * v^2` (resp. `u^2 + 48 * v^2`).
   Hence when neither representation exists, `(q n : ZMod 8) = 0`, i.e., `8 ∣ q n`.
-/

namespace OMA.StrictPartitionModEight

open Finset PowerSeries PowerSeries.WithPiTopology OMA.S_oeis_a386703
open scoped BigOperators Topology

/- ### Step 1: Finite polynomial identity for Gauss's theta series -/

private abbrev QPoly := Polynomial ℤ
private abbrev ZPoly := Polynomial QPoly

private noncomputable abbrev qVar : QPoly := Polynomial.X
private noncomputable abbrev zVar : ZPoly := Polynomial.X

private noncomputable def P (N : ℕ) : ZPoly :=
  ∏ k ∈ Finset.range N,
    (1 + Polynomial.C (qVar ^ (2 * k + 1)) * zVar) *
      (zVar + Polynomial.C (qVar ^ (2 * k + 1)))

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
      rcases r with _ | r
      · omega
      · rw [Polynomial.coeff_mul_X, ih r (by omega), mul_zero]
    have h2 : (P N * (Polynomial.C (qVar ^ (2 * N + 1)) * zVar ^ 2)).coeff r = 0 := by
      rw [mul_left_comm, Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow']
      split_ifs with hle
      · rw [ih (r - 2) (by omega), mul_zero]
      · simp
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
  have he2 : qVar ^ (2 * N) * qVar ^ (2 * (N + m)) = qVar ^ (2 * N) * qVar ^ (2 * N + 2 * m) := by
    congr 2; omega
  have he3 : qVar ^ (2 * N) * (qVar ^ (2 * m - 1) * qVar ^ (2 * N - 2 * m + 2)) =
      qVar ^ (2 * N) * qVar ^ (2 * N + 1) := by
    rw [← pow_add]; congr 2; omega
  calc qVar ^ (2 * N) * ((P N).coeff (N + m) * (1 - qVar ^ (2 * N + 2 * m)))
      = qVar ^ (2 * N) * (P N).coeff (N + m) -
          (qVar ^ (2 * N) * qVar ^ (2 * N + 2 * m)) * (P N).coeff (N + m) := by ring
    _ = qVar ^ (2 * N) * (P N).coeff (N + m) -
          qVar ^ (2 * N) * (qVar ^ (2 * (N + m)) * (P N).coeff (N + m)) := by rw [← he2]; ring
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

/- ### Step 2: Coefficient matching and Gauss's identity in `ℤ⟦X⟧` -/

private lemma coeff_mul_prod_one_sub_q_pow {ι : Type*} (s : Finset ι) (e : ι → ℕ) (n : ℕ)
    (he : ∀ i ∈ s, n < e i) (g : QPoly) :
    (g * ∏ i ∈ s, (1 - qVar ^ (e i))).coeff n = g.coeff n := by
  classical
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

private lemma P_coeff_mul_even_prod_coeff (n m N k : ℕ) (hm : m ≤ n) (hN : N = 2 * n + 1)
    (hk : k ≤ N) :
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
  by_cases hkn : k ≤ n
  · rw [coeff_mul_prod_one_sub_q_pow (Finset.Ico (N - k) N) (fun j => 2 * (j + 1)) m
      (fun j hj => by simp only [Finset.mem_Ico] at hj; omega)]
    rw [coeff_mul_prod_one_sub_q_pow (Finset.range (N - k)) (fun j => 4 * N - 2 * j) m
      (fun j hj => by simp only [Finset.mem_range] at hj; omega)]
  · have hksq : m < k ^ 2 := by nlinarith
    have hmul0 : ∀ h : QPoly, (qVar ^ (k ^ 2) * h).coeff m = 0 := by
      intro h
      change (Polynomial.X ^ (k ^ 2) * h).coeff m = 0
      rw [Polynomial.coeff_X_pow_mul']
      rw [if_neg (not_le.mpr hksq)]
    rw [mul_assoc, hmul0]
    change 0 = (Polynomial.X ^ (k ^ 2) : QPoly).coeff m
    rw [Polynomial.coeff_X_pow, if_neg (by omega)]

private noncomputable def theta4Coeff (n : ℕ) : ℤ :=
  if n = 0 then 1 else if IsSquare n then 2 * Int.negOnePow n.sqrt else 0

private noncomputable def theta4 : ℤ⟦X⟧ :=
  PowerSeries.mk theta4Coeff

private lemma gauss_finite_coeff (n m : ℕ) (hm : m ≤ n) :
    let N := 2 * n + 1
    ((∏ j ∈ Finset.range N, (1 - qVar ^ (2 * (j + 1)))) *
      (∏ j ∈ Finset.range N, (1 - qVar ^ (2 * j + 1)) ^ 2)).coeff m = theta4Coeff m := by
  intro N
  have heval : (P N).eval (-1 : QPoly) =
      (-1 : QPoly) ^ N * ∏ j ∈ Finset.range N, (1 - qVar ^ (2 * j + 1)) ^ 2 := by
    unfold P
    rw [Polynomial.eval_prod]
    have hfac : ∀ j ∈ Finset.range N,
        Polynomial.eval (-1 : QPoly)
          ((1 + Polynomial.C (qVar ^ (2 * j + 1)) * zVar) *
            (zVar + Polynomial.C (qVar ^ (2 * j + 1)))) =
          (-1 : QPoly) * (1 - qVar ^ (2 * j + 1)) ^ 2 := by
      intro j _
      simp [zVar]
      ring
    rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have hsum_eval : (P N).eval (-1 : QPoly) =
      ∑ r ∈ Finset.range (2 * N + 1), (P N).coeff r * (-1 : QPoly) ^ r := by
    rw [Polynomial.eval_eq_sum_range' (lt_of_le_of_lt (by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      exact fun r hr => P_coeff_of_gt N r hr) (Nat.lt_succ_self (2 * N)))]
  set E : QPoly := ∏ j ∈ Finset.range N, (1 - qVar ^ (2 * (j + 1)))
  have hlhs_eq : E * (∏ j ∈ Finset.range N, (1 - qVar ^ (2 * j + 1)) ^ 2) =
      ∑ r ∈ Finset.range (2 * N + 1),
        (-1 : QPoly) ^ (N + r) * ((P N).coeff r * E) := by
    have hmul : (-1 : QPoly) ^ N * (P N).eval (-1 : QPoly) =
        ∏ j ∈ Finset.range N, (1 - qVar ^ (2 * j + 1)) ^ 2 := by
      rw [heval, ← mul_assoc, ← mul_pow]
      simp
    rw [← hmul, hsum_eval, mul_comm E, mul_assoc, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [pow_add]; ring
  rw [hlhs_eq, Polynomial.finsetSum_coeff]
  have hnegOnePow_nat : ∀ k : ℕ, (-1 : ℤ) ^ k = (Int.negOnePow (k : ℤ) : ℤ) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, Nat.cast_add, Nat.cast_one, Int.negOnePow_add, Int.negOnePow_one,
        Units.val_mul]
      simp
  have hterm : ∀ r ∈ Finset.range (2 * N + 1),
      ((-1 : QPoly) ^ (N + r) * ((P N).coeff r * E)).coeff m =
        (Int.negOnePow (N + r : ℕ) : ℤ) * ((P N).coeff r * E).coeff m := by
    intro r _
    have hneg : (-1 : QPoly) ^ (N + r) = Polynomial.C (Int.negOnePow (N + r : ℕ) : ℤ) := by
      rw [← hnegOnePow_nat (N + r), map_pow, map_neg, map_one]
    rw [hneg, Polynomial.coeff_C_mul]
  rw [Finset.sum_congr rfl hterm]
  -- Split `range (2 * N + 1)` into `r = N`, `r = N + k`, and `r = N - k` (`1 ≤ k ≤ N`)
  have hsplit : Finset.range (2 * N + 1) =
      {N} ∪ ((Finset.Icc 1 N).image (fun k => N + k) ∪ (Finset.Icc 1 N).image (fun k => N - k)) := by
    ext r
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
      Finset.mem_Icc]
    constructor
    · intro hr
      rcases lt_trichotomy r N with hlt | rfl | hgt
      · right; right; exact ⟨N - r, ⟨by omega, by omega⟩, by omega⟩
      · left; rfl
      · right; left; exact ⟨r - N, ⟨by omega, by omega⟩, by omega⟩
    · rintro (rfl | ⟨k, ⟨_, hk⟩, rfl⟩ | ⟨k, ⟨_, hk⟩, rfl⟩) <;> omega
  have hd1 : Disjoint ({N} : Finset ℕ)
      ((Finset.Icc 1 N).image (fun k => N + k) ∪ (Finset.Icc 1 N).image (fun k => N - k)) := by
    rw [Finset.disjoint_singleton_left]
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Icc]
    rintro (⟨k, ⟨hk1, _⟩, hk⟩ | ⟨k, ⟨hk1, _⟩, hk⟩) <;> omega
  have hd2 : Disjoint ((Finset.Icc 1 N).image (fun k => N + k))
      ((Finset.Icc 1 N).image (fun k => N - k)) := by
    rw [Finset.disjoint_left]
    intro r hr1 hr2
    simp only [Finset.mem_image, Finset.mem_Icc] at hr1 hr2
    obtain ⟨k1, ⟨hk1, _⟩, rfl⟩ := hr1
    obtain ⟨k2, ⟨hk2, _⟩, hk2eq⟩ := hr2
    omega
  rw [hsplit, Finset.sum_union hd1, Finset.sum_union hd2, Finset.sum_singleton]
  rw [Finset.sum_image (fun a _ b _ h => by omega),
    Finset.sum_image (fun a ha b hb h => by
      simp only [Finset.mem_coe, Finset.mem_Icc] at ha hb; omega)]
  have h0 : (Int.negOnePow (N + N : ℕ) : ℤ) * ((P N).coeff N * E).coeff m =
      if m = 0 then 1 else 0 := by
    have hE0 := P_coeff_mul_even_prod_coeff n m N 0 hm rfl (Nat.zero_le N)
    simp only [add_zero, zero_pow (by decide : 2 ≠ 0), pow_zero] at hE0
    rw [hE0]
    have heven : Even ((N + N : ℕ) : ℤ) := ⟨N, by push_cast; ring⟩
    rw [Int.negOnePow_even _ heven]
    change (1 : ℤ) * (1 : QPoly).coeff m = _
    rw [one_mul, Polynomial.coeff_one]
  have hpos : ∀ k ∈ Finset.Icc 1 N,
      (Int.negOnePow (N + (N + k) : ℕ) : ℤ) * ((P N).coeff (N + k) * E).coeff m =
        (Int.negOnePow (k : ℤ) : ℤ) * (qVar ^ (k ^ 2)).coeff m := by
    intro k hk
    have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
    rw [P_coeff_mul_even_prod_coeff n m N k hm rfl hkN]
    congr 1
    have hparity : ((N + (N + k) : ℕ) : ℤ) = (k : ℤ) + 2 * (N : ℤ) := by push_cast; ring
    rw [hparity, Int.negOnePow_add, Int.negOnePow_even (2 * (N : ℤ)) ⟨N, by ring⟩, mul_one]
  have hneg : ∀ k ∈ Finset.Icc 1 N,
      (Int.negOnePow (N + (N - k) : ℕ) : ℤ) * ((P N).coeff (N - k) * E).coeff m =
        (Int.negOnePow (k : ℤ) : ℤ) * (qVar ^ (k ^ 2)).coeff m := by
    intro k hk
    have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
    have hsym : (P N).coeff (N - k) = (P N).coeff (N + k) := by
      have heq : N - k = 2 * N - (N + k) := by omega
      rw [heq, P_coeff_symm N (N + k) (by omega)]
    rw [hsym, P_coeff_mul_even_prod_coeff n m N k hm rfl hkN]
    congr 1
    have hparity : ((N + (N - k) : ℕ) : ℤ) + (k : ℤ) = 2 * (N : ℤ) := by
      have : N + (N - k) + k = 2 * N := by omega
      exact_mod_cast this
    have h1 : ((N + (N - k) : ℕ) : ℤ) = (2 * (N : ℤ) - 2 * (k : ℤ)) + (k : ℤ) := by linarith
    rw [h1, Int.negOnePow_add, Int.negOnePow_even _ ⟨(N : ℤ) - k, by ring⟩, one_mul]
  rw [h0, Finset.sum_congr rfl hpos, Finset.sum_congr rfl hneg, ← two_mul]
  have hsum_sq : ∑ k ∈ Finset.Icc 1 N, (Int.negOnePow (k : ℤ) : ℤ) * (qVar ^ (k ^ 2)).coeff m =
      if m ≠ 0 ∧ IsSquare m then (Int.negOnePow (m.sqrt : ℤ) : ℤ) else 0 := by
    have hq : ∀ k : ℕ, (qVar ^ (k ^ 2)).coeff m = if k ^ 2 = m then 1 else 0 := fun k => by
      change (Polynomial.X ^ (k ^ 2) : QPoly).coeff m = _
      rw [Polynomial.coeff_X_pow]
      by_cases h : k ^ 2 = m
      · rw [if_pos h.symm, if_pos h]
      · rw [if_neg (Ne.symm h), if_neg h]
    simp_rw [hq, mul_ite, mul_one, mul_zero]
    split_ifs with hmsq
    · obtain ⟨hm0, a, ha⟩ := hmsq
      have hasq : m = a ^ 2 := by simpa [pow_two] using ha
      have ha_eq : a = m.sqrt := by rw [hasq, Nat.sqrt_eq']
      subst ha_eq
      have hmem : m.sqrt ∈ Finset.Icc 1 N := by
        refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
        · by_contra h0
          have hz : m.sqrt = 0 := by omega
          rw [hz] at hasq; simp at hasq; exact hm0 hasq
        · have : m.sqrt ≤ m := Nat.sqrt_le_self m
          omega
      rw [Finset.sum_eq_single m.sqrt]
      · rw [if_pos hasq.symm]
      · intro b _ hne
        rw [if_neg]
        intro hbq
        exact hne (Nat.pow_left_injective (by decide : 2 ≠ 0) (hbq.trans hasq))
      · intro hnot; exact (hnot hmem).elim
    · refine Finset.sum_eq_zero fun k hk => ?_
      rw [if_neg]
      intro hkq
      apply hmsq
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      exact ⟨by nlinarith, k, by simpa [pow_two] using hkq.symm⟩
  rw [hsum_sq]
  unfold theta4Coeff
  by_cases hm0 : m = 0
  · subst hm0; simp
  · by_cases hsq : IsSquare m
    · simp [hm0, hsq]
    · simp [hm0, hsq]

private lemma coeff_prod_one_sub_X_pow_eq (s : Finset ℕ) (e : ℕ → ℕ) (m : ℕ)
    (he : ∀ i ∈ s, m < e i) (g : ℤ⟦X⟧) :
    (g * ∏ i ∈ s, (1 - (X : ℤ⟦X⟧) ^ (e i))).coeff m = g.coeff m := by
  classical
  induction s using Finset.induction_on generalizing g with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, ← mul_assoc]
    have hrest : ∀ j ∈ s, m < e j := fun j hj => he j (Finset.mem_insert_of_mem hj)
    rw [ih hrest (g * (1 - X ^ e i)), mul_sub, mul_one, map_sub]
    have hgt : (g * (X : ℤ⟦X⟧) ^ e i).coeff m = 0 := by
      rw [mul_comm, PowerSeries.coeff_X_pow_mul']
      rw [if_neg (not_le.mpr (he i (Finset.mem_insert_self i s)))]
    rw [hgt, sub_zero]

private lemma pentagonalSeries_coeff_eq_poly (m M : ℕ) (hM : m < M) :
    (pentagonalSeries ℤ).coeff m =
      (∏ i ∈ Finset.range M, (1 - qVar ^ (i + 1))).coeff m := by
  have hprod := hasProd_one_sub_X_pow ℤ
  have hlim : Filter.Tendsto (fun s : Finset ℕ => (∏ i ∈ s, (1 - (X : ℤ⟦X⟧) ^ (i + 1))).coeff m)
      Filter.atTop (𝓝 ((pentagonalSeries ℤ).coeff m)) :=
    ((PowerSeries.WithPiTopology.continuous_coeff ℤ m).continuousAt.tendsto).comp hprod
  have hconst : Filter.Tendsto (fun s : Finset ℕ => (∏ i ∈ s, (1 - (X : ℤ⟦X⟧) ^ (i + 1))).coeff m)
      Filter.atTop (𝓝 ((∏ i ∈ Finset.range M, (1 - (X : ℤ⟦X⟧) ^ (i + 1))).coeff m)) := by
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [Filter.eventually_ge_atTop (Finset.range M)] with s hs
    have hsplit : s = Finset.range M ∪ (s \ Finset.range M) := (Finset.union_sdiff_of_subset hs).symm
    rw [hsplit, Finset.prod_union disjoint_sdiff_self_right]
    exact coeff_prod_one_sub_X_pow_eq (s \ Finset.range M) (fun i => i + 1) m
      (fun i hi => by
        have hnot : i ∉ Finset.range M := (Finset.mem_sdiff.mp hi).2
        simp only [Finset.mem_range] at hnot; omega) _
  have heq := tendsto_nhds_unique hlim hconst
  rw [heq]
  have hcoe : (∏ i ∈ Finset.range M, (1 - (X : ℤ⟦X⟧) ^ (i + 1))) =
      ((∏ i ∈ Finset.range M, (1 - qVar ^ (i + 1)) : QPoly) : ℤ⟦X⟧) := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [Polynomial.coeToPowerSeries.ringHom_apply, qVar]
  rw [hcoe, Polynomial.coeff_coe]

private lemma pentagonalSeries_expand_two_coeff_eq_poly (m N : ℕ) (hN : m < 2 * N) :
    ((pentagonalSeries ℤ).expand 2 (by decide)).coeff m =
      (∏ j ∈ Finset.range N, (1 - qVar ^ (2 * (j + 1)))).coeff m := by
  have hprod : (∏ j ∈ Finset.range N, (1 - qVar ^ (2 * (j + 1)))) =
      Polynomial.expand ℤ 2 (∏ j ∈ Finset.range N, (1 - qVar ^ (j + 1))) := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [map_sub, map_one, map_pow, qVar, Polynomial.expand_X]
    rw [← pow_mul, mul_comm]
  rw [hprod, Polynomial.coeff_expand (by decide : 0 < 2), PowerSeries.coeff_expand]
  split_ifs with h2
  · exact pentagonalSeries_coeff_eq_poly (m / 2) N (by omega)
  · rfl

private lemma prod_range_two_mul (N : ℕ) :
    ∏ i ∈ Finset.range (2 * N), (1 - qVar ^ (i + 1)) =
      (∏ j ∈ Finset.range N, (1 - qVar ^ (2 * (j + 1)))) *
        (∏ j ∈ Finset.range N, (1 - qVar ^ (2 * j + 1))) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h2 : 2 * (N + 1) = (2 * N + 1) + 1 := by omega
    rw [h2, Finset.prod_range_succ, Finset.prod_range_succ, ih,
      Finset.prod_range_succ, Finset.prod_range_succ]
    have h2n : 2 * N + 1 + 1 = 2 * (N + 1) := by omega
    rw [h2n]
    ring

private lemma gauss_identity :
    (pentagonalSeries ℤ) ^ 2 = (pentagonalSeries ℤ).expand 2 (by decide) * theta4 := by
  ext n
  set N := 2 * n + 1
  rw [pow_two, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  have hleft :
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
          (pentagonalSeries ℤ).coeff ij.1 * (pentagonalSeries ℤ).coeff ij.2 =
      ((∏ i ∈ Finset.range (2 * N), (1 - qVar ^ (i + 1))) ^ 2).coeff n := by
    rw [pow_two, Polynomial.coeff_mul]
    refine Finset.sum_congr rfl fun ij hij => ?_
    have hsum : ij.1 + ij.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    rw [pentagonalSeries_coeff_eq_poly ij.1 (2 * N) (by omega),
      pentagonalSeries_coeff_eq_poly ij.2 (2 * N) (by omega)]
  rw [hleft, prod_range_two_mul N]
  have hrew : ((∏ j ∈ Finset.range N, (1 - qVar ^ (2 * (j + 1)))) *
      (∏ j ∈ Finset.range N, (1 - qVar ^ (2 * j + 1)))) ^ 2 =
      (∏ j ∈ Finset.range N, (1 - qVar ^ (2 * (j + 1)))) *
        ((∏ j ∈ Finset.range N, (1 - qVar ^ (2 * (j + 1)))) *
          (∏ j ∈ Finset.range N, (1 - qVar ^ (2 * j + 1)) ^ 2)) := by
    rw [Finset.prod_pow]; ring
  rw [hrew, Polynomial.coeff_mul]
  refine Finset.sum_congr rfl fun ij hij => ?_
  have hsum : ij.1 + ij.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [pentagonalSeries_expand_two_coeff_eq_poly ij.1 N (by omega),
    gauss_finite_coeff n ij.2 (by omega)]
  simp [theta4]

/- ### Step 3: `Q * theta4 = pentagonalSeries` in `ℤ⟦X⟧` -/

private lemma Q_mul_theta4_eq_pentagonal :
    (PowerSeries.mk fun n => (q n : ℤ)) * theta4 = pentagonalSeries ℤ := by
  have h1 : ((PowerSeries.mk fun n => (q n : ℤ)) * theta4) * pentagonalSeries ℤ =
      pentagonalSeries ℤ * pentagonalSeries ℤ := by
    calc ((PowerSeries.mk fun n => (q n : ℤ)) * theta4) * pentagonalSeries ℤ
        = ((PowerSeries.mk fun n => (q n : ℤ)) * pentagonalSeries ℤ) * theta4 := by ring
      _ = (pentagonalSeries ℤ).expand 2 (by decide) * theta4 := by
          rw [A386Series.expanded_product]
      _ = pentagonalSeries ℤ * pentagonalSeries ℤ := by rw [← pow_two, gauss_identity]
  have hunit : IsUnit (pentagonalSeries ℤ) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have h0 : PowerSeries.constantCoeff (pentagonalSeries ℤ) = 1 := by
      have := PowerSeries.coeff_pentagonalSeries_pentagonal ℤ 0
      simpa [PowerSeries.coeff_zero_eq_constantCoeff, pentagonal_def] using this
    rw [h0]
    exact isUnit_one
  exact hunit.mul_right_cancel h1

/- ### Step 4: Modulo 8 inversion of `theta4` in `(ZMod 8)⟦X⟧` -/

private noncomputable def S8 : (ZMod 8)⟦X⟧ :=
  PowerSeries.mk fun n =>
    if n = 0 then 0 else if IsSquare n then (Int.negOnePow n.sqrt : ZMod 8) else 0

private noncomputable def theta4_8 : (ZMod 8)⟦X⟧ :=
  1 + 2 * S8

private lemma coeff_two_mul {R : Type*} [Semiring R] (f : R⟦X⟧) (n : ℕ) :
    ((2 : R⟦X⟧) * f).coeff n = 2 * f.coeff n := by
  rw [show (2 : R⟦X⟧) = PowerSeries.C (2 : R) from (map_ofNat PowerSeries.C 2).symm,
    PowerSeries.coeff_C_mul]

private lemma map_theta4_eq :
    PowerSeries.map (Int.castRingHom (ZMod 8)) theta4 = theta4_8 := by
  ext n
  simp only [PowerSeries.coeff_map, theta4, theta4_8, S8, theta4Coeff, PowerSeries.coeff_mk,
    map_add, PowerSeries.coeff_one, coeff_two_mul]
  by_cases hn : n = 0
  · subst hn; simp
  · by_cases hsq : IsSquare n
    · simp [hn, hsq]
    · simp [hn, hsq]

private lemma four_mul_S8_sq :
    (4 : (ZMod 8)⟦X⟧) * S8 ^ 2 = (4 : (ZMod 8)⟦X⟧) * S8.expand 2 (by decide) := by
  classical
  ext n
  have h4mul : ∀ f : (ZMod 8)⟦X⟧, ((4 : (ZMod 8)⟦X⟧) * f).coeff n = 4 * f.coeff n := by
    intro f
    have hC : (4 : (ZMod 8)⟦X⟧) = PowerSeries.C (4 : ZMod 8) := (map_ofNat _ _).symm
    rw [hC, PowerSeries.coeff_C_mul]
  rw [h4mul, h4mul, pow_two, PowerSeries.coeff_mul, Finset.mul_sum]
  let A := Finset.HasAntidiagonal.antidiagonal n
  let diag := A.filter (fun x => x.1 = x.2)
  let off := A.filter (fun x => ¬ x.1 = x.2)
  rw [← Finset.sum_filter_add_sum_filter_not A (fun x => x.1 = x.2)]
  have hoff : ∑ x ∈ off, (4 : ZMod 8) * (S8.coeff x.1 * S8.coeff x.2) = 0 := by
    have hsw : ∀ x ∈ off, x.swap ∈ off := by
      intro x hx
      obtain ⟨hA, hne⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr
        ⟨Finset.HasAntidiagonal.mem_antidiagonal.mpr
          (by have := Finset.HasAntidiagonal.mem_antidiagonal.mp hA; simpa [add_comm] using this),
          Ne.symm hne⟩
    refine Finset.sum_involution (fun x _ => x.swap) ?_ ?_ hsw (fun _ _ => rfl)
    · intro x _
      have hcomm : S8.coeff x.2 * S8.coeff x.1 = S8.coeff x.1 * S8.coeff x.2 := mul_comm _ _
      rw [Prod.fst_swap, Prod.snd_swap, hcomm, ← add_mul]
      have h8 : (4 : ZMod 8) + 4 = 0 := by decide
      rw [h8, zero_mul]
    · intro x hx _ h
      exact (Finset.mem_filter.mp hx).2 (congrArg Prod.fst h).symm
  change (∑ x ∈ diag, _) + (∑ x ∈ off, _) = _
  rw [hoff, add_zero, PowerSeries.coeff_expand]
  split_ifs with heven
  · obtain ⟨m, rfl⟩ := heven
    have hdiag : diag = {(m, m)} := by
      ext ⟨a, b⟩
      simp only [diag, A, Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal,
        Finset.mem_singleton, Prod.mk.injEq]
      omega
    rw [hdiag, Finset.sum_singleton]
    have hdiv : 2 * m / 2 = m := by omega
    rw [hdiv]
    have h4sq : ∀ x : ZMod 8, (4 : ZMod 8) * (x * x) = 4 * x := by decide
    exact h4sq (S8.coeff m)
  · have hdiag : diag = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      rintro ⟨a, b⟩ hab
      obtain ⟨hA, heq⟩ := Finset.mem_filter.mp hab
      have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hA
      change a = b at heq
      exact heven ⟨a, by omega⟩
    rw [hdiag, Finset.sum_empty, mul_zero]

private lemma theta4_8_mul_inv :
    theta4_8 * (2 * theta4_8.expand 2 (by decide) - theta4_8) = 1 := by
  have hexp : theta4_8.expand 2 (by decide) = 1 + 2 * S8.expand 2 (by decide) := by
    simp only [theta4_8, map_add, map_one, map_mul, map_ofNat]
  have h8 : (8 : (ZMod 8)⟦X⟧) = 0 := by
    have e : (8 : ZMod 8) = 0 := by decide
    calc (8 : (ZMod 8)⟦X⟧) = PowerSeries.C (8 : ZMod 8) := (map_ofNat _ _).symm
      _ = 0 := by rw [e, map_zero]
  rw [hexp]
  unfold theta4_8
  linear_combination -four_mul_S8_sq + (S8 * S8.expand 2 (by decide)) * h8

private lemma Q8_eq :
    (PowerSeries.mk fun n => (q n : ZMod 8)) =
      2 * (pentagonalSeries (ZMod 8) * theta4_8.expand 2 (by decide)) -
        pentagonalSeries (ZMod 8) * theta4_8 := by
  have hmap := congrArg (PowerSeries.map (Int.castRingHom (ZMod 8))) Q_mul_theta4_eq_pentagonal
  rw [map_mul, map_theta4_eq] at hmap
  have hQmap : PowerSeries.map (Int.castRingHom (ZMod 8)) (PowerSeries.mk fun n => (q n : ℤ)) =
      PowerSeries.mk fun n => (q n : ZMod 8) := by
    ext n; simp
  have hPmap : PowerSeries.map (Int.castRingHom (ZMod 8)) (pentagonalSeries ℤ) =
      pentagonalSeries (ZMod 8) := by
    ext n
    rw [PowerSeries.coeff_map]
    by_cases h : n ∈ Set.range pentagonal
    · obtain ⟨k, rfl⟩ := h
      rw [PowerSeries.coeff_pentagonalSeries_pentagonal,
        PowerSeries.coeff_pentagonalSeries_pentagonal]
      simp
    · rw [PowerSeries.coeff_pentagonalSeries_eq_zero ℤ h,
        PowerSeries.coeff_pentagonalSeries_eq_zero (ZMod 8) h, map_zero]
  rw [hQmap, hPmap] at hmap
  have hmul := congrArg (fun f => f * (2 * theta4_8.expand 2 (by decide) - theta4_8)) hmap
  rw [mul_assoc, theta4_8_mul_inv, mul_one] at hmul
  rw [hmul]
  ring

/- ### Step 5: Support of the two series and conclusion -/

private lemma theta4_8_coeff_ne_zero {m : ℕ} (h : theta4_8.coeff m ≠ 0) : IsSquare m := by
  by_contra hnsq
  apply h
  have hm0 : m ≠ 0 := fun hz => hnsq (hz ▸ ⟨0, rfl⟩)
  simp [theta4_8, S8, hm0, hnsq, PowerSeries.coeff_one, coeff_two_mul]

private lemma coeff_pent_theta4_eq_zero {n : ℕ}
    (h24 : ¬ ∃ u v : ℕ, 24 * n + 1 = u ^ 2 + 24 * v ^ 2) :
    (pentagonalSeries (ZMod 8) * theta4_8).coeff n = 0 := by
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun ij hij => ?_
  have hsum : ij.1 + ij.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  by_cases hp : ij.1 ∈ Set.range pentagonal
  · by_cases ht : theta4_8.coeff ij.2 = 0
    · rw [ht, mul_zero]
    · exfalso
      obtain ⟨v, hv⟩ := theta4_8_coeff_ne_zero ht
      obtain ⟨u, hu⟩ := (OMA.R_oeis_a386703_R1.pentagonal_iff_square ij.1).mp hp
      apply h24
      exact ⟨u, v, by nlinarith only [hsum, hv, hu]⟩
  · rw [PowerSeries.coeff_pentagonalSeries_eq_zero (ZMod 8) hp, zero_mul]

private lemma coeff_pent_theta4_expand_eq_zero {n : ℕ}
    (h48 : ¬ ∃ u v : ℕ, 24 * n + 1 = u ^ 2 + 48 * v ^ 2) :
    (pentagonalSeries (ZMod 8) * theta4_8.expand 2 (by decide)).coeff n = 0 := by
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun ij hij => ?_
  have hsum : ij.1 + ij.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  by_cases hp : ij.1 ∈ Set.range pentagonal
  · rw [PowerSeries.coeff_expand]
    split_ifs with h2
    · by_cases ht : theta4_8.coeff (ij.2 / 2) = 0
      · rw [ht, mul_zero]
      · exfalso
        obtain ⟨v, hv⟩ := theta4_8_coeff_ne_zero ht
        obtain ⟨u, hu⟩ := (OMA.R_oeis_a386703_R1.pentagonal_iff_square ij.1).mp hp
        obtain ⟨t, ht2⟩ := h2
        have hj2 : ij.2 = 2 * (v * v) := by
          have : ij.2 / 2 = t := by omega
          rw [this] at hv
          omega
        apply h48
        exact ⟨u, v, by nlinarith only [hsum, hj2, hu]⟩
    · rw [mul_zero]
  · rw [PowerSeries.coeff_pentagonalSeries_eq_zero (ZMod 8) hp, zero_mul]

end OMA.StrictPartitionModEight

theorem OMA.solution : OMA.R_oeis_a386703_R1_H3_R1_H2_R1.H1 := by
  intro n h24 h48
  have h := congrArg (PowerSeries.coeff n) OMA.StrictPartitionModEight.Q8_eq
  rw [PowerSeries.coeff_mk, map_sub, OMA.StrictPartitionModEight.coeff_two_mul,
    OMA.StrictPartitionModEight.coeff_pent_theta4_expand_eq_zero h48,
    OMA.StrictPartitionModEight.coeff_pent_theta4_eq_zero h24] at h
  simp only [mul_zero, sub_zero] at h
  exact (ZMod.natCast_eq_zero_iff (OMA.S_oeis_a386703.q n) 8).mp h

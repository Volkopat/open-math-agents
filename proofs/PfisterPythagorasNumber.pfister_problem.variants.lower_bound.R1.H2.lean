import OMAReductions.R_PfisterPythagorasNumber_pfister_problem_variants_lower_bound_R1
import Mathlib

/-!
# Cassels (1964) 实有理函数域添变量平方和下界定理的精简形式化证明
-/

open scoped BigOperators Polynomial
open Polynomial Finset

section

-- 形式实性：有限平方和为零蕴涵各项皆为零
private def FormReal (R : Type*) [CommRing R] : Prop :=
  ∀ (n : ℕ) (g : Fin n → R), ∑ i, g i * g i = 0 → ∀ i, g i = 0

private lemma formReal_real : FormReal ℝ := fun _ g h i =>
  mul_self_eq_zero.mp ((sum_eq_zero_iff_of_nonneg fun j _ => mul_self_nonneg (g j)).mp h i (mem_univ i))

private lemma formReal_equiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (hR : FormReal R) :
    FormReal S := fun n g h i => by
  have h' : ∑ j, e.symm (g j) * e.symm (g j) = 0 := e.injective (by simp [map_sum, map_mul, h])
  simpa using congrArg e (hR n _ h' i)

private lemma coeff_sq_2d {R : Type*} [CommRing R] (p : R[X]) (d : ℕ) (hd : p.natDegree ≤ d) :
    (p * p).coeff (d + d) = p.coeff d * p.coeff d := by
  rw [coeff_mul]
  refine sum_eq_single (d, d) (fun ⟨u, v⟩ huv hne => ?_) (fun h => by simp at h)
  have huv' : u + v = d + d := by simpa using huv
  have hlt : d < u ∨ d < v := by
    by_contra h
    exact hne (by ext <;> omega)
  rcases hlt with hu | hv
  · rw [coeff_eq_zero_of_natDegree_lt (hd.trans_lt hu), zero_mul]
  · rw [coeff_eq_zero_of_natDegree_lt (hd.trans_lt hv), mul_zero]

private lemma formReal_poly {R : Type*} [CommRing R] (hR : FormReal R) : FormReal R[X] := by
  intro n g hsum i₀
  by_contra hi₀
  let fn : Fin n → ℕ := fun j => (g j).natDegree
  let d : ℕ := univ.sup fn
  have hle : ∀ j, (g j).natDegree ≤ d := fun j => le_sup (f := fn) (mem_univ j)
  have h0 : ∀ j, (g j).coeff d = 0 := hR n (fun j => (g j).coeff d) <| by
    have h1 := congrArg (fun p : R[X] => p.coeff (d + d)) hsum
    simp only [finsetSum_coeff, coeff_zero] at h1
    exact (sum_congr rfl fun j _ => coeff_sq_2d (g j) d (hle j)).symm.trans h1
  obtain ⟨j₁, _, hj₁⟩ := exists_mem_eq_sup univ ⟨i₀, mem_univ i₀⟩ fn
  change d = (g j₁).natDegree at hj₁
  by_cases hd0 : d = 0
  · have hdeg0 : (g i₀).natDegree = 0 := Nat.eq_zero_of_le_zero (hd0 ▸ hle i₀)
    have hc0 : (g i₀).coeff 0 = 0 := hd0 ▸ h0 i₀
    rw [eq_C_of_natDegree_eq_zero hdeg0, hc0, map_zero] at hi₀
    exact hi₀ rfl
  · have hpos : 0 < (g j₁).natDegree := by omega
    have hnz : g j₁ ≠ 0 := fun h => by simp [h] at hpos
    have hlead : (g j₁).coeff d ≠ 0 := by rw [hj₁]; exact leadingCoeff_ne_zero.mpr hnz
    exact hlead (h0 j₁)

private lemma formReal_mv : ∀ k : ℕ, FormReal (MvPolynomial (Fin k) ℝ)
  | 0 => formReal_equiv (MvPolynomial.isEmptyRingEquiv ℝ (Fin 0)).symm formReal_real
  | k + 1 => formReal_equiv (MvPolynomial.finSuccEquiv ℝ k).symm (formReal_poly (formReal_mv k))

-- 分式域有限族通分消去公分母引理
private lemma clear_denom (A K : Type*) [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] {n : ℕ} (g : Fin n → K) :
    ∃ (D : A) (B : Fin n → A), D ≠ 0 ∧ (∀ i, B i = 0 → g i = 0) ∧
      algebraMap A K (∑ i, B i * B i) =
        (∑ i, g i * g i) * (algebraMap A K D * algebraMap A K D) := by
  classical
  choose z hz using fun j => IsLocalization.surj (nonZeroDivisors A) (g j)
  let s : Fin n → nonZeroDivisors A := fun j => (z j).2
  let D : A := ∏ j, (s j : A)
  let R : Fin n → A := fun j => ∏ l ∈ univ.erase j, (s l : A)
  have hs : ∀ j, (s j : A) ≠ 0 := fun j => nonZeroDivisors.ne_zero (s j).2
  have hR : ∀ j, R j ≠ 0 := fun j => prod_ne_zero_iff.mpr fun l _ => hs l
  have hmul : ∀ j, g j * algebraMap A K D = algebraMap A K ((z j).1 * R j) := fun j => by
    dsimp only [D]
    rw [← mul_prod_erase univ (fun l => (s l : A)) (mem_univ j), map_mul, ← mul_assoc]
    change (g j * algebraMap A K (z j).2) * _ = _
    rw [hz j, ← map_mul]
  refine ⟨D, fun j => (z j).1 * R j, prod_ne_zero_iff.mpr fun j _ => hs j, fun i hBi => ?_, ?_⟩
  · have ha0 : (z i).1 = 0 := (mul_eq_zero.mp hBi).resolve_right (hR i)
    have hgi : g i * algebraMap A K (s i : A) = 0 := by
      change g i * algebraMap A K (z i).2 = 0
      rw [hz i, ha0, map_zero]
    have hsiK : algebraMap A K (s i : A) ≠ 0 :=
      fun h => hs i (IsFractionRing.injective A K (h.trans (map_zero _).symm))
    exact (mul_eq_zero.mp hgi).resolve_right hsiK
  · rw [map_sum, sum_mul]
    refine sum_congr rfl fun j _ => ?_
    rw [map_mul, ← hmul j]
    ring

private lemma formReal_frac (A K : Type*) [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (hA : FormReal A) : FormReal K := fun n g hsum i => by
  obtain ⟨_, B, _, hB0, hK⟩ := clear_denom A K g
  rw [hsum, zero_mul, ← map_zero (algebraMap A K)] at hK
  exact hB0 i (hA n B (IsFractionRing.injective A K hK) i)

private lemma two_ne_zero_of_formReal {F : Type*} [Field F] (hF : FormReal F) : (2 : F) ≠ 0 :=
  fun h2 => one_ne_zero <| hF 2 (fun _ => 1) (by rw [Fin.sum_univ_two, mul_one, one_add_one_eq_two, h2]) 0

-- Cassels 反射降次恒等式
private lemma refl_id {R : Type*} [CommRing R] {n : ℕ} (P D : R[X]) (A Q : Fin n → R[X])
    (hPD : ∑ i, A i * A i = P * (D * D)) :
    let B := fun i => A i - D * Q i
    let N := ∑ i, B i * B i
    let M := P * D - ∑ i, A i * Q i
    let D' := P * D - 2 * (∑ i, A i * Q i) + D * (∑ i, Q i * Q i)
    let A' := fun j => (P - ∑ i, Q i * Q i) * A j - 2 * M * Q j
    D * D' = N ∧ D ^ 4 * (∑ j, A' j * A' j) = D ^ 4 * (P * (D' * D')) := by
  intro B N M D' A'
  have hDD' : D * D' = N := by
    calc D * D' = (∑ i, A i * A i) - 2 * D * (∑ i, A i * Q i) + D * D * (∑ i, Q i * Q i) := by
          rw [hPD]; dsimp [D']; ring
      _ = ∑ i, (A i * A i - 2 * D * (A i * Q i) + D * D * (Q i * Q i)) := by
          simp only [mul_sum, sum_add_distrib, sum_sub_distrib]
      _ = N := sum_congr rfl fun i _ => by dsimp [B]; ring
  refine ⟨hDD', ?_⟩
  let AB := ∑ i, A i * B i
  have hAB : AB = D * M := by
    calc AB = ∑ i, (A i * A i - D * (A i * Q i)) := sum_congr rfl fun i _ => by dsimp [B]; ring
      _ = P * (D * D) - D * (∑ i, A i * Q i) := by rw [sum_sub_distrib, mul_sum, hPD]
      _ = D * M := by dsimp [M]; ring
  have hDA' : ∀ j, D * D * A' j = 2 * AB * B j - N * A j := fun j => by
    have hDQ : D * Q j = A j - B j := by dsimp [B]; ring
    calc D * D * A' j = D * (D * P - D * (∑ i, Q i * Q i)) * A j - 2 * (D * M) * (D * Q j) := by
          dsimp [A']; ring
      _ = (D * (D * P - D * (∑ i, Q i * Q i)) - 2 * AB) * A j + 2 * AB * B j := by
          rw [← hAB, hDQ]; ring
      _ = (- (D * D')) * A j + 2 * AB * B j := by rw [hAB]; dsimp [M, D']; ring
      _ = 2 * AB * B j - N * A j := by rw [hDD']; ring
  calc D ^ 4 * (∑ j, A' j * A' j) = ∑ j, (D * D * A' j) * (D * D * A' j) := by
        rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
    _ = ∑ j, (4 * AB * AB * (B j * B j) - 4 * AB * N * (A j * B j) + N * N * (A j * A j)) :=
        sum_congr rfl fun j _ => by rw [hDA' j]; ring
    _ = 4 * AB * AB * N - 4 * AB * N * AB + N * N * (∑ j, A j * A j) := by
        simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum]; rfl
    _ = D ^ 4 * (P * (D' * D')) := by rw [hPD, ← hDD']; ring

-- Cassels 降分母强归纳引理
private lemma poly_descent {F : Type*} [Field F] (hF : FormReal F) {n : ℕ} (P : F[X]) :
    ∀ (deg : ℕ) (D : F[X]), D ≠ 0 → D.natDegree = deg →
      (∃ A : Fin n → F[X], ∑ i, A i * A i = P * (D * D)) →
      ∃ f : Fin n → F[X], ∑ i, f i * f i = P := by
  intro deg
  induction deg using Nat.strong_induction_on with
  | h deg ih =>
    intro D hD hdeg ⟨A, hA⟩
    by_cases hdeg0 : deg = 0
    · have hD0 : D.natDegree = 0 := hdeg.trans hdeg0
      have hc0 : D.coeff 0 ≠ 0 := fun hc => hD ((eq_C_of_natDegree_eq_zero hD0).trans (by simp [hc]))
      refine ⟨fun i => C (D.coeff 0)⁻¹ * A i, ?_⟩
      have hDC : D = C (D.coeff 0) := eq_C_of_natDegree_eq_zero hD0
      have hu : C (D.coeff 0)⁻¹ * C (D.coeff 0) = (1 : F[X]) := by
        rw [← map_mul, inv_mul_cancel₀ hc0, map_one]
      calc ∑ i, (C (D.coeff 0)⁻¹ * A i) * (C (D.coeff 0)⁻¹ * A i)
          = (C (D.coeff 0)⁻¹ * C (D.coeff 0)⁻¹) * (P * (C (D.coeff 0) * C (D.coeff 0))) := by
            rw [← hDC, ← hA, mul_sum]; exact sum_congr rfl fun _ _ => by ring
        _ = (C (D.coeff 0)⁻¹ * C (D.coeff 0)) * (C (D.coeff 0)⁻¹ * C (D.coeff 0)) * P := by ring
        _ = P := by rw [hu, one_mul, one_mul]
    · let lc := D.leadingCoeff
      have hlc : lc ≠ 0 := leadingCoeff_ne_zero.mpr hD
      let Dm : F[X] := C lc⁻¹ * D
      have hmon : Dm.Monic := by rw [Monic, leadingCoeff_mul, leadingCoeff_C, inv_mul_cancel₀ hlc]
      have hDm_nz : Dm ≠ 0 := hmon.ne_zero
      have hDm_deg : Dm.natDegree = deg := by rw [natDegree_C_mul (inv_ne_zero hlc), hdeg]
      have hDm1 : Dm ≠ 1 := fun h1 => hdeg0 (by rw [← hDm_deg, h1, natDegree_one])
      let Am : Fin n → F[X] := fun i => C lc⁻¹ * A i
      have hAm : ∑ i, Am i * Am i = P * (Dm * Dm) := by
        calc ∑ i, (C lc⁻¹ * A i) * (C lc⁻¹ * A i)
            = (C lc⁻¹ * C lc⁻¹) * (P * (D * D)) := by
              rw [← hA, mul_sum]; exact sum_congr rfl fun _ _ => by ring
          _ = P * (Dm * Dm) := by dsimp [Dm]; ring
      let Q : Fin n → F[X] := fun i => Am i /ₘ Dm
      let B : Fin n → F[X] := fun i => Am i - Dm * Q i
      by_cases hallB : ∀ i, B i = 0
      · refine ⟨Q, mul_left_cancel₀ (pow_ne_zero 2 hDm_nz) ?_⟩
        calc Dm ^ 2 * (∑ i, Q i * Q i) = ∑ i, Am i * Am i := by
              rw [mul_sum]
              exact sum_congr rfl fun i _ => by rw [sub_eq_zero.mp (hallB i)]; ring
          _ = Dm ^ 2 * P := by rw [hAm]; ring
      · simp only [not_forall] at hallB
        obtain ⟨i₀, hi₀⟩ := hallB
        let N : F[X] := ∑ i, B i * B i
        have hN_nz : N ≠ 0 := fun hN => hi₀ (formReal_poly hF n B hN i₀)
        have hN_deg : N.natDegree ≤ 2 * (deg - 1) :=
          natDegree_sum_le_of_forall_le univ _ fun i _ => by
            by_cases hBi : B i = 0
            · simp [hBi]
            · have hmod : B i = Am i %ₘ Dm := by
                have hd := modByMonic_add_div (Am i) Dm; dsimp [B, Q]; linear_combination -hd
              have hlt : (B i).natDegree < deg := by
                rw [← hDm_deg, hmod]; exact natDegree_modByMonic_lt (Am i) hmon hDm1
              exact natDegree_mul_le.trans (by omega)
        let M : F[X] := P * Dm - ∑ i, Am i * Q i
        let D' : F[X] := P * Dm - 2 * (∑ i, Am i * Q i) + Dm * (∑ i, Q i * Q i)
        let A' : Fin n → F[X] := fun j => (P - ∑ i, Q i * Q i) * Am j - 2 * M * Q j
        obtain ⟨hDD', hA'sq⟩ := refl_id P Dm Am Q hAm
        change Dm * D' = N at hDD'
        change Dm ^ 4 * (∑ j, A' j * A' j) = Dm ^ 4 * (P * (D' * D')) at hA'sq
        have hD'_nz : D' ≠ 0 := fun h0 => hN_nz (by rw [← hDD', h0, mul_zero])
        have hadd : Dm.natDegree + D'.natDegree = N.natDegree := by
          rw [← hDD', natDegree_mul hDm_nz hD'_nz]
        exact ih D'.natDegree (by omega) D' hD'_nz rfl
          ⟨A', mul_left_cancel₀ (pow_ne_zero 4 hDm_nz) hA'sq⟩

private lemma lin_sq {R : Type*} [CommRing R] (a b : R) :
    ((C a * X + C b) * (C a * X + C b)).coeff 2 = a * a ∧
    ((C a * X + C b) * (C a * X + C b)).coeff 1 = 2 * (a * b) ∧
    ((C a * X + C b) * (C a * X + C b)).coeff 0 = b * b := by
  have h : (C a * X + C b) * (C a * X + C b) =
      C (a * a) * X ^ 2 + C (2 * (a * b)) * X ^ 1 + C (b * b) * X ^ 0 := by
    simp only [map_mul, map_ofNat, pow_zero, pow_one]; ring
  rw [h]
  refine ⟨?_, ?_, ?_⟩ <;> simp only [coeff_add, coeff_C_mul_X_pow] <;> simp

-- Householder 正交反射消去一个平方项
private lemma elim_sq {F : Type*} [Field F] (hF : FormReal F) (m : ℕ) (c : F)
    (f : Fin (m + 1) → F[X]) (hf : ∑ j, f j * f j = C c + X ^ 2) : IsSumSqOfLength m c := by
  have hdeg1 : ∀ j, (f j).natDegree ≤ 1 := by
    by_contra hnot
    simp only [not_forall, not_le] at hnot
    obtain ⟨j₀, hj₀⟩ := hnot
    let fn : Fin (m + 1) → ℕ := fun j => (f j).natDegree
    let d : ℕ := univ.sup fn
    have hd2 : 2 ≤ d := (Nat.succ_le_of_lt hj₀).trans (le_sup (f := fn) (mem_univ j₀))
    have hle : ∀ j, (f j).natDegree ≤ d := fun j => le_sup (f := fn) (mem_univ j)
    have hsum0 : ∑ j, (f j).coeff d * (f j).coeff d = 0 := by
      have h1 := congrArg (fun p : F[X] => p.coeff (d + d)) hf
      rw [finsetSum_coeff, coeff_add, coeff_C, if_neg (by omega),
        coeff_X_pow, if_neg (by omega), add_zero] at h1
      exact (sum_congr rfl fun j _ => coeff_sq_2d (f j) d (hle j)).symm.trans h1
    have hall0 := hF (m + 1) (fun j => (f j).coeff d) hsum0
    obtain ⟨j₁, _, hj₁⟩ := exists_mem_eq_sup univ ⟨0, mem_univ 0⟩ fn
    change d = (f j₁).natDegree at hj₁
    have hpos : 0 < (f j₁).natDegree := by omega
    have hlead : (f j₁).coeff d ≠ 0 := by
      rw [hj₁]
      exact leadingCoeff_ne_zero.mpr fun h => by simp [h] at hpos
    exact hlead (hall0 j₁)
  let a : Fin (m + 1) → F := fun j => (f j).coeff 1
  let b : Fin (m + 1) → F := fun j => (f j).coeff 0
  have hlin : ∀ j, f j = C (a j) * X + C (b j) := fun j => eq_X_add_C_of_natDegree_le_one (hdeg1 j)
  have ha_sq : ∑ j, a j * a j = 1 := by
    have h2 := congrArg (fun p : F[X] => p.coeff 2) hf
    rw [finsetSum_coeff, coeff_add, coeff_C, if_neg (by decide), zero_add,
      coeff_X_pow, if_pos rfl] at h2
    exact (sum_congr rfl fun j _ => by rw [hlin j, (lin_sq (a j) (b j)).1]).symm.trans h2
  have hab : ∑ j, a j * b j = 0 := by
    have h1 := congrArg (fun p : F[X] => p.coeff 1) hf
    rw [finsetSum_coeff, coeff_add, coeff_C, if_neg (by decide), zero_add,
      coeff_X_pow, if_neg (by decide)] at h1
    have h2ab : 2 * ∑ j, a j * b j = 0 := by
      rw [mul_sum, ← h1]
      exact sum_congr rfl fun j _ => by rw [hlin j, (lin_sq (a j) (b j)).2.1]
    exact (mul_eq_zero.mp h2ab).resolve_left (two_ne_zero_of_formReal hF)
  have hb_sq : ∑ j, b j * b j = c := by
    have h0 := congrArg (fun p : F[X] => p.coeff 0) hf
    rw [finsetSum_coeff, coeff_add, coeff_C, if_pos rfl, coeff_X_pow,
      if_neg (by decide), add_zero] at h0
    exact (sum_congr rfl fun j _ => by rw [hlin j, (lin_sq (a j) (b j)).2.2]).symm.trans h0
  by_cases ha0 : a 0 = 1
  · have hai0 : ∀ i : Fin m, a i.succ = 0 := hF m (fun i => a i.succ) <| by
      rw [Fin.sum_univ_succ, ha0, mul_one] at ha_sq; linear_combination ha_sq
    have hb0 : b 0 = 0 := by
      rw [Fin.sum_univ_succ, ha0, one_mul,
        sum_eq_zero fun i _ => by rw [hai0 i, zero_mul], add_zero] at hab
      exact hab
    exact ⟨fun i => b i.succ, by rw [← hb_sq, Fin.sum_univ_succ, hb0, mul_zero, zero_add]⟩
  · have h1a : 1 - a 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm ha0)
    let u : Fin (m + 1) → F := Fin.cons (a 0 - 1) (fun i => a i.succ)
    let t : F := b 0 / (1 - a 0)
    let b' : Fin (m + 1) → F := fun j => b j + t * u j
    have hb'0 : b' 0 = 0 := by
      simp only [b', t, u, Fin.cons_zero]
      have hd : b 0 / (1 - a 0) * (a 0 - 1) = -b 0 := by field_simp [h1a]; ring
      linear_combination hd
    have hu_sq : ∑ j, u j * u j = 2 * (1 - a 0) := by
      have hs := Fin.sum_univ_succ (fun j => a j * a j); rw [ha_sq] at hs
      rw [Fin.sum_univ_succ]; simp only [u, Fin.cons_zero, Fin.cons_succ]
      linear_combination -hs
    have hub : ∑ j, u j * b j = -b 0 := by
      have hs := Fin.sum_univ_succ (fun j => a j * b j); rw [hab] at hs
      rw [Fin.sum_univ_succ]; simp only [u, Fin.cons_zero, Fin.cons_succ]
      linear_combination -hs
    have hb'_sq : ∑ j, b' j * b' j = c := by
      have hexp : ∀ j, b' j * b' j = b j * b j + 2 * t * (u j * b j) + t * t * (u j * u j) :=
        fun j => by dsimp [b']; ring
      calc ∑ j, b' j * b' j
          = (∑ j, b j * b j) + 2 * t * (∑ j, u j * b j) + t * t * (∑ j, u j * u j) := by
            simp only [hexp, sum_add_distrib, ← mul_sum]
        _ = c := by rw [hb_sq, hub, hu_sq]; dsimp [t]; field_simp [h1a]; ring
    exact ⟨fun i => b' i.succ, by rw [← hb'_sq, Fin.sum_univ_succ, hb'0, mul_zero, zero_add]⟩

private def swapLast (k : ℕ) : Fin (k + 1) ≃ Fin (k + 1) where
  toFun := Fin.lastCases 0 Fin.succ
  invFun := Fin.cases (Fin.last k) Fin.castSucc
  left_inv := Fin.lastCases (by simp) (fun _ => by simp)
  right_inv := Fin.cases (by simp) (fun _ => by simp)

private lemma finSucc_rename_succ (k : ℕ) (q : MvPolynomial (Fin k) ℝ) :
    (MvPolynomial.finSuccEquiv ℝ k) (MvPolynomial.rename Fin.succ q) = C q := by
  induction q using MvPolynomial.induction_on with
  | C _ => simp [MvPolynomial.finSuccEquiv_apply]
  | add _ _ hp hr => simp [map_add, hp, hr]
  | mul_X _ _ hp => simp [map_mul, hp, MvPolynomial.rename_X, MvPolynomial.finSuccEquiv_X_succ]

end

-- 主定理：完成 Cassels (1964) 添变量平方和下界步骤证明
theorem OMA.solution :
    OMA.R_PfisterPythagorasNumber_pfister_problem_variants_lower_bound_R1.H2 := by
  intro k m f hnot ⟨g1, hg1⟩
  apply hnot
  let Rk := MvPolynomial (Fin k) ℝ
  let F := MvRatFunc (Fin k) ℝ
  let Rk1 := MvPolynomial (Fin (k + 1)) ℝ
  let F1 := MvRatFunc (Fin (k + 1)) ℝ
  have hF : FormReal F := formReal_frac Rk F (formReal_mv k)
  let e1 : Rk1 ≃+* Rk[X] :=
    (MvPolynomial.renameEquiv ℝ (swapLast k)).trans (MvPolynomial.finSuccEquiv ℝ k)
  let toFX : Rk1 →+* F[X] := (mapRingHom (algebraMap Rk F)).comp e1.toRingHom
  have hinj : Function.Injective ((algebraMap F[X] (RatFunc F)).comp toFX) :=
    (IsFractionRing.injective F[X] (RatFunc F)).comp
      ((Polynomial.map_injective _ (IsFractionRing.injective Rk F)).comp e1.injective)
  let Ψ : F1 →+* RatFunc F := IsFractionRing.lift hinj
  have hCS : toFX (MvPolynomial.rename Fin.castSucc f) = C (algebraMap Rk F f) := by
    have he1 : e1 (MvPolynomial.rename Fin.castSucc f) = C f := by
      change (MvPolynomial.finSuccEquiv ℝ k) ((MvPolynomial.renameEquiv ℝ (swapLast k)) _) = C f
      rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_rename,
        show swapLast k ∘ Fin.castSucc = Fin.succ by ext; simp [swapLast], finSucc_rename_succ]
    change Polynomial.map (algebraMap Rk F) (e1 (MvPolynomial.rename Fin.castSucc f)) = _
    rw [he1, map_C]
  have hL : toFX (MvPolynomial.X (Fin.last k)) = X := by
    have he1 : e1 (MvPolynomial.X (Fin.last k)) = X := by
      change (MvPolynomial.finSuccEquiv ℝ k) ((MvPolynomial.renameEquiv ℝ (swapLast k)) _) = X
      rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
        show swapLast k (Fin.last k) = 0 by simp [swapLast], MvPolynomial.finSuccEquiv_X_zero]
    change Polynomial.map (algebraMap Rk F) (e1 (MvPolynomial.X (Fin.last k))) = X
    rw [he1, map_X]
  let c : F := algebraMap Rk F f
  let P : F[X] := C c + X ^ 2
  have hΨ : Ψ (algebraMap Rk1 F1
      (MvPolynomial.rename Fin.castSucc f + MvPolynomial.X (Fin.last k) ^ 2)) =
      algebraMap F[X] (RatFunc F) P := by
    rw [IsFractionRing.lift_algebraMap]
    change algebraMap F[X] (RatFunc F) (toFX _) = _
    rw [map_add, map_pow, hCS, hL]
  let g : Fin (m + 1) → RatFunc F := fun j => Ψ (g1 j)
  have hg : ∑ j, g j * g j = algebraMap F[X] (RatFunc F) P := by
    rw [← hΨ, hg1, map_sum]
    exact sum_congr rfl fun j _ => (map_mul Ψ (g1 j) (g1 j)).symm
  obtain ⟨D, B, hD, _, hK⟩ := clear_denom F[X] (RatFunc F) g
  rw [hg, ← map_mul, ← map_mul] at hK
  obtain ⟨pf, hpf⟩ := poly_descent hF P D.natDegree D hD rfl
    ⟨B, IsFractionRing.injective F[X] (RatFunc F) hK⟩
  exact elim_sq hF m c pf hpf

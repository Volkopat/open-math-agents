import OMAStatements.S_mo_237342
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Variance of the median of uniform multinomial counts

For a fixed server, centering the contribution of each job gives a discrete
integration-by-parts identity. Applied to a clipped ramp, it bounds the chance
that this server has a load in a short interval. Any median is one of the
server loads, so the union bound applies even though the loads are dependent.
-/

namespace MedianServerLoad

open OMA.S_mo_237342 Finset
open scoped BigOperators

noncomputable abbrev p (q : ℕ) : ℝ := (q : ℝ)⁻¹
noncomputable abbrev v (q : ℕ) : ℝ := p q * (1 - p q)

lemma avgChoice {q : ℕ} [NeZero q] (i : Fin q) (a b : ℝ) :
    (𝔼 x : Fin q, if x = i then a else b) = p q * a + (1 - p q) * b := by
  calc
    _ = 𝔼 x : Fin q, ((if x = i then a - b else 0) + b) := by
      apply expect_congr rfl
      intro x _
      split_ifs <;> ring
    _ = _ := by
      rw [expect_add_distrib, Fintype.expect_const, Fintype.expect_ite_eq']
      simp [NNRat.smul_def, p]
      ring

lemma avgInsert {q n : ℕ} (j : Fin (n + 1)) (F : (Fin (n + 1) → Fin q) → ℝ) :
    (𝔼 w, F w) = 𝔼 u : Fin n → Fin q, 𝔼 x : Fin q, F (j.insertNth x u) := by
  let e := Fin.insertNthEquiv (fun _ : Fin (n + 1) ↦ Fin q) j
  calc
    _ = 𝔼 z : Fin q × (Fin n → Fin q), F (e z) := (Fintype.expect_equiv e _ F (fun _ ↦ rfl)).symm
    _ = 𝔼 x : Fin q, 𝔼 u : Fin n → Fin q, F (j.insertNth x u) := by
      rw [← Finset.expect_product']
      simp [e, Fin.insertNthEquiv]
    _ = _ := expect_comm _ _ _

lemma loadInsert {q n : ℕ} (j : Fin (n + 1)) (x i : Fin q) (u : Fin n → Fin q) :
    load (j.insertNth x u) i = (if x = i then 1 else 0) + load u i := by
  unfold load
  rw [Fin.sum_univ_succAbove _ j]
  simp

lemma centeredTrial {q n : ℕ} [NeZero q] (i : Fin q) (j : Fin (n + 1)) (g : ℕ → ℝ) :
    (𝔼 w : Fin (n + 1) → Fin q, ((if w j = i then (1 : ℝ) else 0) - p q) * g (load w i)) =
      v q * 𝔼 u : Fin n → Fin q, (g (load u i + 1) - g (load u i)) := by
  rw [avgInsert j, mul_expect]
  apply expect_congr rfl
  intro u _
  calc
    _ = 𝔼 x : Fin q, if x = i then (1 - p q) * g (load u i + 1) else -p q * g (load u i) := by
      apply expect_congr rfl
      intro x _
      simp only [Fin.insertNth_apply_same, loadInsert]
      split_ifs <;> simp [Nat.add_comm]
    _ = _ := by rw [avgChoice]; unfold v; ring

/-- The binomial integration-by-parts identity, obtained by removing each job in turn. -/
lemma stein {q : ℕ} [NeZero q] (n : ℕ) (i : Fin q) (g : ℕ → ℝ) :
    (𝔼 w : Fin (n + 1) → Fin q, ((load w i : ℝ) - (n + 1 : ℕ) * p q) * g (load w i)) =
      ((n + 1 : ℕ) * v q) * 𝔼 u : Fin n → Fin q, (g (load u i + 1) - g (load u i)) := by
  calc
    _ = 𝔼 w : Fin (n + 1) → Fin q, ∑ j : Fin (n + 1),
        ((if w j = i then (1 : ℝ) else 0) - p q) * g (load w i) := by
      apply expect_congr rfl
      intro w _
      rw [← sum_mul, sum_sub_distrib]
      congr 1
      simp [load]
    _ = _ := by
      rw [expect_sum_comm]
      simp_rw [centeredTrial]
      simp [mul_assoc]

lemma centeredSecond {q : ℕ} [NeZero q] (n : ℕ) (i : Fin q) :
    (𝔼 w : Fin n → Fin q, ((load w i : ℝ) - n * p q) ^ 2) = n * v q := by
  cases n with
  | zero => simp [load]
  | succ n =>
    have h := stein n i (fun j ↦ (j : ℝ) - (n + 1 : ℕ) * p q)
    simpa [pow_two, sub_sub_sub_cancel_right, Fintype.expect_const] using h

/-- A ramp of slope one on the test interval, bounded everywhere by its width plus one. -/
noncomputable def ramp (c r : ℝ) (j : ℕ) : ℝ := min (max ((j : ℝ) - c + r) 0) (2 * r + 1)

lemma rampStep (c r : ℝ) (j : ℕ) :
    (if |(j : ℝ) - c| ≤ r then (1 : ℝ) else 0) ≤ ramp c r (j + 1) - ramp c r j := by
  split_ifs with h
  · obtain ⟨h₁, h₂⟩ := abs_le.mp h
    unfold ramp
    push_cast
    rw [max_eq_left (by linarith), min_eq_left (by linarith),
      max_eq_left (by linarith), min_eq_left (by linarith)]
    linarith
  · apply sub_nonneg.mpr
    unfold ramp
    gcongr
    exact_mod_cast Nat.le_succ j

lemma rampSq (c r : ℝ) (hr : 0 ≤ r) (j : ℕ) : (ramp c r j) ^ 2 ≤ (2 * r + 1) ^ 2 := by
  have h₀ : 0 ≤ ramp c r j := le_min (le_max_right _ _) (by linarith)
  exact pow_le_pow_left₀ h₀ (min_le_right _ _) _

/-- A uniform short-interval bound for each server, valid around every real center. -/
lemma singleWindow {q : ℕ} [NeZero q] (hv : 0 < v q) (n : ℕ) (i : Fin q) (c r : ℝ) (hr : 0 ≤ r) :
    (𝔼 w : Fin n → Fin q, if |(load w i : ℝ) - c| ≤ r then (1 : ℝ) else 0) *
      Real.sqrt ((n + 1 : ℕ) * v q) ≤ 2 * r + 1 := by
  let M : ℝ := (n + 1 : ℕ) * v q
  let s := Real.sqrt M
  let d := 𝔼 w : Fin n → Fin q, (ramp c r (load w i + 1) - ramp c r (load w i))
  let A := 𝔼 w : Fin n → Fin q, if |(load w i : ℝ) - c| ≤ r then (1 : ℝ) else 0
  have hM : 0 < M := mul_pos (by positivity) hv
  have hs : 0 < s := Real.sqrt_pos.2 hM
  have hss : s ^ 2 = M := Real.sq_sqrt hM.le
  have hAd : A ≤ d := expect_le_expect fun w _ ↦ rampStep c r (load w i)
  have hB : 0 ≤ 2 * r + 1 := by linarith
  have hsq : (𝔼 w : Fin (n + 1) → Fin q, ramp c r (load w i) ^ 2) ≤ (2 * r + 1) ^ 2 := by
    calc
      _ ≤ 𝔼 _w : Fin (n + 1) → Fin q, (2 * r + 1) ^ 2 :=
        expect_le_expect fun w _ ↦ rampSq c r hr (load w i)
      _ = _ := Fintype.expect_const _
  have hcs := expect_mul_sq_le_sq_mul_sq univ
    (fun w : Fin (n + 1) → Fin q ↦ (load w i : ℝ) - (n + 1 : ℕ) * p q)
    (fun w ↦ ramp c r (load w i))
  rw [stein n i (ramp c r), centeredSecond] at hcs
  have hd : M * d ≤ s * (2 * r + 1) := by
    apply le_of_sq_le_sq _ (mul_nonneg hs.le hB)
    calc
      _ ≤ M * (𝔼 w : Fin (n + 1) → Fin q, ramp c r (load w i) ^ 2) := hcs
      _ ≤ M * (2 * r + 1) ^ 2 := mul_le_mul_of_nonneg_left hsq hM.le
      _ = _ := by rw [mul_pow, hss]
  change A * s ≤ 2 * r + 1
  apply le_of_mul_le_mul_left _ hs
  calc
    s * (A * s) = M * A := by rw [← hss]; ring
    _ ≤ M * d := mul_le_mul_of_nonneg_left hAd hM.le
    _ ≤ _ := hd

lemma sqAroundMean {α : Type*} [Fintype α] [Nonempty α] (Z : α → ℝ) (c : ℝ) :
    (𝔼 x, (Z x - 𝔼 y, Z y) ^ 2) ≤ 𝔼 x, (Z x - c) ^ 2 := by
  have h (a : ℝ) : (𝔼 x, (Z x - a) ^ 2) =
      (𝔼 x, Z x ^ 2) - (2 * a) * (𝔼 x, Z x) + a ^ 2 := by
    calc
      _ = 𝔼 x, (Z x ^ 2 - (2 * a) * Z x + a ^ 2) := expect_congr rfl fun x _ ↦ by ring
      _ = _ := by rw [expect_add_distrib, expect_sub_distrib, ← mul_expect, Fintype.expect_const]
  rw [h, h]
  nlinarith [sq_nonneg ((𝔼 x, Z x) - c)]

lemma medianWindow (k n : ℕ) (hv : 0 < v (2 * k + 1)) (c r : ℝ) (hr : 0 ≤ r) :
    (𝔼 w : Fin n → Fin (2 * k + 1), if |(medianLoad w : ℝ) - c| ≤ r then (1 : ℝ) else 0) *
      Real.sqrt ((n + 1 : ℕ) * v (2 * k + 1)) ≤ (2 * k + 1 : ℕ) * (2 * r + 1) := by
  let q := 2 * k + 1
  let s := Real.sqrt ((n + 1 : ℕ) * v q)
  let f (w : Fin n → Fin q) (i : Fin q) : ℝ := if |(load w i : ℝ) - c| ≤ r then 1 else 0
  have hf (w : Fin n → Fin q) (i : Fin q) : 0 ≤ f w i := by unfold f; split_ifs <;> norm_num
  calc
    _ ≤ (𝔼 w : Fin n → Fin q, ∑ i, f w i) * s := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      apply expect_le_expect
      intro w _
      exact single_le_sum (fun i _ ↦ hf w i) (mem_univ _)
    _ = ∑ i : Fin q, (𝔼 w : Fin n → Fin q, f w i) * s := by rw [expect_sum_comm, sum_mul]
    _ ≤ ∑ _i : Fin q, (2 * r + 1) := sum_le_sum fun i _ ↦ singleWindow hv n i c r hr
    _ = _ := by simp [q]; ring

lemma varianceOutside {α : Type*} [Fintype α] [Nonempty α] (Z : α → ℝ) (c r : ℝ) (hr : 0 ≤ r) :
    r ^ 2 * (1 - 𝔼 x, if |Z x - c| ≤ r then (1 : ℝ) else 0) ≤ 𝔼 x, (Z x - c) ^ 2 := by
  calc
    _ = 𝔼 x, r ^ 2 * (1 - (if |Z x - c| ≤ r then (1 : ℝ) else 0)) := by
      rw [← mul_expect, expect_sub_distrib, Fintype.expect_const]
    _ ≤ _ := by
      apply expect_le_expect
      intro x _
      split_ifs with h
      · simp [sq_nonneg]
      · have hh := pow_le_pow_left₀ hr (le_of_lt (lt_of_not_ge h)) 2
        simpa using hh

/-- Once a single-server standard deviation exceeds `4q`, the median variance
is at least the single-server variance divided by `128*q^2`. -/
lemma lowerBound (k n : ℕ) (hv : 0 < v (2 * k + 1))
    (hlarge : (4 * ((2 * k + 1 : ℕ) : ℝ)) ^ 2 ≤ (n + 1 : ℕ) * v (2 * k + 1)) :
    ((n : ℝ) * v (2 * k + 1)) / (128 * ((2 * k + 1 : ℕ) : ℝ) ^ 2) ≤ medianVariance k n := by
  let q := 2 * k + 1
  let s := Real.sqrt ((n + 1 : ℕ) * v q)
  let r := s / (8 * (q : ℝ))
  let Z := fun w : Fin n → Fin q ↦ (medianLoad w : ℝ)
  let c := 𝔼 w, Z w
  let A := 𝔼 w, if |Z w - c| ≤ r then (1 : ℝ) else 0
  have hq : 0 < (q : ℝ) := by dsimp [q]; positivity
  have hs : 0 < s := Real.sqrt_pos.2 (mul_pos (by positivity) hv)
  have hss : s ^ 2 = (n + 1 : ℕ) * v q := Real.sq_sqrt (mul_nonneg (by positivity) hv.le)
  have hr : 0 ≤ r := div_nonneg hs.le (by positivity)
  have h4 : 4 * (q : ℝ) ≤ s := Real.le_sqrt_of_sq_le hlarge
  have h8 : r * (8 * (q : ℝ)) = s := div_mul_cancel₀ _ (by positivity)
  have hA : A ≤ 1 / 2 := by
    have hw : A * s ≤ (q : ℝ) * (2 * r + 1) := medianWindow k n hv c r hr
    apply le_of_mul_le_mul_right _ hs
    nlinarith only [hw, h4, h8]
  have hvar : r ^ 2 * (1 - A) ≤ medianVariance k n := varianceOutside Z c r hr
  calc
    _ ≤ ((n + 1 : ℕ) * v q) / (128 * (q : ℝ) ^ 2) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hv.le
      exact_mod_cast Nat.le_succ n
    _ = r ^ 2 / 2 := by
      rw [← hss]; dsimp only [r]; ring
    _ ≤ r ^ 2 * (1 - A) := by nlinarith only [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hA)]
    _ ≤ _ := hvar

/-- If `k+1` centered entries lie above `a ≥ 0`, their complement must offset
at least `(k+1)*a`. Cauchy-Schwarz on that complement bounds its energy. -/
lemma majoritySquare {α : Type*} [Fintype α] [DecidableEq α] (k : ℕ) (d : α → ℝ)
    (s : Finset α) (hs : s.card = k + 1) (ht : sᶜ.card = k)
    (hz : ∑ i, d i = 0) (a : ℝ) (ha : 0 ≤ a) (hd : ∀ i ∈ s, a ≤ d i) :
    (2 * (k : ℝ) + 1) * (k + 1) * a ^ 2 ≤ k * ∑ i, d i ^ 2 := by
  have hsum : ((k : ℝ) + 1) * a ≤ ∑ i ∈ s, d i := by
    simpa [hs] using sum_le_sum hd
  have hsq : ((k : ℝ) + 1) * a ^ 2 ≤ ∑ i ∈ s, d i ^ 2 := by
    simpa [hs] using sum_le_sum (fun i hi ↦ pow_le_pow_left₀ ha (hd i hi) 2)
  have hbal : (∑ i ∈ s, d i) = -(∑ i ∈ sᶜ, d i) := by
    linarith only [(sum_add_sum_compl s d).trans hz]
  have hc : (((k : ℝ) + 1) * a) ^ 2 ≤ k * ∑ i ∈ sᶜ, d i ^ 2 := by
    calc
      _ ≤ (∑ i ∈ s, d i) ^ 2 := pow_le_pow_left₀ (mul_nonneg (by positivity) ha) hsum _
      _ = (∑ i ∈ sᶜ, d i) ^ 2 := by rw [hbal]; ring
      _ ≤ _ := by simpa [ht] using sum_mul_sq_le_sq_mul_sq sᶜ (fun _ ↦ (1 : ℝ)) d
  rw [← sum_add_sum_compl s (fun i ↦ d i ^ 2)]
  nlinarith only [hc, mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (α := ℝ) k)]

lemma sortedSquare (k : ℕ) (d : Fin (2 * k + 1) → ℝ) (hd : Monotone d) (hz : ∑ i, d i = 0) :
    (2 * (k : ℝ) + 1) * (k + 1) * (d ⟨k, by omega⟩) ^ 2 ≤ k * ∑ i, d i ^ 2 := by
  let j : Fin (2 * k + 1) := ⟨k, by omega⟩
  by_cases ha : 0 ≤ d j
  · have hs : (Ici j).card = k + 1 := by rw [Fin.card_Ici]; dsimp [j]; omega
    exact majoritySquare k d (Ici j) hs (by rw [card_compl, hs]; simp; omega) hz (d j) ha
      (fun i hi ↦ hd (mem_Ici.mp hi))
  · have hs : (Iic j).card = k + 1 := Fin.card_Iic j
    have h := majoritySquare k (fun i ↦ -d i) (Iic j) hs (by rw [card_compl, hs]; simp; omega)
      (by simp [hz]) (-d j) (by linarith) (fun i hi ↦ neg_le_neg (hd (mem_Iic.mp hi)))
    simpa [j] using h

lemma totalLoad {q n : ℕ} (w : Fin n → Fin q) : ∑ i, load w i = n := by
  unfold load
  rw [sum_comm]
  simp

lemma sharpUpper (k n : ℕ) :
    ((k : ℝ) + 1) * medianVariance k n ≤ k * (n * v (2 * k + 1)) := by
  let q := 2 * k + 1
  let μ := (n : ℝ) * p q
  let Z := fun w : Fin n → Fin q ↦ (medianLoad w : ℝ)
  have hq : 0 < (q : ℝ) := by dsimp [q]; positivity
  have point (w : Fin n → Fin q) : (q : ℝ) * ((k : ℝ) + 1) * (Z w - μ) ^ 2 ≤
      k * ∑ i, ((load w i : ℝ) - μ) ^ 2 := by
    let σ := Tuple.sort (load w)
    let d (j : Fin q) : ℝ := (load w (σ j) : ℝ) - μ
    have hm : Monotone d := by
      intro i j hij
      apply sub_le_sub_right
      exact_mod_cast (Tuple.monotone_sort (load w) hij)
    have hz : ∑ i, d i = 0 := by
      have hw : (∑ i, (load w i : ℝ)) = n := by exact_mod_cast totalLoad w
      dsimp only [d]
      rw [sum_sub_distrib, Equiv.sum_comp σ (fun i ↦ (load w i : ℝ)), hw]
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp only [μ, p]
      field_simp
      ring
    have h := sortedSquare k d hm hz
    have he := Equiv.sum_comp σ (fun i ↦ ((load w i : ℝ) - μ) ^ 2)
    change (∑ i, (d i) ^ 2) = _ at he
    rw [he] at h
    simpa only [q, d, σ, Z, medianLoad, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using h
  have hE := expect_le_expect (s := univ) (fun w _ ↦ point w)
  rw [← mul_expect, ← mul_expect, expect_sum_comm] at hE
  have second (i : Fin q) : (𝔼 w : Fin n → Fin q, ((load w i : ℝ) - μ) ^ 2) = n * v q := centeredSecond n i
  simp only [second, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hE
  have hm := sqAroundMean Z μ
  change medianVariance k n ≤ _ at hm
  apply le_of_mul_le_mul_left _ hq
  calc
    (q : ℝ) * ((k + 1) * medianVariance k n) ≤
        (q : ℝ) * ((k : ℝ) + 1) * (𝔼 w, (Z w - μ) ^ 2) := by
      rw [← mul_assoc]; apply mul_le_mul_of_nonneg_left hm; positivity
    _ ≤ _ := hE.trans_eq (by ring)

/-- Number of assignments with a prescribed vector of occupancies. The coefficient
of a monomial in `(X₁ + ⋯ + Xq)^n` counts its assignments in two ways. -/
lemma fiberCard {q n : ℕ} (d : Fin q → ℕ) (hd : ∑ i, d i = n) :
    (univ.filter (fun w : Fin n → Fin q ↦ load w = d)).card = Nat.multinomial univ d := by
  classical
  let D : Fin q →₀ ℕ := Finsupp.equivFunOnFinite.symm d
  let m (w : Fin n → Fin q) : Fin q →₀ ℕ := ∑ j, Finsupp.single (w j) 1
  have hm (w : Fin n → Fin q) (i : Fin q) : m w i = load w i := by
    simp [m, load, Finsupp.finsetSum_apply, Finsupp.single_apply]
  have hD : D.sum (fun _ a ↦ a) = n := by
    exact (Finsupp.sum_of_support_subset D (subset_univ _) (fun _ a ↦ a) (fun _ _ ↦ rfl)).trans hd
  have heq (w : Fin n → Fin q) : m w = D ↔ load w = d := by
    rw [Finsupp.ext_iff, funext_iff]
    simp only [hm]
    rfl
  have hprod (w : Fin n → Fin q) : (∏ j, MvPolynomial.X (w j) : MvPolynomial (Fin q) ℕ) =
      MvPolynomial.monomial (m w) 1 :=
    (MvPolynomial.monomial_sum_one univ (fun j ↦ Finsupp.single (w j) 1)).symm
  have hpow := Finset.sum_pow' univ (MvPolynomial.X (R := ℕ) : Fin q → _) n
  simp only [Fintype.piFinset_univ, hprod] at hpow
  have hc := congrArg (MvPolynomial.coeff D) hpow
  rw [MvPolynomial.coeff_sum_X_pow_of_fintype, if_pos hD,
    Finsupp.multinomial_eq_of_support_subset (subset_univ _), MvPolynomial.coeff_sum] at hc
  simpa [MvPolynomial.coeff_monomial, heq, D, Finset.sum_boole] using hc.symm

/-- Weighted sum over the load vectors with total `n`, with no sum over job assignments. -/
lemma weightedLoads {q n : ℕ} (f : (Fin q → ℕ) → ℕ) :
    (∑ w : Fin n → Fin q, f (load w)) =
      ∑ d ∈ Finset.piAntidiag (univ : Finset (Fin q)) n, Nat.multinomial univ d * f d := by
  classical
  have hmem (w : Fin n → Fin q) (_ : w ∈ univ) :
      load w ∈ Finset.piAntidiag (univ : Finset (Fin q)) n := by
    simp [Finset.mem_piAntidiag, totalLoad]
  rw [← Finset.sum_fiberwise_of_maps_to' hmem f]
  apply sum_congr rfl
  intro d hd
  simp only [sum_const, nsmul_eq_mul, fiberCard d (mem_piAntidiag.mp hd).1, Nat.cast_id]

/-- Unnormalized raw moment, summed over load vectors of total `n`. -/
noncomputable def momentTotal (k n a : ℕ) : ℕ :=
  ∑ d ∈ Finset.piAntidiag (univ : Finset (Fin (2 * k + 1))) n,
    Nat.multinomial univ d * (d (Tuple.sort d ⟨k, by omega⟩)) ^ a

lemma momentExact (k n a : ℕ) :
    (𝔼 w : Fin n → Fin (2 * k + 1), (medianLoad w : ℝ) ^ a) =
      (momentTotal k n a : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ n := by
  apply (eq_div_iff (by positivity)).2
  rw [mul_comm]
  have h := Fintype.card_mul_expect (fun w : Fin n → Fin (2 * k + 1) ↦ (medianLoad w : ℝ) ^ a)
  have hm : momentTotal k n a = ∑ w : Fin n → Fin (2 * k + 1), medianLoad w ^ a :=
    (weightedLoads (n := n) (fun b : Fin (2 * k + 1) → ℕ ↦ (b (Tuple.sort b ⟨k, by omega⟩)) ^ a)).symm
  simpa [Fintype.card_fun, hm] using h

/-- Exact finite-sample variance from two multinomial sums, for every `k` and `n`. -/
lemma finiteVariance (k n : ℕ) : medianVariance k n =
    (momentTotal k n 2 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ n -
    ((momentTotal k n 1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ n) ^ 2 := by
  let Z := fun w : Fin n → Fin (2 * k + 1) ↦ (medianLoad w : ℝ)
  let a := 𝔼 w, Z w
  have h : (𝔼 w, (Z w - a) ^ 2) = (𝔼 w, Z w ^ 2) - a ^ 2 := by
    calc
      _ = 𝔼 w, (Z w ^ 2 - (2 * a) * Z w + a ^ 2) := expect_congr rfl fun w _ ↦ by ring
      _ = _ := by rw [expect_add_distrib, expect_sub_distrib, ← mul_expect, Fintype.expect_const]; dsimp [a]; ring
  calc
    _ = (𝔼 w, Z w ^ 2) - a ^ 2 := h
    _ = _ := by
      rw [← momentExact k n 2, ← momentExact k n 1]
      simp [a, Z]

end MedianServerLoad

open OMA.S_mo_237342 MedianServerLoad

theorem OMA.solution : type_of% @OMA.S_mo_237342.main := by
  intro k hk
  let q := 2 * k + 1
  have hq : 1 < (q : ℝ) := by exact_mod_cast (show 1 < q by dsimp [q]; omega)
  have hq₀ : 0 < (q : ℝ) := by linarith
  have hv : 0 < v q := mul_pos (inv_pos.mpr hq₀) (sub_pos.mpr ((inv_lt_one₀ hq₀).2 hq))
  obtain ⟨N, hN⟩ := exists_nat_ge ((4 * (q : ℝ)) ^ 2 / v q)
  refine ⟨1 / (128 * (q : ℝ) ^ 2), (k : ℝ) / (k + 1), by positivity, by positivity, N, ?_⟩
  intro n hn
  have hn' : (N : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast hn.trans (Nat.le_succ n)
  have hlarge := (div_le_iff₀ hv).mp (le_trans hN hn')
  have hl := lowerBound k n hv hlarge
  have hu : medianVariance k n ≤ ((k : ℝ) / (k + 1)) * (n * v q) := by
    calc
      _ ≤ ((k : ℝ) * (n * v q)) / (k + 1) := (le_div_iff₀ (by positivity)).2 (by
        simpa only [mul_comm (medianVariance k n)] using sharpUpper k n)
      _ = _ := by ring
  simpa [q, p, v, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using And.intro hl hu

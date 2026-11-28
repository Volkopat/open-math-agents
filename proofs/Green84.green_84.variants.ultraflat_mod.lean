import FormalConjectures.GreensOpenProblems.«84»

/-!
# Proof of Ben Green's Open Problem 84 (`Green84.green_84.variants.ultraflat_mod`)

Proves the existence of an infinite family `Q = {p^3 - 1 | p.Prime}` and discrete-log subsets
`A (p^3 - 1) ⊆ ZMod (p^3 - 1)` of size `p ~ q^(1/3)` whose nontrivial Fourier coefficients are
bounded by `2 * √p ≤ 3 * q^(1/6)` via a self-contained proof of Katz's degree-3 character-sum bound
using characteristic-independent Stepanov–Schmidt Hasse derivatives and finite-modulus polynomial
Euler products.
-/

-- Problem: Ben Green's Open Problem 84 — ultraflat mod
-- Upstream: formal-conjectures FormalConjectures/GreensOpenProblems/84.lean:150 (declaration Green84.green_84.variants.ultraflat_mod)
-- Credit: @cybergenesis621

open Filter Polynomial
open scoped ExponentialSum Finset Topology

namespace Green84


-- =============================================================================
-- SECTION 1: ELEMENTARY COMPLEX ROOT-RADIUS LEMMA
-- =============================================================================

/-- If `‖x ^ k + y ^ k‖ ≤ C * r ^ k` for all sufficiently large `k` with `r > 0`,
then `‖x‖ ≤ r` and `‖y‖ ≤ r`. -/
private lemma norm_le_of_pow_add_pow_le {x y : ℂ} {r C : ℝ} (hr : 0 < r)
    (hbound : ∃ K₀ : ℕ, ∀ k ≥ K₀, ‖x ^ k + y ^ k‖ ≤ C * r ^ k) :
    ‖x‖ ≤ r ∧ ‖y‖ ≤ r := by
  suffices hmain : ∀ a b : ℂ, ‖b‖ ≤ ‖a‖ →
      (∃ K₀ : ℕ, ∀ k ≥ K₀, ‖a ^ k + b ^ k‖ ≤ C * r ^ k) → ‖a‖ ≤ r by
    rcases le_total ‖x‖ ‖y‖ with hxy | hyx
    · have hy := hmain y x hxy (by
        obtain ⟨K₀, hK⟩ := hbound
        exact ⟨K₀, fun k hk => by rw [add_comm]; exact hK k hk⟩)
      exact ⟨hxy.trans hy, hy⟩
    · have hx := hmain x y hyx hbound
      exact ⟨hx, hyx.trans hx⟩
  intro a b hba ⟨K₀, hK⟩
  by_contra hgt
  push Not at hgt
  have ha_pos : 0 < ‖a‖ := hr.trans hgt
  have ha_ne : a ≠ 0 := norm_pos_iff.mp ha_pos
  set w : ℂ := b / a
  have hratio_lt : r / ‖a‖ < 1 := (div_lt_one ha_pos).mpr hgt
  have hratio_nn : 0 ≤ r / ‖a‖ := div_nonneg hr.le ha_pos.le
  have h_tendsto : Tendsto (fun k : ℕ => (1 : ℂ) + w ^ k) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h0 : Tendsto (fun k : ℕ => C * (r / ‖a‖) ^ k) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hratio_nn hratio_lt).const_mul C
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [Filter.eventually_ge_atTop K₀] with k hk
    have h1 : (1 : ℂ) + w ^ k = (a ^ k + b ^ k) / a ^ k := by
      have hak : a ^ k ≠ 0 := pow_ne_zero k ha_ne
      simp only [w, div_pow]
      field_simp [hak]
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), h1, norm_div, norm_pow, div_pow]
    calc
      ‖a ^ k + b ^ k‖ / ‖a‖ ^ k ≤ (C * r ^ k) / ‖a‖ ^ k :=
        div_le_div_of_nonneg_right (hK k hk) (pow_nonneg ha_pos.le k)
      _ = C * (r ^ k / ‖a‖ ^ k) := by ring
  have hw_tendsto : Tendsto (fun k : ℕ => w ^ k) atTop (𝓝 (-1 : ℂ)) := by
    have := h_tendsto.sub_const (1 : ℂ)
    simpa using this
  have hw_shift : Tendsto (fun k : ℕ => w ^ (k + 1)) atTop (𝓝 (-1 : ℂ)) :=
    hw_tendsto.comp (tendsto_add_atTop_nat 1)
  have hw_mul : Tendsto (fun k : ℕ => w * w ^ k) atTop (𝓝 (w * (-1 : ℂ))) :=
    hw_tendsto.const_mul w
  have hw_mul' : Tendsto (fun k : ℕ => w ^ (k + 1)) atTop (𝓝 (-w)) := by
    simpa [pow_succ'] using hw_mul
  have hw_eq : (-1 : ℂ) = -w := tendsto_nhds_unique hw_shift hw_mul'
  have hw_one : w = 1 := by linear_combination hw_eq
  have hconst : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 (-1 : ℂ)) := by
    simpa [hw_one] using hw_tendsto
  have h1m1 : (1 : ℂ) = -1 := tendsto_nhds_unique tendsto_const_nhds hconst
  norm_num at h1m1

/-- Root-radius extraction along `3 * k`: if `‖α₁ ^ (3 * k) + α₂ ^ (3 * k)‖ ≤ C * R ^ (3 * k)`
for all sufficiently large `k` (with `R > 0`), then `‖α₁ + α₂‖ ≤ 2 * R`. -/
lemma norm_add_le_two_mul_of_pow_three_mul {α₁ α₂ : ℂ} {R C : ℝ} (hR : 0 < R)
    (hbound : ∃ K₀ : ℕ, ∀ k ≥ K₀, ‖α₁ ^ (3 * k) + α₂ ^ (3 * k)‖ ≤ C * R ^ (3 * k)) :
    ‖α₁ + α₂‖ ≤ 2 * R := by
  have h3 := norm_le_of_pow_add_pow_le (x := α₁ ^ 3) (y := α₂ ^ 3) (r := R ^ 3) (C := C)
    (pow_pos hR 3) (by
      obtain ⟨K₀, hK⟩ := hbound
      exact ⟨K₀, fun k hk => by simpa [pow_mul] using hK k hk⟩)
  have hα₁ : ‖α₁‖ ≤ R := by
    by_contra h
    push Not at h
    have hlt : R ^ 3 < ‖α₁‖ ^ 3 := pow_lt_pow_left₀ h hR.le (by norm_num)
    have h1 : ‖α₁‖ ^ 3 ≤ R ^ 3 := by simpa [norm_pow] using h3.1
    linarith
  have hα₂ : ‖α₂‖ ≤ R := by
    by_contra h
    push Not at h
    have hlt : R ^ 3 < ‖α₂‖ ^ 3 := pow_lt_pow_left₀ h hR.le (by norm_num)
    have h2 : ‖α₂‖ ^ 3 ≤ R ^ 3 := by simpa [norm_pow] using h3.2
    linarith
  calc
    ‖α₁ + α₂‖ ≤ ‖α₁‖ + ‖α₂‖ := norm_add_le α₁ α₂
    _ ≤ R + R := add_le_add hα₁ hα₂
    _ = 2 * R := by ring

-- =============================================================================
-- SECTION 2: STEPANOV–SCHMIDT HASSE-DERIVATIVE BOUND FOR `y^d = g(u)`
-- =============================================================================

/-- If all Hasse derivatives of order `< M` vanish at `r`, then `r` has root multiplicity `≥ M`. -/
private lemma le_rootMultiplicity_of_hasseDeriv_eval_zero {K : Type*} [Field K]
    (Φ : K[X]) (hΦ : Φ ≠ 0) (r : K) (M : ℕ)
    (hzero : ∀ m < M, (Polynomial.hasseDeriv m Φ).eval r = 0) :
    M ≤ Φ.rootMultiplicity r := by
  rw [Polynomial.le_rootMultiplicity_iff hΦ]
  have hdvd_t : X ^ M ∣ Polynomial.taylor r Φ := by
    rw [Polynomial.X_pow_dvd_iff]
    intro m hm
    rw [Polynomial.taylor_coeff]
    exact hzero m hm
  obtain ⟨Q, hQ⟩ := hdvd_t
  refine ⟨Polynomial.taylor (-r) Q, ?_⟩
  have hback : Polynomial.taylor (-r) (Polynomial.taylor r Φ) = Φ := by
    rw [Polynomial.taylor_taylor, neg_add_cancel, Polynomial.taylor_zero]
  rw [← hback, hQ, Polynomial.taylor_mul, Polynomial.taylor_X_pow]
  simp [sub_eq_add_neg]

/-- For `CharP K p` and `q = p ^ t`, `hasseDeriv m (X ^ (b * q)) = 0` for `0 < m < q`. -/
private lemma hasseDeriv_X_pow_mul_char_pow {K : Type*} [CommRing K] (p t : ℕ) [Fact p.Prime]
    [CharP K p] (b m : ℕ) (hm0 : 0 < m) (hmq : m < p ^ t) :
    Polynomial.hasseDeriv m ((X : K[X]) ^ (b * p ^ t)) = 0 := by
  have ht : Polynomial.taylor (1 : K) ((X : K[X]) ^ (b * p ^ t)) =
      (X ^ (p ^ t) + 1) ^ b := by
    rw [Polynomial.taylor_X_pow, pow_mul', add_pow_char_pow]
    simp
  have hcoeff : ((b * p ^ t).choose m : K) = 0 := by
    have h1 : (Polynomial.taylor (1 : K) ((X : K[X]) ^ (b * p ^ t))).coeff m =
        ((b * p ^ t).choose m : K) := by
      rw [Polynomial.taylor_coeff, ← Polynomial.monomial_one_right_eq_X_pow,
        Polynomial.hasseDeriv_monomial, Polynomial.eval_monomial, one_pow, mul_one, mul_one]
    rw [← h1, ht, add_pow]
    simp only [one_pow, mul_one, Polynomial.finsetSum_coeff]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← pow_mul, mul_comm, ← Polynomial.C_eq_natCast, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow]
    split_ifs with hjm
    · exfalso
      rcases eq_or_ne j 0 with rfl | hj0
      · simp at hjm; omega
      · have : p ^ t ≤ p ^ t * j := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hj0)
        omega
    · ring
  rw [← Polynomial.monomial_one_right_eq_X_pow, Polynomial.hasseDeriv_monomial, hcoeff,
    mul_one, Polynomial.monomial_zero_right]

/-- Shift map `K[X] → (K[X])[Y]` via `taylor X (f.map C)`, whose `Y^k` coefficient
is `hasseDeriv k f`. -/
private noncomputable def polyShift {K : Type*} [CommRing K] (f : K[X]) : (K[X])[X] :=
  Polynomial.taylor (Polynomial.X : K[X]) (f.map Polynomial.C)

private lemma polyShift_pow {K : Type*} [CommRing K] (f : K[X]) (n : ℕ) :
    polyShift (f ^ n) = (polyShift f) ^ n := by
  simp [polyShift, Polynomial.map_pow, Polynomial.taylor_pow]

private lemma hasseDeriv_map_C {K : Type*} [CommRing K] (k : ℕ) (f : K[X]) :
    Polynomial.hasseDeriv k (f.map (Polynomial.C : K →+* K[X])) =
      (Polynomial.hasseDeriv k f).map Polynomial.C := by
  ext n
  simp [Polynomial.hasseDeriv_coeff, Polynomial.coeff_map]

private lemma eval_X_map_C {K : Type*} [CommRing K] (f : K[X]) :
    (f.map (Polynomial.C : K →+* K[X])).eval Polynomial.X = f := by
  induction f using Polynomial.induction_on' with
  | add a b iha ihb => simp [iha, ihb]
  | monomial n a => simp [Polynomial.C_mul_X_pow_eq_monomial]

private lemma polyShift_coeff {K : Type*} [CommRing K] (f : K[X]) (k : ℕ) :
    (polyShift f).coeff k = Polynomial.hasseDeriv k f := by
  rw [polyShift, Polynomial.taylor_coeff, hasseDeriv_map_C, eval_X_map_C]

/-- The tail polynomial `H ∈ (K[X])[Y]` satisfying `polyShift g = C g + Y * H`. -/
private noncomputable def shiftTail {K : Type*} [CommRing K] (g : K[X]) : (K[X])[X] :=
  ∑ i ∈ Finset.range g.natDegree, Polynomial.C (Polynomial.hasseDeriv (i + 1) g) * X ^ i

private lemma coeff_shiftTail {K : Type*} [CommRing K] (g : K[X]) (k : ℕ) :
    (shiftTail g).coeff k = if k < g.natDegree then Polynomial.hasseDeriv (k + 1) g else 0 := by
  simp only [shiftTail, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  split_ifs with hk
  · rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hbk; rw [if_neg hbk.symm, mul_zero]
    · intro hm; exact absurd (Finset.mem_range.mpr hk) hm
  · refine Finset.sum_eq_zero fun b hb => ?_
    have hlt : b < g.natDegree := Finset.mem_range.mp hb
    rw [if_neg (by omega), mul_zero]

private lemma polyShift_eq_C_add_X_mul_shiftTail {K : Type*} [CommRing K] (g : K[X]) :
    polyShift g = Polynomial.C g + X * shiftTail g := by
  apply Polynomial.ext
  intro k
  rw [polyShift_coeff, Polynomial.coeff_add, Polynomial.coeff_C]
  cases k with
  | zero =>
    simp
  | succ k =>
    rw [if_neg (Nat.succ_ne_zero k), zero_add, Polynomial.coeff_X_mul, coeff_shiftTail]
    split_ifs with hk
    · rfl
    · exact Polynomial.hasseDeriv_eq_zero_of_lt_natDegree g (k + 1) (by omega)

/-- Degree bound for coefficients of `(shiftTail g) ^ j`. -/
private lemma natDegree_coeff_shiftTail_pow_le {K : Type*} [CommRing K] (g : K[X]) :
    ∀ j w : ℕ, ((shiftTail g ^ j).coeff w).natDegree ≤ j * g.natDegree := by
  intro j
  induction j with
  | zero =>
    intro w
    simp only [pow_zero, Polynomial.coeff_one]
    split_ifs <;> simp
  | succ j ih =>
    intro w
    rw [pow_succ, Polynomial.coeff_mul]
    refine (Polynomial.natDegree_sum_le _ _).trans ?_
    rw [Finset.fold_max_le]
    refine ⟨Nat.zero_le _, fun xy _ => ?_⟩
    refine (Polynomial.natDegree_mul_le).trans ?_
    have h1 := ih xy.1
    have h2 : ((shiftTail g).coeff xy.2).natDegree ≤ g.natDegree := by
      rw [coeff_shiftTail]
      split_ifs with h
      · exact (Polynomial.natDegree_hasseDeriv_le g (xy.2 + 1)).trans (Nat.sub_le _ _)
      · simp
    calc
      ((shiftTail g ^ j).coeff xy.1).natDegree + ((shiftTail g).coeff xy.2).natDegree
          ≤ j * g.natDegree + g.natDegree := Nat.add_le_add h1 h2
      _ = (j + 1) * g.natDegree := by ring

/-- Explicit clearing polynomial `QClear g N m v` satisfying
`g ^ m * hasseDeriv v (g ^ N) = g ^ N * QClear g N m v` whenever `v ≤ m` and `(N = 0 ∨ m ≤ N)`. -/
private noncomputable def QClear {K : Type*} [CommRing K] (g : K[X]) (N m v : ℕ) : K[X] :=
  if N = 0 then
    if v = 0 then g ^ m else 0
  else
    ∑ j ∈ Finset.range (v + 1),
      (N.choose j : K[X]) * g ^ (m - j) * ((shiftTail g ^ j).coeff (v - j))

private lemma mul_hasseDeriv_pow_eq_pow_mul_QClear {K : Type*} [CommRing K]
    (g : K[X]) (N m v : ℕ) (hvm : v ≤ m) (hN : N = 0 ∨ m ≤ N) :
    g ^ m * Polynomial.hasseDeriv v (g ^ N) = g ^ N * QClear g N m v := by
  rcases hN with rfl | hmN
  · simp only [QClear, ↓reduceIte, pow_zero, one_mul]
    cases v with
    | zero => simp
    | succ v =>
      rw [Polynomial.hasseDeriv_apply_one (v + 1) (Nat.succ_pos v), mul_zero]
      simp
  · by_cases hN0 : N = 0
    · subst hN0
      have hm0 : m = 0 := by omega
      have hv0 : v = 0 := by omega
      subst hm0; subst hv0
      simp [QClear]
    · simp only [QClear, if_neg hN0]
      rw [← polyShift_coeff, polyShift_pow, polyShift_eq_C_add_X_mul_shiftTail,
        add_comm (Polynomial.C g), add_pow, Polynomial.finsetSum_coeff]
      rw [Finset.mul_sum, Finset.mul_sum]
      let termY : ℕ → K[X] := fun j =>
        (((X * shiftTail g) ^ j * (Polynomial.C g) ^ (N - j) *
            ((N.choose j : ℕ) : (K[X])[X])).coeff v)
      change ∑ j ∈ Finset.range (N + 1), g ^ m * termY j =
        ∑ j ∈ Finset.range (v + 1),
          g ^ N * ((N.choose j : K[X]) * g ^ (m - j) * (shiftTail g ^ j).coeff (v - j))
      have htrunc :
          ∑ j ∈ Finset.range (N + 1), g ^ m * termY j =
          ∑ j ∈ Finset.range (v + 1), g ^ m * termY j := by
        refine (Finset.sum_subset (Finset.range_mono (by omega : v + 1 ≤ N + 1)) ?_).symm
        intro j _ hjn
        have hjv : v < j := by
          simp only [Finset.mem_range, not_lt] at hjn
          omega
        have hcoeff0 : termY j = 0 := by
          simp only [termY, mul_pow, ← Polynomial.C_pow]
          have hrearr :
              X ^ j * shiftTail g ^ j * Polynomial.C (g ^ (N - j)) *
                  ((N.choose j : ℕ) : (K[X])[X]) =
                (shiftTail g ^ j * Polynomial.C (g ^ (N - j)) *
                  ((N.choose j : ℕ) : (K[X])[X])) * X ^ j := by ring
          rw [hrearr, Polynomial.coeff_mul_X_pow', if_neg (by omega)]
        rw [hcoeff0, mul_zero]
      rw [htrunc]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjv : j ≤ v := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hjm : j ≤ m := hjv.trans hvm
      have hcoeff : termY j =
          (N.choose j : K[X]) * g ^ (N - j) * ((shiftTail g ^ j).coeff (v - j)) := by
        simp only [termY, mul_pow, ← Polynomial.C_pow]
        have hnatC : ((N.choose j : ℕ) : (K[X])[X]) = Polynomial.C (N.choose j : K[X]) :=
          (Polynomial.C_eq_natCast (N.choose j)).symm
        rw [hnatC]
        have hrearr :
            X ^ j * shiftTail g ^ j * Polynomial.C (g ^ (N - j)) *
                Polynomial.C (N.choose j : K[X]) =
              (Polynomial.C ((N.choose j : K[X]) * g ^ (N - j)) * shiftTail g ^ j) * X ^ j := by
          simp only [map_mul]
          ring
        rw [hrearr, Polynomial.coeff_mul_X_pow', if_pos hjv, Polynomial.coeff_C_mul]
      rw [hcoeff]
      have hexp : m + (N - j) = N + (m - j) := by omega
      calc
        g ^ m * ((N.choose j : K[X]) * g ^ (N - j) * (shiftTail g ^ j).coeff (v - j))
            = (N.choose j : K[X]) * (g ^ m * g ^ (N - j)) * (shiftTail g ^ j).coeff (v - j) := by ring
        _ = (N.choose j : K[X]) * (g ^ N * g ^ (m - j)) * (shiftTail g ^ j).coeff (v - j) := by
              rw [← pow_add, ← pow_add, hexp]
        _ = g ^ N * ((N.choose j : K[X]) * g ^ (m - j) * (shiftTail g ^ j).coeff (v - j)) := by ring

private lemma natDegree_QClear_le {K : Type*} [CommRing K]
    (g : K[X]) (N m v : ℕ) (hvm : v ≤ m) :
    (QClear g N m v).natDegree ≤ m * g.natDegree := by
  unfold QClear
  split_ifs with hN hv
  · exact Polynomial.natDegree_pow_le
  · simp
  · refine (Polynomial.natDegree_sum_le _ _).trans ?_
    rw [Finset.fold_max_le]
    refine ⟨Nat.zero_le _, fun j hj => ?_⟩
    have hjv : j ≤ v := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hjm : j ≤ m := hjv.trans hvm
    refine (Polynomial.natDegree_mul_le).trans ?_
    have h1 : ((N.choose j : K[X]) * g ^ (m - j)).natDegree ≤ (m - j) * g.natDegree := by
      refine (Polynomial.natDegree_mul_le).trans ?_
      have hc : (N.choose j : K[X]).natDegree = 0 := Polynomial.natDegree_natCast _
      rw [hc, zero_add]
      exact Polynomial.natDegree_pow_le
    have h2 := natDegree_coeff_shiftTail_pow_le g j (v - j)
    calc
      ((N.choose j : K[X]) * g ^ (m - j)).natDegree + ((shiftTail g ^ j).coeff (v - j)).natDegree
          ≤ (m - j) * g.natDegree + j * g.natDegree := Nat.add_le_add h1 h2
      _ = ((m - j) + j) * g.natDegree := by rw [add_mul]
      _ = m * g.natDegree := by rw [Nat.sub_add_cancel hjm]

-- =============================================================================
-- HOISTED STEPANOV DEFINITIONS & ARITHMETIC HELPERS (L-014_S1)
-- =============================================================================

/-- Build polynomial `h_{b,c}(X)` of degree `< D_h` from coefficient vector `h`. -/
private noncomputable def stepanovHPoly {K : Type*} [CommRing K] {B d D_h : ℕ}
    (h : Fin B × Fin d × Fin D_h → K) (b : Fin B) (c : Fin d) : K[X] :=
  ∑ i : Fin D_h, Polynomial.C (h (b, c, i)) * X ^ i.val

private lemma stepanovHPoly_coeff {K : Type*} [CommRing K] {B d D_h : ℕ}
    (h : Fin B × Fin d × Fin D_h → K) (b : Fin B) (c : Fin d) (k : ℕ) :
    (stepanovHPoly h b c).coeff k = if hk : k < D_h then h (b, c, ⟨k, hk⟩) else 0 := by
  simp only [stepanovHPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow]
  split_ifs with hk
  · rw [Finset.sum_eq_single ⟨k, hk⟩]
    · simp
    · intro i _ hi
      have hne : k ≠ i.val := fun heq => hi (Fin.ext heq.symm)
      rw [if_neg hne, mul_zero]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  · refine Finset.sum_eq_zero fun i _ => ?_
    have hne : k ≠ i.val := fun heq => hk (heq.symm ▸ i.isLt)
    rw [if_neg hne, mul_zero]

private lemma stepanovHPoly_natDegree_lt {K : Type*} [CommRing K] {B d D_h : ℕ}
    (hDh : 0 < D_h) (h : Fin B × Fin d × Fin D_h → K) (b : Fin B) (c : Fin d) :
    (stepanovHPoly h b c).natDegree < D_h := by
  by_cases hz : stepanovHPoly h b c = 0
  · rw [hz, Polynomial.natDegree_zero]; exact hDh
  · rw [Polynomial.natDegree_lt_iff_degree_lt hz, Polynomial.degree_lt_iff_coeff_zero]
    intro k hk
    rw [stepanovHPoly_coeff, dif_neg (by omega)]

/-- The Stepanov auxiliary polynomial `Φ(X) = ∑_{b, c} h_{b,c}(X) * X^(b * q) * g^(c * L)`. -/
private noncomputable def stepanovPhi {K : Type*} [CommRing K] {B d D_h : ℕ}
    (g : K[X]) (q L : ℕ) (h : Fin B × Fin d × Fin D_h → K) : K[X] :=
  ∑ b : Fin B, ∑ c : Fin d, stepanovHPoly h b c * X ^ (b.val * q) * g ^ (c.val * L)

/-- The `m`-th target polynomial `R_m(X)` obtained after clearing `g^m` and substituting
`X^q ↦ X` and `g^L ↦ ζ`. -/
private noncomputable def stepanovRPoly {K : Type*} [CommRing K] {B d D_h : ℕ}
    (g : K[X]) (L : ℕ) (ζ : K) (h : Fin B × Fin d × Fin D_h → K) (m : ℕ) : K[X] :=
  ∑ b : Fin B, ∑ c : Fin d,
    X ^ b.val * Polynomial.C (ζ ^ c.val) *
      ∑ rv ∈ Finset.HasAntidiagonal.antidiagonal m,
        Polynomial.hasseDeriv rv.1 (stepanovHPoly h b c) * QClear g (c.val * L) m rv.2

/-- Non-vanishing of `stepanovPhi`: when `g.natDegree = 3 * d - 1`, `q = d * L + 1`,
`D_h + B < L`, and `h ≠ 0`, the nonzero terms have pairwise distinct degrees, so `Φ ≠ 0`! -/
private lemma stepanovPhi_ne_zero {K : Type*} [Field K] {B d D_h : ℕ}
    (hd : 2 ≤ d) (hDh : 0 < D_h) (g : K[X]) (hgdeg : g.natDegree = 3 * d - 1)
    (q L : ℕ) (hqL : q = d * L + 1) (hsmall : D_h + B < L)
    (h : Fin B × Fin d × Fin D_h → K) (hne : h ≠ 0) :
    stepanovPhi g q L h ≠ 0 := by
  classical
  have hg_ne : g ≠ 0 := by
    intro h0; rw [h0, Polynomial.natDegree_zero] at hgdeg; omega
  let term : Fin B × Fin d → K[X] := fun bc =>
    stepanovHPoly h bc.1 bc.2 * X ^ (bc.1.val * q) * g ^ (bc.2.val * L)
  have hsum_eq : stepanovPhi g q L h = ∑ bc : Fin B × Fin d, term bc := by
    simp only [stepanovPhi, term, Fintype.sum_prod_type]
  have hex : ∃ bc : Fin B × Fin d, term bc ≠ 0 := by
    have hne' : ∃ p : Fin B × Fin d × Fin D_h, h p ≠ 0 := by
      by_contra hall; push Not at hall; exact hne (funext hall)
    obtain ⟨⟨b, c, i⟩, hi⟩ := hne'
    refine ⟨(b, c), ?_⟩
    have hh : stepanovHPoly h b c ≠ 0 := by
      intro hz
      have := congrArg (fun p => p.coeff i.val) hz
      rw [stepanovHPoly_coeff, dif_pos i.isLt, Polynomial.coeff_zero] at this
      exact hi this
    exact mul_ne_zero (mul_ne_zero hh (pow_ne_zero _ Polynomial.X_ne_zero)) (pow_ne_zero _ hg_ne)
  have hdeg_term : ∀ bc : Fin B × Fin d, term bc ≠ 0 →
      (term bc).natDegree =
        (stepanovHPoly h bc.1 bc.2).natDegree + bc.1.val +
          (d * (bc.1.val + 3 * bc.2.val) - bc.2.val) * L := by
    intro ⟨b, c⟩ ht
    have hh : stepanovHPoly h b c ≠ 0 := by
      intro hz; apply ht; simp [term, hz]
    have h1 : (stepanovHPoly h b c * X ^ (b.val * q)).natDegree =
        (stepanovHPoly h b c).natDegree + b.val * q := by
      rw [Polynomial.natDegree_mul hh (pow_ne_zero _ Polynomial.X_ne_zero),
        Polynomial.natDegree_X_pow]
    have h2 : (g ^ (c.val * L)).natDegree = c.val * L * (3 * d - 1) := by
      rw [Polynomial.natDegree_pow, hgdeg]
    have h3 : (term (b, c)).natDegree =
        (stepanovHPoly h b c).natDegree + b.val * q + c.val * L * (3 * d - 1) := by
      simp only [term]
      rw [Polynomial.natDegree_mul (mul_ne_zero hh (pow_ne_zero _ Polynomial.X_ne_zero))
        (pow_ne_zero _ hg_ne), h1, h2]
    rw [h3, hqL]
    have hle : c.val ≤ d * (b.val + 3 * c.val) := by nlinarith
    have hc3 : 1 ≤ 3 * d := by omega
    zify [hle, hc3]
    ring
  have hinj : ∀ bc₁ bc₂ : Fin B × Fin d, term bc₁ ≠ 0 → term bc₂ ≠ 0 →
      (term bc₁).natDegree = (term bc₂).natDegree → bc₁ = bc₂ := by
    intro ⟨b₁, c₁⟩ ⟨b₂, c₂⟩ h1 h2 heq
    rw [hdeg_term _ h1, hdeg_term _ h2] at heq
    dsimp only at heq
    have hd1 : (stepanovHPoly h b₁ c₁).natDegree + b₁.val < L := by
      have := stepanovHPoly_natDegree_lt hDh h b₁ c₁
      have := b₁.isLt; omega
    have hd2 : (stepanovHPoly h b₂ c₂).natDegree + b₂.val < L := by
      have := stepanovHPoly_natDegree_lt hDh h b₂ c₂
      have := b₂.isLt; omega
    set q₁ := d * (b₁.val + 3 * c₁.val) - c₁.val
    set q₂ := d * (b₂.val + 3 * c₂.val) - c₂.val
    have hqeq : q₁ = q₂ := by
      by_contra hqne
      rcases lt_or_gt_of_ne hqne with hlt | hgt
      · have : q₁ * L + L ≤ q₂ * L := by
          have : q₁ + 1 ≤ q₂ := hlt
          nlinarith
        omega
      · have : q₂ * L + L ≤ q₁ * L := by
          have : q₂ + 1 ≤ q₁ := hgt
          nlinarith
        omega
    have hle1 : c₁.val ≤ d * (b₁.val + 3 * c₁.val) := by nlinarith
    have hle2 : c₂.val ≤ d * (b₂.val + 3 * c₂.val) := by nlinarith
    have hqeqZ : (d : ℤ) * (b₁.val + 3 * c₁.val) - c₁.val =
        (d : ℤ) * (b₂.val + 3 * c₂.val) - c₂.val := by
      have := congrArg (Nat.cast (R := ℤ)) hqeq
      simpa [q₁, q₂, hle1, hle2] using this
    have hc_eq : c₁.val = c₂.val := by
      have hdvd : (d : ℤ) ∣ ((c₂.val : ℤ) - c₁.val) :=
        ⟨(b₂.val + 3 * c₂.val : ℤ) - (b₁.val + 3 * c₁.val), by linarith⟩
      obtain ⟨k, hk⟩ := hdvd
      have h1lt : (c₁.val : ℤ) < d := Int.ofNat_lt.mpr c₁.isLt
      have h2lt : (c₂.val : ℤ) < d := Int.ofNat_lt.mpr c₂.isLt
      have hk0 : k = 0 := by nlinarith
      have hdiff0 : (c₂.val : ℤ) - c₁.val = 0 := by rw [hk, hk0, mul_zero]
      omega
    have hb_eq : b₁.val = b₂.val := by nlinarith
    exact Prod.ext (Fin.ext hb_eq) (Fin.ext hc_eq)
  let S := Finset.univ.filter fun bc : Fin B × Fin d => term bc ≠ 0
  have hS : S.Nonempty := by
    obtain ⟨bc, hbc⟩ := hex
    exact ⟨bc, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbc⟩⟩
  obtain ⟨bc₀, hbc₀_mem, hbc₀_max⟩ := Finset.exists_max_image S (fun bc => (term bc).natDegree) hS
  have hbc₀_ne : term bc₀ ≠ 0 := (Finset.mem_filter.mp hbc₀_mem).2
  set D₀ := (term bc₀).natDegree
  intro hPhi0
  have hcoeff := congrArg (fun p => p.coeff D₀) hPhi0
  rw [hsum_eq, Polynomial.finsetSum_coeff, Polynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single bc₀] at hcoeff
  · exact Polynomial.leadingCoeff_ne_zero.mpr hbc₀_ne hcoeff
  · intro bc _ hne_bc
    by_cases h0 : term bc = 0
    · simp [h0]
    · have hle : (term bc).natDegree ≤ D₀ :=
        hbc₀_max bc (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩)
      have hne_deg : (term bc).natDegree ≠ D₀ := fun heq =>
        hne_bc (hinj bc bc₀ h0 hbc₀_ne heq)
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Degree bound on `stepanovRPoly h m`. -/
private lemma natDegree_stepanovRPoly_lt {K : Type*} [CommRing K] {B d D_h : ℕ}
    (hB : 0 < B) (hDh : 0 < D_h) (g : K[X]) (L : ℕ) (ζ : K)
    (h : Fin B × Fin d × Fin D_h → K) (m : ℕ) :
    (stepanovRPoly g L ζ h m).natDegree < D_h + B + m * g.natDegree := by
  by_cases hz : stepanovRPoly g L ζ h m = 0
  · rw [hz, Polynomial.natDegree_zero]; omega
  · refine lt_of_le_of_lt (Polynomial.natDegree_sum_le _ _) ?_
    rw [Finset.fold_max_lt]
    refine ⟨by omega, fun b _ => ?_⟩
    refine lt_of_le_of_lt (Polynomial.natDegree_sum_le _ _) ?_
    rw [Finset.fold_max_lt]
    refine ⟨by omega, fun c _ => ?_⟩
    refine lt_of_le_of_lt Polynomial.natDegree_mul_le ?_
    have h1 : (X ^ b.val * Polynomial.C (ζ ^ c.val)).natDegree ≤ b.val := by
      refine Polynomial.natDegree_mul_le.trans ?_
      rw [Polynomial.natDegree_C, add_zero]
      exact Polynomial.natDegree_X_pow_le _
    have h2 : (∑ rv ∈ Finset.HasAntidiagonal.antidiagonal m,
        Polynomial.hasseDeriv rv.1 (stepanovHPoly h b c) * QClear g (c.val * L) m rv.2).natDegree ≤
        (D_h - 1) + m * g.natDegree := by
      refine (Polynomial.natDegree_sum_le _ _).trans ?_
      rw [Finset.fold_max_le]
      refine ⟨Nat.zero_le _, fun rv hrv => ?_⟩
      have hrv_sum : rv.1 + rv.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hrv
      refine Polynomial.natDegree_mul_le.trans ?_
      have ha : (Polynomial.hasseDeriv rv.1 (stepanovHPoly h b c)).natDegree ≤ D_h - 1 := by
        have := (Polynomial.natDegree_hasseDeriv_le (stepanovHPoly h b c) rv.1).trans (Nat.sub_le _ _)
        have := stepanovHPoly_natDegree_lt hDh h b c
        omega
      have hb : (QClear g (c.val * L) m rv.2).natDegree ≤ m * g.natDegree :=
        natDegree_QClear_le g (c.val * L) m rv.2 (by omega)
      exact Nat.add_le_add ha hb
    have hb_lt : b.val < B := b.isLt
    omega

/-- Evaluation bridge: at every `u₀ ∈ K` with `u₀ ^ q = u₀` and `(g.eval u₀) ^ L = ζ`,
`(g.eval u₀)^m * (hasseDeriv m Φ).eval u₀ = (stepanovRPoly g L ζ h m).eval u₀`! -/
private lemma eval_hasseDeriv_stepanovPhi_eq_RPoly {K : Type*} [Field K]
    (p t : ℕ) [Fact p.Prime] [CharP K p]
    {B d D_h : ℕ} (g : K[X]) (L : ℕ) (ζ : K) (h : Fin B × Fin d × Fin D_h → K)
    (m : ℕ) (hmL : m < L) (hmq : m < p ^ t)
    (u₀ : K) (huq : u₀ ^ (p ^ t) = u₀) (hgz : (g.eval u₀) ^ L = ζ) :
    (g.eval u₀) ^ m * (Polynomial.hasseDeriv m (stepanovPhi g (p ^ t) L h)).eval u₀ =
      (stepanovRPoly g L ζ h m).eval u₀ := by
  simp only [stepanovPhi, stepanovRPoly, map_sum, Polynomial.eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  have hrearr : stepanovHPoly h b c * X ^ (b.val * p ^ t) * g ^ (c.val * L) =
      (stepanovHPoly h b c * g ^ (c.val * L)) * X ^ (b.val * p ^ t) := by ring
  rw [hrearr, Polynomial.hasseDeriv_mul]
  rw [Finset.sum_eq_single (m, 0)]
  · rw [Polynomial.hasseDeriv_zero', Polynomial.hasseDeriv_mul, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X,
      show u₀ ^ (b.val * p ^ t) = (u₀ ^ (p ^ t)) ^ b.val by rw [pow_mul'], huq]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C]
    have hmul_comm : ∀ x : K, (g.eval u₀) ^ m * (x * u₀ ^ b.val) = u₀ ^ b.val * ((g.eval u₀) ^ m * x) := by
      intro x; ring
    rw [hmul_comm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun rv hrv => ?_
    have hrv_sum : rv.1 + rv.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hrv
    have hN : c.val * L = 0 ∨ m ≤ c.val * L := by
      rcases eq_or_ne c.val 0 with hc0 | hc0
      · left; simp [hc0]
      · right
        have : 1 ≤ c.val := Nat.pos_of_ne_zero hc0
        nlinarith
    have hclear := congrArg (Polynomial.eval u₀)
      (mul_hasseDeriv_pow_eq_pow_mul_QClear g (c.val * L) m rv.2 (by omega) hN)
    simp only [Polynomial.eval_mul, Polynomial.eval_pow] at hclear
    rw [show (g.eval u₀) ^ (c.val * L) = ((g.eval u₀) ^ L) ^ c.val by rw [pow_mul'], hgz] at hclear
    calc
      u₀ ^ b.val * ((g.eval u₀) ^ m *
          ((Polynomial.hasseDeriv rv.1 (stepanovHPoly h b c)).eval u₀ *
            (Polynomial.hasseDeriv rv.2 (g ^ (c.val * L))).eval u₀))
          = u₀ ^ b.val * ((Polynomial.hasseDeriv rv.1 (stepanovHPoly h b c)).eval u₀ *
              ((g.eval u₀) ^ m * (Polynomial.hasseDeriv rv.2 (g ^ (c.val * L))).eval u₀)) := by ring
      _ = u₀ ^ b.val * ((Polynomial.hasseDeriv rv.1 (stepanovHPoly h b c)).eval u₀ *
              (ζ ^ c.val * (QClear g (c.val * L) m rv.2).eval u₀)) := by rw [hclear]
      _ = u₀ ^ b.val * ζ ^ c.val *
              ((Polynomial.hasseDeriv rv.1 (stepanovHPoly h b c)).eval u₀ *
                (QClear g (c.val * L) m rv.2).eval u₀) := by ring
  · intro ab hab hne
    have hab_sum : ab.1 + ab.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    have hab2_pos : 0 < ab.2 := by
      by_contra h0; push Not at h0
      have h20 : ab.2 = 0 := Nat.eq_zero_of_le_zero h0
      exact hne (Prod.ext (by omega) h20)
    rw [hasseDeriv_X_pow_mul_char_pow p t b.val ab.2 hab2_pos (by omega), mul_zero]
  · intro hm; exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (add_zero m)) hm

/-- The linear map sending coefficient tuples `h` to all coefficients of `stepanovRPoly g L ζ h m`
for `m < M`. -/
private noncomputable def stepanovLinearMap {K : Type*} [CommRing K]
    (B d D_h M L : ℕ) (g : K[X]) (ζ : K) :
    (Fin B × Fin d × Fin D_h → K) →ₗ[K]
      (∀ m : Fin M, Fin (D_h + B + m.val * g.natDegree) → K) where
  toFun h m j := (stepanovRPoly g L ζ h m.val).coeff j.val
  map_add' h₁ h₂ := by
    ext m j
    have hH : ∀ b c, stepanovHPoly (h₁ + h₂) b c = stepanovHPoly h₁ b c + stepanovHPoly h₂ b c := by
      intro b c
      simp only [stepanovHPoly, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
    simp only [Pi.add_apply, stepanovRPoly, hH, map_add, add_mul, Finset.sum_add_distrib, mul_add,
      Polynomial.coeff_add]
  map_smul' a h := by
    ext m j
    have hH : ∀ b c, stepanovHPoly (a • h) b c = a • stepanovHPoly h b c := by
      intro b c
      simp only [stepanovHPoly, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, Polynomial.smul_eq_C_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, mul_assoc]
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, stepanovRPoly, hH, map_smul,
      smul_mul_assoc, ← Finset.smul_sum, mul_smul_comm, Polynomial.coeff_smul, smul_eq_mul]

/-- Isolated pure-`ℕ` parameter arithmetic for Stepanov's method (`L-014_S1` anti-heartbeat). -/
private lemma stepanov_params_arith (q d : ℕ) (hd : 2 ≤ d) (hdvd : d ∣ (q - 1))
    (hq_big : (32 * d ^ 5) ^ 2 ≤ q) :
    let L := (q - 1) / d
    let B := Nat.sqrt q
    let D_h := L / 2
    let C₂ := 4 * d ^ 2 + 12 * d ^ 4 + 4 * d
    let M := d * B - C₂
    q = d * L + 1 ∧ 0 < B ∧ 0 < D_h ∧ 0 < M ∧
      D_h + B < L ∧ M < L ∧ M < q ∧ 2 * C₂ ≤ d * B ∧
      M * D_h + M * B + M * M * (3 * d) < B * (d * D_h) := by
  intro L B D_h C₂ M
  have hd5_ge : 32 ≤ d ^ 5 := by
    have : 2 ^ 5 ≤ d ^ 5 := Nat.pow_le_pow_left hd 5
    omega
  have hq_ge1 : 1024 ≤ q := by
    have : 32 ^ 2 ≤ (32 * d ^ 5) ^ 2 := Nat.pow_le_pow_left (by nlinarith) 2
    omega
  have hqL : q = d * L + 1 := by
    have h1 : d * L = q - 1 := Nat.mul_div_cancel' hdvd
    omega
  have hB_ge : 32 * d ^ 5 ≤ B := by
    rw [Nat.le_sqrt]
    simpa [sq] using hq_big
  have hB_sq : B * B ≤ q := Nat.sqrt_le q
  have hB_pos : 0 < B := by omega
  have hd2_le : d ^ 2 ≤ d ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hd3_le : d ^ 3 ≤ d ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hd4_le : d ^ 4 ≤ d ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hd1_le : d ≤ d ^ 5 := Nat.le_self_pow (by norm_num) d
  have hC₂_le : C₂ ≤ 20 * d ^ 5 := by simp only [C₂]; omega
  have h2C₂ : 2 * C₂ ≤ d * B := by
    have h1 : 32 * d ^ 5 * d ≤ B * d := Nat.mul_le_mul_right d hB_ge
    have h2 : 40 * d ^ 5 ≤ 32 * d ^ 5 * d := by nlinarith
    linarith
  have hM_pos : 0 < M := by omega
  have hL_ge : 16 * d ^ 4 * B ≤ L := by
    have h1 : 32 * d ^ 5 * B ≤ B * B := Nat.mul_le_mul_right B hB_ge
    have h2 : d * (16 * d ^ 4 * B) + 1 ≤ d * L + 1 := by
      have : d * (16 * d ^ 4 * B) = 16 * d ^ 5 * B := by ring
      nlinarith
    exact Nat.le_of_mul_le_mul_left (by omega) (by omega : 0 < d)
  have hDh_pos : 0 < D_h := by
    have : 16 ≤ 16 * d ^ 4 * B := by
      have : 1 ≤ d ^ 4 := Nat.one_le_pow 4 d (by omega)
      nlinarith
    omega
  have hsmall : D_h + B < L := by
    have : 3 * B + 4 ≤ L := by
      have : 1 ≤ d ^ 4 := Nat.one_le_pow 4 d (by omega)
      nlinarith
    omega
  have hmL : M < L := by
    have h1 : M ≤ d * B := Nat.sub_le _ _
    have h2 : d * B < 16 * d ^ 4 * B := by
      have : d < 16 * d ^ 4 := by
        have : d ≤ d ^ 4 := Nat.le_self_pow (by norm_num) d
        omega
      exact Nat.mul_lt_mul_of_pos_right this hB_pos
    omega
  have hmq : M < q := by nlinarith
  have hdim : M * D_h + M * B + M * M * (3 * d) < B * (d * D_h) := by
    have hdom : B * (d * D_h) = M * D_h + C₂ * D_h := by
      have hMB : M + C₂ = d * B := Nat.sub_add_cancel (by omega)
      calc
        B * (d * D_h) = (d * B) * D_h := by ring
        _ = (M + C₂) * D_h := by rw [hMB]
        _ = M * D_h + C₂ * D_h := by ring
    rw [hdom]
    have hM_le : M ≤ d * B := Nat.sub_le _ _
    have hMB : M * B ≤ d * (B * B) := by
      have := Nat.mul_le_mul_right B hM_le
      linarith
    have hMM : M * M * (3 * d) ≤ 3 * d ^ 3 * (B * B) := by
      have h1 : M * M ≤ (d * B) * (d * B) := Nat.mul_le_mul hM_le hM_le
      have h2 : (d * B) * (d * B) * (3 * d) = 3 * d ^ 3 * (B * B) := by ring
      have := Nat.mul_le_mul_right (3 * d) h1
      omega
    have h2dDh : B * B ≤ 2 * d * D_h + 2 * d + 1 := by
      have hL2 : L ≤ 2 * D_h + 1 := by omega
      have : d * L ≤ d * (2 * D_h + 1) := Nat.mul_le_mul_left d hL2
      linarith
    have hfac : C₂ * D_h = (2 * d + 6 * d ^ 3 + 2) * (2 * d * D_h) := by
      simp only [C₂]; ring
    have hB_big_prod : (2 * d + 6 * d ^ 3 + 2) * (2 * d + 1) < B * B := by
      have h1 : 2 * d + 6 * d ^ 3 + 2 ≤ 10 * d ^ 5 := by omega
      have h2 : 2 * d + 1 ≤ 3 * d ^ 5 := by omega
      have h3 : (10 * d ^ 5) * (3 * d ^ 5) < (32 * d ^ 5) * (32 * d ^ 5) := by
        have hpos : 0 < d ^ 5 := by omega
        nlinarith
      have h4 : (2 * d + 6 * d ^ 3 + 2) * (2 * d + 1) ≤ (10 * d ^ 5) * (3 * d ^ 5) :=
        Nat.mul_le_mul h1 h2
      have h5 : (32 * d ^ 5) * (32 * d ^ 5) ≤ B * B := Nat.mul_le_mul hB_ge hB_ge
      omega
    have hstep1 : (2 * d + 6 * d ^ 3 + 2) * (B * B) ≤
        C₂ * D_h + (2 * d + 6 * d ^ 3 + 2) * (2 * d + 1) := by
      rw [hfac]
      have := Nat.mul_le_mul_left (2 * d + 6 * d ^ 3 + 2) h2dDh
      linarith
    have hstep2 : (d + 3 * d ^ 3) * (B * B) + B * B < (2 * d + 6 * d ^ 3 + 2) * (B * B) := by
      have : (d + 3 * d ^ 3 + 1) < (2 * d + 6 * d ^ 3 + 2) := by omega
      have hB2_pos : 0 < B * B := Nat.mul_pos hB_pos hB_pos
      have := Nat.mul_lt_mul_of_pos_right this hB2_pos
      linarith
    have hsum_eq : (d + 3 * d ^ 3) * (B * B) = d * (B * B) + 3 * d ^ 3 * (B * B) := by ring
    omega
  exact ⟨hqL, hB_pos, hDh_pos, hM_pos, hsmall, hmL, hmq, h2C₂, hdim⟩

/-- Isolated `ℝ` conversion for Stepanov's root-count bound (`L-014_S1` anti-heartbeat). -/
private lemma stepanov_real_bound (q d B C₂ M S_card : ℕ) (hd : 2 ≤ d) (hB : 0 < B)
    (hq_lt : q < (B + 1) * (B + 1)) (h2C₂ : 2 * C₂ ≤ d * B) (hM_eq : M = d * B - C₂)
    (hC₂_le : C₂ ≤ 20 * d ^ 4) (hcard : M * S_card ≤ (B + 3 * d) * q) :
    (S_card : ℝ) ≤ (q : ℝ) / (d : ℝ) + (40 * (d : ℝ) ^ 4) * Real.sqrt (q : ℝ) := by
  have h2B_le : 2 * B ≤ d * B := Nat.mul_le_mul_right B hd
  have hB_le_M : B ≤ M := by omega
  have hM_pos : 0 < M := by omega
  have hd_posR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hM_posR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
  have hq_nn : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hsqrt_le : Real.sqrt (q : ℝ) ≤ (B : ℝ) + 1 := by
    rw [Real.sqrt_le_left (by positivity)]
    have : (q : ℝ) ≤ ((B : ℝ) + 1) * ((B : ℝ) + 1) := by exact_mod_cast hq_lt.le
    linarith [sq ((B : ℝ) + 1)]
  have hM_eqR : (M : ℝ) = (d : ℝ) * (B : ℝ) - (C₂ : ℝ) := by
    have : M + C₂ = d * B := by omega
    have hR : (M : ℝ) + (C₂ : ℝ) = (d : ℝ) * (B : ℝ) := by exact_mod_cast this
    linarith
  have hM_geB : (B : ℝ) ≤ (M : ℝ) := by exact_mod_cast hB_le_M
  have hcardR : (M : ℝ) * (S_card : ℝ) ≤ ((B : ℝ) + 3 * (d : ℝ)) * (q : ℝ) := by
    exact_mod_cast hcard
  have hnum : (M : ℝ) * ((S_card : ℝ) - (q : ℝ) / (d : ℝ)) ≤
      (3 * (d : ℝ) + (C₂ : ℝ) / (d : ℝ)) * (q : ℝ) := by
    have hsub : (M : ℝ) * ((q : ℝ) / (d : ℝ)) =
        (B : ℝ) * (q : ℝ) - (C₂ : ℝ) / (d : ℝ) * (q : ℝ) := by
      rw [hM_eqR]; field_simp [hd_posR.ne']
    linarith
  have hq_le_B2 : (q : ℝ) ≤ 2 * (B : ℝ) * Real.sqrt (q : ℝ) := by
    have hB1 : (B : ℝ) + 1 ≤ 2 * (B : ℝ) := by
      have : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
      linarith
    calc
      (q : ℝ) = Real.sqrt (q : ℝ) * Real.sqrt (q : ℝ) := (Real.mul_self_sqrt hq_nn).symm
      _ ≤ ((B : ℝ) + 1) * Real.sqrt (q : ℝ) :=
        mul_le_mul_of_nonneg_right hsqrt_le (Real.sqrt_nonneg _)
      _ ≤ (2 * (B : ℝ)) * Real.sqrt (q : ℝ) :=
        mul_le_mul_of_nonneg_right hB1 (Real.sqrt_nonneg _)
  have hcoef : 3 * (d : ℝ) + (C₂ : ℝ) / (d : ℝ) ≤ 20 * (d : ℝ) ^ 4 := by
    have hd1 : (d : ℝ) ≤ (d : ℝ) ^ 4 := by exact_mod_cast Nat.le_self_pow (by norm_num) d
    have hC₂R : (C₂ : ℝ) ≤ 20 * (d : ℝ) ^ 4 := by exact_mod_cast hC₂_le
    have hdiv : (C₂ : ℝ) / (d : ℝ) ≤ 10 * (d : ℝ) ^ 4 := by
      rw [div_le_iff₀ hd_posR]
      have hd2R : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      nlinarith [pow_nonneg hd_posR.le 4]
    linarith
  have hfinal : (S_card : ℝ) - (q : ℝ) / (d : ℝ) ≤ (40 * (d : ℝ) ^ 4) * Real.sqrt (q : ℝ) := by
    rw [← mul_le_mul_iff_right₀ hM_posR]
    calc
      (M : ℝ) * ((S_card : ℝ) - (q : ℝ) / (d : ℝ))
          ≤ (3 * (d : ℝ) + (C₂ : ℝ) / (d : ℝ)) * (q : ℝ) := hnum
      _ ≤ (20 * (d : ℝ) ^ 4) * (q : ℝ) :=
        mul_le_mul_of_nonneg_right hcoef hq_nn
      _ ≤ (20 * (d : ℝ) ^ 4) * (2 * (B : ℝ) * Real.sqrt (q : ℝ)) :=
        mul_le_mul_of_nonneg_left hq_le_B2 (by positivity)
      _ = (B : ℝ) * ((40 * (d : ℝ) ^ 4) * Real.sqrt (q : ℝ)) := by ring
      _ ≤ (M : ℝ) * ((40 * (d : ℝ) ^ 4) * Real.sqrt (q : ℝ)) :=
        mul_le_mul_of_nonneg_right hM_geB (by positivity)
  linarith

/-- **Stepanov–Schmidt Root Count Upper Bound** for `y^d = g(u)` over `K = F_{p^t}`. -/
theorem stepanov_root_count_le {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (p t : ℕ) [Fact p.Prime] [CharP K p] (hq : Fintype.card K = p ^ t)
    (d : ℕ) (hd : 2 ≤ d) (hdvd : d ∣ (p ^ t - 1))
    (g : K[X]) (hgdeg : g.natDegree = 3 * d - 1)
    (ζ : K) (hq_big : (32 * d ^ 5) ^ 2 ≤ p ^ t) :
    ((Finset.univ.filter fun u : K =>
        g.eval u ≠ 0 ∧ (g.eval u) ^ ((p ^ t - 1) / d) = ζ).card : ℝ) ≤
      (p ^ t : ℝ) / (d : ℝ) + (40 * (d : ℝ) ^ 4) * Real.sqrt (p ^ t : ℝ) := by
  set q := p ^ t
  set L := (q - 1) / d
  set B := Nat.sqrt q
  set D_h := L / 2
  set C₂ := 4 * d ^ 2 + 12 * d ^ 4 + 4 * d
  set M := d * B - C₂
  obtain ⟨hqL, hB_pos, hDh_pos, hM_pos, hsmall, hmL, hmq, h2C₂, hdim⟩ :=
    stepanov_params_arith q d hd hdvd hq_big
  have hfinrank_lt :
      Module.finrank K (∀ m : Fin M, Fin (D_h + B + m.val * g.natDegree) → K) <
        Module.finrank K (Fin B × Fin d × Fin D_h → K) := by
    simp only [Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin, smul_eq_mul, mul_one]
    have hsum_le :
        (∑ x : Fin M, (D_h + B + x.val * g.natDegree)) ≤
          M * D_h + M * B + M * M * (3 * d) := by
      calc
        ∑ x : Fin M, (D_h + B + x.val * g.natDegree)
            ≤ ∑ _x : Fin M, (D_h + B + M * (3 * d)) := by
              refine Finset.sum_le_sum fun x _ => ?_
              have hx : x.val ≤ M := x.isLt.le
              have hg : g.natDegree ≤ 3 * d := by omega
              have := Nat.mul_le_mul hx hg
              omega
        _ = M * (D_h + B + M * (3 * d)) := by simp
        _ = M * D_h + M * B + M * M * (3 * d) := by ring
    exact lt_of_le_of_lt hsum_le hdim
  -- Kernel of linear map with `finrank codomain < finrank domain` is nontrivial!
  have hker_ne : LinearMap.ker (stepanovLinearMap B d D_h M L g ζ) ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective (stepanovLinearMap B d D_h M L g ζ) :=
      LinearMap.ker_eq_bot.mp hbot
    have hle : Module.finrank K (Fin B × Fin d × Fin D_h → K) ≤
        Module.finrank K (∀ m : Fin M, Fin (D_h + B + m.val * g.natDegree) → K) := by
      rw [← LinearMap.finrank_range_of_inj hinj]
      exact Submodule.finrank_le _
    omega
  obtain ⟨h, hh_ker, hh_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
  have hR_zero : ∀ m < M, stepanovRPoly g L ζ h m = 0 := by
    intro m hm
    ext j
    rw [Polynomial.coeff_zero]
    by_cases hj : j < D_h + B + m * g.natDegree
    · have h0 := congrFun (congrFun (LinearMap.mem_ker.mp hh_ker) ⟨m, hm⟩) ⟨j, hj⟩
      simpa [stepanovLinearMap] using h0
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_lt_of_le (natDegree_stepanovRPoly_lt hB_pos hDh_pos g L ζ h m) (by omega))
  set Φ := stepanovPhi g q L h
  have hPhi_ne : Φ ≠ 0 := stepanovPhi_ne_zero hd hDh_pos g hgdeg q L hqL hsmall h hh_ne
  set S := Finset.univ.filter fun u : K => g.eval u ≠ 0 ∧ (g.eval u) ^ L = ζ
  have hmult : ∀ u₀ ∈ S, M ≤ Φ.rootMultiplicity u₀ := by
    intro u₀ hu₀
    have ⟨hg_u, hgz_u⟩ := (Finset.mem_filter.mp hu₀).2
    refine le_rootMultiplicity_of_hasseDeriv_eval_zero Φ hPhi_ne u₀ M fun m hm => ?_
    have huq : u₀ ^ q = u₀ := by
      have := FiniteField.pow_card u₀
      rwa [hq] at this
    have hev := eval_hasseDeriv_stepanovPhi_eq_RPoly p t g L ζ h m
      (hm.trans hmL) (hm.trans hmq) u₀ huq hgz_u
    rw [hR_zero m hm, Polynomial.eval_zero] at hev
    exact (mul_eq_zero.mp hev).resolve_left (pow_ne_zero m hg_u)
  have hcard_le_deg : M * S.card ≤ Φ.natDegree := by
    have h1 : M * S.card ≤ ∑ u ∈ S, Φ.rootMultiplicity u := by
      calc
        M * S.card = ∑ _u ∈ S, M := by simp [mul_comm]
        _ ≤ ∑ u ∈ S, Φ.rootMultiplicity u := Finset.sum_le_sum hmult
    have h2 : ∑ u ∈ S, Φ.rootMultiplicity u ≤ Φ.roots.card := by
      have hcount : ∀ u ∈ S, Φ.rootMultiplicity u = Multiset.count u Φ.roots := fun u _ =>
        (Polynomial.count_roots Φ).symm
      rw [Finset.sum_congr rfl hcount]
      have hsub : (S.val.bind fun u => Multiset.replicate (Multiset.count u Φ.roots) u) ≤ Φ.roots := by
        rw [Multiset.le_iff_count]
        intro a
        rw [Multiset.count_bind]
        by_cases ha : a ∈ S
        · change (∑ b ∈ S, Multiset.count a (Multiset.replicate (Multiset.count b Φ.roots) b)) ≤
            Multiset.count a Φ.roots
          rw [Finset.sum_eq_single a]
          · simp
          · intro b _ hba; simp [Multiset.count_replicate, hba]
          · intro h; exact absurd ha h
        · change (∑ b ∈ S, Multiset.count a (Multiset.replicate (Multiset.count b Φ.roots) b)) ≤
            Multiset.count a Φ.roots
          rw [Finset.sum_eq_zero]
          · exact Nat.zero_le _
          · intro b hb
            have hba : b ≠ a := fun heq => ha (heq ▸ hb)
            simp [Multiset.count_replicate, hba]
      calc
        ∑ u ∈ S, Multiset.count u Φ.roots
            = (S.val.bind fun u => Multiset.replicate (Multiset.count u Φ.roots) u).card := by
              simp [Multiset.card_bind]
        _ ≤ Φ.roots.card := Multiset.card_le_card hsub
    exact h1.trans (h2.trans (Polynomial.card_roots' Φ))
  have hPhi_deg : Φ.natDegree ≤ (B + 3 * d) * q := by
    refine (Polynomial.natDegree_sum_le _ _).trans ?_
    rw [Finset.fold_max_le]
    refine ⟨Nat.zero_le _, fun b _ => ?_⟩
    refine (Polynomial.natDegree_sum_le _ _).trans ?_
    rw [Finset.fold_max_le]
    refine ⟨Nat.zero_le _, fun c _ => ?_⟩
    refine Polynomial.natDegree_mul_le.trans ?_
    refine (Nat.add_le_add Polynomial.natDegree_mul_le Polynomial.natDegree_pow_le).trans ?_
    have h1 : (stepanovHPoly h b c).natDegree ≤ D_h :=
      (stepanovHPoly_natDegree_lt hDh_pos h b c).le
    have h2 : (X ^ (b.val * q) : K[X]).natDegree = b.val * q := Polynomial.natDegree_X_pow _
    rw [h2, hgdeg]
    have hb_le : b.val + 1 ≤ B := b.isLt
    have hc_le : c.val ≤ d := c.isLt.le
    have hdl : d * L ≤ q := by
      have : d * L + 1 = q := hqL.symm
      omega
    have hDh_le_q : D_h ≤ q := by
      have h1' : D_h ≤ L := Nat.div_le_self L 2
      have h2' : L ≤ d * L := Nat.le_mul_of_pos_left L (by omega)
      omega
    have hcL_le : c.val * L * (3 * d - 1) ≤ (3 * d - 1) * q := by
      have hcl : c.val * L ≤ d * L := Nat.mul_le_mul_right L hc_le
      have hclq : c.val * L ≤ q := hcl.trans hdl
      have := Nat.mul_le_mul_right (3 * d - 1) hclq
      linarith
    have hb_mul : b.val * q + q ≤ B * q := by
      have := Nat.mul_le_mul_right q hb_le
      linarith
    have h3d : (3 * d - 1) * q ≤ 3 * d * q := Nat.mul_le_mul_right q (Nat.sub_le _ _)
    linarith
  have hC₂_le : C₂ ≤ 20 * d ^ 4 := by
    have hd1 : d ≤ d ^ 4 := Nat.le_self_pow (by norm_num) d
    have hd2 : d ^ 2 ≤ d ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    simp only [C₂]; omega
  simpa [q, Nat.cast_pow] using
    stepanov_real_bound q d B C₂ M S.card hd hB_pos (Nat.lt_succ_sqrt q) h2C₂ rfl hC₂_le
      (hcard_le_deg.trans hPhi_deg)

-- =============================================================================
-- SECTION 2B: CHARACTER-SUM BOUND FROM STEPANOV ROOT-COUNT UPPER BOUND
-- =============================================================================

/-- Extend a multiplicative character `χ : Fˣ →* ℂˣ` by zero at `0 : F`. -/
noncomputable def charZero {F : Type*} [Field F] [DecidableEq F]
    (χ : Fˣ →* ℂˣ) : F →*₀ ℂ where
  toFun x := if hx : x = 0 then 0 else (χ (Units.mk0 x hx) : ℂ)
  map_zero' := by simp
  map_one' := by simp
  map_mul' a b := by
    by_cases ha : a = 0
    · simp [ha]
    · by_cases hb : b = 0
      · simp [hb]
      · have hab : a * b ≠ 0 := mul_ne_zero ha hb
        simp only [dif_neg ha, dif_neg hb, dif_neg hab]
        have hu : Units.mk0 (a * b) hab = Units.mk0 a ha * Units.mk0 b hb := by
          ext; rfl
        rw [hu, map_mul, Units.val_mul]

lemma charZero_apply_unit {F : Type*} [Field F] [DecidableEq F]
    (χ : Fˣ →* ℂˣ) (u : Fˣ) : charZero χ (u : F) = (χ u : ℂ) := by
  simp only [charZero, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, dif_neg u.ne_zero]
  have : Units.mk0 (u : F) u.ne_zero = u := by ext; rfl
  rw [this]

lemma sum_char_units_eq_zero {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (χ : Fˣ →* ℂˣ) (hne : ∃ u₀ : Fˣ, χ u₀ ≠ 1) :
    ∑ u : Fˣ, (χ u : ℂ) = 0 := by
  obtain ⟨u₀, hu₀⟩ := hne
  have hshift : (χ u₀ : ℂ) * ∑ u : Fˣ, (χ u : ℂ) = ∑ u : Fˣ, (χ u : ℂ) := by
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft u₀) _ _ fun u => ?_
    simp [map_mul]
  have hne1 : (χ u₀ : ℂ) - 1 ≠ 0 := by
    intro h0
    apply hu₀
    ext
    exact sub_eq_zero.mp h0
  have hprod : ((χ u₀ : ℂ) - 1) * ∑ u : Fˣ, (χ u : ℂ) = 0 := by linear_combination hshift
  exact (mul_eq_zero.mp hprod).resolve_left hne1

lemma sum_charZero_eq_zero {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (χ : Fˣ →* ℂˣ) (hne : ∃ u₀ : Fˣ, χ u₀ ≠ 1) :
    ∑ x : F, charZero χ x = 0 := by
  have hsplit : ∑ x : F, charZero χ x =
      charZero χ 0 + ∑ x ∈ Finset.univ.erase (0 : F), charZero χ x :=
    (Finset.add_sum_erase Finset.univ (fun x => charZero χ x) (Finset.mem_univ 0)).symm
  rw [hsplit, map_zero, zero_add]
  have hbij : ∑ x ∈ Finset.univ.erase (0 : F), charZero χ x = ∑ u : Fˣ, (χ u : ℂ) := by
    refine (Finset.sum_nbij (fun u : Fˣ => (u : F)) ?_ ?_ ?_ ?_).symm
    · intro u _
      exact Finset.mem_erase.mpr ⟨u.ne_zero, Finset.mem_univ _⟩
    · intro u₁ _ u₂ _ heq
      exact Units.ext heq
    · intro x hx
      have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
      exact ⟨Units.mk0 x hx0, Finset.mem_univ _, rfl⟩
    · intro u _
      exact (charZero_apply_unit χ u).symm
  rw [hbij]
  exact sum_char_units_eq_zero χ hne

/-- Upper-bound-only character-sum bound derived from `stepanov_root_count_le`. -/
theorem stepanov_char_sum_bound {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (p t : ℕ) [Fact p.Prime] [CharP K p] (hq : Fintype.card K = p ^ t)
    (d : ℕ) (hd : 2 ≤ d) (hdvd : d ∣ (p ^ t - 1))
    (g : K[X]) (hgdeg : g.natDegree = 3 * d - 1)
    (ψ : Kˣ →* ℂˣ) (hψ_ne : ∃ x : Kˣ, ψ x ≠ 1) (hψ_pow : ∀ x : Kˣ, (ψ x : ℂ) ^ d = 1)
    (hq_big : (32 * d ^ 5) ^ 2 ≤ p ^ t) :
    ‖∑ u : K, charZero ψ (g.eval u)‖ ≤
      (40 * (d : ℝ) ^ 6 + 3 * (d : ℝ) ^ 2) * Real.sqrt (p ^ t : ℝ) := by
  set q := p ^ t
  set L := (q - 1) / d
  have hq_ge : 1024 ≤ q := by
    have h1 : 32 ≤ d ^ 5 := by
      have : 2 ^ 5 ≤ d ^ 5 := Nat.pow_le_pow_left hd 5
      omega
    have h2 : 32 ≤ 32 * d ^ 5 := Nat.le_mul_of_pos_right 32 (by omega)
    have h3 : 32 ^ 2 ≤ (32 * d ^ 5) ^ 2 := Nat.pow_le_pow_left h2 2
    omega
  have hqL : d * L = q - 1 := Nat.mul_div_cancel' hdvd
  have hL_pos : 0 < L := by
    refine Nat.pos_of_ne_zero fun hL0 => ?_
    have hq0 : 0 = q - 1 := by simpa [hL0] using hqL
    have hq_pos : 1 ≤ q - 1 := by omega
    omega
  obtain ⟨gK, hgK⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hcard_units : Fintype.card Kˣ = q - 1 := by
    rw [Fintype.card_units, hq]
  have hord : orderOf gK = q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgK, Nat.card_eq_fintype_card, hcard_units]
  have hgen_pow : ∀ x : Kˣ, ∃ a : ℕ, gK ^ a = x := by
    intro x
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp (hgK x)
    have hfin : IsOfFinOrder gK := isOfFinOrder_of_finite gK
    refine ⟨(z % (orderOf gK : ℤ)).toNat, ?_⟩
    have hpos : (0 : ℤ) < (orderOf gK : ℤ) := by omega
    have hmod_nn : 0 ≤ z % (orderOf gK : ℤ) := Int.emod_nonneg z hpos.ne'
    have hpow_eq : gK ^ ((z % (orderOf gK : ℤ)).toNat : ℤ) = gK ^ z := by
      rw [Int.toNat_of_nonneg hmod_nn, zpow_mod_orderOf]
    rw [← zpow_natCast, hpow_eq, hz]
  set ζ₀ : K := (gK : K) ^ L
  set ω : ℂ := (ψ gK : ℂ)
  have hω_pow : ω ^ d = 1 := hψ_pow gK
  have hω_ne : ω ≠ 1 := by
    intro h1
    have hψg : ψ gK = 1 := Units.ext h1
    obtain ⟨x₀, hx₀⟩ := hψ_ne
    obtain ⟨a, rfl⟩ := hgen_pow x₀
    apply hx₀
    rw [map_pow, hψg, one_pow]
  have hω_norm : ‖ω‖ = 1 := by
    have h1 : ‖ω‖ ^ d = 1 := by rw [← norm_pow, hω_pow, norm_one]
    have hnn : 0 ≤ ‖ω‖ := norm_nonneg ω
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : ‖ω‖ ^ d < 1 ^ d := pow_lt_pow_left₀ hlt hnn (by omega)
      simp at this; linarith
    · have : 1 ^ d < ‖ω‖ ^ d := pow_lt_pow_left₀ hgt (by norm_num) (by omega)
      simp at this; linarith
  have hω_sum : ∑ j : Fin d, ω ^ j.val = 0 := by
    rw [Fin.sum_univ_eq_sum_range]
    have hgeom : (∑ j ∈ Finset.range d, ω ^ j) * (ω - 1) = ω ^ d - 1 := geom_sum_mul ω d
    rw [hω_pow, sub_self] at hgeom
    exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hω_ne)
  have hζ_inj : Function.Injective fun j : Fin d => ζ₀ ^ j.val := by
    intro i j hij
    suffices hle : ∀ a b : Fin d, a.val ≤ b.val → ζ₀ ^ a.val = ζ₀ ^ b.val → a = b by
      rcases le_total i.val j.val with h | h
      · exact hle i j h hij
      · exact (hle j i h hij.symm).symm
    intro a b hab heq
    have h1 : (gK : K) ^ (L * a.val) = (gK : K) ^ (L * b.val) := by
      simpa [ζ₀, ← pow_mul] using heq
    have h2 : (gK : K) ^ (L * a.val) * (gK : K) ^ (L * (b.val - a.val)) =
        (gK : K) ^ (L * a.val) * 1 := by
      rw [← pow_add, ← mul_add, Nat.add_sub_of_le hab, h1, mul_one]
    have h3 : (gK : K) ^ (L * (b.val - a.val)) = 1 :=
      mul_left_cancel₀ (pow_ne_zero _ gK.ne_zero) h2
    have h4 : gK ^ (L * (b.val - a.val)) = 1 := by
      ext; simpa using h3
    have hdvd_ord : orderOf gK ∣ L * (b.val - a.val) := orderOf_dvd_of_pow_eq_one h4
    rw [hord, ← hqL] at hdvd_ord
    have hdvd_sub : d ∣ (b.val - a.val) := by
      rw [mul_comm L] at hdvd_ord
      exact (Nat.mul_dvd_mul_iff_right hL_pos).mp hdvd_ord
    have hlt : b.val - a.val < d := by omega
    have h0 : b.val - a.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd_sub hlt
    exact Fin.ext (by omega)
  let S : Fin d → Finset K := fun j =>
    Finset.univ.filter fun u : K => g.eval u ≠ 0 ∧ (g.eval u) ^ L = ζ₀ ^ j.val
  have hdisj : Set.PairwiseDisjoint ((Finset.univ : Finset (Fin d)) : Set (Fin d)) S := by
    intro i _ j _ hij
    change Disjoint (S i) (S j)
    rw [Finset.disjoint_left]
    intro u hui huj
    have h1 := (Finset.mem_filter.mp hui).2.2
    have h2 := (Finset.mem_filter.mp huj).2.2
    exact hij (hζ_inj (h1.symm.trans h2))
  have hcover : ∀ u : K, g.eval u ≠ 0 →
      ∃ j : Fin d, u ∈ S j ∧ charZero ψ (g.eval u) = ω ^ j.val := by
    intro u hu
    obtain ⟨a, ha⟩ := hgen_pow (Units.mk0 (g.eval u) hu)
    have hgu_eq : g.eval u = (gK : K) ^ a := by
      have := congrArg (fun x : Kˣ => (x : K)) ha.symm
      simpa using this
    let j₀ : Fin d := ⟨a % d, Nat.mod_lt a (by omega)⟩
    have hgK_pow : (gK : K) ^ (d * L) = 1 := by
      rw [hqL, ← hord, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
    have hpowL : (g.eval u) ^ L = ζ₀ ^ j₀.val := by
      rw [hgu_eq, ← pow_mul]
      have hdiv : a * L = (d * L) * (a / d) + L * (a % d) := by
        have hda := Nat.div_add_mod a d
        calc
          a * L = (d * (a / d) + a % d) * L := by rw [hda]
          _ = (d * L) * (a / d) + L * (a % d) := by ring
      rw [hdiv, pow_add, pow_mul, hgK_pow, one_pow, one_mul, pow_mul]
    have hch : charZero ψ (g.eval u) = ω ^ j₀.val := by
      have hu_eq : charZero ψ (g.eval u) = (ψ (Units.mk0 (g.eval u) hu) : ℂ) := by
        simp [charZero, dif_neg hu]
      rw [hu_eq, ← ha, map_pow, Units.val_pow_eq_pow_val]
      have hda := Nat.div_add_mod a d
      calc
        ω ^ a = ω ^ (d * (a / d) + a % d) := by rw [hda]
        _ = (ω ^ d) ^ (a / d) * ω ^ (a % d) := by rw [pow_add, pow_mul]
        _ = ω ^ j₀.val := by rw [hω_pow, one_pow, one_mul]
    exact ⟨j₀, Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu, hpowL⟩, hch⟩
  have hbiUnion : (Finset.univ.biUnion S) = Finset.univ.filter (fun u : K => g.eval u ≠ 0) := by
    ext u
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨j, hj⟩
      exact (Finset.mem_filter.mp hj).2.1
    · intro hu
      obtain ⟨j, hj, _⟩ := hcover u hu
      exact ⟨j, hj⟩
  have hsum_char : ∑ u : K, charZero ψ (g.eval u) =
      ∑ j : Fin d, ((S j).card : ℂ) * ω ^ j.val := by
    have hnz : ∑ u : K, charZero ψ (g.eval u) =
        ∑ u ∈ Finset.univ.filter (fun u : K => g.eval u ≠ 0), charZero ψ (g.eval u) := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) ?_
      intro u _ hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hu
      rw [hu, map_zero]
    rw [hnz, ← hbiUnion, Finset.sum_biUnion (fun i hi j hj hij => hdisj hi hj hij)]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hconst : ∀ u ∈ S j, charZero ψ (g.eval u) = ω ^ j.val := by
      intro u hu
      have hgu := (Finset.mem_filter.mp hu).2.1
      have hpow := (Finset.mem_filter.mp hu).2.2
      obtain ⟨j', hj', hch⟩ := hcover u hgu
      have hpow' := (Finset.mem_filter.mp hj').2.2
      have hjj : j' = j := hζ_inj (hpow'.symm.trans hpow)
      rw [hch, hjj]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hsum_card_ge : q - (3 * d - 1) ≤ ∑ j : Fin d, (S j).card := by
    have htot : (Finset.univ.biUnion S).card = ∑ j : Fin d, (S j).card :=
      Finset.card_biUnion (fun i hi j hj hij => hdisj hi hj hij)
    rw [hbiUnion] at htot
    have hpart :
        (Finset.univ.filter (fun u : K => g.eval u ≠ 0)).card +
          (Finset.univ.filter (fun u : K => g.eval u = 0)).card = q := by
      have hd_part : Disjoint (Finset.univ.filter (fun u : K => g.eval u ≠ 0))
          (Finset.univ.filter (fun u : K => g.eval u = 0)) := by
        rw [Finset.disjoint_left]
        intro u h1 h2
        exact (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
      have hunion : (Finset.univ.filter (fun u : K => g.eval u ≠ 0)) ∪
          (Finset.univ.filter (fun u : K => g.eval u = 0)) = Finset.univ := by
        ext u
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact ne_or_eq (g.eval u) 0
      rw [← Finset.card_union_of_disjoint hd_part, hunion, Finset.card_univ, hq]
    have hg_ne : g ≠ 0 := by
      intro h0; rw [h0, Polynomial.natDegree_zero] at hgdeg; omega
    have hroots : (Finset.univ.filter (fun u : K => g.eval u = 0)).card ≤ 3 * d - 1 := by
      have hsub : Finset.univ.filter (fun u : K => g.eval u = 0) ⊆ g.roots.toFinset := by
        intro u hu
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hg_ne]
        exact (Finset.mem_filter.mp hu).2
      calc
        (Finset.univ.filter (fun u : K => g.eval u = 0)).card
            ≤ g.roots.toFinset.card := Finset.card_le_card hsub
        _ ≤ g.roots.card := Multiset.toFinset_card_le _
        _ ≤ g.natDegree := Polynomial.card_roots' g
        _ = 3 * d - 1 := hgdeg
    omega
  set E : ℝ := (40 * (d : ℝ) ^ 4) * Real.sqrt (q : ℝ)
  have hE_nn : 0 ≤ E := by positivity
  let Δ : Fin d → ℝ := fun j => ((S j).card : ℝ) - (q : ℝ) / (d : ℝ)
  have hΔ_le : ∀ j : Fin d, Δ j ≤ E := by
    intro j
    have hbound := stepanov_root_count_le p t hq d hd hdvd g hgdeg (ζ₀ ^ j.val) hq_big
    have hbound' : ((S j).card : ℝ) ≤ (q : ℝ) / (d : ℝ) + E := by
      simpa [S, L, q, E, Nat.cast_pow] using hbound
    linarith
  have hd_posR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hΔ_sum_ge : -(3 * (d : ℝ)) ≤ ∑ j : Fin d, Δ j := by
    have hsum_eq : ∑ j : Fin d, Δ j = (∑ j : Fin d, ((S j).card : ℝ)) - (q : ℝ) := by
      simp only [Δ, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      have : (d : ℝ) * ((q : ℝ) / (d : ℝ)) = (q : ℝ) := mul_div_cancel₀ _ hd_posR.ne'
      linarith
    rw [hsum_eq]
    have hgeR : (q : ℝ) - (3 * (d : ℝ) - 1) ≤ ∑ j : Fin d, ((S j).card : ℝ) := by
      have h1 : 3 * d - 1 ≤ q := by
        have : 3 * d ≤ 32 * d ^ 5 := by
          have : d ≤ d ^ 5 := Nat.le_self_pow (by norm_num) d
          omega
        have : 32 * d ^ 5 ≤ (32 * d ^ 5) ^ 2 := Nat.le_self_pow (by norm_num) _
        omega
      have h2 : (q - (3 * d - 1) : ℕ) + (3 * d - 1) = q := Nat.sub_add_cancel h1
      have h3 : ((q - (3 * d - 1) : ℕ) : ℝ) ≤ ∑ j : Fin d, ((S j).card : ℝ) := by
        exact_mod_cast hsum_card_ge
      have h4 : ((3 * d - 1 : ℕ) : ℝ) = 3 * (d : ℝ) - 1 := by
        have : (3 * d - 1 : ℕ) + 1 = 3 * d := by omega
        have hR : ((3 * d - 1 : ℕ) : ℝ) + 1 = 3 * (d : ℝ) := by exact_mod_cast this
        linarith
      have h5 : ((q - (3 * d - 1) : ℕ) : ℝ) + ((3 * d - 1 : ℕ) : ℝ) = (q : ℝ) := by
        exact_mod_cast h2
      linarith
    linarith
  have hΔ_abs : ∀ j₀ : Fin d, |Δ j₀| ≤ 3 * (d : ℝ) + (d : ℝ) * E := by
    intro j₀
    rw [abs_le]
    constructor
    · have hsplit := (Finset.add_sum_erase Finset.univ Δ (Finset.mem_univ j₀)).symm
      have herase_le : ∑ j ∈ Finset.univ.erase j₀, Δ j ≤ ((d : ℝ) - 1) * E := by
        calc
          ∑ j ∈ Finset.univ.erase j₀, Δ j
              ≤ ∑ _j ∈ Finset.univ.erase j₀, E := Finset.sum_le_sum fun j _ => hΔ_le j
          _ = ((Finset.univ.erase j₀).card : ℝ) * E := by simp
          _ = ((d : ℝ) - 1) * E := by
                rw [Finset.card_erase_of_mem (Finset.mem_univ j₀), Finset.card_univ, Fintype.card_fin]
                have hd1 : 1 ≤ d := by omega
                rw [Nat.cast_sub hd1, Nat.cast_one]
      have hsub_eq : ((d : ℝ) - 1) * E = (d : ℝ) * E - E := by ring
      linarith [hE_nn, hsplit, herase_le, hΔ_sum_ge, hsub_eq]
    · have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 1 ≤ d)
      have hEd : E ≤ (d : ℝ) * E := le_mul_of_one_le_left hE_nn hd1
      linarith [hΔ_le j₀, hd_posR, hEd]
  have hsum_Δ : ∑ u : K, charZero ψ (g.eval u) = ∑ j : Fin d, (Δ j : ℂ) * ω ^ j.val := by
    rw [hsum_char]
    have h0 : (((q : ℝ) / (d : ℝ) : ℝ) : ℂ) * ∑ j : Fin d, ω ^ j.val = 0 := by
      rw [hω_sum, mul_zero]
    have hsub : ∑ j : Fin d, (Δ j : ℂ) * ω ^ j.val =
        (∑ j : Fin d, ((S j).card : ℂ) * ω ^ j.val) -
          (((q : ℝ) / (d : ℝ) : ℝ) : ℂ) * ∑ j : Fin d, ω ^ j.val := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Δ, Complex.ofReal_sub, Complex.ofReal_natCast]
      ring
    rw [hsub, h0, sub_zero]
  rw [hsum_Δ]
  have hsqrt_ge1 : (1 : ℝ) ≤ Real.sqrt (q : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg q)]
    have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
    linarith
  have hbound_q : ‖∑ j : Fin d, (Δ j : ℂ) * ω ^ j.val‖ ≤
      (40 * (d : ℝ) ^ 6 + 3 * (d : ℝ) ^ 2) * Real.sqrt (q : ℝ) := by
    calc
      ‖∑ j : Fin d, (Δ j : ℂ) * ω ^ j.val‖
          ≤ ∑ j : Fin d, ‖(Δ j : ℂ) * ω ^ j.val‖ := norm_sum_le _ _
      _ = ∑ j : Fin d, |Δ j| := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, hω_norm, one_pow, mul_one]
      _ ≤ ∑ _j : Fin d, (3 * (d : ℝ) + (d : ℝ) * E) :=
            Finset.sum_le_sum fun j _ => hΔ_abs j
      _ = (d : ℝ) * (3 * (d : ℝ) + (d : ℝ) * E) := by simp; ring
      _ = 40 * (d : ℝ) ^ 6 * Real.sqrt (q : ℝ) + 3 * (d : ℝ) ^ 2 := by simp only [E]; ring
      _ ≤ 40 * (d : ℝ) ^ 6 * Real.sqrt (q : ℝ) + 3 * (d : ℝ) ^ 2 * Real.sqrt (q : ℝ) := by
            have h3d2 : (0 : ℝ) ≤ 3 * (d : ℝ) ^ 2 := by positivity
            have hmul := mul_le_mul_of_nonneg_left hsqrt_ge1 h3d2
            linarith
      _ = (40 * (d : ℝ) ^ 6 + 3 * (d : ℝ) ^ 2) * Real.sqrt (q : ℝ) := by ring
  simpa [q, Nat.cast_pow] using hbound_q




/-- Elementary complex square root via `Real.sqrt`. -/
lemma exists_sq_eq_complex (z : ℂ) : ∃ w : ℂ, w ^ 2 = z := by
  set x : ℝ := z.re
  set y : ℝ := z.im
  set r : ℝ := Real.sqrt (x ^ 2 + y ^ 2)
  have hr_sq : r ^ 2 = x ^ 2 + y ^ 2 := Real.sq_sqrt (by positivity)
  have hr_ge_abs : |x| ≤ r := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg y])
  have hrx_nn : 0 ≤ (r + x) / 2 := by
    have := (abs_le.mp hr_ge_abs).1
    linarith
  have hrx'_nn : 0 ≤ (r - x) / 2 := by
    have := (abs_le.mp hr_ge_abs).2
    linarith
  set u : ℝ := Real.sqrt ((r + x) / 2)
  set v0 : ℝ := Real.sqrt ((r - x) / 2)
  set v : ℝ := if 0 ≤ y then v0 else -v0
  refine ⟨⟨u, v⟩, ?_⟩
  have hu2 : u ^ 2 = (r + x) / 2 := Real.sq_sqrt hrx_nn
  have hv02 : v0 ^ 2 = (r - x) / 2 := Real.sq_sqrt hrx'_nn
  have hv2 : v ^ 2 = (r - x) / 2 := by
    simp only [v]; split_ifs <;> nlinarith [hv02]
  have huv_prod : 2 * u * v0 = |y| := by
    have hnn : 0 ≤ 2 * u * v0 := by positivity
    have hsq : (2 * u * v0) ^ 2 = y ^ 2 := by
      calc
        (2 * u * v0) ^ 2 = 4 * u ^ 2 * v0 ^ 2 := by ring
        _ = 4 * ((r + x) / 2) * ((r - x) / 2) := by rw [hu2, hv02]
        _ = r ^ 2 - x ^ 2 := by ring
        _ = y ^ 2 := by linarith [hr_sq]
    have := congrArg Real.sqrt hsq
    rwa [Real.sqrt_sq hnn, Real.sqrt_sq_eq_abs] at this
  have huv : 2 * u * v = y := by
    simp only [v]
    split_ifs with hy
    · rw [huv_prod, abs_of_nonneg hy]
    · push Not at hy
      have : 2 * u * -v0 = -(2 * u * v0) := by ring
      rw [this, huv_prod, abs_of_neg hy, neg_neg]
  apply Complex.ext
  · simp only [sq, Complex.mul_re]
    linarith [hu2, hv2, show u * u = u ^ 2 by ring, show v * v = v ^ 2 by ring]
  · simp only [sq, Complex.mul_im]
    linarith [huv]

/-- Quadratic factorization over `ℂ`: `1 + c₁ X + c₂ X² = (1 - α₁ X)(1 - α₂ X)`. -/
lemma exists_quadratic_factor_complex (c₁ c₂ : ℂ) :
    ∃ α₁ α₂ : ℂ, -(α₁ + α₂) = c₁ ∧
      (1 + Polynomial.C c₁ * X + Polynomial.C c₂ * X ^ 2 : ℂ[X]) =
        (1 - Polynomial.C α₁ * X) * (1 - Polynomial.C α₂ * X) := by
  obtain ⟨w, hw⟩ := exists_sq_eq_complex (c₁ ^ 2 - 4 * c₂)
  refine ⟨(-c₁ + w) / 2, (-c₁ - w) / 2, by ring, ?_⟩
  have hsum : (-c₁ + w) / 2 + (-c₁ - w) / 2 = -c₁ := by ring
  have hprod : ((-c₁ + w) / 2) * ((-c₁ - w) / 2) = c₂ := by linear_combination -(hw / 4)
  calc
    (1 + Polynomial.C c₁ * X + Polynomial.C c₂ * X ^ 2 : ℂ[X])
        = 1 - Polynomial.C (-c₁) * X + Polynomial.C c₂ * X ^ 2 := by simp [map_neg]
    _ = 1 - Polynomial.C ((-c₁ + w) / 2 + (-c₁ - w) / 2) * X +
          Polynomial.C (((-c₁ + w) / 2) * ((-c₁ - w) / 2)) * X ^ 2 := by rw [hsum, hprod]
    _ = (1 - Polynomial.C ((-c₁ + w) / 2) * X) * (1 - Polynomial.C ((-c₁ - w) / 2) * X) := by
          simp only [map_add, map_mul]; ring

/-- Expansion of `∏ i ∈ s, (1 - f i)` over `s.powerset`. -/
private lemma prod_one_sub_eq_sum_powerset {ι R : Type*} [CommRing R] [DecidableEq ι]
    (s : Finset ι) (f : ι → R) :
    ∏ i ∈ s, (1 - f i) = ∑ t ∈ s.powerset, (-1 : R) ^ t.card * ∏ i ∈ t, f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, ih, Finset.powerset_insert]
    have hdisj : Disjoint s.powerset (s.powerset.image (insert a)) := by
      rw [Finset.disjoint_left]
      intro t ht1 ht2
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp ht2
      exact ha (Finset.mem_powerset.mp ht1 (Finset.mem_insert_self a u))
    rw [Finset.sum_union hdisj, sub_mul, one_mul, Finset.mul_sum]
    have himg : ∑ t ∈ s.powerset.image (insert a), (-1 : R) ^ t.card * ∏ i ∈ t, f i =
        -(∑ t ∈ s.powerset, f a * ((-1 : R) ^ t.card * ∏ i ∈ t, f i)) := by
      rw [Finset.sum_image, ← Finset.sum_neg_distrib]
      · refine Finset.sum_congr rfl fun t ht => ?_
        have hat : a ∉ t := fun h => ha (Finset.mem_powerset.mp ht h)
        rw [Finset.card_insert_of_notMem hat, Finset.prod_insert hat, pow_succ]
        ring
      · intro u₁ hu₁ u₂ hu₂ heq
        have ha1 : a ∉ u₁ := fun h => ha (Finset.mem_powerset.mp hu₁ h)
        have ha2 : a ∉ u₂ := fun h => ha (Finset.mem_powerset.mp hu₂ h)
        have := congrArg (fun t => t.erase a) heq
        simpa [Finset.erase_insert ha1, Finset.erase_insert ha2] using this
    rw [himg, sub_eq_add_neg]

/-- Alternating sum over powerset of a nonempty finset vanishes. -/
private lemma sum_powerset_neg_one_pow {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (hs : s.Nonempty) : ∑ t ∈ s.powerset, (-1 : ℂ) ^ t.card = 0 := by
  obtain ⟨a, ha⟩ := hs
  have hse : insert a (s.erase a) = s := Finset.insert_erase ha
  have h1 := prod_one_sub_eq_sum_powerset s (fun _ => (1 : ℂ))
  have hzero : ∏ _i ∈ s, ((1 : ℂ) - 1) = 0 := by
    rw [← hse, Finset.prod_insert (Finset.notMem_erase a s), sub_self, zero_mul]
  have h2 := h1.symm
  rw [hzero] at h2
  simpa using h2

/-- Finset of all monic polynomials in `(ZMod p)[X]` of degree `n`. -/
noncomputable def monicDeg (p n : ℕ) [Fact p.Prime] : Finset (ZMod p)[X] :=
  Finset.univ.image fun c : Fin n → ZMod p =>
    X ^ n + ∑ i : Fin n, Polynomial.C (c i) * X ^ i.val

lemma mem_monicDeg_iff (p n : ℕ) [Fact p.Prime] (f : (ZMod p)[X]) :
    f ∈ monicDeg p n ↔ f.Monic ∧ f.natDegree = n := by
  classical
  simp only [monicDeg, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨c, rfl⟩
    set r : (ZMod p)[X] := ∑ i : Fin n, Polynomial.C (c i) * X ^ i.val
    have hr_deg : r.degree < (n : WithBot ℕ) := by
      refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
      exact (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr fun i _ =>
        lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) (WithBot.coe_lt_coe.mpr i.isLt)
    have hr_lt : r.degree < ((X : (ZMod p)[X]) ^ n).degree := by
      rwa [Polynomial.degree_X_pow]
    have hmon : (X ^ n + r).Monic := (Polynomial.monic_X_pow n).add_of_left hr_lt
    have hdeg : (X ^ n + r).natDegree = n := by
      have h1 : (X ^ n + r).degree = (X ^ n : (ZMod p)[X]).degree :=
        Polynomial.degree_add_eq_left_of_degree_lt hr_lt
      rw [Polynomial.degree_X_pow] at h1
      exact Polynomial.natDegree_eq_of_degree_eq_some h1
    exact ⟨hmon, hdeg⟩
  · rintro ⟨hmon, hdeg⟩
    refine ⟨fun i => f.coeff i.val, ?_⟩
    ext k
    rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff]
    by_cases hkn : k < n
    · rw [if_neg (by omega), zero_add]
      rw [Finset.sum_eq_single ⟨k, hkn⟩]
      · simp
      · intro i _ hi
        have hne : k ≠ i.val := fun h => hi (Fin.ext h.symm)
        simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    · by_cases hkeq : k = n
      · subst hkeq
        rw [if_pos rfl]
        have hsum0 : ∑ i : Fin k, (Polynomial.C (f.coeff i.val) * X ^ i.val).coeff k = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          have hne : k ≠ i.val := by have := i.isLt; omega
          simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]
        rw [hsum0, add_zero, ← hdeg]
        exact hmon.leadingCoeff.symm
      · rw [if_neg hkeq, zero_add]
        have hsum0 : ∑ i : Fin n, (Polynomial.C (f.coeff i.val) * X ^ i.val).coeff k = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          have hne : k ≠ i.val := by have := i.isLt; omega
          simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]
        rw [hsum0]
        exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm

private lemma card_monicDeg (p n : ℕ) [Fact p.Prime] : (monicDeg p n).card = p ^ n := by
  classical
  rw [monicDeg, Finset.card_image_of_injective]
  · simp [ZMod.card]
  · intro c₁ c₂ heq
    ext i
    have h := congrArg (fun f : (ZMod p)[X] => f.coeff i.val) heq
    simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff,
      Polynomial.coeff_C_mul] at h
    have h1 : ∑ j : Fin n, c₁ j * (if i.val = j.val then 1 else 0) = c₁ i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; rw [if_neg (fun heq' => hj (Fin.ext heq'.symm)), mul_zero]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    have h2 : ∑ j : Fin n, c₂ j * (if i.val = j.val then 1 else 0) = c₂ i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; rw [if_neg (fun heq' => hj (Fin.ext heq'.symm)), mul_zero]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    rw [h1, h2] at h
    exact add_left_cancel h

/-- Finset of all monic irreducible polynomials in `(ZMod p)[X]` of degree `1 ≤ d ≤ M`. -/
noncomputable def irredMonicLe (p M : ℕ) [Fact p.Prime] : Finset (ZMod p)[X] :=
  letI := Classical.decPred (fun f : (ZMod p)[X] => Irreducible f)
  (Finset.Icc 1 M).biUnion fun d => (monicDeg p d).filter Irreducible

lemma mem_irredMonicLe_iff (p M : ℕ) [Fact p.Prime] (π : (ZMod p)[X]) :
    π ∈ irredMonicLe p M ↔ π.Monic ∧ Irreducible π ∧ 1 ≤ π.natDegree ∧ π.natDegree ≤ M := by
  classical
  simp only [irredMonicLe, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_filter, mem_monicDeg_iff]
  constructor
  · rintro ⟨d, ⟨h1, h2⟩, ⟨hmon, hdeg⟩, hirr⟩
    exact ⟨hmon, hirr, hdeg ▸ h1, hdeg ▸ h2⟩
  · rintro ⟨hmon, hirr, h1, h2⟩
    exact ⟨π.natDegree, ⟨h1, h2⟩, ⟨hmon, rfl⟩, hirr⟩

/-- Distinct monic irreducibles in `F[X]` are coprime. -/
lemma isCoprime_of_monic_irreducible_ne {F : Type*} [Field F] [DecidableEq F]
    {π₁ π₂ : F[X]} (hm1 : π₁.Monic) (hi1 : Irreducible π₁)
    (hm2 : π₂.Monic) (hi2 : Irreducible π₂) (hne : π₁ ≠ π₂) : IsCoprime π₁ π₂ := by
  set g := EuclideanDomain.gcd π₁ π₂
  have hg1 : g ∣ π₁ := EuclideanDomain.gcd_dvd_left π₁ π₂
  have hg2 : g ∣ π₂ := EuclideanDomain.gcd_dvd_right π₁ π₂
  obtain ⟨q, hq⟩ := hg1
  rcases hi1.isUnit_or_isUnit hq with hu | hqu
  · obtain ⟨u, hu_eq⟩ := hu
    refine ⟨EuclideanDomain.gcdA π₁ π₂ * (u⁻¹ : F[X]ˣ),
      EuclideanDomain.gcdB π₁ π₂ * (u⁻¹ : F[X]ˣ), ?_⟩
    have hbez := EuclideanDomain.gcd_eq_gcd_ab π₁ π₂
    calc
      EuclideanDomain.gcdA π₁ π₂ * (u⁻¹ : F[X]ˣ) * π₁ +
          EuclideanDomain.gcdB π₁ π₂ * (u⁻¹ : F[X]ˣ) * π₂
          = (π₁ * EuclideanDomain.gcdA π₁ π₂ + π₂ * EuclideanDomain.gcdB π₁ π₂) *
              (u⁻¹ : F[X]ˣ) := by ring
      _ = g * (u⁻¹ : F[X]ˣ) := by rw [← hbez]
      _ = (u : F[X]) * (u⁻¹ : F[X]ˣ) := by rw [← hu_eq]
      _ = 1 := by exact_mod_cast Units.mul_inv u
  · exfalso
    have h1g : π₁ ∣ g := by
      obtain ⟨v, hv⟩ := hqu
      refine ⟨(v⁻¹ : F[X]ˣ), ?_⟩
      calc
        g = g * ((v : F[X]) * (v⁻¹ : F[X]ˣ)) := by rw [Units.mul_inv, mul_one]
        _ = (g * q) * (v⁻¹ : F[X]ˣ) := by rw [hv]; ring
        _ = π₁ * (v⁻¹ : F[X]ˣ) := by rw [← hq]
    have h12 : π₁ ∣ π₂ := h1g.trans hg2
    obtain ⟨r, hr⟩ := h12
    rcases hi2.isUnit_or_isUnit hr with hu1 | hur
    · exact hi1.not_isUnit hu1
    · obtain ⟨u, rfl⟩ := hur
      have hnorm := congrArg normalize hr
      rw [hm2.normalize_eq_self, normalize_mul, hm1.normalize_eq_self,
        normalize_coe_units, mul_one] at hnorm
      exact hne hnorm.symm

/-- Character lifted to `(ZMod p)[X]` via `aeval θ`. -/
noncomputable def charPoly (p : ℕ) [Fact p.Prime]
    (θ : GaloisField p 3) (χ : (GaloisField p 3)ˣ →* ℂˣ) : (ZMod p)[X] →*₀ ℂ :=
  letI : DecidableEq (GaloisField p 3) := Classical.decEq _
  (charZero χ).comp (Polynomial.aeval θ).toRingHom.toMonoidWithZeroHom

/-- `n`-th L-function coefficient `c_n = ∑_{f monic, deg n} χ̃(f)`. -/
noncomputable def Lcoeff (p : ℕ) [Fact p.Prime]
    (θ : GaloisField p 3) (χ : (GaloisField p 3)ˣ →* ℂˣ) (n : ℕ) : ℂ :=
  ∑ f ∈ monicDeg p n, charPoly p θ χ f

lemma Lcoeff_zero (p : ℕ) [Fact p.Prime]
    (θ : GaloisField p 3) (χ : (GaloisField p 3)ˣ →* ℂˣ) :
    Lcoeff p θ χ 0 = 1 := by
  have hm0 : monicDeg p 0 = {1} := by
    ext f
    rw [mem_monicDeg_iff, Finset.mem_singleton]
    constructor
    · rintro ⟨hm, hd⟩
      exact Polynomial.eq_one_of_monic_natDegree_zero hm hd
    · rintro rfl
      exact ⟨Polynomial.monic_one, Polynomial.natDegree_one⟩
  simp [Lcoeff, hm0]

lemma Lcoeff_one (p : ℕ) [Fact p.Prime]
    (θ : GaloisField p 3) (χ : (GaloisField p 3)ˣ →* ℂˣ) :
    letI : DecidableEq (GaloisField p 3) := Classical.decEq _
    Lcoeff p θ χ 1 = ∑ t : ZMod p, charZero χ (θ + algebraMap (ZMod p) (GaloisField p 3) t) := by
  classical
  have hm1 : monicDeg p 1 = Finset.univ.image (fun t : ZMod p => X + Polynomial.C t) := by
    ext f
    rw [mem_monicDeg_iff, Finset.mem_image]
    constructor
    · rintro ⟨hm, hd⟩
      refine ⟨f.coeff 0, Finset.mem_univ _, ?_⟩
      ext k
      cases k with
      | zero => simp
      | succ k =>
        cases k with
        | zero =>
          have h1 : f.coeff 1 = f.leadingCoeff := by rw [← hd]; rfl
          simp [h1, hm.leadingCoeff]
        | succ k =>
          have h2 : f.coeff (k + 2) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
          simp [Polynomial.coeff_X, h2]
    · rintro ⟨t, _, rfl⟩
      exact ⟨Polynomial.monic_X_add_C t, Polynomial.natDegree_X_add_C t⟩
  rw [Lcoeff, hm1, Finset.sum_image]
  · refine Finset.sum_congr rfl fun t _ => ?_
    simp [charPoly]
  · intro t₁ _ t₂ _ heq
    have := congrArg (fun f : (ZMod p)[X] => f.coeff 0) heq
    simpa using this

/-- If `θ ∈ GaloisField p 3` is not in the prime field `ZMod p`, then `minpoly (ZMod p) θ`
has degree `3`. -/
lemma natDegree_minpoly_eq_three (p : ℕ) [Fact p.Prime] (θ : GaloisField p 3)
    (hθ : θ ∉ Set.range (algebraMap (ZMod p) (GaloisField p 3))) :
    (minpoly (ZMod p) θ).natDegree = 3 := by
  set P := minpoly (ZMod p) θ
  have hint : IsIntegral (ZMod p) θ := Algebra.IsIntegral.isIntegral θ
  have hirr : Irreducible P := minpoly.irreducible hint
  have : Fact (Irreducible P) := ⟨hirr⟩
  let φ : AdjoinRoot P →ₐ[ZMod p] GaloisField p 3 :=
    AdjoinRoot.liftAlgHom P (Algebra.ofId (ZMod p) (GaloisField p 3)) θ
      (by simpa [Polynomial.aeval_def] using minpoly.aeval (ZMod p) θ)
  let : Algebra (AdjoinRoot P) (GaloisField p 3) := φ.toRingHom.toAlgebra
  have : IsScalarTower (ZMod p) (AdjoinRoot P) (GaloisField p 3) :=
    IsScalarTower.of_algebraMap_eq' (φ.comp_algebraMap.symm)
  have hfin_ad : Module.finrank (ZMod p) (AdjoinRoot P) = P.natDegree := by
    let pb := AdjoinRoot.powerBasis hirr.ne_zero
    simpa [pb] using pb.finrank
  have hmul : Module.finrank (ZMod p) (AdjoinRoot P) *
      Module.finrank (AdjoinRoot P) (GaloisField p 3) =
      Module.finrank (ZMod p) (GaloisField p 3) :=
    Module.finrank_mul_finrank (ZMod p) (AdjoinRoot P) (GaloisField p 3)
  rw [hfin_ad, GaloisField.finrank p (by norm_num)] at hmul
  have hdvd : P.natDegree ∣ 3 := ⟨Module.finrank (AdjoinRoot P) (GaloisField p 3), hmul.symm⟩
  have hpos : 0 < P.natDegree := minpoly.natDegree_pos hint
  have hne1 : P.natDegree ≠ 1 := by
    intro h1
    have hmon : P.Monic := minpoly.monic hint
    have hP : P = X + Polynomial.C (P.coeff 0) := by
      ext k
      cases k with
      | zero => simp
      | succ k =>
        cases k with
        | zero =>
          have hc : P.coeff 1 = P.leadingCoeff := by rw [← h1]; rfl
          simp [hc, hmon.leadingCoeff]
        | succ k =>
          have h0 : P.coeff (k + 2) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
          simp [Polynomial.coeff_X, h0]
    have haev : Polynomial.aeval θ (X + Polynomial.C (P.coeff 0)) = 0 := by
      rw [← hP]; exact minpoly.aeval (ZMod p) θ
    rw [map_add, Polynomial.aeval_X, Polynomial.aeval_C] at haev
    apply hθ
    refine ⟨-(P.coeff 0), ?_⟩
    rw [map_neg]
    exact (eq_neg_of_add_eq_zero_left haev).symm
  have hle3 : P.natDegree ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
  have hcases : P.natDegree = 1 ∨ P.natDegree = 2 ∨ P.natDegree = 3 := by omega
  rcases hcases with h | h | h
  · exact absurd h hne1
  · exfalso; rw [h] at hdvd; norm_num at hdvd
  · exact h

/-- All L-function coefficients of degree `n ≥ 3` vanish when `θ ∉ F_p` and `χ ≠ 1`. -/
lemma Lcoeff_eq_zero_of_ge_three (p : ℕ) [Fact p.Prime]
    (θ : GaloisField p 3) (hθ : θ ∉ Set.range (algebraMap (ZMod p) (GaloisField p 3)))
    (χ : (GaloisField p 3)ˣ →* ℂˣ) (hχ : ∃ u₀ : (GaloisField p 3)ˣ, χ u₀ ≠ 1)
    (n : ℕ) (hn : 3 ≤ n) :
    Lcoeff p θ χ n = 0 := by
  classical
  set P := minpoly (ZMod p) θ
  have hint : IsIntegral (ZMod p) θ := Algebra.IsIntegral.isIntegral θ
  have hPmon : P.Monic := minpoly.monic hint
  have hPdeg : P.natDegree = 3 := natDegree_minpoly_eq_three p θ hθ
  let remPoly : (Fin 3 → ZMod p) → (ZMod p)[X] := fun r =>
    ∑ i : Fin 3, Polynomial.C (r i) * X ^ i.val
  have hrem_deg : ∀ r : Fin 3 → ZMod p, (remPoly r).degree < (3 : WithBot ℕ) := by
    intro r
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe 3)]
    intro i _
    exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) (WithBot.coe_lt_coe.mpr i.isLt)
  let combine : (ZMod p)[X] × (Fin 3 → ZMod p) → (ZMod p)[X] := fun qr =>
    qr.1 * P + remPoly qr.2
  have hcomb_mem : ∀ qr ∈ monicDeg p (n - 3) ×ˢ (Finset.univ : Finset (Fin 3 → ZMod p)),
      combine qr ∈ monicDeg p n := by
    intro ⟨q, r⟩ hqr
    rw [Finset.mem_product] at hqr
    obtain ⟨hqm, hqd⟩ := (mem_monicDeg_iff p (n - 3) q).mp hqr.1
    rw [mem_monicDeg_iff]
    have hqP_mon : (q * P).Monic := hqm.mul hPmon
    have hqP_deg : (q * P).natDegree = n := by
      rw [Polynomial.natDegree_mul hqm.ne_zero hPmon.ne_zero, hqd, hPdeg]; omega
    have hlt : (remPoly r).degree < (q * P).degree := by
      rw [Polynomial.degree_eq_natDegree hqP_mon.ne_zero, hqP_deg]
      exact lt_of_lt_of_le (hrem_deg r) (WithBot.coe_le_coe.mpr hn)
    refine ⟨hqP_mon.add_of_left hlt, ?_⟩
    have hd := Polynomial.degree_add_eq_left_of_degree_lt hlt
    rw [Polynomial.degree_eq_natDegree hqP_mon.ne_zero, hqP_deg] at hd
    exact Polynomial.natDegree_eq_of_degree_eq_some hd
  have hcomb_inj : Set.InjOn combine
      ((monicDeg p (n - 3) ×ˢ (Finset.univ : Finset (Fin 3 → ZMod p)) :
        Finset ((ZMod p)[X] × (Fin 3 → ZMod p))) : Set _) := by
    intro ⟨q₁, r₁⟩ _ ⟨q₂, r₂⟩ _ heq
    have hdiff : (q₁ - q₂) * P = remPoly r₂ - remPoly r₁ := by
      simp only [combine] at heq
      linear_combination heq
    have hqeq : q₁ = q₂ := by
      by_contra hne
      have hne0 : q₁ - q₂ ≠ 0 := sub_ne_zero.mpr hne
      have hLHS : 3 ≤ ((q₁ - q₂) * P).natDegree := by
        rw [Polynomial.natDegree_mul hne0 hPmon.ne_zero, hPdeg]; omega
      have hRHS_ne : remPoly r₂ - remPoly r₁ ≠ 0 := by
        rw [← hdiff]; exact mul_ne_zero hne0 hPmon.ne_zero
      have hRHS : (remPoly r₂ - remPoly r₁).degree < (3 : WithBot ℕ) :=
        lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt (hrem_deg r₂) (hrem_deg r₁))
      have hRHS_nat : (remPoly r₂ - remPoly r₁).natDegree < 3 :=
        (Polynomial.natDegree_lt_iff_degree_lt hRHS_ne).mpr hRHS
      rw [hdiff] at hLHS; omega
    subst hqeq
    have hr_eq : remPoly r₁ = remPoly r₂ := by
      simp only [combine] at heq
      exact add_left_cancel heq
    have hr_fun : r₁ = r₂ := by
      ext i
      have hc := congrArg (fun f : (ZMod p)[X] => f.coeff i.val) hr_eq
      simp only [remPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow] at hc
      have hs1 : ∑ j : Fin 3, r₁ j * (if i.val = j.val then 1 else 0) = r₁ i := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj; rw [if_neg (fun h => hj (Fin.ext h.symm)), mul_zero]
        · intro hm; exact absurd (Finset.mem_univ _) hm
      have hs2 : ∑ j : Fin 3, r₂ j * (if i.val = j.val then 1 else 0) = r₂ i := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj; rw [if_neg (fun h => hj (Fin.ext h.symm)), mul_zero]
        · intro hm; exact absurd (Finset.mem_univ _) hm
      rwa [hs1, hs2] at hc
    exact Prod.ext rfl hr_fun
  have hdom_eq :
      (monicDeg p (n - 3) ×ˢ (Finset.univ : Finset (Fin 3 → ZMod p))).image combine =
        monicDeg p n := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro f hf
      obtain ⟨qr, hqr, rfl⟩ := Finset.mem_image.mp hf
      exact hcomb_mem qr hqr
    · rw [Finset.card_image_of_injOn hcomb_inj, Finset.card_product, card_monicDeg, card_monicDeg,
        Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card, ← pow_add,
        Nat.sub_add_cancel hn]
  have haev_inj : Function.Injective (fun r : Fin 3 → ZMod p => Polynomial.aeval θ (remPoly r)) := by
    intro r₁ r₂ heq
    have h0 : Polynomial.aeval θ (remPoly r₁ - remPoly r₂) = 0 := by
      simp only [map_sub, heq, sub_self]
    have hdvd : P ∣ remPoly r₁ - remPoly r₂ := minpoly.dvd (ZMod p) θ h0
    have hzero : remPoly r₁ - remPoly r₂ = 0 := by
      by_contra hne
      have hle : P.natDegree ≤ (remPoly r₁ - remPoly r₂).natDegree :=
        Polynomial.natDegree_le_of_dvd hdvd hne
      have hlt : (remPoly r₁ - remPoly r₂).degree < (3 : WithBot ℕ) :=
        lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt (hrem_deg r₁) (hrem_deg r₂))
      have hlt_nat : (remPoly r₁ - remPoly r₂).natDegree < 3 :=
        (Polynomial.natDegree_lt_iff_degree_lt hne).mpr hlt
      omega
    have hr_eq : remPoly r₁ = remPoly r₂ := sub_eq_zero.mp hzero
    ext i
    have hc := congrArg (fun f : (ZMod p)[X] => f.coeff i.val) hr_eq
    simp only [remPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow] at hc
    have hs1 : ∑ j : Fin 3, r₁ j * (if i.val = j.val then 1 else 0) = r₁ i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; rw [if_neg (fun h => hj (Fin.ext h.symm)), mul_zero]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    have hs2 : ∑ j : Fin 3, r₂ j * (if i.val = j.val then 1 else 0) = r₂ i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; rw [if_neg (fun h => hj (Fin.ext h.symm)), mul_zero]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    rwa [hs1, hs2] at hc
  let : Fintype (GaloisField p 3) := Fintype.ofFinite _
  have haev_bij : Function.Bijective (fun r : Fin 3 → ZMod p => Polynomial.aeval θ (remPoly r)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨haev_inj, ?_⟩
    rw [Fintype.card_fun, Fintype.card_fin, ZMod.card, Fintype.card_eq_nat_card,
      GaloisField.card p 3 (by norm_num)]
  rw [Lcoeff, ← hdom_eq, Finset.sum_image hcomb_inj, Finset.sum_product]
  have hinner : ∀ q ∈ monicDeg p (n - 3),
      ∑ r : Fin 3 → ZMod p, charPoly p θ χ (combine (q, r)) = 0 := by
    intro q _
    have hrew : ∀ r : Fin 3 → ZMod p,
        charPoly p θ χ (combine (q, r)) = charZero χ (Polynomial.aeval θ (remPoly r)) := by
      intro r
      change charZero χ (Polynomial.aeval θ (q * P + remPoly r)) =
        charZero χ (Polynomial.aeval θ (remPoly r))
      rw [map_add, map_mul, minpoly.aeval, mul_zero, zero_add]
    simp_rw [hrew]
    rw [Fintype.sum_bijective _ haev_bij _ _ (fun _ => rfl)]
    exact sum_charZero_eq_zero χ hχ
  exact Finset.sum_eq_zero hinner

/-- The degree-≤2 L-polynomial `L(X) = 1 + c₁ X + c₂ X²`. -/
noncomputable def Lpoly (p : ℕ) [Fact p.Prime]
    (θ : GaloisField p 3) (χ : (GaloisField p 3)ˣ →* ℂˣ) : ℂ[X] :=
  1 + Polynomial.C (Lcoeff p θ χ 1) * X + Polynomial.C (Lcoeff p θ χ 2) * X ^ 2

lemma Lpoly_coeff (p : ℕ) [Fact p.Prime]
    (θ : GaloisField p 3) (hθ : θ ∉ Set.range (algebraMap (ZMod p) (GaloisField p 3)))
    (χ : (GaloisField p 3)ˣ →* ℂˣ) (hχ : ∃ u₀ : (GaloisField p 3)ˣ, χ u₀ ≠ 1) (n : ℕ) :
    (Lpoly p θ χ).coeff n = Lcoeff p θ χ n := by
  simp only [Lpoly, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_C_mul,
    Polynomial.coeff_X, Polynomial.coeff_X_pow]
  match n with
  | 0 => simp [Lcoeff_zero]
  | 1 => simp
  | 2 => simp
  | n + 3 =>
    rw [Lcoeff_eq_zero_of_ge_three p θ hθ χ hχ (n + 3) (by omega)]
    simp

/-- Finite-modulus Euler product inverse `E_M(X) = ∏_{π ∈ I_M} (1 - χ̃(π) X^(deg π))`. -/
private noncomputable def eulerInv (p M : ℕ) [Fact p.Prime]
    (θ : GaloisField p 3) (χ : (GaloisField p 3)ˣ →* ℂˣ) : ℂ[X] :=
  ∏ π ∈ irredMonicLe p M, (1 - Polynomial.C (charPoly p θ χ π) * X ^ π.natDegree)

/-- Coefficient formula for `eulerInv p M θ χ`. -/
private lemma eulerInv_coeff (p M : ℕ) [Fact p.Prime]
    (θ : GaloisField p 3) (χ : (GaloisField p 3)ˣ →* ℂˣ) (k : ℕ) :
    (eulerInv p M θ χ).coeff k =
      ∑ S ∈ (irredMonicLe p M).powerset.filter (fun S => (∏ π ∈ S, π).natDegree = k),
        (-1 : ℂ) ^ S.card * charPoly p θ χ (∏ π ∈ S, π) := by
  classical
  have heuler_exp : eulerInv p M θ χ =
      ∑ S ∈ (irredMonicLe p M).powerset,
        Polynomial.C ((-1 : ℂ) ^ S.card * charPoly p θ χ (∏ π ∈ S, π)) *
          X ^ (∏ π ∈ S, π).natDegree := by
    rw [eulerInv, prod_one_sub_eq_sum_powerset]
    refine Finset.sum_congr rfl fun S hS => ?_
    have hSsub : S ⊆ irredMonicLe p M := Finset.mem_powerset.mp hS
    have hmonS : ∀ π ∈ S, π.Monic := fun π hπ => ((mem_irredMonicLe_iff p M π).mp (hSsub hπ)).1
    have hdegS : (∏ π ∈ S, π).natDegree = ∑ π ∈ S, π.natDegree :=
      Polynomial.natDegree_prod_of_monic S (fun π => π) hmonS
    rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum, ← hdegS,
      ← map_prod, map_mul, mul_assoc]
    have hc : (-1 : ℂ[X]) ^ S.card = Polynomial.C ((-1 : ℂ) ^ S.card) := by
      simp [map_pow]
    rw [hc]
  rw [heuler_exp, Polynomial.finsetSum_coeff, Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases hk : (∏ π ∈ S, π).natDegree = k
  · rw [if_pos hk.symm, if_pos hk, mul_one]
  · rw [if_neg (Ne.symm hk), if_neg hk, mul_zero]

open Classical in
/-- For monic `f` of degree `1 ≤ n ≤ M`, subsets `S ⊆ I_M` whose product divides `f` are
precisely the subsets of `(normalizedFactors f).toFinset`, which is nonempty. -/
private lemma sum_powerset_dvd_eq_zero (p M n : ℕ) [Fact p.Prime] (hn1 : 1 ≤ n) (hnM : n ≤ M)
    (f : (ZMod p)[X]) (hfm : f.Monic) (hfd : f.natDegree = n) :
    ∑ S ∈ (irredMonicLe p M).powerset.filter (fun S => (∏ π ∈ S, π) ∣ f), (-1 : ℂ) ^ S.card = 0 := by
  classical
  set Pf : Finset (ZMod p)[X] := (UniqueFactorizationMonoid.normalizedFactors f).toFinset
  have hPf_ne : Pf.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hnf0 : UniqueFactorizationMonoid.normalizedFactors f = 0 := by
      ext q
      have hnot : q ∉ UniqueFactorizationMonoid.normalizedFactors f := by
        intro hq
        have : q ∈ Pf := Multiset.mem_toFinset.mpr hq
        rw [hempty] at this
        exact Finset.notMem_empty q this
      simp [Multiset.count_eq_zero_of_notMem hnot]
    have hf1 : f = 1 := by
      have h := Polynomial.leadingCoeff_mul_prod_normalizedFactors f
      rw [hfm.leadingCoeff, map_one, one_mul, hnf0, Multiset.prod_zero] at h
      exact h.symm
    rw [hf1, Polynomial.natDegree_one] at hfd
    omega
  have hfilt_eq :
      (irredMonicLe p M).powerset.filter (fun S => (∏ π ∈ S, π) ∣ f) = Pf.powerset := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨hSsub, hdvd⟩
      intro π hπ
      have ⟨hπm, hπi, _, _⟩ := (mem_irredMonicLe_iff p M π).mp (hSsub hπ)
      have hπ_dvd : π ∣ f := (Finset.dvd_prod_of_mem _ hπ).trans hdvd
      exact Multiset.mem_toFinset.mpr
        ((Polynomial.mem_normalizedFactors_iff hfm.ne_zero).mpr ⟨hπi, hπm, hπ_dvd⟩)
    · intro hSPf
      have hSsub : S ⊆ irredMonicLe p M := by
        intro π hπ
        have hmem := Multiset.mem_toFinset.mp (hSPf hπ)
        obtain ⟨hπi, hπm, hπd⟩ := (Polynomial.mem_normalizedFactors_iff hfm.ne_zero).mp hmem
        rw [mem_irredMonicLe_iff]
        have h1 : 1 ≤ π.natDegree := by
          by_contra hlt
          have h0 : π.natDegree = 0 := by omega
          have hπ1 : π = 1 := Polynomial.eq_one_of_monic_natDegree_zero hπm h0
          rw [hπ1] at hπi
          exact hπi.not_isUnit isUnit_one
        have h2 : π.natDegree ≤ M :=
          (Polynomial.natDegree_le_of_dvd hπd hfm.ne_zero).trans (by omega)
        exact ⟨hπm, hπi, h1, h2⟩
      refine ⟨hSsub, ?_⟩
      refine Finset.prod_dvd_of_coprime ?_ ?_
      · intro π₁ h1 π₂ h2 hne
        have ⟨hm1, hi1, _, _⟩ := (mem_irredMonicLe_iff p M π₁).mp (hSsub h1)
        have ⟨hm2, hi2, _, _⟩ := (mem_irredMonicLe_iff p M π₂).mp (hSsub h2)
        exact isCoprime_of_monic_irreducible_ne hm1 hi1 hm2 hi2 hne
      · intro π hπ
        exact ((Polynomial.mem_normalizedFactors_iff hfm.ne_zero).mp
          (Multiset.mem_toFinset.mp (hSPf hπ))).2.2
  rw [hfilt_eq]
  exact sum_powerset_neg_one_pow Pf hPf_ne

/-- **Finite-Modulus Euler Product Identity**:
`X ^ (M + 1) ∣ Lpoly * eulerInv - 1` (pure `ℂ[X]` Möbius inversion, zero `PowerSeries`). -/
private theorem dvd_X_pow_Lpoly_mul_eulerInv_sub_one (p M : ℕ) [Fact p.Prime]
    (θ : GaloisField p 3) (hθ : θ ∉ Set.range (algebraMap (ZMod p) (GaloisField p 3)))
    (χ : (GaloisField p 3)ˣ →* ℂˣ) (hχ : ∃ u₀ : (GaloisField p 3)ˣ, χ u₀ ≠ 1) :
    (X : ℂ[X]) ^ (M + 1) ∣ Lpoly p θ χ * eulerInv p M θ χ - 1 := by
  classical
  rw [Polynomial.X_pow_dvd_iff]
  intro n hn
  cases n with
  | zero =>
    rw [Polynomial.coeff_sub, Polynomial.coeff_one_zero, Polynomial.coeff_mul]
    simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
    rw [Lpoly_coeff p θ hθ χ hχ 0, Lcoeff_zero, one_mul, eulerInv_coeff p M θ χ 0]
    have hfilt0 :
        (irredMonicLe p M).powerset.filter (fun S => (∏ π ∈ S, π).natDegree = 0) = {∅} := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
      constructor
      · rintro ⟨hSsub, hdeg0⟩
        by_contra hne
        obtain ⟨π, hπ⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        have hmonS : ∀ q ∈ S, q.Monic := fun q hq => ((mem_irredMonicLe_iff p M q).mp (hSsub hq)).1
        have hdegS : (∏ q ∈ S, q).natDegree = ∑ q ∈ S, q.natDegree :=
          Polynomial.natDegree_prod_of_monic S (fun q => q) hmonS
        have hge1 : 1 ≤ π.natDegree := ((mem_irredMonicLe_iff p M π).mp (hSsub hπ)).2.2.1
        have hle : π.natDegree ≤ ∑ q ∈ S, q.natDegree :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) hπ
        omega
      · rintro rfl
        exact ⟨Finset.empty_subset _, by simp⟩
    rw [hfilt0, Finset.sum_singleton]
    simp
  | succ m =>
    set n := m + 1
    have hn_pos : 1 ≤ n := Nat.succ_pos m
    have hn_le : n ≤ M := by omega
    rw [Polynomial.coeff_sub, Polynomial.coeff_one, if_neg (by omega), sub_zero,
      Polynomial.coeff_mul]
    have hstep1 :
        ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n, (Lpoly p θ χ).coeff ab.1 * (eulerInv p M θ χ).coeff ab.2 =
        ∑ S ∈ (irredMonicLe p M).powerset.filter (fun S => (∏ π ∈ S, π).natDegree ≤ n),
          (-1 : ℂ) ^ S.card *
            ∑ g ∈ monicDeg p (n - (∏ π ∈ S, π).natDegree),
              charPoly p θ χ (g * ∏ π ∈ S, π) := by
      have hrew :
          ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n, (Lpoly p θ χ).coeff ab.1 * (eulerInv p M θ χ).coeff ab.2 =
          ∑ k ∈ Finset.range (n + 1),
            ∑ S ∈ (irredMonicLe p M).powerset.filter (fun S => (∏ π ∈ S, π).natDegree = k),
              (-1 : ℂ) ^ S.card *
                ∑ g ∈ monicDeg p (n - k), charPoly p θ χ (g * ∏ π ∈ S, π) := by
        rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b =>
          (Lpoly p θ χ).coeff a * (eulerInv p M θ χ).coeff b)]
        rw [← Finset.sum_range_reflect]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hsub : n - (n - k) = k := Nat.sub_sub_self hkn
        simp only [Nat.succ_sub_one]
        rw [hsub, Lpoly_coeff p θ hθ χ hχ (n - k), Lcoeff, eulerInv_coeff p M θ χ k, Finset.mul_sum]
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [map_mul]; ring
      rw [hrew]
      have hbi :
          ((Finset.range (n + 1)).biUnion fun k =>
            (irredMonicLe p M).powerset.filter (fun S => (∏ π ∈ S, π).natDegree = k)) =
          (irredMonicLe p M).powerset.filter (fun S => (∏ π ∈ S, π).natDegree ≤ n) := by
        ext S
        simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, Nat.lt_succ_iff]
        constructor
        · rintro ⟨k, hk, hS, rfl⟩; exact ⟨hS, hk⟩
        · rintro ⟨hS, hle⟩; exact ⟨(∏ π ∈ S, π).natDegree, hle, hS, rfl⟩
      rw [← hbi, Finset.sum_biUnion]
      · refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun S hS => ?_
        have hkS : (∏ π ∈ S, π).natDegree = k := (Finset.mem_filter.mp hS).2
        rw [hkS]
      · intro k₁ _ k₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro S h1 h2
        exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    rw [hstep1]
    have hstep2 :
        ∑ S ∈ (irredMonicLe p M).powerset.filter (fun S => (∏ π ∈ S, π).natDegree ≤ n),
          (-1 : ℂ) ^ S.card *
            ∑ g ∈ monicDeg p (n - (∏ π ∈ S, π).natDegree), charPoly p θ χ (g * ∏ π ∈ S, π) =
        ∑ S ∈ (irredMonicLe p M).powerset.filter (fun S => (∏ π ∈ S, π).natDegree ≤ n),
          (-1 : ℂ) ^ S.card *
            ∑ f ∈ (monicDeg p n).filter (fun f => (∏ π ∈ S, π) ∣ f), charPoly p θ χ f := by
      refine Finset.sum_congr rfl fun S hS => ?_
      congr 1
      have hSsub : S ⊆ irredMonicLe p M := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
      have hSle : (∏ π ∈ S, π).natDegree ≤ n := (Finset.mem_filter.mp hS).2
      have hPmon : (∏ π ∈ S, π).Monic :=
        Polynomial.monic_prod_of_monic S (fun π => π) fun π hπ =>
          ((mem_irredMonicLe_iff p M π).mp (hSsub hπ)).1
      refine Finset.sum_nbij (fun g => g * ∏ π ∈ S, π) ?_ ?_ ?_ ?_
      · intro g hg
        obtain ⟨hgm, hgd⟩ := (mem_monicDeg_iff p _ g).mp hg
        rw [Finset.mem_filter, mem_monicDeg_iff]
        refine ⟨⟨hgm.mul hPmon, ?_⟩, dvd_mul_left _ _⟩
        rw [Polynomial.natDegree_mul hgm.ne_zero hPmon.ne_zero, hgd, Nat.sub_add_cancel hSle]
      · intro g₁ _ g₂ _ heq
        exact mul_right_cancel₀ hPmon.ne_zero heq
      · intro f hf
        rw [Finset.mem_coe, Finset.mem_filter, mem_monicDeg_iff] at hf
        obtain ⟨⟨hfm, hfd⟩, ⟨q, hq⟩⟩ := hf
        have hqm : q.Monic := by
          have h1 : (q * ∏ π ∈ S, π).Monic := by rwa [mul_comm, ← hq]
          exact Polynomial.Monic.of_mul_monic_right hPmon h1
        have hqd : q.natDegree = n - (∏ π ∈ S, π).natDegree := by
          have h1 : f.natDegree = (∏ π ∈ S, π).natDegree + q.natDegree := by
            rw [hq, Polynomial.natDegree_mul hPmon.ne_zero hqm.ne_zero]
          omega
        exact ⟨q, Finset.mem_coe.mpr ((mem_monicDeg_iff p _ q).mpr ⟨hqm, hqd⟩),
          by dsimp only; rw [mul_comm, ← hq]⟩
      · intro _ _; rfl
    rw [hstep2]
    have hstep3 :
        ∑ S ∈ (irredMonicLe p M).powerset.filter (fun S => (∏ π ∈ S, π).natDegree ≤ n),
          (-1 : ℂ) ^ S.card *
            ∑ f ∈ (monicDeg p n).filter (fun f => (∏ π ∈ S, π) ∣ f), charPoly p θ χ f =
        ∑ f ∈ monicDeg p n,
          charPoly p θ χ f *
            ∑ S ∈ (irredMonicLe p M).powerset.filter (fun S => (∏ π ∈ S, π) ∣ f),
              (-1 : ℂ) ^ S.card := by
      have hL :
          ∑ S ∈ (irredMonicLe p M).powerset.filter (fun S => (∏ π ∈ S, π).natDegree ≤ n),
            (-1 : ℂ) ^ S.card *
              ∑ f ∈ (monicDeg p n).filter (fun f => (∏ π ∈ S, π) ∣ f), charPoly p θ χ f =
          ∑ S ∈ (irredMonicLe p M).powerset,
            ∑ f ∈ monicDeg p n,
              if (∏ π ∈ S, π) ∣ f then (-1 : ℂ) ^ S.card * charPoly p θ χ f else 0 := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun S _ => ?_
        split_ifs with hle
        · simp [Finset.mul_sum, Finset.sum_filter, mul_ite]
        · symm
          refine Finset.sum_eq_zero fun f hf => ?_
          obtain ⟨hfm, hfd⟩ := (mem_monicDeg_iff p n f).mp hf
          rw [if_neg]
          intro hdvd
          have := Polynomial.natDegree_le_of_dvd hdvd hfm.ne_zero
          omega
      rw [hL, Finset.sum_comm]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun S _ => ?_
      by_cases hd : (∏ π ∈ S, π) ∣ f
      · simp [hd, mul_comm]
      · simp [hd]
    rw [hstep3]
    refine Finset.sum_eq_zero fun f hf => ?_
    obtain ⟨hfm, hfd⟩ := (mem_monicDeg_iff p n f).mp hf
    rw [sum_powerset_dvd_eq_zero p M n hn_pos hn_le f hfm hfd, mul_zero]

/-- Truncated geometric series polynomial `∑_{j=0}^M a^j X^(j*d)`. -/
private noncomputable def truncGeom (M : ℕ) (a : ℂ) (d : ℕ) : ℂ[X] :=
  ∑ j ∈ Finset.range (M + 1), Polynomial.C (a ^ j) * X ^ (j * d)

/-- Truncated log-derivative polynomial `- d * a * X^d * truncGeom M a d`. -/
private noncomputable def logDerivPoly (M : ℕ) (a : ℂ) (d : ℕ) : ℂ[X] :=
  -(Polynomial.C ((d : ℂ) * a) * X ^ d) * truncGeom M a d

private lemma dvd_X_pow_factor_mul_logDerivPoly (M : ℕ) (a : ℂ) (d : ℕ) (hd : 1 ≤ d) :
    (X : ℂ[X]) ^ (M + 1) ∣
      (1 - Polynomial.C a * X ^ d) * logDerivPoly M a d -
        X * Polynomial.derivative (1 - Polynomial.C a * X ^ d) := by
  have hgeom : (1 - Polynomial.C a * X ^ d) * truncGeom M a d =
      1 - Polynomial.C (a ^ (M + 1)) * X ^ ((M + 1) * d) := by
    have hmul : (1 - Polynomial.C a * X ^ d) * truncGeom M a d =
        (∑ j ∈ Finset.range (M + 1), Polynomial.C (a ^ j) * X ^ (j * d)) -
          (∑ j ∈ Finset.range (M + 1), Polynomial.C (a ^ (j + 1)) * X ^ ((j + 1) * d)) := by
      rw [sub_mul, one_mul, truncGeom, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [pow_succ', map_mul]
      have hexp : (j + 1) * d = d + j * d := by ring
      rw [hexp, pow_add]; ring
    rw [hmul]
    have htel := Finset.sum_range_sub' (fun j => Polynomial.C (a ^ j) * X ^ (j * d)) (M + 1)
    simpa [pow_zero, zero_mul] using htel
  have hderiv : (X : ℂ[X]) * Polynomial.derivative (1 - Polynomial.C a * X ^ d) =
      -(Polynomial.C ((d : ℂ) * a) * X ^ d) := by
    rw [map_sub, Polynomial.derivative_one, zero_sub, Polynomial.derivative_C_mul_X_pow]
    have hXd : (X : ℂ[X]) * (Polynomial.C (a * (d : ℂ)) * X ^ (d - 1)) =
        Polynomial.C ((d : ℂ) * a) * X ^ d := by
      have h1 : (X : ℂ[X]) * X ^ (d - 1) = X ^ d := by
        rw [← pow_succ', Nat.sub_add_cancel hd]
      have hcomm : a * (d : ℂ) = (d : ℂ) * a := mul_comm a (d : ℂ)
      rw [hcomm]
      calc
        (X : ℂ[X]) * (Polynomial.C ((d : ℂ) * a) * X ^ (d - 1))
            = Polynomial.C ((d : ℂ) * a) * ((X : ℂ[X]) * X ^ (d - 1)) := by ring
        _ = Polynomial.C ((d : ℂ) * a) * X ^ d := by rw [h1]
    rw [mul_neg, hXd]
  rw [logDerivPoly, hderiv]
  have hrearr :
      (1 - Polynomial.C a * X ^ d) * (-(Polynomial.C ((d : ℂ) * a) * X ^ d) * truncGeom M a d) -
        -(Polynomial.C ((d : ℂ) * a) * X ^ d) =
      (Polynomial.C ((d : ℂ) * a) * X ^ d) *
        (1 - (1 - Polynomial.C a * X ^ d) * truncGeom M a d) := by ring
  rw [hrearr, hgeom, sub_sub_cancel]
  have hle : M + 1 ≤ (M + 1) * d := Nat.le_mul_of_pos_right (M + 1) (by omega)
  have hdvd : (X : ℂ[X]) ^ (M + 1) ∣ X ^ ((M + 1) * d) := pow_dvd_pow X hle
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hdvd _) _

/-- Abstract 2-factor product rule for `X^(M+1) ∣ f * D - X * f'`. -/
private lemma dvd_X_pow_mul_logDeriv (M : ℕ) (f₁ f₂ D₁ D₂ : ℂ[X])
    (h1 : (X : ℂ[X]) ^ (M + 1) ∣ f₁ * D₁ - X * Polynomial.derivative f₁)
    (h2 : (X : ℂ[X]) ^ (M + 1) ∣ f₂ * D₂ - X * Polynomial.derivative f₂) :
    (X : ℂ[X]) ^ (M + 1) ∣
      (f₁ * f₂) * (D₁ + D₂) - X * Polynomial.derivative (f₁ * f₂) := by
  rw [Polynomial.derivative_mul]
  have hid :
      (f₁ * f₂) * (D₁ + D₂) - X * (Polynomial.derivative f₁ * f₂ + f₁ * Polynomial.derivative f₂) =
      f₂ * (f₁ * D₁ - X * Polynomial.derivative f₁) +
        f₁ * (f₂ * D₂ - X * Polynomial.derivative f₂) := by ring
  rw [hid]
  exact dvd_add (dvd_mul_of_dvd_right h1 f₂) (dvd_mul_of_dvd_right h2 f₁)

private lemma dvd_X_pow_prod_logDeriv {ι : Type*} [DecidableEq ι] (M : ℕ) (s : Finset ι)
    (f D : ι → ℂ[X])
    (hstep : ∀ i ∈ s, (X : ℂ[X]) ^ (M + 1) ∣ f i * D i - X * Polynomial.derivative (f i)) :
    (X : ℂ[X]) ^ (M + 1) ∣
      (∏ i ∈ s, f i) * (∑ i ∈ s, D i) - X * Polynomial.derivative (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact dvd_X_pow_mul_logDeriv M (f a) (∏ i ∈ s, f i) (D a) (∑ i ∈ s, D i)
      (hstep a (Finset.mem_insert_self a s))
      (ih (fun i hi => hstep i (Finset.mem_insert_of_mem hi)))

private lemma logDerivPoly_coeff (M : ℕ) (a : ℂ) (d : ℕ) (hd : 1 ≤ d)
    (m : ℕ) (hm1 : 1 ≤ m) (hmM : m ≤ M) :
    (logDerivPoly M a d).coeff m =
      if d ∣ m then -((d : ℂ) * a ^ (m / d)) else 0 := by
  have hexp : logDerivPoly M a d =
      ∑ j ∈ Finset.range (M + 1),
        Polynomial.C (-((d : ℂ) * a ^ (j + 1))) * X ^ ((j + 1) * d) := by
    rw [logDerivPoly, truncGeom, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_succ', map_neg, map_mul, map_mul, map_mul]
    have he : (j + 1) * d = d + j * d := by ring
    rw [he, pow_add]; ring
  rw [hexp, Polynomial.finsetSum_coeff]
  split_ifs with hdvd
  · have hq_pos : 1 ≤ m / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (by omega)
    have hq_le : m / d - 1 < M + 1 := by
      have : m / d ≤ m := Nat.div_le_self m d
      omega
    rw [Finset.sum_eq_single (m / d - 1)]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Nat.sub_add_cancel hq_pos,
        Nat.div_mul_cancel hdvd, if_pos rfl, mul_one]
    · intro j _ hj
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      have hne : m ≠ (j + 1) * d := by
        intro heq
        have hdiv : m / d = j + 1 := by
          rw [heq, Nat.mul_div_cancel _ (by omega)]
        omega
      rw [if_neg hne, mul_zero]
    · intro hm; exact absurd (Finset.mem_range.mpr hq_le) hm
  · refine Finset.sum_eq_zero fun j _ => ?_
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    have hne : m ≠ (j + 1) * d := by
      intro heq
      exact hdvd ⟨j + 1, by linarith⟩
    rw [if_neg hne, mul_zero]

/-- **Polynomial Logarithmic-Derivative Identity** (for every `M ≥ 1`):
`-(α₁ ^ M + α₂ ^ M) = ∑_{π ∈ I_M, deg π ∣ M} deg π * χ̃(π)^(M / deg π)`. -/
theorem neg_pow_add_pow_eq_sum_irred (p M : ℕ) [Fact p.Prime] (hM : 1 ≤ M)
    (θ : GaloisField p 3) (hθ : θ ∉ Set.range (algebraMap (ZMod p) (GaloisField p 3)))
    (χ : (GaloisField p 3)ˣ →* ℂˣ) (hχ : ∃ u₀ : (GaloisField p 3)ˣ, χ u₀ ≠ 1)
    (α₁ α₂ : ℂ)
    (hfac : Lpoly p θ χ = (1 - Polynomial.C α₁ * X) * (1 - Polynomial.C α₂ * X)) :
    -(α₁ ^ M + α₂ ^ M) =
      ∑ π ∈ (irredMonicLe p M).filter (fun π => π.natDegree ∣ M),
        (π.natDegree : ℂ) * (charPoly p θ χ π) ^ (M / π.natDegree) := by
  classical
  set P_all : ℂ[X] := Lpoly p θ χ * eulerInv p M θ χ
  have hP_cong : (X : ℂ[X]) ^ (M + 1) ∣ P_all - 1 :=
    dvd_X_pow_Lpoly_mul_eulerInv_sub_one p M θ hθ χ hχ
  have hP_deriv : (X : ℂ[X]) ^ (M + 1) ∣ X * Polynomial.derivative P_all := by
    obtain ⟨Q, hQ⟩ := hP_cong
    have hP_eq : P_all = 1 + X ^ (M + 1) * Q := by linear_combination hQ
    rw [hP_eq, map_add, Polynomial.derivative_one, zero_add, Polynomial.derivative_mul,
      Polynomial.derivative_X_pow]
    refine ⟨Polynomial.C ((M + 1 : ℕ) : ℂ) * Q + X * Polynomial.derivative Q, ?_⟩
    have hX : (X : ℂ[X]) * X ^ M = X ^ (M + 1) := by rw [← pow_succ']
    calc
      (X : ℂ[X]) * (Polynomial.C ((M + 1 : ℕ) : ℂ) * X ^ M * Q + X ^ (M + 1) * Polynomial.derivative Q)
          = ((X : ℂ[X]) * X ^ M) * (Polynomial.C ((M + 1 : ℕ) : ℂ) * Q) +
              X ^ (M + 1) * (X * Polynomial.derivative Q) := by ring
      _ = X ^ (M + 1) * (Polynomial.C ((M + 1 : ℕ) : ℂ) * Q + X * Polynomial.derivative Q) := by
            rw [hX]; ring
  set S_log : ℂ[X] :=
    logDerivPoly M α₁ 1 + logDerivPoly M α₂ 1 +
      ∑ π ∈ irredMonicLe p M, logDerivPoly M (charPoly p θ χ π) π.natDegree
  have hE_log :
      (X : ℂ[X]) ^ (M + 1) ∣
        eulerInv p M θ χ * (∑ π ∈ irredMonicLe p M, logDerivPoly M (charPoly p θ χ π) π.natDegree) -
          X * Polynomial.derivative (eulerInv p M θ χ) := by
    refine dvd_X_pow_prod_logDeriv M (irredMonicLe p M)
      (fun π => 1 - Polynomial.C (charPoly p θ χ π) * X ^ π.natDegree)
      (fun π => logDerivPoly M (charPoly p θ χ π) π.natDegree) ?_
    intro π hπ
    have h1 : 1 ≤ π.natDegree := ((mem_irredMonicLe_iff p M π).mp hπ).2.2.1
    exact dvd_X_pow_factor_mul_logDerivPoly M (charPoly p θ χ π) π.natDegree h1
  have h1_log : (X : ℂ[X]) ^ (M + 1) ∣
      (1 - Polynomial.C α₁ * X) * logDerivPoly M α₁ 1 -
        X * Polynomial.derivative (1 - Polynomial.C α₁ * X) := by
    simpa [pow_one] using dvd_X_pow_factor_mul_logDerivPoly M α₁ 1 le_rfl
  have h2_log : (X : ℂ[X]) ^ (M + 1) ∣
      (1 - Polynomial.C α₂ * X) * logDerivPoly M α₂ 1 -
        X * Polynomial.derivative (1 - Polynomial.C α₂ * X) := by
    simpa [pow_one] using dvd_X_pow_factor_mul_logDerivPoly M α₂ 1 le_rfl
  have hL_log : (X : ℂ[X]) ^ (M + 1) ∣
      Lpoly p θ χ * (logDerivPoly M α₁ 1 + logDerivPoly M α₂ 1) -
        X * Polynomial.derivative (Lpoly p θ χ) := by
    rw [hfac]
    exact dvd_X_pow_mul_logDeriv M _ _ _ _ h1_log h2_log
  have hP_log : (X : ℂ[X]) ^ (M + 1) ∣ P_all * S_log - X * Polynomial.derivative P_all :=
    dvd_X_pow_mul_logDeriv M _ _ _ _ hL_log hE_log
  have hPS_dvd : (X : ℂ[X]) ^ (M + 1) ∣ P_all * S_log := by
    have h := dvd_add hP_log hP_deriv
    simpa using h
  have hS_dvd : (X : ℂ[X]) ^ (M + 1) ∣ S_log := by
    have h := dvd_sub hPS_dvd (dvd_mul_of_dvd_left hP_cong S_log)
    have hid : P_all * S_log - (P_all - 1) * S_log = S_log := by ring
    rwa [hid] at h
  have hcoeff0 : S_log.coeff M = 0 :=
    (Polynomial.X_pow_dvd_iff.mp hS_dvd) M (Nat.lt_succ_self M)
  simp only [S_log, Polynomial.coeff_add, Polynomial.finsetSum_coeff] at hcoeff0
  rw [logDerivPoly_coeff M α₁ 1 le_rfl M hM le_rfl,
      logDerivPoly_coeff M α₂ 1 le_rfl M hM le_rfl] at hcoeff0
  simp only [one_dvd, ↓reduceIte, Nat.cast_one, one_mul, Nat.div_one] at hcoeff0
  have hsum_coeff :
      (∑ π ∈ irredMonicLe p M, (logDerivPoly M (charPoly p θ χ π) π.natDegree).coeff M) =
      -(∑ π ∈ (irredMonicLe p M).filter (fun π => π.natDegree ∣ M),
          (π.natDegree : ℂ) * (charPoly p θ χ π) ^ (M / π.natDegree)) := by
    rw [← Finset.sum_neg_distrib, Finset.sum_filter]
    refine Finset.sum_congr rfl fun π hπ => ?_
    have h1 : 1 ≤ π.natDegree := ((mem_irredMonicLe_iff p M π).mp hπ).2.2.1
    rw [logDerivPoly_coeff M (charPoly p θ χ π) π.natDegree h1 M hM le_rfl]
  rw [hsum_coeff] at hcoeff0
  linear_combination hcoeff0




/-- Frobenius power acts as `x ↦ x^p` on `aeval` of polynomials over `ZMod p`. -/
private lemma aeval_pow_prime {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    [Algebra (ZMod p) K] (f : (ZMod p)[X]) (x : K) :
    Polynomial.aeval (x ^ p) f = (Polynomial.aeval x f) ^ p := by
  induction f using Polynomial.induction_on' with
  | add a b iha ihb =>
    rw [map_add, map_add, add_pow_char, iha, ihb]
  | monomial n c =>
    simp only [Polynomial.aeval_monomial, mul_pow, ← pow_mul, mul_comm p n]
    congr 1
    rw [← map_pow, ZMod.pow_card]

private lemma aeval_pow_prime_pow {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    [Algebra (ZMod p) K] (f : (ZMod p)[X]) (x : K) :
    ∀ j : ℕ, Polynomial.aeval (x ^ (p ^ j)) f = (Polynomial.aeval x f) ^ (p ^ j) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_mul, aeval_pow_prime, ih, pow_mul]

/-- Subtraction distributes over `p^j`-th powers in characteristic `p`. -/
private lemma sub_pow_char_pow' {K : Type*} [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (a b : K) (j : ℕ) : (a - b) ^ (p ^ j) = a ^ (p ^ j) - b ^ (p ^ j) := by
  have h : (a - b) ^ (p ^ j) + b ^ (p ^ j) = a ^ (p ^ j) := by
    rw [← add_pow_char_pow, sub_add_cancel]
  exact eq_sub_of_add_eq h

/-- Every monic irreducible polynomial `π ∈ (ZMod p)[X]` divides `X^(p^(deg π)) - X`. -/
private lemma irreducible_dvd_X_pow_pow_sub_X (p : ℕ) [Fact p.Prime] (π : (ZMod p)[X])
    (hm : π.Monic) (hirr : Irreducible π) :
    π ∣ (X : (ZMod p)[X]) ^ (p ^ π.natDegree) - X := by
  have : Fact (Irreducible π) := ⟨hirr⟩
  let pb := AdjoinRoot.powerBasis hirr.ne_zero
  have : Module.Finite (ZMod p) (AdjoinRoot π) := pb.finite
  have : Finite (AdjoinRoot π) := Module.finite_of_finite (ZMod p)
  let : Fintype (AdjoinRoot π) := Fintype.ofFinite _
  have hfin : Module.finrank (ZMod p) (AdjoinRoot π) = π.natDegree := by
    simpa [pb] using pb.finrank
  have hcard : Fintype.card (AdjoinRoot π) = p ^ π.natDegree := by
    rw [Module.card_eq_pow_finrank (K := ZMod p), hfin, ZMod.card]
  have hroot :
      Polynomial.aeval (AdjoinRoot.root π) ((X : (ZMod p)[X]) ^ (p ^ π.natDegree) - X) = 0 := by
    simp only [map_sub, map_pow, Polynomial.aeval_X, ← hcard, FiniteField.pow_card, sub_self]
  have hdvd := minpoly.dvd (ZMod p) (AdjoinRoot.root π) hroot
  rw [AdjoinRoot.minpoly_root hirr.ne_zero, hm.leadingCoeff, inv_one, map_one, mul_one] at hdvd
  exact hdvd

/-- Divisibility `X^(p^m) - X ∣ X^(p^n) - X` in `(ZMod p)[X]` whenever `m ∣ n` and `1 ≤ m`. -/
private lemma X_pow_pow_sub_X_dvd_of_dvd (p m n : ℕ) [Fact p.Prime] (_hm : 1 ≤ m) (hdvd : m ∣ n) :
    ((X : (ZMod p)[X]) ^ (p ^ m) - X) ∣ (X ^ (p ^ n) - X) := by
  obtain ⟨r, rfl⟩ := hdvd
  induction r with
  | zero => simp
  | succ r ih =>
    have hmul : p ^ (m * (r + 1)) = p ^ (m * r) * p ^ m := by
      rw [mul_add, mul_one, pow_add]
    have hsplit : (X : (ZMod p)[X]) ^ (p ^ (m * (r + 1))) - X =
        (X ^ (p ^ (m * r)) - X) ^ (p ^ m) + (X ^ (p ^ m) - X) := by
      rw [sub_pow_char_pow' p, ← pow_mul, ← hmul]
      ring
    rw [hsplit]
    have hq_pos : 1 ≤ p ^ m := Nat.one_le_pow m p (Fact.out : p.Prime).pos
    have hd1 : ((X : (ZMod p)[X]) ^ (p ^ m) - X) ∣ (X ^ (p ^ (m * r)) - X) ^ (p ^ m) :=
      dvd_pow ih (by omega)
    exact dvd_add hd1 dvd_rfl

/-- For any `t : GaloisField p n` (`n ≠ 0`), `(minpoly (ZMod p) t).natDegree ∣ n`. -/
private lemma minpoly_natDegree_dvd_of_galoisField (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0)
    (t : GaloisField p n) : (minpoly (ZMod p) t).natDegree ∣ n := by
  set π := minpoly (ZMod p) t
  have hint : IsIntegral (ZMod p) t := Algebra.IsIntegral.isIntegral t
  have hirr : Irreducible π := minpoly.irreducible hint
  have : Fact (Irreducible π) := ⟨hirr⟩
  let φ : AdjoinRoot π →ₐ[ZMod p] GaloisField p n :=
    AdjoinRoot.liftAlgHom π (Algebra.ofId (ZMod p) (GaloisField p n)) t
      (by simpa [Polynomial.aeval_def] using minpoly.aeval (ZMod p) t)
  let : Algebra (AdjoinRoot π) (GaloisField p n) := φ.toRingHom.toAlgebra
  have : IsScalarTower (ZMod p) (AdjoinRoot π) (GaloisField p n) :=
    IsScalarTower.of_algebraMap_eq' (φ.comp_algebraMap.symm)
  have hfin : Module.finrank (ZMod p) (AdjoinRoot π) = π.natDegree := by
    let pb := AdjoinRoot.powerBasis hirr.ne_zero
    simpa [pb] using pb.finrank
  have hmul := Module.finrank_mul_finrank (ZMod p) (AdjoinRoot π) (GaloisField p n)
  rw [hfin, GaloisField.finrank p hn] at hmul
  exact ⟨Module.finrank (AdjoinRoot π) (GaloisField p n), hmul.symm⟩

/-- Every monic irreducible `π ∈ (ZMod p)[X]` with `deg π ∣ n` has exactly `deg π` roots
(i.e. elements with `minpoly = π`) in `GaloisField p n`. -/
private lemma card_minpoly_fiber_eq_natDegree (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0)
    (π : (ZMod p)[X]) (hm : π.Monic) (hirr : Irreducible π)
    (hpos : 1 ≤ π.natDegree) (hdvd_n : π.natDegree ∣ n) :
    letI : Fintype (GaloisField p n) := Fintype.ofFinite _
    letI : DecidableEq (GaloisField p n) := Classical.decEq _
    (Finset.univ.filter fun t : GaloisField p n => minpoly (ZMod p) t = π).card = π.natDegree := by
  classical
  let K := GaloisField p n
  let : Fintype K := Fintype.ofFinite K
  have hcard : Nat.card K = p ^ n := GaloisField.card p n hn
  have hdvd1 : π ∣ (X : (ZMod p)[X]) ^ (p ^ π.natDegree) - X :=
    irreducible_dvd_X_pow_pow_sub_X p π hm hirr
  have hdvd2 : ((X : (ZMod p)[X]) ^ (p ^ π.natDegree) - X) ∣ (X ^ (p ^ n) - X) :=
    X_pow_pow_sub_X_dvd_of_dvd p π.natDegree n hpos hdvd_n
  set fK : K[X] := (X : K[X]) ^ (p ^ n) - X
  set πK : K[X] := π.map (algebraMap (ZMod p) K)
  have hdvdK : πK ∣ fK := by
    have hmap := Polynomial.map_dvd (algebraMap (ZMod p) K) (hdvd1.trans hdvd2)
    simpa [πK, fK, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X] using hmap
  have hfK_ne : fK ≠ 0 := by
    have hpn_gt : 1 < p ^ n := one_lt_pow₀ (Fact.out : p.Prime).one_lt hn
    have hdeg : fK.natDegree = p ^ n := by
      have hltX : (X : K[X]).natDegree < ((X : K[X]) ^ (p ^ n)).natDegree := by
        rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]; exact hpn_gt
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hltX, Polynomial.natDegree_X_pow]
    intro h0; rw [h0, Polynomial.natDegree_zero] at hdeg; omega
  have hfK_sep : fK.Separable := galois_poly_separable p (p ^ n) (dvd_pow_self p hn)
  have hfK_splits : fK.Splits := by
    have hsp := Polynomial.splits_X_pow_nat_card_sub_X (K := K)
    rw [hcard] at hsp
    exact hsp
  have hπK_sep : πK.Separable := hfK_sep.of_dvd hdvdK
  have hπK_splits : πK.Splits := hfK_splits.of_dvd hfK_ne hdvdK
  have hπK_nodup : πK.roots.Nodup := Polynomial.nodup_roots hπK_sep
  have hπK_ne : πK ≠ 0 := (hm.map (algebraMap (ZMod p) K)).ne_zero
  have hπK_deg : πK.natDegree = π.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (algebraMap (ZMod p) K).injective π
  have hset :
      (Finset.univ.filter fun t : K => minpoly (ZMod p) t = π) = πK.roots.toFinset := by
    ext t
    rw [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hπK_ne]
    simp only [Finset.mem_univ, true_and, Polynomial.IsRoot.def, πK, Polynomial.eval_map,
      ← Polynomial.aeval_def]
    constructor
    · intro heq
      rw [← heq]; exact minpoly.aeval (ZMod p) t
    · intro h0
      exact (minpoly.eq_of_irreducible_of_monic hirr h0 hm).symm
  rw [hset, Multiset.toFinset_card_of_nodup hπK_nodup, hπK_splits.natDegree_eq_card_roots.symm,
    hπK_deg]

/-- Minimal polynomial of `t : GaloisField p n` splits over `GaloisField p n` as the product
of `(X - C (t^(p^j)))` for `j < deg(minpoly t)`. -/
private lemma minpoly_map_eq_prod_frobenius (p n : ℕ) [Fact p.Prime] (_hn : n ≠ 0)
    (t : GaloisField p n) :
    (minpoly (ZMod p) t).map (algebraMap (ZMod p) (GaloisField p n)) =
      ∏ j ∈ Finset.range (minpoly (ZMod p) t).natDegree,
        (X - Polynomial.C (t ^ (p ^ j))) := by
  classical
  let K := GaloisField p n
  set π := minpoly (ZMod p) t
  set m := π.natDegree
  have hint : IsIntegral (ZMod p) t := Algebra.IsIntegral.isIntegral t
  have hmon : π.Monic := minpoly.monic hint
  have hirr : Irreducible π := minpoly.irreducible hint
  have hroot_j : ∀ j : ℕ, (π.map (algebraMap (ZMod p) K)).IsRoot (t ^ (p ^ j)) := by
    intro j
    rw [Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def, aeval_pow_prime_pow]
    simp only [π, minpoly.aeval, zero_pow (pow_ne_zero j (Fact.out : p.Prime).ne_zero)]
  have hinj : ∀ i ∈ Finset.range m, ∀ j ∈ Finset.range m,
      t ^ (p ^ i) = t ^ (p ^ j) → i = j := by
    suffices hlt : ∀ a b : ℕ, a < b → b < m → t ^ (p ^ a) ≠ t ^ (p ^ b) by
      intro i hi j hj heq
      have hi' : i < m := Finset.mem_range.mp hi
      have hj' : j < m := Finset.mem_range.mp hj
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact hlt i j h hj' heq
      · exact hlt j i h hi' heq.symm
    intro a b hab hbm heq
    set s := b - a
    have hs_pos : 0 < s := by omega
    have hs_lt : s < m := by omega
    have hfix_t : t ^ (p ^ s) = t := by
      have hpow : (t ^ (p ^ s) - t) ^ (p ^ a) = 0 := by
        rw [sub_pow_char_pow' p, ← pow_mul, ← pow_add, show s + a = b by omega, heq, sub_self]
      exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hpow)
    -- Fixed field `{x : K | x^(p^s) = x}` is a `ZMod p`-subalgebra of cardinality `≤ p^s`
    let Sfix : Subalgebra (ZMod p) K :=
      { carrier := {x : K | x ^ (p ^ s) = x}
        mul_mem' := fun {x y} hx hy => by
          show (x * y) ^ (p ^ s) = x * y
          rw [mul_pow, hx, hy]
        one_mem' := by show (1 : K) ^ (p ^ s) = 1; exact one_pow _
        add_mem' := fun {x y} hx hy => by
          show (x + y) ^ (p ^ s) = x + y
          rw [add_pow_char_pow, hx, hy]
        zero_mem' := by
          show (0 : K) ^ (p ^ s) = 0
          exact zero_pow (pow_ne_zero s (Fact.out : p.Prime).ne_zero)
        algebraMap_mem' := fun c => by
          show (algebraMap (ZMod p) K c) ^ (p ^ s) = algebraMap (ZMod p) K c
          rw [← map_pow, ZMod.pow_card_pow] }
    let : Fintype Sfix := Fintype.ofFinite _
    have hcard_Sfix : Fintype.card Sfix ≤ p ^ s := by
      set g_s : K[X] := X ^ (p ^ s) - X
      have hps_gt : 1 < p ^ s := one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega)
      have hdeg_s : g_s.natDegree = p ^ s := by
        have hltX : (X : K[X]).natDegree < ((X : K[X]) ^ (p ^ s)).natDegree := by
          rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]; exact hps_gt
        rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hltX, Polynomial.natDegree_X_pow]
      have hg_ne : g_s ≠ 0 := by
        intro h0; rw [h0, Polynomial.natDegree_zero] at hdeg_s; omega
      have hsub : (Finset.univ.image (fun x : Sfix => (x : K))) ⊆ g_s.roots.toFinset := by
        intro y hy
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hg_ne, Polynomial.IsRoot.def]
        simp only [g_s, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
        exact sub_eq_zero.mpr x.2
      calc
        Fintype.card Sfix = (Finset.univ.image (fun x : Sfix => (x : K))).card := by
          rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ]
        _ ≤ g_s.roots.toFinset.card := Finset.card_le_card hsub
        _ ≤ g_s.roots.card := Multiset.toFinset_card_le _
        _ ≤ g_s.natDegree := Polynomial.card_roots' g_s
        _ = p ^ s := hdeg_s
    have : Fact (Irreducible π) := ⟨hirr⟩
    let pb := AdjoinRoot.powerBasis hirr.ne_zero
    have : Module.Finite (ZMod p) (AdjoinRoot π) := pb.finite
    have : Finite (AdjoinRoot π) := Module.finite_of_finite (ZMod p)
    let : Fintype (AdjoinRoot π) := Fintype.ofFinite _
    have hcard_Ad : Fintype.card (AdjoinRoot π) = p ^ m := by
      have hfin : Module.finrank (ZMod p) (AdjoinRoot π) = m := by simpa [pb] using pb.finrank
      rw [Module.card_eq_pow_finrank (K := ZMod p), hfin, ZMod.card]
    let tS : Sfix := ⟨t, hfix_t⟩
    have haev_S : Polynomial.eval₂ (Algebra.ofId (ZMod p) Sfix) tS π = 0 := by
      apply Subtype.ext
      have h := minpoly.aeval (ZMod p) t
      rw [Polynomial.aeval_def] at h
      have hval : ((Polynomial.eval₂ (Algebra.ofId (ZMod p) Sfix) tS π : Sfix) : K) =
          Polynomial.eval₂ (algebraMap (ZMod p) K) t π := by
        change (Sfix.val : Sfix →+* K) (Polynomial.eval₂ (Algebra.ofId (ZMod p) Sfix) tS π) = _
        rw [Polynomial.hom_eval₂]
        rfl
      rw [hval, h]; rfl
    let emb : AdjoinRoot π →ₐ[ZMod p] Sfix :=
      AdjoinRoot.liftAlgHom π (Algebra.ofId (ZMod p) Sfix) tS haev_S
    have hemb_inj : Function.Injective emb := emb.toRingHom.injective
    have hle_card : p ^ m ≤ p ^ s := by
      rw [← hcard_Ad]
      exact (Fintype.card_le_of_injective emb hemb_inj).trans hcard_Sfix
    have hm_le_s : m ≤ s :=
      (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hle_card
    omega
  set Q : K[X] := ∏ j ∈ Finset.range m, (X - Polynomial.C (t ^ (p ^ j)))
  have hQ_mon : Q.Monic :=
    Polynomial.monic_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C _
  have hQ_deg : Q.natDegree = m := by
    rw [Polynomial.natDegree_prod_of_monic (Finset.range m)
      (fun j => (X - Polynomial.C (t ^ (p ^ j)) : K[X]))
      (fun j _ => Polynomial.monic_X_sub_C _)]
    simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul,
      mul_one]
  have hπK_mon : (π.map (algebraMap (ZMod p) K)).Monic := hmon.map _
  have hπK_deg : (π.map (algebraMap (ZMod p) K)).natDegree = m :=
    Polynomial.natDegree_map_eq_of_injective (algebraMap (ZMod p) K).injective π
  have hQ_dvd : Q ∣ π.map (algebraMap (ZMod p) K) := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro i hi j hj hij
      exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (IsUnit.mk0 _ (sub_ne_zero.mpr fun heq => hij (hinj i hi j hj heq)))
    · intro j _
      exact Polynomial.dvd_iff_isRoot.mpr (hroot_j j)
  obtain ⟨R, hR⟩ := hQ_dvd
  have hR_mon : R.Monic := Polynomial.Monic.of_mul_monic_left hQ_mon (hR ▸ hπK_mon)
  have hR_deg : R.natDegree = 0 := by
    have h1 : (Q * R).natDegree = Q.natDegree + R.natDegree :=
      Polynomial.natDegree_mul hQ_mon.ne_zero hR_mon.ne_zero
    rw [← hR, hπK_deg, hQ_deg] at h1
    omega
  have hR1 : R = 1 := Polynomial.eq_one_of_monic_natDegree_zero hR_mon hR_deg
  rw [hR, hR1, mul_one]

/-- Geometric sum identity `(b - 1) * ∑_{j < k} b^j = b^k - 1` for `b ≥ 2`. -/
private lemma geom_sum_eq_div_nat (b k : ℕ) (hb : 2 ≤ b) :
    ∑ j ∈ Finset.range k, b ^ j = (b ^ k - 1) / (b - 1) := by
  have hmul : (b - 1) * ∑ j ∈ Finset.range k, b ^ j = b ^ k - 1 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      have h1 : 1 ≤ b ^ k := Nat.one_le_pow k b (by omega)
      have h2 : 1 ≤ b := by omega
      have h3 : (b - 1) * b ^ k = b ^ (k + 1) - b ^ k := by
        zify [h2, h1, show b ^ k ≤ b ^ (k + 1) from Nat.le_mul_of_pos_right _ (by omega)]
        rw [pow_succ]; ring
      rw [h3]
      have h4 : b ^ k ≤ b ^ (k + 1) := by
        rw [pow_succ]; exact Nat.le_mul_of_pos_right _ (by omega)
      omega
  rw [← hmul, Nat.mul_div_cancel_left _ (by omega)]

/-- Divisibility `(b - 1) ∣ (b ^ k - 1)` for all `b ≥ 2`. -/
private lemma sub_one_dvd_pow_sub_one (b k : ℕ) (hb : 2 ≤ b) : (b - 1) ∣ (b ^ k - 1) := by
  refine ⟨∑ j ∈ Finset.range k, b ^ j, ?_⟩
  induction k with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ← ih]
    have hm1 : 1 ≤ b ^ m := Nat.one_le_pow m b (by omega)
    have hm2 : b ^ m ≤ b ^ (m + 1) := by rw [pow_succ]; exact Nat.le_mul_of_pos_right _ (by omega)
    have hstep : (b - 1) * b ^ m = b ^ (m + 1) - b ^ m := by
      have hb1 : 1 ≤ b := by omega
      zify [hb1, hm2]; rw [pow_succ]; ring
    rw [hstep]; omega

/-- Exact Frobenius/norm identity for each `t : GaloisField p (3 * k)`:
`(aeval θ (minpoly t)) ^ (3*k / deg) = N(ι θ - t) * N(ι(θ^(p^2)) - t)^p * N(ι(θ^p) - t)^(p^2)`. -/
private lemma minpoly_pow_eval_eq_norm_prod (p k : ℕ) [Fact p.Prime] (hk : 1 ≤ k)
    (ι : GaloisField p 3 →ₐ[ZMod p] GaloisField p (3 * k))
    (θ : GaloisField p 3) (t : GaloisField p (3 * k)) :
    letI : Algebra (GaloisField p 3) (GaloisField p (3 * k)) := ι.toRingHom.toAlgebra
    (Polynomial.aeval θ (minpoly (ZMod p) t)) ^ ((3 * k) / (minpoly (ZMod p) t).natDegree) =
      Algebra.norm (GaloisField p 3) (ι θ - t) *
        (Algebra.norm (GaloisField p 3) (ι (θ ^ (p ^ 2)) - t)) ^ p *
        (Algebra.norm (GaloisField p 3) (ι (θ ^ p) - t)) ^ (p ^ 2) := by
  classical
  let E := GaloisField p 3
  let K := GaloisField p (3 * k)
  let : Algebra E K := ι.toRingHom.toAlgebra
  set π := minpoly (ZMod p) t
  set m := π.natDegree
  set r := (3 * k) / m
  have hint : IsIntegral (ZMod p) t := Algebra.IsIntegral.isIntegral t
  have hmon : π.Monic := minpoly.monic hint
  have hirr : Irreducible π := minpoly.irreducible hint
  have hm_pos : 0 < m := minpoly.natDegree_pos hint
  have hm_dvd : m ∣ 3 * k := minpoly_natDegree_dvd_of_galoisField p (3 * k) (by omega) t
  have hrm : r * m = 3 * k := Nat.div_mul_cancel hm_dvd
  have ht_fix : t ^ (p ^ m) = t := by
    have hdvd := irreducible_dvd_X_pow_pow_sub_X p π hmon hirr
    obtain ⟨q, hq⟩ := hdvd
    have h0 := congrArg (Polynomial.aeval t) hq
    simp only [map_sub, map_pow, map_mul, Polynomial.aeval_X, π, minpoly.aeval, zero_mul] at h0
    exact sub_eq_zero.mp h0
  have ht_per : ∀ q' j : ℕ, t ^ (p ^ (q' * m + j)) = t ^ (p ^ j) := by
    intro q'
    induction q' with
    | zero => intro j; simp
    | succ q' ih =>
      intro j
      have hexp : (q' + 1) * m + j = m + (q' * m + j) := by ring
      rw [hexp, pow_add, pow_mul, ht_fix, ih j]
  -- Step 1: `(π.map _) ^ r = ∏ i ∈ range (3*k), (X - C (t^(p^i)))`
  have hpoly_pow :
      (π.map (algebraMap (ZMod p) K)) ^ r =
        ∏ i ∈ Finset.range (3 * k), (X - Polynomial.C (t ^ (p ^ i))) := by
    rw [minpoly_map_eq_prod_frobenius p (3 * k) (by omega) t]
    have hbij :
        ∏ i ∈ Finset.range (3 * k), (X - Polynomial.C (t ^ (p ^ i))) =
        ∏ q' ∈ Finset.range r, ∏ j ∈ Finset.range m, (X - Polynomial.C (t ^ (p ^ (q' * m + j)))) := by
      rw [← Finset.prod_product']
      symm
      refine Finset.prod_nbij (fun qj : ℕ × ℕ => qj.1 * m + qj.2) ?_ ?_ ?_ ?_
      · intro ⟨q', j⟩ hqj
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hqj
        rw [Finset.mem_range]
        have : (q' + 1) * m ≤ r * m := Nat.mul_le_mul_right m hqj.1
        nlinarith
      · intro ⟨q₁, j₁⟩ h1 ⟨q₂, j₂⟩ h2 heq
        rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_range] at h1 h2
        dsimp only at heq
        have hqeq : q₁ = q₂ := by
          have d1 : (q₁ * m + j₁) / m = q₁ := by
            rw [mul_comm q₁ m, Nat.mul_add_div hm_pos, Nat.div_eq_of_lt h1.2, add_zero]
          have d2 : (q₂ * m + j₂) / m = q₂ := by
            rw [mul_comm q₂ m, Nat.mul_add_div hm_pos, Nat.div_eq_of_lt h2.2, add_zero]
          rw [← d1, ← d2, heq]
        subst hqeq
        exact Prod.ext rfl (by omega)
      · intro i hi
        rw [Finset.mem_coe, Finset.mem_range] at hi
        refine ⟨(i / m, i % m), ?_, ?_⟩
        · rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_range]
          refine ⟨?_, Nat.mod_lt i hm_pos⟩
          exact Nat.div_lt_of_lt_mul (by rwa [mul_comm, hrm])
        · dsimp only; rw [mul_comm, Nat.div_add_mod]
      · intro _ _; rfl
    rw [hbij]
    have hconst : ∀ q' ∈ Finset.range r,
        (∏ j ∈ Finset.range m, (X - Polynomial.C (t ^ (p ^ (q' * m + j))))) =
        (∏ j ∈ Finset.range m, (X - Polynomial.C (t ^ (p ^ j)))) := by
      intro q' _
      refine Finset.prod_congr rfl fun j _ => by rw [ht_per q' j]
    rw [Finset.prod_congr rfl hconst, Finset.prod_const, Finset.card_range]
  -- Step 2: Evaluate at `ι θ` and apply injectivity of `ι`
  apply ι.injective
  change ι _ = ι _
  have hLHS : ι ((Polynomial.aeval θ π) ^ r) =
      ((π.map (algebraMap (ZMod p) K)) ^ r).eval (ι θ) := by
    rw [map_pow, Polynomial.eval_pow, Polynomial.eval_map, ← Polynomial.aeval_def]
    congr 1
    rw [Polynomial.aeval_algHom_apply]
  rw [hLHS, hpoly_pow, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  -- Step 3: Split `Finset.range (3 * k)` into residues `0, 1, 2` mod 3
  have hsplit3 :
      (∏ i ∈ Finset.range (3 * k), (ι θ - t ^ (p ^ i))) =
      (∏ j ∈ Finset.range k, (ι θ - t ^ (p ^ (3 * j)))) *
      (∏ j ∈ Finset.range k, (ι θ - t ^ (p ^ (3 * j + 1)))) *
      (∏ j ∈ Finset.range k, (ι θ - t ^ (p ^ (3 * j + 2)))) := by
    have h3 :
        (∏ i ∈ Finset.range (3 * k), (ι θ - t ^ (p ^ i))) =
        ∏ r₀ ∈ Finset.range 3, ∏ j ∈ Finset.range k, (ι θ - t ^ (p ^ (3 * j + r₀))) := by
      rw [← Finset.prod_product']
      symm
      refine Finset.prod_nbij (fun rj : ℕ × ℕ => 3 * rj.2 + rj.1) ?_ ?_ ?_ ?_
      · intro ⟨r₀, j⟩ hrj
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hrj
        rw [Finset.mem_range]; omega
      · intro ⟨r₁, j₁⟩ h1 ⟨r₂, j₂⟩ h2 heq
        rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_range] at h1 h2
        dsimp only at heq
        exact Prod.ext (by omega) (by omega)
      · intro i hi
        rw [Finset.mem_coe, Finset.mem_range] at hi
        refine ⟨(i % 3, i / 3), ?_, ?_⟩
        · rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_range]
          exact ⟨Nat.mod_lt i (by norm_num), by omega⟩
        · dsimp only; omega
      · intro _ _; rfl
    rw [h3, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_one]
    simp only [add_zero]
  -- Step 4: Identify each of the 3 products with `ι (Algebra.norm E ...)`
  have hθ_fix : θ ^ (p ^ 3) = θ := by
    let : Fintype E := Fintype.ofFinite E
    have hc : Fintype.card E = p ^ 3 := by
      rw [Fintype.card_eq_nat_card, GaloisField.card p 3 (by norm_num)]
    have h := FiniteField.pow_card θ
    rwa [hc] at h
  have hθ_fix_j : ∀ j : ℕ, (ι θ) ^ (p ^ (3 * j)) = ι θ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [mul_add, mul_one, pow_add, pow_mul, ih, ← map_pow, hθ_fix]
  have hnorm_prod : ∀ x : K,
      ∏ j ∈ Finset.range k, x ^ (p ^ (3 * j)) = ι (Algebra.norm E x) := by
    intro x
    rw [Finset.prod_pow_eq_pow_sum]
    have hsum : ∑ j ∈ Finset.range k, p ^ (3 * j) = (Nat.card K - 1) / (Nat.card E - 1) := by
      rw [GaloisField.card p (3 * k) (by omega), GaloisField.card p 3 (by norm_num)]
      have hge2 : 2 ≤ p ^ 3 := by
        have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
        have : 2 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hp2 3
        omega
      have hrew : ∑ j ∈ Finset.range k, p ^ (3 * j) = ∑ j ∈ Finset.range k, (p ^ 3) ^ j := by
        refine Finset.sum_congr rfl fun j _ => by rw [pow_mul]
      rw [hrew, geom_sum_eq_div_nat (p ^ 3) k hge2, ← pow_mul]
    rw [hsum]
    exact (FiniteField.algebraMap_norm_eq_pow (K := E) (K' := K) (x := x)).symm
  have hP0 : (∏ j ∈ Finset.range k, (ι θ - t ^ (p ^ (3 * j)))) = ι (Algebra.norm E (ι θ - t)) := by
    rw [← hnorm_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [sub_pow_char_pow' p, hθ_fix_j j]
  have hP1 : (∏ j ∈ Finset.range k, (ι θ - t ^ (p ^ (3 * j + 1)))) =
      ι ((Algebra.norm E (ι (θ ^ (p ^ 2)) - t)) ^ p) := by
    rw [map_pow, ← hnorm_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [sub_pow_char_pow' p, show (ι (θ ^ p ^ 2) ^ p ^ (3 * j) - t ^ p ^ (3 * j)) ^ p =
        (ι (θ ^ p ^ 2) ^ p ^ (3 * j) - t ^ p ^ (3 * j)) ^ (p ^ 1) by rw [pow_one],
      sub_pow_char_pow' p, pow_one, ← pow_mul, ← pow_mul]
    have h1 : p ^ (3 * j) * p = p ^ (3 * j + 1) := by rw [pow_succ]
    rw [h1]
    congr 1
    rw [← map_pow, ← pow_mul]
    have h2 : p ^ 2 * p ^ (3 * j + 1) = p ^ (3 * (j + 1)) := by
      rw [← pow_add]; congr 1; ring
    rw [h2, map_pow, hθ_fix_j (j + 1)]
  have hP2 : (∏ j ∈ Finset.range k, (ι θ - t ^ (p ^ (3 * j + 2)))) =
      ι ((Algebra.norm E (ι (θ ^ p) - t)) ^ (p ^ 2)) := by
    rw [map_pow, ← hnorm_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [sub_pow_char_pow' p, sub_pow_char_pow' p, ← pow_mul, ← pow_mul]
    have h1 : p ^ (3 * j) * p ^ 2 = p ^ (3 * j + 2) := by rw [← pow_add]
    rw [h1]
    congr 1
    rw [← map_pow, ← pow_mul]
    have h2 : p * p ^ (3 * j + 2) = p ^ (3 * (j + 1)) := by
      rw [← pow_succ' p (3 * j + 2), show 3 * j + 2 + 1 = 3 * (j + 1) by ring]
    rw [h2, map_pow, hθ_fix_j (j + 1)]
  rw [hsplit3, hP0, hP1, hP2, map_mul, map_mul]

/-- If `θ ∈ GaloisField p 3` is not in the prime field `ZMod p`, then `θ^p ≠ θ` and `θ^(p^2) ≠ θ`. -/
private lemma frobenius_ne_self_of_not_mem_range (p : ℕ) [Fact p.Prime] (θ : GaloisField p 3)
    (hθ : θ ∉ Set.range (algebraMap (ZMod p) (GaloisField p 3))) :
    θ ^ p ≠ θ ∧ θ ^ (p ^ 2) ≠ θ := by
  classical
  have hp_ne : θ ^ p ≠ θ := by
    intro hfp
    let E := GaloisField p 3
    set f : E[X] := X ^ p - X
    have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
    have hf_deg : f.natDegree = p := by
      have hlt : (X : E[X]).natDegree < ((X : E[X]) ^ p).natDegree := by
        rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]; exact hp1
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, Polynomial.natDegree_X_pow]
    have hf_ne : f ≠ 0 := by intro h0; rw [h0, Polynomial.natDegree_zero] at hf_deg; omega
    let img : Finset E := Finset.univ.image (algebraMap (ZMod p) E)
    have himg_card : img.card = p := by
      rw [Finset.card_image_of_injective _ (algebraMap (ZMod p) E).injective, Finset.card_univ,
        ZMod.card]
    have hθ_not_img : θ ∉ img := by
      intro hmem
      obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hmem
      exact hθ ⟨c, hc⟩
    have hsub : insert θ img ⊆ f.roots.toFinset := by
      intro x hx
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hf_ne, Polynomial.IsRoot.def]
      simp only [f, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact sub_eq_zero.mpr hfp
      · obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hx'
        rw [← map_pow, ZMod.pow_card, sub_self]
    have hle : p + 1 ≤ p := by
      calc
        p + 1 = (insert θ img).card := by rw [Finset.card_insert_of_notMem hθ_not_img, himg_card]
        _ ≤ f.roots.toFinset.card := Finset.card_le_card hsub
        _ ≤ f.roots.card := Multiset.toFinset_card_le _
        _ ≤ f.natDegree := Polynomial.card_roots' f
        _ = p := hf_deg
    omega
  refine ⟨hp_ne, ?_⟩
  intro hfp2
  apply hp_ne
  let : Fintype (GaloisField p 3) := Fintype.ofFinite _
  have hc : Fintype.card (GaloisField p 3) = p ^ 3 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card p 3 (by norm_num)]
  have h3 : θ ^ (p ^ 3) = θ := by simpa [hc] using FiniteField.pow_card θ
  have := congrArg (fun x => x ^ p) hfp2
  rw [← pow_mul, ← pow_succ, h3] at this
  exact this.symm

/-- **Katz Degree-3 Multiplicative Character-Sum Bound**:
For any prime `p`, `θ ∈ GaloisField p 3 \ F_p`, and nontrivial multiplicative character
`χ : (GaloisField p 3)ˣ →* ℂˣ`,
`‖∑ t : ZMod p, charZero χ (θ + algebraMap (ZMod p) (GaloisField p 3) t)‖ ≤ 2 * √p`. -/
theorem katz_deg3_bound (p : ℕ) [Fact p.Prime]
    (θ : GaloisField p 3) (hθ : θ ∉ Set.range (algebraMap (ZMod p) (GaloisField p 3)))
    (χ : (GaloisField p 3)ˣ →* ℂˣ) (hχ : ∃ u₀ : (GaloisField p 3)ˣ, χ u₀ ≠ 1) :
    letI : DecidableEq (GaloisField p 3) := Classical.decEq _
    ‖∑ t : ZMod p, charZero χ (θ + algebraMap (ZMod p) (GaloisField p 3) t)‖ ≤
      2 * Real.sqrt (p : ℝ) := by
  classical
  let E := GaloisField p 3
  let : Fintype E := Fintype.ofFinite E
  have hE_card : Fintype.card E = p ^ 3 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card p 3 (by norm_num)]
  obtain ⟨α₁, α₂, hsum_α, hfac_L⟩ :=
    exists_quadratic_factor_complex (Lcoeff p θ χ 1) (Lcoeff p θ χ 2)
  have hL1 : -(α₁ + α₂) = ∑ t : ZMod p, charZero χ (θ + algebraMap (ZMod p) E t) := by
    rw [hsum_α, Lcoeff_one]
  rw [← hL1, norm_neg]
  set d : ℕ := p ^ 3 - 1
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hd_ge2 : 2 ≤ d := by
    have : 2 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hp2 3
    omega
  have hR_pos : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (Fact.out : p.Prime).pos)
  refine norm_add_le_two_mul_of_pow_three_mul (R := Real.sqrt (p : ℝ))
    (C := 40 * (d : ℝ) ^ 6 + 3 * (d : ℝ) ^ 2) hR_pos ?_
  -- Choose `K₀ ≥ 1` large enough that `(32 * d^5)^2 ≤ p^(3*k)` for all `k ≥ K₀`
  refine ⟨max 1 ((32 * d ^ 5) ^ 2), fun k hk => ?_⟩
  have hk1 : 1 ≤ k := (le_max_left _ _).trans hk
  have hk_big : (32 * d ^ 5) ^ 2 ≤ k := (le_max_right _ _).trans hk
  have hq_big : (32 * d ^ 5) ^ 2 ≤ p ^ (3 * k) := by
    have h1 : k ≤ 3 * k := by omega
    have h2 : 3 * k < 2 ^ (3 * k) := Nat.lt_two_pow_self
    have h3 : 2 ^ (3 * k) ≤ p ^ (3 * k) := Nat.pow_le_pow_left hp2 (3 * k)
    omega
  let K := GaloisField p (3 * k)
  let : Fintype K := Fintype.ofFinite K
  have hK_card : Fintype.card K = p ^ (3 * k) := by
    rw [Fintype.card_eq_nat_card, GaloisField.card p (3 * k) (by omega)]
  -- Embed `E →ₐ[ZMod p] K`
  have hfin_dvd : Module.finrank (ZMod p) E ∣ Module.finrank (ZMod p) K := by
    rw [GaloisField.finrank p (by norm_num), GaloisField.finrank p (by omega)]
    exact ⟨k, rfl⟩
  obtain ⟨ι⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hfin_dvd
  let : Algebra E K := ι.toRingHom.toAlgebra
  -- Pull back `χ` via norm `N_{K/E}`
  let ψ : Kˣ →* ℂˣ := χ.comp (Units.map (Algebra.norm E (S := K)))
  have hψ_ne : ∃ x : Kˣ, ψ x ≠ 1 := by
    obtain ⟨u₀, hu₀⟩ := hχ
    obtain ⟨x₀, hx₀⟩ := FiniteField.unitsMap_norm_surjective E K u₀
    exact ⟨x₀, by simpa [ψ, hx₀] using hu₀⟩
  have hψ_pow : ∀ x : Kˣ, (ψ x : ℂ) ^ d = 1 := by
    intro x
    have hcardE : Fintype.card Eˣ = d := by rw [Fintype.card_units, hE_card]
    have hy : (Units.map (Algebra.norm E (S := K)) x) ^ d = 1 := by
      rw [← hcardE]; exact pow_card_eq_one
    have hψd : (ψ x) ^ d = 1 := by
      simp only [ψ, MonoidHom.comp_apply, ← map_pow, hy, map_one]
    rw [← Units.val_pow_eq_pow_val, hψd, Units.val_one]
  have hchar_norm : ∀ x : K, charZero χ (Algebra.norm E x) = charZero ψ x := by
    intro x
    by_cases hx : x = 0
    · subst hx
      have hnorm0 : Algebra.norm E (0 : K) = 0 := by
        apply ι.injective
        have hpos_exp : 0 < (Nat.card K - 1) / (Nat.card E - 1) := by
          rw [GaloisField.card p (3 * k) (by omega), GaloisField.card p 3 (by norm_num)]
          have h1 : p ^ 3 - 1 ≤ p ^ (3 * k) - 1 :=
            Nat.sub_le_sub_right (Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)) 1
          exact Nat.div_pos h1 (by omega)
        change algebraMap E K (Algebra.norm E (0 : K)) = algebraMap E K 0
        rw [FiniteField.algebraMap_norm_eq_pow (K := E) (K' := K) (x := (0 : K)),
          zero_pow hpos_exp.ne', map_zero]
      rw [hnorm0, map_zero, map_zero]
    · have h1 : charZero χ (Algebra.norm E x) =
          (χ (Units.map (Algebra.norm E (S := K)) (Units.mk0 x hx)) : ℂ) := by
        simpa using charZero_apply_unit χ (Units.map (Algebra.norm E (S := K)) (Units.mk0 x hx))
      have h2 : charZero ψ x = (ψ (Units.mk0 x hx) : ℂ) := by
        simpa using charZero_apply_unit ψ (Units.mk0 x hx)
      rw [h1, h2]
      rfl
  -- Step A: Trace formula `-(α₁^(3k) + α₂^(3k)) = ∑ t : K, charZero ψ ((ι θ - t) * (ι(θ^(p^2)) - t)^p * (ι(θ^p) - t)^(p^2))`
  have htrace :
      -(α₁ ^ (3 * k) + α₂ ^ (3 * k)) =
        ∑ t : K, charZero ψ
          ((ι θ - t) * (ι (θ ^ (p ^ 2)) - t) ^ p * (ι (θ ^ p) - t) ^ (p ^ 2)) := by
    rw [neg_pow_add_pow_eq_sum_irred p (3 * k) (by omega) θ hθ χ hχ α₁ α₂ hfac_L]
    have hfib :
        ∑ t : K, (charPoly p θ χ (minpoly (ZMod p) t)) ^ ((3 * k) / (minpoly (ZMod p) t).natDegree) =
        ∑ π ∈ (irredMonicLe p (3 * k)).filter (fun π => π.natDegree ∣ 3 * k),
          (π.natDegree : ℂ) * (charPoly p θ χ π) ^ ((3 * k) / π.natDegree) := by
      have hmaps : ∀ t ∈ (Finset.univ : Finset K),
          minpoly (ZMod p) t ∈ (irredMonicLe p (3 * k)).filter (fun π => π.natDegree ∣ 3 * k) := by
        intro t _
        have hint : IsIntegral (ZMod p) t := Algebra.IsIntegral.isIntegral t
        have hdvd := minpoly_natDegree_dvd_of_galoisField p (3 * k) (by omega) t
        rw [Finset.mem_filter, mem_irredMonicLe_iff]
        exact ⟨⟨minpoly.monic hint, minpoly.irreducible hint, minpoly.natDegree_pos hint,
          Nat.le_of_dvd (by omega) hdvd⟩, hdvd⟩
      rw [← Finset.sum_fiberwise_of_maps_to hmaps]
      refine Finset.sum_congr rfl fun π hπ => ?_
      have hfilt := Finset.mem_filter.mp hπ
      have ⟨hm, hirr, hpos, _⟩ := (mem_irredMonicLe_iff p (3 * k) π).mp hfilt.1
      have hconst : ∀ t ∈ Finset.univ.filter (fun t : K => minpoly (ZMod p) t = π),
          (charPoly p θ χ (minpoly (ZMod p) t)) ^ ((3 * k) / (minpoly (ZMod p) t).natDegree) =
            (charPoly p θ χ π) ^ ((3 * k) / π.natDegree) := by
        intro t ht
        rw [(Finset.mem_filter.mp ht).2]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
      have hcard_f := card_minpoly_fiber_eq_natDegree p (3 * k) (by omega) π hm hirr hpos hfilt.2
      rw [hcard_f]
    rw [← hfib]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hnorm_id := minpoly_pow_eval_eq_norm_prod p k hk1 ι θ t
    change (charZero χ (Polynomial.aeval θ (minpoly (ZMod p) t))) ^
        ((3 * k) / (minpoly (ZMod p) t).natDegree) = _
    rw [← map_pow (charZero χ), hnorm_id, map_mul (charZero χ), map_mul (charZero χ),
      map_pow (charZero χ), map_pow (charZero χ)]
    have hcn : ∀ x : K, charZero χ (Algebra.norm (GaloisField p 3) x) = charZero ψ x := hchar_norm
    rw [hcn, hcn, hcn, ← map_pow (charZero ψ), ← map_pow (charZero ψ),
      ← map_mul (charZero ψ), ← map_mul (charZero ψ)]
  -- Step B: Möbius substitution `t = ι θ - u⁻¹` into `g(u)` of degree `3*d - 1`
  have h1pp2_le : 1 + p + p ^ 2 ≤ d := by
    have hfac_p : (p - 1) * (1 + p + p ^ 2) = p ^ 3 - 1 := by
      have hp1 : 1 ≤ p := by omega
      have hp3 : 1 ≤ p ^ 3 := Nat.one_le_pow 3 p (by omega)
      zify [hp1, hp3]; ring
    have h1 : 1 ≤ p - 1 := by omega
    have h2 : 1 * (1 + p + p ^ 2) ≤ (p - 1) * (1 + p + p ^ 2) := Nat.mul_le_mul_right _ h1
    omega
  set e₀ : ℕ := 3 * d - (1 + p + p ^ 2)
  have he₀_pos : 1 ≤ e₀ := by omega
  have he₀_sum : e₀ + p + p ^ 2 = 3 * d - 1 := by omega
  set c₁ : K := ι (θ ^ (p ^ 2)) - ι θ
  set c₂ : K := ι (θ ^ p) - ι θ
  have ⟨hfp1, hfp2⟩ := frobenius_ne_self_of_not_mem_range p θ hθ
  have hc₁_ne : c₁ ≠ 0 := sub_ne_zero.mpr fun h => hfp2 (ι.injective h)
  have hc₂_ne : c₂ ≠ 0 := sub_ne_zero.mpr fun h => hfp1 (ι.injective h)
  set g : K[X] := X ^ e₀ * (1 + Polynomial.C c₁ * X) ^ p * (1 + Polynomial.C c₂ * X) ^ (p ^ 2)
  have hdeg_lin : ∀ c : K, c ≠ 0 → (1 + Polynomial.C c * X : K[X]).natDegree = 1 := by
    intro c hc
    have hcx : (Polynomial.C c * X : K[X]).natDegree = 1 := by
      rw [Polynomial.natDegree_C_mul hc, Polynomial.natDegree_X]
    have hlt : (1 : K[X]).natDegree < (Polynomial.C c * X : K[X]).natDegree := by
      rw [Polynomial.natDegree_one, hcx]; omega
    rw [add_comm, Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt, hcx]
  have hlin_ne : ∀ c : K, c ≠ 0 → (1 + Polynomial.C c * X : K[X]) ≠ 0 := by
    intro c hc h0
    have := hdeg_lin c hc
    rw [h0, Polynomial.natDegree_zero] at this
    omega
  have hg_deg : g.natDegree = 3 * d - 1 := by
    have h1 : (X ^ e₀ : K[X]) ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
    have h2 : ((1 + Polynomial.C c₁ * X : K[X]) ^ p) ≠ 0 := pow_ne_zero _ (hlin_ne c₁ hc₁_ne)
    have h3 : ((1 + Polynomial.C c₂ * X : K[X]) ^ (p ^ 2)) ≠ 0 := pow_ne_zero _ (hlin_ne c₂ hc₂_ne)
    simp only [g]
    rw [Polynomial.natDegree_mul (mul_ne_zero h1 h2) h3, Polynomial.natDegree_mul h1 h2,
      Polynomial.natDegree_X_pow, Polynomial.natDegree_pow, Polynomial.natDegree_pow,
      hdeg_lin c₁ hc₁_ne, hdeg_lin c₂ hc₂_ne, mul_one, mul_one, he₀_sum]
  have hmobius :
      (∑ t : K, charZero ψ
          ((ι θ - t) * (ι (θ ^ (p ^ 2)) - t) ^ p * (ι (θ ^ p) - t) ^ (p ^ 2))) =
        ∑ u : K, charZero ψ (g.eval u) := by
    have hL_erase :
        (∑ t : K, charZero ψ
            ((ι θ - t) * (ι (θ ^ (p ^ 2)) - t) ^ p * (ι (θ ^ p) - t) ^ (p ^ 2))) =
        ∑ t ∈ Finset.univ.erase (ι θ), charZero ψ
            ((ι θ - t) * (ι (θ ^ (p ^ 2)) - t) ^ p * (ι (θ ^ p) - t) ^ (p ^ 2)) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (ι θ))]
      simp
    have hR_erase :
        (∑ u : K, charZero ψ (g.eval u)) =
        ∑ u ∈ Finset.univ.erase (0 : K), charZero ψ (g.eval u) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : K))]
      have hg0 : g.eval 0 = 0 := by
        simp [g, zero_pow (by omega : e₀ ≠ 0)]
      rw [hg0, map_zero, zero_add]
    rw [hL_erase, hR_erase]
    symm
    refine Finset.sum_nbij (fun u : K => ι θ - u⁻¹) ?_ ?_ ?_ ?_
    · intro u hu
      have hu0 : u ≠ 0 := (Finset.mem_erase.mp hu).1
      exact Finset.mem_erase.mpr ⟨fun h => inv_ne_zero hu0 (sub_eq_self.mp h), Finset.mem_univ _⟩
    · intro u₁ _ u₂ _ heq
      have hinv : u₁⁻¹ = u₂⁻¹ := by linear_combination -heq
      exact inv_injective hinv
    · intro t ht
      have ht0 : t ≠ ι θ := (Finset.mem_erase.mp ht).1
      have hd0 : ι θ - t ≠ 0 := sub_ne_zero.mpr ht0.symm
      refine ⟨(ι θ - t)⁻¹, Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨inv_ne_zero hd0, Finset.mem_univ _⟩), ?_⟩
      dsimp only
      rw [inv_inv, sub_sub_cancel]
    · intro u hu
      have hu0 : u ≠ 0 := (Finset.mem_erase.mp hu).1
      have hψu3d : charZero ψ (u ^ (3 * d)) = 1 := by
        have h1 : charZero ψ u = (ψ (Units.mk0 u hu0) : ℂ) := by
          simpa using charZero_apply_unit ψ (Units.mk0 u hu0)
        rw [map_pow, h1, show 3 * d = d * 3 by ring, pow_mul, hψ_pow, one_pow]
      have hval : g.eval u =
          u ^ (3 * d) *
            ((ι θ - (ι θ - u⁻¹)) *
              (ι (θ ^ (p ^ 2)) - (ι θ - u⁻¹)) ^ p *
              (ι (θ ^ p) - (ι θ - u⁻¹)) ^ (p ^ 2)) := by
        simp only [g, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
          Polynomial.eval_one, Polynomial.eval_C, Polynomial.eval_X, c₁, c₂]
        have ha : ι θ - (ι θ - u⁻¹) = u⁻¹ := by ring
        have hb : ι (θ ^ (p ^ 2)) - (ι θ - u⁻¹) = u⁻¹ * (1 + (ι (θ ^ (p ^ 2)) - ι θ) * u) := by
          have hcancel : u⁻¹ * ((ι (θ ^ (p ^ 2)) - ι θ) * u) = ι (θ ^ (p ^ 2)) - ι θ := by
            rw [mul_comm (ι (θ ^ (p ^ 2)) - ι θ) u, ← mul_assoc, inv_mul_cancel₀ hu0, one_mul]
          rw [mul_add, mul_one, hcancel]; ring
        have hc : ι (θ ^ p) - (ι θ - u⁻¹) = u⁻¹ * (1 + (ι (θ ^ p) - ι θ) * u) := by
          have hcancel : u⁻¹ * ((ι (θ ^ p) - ι θ) * u) = ι (θ ^ p) - ι θ := by
            rw [mul_comm (ι (θ ^ p) - ι θ) u, ← mul_assoc, inv_mul_cancel₀ hu0, one_mul]
          rw [mul_add, mul_one, hcancel]; ring
        rw [ha, hb, hc, mul_pow, mul_pow]
        have hu_pow : u ^ (3 * d) * (u⁻¹ * u⁻¹ ^ p * u⁻¹ ^ (p ^ 2)) = u ^ e₀ := by
          have hinv_p : u⁻¹ * u⁻¹ ^ p * u⁻¹ ^ (p ^ 2) = (u ^ (1 + p + p ^ 2))⁻¹ := by
            rw [pow_add, pow_add, pow_one, mul_inv, mul_inv, inv_pow, inv_pow]
          rw [hinv_p]
          have hsplit_e : u ^ (3 * d) = u ^ e₀ * u ^ (1 + p + p ^ 2) := by
            rw [← pow_add, show e₀ + (1 + p + p ^ 2) = 3 * d by omega]
          rw [hsplit_e, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hu0), mul_one]
        calc
          u ^ e₀ * (1 + (ι (θ ^ (p ^ 2)) - ι θ) * u) ^ p * (1 + (ι (θ ^ p) - ι θ) * u) ^ (p ^ 2)
              = (u ^ (3 * d) * (u⁻¹ * u⁻¹ ^ p * u⁻¹ ^ (p ^ 2))) *
                  (1 + (ι (θ ^ (p ^ 2)) - ι θ) * u) ^ p *
                  (1 + (ι (θ ^ p) - ι θ) * u) ^ (p ^ 2) := by rw [hu_pow]
          _ = u ^ (3 * d) *
                (u⁻¹ * (u⁻¹ ^ p * (1 + (ι (θ ^ (p ^ 2)) - ι θ) * u) ^ p) *
                  (u⁻¹ ^ (p ^ 2) * (1 + (ι (θ ^ p) - ι θ) * u) ^ (p ^ 2))) := by ring
      rw [hval, map_mul, hψu3d, one_mul]
  -- Step C: Apply `stepanov_char_sum_bound`!
  have hd_dvd : d ∣ (p ^ (3 * k) - 1) := by
    have hge2 : 2 ≤ p ^ 3 := by
      have : 2 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hp2 3
      omega
    simpa [d, pow_mul] using sub_one_dvd_pow_sub_one (p ^ 3) k hge2
  have hstep := stepanov_char_sum_bound p (3 * k) hK_card d hd_ge2 hd_dvd g hg_deg ψ hψ_ne hψ_pow hq_big
  rw [← norm_neg, htrace, hmobius]
  have hsqrt_eq : Real.sqrt ((p : ℝ) ^ (3 * k)) = (Real.sqrt (p : ℝ)) ^ (3 * k) := by
    have hp_nn : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
    have hgen : ∀ n : ℕ, Real.sqrt ((p : ℝ) ^ n) = (Real.sqrt (p : ℝ)) ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, pow_succ, Real.sqrt_mul (pow_nonneg hp_nn n), ih]
    exact hgen (3 * k)
  simpa [hsqrt_eq] using hstep



private lemma additiveChar_add (x y : ℝ) : e (x + y) = e x * e y := by
  simp only [additiveChar, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma additiveChar_add_nat (x : ℝ) (n : ℕ) : e (x + (n : ℝ)) = e x := by
  rw [additiveChar_add]
  have h1 : e (n : ℝ) = 1 := by
    simp only [additiveChar]
    have hmul : ((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) * Complex.I =
        (n : ℂ) * (2 * ↑Real.pi * Complex.I) := by
      push_cast; ring
    rw [hmul, Complex.exp_nat_mul_two_pi_mul_I]
  rw [h1, mul_one]

private lemma additiveChar_ne_one_of_pos_lt_one {x : ℝ} (h0 : 0 < x) (h1 : x < 1) : e x ≠ 1 := by
  intro heq
  rw [additiveChar, Complex.exp_eq_one_iff] at heq
  rcases heq with ⟨n, hn⟩
  have him := congrArg Complex.im hn
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_one, mul_zero, add_zero, zero_mul, sub_zero, Complex.intCast_re,
    Complex.intCast_im, Complex.re_ofNat, Complex.im_ofNat] at him
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hxn : x = (n : ℝ) := mul_left_cancel₀ hpi.ne' (by linarith)
  have hn_pos : (0 : ℤ) < n := by
    have : (0 : ℝ) < (n : ℝ) := by linarith
    exact_mod_cast this
  have hn_lt : n < (1 : ℤ) := by
    have : (n : ℝ) < (1 : ℝ) := by linarith
    exact_mod_cast this
  omega

private lemma additiveChar_zmod_mul_add {q : ℕ} (hq : 0 < q) (a b r : ZMod q) :
    e ((((a + b) * r).val : ℝ) / q) =
      e (((a * r).val : ℝ) / q) * e (((b * r).val : ℝ) / q) := by
  have : NeZero q := ⟨hq.ne'⟩
  have hadd : ((a + b) * r).val = ((a * r).val + (b * r).val) % q := by
    rw [add_mul, ZMod.val_add]
  set s := (a * r).val + (b * r).val
  have hdiv : s % q + q * (s / q) = s := Nat.mod_add_div s q
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hreal : (((a * r).val : ℝ) / q) + (((b * r).val : ℝ) / q) =
      (((s % q : ℕ) : ℝ) / q) + ((s / q : ℕ) : ℝ) := by
    have hsR : ((s % q : ℕ) : ℝ) + (q : ℝ) * ((s / q : ℕ) : ℝ) =
        ((a * r).val : ℝ) + ((b * r).val : ℝ) := by
      have h1 : ((s % q + q * (s / q) : ℕ) : ℝ) = (s : ℝ) := by exact_mod_cast hdiv
      push_cast [s] at h1
      exact h1
    field_simp [hqR]
    linarith
  rw [← additiveChar_add, hreal, additiveChar_add_nat, hadd]

/-- For each prime `p`, construct a subset `A ⊆ ZMod (p^3 - 1)` of size `p` whose nontrivial
Fourier coefficients all satisfy `‖fourierMod A r‖ ≤ 3 * (p^3 - 1)^(1/6)`. -/
private lemma exists_ultraflat_subset_for_prime (p : ℕ) (hp : p.Prime) :
    ∃ A : Finset (ZMod (p ^ 3 - 1)),
      #A = p ∧
      ∀ r : ZMod (p ^ 3 - 1), r ≠ 0 →
        ‖fourierMod A r‖ ≤ 3 * ((p ^ 3 - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let E := GaloisField p 3
  let : Fintype E := Fintype.ofFinite E
  have hE_card : Fintype.card E = p ^ 3 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card p 3 (by norm_num)]
  set q : ℕ := p ^ 3 - 1
  have hp2 : 2 ≤ p := hp.two_le
  have hq_ge7 : 7 ≤ q := by
    have : 2 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hp2 3
    omega
  have hq_pos : 0 < q := by omega
  have : NeZero q := ⟨hq_pos.ne'⟩
  -- Pick `θ ∈ E \ range (algebraMap (ZMod p) E)`
  have hθ_ex : ∃ θ : E, θ ∉ Set.range (algebraMap (ZMod p) E) := by
    let img : Finset E := Finset.univ.image (algebraMap (ZMod p) E)
    have hlt : img.card < (Finset.univ : Finset E).card := by
      rw [Finset.card_image_of_injective _ (algebraMap (ZMod p) E).injective,
        Finset.card_univ, Finset.card_univ, ZMod.card, hE_card]
      have h1 : p * 1 < p * p ^ 2 :=
        Nat.mul_lt_mul_of_pos_left (by nlinarith) hp.pos
      have h2 : p ^ 3 = p * p ^ 2 := by ring
      omega
    obtain ⟨θ, _, hθ_not⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    refine ⟨θ, fun ⟨t, ht⟩ => hθ_not (Finset.mem_image.mpr ⟨t, Finset.mem_univ t, ht⟩)⟩
  obtain ⟨θ, hθ⟩ := hθ_ex
  -- Pick a generator `g` of `Eˣ` and build discrete logarithm `dlog : Eˣ → ZMod q`
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Eˣ)
  have hcard_u : Fintype.card Eˣ = q := by rw [Fintype.card_units, hE_card]
  have hord_g : orderOf g = q := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, hcard_u]
  have hgen_pow : ∀ u : Eˣ, ∃ a : ℕ, g ^ a = u := by
    intro u
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp (hg u)
    refine ⟨(z % (orderOf g : ℤ)).toNat, ?_⟩
    have hpos : (0 : ℤ) < (orderOf g : ℤ) := by omega
    have hnn : 0 ≤ z % (orderOf g : ℤ) := Int.emod_nonneg z hpos.ne'
    have hpe : g ^ ((z % (orderOf g : ℤ)).toNat : ℤ) = g ^ z := by
      rw [Int.toNat_of_nonneg hnn, zpow_mod_orderOf]
    rw [← zpow_natCast, hpe, hz]
  let dlog : Eˣ → ZMod q := fun u => ((Classical.choose (hgen_pow u) : ℕ) : ZMod q)
  have hdlog_pow : ∀ u : Eˣ, g ^ (dlog u).val = u := by
    intro u
    set a := Classical.choose (hgen_pow u)
    have ha : g ^ a = u := Classical.choose_spec (hgen_pow u)
    have hval : (dlog u).val = a % q := by simp [dlog, a, ZMod.val_natCast]
    rw [hval, ← hord_g, pow_mod_orderOf, ha]
  have hdlog_inj : Function.Injective dlog := by
    intro u v huv
    rw [← hdlog_pow u, ← hdlog_pow v, huv]
  have hdlog_mul : ∀ u v : Eˣ, dlog (u * v) = dlog u + dlog v := by
    intro u v
    have heq : g ^ (dlog (u * v)).val = g ^ ((dlog u).val + (dlog v).val) := by
      rw [pow_add, hdlog_pow, hdlog_pow, hdlog_pow]
    have hmod : (dlog (u * v)).val ≡ (dlog u).val + (dlog v).val [MOD q] := by
      have h0 := pow_eq_pow_iff_modEq.mp heq
      rwa [hord_g] at h0
    have hcast : ((dlog (u * v)).val : ZMod q) = (((dlog u).val + (dlog v).val : ℕ) : ZMod q) :=
      (ZMod.natCast_eq_natCast_iff _ _ q).mpr hmod
    simpa [Nat.cast_add, ZMod.natCast_zmod_val] using hcast
  have hdlog_one : dlog 1 = 0 := by
    have h := hdlog_mul 1 1
    rw [mul_one] at h
    exact (add_left_cancel (by simpa using h.symm : dlog 1 + 0 = dlog 1 + dlog 1)).symm
  have hdlog_g : dlog g = 1 := by
    have heq : g ^ (dlog g).val = g ^ 1 := by rw [hdlog_pow, pow_one]
    have hmod : (dlog g).val ≡ 1 [MOD q] := by
      have h0 := pow_eq_pow_iff_modEq.mp heq
      rwa [hord_g] at h0
    have hcast : ((dlog g).val : ZMod q) = ((1 : ℕ) : ZMod q) :=
      (ZMod.natCast_eq_natCast_iff _ _ q).mpr hmod
    simpa [ZMod.natCast_zmod_val] using hcast
  -- Define the set `A ⊆ ZMod q`
  have hθ_add_ne : ∀ t : ZMod p, θ + algebraMap (ZMod p) E t ≠ 0 := by
    intro t h0
    apply hθ
    refine ⟨-t, ?_⟩
    rw [map_neg]
    exact (eq_neg_of_add_eq_zero_left h0).symm
  let elem : ZMod p → Eˣ := fun t => Units.mk0 (θ + algebraMap (ZMod p) E t) (hθ_add_ne t)
  have helem_inj : Function.Injective elem := by
    intro t₁ t₂ heq
    have h1 : θ + algebraMap (ZMod p) E t₁ = θ + algebraMap (ZMod p) E t₂ :=
      congrArg (fun u : Eˣ => (u : E)) heq
    exact (algebraMap (ZMod p) E).injective (add_left_cancel h1)
  let emb : ZMod p → ZMod q := fun t => dlog (elem t)
  have hemb_inj : Function.Injective emb := hdlog_inj.comp helem_inj
  let A : Finset (ZMod q) := Finset.univ.image emb
  refine ⟨A, ?_, ?_⟩
  · dsimp only [A]
    rw [Finset.card_image_of_injective _ hemb_inj, Finset.card_univ, ZMod.card]
  · intro r hr
    -- Build nontrivial multiplicative character `χ_r : Eˣ →* ℂˣ`
    let χ : Eˣ →* ℂˣ :=
      { toFun := fun u => Units.mk0 (e (((dlog u * r).val : ℝ) / q)) (Complex.exp_ne_zero _)
        map_one' := by
          ext
          simp only [Units.val_mk0, Units.val_one, hdlog_one, zero_mul, ZMod.val_zero, Nat.cast_zero,
            zero_div, additiveChar, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
        map_mul' := fun u v => by
          ext
          simp only [Units.val_mk0, Units.val_mul, hdlog_mul]
          exact additiveChar_zmod_mul_add hq_pos (dlog u) (dlog v) r }
    have hχ_ne : ∃ u₀ : Eˣ, χ u₀ ≠ 1 := by
      refine ⟨g, fun h1 => ?_⟩
      have hv : e (((dlog g * r).val : ℝ) / q) = 1 := congrArg (fun u : ℂˣ => (u : ℂ)) h1
      rw [hdlog_g, one_mul] at hv
      have hr_pos : 0 < r.val := Nat.pos_of_ne_zero fun h0 => hr ((ZMod.val_eq_zero r).mp h0)
      have hr_lt : r.val < q := ZMod.val_lt r
      have h0 : (0 : ℝ) < (r.val : ℝ) / (q : ℝ) := by positivity
      have hlt1 : (r.val : ℝ) / (q : ℝ) < 1 := by
        rw [div_lt_one (by exact_mod_cast hq_pos)]
        exact_mod_cast hr_lt
      exact additiveChar_ne_one_of_pos_lt_one h0 hlt1 hv
    have hfour_eq : fourierMod A r =
        ∑ t : ZMod p, charZero χ (θ + algebraMap (ZMod p) E t) := by
      dsimp only [fourierMod, A]
      rw [Finset.sum_image (fun a _ b _ h => hemb_inj h)]
      refine Finset.sum_congr rfl fun t _ => ?_
      have hu : (elem t : E) = θ + algebraMap (ZMod p) E t := rfl
      rw [← hu, charZero_apply_unit]
      rfl
    rw [hfour_eq]
    have hkatz := katz_deg3_bound p θ hθ χ hχ_ne
    -- Elementary algebraic comparison `2 * √p ≤ 3 * q^(1/6)` for all `p ≥ 2`
    have hcomp : 2 * Real.sqrt (p : ℝ) ≤ 3 * (q : ℝ) ^ ((1 : ℝ) / 6) := by
      have hL_nn : 0 ≤ 2 * Real.sqrt (p : ℝ) := by positivity
      have hR_nn : 0 ≤ 3 * (q : ℝ) ^ ((1 : ℝ) / 6) := by positivity
      rw [← pow_le_pow_iff_left₀ hL_nn hR_nn (by norm_num : 6 ≠ 0)]
      have hL6 : (2 * Real.sqrt (p : ℝ)) ^ 6 = 64 * (p : ℝ) ^ 3 := by
        have hsq : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) := Real.sq_sqrt (Nat.cast_nonneg p)
        calc
          (2 * Real.sqrt (p : ℝ)) ^ 6 = 64 * (Real.sqrt (p : ℝ) ^ 2) ^ 3 := by ring
          _ = 64 * (p : ℝ) ^ 3 := by rw [hsq]
      have hR6 : (3 * (q : ℝ) ^ ((1 : ℝ) / 6)) ^ 6 = 729 * (q : ℝ) := by
        have hq6 : ((q : ℝ) ^ ((1 : ℝ) / 6)) ^ 6 = (q : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q)]
          norm_num
        calc
          (3 * (q : ℝ) ^ ((1 : ℝ) / 6)) ^ 6 = 729 * ((q : ℝ) ^ ((1 : ℝ) / 6)) ^ 6 := by ring
          _ = 729 * (q : ℝ) := by rw [hq6]
      rw [hL6, hR6]
      have hqR_eq : (q : ℝ) = (p : ℝ) ^ 3 - 1 := by
        have h1 : q + 1 = p ^ 3 := by omega
        have h2 : (q : ℝ) + 1 = (p : ℝ) ^ 3 := by exact_mod_cast h1
        linarith
      have hp3_ge8 : (8 : ℝ) ≤ (p : ℝ) ^ 3 := by
        have : 8 ≤ p ^ 3 := by
          have : 2 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hp2 3
          omega
        exact_mod_cast this
      linarith
    exact hkatz.trans hcomp

private lemma exists_ultraflat_subset_for_q (q : ℕ) (hq : ∃ p : ℕ, p.Prime ∧ q = p ^ 3 - 1) :
    ∃ A : Finset (ZMod q),
      (∃ p : ℕ, p.Prime ∧ q = p ^ 3 - 1 ∧ #A = p) ∧
      ∀ r : ZMod q, r ≠ 0 → ‖fourierMod A r‖ ≤ 3 * (q : ℝ) ^ ((1 : ℝ) / 6) := by
  obtain ⟨p, hp, rfl⟩ := hq
  obtain ⟨A, hcard, hbound⟩ := exists_ultraflat_subset_for_prime p hp
  exact ⟨A, ⟨p, hp, rfl, hcard⟩, hbound⟩

/--
**Ben Green's Open Problem 84 — Ultraflat Mod (`Green84.green_84.variants.ultraflat_mod`)**:
There exist an infinite set `Q : Set ℕ`, a uniform constant `C : ℝ`, and subsets
`A q : Finset (ZMod q)` with `|A q| / q^(1/3) → 1` along `Q` such that every nontrivial
Fourier coefficient satisfies `‖fourierMod (A q) r‖ ≤ C * q^(1/6)`.
-/
private theorem ultraflat_mod_proved :
    ∃ Q : Set ℕ, Q.Infinite ∧ ∃ C : ℝ, ∃ A : (q : ℕ) → Finset (ZMod q),
      Tendsto (fun q ↦ (#(A q) : ℝ) / (q : ℝ) ^ ((1 : ℝ) / 3))
        (atTop ⊓ Filter.principal Q) (𝓝 1) ∧
      ∀ q ∈ Q, ∀ r : ZMod q, r ≠ 0 → ‖fourierMod (A q) r‖ ≤ C * (q : ℝ) ^ ((1 : ℝ) / 6) := by
  classical
  let Q : Set ℕ := {q : ℕ | ∃ p : ℕ, p.Prime ∧ q = p ^ 3 - 1}
  have hQ_inf : Q.Infinite := by
    refine Set.infinite_of_forall_exists_gt fun n => ?_
    obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes (n + 2)
    refine ⟨p ^ 3 - 1, ⟨p, hp_prime, rfl⟩, ?_⟩
    have h1 : 2 ≤ p := hp_prime.two_le
    have h2 : p * 2 ≤ p * p ^ 2 := Nat.mul_le_mul_left p (by nlinarith)
    have h3 : p ^ 3 = p * p ^ 2 := by ring
    omega
  -- Choose a witness subset for every `q ∈ Q` (empty outside `Q`)
  let A : (q : ℕ) → Finset (ZMod q) := fun q =>
    if hq : ∃ p : ℕ, p.Prime ∧ q = p ^ 3 - 1 then
      Classical.choose (exists_ultraflat_subset_for_q q hq)
    else
      ∅
  have hA_props : ∀ q ∈ Q, ∃ p : ℕ, p.Prime ∧ q = p ^ 3 - 1 ∧
      #(A q) = p ∧
      ∀ r : ZMod q, r ≠ 0 → ‖fourierMod (A q) r‖ ≤ 3 * (q : ℝ) ^ ((1 : ℝ) / 6) := by
    intro q hq
    have hex : ∃ p : ℕ, p.Prime ∧ q = p ^ 3 - 1 := hq
    have hAq : A q = Classical.choose (exists_ultraflat_subset_for_q q hex) := dif_pos hex
    have hspec := Classical.choose_spec (exists_ultraflat_subset_for_q q hex)
    obtain ⟨⟨p, hp, hqeq, hcard⟩, hbound⟩ := hspec
    exact ⟨p, hp, hqeq, hAq.symm ▸ hcard, fun r hr => hAq.symm ▸ hbound r hr⟩
  refine ⟨Q, hQ_inf, 3, A, ?_, ?_⟩
  · -- Squeeze `1 ≤ #(A q) / q^(1/3) ≤ 1 + 1 / q` on `atTop ⊓ Filter.principal Q`
    have hlo : Tendsto (fun _ : ℕ => (1 : ℝ)) (atTop ⊓ Filter.principal Q) (𝓝 1) :=
      tendsto_const_nhds
    have hhi : Tendsto (fun q : ℕ => (1 : ℝ) + 1 / (q : ℝ)) (atTop ⊓ Filter.principal Q) (𝓝 1) := by
      have h0 : Tendsto (fun q : ℕ => (1 : ℝ) / (q : ℝ)) atTop (𝓝 0) :=
        tendsto_one_div_atTop_nhds_zero_nat
      have h1 : Tendsto (fun q : ℕ => (1 : ℝ) + 1 / (q : ℝ)) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add h0
      rw [add_zero] at h1
      exact h1.mono_left inf_le_left
    have hmemQ : ∀ᶠ q : ℕ in atTop ⊓ Filter.principal Q, q ∈ Q :=
      Filter.eventually_inf_principal.mpr (Filter.Eventually.of_forall fun _ hq => hq)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
    · filter_upwards [hmemQ] with q hq
      obtain ⟨p, hp, hqeq, hcard, _⟩ := hA_props q hq
      rw [hcard]
      have hp2 : 2 ≤ p := hp.two_le
      have hq_pos : 0 < q := by
        have : 2 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hp2 3
        omega
      have hqR_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos
      have hq3_pos : (0 : ℝ) < (q : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hqR_pos _
      have hratio_nn : 0 ≤ (p : ℝ) / (q : ℝ) ^ ((1 : ℝ) / 3) := by positivity
      rw [← pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 1) hratio_nn (by norm_num : 3 ≠ 0)]
      have hq3 : ((q : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = (q : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hqR_pos.le]
        norm_num
      have hcube : ((p : ℝ) / (q : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (p : ℝ) ^ 3 / (q : ℝ) := by
        rw [div_pow, hq3]
      rw [one_pow, hcube, le_div_iff₀ hqR_pos, one_mul]
      have hqp : q ≤ p ^ 3 := by omega
      exact_mod_cast hqp
    · filter_upwards [hmemQ] with q hq
      obtain ⟨p, hp, hqeq, hcard, _⟩ := hA_props q hq
      rw [hcard]
      have hp2 : 2 ≤ p := hp.two_le
      have hq_pos : 0 < q := by
        have : 2 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hp2 3
        omega
      have hqR_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos
      have hratio_nn : 0 ≤ (p : ℝ) / (q : ℝ) ^ ((1 : ℝ) / 3) := by positivity
      have hrhs_nn : 0 ≤ (1 : ℝ) + 1 / (q : ℝ) := by positivity
      rw [← pow_le_pow_iff_left₀ hratio_nn hrhs_nn (by norm_num : 3 ≠ 0)]
      have hq3 : ((q : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = (q : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hqR_pos.le]
        norm_num
      have hcube : ((p : ℝ) / (q : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (p : ℝ) ^ 3 / (q : ℝ) := by
        rw [div_pow, hq3]
      have hp3_eq : (p : ℝ) ^ 3 = (q : ℝ) + 1 := by
        have h1 : p ^ 3 = q + 1 := by
          have : 2 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hp2 3
          omega
        exact_mod_cast h1
      rw [hcube, hp3_eq]
      have hdiv_eq : ((q : ℝ) + 1) / (q : ℝ) = 1 + 1 / (q : ℝ) := by
        field_simp [hqR_pos.ne']
      rw [hdiv_eq]
      have ht_nn : (0 : ℝ) ≤ 1 / (q : ℝ) := by positivity
      nlinarith [sq_nonneg (1 / (q : ℝ))]
  · intro q hq r hr
    obtain ⟨_, _, _, _, hbound⟩ := hA_props q hq
    exact hbound r hr



end Green84

theorem OMA.solution : type_of% @Green84.green_84.variants.ultraflat_mod :=
  Green84.ultraflat_mod_proved

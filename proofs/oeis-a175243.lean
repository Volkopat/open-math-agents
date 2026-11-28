import OMAStatements.S_oeis_a175243

open Polynomial
open scoped BigOperators

namespace A175243

-- The two roots of X² - (m + 2)X + 1 are reciprocal.
private lemma exists_root (m : ℕ) :
    ∃ r : ℝ, r ≠ 0 ∧ r + r⁻¹ = (m : ℝ) + 2 := by
  let a : ℝ := 1 + (m : ℝ) / 2
  have ha : 1 ≤ a := by dsimp [a]; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hsq := Real.sq_sqrt (show 0 ≤ a ^ 2 - 1 by nlinarith)
  have hp : (a + Real.sqrt (a ^ 2 - 1)) * (a - Real.sqrt (a ^ 2 - 1)) = 1 := by
    nlinarith
  have hr : a + Real.sqrt (a ^ 2 - 1) ≠ 0 := left_ne_zero_of_mul_eq_one hp
  refine ⟨_, hr, ?_⟩
  have hinv : (a + Real.sqrt (a ^ 2 - 1))⁻¹ = a - Real.sqrt (a ^ 2 - 1) := by
    apply mul_left_cancel₀ hr
    rw [mul_inv_cancel₀ hr, hp]
  rw [hinv]
  dsimp [a]
  ring

private lemma chebyshev_value {m : ℕ} {r : ℝ} (hr : r ≠ 0)
    (ht : r + r⁻¹ = (m : ℝ) + 2) (n : ℕ) :
    2 * (Chebyshev.T ℝ n).eval (1 + (m : ℝ) / 2) = r ^ n + (r⁻¹) ^ n := by
  have h := dickson_one_one_eval_add_inv r r⁻¹ (mul_inv_cancel₀ hr) n
  rw [ht, dickson_one_one_eq_chebyshev_T] at h
  simpa only [eval_mul, eval_ofNat, eval_comp, eval_C, eval_X, invOf_eq_inv,
    show (2 : ℝ)⁻¹ * ((m : ℝ) + 2) = 1 + (m : ℝ) / 2 by ring] using h

private noncomputable def rootTrace (m j : ℕ) : ℤ :=
  (dickson 1 (1 : ℤ) j).eval ((m : ℤ) + 2)

private lemma rootTrace_eq {m : ℕ} {r : ℝ} (hr : r ≠ 0)
    (ht : r + r⁻¹ = (m : ℝ) + 2) (j : ℕ) :
    (rootTrace m j : ℝ) = r ^ j + (r⁻¹) ^ j := by
  change (Int.castRingHom ℝ) ((dickson 1 (1 : ℤ) j).eval ((m : ℤ) + 2)) = _
  rw [← eval_map_apply, map_dickson]
  simpa [ht] using dickson_one_one_eval_add_inv r r⁻¹ (mul_inv_cancel₀ hr) j

private noncomputable def quadratic (t : ℤ) : ℤ[X] := X ^ 2 - C t * X + 1

private lemma quadratic_monic (t : ℤ) : (quadratic t).Monic := by
  unfold quadratic
  monicity!

private lemma quadratic_degree (t : ℤ) : (quadratic t).natDegree = 2 := by
  unfold quadratic
  compute_degree!

-- Each quadratic supplies the next pair of conjugate powers.
private noncomputable def rootProduct (m : ℕ) : ℕ → ℤ[X]
  | 0 => X - 1
  | s + 1 => rootProduct m s * quadratic (rootTrace m (s + 1))

private lemma rootProduct_spec (m s : ℕ) :
    (rootProduct m s).Monic ∧ (rootProduct m s).natDegree = 2 * s + 1 := by
  induction s with
  | zero =>
    constructor
    · simpa [rootProduct] using (monic_X_sub_C (1 : ℤ))
    · change (X - 1 : ℤ[X]).natDegree = 1
      compute_degree!
  | succ s ih =>
    obtain ⟨hm, hd⟩ := ih
    refine ⟨hm.mul (quadratic_monic _), ?_⟩
    rw [rootProduct, natDegree_mul hm.ne_zero (quadratic_monic _).ne_zero, hd, quadratic_degree]
    omega

private lemma eval_quadratic {t : ℤ} {u v : ℝ} (hs : (t : ℝ) = u + v)
    (hp : u * v = 1) (x : ℝ) :
    (quadratic t).eval₂ (Int.castRingHom ℝ) x = (x - u) * (x - v) := by
  simp only [quadratic, eval₂_add, eval₂_sub, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C,
    Int.coe_castRingHom, eval₂_one, hs]
  nlinarith only [hp]

private lemma rootProduct_vanishes {m : ℕ} {r : ℝ} (hr : r ≠ 0)
    (ht : r + r⁻¹ = (m : ℝ) + 2) (s : ℕ) (k : ℤ)
    (hl : -(s : ℤ) ≤ k) (hu : k ≤ s) :
    (rootProduct m s).eval₂ (Int.castRingHom ℝ) (r ^ k) = 0 := by
  induction s generalizing k with
  | zero =>
    have hk : k = 0 := by omega
    simp [rootProduct, hk]
  | succ s ih =>
    rw [rootProduct, eval₂_mul]
    by_cases hi : -(s : ℤ) ≤ k ∧ k ≤ s
    · simp [ih k hi.1 hi.2]
    · have hk : k = ((s + 1 : ℕ) : ℤ) ∨ k = -((s + 1 : ℕ) : ℤ) := by omega
      have hp : r ^ (s + 1) * (r⁻¹) ^ (s + 1) = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ hr, one_pow]
      rw [eval_quadratic (rootTrace_eq hr ht (s + 1)) hp]
      rcases hk with rfl | rfl <;>
        simp only [zpow_neg, zpow_natCast, inv_pow, sub_self, zero_mul, mul_zero]

-- Apply a polynomial in the shift to a sequence, evaluated at index n.
private noncomputable def recurrence (p : ℤ[X]) (n : ℕ) : (ℕ → ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i : ℝ) * f (n + i)
  map_add' f g := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a f := by simp [Finset.mul_sum, mul_left_comm]

-- A double root x annihilates the sequence n ↦ n xⁿ. The derivative records the
-- factor i when the polynomial in the shift is expanded at n + i.
private lemma double_root {q : ℤ[X]} {x : ℝ}
    (hx : q.eval₂ (Int.castRingHom ℝ) x = 0) (hd : (q ^ 2).natDegree ≠ 0) (n : ℕ) :
    recurrence (q ^ 2) n (fun j => (j : ℝ) * x ^ j) = 0 := by
  let p := q ^ 2
  let castInt := Int.castRingHom ℝ
  have hp : p.eval₂ castInt x = 0 := by simp [p, castInt, eval₂_pow, hx]
  have hder : (p.derivative * X).eval₂ castInt x = 0 := by
    simp [p, castInt, pow_two, derivative_mul, eval₂_mul, hx]
  have hbound : (p.derivative * X).natDegree < p.natDegree + 1 := by
    have h := natDegree_mul_le (p := p.derivative) (q := (X : ℤ[X]))
    have h' := natDegree_derivative_lt (p := p) hd
    rw [natDegree_X] at h
    omega
  have hc (i : ℕ) : (p.derivative * X).coeff i = p.coeff i * (i : ℤ) := by
    cases i with
    | zero => simp
    | succ i => simp [coeff_mul_X, coeff_derivative]
  rw [eval₂_eq_sum_range] at hp
  rw [eval₂_eq_sum_range' castInt hbound x] at hder
  simp only [castInt, hc, map_mul, Int.coe_castRingHom, Int.cast_natCast] at hder
  simp only [castInt, Int.coe_castRingHom] at hp
  change (∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i : ℝ) *
    ((↑(n + i) : ℝ) * x ^ (n + i))) = 0
  calc
    _ = x ^ n * ((n : ℝ) * (∑ i ∈ Finset.range (p.natDegree + 1),
          (p.coeff i : ℝ) * x ^ i) + ∑ i ∈ Finset.range (p.natDegree + 1),
          (p.coeff i : ℝ) * (i : ℝ) * x ^ i) := by
        simp only [Finset.mul_sum, mul_add, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        push_cast
        rw [pow_add]
        ring
    _ = 0 := by rw [hp, hder]; ring

-- Multiplication by the Chebyshev expression shifts k up or down by one.
private noncomputable def mode (r : ℝ) (k : ℤ) (d n : ℕ) : ℝ :=
  (n : ℝ) * (r ^ k) ^ n * (r ^ n + (r⁻¹) ^ n - 2) ^ d

private lemma mode_succ {r : ℝ} (hr : r ≠ 0) (k : ℤ) (d : ℕ) :
    mode r k (d + 1) = mode r (k + 1) d + mode r (k - 1) d - (2 : ℝ) • mode r k d := by
  funext n
  simp only [mode, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, pow_succ,
    zpow_add₀ hr, zpow_sub₀ hr, zpow_one, div_eq_mul_inv, mul_pow]
  ring

private lemma recurrence_mode {m : ℕ} {r : ℝ} (hr : r ≠ 0)
    (ht : r + r⁻¹ = (m : ℝ) + 2) (s n d : ℕ) (k : ℤ)
    (hl : -(s : ℤ) + d ≤ k) (hu : k ≤ (s : ℤ) - d) :
    recurrence (rootProduct m s ^ 2) n (mode r k d) = 0 := by
  induction d generalizing k with
  | zero =>
    have hd : (rootProduct m s ^ 2).natDegree ≠ 0 := by
      rw [natDegree_pow, (rootProduct_spec m s).2]
      omega
    have h := rootProduct_vanishes hr ht s k (by omega) (by omega)
    have hzero : mode r k 0 = fun j : ℕ => (j : ℝ) * (r ^ k) ^ j := by
      funext j
      simp [mode]
    rw [hzero]
    exact double_root h hd n
  | succ d ih =>
    rw [mode_succ hr, map_sub, map_add, map_smul,
      ih (k + 1) (by omega) (by omega), ih (k - 1) (by omega) (by omega),
      ih k (by omega) (by omega)]
    simp

end A175243

open A175243 OMA.S_oeis_a175243

theorem OMA.solution : type_of% @OMA.S_oeis_a175243.main := by
  intro m hm
  obtain ⟨r, hr, ht⟩ := exists_root m
  let s := m - 1
  obtain ⟨hmonic, hdeg⟩ := rootProduct_spec m s
  refine ⟨rootProduct m s ^ 2, hmonic.pow 2, ?_, ?_⟩
  · rw [natDegree_pow, hdeg]
    dsimp [s]
    omega
  · intro n _
    have hcol : column m = (m : ℝ)⁻¹ • mode r 0 s := by
      funext j
      rw [column, chebyshev_value hr ht]
      simp [mode, s, div_eq_mul_inv, mul_comm]
    change recurrence (rootProduct m s ^ 2) n (column m) = 0
    rw [hcol, map_smul, recurrence_mode hr ht s n s 0 (by omega) (by omega)]
    simp

import OMAStatements.S_mo_479805
import Mathlib

/-!
# MathOverflow 479805 — a binomial cdf ratio inequality

Retains @koolkao's beta-integral proof from open-math-agents PR #24532.
The derivative calculation uses the product and power rules directly; the
quadratic moment inequality follows from the standard discriminant criterion.

`h(n) = (F_n(k) + F_n(k+1)) / ((n-k)(F_n(k-1) + F_n(k)))` is non-increasing in `n ≥ k+1`
(`F_n` the cdf of `Bin(n,p)`, `0 < p < 1`, `k ≥ 1`). Proof: beta-integral representation of `F_n(k)`,
one integration by parts, and three positivity facts for the moments
`a i = ∫₀ˣ s^i (1-s)^(k-1) ds` (`x = 1-p`).
-/

namespace OMA.P479805

open intervalIntegral Finset OMA.S_mo_479805

/-- Integration by parts: `(m+1) ∫₀ˣ s^m (1-s)^(l+1) = x^(m+1) (1-x)^(l+1) + (l+1) ∫₀ˣ s^(m+1) (1-s)^l`. -/
lemma ibp (m l : ℕ) (x : ℝ) :
    ((m : ℝ) + 1) * ∫ s in (0 : ℝ)..x, s ^ m * (1 - s) ^ (l + 1) =
      x ^ (m + 1) * (1 - x) ^ (l + 1) + ((l : ℝ) + 1) * ∫ s in (0 : ℝ)..x, s ^ (m + 1) * (1 - s) ^ l := by
  have hd (s : ℝ) :
      HasDerivAt (fun s : ℝ => s ^ (m + 1) * (1 - s) ^ (l + 1))
        (((m : ℝ) + 1) * (s ^ m * (1 - s) ^ (l + 1)) - ((l : ℝ) + 1) * (s ^ (m + 1) * (1 - s) ^ l)) s := by
    refine (((hasDerivAt_id s).pow (m + 1)).mul
      (((hasDerivAt_id s).const_sub 1).pow (l + 1))).congr_deriv ?_
    simp
    ring
  have := integral_eq_sub_of_hasDerivAt (a := 0) (b := x) (fun s _ => hd s)
    (by apply Continuous.intervalIntegrable; fun_prop)
  rw [integral_sub, integral_const_mul, integral_const_mul] at this
  · simp at this; linarith
  · apply Continuous.intervalIntegrable; fun_prop
  · apply Continuous.intervalIntegrable; fun_prop


/-- Beta-integral representation: `F_n(i) = (n-i) C(n,i) ∫₀^{1-p} s^(n-i-1) (1-s)^i ds` for `i < n`. -/
lemma beta_rep (p : ℝ) : ∀ (i r : ℕ), cdf (i + r + 1) p i =
    ((r : ℝ) + 1) * ((i + r + 1).choose i : ℝ) * ∫ s in (0 : ℝ)..(1 - p), s ^ r * (1 - s) ^ i := by
  intro i
  induction i with
  | zero =>
    intro r
    simp only [cdf, zero_add, Finset.sum_range_one, Nat.choose_zero_right, Nat.cast_one, pow_zero,
      mul_one, one_mul, Nat.sub_zero, integral_pow]
    field_simp
    ring
  | succ i ih =>
    intro r
    -- F(i+1) = F(i) + C(n,i+1) p^(i+1) (1-p)^r with n = i + r + 2
    have hn : i + 1 + r + 1 = i + (r + 1) + 1 := by ring
    have hF : cdf (i + 1 + r + 1) p (i + 1) = cdf (i + (r + 1) + 1) p i +
        ((i + 1 + r + 1).choose (i + 1) : ℝ) * p ^ (i + 1) * (1 - p) ^ (r + 1) := by
      rw [cdf, Finset.sum_range_succ, ← cdf, hn]
      simp only [show i + (r + 1) + 1 - (i + 1) = r + 1 by omega]
    rw [hF, ih (r + 1)]
    have hibp := ibp r i (1 - p)
    have hch : ((i + (r + 1) + 1).choose (i + 1) : ℝ) * ((i : ℝ) + 1) =
        ((i + (r + 1) + 1).choose i : ℝ) * ((r : ℝ) + 1 + 1) := by
      have := Nat.choose_succ_right_eq (i + (r + 1) + 1) i
      have h2 : i + (r + 1) + 1 - i = r + 2 := by omega
      rw [h2] at this
      exact_mod_cast this
    rw [hn]
    simp only [Nat.cast_add, Nat.cast_one] at hibp hch ⊢
    have h1p : (1 : ℝ) - (1 - p) = p := by ring
    rw [h1p] at hibp
    linear_combination (-(↑((i + (r + 1) + 1).choose (i + 1)) : ℝ)) * hibp - (∫ s in (0 : ℝ)..(1 - p), s ^ (r + 1) * (1 - s) ^ i) * hch


/-- Moments `A l x t = ∫₀ˣ s^t (1-s)^l ds`. -/
noncomputable def A (l : ℕ) (x : ℝ) (t : ℕ) : ℝ := ∫ s in (0 : ℝ)..x, s ^ t * (1 - s) ^ l

lemma int_lin (l : ℕ) (x : ℝ) (t : ℕ) (c0 c1 c2 : ℝ) :
    ∫ s in (0 : ℝ)..x, s ^ t * (1 - s) ^ l * (c0 + c1 * s + c2 * s ^ 2) =
      c0 * A l x t + c1 * A l x (t + 1) + c2 * A l x (t + 2) := by
  have h : (fun s : ℝ => s ^ t * (1 - s) ^ l * (c0 + c1 * s + c2 * s ^ 2)) =
      fun s => c0 * (s ^ t * (1 - s) ^ l) + c1 * (s ^ (t + 1) * (1 - s) ^ l) +
        c2 * (s ^ (t + 2) * (1 - s) ^ l) := by
    funext s; ring
  rw [h, integral_add, integral_add, integral_const_mul, integral_const_mul, integral_const_mul]
  · rfl
  all_goals (apply Continuous.intervalIntegrable; fun_prop)

lemma A_succ (l : ℕ) (x : ℝ) (t : ℕ) :
    ∫ s in (0 : ℝ)..x, s ^ t * (1 - s) ^ (l + 1) = A l x t - A l x (t + 1) := by
  have := int_lin l x t 1 (-1) 0
  have h : (fun s : ℝ => s ^ t * (1 - s) ^ (l + 1)) =
      fun s => s ^ t * (1 - s) ^ l * (1 + (-1) * s + 0 * s ^ 2) := by funext s; ring
  rw [h, this]; ring

lemma quad_nonneg (l : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (t : ℕ) (c0 c1 c2 : ℝ)
    (hq : ∀ s, 0 ≤ s → s ≤ x → 0 ≤ c0 + c1 * s + c2 * s ^ 2) :
    0 ≤ c0 * A l x t + c1 * A l x (t + 1) + c2 * A l x (t + 2) := by
  rw [← int_lin]
  apply integral_nonneg hx0
  intro s hs
  have h1 : 0 ≤ s ^ t := pow_nonneg hs.1 _
  have h2 : 0 ≤ (1 - s) ^ l := pow_nonneg (by linarith [hs.2]) _
  exact mul_nonneg (mul_nonneg h1 h2) (hq s hs.1 hs.2)

lemma A_pos (l : ℕ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (t : ℕ) : 0 < A l x t := by
  unfold A
  apply intervalIntegral_pos_of_pos_on
  · apply Continuous.intervalIntegrable; fun_prop
  · intro s hs
    exact mul_pos (pow_pos hs.1 _) (pow_pos (by linarith [hs.2]) _)
  · exact hx0

lemma F1 (l : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (t : ℕ) : 0 ≤ x * A l x t - A l x (t + 1) := by
  have := quad_nonneg l hx0 hx1 t x (-1) 0 (fun s _ hs => by nlinarith)
  linarith

lemma F2 (l : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (t : ℕ) :
    0 ≤ x ^ 2 * A l x t - 2 * x * A l x (t + 1) + A l x (t + 2) := by
  have := quad_nonneg l hx0 hx1 t (x ^ 2) (-2 * x) 1 (fun s _ _ => by nlinarith [sq_nonneg (x - s)])
  linarith

lemma F3 (l : ℕ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (t : ℕ) :
    0 ≤ A l x t * A l x (t + 2) - A l x (t + 1) ^ 2 := by
  have hq (c : ℝ) :
      0 ≤ A l x t * (c * c) + (-2 * A l x (t + 1)) * c + A l x (t + 2) := by
    have := quad_nonneg l hx0.le hx1.le t (c * c) (-2 * c) 1
      (fun s _ _ => by nlinarith [sq_nonneg (c - s)])
    nlinarith
  have h := discrim_le_zero hq
  dsimp [discrim] at h
  nlinarith



/-- `h(n) = (F_n(k) + F_n(k+1)) / ((n-k)(F_n(k-1) + F_n(k)))`. -/
noncomputable def h (n k : ℕ) (p : ℝ) : ℝ :=
  (cdf n p k + cdf n p (k + 1)) / (((n : ℝ) - k) * (cdf n p (k - 1) + cdf n p k))

lemma cdf_succ (n : ℕ) (p : ℝ) (t : ℕ) :
    cdf n p (t + 1) = cdf n p t + (n.choose (t + 1) : ℝ) * p ^ (t + 1) * (1 - p) ^ (n - (t + 1)) := by
  rw [cdf, Finset.sum_range_succ, ← cdf]

/-- The key formula: `(k+1) h(n) = N/D` with `k = l+1`, `n = l+i+2`, `x = 1-p`. -/
lemma formula (l i : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ((l : ℝ) + 2) * h (l + i + 2) (l + 1) p =
      ((1 - p) ^ i * p ^ (l + 2) + 2 * ((l : ℝ) + 2) * (A l (1 - p) i - A l (1 - p) (i + 1))) /
        ((1 - p) ^ (i + 1) * p ^ (l + 1) + 2 * ((l : ℝ) + 1) * A l (1 - p) (i + 1)) := by
  set x := 1 - p with hx
  have hx0 : 0 < x := by linarith
  set n := l + i + 2 with hn
  set I := ∫ s in (0 : ℝ)..x, s ^ i * (1 - s) ^ (l + 1) with hI
  set c : ℝ := (n.choose (l + 1) : ℝ) with hc
  set c' : ℝ := (n.choose (l + 2) : ℝ) with hc'
  have hcpos : 0 < c := by
    rw [hc]; exact_mod_cast Nat.choose_pos (by omega)
  -- F_n(k) = (i+1) c I
  have hFk : cdf n p (l + 1) = ((i : ℝ) + 1) * c * I := by
    have := beta_rep p (l + 1) i
    have e : l + 1 + i + 1 = n := by omega
    rw [e] at this
    rw [this, hc, hI, hx]
  have hFk1 : cdf n p (l + 2) = cdf n p (l + 1) + c' * p ^ (l + 2) * x ^ i := by
    rw [cdf_succ, hc', hx, show n - (l + 1 + 1) = i by omega]
  have hFkm : cdf n p (l + 1) = cdf n p l + c * p ^ (l + 1) * x ^ (i + 1) := by
    rw [cdf_succ, hc, hx, show n - (l + 1) = i + 1 by omega]
  have hch : c' * ((l : ℝ) + 2) = c * ((i : ℝ) + 1) := by
    have := Nat.choose_succ_right_eq n (l + 1)
    rw [show n - (l + 1) = i + 1 by omega] at this
    rw [hc, hc']; exact_mod_cast this
  have hibp := ibp i l x
  rw [← hI, show (1 : ℝ) - x = p by rw [hx]; ring] at hibp
  have hAs : I = A l x i - A l x (i + 1) := A_succ l x i
  have hA1 : (∫ s in (0 : ℝ)..x, s ^ (i + 1) * (1 - s) ^ l) = A l x (i + 1) := rfl
  rw [hA1] at hibp
  have hnk : ((n : ℝ) - ((l + 1 : ℕ) : ℝ)) = (i : ℝ) + 1 := by rw [hn]; push_cast; ring
  have hD : 0 < x ^ (i + 1) * p ^ (l + 1) + 2 * ((l : ℝ) + 1) * A l x (i + 1) := by
    have := A_pos l hx0 (by linarith) (i + 1)
    positivity
  unfold h
  rw [hnk, show l + 1 + 1 = l + 2 by ring, show l + 1 - 1 = l by omega]
  have hden : ((i : ℝ) + 1) * (cdf n p l + cdf n p (l + 1)) =
      ((i : ℝ) + 1) * c * (x ^ (i + 1) * p ^ (l + 1) + 2 * ((l : ℝ) + 1) * A l x (i + 1)) := by
    have : cdf n p l = cdf n p (l + 1) - c * p ^ (l + 1) * x ^ (i + 1) := by linarith
    rw [this, hFk]
    linear_combination (2 * c * ((i : ℝ) + 1)) * hibp
  have hnum : ((l : ℝ) + 2) * (cdf n p (l + 1) + cdf n p (l + 2)) =
      ((i : ℝ) + 1) * c * (x ^ i * p ^ (l + 2) + 2 * ((l : ℝ) + 2) * (A l x i - A l x (i + 1))) := by
    rw [hFk1, hFk, ← hAs]
    linear_combination (p ^ (l + 2) * x ^ i) * hch
  rw [hden, ← mul_div_assoc, hnum, mul_div_mul_left _ _ (by positivity)]


lemma step (l i : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    h (l + (i + 1) + 2) (l + 1) p ≤ h (l + i + 2) (l + 1) p := by
  have e0 := formula l i hp0 hp1
  have e1 := formula l (i + 1) hp0 hp1
  set x := 1 - p with hx
  have hx0 : 0 < x := by linarith
  have hx1 : x < 1 := by linarith
  set a0 := A l x i
  set a1 := A l x (i + 1)
  set a2 := A l x (i + 2)
  have f1 : 0 ≤ x * a1 - a2 := F1 l hx0.le hx1.le (i + 1)
  have f2 : 0 ≤ x ^ 2 * a0 - 2 * x * a1 + a2 := F2 l hx0.le hx1.le i
  have f3 : 0 ≤ a0 * a2 - a1 ^ 2 := F3 l hx0 hx1 i
  have ha1 : 0 < a1 := A_pos l hx0 hx1 (i + 1)
  have ha2 : 0 < a2 := A_pos l hx0 hx1 (i + 2)
  set N0 := x ^ i * p ^ (l + 2) + 2 * ((l : ℝ) + 2) * (a0 - a1)
  set D0 := x ^ (i + 1) * p ^ (l + 1) + 2 * ((l : ℝ) + 1) * a1
  set N1 := x ^ (i + 1) * p ^ (l + 2) + 2 * ((l : ℝ) + 2) * (a1 - a2)
  set D1 := x ^ (i + 1 + 1) * p ^ (l + 1) + 2 * ((l : ℝ) + 1) * a2
  have hD0 : 0 < D0 := by positivity
  have hD1 : 0 < D1 := by positivity
  have key : N0 * D1 - N1 * D0 = 2 * x ^ i * p ^ (l + 2) * (x * a1 - a2) +
      2 * ((l : ℝ) + 2) * x ^ i * p ^ (l + 1) * (x ^ 2 * a0 - 2 * x * a1 + a2) +
      4 * ((l : ℝ) + 1) * ((l : ℝ) + 2) * (a0 * a2 - a1 ^ 2) := by
    simp only [N0, D0, N1, D1, hx]; ring
  have hpos : 0 ≤ N0 * D1 - N1 * D0 := by
    rw [key]
    have : 0 ≤ x ^ i := pow_nonneg hx0.le _
    have : 0 ≤ p ^ (l + 2) := pow_nonneg hp0.le _
    have : 0 ≤ p ^ (l + 1) := pow_nonneg hp0.le _
    positivity
  have hle : N1 / D1 ≤ N0 / D0 := by
    rw [div_le_div_iff₀ hD1 hD0]; linarith
  have h2 : (0 : ℝ) < (l : ℝ) + 2 := by positivity
  rw [← e0, ← e1] at hle
  exact le_of_mul_le_mul_left hle h2

lemma anti (l : ℕ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {i i' : ℕ} (hii : i ≤ i') :
    h (l + i' + 2) (l + 1) p ≤ h (l + i + 2) (l + 1) p := by
  have : Antitone (fun i => h (l + i + 2) (l + 1) p) :=
    antitone_nat_of_succ_le (fun i => step l i hp0 hp1)
  exact this hii

/-- MO 479805: for `0 < p < 1`, `n > m`, `1 ≤ k ≤ m - 1`, the inequality (1) holds. -/
theorem main (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (n m : ℕ) (hmn : m < n) (k : ℕ) (hk1 : 1 ≤ k)
    (hkm : k ≤ m - 1) :
    1 / ((n : ℝ) - k) * (cdf n p k + cdf n p (k + 1)) / (cdf n p (k - 1) + cdf n p k) ≤
      1 / ((m : ℝ) - k) * (cdf m p k + cdf m p (k + 1)) / (cdf m p (k - 1) + cdf m p k) := by
  have hform : ∀ N : ℕ, 1 / ((N : ℝ) - k) * (cdf N p k + cdf N p (k + 1)) / (cdf N p (k - 1) + cdf N p k) =
      h N k p := by
    intro N; unfold h; rw [one_div, inv_mul_eq_div, div_div]
  rw [hform, hform]
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
  obtain ⟨i, rfl⟩ : ∃ i, m = l + i + 2 := ⟨m - l - 2, by omega⟩
  obtain ⟨i', rfl⟩ : ∃ i', n = l + i' + 2 := ⟨n - l - 2, by omega⟩
  exact anti l hp0 hp1 (by omega)

end OMA.P479805

theorem OMA.solution : type_of% @OMA.S_mo_479805.main :=
  fun p hp0 hp1 n m hmn k hk1 hkm => OMA.P479805.main p hp0 hp1 n m hmn k hk1 hkm

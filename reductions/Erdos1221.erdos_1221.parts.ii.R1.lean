import FormalConjectures.ErdosProblems.«1221»

-- Reduction Erdos1221.erdos_1221.parts.ii.R1 of the second de Bruijn-Erdős consecutive-gap conjecture
-- Source: S. Korsky, A Resolution of the de Bruijn-Erdős Consecutive-Gap Problem, arXiv:2609.07196
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# `r - λ_r → ∞` from Korsky's two-stage argument

Korsky (arXiv:2609.07196, Theorem 1.1, second bound) proves that for large `r` and every sequence of
distinct points on the circle, `limsup_n (r - n m_n^(r)) ≥ c √(log r)`. The proof has two stages,
which are the two hypotheses here. For `n` points and `D ≥ 0`, let `N_n(x, D)` be the number of the
first `n` points in the arc `(x, x + D/n]`.

* `H1` (Korsky, Proposition 6.4, the combinatorial core): there are absolute `C₂, C₃` such that if
  `1 ≤ A`, `C₂ A ≤ r` and eventually `r - n m_n^(r) ≤ A`, then for all large `n` and every
  `0 ≤ D ≤ S = √(A r) / log² (r / A)`, `∫_𝕋 |N_n(x, D) - D| dx ≤ C₃ A`. This is a conditional statement
  from the span hypothesis to a discrepancy bound. It is not the target.
* `H2` (Korsky, Lemma 7.2, from Halász's planar `L¹` discrepancy theorem): there are `c₄ > 0` and `S₀`
  such that if `S ≥ S₀`, `B ≥ 1`, and for all large `n` and every `0 ≤ D ≤ S` the same integral is at most
  `B`, then `B ≥ c₄ √(log S)`. This is a pure discrepancy statement about one sequence and does not
  mention spans. It is the deep input.

`main` fixes `A = max K 0 + 1`. For large `r`, `S(r)` is so large that `c₄ √(log S) > max (C₃ A) 1`.
So no sequence has `r - n m_n^(r) ≤ A` eventually. Hence every `liminf_n n m_n^(r) ≤ r - A < r - K`.
The merged `smallLambda_le` bound is not used: it gives only `r - λ_r ≥ 1/2 - o(1)`.
-/

namespace OMA.R_Erdos1221_erdos_1221_parts_ii_R1

open Filter Real

/-- Korsky, arXiv:2609.07196, Proposition 6.4: under eventually `r - n m_n^(r) ≤ A`, the short-interval
`L¹` discrepancy of the first `n` points is `O(A)` uniformly for `0 ≤ D ≤ √(A r) / log² (r / A)`. -/
def H1 : Prop :=
  ∃ C₂ C₃ : ℝ, ∀ (r : ℕ) (A : ℝ), 1 ≤ A → C₂ * A ≤ r →
    ∀ a : ℕ → ℝ, Function.Injective (fun k => Int.fract (a k)) →
    (∀ᶠ n : ℕ in atTop, (r : ℝ) - n * Erdos1221.minSpan a n r ≤ A) →
    ∀ᶠ n : ℕ in atTop, ∀ D : ℝ, 0 ≤ D → D ≤ √(A * r) / Real.log (r / A) ^ 2 →
      ∫ x in (0 : ℝ)..1,
        |(((Finset.range n).filter
          (fun j => Int.fract (a j - x) ∈ Set.Ioc (0 : ℝ) (D / n))).card : ℝ) - D| ≤ C₃ * A

/-- Korsky, arXiv:2609.07196, Lemma 7.2 (via Halász's planar `L¹` discrepancy theorem): a short-interval
`L¹` discrepancy bound `B` that holds for all large `n` and all `0 ≤ D ≤ S` forces `B ≥ c₄ √(log S)`. -/
def H2 : Prop :=
  ∃ c₄ : ℝ, 0 < c₄ ∧ ∃ S₀ : ℝ, ∀ S : ℝ, S₀ ≤ S → ∀ B : ℝ, 1 ≤ B →
    ∀ a : ℕ → ℝ, Function.Injective (fun k => Int.fract (a k)) →
    (∀ᶠ n : ℕ in atTop, ∀ D : ℝ, 0 ≤ D → D ≤ S →
      ∫ x in (0 : ℝ)..1,
        |(((Finset.range n).filter
          (fun j => Int.fract (a j - x) ∈ Set.Ioc (0 : ℝ) (D / n))).card : ℝ) - D| ≤ B) →
    c₄ * √(Real.log S) ≤ B

/-- The scale `√(A r) / log² (r / A)` exceeds `T` once `r ≥ A (64 T + 1)^8`. -/
lemma scale_large (A T r : ℝ) (hA : 1 ≤ A) (hT : 0 ≤ T) (hr : A * (64 * T + 1) ^ 8 ≤ r) :
    T ≤ √(A * r) / Real.log (r / A) ^ 2 := by
  have hA0 : 0 < A := by linarith
  set x := r / A with hxdef
  have hx : (64 * T + 1) ^ 8 ≤ x := by
    rw [hxdef, le_div_iff₀ hA0]; linarith
  have hM1 : 1 ≤ 64 * T + 1 := by linarith
  have hx1' : 1 ≤ x := le_trans (one_le_pow₀ hM1) hx
  have hx0 : 0 ≤ x := by linarith
  have hrx : x ≤ A * r := by
    have hr0 : 0 ≤ r := le_trans (by positivity) hr
    have : x ≤ r := by
      rw [hxdef, div_le_iff₀ hA0]; nlinarith
    nlinarith
  set y := x ^ ((8 : ℕ) : ℝ)⁻¹ with hydef
  have hy0 : 0 ≤ y := Real.rpow_nonneg hx0 _
  have hy8 : y ^ 8 = x := Real.rpow_inv_natCast_pow hx0 (by norm_num)
  have hyM : 64 * T + 1 ≤ y := by
    have h := Real.rpow_le_rpow (by positivity) hx (by positivity : (0 : ℝ) ≤ ((8 : ℕ) : ℝ)⁻¹)
    rwa [Real.pow_rpow_inv_natCast (by positivity) (by norm_num)] at h
  have hlog : Real.log x ≤ y * 8 := by
    have h := Real.log_le_rpow_div hx0 (by positivity : (0 : ℝ) < ((8 : ℕ) : ℝ)⁻¹)
    rw [← hydef, div_inv_eq_mul] at h
    simpa using h
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1'
  have hsqrt : √x = y ^ 4 := by
    rw [← hy8, show y ^ 8 = (y ^ 4) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hlog2 : Real.log x ^ 2 ≤ 64 * y ^ 2 := by nlinarith
  have hstep : T ≤ y ^ 4 / Real.log x ^ 2 := by
    rcases eq_or_lt_of_le hT with hT0 | hTpos
    · rw [← hT0]; positivity
    · have hx1 : 1 < x := lt_of_lt_of_le (one_lt_pow₀ (by linarith) (by norm_num)) hx
      have hpos := Real.log_pos hx1
      rw [le_div_iff₀ (by positivity)]
      have hy1 : 1 ≤ y := le_trans hM1 hyM
      have : 64 * T ≤ y ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hlog2 hT, sq_nonneg y]
  calc T ≤ y ^ 4 / Real.log x ^ 2 := hstep
    _ = √x / Real.log x ^ 2 := by rw [hsqrt]
    _ ≤ √(A * r) / Real.log (r / A) ^ 2 := by
        rw [← hxdef]
        gcongr

theorem main : H1 → H2 → type_of% @Erdos1221.erdos_1221.parts.ii := by
  intro h1 h2 K
  obtain ⟨C₂, C₃, h1⟩ := h1
  obtain ⟨c₄, hc₄, S₀, h2⟩ := h2
  set A : ℝ := max K 0 + 1 with hAdef
  have hA1 : 1 ≤ A := by have := le_max_right K 0; linarith
  have hAK : K < A := by have := le_max_left K 0; linarith
  set B : ℝ := max (C₃ * A) 1 with hBdef
  set T : ℝ := max S₀ (Real.exp (((B + 1) / c₄) ^ 2)) with hTdef
  have hT0 : 0 ≤ T := le_trans (Real.exp_pos _).le (le_max_right _ _)
  -- for S ≥ T, `c₄ √(log S) > B`
  have hbig : ∀ S : ℝ, T ≤ S → B < c₄ * √(Real.log S) := by
    intro S hS
    have hSexp : Real.exp (((B + 1) / c₄) ^ 2) ≤ S := le_trans (le_max_right _ _) hS
    have hlogS : ((B + 1) / c₄) ^ 2 ≤ Real.log S := by
      rw [← Real.log_exp (((B + 1) / c₄) ^ 2)]
      exact Real.log_le_log (Real.exp_pos _) hSexp
    have hB1 : 1 ≤ B := le_max_right _ _
    have hq : (B + 1) / c₄ ≤ √(Real.log S) := by
      rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (B + 1) / c₄)]
      exact Real.sqrt_le_sqrt hlogS
    have : B + 1 ≤ c₄ * √(Real.log S) := by
      rw [div_le_iff₀ hc₄] at hq; linarith
    linarith
  obtain ⟨R, hR⟩ := exists_nat_ge (max (max (C₂ * A) (K + 1)) (A * (64 * T + 1) ^ 8))
  refine eventually_atTop.2 ⟨R, fun r hr => ?_⟩
  have hrR : (R : ℝ) ≤ r := by exact_mod_cast hr
  have hrC : C₂ * A ≤ r := by
    have := le_trans (le_max_left _ _) (le_max_left _ _ |>.trans hR); linarith
  have hrK : K + 1 ≤ (r : ℝ) := by
    have := le_trans (le_max_right _ _) (le_max_left _ _ |>.trans hR); linarith
  have hrS : A * (64 * T + 1) ^ 8 ≤ (r : ℝ) := by
    have := le_trans (le_max_right _ _) hR; linarith
  have hscale := scale_large A T r hA1 hT0 hrS
  have hle : Erdos1221.smallLambda r ≤ ENNReal.ofReal ((r : ℝ) - A) := by
    unfold Erdos1221.smallLambda
    refine iSup₂_le fun a ha => ?_
    by_contra hlt
    rw [not_le] at hlt
    have hev := eventually_lt_of_lt_liminf hlt
    have hspan : ∀ᶠ n : ℕ in atTop, (r : ℝ) - n * Erdos1221.minSpan a n r ≤ A := by
      filter_upwards [hev] with n hn
      have := ((ENNReal.ofReal_lt_ofReal_iff').1 hn).1
      linarith
    have hdisc := h1 r A hA1 hrC a ha hspan
    have hdisc' : ∀ᶠ n : ℕ in atTop, ∀ D : ℝ, 0 ≤ D →
        D ≤ √(A * r) / Real.log (r / A) ^ 2 →
        ∫ x in (0 : ℝ)..1,
          |(((Finset.range n).filter
            (fun j => Int.fract (a j - x) ∈ Set.Ioc (0 : ℝ) (D / n))).card : ℝ) - D| ≤ B := by
      filter_upwards [hdisc] with n hn D hD0 hDS
      exact le_trans (hn D hD0 hDS) (le_max_left _ _)
    have hS0 : S₀ ≤ √(A * r) / Real.log (r / A) ^ 2 := le_trans (le_max_left _ _) hscale
    have hc := h2 _ hS0 B (le_max_right _ _) a ha hdisc'
    have := hbig _ hscale
    linarith
  refine lt_of_le_of_lt hle ?_
  exact (ENNReal.ofReal_lt_ofReal_iff').2 ⟨by linarith, by linarith⟩

end OMA.R_Erdos1221_erdos_1221_parts_ii_R1

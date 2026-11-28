import OMAStatements.S_oeis_a111000
import Mathlib

/-!
Proof. Put `u k = ζ(k) - 1 = ∑_{n ≥ 0} (n+2)^{-k} > 0` for `k ≥ 2`.
* `2^k u k = ∑_{n ≥ 0} (2/(n+2))^k → 1` by dominated convergence (bound `(2/(n+2))^2`).
  Hence `u k → 0⁺` and `u (k+1) / u k → 1/2`.
* The residue of `ζ` at `1` gives `x · ζ(1 + x) → 1` as `x → 0⁺`, so
  `u k · ζ(ζ(k)) = u k · ζ(1 + u k) → 1`.
* Therefore `ζ(ζ(k)) / ζ(ζ(k+1)) = (u k ζ(ζ k)) / (u (k+1) ζ(ζ(k+1))) · (2^(k+1) u (k+1)) / (2^k u k) / 2 → 1/2`.
-/

namespace A111000
open Filter Topology

/-- `ζ(k) - 1 = ∑_{n ≥ 0} 1/(n+2)^k`. -/
noncomputable def u (k : ℕ) : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ k

lemma summ (k : ℕ) (hk : 2 ≤ k) : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ k := by
  have h := (Real.summable_one_div_nat_pow (p := k)).mpr (by omega)
  have := (summable_nat_add_iff 1).mpr h
  simpa using this

lemma zeta_re (k : ℕ) (hk : 2 ≤ k) : (riemannZeta k).re = 1 + u k := by
  have h1 : riemannZeta k = ((∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ k : ℝ) : ℂ) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simp; exact_mod_cast hk), Complex.ofReal_tsum]
    congr 1; ext n
    rw [Complex.cpow_natCast]; push_cast; rfl
  rw [h1, Complex.ofReal_re, (summ k hk).tsum_eq_zero_add]
  simp only [u]
  norm_num
  congr 1; ext n; ring_nf

lemma u_pos (k : ℕ) (hk : 2 ≤ k) : 0 < u k := by
  have hs : Summable fun n : ℕ => 1 / ((n : ℝ) + 2) ^ k := by
    have := (summable_nat_add_iff 1).mpr (summ k hk)
    simpa [add_assoc, one_add_one_eq_two] using this
  exact hs.tsum_pos (fun n => by positivity) 0 (by positivity)

lemma two_pow_u : Tendsto (fun k : ℕ => 2 ^ k * u k) atTop (𝓝 1) := by
  have hrw : ∀ k : ℕ, 2 ^ k * u k = ∑' n : ℕ, (2 / ((n : ℝ) + 2)) ^ k := by
    intro k
    rw [u, ← tsum_mul_left]
    congr 1; ext n; rw [div_pow]; ring
  simp_rw [hrw]
  have hlim : (∑' n : ℕ, (if n = 0 then (1 : ℝ) else 0)) = 1 := by
    rw [tsum_ite_eq]
  rw [← hlim]
  refine tendsto_tsum_of_dominated_convergence (bound := fun n : ℕ => (2 / ((n : ℝ) + 2)) ^ 2) ?_ ?_ ?_
  · have h := (summable_nat_add_iff 1).mpr (summ 2 le_rfl)
    have : Summable fun n : ℕ => 4 * (1 / ((n : ℝ) + 2) ^ 2) := by
      simpa [add_assoc, one_add_one_eq_two] using h.mul_left 4
    refine this.congr fun n => ?_
    rw [div_pow]; ring
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · simp only [Nat.pos_iff_ne_zero.mp hn, if_false]
      apply tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      rw [div_lt_one (by positivity)]
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
  · filter_upwards [eventually_ge_atTop 2] with k hk n
    have h0 : 0 ≤ 2 / ((n : ℝ) + 2) := by positivity
    have h1 : 2 / ((n : ℝ) + 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_of_le_one h0 h1 hk

lemma u_tendsto : Tendsto u atTop (𝓝[>] 0) := by
  have h : Tendsto (fun k : ℕ => (2 ^ k * u k) * (1 / 2) ^ k) atTop (𝓝 (1 * 0)) :=
    two_pow_u.mul (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  rw [mul_zero] at h
  refine tendsto_nhdsWithin_iff.mpr ⟨h.congr fun k => ?_, ?_⟩
  · rw [mul_assoc, mul_comm (u k), ← mul_assoc, ← mul_pow]; norm_num
  · filter_upwards [eventually_ge_atTop 2] with k hk using u_pos k hk

lemma residue_real :
    Tendsto (fun x : ℝ => x * (riemannZeta ((1 + x : ℝ) : ℂ)).re) (𝓝[>] 0) (𝓝 1) := by
  have hmap : Tendsto (fun x : ℝ => ((1 + x : ℝ) : ℂ)) (𝓝[>] 0) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun x : ℝ => ((1 + x : ℝ) : ℂ)) (𝓝 0) (𝓝 ((1 + 0 : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.comp (continuous_const.add continuous_id)).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      have := congrArg Complex.re h
      simp at this
      exact (ne_of_gt hx) this
  have h2 := (Complex.continuous_re.tendsto 1).comp (riemannZeta_residue_one.comp hmap)
  rw [Complex.one_re] at h2
  refine h2.congr (fun x => ?_)
  simp only [Function.comp_apply]
  rw [show ((1 + x : ℝ) : ℂ) - 1 = (x : ℂ) by push_cast; ring, Complex.re_ofReal_mul]

lemma A_tendsto : Tendsto (fun k : ℕ => u k * OMA.S_oeis_a111000.zz k) atTop (𝓝 1) := by
  refine (residue_real.comp u_tendsto).congr' ?_
  filter_upwards [eventually_ge_atTop 2] with k hk
  simp only [Function.comp, OMA.S_oeis_a111000.zz, zeta_re k hk]

end A111000

open Filter Topology A111000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a111000.main := by
  have hA := A_tendsto
  have hA1 := hA.comp (tendsto_add_atTop_nat 1)
  have hB := two_pow_u
  have hB1 := hB.comp (tendsto_add_atTop_nat 1)
  have hlim := ((hA.div hA1 one_ne_zero).mul (hB1.div hB one_ne_zero)).div_const 2
  simp only [div_one, mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 2, hA1.eventually_ne one_ne_zero] with k hk hz
  simp only [Function.comp] at hz ⊢
  have hu := u_pos k hk
  have hu1 := u_pos (k + 1) (by omega)
  have hz1 : OMA.S_oeis_a111000.zz (k + 1) ≠ 0 := fun h => hz (by rw [h, mul_zero]) |>.elim
  simp only [Pi.div_apply, Function.comp_apply]
  field_simp
  ring

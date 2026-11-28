import OMAStatements.S_mo_216263

/-!
Credited port of @connoranderson's complete public proof, linked from merged statement
PR #25016 and desk DONE note #114634, pinned at:
https://github.com/connoranderson/open-math-agents/blob/efdfeb716a70120a7ee300eaf8710dea8625c393/proofs/mo-216263.lean
All mathematical code is retained unchanged. This integrates prior proof work,
not a claim of a new mathematical discovery. Qzyx posed the original question at
https://mathoverflow.net/questions/216263 (CC BY-SA 3.0).
The degree bound is strict: N columns correspond to powers 0 through N-1.
The result gives a sufficient series condition and the specified M/j^2 data,
not a necessary and sufficient criterion for all nonnegative target data.
-/

/-! An exact nodal-polynomial parameterization and a convergent Lagrange correction of nonnegative series. -/

namespace OMA.S_mo_216263

open Polynomial Finset Filter
open scoped Topology

private theorem all_interpolants {M : ℕ} (x v : Fin M → ℝ) (hx : Function.Injective x)
    (p : ℝ[X]) : (∀ i, p.eval (x i) = v i) ↔
    ∃ q, p = Lagrange.interpolate univ x v + Lagrange.nodal univ x*q := by
  let L := Lagrange.interpolate univ x v
  have he (i) : L.eval (x i) = v i := Lagrange.eval_interpolate_at_node _ hx.injOn (mem_univ _)
  constructor
  · intro hp
    have hd : Lagrange.nodal univ x ∣ p-L := by
      unfold Lagrange.nodal
      apply Finset.prod_dvd_of_coprime
      · exact fun i _ j _ hij => Polynomial.pairwise_coprime_X_sub_C hx hij
      · intro i _
        apply Polynomial.dvd_iff_isRoot.mpr
        simp [Polynomial.IsRoot, hp i, he i]
    obtain ⟨q,hq⟩ := hd
    refine ⟨q,?_⟩
    change p = L + _
    rw [← hq]
    abel
  · rintro ⟨q,rfl⟩ i
    rw [eval_add,eval_mul,Lagrange.eval_nodal_at_node (mem_univ i),zero_mul,add_zero]
    exact he i

private lemma trunc_coeff (c : ℕ → ℝ) (N j : ℕ) :
    (truncation c N).coeff j = if j<N then c j else 0 := by
  simp [truncation, Polynomial.finsetSum_coeff, coeff_monomial]

private lemma trunc_eval (c : ℕ → ℝ) (N : ℕ) (x : ℝ) :
    (truncation c N).eval x = ∑ j ∈ range N, c j*x^j := by
  simp [truncation,Polynomial.eval_finsetSum]

private lemma trunc_degree (c : ℕ → ℝ) (N : ℕ) :
    (truncation c N).degree < (N : WithBot ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro j hj
  simp [trunc_coeff,not_lt.mpr hj]

private theorem eventual_fit {M : ℕ} (x v : Fin M → ℝ) (hx : Function.Injective x)
    (c : ℕ → ℝ) (hc : ∀ j, 0 ≤ c j) (hpos : ∀ j < M, 0 < c j)
    (hs : ∀ i, HasSum (fun j => c j*(x i)^j) (v i)) :
    ∀ᶠ N in atTop, Feasible x v N (corrected x v c N) := by
  classical
  let r (N : ℕ) (i : Fin M) := v i - (truncation c N).eval (x i)
  let L (N : ℕ) := Lagrange.interpolate univ x (r N)
  have hd (N : ℕ) : (L N).degree < (M:WithBot ℕ) := by
    simpa [L] using Lagrange.degree_interpolate_lt (r N) (s := univ) hx.injOn
  have hr (i : Fin M) : Tendsto (fun N => r N i) atTop (𝓝 0) := by
    simpa [r, trunc_eval] using (tendsto_const_nhds (x := v i)).sub (hs i).tendsto_sum_nat
  have hl (j : ℕ) : Tendsto (fun N => (L N).coeff j) atTop (𝓝 0) := by
    have h := tendsto_finsetSum univ fun i (_ : i ∈ (univ : Finset (Fin M))) =>
      (hr i).mul_const ((Lagrange.basis univ x i).coeff j)
    simpa [L,Lagrange.interpolate_apply,Polynomial.finsetSum_coeff] using h
  have hp (j : Fin M) : ∀ᶠ N in atTop, 0 < c j + (L N).coeff j := by
    apply Filter.Tendsto.eventually_const_lt (hpos j j.isLt)
    simpa using (tendsto_const_nhds (x := c j)).add (hl j)
  filter_upwards [eventually_ge_atTop M, Filter.eventually_all.mpr hp] with N hN hpN
  change (truncation c N + L N).degree < _ ∧ _ ∧ _
  refine ⟨(degree_add_le ..).trans_lt (max_lt (trunc_degree c N) ((hd N).trans_le (by exact_mod_cast hN))),?_,?_⟩
  · intro j
    change 0 ≤ (truncation c N + L N).coeff j
    rw [coeff_add,trunc_coeff]
    by_cases hj : j < M
    · rw [if_pos (hj.trans_le hN)]
      exact (hpN ⟨j,hj⟩).le
    · rw [coeff_eq_zero_of_degree_lt ((hd N).trans_le (by exact_mod_cast Nat.le_of_not_lt hj)),add_zero]
      split_ifs
      · exact hc j
      · exact le_rfl
  · intro i
    change (truncation c N + L N).eval (x i) = v i
    rw [eval_add,show (L N).eval (x i) = r N i from
      Lagrange.eval_interpolate_at_node _ hx.injOn (mem_univ i)]
    simp [r]

end OMA.S_mo_216263
namespace OMA.S_mo_216263

open Polynomial Finset Filter

private lemma grid_inj (M : ℕ) (hM : 0<M) : Function.Injective (nodes M) := by
  intro i j h
  have hm : (M:ℝ) ≠ 0 := by positivity
  simp only [nodes, sub_right_inj] at h
  have hval : (i.val:ℝ)+1 = (j.val:ℝ)+1 := (div_left_inj' hm).mp h
  apply Fin.ext
  exact_mod_cast add_right_cancel hval

private lemma grid_series (M : ℕ) (hM : 0<M) (i : Fin M) :
    HasSum (fun j : ℕ => (((j:ℝ)+1)/M)*(nodes M i)^j) (values M i) := by
  have hm : (0:ℝ) < M := by exact_mod_cast hM
  have hix : (i.val:ℝ)+1 ≤ M := by exact_mod_cast i.isLt
  have hn : ‖nodes M i‖ < 1 := by
    rw [Real.norm_eq_abs,abs_lt]
    unfold nodes
    constructor
    · have := (div_le_one hm).mpr hix
      linarith
    · have : 0 < ((i.val:ℝ)+1)/M := by positivity
      linarith
  have H := (hasSum_choose_mul_geometric_of_norm_lt_one' 1 hn).div_const (M:ℝ)
  convert! H using 1
  · ext j
    simp only [Nat.choose_one_right,Nat.cast_add,Nat.cast_one]
    ring
  · simp [nodes,values, Ring.inverse_eq_inv']
    field_simp

end OMA.S_mo_216263

theorem OMA.solution : type_of% @OMA.S_mo_216263.main := by
  refine ⟨fun x v hx => ⟨OMA.S_mo_216263.all_interpolants x v hx,
    OMA.S_mo_216263.eventual_fit x v hx⟩,?_⟩
  intro M hM
  exact OMA.S_mo_216263.eventual_fit _ _ (OMA.S_mo_216263.grid_inj M hM)
    _ (fun j => by positivity) (fun j _ => by positivity) (OMA.S_mo_216263.grid_series M hM)

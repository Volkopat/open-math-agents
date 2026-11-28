import OMAStatements.S_mo_156321
import Mathlib

-- Problem: mo-156321, is the convex hull of a compact subset of a separable Hilbert space
-- compact?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. In l^2 take u_n = e_n / (n + 1) and A = {0} together with all u_n: a convergent sequence
-- with its limit, hence compact. Every point of the convex hull of A is finitely supported.
-- The points t_N = sum_{n < N} 2^{-(n+1)} u_n lie in the hull (t_N + 2^{-N} h is in the hull for
-- every h in the hull, by induction on N). If the hull were compact, a subsequence of (t_N)
-- would converge to a point l of the hull; but coordinatewise t_N tends to the sequence
-- 2^{-(n+1)} / (n + 1), which has no zero coordinate, while l is finitely supported.

namespace MO156321

open Filter Topology

abbrev E := lp (fun _ : ℕ => ℝ) 2

noncomputable def u (n : ℕ) : E := (1 / ((n : ℝ) + 1)) • lp.single 2 n (1 : ℝ)

theorem u_apply_self (n : ℕ) : u n n = 1 / ((n : ℝ) + 1) := by
  rw [u, lp.coeFn_smul, Pi.smul_apply, lp.single_apply_self, smul_eq_mul, mul_one]

theorem u_apply_ne (m n : ℕ) (h : n ≠ m) : u m n = 0 := by
  have h0 : lp.single (E := fun _ : ℕ => ℝ) 2 m (1 : ℝ) n = 0 :=
    lp.single_apply_ne (E := fun _ : ℕ => ℝ) 2 m (1 : ℝ) h
  rw [u, lp.coeFn_smul, Pi.smul_apply, h0, smul_zero]

theorem u_tendsto : Tendsto u atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h : ∀ n, ‖u n‖ = 1 / ((n : ℝ) + 1) := by
    intro n
    rw [u, norm_smul, lp.norm_single (by norm_num), norm_one, mul_one,
      Real.norm_of_nonneg (by positivity)]
  simp only [h]
  exact tendsto_one_div_add_atTop_nhds_zero_nat

noncomputable def t : ℕ → E
  | 0 => 0
  | N + 1 => t N + ((1 / 2 : ℝ) ^ (N + 1)) • u N

def A : Set E := insert 0 (Set.range u)

theorem A_compact : IsCompact A := u_tendsto.isCompact_insert_range

def S : Set E := {v | ∃ N : ℕ, ∀ n, N ≤ n → v n = 0}

theorem S_convex : Convex ℝ S := by
  intro v hv w hw a b _ _ _
  obtain ⟨N1, h1⟩ := hv
  obtain ⟨N2, h2⟩ := hw
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have e1 := h1 n (le_trans (le_max_left _ _) hn)
  have e2 := h2 n (le_trans (le_max_right _ _) hn)
  rw [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, lp.coeFn_smul, Pi.smul_apply, Pi.smul_apply,
    e1, e2, smul_zero, smul_zero, add_zero]

theorem A_sub_S : A ⊆ S := by
  rintro v (rfl | ⟨m, rfl⟩)
  · exact ⟨0, fun n _ => by rw [lp.coeFn_zero]; rfl⟩
  · exact ⟨m + 1, fun n hn => u_apply_ne m n (by omega)⟩

theorem t_mem (N : ℕ) :
    ∀ h ∈ convexHull ℝ A, t N + ((1 / 2 : ℝ) ^ N) • h ∈ convexHull ℝ A := by
  induction N with
  | zero =>
    intro h hh
    simpa [t] using hh
  | succ N ih =>
    intro h hh
    have hu : u N ∈ convexHull ℝ A := subset_convexHull ℝ A (Or.inr ⟨N, rfl⟩)
    have hmid : (1 / 2 : ℝ) • u N + (1 / 2 : ℝ) • h ∈ convexHull ℝ A :=
      (convex_convexHull ℝ A) hu hh (by norm_num) (by norm_num) (by norm_num)
    have h3 := ih _ hmid
    have e : t (N + 1) + ((1 / 2 : ℝ) ^ (N + 1)) • h =
        t N + ((1 / 2 : ℝ) ^ N) • ((1 / 2 : ℝ) • u N + (1 / 2 : ℝ) • h) := by
      rw [t, smul_add, smul_smul, smul_smul, pow_succ, add_assoc]
    rw [e]
    exact h3

theorem t_mem' (N : ℕ) : t N ∈ convexHull ℝ A := by
  have h0 : (0 : E) ∈ convexHull ℝ A := subset_convexHull ℝ A (Or.inl rfl)
  simpa using t_mem N 0 h0

theorem t_apply_ge (N : ℕ) : ∀ n, N ≤ n → t N n = 0 := by
  induction N with
  | zero =>
    intro n _
    rw [t, lp.coeFn_zero]
    rfl
  | succ N ih =>
    intro n hn
    rw [t, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply, ih n (by omega),
      u_apply_ne N n (by omega), smul_zero, add_zero]

theorem t_apply_lt (n : ℕ) :
    ∀ N, n < N → t N n = (1 / 2 : ℝ) ^ (n + 1) * (1 / ((n : ℝ) + 1)) := by
  intro N hN
  induction N with
  | zero => omega
  | succ N ih =>
    rw [t, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hN with h | h
    · rw [ih h, u_apply_ne N n (by omega), smul_zero, add_zero]
    · subst h
      rw [t_apply_ge n n le_rfl, u_apply_self, zero_add, smul_eq_mul]

theorem not_compact : ¬ IsCompact (convexHull ℝ A) := by
  intro hc
  obtain ⟨l, hl, φ, hφ, hlim⟩ := hc.tendsto_subseq (fun N => t_mem' N)
  obtain ⟨N0, hN0⟩ := (convexHull_min A_sub_S S_convex) hl
  have hz : l N0 = 0 := hN0 N0 le_rfl
  have h1 : Tendsto (fun k => ‖t (φ k) - l‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hlim
  have h2 : Tendsto (fun k => ‖(t (φ k) - l) N0‖) atTop (𝓝 0) :=
    squeeze_zero (fun k => norm_nonneg _)
      (fun k => lp.norm_apply_le_norm (by norm_num) _ N0) h1
  have h3 : ∀ᶠ k in atTop,
      ‖(t (φ k) - l) N0‖ = (1 / 2 : ℝ) ^ (N0 + 1) * (1 / ((N0 : ℝ) + 1)) := by
    filter_upwards [eventually_gt_atTop N0] with k hk
    have hk' : N0 < φ k := lt_of_lt_of_le hk (hφ.id_le k)
    rw [lp.coeFn_sub, Pi.sub_apply, t_apply_lt N0 _ hk', hz, sub_zero,
      Real.norm_of_nonneg (by positivity)]
  have h4 := tendsto_nhds_unique (tendsto_const_nhds.congr' (h3.mono fun k hk => hk.symm)) h2
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (N0 + 1) * (1 / ((N0 : ℝ) + 1)) := by positivity
  linarith

theorem sep : TopologicalSpace.SeparableSpace E := by
  obtain ⟨b⟩ : Nonempty (HilbertBasis ℕ ℝ E) :=
    ⟨HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ E)⟩
  have h1 : TopologicalSpace.IsSeparable (Set.range b) := (Set.countable_range b).isSeparable
  have h2 : TopologicalSpace.IsSeparable
      ((Submodule.span ℝ (Set.range b) : Submodule ℝ E) : Set E) := h1.span
  have h3 := h2.closure
  have h4 : closure ((Submodule.span ℝ (Set.range b) : Submodule ℝ E) : Set E) = Set.univ := by
    rw [← Submodule.topologicalClosure_coe, b.dense_span]
    rfl
  rw [h4] at h3
  exact TopologicalSpace.isSeparable_univ_iff.mp h3

end MO156321

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_156321.main) := by
  intro h
  have hsep := MO156321.sep
  exact MO156321.not_compact (h MO156321.E MO156321.A MO156321.A_compact)

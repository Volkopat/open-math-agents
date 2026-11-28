import OMAReductions.R_Erdos687_erdos_687_variants_fgkmt_R1
import Mathlib

-- Step Erdos687.erdos_687.variants.fgkmt.R1.H3: hypothesis H3 of reduction Erdos687.erdos_687.variants.fgkmt.R1
-- Credit: @ivillar. The Chebyshev estimate below (`log_le_two_sqrt`, `mul_log_le`, `card_primes_Ioc`, `exists_many_primes`) is
-- reused unchanged from the merged reduction reductions/Green46.green_46.variants.lower.R1.lean
-- by @chris01-dev (PR 2548); only the namespace and the final wrapper are new.
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Chebyshev's estimate: `π(Cx) ≥ 0.17 C x / log x` (from `Chebyshev.pi_ge`) and
`π(x) ≤ 2.4 x / log x` (from `Chebyshev.eventually_primeCounting_le`), so for `C` large in terms
of `A` the primes in `(x, C x]` number at least `A x / log x`. -/

namespace P4E687fgkmt

open Real Filter

lemma log_le_two_sqrt (t : ℝ) (ht : 0 < t) : log t ≤ 2 * √t := by
  have h1 : log (√t) = log t / 2 := Real.log_sqrt ht.le
  have h2 : log (√t) ≤ √t - 1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr ht)
  linarith

lemma mul_log_le (A t : ℝ) (hA : 0 < A) (ht : (2 * A) ^ 2 ≤ t) : A * log t ≤ t := by
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  have hs : 2 * A ≤ √t := Real.le_sqrt_of_sq_le ht
  have h1 := log_le_two_sqrt t ht0
  have h2 : √t * √t = t := Real.mul_self_sqrt ht0.le
  have h3 : 0 ≤ √t := Real.sqrt_nonneg t
  nlinarith

lemma card_primes_Ioc (x n : ℕ) (h : x ≤ n) :
    ((Finset.Ioc x n).filter Nat.Prime).card + Nat.primeCounting x = Nat.primeCounting n := by
  rw [← Nat.primesLE_card_eq_primeCounting, ← Nat.primesLE_card_eq_primeCounting,
    Nat.primesLE_eq_filter_Ioc_zero, Nat.primesLE_eq_filter_Ioc_zero,
    ← Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le x) h, Finset.filter_union, add_comm]
  refine (Finset.card_union_of_disjoint ?_).symm
  rw [Finset.disjoint_left]
  intro p hp hp'
  have h1 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
  have h2 := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp').1).1
  omega

lemma exists_many_primes (K : ℝ) : ∃ C : ℕ, 1 ≤ C ∧ ∀ᶠ x : ℕ in atTop,
    K * (x : ℝ) / log (x : ℝ) ≤ (((Finset.Ioc x (C * x)).filter Nat.Prime).card : ℝ) := by
  set C : ℕ := ⌈6 * (|K| + 3)⌉₊ + 1 with hCdef
  have hC6 : 6 * (|K| + 3) ≤ (C : ℝ) := by
    have h := Nat.le_ceil (6 * (|K| + 3))
    rw [hCdef]
    push_cast
    linarith
  have hC1 : 1 ≤ C := by omega
  refine ⟨C, hC1, ?_⟩
  have hup := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Chebyshev.eventually_primeCounting_le (ε := 1) one_pos)
  filter_upwards [hup, eventually_ge_atTop (max C 64)] with x hx hxge
  have hxC : C ≤ x := (le_max_left _ _).trans hxge
  have hx64 : 64 ≤ x := (le_max_right _ _).trans hxge
  rw [Nat.floor_natCast] at hx
  have hxR : (64 : ℝ) ≤ x := by exact_mod_cast hx64
  have hCR : (1 : ℝ) ≤ C := by exact_mod_cast hC1
  have hCx : (C : ℝ) ≤ x := by exact_mod_cast hxC
  have hlogx : 0 < log (x : ℝ) := Real.log_pos (by linarith)
  set u : ℝ := (x : ℝ) / log (x : ℝ) with hu
  have hu0 : 0 ≤ u := div_nonneg (by linarith) hlogx.le
  have hul : u * log (x : ℝ) = x := div_mul_cancel₀ _ hlogx.ne'
  have hlog4 : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  -- upper bound for the primes up to x
  have hpix : (Nat.primeCounting x : ℝ) ≤ 2.4 * u := by
    have h1 : (log 4 + 1) * (x : ℝ) / log (x : ℝ) = (log 4 + 1) * u := by
      rw [hu, mul_div_assoc]
    rw [h1] at hx
    have h2 : (log 4 + 1) * u ≤ 2.4 * u := by
      apply mul_le_mul_of_nonneg_right _ hu0
      rw [hlog4]
      linarith
    linarith
  -- lower bound for the primes up to C x
  have hn : ((C * x : ℕ) : ℝ) = (C : ℝ) * x := by push_cast; ring
  have hnge : (64 : ℝ) ≤ (C : ℝ) * x := by nlinarith
  have hlogn : 0 < log ((C : ℝ) * x) := Real.log_pos (by linarith)
  have hlogn2 : log ((C : ℝ) * x) ≤ 2 * log (x : ℝ) := by
    rw [Real.log_mul (by linarith) (by linarith)]
    have := Real.log_le_log (by linarith) hCx
    linarith
  have hlog1 : log ((C : ℝ) * x + 1) ≤ ((C : ℝ) * x + 1) / 4 := by
    have := mul_log_le 4 ((C : ℝ) * x + 1) (by norm_num) (by norm_num; linarith)
    linarith
  have hpin : 0.17 * (C : ℝ) * u ≤ (Nat.primeCounting (C * x) : ℝ) := by
    have h1 := Chebyshev.pi_ge (C * x)
    rw [hn] at h1
    refine le_trans ?_ h1
    rw [le_div_iff₀ hlogn]
    have h2 : 0.17 * (C : ℝ) * u * log ((C : ℝ) * x) ≤ 0.17 * (C : ℝ) * u * (2 * log (x : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogn2 (by positivity)
    have h3 : 0.17 * (C : ℝ) * u * (2 * log (x : ℝ)) = 0.34 * ((C : ℝ) * (u * log (x : ℝ))) := by
      ring
    rw [hul] at h3
    nlinarith
  have hcardeq := card_primes_Ioc x (C * x) (Nat.le_mul_of_pos_left x (by omega))
  have hcardR : (((Finset.Ioc x (C * x)).filter Nat.Prime).card : ℝ) =
      (Nat.primeCounting (C * x) : ℝ) - (Nat.primeCounting x : ℝ) := by
    have : (((Finset.Ioc x (C * x)).filter Nat.Prime).card : ℝ) + (Nat.primeCounting x : ℝ) =
        (Nat.primeCounting (C * x) : ℝ) := by exact_mod_cast hcardeq
    linarith
  rw [hcardR, mul_div_assoc, ← hu]
  have hK : K ≤ |K| := le_abs_self K
  have h5 : (K + 2.4) * u ≤ 0.17 * (C : ℝ) * u := by
    apply mul_le_mul_of_nonneg_right _ hu0
    have : 0 ≤ |K| := abs_nonneg K
    linarith
  linarith

end P4E687fgkmt

theorem OMA.solution : OMA.R_Erdos687_erdos_687_variants_fgkmt_R1.H3 := by
  intro A
  obtain ⟨C, -, hC⟩ := P4E687fgkmt.exists_many_primes A
  exact ⟨C, hC⟩

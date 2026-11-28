import FormalConjectures.ErdosProblems.«902»
import Mathlib.Tactic

open Finset Real Filter

theorem OMA.solution : type_of% @Erdos902.erdos_902.variants.erdos_upper := by
  intro ε hε
  have h := tendsto_natCast_atTop_atTop.atTop_mul_const hε
  filter_upwards [eventually_gt_atTop 0, h.eventually_gt_atTop 8, h.eventually_gt_atTop (4 * (log (log 2 + ε) - 2 * log (ε / 8)))] with n h0 h8 hn
  have hP : (2:ℝ) ≤ 2^n := le_self_pow₀ one_le_two h0.ne'
  have h1 : (0:ℝ) < n := by positivity
  obtain ⟨k, hk, hl⟩ : ∃ k : ℕ, ↑k ≤ (log 2 + ε/2) * n^2 * 2^n ∧ _ < (k:ℝ) + 1 := ⟨_, Nat.floor_le (by positivity), Nat.lt_floor_add_one _⟩
  have hM : (n + k : ℕ) ≤ (log 2 + ε) * n^2 * 2^n := by
    push_cast
    linarith [mul_le_mul_of_nonneg_left hP (by positivity : 0 ≤ ε * n^2), mul_lt_mul_of_pos_left h8 h1]
  have h2 := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (by positivity : 0 < ε / 8 * n)) h1.le
  have h4 : (log 2 + ε/2) * n^2 - 1 < k * (1 / 2^n) := by field_simp; linarith
  refine hM.trans' (Nat.cast_le.2 (Nat.sInf_le ⟨le_self_add, ?_⟩))
  refine (exists_mem_notMem_of_card_lt_card (t := univ) ((card_biUnion_le_card_mul (powersetCard n univ) (fun E => {ω : _ → Finset _ | ∀ x ∉ E, ¬∀ e ∈ E, (e ∈ ω x ↔ x ∈ ω e) ↔ e < x}) ((2^(n+k))^n * (2^(n+k) - 2^k)^k) fun E hE => le_trans (card_le_card_of_injOn (fun ω a => {b | b ∈ ω a ↔ (b ∈ E → a ∉ E → (a ∈ ω b ↔ a < b))}) (t := Fintype.piFinset fun x => if x ∈ E then univ else univ \ (univ \ E).powerset) (fun ω hω => by simp at hω ⊢; intro i; split_ifs <;> simp [subset_iff]; grind) (Function.Involutive.injective fun ω => by ext; simp; tauto).injOn) (by simp_all [apply_ite, prod_ite, filter_not, card_univ_diff])).trans_lt ?_)).elim fun ω ⟨_, hω⟩ => ⟨⟨fun u v => (v ∈ ω u ↔ u ∈ ω v) ↔ v < u⟩, ⟨by simp, by simp; grind⟩, by simp at hω; exact hω⟩
  simp
  rify [Nat.pow_le_pow_right two_pos le_add_self]
  rw [show (2:ℝ)^(n+k) - 2^k = 2^(n+k) * (1 - 1/2^n) by field_simp; ring, mul_pow]
  have hu : 0 < 1 - 1/(2:ℝ)^n := by field_simp; linarith
  refine (mul_le_mul_of_nonneg_right ((pow_le_pow_left₀ (by positivity) hM n).trans' (by exact_mod_cast Nat.choose_le_pow _ _)) (by positivity)).trans_lt ?_
  rw [← log_lt_log_iff] <;> try positivity
  simp (disch := positivity) only [log_mul, log_pow, Nat.cast_ofNat, Nat.cast_add] at h2 ⊢
  linarith [mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos hu) k.cast_nonneg, mul_lt_mul_of_pos_left hn h1, (Nat.one_le_cast.2 h0 : (1:ℝ) ≤ n)]


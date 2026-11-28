import OMAStatements.S_oeis_a346952
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Tactic

namespace OMA.P_oeis_a346952

open OMA.S_oeis_a346952
open Filter Topology

/-! ### Part 1: Divergence of `∑_{p ≡ a [ZMOD q]} 1/p` from `PrimesInAP` -/

private lemma log_div_rpow_le {m : ℕ} (hm : 1 ≤ m) {x : ℝ} (hx : 1 < x) :
    Real.log (m : ℝ) / (m : ℝ) ^ x ≤ (x - 1)⁻¹ * ((1 : ℝ) / (m : ℝ)) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
  have hx1 : 0 < x - 1 := sub_pos.mpr hx
  have hlog : (x - 1) * Real.log (m : ℝ) ≤ (m : ℝ) ^ (x - 1) := by
    rw [← Real.log_rpow hm_pos]
    have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hm_pos (x - 1))
    linarith
  have hrpow : (m : ℝ) ^ x = (m : ℝ) ^ (x - 1) * (m : ℝ) := by
    conv_lhs => rw [show x = (x - 1) + 1 by ring]
    rw [Real.rpow_add hm_pos, Real.rpow_one]
  rw [hrpow, one_div, inv_mul_eq_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hcancel : (m : ℝ)⁻¹ * ((m : ℝ) ^ (x - 1) * (m : ℝ)) = (m : ℝ) ^ (x - 1) := by field_simp
  rw [hcancel]
  linarith

private lemma not_summable_prime_recip_mod {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    ¬ Summable (fun n : ℕ => if n.Prime ∧ (n : ZMod q) = a then (1 : ℝ) / (n : ℝ) else 0) := by
  intro hs
  let f : ℕ → ℝ := fun n => if n.Prime ∧ (n : ZMod q) = a then (1 : ℝ) / (n : ℝ) else 0
  have hf_nn : ∀ n, 0 ≤ f n := by
    intro n; dsimp only [f]; split_ifs <;> positivity
  have hq_pos : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  let ε : ℝ := (2 * (q.totient : ℝ))⁻¹
  have hε : 0 < ε := by positivity
  have htend : Tendsto (fun N => ∑ n ∈ Finset.range N, f n) atTop (nhds (∑' n, f n)) :=
    hs.hasSum.tendsto_sum_nat
  have hev : ∀ᶠ N in atTop, ∑' n, f n - ε < ∑ n ∈ Finset.range N, f n :=
    htend.eventually (Ioi_mem_nhds (by linarith))
  obtain ⟨N, hN⟩ := hev.exists
  have htail_lt : ∑' n, f (n + N) < ε := by
    have hsplit := hs.sum_add_tsum_nat_add N
    linarith
  -- Non-prime contribution bound
  have hnp_sum : Summable (fun n : ℕ => (if n.Prime then 0 else
      ArithmeticFunction.vonMangoldt.residueClass a n) / (n : ℝ)) :=
    ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div a
  let C_np : ℝ := ∑' n : ℕ, (if n.Prime then 0 else
      ArithmeticFunction.vonMangoldt.residueClass a n) / (n : ℝ)
  let B_N : ℝ := ∑ n ∈ Finset.range N, ArithmeticFunction.vonMangoldt.residueClass a n
  obtain ⟨C, hC⟩ := ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound ha
  have hbound : ∀ x ∈ Set.Ioc (1 : ℝ) 2,
      (q.totient : ℝ)⁻¹ / (x - 1) - C ≤ C_np + B_N + ε / (x - 1) := by
    intro x hx
    have hx1 : 1 < x := hx.1
    have hsum_all : Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt.residueClass a n / (n : ℝ) ^ x) :=
      LSeries.summable_real_of_abscissaOfAbsConv_lt <|
        (ArithmeticFunction.vonMangoldt.abscissaOfAbsConv_residueClass_le_one a).trans_lt (by exact_mod_cast hx1)
    let g_np : ℕ → ℝ := fun n => (if n.Prime then 0 else
        ArithmeticFunction.vonMangoldt.residueClass a n) / (n : ℝ) ^ x
    let g_p : ℕ → ℝ := fun n => (if n.Prime then
        ArithmeticFunction.vonMangoldt.residueClass a n else 0) / (n : ℝ) ^ x
    have hg_np_le : ∀ n, g_np n ≤ (if n.Prime then 0 else
        ArithmeticFunction.vonMangoldt.residueClass a n) / (n : ℝ) := by
      intro n
      dsimp only [g_np]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · refine div_le_div_of_nonneg_left ?_ (by positivity) ?_
        · split_ifs
          · exact le_rfl
          · exact ArithmeticFunction.vonMangoldt.residueClass_nonneg a n
        · conv_lhs => rw [← Real.rpow_one (n : ℝ)]
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hx1.le
    have hg_np_nn : ∀ n, 0 ≤ g_np n := by
      intro n; dsimp only [g_np]
      have := ArithmeticFunction.vonMangoldt.residueClass_nonneg a n
      split_ifs <;> positivity
    have hg_np_sum : Summable g_np := hnp_sum.of_nonneg_of_le hg_np_nn hg_np_le
    have hg_p_nn : ∀ n, 0 ≤ g_p n := by
      intro n; dsimp only [g_p]
      have := ArithmeticFunction.vonMangoldt.residueClass_nonneg a n
      split_ifs <;> positivity
    have hg_p_le_all : ∀ n, g_p n ≤ ArithmeticFunction.vonMangoldt.residueClass a n / (n : ℝ) ^ x := by
      intro n; dsimp only [g_p]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      split_ifs
      · exact le_rfl
      · exact ArithmeticFunction.vonMangoldt.residueClass_nonneg a n
    have hg_p_sum : Summable g_p := hsum_all.of_nonneg_of_le hg_p_nn hg_p_le_all
    have htsum_eq : ∑' n, ArithmeticFunction.vonMangoldt.residueClass a n / (n : ℝ) ^ x =
        (∑' n, g_np n) + (∑' n, g_p n) := by
      rw [← hg_np_sum.tsum_add hg_p_sum]
      refine tsum_congr fun n => ?_
      dsimp only [g_np, g_p]
      rw [← add_div]
      split_ifs <;> simp
    have h1 : ∑' n, g_np n ≤ C_np := hg_np_sum.tsum_le_tsum hg_np_le hnp_sum
    have h2 : ∑' n, g_p n = (∑ n ∈ Finset.range N, g_p n) + ∑' n, g_p (n + N) :=
      (hg_p_sum.sum_add_tsum_nat_add N).symm
    have h2a : ∑ n ∈ Finset.range N, g_p n ≤ B_N := by
      apply Finset.sum_le_sum
      intro n _
      dsimp only [g_p]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [ArithmeticFunction.vonMangoldt.residueClass_apply_zero]
      · have hge1 : (1 : ℝ) ≤ (n : ℝ) ^ x :=
          Real.one_le_rpow (by exact_mod_cast hn) (by linarith)
        have hnn := ArithmeticFunction.vonMangoldt.residueClass_nonneg a n
        split_ifs
        · exact div_le_self hnn hge1
        · rw [zero_div]; exact hnn
    have h2b_le : ∀ n, g_p (n + N) ≤ (x - 1)⁻¹ * f (n + N) := by
      intro n
      dsimp only [g_p, f]
      by_cases hpr : (n + N).Prime
      · by_cases hmod : ((n + N : ℕ) : ZMod q) = a
        · rw [if_pos hpr, if_pos ⟨hpr, hmod⟩]
          have hrc : ArithmeticFunction.vonMangoldt.residueClass a (n + N) = Real.log (n + N : ℕ) := by
            simp [ArithmeticFunction.vonMangoldt.residueClass, hmod,
              ArithmeticFunction.vonMangoldt_apply_prime hpr]
          rw [hrc]
          exact log_div_rpow_le hpr.one_le hx1
        · rw [if_pos hpr, if_neg (fun h => hmod h.2), mul_zero]
          have hrc : ArithmeticFunction.vonMangoldt.residueClass a (n + N) = 0 := by
            rw [ArithmeticFunction.vonMangoldt.residueClass, Set.indicator_of_notMem]
            simpa using hmod
          rw [hrc, zero_div]
      · rw [if_neg hpr, if_neg (fun h => hpr h.1), zero_div, mul_zero]
    have h2b : ∑' n, g_p (n + N) ≤ ε / (x - 1) := by
      have hs_tail : Summable (fun n => f (n + N)) := (summable_nat_add_iff N).mpr hs
      have hgp_tail : Summable (fun n => g_p (n + N)) := (summable_nat_add_iff N).mpr hg_p_sum
      calc ∑' n, g_p (n + N)
          ≤ ∑' n, (x - 1)⁻¹ * f (n + N) := hgp_tail.tsum_le_tsum h2b_le (hs_tail.mul_left _)
        _ = (x - 1)⁻¹ * ∑' n, f (n + N) := tsum_mul_left
        _ ≤ (x - 1)⁻¹ * ε := mul_le_mul_of_nonneg_left htail_lt.le (by positivity)
        _ = ε / (x - 1) := by rw [div_eq_inv_mul]
    have hlow := hC hx
    linarith
  -- Contradiction as x → 1⁺
  have hsub : (q.totient : ℝ)⁻¹ - ε = ε := by
    dsimp only [ε]; field_simp; ring
  let K : ℝ := max 1 (C + C_np + B_N)
  have hK : 1 ≤ K := le_max_left _ _
  let x0 : ℝ := 1 + min 1 (ε / (2 * K))
  have hx0_mem : x0 ∈ Set.Ioc (1 : ℝ) 2 := by
    refine ⟨?_, ?_⟩
    · dsimp only [x0]; have : 0 < min 1 (ε / (2 * K)) := lt_min one_pos (by positivity); linarith
    · dsimp only [x0]; have : min 1 (ε / (2 * K)) ≤ 1 := min_le_left _ _; linarith
  have hb := hbound x0 hx0_mem
  have hx0_sub : x0 - 1 = min 1 (ε / (2 * K)) := by dsimp only [x0]; ring
  have hpos_sub : 0 < x0 - 1 := sub_pos.mpr hx0_mem.1
  have hle_half : x0 - 1 ≤ ε / (2 * K) := by rw [hx0_sub]; exact min_le_right _ _
  have hkey : ε / (x0 - 1) ≤ C + C_np + B_N := by
    have : (q.totient : ℝ)⁻¹ / (x0 - 1) - ε / (x0 - 1) = ε / (x0 - 1) := by
      rw [← sub_div, hsub]
    linarith
  have hkey2 : ε / (x0 - 1) ≤ K := le_trans hkey (le_max_right _ _)
  have hmul : ε ≤ K * (x0 - 1) := (div_le_iff₀ hpos_sub).mp hkey2
  have hmul2 : K * (x0 - 1) ≤ K * (ε / (2 * K)) :=
    mul_le_mul_of_nonneg_left hle_half (by linarith)
  have hsimp : K * (ε / (2 * K)) = ε / 2 := by
    have hKne : K ≠ 0 := by linarith
    field_simp
  linarith

private lemma exists_finset_primes_prod_lt {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a)
    (M : ℕ) (hM : 0 < M) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset ℕ, (∀ p ∈ F, p.Prime ∧ (p : ZMod q) = a ∧ Nat.Coprime p M) ∧
      ∏ p ∈ F, (1 - (1 : ℝ) / (p : ℝ)) < ε := by
  let f : ℕ → ℝ := fun n => if n.Prime ∧ (n : ZMod q) = a then (1 : ℝ) / (n : ℝ) else 0
  have hns : ¬ Summable f := not_summable_prime_recip_mod ha
  have hns_shift : ¬ Summable (fun n => f (n + (M + 1))) := fun h =>
    hns ((summable_nat_add_iff (M + 1)).mp h)
  have hf_nn : ∀ n, 0 ≤ f (n + (M + 1)) := by
    intro n; dsimp only [f]; split_ifs <;> positivity
  have htend : Tendsto (fun N => ∑ n ∈ Finset.range N, f (n + (M + 1))) atTop atTop :=
    not_summable_iff_tendsto_nat_atTop_of_nonneg hf_nn |>.mp hns_shift
  obtain ⟨N, hN⟩ := (htend.eventually (Ioi_mem_atTop (-Real.log ε))).exists
  let F : Finset ℕ := (Finset.Ico (M + 1) (N + (M + 1))).filter (fun p => p.Prime ∧ (p : ZMod q) = a)
  refine ⟨F, ?_, ?_⟩
  · intro p hp
    simp only [F, Finset.mem_filter, Finset.mem_Ico] at hp
    refine ⟨hp.2.1, hp.2.2, ?_⟩
    apply hp.2.1.coprime_iff_not_dvd.mpr
    intro hd
    have := Nat.le_of_dvd hM hd
    omega
  · have hsum_eq : ∑ p ∈ F, (1 : ℝ) / (p : ℝ) = ∑ n ∈ Finset.range N, f (n + (M + 1)) := by
      have h1 : ∑ p ∈ F, (1 : ℝ) / (p : ℝ) =
          ∑ p ∈ Finset.Ico (M + 1) (N + (M + 1)), f p := by
        rw [Finset.sum_filter]
      rw [h1]
      refine (Finset.sum_bij (fun n _ => n + (M + 1)) ?_ ?_ ?_ ?_).symm
      · intro n hn; simp only [Finset.mem_range] at hn; simp only [Finset.mem_Ico]; omega
      · intro n1 _ n2 _ h; omega
      · intro p hp; simp only [Finset.mem_Ico] at hp
        exact ⟨p - (M + 1), Finset.mem_range.mpr (by omega), by omega⟩
      · intro n _; rfl
    have hprod_le : ∏ p ∈ F, (1 - (1 : ℝ) / (p : ℝ)) ≤ Real.exp (- ∑ p ∈ F, (1 : ℝ) / (p : ℝ)) := by
      rw [← Finset.sum_neg_distrib, Real.exp_sum]
      apply Finset.prod_le_prod
      · intro p hp
        simp only [F, Finset.mem_filter] at hp
        have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.2.1.one_le
        have : (1 : ℝ) / (p : ℝ) ≤ 1 := div_le_one_of_le₀ hp1 (by positivity)
        linarith
      · intro p _
        have := Real.add_one_le_exp (-((1 : ℝ) / (p : ℝ)))
        linarith
    have hexp_lt : Real.exp (- ∑ p ∈ F, (1 : ℝ) / (p : ℝ)) < ε := by
      rw [hsum_eq]
      calc Real.exp (- ∑ n ∈ Finset.range N, f (n + (M + 1)))
          < Real.exp (Real.log ε) := Real.exp_lt_exp.mpr (by linarith)
        _ = ε := Real.exp_log hε
    exact lt_of_le_of_lt hprod_le hexp_lt

/-! ### Part 2: Elementary CRT counting on intervals -/

private lemma card_mod_sieve_range {M r : ℕ} (hM : 0 < M) (hr : r < M) (F : Finset ℕ)
    (hF : ∀ p ∈ F, p.Prime ∧ Nat.Coprime p M) :
    ((Finset.range (M * ∏ p ∈ F, p)).filter
      (fun m => m % M = r ∧ ∀ p ∈ F, ¬ p ∣ m)).card = ∏ p ∈ F, (p - 1) := by
  classical
  induction F using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty, mul_one, Finset.notMem_empty, IsEmpty.forall_iff,
      implies_true, and_true]
    have heq : (Finset.range M).filter (fun m => m % M = r) = {r} := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨hm, hmod⟩; rw [← hmod, Nat.mod_eq_of_lt hm]
      · rintro rfl; exact ⟨hr, Nat.mod_eq_of_lt hr⟩
    rw [heq, Finset.card_singleton]
  | @insert p s hps ih =>
    have hp_prime : p.Prime := (hF p (Finset.mem_insert_self p s)).1
    have hp_copM : Nat.Coprime p M := (hF p (Finset.mem_insert_self p s)).2
    have hsF : ∀ q ∈ s, q.Prime ∧ Nat.Coprime q M :=
      fun q hq => hF q (Finset.mem_insert_of_mem hq)
    set L := M * ∏ q ∈ s, q
    have hL_pos : 0 < L := by
      apply Nat.mul_pos hM
      apply Finset.prod_pos
      intro q hq; exact (hsF q hq).1.pos
    have hcop_pL : Nat.Coprime p L := by
      apply Nat.Coprime.mul_right hp_copM
      apply Nat.Coprime.prod_right
      intro q hq
      have hq_prime := (hsF q hq).1
      exact (Nat.coprime_primes hp_prime hq_prime).mpr (fun h => hps (h ▸ hq))
    have hprod_eq : M * ∏ q ∈ insert p s, q = L * p := by
      rw [Finset.prod_insert hps]; ring
    rw [hprod_eq, Finset.prod_insert hps, ← ih hsF, mul_comm (p - 1)]
    let A := (Finset.range L).filter (fun m => m % M = r ∧ ∀ q ∈ s, ¬ q ∣ m)
    let B := (Finset.range p).filter (fun v => v ≠ 0)
    have hB : B.card = p - 1 := by
      have heq : B = (Finset.range p).erase 0 := by
        ext v; simp [B, Finset.mem_erase, and_comm]
      rw [heq, Finset.card_erase_of_mem (Finset.mem_range.mpr hp_prime.pos), Finset.card_range]
    rw [← hB, ← Finset.card_product]
    refine Finset.card_bij (fun m _ => (m % L, m % p)) ?_ ?_ ?_
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_range] at hm
      simp only [Finset.mem_product, B, Finset.mem_filter, Finset.mem_range]
      refine ⟨⟨Nat.mod_lt m hL_pos, ?_, ?_⟩, Nat.mod_lt m hp_prime.pos, ?_⟩
      · have hML : M ∣ L := dvd_mul_right M _
        rw [Nat.mod_mod_of_dvd m hML]; exact hm.2.1
      · intro q hq hd
        have hqL : q ∣ L := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hq) M
        exact hm.2.2 q (Finset.mem_insert_of_mem hq) ((Nat.dvd_mod_iff hqL).mp hd)
      · intro h0
        exact hm.2.2 p (Finset.mem_insert_self p s) (Nat.dvd_of_mod_eq_zero h0)
    · intro m1 hm1 m2 hm2 heq
      simp only [Finset.mem_filter, Finset.mem_range] at hm1 hm2
      rcases Prod.mk.inj heq with ⟨hL, hp⟩
      have hmodeq1 : m1 ≡ m2 [MOD L] := hL
      have hmodeq2 : m1 ≡ m2 [MOD p] := hp
      have hmodeq : m1 ≡ m2 [MOD L * p] :=
        (Nat.modEq_and_modEq_iff_modEq_mul hcop_pL.symm).mp ⟨hmodeq1, hmodeq2⟩
      exact Eq.trans (Nat.mod_eq_of_lt hm1.1).symm (Eq.trans hmodeq (Nat.mod_eq_of_lt hm2.1))
    · intro ⟨u, v⟩ huv
      simp only [Finset.mem_product, B, Finset.mem_filter, Finset.mem_range] at huv
      obtain ⟨⟨huL, huM, hus⟩, hvp, hv0⟩ := huv
      let crt := Nat.chineseRemainder hcop_pL.symm u v
      let m := crt.val % (L * p)
      have hm_lt : m < L * p := Nat.mod_lt _ (Nat.mul_pos hL_pos hp_prime.pos)
      have hm_L : m % L = u := by
        rw [Nat.mod_mod_of_dvd _ (dvd_mul_right L p)]
        exact Eq.trans crt.property.1 (Nat.mod_eq_of_lt huL)
      have hm_p : m % p = v := by
        rw [Nat.mod_mod_of_dvd _ (dvd_mul_left p L)]
        exact Eq.trans crt.property.2 (Nat.mod_eq_of_lt hvp)
      refine ⟨m, ?_, Prod.ext hm_L hm_p⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨hm_lt, ?_, ?_⟩
      · have hML : M ∣ L := dvd_mul_right M _
        rw [← Nat.mod_mod_of_dvd m hML, hm_L]; exact huM
      · intro q hq hd
        simp only [Finset.mem_insert] at hq
        rcases hq with rfl | hqs
        · exact hv0 (hm_p.symm.trans (Nat.mod_eq_zero_of_dvd hd))
        · have hqL : q ∣ L := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hqs) M
          exact hus q hqs ((Nat.dvd_mod_iff hqL).mpr hd |>.trans (by rw [hm_L]))

/-- Shifting a period-`L` predicate over any block `[A, A + L)` gives the same count as `[0, L)`. -/
private lemma card_Ico_periodic_block {L : ℕ} (hL : 0 < L) (P : ℕ → Prop) [DecidablePred P]
    (hper : ∀ x, P (x % L) ↔ P x) (A : ℕ) :
    ((Finset.Ico A (A + L)).filter P).card = ((Finset.range L).filter P).card := by
  refine Finset.card_bij (fun m _ => m % L) ?_ ?_ ?_
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range] at hm ⊢
    exact ⟨Nat.mod_lt m hL, (hper m).mpr hm.2⟩
  · intro m1 h1 m2 h2 heq
    simp only [Finset.mem_filter, Finset.mem_Ico] at h1 h2
    have h1' := Nat.div_add_mod m1 L
    have h2' := Nat.div_add_mod m2 L
    have hq : m1 / L = m2 / L := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have : m1 / L + 1 ≤ m2 / L := hlt
        nlinarith
      · have : m2 / L + 1 ≤ m1 / L := hgt
        nlinarith
    rw [hq] at h1'
    omega
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    let m := if A % L ≤ r then A - A % L + r else A - A % L + L + r
    have hAm : A % L ≤ A := Nat.mod_le A L
    have hA_lt : A % L < L := Nat.mod_lt A hL
    have hAm_div : A - A % L = L * (A / L) := by have := Nat.div_add_mod A L; omega
    have hm_mem : m ∈ Finset.Ico A (A + L) := by
      simp only [Finset.mem_Ico, m]
      split_ifs <;> omega
    have hm_mod : m % L = r := by
      dsimp only [m]
      split_ifs
      · rw [hAm_div, Nat.mul_add_mod, Nat.mod_eq_of_lt hr.1]
      · rw [hAm_div, show L * (A / L) + L + r = L * (A / L + 1) + r by ring,
          Nat.mul_add_mod, Nat.mod_eq_of_lt hr.1]
    exact ⟨m, Finset.mem_filter.mpr ⟨hm_mem, (hper m).mp (hm_mod ▸ hr.2)⟩, hm_mod⟩

/-- Upper bound for a periodic predicate on `[A, B)`: at most `((B - A) / L + 1)` full blocks. -/
private lemma card_Ico_periodic_le {L : ℕ} (hL : 0 < L) (P : ℕ → Prop) [DecidablePred P]
    (hper : ∀ x, P (x % L) ↔ P x) (A B : ℕ) :
    ((Finset.Ico A B).filter P).card ≤ ((B - A) / L + 1) * ((Finset.range L).filter P).card := by
  set c := ((Finset.range L).filter P).card
  have hblocks : ∀ t : ℕ, ((Finset.Ico A (A + t * L)).filter P).card = t * c := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have hsplit : Finset.Ico A (A + (t + 1) * L) =
          Finset.Ico A (A + t * L) ∪ Finset.Ico (A + t * L) (A + t * L + L) := by
        ext x
        simp only [Finset.mem_Ico, Finset.mem_union]
        have : A + (t + 1) * L = A + t * L + L := by ring
        omega
      have hdisj : Disjoint (Finset.Ico A (A + t * L)) (Finset.Ico (A + t * L) (A + t * L + L)) := by
        rw [Finset.disjoint_left]
        intro x h1 h2
        simp only [Finset.mem_Ico] at h1 h2; omega
      rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
        ih, card_Ico_periodic_block hL P hper (A + t * L)]
      ring
  have hle_end : B ≤ A + ((B - A) / L + 1) * L := by
    have hdm := Nat.div_add_mod (B - A) L
    have hlt := Nat.mod_lt (B - A) hL
    have : ((B - A) / L + 1) * L = L * ((B - A) / L) + L := by ring
    omega
  have hsub : (Finset.Ico A B).filter P ⊆ (Finset.Ico A (A + ((B - A) / L + 1) * L)).filter P := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_Ico] at hx ⊢
    exact ⟨⟨hx.1.1, lt_of_lt_of_le hx.1.2 hle_end⟩, hx.2⟩
  calc ((Finset.Ico A B).filter P).card
      ≤ ((Finset.Ico A (A + ((B - A) / L + 1) * L)).filter P).card := Finset.card_le_card hsub
    _ = ((B - A) / L + 1) * c := hblocks ((B - A) / L + 1)

/-- Exact count of `m ∈ [A, A + t * M)` with `m % M = r` is `t`. -/
private lemma card_Ico_mod_exact {M r : ℕ} (hM : 0 < M) (hr : r < M) (A t : ℕ) :
    ((Finset.Ico A (A + t * M)).filter (fun m => m % M = r)).card = t := by
  have hper : ∀ x, (x % M) % M = r ↔ x % M = r := fun x => by rw [Nat.mod_mod]
  have h0 : ((Finset.range M).filter (fun m => m % M = r)).card = 1 := by
    have heq : (Finset.range M).filter (fun m => m % M = r) = {r} := by
      ext m; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      exact ⟨fun ⟨hm, h⟩ => h.symm.trans (Nat.mod_eq_of_lt hm) |>.symm,
        fun h => by subst h; exact ⟨hr, Nat.mod_eq_of_lt hr⟩⟩
    rw [heq, Finset.card_singleton]
  induction t with
  | zero => simp
  | succ t ih =>
    have hsplit : Finset.Ico A (A + (t + 1) * M) =
        Finset.Ico A (A + t * M) ∪ Finset.Ico (A + t * M) (A + t * M + M) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_union]
      have : A + (t + 1) * M = A + t * M + M := by ring
      omega
    have hdisj : Disjoint (Finset.Ico A (A + t * M)) (Finset.Ico (A + t * M) (A + t * M + M)) := by
      rw [Finset.disjoint_left]; intro x h1 h2; simp only [Finset.mem_Ico] at h1 h2; omega
    rw [hsplit, Finset.filter_union,
      Finset.card_union_of_disjoint (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
      ih, card_Ico_periodic_block hM (fun m => m % M = r) hper (A + t * M), h0]

/-! ### Part 3: Main density & ratio limit theorem for any Spezia progression family -/

private lemma ratio_tendsto_ten_of_progression_sieve
    (S : ℕ → Prop) [DecidablePred S]
    (M r a_res : ℕ) (hM : 0 < M) (hr : r < M) (hM_dvd : M ∣ 100)
    (ha_lt : a_res < 10) (ha_cop : Nat.Coprime a_res 10)
    (hS_sub : ∀ m, S m → m % M = r)
    (hS_sup : ∃ B : ℕ, ∀ m, B ≤ m → m % M = r →
      (∃ p : ℕ, p.Prime ∧ p % 10 = a_res ∧ p ∣ m ∧ p < m) → S m) :
    Tendsto (fun n : ℕ =>
      (((Finset.Ico (10 ^ (n - 1)) (10 ^ n)).filter S).card : ℝ) /
      (((Finset.Ico (10 ^ (n - 1 - 1)) (10 ^ (n - 1))).filter S).card : ℝ))
      atTop (nhds (10 : ℝ)) := by
  let cnt (n : ℕ) : ℕ := ((Finset.Ico (10 ^ (n - 1)) (10 ^ n)).filter S).card
  -- Show cnt n / (9 * 10^(n-1)) → 1 / M!
  have hdens : Tendsto (fun n : ℕ => (cnt n : ℝ) / (9 * (10 : ℝ) ^ (n - 1))) atTop (nhds ((1 : ℝ) / (M : ℝ))) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    have hM_pos : (0 : ℝ) < (M : ℝ) := by positivity
    have hε : 0 < (M : ℝ) * δ / 2 := by positivity
    have ha_unit : IsUnit (a_res : ZMod 10) := (ZMod.isUnit_iff_coprime a_res 10).mpr ha_cop
    obtain ⟨F, hF, hprod_lt⟩ := exists_finset_primes_prod_lt ha_unit M hM hε
    rcases hS_sup with ⟨B, hB⟩
    let P := ∏ p ∈ F, p
    have hP_pos : 0 < P := Finset.prod_pos (fun p hp => (hF p hp).1.pos)
    let L := M * P
    have hL_pos : 0 < L := Nat.mul_pos hM hP_pos
    let maxF := F.sup id
    -- Choose N0 large enough that 10^(N0 - 1) > max B maxF, N0 ≥ 3, and L / (9 * 10^(N0 - 1)) < δ / 2
    obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ, 3 ≤ N0 ∧ B ≤ 10 ^ (N0 - 1) ∧ maxF < 10 ^ (N0 - 1) ∧
        (L : ℝ) / (9 * (10 : ℝ) ^ (N0 - 1)) < δ / 2 := by
      have ht1 : Tendsto (fun n : ℕ => (10 : ℝ) ^ (n - 1)) atTop atTop :=
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 10)).comp
          (tendsto_sub_atTop_nat 1)
      have hev1 : ∀ᶠ n in atTop, (max (max B maxF) 100 : ℝ) < (10 : ℝ) ^ (n - 1) :=
        ht1.eventually (Ioi_mem_atTop _)
      have hev2 : ∀ᶠ n in atTop, (2 * (L : ℝ) / (9 * δ)) < (10 : ℝ) ^ (n - 1) :=
        ht1.eventually (Ioi_mem_atTop _)
      have hev3 : ∀ᶠ n in atTop, 3 ≤ n := eventually_ge_atTop 3
      obtain ⟨N0, h1, h2, h3⟩ := (hev1.and (hev2.and hev3)).exists
      refine ⟨N0, h3, ?_, ?_, ?_⟩
      · have : (B : ℝ) < (10 : ℝ) ^ (N0 - 1) := lt_of_le_of_lt (by exact_mod_cast le_trans (le_max_left _ _) (le_max_left _ _)) h1
        exact_mod_cast this.le
      · have : (maxF : ℝ) < (10 : ℝ) ^ (N0 - 1) := lt_of_le_of_lt (by exact_mod_cast le_trans (le_max_right _ _) (le_max_left _ _)) h1
        exact_mod_cast this
      · rw [div_lt_iff₀ (by positivity)]
        have hlt : 2 * (L : ℝ) / (9 * δ) * (9 * δ) < (10 : ℝ) ^ (N0 - 1) * (9 * δ) :=
          mul_lt_mul_of_pos_right h2 (by positivity)
        have hne : (9 * δ : ℝ) ≠ 0 := by positivity
        rw [div_mul_cancel₀ _ hne] at hlt
        linarith
    refine ⟨N0, fun n hn => ?_⟩
    have hn3 : 3 ≤ n := le_trans hN0.1 hn
    have hpow_mono : 10 ^ (N0 - 1) ≤ 10 ^ (n - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    -- Total elements in Ico (10^(n-1)) (10^n) with m % M = r
    have hM_dvd_len : M ∣ 9 * 10 ^ (n - 1) := by
      have h100 : 100 ∣ 10 ^ (n - 1) := by
        have : 100 = 10 ^ 2 := by norm_num
        rw [this]; exact Nat.pow_dvd_pow 10 (by omega)
      exact dvd_mul_of_dvd_right (dvd_trans hM_dvd h100) 9
    set t := (9 * 10 ^ (n - 1)) / M
    have ht_eq : t * M = 9 * 10 ^ (n - 1) := Nat.div_mul_cancel hM_dvd_len
    have hIco_end : 10 ^ (n - 1) + t * M = 10 ^ n := by
      rw [ht_eq, show 10 ^ n = 10 * 10 ^ (n - 1) by rw [← pow_succ', show n - 1 + 1 = n by omega]]
      ring
    have htot : ((Finset.Ico (10 ^ (n - 1)) (10 ^ n)).filter (fun m => m % M = r)).card = t := by
      rw [← hIco_end]; exact card_Ico_mod_exact hM hr (10 ^ (n - 1)) t
    -- Upper bound: cnt n ≤ t
    have hcnt_le : cnt n ≤ t := by
      rw [← htot]
      apply Finset.card_le_card
      intro m hm
      simp only [Finset.mem_filter] at hm ⊢
      exact ⟨hm.1, hS_sub m hm.2⟩
    -- Missed elements: m % M = r and ¬ S m ⇒ ∀ p ∈ F, ¬ p ∣ m
    let Missed := (Finset.Ico (10 ^ (n - 1)) (10 ^ n)).filter (fun m => m % M = r ∧ ∀ p ∈ F, ¬ p ∣ m)
    have hdiff_le : t - cnt n ≤ Missed.card := by
      have hsub : (Finset.Ico (10 ^ (n - 1)) (10 ^ n)).filter (fun m => m % M = r) ⊆
          (Finset.Ico (10 ^ (n - 1)) (10 ^ n)).filter S ∪ Missed := by
        intro m hm
        simp only [Finset.mem_union, Finset.mem_filter, Missed] at hm ⊢
        by_cases hSm : S m
        · exact Or.inl ⟨hm.1, hSm⟩
        · refine Or.inr ⟨hm.1, hm.2, fun p hp hpm => hSm ?_⟩
          have hpm_lt : p < m := by
            have hp_le : p ≤ maxF := Finset.le_sup (f := id) hp
            simp only [Finset.mem_Ico] at hm
            omega
          have hB_le : B ≤ m := by simp only [Finset.mem_Ico] at hm; omega
          have hp_mod : p % 10 = a_res := by
            have hza : (p : ZMod 10) = (a_res : ZMod 10) := (hF p hp).2.1
            have h1 := congrArg ZMod.val hza
            rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha_lt] at h1
            exact h1
          exact hB m hB_le hm.2 ⟨p, (hF p hp).1, hp_mod, hpm, hpm_lt⟩
      have hcard := Finset.card_le_card hsub
      have hun := Finset.card_union_le ((Finset.Ico (10 ^ (n - 1)) (10 ^ n)).filter S) Missed
      rw [htot] at hcard
      have hle := le_trans hcard hun
      change t ≤ cnt n + Missed.card at hle
      omega
    -- Bound Missed.card using card_Ico_periodic_le and card_mod_sieve_range
    have hper : ∀ x, ((x % L) % M = r ∧ ∀ p ∈ F, ¬ p ∣ x % L) ↔ (x % M = r ∧ ∀ p ∈ F, ¬ p ∣ x) := by
      intro x
      constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨?_, ?_⟩
      · rwa [Nat.mod_mod_of_dvd x (dvd_mul_right M P)] at h1
      · intro p hp; have hpL : p ∣ L := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hp) M
        exact fun h => h2 p hp ((Nat.dvd_mod_iff hpL).mpr h)
      · rwa [Nat.mod_mod_of_dvd x (dvd_mul_right M P)]
      · intro p hp; have hpL : p ∣ L := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hp) M
        exact fun h => h2 p hp ((Nat.dvd_mod_iff hpL).mp h)
    have hmiss_le : Missed.card ≤ ((10 ^ n - 10 ^ (n - 1)) / L + 1) * ∏ p ∈ F, (p - 1) := by
      have h1 := card_Ico_periodic_le hL_pos (fun m => m % M = r ∧ ∀ p ∈ F, ¬ p ∣ m) hper (10 ^ (n - 1)) (10 ^ n)
      rw [card_mod_sieve_range hM hr F (fun p hp => ⟨(hF p hp).1, (hF p hp).2.2⟩)] at h1
      exact h1
    have hlen_sub : 10 ^ n - 10 ^ (n - 1) = 9 * 10 ^ (n - 1) := by
      rw [show 10 ^ n = 10 * 10 ^ (n - 1) by rw [← pow_succ', show n - 1 + 1 = n by omega]]
      omega
    rw [hlen_sub] at hmiss_le
    -- Convert to ℝ and finish metric bound!
    have hden_pos : (0 : ℝ) < 9 * (10 : ℝ) ^ (n - 1) := by positivity
    have ht_real : (t : ℝ) / (9 * (10 : ℝ) ^ (n - 1)) = (1 : ℝ) / (M : ℝ) := by
      have hcast : (t : ℝ) * (M : ℝ) = 9 * (10 : ℝ) ^ (n - 1) := by exact_mod_cast ht_eq
      rw [div_eq_div_iff (by positivity) (by positivity)]
      linarith
    have hprod_eq_R : ((∏ p ∈ F, (p - 1) : ℕ) : ℝ) / (P : ℝ) = ∏ p ∈ F, (1 - (1 : ℝ) / (p : ℝ)) := by
      dsimp only [P]
      rw [Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      have hp1 : 1 ≤ p := (hF p hp).1.one_le
      have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (hF p hp).1.pos
      rw [Nat.cast_sub hp1, Nat.cast_one, sub_div, div_self hp_pos.ne']
    have hmiss_real : (Missed.card : ℝ) / (9 * (10 : ℝ) ^ (n - 1)) < δ := by
      have h1 : (Missed.card : ℝ) ≤ (((9 * 10 ^ (n - 1)) / L : ℕ) + 1 : ℝ) * ((∏ p ∈ F, (p - 1) : ℕ) : ℝ) := by
        exact_mod_cast hmiss_le
      have hdiv_le : (((9 * 10 ^ (n - 1)) / L : ℕ) : ℝ) ≤ (9 * (10 : ℝ) ^ (n - 1)) / (L : ℝ) := by
        rw [le_div_iff₀ (by positivity)]
        exact_mod_cast Nat.div_mul_le_self (9 * 10 ^ (n - 1)) L
      have hprod_le_P : ((∏ p ∈ F, (p - 1) : ℕ) : ℝ) ≤ (P : ℝ) := by
        dsimp only [P]; rw [Nat.cast_prod, Nat.cast_prod]
        apply Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
        intro p _; exact_mod_cast Nat.sub_le p 1
      have hterm1 : ((9 * (10 : ℝ) ^ (n - 1)) / (L : ℝ)) * ((∏ p ∈ F, (p - 1) : ℕ) : ℝ) / (9 * (10 : ℝ) ^ (n - 1))
          = (1 / (M : ℝ)) * (∏ p ∈ F, (1 - (1 : ℝ) / (p : ℝ))) := by
        have hL_cast : (L : ℝ) = (M : ℝ) * (P : ℝ) := by exact_mod_cast rfl
        rw [← hprod_eq_R, hL_cast]
        have h1ne : 9 * (10 : ℝ) ^ (n - 1) ≠ 0 := by positivity
        have hMne : (M : ℝ) ≠ 0 := by positivity
        have hPne : (P : ℝ) ≠ 0 := by positivity
        field_simp
      have hterm1_lt : (1 / (M : ℝ)) * (∏ p ∈ F, (1 - (1 : ℝ) / (p : ℝ))) < δ / 2 := by
        calc (1 / (M : ℝ)) * (∏ p ∈ F, (1 - (1 : ℝ) / (p : ℝ)))
            < (1 / (M : ℝ)) * ((M : ℝ) * δ / 2) := mul_lt_mul_of_pos_left hprod_lt (by positivity)
          _ = δ / 2 := by field_simp
      have hterm2_lt : ((∏ p ∈ F, (p - 1) : ℕ) : ℝ) / (9 * (10 : ℝ) ^ (n - 1)) < δ / 2 := by
        have hPL : (P : ℝ) ≤ (L : ℝ) := by
          have : P ≤ M * P := Nat.le_mul_of_pos_left P hM
          exact_mod_cast this
        have hmono_R : (9 * (10 : ℝ) ^ (N0 - 1)) ≤ 9 * (10 : ℝ) ^ (n - 1) := by
          have : (10 : ℝ) ^ (N0 - 1) ≤ (10 : ℝ) ^ (n - 1) := by exact_mod_cast hpow_mono
          linarith
        calc ((∏ p ∈ F, (p - 1) : ℕ) : ℝ) / (9 * (10 : ℝ) ^ (n - 1))
            ≤ (L : ℝ) / (9 * (10 : ℝ) ^ (n - 1)) := by
              apply div_le_div_of_nonneg_right (le_trans hprod_le_P hPL) (by positivity)
          _ ≤ (L : ℝ) / (9 * (10 : ℝ) ^ (N0 - 1)) :=
              div_le_div_of_nonneg_left (by positivity) (by positivity) hmono_R
          _ < δ / 2 := hN0.2.2.2
      have h2 : (Missed.card : ℝ) / (9 * (10 : ℝ) ^ (n - 1)) ≤
          (((9 * (10 : ℝ) ^ (n - 1)) / (L : ℝ)) * ((∏ p ∈ F, (p - 1) : ℕ) : ℝ) / (9 * (10 : ℝ) ^ (n - 1))) +
          (((∏ p ∈ F, (p - 1) : ℕ) : ℝ) / (9 * (10 : ℝ) ^ (n - 1))) := by
        rw [← add_div]
        have hfac : ((9 * (10 : ℝ) ^ (n - 1)) / (L : ℝ)) * ((∏ p ∈ F, (p - 1) : ℕ) : ℝ) +
            ((∏ p ∈ F, (p - 1) : ℕ) : ℝ) =
            ((9 * (10 : ℝ) ^ (n - 1)) / (L : ℝ) + 1) * ((∏ p ∈ F, (p - 1) : ℕ) : ℝ) := by ring
        rw [hfac]
        apply div_le_div_of_nonneg_right _ (by positivity)
        have : (((9 * 10 ^ (n - 1)) / L : ℕ) + 1 : ℝ) * ((∏ p ∈ F, (p - 1) : ℕ) : ℝ) ≤
            ((9 * (10 : ℝ) ^ (n - 1)) / (L : ℝ) + 1) * ((∏ p ∈ F, (p - 1) : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
        linarith
      linarith
    rw [Real.dist_eq, abs_lt]
    have hcnt_le_R : (cnt n : ℝ) ≤ (t : ℝ) := by exact_mod_cast hcnt_le
    have hdiff_R : (t : ℝ) - (cnt n : ℝ) ≤ (Missed.card : ℝ) := by
      have : (t - cnt n : ℕ) ≤ Missed.card := hdiff_le
      have hcast : ((t - cnt n : ℕ) : ℝ) ≤ (Missed.card : ℝ) := by exact_mod_cast this
      rw [Nat.cast_sub hcnt_le] at hcast
      exact hcast
    have hupper : (cnt n : ℝ) / (9 * (10 : ℝ) ^ (n - 1)) ≤ (1 : ℝ) / (M : ℝ) := by
      rw [← ht_real]; exact div_le_div_of_nonneg_right hcnt_le_R (by positivity)
    have hlower : (1 : ℝ) / (M : ℝ) - (cnt n : ℝ) / (9 * (10 : ℝ) ^ (n - 1)) ≤
        (Missed.card : ℝ) / (9 * (10 : ℝ) ^ (n - 1)) := by
      rw [← ht_real, ← sub_div]
      exact div_le_div_of_nonneg_right hdiff_R (by positivity)
    constructor <;> linarith
  -- Deduce cnt n / cnt (n - 1) → 10 from hdens!
  have hdens_prev : Tendsto (fun n : ℕ => (cnt (n - 1) : ℝ) / (9 * (10 : ℝ) ^ (n - 1 - 1)))
      atTop (nhds ((1 : ℝ) / (M : ℝ))) :=
    hdens.comp (tendsto_sub_atTop_nat 1)
  have hM_ne : (1 : ℝ) / (M : ℝ) ≠ 0 := by positivity
  have hquot : Tendsto (fun n : ℕ =>
      10 * ((cnt n : ℝ) / (9 * (10 : ℝ) ^ (n - 1))) /
        ((cnt (n - 1) : ℝ) / (9 * (10 : ℝ) ^ (n - 1 - 1)))) atTop (nhds (10 : ℝ)) := by
    have h1 := (hdens.const_mul (10 : ℝ)).div hdens_prev hM_ne
    have hlim : 10 * ((1 : ℝ) / (M : ℝ)) / ((1 : ℝ) / (M : ℝ)) = 10 := by
      rw [mul_div_cancel_right₀ _ hM_ne]
    rwa [hlim] at h1
  refine hquot.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hpow : (10 : ℝ) ^ (n - 1) = 10 * (10 : ℝ) ^ (n - 1 - 1) := by
    rw [← pow_succ', show n - 1 - 1 + 1 = n - 1 by omega]
  have hpne : (10 : ℝ) ^ (n - 1 - 1) ≠ 0 := by positivity
  rw [hpow]
  field_simp
  rfl

private theorem prove_main : type_of% @OMA.S_oeis_a346952.main := by
  classical
  have hmain := ratio_tendsto_ten_of_progression_sieve IsProdEnd3 10 9 3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
    (fun m ⟨x, y, hx, hy, hxy⟩ => by rw [hxy, Nat.mul_mod, hx, hy])
    ⟨0, fun m _ hm9 ⟨p, _, hp3, hpm, _⟩ => by
      refine ⟨p, m / p, hp3, ?_, (Nat.mul_div_cancel' hpm).symm⟩
      have hmul : p * (m / p) = m := Nat.mul_div_cancel' hpm
      have hmod : (p * (m / p)) % 10 = 9 := by rw [hmul]; exact hm9
      rw [Nat.mul_mod, hp3] at hmod
      omega⟩
  simpa [a] using hmain

end OMA.P_oeis_a346952

theorem OMA.solution : type_of% @OMA.S_oeis_a346952.main :=
  OMA.P_oeis_a346952.prove_main

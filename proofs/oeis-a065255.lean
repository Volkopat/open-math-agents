import OMAStatements.S_oeis_a065255

/-!
# OEIS A065255: `b(k)/k → 10`

Outline.  If a prime `p ≡ 9 (mod 10)` divides `m` exactly once, then `10 ∣ p + 1 ∣ σ(m)`.
The reciprocals of the primes `≡ 9 (mod 10)` have divergent sum (derived here from Mathlib's
lower bound for the L-series of the von Mangoldt function on a residue class), and a second
moment (Turán–Kubilius style) estimate then shows that the `m` without such a prime have
density `0`.  Hence `σ(m) ≡ m (mod 10)` iff `10 ∣ m` outside a set of density `0`, the counting
function of `P` is `n/10 + o(n)`, and `b(k)/k → 10`.
-/

namespace OMA.P065255

open Finset Filter Topology OMA.S_oeis_a065255

/-! ### Part A: the reciprocals of the primes `≡ 9 (mod 10)` are not summable -/

/-- Reciprocal of `n` if `n` is a prime `≡ 9 (mod 10)`, else `0`. -/
noncomputable def g (n : ℕ) : ℝ := if n.Prime ∧ (n : ZMod 10) = 9 then 1 / (n : ℝ) else 0

lemma g_nonneg (n : ℕ) : 0 ≤ g n := by
  unfold g; split_ifs <;> positivity

lemma div_rpow_le (v : ℝ) (hv : 0 ≤ v) (n : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    v / (n : ℝ) ^ x ≤ v / n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [Real.zero_rpow (by linarith : x ≠ 0)]
  · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact div_le_div_of_nonneg_left hv (by positivity) (Real.self_le_rpow_of_one_le h1 hx)

lemma prime_term_le (n : ℕ) {x : ℝ} (hx : 1 < x) :
    (if n.Prime then ArithmeticFunction.vonMangoldt.residueClass (9 : ZMod 10) n else 0) /
      (n : ℝ) ^ x ≤ g n / (x - 1) := by
  have hx1 : 0 < x - 1 := sub_pos.mpr hx
  by_cases hp : n.Prime
  · by_cases hc : (n : ZMod 10) = 9
    · have hn : (0 : ℝ) < n := by exact_mod_cast hp.pos
      have hr : ArithmeticFunction.vonMangoldt.residueClass (9 : ZMod 10) n = Real.log n := by
        simp [ArithmeticFunction.vonMangoldt.residueClass, hc,
          ArithmeticFunction.vonMangoldt_apply_prime hp]
      have hg : g n = 1 / (n : ℝ) := by simp [g, hp, hc]
      rw [if_pos hp, hr, hg]
      have hlog := Real.log_le_rpow_div hn.le hx1
      have hpow : (n : ℝ) ^ x = n * (n : ℝ) ^ (x - 1) := by
        have h := Real.rpow_add hn 1 (x - 1)
        rw [Real.rpow_one] at h
        rw [← h]; congr 1; ring
      have hpp : 0 < (n : ℝ) ^ (x - 1) := Real.rpow_pos_of_pos hn _
      rw [hpow, div_le_div_iff₀ (by positivity) hx1]
      have h2 : 1 / (n : ℝ) * (n * (n : ℝ) ^ (x - 1)) = (n : ℝ) ^ (x - 1) := by field_simp
      rw [h2]
      rwa [le_div_iff₀ hx1] at hlog
    · have hr : ArithmeticFunction.vonMangoldt.residueClass (9 : ZMod 10) n = 0 := by
        simp [ArithmeticFunction.vonMangoldt.residueClass, hc]
      rw [if_pos hp, hr, zero_div]; exact div_nonneg (g_nonneg n) hx1.le
  · rw [if_neg hp, zero_div]; exact div_nonneg (g_nonneg n) hx1.le

theorem not_summable_g : ¬ Summable g := by
  intro hg
  have ha : IsUnit (9 : ZMod 10) := by decide
  obtain ⟨C', hC'⟩ := ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound ha
  have hN := ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div (9 : ZMod 10)
  have hc : (0 : ℝ) < ((10 : ℕ).totient : ℝ)⁻¹ := by
    have : 0 < (10 : ℕ).totient := Nat.totient_pos.mpr (by norm_num)
    positivity
  generalize ((10 : ℕ).totient : ℝ)⁻¹ = c at hc hC'
  obtain ⟨N, hNt⟩ : ∃ N, ∑' k, g (k + N) < c / 2 :=
    ((tendsto_sum_nat_add g).eventually (gt_mem_nhds (half_pos hc))).exists
  have hrn : ∀ n, 0 ≤ ArithmeticFunction.vonMangoldt.residueClass (9 : ZMod 10) n :=
    ArithmeticFunction.vonMangoldt.residueClass_nonneg _
  set C0 := ∑' n : ℕ,
    (if n.Prime then 0 else ArithmeticFunction.vonMangoldt.residueClass (9 : ZMod 10) n) / n
    with hC0
  set K := ∑ n ∈ Finset.range N,
    (if n.Prime then ArithmeticFunction.vonMangoldt.residueClass (9 : ZMod 10) n else 0) / (n : ℝ)
    with hK
  set D := C' + C0 + K with hD
  have key : ∀ x : ℝ, x ∈ Set.Ioc (1 : ℝ) 2 → c / (x - 1) ≤ D + (c / 2) / (x - 1) := by
    intro x hx
    have hx1 : 0 < x - 1 := sub_pos.mpr hx.1
    have hsum : Summable fun n : ℕ =>
        ArithmeticFunction.vonMangoldt.residueClass (9 : ZMod 10) n / (n : ℝ) ^ x :=
      LSeries.summable_real_of_abscissaOfAbsConv_lt <|
        (ArithmeticFunction.vonMangoldt.abscissaOfAbsConv_residueClass_le_one (9 : ZMod 10)).trans_lt
          <| mod_cast hx.1
    set T1 : ℕ → ℝ := fun n =>
      (if n.Prime then 0 else ArithmeticFunction.vonMangoldt.residueClass (9 : ZMod 10) n) /
        (n : ℝ) ^ x with hT1
    set T2 : ℕ → ℝ := fun n =>
      (if n.Prime then ArithmeticFunction.vonMangoldt.residueClass (9 : ZMod 10) n else 0) /
        (n : ℝ) ^ x with hT2
    have hpow0 : ∀ n : ℕ, 0 ≤ (n : ℝ) ^ x := fun n => Real.rpow_nonneg (Nat.cast_nonneg n) x
    have hT1n : ∀ n, 0 ≤ T1 n := fun n => by
      simp only [hT1]; split_ifs
      · simp
      · exact div_nonneg (hrn n) (hpow0 n)
    have hT2n : ∀ n, 0 ≤ T2 n := fun n => by
      simp only [hT2]; split_ifs
      · exact div_nonneg (hrn n) (hpow0 n)
      · simp
    have hT1s : Summable T1 := Summable.of_nonneg_of_le hT1n (fun n => by
      simp only [hT1]; split_ifs
      · rw [zero_div]; exact div_nonneg (hrn n) (hpow0 n)
      · exact le_rfl) hsum
    have hT2s : Summable T2 := Summable.of_nonneg_of_le hT2n (fun n => by
      simp only [hT2]; split_ifs
      · exact le_rfl
      · rw [zero_div]; exact div_nonneg (hrn n) (hpow0 n)) hsum
    have hsplit : ∑' n : ℕ,
        ArithmeticFunction.vonMangoldt.residueClass (9 : ZMod 10) n / (n : ℝ) ^ x =
          ∑' n, T1 n + ∑' n, T2 n := by
      rw [← hT1s.tsum_add hT2s]
      refine tsum_congr fun n => ?_
      simp only [hT1, hT2]; split_ifs <;> simp
    have h1 : ∑' n, T1 n ≤ C0 := by
      refine hT1s.tsum_le_tsum (fun n => ?_) hN
      simp only [hT1]
      refine div_rpow_le _ ?_ n hx.1.le
      split_ifs
      · exact le_rfl
      · exact hrn n
    have h2 : ∑' n, T2 n ≤ K + (c / 2) / (x - 1) := by
      rw [← hT2s.sum_add_tsum_nat_add N]
      refine add_le_add ?_ ?_
      · refine Finset.sum_le_sum fun n _ => ?_
        simp only [hT2]
        refine div_rpow_le _ ?_ n hx.1.le
        split_ifs
        · exact hrn n
        · exact le_rfl
      · have hgs : Summable fun i => g (i + N) / (x - 1) :=
          ((summable_nat_add_iff N).mpr hg).div_const _
        calc ∑' i, T2 (i + N) ≤ ∑' i, g (i + N) / (x - 1) :=
              ((summable_nat_add_iff N).mpr hT2s).tsum_le_tsum
                (fun i => prime_term_le (i + N) hx.1) hgs
          _ = (∑' i, g (i + N)) / (x - 1) := tsum_div_const
          _ ≤ (c / 2) / (x - 1) := div_le_div_of_nonneg_right hNt.le hx1.le
    have h3 := hC' hx
    rw [hsplit] at h3
    linarith
  have hD2 : c / 2 ≤ D := by
    have h := key 2 ⟨by norm_num, le_rfl⟩
    norm_num at h
    linarith
  have hDpos : 0 < D := lt_of_lt_of_le (half_pos hc) hD2
  have hδ : 0 < c / (4 * D) := by positivity
  have hδ1 : c / (4 * D) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have h := key (1 + c / (4 * D)) ⟨by linarith, by linarith⟩
  rw [add_sub_cancel_left] at h
  have e1 : c / (c / (4 * D)) = 4 * D := by field_simp
  have e2 : c / 2 / (c / (4 * D)) = 2 * D := by field_simp; ring
  rw [e1, e2] at h
  linarith

/-- Finite sets of primes `≡ 9 (mod 10)` with arbitrarily large reciprocal sum. -/
lemma exists_S (T : ℝ) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p % 10 = 9) ∧ T ≤ ∑ p ∈ S, 1 / (p : ℝ) := by
  have h := (not_summable_iff_tendsto_nat_atTop_of_nonneg g_nonneg).mp not_summable_g
  obtain ⟨n, hn⟩ := (h.eventually_ge_atTop T).exists
  refine ⟨(Finset.range n).filter fun p => p.Prime ∧ (p : ZMod 10) = 9, ?_, ?_⟩
  · intro p hp
    obtain ⟨_, hpp, hpc⟩ := Finset.mem_filter.mp hp
    refine ⟨hpp, ?_⟩
    have h9 : (p : ZMod 10) = ((9 : ℕ) : ZMod 10) := by simpa using hpc
    simpa using (ZMod.natCast_eq_natCast_iff' p 9 10).mp h9
  · rw [Finset.sum_filter]; exact hn

/-! ### Part B: the second moment sieve -/

/-- Indicator of `p` dividing `m` exactly once. -/
noncomputable def e (p m : ℕ) : ℝ := if p ∣ m ∧ ¬ p ^ 2 ∣ m then 1 else 0

lemma sum_dvd (x d : ℕ) :
    ∑ m ∈ Ioc 0 x, (if d ∣ m then (1 : ℝ) else 0) = ((x / d : ℕ) : ℝ) := by
  rw [Finset.sum_boole, Nat.Ioc_filter_dvd_card_eq_div]

lemma cast_div_ge (x d : ℕ) (hd : 0 < d) : (x : ℝ) / d - 1 ≤ ((x / d : ℕ) : ℝ) := by
  have h : x < d * (x / d + 1) := Nat.lt_mul_div_succ x hd
  have h' : (x : ℝ) < d * (((x / d : ℕ) : ℝ) + 1) := by exact_mod_cast h
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [sub_le_iff_le_add, div_le_iff₀ hd']
  linarith

lemma first_moment (x p : ℕ) (hp : 0 < p) :
    (x : ℝ) / p - 1 - (x : ℝ) / (p : ℝ) ^ 2 ≤ ∑ m ∈ Ioc 0 x, e p m := by
  have h : ∀ m, (if p ∣ m then (1 : ℝ) else 0) - (if p ^ 2 ∣ m then (1 : ℝ) else 0) ≤ e p m := by
    intro m
    unfold e
    by_cases h1 : p ∣ m <;> by_cases h2 : p ^ 2 ∣ m <;> simp [h1, h2]
  have h1 := cast_div_ge x p hp
  have h2 : ((x / p ^ 2 : ℕ) : ℝ) ≤ (x : ℝ) / (p : ℝ) ^ 2 := by
    have h3 : ((x / p ^ 2 : ℕ) : ℝ) ≤ (x : ℝ) / ((p ^ 2 : ℕ) : ℝ) := Nat.cast_div_le
    push_cast at h3
    exact h3
  calc (x : ℝ) / p - 1 - (x : ℝ) / (p : ℝ) ^ 2
      ≤ ((x / p : ℕ) : ℝ) - ((x / p ^ 2 : ℕ) : ℝ) := by linarith
    _ = ∑ m ∈ Ioc 0 x,
          ((if p ∣ m then (1 : ℝ) else 0) - (if p ^ 2 ∣ m then (1 : ℝ) else 0)) := by
        rw [Finset.sum_sub_distrib, sum_dvd, sum_dvd]
    _ ≤ ∑ m ∈ Ioc 0 x, e p m := Finset.sum_le_sum fun m _ => h m

lemma second_moment (x p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    ∑ m ∈ Ioc 0 x, e p m * e q m ≤
      (x : ℝ) / ((p : ℝ) * q) + (if p = q then (x : ℝ) / p else 0) := by
  by_cases hpq : p = q
  · subst hpq
    rw [if_pos rfl]
    have h : ∀ m, e p m * e p m ≤ (if p ∣ m then (1 : ℝ) else 0) := by
      intro m; unfold e
      by_cases h1 : p ∣ m <;> by_cases h2 : p ^ 2 ∣ m <;> simp [h1, h2]
    calc ∑ m ∈ Ioc 0 x, e p m * e p m
        ≤ ∑ m ∈ Ioc 0 x, (if p ∣ m then (1 : ℝ) else 0) := Finset.sum_le_sum fun m _ => h m
      _ = ((x / p : ℕ) : ℝ) := sum_dvd x p
      _ ≤ (x : ℝ) / p := Nat.cast_div_le
      _ ≤ (x : ℝ) / ((p : ℝ) * p) + (x : ℝ) / p := le_add_of_nonneg_left (by positivity)
  · rw [if_neg hpq, add_zero]
    have hco : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
    have h : ∀ m, e p m * e q m ≤ (if p * q ∣ m then (1 : ℝ) else 0) := by
      intro m; unfold e
      by_cases h1 : p ∣ m
      · by_cases h2 : q ∣ m
        · rw [if_pos (hco.mul_dvd_of_dvd_of_dvd h1 h2)]
          split_ifs <;> norm_num
        · rw [if_neg (fun h : q ∣ m ∧ ¬ q ^ 2 ∣ m => h2 h.1), mul_zero]; split_ifs <;> norm_num
      · rw [if_neg (fun h : p ∣ m ∧ ¬ p ^ 2 ∣ m => h1 h.1), zero_mul]; split_ifs <;> norm_num
    calc ∑ m ∈ Ioc 0 x, e p m * e q m
        ≤ ∑ m ∈ Ioc 0 x, (if p * q ∣ m then (1 : ℝ) else 0) := Finset.sum_le_sum fun m _ => h m
      _ = ((x / (p * q) : ℕ) : ℝ) := sum_dvd x (p * q)
      _ ≤ (x : ℝ) / ((p * q : ℕ) : ℝ) := Nat.cast_div_le
      _ = (x : ℝ) / ((p : ℝ) * q) := by push_cast; rfl

theorem sieve (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (x : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hB : ∑ p ∈ S, 1 / (p : ℝ) ^ 2 ≤ C) (hA : 1 ≤ ∑ p ∈ S, 1 / (p : ℝ)) :
    (((Ioc 0 x).filter fun m => ¬ ∃ p ∈ S, p ∣ m ∧ ¬ p ^ 2 ∣ m).card : ℝ) *
        ∑ p ∈ S, 1 / (p : ℝ)
      ≤ x * (1 + 2 * C) + 2 * S.card * ∑ p ∈ S, 1 / (p : ℝ) := by
  set A := ∑ p ∈ S, 1 / (p : ℝ) with hAdef
  set B := ∑ p ∈ S, 1 / (p : ℝ) ^ 2 with hBdef
  set G := (Ioc 0 x).filter fun m => ∃ p ∈ S, p ∣ m ∧ ¬ p ^ 2 ∣ m with hG
  have hE0 : ∀ m, 0 ≤ ∑ p ∈ S, e p m := fun m =>
    Finset.sum_nonneg fun p _ => by unfold e; split_ifs <;> norm_num
  have hEG : ∀ m ∈ Ioc 0 x, m ∉ G → ∑ p ∈ S, e p m = 0 := by
    intro m hm hmG
    refine Finset.sum_eq_zero fun p hp => ?_
    unfold e
    rw [if_neg]
    intro h
    exact hmG (Finset.mem_filter.mpr ⟨hm, p, hp, h⟩)
  have hM1 : (x : ℝ) * A - S.card - x * B ≤ ∑ m ∈ Ioc 0 x, ∑ p ∈ S, e p m := by
    rw [Finset.sum_comm]
    have h : (x : ℝ) * A - S.card - x * B =
        ∑ p ∈ S, ((x : ℝ) / p - 1 - (x : ℝ) / (p : ℝ) ^ 2) := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hAdef, hBdef, Finset.mul_sum,
        Finset.mul_sum]
      simp [div_eq_mul_inv]
    rw [h]
    exact Finset.sum_le_sum fun p hp => first_moment x p (hS p hp).pos
  have hM2 : ∑ m ∈ Ioc 0 x, (∑ p ∈ S, e p m) ^ 2 ≤ x * (A ^ 2 + A) := by
    have h1 : ∀ m, (∑ p ∈ S, e p m) ^ 2 = ∑ p ∈ S, ∑ q ∈ S, e p m * e q m := by
      intro m; rw [sq, Finset.sum_mul_sum]
    have e1 : ∀ p ∈ S,
        ∑ q ∈ S, ((x : ℝ) / ((p : ℝ) * q) + (if p = q then (x : ℝ) / p else 0)) =
          x * (1 / (p : ℝ)) * A + x * (1 / (p : ℝ)) := by
      intro p hp
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos hp, hAdef, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun q _ => by ring
      · ring
    calc ∑ m ∈ Ioc 0 x, (∑ p ∈ S, e p m) ^ 2
        = ∑ p ∈ S, ∑ q ∈ S, ∑ m ∈ Ioc 0 x, e p m * e q m := by
          simp_rw [h1]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun p _ => Finset.sum_comm
      _ ≤ ∑ p ∈ S, ∑ q ∈ S,
            ((x : ℝ) / ((p : ℝ) * q) + (if p = q then (x : ℝ) / p else 0)) :=
          Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq =>
            second_moment x p q (hS p hp) (hS q hq)
      _ = x * (A ^ 2 + A) := by
          rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, ← Finset.sum_mul,
            ← Finset.mul_sum]
          ring
  have hCS : (∑ m ∈ Ioc 0 x, ∑ p ∈ S, e p m) ^ 2 ≤ (G.card : ℝ) * (x * (A ^ 2 + A)) := by
    have hsub : G ⊆ Ioc 0 x := Finset.filter_subset _ _
    have h1 : ∑ m ∈ Ioc 0 x, ∑ p ∈ S, e p m = ∑ m ∈ G, ∑ p ∈ S, e p m :=
      (Finset.sum_subset hsub hEG).symm
    have h2 : ∑ m ∈ G, (∑ p ∈ S, e p m) ^ 2 ≤ ∑ m ∈ Ioc 0 x, (∑ p ∈ S, e p m) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => sq_nonneg _
    rw [h1]
    calc (∑ m ∈ G, ∑ p ∈ S, e p m) ^ 2
        ≤ (G.card : ℝ) * ∑ m ∈ G, (∑ p ∈ S, e p m) ^ 2 := sq_sum_le_card_mul_sum_sq
      _ ≤ (G.card : ℝ) * (x * (A ^ 2 + A)) :=
          mul_le_mul_of_nonneg_left (h2.trans hM2) (Nat.cast_nonneg _)
  have hcard : (((Ioc 0 x).filter fun m => ¬ ∃ p ∈ S, p ∣ m ∧ ¬ p ^ 2 ∣ m).card : ℝ) +
      G.card = x := by
    rw [hG, ← Finset.sum_boole, ← Finset.sum_boole, ← Finset.sum_add_distrib]
    have h : ∀ m ∈ Ioc 0 x,
        ((if ¬ ∃ p ∈ S, p ∣ m ∧ ¬ p ^ 2 ∣ m then (1 : ℝ) else 0) +
          (if ∃ p ∈ S, p ∣ m ∧ ¬ p ^ 2 ∣ m then (1 : ℝ) else 0)) = 1 := by
      intro m _
      by_cases hm : ∃ p ∈ S, p ∣ m ∧ ¬ p ^ 2 ∣ m <;> simp [hm]
    rw [Finset.sum_congr rfl h]
    simp
  have hM10 : 0 ≤ ∑ m ∈ Ioc 0 x, ∑ p ∈ S, e p m := Finset.sum_nonneg fun m _ => hE0 m
  generalize ∑ m ∈ Ioc 0 x, ∑ p ∈ S, e p m = M1 at hM1 hCS hM10
  generalize (((Ioc 0 x).filter fun m => ¬ ∃ p ∈ S, p ∣ m ∧ ¬ p ^ 2 ∣ m).card : ℝ) = bad
    at hcard ⊢
  have hg0 : (0 : ℝ) ≤ G.card := Nat.cast_nonneg _
  generalize (G.card : ℝ) = gg at hcard hCS hg0
  have hs0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  generalize (S.card : ℝ) = s at hM1 hs0 ⊢
  have hX0 : (0 : ℝ) ≤ x := Nat.cast_nonneg _
  generalize (x : ℝ) = X at hM1 hCS hcard hX0 ⊢
  have hL : X * (A - C) - s ≤ M1 := by
    have := mul_le_mul_of_nonneg_left hB hX0
    linarith
  have hbad : bad = X - gg := by linarith
  rw [hbad]
  by_contra hcon
  rw [not_le] at hcon
  have hgA : 0 ≤ gg * A := mul_nonneg hg0 (by linarith)
  have hXC : 0 ≤ X * C := mul_nonneg hX0 hC
  have hsA : 0 ≤ s * (A - 1) := mul_nonneg hs0 (by linarith)
  rcases le_or_gt (X * (A - C) - s) 0 with hL0 | hL0
  · linarith
  · have h3 : (X * (A - C) - s) ^ 2 ≤ gg * (X * (A ^ 2 + A)) :=
      (pow_le_pow_left₀ hL0.le hL 2).trans hCS
    have hXpos : 0 < X := by
      by_contra hX
      have hX' : X = 0 := le_antisymm (not_lt.mp hX) hX0
      rw [hX'] at hL0
      linarith
    have h4 : gg * A * (X * (A + 1)) < (X * A - X * (1 + 2 * C) - 2 * s * A) * (X * (A + 1)) :=
      mul_lt_mul_of_pos_right (by linarith) (mul_pos hXpos (by linarith))
    have h5 : (X * (A - C) - s) ^ 2 - (X * A - X * (1 + 2 * C) - 2 * s * A) * (X * (A + 1)) =
        X ^ 2 * (C + 1) ^ 2 + s ^ 2 + 2 * s * X * (A ^ 2 + C) := by ring
    have h6 : 0 ≤ X ^ 2 * (C + 1) ^ 2 + s ^ 2 + 2 * s * X * (A ^ 2 + C) :=
      add_nonneg (add_nonneg (by positivity) (by positivity))
        (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hs0) hX0) (add_nonneg (sq_nonneg A) hC))
    have h7 : gg * A * (X * (A + 1)) = gg * (X * (A ^ 2 + A)) := by ring
    linarith

/-! ### Part C: a prime `≡ 9 (mod 10)` dividing `m` exactly once forces `10 ∣ σ(m)` -/

lemma ten_dvd_sigma {p m : ℕ} (hp : p.Prime) (hp9 : p % 10 = 9) (h1 : p ∣ m)
    (h2 : ¬ p ^ 2 ∣ m) : 10 ∣ ∑ d ∈ m.divisors, d := by
  obtain ⟨k, rfl⟩ := h1
  have hk : ¬ p ∣ k := fun h => h2 (by rw [sq]; exact Nat.mul_dvd_mul_left p h)
  have hco : Nat.Coprime p k := (Nat.Prime.coprime_iff_not_dvd hp).mpr hk
  have h := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime hco
  rw [ArithmeticFunction.sigma_one_apply, ArithmeticFunction.sigma_one_apply,
    ArithmeticFunction.sigma_one_apply] at h
  rw [h, hp.divisors, Finset.sum_pair hp.one_lt.ne]
  exact Dvd.dvd.mul_right (by omega : 10 ∣ 1 + p) _

/-! ### Part D: counting and the limit -/

open Classical in
lemma count_bound (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p % 10 = 9) (n : ℕ) :
    |(Nat.count P n : ℝ) - (n : ℝ) / 10| ≤
      (((Ioc 0 n).filter fun m => ¬ ∃ p ∈ S, p ∣ m ∧ ¬ p ^ 2 ∣ m).card : ℝ) + 1 := by
  set Bad := (Ioc 0 n).filter fun m => ¬ ∃ p ∈ S, p ∣ m ∧ ¬ p ^ 2 ∣ m with hBad
  set a := (range n).filter P with ha
  set c := (range n).filter fun m => 1 ≤ m ∧ 10 ∣ m with hc
  have hkey : ∀ m ∈ range n, m ∉ Bad → (P m ↔ (1 ≤ m ∧ 10 ∣ m)) := by
    intro m hm hmb
    by_cases hm0 : m = 0
    · subst hm0; simp [P]
    have hmI : m ∈ Ioc 0 n :=
      Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hm0, (Finset.mem_range.mp hm).le⟩
    have hgood : ∃ p ∈ S, p ∣ m ∧ ¬ p ^ 2 ∣ m := by
      by_contra h; exact hmb (Finset.mem_filter.mpr ⟨hmI, h⟩)
    obtain ⟨p, hp, h1, h2⟩ := hgood
    have h10 := ten_dvd_sigma (hS p hp).1 (hS p hp).2 h1 h2
    unfold P
    constructor
    · rintro ⟨h, he⟩; exact ⟨h, by omega⟩
    · rintro ⟨h, hd⟩; exact ⟨h, by omega⟩
  have hac : a ⊆ c ∪ Bad := by
    intro m hm
    obtain ⟨hmr, hPm⟩ := Finset.mem_filter.mp hm
    by_cases hb : m ∈ Bad
    · exact Finset.mem_union_right _ hb
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hmr, (hkey m hmr hb).mp hPm⟩)
  have hca : c ⊆ a ∪ Bad := by
    intro m hm
    obtain ⟨hmr, hQm⟩ := Finset.mem_filter.mp hm
    by_cases hb : m ∈ Bad
    · exact Finset.mem_union_right _ hb
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hmr, (hkey m hmr hb).mpr hQm⟩)
  have h1 : a.card ≤ c.card + Bad.card :=
    (Finset.card_le_card hac).trans (Finset.card_union_le _ _)
  have h2 : c.card ≤ a.card + Bad.card :=
    (Finset.card_le_card hca).trans (Finset.card_union_le _ _)
  have hcc : c.card = (n - 1) / 10 := by
    have h : c = (Ioc 0 (n - 1)).filter fun m => 10 ∣ m := by
      ext m
      simp only [hc, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
      omega
    rw [h, Nat.Ioc_filter_dvd_card_eq_div]
  have h3 : 10 * c.card ≤ n ∧ n ≤ 10 * c.card + 10 := by rw [hcc]; omega
  have haa : Nat.count P n = a.card := Nat.count_eq_card_filter_range P n
  have h1' : (a.card : ℝ) ≤ c.card + Bad.card := by exact_mod_cast h1
  have h2' : (c.card : ℝ) ≤ a.card + Bad.card := by exact_mod_cast h2
  have h3a : (10 : ℝ) * c.card ≤ n := by exact_mod_cast h3.1
  have h3b : (n : ℝ) ≤ 10 * c.card + 10 := by exact_mod_cast h3.2
  rw [haa, abs_le]
  constructor <;> linarith

open Classical in
lemma count_asymp (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, |(Nat.count P n : ℝ) - (n : ℝ) / 10| ≤ ε * n + K := by
  have hsum : Summable fun n : ℕ => 1 / (n : ℝ) ^ 2 :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  set C := ∑' n : ℕ, 1 / (n : ℝ) ^ 2 with hCdef
  have hC : 0 ≤ C := tsum_nonneg fun n => by positivity
  obtain ⟨S, hS, hSA⟩ := exists_S (max 1 ((1 + 2 * C) / ε))
  refine ⟨2 * S.card + 1, by positivity, fun n => ?_⟩
  have hB : ∑ p ∈ S, 1 / (p : ℝ) ^ 2 ≤ C :=
    hsum.sum_le_tsum S fun n _ => by positivity
  have hA1 : 1 ≤ ∑ p ∈ S, 1 / (p : ℝ) := (le_max_left _ _).trans hSA
  have hA2 : (1 + 2 * C) / ε ≤ ∑ p ∈ S, 1 / (p : ℝ) := (le_max_right _ _).trans hSA
  have hsv := sieve S (fun p hp => (hS p hp).1) n C hC hB hA1
  have hcb := count_bound S hS n
  generalize ∑ p ∈ S, 1 / (p : ℝ) = A at hA1 hA2 hsv
  generalize (((Ioc 0 n).filter fun m => ¬ ∃ p ∈ S, p ∣ m ∧ ¬ p ^ 2 ∣ m).card : ℝ) = bad
    at hsv hcb
  have h12 : 1 + 2 * C ≤ ε * A := by rwa [div_le_iff₀' hε] at hA2
  have hApos : 0 < A := by linarith
  have hbad : bad ≤ ε * n + 2 * S.card := by
    have h := mul_le_mul_of_nonneg_left h12 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have h' : bad * A ≤ (ε * n + 2 * S.card) * A := by linarith
    exact le_of_mul_le_mul_right h' hApos
  linarith

lemma P_infinite : {m | P m}.Infinite := by
  classical
  intro hfin
  obtain ⟨K, hK0, hK⟩ := count_asymp (1 / 20) (by norm_num)
  obtain ⟨n, hn⟩ := exists_nat_gt (20 * ((hfin.toFinset.card : ℝ) + K + 1))
  have h1 := abs_le.mp (hK n)
  have h2 : Nat.count P n ≤ hfin.toFinset.card := Nat.count_le_card hfin n
  have h2' : (Nat.count P n : ℝ) ≤ hfin.toFinset.card := by exact_mod_cast h2
  linarith [h1.1]

theorem main_aux : Tendsto (fun k : ℕ => (b k : ℝ) / k) atTop (𝓝 10) := by
  classical
  rw [Metric.tendsto_atTop]
  intro η hη
  have hε0 : 0 < min (1 / 20 : ℝ) (η / 400) := lt_min (by norm_num) (by positivity)
  have he1 : min (1 / 20 : ℝ) (η / 400) ≤ 1 / 20 := min_le_left _ _
  have he2 : min (1 / 20 : ℝ) (η / 400) ≤ η / 400 := min_le_right _ _
  obtain ⟨K, hK0, hK⟩ := count_asymp (min (1 / 20 : ℝ) (η / 400)) hε0
  generalize min (1 / 20 : ℝ) (η / 400) = ε at hε0 he1 he2 hK
  refine ⟨⌈2 * (10 + 20 * K) / η⌉₊ + 1, fun k hk => ?_⟩
  have hk1 : 1 ≤ k := le_trans (Nat.le_add_left 1 _) hk
  have hkR : 2 * (10 + 20 * K) / η < k := by
    have h1 := Nat.le_ceil (2 * (10 + 20 * K) / η)
    have h2 : ((⌈2 * (10 + 20 * K) / η⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
    push_cast at h2
    linarith
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hcount : Nat.count P (b k) = k - 1 := Nat.count_nth_of_infinite P_infinite (k - 1)
  have h := abs_le.mp (hK (b k))
  rw [hcount, Nat.cast_sub hk1, Nat.cast_one] at h
  have hn0 : (0 : ℝ) ≤ b k := Nat.cast_nonneg _
  generalize (b k : ℝ) = n at h hn0 ⊢
  have hen := mul_le_mul_of_nonneg_right he1 hn0
  have hnk : n ≤ 20 * (k + K) := by linarith [h.1]
  have hεn : ε * n ≤ (η / 20) * k + K := by
    have a1 : ε * n ≤ ε * (20 * (k + K)) := mul_le_mul_of_nonneg_left hnk hε0.le
    have a2 : ε * k ≤ (η / 400) * k := mul_le_mul_of_nonneg_right he2 hkpos.le
    have a3 : ε * K ≤ (1 / 20) * K := mul_le_mul_of_nonneg_right he1 hK0
    linarith
  have hd : |n - 10 * k| ≤ 10 + 20 * K + (η / 2) * k := by
    rw [abs_le]; constructor <;> linarith [h.1, h.2]
  rw [Real.dist_eq]
  have hq : n / k - 10 = (n - 10 * k) / k := by field_simp
  rw [hq, abs_div, abs_of_pos hkpos, div_lt_iff₀ hkpos]
  have hk2 : 2 * (10 + 20 * K) < k * η := by rwa [div_lt_iff₀ hη] at hkR
  linarith

end OMA.P065255

theorem OMA.solution : type_of% @OMA.S_oeis_a065255.main := OMA.P065255.main_aux

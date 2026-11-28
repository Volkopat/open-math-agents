import OMAStatements.S_erdos_371

/-!
# Erdős 371 from Dickman's marginal law and asymptotic independence

`P n` is the largest prime factor (`n.primeFactors.sup id`, as in the statement).

* `H1` (Dickman's law, for `P(n)` and for `P(n+1)`, both measured against `n`): for `0 < a < 1`
  the densities of `P(n) ≤ n^a` and of `P(n+1) ≤ n^a` tend to `F a`, where `F` is continuous on
  `[0, 1]` with `F 0 = 0` and `F 1 = 1` (for Dickman's function, `F a = ρ(1/a)`).
* `H2` (asymptotic independence of `P(n)` and `P(n+1)`): the density of
  `P(n) ≤ n^a ∧ P(n+1) ≤ n^b` minus the product of the two marginal densities tends to `0`.

The deduction adapts the strip argument of OpenAI/math@3344da59991ed94f9ba711217b29c1d760badfa6,
`OAI.NumberTheory.JointDickman.Amplification.Ordering` (`increasingOrderLaw_of_jointDickmanLaw`),
there proved for Dickman's function: disjoint strips between quantiles of `F` lie below or above the
diagonal, each carrying limiting mass `F(t_i) (F(t_{i+1}) - F(t_i))`, which sums to almost `1/2`;
since `P(n) ≠ P(n+1)` for `n ≥ 1`, the two orderings together have density one.
-/

namespace OMA.R_erdos_371_R1

open Filter Topology

def H1 : Prop :=
  ∃ F : ℝ → ℝ, ContinuousOn F (Set.Icc 0 1) ∧ F 0 = 0 ∧ F 1 = 1 ∧
    ∀ a : ℝ, 0 < a → a < 1 →
      Tendsto (fun N : ℕ => (((Finset.Icc 1 N).filter
          (fun n : ℕ => ((n.primeFactors.sup id : ℕ) : ℝ) ≤ (n : ℝ) ^ a)).card : ℝ) / N)
        atTop (𝓝 (F a)) ∧
      Tendsto (fun N : ℕ => (((Finset.Icc 1 N).filter
          (fun n : ℕ => (((n + 1).primeFactors.sup id : ℕ) : ℝ) ≤ (n : ℝ) ^ a)).card : ℝ) / N)
        atTop (𝓝 (F a))

def H2 : Prop :=
  ∀ a b : ℝ, 0 < a → a < 1 → 0 < b → b < 1 →
    Tendsto (fun N : ℕ =>
      (((Finset.Icc 1 N).filter (fun n : ℕ => ((n.primeFactors.sup id : ℕ) : ℝ) ≤ (n : ℝ) ^ a ∧
          (((n + 1).primeFactors.sup id : ℕ) : ℝ) ≤ (n : ℝ) ^ b)).card : ℝ) / N -
      ((((Finset.Icc 1 N).filter
          (fun n : ℕ => ((n.primeFactors.sup id : ℕ) : ℝ) ≤ (n : ℝ) ^ a)).card : ℝ) / N) *
      ((((Finset.Icc 1 N).filter
          (fun n : ℕ => (((n + 1).primeFactors.sup id : ℕ) : ℝ) ≤ (n : ℝ) ^ b)).card : ℝ) / N))
      atTop (𝓝 0)

theorem dens_sub {S T R : ℕ → Prop} [DecidablePred S] [DecidablePred T] [DecidablePred R]
    (h : ∀ n, 1 ≤ n → (S n ↔ T n ∧ ¬ R n)) (hsub : ∀ n, 1 ≤ n → R n → T n) (N : ℕ) :
    (((Finset.Icc 1 N).filter T).card : ℝ) / N - (((Finset.Icc 1 N).filter R).card : ℝ) / N =
      (((Finset.Icc 1 N).filter S).card : ℝ) / N := by
  have hc : ((Finset.Icc 1 N).filter T).card =
      ((Finset.Icc 1 N).filter S).card + ((Finset.Icc 1 N).filter R).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext n
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hn, hT⟩
        by_cases hR : R n
        · exact Or.inr ⟨hn, hR⟩
        · exact Or.inl ⟨hn, (h n (Finset.mem_Icc.mp hn).1).2 ⟨hT, hR⟩⟩
      · rintro (⟨hn, hS⟩ | ⟨hn, hR⟩)
        · exact ⟨hn, ((h n (Finset.mem_Icc.mp hn).1).1 hS).1⟩
        · exact ⟨hn, hsub n (Finset.mem_Icc.mp hn).1 hR⟩
    · rw [Finset.disjoint_filter]
      intro n hn hS hR
      exact ((h n (Finset.mem_Icc.mp hn).1).1 hS).2 hR
  rw [hc, Nat.cast_add, add_div]
  ring

theorem dens_sum_le {ι : Type*} [Fintype ι] (S : ι → ℕ → Prop) [∀ i, DecidablePred (S i)]
    {Q : ℕ → Prop} [DecidablePred Q] (hdisj : ∀ n, 1 ≤ n → ∀ i j, S i n → S j n → i = j)
    (hsub : ∀ i n, 1 ≤ n → S i n → Q n) (N : ℕ) :
    ∑ i, (((Finset.Icc 1 N).filter (S i)).card : ℝ) / N ≤
      (((Finset.Icc 1 N).filter Q).card : ℝ) / N := by
  classical
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hd : (↑(Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
      (fun i => (Finset.Icc 1 N).filter (S i)) := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun n hi hj => hij ?_
    have hi' := Finset.mem_filter.mp hi
    exact hdisj n (Finset.mem_Icc.mp hi'.1).1 i j hi'.2 (Finset.mem_filter.mp hj).2
  have hs : Finset.univ.biUnion (fun i => (Finset.Icc 1 N).filter (S i)) ⊆
      (Finset.Icc 1 N).filter Q := by
    intro n hn
    obtain ⟨i, _, hni⟩ := Finset.mem_biUnion.mp hn
    have hi' := Finset.mem_filter.mp hni
    exact Finset.mem_filter.mpr ⟨hi'.1, hsub i n (Finset.mem_Icc.mp hi'.1).1 hi'.2⟩
  have hc := Finset.card_le_card hs
  rw [Finset.card_biUnion hd] at hc
  exact_mod_cast hc

theorem half_of_approx (inc dec mass : ℕ → ℝ)
    (hsum : Tendsto (fun N => inc N + dec N) atTop (𝓝 1))
    (hmass : Tendsto mass atTop (𝓝 (1 / 2)))
    (happrox : ∀ m, ∃ f g : ℕ → ℝ, Tendsto f atTop (𝓝 (mass m)) ∧
      Tendsto g atTop (𝓝 (mass m)) ∧ (∀ N, f N ≤ inc N) ∧ ∀ N, g N ≤ dec N) :
    Tendsto inc atTop (𝓝 (1 / 2)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨m, hm⟩ := ((tendsto_order.mp hmass).1 a ha).exists
    obtain ⟨f, g, hf, -, hfI, -⟩ := happrox m
    filter_upwards [(tendsto_order.mp hf).1 a hm] with N hN
    exact hN.trans_le (hfI N)
  · intro b hb
    obtain ⟨m, hm⟩ := ((tendsto_order.mp hmass).1 (1 - b) (by linarith)).exists
    obtain ⟨f, g, -, hg, -, hgD⟩ := happrox m
    have hc : 1 < (1 + b + mass m) / 2 := by linarith
    filter_upwards [(tendsto_order.mp hsum).2 _ hc,
      (tendsto_order.mp hg).1 ((1 + b + mass m) / 2 - b) (by linarith)] with N h1 h2
    have := hgD N
    linarith

theorem exists_grid {F : ℝ → ℝ} (hc : ContinuousOn F (Set.Icc 0 1)) (h0 : F 0 = 0)
    (h1 : F 1 = 1) (hmono : ∀ a b : ℝ, 0 < a → a ≤ b → b < 1 → F a ≤ F b) (m : ℕ) :
    ∃ t : Fin (m + 1) → ℝ,
      (∀ i, 0 < t i ∧ t i < 1 ∧ F (t i) = ((i.val : ℝ) + 1) / (m + 2)) ∧ StrictMono t := by
  have hex : ∀ i : Fin (m + 1), ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      F t = ((i.val : ℝ) + 1) / (m + 2) := by
    intro i
    have hy0 : (0 : ℝ) < ((i.val : ℝ) + 1) / (m + 2) := by positivity
    have hy1 : ((i.val : ℝ) + 1) / (m + 2) < 1 := by
      rw [div_lt_one (by positivity)]
      have : (i.val : ℝ) < m + 1 := by exact_mod_cast i.isLt
      linarith
    obtain ⟨t, ht, hty⟩ := intermediate_value_Icc (zero_le_one' ℝ) hc
      (show ((i.val : ℝ) + 1) / (m + 2) ∈ Set.Icc (F 0) (F 1) by
        rw [h0, h1]; exact ⟨hy0.le, hy1.le⟩)
    refine ⟨t, lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_, hty⟩
    · rintro rfl
      rw [h0] at hty
      linarith
    · rintro rfl
      rw [h1] at hty
      linarith
  choose t ht using hex
  refine ⟨t, ht, fun i j hij => ?_⟩
  by_contra hle
  have hle' : t j ≤ t i := le_of_not_gt hle
  have hF := hmono (t j) (t i) (ht j).1 hle' (ht i).2.1
  rw [(ht i).2.2, (ht j).2.2] at hF
  have hv : (i.val : ℝ) < j.val := by exact_mod_cast hij
  have := (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < m + 2)).mp hF
  linarith

theorem sum_fin_cast_add_one (m : ℕ) :
    ∑ i : Fin m, ((i.val : ℝ) + 1) = (m : ℝ) * (m + 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih, Nat.cast_add, Nat.cast_one]
    ring

theorem grid_mass {F : ℝ → ℝ} {m : ℕ} {t : Fin (m + 1) → ℝ}
    (hq : ∀ i, F (t i) = ((i.val : ℝ) + 1) / (m + 2)) :
    ∑ i : Fin m, F (t i.castSucc) * (F (t i.succ) - F (t i.castSucc)) =
      ((m : ℝ) / (m + 2)) * (((m : ℝ) + 1) / (m + 2)) / 2 := by
  have hterm : ∀ i : Fin m, F (t i.castSucc) * (F (t i.succ) - F (t i.castSucc)) =
      ((i.val : ℝ) + 1) / ((m : ℝ) + 2) ^ 2 := by
    intro i
    simp only [hq, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  simp_rw [hterm]
  rw [← Finset.sum_div, sum_fin_cast_add_one]
  field_simp

theorem mass_tendsto :
    Tendsto (fun m : ℕ => ((m : ℝ) / (m + 2)) * (((m : ℝ) + 1) / (m + 2)) / 2)
      atTop (𝓝 (1 / 2)) := by
  have hleft := tendsto_natCast_div_add_atTop (2 : ℝ)
  have hright : Tendsto (fun m : ℕ => ((m : ℝ) + 1) / (m + 2)) atTop (𝓝 1) := by
    simpa [add_comm] using
      (tendsto_add_mul_div_add_mul_atTop_nhds (d := (1 : ℝ)) (1 : ℝ) 2 1 (by norm_num))
  convert (hleft.mul hright).div_const 2 using 1
  norm_num

theorem primeFactors_sup_ne_succ (n : ℕ) (hn : 1 ≤ n) :
    n.primeFactors.sup id ≠ (n + 1).primeFactors.sup id := by
  intro heq
  have hne1 : (n + 1).primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  obtain ⟨q, hq, hqe⟩ := Finset.exists_mem_eq_sup _ hne1 id
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hne0 : n.primeFactors.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Finset.sup_empty, hqe] at heq
    exact hqp.ne_zero heq.symm
  obtain ⟨r, hr, hre⟩ := Finset.exists_mem_eq_sup _ hne0 id
  rw [hre, hqe] at heq
  have hrq : r = q := heq
  have hqn : q ∈ n.primeFactors := hrq ▸ hr
  have h1 := Nat.dvd_of_mem_primeFactors hqn
  have h2 := Nat.dvd_of_mem_primeFactors hq
  have h3 : q ∣ 1 := (Nat.dvd_add_right h1).mp h2
  exact hqp.one_lt.ne' (Nat.dvd_one.mp h3)

theorem order_half : H1 → H2 → Tendsto (fun N : ℕ => (((Finset.Icc 1 N).filter
      (fun n : ℕ => n.primeFactors.sup id < (n + 1).primeFactors.sup id)).card : ℝ) / N)
    atTop (𝓝 (1 / 2)) := by
  rintro ⟨F, hcont, hF0, hF1, hmarg⟩ hind
  have hpow : ∀ (n : ℕ) (a b : ℝ), 1 ≤ n → a ≤ b → (n : ℝ) ^ a ≤ (n : ℝ) ^ b :=
    fun n a b hn hab => Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hab
  have hmono : ∀ a b : ℝ, 0 < a → a ≤ b → b < 1 → F a ≤ F b := by
    intro a b ha hab hb
    refine le_of_tendsto_of_tendsto' (hmarg a ha (hab.trans_lt hb)).1
      (hmarg b (ha.trans_le hab) hb).1 fun N => ?_
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    refine Nat.cast_le.mpr (Finset.card_le_card fun n hn => ?_)
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.trans (hpow n a b (Finset.mem_Icc.mp hn.1).1 hab)⟩
  have hjoint : ∀ a b : ℝ, 0 < a → a < 1 → 0 < b → b < 1 →
      Tendsto (fun N : ℕ => (((Finset.Icc 1 N).filter
        (fun n : ℕ => ((n.primeFactors.sup id : ℕ) : ℝ) ≤ (n : ℝ) ^ a ∧
          (((n + 1).primeFactors.sup id : ℕ) : ℝ) ≤ (n : ℝ) ^ b)).card : ℝ) / N)
        atTop (𝓝 (F a * F b)) := by
    intro a b ha ha1 hb hb1
    have := (hind a b ha ha1 hb hb1).add ((hmarg a ha ha1).1.mul (hmarg b hb hb1).2)
    simpa using this
  have hinc : ∀ a b : ℝ, 0 < a → a ≤ b → b < 1 →
      Tendsto (fun N : ℕ => (((Finset.Icc 1 N).filter
        (fun n : ℕ => ((n.primeFactors.sup id : ℕ) : ℝ) ≤ (n : ℝ) ^ a ∧
          (n : ℝ) ^ a < (((n + 1).primeFactors.sup id : ℕ) : ℝ) ∧
          (((n + 1).primeFactors.sup id : ℕ) : ℝ) ≤ (n : ℝ) ^ b)).card : ℝ) / N)
        atTop (𝓝 (F a * (F b - F a))) := by
    intro a b ha hab hb
    have hl := (hjoint a b ha (hab.trans_lt hb) (ha.trans_le hab) hb).sub
      (hjoint a a ha (hab.trans_lt hb) ha (hab.trans_lt hb))
    rw [show F a * F b - F a * F a = F a * (F b - F a) by ring] at hl
    refine hl.congr fun N => dens_sub (fun n _ => ?_) (fun n hn h => ?_) N
    · constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨h1, h3⟩, fun h => (not_le.mpr h2) h.2⟩
      · rintro ⟨⟨h1, h3⟩, h⟩
        exact ⟨h1, lt_of_not_ge fun h2 => h ⟨h1, h2⟩, h3⟩
    · exact ⟨h.1, h.2.trans (hpow n a b hn hab)⟩
  have hdec : ∀ a b : ℝ, 0 < a → a ≤ b → b < 1 →
      Tendsto (fun N : ℕ => (((Finset.Icc 1 N).filter
        (fun n : ℕ => (((n + 1).primeFactors.sup id : ℕ) : ℝ) ≤ (n : ℝ) ^ a ∧
          (n : ℝ) ^ a < ((n.primeFactors.sup id : ℕ) : ℝ) ∧
          ((n.primeFactors.sup id : ℕ) : ℝ) ≤ (n : ℝ) ^ b)).card : ℝ) / N)
        atTop (𝓝 (F a * (F b - F a))) := by
    intro a b ha hab hb
    have hl := (hjoint b a (ha.trans_le hab) hb ha (hab.trans_lt hb)).sub
      (hjoint a a ha (hab.trans_lt hb) ha (hab.trans_lt hb))
    rw [show F b * F a - F a * F a = F a * (F b - F a) by ring] at hl
    refine hl.congr fun N => dens_sub (fun n _ => ?_) (fun n hn h => ?_) N
    · constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨h3, h1⟩, fun h => (not_le.mpr h2) h.1⟩
      · rintro ⟨⟨h3, h1⟩, h⟩
        exact ⟨h1, lt_of_not_ge fun h2 => h ⟨h2, h1⟩, h3⟩
    · exact ⟨h.1.trans (hpow n a b hn hab), h.2⟩
  have hcount : ∀ N : ℕ, ((Finset.Icc 1 N).filter
      (fun n : ℕ => n.primeFactors.sup id < (n + 1).primeFactors.sup id)).card +
      ((Finset.Icc 1 N).filter
      (fun n : ℕ => (n + 1).primeFactors.sup id < n.primeFactors.sup id)).card = N := by
    intro N
    have hf : (Finset.Icc 1 N).filter
        (fun n : ℕ => (n + 1).primeFactors.sup id < n.primeFactors.sup id) =
        (Finset.Icc 1 N).filter
        (fun n : ℕ => ¬ n.primeFactors.sup id < (n + 1).primeFactors.sup id) := by
      apply Finset.filter_congr
      intro n hn
      have := primeFactors_sup_ne_succ n (Finset.mem_Icc.mp hn).1
      constructor <;> intro h <;> omega
    rw [hf, Finset.card_filter_add_card_filter_not, Nat.card_Icc]
    omega
  refine half_of_approx _ (fun N : ℕ => (((Finset.Icc 1 N).filter
      (fun n : ℕ => (n + 1).primeFactors.sup id < n.primeFactors.sup id)).card : ℝ) / N)
    _ ?_ mass_tendsto ?_
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    rw [← add_div, ← Nat.cast_add, hcount N, div_self hN']
  · intro m
    obtain ⟨t, ht, hmon⟩ := exists_grid hcont hF0 hF1 hmono m
    have hord : ∀ i : Fin m, t i.castSucc ≤ t i.succ :=
      fun i => hmon.monotone (by change i.val ≤ i.val + 1; omega)
    have hm := grid_mass (F := F) (fun i => (ht i).2.2)
    refine ⟨fun N => ∑ i : Fin m, (((Finset.Icc 1 N).filter
        (fun n : ℕ => ((n.primeFactors.sup id : ℕ) : ℝ) ≤ (n : ℝ) ^ t i.castSucc ∧
          (n : ℝ) ^ t i.castSucc < (((n + 1).primeFactors.sup id : ℕ) : ℝ) ∧
          (((n + 1).primeFactors.sup id : ℕ) : ℝ) ≤ (n : ℝ) ^ t i.succ)).card : ℝ) / N,
      fun N => ∑ i : Fin m, (((Finset.Icc 1 N).filter
        (fun n : ℕ => (((n + 1).primeFactors.sup id : ℕ) : ℝ) ≤ (n : ℝ) ^ t i.castSucc ∧
          (n : ℝ) ^ t i.castSucc < ((n.primeFactors.sup id : ℕ) : ℝ) ∧
          ((n.primeFactors.sup id : ℕ) : ℝ) ≤ (n : ℝ) ^ t i.succ)).card : ℝ) / N,
      ?_, ?_, fun N => ?_, fun N => ?_⟩
    · rw [← hm]
      exact tendsto_finsetSum _ fun i _ =>
        hinc _ _ (ht _).1 (hord i) (ht _).2.1
    · rw [← hm]
      exact tendsto_finsetSum _ fun i _ =>
        hdec _ _ (ht _).1 (hord i) (ht _).2.1
    · refine dens_sum_le _ (fun n hn i j hi hj => ?_) (fun i n _ h => ?_) N
      · rcases lt_trichotomy i j with hij | hij | hij
        · have he : t i.succ ≤ t j.castSucc :=
            hmon.monotone (by change i.val + 1 ≤ j.val; exact hij)
          exact absurd (hi.2.2.trans (hpow n _ _ hn he)) (not_le.mpr hj.2.1)
        · exact hij
        · have he : t j.succ ≤ t i.castSucc :=
            hmon.monotone (by change j.val + 1 ≤ i.val; exact hij)
          exact absurd (hj.2.2.trans (hpow n _ _ hn he)) (not_le.mpr hi.2.1)
      · exact_mod_cast h.1.trans_lt h.2.1
    · refine dens_sum_le _ (fun n hn i j hi hj => ?_) (fun i n _ h => ?_) N
      · rcases lt_trichotomy i j with hij | hij | hij
        · have he : t i.succ ≤ t j.castSucc :=
            hmon.monotone (by change i.val + 1 ≤ j.val; exact hij)
          exact absurd (hi.2.2.trans (hpow n _ _ hn he)) (not_le.mpr hj.2.1)
        · exact hij
        · have he : t j.succ ≤ t i.castSucc :=
            hmon.monotone (by change j.val + 1 ≤ i.val; exact hij)
          exact absurd (hj.2.2.trans (hpow n _ _ hn he)) (not_le.mpr hi.2.1)
      · exact_mod_cast h.1.trans_lt h.2.1

theorem main : H1 → H2 → type_of% @OMA.S_erdos_371.main := order_half

end OMA.R_erdos_371_R1

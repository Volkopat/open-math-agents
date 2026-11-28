import FormalConjectures.ErdosProblems.«323»

-- Reduction Erdos323.erdos_323.parts.i.R1 of Erdos Problem 323, part (i)
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdos 323 (i) from Hooley's Hypothesis K* and Landau's theorem

The target says that for every `k ≥ 1` and `ε > 0` the number `f k k x` of integers `n ≤ x`
that are sums of `k` nonnegative `k`th powers is `≫ x ^ (1 - ε)`.

* `H1` is Landau's theorem for sums of two squares, word for word the catalogue row
  `Erdos323.erdos_323.variants.k_eq_2` (proved upstream). It gives the case `k = 2`.
* `H2` is Hooley's Hypothesis K* for `k ≥ 3`, in the weak form with `ε`: the mean square of
  `r_{k,k}(l)`, the number of representations of `l` as a sum of `k` positive `k`th powers,
  satisfies `∑_{l ≤ N} r_{k,k}(l) ^ 2 = O(N ^ (1 + ε))`. It is open for every `k ≥ 3`; for
  `k = 3` it is known under the Riemann hypothesis for certain Hasse-Weil L-functions (Hooley,
  Heath-Brown). It is stronger than the target for `k ≥ 3`, so this is an upward reduction:
  the target is the support-size consequence of K*.

`main` proves the case `k = 1` directly, gets `k = 2` from `H1` (with `sqrt (log x) ≤ x ^ ε`),
and for `k ≥ 3` runs the second moment method. With `T` the set of `k`-tuples of positive
integers whose power sum is at most `x`, Cauchy-Schwarz over the fibres of the power sum gives
`|T| ^ 2 ≤ f k k x * ∑_{l ≤ x} r_{k,k}(l) ^ 2`, and the box `[1, m] ^ k` with
`k * m ^ k ≤ x < k * (m + 1) ^ k` gives `k * 2 ^ k * |T| > x`.

Source: erdosproblems.com/323; L. B. Pierce, On discrete fractional integral operators and
mean values of Weyl sums, arXiv:1005.4052, Section 4 (statement and status of Hypothesis K*).
-/

open Filter Asymptotics

namespace OMA.R_Erdos323_erdos_323_parts_i_R1

/-- Landau: the number of `n ≤ x` that are sums of two squares is `~ c x / sqrt (log x)`.
This is the catalogue row `Erdos323.erdos_323.variants.k_eq_2`. -/
def H1 : Prop :=
  ∃ c > 0, (fun (x : ℕ) ↦ (Erdos323.f 2 2 x : ℝ)) ~[atTop]
    (fun (x : ℕ) ↦ c * (x : ℝ) / Real.sqrt (Real.log (x : ℝ)))

/-- Hooley's Hypothesis K* for `k ≥ 3`, in the weak form with `ε`: with `r_{k,k}(l)` the number
of representations of `l` as a sum of `k` positive `k`th powers,
`∑_{l ≤ N} r_{k,k}(l) ^ 2 = O(N ^ (1 + ε))` for every `ε > 0`. -/
def H2 : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε →
    (fun N : ℕ ↦ ((∑ l ∈ Finset.Icc 1 N,
        {v : Fin k → ℕ | (∀ i, 0 < v i) ∧ ∑ i, v i ^ k = l}.ncard ^ 2 : ℕ) : ℝ))
      =O[atTop] (fun N : ℕ ↦ (N : ℝ) ^ (1 + ε))

/-- Cauchy-Schwarz for fibres: `|T| ^ 2` is at most the size of the image times the sum of the
squares of the fibre sizes. -/
lemma card_sq_le_image_mul_sum_sq {α β : Type*} [DecidableEq β]
    (T : Finset α) (g : α → β) :
    T.card ^ 2 ≤ (T.image g).card *
      ∑ b ∈ T.image g, (T.filter (fun a => g a = b)).card ^ 2 := by
  have h1 : T.card = ∑ b ∈ T.image g, (T.filter (fun a => g a = b)).card :=
    Finset.card_eq_sum_card_image g T
  calc T.card ^ 2 = (∑ b ∈ T.image g, (T.filter (fun a => g a = b)).card) ^ 2 := by rw [← h1]
    _ ≤ _ := sq_sum_le_card_mul_sum_sq

/-- A coordinate is at most the sum of the `k`th powers. -/
lemma coord_le_sum_pow (k : ℕ) (hk : 1 ≤ k) (v : Fin k → ℕ) (i : Fin k) :
    v i ≤ ∑ j, v j ^ k :=
  (Nat.le_self_pow (by omega) _).trans
    (Finset.single_le_sum (f := fun j => v j ^ k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))

/-- For `x ≥ k` there are more than `x / (k * 2 ^ k)` tuples of positive integers with sum of
`k`th powers at most `x`. -/
lemma lt_mul_card_tuples (k x : ℕ) (hk : 1 ≤ k) (hkx : k ≤ x) :
    x < k * 2 ^ k * ((Fintype.piFinset fun _ : Fin k => Finset.Icc 1 x).filter
      (fun v => ∑ i, v i ^ k ≤ x)).card := by
  set m := Nat.findGreatest (fun m => k * m ^ k ≤ x) x with hm
  have h1x : k * 1 ^ k ≤ x := by simpa using hkx
  have hspec : k * m ^ k ≤ x :=
    Nat.findGreatest_spec (P := fun m => k * m ^ k ≤ x) (by omega : 1 ≤ x) h1x
  have hm1 : 1 ≤ m :=
    Nat.le_findGreatest (P := fun m => k * m ^ k ≤ x) (by omega : 1 ≤ x) h1x
  have hmx : m ≤ x := Nat.findGreatest_le x
  have hnext : x < k * (m + 1) ^ k := by
    by_contra h
    rw [not_lt] at h
    have h1 : m + 1 ≤ (m + 1) ^ k := Nat.le_self_pow (by omega) _
    have h2 : (m + 1) ^ k ≤ k * (m + 1) ^ k := Nat.le_mul_of_pos_left _ (by omega)
    exact Nat.findGreatest_is_greatest (P := fun m => k * m ^ k ≤ x) (Nat.lt_succ_self m)
      (by omega) h
  have hsub : (Fintype.piFinset fun _ : Fin k => Finset.Icc 1 m) ⊆
      (Fintype.piFinset fun _ : Fin k => Finset.Icc 1 x).filter
        (fun v => ∑ i, v i ^ k ≤ x) := by
    intro v hv
    rw [Fintype.mem_piFinset] at hv
    have hv' : ∀ i, 1 ≤ v i ∧ v i ≤ m := fun i => Finset.mem_Icc.mp (hv i)
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun i => ?_, ?_⟩
    · have := hv' i
      rw [Finset.mem_Icc]
      omega
    · calc ∑ i, v i ^ k ≤ ∑ _i : Fin k, m ^ k :=
            Finset.sum_le_sum fun i _ => Nat.pow_le_pow_left (hv' i).2 k
        _ = k * m ^ k := by simp
        _ ≤ x := hspec
  have hcard := Finset.card_le_card hsub
  rw [Fintype.card_piFinset_const, Nat.card_Icc, Nat.add_sub_cancel] at hcard
  have hpow : (m + 1) ^ k ≤ 2 ^ k * m ^ k := by
    rw [← Nat.mul_pow]
    exact Nat.pow_le_pow_left (by omega) k
  calc x < k * (m + 1) ^ k := hnext
    _ ≤ k * (2 ^ k * m ^ k) := Nat.mul_le_mul_left k hpow
    _ = k * 2 ^ k * m ^ k := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hcard

/-- The image of the positive tuples is counted by the target function. -/
lemma image_card_le_f (k x : ℕ) :
    (((Fintype.piFinset fun _ : Fin k => Finset.Icc 1 x).filter
      (fun v => ∑ i, v i ^ k ≤ x)).image (fun v => ∑ i, v i ^ k)).card ≤ Erdos323.f k k x := by
  unfold Erdos323.f
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard ?_ ((Set.finite_Iic x).subset fun n hn => hn.1)
  intro n hn
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter] at hn
  obtain ⟨v, ⟨-, hv⟩, rfl⟩ := hn
  exact ⟨hv, v, rfl⟩

/-- A fibre of the positive tuples is the representation set of `r_{k,k}`. -/
lemma fibre_card_eq (k x l : ℕ) (hk : 1 ≤ k) (hl : l ≤ x) :
    (((Fintype.piFinset fun _ : Fin k => Finset.Icc 1 x).filter
      (fun v => ∑ i, v i ^ k ≤ x)).filter (fun v => ∑ i, v i ^ k = l)).card =
    {v : Fin k → ℕ | (∀ i, 0 < v i) ∧ ∑ i, v i ^ k = l}.ncard := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext v
  simp only [Finset.coe_filter, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hv, -⟩, he⟩
    exact ⟨fun i => (hv i).1, he⟩
  · rintro ⟨hv, he⟩
    refine ⟨⟨fun i => ⟨hv i, ?_⟩, by omega⟩, he⟩
    have := coord_le_sum_pow k hk v i
    omega

/-- The second moment inequality:
`x ^ 2 ≤ (k * 2 ^ k) ^ 2 * f k k x * ∑_{l ≤ x} r_{k,k}(l) ^ 2` for `x ≥ k`. -/
lemma sq_le_mul_moment (k x : ℕ) (hk : 1 ≤ k) (hkx : k ≤ x) :
    x ^ 2 ≤ (k * 2 ^ k) ^ 2 * (Erdos323.f k k x * ∑ l ∈ Finset.Icc 1 x,
        {v : Fin k → ℕ | (∀ i, 0 < v i) ∧ ∑ i, v i ^ k = l}.ncard ^ 2) := by
  have h1 := lt_mul_card_tuples k x hk hkx
  have h2 := card_sq_le_image_mul_sum_sq
    ((Fintype.piFinset fun _ : Fin k => Finset.Icc 1 x).filter
      (fun v => ∑ i, v i ^ k ≤ x)) (fun v => ∑ i, v i ^ k)
  have h3 := image_card_le_f k x
  have hsub : ((Fintype.piFinset fun _ : Fin k => Finset.Icc 1 x).filter
      (fun v => ∑ i, v i ^ k ≤ x)).image (fun v => ∑ i, v i ^ k) ⊆ Finset.Icc 1 x := by
    intro n hn
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hn
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hv
    have h0 := Finset.mem_Icc.mp (hv.1 ⟨0, by omega⟩)
    have := coord_le_sum_pow k hk v ⟨0, by omega⟩
    rw [Finset.mem_Icc]
    exact ⟨by omega, hv.2⟩
  have h4 : ∑ b ∈ ((Fintype.piFinset fun _ : Fin k => Finset.Icc 1 x).filter
        (fun v => ∑ i, v i ^ k ≤ x)).image (fun v => ∑ i, v i ^ k),
      (((Fintype.piFinset fun _ : Fin k => Finset.Icc 1 x).filter
        (fun v => ∑ i, v i ^ k ≤ x)).filter (fun v => ∑ i, v i ^ k = b)).card ^ 2 ≤
      ∑ l ∈ Finset.Icc 1 x,
        {v : Fin k → ℕ | (∀ i, 0 < v i) ∧ ∑ i, v i ^ k = l}.ncard ^ 2 := by
    refine (Finset.sum_le_sum_of_subset hsub).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [fibre_card_eq k x l hk (Finset.mem_Icc.mp hl).2]
  calc x ^ 2 ≤ (k * 2 ^ k * ((Fintype.piFinset fun _ : Fin k => Finset.Icc 1 x).filter
          (fun v => ∑ i, v i ^ k ≤ x)).card) ^ 2 := Nat.pow_le_pow_left h1.le 2
    _ = (k * 2 ^ k) ^ 2 * ((Fintype.piFinset fun _ : Fin k => Finset.Icc 1 x).filter
          (fun v => ∑ i, v i ^ k ≤ x)).card ^ 2 := by ring
    _ ≤ (k * 2 ^ k) ^ 2 * (_ * _) := Nat.mul_le_mul_left _ h2
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul h3 h4)

/-- The mean square bound gives the lower bound for the number of represented integers. -/
lemma lower_of_moment (k : ℕ) (hk : 1 ≤ k) (ε : ℝ)
    (h : (fun N : ℕ ↦ ((∑ l ∈ Finset.Icc 1 N,
        {v : Fin k → ℕ | (∀ i, 0 < v i) ∧ ∑ i, v i ^ k = l}.ncard ^ 2 : ℕ) : ℝ))
      =O[atTop] (fun N : ℕ ↦ (N : ℝ) ^ (1 + ε))) :
    (fun (x : ℕ) ↦ (x : ℝ) ^ (1 - ε)) =O[atTop] (fun (x : ℕ) ↦ (Erdos323.f k k x : ℝ)) := by
  obtain ⟨C, hC⟩ := h.bound
  refine IsBigO.of_bound (((k : ℝ) * 2 ^ k) ^ 2 * (|C| + 1)) ?_
  filter_upwards [hC, eventually_ge_atTop k] with x hx hxk
  have hx1 : 1 ≤ x := hk.trans hxk
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx1
  have hp1 : (0 : ℝ) < (x : ℝ) ^ (1 + ε) := Real.rpow_pos_of_pos hxpos _
  have hp2 : (0 : ℝ) ≤ (x : ℝ) ^ (1 - ε) := (Real.rpow_pos_of_pos hxpos _).le
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg hp1.le] at hx
  rw [Real.norm_of_nonneg hp2, Real.norm_of_nonneg (Nat.cast_nonneg _)]
  have hsq : ((x : ℝ)) ^ 2 ≤ ((k : ℝ) * 2 ^ k) ^ 2 * ((Erdos323.f k k x : ℝ) *
      ((∑ l ∈ Finset.Icc 1 x,
        {v : Fin k → ℕ | (∀ i, 0 < v i) ∧ ∑ i, v i ^ k = l}.ncard ^ 2 : ℕ) : ℝ)) := by
    exact_mod_cast sq_le_mul_moment k x hk hxk
  have hsplit : (x : ℝ) ^ (1 - ε) * (x : ℝ) ^ (1 + ε) = (x : ℝ) ^ 2 := by
    rw [← Real.rpow_add hxpos, ← Real.rpow_natCast]
    norm_num
  have hS : ((∑ l ∈ Finset.Icc 1 x,
        {v : Fin k → ℕ | (∀ i, 0 < v i) ∧ ∑ i, v i ^ k = l}.ncard ^ 2 : ℕ) : ℝ) ≤
      (|C| + 1) * (x : ℝ) ^ (1 + ε) :=
    hx.trans (mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) hp1.le)
  have hf : (0 : ℝ) ≤ (Erdos323.f k k x : ℝ) := Nat.cast_nonneg _
  have hk2 : (0 : ℝ) ≤ ((k : ℝ) * 2 ^ k) ^ 2 := by positivity
  have hfin : (x : ℝ) ^ (1 - ε) * (x : ℝ) ^ (1 + ε) ≤
      (((k : ℝ) * 2 ^ k) ^ 2 * (|C| + 1) * (Erdos323.f k k x : ℝ)) * (x : ℝ) ^ (1 + ε) := by
    rw [hsplit]
    calc (x : ℝ) ^ 2 ≤ ((k : ℝ) * 2 ^ k) ^ 2 * ((Erdos323.f k k x : ℝ) *
          ((∑ l ∈ Finset.Icc 1 x,
            {v : Fin k → ℕ | (∀ i, 0 < v i) ∧ ∑ i, v i ^ k = l}.ncard ^ 2 : ℕ) : ℝ)) := hsq
      _ ≤ ((k : ℝ) * 2 ^ k) ^ 2 *
          ((Erdos323.f k k x : ℝ) * ((|C| + 1) * (x : ℝ) ^ (1 + ε))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS hf) hk2
      _ = _ := by ring
  exact le_of_mul_le_mul_right hfin hp1

/-- The case `k = 1`: every `n ≤ x` is represented. -/
lemma case_one (ε : ℝ) (hε : 0 < ε) :
    (fun (x : ℕ) ↦ (x : ℝ) ^ (1 - ε)) =O[atTop] (fun (x : ℕ) ↦ (Erdos323.f 1 1 x : ℝ)) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with x hx1
  have hxge : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hf : Erdos323.f 1 1 x = x + 1 := by
    unfold Erdos323.f
    have : {n : ℕ | n ≤ x ∧ ∃ v : Fin 1 → ℕ, n = ∑ i, v i ^ 1} =
        ((Finset.range (x + 1) : Finset ℕ) : Set ℕ) := by
      ext n
      simp only [Set.mem_ofPred_eq, Finset.coe_range, Set.mem_Iio]
      constructor
      · rintro ⟨hn, -⟩
        omega
      · intro hn
        exact ⟨by omega, fun _ => n, by simp⟩
    rw [this, Set.ncard_coe_finset, Finset.card_range]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _),
    Real.norm_of_nonneg (Nat.cast_nonneg _), hf, one_mul]
  have h1 : (x : ℝ) ^ (1 - ε) ≤ (x : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hxge (by linarith)
  rw [Real.rpow_one] at h1
  push_cast
  linarith

/-- The case `k = 2` from Landau's theorem. -/
lemma case_two (h1 : H1) (ε : ℝ) (hε : 0 < ε) :
    (fun (x : ℕ) ↦ (x : ℝ) ^ (1 - ε)) =O[atTop] (fun (x : ℕ) ↦ (Erdos323.f 2 2 x : ℝ)) := by
  obtain ⟨c, hc, heq⟩ := h1
  refine IsBigO.trans ?_ heq.isBigO_symm
  have hlog := (isLittleO_log_rpow_atTop (r := 2 * ε) (by linarith)).bound one_pos
  have hev : ∀ᶠ t : ℝ in atTop, ‖t ^ (1 - ε)‖ ≤
      (1 / c) * ‖c * t / Real.sqrt (Real.log t)‖ := by
    filter_upwards [hlog, eventually_ge_atTop 2] with t ht ht2
    have htpos : (0 : ℝ) < t := by linarith
    have hlogpos : 0 < Real.log t := Real.log_pos (by linarith)
    have hsqrtpos : 0 < Real.sqrt (Real.log t) := Real.sqrt_pos.mpr hlogpos
    rw [Real.norm_of_nonneg hlogpos.le, one_mul,
      Real.norm_of_nonneg (Real.rpow_nonneg htpos.le _)] at ht
    have hs : Real.sqrt (Real.log t) ≤ t ^ ε := by
      have h2 : Real.sqrt (t ^ (2 * ε)) = t ^ ε := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul htpos.le]
        congr 1
        ring
      rw [← h2]
      exact Real.sqrt_le_sqrt ht
    have hmul : t ^ (1 - ε) * Real.sqrt (Real.log t) ≤ t := by
      calc t ^ (1 - ε) * Real.sqrt (Real.log t) ≤ t ^ (1 - ε) * t ^ ε :=
            mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg htpos.le _)
        _ = t := by
            rw [← Real.rpow_add htpos]
            norm_num
    have hquot : (0 : ℝ) ≤ c * t / Real.sqrt (Real.log t) := by positivity
    rw [Real.norm_of_nonneg (Real.rpow_nonneg htpos.le _), Real.norm_of_nonneg hquot]
    have hrw : 1 / c * (c * t / Real.sqrt (Real.log t)) = t / Real.sqrt (Real.log t) := by
      field_simp
    rw [hrw, le_div_iff₀ hsqrtpos]
    exact hmul
  exact IsBigO.of_bound (1 / c) (tendsto_natCast_atTop_atTop.eventually hev)

theorem main : H1 → H2 → type_of% @Erdos323.erdos_323.parts.i := by
  intro h1 h2 k hk ε hε
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · have hk12 : k = 1 ∨ k = 2 := by omega
    rcases hk12 with rfl | rfl
    · exact case_one ε hε
    · exact case_two h1 ε hε
  · exact lower_of_moment k hk ε (h2 k hk3 ε hε)

end OMA.R_Erdos323_erdos_323_parts_i_R1

import FormalConjectures.OEIS.«120424»

/-!
# Half-Fibonacci density from spacing and excess of long gaps

The gaps between even transformed values have length at least three.
Separate the frequency of gaps of length at least four from their mean excess over three.
-/

-- Credit: @Pockenauer-AI

open Filter Finset
open scoped Topology

namespace OMA.R_OeisA120424_conjecture1_R2

open OeisA120424 (a f)

private theorem b_step (n : ℕ) : f (a (n + 2)) = f (f (a n) + f (a (n + 1))) := by
  rw [a, Nat.add_comm]

private theorem no_two_even (n : ℕ) : ¬ (f (a n) % 2 = 0 ∧ f (a (n + 1)) % 2 = 0) := by
  induction n with
  | zero => decide
  | succ n ih =>
    intro h
    change f (a (n + 1)) % 2 = 0 ∧ f (a (n + 2)) % 2 = 0 at h
    change ¬ (f (a n) % 2 = 0 ∧ f (a (n + 1)) % 2 = 0) at ih
    rw [b_step] at h
    have hodd : (f (a n) + f (a (n + 1))) % 2 ≠ 0 := by omega
    have heq : f (f (a n) + f (a (n + 1))) = f (a n) + f (a (n + 1)) := if_neg hodd
    rw [heq] at h
    exact hodd h.2

private theorem positive_b (n : ℕ) : 0 < f (a n) := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n h₀ h₁ =>
    rw [b_step]
    suffices ∀ x : ℕ, 2 ≤ x → 0 < f x from this _ (by omega)
    intro x hx
    unfold f
    split_ifs <;> omega

private theorem consecutive_ne (n : ℕ) : f (a n) ≠ f (a (n + 1)) := by
  induction n with
  | zero => decide
  | succ n ih =>
    change f (a (n + 1)) ≠ f (a (n + 2))
    rw [b_step]
    suffices ∀ x y : ℕ, 0 < x → x ≠ y → y ≠ f (x + y) from this _ _ (positive_b n) ih
    intro x y hx hxy
    unfold f
    split_ifs <;> omega

private theorem infinitely_many_even : (Set.ofPred (fun k => f (a k) % 2 = 0)).Infinite := by
  refine Set.infinite_of_forall_exists_gt fun N => ?_
  by_contra! h
  have odd_above (c : ℕ) (hc : N < c) : f (a c) % 2 ≠ 0 := fun he => hc.not_ge (h c he)
  let difference := fun j : ℕ => (f (a (N + 1 + j + 1)) : ℤ) - f (a (N + 1 + j))
  have decrease (j : ℕ) : (difference (j + 1)).natAbs + 1 ≤ (difference j).natAbs := by
    let n := N + 1 + j
    have h₀ : f (a n) % 2 ≠ 0 := odd_above n (by dsimp [n]; omega)
    have h₁ : f (a (n + 1)) % 2 ≠ 0 := odd_above (n + 1) (by dsimp [n]; omega)
    have hsum : (f (a n) + f (a (n + 1))) % 2 = 0 := by omega
    have hnext : f (a (n + 2)) = (f (a n) + f (a (n + 1))) / 2 := by
      rw [b_step]
      exact if_pos hsum
    have hrel : difference j = (-2) * difference (j + 1) := by
      change (f (a (n + 1)) : ℤ) - f (a n) = (-2) * ((f (a (n + 2)) : ℤ) - f (a (n + 1)))
      omega
    have hne : 0 < (difference (j + 1)).natAbs := by
      have hne' := consecutive_ne (n + 1)
      change 0 < ((f (a (n + 2)) : ℤ) - f (a (n + 1))).natAbs
      exact Int.natAbs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hne'.symm))
    rw [hrel, Int.natAbs_mul]
    norm_num
    omega
  have bound (j : ℕ) : j + (difference j).natAbs ≤ (difference 0).natAbs := by
    induction j with
    | zero => simp
    | succ j ih => have hd := decrease j; omega
  have contradiction := bound ((difference 0).natAbs + 1)
  omega

private theorem gap_ge_three (j : ℕ) :
    let position := Nat.nth (fun n => f (a n) % 2 = 0)
    3 ≤ (position (j + 1) : ℝ) - position j := by
  let evenPosition := fun n => f (a n) % 2 = 0
  let position := Nat.nth evenPosition
  change (3 : ℝ) ≤ (position (j + 1) : ℝ) - position j
  let n := position j
  have he : f (a n) % 2 = 0 := Nat.nth_mem_of_infinite infinitely_many_even j
  have hn : f (a (n + 1)) % 2 ≠ 0 := fun h => no_two_even n ⟨he, h⟩
  have hn' : f (a (n + 2)) % 2 ≠ 0 := by
    have hodd : (f (a n) + f (a (n + 1))) % 2 ≠ 0 := by omega
    rw [b_step, show f (f (a n) + f (a (n + 1))) = f (a n) + f (a (n + 1)) from if_neg hodd]
    exact hodd
  have hlt : n < position (j + 1) := Nat.nth_strictMono infinitely_many_even (Nat.lt_succ_self j)
  have hne₁ : position (j + 1) ≠ n + 1 := fun h => hn (h ▸
    (Nat.nth_mem_of_infinite infinitely_many_even (j + 1) : evenPosition (position (j + 1))))
  have hne₂ : position (j + 1) ≠ n + 2 := fun h => hn' (h ▸
    (Nat.nth_mem_of_infinite infinitely_many_even (j + 1) : evenPosition (position (j + 1))))
  apply (le_sub_iff_add_le).2
  exact_mod_cast (show 3 + position j ≤ position (j + 1) by change 3 + n ≤ _; omega)

private theorem bit_step (n : ℕ) :
    (if a (n + 2) % 2 = 0 then 1 else 0) +
      (if f (a n) % 2 = 0 then 1 else 0) + (if f (a (n + 1)) % 2 = 0 then 1 else 0) = (1 : ℕ) := by
  have h := no_two_even n
  change ¬ (f (a n) % 2 = 0 ∧ f (a (n + 1)) % 2 = 0) at h
  have ha : a (n + 2) = f (a n) + f (a (n + 1)) := by rw [a, Nat.add_comm]
  rw [ha]
  split_ifs <;> omega

private theorem count_identity (n : ℕ) :
    Nat.count (fun k => a k % 2 = 0) (n + 2) + 2 * Nat.count (fun k => f (a k) % 2 = 0) n +
      (if f (a n) % 2 = 0 then 1 else 0) = n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 by omega, Nat.count_succ (fun k => a k % 2 = 0) (n + 2),
      Nat.count_succ (fun k => f (a k) % 2 = 0) n]
    have h := bit_step n
    change Nat.count (fun k => a k % 2 = 0) (n + 2) +
      (if a (n + 2) % 2 = 0 then 1 else 0) +
      2 * (Nat.count (fun k => f (a k) % 2 = 0) n + (if f (a n) % 2 = 0 then 1 else 0)) +
      (if f (a (n + 1)) % 2 = 0 then 1 else 0) = n + 1
    omega

private theorem count_bounds (n : ℕ) :
    Nat.count (fun k => a k % 2 = 0) n + 2 * Nat.count (fun k => f (a k) % 2 = 0) n ≤ n ∧
      n ≤ Nat.count (fun k => a k % 2 = 0) n + 2 * Nat.count (fun k => f (a k) % 2 = 0) n + 2 := by
  cases n with
  | zero => decide
  | succ n =>
    cases n with
    | zero => decide
    | succ n =>
      change Nat.count (fun k => a k % 2 = 0) (n + 2) + 2 * Nat.count (fun k => f (a k) % 2 = 0) (n + 2) ≤ n + 2 ∧
        n + 2 ≤ Nat.count (fun k => a k % 2 = 0) (n + 2) + 2 * Nat.count (fun k => f (a k) % 2 = 0) (n + 2) + 2
      rw [Nat.count_succ (fun k => f (a k) % 2 = 0) (n + 1), Nat.count_succ (fun k => f (a k) % 2 = 0) n]
      have hi := count_identity n
      have hp := no_two_even n
      split_ifs at * <;> omega

private theorem count_density_of_nth (p : ℕ → Prop) [DecidablePred p]
    (hp : (Set.ofPred p).Infinite) {mean : ℝ} (hm : mean ≠ 0)
    (hnth : Tendsto (fun m : ℕ => (Nat.nth p m : ℝ) / m) atTop (𝓝 mean)) :
    Tendsto (fun n : ℕ => (Nat.count p n : ℝ) / n) atTop (𝓝 mean⁻¹) := by
  have grow : Tendsto (Nat.count p) atTop atTop := by
    refine tendsto_atTop.2 fun j => eventually_atTop.2 ⟨Nat.nth p j, fun n hn => ?_⟩
    simpa only [Nat.count_nth_of_infinite hp] using Nat.count_monotone p hn
  have growPrev : Tendsto (fun n => Nat.count p n - 1) atTop atTop := by
    refine tendsto_atTop.2 fun j => ((tendsto_atTop.1 grow) (j + 1)).mono fun n hn => ?_
    omega
  have shift : Tendsto (fun m : ℕ => (Nat.nth p m : ℝ) / ((m : ℝ) + 1)) atTop (𝓝 mean) := by
    have hv : Tendsto (fun m : ℕ => 1 - 1 / ((m : ℝ) + 1)) atTop (𝓝 (1 : ℝ)) := by
      simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hmul := hnth.mul hv
    rw [mul_one] at hmul
    refine hmul.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    have hm'' : (m : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  have squeezed : Tendsto (fun n : ℕ => (n : ℝ) / Nat.count p n) atTop (𝓝 mean) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (shift.comp growPrev) (hnth.comp grow) ?_ ?_
    · filter_upwards [(tendsto_atTop.1 grow) 1] with n hn
      have hpos : (0 : ℝ) < Nat.count p n := by exact_mod_cast hn
      have hcast : ((Nat.count p n - 1 : ℕ) : ℝ) + 1 = Nat.count p n := by
        rw [Nat.cast_sub hn, Nat.cast_one, sub_add_cancel]
      simp only [Function.comp_apply, hcast]
      have hlt : Nat.nth p (Nat.count p n - 1) < n := Nat.nth_lt_of_lt_count (by omega)
      exact div_le_div_of_nonneg_right (by exact_mod_cast hlt.le) hpos.le
    · exact Eventually.of_forall fun n =>
        div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_nth_count hp n) (by positivity)
  simpa only [inv_div, one_div] using squeezed.inv₀ hm


/-- The mean spacing between indices of gaps of length at least four is two. -/
def H1 : Prop :=
  let position := Nat.nth (fun n => f (a n) % 2 = 0)
  let long := fun j => 4 ≤ position (j + 1) - position j
  Tendsto (fun m : ℕ => (Nat.nth long m : ℝ) / m) atTop (𝓝 (2 : ℝ))

/-- The mean amount beyond length three, among the gaps of length at least four, is two. -/
def H2 : Prop :=
  let position := Nat.nth (fun n => f (a n) % 2 = 0)
  let long := fun j => 4 ≤ position (j + 1) - position j
  Tendsto (fun m : ℕ => (∑ j ∈ range m,
    ((position (Nat.nth long j + 1) : ℝ) - position (Nat.nth long j) - 3)) / m)
    atTop (𝓝 (2 : ℝ))

private theorem sparse_sum (p : ℕ → Prop) [DecidablePred p] (u : ℕ → ℝ)
    (hzero : ∀ j, ¬ p j → u j = 0) (n : ℕ) :
    (∑ j ∈ range n, u j) = ∑ k ∈ range (Nat.count p n), u (Nat.nth p k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, Nat.count_succ p]
    by_cases hp : p n
    · rw [if_pos hp, sum_range_succ, Nat.nth_count hp]
    · rw [if_neg hp, Nat.add_zero, hzero n hp, add_zero]

theorem main : H1 → H2 → type_of% @OeisA120424.conjecture1 := by
  intro hspacing hexcess
  let position := Nat.nth (fun n => f (a n) % 2 = 0)
  let long := fun j => 4 ≤ position (j + 1) - position j
  let excess := fun j => (position (j + 1) : ℝ) - position j - 3
  change Tendsto (fun m : ℕ => (Nat.nth long m : ℝ) / m) atTop (𝓝 (2 : ℝ)) at hspacing
  change Tendsto (fun m : ℕ => (∑ j ∈ range m, excess (Nat.nth long j)) / m)
    atTop (𝓝 (2 : ℝ)) at hexcess
  have hinfinite : (Set.ofPred long).Infinite := by
    intro hf
    have hz : Tendsto (fun m : ℕ => (Nat.nth long m : ℝ) / m) atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop hf.toFinset.card] with m hm
      rw [Nat.nth_of_card_le hf hm, Nat.cast_zero, zero_div]
    exact (by norm_num : (2 : ℝ) ≠ 0) (tendsto_nhds_unique hspacing hz)
  have hl := count_density_of_nth long hinfinite (by norm_num : (2 : ℝ) ≠ 0) hspacing
  have hgrow : Tendsto (Nat.count long) atTop atTop := by
    refine tendsto_atTop.2 fun k => eventually_atTop.2 ⟨Nat.nth long k, fun m hm => ?_⟩
    simpa only [Nat.count_nth_of_infinite hinfinite] using Nat.count_monotone long hm
  have hzero (j : ℕ) (h : ¬ long j) : excess j = 0 := by
    have hge := gap_ge_three j
    change (3 : ℝ) ≤ (position (j + 1) : ℝ) - position j at hge
    change ¬ 4 ≤ position (j + 1) - position j at h
    have hle : position (j + 1) ≤ position j + 3 := by omega
    have hle' : (position (j + 1) : ℝ) ≤ position j + 3 := by exact_mod_cast hle
    change (position (j + 1) : ℝ) - position j - 3 = 0
    linarith
  have htotal : Tendsto (fun n : ℕ => (∑ j ∈ range n, excess j) / n) atTop (𝓝 (1 : ℝ)) := by
    have h := (hexcess.comp hgrow).mul hl
    norm_num only [show (2 : ℝ) * 2⁻¹ = 1 by norm_num] at h
    refine h.congr' ?_
    filter_upwards [(tendsto_atTop.1 hgrow) 1] with n hn
    have hn' : (Nat.count long n : ℝ) ≠ 0 := by exact_mod_cast (show Nat.count long n ≠ 0 by omega)
    simp only [Function.comp_apply, sparse_sum long excess hzero n]
    field_simp
  have htel (m : ℕ) : (∑ j ∈ range m, excess j) =
      (position m : ℝ) - position 0 - 3 * m := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ, ih]
      dsimp [excess]
      push_cast
      ring
  have hnth : Tendsto (fun m : ℕ => (position m : ℝ) / m) atTop (𝓝 (4 : ℝ)) := by
    have hsmall : Tendsto (fun m : ℕ => (position 0 : ℝ) / m) atTop (𝓝 0) :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).const_div_atTop _
    have h := (htotal.add hsmall).add (tendsto_const_nhds (x := (3 : ℝ)))
    norm_num only [add_zero, show (1 : ℝ) + 3 = 4 by norm_num] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    rw [htel]
    field_simp
    ring
  have hb : Tendsto (fun n : ℕ => (Nat.count (fun k => f (a k) % 2 = 0) n : ℝ) / n)
      atTop (𝓝 (1 / 4 : ℝ)) := by
    simpa only [inv_eq_one_div] using
      count_density_of_nth (fun k => f (a k) % 2 = 0) infinitely_many_even
        (by norm_num : (4 : ℝ) ≠ 0) hnth
  let p : ℕ → Prop := fun k => a k % 2 = 0
  have hsum : Tendsto (fun n : ℕ => ((Nat.count p n : ℝ) + 2 * (Nat.count (fun k => f (a k) % 2 = 0) n : ℝ)) / n)
      atTop (𝓝 (1 : ℝ)) := by
    have hg : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hsmall : Tendsto (fun n : ℕ => (2 : ℝ) / n) atTop (𝓝 0) := hg.const_div_atTop 2
    have hnear : Tendsto (fun n : ℕ => 1 - 2 / (n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
      simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hsmall
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hnear tendsto_const_nhds ?_ ?_
    · filter_upwards [hg.eventually_gt_atTop 0] with n hn
      have h : (n : ℝ) ≤ (Nat.count p n : ℝ) + 2 * (Nat.count (fun k => f (a k) % 2 = 0) n : ℝ) + 2 := by
        exact_mod_cast (count_bounds n).2
      apply (le_div_iff₀ hn).2
      calc
        (1 - 2 / (n : ℝ)) * (n : ℝ) = (n : ℝ) - 2 := by field_simp
        _ ≤ _ := by linarith
    · filter_upwards [hg.eventually_gt_atTop 0] with n hn
      exact (div_le_one hn).2 (by exact_mod_cast (count_bounds n).1)
  have hdouble : Tendsto (fun n : ℕ => 2 * ((Nat.count (fun k => f (a k) % 2 = 0) n : ℝ) / n)) atTop (𝓝 (2 * (1 / 4 : ℝ))) :=
    hb.const_mul 2
  have h := hsum.sub hdouble
  have heq (n : ℕ) :
      ((Nat.count p n : ℝ) + 2 * (Nat.count (fun k => f (a k) % 2 = 0) n : ℝ)) / (n : ℝ) -
        2 * ((Nat.count (fun k => f (a k) % 2 = 0) n : ℝ) / (n : ℝ)) = (Nat.count p n : ℝ) / (n : ℝ) := by ring
  have hfinal : Tendsto (fun n : ℕ => (Nat.count p n : ℝ) / n) atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa only [heq, show 1 - 2 * (1 / 4) = (1 / 2 : ℝ) by norm_num] using h
  simpa only [Nat.count_eq_card_filter_range, p] using hfinal

end OMA.R_OeisA120424_conjecture1_R2

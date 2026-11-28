import OMAReductions.R_Erdos241_erdos_241_variants_generalization_R1
import Mathlib

-- Reduction Erdos241.erdos_241.variants.generalization.R1.H2.R1 of step Erdos241.erdos_241.variants.generalization.R1.H2
-- Credit: @rickmanelius

/-!
# Bose-Chowla upper bound: the case `r = 2` proved, `r = 3` and `r ≥ 4` left open

The step asks, for every `r ≥ 2`, that `f N r ≤ (1 + o(1)) N ^ (1 / r)`, where `f N r` is the
largest size of a set `A ⊆ [1, N]` whose `r`-fold sums are distinct apart from rearrangements.

Proved below, with no hypothesis (`case_two`): the case `r = 2`, the upper bound of Erdős and
Turán for Sidon sets. For `A ⊆ [1, N]` with `k` elements and a window length `u ≥ 1`, let `w m`
count the elements of `A` in `(m - u, m]`, for `m < N + u`. Then `∑ w m = k u`, and the pairs of
distinct elements in a common window inject into pairs of distinct offsets in `[0, u)` through
`(m, a, b) ↦ (m - a, m - b)`, because a difference of two elements of `A` determines them. So
`∑ w m ^ 2 ≤ k u + u (u - 1)`, and Cauchy-Schwarz gives `k ^ 2 u ≤ (N + u) (k + u)`
(`window_bound`). With `u = ⌊N / M⌋` and `M > 1 / c` this gives `f N 2 ≤ (1 + c) √N` for all
large `N` (`f_two_le`). This is the upper half of the merged problem
`Erdos241.erdos_241.variants.r_eq_2`, proved again here because proof files cannot be imported.

The remaining cases are left as two hypotheses, each the step restricted to a range of `r`:
* `H1`: the case `r = 3`, the open half of Erdős Problem 241 itself (the lower bound
  `(1 + o(1)) N ^ (1 / 3) ≤ f N 3` is the Bose-Chowla construction).
* `H2`: the cases `r ≥ 4`.
-/

namespace OMA.R_Erdos241_erdos_241_variants_generalization_R1_H2_R1

open Filter Asymptotics Finset

/-- The upper bound for `r = 3`: `f N 3 ≤ (1 + o(1)) N ^ (1 / 3)`. -/
def H1 : Prop := ∃ ε : ℕ → ℝ, ε =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
  ∀ᶠ N in atTop, (Erdos241.f N 3 : ℝ) ≤ (1 + ε N) * (N : ℝ) ^ ((1 : ℝ) / 3)

/-- The upper bound for every `r ≥ 4`: `f N r ≤ (1 + o(1)) N ^ (1 / r)`. -/
def H2 : Prop := ∀ r : ℕ, 4 ≤ r → ∃ ε : ℕ → ℝ, ε =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
  ∀ᶠ N in atTop, (Erdos241.f N r : ℝ) ≤ (1 + ε N) * (N : ℝ) ^ ((1 : ℝ) / r)

/-- Two-fold sums determine the pair: the defining property of `f N 2`, in additive form. -/
lemma sidon_of_pairs {A : Finset ℕ}
    (hA : ∀ m₁ m₂ : Multiset ℕ, m₁.card = 2 → m₂.card = 2 → (∀ x ∈ m₁, x ∈ A) →
      (∀ x ∈ m₂, x ∈ A) → m₁.sum = m₂.sum → m₁ = m₂)
    {x y z w : ℕ} (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A) (hw : w ∈ A) (h : x + y = z + w) :
    (x = z ∧ y = w) ∨ (x = w ∧ y = z) := by
  have hm := hA {x, y} {z, w} (by simp) (by simp)
    (by intro t ht; simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
      Multiset.mem_singleton] at ht; rcases ht with rfl | rfl <;> assumption)
    (by intro t ht; simp only [Multiset.insert_eq_cons, Multiset.mem_cons,
      Multiset.mem_singleton] at ht; rcases ht with rfl | rfl <;> assumption)
    (by simpa using h)
  have hxm : x ∈ ({z, w} : Multiset ℕ) := by rw [← hm]; simp
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hxm
  rcases hxm with rfl | rfl
  · left; exact ⟨rfl, by omega⟩
  · right; exact ⟨rfl, by omega⟩

/-- Erdős-Turán counting with windows of length `u`: a set `A ⊆ [1, N]` with `k` elements whose
two-fold sums determine the pair satisfies `k ^ 2 * u ≤ (N + u) * (k + u)`. -/
lemma window_bound (N u : ℕ) (hu : 1 ≤ u) (A : Finset ℕ) (hAN : A ⊆ Icc 1 N)
    (hS : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, ∀ w ∈ A, x + y = z + w →
      (x = z ∧ y = w) ∨ (x = w ∧ y = z)) :
    A.card ^ 2 * u ≤ (N + u) * (A.card + u) := by
  set S : ℕ → Finset ℕ := fun m => A.filter (fun a => a ≤ m ∧ m < a + u) with hSdef
  -- each element lies in exactly `u` windows
  have hsum : ∑ m ∈ range (N + u), (S m).card = A.card * u := by
    simp only [hSdef, card_filter]
    rw [Finset.sum_comm]
    have hin : ∀ a ∈ A, ∑ m ∈ range (N + u), (if a ≤ m ∧ m < a + u then 1 else 0) = u := by
      intro a ha
      have haN : a ≤ N := (mem_Icc.mp (hAN ha)).2
      rw [← card_filter]
      have : (range (N + u)).filter (fun m => a ≤ m ∧ m < a + u) = Ico a (a + u) := by
        ext m
        simp only [mem_filter, mem_range, mem_Ico]
        constructor
        · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨by omega, h1, h2⟩
      rw [this, Nat.card_Ico]
      omega
    rw [Finset.sum_congr rfl hin, sum_const, smul_eq_mul]
  -- pairs of distinct elements in a common window inject into distinct pairs of offsets
  have hoff : ∑ m ∈ range (N + u), (S m).offDiag.card ≤ u * u - u := by
    rw [← card_sigma]
    have hcard : ((range u).offDiag).card = u * u - u := by
      rw [offDiag_card, card_range]
    rw [← hcard]
    refine card_le_card_of_injOn (fun p => (p.1 - p.2.1, p.1 - p.2.2)) ?_ ?_
    · rintro ⟨m, a, b⟩ hp
      simp only [Finset.mem_coe, mem_sigma, mem_offDiag, hSdef, mem_filter] at hp
      obtain ⟨-, ⟨-, ha1, ha2⟩, ⟨-, hb1, hb2⟩, hab⟩ := hp
      simp only [Finset.mem_coe, mem_offDiag, mem_range]
      exact ⟨by omega, by omega, by omega⟩
    · rintro ⟨m, a, b⟩ hp ⟨m', a', b'⟩ hp' heq
      simp only [Finset.mem_coe, mem_sigma, mem_offDiag, hSdef, mem_filter] at hp hp'
      obtain ⟨-, ⟨haA, ha1, ha2⟩, ⟨hbA, hb1, hb2⟩, hab⟩ := hp
      obtain ⟨-, ⟨haA', ha1', ha2'⟩, ⟨hbA', hb1', hb2'⟩, hab'⟩ := hp'
      simp only [Prod.mk.injEq] at heq
      obtain ⟨e1, e2⟩ := heq
      have key : a' + b = a + b' := by omega
      rcases hS a' haA' b hbA a haA b' hbA' key with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1; subst h2
        have : m = m' := by omega
        subst this
        rfl
      · exact absurd h2.symm hab
  have hsq : ∑ m ∈ range (N + u), (S m).card ^ 2 ≤ A.card * u + (u * u - u) := by
    have hsplit : ∀ m, (S m).card ^ 2 = (S m).card + (S m).offDiag.card := by
      intro m
      rw [offDiag_card]
      have : (S m).card ≤ (S m).card * (S m).card := Nat.le_mul_self _
      rw [sq]
      omega
    rw [Finset.sum_congr rfl (fun m _ => hsplit m), sum_add_distrib, hsum]
    omega
  have hcs := sq_sum_le_card_mul_sum_sq (s := range (N + u)) (f := fun m => (S m).card)
  rw [hsum, card_range] at hcs
  have h1 : (A.card * u) ^ 2 ≤ (N + u) * (A.card * u + (u * u - u)) :=
    hcs.trans (Nat.mul_le_mul_left _ hsq)
  have h3 : u * (A.card ^ 2 * u) ≤ u * ((N + u) * (A.card + u)) := by
    calc u * (A.card ^ 2 * u) = (A.card * u) ^ 2 := by ring
      _ ≤ (N + u) * (A.card * u + (u * u - u)) := h1
      _ ≤ (N + u) * (A.card * u + u * u) := by gcongr; omega
      _ = u * ((N + u) * (A.card + u)) := by ring
  exact Nat.le_of_mul_le_mul_left h3 (by omega)

/-- The window bound for `f N 2` itself (the maximum is attained by an admissible set). -/
lemma f_two_window (N u : ℕ) (hu : 1 ≤ u) :
    Erdos241.f N 2 ^ 2 * u ≤ (N + u) * (Erdos241.f N 2 + u) := by
  classical
  unfold Erdos241.f
  set C := (Icc 1 N).powerset.filter (fun A : Finset ℕ ↦
    ∀ m₁ m₂ : Multiset ℕ, m₁.card = 2 → m₂.card = 2 → (∀ x ∈ m₁, x ∈ A) →
      (∀ x ∈ m₂, x ∈ A) → m₁.sum = m₂.sum → m₁ = m₂) with hC
  have hne : C.Nonempty := by
    refine ⟨∅, ?_⟩
    rw [hC, mem_filter, mem_powerset]
    refine ⟨empty_subset _, ?_⟩
    intro m₁ m₂ h₁ _ hm₁ _ _
    obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < Multiset.card m₁)
    exact absurd (hm₁ x hx) (Finset.notMem_empty x)
  obtain ⟨A, hA, hsup⟩ := exists_mem_eq_sup C hne card
  rw [hsup]
  rw [hC, mem_filter, mem_powerset] at hA
  obtain ⟨hAN, hAS⟩ := hA
  exact window_bound N u hu A hAN fun x hx y hy z hz w hw h => sidon_of_pairs hAS hx hy hz hw h

/-- For every `c > 0`, eventually `f N 2 ≤ (1 + c) √N`. -/
lemma f_two_le (c : ℝ) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, (Erdos241.f N 2 : ℝ) ≤ (1 + c) * Real.sqrt N := by
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / c)
  have hcM : 1 < c * M := by
    have := (div_lt_iff₀' hc).mp hM
    linarith
  have hM1 : 1 ≤ M := by
    by_contra h
    have h0 : M = 0 := by omega
    rw [h0] at hcM
    simp at hcM
    linarith
  obtain ⟨N0, hN0⟩ := exists_nat_gt ((2 * (2 * M + 1) / c) ^ 2)
  filter_upwards [eventually_ge_atTop (max (2 * M) N0)] with N hN
  have hN2M : 2 * M ≤ N := le_trans (le_max_left _ _) hN
  have hNN0 : N0 ≤ N := le_trans (le_max_right _ _) hN
  set k := Erdos241.f N 2 with hk
  set u := N / M with hu
  have hu1 : 1 ≤ u := by
    rw [hu, Nat.le_div_iff_mul_le (by omega)]
    omega
  have hwin := f_two_window N u hu1
  rw [← hk] at hwin
  -- integer facts about `u = N / M`
  have hMu : M * u ≤ N := Nat.mul_div_le N M
  have hN2 : N ≤ 2 * M * u := by
    have h1 := Nat.lt_mul_div_succ N (show 0 < M by omega)
    nlinarith
  -- real versions
  have hwinR : (k : ℝ) ^ 2 * u ≤ ((N : ℝ) + u) * ((k : ℝ) + u) := by exact_mod_cast hwin
  have hMuR : (M : ℝ) * u ≤ N := by exact_mod_cast hMu
  have hN2R : (N : ℝ) ≤ 2 * M * u := by exact_mod_cast hN2
  have hu1R : (1 : ℝ) ≤ u := by exact_mod_cast hu1
  have hNpos : (0 : ℝ) < N := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    linarith
  set x := Real.sqrt N with hx
  have hxx : x * x = N := Real.mul_self_sqrt (by positivity)
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hxbig : 2 * (2 * M + 1) / c ≤ x := by
    rw [hx]
    apply Real.le_sqrt_of_sq_le
    have : ((N0 : ℕ) : ℝ) ≤ N := by exact_mod_cast hNN0
    linarith
  have h2M : (2 * M + 1 : ℝ) ≤ c / 2 * x := by
    have := (div_le_iff₀ hc).mp hxbig
    linarith
  by_contra hcon
  rw [not_le] at hcon
  -- `k > (1 + c) x`
  have hk0 : (0 : ℝ) ≤ k := by positivity
  -- `u < c N`
  have huc : (u : ℝ) < c * N := by
    have : (u : ℝ) * 1 < u * (c * M) := mul_lt_mul_of_pos_left hcM (by linarith)
    nlinarith
  -- `k ^ 2 < (2 M + 1) k + (1 + c) N`
  have hquad : (k : ℝ) ^ 2 < (2 * M + 1) * k + (1 + c) * N := by
    have e1 : (N : ℝ) * k ≤ 2 * M * u * k := mul_le_mul_of_nonneg_right hN2R hk0
    have e2 : (u : ℝ) * u < c * N * u := mul_lt_mul_of_pos_right huc (by linarith)
    have e3 : (k : ℝ) ^ 2 * u < ((2 * M + 1) * k + (1 + c) * N) * u := by nlinarith
    exact lt_of_mul_lt_mul_right e3 (by linarith)
  have e4 : (2 * M + 1 : ℝ) * k ≤ c / 2 * x * k := mul_le_mul_of_nonneg_right h2M hk0
  have e5 : (1 + c) * x * ((1 + c / 2) * x) < k * (k - c / 2 * x) :=
    mul_lt_mul'' hcon (by linarith) (by positivity) (by positivity)
  have e6 : (1 + c) * (N : ℝ) ≤ (1 + c) * x * ((1 + c / 2) * x) := by
    rw [← hxx]
    nlinarith [mul_nonneg hx0 hx0, hc.le]
  nlinarith [hquad, e4, e5, e6]

/-- The case `r = 2` of the upper bound (Erdős and Turán). -/
theorem case_two : ∃ ε : ℕ → ℝ, ε =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ᶠ N in atTop, (Erdos241.f N 2 : ℝ) ≤ (1 + ε N) * (N : ℝ) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) := by
  refine ⟨fun N => max 0 ((Erdos241.f N 2 : ℝ) / Real.sqrt N - 1), ?_, ?_⟩
  · refine IsLittleO.of_bound fun c hc => ?_
    filter_upwards [f_two_le c hc, eventually_ge_atTop 1] with N hN hN1
    have hpos : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN1)
    rw [norm_one, mul_one, Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    refine max_le hc.le ?_
    rw [sub_le_iff_le_add, div_le_iff₀ hpos]
    linarith
  · filter_upwards [eventually_ge_atTop 1] with N hN1
    have hpos : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN1)
    have hrw : (N : ℝ) ^ ((1 : ℝ) / ((2 : ℕ) : ℝ)) = Real.sqrt N := by
      rw [Real.sqrt_eq_rpow]
      norm_num
    rw [hrw]
    have h1 : (Erdos241.f N 2 : ℝ) / Real.sqrt N - 1 ≤
        max 0 ((Erdos241.f N 2 : ℝ) / Real.sqrt N - 1) := le_max_right _ _
    calc (Erdos241.f N 2 : ℝ) = (Erdos241.f N 2 : ℝ) / Real.sqrt N * Real.sqrt N :=
          (div_mul_cancel₀ _ hpos.ne').symm
      _ ≤ (1 + max 0 ((Erdos241.f N 2 : ℝ) / Real.sqrt N - 1)) * Real.sqrt N :=
          mul_le_mul_of_nonneg_right (by linarith) hpos.le

theorem main : H1 → H2 → OMA.R_Erdos241_erdos_241_variants_generalization_R1.H2 := by
  intro h1 h2 r hr
  rcases Nat.lt_or_ge r 3 with h | h
  · obtain rfl : r = 2 := by omega
    exact case_two
  · rcases Nat.lt_or_ge r 4 with h' | h'
    · obtain rfl : r = 3 := by omega
      obtain ⟨ε, hε, hb⟩ := h1
      refine ⟨ε, hε, ?_⟩
      filter_upwards [hb] with N hN
      convert hN using 3
      norm_num
    · exact h2 r h'

end OMA.R_Erdos241_erdos_241_variants_generalization_R1_H2_R1

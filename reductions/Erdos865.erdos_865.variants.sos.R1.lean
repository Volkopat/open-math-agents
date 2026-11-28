import FormalConjectures.ErdosProblems.«865»

-- Reduction Erdos865.erdos_865.variants.sos.R1 of the Erdős–Sós asymptotic for f_k(N)
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The Erdős–Sós asymptotic from the upper bounds alone

Write `c_k = (1/2) (1 + ∑_{1 ≤ r ≤ k-2} 4^{-r})`. The target says `f_k(N) ~ c_k N` for every `k ≥ 2`.

This file proves, with no hypothesis:
* the lower bound `f_k(N) ≥ c_k N - k` for every `k ≥ 2` and every `N`, from the layered set
  `⋃_{0 ≤ r ≤ k-2} (N / (2·4^r), N / 4^r]`: two elements of one layer never have their sum in the
  set, so a set with all pairwise sums in it meets each of the `k - 1` layers at most once;
* the case `k = 2` in full (the upper bound is the proved sibling `erdos_865.variants.k2`).

What is left is the upper bound for `k ≥ 3`:
* `H1` is the statement of the main problem `Erdos865.erdos_865`, word for word (the case `k = 3`,
  constant `5/8`). It is a theorem: R. Cipollini, *A sharp 5/8 bound for an Erdős–Sós pairwise-sums
  problem*, arXiv:2606.29361, with two public Lean proofs named in the catalogue file.
* `H2` is the open part: for `k ≥ 4`, every `A ⊆ [1, N]` with `|A| ≥ (c_k + ε) N` contains `k`
  elements with all pairwise sums in `A`, for large `N`. It is a special case of the target
  (the target for `k ≥ 4` gives `f_k(N) ≤ (c_k + ε) N`), and it carries no lower bound.
-/

namespace OMA.R_Erdos865_erdos_865_variants_sos_R1

open Filter Asymptotics Finset Erdos865

/-- Erdős problem 865 itself (`k = 3`): Cipollini, arXiv:2606.29361. Same statement as
`Erdos865.erdos_865`. -/
def H1 : Prop :=
  ∃ C > 0, ∀ᶠ (N : ℕ) in atTop,
    ∀ A ⊆ Icc 1 N, A.card ≥ (5 / 8 : ℝ) * N + C →
    ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    a + b ∈ A ∧ a + c ∈ A ∧ b + c ∈ A

/-- The open part: the upper bound for `k ≥ 4`. -/
def H2 : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∀ ε : ℝ, 0 < ε → ∀ᶠ (N : ℕ) in atTop,
    ∀ A ⊆ Icc 1 N,
      ((1 / 2 : ℝ) * (1 + ∑ r ∈ Icc 1 (k - 2), (1 / 4 : ℝ) ^ r) + ε) * N ≤ A.card →
      ∃ S ⊆ A, S.card = k ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x + y ∈ A

/-- Two elements of layer `r` cannot have their sum in a layer `s`. -/
lemma layer_sum_false {N x y r s : ℕ} (hx1 : x * 4 ^ r ≤ N) (hx2 : N < x * (2 * 4 ^ r))
    (hy1 : y * 4 ^ r ≤ N) (hy2 : N < y * (2 * 4 ^ r))
    (hs1 : (x + y) * 4 ^ s ≤ N) (hs2 : N < (x + y) * (2 * 4 ^ s)) : False := by
  rcases le_or_gt r s with hrs | hrs
  · have hP : 4 ^ r ≤ 4 ^ s := Nat.pow_le_pow_right (by norm_num) hrs
    have h1 : (x + y) * 4 ^ r ≤ (x + y) * 4 ^ s := Nat.mul_le_mul_left _ hP
    nlinarith
  · have hP : 4 ^ (s + 1) ≤ 4 ^ r := Nat.pow_le_pow_right (by norm_num) hrs
    have h1 : (x + y) * 4 ^ (s + 1) ≤ (x + y) * 4 ^ r := Nat.mul_le_mul_left _ hP
    rw [pow_succ] at h1
    nlinarith

/-- An element lies in at most one layer. -/
lemma layer_unique {N x r s : ℕ} (hrs : r < s) (hr2 : N < x * (2 * 4 ^ r))
    (hs1 : x * 4 ^ s ≤ N) : False := by
  have hP : 4 ^ (r + 1) ≤ 4 ^ s := Nat.pow_le_pow_right (by norm_num) hrs
  have h1 : x * 4 ^ (r + 1) ≤ x * 4 ^ s := Nat.mul_le_mul_left _ hP
  rw [pow_succ] at h1
  nlinarith

/-- Size of one layer. -/
lemma layer_card (N r : ℕ) :
    (1 / 2 : ℝ) * (1 / 4 : ℝ) ^ r * N - 1 ≤ ((N / 4 ^ r - N / (2 * 4 ^ r) : ℕ) : ℝ) := by
  have hD : 0 < 4 ^ r := by positivity
  have hDr : (0 : ℝ) < (4 : ℝ) ^ r := by positivity
  have h2 : N / (2 * 4 ^ r) = N / 4 ^ r / 2 := by
    rw [mul_comm, Nat.div_div_eq_div_mul]
  have h3 : N < 4 ^ r * (N / 4 ^ r + 1) := Nat.lt_mul_div_succ N hD
  have h3r : (N : ℝ) < (4 : ℝ) ^ r * ((N / 4 ^ r : ℕ) + 1) := by exact_mod_cast h3
  have h4 : (N : ℝ) / (4 : ℝ) ^ r < ((N / 4 ^ r : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hDr]; linarith
  have h5 : N / 4 ^ r / 2 ≤ N / 4 ^ r := Nat.div_le_self _ _
  have h6 : ((N / 4 ^ r / 2 : ℕ) : ℝ) ≤ ((N / 4 ^ r : ℕ) : ℝ) / 2 := Nat.cast_div_le
  rw [h2, Nat.cast_sub h5]
  have h7 : (1 / 2 : ℝ) * (1 / 4 : ℝ) ^ r * N = (N : ℝ) / (4 : ℝ) ^ r / 2 := by
    rw [one_div_pow]; field_simp
  rw [h7]
  linarith

/-- The layered set: at most `j + 1` elements of it can have all pairwise sums in it. -/
lemma exists_free (N j : ℕ) :
    ∃ A ⊆ Icc 1 N, (∀ S ⊆ A, (∀ x ∈ S, ∀ y ∈ S, x ≠ y → x + y ∈ A) → S.card ≤ j + 1) ∧
      (1 / 2 : ℝ) * (∑ r ∈ range (j + 1), (1 / 4 : ℝ) ^ r) * N - (j + 1) ≤ A.card := by
  classical
  have hmem : ∀ x, x ∈ (range (j + 1)).biUnion (fun r => Ioc (N / (2 * 4 ^ r)) (N / 4 ^ r)) ↔
      ∃ r, r < j + 1 ∧ N < x * (2 * 4 ^ r) ∧ x * 4 ^ r ≤ N := by
    intro x
    simp only [mem_biUnion, mem_range, mem_Ioc]
    constructor
    · rintro ⟨r, hr, h1, h2⟩
      exact ⟨r, hr, (Nat.div_lt_iff_lt_mul (by positivity)).mp h1,
        (Nat.le_div_iff_mul_le (by positivity)).mp h2⟩
    · rintro ⟨r, hr, h1, h2⟩
      exact ⟨r, hr, (Nat.div_lt_iff_lt_mul (by positivity)).mpr h1,
        (Nat.le_div_iff_mul_le (by positivity)).mpr h2⟩
  refine ⟨(range (j + 1)).biUnion (fun r => Ioc (N / (2 * 4 ^ r)) (N / 4 ^ r)), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨r, -, h1, h2⟩ := (hmem x).mp hx
    have hD : 0 < 4 ^ r := by positivity
    rw [mem_Icc]
    constructor
    · rcases Nat.eq_zero_or_pos x with h0 | h0
      · subst h0; simp at h1
      · exact h0
    · nlinarith
  · intro S hS hsum
    by_contra hcard
    have hcard' : (range (j + 1)).card < S.card := by
      rw [card_range]; omega
    have hex : ∀ x ∈ S, ∃ r, r < j + 1 ∧ N < x * (2 * 4 ^ r) ∧ x * 4 ^ r ≤ N :=
      fun x hx => (hmem x).mp (hS hx)
    choose! g hg using hex
    have hmaps : ∀ x ∈ S, g x ∈ range (j + 1) := fun x hx => mem_range.mpr (hg x hx).1
    obtain ⟨x, hx, y, hy, hxy, hgxy⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard' hmaps
    obtain ⟨s, -, hs2, hs1⟩ := (hmem (x + y)).mp (hsum x hx y hy hxy)
    have hx' := hg x hx
    have hy' := hg y hy
    rw [← hgxy] at hy'
    exact layer_sum_false hx'.2.2 hx'.2.1 hy'.2.2 hy'.2.1 hs1 hs2
  · have hdisj : ∀ r ∈ range (j + 1), ∀ s ∈ range (j + 1), r ≠ s →
        Disjoint (Ioc (N / (2 * 4 ^ r)) (N / 4 ^ r)) (Ioc (N / (2 * 4 ^ s)) (N / 4 ^ s)) := by
      intro r _ s _ hrs
      rw [Finset.disjoint_left]
      intro x hxr hxs
      rw [mem_Ioc] at hxr hxs
      have hr2 := (Nat.div_lt_iff_lt_mul (by positivity)).mp hxr.1
      have hr1 := (Nat.le_div_iff_mul_le (by positivity)).mp hxr.2
      have hs2 := (Nat.div_lt_iff_lt_mul (by positivity)).mp hxs.1
      have hs1 := (Nat.le_div_iff_mul_le (by positivity)).mp hxs.2
      rcases Nat.lt_or_gt_of_ne hrs with h | h
      · exact layer_unique h hr2 hs1
      · exact layer_unique h hs2 hr1
    rw [card_biUnion hdisj]
    simp only [Nat.card_Ioc]
    rw [Nat.cast_sum, mul_assoc, Finset.sum_mul, Finset.mul_sum]
    have hsum : ∑ r ∈ range (j + 1), ((1 / 2 : ℝ) * ((1 / 4 : ℝ) ^ r * N) - 1) ≤
        ∑ r ∈ range (j + 1), ((N / 4 ^ r - N / (2 * 4 ^ r) : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro r _
      have := layer_card N r
      linarith
    rw [Finset.sum_sub_distrib] at hsum
    simp only [sum_const, card_range, nsmul_eq_mul, mul_one] at hsum
    push_cast at hsum ⊢
    linarith

/-- The lower bound for `f`. -/
lemma f_lower (N j : ℕ) :
    (1 / 2 : ℝ) * (1 + ∑ r ∈ Icc 1 j, (1 / 4 : ℝ) ^ r) * N - (j + 1) ≤ (f N (j + 2) : ℝ) := by
  obtain ⟨A, hA, hfree, hcard⟩ := exists_free N j
  have hne : {m | ∀ A ⊆ Icc 1 N, A.card ≥ m →
      ∃ S ⊆ A, S.card = j + 2 ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x + y ∈ A}.Nonempty := by
    refine ⟨N + 1, ?_⟩
    intro B hB hcardB
    have := card_le_card hB
    rw [Nat.card_Icc] at this
    omega
  have hmem := Nat.sInf_mem hne
  have hlt : A.card < f N (j + 2) := by
    by_contra hle
    obtain ⟨S, hS, hSc, hSs⟩ := hmem A hA (not_lt.mp hle)
    have := hfree S hS hSs
    omega
  have hsumeq : ∑ r ∈ range (j + 1), (1 / 4 : ℝ) ^ r = 1 + ∑ r ∈ Icc 1 j, (1 / 4 : ℝ) ^ r := by
    rw [Finset.sum_range_succ', pow_zero, add_comm]
    congr 1
    rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (fun r => (1 / 4 : ℝ) ^ r) 0 j 1]
    rfl
  rw [← hsumeq]
  have : (A.card : ℝ) ≤ (f N (j + 2) : ℝ) := by exact_mod_cast hlt.le
  linarith

/-- An upper bound for `f` from a forcing threshold. -/
lemma f_upper (N k : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (h : ∀ A ⊆ Icc 1 N, t ≤ (A.card : ℝ) →
      ∃ S ⊆ A, S.card = k ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x + y ∈ A) :
    (f N k : ℝ) ≤ t + 1 := by
  have hle : f N k ≤ ⌈t⌉₊ := by
    apply Nat.sInf_le
    intro A hA hcard
    exact h A hA ((Nat.ceil_le.mp hcard))
  have h1 : (f N k : ℝ) ≤ (⌈t⌉₊ : ℝ) := by exact_mod_cast hle
  have h2 := Nat.ceil_lt_add_one ht
  linarith

/-- Lower bound for every `N` and an eventual upper bound with slack give the asymptotic. -/
lemma equiv_of_bounds (g : ℕ → ℕ) (c K : ℝ) (hc : 0 < c)
    (hlow : ∀ N : ℕ, c * N - K ≤ (g N : ℝ))
    (hup : ∀ ε : ℝ, 0 < ε → ∃ K' : ℝ, ∀ᶠ (N : ℕ) in atTop, (g N : ℝ) ≤ (c + ε) * N + K') :
    (fun N ↦ (g N : ℝ)) ~[atTop] (fun N ↦ c * N) := by
  rw [IsEquivalent, isLittleO_iff]
  intro δ hδ
  obtain ⟨K', hK'⟩ := hup (δ * c / 2) (by positivity)
  have hev : ∀ᶠ (N : ℕ) in atTop, (2 * (|K| + |K'|) / (δ * c) : ℝ) ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (Filter.eventually_ge_atTop _)
  filter_upwards [hK', hev] with N hN1 hN2
  have hδc : 0 < δ * c := by positivity
  have hN3 : 2 * (|K| + |K'|) ≤ δ * c * N := by
    rw [div_le_iff₀ hδc] at hN2; linarith
  have hNnn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hlow' := hlow N
  have hKa := le_abs_self K
  have hKb := le_abs_self K'
  have hKc := abs_nonneg K
  have hKd := abs_nonneg K'
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ c * N), abs_le]
  constructor <;> nlinarith

theorem main : H1 → H2 → type_of% @Erdos865.erdos_865.variants.sos := by
  intro h1 h2 k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have hjj : j + 2 - 2 = j := by omega
  rw [hjj]
  have hsnn : (0 : ℝ) ≤ ∑ r ∈ Icc 1 j, (1 / 4 : ℝ) ^ r :=
    Finset.sum_nonneg (fun r _ => by positivity)
  have hc : (0 : ℝ) < (1 / 2 : ℝ) * (1 + ∑ r ∈ Icc 1 j, (1 / 4 : ℝ) ^ r) := by positivity
  refine equiv_of_bounds (fun N => f N (j + 2)) _ (j + 1) hc (fun N => f_lower N j) ?_
  intro ε hε
  rcases Nat.lt_or_ge j 2 with hj | hj
  · interval_cases j
    · -- k = 2
      refine ⟨3, Filter.Eventually.of_forall (fun N => ?_)⟩
      have hup := f_upper N 2 ((N : ℝ) / 2 + 2) (by positivity) (by
        intro A hA hcard
        have hA' : A ⊆ Icc 1 (2 * ((N + 1) / 2)) :=
          hA.trans (Icc_subset_Icc_right (by omega))
        have hc2 : A.card ≥ (N + 1) / 2 + 2 := by
          have h3 : ((N : ℝ) + 4) / 2 ≤ (A.card : ℝ) := by linarith
          have h4 : (N + 4 : ℝ) ≤ 2 * (A.card : ℝ) := by linarith
          have h5 : N + 4 ≤ 2 * A.card := by exact_mod_cast h4
          omega
        obtain ⟨a, ha, b, hb, hab, habA⟩ := erdos_865.variants.k2 ((N + 1) / 2) A hA' hc2
        refine ⟨{a, b}, ?_, card_pair hab, ?_⟩
        · intro x hx
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        · intro x hx y hy hxy
          simp only [mem_insert, mem_singleton] at hx hy
          rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
            first
              | exact absurd rfl hxy
              | assumption
              | (rw [add_comm]; assumption))
      have hNnn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      simp only [Icc_eq_empty_of_lt (by norm_num : (0 : ℕ) < 1), sum_empty, add_zero]
      nlinarith
    · -- k = 3
      obtain ⟨C, hC, hev⟩ := h1
      refine ⟨C + 1, ?_⟩
      filter_upwards [hev] with N hN
      have hNnn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have hup := f_upper N 3 ((5 / 8 : ℝ) * N + C) (by positivity) (by
        intro A hA hcard
        obtain ⟨a, ha, b, hb, c, hc', hab, hac, hbc, h4, h5, h6⟩ := hN A hA hcard
        refine ⟨{a, b, c}, ?_, card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩, ?_⟩
        · intro x hx
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl | rfl <;> assumption
        · intro x hx y hy hxy
          simp only [mem_insert, mem_singleton] at hx hy
          rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
            first
              | exact absurd rfl hxy
              | assumption
              | (rw [add_comm]; assumption))
      simp only [Icc_self, sum_singleton, pow_one]
      nlinarith
  · -- k ≥ 4
    refine ⟨1, ?_⟩
    filter_upwards [h2 (j + 2) (by omega) ε hε] with N hN
    rw [hjj] at hN
    have hNnn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hup := f_upper N (j + 2)
      (((1 / 2 : ℝ) * (1 + ∑ r ∈ Icc 1 j, (1 / 4 : ℝ) ^ r) + ε) * N) (by positivity) hN
    linarith

end OMA.R_Erdos865_erdos_865_variants_sos_R1

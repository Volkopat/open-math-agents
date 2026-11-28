import OMAReductions.R_Green43_green_43_variants_general_exponent_R1

-- Step Green43.green_43.variants.general_exponent.R1.H1: the sieve bound is monotone in the exponent
-- Credit: @LordMike

namespace OMAGreen43Mono

open Finset Green43

/-- A residue class modulo `q` has at most `M / q + 1` points in `[1, M]`. -/
lemma card_class_le (M q : ℕ) (hq : 0 < q) (c : ℤ) :
    ((Icc (1 : ℤ) M).filter (fun n => (q : ℤ) ∣ n - c)).card ≤ M / q + 1 := by
  have := Finset.card_le_card_of_injOn
    (s := (Icc (1 : ℤ) M).filter (fun n => (q : ℤ) ∣ n - c))
    (t := Finset.range (M / q + 1)) (fun n : ℤ => (n - 1).toNat / q) ?_ ?_
  · simpa using this
  · intro n hn
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn
    rw [Finset.mem_coe, Finset.mem_range, Nat.lt_succ_iff]
    apply Nat.div_le_div_right
    omega
  · intro n hn n' hn' h
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn hn'
    have hd : (q : ℤ) ∣ n - n' := by
      have := dvd_sub hn.2 hn'.2
      rwa [show n - c - (n' - c) = n - n' by ring] at this
    have h' : (n - 1).toNat / q = (n' - 1).toNat / q := h
    have hu1 : (((n - 1).toNat : ℕ) : ℤ) = n - 1 := Int.toNat_of_nonneg (by omega)
    have hu1' : (((n' - 1).toNat : ℕ) : ℤ) = n' - 1 := Int.toNat_of_nonneg (by omega)
    generalize (n - 1).toNat = u at h' hu1
    generalize (n' - 1).toNat = u' at h' hu1'
    have e1 := Nat.div_add_mod u q
    have e2 := Nat.div_add_mod u' q
    have hr1 := Nat.mod_lt u hq
    have hr2 := Nat.mod_lt u' hq
    rw [h'] at e1
    have key : u % q + u' = u' % q + u := by
      generalize q * (u' / q) = X at e1 e2
      omega
    have keyZ : ((u % q : ℕ) : ℤ) + u' = ((u' % q : ℕ) : ℤ) + u := by exact_mod_cast key
    have hdiff : n - n' = ((u % q : ℕ) : ℤ) - ((u' % q : ℕ) : ℤ) := by linarith
    rw [hdiff] at hd
    have hr1Z : ((u % q : ℕ) : ℤ) < (q : ℤ) := by exact_mod_cast hr1
    have hr2Z : ((u' % q : ℕ) : ℤ) < (q : ℤ) := by exact_mod_cast hr2
    have hz := Int.eq_zero_of_abs_lt_dvd hd (by
      rw [abs_lt]
      constructor <;> linarith [(Nat.cast_nonneg (u % q) : (0 : ℤ) ≤ ((u % q : ℕ) : ℤ)),
        (Nat.cast_nonneg (u' % q) : (0 : ℤ) ≤ ((u' % q : ℕ) : ℤ))])
    linarith

/-- Cut `[1, N]` into `N / M` blocks of length `M`. The sieved set of `[1, N]` contains a shifted
copy of the sieved set of each block, for the shifted classes. -/
lemma blocks (N M : ℕ) (hM : 0 < M) (a : ℕ → ℤ) (lo hi : ℝ) :
    ∑ t ∈ range (N / M), sievedCard M (fun p => a p - (t : ℤ) * M) lo hi ≤
      sievedCard N a lo hi := by
  classical
  unfold sievedCard
  have hMZ : (0 : ℤ) < M := by exact_mod_cast hM
  set G : ℕ → Finset ℤ := fun t =>
    (sievedSet M (fun p => a p - (t : ℤ) * M) lo hi).image (fun n => n + (t : ℤ) * M) with hG
  have hsub : (range (N / M)).biUnion G ⊆ sievedSet N a lo hi := by
    intro x hx
    obtain ⟨t, ht, hx⟩ := mem_biUnion.mp hx
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hx
    unfold sievedSet at hn ⊢
    rw [mem_filter, mem_Icc] at hn ⊢
    obtain ⟨⟨h1, h2⟩, p, hp, hlo, hhi, hdvd⟩ := hn
    have ht' : t + 1 ≤ N / M := mem_range.mp ht
    have h3 : (t + 1) * M ≤ N := (Nat.mul_le_mul_right M ht').trans (Nat.div_mul_le_self N M)
    have h4 : ((t : ℤ) + 1) * M ≤ N := by exact_mod_cast h3
    have h5 : (0 : ℤ) ≤ (t : ℤ) * M := by positivity
    refine ⟨⟨by linarith, by linarith⟩, p, hp, hlo, hhi, ?_⟩
    have e : n + (t : ℤ) * M - a p = n - (a p - (t : ℤ) * M) := by ring
    rw [e]
    exact hdvd
  have hlt : ∀ t t' : ℕ, t < t' → Disjoint (G t) (G t') := by
    intro t t' htt
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hx
    obtain ⟨n', hn', hnn⟩ := mem_image.mp hx'
    unfold sievedSet at hn hn'
    rw [mem_filter, mem_Icc] at hn hn'
    have h1 : ((t : ℤ) + 1) * M ≤ (t' : ℤ) * M := by
      have : (t : ℤ) + 1 ≤ t' := by exact_mod_cast htt
      exact mul_le_mul_of_nonneg_right this hMZ.le
    linarith [hn.1.1, hn.1.2, hn'.1.1, hn'.1.2]
  have hdisj : ((range (N / M) : Finset ℕ) : Set ℕ).PairwiseDisjoint G := by
    intro t _ t' _ htt
    rcases lt_or_gt_of_ne htt with h | h
    · exact hlt t t' h
    · exact (hlt t' t h).symm
  calc ∑ t ∈ range (N / M), (sievedSet M (fun p => a p - (t : ℤ) * M) lo hi).card
      = ∑ t ∈ range (N / M), (G t).card := by
        refine Finset.sum_congr rfl fun t _ => ?_
        exact (Finset.card_image_of_injective _ (add_left_injective _)).symm
    _ = ((range (N / M)).biUnion G).card := (Finset.card_biUnion hdisj).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- Moving the prime range from `[b, 2 * b)` to `[y, 2 * y)` with `b ≤ y < b + 1` loses at most one
prime, hence at most one residue class. -/
lemma shrink (M : ℕ) (a : ℕ → ℤ) (b y : ℝ) (hb1 : 1 ≤ b) (hby : b ≤ y) (hyb : y < b + 1) :
    (sievedCard M a b (2 * b) : ℝ) ≤ sievedCard M a y (2 * y) + (M / b + 1) := by
  classical
  have hqb : b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
  have hq0 : 0 < ⌈b⌉₊ := Nat.ceil_pos.mpr (by linarith)
  have hsub : sievedSet M a b (2 * b) ⊆ sievedSet M a y (2 * y) ∪
      (Icc (1 : ℤ) M).filter (fun n => ((⌈b⌉₊ : ℕ) : ℤ) ∣ n - a ⌈b⌉₊) := by
    intro n hn
    unfold sievedSet at hn ⊢
    rw [mem_filter] at hn
    obtain ⟨hI, p, hp, hlo, hhi, hdvd⟩ := hn
    rw [mem_union, mem_filter, mem_filter]
    by_cases hpy : y ≤ p
    · left
      exact ⟨hI, p, hp, hpy, by linarith, hdvd⟩
    · right
      have hpq : ⌈b⌉₊ = p := by
        rw [Nat.ceil_eq_iff hp.pos.ne']
        refine ⟨?_, hlo⟩
        have e : ((p - 1 : ℕ) : ℝ) = p - 1 := by
          rw [Nat.cast_sub hp.pos]
          simp
        rw [e]
        rw [not_le] at hpy
        linarith
      rw [hpq]
      exact ⟨hI, hdvd⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (sievedSet M a y (2 * y))
    ((Icc (1 : ℤ) M).filter (fun n => ((⌈b⌉₊ : ℕ) : ℤ) ∣ n - a ⌈b⌉₊))
  have h3 := card_class_le M ⌈b⌉₊ hq0 (a ⌈b⌉₊)
  have h4 : ((M / ⌈b⌉₊ : ℕ) : ℝ) ≤ M / b := by
    calc ((M / ⌈b⌉₊ : ℕ) : ℝ) ≤ (M : ℝ) / (⌈b⌉₊ : ℝ) := Nat.cast_div_le
      _ ≤ M / b := div_le_div_of_nonneg_left (by positivity) (by linarith) hqb
  unfold sievedCard
  have h5 : (sievedSet M a b (2 * b)).card ≤
      (sievedSet M a y (2 * y)).card + (M / ⌈b⌉₊ + 1) :=
    h1.trans (h2.trans (Nat.add_le_add_left h3 _))
  have h6 : ((sievedSet M a b (2 * b)).card : ℝ) ≤
      (sievedSet M a y (2 * y)).card + (((M / ⌈b⌉₊ : ℕ) : ℝ) + 1) := by exact_mod_cast h5
  linarith

/-- The lost class is at most half of the bound in a block. -/
lemma lost_le (M b v w : ℝ) (hM : 1 ≤ M) (hb1 : 1 ≤ b) (hbM : b ≤ M) (hbv : b = v * v)
    (hv : 6 ≤ v) (hw1 : 1 ≤ w) (hwv : w ≤ v) : M / b + 1 ≤ M / (2 * w) := by
  rw [div_add_one (by linarith), div_le_div_iff₀ (by linarith) (by linarith)]
  have hA : M + b ≤ 2 * M := by linarith
  have hB : (M + b) * (2 * w) ≤ (2 * M) * (2 * v) :=
    mul_le_mul hA (by linarith) (by linarith) (by linarith)
  have hC : M * (6 * v) ≤ M * b := by
    rw [hbv]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hv (by linarith)) (by linarith)
  have hD : 0 ≤ M * v := mul_nonneg (by linarith) (by linarith)
  linarith

/-- The block count: a bound `M / w` in every block of length `M` for the range `[b, 2 * b)` gives
`N / (4 * w)` in `[1, N]` for the range `[y, 2 * y)`. -/
lemma step (N M : ℕ) (a : ℕ → ℤ) (b y w : ℝ) (hM1 : 1 ≤ M) (h2M : 2 * (M : ℝ) ≤ N)
    (hb1 : 1 ≤ b) (hby : b ≤ y) (hyb : y < b + 1) (hw : 0 < w)
    (hlost : (M : ℝ) / b + 1 ≤ M / (2 * w))
    (hP : ∀ a' : ℕ → ℤ, (M : ℝ) / w ≤ sievedCard M a' b (2 * b)) :
    (N : ℝ) / (4 * w) ≤ sievedCard N a y (2 * y) := by
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hM0 : 0 < M := hM1
  have hblock : ∀ a' : ℕ → ℤ, (M : ℝ) / (2 * w) ≤ sievedCard M a' y (2 * y) := by
    intro a'
    have h1 := hP a'
    have h2 := shrink M a' b y hb1 hby hyb
    have h4 : (M : ℝ) / w = M / (2 * w) + M / (2 * w) := by
      field_simp
      ring
    linarith
  have hT := blocks N M hM0 a y (2 * y)
  have hsum : ((N / M : ℕ) : ℝ) * ((M : ℝ) / (2 * w)) ≤
      ∑ t ∈ range (N / M), (sievedCard M (fun p => a p - (t : ℤ) * M) y (2 * y) : ℝ) := by
    have := Finset.sum_le_sum
      (fun t (_ : t ∈ range (N / M)) => hblock (fun p => a p - (t : ℤ) * M))
    rw [Finset.sum_const, card_range, nsmul_eq_mul] at this
    exact this
  have hTR : (∑ t ∈ range (N / M),
      (sievedCard M (fun p => a p - (t : ℤ) * M) y (2 * y) : ℝ)) ≤
      sievedCard N a y (2 * y) := by exact_mod_cast hT
  have hTge : (N : ℝ) / (2 * M) ≤ ((N / M : ℕ) : ℝ) := by
    have h1 : (N : ℝ) < ((N / M : ℕ) : ℝ) * M + M := by
      have := Nat.lt_div_mul_add (a := N) hM0
      exact_mod_cast this
    rw [div_le_iff₀ (by linarith)]
    linarith
  have e1 : (N : ℝ) / (2 * M) * ((M : ℝ) / (2 * w)) = N / (4 * w) := by
    field_simp
    ring
  have hstep : (N : ℝ) / (2 * M) * ((M : ℝ) / (2 * w)) ≤
      ((N / M : ℕ) : ℝ) * ((M : ℝ) / (2 * w)) :=
    mul_le_mul_of_nonneg_right hTge (by positivity)
  linarith

/-- The real-exponent bookkeeping for `M = ⌊N ^ γ⌋` with `γ * β = α`. -/
lemma exponents (N M : ℕ) (α β γ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγβ : γ * β = α)
    (hN1 : 1 ≤ N) (hMz : (M : ℝ) ≤ (N : ℝ) ^ γ) (hzM : (N : ℝ) ^ γ < (M : ℝ) + 1) :
    (M : ℝ) ^ β ≤ (N : ℝ) ^ α ∧ (N : ℝ) ^ α < (M : ℝ) ^ β + 1 := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hz0 : 0 ≤ (N : ℝ) ^ γ := by positivity
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hzy : ((N : ℝ) ^ γ) ^ β = (N : ℝ) ^ α := by
    rw [← Real.rpow_mul (by linarith), hγβ]
  constructor
  · rw [← hzy]
    exact Real.rpow_le_rpow hM0 hMz hβ0.le
  · rw [← hzy]
    calc ((N : ℝ) ^ γ) ^ β < ((M : ℝ) + 1) ^ β := Real.rpow_lt_rpow hz0 hzM hβ0
      _ ≤ (M : ℝ) ^ β + (1 : ℝ) ^ β :=
          Real.rpow_add_le_add_rpow hM0 zero_le_one hβ0.le hβ1.le
      _ = (M : ℝ) ^ β + 1 := by rw [Real.one_rpow]

/-- The final comparison `N ^ (1 - ε) ≤ N / (4 * M ^ ε')`. -/
lemma final (N M : ℕ) (γ ε ε' : ℝ) (hγ0 : 0 < γ) (hε'0 : 0 < ε') (hε'ε : ε' ≤ ε)
    (hN1 : 1 ≤ N) (hM1 : 1 ≤ M) (hMz : (M : ℝ) ≤ (N : ℝ) ^ γ)
    (hN4 : 4 ≤ (N : ℝ) ^ (ε * (1 - γ))) :
    (N : ℝ) ^ (1 - ε) ≤ N / (4 * (M : ℝ) ^ ε') := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hw1 : 1 ≤ (M : ℝ) ^ ε' := Real.one_le_rpow hMR hε'0.le
  have hsplit : (N : ℝ) ^ ε = (N : ℝ) ^ (γ * ε) * (N : ℝ) ^ (ε * (1 - γ)) := by
    rw [← Real.rpow_add (by linarith)]
    ring_nf
  have hNε : (N : ℝ) ^ (1 - ε) = N / (N : ℝ) ^ ε := by
    rw [Real.rpow_sub (by linarith), Real.rpow_one]
  have hw2 : (M : ℝ) ^ ε' ≤ (N : ℝ) ^ (γ * ε) := by
    calc (M : ℝ) ^ ε' ≤ ((N : ℝ) ^ γ) ^ ε' := Real.rpow_le_rpow (by linarith) hMz hε'0.le
      _ = (N : ℝ) ^ (γ * ε') := by rw [← Real.rpow_mul (by linarith)]
      _ ≤ (N : ℝ) ^ (γ * ε) :=
          Real.rpow_le_rpow_of_exponent_le hNR (mul_le_mul_of_nonneg_left hε'ε hγ0.le)
  rw [hNε]
  apply div_le_div_of_nonneg_left (by linarith) (by linarith)
  rw [hsplit]
  have hP0 : 0 ≤ (N : ℝ) ^ (γ * ε) := by linarith
  calc 4 * (M : ℝ) ^ ε' ≤ (N : ℝ) ^ (γ * ε) * 4 := by linarith
    _ ≤ (N : ℝ) ^ (γ * ε) * (N : ℝ) ^ (ε * (1 - γ)) := mul_le_mul_of_nonneg_left hN4 hP0

theorem mono (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hβ1 : β < 1)
    (h : SievedLowerBoundExp β) : SievedLowerBoundExp α := by
  unfold SievedLowerBoundExp SievedLowerBound at h ⊢
  intro ε hε
  have hβ0 : 0 < β := hα.trans hαβ
  have hγ0 : 0 < α / β := div_pos hα hβ0
  have hγ1 : α / β < 1 := (div_lt_one hβ0).mpr hαβ
  have hγβ : α / β * β = α := div_mul_cancel₀ α hβ0.ne'
  have hε'0 : 0 < min ε (β / 2) := lt_min hε (by linarith)
  have hε'ε : min ε (β / 2) ≤ ε := min_le_left _ _
  have hε'β : min ε (β / 2) ≤ β / 2 := min_le_right _ _
  have hzN : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (α / β)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hγ0).comp tendsto_natCast_atTop_atTop
  have hMN : Filter.Tendsto (fun N : ℕ => ⌊(N : ℝ) ^ (α / β)⌋₊) Filter.atTop Filter.atTop :=
    tendsto_nat_floor_atTop.comp hzN
  have hvM : Filter.Tendsto (fun M : ℕ => (M : ℝ) ^ (β / 2)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  have h1N : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - α / β)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  have h2N : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (ε * (1 - α / β)))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (mul_pos hε (by linarith))).comp tendsto_natCast_atTop_atTop
  filter_upwards [hMN.eventually (h (min ε (β / 2)) hε'0),
    hMN.eventually (hvM.eventually_ge_atTop 6),
    hMN.eventually (Filter.eventually_ge_atTop 1), h1N.eventually_ge_atTop 2,
    h2N.eventually_ge_atTop 4, Filter.eventually_ge_atTop 1] with N hP hv hM1 hN2 hN4 hN1
  intro a
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hz0 : 0 ≤ (N : ℝ) ^ (α / β) := by positivity
  have hMz : ((⌊(N : ℝ) ^ (α / β)⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) ^ (α / β) := Nat.floor_le hz0
  have hzM : (N : ℝ) ^ (α / β) < ((⌊(N : ℝ) ^ (α / β)⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  generalize ⌊(N : ℝ) ^ (α / β)⌋₊ = M at hP hv hM1 hMz hzM
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  obtain ⟨hby, hyb⟩ := exponents N M α β (α / β) hβ0 hβ1 hγβ hN1 hMz hzM
  have hb1 : 1 ≤ (M : ℝ) ^ β := Real.one_le_rpow hMR hβ0.le
  have hbM : (M : ℝ) ^ β ≤ M := by
    have := Real.rpow_le_rpow_of_exponent_le hMR hβ1.le
    rwa [Real.rpow_one] at this
  have hbv : (M : ℝ) ^ β = (M : ℝ) ^ (β / 2) * (M : ℝ) ^ (β / 2) := by
    rw [← Real.rpow_add (by linarith)]
    ring_nf
  have hw1 : 1 ≤ (M : ℝ) ^ min ε (β / 2) := Real.one_le_rpow hMR hε'0.le
  have hwv : (M : ℝ) ^ min ε (β / 2) ≤ (M : ℝ) ^ (β / 2) :=
    Real.rpow_le_rpow_of_exponent_le hMR hε'β
  have hMw : (M : ℝ) ^ (1 - min ε (β / 2)) = M / (M : ℝ) ^ min ε (β / 2) := by
    rw [Real.rpow_sub (by linarith), Real.rpow_one]
  have h2M : 2 * (M : ℝ) ≤ N := by
    have hNsplit : (N : ℝ) = (N : ℝ) ^ (α / β) * (N : ℝ) ^ (1 - α / β) := by
      rw [← Real.rpow_add (by linarith)]
      simp
    have := mul_le_mul_of_nonneg_left hN2 hz0
    linarith
  have hlost := lost_le M ((M : ℝ) ^ β) ((M : ℝ) ^ (β / 2)) ((M : ℝ) ^ min ε (β / 2))
    hMR hb1 hbM hbv hv hw1 hwv
  have hP' : ∀ a' : ℕ → ℤ, (M : ℝ) / (M : ℝ) ^ min ε (β / 2) ≤
      sievedCard M a' ((M : ℝ) ^ β) (2 * (M : ℝ) ^ β) := by
    intro a'
    rw [← hMw]
    exact hP a'
  have hmain := step N M a ((M : ℝ) ^ β) ((N : ℝ) ^ α) ((M : ℝ) ^ min ε (β / 2)) hM1 h2M
    hb1 hby hyb (by linarith) hlost hP'
  have hfin := final N M (α / β) ε (min ε (β / 2)) hγ0 hε'0 hε'ε hN1 hM1 hMz hN4
  linarith

end OMAGreen43Mono

theorem OMA.solution : OMA.R_Green43_green_43_variants_general_exponent_R1.H1 :=
  fun α β hα hαβ hβ1 h => OMAGreen43Mono.mono α β hα hαβ hβ1 h

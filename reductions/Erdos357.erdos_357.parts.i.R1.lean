import FormalConjectures.ErdosProblems.«357»

/-!
# Erdős 357 (i): reduction to dyadic blocks, sorted by jump size
Credit: @sntntHb

A sequence counted by `f n` lies in `[1, n]`. Its terms with value in a dyadic block
`[c, 2c)` form a consecutive run of the sequence, and every term except the last has a
jump `j = a (i+1) - a i ≥ 1`. Jumps larger than `K` occur at most `n / K + 1` times, and the
terms below `2^C` number at most `2^C`. So it suffices to know, for every fixed jump size `j`,
that inside a single block `[c, 2c)` the positions with jump exactly `j` are `o(c)`.

H1 is this statement for jump `1` (runs of consecutive integers; a pure run of length about
`2 √c` already forces two equal consecutive sums). H2 is the same statement for every fixed
jump `j ≥ 2`. Numerically, optimal sequences in a block `[c, 2c)` have about `4.4 √c` terms
(c up to 800), made of short runs joined by jumps 1 to 3, so both hypotheses are expected to hold
with room to spare. `main` proves `f(n) = o(n)` from H1 and H2 by summing the block bounds over
dyadic blocks and over jump sizes.
-/

namespace OMA.R_Erdos357_erdos_357_parts_i_R1

open Finset

def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℕ, ∀ c : ℕ, C ≤ c → ∀ (k : ℕ) (a : Fin k → ℤ), StrictMono a →
    Erdos357.HasDistinctSums a →
    ((univ.filter (fun i : Fin k => (c : ℤ) ≤ a i ∧ a i < 2 * (c : ℤ) ∧
      ∃ h : i.val + 1 < k, a ⟨i.val + 1, h⟩ = a i + 1)).card : ℝ) ≤ ε * c

def H2 : Prop :=
  ∀ j : ℕ, 2 ≤ j → ∀ ε : ℝ, 0 < ε → ∃ C : ℕ, ∀ c : ℕ, C ≤ c → ∀ (k : ℕ) (a : Fin k → ℤ),
    StrictMono a → Erdos357.HasDistinctSums a →
    ((univ.filter (fun i : Fin k => (c : ℤ) ≤ a i ∧ a i < 2 * (c : ℤ) ∧
      ∃ h : i.val + 1 < k, a ⟨i.val + 1, h⟩ = a i + (j : ℤ))).card : ℝ) ≤ ε * c

theorem low_card {k : ℕ} (a : Fin k → ℤ) (hinj : Function.Injective a)
    (hpos : ∀ i, 1 ≤ a i) (B : ℕ) : (univ.filter (fun i : Fin k => a i < (B : ℤ))).card ≤ B := by
  have h := Finset.card_le_card_of_injOn a (s := univ.filter (fun i : Fin k => a i < (B : ℤ)))
    (t := Finset.Ico (1 : ℤ) B)
    (fun i hi => by
      rw [Finset.mem_coe, mem_filter] at hi
      rw [Finset.mem_coe, mem_Ico]
      exact ⟨hpos i, hi.2⟩) hinj.injOn
  simp only [Int.card_Ico] at h
  omega

theorem big_card {k n K : ℕ} (a : Fin k → ℤ) (hm : StrictMono a) (hK : 1 ≤ K)
    (hr : ∀ i, 1 ≤ a i ∧ a i ≤ n) :
    (univ.filter (fun i : Fin k => ∃ h : i.val + 1 < k, a i + K < a ⟨i.val + 1, h⟩)).card
      ≤ n / K + 1 := by
  have hK' : (0 : ℤ) < K := by exact_mod_cast hK
  have key : ∀ i i' : Fin k, i < i' → (∃ h : i.val + 1 < k, a i + K < a ⟨i.val + 1, h⟩) →
      (a i - 1) / K < (a i' - 1) / K := by
    intro i i' hii' ⟨h, hlt⟩
    have hle : a ⟨i.val + 1, h⟩ ≤ a i' := hm.monotone (by
      show i.val + 1 ≤ i'.val
      exact hii')
    have h1 : (a i - 1) / K + 1 = (a i - 1 + 1 * K) / K := by
      rw [Int.add_mul_ediv_right _ _ (ne_of_gt hK')]
    have h2 : (a i - 1 + 1 * K) / K ≤ (a i' - 1) / K :=
      Int.ediv_le_ediv hK' (by linarith)
    linarith
  have h := Finset.card_le_card_of_injOn (fun i => (a i - 1) / (K : ℤ))
    (s := univ.filter (fun i : Fin k => ∃ h : i.val + 1 < k, a i + K < a ⟨i.val + 1, h⟩))
    (t := Finset.Icc (0 : ℤ) ((n : ℤ) / K))
    (fun i _ => by
      rw [Finset.mem_coe, mem_Icc]
      constructor
      · exact Int.ediv_nonneg (by linarith [(hr i).1]) hK'.le
      · exact Int.ediv_le_ediv hK' (by linarith [(hr i).2]))
    (by
      intro i hi i' hi' heq
      rw [Finset.mem_coe, mem_filter] at hi hi'
      replace hi := hi.2
      replace hi' := hi'.2
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact absurd heq (ne_of_lt (key i i' hlt hi))
      · exact absurd heq (ne_of_gt (key i' i hlt hi')))
  simp only [Int.card_Icc] at h
  have e : (n : ℤ) / (K : ℤ) = ((n / K : ℕ) : ℤ) := (Int.natCast_div n K).symm
  rw [e] at h
  clear e key
  generalize n / K = q at h ⊢
  omega

theorem geom_two (L : ℕ) : ∑ m ∈ range L, 2 ^ m + 1 = 2 ^ L := by
  induction L with
  | zero => simp
  | succ L ih => rw [sum_range_succ, pow_succ]; omega

theorem block_card {k n C j : ℕ} (a : Fin k → ℤ) (hr : ∀ i, 1 ≤ a i ∧ a i ≤ n) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hb : ∀ c : ℕ, C ≤ c → ((univ.filter (fun i : Fin k => (c : ℤ) ≤ a i ∧ a i < 2 * (c : ℤ) ∧
      ∃ h : i.val + 1 < k, a ⟨i.val + 1, h⟩ = a i + (j : ℤ))).card : ℝ) ≤ ε * c) :
    ((univ.filter (fun i : Fin k => ((2 ^ C : ℕ) : ℤ) ≤ a i ∧
      ∃ h : i.val + 1 < k, a ⟨i.val + 1, h⟩ = a i + (j : ℤ))).card : ℝ) ≤ ε * (2 * n) := by
  classical
  by_cases hn : n = 0
  · have : (univ.filter (fun i : Fin k => ((2 ^ C : ℕ) : ℤ) ≤ a i ∧
        ∃ h : i.val + 1 < k, a ⟨i.val + 1, h⟩ = a i + (j : ℤ))) = ∅ := by
      rw [filter_eq_empty_iff]
      intro i _
      have := hr i
      subst hn
      push_cast at this
      omega
    rw [this, card_empty, Nat.cast_zero]
    positivity
  set L := Nat.log 2 n with hL
  have hsub : (univ.filter (fun i : Fin k => ((2 ^ C : ℕ) : ℤ) ≤ a i ∧
      ∃ h : i.val + 1 < k, a ⟨i.val + 1, h⟩ = a i + (j : ℤ))) ⊆
      (Finset.Icc C L).biUnion (fun m => univ.filter (fun i : Fin k =>
        ((2 ^ m : ℕ) : ℤ) ≤ a i ∧ a i < 2 * ((2 ^ m : ℕ) : ℤ) ∧
        ∃ h : i.val + 1 < k, a ⟨i.val + 1, h⟩ = a i + (j : ℤ))) := by
    intro i hi
    rw [mem_filter] at hi
    obtain ⟨_, hC, hj⟩ := hi
    have hv : ((a i).toNat : ℤ) = a i := Int.toNat_of_nonneg (by linarith [(hr i).1])
    have hv1 : 1 ≤ (a i).toNat := by have := (hr i).1; omega
    have hvn : (a i).toNat ≤ n := by have := (hr i).2; omega
    have h1 : 2 ^ (Nat.log 2 (a i).toNat) ≤ (a i).toNat := Nat.pow_log_le_self 2 (by omega)
    have h2 : (a i).toNat < 2 ^ (Nat.log 2 (a i).toNat + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) _
    have hCv : 2 ^ C ≤ (a i).toNat := by
      have : ((2 ^ C : ℕ) : ℤ) ≤ ((a i).toNat : ℤ) := by rw [hv]; exact hC
      exact_mod_cast this
    have hmC : C ≤ Nat.log 2 (a i).toNat := Nat.le_log_of_pow_le (by norm_num) hCv
    have hmL : Nat.log 2 (a i).toNat ≤ L := Nat.log_mono_right hvn
    rw [mem_biUnion]
    refine ⟨Nat.log 2 (a i).toNat, mem_Icc.mpr ⟨hmC, hmL⟩, ?_⟩
    rw [mem_filter]
    refine ⟨mem_univ _, ?_, ?_, hj⟩
    · have : ((2 ^ Nat.log 2 (a i).toNat : ℕ) : ℤ) ≤ ((a i).toNat : ℤ) := by exact_mod_cast h1
      linarith
    · have h3 : (a i).toNat < 2 * 2 ^ Nat.log 2 (a i).toNat := by rw [pow_succ] at h2; omega
      have : ((a i).toNat : ℤ) < 2 * ((2 ^ Nat.log 2 (a i).toNat : ℕ) : ℤ) := by exact_mod_cast h3
      linarith
  have hc1 := card_le_card hsub
  have hc2 := card_biUnion_le (s := Finset.Icc C L) (t := fun m => univ.filter (fun i : Fin k =>
        ((2 ^ m : ℕ) : ℤ) ≤ a i ∧ a i < 2 * ((2 ^ m : ℕ) : ℤ) ∧
        ∃ h : i.val + 1 < k, a ⟨i.val + 1, h⟩ = a i + (j : ℤ)))
  have hsum : (∑ m ∈ Finset.Icc C L, ((univ.filter (fun i : Fin k =>
        ((2 ^ m : ℕ) : ℤ) ≤ a i ∧ a i < 2 * ((2 ^ m : ℕ) : ℤ) ∧
        ∃ h : i.val + 1 < k, a ⟨i.val + 1, h⟩ = a i + (j : ℤ))).card : ℝ))
      ≤ ∑ m ∈ Finset.Icc C L, ε * ((2 ^ m : ℕ) : ℝ) := by
    apply sum_le_sum
    intro m hm
    rw [mem_Icc] at hm
    exact hb _ (le_trans hm.1 (Nat.lt_two_pow_self).le)
  have hgeo : ∑ m ∈ Finset.Icc C L, 2 ^ m ≤ 2 * n := by
    have hs : Finset.Icc C L ⊆ range (L + 1) := by
      intro m hm; rw [mem_Icc] at hm; rw [mem_range]; omega
    have := sum_le_sum_of_subset (f := fun m => 2 ^ m) hs
    have hg := geom_two (L + 1)
    have hLn : 2 ^ L ≤ n := Nat.pow_log_le_self 2 hn
    rw [pow_succ] at hg
    omega
  have hgeoR : (∑ m ∈ Finset.Icc C L, ((2 ^ m : ℕ) : ℝ)) ≤ 2 * n := by exact_mod_cast hgeo
  calc ((univ.filter (fun i : Fin k => ((2 ^ C : ℕ) : ℤ) ≤ a i ∧
      ∃ h : i.val + 1 < k, a ⟨i.val + 1, h⟩ = a i + (j : ℤ))).card : ℝ)
      ≤ ((∑ m ∈ Finset.Icc C L, (univ.filter (fun i : Fin k =>
        ((2 ^ m : ℕ) : ℤ) ≤ a i ∧ a i < 2 * ((2 ^ m : ℕ) : ℤ) ∧
        ∃ h : i.val + 1 < k, a ⟨i.val + 1, h⟩ = a i + (j : ℤ))).card : ℕ) : ℝ) := by
        exact_mod_cast le_trans hc1 hc2
    _ = ∑ m ∈ Finset.Icc C L, ((univ.filter (fun i : Fin k =>
        ((2 ^ m : ℕ) : ℤ) ≤ a i ∧ a i < 2 * ((2 ^ m : ℕ) : ℤ) ∧
        ∃ h : i.val + 1 < k, a ⟨i.val + 1, h⟩ = a i + (j : ℤ))).card : ℝ) := by push_cast; rfl
    _ ≤ ∑ m ∈ Finset.Icc C L, ε * ((2 ^ m : ℕ) : ℝ) := hsum
    _ = ε * ∑ m ∈ Finset.Icc C L, ((2 ^ m : ℕ) : ℝ) := by rw [mul_sum]
    _ ≤ ε * (2 * n) := mul_le_mul_of_nonneg_left hgeoR hε

theorem count_le {k n K C : ℕ} (a : Fin k → ℤ) (hm : StrictMono a) (hK : 1 ≤ K)
    (hr : ∀ i, 1 ≤ a i ∧ a i ≤ n) :
    k ≤ 1 + 2 ^ C + (n / K + 1) + ∑ j ∈ Finset.Icc 1 K,
      (univ.filter (fun i : Fin k => ((2 ^ C : ℕ) : ℤ) ≤ a i ∧
        ∃ h : i.val + 1 < k, a ⟨i.val + 1, h⟩ = a i + (j : ℤ))).card := by
  classical
  have hsub : (univ : Finset (Fin k)) ⊆
      ((univ.filter (fun i : Fin k => ¬ (i.val + 1 < k))) ∪
        (univ.filter (fun i : Fin k => a i < ((2 ^ C : ℕ) : ℤ)))) ∪
      ((univ.filter (fun i : Fin k => ∃ h : i.val + 1 < k, a i + K < a ⟨i.val + 1, h⟩)) ∪
        (Finset.Icc 1 K).biUnion (fun j => univ.filter (fun i : Fin k =>
          ((2 ^ C : ℕ) : ℤ) ≤ a i ∧ ∃ h : i.val + 1 < k, a ⟨i.val + 1, h⟩ = a i + (j : ℤ)))) := by
    intro i _
    by_cases h : i.val + 1 < k
    · have hlt : a i < a ⟨i.val + 1, h⟩ := hm (show i < ⟨i.val + 1, h⟩ from by
        rw [Fin.lt_def]; simp)
      by_cases hbig : a i + K < a ⟨i.val + 1, h⟩
      · apply mem_union_right; apply mem_union_left
        rw [mem_filter]; exact ⟨mem_univ _, h, hbig⟩
      · by_cases hlow : a i < ((2 ^ C : ℕ) : ℤ)
        · apply mem_union_left; apply mem_union_right
          rw [mem_filter]; exact ⟨mem_univ _, hlow⟩
        · apply mem_union_right; apply mem_union_right
          rw [mem_biUnion]
          refine ⟨(a ⟨i.val + 1, h⟩ - a i).toNat, ?_, ?_⟩
          · rw [mem_Icc]; constructor <;> omega
          · rw [mem_filter]
            refine ⟨mem_univ _, by omega, h, ?_⟩
            have : (((a ⟨i.val + 1, h⟩ - a i).toNat : ℕ) : ℤ) = a ⟨i.val + 1, h⟩ - a i :=
              Int.toNat_of_nonneg (by omega)
            rw [this]; ring
    · apply mem_union_left; apply mem_union_left
      rw [mem_filter]; exact ⟨mem_univ _, h⟩
  have hlast : (univ.filter (fun i : Fin k => ¬ (i.val + 1 < k))).card ≤ 1 := by
    rw [card_le_one]
    intro x hx y hy
    rw [mem_filter] at hx hy
    ext; omega
  have hlow := low_card a hm.injective (fun i => (hr i).1) (2 ^ C)
  have hbig := big_card a hm hK hr
  have h0 := card_le_card hsub
  rw [card_univ, Fintype.card_fin] at h0
  have hu1 := card_union_le
    ((univ.filter (fun i : Fin k => ¬ (i.val + 1 < k))) ∪
        (univ.filter (fun i : Fin k => a i < ((2 ^ C : ℕ) : ℤ))))
    ((univ.filter (fun i : Fin k => ∃ h : i.val + 1 < k, a i + K < a ⟨i.val + 1, h⟩)) ∪
        (Finset.Icc 1 K).biUnion (fun j => univ.filter (fun i : Fin k =>
          ((2 ^ C : ℕ) : ℤ) ≤ a i ∧ ∃ h : i.val + 1 < k, a ⟨i.val + 1, h⟩ = a i + (j : ℤ))))
  have hu2 := card_union_le (univ.filter (fun i : Fin k => ¬ (i.val + 1 < k)))
        (univ.filter (fun i : Fin k => a i < ((2 ^ C : ℕ) : ℤ)))
  have hu3 := card_union_le
    (univ.filter (fun i : Fin k => ∃ h : i.val + 1 < k, a i + K < a ⟨i.val + 1, h⟩))
    ((Finset.Icc 1 K).biUnion (fun j => univ.filter (fun i : Fin k =>
          ((2 ^ C : ℕ) : ℤ) ≤ a i ∧ ∃ h : i.val + 1 < k, a ⟨i.val + 1, h⟩ = a i + (j : ℤ))))
  have hu4 := card_biUnion_le (s := Finset.Icc 1 K) (t := fun j => univ.filter (fun i : Fin k =>
          ((2 ^ C : ℕ) : ℤ) ≤ a i ∧ ∃ h : i.val + 1 < k, a ⟨i.val + 1, h⟩ = a i + (j : ℤ)))

  omega

open Filter Asymptotics in
theorem main : H1 → H2 → type_of% @Erdos357.erdos_357.parts.i := by
  intro h1 h2
  have hall : ∀ j : ℕ, 1 ≤ j → ∀ ε : ℝ, 0 < ε → ∃ C : ℕ, ∀ c : ℕ, C ≤ c →
      ∀ (k : ℕ) (a : Fin k → ℤ), StrictMono a → Erdos357.HasDistinctSums a →
      ((univ.filter (fun i : Fin k => (c : ℤ) ≤ a i ∧ a i < 2 * (c : ℤ) ∧
        ∃ h : i.val + 1 < k, a ⟨i.val + 1, h⟩ = a i + (j : ℤ))).card : ℝ) ≤ ε * c := by
    intro j hj ε hε
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · obtain rfl : j = 1 := by omega
      obtain ⟨C, hC⟩ := h1 ε hε
      refine ⟨C, fun c hc k a hm hd => ?_⟩
      have := hC c hc k a hm hd
      simpa using this
    · exact h2 j hj2 ε hε
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  set K : ℕ := ⌈3 / ε⌉₊ + 1 with hKdef
  have hK1 : 1 ≤ K := by omega
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
  have hK3 : 3 / ε ≤ (K : ℝ) := by
    have := Nat.le_ceil (3 / ε)
    have : ((⌈3 / ε⌉₊ : ℕ) : ℝ) ≤ K := by exact_mod_cast (by omega : ⌈3 / ε⌉₊ ≤ K)
    linarith
  set ε' : ℝ := ε / (6 * K) with hε'
  have hε'pos : 0 < ε' := by positivity
  have hex : ∀ j : ℕ, ∃ C : ℕ, ∀ c : ℕ, C ≤ c →
      ∀ (k : ℕ) (a : Fin k → ℤ), StrictMono a → Erdos357.HasDistinctSums a →
      ((univ.filter (fun i : Fin k => (c : ℤ) ≤ a i ∧ a i < 2 * (c : ℤ) ∧
        ∃ h : i.val + 1 < k, a ⟨i.val + 1, h⟩ = a i + (j : ℤ))).card : ℝ) ≤ ε' * c := by
    intro j
    by_cases hj : 1 ≤ j
    · exact hall j hj ε' hε'pos
    · obtain rfl : j = 0 := by omega
      refine ⟨0, fun c _ k a hm _ => ?_⟩
      have hempty : (univ.filter (fun i : Fin k => (c : ℤ) ≤ a i ∧ a i < 2 * (c : ℤ) ∧
          ∃ h : i.val + 1 < k, a ⟨i.val + 1, h⟩ = a i + ((0 : ℕ) : ℤ))) = ∅ := by
        rw [filter_eq_empty_iff]
        rintro i _ ⟨_, _, h, heq⟩
        have hlt : a i < a ⟨i.val + 1, h⟩ := hm (show i < ⟨i.val + 1, h⟩ from by
          rw [Fin.lt_def]; simp)
        simp at heq
        omega
      rw [hempty, card_empty, Nat.cast_zero]
      positivity
  choose Cf hCf using hex
  set C : ℕ := ∑ j ∈ range (K + 1), Cf j with hCdef
  have hCj : ∀ j ∈ Finset.Icc 1 K, Cf j ≤ C := by
    intro j hj
    rw [mem_Icc] at hj
    exact single_le_sum (f := Cf) (fun _ _ => Nat.zero_le _) (mem_range.mpr (by omega))
  filter_upwards [eventually_ge_atTop ⌈3 * (2 + (2 : ℝ) ^ C) / ε⌉₊] with n hn
  rw [Real.norm_natCast, Real.norm_natCast]
  have hnR : 3 * (2 + (2 : ℝ) ^ C) / ε ≤ n := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  have hsmall : 2 + (2 : ℝ) ^ C ≤ ε * n / 3 := by
    rw [div_le_iff₀ hε] at hnR
    linarith
  have bound : ∀ (k : ℕ) (a : Fin k → ℤ), Set.range a ⊆ Set.Icc 1 (n : ℤ) → StrictMono a →
      Erdos357.HasDistinctSums a → (k : ℝ) ≤ ε * n := by
    intro k a hra hm hd
    have hr : ∀ i, 1 ≤ a i ∧ a i ≤ n := fun i => hra ⟨i, rfl⟩
    have hc := count_le (C := C) a hm hK1 hr
    have hT : ∀ j ∈ Finset.Icc 1 K,
        ((univ.filter (fun i : Fin k => ((2 ^ C : ℕ) : ℤ) ≤ a i ∧
          ∃ h : i.val + 1 < k, a ⟨i.val + 1, h⟩ = a i + (j : ℤ))).card : ℝ) ≤ ε' * (2 * n) := by
      intro j hj
      apply block_card a hr ε' hε'pos.le
      intro c hc
      have hj1 : 1 ≤ j := (mem_Icc.mp hj).1
      exact hCf j c (le_trans (hCj j hj) hc) k a hm hd
    have hsumT : (∑ j ∈ Finset.Icc 1 K, ((univ.filter (fun i : Fin k => ((2 ^ C : ℕ) : ℤ) ≤ a i ∧
          ∃ h : i.val + 1 < k, a ⟨i.val + 1, h⟩ = a i + (j : ℤ))).card : ℝ)) ≤ K * (ε' * (2 * n)) := by
      have := sum_le_sum hT
      rw [sum_const, Nat.card_Icc, nsmul_eq_mul] at this
      simpa using this
    have hdiv : ((n / K : ℕ) : ℝ) ≤ ε * n / 3 := by
      have h1 : ((n / K : ℕ) : ℝ) ≤ (n : ℝ) / K := Nat.cast_div_le
      have h2 : (n : ℝ) / K ≤ ε * n / 3 := by
        rw [div_le_div_iff₀ hKpos (by norm_num)]
        have : 3 ≤ ε * K := by rw [div_le_iff₀ hε] at hK3; linarith
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      linarith
    have hKe : (K : ℝ) * (ε' * (2 * n)) = ε * n / 3 := by
      rw [hε']; field_simp; ring
    have hcR : (k : ℝ) ≤ 1 + (2 : ℝ) ^ C + ((n / K : ℕ) + 1) + ∑ j ∈ Finset.Icc 1 K,
        ((univ.filter (fun i : Fin k => ((2 ^ C : ℕ) : ℤ) ≤ a i ∧
          ∃ h : i.val + 1 < k, a ⟨i.val + 1, h⟩ = a i + (j : ℤ))).card : ℝ) := by
      exact_mod_cast hc
    linarith
  have hfle : Erdos357.f n ≤ ⌊ε * n⌋₊ := by
    unfold Erdos357.f
    apply csSup_le'
    rintro k ⟨a, hra, hm, hd⟩
    exact Nat.le_floor (bound k a hra hm hd)
  calc (Erdos357.f n : ℝ) ≤ (⌊ε * n⌋₊ : ℝ) := by exact_mod_cast hfle
    _ ≤ ε * n := Nat.floor_le (by positivity)

end OMA.R_Erdos357_erdos_357_parts_i_R1

import FormalConjectures.ErdosProblems.«39»

/-!
# Half-window adaptive-pruning dyadic block packing and sub-exponential additive code for Erdős Problem 39

This reduction strictly strengthens `Erdos39.erdos_39.R1` by proving inside `main`:
1. Compactness on `ℕ → Bool` (eliminating `R1.H2` unconditionally).
2. Exact adaptive short-difference pruning at threshold `|B j| / 2`, which retains at least half
   of every dyadic Sidon block `B j ⊆ [2^j, 2^(j+1))` with no asymptotic pruning budget and
   eliminates all cross-scale collisions for `(2^i * (4 * g j))^2 < 2^j` (i.e., all scales
   `i ≤ j/2 - log₂(4 * g j) - 1`, shrinking the collision window to the upper half `(j/2 - o(j), j)`).
3. Two-block core and coded-union Sidon gluing for any sub-exponential additive dyadic-label code.
4. Simultaneous multi-exponent dyadic-to-`IsBigO` transfer giving `N^(1/2 - ε) =O |Icc 1 N ∩ A|`
   for all `ε > 0` at once.

The remaining open problem splits cleanly into two independent pure-`ℕ` hypotheses:
- `H1`: Half-window nearby-scale dyadic Sidon blocks with arbitrary sub-exponential loss `g`.
- `H2`: A sub-exponential additive code `E` recovering `a + b` and `{Nat.log 2 a, Nat.log 2 b}`
  from `E a + E b`.
-/

-- Credit: @sanchan

namespace OMA.R_Erdos39_erdos_39_R2

open Filter Set Asymptotics
open scoped Topology

/- ### Part 1: Compactness on Boolean sequences -/

lemma closed_prefix_condition (n : ℕ) (P : (ℕ → Bool) → Prop)
    (hP : ∀ f g, (∀ i ≤ n, f i = g i) → P f → P g) : IsClosed {f | P f} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro f hf
  have hagree : ∀ᶠ g in 𝓝 f, ∀ i ∈ Finset.range (n + 1), g i = f i := by
    refine (eventually_all_finset _).mpr fun i _ => ?_
    have hopen : IsOpen ((fun g : ℕ → Bool => g i) ⁻¹' {f i}) :=
      (isOpen_discrete _).preimage (continuous_apply i)
    exact hopen.mem_nhds (by simp)
  exact hagree.mono fun g hg hPg => hf (hP g f
    (fun i hi => hg i (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))) hPg)

lemma compact_prefix_conditions (P : ℕ → (ℕ → Bool) → Prop)
    (hloc : ∀ n f g, (∀ i ≤ n, f i = g i) → P n f → P n g)
    (hfin : ∀ N, ∃ f, ∀ n ≤ N, P n f) : ∃ f, ∀ n, P n f := by
  classical
  let C (n : ℕ) : Set (ℕ → Bool) := {f | P n f}
  have hnonempty := (isCompact_univ : IsCompact (univ : Set (ℕ → Bool))).inter_iInter_nonempty C
    (fun n => closed_prefix_condition n (P n) (hloc n)) ?_
  · obtain ⟨f, _, hf⟩ := hnonempty
    exact ⟨f, mem_iInter.mp hf⟩
  · intro u
    obtain ⟨N, hN⟩ := (u.finite_toSet.bddAbove : BddAbove (u : Set ℕ))
    obtain ⟨f, hf⟩ := hfin N
    exact ⟨f, mem_univ _, mem_iInter₂.mpr fun n hn => hf n (hN hn)⟩

lemma sidon_of_multi_dyadic_witnesses (M : ℕ → ℕ)
    (h : ∀ N : ℕ, ∃ S : Set ℕ, S ⊆ Icc 1 (2 ^ N) ∧ IsSidon S ∧
      ∀ k ≥ 1, ∀ m, M k ≤ m → m ≤ N →
        2 ^ ((k - 1) * m) ≤ (Icc 1 (2 ^ m) ∩ S).ncard ^ (2 * k)) :
    ∃ A : Set ℕ, IsSidon A ∧
      ∀ k ≥ 1, ∀ m ≥ M k, 2 ^ ((k - 1) * m) ≤ (Icc 1 (2 ^ m) ∩ A).ncard ^ (2 * k) := by
  classical
  let cut (f : ℕ → Bool) (n : ℕ) : Set ℕ := Icc 1 n ∩ {a | f a = true}
  let P (n : ℕ) (f : ℕ → Bool) : Prop :=
    IsSidon (cut f n) ∧
      ∀ k ≥ 1, ∀ m, M k ≤ m → 2 ^ m ≤ n →
        2 ^ ((k - 1) * m) ≤ (Icc 1 (2 ^ m) ∩ cut f n).ncard ^ (2 * k)
  obtain ⟨f, hf⟩ : ∃ f, ∀ n, P n f := by
    apply compact_prefix_conditions P
    · intro n f g hagree hpf
      have hcut : cut f n = cut g n := by
        ext a
        constructor
        · rintro ⟨hn, ha⟩
          exact ⟨hn, (hagree a hn.2).symm.trans ha⟩
        · rintro ⟨hn, ha⟩
          exact ⟨hn, (hagree a hn.2).trans ha⟩
      simpa only [P, hcut] using hpf
    · intro N
      obtain ⟨S, _, hSidon, hcount⟩ := h N
      let f : ℕ → Bool := fun a => decide (a ∈ S)
      refine ⟨f, fun n hn => ?_⟩
      have hcut : cut f n = Icc 1 n ∩ S := by
        ext a; simp [cut, f]
      dsimp only [P]
      rw [hcut]
      refine ⟨hSidon.subset inter_subset_right, fun k hk m hMm hm2 => ?_⟩
      have hinter : Icc 1 (2 ^ m) ∩ (Icc 1 n ∩ S) = Icc 1 (2 ^ m) ∩ S := by
        rw [← inter_assoc, inter_eq_left.mpr (Icc_subset_Icc_right hm2)]
      rw [hinter]
      have hle : (2 : ℕ) ^ m ≤ 2 ^ N := hm2.trans (hn.trans N.lt_two_pow_self.le)
      have hmN : m ≤ N := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hle
      exact hcount k hk m hMm hmN
  let A : Set ℕ := Ici 1 ∩ {a | f a = true}
  have hcut (n : ℕ) : Icc 1 n ∩ A = cut f n := by
    dsimp only [A, cut]
    rw [← inter_assoc, inter_eq_left.mpr Icc_subset_Ici_self]
  refine ⟨A, ?_, fun k hk m hMm => ?_⟩
  · intro a ha b hb c hc e he hsum
    let n := a + b + c + e
    have hm (x : ℕ) (hx : x ∈ A) (hxn : x ≤ n) : x ∈ cut f n := by
      rw [← hcut]
      exact ⟨⟨hx.1, hxn⟩, hx⟩
    exact (hf n).1 a (hm a ha (by dsimp [n]; omega)) b (hm b hb (by dsimp [n]; omega))
      c (hm c hc (by dsimp [n]; omega)) e (hm e he (by dsimp [n]; omega)) hsum
  · have hcount := (hf (2 ^ m)).2 k hk m hMm le_rfl
    have hinter : Icc 1 (2 ^ m) ∩ cut f (2 ^ m) = Icc 1 (2 ^ m) ∩ A := by
      rw [← hcut, ← inter_assoc, inter_self]
    rwa [hinter] at hcount

/- ### Part 2: Simultaneous multi-exponent dyadic-to-BigO transfer -/

lemma infinite_of_multi_dyadic (A : Set ℕ) (M : ℕ → ℕ)
    (h : ∀ k ≥ 1, ∀ m ≥ M k, 2 ^ ((k - 1) * m) ≤ (Icc 1 (2 ^ m) ∩ A).ncard ^ (2 * k)) :
    A.Infinite := by
  intro hfin
  let c : ℕ := A.ncard
  let m : ℕ := max (M 2) (c ^ 4 + 1)
  have hmM : M 2 ≤ m := le_max_left _ _
  have hm_big : c ^ 4 < 2 ^ m := lt_of_lt_of_le (by dsimp [m]; omega) m.lt_two_pow_self.le
  have h2 := h 2 (by norm_num) m hmM
  have hcard : (Icc 1 (2 ^ m) ∩ A).ncard ≤ c := Set.ncard_le_ncard inter_subset_right hfin
  have hpow : (Icc 1 (2 ^ m) ∩ A).ncard ^ 4 ≤ c ^ 4 := Nat.pow_le_pow_left hcard 4
  have h1 : 2 ^ m ≤ (Icc 1 (2 ^ m) ∩ A).ncard ^ 4 := by
    simpa only [show (2 - 1) * m = m by omega, show 2 * 2 = 4 by norm_num] using h2
  omega

lemma bigO_of_multi_dyadic (A : Set ℕ) (M : ℕ → ℕ)
    (h : ∀ k ≥ 1, ∀ m ≥ M k, 2 ^ ((k - 1) * m) ≤ (Icc 1 (2 ^ m) ∩ A).ncard ^ (2 * k)) :
    ∀ ε > (0 : ℝ), (· ^ (1 / 2 - ε) : ℕ → ℝ) =O[atTop] fun N => ((Icc 1 N ∩ A).ncard : ℝ) := by
  intro ε hε
  by_cases hhalf : (1 / 2 : ℝ) ≤ ε
  · refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (2 ^ M 2)] with N hN
    have hN1 : 1 ≤ N := le_trans (Nat.one_le_two_pow) hN
    have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hrpow_nn : 0 ≤ (N : ℝ) ^ (1 / 2 - ε) := Real.rpow_nonneg (by positivity) _
    have hrpow_le1 : (N : ℝ) ^ (1 / 2 - ε) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hN1R (by linarith)
    have hcount_ge1 : 1 ≤ (Icc 1 N ∩ A).ncard := by
      have h2 := h 2 (by norm_num) (M 2) le_rfl
      have hsub : Icc 1 (2 ^ M 2) ∩ A ⊆ Icc 1 N ∩ A :=
        inter_subset_inter_left A (Icc_subset_Icc_right hN)
      have hmono := Set.ncard_le_ncard hsub ((finite_Icc 1 N).subset inter_subset_left)
      have hpos : 0 < (Icc 1 (2 ^ M 2) ∩ A).ncard ^ 4 :=
        lt_of_lt_of_le (by positivity : 0 < 2 ^ ((2 - 1) * M 2)) h2
      have hpos1 : 0 < (Icc 1 (2 ^ M 2) ∩ A).ncard := by
        by_contra h0
        have heq : (Icc 1 (2 ^ M 2) ∩ A).ncard = 0 := by omega
        rw [heq] at hpos; norm_num at hpos
      omega
    have hcountR : (1 : ℝ) ≤ ((Icc 1 N ∩ A).ncard : ℝ) := by exact_mod_cast hcount_ge1
    rw [Real.norm_of_nonneg hrpow_nn, Real.norm_natCast, one_mul]
    linarith
  · push Not at hhalf
    obtain ⟨k0, hk0⟩ := exists_nat_gt (1 / (2 * ε))
    let k : ℕ := max 2 k0
    have hk2 : 2 ≤ k := le_max_left _ _
    have hk1 : 1 ≤ k := by omega
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
    have hk_gt : 1 / (2 * ε) < (k : ℝ) := lt_of_lt_of_le hk0 (by exact_mod_cast le_max_right 2 k0)
    have hinv_le : 1 / (2 * (k : ℝ)) ≤ ε := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (k : ℝ))]
      have h1 : 1 < (k : ℝ) * (2 * ε) := (div_lt_iff₀ (by positivity)).mp hk_gt
      linarith
    have hexp_le : 1 / 2 - ε ≤ ((k - 1 : ℕ) : ℝ) / (2 * (k : ℝ)) := by
      have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub hk1, Nat.cast_one]
      rw [hcast, sub_div, show (k : ℝ) / (2 * (k : ℝ)) = 1 / 2 by field_simp [hk_pos.ne']]
      linarith
    have hexp_pos : 0 < 1 / 2 - ε := by linarith
    have hfrac_le1 : ((k - 1 : ℕ) : ℝ) / (2 * (k : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity : (0 : ℝ) < 2 * (k : ℝ))]
      have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub hk1, Nat.cast_one]
      linarith
    refine Asymptotics.IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop (2 ^ M k)] with N hN
    have hN1 : 1 ≤ N := le_trans Nat.one_le_two_pow hN
    have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    set m : ℕ := Nat.log 2 N
    have hmM : M k ≤ m := Nat.le_log_of_pow_le (by decide) hN
    have hlo : 2 ^ m ≤ N := Nat.pow_log_le_self 2 (by omega)
    have hhi : N ≤ 2 * 2 ^ m := by
      have hlt : N < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by decide : 1 < 2) N
      rw [pow_succ] at hlt
      omega
    have hsub : Icc 1 (2 ^ m) ∩ A ⊆ Icc 1 N ∩ A :=
      inter_subset_inter_left A (Icc_subset_Icc_right hlo)
    have hmono : (Icc 1 (2 ^ m) ∩ A).ncard ≤ (Icc 1 N ∩ A).ncard :=
      Set.ncard_le_ncard hsub ((finite_Icc 1 N).subset inter_subset_left)
    have hdyad := h k hk1 m hmM
    let c : ℝ := ((Icc 1 (2 ^ m) ∩ A).ncard : ℝ)
    have hc_nn : 0 ≤ c := Nat.cast_nonneg _
    have hrpow_dyad : ((2 : ℝ) ^ m) ^ (((k - 1 : ℕ) : ℝ) / (2 * (k : ℝ))) ≤ c := by
      have hpow_le : (((2 : ℝ) ^ m) ^ (((k - 1 : ℕ) : ℝ) / (2 * (k : ℝ)))) ^ (2 * k) ≤ c ^ (2 * k) := by
        rw [← Real.rpow_natCast (((2 : ℝ) ^ m) ^ _), ← Real.rpow_mul (by positivity)]
        have hmul' : (((k - 1 : ℕ) : ℝ) / (2 * (k : ℝ))) * ((2 * k : ℕ) : ℝ) = ((k - 1 : ℕ) : ℝ) := by
          push_cast; field_simp [hk_pos.ne']
        rw [hmul', Real.rpow_natCast, ← pow_mul, mul_comm m (k - 1)]
        dsimp only [c]
        exact_mod_cast hdyad
      exact le_of_pow_le_pow_left₀ (by omega : 2 * k ≠ 0) hc_nn hpow_le
    have h2pow : (2 : ℝ) ^ (((k - 1 : ℕ) : ℝ) / (2 * (k : ℝ))) ≤ 2 := by
      calc (2 : ℝ) ^ (((k - 1 : ℕ) : ℝ) / (2 * (k : ℝ)))
          ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hfrac_le1
        _ = 2 := Real.rpow_one 2
    have hstep1 : (N : ℝ) ^ (1 / 2 - ε) ≤ (N : ℝ) ^ (((k - 1 : ℕ) : ℝ) / (2 * (k : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le hN1R hexp_le
    have hstep2 : (N : ℝ) ^ (((k - 1 : ℕ) : ℝ) / (2 * (k : ℝ))) ≤
        (2 * (2 : ℝ) ^ m) ^ (((k - 1 : ℕ) : ℝ) / (2 * (k : ℝ))) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hhi) (by linarith)
    have hstep3 : (2 * (2 : ℝ) ^ m) ^ (((k - 1 : ℕ) : ℝ) / (2 * (k : ℝ))) ≤ 2 * c := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
      exact mul_le_mul h2pow hrpow_dyad (Real.rpow_nonneg (by positivity) _) (by norm_num)
    have hstep4 : c ≤ ((Icc 1 N ∩ A).ncard : ℝ) := by dsimp only [c]; exact_mod_cast hmono
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _), Real.norm_natCast]
    linarith

/- ### Part 3: Adaptive short-difference pruning (half-window reduction) -/

lemma sidon_positive_difference_unique (S : Finset ℕ) (hS : IsSidon (S : Set ℕ))
    {a b u v : ℕ} (ha : a ∈ S) (hb : b ∈ S) (hu : u ∈ S) (hv : v ∈ S)
    (hba : b < a) (hvu : v < u) (heq : a - b = u - v) : a = u ∧ b = v := by
  have hadd : a + v = u + b := by omega
  rcases hS a ha u hu v hv b hb hadd with h | h
  · exact ⟨h.1, h.2.symm⟩
  · omega

lemma prune_short_differences (S : Finset ℕ) (hS : IsSidon (S : Set ℕ)) (t : ℕ) :
    ∃ T ⊆ S, S.card ≤ T.card + t ∧ ∀ a ∈ T, ∀ b ∈ T, b < a → t ≤ a - b := by
  let bad := (S.product S).filter fun p => p.2 < p.1 ∧ p.1 - p.2 < t
  let drop := bad.image Prod.fst
  have hbad : bad.card ≤ t := by
    rw [← Finset.card_range t]
    apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.1 - p.2)
    · intro p hp
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2.2
    · intro p hp q hq heq
      obtain ⟨hab, hp₁, _⟩ := Finset.mem_filter.mp hp
      obtain ⟨huv, hq₁, _⟩ := Finset.mem_filter.mp hq
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
      obtain ⟨hu, hv⟩ := Finset.mem_product.mp huv
      obtain ⟨h₁, h₂⟩ := sidon_positive_difference_unique S hS ha hb hu hv hp₁ hq₁ heq
      exact Prod.ext h₁ h₂
  have hsubset : drop ⊆ S := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  have hdrop : drop.card ≤ t := Finset.card_image_le.trans hbad
  have hsc := Finset.card_sdiff_add_card_eq_card hsubset
  refine ⟨S \ drop, Finset.sdiff_subset, by omega, ?_⟩
  intro a ha b hb hba
  by_contra! hlt
  obtain ⟨haS, haD⟩ := Finset.mem_sdiff.mp ha
  have hbS := (Finset.mem_sdiff.mp hb).1
  have hp : (a, b) ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨haS, hbS⟩, hba, hlt⟩
  exact haD (Finset.mem_image.mpr ⟨(a, b), hp, rfl⟩)

lemma prune_half_window_collisions (g : ℕ → ℕ) (J₀ N : ℕ)
    (hg1 : ∀ j, 1 ≤ g j)
    (B : ℕ → Finset ℕ) (hpos : ∀ j, B j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1)))
    (hS : ∀ j, IsSidon (B j : Set ℕ))
    (hcount : ∀ j, J₀ ≤ j → j ≤ N → 2 ^ j ≤ (B j).card ^ 2 * (g j) ^ 2)
    (hnear : ∀ i j, i < j → 2 ^ j ≤ (2 ^ i * (4 * g j)) ^ 2 →
      ∀ a ∈ B i, ∀ b ∈ B i, ∀ u ∈ B j, ∀ v ∈ B j, b < a → v < u → a - b ≠ u - v) :
    ∃ C : ℕ → Finset ℕ,
      (∀ j, C j ⊆ B j) ∧
      (∀ j, J₀ ≤ j → j ≤ N → 2 ^ j ≤ (C j).card ^ 2 * (2 * g j) ^ 2) ∧
      ∀ i j, i < j → ∀ a ∈ C i, ∀ b ∈ C i, ∀ u ∈ C j, ∀ v ∈ C j,
        b < a → v < u → a - b ≠ u - v := by
  classical
  choose P hPsub hPcard hPsep using fun j =>
    prune_short_differences (B j) (hS j) ((B j).card / 2)
  let C : ℕ → Finset ℕ := fun j => if J₀ ≤ j ∧ j ≤ N then P j else ∅
  refine ⟨C, ?_, ?_, ?_⟩
  · intro j
    dsimp only [C]
    split_ifs
    · exact hPsub j
    · exact Finset.empty_subset _
  · intro j hJ hjN
    have hCj : C j = P j := if_pos ⟨hJ, hjN⟩
    rw [hCj]
    have hhalf : (B j).card ≤ 2 * (P j).card := by
      have := hPcard j; omega
    have hsq : (B j).card ^ 2 ≤ (2 * (P j).card) ^ 2 := Nat.pow_le_pow_left hhalf 2
    have hc := hcount j hJ hjN
    calc 2 ^ j ≤ (B j).card ^ 2 * (g j) ^ 2 := hc
      _ ≤ (2 * (P j).card) ^ 2 * (g j) ^ 2 := Nat.mul_le_mul_right _ hsq
      _ = (P j).card ^ 2 * (2 * g j) ^ 2 := by ring
  · intro i j hij a ha b hb u hu v hv hba hvu
    dsimp only [C] at ha hb hu hv
    by_cases hi : J₀ ≤ i ∧ i ≤ N
    · rw [if_pos hi] at ha hb
      by_cases hj : J₀ ≤ j ∧ j ≤ N
      · rw [if_pos hj] at hu hv
        by_cases hwin : 2 ^ j ≤ (2 ^ i * (4 * g j)) ^ 2
        · exact hnear i j hij hwin a (hPsub i ha) b (hPsub i hb) u (hPsub j hu) v (hPsub j hv) hba hvu
        · have hlt : (2 ^ i * (4 * g j)) ^ 2 < ((B j).card * g j) ^ 2 := by
            calc (2 ^ i * (4 * g j)) ^ 2 < 2 ^ j := by omega
              _ ≤ (B j).card ^ 2 * (g j) ^ 2 := hcount j hj.1 hj.2
              _ = ((B j).card * g j) ^ 2 := by ring
          have hlt1 : 2 ^ i * (4 * g j) < (B j).card * g j := by
            by_contra hge
            have hle : (B j).card * g j ≤ 2 ^ i * (4 * g j) := by omega
            have hsq := Nat.pow_le_pow_left hle 2
            omega
          have hgpos : 1 ≤ g j := hg1 j
          have h4lt : 4 * 2 ^ i < (B j).card := by nlinarith
          have hcap : 2 ^ i ≤ (B j).card / 2 := by omega
          have htop := (Finset.mem_Ico.mp (hpos i (hPsub i ha))).2
          have hbot := (Finset.mem_Ico.mp (hpos i (hPsub i hb))).1
          rw [pow_succ] at htop
          have hgap : a - b < 2 ^ i := by omega
          have hsep := hPsep j u hu v hv hvu
          omega
      · rw [if_neg hj] at hu
        exact absurd hu (Finset.notMem_empty _)
    · rw [if_neg hi] at ha
      exact absurd ha (Finset.notMem_empty _)

/- ### Part 4: Two-block core and coded-union Sidon gluing -/

lemma two_block_core (C : ℕ → Finset ℕ) (hS : ∀ j, IsSidon (C j : Set ℕ))
    (hcross : ∀ i j, i < j → ∀ a ∈ C i, ∀ b ∈ C i, ∀ u ∈ C j, ∀ v ∈ C j,
      b < a → v < u → a - b ≠ u - v)
    {p r a b u v : ℕ} (ha : a ∈ C p) (hb : b ∈ C r) (hu : u ∈ C p) (hv : v ∈ C r)
    (hs : a + b = u + v) : (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
  rcases lt_trichotomy p r with hpr | rfl | hpr
  · left
    rcases lt_trichotomy a u with h | h | h
    · exact (hcross p r hpr u hu a ha b hb v hv h (by omega) (by omega)).elim
    · exact ⟨h, by omega⟩
    · exact (hcross p r hpr a ha u hu v hv b hb h (by omega) (by omega)).elim
  · exact hS p a ha u hu b hb v hv hs
  · left
    rcases lt_trichotomy b v with h | h | h
    · exact (hcross r p hpr v hv b hb a ha u hu h (by omega) (by omega)).elim
    · exact ⟨by omega, h⟩
    · exact (hcross r p hpr b hb v hv u hu a ha h (by omega) (by omega)).elim

lemma coded_union_sidon (C : ℕ → Finset ℕ) (hpos : ∀ j, C j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1)))
    (hS : ∀ j, IsSidon (C j : Set ℕ))
    (hcross : ∀ i j, i < j → ∀ a ∈ C i, ∀ b ∈ C i, ∀ u ∈ C j, ∀ v ∈ C j,
      b < a → v < u → a - b ≠ u - v)
    (E : ℕ → ℕ)
    (hsum : ∀ a b u v, E a + E b = E u + E v →
      a + b = u + v ∧
        ((Nat.log 2 a = Nat.log 2 u ∧ Nat.log 2 b = Nat.log 2 v) ∨
         (Nat.log 2 a = Nat.log 2 v ∧ Nat.log 2 b = Nat.log 2 u)))
    (I : Finset ℕ) : IsSidon ((I.biUnion fun j => (C j).image E : Finset ℕ) : Set ℕ) := by
  have hlog : ∀ j a, a ∈ C j → Nat.log 2 a = j := fun j a ha =>
    Nat.log_eq_of_pow_le_of_lt_pow (Finset.mem_Ico.mp (hpos j ha)).1
      (Finset.mem_Ico.mp (hpos j ha)).2
  have hmem : ∀ x, x ∈ ((I.biUnion fun j => (C j).image E : Finset ℕ) : Set ℕ) →
      ∃ a, a ∈ C (Nat.log 2 a) ∧ E a = x := by
    intro x hx
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hx)
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hj
    exact ⟨a, by rw [hlog j a ha]; exact ha, rfl⟩
  intro x hx y hy z hz w hw hxz
  obtain ⟨a, ha, rfl⟩ := hmem x hx
  obtain ⟨u, hu, rfl⟩ := hmem y hy
  obtain ⟨b, hb, rfl⟩ := hmem z hz
  obtain ⟨v, hv, rfl⟩ := hmem w hw
  obtain ⟨hs, hl | hl⟩ := hsum a b u v hxz
  · rw [← hl.1] at hu
    rw [← hl.2] at hv
    rcases two_block_core C hS hcross ha hb hu hv hs with h | h
    · exact Or.inl ⟨by rw [h.1], by rw [h.2]⟩
    · exact Or.inr ⟨by rw [h.1], by rw [h.2]⟩
  · rw [← hl.1] at hv
    rw [← hl.2] at hu
    rcases two_block_core C hS hcross ha hb hv hu (by omega) with h | h
    · exact Or.inr ⟨by rw [h.1], by rw [h.2]⟩
    · exact Or.inl ⟨by rw [h.1], by rw [h.2]⟩

/- ### Part 5: Finite multi-exponent Sidon witnesses from sub-exponential blocks and code -/

lemma coded_multi_finite_witness (g : ℕ → ℕ) (J₀ : ℕ)
    (hg1 : ∀ j, 1 ≤ g j)
    (hg_sub : ∀ r ≥ 1, ∃ J, ∀ j ≥ J, (g j) ^ r ≤ 2 ^ j)
    (hB : ∀ N : ℕ, ∃ B : ℕ → Finset ℕ,
      (∀ j, B j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1))) ∧
      (∀ j, IsSidon (B j : Set ℕ)) ∧
      (∀ j, J₀ ≤ j → j ≤ N → 2 ^ j ≤ (B j).card ^ 2 * (g j) ^ 2) ∧
      ∀ i j, i < j → 2 ^ j ≤ (2 ^ i * (4 * g j)) ^ 2 →
        ∀ a ∈ B i, ∀ b ∈ B i, ∀ u ∈ B j, ∀ v ∈ B j, b < a → v < u → a - b ≠ u - v)
    (E : ℕ → ℕ) (h : ℕ → ℕ)
    (hh_sub : ∀ r ≥ 1, ∃ J, ∀ j ≥ J, (h j) ^ r ≤ 2 ^ j)
    (hsum : ∀ a b u v, E a + E b = E u + E v →
      a + b = u + v ∧
        ((Nat.log 2 a = Nat.log 2 u ∧ Nat.log 2 b = Nat.log 2 v) ∨
         (Nat.log 2 a = Nat.log 2 v ∧ Nat.log 2 b = Nat.log 2 u)))
    (hsize : ∀ j, ∀ a ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), 1 ≤ E a ∧ E a ≤ 2 ^ j * h j) :
    ∃ M : ℕ → ℕ, ∀ N : ℕ, ∃ S : Set ℕ, S ⊆ Icc 1 (2 ^ N) ∧ IsSidon S ∧
      ∀ k ≥ 1, ∀ m, M k ≤ m → m ≤ N →
        2 ^ ((k - 1) * m) ≤ (Icc 1 (2 ^ m) ∩ S).ncard ^ (2 * k) := by
  classical
  have hEinj : Function.Injective E := by
    intro a b hab
    have h1 := (hsum a a b b (by rw [hab])).1
    omega
  choose Jg hJg using fun k : ℕ => hg_sub (8 * max 1 k) (by omega)
  choose Jh hJh using fun k : ℕ => hh_sub (4 * max 1 k) (by omega)
  let M : ℕ → ℕ := fun k => 2 * max (max J₀ (max (Jh k) (Jg k))) (8 * max 1 k) + 8 * max 1 k + 4
  refine ⟨M, fun N => ?_⟩
  obtain ⟨B, hpos, hBS, hcounts, hnear⟩ := hB N
  obtain ⟨C, hCsub, hCcount, hcross⟩ :=
    prune_half_window_collisions g J₀ N hg1 B hpos hBS hcounts hnear
  have hCpos : ∀ j, C j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1)) := fun j => (hCsub j).trans (hpos j)
  have hCS : ∀ j, IsSidon (C j : Set ℕ) := fun j => (hBS j).subset (Finset.coe_subset.mpr (hCsub j))
  let I : Finset ℕ := (Finset.range (N + 1)).filter (fun j => 2 ^ j * h j ≤ 2 ^ N)
  let T : Finset ℕ := I.biUnion fun j => (C j).image E
  refine ⟨(T : Set ℕ), ?_, coded_union_sidon C hCpos hCS hcross E hsum I, ?_⟩
  · intro x hx
    obtain ⟨j, hj, hjx⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hx)
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hjx
    have h1 := hsize j a (hCpos j ha)
    exact ⟨h1.1, h1.2.trans (Finset.mem_filter.mp hj).2⟩
  · intro k hk m hMm hmN
    have hmaxk : max 1 k = k := max_eq_right hk
    let L0 : ℕ := max (max J₀ (max (Jh k) (Jg k))) (8 * k)
    have hMm' : 2 * L0 + 8 * k + 4 ≤ m := by
      dsimp only [M, L0] at hMm ⊢
      rwa [hmaxk] at hMm
    let t : ℕ := m / (4 * k) + 1
    let j : ℕ := m - t
    have ht_le : t ≤ m / 2 := by
      have h4 : 4 ≤ 4 * k := by omega
      have hdiv : m / (4 * k) ≤ m / 4 := Nat.div_le_div_left h4 (by omega)
      dsimp only [t]; omega
    have hjt : j + t = m := by dsimp only [j]; omega
    have hj_ge_L0 : L0 ≤ j := by dsimp only [j]; omega
    have hj_J0 : J₀ ≤ j := (le_trans (le_max_left _ _) (le_max_left _ _)).trans hj_ge_L0
    have hj_Jh : Jh k ≤ j :=
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)).trans hj_ge_L0
    have hj_Jg : Jg k ≤ j :=
      (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)).trans hj_ge_L0
    have hj_8k : 8 * k ≤ j := (le_max_right _ _).trans hj_ge_L0
    have hjm : j ≤ m := Nat.sub_le m t
    have hjN : j ≤ N := hjm.trans hmN
    have hm_lt_4kt : m < 4 * k * t := by
      dsimp only [t]
      have hdiv := Nat.lt_mul_div_succ m (show 0 < 4 * k by omega)
      linarith
    have h4kt_le : 4 * k * t ≤ m + 4 * k := by
      dsimp only [t]
      have hmul := Nat.mul_div_le m (4 * k)
      linarith
    have hh_le_2t : h j ≤ 2 ^ t := by
      have hhpow : (h j) ^ (4 * k) ≤ 2 ^ j := by
        have := hJh k j hj_Jh
        rwa [hmaxk] at this
      have hpow2 : (h j) ^ (4 * k) ≤ (2 ^ t) ^ (4 * k) := by
        rw [← pow_mul, mul_comm t (4 * k)]
        exact hhpow.trans (Nat.pow_le_pow_right (by decide) (by linarith only [hjm, hm_lt_4kt]))
      exact le_of_pow_le_pow_left₀ (by omega : 4 * k ≠ 0) (Nat.zero_le _) hpow2
    have hjm2 : 2 ^ j * h j ≤ 2 ^ m := by
      rw [← hjt, pow_add]
      exact Nat.mul_le_mul_left _ hh_le_2t
    have hjI : j ∈ I := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), hjm2.trans (Nat.pow_le_pow_right (by decide) hmN)⟩
    have hsub : (((C j).image E : Finset ℕ) : Set ℕ) ⊆ Icc 1 (2 ^ m) ∩ (T : Set ℕ) := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      have h1 := hsize j a (hCpos j ha)
      exact ⟨⟨h1.1, h1.2.trans hjm2⟩,
        Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨j, hjI, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩)⟩
    have hcard : (C j).card ≤ (Icc 1 (2 ^ m) ∩ (T : Set ℕ)).ncard := by
      have hle := Set.ncard_le_ncard hsub ((finite_Icc 1 (2 ^ m)).subset inter_subset_left)
      rwa [Set.ncard_coe_finset, Finset.card_image_of_injective _ hEinj] at hle
    let loss : ℕ := (2 * g j) ^ 2 * 2 ^ t
    have hloss_pow4 : (loss ^ k) ^ 4 ≤ (2 ^ m) ^ 4 := by
      have hgpow : (g j) ^ (8 * k) ≤ 2 ^ j := by
        have := hJg k j hj_Jg
        rwa [hmaxk] at this
      have h2pow : 2 ^ (8 * k) ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) hj_8k
      have h4km : 4 * k ≤ m := by linarith only [hMm']
      calc (loss ^ k) ^ 4 = loss ^ (4 * k) := by rw [← pow_mul, mul_comm k 4]
        _ = ((2 * g j) ^ 2) ^ (4 * k) * (2 ^ t) ^ (4 * k) := by dsimp only [loss]; rw [mul_pow]
        _ = 2 ^ (8 * k) * (g j) ^ (8 * k) * 2 ^ (4 * k * t) := by
            rw [← pow_mul, ← pow_mul, mul_pow, show 2 * (4 * k) = 8 * k by ring, mul_comm t (4 * k)]
        _ ≤ 2 ^ j * 2 ^ j * 2 ^ (4 * k * t) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul h2pow hgpow)
        _ = 2 ^ (j + j + 4 * k * t) := by rw [← pow_add, ← pow_add]
        _ ≤ 2 ^ (4 * m) := Nat.pow_le_pow_right (by decide) (by linarith only [hjm, h4kt_le, h4km])
        _ = (2 ^ m) ^ 4 := by rw [← pow_mul, mul_comm m 4]
    have hloss_k : loss ^ k ≤ 2 ^ m :=
      le_of_pow_le_pow_left₀ (by norm_num : 4 ≠ 0) (Nat.zero_le _) hloss_pow4
    have hstep : 2 ^ m ≤ (C j).card ^ 2 * loss := by
      calc 2 ^ m = 2 ^ j * 2 ^ t := by rw [← pow_add, hjt]
        _ ≤ ((C j).card ^ 2 * (2 * g j) ^ 2) * 2 ^ t :=
            Nat.mul_le_mul_right _ (hCcount j hj_J0 hjN)
        _ = (C j).card ^ 2 * loss := by dsimp only [loss]; ring
    have hstep_k : 2 ^ ((k - 1) * m) * 2 ^ m ≤ (C j).card ^ (2 * k) * 2 ^ m := by
      calc 2 ^ ((k - 1) * m) * 2 ^ m = 2 ^ (k * m) := by
            rw [← pow_add]
            congr 1
            have hksub : (k - 1) * m + m = k * m := by
              cases k with
              | zero => omega
              | succ k' => simp [Nat.succ_mul]
            exact hksub
        _ = (2 ^ m) ^ k := by rw [← pow_mul, mul_comm m k]
        _ ≤ ((C j).card ^ 2 * loss) ^ k := Nat.pow_le_pow_left hstep k
        _ = (C j).card ^ (2 * k) * loss ^ k := by rw [mul_pow, ← pow_mul]
        _ ≤ (C j).card ^ (2 * k) * 2 ^ m := Nat.mul_le_mul_left _ hloss_k
    have hCj_bound : 2 ^ ((k - 1) * m) ≤ (C j).card ^ (2 * k) :=
      Nat.le_of_mul_le_mul_right hstep_k (by positivity : 0 < 2 ^ m)
    exact hCj_bound.trans (Nat.pow_le_pow_left hcard (2 * k))

/- ### Hypotheses and Main Reduction -/

/-- Half-window nearby-scale dyadic Sidon blocks with any sub-exponential loss function `g`:
for every finite horizon `N`, Sidon blocks `B j ⊆ [2^j, 2^(j+1))` of size `≥ 2^(j/2) / g j`
whose positive differences avoid only blocks in the upper half-window
`2^j ≤ (2^i * (4 * g j))^2` (i.e., `i ≥ j/2 - log₂(4 * g j)`). -/
def H1 : Prop :=
  ∃ (g : ℕ → ℕ) (J₀ : ℕ),
    (∀ j, 1 ≤ g j) ∧
    (∀ r ≥ 1, ∃ J, ∀ j ≥ J, (g j) ^ r ≤ 2 ^ j) ∧
    ∀ N : ℕ, ∃ B : ℕ → Finset ℕ,
      (∀ j, B j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1))) ∧
      (∀ j, IsSidon (B j : Set ℕ)) ∧
      (∀ j, J₀ ≤ j → j ≤ N → 2 ^ j ≤ (B j).card ^ 2 * (g j) ^ 2) ∧
      ∀ i j, i < j → 2 ^ j ≤ (2 ^ i * (4 * g j)) ^ 2 →
        ∀ a ∈ B i, ∀ b ∈ B i, ∀ u ∈ B j, ∀ v ∈ B j, b < a → v < u → a - b ≠ u - v

/-- A sub-exponential additive code `E : ℕ → ℕ` whose pair sums recover both the original sum
`a + b` and the unordered pair of dyadic labels `{Nat.log 2 a, Nat.log 2 b}`, expanding each
dyadic block `[2^j, 2^(j+1))` by at most a sub-exponential factor `h j = 2^(o(j))`. -/
def H2 : Prop :=
  ∃ (E : ℕ → ℕ) (h : ℕ → ℕ),
    (∀ r ≥ 1, ∃ J, ∀ j ≥ J, (h j) ^ r ≤ 2 ^ j) ∧
    (∀ a b u v, E a + E b = E u + E v →
      a + b = u + v ∧
        ((Nat.log 2 a = Nat.log 2 u ∧ Nat.log 2 b = Nat.log 2 v) ∨
         (Nat.log 2 a = Nat.log 2 v ∧ Nat.log 2 b = Nat.log 2 u))) ∧
    ∀ j, ∀ a ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), 1 ≤ E a ∧ E a ≤ 2 ^ j * h j

theorem main : H1 → H2 → type_of% @Erdos39.erdos_39 := by
  intro h1 h2
  obtain ⟨g, J₀, hg1, hg_sub, hB⟩ := h1
  obtain ⟨E, h, hh_sub, hsum, hsize⟩ := h2
  obtain ⟨M, hfin⟩ := coded_multi_finite_witness g J₀ hg1 hg_sub hB E h hh_sub hsum hsize
  obtain ⟨A, hSidon, hcount⟩ := sidon_of_multi_dyadic_witnesses M hfin
  exact ⟨A, infinite_of_multi_dyadic A M hcount, hSidon, bigO_of_multi_dyadic A M hcount⟩

end OMA.R_Erdos39_erdos_39_R2

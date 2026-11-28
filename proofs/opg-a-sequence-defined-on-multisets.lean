import OMAStatements.S_opg_a_sequence_defined_on_multisets

namespace OPGMultisetProof

open OMA.S_opg_a_sequence_defined_on_multisets

private lemma count_map_val (S : Finset ℕ) (f : ℕ → ℕ) (x : ℕ) :
    Multiset.count x (S.val.map f) = (S.filter (fun y => f y = x)).card := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
      rw [Finset.insert_val_of_notMem has, Multiset.map_cons, Multiset.count_cons,
        Finset.filter_insert, ih]
      by_cases hfa : f a = x
      · have han : a ∉ s.filter (fun y => f y = x) := fun h => has (Finset.mem_filter.mp h).1
        rw [if_pos hfa, Finset.card_insert_of_notMem han, if_pos hfa.symm]
      · rw [if_neg hfa, if_neg (Ne.symm hfa), add_zero]

private lemma step_apply (f : ℕ →₀ ℕ) (x : ℕ) :
    step f x = (if x ∈ f.support then 1 else 0) + (f.support.filter (fun y => f y = x)).card := by
  unfold step
  rw [Multiset.toFinsupp_apply, Multiset.count_add, count_map_val]
  congr 1
  by_cases hx : x ∈ f.support
  · rw [if_pos hx]
    exact Multiset.count_eq_one_of_mem f.support.nodup hx
  · rw [if_neg hx]
    exact Multiset.count_eq_zero.mpr (by simpa using hx)

private lemma mem_step_support_iff (f : ℕ →₀ ℕ) (x : ℕ) :
    x ∈ (step f).support ↔ x ∈ f.support ∨ ∃ y ∈ f.support, f y = x := by
  rw [Finsupp.mem_support_iff, step_apply]
  by_cases hx : x ∈ f.support
  · simp [hx]
  · simp [hx, Finset.card_eq_zero, Finset.filter_eq_empty_iff]

private lemma support_subset_step (f : ℕ →₀ ℕ) : f.support ⊆ (step f).support := by
  intro x hx
  exact (mem_step_support_iff f x).mpr (Or.inl hx)

private lemma step_ne_zero {f : ℕ →₀ ℕ} (hf : f ≠ 0) : step f ≠ 0 := by
  intro h0
  have hsub := support_subset_step f
  rw [h0, Finsupp.support_zero, Finset.subset_empty, Finsupp.support_eq_empty] at hsub
  exact hf hsub

private lemma zero_notMem_step {f : ℕ →₀ ℕ} (h0 : 0 ∉ f.support) : 0 ∉ (step f).support := by
  rw [mem_step_support_iff]
  rintro (h | ⟨y, hy, hfy⟩)
  · exact h0 h
  · exact Finsupp.mem_support_iff.mp hy hfy

private lemma step_iter_ne_zero {f : ℕ →₀ ℕ} (hf : f ≠ 0) : ∀ n, step^[n] f ≠ 0
  | 0 => hf
  | n + 1 => by
      rw [Function.iterate_succ_apply']
      exact step_ne_zero (step_iter_ne_zero hf n)

private lemma step_iter_zero_notMem {f : ℕ →₀ ℕ} (h0 : 0 ∉ f.support) :
    ∀ n, 0 ∉ (step^[n] f).support
  | 0 => h0
  | n + 1 => by
      rw [Function.iterate_succ_apply']
      exact zero_notMem_step (step_iter_zero_notMem h0 n)

private lemma support_subset_iter (f : ℕ →₀ ℕ) :
    ∀ m n, m ≤ n → (step^[m] f).support ⊆ (step^[n] f).support := by
  intro m n hmn
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  clear hmn
  induction d with
  | zero => exact Finset.Subset.refl _
  | succ d ih =>
      refine Finset.Subset.trans ih ?_
      rw [← Nat.add_assoc, Function.iterate_succ_apply']
      exact support_subset_step _

private lemma step_sum (f : ℕ →₀ ℕ) : ∑ x ∈ (step f).support, step f x = 2 * f.support.card := by
  have hrew : ∀ x ∈ (step f).support,
      step f x = (if x ∈ f.support then 1 else 0) + (f.support.filter (fun y => f y = x)).card :=
    fun x _ => step_apply f x
  rw [Finset.sum_congr rfl hrew, Finset.sum_add_distrib]
  have h1 : ∑ x ∈ (step f).support, (if x ∈ f.support then 1 else 0) = f.support.card := by
    rw [← Finset.card_filter]
    have hf : (step f).support.filter (fun x => x ∈ f.support) = f.support := by
      ext x
      simp only [Finset.mem_filter, and_iff_right_iff_imp]
      exact fun hx => support_subset_step f hx
    rw [hf]
  have h2 : ∑ x ∈ (step f).support, (f.support.filter (fun y => f y = x)).card = f.support.card := by
    symm
    refine Finset.card_eq_sum_card_fiberwise ?_
    intro y hy
    exact (mem_step_support_iff f (f y)).mpr (Or.inr ⟨y, hy, rfl⟩)
  rw [h1, h2]
  omega

private lemma sum_pos_finset_ge (T : Finset ℕ) (h0 : 0 ∉ T) :
    T.card * (T.card + 1) ≤ 2 * ∑ v ∈ T, v := by
  induction T using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
      have has : a ∉ s := fun h => lt_irrefl a (ha a h)
      have h0s : 0 ∉ s := fun h => h0 (Finset.mem_insert_of_mem h)
      have ha0 : 0 < a := Nat.pos_of_ne_zero (fun h => h0 (h ▸ Finset.mem_insert_self a s))
      have hsub : s ⊆ Finset.Ico 1 a := by
        intro b hb
        rw [Finset.mem_Ico]
        exact ⟨Nat.pos_of_ne_zero (fun h => h0s (h ▸ hb)), ha b hb⟩
      have hcard : s.card ≤ a - 1 := by
        have hle := Finset.card_le_card hsub
        simpa using hle
      have ha1 : s.card + 1 ≤ a := by omega
      have hih := ih h0s
      rw [Finset.card_insert_of_notMem has, Finset.sum_insert has]
      nlinarith

private lemma val_le_of_step3 {g : ℕ →₀ ℕ} (hg : g ≠ 0) (h0 : 0 ∉ g.support) :
    ∀ x ∈ (step^[3] g).support, step^[3] g x ≤ max (step^[3] g).support.card 7 := by
  set g1 := step g
  set g2 := step g1
  set g3 := step g2
  change ∀ x ∈ g3.support, g3 x ≤ max g3.support.card 7
  have hg1 : g1 ≠ 0 := step_ne_zero hg
  have hg2 : g2 ≠ 0 := step_ne_zero hg1
  have h01 : 0 ∉ g1.support := zero_notMem_step h0
  have h02 : 0 ∉ g2.support := zero_notMem_step h01
  intro x hx
  by_cases hle : g3 x ≤ g3.support.card
  · exact le_trans hle (le_max_left _ _)
  · have hgt : g3.support.card + 1 ≤ g3 x := by omega
    have hsum3 : ∑ y ∈ g3.support, g3 y = 2 * g2.support.card := step_sum g2
    have hsplit : g3 x + ∑ y ∈ g3.support.erase x, g3 y = 2 * g2.support.card := by
      rw [Finset.add_sum_erase _ _ hx, hsum3]
    have herase_le : (g3.support.erase x).card ≤ ∑ y ∈ g3.support.erase x, g3 y := by
      have h1 : (g3.support.erase x).card = ∑ _y ∈ g3.support.erase x, 1 := by simp
      rw [h1]
      refine Finset.sum_le_sum fun y hy => ?_
      have hy3 : y ∈ g3.support := Finset.mem_of_mem_erase hy
      have hne : g3 y ≠ 0 := Finsupp.mem_support_iff.mp hy3
      omega
    have herase_card : (g3.support.erase x).card = g3.support.card - 1 :=
      Finset.card_erase_of_mem hx
    have hcard_pos3 : 1 ≤ g3.support.card := Finset.card_pos.mpr ⟨x, hx⟩
    have hsub23 : g2.support ⊆ g3.support := support_subset_step g2
    have hcard23 : g2.support.card ≤ g3.support.card := Finset.card_le_card hsub23
    have hcard_eq23 : g2.support.card = g3.support.card := by omega
    have hg3x : g3 x = g3.support.card + 1 := by omega
    have hsupp23 : g2.support = g3.support :=
      Finset.eq_of_subset_of_card_le hsub23 (by omega)
    have hx2 : x ∈ g2.support := hsupp23 ▸ hx
    have hfilt_card : (g2.support.filter (fun y => g2 y = x)).card = g2.support.card := by
      have happ := step_apply g2 x
      change g3 x = _ at happ
      rw [if_pos hx2] at happ
      omega
    have hfilt_eq : g2.support.filter (fun y => g2 y = x) = g2.support :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    have hconst : ∀ y ∈ g2.support, g2 y = x := by
      intro y hy
      rw [← hfilt_eq] at hy
      exact (Finset.mem_filter.mp hy).2
    have hsum2 : g2.support.card * x = 2 * g1.support.card := by
      have h1 : ∑ y ∈ g2.support, g2 y = g2.support.card * x := by
        rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
      rw [← h1]
      exact step_sum g1
    have hx_pos : 1 ≤ x := Nat.pos_of_ne_zero (fun h => h02 (h ▸ hx2))
    have hsub12 : g1.support ⊆ g2.support := support_subset_step g1
    have hcard12 : g1.support.card ≤ g2.support.card := Finset.card_le_card hsub12
    have hcard_pos2 : 1 ≤ g2.support.card := by omega
    have hx_le2 : x ≤ 2 := by nlinarith
    have hx12 : x = 1 ∨ x = 2 := by omega
    have hinj : Set.InjOn g1 g1.support := by
      intro u₁ hu₁ u₂ hu₂ heq
      set z := g1 u₁
      have hz2 : z ∈ g2.support := (mem_step_support_iff g1 z).mpr (Or.inr ⟨u₁, hu₁, rfl⟩)
      have hg2z : g2 z = x := hconst z hz2
      have hcard_le1 : (g1.support.filter (fun y => g1 y = z)).card ≤ 1 := by
        have happ := step_apply g1 z
        change g2 z = _ at happ
        rcases hx12 with hx1 | hx2'
        · omega
        · have hcard_eq12 : g1.support.card = g2.support.card := by
            rw [hx2'] at hsum2
            omega
          have hsupp12 : g1.support = g2.support :=
            Finset.eq_of_subset_of_card_le hsub12 (by omega)
          have hz1 : z ∈ g1.support := hsupp12 ▸ hz2
          rw [if_pos hz1] at happ
          omega
      have hu₁' : u₁ ∈ g1.support.filter (fun y => g1 y = z) :=
        Finset.mem_filter.mpr ⟨hu₁, rfl⟩
      have hu₂' : u₂ ∈ g1.support.filter (fun y => g1 y = z) :=
        Finset.mem_filter.mpr ⟨hu₂, heq.symm⟩
      exact Finset.card_le_one.mp hcard_le1 u₁ hu₁' u₂ hu₂'
    set T := g1.support.image g1
    have hT_card : T.card = g1.support.card := Finset.card_image_of_injOn hinj
    have h0T : 0 ∉ T := by
      intro hmem
      rcases Finset.mem_image.mp hmem with ⟨u, hu, hu0⟩
      exact Finsupp.mem_support_iff.mp hu hu0
    have hT_sum : ∑ v ∈ T, v = 2 * g.support.card := by
      rw [Finset.sum_image (fun a ha b hb hab => hinj ha hb hab)]
      exact step_sum g
    have hsub01 : g.support ⊆ g1.support := support_subset_step g
    have hcard01 : g.support.card ≤ g1.support.card := Finset.card_le_card hsub01
    have hge := sum_pos_finset_ge T h0T
    rw [hT_card, hT_sum] at hge
    have hg1_le3 : g1.support.card ≤ 3 := by nlinarith
    have hg3_le6 : g3.support.card ≤ 6 := by nlinarith
    have : g3 x ≤ 7 := by omega
    exact le_trans this (le_max_right _ _)

private lemma support_stabilizes {f : ℕ →₀ ℕ} (hf : f ≠ 0) (h0 : 0 ∉ f.support) :
    ∃ N₀, ∀ n ≥ N₀, (step^[n] f).support = (step^[N₀] f).support := by
  set M := max ((step^[3] f).support.sup id) 7
  have hbound : ∀ n, ∀ x ∈ (step^[n + 3] f).support, x ≤ M := by
    intro n
    induction n with
    | zero =>
        intro x hx
        exact le_trans (Finset.le_sup (f := id) hx) (le_max_left _ _)
    | succ n ih =>
        intro x hx
        have hstep_eq : step^[n + 1 + 3] f = step (step^[n + 3] f) := by
          have : n + 1 + 3 = (n + 3) + 1 := by omega
          rw [this, Function.iterate_succ_apply']
        rw [hstep_eq, mem_step_support_iff] at hx
        rcases hx with hx | ⟨y, hy, rfl⟩
        · exact ih x hx
        · have hiter : step^[n + 3] f = step^[3] (step^[n] f) := by
            rw [← Function.iterate_add_apply, Nat.add_comm]
          have hv := val_le_of_step3 (step_iter_ne_zero hf n) (step_iter_zero_notMem h0 n)
            y (hiter ▸ hy)
          rw [← hiter] at hv
          have hsub : (step^[n + 3] f).support ⊆ Finset.Icc 1 M := by
            intro z hz
            rw [Finset.mem_Icc]
            have hz0 : z ≠ 0 := fun h => step_iter_zero_notMem h0 (n + 3) (h ▸ hz)
            exact ⟨Nat.pos_of_ne_zero hz0, ih z hz⟩
          have hcard : (step^[n + 3] f).support.card ≤ M := by
            have hle := Finset.card_le_card hsub
            simpa using hle
          have h7 : 7 ≤ M := le_max_right _ _
          omega
  have hcard_le : ∀ n, (step^[n + 3] f).support.card ≤ M := by
    intro n
    have hsub : (step^[n + 3] f).support ⊆ Finset.Icc 1 M := by
      intro z hz
      rw [Finset.mem_Icc]
      have hz0 : z ≠ 0 := fun h => step_iter_zero_notMem h0 (n + 3) (h ▸ hz)
      exact ⟨Nat.pos_of_ne_zero hz0, hbound n z hz⟩
    have hle := Finset.card_le_card hsub
    simpa using hle
  have hstab : ∀ d m, M - (step^[m + 3] f).support.card ≤ d →
      ∃ N₀, ∀ n ≥ N₀, (step^[n] f).support = (step^[N₀] f).support := by
    intro d
    induction d with
    | zero =>
        intro m hm
        refine ⟨m + 3, fun n hn => ?_⟩
        have hsub := support_subset_iter f (m + 3) n hn
        obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
        have hle : (step^[m + 3 + r] f).support.card ≤ M := by
          have : m + 3 + r = (m + r) + 3 := by omega
          rw [this]
          exact hcard_le (m + r)
        exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
    | succ d ih =>
        intro m hm
        by_cases hall : ∀ n ≥ m + 3, (step^[n] f).support = (step^[m + 3] f).support
        · exact ⟨m + 3, hall⟩
        · push Not at hall
          rcases hall with ⟨n, hn, hne⟩
          obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hn
          have hsub := support_subset_iter f (m + 3) (m + 3 + r) (by omega)
          have hlt : (step^[m + 3] f).support.card < (step^[m + 3 + r] f).support.card :=
            Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne.symm⟩)
          have hmr : (m + r) + 3 = m + 3 + r := by omega
          exact ih (m + r) (by rw [hmr]; omega)
  exact hstab M 0 (by omega)

private def partOf (g : ℕ →₀ ℕ) : Multiset ℕ :=
  (g.support.val.map (fun x => g x - 1)).filter (0 < ·)

private def partStep (k : ℕ) (p : Multiset ℕ) : Multiset ℕ :=
  (if p.card < k then {k - p.card} else 0) +
    p.toFinset.val.map (fun d => p.count d)

private lemma partOf_pos (g : ℕ →₀ ℕ) : ∀ x ∈ partOf g, 0 < x := by
  intro x hx
  exact (Multiset.mem_filter.mp hx).2

private lemma partOf_count (g : ℕ →₀ ℕ) (d : ℕ) (hd : 0 < d) :
    (partOf g).count d = (g.support.filter (fun y => g y = d + 1)).card := by
  unfold partOf
  rw [Multiset.count_filter_of_pos hd, count_map_val]
  congr 1
  ext y
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hy, hgy⟩
    have h0 : g y ≠ 0 := Finsupp.mem_support_iff.mp hy
    exact ⟨hy, by omega⟩
  · rintro ⟨hy, hgy⟩
    exact ⟨hy, by omega⟩

private lemma partOf_card_add_ones (g : ℕ →₀ ℕ) :
    (partOf g).card + (g.support.filter (fun y => g y = 1)).card = g.support.card := by
  have h1 : (partOf g).card = (g.support.filter (fun y => g y ≠ 1)).card := by
    unfold partOf
    rw [Multiset.filter_map, Multiset.card_map]
    change (g.support.filter (fun y => 0 < g y - 1)).card = _
    congr 1
    ext y
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hy, hpos⟩
      exact ⟨hy, by omega⟩
    · rintro ⟨hy, hne⟩
      have h0 : g y ≠ 0 := Finsupp.mem_support_iff.mp hy
      exact ⟨hy, by omega⟩
  rw [h1]
  have h := Finset.sum_filter_add_sum_filter_not g.support (fun y => g y = 1) (fun _ => (1 : ℕ))
  simpa [Nat.add_comm] using h

private lemma partOf_sum {g : ℕ →₀ ℕ} (hsum : ∑ x ∈ g.support, g x = 2 * g.support.card) :
    (partOf g).sum = g.support.card := by
  have h1 : (partOf g).sum = (g.support.val.map (fun x => g x - 1)).sum := by
    unfold partOf
    have hsplit := Multiset.filter_add_not (0 < ·) (g.support.val.map (fun x => g x - 1))
    have h0 : ((g.support.val.map (fun x => g x - 1)).filter (fun x => ¬ 0 < x)).sum = 0 := by
      rw [Multiset.sum_eq_zero_iff]
      intro x hx
      have := (Multiset.mem_filter.mp hx).2
      omega
    have := congrArg Multiset.sum hsplit
    rw [Multiset.sum_add, h0, add_zero] at this
    exact this
  rw [h1]
  have h2 : (g.support.val.map (fun x => g x - 1)).sum = ∑ x ∈ g.support, (g x - 1) := rfl
  rw [h2]
  have hadd : (∑ x ∈ g.support, (g x - 1)) + g.support.card = ∑ x ∈ g.support, g x := by
    have hones : g.support.card = ∑ _x ∈ g.support, 1 := by simp
    rw [hones, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hgx : g x ≠ 0 := Finsupp.mem_support_iff.mp hx
    omega
  omega

private lemma partOf_eq_imp_step_eq {g₁ g₂ : ℕ →₀ ℕ} {S : Finset ℕ}
    (hs1 : g₁.support = S) (hs2 : g₂.support = S)
    (hns1 : (step g₁).support = S) (hns2 : (step g₂).support = S)
    (h0 : 0 ∉ S) (hp : partOf g₁ = partOf g₂) :
    step g₁ = step g₂ := by
  ext x
  by_cases hx : x ∈ S
  · have hx0 : x ≠ 0 := fun h => h0 (h ▸ hx)
    rw [step_apply, step_apply, hs1, hs2, if_pos hx]
    congr 1
    by_cases hx1 : x = 1
    · subst hx1
      have hc1 := partOf_card_add_ones g₁
      have hc2 := partOf_card_add_ones g₂
      rw [hs1] at hc1
      rw [hs2] at hc2
      rw [hp] at hc1
      omega
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hx0
      have hd : 0 < d := by omega
      have hc1 := partOf_count g₁ d hd
      have hc2 := partOf_count g₂ d hd
      rw [hs1] at hc1
      rw [hs2] at hc2
      rw [← hc1, ← hc2, hp]
  · have h1 : step g₁ x = 0 := Finsupp.notMem_support_iff.mp (hns1.symm ▸ hx)
    have h2 : step g₂ x = 0 := Finsupp.notMem_support_iff.mp (hns2.symm ▸ hx)
    rw [h1, h2]

private lemma partOf_step {g : ℕ →₀ ℕ} {S : Finset ℕ}
    (hs : g.support = S) (hns : (step g).support = S) (_h0 : 0 ∉ S) :
    partOf (step g) = partStep S.card (partOf g) := by
  have hcard_ones : (partOf g).card + (S.filter (fun y => g y = 1)).card = S.card := by
    have h := partOf_card_add_ones g
    rw [hs] at h
    exact h
  have hpart_rew : partOf (step g) =
      (S.filter (fun x => 0 < step g x - 1)).val.map (fun x => step g x - 1) := by
    unfold partOf
    rw [hns, Multiset.filter_map]
    rfl
  rw [hpart_rew]
  set A := S.filter (fun x => 0 < step g x - 1)
  have hval : ∀ x ∈ S, step g x - 1 = (S.filter (fun y => g y = x)).card := by
    intro x hx
    rw [step_apply, hs, if_pos hx]
    omega
  have hmemA : ∀ x, x ∈ A ↔ ∃ y ∈ S, g y = x := by
    intro x
    simp only [A, Finset.mem_filter]
    constructor
    · rintro ⟨hx, hpos⟩
      rw [hval x hx] at hpos
      rcases Finset.card_pos.mp hpos with ⟨y, hy⟩
      exact ⟨y, (Finset.mem_filter.mp hy).1, (Finset.mem_filter.mp hy).2⟩
    · rintro ⟨y, hy, rfl⟩
      have hgx : g y ∈ S := by
        rw [← hns, mem_step_support_iff, hs]
        exact Or.inr ⟨y, hy, rfl⟩
      refine ⟨hgx, ?_⟩
      rw [hval (g y) hgx]
      exact Finset.card_pos.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, rfl⟩⟩
  have h1mem : 1 ∈ A ↔ (partOf g).card < S.card := by
    rw [hmemA]
    constructor
    · rintro ⟨y, hy, hy1⟩
      have hpos : 0 < (S.filter (fun z => g z = 1)).card :=
        Finset.card_pos.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hy1⟩⟩
      omega
    · intro hlt
      have hpos : 0 < (S.filter (fun z => g z = 1)).card := by omega
      rcases Finset.card_pos.mp hpos with ⟨y, hy⟩
      exact ⟨y, (Finset.mem_filter.mp hy).1, (Finset.mem_filter.mp hy).2⟩
  have herase_eq : A.erase 1 = (partOf g).toFinset.image (· + 1) := by
    ext x
    simp only [Finset.mem_erase, hmemA, Finset.mem_image, Multiset.mem_toFinset]
    constructor
    · rintro ⟨hx1, y, hy, rfl⟩
      have hgy0 : g y ≠ 0 := Finsupp.mem_support_iff.mp (hs.symm ▸ hy)
      refine ⟨g y - 1, ?_, by omega⟩
      unfold partOf
      rw [Multiset.mem_filter]
      refine ⟨Multiset.mem_map.mpr ⟨y, hs.symm ▸ hy, rfl⟩, by omega⟩
    · rintro ⟨d, hd, rfl⟩
      have hdpos : 0 < d := partOf_pos g d hd
      have hcnt : (partOf g).count d = (S.filter (fun y => g y = d + 1)).card := by
        have h := partOf_count g d hdpos
        rw [hs] at h
        exact h
      have hcnt_pos : 0 < (S.filter (fun y => g y = d + 1)).card := by
        rw [← hcnt]
        exact Multiset.count_pos.mpr hd
      rcases Finset.card_pos.mp hcnt_pos with ⟨y, hy⟩
      exact ⟨by omega, y, (Finset.mem_filter.mp hy).1, (Finset.mem_filter.mp hy).2⟩
  have herase_map : (A.erase 1).val.map (fun x => step g x - 1) =
      (partOf g).toFinset.val.map (fun d => (partOf g).count d) := by
    rw [herase_eq]
    have hinj : Set.InjOn (· + 1) ((partOf g).toFinset : Set ℕ) :=
      fun _ _ _ _ hab => Nat.add_right_cancel hab
    rw [Finset.image_val_of_injOn hinj, Multiset.map_map]
    refine Multiset.map_congr rfl fun d hd => ?_
    have hd' : d ∈ partOf g := Multiset.mem_toFinset.mp hd
    have hdpos : 0 < d := partOf_pos g d hd'
    have hmem : d + 1 ∈ A := by
      have : d + 1 ∈ A.erase 1 := by
        rw [herase_eq]
        exact Finset.mem_image_of_mem _ hd
      exact Finset.mem_of_mem_erase this
    have hS : d + 1 ∈ S := (Finset.mem_filter.mp hmem).1
    simp only [Function.comp_apply]
    rw [hval (d + 1) hS, ← hs, ← partOf_count g d hdpos]
  unfold partStep
  by_cases hlt : (partOf g).card < S.card
  · have h1A : 1 ∈ A := h1mem.mpr hlt
    have h1S : 1 ∈ S := (Finset.mem_filter.mp h1A).1
    have hsplit : A = insert 1 (A.erase 1) := (Finset.insert_erase h1A).symm
    have hval1 : step g 1 - 1 = S.card - (partOf g).card := by
      rw [hval 1 h1S]
      omega
    rw [if_pos hlt, hsplit, Finset.insert_val_of_notMem (Finset.notMem_erase 1 A),
      Multiset.map_cons, hval1, herase_map]
    simp
  · have h1nA : 1 ∉ A := fun h => hlt (h1mem.mp h)
    rw [if_neg hlt, zero_add, ← Finset.erase_eq_of_notMem h1nA, herase_map]

private def ValidPart (k : ℕ) (p : Multiset ℕ) : Prop :=
  (∀ x ∈ p, 0 < x) ∧ p.sum = k

private lemma valid_card_le {k : ℕ} {p : Multiset ℕ} (hp : ValidPart k p) : p.card ≤ k := by
  have hle : ∀ s : Multiset ℕ, (∀ x ∈ s, 0 < x) → s.card ≤ s.sum := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; simp
    | cons a t ih =>
        intro hpos
        have ha := hpos a (Multiset.mem_cons_self a t)
        have ht := ih fun x hx => hpos x (Multiset.mem_cons_of_mem hx)
        simp only [Multiset.card_cons, Multiset.sum_cons]
        omega
  have := hle p hp.1
  have := hp.2
  omega

private lemma valid_partStep {k : ℕ} {p : Multiset ℕ} (hp : ValidPart k p) :
    ValidPart k (partStep k p) := by
  have hle := valid_card_le hp
  refine ⟨?_, ?_⟩
  · intro x hx
    unfold partStep at hx
    rcases Multiset.mem_add.mp hx with h1 | h2
    · split_ifs at h1 with hlt
      · have : x = k - p.card := Multiset.mem_singleton.mp h1
        omega
      · exact absurd h1 (Multiset.notMem_zero x)
    · rcases Multiset.mem_map.mp h2 with ⟨d, hd, rfl⟩
      exact Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hd)
  · unfold partStep
    rw [Multiset.sum_add]
    have h2 : (p.toFinset.val.map (fun d => p.count d)).sum = p.card := by
      have : (p.toFinset.val.map (fun d => p.count d)).sum = ∑ d ∈ p.toFinset, p.count d := rfl
      rw [this, Multiset.toFinset_sum_count_eq]
    rw [h2]
    split_ifs with hlt
    · simp only [Multiset.sum_singleton]
      omega
    · simp only [Multiset.sum_zero, zero_add]
      omega

private lemma valid_partStep_iter {k : ℕ} {p : Multiset ℕ} (hp : ValidPart k p) :
    ∀ n, ValidPart k ((partStep k)^[n] p)
  | 0 => hp
  | n + 1 => by
      rw [Function.iterate_succ_apply']
      exact valid_partStep (valid_partStep_iter hp n)

private lemma card_partStep_two {k : ℕ} {p : Multiset ℕ} (_hp : ValidPart k p) :
    let p2 := partStep k (partStep k p)
    (p.card ≥ 5 → p2.card < p.card) ∧ (p.card ≤ 4 → p2.card ≤ 4) := by
  set R := p.toFinset.val.map (fun d => p.count d)
  have hR_sum : R.sum = p.card := by
    have : R.sum = ∑ d ∈ p.toFinset, p.count d := rfl
    rw [this, Multiset.toFinset_sum_count_eq]
  have h0R : 0 ∉ R.toFinset := by
    intro hmem
    have h0 := Multiset.mem_toFinset.mp hmem
    rcases Multiset.mem_map.mp h0 with ⟨d, hd, hcnt⟩
    have := Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hd)
    omega
  have hT_le : ∑ v ∈ R.toFinset, v ≤ R.sum := by
    have hle : R.toFinset.val ≤ R := Multiset.dedup_le R
    obtain ⟨t, ht⟩ := Multiset.le_iff_exists_add.mp hle
    have hs : (R.toFinset.val).sum + t.sum = R.sum := by rw [← Multiset.sum_add, ← ht]
    have heq : ∑ v ∈ R.toFinset, v = R.toFinset.val.sum := by
      simp [Finset.sum]
    omega
  have hge := sum_pos_finset_ge R.toFinset h0R
  have hR_bound : R.toFinset.card * (R.toFinset.card + 1) ≤ 2 * p.card := by
    omega
  set p1 := partStep k p
  have hp1_toFinset : p1.toFinset.card ≤ 1 + R.toFinset.card := by
    have hsub : p1.toFinset ⊆ (if p.card < k then {k - p.card} else (∅ : Finset ℕ)) ∪ R.toFinset := by
      intro x hx
      have hx' := Multiset.mem_toFinset.mp hx
      unfold p1 partStep at hx'
      rcases Multiset.mem_add.mp hx' with h1 | h2
      · apply Finset.mem_union_left
        split_ifs at h1 ⊢
        · simpa using h1
        · exact absurd h1 (Multiset.notMem_zero x)
      · exact Finset.mem_union_right _ (Multiset.mem_toFinset.mpr h2)
    have hle := Finset.card_le_card hsub
    have hun := Finset.card_union_le (if p.card < k then {k - p.card} else (∅ : Finset ℕ)) R.toFinset
    have h1 : (if p.card < k then ({k - p.card} : Finset ℕ) else ∅).card ≤ 1 := by
      split_ifs <;> simp
    omega
  have hp2_card : (partStep k p1).card ≤ 1 + p1.toFinset.card := by
    unfold partStep
    rw [Multiset.card_add, Multiset.card_map]
    have h1 : (if p1.card < k then ({k - p1.card} : Multiset ℕ) else 0).card ≤ 1 := by
      split_ifs <;> simp
    have h2 : p1.toFinset.val.card = p1.toFinset.card := rfl
    omega
  have hp2_le : (partStep k p1).card ≤ 2 + R.toFinset.card := by omega
  constructor
  · intro h5
    by_contra hnot
    have hd : p.card - 2 ≤ R.toFinset.card := by omega
    have hmul : (p.card - 2) * (p.card - 1) ≤ R.toFinset.card * (R.toFinset.card + 1) := by
      have : p.card - 2 + 1 = p.card - 1 := by omega
      rw [← this]
      exact Nat.mul_le_mul hd (by omega)
    have : (p.card - 2) * (p.card - 1) ≤ 2 * p.card := le_trans hmul hR_bound
    have hsub1 : (p.card - 2) + 2 = p.card := by omega
    have hsub2 : (p.card - 1) + 1 = p.card := by omega
    nlinarith
  · intro h4
    have hd2 : R.toFinset.card ≤ 2 := by nlinarith
    omega

private lemma reaches_small_pair {k : ℕ} {p : Multiset ℕ} (hp : ValidPart k p) :
    ∃ N, ((partStep k)^[N] p).card ≤ 4 ∧ ((partStep k)^[N + 1] p).card ≤ 4 := by
  have hdesc : ∀ m, ∀ q : Multiset ℕ, ValidPart k q →
      max q.card (partStep k q).card ≤ m →
      ∃ N, ((partStep k)^[N] q).card ≤ 4 ∧ ((partStep k)^[N + 1] q).card ≤ 4 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro q hq hmax
        by_cases hle4 : max q.card (partStep k q).card ≤ 4
        · exact ⟨0, by simp [le_trans (le_max_left _ _) hle4],
            by simp [le_trans (le_max_right _ _) hle4]⟩
        · have hge5 : 5 ≤ max q.card (partStep k q).card := by omega
          have hq1 := valid_partStep hq
          have hc0 := card_partStep_two hq
          have hc1 := card_partStep_two hq1
          have hlt0 : (partStep k (partStep k q)).card < max q.card (partStep k q).card := by
            by_cases h : q.card ≥ 5
            · exact lt_of_lt_of_le (hc0.1 h) (le_max_left _ _)
            · have : (partStep k (partStep k q)).card ≤ 4 := hc0.2 (by omega)
              omega
          have hlt1 : (partStep k (partStep k (partStep k q))).card < max q.card (partStep k q).card := by
            by_cases h : (partStep k q).card ≥ 5
            · exact lt_of_lt_of_le (hc1.1 h) (le_max_right _ _)
            · have : (partStep k (partStep k (partStep k q))).card ≤ 4 := hc1.2 (by omega)
              omega
          have hnew_lt : max (partStep k (partStep k q)).card
              (partStep k (partStep k (partStep k q))).card < m := by
            exact lt_of_lt_of_le (max_lt hlt0 hlt1) hmax
          rcases ih _ hnew_lt (partStep k (partStep k q)) (valid_partStep hq1) le_rfl with
            ⟨N, hN0, hN1⟩
          refine ⟨N + 2, ?_, ?_⟩
          · rw [Function.iterate_add_apply]
            exact hN0
          · have : N + 2 + 1 = (N + 1) + 2 := by omega
            rw [this, Function.iterate_add_apply]
            exact hN1
  exact hdesc (max p.card (partStep k p).card) p hp le_rfl

private lemma partStep_pair {k a b : ℕ} (hk : 2 < k) (hab : a ≠ b) :
    partStep k ({a, b} : Multiset ℕ) = {k - 2, 1, 1} := by
  have hcard : ({a, b} : Multiset ℕ).card = 2 := by simp
  have htf : ({a, b} : Multiset ℕ).toFinset = {a, b} := by
    ext x; simp
  unfold partStep
  rw [hcard, if_pos hk, htf]
  have ha_not : a ∉ ({b} : Finset ℕ) := by simp [hab]
  rw [Finset.insert_val_of_notMem ha_not, Multiset.map_cons]
  have hsing : ({b} : Finset ℕ).val = {b} := rfl
  rw [hsing, Multiset.map_singleton]
  have hca : Multiset.count a ({a, b} : Multiset ℕ) = 1 := by simp [hab]
  have hcb : Multiset.count b ({a, b} : Multiset ℕ) = 1 := by simp [hab.symm]
  rw [hca, hcb]
  ext x
  simp [Multiset.count_cons, Multiset.count_singleton]
  omega

private lemma partStep_abb {k a b : ℕ} (hk : 3 < k) (hab : a ≠ b) :
    partStep k ({a, b, b} : Multiset ℕ) = {k - 3, 2, 1} := by
  have hcard : ({a, b, b} : Multiset ℕ).card = 3 := by simp
  have htf : ({a, b, b} : Multiset ℕ).toFinset = {a, b} := by
    ext x; simp
  unfold partStep
  rw [hcard, if_pos hk, htf]
  have ha_not : a ∉ ({b} : Finset ℕ) := by simp [hab]
  rw [Finset.insert_val_of_notMem ha_not, Multiset.map_cons]
  have hsing : ({b} : Finset ℕ).val = {b} := rfl
  rw [hsing, Multiset.map_singleton]
  have hca : Multiset.count a ({a, b, b} : Multiset ℕ) = 1 := by simp [hab]
  have hcb : Multiset.count b ({a, b, b} : Multiset ℕ) = 2 := by simp [hab.symm]
  rw [hca, hcb]
  ext x
  simp [Multiset.count_cons, Multiset.count_singleton]
  omega

private lemma partStep_abc {k a b c : ℕ} (hk : 3 < k) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    partStep k ({a, b, c} : Multiset ℕ) = {k - 3, 1, 1, 1} := by
  have hcard : ({a, b, c} : Multiset ℕ).card = 3 := by simp
  have htf : ({a, b, c} : Multiset ℕ).toFinset = {a, b, c} := by
    ext x; simp
  unfold partStep
  rw [hcard, if_pos hk, htf]
  have ha_not : a ∉ ({b, c} : Finset ℕ) := by simp [hab, hac]
  have hb_not : b ∉ ({c} : Finset ℕ) := by simp [hbc]
  rw [Finset.insert_val_of_notMem ha_not, Multiset.map_cons,
    Finset.insert_val_of_notMem hb_not, Multiset.map_cons]
  have hsing : ({c} : Finset ℕ).val = {c} := rfl
  rw [hsing, Multiset.map_singleton]
  have hca : Multiset.count a ({a, b, c} : Multiset ℕ) = 1 := by simp [hab, hac]
  have hcb : Multiset.count b ({a, b, c} : Multiset ℕ) = 1 := by simp [hab.symm, hbc]
  have hcc : Multiset.count c ({a, b, c} : Multiset ℕ) = 1 := by simp [hac.symm, hbc.symm]
  rw [hca, hcb, hcc]
  ext x
  simp [Multiset.count_cons, Multiset.count_singleton]
  omega

private lemma partStep_abbb {k a b : ℕ} (hk : 4 < k) (hab : a ≠ b) :
    partStep k ({a, b, b, b} : Multiset ℕ) = {k - 4, 3, 1} := by
  have hcard : ({a, b, b, b} : Multiset ℕ).card = 4 := by simp
  have htf : ({a, b, b, b} : Multiset ℕ).toFinset = {a, b} := by
    ext x; simp
  unfold partStep
  rw [hcard, if_pos hk, htf]
  have ha_not : a ∉ ({b} : Finset ℕ) := by simp [hab]
  rw [Finset.insert_val_of_notMem ha_not, Multiset.map_cons]
  have hsing : ({b} : Finset ℕ).val = {b} := rfl
  rw [hsing, Multiset.map_singleton]
  have hca : Multiset.count a ({a, b, b, b} : Multiset ℕ) = 1 := by simp [hab]
  have hcb : Multiset.count b ({a, b, b, b} : Multiset ℕ) = 3 := by simp [hab.symm]
  rw [hca, hcb]
  ext x
  simp [Multiset.count_cons, Multiset.count_singleton]
  omega

private lemma partStep_abcc {k a b c : ℕ} (hk : 4 < k) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    partStep k ({a, b, c, c} : Multiset ℕ) = {k - 4, 2, 1, 1} := by
  have hcard : ({a, b, c, c} : Multiset ℕ).card = 4 := by simp
  have htf : ({a, b, c, c} : Multiset ℕ).toFinset = {a, b, c} := by
    ext x; simp
  unfold partStep
  rw [hcard, if_pos hk, htf]
  have ha_not : a ∉ ({b, c} : Finset ℕ) := by simp [hab, hac]
  have hb_not : b ∉ ({c} : Finset ℕ) := by simp [hbc]
  rw [Finset.insert_val_of_notMem ha_not, Multiset.map_cons,
    Finset.insert_val_of_notMem hb_not, Multiset.map_cons]
  have hsing : ({c} : Finset ℕ).val = {c} := rfl
  rw [hsing, Multiset.map_singleton]
  have hca : Multiset.count a ({a, b, c, c} : Multiset ℕ) = 1 := by simp [hab, hac]
  have hcb : Multiset.count b ({a, b, c, c} : Multiset ℕ) = 1 := by simp [hab.symm, hbc]
  have hcc : Multiset.count c ({a, b, c, c} : Multiset ℕ) = 2 := by simp [hac.symm, hbc.symm]
  rw [hca, hcb, hcc]
  ext x
  simp [Multiset.count_cons, Multiset.count_singleton]
  omega

private lemma partStep_abbbb {k a b : ℕ} (hk : 5 < k) (hab : a ≠ b) :
    partStep k ({a, b, b, b, b} : Multiset ℕ) = {k - 5, 4, 1} := by
  have hcard : ({a, b, b, b, b} : Multiset ℕ).card = 5 := by simp
  have htf : ({a, b, b, b, b} : Multiset ℕ).toFinset = {a, b} := by
    ext x; simp
  unfold partStep
  rw [hcard, if_pos hk, htf]
  have ha_not : a ∉ ({b} : Finset ℕ) := by simp [hab]
  rw [Finset.insert_val_of_notMem ha_not, Multiset.map_cons]
  have hsing : ({b} : Finset ℕ).val = {b} := rfl
  rw [hsing, Multiset.map_singleton]
  have hca : Multiset.count a ({a, b, b, b, b} : Multiset ℕ) = 1 := by simp [hab]
  have hcb : Multiset.count b ({a, b, b, b, b} : Multiset ℕ) = 4 := by simp [hab.symm]
  rw [hca, hcb]
  ext x
  simp [Multiset.count_cons, Multiset.count_singleton]
  omega

private lemma classify_sum_le_four (R : Multiset ℕ) (hpos : ∀ x ∈ R, 0 < x)
    (hsum1 : 1 ≤ R.sum) (hsum4 : R.sum ≤ 4) :
    (R.sum = 1 ∧ R = {1}) ∨
    (R.sum = 2 ∧ (R = {2} ∨ R = {1, 1})) ∨
    (R.sum = 3 ∧ (R = {3} ∨ R = {2, 1} ∨ R = {1, 1, 1})) ∨
    (R.sum = 4 ∧ (R = {4} ∨ R = {3, 1} ∨ R = {2, 2} ∨ R = {2, 1, 1} ∨ R = {1, 1, 1, 1})) := by
  have hpeel : ∀ (M : Multiset ℕ), (∀ x ∈ M, 0 < x) → M.sum ≤ 4 →
      M = 0 ∨ M = {1} ∨ M = {2} ∨ M = {1, 1} ∨ M = {3} ∨ M = {2, 1} ∨ M = {1, 1, 1} ∨
      M = {4} ∨ M = {3, 1} ∨ M = {2, 2} ∨ M = {2, 1, 1} ∨ M = {1, 1, 1, 1} := by
    intro M
    induction M using Multiset.induction_on with
    | empty => intro _ _; exact Or.inl rfl
    | cons a s ih =>
        intro hp hs
        have ha : 0 < a := hp a (Multiset.mem_cons_self a s)
        have hps : ∀ x ∈ s, 0 < x := fun x hx => hp x (Multiset.mem_cons_of_mem hx)
        rw [Multiset.sum_cons] at hs
        have hih := ih hps (by omega)
        have ha4 : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by omega
        rcases hih with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases ha4 with rfl | rfl | rfl | rfl <;>
        (try simp at hs) <;>
        try omega
        all_goals
          first
          | (right; left; ext x; simp [Multiset.count_cons, Multiset.count_singleton] <;> omega)
          | (right; right; left; ext x; simp [Multiset.count_cons, Multiset.count_singleton] <;> omega)
          | (right; right; right; left; ext x; simp [Multiset.count_cons, Multiset.count_singleton] <;> omega)
          | (right; right; right; right; left; ext x; simp [Multiset.count_cons, Multiset.count_singleton] <;> omega)
          | (right; right; right; right; right; left; ext x; simp [Multiset.count_cons, Multiset.count_singleton] <;> omega)
          | (right; right; right; right; right; right; left; ext x; simp [Multiset.count_cons, Multiset.count_singleton] <;> omega)
          | (right; right; right; right; right; right; right; left; ext x; simp [Multiset.count_cons, Multiset.count_singleton] <;> omega)
          | (right; right; right; right; right; right; right; right; left; ext x; simp [Multiset.count_cons, Multiset.count_singleton] <;> omega)
          | (right; right; right; right; right; right; right; right; right; left; ext x; simp [Multiset.count_cons, Multiset.count_singleton] <;> omega)
          | (right; right; right; right; right; right; right; right; right; right; left; ext x; simp [Multiset.count_cons, Multiset.count_singleton] <;> omega)
          | (right; right; right; right; right; right; right; right; right; right; right; ext x; simp [Multiset.count_cons, Multiset.count_singleton] <;> omega)
  rcases hpeel R hpos hsum4 with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all

private lemma large_k_periodic {k : ℕ} (hk : 10 ≤ k) {q₀ : Multiset ℕ}
    (hq0 : ValidPart k q₀) (hcard : q₀.card ≤ 4) :
    ∃ N, ∃ q ∈ ({1, 2, 3} : Finset ℕ), (partStep k)^[N + q] q₀ = (partStep k)^[N] q₀ := by
  have hq0_pos : 1 ≤ q₀.card := by
    by_contra h
    have hc : q₀.card = 0 := by omega
    have hz : q₀ = 0 := Multiset.card_eq_zero.mp hc
    have hs := hq0.2
    rw [hz, Multiset.sum_zero] at hs
    omega
  set R := q₀.toFinset.val.map (fun d => q₀.count d)
  have hR_pos : ∀ x ∈ R, 0 < x := by
    intro x hx
    rcases Multiset.mem_map.mp hx with ⟨d, hd, rfl⟩
    exact Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hd)
  have hR_sum : R.sum = q₀.card := by
    have : R.sum = ∑ d ∈ q₀.toFinset, q₀.count d := rfl
    rw [this, Multiset.toFinset_sum_count_eq]
  have hq1 : partStep k q₀ = (k - R.sum) ::ₘ R := by
    unfold partStep
    rw [if_pos (by omega), hR_sum]
    simp [R]
  have hcycle2 : (partStep k)^[2] ({k - 3, 1, 1, 1} : Multiset ℕ) = {k - 3, 1, 1, 1} := by
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [partStep_abbb (by omega) (by omega), partStep_abc (by omega) (by omega) (by omega) (by omega)]
  have hcycle1 : partStep k ({k - 4, 2, 1, 1} : Multiset ℕ) = {k - 4, 2, 1, 1} :=
    partStep_abcc (by omega) (by omega) (by omega) (by omega)
  have from_c3111 : ∀ n, (partStep k)^[n] q₀ = {k - 3, 1, 1, 1} →
      ∃ N, ∃ q ∈ ({1, 2, 3} : Finset ℕ), (partStep k)^[N + q] q₀ = (partStep k)^[N] q₀ := by
    intro n hn
    refine ⟨n, 2, by decide, ?_⟩
    rw [Nat.add_comm, Function.iterate_add_apply, hn, hcycle2]
  have from_c321 : ∀ n, (partStep k)^[n] q₀ = {k - 3, 2, 1} →
      ∃ N, ∃ q ∈ ({1, 2, 3} : Finset ℕ), (partStep k)^[N + q] q₀ = (partStep k)^[N] q₀ := by
    intro n hn
    apply from_c3111 (n + 1)
    rw [Function.iterate_succ_apply', hn, partStep_abc (by omega) (by omega) (by omega) (by omega)]
  have from_c211 : ∀ n, (partStep k)^[n] q₀ = {k - 2, 1, 1} →
      ∃ N, ∃ q ∈ ({1, 2, 3} : Finset ℕ), (partStep k)^[N + q] q₀ = (partStep k)^[N] q₀ := by
    intro n hn
    apply from_c321 (n + 1)
    rw [Function.iterate_succ_apply', hn, partStep_abb (by omega) (by omega)]
  have hcls := classify_sum_le_four R hR_pos (by omega) (by omega)
  rcases hcls with ⟨hs, hR⟩ | ⟨hs, hR | hR⟩ | ⟨hs, hR | hR | hR⟩ | ⟨hs, hR | hR | hR | hR | hR⟩
  · apply from_c211 2
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [hq1, hs, hR]
    exact partStep_pair (by omega) (by omega)
  · apply from_c211 2
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [hq1, hs, hR]
    exact partStep_pair (by omega) (by omega)
  · apply from_c211 1
    simp [hq1, hR]
  · apply from_c211 2
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [hq1, hs, hR]
    exact partStep_pair (by omega) (by omega)
  · apply from_c321 1
    simp [hq1, hR]
  · apply from_c3111 1
    simp [hq1, hR]
  · apply from_c211 2
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [hq1, hs, hR]
    exact partStep_pair (by omega) (by omega)
  · apply from_c3111 2
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [hq1, hs, hR]
    exact partStep_abc (by omega) (by omega) (by omega) (by omega)
  · apply from_c321 2
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [hq1, hs, hR]
    exact partStep_abb (by omega) (by omega)
  · refine ⟨1, 1, by decide, ?_⟩
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [hq1, hs, hR]
    exact hcycle1
  · apply from_c3111 3
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    rw [hq1, hs, hR]
    have h4 : (k - 4) ::ₘ ({1, 1, 1, 1} : Multiset ℕ) = {k - 4, 1, 1, 1, 1} := rfl
    rw [h4, partStep_abbbb (by omega) (by omega),
      partStep_abc (by omega) (by omega) (by omega) (by omega)]

private def myDedup : List ℕ → List ℕ
  | [] => []
  | a :: t => if t.contains a then myDedup t else a :: myDedup t

private lemma mem_myDedup (L : List ℕ) (x : ℕ) : x ∈ myDedup L ↔ x ∈ L := by
  induction L with
  | nil => simp [myDedup]
  | cons a t ih =>
      unfold myDedup
      split_ifs with h
      · have hat : a ∈ t := List.elem_iff.mp (by simpa using h)
        rw [ih]
        simp only [List.mem_cons]
        constructor
        · exact Or.inr
        · rintro (rfl | hx)
          · exact hat
          · exact hx
      · simp [ih]

private lemma nodup_myDedup (L : List ℕ) : (myDedup L).Nodup := by
  induction L with
  | nil => simp [myDedup]
  | cons a t ih =>
      unfold myDedup
      split_ifs with h
      · exact ih
      · rw [List.nodup_cons]
        refine ⟨?_, ih⟩
        rw [mem_myDedup]
        intro hat
        exact h (by simpa using hat)

private lemma coe_myDedup (L : List ℕ) :
    ((myDedup L : List ℕ) : Multiset ℕ) = (L : Multiset ℕ).toFinset.val := by
  have hnd : ((myDedup L : List ℕ) : Multiset ℕ).Nodup :=
    Multiset.coe_nodup.mpr (nodup_myDedup L)
  have hnd2 : (L : Multiset ℕ).toFinset.val.Nodup := (L : Multiset ℕ).toFinset.nodup
  exact (Multiset.Nodup.ext hnd hnd2).mpr fun x => by
    simp [mem_myDedup]

private def partStepList (k : ℕ) (L : List ℕ) : List ℕ :=
  (if L.length < k then [k - L.length] else []) ++
    (myDedup L).map (fun d => L.count d)

private lemma coe_partStepList (k : ℕ) (L : List ℕ) :
    ((partStepList k L : List ℕ) : Multiset ℕ) = partStep k (L : Multiset ℕ) := by
  unfold partStepList partStep
  rw [← Multiset.coe_add]
  congr 1
  · by_cases h : L.length < k
    · simp [h]
    · simp [h]
  · rw [← Multiset.map_coe, coe_myDedup]
    refine Multiset.map_congr rfl fun d _ => (Multiset.coe_count d L).symm

private def iterList (k : ℕ) : ℕ → List ℕ → List ℕ
  | 0, L => L
  | n + 1, L => partStepList k (iterList k n L)

private lemma coe_iterList (k : ℕ) :
    ∀ n L, ((iterList k n L : List ℕ) : Multiset ℕ) = (partStep k)^[n] (L : Multiset ℕ)
  | 0, _ => rfl
  | n + 1, L => by
      simp only [iterList, Function.iterate_succ_apply']
      rw [coe_partStepList, coe_iterList k n L]

private def sameMultiset (L₁ L₂ : List ℕ) : Bool :=
  L₁.all (fun x => L₁.count x == L₂.count x) &&
  L₂.all (fun x => L₁.count x == L₂.count x)

private lemma sameMultiset_eq {L₁ L₂ : List ℕ} (h : sameMultiset L₁ L₂ = true) :
    (L₁ : Multiset ℕ) = (L₂ : Multiset ℕ) := by
  unfold sameMultiset at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  ext x
  rw [Multiset.coe_count, Multiset.coe_count]
  by_cases hx1 : x ∈ L₁
  · exact beq_iff_eq.mp (h.1 x hx1)
  · by_cases hx2 : x ∈ L₂
    · exact beq_iff_eq.mp (h.2 x hx2)
    · rw [List.count_eq_zero.mpr hx1, List.count_eq_zero.mpr hx2]

private def checkPeriod (k : ℕ) (L : List ℕ) : Bool :=
  let s := iterList k 12 L
  sameMultiset (iterList k 1 s) s ||
    sameMultiset (iterList k 2 s) s ||
    sameMultiset (iterList k 3 s) s

private lemma small_k_check : ∀ a b c d : Fin 10,
    a.val ≤ b.val → b.val ≤ c.val → c.val ≤ d.val →
    1 ≤ a.val + b.val + c.val + d.val →
    a.val + b.val + c.val + d.val ≤ 9 →
    checkPeriod (a.val + b.val + c.val + d.val)
      ([a.val, b.val, c.val, d.val].filter (fun x => decide (0 < x))) = true := by
  decide

private lemma small_k_periodic {k : ℕ} (hk1 : 1 ≤ k) (hk9 : k ≤ 9) {q₀ : Multiset ℕ}
    (hq0 : ValidPart k q₀) (hcard : q₀.card ≤ 4) :
    ∃ N, ∃ q ∈ ({1, 2, 3} : Finset ℕ), (partStep k)^[N + q] q₀ = (partStep k)^[N] q₀ := by
  set L := q₀.sort (· ≤ ·)
  have hL_coe : (L : Multiset ℕ) = q₀ := Multiset.sort_eq q₀ (· ≤ ·)
  have hL_len : L.length ≤ 4 := by
    have : L.length = q₀.card := by rw [← Multiset.coe_card, hL_coe]
    omega
  have hL_sorted : L.Pairwise (· ≤ ·) := Multiset.pairwise_sort q₀ (· ≤ ·)
  have hL_pos : ∀ x ∈ L, 0 < x := by
    intro x hx
    exact hq0.1 x (hL_coe ▸ Multiset.mem_coe.mpr hx)
  have hL_sum : L.sum = k := by
    rw [← Multiset.sum_coe, hL_coe, hq0.2]
  have hL_lt : ∀ x ∈ L, x < 10 := by
    intro x hx
    have hle : x ≤ L.sum := List.le_sum_of_mem hx
    omega
  have hex : ∃ a b c d : Fin 10,
      a.val ≤ b.val ∧ b.val ≤ c.val ∧ c.val ≤ d.val ∧
      a.val + b.val + c.val + d.val = k ∧
      [a.val, b.val, c.val, d.val].filter (fun x => decide (0 < x)) = L := by
    match L, hL_len, hL_sorted, hL_pos, hL_sum, hL_lt with
    | [], _, _, _, hs, _ => simp at hs; omega
    | [x₁], _, _, hp, hs, hlt =>
        have h1 : 0 < x₁ := hp x₁ (by simp)
        have h1lt : x₁ < 10 := hlt x₁ (by simp)
        refine ⟨⟨0, by omega⟩, ⟨0, by omega⟩, ⟨0, by omega⟩, ⟨x₁, h1lt⟩,
          by simp, by simp, by simp, by simp at hs ⊢; omega, ?_⟩
        simp [h1]
    | [x₁, x₂], _, hst, hp, hs, hlt =>
        have h1 : 0 < x₁ := hp x₁ (by simp)
        have h2 : 0 < x₂ := hp x₂ (by simp)
        have h1lt : x₁ < 10 := hlt x₁ (by simp)
        have h2lt : x₂ < 10 := hlt x₂ (by simp)
        have hle12 : x₁ ≤ x₂ := by simpa using hst
        refine ⟨⟨0, by omega⟩, ⟨0, by omega⟩, ⟨x₁, h1lt⟩, ⟨x₂, h2lt⟩,
          by simp, by simp, hle12, by simp at hs ⊢; omega, ?_⟩
        simp [h1, h2]
    | [x₁, x₂, x₃], _, hst, hp, hs, hlt =>
        have h1 : 0 < x₁ := hp x₁ (by simp)
        have h2 : 0 < x₂ := hp x₂ (by simp)
        have h3 : 0 < x₃ := hp x₃ (by simp)
        have h1lt : x₁ < 10 := hlt x₁ (by simp)
        have h2lt : x₂ < 10 := hlt x₂ (by simp)
        have h3lt : x₃ < 10 := hlt x₃ (by simp)
        simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq] at hst
        refine ⟨⟨0, by omega⟩, ⟨x₁, h1lt⟩, ⟨x₂, h2lt⟩, ⟨x₃, h3lt⟩,
          by simp, hst.1.1, hst.2.1, by simp at hs ⊢; omega, ?_⟩
        simp [h1, h2, h3]
    | [x₁, x₂, x₃, x₄], _, hst, hp, hs, hlt =>
        have h1 : 0 < x₁ := hp x₁ (by simp)
        have h2 : 0 < x₂ := hp x₂ (by simp)
        have h3 : 0 < x₃ := hp x₃ (by simp)
        have h4 : 0 < x₄ := hp x₄ (by simp)
        have h1lt : x₁ < 10 := hlt x₁ (by simp)
        have h2lt : x₂ < 10 := hlt x₂ (by simp)
        have h3lt : x₃ < 10 := hlt x₃ (by simp)
        have h4lt : x₄ < 10 := hlt x₄ (by simp)
        simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq] at hst
        refine ⟨⟨x₁, h1lt⟩, ⟨x₂, h2lt⟩, ⟨x₃, h3lt⟩, ⟨x₄, h4lt⟩,
          hst.1.1, hst.2.1.1, hst.2.2.1, by simp at hs ⊢; omega, ?_⟩
        simp [h1, h2, h3, h4]
    | _ :: _ :: _ :: _ :: _ :: _, hlen, _, _, _, _ => simp at hlen; omega
  rcases hex with ⟨a, b, c, d, hab, hbc, hcd, hsum, hflt⟩
  have hchk := small_k_check a b c d hab hbc hcd (by omega) (by omega)
  rw [hsum, hflt] at hchk
  unfold checkPeriod at hchk
  simp only [Bool.or_eq_true] at hchk
  rcases hchk with (h1 | h2) | h3
  · refine ⟨12, 1, by decide, ?_⟩
    have hm := sameMultiset_eq h1
    rw [coe_iterList, coe_iterList, hL_coe] at hm
    rw [Nat.add_comm, Function.iterate_add_apply]
    exact hm
  · refine ⟨12, 2, by decide, ?_⟩
    have hm := sameMultiset_eq h2
    rw [coe_iterList, coe_iterList, hL_coe] at hm
    rw [Nat.add_comm, Function.iterate_add_apply]
    exact hm
  · refine ⟨12, 3, by decide, ?_⟩
    have hm := sameMultiset_eq h3
    rw [coe_iterList, coe_iterList, hL_coe] at hm
    rw [Nat.add_comm, Function.iterate_add_apply]
    exact hm

private lemma partStep_periodic {k : ℕ} (hk : 1 ≤ k) {p : Multiset ℕ} (hp : ValidPart k p) :
    ∃ N, ∃ q ∈ ({1, 2, 3} : Finset ℕ), (partStep k)^[N + q] p = (partStep k)^[N] p := by
  rcases reaches_small_pair hp with ⟨N₁, hN₁, _⟩
  set q₀ := (partStep k)^[N₁] p
  have hq0 : ValidPart k q₀ := valid_partStep_iter hp N₁
  have hres : ∃ N₂, ∃ q ∈ ({1, 2, 3} : Finset ℕ),
      (partStep k)^[N₂ + q] q₀ = (partStep k)^[N₂] q₀ := by
    by_cases hk10 : 10 ≤ k
    · exact large_k_periodic hk10 hq0 hN₁
    · exact small_k_periodic hk (by omega) hq0 hN₁
  rcases hres with ⟨N₂, q, hq, heq⟩
  refine ⟨N₂ + N₁, q, hq, ?_⟩
  have hadd : N₂ + N₁ + q = (N₂ + q) + N₁ := by omega
  rw [hadd, Function.iterate_add_apply (partStep k) (N₂ + q) N₁,
    Function.iterate_add_apply (partStep k) N₂ N₁]
  exact heq

end OPGMultisetProof

theorem OMA.solution : type_of% @OMA.S_opg_a_sequence_defined_on_multisets.main := by
  intro f hf h0
  rcases OPGMultisetProof.support_stabilizes hf h0 with ⟨N₀, hstab⟩
  set S := (OMA.S_opg_a_sequence_defined_on_multisets.step^[N₀] f).support
  set g₀ := OMA.S_opg_a_sequence_defined_on_multisets.step^[N₀ + 1] f
  have hsupp : ∀ n, (OMA.S_opg_a_sequence_defined_on_multisets.step^[n] g₀).support = S := by
    intro n
    have h1 : OMA.S_opg_a_sequence_defined_on_multisets.step^[n] g₀ =
        OMA.S_opg_a_sequence_defined_on_multisets.step^[n + (N₀ + 1)] f := by
      dsimp only [g₀]
      rw [← Function.iterate_add_apply]
    rw [h1]
    exact hstab (n + (N₀ + 1)) (by omega)
  have h0S : 0 ∉ S := OPGMultisetProof.step_iter_zero_notMem h0 N₀
  have hS_pos : 1 ≤ S.card := by
    have hne : OMA.S_opg_a_sequence_defined_on_multisets.step^[N₀] f ≠ 0 :=
      OPGMultisetProof.step_iter_ne_zero hf N₀
    exact Finset.card_pos.mpr (Finsupp.support_nonempty_iff.mpr hne)
  have hg0_sum : ∑ x ∈ g₀.support, g₀ x = 2 * g₀.support.card := by
    have hg0_eq : g₀ = OMA.S_opg_a_sequence_defined_on_multisets.step
        (OMA.S_opg_a_sequence_defined_on_multisets.step^[N₀] f) := by
      dsimp only [g₀]
      rw [Function.iterate_succ_apply']
    have hs0 : g₀.support = S := by simpa using hsupp 0
    have hsum := OPGMultisetProof.step_sum (OMA.S_opg_a_sequence_defined_on_multisets.step^[N₀] f)
    rw [← hg0_eq] at hsum
    rw [hsum, hs0]
  have hvalid : OPGMultisetProof.ValidPart S.card (OPGMultisetProof.partOf g₀) := by
    refine ⟨OPGMultisetProof.partOf_pos g₀, ?_⟩
    have hs0 : g₀.support = S := by simpa using hsupp 0
    rw [OPGMultisetProof.partOf_sum hg0_sum, hs0]
  have hpart_iter : ∀ n, OPGMultisetProof.partOf
      (OMA.S_opg_a_sequence_defined_on_multisets.step^[n] g₀) =
      (OPGMultisetProof.partStep S.card)^[n] (OPGMultisetProof.partOf g₀) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
        refine OPGMultisetProof.partOf_step (hsupp n) ?_ h0S
        simpa [Function.iterate_succ_apply'] using hsupp (n + 1)
  rcases OPGMultisetProof.partStep_periodic hS_pos hvalid with ⟨N, q, hq, heq⟩
  refine ⟨N + N₀ + 2, q, hq, ?_⟩
  have hp_eq : OPGMultisetProof.partOf
      (OMA.S_opg_a_sequence_defined_on_multisets.step^[N + q] g₀) =
      OPGMultisetProof.partOf
      (OMA.S_opg_a_sequence_defined_on_multisets.step^[N] g₀) := by
    rw [hpart_iter (N + q), hpart_iter N, heq]
  have hstep_eq : OMA.S_opg_a_sequence_defined_on_multisets.step
      (OMA.S_opg_a_sequence_defined_on_multisets.step^[N + q] g₀) =
      OMA.S_opg_a_sequence_defined_on_multisets.step
      (OMA.S_opg_a_sequence_defined_on_multisets.step^[N] g₀) := by
    refine OPGMultisetProof.partOf_eq_imp_step_eq (hsupp (N + q)) (hsupp N) ?_ ?_ h0S hp_eq
    · simpa [Function.iterate_succ_apply'] using hsupp (N + q + 1)
    · simpa [Function.iterate_succ_apply'] using hsupp (N + 1)
  have hL : OMA.S_opg_a_sequence_defined_on_multisets.step^[N + N₀ + 2 + q] f =
      OMA.S_opg_a_sequence_defined_on_multisets.step
        (OMA.S_opg_a_sequence_defined_on_multisets.step^[N + q] g₀) := by
    dsimp only [g₀]
    rw [← Function.iterate_succ_apply' OMA.S_opg_a_sequence_defined_on_multisets.step (N + q),
      ← Function.iterate_add_apply]
    congr 1
    omega
  have hR : OMA.S_opg_a_sequence_defined_on_multisets.step^[N + N₀ + 2] f =
      OMA.S_opg_a_sequence_defined_on_multisets.step
        (OMA.S_opg_a_sequence_defined_on_multisets.step^[N] g₀) := by
    dsimp only [g₀]
    rw [← Function.iterate_succ_apply' OMA.S_opg_a_sequence_defined_on_multisets.step N,
      ← Function.iterate_add_apply]
    congr 1
    omega
  rw [hL, hR, hstep_eq]

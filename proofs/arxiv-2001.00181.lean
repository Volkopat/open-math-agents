import OMAStatements.S_arxiv_2001_00181
namespace OMA.P_arxiv_2001_00181

open OMA.S_arxiv_2001_00181

/-! ### Part 1: Kostka dominance inequality `K_{lam, (n+1, n-1, n-1)} ≤ K_{lam, (n, n, n-1)}` -/

private def wUnb (n : ℕ) : Fin 3 → ℕ
  | ⟨0, _⟩ => n + 1
  | ⟨1, _⟩ => n - 1
  | ⟨2, _⟩ => n - 1

private def wBal (n : ℕ) : Fin 3 → ℕ
  | ⟨0, _⟩ => n
  | ⟨1, _⟩ => n
  | ⟨2, _⟩ => n - 1

private lemma ssyt_zero_row_zero {lam : List ℕ} {k : ℕ} {w : Fin k → ℕ}
    {T : (r : Fin lam.length) → Fin (lam.get r) → Fin k}
    (hpart : IsPartitionOf N lam) (hT : IsSSYT lam k w T)
    (r : Fin lam.length) (c : Fin (lam.get r)) (h0 : (T r c).val = 0) : r.val = 0 := by
  by_contra hr
  have hrpos : 0 < r.val := Nat.pos_of_ne_zero hr
  let r0 : Fin lam.length := ⟨0, lt_trans hrpos r.isLt⟩
  have hge : lam.get r ≤ lam.get r0 := by
    have hpw := List.pairwise_iff_get.mp hpart.2.2
    exact hpw r0 r hrpos
  let c0 : Fin (lam.get r0) := ⟨c.val, lt_of_lt_of_le c.isLt hge⟩
  have hlt := hT.2.1 r0 r c0 c hrpos rfl
  have hltv : (T r0 c0).val < (T r c).val := hlt
  omega

private lemma ssyt_one_row_le_one {lam : List ℕ} {k : ℕ} {w : Fin k → ℕ}
    {T : (r : Fin lam.length) → Fin (lam.get r) → Fin k}
    (hpart : IsPartitionOf N lam) (hT : IsSSYT lam k w T)
    (r : Fin lam.length) (c : Fin (lam.get r)) (h1 : (T r c).val ≤ 1) : r.val ≤ 1 := by
  by_contra hr
  have hr2 : 2 ≤ r.val := by omega
  let r0 : Fin lam.length := ⟨0, lt_of_lt_of_le (by omega) r.isLt⟩
  let r1 : Fin lam.length := ⟨1, lt_of_lt_of_le (by omega) r.isLt⟩
  have hpw := List.pairwise_iff_get.mp hpart.2.2
  have hge0 : lam.get r ≤ lam.get r0 := hpw r0 r (show (0 : ℕ) < r.val by omega)
  have hge1 : lam.get r ≤ lam.get r1 := hpw r1 r (show (1 : ℕ) < r.val by omega)
  let c0 : Fin (lam.get r0) := ⟨c.val, lt_of_lt_of_le c.isLt hge0⟩
  let c1 : Fin (lam.get r1) := ⟨c.val, lt_of_lt_of_le c.isLt hge1⟩
  have hlt01 : (T r0 c0).val < (T r1 c1).val := hT.2.1 r0 r1 c0 c1 (show (0 : ℕ) < 1 by omega) rfl
  have hlt1r : (T r1 c1).val < (T r c).val := hT.2.1 r1 r c1 c (show (1 : ℕ) < r.val by omega) rfl
  omega

/-- For any partition `lam` of `N` and `n ≥ 2`, `K_{lam, (n+1, n-1, n-1)} ≤ K_{lam, (n, n, n-1)}`.
The injection simply flips the single fixed cell `(0, n)` from `0` to `1`. -/
private lemma kostka_unb_le_bal {N n : ℕ} (hn : 2 ≤ n) {lam : List ℕ}
    (hpart : IsPartitionOf N lam) :
    kostka lam 3 (wUnb n) ≤ kostka lam 3 (wBal n) := by
  unfold kostka
  let SUnb := @Finset.filter ((r : Fin lam.length) → Fin (lam.get r) → Fin 3)
    (fun T => IsSSYT lam 3 (wUnb n) T) (Classical.decPred _) Finset.univ
  let SBal := @Finset.filter ((r : Fin lam.length) → Fin (lam.get r) → Fin 3)
    (fun T => IsSSYT lam 3 (wBal n) T) (Classical.decPred _) Finset.univ
  change SUnb.card ≤ SBal.card
  by_cases hne : SUnb.Nonempty
  · -- From any `T₀ ∈ SUnb`, deduce `0 < lam.length` and `n < lam[0]`.
    rcases hne with ⟨T₀, hT₀_mem⟩
    have hT₀ : IsSSYT lam 3 (wUnb n) T₀ := ((@Finset.mem_filter _ _ (Classical.decPred _)).mp hT₀_mem).2
    have hcnt0 : (Finset.univ.filter
        (fun p : Sigma (fun r : Fin lam.length => Fin (lam.get r)) => T₀ p.1 p.2 = 0)).card =
        n + 1 := hT₀.2.2 0
    have hlen_pos : 0 < lam.length := by
      by_contra hlen
      have hlen0 : lam.length = 0 := by omega
      have hempty : (Finset.univ.filter
          (fun p : Sigma (fun r : Fin lam.length => Fin (lam.get r)) => T₀ p.1 p.2 = 0)) = ∅ := by
        ext p
        exact absurd p.1.isLt (by omega)
      rw [hempty, Finset.card_empty] at hcnt0
      omega
    let r0 : Fin lam.length := ⟨0, hlen_pos⟩
    have hrow0_gt : n < lam.get r0 := by
      have hsub : (Finset.univ.filter
          (fun p : Sigma (fun r : Fin lam.length => Fin (lam.get r)) => T₀ p.1 p.2 = 0)) ⊆
          Finset.univ.image (fun c : Fin (lam.get r0) => (⟨r0, c⟩ : Sigma (fun r : Fin lam.length => Fin (lam.get r)))) := by
        intro p hp
        have hp0 : T₀ p.1 p.2 = 0 := (Finset.mem_filter.mp hp).2
        have hr0 : p.1.val = 0 := ssyt_zero_row_zero hpart hT₀ p.1 p.2 (by rw [hp0]; rfl)
        have hpeq : p.1 = r0 := Fin.ext hr0
        rw [Finset.mem_image]
        rcases p with ⟨pr, pc⟩
        dsimp at hpeq
        subst hpeq
        exact ⟨pc, Finset.mem_univ _, rfl⟩
      have hle := Finset.card_le_card hsub
      rw [hcnt0] at hle
      have himg : (Finset.univ.image (fun c : Fin (lam.get r0) =>
          (⟨r0, c⟩ : Sigma (fun r : Fin lam.length => Fin (lam.get r))))).card ≤ lam.get r0 := by
        calc _ ≤ (Finset.univ : Finset (Fin (lam.get r0))).card := Finset.card_image_le
          _ = lam.get r0 := by simp
      omega
    let cn : Fin (lam.get r0) := ⟨n, hrow0_gt⟩
    -- Define the flip map `φ`: change cell `(r0, cn)` to `1`, keep all other cells unchanged.
    let φ : ((r : Fin lam.length) → Fin (lam.get r) → Fin 3) →
            ((r : Fin lam.length) → Fin (lam.get r) → Fin 3) :=
      fun T r c => if r.val = 0 ∧ c.val = n then 1 else T r c
    -- Key structural facts for any `T ∈ SUnb`:
    have hT_row0 : ∀ T, IsSSYT lam 3 (wUnb n) T →
        ∀ c : Fin (lam.get r0), T r0 c = 0 ↔ c.val ≤ n := by
      intro T hT
      -- Count how many `0`s are in row 0: every `0` in `T` is in row 0, so there are `n + 1` of them.
      let Z0 := Finset.univ.filter (fun c : Fin (lam.get r0) => T r0 c = 0)
      have hZ0_card : Z0.card = n + 1 := by
        have hbij : Z0.card = (Finset.univ.filter
            (fun p : Sigma (fun r : Fin lam.length => Fin (lam.get r)) => T p.1 p.2 = 0)).card := by
          apply Finset.card_bij (fun c _ => ⟨r0, c⟩)
          · intro c hc
            rw [Finset.mem_filter] at hc ⊢
            exact ⟨Finset.mem_univ _, hc.2⟩
          · intro c₁ _ c₂ _ h
            exact eq_of_heq (Sigma.mk.inj h).2
          · intro p hp
            rw [Finset.mem_filter] at hp
            have hr0 : p.1.val = 0 := ssyt_zero_row_zero hpart hT p.1 p.2 (by rw [hp.2]; rfl)
            have hpeq : p.1 = r0 := Fin.ext hr0
            rcases p with ⟨pr, pc⟩
            dsimp at hpeq
            subst hpeq
            exact ⟨pc, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2⟩, rfl⟩
        rw [hbij]
        exact hT.2.2 0
      -- `Z0` is downward closed because row 0 is weakly increasing.
      have hdown : ∀ c₁ c₂ : Fin (lam.get r0), c₁.val ≤ c₂.val → c₂ ∈ Z0 → c₁ ∈ Z0 := by
        intro c₁ c₂ hle hc₂
        rw [Finset.mem_filter] at hc₂ ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        have hleT : (T r0 c₁).val ≤ (T r0 c₂).val := hT.1 r0 c₁ c₂ hle
        rw [hc₂.2] at hleT
        apply Fin.ext
        change (T r0 c₁).val = 0
        omega
      -- Therefore `Z0 = {c | c.val ≤ n}`.
      let I0 := Finset.univ.filter (fun c : Fin (lam.get r0) => c.val ≤ n)
      have hI0_card : I0.card = n + 1 := by
        have hbij : I0.card = (Finset.univ : Finset (Fin (n + 1))).card := by
          apply Finset.card_bij (fun c hc => ⟨c.val, by
            have := (Finset.mem_filter.mp hc).2; omega⟩)
          · intro _ _; exact Finset.mem_univ _
          · intro c₁ _ c₂ _ h; exact Fin.ext (Fin.mk.inj h)
          · intro j _
            exact ⟨⟨j.val, lt_of_lt_of_le j.isLt hrow0_gt⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩, Fin.ext rfl⟩
        rw [hbij]; simp
      have hZ0_eq_I0 : Z0 = I0 := by
        by_contra hne_set
        -- Either there exists `c ∈ Z0` with `n < c.val` (making `I0 ⊂ Z0`, card ≥ n+2)
        -- or `Z0 ⊆ I0` (contradicting `Z0.card = I0.card` and `Z0 ≠ I0`).
        by_cases hsub : Z0 ⊆ I0
        · exact hne_set (Finset.eq_of_subset_of_card_le hsub (by rw [hZ0_card, hI0_card]))
        · rw [Finset.subset_iff] at hsub
          push Not at hsub
          rcases hsub with ⟨cmax, hcmax_Z, hcmax_nI⟩
          have hcmax_gt : n < cmax.val := by
            have : ¬ cmax.val ≤ n := fun h => hcmax_nI (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
            omega
          have hI0_sub : I0 ⊆ Z0 := by
            intro c hc
            exact hdown c cmax (by have := (Finset.mem_filter.mp hc).2; omega) hcmax_Z
          have hssub : I0 ⊂ Z0 := Finset.ssubset_iff_subset_ne.mpr ⟨hI0_sub, fun heq => hne_set heq.symm⟩
          have hlt := Finset.card_lt_card hssub
          omega
      intro c
      have hmem : c ∈ Z0 ↔ c ∈ I0 := by rw [hZ0_eq_I0]
      simpa [Z0, I0] using hmem
    -- If row 1 exists and has length > n, then `T r1 c = 2` at col `n`.
    have hT_row1_n : ∀ T, IsSSYT lam 3 (wUnb n) T →
        ∀ (r : Fin lam.length) (c : Fin (lam.get r)), 0 < r.val → c.val = n → 1 < (T r c).val := by
      intro T hT r c hrpos hcn
      by_contra hle1
      have hle1' : (T r c).val ≤ 1 := by omega
      have hr1 : r.val = 1 := by
        have h1 := ssyt_one_row_le_one hpart hT r c hle1'
        omega
      -- Every cell `(r, j)` with `j ≤ n` has `T r j ≤ T r c ≤ 1`, and `T r j ≠ 0` since `r.val = 1 > 0`,
      -- so `T r j = 1` for all `j = 0, ..., n` (`n + 1` cells!), contradicting `wUnb n 1 = n - 1`!
      have hcnt1 : (Finset.univ.filter
          (fun p : Sigma (fun r' : Fin lam.length => Fin (lam.get r')) => T p.1 p.2 = 1)).card =
          n - 1 := hT.2.2 1
      let cols := (Finset.univ : Finset (Fin (n + 1))).image (fun j =>
        (⟨r, ⟨j.val, lt_of_le_of_lt (by omega) c.isLt⟩⟩ : Sigma (fun r' : Fin lam.length => Fin (lam.get r'))))
      have hsub : cols ⊆ Finset.univ.filter
          (fun p : Sigma (fun r' : Fin lam.length => Fin (lam.get r')) => T p.1 p.2 = 1) := by
        intro p hp
        rw [Finset.mem_image] at hp
        rcases hp with ⟨j, _, rfl⟩
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have hle_j : (T r ⟨j.val, lt_of_le_of_lt (by omega) c.isLt⟩).val ≤ (T r c).val :=
          hT.1 r ⟨j.val, lt_of_le_of_lt (by omega) c.isLt⟩ c (by dsimp; omega)
        have hne0 : (T r ⟨j.val, lt_of_le_of_lt (by omega) c.isLt⟩).val ≠ 0 := by
          intro h0
          have := ssyt_zero_row_zero hpart hT r _ h0
          omega
        apply Fin.ext
        change (T r ⟨j.val, lt_of_le_of_lt (by omega) c.isLt⟩).val = 1
        omega
      have hcols_card : cols.card = n + 1 := by
        rw [Finset.card_image_of_injective]
        · simp
        · intro j₁ j₂ h
          have h2 := eq_of_heq (Sigma.mk.inj h).2
          exact Fin.ext (Fin.mk.inj h2)
      have hle := Finset.card_le_card hsub
      rw [hcols_card, hcnt1] at hle
      omega
    -- Now apply `Finset.card_le_card_of_injOn` with `φ`!
    apply Finset.card_le_card_of_injOn φ
    · intro T hT_mem
      have hT : IsSSYT lam 3 (wUnb n) T :=
        ((@Finset.mem_filter _ _ (Classical.decPred _)).mp (Finset.mem_coe.mp hT_mem)).2
      rw [Finset.mem_coe, @Finset.mem_filter _ _ (Classical.decPred _)]
      refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
      · -- Row weak monotonicity
        intro r c₁ c₂ hle
        dsimp [φ]
        split_ifs with h1 h2 h2
        · exact le_refl _
        · -- `r = 0, c₁ = n < c₂`: `T r c₂ ≠ 0`, so `1 ≤ T r c₂`!
          have hr0 : r = r0 := Fin.ext h1.1
          subst hr0
          have hne0 : T r0 c₂ ≠ 0 := by
            intro hz
            have := (hT_row0 T hT c₂).mp hz
            omega
          change (1 : ℕ) ≤ (T r0 c₂).val
          have : (T r0 c₂).val ≠ 0 := fun h => hne0 (Fin.ext h)
          omega
        · -- `r = 0, c₁ < c₂ = n`: `T r c₁ = 0 ≤ 1`!
          have hr0 : r = r0 := Fin.ext h2.1
          subst hr0
          have hz : T r0 c₁ = 0 := (hT_row0 T hT c₁).mpr (by omega)
          rw [hz]
          decide
        · exact hT.1 r c₁ c₂ hle
      · -- Column strict monotonicity
        intro r₁ r₂ c₁ c₂ hrlt hceq
        dsimp [φ]
        split_ifs with h1 h2 h2
        · omega
        · -- `r₁ = 0, c₁ = n, r₂ > 0, c₂ = n`: `1 < T r₂ c₂`!
          have hgt := hT_row1_n T hT r₂ c₂ (by omega) (by omega)
          exact hgt
        · omega
        · exact hT.2.1 r₁ r₂ c₁ c₂ hrlt hceq
      · -- Content of `φ T` equals `wBal n`!
        let p0 : Sigma (fun r : Fin lam.length => Fin (lam.get r)) := ⟨r0, cn⟩
        have hp0_T : T p0.1 p0.2 = 0 := (hT_row0 T hT cn).mpr (le_refl n)
        have hp0_φ : φ T p0.1 p0.2 = 1 := by simp [φ, p0, r0, cn]
        have hother : ∀ p : Sigma (fun r : Fin lam.length => Fin (lam.get r)),
            p ≠ p0 → φ T p.1 p.2 = T p.1 p.2 := by
          intro p hne
          dsimp [φ]
          split_ifs with h
          · exfalso; apply hne
            rcases p with ⟨pr, pc⟩
            have h1 : pr = r0 := Fin.ext h.1
            subst h1
            have h2 : pc = cn := Fin.ext h.2
            subst h2
            rfl
          · rfl
        intro col
        match col with
        | 0 =>
          have hset : Finset.univ.filter (fun p : Sigma (fun r : Fin lam.length => Fin (lam.get r)) => φ T p.1 p.2 = 0) =
              (Finset.univ.filter (fun p : Sigma (fun r : Fin lam.length => Fin (lam.get r)) => T p.1 p.2 = 0)).erase p0 := by
            ext p
            by_cases hp : p = p0
            · subst hp; simp [hp0_φ]
            · simp [hp, hother p hp]
          have hmem0 : p0 ∈ Finset.univ.filter (fun p : Sigma (fun r : Fin lam.length => Fin (lam.get r)) => T p.1 p.2 = 0) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp0_T⟩
          rw [hset, Finset.card_erase_of_mem hmem0]
          have h0 := hT.2.2 0
          dsimp [wUnb, wBal] at h0 ⊢
          omega
        | 1 =>
          have hset : Finset.univ.filter (fun p : Sigma (fun r : Fin lam.length => Fin (lam.get r)) => φ T p.1 p.2 = 1) =
              insert p0 (Finset.univ.filter (fun p : Sigma (fun r : Fin lam.length => Fin (lam.get r)) => T p.1 p.2 = 1)) := by
            ext p
            by_cases hp : p = p0
            · subst hp; simp [hp0_φ]
            · simp [hp, hother p hp]
          have hnotmem : p0 ∉ Finset.univ.filter (fun p : Sigma (fun r : Fin lam.length => Fin (lam.get r)) => T p.1 p.2 = 1) := by
            simp [hp0_T]
          rw [hset, Finset.card_insert_of_notMem hnotmem]
          have h1 := hT.2.2 1
          dsimp [wUnb, wBal] at h1 ⊢
          omega
        | 2 =>
          have hset : Finset.univ.filter (fun p : Sigma (fun r : Fin lam.length => Fin (lam.get r)) => φ T p.1 p.2 = 2) =
              Finset.univ.filter (fun p : Sigma (fun r : Fin lam.length => Fin (lam.get r)) => T p.1 p.2 = 2) := by
            ext p
            by_cases hp : p = p0
            · subst hp; simp [hp0_φ, hp0_T]
            · simp [hother p hp]
          rw [hset]
          exact hT.2.2 2
    · -- Injectivity of `φ` on `SUnb`
      intro T₁ hT₁_mem T₂ hT₂_mem hφ
      have hT₁ : IsSSYT lam 3 (wUnb n) T₁ :=
        ((@Finset.mem_filter _ _ (Classical.decPred _)).mp (Finset.mem_coe.mp hT₁_mem)).2
      have hT₂ : IsSSYT lam 3 (wUnb n) T₂ :=
        ((@Finset.mem_filter _ _ (Classical.decPred _)).mp (Finset.mem_coe.mp hT₂_mem)).2
      funext r c
      by_cases hrc : r.val = 0 ∧ c.val = n
      · have hr0 : r = r0 := Fin.ext hrc.1
        subst hr0
        have hc0 : c = cn := Fin.ext hrc.2
        subst hc0
        rw [(hT_row0 T₁ hT₁ cn).mpr (le_refl n), (hT_row0 T₂ hT₂ cn).mpr (le_refl n)]
      · have heval := congrFun (congrFun hφ r) c
        simpa [φ, hrc] using heval
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    exact Nat.zero_le _

/-! ### Part 2: Exact proper 3-coloring counts on `squidGraph n` -/

/-- Helper: in any proper 3-coloring of `squidGraph n`, every color appears at most `n - 1`
times on the odd cycle `C_{2n - 1}` (`v < 2n - 1`). -/
private lemma cycle_color_card_le {n : ℕ} (hn : 3 ≤ n)
    {f : Fin (3 * n - 1) → Fin 3} (hf : ∀ u v, (squidGraph n).Adj u v → f u ≠ f v)
    (c : Fin 3) :
    (Finset.univ.filter (fun v : Fin (3 * n - 1) => v.val < 2 * n - 1 ∧ f v = c)).card ≤ n - 1 := by
  let Sc := Finset.univ.filter (fun v : Fin (3 * n - 1) => v.val < 2 * n - 1 ∧ f v = c)
  by_cases hlast : f ⟨2 * n - 2, by omega⟩ = c
  · -- Then `f 0 ≠ c` and `f (2n - 3) ≠ c` (both adjacent to `2n - 2`), so map `Sc \ {2n - 2}` to `Fin (n - 2)`.
    have h0ne : f ⟨0, by omega⟩ ≠ c := by
      rw [← hlast]
      exact hf ⟨0, by omega⟩ ⟨2 * n - 2, by omega⟩
        (Or.inl ⟨by dsimp; omega, by dsimp; omega, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by omega⟩))⟩)
    have hprevne : f ⟨2 * n - 3, by omega⟩ ≠ c := by
      rw [← hlast]
      exact hf ⟨2 * n - 3, by omega⟩ ⟨2 * n - 2, by omega⟩
        (Or.inl ⟨by dsimp; omega, by dsimp; omega, Or.inl (by dsimp; omega)⟩)
    let Sc' := Sc.erase ⟨2 * n - 2, by omega⟩
    have hSc'_le : Sc'.card ≤ n - 2 := by
      let g : Fin (3 * n - 1) → Fin (n - 2) := fun v =>
        if hv : 1 ≤ v.val ∧ v.val < 2 * n - 3 then ⟨(v.val - 1) / 2, by omega⟩ else ⟨0, by omega⟩
      have hinj : Set.InjOn g (Sc' : Set (Fin (3 * n - 1))) := by
        intro u hu v hv hguv
        have hu' := Finset.mem_erase.mp (Finset.mem_coe.mp hu)
        have hv' := Finset.mem_erase.mp (Finset.mem_coe.mp hv)
        have huS := (Finset.mem_filter.mp hu'.2).2
        have hvS := (Finset.mem_filter.mp hv'.2).2
        have hu_ne0 : u.val ≠ 0 := by intro h; have heq : u = ⟨0, by omega⟩ := Fin.ext h; exact h0ne (heq ▸ huS.2)
        have hv_ne0 : v.val ≠ 0 := by intro h; have heq : v = ⟨0, by omega⟩ := Fin.ext h; exact h0ne (heq ▸ hvS.2)
        have hu_neP : u.val ≠ 2 * n - 3 := by intro h; have heq : u = ⟨2 * n - 3, by omega⟩ := Fin.ext h; exact hprevne (heq ▸ huS.2)
        have hv_neP : v.val ≠ 2 * n - 3 := by intro h; have heq : v = ⟨2 * n - 3, by omega⟩ := Fin.ext h; exact hprevne (heq ▸ hvS.2)
        have hu_neL : u.val ≠ 2 * n - 2 := fun h => hu'.1 (Fin.ext h)
        have hv_neL : v.val ≠ 2 * n - 2 := fun h => hv'.1 (Fin.ext h)
        have hu_rng : 1 ≤ u.val ∧ u.val < 2 * n - 3 := by omega
        have hv_rng : 1 ≤ v.val ∧ v.val < 2 * n - 3 := by omega
        simp only [g, dif_pos hu_rng, dif_pos hv_rng, Fin.mk.injEq] at hguv
        by_contra hne
        have hval_ne : u.val ≠ v.val := fun h => hne (Fin.ext h)
        have hadj : (squidGraph n).Adj u v := Or.inl ⟨huS.1, hvS.1, by omega⟩
        exact hf u v hadj (huS.2.trans hvS.2.symm)
      calc Sc'.card = (Sc'.image g).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.univ : Finset (Fin (n - 2))).card := Finset.card_le_univ _
        _ = n - 2 := by simp
    have hmem : (⟨2 * n - 2, by omega⟩ : Fin (3 * n - 1)) ∈ Sc :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega, hlast⟩
    have hcard : Sc'.card = Sc.card - 1 := Finset.card_erase_of_mem hmem
    change Sc.card ≤ n - 1
    omega
  · -- `f (2n - 2) ≠ c`: map every `v ∈ Sc` to `v / 2 : Fin (n - 1)`!
    let g : Fin (3 * n - 1) → Fin (n - 1) := fun v =>
      if hv : v.val < 2 * n - 2 then ⟨v.val / 2, by omega⟩ else ⟨0, by omega⟩
    have hinj : Set.InjOn g (Sc : Set (Fin (3 * n - 1))) := by
      intro u hu v hv hguv
      have huS := (Finset.mem_filter.mp (Finset.mem_coe.mp hu)).2
      have hvS := (Finset.mem_filter.mp (Finset.mem_coe.mp hv)).2
      have hu_neL : u.val ≠ 2 * n - 2 := by intro h; have heq : u = ⟨2 * n - 2, by omega⟩ := Fin.ext h; exact hlast (heq ▸ huS.2)
      have hv_neL : v.val ≠ 2 * n - 2 := by intro h; have heq : v = ⟨2 * n - 2, by omega⟩ := Fin.ext h; exact hlast (heq ▸ hvS.2)
      have hu_lt : u.val < 2 * n - 2 := by omega
      have hv_lt : v.val < 2 * n - 2 := by omega
      simp only [g, dif_pos hu_lt, dif_pos hv_lt, Fin.mk.injEq] at hguv
      by_contra hne
      have hval_ne : u.val ≠ v.val := fun h => hne (Fin.ext h)
      have hadj : (squidGraph n).Adj u v := Or.inl ⟨huS.1, hvS.1, by omega⟩
      exact hf u v hadj (huS.2.trans hvS.2.symm)
    calc Sc.card = (Sc.image g).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.univ : Finset (Fin (n - 1))).card := Finset.card_le_univ _
      _ = n - 1 := by simp

/-- If the hub vertex `0` has color `c0`, then color `c0` cannot appear on any leaf,
so its total count equals its cycle count `≤ n - 1`. -/
private lemma hub_color_card_le {n : ℕ} (hn : 3 ≤ n)
    {f : Fin (3 * n - 1) → Fin 3} (hf : ∀ u v, (squidGraph n).Adj u v → f u ≠ f v)
    {c0 : Fin 3} (hhub : f ⟨0, by omega⟩ = c0) :
    (Finset.univ.filter (fun v : Fin (3 * n - 1) => f v = c0)).card ≤ n - 1 := by
  have heq : Finset.univ.filter (fun v : Fin (3 * n - 1) => f v = c0) =
      Finset.univ.filter (fun v : Fin (3 * n - 1) => v.val < 2 * n - 1 ∧ f v = c0) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hv
      refine ⟨?_, hv⟩
      by_contra hge
      have hadj : (squidGraph n).Adj ⟨0, by omega⟩ v := Or.inr (Or.inl ⟨rfl, by omega⟩)
      exact hf _ _ hadj (hhub.trans hv.symm)
    · exact And.right
  rw [heq]
  exact cycle_color_card_le hn hf c0

/-- Canonical independent set `I(n, r)` of size `n - 1` on `C_{2n - 1}` containing `0`:
`{2j | j ≤ r} ∪ {2j + 1 | r < j < n - 1}`. -/
private def canonIndep (n : ℕ) (r : Fin (n - 1)) (v : Fin (3 * n - 1)) : Prop :=
  v.val < 2 * n - 1 ∧
    ((v.val % 2 = 0 ∧ v.val ≤ 2 * r.val) ∨
     (v.val % 2 = 1 ∧ 2 * r.val + 3 ≤ v.val))

private instance (n : ℕ) (r : Fin (n - 1)) : DecidablePred (canonIndep n r) := by
  intro v; unfold canonIndep; infer_instance

/-- Every proper 3-coloring of `squidGraph n` whose hub color `c0` occurs `n - 1` times
has `{v | f v = c0} = canonIndep n r` for a unique `r : Fin (n - 1)`. -/
private lemma hub_color_fiber_eq_canon {n : ℕ} (hn : 3 ≤ n)
    {f : Fin (3 * n - 1) → Fin 3} (hf : ∀ u v, (squidGraph n).Adj u v → f u ≠ f v)
    {c0 : Fin 3} (hhub : f ⟨0, by omega⟩ = c0)
    (hcard : (Finset.univ.filter (fun v : Fin (3 * n - 1) => f v = c0)).card = n - 1) :
    ∃! r : Fin (n - 1), ∀ v : Fin (3 * n - 1), f v = c0 ↔ canonIndep n r v := by
  -- No leaf has color `c0`, and `2n - 2` does not have color `c0` (adjacent to hub `0`).
  have hlt_2n2 : ∀ v : Fin (3 * n - 1), f v = c0 → v.val < 2 * n - 2 := by
    intro v hv
    by_contra hge
    by_cases heq : v.val = 2 * n - 2
    · have hadj : (squidGraph n).Adj ⟨0, by omega⟩ v :=
        Or.inl ⟨by dsimp; omega, by omega, Or.inr (Or.inr (Or.inl ⟨rfl, heq, by omega⟩))⟩
      exact hf _ _ hadj (hhub.trans hv.symm)
    · have hadj : (squidGraph n).Adj ⟨0, by omega⟩ v := Or.inr (Or.inl ⟨rfl, by omega⟩)
      exact hf _ _ hadj (hhub.trans hv.symm)
  -- In each pair `{2j, 2j + 1}` (`0 ≤ j < n - 1`), `f` hits `c0` at most once; since there are
  -- `n - 1` hits total, `f` hits `c0` EXACTLY once in every pair `{2j, 2j + 1}`!
  let Sc := Finset.univ.filter (fun v : Fin (3 * n - 1) => f v = c0)
  let proj : Fin (3 * n - 1) → Fin (n - 1) := fun v =>
    if hv : v.val < 2 * n - 2 then ⟨v.val / 2, by omega⟩ else ⟨0, by omega⟩
  have hinj : Set.InjOn proj (Sc : Set (Fin (3 * n - 1))) := by
    intro u hu v hv hpu
    have hu0 : f u = c0 := (Finset.mem_filter.mp (Finset.mem_coe.mp hu)).2
    have hv0 : f v = c0 := (Finset.mem_filter.mp (Finset.mem_coe.mp hv)).2
    have hult := hlt_2n2 u hu0
    have hvlt := hlt_2n2 v hv0
    simp only [proj, dif_pos hult, dif_pos hvlt, Fin.mk.injEq] at hpu
    by_contra hne
    have hval : u.val ≠ v.val := fun h => hne (Fin.ext h)
    have hadj : (squidGraph n).Adj u v := Or.inl ⟨by omega, by omega, by omega⟩
    exact hf u v hadj (hu0.trans hv0.symm)
  have himg_eq : Sc.image proj = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_image_of_injOn hinj]
    simp [Sc, hcard]
  -- Hence for every `j : Fin (n - 1)`, either `f (2j) = c0` or `f (2j + 1) = c0` (exclusively).
  have hpair : ∀ j : Fin (n - 1),
      (f ⟨2 * j.val, by omega⟩ = c0 ∧ f ⟨2 * j.val + 1, by omega⟩ ≠ c0) ∨
      (f ⟨2 * j.val, by omega⟩ ≠ c0 ∧ f ⟨2 * j.val + 1, by omega⟩ = c0) := by
    intro j
    have hj_mem : j ∈ Sc.image proj := by rw [himg_eq]; exact Finset.mem_univ j
    rcases Finset.mem_image.mp hj_mem with ⟨v, hv_mem, hv_eq⟩
    have hv0 : f v = c0 := (Finset.mem_filter.mp hv_mem).2
    have hvlt := hlt_2n2 v hv0
    simp only [proj, dif_pos hvlt] at hv_eq
    have hdiv : v.val / 2 = j.val := congrArg Fin.val hv_eq
    have hadj : (squidGraph n).Adj ⟨2 * j.val, by omega⟩ ⟨2 * j.val + 1, by omega⟩ :=
      Or.inl ⟨by dsimp; omega, by dsimp; omega, Or.inl rfl⟩
    have hne := hf _ _ hadj
    by_cases hmod : v.val % 2 = 0
    · have hv_e : v = ⟨2 * j.val, by omega⟩ := Fin.ext (by dsimp; omega)
      rw [hv_e] at hv0
      exact Or.inl ⟨hv0, fun h => hne (hv0.trans h.symm)⟩
    · have hv_o : v = ⟨2 * j.val + 1, by omega⟩ := Fin.ext (by dsimp; omega)
      rw [hv_o] at hv0
      exact Or.inr ⟨fun h => hne (h.trans hv0.symm), hv0⟩
  -- Monotonicity: if `f (2j + 1) = c0`, then `f (2(j+1)) ≠ c0`, so `f (2(j+1) + 1) = c0`!
  have hmono : ∀ j : ℕ, (hj : j + 1 < n - 1) →
      f ⟨2 * j + 1, by omega⟩ = c0 → f ⟨2 * (j + 1) + 1, by omega⟩ = c0 := by
    intro j hj hodd
    have hadj : (squidGraph n).Adj ⟨2 * j + 1, by omega⟩ ⟨2 * (j + 1), by omega⟩ :=
      Or.inl ⟨by dsimp; omega, by dsimp; omega, Or.inl (by dsimp; omega)⟩
    have hne : f ⟨2 * (j + 1), by omega⟩ ≠ c0 := fun h => hf _ _ hadj (hodd.trans h.symm)
    rcases hpair ⟨j + 1, hj⟩ with ⟨he, _⟩ | ⟨_, ho⟩
    · exact absurd he hne
    · exact ho
  have hmono_le : ∀ j₁ j₂ : ℕ, (hle : j₁ ≤ j₂) → (hj₂ : j₂ < n - 1) →
      f ⟨2 * j₁ + 1, by omega⟩ = c0 → f ⟨2 * j₂ + 1, by omega⟩ = c0 := by
    intro j₁ j₂ hle hj₂ h1
    induction j₂ with
    | zero =>
      have : j₁ = 0 := by omega
      subst this; exact h1
    | succ k ih =>
      by_cases hlt : j₁ ≤ k
      · exact hmono k hj₂ (ih hlt (by omega) h1)
      · have : j₁ = k + 1 := by omega
        subst this; exact h1
  -- Let `r` be the maximum `j < n - 1` with `f (2j) = c0` (well-defined since `j = 0` works!).
  let evens := Finset.univ.filter (fun j : Fin (n - 1) => f ⟨2 * j.val, by omega⟩ = c0)
  have hevens_ne : evens.Nonempty := ⟨⟨0, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hhub⟩⟩
  let r : Fin (n - 1) := evens.max' hevens_ne
  have hr_even : f ⟨2 * r.val, by omega⟩ = c0 := (Finset.mem_filter.mp (Finset.max'_mem evens hevens_ne)).2
  have hle_r : ∀ j : Fin (n - 1), j.val ≤ r.val → f ⟨2 * j.val, by omega⟩ = c0 := by
    intro j hj
    rcases hpair j with ⟨he, _⟩ | ⟨_, ho⟩
    · exact he
    · exfalso
      have hrodd := hmono_le j.val r.val hj r.isLt ho
      rcases hpair r with ⟨_, hno⟩ | ⟨hne, _⟩
      · exact hno hrodd
      · exact hne hr_even
  have hgt_r : ∀ j : Fin (n - 1), r.val < j.val → f ⟨2 * j.val + 1, by omega⟩ = c0 := by
    intro j hj
    rcases hpair j with ⟨he, _⟩ | ⟨_, ho⟩
    · exfalso
      have hmem : j ∈ evens := Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
      have hle := Finset.le_max' evens j hmem
      have : j.val ≤ r.val := hle
      omega
    · exact ho
  refine ⟨r, ?_, ?_⟩
  · intro v
    constructor
    · intro hv
      have hvlt := hlt_2n2 v hv
      refine ⟨by omega, ?_⟩
      let j : Fin (n - 1) := ⟨v.val / 2, by omega⟩
      by_cases hmod : v.val % 2 = 0
      · left
        refine ⟨hmod, ?_⟩
        by_contra hgt
        have hjgt : r.val < j.val := by dsimp [j]; omega
        have ho := hgt_r j hjgt
        have hv_eq : v = ⟨2 * j.val, by omega⟩ := Fin.ext (by dsimp [j]; omega)
        rw [hv_eq] at hv
        rcases hpair j with ⟨_, hno⟩ | ⟨hne, _⟩
        · exact hno ho
        · exact hne hv
      · right
        refine ⟨by omega, ?_⟩
        by_contra hle
        have hjle : j.val ≤ r.val := by dsimp [j]; omega
        have he := hle_r j hjle
        have hv_eq : v = ⟨2 * j.val + 1, by omega⟩ := Fin.ext (by dsimp [j]; omega)
        rw [hv_eq] at hv
        rcases hpair j with ⟨_, hno⟩ | ⟨hne, _⟩
        · exact hno hv
        · exact hne he
    · intro hcan
      rcases hcan with ⟨hvlt, ⟨hmod, hle⟩ | ⟨hmod, hge⟩⟩
      · have hjlt : v.val / 2 < n - 1 := by omega
        have he := hle_r ⟨v.val / 2, hjlt⟩ (by dsimp; omega)
        convert he using 2
        exact Fin.ext (by dsimp; omega)
      · have hjlt : v.val / 2 < n - 1 := by omega
        have ho := hgt_r ⟨v.val / 2, hjlt⟩ (by dsimp; omega)
        convert ho using 2
        exact Fin.ext (by dsimp; omega)
  · intro r' hr'
    by_contra hne
    have hval_ne : r'.val ≠ r.val := fun h => hne (Fin.ext h)
    by_cases hlt : r'.val < r.val
    · have h1 := (hr' ⟨2 * r.val, by omega⟩).mp hr_even
      unfold canonIndep at h1
      dsimp at h1
      omega
    · have hr'_even : f ⟨2 * r'.val, by omega⟩ = c0 :=
        (hr' ⟨2 * r'.val, by omega⟩).mpr ⟨by dsimp; omega, Or.inl ⟨by dsimp; omega, by dsimp; omega⟩⟩
      have hmem : r' ∈ evens := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr'_even⟩
      have hle : r'.val ≤ r.val := Finset.le_max' evens r' hmem
      omega

private lemma fin3_exhaustive :
    ∀ (c0 c1 c2 : Fin 3), c0 ≠ c1 → c0 ≠ c2 → c1 ≠ c2 →
    ∀ x : Fin 3, x = c0 ∨ x = c1 ∨ x = c2 := by
  decide

private lemma fin3_ne_iff :
    ∀ (c0 c1 c2 x y : Fin 3), c0 ≠ c1 → c0 ≠ c2 → c1 ≠ c2 →
    x ≠ c0 → y ≠ c0 → x ≠ y → (y = c1 ↔ x ≠ c1) := by
  decide

private lemma fin3_eq_of_iff :
    ∀ (c0 c1 c2 x y : Fin 3), c0 ≠ c1 → c0 ≠ c2 → c1 ≠ c2 →
    x ≠ c0 → y ≠ c0 → (x = c1 ↔ y = c1) → x = y := by
  decide

/-- Exact count of proper 3-colorings of `squidGraph n` with hub color `c0`, fixed
`canonIndep n r` as the `c0`-fiber, and `m` occurrences of color `c1` (the other two colors
being `c1, c2`, with `c0, c1, c2` pairwise distinct and `1 ≤ m ≤ 2n - 1`). -/
private lemma count_fixed_r {n : ℕ} (hn : 3 ≤ n) (r : Fin (n - 1))
    (c0 c1 c2 : Fin 3) (h01 : c0 ≠ c1) (h02 : c0 ≠ c2) (h12 : c1 ≠ c2)
    (m : ℕ) (hm1 : 1 ≤ m) (hm2 : m ≤ 2 * n - 1) :
    (@Finset.filter (Fin (3 * n - 1) → Fin 3)
      (fun f => (∀ u v, (squidGraph n).Adj u v → f u ≠ f v) ∧
        (∀ v, f v = c0 ↔ canonIndep n r v) ∧
        (Finset.univ.filter (fun v => f v = c1)).card = m)
      (Classical.decPred _) Finset.univ).card =
    2 * Nat.choose (2 * n - 2) (m - 1) := by
  let pA : Fin (3 * n - 1) := ⟨2 * r.val + 1, by omega⟩
  let pB : Fin (3 * n - 1) := ⟨2 * r.val + 2, by omega⟩
  have hpAB_ne : pA ≠ pB := by intro h; have := congrArg Fin.val h; dsimp [pA, pB] at this; omega
  have hpA_nc : ¬ canonIndep n r pA := by unfold canonIndep; dsimp [pA]; omega
  have hpB_nc : ¬ canonIndep n r pB := by unfold canonIndep; dsimp [pB]; omega
  -- The remaining `2n - 2` free vertices outside `canonIndep n r ∪ {pA, pB}`.
  let Free : Finset (Fin (3 * n - 1)) :=
    Finset.univ.filter (fun v => ¬ canonIndep n r v ∧ v ≠ pA ∧ v ≠ pB)
  have hI_card : (Finset.univ.filter (fun v : Fin (3 * n - 1) => canonIndep n r v)).card = n - 1 := by
    have hbij : (Finset.univ.filter (fun v : Fin (3 * n - 1) => canonIndep n r v)).card =
        (Finset.univ : Finset (Fin (n - 1))).card := by
      apply Finset.card_bij (fun v hv => ⟨v.val / 2, by
        have hv' := (Finset.mem_filter.mp hv).2; unfold canonIndep at hv'; omega⟩)
      · intro _ _; exact Finset.mem_univ _
      · intro u hu v hv h
        have hu' := (Finset.mem_filter.mp hu).2
        have hv' := (Finset.mem_filter.mp hv).2
        have hdiv : u.val / 2 = v.val / 2 := Fin.mk.inj h
        unfold canonIndep at hu' hv'
        apply Fin.ext; omega
      · intro j _
        by_cases hj : j.val ≤ r.val
        · refine ⟨⟨2 * j.val, by omega⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by unfold canonIndep; dsimp; omega⟩,
            Fin.ext (by dsimp; omega)⟩
        · refine ⟨⟨2 * j.val + 1, by omega⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by unfold canonIndep; dsimp; omega⟩,
            Fin.ext (by dsimp; omega)⟩
    rw [hbij]; simp
  have hFree_card : Free.card = 2 * n - 2 := by
    let Iset := Finset.univ.filter (fun v : Fin (3 * n - 1) => canonIndep n r v)
    let AB : Finset (Fin (3 * n - 1)) := {pA, pB}
    have hdisj : Disjoint Iset AB := by
      rw [Finset.disjoint_right]
      intro v hv
      simp only [AB, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · simp [Iset, hpA_nc]
      · simp [Iset, hpB_nc]
    have hAB_card : AB.card = 2 := Finset.card_pair hpAB_ne
    have hcompl : Free = Finset.univ \ (Iset ∪ AB) := by
      ext v
      simp only [Free, Iset, AB, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [hcompl, Finset.card_sdiff]
    have hsub : (Iset ∪ AB) ∩ Finset.univ = Iset ∪ AB := Finset.inter_univ _
    rw [hsub, Finset.card_union_of_disjoint hdisj, hI_card, hAB_card]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  -- Key graph property: the ONLY edge outside `canonIndep n r` is `{pA, pB}`!
  have honly_edge : ∀ u v : Fin (3 * n - 1),
      ¬ canonIndep n r u → ¬ canonIndep n r v →
      (squidGraph n).Adj u v → (u = pA ∧ v = pB) ∨ (u = pB ∧ v = pA) := by
    intro u v hu hv hadj
    unfold canonIndep at hu hv
    rcases hadj with ⟨hu1, hv1, h1 | h2 | h3 | h4⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · by_cases hcase : u.val = 2 * r.val + 1
      · left; exact ⟨Fin.ext hcase, Fin.ext (by dsimp [pB]; omega)⟩
      · omega
    · by_cases hcase : v.val = 2 * r.val + 1
      · right; exact ⟨Fin.ext (by dsimp [pB]; omega), Fin.ext hcase⟩
      · omega
    · exfalso; apply hu; exact ⟨hu1, Or.inl ⟨by omega, by omega⟩⟩
    · exfalso; apply hv; exact ⟨hv1, Or.inl ⟨by omega, by omega⟩⟩
    · exfalso; apply hu; exact ⟨by omega, Or.inl ⟨by omega, by omega⟩⟩
    · exfalso; apply hv; exact ⟨by omega, Or.inl ⟨by omega, by omega⟩⟩
  have hpAB_adj : (squidGraph n).Adj pA pB :=
    Or.inl ⟨by dsimp [pA]; omega, by dsimp [pB]; omega, Or.inl (by dsimp [pA, pB])⟩
  -- Bijection between valid colorings `f` and `Bool × (Free.powersetCard (m - 1))`!
  -- `b = true` means `f pA = c1, f pB = c2`; `b = false` means `f pA = c2, f pB = c1`.
  -- `S ∈ Free.powersetCard (m - 1)` is `{v ∈ Free | f v = c1}`.
  let Target := @Finset.filter (Fin (3 * n - 1) → Fin 3)
    (fun f => (∀ u v, (squidGraph n).Adj u v → f u ≠ f v) ∧
      (∀ v, f v = c0 ↔ canonIndep n r v) ∧
      (Finset.univ.filter (fun v => f v = c1)).card = m)
    (Classical.decPred _) Finset.univ
  have hbij : Target.card = ((Finset.univ : Finset Bool) ×ˢ Free.powersetCard (m - 1)).card := by
    apply Finset.card_bij
      (fun f _ => (decide (f pA = c1), Free.filter (fun v => f v = c1)))
    · intro f hf
      rw [@Finset.mem_filter _ _ (Classical.decPred _)] at hf
      rcases hf.2 with ⟨hprop, hfib, hmc⟩
      rw [Finset.mem_product, Finset.mem_powersetCard]
      refine ⟨Finset.mem_univ _, Finset.filter_subset _ _, ?_⟩
      -- Either `f pA = c1` and `f pB = c2`, or `f pA = c2` and `f pB = c1`; in both cases
      -- exactly ONE of `pA, pB` has color `c1`, and all other `c1`-vertices lie in `Free`!
      have hne0_A : f pA ≠ c0 := fun h => hpA_nc ((hfib pA).mp h)
      have hne0_B : f pB ≠ c0 := fun h => hpB_nc ((hfib pB).mp h)
      have hneAB : f pA ≠ f pB := hprop pA pB hpAB_adj
      have hcases3 : ∀ x : Fin 3, x = c0 ∨ x = c1 ∨ x = c2 := fin3_exhaustive c0 c1 c2 h01 h02 h12
      have hAB_one : (f pA = c1 ∧ f pB ≠ c1) ∨ (f pA ≠ c1 ∧ f pB = c1) := by
        rcases hcases3 (f pA) with hA | hA | hA
        · exact absurd hA hne0_A
        · exact Or.inl ⟨hA, fun hB => hneAB (hA.trans hB.symm)⟩
        · rcases hcases3 (f pB) with hB | hB | hB
          · exact absurd hB hne0_B
          · exact Or.inr ⟨fun h => h12 (h.symm.trans hA), hB⟩
          · exact absurd (hA.trans hB.symm) hneAB
      have hsplit : ∀ w : Fin (3 * n - 1), (w = pA ∨ w = pB) → f w = c1 →
          (∀ w' : Fin (3 * n - 1), (w' = pA ∨ w' = pB) → w' ≠ w → f w' ≠ c1) →
          (Free.filter (fun v => f v = c1)).card = m - 1 := by
        intro w hw hfw hother
        have hset : Free.filter (fun v => f v = c1) =
            (Finset.univ.filter (fun v => f v = c1)).erase w := by
          ext v
          simp only [Free, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
          constructor
          · rintro ⟨⟨_, hvA, hvB⟩, hfv⟩
            refine ⟨?_, hfv⟩
            rcases hw with rfl | rfl <;> assumption
          · rintro ⟨hvw, hfv⟩
            refine ⟨⟨fun hcan => h01 (((hfib v).mpr hcan).symm.trans hfv), ?_, ?_⟩, hfv⟩
            · intro hvA; subst hvA
              exact hother pA (Or.inl rfl) hvw hfv
            · intro hvB; subst hvB
              exact hother pB (Or.inr rfl) hvw hfv
        have hmemw : w ∈ Finset.univ.filter (fun v => f v = c1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfw⟩
        rw [hset, Finset.card_erase_of_mem hmemw, hmc]
      rcases hAB_one with ⟨hA, hB⟩ | ⟨hA, hB⟩
      · exact hsplit pA (Or.inl rfl) hA (by intro w' hw' hne; rcases hw' with rfl | rfl; exact absurd rfl hne; exact hB)
      · exact hsplit pB (Or.inr rfl) hB (by intro w' hw' hne; rcases hw' with rfl | rfl; exact hA; exact absurd rfl hne)
    · -- Injectivity
      intro f₁ hf₁ f₂ hf₂ heq
      rw [@Finset.mem_filter _ _ (Classical.decPred _)] at hf₁ hf₂
      rcases hf₁.2 with ⟨hprop₁, hfib₁, _⟩
      rcases hf₂.2 with ⟨hprop₂, hfib₂, _⟩
      have hb : decide (f₁ pA = c1) = decide (f₂ pA = c1) := congrArg Prod.fst heq
      have hS : Free.filter (fun v => f₁ v = c1) = Free.filter (fun v => f₂ v = c1) := congrArg Prod.snd heq
      have hcases3 : ∀ x : Fin 3, x = c0 ∨ x = c1 ∨ x = c2 := fin3_exhaustive c0 c1 c2 h01 h02 h12
      funext v
      by_cases hcan : canonIndep n r v
      · rw [(hfib₁ v).mpr hcan, (hfib₂ v).mpr hcan]
      · have hv₁ : f₁ v ≠ c0 := fun h => hcan ((hfib₁ v).mp h)
        have hv₂ : f₂ v ≠ c0 := fun h => hcan ((hfib₂ v).mp h)
        have heq_c1 : f₁ v = c1 ↔ f₂ v = c1 := by
          by_cases hvA : v = pA
          · subst hvA
            simpa using congrArg (· = true) hb
          · by_cases hvB : v = pB
            · subst hvB
              have hneA1 : f₁ pA ≠ c0 := fun h => hpA_nc ((hfib₁ pA).mp h)
              have hneA2 : f₂ pA ≠ c0 := fun h => hpA_nc ((hfib₂ pA).mp h)
              have h1 : f₁ pB = c1 ↔ f₁ pA ≠ c1 :=
                fin3_ne_iff c0 c1 c2 (f₁ pA) (f₁ pB) h01 h02 h12 hneA1 hv₁ (hprop₁ pA pB hpAB_adj)
              have h2 : f₂ pB = c1 ↔ f₂ pA ≠ c1 :=
                fin3_ne_iff c0 c1 c2 (f₂ pA) (f₂ pB) h01 h02 h12 hneA2 hv₂ (hprop₂ pA pB hpAB_adj)
              rw [h1, h2]
              have hAeq : f₁ pA = c1 ↔ f₂ pA = c1 := by simpa using congrArg (· = true) hb
              tauto
            · have hvF : v ∈ Free := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcan, hvA, hvB⟩
              have := Finset.ext_iff.mp hS v
              simpa [hvF] using this
        exact fin3_eq_of_iff c0 c1 c2 (f₁ v) (f₂ v) h01 h02 h12 hv₁ hv₂ heq_c1
    · -- Surjectivity: construct `f` from `(b, S)`!
      rintro ⟨b, S⟩ hbS
      rw [Finset.mem_product, Finset.mem_powersetCard] at hbS
      rcases hbS with ⟨_, hS_sub, hS_card⟩
      let f : Fin (3 * n - 1) → Fin 3 := fun v =>
        if canonIndep n r v then c0
        else if v = pA then (if b then c1 else c2)
        else if v = pB then (if b then c2 else c1)
        else if v ∈ S then c1 else c2
      have hfib : ∀ v, f v = c0 ↔ canonIndep n r v := by
        intro v
        by_cases h1 : canonIndep n r v
        · simp [f, h1]
        · by_cases h2 : v = pA
          · subst h2; cases b <;> simp [f, hpA_nc, h01.symm, h02.symm]
          · by_cases h3 : v = pB
            · subst h3; cases b <;> simp [f, hpB_nc, hpAB_ne.symm, h01.symm, h02.symm]
            · by_cases h4 : v ∈ S
              · simp [f, h1, h2, h3, h4, h01.symm]
              · simp [f, h1, h2, h3, h4, h02.symm]
      have hprop : ∀ u v, (squidGraph n).Adj u v → f u ≠ f v := by
        intro u v hadj
        by_cases hu : canonIndep n r u
        · by_cases hv : canonIndep n r v
          · -- `canonIndep n r` is an independent set!
            exfalso
            unfold canonIndep at hu hv
            rcases hadj with ⟨_, _, h1 | h2 | h3 | h4⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
          · rw [(hfib u).mpr hu]
            exact fun h => hv ((hfib v).mp h.symm)
        · by_cases hv : canonIndep n r v
          · rw [(hfib v).mpr hv]
            exact fun h => hu ((hfib u).mp h)
          · rcases honly_edge u v hu hv hadj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · dsimp [f]
              rw [if_neg hpA_nc, if_neg hpB_nc, if_pos rfl, if_neg hpAB_ne.symm, if_pos rfl]
              cases b <;> simp [h12, h12.symm]
            · dsimp [f]
              rw [if_neg hpB_nc, if_neg hpA_nc, if_neg hpAB_ne.symm, if_pos rfl, if_pos rfl]
              cases b <;> simp [h12, h12.symm]
      have hmc : (Finset.univ.filter (fun v => f v = c1)).card = m := by
        let w := if b then pA else pB
        have hw_not_S : w ∉ S := by
          intro hwS
          have hwF := hS_sub hwS
          have := (Finset.mem_filter.mp hwF).2
          cases b <;> simp [w] at this
        have hset : Finset.univ.filter (fun v => f v = c1) = insert w S := by
          ext v
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          dsimp [f, w]
          by_cases hcan : canonIndep n r v
          · have hvS : v ∉ S := fun hv => (Finset.mem_filter.mp (hS_sub hv)).2.1 hcan
            have hvA : v ≠ pA := fun h => hpA_nc (h ▸ hcan)
            have hvB : v ≠ pB := fun h => hpB_nc (h ▸ hcan)
            cases b <;> simp [hcan, h01, hvS, hvA, hvB]
          · by_cases hvA : v = pA
            · subst hvA
              have hvS : pA ∉ S := fun hv => (Finset.mem_filter.mp (hS_sub hv)).2.2.1 rfl
              cases b <;> simp [hpA_nc, h12.symm, hvS, hpAB_ne]
            · by_cases hvB : v = pB
              · subst hvB
                have hvS : pB ∉ S := fun hv => (Finset.mem_filter.mp (hS_sub hv)).2.2.2 rfl
                cases b <;> simp [hpB_nc, h12.symm, hvS, hpAB_ne.symm]
              · cases b <;> simp [hcan, hvA, hvB, h12.symm]
        rw [hset, Finset.card_insert_of_notMem hw_not_S, hS_card]
        omega
      refine ⟨f, (@Finset.mem_filter _ _ (Classical.decPred _)).mpr ⟨Finset.mem_univ _, hprop, hfib, hmc⟩, ?_⟩
      ext
      · cases b <;> simp [f, hpA_nc, h12.symm]
      · simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hvF, hfv⟩
          have hv' := (Finset.mem_filter.mp hvF).2
          dsimp [f] at hfv
          rw [if_neg hv'.1, if_neg hv'.2.1, if_neg hv'.2.2] at hfv
          by_contra hvS
          rw [if_neg hvS] at hfv
          exact h12 hfv.symm
        · intro hvS
          have hvF := hS_sub hvS
          have hv' := (Finset.mem_filter.mp hvF).2
          refine ⟨hvF, ?_⟩
          dsimp [f]
          rw [if_neg hv'.1, if_neg hv'.2.1, if_neg hv'.2.2, if_pos hvS]
  rw [hbij, Finset.card_product, Finset.card_powersetCard, hFree_card]
  simp

/-- Helper: counting proper 3-colorings with hub color `c0` occurring `n - 1` times and color `c1`
occurring `m` times (`c2` gets the rest automatically). -/
private lemma count_with_hub_color {n : ℕ} (hn : 3 ≤ n)
    (c0 c1 c2 : Fin 3) (h01 : c0 ≠ c1) (h02 : c0 ≠ c2) (h12 : c1 ≠ c2)
    (m : ℕ) (hm1 : 1 ≤ m) (hm2 : m ≤ 2 * n - 1) :
    (@Finset.filter (Fin (3 * n - 1) → Fin 3)
      (fun f => (∀ u v, (squidGraph n).Adj u v → f u ≠ f v) ∧
        f ⟨0, by omega⟩ = c0 ∧
        (Finset.univ.filter (fun v => f v = c0)).card = n - 1 ∧
        (Finset.univ.filter (fun v => f v = c1)).card = m)
      (Classical.decPred _) Finset.univ).card =
    (n - 1) * (2 * Nat.choose (2 * n - 2) (m - 1)) := by
  let All := @Finset.filter (Fin (3 * n - 1) → Fin 3)
    (fun f => (∀ u v, (squidGraph n).Adj u v → f u ≠ f v) ∧
      f ⟨0, by omega⟩ = c0 ∧
      (Finset.univ.filter (fun v => f v = c0)).card = n - 1 ∧
      (Finset.univ.filter (fun v => f v = c1)).card = m)
    (Classical.decPred _) Finset.univ
  let Fiber : Fin (n - 1) → Finset (Fin (3 * n - 1) → Fin 3) := fun r =>
    @Finset.filter (Fin (3 * n - 1) → Fin 3)
      (fun f => (∀ u v, (squidGraph n).Adj u v → f u ≠ f v) ∧
        (∀ v, f v = c0 ↔ canonIndep n r v) ∧
        (Finset.univ.filter (fun v => f v = c1)).card = m)
      (Classical.decPred _) Finset.univ
  have hpart_eq : All = Finset.univ.biUnion Fiber := by
    ext f
    rw [@Finset.mem_filter _ _ (Classical.decPred _), Finset.mem_biUnion]
    simp only [Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hprop, hhub, hc0, hc1⟩
      rcases hub_color_fiber_eq_canon hn hprop hhub hc0 with ⟨r, hr, _⟩
      exact ⟨r, (@Finset.mem_filter _ _ (Classical.decPred _)).mpr ⟨Finset.mem_univ _, hprop, hr, hc1⟩⟩
    · rintro ⟨r, hf⟩
      rw [@Finset.mem_filter _ _ (Classical.decPred _)] at hf
      rcases hf.2 with ⟨hprop, hr, hc1⟩
      refine ⟨hprop, (hr ⟨0, by omega⟩).mpr (by unfold canonIndep; dsimp; omega), ?_, hc1⟩
      have hset : Finset.univ.filter (fun v => f v = c0) =
          Finset.univ.filter (fun v : Fin (3 * n - 1) => canonIndep n r v) := by
        ext v; simp [hr v]
      rw [hset]
      have hbij : (Finset.univ.filter (fun v : Fin (3 * n - 1) => canonIndep n r v)).card =
          (Finset.univ : Finset (Fin (n - 1))).card := by
        apply Finset.card_bij (fun v hv => ⟨v.val / 2, by
          have hv' := (Finset.mem_filter.mp hv).2; unfold canonIndep at hv'; omega⟩)
        · intro _ _; exact Finset.mem_univ _
        · intro u hu v hv h
          have hu' := (Finset.mem_filter.mp hu).2
          have hv' := (Finset.mem_filter.mp hv).2
          have hdiv : u.val / 2 = v.val / 2 := Fin.mk.inj h
          unfold canonIndep at hu' hv'
          apply Fin.ext; omega
        · intro j _
          by_cases hj : j.val ≤ r.val
          · refine ⟨⟨2 * j.val, by omega⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, by unfold canonIndep; dsimp; omega⟩,
              Fin.ext (by dsimp; omega)⟩
          · refine ⟨⟨2 * j.val + 1, by omega⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, by unfold canonIndep; dsimp; omega⟩,
              Fin.ext (by dsimp; omega)⟩
      rw [hbij]; simp
  have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin (n - 1))) Fiber := by
    intro r₁ _ r₂ _ hne
    change Disjoint (Fiber r₁) (Fiber r₂)
    rw [Finset.disjoint_left]
    intro f hf₁ hf₂
    rw [@Finset.mem_filter _ _ (Classical.decPred _)] at hf₁ hf₂
    have hhub : f ⟨0, by omega⟩ = c0 :=
      (hf₁.2.2.1 ⟨0, by omega⟩).mpr (by unfold canonIndep; dsimp; omega)
    have hc0 : (Finset.univ.filter (fun v => f v = c0)).card = n - 1 := by
      have hf_all : f ∈ All := by
        rw [hpart_eq, Finset.mem_biUnion]
        exact ⟨r₁, Finset.mem_univ _, (@Finset.mem_filter _ _ (Classical.decPred _)).mpr hf₁⟩
      exact ((@Finset.mem_filter _ _ (Classical.decPred _)).mp hf_all).2.2.2.1
    rcases hub_color_fiber_eq_canon hn hf₁.2.1 hhub hc0 with ⟨r0, _, huniq⟩
    exact hne ((huniq r₁ hf₁.2.2.1).trans (huniq r₂ hf₂.2.2.1).symm)
  change All.card = _
  rw [hpart_eq, Finset.card_biUnion hdisj]
  have hsum : ∑ r : Fin (n - 1), (Fiber r).card =
      ∑ _r : Fin (n - 1), (2 * Nat.choose (2 * n - 2) (m - 1)) := by
    apply Finset.sum_congr rfl
    intro r _
    exact count_fixed_r hn r c0 c1 c2 h01 h02 h12 m hm1 hm2
  rw [hsum]
  simp

private lemma card_fin3_sum {N : ℕ} (f : Fin N → Fin 3) :
    (Finset.univ.filter (fun v => f v = 0)).card +
    (Finset.univ.filter (fun v => f v = 1)).card +
    (Finset.univ.filter (fun v => f v = 2)).card = N := by
  have h := Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ) (t := Finset.univ)
    (fun x _ => Finset.mem_univ (f x))
  rw [Fin.sum_univ_three] at h
  simpa using h.symm

private lemma chromCoeff_bal {n : ℕ} (hn : 3 ≤ n) :
    chromCoeff (squidGraph n) 3 (wBal n) = (n - 1) * (2 * Nat.choose (2 * n - 2) (n - 1)) := by
  unfold chromCoeff
  rw [← count_with_hub_color hn 2 0 1 (by decide) (by decide) (by decide) n (by omega) (by omega)]
  congr 1
  ext f
  rw [@Finset.mem_filter _ _ (Classical.decPred _), @Finset.mem_filter _ _ (Classical.decPred _)]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hprop, hcnt⟩
    have hc0 := hcnt 0; have hc1 := hcnt 1; have hc2 := hcnt 2
    dsimp [wBal] at hc0 hc1 hc2
    have hhub : f ⟨0, by omega⟩ = 2 := by
      have hle := hub_color_card_le hn hprop rfl
      match hf0 : f ⟨0, by omega⟩ with
      | 0 => rw [hf0, hc0] at hle; omega
      | 1 => rw [hf0, hc1] at hle; omega
      | 2 => rfl
    exact ⟨hprop, hhub, hc2, hc0⟩
  · rintro ⟨hprop, _, hc2, hc0⟩
    refine ⟨hprop, ?_⟩
    intro c
    have hsum := card_fin3_sum f
    match c with
    | 0 => exact hc0
    | 1 => dsimp [wBal]; omega
    | 2 => exact hc2

private lemma chromCoeff_unb {n : ℕ} (hn : 3 ≤ n) :
    chromCoeff (squidGraph n) 3 (wUnb n) = 2 * ((n - 1) * (2 * Nat.choose (2 * n - 2) (n - 2))) := by
  unfold chromCoeff
  let S1 := @Finset.filter (Fin (3 * n - 1) → Fin 3)
    (fun f => (∀ u v, (squidGraph n).Adj u v → f u ≠ f v) ∧
      f ⟨0, by omega⟩ = 1 ∧
      (Finset.univ.filter (fun v => f v = 1)).card = n - 1 ∧
      (Finset.univ.filter (fun v => f v = 2)).card = n - 1)
    (Classical.decPred _) Finset.univ
  let S2 := @Finset.filter (Fin (3 * n - 1) → Fin 3)
    (fun f => (∀ u v, (squidGraph n).Adj u v → f u ≠ f v) ∧
      f ⟨0, by omega⟩ = 2 ∧
      (Finset.univ.filter (fun v => f v = 2)).card = n - 1 ∧
      (Finset.univ.filter (fun v => f v = 1)).card = n - 1)
    (Classical.decPred _) Finset.univ
  have heq : @Finset.filter (Fin (3 * n - 1) → Fin 3)
      (fun f => (∀ u v, (squidGraph n).Adj u v → f u ≠ f v) ∧
        ∀ c : Fin 3, (Finset.univ.filter (fun v => f v = c)).card = wUnb n c)
      (Classical.decPred _) Finset.univ = S1 ∪ S2 := by
    ext f
    rw [@Finset.mem_filter _ _ (Classical.decPred _), Finset.mem_union,
        @Finset.mem_filter _ _ (Classical.decPred _), @Finset.mem_filter _ _ (Classical.decPred _)]
    simp only [Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hprop, hcnt⟩
      have hc0 := hcnt 0; have hc1 := hcnt 1; have hc2 := hcnt 2
      dsimp [wUnb] at hc0 hc1 hc2
      have hle := hub_color_card_le hn hprop rfl
      match hf0 : f ⟨0, by omega⟩ with
      | 0 => rw [hf0, hc0] at hle; omega
      | 1 => exact Or.inl ⟨hprop, rfl, hc1, hc2⟩
      | 2 => exact Or.inr ⟨hprop, rfl, hc2, hc1⟩
    · rintro (⟨hprop, _, hc1, hc2⟩ | ⟨hprop, _, hc2, hc1⟩)
      · refine ⟨hprop, ?_⟩
        intro c; have hsum := card_fin3_sum f
        match c with
        | 0 => dsimp [wUnb]; omega
        | 1 => exact hc1
        | 2 => exact hc2
      · refine ⟨hprop, ?_⟩
        intro c; have hsum := card_fin3_sum f
        match c with
        | 0 => dsimp [wUnb]; omega
        | 1 => exact hc1
        | 2 => exact hc2
  have hdisj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro f hf1 hf2
    have h1 := ((@Finset.mem_filter _ _ (Classical.decPred _)).mp hf1).2.2.1
    have h2 := ((@Finset.mem_filter _ _ (Classical.decPred _)).mp hf2).2.2.1
    rw [h1] at h2
    exact absurd h2 (by decide)
  rw [heq, Finset.card_union_of_disjoint hdisj]
  have hS1 := count_with_hub_color hn 1 2 0 (by decide) (by decide) (by decide) (n - 1) (by omega) (by omega)
  have hS2 := count_with_hub_color hn 2 1 0 (by decide) (by decide) (by decide) (n - 1) (by omega) (by omega)
  have hn2 : n - 1 - 1 = n - 2 := by omega
  rw [hn2] at hS1 hS2
  change S1.card + S2.card = _
  rw [hS1, hS2]
  ring

private lemma chromCoeff_bal_lt_unb {n : ℕ} (hn : 3 ≤ n) :
    chromCoeff (squidGraph n) 3 (wBal n) < chromCoeff (squidGraph n) 3 (wUnb n) := by
  rw [chromCoeff_bal hn, chromCoeff_unb hn]
  have hch : (n - 1) * Nat.choose (2 * n - 2) (n - 1) = n * Nat.choose (2 * n - 2) (n - 2) := by
    have h1 := Nat.choose_succ_right_eq (2 * n - 2) (n - 2)
    have h2 : n - 2 + 1 = n - 1 := by omega
    have h3 : 2 * n - 2 - (n - 2) = n := by omega
    rw [h2, h3] at h1
    linarith
  have hpos : 0 < Nat.choose (2 * n - 2) (n - 2) := Nat.choose_pos (by omega)
  have h1 : (n - 1) * (2 * Nat.choose (2 * n - 2) (n - 1)) = 2 * n * Nat.choose (2 * n - 2) (n - 2) := by
    calc (n - 1) * (2 * Nat.choose (2 * n - 2) (n - 1))
        = 2 * ((n - 1) * Nat.choose (2 * n - 2) (n - 1)) := by ring
      _ = 2 * (n * Nat.choose (2 * n - 2) (n - 2)) := by rw [hch]
      _ = 2 * n * Nat.choose (2 * n - 2) (n - 2) := by ring
  have h2 : 2 * ((n - 1) * (2 * Nat.choose (2 * n - 2) (n - 2))) =
      4 * (n - 1) * Nat.choose (2 * n - 2) (n - 2) := by ring
  rw [h1, h2]
  have hlt : 2 * n < 4 * (n - 1) := by omega
  exact Nat.mul_lt_mul_of_pos_right hlt hpos

private lemma main_proof : type_of% @OMA.S_arxiv_2001_00181.main := by
  intro n hn hsp
  rcases hsp with ⟨S, c, hSc, hEq⟩
  have hbal := hEq 3 (wBal n)
  have hunb := hEq 3 (wUnb n)
  have hsum_le : ∑ lam ∈ S, c lam * (kostka lam 3 (wUnb n) : ℝ) ≤
      ∑ lam ∈ S, c lam * (kostka lam 3 (wBal n) : ℝ) := by
    apply Finset.sum_le_sum
    intro lam hlam
    rcases hSc lam hlam with ⟨hpart, hc0⟩
    have hk : (kostka lam 3 (wUnb n) : ℝ) ≤ (kostka lam 3 (wBal n) : ℝ) :=
      Nat.cast_le.mpr (kostka_unb_le_bal (by omega) hpart)
    exact mul_le_mul_of_nonneg_left hk hc0
  rw [← hunb, ← hbal] at hsum_le
  have hlt : (chromCoeff (squidGraph n) 3 (wBal n) : ℝ) <
      (chromCoeff (squidGraph n) 3 (wUnb n) : ℝ) :=
    Nat.cast_lt.mpr (chromCoeff_bal_lt_unb hn)
  linarith

end OMA.P_arxiv_2001_00181

theorem OMA.solution : type_of% @OMA.S_arxiv_2001_00181.main :=
  OMA.P_arxiv_2001_00181.main_proof

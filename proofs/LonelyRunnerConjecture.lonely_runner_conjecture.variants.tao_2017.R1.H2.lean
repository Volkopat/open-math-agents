import OMAReductions.R_LonelyRunnerConjecture_lonely_runner_conjecture_variants_tao_2017_R1

/-!
Sparse-pair overlap bound for Lonely Runner (Hu and Jing, arXiv:2610.23790, Sections 3, 4, and 8).
We prove Lemma 3.3 (pairwise Type II Bohr-set overlap bounds), Lemma 4.1 (exact k-coloring of
half-open intervals on R), Lemma 4.2 (dilation monotonicity of excess multiplicity on R),
Lemma 4.3 (period-limit transfer to UnitAddCircle), Proposition 4.4 (dilation spillover),
and deduce the uniform overlap lower bound 5 / 96.
-/

namespace LonelyRunnerSparseProof

open MeasureTheory MeasureTheory.Measure Function Metric Set Filter
open scoped Finset Classical

/- ### Part 1: Elementary natural-number layer identity -/

private lemma nat_pair_layer_identity (n a : ℕ) (ha : a ≤ n) :
    (a : ℝ) * ((a : ℝ) - 1) - 2 * ((a - 1 : ℕ) : ℝ) =
      2 * ∑ k ∈ Finset.Ico 2 n, ((a - k : ℕ) : ℝ) := by
  induction a with
  | zero =>
    simp
  | succ m ih =>
    have hm : m ≤ n := Nat.le_of_succ_le ha
    have ih' := ih hm
    have hcard :
        (((Finset.Ico 2 n).filter (fun k => k ≤ m)).card : ℝ) = ((m - 1 : ℕ) : ℝ) := by
      have hfilt : (Finset.Ico 2 n).filter (fun k => k ≤ m) = Finset.Ico 2 (m + 1) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_Ico]
        omega
      rw [hfilt, Nat.card_Ico]
      have : m + 1 - 2 = m - 1 := by omega
      rw [this]
    have hsum :
        ∑ k ∈ Finset.Ico 2 n, ((m + 1 - k : ℕ) : ℝ) =
          (∑ k ∈ Finset.Ico 2 n, ((m - k : ℕ) : ℝ)) + ((m - 1 : ℕ) : ℝ) := by
      have h1 :
          ∑ k ∈ Finset.Ico 2 n, ((m + 1 - k : ℕ) : ℝ) =
            (∑ k ∈ Finset.Ico 2 n, ((m - k : ℕ) : ℝ)) +
              (((Finset.Ico 2 n).filter (fun k => k ≤ m)).card : ℝ) := by
        calc
          ∑ k ∈ Finset.Ico 2 n, ((m + 1 - k : ℕ) : ℝ)
              = ∑ k ∈ Finset.Ico 2 n, (((m - k : ℕ) : ℝ) + if k ≤ m then (1 : ℝ) else 0) := by
                refine Finset.sum_congr rfl fun k _ => ?_
                split_ifs with hkm
                · have : m + 1 - k = m - k + 1 := by omega
                  rw [this]; push_cast; ring
                · have h1' : m + 1 - k = 0 := by omega
                  have h2' : m - k = 0 := by omega
                  rw [h1', h2']; simp
          _ = (∑ k ∈ Finset.Ico 2 n, ((m - k : ℕ) : ℝ)) +
                ∑ k ∈ Finset.Ico 2 n, (if k ≤ m then (1 : ℝ) else 0) := Finset.sum_add_distrib
          _ = (∑ k ∈ Finset.Ico 2 n, ((m - k : ℕ) : ℝ)) +
                (((Finset.Ico 2 n).filter (fun k => k ≤ m)).card : ℝ) := by
                rw [Finset.sum_boole]
      rw [h1, hcard]
    rw [hsum]
    cases m with
    | zero => simp at ih' ⊢
    | succ m' =>
      have hcast1 : ((m' + 1 - 1 : ℕ) : ℝ) = (m' : ℝ) := by simp
      have hcast2 : ((m' + 1 + 1 - 1 : ℕ) : ℝ) = (m' : ℝ) + 1 := by
        have : m' + 1 + 1 - 1 = m' + 1 := by omega
        rw [this]; push_cast; ring
      rw [hcast1] at ih'
      push_cast at ih' ⊢
      linarith

/- ### Part 2: Lemma 4.1 (Exact k-coloring of half-open intervals on R) -/

private lemma exists_unique_of_rank_strictLinear {α : Type*} [DecidableEq α]
    (lt : α → α → Prop) [DecidableRel lt]
    (h_irrefl : ∀ a, ¬ lt a a)
    (h_trans : ∀ a b c, lt a b → lt b c → lt a c)
    (h_total : ∀ a b, a ≠ b → lt a b ∨ lt b a)
    (S : Finset α) (j : ℕ) (hj : j < S.card) :
    ∃ a ∈ S, (S.filter fun b => lt b a).card = j := by
  -- Proof by induction on S.card removing the unique minimum element
  induction hcard : S.card generalizing S j with
  | zero => omega
  | succ c ih =>
    -- Find minimum element of S under lt
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    have hex_min : ∃ m ∈ S, ∀ x ∈ S, x ≠ m → lt m x := by
      clear ih hj hcard
      induction hne using Finset.Nonempty.cons_induction with
      | singleton a => exact ⟨a, Finset.mem_singleton_self a, fun x hx hxa => absurd (Finset.mem_singleton.mp hx) hxa⟩
      | cons a T ha hT ihT =>
        obtain ⟨m, hmT, hmmin⟩ := ihT
        have ham : a ≠ m := fun h => ha (h ▸ hmT)
        rcases h_total a m ham with hlt | hlt
        · refine ⟨a, Finset.mem_cons_self a T, fun x hx hxa => ?_⟩
          rcases Finset.mem_cons.mp hx with rfl | hxT
          · exact absurd rfl hxa
          · by_cases hxm : x = m
            · exact hxm ▸ hlt
            · exact h_trans a m x hlt (hmmin x hxT hxm)
        · refine ⟨m, Finset.mem_cons_of_mem hmT, fun x hx hxm => ?_⟩
          rcases Finset.mem_cons.mp hx with rfl | hxT
          · exact hlt
          · exact hmmin x hxT hxm
    obtain ⟨m, hmS, hmmin⟩ := hex_min
    cases j with
    | zero =>
      refine ⟨m, hmS, ?_⟩
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro b hb hlt
      by_cases hbm : b = m
      · exact h_irrefl m (hbm ▸ hlt)
      · exact h_irrefl m (h_trans m b m (hmmin b hb hbm) hlt)
    | succ j' =>
      have hcard' : (S.erase m).card = c := by
        rw [Finset.card_erase_of_mem hmS, hcard]; simp
      obtain ⟨a, haE, harank⟩ := ih (S.erase m) j' (by omega) hcard'
      have haS : a ∈ S := Finset.mem_of_mem_erase haE
      have ham : a ≠ m := (Finset.mem_erase.mp haE).1
      refine ⟨a, haS, ?_⟩
      have hfilt : S.filter (fun b => lt b a) =
          insert m ((S.erase m).filter (fun b => lt b a)) := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
        constructor
        · intro ⟨hbS, hlt⟩
          by_cases hbm : b = m
          · exact Or.inl hbm
          · exact Or.inr ⟨⟨hbm, hbS⟩, hlt⟩
        · rintro (rfl | ⟨⟨_, hbS⟩, hlt⟩)
          · exact ⟨hmS, hmmin a haS ham⟩
          · exact ⟨hbS, hlt⟩
      rw [hfilt, Finset.card_insert_of_notMem, harank]
      simp

private lemma card_rank_lt_strictLinear {α : Type*} [DecidableEq α]
    (lt : α → α → Prop) [DecidableRel lt]
    (h_irrefl : ∀ a, ¬ lt a a)
    (h_trans : ∀ a b c, lt a b → lt b c → lt a c)
    (h_total : ∀ a b, a ≠ b → lt a b ∨ lt b a)
    (S : Finset α) (k : ℕ) :
    (S.filter fun a => (S.filter fun b => lt b a).card < k).card = min S.card k := by
  let rank (a : α) : ℕ := (S.filter fun b => lt b a).card
  have hinj : Set.InjOn rank (S : Set α) := by
    intro a ha b hb hab
    by_contra hne
    rcases h_total a b hne with hlt | hlt
    · have hsub : S.filter (fun c => lt c a) ⊂ S.filter (fun c => lt c b) := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨fun c hc => ?_, fun heq => ?_⟩
        · simp only [Finset.mem_filter] at hc ⊢
          exact ⟨hc.1, h_trans c a b hc.2 hlt⟩
        · have ha_mem : a ∈ S.filter (fun c => lt c b) := Finset.mem_filter.mpr ⟨ha, hlt⟩
          rw [← heq] at ha_mem
          exact h_irrefl a (Finset.mem_filter.mp ha_mem).2
      have := Finset.card_lt_card hsub
      dsimp [rank] at hab
      omega
    · have hsub : S.filter (fun c => lt c b) ⊂ S.filter (fun c => lt c a) := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨fun c hc => ?_, fun heq => ?_⟩
        · simp only [Finset.mem_filter] at hc ⊢
          exact ⟨hc.1, h_trans c b a hc.2 hlt⟩
        · have hb_mem : b ∈ S.filter (fun c => lt c a) := Finset.mem_filter.mpr ⟨hb, hlt⟩
          rw [← heq] at hb_mem
          exact h_irrefl b (Finset.mem_filter.mp hb_mem).2
      have := Finset.card_lt_card hsub
      dsimp [rank] at hab
      omega
  have himg : (S.filter fun a => rank a < k).image rank = Finset.range (min S.card k) := by
    ext j
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range, lt_min_iff]
    constructor
    · rintro ⟨a, ⟨haS, hlt⟩, rfl⟩
      refine ⟨?_, hlt⟩
      have hss : S.filter (fun b => lt b a) ⊂ S := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨Finset.filter_subset _ _, fun heq => ?_⟩
        have ha' : a ∈ S.filter (fun b => lt b a) := heq.symm ▸ haS
        exact h_irrefl a (Finset.mem_filter.mp ha').2
      exact Finset.card_lt_card hss
    · rintro ⟨hjS, hjk⟩
      obtain ⟨a, haS, harank⟩ := exists_unique_of_rank_strictLinear lt h_irrefl h_trans h_total S j hjS
      refine ⟨a, ⟨haS, ?_⟩, harank⟩
      change (S.filter fun b => lt b a).card < k
      omega
  rw [← Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _)), himg, Finset.card_range]

private lemma interval_coloring_sorted {m k : ℕ} (hk : 1 ≤ k) (l r : Fin m → ℝ)
    (hl : Monotone l) :
    ∃ col : Fin m → Fin k, ∀ x : ℝ,
      (Finset.univ.filter fun a : Fin k => ∃ i : Fin m, col i = a ∧ x ∈ Set.Ico (l i) (r i)).card =
        min (Finset.univ.filter fun i : Fin m => x ∈ Set.Ico (l i) (r i)).card k := by
  classical
  -- Strict linear order on Fin m: larger right endpoint comes first; ties broken by larger index
  let gtR : Fin m → Fin m → Prop := fun a b => r b < r a ∨ (r b = r a ∧ b.1 < a.1)
  have h_irrefl : ∀ a, ¬ gtR a a := fun a h => by
    rcases h with h | ⟨_, h⟩ <;> exact lt_irrefl _ h
  have h_trans : ∀ a b c, gtR a b → gtR b c → gtR a c := by
    intro a b c hab hbc
    rcases hab with h1 | ⟨e1, h1⟩ <;> rcases hbc with h2 | ⟨e2, h2⟩
    · exact Or.inl (lt_trans h2 h1)
    · exact Or.inl (e2 ▸ h1)
    · exact Or.inl (e1.symm ▸ h2)
    · exact Or.inr ⟨e2.trans e1, lt_trans h2 h1⟩
  have h_total : ∀ a b, a ≠ b → gtR a b ∨ gtR b a := by
    intro a b hab
    rcases lt_trichotomy (r b) (r a) with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases lt_trichotomy b.1 a.1 with h' | h' | h'
      · exact Or.inl (Or.inr ⟨h, h'⟩)
      · exact absurd (Fin.ext h'.symm) hab
      · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
    · exact Or.inr (Or.inl h)
  -- Prefix active set for t ≤ m
  let active (t : ℕ) (x : ℝ) : Finset (Fin m) :=
    Finset.univ.filter fun i => i.1 < t ∧ x ∈ Set.Ico (l i) (r i)
  let topK (S : Finset (Fin m)) : Finset (Fin m) :=
    S.filter fun a => (S.filter fun b => gtR b a).card < k
  -- Prove by induction on t ≤ m that there exists col : Fin m → Fin k injective on topK (active t x)
  have h_ind : ∀ t ≤ m, ∃ col : Fin m → Fin k, ∀ x : ℝ,
      Set.InjOn col (topK (active t x) : Set (Fin m)) := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨fun _ => ⟨0, hk⟩, fun x a ha => ?_⟩
      simp [topK, active] at ha
    | succ t ih =>
      intro htm
      obtain ⟨col, hcol⟩ := ih (Nat.le_of_succ_le htm)
      let it : Fin m := ⟨t, htm⟩
      let S0 := active t (l it)
      -- Choose color c_new for it
      have hex_c : ∃ c_new : Fin k,
          (S0.card < k → c_new ∉ S0.image col) ∧
          (k ≤ S0.card → ∃ ik ∈ S0, (S0.filter fun b => gtR b ik).card = k - 1 ∧ c_new = col ik) := by
        by_cases hsmall : S0.card < k
        · have hlt : (S0.image col).card < (Finset.univ : Finset (Fin k)).card := by
            calc (S0.image col).card ≤ S0.card := Finset.card_image_le
              _ < k := hsmall
              _ = (Finset.univ : Finset (Fin k)).card := by simp
          obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
          exact ⟨c, fun _ => hc, fun h => absurd h (not_le_of_gt hsmall)⟩
        · have hge : k ≤ S0.card := not_lt.mp hsmall
          obtain ⟨ik, hikS, hikrank⟩ :=
            exists_unique_of_rank_strictLinear gtR h_irrefl h_trans h_total S0 (k - 1) (by omega)
          exact ⟨col ik, fun h => absurd h hsmall, fun _ => ⟨ik, hikS, hikrank, rfl⟩⟩
      obtain ⟨c_new, hc_small, hc_large⟩ := hex_c
      let col' : Fin m → Fin k := fun i => if i = it then c_new else col i
      refine ⟨col', fun x a ha b hb hab => ?_⟩
      -- If x ∉ Ico (l it) (r it), active (t+1) x = active t x
      by_cases hxit : x ∈ Set.Ico (l it) (r it)
      · -- Here active (t+1) x = insert it (active t x)
        have hact_eq : active (t + 1) x = insert it (active t x) := by
          ext i
          simp only [active, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          constructor
          · rintro ⟨hlt, hxi⟩
            by_cases hi : i.1 = t
            · exact Or.inl (Fin.ext hi)
            · exact Or.inr ⟨by omega, hxi⟩
          · rintro (rfl | ⟨hlt, hxi⟩)
            · exact ⟨Nat.lt_succ_self t, hxit⟩
            · exact ⟨Nat.lt_succ_of_lt hlt, hxi⟩
        -- active t x is a subset of S0 and is an initial segment of S0 under gtR
        have hsub_S0 : active t x ⊆ S0 := by
          intro i hi
          simp only [active, S0, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Ico] at hi hxit ⊢
          have hli : l i ≤ l it := hl (Nat.le_of_lt hi.1)
          exact ⟨hi.1, hli, lt_of_le_of_lt hxit.1 hi.2.2⟩
        have hinit_S0 : ∀ i ∈ active t x, ∀ j ∈ S0, gtR j i → j ∈ active t x := by
          intro i hi j hj hji
          simp only [active, S0, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Ico] at hi hj hxit ⊢
          have hrij : r i ≤ r j := by
            rcases hji with h | ⟨e, _⟩
            · exact le_of_lt h
            · exact le_of_eq e
          exact ⟨hj.1, le_trans hj.2.1 hxit.1, lt_of_lt_of_le hi.2.2 hrij⟩
        have hrank_eq : ∀ i ∈ active t x,
            ((active t x).filter fun j => gtR j i).card = (S0.filter fun j => gtR j i).card := by
          intro i hi
          congr 1
          ext j
          simp only [Finset.mem_filter]
          exact ⟨fun ⟨hj, hji⟩ => ⟨hsub_S0 hj, hji⟩, fun ⟨hj, hji⟩ => ⟨hinit_S0 i hi j hj hji, hji⟩⟩
        have hit_not_mem : it ∉ active t x := by
          simp [active, it]
        -- Helper: for u ≠ it in topK (active (t+1) x), u ∈ active t x and u ∈ topK S0 and col' u = col u
        have hmem_other : ∀ u ∈ topK (active (t + 1) x), u ≠ it →
            u ∈ active t x ∧ u ∈ topK (active t x) ∧ u ∈ topK S0 := by
          intro u hu huit
          have hu_act : u ∈ active (t + 1) x := (Finset.mem_filter.mp hu).1
          have hu_rank : ((active (t + 1) x).filter fun j => gtR j u).card < k := (Finset.mem_filter.mp hu).2
          have hu_t : u ∈ active t x := by
            rw [hact_eq, Finset.mem_insert] at hu_act
            exact hu_act.resolve_left huit
          have hsub_f : (active t x).filter (fun j => gtR j u) ⊆ (active (t + 1) x).filter (fun j => gtR j u) := by
            rw [hact_eq]
            exact Finset.filter_subset_filter _ (Finset.subset_insert _ _)
          have hlt_t : ((active t x).filter fun j => gtR j u).card < k :=
            lt_of_le_of_lt (Finset.card_le_card hsub_f) hu_rank
          refine ⟨hu_t, Finset.mem_filter.mpr ⟨hu_t, hlt_t⟩, ?_⟩
          refine Finset.mem_filter.mpr ⟨hsub_S0 hu_t, ?_⟩
          rwa [← hrank_eq u hu_t]
        -- Helper: if u ∈ topK (active (t+1) x), u ≠ it, and it ∈ topK (active (t+1) x), then col u ≠ c_new
        have hne_it : ∀ u ∈ topK (active (t + 1) x), u ≠ it → it ∈ topK (active (t + 1) x) → col u ≠ c_new := by
          intro u hu huit hit_top
          obtain ⟨hu_t, _, hu_S0top⟩ := hmem_other u hu huit
          by_cases hsmall : S0.card < k
          · intro heq
            exact hc_small hsmall (heq ▸ Finset.mem_image_of_mem col (hsub_S0 hu_t))
          · obtain ⟨ik, hikS, hikrank, rfl⟩ := hc_large (not_lt.mp hsmall)
            have hik_top : ik ∈ topK S0 := Finset.mem_filter.mpr ⟨hikS, by omega⟩
            intro heq
            have huik : u = ik := hcol (l it) hu_S0top hik_top heq
            have hik_t : ik ∈ active t x := huik ▸ hu_t
            have hik_top_next : ik ∈ topK (active (t + 1) x) := huik ▸ hu
            have hik_ne_it : it ≠ ik := (huik ▸ huit).symm
            -- Now ik ∈ active t x, with rank_{S0}(ik) = k - 1
            have hik_rank_act : ((active t x).filter fun j => gtR j ik).card = k - 1 := by
              rw [hrank_eq ik hik_t, hikrank]
            rcases h_total it ik hik_ne_it with hgt | hgt
            · -- gtR it ik: then it is in (active (t+1) x).filter (gtR · ik), so rank of ik in active (t+1) x is k
              have hfilt : (active (t + 1) x).filter (fun j => gtR j ik) =
                  insert it ((active t x).filter (fun j => gtR j ik)) := by
                rw [hact_eq, Finset.filter_insert, if_pos hgt]
              have hcard_ik : ((active (t + 1) x).filter fun j => gtR j ik).card = k := by
                rw [hfilt, Finset.card_insert_of_notMem (by simp [hit_not_mem]), hik_rank_act]
                exact Nat.sub_add_cancel hk
              have hlt_ik : ((active (t + 1) x).filter fun j => gtR j ik).card < k :=
                (Finset.mem_filter.mp hik_top_next).2
              rw [hcard_ik] at hlt_ik
              exact lt_irrefl k hlt_ik
            · -- gtR ik it: then every j in (active t x).filter (gtR · ik) and ik itself satisfy gtR · it
              have hsub_it : insert ik ((active t x).filter fun j => gtR j ik) ⊆
                  (active (t + 1) x).filter (fun j => gtR j it) := by
                intro j hj
                rw [Finset.mem_insert] at hj
                rw [hact_eq, Finset.mem_filter]
                rcases hj with rfl | hj
                · exact ⟨Finset.mem_insert_of_mem hik_t, hgt⟩
                · rw [Finset.mem_filter] at hj
                  exact ⟨Finset.mem_insert_of_mem hj.1, h_trans j ik it hj.2 hgt⟩
              have hik_not : ik ∉ (active t x).filter (fun j => gtR j ik) := by
                simp [h_irrefl]
              have hle : k ≤ ((active (t + 1) x).filter fun j => gtR j it).card := by
                have h1 := Finset.card_le_card hsub_it
                rw [Finset.card_insert_of_notMem hik_not, hik_rank_act, Nat.sub_add_cancel hk] at h1
                exact h1
              have hlt_it : ((active (t + 1) x).filter fun j => gtR j it).card < k :=
                (Finset.mem_filter.mp hit_top).2
              exact not_le_of_gt hlt_it hle
        by_cases ha_it : a = it
        · by_cases hb_it : b = it
          · exact ha_it.trans hb_it.symm
          · subst ha_it
            dsimp [col'] at hab
            rw [if_pos rfl, if_neg hb_it] at hab
            exact absurd hab.symm (hne_it b hb hb_it ha)
        · by_cases hb_it : b = it
          · subst hb_it
            dsimp [col'] at hab
            rw [if_neg ha_it, if_pos rfl] at hab
            exact absurd hab (hne_it a ha ha_it hb)
          · dsimp [col'] at hab
            rw [if_neg ha_it, if_neg hb_it] at hab
            exact hcol x (hmem_other a ha ha_it).2.1 (hmem_other b hb hb_it).2.1 hab
      · have hact_eq : active (t + 1) x = active t x := by
          ext i
          simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hlt, hxi⟩
            refine ⟨?_, hxi⟩
            by_contra hge
            have hi : i = it := Fin.ext (show i.1 = t by omega)
            exact hxit (hi ▸ hxi)
          · rintro ⟨hlt, hxi⟩
            exact ⟨Nat.lt_succ_of_lt hlt, hxi⟩
        rw [hact_eq] at ha hb
        have ha_ne : a ≠ it := by
          intro h; subst h
          have hmem : it ∈ active t x := (Finset.mem_filter.mp ha).1
          have hlt : it.1 < t := (Finset.mem_filter.mp hmem).2.1
          change t < t at hlt
          omega
        have hb_ne : b ≠ it := by
          intro h; subst h
          have hmem : it ∈ active t x := (Finset.mem_filter.mp hb).1
          have hlt : it.1 < t := (Finset.mem_filter.mp hmem).2.1
          change t < t at hlt
          omega
        dsimp [col'] at hab
        rw [if_neg ha_ne, if_neg hb_ne] at hab
        exact hcol x ha hb hab
  obtain ⟨col, hcol⟩ := h_ind m le_rfl
  refine ⟨col, fun x => ?_⟩
  have hact_m : active m x = Finset.univ.filter (fun i : Fin m => x ∈ Set.Ico (l i) (r i)) := by
    ext i
    simp [active]
  have hfilt_eq :
      (Finset.univ.filter fun a : Fin k => ∃ i : Fin m, col i = a ∧ x ∈ Set.Ico (l i) (r i)) =
        (active m x).image col := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hact_m]
    constructor
    · rintro ⟨i, rfl, hi⟩; exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨i, rfl, hi⟩
  rw [hfilt_eq, ← hact_m]
  apply le_antisymm
  · rw [le_min_iff]
    refine ⟨Finset.card_image_le, ?_⟩
    exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin k)
  · have htop_card : (topK (active m x)).card = min (active m x).card k :=
      card_rank_lt_strictLinear gtR h_irrefl h_trans h_total (active m x) k
    rw [← htop_card, ← Finset.card_image_of_injOn (hcol x)]
    exact Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))

private lemma interval_coloring {m k : ℕ} (hk : 1 ≤ k) (l r : Fin m → ℝ) :
    ∃ col : Fin m → Fin k, ∀ x : ℝ,
      (Finset.univ.filter fun a : Fin k => ∃ i : Fin m, col i = a ∧ x ∈ Set.Ico (l i) (r i)).card =
        min (Finset.univ.filter fun i : Fin m => x ∈ Set.Ico (l i) (r i)).card k := by
  let σ : Equiv.Perm (Fin m) := Tuple.sort l
  have hl : Monotone (l ∘ σ) := Tuple.monotone_sort l
  obtain ⟨col, hcol⟩ := interval_coloring_sorted hk (l ∘ σ) (r ∘ σ) hl
  refine ⟨col ∘ σ.symm, fun x => ?_⟩
  have h1 :
      (Finset.univ.filter fun a : Fin k => ∃ i : Fin m, (col ∘ σ.symm) i = a ∧ x ∈ Set.Ico (l i) (r i)) =
        Finset.univ.filter fun a : Fin k => ∃ j : Fin m, col j = a ∧ x ∈ Set.Ico ((l ∘ σ) j) ((r ∘ σ) j) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
    constructor
    · rintro ⟨i, rfl, hi⟩
      exact ⟨σ.symm i, rfl, by simpa using hi⟩
    · rintro ⟨j, rfl, hj⟩
      exact ⟨σ j, by simp, hj⟩
  have h2 :
      (Finset.univ.filter fun i : Fin m => x ∈ Set.Ico (l i) (r i)).card =
        (Finset.univ.filter fun j : Fin m => x ∈ Set.Ico ((l ∘ σ) j) ((r ∘ σ) j)).card := by
    refine Finset.card_bij (fun i _ => σ.symm i) ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply] at hi ⊢
      simpa using hi
    · intro i₁ _ i₂ _ h; exact σ.symm.injective h
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply] at hj ⊢
      exact ⟨σ j, hj, by simp⟩
  rw [h1, h2]
  exact hcol x

/- ### Part 3: Lemma 4.2 (Monotonicity of union under center dilation and excess dilation) -/

private lemma exists_disjoint_Icc_union {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a b : ι → ℝ) (hab : ∀ i ∈ S, a i ≤ b i) :
    ∃ (C : Finset (ℝ × ℝ)),
      (∀ p ∈ C, p.1 ≤ p.2) ∧
      (C : Set (ℝ × ℝ)).PairwiseDisjoint (fun p => Set.Icc p.1 p.2) ∧
      (⋃ p ∈ C, Set.Icc p.1 p.2) = ⋃ i ∈ S, Set.Icc (a i) (b i) := by
  classical
  induction S using Finset.induction with
  | empty =>
    exact ⟨∅, by simp, by simp, by simp⟩
  | @insert i₀ S hi₀ ih =>
    obtain ⟨C, hle, hdisj, hunion⟩ := ih (fun i hi => hab i (Finset.mem_insert_of_mem hi))
    have h0 : a i₀ ≤ b i₀ := hab i₀ (Finset.mem_insert_self i₀ S)
    let M := C.filter fun p => ¬ Disjoint (Set.Icc p.1 p.2) (Set.Icc (a i₀) (b i₀))
    let K := C.filter fun p => Disjoint (Set.Icc p.1 p.2) (Set.Icc (a i₀) (b i₀))
    let L : ℝ := M.fold min (a i₀) Prod.fst
    let R : ℝ := M.fold max (b i₀) Prod.snd
    have hL_le_a : L ≤ a i₀ := by
      change M.fold min (a i₀) Prod.fst ≤ a i₀
      induction M using Finset.induction with
      | empty => simp
      | @insert q M' hq ihM =>
        rw [Finset.fold_insert hq]
        exact min_le_of_right_le ihM
    have hb_le_R : b i₀ ≤ R := by
      change b i₀ ≤ M.fold max (b i₀) Prod.snd
      induction M using Finset.induction with
      | empty => simp
      | @insert q M' hq ihM =>
        rw [Finset.fold_insert hq]
        exact le_max_of_le_right ihM
    have hL_le_p : ∀ p ∈ M, L ≤ p.1 := by
      change ∀ p ∈ M, M.fold min (a i₀) Prod.fst ≤ p.1
      induction M using Finset.induction with
      | empty => intro p hp; simp at hp
      | @insert q M' hq ihM =>
        intro p hp
        rw [Finset.fold_insert hq]
        rcases Finset.mem_insert.mp hp with rfl | hp'
        · exact min_le_left _ _
        · exact min_le_of_right_le (ihM p hp')
    have hp_le_R : ∀ p ∈ M, p.2 ≤ R := by
      change ∀ p ∈ M, p.2 ≤ M.fold max (b i₀) Prod.snd
      induction M using Finset.induction with
      | empty => intro p hp; simp at hp
      | @insert q M' hq ihM =>
        intro p hp
        rw [Finset.fold_insert hq]
        rcases Finset.mem_insert.mp hp with rfl | hp'
        · exact le_max_left _ _
        · exact le_max_of_le_right (ihM p hp')
    have hL_attained : L = a i₀ ∨ ∃ p ∈ M, L = p.1 := by
      change M.fold min (a i₀) Prod.fst = a i₀ ∨ ∃ p ∈ M, M.fold min (a i₀) Prod.fst = p.1
      induction M using Finset.induction with
      | empty => left; simp
      | @insert q M' hq ihM =>
        rw [Finset.fold_insert hq]
        rcases min_cases q.1 (M'.fold min (a i₀) Prod.fst) with ⟨heq, _⟩ | ⟨heq, _⟩
        · right; exact ⟨q, Finset.mem_insert_self _ _, heq⟩
        · rw [heq]
          rcases ihM with h | ⟨p, hp, h⟩
          · exact Or.inl h
          · exact Or.inr ⟨p, Finset.mem_insert_of_mem hp, h⟩
    have hR_attained : R = b i₀ ∨ ∃ p ∈ M, R = p.2 := by
      change M.fold max (b i₀) Prod.snd = b i₀ ∨ ∃ p ∈ M, M.fold max (b i₀) Prod.snd = p.2
      induction M using Finset.induction with
      | empty => left; simp
      | @insert q M' hq ihM =>
        rw [Finset.fold_insert hq]
        rcases max_cases q.2 (M'.fold max (b i₀) Prod.snd) with ⟨heq, _⟩ | ⟨heq, _⟩
        · right; exact ⟨q, Finset.mem_insert_self _ _, heq⟩
        · rw [heq]
          rcases ihM with h | ⟨p, hp, h⟩
          · exact Or.inl h
          · exact Or.inr ⟨p, Finset.mem_insert_of_mem hp, h⟩
    have hLR : L ≤ R := hL_le_a.trans (h0.trans hb_le_R)
    -- Every point in [L, R] lies in [a i₀, b i₀] ∪ ⋃ p ∈ M, [p.1, p.2]
    have hLR_eq : Set.Icc L R = Set.Icc (a i₀) (b i₀) ∪ ⋃ p ∈ M, Set.Icc p.1 p.2 := by
      apply Set.Subset.antisymm
      · intro x ⟨hxL, hxR⟩
        by_cases hxa : x < a i₀
        · rcases hL_attained with hLa | ⟨p, hpM, hLp⟩
          · linarith
          · have hp_nd : ¬ Disjoint (Set.Icc p.1 p.2) (Set.Icc (a i₀) (b i₀)) :=
              (Finset.mem_filter.mp hpM).2
            rw [Set.not_disjoint_iff] at hp_nd
            obtain ⟨y, ⟨_, hyp2⟩, ⟨hya, _⟩⟩ := hp_nd
            exact Or.inr (Set.mem_biUnion hpM ⟨by linarith, by linarith⟩)
        · by_cases hxb : b i₀ < x
          · rcases hR_attained with hRb | ⟨p, hpM, hRp⟩
            · linarith
            · have hp_nd : ¬ Disjoint (Set.Icc p.1 p.2) (Set.Icc (a i₀) (b i₀)) :=
                (Finset.mem_filter.mp hpM).2
              rw [Set.not_disjoint_iff] at hp_nd
              obtain ⟨y, ⟨hyp1, _⟩, ⟨_, hyb⟩⟩ := hp_nd
              exact Or.inr (Set.mem_biUnion hpM ⟨by linarith, by linarith⟩)
          · exact Or.inl ⟨not_lt.mp hxa, not_lt.mp hxb⟩
      · refine Set.union_subset (Set.Icc_subset_Icc hL_le_a hb_le_R) ?_
        refine Set.iUnion₂_subset fun p hp => Set.Icc_subset_Icc (hL_le_p p hp) (hp_le_R p hp)
    refine ⟨insert (L, R) K, ?_, ?_, ?_⟩
    · intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hpK
      · exact hLR
      · exact hle p (Finset.mem_filter.mp hpK).1
    · intro p hp q hq hpq
      rcases Finset.mem_insert.mp hp with rfl | hpK <;> rcases Finset.mem_insert.mp hq with rfl | hqK
      · exact absurd rfl hpq
      · change Disjoint (Set.Icc L R) (Set.Icc q.1 q.2)
        rw [hLR_eq, Set.disjoint_union_left]
        refine ⟨(Finset.mem_filter.mp hqK).2.symm, ?_⟩
        rw [Set.disjoint_iUnion₂_left]
        intro r hrM
        have hrC : r ∈ C := (Finset.mem_filter.mp hrM).1
        have hqC : q ∈ C := (Finset.mem_filter.mp hqK).1
        have hrq : r ≠ q := fun heq => (Finset.mem_filter.mp hrM).2 (heq ▸ (Finset.mem_filter.mp hqK).2)
        exact hdisj hrC hqC hrq
      · change Disjoint (Set.Icc p.1 p.2) (Set.Icc L R)
        rw [hLR_eq, Set.disjoint_union_right]
        refine ⟨(Finset.mem_filter.mp hpK).2, ?_⟩
        rw [Set.disjoint_iUnion₂_right]
        intro r hrM
        have hrC : r ∈ C := (Finset.mem_filter.mp hrM).1
        have hpC : p ∈ C := (Finset.mem_filter.mp hpK).1
        have hpr : p ≠ r := fun heq => (Finset.mem_filter.mp hrM).2 (heq ▸ (Finset.mem_filter.mp hpK).2)
        exact hdisj hpC hrC hpr
      · exact hdisj (Finset.mem_filter.mp hpK).1 (Finset.mem_filter.mp hqK).1 hpq
    · calc
        (⋃ p ∈ insert (L, R) K, Set.Icc p.1 p.2)
            = Set.Icc L R ∪ ⋃ p ∈ K, Set.Icc p.1 p.2 := by simp
        _ = Set.Icc (a i₀) (b i₀) ∪ ((⋃ p ∈ M, Set.Icc p.1 p.2) ∪ ⋃ p ∈ K, Set.Icc p.1 p.2) := by
              rw [hLR_eq, Set.union_assoc]
        _ = Set.Icc (a i₀) (b i₀) ∪ ⋃ p ∈ C, Set.Icc p.1 p.2 := by
              congr 1
              ext x
              simp only [Set.mem_union, Set.mem_iUnion, exists_prop, M, K, Finset.mem_filter]
              constructor
              · rintro (⟨p, ⟨hpC, _⟩, hx⟩ | ⟨p, ⟨hpC, _⟩, hx⟩) <;> exact ⟨p, hpC, hx⟩
              · rintro ⟨p, hpC, hx⟩
                by_cases hd : Disjoint (Set.Icc p.1 p.2) (Set.Icc (a i₀) (b i₀))
                · exact Or.inr ⟨p, ⟨hpC, hd⟩, hx⟩
                · exact Or.inl ⟨p, ⟨hpC, hd⟩, hx⟩
        _ = ⋃ i ∈ insert i₀ S, Set.Icc (a i) (b i) := by
              rw [hunion]; simp

private lemma union_Icc_mono_center_dilation {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c r : ι → ℝ) (hr : ∀ i ∈ S, 0 ≤ r i)
    {lam1 lam2 : ℝ} (hlam1 : 0 < lam1) (hlam : lam1 ≤ lam2) :
    volume.real (⋃ i ∈ S, Set.Icc (lam1 * c i - r i) (lam1 * c i + r i)) ≤
      volume.real (⋃ i ∈ S, Set.Icc (lam2 * c i - r i) (lam2 * c i + r i)) := by
  classical
  let J (t : ℝ) (i : ι) : Set ℝ := Set.Icc (t * c i - r i) (t * c i + r i)
  obtain ⟨C, hCle, hCdisj, hCunion⟩ := exists_disjoint_Icc_union S
    (fun i => lam2 * c i - r i) (fun i => lam2 * c i + r i)
    (fun i hi => by linarith [hr i hi])
  -- Each J lam2 i is contained in some C-component p ∈ C (connectedness of Icc!)
  have hcover_C : ∀ i ∈ S, ∃ p ∈ C, J lam2 i ⊆ Set.Icc p.1 p.2 := by
    intro i hi
    have hmem_u : lam2 * c i ∈ ⋃ p ∈ C, Set.Icc p.1 p.2 := by
      rw [hCunion]
      exact Set.mem_biUnion hi ⟨by linarith [hr i hi], by linarith [hr i hi]⟩
    obtain ⟨p, hpC, hxp⟩ := Set.mem_iUnion₂.mp hmem_u
    refine ⟨p, hpC, ?_⟩
    let U₁ : Set ℝ := Set.Icc p.1 p.2
    let U₂ : Set ℝ := ⋃ q ∈ C.erase p, Set.Icc q.1 q.2
    have hU₁ : IsClosed U₁ := isClosed_Icc
    have hU₂ : IsClosed U₂ := (C.erase p).finite_toSet.isClosed_biUnion fun _ _ => isClosed_Icc
    have hdisj12 : Disjoint U₁ U₂ := by
      rw [Set.disjoint_iUnion₂_right]
      intro q hq
      exact hCdisj hpC (Finset.mem_of_mem_erase hq) (Finset.ne_of_mem_erase hq).symm
    have hsub12 : J lam2 i ⊆ U₁ ∪ U₂ := by
      intro y hy
      have hyu : y ∈ ⋃ q ∈ C, Set.Icc q.1 q.2 := hCunion.symm ▸ Set.mem_biUnion hi hy
      obtain ⟨q, hqC, hyq⟩ := Set.mem_iUnion₂.mp hyu
      by_cases hqp : q = p
      · exact Or.inl (show y ∈ Set.Icc p.1 p.2 by rwa [← hqp])
      · exact Or.inr (Set.mem_biUnion (Finset.mem_erase.mpr ⟨hqp, hqC⟩) hyq)
    have hconn : IsPreconnected (J lam2 i) := isPreconnected_Icc
    have hsplit := isPreconnected_iff_subset_of_disjoint_closed.mp hconn U₁ U₂ hU₁ hU₂ hsub12 (by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨_, hy1, hy2⟩
      exact Set.disjoint_left.mp hdisj12 hy1 hy2)
    rcases hsplit with h1 | h2
    · exact h1
    · exact (Set.disjoint_left.mp hdisj12 hxp (h2 ⟨by linarith [hr i hi], by linarith [hr i hi]⟩)).elim
  let T (p : ℝ × ℝ) : Finset ι := S.filter fun i => J lam2 i ⊆ Set.Icc p.1 p.2
  have hsub_union : (⋃ i ∈ S, J lam1 i) ⊆ ⋃ p ∈ C, ⋃ i ∈ T p, J lam1 i := by
    intro x hx
    obtain ⟨i, hiS, hxi⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨p, hpC, hpi⟩ := hcover_C i hiS
    exact Set.mem_biUnion hpC (Set.mem_biUnion (Finset.mem_filter.mpr ⟨hiS, hpi⟩) hxi)
  have hblock : ∀ p ∈ C, volume.real (⋃ i ∈ T p, J lam1 i) ≤ volume.real (Set.Icc p.1 p.2) := by
    intro p hpC
    by_cases hne : (T p).Nonempty
    · obtain ⟨a₁, ha₁T, ha₁min⟩ := Finset.exists_min_image (T p) (fun i => lam1 * c i - r i) hne
      obtain ⟨b₁, hb₁T, hb₁max⟩ := Finset.exists_max_image (T p) (fun i => lam1 * c i + r i) hne
      have ha₁S : a₁ ∈ S := (Finset.mem_filter.mp ha₁T).1
      have hb₁S : b₁ ∈ S := (Finset.mem_filter.mp hb₁T).1
      have ha₁sub : J lam2 a₁ ⊆ Set.Icc p.1 p.2 := (Finset.mem_filter.mp ha₁T).2
      have hb₁sub : J lam2 b₁ ⊆ Set.Icc p.1 p.2 := (Finset.mem_filter.mp hb₁T).2
      have hsub_Icc : (⋃ i ∈ T p, J lam1 i) ⊆ Set.Icc (lam1 * c a₁ - r a₁) (lam1 * c b₁ + r b₁) := by
        refine Set.iUnion₂_subset fun i hi => ?_
        exact Set.Icc_subset_Icc (ha₁min i hi) (hb₁max i hi)
      have ha₁_lo : p.1 ≤ lam2 * c a₁ - r a₁ :=
        (ha₁sub ⟨le_rfl, by linarith [hr a₁ ha₁S]⟩).1
      have ha₁_hi : lam2 * c a₁ + r a₁ ≤ p.2 :=
        (ha₁sub ⟨by linarith [hr a₁ ha₁S], le_rfl⟩).2
      have hb₁_lo : p.1 ≤ lam2 * c b₁ - r b₁ :=
        (hb₁sub ⟨le_rfl, by linarith [hr b₁ hb₁S]⟩).1
      have hb₁_hi : lam2 * c b₁ + r b₁ ≤ p.2 :=
        (hb₁sub ⟨by linarith [hr b₁ hb₁S], le_rfl⟩).2
      have hlen : (lam1 * c b₁ + r b₁) - (lam1 * c a₁ - r a₁) ≤ p.2 - p.1 := by
        by_cases hcb : c a₁ ≤ c b₁
        · have : lam1 * (c b₁ - c a₁) ≤ lam2 * (c b₁ - c a₁) :=
            mul_le_mul_of_nonneg_right hlam (sub_nonneg.mpr hcb)
          linarith
        · have hca : c b₁ ≤ c a₁ := le_of_lt (not_le.mp hcb)
          have h1 : lam1 * (c b₁ - c a₁) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam1.le (sub_nonpos.mpr hca)
          have h2 : 0 ≤ lam2 * (c a₁ - c b₁) := mul_nonneg (hlam1.le.trans hlam) (sub_nonneg.mpr hca)
          linarith
      have hnonneg_len : 0 ≤ (lam1 * c b₁ + r b₁) - (lam1 * c a₁ - r a₁) := by
        linarith [hr a₁ ha₁S, hr b₁ hb₁S, ha₁min b₁ hb₁T]
      calc
        volume.real (⋃ i ∈ T p, J lam1 i)
            ≤ volume.real (Set.Icc (lam1 * c a₁ - r a₁) (lam1 * c b₁ + r b₁)) :=
              measureReal_mono hsub_Icc (by simp)
        _ = (lam1 * c b₁ + r b₁) - (lam1 * c a₁ - r a₁) := by
              rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal hnonneg_len]
        _ ≤ p.2 - p.1 := hlen
        _ = volume.real (Set.Icc p.1 p.2) := by
              rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr (hCle p hpC))]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp
  have hfin_C : ∀ p ∈ C, volume (Set.Icc p.1 p.2) ≠ ⊤ := fun _ _ => by simp
  have hfin_T : ∀ p ∈ C, volume (⋃ i ∈ T p, J lam1 i) ≠ ⊤ := fun p _ => by
    have hle_fin : volume (⋃ i ∈ T p, J lam1 i) ≤ ∑ i ∈ T p, volume (J lam1 i) :=
      measure_biUnion_finset_le _ _
    refine ne_top_of_le_ne_top ?_ hle_fin
    exact ENNReal.sum_ne_top.mpr fun i _ => by simp [J]
  have hfin_U : volume (⋃ p ∈ C, ⋃ i ∈ T p, J lam1 i) ≠ ⊤ := by
    have hle_fin := measure_biUnion_finset_le (μ := volume) C (fun p => ⋃ i ∈ T p, J lam1 i)
    exact ne_top_of_le_ne_top (ENNReal.sum_ne_top.mpr hfin_T) hle_fin
  calc
    volume.real (⋃ i ∈ S, J lam1 i)
        ≤ volume.real (⋃ p ∈ C, ⋃ i ∈ T p, J lam1 i) :=
          measureReal_mono hsub_union hfin_U
    _ ≤ ∑ p ∈ C, volume.real (⋃ i ∈ T p, J lam1 i) :=
          measureReal_biUnion_finset_le (μ := volume) C (fun p => ⋃ i ∈ T p, J lam1 i)
    _ ≤ ∑ p ∈ C, volume.real (Set.Icc p.1 p.2) := Finset.sum_le_sum hblock
    _ = volume.real (⋃ p ∈ C, Set.Icc p.1 p.2) := by
          rw [measureReal_biUnion_finset hCdisj (fun _ _ => measurableSet_Icc) hfin_C]
    _ = volume.real (⋃ i ∈ S, J lam2 i) := by rw [hCunion]

private lemma union_Ico_eq_ae_Icc {ι : Type*} (S : Finset ι) (a b : ι → ℝ) :
    (⋃ i ∈ S, Set.Ico (a i) (b i)) =ᵐ[volume] (⋃ i ∈ S, Set.Icc (a i) (b i)) := by
  have hdiff : (⋃ i ∈ S, Set.Icc (a i) (b i)) \ (⋃ i ∈ S, Set.Ico (a i) (b i)) ⊆
      (S.image b : Set ℝ) := by
    intro x ⟨hxcc, hxco⟩
    obtain ⟨i, hiS, hxi⟩ := Set.mem_iUnion₂.mp hxcc
    have hnot : x ∉ Set.Ico (a i) (b i) := fun h => hxco (Set.mem_biUnion hiS h)
    have hxb : x = b i := by
      simp only [Set.mem_Icc, Set.mem_Ico, not_and, not_lt] at hxi hnot
      exact le_antisymm hxi.2 (hnot hxi.1)
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, hiS, hxb.symm⟩)
  have hnull : volume ((⋃ i ∈ S, Set.Icc (a i) (b i)) \ (⋃ i ∈ S, Set.Ico (a i) (b i))) = 0 :=
    measure_mono_null hdiff ((Finset.finite_toSet _).measure_zero volume)
  have hsub : (⋃ i ∈ S, Set.Ico (a i) (b i)) ⊆ (⋃ i ∈ S, Set.Icc (a i) (b i)) :=
    Set.iUnion₂_mono fun _ _ => Set.Ico_subset_Icc_self
  rw [MeasureTheory.ae_eq_set]
  have hempty : (⋃ i ∈ S, Set.Ico (a i) (b i)) \ (⋃ i ∈ S, Set.Icc (a i) (b i)) = ∅ := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_empty_iff_false, iff_false, not_and, not_not]
    exact fun hx => hsub hx
  exact ⟨by rw [hempty, measure_empty], hnull⟩

private lemma real_excess_dilation_mono {m k : ℕ} (hk : 1 ≤ k) (c r : Fin m → ℝ)
    (hr : ∀ i, 0 ≤ r i) {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hs : s₁ ≤ s₂) :
    (1 / s₁) * ∫ x : ℝ, (((Finset.univ.filter fun i : Fin m =>
        x ∈ Set.Icc (c i - s₁ * r i) (c i + s₁ * r i)).card - k : ℕ) : ℝ) ≤
      (1 / s₂) * ∫ x : ℝ, (((Finset.univ.filter fun i : Fin m =>
        x ∈ Set.Icc (c i - s₂ * r i) (c i + s₂ * r i)).card - k : ℕ) : ℝ) := by
  classical
  have hs₂ : 0 < s₂ := lt_of_lt_of_le hs₁ hs
  -- Change of variables: x = s * y turns Icc (c i - s * r i) (c i + s * r i) into Icc (λ * c i - r i) (λ * c i + r i) with λ = 1 / s
  have hcov : ∀ s : ℝ, 0 < s →
      (1 / s) * ∫ x : ℝ, (((Finset.univ.filter fun i : Fin m =>
          x ∈ Set.Icc (c i - s * r i) (c i + s * r i)).card - k : ℕ) : ℝ) =
        ∫ y : ℝ, (((Finset.univ.filter fun i : Fin m =>
          y ∈ Set.Ico ((1 / s) * c i - r i) ((1 / s) * c i + r i)).card - k : ℕ) : ℝ) := by
    intro s hspos
    let f (x : ℝ) : ℝ := (((Finset.univ.filter fun i : Fin m =>
      x ∈ Set.Icc (c i - s * r i) (c i + s * r i)).card - k : ℕ) : ℝ)
    have hmul := Measure.integral_comp_mul_left f s
    rw [abs_inv, abs_of_pos hspos, smul_eq_mul] at hmul
    rw [one_div, ← hmul]
    -- Show integrand agrees a.e. with Ico version
    refine integral_congr_ae ?_
    have hfin : (Finset.univ.image (fun i : Fin m => (1 / s) * c i + r i) : Set ℝ).Finite :=
      Finset.finite_toSet _
    filter_upwards [compl_mem_ae_iff.mpr (hfin.measure_zero volume)] with y hy
    have hmem_iff : ∀ i : Fin m,
        s * y ∈ Set.Icc (c i - s * r i) (c i + s * r i) ↔
          y ∈ Set.Ico ((1 / s) * c i - r i) ((1 / s) * c i + r i) := by
      intro i
      have hne : y ≠ (1 / s) * c i + r i := fun heq =>
        hy (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, heq.symm⟩))
      simp only [Set.mem_Icc, Set.mem_Ico]
      constructor
      · rintro ⟨h1, h2⟩
        have h1' : (1 / s) * c i - r i ≤ y := by
          have := (div_le_iff₀' hspos).mpr (by linarith : c i - s * r i ≤ s * y)
          have heq : (c i - s * r i) / s = (1 / s) * c i - r i := by field_simp
          linarith
        have h2' : y ≤ (1 / s) * c i + r i := by
          have := (le_div_iff₀' hspos).mpr (by linarith : s * y ≤ c i + s * r i)
          have heq : (c i + s * r i) / s = (1 / s) * c i + r i := by field_simp
          linarith
        exact ⟨h1', lt_of_le_of_ne h2' hne⟩
      · rintro ⟨h1, h2⟩
        have h1' : c i - s * r i ≤ s * y := by
          have := mul_le_mul_of_nonneg_left h1 hspos.le
          have heq : s * ((1 / s) * c i - r i) = c i - s * r i := by field_simp
          linarith
        have h2' : s * y ≤ c i + s * r i := by
          have := mul_le_mul_of_nonneg_left h2.le hspos.le
          have heq : s * ((1 / s) * c i + r i) = c i + s * r i := by field_simp
          linarith
        exact ⟨h1', h2'⟩
    dsimp [f]
    congr 3
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← one_div]
    exact hmem_iff i
  rw [hcov s₁ hs₁, hcov s₂ hs₂]
  let lam1 := 1 / s₂
  let lam2 := 1 / s₁
  have hlam1 : 0 < lam1 := one_div_pos.mpr hs₂
  have hlam : lam1 ≤ lam2 := one_div_le_one_div_of_le hs₁ hs
  -- Goal is ∫ (N_{lam2} - k)_+ ≤ ∫ (N_{lam1} - k)_+
  let J (t : ℝ) (i : Fin m) : Set ℝ := Set.Ico (t * c i - r i) (t * c i + r i)
  let N (t : ℝ) (y : ℝ) : ℕ := (Finset.univ.filter fun i : Fin m => y ∈ J t i).card
  -- Integrability of N t, min (N t) k, and (N t - k)_+
  have hN_int : ∀ t : ℝ, Integrable (fun y => (N t y : ℝ)) := by
    intro t
    have heq : (fun y => (N t y : ℝ)) = fun y => ∑ i : Fin m, (J t i).indicator (fun _ => (1 : ℝ)) y := by
      ext y
      simp only [N, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
        Set.indicator]
    rw [heq]
    exact integrable_finsetSum _ fun i _ =>
      (integrableOn_const (by simp [J])).integrable_indicator measurableSet_Ico
  have hN_sum : ∀ t : ℝ, ∫ y : ℝ, (N t y : ℝ) = ∑ i : Fin m, 2 * r i := by
    intro t
    have heq : (fun y => (N t y : ℝ)) = fun y => ∑ i : Fin m, (J t i).indicator (fun _ => (1 : ℝ)) y := by
      ext y
      simp only [N, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
        Set.indicator]
    rw [heq, integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_indicator measurableSet_Ico, setIntegral_const, smul_eq_mul, mul_one,
        measureReal_def, Real.volume_Ico]
      have hnonneg : 0 ≤ (t * c i + r i) - (t * c i - r i) := by linarith [hr i]
      rw [ENNReal.toReal_ofReal hnonneg]
      ring
    · intro i _
      exact (integrableOn_const (by simp [J])).integrable_indicator measurableSet_Ico
  have hmin_int : ∀ t : ℝ, Integrable (fun y => ((min (N t y) k : ℕ) : ℝ)) := by
    intro t
    refine (hN_int t).mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
    · have hmeasN : Measurable (fun y => N t y) := by
        have heq : (fun y => N t y) = fun y => ∑ i : Fin m, Set.indicator (J t i) (fun _ => 1) y := by
          ext y
          simp only [N, Finset.card_filter, Set.indicator]
        rw [heq]
        exact Finset.measurable_sum _ fun i _ => measurable_const.indicator measurableSet_Ico
      exact (Measurable.comp measurable_from_top (hmeasN.min measurable_const)).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast min_le_left (N t y) k
  have hex_int : ∀ t : ℝ, Integrable (fun y => ((N t y - k : ℕ) : ℝ)) := by
    intro t
    have heq : (fun y => ((N t y - k : ℕ) : ℝ)) = fun y => (N t y : ℝ) - ((min (N t y) k : ℕ) : ℝ) := by
      ext y
      by_cases h : k ≤ N t y
      · rw [min_eq_right h, Nat.cast_sub h]
      · rw [min_eq_left (le_of_lt (not_le.mp h)), Nat.sub_eq_zero_of_le (le_of_lt (not_le.mp h))]
        simp
    rw [heq]
    exact (hN_int t).sub (hmin_int t)
  -- Since (N - k)_+ + min(N, k) = N and ∫ N is independent of t, it suffices to show ∫ min(N_{lam1}, k) ≤ ∫ min(N_{lam2}, k)
  suffices hmin_le : ∫ y : ℝ, ((min (N lam1 y) k : ℕ) : ℝ) ≤ ∫ y : ℝ, ((min (N lam2 y) k : ℕ) : ℝ) by
    have hsplit : ∀ t : ℝ,
        (∫ y : ℝ, ((N t y - k : ℕ) : ℝ)) + ∫ y : ℝ, ((min (N t y) k : ℕ) : ℝ) = ∑ i : Fin m, 2 * r i := by
      intro t
      rw [← integral_add (hex_int t) (hmin_int t), ← hN_sum t]
      congr 1; ext y
      by_cases h : k ≤ N t y
      · rw [min_eq_right h, Nat.cast_sub h]; ring
      · rw [min_eq_left (le_of_lt (not_le.mp h)), Nat.sub_eq_zero_of_le (le_of_lt (not_le.mp h))]
        simp
    linarith [hsplit lam1, hsplit lam2]
  -- Apply Lemma 4.1 at lam1
  obtain ⟨col, hcol⟩ := interval_coloring hk (fun i => lam1 * c i - r i) (fun i => lam1 * c i + r i)
  let U (t : ℝ) (a : Fin k) : Set ℝ := ⋃ i ∈ Finset.univ.filter (fun i => col i = a), J t i
  have hU_meas : ∀ t a, MeasurableSet (U t a) := fun t a =>
    Finset.measurableSet_biUnion _ fun _ _ => measurableSet_Ico
  have hU_fin : ∀ t a, volume (U t a) ≠ ⊤ := fun t a => by
    refine ne_top_of_le_ne_top ?_ (measure_biUnion_finset_le _ _)
    exact ENNReal.sum_ne_top.mpr fun _ _ => by simp [J]
  have hU_int : ∀ t a, Integrable ((U t a).indicator (fun _ => (1 : ℝ))) := fun t a =>
    (integrableOn_const (hU_fin t a)).integrable_indicator (hU_meas t a)
  -- At lam1, min(N_{lam1}(y), k) = ∑ a, 1_{U lam1 a}(y)
  have h_eq1 : (fun y => ((min (N lam1 y) k : ℕ) : ℝ)) = fun y => ∑ a : Fin k, (U lam1 a).indicator (fun _ => (1 : ℝ)) y := by
    ext y
    have hcoly : min (N lam1 y) k =
        (Finset.univ.filter fun a : Fin k => ∃ i : Fin m, col i = a ∧ y ∈ J lam1 i).card :=
      (hcol y).symm
    rw [hcoly]
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      Set.indicator, U, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [exists_prop]
  -- At lam2, ∑ a, 1_{U lam2 a}(y) ≤ min(N_{lam2}(y), k)
  have h_le2 : ∀ y : ℝ, ∑ a : Fin k, (U lam2 a).indicator (fun _ => (1 : ℝ)) y ≤ ((min (N lam2 y) k : ℕ) : ℝ) := by
    intro y
    have hcard :
        ∑ a : Fin k, (U lam2 a).indicator (fun _ => (1 : ℝ)) y =
          ((Finset.univ.filter fun a : Fin k => y ∈ U lam2 a).card : ℝ) := by
      simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
        Set.indicator]
    rw [hcard]
    norm_cast
    rw [le_min_iff]
    refine ⟨?_, (Finset.card_le_univ _).trans_eq (Fintype.card_fin k)⟩
    have hsub : (Finset.univ.filter fun a : Fin k => y ∈ U lam2 a) ⊆
        (Finset.univ.filter fun i : Fin m => y ∈ J lam2 i).image col := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, U, Set.mem_iUnion,
        Finset.mem_image] at ha ⊢
      obtain ⟨i, hci, hyi⟩ := ha
      exact ⟨i, hyi, hci⟩
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  calc
    ∫ y : ℝ, ((min (N lam1 y) k : ℕ) : ℝ)
        = ∑ a : Fin k, volume.real (U lam1 a) := by
          rw [h_eq1, integral_finsetSum _ (fun a _ => hU_int lam1 a)]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [integral_indicator (hU_meas lam1 a), setIntegral_const, smul_eq_mul, mul_one]
    _ ≤ ∑ a : Fin k, volume.real (U lam2 a) := by
          refine Finset.sum_le_sum fun a _ => ?_
          let Sa := Finset.univ.filter (fun i : Fin m => col i = a)
          have h1 := measureReal_congr (union_Ico_eq_ae_Icc Sa (fun i => lam1 * c i - r i) (fun i => lam1 * c i + r i))
          have h2 := measureReal_congr (union_Ico_eq_ae_Icc Sa (fun i => lam2 * c i - r i) (fun i => lam2 * c i + r i))
          change volume.real (⋃ i ∈ Sa, Set.Ico (lam1 * c i - r i) (lam1 * c i + r i)) ≤
            volume.real (⋃ i ∈ Sa, Set.Ico (lam2 * c i - r i) (lam2 * c i + r i))
          rw [h1, h2]
          exact union_Icc_mono_center_dilation Sa c r (fun i _ => hr i) hlam1 hlam
    _ = ∫ y : ℝ, ∑ a : Fin k, (U lam2 a).indicator (fun _ => (1 : ℝ)) y := by
          rw [integral_finsetSum _ (fun a _ => hU_int lam2 a)]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [integral_indicator (hU_meas lam2 a), setIntegral_const, smul_eq_mul, mul_one]
    _ ≤ ∫ y : ℝ, ((min (N lam2 y) k : ℕ) : ℝ) :=
          integral_mono (integrable_finsetSum _ fun a _ => hU_int lam2 a) (hmin_int lam2) h_le2

/- ### Part 4: Bohr sets on UnitAddCircle, Lemma 4.3 (Torus lift), and Lemma 3.3 (Type II bounds) -/

private def bohrSet (v : ℕ) (δ : ℝ) : Set UnitAddCircle :=
  (fun t : UnitAddCircle => (v : ℤ) • t) ⁻¹' closedBall 0 δ

private lemma measurableSet_bohrSet (v : ℕ) (δ : ℝ) : MeasurableSet (bohrSet v δ) :=
  measurableSet_closedBall.preimage (continuous_zsmul (v : ℤ)).measurable

private lemma volume_real_bohrSet {v : ℕ} (hv : 0 < v) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : 2 * δ ≤ 1) :
    volume.real (bohrSet v δ) = 2 * δ := by
  have hmp : MeasurePreserving (fun t : UnitAddCircle => (v : ℤ) • t) volume volume :=
    measurePreserving_zsmul volume (by exact_mod_cast hv.ne')
  rw [measureReal_def, bohrSet, hmp.measure_preimage measurableSet_closedBall.nullMeasurableSet,
    AddCircle.volume_closedBall, min_eq_right hδ1, ENNReal.toReal_ofReal (by linarith)]

private lemma mem_bohrSet_coe_iff {v : ℕ} (hv : 0 < v) {δ : ℝ} (x : ℝ) :
    (x : UnitAddCircle) ∈ bohrSet v δ ↔
      ∃ m : ℤ, x ∈ Set.Icc ((m : ℝ) / v - δ / v) ((m : ℝ) / v + δ / v) := by
  have hvR : (0 : ℝ) < (v : ℝ) := Nat.cast_pos.mpr hv
  simp only [bohrSet, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
  have hcoe : ((v : ℤ) • (x : UnitAddCircle)) = (((v : ℝ) * x : ℝ) : UnitAddCircle) := by
    rw [← QuotientAddGroup.mk_zsmul, zsmul_eq_mul, Int.cast_natCast]
  rw [hcoe, UnitAddCircle.norm_eq]
  constructor
  · intro h
    refine ⟨round ((v : ℝ) * x), ?_, ?_⟩
    · rw [abs_le] at h
      have h1 : (round ((v : ℝ) * x) : ℝ) - δ ≤ (v : ℝ) * x := by linarith
      have := (div_le_iff₀' hvR).mpr h1
      linarith [sub_div (round ((v : ℝ) * x) : ℝ) δ (v : ℝ)]
    · rw [abs_le] at h
      have h2 : (v : ℝ) * x ≤ (round ((v : ℝ) * x) : ℝ) + δ := by linarith
      have := (le_div_iff₀' hvR).mpr h2
      linarith [add_div (round ((v : ℝ) * x) : ℝ) δ (v : ℝ)]
  · rintro ⟨m, h1, h2⟩
    have h1' : (m : ℝ) - δ ≤ (v : ℝ) * x := by
      have := mul_le_mul_of_nonneg_left h1 hvR.le
      have heq : (v : ℝ) * ((m : ℝ) / (v : ℝ) - δ / (v : ℝ)) = (m : ℝ) - δ := by field_simp
      linarith
    have h2' : (v : ℝ) * x ≤ (m : ℝ) + δ := by
      have := mul_le_mul_of_nonneg_left h2 hvR.le
      have heq : (v : ℝ) * ((m : ℝ) / (v : ℝ) + δ / (v : ℝ)) = (m : ℝ) + δ := by field_simp
      linarith
    have habs : |(v : ℝ) * x - (m : ℝ)| ≤ δ := abs_le.mpr ⟨by linarith, by linarith⟩
    exact (round_le ((v : ℝ) * x) m).trans habs

private lemma bohrSet_intervals_disjoint {v : ℕ} (hv : 0 < v) {δ : ℝ} (hδ : δ < 1 / 2)
    {m₁ m₂ : ℤ} (hm : m₁ ≠ m₂) :
    Disjoint (Set.Icc ((m₁ : ℝ) / v - δ / v) ((m₁ : ℝ) / v + δ / v))
      (Set.Icc ((m₂ : ℝ) / v - δ / v) ((m₂ : ℝ) / v + δ / v)) := by
  have hvR : (0 : ℝ) < (v : ℝ) := Nat.cast_pos.mpr hv
  rw [Set.disjoint_left]
  intro x hx1 hx2
  have hdiff : |(m₁ : ℝ) - (m₂ : ℝ)| ≤ 2 * δ := by
    have h1 : (m₁ : ℝ) - δ ≤ (v : ℝ) * x ∧ (v : ℝ) * x ≤ (m₁ : ℝ) + δ := by
      have ha := mul_le_mul_of_nonneg_left hx1.1 hvR.le
      have hb := mul_le_mul_of_nonneg_left hx1.2 hvR.le
      have e1 : (v : ℝ) * ((m₁ : ℝ) / (v : ℝ) - δ / (v : ℝ)) = (m₁ : ℝ) - δ := by field_simp
      have e2 : (v : ℝ) * ((m₁ : ℝ) / (v : ℝ) + δ / (v : ℝ)) = (m₁ : ℝ) + δ := by field_simp
      exact ⟨by linarith, by linarith⟩
    have h2 : (m₂ : ℝ) - δ ≤ (v : ℝ) * x ∧ (v : ℝ) * x ≤ (m₂ : ℝ) + δ := by
      have ha := mul_le_mul_of_nonneg_left hx2.1 hvR.le
      have hb := mul_le_mul_of_nonneg_left hx2.2 hvR.le
      have e1 : (v : ℝ) * ((m₂ : ℝ) / (v : ℝ) - δ / (v : ℝ)) = (m₂ : ℝ) - δ := by field_simp
      have e2 : (v : ℝ) * ((m₂ : ℝ) / (v : ℝ) + δ / (v : ℝ)) = (m₂ : ℝ) + δ := by field_simp
      exact ⟨by linarith, by linarith⟩
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hge1 : (1 : ℝ) ≤ |(m₁ : ℝ) - (m₂ : ℝ)| := by
    have hne : m₁ - m₂ ≠ 0 := sub_ne_zero.mpr hm
    have habs : (1 : ℤ) ≤ |m₁ - m₂| := Int.one_le_abs hne
    exact_mod_cast habs
  linarith

private lemma torus_excess_dilation_mono {n k : ℕ} (hk : 1 ≤ k)
    (v : Fin n → ℕ) (hv : ∀ i, 0 < v i)
    {δ₀ δ₁ : ℝ} (hδ₀ : 0 < δ₀) (hδ : δ₀ ≤ δ₁) (hδ₁ : δ₁ < 1 / 2) :
    (1 / δ₀) * ∫ t : UnitAddCircle,
        (((Finset.univ.filter fun i : Fin n => t ∈ bohrSet (v i) δ₀).card - k : ℕ) : ℝ) ≤
      (1 / δ₁) * ∫ t : UnitAddCircle,
        (((Finset.univ.filter fun i : Fin n => t ∈ bohrSet (v i) δ₁).card - k : ℕ) : ℝ) := by
  classical
  let N (δ : ℝ) (t : UnitAddCircle) : ℕ :=
    (Finset.univ.filter fun i : Fin n => t ∈ bohrSet (v i) δ).card
  let F (δ : ℝ) (t : UnitAddCircle) : ℝ := ((N δ t - k : ℕ) : ℝ)
  have hF_meas : ∀ δ : ℝ, Measurable (F δ) := by
    intro δ
    have hmeasN : Measurable (N δ) := by
      have heq : N δ = fun t => ∑ i : Fin n, (bohrSet (v i) δ).indicator (fun _ => 1) t := by
        ext t; simp only [N, Finset.card_filter, Set.indicator]
      rw [heq]
      exact Finset.measurable_sum _ fun i _ => measurable_const.indicator (measurableSet_bohrSet _ _)
    exact Measurable.comp measurable_from_top (hmeasN.sub measurable_const)
  have hF_int : ∀ δ : ℝ, Integrable (F δ) := by
    intro δ
    refine Integrable.of_bound (hF_meas δ).aestronglyMeasurable (n : ℝ) (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast (Nat.sub_le _ _).trans ((Finset.card_filter_le _ _).trans_eq (Fintype.card_fin n))
  -- For any integer L ≥ 1, define finite lifted family of intervals with shifts q ∈ Icc (-L) L
  have hL_bound : ∀ L : ℕ, 1 ≤ L →
      (1 / δ₀) * ((2 * (L : ℝ) - 1) * (∫ t : UnitAddCircle, F δ₀ t)) ≤
        (1 / δ₁) * ((2 * (L : ℝ) - 1) * (∫ t : UnitAddCircle, F δ₁ t) + 4 * (n : ℝ)) := by
    intro L hL
    -- Index type: (i : Fin n) × (a : Fin (v i)) × (q : Fin (2*L + 1)), with center q - L + a / v i and radius 1 / v i
    let α := Σ i : Fin n, Fin (v i) × Fin (2 * L + 1)
    let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
    let center (idx : α) : ℝ :=
      ((idx.2.2.1 : ℤ) - (L : ℤ) : ℤ) + (idx.2.1.1 : ℝ) / (v idx.1 : ℝ)
    let rad (idx : α) : ℝ := 1 / (v idx.1 : ℝ)
    have hrad : ∀ idx : α, 0 ≤ rad idx := fun idx => by positivity
    let NL (δ : ℝ) (x : ℝ) : ℕ :=
      (Finset.univ.filter fun idx : α =>
        x ∈ Set.Icc (center idx - δ * rad idx) (center idx + δ * rad idx)).card
    let FL (δ : ℝ) (x : ℝ) : ℝ := ((NL δ x - k : ℕ) : ℝ)
    -- Apply real_excess_dilation_mono via e.symm
    have hmono : (1 / δ₀) * ∫ x : ℝ, FL δ₀ x ≤ (1 / δ₁) * ∫ x : ℝ, FL δ₁ x := by
      have hre := real_excess_dilation_mono hk (center ∘ e.symm) (rad ∘ e.symm)
        (fun j => hrad (e.symm j)) hδ₀ hδ
      have hcard_eq : ∀ δ x,
          (Finset.univ.filter fun j : Fin (Fintype.card α) =>
            x ∈ Set.Icc ((center ∘ e.symm) j - δ * (rad ∘ e.symm) j)
              ((center ∘ e.symm) j + δ * (rad ∘ e.symm) j)).card = NL δ x := by
        intro δ x
        refine Finset.card_bij (fun j _ => e.symm j) ?_ ?_ ?_
        · intro j hj; simpa [Function.comp_apply] using hj
        · intro j₁ _ j₂ _ h; exact e.symm.injective h
        · intro idx hidx
          exact ⟨e idx, by simpa [Function.comp_apply] using hidx, by simp⟩
      have hfn_eq : ∀ δ,
          (fun x : ℝ => (((Finset.univ.filter fun j : Fin (Fintype.card α) =>
            x ∈ Set.Icc ((center ∘ e.symm) j - δ * (rad ∘ e.symm) j)
              ((center ∘ e.symm) j + δ * (rad ∘ e.symm) j)).card - k : ℕ) : ℝ)) = FL δ := by
        intro δ
        ext x
        dsimp only [FL]
        have hc :
            (Finset.univ.filter fun j : Fin (Fintype.card α) =>
              x ∈ Set.Icc ((center ∘ e.symm) j - δ * (rad ∘ e.symm) j)
                ((center ∘ e.symm) j + δ * (rad ∘ e.symm) j)).card = NL δ x :=
          hcard_eq δ x
        rw [hc]
      rw [hfn_eq δ₀, hfn_eq δ₁] at hre
      exact hre
    -- Key properties of NL δ x for any 0 < δ < 1/2:
    have hNL_props : ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
        (∀ x, NL δ x ≤ n) ∧
        (∀ x ∈ Set.Ioc (-(L : ℝ) + 1) (L : ℝ), NL δ x = N δ (x : UnitAddCircle)) ∧
        (∀ x, x ∉ Set.Ioc (-(L : ℝ) - 1) ((L : ℝ) + 2) → NL δ x = 0) := by
      intro δ hδpos hδlt
      have hcenter_eq : ∀ (idx : α),
          center idx = ((((idx.2.2.1 : ℤ) - (L : ℤ)) * (v idx.1 : ℤ) + (idx.2.1.1 : ℤ) : ℤ) : ℝ) / (v idx.1 : ℝ) ∧
          δ * rad idx = δ / (v idx.1 : ℝ) := by
        intro idx
        have hvne : (v idx.1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hv idx.1).ne'
        constructor
        · dsimp [center]; push_cast; field_simp
        · dsimp [rad]; ring
      -- For fixed i and x, at most one pair (a, q) covers x
      have huniq : ∀ (i : Fin n) (x : ℝ) (p₁ p₂ : Fin (v i) × Fin (2 * L + 1)),
          x ∈ Set.Icc (center ⟨i, p₁⟩ - δ * rad ⟨i, p₁⟩) (center ⟨i, p₁⟩ + δ * rad ⟨i, p₁⟩) →
          x ∈ Set.Icc (center ⟨i, p₂⟩ - δ * rad ⟨i, p₂⟩) (center ⟨i, p₂⟩ + δ * rad ⟨i, p₂⟩) →
          p₁ = p₂ := by
        intro i x p₁ p₂ h1 h2
        rw [(hcenter_eq ⟨i, p₁⟩).1, (hcenter_eq ⟨i, p₁⟩).2] at h1
        rw [(hcenter_eq ⟨i, p₂⟩).1, (hcenter_eq ⟨i, p₂⟩).2] at h2
        have hmeq :
            ((p₁.2.1 : ℤ) - (L : ℤ)) * (v i : ℤ) + (p₁.1.1 : ℤ) =
              ((p₂.2.1 : ℤ) - (L : ℤ)) * (v i : ℤ) + (p₂.1.1 : ℤ) := by
          by_contra hne
          exact Set.disjoint_left.mp (bohrSet_intervals_disjoint (hv i) hδlt hne) h1 h2
        have hvpos : (0 : ℤ) < (v i : ℤ) := Int.natCast_pos.mpr (hv i)
        have ha1 : (p₁.1.1 : ℤ) < (v i : ℤ) := Int.ofNat_lt.mpr p₁.1.2
        have ha2 : (p₂.1.1 : ℤ) < (v i : ℤ) := Int.ofNat_lt.mpr p₂.1.2
        have hqeq : (p₁.2.1 : ℤ) = (p₂.2.1 : ℤ) := by nlinarith
        have haeq : (p₁.1.1 : ℤ) = (p₂.1.1 : ℤ) := by rw [hqeq] at hmeq; linarith
        exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
      refine ⟨?_, ?_, ?_⟩
      · -- NL δ x ≤ n via injective projection Sigma.fst
        intro x
        have hinj : Set.InjOn Sigma.fst
            ((Finset.univ.filter fun idx : α =>
              x ∈ Set.Icc (center idx - δ * rad idx) (center idx + δ * rad idx)) : Set α) := by
          intro idx₁ h1 idx₂ h2 hfst
          rcases idx₁ with ⟨i₁, p₁⟩
          rcases idx₂ with ⟨i₂, p₂⟩
          dsimp at hfst; subst hfst
          rw [Finset.mem_coe, Finset.mem_filter] at h1 h2
          exact congrArg (Sigma.mk i₁) (huniq i₁ x p₁ p₂ h1.2 h2.2)
        calc
          NL δ x = ((Finset.univ.filter fun idx : α =>
              x ∈ Set.Icc (center idx - δ * rad idx) (center idx + δ * rad idx)).image Sigma.fst).card :=
            (Finset.card_image_of_injOn hinj).symm
          _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
          _ = n := Fintype.card_fin n
      · -- For x ∈ Ioc (-L + 1) L, NL δ x = N δ (x : UnitAddCircle)
        intro x hx
        have hbij :
            ((Finset.univ.filter fun idx : α =>
              x ∈ Set.Icc (center idx - δ * rad idx) (center idx + δ * rad idx)).image Sigma.fst) =
            Finset.univ.filter fun i : Fin n => (x : UnitAddCircle) ∈ bohrSet (v i) δ := by
          ext i
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨⟨j, p⟩, hxp, rfl⟩
            rw [mem_bohrSet_coe_iff (hv j)]
            rw [(hcenter_eq ⟨j, p⟩).1, (hcenter_eq ⟨j, p⟩).2] at hxp
            exact ⟨_, hxp⟩
          · intro hxi
            rw [mem_bohrSet_coe_iff (hv i)] at hxi
            obtain ⟨m, hxm⟩ := hxi
            -- Write m = q * v i + a with 0 ≤ a < v i
            let q : ℤ := m / (v i : ℤ)
            let a : ℕ := (m % (v i : ℤ)).toNat
            have hvpos : (0 : ℤ) < (v i : ℤ) := Int.natCast_pos.mpr (hv i)
            have hrem_nn : 0 ≤ m % (v i : ℤ) := Int.emod_nonneg m hvpos.ne'
            have hrem_lt : m % (v i : ℤ) < (v i : ℤ) := Int.emod_lt_of_pos m hvpos
            have ha_lt : a < v i := by omega
            have hm_eq : m = q * (v i : ℤ) + (a : ℤ) := by
              have := Int.emod_add_mul_ediv m (v i : ℤ)
              dsimp [q, a] at *
              have haZ : ((m % (v i : ℤ)).toNat : ℤ) = m % (v i : ℤ) := Int.toNat_of_nonneg hrem_nn
              linarith
            -- Bound q from x ∈ (-L + 1, L] and |x - m / v i| ≤ δ / v i < 1/2
            have hvR : (0 : ℝ) < (v i : ℝ) := Nat.cast_pos.mpr (hv i)
            have hq_lo : -(L : ℤ) ≤ q := by
              have h1 : (q : ℝ) ≤ (m : ℝ) / (v i : ℝ) := by
                have : (q : ℝ) * (v i : ℝ) ≤ (m : ℝ) := by
                  have : q * (v i : ℤ) ≤ m := by omega
                  exact_mod_cast this
                exact (le_div_iff₀ hvR).mpr this
              have h2 : (m : ℝ) / (v i : ℝ) ≤ (q : ℝ) + 1 := by
                have : (m : ℝ) < ((q : ℝ) + 1) * (v i : ℝ) := by
                  have : m < (q + 1) * (v i : ℤ) := by nlinarith
                  exact_mod_cast this
                exact le_of_lt ((div_lt_iff₀ hvR).mpr this)
              have hδv : δ / (v i : ℝ) ≤ δ := div_le_self hδpos.le (by exact_mod_cast hv i)
              have hqR : -(L : ℝ) - 1 < (q : ℝ) := by linarith [hx.1, hxm.2, h2, hδv, hδlt]
              have : -(L : ℤ) - 1 < q := by exact_mod_cast hqR
              omega
            have hq_hi : q ≤ (L : ℤ) := by
              have h1 : (q : ℝ) ≤ (m : ℝ) / (v i : ℝ) := by
                have : (q : ℝ) * (v i : ℝ) ≤ (m : ℝ) := by
                  have : q * (v i : ℤ) ≤ m := by omega
                  exact_mod_cast this
                exact (le_div_iff₀ hvR).mpr this
              have hδv : δ / (v i : ℝ) ≤ δ := div_le_self hδpos.le (by exact_mod_cast hv i)
              have hqR : (q : ℝ) < (L : ℝ) + 1 := by linarith [hx.2, hxm.1, h1, hδv, hδlt]
              have : q < (L : ℤ) + 1 := by exact_mod_cast hqR
              omega
            let qn : ℕ := (q + (L : ℤ)).toNat
            have hqn_lt : qn < 2 * L + 1 := by omega
            refine ⟨⟨i, ⟨a, ha_lt⟩, ⟨qn, hqn_lt⟩⟩, ?_, rfl⟩
            rw [(hcenter_eq ⟨i, ⟨a, ha_lt⟩, ⟨qn, hqn_lt⟩⟩).1,
              (hcenter_eq ⟨i, ⟨a, ha_lt⟩, ⟨qn, hqn_lt⟩⟩).2]
            have hqn_eq : (qn : ℤ) - (L : ℤ) = q := by
              dsimp [qn]
              have : ((q + (L : ℤ)).toNat : ℤ) = q + (L : ℤ) := Int.toNat_of_nonneg (by omega)
              linarith
            have hmeq' : ((qn : ℤ) - (L : ℤ)) * (v i : ℤ) + (a : ℤ) = m := by
              rw [hqn_eq]; exact hm_eq.symm
            rwa [hmeq']
        have hinj : Set.InjOn Sigma.fst
            ((Finset.univ.filter fun idx : α =>
              x ∈ Set.Icc (center idx - δ * rad idx) (center idx + δ * rad idx)) : Set α) := by
          intro idx₁ h1 idx₂ h2 hfst
          rcases idx₁ with ⟨i₁, p₁⟩
          rcases idx₂ with ⟨i₂, p₂⟩
          dsimp at hfst; subst hfst
          rw [Finset.mem_coe, Finset.mem_filter] at h1 h2
          exact congrArg (Sigma.mk i₁) (huniq i₁ x p₁ p₂ h1.2 h2.2)
        dsimp [NL, N]
        rw [← hbij, Finset.card_image_of_injOn hinj]
      · -- Support of NL δ is inside Ioc (-L - 1) (L + 2)
        intro x hx
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro idx _ hmem
        apply hx
        have hv1 : (1 : ℝ) ≤ (v idx.1 : ℝ) := by exact_mod_cast hv idx.1
        have ha0 : 0 ≤ (idx.2.1.1 : ℝ) / (v idx.1 : ℝ) := by positivity
        have ha1 : (idx.2.1.1 : ℝ) / (v idx.1 : ℝ) ≤ 1 := by
          rw [div_le_one (by positivity)]
          exact_mod_cast le_of_lt idx.2.1.2
        have hq0 : -(L : ℝ) ≤ (((idx.2.2.1 : ℤ) - (L : ℤ) : ℤ) : ℝ) := by
          push_cast; linarith [Nat.cast_nonneg (α := ℝ) idx.2.2.1]
        have hq1 : (((idx.2.2.1 : ℤ) - (L : ℤ) : ℤ) : ℝ) ≤ (L : ℝ) := by
          have : idx.2.2.1 ≤ 2 * L := Nat.lt_succ_iff.mp idx.2.2.2
          have : (idx.2.2.1 : ℝ) ≤ 2 * (L : ℝ) := by exact_mod_cast this
          push_cast; linarith
        have hrad1 : δ * rad idx < 1 / 2 := by
          dsimp [rad]
          have : δ * (1 / (v idx.1 : ℝ)) ≤ δ := by
            rw [mul_one_div]
            exact div_le_self hδpos.le hv1
          linarith
        dsimp [center] at hmem
        exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
    -- Integrate F δ over Ioc (-L + 1) L = (2L - 1) * ∫_T F δ
    have hcore_int : ∀ δ : ℝ,
        ∫ x in Set.Ioc (-(L : ℝ) + 1) (L : ℝ), F δ (x : UnitAddCircle) =
          (2 * (L : ℝ) - 1) * ∫ t : UnitAddCircle, F δ t := by
      intro δ
      -- Split Ioc (-L + 1) L into 2L - 1 unit intervals Ioc (-(L:ℝ) + 1 + j) (-(L:ℝ) + 1 + j + 1)
      have hlen : (-(L : ℝ) + 1) + ((2 * L - 1 : ℕ) : ℝ) = (L : ℝ) := by
        have : ((2 * L - 1 : ℕ) : ℝ) = 2 * (L : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        linarith
      have hsum : ∀ m : ℕ, ∀ a : ℝ,
          ∫ x in Set.Ioc a (a + (m : ℝ)), F δ (x : UnitAddCircle) =
            (m : ℝ) * ∫ t : UnitAddCircle, F δ t := by
        intro m
        induction m with
        | zero => intro a; simp
        | succ m' ihm =>
          intro a
          have h1 : a ≤ a + (m' : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) m']
          have h2 : a + (m' : ℝ) ≤ a + ((m' + 1 : ℕ) : ℝ) := by push_cast; linarith
          have hunion : Set.Ioc a (a + ((m' + 1 : ℕ) : ℝ)) =
              Set.Ioc a (a + (m' : ℝ)) ∪ Set.Ioc (a + (m' : ℝ)) (a + (m' : ℝ) + 1) := by
            have heq : a + ((m' + 1 : ℕ) : ℝ) = a + (m' : ℝ) + 1 := by push_cast; ring
            rw [heq, Set.Ioc_union_Ioc_eq_Ioc h1 (by linarith)]
          have hdisj : Disjoint (Set.Ioc a (a + (m' : ℝ))) (Set.Ioc (a + (m' : ℝ)) (a + (m' : ℝ) + 1)) :=
            Set.Ioc_disjoint_Ioc_of_le le_rfl
          have hint1 : IntegrableOn (fun x : ℝ => F δ (x : UnitAddCircle)) (Set.Ioc a (a + (m' : ℝ))) := by
            refine IntegrableOn.of_bound (by simp)
              ((hF_meas δ).comp AddCircle.measurable_mk').aestronglyMeasurable.restrict
              (n : ℝ) (Filter.Eventually.of_forall fun x => ?_)
            rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
            exact_mod_cast (Nat.sub_le _ _).trans ((Finset.card_filter_le _ _).trans_eq (Fintype.card_fin n))
          have hint2 : IntegrableOn (fun x : ℝ => F δ (x : UnitAddCircle))
              (Set.Ioc (a + (m' : ℝ)) (a + (m' : ℝ) + 1)) := by
            refine IntegrableOn.of_bound (by simp)
              ((hF_meas δ).comp AddCircle.measurable_mk').aestronglyMeasurable.restrict
              (n : ℝ) (Filter.Eventually.of_forall fun x => ?_)
            rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
            exact_mod_cast (Nat.sub_le _ _).trans ((Finset.card_filter_le _ _).trans_eq (Fintype.card_fin n))
          rw [hunion, setIntegral_union hdisj measurableSet_Ioc hint1 hint2,
            ihm a, AddCircle.integral_preimage 1 (a + (m' : ℝ)) (F δ)]
          push_cast; ring
      have := hsum (2 * L - 1) (-(L : ℝ) + 1)
      rw [hlen] at this
      have hcast : ((2 * L - 1 : ℕ) : ℝ) = 2 * (L : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rwa [hcast] at this
    -- Compare ∫ FL δ₀ ≥ (2L-1) ∫ F δ₀ and ∫ FL δ₁ ≤ (2L-1) ∫ F δ₁ + 4 n
    have hFL_int : ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → Integrable (FL δ) := by
      intro δ hδpos hδlt
      have ⟨hbd, _, hsupp⟩ := hNL_props δ hδpos hδlt
      have hmeas : Measurable (FL δ) := by
        have hmeasNL : Measurable (NL δ) := by
          have heq : NL δ = fun x => ∑ idx : α,
              (Set.Icc (center idx - δ * rad idx) (center idx + δ * rad idx)).indicator (fun _ => 1) x := by
            ext x; simp only [NL, Finset.card_filter, Set.indicator]
          rw [heq]
          exact Finset.measurable_sum _ fun _ _ => measurable_const.indicator measurableSet_Icc
        exact Measurable.comp measurable_from_top (hmeasNL.sub measurable_const)
      have heq_ind : FL δ = (Set.Ioc (-(L : ℝ) - 1) ((L : ℝ) + 2)).indicator (FL δ) := by
        ext x
        by_cases hx : x ∈ Set.Ioc (-(L : ℝ) - 1) ((L : ℝ) + 2)
        · simp [hx]
        · simp [hx, FL, hsupp x hx]
      rw [heq_ind]
      refine (IntegrableOn.of_bound (by simp) hmeas.aestronglyMeasurable.restrict (n : ℝ)
        (Filter.Eventually.of_forall fun x => ?_)).integrable_indicator measurableSet_Ioc
      rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast (Nat.sub_le _ _).trans (hbd x)
    have hlo : (2 * (L : ℝ) - 1) * ∫ t : UnitAddCircle, F δ₀ t ≤ ∫ x : ℝ, FL δ₀ x := by
      rw [← hcore_int δ₀]
      have ⟨_, heq_core, _⟩ := hNL_props δ₀ hδ₀ (lt_of_le_of_lt hδ hδ₁)
      have h1 : ∫ x in Set.Ioc (-(L : ℝ) + 1) (L : ℝ), F δ₀ (x : UnitAddCircle) =
          ∫ x in Set.Ioc (-(L : ℝ) + 1) (L : ℝ), FL δ₀ x :=
        setIntegral_congr_fun measurableSet_Ioc fun x hx => by simp [F, FL, heq_core x hx]
      rw [h1]
      exact setIntegral_le_integral (hFL_int δ₀ hδ₀ (lt_of_le_of_lt hδ hδ₁))
        (Filter.Eventually.of_forall fun x => Nat.cast_nonneg _)
    have hhi : ∫ x : ℝ, FL δ₁ x ≤ (2 * (L : ℝ) - 1) * (∫ t : UnitAddCircle, F δ₁ t) + 4 * (n : ℝ) := by
      have ⟨hbd, heq_core, hsupp⟩ := hNL_props δ₁ (lt_of_lt_of_le hδ₀ hδ) hδ₁
      have hFL_Ioc : ∫ x : ℝ, FL δ₁ x = ∫ x in Set.Ioc (-(L : ℝ) - 1) ((L : ℝ) + 2), FL δ₁ x := by
        rw [← integral_indicator measurableSet_Ioc]
        congr 1; ext x
        by_cases hx : x ∈ Set.Ioc (-(L : ℝ) - 1) ((L : ℝ) + 2)
        · simp [hx]
        · simp [hx, FL, hsupp x hx]
      have hsplit1 : Set.Ioc (-(L : ℝ) - 1) ((L : ℝ) + 2) =
          Set.Ioc (-(L : ℝ) - 1) (-(L : ℝ) + 1) ∪
          (Set.Ioc (-(L : ℝ) + 1) (L : ℝ) ∪ Set.Ioc (L : ℝ) ((L : ℝ) + 2)) := by
        have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
        rw [Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith),
          Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)]
      have hint_all := hFL_int δ₁ (lt_of_lt_of_le hδ₀ hδ) hδ₁
      rw [hFL_Ioc, hsplit1,
        setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl |>.mono_right (by
          rw [Set.Ioc_union_Ioc_eq_Ioc (by linarith [(by exact_mod_cast hL : (1 : ℝ) ≤ L)]) (by linarith)]))
          (measurableSet_Ioc.union measurableSet_Ioc) hint_all.integrableOn hint_all.integrableOn,
        setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
          hint_all.integrableOn hint_all.integrableOn]
      have hcore1 : ∫ x in Set.Ioc (-(L : ℝ) + 1) (L : ℝ), FL δ₁ x =
          (2 * (L : ℝ) - 1) * ∫ t : UnitAddCircle, F δ₁ t := by
        rw [← hcore_int δ₁]
        exact setIntegral_congr_fun measurableSet_Ioc fun x hx => by simp [F, FL, heq_core x hx]
      have hbnd_strip : ∀ a b : ℝ, a ≤ b →
          ∫ x in Set.Ioc a b, FL δ₁ x ≤ (b - a) * (n : ℝ) := by
        intro a b hab
        calc
          ∫ x in Set.Ioc a b, FL δ₁ x ≤ ∫ _x in Set.Ioc a b, (n : ℝ) := by
            refine setIntegral_mono_on hint_all.integrableOn (integrableOn_const (by simp))
              measurableSet_Ioc fun x _ => ?_
            dsimp [FL]
            exact_mod_cast (Nat.sub_le (NL δ₁ x) k).trans (hbd x)
          _ = (b - a) * (n : ℝ) := by
            rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Ioc,
              ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
      have hsL : ∫ x in Set.Ioc (-(L : ℝ) - 1) (-(L : ℝ) + 1), FL δ₁ x ≤ 2 * (n : ℝ) := by
        have h1 := hbnd_strip (-(L : ℝ) - 1) (-(L : ℝ) + 1) (by linarith)
        have h2 : (-(L : ℝ) + 1 - (-(L : ℝ) - 1)) * (n : ℝ) = 2 * (n : ℝ) := by ring
        linarith
      have hsR : ∫ x in Set.Ioc (L : ℝ) ((L : ℝ) + 2), FL δ₁ x ≤ 2 * (n : ℝ) := by
        have h1 := hbnd_strip (L : ℝ) ((L : ℝ) + 2) (by linarith)
        have h2 : ((L : ℝ) + 2 - (L : ℝ)) * (n : ℝ) = 2 * (n : ℝ) := by ring
        linarith
      rw [hcore1]
      calc
        (∫ x in Set.Ioc (-(L : ℝ) - 1) (-(L : ℝ) + 1), FL δ₁ x) +
            ((2 * (L : ℝ) - 1) * (∫ t : UnitAddCircle, F δ₁ t) +
              ∫ x in Set.Ioc (L : ℝ) ((L : ℝ) + 2), FL δ₁ x)
            ≤ 2 * (n : ℝ) + ((2 * (L : ℝ) - 1) * (∫ t : UnitAddCircle, F δ₁ t) + 2 * (n : ℝ)) :=
              add_le_add hsL (add_le_add le_rfl hsR)
        _ = (2 * (L : ℝ) - 1) * (∫ t : UnitAddCircle, F δ₁ t) + 4 * (n : ℝ) := by ring
    have hδ₁_pos : 0 < δ₁ := lt_of_lt_of_le hδ₀ hδ
    have hδ₀_nn : 0 ≤ 1 / δ₀ := by positivity
    have hδ₁_nn : 0 ≤ 1 / δ₁ := by positivity
    calc
      (1 / δ₀) * ((2 * (L : ℝ) - 1) * ∫ t : UnitAddCircle, F δ₀ t)
          ≤ (1 / δ₀) * ∫ x : ℝ, FL δ₀ x := mul_le_mul_of_nonneg_left hlo hδ₀_nn
      _ ≤ (1 / δ₁) * ∫ x : ℝ, FL δ₁ x := hmono
      _ ≤ (1 / δ₁) * ((2 * (L : ℝ) - 1) * (∫ t : UnitAddCircle, F δ₁ t) + 4 * (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hhi hδ₁_nn
  -- Conclude by letting L → ∞ (contradiction if LHS > RHS)
  by_contra hnot
  push Not at hnot
  have hδ₁_pos : 0 < δ₁ := lt_of_lt_of_le hδ₀ hδ
  have hdiff : 0 < (1 / δ₀) * (∫ t : UnitAddCircle, F δ₀ t) - (1 / δ₁) * (∫ t : UnitAddCircle, F δ₁ t) :=
    sub_pos.mpr hnot
  obtain ⟨L, hL⟩ := exists_nat_gt (((1 / δ₁) * (4 * (n : ℝ))) /
    ((1 / δ₀) * (∫ t : UnitAddCircle, F δ₀ t) - (1 / δ₁) * (∫ t : UnitAddCircle, F δ₁ t)) + 1)
  have hL1 : 1 ≤ L := by
    have hnn : 0 ≤ ((1 / δ₁) * (4 * (n : ℝ))) /
        ((1 / δ₀) * (∫ t : UnitAddCircle, F δ₀ t) - (1 / δ₁) * (∫ t : UnitAddCircle, F δ₁ t)) := by
      positivity
    have : (1 : ℝ) < (L : ℝ) := by linarith
    exact_mod_cast le_of_lt this
  have hLb := hL_bound L hL1
  have h2L : ((1 / δ₁) * (4 * (n : ℝ))) /
      ((1 / δ₀) * (∫ t : UnitAddCircle, F δ₀ t) - (1 / δ₁) * (∫ t : UnitAddCircle, F δ₁ t)) <
      2 * (L : ℝ) - 1 := by linarith
  have hmul := (div_lt_iff₀ hdiff).mp h2L
  have e1 : (1 / δ₀) * ((2 * (L : ℝ) - 1) * (∫ t : UnitAddCircle, F δ₀ t)) =
      (2 * (L : ℝ) - 1) * ((1 / δ₀) * (∫ t : UnitAddCircle, F δ₀ t)) := by ring
  have e2 : (1 / δ₁) * ((2 * (L : ℝ) - 1) * (∫ t : UnitAddCircle, F δ₁ t) + 4 * (n : ℝ)) =
      (2 * (L : ℝ) - 1) * ((1 / δ₁) * (∫ t : UnitAddCircle, F δ₁ t)) + (1 / δ₁) * (4 * (n : ℝ)) := by ring
  have e3 : (2 * (L : ℝ) - 1) *
      ((1 / δ₀) * (∫ t : UnitAddCircle, F δ₀ t) - (1 / δ₁) * (∫ t : UnitAddCircle, F δ₁ t)) =
      (2 * (L : ℝ) - 1) * ((1 / δ₀) * (∫ t : UnitAddCircle, F δ₀ t)) -
        (2 * (L : ℝ) - 1) * ((1 / δ₁) * (∫ t : UnitAddCircle, F δ₁ t)) := by ring
  linarith

/- ### Part 5: Lemma 3.3 (Pairwise Type II Bohr-set overlap bounds) -/

private def trap (α β x : ℝ) : ℝ :=
  max 0 (min α (β - |x|) - max (-α) (-β - |x|))

private lemma trap_eq_measureReal {α β : ℝ} (_hα : 0 ≤ α) (_hβ : 0 ≤ β) (x : ℝ) :
    volume.real (Set.Icc (-α) α ∩ Set.Icc (-β - x) (β - x)) = trap α β x := by
  have hsym : ∀ y : ℝ,
      volume.real (Set.Icc (-α) α ∩ Set.Icc (-β - y) (β - y)) =
        max 0 (min α (β - y) - max (-α) (-β - y)) := by
    intro y
    rw [Set.Icc_inter_Icc, measureReal_def, Real.volume_Icc]
    by_cases h : max (-α) (-β - y) ≤ min α (β - y)
    · rw [ENNReal.toReal_ofReal (sub_nonneg.mpr h), max_eq_right (sub_nonneg.mpr h)]
    · rw [ENNReal.ofReal_of_nonpos (sub_nonpos.mpr (le_of_lt (not_le.mp h))),
        ENNReal.toReal_zero, max_eq_left (sub_nonpos.mpr (le_of_lt (not_le.mp h)))]
  rw [hsym x]
  dsimp [trap]
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg (not_le.mp hx)]
    -- Symmetry: min α (β - x) - max (-α) (-β - x) = min α (β + x) - max (-α) (-β + x)
    have hsub1 : β - -x = β + x := by ring
    have hsub2 : -β - -x = -β + x := by ring
    rw [hsub1, hsub2]
    congr 1
    have h1 : -max (-α) (-β - x) = min α (β + x) := by
      rw [← min_neg_neg, neg_neg]; congr 1; ring
    have h2 : -min α (β - x) = max (-α) (-β + x) := by
      rw [← max_neg_neg]; congr 1; ring
    linarith

private lemma trap_nonneg (α β x : ℝ) : 0 ≤ trap α β x := le_max_left _ _

private lemma trap_even (α β x : ℝ) : trap α β (-x) = trap α β x := by
  simp [trap]

private lemma trap_zero {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    trap α β 0 = 2 * min α β := by
  dsimp [trap]
  simp only [abs_zero, sub_zero]
  have h1 : max (-α) (-β) = -min α β := max_neg_neg α β
  rw [h1]
  have hnn : 0 ≤ 2 * min α β := by linarith [le_min hα hβ]
  rw [sub_neg_eq_add, ← two_mul, max_eq_right hnn]

private lemma trap_eq_zero_of_ge {α β x : ℝ} (hx : α + β ≤ |x|) : trap α β x = 0 := by
  dsimp [trap]
  apply max_eq_left
  have h1 : min α (β - |x|) ≤ β - |x| := min_le_right _ _
  have h2 : -α ≤ max (-α) (-β - |x|) := le_max_left _ _
  linarith

private lemma trap_antitoneOn {α β : ℝ} : AntitoneOn (trap α β) (Set.Ici 0) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := Set.mem_Ici.mp hx
  have hy0 : 0 ≤ y := Set.mem_Ici.mp hy
  dsimp [trap]
  rw [abs_of_nonneg hx0, abs_of_nonneg hy0]
  refine max_le_max_left 0 ?_
  have hexpl : ∀ z : ℝ, 0 ≤ z →
      min α (β - z) - max (-α) (-β - z) = min (min (2 * α) (2 * β)) (α + β - z) := by
    intro z hz
    rcases le_total α (β - z) with h1' | h1' <;> rcases le_total (-α) (-β - z) with h2' | h2'
    · have hz0 : z = 0 := by linarith
      have hab : α = β := by linarith
      subst hz0; subst hab
      simp only [sub_zero, min_self, max_self]
      have : α + α = 2 * α := by ring
      rw [this, min_self]; ring
    · rw [min_eq_left h1', max_eq_left h2']
      rw [min_eq_left (by linarith : 2 * α ≤ 2 * β), min_eq_left (by linarith : 2 * α ≤ α + β - z)]
      ring
    · rw [min_eq_right h1', max_eq_right h2']
      rw [min_eq_right (by linarith : 2 * β ≤ 2 * α), min_eq_left (by linarith : 2 * β ≤ α + β - z)]
      ring
    · rw [min_eq_right h1', max_eq_left h2']
      rw [min_eq_right (le_min (by linarith : α + β - z ≤ 2 * α) (by linarith : α + β - z ≤ 2 * β))]
      ring
  rw [hexpl x hx0, hexpl y hy0]
  exact min_le_min_left _ (by linarith)

private lemma trap_explicit_nonneg {α β x : ℝ} (_hα : 0 ≤ α) (_hβ : 0 ≤ β) (hx : 0 ≤ x) :
    trap α β x = max 0 (min (min (2 * α) (2 * β)) (α + β - x)) := by
  dsimp [trap]
  rw [abs_of_nonneg hx]
  congr 1
  rcases le_total α (β - x) with h1 | h1 <;> rcases le_total (-α) (-β - x) with h2 | h2
  · have hx0 : x = 0 := by linarith
    have hab : α = β := by linarith
    subst hx0; subst hab
    simp only [sub_zero, min_self, max_self]
    have : α + α = 2 * α := by ring
    rw [this, min_self]; ring
  · rw [min_eq_left h1, max_eq_left h2,
      min_eq_left (by linarith : 2 * α ≤ 2 * β), min_eq_left (by linarith : 2 * α ≤ α + β - x)]
    ring
  · rw [min_eq_right h1, max_eq_right h2,
      min_eq_right (by linarith : 2 * β ≤ 2 * α), min_eq_left (by linarith : 2 * β ≤ α + β - x)]
    ring
  · rw [min_eq_right h1, max_eq_left h2,
      min_eq_right (le_min (by linarith : α + β - x ≤ 2 * α) (by linarith : α + β - x ≤ 2 * β))]
    ring

private lemma trap_integral_nonneg {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    ∫ x in Set.Ioc 0 (α + β), trap α β x = 2 * α * β := by
  -- WLOG assume α ≤ β by symmetry
  wlog hle : α ≤ β generalizing α β
  · have hsym : ∀ x, 0 ≤ x → trap α β x = trap β α x := fun x hx => by
      rw [trap_explicit_nonneg hα hβ hx, trap_explicit_nonneg hβ hα hx, min_comm (2 * α), add_comm α β]
    rw [add_comm α β, setIntegral_congr_fun measurableSet_Ioc (fun x hx => hsym x hx.1.le),
      this hβ hα (le_of_lt (not_le.mp hle))]
    ring
  -- For α ≤ β: trap(x) = 2α on (0, β - α], and = α + β - x on (β - α, α + β]
  have hsplit : Set.Ioc 0 (α + β) = Set.Ioc 0 (β - α) ∪ Set.Ioc (β - α) (α + β) :=
    (Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)).symm
  have hdisj : Disjoint (Set.Ioc 0 (β - α)) (Set.Ioc (β - α) (α + β)) :=
    Set.Ioc_disjoint_Ioc_of_le le_rfl
  have h1 : ∀ x ∈ Set.Ioc 0 (β - α), trap α β x = 2 * α := by
    intro x hx
    rw [trap_explicit_nonneg hα hβ hx.1.le, min_eq_left (by linarith : 2 * α ≤ 2 * β),
      min_eq_left (by linarith [hx.2] : 2 * α ≤ α + β - x), max_eq_right (by linarith)]
  have h2 : ∀ x ∈ Set.Ioc (β - α) (α + β), trap α β x = α + β - x := by
    intro x hx
    rw [trap_explicit_nonneg hα hβ (by linarith [hx.1]), min_eq_left (by linarith : 2 * α ≤ 2 * β),
      min_eq_right (by linarith [hx.1] : α + β - x ≤ 2 * α), max_eq_right (by linarith [hx.2])]
  have hint1 : IntegrableOn (trap α β) (Set.Ioc 0 (β - α)) :=
    (integrableOn_const (by simp)).congr_fun (fun x hx => (h1 x hx).symm) measurableSet_Ioc
  have hint2 : IntegrableOn (trap α β) (Set.Ioc (β - α) (α + β)) :=
    (((continuous_const.sub continuous_id).continuousOn).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).congr_fun
      (fun x hx => (h2 x hx).symm) measurableSet_Ioc
  rw [hsplit, setIntegral_union hdisj measurableSet_Ioc hint1 hint2,
    setIntegral_congr_fun measurableSet_Ioc h1,
    setIntegral_congr_fun measurableSet_Ioc h2]
  have hi1 : ∫ _x in Set.Ioc 0 (β - α), (2 * α) = (β - α) * (2 * α) := by
    rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Ioc, sub_zero,
      ENNReal.toReal_ofReal (by linarith)]
  have hi2 : ∫ x in Set.Ioc (β - α) (α + β), (α + β - x) = 2 * α ^ 2 := by
    rw [← intervalIntegral.integral_of_le (by linarith)]
    have hid : IntervalIntegrable (fun x : ℝ => x) volume (β - α) (α + β) :=
      continuous_id.intervalIntegrable _ _
    rw [intervalIntegral.integral_sub intervalIntegrable_const hid,
      intervalIntegral.integral_const, integral_id, smul_eq_mul]
    ring
  rw [hi1, hi2]
  ring

private lemma pair_typeII_bounds_coprime {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (hcop : Nat.Coprime u v) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    let q := volume.real (bohrSet u δ ∩ bohrSet v δ) - 2 * δ / (max u v : ℝ)
    0 ≤ q ∧ 4 * δ ^ 2 - 4 * δ / (max u v : ℝ) ≤ q ∧ q ≤ 4 * δ ^ 2 := by
  classical
  have huR : (0 : ℝ) < (u : ℝ) := Nat.cast_pos.mpr hu
  have hvR : (0 : ℝ) < (v : ℝ) := Nat.cast_pos.mpr hv
  let α := δ / (u : ℝ)
  let β := δ / (v : ℝ)
  have hα : 0 < α := div_pos hδ0 huR
  have hβ : 0 < β := div_pos hδ0 hvR
  -- Lift bohrSet u δ ∩ bohrSet v δ to fundamental domain Ioc (-α) (1 - α)
  have hmeas_uv : MeasurableSet (bohrSet u δ ∩ bohrSet v δ) :=
    (measurableSet_bohrSet u δ).inter (measurableSet_bohrSet v δ)
  let S_pre : Set ℝ := (QuotientAddGroup.mk : ℝ → UnitAddCircle) ⁻¹' (bohrSet u δ ∩ bohrSet v δ)
  have hvol_eq : volume.real (bohrSet u δ ∩ bohrSet v δ) =
      volume.real (S_pre ∩ Set.Ioc (-α) (1 - α)) := by
    rw [measureReal_def, measureReal_def]
    have := AddCircle.add_projection_respects_measure 1 (-α) hmeas_uv
    have heq : -α + 1 = 1 - α := by ring
    rw [heq] at this
    exact congrArg ENNReal.toReal this
  -- On Ioc (-α) (1 - α), S_pre agrees a.e. with ⋃ a : Fin u, ⋃ b ∈ B, (Iu a ∩ Iv b)
  let Iu (a : Fin u) : Set ℝ := Set.Icc ((a.1 : ℝ) / u - α) ((a.1 : ℝ) / u + α)
  let Iv (b : ℤ) : Set ℝ := Set.Icc ((b : ℝ) / v - β) ((b : ℝ) / v + β)
  -- Restrict b to Finset B := Icc (-v : ℤ) (2 * v)
  let B : Finset ℤ := Finset.Icc (-(v : ℤ)) (2 * (v : ℤ))
  have hset_ae :
      ((S_pre ∩ Set.Ioc (-α) (1 - α) : Set ℝ)) =ᵐ[volume]
        (⋃ a : Fin u, ⋃ b ∈ B, (Iu a ∩ Iv b) : Set ℝ) := by
    -- Differ at most at the two points {-α, 1 - α}
    have hpt_iff : ∀ x : ℝ, x ≠ -α → x ≠ 1 - α →
        (x ∈ S_pre ∩ Set.Ioc (-α) (1 - α) ↔
          x ∈ ⋃ a : Fin u, ⋃ b ∈ B, (Iu a ∩ Iv b)) := by
      intro x hx_ne1 hx_ne2
      constructor
      · rintro ⟨⟨hxu, hxv⟩, hxIoc⟩
        have hxu' : (x : UnitAddCircle) ∈ bohrSet u δ := hxu
        have hxv' : (x : UnitAddCircle) ∈ bohrSet v δ := hxv
        rw [mem_bohrSet_coe_iff hu] at hxu'
        rw [mem_bohrSet_coe_iff hv] at hxv'
        obtain ⟨m, hxm⟩ := hxu'
        obtain ⟨b, hxb⟩ := hxv'
        have hm0 : 0 ≤ m := by
          have : -(1 : ℝ) < (m : ℝ) := by
            have h1 : (m : ℝ) / (u : ℝ) + δ / (u : ℝ) > -δ / (u : ℝ) := by
              have hlo := hxIoc.1
              dsimp [α] at hlo
              rw [neg_div]
              linarith [hxm.2]
            have := mul_lt_mul_of_pos_left h1 huR
            have e1 : (u : ℝ) * ((m : ℝ) / (u : ℝ) + δ / (u : ℝ)) = (m : ℝ) + δ := by field_simp
            have e2 : (u : ℝ) * (-δ / (u : ℝ)) = -δ := by field_simp
            linarith
          have : (-1 : ℤ) < m := by exact_mod_cast this
          omega
        have hmu : m < (u : ℤ) := by
          have hxlt : x < 1 - α := lt_of_le_of_ne hxIoc.2 hx_ne2
          have : (m : ℝ) < (u : ℝ) := by
            have h1 : (m : ℝ) / (u : ℝ) - δ / (u : ℝ) < 1 - δ / (u : ℝ) := by
              dsimp [α] at hxlt; linarith [hxm.1]
            have := mul_lt_mul_of_pos_left h1 huR
            have e1 : (u : ℝ) * ((m : ℝ) / (u : ℝ) - δ / (u : ℝ)) = (m : ℝ) - δ := by field_simp
            have e2 : (u : ℝ) * (1 - δ / (u : ℝ)) = (u : ℝ) - δ := by field_simp
            linarith
          exact_mod_cast this
        refine Set.mem_iUnion.mpr ⟨⟨m.toNat, by omega⟩, Set.mem_biUnion ?_ ⟨?_, hxb⟩⟩
        · have hbl : -(v : ℝ) ≤ (b : ℝ) := by
            have h1 : -(1 : ℝ) < (b : ℝ) / (v : ℝ) := by
              have hα1 : α < 1 / 2 := by
                have : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
                have : δ / (u : ℝ) ≤ δ := div_le_self hδ0.le this
                linarith
              have hβ1 : β < 1 / 2 := by
                have : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv
                have : δ / (v : ℝ) ≤ δ := div_le_self hδ0.le this
                linarith
              linarith [hxIoc.1, hxb.2]
            have := mul_lt_mul_of_pos_left h1 hvR
            have e1 : (v : ℝ) * ((b : ℝ) / (v : ℝ)) = (b : ℝ) := by field_simp
            linarith
          have hbu : (b : ℝ) ≤ 2 * (v : ℝ) := by
            have h1 : (b : ℝ) / (v : ℝ) ≤ 2 := by
              have hβ1 : β < 1 / 2 := by
                have : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv
                have : δ / (v : ℝ) ≤ δ := div_le_self hδ0.le this
                linarith
              linarith [hxIoc.2, hxb.1, hα]
            have := mul_le_mul_of_nonneg_left h1 hvR.le
            have e1 : (v : ℝ) * ((b : ℝ) / (v : ℝ)) = (b : ℝ) := by field_simp
            linarith
          exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hbl, by exact_mod_cast hbu⟩
        · have : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hm0
          simpa [Iu, α, this] using hxm
      · rintro hmem
        obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hmem
        obtain ⟨b, _, hxa, hxb⟩ := Set.mem_iUnion₂.mp ha
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · change (x : UnitAddCircle) ∈ bohrSet u δ
          rw [mem_bohrSet_coe_iff hu]
          exact ⟨(a.1 : ℤ), by simpa [Iu, α] using hxa⟩
        · change (x : UnitAddCircle) ∈ bohrSet v δ
          rw [mem_bohrSet_coe_iff hv]
          exact ⟨b, by simpa [Iv, β] using hxb⟩
        · have ha0 : (0 : ℝ) ≤ (a.1 : ℝ) / (u : ℝ) := by positivity
          have hau : (a.1 : ℝ) / (u : ℝ) + α ≤ 1 - α := by
            have ha_le : (a.1 : ℝ) + 1 ≤ (u : ℝ) := by exact_mod_cast a.2
            have h2δ : 2 * δ < 1 := by linarith
            have : ((a.1 : ℝ) + 2 * δ) / (u : ℝ) ≤ 1 := by
              rw [div_le_one huR]; linarith
            dsimp [α]
            linarith [add_div (a.1 : ℝ) (2 * δ) (u : ℝ), mul_div_assoc (2 : ℝ) δ (u : ℝ)]
          have hlo : -α < x := lt_of_le_of_ne (by linarith [hxa.1, ha0]) hx_ne1.symm
          exact ⟨hlo, by linarith [hxa.2, hau]⟩
    rw [MeasureTheory.ae_eq_set]
    have hfin2 : volume ({-α, 1 - α} : Set ℝ) = 0 := (Set.toFinite _).measure_zero volume
    constructor
    · refine measure_mono_null (t := ({-α, 1 - α} : Set ℝ)) ?_ hfin2
      intro x ⟨hx1, hx2⟩
      by_contra hnot
      exact hx2 ((hpt_iff x (fun h => hnot (Or.inl h)) (fun h => hnot (Or.inr h))).mp hx1)
    · refine measure_mono_null (t := ({-α, 1 - α} : Set ℝ)) ?_ hfin2
      intro x ⟨hx1, hx2⟩
      by_contra hnot
      exact hx2 ((hpt_iff x (fun h => hnot (Or.inl h)) (fun h => hnot (Or.inr h))).mpr hx1)
  -- Disjointness of (Iu a ∩ Iv b) over (a, b) ∈ Fin u × B
  have hdisj_ab : ((Finset.univ ×ˢ B : Finset (Fin u × ℤ)) : Set (Fin u × ℤ)).PairwiseDisjoint
      (fun p => Iu p.1 ∩ Iv p.2) := by
    intro p₁ _ p₂ _ hp
    by_cases ha : p₁.1 ≠ p₂.1
    · have hne : (p₁.1.1 : ℤ) ≠ (p₂.1.1 : ℤ) := by
        intro h; exact ha (Fin.ext (by omega))
      exact (bohrSet_intervals_disjoint hu hδ1 hne).mono Set.inter_subset_left Set.inter_subset_left
    · push Not at ha
      have hb : p₁.2 ≠ p₂.2 := fun h => hp (Prod.ext ha h)
      exact (bohrSet_intervals_disjoint hv hδ1 hb).mono Set.inter_subset_right Set.inter_subset_right
  -- Measure of each Iu a ∩ Iv b = trap α β (a/u - b/v)
  have hmeas_ab : ∀ (a : Fin u) (b : ℤ),
      volume.real (Iu a ∩ Iv b) = trap α β ((a.1 : ℝ) / u - (b : ℝ) / v) := by
    intro a b
    let x0 : ℝ := (a.1 : ℝ) / u - (b : ℝ) / v
    have hdiff_eq :
        min ((a.1 : ℝ) / u + α) ((b : ℝ) / v + β) - max ((a.1 : ℝ) / u - α) ((b : ℝ) / v - β) =
          min α (β - x0) - max (-α) (-β - x0) := by
      have h1 : min ((a.1 : ℝ) / u + α) ((b : ℝ) / v + β) = (a.1 : ℝ) / u + min α (β - x0) := by
        rw [add_min]; congr 1; dsimp [x0]; ring
      have h2 : max ((a.1 : ℝ) / u - α) ((b : ℝ) / v - β) = (a.1 : ℝ) / u + max (-α) (-β - x0) := by
        rw [add_max]; congr 1 <;> (dsimp [x0]; ring)
      rw [h1, h2]; ring
    rw [← trap_eq_measureReal hα.le hβ.le x0]
    dsimp [Iu, Iv]
    rw [Set.Icc_inter_Icc, Set.Icc_inter_Icc, measureReal_def, measureReal_def,
      Real.volume_Icc, Real.volume_Icc, hdiff_eq]
  -- Bijection (a, b) ↦ v*a - u*b onto Icc (-M) M (with M = u * v)
  let M : ℕ := u * v
  have hvol_sum :
      volume.real (bohrSet u δ ∩ bohrSet v δ) =
        ∑ j ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), trap α β ((j : ℝ) / ((u : ℝ) * (v : ℝ))) := by
    have hunion_eq : (⋃ a : Fin u, ⋃ b ∈ B, (Iu a ∩ Iv b)) =
        ⋃ p ∈ (Finset.univ ×ˢ B : Finset (Fin u × ℤ)), (Iu p.1 ∩ Iv p.2) := by
      ext x
      simp only [Set.mem_iUnion, Finset.mem_product, Finset.mem_univ, true_and, Prod.exists, exists_prop]
    rw [hvol_eq, measureReal_congr hset_ae, hunion_eq,
      measureReal_biUnion_finset hdisj_ab (fun _ _ => measurableSet_Icc.inter measurableSet_Icc)
        (fun _ _ => ne_top_of_le_ne_top (by simp [Iu]) (measure_mono Set.inter_subset_left))]
    simp_rw [hmeas_ab]
    -- Map p ↦ v * p.1 - u * p.2 is injective on Fin u × B, and covers every j with trap(j/uv) ≠ 0
    let φ : Fin u × ℤ → ℤ := fun p => (v : ℤ) * (p.1.1 : ℤ) - (u : ℤ) * p.2
    have hφ_val : ∀ p : Fin u × ℤ,
        (p.1.1 : ℝ) / (u : ℝ) - (p.2 : ℝ) / (v : ℝ) = (φ p : ℝ) / ((u : ℝ) * (v : ℝ)) := by
      intro p
      dsimp [φ]; push_cast; field_simp
    simp_rw [hφ_val]
    have hφ_inj : Set.InjOn φ ((Finset.univ ×ˢ B : Finset (Fin u × ℤ)) : Set (Fin u × ℤ)) := by
      intro p₁ _ p₂ _ heq
      dsimp [φ] at heq
      have hdvd : (u : ℤ) ∣ (v : ℤ) * ((p₁.1.1 : ℤ) - (p₂.1.1 : ℤ)) :=
        ⟨p₁.2 - p₂.2, by linarith⟩
      have hcopZ : IsCoprime (u : ℤ) (v : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
      have hdvd' : (u : ℤ) ∣ (p₁.1.1 : ℤ) - (p₂.1.1 : ℤ) := hcopZ.dvd_of_dvd_mul_left hdvd
      obtain ⟨t, ht⟩ := hdvd'
      have ha1 : (p₁.1.1 : ℤ) < (u : ℤ) := Int.ofNat_lt.mpr p₁.1.2
      have ha2 : (p₂.1.1 : ℤ) < (u : ℤ) := Int.ofNat_lt.mpr p₂.1.2
      have ht0 : t = 0 := by nlinarith
      rw [ht0, mul_zero] at ht
      have haeq : p₁.1 = p₂.1 := Fin.ext (by omega)
      have huZ : (0 : ℤ) < (u : ℤ) := Int.natCast_pos.mpr hu
      rw [haeq] at heq
      have hbeq : p₁.2 = p₂.2 := by nlinarith
      exact Prod.ext haeq hbeq
    rw [← Finset.sum_image (f := fun j : ℤ => trap α β ((j : ℝ) / ((u : ℝ) * (v : ℝ)))) hφ_inj]
    symm
    refine Finset.sum_subset ?_ ?_
    · intro j hj
      simp only [Finset.mem_Icc] at hj
      obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.mpr hcop
      -- x * u + y * v = 1
      have huZ : (0 : ℤ) < (u : ℤ) := Int.natCast_pos.mpr hu
      let r : ℤ := (j * y) % (u : ℤ)
      have hr0 : 0 ≤ r := Int.emod_nonneg (j * y) huZ.ne'
      have hru : r < (u : ℤ) := Int.emod_lt_of_pos (j * y) huZ
      let a : Fin u := ⟨r.toNat, by omega⟩
      have haZ : (a.1 : ℤ) = r := Int.toNat_of_nonneg hr0
      have hdiv : (u : ℤ) ∣ (v : ℤ) * (a.1 : ℤ) - j := by
        have hmod : (u : ℤ) ∣ r - j * y := by
          have := Int.emod_add_mul_ediv (j * y) (u : ℤ)
          exact ⟨-(j * y / (u : ℤ)), by dsimp [r]; linarith⟩
        obtain ⟨k, hk⟩ := hmod
        refine ⟨(v : ℤ) * k - j * x, ?_⟩
        rw [haZ]
        nlinarith
      obtain ⟨b, hb⟩ := hdiv
      have hφ_eq : φ (a, b) = j := by
        dsimp [φ]; linarith
      have hbB : b ∈ B := by
        simp only [B, Finset.mem_Icc]
        have ha_hi : (a.1 : ℤ) < (u : ℤ) := Int.ofNat_lt.mpr a.2
        have hM_eq : (M : ℤ) = (u : ℤ) * (v : ℤ) := Nat.cast_mul u v
        have hlo : -((u : ℤ) * (v : ℤ)) ≤ (u : ℤ) * b := by nlinarith
        have hhi : (u : ℤ) * b ≤ (u : ℤ) * (2 * (v : ℤ)) := by nlinarith
        exact ⟨by nlinarith, by nlinarith⟩
      exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨Finset.mem_univ a, hbB⟩, hφ_eq⟩
    · intro j _ hjnot
      simp only [Finset.mem_Icc, not_and_or, not_le] at hjnot
      apply trap_eq_zero_of_ge
      have hαβ : α + β < 1 := by
        have hu1 : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
        have hv1 : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv
        have h1 : δ / (u : ℝ) ≤ δ := div_le_self hδ0.le hu1
        have h2 : δ / (v : ℝ) ≤ δ := div_le_self hδ0.le hv1
        linarith
      have hM_eq : (M : ℤ) = (u : ℤ) * (v : ℤ) := Nat.cast_mul u v
      have habs : ((u : ℝ) * (v : ℝ)) ≤ |(j : ℝ)| := by
        rcases hjnot with hlt | hgt
        · have : (j : ℝ) < -((u : ℝ) * (v : ℝ)) := by exact_mod_cast (hM_eq ▸ hlt)
          rw [abs_of_neg (by nlinarith)]; linarith
        · have : (u : ℝ) * (v : ℝ) < (j : ℝ) := by exact_mod_cast (hM_eq ▸ hgt)
          rw [abs_of_pos (by nlinarith)]; linarith
      have hge1 : (1 : ℝ) ≤ |(j : ℝ) / ((u : ℝ) * (v : ℝ))| := by
        rw [abs_div, abs_of_pos (mul_pos huR hvR), one_le_div (mul_pos huR hvR)]
        exact habs
      linarith
  -- Split j = 0 and j ≠ 0
  have htrap0 : trap α β 0 = 2 * δ / (max (u : ℝ) (v : ℝ)) := by
    rw [trap_zero hα.le hβ.le]
    dsimp [α, β]
    rcases le_total u v with huv | huv
    · rw [max_eq_right (Nat.cast_le.mpr huv),
        min_eq_right (div_le_div_of_nonneg_left hδ0.le huR (Nat.cast_le.mpr huv))]
      ring
    · rw [max_eq_left (Nat.cast_le.mpr huv),
        min_eq_left (div_le_div_of_nonneg_left hδ0.le hvR (Nat.cast_le.mpr huv))]
      ring
  have hsum_split :
      volume.real (bohrSet u δ ∩ bohrSet v δ) =
        2 * δ / (max u v : ℝ) + 2 * ∑ j ∈ Finset.Icc 1 M, trap α β ((j : ℝ) / ((u : ℝ) * (v : ℝ))) := by
    rw [hvol_sum]
    have hsplit : Finset.Icc (-(M : ℤ)) (M : ℤ) =
        insert 0 ((Finset.Icc 1 M).image (fun j : ℕ => (j : ℤ)) ∪
          (Finset.Icc 1 M).image (fun j : ℕ => -(j : ℤ))) := by
      ext z
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
      constructor
      · intro ⟨hlo, hhi⟩
        rcases lt_trichotomy z 0 with hz | rfl | hz
        · exact Or.inr (Or.inr ⟨(-z).toNat, ⟨by omega, by omega⟩, by omega⟩)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨z.toNat, ⟨by omega, by omega⟩, by omega⟩)
      · rintro (rfl | ⟨j, ⟨h1, h2⟩, rfl⟩ | ⟨j, ⟨h1, h2⟩, rfl⟩) <;> omega
    have h0not : (0 : ℤ) ∉ (Finset.Icc 1 M).image (fun j : ℕ => (j : ℤ)) ∪
        (Finset.Icc 1 M).image (fun j : ℕ => -(j : ℤ)) := by
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Icc, not_or, not_exists, not_and]
      exact ⟨fun j h1 _ => by omega, fun j h1 _ => by omega⟩
    have hdisj_pm : Disjoint ((Finset.Icc 1 M).image (fun j : ℕ => (j : ℤ)))
        ((Finset.Icc 1 M).image (fun j : ℕ => -(j : ℤ))) := by
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      simp only [Finset.mem_image, Finset.mem_Icc] at hz1 hz2
      obtain ⟨j₁, ⟨h1, _⟩, rfl⟩ := hz1
      obtain ⟨j₂, ⟨h2, _⟩, heq⟩ := hz2
      omega
    rw [hsplit, Finset.sum_insert h0not, Finset.sum_union hdisj_pm,
      Finset.sum_image (fun _ _ _ _ h => by omega),
      Finset.sum_image (fun _ _ _ _ h => by omega)]
    simp only [Int.cast_zero, zero_div, htrap0, Int.cast_neg, Int.cast_natCast, neg_div, trap_even]
    ring
  -- Now compare h * ∑_{j=1}^M trap(j*h) with ∫_0^{α+β} trap(x) dx = 2 α β = 2 δ² / (u v)
  let h : ℝ := 1 / ((u : ℝ) * (v : ℝ))
  have hh : 0 < h := by positivity
  have hMh : α + β ≤ (M : ℝ) * h := by
    have hαβ : α + β < 1 := by
      have hu1 : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
      have hv1 : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv
      have h1 : δ / (u : ℝ) ≤ δ := div_le_self hδ0.le hu1
      have h2 : δ / (v : ℝ) ≤ δ := div_le_self hδ0.le hv1
      linarith
    have hMh1 : (M : ℝ) * h = 1 := by
      dsimp [M, h]; push_cast; field_simp
    linarith
  have hint_Mh : ∫ x in Set.Ioc 0 ((M : ℝ) * h), trap α β x = 2 * α * β := by
    have hsplit : Set.Ioc 0 ((M : ℝ) * h) = Set.Ioc 0 (α + β) ∪ Set.Ioc (α + β) ((M : ℝ) * h) :=
      (Set.Ioc_union_Ioc_eq_Ioc (by linarith) hMh).symm
    have hzero : ∀ x ∈ Set.Ioc (α + β) ((M : ℝ) * h), trap α β x = 0 := fun x hx =>
      trap_eq_zero_of_ge (by rw [abs_of_nonneg (by linarith [hx.1])]; exact le_of_lt hx.1)
    have hint1 : IntegrableOn (trap α β) (Set.Ioc 0 (α + β)) := by
      have hcont : Continuous (trap α β) := by
        unfold trap; fun_prop
      exact hcont.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    have hint2 : IntegrableOn (trap α β) (Set.Ioc (α + β) ((M : ℝ) * h)) :=
      (integrableOn_zero).congr_fun (fun x hx => (hzero x hx).symm) measurableSet_Ioc
    rw [hsplit, setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hint1 hint2,
      trap_integral_nonneg hα.le hβ.le, setIntegral_congr_fun measurableSet_Ioc hzero,
      integral_zero, add_zero]
  -- Split ∫_0^{M*h} into ∑_{j=1}^M ∫_{(j-1)h}^{jh}
  have hriem : ∀ m : ℕ,
      h * ∑ j ∈ Finset.Icc 1 m, trap α β ((j : ℝ) * h) ≤ ∫ x in Set.Ioc 0 ((m : ℝ) * h), trap α β x ∧
      ∫ x in Set.Ioc 0 ((m : ℝ) * h), trap α β x ≤
        h * ∑ j ∈ Finset.Icc 1 m, trap α β (((j - 1 : ℕ) : ℝ) * h) := by
    intro m
    induction m with
    | zero => simp
    | succ m' ihm =>
      have hsplit : Set.Ioc 0 (((m' + 1 : ℕ) : ℝ) * h) =
          Set.Ioc 0 ((m' : ℝ) * h) ∪ Set.Ioc ((m' : ℝ) * h) (((m' + 1 : ℕ) : ℝ) * h) := by
        refine (Set.Ioc_union_Ioc_eq_Ioc (by positivity) ?_).symm
        push_cast; nlinarith
      have hcont : Continuous (trap α β) := by unfold trap; fun_prop
      have hi1 : IntegrableOn (trap α β) (Set.Ioc 0 ((m' : ℝ) * h)) :=
        hcont.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
      have hi2 : IntegrableOn (trap α β) (Set.Ioc ((m' : ℝ) * h) (((m' + 1 : ℕ) : ℝ) * h)) :=
        hcont.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
      rw [hsplit, setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hi1 hi2]
      have hIcc : Finset.Icc 1 (m' + 1) = insert (m' + 1) (Finset.Icc 1 m') := by
        ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : m' + 1 ∉ Finset.Icc 1 m' := by simp
      have hlen : (((m' + 1 : ℕ) : ℝ) * h) - ((m' : ℝ) * h) = h := by push_cast; ring
      have hstep_lo : h * trap α β (((m' + 1 : ℕ) : ℝ) * h) ≤
          ∫ x in Set.Ioc ((m' : ℝ) * h) (((m' + 1 : ℕ) : ℝ) * h), trap α β x := by
        calc
          h * trap α β (((m' + 1 : ℕ) : ℝ) * h)
              = ∫ _x in Set.Ioc ((m' : ℝ) * h) (((m' + 1 : ℕ) : ℝ) * h),
                  trap α β (((m' + 1 : ℕ) : ℝ) * h) := by
                rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Ioc, hlen,
                  ENNReal.toReal_ofReal hh.le]
          _ ≤ ∫ x in Set.Ioc ((m' : ℝ) * h) (((m' + 1 : ℕ) : ℝ) * h), trap α β x := by
                refine setIntegral_mono_on (integrableOn_const (by simp)) hi2 measurableSet_Ioc fun x hx => ?_
                have hx0 : 0 ≤ x := le_trans (mul_nonneg (Nat.cast_nonneg m') hh.le) hx.1.le
                exact trap_antitoneOn (Set.mem_Ici.mpr hx0) (Set.mem_Ici.mpr (by positivity)) hx.2
      have hstep_hi :
          ∫ x in Set.Ioc ((m' : ℝ) * h) (((m' + 1 : ℕ) : ℝ) * h), trap α β x ≤
            h * trap α β ((m' : ℝ) * h) := by
        calc
          ∫ x in Set.Ioc ((m' : ℝ) * h) (((m' + 1 : ℕ) : ℝ) * h), trap α β x
              ≤ ∫ _x in Set.Ioc ((m' : ℝ) * h) (((m' + 1 : ℕ) : ℝ) * h), trap α β ((m' : ℝ) * h) := by
                refine setIntegral_mono_on hi2 (integrableOn_const (by simp)) measurableSet_Ioc fun x hx => ?_
                have hx0 : 0 ≤ x := le_trans (mul_nonneg (Nat.cast_nonneg m') hh.le) hx.1.le
                exact trap_antitoneOn (Set.mem_Ici.mpr (by positivity)) (Set.mem_Ici.mpr hx0) hx.1.le
          _ = h * trap α β ((m' : ℝ) * h) := by
                rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Ioc, hlen,
                  ENNReal.toReal_ofReal hh.le]
      rw [hIcc, Finset.sum_insert hnot, Finset.sum_insert hnot]
      simp only [Nat.add_sub_cancel]
      exact ⟨by linarith [ihm.1], by linarith [ihm.2]⟩
  have ⟨hlo_r, hhi_r⟩ := hriem M
  rw [hint_Mh] at hlo_r hhi_r
  -- Note ∑_{j=1}^M trap((j-1)*h) = trap(0) + ∑_{j=1}^{M-1} trap(j*h) ≤ trap(0) + ∑_{j=1}^M trap(j*h)
  have hshift_sum :
      ∑ j ∈ Finset.Icc 1 M, trap α β (((j - 1 : ℕ) : ℝ) * h) ≤
        trap α β 0 + ∑ j ∈ Finset.Icc 1 M, trap α β ((j : ℝ) * h) := by
    have hMpos : 1 ≤ M := Nat.mul_pos hu hv
    have hrew : ∑ j ∈ Finset.Icc 1 M, trap α β (((j - 1 : ℕ) : ℝ) * h) =
        ∑ j ∈ Finset.range M, trap α β ((j : ℝ) * h) := by
      refine Finset.sum_bij (fun j _ => j - 1) ?_ ?_ ?_ ?_
      · intro j hj; simp only [Finset.mem_Icc] at hj; simp only [Finset.mem_range]; omega
      · intro j₁ h1 j₂ h2 heq; simp only [Finset.mem_Icc] at h1 h2; omega
      · intro r hr; simp only [Finset.mem_range] at hr
        exact ⟨r + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro j _; rfl
    rw [hrew]
    have hsub : Finset.range M ⊆ insert 0 (Finset.Icc 1 M) := by
      intro r hr; simp only [Finset.mem_range] at hr
      simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    calc
      ∑ j ∈ Finset.range M, trap α β ((j : ℝ) * h)
          ≤ ∑ j ∈ insert 0 (Finset.Icc 1 M), trap α β ((j : ℝ) * h) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => trap_nonneg _ _ _
      _ = trap α β 0 + ∑ j ∈ Finset.Icc 1 M, trap α β ((j : ℝ) * h) := by
            rw [Finset.sum_insert (by simp)]; simp
  have hsum_eq_q :
      volume.real (bohrSet u δ ∩ bohrSet v δ) - 2 * δ / (max u v : ℝ) =
        2 * ∑ j ∈ Finset.Icc 1 M, trap α β ((j : ℝ) * h) := by
    rw [hsum_split]
    have heq : ∀ j : ℕ, (j : ℝ) / ((u : ℝ) * (v : ℝ)) = (j : ℝ) * h := fun j => by
      dsimp [h]; ring
    simp_rw [heq]
    ring
  have h2αβ : 2 * ((2 * α * β) / h) = 4 * δ ^ 2 := by
    dsimp [α, β, h]; field_simp; ring
  dsimp only
  rw [hsum_eq_q]
  refine ⟨?_, ?_, ?_⟩
  · exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => trap_nonneg _ _ _)
  · have h1 : 2 * α * β ≤ h * (trap α β 0 + ∑ j ∈ Finset.Icc 1 M, trap α β ((j : ℝ) * h)) :=
      hhi_r.trans (mul_le_mul_of_nonneg_left hshift_sum hh.le)
    have h2 : (2 * α * β) / h ≤ trap α β 0 + ∑ j ∈ Finset.Icc 1 M, trap α β ((j : ℝ) * h) :=
      (div_le_iff₀' hh).mpr h1
    rw [htrap0] at h2
    have h4 : 4 * δ / max (u : ℝ) (v : ℝ) = 2 * (2 * δ / max (u : ℝ) (v : ℝ)) := by ring
    linarith [h2αβ, h4]
  · have h2 : ∑ j ∈ Finset.Icc 1 M, trap α β ((j : ℝ) * h) ≤ (2 * α * β) / h :=
      (le_div_iff₀' hh).mpr hlo_r
    linarith [h2αβ]

private lemma pair_typeII_bounds {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) :
    let q := volume.real (bohrSet u δ ∩ bohrSet v δ) -
      2 * δ * (Nat.gcd u v : ℝ) / (max (u : ℝ) (v : ℝ))
    0 ≤ q ∧ 4 * δ ^ 2 - 4 * δ * (Nat.gcd u v : ℝ) / (max (u : ℝ) (v : ℝ)) ≤ q ∧ q ≤ 4 * δ ^ 2 := by
  let d := Nat.gcd u v
  have hd : 0 < d := Nat.gcd_pos_of_pos_left v hu
  let u' := u / d
  let v' := v / d
  have hu_eq : u = d * u' := (Nat.mul_div_cancel' (Nat.gcd_dvd_left u v)).symm
  have hv_eq : v = d * v' := (Nat.mul_div_cancel' (Nat.gcd_dvd_right u v)).symm
  have hu' : 0 < u' := Nat.div_pos (Nat.le_of_dvd hu (Nat.gcd_dvd_left u v)) hd
  have hv' : 0 < v' := Nat.div_pos (Nat.le_of_dvd hv (Nat.gcd_dvd_right u v)) hd
  have hcop : Nat.Coprime u' v' := Nat.coprime_div_gcd_div_gcd hd
  have hmp : MeasurePreserving (fun t : UnitAddCircle => (d : ℤ) • t) volume volume :=
    measurePreserving_zsmul volume (by exact_mod_cast hd.ne')
  have hpre : bohrSet u δ ∩ bohrSet v δ =
      (fun t : UnitAddCircle => (d : ℤ) • t) ⁻¹' (bohrSet u' δ ∩ bohrSet v' δ) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_preimage, bohrSet]
    have h1 : (u : ℤ) • t = (u' : ℤ) • ((d : ℤ) • t) := by
      rw [hu_eq, Nat.cast_mul, mul_comm, mul_zsmul]
    have h2 : (v : ℤ) • t = (v' : ℤ) • ((d : ℤ) • t) := by
      rw [hv_eq, Nat.cast_mul, mul_comm, mul_zsmul]
    rw [h1, h2]
  have hvol : volume.real (bohrSet u δ ∩ bohrSet v δ) =
      volume.real (bohrSet u' δ ∩ bohrSet v' δ) := by
    rw [hpre, measureReal_def, measureReal_def,
      hmp.measure_preimage ((measurableSet_bohrSet u' δ).inter (measurableSet_bohrSet v' δ)).nullMeasurableSet]
  have hratio : (Nat.gcd u v : ℝ) / (max (u : ℝ) (v : ℝ)) = 1 / (max (u' : ℝ) (v' : ℝ)) := by
    have hmax : max (u : ℝ) (v : ℝ) = (d : ℝ) * max (u' : ℝ) (v' : ℝ) := by
      have h1 : (u : ℝ) = (d : ℝ) * (u' : ℝ) := by exact_mod_cast hu_eq
      have h2 : (v : ℝ) = (d : ℝ) * (v' : ℝ) := by exact_mod_cast hv_eq
      rw [h1, h2, ← mul_max_of_nonneg _ _ (Nat.cast_nonneg d)]
    rw [hmax]
    have hdne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
    dsimp [d]
    field_simp
  have hcop_b := pair_typeII_bounds_coprime hu' hv' hcop hδ0 hδ1
  dsimp only at hcop_b ⊢
  rw [hvol]
  have e1 : 2 * δ * (Nat.gcd u v : ℝ) / (max (u : ℝ) (v : ℝ)) = 2 * δ / (max (u' : ℝ) (v' : ℝ)) := by
    rw [mul_div_assoc, hratio]; ring
  have e2 : 4 * δ * (Nat.gcd u v : ℝ) / (max (u : ℝ) (v : ℝ)) = 4 * δ / (max (u' : ℝ) (v' : ℝ)) := by
    rw [mul_div_assoc, hratio]; ring
  rw [e1, e2]
  exact hcop_b

/- ### Part 6: Proposition 4.4 and Section 8 assembly -/

private lemma overlap_ge_excess {n : ℕ} (A : Fin n → Set UnitAddCircle)
    (hA : ∀ i, MeasurableSet (A i)) :
    ∫ t : UnitAddCircle, (((Finset.univ.filter fun i : Fin n => t ∈ A i).card - 1 : ℕ) : ℝ) ≤
      ∑ i : Fin n, volume.real (A i ∩ ⋃ j, ⋃ (_ : j ≠ i), A j) := by
  classical
  let N (t : UnitAddCircle) : ℕ := (Finset.univ.filter fun i : Fin n => t ∈ A i).card
  let B (i : Fin n) : Set UnitAddCircle := A i ∩ ⋃ j, ⋃ (_ : j ≠ i), A j
  have hB : ∀ i, MeasurableSet (B i) := fun i =>
    (hA i).inter (MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => hA j)
  have hRHS : ∑ i : Fin n, volume.real (B i) =
      ∫ t : UnitAddCircle, ∑ i : Fin n, (B i).indicator (fun _ => (1 : ℝ)) t := by
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_indicator (hB i), setIntegral_const, smul_eq_mul, mul_one]
    · intro i _
      exact (integrableOn_const (measure_ne_top _ _)).integrable_indicator (hB i)
  rw [hRHS]
  refine integral_mono ?_ (integrable_finsetSum _ fun i _ =>
    (integrableOn_const (measure_ne_top _ _)).integrable_indicator (hB i)) fun t => ?_
  · refine Integrable.of_bound ?_ (n : ℝ) (Filter.Eventually.of_forall fun t => ?_)
    · have hmeasN : Measurable N := by
        have heq : N = fun t => ∑ i : Fin n, (A i).indicator (fun _ => 1) t := by
          ext t; simp only [N, Finset.card_filter, Set.indicator]
        rw [heq]
        exact Finset.measurable_sum _ fun i _ => measurable_const.indicator (hA i)
      exact (Measurable.comp measurable_from_top (hmeasN.sub measurable_const)).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast (Nat.sub_le _ _).trans ((Finset.card_filter_le _ _).trans_eq (Fintype.card_fin n))
  · -- Pointwise: (N t - 1)_+ ≤ ∑ i, 1_{B i}(t)
    have hsum_eq : ∑ i : Fin n, (B i).indicator (fun _ => (1 : ℝ)) t =
        if 2 ≤ N t then (N t : ℝ) else 0 := by
      split_ifs with h2
      · have hfilt : ∀ i : Fin n, t ∈ B i ↔ t ∈ A i := by
          intro i
          refine ⟨fun h => h.1, fun hi => ⟨hi, ?_⟩⟩
          have hcard : 1 < (Finset.univ.filter fun j : Fin n => t ∈ A j).card := h2
          obtain ⟨j, hj, hji⟩ := Finset.exists_mem_ne hcard i
          exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hji, (Finset.mem_filter.mp hj).2⟩⟩
        simp only [N, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
          Set.indicator]
        exact Finset.sum_congr rfl fun i _ => by rw [if_congr (hfilt i) rfl rfl]
      · refine Finset.sum_eq_zero fun i _ => ?_
        have hnot : t ∉ B i := by
          rintro ⟨hi, hj⟩
          obtain ⟨j, hj'⟩ := Set.mem_iUnion.mp hj
          obtain ⟨hji, htj⟩ := Set.mem_iUnion.mp hj'
          have hsub : ({i, j} : Finset (Fin n)) ⊆ Finset.univ.filter (fun k => t ∈ A k) := by
            intro k hk
            rcases Finset.mem_insert.mp hk with rfl | hk'
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
            · rw [Finset.mem_singleton.mp hk']
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, htj⟩
          have hcard := Finset.card_le_card hsub
          rw [Finset.card_pair hji.symm] at hcard
          exact h2 hcard
        simp [Set.indicator, hnot]
    rw [hsum_eq]
    split_ifs with h2
    · change ((N t - 1 : ℕ) : ℝ) ≤ (N t : ℝ)
      exact_mod_cast Nat.sub_le (N t) 1
    · have : N t - 1 = 0 := by omega
      change ((N t - 1 : ℕ) : ℝ) ≤ 0
      rw [this]; norm_num

private lemma excess_one_eq {n : ℕ} (v : Fin n → ℕ) (hv : ∀ i, 0 < v i)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : 2 * δ ≤ 1) :
    ∫ t : UnitAddCircle, (((Finset.univ.filter fun i : Fin n => t ∈ bohrSet (v i) δ).card - 1 : ℕ) : ℝ) =
      2 * (n : ℝ) * δ - volume.real (⋃ i : Fin n, bohrSet (v i) δ) := by
  classical
  let N (t : UnitAddCircle) : ℕ := (Finset.univ.filter fun i : Fin n => t ∈ bohrSet (v i) δ).card
  let U : Set UnitAddCircle := ⋃ i : Fin n, bohrSet (v i) δ
  have hU : MeasurableSet U := MeasurableSet.iUnion fun i => measurableSet_bohrSet _ _
  have hN_int : Integrable (fun t => (N t : ℝ)) := by
    have heq : (fun t => (N t : ℝ)) = fun t => ∑ i : Fin n, (bohrSet (v i) δ).indicator (fun _ => (1 : ℝ)) t := by
      ext t; simp only [N, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Set.indicator]
    rw [heq]
    exact integrable_finsetSum _ fun i _ =>
      (integrableOn_const (measure_ne_top _ _)).integrable_indicator (measurableSet_bohrSet _ _)
  have hU_int : Integrable (U.indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const (measure_ne_top _ _)).integrable_indicator hU
  have hpt : (fun t => ((N t - 1 : ℕ) : ℝ)) = fun t => (N t : ℝ) - U.indicator (fun _ => (1 : ℝ)) t := by
    ext t
    by_cases ht : t ∈ U
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ht
      have hpos : 1 ≤ N t := Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
      simp [ht, Nat.cast_sub hpos]
    · have h0 : N t = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i _ hi; exact ht (Set.mem_iUnion.mpr ⟨i, hi⟩)
      simp [ht, h0]
  rw [hpt, integral_sub hN_int hU_int]
  have h1 : ∫ t : UnitAddCircle, (N t : ℝ) = 2 * (n : ℝ) * δ := by
    have heq : (fun t => (N t : ℝ)) = fun t => ∑ i : Fin n, (bohrSet (v i) δ).indicator (fun _ => (1 : ℝ)) t := by
      ext t; simp only [N, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Set.indicator]
    rw [heq, integral_finsetSum _ fun i _ =>
      (integrableOn_const (measure_ne_top _ _)).integrable_indicator (measurableSet_bohrSet _ _)]
    have hterm : ∀ i : Fin n,
        ∫ t : UnitAddCircle, (bohrSet (v i) δ).indicator (fun _ => (1 : ℝ)) t = 2 * δ := fun i => by
      rw [integral_indicator (measurableSet_bohrSet _ _), setIntegral_const, smul_eq_mul, mul_one,
        volume_real_bohrSet (hv i) hδ0 hδ1]
    simp_rw [hterm]
    simp; ring
  have h2 : ∫ t : UnitAddCircle, U.indicator (fun _ => (1 : ℝ)) t = volume.real U := by
    rw [integral_indicator hU, setIntegral_const, smul_eq_mul, mul_one]
  rw [h1, h2]

private lemma pair_integral_eq {n : ℕ} (v : Fin n → ℕ) (δ : ℝ) :
    ∫ t : UnitAddCircle,
        ((Finset.univ.filter fun i : Fin n => t ∈ bohrSet (v i) δ).card : ℝ) *
          (((Finset.univ.filter fun i : Fin n => t ∈ bohrSet (v i) δ).card : ℝ) - 1) =
      ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag,
        volume.real (bohrSet (v p.1) δ ∩ bohrSet (v p.2) δ) := by
  classical
  have hpt : ∀ t : UnitAddCircle,
      ((Finset.univ.filter fun i : Fin n => t ∈ bohrSet (v i) δ).card : ℝ) *
        (((Finset.univ.filter fun i : Fin n => t ∈ bohrSet (v i) δ).card : ℝ) - 1) =
        ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag,
          (bohrSet (v p.1) δ ∩ bohrSet (v p.2) δ).indicator (fun _ => (1 : ℝ)) t := by
    intro t
    let S := Finset.univ.filter fun i : Fin n => t ∈ bohrSet (v i) δ
    have hcard : (S.offDiag.card : ℝ) = (S.card : ℝ) * ((S.card : ℝ) - 1) := by
      rw [Finset.offDiag_card]
      cases h : S.card with
      | zero => simp
      | succ c =>
        have h1 : (c + 1) * (c + 1) - (c + 1) = (c + 1) * c := by
          have : (c + 1) * (c + 1) = (c + 1) * c + (c + 1) := by ring
          omega
        rw [h1]
        push_cast; ring
    change (S.card : ℝ) * ((S.card : ℝ) - 1) = _
    rw [← hcard]
    have hfilt : S.offDiag = (Finset.univ : Finset (Fin n)).offDiag.filter
        (fun p => t ∈ bohrSet (v p.1) δ ∩ bohrSet (v p.2) δ) := by
      ext ⟨i, j⟩
      simp only [S, Finset.mem_offDiag, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_inter_iff]
      tauto
    rw [hfilt, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [Set.indicator]
  simp_rw [hpt]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_indicator ((measurableSet_bohrSet _ _).inter (measurableSet_bohrSet _ _)),
      setIntegral_const, smul_eq_mul, mul_one]
  · intro p _
    exact (integrableOn_const (measure_ne_top _ _)).integrable_indicator
      ((measurableSet_bohrSet _ _).inter (measurableSet_bohrSet _ _))

private theorem main_sparse_bound :
    OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_variants_tao_2017_R1.H2 := by
  classical
  refine ⟨5 / 96, by norm_num, fun n hn v hv hsparse => ?_⟩
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  let δ₀ : ℝ := 1 / (2 * (n : ℝ))
  let δ₁ : ℝ := 3 / (4 * (n : ℝ))
  have hδ₀ : 0 < δ₀ := by positivity
  have hδ₁_pos : 0 < δ₁ := by positivity
  have hδ_le : δ₀ ≤ δ₁ := by
    dsimp [δ₀, δ₁]; rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
  have hδ₁_lt : δ₁ < 1 / 2 := by
    dsimp [δ₁]; rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hδ₀_lt : δ₀ < 1 / 2 := lt_of_le_of_lt hδ_le hδ₁_lt
  have hs : δ₁ / δ₀ = 3 / 2 := by
    dsimp [δ₀, δ₁]; field_simp; ring
  let N (δ : ℝ) (t : UnitAddCircle) : ℕ :=
    (Finset.univ.filter fun i : Fin n => t ∈ bohrSet (v i) δ).card
  let w (δ : ℝ) : ℝ := ∫ t : UnitAddCircle, ((N δ t - 1 : ℕ) : ℝ)
  let P (δ : ℝ) : ℝ := ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag,
    volume.real (bohrSet (v p.1) δ ∩ bohrSet (v p.2) δ)
  let cType1 : ℝ := ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag,
    (Nat.gcd (v p.1) (v p.2) : ℝ) / (max (v p.1 : ℝ) (v p.2 : ℝ))
  let Q (δ : ℝ) : ℝ := P δ - 2 * δ * cType1
  -- Step 1: Dilation spillover inequality: P δ₁ - 2 * w δ₁ ≥ (3 / 2) * (P δ₀ - 2 * w δ₀)
  have hP_spill : (3 / 2 : ℝ) * (P δ₀ - 2 * w δ₀) ≤ P δ₁ - 2 * w δ₁ := by
    have hlayer : ∀ δ : ℝ, P δ - 2 * w δ =
        2 * ∑ k ∈ Finset.Ico 2 n, ∫ t : UnitAddCircle, ((N δ t - k : ℕ) : ℝ) := by
      intro δ
      have hmeasN : Measurable (N δ) := by
        have heq : N δ = fun t => ∑ i : Fin n, (bohrSet (v i) δ).indicator (fun _ => 1) t := by
          ext t; simp only [N, Finset.card_filter, Set.indicator]
        rw [heq]
        exact Finset.measurable_sum _ fun i _ => measurable_const.indicator (measurableSet_bohrSet _ _)
      have hint_k : ∀ k ∈ Finset.Ico 2 n,
          Integrable (fun t : UnitAddCircle => ((N δ t - k : ℕ) : ℝ)) := fun k _ => by
        refine Integrable.of_bound
          (Measurable.comp measurable_from_top (hmeasN.sub measurable_const)).aestronglyMeasurable
          (n : ℝ) (Filter.Eventually.of_forall fun t => ?_)
        rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
        exact_mod_cast (Nat.sub_le _ _).trans ((Finset.card_filter_le _ _).trans_eq (Fintype.card_fin n))
      have hP_int : Integrable (fun t : UnitAddCircle => (N δ t : ℝ) * ((N δ t : ℝ) - 1)) := by
        have hpt : ∀ t : UnitAddCircle,
            (N δ t : ℝ) * ((N δ t : ℝ) - 1) =
              ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag,
                (bohrSet (v p.1) δ ∩ bohrSet (v p.2) δ).indicator (fun _ => (1 : ℝ)) t := by
          intro t
          let S := Finset.univ.filter fun i : Fin n => t ∈ bohrSet (v i) δ
          have hcard : (S.offDiag.card : ℝ) = (S.card : ℝ) * ((S.card : ℝ) - 1) := by
            rw [Finset.offDiag_card]
            cases h : S.card with
            | zero => simp
            | succ c =>
              have h1 : (c + 1) * (c + 1) - (c + 1) = (c + 1) * c := by
                have : (c + 1) * (c + 1) = (c + 1) * c + (c + 1) := by ring
                omega
              rw [h1]; push_cast; ring
          change (S.card : ℝ) * ((S.card : ℝ) - 1) = _
          rw [← hcard]
          have hfilt : S.offDiag = (Finset.univ : Finset (Fin n)).offDiag.filter
              (fun p => t ∈ bohrSet (v p.1) δ ∩ bohrSet (v p.2) δ) := by
            ext ⟨i, j⟩
            simp only [S, Finset.mem_offDiag, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_inter_iff]
            tauto
          rw [hfilt, Finset.card_filter, Nat.cast_sum]
          exact Finset.sum_congr rfl fun p _ => by simp [Set.indicator]
        simp_rw [hpt]
        exact integrable_finsetSum _ fun p _ =>
          (integrableOn_const (measure_ne_top _ _)).integrable_indicator
            ((measurableSet_bohrSet _ _).inter (measurableSet_bohrSet _ _))
      have hw_int : Integrable (fun t : UnitAddCircle => ((N δ t - 1 : ℕ) : ℝ)) := by
        refine Integrable.of_bound
          (Measurable.comp measurable_from_top (hmeasN.sub measurable_const)).aestronglyMeasurable
          (n : ℝ) (Filter.Eventually.of_forall fun t => ?_)
        rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
        exact_mod_cast (Nat.sub_le _ _).trans ((Finset.card_filter_le _ _).trans_eq (Fintype.card_fin n))
      rw [← integral_finsetSum _ hint_k, ← integral_const_mul]
      dsimp [P, w]
      rw [← pair_integral_eq (fun i => v i) δ, ← integral_const_mul, ← integral_sub hP_int (hw_int.const_mul 2)]
      congr 1; ext t
      exact nat_pair_layer_identity n (N δ t) ((Finset.card_filter_le _ _).trans_eq (Fintype.card_fin n))
    rw [hlayer δ₀, hlayer δ₁]
    have hsum_mono :
        ∑ k ∈ Finset.Ico 2 n, (1 / δ₀) * ∫ t : UnitAddCircle, ((N δ₀ t - k : ℕ) : ℝ) ≤
          ∑ k ∈ Finset.Ico 2 n, (1 / δ₁) * ∫ t : UnitAddCircle, ((N δ₁ t - k : ℕ) : ℝ) := by
      refine Finset.sum_le_sum fun k hk => ?_
      have hk1 : 1 ≤ k := by have := (Finset.mem_Ico.mp hk).1; omega
      exact torus_excess_dilation_mono hk1 (fun i => v i) hv hδ₀ hδ_le hδ₁_lt
    rw [← Finset.mul_sum, ← Finset.mul_sum] at hsum_mono
    have hmul := mul_le_mul_of_nonneg_left hsum_mono (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hδ₁_pos.le)
    have e1 : 2 * δ₁ * ((1 / δ₀) * ∑ k ∈ Finset.Ico 2 n, ∫ t : UnitAddCircle, ((N δ₀ t - k : ℕ) : ℝ)) =
        (3 / 2 : ℝ) * (2 * ∑ k ∈ Finset.Ico 2 n, ∫ t : UnitAddCircle, ((N δ₀ t - k : ℕ) : ℝ)) := by
      have hrat : δ₁ * (1 / δ₀) = 3 / 2 := by rw [mul_one_div, hs]
      calc
        2 * δ₁ * ((1 / δ₀) * ∑ k ∈ Finset.Ico 2 n, ∫ t : UnitAddCircle, ((N δ₀ t - k : ℕ) : ℝ))
            = 2 * (δ₁ * (1 / δ₀)) * ∑ k ∈ Finset.Ico 2 n, ∫ t : UnitAddCircle, ((N δ₀ t - k : ℕ) : ℝ) := by ring
        _ = 2 * (3 / 2 : ℝ) * ∑ k ∈ Finset.Ico 2 n, ∫ t : UnitAddCircle, ((N δ₀ t - k : ℕ) : ℝ) := by rw [hrat]
        _ = (3 / 2 : ℝ) * (2 * ∑ k ∈ Finset.Ico 2 n, ∫ t : UnitAddCircle, ((N δ₀ t - k : ℕ) : ℝ)) := by ring
    have e2 : 2 * δ₁ * ((1 / δ₁) * ∑ k ∈ Finset.Ico 2 n, ∫ t : UnitAddCircle, ((N δ₁ t - k : ℕ) : ℝ)) =
        2 * ∑ k ∈ Finset.Ico 2 n, ∫ t : UnitAddCircle, ((N δ₁ t - k : ℕ) : ℝ) := by
      field_simp
    linarith
  -- Step 2: Subtract linear Type I term to get Q δ₁ ≥ (3 / 2) * Q δ₀ + 2 * w δ₁ - 3 * w δ₀
  have hQ_spill : (3 / 2 : ℝ) * Q δ₀ + 2 * w δ₁ - 3 * w δ₀ ≤ Q δ₁ := by
    have hlin : (3 / 2 : ℝ) * (2 * δ₀ * cType1) = 2 * δ₁ * cType1 := by
      have hδeq : (3 / 2 : ℝ) * δ₀ = δ₁ := by
        have := hs; rw [div_eq_iff hδ₀.ne'] at this; linarith
      calc
        (3 / 2 : ℝ) * (2 * δ₀ * cType1) = 2 * ((3 / 2 : ℝ) * δ₀) * cType1 := by ring
        _ = 2 * δ₁ * cType1 := by rw [hδeq]
    dsimp [Q] at *
    linarith
  -- Step 3: w δ₁ ≥ 1 / 2
  have hw1 : (1 / 2 : ℝ) ≤ w δ₁ := by
    dsimp [w]
    rw [excess_one_eq (fun i => v i) hv hδ₁_pos.le (by linarith)]
    have hU_le : volume.real (⋃ i : Fin n, bohrSet (v i) δ₁) ≤ 1 := by
      calc
        volume.real (⋃ i : Fin n, bohrSet (v i) δ₁) ≤ volume.real (Set.univ : Set UnitAddCircle) :=
          measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)
        _ = 1 := by simp [measureReal_def]
    have h2nδ₁ : 2 * (n : ℝ) * δ₁ = 3 / 2 := by dsimp [δ₁]; field_simp; ring
    linarith
  -- Step 4: Upper bound Q δ₁ ≤ (9 / 4) * (1 - 1 / n)
  have hQ1_ub : Q δ₁ ≤ (9 / 4 : ℝ) * (1 - 1 / (n : ℝ)) := by
    have hQ_eq : Q δ₁ = ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag,
        (volume.real (bohrSet (v p.1) δ₁ ∩ bohrSet (v p.2) δ₁) -
          2 * δ₁ * (Nat.gcd (v p.1) (v p.2) : ℝ) / (max (v p.1 : ℝ) (v p.2 : ℝ))) := by
      dsimp [Q, P, cType1]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => by ring
    rw [hQ_eq]
    have hle : ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag,
        (volume.real (bohrSet (v p.1) δ₁ ∩ bohrSet (v p.2) δ₁) -
          2 * δ₁ * (Nat.gcd (v p.1) (v p.2) : ℝ) / (max (v p.1 : ℝ) (v p.2 : ℝ))) ≤
        ∑ _p ∈ (Finset.univ : Finset (Fin n)).offDiag, (4 * δ₁ ^ 2) :=
      Finset.sum_le_sum fun p _ => (pair_typeII_bounds (hv p.1) (hv p.2) hδ₁_pos hδ₁_lt).2.2
    refine hle.trans_eq ?_
    rw [Finset.sum_const, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hsub : ((n * n - n : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
      have h1 : n * n - n = n * (n - 1) := by rw [Nat.mul_sub_left_distrib, mul_one]
      rw [h1, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    rw [hsub]
    dsimp [δ₁]
    field_simp
    ring
  -- Step 5: Lower bound Q δ₀ ≥ 1 - 1 / n - 1 / 16
  have hQ0_lb : 1 - 1 / (n : ℝ) - 1 / 16 ≤ Q δ₀ := by
    have hQ_eq : Q δ₀ = ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag,
        (volume.real (bohrSet (v p.1) δ₀ ∩ bohrSet (v p.2) δ₀) -
          2 * δ₀ * (Nat.gcd (v p.1) (v p.2) : ℝ) / (max (v p.1 : ℝ) (v p.2 : ℝ))) := by
      dsimp [Q, P, cType1]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => by ring
    rw [hQ_eq]
    let denseU := (Finset.univ : Finset (Fin n × Fin n)).filter fun ij =>
      ij.1 < ij.2 ∧ max (v ij.1) (v ij.2) ≤ 64 * n * Nat.gcd (v ij.1) (v ij.2)
    let denseO := (Finset.univ : Finset (Fin n)).offDiag.filter fun p =>
      max (v p.1) (v p.2) ≤ 64 * n * Nat.gcd (v p.1) (v p.2)
    let sparseO := (Finset.univ : Finset (Fin n)).offDiag.filter fun p =>
      ¬ (max (v p.1) (v p.2) ≤ 64 * n * Nat.gcd (v p.1) (v p.2))
    have hdenseO_card : denseO.card = 2 * denseU.card := by
      have hsplit : denseO = denseU ∪ denseU.image Prod.swap := by
        ext ⟨i, j⟩
        simp only [denseO, denseU, Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ,
          true_and, Finset.mem_union, Finset.mem_image, Prod.exists, Prod.swap_prod_mk,
          Prod.mk.injEq]
        constructor
        · rintro ⟨hij, hle⟩
          rcases lt_or_gt_of_ne hij with hlt | hgt
          · exact Or.inl ⟨hlt, hle⟩
          · exact Or.inr ⟨j, i, ⟨hgt, by simpa [max_comm, Nat.gcd_comm] using hle⟩, rfl, rfl⟩
        · rintro (⟨hlt, hle⟩ | ⟨a, b, ⟨hlt, hle⟩, rfl, rfl⟩)
          · exact ⟨hlt.ne, hle⟩
          · exact ⟨hlt.ne', by simpa [max_comm, Nat.gcd_comm] using hle⟩
      have hdisj : Disjoint denseU (denseU.image Prod.swap) := by
        rw [Finset.disjoint_left]
        intro ⟨i, j⟩ h1 h2
        simp only [denseU, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
          Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq] at h1 h2
        obtain ⟨a, b, ⟨hab, _⟩, rfl, rfl⟩ := h2
        exact lt_asymm h1.1 hab
      rw [hsplit, Finset.card_union_of_disjoint hdisj,
        Finset.card_image_of_injective _ Prod.swap_injective, two_mul]
    have hdenseU_eq : denseU.card =
        ((Finset.univ : Finset (Fin n × Fin n)).filter fun ij =>
          ij.1 < ij.2 ∧ max (v ij.1) (v ij.2) ≤ 64 * n * Nat.gcd (v ij.1) (v ij.2)).card := by
      congr 1
    have hdenseO_lt : 32 * denseO.card < n ^ 2 := by
      rw [hdenseO_card, hdenseU_eq]; omega
    have hsparse_card : sparseO.card + denseO.card = n * n - n := by
      have hadd := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n)).offDiag)
        (p := fun p : Fin n × Fin n => max (v p.1) (v p.2) ≤ 64 * n * Nat.gcd (v p.1) (v p.2))
      rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin] at hadd
      change denseO.card + sparseO.card = n * n - n at hadd
      omega
    have hsum_ge :
        ∑ p ∈ sparseO, ((1 - 1 / 32 : ℝ) / (n : ℝ) ^ 2) ≤
          ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag,
            (volume.real (bohrSet (v p.1) δ₀ ∩ bohrSet (v p.2) δ₀) -
              2 * δ₀ * (Nat.gcd (v p.1) (v p.2) : ℝ) / (max (v p.1 : ℝ) (v p.2 : ℝ))) := by
      have h1 :
          ∑ p ∈ sparseO, ((1 - 1 / 32 : ℝ) / (n : ℝ) ^ 2) ≤
            ∑ p ∈ sparseO,
              (volume.real (bohrSet (v p.1) δ₀ ∩ bohrSet (v p.2) δ₀) -
                2 * δ₀ * (Nat.gcd (v p.1) (v p.2) : ℝ) / (max (v p.1 : ℝ) (v p.2 : ℝ))) := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hgt : 64 * n * Nat.gcd (v p.1) (v p.2) < max (v p.1) (v p.2) :=
          not_le.mp (Finset.mem_filter.mp hp).2
        have hmax_pos : (0 : ℝ) < (max (v p.1 : ℝ) (v p.2 : ℝ)) := by
          exact lt_of_lt_of_le (Nat.cast_pos.mpr (hv p.1)) (le_max_left _ _)
        have hratio_le : (Nat.gcd (v p.1) (v p.2) : ℝ) / (max (v p.1 : ℝ) (v p.2 : ℝ)) ≤
            1 / (64 * (n : ℝ)) := by
          rw [div_le_div_iff₀ hmax_pos (by positivity), one_mul]
          have hgtR : 64 * (n : ℝ) * (Nat.gcd (v p.1) (v p.2) : ℝ) ≤ (max (v p.1 : ℝ) (v p.2 : ℝ)) := by
            have : 64 * (n : ℝ) * (Nat.gcd (v p.1) (v p.2) : ℝ) ≤ ((max (v p.1) (v p.2) : ℕ) : ℝ) := by
              exact_mod_cast le_of_lt hgt
            rwa [Nat.cast_max] at this
          linarith
        have hlb := (pair_typeII_bounds (hv p.1) (hv p.2) hδ₀ hδ₀_lt).2.1
        have h4δ₀ : 4 * δ₀ ^ 2 = 1 / (n : ℝ) ^ 2 := by dsimp [δ₀]; field_simp; ring
        have h4δ₀r : 4 * δ₀ * (Nat.gcd (v p.1) (v p.2) : ℝ) / (max (v p.1 : ℝ) (v p.2 : ℝ)) ≤
            (1 / 32 : ℝ) / (n : ℝ) ^ 2 := by
          rw [mul_div_assoc]
          calc
            4 * δ₀ * ((Nat.gcd (v p.1) (v p.2) : ℝ) / (max (v p.1 : ℝ) (v p.2 : ℝ)))
                ≤ 4 * δ₀ * (1 / (64 * (n : ℝ))) :=
                  mul_le_mul_of_nonneg_left hratio_le (by positivity)
            _ = (1 / 32 : ℝ) / (n : ℝ) ^ 2 := by dsimp [δ₀]; field_simp; ring
        have hsub : (1 - 1 / 32 : ℝ) / (n : ℝ) ^ 2 = 1 / (n : ℝ) ^ 2 - (1 / 32 : ℝ) / (n : ℝ) ^ 2 := by ring
        linarith
      refine h1.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun p _ _ => ?_)
      exact (pair_typeII_bounds (hv p.1) (hv p.2) hδ₀ hδ₀_lt).1
    refine le_trans ?_ hsum_ge
    rw [Finset.sum_const, nsmul_eq_mul]
    have hsparse_R : (sparseO.card : ℝ) = (n : ℝ) ^ 2 - (n : ℝ) - (denseO.card : ℝ) := by
      have h1 : (sparseO.card : ℝ) + (denseO.card : ℝ) = ((n * n - n : ℕ) : ℝ) := by
        exact_mod_cast hsparse_card
      have h2 : ((n * n - n : ℕ) : ℝ) = (n : ℝ) ^ 2 - (n : ℝ) := by
        rw [Nat.cast_sub (Nat.le_mul_self n)]; push_cast; ring
      linarith
    have hdense_R : (denseO.card : ℝ) < (n : ℝ) ^ 2 / 32 := by
      have : 32 * (denseO.card : ℝ) < (n : ℝ) ^ 2 := by exact_mod_cast hdenseO_lt
      linarith
    rw [hsparse_R]
    have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    have h1 : (1 - 1 / (n : ℝ) - 1 / 32) ≤ ((n : ℝ) ^ 2 - (n : ℝ) - (denseO.card : ℝ)) / (n : ℝ) ^ 2 := by
      rw [le_div_iff₀ hn2]
      have : (1 - 1 / (n : ℝ) - 1 / 32) * (n : ℝ) ^ 2 = (n : ℝ) ^ 2 - (n : ℝ) - (n : ℝ) ^ 2 / 32 := by
        field_simp
      linarith
    have h2 : ((n : ℝ) ^ 2 - (n : ℝ) - (denseO.card : ℝ)) * ((1 - 1 / 32 : ℝ) / (n : ℝ) ^ 2) =
        (1 - 1 / 32 : ℝ) * (((n : ℝ) ^ 2 - (n : ℝ) - (denseO.card : ℝ)) / (n : ℝ) ^ 2) := by ring
    rw [h2]
    have h3 : 1 - 1 / (n : ℝ) - 1 / 16 ≤ (1 - 1 / 32 : ℝ) * (1 - 1 / (n : ℝ) - 1 / 32) := by
      have hinv : 0 ≤ 1 / (n : ℝ) := by positivity
      nlinarith
    exact h3.trans (mul_le_mul_of_nonneg_left h1 (by norm_num))
  -- Step 6: Combine to get 5 / 96 ≤ w δ₀ ≤ ∑ i, volume.real (A i ∩ ⋃ j ≠ i, A j)
  have hw0_ge : (5 / 96 : ℝ) ≤ w δ₀ := by
    have hinv : 0 < 1 / (n : ℝ) := by positivity
    linarith
  exact hw0_ge.trans (overlap_ge_excess (fun i => bohrSet (v i) δ₀) fun i => measurableSet_bohrSet _ _)

end LonelyRunnerSparseProof

theorem OMA.solution :
    OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_variants_tao_2017_R1.H2 :=
  LonelyRunnerSparseProof.main_sparse_bound

import OMAReductions.R_wp_perfect_1_factorization_conjecture_R1
import Mathlib.Data.Finset.Pi

/-!
# Proof of `wp-perfect-1-factorization-conjecture.R1.H1`

Count perfect matchings containing the root edge `(Fin.last m, c.castSucc)` and preserving every
cut `S ∈ D` by translating matchings to fixed-point-free involutions on the remaining vertices,
decomposing over cut-signature fibers via `Finset.pi`, and evaluating each fiber size via the
double-factorial recurrence `(n + 1)!! = (n + 1) * (n - 1)!!`.
-/

-- Step wp-perfect-1-factorization-conjecture.R1.H1: hypothesis H1 of reduction wp-perfect-1-factorization-conjecture.R1
-- Credit: @LiJiaHua1024

namespace OMA.Step_Perfect1Fact_H1

open Finset SimpleGraph
open scoped BigOperators

/-- `f : V → V` acts as a fixed-point-free involution on `U` and the identity outside `U`. -/
def IsFPFInvOn {V : Type*} (U : Finset V) (f : V → V) : Prop :=
  (∀ x ∈ U, f x ∈ U ∧ f x ≠ x ∧ f (f x) = x) ∧ (∀ x, x ∉ U → f x = x)

noncomputable def fpfFinset {V : Type*} [Fintype V] [DecidableEq V] (U : Finset V) :
    Finset (V → V) :=
  open Classical in Finset.univ.filter (IsFPFInvOn U)

lemma mem_fpfFinset {V : Type*} [Fintype V] [DecidableEq V] {U : Finset V} {f : V → V} :
    f ∈ fpfFinset U ↔ IsFPFInvOn U f := by
  classical
  simp [fpfFinset]

def swapExtend {V : Type*} [DecidableEq V] (a b : V) (g : V → V) (x : V) : V :=
  if x = a then b else if x = b then a else g x

lemma swapExtend_mem_fpfFinset {V : Type*} [Fintype V] [DecidableEq V]
    {U : Finset V} {a b : V} (ha : a ∈ U) (hb : b ∈ U.erase a)
    {g : V → V} (hg : g ∈ fpfFinset ((U.erase a).erase b)) :
    swapExtend a b g ∈ fpfFinset U := by
  rw [mem_fpfFinset] at hg ⊢
  have hba : b ≠ a := (Finset.mem_erase.mp hb).1
  have hbU : b ∈ U := (Finset.mem_erase.mp hb).2
  constructor
  · intro x hx
    by_cases hxa : x = a
    · subst hxa
      simp [swapExtend, hbU, hba]
    · by_cases hxb : x = b
      · subst hxb
        simp [swapExtend, ha, hba, hba.symm]
      · have hxrem : x ∈ (U.erase a).erase b :=
          Finset.mem_erase.mpr ⟨hxb, Finset.mem_erase.mpr ⟨hxa, hx⟩⟩
        obtain ⟨hmem, hne, hinv⟩ := hg.1 x hxrem
        have hgy_ne_b : g x ≠ b := (Finset.mem_erase.mp hmem).1
        have hgy_ne_a : g x ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hmem).2).1
        have hgy_U : g x ∈ U := (Finset.mem_erase.mp (Finset.mem_erase.mp hmem).2).2
        simp [swapExtend, hxa, hxb, hgy_ne_a, hgy_ne_b, hgy_U, hne, hinv]
  · intro x hxU
    have hxa : x ≠ a := fun h => hxU (h ▸ ha)
    have hxb : x ≠ b := fun h => hxU (h ▸ hbU)
    have hxrem : x ∉ (U.erase a).erase b := fun h =>
      hxU (Finset.mem_erase.mp (Finset.mem_erase.mp h).2).2
    simp [swapExtend, hxa, hxb, hg.2 x hxrem]

lemma swapExtend_injOn {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset V) (a b : V) :
    Set.InjOn (swapExtend a b) (fpfFinset ((U.erase a).erase b) : Set (V → V)) := by
  intro g₁ hg₁ g₂ hg₂ heq
  rw [Finset.mem_coe, mem_fpfFinset] at hg₁ hg₂
  funext x
  by_cases hxa : x = a
  · subst hxa
    have hn : x ∉ (U.erase x).erase b := by simp
    rw [hg₁.2 x hn, hg₂.2 x hn]
  · by_cases hxb : x = b
    · subst hxb
      have hn : x ∉ (U.erase a).erase x := by simp
      rw [hg₁.2 x hn, hg₂.2 x hn]
    · have h := congrFun heq x
      simpa [swapExtend, hxa, hxb] using h

lemma card_fpfFinset {V : Type*} [Fintype V] [DecidableEq V] (U : Finset V) :
    (fpfFinset U).card = if Even U.card then (U.card - 1).doubleFactorial else 0 := by
  generalize hk : U.card = k
  induction k using Nat.strong_induction_on generalizing U with
  | _ k ih =>
    rcases k with _ | _ | n
    · have hU : U = ∅ := Finset.card_eq_zero.mp hk
      subst hU
      have heq : fpfFinset (∅ : Finset V) = {id} := by
        ext f
        simp [mem_fpfFinset, IsFPFInvOn, funext_iff]
      rw [heq]
      simp
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hk
      have heq : fpfFinset ({a} : Finset V) = ∅ := by
        ext f
        simp only [mem_fpfFinset, Finset.notMem_empty, iff_false]
        intro hf
        obtain ⟨hmem, hne, -⟩ := hf.1 a (Finset.mem_singleton_self a)
        exact hne (Finset.mem_singleton.mp hmem)
      rw [heq]
      simp
    · obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < U.card)
      let U' := U.erase a
      have hU'card : U'.card = n + 1 := by
        dsimp [U']
        rw [Finset.card_erase_of_mem ha, hk]
        rfl
      have hpart : fpfFinset U =
          U'.biUnion (fun b => (fpfFinset (U'.erase b)).image (swapExtend a b)) := by
        ext f
        simp only [Finset.mem_biUnion, Finset.mem_image]
        constructor
        · intro hf
          rw [mem_fpfFinset] at hf
          obtain ⟨hfa_U, hfa_ne, hffa⟩ := hf.1 a ha
          have hb : f a ∈ U' := Finset.mem_erase.mpr ⟨hfa_ne, hfa_U⟩
          let g : V → V := fun x => if x = a ∨ x = f a then x else f x
          refine ⟨f a, hb, g, ?_, ?_⟩
          · rw [mem_fpfFinset]
            constructor
            · intro x hx
              have hx_ne_fa : x ≠ f a := (Finset.mem_erase.mp hx).1
              have hx_ne_a : x ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
              have hxU : x ∈ U := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2
              obtain ⟨hfxU, hfx_ne, hffx⟩ := hf.1 x hxU
              have hfx_ne_a : f x ≠ a := by
                intro h
                have := congrArg f h
                rw [hffx] at this
                exact hx_ne_fa this
              have hfx_ne_fa : f x ≠ f a := by
                intro h
                have := congrArg f h
                rw [hffx, hffa] at this
                exact hx_ne_a this
              have hgx : g x = f x := by simp [g, hx_ne_a, hx_ne_fa]
              have hgfx : g (f x) = f (f x) := by simp [g, hfx_ne_a, hfx_ne_fa]
              refine ⟨?_, ?_, ?_⟩
              · rw [hgx]
                exact Finset.mem_erase.mpr ⟨hfx_ne_fa, Finset.mem_erase.mpr ⟨hfx_ne_a, hfxU⟩⟩
              · rw [hgx]; exact hfx_ne
              · rw [hgx, hgfx, hffx]
            · intro x hx
              by_cases hcond : x = a ∨ x = f a
              · simp [g, hcond]
              · push Not at hcond
                have hxnotU : x ∉ U := fun hxU =>
                  hx (Finset.mem_erase.mpr ⟨hcond.2, Finset.mem_erase.mpr ⟨hcond.1, hxU⟩⟩)
                simp [g, hcond.1, hcond.2, hf.2 x hxnotU]
          · funext x
            by_cases hxa : x = a
            · subst hxa; simp [swapExtend]
            · by_cases hxb : x = f a
              · subst hxb; simp [swapExtend, hfa_ne, hffa]
              · simp [swapExtend, g, hxa, hxb]
        · rintro ⟨b, hb, g, hg, rfl⟩
          exact swapExtend_mem_fpfFinset ha hb hg
      have hdisj : (U' : Set V).PairwiseDisjoint
          (fun b => (fpfFinset (U'.erase b)).image (swapExtend a b)) := by
        intro b₁ _ b₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro f hf₁ hf₂
        obtain ⟨g₁, -, rfl⟩ := Finset.mem_image.mp hf₁
        obtain ⟨g₂, -, heq⟩ := Finset.mem_image.mp hf₂
        have := congrFun heq a
        simp only [swapExtend, ↓reduceIte] at this
        exact hne this.symm
      rw [hpart, Finset.card_biUnion hdisj]
      have hterm : ∀ b ∈ U',
          ((fpfFinset (U'.erase b)).image (swapExtend a b)).card =
            if Even n then (n - 1).doubleFactorial else 0 := by
        intro b hb
        rw [Finset.card_image_of_injOn (swapExtend_injOn U a b)]
        have hc : (U'.erase b).card = n := by
          rw [Finset.card_erase_of_mem hb, hU'card]
          rfl
        exact ih n (by omega) (U'.erase b) hc
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, hU'card, smul_eq_mul]
      have heven_iff : Even (n + 2) ↔ Even n := by
        rw [Nat.even_add]
        simp
      by_cases hn : Even n
      · rw [if_pos hn, if_pos (heven_iff.mpr hn)]
        change (n + 1) * (n - 1).doubleFactorial = (n + 1).doubleFactorial
        exact (Nat.doubleFactorial_add_one n).symm
      · rw [if_neg hn, if_neg (mt heven_iff.mp hn), mul_zero]

/-- Fiber decomposition of signature-preserving involutions on `rem`. -/
lemma card_sig_fpfFinset {V α : Type*} [Fintype V] [DecidableEq V] [DecidableEq α]
    (rem : Finset V) (sig : V → α) :
    ((fpfFinset rem).filter (fun g => ∀ x ∈ rem, sig (g x) = sig x)).card =
      ∏ s ∈ rem.image sig, (fpfFinset (rem.filter (fun v => sig v = s))).card := by
  rw [← Finset.card_pi]
  refine Finset.card_bij
    (fun g _ s _ => fun x => if sig x = s then g x else x)
    ?_ ?_ ?_
  · intro g hg
    obtain ⟨hg_fpf, hgsig⟩ := Finset.mem_filter.mp hg
    rw [mem_fpfFinset] at hg_fpf
    rw [Finset.mem_pi]
    intro s _
    rw [mem_fpfFinset]
    constructor
    · intro x hx
      obtain ⟨hx_rem, hxs⟩ := Finset.mem_filter.mp hx
      obtain ⟨hgx_rem, hgx_ne, hggx⟩ := hg_fpf.1 x hx_rem
      have hgxs : sig (g x) = s := (hgsig x hx_rem).trans hxs
      refine ⟨?_, ?_, ?_⟩
      · simp [hxs, hgx_rem, hgxs]
      · simp [hxs, hgx_ne]
      · simp [hxs, hgxs, hggx]
    · intro x hx
      by_cases hxs : sig x = s
      · have hx_not_rem : x ∉ rem := fun h => hx (Finset.mem_filter.mpr ⟨h, hxs⟩)
        simp [hxs, hg_fpf.2 x hx_not_rem]
      · simp [hxs]
  · intro g₁ hg₁ g₂ hg₂ heq
    obtain ⟨hg₁_fpf, -⟩ := Finset.mem_filter.mp hg₁
    obtain ⟨hg₂_fpf, -⟩ := Finset.mem_filter.mp hg₂
    rw [mem_fpfFinset] at hg₁_fpf hg₂_fpf
    funext x
    by_cases hx : x ∈ rem
    · have hs : sig x ∈ rem.image sig := Finset.mem_image_of_mem sig hx
      have h := congrFun (congrFun (congrFun heq (sig x)) hs) x
      simpa using h
    · rw [hg₁_fpf.2 x hx, hg₂_fpf.2 x hx]
  · intro h hh
    rw [Finset.mem_pi] at hh
    let g : V → V := fun x =>
      if hx : x ∈ rem then h (sig x) (Finset.mem_image_of_mem sig hx) x else x
    refine ⟨g, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · rw [mem_fpfFinset]
        constructor
        · intro x hx
          have hs : sig x ∈ rem.image sig := Finset.mem_image_of_mem sig hx
          have h_fpf := mem_fpfFinset.mp (hh (sig x) hs)
          have hxf : x ∈ rem.filter (fun v => sig v = sig x) :=
            Finset.mem_filter.mpr ⟨hx, rfl⟩
          obtain ⟨hy_mem, hy_ne, hy_inv⟩ := h_fpf.1 x hxf
          obtain ⟨hy_rem, hy_sig⟩ := Finset.mem_filter.mp hy_mem
          have hgx : g x = h (sig x) hs x := dif_pos hx
          refine ⟨?_, ?_, ?_⟩
          · rw [hgx]; exact hy_rem
          · rw [hgx]; exact hy_ne
          · have hgy : g (h (sig x) hs x) =
                h (sig (h (sig x) hs x)) (Finset.mem_image_of_mem sig hy_rem) (h (sig x) hs x) :=
              dif_pos hy_rem
            rw [hgx, hgy]
            have hcongr : ∀ (s' : α) (hs' : s' ∈ rem.image sig), s' = sig x →
                h s' hs' (h (sig x) hs x) = h (sig x) hs (h (sig x) hs x) := by
              rintro _ _ rfl
              rfl
            rw [hcongr _ (Finset.mem_image_of_mem sig hy_rem) hy_sig, hy_inv]
        · intro x hx
          exact dif_neg hx
      · intro x hx
        have hs : sig x ∈ rem.image sig := Finset.mem_image_of_mem sig hx
        have h_fpf := mem_fpfFinset.mp (hh (sig x) hs)
        have hxf : x ∈ rem.filter (fun v => sig v = sig x) :=
          Finset.mem_filter.mpr ⟨hx, rfl⟩
        have hy_mem := (h_fpf.1 x hxf).1
        simpa [g, hx] using (Finset.mem_filter.mp hy_mem).2
    · funext s hs x
      by_cases hxs : sig x = s
      · simp only [hxs, ↓reduceIte]
        by_cases hx : x ∈ rem
        · simp only [g, hx, ↓reduceDIte]
          subst hxs
          rfl
        · have h_fpf := mem_fpfFinset.mp (hh s hs)
          have hx_not : x ∉ rem.filter (fun v => sig v = s) := fun hm =>
            hx (Finset.mem_filter.mp hm).1
          simp [g, hx, h_fpf.2 x hx_not]
      · have h_fpf := mem_fpfFinset.mp (hh s hs)
        have hx_not : x ∉ rem.filter (fun v => sig v = s) := fun hm =>
          hxs (Finset.mem_filter.mp hm).2
        simp [hxs, h_fpf.2 x hx_not]

/-- Spanning subgraph of `completeGraph V` associated to a fixed-point-free involution `f`. -/
def subgraphOfInv {V : Type*} (f : V → V) (hf_ne : ∀ v, f v ≠ v)
    (hf_inv : ∀ v, f (f v) = v) : (completeGraph V).Subgraph where
  verts := Set.univ
  Adj u v := f u = v
  adj_sub := by
    intro u v h
    subst h
    exact (hf_ne u).symm
  edge_vert := fun _ => Set.mem_univ _
  symm := ⟨fun u _ h => by rw [← h, hf_inv u]⟩

end OMA.Step_Perfect1Fact_H1

open SimpleGraph
open scoped BigOperators

theorem OMA.solution : OMA.R_wp_perfect_1_factorization_conjecture_R1.H1 := by
  classical
  intro m c D
  let V := Fin (m + 1)
  let r : V := Fin.last m
  let c' : V := c.castSucc
  have hrc : r ≠ c' := by
    intro h
    have hv := congrArg Fin.val h
    simp only [r, c', Fin.val_last, Fin.val_castSucc] at hv
    exact (Nat.ne_of_gt c.isLt) hv
  let rem : Finset V := (Finset.univ.erase r).erase c'
  let sig : V → Finset (Finset V) := fun v => D.filter (v ∈ ·)
  let P := {M : (completeGraph V).Subgraph // M.IsPerfectMatching ∧ M.Adj r c'}
  let validP : Finset P :=
    Finset.univ.filter (fun M : P => ∀ S ∈ D, ∀ x ∈ S, ∀ y, M.val.Adj x y → y ∈ S)
  change validP.card =
    if sig r ≠ sig c' then 0 else
      ∏ s ∈ rem.image sig,
        let k := (rem.filter (sig · = s)).card
        if Even k then Nat.doubleFactorial (k - 1) else 0
  by_cases hsig_rc : sig r ≠ sig c'
  · rw [if_pos hsig_rc]
    suffices hEmpty : validP = ∅ by rw [hEmpty, Finset.card_empty]
    rw [Finset.eq_empty_iff_forall_notMem]
    intro M hM
    have hclosed := (Finset.mem_filter.mp hM).2
    apply hsig_rc
    ext S
    simp only [sig, Finset.mem_filter]
    constructor
    · intro ⟨hSD, hrS⟩
      exact ⟨hSD, hclosed S hSD r hrS c' M.2.2⟩
    · intro ⟨hSD, hcS⟩
      exact ⟨hSD, hclosed S hSD c' hcS r (M.1.adj_symm M.2.2)⟩
  · rw [if_neg hsig_rc]
    push Not at hsig_rc
    let S_inv := (OMA.Step_Perfect1Fact_H1.fpfFinset rem).filter
      (fun g => ∀ x ∈ rem, sig (g x) = sig x)
    have hbij : validP.card = S_inv.card := by
      refine Finset.card_bij
        (fun M _ => fun x =>
          if x ∈ rem then Classical.choose (Subgraph.isPerfectMatching_iff.mp M.2.1 x).exists else x)
        ?_ ?_ ?_
      · intro M hM
        have hclosed := (Finset.mem_filter.mp hM).2
        have oneM := Subgraph.isPerfectMatching_iff.mp M.2.1
        let mate (v : V) : V := Classical.choose (oneM v).exists
        have hmate_adj (v : V) : M.1.Adj v (mate v) := Classical.choose_spec (oneM v).exists
        have hmate_eq {u v : V} (h : M.1.Adj u v) : mate u = v :=
          (oneM u).unique (hmate_adj u) h
        have hmate_inv (v : V) : mate (mate v) = v :=
          hmate_eq (M.1.adj_symm (hmate_adj v))
        have hmate_ne (v : V) : mate v ≠ v :=
          (M.1.adj_sub (hmate_adj v)).symm
        have hmate_r : mate r = c' := hmate_eq M.2.2
        have hmate_c : mate c' = r := hmate_eq (M.1.adj_symm M.2.2)
        have hmate_rem {x : V} (hx : x ∈ rem) : mate x ∈ rem := by
          have hxc : x ≠ c' := (Finset.mem_erase.mp hx).1
          have hxr : x ≠ r := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
          have hyc : mate x ≠ c' := by
            intro h
            have := congrArg mate h
            rw [hmate_inv, hmate_c] at this
            exact hxr this
          have hyr : mate x ≠ r := by
            intro h
            have := congrArg mate h
            rw [hmate_inv, hmate_r] at this
            exact hxc this
          exact Finset.mem_erase.mpr ⟨hyc, Finset.mem_erase.mpr ⟨hyr, Finset.mem_univ _⟩⟩
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · rw [OMA.Step_Perfect1Fact_H1.mem_fpfFinset]
          constructor
          · intro x hx
            have hy : mate x ∈ rem := hmate_rem hx
            change (if x ∈ rem then mate x else x) ∈ rem ∧
              (if x ∈ rem then mate x else x) ≠ x ∧
              (if (if x ∈ rem then mate x else x) ∈ rem then
                mate (if x ∈ rem then mate x else x)
              else (if x ∈ rem then mate x else x)) = x
            simp only [hx, hy, ↓reduceIte]
            exact ⟨trivial, hmate_ne x, hmate_inv x⟩
          · intro x hx
            simp [hx]
        · intro x hx
          simp only [hx, ↓reduceIte]
          ext S
          simp only [sig, Finset.mem_filter]
          constructor
          · intro ⟨hSD, hmS⟩
            exact ⟨hSD, hclosed S hSD (mate x) hmS x (M.1.adj_symm (hmate_adj x))⟩
          · intro ⟨hSD, hxS⟩
            exact ⟨hSD, hclosed S hSD x hxS (mate x) (hmate_adj x)⟩
      · intro M₁ _ M₂ _ heq
        apply Subtype.ext
        have one₁ := Subgraph.isPerfectMatching_iff.mp M₁.2.1
        have one₂ := Subgraph.isPerfectMatching_iff.mp M₂.2.1
        have hverts : ∀ (M : (completeGraph V).Subgraph), M.IsPerfectMatching → M.verts = Set.univ := by
          intro M hpm
          ext v
          simp only [Set.mem_univ, iff_true]
          obtain ⟨w, hw, -⟩ := Subgraph.isPerfectMatching_iff.mp hpm v
          exact M.edge_vert hw
        apply Subgraph.ext ((hverts M₁.1 M₁.2.1).trans (hverts M₂.1 M₂.2.1).symm)
        funext u v
        apply propext
        have hadj_iff : ∀ (M : P) (x y : V),
            M.1.Adj x y ↔
              Classical.choose (Subgraph.isPerfectMatching_iff.mp M.2.1 x).exists = y := by
          intro M x y
          have one := Subgraph.isPerfectMatching_iff.mp M.2.1 x
          constructor
          · intro hxy
            exact one.unique (Classical.choose_spec one.exists) hxy
          · rintro rfl
            exact Classical.choose_spec one.exists
        rw [hadj_iff M₁ u v, hadj_iff M₂ u v]
        suffices hmate_eq :
            Classical.choose (one₁ u).exists = Classical.choose (one₂ u).exists by
          rw [hmate_eq]
        by_cases hurem : u ∈ rem
        · have h := congrFun heq u
          simpa [hurem] using h
        · have hu_cases : u = r ∨ u = c' := by
            by_contra hnot
            push Not at hnot
            exact hurem (Finset.mem_erase.mpr ⟨hnot.2, Finset.mem_erase.mpr ⟨hnot.1, Finset.mem_univ u⟩⟩)
          rcases hu_cases with rfl | rfl
          · have hr1 : Classical.choose (one₁ r).exists = c' :=
              (one₁ r).unique (Classical.choose_spec (one₁ r).exists) M₁.2.2
            have hr2 : Classical.choose (one₂ r).exists = c' :=
              (one₂ r).unique (Classical.choose_spec (one₂ r).exists) M₂.2.2
            rw [hr1, hr2]
          · have hc1 : Classical.choose (one₁ c').exists = r :=
              (one₁ c').unique (Classical.choose_spec (one₁ c').exists) (M₁.1.adj_symm M₁.2.2)
            have hc2 : Classical.choose (one₂ c').exists = r :=
              (one₂ c').unique (Classical.choose_spec (one₂ c').exists) (M₂.1.adj_symm M₂.2.2)
            rw [hc1, hc2]
      · intro g hg
        obtain ⟨hg_fpf, hgsig⟩ := Finset.mem_filter.mp hg
        rw [OMA.Step_Perfect1Fact_H1.mem_fpfFinset] at hg_fpf
        let f : V → V := OMA.Step_Perfect1Fact_H1.swapExtend r c' g
        have hf_ne : ∀ v : V, f v ≠ v := by
          intro v
          by_cases hvr : v = r
          · subst hvr; simp [f, OMA.Step_Perfect1Fact_H1.swapExtend, hrc.symm]
          · by_cases hvc : v = c'
            · subst hvc; simp [f, OMA.Step_Perfect1Fact_H1.swapExtend, hrc, hrc.symm]
            · have hvrem : v ∈ rem :=
                Finset.mem_erase.mpr ⟨hvc, Finset.mem_erase.mpr ⟨hvr, Finset.mem_univ v⟩⟩
              simp [f, OMA.Step_Perfect1Fact_H1.swapExtend, hvr, hvc, (hg_fpf.1 v hvrem).2.1]
        have hf_inv : ∀ v : V, f (f v) = v := by
          intro v
          by_cases hvr : v = r
          · subst hvr; simp [f, OMA.Step_Perfect1Fact_H1.swapExtend, hrc.symm]
          · by_cases hvc : v = c'
            · subst hvc; simp [f, OMA.Step_Perfect1Fact_H1.swapExtend, hrc.symm]
            · have hvrem : v ∈ rem :=
                Finset.mem_erase.mpr ⟨hvc, Finset.mem_erase.mpr ⟨hvr, Finset.mem_univ v⟩⟩
              obtain ⟨hgv_rem, -, hggv⟩ := hg_fpf.1 v hvrem
              have hgvc : g v ≠ c' := (Finset.mem_erase.mp hgv_rem).1
              have hgvr : g v ≠ r := (Finset.mem_erase.mp (Finset.mem_erase.mp hgv_rem).2).1
              simp [f, OMA.Step_Perfect1Fact_H1.swapExtend, hvr, hvc, hgvr, hgvc, hggv]
        let Msub := OMA.Step_Perfect1Fact_H1.subgraphOfInv f hf_ne hf_inv
        have hM_pm : Msub.IsPerfectMatching := by
          rw [Subgraph.isPerfectMatching_iff]
          intro v
          exact ⟨f v, rfl, fun w (hw : f v = w) => hw.symm⟩
        have hM_rc : Msub.Adj r c' := by
          change f r = c'
          simp [f, OMA.Step_Perfect1Fact_H1.swapExtend]
        let M : P := ⟨Msub, hM_pm, hM_rc⟩
        refine ⟨M, ?_, ?_⟩
        · refine Finset.mem_filter.mpr ⟨Finset.mem_univ M, ?_⟩
          intro S hSD x hxS y hxy
          change f x = y at hxy
          subst hxy
          have hsig_eq : sig (f x) = sig x := by
            by_cases hxr : x = r
            · subst hxr
              simp [f, OMA.Step_Perfect1Fact_H1.swapExtend, hsig_rc]
            · by_cases hxc : x = c'
              · subst hxc
                simp [f, OMA.Step_Perfect1Fact_H1.swapExtend, hrc.symm, hsig_rc]
              · have hxrem : x ∈ rem :=
                  Finset.mem_erase.mpr ⟨hxc, Finset.mem_erase.mpr ⟨hxr, Finset.mem_univ x⟩⟩
                simpa [f, OMA.Step_Perfect1Fact_H1.swapExtend, hxr, hxc] using hgsig x hxrem
          have hmem : S ∈ sig x := Finset.mem_filter.mpr ⟨hSD, hxS⟩
          rw [← hsig_eq] at hmem
          exact (Finset.mem_filter.mp hmem).2
        · funext x
          by_cases hxrem : x ∈ rem
          · have hxc : x ≠ c' := (Finset.mem_erase.mp hxrem).1
            have hxr : x ≠ r := (Finset.mem_erase.mp (Finset.mem_erase.mp hxrem).2).1
            have one := Subgraph.isPerfectMatching_iff.mp hM_pm x
            have hchoose : Classical.choose one.exists = f x :=
              one.unique (Classical.choose_spec one.exists) (show Msub.Adj x (f x) from rfl)
            simp [hxrem, hchoose, f, OMA.Step_Perfect1Fact_H1.swapExtend, hxr, hxc]
          · simp [hxrem, hg_fpf.2 x hxrem]
    rw [hbij]
    trans (∏ s ∈ rem.image sig,
      (OMA.Step_Perfect1Fact_H1.fpfFinset (rem.filter (fun v => sig v = s))).card)
    · convert OMA.Step_Perfect1Fact_H1.card_sig_fpfFinset rem sig
    · refine Finset.prod_congr rfl fun s _ => ?_
      exact OMA.Step_Perfect1Fact_H1.card_fpfFinset (rem.filter (fun v => sig v = s))

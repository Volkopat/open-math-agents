import OMAReductions.R_Erdos19_erdos_19_R1_H1_R1
import Mathlib.Logic.Relation

/-!
# Reduction of `Erdos19.erdos_19.R1.H1.R1.H2` (linear spaces with at most 6 points outside a block)

For any complete linear space `(Fin n, L)` with a block `b ∈ L` leaving `u = n - |b| ≤ 6`
points in `U = Fin n \ b`, we prove unconditionally:

1. **König's bipartite edge-coloring theorem** (`E19NearBlock.bipartite_edge_coloring`) from
   scratch via Kempe-chain reachability swaps.
2. **Single-big-block spaces** (`E19NearBlock.color_single_big_block`): every linear space where
   all blocks other than `b` have size `2` is `n`-colorable for all `n` (via explicit
   1-factorizations for even `n` and negation-symmetric embeddings for odd `n`).
3. **General small-outside coloring theorem** (`E19NearBlock.color_of_small_outside`): if
   `L_U = {a ∈ L \ {b} : 2 ≤ |a ∩ U|}` (minus any pairwise-disjoint subfamily `I_0 ⊆ L_U`
   disjoint from `b`) is properly `k`-colorable and `k + 1 ≤ |b|`, then greedy matching
   extension of the `k` color classes into the bipartite 2-line graph `G` reduces `Δ(G')` to
   `F = n - 1 - k`, and König's theorem completes an `n`-coloring of `L`.
4. **Exact degree bound on `L_U`** (`E19NearBlock.degree_LU_le`):
   `Δ(L_U) ≤ s (u - s) + (u - s) / 2` for `s = |a ∩ U| ∈ [2, u]`, yielding greedy chromatic
   bounds `k ≤ 1` (`u = 2`), `k ≤ 3` (`u = 3`), `k ≤ 6` (`u = 4`), `k ≤ 8` (`u = 5`),
   `k ≤ 11` (`u = 6`).
5. **Complete closure of `u ≤ 3` for all `n`** (`E19NearBlock.color_u_le_three`) and **all
   `n ≥ 18`** (plus `u = 4, |b| ≥ 7` and `u = 5, |b| ≥ 9`).

This collapses the infinite problem `Erdos19.erdos_19.R1.H1.R1.H2` to only finitely many
orders `n ≤ 17` with `4 ≤ n - |b| ≤ 6` and a second block of size `≥ 3`, split cleanly into
`H1` (`n ≤ 12`) and `H2` (`13 ≤ n ≤ 17`, `5 ≤ n - |b| ≤ 6`, `7 ≤ |b| ≤ 11`).
-/

section

open Finset
open scoped Classical

namespace E19NearBlock

/- ## Section 1: König's bipartite edge-coloring theorem -/

lemma exists_walk_of_reflTransGen {γ : Type*} {r : γ → γ → Prop} {u v : γ}
    (h : Relation.ReflTransGen r u v) :
    ∃ (k : ℕ) (p : ℕ → γ), p 0 = u ∧ p k = v ∧ ∀ i < k, r (p i) (p (i + 1)) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, fun _ => v, rfl, rfl, fun _ hi => by omega⟩
  | @head a' c' hab _ ih =>
    obtain ⟨k, p, hp0, hpk, hp⟩ := ih
    refine ⟨k + 1, fun i => if i = 0 then a' else p (i - 1), by simp, by simp [hpk], ?_⟩
    intro i hi
    rcases i with _ | i
    · simpa [hp0] using hab
    · simpa using hp i (by omega)

lemma swapCol_inj {D : ℕ} (γ₁ γ₂ : Fin D) :
    Function.Injective (fun γ : Fin D => if γ = γ₁ then γ₂ else if γ = γ₂ then γ₁ else γ) := by
  intro x y hxy
  by_cases hx1 : x = γ₁ <;> by_cases hx2 : x = γ₂ <;>
    by_cases hy1 : y = γ₁ <;> by_cases hy2 : y = γ₂ <;> simp_all

lemma ite_swapCol_eq {D : ℕ} (γ₁ γ₂ x : Fin D) :
    (if x = γ₁ ∨ x = γ₂ then (if x = γ₁ then γ₂ else if x = γ₂ then γ₁ else x) else x) =
    (if x = γ₁ then γ₂ else if x = γ₂ then γ₁ else x) := by
  by_cases h1 : x = γ₁ <;> by_cases h2 : x = γ₂ <;> simp [h1, h2]

/-- König's edge-coloring theorem for finite bipartite graphs: if every vertex on each side has
degree at most `D`, then the edge set `E ⊆ α × β` admits a proper `D`-edge-coloring. -/
theorem bipartite_edge_coloring {α β : Type*} [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β]
    (E : Finset (α × β)) (D : ℕ)
    (hL : ∀ a : α, (E.filter (fun e => e.1 = a)).card ≤ D)
    (hR : ∀ b : β, (E.filter (fun e => e.2 = b)).card ≤ D) :
    ∃ c : E → Fin D,
      (∀ e₁ e₂ : E, e₁ ≠ e₂ → e₁.1.1 = e₂.1.1 → c e₁ ≠ c e₂) ∧
      (∀ e₁ e₂ : E, e₁ ≠ e₂ → e₁.1.2 = e₂.1.2 → c e₁ ≠ c e₂) := by
  induction E using Finset.induction_on with
  | empty =>
    exact ⟨fun e => (Finset.notMem_empty _ e.2).elim,
      fun e => (Finset.notMem_empty _ e.2).elim,
      fun e => (Finset.notMem_empty _ e.2).elim⟩
  | @insert ab E' hab ih =>
    rcases ab with ⟨a, b⟩
    have hL' : ∀ x : α, (E'.filter (fun e => e.1 = x)).card ≤ D := fun x =>
      (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))).trans (hL x)
    have hR' : ∀ y : β, (E'.filter (fun e => e.2 = y)).card ≤ D := fun y =>
      (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))).trans (hR y)
    obtain ⟨c', hcL', hcR'⟩ := ih hL' hR'
    let cfn : α × β → Option (Fin D) := fun e => if h : e ∈ E' then some (c' ⟨e, h⟩) else none
    have hcfn_L : ∀ x y₁ y₂ γ, cfn (x, y₁) = some γ → cfn (x, y₂) = some γ → y₁ = y₂ := by
      intro x y₁ y₂ γ h₁ h₂
      dsimp only [cfn] at h₁ h₂
      split_ifs at h₁ h₂ with m₁ m₂
      have heq : c' ⟨(x, y₁), m₁⟩ = c' ⟨(x, y₂), m₂⟩ := Option.some.inj (h₁.trans h₂.symm)
      by_contra hne
      exact hcL' ⟨(x, y₁), m₁⟩ ⟨(x, y₂), m₂⟩ (fun h => hne (by simpa using congrArg (fun z : E' => z.1.2) h)) rfl heq
    have hcfn_R : ∀ x₁ x₂ y γ, cfn (x₁, y) = some γ → cfn (x₂, y) = some γ → x₁ = x₂ := by
      intro x₁ x₂ y γ h₁ h₂
      dsimp only [cfn] at h₁ h₂
      split_ifs at h₁ h₂ with m₁ m₂
      have heq : c' ⟨(x₁, y), m₁⟩ = c' ⟨(x₂, y), m₂⟩ := Option.some.inj (h₁.trans h₂.symm)
      by_contra hne
      exact hcR' ⟨(x₁, y), m₁⟩ ⟨(x₂, y), m₂⟩ (fun h => hne (by simpa using congrArg (fun z : E' => z.1.1) h)) rfl heq
    have hlt_a : (E'.filter (fun e => e.1 = a)).card < D := by
      have h1 := hL a
      rw [Finset.filter_insert, if_pos rfl, Finset.card_insert_of_notMem (by simp [hab])] at h1
      omega
    have hlt_b : (E'.filter (fun e => e.2 = b)).card < D := by
      have h1 := hR b
      rw [Finset.filter_insert, if_pos rfl, Finset.card_insert_of_notMem (by simp [hab])] at h1
      omega
    -- Find a free color γ₁ at a
    have hex_γ₁ : ∃ γ₁ : Fin D, ∀ y : β, cfn (a, y) ≠ some γ₁ := by
      let usedA : Finset (Fin D) := (E'.filter (fun e => e.1 = a)).attach.image
        (fun e => c' ⟨e.1, (Finset.mem_filter.mp e.2).1⟩)
      have hcard : usedA.card < (Finset.univ : Finset (Fin D)).card := by
        rw [Finset.card_univ, Fintype.card_fin]
        exact (Finset.card_image_le.trans (by rw [Finset.card_attach])).trans_lt hlt_a
      obtain ⟨γ₁, _, hγ₁⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
      refine ⟨γ₁, fun y hy => hγ₁ ?_⟩
      dsimp only [cfn] at hy
      split_ifs at hy with hm
      rw [Finset.mem_image]
      refine ⟨⟨(a, y), Finset.mem_filter.mpr ⟨hm, rfl⟩⟩, Finset.mem_attach _ _, Option.some.inj hy⟩
    -- Find a free color γ₂ at b
    have hex_γ₂ : ∃ γ₂ : Fin D, ∀ x : α, cfn (x, b) ≠ some γ₂ := by
      let usedB : Finset (Fin D) := (E'.filter (fun e => e.2 = b)).attach.image
        (fun e => c' ⟨e.1, (Finset.mem_filter.mp e.2).1⟩)
      have hcard : usedB.card < (Finset.univ : Finset (Fin D)).card := by
        rw [Finset.card_univ, Fintype.card_fin]
        exact (Finset.card_image_le.trans (by rw [Finset.card_attach])).trans_lt hlt_b
      obtain ⟨γ₂, _, hγ₂⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
      refine ⟨γ₂, fun x hx => hγ₂ ?_⟩
      dsimp only [cfn] at hx
      split_ifs at hx with hm
      rw [Finset.mem_image]
      refine ⟨⟨(x, b), Finset.mem_filter.mpr ⟨hm, rfl⟩⟩, Finset.mem_attach _ _, Option.some.inj hx⟩
    obtain ⟨γ₁, hγ₁⟩ := hex_γ₁
    obtain ⟨γ₂, hγ₂⟩ := hex_γ₂
    -- Swap γ₁ and γ₂ on the (γ₁, γ₂)-component of Sum.inr b
    let Hstep : (α ⊕ β) → (α ⊕ β) → Prop := fun u v =>
      match u, v with
      | Sum.inl x, Sum.inr y => cfn (x, y) = some γ₁ ∨ cfn (x, y) = some γ₂
      | Sum.inr y, Sum.inl x => cfn (x, y) = some γ₁ ∨ cfn (x, y) = some γ₂
      | _, _ => False
    have hHsymm : ∀ u v, Hstep u v → Hstep v u := by
      rintro (x | y) (x' | y') h <;> exact h
    let Reach : α ⊕ β → Prop := Relation.ReflTransGen Hstep (Sum.inr b)
    have hnot_reach_a : γ₁ ≠ γ₂ → ¬ Reach (Sum.inl a) := by
      intro hne hreach
      have hex : ∃ k : ℕ, ∃ p : ℕ → α ⊕ β, p 0 = Sum.inr b ∧ p k = Sum.inl a ∧
          ∀ i < k, Hstep (p i) (p (i + 1)) := exists_walk_of_reflTransGen hreach
      let k := Nat.find hex
      obtain ⟨p, hp0, hpk, hp⟩ := Nat.find_spec hex
      have hnoback : ∀ i, i + 2 ≤ k → p (i + 2) ≠ p i := by
        intro i hi heq
        have hlt : k - 2 < k := by omega
        apply Nat.find_min hex hlt
        refine ⟨fun j => if j ≤ i then p j else p (j + 2), ?_, ?_, ?_⟩
        · simp [hp0]
        · dsimp only
          split_ifs with hji
          · have hki : k - 2 = i := by omega
            have hk2 : i + 2 = k := by omega
            rw [hki, ← heq, hk2, hpk]
          · have : k - 2 + 2 = k := by omega
            rw [this, hpk]
        · intro j hj
          by_cases h1 : j < i
          · simp [show j ≤ i by omega, show j + 1 ≤ i by omega, hp j (by omega)]
          · by_cases h2 : j = i
            · subst h2
              have hle1 : ¬ j + 1 ≤ j := by omega
              simp only [le_refl, ↓reduceIte, hle1]
              rw [← heq]
              exact hp (j + 2) (by omega)
            · have hle0 : ¬ j ≤ i := by omega
              have hle1 : ¬ j + 1 ≤ i := by omega
              simp only [hle0, hle1, ↓reduceIte]
              have : j + 1 + 2 = (j + 2) + 1 := by omega
              rw [this]
              exact hp (j + 2) (by omega)
      -- Alternating parity and color invariant along the minimal walk p
      have hinv : ∀ i ≤ k,
          (i % 2 = 0 → (∃ y, p i = Sum.inr y) ∧
            ∀ (hi : 0 < i), ∃ x y, p (i - 1) = Sum.inl x ∧ p i = Sum.inr y ∧ cfn (x, y) = some γ₂) ∧
          (i % 2 = 1 → (∃ x, p i = Sum.inl x) ∧
            ∃ x y, p (i - 1) = Sum.inr y ∧ p i = Sum.inl x ∧ cfn (x, y) = some γ₁) := by
        intro i
        induction i with
        | zero =>
          intro _
          refine ⟨fun _ => ⟨⟨b, hp0⟩, fun h0 => (Nat.lt_irrefl 0 h0).elim⟩, fun h1 => by omega⟩
        | succ i ihi =>
          intro hik
          obtain ⟨heven, hodd⟩ := ihi (by omega)
          have hstep := hp i (by omega)
          constructor
          · intro hmod
            have hodd_i : i % 2 = 1 := by omega
            obtain ⟨⟨x, hpx⟩, x₀, y₀, hpim, hpx₀, hcol_in⟩ := hodd hodd_i
            have hx_eq : x₀ = x := Sum.inl.inj (hpx₀.symm.trans hpx)
            subst x₀
            rw [hpx] at hstep
            cases hpi1 : p (i + 1) with
            | inl x' => rw [hpi1] at hstep; exact hstep.elim
            | inr y =>
              rw [hpi1] at hstep
              have hcol_out : cfn (x, y) = some γ₂ := by
                rcases hstep with h1 | h2
                · exfalso
                  have hy_eq : y = y₀ := hcfn_L x y y₀ γ₁ h1 hcol_in
                  have hback : p (i - 1 + 2) = p (i - 1) := by
                    have : i - 1 + 2 = i + 1 := by omega
                    rw [this, hpi1, hpim, hy_eq]
                  exact hnoback (i - 1) (by omega) hback
                · exact h2
              exact ⟨⟨y, rfl⟩, fun _ => ⟨x, y, by simpa using hpx, rfl, hcol_out⟩⟩
          · intro hmod
            have heven_i : i % 2 = 0 := by omega
            obtain ⟨⟨y, hpy⟩, hprev⟩ := heven heven_i
            rw [hpy] at hstep
            cases hpi1 : p (i + 1) with
            | inr y' => rw [hpi1] at hstep; exact hstep.elim
            | inl x =>
              rw [hpi1] at hstep
              have hcol_out : cfn (x, y) = some γ₁ := by
                rcases hstep with h1 | h2
                · exact h1
                · exfalso
                  rcases i with _ | i'
                  · have hyb : y = b := Sum.inr.inj (hpy.symm.trans hp0)
                    subst hyb
                    exact hγ₂ x h2
                  · obtain ⟨x₀, y₀, hpim, hpy₀, hcol_in⟩ := hprev (Nat.succ_pos i')
                    have hy_eq : y₀ = y := Sum.inr.inj (hpy₀.symm.trans hpy)
                    subst y₀
                    have hx_eq : x = x₀ := hcfn_R x x₀ y γ₂ h2 hcol_in
                    have hpim' : p i' = Sum.inl x₀ := by simpa using hpim
                    have hback : p (i' + 2) = p i' := by
                      have : i' + 2 = i' + 1 + 1 := by omega
                      rw [this, hpi1, hpim', hx_eq]
                    exact hnoback i' (by omega) hback
              exact ⟨⟨x, rfl⟩, x, y, by simpa using hpy, rfl, hcol_out⟩
      obtain ⟨heven_k, hodd_k⟩ := hinv k le_rfl
      rcases Nat.mod_two_eq_zero_or_one k with hk0 | hk1
      · obtain ⟨⟨y, hpy⟩, _⟩ := heven_k hk0
        have := hpk.symm.trans hpy; cases this
      · obtain ⟨_, x, y, _, hpx, hcol⟩ := hodd_k hk1
        have hxa : x = a := Sum.inl.inj (hpx.symm.trans hpk)
        subst hxa
        exact hγ₁ y hcol
    -- Define the swapped coloring on E' (when γ₁ = γ₂, swap is identity!)
    let swapCol : Fin D → Fin D := fun γ => if γ = γ₁ then γ₂ else if γ = γ₂ then γ₁ else γ
    have hswap_inj : Function.Injective swapCol := swapCol_inj γ₁ γ₂
    let c'' : E' → Fin D := fun e =>
      if Reach (Sum.inl e.1.1) ∧ (c' e = γ₁ ∨ c' e = γ₂) then swapCol (c' e) else c' e
    have hreach_edge : ∀ e : E', (c' e = γ₁ ∨ c' e = γ₂) →
        (Reach (Sum.inl e.1.1) ↔ Reach (Sum.inr e.1.2)) := by
      intro e hcol
      have hcfn_e : cfn e.1 = some γ₁ ∨ cfn e.1 = some γ₂ := by
        dsimp only [cfn]; rw [dif_pos e.2]; rcases hcol with h | h <;> simp [h]
      have hst : Hstep (Sum.inl e.1.1) (Sum.inr e.1.2) := hcfn_e
      exact ⟨fun h => h.tail hst, fun h => h.tail (hHsymm (Sum.inl e.1.1) (Sum.inr e.1.2) hst)⟩
    have hc''_L : ∀ e₁ e₂ : E', e₁ ≠ e₂ → e₁.1.1 = e₂.1.1 → c'' e₁ ≠ c'' e₂ := by
      intro e₁ e₂ hne heq hcol
      have hne_c := hcL' e₁ e₂ hne heq
      dsimp only [c''] at hcol
      rw [← heq] at hcol
      by_cases hr : Reach (Sum.inl e₁.1.1)
      · simp only [hr, true_and] at hcol
        have h1 : (if c' e₁ = γ₁ ∨ c' e₁ = γ₂ then swapCol (c' e₁) else c' e₁) = swapCol (c' e₁) :=
          ite_swapCol_eq γ₁ γ₂ (c' e₁)
        have h2 : (if c' e₂ = γ₁ ∨ c' e₂ = γ₂ then swapCol (c' e₂) else c' e₂) = swapCol (c' e₂) :=
          ite_swapCol_eq γ₁ γ₂ (c' e₂)
        rw [h1, h2] at hcol
        exact hne_c (hswap_inj hcol)
      · simp only [hr, false_and, ↓reduceIte] at hcol
        exact hne_c hcol
    have hc''_R : ∀ e₁ e₂ : E', e₁ ≠ e₂ → e₁.1.2 = e₂.1.2 → c'' e₁ ≠ c'' e₂ := by
      intro e₁ e₂ hne heq hcol
      have hne_c := hcR' e₁ e₂ hne heq
      have hr1 : c'' e₁ = if Reach (Sum.inr e₁.1.2) ∧ (c' e₁ = γ₁ ∨ c' e₁ = γ₂) then swapCol (c' e₁) else c' e₁ := by
        dsimp only [c'']
        by_cases h1 : c' e₁ = γ₁ ∨ c' e₁ = γ₂
        · simp [h1, hreach_edge e₁ h1]
        · simp [h1]
      have hr2 : c'' e₂ = if Reach (Sum.inr e₂.1.2) ∧ (c' e₂ = γ₁ ∨ c' e₂ = γ₂) then swapCol (c' e₂) else c' e₂ := by
        dsimp only [c'']
        by_cases h2 : c' e₂ = γ₁ ∨ c' e₂ = γ₂
        · simp [h2, hreach_edge e₂ h2]
        · simp [h2]
      rw [hr1, hr2, ← heq] at hcol
      by_cases hr : Reach (Sum.inr e₁.1.2)
      · simp only [hr, true_and] at hcol
        have h1 : (if c' e₁ = γ₁ ∨ c' e₁ = γ₂ then swapCol (c' e₁) else c' e₁) = swapCol (c' e₁) :=
          ite_swapCol_eq γ₁ γ₂ (c' e₁)
        have h2 : (if c' e₂ = γ₁ ∨ c' e₂ = γ₂ then swapCol (c' e₂) else c' e₂) = swapCol (c' e₂) :=
          ite_swapCol_eq γ₁ γ₂ (c' e₂)
        rw [h1, h2] at hcol
        exact hne_c (hswap_inj hcol)
      · simp only [hr, false_and, ↓reduceIte] at hcol
        exact hne_c hcol
    have hfree_a : ∀ e : E', e.1.1 = a → c'' e ≠ γ₁ := by
      intro e hea hcol
      dsimp only [c''] at hcol
      by_cases hne : γ₁ = γ₂
      · subst hne
        have hce : c' e = γ₁ := by
          split_ifs at hcol with h
          · exact h.2.elim id id
          · exact hcol
        have : cfn (a, e.1.2) = some γ₁ := by
          dsimp only [cfn]; rw [← hea, dif_pos e.2, hce]
        exact hγ₁ e.1.2 this
      · have hnr : ¬ Reach (Sum.inl e.1.1) := by rw [hea]; exact hnot_reach_a hne
        simp only [hnr, false_and, ↓reduceIte] at hcol
        have : cfn (a, e.1.2) = some γ₁ := by
          dsimp only [cfn]; rw [← hea, dif_pos e.2, hcol]
        exact hγ₁ e.1.2 this
    have hfree_b : ∀ e : E', e.1.2 = b → c'' e ≠ γ₁ := by
      intro e heb hcol
      have hrb : Reach (Sum.inr e.1.2) := by rw [heb]
      have hne2 : c' e ≠ γ₂ := by
        intro h2
        have : cfn (e.1.1, b) = some γ₂ := by
          dsimp only [cfn]; rw [← heb, dif_pos e.2, h2]
        exact hγ₂ e.1.1 this
      dsimp only [c''] at hcol
      by_cases h1 : c' e = γ₁
      · have hra : Reach (Sum.inl e.1.1) := (hreach_edge e (Or.inl h1)).mpr hrb
        simp only [hra, h1, true_or, and_self, ↓reduceIte, swapCol] at hcol
        exact hne2 (h1.trans hcol.symm)
      · have hnot : ¬ (c' e = γ₁ ∨ c' e = γ₂) := by tauto
        simp only [hnot, and_false, ↓reduceIte] at hcol
        exact h1 hcol
    -- Extend c'' to insert (a, b) E' by assigning γ₁ to (a, b)
    let c : ↑(insert (a, b) E') → Fin D := fun e =>
      if h : e.1 ∈ E' then c'' ⟨e.1, h⟩ else γ₁
    refine ⟨c, ?_, ?_⟩
    · intro e₁ e₂ hne heq
      dsimp only [c]
      by_cases m₁ : e₁.1 ∈ E' <;> by_cases m₂ : e₂.1 ∈ E'
      · rw [dif_pos m₁, dif_pos m₂]
        exact hc''_L ⟨e₁.1, m₁⟩ ⟨e₂.1, m₂⟩ (fun h => hne (Subtype.ext (congrArg (fun z : E' => z.1) h))) heq
      · rw [dif_pos m₁, dif_neg m₂]
        have h2ab : e₂.1 = (a, b) := (Finset.mem_insert.mp e₂.2).resolve_right m₂
        exact hfree_a ⟨e₁.1, m₁⟩ (by rw [heq, h2ab])
      · rw [dif_neg m₁, dif_pos m₂]
        have h1ab : e₁.1 = (a, b) := (Finset.mem_insert.mp e₁.2).resolve_right m₁
        exact (hfree_a ⟨e₂.1, m₂⟩ (by rw [← heq, h1ab])).symm
      · exfalso
        have h1ab : e₁.1 = (a, b) := (Finset.mem_insert.mp e₁.2).resolve_right m₁
        have h2ab : e₂.1 = (a, b) := (Finset.mem_insert.mp e₂.2).resolve_right m₂
        exact hne (Subtype.ext (h1ab.trans h2ab.symm))
    · intro e₁ e₂ hne heq
      dsimp only [c]
      by_cases m₁ : e₁.1 ∈ E' <;> by_cases m₂ : e₂.1 ∈ E'
      · rw [dif_pos m₁, dif_pos m₂]
        exact hc''_R ⟨e₁.1, m₁⟩ ⟨e₂.1, m₂⟩ (fun h => hne (Subtype.ext (congrArg (fun z : E' => z.1) h))) heq
      · rw [dif_pos m₁, dif_neg m₂]
        have h2ab : e₂.1 = (a, b) := (Finset.mem_insert.mp e₂.2).resolve_right m₂
        exact hfree_b ⟨e₁.1, m₁⟩ (by rw [heq, h2ab])
      · rw [dif_neg m₁, dif_pos m₂]
        have h1ab : e₁.1 = (a, b) := (Finset.mem_insert.mp e₁.2).resolve_right m₁
        exact (hfree_b ⟨e₂.1, m₂⟩ (by rw [← heq, h1ab])).symm
      · exfalso
        have h1ab : e₁.1 = (a, b) := (Finset.mem_insert.mp e₁.2).resolve_right m₁
        have h2ab : e₂.1 = (a, b) := (Finset.mem_insert.mp e₂.2).resolve_right m₂
        exact hne (Subtype.ext (h1ab.trans h2ab.symm))

/- ## Section 2: Greedy graph coloring -/

/-- Any finite family with maximum intersection degree at most `D` is `(D + 1)`-colorable. -/
theorem greedy_block_coloring {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (D : ℕ)
    (hdeg : ∀ a ∈ F, ((F.erase a).filter (fun b => (a ∩ b).Nonempty)).card ≤ D) :
    ∃ c : F → Fin (D + 1),
      ∀ A B : F, A ≠ B → (A.1 ∩ B.1).Nonempty → c A ≠ c B := by
  have go : ∀ S : Finset (Finset α), S ⊆ F →
      ∃ c : S → Fin (D + 1), ∀ A B : S, A ≠ B → (A.1 ∩ B.1).Nonempty → c A ≠ c B := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨fun a => (Finset.notMem_empty _ a.2).elim, fun a => (Finset.notMem_empty _ a.2).elim⟩
    | @insert a S' ha ih =>
      intro hsub
      have haF : a ∈ F := hsub (Finset.mem_insert_self a S')
      have hS'F : S' ⊆ F := (Finset.subset_insert a S').trans hsub
      obtain ⟨c', hc'⟩ := ih hS'F
      let nbrs := S'.filter (fun b => (a ∩ b).Nonempty)
      have hnbrs_sub : nbrs ⊆ (F.erase a).filter (fun b => (a ∩ b).Nonempty) := by
        intro b hb
        obtain ⟨hbS, hmeet⟩ := Finset.mem_filter.mp hb
        exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨fun h => ha (h ▸ hbS), hS'F hbS⟩, hmeet⟩
      have hnbrs_card : nbrs.card ≤ D := (Finset.card_le_card hnbrs_sub).trans (hdeg a haF)
      let used : Finset (Fin (D + 1)) := nbrs.attach.image (fun b => c' ⟨b.1, (Finset.mem_filter.mp b.2).1⟩)
      have hused_lt : used.card < (Finset.univ : Finset (Fin (D + 1))).card := by
        rw [Finset.card_univ, Fintype.card_fin]
        have : used.card ≤ nbrs.card := Finset.card_image_le.trans (by rw [Finset.card_attach])
        omega
      obtain ⟨γ, _, hγ⟩ := Finset.exists_mem_notMem_of_card_lt_card hused_lt
      let c : ↑(insert a S') → Fin (D + 1) := fun A =>
        if h : A.1 ∈ S' then c' ⟨A.1, h⟩ else γ
      refine ⟨c, fun A B hne hmeet => ?_⟩
      dsimp only [c]
      by_cases mA : A.1 ∈ S' <;> by_cases mB : B.1 ∈ S'
      · rw [dif_pos mA, dif_pos mB]
        exact hc' ⟨A.1, mA⟩ ⟨B.1, mB⟩ (fun h => hne (Subtype.ext (congrArg (fun z : S' => z.1) h))) hmeet
      · rw [dif_pos mA, dif_neg mB]
        have hBa : B.1 = a := (Finset.mem_insert.mp B.2).resolve_right mB
        have hmeet' : (a ∩ A.1).Nonempty := by
          obtain ⟨z, hz⟩ := hmeet; rw [Finset.mem_inter] at hz
          exact ⟨z, Finset.mem_inter.mpr ⟨hBa ▸ hz.2, hz.1⟩⟩
        intro hcol
        apply hγ
        rw [Finset.mem_image]
        exact ⟨⟨A.1, Finset.mem_filter.mpr ⟨mA, hmeet'⟩⟩, Finset.mem_attach _ _, hcol⟩
      · rw [dif_neg mA, dif_pos mB]
        have hAa : A.1 = a := (Finset.mem_insert.mp A.2).resolve_right mA
        have hmeet' : (a ∩ B.1).Nonempty := by
          obtain ⟨z, hz⟩ := hmeet; rw [Finset.mem_inter] at hz
          exact ⟨z, Finset.mem_inter.mpr ⟨hAa ▸ hz.1, hz.2⟩⟩
        intro hcol
        apply hγ
        rw [Finset.mem_image]
        exact ⟨⟨B.1, Finset.mem_filter.mpr ⟨mB, hmeet'⟩⟩, Finset.mem_attach _ _, hcol.symm⟩
      · exfalso
        have hAa : A.1 = a := (Finset.mem_insert.mp A.2).resolve_right mA
        have hBa : B.1 = a := (Finset.mem_insert.mp B.2).resolve_right mB
        exact hne (Subtype.ext (hAa.trans hBa.symm))
  exact go F (Finset.Subset.refl F)

/- ## Section 3: Single-big-block spaces (all blocks other than `b` have size 2) -/

lemma mod_eq_of_lt_two_mul {a b q : ℕ} (hq : 0 < q) (ha : a < 2 * q) (hb : b < 2 * q)
    (h : a % q = b % q) : a = b ∨ a = b + q ∨ b = a + q := by
  have h1 := Nat.div_add_mod a q
  have h2 := Nat.div_add_mod b q
  have hd1 : a / q ≤ 1 := Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hq).mpr (by omega))
  have hd2 : b / q ≤ 1 := Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hq).mpr (by omega))
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd1 with hda | hda <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd2 with hdb | hdb <;>
    (rw [hda] at h1; rw [hdb] at h2; omega)

lemma pair_color_even {n : ℕ} (hn : 2 ≤ n) (heven : n % 2 = 0) :
    ∃ f : Fin n → Fin n → Fin n,
      (∀ i j, f i j = f j i) ∧
      (∀ i j, i ≠ j → (f i j).val ≠ 0) ∧
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k → f i j ≠ f i k) := by
  let q := n - 1
  have hq_pos : 0 < q := by omega
  have hq_odd : q % 2 = 1 := by omega
  let f : Fin n → Fin n → Fin n := fun i j =>
    if i.val < q ∧ j.val < q then ⟨(i.val + j.val) % q + 1, by have := Nat.mod_lt (i.val + j.val) hq_pos; omega⟩
    else if i.val < q then ⟨(2 * i.val) % q + 1, by have := Nat.mod_lt (2 * i.val) hq_pos; omega⟩
    else ⟨(2 * j.val) % q + 1, by have := Nat.mod_lt (2 * j.val) hq_pos; omega⟩
  refine ⟨f, ?_, ?_, ?_⟩
  · intro i j
    dsimp only [f]
    by_cases hi : i.val < q <;> by_cases hj : j.val < q
    · simp only [hi, hj, and_self, ↓reduceIte, add_comm]
    · simp only [hi, hj, and_true, and_false, ↓reduceIte]
    · simp only [hi, hj, and_true, and_false, ↓reduceIte]
    · have : i.val = q ∧ j.val = q := by omega
      simp only [this.1, this.2]
  · intro i j _
    dsimp only [f]
    split_ifs <;> simp
  · intro i j k hij hik hjk hfeq
    have hval := congrArg Fin.val hfeq
    have hne_ij : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hne_ik : i.val ≠ k.val := fun h => hik (Fin.ext h)
    have hne_jk : j.val ≠ k.val := fun h => hjk (Fin.ext h)
    dsimp only [f] at hval
    by_cases hi : i.val < q
    · by_cases hj : j.val < q <;> by_cases hk : k.val < q
      · simp only [hi, hj, hk, and_self, ↓reduceIte] at hval
        have hmod : (i.val + j.val) % q = (i.val + k.val) % q := by omega
        have := mod_eq_of_lt_two_mul hq_pos (by omega) (by omega) hmod
        omega
      · simp only [hi, hj, hk, and_true, and_false, ↓reduceIte] at hval
        have hmod : (i.val + j.val) % q = (2 * i.val) % q := by omega
        have := mod_eq_of_lt_two_mul hq_pos (by omega) (by omega) hmod
        omega
      · simp only [hi, hj, hk, and_true, and_false, ↓reduceIte] at hval
        have hmod : (2 * i.val) % q = (i.val + k.val) % q := by omega
        have := mod_eq_of_lt_two_mul hq_pos (by omega) (by omega) hmod
        omega
      · omega
    · have hj : j.val < q := by omega
      have hk : k.val < q := by omega
      simp only [hi, false_and, ↓reduceIte] at hval
      have hmod : (2 * j.val) % q = (2 * k.val) % q := by omega
      have := mod_eq_of_lt_two_mul hq_pos (by omega) (by omega) hmod
      omega

/-- Every linear space where all blocks other than `b` have size `2` is `n`-colorable. -/
theorem color_single_big_block {n : ℕ} (L : Finset (Finset (Fin n))) (b : Finset (Fin n))
    (hb : b ∈ L)
    (hsize : ∀ a ∈ L, 2 ≤ a.card)
    (hlin : ∀ a ∈ L, ∀ c ∈ L, a ≠ c → (a ∩ c).card ≤ 1)
    (hother : ∀ a ∈ L, a ≠ b → a.card = 2) :
    ∃ c : L → Fin n, ∀ A B : L, A ≠ B → (A.1 ∩ B.1).Nonempty → c A ≠ c B := by
  have hn2 : 2 ≤ n := (hsize b hb).trans (by simpa using Finset.card_le_univ b)
  rcases Nat.mod_two_eq_zero_or_one n with heven | hodd
  · obtain ⟨f, hsymm, hnz, hprop⟩ := pair_color_even hn2 heven
    let c : L → Fin n := fun A =>
      if hA : A.1 = b then ⟨0, by omega⟩
      else
        let h2 := hother A.1 A.2 hA
        let ex := Finset.card_eq_two.mp h2
        f ex.choose ex.choose_spec.choose
    have hc_pair : ∀ (A : L) (x y : Fin n), A.1 ≠ b → x ≠ y → A.1 = {x, y} → c A = f x y := by
      intro A x y hAb hxy hAeq
      dsimp only [c]
      rw [dif_neg hAb]
      set ex := Finset.card_eq_two.mp (hother A.1 A.2 hAb)
      obtain ⟨hne, heq⟩ := ex.choose_spec.choose_spec
      have hpair : ({ex.choose, ex.choose_spec.choose} : Finset (Fin n)) = {x, y} := heq.symm.trans hAeq
      have hm1 : ex.choose ∈ ({x, y} : Finset (Fin n)) := hpair ▸ by simp
      have hm2 : ex.choose_spec.choose ∈ ({x, y} : Finset (Fin n)) := hpair ▸ by simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm1 hm2
      rcases hm1 with h1 | h1 <;> rcases hm2 with h2 | h2
      · exact (hne (h1.trans h2.symm)).elim
      · exact congrArg₂ f h1 h2
      · exact (congrArg₂ f h1 h2).trans (hsymm _ _)
      · exact (hne (h1.trans h2.symm)).elim
    refine ⟨c, fun A B hne hmeet => ?_⟩
    by_cases hAb : A.1 = b
    · have hBb : B.1 ≠ b := fun h => hne (Subtype.ext (hAb.trans h.symm))
      obtain ⟨x, y, hxy, hBeq⟩ := Finset.card_eq_two.mp (hother B.1 B.2 hBb)
      rw [show c A = ⟨0, by omega⟩ by dsimp only [c]; rw [dif_pos hAb], hc_pair B x y hBb hxy hBeq]
      intro h0
      exact hnz x y hxy (congrArg Fin.val h0).symm
    · by_cases hBb : B.1 = b
      · obtain ⟨x, y, hxy, hAeq⟩ := Finset.card_eq_two.mp (hother A.1 A.2 hAb)
        rw [show c B = ⟨0, by omega⟩ by dsimp only [c]; rw [dif_pos hBb], hc_pair A x y hAb hxy hAeq]
        intro h0
        exact hnz x y hxy (congrArg Fin.val h0)
      · obtain ⟨x, hx⟩ := hmeet
        obtain ⟨hxA, hxB⟩ := Finset.mem_inter.mp hx
        obtain ⟨y, hyA, hxy, hAeq⟩ : ∃ y, y ∈ A.1 ∧ x ≠ y ∧ A.1 = {x, y} := by
          obtain ⟨u, v, huv, heq⟩ := Finset.card_eq_two.mp (hother A.1 A.2 hAb)
          have hxu : x = u ∨ x = v := by simpa [heq] using hxA
          rcases hxu with rfl | rfl
          · exact ⟨v, by simp [heq], huv, heq⟩
          · exact ⟨u, by simp [heq], huv.symm, by rw [heq, Finset.pair_comm]⟩
        obtain ⟨z, hzB, hxz, hBeq⟩ : ∃ z, z ∈ B.1 ∧ x ≠ z ∧ B.1 = {x, z} := by
          obtain ⟨u, v, huv, heq⟩ := Finset.card_eq_two.mp (hother B.1 B.2 hBb)
          have hxu : x = u ∨ x = v := by simpa [heq] using hxB
          rcases hxu with rfl | rfl
          · exact ⟨v, by simp [heq], huv, heq⟩
          · exact ⟨u, by simp [heq], huv.symm, by rw [heq, Finset.pair_comm]⟩
        have hyz : y ≠ z := fun h => hne (Subtype.ext (by rw [hAeq, hBeq, h]))
        rw [hc_pair A x y hAb hxy hAeq, hc_pair B x z hBb hxz hBeq]
        exact hprop x y z hxy hxz hyz
  · -- Odd n: embed b onto a negation-closed subset B₀ ⊆ Fin n and color {x, y} by (σ x + σ y) % n
    let k := b.card
    have hk_le : k ≤ n := by simpa [k] using Finset.card_le_univ b
    let half := k / 2
    have h2half : 2 * half < n := by omega
    let pairs : Finset (Fin n) := (Finset.Icc 1 half).biUnion
      (fun r => if hr : r < n ∧ n - r < n then {⟨r, hr.1⟩, ⟨n - r, hr.2⟩} else ∅)
    let B₀ : Finset (Fin n) := if k % 2 = 1 then insert ⟨0, by omega⟩ pairs else pairs
    have hmem_pairs : ∀ z : Fin n, z ∈ pairs ↔ (1 ≤ z.val ∧ z.val ≤ half) ∨ (n - half ≤ z.val ∧ z.val < n) := by
      intro z
      simp only [pairs, Finset.mem_biUnion, Finset.mem_Icc]
      constructor
      · rintro ⟨r, ⟨hr1, hrh⟩, hz⟩
        have hrlt : r < n ∧ n - r < n := ⟨by omega, by omega⟩
        rw [dif_pos hrlt, Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact Or.inl ⟨hr1, hrh⟩
        · exact Or.inr ⟨by dsimp only; omega, by dsimp only; omega⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · refine ⟨z.val, ⟨h1, h2⟩, ?_⟩
          rw [dif_pos ⟨by omega, by omega⟩]; simp
        · refine ⟨n - z.val, ⟨by omega, by omega⟩, ?_⟩
          have hlt : n - z.val < n ∧ n - (n - z.val) < n := ⟨by omega, by omega⟩
          rw [dif_pos hlt]
          have hval : n - (n - z.val) = z.val := by omega
          simp [Fin.ext_iff, hval]
    have h0_npairs : (⟨0, by omega⟩ : Fin n) ∉ pairs := by
      rw [hmem_pairs]; dsimp only; omega
    have hpairs_card : pairs.card = 2 * half := by
      have hdisj : ((Finset.Icc 1 half) : Set ℕ).PairwiseDisjoint
          (fun r => if hr : r < n ∧ n - r < n then ({⟨r, hr.1⟩, ⟨n - r, hr.2⟩} : Finset (Fin n)) else ∅) := by
        intro r₁ hr₁ r₂ hr₂ hne
        simp only [Finset.mem_coe, Finset.mem_Icc] at hr₁ hr₂
        have hlt1 : r₁ < n ∧ n - r₁ < n := ⟨by omega, by omega⟩
        have hlt2 : r₂ < n ∧ n - r₂ < n := ⟨by omega, by omega⟩
        dsimp only [Function.onFun]
        rw [dif_pos hlt1, dif_pos hlt2, Finset.disjoint_left]
        intro z hz₁ hz₂
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz₁ hz₂
        rcases hz₁ with rfl | rfl <;> rcases hz₂ with h | h <;> have hv := congrArg Fin.val h <;> dsimp only at hv <;> omega
      rw [Finset.card_biUnion hdisj]
      have hterm : ∀ r ∈ Finset.Icc 1 half,
          (if hr : r < n ∧ n - r < n then ({⟨r, hr.1⟩, ⟨n - r, hr.2⟩} : Finset (Fin n)) else ∅).card = 2 := by
        intro r hr
        simp only [Finset.mem_Icc] at hr
        have hlt : r < n ∧ n - r < n := ⟨by omega, by omega⟩
        rw [dif_pos hlt]
        exact Finset.card_pair (fun h => by have hv := congrArg Fin.val h; dsimp only at hv; omega)
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Icc, smul_eq_mul]
      omega
    have hB₀_card : B₀.card = b.card := by
      dsimp only [B₀]
      split_ifs with h1
      · rw [Finset.card_insert_of_notMem h0_npairs, hpairs_card]; omega
      · rw [hpairs_card]; omega
    have hB₀_neg : ∀ x y : Fin n, x ≠ y → (x.val + y.val) % n = 0 → (x ∈ B₀ ↔ y ∈ B₀) := by
      intro x y hxy hsum
      have hne_val : x.val ≠ y.val := fun h => hxy (Fin.ext h)
      have hxy_n : x.val + y.val = n := by
        have hmod : (x.val + y.val) % n = 0 % n := by simpa using hsum
        have := mod_eq_of_lt_two_mul (by omega : 0 < n) (by omega) (by omega) hmod
        omega
      have hx0 : x.val ≠ 0 := by omega
      have hy0 : y.val ≠ 0 := by omega
      have hmem : ∀ z : Fin n, z.val ≠ 0 → (z ∈ B₀ ↔ z ∈ pairs) := by
        intro z hz0
        dsimp only [B₀]
        split_ifs
        · simp [Finset.mem_insert, Fin.ext_iff, hz0]
        · rfl
      rw [hmem x hx0, hmem y hy0, hmem_pairs, hmem_pairs]
      omega
    -- Build bijection σ : Fin n ≃ Fin n sending b onto B₀
    have hcompl_card : (Finset.univ \ b).card = (Finset.univ \ B₀).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_sdiff_of_subset (Finset.subset_univ _), hB₀_card]
    let e₁ : {x : Fin n // x ∈ b} ≃ {x : Fin n // x ∈ B₀} :=
      Fintype.equivOfCardEq (by simp only [Fintype.card_coe]; exact hB₀_card.symm)
    let e₂ : {x : Fin n // x ∈ Finset.univ \ b} ≃ {x : Fin n // x ∈ Finset.univ \ B₀} :=
      Fintype.equivOfCardEq (by simp only [Fintype.card_coe]; exact hcompl_card)
    let σfun : Fin n → Fin n := fun x =>
      if h : x ∈ b then (e₁ ⟨x, h⟩).1 else (e₂ ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩⟩).1
    have hσ_mem : ∀ x, σfun x ∈ B₀ ↔ x ∈ b := by
      intro x
      dsimp only [σfun]
      split_ifs with h
      · exact ⟨fun _ => h, fun _ => (e₁ ⟨x, h⟩).2⟩
      · have hm := (Finset.mem_sdiff.mp (e₂ ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩⟩).2).2
        exact ⟨fun hB => (hm hB).elim, fun hb' => (h hb').elim⟩
    have hσ_inj : Function.Injective σfun := by
      intro x y hxy
      by_cases hx : x ∈ b <;> by_cases hy : y ∈ b
      · dsimp only [σfun] at hxy; rw [dif_pos hx, dif_pos hy] at hxy
        exact congrArg Subtype.val (e₁.injective (Subtype.ext hxy))
      · exfalso; have := (hσ_mem x).mpr hx; rw [hxy, hσ_mem] at this; exact hy this
      · exfalso; have := (hσ_mem y).mpr hy; rw [← hxy, hσ_mem] at this; exact hx this
      · dsimp only [σfun] at hxy; rw [dif_neg hx, dif_neg hy] at hxy
        exact congrArg Subtype.val (e₂.injective (Subtype.ext hxy))
    let f : Fin n → Fin n → Fin n := fun x y =>
      ⟨((σfun x).val + (σfun y).val) % n, Nat.mod_lt _ (by omega)⟩
    let c : L → Fin n := fun A =>
      if hA : A.1 = b then ⟨0, by omega⟩
      else
        let ex := Finset.card_eq_two.mp (hother A.1 A.2 hA)
        f ex.choose ex.choose_spec.choose
    have hc_pair : ∀ (A : L) (x y : Fin n), A.1 ≠ b → x ≠ y → A.1 = {x, y} → c A = f x y := by
      intro A x y hAb hxy hAeq
      dsimp only [c]
      rw [dif_neg hAb]
      set ex := Finset.card_eq_two.mp (hother A.1 A.2 hAb)
      obtain ⟨hne, heq⟩ := ex.choose_spec.choose_spec
      have hpair : ({ex.choose, ex.choose_spec.choose} : Finset (Fin n)) = {x, y} := heq.symm.trans hAeq
      have hm1 : ex.choose ∈ ({x, y} : Finset (Fin n)) := hpair ▸ by simp
      have hm2 : ex.choose_spec.choose ∈ ({x, y} : Finset (Fin n)) := hpair ▸ by simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm1 hm2
      rcases hm1 with h1 | h1 <;> rcases hm2 with h2 | h2
      · exact (hne (h1.trans h2.symm)).elim
      · exact congrArg₂ f h1 h2
      · exact (congrArg₂ f h1 h2).trans (Fin.ext (by dsimp only [f]; rw [add_comm]))
      · exact (hne (h1.trans h2.symm)).elim
    refine ⟨c, fun A B hne hmeet => ?_⟩
    by_cases hAb : A.1 = b
    · have hBb : B.1 ≠ b := fun h => hne (Subtype.ext (hAb.trans h.symm))
      obtain ⟨x, y, hxy, hBeq⟩ := Finset.card_eq_two.mp (hother B.1 B.2 hBb)
      rw [show c A = ⟨0, by omega⟩ by dsimp only [c]; rw [dif_pos hAb], hc_pair B x y hBb hxy hBeq]
      intro h0
      have hmod : ((σfun x).val + (σfun y).val) % n = 0 := (congrArg Fin.val h0).symm
      have hiff : x ∈ b ↔ y ∈ b := by
        rw [← hσ_mem x, ← hσ_mem y]
        exact hB₀_neg (σfun x) (σfun y) (fun h => hxy (hσ_inj h)) hmod
      obtain ⟨z, hz⟩ := hmeet
      obtain ⟨hzA, hzB⟩ := Finset.mem_inter.mp hz
      rw [hAb] at hzA
      rw [hBeq, Finset.mem_insert, Finset.mem_singleton] at hzB
      have hboth : x ∈ b ∧ y ∈ b := by
        rcases hzB with rfl | rfl
        · exact ⟨hzA, hiff.mp hzA⟩
        · exact ⟨hiff.mpr hzA, hzA⟩
      have hsub : B.1 ⊆ B.1 ∩ b := by
        intro w hw; rw [hBeq, Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl <;> exact Finset.mem_inter.mpr ⟨by simp [hBeq], by tauto⟩
      have h2le : 2 ≤ (B.1 ∩ b).card := by
        rw [← hother B.1 B.2 hBb]; exact Finset.card_le_card hsub
      have hle1 := hlin B.1 B.2 b hb hBb
      omega
    · by_cases hBb : B.1 = b
      · obtain ⟨x, y, hxy, hAeq⟩ := Finset.card_eq_two.mp (hother A.1 A.2 hAb)
        rw [show c B = ⟨0, by omega⟩ by dsimp only [c]; rw [dif_pos hBb], hc_pair A x y hAb hxy hAeq]
        intro h0
        have hmod : ((σfun x).val + (σfun y).val) % n = 0 := congrArg Fin.val h0
        have hiff : x ∈ b ↔ y ∈ b := by
          rw [← hσ_mem x, ← hσ_mem y]
          exact hB₀_neg (σfun x) (σfun y) (fun h => hxy (hσ_inj h)) hmod
        obtain ⟨z, hz⟩ := hmeet
        obtain ⟨hzA, hzB⟩ := Finset.mem_inter.mp hz
        rw [hBb] at hzB
        rw [hAeq, Finset.mem_insert, Finset.mem_singleton] at hzA
        have hboth : x ∈ b ∧ y ∈ b := by
          rcases hzA with rfl | rfl
          · exact ⟨hzB, hiff.mp hzB⟩
          · exact ⟨hiff.mpr hzB, hzB⟩
        have hsub : A.1 ⊆ A.1 ∩ b := by
          intro w hw; rw [hAeq, Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl <;> exact Finset.mem_inter.mpr ⟨by simp [hAeq], by tauto⟩
        have h2le : 2 ≤ (A.1 ∩ b).card := by
          rw [← hother A.1 A.2 hAb]; exact Finset.card_le_card hsub
        have hle1 := hlin A.1 A.2 b hb hAb
        omega
      · obtain ⟨x, hx⟩ := hmeet
        obtain ⟨hxA, hxB⟩ := Finset.mem_inter.mp hx
        obtain ⟨y, _, hxy, hAeq⟩ : ∃ y, y ∈ A.1 ∧ x ≠ y ∧ A.1 = {x, y} := by
          obtain ⟨u, v, huv, heq⟩ := Finset.card_eq_two.mp (hother A.1 A.2 hAb)
          have hxu : x = u ∨ x = v := by simpa [heq] using hxA
          rcases hxu with rfl | rfl
          · exact ⟨v, by simp [heq], huv, heq⟩
          · exact ⟨u, by simp [heq], huv.symm, by rw [heq, Finset.pair_comm]⟩
        obtain ⟨z, _, hxz, hBeq⟩ : ∃ z, z ∈ B.1 ∧ x ≠ z ∧ B.1 = {x, z} := by
          obtain ⟨u, v, huv, heq⟩ := Finset.card_eq_two.mp (hother B.1 B.2 hBb)
          have hxu : x = u ∨ x = v := by simpa [heq] using hxB
          rcases hxu with rfl | rfl
          · exact ⟨v, by simp [heq], huv, heq⟩
          · exact ⟨u, by simp [heq], huv.symm, by rw [heq, Finset.pair_comm]⟩
        have hyz : y ≠ z := fun h => hne (Subtype.ext (by rw [hAeq, hBeq, h]))
        rw [hc_pair A x y hAb hxy hAeq, hc_pair B x z hBb hxz hBeq]
        intro hcol
        have hval := congrArg Fin.val hcol
        dsimp only [f] at hval
        have := mod_eq_of_lt_two_mul (by omega : 0 < n) (by omega) (by omega) hval
        have hsyz : (σfun y).val = (σfun z).val := by omega
        exact hyz (hσ_inj (Fin.ext hsyz))

/- ## Section 4: General small-outside coloring theorem via matching extension + König -/

/-- General small-outside coloring theorem:
Given a complete linear space `(Fin n, L)` with a block `b ∈ L`, let `U = univ \ b` and
`L_U = {a ∈ L \ {b} : 2 ≤ |a ∩ U|}`. If `I₀ ⊆ L_U` is a pairwise-disjoint subfamily disjoint
from `b`, `L_U \ I₀` admits a proper `k`-coloring, and `k + 1 ≤ |b|`, then `L` is `n`-colorable. -/
theorem color_of_small_outside {n k : ℕ} (L : Finset (Finset (Fin n))) (b : Finset (Fin n))
    (hb : b ∈ L)
    (hsize : ∀ a ∈ L, 2 ≤ a.card)
    (hlin : ∀ a ∈ L, ∀ c ∈ L, a ≠ c → (a ∩ c).card ≤ 1)
    (hcov : ∀ i j : Fin n, i ≠ j → ∃ e ∈ L, i ∈ e ∧ j ∈ e)
    (I₀ : Finset (Finset (Fin n)))
    (_hI₀_sub : I₀ ⊆ (L.erase b).filter (fun a => 2 ≤ (a ∩ (Finset.univ \ b)).card))
    (hI₀_disj_b : ∀ a ∈ I₀, Disjoint a b)
    (hI₀_pw : ∀ a₁ ∈ I₀, ∀ a₂ ∈ I₀, a₁ ≠ a₂ → Disjoint a₁ a₂)
    (hcU : ∃ cU : ↑(((L.erase b).filter (fun a => 2 ≤ (a ∩ (Finset.univ \ b)).card)) \ I₀) → Fin k,
      ∀ A B, A ≠ B → (A.1 ∩ B.1).Nonempty → cU A ≠ cU B)
    (hbk : k + 1 ≤ b.card) :
    ∃ c : L → Fin n, ∀ A B : L, A ≠ B → (A.1 ∩ B.1).Nonempty → c A ≠ c B := by
  let U : Finset (Fin n) := Finset.univ \ b
  let u : ℕ := U.card
  let LU : Finset (Finset (Fin n)) := (L.erase b).filter (fun a => 2 ≤ (a ∩ U).card)
  let LU' : Finset (Finset (Fin n)) := LU \ I₀
  obtain ⟨cU, hcU_prop⟩ := hcU
  have hbu : b.card + u = n := by
    have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ b)
    rw [Finset.card_univ, Fintype.card_fin] at this
    dsimp only [U, u]; omega
  have hkn : k + 1 ≤ n := by omega
  let F : ℕ := b.card + u - 1 - k
  have huF : u ≤ F := by omega
  have h1kF : 1 + k + F = n := by omega
  -- Bipartite 2-line graph G between b and U
  let G : Finset (Fin n × Fin n) := (b ×ˢ U).filter (fun p => ({p.1, p.2} : Finset (Fin n)) ∈ L)
  have hG_mem : ∀ p, p ∈ G ↔ p.1 ∈ b ∧ p.2 ∈ U ∧ ({p.1, p.2} : Finset (Fin n)) ∈ L := by
    intro p; simp [G, Finset.mem_product, and_assoc]
  have hbu_disj : Disjoint b U := Finset.disjoint_sdiff
  have hne_of_bU : ∀ x ∈ b, ∀ y ∈ U, x ≠ y := fun x hx y hy h =>
    Finset.disjoint_left.mp hbu_disj hx (h ▸ hy)
  -- Classification of lines in L \ ({b} ∪ LU) as unique pairs in G
  have hclass : ∀ a ∈ L, a ≠ b → a ∉ LU → ∃ x ∈ b, ∃ y ∈ U, a = {x, y} := by
    intro a ha hab haLU
    have hlt2 : (a ∩ U).card ≤ 1 := by
      have : ¬ 2 ≤ (a ∩ U).card := fun h2 =>
        haLU (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hab, ha⟩, h2⟩)
      omega
    have hle1b : (a ∩ b).card ≤ 1 := hlin a ha b hb hab
    have hpart : (a ∩ b).card + (a ∩ U).card = a.card := by
      have hunion : (a ∩ b) ∪ (a ∩ U) = a := by
        ext z; simp only [Finset.mem_union, Finset.mem_inter, U, Finset.mem_sdiff, Finset.mem_univ, true_and]
        by_cases hzb : z ∈ b <;> tauto
      have hdisj : Disjoint (a ∩ b) (a ∩ U) := Finset.disjoint_left.mpr fun z h1 h2 =>
        Finset.disjoint_left.mp hbu_disj (Finset.mem_inter.mp h1).2 (Finset.mem_inter.mp h2).2
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    have ha2 := hsize a ha
    have hcb1 : (a ∩ b).card = 1 := by omega
    have hcu1 : (a ∩ U).card = 1 := by omega
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcb1
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hcu1
    have hxb : x ∈ b := (Finset.mem_inter.mp (hx ▸ Finset.mem_singleton_self x)).2
    have hyU : y ∈ U := (Finset.mem_inter.mp (hy ▸ Finset.mem_singleton_self y)).2
    refine ⟨x, hxb, y, hyU, ?_⟩
    ext z
    have hunion : z ∈ a ↔ z ∈ a ∩ b ∨ z ∈ a ∩ U := by
      simp only [Finset.mem_inter, U, Finset.mem_sdiff, Finset.mem_univ, true_and]
      by_cases hzb : z ∈ b <;> tauto
    rw [hunion, hx, hy]; simp
  -- Degree of x ∈ b in G is at most u ≤ F
  have hG_deg_x : ∀ x : Fin n, (G.filter (fun p => p.1 = x)).card ≤ u := by
    intro x
    calc (G.filter (fun p => p.1 = x)).card
        = ((G.filter (fun p => p.1 = x)).image Prod.snd).card := by
          rw [Finset.card_image_of_injOn]
          intro p₁ hp₁ p₂ hp₂ heq
          have h1 := (Finset.mem_filter.mp hp₁).2
          have h2 := (Finset.mem_filter.mp hp₂).2
          exact Prod.ext (h1.trans h2.symm) heq
      _ ≤ U.card := Finset.card_le_card (fun y hy => by
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
          exact (hG_mem p).mp (Finset.mem_filter.mp hp).1 |>.2.1)
  -- For each y ∈ U, count lines in LU' hitting y and b (T_y) and lines inside U (S_y)
  let Ty : Fin n → Finset (Finset (Fin n)) := fun y => LU'.filter (fun a => y ∈ a ∧ (a ∩ b).Nonempty)
  let Sy : Fin n → Finset (Finset (Fin n)) := fun y => LU'.filter (fun a => y ∈ a ∧ Disjoint a b)
  have hTy_add_Sy : ∀ y ∈ U, (Ty y).card + (Sy y).card ≤ u - 1 := by
    intro y hyU
    have hdisj_TS : Disjoint (Ty y) (Sy y) := Finset.disjoint_left.mpr fun a h1 h2 =>
      Finset.not_disjoint_iff_nonempty_inter.mpr (Finset.mem_filter.mp h1).2.2 (Finset.mem_filter.mp h2).2.2
    rw [← Finset.card_union_of_disjoint hdisj_TS]
    -- Every a ∈ Ty y ∪ Sy y contains a point of U.erase y, pairwise disjointly
    have hex_pt : ∀ a ∈ Ty y ∪ Sy y, ∃ w ∈ U.erase y, w ∈ a := by
      intro a ha
      have haLU' : a ∈ LU' ∧ y ∈ a := by
        rcases Finset.mem_union.mp ha with h | h <;> exact ⟨(Finset.mem_filter.mp h).1, (Finset.mem_filter.mp h).2.1⟩
      have h2 : 2 ≤ (a ∩ U).card := (Finset.mem_filter.mp (Finset.mem_sdiff.mp haLU'.1).1).2
      have hy_in : y ∈ a ∩ U := Finset.mem_inter.mpr ⟨haLU'.2, hyU⟩
      have hpos : 0 < ((a ∩ U).erase y).card := by rw [Finset.card_erase_of_mem hy_in]; omega
      obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
      obtain ⟨hwy, hw_in⟩ := Finset.mem_erase.mp hw
      obtain ⟨hwa, hwU⟩ := Finset.mem_inter.mp hw_in
      exact ⟨w, Finset.mem_erase.mpr ⟨hwy, hwU⟩, hwa⟩
    let pick : Finset (Fin n) → Fin n := fun a =>
      if h : a ∈ Ty y ∪ Sy y then (hex_pt a h).choose else y
    have hinj : Set.InjOn pick ((Ty y ∪ Sy y : Finset _) : Set _) := by
      intro a₁ h₁ a₂ h₂ heq
      have h₁' : a₁ ∈ Ty y ∪ Sy y := Finset.mem_coe.mp h₁
      have h₂' : a₂ ∈ Ty y ∪ Sy y := Finset.mem_coe.mp h₂
      by_contra hne
      dsimp only [pick] at heq
      rw [dif_pos h₁', dif_pos h₂'] at heq
      set w := (hex_pt a₁ h₁').choose
      have hw1 := (hex_pt a₁ h₁').choose_spec
      have hw2 := (hex_pt a₂ h₂').choose_spec
      have hwa1 : w ∈ a₁ := hw1.2
      have hwa2 : w ∈ a₂ := heq ▸ hw2.2
      have hwy : w ≠ y := (Finset.mem_erase.mp hw1.1).1
      have hy1 : y ∈ a₁ := by rcases Finset.mem_union.mp h₁' with h | h <;> exact (Finset.mem_filter.mp h).2.1
      have hy2 : y ∈ a₂ := by rcases Finset.mem_union.mp h₂' with h | h <;> exact (Finset.mem_filter.mp h).2.1
      have ha1L : a₁ ∈ L := by
        rcases Finset.mem_union.mp h₁' with h | h <;>
          exact (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp h).1).1).1).2
      have ha2L : a₂ ∈ L := by
        rcases Finset.mem_union.mp h₂' with h | h <;>
          exact (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp h).1).1).1).2
      have hsub : ({w, y} : Finset (Fin n)) ⊆ a₁ ∩ a₂ := by
        intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> exact Finset.mem_inter.mpr (by tauto)
      have h2le : 2 ≤ (a₁ ∩ a₂).card := (Finset.card_pair hwy).symm ▸ Finset.card_le_card hsub
      have hle1 := hlin a₁ ha1L a₂ ha2L hne
      omega
    calc (Ty y ∪ Sy y).card = ((Ty y ∪ Sy y).image pick).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (U.erase y).card := Finset.card_le_card (fun w hw => by
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
          dsimp only [pick]; rw [dif_pos ha]; exact (hex_pt a ha).choose_spec.1)
      _ = u - 1 := Finset.card_erase_of_mem hyU
  -- Exact count of G-edges at y ∈ U: (G.filter (·.2 = y)).card + (Ty y).card = b.card
  have hG_deg_y : ∀ y ∈ U, (G.filter (fun p => p.2 = y)).card + (Ty y).card = b.card := by
    intro y hyU
    let badX := b.filter (fun x => (x, y) ∉ G)
    let goodX := b.filter (fun x => (x, y) ∈ G)
    have hpart := Finset.card_filter_add_card_filter_not (s := b) (fun x => (x, y) ∈ G)
    have hgood_eq : goodX.card = (G.filter (fun p => p.2 = y)).card := by
      rw [← Finset.card_image_of_injOn (f := fun x => (x, y)) (fun _ _ _ _ h => (Prod.mk.inj h).1)]
      congr 1; ext ⟨x, y'⟩
      simp only [goodX, Finset.mem_image, Finset.mem_filter, hG_mem]
      constructor
      · rintro ⟨x', ⟨hx', _, _, hL⟩, hpair⟩
        rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
        exact ⟨⟨hx', hyU, hL⟩, rfl⟩
      · rintro ⟨⟨hx', hy', hL⟩, rfl⟩
        exact ⟨x, ⟨hx', hx', hy', hL⟩, rfl⟩
    -- Bijection between badX and Ty y
    have hbad_eq : badX.card = (Ty y).card := by
      have hex_line : ∀ x ∈ badX, ∃ a ∈ Ty y, x ∈ a := by
        intro x hx
        have hxb : x ∈ b := (Finset.mem_filter.mp hx).1
        have hnotG : (x, y) ∉ G := (Finset.mem_filter.mp hx).2
        have hxy : x ≠ y := hne_of_bU x hxb y hyU
        obtain ⟨e, heL, hxe, hye⟩ := hcov x y hxy
        have heb : e ≠ b := fun h => Finset.disjoint_left.mp hbu_disj (h ▸ hye) hyU
        have heLU : e ∈ LU := by
          by_contra hnotLU
          obtain ⟨x', hx'b, y', hy'U, heq⟩ := hclass e heL heb hnotLU
          have hxx' : x = x' := by
            have : x ∈ ({x', y'} : Finset (Fin n)) := heq ▸ hxe
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            exact this.resolve_right (hne_of_bU x hxb y' hy'U)
          have hyy' : y = y' := by
            have : y ∈ ({x', y'} : Finset (Fin n)) := heq ▸ hye
            simp only [Finset.mem_insert, Finset.mem_singleton] at this
            exact this.resolve_left (hne_of_bU x' hx'b y hyU).symm
          exact hnotG ((hG_mem (x, y)).mpr ⟨hxb, hyU, by rwa [hxx', hyy', ← heq]⟩)
        have he_nI0 : e ∉ I₀ := fun hI0 => Finset.disjoint_left.mp (hI₀_disj_b e hI0) hxe hxb
        refine ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨heLU, he_nI0⟩, hye, ⟨x, Finset.mem_inter.mpr ⟨hxe, hxb⟩⟩⟩, hxe⟩
      let toLine : Fin n → Finset (Fin n) := fun x => if h : x ∈ badX then (hex_line x h).choose else ∅
      apply Finset.card_bij (fun x _ => toLine x)
      · intro x hx
        dsimp only [toLine]; rw [dif_pos hx]; exact (hex_line x hx).choose_spec.1
      · intro x₁ hx₁ x₂ hx₂ heq
        dsimp only [toLine] at heq; rw [dif_pos hx₁, dif_pos hx₂] at heq
        set a := (hex_line x₁ hx₁).choose
        have ha1 := (hex_line x₁ hx₁).choose_spec
        have ha2 := (hex_line x₂ hx₂).choose_spec
        have hx1a : x₁ ∈ a := ha1.2
        have hx2a : x₂ ∈ a := heq ▸ ha2.2
        have hx1b : x₁ ∈ b := (Finset.mem_filter.mp hx₁).1
        have hx2b : x₂ ∈ b := (Finset.mem_filter.mp hx₂).1
        have haL : a ∈ L := (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp ha1.1).1).1).1).2
        have hab : a ≠ b := (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp ha1.1).1).1).1).1
        by_contra hne
        have hsub : ({x₁, x₂} : Finset (Fin n)) ⊆ a ∩ b := by
          intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> exact Finset.mem_inter.mpr (by tauto)
        have h2le : 2 ≤ (a ∩ b).card := (Finset.card_pair hne).symm ▸ Finset.card_le_card hsub
        have hle1 := hlin a haL b hb hab
        omega
      · intro a ha
        obtain ⟨haLU', hya, ⟨x, hxab⟩⟩ := Finset.mem_filter.mp ha
        obtain ⟨hxa, hxb⟩ := Finset.mem_inter.mp hxab
        have hx_bad : x ∈ badX := by
          refine Finset.mem_filter.mpr ⟨hxb, fun hxG => ?_⟩
          have hpairL : ({x, y} : Finset (Fin n)) ∈ L := ((hG_mem (x, y)).mp hxG).2.2
          have haL : a ∈ L := (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp haLU').1).1).2
          have ha_card : 3 ≤ a.card := by
            have h2 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp haLU').1).2
            have hx_nU : x ∉ a ∩ U := fun hxU => Finset.disjoint_left.mp hbu_disj hxb (Finset.mem_inter.mp hxU).2
            have hsub : insert x (a ∩ U) ⊆ a := Finset.insert_subset hxa Finset.inter_subset_left
            have := Finset.card_le_card hsub
            rw [Finset.card_insert_of_notMem hx_nU] at this
            omega
          have hne : a ≠ {x, y} := fun h => by rw [h, Finset.card_pair (hne_of_bU x hxb y hyU)] at ha_card; omega
          have hsub : ({x, y} : Finset (Fin n)) ⊆ a ∩ {x, y} := by
            intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl <;> exact Finset.mem_inter.mpr (by simp [hxa, hya])
          have h2le : 2 ≤ (a ∩ {x, y}).card := (Finset.card_pair (hne_of_bU x hxb y hyU)).symm ▸ Finset.card_le_card hsub
          have hle1 := hlin a haL {x, y} hpairL hne
          omega
        refine ⟨x, hx_bad, ?_⟩
        dsimp only [toLine]; rw [dif_pos hx_bad]
        set a' := (hex_line x hx_bad).choose
        have ha'1 := (hex_line x hx_bad).choose_spec
        have hya' : y ∈ a' := (Finset.mem_filter.mp ha'1.1).2.1
        have hxa' : x ∈ a' := ha'1.2
        have ha'L : a' ∈ L := (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp ha'1.1).1).1).1).2
        have haL : a ∈ L := (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp haLU').1).1).2
        by_contra hne
        have hsub : ({x, y} : Finset (Fin n)) ⊆ a' ∩ a := by
          intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> exact Finset.mem_inter.mpr (by tauto)
        have h2le : 2 ≤ (a' ∩ a).card := (Finset.card_pair (hne_of_bU x hxb y hyU)).symm ▸ Finset.card_le_card hsub
        have hle1 := hlin a' ha'L a haL hne
        omega
    change goodX.card + badX.card = b.card at hpart
    omega
  -- Color classes of cU on LU'
  let classC : Fin k → Finset (Finset (Fin n)) := fun c =>
    LU'.attach.filter (fun A => cU A = c) |>.image Subtype.val
  let Ucov : Fin k → Finset (Fin n) := fun c => (classC c).biUnion (fun a => a ∩ U)
  let Bcov : Fin k → Finset (Fin n) := fun c => (classC c).biUnion (fun a => a ∩ b)
  have hBcov_le : ∀ c : Fin k, (Bcov c).card ≤ (classC c).card := by
    intro c
    calc (Bcov c).card ≤ ∑ a ∈ classC c, (a ∩ b).card := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ classC c, 1 := Finset.sum_le_sum fun a ha => by
          obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp ha
          have hmem := (Finset.mem_filter.mp (Finset.mem_sdiff.mp A.2).1).1
          exact hlin A.1 (Finset.mem_erase.mp hmem).2 b hb (Finset.mem_erase.mp hmem).1
      _ = (classC c).card := by simp
  have hUcov_ge : ∀ c : Fin k, 2 * (classC c).card ≤ (Ucov c).card := by
    intro c
    have hdisj : ((classC c) : Set (Finset (Fin n))).PairwiseDisjoint (fun a => a ∩ U) := by
      intro a₁ h₁ a₂ h₂ hne
      obtain ⟨A₁, hA₁, rfl⟩ := Finset.mem_image.mp h₁
      obtain ⟨A₂, hA₂, rfl⟩ := Finset.mem_image.mp h₂
      have hc1 : cU A₁ = c := (Finset.mem_filter.mp hA₁).2
      have hc2 : cU A₂ = c := (Finset.mem_filter.mp hA₂).2
      have hdisjA : Disjoint A₁.1 A₂.1 := Finset.disjoint_iff_inter_eq_empty.mpr (by
        by_contra hne_int
        have hmeet : (A₁.1 ∩ A₂.1).Nonempty := Finset.nonempty_iff_ne_empty.mpr hne_int
        exact hcU_prop A₁ A₂ (fun h => hne (congrArg Subtype.val h)) hmeet (hc1.trans hc2.symm))
      exact Finset.disjoint_left.mpr fun z hz₁ hz₂ =>
        Finset.disjoint_left.mp hdisjA (Finset.mem_inter.mp hz₁).1 (Finset.mem_inter.mp hz₂).1
    rw [Finset.card_biUnion hdisj]
    calc 2 * (classC c).card = ∑ _a ∈ classC c, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ a ∈ classC c, (a ∩ U).card := Finset.sum_le_sum fun a ha => by
          obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp ha
          exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp A.2).1).2
  have hUcov_sub : ∀ c : Fin k, Ucov c ⊆ U := fun c z hz => by
    obtain ⟨_, _, h2⟩ := Finset.mem_biUnion.mp hz; exact (Finset.mem_inter.mp h2).2
  -- Needed matchings for each y ∈ U
  let need : Fin n → ℕ := fun y => (b.card - (Ty y).card) - F
  -- Inductive extraction of pairwise edge-disjoint matchings M c ⊆ G for c : Fin k
  have hex_M : ∀ j ≤ k, ∃ M : Fin k → Finset (Fin n × Fin n),
      (∀ c, M c ⊆ G) ∧
      (∀ c, j ≤ c.val → M c = ∅) ∧
      (∀ c, ∀ e₁ ∈ M c, ∀ e₂ ∈ M c, e₁ ≠ e₂ → e₁.1 ≠ e₂.1 ∧ e₁.2 ≠ e₂.2) ∧
      (∀ c, ∀ e ∈ M c, e.1 ∉ Bcov c ∧ e.2 ∉ Ucov c) ∧
      (∀ c₁ c₂, c₁ ≠ c₂ → Disjoint (M c₁) (M c₂)) ∧
      (∀ y ∈ U, min (need y) ((Finset.univ.filter (fun c : Fin k => c.val < j ∧ y ∉ Ucov c)).card) ≤
        (Finset.univ.filter (fun c : Fin k => c.val < j ∧ ∃ x, (x, y) ∈ M c)).card) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨fun _ => ∅, fun _ => Finset.empty_subset _, fun _ _ => rfl,
        fun _ _ h => (Finset.notMem_empty _ h).elim, fun _ _ h => (Finset.notMem_empty _ h).elim,
        fun _ _ _ => Finset.disjoint_empty_left _, ?_⟩
      intro y _; simp
    | succ j ih =>
      intro hj1
      obtain ⟨M, hMG, hMempty, hMmatch, hMavoid, hMdisj, hMneed⟩ := ih (by omega)
      let c₀ : Fin k := ⟨j, by omega⟩
      let prevC : Finset (Fin k) := Finset.univ.filter (fun c : Fin k => c.val < j)
      let prevE : Finset (Fin n × Fin n) := prevC.biUnion M
      let matchedCnt : Fin n → ℕ := fun y =>
        (Finset.univ.filter (fun c : Fin k => c.val < j ∧ ∃ x, (x, y) ∈ M c)).card
      let Need : Finset (Fin n) := (U \ Ucov c₀).filter (fun y => matchedCnt y < need y)
      -- Greedily build a matching M₀ ⊆ G \ prevE covering every y ∈ Need
      have hex_M₀ : ∀ W ⊆ Need, ∃ M₀ : Finset (Fin n × Fin n),
          M₀ ⊆ G ∧ Disjoint M₀ prevE ∧
          (∀ e₁ ∈ M₀, ∀ e₂ ∈ M₀, e₁ ≠ e₂ → e₁.1 ≠ e₂.1 ∧ e₁.2 ≠ e₂.2) ∧
          (∀ e ∈ M₀, e.1 ∉ Bcov c₀ ∧ e.2 ∈ W) ∧
          (∀ y ∈ W, ∃ x, (x, y) ∈ M₀) ∧ M₀.card = W.card := by
        intro W
        induction W using Finset.induction_on with
        | empty =>
          intro _
          exact ⟨∅, Finset.empty_subset _, Finset.disjoint_empty_left _,
            fun _ h => (Finset.notMem_empty _ h).elim,
            fun _ h => (Finset.notMem_empty _ h).elim,
            fun _ h => (Finset.notMem_empty _ h).elim, rfl⟩
        | @insert y W' hyW' ihW =>
          intro hWsub
          obtain ⟨M₀, hM₀G, hM₀prev, hM₀m, hM₀av, hM₀cov, hM₀card⟩ :=
            ihW ((Finset.subset_insert y W').trans hWsub)
          have hyNeed : y ∈ Need := hWsub (Finset.mem_insert_self y W')
          obtain ⟨hyDiff, hyLt⟩ := Finset.mem_filter.mp hyNeed
          obtain ⟨hyU, hy_nUcov⟩ := Finset.mem_sdiff.mp hyDiff
          let badX : Finset (Fin n) := b.filter (fun x => (x, y) ∉ G)
          let usedX : Finset (Fin n) := prevC.biUnion (fun c => ((M c).filter (fun e => e.2 = y)).image Prod.fst)
          let Forb : Finset (Fin n) := badX ∪ usedX ∪ Bcov c₀ ∪ M₀.image Prod.fst
          have hbad_card : badX.card = (Ty y).card := by
            have hpart := Finset.card_filter_add_card_filter_not (s := b) (fun x => (x, y) ∈ G)
            have hgood : (b.filter (fun x => (x, y) ∈ G)).card = (G.filter (fun p => p.2 = y)).card := by
              rw [← Finset.card_image_of_injOn (f := fun x => (x, y)) (fun _ _ _ _ h => (Prod.mk.inj h).1)]
              congr 1; ext ⟨x, y'⟩
              simp only [Finset.mem_image, Finset.mem_filter, hG_mem]
              constructor
              · rintro ⟨x', ⟨hx', _, _, hL⟩, hpair⟩; rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩; exact ⟨⟨hx', hyU, hL⟩, rfl⟩
              · rintro ⟨⟨hx', hy', hL⟩, rfl⟩; exact ⟨x, ⟨hx', hx', hy', hL⟩, rfl⟩
            have hdeg := hG_deg_y y hyU
            change (b.filter (fun x => (x, y) ∈ G)).card + badX.card = b.card at hpart
            omega
          have hused_card : usedX.card ≤ matchedCnt y := by
            have hsub_u : usedX ⊆ (Finset.univ.filter (fun c : Fin k => c.val < j ∧ ∃ x, (x, y) ∈ M c)).biUnion
                (fun c => ((M c).filter (fun e => e.2 = y)).image Prod.fst) := by
              intro x hx
              obtain ⟨c, hc, hxin⟩ := Finset.mem_biUnion.mp hx
              obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hxin
              obtain ⟨heM, hey⟩ := Finset.mem_filter.mp he
              refine Finset.mem_biUnion.mpr ⟨c, Finset.mem_filter.mpr
                ⟨Finset.mem_univ _, (Finset.mem_filter.mp hc).2, ⟨e.1, by rwa [← hey]⟩⟩, hxin⟩
            calc usedX.card
                ≤ ∑ c ∈ Finset.univ.filter (fun c : Fin k => c.val < j ∧ ∃ x, (x, y) ∈ M c),
                    (((M c).filter (fun e => e.2 = y)).image Prod.fst).card :=
                  (Finset.card_le_card hsub_u).trans Finset.card_biUnion_le
              _ ≤ ∑ _c ∈ Finset.univ.filter (fun c : Fin k => c.val < j ∧ ∃ x, (x, y) ∈ M c), 1 := by
                  refine Finset.sum_le_sum fun c _ => ?_
                  refine Finset.card_image_le.trans (Finset.card_le_one.mpr fun e₁ h₁ e₂ h₂ => ?_)
                  by_contra hne
                  exact (hMmatch c e₁ (Finset.mem_filter.mp h₁).1 e₂ (Finset.mem_filter.mp h₂).1 hne).2
                    ((Finset.mem_filter.mp h₁).2.trans (Finset.mem_filter.mp h₂).2.symm)
              _ = matchedCnt y := by simp [matchedCnt]
          have hW'_le : W'.card + 1 ≤ (U \ Ucov c₀).card := by
            have hsub : insert y W' ⊆ U \ Ucov c₀ := fun z hz => (Finset.mem_filter.mp (hWsub hz)).1
            have := Finset.card_le_card hsub
            rwa [Finset.card_insert_of_notMem hyW'] at this
          have hUdiff : (U \ Ucov c₀).card + (Ucov c₀).card = u := by
            exact Finset.card_sdiff_add_card_eq_card (hUcov_sub c₀)
          have hForb_lt : Forb.card < b.card := by
            have h1 : Forb.card ≤ badX.card + usedX.card + (Bcov c₀).card + (M₀.image Prod.fst).card := by
              dsimp only [Forb]
              exact (Finset.card_union_le _ _).trans (Nat.add_le_add_right
                ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _)
            have h2 : (M₀.image Prod.fst).card ≤ W'.card := Finset.card_image_le.trans (le_of_eq hM₀card)
            have h3 := hBcov_le c₀
            have h4 := hUcov_ge c₀
            have hneed_pos : 0 < need y := by omega
            have hneed_eq : need y = k - (Ty y).card - (u - 1) := by dsimp only [need, F]; omega
            omega
          obtain ⟨x, hxb, hxForb⟩ := Finset.exists_mem_notMem_of_card_lt_card hForb_lt
          have hx_not_bad : x ∉ badX := fun h => hxForb (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
          have hx_not_used : x ∉ usedX := fun h => hxForb (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
          have hx_not_Bcov : x ∉ Bcov c₀ := fun h => hxForb (Finset.mem_union_left _ (Finset.mem_union_right _ h))
          have hx_not_M0 : x ∉ M₀.image Prod.fst := fun h => hxForb (Finset.mem_union_right _ h)
          have hxyG : (x, y) ∈ G := by
            by_contra hnot; exact hx_not_bad (Finset.mem_filter.mpr ⟨hxb, hnot⟩)
          have hxy_nprev : (x, y) ∉ prevE := by
            intro hmem
            obtain ⟨c, hc, hxyM⟩ := Finset.mem_biUnion.mp hmem
            apply hx_not_used
            exact Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_image.mpr ⟨(x, y), Finset.mem_filter.mpr ⟨hxyM, rfl⟩, rfl⟩⟩
          have hxy_nM0 : (x, y) ∉ M₀ := fun h => hx_not_M0 (Finset.mem_image.mpr ⟨(x, y), h, rfl⟩)
          refine ⟨insert (x, y) M₀, Finset.insert_subset hxyG hM₀G,
            Finset.disjoint_insert_left.mpr ⟨hxy_nprev, hM₀prev⟩, ?_, ?_, ?_, ?_⟩
          · intro e₁ h₁ e₂ h₂ hne
            rcases Finset.mem_insert.mp h₁ with rfl | h₁' <;> rcases Finset.mem_insert.mp h₂ with rfl | h₂'
            · exact (hne rfl).elim
            · exact ⟨fun h => hx_not_M0 (Finset.mem_image.mpr ⟨e₂, h₂', h.symm⟩),
                fun h => hyW' (by dsimp only at h; rw [h]; exact (hM₀av e₂ h₂').2)⟩
            · exact ⟨fun h => hx_not_M0 (Finset.mem_image.mpr ⟨e₁, h₁', h⟩),
                fun h => hyW' (by dsimp only at h; rw [← h]; exact (hM₀av e₁ h₁').2)⟩
            · exact hM₀m e₁ h₁' e₂ h₂' hne
          · intro e he
            rcases Finset.mem_insert.mp he with rfl | he'
            · exact ⟨hx_not_Bcov, Finset.mem_insert_self y W'⟩
            · exact ⟨(hM₀av e he').1, Finset.mem_insert_of_mem (hM₀av e he').2⟩
          · intro z hz
            rcases Finset.mem_insert.mp hz with rfl | hz'
            · exact ⟨x, Finset.mem_insert_self _ _⟩
            · obtain ⟨x', hx'⟩ := hM₀cov z hz'
              exact ⟨x', Finset.mem_insert_of_mem hx'⟩
          · rw [Finset.card_insert_of_notMem hxy_nM0, Finset.card_insert_of_notMem hyW', hM₀card]
      obtain ⟨M₀, hM₀G, hM₀prev, hM₀m, hM₀av, hM₀cov, _⟩ := hex_M₀ Need (Finset.Subset.refl _)
      let M' : Fin k → Finset (Fin n × Fin n) := fun c => if c = c₀ then M₀ else M c
      refine ⟨M', ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro c; dsimp only [M']; split_ifs <;> [exact hM₀G; exact hMG c]
      · intro c hc; dsimp only [M']; rw [if_neg (fun h => by rw [h] at hc; dsimp only [c₀] at hc; omega)]
        exact hMempty c (by omega)
      · intro c; dsimp only [M']; split_ifs <;> [exact hM₀m; exact hMmatch c]
      · intro c e he; dsimp only [M'] at he; split_ifs at he with hc
        · subst hc; exact ⟨(hM₀av e he).1, (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hM₀av e he).2).1).2⟩
        · exact hMavoid c e he
      · intro c₁ c₂ hne
        dsimp only [M']
        by_cases h1 : c₁ = c₀ <;> by_cases h2 : c₂ = c₀
        · exact (hne (h1.trans h2.symm)).elim
        · rw [if_pos h1, if_neg h2]
          by_cases hc2 : c₂.val < j
          · exact Finset.disjoint_of_subset_right
              (Finset.subset_biUnion_of_mem M (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc2⟩)) hM₀prev
          · rw [hMempty c₂ (by omega)]; exact Finset.disjoint_empty_right _
        · rw [if_neg h1, if_pos h2]
          by_cases hc1 : c₁.val < j
          · exact (Finset.disjoint_of_subset_right
              (Finset.subset_biUnion_of_mem M (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc1⟩)) hM₀prev).symm
          · rw [hMempty c₁ (by omega)]; exact Finset.disjoint_empty_left _
        · rw [if_neg h1, if_neg h2]
          exact hMdisj c₁ c₂ hne
      · intro y hyU
        have hprev := hMneed y hyU
        have havail_eq : (Finset.univ.filter (fun c : Fin k => c.val < j + 1 ∧ y ∉ Ucov c)).card =
            (Finset.univ.filter (fun c : Fin k => c.val < j ∧ y ∉ Ucov c)).card +
              (if y ∉ Ucov c₀ then 1 else 0) := by
          by_cases hy0 : y ∉ Ucov c₀
          · rw [if_pos hy0]
            have hset : Finset.univ.filter (fun c : Fin k => c.val < j + 1 ∧ y ∉ Ucov c) =
                insert c₀ (Finset.univ.filter (fun c : Fin k => c.val < j ∧ y ∉ Ucov c)) := by
              ext c; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, c₀]
              constructor
              · rintro ⟨hlt, hyc⟩
                rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hlt) with h | h
                · exact Or.inr ⟨h, hyc⟩
                · exact Or.inl h
              · rintro (rfl | ⟨hlt, hyc⟩)
                · exact ⟨Nat.lt_succ_self _, hy0⟩
                · exact ⟨Nat.lt_succ_of_lt hlt, hyc⟩
            rw [hset, Finset.card_insert_of_notMem (by simp [c₀])]
          · rw [if_neg hy0, add_zero]
            congr 1; ext c
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨hlt, hyc⟩
              refine ⟨?_, hyc⟩
              by_contra hge
              have hceq : c = c₀ := Fin.ext (by dsimp only [c₀]; omega)
              exact hy0 (hceq ▸ hyc)
            · rintro ⟨hlt, hyc⟩; exact ⟨Nat.lt_succ_of_lt hlt, hyc⟩
        have hmatch_eq : (Finset.univ.filter (fun c : Fin k => c.val < j + 1 ∧ ∃ x, (x, y) ∈ M' c)).card =
            matchedCnt y + (if ∃ x, (x, y) ∈ M₀ then 1 else 0) := by
          by_cases hy0 : ∃ x, (x, y) ∈ M₀
          · rw [if_pos hy0]
            have hset : Finset.univ.filter (fun c : Fin k => c.val < j + 1 ∧ ∃ x, (x, y) ∈ M' c) =
                insert c₀ (Finset.univ.filter (fun c : Fin k => c.val < j ∧ ∃ x, (x, y) ∈ M c)) := by
              ext c; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, c₀]
              constructor
              · rintro ⟨hlt, hx⟩
                rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hlt) with h | h
                · right; refine ⟨h, ?_⟩
                  have hne : c ≠ c₀ := fun hc => by rw [hc] at h; dsimp only [c₀] at h; omega
                  simpa [M', hne] using hx
                · exact Or.inl h
              · rintro (hc_eq | ⟨hlt, hx⟩)
                · have hceq : c = c₀ := Fin.ext hc_eq
                  refine ⟨by rw [hceq]; exact Nat.lt_succ_self _, ?_⟩
                  rw [hceq]; dsimp only [M']; rw [if_pos rfl]; exact hy0
                · have hne : c ≠ c₀ := fun hc => by rw [hc] at hlt; dsimp only [c₀] at hlt; omega
                  exact ⟨Nat.lt_succ_of_lt hlt, by simpa [M', hne] using hx⟩
            rw [hset, Finset.card_insert_of_notMem (by simp [c₀])]
          · rw [if_neg hy0, add_zero]
            congr 1; ext c
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨hlt, hx⟩
              have hne : c ≠ c₀ := by
                rintro rfl; exact hy0 (by simpa [M'] using hx)
              have hlt' : c.val < j := by have : c.val ≠ j := fun h => hne (Fin.ext h); omega
              exact ⟨hlt', by simpa [M', hne] using hx⟩
            · rintro ⟨hlt, hx⟩
              have hne : c ≠ c₀ := fun hc => by rw [hc] at hlt; dsimp only [c₀] at hlt; omega
              exact ⟨Nat.lt_succ_of_lt hlt, by simpa [M', hne] using hx⟩
        rw [havail_eq, hmatch_eq]
        by_cases hlt : matchedCnt y < need y
        · by_cases hy0 : y ∉ Ucov c₀
          · have hyN : y ∈ Need := Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hyU, hy0⟩, hlt⟩
            rw [if_pos hy0, if_pos (hM₀cov y hyN)]
            change min (need y) _ ≤ matchedCnt y at hprev
            omega
          · rw [if_neg hy0]; change min (need y) _ ≤ matchedCnt y at hprev; omega
        · omega
  obtain ⟨M, hMG, _, hMmatch, hMavoid, hMdisj, hMneed⟩ := hex_M k le_rfl
  let allM : Finset (Fin n × Fin n) := Finset.univ.biUnion M
  let G' : Finset (Fin n × Fin n) := G \ allM
  -- Bound degrees of G' by F
  have hG'_L : ∀ x : Fin n, (G'.filter (fun e => e.1 = x)).card ≤ F := fun x =>
    ((Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset)).trans (hG_deg_x x)).trans huF
  have hG'_R : ∀ y : Fin n, (G'.filter (fun e => e.2 = y)).card ≤ F := by
    intro y
    by_cases hyU : y ∈ U
    · -- Count available colors for y in Fin k
      have havail_ge : k - ((Ty y).card + (Sy y).card) ≤
          (Finset.univ.filter (fun c : Fin k => c.val < k ∧ y ∉ Ucov c)).card := by
        have hpart := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k))) (fun c => y ∈ Ucov c)
        rw [Finset.card_univ, Fintype.card_fin] at hpart
        have hcov_le : (Finset.univ.filter (fun c : Fin k => y ∈ Ucov c)).card ≤ (Ty y).card + (Sy y).card := by
          have hsub : Finset.univ.filter (fun c : Fin k => y ∈ Ucov c) ⊆
              ((Ty y ∪ Sy y).attach.image (fun A => cU ⟨A.1, by
                rcases Finset.mem_union.mp A.2 with h | h <;> exact (Finset.mem_filter.mp h).1⟩)) := by
            intro c hc
            obtain ⟨a, ha, hyaU⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hc).2
            obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp ha
            have hyA : y ∈ A.1 := (Finset.mem_inter.mp hyaU).1
            have hATS : A.1 ∈ Ty y ∪ Sy y := by
              by_cases hhit : (A.1 ∩ b).Nonempty
              · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨A.2, hyA, hhit⟩)
              · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨A.2, hyA,
                  Finset.disjoint_iff_inter_eq_empty.mpr (Finset.not_nonempty_iff_eq_empty.mp hhit)⟩)
            exact Finset.mem_image.mpr ⟨⟨A.1, hATS⟩, Finset.mem_attach _ _, (Finset.mem_filter.mp hA).2⟩
          have hdisj_TS : Disjoint (Ty y) (Sy y) := Finset.disjoint_left.mpr fun a h1 h2 =>
            Finset.not_disjoint_iff_nonempty_inter.mpr (Finset.mem_filter.mp h1).2.2 (Finset.mem_filter.mp h2).2.2
          calc (Finset.univ.filter (fun c : Fin k => y ∈ Ucov c)).card
              ≤ ((Ty y ∪ Sy y).attach.image _).card := Finset.card_le_card hsub
            _ ≤ (Ty y ∪ Sy y).card := Finset.card_image_le.trans (by rw [Finset.card_attach])
            _ = (Ty y).card + (Sy y).card := Finset.card_union_of_disjoint hdisj_TS
        have heq : Finset.univ.filter (fun c : Fin k => c.val < k ∧ y ∉ Ucov c) =
            Finset.univ.filter (fun c : Fin k => ¬ y ∈ Ucov c) := by
          ext c; simp
        rw [heq]; omega
      have hTS := hTy_add_Sy y hyU
      have hdeg_y := hG_deg_y y hyU
      have hu1 : 1 ≤ u := Finset.card_pos.mpr ⟨y, hyU⟩
      have hneed_le_avail : need y ≤ (Finset.univ.filter (fun c : Fin k => c.val < k ∧ y ∉ Ucov c)).card := by
        dsimp only [need, F]; omega
      have hmatched_ge : need y ≤ (Finset.univ.filter (fun c : Fin k => c.val < k ∧ ∃ x, (x, y) ∈ M c)).card := by
        have h := hMneed y hyU
        rw [min_eq_left hneed_le_avail] at h
        exact h
      -- Each color c with ∃ x, (x, y) ∈ M c contributes a distinct edge in allM.filter (·.2 = y) ⊆ G.filter (·.2 = y)
      have hallM_ge : need y ≤ (allM.filter (fun e => e.2 = y)).card := by
        let Cset := Finset.univ.filter (fun c : Fin k => c.val < k ∧ ∃ x, (x, y) ∈ M c)
        let pickE : Fin k → Fin n × Fin n := fun c =>
          if h : c ∈ Cset then ((Finset.mem_filter.mp h).2.2.choose, y) else (y, y)
        have hinj : Set.InjOn pickE Cset := by
          intro c₁ h₁ c₂ h₂ heq
          have h₁' : c₁ ∈ Cset := Finset.mem_coe.mp h₁
          have h₂' : c₂ ∈ Cset := Finset.mem_coe.mp h₂
          by_contra hne
          dsimp only [pickE] at heq
          rw [dif_pos h₁', dif_pos h₂'] at heq
          have hm1 : ((Finset.mem_filter.mp h₁').2.2.choose, y) ∈ M c₁ := (Finset.mem_filter.mp h₁').2.2.choose_spec
          have hm2 : ((Finset.mem_filter.mp h₂').2.2.choose, y) ∈ M c₂ := (Finset.mem_filter.mp h₂').2.2.choose_spec
          exact Finset.disjoint_left.mp (hMdisj c₁ c₂ hne) hm1 (heq ▸ hm2)
        have hsub : Cset.image pickE ⊆ allM.filter (fun e => e.2 = y) := by
          intro e he
          obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp he
          dsimp only [pickE]; rw [dif_pos hc]
          exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _,
            (Finset.mem_filter.mp hc).2.2.choose_spec⟩, rfl⟩
        calc need y ≤ Cset.card := hmatched_ge
          _ = (Cset.image pickE).card := (Finset.card_image_of_injOn hinj).symm
          _ ≤ (allM.filter (fun e => e.2 = y)).card := Finset.card_le_card hsub
      have hsub_G : allM.filter (fun e => e.2 = y) ⊆ G.filter (fun e => e.2 = y) := by
        intro e he
        obtain ⟨h1, h2⟩ := Finset.mem_filter.mp he
        obtain ⟨c, _, heM⟩ := Finset.mem_biUnion.mp h1
        exact Finset.mem_filter.mpr ⟨hMG c heM, h2⟩
      have hsdiff : G'.filter (fun e => e.2 = y) = G.filter (fun e => e.2 = y) \ allM.filter (fun e => e.2 = y) := by
        ext e; simp only [G', Finset.mem_filter, Finset.mem_sdiff]; tauto
      rw [hsdiff, Finset.card_sdiff_of_subset hsub_G]
      dsimp only [need] at hallM_ge
      omega
    · have hempty : G'.filter (fun e => e.2 = y) = ∅ := by
        ext e; simp only [G', Finset.mem_filter, Finset.mem_sdiff, Finset.notMem_empty, iff_false]
        rintro ⟨⟨heG, _⟩, rfl⟩; exact hyU ((hG_mem e).mp heG).2.1
      rw [hempty]; simp
  -- Apply König's theorem to G' with F colors
  obtain ⟨cG', hcG'L, hcG'R⟩ := bipartite_edge_coloring G' F hG'_L hG'_R
  -- Assemble the full n-coloring c : L → Fin n
  have hex_pair : ∀ a ∈ L, a ≠ b → a ∉ LU → ∃ p ∈ G, a = {p.1, p.2} := by
    intro a ha hab haLU
    obtain ⟨x, hxb, y, hyU, heq⟩ := hclass a ha hab haLU
    exact ⟨(x, y), (hG_mem (x, y)).mpr ⟨hxb, hyU, heq ▸ ha⟩, heq⟩
  let c : L → Fin n := fun A =>
    if h1 : A.1 = b ∨ A.1 ∈ I₀ then ⟨0, by omega⟩
    else if h2 : A.1 ∈ LU' then ⟨1 + (cU ⟨A.1, h2⟩).val, by have := (cU ⟨A.1, h2⟩).isLt; omega⟩
    else
      have hAb : A.1 ≠ b := fun h => h1 (Or.inl h)
      have hALU : A.1 ∉ LU := fun h => h2 (Finset.mem_sdiff.mpr ⟨h, fun hI => h1 (Or.inr hI)⟩)
      let p := (hex_pair A.1 A.2 hAb hALU).choose
      let hpG := (hex_pair A.1 A.2 hAb hALU).choose_spec.1
      if h3 : ∃ c₀ : Fin k, p ∈ M c₀ then ⟨1 + h3.choose.val, by have := h3.choose.isLt; omega⟩
      else
        let hpG' : p ∈ G' := Finset.mem_sdiff.mpr ⟨hpG, fun hM => by
          obtain ⟨c₀, _, hpM⟩ := Finset.mem_biUnion.mp hM; exact h3 ⟨c₀, hpM⟩⟩
        ⟨1 + k + (cG' ⟨p, hpG'⟩).val, by have := (cG' ⟨p, hpG'⟩).isLt; omega⟩
  -- Clean characterization of c on each of the 4 disjoint parts of L
  have hc_case : ∀ A : L,
      ((A.1 = b ∨ A.1 ∈ I₀) ∧ (c A).val = 0) ∨
      (∃ h2 : A.1 ∈ LU', (c A).val = 1 + (cU ⟨A.1, h2⟩).val ∧ (c A).val ≤ k) ∨
      (∃ p ∈ G, A.1 = {p.1, p.2} ∧ ∃ c₀ : Fin k, p ∈ M c₀ ∧ (c A).val = 1 + c₀.val ∧ (c A).val ≤ k) ∨
      (∃ p, ∃ hpG' : p ∈ G', A.1 = {p.1, p.2} ∧ (c A).val = 1 + k + (cG' ⟨p, hpG'⟩).val) := by
    intro A
    by_cases h1 : A.1 = b ∨ A.1 ∈ I₀
    · exact Or.inl ⟨h1, by dsimp only [c]; rw [dif_pos h1]⟩
    · by_cases h2 : A.1 ∈ LU'
      · refine Or.inr (Or.inl ⟨h2, ?_, ?_⟩)
        · dsimp only [c]; rw [dif_neg h1, dif_pos h2]
        · dsimp only [c]; rw [dif_neg h1, dif_pos h2]; dsimp only; have := (cU ⟨A.1, h2⟩).isLt; omega
      · have hAb : A.1 ≠ b := fun h => h1 (Or.inl h)
        have hALU : A.1 ∉ LU := fun h => h2 (Finset.mem_sdiff.mpr ⟨h, fun hI => h1 (Or.inr hI)⟩)
        set p := (hex_pair A.1 A.2 hAb hALU).choose
        have hpG : p ∈ G := (hex_pair A.1 A.2 hAb hALU).choose_spec.1
        have hpEq : A.1 = {p.1, p.2} := (hex_pair A.1 A.2 hAb hALU).choose_spec.2
        by_cases h3 : ∃ c₀ : Fin k, p ∈ M c₀
        · refine Or.inr (Or.inr (Or.inl ⟨p, hpG, hpEq, h3.choose, h3.choose_spec, ?_, ?_⟩))
          · dsimp only [c]; rw [dif_neg h1, dif_neg h2, dif_pos h3]
          · dsimp only [c]; rw [dif_neg h1, dif_neg h2, dif_pos h3]; dsimp only; have := h3.choose.isLt; omega
        · have hpG' : p ∈ G' := Finset.mem_sdiff.mpr ⟨hpG, fun hM => by
            obtain ⟨c₀, _, hpM⟩ := Finset.mem_biUnion.mp hM; exact h3 ⟨c₀, hpM⟩⟩
          refine Or.inr (Or.inr (Or.inr ⟨p, hpG', hpEq, ?_⟩))
          dsimp only [c]; rw [dif_neg h1, dif_neg h2, dif_neg h3]
  -- Helper: LU' line and M c₀ edge cannot share both color and a point
  have hLU_M_clash : ∀ (X Y : L) (hX : X.1 ∈ LU') (p : Fin n × Fin n) (hpG : p ∈ G)
      (hYeq : Y.1 = {p.1, p.2}) (c₀ : Fin k) (hpM : p ∈ M c₀),
      cU ⟨X.1, hX⟩ = c₀ → (X.1 ∩ Y.1).Nonempty → False := by
    intro X Y hX p hpG hYeq c₀ hpM hc_eq hm
    have hpav := hMavoid c₀ p hpM
    have hXclass : X.1 ∈ classC c₀ := Finset.mem_image.mpr
      ⟨⟨X.1, hX⟩, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hc_eq⟩, rfl⟩
    obtain ⟨z, hz⟩ := hm
    obtain ⟨hzX, hzY⟩ := Finset.mem_inter.mp hz
    rw [hYeq, Finset.mem_insert, Finset.mem_singleton] at hzY
    have hpMem := (hG_mem p).mp hpG
    rcases hzY with hz1 | hz2
    · exact hpav.1 (Finset.mem_biUnion.mpr ⟨X.1, hXclass, Finset.mem_inter.mpr ⟨hz1 ▸ hzX, hpMem.1⟩⟩)
    · exact hpav.2 (Finset.mem_biUnion.mpr ⟨X.1, hXclass, Finset.mem_inter.mpr ⟨hz2 ▸ hzX, hpMem.2.1⟩⟩)
  -- Verify properness of c
  refine ⟨c, fun A B hne hmeet hcol => ?_⟩
  have hval := congrArg Fin.val hcol
  rcases hc_case A with ⟨hA1, hAv⟩ | ⟨hA2, hAv, hAle⟩ | ⟨pA, hpAG, hAeq, cA, hpAM, hAv, hAle⟩ | ⟨pA, hpAG', hAeq, hAv⟩ <;>
    rcases hc_case B with ⟨hB1, hBv⟩ | ⟨hB2, hBv, hBle⟩ | ⟨pB, hpBG, hBeq, cB, hpBM, hBv, hBle⟩ | ⟨pB, hpBG', hBeq, hBv⟩
  · -- both in {b} ∪ I₀
    rcases hA1 with hAb | hAI <;> rcases hB1 with hBb | hBI
    · exact hne (Subtype.ext (hAb.trans hBb.symm))
    · have hd := Finset.disjoint_iff_inter_eq_empty.mp (hI₀_disj_b B.1 hBI)
      rw [hAb, Finset.inter_comm, hd] at hmeet; exact Finset.not_nonempty_empty hmeet
    · have hd := Finset.disjoint_iff_inter_eq_empty.mp (hI₀_disj_b A.1 hAI)
      rw [hBb, hd] at hmeet; exact Finset.not_nonempty_empty hmeet
    · have hd := Finset.disjoint_iff_inter_eq_empty.mp (hI₀_pw A.1 hAI B.1 hBI (fun h => hne (Subtype.ext h)))
      rw [hd] at hmeet; exact Finset.not_nonempty_empty hmeet
  · omega
  · omega
  · omega
  · omega
  · exact hcU_prop ⟨A.1, hA2⟩ ⟨B.1, hB2⟩ (fun h => hne (Subtype.ext (congrArg (fun z : LU' => z.1) h))) hmeet (Fin.ext (by omega))
  · exact hLU_M_clash A B hA2 pB hpBG hBeq cB hpBM (Fin.ext (by omega)) hmeet
  · omega
  · omega
  · exact hLU_M_clash B A hB2 pA hpAG hAeq cA hpAM (Fin.ext (by omega)) (by rw [Finset.inter_comm]; exact hmeet)
  · have hc_eq : cA = cB := Fin.ext (by omega)
    have hpne : pA ≠ pB := fun h => hne (Subtype.ext (hAeq.trans (h ▸ hBeq.symm)))
    have hdisj_p := hMmatch cA pA hpAM pB (hc_eq ▸ hpBM) hpne
    obtain ⟨z, hz⟩ := hmeet
    obtain ⟨hzA, hzB⟩ := Finset.mem_inter.mp hz
    rw [hAeq, Finset.mem_insert, Finset.mem_singleton] at hzA
    rw [hBeq, Finset.mem_insert, Finset.mem_singleton] at hzB
    have hAG := (hG_mem pA).mp hpAG
    have hBG := (hG_mem pB).mp hpBG
    rcases hzA with hzA | hzA <;> rcases hzB with hzB | hzB
    · exact hdisj_p.1 (hzA.symm.trans hzB)
    · exact hne_of_bU pA.1 hAG.1 pB.2 hBG.2.1 (hzA.symm.trans hzB)
    · exact hne_of_bU pB.1 hBG.1 pA.2 hAG.2.1 (hzB.symm.trans hzA)
    · exact hdisj_p.2 (hzA.symm.trans hzB)
  · omega
  · omega
  · omega
  · omega
  · have hpne : pA ≠ pB := fun h => hne (Subtype.ext (hAeq.trans (h ▸ hBeq.symm)))
    have hceq : cG' ⟨pA, hpAG'⟩ = cG' ⟨pB, hpBG'⟩ := Fin.ext (by omega)
    obtain ⟨z, hz⟩ := hmeet
    obtain ⟨hzA, hzB⟩ := Finset.mem_inter.mp hz
    rw [hAeq, Finset.mem_insert, Finset.mem_singleton] at hzA
    rw [hBeq, Finset.mem_insert, Finset.mem_singleton] at hzB
    have hAG := (hG_mem pA).mp (Finset.mem_sdiff.mp hpAG').1
    have hBG := (hG_mem pB).mp (Finset.mem_sdiff.mp hpBG').1
    rcases hzA with hzA | hzA <;> rcases hzB with hzB | hzB
    · exact hcG'L ⟨pA, hpAG'⟩ ⟨pB, hpBG'⟩ (fun he => hpne (congrArg Subtype.val he)) (hzA.symm.trans hzB) hceq
    · exact hne_of_bU pA.1 hAG.1 pB.2 hBG.2.1 (hzA.symm.trans hzB)
    · exact hne_of_bU pB.1 hBG.1 pA.2 hAG.2.1 (hzB.symm.trans hzA)
    · exact hcG'R ⟨pA, hpAG'⟩ ⟨pB, hpBG'⟩ (fun he => hpne (congrArg Subtype.val he)) (hzA.symm.trans hzB) hceq

/- ## Section 5: Intersection degree bound on `L_U` and `u ≤ 3` closure -/

/-- Exact degree bound in `L_U`: for `a ∈ L_U` with `s = |a ∩ U|`, the number of lines in `L_U \ {a}`
meeting `a` is at most `s * (u - s) + (u - s) / 2`. -/
theorem degree_LU_le {n : ℕ} (L : Finset (Finset (Fin n))) (b : Finset (Fin n))
    (hb : b ∈ L)
    (hlin : ∀ a ∈ L, ∀ c ∈ L, a ≠ c → (a ∩ c).card ≤ 1)
    {a : Finset (Fin n)}
    (ha : a ∈ (L.erase b).filter (fun e => 2 ≤ (e ∩ (Finset.univ \ b)).card)) :
    let U := Finset.univ \ b
    let LU := (L.erase b).filter (fun e => 2 ≤ (e ∩ U).card)
    ((LU.erase a).filter (fun e => (a ∩ e).Nonempty)).card ≤
      (a ∩ U).card * (U.card - (a ∩ U).card) + (U.card - (a ∩ U).card) / 2 := by
  intro U LU
  have haL : a ∈ L := (Finset.mem_erase.mp (Finset.mem_filter.mp ha).1).2
  have hab : a ≠ b := (Finset.mem_erase.mp (Finset.mem_filter.mp ha).1).1
  have hU_sub : U \ a ⊆ U := Finset.sdiff_subset
  have hU_diff : (U \ a).card = U.card - (a ∩ U).card := by
    have : U \ a = U \ (a ∩ U) := by ext z; simp
    rw [this, Finset.card_sdiff_of_subset Finset.inter_subset_right]
  let nbrs := (LU.erase a).filter (fun e => (a ∩ e).Nonempty)
  let N_U := nbrs.filter (fun e => (a ∩ U ∩ e).Nonempty)
  let N_b := nbrs.filter (fun e => ¬ (a ∩ U ∩ e).Nonempty)
  have hpart := Finset.card_filter_add_card_filter_not (s := nbrs) (fun e => (a ∩ U ∩ e).Nonempty)
  -- Bound N_U ≤ (a ∩ U).card * (U \ a).card
  have hNU_le : N_U.card ≤ (a ∩ U).card * (U \ a).card := by
    have hsub : N_U ⊆ (a ∩ U).biUnion (fun y => (LU.erase a).filter (fun e => y ∈ e)) := by
      intro e he
      obtain ⟨h1, ⟨y, hy⟩⟩ := Finset.mem_filter.mp he
      obtain ⟨hyAU, hye⟩ := Finset.mem_inter.mp hy
      exact Finset.mem_biUnion.mpr ⟨y, hyAU, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h1).1, hye⟩⟩
    calc N_U.card
        ≤ ∑ y ∈ a ∩ U, ((LU.erase a).filter (fun e => y ∈ e)).card :=
          (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      _ ≤ ∑ _y ∈ a ∩ U, (U \ a).card := by
          refine Finset.sum_le_sum fun y hy => ?_
          let Fy := (LU.erase a).filter (fun e => y ∈ e)
          have hex : ∀ e ∈ Fy, ∃ w ∈ U \ a, w ∈ e := by
            intro e he
            obtain ⟨he1, hye⟩ := Finset.mem_filter.mp he
            obtain ⟨hea, heLU⟩ := Finset.mem_erase.mp he1
            have heL : e ∈ L := (Finset.mem_erase.mp (Finset.mem_filter.mp heLU).1).2
            have h2 : 2 ≤ (e ∩ U).card := (Finset.mem_filter.mp heLU).2
            have hy_eU : y ∈ e ∩ U := Finset.mem_inter.mpr ⟨hye, (Finset.mem_inter.mp hy).2⟩
            have hpos : 0 < ((e ∩ U).erase y).card := by rw [Finset.card_erase_of_mem hy_eU]; omega
            obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
            obtain ⟨hwy, hweU⟩ := Finset.mem_erase.mp hw
            obtain ⟨hwe, hwU⟩ := Finset.mem_inter.mp hweU
            have hwa : w ∉ a := by
              intro hwa
              have hya : y ∈ a := (Finset.mem_inter.mp hy).1
              have hsub2 : ({w, y} : Finset (Fin n)) ⊆ a ∩ e := by
                intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                rcases hz with rfl | rfl <;> exact Finset.mem_inter.mpr (by tauto)
              have h2le : 2 ≤ (a ∩ e).card := (Finset.card_pair hwy).symm ▸ Finset.card_le_card hsub2
              have hle1 := hlin a haL e heL hea.symm
              omega
            exact ⟨w, Finset.mem_sdiff.mpr ⟨hwU, hwa⟩, hwe⟩
          let pick : Finset (Fin n) → Fin n := fun e => if h : e ∈ Fy then (hex e h).choose else y
          have hinj : Set.InjOn pick Fy := by
            intro e₁ h₁ e₂ h₂ heq
            have h₁' : e₁ ∈ Fy := Finset.mem_coe.mp h₁
            have h₂' : e₂ ∈ Fy := Finset.mem_coe.mp h₂
            by_contra hne
            dsimp only [pick] at heq; rw [dif_pos h₁', dif_pos h₂'] at heq
            set w := (hex e₁ h₁').choose
            have hw1 := (hex e₁ h₁').choose_spec
            have hw2 := (hex e₂ h₂').choose_spec
            have hwy : w ≠ y := fun h => (Finset.mem_sdiff.mp hw1.1).2 (by change w ∈ a; rw [h]; exact (Finset.mem_inter.mp hy).1)
            have he1L : e₁ ∈ L := (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_erase.mp (Finset.mem_filter.mp h₁').1).2).1).2
            have he2L : e₂ ∈ L := (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_erase.mp (Finset.mem_filter.mp h₂').1).2).1).2
            have hsub2 : ({w, y} : Finset (Fin n)) ⊆ e₁ ∩ e₂ := by
              intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl
              · exact Finset.mem_inter.mpr ⟨hw1.2, heq ▸ hw2.2⟩
              · exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp h₁').2, (Finset.mem_filter.mp h₂').2⟩
            have h2le : 2 ≤ (e₁ ∩ e₂).card := (Finset.card_pair hwy).symm ▸ Finset.card_le_card hsub2
            have hle1 := hlin e₁ he1L e₂ he2L hne
            omega
          calc Fy.card = (Fy.image pick).card := (Finset.card_image_of_injOn hinj).symm
            _ ≤ (U \ a).card := Finset.card_le_card fun w hw => by
                obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hw
                dsimp only [pick]; rw [dif_pos he]; exact (hex e he).choose_spec.1
      _ = (a ∩ U).card * (U \ a).card := by rw [Finset.sum_const, smul_eq_mul]
  -- Bound 2 * N_b.card ≤ (U \ a).card
  have hNb_le : 2 * N_b.card ≤ (U \ a).card := by
    by_cases hne : N_b.Nonempty
    · -- Every e ∈ N_b meets a at the unique point x of a ∩ b
      have hxb_ex : ∃ x ∈ a ∩ b, ∀ e ∈ N_b, x ∈ e := by
        obtain ⟨e₀, he₀⟩ := hne
        obtain ⟨h1, hnoU⟩ := Finset.mem_filter.mp he₀
        obtain ⟨x, hx⟩ := (Finset.mem_filter.mp h1).2
        obtain ⟨hxa, hxe₀⟩ := Finset.mem_inter.mp hx
        have hxb : x ∈ b := by
          by_contra hxnb
          exact hnoU ⟨x, Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hxa, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxnb⟩⟩, hxe₀⟩⟩
        refine ⟨x, Finset.mem_inter.mpr ⟨hxa, hxb⟩, fun e he => ?_⟩
        obtain ⟨he1, henoU⟩ := Finset.mem_filter.mp he
        obtain ⟨x', hx'⟩ := (Finset.mem_filter.mp he1).2
        obtain ⟨hx'a, hx'e⟩ := Finset.mem_inter.mp hx'
        have hx'b : x' ∈ b := by
          by_contra hx'nb
          exact henoU ⟨x', Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hx'a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx'nb⟩⟩, hx'e⟩⟩
        have hxx' : x' = x := by
          by_contra hdiff
          have hsub : ({x, x'} : Finset (Fin n)) ⊆ a ∩ b := by
            intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl <;> exact Finset.mem_inter.mpr (by tauto)
          have h2le : 2 ≤ (a ∩ b).card := (Finset.card_pair (Ne.symm hdiff)).symm ▸ Finset.card_le_card hsub
          have hle1 := hlin a haL b hb hab
          omega
        exact hxx' ▸ hx'e
      obtain ⟨x, hxa_b, hxall⟩ := hxb_ex
      have hdisj : (N_b : Set (Finset (Fin n))).PairwiseDisjoint (fun e => e ∩ U) := by
        intro e₁ h₁ e₂ h₂ hdiff
        refine Finset.disjoint_left.mpr fun w hw₁ hw₂ => ?_
        have hwx : w ≠ x := fun h =>
          Finset.disjoint_left.mp (Finset.disjoint_sdiff : Disjoint b U) (Finset.mem_inter.mp hxa_b).2 (h ▸ (Finset.mem_inter.mp hw₁).2)
        have he1L : e₁ ∈ L := (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_filter.mp h₁).1).1).2).1).2
        have he2L : e₂ ∈ L := (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_filter.mp h₂).1).1).2).1).2
        have hsub : ({w, x} : Finset (Fin n)) ⊆ e₁ ∩ e₂ := by
          intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hw₁).1, (Finset.mem_inter.mp hw₂).1⟩
          · exact Finset.mem_inter.mpr ⟨hxall e₁ h₁, hxall e₂ h₂⟩
        have h2le : 2 ≤ (e₁ ∩ e₂).card := (Finset.card_pair hwx).symm ▸ Finset.card_le_card hsub
        have hle1 := hlin e₁ he1L e₂ he2L hdiff
        omega
      have hsub_Ua : N_b.biUnion (fun e => e ∩ U) ⊆ U \ a := by
        intro w hw
        obtain ⟨e, he, hweU⟩ := Finset.mem_biUnion.mp hw
        obtain ⟨hwe, hwU⟩ := Finset.mem_inter.mp hweU
        have hwna : w ∉ a := fun hwa =>
          (Finset.mem_filter.mp he).2 ⟨w, Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hwa, hwU⟩, hwe⟩⟩
        exact Finset.mem_sdiff.mpr ⟨hwU, hwna⟩
      calc 2 * N_b.card = ∑ _e ∈ N_b, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ e ∈ N_b, (e ∩ U).card := Finset.sum_le_sum fun e he =>
            (Finset.mem_filter.mp (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1).2).2
        _ = (N_b.biUnion (fun e => e ∩ U)).card := (Finset.card_biUnion hdisj).symm
        _ ≤ (U \ a).card := Finset.card_le_card hsub_Ua
    · have hempty : N_b = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      rw [hempty]; simp
  change N_U.card + N_b.card = nbrs.card at hpart
  rw [hU_diff] at hNU_le hNb_le
  dsimp only [nbrs] at hpart
  omega

/-- Concrete degree bound `Δ(L_U) ≤ D` for each `u ≤ 6`. -/
lemma color_by_u_bound {n D : ℕ} (L : Finset (Finset (Fin n))) (b : Finset (Fin n))
    (hb : b ∈ L)
    (hsize : ∀ a ∈ L, 2 ≤ a.card)
    (hlin : ∀ a ∈ L, ∀ c ∈ L, a ≠ c → (a ∩ c).card ≤ 1)
    (hcov : ∀ i j : Fin n, i ≠ j → ∃ e ∈ L, i ∈ e ∧ j ∈ e)
    (hD : ∀ s, 2 ≤ s → s ≤ (Finset.univ \ b).card →
      s * ((Finset.univ \ b).card - s) + ((Finset.univ \ b).card - s) / 2 ≤ D)
    (hbD : D + 2 ≤ b.card) :
    ∃ c : L → Fin n, ∀ A B : L, A ≠ B → (A.1 ∩ B.1).Nonempty → c A ≠ c B := by
  let U := Finset.univ \ b
  let LU := (L.erase b).filter (fun e => 2 ≤ (e ∩ U).card)
  have hdeg : ∀ a ∈ LU, ((LU.erase a).filter (fun e => (a ∩ e).Nonempty)).card ≤ D := by
    intro a ha
    have h1 := degree_LU_le L b hb hlin ha
    have hs2 : 2 ≤ (a ∩ U).card := (Finset.mem_filter.mp ha).2
    have hsu : (a ∩ U).card ≤ U.card := Finset.card_le_card Finset.inter_subset_right
    exact h1.trans (hD (a ∩ U).card hs2 hsu)
  obtain ⟨cU, hcU⟩ := greedy_block_coloring LU D hdeg
  have hLU_eq : LU \ ∅ = LU := Finset.sdiff_empty
  refine color_of_small_outside L b hb hsize hlin hcov ∅ (Finset.empty_subset _)
    (fun _ h => (Finset.notMem_empty _ h).elim) (fun _ h => (Finset.notMem_empty _ h).elim) ?_ (by omega)
  exact ⟨fun A => cU ⟨A.1, hLU_eq ▸ A.2⟩, fun A B hne hmeet =>
    hcU ⟨A.1, hLU_eq ▸ A.2⟩ ⟨B.1, hLU_eq ▸ B.2⟩ (fun h => hne (Subtype.ext (congrArg (fun z : LU => z.1) h))) hmeet⟩

/-- Complete closure of `u = n - |b| ≤ 3` for every `n`. -/
theorem color_u_le_three {n : ℕ} (L : Finset (Finset (Fin n))) (b : Finset (Fin n))
    (hb : b ∈ L)
    (hsize : ∀ a ∈ L, 2 ≤ a.card)
    (hlin : ∀ a ∈ L, ∀ c ∈ L, a ≠ c → (a ∩ c).card ≤ 1)
    (hcov : ∀ i j : Fin n, i ≠ j → ∃ e ∈ L, i ∈ e ∧ j ∈ e)
    (hmax : ∀ a ∈ L, a.card ≤ b.card)
    (hu3 : (Finset.univ \ b).card ≤ 3) :
    ∃ c : L → Fin n, ∀ A B : L, A ≠ B → (A.1 ∩ B.1).Nonempty → c A ≠ c B := by
  let U := Finset.univ \ b
  have hbu : b.card + U.card = n := by
    have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ b)
    rw [Finset.card_univ, Fintype.card_fin] at this
    dsimp only [U]; omega
  have hb2 : 2 ≤ b.card := hsize b hb
  -- If b.card = 2 then every block has size 2
  by_cases hbe2 : b.card = 2
  · exact color_single_big_block L b hb hsize hlin fun a ha _ => by have := hsize a ha; have := hmax a ha; omega
  have hb3 : 3 ≤ b.card := by omega
  -- If u ≤ 2, Δ(L_U) = 0, so D = 0 and D + 2 = 2 ≤ b.card
  by_cases hu2 : U.card ≤ 2
  · exact color_by_u_bound L b hb hsize hlin hcov (D := 0)
      (fun s hs2 hsu => by have hu2' : (Finset.univ \ b).card ≤ 2 := hu2; have hs_le : s ≤ 2 := hsu.trans hu2'; interval_cases s <;> omega) (by omega)
  -- Now U.card = 3 and 3 ≤ b.card
  have hu_eq3 : U.card = 3 := by dsimp only [U] at hu2 ⊢; omega
  by_cases hb4 : 4 ≤ b.card
  · exact color_by_u_bound L b hb hsize hlin hcov (D := 2)
      (fun s hs2 hsu => by rw [show (Finset.univ \ b).card = 3 from hu_eq3] at hsu ⊢; interval_cases s <;> omega) (by omega)
  -- Remaining single order: U.card = 3, b.card = 3, n = 6
  have hb_eq3 : b.card = 3 := by omega
  have hn6 : n = 6 := by omega
  let LU := (L.erase b).filter (fun e => 2 ≤ (e ∩ U).card)
  -- Note: |LU| ≤ 3 because each a ∈ LU covers at least 1 pair of the 3 pairs in U, pairwise disjointly
  have hLU_le3 : LU.card ≤ 3 := by
    by_cases hne : LU.Nonempty
    · obtain ⟨a₀, ha₀⟩ := hne
      have hdeg := degree_LU_le L b hb hlin ha₀
      have hs2 : 2 ≤ (a₀ ∩ U).card := (Finset.mem_filter.mp ha₀).2
      have hsu : (a₀ ∩ U).card ≤ 3 := hu_eq3 ▸ Finset.card_le_card Finset.inter_subset_right
      -- Any two distinct elements of LU meet in U (since |a ∩ U| ≥ 2 in a 3-element set U!)
      have hsub : LU.erase a₀ ⊆ (LU.erase a₀).filter (fun e => (a₀ ∩ e).Nonempty) := by
        intro e he
        refine Finset.mem_filter.mpr ⟨he, ?_⟩
        have heLU := (Finset.mem_erase.mp he).2
        have he2 : 2 ≤ (e ∩ U).card := (Finset.mem_filter.mp heLU).2
        by_contra hnot
        have hdisj : Disjoint (a₀ ∩ U) (e ∩ U) := Finset.disjoint_left.mpr fun z h1 h2 =>
          hnot ⟨z, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp h1).1, (Finset.mem_inter.mp h2).1⟩⟩
        have hun : (a₀ ∩ U) ∪ (e ∩ U) ⊆ U := Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
        have hle := Finset.card_le_card hun
        rw [Finset.card_union_of_disjoint hdisj] at hle
        omega
      have h1 : (LU.erase a₀).card ≤ 2 := by
        have hle := (Finset.card_le_card hsub).trans hdeg
        dsimp only [U, LU] at hle hs2 hsu hu_eq3 ⊢
        rw [hu_eq3] at hle
        set s := (a₀ ∩ (Finset.univ \ b)).card
        interval_cases s <;> omega
      have h2 := Finset.card_erase_add_one ha₀
      omega
    · simp [Finset.not_nonempty_iff_eq_empty.mp hne]
  -- Case 1: |LU| ≤ 2 → trivial 2-coloring of LU, k = 2, k + 1 = 3 = b.card!
  by_cases hLU2 : LU.card ≤ 2
  · have hcol : ∃ cU : ↑(LU \ ∅) → Fin 2, ∀ A B, A ≠ B → (A.1 ∩ B.1).Nonempty → cU A ≠ cU B := by
      let e : ↑(LU \ ∅) ≃ Fin (LU \ ∅).card := (LU \ ∅).equivFin
      refine ⟨fun A => ⟨(e A).val, by have := (e A).isLt; simp at this ⊢; omega⟩, fun A B hne _ h => ?_⟩
      exact hne (e.injective (Fin.ext (by simpa using congrArg Fin.val h)))
    exact color_of_small_outside L b hb hsize hlin hcov ∅ (Finset.empty_subset _)
      (fun _ h => (Finset.notMem_empty _ h).elim) (fun _ h => (Finset.notMem_empty _ h).elim) hcol (by omega)
  -- Case 2: |LU| = 3 and some a₀ ∈ LU is disjoint from b → put I₀ = {a₀}, |LU \ I₀| = 2!
  have hLU3 : LU.card = 3 := by omega
  by_cases hex_in : ∃ a₀ ∈ LU, Disjoint a₀ b
  · obtain ⟨a₀, ha₀, ha₀_disj⟩ := hex_in
    have hcard2 : (LU \ {a₀}).card = 2 := by
      rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr ha₀), Finset.card_singleton, hLU3]
    have hcol : ∃ cU : ↑(LU \ {a₀}) → Fin 2, ∀ A B, A ≠ B → (A.1 ∩ B.1).Nonempty → cU A ≠ cU B := by
      let e : ↑(LU \ {a₀}) ≃ Fin (LU \ {a₀}).card := (LU \ {a₀}).equivFin
      refine ⟨fun A => ⟨(e A).val, by rw [← hcard2]; exact (e A).isLt⟩, fun A B hne _ h => ?_⟩
      exact hne (e.injective (Fin.ext (by simpa using congrArg Fin.val h)))
    exact color_of_small_outside L b hb hsize hlin hcov {a₀} (Finset.singleton_subset_iff.mpr ha₀)
      (fun a ha => by rw [Finset.mem_singleton.mp ha]; exact ha₀_disj)
      (fun a₁ h₁ a₂ h₂ hne => (hne ((Finset.mem_singleton.mp h₁).trans (Finset.mem_singleton.mp h₂).symm)).elim)
      hcol (by omega)
  -- Case 3: |LU| = 3 and every a ∈ LU meets b.
  push Not at hex_in
  have hall_hit : ∀ a ∈ LU, ∃ x, x ∈ a ∩ b := fun a ha =>
    Finset.not_disjoint_iff_nonempty_inter.mp (hex_in a ha)
  have hLU_meet_U : ∀ a₁ ∈ LU, ∀ a₂ ∈ LU, (a₁ ∩ U ∩ a₂).Nonempty := by
    intro a₁ h₁ a₂ h₂
    have c1 : 2 ≤ (a₁ ∩ U).card := (Finset.mem_filter.mp h₁).2
    have c2 : 2 ≤ (a₂ ∩ U).card := (Finset.mem_filter.mp h₂).2
    by_contra hnot
    have hdisj : Disjoint (a₁ ∩ U) (a₂ ∩ U) := Finset.disjoint_left.mpr fun z hz₁ hz₂ =>
      hnot ⟨z, Finset.mem_inter.mpr ⟨hz₁, (Finset.mem_inter.mp hz₂).1⟩⟩
    have hle := Finset.card_le_card (Finset.union_subset (s := a₁ ∩ U) (t := a₂ ∩ U)
      Finset.inter_subset_right Finset.inter_subset_right)
    rw [Finset.card_union_of_disjoint hdisj] at hle
    omega
  have hLU_card_U : ∀ a ∈ LU, (a ∩ U).card = 2 := by
    intro a ha
    have h2 : 2 ≤ (a ∩ U).card := (Finset.mem_filter.mp ha).2
    have h3 : (a ∩ U).card ≤ 3 := hu_eq3 ▸ Finset.card_le_card Finset.inter_subset_right
    by_contra hne
    have haU : a ∩ U = U := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    have h2' : 1 < LU.card := by omega
    obtain ⟨a', ha', hne'⟩ := Finset.exists_mem_ne h2' a
    have ha'U : a' ∩ U ⊆ a ∩ a' := fun z hz =>
      Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (haU.symm ▸ (Finset.mem_inter.mp hz).2)).1, (Finset.mem_inter.mp hz).1⟩
    have hle1 := hlin a (Finset.mem_erase.mp (Finset.mem_filter.mp ha).1).2
      a' (Finset.mem_erase.mp (Finset.mem_filter.mp ha').1).2 hne'.symm
    have hge2 : 2 ≤ (a' ∩ U).card := (Finset.mem_filter.mp ha').2
    have := Finset.card_le_card ha'U
    omega
  -- The 3 lines of LU hit 3 distinct points of b, so every x ∈ b is hit by some a ∈ LU
  let pickB : Finset (Fin n) → Fin n := fun a => if h : a ∈ LU then (hall_hit a h).choose else ⟨0, by omega⟩
  have hpickB_inj : Set.InjOn pickB LU := by
    intro a₁ h₁ a₂ h₂ heq
    have h₁' : a₁ ∈ LU := Finset.mem_coe.mp h₁
    have h₂' : a₂ ∈ LU := Finset.mem_coe.mp h₂
    by_contra hne
    dsimp only [pickB] at heq; rw [dif_pos h₁', dif_pos h₂'] at heq
    set x := (hall_hit a₁ h₁').choose
    have hx1 := (hall_hit a₁ h₁').choose_spec
    have hx2 := (hall_hit a₂ h₂').choose_spec
    obtain ⟨y, hy⟩ := hLU_meet_U a₁ h₁' a₂ h₂'
    obtain ⟨hy1U, hy2⟩ := Finset.mem_inter.mp hy
    obtain ⟨hy1, hyU⟩ := Finset.mem_inter.mp hy1U
    have hxy : x ≠ y := fun h =>
      Finset.disjoint_left.mp (Finset.disjoint_sdiff : Disjoint b U) (Finset.mem_inter.mp hx1).2 (by change x ∈ U; rw [h]; exact hyU)
    have hsub : ({x, y} : Finset (Fin n)) ⊆ a₁ ∩ a₂ := by
      intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx1).1, (Finset.mem_inter.mp (by rw [heq]; exact hx2)).1⟩
      · exact Finset.mem_inter.mpr ⟨hy1, hy2⟩
    have hle1 := hlin a₁ (Finset.mem_erase.mp (Finset.mem_filter.mp h₁').1).2
      a₂ (Finset.mem_erase.mp (Finset.mem_filter.mp h₂').1).2 hne
    have h2le : 2 ≤ (a₁ ∩ a₂).card := (Finset.card_pair hxy).symm ▸ Finset.card_le_card hsub
    omega
  have hpickB_surj : LU.image pickB = b := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      dsimp only [pickB]; rw [dif_pos ha]; exact (Finset.mem_inter.mp (hall_hit a ha).choose_spec).2
    · rw [Finset.card_image_of_injOn hpickB_inj, hLU3, hb_eq3]
  -- Every line in L \ ({b} ∪ LU) has size 2 (one point in b, one in U), and two distinct such lines are DISJOINT!
  have hG_disj : ∀ e₁ ∈ L, ∀ e₂ ∈ L, e₁ ≠ b → e₂ ≠ b → e₁ ∉ LU → e₂ ∉ LU → e₁ ≠ e₂ → Disjoint e₁ e₂ := by
    intro e₁ he₁ e₂ he₂ hb₁ hb₂ hLU₁ hLU₂ hne
    have hpair : ∀ e ∈ L, e ≠ b → e ∉ LU → ∃ x ∈ b, ∃ y ∈ U, e = {x, y} := by
      intro e he heb heLU
      have h1 : (e ∩ U).card ≤ 1 := by
        have : ¬ 2 ≤ (e ∩ U).card := fun h => heLU (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨heb, he⟩, h⟩)
        omega
      have h2 : (e ∩ b).card ≤ 1 := hlin e he b hb heb
      have hpart : (e ∩ b).card + (e ∩ U).card = e.card := by
        have hun : (e ∩ b) ∪ (e ∩ U) = e := by
          ext z; simp only [Finset.mem_union, Finset.mem_inter, U, Finset.mem_sdiff, Finset.mem_univ, true_and]
          by_cases hzb : z ∈ b <;> tauto
        have hdj : Disjoint (e ∩ b) (e ∩ U) := Finset.disjoint_left.mpr fun z h1 h2 =>
          Finset.disjoint_left.mp (Finset.disjoint_sdiff : Disjoint b U) (Finset.mem_inter.mp h1).2 (Finset.mem_inter.mp h2).2
        rw [← Finset.card_union_of_disjoint hdj, hun]
      have hge2 := hsize e he
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (by omega : (e ∩ b).card = 1)
      obtain ⟨y, hy⟩ := Finset.card_eq_one.mp (by omega : (e ∩ U).card = 1)
      refine ⟨x, (Finset.mem_inter.mp (hx ▸ Finset.mem_singleton_self x)).2,
        y, (Finset.mem_inter.mp (hy ▸ Finset.mem_singleton_self y)).2, ?_⟩
      ext z
      have hun : z ∈ e ↔ z ∈ e ∩ b ∨ z ∈ e ∩ U := by
        simp only [Finset.mem_inter, U, Finset.mem_sdiff, Finset.mem_univ, true_and]
        by_cases hzb : z ∈ b <;> tauto
      rw [hun, hx, hy]; simp
    obtain ⟨x₁, hx₁b, y₁, hy₁U, heq₁⟩ := hpair e₁ he₁ hb₁ hLU₁
    obtain ⟨x₂, hx₂b, y₂, hy₂U, heq₂⟩ := hpair e₂ he₂ hb₂ hLU₂
    refine Finset.disjoint_left.mpr fun z hz₁ hz₂ => ?_
    rw [heq₁, Finset.mem_insert, Finset.mem_singleton] at hz₁
    rw [heq₂, Finset.mem_insert, Finset.mem_singleton] at hz₂
    have hdisj_bU : ∀ x ∈ b, ∀ y ∈ U, x ≠ y := fun x hx y hy h =>
      Finset.disjoint_left.mp (Finset.disjoint_sdiff : Disjoint b U) hx (h ▸ hy)
    rcases hz₁ with hz₁ | hz₁ <;> rcases hz₂ with hz₂ | hz₂
    · -- x₁ = x₂
      have hx12 : x₂ = x₁ := hz₂.symm.trans hz₁
      rw [hx12] at heq₂
      have hx_im : x₁ ∈ LU.image pickB := hpickB_surj.symm ▸ hx₁b
      obtain ⟨a, ha, hpa⟩ := Finset.mem_image.mp hx_im
      have hxa : x₁ ∈ a := by
        dsimp only [pickB] at hpa; rw [dif_pos ha] at hpa
        exact (Finset.mem_inter.mp (hpa ▸ (hall_hit a ha).choose_spec)).1
      have haL : a ∈ L := (Finset.mem_erase.mp (Finset.mem_filter.mp ha).1).2
      have hnot_in_a : ∀ y ∈ U, {x₁, y} ∈ L → y ∉ a ∩ U := by
        intro y hyU hL' hyin
        have hne' : a ≠ {x₁, y} := fun heq => by
          have h2 : (a ∩ U).card = 2 := hLU_card_U a ha
          have hsub : a ∩ U ⊆ {y} := by
            intro w hw; rw [heq] at hw; obtain ⟨hw1, hwU⟩ := Finset.mem_inter.mp hw
            simp only [Finset.mem_insert, Finset.mem_singleton] at hw1
            exact Finset.mem_singleton.mpr (hw1.resolve_left (fun h => hdisj_bU x₁ hx₁b w hwU h.symm))
          have := Finset.card_le_card hsub; simp at this; omega
        have hsub : ({x₁, y} : Finset (Fin n)) ⊆ a ∩ {x₁, y} := by
          intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl <;> exact Finset.mem_inter.mpr ⟨by first | exact hxa | exact (Finset.mem_inter.mp hyin).1, by simp⟩
        have h2le : 2 ≤ (a ∩ {x₁, y}).card := (Finset.card_pair (hdisj_bU x₁ hx₁b y hyU)).symm ▸ Finset.card_le_card hsub
        have hle1 := hlin a haL {x₁, y} hL' hne'
        omega
      have hy1_out : y₁ ∈ U \ (a ∩ U) := Finset.mem_sdiff.mpr ⟨hy₁U, hnot_in_a y₁ hy₁U (heq₁ ▸ he₁)⟩
      have hy2_out : y₂ ∈ U \ (a ∩ U) := Finset.mem_sdiff.mpr ⟨hy₂U, hnot_in_a y₂ hy₂U (heq₂ ▸ he₂)⟩
      have hcard1 : (U \ (a ∩ U)).card = 1 := by
        rw [Finset.card_sdiff_of_subset Finset.inter_subset_right, hu_eq3, hLU_card_U a ha]
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard1
      have hy12 : y₁ = y₂ := by
        rw [hw, Finset.mem_singleton] at hy1_out hy2_out; exact hy1_out.trans hy2_out.symm
      exact hne (by rw [heq₁, heq₂, hy12])
    · exact hdisj_bU x₁ hx₁b y₂ hy₂U (hz₁.symm.trans hz₂)
    · exact hdisj_bU x₂ hx₂b y₁ hy₁U (hz₂.symm.trans hz₁)
    · -- y₁ = y₂
      have hy12 : y₂ = y₁ := hz₂.symm.trans hz₁
      rw [hy12] at heq₂
      have hLU_y : (LU.filter (fun a => y₁ ∈ a)).card = 2 := by
        have hcard_er : (U.erase y₁).card = 2 := by rw [Finset.card_erase_of_mem hy₁U, hu_eq3]
        have hsum : ∑ a ∈ LU.filter (fun a => y₁ ∈ a), ((a ∩ U).erase y₁).card = 2 := by
          have hdisj : ((LU.filter (fun a => y₁ ∈ a)) : Set (Finset (Fin n))).PairwiseDisjoint (fun a => (a ∩ U).erase y₁) := by
            intro a₁ h₁ a₂ h₂ hdiff
            refine Finset.disjoint_left.mpr fun w hw₁ hw₂ => ?_
            have hwy : w ≠ y₁ := (Finset.mem_erase.mp hw₁).1
            have ha1L : a₁ ∈ L := (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_filter.mp h₁).1).1).2
            have ha2L : a₂ ∈ L := (Finset.mem_erase.mp (Finset.mem_filter.mp (Finset.mem_filter.mp h₂).1).1).2
            have hsub : ({w, y₁} : Finset (Fin n)) ⊆ a₁ ∩ a₂ := by
              intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
              rcases hv with rfl | rfl
              · exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_erase.mp hw₁).2).1,
                  (Finset.mem_inter.mp (Finset.mem_erase.mp hw₂).2).1⟩
              · exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp h₁).2, (Finset.mem_filter.mp h₂).2⟩
            have h2le : 2 ≤ (a₁ ∩ a₂).card := (Finset.card_pair hwy).symm ▸ Finset.card_le_card hsub
            have hle1 := hlin a₁ ha1L a₂ ha2L hdiff
            omega
          rw [← Finset.card_biUnion hdisj]
          have heq : (LU.filter (fun a => y₁ ∈ a)).biUnion (fun a => (a ∩ U).erase y₁) = U.erase y₁ := by
            ext w
            simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_erase, Finset.mem_inter]
            constructor
            · rintro ⟨a, _, hwy, _, hwU⟩; exact ⟨hwy, hwU⟩
            · rintro ⟨hwy, hwU⟩
              obtain ⟨a, haL, hwa, hya⟩ := hcov w y₁ hwy
              have hab : a ≠ b := fun h => hdisj_bU y₁ (h ▸ hya) y₁ hy₁U rfl
              have h2 : 2 ≤ (a ∩ U).card := by
                have hsub : ({w, y₁} : Finset (Fin n)) ⊆ a ∩ U := by
                  intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
                  rcases hv with rfl | rfl <;> exact Finset.mem_inter.mpr (by tauto)
                exact (Finset.card_pair hwy).symm ▸ Finset.card_le_card hsub
              have haLU : a ∈ LU := Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hab, haL⟩, h2⟩
              exact ⟨a, ⟨haLU, hya⟩, hwy, hwa, hwU⟩
          rw [heq, hcard_er]
        have hterm : ∀ a ∈ LU.filter (fun a => y₁ ∈ a), ((a ∩ U).erase y₁).card = 1 := by
          intro a ha
          have haLU := (Finset.mem_filter.mp ha).1
          have hyin : y₁ ∈ a ∩ U := Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp ha).2, hy₁U⟩
          rw [Finset.card_erase_of_mem hyin, hLU_card_U a haLU]
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, mul_one] at hsum
        exact hsum
      let B_y := (LU.filter (fun a => y₁ ∈ a)).image pickB
      have hBy_sub : B_y ⊆ b := (Finset.image_subset_image (Finset.filter_subset _ _)).trans hpickB_surj.subset
      have hBy_card : B_y.card = 2 := by
        rw [Finset.card_image_of_injOn (hpickB_inj.mono (Finset.filter_subset _ _)), hLU_y]
      have hnot_By : ∀ x ∈ b, {x, y₁} ∈ L → x ∉ B_y := by
        intro x hxb hL' hxBy
        obtain ⟨a, ha, hpa⟩ := Finset.mem_image.mp hxBy
        obtain ⟨haLU, hya⟩ := Finset.mem_filter.mp ha
        have hxa : x ∈ a := by
          dsimp only [pickB] at hpa; rw [dif_pos haLU] at hpa
          exact (Finset.mem_inter.mp (hpa ▸ (hall_hit a haLU).choose_spec)).1
        have haL : a ∈ L := (Finset.mem_erase.mp (Finset.mem_filter.mp haLU).1).2
        have hne' : a ≠ {x, y₁} := fun heq => by
          have h2 := hLU_card_U a haLU
          have hsub : a ∩ U ⊆ {y₁} := by
            intro w hw; rw [heq] at hw; obtain ⟨hw1, hwU⟩ := Finset.mem_inter.mp hw
            simp only [Finset.mem_insert, Finset.mem_singleton] at hw1
            exact Finset.mem_singleton.mpr (hw1.resolve_left (fun h => hdisj_bU x hxb w hwU h.symm))
          have := Finset.card_le_card hsub; simp at this; omega
        have hsub : ({x, y₁} : Finset (Fin n)) ⊆ a ∩ {x, y₁} := by
          intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl <;> exact Finset.mem_inter.mpr ⟨by first | exact hxa | exact hya, by simp⟩
        have h2le : 2 ≤ (a ∩ {x, y₁}).card := (Finset.card_pair (hdisj_bU x hxb y₁ hy₁U)).symm ▸ Finset.card_le_card hsub
        have hle1 := hlin a haL {x, y₁} hL' hne'
        omega
      have hx1_out : x₁ ∈ b \ B_y := Finset.mem_sdiff.mpr ⟨hx₁b, hnot_By x₁ hx₁b (heq₁ ▸ he₁)⟩
      have hx2_out : x₂ ∈ b \ B_y := Finset.mem_sdiff.mpr ⟨hx₂b, hnot_By x₂ hx₂b (heq₂ ▸ he₂)⟩
      have hcard1 : (b \ B_y).card = 1 := by rw [Finset.card_sdiff_of_subset hBy_sub, hb_eq3, hBy_card]
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard1
      have hx12 : x₁ = x₂ := by
        rw [hw, Finset.mem_singleton] at hx1_out hx2_out; exact hx1_out.trans hx2_out.symm
      exact hne (by rw [heq₁, heq₂, hx12])
  -- Color b with 0, the 3 lines of LU with 1, 2, 3, and all remaining 2-lines with 4 (all < 6 = n)!
  let eLU : LU ≃ Fin 3 := Fintype.equivOfCardEq (by simp [hLU3])
  let c : L → Fin n := fun A =>
    if h1 : A.1 = b then ⟨0, by omega⟩
    else if h2 : A.1 ∈ LU then ⟨1 + (eLU ⟨A.1, h2⟩).val, by have := (eLU ⟨A.1, h2⟩).isLt; omega⟩
    else ⟨4, by omega⟩
  refine ⟨c, fun A B hne hmeet hcol => ?_⟩
  have hval := congrArg Fin.val hcol
  dsimp only [c] at hval
  by_cases hA1 : A.1 = b <;> by_cases hB1 : B.1 = b
  · exact hne (Subtype.ext (hA1.trans hB1.symm))
  · rw [dif_pos hA1, dif_neg hB1] at hval
    by_cases hB2 : B.1 ∈ LU
    · rw [dif_pos hB2] at hval; dsimp only at hval; omega
    · rw [dif_neg hB2] at hval; dsimp only at hval; omega
  · rw [dif_neg hA1, dif_pos hB1] at hval
    by_cases hA2 : A.1 ∈ LU
    · rw [dif_pos hA2] at hval; dsimp only at hval; omega
    · rw [dif_neg hA2] at hval; dsimp only at hval; omega
  · rw [dif_neg hA1, dif_neg hB1] at hval
    by_cases hA2 : A.1 ∈ LU <;> by_cases hB2 : B.1 ∈ LU
    · rw [dif_pos hA2, dif_pos hB2] at hval; dsimp only at hval
      have := eLU.injective (Fin.ext (by omega : (eLU ⟨A.1, hA2⟩).val = (eLU ⟨B.1, hB2⟩).val))
      exact hne (Subtype.ext (congrArg (fun z : LU => z.1) this))
    · rw [dif_pos hA2, dif_neg hB2] at hval; dsimp only at hval
      have := (eLU ⟨A.1, hA2⟩).isLt; omega
    · rw [dif_neg hA2, dif_pos hB2] at hval; dsimp only at hval
      have := (eLU ⟨B.1, hB2⟩).isLt; omega
    · have hd := Finset.disjoint_iff_inter_eq_empty.mp
        (hG_disj A.1 A.2 B.1 B.2 hA1 hB1 hA2 hB2 (fun h => hne (Subtype.ext h)))
      rw [hd] at hmeet; exact Finset.not_nonempty_empty hmeet

end E19NearBlock

end

namespace OMA.R_Erdos19_erdos_19_R1_H1_R1_H2_R1

open scoped Classical

/-- Small-order finite residual (`n ≤ 12`): linear spaces with `4 ≤ n - |b| ≤ 6` outside a
maximum-size block `b` and at least one other block of size `≥ 3`. -/
def H1 : Prop := ∀ (n : ℕ) (L : Finset (Finset (Fin n))),
    n ≤ 12 →
    (∀ a ∈ L, 2 ≤ a.card) →
    (∀ a ∈ L, ∀ b ∈ L, a ≠ b → (a ∩ b).card ≤ 1) →
    (∀ i j : Fin n, i ≠ j → ∃ e ∈ L, i ∈ e ∧ j ∈ e) →
    (∃ S ⊆ L, (∀ a ∈ L, 3 ≤ a.card → a ∈ S) ∧
      ∀ a ∈ S, n ≤ ((S.erase a).filter fun b => (a ∩ b).Nonempty).card) →
    (∃ b ∈ L, (∀ a ∈ L, a.card ≤ b.card) ∧ 4 ≤ n - b.card ∧ n - b.card ≤ 6 ∧
      3 ≤ b.card ∧ b.card ≤ 8 ∧ ∃ a ∈ L, a ≠ b ∧ 3 ≤ a.card) →
    ∃ c : L → Fin n, ∀ A B : L, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B

/-- Intermediate finite residual (`13 ≤ n ≤ 17`): linear spaces with `5 ≤ n - |b| ≤ 6` outside
a maximum-size block `b` (`b.card = 8` if `n - |b| = 5`, `7 ≤ b.card ≤ 11` if `n - |b| = 6`)
and at least one other block of size `≥ 3`. -/
def H2 : Prop := ∀ (n : ℕ) (L : Finset (Finset (Fin n))),
    13 ≤ n → n ≤ 17 →
    (∀ a ∈ L, 2 ≤ a.card) →
    (∀ a ∈ L, ∀ b ∈ L, a ≠ b → (a ∩ b).card ≤ 1) →
    (∀ i j : Fin n, i ≠ j → ∃ e ∈ L, i ∈ e ∧ j ∈ e) →
    (∃ S ⊆ L, (∀ a ∈ L, 3 ≤ a.card → a ∈ S) ∧
      ∀ a ∈ S, n ≤ ((S.erase a).filter fun b => (a ∩ b).Nonempty).card) →
    (∃ b ∈ L, (∀ a ∈ L, a.card ≤ b.card) ∧
      ((n - b.card = 5 ∧ b.card = 8) ∨ (n - b.card = 6 ∧ 7 ≤ b.card ∧ b.card ≤ 11)) ∧
      ∃ a ∈ L, a ≠ b ∧ 3 ≤ a.card) →
    ∃ c : L → Fin n, ∀ A B : L, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B

theorem main : H1 → H2 → OMA.R_Erdos19_erdos_19_R1_H1_R1.H2 := by
  intro h1 h2 n L hsize hlin hcov hcore ⟨b₀, hb₀, hb₀_near⟩
  -- Replace b₀ by a maximum-size block b ∈ L (still satisfying n ≤ b.card + 6)
  obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image L Finset.card ⟨b₀, hb₀⟩
  have hb_near : n ≤ b.card + 6 := hb₀_near.trans (Nat.add_le_add_right (hmax b₀ hb₀) 6)
  have hbu : b.card + (Finset.univ \ b).card = n := by
    have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ b)
    rw [Finset.card_univ, Fintype.card_fin] at this
    omega
  have hu_eq : (Finset.univ \ b).card = n - b.card := by omega
  have hu_le6 : (Finset.univ \ b).card ≤ 6 := by omega
  -- Case 1: every block other than b has size 2
  by_cases hsingle : ∀ a ∈ L, a ≠ b → a.card = 2
  · exact E19NearBlock.color_single_big_block L b hb hsize hlin hsingle
  have hex3 : ∃ a ∈ L, a ≠ b ∧ 3 ≤ a.card := by
    push Not at hsingle
    obtain ⟨a, ha, hab, hne2⟩ := hsingle
    have h2 := hsize a ha
    exact ⟨a, ha, hab, by omega⟩
  have hb3 : 3 ≤ b.card := by
    obtain ⟨a, ha, _, ha3⟩ := hex3
    exact ha3.trans (hmax a ha)
  -- Case 2: u = n - b.card ≤ 3 (closed for all n)
  by_cases hu3 : (Finset.univ \ b).card ≤ 3
  · exact E19NearBlock.color_u_le_three L b hb hsize hlin hcov hmax hu3
  -- Case 3: u = 4 and b.card ≥ 7 (Δ(L_U) ≤ 5)
  by_cases hu4 : (Finset.univ \ b).card = 4
  · by_cases hb7 : 7 ≤ b.card
    · exact E19NearBlock.color_by_u_bound L b hb hsize hlin hcov (D := 5)
        (fun s hs2 hsu => by rw [hu4] at hsu ⊢; interval_cases s <;> omega) (by omega)
    · exact h1 n L (by omega) hsize hlin hcov hcore
        ⟨b, hb, hmax, by omega, by omega, hb3, by omega, hex3⟩
  -- Case 4: u = 5 and b.card ≥ 9 (Δ(L_U) ≤ 7)
  by_cases hu5 : (Finset.univ \ b).card = 5
  · by_cases hb9 : 9 ≤ b.card
    · exact E19NearBlock.color_by_u_bound L b hb hsize hlin hcov (D := 7)
        (fun s hs2 hsu => by rw [hu5] at hsu ⊢; interval_cases s <;> omega) (by omega)
    · by_cases hn12 : n ≤ 12
      · exact h1 n L hn12 hsize hlin hcov hcore
          ⟨b, hb, hmax, by omega, by omega, hb3, by omega, hex3⟩
      · exact h2 n L (by omega) (by omega) hsize hlin hcov hcore
          ⟨b, hb, hmax, Or.inl ⟨by omega, by omega⟩, hex3⟩
  -- Case 5: u = 6 and b.card ≥ 12 (Δ(L_U) ≤ 10, closes all n ≥ 18)
  have hu6 : (Finset.univ \ b).card = 6 := by omega
  by_cases hb12 : 12 ≤ b.card
  · exact E19NearBlock.color_by_u_bound L b hb hsize hlin hcov (D := 10)
      (fun s hs2 hsu => by rw [hu6] at hsu ⊢; interval_cases s <;> omega) (by omega)
  · by_cases hn12 : n ≤ 12
    · exact h1 n L hn12 hsize hlin hcov hcore
        ⟨b, hb, hmax, by omega, by omega, hb3, by omega, hex3⟩
    · exact h2 n L (by omega) (by omega) hsize hlin hcov hcore
        ⟨b, hb, hmax, Or.inr ⟨by omega, by omega, by omega⟩, hex3⟩

end OMA.R_Erdos19_erdos_19_R1_H1_R1_H2_R1

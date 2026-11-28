import OMAReductions.R_BollobasEldridgeCatlinConjecture_bollobas_eldridge_catlin_conjecture_variants_maxDegree_le_two_R1_H2_R1

/-!
Short-cycle factor case for graphs of maximum degree at most two: every component of C has at most
five vertices (isolated vertices, triangles, quadrilaterals, and pentagons).
The pure triangle-factor base case uses the Kierstead-Kostochka proof of the Hajnal-Szemeredi
equitable coloring theorem, and the quadrilateral and pentagon cases follow the Aigner-Brandt
local repacking and degree-counting method via verified finite witness reflection.
-/

namespace E914P
open scoped Classical
namespace TerminalVertex
variable {α : Type*} [Fintype α] [DecidableEq α]
omit [DecidableEq α]
omit [Fintype α] in
lemma exists_nodup_chain'
    {R : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen R a b) (hab : a ≠ b) :
    ∃ l : List α, l.Nodup ∧ l.IsChain R ∧ l.head? = some a ∧
    l.getLast? = some b ∧ 2 ≤ l.length := by
  obtain ⟨l, hl⟩ : ∃ l : List α, List.IsChain R l ∧ l.head? = some a ∧ l.getLast? =
    some b := by
    have h_contradiction : ∀ {x y : α}, Relation.ReflTransGen R x y → ∃ l : List α,
      List.IsChain R l ∧ l.head? = some x ∧ l.getLast? = some y := by
      intro x y hxy
      induction hxy with
      | refl =>
        exact ⟨[x], List.isChain_singleton _, rfl, rfl⟩;
      | @tail mid y hxy hstep ih =>
        obtain ⟨l, hl₁, hl₂, hl₃⟩ := ih; use l ++ [y]; simp_all;
        exact List.isChain_append.mpr ⟨hl₁, by aesop⟩;
    exact h_contradiction h;
  obtain ⟨l, hl_min⟩ : ∃ l : List α, List.IsChain R l ∧ l.head? = some a ∧ l.getLast? =
    some b ∧ ∀ l' : List α, List.IsChain R l' → l'.head? = some a → l'.getLast? =
      some b → l.length ≤ l'.length := by
    have h_well_founded : WellFounded fun l l' : { l : List α // List.IsChain R l ∧ l.head? =
      some a ∧ l.getLast? = some b } => l.val.length < l'.val.length := by
      rw [WellFounded.wellFounded_iff_has_min];
      intro s hs;
      have h_well_founded : WellFounded fun l l' : ℕ => l < l' := by
        exact wellFounded_lt;
      have := h_well_founded.has_min (Set.image (fun x : { l : List α // List.IsChain R l ∧
        l.head? = some a ∧ l.getLast? = some b } => x.val.length) s) ⟨_,
          Set.mem_image_of_mem _ hs.choose_spec⟩; aesop;
    have := h_well_founded.has_min { l : { l : List α // List.IsChain R l ∧ l.head? = some a ∧
      l.getLast? = some b } | True } ⟨⟨l, hl⟩, trivial⟩; aesop;
  by_cases h_dup : ∃ i j : Fin l.length, i < j ∧ l.get i = l.get j;
  · obtain ⟨i, j, hij, h_eq⟩ := h_dup;
    have h_shorter : ∃ l' : List α, List.IsChain R l' ∧ l'.head? = some a ∧ l'.getLast? =
      some b ∧ l'.length < l.length := by
      refine ⟨l.take i.val ++ l.drop j.val, ?_, ?_, ?_, ?_⟩ <;> simp_all;
      · refine List.isChain_append.mpr ⟨?_, ?_, ?_⟩;
        · have := hl_min.1;
          exact List.IsChain.take this ↑i;
        · have := hl_min.1;
          exact List.IsChain.drop this ↑j;
        · rcases i with ⟨_ | i, hi⟩ <;> rcases j with ⟨_ | j, hj⟩ <;>
            simp_all [List.getLast?_take, List.head?_drop];
          have := List.isChain_iff_getElem.mp hl_min.1;
          convert this i (by omega) using 1;
          · rw [List.getElem?_eq_getElem]; aesop;
          · exact h_eq.symm;
      · rcases i with ⟨_ | i, hi⟩ <;> rcases j with ⟨_ | j, hj⟩ <;>
          simp_all [List.take];
        · cases l <;> aesop;
        · cases l <;> aesop;
      · rw [List.getLast?_drop]; aesop;
      · linarith [show (i : ℕ) < j from hij, Nat.sub_add_cancel (show (j : ℕ) ≤
        l.length from j.2.le)];
    grind;
  · refine ⟨l, ?_, hl_min.1, hl_min.2.1, hl_min.2.2.1, ?_⟩;
    · exact List.nodup_iff_injective_get.mpr fun i j hij => le_antisymm (not_lt.mp fun hi =>
      h_dup ⟨j, i, hi, hij.symm⟩) (not_lt.mp fun hj => h_dup ⟨i, j, hj, hij⟩);
    · rcases l with (_ | ⟨x, _ | ⟨y, l⟩⟩) <;> simp_all;
      grind
omit [Fintype α] [DecidableEq α] in
lemma chain_to_reflTransGen
    {R : α → α → Prop} {l : List α} {a b : α}
    (hchain : l.IsChain R) (hhead : l.head? = some a)
    (hlast : l.getLast? = some b) :
    Relation.ReflTransGen R a b := by
  induction l generalizing a b with
  | nil =>
    cases hhead;
  | cons x l ih =>
    cases l with
    | nil => simp_all; rfl
    | cons y l =>
      simp at hhead; subst hhead
      exact Relation.ReflTransGen.head (List.isChain_cons_cons.mp hchain |>.1)
        (ih (List.isChain_cons_cons.mp hchain |>.2) rfl hlast)
omit [Fintype α] [DecidableEq α] in
lemma chain_to_restricted_reflTransGen
    {R : α → α → Prop} {l : List α} {a b w : α}
    (hchain : l.IsChain R) (hhead : l.head? = some a)
    (hlast : l.getLast? = some b)
    (hw : w ∉ l ∨ w = b) :
    Relation.ReflTransGen (fun x y => R x y ∧ x ≠ w) a b := by
      induction l generalizing a b w with
      | nil =>
        simp_all
      | cons x xs hx =>
        simp_all
        cases xs <;> simp_all;
        · rfl;
        · grind +suggestions
omit [Fintype α] [DecidableEq α] in
lemma nodup_chain_suffix
    {R : α → α → Prop} {l : List α} {a b w : α}
    (hchain : l.IsChain R) (hnodup : l.Nodup)
    (hhead : l.head? = some a) (hlast : l.getLast? = some b)
    (hw_mem : w ∈ l) (hw_ne_a : w ≠ a) (_hw_ne_b : w ≠ b) :
    ∃ l' : List α, l'.IsChain R ∧ l'.Nodup ∧ l'.head? = some w ∧
      l'.getLast? = some b ∧ l'.length < l.length ∧ a ∉ l' := by
  obtain ⟨l₁, l₂, hl₁, hl₂⟩ : ∃ l₁ l₂ : List α, l = l₁ ++ w :: l₂ := by
    exact List.mem_iff_append.mp hw_mem;
  refine ⟨w :: l₂, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all;
  · exact List.IsChain.suffix hchain (List.suffix_append _ _);
  · grind;
  · cases l₁ <;> aesop;
  · cases l₁ <;> aesop
set_option maxHeartbeats 800000 in
omit [Fintype α] in
theorem exists_terminal_vertex
    [Finite α]
    (R : α → α → Prop) (r : α)
    (W₀ : α) (hW₀ : Relation.ReflTransGen R W₀ r) (hW₀_ne : W₀ ≠ r) :
    ∃ W : α, Relation.ReflTransGen R W r ∧ W ≠ r ∧
      ∀ C : α, Relation.ReflTransGen R C r → C ≠ W →
        Relation.ReflTransGen (fun a b => R a b ∧ a ≠ W) C r := by
  let := Fintype.ofFinite α
  by_contra! h_contra;
  obtain ⟨W_star, hW_star⟩ : ∃ W_star : α, Relation.ReflTransGen R W_star r ∧
    W_star ≠ r ∧ ∀ W' : α, Relation.ReflTransGen R W' r → W' ≠ r →
      (Nat.card {C : α | Relation.ReflTransGen R C r ∧ C ≠ W' ∧
        ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ W') C r}) ≥
          (Nat.card {C : α | Relation.ReflTransGen R C r ∧ C ≠ W_star ∧
            ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ W_star) C r}) := by
    have h_finite : Set.Finite {W : α | Relation.ReflTransGen R W r ∧ W ≠ r} := by
      exact Set.toFinite _;
    have := h_finite.toFinset.exists_min_image (fun W => Nat.card { C :
      α | Relation.ReflTransGen R C r ∧ C ≠ W ∧ ¬Relation.ReflTransGen (fun a b =>
        R a b ∧ a ≠ W) C r }) ⟨W₀, by aesop⟩; aesop;
  obtain ⟨C, hC⟩ : ∃ C : α, Relation.ReflTransGen R C r ∧ C ≠ W_star ∧
    ¬Relation.ReflTransGen (fun a b => R a b ∧
      a ≠ W_star) C r := h_contra W_star hW_star.left hW_star.right.left;
  have h_block_subset : ∀ D : α, Relation.ReflTransGen R D r → D ≠ C →
    ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ C) D r → D ≠ W_star ∧
      ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ W_star) D r := by
    intro D hD hD_ne_C hD_not_reach_C
    constructor;
    · rintro rfl;
      obtain ⟨l, hl_nodup, hl_chain, hl_head, hl_last, hl_length⟩ : ∃ l : List α, l.Nodup ∧
        l.IsChain R ∧ l.head? = some D ∧ l.getLast? = some r ∧ 2 ≤ l.length := by
        apply exists_nodup_chain' hD hW_star.2.1;
      by_cases hC_in_l : C ∈ l;
      · obtain ⟨l', hl'_chain, hl'_nodup, hl'_head, hl'_last, hl'_length, hl'_not_D⟩ :
        ∃ l' : List α, l'.IsChain R ∧ l'.Nodup ∧ l'.head? = some C ∧ l'.getLast? =
          some r ∧ l'.length < l.length ∧ D ∉ l' := by
          apply nodup_chain_suffix hl_chain hl_nodup hl_head hl_last hC_in_l;
          · grobner;
          · rintro rfl; simp_all [Relation.ReflTransGen.refl];
        have := chain_to_restricted_reflTransGen hl'_chain hl'_head hl'_last (Or.inl hl'_not_D);
          simp_all;
      · exact hD_not_reach_C
          (chain_to_restricted_reflTransGen hl_chain hl_head hl_last (Or.inl hC_in_l))
    · intro hD_reach_W_star;
      obtain ⟨l, hl_nodup, hl_chain, hl_head, hl_last, hl_length⟩ : ∃ l : List α, l.Nodup ∧
        l.IsChain (fun a b => R a b ∧ a ≠ W_star) ∧ l.head? = some D ∧ l.getLast? =
          some r ∧ 2 ≤ l.length := by
        apply exists_nodup_chain' hD_reach_W_star;
        grind +suggestions;
      by_cases hC_in_l : C ∈ l;
      · obtain ⟨l', hl'_chain, hl'_nodup, hl'_head, hl'_last, hl'_length, hl'_not_in_l⟩ :
        ∃ l' : List α, l'.IsChain (fun a b => R a b ∧ a ≠ W_star) ∧ l'.Nodup ∧ l'.head? =
          some C ∧ l'.getLast? = some r ∧ l'.length < l.length ∧ D ∉ l' := by
          apply_rules [nodup_chain_suffix];
          grind;
        have hC_reach_r : Relation.ReflTransGen (fun a b => R a b ∧ a ≠ W_star) C r := by
          exact chain_to_reflTransGen hl'_chain hl'_head hl'_last;
        exact hC.2.2 hC_reach_r;
      · refine hD_not_reach_C ?_;
        have h_chain_to_restricted_reflTransGen : Relation.ReflTransGen (fun a b => R a b ∧
          a ≠ W_star ∧ a ≠ C) D r := by
          have h_chain_to_restricted_aux : ∀ {l : List α}, l.Nodup →
            l.IsChain (fun a b => R a b ∧ a ≠ W_star) → l.head? = some D → l.getLast? =
              some r → C ∉ l → Relation.ReflTransGen (fun a b => R a b ∧ a ≠ W_star ∧
                a ≠ C) D r := by
            intros l hl_nodup hl_chain hl_head hl_last hC_in_l;
            convert chain_to_restricted_reflTransGen hl_chain hl_head hl_last _ using 1;
            rotate_left
            focus
              exact C
            · exact Or.inl hC_in_l;
            · simp only [and_assoc];
          exact h_chain_to_restricted_aux hl_nodup hl_chain hl_head hl_last hC_in_l;
        exact Relation.ReflTransGen.mono
          (fun a b hab => And.intro hab.1 hab.2.2) D r h_chain_to_restricted_reflTransGen;
  have h_block_card_lt : Nat.card {D : α | Relation.ReflTransGen R D r ∧ D ≠ C ∧
    ¬Relation.ReflTransGen (fun a b => R a b ∧
      a ≠ C) D r} < Nat.card {D : α | Relation.ReflTransGen R D r ∧ D ≠ W_star ∧
        ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ W_star) D r} := by
    apply_rules [Set.ncard_lt_ncard];
    · simp_all [Set.ssubset_def, Set.subset_def];
      exact ⟨C, hC.1, by tauto, hC.2.2, by tauto⟩;
    · exact Set.toFinite _;
  grind
end TerminalVertex
open Finset
lemma weight_sum_lower_bound {ι : Type*}
    (F : Finset ι) (s : ι → ℕ) (q t c_max : ℕ)
    (hq : 1 ≤ q) (ht : q < t)
    (hF_card : F.card ≥ t - q + c_max)
    (hc_max_le : c_max ≤ q)
    (hc_max_pos : 1 ≤ c_max)
    (hs_pos : ∀ i ∈ F, 1 ≤ s i)
    (hs_le : ∀ i ∈ F, s i ≤ c_max) :
    ∑ i ∈ F, (q : ℚ) / (s i : ℚ) ≥ (t : ℚ) := by
  classical
  have h_term_bound : ∀ i ∈ F, (q : ℚ) / s i ≥ q / c_max := by
    field_simp;
    exact fun i hi => by
      rw [le_div_iff₀] <;> norm_cast <;>
        linarith [hs_pos i hi, hs_le i hi]
  refine le_trans ?_ (Finset.sum_le_sum h_term_bound);
  simp +zetaDelta at *;
  rw [mul_div, le_div_iff₀] <;> norm_cast;
  nlinarith [Nat.sub_add_cancel ht.le]
lemma weight_function_contradiction
    {α β : Type*} [DecidableEq β]
    (A : Finset α) (B : Finset β)
    (Solo : α → Finset β)
    (q t s : ℕ)
    (hq : 1 ≤ q) (ht : q < t) (_hs : 1 ≤ s)
    (hA_card_le : A.card ≤ t * s)
    (hB_card : B.card = q * s + 1)
    (hS_sub : ∀ a ∈ A, Solo a ⊆ B)
    (_hS_pos : ∀ a ∈ A, (Solo a).Nonempty → 1 ≤ (Solo a).card)
    (_hS_le : ∀ a ∈ A, (Solo a).card ≤ q)
    (h_lower : ∀ y ∈ B,
      let Sy := A.filter (fun z => y ∈ Solo z)
      ∃ c_max : ℕ, 1 ≤ c_max ∧ c_max ≤ q ∧
        Sy.card ≥ t - q + c_max ∧
        (∀ z ∈ Sy, (Solo z).card ≤ c_max) ∧
        (∀ z ∈ Sy, 1 ≤ (Solo z).card)) :
    False := by
  classical
  set μ := ∑ a ∈ A, ∑ b ∈ Solo a, (q : ℚ) / ((Solo a).card : ℚ)
  have mu_upper : μ ≤ q * (t * s) := by
    refine le_trans (Finset.sum_le_sum (g := fun _ => (q : ℚ)) ?_) ?_;
    · intro a ha; by_cases ha' : Solo a = ∅ <;> simp_all;
      rw [
        mul_div_cancel₀ _
          (Nat.cast_ne_zero.mpr
            (Finset.card_ne_zero_of_mem
              (Classical.choose_spec (Finset.nonempty_of_ne_empty ha'))))]
    · simp +zetaDelta at *;
      norm_cast; nlinarith;
  have mu_lower : ∑ y ∈ B, ∑ z ∈ A, (if y ∈ Solo z then (q : ℚ) / ((Solo z).card : ℚ)
    else 0) ≥ t * (q * s + 1) := by
    have mu_lower : ∀ y ∈ B, ∑ z ∈ A, (if y ∈ Solo z then (q : ℚ) /
      ((Solo z).card : ℚ) else 0) ≥ t := by
      intro y hy
      obtain ⟨c_max, hc1, hcq, hcard, hle, hpos⟩ := h_lower y hy
      have h_lower_bound : ∑ z ∈ A.filter (fun z => y ∈ Solo z), (q : ℚ) /
        ((Solo z).card : ℚ) ≥ t := by
        convert weight_sum_lower_bound _ _ q t c_max hq ht hcard hcq hc1 hpos hle;
      simpa [Finset.sum_ite] using h_lower_bound;
    exact le_trans (by simp [mul_comm, hB_card]) (Finset.sum_le_sum mu_lower);
  have mu_fubini : ∑ y ∈ B, ∑ z ∈ A, (if y ∈ Solo z then (q : ℚ) / ((Solo z).card : ℚ)
    else 0) = ∑ z ∈ A, ∑ y ∈ B, (if y ∈ Solo z then (q : ℚ) / ((Solo z).card : ℚ)
      else 0) := by
    exact Finset.sum_comm;
  have mu_simplified : ∑ z ∈ A, ∑ y ∈ B, (if y ∈ Solo z then (q : ℚ) /
    ((Solo z).card : ℚ) else 0) = ∑ z ∈ A, ∑ y ∈ Solo z, (q : ℚ) / ((Solo z).card : ℚ)
      := by
    simp +contextual [Finset.inter_eq_right.mpr (hS_sub _ _)];
  nlinarith [(by norm_cast : (1 : ℚ) ≤ q), (by norm_cast : (q : ℚ) < t),
    (by norm_cast : (1 : ℚ) ≤ s)]
namespace HajnalSzemeredi
open Finset Function SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
lemma cannot_reach_transitive {α : Type*} [Finite α]
    (R : α → α → Prop) (target U W C : α)
    (hW : ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ U) W target)
    (hC : ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ W) C target)
    (_hCU : C ≠ U) :
    ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ U) C target := by
  classical
  let := Fintype.ofFinite α
  contrapose! hC;
  induction hC;
  · rfl;
  · grind +locals
lemma mutual_dependency_impossible {α : Type*} [Finite α]
    (R : α → α → Prop) (target U W : α)
    (hUW : U ≠ W)
    (hU_acc : Relation.ReflTransGen R U target)
    (hW_acc : Relation.ReflTransGen R W target)
    (hU_needs_W : ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ W) U target)
    (hW_needs_U : ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ U) W target) :
    False := by
  classical
  let := Fintype.ofFinite α
  obtain ⟨l, hl_nodup, hl_chain, hl_head, hl_last⟩ : ∃ l : List α, l.Nodup ∧
    l.IsChain R ∧ l.head? = some U ∧ l.getLast? = some target ∧ 2 ≤ l.length := by
    by_cases h : U = target <;> simp_all [Relation.ReflTransGen.refl];
    exact TerminalVertex.exists_nodup_chain' hU_acc h;
  have hW_in_l : W ∈ l := by
    grind +suggestions;
  obtain ⟨l', hl'_chain, hl'_nodup, hl'_head, hl'_last, hl'_length, hl'_not_U⟩ :
    ∃ l' : List α, l'.IsChain R ∧ l'.Nodup ∧ l'.head? = some W ∧ l'.getLast? =
      some target ∧ l'.length < l.length ∧ U ∉ l' := by
    apply TerminalVertex.nodup_chain_suffix hl_chain hl_nodup hl_head hl_last.left hW_in_l hUW.symm;
    contrapose! hW_needs_U; aesop;
  contrapose! hW_needs_U;
  grind +suggestions
lemma terminal_set_members_are_terminal {α : Type*} [Finite α] [DecidableEq α]
    (R : α → α → Prop) (target : α)
    (acc : Finset α)
    (hacc : ∀ c ∈ acc, Relation.ReflTransGen R c target)
    (U : α) (hU_acc : U ∈ acc)
    (hU_nonterm : ∃ C ∈ acc, C ≠ U ∧
      ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ U) C target)
    (T_U : Finset α)
    (hT_U_def : T_U = acc.filter (fun c => c ≠ U ∧
      ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ U) c target))
    (hT_U_min : ∀ V ∈ acc,
      (∃ C ∈ acc, C ≠ V ∧ ¬Relation.ReflTransGen (fun a b => R a b ∧
        a ≠ V) C target) →
      T_U.card ≤ (acc.filter (fun c => c ≠ V ∧
        ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ V) c target)).card)
    (W : α) (hW : W ∈ T_U) :
    ∀ C ∈ acc, C ≠ W →
      Relation.ReflTransGen (fun a b => R a b ∧ a ≠ W) C target := by
  classical
  let := Fintype.ofFinite α
  intro C hC hCW; contrapose! hT_U_min; simp_all;
  refine ⟨W, hW.1, ⟨C, hC, hCW, hT_U_min⟩, ?_⟩;
  refine Finset.card_lt_card ?_;
  constructor;
  · intro c hc; simp_all;
    refine ⟨?_, ?_⟩;
    · grind +suggestions;
    · intro h;
      apply cannot_reach_transitive R target U W c;
      · exact hW.2.2;
      · exact hc.2.2;
      · grind;
      · exact h;
  · rw [Finset.not_subset]; use W; aesop;
noncomputable def cClass (f : V → Fin k) (c : Fin k) : Finset V :=
  Finset.univ.filter (fun v => f v = c)
omit [DecidableEq V] in
@[simp]
lemma mem_cClass (f : V → Fin k) (c : Fin k) (v : V) :
    v ∈ cClass f c ↔ f v = c := by simp [cClass]
def IsProper (G : SimpleGraph V) (f : V → α) : Prop :=
  ∀ v w : V, G.Adj v w → f v ≠ f w
def IsEquitable (f : V → Fin k) : Prop :=
  ∀ c₁ c₂ : Fin k, (cClass f c₁).card ≤ (cClass f c₂).card + 1
def HasEquitableColoring (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ f : V → Fin k, IsProper G f ∧ IsEquitable f
omit [DecidableEq V] in
lemma hasEquitableColoring_of_iso {W : Type*} [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} {k : ℕ}
    (e : H ≃g G) :
    HasEquitableColoring H k → HasEquitableColoring G k := by
  classical
  rintro ⟨f, hf_proper, hf_equitable⟩
  refine ⟨fun v => f (e.symm v), ?_, ?_⟩
  · intro v w hvw h_eq
    exact hf_proper (e.symm v) (e.symm w) (e.symm.map_adj_iff.mpr hvw) h_eq
  · have h_card : ∀ c : Fin k,
        (cClass (fun v : V => f (e.symm v)) c).card = (cClass f c).card := by
      intro c
      refine Finset.card_bij
        (s := cClass (fun v : V => f (e.symm v)) c) (t := cClass f c)
        (fun v _ => e.symm v) ?_ ?_ ?_
      · intro v hv
        simpa [cClass] using hv
      · intro a _ b _ h
        exact e.symm.injective h
      · intro w hw
        refine ⟨e w, ?_, by simp⟩
        simpa [cClass] using hw
    intro c₁ c₂
    rw [h_card c₁, h_card c₂]
    exact hf_equitable c₁ c₂
def IsMovable (G : SimpleGraph V) (f : V → Fin k) (v : V) (c : Fin k) : Prop :=
  f v ≠ c ∧ ∀ w : V, f w = c → ¬G.Adj v w
def recolor (f : V → Fin k) (v : V) (c : Fin k) : V → Fin k :=
  Function.update f v c
omit [DecidableEq V] in
lemma cClass_card_sum (f : V → Fin k) :
    ∑ c : Fin k, (cClass f c).card = Fintype.card V := by
  have h_insert : ∑ c : Fin k, Finset.card (Finset.filter (fun v => f v = c) Finset.univ) =
    Finset.card (Finset.univ : Finset V) := by
    simp only [card_filter]
    rw [Finset.sum_comm]; aesop
  exact h_insert
omit [Fintype V] in
lemma recolor_preserves_proper {G : SimpleGraph V}
    {f : V → Fin k} (hf : IsProper G f) {v : V} {c : Fin k}
    (hm : IsMovable G f v c) :
    IsProper G (recolor f v c) := by
  classical
  intro w x hwx hwx_color
  by_cases hw : w = v
  · subst w
    by_cases hx : x = v
    · subst x
      exact hwx.ne rfl
    · have hx_color : f x = c := by
        simpa [recolor, Function.update, hx] using hwx_color.symm
      exact (hm.2 x hx_color) hwx
  · by_cases hx : x = v
    · subst x
      have hw_color : f w = c := by
        simpa [recolor, Function.update, hw] using hwx_color
      exact (hm.2 w hw_color) hwx.symm
    · exact hf w x hwx (by simpa [recolor, Function.update, hw, hx] using hwx_color)
lemma cClass_recolor_old {f : V → Fin k} {v : V} {c : Fin k}
    (hvc : f v ≠ c) :
    cClass (recolor f v c) (f v) = (cClass f (f v)).erase v := by
  ext w; by_cases hw : w = v <;> simp [*, recolor];
  exact Ne.symm hvc
lemma cClass_recolor_new {f : V → Fin k} {v : V} {c : Fin k}
    (hvc : f v ≠ c) :
    cClass (recolor f v c) c = insert v (cClass f c) := by
  ext w; by_cases hw : w = v <;> simp [*, recolor];
lemma cClass_recolor_other {f : V → Fin k} {v : V} {c d : Fin k}
    (hd1 : d ≠ f v) (hd2 : d ≠ c) :
    cClass (recolor f v c) d = cClass f d := by
  ext w; by_cases hw : w = v <;> simp [*, recolor];
  aesop
lemma cClass_recolor_old_card {f : V → Fin k} {v : V} {c : Fin k}
    (hvc : f v ≠ c) :
    (cClass (recolor f v c) (f v)).card = (cClass f (f v)).card - 1 := by
  rw [cClass_recolor_old hvc, Finset.card_erase_of_mem]; aesop
lemma cClass_recolor_new_card {f : V → Fin k} {v : V} {c : Fin k}
    (hvc : f v ≠ c) :
    (cClass (recolor f v c) c).card = (cClass f c).card + 1 := by
  rw [cClass_recolor_new hvc, Finset.card_insert_of_notMem]; aesop
lemma cClass_recolor_other_card {f : V → Fin k} {v : V} {c d : Fin k}
    (hd1 : d ≠ f v) (hd2 : d ≠ c) :
    (cClass (recolor f v c) d).card = (cClass f d).card := by
  rw [cClass_recolor_other hd1 hd2]
instance deleteEdges_decidable (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set (Sym2 V)) [DecidablePred (· ∈ s)] :
    DecidableRel (G.deleteEdges s).Adj := by
  intro v w; simp only [deleteEdges_adj]; infer_instance
omit [DecidableEq V] in
lemma maxDegree_deleteEdges_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set (Sym2 V)) [DecidablePred (· ∈ s)] :
    (G.deleteEdges s).maxDegree ≤ G.maxDegree := by
  apply_rules [SimpleGraph.maxDegree_le_of_forall_degree_le]
  intro v
  have h_deg_le : (G.deleteEdges s).degree v ≤ G.degree v := by
    exact Finset.card_mono fun x hx => by aesop
  linarith [h_deg_le, G.degree_le_maxDegree v]
omit [DecidableEq V] in
set_option maxHeartbeats 800000 in
lemma equitable_coloring_of_edgeless (G : SimpleGraph V)
    (r : ℕ) (hG : G.edgeSet = ∅) :
    HasEquitableColoring G (r + 1) := by
  classical
  simp [Set.ext_iff] at hG ⊢
  have h_eq : ∃ f : V → Fin (r + 1), ∀ c₁ c₂ : Fin (r + 1), ((cClass f c₁).card ≤
    (cClass f c₂).card + 1) := by
    have h_card : ∀ n : ℕ, ∃ f : Fin n → Fin (r + 1), ∀ c₁ c₂ : Fin (r + 1),
      ((Finset.filter (fun v => f v = c₁) (Finset.univ)).card ≤ (Finset.filter (fun v => f v =
        c₂) (Finset.univ)).card + 1) := by
      intro n
      use fun i => ⟨i.val % (r + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
      intro c₁ c₂
      simp [Finset.card] at *
      have h_card_classes : ∀ c : Fin (r + 1), (Finset.filter (fun v : Fin n => v.val % (r + 1) =
        c.val) Finset.univ).card = n / (r + 1) + if c.val < n % (r + 1) then 1 else 0 := by
        intro c
        have h_card_classes : (Finset.filter (fun v : Fin n => v.val % (r + 1) =
          c.val) Finset.univ).card = Finset.card (Finset.filter (fun v : ℕ => v % (r + 1) =
            c.val) (Finset.range n)) := by
          refine Finset.card_bij (fun x hx => x) ?_ ?_ ?_ <;> simp [Fin.ext_iff]
          exact fun b hb hb' => ⟨⟨b, hb⟩, hb', rfl⟩
        simp [h_card_classes] at *
        have h_set_eq : {v ∈ Finset.range n | v % (r + 1) = c.val} = Finset.image (fun k => k *
          (r + 1) + c.val) (Finset.range (n / (r + 1) + if c.val < n % (r + 1) then 1 else 0)) := by
          ext v; simp [Finset.mem_image] at *
          constructor <;> intro h <;> rcases h with ⟨h₁, h₂⟩ <;> simp_all
          · exact ⟨v / (r + 1), by
              have hvdiv := Nat.mod_add_div v (r + 1)
              have hvmod := Nat.mod_lt v (Nat.succ_pos r)
              have hndiv := Nat.mod_add_div n (r + 1)
              have hnmod := Nat.mod_lt n (Nat.succ_pos r)
              split_ifs <;> nlinarith
            , by linarith [Nat.mod_add_div v (r + 1)]⟩
          · split_ifs at h₂ <;>
              exact ⟨by
                have hdiv := Nat.div_mul_le_self n (r + 1)
                have hmod := Nat.mod_add_div n (r + 1)
                have hc_lt := Fin.is_lt c
                nlinarith, by
                have hc_lt := Fin.is_lt c
                simp [← h₂.2, Nat.add_mod, Nat.mod_eq_of_lt hc_lt]⟩
        generalize_proofs at *
        rw [h_set_eq, Finset.card_image_of_injective] <;> simp [Function.Injective, *]
      simp_all [Fin.ext_iff, Finset.card]
      split_ifs <;> simp +arith [*] at *
    obtain ⟨f, hf⟩ := h_card (Fintype.card V)
    obtain ⟨e, he⟩ : ∃ e : V ≃ Fin (Fintype.card V), True := ⟨Fintype.equivFin V,
      trivial⟩
    use fun v => f (e v)
    intro c₁ c₂
    convert hf c₁ c₂ using 1
    focus
      simp [cClass]
    · rw [Finset.card_filter, Finset.card_filter]; conv_rhs => rw [← Equiv.sum_comp e]
    · rw [show cClass (fun v => f (e v)) c₂ = Finset.image (fun v =>
      e.symm v) (Finset.filter (fun v => f v = c₂) Finset.univ) from ?_,
        Finset.card_image_of_injective _ e.symm.injective]; aesop
  refine ⟨h_eq.choose, ?_, h_eq.choose_spec⟩
  intro v w hvw
  have h_edge : s(v, w) ∈ G.edgeSet := by
    simpa [SimpleGraph.mem_edgeSet] using hvw
  exact False.elim (hG s(v, w) h_edge)
def AuxAdj (G : SimpleGraph V) (f : V → Fin k) (i j : Fin k) : Prop :=
  ∃ v, f v = i ∧ ∀ w, f w = j → ¬G.Adj v w
def IsAccessible (G : SimpleGraph V) (f : V → Fin k)
    (i_minus j : Fin k) : Prop :=
  Relation.ReflTransGen (AuxAdj G f) j i_minus
structure NearlyEquitable (G : SimpleGraph V) (k s : ℕ) where
  f : V → Fin k
  proper : IsProper G f
  small : Fin k
  large : Fin k
  ne_small_large : small ≠ large
  card_small : (cClass f small).card = s - 1
  card_large : (cClass f large).card = s + 1
  card_other : ∀ c, c ≠ small → c ≠ large → (cClass f c).card = s
  card_total : Fintype.card V = k * s
omit [DecidableEq V] in
lemma one_step_equitable
    (G : SimpleGraph V) (k s : ℕ) (hs : 1 ≤ s)
    (ne : NearlyEquitable G k s)
    (hdirect : AuxAdj G ne.f ne.large ne.small) :
    HasEquitableColoring G k := by
  classical
  obtain ⟨v, hv⟩ := hdirect;
  refine ⟨recolor ne.f v ne.small, ?_, ?_⟩ <;> simp_all [IsProper, IsEquitable];
  · intro u w huw; by_cases hu : u = v <;> by_cases hw : w = v <;> simp_all [recolor,
    SimpleGraph.adj_comm];
    · grind +splitIndPred;
    · contrapose! hv; aesop;
    · exact ne.proper u w huw;
  ·
    have h_rec : ∀ c, (cClass (recolor ne.f v ne.small) c).card = if c = ne.large
      then (cClass ne.f ne.large).card - 1 else if c = ne.small then (cClass ne.f ne.small).card + 1
        else (cClass ne.f c).card := by
      intro c; split_ifs <;> simp_all [cClass_recolor_other_card];
      · convert cClass_recolor_old_card _
        focus
          aesop
        · rw [hv.1];
        · infer_instance;
        · exact hv.1.symm ▸ ne.ne_small_large.symm;
      · rw [cClass_recolor_new_card]; aesop;
    intro c₁ c₂; by_cases hc₁ : c₁ = ne.large <;> by_cases hc₂ : c₂ = ne.large <;>
      simp [*];
    · split_ifs <;> simp_all [NearlyEquitable.card_large, NearlyEquitable.card_small,
      NearlyEquitable.card_other];
    · split_ifs <;> simp_all [ne.card_small, ne.card_large, ne.card_other];
    · by_cases hc₃ : c₁ = ne.small <;> by_cases hc₄ : c₂ = ne.small <;>
        simp_all [ne.card_small, ne.card_large, ne.card_other]
omit [Fintype V] in
lemma auxAdj_preserved_by_recolor
    (G : SimpleGraph V)
    {k : ℕ} {f : V → Fin k} {v : V} {c : Fin k}
    {i j : Fin k} (hvc : f v ≠ c)
    (hij : AuxAdj G f i j)
    (hi_ne : i ≠ f v) (hj_ne : j ≠ c) :
    AuxAdj G (recolor f v c) i j := by
  classical
  obtain ⟨u, hu⟩ := hij;
  refine ⟨u, ?_, ?_⟩ <;> simp_all [recolor];
  · rw [Function.update_apply]; aesop;
  · intro w hw; by_cases hw' : w = v <;> simp_all;
lemma exists_nodup_chain {α : Type*} [Finite α]
    {R : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen R a b) (hab : a ≠ b) :
    ∃ l : List α, l.Nodup ∧ l.IsChain R ∧ l.head? = some a ∧
      l.getLast? = some b ∧ 2 ≤ l.length := by
  classical
  let := Fintype.ofFinite α
  obtain ⟨l, hl⟩ : ∃ l : List α, l.head? = some a ∧ l.getLast? = some b ∧
    List.IsChain R l ∧ ¬∃ l' : List α, l'.head? = some a ∧ l'.getLast? = some b ∧
      List.IsChain R l' ∧ l'.length < l.length := by
    have h_shortest : ∃ l : List α, l.head? = some a ∧ l.getLast? = some b ∧ List.IsChain R l
      := by
      have h_path : ∀ {a b : α}, Relation.ReflTransGen R a b → ∃ l : List α, l.head? =
        some a ∧ l.getLast? = some b ∧ List.IsChain R l := by
        intro a b h
        induction h with
        | refl =>
          exact ⟨[a], rfl, rfl, List.isChain_singleton _⟩;
        | @tail mid b hprev hstep ih =>
          obtain ⟨l, hl₁, hl₂, hl₃⟩ := ih; use l ++ [b]; simp_all;
          exact List.isChain_append.mpr ⟨hl₃, by aesop⟩;
      exact h_path h;
    have h_well_founded : WellFounded fun l l' : List α => l.length < l'.length := by
      refine ⟨fun l => ?_⟩;
      induction n : l.length using Nat.strong_induction_on generalizing l
      rename_i n ih
      exact ⟨_, fun l' hl' => ih _ (by linarith) _ rfl⟩;
    have := h_well_founded.has_min { l : List α | l.head? = some a ∧ l.getLast? = some b ∧
      List.IsChain R l } ⟨_, h_shortest.choose_spec⟩; aesop;
  refine ⟨l, ?_, hl.2.2.1, hl.1, hl.2.1, ?_⟩;
  ·
    by_contra h_dup
    obtain ⟨i, j, hij, h_dup⟩ : ∃ i j, i < j ∧ l.get i = l.get j := by
      rw [List.nodup_iff_injective_get] at h_dup;
      obtain ⟨i, j, hij⟩ := Function.not_injective_iff.mp h_dup;
      grind;
    set l' : List α := l.take i.val ++ l.drop j.val;
    refine hl.2.2.2 ⟨l', ?_, ?_, ?_, ?_⟩;
    · rcases i with ⟨_ | i, hi⟩ <;> rcases j with ⟨_ | j, hj⟩ <;> simp_all;
      · cases l <;> aesop;
      · cases l <;> aesop;
    · grind +suggestions;
    · refine List.isChain_append.mpr ⟨?_, ?_, ?_⟩;
      · have := hl.2.2.1;
        exact List.IsChain.take this _;
      · have := hl.2.2.1;
        exact List.IsChain.drop this _;
      · have := List.isChain_iff_getElem.mp hl.2.2.1;
        rcases i with ⟨_ | i, hi⟩ <;> rcases j with ⟨_ | j, hj⟩ <;>
          simp_all [List.getLast?_take, List.head?_drop];
        convert this i (by omega) using 1;
        · rw [List.getElem?_eq_getElem]; aesop;
        · exact h_dup.symm;
    · grind;
  · rcases l with (_ | ⟨x, _ | ⟨y, l⟩⟩) <;> simp_all;
    grind
omit [Fintype V] in
lemma chain_preserved_after_recolor
    (G : SimpleGraph V)
    {k : ℕ} {f : V → Fin k} {v : V} {c : Fin k}
    (hvc : f v ≠ c)
    {path : List (Fin k)}
    (hchain : path.IsChain (AuxAdj G f))
    (hi_avoid : ∀ x ∈ path, x ≠ f v)
    (hj_avoid : ∀ x ∈ path.tail, x ≠ c) :
    path.IsChain (AuxAdj G (recolor f v c)) := by
      classical
      induction path
      · exact List.isChain_nil;
      · rename_i x path ih
        rcases path <;> simp_all;
        exact auxAdj_preserved_by_recolor G hvc hchain.1 hi_avoid.1 hj_avoid.1
omit [DecidableEq V] in
lemma step_with_chain_preservation
    (G : SimpleGraph V) (k s : ℕ) (_hs : 1 ≤ s)
    (ne : NearlyEquitable G k s)
    (mid : Fin k) (hmid_ne_small : mid ≠ ne.small)
    (hmid_ne_large : mid ≠ ne.large)
    (hedge : AuxAdj G ne.f ne.large mid)
    {tail : List (Fin k)}
    (hchain_tail : (mid :: tail).IsChain (AuxAdj G ne.f))
    (hnodup_full : (ne.large :: mid :: tail).Nodup)
    (hlast : (mid :: tail).getLast? = some ne.small) :
    ∃ ne' : NearlyEquitable G k s,
      ne'.small = ne.small ∧ ne'.large = mid ∧
      (mid :: tail).Nodup ∧
      (mid :: tail).IsChain (AuxAdj G ne'.f) ∧
      (mid :: tail).head? = some ne'.large ∧
      (mid :: tail).getLast? = some ne'.small := by
  classical
  obtain ⟨v, hv1, hv2⟩ := hedge; use ⟨recolor ne.f v mid, ?_, ne.small, mid, ?_, ?_, ?_,
    ?_, ?_⟩ <;> simp_all;
  any_goals tauto;
  any_goals exact ne.card_total;
  · apply chain_preserved_after_recolor;
    · grind;
    · exact hchain_tail;
    · grind +ring;
    · grind +ring;
  · exact recolor_preserves_proper ne.proper ⟨by aesop, hv2⟩;
  · rw [← ne.card_small, cClass_recolor_other_card] <;> simp_all;
    · grind;
    · tauto;
  · convert cClass_recolor_new_card (show ne.f v ≠ mid from by aesop) using 1;
    rw [ne.card_other mid (by tauto) (by tauto)];
  · intro c hc1 hc2; by_cases hc3 : c = ne.large <;>
    simp_all [cClass_recolor_other_card];
    · convert cClass_recolor_old_card (show ne.f v ≠ mid from by aesop) using 1;
      · rw [hv1];
      · have := ne.card_large; aesop;
    · exact ne.card_other c hc1 hc3
omit [DecidableEq V] in
lemma equitable_from_nodup_chain
    (G : SimpleGraph V) (k s : ℕ)
    (ne : NearlyEquitable G k s)
    (path : List (Fin k))
    (hnodup : path.Nodup)
    (hchain : path.IsChain (AuxAdj G ne.f))
    (hhead : path.head? = some ne.large)
    (hlast : path.getLast? = some ne.small) :
    HasEquitableColoring G k := by
      classical
      by_cases hs : 1 ≤ s;
      · induction n : path.length using Nat.strong_induction_on generalizing path ne
        rename_i n ih
        by_cases hpath : path.length ≤ 2;
        · rcases path with (_ | ⟨x, _ | ⟨y, _ | path⟩⟩) <;> simp_all;
          · exact absurd hlast ne.ne_small_large.symm;
          · exact one_step_equitable G k s hs ne hchain;
          · linarith;
        · obtain ⟨mid, tail, htail⟩ : ∃ mid tail, path = ne.large :: mid :: tail := by
            rcases path with (_ | ⟨x, _ | ⟨y, path⟩⟩) <;> simp_all;
            linarith;
          by_cases hmid : mid = ne.small;
          · simp_all [List.isChain_cons_cons];
            exact one_step_equitable G k s hs ne hchain.1;
          · obtain ⟨ne', hne'⟩ : ∃ ne' : NearlyEquitable G k s, ne'.small = ne.small ∧
            ne'.large = mid ∧ (mid :: tail).Nodup ∧ (mid :: tail).IsChain (AuxAdj G ne'.f) ∧
              (mid :: tail).head? = some ne'.large ∧ (mid :: tail).getLast? = some ne'.small := by
              apply step_with_chain_preservation;
              all_goals simp_all [List.isChain_cons_cons];
              tauto;
            grind;
      · have := ne.card_small; have := ne.card_large; simp_all;
        have := ne.card_total; simp_all [cClass];
        rw [Fintype.card_eq_zero_iff] at this; aesop
omit [DecidableEq V] in
lemma accessible_large_gives_equitable
    (G : SimpleGraph V) (k s : ℕ)
    (ne : NearlyEquitable G k s)
    (hacc : IsAccessible G ne.f ne.small ne.large) :
    HasEquitableColoring G k := by
  classical
  obtain ⟨l, hl⟩ : ∃ l : List (Fin k), l.Nodup ∧ l.IsChain (AuxAdj G ne.f) ∧ l.head? =
    some ne.large ∧ l.getLast? = some ne.small ∧ 2 ≤ l.length := by
    apply exists_nodup_chain
    · assumption
    · exact ne.ne_small_large.symm
  apply
    equitable_from_nodup_chain G k s ne l hl.left hl.right.left hl.right.right.left
      hl.right.right.right.left
omit [DecidableEq V] in
lemma equitable_all_same_size {k s : ℕ}
    {f : V → Fin k} (hf : IsEquitable f)
    (htotal : Fintype.card V = k * s) :
    ∀ c : Fin k, (cClass f c).card = s := by
  intro c
  have h_sum : ∑ c, (cClass f c).card = k * s := by
    rw [← htotal, cClass_card_sum];
  by_contra h_contra;
  obtain ⟨d, hd⟩ : ∃ d, (cClass f d).card < s := by
    by_cases h_all_ge_s : ∀ c, (cClass f c).card ≥ s;
    · exact absurd
        (h_sum ▸ Finset.sum_lt_sum (fun a _ => h_all_ge_s a)
          ⟨c, Finset.mem_univ c,
            lt_of_le_of_ne (h_all_ge_s c) (Ne.symm h_contra)⟩)
        (by simp);
    · aesop;
  have h_all_le : ∀ c, (cClass f c).card ≤ s := by
    exact fun c => by linarith [hf c d, hf d c];
  exact absurd h_sum (ne_of_lt (lt_of_lt_of_le (Finset.sum_lt_sum (fun x _ =>
    h_all_le x) ⟨d, Finset.mem_univ d, hd⟩) (by simp)))
omit [DecidableEq V] in
lemma exists_movable_class
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : ℕ} (hd : G.maxDegree ≤ r)
    (f : V → Fin (r + 1)) (x : V)
    (hx_neighbor : ∃ w, f w = f x ∧ G.Adj x w) :
    ∃ c : Fin (r + 1), c ≠ f x ∧ ∀ w, f w = c → ¬G.Adj x w := by
  set S := (G.neighborFinset x).image f with hS_def
  have hS_card : S.card ≤ r := by
    exact le_trans (Finset.card_image_le) (by simpa using G.degree_le_maxDegree x |> le_trans <|
      hd);
  have h_compl_card : (Finset.univ \ S).card ≥ 1 := by
    simp [Finset.card_sdiff, *];
    exact Nat.sub_pos_of_lt (lt_of_le_of_lt hS_card (Nat.lt_succ_self _));
  obtain ⟨c, hc⟩ := Finset.card_pos.mp h_compl_card; use c; aesop;
omit [DecidableEq V] in
set_option maxHeartbeats 800000 in
lemma induction_step_with_callback
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (hs_card : (r + 1) ∣ Fintype.card V)
    (hd : G.maxDegree ≤ r)
    (e : Sym2 V) (he : e ∈ G.edgeSet)
    (hIH : HasEquitableColoring (G.deleteEdges {e}) (r + 1))
    (h_ne : ∀ (s : ℕ), Fintype.card V = (r + 1) * s → 0 < s →
      NearlyEquitable G (r + 1) s → HasEquitableColoring G (r + 1)) :
    HasEquitableColoring G (r + 1) := by
  classical
  cases' hIH with f hf
  rcases e with ⟨x, y⟩
  by_cases hxy : f x = f y
  · obtain ⟨c, hc_ne, hc_movable⟩ : ∃ c : Fin (r + 1), c ≠ f x ∧ ∀ w, f w = c →
    ¬G.Adj x w := by
      apply exists_movable_class G hd f x ⟨y, by aesop⟩
    set f' : V → Fin (r + 1) := recolor f x c
    have hf'_proper : IsProper G f' := by
      intro u v huv; by_cases hu : u = x <;> by_cases hv : v = x <;> simp_all
      · simp +zetaDelta at *; unfold recolor; aesop
      · simp +zetaDelta at *; simp [*, recolor]
        exact fun h => hc_movable u h (by simpa [SimpleGraph.adj_comm] using huv)
      · simp +zetaDelta at *; unfold recolor; aesop
    obtain ⟨s, hs⟩ : ∃ s : ℕ, Fintype.card V = (r + 1) * s := hs_card
    have h_card_f' : ∀ c' : Fin (r + 1), (cClass f' c').card =
        if c' = f x then s - 1 else if c' = c then s + 1 else s := by
      have h1 : ∀ c' : Fin (r + 1), (cClass f' c').card =
          if c' = f x then (cClass f (f x)).card - 1
          else if c' = c then (cClass f c).card + 1
          else (cClass f c').card := by
        intro c'
        by_cases hc'_eq_fx : c' = f x
        · rw [hc'_eq_fx, cClass_recolor_old_card]
          focus
            aesop
          exact Ne.symm hc_ne
        · by_cases hc'_eq_c : c' = c <;>
            simp_all
          · rw [cClass_recolor_new_card]; aesop
          · convert
              cClass_recolor_other_card (show c' ≠ f x from by aesop)
                (show c' ≠ c from by aesop)
              using 1
      have h_card_f : ∀ c' : Fin (r + 1), (cClass f c').card = s := by
        apply equitable_all_same_size hf.2 hs
      aesop
    refine h_ne s hs (Nat.pos_of_ne_zero ?_) ⟨f', hf'_proper, f x, c, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp_all
    · rintro rfl; simp_all [Fintype.card_eq_zero_iff]; exact hs.elim x
    · exact Ne.symm hc_ne
  · refine ⟨f, ?_, hf.2⟩
    intro v w hvw; by_cases h : v = x ∧ w = y ∨ v = y ∧ w = x <;>
      simp_all [SimpleGraph.deleteEdges]
    · grind +ring
    · exact hf.1 v w (by aesop)
lemma edgeFinset_card_deleteEdges_lt (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    (G.deleteEdges {↑e}).edgeFinset.card < G.edgeFinset.card := by
  apply Finset.card_lt_card
  rw [SimpleGraph.edgeFinset_ssubset_edgeFinset, lt_iff_le_and_ne]
  refine ⟨SimpleGraph.deleteEdges_le _, ?_⟩
  intro hEq
  have hmem : e ∈ (G.deleteEdges {↑e}).edgeSet := by
    rw [hEq]
    exact SimpleGraph.mem_edgeFinset.mp he
  simp at hmem
omit [Fintype V] [DecidableEq V] in
lemma non_acc_has_acc_neighbor
    (G : SimpleGraph V)
    {k : ℕ} {f : V → Fin k} {i_minus : Fin k}
    {y : V} {c : Fin k}
    (hacc_c : IsAccessible G f i_minus c)
    (hnacc_y : ¬IsAccessible G f i_minus (f y)) :
    ∃ w, f w = c ∧ G.Adj y w := by
  classical
  by_contra h_contra; push Not at h_contra; (
  have h_aux_adj_y : AuxAdj G f (f y) c := by
    exact ⟨y, rfl, h_contra⟩;
  exact hnacc_y (Relation.ReflTransGen.head h_aux_adj_y hacc_c));
omit [DecidableEq V] in
lemma acc_has_second_color
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large) :
    ∃ W : Fin (r + 1), W ≠ ne.small ∧ W ≠ ne.large ∧ IsAccessible G ne.f ne.small W := by
  classical
  by_contra h_contra;
  have h_adj_small_large : ∀ y : V, ne.f y ≠ ne.small → ∃ w : V, ne.f w = ne.small ∧
    G.Adj y w := by
    intro y hy_ne_small
    generalize_proofs at *; (
    apply non_acc_has_acc_neighbor G (Relation.ReflTransGen.refl) (by
    by_cases hy_large : ne.f y = ne.large <;> simp_all [IsAccessible]))
  generalize_proofs at *; (
  have h_edges : (Finset.card (Finset.filter (fun v => ne.f v ≠ ne.small) Finset.univ)) ≤ r *
    (Finset.card (Finset.filter (fun v => ne.f v = ne.small) Finset.univ)) := by
    have h_edges : (Finset.card (Finset.filter (fun v => ne.f v ≠ ne.small) Finset.univ)) ≤
      Finset.sum (Finset.filter (fun v => ne.f v = ne.small) Finset.univ) (fun v =>
        Finset.card (Finset.filter (fun w => ne.f w ≠ ne.small ∧ G.Adj v w) Finset.univ)) := by
      have h_edges : Finset.filter (fun v =>
        ne.f v ≠ ne.small) Finset.univ ⊆ Finset.biUnion (Finset.filter (fun v => ne.f v =
          ne.small) Finset.univ) (fun v => Finset.filter (fun w => ne.f w ≠ ne.small ∧
            G.Adj v w) Finset.univ) := by
        intro v hv
        have h := h_adj_small_large v (by simpa using hv)
        exact Finset.mem_biUnion.mpr
          ⟨h.choose, by simp [h.choose_spec.1],
            by simp [(Finset.mem_filter.mp hv).2, h.choose_spec.2.symm]⟩
      generalize_proofs at *; (
      exact le_trans (Finset.card_le_card h_edges) (Finset.card_biUnion_le) |> le_trans <|
        by simp [Finset.sum_filter];)
    generalize_proofs at *; (
    have h_edges : ∀ v ∈ Finset.filter (fun v => ne.f v = ne.small) Finset.univ,
      Finset.card (Finset.filter (fun w => ne.f w ≠ ne.small ∧ G.Adj v w) Finset.univ) ≤ r
        := by
      intro v hv
      have h_deg_v : Finset.card (Finset.filter (fun w => G.Adj v w) Finset.univ) ≤ r := by
        simpa [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
          using (SimpleGraph.degree_le_maxDegree G v).trans hd
      generalize_proofs at *; (
      exact le_trans (Finset.card_le_card fun w hw => by aesop) h_deg_v)
    generalize_proofs at *; (
    exact le_trans ‹_› (by simpa [mul_comm] using Finset.sum_le_sum h_edges)))
  generalize_proofs at *; (
  have h_card_small : (Finset.card (Finset.filter (fun v => ne.f v = ne.small) Finset.univ)) = s - 1
    := by
    simpa [cClass] using ne.card_small
  generalize_proofs at *; (
  simp_all [Finset.filter_not, Finset.card_sdiff];
  nlinarith only [h_edges, hs0, Nat.sub_add_cancel hs0])))
lemma exists_terminal_vertex {α : Type*} [Finite α]
    (R : α → α → Prop) (r : α)
    (W₀ : α) (hW₀ : Relation.ReflTransGen R W₀ r) (hW₀_ne : W₀ ≠ r) :
    ∃ W : α, Relation.ReflTransGen R W r ∧ W ≠ r ∧
      ∀ C : α, Relation.ReflTransGen R C r → C ≠ W →
        Relation.ReflTransGen (fun a b => R a b ∧ a ≠ W) C r :=
  by
    classical
    let := Fintype.ofFinite α
    exact TerminalVertex.exists_terminal_vertex R r W₀ hW₀ hW₀_ne
omit [Fintype V] [DecidableEq V] in
lemma exists_terminal_color
    (G : SimpleGraph V)
    (k : ℕ) (f : V → Fin k) (small : Fin k)
    (W₀ : Fin k) (hW₀ : IsAccessible G f small W₀) (hW₀_ne : W₀ ≠ small) :
    ∃ W : Fin k, IsAccessible G f small W ∧ W ≠ small ∧
      ∀ C : Fin k, IsAccessible G f small C → C ≠ W →
        Relation.ReflTransGen (fun c d => AuxAdj G f c d ∧ c ≠ W) C small :=
  exists_terminal_vertex (AuxAdj G f) small W₀ hW₀ hW₀_ne
omit [DecidableEq V] in
set_option maxHeartbeats 1600000 in
lemma solo_weight_contradiction
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (h_all_bad : ∀ (W : Fin (r + 1)) (z y₁ : V),
      IsAccessible G ne.f ne.small W → W ≠ ne.small → W ≠ ne.large →
      ne.f z = W → ¬IsAccessible G ne.f ne.small (ne.f y₁) →
      G.Adj y₁ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₁ w) →
      (∀ X, X ≠ W → IsAccessible G ne.f ne.small X → ∃ w, ne.f w = X ∧ G.Adj z w) ∧
      (∀ y₂, y₂ ≠ y₁ → ¬IsAccessible G ne.f ne.small (ne.f y₂) →
        G.Adj y₂ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₂ w) → G.Adj y₁ y₂)) :
    False := by
  classical
  obtain ⟨W₀, hW₀_ne_small, hW₀_ne_large, hW₀_acc⟩ :=
    acc_has_second_color G r s hs hd hs0 ne hacc
  let B_verts := Finset.univ.filter (fun v : V => ¬IsAccessible G ne.f ne.small (ne.f v))
  let W₀_class := cClass ne.f W₀
  let acc_colors := Finset.univ.filter (fun c : Fin (r + 1) => IsAccessible G ne.f ne.small c)
  have hW₀_card : W₀_class.card = s := ne.card_other W₀ hW₀_ne_small hW₀_ne_large
  have hW₀_mem : W₀ ∈ acc_colors := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hW₀_acc⟩
  have hsmall_mem : ne.small ∈ acc_colors := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    Relation.ReflTransGen.refl⟩
  have hlarge_nmem : ne.large ∉ acc_colors := by simp [acc_colors, Finset.mem_filter]; exact hacc
  have hacc_ge_2 : 2 ≤ acc_colors.card := by
    have : {ne.small, W₀} ⊆ acc_colors := by
      simp [Finset.subset_iff]; exact ⟨hsmall_mem, hW₀_mem⟩
    exact le_trans (by simp [Finset.card_pair hW₀_ne_small.symm]) (Finset.card_le_card this)
  have hB_has_nbr : ∀ y : V, ¬IsAccessible G ne.f ne.small (ne.f y) →
      ∀ c, IsAccessible G ne.f ne.small c → ∃ w, ne.f w = c ∧ G.Adj y w := by
    intro y hy c hc; exact non_acc_has_acc_neighbor G hc hy
  have h_solo_deg_bound : ∀ z : V, ne.f z = W₀ →
      (∃ y₁ : V, ¬IsAccessible G ne.f ne.small (ne.f y₁) ∧
        G.Adj y₁ z ∧ (∀ w, ne.f w = W₀ → w ≠ z → ¬G.Adj y₁ w)) →
      (Finset.univ.filter (fun w => G.Adj z w ∧ ¬IsAccessible G ne.f ne.small (ne.f w))).card
        ≤ r + 1 - acc_colors.card := by
    intro z hz ⟨y₁, hy₁_nacc, hy₁_adj, hy₁_uniq⟩
    have h_bad :=
      h_all_bad W₀ z y₁ hW₀_acc hW₀_ne_small hW₀_ne_large hz hy₁_nacc hy₁_adj
        hy₁_uniq
    have h_deg_bound : Finset.card (Finset.filter (fun w => G.Adj z w ∧
      IsAccessible G ne.f ne.small (ne.f w)) (Finset.univ : Finset V)) ≥ acc_colors.card - 1 := by
      have hN_acc_ge : Finset.card (acc_colors.erase W₀) ≤ Finset.card (Finset.image (fun w =>
        ne.f w) (Finset.filter (fun w => G.Adj z w ∧
          IsAccessible G ne.f ne.small (ne.f w)) (Finset.univ : Finset V))) := by
        refine Finset.card_le_card ?_;
        grind;
      exact le_trans
        (by rw [Finset.card_erase_of_mem hW₀_mem])
        (hN_acc_ge.trans Finset.card_image_le)
    have h_deg_bound : Finset.card (Finset.filter (fun w => G.Adj z w) (Finset.univ : Finset V)) ≤
      r := by
      simpa [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
        using (SimpleGraph.degree_le_maxDegree G z).trans hd
    have h_deg_bound : Finset.card (Finset.filter (fun w => G.Adj z w ∧
      IsAccessible G ne.f ne.small (ne.f w)) (Finset.univ : Finset V)) +
        Finset.card (Finset.filter (fun w => G.Adj z w ∧
          ¬IsAccessible G ne.f ne.small (ne.f w)) (Finset.univ : Finset V)) =
            Finset.card (Finset.filter (fun w => G.Adj z w) (Finset.univ : Finset V)) := by
      rw [Finset.card_filter, Finset.card_filter, Finset.card_filter];
        rw [← Finset.sum_add_distrib]; congr; ext w;
          by_cases hw : IsAccessible G ne.f ne.small (ne.f w) <;> simp [hw];
    omega
  set q := r + 1 - acc_colors.card with hq_def
  have hacc_le : acc_colors.card ≤ r + 1 := by
    exact le_trans (Finset.card_filter_le _ _) (by simp)
  have hB_card : B_verts.card = q * s + 1 := by
    have hB_card : B_verts.card = Fintype.card V - ∑ c ∈ acc_colors, (cClass ne.f c).card := by
      rw [← Finset.card_biUnion];
      · rw [← Finset.card_compl];
        congr with v; simp [B_verts, acc_colors, cClass];
      · exact fun x hx y hy hxy => Finset.disjoint_filter.2 fun z => by simp +contextual [hxy];
    have hB_card : ∑ c ∈ acc_colors, (cClass ne.f c).card = (acc_colors.card - 1) * s + (s - 1)
      := by
      have hB_card : ∑ c ∈ acc_colors, (cClass ne.f c).card =
        ∑ c ∈ acc_colors.erase ne.small, (cClass ne.f c).card + (cClass ne.f ne.small).card
          := by
        rw [Finset.sum_erase_add _ _ hsmall_mem];
      rw [hB_card, Finset.sum_congr rfl fun x hx => ne.card_other x ?_ ?_] <;> simp [*,
        Finset.card_erase_of_mem hsmall_mem];
      · exact ne.card_small;
      · exact Finset.ne_of_mem_erase hx;
      · exact fun h => hlarge_nmem <| h ▸ Finset.mem_of_mem_erase hx;
    rw [‹#B_verts = Fintype.card V - ∑ c ∈ acc_colors, #(cClass ne.f c)›, hs, hB_card];
    exact Nat.sub_eq_of_eq_add <| by
      have hs1 : 1 ≤ s := by exact Nat.succ_le_of_lt hs0
      have hacc_pos : 1 ≤ Finset.card acc_colors := by linarith
      nlinarith only [Nat.sub_add_cancel hacc_le, Nat.sub_add_cancel hs1,
        Nat.sub_add_cancel hacc_pos]
  have hB_deg : ∀ y : V, y ∈ B_verts →
      (B_verts.filter (fun w => G.Adj y w)).card ≤ q - 1 := by
    intro y hy; specialize hB_has_nbr y; simp_all;
    have h_y_acc_nbr : (Finset.filter (fun w =>
      IsAccessible G ne.f ne.small (ne.f w)) (G.neighborFinset y)).card ≥ acc_colors.card := by
      have h_y_acc_nbr : (Finset.image (fun w => ne.f w) (Finset.filter (fun w =>
        IsAccessible G ne.f ne.small (ne.f w)) (G.neighborFinset y))).card ≥ acc_colors.card := by
        refine Finset.card_le_card ?_;
        intro c hc
        specialize hB_has_nbr (Finset.mem_filter.mp hy |>.2) c
          (Finset.mem_filter.mp hc |>.2)
        aesop
      exact h_y_acc_nbr.trans (Finset.card_image_le);
    have h_y_total_nbr : (Finset.filter (fun w =>
      IsAccessible G ne.f ne.small (ne.f w)) (G.neighborFinset y)).card + (Finset.filter (fun w =>
        ¬IsAccessible G ne.f ne.small (ne.f w)) (G.neighborFinset y)).card ≤ r := by
      rw [Finset.card_filter_add_card_filter_not];
        exact le_trans (SimpleGraph.degree_le_maxDegree _ _) hd;
    rw [show { w ∈ B_verts | G.Adj y w } =
      { w ∈ G.neighborFinset y | ¬IsAccessible G ne.f ne.small (ne.f w) } from ?_];
    · omega;
    · ext; simp [B_verts];
      tauto
  by_cases h_case : acc_colors.card * 2 ≤ r + 2
  ·
    have h_edge_count : 2 * (q * s + 1) - q * Finset.card (Finset.filter (fun z =>
      z ∈ W₀_class ∧ ∃ y, y ∈ B_verts ∧ G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z →
        ¬G.Adj y w) W₀_class) ≤ q * Finset.card (Finset.filter (fun z => z ∈ W₀_class ∧
          ∃ y, y ∈ B_verts ∧ G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z →
            ¬G.Adj y w) W₀_class) + r * Finset.card (Finset.filter (fun z => z ∈ W₀_class ∧
              ¬∃ y, y ∈ B_verts ∧ G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z →
                ¬G.Adj y w) W₀_class) := by
      have h_edge_count : ∑ z ∈ W₀_class, (B_verts.filter (fun w => G.Adj z w)).card =
        ∑ y ∈ B_verts, (W₀_class.filter (fun w => G.Adj y w)).card := by
        simp only [card_filter];
        exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ =>
          Finset.sum_congr rfl fun _ _ => by simp [SimpleGraph.adj_comm]);
      have h_edge_count : ∑ y ∈ B_verts, (W₀_class.filter (fun w => G.Adj y w)).card ≥ 2 *
        (q * s + 1) - q * Finset.card (Finset.filter (fun z => z ∈ W₀_class ∧ ∃ y,
          y ∈ B_verts ∧ G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w) W₀_class)
            := by
        have h_edge_count : ∀ y ∈ B_verts, (W₀_class.filter (fun w => G.Adj y w)).card ≥
          if ∃ z ∈ W₀_class, G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w
            then 1 else 2 := by
          intro y hy
          by_cases h_exists_z : ∃ z ∈ W₀_class, G.Adj y z ∧ ∀ w ∈ W₀_class,
            w ≠ z → ¬G.Adj y w;
          · simp +zetaDelta at *;
            rw [if_pos h_exists_z]; exact Finset.card_pos.mpr ⟨h_exists_z.choose,
              Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                h_exists_z.choose_spec.1⟩, h_exists_z.choose_spec.2.1⟩⟩;
          · obtain ⟨z₁, hz₁⟩ : ∃ z₁ ∈ W₀_class, G.Adj y z₁ := by
              simp +zetaDelta at *;
              exact Exists.elim (hB_has_nbr y hy W₀ hW₀_mem) fun z hz => ⟨z, hz.1,
                hz.2⟩;
            obtain ⟨z₂, hz₂⟩ : ∃ z₂ ∈ W₀_class, G.Adj y z₂ ∧ z₂ ≠ z₁ := by
              grind;
            simp [h_exists_z];
            refine Finset.one_lt_card.mpr ⟨z₁, ?_, z₂, ?_, ?_⟩ <;> simp [hz₁,
              hz₂];
            exact Ne.symm hz₂.2.2;
        have h_edge_count : ∑ y ∈ B_verts, (if ∃ z ∈ W₀_class, G.Adj y z ∧
          ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w then 1 else 2) ≥ 2 * (q * s + 1) - q *
            Finset.card (Finset.filter (fun z => z ∈ W₀_class ∧ ∃ y, y ∈ B_verts ∧
              G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w) W₀_class) := by
          have h_edge_count : Finset.card (Finset.filter (fun y => ∃ z ∈ W₀_class,
            G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w) B_verts) ≤ q *
              Finset.card (Finset.filter (fun z => z ∈ W₀_class ∧ ∃ y, y ∈ B_verts ∧
                G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w) W₀_class) := by
            have h_edge_count : ∀ z ∈ W₀_class, (Finset.filter (fun y => G.Adj y z ∧
              ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w) B_verts).card ≤ q := by
              intros z hz
              by_cases hz_solo : ∃ y₁, y₁ ∈ B_verts ∧ G.Adj y₁ z ∧
                ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y₁ w;
              · refine le_trans ?_ (h_solo_deg_bound z ?_ ?_);
                · refine Finset.card_le_card ?_;
                  simp +contextual [Finset.subset_iff, SimpleGraph.adj_comm];
                  exact fun x hx hx' hx'' => Finset.mem_filter.mp hx |>.2;
                · exact Finset.mem_filter.mp hz |>.2;
                · exact ⟨hz_solo.choose, Finset.mem_filter.mp hz_solo.choose_spec.1 |>.2,
                  hz_solo.choose_spec.2.1, fun w hw hw' =>
                    hz_solo.choose_spec.2.2 w (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                      hw⟩) hw'⟩;
              · rw [Finset.card_eq_zero.mpr] <;> norm_num;
                grind;
            have h_edge_count : Finset.card (Finset.filter (fun y => ∃ z ∈ W₀_class,
              G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w) B_verts) ≤
                ∑ z ∈ Finset.filter (fun z => z ∈ W₀_class ∧ ∃ y ∈ B_verts,
                  G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w) W₀_class,
                    (Finset.filter (fun y => G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z →
                      ¬G.Adj y w) B_verts).card := by
              have h_edge_count : Finset.filter (fun y => ∃ z ∈ W₀_class, G.Adj y z ∧
                ∀ w ∈ W₀_class, w ≠ z →
                  ¬G.Adj y w) B_verts ⊆ Finset.biUnion (Finset.filter (fun z =>
                    z ∈ W₀_class ∧ ∃ y ∈ B_verts, G.Adj y z ∧ ∀ w ∈ W₀_class,
                      w ≠ z → ¬G.Adj y w) W₀_class) (fun z => Finset.filter (fun y =>
                        G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w) B_verts) := by
                simp +contextual [Finset.subset_iff];
                exact fun x hx y hy hxy hyx => ⟨y, ⟨hy, x, hx, hxy, hyx⟩, hxy, hyx⟩;
              exact le_trans (Finset.card_le_card h_edge_count) (Finset.card_biUnion_le);
            exact h_edge_count.trans (by
              simpa [mul_comm] using
                Finset.sum_le_sum fun x hx =>
                  ‹∀ z ∈ W₀_class,
                      #({y ∈ B_verts | G.Adj y z ∧
                        ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w}) ≤ q›
                    x (Finset.mem_filter.mp hx |>.1));
          simp [Finset.sum_ite, *] at *;
          rw [show (Finset.filter (fun x => ∀ x_1 ∈ W₀_class, G.Adj x x_1 →
            ∃ x_2 ∈ W₀_class, ¬x_2 = x_1 ∧ G.Adj x x_2) B_verts) =
              B_verts \ (Finset.filter (fun x => ∃ z ∈ W₀_class, G.Adj x z ∧
                ∀ w ∈ W₀_class, ¬w = z → ¬G.Adj x w) B_verts) from ?_];
          · grind;
          · grind;
        exact h_edge_count.trans (Finset.sum_le_sum ‹_›);
      have h_edge_count : ∑ z ∈ W₀_class, (B_verts.filter (fun w => G.Adj z w)).card ≤ q *
        Finset.card (Finset.filter (fun z => z ∈ W₀_class ∧ ∃ y, y ∈ B_verts ∧
          G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w) W₀_class) + r *
            Finset.card (Finset.filter (fun z => z ∈ W₀_class ∧ ¬∃ y, y ∈ B_verts ∧
              G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w) W₀_class) := by
        have h_edge_count : ∀ z ∈ W₀_class, (B_verts.filter (fun w => G.Adj z w)).card ≤
          if ∃ y ∈ B_verts, G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w then q
            else r := by
          intro z hz;
          split_ifs with h;
          · convert h_solo_deg_bound z (Finset.mem_filter.mp hz |>.2) _ using 1;
            · congr 1 with w; simp;
              exact ⟨fun h => ⟨h.2, Finset.mem_filter.mp h.1 |>.2⟩, fun h =>
                ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.2⟩, h.1⟩⟩;
            · exact ⟨h.choose, Finset.mem_filter.mp h.choose_spec.1 |>.2, h.choose_spec.2.1,
              fun w hw hw' => h.choose_spec.2.2 w (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                hw⟩) hw'⟩;
          · have h_deg_z : (B_verts.filter (fun w => G.Adj z w)).card ≤ G.degree z := by
              exact Finset.card_le_card fun x hx =>
                by simpa [SimpleGraph.adj_comm] using Finset.mem_filter.mp hx |>.2;
            exact le_trans h_deg_z (le_trans (SimpleGraph.degree_le_maxDegree _ _) hd);
        simpa [Finset.sum_ite, Finset.filter_and, mul_comm,
          Finset.filter_mem_eq_inter, Finset.inter_filter] using Finset.sum_le_sum h_edge_count
      linarith;
    have hS₀_card : Finset.card (Finset.filter (fun z => z ∈ W₀_class ∧ ∃ y,
      y ∈ B_verts ∧ G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w) W₀_class) +
        Finset.card (Finset.filter (fun z => z ∈ W₀_class ∧ ¬∃ y, y ∈ B_verts ∧
          G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w) W₀_class) = s := by
      rw [← hW₀_card, ← Finset.card_union_of_disjoint];
      · congr with z; by_cases h : ∃ y ∈ B_verts, G.Adj y z ∧ ∀ w ∈ W₀_class,
        w ≠ z → ¬G.Adj y w <;> simp [h];
        grind;
      · simp +contextual [Finset.disjoint_left];
    rw [tsub_le_iff_right] at h_edge_count; nlinarith only [h_case, hS₀_card, h_edge_count,
      Nat.sub_add_cancel hacc_le];
  ·
    push Not at h_case
    by_cases hq0 : q = 0
    ·
      have : acc_colors.card = r + 1 := by omega
      have hacc_full : acc_colors.card = Fintype.card (Fin (r+1)) := by simp; omega
      have := Finset.eq_univ_of_card acc_colors hacc_full
      exact hlarge_nmem (this ▸ Finset.mem_univ _)
    ·
      set t_val := acc_colors.card - 1 with ht_def
      have ht_gt_q : q < t_val := by omega
      set A'_colors := acc_colors.erase ne.small with hA'_def
      have hA'_card : A'_colors.card = t_val := by
        rw [show A'_colors = acc_colors.erase ne.small from rfl,
          Finset.card_erase_of_mem hsmall_mem]
      set A'_verts := Finset.univ.filter (fun v : V => ne.f v ∈ A'_colors) with hA'_verts_def
      set Solo : V → Finset V := fun z =>
        B_verts.filter (fun y => G.Adj y z ∧ ∀ w, ne.f w = ne.f z → w ≠ z → ¬G.Adj y w)
      exact weight_function_contradiction A'_verts B_verts Solo q t_val s
        (by omega) ht_gt_q hs0
        (by
          have : A'_verts.card = ∑ c ∈ A'_colors, (cClass ne.f c).card := by
            rw [← Finset.card_biUnion]
            · congr 1; ext v; simp [A'_verts, A'_colors, cClass]
            · intro x hx y hy hxy
              exact Finset.disjoint_filter.2 fun z => by
                simp +contextual [hxy]
          rw [this, ← hA'_card]
          apply Finset.sum_le_card_nsmul
          intro c hc
          have hc_ne_small : c ≠ ne.small := Finset.ne_of_mem_erase hc
          have hc_ne_large : c ≠ ne.large := by
            intro h; exact hlarge_nmem (h ▸ Finset.mem_of_mem_erase hc)
          exact le_of_eq (ne.card_other c hc_ne_small hc_ne_large))
        hB_card
        (fun z _ => Finset.filter_subset _ _)
        (fun z _ h => Finset.card_pos.mpr h)
        (by
          intro z hz
          by_cases hSz : (Solo z).card = 0
          · omega
          ·
            obtain ⟨y₁, hy₁⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hSz)
            have hy₁_mem := Finset.mem_filter.mp hy₁
            have hz_mem := Finset.mem_filter.mp hz
            have hz_acc : IsAccessible G ne.f ne.small (ne.f z) :=
              (Finset.mem_filter.mp (Finset.mem_of_mem_erase (hA'_def ▸ hz_mem.2))).2
            have hz_ne_small : ne.f z ≠ ne.small :=
              Finset.ne_of_mem_erase (hA'_def ▸ hz_mem.2)
            have hz_ne_large : ne.f z ≠ ne.large := by
              intro h; exact hlarge_nmem (h ▸ Finset.mem_of_mem_erase (hA'_def ▸ hz_mem.2))
            have hy₁_B := (Finset.mem_filter.mp hy₁_mem.1).2
            by_contra h_gt
            push Not at h_gt
            have : (B_verts.filter (fun w => G.Adj y₁ w)).card ≥ q := by
              have h_clique : ∀ y₂ ∈ Solo z, y₂ ≠ y₁ → G.Adj y₁ y₂ := by
                intro y₂ hy₂ hne
                have hy₂_mem := Finset.mem_filter.mp hy₂
                exact (h_all_bad (ne.f z) z y₁ hz_acc hz_ne_small hz_ne_large rfl
                  hy₁_B hy₁_mem.2.1 hy₁_mem.2.2).2
                  y₂ hne (Finset.mem_filter.mp hy₂_mem.1).2
                  hy₂_mem.2.1 hy₂_mem.2.2
              have h_sub : (Solo z).erase y₁ ⊆ B_verts.filter (fun w => G.Adj y₁ w) := by
                intro w hw
                have hw_ne := Finset.ne_of_mem_erase hw
                have hw_solo := Finset.mem_of_mem_erase hw
                exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw_solo).1,
                  h_clique w hw_solo hw_ne⟩
              calc (B_verts.filter (fun w => G.Adj y₁ w)).card
                  ≥ ((Solo z).erase y₁).card := Finset.card_le_card h_sub
                _ = (Solo z).card - 1 := Finset.card_erase_of_mem hy₁
                _ ≥ q := by omega
            have := hB_deg y₁ hy₁_mem.1
            omega)
        (by
          intro y hy
          have hy_nacc : ¬IsAccessible G ne.f ne.small (ne.f y) :=
            (Finset.mem_filter.mp hy).2
          have h_has_nbr_A' : ∀ c ∈ A'_colors, ∃ w, ne.f w = c ∧ G.Adj y w :=
            fun c hc => hB_has_nbr y hy_nacc c (Finset.mem_filter.mp (Finset.mem_of_mem_erase hc)).2
          have h_deg_y : G.degree y ≤ r := le_trans (G.degree_le_maxDegree y) hd
          set dB := (B_verts.filter (fun w => G.Adj y w)).card
          have hdB_le : dB ≤ q - 1 := hB_deg y hy
          refine ⟨dB + 1, by omega, by omega, ?_, ?_, ?_⟩
          ·
            have h_multi_count : (Finset.filter (fun c => (Finset.filter (fun w => ne.f w =
              c) (Finset.filter (fun w => G.Adj y w) Finset.univ)).card ≥ 2) A'_colors).card ≤
                (G.degree y - 1 - dB) - t_val := by
              have h_multi_count : (Finset.sum A'_colors (fun c => (Finset.filter (fun w => ne.f w =
                c) (Finset.filter (fun w => G.Adj y w) Finset.univ)).card)) + 1 + dB ≤ G.degree y
                  := by
                have h_multi_count : (Finset.sum A'_colors (fun c => (Finset.filter (fun w =>
                  ne.f w = c) (Finset.filter (fun w => G.Adj y w) Finset.univ)).card)) +
                    (Finset.filter (fun w => ne.f w = ne.small) (Finset.filter (fun w =>
                      G.Adj y w) Finset.univ)).card + dB ≤ G.degree y := by
                  rw [← Finset.card_biUnion, ← Finset.card_union_of_disjoint,
                    ← Finset.card_union_of_disjoint];
                  · refine le_trans (Finset.card_le_card ?_)
                      (Finset.card_le_card
                        (s := Finset.filter (fun w => G.Adj y w) Finset.univ) ?_);
                    · grind;
                    · exact fun x hx => by simpa using hx;
                  · simp +contextual [Finset.disjoint_left];
                    grind +ring;
                  · simp +contextual [Finset.disjoint_left];
                    exact fun v hv₁ hv₂ => Finset.ne_of_mem_erase hv₁ |> fun h =>
                      by simp [h];
                  · exact fun x hx y hy hxy =>
                      Finset.disjoint_left.mpr fun z => by
                        simp +contextual [hxy];
                generalize_proofs at *; (
                refine le_trans ?_ h_multi_count
                generalize_proofs at *; (
                simp +zetaDelta at *;
                exact Exists.elim (hB_has_nbr y hy ne.small hsmall_mem) fun w hw => ⟨w,
                  by aesop⟩))
              generalize_proofs at *; (
              have h_multi_count : ∑ c ∈ A'_colors, (Finset.filter (fun w => ne.f w =
                c) (Finset.filter (fun w => G.Adj y w) Finset.univ)).card ≥ ∑ c ∈ A'_colors,
                  1 + ∑ c ∈ Finset.filter (fun c => (Finset.filter (fun w => ne.f w =
                    c) (Finset.filter (fun w => G.Adj y w) Finset.univ)).card ≥ 2) A'_colors, 1
                      := by
                rw [Finset.sum_filter]
                rw [← Finset.sum_add_distrib]
                exact Finset.sum_le_sum fun x hx => by
                  have hx_pos :
                      Finset.card
                        (Finset.filter (fun w => ne.f w = x)
                          (Finset.filter (fun w => G.Adj y w) Finset.univ)) ≥ 1 := by
                    obtain ⟨w, hw₁, hw₂⟩ := h_has_nbr_A' x hx
                    exact Finset.card_pos.mpr
                      ⟨w,
                        Finset.mem_filter.mpr
                          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw₂⟩, hw₁⟩⟩
                  split_ifs <;> linarith
              generalize_proofs at *; (
              simp +zetaDelta at *; omega;));
            have h_solo_set : {z ∈ A'_verts | y ∈ Solo z} =
              Finset.biUnion (Finset.filter (fun c => (Finset.filter (fun w => ne.f w =
                c) (Finset.filter (fun w => G.Adj y w) Finset.univ)).card = 1) A'_colors) (fun c =>
                  Finset.filter (fun z => ne.f z = c ∧ G.Adj y z ∧ ∀ w, ne.f w = c →
                    w ≠ z → ¬G.Adj y w) A'_verts) := by
              ext z; simp [Solo, hA'_verts_def];
              simp [Finset.card_eq_one, Finset.filter_filter];
              simp [Finset.eq_singleton_iff_unique_mem];
              grind;
            rw [h_solo_set, Finset.card_biUnion];
            · refine le_trans ?_ (Finset.sum_le_sum fun c hc => Finset.card_pos.mpr ?_);
              · simp +zetaDelta at *;
                rw [show (Finset.filter (fun c => Finset.card (Finset.filter (fun w => ne.f w =
                  c) (Finset.filter (fun w => G.Adj y w) Finset.univ)) =
                    1) (Finset.erase (Finset.filter (fun c =>
                      IsAccessible G ne.f ne.small c) Finset.univ) ne.small)) =
                        Finset.erase (Finset.filter (fun c =>
                          IsAccessible G ne.f ne.small c) Finset.univ) ne.small \
                            (Finset.filter
                              (fun c =>
                                2 ≤ Finset.card
                                  (Finset.filter
                                    (fun w => ne.f w = c)
                                    (Finset.filter (fun w => G.Adj y w) Finset.univ)))
                              (Finset.erase
                                (Finset.filter
                                  (fun c => IsAccessible G ne.f ne.small c) Finset.univ)
                                ne.small)) from ?_];
                · grind;
                · ext; simp [Finset.mem_sdiff, Finset.mem_filter];
                  exact fun _ _ =>
                    ⟨fun h => fun _ _ => by linarith,
                      fun h => by
                        have h_pos :
                            # (Finset.filter (fun w => ne.f w = ‹_›)
                                (Finset.filter (fun w => G.Adj y w) Finset.univ)) ≥ 1 := by
                          obtain ⟨w, hw₁, hw₂⟩ := h_has_nbr_A' _ ‹_› ‹_›
                          exact Finset.card_pos.mpr ⟨w, by aesop⟩
                        linarith [h ‹_› ‹_›, h_pos]⟩;
              · obtain ⟨z, hz⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hc |>.2);
                use z;
                simp [Finset.eq_singleton_iff_unique_mem] at hz ⊢;
                grind;
            · intros c hc d hd hcd; simp +contextual [Finset.disjoint_left, hcd];
          ·
            intro z hz
            have hz_mem := Finset.mem_filter.mp hz
            have hy_in_solo : y ∈ Solo z := hz_mem.2
            have hz_in_A' : z ∈ A'_verts := hz_mem.1
            have hz_A'_color : ne.f z ∈ A'_colors := (Finset.mem_filter.mp hz_in_A').2
            have hz_acc : IsAccessible G ne.f ne.small (ne.f z) :=
              (Finset.mem_filter.mp (Finset.mem_of_mem_erase hz_A'_color)).2
            have hz_ne_small : ne.f z ≠ ne.small := Finset.ne_of_mem_erase hz_A'_color
            have hz_ne_large : ne.f z ≠ ne.large := by
              intro h; exact hlarge_nmem (h ▸ Finset.mem_of_mem_erase hz_A'_color)
            have hy_solo := Finset.mem_filter.mp hy_in_solo
            have h_bad := h_all_bad (ne.f z) z y hz_acc hz_ne_small hz_ne_large rfl
              hy_nacc hy_solo.2.1 hy_solo.2.2
            have h_sub : (Solo z).erase y ⊆ B_verts.filter (fun w => G.Adj y w) := by
              intro w hw
              have hw_ne := Finset.ne_of_mem_erase hw
              have hw_solo := Finset.mem_of_mem_erase hw
              have hw_mem := Finset.mem_filter.mp hw_solo
              exact Finset.mem_filter.mpr ⟨hw_mem.1,
                h_bad.2 w hw_ne (Finset.mem_filter.mp hw_mem.1).2 hw_mem.2.1 hw_mem.2.2⟩
            have h_erase_card := Finset.card_erase_of_mem hy_in_solo
            have h_card_le := Finset.card_le_card h_sub
            have h_pos := Finset.card_pos.mpr ⟨y, hy_in_solo⟩
            omega
          ·
            intro z hz
            exact Finset.card_pos.mpr ⟨y, (Finset.mem_filter.mp hz).2⟩)
omit [DecidableEq V] in
lemma good_solo_vertex_exists
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large) :
    ∃ (W : Fin (r + 1)) (z y₁ : V),
      IsAccessible G ne.f ne.small W ∧
      W ≠ ne.small ∧ W ≠ ne.large ∧
      ne.f z = W ∧
      ¬IsAccessible G ne.f ne.small (ne.f y₁) ∧
      G.Adj y₁ z ∧
      (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₁ w) ∧
      ((∃ X : Fin (r+1), X ≠ W ∧ IsAccessible G ne.f ne.small X ∧
        ∀ w, ne.f w = X → ¬G.Adj z w) ∨
       (∃ y₂ : V, y₂ ≠ y₁ ∧ ¬IsAccessible G ne.f ne.small (ne.f y₂) ∧
        G.Adj y₂ z ∧ (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₂ w) ∧
        ¬G.Adj y₁ y₂ ∧
        (∀ X : Fin (r+1), IsAccessible G ne.f ne.small X → X ≠ W →
          ∃ w, ne.f w = X ∧ G.Adj z w))) := by
  classical
  by_contra h_neg
  apply solo_weight_contradiction G r s hs hd hs0 ne hacc
  intro W z y₁ hW_acc hW_ne_small hW_ne_large hz_color hy₁_nacc hadj huniq
  have h_not_movable : ∀ X, X ≠ W → IsAccessible G ne.f ne.small X →
      ∃ w, ne.f w = X ∧ G.Adj z w := by
    intro X hXW hXacc
    by_contra h_no
    exact h_neg ⟨W, z, y₁, hW_acc, hW_ne_small, hW_ne_large, hz_color, hy₁_nacc, hadj, huniq,
      Or.inl ⟨X, hXW, hXacc, fun w hw => by
        intro hadj_zw; exact h_no ⟨w, hw, hadj_zw⟩⟩⟩
  refine ⟨h_not_movable, fun y₂ hy₂_ne hy₂_nacc hy₂_adj hy₂_uniq => ?_⟩
  by_contra h_not_adj
  exact h_neg ⟨W, z, y₁, hW_acc, hW_ne_small, hW_ne_large, hz_color, hy₁_nacc, hadj, huniq,
    Or.inr ⟨y₂, hy₂_ne, hy₂_nacc, hy₂_adj, hy₂_uniq, h_not_adj,
      fun X hXacc hXW => h_not_movable X hXW hXacc⟩⟩
omit [DecidableEq V] in
set_option maxHeartbeats 1600000 in
lemma T_vertex_B_degree_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (_hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (_hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (_hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (T : Finset (Fin (r + 1)))
    (_hT_sub : ∀ c ∈ T, IsAccessible G ne.f ne.small c)
    (U : Fin (r + 1))
    (_hU_acc : IsAccessible G ne.f ne.small U)
    (hU_not_T : U ∉ T)
    (h_not_mov_outside : ∀ W ∈ T, ∀ x : V, ne.f x = W →
      ∀ V_out : Fin (r + 1), IsAccessible G ne.f ne.small V_out →
      V_out ∉ T → V_out ≠ U →
      ∃ w, ne.f w = V_out ∧ G.Adj x w)
    (x : V) (W : Fin (r + 1)) (hW_T : W ∈ T) (hx : ne.f x = W) :
    (Finset.univ.filter (fun w => G.Adj x w ∧ ¬IsAccessible G ne.f ne.small (ne.f w))).card
      ≤ r + 1 - (Finset.univ.filter (fun c : Fin (r + 1) =>
        IsAccessible G ne.f ne.small c)).card + T.card := by
  classical
  have h_acc_neighbors : (Finset.filter (fun w => G.Adj x w ∧
    IsAccessible G ne.f ne.small (ne.f w)) Finset.univ).card ≥ (Finset.filter (fun c =>
      IsAccessible G ne.f ne.small c) Finset.univ).card - T.card - 1 := by
    have h_acc_neighbors : (Finset.image (fun w => ne.f w) (Finset.filter (fun w => G.Adj x w ∧
      IsAccessible G ne.f ne.small (ne.f w)) Finset.univ)).card ≥ (Finset.filter (fun c =>
        IsAccessible G ne.f ne.small c) Finset.univ \ (T ∪ {U})).card := by
      refine Finset.card_le_card ?_;
      grind;
    grind +splitImp;
  have h_total_neighbors : (Finset.filter (fun w => G.Adj x w) Finset.univ).card ≤ r := by
    simpa [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
      using (SimpleGraph.degree_le_maxDegree G x).trans hd
  rw [show (Finset.filter (fun w => G.Adj x w ∧
    ¬IsAccessible G ne.f ne.small (ne.f w)) Finset.univ) = Finset.filter (fun w =>
      G.Adj x w) Finset.univ \ Finset.filter (fun w => G.Adj x w ∧
        IsAccessible G ne.f ne.small (ne.f w)) Finset.univ by ext; aesop];
          rw [Finset.card_sdiff]; simp_all;
  rw [show (Finset.filter (fun w => G.Adj x w ∧
    IsAccessible G ne.f ne.small (ne.f w)) Finset.univ ∩ Finset.filter (fun w =>
      G.Adj x w) Finset.univ) = Finset.filter (fun w => G.Adj x w ∧
        IsAccessible G ne.f ne.small (ne.f w)) Finset.univ by ext; aesop]; omega;
omit [DecidableEq V] in
set_option maxHeartbeats 1600000 in
lemma T_solo_vertex_B_degree_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (_hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (_hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (_hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (z y₁ : V) (W : Fin (r + 1))
    (_hz : ne.f z = W) (_hy₁_nacc : ¬IsAccessible G ne.f ne.small (ne.f y₁))
    (_hadj : G.Adj y₁ z) (_huniq : ∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₁ w)
    (h_nbr_all : ∀ X, X ≠ W → IsAccessible G ne.f ne.small X → ∃ w, ne.f w = X ∧
      G.Adj z w) :
    (Finset.univ.filter (fun w => G.Adj z w ∧ ¬IsAccessible G ne.f ne.small (ne.f w))).card
      ≤ r + 1 - (Finset.univ.filter (fun c : Fin (r + 1) => IsAccessible G ne.f ne.small c)).card
        := by
  classical
  have h_image : Finset.card (Finset.image (fun w => ne.f w) (Finset.univ.filter (fun w =>
    G.Adj z w ∧ IsAccessible G ne.f ne.small (ne.f w)))) ≥
      Finset.card (Finset.univ.filter (fun c => IsAccessible G ne.f ne.small c)) - 1 := by
    refine le_trans ?_ (Finset.card_mono <| show Finset.image (fun w =>
      ne.f w) (Finset.filter (fun w => G.Adj z w ∧
        IsAccessible G ne.f ne.small (ne.f w)) Finset.univ) ≥ Finset.univ.filter (fun c =>
          IsAccessible G ne.f ne.small c) \ { W } from ?_);
    · grind;
    · intro c hc
      rcases Finset.mem_sdiff.mp hc with ⟨hc_acc_mem, hc_ne_W_mem⟩
      have hc_acc : IsAccessible G ne.f ne.small c := (Finset.mem_filter.mp hc_acc_mem).2
      have hc_ne_W : c ≠ W := by
        intro h
        exact hc_ne_W_mem (by simp [h])
      rcases h_nbr_all c hc_ne_W hc_acc with ⟨w, hw_color, hw_adj⟩
      exact Finset.mem_image.mpr
        ⟨w, by simp [hw_adj, hc_acc, hw_color], hw_color⟩
  have h_acc_lower : Finset.card (Finset.univ.filter (fun w => G.Adj z w ∧
    IsAccessible G ne.f ne.small (ne.f w))) ≥ Finset.card (Finset.univ.filter (fun c =>
      IsAccessible G ne.f ne.small c)) - 1 := by
    exact h_image.trans (Finset.card_image_le);
  have h_partition_degree : Finset.card (Finset.univ.filter (fun w => G.Adj z w ∧
    ¬IsAccessible G ne.f ne.small (ne.f w))) + Finset.card (Finset.univ.filter (fun w =>
      G.Adj z w ∧ IsAccessible G ne.f ne.small (ne.f w))) ≤ G.degree z := by
    have h_partition_eq : Finset.card (Finset.univ.filter (fun w => G.Adj z w ∧
      ¬IsAccessible G ne.f ne.small (ne.f w))) + Finset.card (Finset.univ.filter (fun w =>
        G.Adj z w ∧ IsAccessible G ne.f ne.small (ne.f w))) =
        Finset.card (Finset.univ.filter (fun w => G.Adj z w)) := by
      rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro w _hw
      by_cases hadj : G.Adj z w <;>
        by_cases hacc_w : IsAccessible G ne.f ne.small (ne.f w) <;>
          simp [hadj, hacc_w]
    rw [h_partition_eq]
    simp [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
  have h_degree_le : G.degree z ≤ r := by
    exact le_trans (SimpleGraph.degree_le_maxDegree _ _) hd;
  have h_bound :
      Finset.card (Finset.univ.filter (fun w => G.Adj z w ∧
        ¬IsAccessible G ne.f ne.small (ne.f w))) +
        ((Finset.univ.filter (fun c : Fin (r + 1) =>
          IsAccessible G ne.f ne.small c)).card - 1) ≤ r := by
    exact (Nat.add_le_add_left h_acc_lower _).trans (h_partition_degree.trans h_degree_le)
  by_cases hC : (Finset.univ.filter (fun c : Fin (r + 1) =>
      IsAccessible G ne.f ne.small c)).card = 0
  · have h_nonacc_le_r : Finset.card (Finset.univ.filter (fun w => G.Adj z w ∧
        ¬IsAccessible G ne.f ne.small (ne.f w))) ≤ r := by
      omega
    omega
  · have hCpos : 0 < (Finset.univ.filter (fun c : Fin (r + 1) =>
        IsAccessible G ne.f ne.small c)).card := Nat.pos_of_ne_zero hC
    have h_bound' : Finset.card (Finset.univ.filter (fun w => G.Adj z w ∧
        ¬IsAccessible G ne.f ne.small (ne.f w))) +
        (Finset.univ.filter (fun c : Fin (r + 1) =>
          IsAccessible G ne.f ne.small c)).card ≤ r + 1 := by
      have h := Nat.add_le_add_right h_bound 1
      simpa [Nat.add_assoc, Nat.sub_add_cancel hCpos] using h
    exact Nat.le_sub_of_add_le h_bound'
omit [DecidableEq V] in
lemma B_card_eq_aux
    (G : SimpleGraph V)
    (r s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large) :
    (Finset.univ.filter (fun v : V => ¬IsAccessible G ne.f ne.small (ne.f v))).card =
    (r + 1 - (Finset.univ.filter (fun c : Fin (r + 1) => IsAccessible G ne.f ne.small c)).card) *
      s + 1 := by
  classical
  have h_union_accessible_size : ∑ c ∈ Finset.univ.filter (fun c =>
    IsAccessible G ne.f ne.small c), (cClass ne.f c).card = (Finset.univ.filter (fun c =>
      IsAccessible G ne.f ne.small c)).sum (fun c => if c = ne.small then s - 1 else s) := by
    refine Finset.sum_congr rfl fun c hc => ?_;
    split_ifs <;> simp_all [NearlyEquitable.card_small];
    exact ne.card_other c ‹_› (by rintro rfl; exact hacc hc);
  have h_total_vertices : (Finset.univ.filter (fun v =>
    ¬IsAccessible G ne.f ne.small (ne.f v))).card + (Finset.univ.filter (fun c =>
      IsAccessible G ne.f ne.small c)).sum (fun c => (cClass ne.f c).card) = Fintype.card V := by
    rw [← Finset.card_biUnion];
    · rw [← Finset.card_union_of_disjoint];
      · convert Finset.card_univ using 2; ext v;
        by_cases hv : IsAccessible G ne.f ne.small (ne.f v) <;> simp [hv];
      · simp +contextual [Finset.disjoint_left];
    · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz hz' => hxy <| by aesop;
  simp_all [Finset.sum_ite, Finset.filter_ne', Finset.filter_eq'];
  split_ifs at * <;> simp_all [Finset.card_erase_of_mem];
  · zify at *;
    rw [Nat.cast_sub] at * <;> push_cast at *;
    · rw [Nat.cast_sub] at * <;> push_cast at *;
      · grind +revert;
      · exact Finset.card_pos.mpr ⟨ne.small, by aesop⟩;
      · exact Finset.card_pos.mpr ⟨ne.small, by aesop⟩;
    · linarith;
    · linarith;
    · exact le_trans (Finset.card_le_univ _) (by simp);
  · exact False.elim
      (‹¬IsAccessible G ne.f ne.small ne.small› Relation.ReflTransGen.refl)
omit [DecidableEq V] in
lemma solo_card_le_q_aux
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (T : Finset (Fin (r + 1)))
    (W₀ : Fin (r + 1)) (hW₀ : W₀ ∈ T)
    (h_bad : ∀ (W : Fin (r + 1)), W ∈ T → ∀ (z y₁ : V),
      ne.f z = W → ¬IsAccessible G ne.f ne.small (ne.f y₁) →
      G.Adj y₁ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₁ w) →
      (∀ X, X ≠ W → IsAccessible G ne.f ne.small X → ∃ w, ne.f w = X ∧ G.Adj z w) ∧
      (∀ y₂, y₂ ≠ y₁ → ¬IsAccessible G ne.f ne.small (ne.f y₂) →
        G.Adj y₂ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₂ w) → G.Adj y₁ y₂))
    (z : V) (hz : ne.f z = W₀)
    (y₁ : V) (hy₁_nacc : ¬IsAccessible G ne.f ne.small (ne.f y₁))
    (hy₁_adj : G.Adj y₁ z) (hy₁_uniq : ∀ w, ne.f w = W₀ → w ≠ z → ¬G.Adj y₁ w) :
    (Finset.univ.filter (fun w => G.Adj z w ∧ ¬IsAccessible G ne.f ne.small (ne.f w))).card ≤
    r + 1 - (Finset.univ.filter (fun c : Fin (r + 1) => IsAccessible G ne.f ne.small c)).card := by
  classical
  exact
    T_solo_vertex_B_degree_bound G r s hs hd hs0 ne hacc z y₁ W₀ hz hy₁_nacc
      hy₁_adj hy₁_uniq ((h_bad W₀ hW₀ z y₁ hz hy₁_nacc hy₁_adj hy₁_uniq).1)
set_option maxHeartbeats 3200000 in
omit [DecidableEq V] in
lemma restricted_T_card_gt_q
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (T : Finset (Fin (r + 1)))
    (hT_sub : ∀ c ∈ T, IsAccessible G ne.f ne.small c)
    (hT_ne_small : ∀ c ∈ T, c ≠ ne.small)
    (hT_ne_large : ∀ c ∈ T, c ≠ ne.large)
    (hT_nonempty : T.Nonempty)
    (h_bad : ∀ (W : Fin (r + 1)), W ∈ T → ∀ (z y₁ : V),
      ne.f z = W → ¬IsAccessible G ne.f ne.small (ne.f y₁) →
      G.Adj y₁ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₁ w) →
      (∀ X, X ≠ W → IsAccessible G ne.f ne.small X → ∃ w, ne.f w = X ∧ G.Adj z w) ∧
      (∀ y₂, y₂ ≠ y₁ → ¬IsAccessible G ne.f ne.small (ne.f y₂) →
        G.Adj y₂ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₂ w) → G.Adj y₁ y₂))
    (U : Fin (r + 1))
    (hU_acc : IsAccessible G ne.f ne.small U)
    (hU_not_T : U ∉ T)
    (h_not_mov_outside : ∀ W ∈ T, ∀ x : V, ne.f x = W →
      ∀ V_out : Fin (r + 1), IsAccessible G ne.f ne.small V_out →
      V_out ∉ T → V_out ≠ U →
      ∃ w, ne.f w = V_out ∧ G.Adj x w) :
    (r + 1 - (Finset.univ.filter (fun c : Fin (r + 1) =>
      IsAccessible G ne.f ne.small c)).card) < T.card := by
  classical
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ ∈ T, True := by
    exact ⟨hT_nonempty.choose, hT_nonempty.choose_spec, trivial⟩;
  set B := Finset.univ.filter (fun v => ¬IsAccessible G ne.f ne.small (ne.f v))
  set W₀_class := cClass ne.f W₀;
  set p := (W₀_class.filter (fun z => ∃ y ∈ B, G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z →
    ¬G.Adj y w)).card;
  have h_upper_bound : ∑ z ∈ W₀_class, (B.filter (fun y => G.Adj y z)).card ≤ p * (r + 1 -
    Finset.card (Finset.univ.filter (fun c => IsAccessible G ne.f ne.small c))) + (s - p) * (r + 1 -
      Finset.card (Finset.univ.filter (fun c => IsAccessible G ne.f ne.small c)) + T.card) := by
    have h_upper_bound : ∀ z ∈ W₀_class, (B.filter (fun y => G.Adj y z)).card ≤
      if ∃ y ∈ B, G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w then r + 1 -
        Finset.card (Finset.univ.filter (fun c => IsAccessible G ne.f ne.small c)) else r + 1 -
          Finset.card (Finset.univ.filter (fun c => IsAccessible G ne.f ne.small c)) + T.card := by
      intro z hz
      by_cases h_solo : ∃ y ∈ B, G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w;
      · rw [if_pos h_solo];
        obtain ⟨y, hyB, hyz, hy⟩ := h_solo;
        have := solo_card_le_q_aux G r s hs hd hs0 ne hacc T W₀ hW₀.1 h_bad z (by
        exact Finset.mem_filter.mp hz |>.2) y (by
        exact Finset.mem_filter.mp hyB |>.2) hyz (by
        exact fun w hw hwz => hy w (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩) hwz);
        convert this using 1;
        simp [SimpleGraph.adj_comm];
        exact congr_arg Finset.card (by ext; aesop);
      · rw [if_neg h_solo];
        convert
          T_vertex_B_degree_bound G r s hs hd hs0 ne hacc T hT_sub U hU_acc
            hU_not_T h_not_mov_outside z W₀ hW₀.1 (by aesop)
          using 1;
        simp [SimpleGraph.adj_comm];
        exact congr_arg Finset.card (by ext; aesop);
    refine le_trans (Finset.sum_le_sum h_upper_bound) ?_;
    simp +zetaDelta at *;
    simp [Finset.sum_ite];
    rw [show (Finset.filter (fun x => ∀ x_1 : V,
      ¬IsAccessible G ne.f ne.small (ne.f x_1) → G.Adj x_1 x → ∃ x_2 : V, ne.f x_2 =
        W₀ ∧ ¬x_2 = x ∧ G.Adj x_1 x_2) (cClass ne.f W₀)) =
          cClass ne.f W₀ \ (Finset.filter (fun x => ∃ y : V,
            ¬IsAccessible G ne.f ne.small (ne.f y) ∧ G.Adj y x ∧ ∀ w : V, ne.f w = W₀ →
              ¬w = x → ¬G.Adj y w) (cClass ne.f W₀)) from ?_];
    · rw [Finset.card_sdiff]; norm_num [ne.card_other W₀ (by aesop) (by aesop)];
      simp [Finset.filter_inter];
    · grind;
  have h_lower_bound : ∑ y ∈ B, (W₀_class.filter (fun z => G.Adj y z)).card ≥ 2 * B.card -
    p * (r + 1 - Finset.card (Finset.univ.filter (fun c => IsAccessible G ne.f ne.small c))) := by
    have h_B_neighbor : ∀ y ∈ B, ∃ z ∈ W₀_class, G.Adj y z := by
      intro y hy;
      have := non_acc_has_acc_neighbor G (hT_sub W₀ hW₀.1) (Finset.mem_filter.mp hy |>.2);
      exact ⟨this.choose, Finset.mem_filter.mpr ⟨Finset.mem_univ _, this.choose_spec.1⟩,
        this.choose_spec.2⟩;
    have h_B_one_neighbor : ∑ y ∈ B, (if (W₀_class.filter (fun z => G.Adj y z)).card = 1
      then 1 else 0) ≤ p * (r + 1 - Finset.card (Finset.univ.filter (fun c =>
        IsAccessible G ne.f ne.small c))) := by
      have h_B_one_neighbor : ∀ z ∈ W₀_class.filter (fun z => ∃ y ∈ B, G.Adj y z ∧
        ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w), (B.filter (fun y => G.Adj y z ∧
          ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w)).card ≤ r + 1 -
            Finset.card (Finset.univ.filter (fun c => IsAccessible G ne.f ne.small c)) := by
        intros z hz
        have hz_degree : (B.filter (fun y => G.Adj y z ∧ ∀ w ∈ W₀_class, w ≠ z →
          ¬G.Adj y w)).card ≤ r + 1 - Finset.card (Finset.univ.filter (fun c =>
            IsAccessible G ne.f ne.small c)) := by
          have :=
            T_solo_vertex_B_degree_bound G r s hs hd hs0 ne hacc z
              (Classical.choose (Finset.mem_filter.mp hz).right) W₀ (by
          exact Finset.mem_filter.mp (Finset.mem_filter.mp hz |>.1) |>.2) (by
          grind) (by
          exact Classical.choose_spec (Finset.mem_filter.mp hz |>.2) |>.2.1) (by
          have := Classical.choose_spec (Finset.mem_filter.mp hz |>.2);
          exact fun w hw hwz => this.2.2 w (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            hw⟩) hwz)
          refine le_trans ?_ (this ?_);
          · refine Finset.card_le_card ?_;
            simp +contextual [Finset.subset_iff, SimpleGraph.adj_comm];
            exact fun x hx hx' hx'' => Finset.mem_filter.mp hx |>.2;
          · exact fun X hX₁ hX₂ =>
            h_bad W₀ hW₀.1 z (Classical.choose (Finset.mem_filter.mp hz |>.2)) (by
              exact Finset.mem_filter.mp (Finset.mem_filter.mp hz |>.1) |>.2) (by
              exact Classical.choose_spec (Finset.mem_filter.mp hz |>.2) |>.1 |>
                Finset.mem_filter.mp |>.2) (by
              exact Classical.choose_spec (Finset.mem_filter.mp hz |>.2) |>.2.1) (by
              exact fun w hw₁ hw₂ =>
                (Classical.choose_spec (Finset.mem_filter.mp hz |>.2)).2.2 w
                  (by aesop) hw₂) |>.1 X hX₁ hX₂;
        exact hz_degree;
      have h_B_one_neighbor : ∑ y ∈ B, (if (W₀_class.filter (fun z => G.Adj y z)).card = 1
        then 1 else 0) ≤ ∑ z ∈ W₀_class.filter (fun z => ∃ y ∈ B, G.Adj y z ∧
          ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w), (B.filter (fun y => G.Adj y z ∧
            ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w)).card := by
        have h_B_one_neighbor : ∀ y ∈ B, (if (W₀_class.filter (fun z => G.Adj y z)).card = 1
          then 1 else 0) ≤ ∑ z ∈ W₀_class.filter (fun z => ∃ y ∈ B, G.Adj y z ∧
            ∀ w ∈ W₀_class, w ≠ z → ¬G.Adj y w), (if G.Adj y z ∧ ∀ w ∈ W₀_class,
              w ≠ z → ¬G.Adj y w then 1 else 0) := by
          intro y hy
          by_cases h : (W₀_class.filter (fun z => G.Adj y z)).card = 1;
          · obtain ⟨z, hz⟩ := Finset.card_eq_one.mp h;
            rw [Finset.eq_singleton_iff_unique_mem] at hz;
            simp +zetaDelta at *;
            rw [if_pos h];
            refine Finset.card_pos.mpr ⟨z, ?_⟩; simp [hz];
            exact ⟨⟨y, hy, hz.1.2, fun w hw hw' hw'' => hw' <| hz.2 w hw hw''⟩,
              fun w hw hw' hw'' => hw' <| hz.2 w hw hw''⟩;
          · lia;
        refine le_trans (Finset.sum_le_sum h_B_one_neighbor) ?_;
        rw [Finset.sum_comm];
        simp;
      exact h_B_one_neighbor.trans (Finset.sum_le_card_nsmul _ _ _ fun x hx => by solve_by_elim);
    have h_B_contribution : ∑ y ∈ B, (W₀_class.filter (fun z => G.Adj y z)).card ≥
      ∑ y ∈ B, (if (W₀_class.filter (fun z => G.Adj y z)).card = 1 then 1 else 2) := by
      gcongr;
      split_ifs <;> norm_num;
      · exact Exists.elim (h_B_neighbor _ ‹_›) fun x hx => ⟨x, by aesop⟩;
      · exact Nat.lt_of_le_of_ne
          (Finset.card_pos.mpr
            ⟨Classical.choose (h_B_neighbor _ ‹_›),
              Finset.mem_filter.mpr
                ⟨Classical.choose_spec (h_B_neighbor _ ‹_›) |>.1,
                  Classical.choose_spec (h_B_neighbor _ ‹_›) |>.2⟩⟩)
          (Ne.symm ‹_›)
    simp_all [Finset.sum_ite];
    rw [show #B = # ({ x ∈ B | # ({ z ∈ W₀_class | G.Adj x z }) = 1 }) +
      # ({ x ∈ B | ¬# ({ z ∈ W₀_class | G.Adj x z }) =
        1 }) by rw [Finset.card_filter_add_card_filter_not]]; linarith;
  have h_fubini : ∑ z ∈ W₀_class, (B.filter (fun y => G.Adj y z)).card = ∑ y ∈ B,
    (W₀_class.filter (fun z => G.Adj y z)).card := by
    simp only [card_filter];
    exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      by simp);
  have hB_card : B.card = (r + 1 - Finset.card (Finset.univ.filter (fun c =>
    IsAccessible G ne.f ne.small c))) * s + 1 := by
    convert B_card_eq_aux G r s hs hs0 ne hacc using 1;
  contrapose! h_lower_bound;
  rw [Nat.lt_sub_iff_add_lt];
  rw [← h_fubini];
  refine lt_of_le_of_lt (Nat.add_le_add_right h_upper_bound _) ?_;
  rw [hB_card];
  have hp_le_s : p ≤ s := by
    have hp_le_s : W₀_class.card = s := by
      exact ne.card_other W₀ (hT_ne_small W₀ hW₀.1) (hT_ne_large W₀ hW₀.1);
    exact le_trans (Finset.card_filter_le _ _) hp_le_s.le;
  nlinarith only [Nat.sub_add_cancel hp_le_s, h_lower_bound, hp_le_s, hs0,
    Nat.sub_add_cancel (show Finset.card (Finset.filter (fun c =>
      IsAccessible G ne.f ne.small c) Finset.univ) ≤ r +
        1 from le_trans (Finset.card_le_univ _) (by simp))]
set_option maxHeartbeats 1600000 in
lemma restricted_Solo_card_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (T : Finset (Fin (r + 1)))
    (_hT_sub : ∀ c ∈ T, IsAccessible G ne.f ne.small c)
    (_hT_ne_small : ∀ c ∈ T, c ≠ ne.small)
    (_hT_ne_large : ∀ c ∈ T, c ≠ ne.large)
    (h_bad : ∀ (W : Fin (r + 1)), W ∈ T → ∀ (z y₁ : V),
      ne.f z = W → ¬IsAccessible G ne.f ne.small (ne.f y₁) →
      G.Adj y₁ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₁ w) →
      (∀ X, X ≠ W → IsAccessible G ne.f ne.small X → ∃ w, ne.f w = X ∧ G.Adj z w) ∧
      (∀ y₂, y₂ ≠ y₁ → ¬IsAccessible G ne.f ne.small (ne.f y₂) →
        G.Adj y₂ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₂ w) → G.Adj y₁ y₂)) :
    let B_verts := Finset.univ.filter (fun v : V => ¬IsAccessible G ne.f ne.small (ne.f v))
    let Solo : V → Finset V := fun z =>
      B_verts.filter (fun y => G.Adj y z ∧ ∀ w, ne.f w = ne.f z → w ≠ z → ¬G.Adj y w)
    let A'_verts := Finset.univ.filter (fun v : V => ne.f v ∈ T)
    let q := r + 1 - (Finset.univ.filter (fun c : Fin (r + 1) =>
      IsAccessible G ne.f ne.small c)).card
    ∀ z ∈ A'_verts, (Solo z).card ≤ q := by
  intro B_verts Solo A'_verts q z hz
  by_cases h_empty : (Solo z).card = 0
  · omega
  · obtain ⟨y₁, hy₁⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h_empty)
    have hy₁_B : y₁ ∈ B_verts := (Finset.mem_filter.mp hy₁).1
    have hy₁_nacc : ¬IsAccessible G ne.f ne.small (ne.f y₁) := (Finset.mem_filter.mp hy₁_B).2
    have hy₁_adj : G.Adj y₁ z := (Finset.mem_filter.mp hy₁).2.1
    have hy₁_uniq : ∀ w, ne.f w = ne.f z → w ≠ z →
      ¬G.Adj y₁ w := (Finset.mem_filter.mp hy₁).2.2
    have hz_T : ne.f z ∈ T := (Finset.mem_filter.mp hz).2
    have h_nbr_all := (h_bad (ne.f z) hz_T z y₁ rfl hy₁_nacc hy₁_adj hy₁_uniq).1
    have h_deg := T_solo_vertex_B_degree_bound G r s hs hd hs0 ne hacc z y₁ (ne.f z) rfl
      hy₁_nacc hy₁_adj hy₁_uniq h_nbr_all
    exact le_trans (Finset.card_le_card (fun x hx => by
      have hx_mem := Finset.mem_filter.mp hx
      have hx_B := Finset.mem_filter.mp hx_mem.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (SimpleGraph.adj_comm G _ _).mp hx_mem.2.1, hx_B.2⟩)) h_deg
set_option maxHeartbeats 1600000 in
lemma solo_card_le_dB_plus_one
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (_hs : Fintype.card V = (r + 1) * s)
    (_hd : G.maxDegree ≤ r) (_hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (_hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (T : Finset (Fin (r + 1)))
    (_hT_sub : ∀ c ∈ T, IsAccessible G ne.f ne.small c)
    (h_bad : ∀ (W : Fin (r + 1)), W ∈ T → ∀ (z y₁ : V),
      ne.f z = W → ¬IsAccessible G ne.f ne.small (ne.f y₁) →
      G.Adj y₁ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₁ w) →
      (∀ X, X ≠ W → IsAccessible G ne.f ne.small X → ∃ w, ne.f w = X ∧ G.Adj z w) ∧
      (∀ y₂, y₂ ≠ y₁ → ¬IsAccessible G ne.f ne.small (ne.f y₂) →
        G.Adj y₂ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₂ w) → G.Adj y₁ y₂))
    (y : V) (hy : y ∈ Finset.univ.filter (fun v : V => ¬IsAccessible G ne.f ne.small (ne.f v))) :
    let B_verts := Finset.univ.filter (fun v : V => ¬IsAccessible G ne.f ne.small (ne.f v))
    let Solo : V → Finset V := fun z =>
      B_verts.filter (fun y => G.Adj y z ∧ ∀ w, ne.f w = ne.f z → w ≠ z → ¬G.Adj y w)
    let A'_verts := Finset.univ.filter (fun v : V => ne.f v ∈ T)
    let dB := (B_verts.filter (fun w => G.Adj y w)).card
    ∀ z ∈ A'_verts.filter (fun z => y ∈ Solo z), (Solo z).card ≤ dB + 1 := by
  intro B_verts Solo A'_verts dB z hz;
  have h_erase : Solo z ⊆ insert y (B_verts.filter (fun w => G.Adj y w)) := by
    grind;
  exact le_trans (Finset.card_le_card h_erase) (Finset.card_insert_le _ _)
set_option maxHeartbeats 1600000 in
lemma sy_card_lower_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (_hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (_hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (T : Finset (Fin (r + 1)))
    (hT_sub : ∀ c ∈ T, IsAccessible G ne.f ne.small c)
    (hT_card_gt_q : (r + 1 - (Finset.univ.filter (fun c : Fin (r + 1) =>
      IsAccessible G ne.f ne.small c)).card) < T.card)
    (_h_bad : ∀ (W : Fin (r + 1)), W ∈ T → ∀ (z y₁ : V),
      ne.f z = W → ¬IsAccessible G ne.f ne.small (ne.f y₁) →
      G.Adj y₁ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₁ w) →
      (∀ X, X ≠ W → IsAccessible G ne.f ne.small X → ∃ w, ne.f w = X ∧ G.Adj z w) ∧
      (∀ y₂, y₂ ≠ y₁ → ¬IsAccessible G ne.f ne.small (ne.f y₂) →
        G.Adj y₂ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₂ w) → G.Adj y₁ y₂))
    (y : V) (hy : y ∈ Finset.univ.filter (fun v : V => ¬IsAccessible G ne.f ne.small (ne.f v))) :
    let B_verts := Finset.univ.filter (fun v : V => ¬IsAccessible G ne.f ne.small (ne.f v))
    let Solo : V → Finset V := fun z =>
      B_verts.filter (fun y => G.Adj y z ∧ ∀ w, ne.f w = ne.f z → w ≠ z → ¬G.Adj y w)
    let A'_verts := Finset.univ.filter (fun v : V => ne.f v ∈ T)
    let dB := (B_verts.filter (fun w => G.Adj y w)).card
    let q := r + 1 - (Finset.univ.filter (fun c : Fin (r + 1) =>
      IsAccessible G ne.f ne.small c)).card
    (A'_verts.filter (fun z => y ∈ Solo z)).card ≥ T.card - q + (dB + 1) := by
  intro B_verts Solo A'_verts dB q
  have hy_nacc : ¬IsAccessible G ne.f ne.small (ne.f y) := (Finset.mem_filter.mp hy).2
  set acc_colors := Finset.univ.filter (fun c : Fin (r + 1) => IsAccessible G ne.f ne.small c)
  have hT_gt_q : q < T.card := hT_card_gt_q
  have h_has_nbr : ∀ W ∈ T, ∃ w, ne.f w = W ∧ G.Adj y w :=
    fun W hW => non_acc_has_acc_neighbor G (hT_sub W hW) hy_nacc
  set S_y := A'_verts.filter (fun z => y ∈ Solo z)
  set nbrs_of_y_in := fun W : Fin (r + 1) => Finset.univ.filter (fun w : V => ne.f w = W ∧
    G.Adj y w)
  set solo_colors := T.filter (fun W => (nbrs_of_y_in W).card = 1)
  set multi_colors := T.filter (fun W => (nbrs_of_y_in W).card ≥ 2)
  have h_solo_inj : solo_colors.card ≤ S_y.card := by
    have h_inj : ∀ W ∈ solo_colors, ∃! z, z ∈ S_y ∧ ne.f z = W := by
      intro W hW;
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hW |>.2);
      use z;
      simp_all [Finset.ext_iff];
      simp +zetaDelta at *;
      grind;
    choose! f hf₁ hf₂ using h_inj;
    have h_inj : Function.Injective (fun W : solo_colors => f W W.2) := by
      intro W₁ W₂ h_eq;
      grind;
    have := Finset.card_le_card (show Finset.image (fun W : solo_colors =>
      f W W.2) Finset.univ ⊆ S_y from Finset.image_subset_iff.mpr fun W _ => hf₁ _ _ |>.1);
        simp [Finset.card_image_of_injective _ h_inj] at this ⊢; linarith;
  have h_multi_dB_bound : multi_colors.card + dB ≤ q - 1 := by
    have h_multi_colors_card : ∑ c ∈ acc_colors, (nbrs_of_y_in c).card ≤ r - dB := by
      have h_multi_colors_card : (∑ c ∈ acc_colors, (nbrs_of_y_in c).card) + dB ≤
        (SimpleGraph.neighborFinset G y).card := by
        have h_accessible_neighbors : ∑ c ∈ acc_colors, (nbrs_of_y_in c).card =
          (Finset.filter (fun w => IsAccessible G ne.f ne.small (ne.f w)) (G.neighborFinset y)).card
            := by
          rw [← Finset.card_biUnion]
          focus
            congr
          focus
            ext
          focus
            aesop
          exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz₁ hz₂ => hxy <| by aesop;
        rw [h_accessible_neighbors, ← Finset.card_union_of_disjoint];
        · exact Finset.card_le_card fun x hx => by aesop;
        · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by aesop;
      exact le_tsub_of_add_le_right
        (h_multi_colors_card.trans (by simpa using hd.trans' (G.degree_le_maxDegree y)))
    have h_multi_colors_card : ∑ c ∈ acc_colors, (nbrs_of_y_in c).card ≥ acc_colors.card +
      multi_colors.card := by
      have h_multi_colors_card : ∀ c ∈ acc_colors, (nbrs_of_y_in c).card ≥ 1 +
        (if c ∈ multi_colors then 1 else 0) := by
        intro c hc; split_ifs <;> simp_all;
        · grind;
        · simp +zetaDelta at *;
          exact non_acc_has_acc_neighbor G hc hy_nacc |> fun ⟨w, hw₁, hw₂⟩ => ⟨w,
            by aesop⟩;
      refine le_trans ?_ (Finset.sum_le_sum h_multi_colors_card);
      simp [Finset.sum_add_distrib];
      exact Finset.card_le_card fun x hx =>
        Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by aesop⟩, hx⟩;
    rw [Nat.le_sub_iff_add_le] at *;
    · grind;
    · have := G.degree_le_maxDegree y;
      exact le_trans (Finset.card_le_card (show Finset.filter (fun w =>
        G.Adj y w) B_verts ⊆ G.neighborFinset y from fun x hx =>
          by aesop)) (by simpa using this.trans hd);
    · grind
  have h_partition : solo_colors.card + multi_colors.card = T.card := by
    rw [← Finset.card_union_of_disjoint, Finset.filter_union_right];
    · refine congr_arg Finset.card (Finset.filter_true_of_mem fun x hx => ?_);
      exact Classical.or_iff_not_imp_left.2 fun h => Nat.lt_of_le_of_ne (Finset.card_pos.2 <|
        by obtain ⟨w, hw₁, hw₂⟩ := h_has_nbr x hx; exact ⟨w,
          by aesop⟩) (Ne.symm h);
    · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;
  have hq_pos : q ≥ 1 := Nat.sub_pos_of_lt (lt_of_lt_of_le (Finset.card_lt_card
    (Finset.filter_ssubset.mpr ⟨ne.large, Finset.mem_univ _, hacc⟩)) (by simp))
  have : q ≤ T.card := le_of_lt hT_gt_q
  have : multi_colors.card + dB + 1 ≤ q := by omega
  have : solo_colors.card ≥ T.card - q + dB + 1 := by omega
  omega
set_option maxHeartbeats 1600000 in
lemma restricted_Solo_lower_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (T : Finset (Fin (r + 1)))
    (hT_sub : ∀ c ∈ T, IsAccessible G ne.f ne.small c)
    (hT_card_gt_q : (r + 1 - (Finset.univ.filter (fun c : Fin (r + 1) =>
      IsAccessible G ne.f ne.small c)).card) < T.card)
    (h_bad : ∀ (W : Fin (r + 1)), W ∈ T → ∀ (z y₁ : V),
      ne.f z = W → ¬IsAccessible G ne.f ne.small (ne.f y₁) →
      G.Adj y₁ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₁ w) →
      (∀ X, X ≠ W → IsAccessible G ne.f ne.small X → ∃ w, ne.f w = X ∧ G.Adj z w) ∧
      (∀ y₂, y₂ ≠ y₁ → ¬IsAccessible G ne.f ne.small (ne.f y₂) →
        G.Adj y₂ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₂ w) → G.Adj y₁ y₂)) :
    let B_verts := Finset.univ.filter (fun v : V => ¬IsAccessible G ne.f ne.small (ne.f v))
    let Solo : V → Finset V := fun z =>
      B_verts.filter (fun y => G.Adj y z ∧ ∀ w, ne.f w = ne.f z → w ≠ z → ¬G.Adj y w)
    let A'_verts := Finset.univ.filter (fun v : V => ne.f v ∈ T)
    let q := r + 1 - (Finset.univ.filter (fun c : Fin (r + 1) =>
      IsAccessible G ne.f ne.small c)).card
    ∀ y ∈ B_verts,
      ∃ c_max : ℕ, 1 ≤ c_max ∧ c_max ≤ q ∧
        (A'_verts.filter (fun z => y ∈ Solo z)).card ≥ T.card - q + c_max ∧
        (∀ z ∈ A'_verts.filter (fun z => y ∈ Solo z), (Solo z).card ≤ c_max) ∧
        (∀ z ∈ A'_verts.filter (fun z => y ∈ Solo z), 1 ≤ (Solo z).card) := by
  intro B_verts Solo A'_verts q y hy
  have hy_nacc : ¬IsAccessible G ne.f ne.small (ne.f y) := (Finset.mem_filter.mp hy).2
  set acc_colors := Finset.univ.filter (fun c : Fin (r + 1) => IsAccessible G ne.f ne.small c)
  have h_has_nbr : ∀ c, IsAccessible G ne.f ne.small c → ∃ w, ne.f w = c ∧ G.Adj y w :=
    fun c hc => non_acc_has_acc_neighbor G hc hy_nacc
  have h_deg_y : G.degree y ≤ r := le_trans (G.degree_le_maxDegree y) hd
  set dB := (B_verts.filter (fun w => G.Adj y w)).card
  have hq_pos : 1 ≤ q := Nat.sub_pos_of_lt (lt_of_lt_of_le (Finset.card_lt_card
    (Finset.filter_ssubset.mpr ⟨ne.large, Finset.mem_univ _, hacc⟩)) (by simp))
  have hdB_le : dB ≤ q - 1 := by
    have h_deg_y_acc : Finset.card (Finset.filter (fun w =>
      IsAccessible G ne.f ne.small (ne.f w)) (G.neighborFinset y)) ≥ Finset.card acc_colors := by
      have h_deg_y_acc : Finset.card (Finset.image (fun w => ne.f w) (Finset.filter (fun w =>
        IsAccessible G ne.f ne.small (ne.f w)) (G.neighborFinset y))) ≥ Finset.card acc_colors
          := by
        refine Finset.card_le_card ?_;
        intro c hc; obtain ⟨w, rfl, hw⟩ := h_has_nbr c (Finset.mem_filter.mp hc |>.2);
          aesop;
      exact h_deg_y_acc.trans (Finset.card_image_le);
    have h_deg_y_nonacc : Finset.card (Finset.filter (fun w =>
      ¬IsAccessible G ne.f ne.small (ne.f w)) (G.neighborFinset y)) ≥ dB := by
      exact Finset.card_mono fun x hx => by aesop;
    have h_deg_y_total : Finset.card (Finset.filter (fun w =>
      IsAccessible G ne.f ne.small (ne.f w)) (G.neighborFinset y)) +
        Finset.card (Finset.filter (fun w =>
          ¬IsAccessible G ne.f ne.small (ne.f w)) (G.neighborFinset y)) = G.degree y := by
      rw [Finset.card_filter_add_card_filter_not, SimpleGraph.degree];
    grind
  exact ⟨dB + 1, by omega, by omega,
    sy_card_lower_bound G r s hs hd hs0 ne hacc T hT_sub hT_card_gt_q h_bad y hy,
    solo_card_le_dB_plus_one G r s hs hd hs0 ne hacc T hT_sub h_bad y hy,
    fun z hz => Finset.card_pos.mpr ⟨y, (Finset.mem_filter.mp hz).2⟩⟩
omit [DecidableEq V] in
lemma non_acc_verts_card_q
    (G : SimpleGraph V)
    (r : ℕ) (s : ℕ) (_hs : Fintype.card V = (r + 1) * s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large) :
    (Finset.univ.filter (fun v : V => ¬IsAccessible G ne.f ne.small (ne.f v))).card =
    (r + 1 - (Finset.univ.filter (fun c : Fin (r + 1) => IsAccessible G ne.f ne.small c)).card) *
      s + 1 := by
  classical
  have := ne.card_total;
  rw [tsub_mul, mul_comm];
  rw [mul_comm, this.symm];
  rw [tsub_add_eq_add_tsub];
  · rw [Fintype.card_eq_sum_ones];
    rw [Finset.sum_const, Finset.card_eq_sum_ones];
    rw [show (Finset.univ.filter fun v => ¬IsAccessible G ne.f ne.small (ne.f v)) =
      Finset.biUnion (Finset.univ.filter fun c => ¬IsAccessible G ne.f ne.small c) (fun c =>
        Finset.filter (fun v => ne.f v = c) Finset.univ) from ?_, Finset.sum_biUnion];
    · have h_card : ∀ c : Fin (r + 1), (Finset.univ.filter (fun v => ne.f v = c)).card = if c =
      ne.small then s - 1 else if c = ne.large then s + 1 else s := by
        have := ne.card_small; have := ne.card_large; have := ne.card_other; aesop;
      simp_all [Finset.sum_ite];
      simp [Finset.filter_eq', Finset.filter_ne'];
      split_ifs <;> simp_all
      · rw [show (Finset.univ.filter fun c => ¬IsAccessible G ne.f ne.small c) =
        Finset.univ \ (Finset.univ.filter fun c => IsAccessible G ne.f ne.small c) by
          ext
          simp, Finset.card_sdiff]; simp [Finset.card_univ];
        rw [tsub_tsub, add_comm];
        exact eq_tsub_of_add_eq (by
          nlinarith only [
            Nat.sub_add_cancel
              (show
                (Finset.card
                    (Finset.filter
                      (fun c => IsAccessible G ne.f ne.small c) Finset.univ) + 1) ≤
                  r + 1 from
                Nat.succ_le_of_lt
                  (lt_of_lt_of_le
                    (Finset.card_lt_card
                      (Finset.filter_ssubset.mpr ⟨ne.large, by aesop⟩))
                    (by simp)))])
      · exact False.elim
          (‹¬IsAccessible G ne.f ne.small ne.small› Relation.ReflTransGen.refl)
      · exact absurd ‹_› (ne.ne_small_large.symm);
    · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun v hvx hvy => hxy <| by aesop;
    · ext; aesop;
  · rw [this];
    exact Nat.mul_le_mul_right _ (le_trans (Finset.card_le_univ _) (by simp))
omit [DecidableEq V] in
set_option maxHeartbeats 3200000 in
lemma restricted_solo_weight_contradiction
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (T : Finset (Fin (r + 1)))
    (hT_sub : ∀ c ∈ T, IsAccessible G ne.f ne.small c)
    (hT_ne_small : ∀ c ∈ T, c ≠ ne.small)
    (hT_ne_large : ∀ c ∈ T, c ≠ ne.large)
    (hT_nonempty : T.Nonempty)
    (h_bad : ∀ (W : Fin (r + 1)), W ∈ T → ∀ (z y₁ : V),
      ne.f z = W → ¬IsAccessible G ne.f ne.small (ne.f y₁) →
      G.Adj y₁ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₁ w) →
      (∀ X, X ≠ W → IsAccessible G ne.f ne.small X → ∃ w, ne.f w = X ∧ G.Adj z w) ∧
      (∀ y₂, y₂ ≠ y₁ → ¬IsAccessible G ne.f ne.small (ne.f y₂) →
        G.Adj y₂ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₂ w) → G.Adj y₁ y₂))
    (U : Fin (r + 1))
    (hU_acc : IsAccessible G ne.f ne.small U)
    (hU_not_T : U ∉ T)
    (h_not_mov_outside : ∀ W ∈ T, ∀ x : V, ne.f x = W →
      ∀ V_out : Fin (r + 1), IsAccessible G ne.f ne.small V_out →
      V_out ∉ T → V_out ≠ U →
      ∃ w, ne.f w = V_out ∧ G.Adj x w) :
    False := by
  classical
  set acc_colors := Finset.univ.filter (fun c => IsAccessible G ne.f ne.small c)
  set q := r + 1 - acc_colors.card
  set B_verts := Finset.univ.filter (fun v : V => ¬IsAccessible G ne.f ne.small (ne.f v))
  set Solo : V → Finset V := fun z =>
    B_verts.filter (fun y => G.Adj y z ∧ ∀ w, ne.f w = ne.f z → w ≠ z → ¬G.Adj y w)
  set A'_verts := Finset.univ.filter (fun v : V => ne.f v ∈ T)
  have hq_ge_1 : 1 ≤ q := by
    exact Nat.sub_pos_of_lt (lt_of_lt_of_le (Finset.card_lt_card
      (Finset.filter_ssubset.mpr ⟨ne.large, Finset.mem_univ _, hacc⟩)) (by simp))
  have ht : q < T.card :=
    restricted_T_card_gt_q G r s hs hd hs0 ne hacc T hT_sub hT_ne_small hT_ne_large
      hT_nonempty h_bad U hU_acc hU_not_T h_not_mov_outside
  have hA_card : A'_verts.card ≤ T.card * s := by
    have hA'_verts_union : A'_verts = Finset.biUnion T (fun c => Finset.filter (fun v => ne.f v =
      c) Finset.univ) := by
      ext v; simp [A'_verts, Finset.mem_biUnion];
    rw [hA'_verts_union, Finset.card_biUnion];
    · refine le_trans (Finset.sum_le_sum fun x hx => show Finset.card (Finset.filter (fun v =>
      ne.f v = x) Finset.univ) ≤ s from ?_) ?_;
      · exact ne.card_other x (hT_ne_small x hx) (hT_ne_large x hx) |> fun h => h.le;
      · simp;
    · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun v hvx hvy => hxy <| by aesop;
  have hB_card : B_verts.card = q * s + 1 := by
    exact non_acc_verts_card_q G r s hs ne hacc
  exact weight_function_contradiction A'_verts B_verts Solo q T.card s hq_ge_1 ht hs0
    hA_card hB_card (fun z _ => Finset.filter_subset _ _)
    (fun z _ h => Finset.card_pos.mpr h)
    (restricted_Solo_card_le G r s hs hd hs0 ne hacc T hT_sub hT_ne_small hT_ne_large h_bad)
    (restricted_Solo_lower_bound G r s hs hd hs0 ne hacc T hT_sub ht h_bad)
omit [DecidableEq V] in
set_option maxHeartbeats 3200000 in
lemma terminal_weight_contradiction
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (h_neg : ¬∃ (W : Fin (r + 1)) (z y₁ : V),
      IsAccessible G ne.f ne.small W ∧ W ≠ ne.small ∧ W ≠ ne.large ∧
      ne.f z = W ∧ ¬IsAccessible G ne.f ne.small (ne.f y₁) ∧
      G.Adj y₁ z ∧ (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₁ w) ∧
      (∀ C : Fin (r + 1), IsAccessible G ne.f ne.small C → C ≠ W →
        Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W) C ne.small) ∧
      ((∃ X : Fin (r+1), X ≠ W ∧ IsAccessible G ne.f ne.small X ∧
        ∀ w, ne.f w = X → ¬G.Adj z w) ∨
       (∃ y₂ : V, y₂ ≠ y₁ ∧ ¬IsAccessible G ne.f ne.small (ne.f y₂) ∧
        G.Adj y₂ z ∧ (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₂ w) ∧
        ¬G.Adj y₁ y₂ ∧
        (∀ X : Fin (r+1), IsAccessible G ne.f ne.small X → X ≠ W →
          ∃ w, ne.f w = X ∧ G.Adj z w)))) :
    False := by
  classical
  have h_bad_from_terminal : ∀ (W : Fin (r + 1)) (z y₁ : V),
      IsAccessible G ne.f ne.small W → W ≠ ne.small → W ≠ ne.large →
      ne.f z = W → ¬IsAccessible G ne.f ne.small (ne.f y₁) →
      G.Adj y₁ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₁ w) →
      (∀ C : Fin (r + 1), IsAccessible G ne.f ne.small C → C ≠ W →
        Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W) C ne.small) →
      (∀ X, X ≠ W → IsAccessible G ne.f ne.small X → ∃ w, ne.f w = X ∧ G.Adj z w) ∧
      (∀ y₂, y₂ ≠ y₁ → ¬IsAccessible G ne.f ne.small (ne.f y₂) →
        G.Adj y₂ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₂ w) → G.Adj y₁ y₂)
          := by
    intro W z y₁ hW_acc hW_ne_small hW_ne_large hz_color hy₁_nacc hadj huniq hW_term
    have h_not_movable : ∀ X, X ≠ W → IsAccessible G ne.f ne.small X →
        ∃ w, ne.f w = X ∧ G.Adj z w := by
      intro X hXW hXacc
      by_contra h_no_nbr; push Not at h_no_nbr
      exact h_neg ⟨W, z, y₁, hW_acc, hW_ne_small, hW_ne_large, hz_color, hy₁_nacc,
        hadj, huniq, hW_term, Or.inl ⟨X, hXW, hXacc, fun w hw => by
          exact fun hadj_zw => (h_no_nbr w hw).elim hadj_zw⟩⟩
    refine ⟨h_not_movable, ?_⟩
    intro y₂ hy₂_ne hy₂_nacc hy₂_adj hy₂_uniq
    by_contra h_not_adj
    exact h_neg ⟨W, z, y₁, hW_acc, hW_ne_small, hW_ne_large, hz_color, hy₁_nacc,
      hadj, huniq, hW_term,
      Or.inr ⟨y₂, hy₂_ne, hy₂_nacc, hy₂_adj, hy₂_uniq, h_not_adj,
        fun X hXacc hXW => h_not_movable X hXW hXacc⟩⟩
  obtain ⟨W₀, z₀, y₁₀, hW₀_acc, hW₀_ne_small, hW₀_ne_large, hz₀, hy₁₀_nacc,
    hadj₀, huniq₀, hcases₀⟩ := good_solo_vertex_exists G r s hs hd hs0 ne hacc
  have hW₀_nonterm : ¬∀ C : Fin (r + 1), IsAccessible G ne.f ne.small C → C ≠ W₀ →
      Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W₀) C ne.small := by
    intro h; exact h_neg ⟨W₀, z₀, y₁₀, hW₀_acc, hW₀_ne_small, hW₀_ne_large, hz₀,
      hy₁₀_nacc, hadj₀, huniq₀, h, hcases₀⟩
  push Not at hW₀_nonterm
  obtain ⟨C₀, hC₀_acc, hC₀_ne_W₀, hC₀_cant⟩ := hW₀_nonterm
  set R := AuxAdj G ne.f with hR_def
  set acc_colors := Finset.univ.filter (fun c : Fin (r + 1) => IsAccessible G ne.f ne.small c)
  let T_of (U : Fin (r + 1)) := acc_colors.filter (fun c => c ≠ U ∧
    ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ U) c ne.small)
  have hC₀_in : C₀ ∈ T_of W₀ :=
    Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC₀_acc⟩,
      hC₀_ne_W₀, hC₀_cant⟩
  set NonTerm := acc_colors.filter (fun U => (T_of U).Nonempty) with hNonTerm_def
  have hW₀_nonterm' : W₀ ∈ NonTerm := by
    simp only [NonTerm, Finset.mem_filter]
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hW₀_acc⟩, ⟨C₀, hC₀_in⟩⟩
  obtain ⟨U, hU_mem, hU_min⟩ := NonTerm.exists_min_image (fun U => (T_of U).card)
    ⟨W₀, hW₀_nonterm'⟩
  have hU_acc : IsAccessible G ne.f ne.small U := by
    have := (Finset.mem_filter.mp hU_mem).1; exact (Finset.mem_filter.mp this).2
  have hU_nonterm_T : (T_of U).Nonempty := (Finset.mem_filter.mp hU_mem).2
  set T := T_of U with hT_def
  have hT_terminal : ∀ W ∈ T, ∀ C : Fin (r + 1),
      IsAccessible G ne.f ne.small C → C ≠ W →
      Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W) C ne.small := by
    intro W hW C hC_acc hC_ne
    have hU_nonterm_witness : ∃ C ∈ acc_colors, C ≠ U ∧
        ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ U) C ne.small := by
      obtain ⟨c₀, hc₀⟩ := hU_nonterm_T
      exact ⟨c₀, (Finset.mem_filter.mp hc₀).1,
        (Finset.mem_filter.mp hc₀).2.1, (Finset.mem_filter.mp hc₀).2.2⟩
    have hT_min : ∀ V ∈ acc_colors,
        (∃ C ∈ acc_colors, C ≠ V ∧
          ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ V) C ne.small) →
        T.card ≤ (acc_colors.filter (fun c => c ≠ V ∧
          ¬Relation.ReflTransGen (fun a b => R a b ∧ a ≠ V) c ne.small)).card := by
      intro V hV hV_nonterm
      have hV_nonterm_T : (T_of V).Nonempty := by
        obtain ⟨C', hC'_acc, hC'_ne, hC'_cant⟩ := hV_nonterm
        exact ⟨C', Finset.mem_filter.mpr ⟨hC'_acc, hC'_ne, hC'_cant⟩⟩
      exact hU_min V (Finset.mem_filter.mpr ⟨hV, hV_nonterm_T⟩)
    exact terminal_set_members_are_terminal R ne.small acc_colors
      (fun c hc => (Finset.mem_filter.mp hc).2) U
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU_acc⟩)
      hU_nonterm_witness T rfl hT_min W hW C
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC_acc⟩) hC_ne
  have hT_sub : ∀ c ∈ T, IsAccessible G ne.f ne.small c := by
    intro c hc; exact (Finset.mem_filter.mp ((Finset.mem_filter.mp hc).1)).2
  have hT_ne_small : ∀ c ∈ T, c ≠ ne.small := by
    intro c hc habs; subst habs
    exact (Finset.mem_filter.mp hc).2.2 Relation.ReflTransGen.refl
  have hT_ne_large : ∀ c ∈ T, c ≠ ne.large := by
    intro c hc habs; subst habs; exact hacc ((Finset.mem_filter.mp ((Finset.mem_filter.mp hc).1)).2)
  have h_T_bad : ∀ W ∈ T, ∀ (z y₁ : V),
      ne.f z = W → ¬IsAccessible G ne.f ne.small (ne.f y₁) →
      G.Adj y₁ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₁ w) →
      (∀ X, X ≠ W → IsAccessible G ne.f ne.small X → ∃ w, ne.f w = X ∧ G.Adj z w) ∧
      (∀ y₂, y₂ ≠ y₁ → ¬IsAccessible G ne.f ne.small (ne.f y₂) →
        G.Adj y₂ z → (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₂ w) → G.Adj y₁ y₂)
          := by
    intro W hW z y₁ hz hy₁ hadj huniq
    exact h_bad_from_terminal W z y₁ (hT_sub W hW) (hT_ne_small W hW) (hT_ne_large W hW)
      hz hy₁ hadj huniq (hT_terminal W hW)
  have h_not_mov : ∀ W ∈ T, ∀ x : V, ne.f x = W →
      ∀ V_out : Fin (r + 1), IsAccessible G ne.f ne.small V_out →
      V_out ∉ T → V_out ≠ U →
      ∃ w, ne.f w = V_out ∧ G.Adj x w := by
    intro W hW x hx V_out hV_out_acc hV_out_not_T hV_out_ne_U
    by_contra h_no_nbr
    push Not at h_no_nbr
    have h_aux : AuxAdj G ne.f W V_out := ⟨x, hx, fun w hw => h_no_nbr w hw⟩
    have hW_props := (Finset.mem_filter.mp hW).2
    apply hW_props.2
    have hV_out_reach : Relation.ReflTransGen (fun a b => R a b ∧ a ≠ U) V_out ne.small := by
      have hV_out_in_acc : V_out ∈ acc_colors :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hV_out_acc⟩
      have hV_not_T : V_out ∉ T := hV_out_not_T
      by_contra h_cant
      apply hV_not_T
      exact Finset.mem_filter.mpr ⟨hV_out_in_acc, hV_out_ne_U, h_cant⟩
    exact Relation.ReflTransGen.head ⟨h_aux, hW_props.1⟩ hV_out_reach
  have hU_not_T : U ∉ T := by
    intro habs; exact (Finset.mem_filter.mp habs).2.1 rfl
  exact restricted_solo_weight_contradiction G r s hs hd hs0 ne hacc
    T hT_sub hT_ne_small hT_ne_large hU_nonterm_T h_T_bad U hU_acc hU_not_T h_not_mov
omit [DecidableEq V] in
set_option maxHeartbeats 800000 in
lemma no_terminal_good_solo_contradiction
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (W_t : Fin (r + 1))
    (_hWt_acc : IsAccessible G ne.f ne.small W_t)
    (_hWt_ne_small : W_t ≠ ne.small)
    (_hWt_terminal : ∀ C : Fin (r + 1), IsAccessible G ne.f ne.small C → C ≠ W_t →
      Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W_t) C ne.small)
    (h_neg : ¬∃ (W : Fin (r + 1)) (z y₁ : V),
      IsAccessible G ne.f ne.small W ∧ W ≠ ne.small ∧ W ≠ ne.large ∧
      ne.f z = W ∧ ¬IsAccessible G ne.f ne.small (ne.f y₁) ∧
      G.Adj y₁ z ∧ (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₁ w) ∧
      (∀ C : Fin (r + 1), IsAccessible G ne.f ne.small C → C ≠ W →
        Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W) C ne.small) ∧
      ((∃ X : Fin (r+1), X ≠ W ∧ IsAccessible G ne.f ne.small X ∧
        ∀ w, ne.f w = X → ¬G.Adj z w) ∨
       (∃ y₂ : V, y₂ ≠ y₁ ∧ ¬IsAccessible G ne.f ne.small (ne.f y₂) ∧
        G.Adj y₂ z ∧ (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₂ w) ∧
        ¬G.Adj y₁ y₂ ∧
        (∀ X : Fin (r+1), IsAccessible G ne.f ne.small X → X ≠ W →
          ∃ w, ne.f w = X ∧ G.Adj z w)))) :
    False := by
  classical
  by_cases h_all_term : ∀ W : Fin (r + 1),
    IsAccessible G ne.f ne.small W → W ≠ ne.small → W ≠ ne.large →
    ∀ C : Fin (r + 1), IsAccessible G ne.f ne.small C → C ≠ W →
      Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W) C ne.small
  ·
    apply solo_weight_contradiction G r s hs hd hs0 ne hacc
    intro W z y₁ hW_acc hW_ne_small hW_ne_large hz_color hy₁_nacc hadj huniq
    have hW_term := h_all_term W hW_acc hW_ne_small hW_ne_large
    have h_not_movable : ∀ X, X ≠ W → IsAccessible G ne.f ne.small X →
        ∃ w, ne.f w = X ∧ G.Adj z w := by
      intro X hXW hXacc
      by_contra h_no
      push Not at h_no
      exact h_neg ⟨W, z, y₁, hW_acc, hW_ne_small, hW_ne_large, hz_color, hy₁_nacc, hadj,
        huniq,
        hW_term, Or.inl ⟨X, hXW, hXacc, fun w hw => h_no w hw⟩⟩
    refine ⟨h_not_movable, fun y₂ hy₂_ne hy₂_nacc hy₂_adj hy₂_uniq => ?_⟩
    by_contra h_not_adj
    exact h_neg ⟨W, z, y₁, hW_acc, hW_ne_small, hW_ne_large, hz_color, hy₁_nacc, hadj, huniq,
      hW_term, Or.inr ⟨y₂, hy₂_ne, hy₂_nacc, hy₂_adj, hy₂_uniq, h_not_adj,
        fun X hXacc hXW => h_not_movable X hXW hXacc⟩⟩
  ·
    push Not at h_all_term
    obtain ⟨U, hU_acc, hU_ne_small, hU_ne_large, C₀, hC₀_acc, hC₀_ne_U,
      hC₀_cant⟩ := h_all_term
    exact terminal_weight_contradiction G r s hs hd hs0 ne hacc h_neg
omit [DecidableEq V] in
lemma good_solo_vertex_exists_terminal
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large) :
    ∃ (W : Fin (r + 1)) (z y₁ : V),
      IsAccessible G ne.f ne.small W ∧
      W ≠ ne.small ∧ W ≠ ne.large ∧
      ne.f z = W ∧
      ¬IsAccessible G ne.f ne.small (ne.f y₁) ∧
      G.Adj y₁ z ∧
      (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₁ w) ∧
      (∀ C : Fin (r + 1), IsAccessible G ne.f ne.small C → C ≠ W →
        Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W) C ne.small) ∧
      ((∃ X : Fin (r+1), X ≠ W ∧ IsAccessible G ne.f ne.small X ∧
        ∀ w, ne.f w = X → ¬G.Adj z w) ∨
       (∃ y₂ : V, y₂ ≠ y₁ ∧ ¬IsAccessible G ne.f ne.small (ne.f y₂) ∧
        G.Adj y₂ z ∧ (∀ w, ne.f w = W → w ≠ z → ¬G.Adj y₂ w) ∧
        ¬G.Adj y₁ y₂ ∧
        (∀ X : Fin (r+1), IsAccessible G ne.f ne.small X → X ≠ W →
          ∃ w, ne.f w = X ∧ G.Adj z w))) := by
  classical
  obtain ⟨W, z, y₁, hW_acc, hW_ne_small, hW_ne_large, hz_color, hy₁_nacc,
    hadj_y₁_z, huniq_y₁, hcases⟩ :=
    good_solo_vertex_exists G r s hs hd hs0 ne hacc
  by_cases hW_term : ∀ C : Fin (r + 1), IsAccessible G ne.f ne.small C → C ≠ W →
      Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W) C ne.small
  · exact ⟨W, z, y₁, hW_acc, hW_ne_small, hW_ne_large, hz_color, hy₁_nacc,
      hadj_y₁_z, huniq_y₁, hW_term, hcases⟩
  ·
    by_contra h_neg
    obtain ⟨W_t, hWt_acc, hWt_ne_small, hWt_terminal⟩ :=
      exists_terminal_color G (r + 1) ne.f ne.small W hW_acc hW_ne_small
    apply solo_weight_contradiction G r s hs hd hs0 ne hacc
    intro W' z' y₁' hW'_acc hW'_ne_small hW'_ne_large hz'_color hy₁'_nacc hadj' huniq'
    have h_bad_part1 : ∀ X, X ≠ W' → IsAccessible G ne.f ne.small X → ∃ w, ne.f w = X ∧
      G.Adj z' w := by
      intro X hXW' hXacc
      by_contra h_no
      push Not at h_no
      by_cases hW'_term : ∀ C : Fin (r + 1), IsAccessible G ne.f ne.small C → C ≠ W' →
          Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W') C ne.small
      · exact h_neg ⟨W', z', y₁', hW'_acc, hW'_ne_small, hW'_ne_large, hz'_color,
          hy₁'_nacc, hadj', huniq', hW'_term,
          Or.inl ⟨X, hXW', hXacc, fun w hw hadj_zw => h_no w hw |>.elim hadj_zw⟩⟩
      ·
        exfalso
        exact no_terminal_good_solo_contradiction G r s hs hd hs0 ne hacc
          W_t hWt_acc hWt_ne_small hWt_terminal h_neg
    refine ⟨h_bad_part1, ?_⟩
    ·
      intro y₂' hy₂'_ne hy₂'_nacc hy₂'_adj hy₂'_uniq
      by_contra h_not_adj
      by_cases hW'_term : ∀ C : Fin (r + 1), IsAccessible G ne.f ne.small C → C ≠ W' →
          Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W') C ne.small
      ·
        exact h_neg ⟨W', z', y₁', hW'_acc, hW'_ne_small, hW'_ne_large, hz'_color,
          hy₁'_nacc, hadj', huniq', hW'_term,
          Or.inr ⟨y₂', hy₂'_ne, hy₂'_nacc, hy₂'_adj, hy₂'_uniq, h_not_adj,
            fun X hXacc hXW' => h_bad_part1 X hXW' hXacc⟩⟩
      ·
        exact no_terminal_good_solo_contradiction G r s hs hd hs0 ne hacc
          W_t hWt_acc hWt_ne_small hWt_terminal h_neg
omit [DecidableEq V] in
lemma combine_disjoint_equitable
    (G : SimpleGraph V)
    (A_set : Set V) [DecidablePred (· ∈ A_set)]
    (a b s_val : ℕ)
    (hA_card : Fintype.card ↥A_set = a * s_val)
    (hB_card : Fintype.card ↥(A_setᶜ) = b * s_val)
    (fA : ↥A_set → Fin a) (fB : ↥(A_setᶜ) → Fin b)
    (hfA_proper : IsProper (G.induce A_set) fA)
    (hfB_proper : IsProper (G.induce A_setᶜ) fB)
    (hfA_equitable : IsEquitable fA)
    (hfB_equitable : IsEquitable fB) :
    HasEquitableColoring G (a + b) := by
  classical
  use fun v => if h : v ∈ A_set then Fin.castAdd b (fA ⟨v, h⟩)
    else Fin.natAdd a (fB ⟨v, by simpa using h⟩);
  refine ⟨fun v w hvw => ?_, fun c₁ c₂ => ?_⟩;
  · by_cases hv : v ∈ A_set <;> by_cases hw : w ∈ A_set <;> simp [hv, hw];
    · exact hfA_proper _ _ (by simpa [hv, hw] using hvw);
    · simp [Fin.ext_iff];
      grind;
    · simp [Fin.ext_iff];
      grind;
    · exact hfB_proper _ _ (by simpa [hv, hw] using hvw);
  ·
    have h_classes : ∀ c : Fin (a + b), (cClass (fun v => if h : v ∈ A_set
      then Fin.castAdd b (fA ⟨v, h⟩) else Fin.natAdd a (fB ⟨v, by simpa using h⟩)) c).card =
        if h : c.val < a then (cClass fA ⟨c.val, by
      exact h⟩).card else (cClass fB ⟨c.val - a, by
      rw [tsub_lt_iff_left] <;> linarith [Fin.is_lt c]⟩).card := by
      intro c; split_ifs <;> simp_all [cClass];
      · refine Finset.card_bij (fun v hv => ⟨v, ?_⟩) ?_ ?_ ?_ <;>
        simp_all [Fin.ext_iff];
        focus
          grind +locals
        grind +splitImp;
      · rw [Finset.card_filter, Finset.card_filter];
        rw [← Finset.sum_subset (Finset.subset_univ (Finset.filter (fun x =>
          x∉A_set) Finset.univ))];
        · refine Finset.sum_bij (fun x hx => ⟨x, by aesop⟩) ?_ ?_ ?_ ?_ <;>
          simp [Fin.ext_iff];
          grind;
        · grind
    generalize_proofs at *;
    have h_classes_fA : ∀ c : Fin a, (cClass fA c).card = s_val := by
      apply equitable_all_same_size hfA_equitable hA_card
    have h_classes_fB : ∀ c : Fin b, (cClass fB c).card = s_val := by
      apply equitable_all_same_size hfB_equitable hB_card
    generalize_proofs at *;
    grind +ring
omit [DecidableEq V] in
lemma non_acc_verts_card
    (G : SimpleGraph V)
    (r : ℕ) (s : ℕ) (_hs : Fintype.card V = (r + 1) * s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large) :
    (Finset.univ.filter (fun v : V => ¬IsAccessible G ne.f ne.small (ne.f v))).card =
    (Finset.univ.filter (fun c : Fin (r + 1) => ¬IsAccessible G ne.f ne.small c)).card * s + 1
      := by
  classical
  have h_sum : ∑ c ∈ Finset.univ.filter (fun c => ¬IsAccessible G ne.f ne.small c),
    (cClass ne.f c).card = (Finset.univ.filter (fun c => ¬IsAccessible G ne.f ne.small c)).card *
      s + 1 := by
    have h_sum : ∑ c ∈ Finset.univ.filter (fun c => ¬IsAccessible G ne.f ne.small c),
      (cClass ne.f c).card = ∑ c ∈ Finset.univ.filter (fun c =>
        ¬IsAccessible G ne.f ne.small c), (if c = ne.large then s + 1 else s) := by
      refine Finset.sum_congr rfl fun c hc => ?_;
      split_ifs <;> simp_all;
      · exact ne.card_large;
      · exact ne.card_other c
          (by
            rintro rfl
            exact hc Relation.ReflTransGen.refl)
          (by assumption);
    simp_all [Finset.sum_ite, Finset.filter_ne', Finset.filter_eq'];
    nlinarith only [Nat.sub_add_cancel (show 1 ≤ Finset.card (Finset.filter (fun c =>
      ¬IsAccessible G ne.f ne.small c) Finset.univ) from Finset.card_pos.mpr ⟨ne.large,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hacc⟩⟩)];
  rw [← h_sum, eq_comm];
  rw [← Finset.card_biUnion];
  · congr with v; aesop;
  · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz hz' => hxy <| by aesop;
lemma non_acc_verts_minus_one_card
    (G : SimpleGraph V)
    (r : ℕ) (s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (y₁ : V) (hy₁_nacc : ¬IsAccessible G ne.f ne.small (ne.f y₁)) :
    ((Finset.univ.filter (fun v : V => ¬IsAccessible G ne.f ne.small (ne.f v))).erase y₁).card =
    (Finset.univ.filter (fun c : Fin (r + 1) => ¬IsAccessible G ne.f ne.small c)).card * s := by
  classical
  rw [Finset.card_erase_of_mem];
  · convert Nat.sub_eq_of_eq_add <| non_acc_verts_card G r s hs ne hacc using 1;
  · aesop
omit [DecidableEq V] in
lemma non_acc_degree_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (s : ℕ) (_hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r)
    (ne : NearlyEquitable G (r + 1) s)
    (_hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (S : Finset V)
    (hS : S ⊆ Finset.univ.filter (fun v : V => ¬IsAccessible G ne.f ne.small (ne.f v)))
    (v : V) (hv : v ∈ S) :
    (S.filter (fun w => G.Adj v w)).card ≤
    (Finset.univ.filter (fun c : Fin (r + 1) => ¬IsAccessible G ne.f ne.small c)).card - 1 := by
  classical
  have hv_nonacc : ¬IsAccessible G ne.f ne.small (ne.f v) := by
    simpa using hS hv;
  have hv_acc_neighbors : Finset.card (Finset.filter (fun w =>
    IsAccessible G ne.f ne.small (ne.f w)) (G.neighborFinset v)) ≥ (Finset.univ.filter (fun c =>
      IsAccessible G ne.f ne.small c)).card := by
    have hv_acc_neighbors : Finset.card (Finset.image (fun w => ne.f w) (Finset.filter (fun w =>
      IsAccessible G ne.f ne.small (ne.f w)) (G.neighborFinset v))) ≥
        (Finset.univ.filter (fun c => IsAccessible G ne.f ne.small c)).card := by
      refine Finset.card_le_card ?_;
      intro c hc;
        have h_non_acc := non_acc_has_acc_neighbor G
          (show IsAccessible G ne.f ne.small c from by simpa using hc) hv_nonacc;
        aesop
    exact hv_acc_neighbors.trans (Finset.card_image_le);
  have hv_neighbors_S : Finset.card (Finset.filter (fun w => G.Adj v w) S) +
    Finset.card (Finset.filter (fun w =>
      IsAccessible G ne.f ne.small (ne.f w)) (G.neighborFinset v)) ≤ G.degree v := by
    rw [← Finset.card_union_of_disjoint];
    · exact Finset.card_le_card fun x hx => by aesop;
    · simp_all [Finset.disjoint_left];
      exact fun w hw hw' => Finset.mem_filter.mp (hS hw) |>.2;
  have hv_deg : G.degree v ≤ r := by
    exact le_trans (SimpleGraph.degree_le_maxDegree _ _) hd;
  have hv_card : Finset.card (Finset.univ.filter (fun c => IsAccessible G ne.f ne.small c)) +
    Finset.card (Finset.univ.filter (fun c => ¬IsAccessible G ne.f ne.small c)) = r + 1 := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_fin];
  exact le_tsub_of_add_le_left (by linarith)
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 80000 in
lemma B_minus_equitable
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (_hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (ih_primary : ∀ (W : Type*) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj] (r' : ℕ),
      Fintype.card W < Fintype.card V →
      H.maxDegree ≤ r' → (r' + 1) ∣ Fintype.card W →
      HasEquitableColoring H (r' + 1))
    (y₁ : V) (hy₁_nacc : ¬IsAccessible G ne.f ne.small (ne.f y₁)) :
    let B_minus : Set V := {v | ¬IsAccessible G ne.f ne.small (ne.f v) ∧ v ≠ y₁}
    let q := (Finset.univ.filter (fun c : Fin (r + 1) => ¬IsAccessible G ne.f ne.small c)).card
    HasEquitableColoring (G.induce B_minus) q := by
  revert ih_primary;
  intro ih
  set B_minus := {v : V | ¬IsAccessible G ne.f ne.small (ne.f v) ∧ v ≠ y₁}
  set q := (Finset.univ.filter (fun c => ¬IsAccessible G ne.f ne.small c)).card
  have hB_minus_card : Fintype.card B_minus = q * s := by
    convert non_acc_verts_minus_one_card G r s hs ne hacc y₁ hy₁_nacc using 1;
    rw [Fintype.card_of_subtype]; aesop
  have h_ind : HasEquitableColoring (G.induce B_minus) q := by
    have h_ind : (G.induce B_minus).maxDegree ≤ q - 1 := by
      have h_ind : ∀ v : B_minus, (G.induce B_minus).degree v ≤ q - 1 := by
        intro v
        have h_deg_le : (Finset.univ.filter (fun w => G.Adj v w ∧ w ∈ B_minus)).card ≤ q - 1
          := by
          have h_deg_le : (Finset.univ.filter (fun w => G.Adj v.val w ∧
            ¬IsAccessible G ne.f ne.small (ne.f w))).card ≤ q - 1 := by
            convert non_acc_degree_bound G r s hs hd ne hacc (Finset.univ.filter fun w =>
              ¬IsAccessible G ne.f ne.small (ne.f w)) _ v.val _ using 1;
            · exact congr_arg Finset.card (by ext; aesop);
            · exact fun x hx => hx;
            · aesop;
          exact le_trans (Finset.card_le_card fun x hx => by aesop) h_deg_le
        have hsub :
            ((G.induce B_minus).neighborFinset v).map (.subtype (· ∈ B_minus)) ⊆
              Finset.univ.filter (fun w : V => G.Adj v w ∧ w ∈ B_minus) := by
          intro w hw
          simpa [SimpleGraph.map_neighborFinset_induce, SimpleGraph.mem_neighborFinset] using hw
        calc
          (G.induce B_minus).degree v =
              (((G.induce B_minus).neighborFinset v).map (.subtype (· ∈ B_minus))).card := by
            rw [SimpleGraph.degree]
            exact (Finset.card_map (s := (G.induce B_minus).neighborFinset v)
              (.subtype (· ∈ B_minus))).symm
          _ ≤ (Finset.univ.filter (fun w : V => G.Adj v w ∧ w ∈ B_minus)).card :=
            Finset.card_le_card hsub
          _ ≤ q - 1 := h_deg_le
      exact SimpleGraph.maxDegree_le_of_forall_degree_le _ _ h_ind
    by_cases hq : q = 0;
    · simp_all [Finset.ext_iff];
      contrapose! hB_minus_card;
      simp +zetaDelta at *;
      grind;
    · have h_card_lt : Fintype.card B_minus < Fintype.card V := by
        rw [Fintype.card_subtype];
          exact Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨y₁, by aesop⟩);
      have h_dvd : q ∣ Fintype.card B_minus := by
        rw [hB_minus_card]
        exact dvd_mul_right q s
      let Hfin : SimpleGraph (Fin (Fintype.card B_minus)) :=
        (G.induce B_minus).overFin rfl
      let efin : G.induce B_minus ≃g Hfin :=
        (G.induce B_minus).overFinIso rfl
      have : DecidableRel Hfin.Adj := by
        dsimp [Hfin, SimpleGraph.overFin]
        infer_instance
      let W := ULift (Fin (Fintype.card B_minus))
      let H : SimpleGraph W :=
        Hfin.comap ((Equiv.ulift : W ≃ Fin (Fintype.card B_minus)).toEmbedding)
      let e : H ≃g Hfin :=
        SimpleGraph.Iso.comap
          (Equiv.ulift : W ≃ Fin (Fintype.card B_minus)) Hfin
      have : DecidableRel H.Adj := by
        dsimp [H]
        infer_instance
      have h_card_W : Fintype.card W = Fintype.card B_minus := by
        simp [W]
      have h_card_lt_lift : Fintype.card W < Fintype.card V := by
        rw [h_card_W]
        exact h_card_lt
      have h_ind_fin : Hfin.maxDegree ≤ q - 1 := by
        rwa [← efin.maxDegree_eq]
      have h_ind_lift : H.maxDegree ≤ q - 1 := by
        rwa [e.maxDegree_eq]
      have h_dvd_lift : q ∣ Fintype.card W := by
        rw [h_card_W]
        exact h_dvd
      have h_dvd_lift' : (q - 1 + 1) ∣ Fintype.card W := by
        simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hq)] using h_dvd_lift
      have h_col_H : HasEquitableColoring H q := by
        simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hq)]
          using ih W H (q - 1)
            h_card_lt_lift h_ind_lift h_dvd_lift'
      have h_col_Hfin : HasEquitableColoring Hfin q :=
        hasEquitableColoring_of_iso e h_col_H
      exact hasEquitableColoring_of_iso efin.symm h_col_Hfin
  exact h_ind
lemma auxadj_transfer_step
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (r : ℕ) (ne : NearlyEquitable G (r + 1) s)
    (W_col : Fin (r + 1)) (z y₁ : V) (X : Fin (r + 1))
    (hz_color : ne.f z = W_col)
    (hy₁_nacc : ¬IsAccessible G ne.f ne.small (ne.f y₁))
    (_hXW : X ≠ W_col)
    (A_plus : Set V)
    (hA_def : A_plus = {v | IsAccessible G ne.f ne.small (ne.f v) ∨ v = y₁})
    (g : V → Fin (r + 1))
    (hg_def : g = fun v => if v = z then X else if v = y₁ then W_col else ne.f v)
    (φ : {c : Fin (r + 1) // IsAccessible G ne.f ne.small c} ≃ Fin m1)
    (hg_acc : ∀ v : V, v ∈ A_plus → IsAccessible G ne.f ne.small (g v))
    (f_A : ↥A_plus → Fin m1)
    (hf_def : f_A = fun v => φ ⟨g v.val, hg_acc v.val v.prop⟩)
    (c d : Fin (r + 1))
    (hc_acc : IsAccessible G ne.f ne.small c)
    (hd_acc : IsAccessible G ne.f ne.small d)
    (hc_ne_W : c ≠ W_col)
    (hd_ne_W : d ≠ W_col)
    (hd_ne_X : d ≠ X)
    (hadj_cd : AuxAdj G ne.f c d) :
    AuxAdj (G.induce A_plus) f_A (φ ⟨c, hc_acc⟩) (φ ⟨d, hd_acc⟩) := by
  classical
  obtain ⟨v, hv, hv'⟩ := hadj_cd;
  refine ⟨⟨v, ?_⟩, ?_, ?_⟩ <;> simp_all;
  · grind;
  · grind
set_option maxHeartbeats 1600000 in
lemma A_plus_equitable
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (_hd : G.maxDegree ≤ r) (hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (W_col : Fin (r + 1)) (z y₁ : V)
    (hW_acc : IsAccessible G ne.f ne.small W_col)
    (hW_ne_small : W_col ≠ ne.small)
    (hW_ne_large : W_col ≠ ne.large)
    (hz_color : ne.f z = W_col)
    (hy₁_nacc : ¬IsAccessible G ne.f ne.small (ne.f y₁))
    (hadj_y₁_z : G.Adj y₁ z)
    (huniq_y₁ : ∀ (w : V), ne.f w = W_col → w ≠ z → ¬G.Adj y₁ w)
    (X : Fin (r + 1))
    (hXW : X ≠ W_col)
    (hXacc : IsAccessible G ne.f ne.small X)
    (hXmov : ∀ (w : V), ne.f w = X → ¬G.Adj z w)
    (hW_terminal : ∀ C : Fin (r + 1),
      IsAccessible G ne.f ne.small C → C ≠ W_col →
      Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W_col) C ne.small) :
    let A_plus : Set V := {v | IsAccessible G ne.f ne.small (ne.f v) ∨ v = y₁}
    let m1 := (Finset.univ.filter (fun c : Fin (r + 1) => IsAccessible G ne.f ne.small c)).card
    HasEquitableColoring (G.induce A_plus) m1 := by
  intro A_plus m1
  have hz_ne_y₁ : z ≠ y₁ := by
    intro h; subst h; exact hy₁_nacc (hz_color ▸ hW_acc)
  have hy₁_ne_z : y₁ ≠ z := fun h => hz_ne_y₁ h.symm
  have hy₁_ne_W : ne.f y₁ ≠ W_col := by
    intro h; exact hy₁_nacc (h ▸ hW_acc)
  set accType := {c : Fin (r + 1) // IsAccessible G ne.f ne.small c}
  have hm1_eq : Fintype.card accType = m1 := by
    simp [m1, accType, Fintype.card_subtype]
  set φ : accType ≃ Fin m1 := (Fintype.equivFin accType).trans (finCongr hm1_eq)
  set g : V → Fin (r + 1) := fun v =>
    if v = z then X else if v = y₁ then W_col else ne.f v
  have hg_acc : ∀ v : V, v ∈ A_plus → IsAccessible G ne.f ne.small (g v) := by
    intro v hv; simp only [g]
    split_ifs with h1 h2
    · exact hXacc
    · exact hW_acc
    · exact hv.resolve_right h2
  set f_A : ↥A_plus → Fin m1 := fun v => φ ⟨g v.val, hg_acc v.val v.prop⟩
  have hX_ne_fy₁ : X ≠ ne.f y₁ := by
    intro h; exact hy₁_nacc (h ▸ hXacc)
  have hproper : IsProper (G.induce A_plus) f_A := by
    intro u v huv h_eq
    have hg_eq : g u.val = g v.val := by
      simpa [f_A] using congr_arg Subtype.val (φ.injective h_eq)
    by_cases huz : u.val = z
    · by_cases hvz : v.val = z
      · exact huv.ne (Subtype.ext (by simp [huz, hvz]))
      · by_cases hvy : v.val = y₁
        · have hXW' : X = W_col := by
            simpa [g, huz, hvz, hvy, hy₁_ne_z] using hg_eq
          exact hXW hXW'
        · have hv_color : ne.f v.val = X := by
            simpa [g, huz, hvz, hvy] using hg_eq.symm
          exact hXmov v.val hv_color (by simpa [huz] using huv)
    · by_cases hvz : v.val = z
      · by_cases huy : u.val = y₁
        · have hXW' : W_col = X := by
            simpa [g, huz, hvz, huy, hy₁_ne_z] using hg_eq
          exact hXW hXW'.symm
        · have hu_color : ne.f u.val = X := by
            simpa [g, huz, hvz, huy] using hg_eq
          exact hXmov u.val hu_color (by simpa [hvz] using huv.symm)
      · by_cases huy : u.val = y₁
        · by_cases hvy : v.val = y₁
          · exact huv.ne (Subtype.ext (by simp [huy, hvy]))
          · have hv_color : ne.f v.val = W_col := by
              simpa [g, huz, hvz, huy, hvy, hy₁_ne_z] using hg_eq.symm
            exact huniq_y₁ v.val hv_color hvz (by simpa [huy] using huv)
        · by_cases hvy : v.val = y₁
          · have hu_color : ne.f u.val = W_col := by
              simpa [g, huz, hvz, huy, hvy, hy₁_ne_z] using hg_eq
            exact huniq_y₁ u.val hu_color huz (by simpa [hvy] using huv.symm)
          · have h_ne_f_eq : ne.f u.val = ne.f v.val := by
              simpa [g, huz, hvz, huy, hvy] using hg_eq
            exact ne.proper u.val v.val huv h_ne_f_eq
  by_cases hX_eq : X = ne.small
  ·
    refine ⟨f_A, hproper, ?_⟩
    intro c₁ c₂
    have h_class_size : ∀ c : { c : Fin (r + 1) // IsAccessible G ne.f ne.small c },
      #(cClass f_A (φ c)) = s := by
      intro c
      have h_card : #(cClass f_A (φ c)) = #(cClass g (c.val)) := by
        refine Finset.card_bij (fun x hx => x.val) ?_ ?_ ?_ <;> simp [cClass];
        · aesop;
        · grind;
      by_cases hc : c.val = ne.small <;> by_cases hc' : c.val = W_col <;>
        simp_all [cClass];
      · have h_card : #(cClass ne.f ne.small) = s - 1 := by
          exact ne.card_small;
        rw [show (Finset.filter (fun v => g v = ne.small) Finset.univ : Finset V) =
          Finset.filter (fun v => ne.f v = ne.small) Finset.univ ∪ { z } from ?_,
            Finset.card_union] <;> simp_all;
        · exact h_card.symm ▸ Nat.succ_pred_eq_of_pos hs0;
        · ext v; by_cases hv : v = z <;> by_cases hv' : v = y₁ <;> simp [hv, hv'];
          · grind +revert;
          · grind +ring;
          · grind;
          · grind +ring;
      · rw [show (Finset.filter (fun v => g v = W_col) Finset.univ) =
        { y₁ } ∪ (Finset.filter (fun v => ne.f v = W_col) Finset.univ \ { z }) from ?_,
          Finset.card_union] <;> simp [*, Finset.card_sdiff];
        · rw [add_tsub_cancel_of_le];
          · exact ne.card_other _ (by aesop) (by aesop);
          · exact Finset.card_pos.mpr ⟨z, by aesop⟩;
        · grind (splits := 20);
      · convert ne.card_other c.val hc (show c.val ≠ ne.large from ?_) using 1;
        · congr with v; aesop;
        · exact fun h => hacc <| h ▸ c.2;
    rw [show cClass f_A c₁ = cClass f_A (φ (φ.symm c₁)) by simp,
      show cClass f_A c₂ = cClass f_A (φ (φ.symm c₂)) by simp, h_class_size,
        h_class_size]; linarith
  ·
    have hne_small_acc : IsAccessible G ne.f ne.small ne.small := Relation.ReflTransGen.refl
    set small_idx := φ ⟨ne.small, hne_small_acc⟩
    set large_idx := φ ⟨X, hXacc⟩
    have hne_sl : small_idx ≠ large_idx := by
      intro h
      exact hX_eq (Subtype.ext_iff.mp (φ.injective h)).symm
    have card_small : (cClass f_A small_idx).card = s - 1 := by
      rw [← ne.card_small]
      refine Finset.card_bij (fun v _hv => (v : V)) ?_ ?_ ?_
      · intro v hv
        have hfv : f_A v = small_idx := (mem_cClass f_A small_idx v).mp hv
        have hg_small : g (v : V) = ne.small := by
          exact Subtype.ext_iff.mp (φ.injective hfv)
        have hv_ne_z : (v : V) ≠ z := by
          intro hvz
          exact hX_eq (by simpa [g, hvz] using hg_small)
        have hv_ne_y₁ : (v : V) ≠ y₁ := by
          intro hvy₁
          exact hW_ne_small (by simpa [g, hv_ne_z, hvy₁, hy₁_ne_z] using hg_small)
        exact (mem_cClass ne.f ne.small (v : V)).mpr
          (by simpa [g, hv_ne_z, hv_ne_y₁] using hg_small)
      · intro x _ y _ hxy
        exact Subtype.ext hxy
      · intro y hy
        have hy_color : ne.f y = ne.small := (mem_cClass ne.f ne.small y).mp hy
        have hy_mem : y ∈ A_plus := Or.inl (by simpa [hy_color] using hne_small_acc)
        refine ⟨⟨y, hy_mem⟩, ?_, rfl⟩
        have hy_ne_z : y ≠ z := by
          intro hyz
          have hz_small : ne.f z = ne.small := by simpa [hyz] using hy_color
          exact hW_ne_small (hz_color.symm.trans hz_small)
        have hy_ne_y₁ : y ≠ y₁ := by
          intro hyy₁
          exact hy₁_nacc (by simpa [← hyy₁, hy_color] using hne_small_acc)
        exact (mem_cClass f_A small_idx ⟨y, hy_mem⟩).mpr
          (by simp [f_A, small_idx, g, hy_ne_z, hy_ne_y₁, hy_color])
    have card_large : (cClass f_A large_idx).card = s + 1 := by
      have card_large : (cClass f_A large_idx).card = 1 + (Finset.univ.filter (fun v => ne.f v =
        X ∧ v ∈ A_plus)).card := by
        have card_large : (cClass f_A large_idx).card = (Finset.filter (fun v => v.val =
          z) (Finset.univ : Finset ↑A_plus)).card + (Finset.filter (fun v => v.val ≠ z ∧
            g v.val = X) (Finset.univ : Finset ↑A_plus)).card := by
          rw [← Finset.card_union_of_disjoint];
          · refine congr_arg Finset.card (Finset.ext fun x => ?_);
            simp [cClass, f_A, large_idx];
            grind;
          · exact Finset.disjoint_filter.mpr (by aesop);
        convert card_large using 2;
        · rw [Finset.card_eq_one.mpr];
          use ⟨z, by
            exact Or.inl (by simpa [hz_color] using hW_acc)⟩
          generalize_proofs at *;
          grind +revert;
        · rw [← Finset.card_image_of_injective _ Subtype.coe_injective]; congr; ext
          simp [g];
          grind +ring;
      have hX_ne_large : X ≠ ne.large := by
        intro h
        exact hacc (h ▸ hXacc)
      have h_filter_eq : (Finset.univ.filter fun v => ne.f v = X ∧ v ∈ A_plus) =
          Finset.univ.filter fun v => ne.f v = X := by
        ext v
        simp [A_plus]
        intro hvX
        exact Or.inl (hvX ▸ hXacc)
      rw [card_large, h_filter_eq]
      change 1 + (cClass ne.f X).card = s + 1
      rw [ne.card_other X (by tauto) hX_ne_large]
      omega
    have card_other : ∀ c, c ≠ small_idx → c ≠ large_idx → (cClass f_A c).card = s := by
      intro c hc_ne_small hc_ne_large
      obtain ⟨a, ha⟩ : ∃ a : accType, φ a = c := by
        exact φ.surjective c;
      by_cases haW : a.val = W_col;
      · have h_fA_W : (cClass f_A c).card = (Finset.univ.filter (fun v => ne.f v = W_col ∧
        v ≠ z ∧ v ≠ y₁)).card + 1 := by
          have h_card_fA_W : (cClass f_A c).card = (Finset.univ.filter (fun v : A_plus => g v =
            W_col)).card := by
            refine Finset.card_bij (fun v hv => v) ?_ ?_ ?_ <;> simp;
            · intro v hv hv'; have := φ.injective (hv'.trans ha.symm); aesop;
            · grind;
          rw [h_card_fA_W, show (Finset.filter (fun v : A_plus => g v = W_col) Finset.univ) =
            Finset.filter (fun v : A_plus => ne.f v = W_col ∧ v ≠ z ∧
              v ≠ y₁) Finset.univ ∪ { ⟨y₁, Or.inr rfl⟩ } from ?_,
                Finset.card_union] <;> simp [*, Finset.filter_ne', Finset.filter_and];
          · rw [← Finset.card_image_of_injective _ Subtype.coe_injective]; congr; ext;
            simp [*];
            exact fun _ _ _ => Or.inl <| by aesop;
          · ext ⟨v, hv⟩; simp [g];
            grind +ring;
        have h_without_z : (Finset.univ.filter (fun v => ne.f v = W_col ∧ v ≠ z ∧
          v ≠ y₁)).card = (Finset.univ.filter (fun v => ne.f v = W_col)).card - 1 := by
          rw [show (Finset.filter (fun v => ne.f v = W_col ∧ v ≠ z ∧
            v ≠ y₁) Finset.univ) = Finset.filter (fun v => ne.f v =
              W_col) Finset.univ \ { z } from ?_, Finset.card_sdiff] <;> simp [*];
          · ext v
            by_cases hvz : v = z <;> by_cases hvy : v = y₁ <;>
              simp [hvz, hvy, hz_color, hy₁_ne_W]
        have hW_card : (Finset.univ.filter (fun v => ne.f v = W_col)).card = s := by
          simpa [cClass] using ne.card_other W_col hW_ne_small hW_ne_large
        rw [h_fA_W, h_without_z, hW_card]
        omega
      · convert ne.card_other a.val _ _ using 1;
        · refine Finset.card_bij (fun v hv => v.val) ?_ ?_ ?_ <;> simp [cClass];
          · intro v hv hv'; replace hv' := congr_arg φ.symm hv'; aesop;
          · grind;
        · grind;
        · exact fun h => hacc <| h ▸ a.2
    have card_total : Fintype.card ↥A_plus = m1 * s := by
      have hA_plus_card : (Finset.univ.filter (fun v =>
        IsAccessible G ne.f ne.small (ne.f v))).card = m1 * s - 1 := by
        have hA_plus_card : (Finset.univ.filter (fun v =>
          IsAccessible G ne.f ne.small (ne.f v))).card = (Finset.univ.filter (fun c =>
            IsAccessible G ne.f ne.small c)).card * s - 1 := by
          have := non_acc_verts_card G r s hs ne hacc
          simp_all [Finset.filter_not, Finset.card_sdiff];
          exact eq_tsub_of_add_eq (by nlinarith only [this, Nat.sub_add_cancel (show (r + 1) *
            s ≥ Finset.card (Finset.filter (fun v =>
              IsAccessible G ne.f ne.small (ne.f v)) Finset.univ) from Finset.card_le_univ _ |>
                le_trans <| by simp [hs]), Nat.sub_add_cancel (show (r + 1) ≥
                  Finset.card (Finset.filter (fun c =>
                    IsAccessible G ne.f ne.small c) Finset.univ) from Finset.card_le_univ _ |>
                      le_trans <| by simp)]);
        simpa [m1] using hA_plus_card
      rw [Fintype.card_subtype];
      rw [show (Finset.filter (Membership.mem A_plus) Finset.univ : Finset V) =
        Finset.filter (fun v =>
          IsAccessible G ne.f ne.small (ne.f v)) Finset.univ ∪ { y₁ } from ?_,
            Finset.card_union] <;> simp [*];
      · have hm1_pos : 0 < m1 := by
          dsimp [m1]
          exact Finset.card_pos.mpr ⟨ne.small,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.ReflTransGen.refl⟩⟩
        rw [Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.mul_pos hm1_pos hs0))]
      · ext v; simp [A_plus];
        grind
    set ne_A : NearlyEquitable (G.induce A_plus) m1 s :=
      ⟨f_A, hproper, small_idx, large_idx, hne_sl, card_small, card_large, card_other,
        card_total⟩
    have h_transfer : ∀ c : Fin (r + 1),
        (hc_acc : IsAccessible G ne.f ne.small c) →
        c ≠ W_col →
        Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W_col ∧
          d ≠ X) c ne.small →
        Relation.ReflTransGen (AuxAdj (G.induce A_plus) f_A) (φ ⟨c, hc_acc⟩) small_idx := by
      have h_step :
          ∀ (c d : Fin (r + 1))
            (hc_acc : IsAccessible G ne.f ne.small c)
            (hd_acc : IsAccessible G ne.f ne.small d)
            (hc_ne_W : c ≠ W_col) (hd_ne_W : d ≠ W_col)
            (hd_ne_X : d ≠ X) (hadj_cd : AuxAdj G ne.f c d),
            AuxAdj (induce A_plus G) f_A (φ ⟨c, hc_acc⟩) (φ ⟨d, hd_acc⟩) := by
        intros c d hc_acc hd_acc hc_ne_W hd_ne_W hd_ne_X hadj_cd
        apply
          auxadj_transfer_step G r ne W_col z y₁ X hz_color hy₁_nacc hXW A_plus rfl
            g rfl φ hg_acc f_A rfl c d hc_acc hd_acc hc_ne_W hd_ne_W hd_ne_X
            hadj_cd
      have h_ind :
          ∀ (c d : Fin (r + 1))
            (hc_acc : IsAccessible G ne.f ne.small c)
            (hd_acc : IsAccessible G ne.f ne.small d)
            (hc_ne_W : c ≠ W_col) (hd_ne_W : d ≠ W_col),
            Relation.ReflTransGen
              (fun c d => AuxAdj G ne.f c d ∧ c ≠ W_col ∧ d ≠ X) c d →
              Relation.ReflTransGen (AuxAdj (induce A_plus G) f_A)
                (φ ⟨c, hc_acc⟩) (φ ⟨d, hd_acc⟩) := by
        intros c d hc_acc hd_acc hc_ne_W hd_ne_W hc_chain
        induction hc_chain with
        | refl =>
          all_goals generalize_proofs at *;
          exact Relation.ReflTransGen.refl;
        | @tail mid d hprev hd ih =>
          all_goals generalize_proofs at *;
          have hmid_acc : IsAccessible G ne.f ne.small mid := by
            exact Relation.ReflTransGen.head hd.1 hd_acc
          apply Relation.ReflTransGen.trans
          · exact ih hmid_acc hd.2.1
          · exact Relation.ReflTransGen.single
              (h_step mid d hmid_acc hd_acc hd.2.1 hd_ne_W hd.2.2 hd.1)
      intro c hc_acc hc_ne_W hchain
      simpa [small_idx] using
        h_ind c ne.small hc_acc hne_small_acc hc_ne_W (Ne.symm hW_ne_small) hchain
    have hacc_X : IsAccessible (G.induce A_plus) f_A small_idx large_idx := by
      have hchain_orig := hW_terminal X hXacc hXW
      obtain ⟨l, hnodup, hchain, hhead, hlast, hlen⟩ :=
        exists_nodup_chain hchain_orig hX_eq
      contrapose! h_transfer;
      refine ⟨X, hXacc, hXW, ?_, ?_⟩;
      · refine hchain_orig.recOn ?_ ?_;
        · rfl;
        · grind;
      · exact Not.imp h_transfer fun a => a
    exact accessible_large_gives_equitable (G.induce A_plus) m1 s ne_A hacc_X
omit [DecidableEq V] in
set_option maxHeartbeats 1600000 in
lemma non_accessible_case1
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (ih_primary : ∀ (W : Type*) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj] (r' : ℕ),
      Fintype.card W < Fintype.card V →
      H.maxDegree ≤ r' → (r' + 1) ∣ Fintype.card W →
      HasEquitableColoring H (r' + 1))
    (_q_val : ℕ)
    (W : Fin (r + 1)) (z y₁ : V)
    (hW_acc : IsAccessible G ne.f ne.small W)
    (hW_ne_small : W ≠ ne.small)
    (hW_ne_large : W ≠ ne.large)
    (hz_color : ne.f z = W)
    (hy₁_nacc : ¬IsAccessible G ne.f ne.small (ne.f y₁))
    (hadj_y₁_z : G.Adj y₁ z)
    (huniq_y₁ : ∀ (w : V), ne.f w = W → w ≠ z → ¬G.Adj y₁ w)
    (X : Fin (r + 1))
    (hXW : X ≠ W)
    (hXacc : IsAccessible G ne.f ne.small X)
    (hXmov : ∀ (w : V), ne.f w = X → ¬G.Adj z w)
    (hW_terminal : ∀ C : Fin (r + 1),
      IsAccessible G ne.f ne.small C → C ≠ W →
      Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W) C ne.small) :
    HasEquitableColoring G (r + 1) := by
  classical
  set A_plus := {v : V | IsAccessible G ne.f ne.small (ne.f v) ∨ v = y₁}
  set B_minus := {v : V | ¬IsAccessible G ne.f ne.small (ne.f v) ∧ v ≠ y₁};
  have hA_plus_card : Fintype.card A_plus = (Finset.univ.filter (fun c : Fin (r + 1) =>
    IsAccessible G ne.f ne.small c)).card * s := by
    have hA_plus_card : Fintype.card A_plus = Fintype.card V - Fintype.card B_minus := by
      rw [Fintype.card_subtype, Fintype.card_subtype];
      rw [tsub_eq_of_eq_add_rev];
      rw [Fintype.card_eq_sum_ones, Finset.card_filter, Finset.card_filter];
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl]; aesop;
    have hB_minus_card' : Fintype.card B_minus =
        (Finset.univ.filter (fun c : Fin (r + 1) =>
          ¬IsAccessible G ne.f ne.small c)).card * s := by
      convert non_acc_verts_minus_one_card G r s hs ne hacc y₁ hy₁_nacc using 1;
      rw [Fintype.card_of_subtype]; aesop;
    have h_card_sum' :
        (Finset.univ.filter (fun c : Fin (r + 1) =>
          IsAccessible G ne.f ne.small c)).card +
        (Finset.univ.filter (fun c : Fin (r + 1) =>
          ¬IsAccessible G ne.f ne.small c)).card = r + 1 := by
      rw [Finset.card_filter_add_card_filter_not, Finset.card_fin];
    have hmul :
        (r + 1) * s =
          (Finset.univ.filter (fun c : Fin (r + 1) =>
            IsAccessible G ne.f ne.small c)).card * s +
          (Finset.univ.filter (fun c : Fin (r + 1) =>
            ¬IsAccessible G ne.f ne.small c)).card * s := by
      calc
        (r + 1) * s =
            ((Finset.univ.filter (fun c : Fin (r + 1) =>
              IsAccessible G ne.f ne.small c)).card +
            (Finset.univ.filter (fun c : Fin (r + 1) =>
              ¬IsAccessible G ne.f ne.small c)).card) * s := by
          exact (congr_arg (fun n => n * s) h_card_sum').symm
        _ =
            (Finset.univ.filter (fun c : Fin (r + 1) =>
              IsAccessible G ne.f ne.small c)).card * s +
            (Finset.univ.filter (fun c : Fin (r + 1) =>
              ¬IsAccessible G ne.f ne.small c)).card * s := by
          rw [Nat.add_mul]
    rw [hA_plus_card, hs, hB_minus_card', hmul, Nat.add_sub_cancel_right]
  have hB_minus_card : Fintype.card B_minus = (Finset.univ.filter (fun c : Fin (r + 1) =>
    ¬IsAccessible G ne.f ne.small c)).card * s := by
    convert non_acc_verts_minus_one_card G r s hs ne hacc y₁ hy₁_nacc using 1;
    rw [Fintype.card_of_subtype]; aesop;
  have hA_plus_equitable :
    HasEquitableColoring (G.induce A_plus) (Finset.card (Finset.univ.filter (fun c : Fin (r + 1) =>
      IsAccessible G ne.f ne.small c))) := by
    apply_rules [A_plus_equitable]
  have hB_minus_equitable :
    HasEquitableColoring (G.induce B_minus) (Finset.card (Finset.univ.filter (fun c : Fin (r + 1) =>
      ¬IsAccessible G ne.f ne.small c))) := by
    apply B_minus_equitable G r s hs hd hs0 ne hacc ih_primary y₁ hy₁_nacc;
  have h_card_sum : (Finset.card (Finset.univ.filter (fun c : Fin (r + 1) =>
    IsAccessible G ne.f ne.small c))) + (Finset.card (Finset.univ.filter (fun c : Fin (r + 1) =>
      ¬IsAccessible G ne.f ne.small c))) = r + 1 := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_fin];
  have := @combine_disjoint_equitable V _ G;
  specialize this A_plus (Finset.card (Finset.univ.filter (fun c : Fin (r + 1) =>
    IsAccessible G ne.f ne.small c))) (Finset.card (Finset.univ.filter (fun c : Fin (r + 1) =>
      ¬IsAccessible G ne.f ne.small c))) s hA_plus_card ?_;
  · have h_compl_eq : (A_plusᶜ : Set V) = B_minus := by
      ext v
      simp [A_plus, B_minus, not_or]
    simpa [h_compl_eq] using hB_minus_card
  · obtain ⟨fA, hfA_proper, hfA_equitable⟩ := hA_plus_equitable
    obtain ⟨fB, hfB_proper, hfB_equitable⟩ := hB_minus_equitable
    let eB : ↥(A_plusᶜ : Set V) ≃ B_minus :=
      { toFun := fun v => ⟨v, by
          have hv : ¬((v : V) ∈ A_plus) := v.2
          change ¬(IsAccessible G ne.f ne.small (ne.f (v : V)) ∨ (v : V) = y₁) at hv
          exact not_or.mp hv⟩
        invFun := fun v => ⟨v, by
          have hv : (v : V) ∈ B_minus := v.2
          change ¬IsAccessible G ne.f ne.small (ne.f (v : V)) ∧ (v : V) ≠ y₁ at hv
          exact fun h => hv.1 (h.resolve_right hv.2)⟩
        left_inv := by
          intro v
          ext
          rfl
        right_inv := by
          intro v
          ext
          rfl }
    specialize this fA (fun v => fB (eB v)) hfA_proper (by
      intro v w hvw
      exact hfB_proper (eB v) (eB w) hvw) hfA_equitable (by
      intro c₁ c₂
      have hcard :
          ∀ c, (cClass (fun v : ↥(A_plusᶜ : Set V) => fB (eB v)) c).card =
            (cClass fB c).card := by
        intro c
        refine Finset.card_bij (fun x _ => eB x) ?_ ?_ ?_
        · intro x hx
          simpa [cClass] using hx
        · intro x₁ _ x₂ _ h
          exact eB.injective h
        · intro y hy
          refine ⟨eB.symm y, ?_, by simp⟩
          simpa [cClass] using hy
      rw [hcard c₁, hcard c₂]
      exact hfB_equitable c₁ c₂);
    simpa [h_card_sum] using this
lemma transGen_exists_ne_first_step {α : Type*} {r : α → α → Prop} {a b : α}
    (h : Relation.TransGen r a b) (hne : a ≠ b) :
    ∃ c, c ≠ a ∧ r a c ∧ Relation.ReflTransGen r c b := by
  induction h with
  | single h =>
    rename_i final
    exact ⟨final, Ne.symm hne, h, by rfl⟩;
  | @tail mid final hprev hstep ih =>
    by_cases hac : a = mid <;> simp_all;
    · exact ⟨final, Ne.symm hne, hstep, by rfl⟩;
    · obtain ⟨d, hd₁, hd₂, hd₃⟩ := ih
      exact ⟨d, hd₁, hd₂, hd₃.tail hstep⟩;
omit [DecidableEq V] in
set_option maxHeartbeats 6400000 in
lemma non_accessible_case2_paper
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (hacc : ¬IsAccessible G ne.f ne.small ne.large)
    (ih_primary : ∀ (W : Type*) [Fintype W] [DecidableEq W]
        (H : SimpleGraph W) [DecidableRel H.Adj] (r' : ℕ),
        Fintype.card W < Fintype.card V →
        H.maxDegree ≤ r' → (r' + 1) ∣ Fintype.card W →
        HasEquitableColoring H (r' + 1))
    (q_val : ℕ)
    (ih : ∀ (ne' : NearlyEquitable G (r + 1) s),
      (Finset.univ.filter (fun c : Fin (r + 1) =>
        ¬IsAccessible G ne'.f ne'.small c)).card ≤ q_val →
      HasEquitableColoring G (r + 1))
    (hq' : (Finset.univ.filter (fun c : Fin (r + 1) =>
        ¬IsAccessible G ne.f ne.small c)).card ≤ q_val + 1)
    (W : Fin (r + 1)) (z y₁ y₂ : V)
    (hW_acc : IsAccessible G ne.f ne.small W)
    (hW_ne_small : W ≠ ne.small)
    (hW_ne_large : W ≠ ne.large)
    (hz_color : ne.f z = W)
    (hy₁_nacc : ¬IsAccessible G ne.f ne.small (ne.f y₁))
    (hadj_y₁_z : G.Adj y₁ z)
    (huniq_y₁ : ∀ (w : V), ne.f w = W → w ≠ z → ¬G.Adj y₁ w)
    (hy₂ne : y₂ ≠ y₁)
    (hy₂nacc : ¬IsAccessible G ne.f ne.small (ne.f y₂))
    (hy₂adj : G.Adj y₂ z)
    (hy₂uniq : ∀ (w : V), ne.f w = W → w ≠ z → ¬G.Adj y₂ w)
    (hnonadj : ¬G.Adj y₁ y₂)
    (hnotmov : ∀ (X : Fin (r + 1)),
      IsAccessible G ne.f ne.small X → X ≠ W → ∃ w, ne.f w = X ∧ G.Adj z w)
    (hW_terminal : ∀ C : Fin (r + 1),
      IsAccessible G ne.f ne.small C → C ≠ W →
      Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W) C ne.small) :
    HasEquitableColoring G (r + 1) := by
  classical
  set nacc_colors := Finset.univ.filter (fun c : Fin (r + 1) => ¬IsAccessible G ne.f ne.small c)
    with nacc_colors_def
  set q_nacc := nacc_colors.card with hq_nacc_def
  set B_minus_set : Set V := {v | ¬IsAccessible G ne.f ne.small (ne.f v) ∧
    v ≠ y₁} with hBms_def
  let B_minus := Finset.univ.filter (fun v : V => ¬IsAccessible G ne.f ne.small (ne.f v) ∧
    v ≠ y₁)
  obtain ⟨g, hg_proper, hg_equitable⟩ : HasEquitableColoring (G.induce B_minus_set) q_nacc :=
    B_minus_equitable G r s hs hd hs0 ne hacc ih_primary y₁ hy₁_nacc
  have hsmall_acc : IsAccessible G ne.f ne.small ne.small := Relation.ReflTransGen.refl
  have hnacc_pos : 0 < q_nacc := by
    exact Finset.card_pos.mpr ⟨ne.large, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hacc⟩⟩
  have hB_card : Fintype.card ↥B_minus_set = q_nacc * s := by
    convert non_acc_verts_minus_one_card G r s hs ne hacc y₁ hy₁_nacc using 1
    rw [Fintype.card_of_subtype]; aesop
  have hg_class_size : ∀ c : Fin q_nacc, (cClass g c).card = s :=
    equitable_all_same_size hg_equitable hB_card
  have hz_not_in_B : z ∉ B_minus_set := by
    simp only [B_minus_set, Set.mem_ofPred_eq, not_and]
    intro hnacc; exact absurd (hz_color ▸ hW_acc) hnacc
  have hy₂_in_B : y₂ ∈ B_minus_set := by
    simp [B_minus_set]; exact ⟨hy₂nacc, hy₂ne⟩
  have hz_B_deg : (B_minus.filter (fun w => G.Adj z w)).card ≤ q_nacc - 1 := by
    have hzacc_adj : Finset.card (Finset.filter (fun w => G.Adj z w) (Finset.univ.filter (fun w =>
      IsAccessible G ne.f ne.small (ne.f w)))) ≥ Finset.card (Finset.filter (fun c =>
        IsAccessible G ne.f ne.small c) Finset.univ) - 1 := by
      have hzacc_adj : Finset.card (Finset.image ne.f (Finset.filter (fun w =>
        G.Adj z w) (Finset.univ.filter (fun w => IsAccessible G ne.f ne.small (ne.f w))))) ≥
          Finset.card (Finset.filter (fun c => IsAccessible G ne.f ne.small c) Finset.univ) - 1
            := by
        have hzacc_adj : Finset.image ne.f (Finset.filter (fun w =>
          G.Adj z w) (Finset.univ.filter (fun w =>
            IsAccessible G ne.f ne.small (ne.f w)))) ⊇ Finset.filter (fun c =>
              IsAccessible G ne.f ne.small c) Finset.univ \ {W} := by
          grind (splits := 20);
        exact le_trans (by rw [Finset.card_sdiff]; aesop) (Finset.card_mono hzacc_adj);
      exact hzacc_adj.trans (Finset.card_image_le);
    have hzacc_adj : Finset.card (Finset.filter (fun w => G.Adj z w) (Finset.univ.filter (fun w =>
      IsAccessible G ne.f ne.small (ne.f w)))) + Finset.card (Finset.filter (fun w =>
        G.Adj z w) (Finset.univ.filter (fun w => ¬IsAccessible G ne.f ne.small (ne.f w)))) ≤ r
          := by
      rw [← Finset.card_union_of_disjoint];
      · have hzacc_adj : Finset.card (Finset.filter (fun w => G.Adj z w) Finset.univ) ≤ r := by
          simpa [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
            using (SimpleGraph.degree_le_maxDegree G z).trans hd
        convert hzacc_adj using 2; ext w;
          by_cases hw : IsAccessible G ne.f ne.small (ne.f w) <;> simp [hw];
      · exact Finset.disjoint_left.mpr (by aesop);
    have hzacc_adj : Finset.card (Finset.filter (fun c =>
      IsAccessible G ne.f ne.small c) Finset.univ) + Finset.card (Finset.filter (fun c =>
        ¬IsAccessible G ne.f ne.small c) Finset.univ) = r + 1 := by
      rw [Finset.card_filter_add_card_filter_not, Finset.card_fin];
    have hzacc_adj : Finset.card (Finset.filter (fun w => G.Adj z w) (Finset.univ.filter (fun w =>
      ¬IsAccessible G ne.f ne.small (ne.f w)))) ≥ Finset.card (Finset.filter (fun w =>
        G.Adj z w) (Finset.univ.filter (fun w => ¬IsAccessible G ne.f ne.small (ne.f w) ∧
          w ≠ y₁))) + 1 := by
      refine Finset.card_lt_card ?_;
      simp [Finset.ssubset_def, Finset.subset_iff];
      exact ⟨fun x hx₁ hx₂ hx₃ => ⟨hx₁, hx₃⟩, y₁, hy₁_nacc, hadj_y₁_z.symm,
        by tauto⟩;
    grind
  have ⟨Y, hY_no_z_nbr⟩ : ∃ Y : Fin q_nacc,
      ∀ w : ↥B_minus_set, g w = Y → ¬G.Adj z w.val := by
    contrapose! hz_B_deg;
    choose f hf using hz_B_deg;
    refine lt_of_lt_of_le ?_
      (Finset.card_le_card (s := Finset.image (fun Y => (f Y : V)) Finset.univ) ?_);
    · rw [Finset.card_image_of_injective _ fun x y hxy => _] <;>
      simp_all [Fin.ext_iff];
      grind;
    · simp [Finset.subset_iff, hf];
      exact fun Y => Finset.mem_filter.mpr ⟨Finset.mem_univ _, f Y |>.2⟩
  let φ_equiv := nacc_colors.equivFin
  let φ : Fin q_nacc → Fin (r + 1) := fun i => (φ_equiv.symm i).val
  have hφ_inj : Function.Injective φ := by
    intro a b hab
    exact φ_equiv.symm.injective (Subtype.val_injective hab)
  have hφ_nacc : ∀ i, ¬IsAccessible G ne.f ne.small (φ i) := by
    intro i; exact (Finset.mem_filter.mp (φ_equiv.symm i).prop).2
  have hφ_ne_W : ∀ i, φ i ≠ W := fun i h => hφ_nacc i (h ▸ hW_acc)
  let f' : V → Fin (r + 1) := fun v =>
    if v = y₁ then W
    else if hv : v ∈ B_minus_set then φ (g ⟨v, hv⟩)
    else if v = z then φ Y
    else ne.f v
  have hf'_proper_paper : IsProper G f' := by
    intro u v huv;
    by_cases hu : u = y₁ <;> by_cases hv : v = y₁ <;> simp [hu, hv] at huv ⊢;
    · grind;
    · simp +zetaDelta at *;
      split_ifs <;> simp_all;
      (expose_names; exact Ne.intro fun a => huniq_y₁ u a h_1 (id (adj_symm G huv)));
    · by_cases huB : u ∈ B_minus_set <;> by_cases hvB : v ∈ B_minus_set <;> simp [huB,
      hvB, f'] at huv ⊢;
      · have := hg_proper ⟨u, huB⟩ ⟨v, hvB⟩; simp_all [IsProper];
        exact hφ_inj.ne this;
      · split_ifs <;> simp_all [IsProper];
        · intro h; have := hφ_inj h; simp_all;
          exact hY_no_z_nbr u huB.1 huB.2 this huv.symm;
        · grind;
      · split_ifs <;> simp_all [IsProper];
        · exact hφ_inj.ne (by specialize hY_no_z_nbr v hvB.1 hvB.2; aesop);
        · exact fun h => hφ_nacc _ (h ▸ huB);
      · by_cases huZ : u = z <;> by_cases hvZ : v = z <;> simp [hu, hv, huZ,
        hvZ] at huB hvB ⊢;
        · exact huv.ne (huZ.trans hvZ.symm);
        · grind +revert;
        · split_ifs <;> simp_all [SimpleGraph.adj_comm];
          exact fun h => hφ_nacc Y <| h ▸ huB;
        · exact ne.proper u v huv
  have hf'_proper := hf'_proper_paper
  have hf'_small : (cClass f' ne.small).card = s - 1 := by
    have h_card_small_f'_eq : (cClass f' ne.small) = (cClass ne.f ne.small) \ {y₁} := by
      ext v; simp [f', cClass];
      grind +revert;
    have := ne.card_small; simp_all [Finset.card_sdiff];
    by_cases hy₁ : ne.f y₁ = ne.small <;> simp_all [cClass]
  have hf'_large : (cClass f' (φ Y)).card = s + 1 := by
    have hf'_phi_Y : cClass f' (φ Y) = Finset.image (fun w : B_minus_set =>
      w.val) (cClass g Y) ∪ {z} := by
      ext v;
      simp [cClass];
      simp +zetaDelta at *;
      split_ifs <;> simp [*];
      · grind;
      · grind;
      · grind +splitIndPred;
    rw [hf'_phi_Y, Finset.card_union]
    have h_image_card :
        (Finset.image (fun w : B_minus_set => w.val) (cClass g Y)).card = s := by
      rw [Finset.card_image_of_injective _ Subtype.val_injective, hg_class_size]
    simp [*]
  have hf'_other : ∀ c, c ≠ ne.small → c ≠ φ Y → (cClass f' c).card = s := by
    intro c hc_ne_small hc_ne_Y
    by_cases hc_acc : IsAccessible G ne.f ne.small c;
    · by_cases hc_eq_W : c = W;
      · subst hc_eq_W;
        have h_color_class_c : cClass f' c = {y₁} ∪ (cClass ne.f c \ {z}) := by
          ext v; simp [f', cClass];
          by_cases hv : v = z <;> simp [hv, hz_color];
          · grind;
          · by_cases hv : v ∈ B_minus_set <;> simp [hv, hφ_ne_W];
            · exact fun h => False.elim (hv.1 (h ▸ hc_acc));
            · grind +ring;
        rw [h_color_class_c, Finset.card_union_of_disjoint] <;> simp [*,
          Finset.disjoint_singleton_left];
        · rw [Finset.card_sdiff]; simp [*];
          rw [ne.card_other _ hW_ne_small hW_ne_large,
            add_tsub_cancel_of_le (Nat.succ_le_of_lt hs0)];
        · grind +ring;
      · convert ne.card_other c hc_ne_small (show c ≠ ne.large from _) using 1;
        · refine Finset.card_bij (fun v hv => v) ?_ ?_ ?_ <;> simp [*];
          · grind (splits := 20);
          · grind +revert;
        · exact fun h => hacc <| h ▸ hc_acc;
    ·
      obtain ⟨i, hi⟩ : ∃ i : Fin q_nacc, φ i = c := by
        exact ⟨φ_equiv ⟨c, by aesop⟩, by aesop⟩;
      have hc_class_eq : cClass f' c = Finset.image (fun w : B_minus_set => w.val) (cClass g i)
        := by
        ext v; simp [f'];
        split_ifs <;> simp [← hi, hφ_inj.eq_iff];
        · exact iff_of_false (Ne.symm (hφ_ne_W i)) (by aesop);
        · exact ⟨fun h => ⟨by assumption, h⟩, fun ⟨_, h⟩ => h⟩;
        · grind;
        · contrapose! hc_acc; aesop;
      rw [hc_class_eq, Finset.card_image_of_injective _ fun x y hxy =>
        by simpa [Subtype.ext_iff] using hxy, hg_class_size]
  have hf'_small_ne_large : ne.small ≠ φ Y :=
    Ne.symm (fun h => hφ_nacc Y (h ▸ hsmall_acc))
  set ne' : NearlyEquitable G (r + 1) s :=
    ⟨f', hf'_proper, ne.small, φ Y, hf'_small_ne_large, hf'_small, hf'_large, hf'_other, hs⟩
  apply ih ne'
  show (Finset.univ.filter (fun c : Fin (r + 1) =>
      ¬IsAccessible G ne'.f ne'.small c)).card ≤ q_val
  have hf'_eq_acc : ∀ v, IsAccessible G ne.f ne.small (ne.f v) → v ≠ y₁ → v ≠ z →
      f' v = ne.f v := by
    intros v hv_acc hv_ne_y₁ hv_ne_z
    simp [f', hv_ne_y₁, hv_ne_z];
    exact fun h => False.elim <| h.1 hv_acc
  have hcClass_eq_acc : ∀ c, IsAccessible G ne.f ne.small c → c ≠ W →
      cClass f' c = cClass ne.f c := by
    intro c hc hcW
    ext v
    simp [cClass];
    grind
  have hAuxAdj_pres : ∀ c d, AuxAdj G ne.f c d → c ≠ W → d ≠ W →
      IsAccessible G ne.f ne.small c → IsAccessible G ne.f ne.small d →
      AuxAdj G f' c d := by
    intros c d hcd hcW hdW hc hd
    simp [AuxAdj] at hcd ⊢;
    obtain ⟨v, hv₁, hv₂⟩ := hcd;
    use v;
    grind
  have hAuxAdj_pres2 : ∀ c d, AuxAdj G ne.f c d →
      IsAccessible G ne.f ne.small c → IsAccessible G ne.f ne.small d → d ≠ W →
      AuxAdj G f' c d := by
    intros c d hcd hc hd hd_ne_W;
    obtain ⟨v, hv₁, hv₂⟩ := hcd;
    use v;
    grind +ring
  have hacc_not_W : ∀ c, IsAccessible G ne.f ne.small c → c ≠ W →
      IsAccessible G f' ne.small c := by
    intro c hc hcW
    have h_path : Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧ c ≠ W) c ne.small := by
      exact hW_terminal c hc hcW;
    have h_path_f' : ∀ c d, Relation.ReflTransGen (fun c d => AuxAdj G ne.f c d ∧
      c ≠ W) c d → IsAccessible G ne.f ne.small c → IsAccessible G ne.f ne.small d →
        d ≠ W → Relation.ReflTransGen (AuxAdj G f') c d := by
      intros c d h_path hc hd hdW
      induction h_path with
      | refl =>
        exact Relation.ReflTransGen.refl;
      | @tail mid d hprev hstep h =>
        exact Relation.ReflTransGen.trans
          (h (by
            exact Relation.ReflTransGen.head hstep.1 (by tauto)) hstep.2)
          (Relation.ReflTransGen.single
            (hAuxAdj_pres2 _ _ hstep.1 (by
              exact Relation.ReflTransGen.head hstep.1 (by tauto)) hd hdW))
    exact h_path_f' c ne.small h_path hc (by exact Relation.ReflTransGen.refl) (by tauto)
  have hacc_W : IsAccessible G f' ne.small W := by
    have hW_trans : Relation.TransGen (AuxAdj G ne.f) W ne.small :=
      (Relation.reflTransGen_iff_eq_or_transGen.mp hW_acc).resolve_left (Ne.symm hW_ne_small)
    obtain ⟨d, hd_ne_W, hd_adj, hd_path⟩ := transGen_exists_ne_first_step hW_trans hW_ne_small
    have hd_acc : IsAccessible G ne.f ne.small d := hd_path
    exact Relation.ReflTransGen.head
      (hAuxAdj_pres2 W d hd_adj hW_acc hd_acc hd_ne_W)
      (hacc_not_W d hd_acc hd_ne_W)
  have hacc_preserved : ∀ c, IsAccessible G ne.f ne.small c → IsAccessible G f' ne.small c := by
    intro c hc
    by_cases hcW : c = W
    · exact hcW ▸ hacc_W
    · exact hacc_not_W c hc hcW
  have hy₂_mov_W : ∀ w, f' w = W → ¬G.Adj y₂ w := by
    intro w hw
    simp [f'] at hw;
    by_cases hw' : w = y₁ <;> simp [hw'] at hw ⊢;
    · exact Not.imp hnonadj fun a => id (adj_symm G a);
    · grind
  have hf'_y₂_nacc_old : ¬IsAccessible G ne.f ne.small (f' y₂) := by
    grind
  have hy₂_acc_f' : IsAccessible G f' ne.small (f' y₂) :=
    (hacc_preserved W hW_acc).head ⟨y₂, rfl, hy₂_mov_W⟩
  have hsubset : Finset.univ.filter (fun c => ¬IsAccessible G f' ne.small c) ⊆
      Finset.univ.filter (fun c => ¬IsAccessible G ne.f ne.small c) := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact fun h => hc (hacc_preserved c h)
  have hstrict : Finset.univ.filter (fun c => ¬IsAccessible G f' ne.small c) ⊂
      Finset.univ.filter (fun c => ¬IsAccessible G ne.f ne.small c) := by
    refine hsubset.ssubset_of_ne ?_
    intro h
    have hmem : f' y₂ ∈ Finset.univ.filter (fun c => ¬IsAccessible G ne.f ne.small c) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf'_y₂_nacc_old⟩
    rw [← h] at hmem
    exact (Finset.mem_filter.mp hmem).2 hy₂_acc_f'
  linarith [Finset.card_lt_card hstrict]
omit [DecidableEq V] in
lemma non_accessible_case
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (s : ℕ) (hs : Fintype.card V = (r + 1) * s)
    (hd : G.maxDegree ≤ r) (hs0 : 0 < s)
    (ne : NearlyEquitable G (r + 1) s)
    (ih_primary : ∀ (W : Type*) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj] (r' : ℕ),
      Fintype.card W < Fintype.card V →
      H.maxDegree ≤ r' → (r' + 1) ∣ Fintype.card W →
      HasEquitableColoring H (r' + 1)) :
    HasEquitableColoring G (r + 1) := by
  classical
  suffices h_sec : ∀ q_val, ∀ (ne : NearlyEquitable G (r + 1) s),
      (Finset.univ.filter (fun c : Fin (r + 1) =>
        ¬IsAccessible G ne.f ne.small c)).card ≤ q_val →
      HasEquitableColoring G (r + 1) from
    h_sec _ ne le_rfl
  intro q_val
  induction q_val with
  | zero =>
    intro ne' hq'
    have : IsAccessible G ne'.f ne'.small ne'.large := by
      by_contra h
      have : 1 ≤ (Finset.univ.filter
          (fun c : Fin (r + 1) => ¬IsAccessible G ne'.f ne'.small c)).card :=
        Finset.card_pos.mpr ⟨ne'.large, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
      omega
    exact accessible_large_gives_equitable G (r + 1) s ne' this
  | succ q_val ih =>
    intro ne' hq'
    by_cases hacc' : IsAccessible G ne'.f ne'.small ne'.large
    · exact accessible_large_gives_equitable G (r + 1) s ne' hacc'
    ·
      obtain ⟨W, z, y₁, hW_acc, hW_ne_small, hW_ne_large, hz_color, hy₁_nacc,
        hadj_y₁_z, huniq_y₁, hW_terminal, hcases⟩ :=
        good_solo_vertex_exists_terminal G r s hs hd hs0 ne' hacc'
      rcases hcases with ⟨X, hXW, hXacc, hXmov⟩ | ⟨y₂, hy₂ne, hy₂nacc, hy₂adj,
        hy₂uniq, hnonadj, hnotmov⟩
      · exact non_accessible_case1 G r s hs hd hs0 ne' hacc' ih_primary
          q_val W z y₁ hW_acc hW_ne_small hW_ne_large hz_color hy₁_nacc
          hadj_y₁_z huniq_y₁ X hXW hXacc hXmov hW_terminal
      ·
        exact non_accessible_case2_paper G r s hs hd hs0 ne' hacc' ih_primary q_val ih hq'
            W z y₁ y₂ hW_acc hW_ne_small hW_ne_large hz_color hy₁_nacc hadj_y₁_z huniq_y₁
            hy₂ne hy₂nacc hy₂adj hy₂uniq hnonadj
            (fun X hXacc hXW => hnotmov X hXacc hXW) hW_terminal
omit [DecidableEq V] in
lemma hajnal_szemeredi_edge_induction
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (h : G.maxDegree ≤ r) (hdiv : (r + 1) ∣ Fintype.card V)
    (ih_primary : ∀ (W : Type*) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj] (r' : ℕ),
      Fintype.card W < Fintype.card V →
      H.maxDegree ≤ r' → (r' + 1) ∣ Fintype.card W →
      HasEquitableColoring H (r' + 1)) :
    HasEquitableColoring G (r + 1) := by
  classical
  have h_ind : ∀ (G' : SimpleGraph V) [DecidableRel G'.Adj],
      G'.maxDegree ≤ r → HasEquitableColoring G' (r + 1) := by
    intro G' _ hG'
    induction n : G'.edgeFinset.card using Nat.strong_induction_on generalizing G' with
    | h n ih =>
      by_cases h_edge : G'.edgeFinset.Nonempty
      · obtain ⟨e, he⟩ := h_edge
        have h_ind : HasEquitableColoring (G'.deleteEdges {e}) (r + 1) := by
          apply ih (G'.deleteEdges {e}).edgeFinset.card
          · rw [← n]; exact edgeFinset_card_deleteEdges_lt G' e he
          · exact le_trans (maxDegree_deleteEdges_le _ _) hG'
          · rfl
        apply induction_step_with_callback G' r hdiv hG' e
          (by rwa [SimpleGraph.mem_edgeFinset] at he) h_ind
        intro s hs_eq hs0 ne
        by_cases hacc : IsAccessible G' ne.f ne.small ne.large
        · exact accessible_large_gives_equitable G' (r + 1) s ne hacc
        · exact non_accessible_case G' r s hs_eq hG' hs0 ne ih_primary
      · exact equitable_coloring_of_edgeless G' r (by
          ext e; simp only [Set.mem_empty_iff_false, iff_false]
          intro he; exact h_edge ⟨e, SimpleGraph.mem_edgeFinset.mpr he⟩)
  exact h_ind G h
set_option maxHeartbeats 400000 in
private theorem hajnal_szemeredi_outer' : ∀ (n : ℕ)
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (r : ℕ),
    Fintype.card W ≤ n →
    H.maxDegree ≤ r → (r + 1) ∣ Fintype.card W →
    HasEquitableColoring H (r + 1) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro W _ H _ r hn hmax hdiv
    exact hajnal_szemeredi_edge_induction H r hmax hdiv
      (fun W' _ _ H' _ r' hcard hmax' hdiv' =>
        ih (Fintype.card W') (by omega) H' r' le_rfl hmax' hdiv')
omit [DecidableEq V] in
theorem hajnal_szemeredi_divisible' (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (h : G.maxDegree ≤ r) (hdiv : (r + 1) ∣ Fintype.card V) :
    HasEquitableColoring G (r + 1) :=
  hajnal_szemeredi_outer' _ G r le_rfl h hdiv
noncomputable def paddedGraph (G : SimpleGraph V) (p : ℕ) :
    SimpleGraph (V ⊕ Fin p) where
  Adj x y := match x, y with
    | Sum.inl u, Sum.inl v => G.Adj u v
    | Sum.inr i, Sum.inr j => i ≠ j
    | _, _ => False
  symm := ⟨by
    intro x y h
    cases x with
    | inl u =>
      cases y with
      | inl v => exact G.symm.symm u v h
      | inr j => exact False.elim h
    | inr i =>
      cases y with
      | inl v => exact False.elim h
      | inr j => exact Ne.symm h⟩
  loopless := ⟨fun x => by match x with
    | Sum.inl v => exact G.loopless.irrefl v
    | Sum.inr i => simp⟩
noncomputable instance paddedGraph_decRel (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℕ) :
    DecidableRel (paddedGraph G p).Adj := by
  intro x y
  cases x with
  | inl u =>
    cases y with
    | inl v => exact inferInstance
    | inr j => exact isFalse id
  | inr i =>
    cases y with
    | inl v => exact isFalse id
    | inr j => exact inferInstance
omit [Fintype V] [DecidableEq V] in
@[simp]
lemma paddedGraph_adj_inl_inl (G : SimpleGraph V) (p : ℕ) (u v : V) :
    (paddedGraph G p).Adj (Sum.inl u) (Sum.inl v) ↔ G.Adj u v := by
  simp [paddedGraph]
omit [Fintype V] [DecidableEq V] in
@[simp]
lemma paddedGraph_adj_inr_inr (G : SimpleGraph V) (p : ℕ) (i j : Fin p) :
    (paddedGraph G p).Adj (Sum.inr i) (Sum.inr j) ↔ i ≠ j := by
  simp [paddedGraph]
omit [Fintype V] [DecidableEq V] in
@[simp]
lemma paddedGraph_adj_inl_inr (G : SimpleGraph V) (p : ℕ) (v : V) (i : Fin p) :
    ¬(paddedGraph G p).Adj (Sum.inl v) (Sum.inr i) := by
  change ¬False
  exact not_false
omit [Fintype V] [DecidableEq V] in
@[simp]
lemma paddedGraph_adj_inr_inl (G : SimpleGraph V) (p : ℕ) (i : Fin p) (v : V) :
    ¬(paddedGraph G p).Adj (Sum.inr i) (Sum.inl v) := by
  change ¬False
  exact not_false
omit [DecidableEq V] in
lemma paddedGraph_card (p : ℕ) :
    Fintype.card (V ⊕ Fin p) = Fintype.card V + p := by
  simp [Fintype.card_sum]
omit [DecidableEq V] in
lemma paddedGraph_degree_inl (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℕ) (v : V) :
    (paddedGraph G p).degree (Sum.inl v) = G.degree v := by
  refine Finset.card_bij (fun w _hw => Sum.elim id (fun i => by tauto) w) ?_ ?_ ?_ <;>
    simp
omit [DecidableEq V] in
lemma paddedGraph_degree_inr (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℕ) (i : Fin p) :
    (paddedGraph G p).degree (Sum.inr i) = p - 1 := by
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_def]
  rw [show ((paddedGraph G p).neighborSet (Sum.inr i)).toFinset =
    Finset.image Sum.inr (Finset.univ.erase i) from ?_,
    Finset.card_image_of_injective _ fun x y hxy ↦ by simpa using hxy]
  · simp [Finset.card_univ]
  · ext x; aesop
omit [DecidableEq V] in
lemma paddedGraph_maxDegree_le (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℕ) (r : ℕ)
    (hG : G.maxDegree ≤ r) (hp : p ≤ r + 1) :
    (paddedGraph G p).maxDegree ≤ r := by
  apply SimpleGraph.maxDegree_le_of_forall_degree_le
  intro x
  cases x
  · rw [paddedGraph_degree_inl]
    exact le_trans (SimpleGraph.degree_le_maxDegree _ _) hG
  · rw [paddedGraph_degree_inr]; omega
omit [Fintype V] [DecidableEq V] in
lemma paddedGraph_proper_restrict (G : SimpleGraph V) (p : ℕ)
    {k : ℕ} (f : (V ⊕ Fin p) → Fin k) (hf : IsProper (paddedGraph G p) f) :
    IsProper G (f ∘ Sum.inl) := by
  intro u v huv hcolor
  exact hf (Sum.inl u) (Sum.inl v) ((paddedGraph_adj_inl_inl G p u v).mpr huv) hcolor
omit [Fintype V] [DecidableEq V] in
lemma paddedGraph_proper_inr_injective (G : SimpleGraph V) (p : ℕ)
    {k : ℕ} (f : (V ⊕ Fin p) → Fin k) (hf : IsProper (paddedGraph G p) f) :
    Function.Injective (f ∘ Sum.inr) := by
  intro i j hij
  by_contra h
  exact hf (Sum.inr i) (Sum.inr j) ((paddedGraph_adj_inr_inr G p i j).mpr h) hij
lemma equitable_classes_equal_of_dvd {W : Type*} [Fintype W]
    {k : ℕ} (f : W → Fin k)
    (hequit : IsEquitable f) (hdvd : k ∣ Fintype.card W) (c : Fin k) :
    (cClass f c).card = Fintype.card W / k := by
  classical
  obtain ⟨m, hm⟩ := hdvd
  have h_sum : ∑ c : Fin k, (cClass f c).card = Fintype.card W := by
    simp only [cClass, Finset.card_eq_sum_ones,
      Finset.sum_fiberwise (Finset.univ : Finset W)]
    rw [Fintype.card_eq_sum_ones]
  have h_min : ∀ c : Fin k, m ≤ (cClass f c).card := by
    contrapose! h_sum
    refine ne_of_lt (lt_of_lt_of_le (Finset.sum_lt_sum (g := fun _ => m) ?_ ?_) ?_)
    · exact fun i _ => by obtain ⟨j, hj⟩ := h_sum; linarith [hequit i j]
    · aesop
    · simp [hm]
  rw [hm, Nat.mul_div_cancel_left _ (Fin.pos c)]
  exact le_antisymm
    (le_of_not_gt fun h => by
      have := Finset.sum_lt_sum (fun a _ => h_min a) ⟨c, Finset.mem_univ c, h⟩
      simp_all)
    (h_min c)
omit [DecidableEq V] in
lemma cClass_comp_inl_card {k : ℕ} {p : ℕ}
    (f : (V ⊕ Fin p) → Fin k) (c : Fin k) :
    (cClass (f ∘ Sum.inl) c).card =
      (cClass f c).card - (Finset.univ.filter (fun i : Fin p => f (Sum.inr i) = c)).card := by
  unfold cClass
  refine eq_tsub_of_add_eq ?_
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter]
  exact Eq.symm (Fintype.sum_sum_type fun x => if f x = c then 1 else 0)
omit [DecidableEq V] in
lemma paddedGraph_equitable_restrict (G : SimpleGraph V) (p : ℕ)
    {k : ℕ} (f : (V ⊕ Fin p) → Fin k)
    (hf_proper : IsProper (paddedGraph G p) f)
    (hf_equitable : IsEquitable f)
    (hdvd : k ∣ Fintype.card (V ⊕ Fin p)) :
    IsEquitable (f ∘ Sum.inl) := by
  classical
  have h_eq_classes : ∀ c : Fin k, (cClass f c).card = (Fintype.card (V ⊕ Fin p)) / k :=
    fun c => equitable_classes_equal_of_dvd f hf_equitable hdvd c
  have h_inj_classes : ∀ c : Fin k, ((cClass f c).card - (cClass (f ∘ Sum.inl) c).card) ≤ 1
    := by
    intro c
    have h_inj_classes_aux :
        ((Finset.univ.filter (fun i : Fin p => f (Sum.inr i) = c)).card) ≤ 1 := by
      have := paddedGraph_proper_inr_injective G p f hf_proper
      exact Finset.card_le_one.2 fun i hi j hj => this <| by aesop
    rw [cClass_comp_inl_card]
    omega
  intro c₁ c₂
  have h_restrict_le_full :
      (cClass (f ∘ Sum.inl) c₁).card ≤ (cClass f c₁).card := by
    rw [cClass_comp_inl_card]
    exact Nat.sub_le _ _
  have h_full_le_restrict :
      (cClass f c₂).card ≤ (cClass (f ∘ Sum.inl) c₂).card + 1 := by
    have hloss := h_inj_classes c₂
    have hle : (cClass (f ∘ Sum.inl) c₂).card ≤ (cClass f c₂).card := by
      rw [cClass_comp_inl_card]
      exact Nat.sub_le _ _
    omega
  calc
    (cClass (f ∘ Sum.inl) c₁).card ≤ (cClass f c₁).card := h_restrict_le_full
    _ = Fintype.card (V ⊕ Fin p) / k := h_eq_classes c₁
    _ = (cClass f c₂).card := (h_eq_classes c₂).symm
    _ ≤ (cClass (f ∘ Sum.inl) c₂).card + 1 := h_full_le_restrict
lemma padding_dvd (n k : ℕ) (hk : 0 < k) : k ∣ (n + (k - n % k) % k) := by
  suffices h : (n + (k - n % k) % k) % k = 0 by exact Nat.dvd_of_mod_eq_zero h
  calc (n + (k - n % k) % k) % k
      = (n % k + ((k - n % k) % k) % k) % k := by rw [Nat.add_mod]
    _ = (n % k + (k - n % k) % k) % k := by rw [Nat.mod_mod_of_dvd]; exact dvd_refl k
    _ = _ := by
        by_cases h0 : n % k = 0
        · simp [h0]
        · have : n % k < k := Nat.mod_lt n hk
          have : 0 < n % k := Nat.pos_of_ne_zero h0
          rw [Nat.mod_eq_of_lt (by omega : k - n % k < k)]
          have : n % k + (k - n % k) = k := by omega
          rw [this, Nat.mod_self]
omit [DecidableEq V] in
theorem hajnal_szemeredi (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (h : G.maxDegree ≤ r) :
    HasEquitableColoring G (r + 1) := by
  set kk := r + 1
  set n := Fintype.card V
  set p := (kk - n % kk) % kk
  have hk_pos : 0 < kk := Nat.succ_pos r
  have hp_lt : p < kk := Nat.mod_lt _ hk_pos
  have hdiv : kk ∣ (n + p) := padding_dvd n kk hk_pos
  have hcard : Fintype.card (V ⊕ Fin p) = n + p := paddedGraph_card p
  have hmaxdeg : (paddedGraph G p).maxDegree ≤ r :=
    paddedGraph_maxDegree_le G p r h (by omega)
  have hdiv' : kk ∣ Fintype.card (V ⊕ Fin p) := by rw [hcard]; exact hdiv
  obtain ⟨f', hf'_proper, hf'_equitable⟩ := hajnal_szemeredi_divisible'
    (paddedGraph G p) r hmaxdeg hdiv'
  exact ⟨f' ∘ Sum.inl,
    paddedGraph_proper_restrict G p f' hf'_proper,
    paddedGraph_equitable_restrict G p f' hf'_proper hf'_equitable hdiv'⟩
end HajnalSzemeredi
end E914P
namespace OMA.TrianglePack
open Finset SimpleGraph BollobasEldridgeCatlinConjecture
private lemma enough_classes {V : Type} [Fintype V] {k : ℕ} (f : V → Fin k)
    (hk : k = (Fintype.card V + 1) / 3)
    (he : ∀ i j, (univ.filter fun v => f v = i).card ≤ (univ.filter fun v => f v = j).card + 1) :
    Fintype.card V / 3 ≤ (univ.filter fun i => 3 ≤ (univ.filter fun v => f v = i).card).card := by
  classical
  let s (i : Fin k) := (univ.filter fun v => f v = i).card
  let L := univ.filter fun i => 3 ≤ s i
  change Fintype.card V / 3 ≤ L.card
  by_cases h : ∀ i, 3 ≤ s i
  · have hL : L = univ := by ext; simp [L, h]
    rw [hL, card_univ, Fintype.card_fin]; omega
  push Not at h
  obtain ⟨j,hj⟩ := h
  have hs : Fintype.card V = ∑ i, s i := by
    simpa [s] using (card_eq_sum_card_fiberwise (s := (univ : Finset V))
      (t := (univ : Finset (Fin k))) (f := f) (by simp))
  have bound (i : Fin k) : s i ≤ 2 + (if 3 ≤ s i then 1 else 0) := by
    have h' : s i ≤ s j + 1 := he i j
    split_ifs <;> omega
  have hsum : Fintype.card V ≤ 2 * k + L.card := by
    calc
      _ = ∑ i, s i := hs
      _ ≤ ∑ i, (2 + (if 3 ≤ s i then 1 else 0)) := sum_le_sum fun i _ => bound i
      _ = _ := by simp [sum_add_distrib, L, sum_boole, Nat.mul_comm]
  omega
lemma pack {V : Type} [Fintype V] [DecidableEq V] (C G : SimpleGraph V)
    [DecidableRel G.Adj] (hd : 3*(G.maxDegree+1) ≤ Fintype.card V + 1)
    (deg : ∀ v a b c, C.Adj v a → C.Adj v b → C.Adj v c → a = b ∨ a = c ∨ b = c)
    (tri : ∀ x y, C.Adj x y → ∃ u, C.Adj x u ∧ C.Adj y u)
    (equitable : ∀ r : ℕ, G.maxDegree ≤ r → ∃ f : V → Fin (r+1),
      (∀ v w, G.Adj v w → f v ≠ f w) ∧ ∀ i j,
      (univ.filter fun v => f v = i).card ≤ (univ.filter fun v => f v = j).card + 1) :
    Packs C G := by
  classical
  let k := (Fintype.card V + 1)/3
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hmax : G.maxDegree ≤ k-1 := by dsimp [k]; omega
  obtain ⟨f,proper,balanced⟩ := equitable (k-1) hmax
  let fiber (i : Fin (k-1+1)) := univ.filter fun v => f v = i
  let good := univ.filter fun i => 3 ≤ (fiber i).card
  have hgood : Fintype.card V / 3 ≤ good.card :=
    enough_classes f (by dsimp [k] at *; omega) balanced
  let cl (x : V) := insert x (C.neighborFinset x)
  have edge {x y : V} (h : C.Adj x y) :
      cl x = cl y ∧ (cl x).card = 3 := by
    obtain ⟨z,hxz,hyz⟩ := tri _ _ h
    have nodes (u w z' : V) (huw : C.Adj u w) (huz : C.Adj u z') (hwz : w ≠ z') :
        cl u = {u,w,z'} := by
      ext b
      simp only [cl, mem_insert, mem_singleton, mem_neighborFinset]
      constructor
      · rintro (rfl|hb)
        · exact Or.inl rfl
        · rcases deg u b w z' hb huw huz with h|h|h <;> tauto
      · rintro (rfl|rfl|rfl) <;> tauto
    have hx := nodes x y z h hxz hyz.ne
    have hy := nodes y x z h.symm hyz hxz.ne
    exact ⟨by rw [hx,hy]; ext; simp; tauto,
      by rw [hx]; simp [h.ne,hxz.ne,hyz.ne]⟩
  have closed {x y : V} (hy : y ∈ cl x) : cl y = cl x := by
    rcases mem_insert.mp hy with rfl|hy
    · rfl
    · exact (edge ((C.mem_neighborFinset x y).mp hy)).1.symm
  let blocks := (univ.image cl).filter fun T => T.card = 3
  have repr (T : blocks) : ∃ x : V, cl x = T.val := by
    obtain ⟨x,_,hx⟩ := mem_image.mp (mem_filter.mp T.property).1
    exact ⟨x,hx⟩
  let domain := (T : blocks) × ↑T.val
  let src (u : domain) : V := u.2.val
  have src_inj : Function.Injective src := by
    rintro ⟨T,x⟩ ⟨U,y⟩ h
    change x.val = y.val at h
    obtain ⟨v,hv⟩ := repr T
    obtain ⟨w,hw⟩ := repr U
    have a := closed (hv.symm ▸ x.property : x.val ∈ cl v)
    have b := closed (hw.symm ▸ y.property : y.val ∈ cl w)
    have eq : T = U := Subtype.ext (by rw [← hv, ← hw, ← a, ← b, h])
    subst U
    exact congrArg (Sigma.mk T) (Subtype.ext h)
  have hnum : blocks.card ≤ good.card := by
    have a := Fintype.card_le_of_injective src src_inj
    have eq (T : blocks) : Fintype.card ↥T.val = 3 := by
      simpa using (mem_filter.mp T.property).2
    change Fintype.card ((T : blocks) × ↑T.val) ≤ _ at a
    simp only [Fintype.card_sigma, eq, sum_const, card_univ, Fintype.card_coe, smul_eq_mul] at a
    omega
  obtain ⟨label⟩ := Function.Embedding.nonempty_of_card_le
    (by simpa using hnum : Fintype.card ↥blocks ≤ Fintype.card ↥good)
  have embed (T : blocks) : Nonempty (↥T.val ↪ ↥(fiber (label T).val)) := by
    apply Function.Embedding.nonempty_of_card_le
    simp only [Fintype.card_coe]
    exact (mem_filter.mp T.property).2.le.trans (mem_filter.mp (label T).property).2
  let put (T : blocks) := Classical.choice (embed T)
  let dst (u : domain) : V := (put u.1 u.2).val
  have color (T : blocks) (x : T.val) : f (dst ⟨T,x⟩) = (label T).val :=
    (mem_filter.mp (put T x).property).2
  have dst_inj : Function.Injective dst := by
    rintro ⟨T,x⟩ ⟨U,y⟩ h
    have eq : T = U := label.injective (Subtype.ext ((color T x).symm.trans ((congrArg f h).trans (color U y))))
    subst U
    exact congrArg (Sigma.mk T) ((put T).injective (Subtype.ext h))
  obtain ⟨perm,hperm⟩ := Equiv.Perm.exists_extending_pair src dst src_inj dst_inj
  refine ⟨perm, ?_⟩
  intro x y hxy hadj
  let T : blocks := ⟨cl x, mem_filter.mpr ⟨mem_image.mpr ⟨x,mem_univ _,rfl⟩,(edge hxy).2⟩⟩
  let a : T.val := ⟨x, mem_insert_self _ _⟩
  let b : T.val := ⟨y, mem_insert_of_mem ((C.mem_neighborFinset x y).mpr hxy)⟩
  apply proper _ _ hadj
  change f (perm (src ⟨T,a⟩)) = f (perm (src ⟨T,b⟩))
  rw [hperm,hperm,color,color]
end OMA.TrianglePack

namespace OMA.ShortCycles
open SimpleGraph Finset BollobasEldridgeCatlinConjecture
section Helpers
def b01 (p : Prop) [Decidable p] : ℕ := if p then 1 else 0
lemma b01_eq_one {p : Prop} [Decidable p] (h : p) : b01 p = 1 := if_pos h
lemma b01_zero_le {p : Prop} [Decidable p] (h : ¬ p) : b01 p ≤ 0 := by simp [b01, h]
lemma b01_le_one (p : Prop) [Decidable p] : b01 p ≤ 1 := by unfold b01; split_ifs <;> omega
lemma adj_symm_not {V : Type} (G : SimpleGraph V) {u v : V} (h : ¬ G.Adj u v) : ¬ G.Adj v u :=
  fun huv => h huv.symm
def kScore {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj] (a0 a1 a2 a3 a4 : V) : ℕ :=
  2 * (b01 (G.Adj a0 a2) + b01 (G.Adj a0 a3) + b01 (G.Adj a0 a4) +
       b01 (G.Adj a1 a3) + b01 (G.Adj a1 a4) + b01 (G.Adj a2 a4)) +
  b01 (G.Adj a0 a2 ∧ G.Adj a0 a4 ∧ G.Adj a2 a4)
lemma kScore_rev {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj] (a0 a1 a2 a3 a4 : V) :
    kScore G a4 a3 a2 a1 a0 = kScore G a0 a1 a2 a3 a4 := by
  unfold kScore b01
  simp only [G.adj_comm]
  have hiff : (G.Adj a2 a4 ∧ G.Adj a0 a4 ∧ G.Adj a0 a2) ↔
      (G.Adj a0 a2 ∧ G.Adj a0 a4 ∧ G.Adj a2 a4) := by tauto
  simp only [hiff]
  omega
def rCount {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj] (σ : Equiv.Perm V)
    (z : V) (S : Finset V) : ℕ :=
  (S.filter (fun u => G.Adj (σ z) (σ u))).card
lemma rCount_univ_le {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : Equiv.Perm V) (z : V) :
    rCount G σ z univ ≤ G.maxDegree := by
  classical
  apply le_trans _ (G.degree_le_maxDegree (σ z))
  rw [← G.card_neighborFinset_eq_degree]
  apply card_le_card_of_injOn σ _ σ.injective.injOn
  intro u hu
  exact (G.mem_neighborFinset _ _).2 (mem_filter.mp hu).2
lemma rCount_union_disjoint {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : Equiv.Perm V) (z : V) {S T : Finset V} (hd : Disjoint S T) :
    rCount G σ z (S ∪ T) = rCount G σ z S + rCount G σ z T := by
  unfold rCount
  rw [filter_union, card_union_of_disjoint (hd.mono (filter_subset _ _) (filter_subset _ _))]
lemma rCount_biUnion {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : Equiv.Perm V) (z : V) (F : Finset (Finset V))
    (hd : (F : Set (Finset V)).PairwiseDisjoint id) :
    rCount G σ z (F.biUnion id) = ∑ M ∈ F, rCount G σ z M := by
  unfold rCount
  rw [filter_biUnion,
    card_biUnion (fun M hM N hN hne => (hd hM hN hne).mono (filter_subset _ _) (filter_subset _ _))]
  rfl
lemma rCount_1 {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : Equiv.Perm V) (z u0 : V) :
    rCount G σ z {u0} = b01 (G.Adj (σ z) (σ u0)) := by
  rw [rCount, card_filter, sum_singleton]; rfl
lemma rCount_3 {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : Equiv.Perm V) (z u0 u1 u2 : V) (h01 : u0 ≠ u1) (h02 : u0 ≠ u2) (h12 : u1 ≠ u2) :
    rCount G σ z {u0, u1, u2} =
      b01 (G.Adj (σ z) (σ u0)) + b01 (G.Adj (σ z) (σ u1)) + b01 (G.Adj (σ z) (σ u2)) := by
  have m0 : u0 ∉ ({u1, u2} : Finset V) := by simp [h01, h02]
  have m1 : u1 ∉ ({u2} : Finset V) := by simp [h12]
  rw [rCount, card_filter, sum_insert m0, sum_insert m1, sum_singleton]
  dsimp [b01]; omega
lemma rCount_4 {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : Equiv.Perm V) (z u0 u1 u2 u3 : V)
    (h01 : u0 ≠ u1) (h02 : u0 ≠ u2) (h03 : u0 ≠ u3)
    (h12 : u1 ≠ u2) (h13 : u1 ≠ u3) (h23 : u2 ≠ u3) :
    rCount G σ z {u0, u1, u2, u3} =
      b01 (G.Adj (σ z) (σ u0)) + b01 (G.Adj (σ z) (σ u1)) +
      b01 (G.Adj (σ z) (σ u2)) + b01 (G.Adj (σ z) (σ u3)) := by
  have m0 : u0 ∉ ({u1, u2, u3} : Finset V) := by simp [h01, h02, h03]
  have m1 : u1 ∉ ({u2, u3} : Finset V) := by simp [h12, h13]
  have m2 : u2 ∉ ({u3} : Finset V) := by simp [h23]
  rw [rCount, card_filter, sum_insert m0, sum_insert m1, sum_insert m2, sum_singleton]
  dsimp [b01]; omega
lemma rCount_5 {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : Equiv.Perm V) (z u0 u1 u2 u3 u4 : V)
    (h01 : u0 ≠ u1) (h02 : u0 ≠ u2) (h03 : u0 ≠ u3) (h04 : u0 ≠ u4)
    (h12 : u1 ≠ u2) (h13 : u1 ≠ u3) (h14 : u1 ≠ u4)
    (h23 : u2 ≠ u3) (h24 : u2 ≠ u4) (h34 : u3 ≠ u4) :
    rCount G σ z {u0, u1, u2, u3, u4} =
      b01 (G.Adj (σ z) (σ u0)) + b01 (G.Adj (σ z) (σ u1)) + b01 (G.Adj (σ z) (σ u2)) +
      b01 (G.Adj (σ z) (σ u3)) + b01 (G.Adj (σ z) (σ u4)) := by
  have m0 : u0 ∉ ({u1, u2, u3, u4} : Finset V) := by simp [h01, h02, h03, h04]
  have m1 : u1 ∉ ({u2, u3, u4} : Finset V) := by simp [h12, h13, h14]
  have m2 : u2 ∉ ({u3, u4} : Finset V) := by simp [h23, h24]
  have m3 : u3 ∉ ({u4} : Finset V) := by simp [h34]
  rw [rCount, card_filter, sum_insert m0, sum_insert m1, sum_insert m2, sum_insert m3, sum_singleton]
  dsimp [b01]; omega
def invPerm {n : ℕ} (π : Fin n → Fin n) : Fin n → Fin n :=
  fun i => ((List.finRange n).find? (fun j => π j == i)).getD i
def okP {n : ℕ} (π : Fin n → Fin n) : Bool :=
  (List.finRange n).all (fun i => decide (invPerm π (π i) = i ∧ π (invPerm π i) = i))
lemma okP_left {n : ℕ} {π : Fin n → Fin n} (h : okP π = true) : ∀ i, invPerm π (π i) = i := by
  intro i
  exact (of_decide_eq_true ((List.all_eq_true.1 h) i (List.mem_finRange i))).1
lemma okP_right {n : ℕ} {π : Fin n → Fin n} (h : okP π = true) : ∀ i, π (invPerm π i) = i := by
  intro i
  exact (of_decide_eq_true ((List.all_eq_true.1 h) i (List.mem_finRange i))).2
lemma z_false_iso {V : Type} (C G : SimpleGraph V) (σ : Equiv.Perm V)
    (k0 k1 k2 k3 k4 u : V) (hiso : ∀ b, ¬ C.Adj u b)
    (hz : (G.Adj (σ k1) (σ u) ∧ G.Adj (σ k3) (σ u)) ∨
          ∃ b, C.Adj u b ∧ (G.Adj (σ k0) (σ b) ∨ G.Adj (σ k2) (σ b) ∨ G.Adj (σ k4) (σ b)))
    (hn : ¬ G.Adj (σ k1) (σ u) ∨ ¬ G.Adj (σ k3) (σ u)) : False := by
  rcases hz with ⟨h1, h3⟩ | ⟨b, hb, -⟩
  · rcases hn with h | h
    · exact h h1
    · exact h h3
  · exact hiso b hb
lemma z_false_deg2 {V : Type} (C G : SimpleGraph V) (σ : Equiv.Perm V)
    (k0 k1 k2 k3 k4 u up un : V) (hnb : ∀ b, C.Adj u b ↔ b = up ∨ b = un)
    (hz : (G.Adj (σ k1) (σ u) ∧ G.Adj (σ k3) (σ u)) ∨
          ∃ b, C.Adj u b ∧ (G.Adj (σ k0) (σ b) ∨ G.Adj (σ k2) (σ b) ∨ G.Adj (σ k4) (σ b)))
    (hn : ¬ G.Adj (σ k1) (σ u) ∨ ¬ G.Adj (σ k3) (σ u))
    (p0 : ¬ G.Adj (σ k0) (σ up)) (p2 : ¬ G.Adj (σ k2) (σ up)) (p4 : ¬ G.Adj (σ k4) (σ up))
    (n0 : ¬ G.Adj (σ k0) (σ un)) (n2 : ¬ G.Adj (σ k2) (σ un)) (n4 : ¬ G.Adj (σ k4) (σ un)) :
    False := by
  rcases hz with ⟨h1, h3⟩ | ⟨b, hb, h024⟩
  · rcases hn with h | h
    · exact h h1
    · exact h h3
  · rcases (hnb b).1 hb with rfl | rfl
    · rcases h024 with h | h | h
      · exact p0 h
      · exact p2 h
      · exact p4 h
    · rcases h024 with h | h | h
      · exact n0 h
      · exact n2 h
      · exact n4 h
end Helpers
section Components
variable {V : Type} [Fintype V] [DecidableEq V]
def IsComp1 (C : SimpleGraph V) (u0 : V) : Prop :=
  ∀ b, ¬ C.Adj u0 b
def IsComp3 (C : SimpleGraph V) (u0 u1 u2 : V) : Prop :=
  u0 ≠ u1 ∧ u0 ≠ u2 ∧ u1 ≠ u2 ∧
  (∀ b, C.Adj u0 b ↔ b = u2 ∨ b = u1) ∧
  (∀ b, C.Adj u1 b ↔ b = u0 ∨ b = u2) ∧
  (∀ b, C.Adj u2 b ↔ b = u1 ∨ b = u0)
def IsComp4 (C : SimpleGraph V) (u0 u1 u2 u3 : V) : Prop :=
  u0 ≠ u1 ∧ u0 ≠ u2 ∧ u0 ≠ u3 ∧ u1 ≠ u2 ∧ u1 ≠ u3 ∧ u2 ≠ u3 ∧
  (∀ b, C.Adj u0 b ↔ b = u3 ∨ b = u1) ∧
  (∀ b, C.Adj u1 b ↔ b = u0 ∨ b = u2) ∧
  (∀ b, C.Adj u2 b ↔ b = u1 ∨ b = u3) ∧
  (∀ b, C.Adj u3 b ↔ b = u2 ∨ b = u0)
def IsComp5 (C : SimpleGraph V) (u0 u1 u2 u3 u4 : V) : Prop :=
  u0 ≠ u1 ∧ u0 ≠ u2 ∧ u0 ≠ u3 ∧ u0 ≠ u4 ∧
  u1 ≠ u2 ∧ u1 ≠ u3 ∧ u1 ≠ u4 ∧ u2 ≠ u3 ∧ u2 ≠ u4 ∧ u3 ≠ u4 ∧
  (∀ b, C.Adj u0 b ↔ b = u4 ∨ b = u1) ∧
  (∀ b, C.Adj u1 b ↔ b = u0 ∨ b = u2) ∧
  (∀ b, C.Adj u2 b ↔ b = u1 ∨ b = u3) ∧
  (∀ b, C.Adj u3 b ↔ b = u2 ∨ b = u4) ∧
  (∀ b, C.Adj u4 b ↔ b = u3 ∨ b = u0)
omit [Fintype V] [DecidableEq V] in
lemma IsComp3.rot {C : SimpleGraph V} {u0 u1 u2 : V} (h : IsComp3 C u0 u1 u2) :
    IsComp3 C u1 u2 u0 := by
  rcases h with ⟨h01, h02, h12, n0, n1, n2⟩
  exact ⟨h12, h01.symm, h02.symm, n1, n2, n0⟩
omit [Fintype V] [DecidableEq V] in
lemma IsComp3.rev {C : SimpleGraph V} {u0 u1 u2 : V} (h : IsComp3 C u0 u1 u2) :
    IsComp3 C u0 u2 u1 := by
  rcases h with ⟨h01, h02, h12, n0, n1, n2⟩
  refine ⟨h02, h01, h12.symm, ?_, ?_, ?_⟩
  · intro b; rw [n0, or_comm]
  · intro b; rw [n2, or_comm]
  · intro b; rw [n1, or_comm]
omit [Fintype V] [DecidableEq V] in
lemma IsComp4.rot {C : SimpleGraph V} {u0 u1 u2 u3 : V} (h : IsComp4 C u0 u1 u2 u3) :
    IsComp4 C u1 u2 u3 u0 := by
  rcases h with ⟨h01, h02, h03, h12, h13, h23, n0, n1, n2, n3⟩
  exact ⟨h12, h13, h01.symm, h23, h02.symm, h03.symm, n1, n2, n3, n0⟩
omit [Fintype V] [DecidableEq V] in
lemma IsComp4.rev {C : SimpleGraph V} {u0 u1 u2 u3 : V} (h : IsComp4 C u0 u1 u2 u3) :
    IsComp4 C u0 u3 u2 u1 := by
  rcases h with ⟨h01, h02, h03, h12, h13, h23, n0, n1, n2, n3⟩
  refine ⟨h03, h02, h01, h23.symm, h13.symm, h12.symm, ?_, ?_, ?_, ?_⟩
  · intro b; rw [n0, or_comm]
  · intro b; rw [n3, or_comm]
  · intro b; rw [n2, or_comm]
  · intro b; rw [n1, or_comm]
omit [Fintype V] [DecidableEq V] in
lemma IsComp5.rot {C : SimpleGraph V} {u0 u1 u2 u3 u4 : V} (h : IsComp5 C u0 u1 u2 u3 u4) :
    IsComp5 C u1 u2 u3 u4 u0 := by
  rcases h with ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34, n0, n1, n2, n3, n4⟩
  exact ⟨h12, h13, h14, h01.symm, h23, h24, h02.symm, h34, h03.symm, h04.symm, n1, n2, n3, n4, n0⟩
omit [Fintype V] [DecidableEq V] in
lemma IsComp5.rev {C : SimpleGraph V} {u0 u1 u2 u3 u4 : V} (h : IsComp5 C u0 u1 u2 u3 u4) :
    IsComp5 C u0 u4 u3 u2 u1 := by
  rcases h with ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34, n0, n1, n2, n3, n4⟩
  refine ⟨h04, h03, h02, h01, h34.symm, h24.symm, h14.symm, h23.symm, h13.symm, h12.symm,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro b; rw [n0, or_comm]
  · intro b; rw [n4, or_comm]
  · intro b; rw [n3, or_comm]
  · intro b; rw [n2, or_comm]
  · intro b; rw [n1, or_comm]
omit [Fintype V] [DecidableEq V] in
lemma IsComp5.revK {C : SimpleGraph V} {k0 k1 k2 k3 k4 : V} (h : IsComp5 C k0 k1 k2 k3 k4) :
    IsComp5 C k4 k3 k2 k1 k0 :=
  h.rev.rot
noncomputable def compSet (C : SimpleGraph V) (v : V) : Finset V := by
  classical exact univ.filter (C.Reachable v)
lemma mem_compSet (C : SimpleGraph V) (v u : V) : u ∈ compSet C v ↔ C.Reachable v u := by
  classical simp [compSet]
lemma self_mem_compSet (C : SimpleGraph V) (v : V) : v ∈ compSet C v :=
  (mem_compSet C v v).2 (Reachable.refl v)
lemma compSet_closed (C : SimpleGraph V) {v u w : V} (hu : u ∈ compSet C v) (hadj : C.Adj u w) :
    w ∈ compSet C v :=
  (mem_compSet C v w).2 (((mem_compSet C v u).1 hu).trans hadj.reachable)
lemma compSet_eq_of_mem (C : SimpleGraph V) {v u : V} (hu : u ∈ compSet C v) :
    compSet C u = compSet C v := by
  ext w
  rw [mem_compSet, mem_compSet]
  have hvu := (mem_compSet C v u).1 hu
  exact ⟨fun huw => hvu.trans huw, fun hvw => hvu.symm.trans hvw⟩
lemma compSet_card_eq_ncard (C : SimpleGraph V) (v : V) :
    (compSet C v).card = Set.ncard {u | C.Reachable v u} := by
  have heq : ((compSet C v : Finset V) : Set V) = {u | C.Reachable v u} := by
    ext u; exact mem_compSet C v u
  rw [← heq, Set.ncard_coe_finset]
lemma compSet_disjoint (C : SimpleGraph V) {M1 M2 : Finset V}
    (h1 : M1 ∈ univ.image (compSet C)) (h2 : M2 ∈ univ.image (compSet C)) (hne : M1 ≠ M2) :
    Disjoint M1 M2 := by
  rw [Finset.disjoint_left]
  intro w hw1 hw2
  obtain ⟨v1, _, rfl⟩ := mem_image.1 h1
  obtain ⟨v2, _, rfl⟩ := mem_image.1 h2
  exact hne ((compSet_eq_of_mem C hw1).symm.trans (compSet_eq_of_mem C hw2))
lemma remComps_biUnion (C : SimpleGraph V) (v0 : V) :
    ((univ.image (compSet C)).erase (compSet C v0)).biUnion id = (compSet C v0)ᶜ := by
  ext u
  simp only [mem_biUnion, mem_erase, mem_image, mem_univ, true_and, id_eq, mem_compl]
  constructor
  · rintro ⟨M, ⟨hne, w, rfl⟩, hu⟩ hu0
    exact hne ((compSet_eq_of_mem C hu).symm.trans (compSet_eq_of_mem C hu0))
  · intro hu0
    refine ⟨compSet C u, ⟨fun heq => hu0 ?_, u, rfl⟩, self_mem_compSet C u⟩
    rw [← heq]; exact self_mem_compSet C u
lemma compSet_classify (C : SimpleGraph V)
    (hdeg : ∀ v a b c, C.Adj v a → C.Adj v b → C.Adj v c → a = b ∨ a = c ∨ b = c)
    (hnl : ∀ x y, C.Adj x y → ∃ z, z ≠ y ∧ C.Adj x z)
    (hshort : ∀ v, Set.ncard {u | C.Reachable v u} ≤ 5) (v : V) :
    (∃ u0, compSet C v = {u0} ∧ IsComp1 C u0) ∨
    (∃ u0 u1 u2, compSet C v = {u0, u1, u2} ∧ IsComp3 C u0 u1 u2) ∨
    (∃ u0 u1 u2 u3, compSet C v = {u0, u1, u2, u3} ∧ IsComp4 C u0 u1 u2 u3) ∨
    (∃ u0 u1 u2 u3 u4, compSet C v = {u0, u1, u2, u3, u4} ∧ IsComp5 C u0 u1 u2 u3 u4) := by
  classical
  by_cases hadj : ∃ x, C.Adj x v
  swap
  · left
    refine ⟨v, ?_, fun b hb => hadj ⟨b, hb.symm⟩⟩
    ext u
    rw [mem_compSet, mem_singleton]
    constructor
    · rintro ⟨w⟩
      cases w with
      | nil => rfl
      | cons h _ => exact absurd ⟨_, h.symm⟩ hadj
    · intro hu_eq; rw [hu_eq]
  obtain ⟨x, hxv⟩ := hadj
  obtain ⟨p, L, hL2, hinj, hp0, hpL, hpadj, hcov, hnb, hnbL⟩ := OMA.cycle_path C hdeg hnl x v hxv
  have hreach_p : ∀ j, j ≤ L → C.Reachable v (p j) := by
    intro j hj
    induction j with
    | zero => rw [hp0]
    | succ k ih => exact (ih (by omega)).trans (hpadj k (by omega)).reachable
  have hcomp_eq : compSet C v = (range (L + 1)).image p := by
    ext u
    rw [mem_compSet, mem_image]
    constructor
    · intro hu
      obtain ⟨j, hj, rfl⟩ := hcov u hu
      exact ⟨j, mem_range.2 (by omega), rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact hreach_p j (by rw [mem_range] at hj; omega)
  have hcard : (compSet C v).card = L + 1 := by
    rw [hcomp_eq, card_image_of_injOn, card_range]
    intro j hj k hk hjk
    simp only [mem_coe, mem_range] at hj hk
    exact hinj j k (by omega) (by omega) hjk
  have hcard_le : L + 1 ≤ 5 := by
    have := hshort v
    rw [← compSet_card_eq_ncard, hcard] at this
    exact this
  have hnb0 : ∀ b, C.Adj (p 0) b ↔ b = p L ∨ b = p 1 := by
    intro b
    have h0L : C.Adj (p 0) (p L) := by rw [hp0, hpL]; exact hxv.symm
    have h01 : C.Adj (p 0) (p 1) := hpadj 0 (by omega)
    constructor
    · intro hb
      rcases hdeg (p 0) b (p L) (p 1) hb h0L h01 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · have := hinj L 1 le_rfl (by omega) h; omega
    · rintro (rfl | rfl)
      · exact h0L
      · exact h01
  have hnb_mid : ∀ j, 1 ≤ j → j < L → ∀ b, C.Adj (p j) b ↔ b = p (j - 1) ∨ b = p (j + 1) := by
    intro j hj1 hj2 b
    constructor
    · exact hnb j b hj1 hj2
    · rintro (rfl | rfl)
      · have h := hpadj (j - 1) (by omega)
        rw [show j - 1 + 1 = j by omega] at h
        exact h.symm
      · exact hpadj j hj2
  have hnb_end : ∀ b, C.Adj (p L) b ↔ b = p (L - 1) ∨ b = p 0 := by
    intro b
    have hLL : C.Adj (p L) (p (L - 1)) := by
      have h := hpadj (L - 1) (by omega)
      rw [show L - 1 + 1 = L by omega] at h
      exact h.symm
    have hL0 : C.Adj (p L) (p 0) := by rw [hpL, hp0]; exact hxv
    constructor
    · intro hb
      rw [hpL] at hb
      rcases hnbL b hb with h | h
      · exact Or.inl h
      · exact Or.inr (h.trans hp0.symm)
    · rintro (rfl | rfl)
      · exact hLL
      · exact hL0
  have ne_of_idx : ∀ j k, j ≤ L → k ≤ L → j ≠ k → p j ≠ p k :=
    fun j k hj hk hne hp => hne (hinj j k hj hk hp)
  have hL_cases : L = 2 ∨ L = 3 ∨ L = 4 := by omega
  rcases hL_cases with rfl | rfl | rfl
  · right; left
    refine ⟨p 0, p 1, p 2, ?_, ?_⟩
    · rw [hcomp_eq]; ext w; simp only [mem_image, mem_range, mem_insert, mem_singleton]
      constructor
      · rintro ⟨a, ha, rfl⟩; interval_cases a <;> tauto
      · rintro (rfl | rfl | rfl)
        · exact ⟨0, by omega, rfl⟩
        · exact ⟨1, by omega, rfl⟩
        · exact ⟨2, by omega, rfl⟩
    · exact ⟨ne_of_idx 0 1 (by omega) (by omega) (by omega),
             ne_of_idx 0 2 (by omega) (by omega) (by omega),
             ne_of_idx 1 2 (by omega) (by omega) (by omega),
             hnb0, hnb_mid 1 le_rfl (by omega), hnb_end⟩
  · right; right; left
    refine ⟨p 0, p 1, p 2, p 3, ?_, ?_⟩
    · rw [hcomp_eq]; ext w; simp only [mem_image, mem_range, mem_insert, mem_singleton]
      constructor
      · rintro ⟨a, ha, rfl⟩; interval_cases a <;> tauto
      · rintro (rfl | rfl | rfl | rfl)
        · exact ⟨0, by omega, rfl⟩
        · exact ⟨1, by omega, rfl⟩
        · exact ⟨2, by omega, rfl⟩
        · exact ⟨3, by omega, rfl⟩
    · exact ⟨ne_of_idx 0 1 (by omega) (by omega) (by omega),
             ne_of_idx 0 2 (by omega) (by omega) (by omega),
             ne_of_idx 0 3 (by omega) (by omega) (by omega),
             ne_of_idx 1 2 (by omega) (by omega) (by omega),
             ne_of_idx 1 3 (by omega) (by omega) (by omega),
             ne_of_idx 2 3 (by omega) (by omega) (by omega),
             hnb0, hnb_mid 1 le_rfl (by omega), hnb_mid 2 (by omega) (by omega), hnb_end⟩
  · right; right; right
    refine ⟨p 0, p 1, p 2, p 3, p 4, ?_, ?_⟩
    · rw [hcomp_eq]; ext w; simp only [mem_image, mem_range, mem_insert, mem_singleton]
      constructor
      · rintro ⟨a, ha, rfl⟩; interval_cases a <;> tauto
      · rintro (rfl | rfl | rfl | rfl | rfl)
        · exact ⟨0, by omega, rfl⟩
        · exact ⟨1, by omega, rfl⟩
        · exact ⟨2, by omega, rfl⟩
        · exact ⟨3, by omega, rfl⟩
        · exact ⟨4, by omega, rfl⟩
    · exact ⟨ne_of_idx 0 1 (by omega) (by omega) (by omega),
             ne_of_idx 0 2 (by omega) (by omega) (by omega),
             ne_of_idx 0 3 (by omega) (by omega) (by omega),
             ne_of_idx 0 4 (by omega) (by omega) (by omega),
             ne_of_idx 1 2 (by omega) (by omega) (by omega),
             ne_of_idx 1 3 (by omega) (by omega) (by omega),
             ne_of_idx 1 4 (by omega) (by omega) (by omega),
             ne_of_idx 2 3 (by omega) (by omega) (by omega),
             ne_of_idx 2 4 (by omega) (by omega) (by omega),
             ne_of_idx 3 4 (by omega) (by omega) (by omega),
             hnb0, hnb_mid 1 le_rfl (by omega), hnb_mid 2 (by omega) (by omega),
             hnb_mid 3 (by omega) (by omega), hnb_end⟩
end Components
section LocalPerm
noncomputable def extPerm {V : Type} [DecidableEq V] {s : ℕ} (f : Fin s → V)
    (hf : Function.Injective f) (π π_inv : Fin s → Fin s)
    (h1 : ∀ i, π_inv (π i) = i) (h2 : ∀ i, π (π_inv i) = i) : Equiv.Perm V where
  toFun v := if h : ∃ i, f i = v then f (π (Classical.choose h)) else v
  invFun v := if h : ∃ i, f i = v then f (π_inv (Classical.choose h)) else v
  left_inv v := by
    dsimp only
    by_cases hv : ∃ i, f i = v
    · obtain ⟨i, rfl⟩ := hv
      have h_ex1 : ∃ j, f j = f i := ⟨i, rfl⟩
      rw [dif_pos h_ex1]
      have hi1 : Classical.choose h_ex1 = i := hf (Classical.choose_spec h_ex1)
      rw [hi1]
      have h_ex2 : ∃ j, f j = f (π i) := ⟨π i, rfl⟩
      rw [dif_pos h_ex2]
      have hi2 : Classical.choose h_ex2 = π i := hf (Classical.choose_spec h_ex2)
      rw [hi2, h1]
    · rw [dif_neg hv, dif_neg hv]
  right_inv v := by
    dsimp only
    by_cases hv : ∃ i, f i = v
    · obtain ⟨i, rfl⟩ := hv
      have h_ex1 : ∃ j, f j = f i := ⟨i, rfl⟩
      rw [dif_pos h_ex1]
      have hi1 : Classical.choose h_ex1 = i := hf (Classical.choose_spec h_ex1)
      rw [hi1]
      have h_ex2 : ∃ j, f j = f (π_inv i) := ⟨π_inv i, rfl⟩
      rw [dif_pos h_ex2]
      have hi2 : Classical.choose h_ex2 = π_inv i := hf (Classical.choose_spec h_ex2)
      rw [hi2, h2]
    · rw [dif_neg hv, dif_neg hv]
lemma extPerm_apply_f {V : Type} [DecidableEq V] {s : ℕ} (f : Fin s → V)
    (hf : Function.Injective f) (π π_inv : Fin s → Fin s)
    (h1 : ∀ i, π_inv (π i) = i) (h2 : ∀ i, π (π_inv i) = i) (i : Fin s) :
    extPerm f hf π π_inv h1 h2 (f i) = f (π i) := by
  change (if h : ∃ j, f j = f i then f (π (Classical.choose h)) else f i) = f (π i)
  have hex : ∃ j, f j = f i := ⟨i, rfl⟩
  rw [dif_pos hex, hf (Classical.choose_spec hex)]
lemma extPerm_apply_out {V : Type} [DecidableEq V] {s : ℕ} (f : Fin s → V)
    (hf : Function.Injective f) (π π_inv : Fin s → Fin s)
    (h1 : ∀ i, π_inv (π i) = i) (h2 : ∀ i, π (π_inv i) = i) {v : V} (hv : ∀ i, f i ≠ v) :
    extPerm f hf π π_inv h1 h2 v = v := by
  change (if h : ∃ j, f j = v then f (π (Classical.choose h)) else v) = v
  rw [dif_neg (fun ⟨j, hj⟩ => hv j hj)]
lemma local_pack_gen {V : Type} [Fintype V] [DecidableEq V] {s : ℕ}
    (C G : SimpleGraph V) (x y : V) (σ : Equiv.Perm V)
    (hσ : ∀ a b, C.Adj a b → ¬(a = x ∧ b = y) → ¬(a = y ∧ b = x) → ¬ G.Adj (σ a) (σ b))
    (f : Fin s → V) (hf : Function.Injective f)
    (hx : ∃ i, f i = x) (_hy : ∃ i, f i = y)
    (hcl : ∀ i b, C.Adj (f i) b → ∃ j, f j = b)
    (π π_inv : Fin s → Fin s) (h1 : ∀ i, π_inv (π i) = i) (h2 : ∀ i, π (π_inv i) = i)
    (hgood : ∀ i j, C.Adj (f i) (f j) → ¬ G.Adj (σ (f (π i))) (σ (f (π j)))) :
    Packs C G := by
  refine ⟨(extPerm f hf π π_inv h1 h2).trans σ, fun a b hab => ?_⟩
  simp only [Equiv.trans_apply]
  by_cases ha : ∃ i, f i = a
  · obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hcl i b hab
    rw [extPerm_apply_f, extPerm_apply_f]
    exact hgood i j hab
  · have ha' : ∀ i, f i ≠ a := fun i hi => ha ⟨i, hi⟩
    have hb' : ∀ j, f j ≠ b := fun j hj => by
      subst hj
      obtain ⟨i, rfl⟩ := hcl j a hab.symm
      exact ha ⟨i, rfl⟩
    rw [extPerm_apply_out f hf π π_inv h1 h2 ha', extPerm_apply_out f hf π π_inv h1 h2 hb']
    refine hσ a b hab ?_ ?_
    · rintro ⟨rfl, -⟩; exact ha hx
    · rintro ⟨-, hbx⟩; obtain ⟨j, hj⟩ := hx; exact hb' j (hj.trans hbx.symm)
lemma local_almost_gen {V : Type} [DecidableEq V] {s : ℕ}
    (C G : SimpleGraph V) (v_x v_y : V) (i_x i_y : Fin s) (σ : Equiv.Perm V)
    (hσ : ∀ a b, C.Adj a b → ¬(a = v_x ∧ b = v_y) → ¬(a = v_y ∧ b = v_x) → ¬ G.Adj (σ a) (σ b))
    (f : Fin s → V) (hf : Function.Injective f)
    (hvx : f i_x = v_x) (hvy : f i_y = v_y)
    (hcl : ∀ i b, C.Adj (f i) b → ∃ j, f j = b)
    (π π_inv : Fin s → Fin s) (h1 : ∀ i, π_inv (π i) = i) (h2 : ∀ i, π (π_inv i) = i)
    (hgood : ∀ i j, C.Adj (f i) (f j) → ¬(i = i_x ∧ j = i_y) → ¬(i = i_y ∧ j = i_x) →
      ¬ G.Adj (σ (f (π i))) (σ (f (π j)))) :
    let τ := (extPerm f hf π π_inv h1 h2).trans σ
    (∀ a b, C.Adj a b → ¬(a = v_x ∧ b = v_y) → ¬(a = v_y ∧ b = v_x) → ¬ G.Adj (τ a) (τ b)) ∧
    (∀ i, τ (f i) = σ (f (π i))) := by
  refine ⟨fun a b hab hn1 hn2 => ?_, fun i => by simp [extPerm_apply_f]⟩
  simp only [Equiv.trans_apply]
  by_cases ha : ∃ i, f i = a
  · obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hcl i b hab
    rw [extPerm_apply_f, extPerm_apply_f]
    refine hgood i j hab ?_ ?_
    · rintro ⟨rfl, rfl⟩; exact hn1 ⟨hvx, hvy⟩
    · rintro ⟨rfl, rfl⟩; exact hn2 ⟨hvy, hvx⟩
  · have ha' : ∀ i, f i ≠ a := fun i hi => ha ⟨i, hi⟩
    have hb' : ∀ j, f j ≠ b := fun j hj => by
      subst hj
      obtain ⟨i, rfl⟩ := hcl j a hab.symm
      exact ha ⟨i, rfl⟩
    rw [extPerm_apply_out f hf π π_inv h1 h2 ha', extPerm_apply_out f hf π π_inv h1 h2 hb']
    exact hσ a b hab hn1 hn2
lemma pack4_0 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) (k0 k1 k2 k3 : V) (hK : IsComp4 C k0 k1 k2 k3) (σ : Equiv.Perm V)
    (hσ : ∀ a b, C.Adj a b → ¬(a = k3 ∧ b = k0) → ¬(a = k0 ∧ b = k3) → ¬ G.Adj (σ a) (σ b))
    (π : Fin 4 → Fin 4)
    (he0 : ¬ G.Adj (σ (![k0, k1, k2, k3] (π 0))) (σ (![k0, k1, k2, k3] (π 1))))
    (he1 : ¬ G.Adj (σ (![k0, k1, k2, k3] (π 1))) (σ (![k0, k1, k2, k3] (π 2))))
    (he2 : ¬ G.Adj (σ (![k0, k1, k2, k3] (π 2))) (σ (![k0, k1, k2, k3] (π 3))))
    (he3 : ¬ G.Adj (σ (![k0, k1, k2, k3] (π 3))) (σ (![k0, k1, k2, k3] (π 0))))
    (hok : okP π = true := by rfl) : Packs C G := by
  let f : Fin 4 → V := ![k0, k1, k2, k3]
  rcases hK with ⟨hk01, hk02, hk03, hk12, hk13, hk23, hkn0, hkn1, hkn2, hkn3⟩
  have hf : Function.Injective f := by
    intro i j hij; fin_cases i <;> fin_cases j <;> dsimp [f] at hij ⊢
    all_goals first | rfl | exact absurd hij (by assumption) | exact absurd hij.symm (by assumption)
  have hcl : ∀ i b, C.Adj (f i) b → ∃ j, f j = b := by
    intro i b hab; fin_cases i <;> dsimp [f] at hab
    · rcases (hkn0 b).1 hab with rfl | rfl
      · exact ⟨3, rfl⟩
      · exact ⟨1, rfl⟩
    · rcases (hkn1 b).1 hab with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨2, rfl⟩
    · rcases (hkn2 b).1 hab with rfl | rfl
      · exact ⟨1, rfl⟩
      · exact ⟨3, rfl⟩
    · rcases (hkn3 b).1 hab with rfl | rfl
      · exact ⟨2, rfl⟩
      · exact ⟨0, rfl⟩
  have hgood : ∀ i j, C.Adj (f i) (f j) → ¬ G.Adj (σ (f (π i))) (σ (f (π j))) := by
    intro i j hij; fin_cases i <;> dsimp [f] at hij
    · rcases (hkn0 (f j)).1 hij with hj | hj
      · have rj : j = 3 := hf hj; subst rj
        exact (adj_symm_not G he3)
      · have rj : j = 1 := hf hj; subst rj
        exact he0
    · rcases (hkn1 (f j)).1 hij with hj | hj
      · have rj : j = 0 := hf hj; subst rj
        exact (adj_symm_not G he0)
      · have rj : j = 2 := hf hj; subst rj
        exact he1
    · rcases (hkn2 (f j)).1 hij with hj | hj
      · have rj : j = 1 := hf hj; subst rj
        exact (adj_symm_not G he1)
      · have rj : j = 3 := hf hj; subst rj
        exact he2
    · rcases (hkn3 (f j)).1 hij with hj | hj
      · have rj : j = 2 := hf hj; subst rj
        exact (adj_symm_not G he2)
      · have rj : j = 0 := hf hj; subst rj
        exact he3
  exact local_pack_gen C G k3 k0 σ hσ f hf ⟨3, rfl⟩ ⟨0, rfl⟩ hcl π (invPerm π) (okP_left hok) (okP_right hok) hgood
lemma pack5_0 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) (k0 k1 k2 k3 k4 : V) (hK : IsComp5 C k0 k1 k2 k3 k4) (σ : Equiv.Perm V)
    (hσ : ∀ a b, C.Adj a b → ¬(a = k4 ∧ b = k0) → ¬(a = k0 ∧ b = k4) → ¬ G.Adj (σ a) (σ b))
    (π : Fin 5 → Fin 5)
    (he0 : ¬ G.Adj (σ (![k0, k1, k2, k3, k4] (π 0))) (σ (![k0, k1, k2, k3, k4] (π 1))))
    (he1 : ¬ G.Adj (σ (![k0, k1, k2, k3, k4] (π 1))) (σ (![k0, k1, k2, k3, k4] (π 2))))
    (he2 : ¬ G.Adj (σ (![k0, k1, k2, k3, k4] (π 2))) (σ (![k0, k1, k2, k3, k4] (π 3))))
    (he3 : ¬ G.Adj (σ (![k0, k1, k2, k3, k4] (π 3))) (σ (![k0, k1, k2, k3, k4] (π 4))))
    (he4 : ¬ G.Adj (σ (![k0, k1, k2, k3, k4] (π 4))) (σ (![k0, k1, k2, k3, k4] (π 0))))
    (hok : okP π = true := by rfl) : Packs C G := by
  let f : Fin 5 → V := ![k0, k1, k2, k3, k4]
  rcases hK with ⟨hk01, hk02, hk03, hk04, hk12, hk13, hk14, hk23, hk24, hk34, hkn0, hkn1, hkn2, hkn3, hkn4⟩
  have hf : Function.Injective f := by
    intro i j hij; fin_cases i <;> fin_cases j <;> dsimp [f] at hij ⊢
    all_goals first | rfl | exact absurd hij (by assumption) | exact absurd hij.symm (by assumption)
  have hcl : ∀ i b, C.Adj (f i) b → ∃ j, f j = b := by
    intro i b hab; fin_cases i <;> dsimp [f] at hab
    · rcases (hkn0 b).1 hab with rfl | rfl
      · exact ⟨4, rfl⟩
      · exact ⟨1, rfl⟩
    · rcases (hkn1 b).1 hab with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨2, rfl⟩
    · rcases (hkn2 b).1 hab with rfl | rfl
      · exact ⟨1, rfl⟩
      · exact ⟨3, rfl⟩
    · rcases (hkn3 b).1 hab with rfl | rfl
      · exact ⟨2, rfl⟩
      · exact ⟨4, rfl⟩
    · rcases (hkn4 b).1 hab with rfl | rfl
      · exact ⟨3, rfl⟩
      · exact ⟨0, rfl⟩
  have hgood : ∀ i j, C.Adj (f i) (f j) → ¬ G.Adj (σ (f (π i))) (σ (f (π j))) := by
    intro i j hij; fin_cases i <;> dsimp [f] at hij
    · rcases (hkn0 (f j)).1 hij with hj | hj
      · have rj : j = 4 := hf hj; subst rj
        exact (adj_symm_not G he4)
      · have rj : j = 1 := hf hj; subst rj
        exact he0
    · rcases (hkn1 (f j)).1 hij with hj | hj
      · have rj : j = 0 := hf hj; subst rj
        exact (adj_symm_not G he0)
      · have rj : j = 2 := hf hj; subst rj
        exact he1
    · rcases (hkn2 (f j)).1 hij with hj | hj
      · have rj : j = 1 := hf hj; subst rj
        exact (adj_symm_not G he1)
      · have rj : j = 3 := hf hj; subst rj
        exact he2
    · rcases (hkn3 (f j)).1 hij with hj | hj
      · have rj : j = 2 := hf hj; subst rj
        exact (adj_symm_not G he2)
      · have rj : j = 4 := hf hj; subst rj
        exact he3
    · rcases (hkn4 (f j)).1 hij with hj | hj
      · have rj : j = 3 := hf hj; subst rj
        exact (adj_symm_not G he3)
      · have rj : j = 0 := hf hj; subst rj
        exact he4
  exact local_pack_gen C G k4 k0 σ hσ f hf ⟨4, rfl⟩ ⟨0, rfl⟩ hcl π (invPerm π) (okP_left hok) (okP_right hok) hgood
end LocalPerm
section SumAndRelocate
lemma rCount_rem_add_le {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (σ : Equiv.Perm V) (v0 z : V) :
    (∑ M ∈ (univ.image (compSet C)).erase (compSet C v0), rCount G σ z M) +
      rCount G σ z (compSet C v0) ≤ G.maxDegree := by
  have hpd : (((univ.image (compSet C)).erase (compSet C v0) : Finset (Finset V)) :
      Set (Finset V)).PairwiseDisjoint id := by
    intro M1 h1 M2 h2 hne
    exact compSet_disjoint C (mem_of_mem_erase h1) (mem_of_mem_erase h2) hne
  have huniv : (compSet C v0)ᶜ ∪ compSet C v0 = univ := by
    ext x; simp only [mem_union, mem_compl, mem_univ, iff_true]; exact (em _).symm
  rw [← rCount_biUnion G σ z _ hpd, remComps_biUnion C v0,
      ← rCount_union_disjoint G σ z disjoint_compl_left, huniv]
  exact rCount_univ_le G σ z
lemma card_rem_add {V : Type} [Fintype V] [DecidableEq V] (C : SimpleGraph V) (v0 : V) :
    (∑ M ∈ (univ.image (compSet C)).erase (compSet C v0), M.card) +
      (compSet C v0).card = Fintype.card V := by
  have hpd : (((univ.image (compSet C)).erase (compSet C v0) : Finset (Finset V)) :
      Set (Finset V)).PairwiseDisjoint id := by
    intro M1 h1 M2 h2 hne
    exact compSet_disjoint C (mem_of_mem_erase h1) (mem_of_mem_erase h2) hne
  have hbi : ((univ.image (compSet C)).erase (compSet C v0)).biUnion id = (compSet C v0)ᶜ :=
    remComps_biUnion C v0
  have hc : (((univ.image (compSet C)).erase (compSet C v0)).biUnion id).card =
      ∑ M ∈ (univ.image (compSet C)).erase (compSet C v0), M.card := card_biUnion hpd
  rw [← hc, hbi, card_compl_add_card]
lemma sum4_contradiction {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj]
    (hd : 3 * (G.maxDegree + 1) ≤ Fintype.card V + 1)
    (k0 k1 k2 k3 : V) (hK_card : (compSet C k0).card = 4) (σ : Equiv.Perm V)
    (hK_deg : 7 ≤ 2 * rCount G σ k0 (compSet C k0) + rCount G σ k1 (compSet C k0) +
      rCount G σ k2 (compSet C k0) + 2 * rCount G σ k3 (compSet C k0))
    (hM_bound : ∀ M ∈ (univ.image (compSet C)).erase (compSet C k0),
      2 * M.card ≤ 2 * rCount G σ k0 M + rCount G σ k1 M +
        rCount G σ k2 M + 2 * rCount G σ k3 M) : False := by
  have hsum := sum_le_sum hM_bound
  simp only [← mul_sum, sum_add_distrib] at hsum
  have c0 := rCount_rem_add_le C G σ k0 k0
  have c1 := rCount_rem_add_le C G σ k0 k1
  have c2 := rCount_rem_add_le C G σ k0 k2
  have c3 := rCount_rem_add_le C G σ k0 k3
  have cn := card_rem_add C k0
  omega
lemma sum5_contradiction {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj]
    (hd : 3 * (G.maxDegree + 1) ≤ Fintype.card V + 1)
    (k0 k1 k2 k3 k4 : V) (hK_card : (compSet C k0).card = 5) (σ : Equiv.Perm V)
    (w0 w1 w2 w3 w4 S : ℕ) (hwS : w0 + w1 + w2 + w3 + w4 = 3 * S)
    (hK_deg : 3 * S < w0 * rCount G σ k0 (compSet C k0) + w1 * rCount G σ k1 (compSet C k0) +
      w2 * rCount G σ k2 (compSet C k0) + w3 * rCount G σ k3 (compSet C k0) +
      w4 * rCount G σ k4 (compSet C k0))
    (hM_bound : ∀ M ∈ (univ.image (compSet C)).erase (compSet C k0),
      S * M.card ≤ w0 * rCount G σ k0 M + w1 * rCount G σ k1 M +
        w2 * rCount G σ k2 M + w3 * rCount G σ k3 M + w4 * rCount G σ k4 M) : False := by
  have hsum := sum_le_sum hM_bound
  simp only [← mul_sum, sum_add_distrib] at hsum
  have c0 := Nat.mul_le_mul_left w0 (rCount_rem_add_le C G σ k0 k0)
  have c1 := Nat.mul_le_mul_left w1 (rCount_rem_add_le C G σ k0 k1)
  have c2 := Nat.mul_le_mul_left w2 (rCount_rem_add_le C G σ k0 k2)
  have c3 := Nat.mul_le_mul_left w3 (rCount_rem_add_le C G σ k0 k3)
  have c4 := Nat.mul_le_mul_left w4 (rCount_rem_add_le C G σ k0 k4)
  have cn := Nat.mul_le_mul_left S (le_of_eq (card_rem_add C k0).symm)
  simp only [mul_add] at c0 c1 c2 c3 c4 cn
  rw [hK_card] at cn
  have hlin : (w0 + w1 + w2 + w3 + w4) * G.maxDegree = 3 * (S * G.maxDegree) := by
    rw [hwS]; ring
  have hdS : 3 * (S * G.maxDegree) + 2 * S ≤ S * Fintype.card V := by
    have h1 : 3 * G.maxDegree + 2 ≤ Fintype.card V := by omega
    have h2 := Nat.mul_le_mul_left S h1
    linarith
  linarith
lemma sum5_erase_Mw_contradiction {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj]
    (hd : 3 * (G.maxDegree + 1) ≤ Fintype.card V + 1)
    (k0 k2 k4 w : V) (hK_card : (compSet C k0).card = 5) (σ : Equiv.Perm V)
    (Mw : Finset V) (hMw_mem : Mw ∈ (univ.image (compSet C)).erase (compSet C k0))
    (hwK : 3 ≤ rCount G σ w (compSet C k0))
    (hK_A : 6 ≤ rCount G σ k0 (compSet C k0) + rCount G σ k2 (compSet C k0) +
      rCount G σ k4 (compSet C k0))
    (hMw_A : 3 * Mw.card < 2 * (rCount G σ k0 Mw + rCount G σ k2 Mw + rCount G σ k4 Mw) + 12)
    (hM_bound : ∀ M ∈ ((univ.image (compSet C)).erase (compSet C k0)).erase Mw,
      3 * M.card ≤ 3 * rCount G σ w M +
        2 * (rCount G σ k0 M + rCount G σ k2 M + rCount G σ k4 M)) : False := by
  have hsum := sum_le_sum hM_bound
  simp only [← mul_sum, mul_add, sum_add_distrib] at hsum
  have sw := sum_erase_add ((univ.image (compSet C)).erase (compSet C k0)) (fun M => rCount G σ w M) hMw_mem
  have s0 := sum_erase_add ((univ.image (compSet C)).erase (compSet C k0)) (fun M => rCount G σ k0 M) hMw_mem
  have s2 := sum_erase_add ((univ.image (compSet C)).erase (compSet C k0)) (fun M => rCount G σ k2 M) hMw_mem
  have s4 := sum_erase_add ((univ.image (compSet C)).erase (compSet C k0)) (fun M => rCount G σ k4 M) hMw_mem
  have sc := sum_erase_add ((univ.image (compSet C)).erase (compSet C k0)) (fun M => M.card) hMw_mem
  have cw := rCount_rem_add_le C G σ k0 w
  have c0 := rCount_rem_add_le C G σ k0 k0
  have c2 := rCount_rem_add_le C G σ k0 k2
  have c4 := rCount_rem_add_le C G σ k0 k4
  have cn := card_rem_add C k0
  omega
lemma k0_w_almost {V : Type} [DecidableEq V]
    (C G : SimpleGraph V) (k0 k1 k2 k3 k4 w : V)
    (hK : IsComp5 C k0 k1 k2 k3 k4) (hwK : w ∉ ({k0, k1, k2, k3, k4} : Finset V))
    (σ : Equiv.Perm V)
    (hσ : ∀ a b, C.Adj a b → ¬(a = k4 ∧ b = k0) → ¬(a = k0 ∧ b = k4) → ¬ G.Adj (σ a) (σ b))
    (π : Fin 6 → Fin 6)
    (he0 : ¬ G.Adj (σ (![k0, k1, k2, k3, k4, w] (π 0))) (σ (![k0, k1, k2, k3, k4, w] (π 1))))
    (he1 : ¬ G.Adj (σ (![k0, k1, k2, k3, k4, w] (π 1))) (σ (![k0, k1, k2, k3, k4, w] (π 2))))
    (he2 : ¬ G.Adj (σ (![k0, k1, k2, k3, k4, w] (π 2))) (σ (![k0, k1, k2, k3, k4, w] (π 3))))
    (he3 : ¬ G.Adj (σ (![k0, k1, k2, k3, k4, w] (π 3))) (σ (![k0, k1, k2, k3, k4, w] (π 4))))
    (hwnb : ∀ b, C.Adj w b → ¬ G.Adj (σ (![k0, k1, k2, k3, k4, w] (π 5))) (σ b))
    (hok : okP π = true := by rfl) :
    ∃ τ : Equiv.Perm V,
      (∀ a b, C.Adj a b → ¬(a = k4 ∧ b = k0) → ¬(a = k0 ∧ b = k4) → ¬ G.Adj (τ a) (τ b)) ∧
      (∀ i : Fin 6, τ (![k0, k1, k2, k3, k4, w] i) = σ (![k0, k1, k2, k3, k4, w] (π i))) ∧
      (∀ u, u ∉ ({k0, k1, k2, k3, k4, w} : Finset V) → τ u = σ u) := by
  let f : Fin 6 → V := ![k0, k1, k2, k3, k4, w]
  rcases hK with ⟨hk01, hk02, hk03, hk04, hk12, hk13, hk14, hk23, hk24, hk34,
                  hkn0, hkn1, hkn2, hkn3, hkn4⟩
  have hwk0 : k0 ≠ w := fun e => hwK (by simp [← e])
  have hwk1 : k1 ≠ w := fun e => hwK (by simp [← e])
  have hwk2 : k2 ≠ w := fun e => hwK (by simp [← e])
  have hwk3 : k3 ≠ w := fun e => hwK (by simp [← e])
  have hwk4 : k4 ≠ w := fun e => hwK (by simp [← e])
  have hf : Function.Injective f := by
    intro i j hij; fin_cases i <;> fin_cases j <;> dsimp [f] at hij ⊢
    all_goals first | rfl | exact absurd hij (by assumption) | exact absurd hij.symm (by assumption)
  have k_closed : ∀ u ∈ ({k0, k1, k2, k3, k4} : Finset V), ∀ b, C.Adj u b →
      b ∈ ({k0, k1, k2, k3, k4} : Finset V) := by
    intro u hu b hub
    simp only [mem_insert, mem_singleton] at hu ⊢
    rcases hu with rfl | rfl | rfl | rfl | rfl
    · rcases (hkn0 b).1 hub with rfl | rfl <;> tauto
    · rcases (hkn1 b).1 hub with rfl | rfl <;> tauto
    · rcases (hkn2 b).1 hub with rfl | rfl <;> tauto
    · rcases (hkn3 b).1 hub with rfl | rfl <;> tauto
    · rcases (hkn4 b).1 hub with rfl | rfl <;> tauto
  let ep := extPerm f hf π (invPerm π) (okP_left hok) (okP_right hok)
  have step_k : ∀ (i : Fin 6) (b' : V), i ≠ 5 → C.Adj (f i) b' → ¬(f i = k4 ∧ b' = k0) →
      ¬(f i = k0 ∧ b' = k4) → ¬ G.Adj (σ (ep (f i))) (σ (ep b')) := by
    intro i b' hi5 hb hn1' hn2'
    dsimp only [ep]; rw [extPerm_apply_f]
    fin_cases i
    · dsimp [f] at hb hn1' hn2'
      rcases (hkn0 b').1 hb with rfl | rfl
      · exact absurd ⟨rfl, rfl⟩ hn2'
      · change ¬ G.Adj _ (σ (extPerm f hf _ _ _ _ (f 1))); rw [extPerm_apply_f]; exact he0
    · dsimp [f] at hb
      rcases (hkn1 b').1 hb with rfl | rfl
      · change ¬ G.Adj _ (σ (extPerm f hf _ _ _ _ (f 0))); rw [extPerm_apply_f]; exact adj_symm_not G he0
      · change ¬ G.Adj _ (σ (extPerm f hf _ _ _ _ (f 2))); rw [extPerm_apply_f]; exact he1
    · dsimp [f] at hb
      rcases (hkn2 b').1 hb with rfl | rfl
      · change ¬ G.Adj _ (σ (extPerm f hf _ _ _ _ (f 1))); rw [extPerm_apply_f]; exact adj_symm_not G he1
      · change ¬ G.Adj _ (σ (extPerm f hf _ _ _ _ (f 3))); rw [extPerm_apply_f]; exact he2
    · dsimp [f] at hb
      rcases (hkn3 b').1 hb with rfl | rfl
      · change ¬ G.Adj _ (σ (extPerm f hf _ _ _ _ (f 2))); rw [extPerm_apply_f]; exact adj_symm_not G he2
      · change ¬ G.Adj _ (σ (extPerm f hf _ _ _ _ (f 4))); rw [extPerm_apply_f]; exact he3
    · dsimp [f] at hb hn1' hn2'
      rcases (hkn4 b').1 hb with rfl | rfl
      · change ¬ G.Adj _ (σ (extPerm f hf _ _ _ _ (f 3))); rw [extPerm_apply_f]; exact adj_symm_not G he3
      · exact absurd ⟨rfl, rfl⟩ hn1'
    · exact absurd rfl hi5
  refine ⟨ep.trans σ, ?_, ?_, ?_⟩
  · intro a b hab hn1 hn2
    simp only [Equiv.trans_apply]
    by_cases ha : ∃ i, f i = a
    · obtain ⟨i, rfl⟩ := ha
      by_cases hi5 : i = 5
      · subst hi5
        dsimp only [ep]; rw [extPerm_apply_f]
        have hb_out : ∀ j, f j ≠ b := by
          intro j hj
          have habw : C.Adj w b := hab
          fin_cases j <;> dsimp [f] at hj
          · exact hwK (k_closed k0 (by simp) w (hj ▸ habw).symm)
          · exact hwK (k_closed k1 (by simp) w (hj ▸ habw).symm)
          · exact hwK (k_closed k2 (by simp) w (hj ▸ habw).symm)
          · exact hwK (k_closed k3 (by simp) w (hj ▸ habw).symm)
          · exact hwK (k_closed k4 (by simp) w (hj ▸ habw).symm)
          · rw [← hj] at habw; exact C.loopless.irrefl w habw
        rw [extPerm_apply_out f hf _ _ _ _ hb_out]
        exact hwnb b hab
      · exact step_k i b hi5 hab hn1 hn2
    · have ha_out : ∀ i, f i ≠ a := fun i hi => ha ⟨i, hi⟩
      by_cases hb : ∃ j, f j = b
      · obtain ⟨j, rfl⟩ := hb
        by_cases hj5 : j = 5
        · subst hj5
          dsimp only [ep]
          rw [extPerm_apply_out f hf _ _ _ _ ha_out, extPerm_apply_f]
          exact adj_symm_not G (hwnb a hab.symm)
        · exact adj_symm_not G (step_k j a hj5 hab.symm
            (fun e => hn2 ⟨e.2, e.1⟩) (fun e => hn1 ⟨e.2, e.1⟩))
      · have hb_out : ∀ j, f j ≠ b := fun j hj => hb ⟨j, hj⟩
        dsimp only [ep]
        rw [extPerm_apply_out f hf _ _ _ _ ha_out, extPerm_apply_out f hf _ _ _ _ hb_out]
        exact hσ a b hab hn1 hn2
  · intro i
    simp only [Equiv.trans_apply]
    dsimp only [ep]
    change σ (extPerm f hf _ _ _ _ (f i)) = σ (f (π i))
    rw [extPerm_apply_f]
  · intro u hu
    have hu_out : ∀ i, f i ≠ u := by
      intro i hi; apply hu; subst hi
      fin_cases i <;> simp [f]
    simp only [Equiv.trans_apply]
    dsimp only [ep]
    rw [extPerm_apply_out f hf _ _ _ _ hu_out]
end SumAndRelocate
section PureDTReflection
inductive DT where
  | b : DT
  | p : ℕ → DT
  | a : ℕ → DT
  | z : ℕ → ℕ → DT
  | n : ℕ → DT → DT → DT
open DT
def wSumMask : List ℕ → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | w :: ws, i, msk => (if msk.testBit i then w else 0) + wSumMask ws (i + 1) msk
def wSumBool : List ℕ → List Bool → ℕ
  | w :: ws, d :: bs => (if d then w else 0) + wSumBool ws bs
  | _, _ => 0
lemma wSumMask_le_wSumBool : ∀ (wL : List ℕ) (ebL : List Bool) (idx msk : ℕ),
    wL.length = ebL.length →
    (∀ j, msk.testBit (idx + j) = true → ebL.getD j false = true) →
    wSumMask wL idx msk ≤ wSumBool wL ebL
  | [], [], _, _, _, _ => le_rfl
  | _ :: _, [], _, _, hlen, _ => by simp at hlen
  | [], _ :: _, _, _, hlen, _ => by simp at hlen
  | w :: ws, d :: bs, idx, msk, hlen, h => by
      simp only [wSumMask, wSumBool]
      have h0 : (if msk.testBit idx then w else 0) ≤ (if d then w else 0) := by
        by_cases hti : msk.testBit idx = true
        · have hd : d = true := by simpa using h 0 (by simpa using hti)
          simp [hti, hd]
        · simp [hti]
      refine Nat.add_le_add h0 (wSumMask_le_wSumBool ws bs (idx + 1) msk
        (Nat.succ.inj hlen) fun j hj => ?_)
      have hj' : msk.testBit (idx + (j + 1)) = true := by
        rwa [show idx + (j + 1) = idx + 1 + j by omega]
      simpa using h (j + 1) hj'
def rowOf : ℕ → ℕ → ℕ
  | 1, 0 => 5
  | 2, 0 => 5
  | 2, 2 => 0
  | 3, 0 => 5
  | 3, 4 => 0
  | _, i => i
def knownNonAdjDir (L0 m e0_mask : ℕ) (has_nw1 : Bool) (f_msk r_idx u v : ℕ) : Bool :=
  if u < L0 && v < L0 then
    let ru := rowOf r_idx u
    let rv := rowOf r_idx v
    let lo := min ru rv
    let hi := max ru rv
    if lo == hi then true
    else if hi == 5 then (lo == 1) && has_nw1
    else (hi == lo + 1) || !(e0_mask.testBit (lo * 5 + hi))
  else if L0 ≤ u && L0 ≤ v then
    let j1 := u - L0
    let j2 := v - L0
    (j2 == j1 + 1) || (j1 == 0 && j2 == m - 1)
  else if u < L0 && L0 ≤ v then
    let ru := rowOf r_idx u
    let j := v - L0
    f_msk.testBit (ru * m + j)
  else false
def knownNonAdj (L0 m e0_mask : ℕ) (has_nw1 : Bool) (f_msk r_idx u v : ℕ) : Bool :=
  if u == v then true
  else if u < v then knownNonAdjDir L0 m e0_mask has_nw1 f_msk r_idx u v
  else knownNonAdjDir L0 m e0_mask has_nw1 f_msk r_idx v u
lemma knownNonAdj_symm (L0 m e0_mask : ℕ) (has_nw1 : Bool) (f_msk r_idx u v : ℕ) :
    knownNonAdj L0 m e0_mask has_nw1 f_msk r_idx u v =
    knownNonAdj L0 m e0_mask has_nw1 f_msk r_idx v u := by
  unfold knownNonAdj
  by_cases huv : u = v
  · subst huv; simp
  · have hvu : (v == u) = false := beq_false_of_ne (Ne.symm huv)
    have huv' : (u == v) = false := beq_false_of_ne huv
    rw [huv', hvu]
    by_cases hlt : u < v
    · have hvlt : ¬ v < u := by omega
      simp [hlt, hvlt]
    · have hvlt : v < u := by omega
      simp [hlt, hvlt]
def nib (c i : ℕ) : ℕ := (c >>> (4 * i)) &&& 15
def invCode (s pc : ℕ) : ℕ :=
  (List.range s).foldl (fun acc i => acc ||| (i <<< (4 * nib pc i))) 0
def okPermCode (s pc ic : ℕ) : Bool :=
  (List.range s).all (fun i =>
    let p := nib pc i
    let q := nib ic i
    decide (p < s) && decide (q < s) && (nib ic p == i) && (nib pc q == i))
def permOfCode {s pc ic : ℕ} (hok : okPermCode s pc ic = true) : Fin s → Fin s :=
  fun i =>
    have hi := (List.all_eq_true.1 hok) i.1 (List.mem_range.2 i.2)
    ⟨nib pc i.1, by simp only [Bool.and_eq_true, decide_eq_true_eq] at hi; exact hi.1.1.1⟩
def invOfCode {s pc ic : ℕ} (hok : okPermCode s pc ic = true) : Fin s → Fin s :=
  fun i =>
    have hi := (List.all_eq_true.1 hok) i.1 (List.mem_range.2 i.2)
    ⟨nib ic i.1, by simp only [Bool.and_eq_true, decide_eq_true_eq] at hi; exact hi.1.1.2⟩
lemma okPermCode_left {s pc ic : ℕ} (hok : okPermCode s pc ic = true) (i : Fin s) :
    invOfCode hok (permOfCode hok i) = i := by
  have hi := (List.all_eq_true.1 hok) i.1 (List.mem_range.2 i.2)
  simp only [Bool.and_eq_true, beq_iff_eq] at hi
  exact Fin.ext hi.1.2
lemma okPermCode_right {s pc ic : ℕ} (hok : okPermCode s pc ic = true) (i : Fin s) :
    permOfCode hok (invOfCode hok i) = i := by
  have hi := (List.all_eq_true.1 hok) i.1 (List.mem_range.2 i.2)
  simp only [Bool.and_eq_true, beq_iff_eq] at hi
  exact Fin.ext hi.2
def cEdgesK (L0 : ℕ) : List (ℕ × ℕ) :=
  (List.range L0).map (fun i => (i, (i + 1) % L0))
def cEdgesKm (L0 : ℕ) : List (ℕ × ℕ) :=
  (List.range (L0 - 1)).map (fun i => (i, i + 1))
def cEdgesM (L0 m : ℕ) : List (ℕ × ℕ) :=
  if m ≤ 1 then []
  else (List.range m).map (fun j => (L0 + j, L0 + (j + 1) % m))
def hasUndirEdge (es : List (ℕ × ℕ)) (u v : ℕ) : Bool :=
  es.any (fun e => (e.1 == u && e.2 == v) || (e.1 == v && e.2 == u))
lemma hasUndirEdge_alm_of_pack {L0 m u v : ℕ} (hL0 : 4 ≤ L0)
    (hn1 : ¬(u = L0 - 1 ∧ v = 0)) (hn2 : ¬(u = 0 ∧ v = L0 - 1))
    (hp : hasUndirEdge (cEdgesK L0 ++ cEdgesM L0 m) u v = true) :
    hasUndirEdge (cEdgesKm L0 ++ cEdgesM L0 m) u v = true := by
  unfold hasUndirEdge at hp ⊢
  rw [List.any_append, Bool.or_eq_true] at hp ⊢
  rcases hp with hk | hm
  · left
    obtain ⟨e, he, heq⟩ := List.any_eq_true.1 hk
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 he
    rw [List.mem_range] at hi
    have hi_lt : i < L0 - 1 := by
      by_contra hge
      have hi_eq : i = L0 - 1 := by omega
      subst hi_eq
      have hmod : (L0 - 1 + 1) % L0 = 0 := by rw [show L0 - 1 + 1 = L0 by omega, Nat.mod_self]
      rw [hmod] at heq
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at heq
      rcases heq with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact hn1 ⟨e1.symm, e2.symm⟩
      · exact hn2 ⟨e2.symm, e1.symm⟩
    have hmod : (i + 1) % L0 = i + 1 := Nat.mod_eq_of_lt (by omega)
    rw [hmod] at heq
    exact List.any_eq_true.2 ⟨(i, i + 1), List.mem_map.2 ⟨i, List.mem_range.2 hi_lt, rfl⟩, heq⟩
  · exact Or.inr hm
def evalPackLeaf (L0 m e0_mask : ℕ) (has_nw1 : Bool) (edgesP : List (ℕ × ℕ)) (ptab : List ℕ)
    (code f_msk : ℕ) : Bool :=
  let r_idx := code &&& 3
  let pc := ptab.getD (code >>> 2) 0
  let ic := invCode (L0 + m) pc
  (r_idx == 0 || (has_nw1 && (r_idx == 1 || r_idx == 2 || r_idx == 3))) &&
  okPermCode (L0 + m) pc ic &&
  edgesP.all (fun e =>
    knownNonAdj L0 m e0_mask has_nw1 f_msk r_idx (nib pc e.1) (nib pc e.2))
def evalDTCore (L0 m e0_mask sc0 : ℕ) (has_nw1 has_z : Bool)
    (edgesP edgesA : List (ℕ × ℕ)) (ptab wL : List ℕ) (tgt : ℕ) :
    DT → ℕ → ℕ → Bool
  | .b, t_msk, _ => decide (tgt ≤ wSumMask wL 0 t_msk)
  | .p code, _, f_msk => evalPackLeaf L0 m e0_mask has_nw1 edgesP ptab code f_msk
  | .a p_idx, _, f_msk =>
      let pc := ptab.getD p_idx 0
      let ic := invCode (L0 + m) pc
      (L0 == 5) && decide (0 < sc0) &&
      okPermCode (L0 + m) pc ic &&
      edgesA.all (fun e =>
        knownNonAdj L0 m e0_mask has_nw1 f_msk 0 (nib pc e.1) (nib pc e.2)) &&
      (let kn (ia ib : ℕ) : ℕ :=
         if knownNonAdj L0 m e0_mask has_nw1 f_msk 0 (nib pc ia) (nib pc ib) then 0 else 1
       let u02 := kn 0 2; let u03 := kn 0 3; let u04 := kn 0 4
       let u13 := kn 1 3; let u14 := kn 1 4; let u24 := kn 2 4
       let utri := if u02 + u04 + u24 == 3 then 1 else 0
       decide (2 * (u02 + u03 + u04 + u13 + u14 + u24) + utri < sc0))
  | .z j b_row, _, f_msk =>
      has_z && (L0 == 5) && (b_row == 1 || b_row == 3) && decide (j < m) &&
      f_msk.testBit (b_row * m + j) &&
      (if m ≤ 1 then true
       else
         let jp := (j + m - 1) % m
         let jn := (j + 1) % m
         f_msk.testBit (0 * m + jp) && f_msk.testBit (2 * m + jp) && f_msk.testBit (4 * m + jp) &&
         f_msk.testBit (0 * m + jn) && f_msk.testBit (2 * m + jn) && f_msk.testBit (4 * m + jn))
  | .n bit l r, t_msk, f_msk =>
      evalDTCore L0 m e0_mask sc0 has_nw1 has_z edgesP edgesA ptab wL tgt l (t_msk ||| (1 <<< bit)) f_msk &&
      evalDTCore L0 m e0_mask sc0 has_nw1 has_z edgesP edgesA ptab wL tgt r t_msk (f_msk ||| (1 <<< bit))
def evalDT (L0 m e0_mask sc0 : ℕ) (has_nw1 has_z : Bool) (ptab wL : List ℕ) (tgt : ℕ)
    (tree : DT) (t_msk f_msk : ℕ) : Bool :=
  evalDTCore L0 m e0_mask sc0 has_nw1 has_z
    (cEdgesK L0 ++ cEdgesM L0 m) (cEdgesKm L0 ++ cEdgesM L0 m) ptab wL tgt tree t_msk f_msk
structure ReflCtx (V : Type) [Fintype V] [DecidableEq V] where
  C : SimpleGraph V
  G : SimpleGraph V
  decG : DecidableRel G.Adj
  L0 : ℕ
  m : ℕ
  e0_mask : ℕ
  sc0 : ℕ
  has_nw1 : Bool
  has_z : Bool
  ebL : List Bool
  hL0_pos : 4 ≤ L0
  hm_pos : 1 ≤ m
  f : Fin (L0 + m) → V
  hf : Function.Injective f
  kV : ℕ → V
  hkV_eq : ∀ i (hi : i < L0), f ⟨i, by omega⟩ = kV i
  σ : Equiv.Perm V
  σr : ℕ → Equiv.Perm V
  hnp : ¬ Packs C G
  hrow_spec : ∀ r i, (r = 0 ∨ (has_nw1 = true ∧ (r = 1 ∨ r = 2 ∨ r = 3))) → i < L0 →
    rowOf r i < L0 ∨ (has_nw1 = true ∧ rowOf r i = 5)
  hσr0 : ∀ x, σr 0 x = σ x
  hσr_alm : ∀ r, (r = 0 ∨ (has_nw1 = true ∧ (r = 1 ∨ r = 2 ∨ r = 3))) →
    ∀ a b, C.Adj a b →
      ¬(a = f ⟨L0 - 1, by omega⟩ ∧ b = f ⟨0, by omega⟩) →
      ¬(a = f ⟨0, by omega⟩ ∧ b = f ⟨L0 - 1, by omega⟩) →
      ¬ G.Adj (σr r a) (σr r b)
  hσr_k : ∀ r, (r = 0 ∨ (has_nw1 = true ∧ (r = 1 ∨ r = 2 ∨ r = 3))) →
    ∀ i (hi : i < L0), σr r (f ⟨i, by omega⟩) = σ (kV (rowOf r i))
  hσr_m : ∀ r, (r = 0 ∨ (has_nw1 = true ∧ (r = 1 ∨ r = 2 ∨ r = 3))) →
    ∀ j (hj : j < m), σr r (f ⟨L0 + j, by omega⟩) = σ (f ⟨L0 + j, by omega⟩)
  hk_path : ∀ i, i + 1 < L0 → ¬ G.Adj (σ (kV i)) (σ (kV (i + 1)))
  hk_e0 : ∀ i j, i < j → j < L0 → j ≠ i + 1 → e0_mask.testBit (i * 5 + j) = false →
    ¬ G.Adj (σ (kV i)) (σ (kV j))
  hnw1 : has_nw1 = true → ¬ G.Adj (σ (kV 1)) (σ (kV 5))
  hm_edge : ∀ j1 j2 (hj12 : j1 < j2) (hj2 : j2 < m),
    (j2 = j1 + 1 ∨ (j1 = 0 ∧ j2 = m - 1)) →
    ¬ G.Adj (σ (f ⟨L0 + j1, by omega⟩)) (σ (f ⟨L0 + j2, by omega⟩))
  heb : ∀ ru j (hj : j < m),
    (ru < L0 ∨ (has_nw1 = true ∧ ru = 5)) →
    ebL.getD (ru * m + j) false = @decide (G.Adj (σ (kV ru)) (σ (f ⟨L0 + j, by omega⟩))) (decG _ _)
  hcl_pack : ∀ idx1 : Fin (L0 + m), ∀ b, C.Adj (f idx1) b →
    ∃ idx2 : Fin (L0 + m), f idx2 = b ∧
      hasUndirEdge (cEdgesK L0 ++ cEdgesM L0 m) idx1.1 idx2.1 = true
  halm_min : L0 = 5 → 0 < sc0 →
    sc0 ≤ @kScore V G decG (σ (kV 0)) (σ (kV 1)) (σ (kV 2)) (σ (kV 3)) (σ (kV 4)) ∧
    ∀ τ : Equiv.Perm V,
      (∀ a b, C.Adj a b →
        ¬(a = kV 4 ∧ b = kV 0) →
        ¬(a = kV 0 ∧ b = kV 4) →
        ¬ G.Adj (τ a) (τ b)) →
      @kScore V G decG (σ (kV 0)) (σ (kV 1)) (σ (kV 2)) (σ (kV 3)) (σ (kV 4)) ≤
      @kScore V G decG (τ (kV 0)) (τ (kV 1)) (τ (kV 2)) (τ (kV 3)) (τ (kV 4))
  hz_prop : has_z = true → L0 = 5 → ∀ j (hj : j < m),
    (m ≤ 1 → ∀ b, ¬ C.Adj (f ⟨L0 + j, by omega⟩) b) ∧
    (¬ m ≤ 1 → ∀ b, C.Adj (f ⟨L0 + j, by omega⟩) b ↔
      b = f ⟨L0 + (j + m - 1) % m, by have := Nat.mod_lt (j + m - 1) hm_pos; omega⟩ ∨
      b = f ⟨L0 + (j + 1) % m, by have := Nat.mod_lt (j + 1) hm_pos; omega⟩) ∧
    ((G.Adj (σ (kV 1)) (σ (f ⟨L0 + j, by omega⟩)) ∧
      G.Adj (σ (kV 3)) (σ (f ⟨L0 + j, by omega⟩))) ∨
     ∃ b, C.Adj (f ⟨L0 + j, by omega⟩) b ∧
       (G.Adj (σ (kV 0)) (σ b) ∨ G.Adj (σ (kV 2)) (σ b) ∨ G.Adj (σ (kV 4)) (σ b)))
lemma knownNonAdjDir_sound {V : Type} [Fintype V] [DecidableEq V] (ctx : ReflCtx V)
    {f_msk r_idx : ℕ}
    (hf_msk : ∀ i, f_msk.testBit i = true → ctx.ebL.getD i false = false)
    (hr : r_idx = 0 ∨ (ctx.has_nw1 = true ∧ (r_idx = 1 ∨ r_idx = 2 ∨ r_idx = 3)))
    {u v : ℕ} (huv : u < v) (hv : v < ctx.L0 + ctx.m)
    (hkn : knownNonAdjDir ctx.L0 ctx.m ctx.e0_mask ctx.has_nw1 f_msk r_idx u v = true) :
    ¬ ctx.G.Adj (ctx.σr r_idx (ctx.f ⟨u, by omega⟩)) (ctx.σr r_idx (ctx.f ⟨v, hv⟩)) := by
  unfold knownNonAdjDir at hkn
  by_cases huvL : u < ctx.L0 ∧ v < ctx.L0
  · have huL := huvL.1; have hvL := huvL.2
    have hcond : (decide (u < ctx.L0) && decide (v < ctx.L0)) = true := by simp [huL, hvL]
    simp only [hcond, ↓reduceIte] at hkn
    rw [ctx.hσr_k r_idx hr u huL, ctx.hσr_k r_idx hr v hvL]
    set ru := rowOf r_idx u
    set rv := rowOf r_idx v
    have hru_sp := ctx.hrow_spec r_idx u hr huL
    have hrv_sp := ctx.hrow_spec r_idx v hr hvL
    set lo := min ru rv
    set hi := max ru rv
    have h_ord : (lo = ru ∧ hi = rv) ∨ (lo = rv ∧ hi = ru) := by
      by_cases hle : ru ≤ rv
      · exact Or.inl ⟨Nat.min_eq_left hle, Nat.max_eq_right hle⟩
      · have hle' : rv ≤ ru := by omega
        exact Or.inr ⟨Nat.min_eq_right hle', Nat.max_eq_left hle'⟩
    suffices hlo_hi : ¬ ctx.G.Adj (ctx.σ (ctx.kV lo)) (ctx.σ (ctx.kV hi)) by
      rcases h_ord with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rwa [← e1, ← e2]
      · rw [← e1, ← e2]; exact adj_symm_not ctx.G hlo_hi
    have hle_lh : lo ≤ hi := by dsimp [lo, hi]; omega
    by_cases heq_lh : lo = hi
    · rw [heq_lh]; exact ctx.G.loopless.irrefl _
    · have hbeq_lh : (lo == hi) = false := beq_false_of_ne heq_lh
      rw [hbeq_lh] at hkn; simp only [Bool.false_eq_true, ↓reduceIte] at hkn
      have hlt_lh : lo < hi := by omega
      have hhi_sp : hi < ctx.L0 ∨ (ctx.has_nw1 = true ∧ hi = 5) := by
        rcases h_ord with ⟨_, e2⟩ | ⟨_, e2⟩ <;> rw [e2] <;> assumption
      by_cases hhi5 : hi = 5
      · rw [hhi5] at hkn ⊢
        simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hkn
        rw [hkn.1]; exact ctx.hnw1 hkn.2
      · have hbeq5 : (hi == 5) = false := beq_false_of_ne hhi5
        rw [hbeq5] at hkn; simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true,
          beq_iff_eq, Bool.not_eq_true'] at hkn
        have hhiL : hi < ctx.L0 := by rcases hhi_sp with h | ⟨_, h⟩; exact h; exact absurd h hhi5
        by_cases hsucc : hi = lo + 1
        · rw [hsucc]; exact ctx.hk_path lo (by omega)
        · rcases hkn with h | h
          · exact absurd h hsucc
          · exact ctx.hk_e0 lo hi hlt_lh hhiL hsucc h
  · have hcond1 : (decide (u < ctx.L0) && decide (v < ctx.L0)) = false := by
      rw [Bool.and_eq_false_iff]; by_cases h1 : u < ctx.L0
      · right; simp [show ¬ v < ctx.L0 by omega]
      · left; simp [h1]
    rw [hcond1] at hkn; simp only [Bool.false_eq_true, ↓reduceIte] at hkn
    by_cases huvM : ctx.L0 ≤ u ∧ ctx.L0 ≤ v
    · have hcond2 : (decide (ctx.L0 ≤ u) && decide (ctx.L0 ≤ v)) = true := by simp [huvM.1, huvM.2]
      rw [hcond2] at hkn; simp only [↓reduceIte, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hkn
      have hj1 : u - ctx.L0 < ctx.m := by omega
      have hj2 : v - ctx.L0 < ctx.m := by omega
      have eu : (⟨u, by omega⟩ : Fin (ctx.L0 + ctx.m)) = ⟨ctx.L0 + (u - ctx.L0), by omega⟩ :=
        Fin.ext (by dsimp; omega)
      have ev : (⟨v, hv⟩ : Fin (ctx.L0 + ctx.m)) = ⟨ctx.L0 + (v - ctx.L0), by omega⟩ :=
        Fin.ext (by dsimp; omega)
      rw [eu, ev, ctx.hσr_m r_idx hr _ hj1, ctx.hσr_m r_idx hr _ hj2]
      exact ctx.hm_edge (u - ctx.L0) (v - ctx.L0) (by omega) hj2 hkn
    · have hcond2 : (decide (ctx.L0 ≤ u) && decide (ctx.L0 ≤ v)) = false := by
        rw [Bool.and_eq_false_iff]; left; simp [show ¬ ctx.L0 ≤ u by omega]
      rw [hcond2] at hkn; simp only [Bool.false_eq_true, ↓reduceIte] at hkn
      have huL : u < ctx.L0 := by omega
      have hvM : ctx.L0 ≤ v := by omega
      have hcond3 : (decide (u < ctx.L0) && decide (ctx.L0 ≤ v)) = true := by simp [huL, hvM]
      rw [hcond3] at hkn; simp only [↓reduceIte] at hkn
      have hj : v - ctx.L0 < ctx.m := by omega
      have ev : (⟨v, hv⟩ : Fin (ctx.L0 + ctx.m)) = ⟨ctx.L0 + (v - ctx.L0), by omega⟩ :=
        Fin.ext (by dsimp; omega)
      rw [ev, ctx.hσr_k r_idx hr u huL, ctx.hσr_m r_idx hr _ hj]
      have heb_false := hf_msk (rowOf r_idx u * ctx.m + (v - ctx.L0)) hkn
      rw [ctx.heb (rowOf r_idx u) (v - ctx.L0) hj (ctx.hrow_spec r_idx u hr huL)] at heb_false
      exact @of_decide_eq_false _ (ctx.decG _ _) heb_false
lemma knownNonAdj_sound {V : Type} [Fintype V] [DecidableEq V] (ctx : ReflCtx V)
    {f_msk r_idx : ℕ}
    (hf_msk : ∀ i, f_msk.testBit i = true → ctx.ebL.getD i false = false)
    (hr : r_idx = 0 ∨ (ctx.has_nw1 = true ∧ (r_idx = 1 ∨ r_idx = 2 ∨ r_idx = 3)))
    (u v : Fin (ctx.L0 + ctx.m))
    (hkn : knownNonAdj ctx.L0 ctx.m ctx.e0_mask ctx.has_nw1 f_msk r_idx u.1 v.1 = true) :
    ¬ ctx.G.Adj (ctx.σr r_idx (ctx.f u)) (ctx.σr r_idx (ctx.f v)) := by
  unfold knownNonAdj at hkn
  by_cases heq : u.1 = v.1
  · have huv : u = v := Fin.ext heq; subst huv; exact ctx.G.loopless.irrefl _
  · have hbeq : (u.1 == v.1) = false := beq_false_of_ne heq
    rw [hbeq] at hkn; simp only [Bool.false_eq_true, ↓reduceIte] at hkn
    by_cases hlt : u.1 < v.1
    · simp only [hlt, ↓reduceIte] at hkn
      exact knownNonAdjDir_sound ctx hf_msk hr hlt v.2 hkn
    · simp only [hlt, ↓reduceIte] at hkn
      have hvlt : v.1 < u.1 := by omega
      exact adj_symm_not ctx.G (knownNonAdjDir_sound ctx hf_msk hr hvlt u.2 hkn)
lemma known_of_hasUndirEdge {es : List (ℕ × ℕ)} {L0 m e0_mask : ℕ} {has_nw1 : Bool}
    {f_msk r_idx pc u v : ℕ}
    (hall : ∀ x ∈ es, knownNonAdj L0 m e0_mask has_nw1 f_msk r_idx (nib pc x.1) (nib pc x.2) = true)
    (hmem : hasUndirEdge es u v = true) :
    knownNonAdj L0 m e0_mask has_nw1 f_msk r_idx (nib pc u) (nib pc v) = true := by
  unfold hasUndirEdge at hmem
  obtain ⟨e, he, h_eq⟩ := List.any_eq_true.1 hmem
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h_eq
  rcases h_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hall e he
  · rw [knownNonAdj_symm]; exact hall e he
lemma evalPackLeaf_false {V : Type} [Fintype V] [DecidableEq V] (ctx : ReflCtx V)
    {ptab : List ℕ} {code f_msk : ℕ}
    (hf : ∀ i, f_msk.testBit i = true → ctx.ebL.getD i false = false)
    (hev : evalPackLeaf ctx.L0 ctx.m ctx.e0_mask ctx.has_nw1
      (cEdgesK ctx.L0 ++ cEdgesM ctx.L0 ctx.m) ptab code f_msk = true) : False := by
  simp only [evalPackLeaf, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true] at hev
  rcases hev with ⟨⟨hr_raw, hok⟩, hall⟩
  have hr : (code &&& 3) = 0 ∨ (ctx.has_nw1 = true ∧ ((code &&& 3) = 1 ∨ (code &&& 3) = 2 ∨ (code &&& 3) = 3)) := by tauto
  let π := permOfCode hok
  let π_inv := invOfCode hok
  have hcl_simple : ∀ i b, ctx.C.Adj (ctx.f i) b → ∃ k, ctx.f k = b := by
    intro i b hab; obtain ⟨k, hk, _⟩ := ctx.hcl_pack i b hab; exact ⟨k, hk⟩
  exact ctx.hnp (local_pack_gen ctx.C ctx.G (ctx.f ⟨ctx.L0 - 1, by have := ctx.hL0_pos; omega⟩)
    (ctx.f ⟨0, by have := ctx.hL0_pos; omega⟩) (ctx.σr (code &&& 3)) (ctx.hσr_alm (code &&& 3) hr)
    ctx.f ctx.hf ⟨⟨ctx.L0 - 1, by have := ctx.hL0_pos; omega⟩, rfl⟩
    ⟨⟨0, by have := ctx.hL0_pos; omega⟩, rfl⟩
    hcl_simple π π_inv (okPermCode_left hok) (okPermCode_right hok)
    (fun i j hij => by
      obtain ⟨j', hj', hmem⟩ := ctx.hcl_pack i (ctx.f j) hij
      have rj : j' = j := ctx.hf hj'; subst j'
      exact knownNonAdj_sound ctx hf hr (π i) (π j) (known_of_hasUndirEdge hall hmem)))
lemma b01_tri_le_each {p q r : Prop} [Decidable p] [Decidable q] [Decidable r]
    [Decidable (p ∧ q ∧ r)] :
    b01 (p ∧ q ∧ r) ≤ b01 p ∧ b01 (p ∧ q ∧ r) ≤ b01 q ∧ b01 (p ∧ q ∧ r) ≤ b01 r := by
  unfold b01; split_ifs <;> tauto
lemma testBit_one_shiftLeft (b i : ℕ) : (1 <<< b).testBit i = (b == i) := by
  rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
  by_cases h : b = i <;> simp [h]
lemma evalDTCore_sound {V : Type} [Fintype V] [DecidableEq V] (ctx : ReflCtx V)
    (ptab wL : List ℕ) (tgt : ℕ) (hlen : wL.length = ctx.ebL.length) (tree : DT) :
    ∀ t_msk f_msk : ℕ,
      (∀ i, t_msk.testBit i = true → ctx.ebL.getD i false = true) →
      (∀ i, f_msk.testBit i = true → ctx.ebL.getD i false = false) →
      evalDTCore ctx.L0 ctx.m ctx.e0_mask ctx.sc0 ctx.has_nw1 ctx.has_z
        (cEdgesK ctx.L0 ++ cEdgesM ctx.L0 ctx.m) (cEdgesKm ctx.L0 ++ cEdgesM ctx.L0 ctx.m)
        ptab wL tgt tree t_msk f_msk = true →
      tgt ≤ wSumBool wL ctx.ebL := by
  let _ : DecidableRel ctx.G.Adj := ctx.decG
  induction tree with
  | b =>
    intro t_msk _ ht _ hev
    simp only [evalDTCore, decide_eq_true_eq] at hev
    exact le_trans hev (wSumMask_le_wSumBool wL ctx.ebL 0 t_msk hlen (by simpa using ht))
  | p code =>
    intro _ f_msk _ hf hev
    exact False.elim (evalPackLeaf_false ctx hf hev)
  | a p_idx =>
    intro _ f_msk _ hf hev
    simp only [evalDTCore, Bool.and_eq_true, List.all_eq_true] at hev
    rcases hev with ⟨⟨⟨⟨hL0_b, hsc_b⟩, hok⟩, hall⟩, hsc_lt_b⟩
    have hL0_5 : ctx.L0 = 5 := beq_iff_eq.1 hL0_b
    have hsc_pos : 0 < ctx.sc0 := of_decide_eq_true hsc_b
    have hsc_lt := of_decide_eq_true hsc_lt_b
    let π := permOfCode hok
    let π_inv := invOfCode hok
    have hcl_simple : ∀ i b, ctx.C.Adj (ctx.f i) b → ∃ k, ctx.f k = b := by
      intro i b hab; obtain ⟨k, hk, _⟩ := ctx.hcl_pack i b hab; exact ⟨k, hk⟩
    obtain ⟨hτ, hτf⟩ := local_almost_gen ctx.C ctx.G
      (ctx.f ⟨ctx.L0 - 1, by omega⟩) (ctx.f ⟨0, by omega⟩)
      ⟨ctx.L0 - 1, by omega⟩ ⟨0, by omega⟩
      (ctx.σr 0) (ctx.hσr_alm 0 (Or.inl rfl)) ctx.f ctx.hf rfl rfl hcl_simple
      π π_inv (okPermCode_left hok) (okPermCode_right hok)
      (fun i j hij hn1 hn2 => by
        obtain ⟨j', hj', hmem⟩ := ctx.hcl_pack i (ctx.f j) hij
        have rj : j' = j := ctx.hf hj'; subst j'
        have hmem_alm := hasUndirEdge_alm_of_pack ctx.hL0_pos
          (fun ⟨e1, e2⟩ => hn1 ⟨Fin.ext e1, Fin.ext e2⟩)
          (fun ⟨e1, e2⟩ => hn2 ⟨Fin.ext e1, Fin.ext e2⟩) hmem
        exact knownNonAdj_sound ctx hf (Or.inl rfl) (π i) (π j) (known_of_hasUndirEdge hall hmem_alm))
    obtain ⟨hsc0_ge, hmin⟩ := ctx.halm_min hL0_5 hsc_pos
    have h0L : 0 < ctx.L0 := by omega
    have h1L : 1 < ctx.L0 := by omega
    have h2L : 2 < ctx.L0 := by omega
    have h3L : 3 < ctx.L0 := by omega
    have h4L : 4 < ctx.L0 := by omega
    have h4_eq : (⟨ctx.L0 - 1, by omega⟩ : Fin (ctx.L0 + ctx.m)) = ⟨4, by omega⟩ :=
      Fin.ext (by dsimp; omega)
    have hτ' : ∀ a b, ctx.C.Adj a b → ¬(a = ctx.kV 4 ∧ b = ctx.kV 0) →
        ¬(a = ctx.kV 0 ∧ b = ctx.kV 4) →
        ¬ ctx.G.Adj ((extPerm ctx.f ctx.hf π π_inv (okPermCode_left hok) (okPermCode_right hok)).trans (ctx.σr 0) a)
          ((extPerm ctx.f ctx.hf π π_inv (okPermCode_left hok) (okPermCode_right hok)).trans (ctx.σr 0) b) := by
      rw [← ctx.hkV_eq 4 h4L, ← ctx.hkV_eq 0 h0L, ← h4_eq]
      exact hτ
    have htot := le_trans hsc0_ge (hmin _ hτ')
    have ub_pair : ∀ (ia ib : ℕ) (hia : ia < ctx.L0 + ctx.m) (hib : ib < ctx.L0 + ctx.m),
        b01 (ctx.G.Adj (ctx.σ (ctx.f (π ⟨ia, hia⟩))) (ctx.σ (ctx.f (π ⟨ib, hib⟩)))) ≤
          if knownNonAdj ctx.L0 ctx.m ctx.e0_mask ctx.has_nw1 f_msk 0
               (nib (ptab.getD p_idx 0) ia) (nib (ptab.getD p_idx 0) ib) then 0 else 1 := by
      intro ia ib hia hib
      by_cases hkn : knownNonAdj ctx.L0 ctx.m ctx.e0_mask ctx.has_nw1 f_msk 0 (nib (ptab.getD p_idx 0) ia) (nib (ptab.getD p_idx 0) ib) = true
      · rw [if_pos hkn]
        have hn := knownNonAdj_sound ctx hf (Or.inl rfl) (π ⟨ia, hia⟩) (π ⟨ib, hib⟩) hkn
        rw [ctx.hσr0, ctx.hσr0] at hn
        exact b01_zero_le hn
      · simp only [Bool.not_eq_true] at hkn; rw [hkn]; simp only [Bool.false_eq_true, ↓reduceIte]
        exact b01_le_one _
    have h0 : 0 < ctx.L0 + ctx.m := by omega
    have h1 : 1 < ctx.L0 + ctx.m := by omega
    have h2 : 2 < ctx.L0 + ctx.m := by omega
    have h3 : 3 < ctx.L0 + ctx.m := by omega
    have h4 : 4 < ctx.L0 + ctx.m := by omega
    rw [← ctx.hkV_eq 0 h0L, ← ctx.hkV_eq 1 h1L, ← ctx.hkV_eq 2 h2L, ← ctx.hkV_eq 3 h3L, ← ctx.hkV_eq 4 h4L] at htot
    have e0 : _ = ctx.σ (ctx.f (π ⟨0, h0⟩)) := (hτf ⟨0, h0⟩).trans (ctx.hσr0 _)
    have e1 : _ = ctx.σ (ctx.f (π ⟨1, h1⟩)) := (hτf ⟨1, h1⟩).trans (ctx.hσr0 _)
    have e2 : _ = ctx.σ (ctx.f (π ⟨2, h2⟩)) := (hτf ⟨2, h2⟩).trans (ctx.hσr0 _)
    have e3 : _ = ctx.σ (ctx.f (π ⟨3, h3⟩)) := (hτf ⟨3, h3⟩).trans (ctx.hσr0 _)
    have e4 : _ = ctx.σ (ctx.f (π ⟨4, h4⟩)) := (hτf ⟨4, h4⟩).trans (ctx.hσr0 _)
    rw [e0, e1, e2, e3, e4] at htot
    have u02 := ub_pair 0 2 h0 h2
    have u03 := ub_pair 0 3 h0 h3
    have u04 := ub_pair 0 4 h0 h4
    have u13 := ub_pair 1 3 h1 h3
    have u14 := ub_pair 1 4 h1 h4
    have u24 := ub_pair 2 4 h2 h4
    have ⟨t1, t2, t3⟩ := b01_tri_le_each
      (p := ctx.G.Adj (ctx.σ (ctx.f (π ⟨0, h0⟩))) (ctx.σ (ctx.f (π ⟨2, h2⟩))))
      (q := ctx.G.Adj (ctx.σ (ctx.f (π ⟨0, h0⟩))) (ctx.σ (ctx.f (π ⟨4, h4⟩))))
      (r := ctx.G.Adj (ctx.σ (ctx.f (π ⟨2, h2⟩))) (ctx.σ (ctx.f (π ⟨4, h4⟩))))
    have b02_le1 : (if knownNonAdj ctx.L0 ctx.m ctx.e0_mask ctx.has_nw1 f_msk 0 (nib (ptab.getD p_idx 0) 0) (nib (ptab.getD p_idx 0) 2) then 0 else 1) ≤ 1 := by split_ifs <;> omega
    have b04_le1 : (if knownNonAdj ctx.L0 ctx.m ctx.e0_mask ctx.has_nw1 f_msk 0 (nib (ptab.getD p_idx 0) 0) (nib (ptab.getD p_idx 0) 4) then 0 else 1) ≤ 1 := by split_ifs <;> omega
    have b24_le1 : (if knownNonAdj ctx.L0 ctx.m ctx.e0_mask ctx.has_nw1 f_msk 0 (nib (ptab.getD p_idx 0) 2) (nib (ptab.getD p_idx 0) 4) then 0 else 1) ≤ 1 := by split_ifs <;> omega
    unfold kScore at htot
    by_cases hsum3 : (if knownNonAdj ctx.L0 ctx.m ctx.e0_mask ctx.has_nw1 f_msk 0 (nib (ptab.getD p_idx 0) 0) (nib (ptab.getD p_idx 0) 2) then 0 else 1) +
        (if knownNonAdj ctx.L0 ctx.m ctx.e0_mask ctx.has_nw1 f_msk 0 (nib (ptab.getD p_idx 0) 0) (nib (ptab.getD p_idx 0) 4) then 0 else 1) +
        (if knownNonAdj ctx.L0 ctx.m ctx.e0_mask ctx.has_nw1 f_msk 0 (nib (ptab.getD p_idx 0) 2) (nib (ptab.getD p_idx 0) 4) then 0 else 1) = 3
    · have hbeq3 : ((if knownNonAdj ctx.L0 ctx.m ctx.e0_mask ctx.has_nw1 f_msk 0 (nib (ptab.getD p_idx 0) 0) (nib (ptab.getD p_idx 0) 2) then 0 else 1) +
          (if knownNonAdj ctx.L0 ctx.m ctx.e0_mask ctx.has_nw1 f_msk 0 (nib (ptab.getD p_idx 0) 0) (nib (ptab.getD p_idx 0) 4) then 0 else 1) +
          (if knownNonAdj ctx.L0 ctx.m ctx.e0_mask ctx.has_nw1 f_msk 0 (nib (ptab.getD p_idx 0) 2) (nib (ptab.getD p_idx 0) 4) then 0 else 1) == 3) = true := beq_iff_eq.2 hsum3
      rw [hbeq3] at hsc_lt; simp only [↓reduceIte] at hsc_lt
      exact False.elim (by omega)
    · have hbeq3 : ((if knownNonAdj ctx.L0 ctx.m ctx.e0_mask ctx.has_nw1 f_msk 0 (nib (ptab.getD p_idx 0) 0) (nib (ptab.getD p_idx 0) 2) then 0 else 1) +
          (if knownNonAdj ctx.L0 ctx.m ctx.e0_mask ctx.has_nw1 f_msk 0 (nib (ptab.getD p_idx 0) 0) (nib (ptab.getD p_idx 0) 4) then 0 else 1) +
          (if knownNonAdj ctx.L0 ctx.m ctx.e0_mask ctx.has_nw1 f_msk 0 (nib (ptab.getD p_idx 0) 2) (nib (ptab.getD p_idx 0) 4) then 0 else 1) == 3) = false := beq_false_of_ne hsum3
      rw [hbeq3] at hsc_lt; simp only [Bool.false_eq_true, ↓reduceIte] at hsc_lt
      exact False.elim (by omega)
  | z j b_row =>
    intro _ f_msk _ hf hev
    simp only [evalDTCore, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hev
    rcases hev with ⟨⟨⟨⟨⟨hhz, hL0_5⟩, hbr⟩, hj_lt⟩, hf_br⟩, hnb_bits⟩
    obtain ⟨hiso, hdeg2, hz_or⟩ := ctx.hz_prop hhz hL0_5 j hj_lt
    have not_of_bit : ∀ (rz u_idx : ℕ) (hu : u_idx < ctx.m) (hrz : rz < ctx.L0),
        f_msk.testBit (rz * ctx.m + u_idx) = true →
        ¬ ctx.G.Adj (ctx.σ (ctx.kV rz)) (ctx.σ (ctx.f ⟨ctx.L0 + u_idx, by omega⟩)) := by
      intro rz u_idx hu hrz hbit
      have heb_f := hf (rz * ctx.m + u_idx) hbit
      rw [ctx.heb rz u_idx hu (Or.inl hrz)] at heb_f
      exact @of_decide_eq_false _ (ctx.decG _ _) heb_f
    have hn_13 : ¬ ctx.G.Adj (ctx.σ (ctx.kV 1)) (ctx.σ (ctx.f ⟨ctx.L0 + j, by omega⟩)) ∨
                 ¬ ctx.G.Adj (ctx.σ (ctx.kV 3)) (ctx.σ (ctx.f ⟨ctx.L0 + j, by omega⟩)) := by
      rcases hbr with rfl | rfl
      · exact Or.inl (not_of_bit 1 j hj_lt (by omega) hf_br)
      · exact Or.inr (not_of_bit 3 j hj_lt (by omega) hf_br)
    by_cases hm1 : ctx.m ≤ 1
    · exact False.elim (z_false_iso ctx.C ctx.G ctx.σ (ctx.kV 0) (ctx.kV 1) (ctx.kV 2)
        (ctx.kV 3) (ctx.kV 4) (ctx.f ⟨ctx.L0 + j, by omega⟩) (hiso hm1) hz_or hn_13)
    · simp only [hm1, ↓reduceIte, Bool.and_eq_true] at hnb_bits
      rcases hnb_bits with ⟨⟨⟨⟨⟨b0p, b2p⟩, b4p⟩, b0n⟩, b2n⟩, b4n⟩
      have hjp : (j + ctx.m - 1) % ctx.m < ctx.m := Nat.mod_lt _ ctx.hm_pos
      have hjn : (j + 1) % ctx.m < ctx.m := Nat.mod_lt _ ctx.hm_pos
      exact False.elim (z_false_deg2 ctx.C ctx.G ctx.σ (ctx.kV 0) (ctx.kV 1) (ctx.kV 2)
        (ctx.kV 3) (ctx.kV 4) (ctx.f ⟨ctx.L0 + j, by omega⟩)
        (ctx.f ⟨ctx.L0 + (j + ctx.m - 1) % ctx.m, by omega⟩)
        (ctx.f ⟨ctx.L0 + (j + 1) % ctx.m, by omega⟩)
        (hdeg2 hm1) hz_or hn_13
        (not_of_bit 0 _ hjp (by omega) b0p) (not_of_bit 2 _ hjp (by omega) b2p)
        (not_of_bit 4 _ hjp (by omega) b4p) (not_of_bit 0 _ hjn (by omega) b0n)
        (not_of_bit 2 _ hjn (by omega) b2n) (not_of_bit 4 _ hjn (by omega) b4n))
  | n bit l r ihl ihr =>
    intro t_msk f_msk ht hf hev
    simp only [evalDTCore, Bool.and_eq_true] at hev
    cases heb : ctx.ebL.getD bit false
    · refine ihr t_msk (f_msk ||| (1 <<< bit)) ht (fun i hi => ?_) hev.2
      rw [Nat.testBit_or] at hi
      rcases Bool.or_eq_true_iff.1 hi with h1 | h2
      · exact hf i h1
      · rw [testBit_one_shiftLeft, beq_iff_eq] at h2; subst h2; exact heb
    · refine ihl (t_msk ||| (1 <<< bit)) f_msk (fun i hi => ?_) hf hev.1
      rw [Nat.testBit_or] at hi
      rcases Bool.or_eq_true_iff.1 hi with h1 | h2
      · exact ht i h1
      · rw [testBit_one_shiftLeft, beq_iff_eq] at h2; subst h2; exact heb
lemma evalDT_sound {V : Type} [Fintype V] [DecidableEq V]
    {L0 m e0_mask sc0 : ℕ} {has_nw1 has_z : Bool} {ebL : List Bool}
    (hctx : ∃ ctx : ReflCtx V, ctx.L0 = L0 ∧ ctx.m = m ∧ ctx.e0_mask = e0_mask ∧
      ctx.sc0 = sc0 ∧ ctx.has_nw1 = has_nw1 ∧ ctx.has_z = has_z ∧ ctx.ebL = ebL)
    (ptab wL : List ℕ) (tgt : ℕ) (hlen : wL.length = ebL.length) (tree : DT)
    (t_msk f_msk : ℕ)
    (ht : ∀ i, t_msk.testBit i = true → ebL.getD i false = true)
    (hf : ∀ i, f_msk.testBit i = true → ebL.getD i false = false)
    (hev : evalDT L0 m e0_mask sc0 has_nw1 has_z ptab wL tgt tree t_msk f_msk = true) :
    tgt ≤ wSumBool wL ebL := by
  obtain ⟨ctx, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hctx
  exact evalDTCore_sound ctx ptab wL tgt hlen tree t_msk f_msk ht hf hev
lemma if_decide_eq_mul_b01 (w : ℕ) (p : Prop) [Decidable p] :
    (if decide p then w else 0) = w * b01 p := by
  by_cases hp : p <;> simp [b01, hp]
lemma mz {P : ℕ → Prop} : ∀ i, (0 : ℕ).testBit i = true → P i := by
  intro i hi; simp at hi
lemma mo {P : ℕ → Prop} {m1 m2 : ℕ}
    (h1 : ∀ i, m1.testBit i = true → P i) (h2 : ∀ i, m2.testBit i = true → P i) :
    ∀ i, (m1 ||| m2).testBit i = true → P i := by
  intro i hi; rw [Nat.testBit_or] at hi
  rcases Bool.or_eq_true_iff.1 hi with h | h
  · exact h1 i h
  · exact h2 i h
lemma mt {ebL : List Bool} (b : ℕ) {p : Prop} [Decidable p] (hp : p)
    (heq : ebL.getD b false = decide p := by rfl) :
    ∀ i, (1 <<< b).testBit i = true → ebL.getD i false = true := by
  intro i hi; rw [testBit_one_shiftLeft, beq_iff_eq] at hi
  subst hi; rw [heq]; exact decide_eq_true hp
lemma mf {ebL : List Bool} (b : ℕ) {p : Prop} [Decidable p] (hp : ¬ p)
    (heq : ebL.getD b false = decide p := by rfl) :
    ∀ i, (1 <<< b).testBit i = true → ebL.getD i false = false := by
  intro i hi; rw [testBit_one_shiftLeft, beq_iff_eq] at hi
  subst hi; rw [heq]; exact decide_eq_false hp
lemma fd {b : Bool} {P : Prop} (hb : b = true := by rfl) : b = false → P := by
  intro h; rw [hb] at h; cases h
lemma ff {P : Prop} : false = true → P := Bool.noConfusion
lemma fz {P : Prop} : 0 < 0 → P := fun h => absurd h (Nat.lt_irrefl 0)
abbrev AlmOn {V : Type} (C G : SimpleGraph V) (x y : V) (σ : Equiv.Perm V) : Prop :=
  ∀ a b, C.Adj a b → ¬(a = x ∧ b = y) → ¬(a = y ∧ b = x) → ¬ G.Adj (σ a) (σ b)
abbrev MinSc {V : Type} (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 k4 : V) (σ : Equiv.Perm V) : Prop :=
  ∀ τ : Equiv.Perm V, AlmOn C G k4 k0 τ →
    kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4) ≤ kScore G (τ k0) (τ k1) (τ k2) (τ k3) (τ k4)
abbrev ZProp {V : Type} (C G : SimpleGraph V) (k0 k1 k2 k3 k4 : V) (σ : Equiv.Perm V) (M : Finset V) : Prop :=
  ∀ u ∈ M, (G.Adj (σ k1) (σ u) ∧ G.Adj (σ k3) (σ u)) ∨
    ∃ b, C.Adj u b ∧ (G.Adj (σ k0) (σ b) ∨ G.Adj (σ k2) (σ b) ∨ G.Adj (σ k4) (σ b))
abbrev Dj4 {V : Type} [DecidableEq V] (k0 k1 k2 k3 : V) (M : Finset V) : Prop :=
  Disjoint ({k0, k1, k2, k3} : Finset V) M
abbrev Dj5 {V : Type} [DecidableEq V] (k0 k1 k2 k3 k4 : V) (M : Finset V) : Prop :=
  Disjoint ({k0, k1, k2, k3, k4} : Finset V) M
abbrev EqOn {V : Type} (τ σ : Equiv.Perm V) (M : Finset V) : Prop := ∀ u ∈ M, τ u = σ u
abbrev Fix5 {V : Type} (τ σ : Equiv.Perm V) (a0 a1 a2 a3 a4 k0 k1 k2 k3 k4 : V) : Prop :=
  τ k0 = σ a0 ∧ τ k1 = σ a1 ∧ τ k2 = σ a2 ∧ τ k3 = σ a3 ∧ τ k4 = σ a4
private lemma row_spec4 {has_nw1 : Bool} (hnw_false : has_nw1 = false) :
    ∀ r i, (r = 0 ∨ (has_nw1 = true ∧ (r = 1 ∨ r = 2 ∨ r = 3))) → i < 4 →
      rowOf r i < 4 ∨ (has_nw1 = true ∧ rowOf r i = 5) := by
  rintro r i (rfl | ⟨hnw, -⟩) hi; (interval_cases i <;> simp [rowOf]); (rw [hnw_false] at hnw; simp at hnw)
private lemma row_spec5 {has_nw1 : Bool} :
    ∀ r i, (r = 0 ∨ (has_nw1 = true ∧ (r = 1 ∨ r = 2 ∨ r = 3))) → i < 5 →
      rowOf r i < 5 ∨ (has_nw1 = true ∧ rowOf r i = 5) := by
  rintro r i (rfl | ⟨hnw, h_r⟩) hi; (interval_cases i <;> simp [rowOf]); (rcases h_r with rfl | rfl | rfl <;> interval_cases i <;> simp [rowOf, hnw])
abbrev kV4 {V : Type} (k0 k1 k2 k3 w : V) (r : ℕ) : V :=
  match r with | 0 => k0 | 1 => k1 | 2 => k2 | 3 => k3 | _ => w
abbrev kV5 {V : Type} (k0 k1 k2 k3 k4 w : V) (r : ℕ) : V :=
  match r with | 0 => k0 | 1 => k1 | 2 => k2 | 3 => k3 | 4 => k4 | _ => w
lemma rCount_comp3 {V : Type} [Fintype V] [DecidableEq V] {C : SimpleGraph V}
    (G : SimpleGraph V) [DecidableRel G.Adj] (σ : Equiv.Perm V) (z u0 u1 u2 : V)
    (hM : IsComp3 C u0 u1 u2) :
    rCount G σ z {u0, u1, u2} =
      b01 (G.Adj (σ z) (σ u0)) + b01 (G.Adj (σ z) (σ u1)) + b01 (G.Adj (σ z) (σ u2)) :=
  rCount_3 G σ z u0 u1 u2 hM.1 hM.2.1 hM.2.2.1
lemma rCount_comp4 {V : Type} [Fintype V] [DecidableEq V] {C : SimpleGraph V}
    (G : SimpleGraph V) [DecidableRel G.Adj] (σ : Equiv.Perm V) (z u0 u1 u2 u3 : V)
    (hM : IsComp4 C u0 u1 u2 u3) :
    rCount G σ z {u0, u1, u2, u3} =
      b01 (G.Adj (σ z) (σ u0)) + b01 (G.Adj (σ z) (σ u1)) +
      b01 (G.Adj (σ z) (σ u2)) + b01 (G.Adj (σ z) (σ u3)) :=
  rCount_4 G σ z u0 u1 u2 u3 hM.1 hM.2.1 hM.2.2.1 hM.2.2.2.1 hM.2.2.2.2.1 hM.2.2.2.2.2.1
lemma rCount_comp5 {V : Type} [Fintype V] [DecidableEq V] {C : SimpleGraph V}
    (G : SimpleGraph V) [DecidableRel G.Adj] (σ : Equiv.Perm V) (z u0 u1 u2 u3 u4 : V)
    (hM : IsComp5 C u0 u1 u2 u3 u4) :
    rCount G σ z {u0, u1, u2, u3, u4} =
      b01 (G.Adj (σ z) (σ u0)) + b01 (G.Adj (σ z) (σ u1)) + b01 (G.Adj (σ z) (σ u2)) +
      b01 (G.Adj (σ z) (σ u3)) + b01 (G.Adj (σ z) (σ u4)) :=
  rCount_5 G σ z u0 u1 u2 u3 u4 hM.1 hM.2.1 hM.2.2.1 hM.2.2.2.1 hM.2.2.2.2.1 hM.2.2.2.2.2.1
    hM.2.2.2.2.2.2.1 hM.2.2.2.2.2.2.2.1 hM.2.2.2.2.2.2.2.2.1 hM.2.2.2.2.2.2.2.2.2.1
lemma comp4_c_nonadj {V : Type} {C G : SimpleGraph V} {k0 k1 k2 k3 : V}
    (hK : IsComp4 C k0 k1 k2 k3) (σ : Equiv.Perm V)
    (hσ : ∀ a b, C.Adj a b → ¬(a = k3 ∧ b = k0) → ¬(a = k0 ∧ b = k3) → ¬ G.Adj (σ a) (σ b)) :
    ¬ G.Adj (σ k0) (σ k1) ∧ ¬ G.Adj (σ k1) (σ k2) ∧ ¬ G.Adj (σ k2) (σ k3) := by
  rcases hK with ⟨h01, h02, h03, h12, h13, h23, n0, n1, n2, _⟩
  refine ⟨hσ k0 k1 ((n0 k1).2 (Or.inr rfl)) (fun ⟨e, _⟩ => h03 e) (fun ⟨_, e⟩ => h13 e),
          hσ k1 k2 ((n1 k2).2 (Or.inr rfl)) (fun ⟨e, _⟩ => h13 e) (fun ⟨e, _⟩ => h01 e.symm),
          hσ k2 k3 ((n2 k3).2 (Or.inr rfl)) (fun ⟨e, _⟩ => h23 e) (fun ⟨e, _⟩ => h02 e.symm)⟩
lemma comp5_c_nonadj {V : Type} {C G : SimpleGraph V} {k0 k1 k2 k3 k4 : V}
    (hK : IsComp5 C k0 k1 k2 k3 k4) (σ : Equiv.Perm V)
    (hσ : ∀ a b, C.Adj a b → ¬(a = k4 ∧ b = k0) → ¬(a = k0 ∧ b = k4) → ¬ G.Adj (σ a) (σ b)) :
    ¬ G.Adj (σ k0) (σ k1) ∧ ¬ G.Adj (σ k1) (σ k2) ∧
    ¬ G.Adj (σ k2) (σ k3) ∧ ¬ G.Adj (σ k3) (σ k4) := by
  rcases hK with ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34, n0, n1, n2, n3, _⟩
  refine ⟨hσ k0 k1 ((n0 k1).2 (Or.inr rfl)) (fun ⟨e, _⟩ => h04 e) (fun ⟨_, e⟩ => h14 e),
          hσ k1 k2 ((n1 k2).2 (Or.inr rfl)) (fun ⟨e, _⟩ => h14 e) (fun ⟨e, _⟩ => h01 e.symm),
          hσ k2 k3 ((n2 k3).2 (Or.inr rfl)) (fun ⟨e, _⟩ => h24 e) (fun ⟨e, _⟩ => h02 e.symm),
          hσ k3 k4 ((n3 k4).2 (Or.inr rfl)) (fun ⟨e, _⟩ => h34 e) (fun ⟨e, _⟩ => h03 e.symm)⟩
lemma nonadj_of_disjoint {V : Type} [DecidableEq V] {C G : SimpleGraph V}
    {x y u v : V} {K M : Finset V} {σ : Equiv.Perm V}
    (hx : x ∈ K) (hd : Disjoint K M) (hu : u ∈ M) (hv : v ∈ M)
    (hσ : ∀ a b, C.Adj a b → ¬(a = x ∧ b = y) → ¬(a = y ∧ b = x) → ¬ G.Adj (σ a) (σ b))
    (hab : C.Adj u v) : ¬ G.Adj (σ u) (σ v) :=
  hσ u v hab
    (fun ⟨e, _⟩ => Finset.disjoint_left.1 hd (e ▸ hx) hu)
    (fun ⟨_, e⟩ => Finset.disjoint_left.1 hd (e ▸ hx) hv)
lemma comp3_m_nonadj {V : Type} [DecidableEq V] {C G : SimpleGraph V}
    {x y u0 u1 u2 : V} {K : Finset V} {σ : Equiv.Perm V}
    (hx : x ∈ K) (hM : IsComp3 C u0 u1 u2) (hd : Disjoint K {u0, u1, u2})
    (hσ : ∀ a b, C.Adj a b → ¬(a = x ∧ b = y) → ¬(a = y ∧ b = x) → ¬ G.Adj (σ a) (σ b)) :
    ¬ G.Adj (σ u0) (σ u1) ∧ ¬ G.Adj (σ u1) (σ u2) ∧ ¬ G.Adj (σ u2) (σ u0) := by
  rcases hM with ⟨_, _, _, n0, n1, n2⟩
  exact ⟨nonadj_of_disjoint hx hd (by simp) (by simp) hσ ((n0 u1).2 (Or.inr rfl)),
         nonadj_of_disjoint hx hd (by simp) (by simp) hσ ((n1 u2).2 (Or.inr rfl)),
         nonadj_of_disjoint hx hd (by simp) (by simp) hσ ((n2 u0).2 (Or.inr rfl))⟩
lemma comp4_m_nonadj {V : Type} [DecidableEq V] {C G : SimpleGraph V}
    {x y u0 u1 u2 u3 : V} {K : Finset V} {σ : Equiv.Perm V}
    (hx : x ∈ K) (hM : IsComp4 C u0 u1 u2 u3) (hd : Disjoint K {u0, u1, u2, u3})
    (hσ : ∀ a b, C.Adj a b → ¬(a = x ∧ b = y) → ¬(a = y ∧ b = x) → ¬ G.Adj (σ a) (σ b)) :
    ¬ G.Adj (σ u0) (σ u1) ∧ ¬ G.Adj (σ u1) (σ u2) ∧
    ¬ G.Adj (σ u2) (σ u3) ∧ ¬ G.Adj (σ u3) (σ u0) := by
  rcases hM with ⟨_, _, _, _, _, _, n0, n1, n2, n3⟩
  exact ⟨nonadj_of_disjoint hx hd (by simp) (by simp) hσ ((n0 u1).2 (Or.inr rfl)),
         nonadj_of_disjoint hx hd (by simp) (by simp) hσ ((n1 u2).2 (Or.inr rfl)),
         nonadj_of_disjoint hx hd (by simp) (by simp) hσ ((n2 u3).2 (Or.inr rfl)),
         nonadj_of_disjoint hx hd (by simp) (by simp) hσ ((n3 u0).2 (Or.inr rfl))⟩
lemma comp5_m_nonadj {V : Type} [DecidableEq V] {C G : SimpleGraph V}
    {x y u0 u1 u2 u3 u4 : V} {K : Finset V} {σ : Equiv.Perm V}
    (hx : x ∈ K) (hM : IsComp5 C u0 u1 u2 u3 u4) (hd : Disjoint K {u0, u1, u2, u3, u4})
    (hσ : ∀ a b, C.Adj a b → ¬(a = x ∧ b = y) → ¬(a = y ∧ b = x) → ¬ G.Adj (σ a) (σ b)) :
    ¬ G.Adj (σ u0) (σ u1) ∧ ¬ G.Adj (σ u1) (σ u2) ∧ ¬ G.Adj (σ u2) (σ u3) ∧
    ¬ G.Adj (σ u3) (σ u4) ∧ ¬ G.Adj (σ u4) (σ u0) := by
  rcases hM with ⟨_, _, _, _, _, _, _, _, _, _, n0, n1, n2, n3, n4⟩
  exact ⟨nonadj_of_disjoint hx hd (by simp) (by simp) hσ ((n0 u1).2 (Or.inr rfl)),
         nonadj_of_disjoint hx hd (by simp) (by simp) hσ ((n1 u2).2 (Or.inr rfl)),
         nonadj_of_disjoint hx hd (by simp) (by simp) hσ ((n2 u3).2 (Or.inr rfl)),
         nonadj_of_disjoint hx hd (by simp) (by simp) hσ ((n3 u4).2 (Or.inr rfl)),
         nonadj_of_disjoint hx hd (by simp) (by simp) hσ ((n4 u0).2 (Or.inr rfl))⟩
lemma set3_rot {V : Type} [DecidableEq V] (u0 u1 u2 : V) :
    ({u1, u2, u0} : Finset V) = {u0, u1, u2} := by ext x; simp; tauto
lemma set3_rev {V : Type} [DecidableEq V] (u0 u1 u2 : V) :
    ({u0, u2, u1} : Finset V) = {u0, u1, u2} := by ext x; simp; tauto
lemma set4_rot {V : Type} [DecidableEq V] (u0 u1 u2 u3 : V) :
    ({u1, u2, u3, u0} : Finset V) = {u0, u1, u2, u3} := by ext x; simp; tauto
lemma set4_rev {V : Type} [DecidableEq V] (u0 u1 u2 u3 : V) :
    ({u0, u3, u2, u1} : Finset V) = {u0, u1, u2, u3} := by ext x; simp; tauto
lemma set5_rot {V : Type} [DecidableEq V] (u0 u1 u2 u3 u4 : V) :
    ({u1, u2, u3, u4, u0} : Finset V) = {u0, u1, u2, u3, u4} := by ext x; simp; tauto
lemma set5_rev {V : Type} [DecidableEq V] (u0 u1 u2 u3 u4 : V) :
    ({u0, u4, u3, u2, u1} : Finset V) = {u0, u1, u2, u3, u4} := by ext x; simp; tauto
lemma sym_m3 {V : Type} [Fintype V] [DecidableEq V] (C G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : Equiv.Perm V) (zpiv : V) (P : Finset V → Prop)
    (h_none : ∀ u0 u1 u2, IsComp3 C u0 u1 u2 →
      ¬ G.Adj (σ zpiv) (σ u0) → ¬ G.Adj (σ zpiv) (σ u1) → ¬ G.Adj (σ zpiv) (σ u2) →
      P {u0, u1, u2})
    (h_01 : ∀ u0 u1 u2, IsComp3 C u0 u1 u2 →
      G.Adj (σ zpiv) (σ u0) → G.Adj (σ zpiv) (σ u1) → P {u0, u1, u2})
    (h_0n : ∀ u0 u1 u2, IsComp3 C u0 u1 u2 →
      G.Adj (σ zpiv) (σ u0) → ¬ G.Adj (σ zpiv) (σ u1) → ¬ G.Adj (σ zpiv) (σ u2) →
      P {u0, u1, u2})
    (u0 u1 u2 : V) (hM : IsComp3 C u0 u1 u2) : P {u0, u1, u2} := by
  have at0 : ∀ a0 a1 a2, IsComp3 C a0 a1 a2 → G.Adj (σ zpiv) (σ a0) → P {a0, a1, a2} := by
    intro a0 a1 a2 hMa t0
    by_cases t1 : G.Adj (σ zpiv) (σ a1)
    · exact h_01 a0 a1 a2 hMa t0 t1
    · by_cases t2 : G.Adj (σ zpiv) (σ a2)
      · rw [← set3_rev a0 a1 a2]; exact h_01 a0 a2 a1 hMa.rev t0 t2
      · exact h_0n a0 a1 a2 hMa t0 t1 t2
  by_cases t0 : G.Adj (σ zpiv) (σ u0)
  · exact at0 u0 u1 u2 hM t0
  · by_cases t1 : G.Adj (σ zpiv) (σ u1)
    · rw [← set3_rot u0 u1 u2]; exact at0 u1 u2 u0 hM.rot t1
    · by_cases t2 : G.Adj (σ zpiv) (σ u2)
      · rw [← set3_rot u0 u1 u2, ← set3_rot u1 u2 u0]; exact at0 u2 u0 u1 hM.rot.rot t2
      · exact h_none u0 u1 u2 hM t0 t1 t2
lemma sym_m4 {V : Type} [Fintype V] [DecidableEq V] (C G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : Equiv.Perm V) (zpiv : V) (P : Finset V → Prop)
    (h_none : ∀ u0 u1 u2 u3, IsComp4 C u0 u1 u2 u3 →
      ¬ G.Adj (σ zpiv) (σ u0) → ¬ G.Adj (σ zpiv) (σ u1) → ¬ G.Adj (σ zpiv) (σ u2) →
      ¬ G.Adj (σ zpiv) (σ u3) → P {u0, u1, u2, u3})
    (h_01 : ∀ u0 u1 u2 u3, IsComp4 C u0 u1 u2 u3 →
      G.Adj (σ zpiv) (σ u0) → G.Adj (σ zpiv) (σ u1) → P {u0, u1, u2, u3})
    (h_0n : ∀ u0 u1 u2 u3, IsComp4 C u0 u1 u2 u3 →
      G.Adj (σ zpiv) (σ u0) → ¬ G.Adj (σ zpiv) (σ u1) → ¬ G.Adj (σ zpiv) (σ u3) →
      P {u0, u1, u2, u3})
    (u0 u1 u2 u3 : V) (hM : IsComp4 C u0 u1 u2 u3) : P {u0, u1, u2, u3} := by
  have at0 : ∀ a0 a1 a2 a3, IsComp4 C a0 a1 a2 a3 → G.Adj (σ zpiv) (σ a0) → P {a0, a1, a2, a3} := by
    intro a0 a1 a2 a3 hMa t0
    by_cases t1 : G.Adj (σ zpiv) (σ a1)
    · exact h_01 a0 a1 a2 a3 hMa t0 t1
    · by_cases t3 : G.Adj (σ zpiv) (σ a3)
      · rw [← set4_rev a0 a1 a2 a3]; exact h_01 a0 a3 a2 a1 hMa.rev t0 t3
      · exact h_0n a0 a1 a2 a3 hMa t0 t1 t3
  by_cases t0 : G.Adj (σ zpiv) (σ u0)
  · exact at0 u0 u1 u2 u3 hM t0
  · by_cases t1 : G.Adj (σ zpiv) (σ u1)
    · rw [← set4_rot u0 u1 u2 u3]; exact at0 u1 u2 u3 u0 hM.rot t1
    · by_cases t2 : G.Adj (σ zpiv) (σ u2)
      · rw [← set4_rot u0 u1 u2 u3, ← set4_rot u1 u2 u3 u0]
        exact at0 u2 u3 u0 u1 hM.rot.rot t2
      · by_cases t3 : G.Adj (σ zpiv) (σ u3)
        · rw [← set4_rot u0 u1 u2 u3, ← set4_rot u1 u2 u3 u0, ← set4_rot u2 u3 u0 u1]
          exact at0 u3 u0 u1 u2 hM.rot.rot.rot t3
        · exact h_none u0 u1 u2 u3 hM t0 t1 t2 t3
lemma sym_m5 {V : Type} [Fintype V] [DecidableEq V] (C G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : Equiv.Perm V) (zpiv : V) (P : Finset V → Prop)
    (h_none : ∀ u0 u1 u2 u3 u4, IsComp5 C u0 u1 u2 u3 u4 →
      ¬ G.Adj (σ zpiv) (σ u0) → ¬ G.Adj (σ zpiv) (σ u1) → ¬ G.Adj (σ zpiv) (σ u2) →
      ¬ G.Adj (σ zpiv) (σ u3) → ¬ G.Adj (σ zpiv) (σ u4) → P {u0, u1, u2, u3, u4})
    (h_01 : ∀ u0 u1 u2 u3 u4, IsComp5 C u0 u1 u2 u3 u4 →
      G.Adj (σ zpiv) (σ u0) → G.Adj (σ zpiv) (σ u1) → P {u0, u1, u2, u3, u4})
    (h_0n : ∀ u0 u1 u2 u3 u4, IsComp5 C u0 u1 u2 u3 u4 →
      G.Adj (σ zpiv) (σ u0) → ¬ G.Adj (σ zpiv) (σ u1) → ¬ G.Adj (σ zpiv) (σ u4) →
      P {u0, u1, u2, u3, u4})
    (u0 u1 u2 u3 u4 : V) (hM : IsComp5 C u0 u1 u2 u3 u4) : P {u0, u1, u2, u3, u4} := by
  have at0 : ∀ a0 a1 a2 a3 a4, IsComp5 C a0 a1 a2 a3 a4 → G.Adj (σ zpiv) (σ a0) →
      P {a0, a1, a2, a3, a4} := by
    intro a0 a1 a2 a3 a4 hMa t0
    by_cases t1 : G.Adj (σ zpiv) (σ a1)
    · exact h_01 a0 a1 a2 a3 a4 hMa t0 t1
    · by_cases t4 : G.Adj (σ zpiv) (σ a4)
      · rw [← set5_rev a0 a1 a2 a3 a4]; exact h_01 a0 a4 a3 a2 a1 hMa.rev t0 t4
      · exact h_0n a0 a1 a2 a3 a4 hMa t0 t1 t4
  by_cases t0 : G.Adj (σ zpiv) (σ u0)
  · exact at0 u0 u1 u2 u3 u4 hM t0
  · by_cases t1 : G.Adj (σ zpiv) (σ u1)
    · rw [← set5_rot u0 u1 u2 u3 u4]; exact at0 u1 u2 u3 u4 u0 hM.rot t1
    · by_cases t2 : G.Adj (σ zpiv) (σ u2)
      · rw [← set5_rot u0 u1 u2 u3 u4, ← set5_rot u1 u2 u3 u4 u0]
        exact at0 u2 u3 u4 u0 u1 hM.rot.rot t2
      · by_cases t3 : G.Adj (σ zpiv) (σ u3)
        · rw [← set5_rot u0 u1 u2 u3 u4, ← set5_rot u1 u2 u3 u4 u0, ← set5_rot u2 u3 u4 u0 u1]
          exact at0 u3 u4 u0 u1 u2 hM.rot.rot.rot t3
        · by_cases t4 : G.Adj (σ zpiv) (σ u4)
          · rw [← set5_rot u0 u1 u2 u3 u4, ← set5_rot u1 u2 u3 u4 u0,
                ← set5_rot u2 u3 u4 u0 u1, ← set5_rot u3 u4 u0 u1 u2]
            exact at0 u4 u0 u1 u2 u3 hM.rot.rot.rot.rot t4
          · exact h_none u0 u1 u2 u3 u4 hM t0 t1 t2 t3 t4
lemma sym2_m3 {V : Type} [Fintype V] [DecidableEq V] (C G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : Equiv.Perm V) (zp1 zp2 : V) (P : Finset V → Prop)
    (h_p1_01 : ∀ u0 u1 u2, IsComp3 C u0 u1 u2 →
      G.Adj (σ zp1) (σ u0) → G.Adj (σ zp1) (σ u1) → P {u0, u1, u2})
    (h_p1_0n : ∀ u0 u1 u2, IsComp3 C u0 u1 u2 →
      G.Adj (σ zp1) (σ u0) → ¬ G.Adj (σ zp1) (σ u1) → ¬ G.Adj (σ zp1) (σ u2) →
      P {u0, u1, u2})
    (h_p2_01 : ∀ u0 u1 u2, IsComp3 C u0 u1 u2 →
      ¬ G.Adj (σ zp1) (σ u0) → ¬ G.Adj (σ zp1) (σ u1) → ¬ G.Adj (σ zp1) (σ u2) →
      G.Adj (σ zp2) (σ u0) → G.Adj (σ zp2) (σ u1) → P {u0, u1, u2})
    (h_p2_0n : ∀ u0 u1 u2, IsComp3 C u0 u1 u2 →
      ¬ G.Adj (σ zp1) (σ u0) → ¬ G.Adj (σ zp1) (σ u1) → ¬ G.Adj (σ zp1) (σ u2) →
      G.Adj (σ zp2) (σ u0) → ¬ G.Adj (σ zp2) (σ u1) → ¬ G.Adj (σ zp2) (σ u2) →
      P {u0, u1, u2})
    (h_none : ∀ u0 u1 u2, IsComp3 C u0 u1 u2 →
      ¬ G.Adj (σ zp1) (σ u0) → ¬ G.Adj (σ zp1) (σ u1) → ¬ G.Adj (σ zp1) (σ u2) →
      ¬ G.Adj (σ zp2) (σ u0) → ¬ G.Adj (σ zp2) (σ u1) → ¬ G.Adj (σ zp2) (σ u2) →
      P {u0, u1, u2})
    (u0 u1 u2 : V) (hM : IsComp3 C u0 u1 u2) : P {u0, u1, u2} := by
  refine sym_m3 C G σ zp1 P (fun a0 a1 a2 hMa n0 n1 n2 => ?_) h_p1_01 h_p1_0n u0 u1 u2 hM
  have hn1 : ∀ u ∈ ({a0, a1, a2} : Finset V), ¬ G.Adj (σ zp1) (σ u) := by
    intro u hu; simp only [mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl | rfl <;> assumption
  exact sym_m3 C G σ zp2 (fun M => (∀ u ∈ M, ¬ G.Adj (σ zp1) (σ u)) → P M)
    (fun b0 b1 b2 hMb q0 q1 q2 hM1 => h_none b0 b1 b2 hMb (hM1 b0 (by simp)) (hM1 b1 (by simp)) (hM1 b2 (by simp)) q0 q1 q2)
    (fun b0 b1 b2 hMb t0 t1 hM1 => h_p2_01 b0 b1 b2 hMb (hM1 b0 (by simp)) (hM1 b1 (by simp)) (hM1 b2 (by simp)) t0 t1)
    (fun b0 b1 b2 hMb t0 q1 q2 hM1 => h_p2_0n b0 b1 b2 hMb (hM1 b0 (by simp)) (hM1 b1 (by simp)) (hM1 b2 (by simp)) t0 q1 q2)
    a0 a1 a2 hMa hn1
lemma sym2_m4 {V : Type} [Fintype V] [DecidableEq V] (C G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : Equiv.Perm V) (zp1 zp2 : V) (P : Finset V → Prop)
    (h_p1_01 : ∀ u0 u1 u2 u3, IsComp4 C u0 u1 u2 u3 →
      G.Adj (σ zp1) (σ u0) → G.Adj (σ zp1) (σ u1) → P {u0, u1, u2, u3})
    (h_p1_0n : ∀ u0 u1 u2 u3, IsComp4 C u0 u1 u2 u3 →
      G.Adj (σ zp1) (σ u0) → ¬ G.Adj (σ zp1) (σ u1) → ¬ G.Adj (σ zp1) (σ u3) →
      P {u0, u1, u2, u3})
    (h_p2_01 : ∀ u0 u1 u2 u3, IsComp4 C u0 u1 u2 u3 →
      ¬ G.Adj (σ zp1) (σ u0) → ¬ G.Adj (σ zp1) (σ u1) → ¬ G.Adj (σ zp1) (σ u2) → ¬ G.Adj (σ zp1) (σ u3) →
      G.Adj (σ zp2) (σ u0) → G.Adj (σ zp2) (σ u1) → P {u0, u1, u2, u3})
    (h_p2_0n : ∀ u0 u1 u2 u3, IsComp4 C u0 u1 u2 u3 →
      ¬ G.Adj (σ zp1) (σ u0) → ¬ G.Adj (σ zp1) (σ u1) → ¬ G.Adj (σ zp1) (σ u2) → ¬ G.Adj (σ zp1) (σ u3) →
      G.Adj (σ zp2) (σ u0) → ¬ G.Adj (σ zp2) (σ u1) → ¬ G.Adj (σ zp2) (σ u3) →
      P {u0, u1, u2, u3})
    (h_none : ∀ u0 u1 u2 u3, IsComp4 C u0 u1 u2 u3 →
      ¬ G.Adj (σ zp1) (σ u0) → ¬ G.Adj (σ zp1) (σ u1) → ¬ G.Adj (σ zp1) (σ u2) → ¬ G.Adj (σ zp1) (σ u3) →
      ¬ G.Adj (σ zp2) (σ u0) → ¬ G.Adj (σ zp2) (σ u1) → ¬ G.Adj (σ zp2) (σ u2) → ¬ G.Adj (σ zp2) (σ u3) →
      P {u0, u1, u2, u3})
    (u0 u1 u2 u3 : V) (hM : IsComp4 C u0 u1 u2 u3) : P {u0, u1, u2, u3} := by
  refine sym_m4 C G σ zp1 P (fun a0 a1 a2 a3 hMa n0 n1 n2 n3 => ?_) h_p1_01 h_p1_0n u0 u1 u2 u3 hM
  have hn1 : ∀ u ∈ ({a0, a1, a2, a3} : Finset V), ¬ G.Adj (σ zp1) (σ u) := by
    intro u hu; simp only [mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> assumption
  exact sym_m4 C G σ zp2 (fun M => (∀ u ∈ M, ¬ G.Adj (σ zp1) (σ u)) → P M)
    (fun b0 b1 b2 b3 hMb q0 q1 q2 q3 hM1 => h_none b0 b1 b2 b3 hMb (hM1 b0 (by simp)) (hM1 b1 (by simp)) (hM1 b2 (by simp)) (hM1 b3 (by simp)) q0 q1 q2 q3)
    (fun b0 b1 b2 b3 hMb t0 t1 hM1 => h_p2_01 b0 b1 b2 b3 hMb (hM1 b0 (by simp)) (hM1 b1 (by simp)) (hM1 b2 (by simp)) (hM1 b3 (by simp)) t0 t1)
    (fun b0 b1 b2 b3 hMb t0 q1 q3 hM1 => h_p2_0n b0 b1 b2 b3 hMb (hM1 b0 (by simp)) (hM1 b1 (by simp)) (hM1 b2 (by simp)) (hM1 b3 (by simp)) t0 q1 q3)
    a0 a1 a2 a3 hMa hn1
lemma sym2_m5 {V : Type} [Fintype V] [DecidableEq V] (C G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : Equiv.Perm V) (zp1 zp2 : V) (P : Finset V → Prop)
    (h_p1_01 : ∀ u0 u1 u2 u3 u4, IsComp5 C u0 u1 u2 u3 u4 →
      G.Adj (σ zp1) (σ u0) → G.Adj (σ zp1) (σ u1) → P {u0, u1, u2, u3, u4})
    (h_p1_0n : ∀ u0 u1 u2 u3 u4, IsComp5 C u0 u1 u2 u3 u4 →
      G.Adj (σ zp1) (σ u0) → ¬ G.Adj (σ zp1) (σ u1) → ¬ G.Adj (σ zp1) (σ u4) →
      P {u0, u1, u2, u3, u4})
    (h_p2_01 : ∀ u0 u1 u2 u3 u4, IsComp5 C u0 u1 u2 u3 u4 →
      ¬ G.Adj (σ zp1) (σ u0) → ¬ G.Adj (σ zp1) (σ u1) → ¬ G.Adj (σ zp1) (σ u2) →
      ¬ G.Adj (σ zp1) (σ u3) → ¬ G.Adj (σ zp1) (σ u4) →
      G.Adj (σ zp2) (σ u0) → G.Adj (σ zp2) (σ u1) → P {u0, u1, u2, u3, u4})
    (h_p2_0n : ∀ u0 u1 u2 u3 u4, IsComp5 C u0 u1 u2 u3 u4 →
      ¬ G.Adj (σ zp1) (σ u0) → ¬ G.Adj (σ zp1) (σ u1) → ¬ G.Adj (σ zp1) (σ u2) →
      ¬ G.Adj (σ zp1) (σ u3) → ¬ G.Adj (σ zp1) (σ u4) →
      G.Adj (σ zp2) (σ u0) → ¬ G.Adj (σ zp2) (σ u1) → ¬ G.Adj (σ zp2) (σ u4) →
      P {u0, u1, u2, u3, u4})
    (h_none : ∀ u0 u1 u2 u3 u4, IsComp5 C u0 u1 u2 u3 u4 →
      ¬ G.Adj (σ zp1) (σ u0) → ¬ G.Adj (σ zp1) (σ u1) → ¬ G.Adj (σ zp1) (σ u2) →
      ¬ G.Adj (σ zp1) (σ u3) → ¬ G.Adj (σ zp1) (σ u4) →
      ¬ G.Adj (σ zp2) (σ u0) → ¬ G.Adj (σ zp2) (σ u1) → ¬ G.Adj (σ zp2) (σ u2) →
      ¬ G.Adj (σ zp2) (σ u3) → ¬ G.Adj (σ zp2) (σ u4) → P {u0, u1, u2, u3, u4})
    (u0 u1 u2 u3 u4 : V) (hM : IsComp5 C u0 u1 u2 u3 u4) : P {u0, u1, u2, u3, u4} := by
  refine sym_m5 C G σ zp1 P (fun a0 a1 a2 a3 a4 hMa n0 n1 n2 n3 n4 => ?_) h_p1_01 h_p1_0n u0 u1 u2 u3 u4 hM
  have hn1 : ∀ u ∈ ({a0, a1, a2, a3, a4} : Finset V), ¬ G.Adj (σ zp1) (σ u) := by
    intro u hu; simp only [mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl <;> assumption
  exact sym_m5 C G σ zp2 (fun M => (∀ u ∈ M, ¬ G.Adj (σ zp1) (σ u)) → P M)
    (fun b0 b1 b2 b3 b4 hMb q0 q1 q2 q3 q4 hM1 => h_none b0 b1 b2 b3 b4 hMb (hM1 b0 (by simp)) (hM1 b1 (by simp)) (hM1 b2 (by simp)) (hM1 b3 (by simp)) (hM1 b4 (by simp)) q0 q1 q2 q3 q4)
    (fun b0 b1 b2 b3 b4 hMb t0 t1 hM1 => h_p2_01 b0 b1 b2 b3 b4 hMb (hM1 b0 (by simp)) (hM1 b1 (by simp)) (hM1 b2 (by simp)) (hM1 b3 (by simp)) (hM1 b4 (by simp)) t0 t1)
    (fun b0 b1 b2 b3 b4 hMb t0 q1 q4 hM1 => h_p2_0n b0 b1 b2 b3 b4 hMb (hM1 b0 (by simp)) (hM1 b1 (by simp)) (hM1 b2 (by simp)) (hM1 b3 (by simp)) (hM1 b4 (by simp)) t0 q1 q4)
    a0 a1 a2 a3 a4 hMa hn1
private lemma k_path4 {V : Type} {C G : SimpleGraph V} {k0 k1 k2 k3 w : V}
    (hK : IsComp4 C k0 k1 k2 k3) {σ : Equiv.Perm V} (hσ : AlmOn C G k3 k0 σ) :
    ∀ i, i + 1 < 4 → ¬ G.Adj (σ (kV4 k0 k1 k2 k3 w i)) (σ (kV4 k0 k1 k2 k3 w (i + 1))) := by
  obtain ⟨c0, c1, c2⟩ := comp4_c_nonadj hK σ hσ
  intro i hi
  have hi' : i < 3 := by omega
  interval_cases i <;> assumption
private lemma k_path5 {V : Type} {C G : SimpleGraph V} {k0 k1 k2 k3 k4 w : V}
    (hK : IsComp5 C k0 k1 k2 k3 k4) {σ : Equiv.Perm V} (hσ : AlmOn C G k4 k0 σ) :
    ∀ i, i + 1 < 5 → ¬ G.Adj (σ (kV5 k0 k1 k2 k3 k4 w i)) (σ (kV5 k0 k1 k2 k3 k4 w (i + 1))) := by
  obtain ⟨c0, c1, c2, c3⟩ := comp5_c_nonadj hK σ hσ
  intro i hi
  have hi' : i < 4 := by omega
  interval_cases i <;> assumption
private lemma k_e0_4 {V : Type} {G : SimpleGraph V} {k0 k1 k2 k3 w : V} {σ : Equiv.Perm V} {e0_mask : ℕ}
    (hne_0_2 : e0_mask.testBit 2 = false → ¬ G.Adj (σ k0) (σ k2))
    (hne_0_3 : e0_mask.testBit 3 = false → ¬ G.Adj (σ k0) (σ k3))
    (hne_1_3 : e0_mask.testBit 8 = false → ¬ G.Adj (σ k1) (σ k3)) :
    ∀ i j, i < j → j < 4 → j ≠ i + 1 → e0_mask.testBit (i * 5 + j) = false →
      ¬ G.Adj (σ (kV4 k0 k1 k2 k3 w i)) (σ (kV4 k0 k1 k2 k3 w j)) := by
  intro i j hij hj hne hbit
  interval_cases j <;> interval_cases i <;> first | omega | exact hne_0_2 hbit | exact hne_0_3 hbit | exact hne_1_3 hbit
private lemma k_e0_5 {V : Type} {G : SimpleGraph V} {k0 k1 k2 k3 k4 w : V} {σ : Equiv.Perm V} {e0_mask : ℕ}
    (hne_0_2 : e0_mask.testBit 2 = false → ¬ G.Adj (σ k0) (σ k2))
    (hne_0_3 : e0_mask.testBit 3 = false → ¬ G.Adj (σ k0) (σ k3))
    (hne_0_4 : e0_mask.testBit 4 = false → ¬ G.Adj (σ k0) (σ k4))
    (hne_1_3 : e0_mask.testBit 8 = false → ¬ G.Adj (σ k1) (σ k3))
    (hne_1_4 : e0_mask.testBit 9 = false → ¬ G.Adj (σ k1) (σ k4))
    (hne_2_4 : e0_mask.testBit 14 = false → ¬ G.Adj (σ k2) (σ k4)) :
    ∀ i j, i < j → j < 5 → j ≠ i + 1 → e0_mask.testBit (i * 5 + j) = false →
      ¬ G.Adj (σ (kV5 k0 k1 k2 k3 k4 w i)) (σ (kV5 k0 k1 k2 k3 k4 w j)) := by
  intro i j hij hj hne hbit
  interval_cases j <;> interval_cases i <;> first | omega | exact hne_0_2 hbit | exact hne_0_3 hbit | exact hne_0_4 hbit | exact hne_1_3 hbit | exact hne_1_4 hbit | exact hne_2_4 hbit
abbrev fArr4_1 {V : Type} (k0 k1 k2 k3 u0 : V) (idx : Fin 5) : V := match idx.1 with | 0 => k0 | 1 => k1 | 2 => k2 | 3 => k3 | _ => u0
abbrev eb4_1 {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj] (σ : Equiv.Perm V) (k0 k1 k2 k3 u0 : V) : List Bool := [decide (G.Adj (σ k0) (σ u0)), decide (G.Adj (σ k1) (σ u0)), decide (G.Adj (σ k2) (σ u0)), decide (G.Adj (σ k3) (σ u0))]
private lemma wSum_eb4_1 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (σ : Equiv.Perm V) (w0 w1 w2 w3 : ℕ) (k0 k1 k2 k3 u0 : V) :
    wSumBool [w0, w1, w2, w3] (eb4_1 G σ k0 k1 k2 k3 u0) = w0 * rCount G σ k0 {u0} + w1 * rCount G σ k1 {u0} + w2 * rCount G σ k2 {u0} + w3 * rCount G σ k3 {u0} := by
  simp only [wSumBool, if_decide_eq_mul_b01, rCount_1]; ring
private lemma fArr4_1_inj {V : Type} [DecidableEq V] {C : SimpleGraph V}
    {k0 k1 k2 k3 u0 : V} (hK : IsComp4 C k0 k1 k2 k3) (_hM : IsComp1 C u0)
    (hd : Dj4 k0 k1 k2 k3 {u0}) : Function.Injective (fArr4_1 k0 k1 k2 k3 u0) := by
  rcases hK with ⟨hk01, hk02, hk03, hk12, hk13, hk23, -⟩
  simp only [Dj4, Finset.disjoint_insert_left, Finset.disjoint_singleton_left, mem_singleton] at hd
  rcases hd with ⟨hkm00, hkm10, hkm20, hkm30⟩
  intro i j hij; fin_cases i <;> fin_cases j <;> simp only [fArr4_1] at hij ⊢
  all_goals first | rfl | exact absurd hij (by assumption) | exact absurd hij.symm (by assumption)
private lemma fArr4_1_hcl {V : Type} {C : SimpleGraph V} {k0 k1 k2 k3 u0 : V}
    (hK : IsComp4 C k0 k1 k2 k3) (hM : IsComp1 C u0) :
    ∀ idx1 : Fin 5, ∀ b, C.Adj ((fArr4_1 k0 k1 k2 k3 u0) idx1) b →
      ∃ idx2 : Fin 5, (fArr4_1 k0 k1 k2 k3 u0) idx2 = b ∧
        hasUndirEdge (cEdgesK 4 ++ cEdgesM 4 1) idx1.1 idx2.1 = true := by
  rcases hK with ⟨_, _, _, _, _, _, hkn0, hkn1, hkn2, hkn3⟩
  intro idx1 b hab; fin_cases idx1 <;> dsimp [fArr4_1] at hab
  · rcases (hkn0 b).1 hab with rfl | rfl
    · exact ⟨⟨3, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨1, by decide⟩, rfl, rfl⟩
  · rcases (hkn1 b).1 hab with rfl | rfl
    · exact ⟨⟨0, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨2, by decide⟩, rfl, rfl⟩
  · rcases (hkn2 b).1 hab with rfl | rfl
    · exact ⟨⟨1, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨3, by decide⟩, rfl, rfl⟩
  · rcases (hkn3 b).1 hab with rfl | rfl
    · exact ⟨⟨2, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨0, by decide⟩, rfl, rfl⟩
  · exact absurd hab (hM b)
private lemma mkCtx4_1 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 w u0 : V)
    (hK : IsComp4 C k0 k1 k2 k3) (hM : IsComp1 C u0)
    (hd : Dj4 k0 k1 k2 k3 {u0}) (σ : Equiv.Perm V) (hσ : AlmOn C G k3 k0 σ)
    (hnp : ¬ Packs C G) (e0_mask sc0 : ℕ) (has_nw1 has_z : Bool) (σ1 σ2 σ3 : Equiv.Perm V)
    (hne_0_2 : e0_mask.testBit 2 = false → ¬ G.Adj (σ k0) (σ k2))
    (hne_0_3 : e0_mask.testBit 3 = false → ¬ G.Adj (σ k0) (σ k3))
    (hne_1_3 : e0_mask.testBit 8 = false → ¬ G.Adj (σ k1) (σ k3))
    (hnw_false : has_nw1 = false)
    : ∃ ctx : ReflCtx V, ctx.L0 = 4 ∧ ctx.m = 1 ∧ ctx.e0_mask = e0_mask ∧ ctx.sc0 = sc0 ∧ ctx.has_nw1 = has_nw1 ∧ ctx.has_z = has_z ∧ ctx.ebL = (eb4_1 G σ k0 k1 k2 k3 u0) :=
  ⟨{
    C := C, G := G, decG := inferInstance, L0 := 4, m := 1,
    e0_mask := e0_mask, sc0 := sc0, has_nw1 := has_nw1, has_z := has_z,
    ebL := (eb4_1 G σ k0 k1 k2 k3 u0), hL0_pos := by decide, hm_pos := by decide,
    f := (fArr4_1 k0 k1 k2 k3 u0), hf := fArr4_1_inj hK hM hd, kV := (kV4 k0 k1 k2 k3 w),
    hkV_eq := by intro i hi; interval_cases i <;> rfl,
    σ := σ, σr := (fun r => match r with | 1 => σ1 | 2 => σ2 | 3 => σ3 | _ => σ),
    hnp := hnp,
    hrow_spec := row_spec4 hnw_false,
    hσr0 := fun _ => rfl,
    hσr_alm := by rintro r (rfl | ⟨hnw, -⟩); exact hσ; (rw [hnw_false] at hnw; simp at hnw),
    hσr_k := by rintro r (rfl | ⟨hnw, -⟩) i hi; (interval_cases i <;> rfl); (rw [hnw_false] at hnw; simp at hnw),
    hσr_m := by rintro r (rfl | ⟨hnw, -⟩) j hj; (interval_cases j; rfl); (rw [hnw_false] at hnw; simp at hnw),
    hk_path := k_path4 hK hσ,
    hk_e0 := k_e0_4 hne_0_2 hne_0_3 hne_1_3,
    hnw1 := fun h => by rw [hnw_false] at h; simp at h,
    hm_edge := fun j1 j2 hj12 hj2 _ => by omega,
    heb := by rintro ru j hj (hlt | ⟨hnw, -⟩); (interval_cases ru <;> interval_cases j <;> rfl); (rw [hnw_false] at hnw; simp at hnw),
    hcl_pack := fArr4_1_hcl hK hM,
    halm_min := fun h5 => by omega, hz_prop := fun _ h5 => by omega }, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
abbrev fArr4_3 {V : Type} (k0 k1 k2 k3 u0 u1 u2 : V) (idx : Fin 7) : V := match idx.1 with | 0 => k0 | 1 => k1 | 2 => k2 | 3 => k3 | 4 => u0 | 5 => u1 | _ => u2
abbrev eb4_3 {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj] (σ : Equiv.Perm V) (k0 k1 k2 k3 u0 u1 u2 : V) : List Bool := [decide (G.Adj (σ k0) (σ u0)), decide (G.Adj (σ k0) (σ u1)), decide (G.Adj (σ k0) (σ u2)), decide (G.Adj (σ k1) (σ u0)), decide (G.Adj (σ k1) (σ u1)), decide (G.Adj (σ k1) (σ u2)), decide (G.Adj (σ k2) (σ u0)), decide (G.Adj (σ k2) (σ u1)), decide (G.Adj (σ k2) (σ u2)), decide (G.Adj (σ k3) (σ u0)), decide (G.Adj (σ k3) (σ u1)), decide (G.Adj (σ k3) (σ u2))]
private lemma wSum_eb4_3 {V : Type} [Fintype V] [DecidableEq V] {C : SimpleGraph V} (G : SimpleGraph V) [DecidableRel G.Adj] (σ : Equiv.Perm V) (w0 w1 w2 w3 : ℕ) (k0 k1 k2 k3 u0 u1 u2 : V) (hM : IsComp3 C u0 u1 u2) :
    wSumBool [w0, w0, w0, w1, w1, w1, w2, w2, w2, w3, w3, w3] (eb4_3 G σ k0 k1 k2 k3 u0 u1 u2) = w0 * rCount G σ k0 {u0, u1, u2} + w1 * rCount G σ k1 {u0, u1, u2} + w2 * rCount G σ k2 {u0, u1, u2} + w3 * rCount G σ k3 {u0, u1, u2} := by
  simp only [wSumBool, if_decide_eq_mul_b01, rCount_comp3 G σ _ u0 u1 u2 hM]; ring
private lemma fArr4_3_inj {V : Type} [DecidableEq V] {C : SimpleGraph V}
    {k0 k1 k2 k3 u0 u1 u2 : V} (hK : IsComp4 C k0 k1 k2 k3) (hM : IsComp3 C u0 u1 u2)
    (hd : Dj4 k0 k1 k2 k3 {u0, u1, u2}) : Function.Injective (fArr4_3 k0 k1 k2 k3 u0 u1 u2) := by
  rcases hK with ⟨hk01, hk02, hk03, hk12, hk13, hk23, -⟩
  rcases hM with ⟨hm01, hm02, hm12, -⟩
  simp only [Dj4, Finset.disjoint_insert_left, Finset.disjoint_singleton_left, mem_insert, mem_singleton, not_or] at hd
  rcases hd with ⟨⟨hkm00, hkm01, hkm02⟩, ⟨hkm10, hkm11, hkm12⟩, ⟨hkm20, hkm21, hkm22⟩, ⟨hkm30, hkm31, hkm32⟩⟩
  intro i j hij; fin_cases i <;> fin_cases j <;> simp only [fArr4_3] at hij ⊢
  all_goals first | rfl | exact absurd hij (by assumption) | exact absurd hij.symm (by assumption)
private lemma fArr4_3_hcl {V : Type} {C : SimpleGraph V} {k0 k1 k2 k3 u0 u1 u2 : V}
    (hK : IsComp4 C k0 k1 k2 k3) (hM : IsComp3 C u0 u1 u2) :
    ∀ idx1 : Fin 7, ∀ b, C.Adj ((fArr4_3 k0 k1 k2 k3 u0 u1 u2) idx1) b →
      ∃ idx2 : Fin 7, (fArr4_3 k0 k1 k2 k3 u0 u1 u2) idx2 = b ∧
        hasUndirEdge (cEdgesK 4 ++ cEdgesM 4 3) idx1.1 idx2.1 = true := by
  rcases hK with ⟨_, _, _, _, _, _, hkn0, hkn1, hkn2, hkn3⟩
  rcases hM with ⟨_, _, _, hmn0, hmn1, hmn2⟩
  intro idx1 b hab; fin_cases idx1 <;> dsimp [fArr4_3] at hab
  · rcases (hkn0 b).1 hab with rfl | rfl
    · exact ⟨⟨3, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨1, by decide⟩, rfl, rfl⟩
  · rcases (hkn1 b).1 hab with rfl | rfl
    · exact ⟨⟨0, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨2, by decide⟩, rfl, rfl⟩
  · rcases (hkn2 b).1 hab with rfl | rfl
    · exact ⟨⟨1, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨3, by decide⟩, rfl, rfl⟩
  · rcases (hkn3 b).1 hab with rfl | rfl
    · exact ⟨⟨2, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨0, by decide⟩, rfl, rfl⟩
  · rcases (hmn0 b).1 hab with rfl | rfl
    · exact ⟨⟨6, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨5, by decide⟩, rfl, rfl⟩
  · rcases (hmn1 b).1 hab with rfl | rfl
    · exact ⟨⟨4, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨6, by decide⟩, rfl, rfl⟩
  · rcases (hmn2 b).1 hab with rfl | rfl
    · exact ⟨⟨5, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨4, by decide⟩, rfl, rfl⟩
private lemma fArr4_3_hm {V : Type} [DecidableEq V] {C G : SimpleGraph V} {k0 k1 k2 k3 u0 u1 u2 : V}
    {σ : Equiv.Perm V} (hM : IsComp3 C u0 u1 u2) (hd : Dj4 k0 k1 k2 k3 {u0, u1, u2})
    (hσ : AlmOn C G k3 k0 σ) : ∀ j1 j2 (hj12 : j1 < j2) (hj2 : j2 < 3),
      (j2 = j1 + 1 ∨ (j1 = 0 ∧ j2 = 3 - 1)) →
      ¬ G.Adj (σ ((fArr4_3 k0 k1 k2 k3 u0 u1 u2) ⟨4 + j1, by omega⟩)) (σ ((fArr4_3 k0 k1 k2 k3 u0 u1 u2) ⟨4 + j2, by omega⟩)) := by
  obtain ⟨m0, m1, m2⟩ := comp3_m_nonadj (by simp : k3 ∈ ({k0, k1, k2, k3} : Finset V)) hM hd hσ
  intro j1 j2 hj12 hj2 hcond
  interval_cases j2 <;> interval_cases j1 <;> (try dsimp [fArr4_3]) <;> first | omega | exact m0 | exact m1 | exact adj_symm_not G m2
private lemma mkCtx4_3 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 w u0 u1 u2 : V)
    (hK : IsComp4 C k0 k1 k2 k3) (hM : IsComp3 C u0 u1 u2)
    (hd : Dj4 k0 k1 k2 k3 {u0, u1, u2}) (σ : Equiv.Perm V) (hσ : AlmOn C G k3 k0 σ)
    (hnp : ¬ Packs C G) (e0_mask sc0 : ℕ) (has_nw1 has_z : Bool) (σ1 σ2 σ3 : Equiv.Perm V)
    (hne_0_2 : e0_mask.testBit 2 = false → ¬ G.Adj (σ k0) (σ k2))
    (hne_0_3 : e0_mask.testBit 3 = false → ¬ G.Adj (σ k0) (σ k3))
    (hne_1_3 : e0_mask.testBit 8 = false → ¬ G.Adj (σ k1) (σ k3))
    (hnw_false : has_nw1 = false)
    : ∃ ctx : ReflCtx V, ctx.L0 = 4 ∧ ctx.m = 3 ∧ ctx.e0_mask = e0_mask ∧ ctx.sc0 = sc0 ∧ ctx.has_nw1 = has_nw1 ∧ ctx.has_z = has_z ∧ ctx.ebL = (eb4_3 G σ k0 k1 k2 k3 u0 u1 u2) :=
  ⟨{
    C := C, G := G, decG := inferInstance, L0 := 4, m := 3,
    e0_mask := e0_mask, sc0 := sc0, has_nw1 := has_nw1, has_z := has_z,
    ebL := (eb4_3 G σ k0 k1 k2 k3 u0 u1 u2), hL0_pos := by decide, hm_pos := by decide,
    f := (fArr4_3 k0 k1 k2 k3 u0 u1 u2), hf := fArr4_3_inj hK hM hd, kV := (kV4 k0 k1 k2 k3 w),
    hkV_eq := by intro i hi; interval_cases i <;> rfl,
    σ := σ, σr := (fun r => match r with | 1 => σ1 | 2 => σ2 | 3 => σ3 | _ => σ),
    hnp := hnp,
    hrow_spec := row_spec4 hnw_false,
    hσr0 := fun _ => rfl,
    hσr_alm := by rintro r (rfl | ⟨hnw, -⟩); exact hσ; (rw [hnw_false] at hnw; simp at hnw),
    hσr_k := by rintro r (rfl | ⟨hnw, -⟩) i hi; (interval_cases i <;> rfl); (rw [hnw_false] at hnw; simp at hnw),
    hσr_m := by rintro r (rfl | ⟨hnw, -⟩) j hj; (interval_cases j <;> rfl); (rw [hnw_false] at hnw; simp at hnw),
    hk_path := k_path4 hK hσ,
    hk_e0 := k_e0_4 hne_0_2 hne_0_3 hne_1_3,
    hnw1 := fun h => by rw [hnw_false] at h; simp at h,
    hm_edge := fArr4_3_hm hM hd hσ,
    heb := by rintro ru j hj (hlt | ⟨hnw, -⟩); (interval_cases ru <;> interval_cases j <;> rfl); (rw [hnw_false] at hnw; simp at hnw),
    hcl_pack := fArr4_3_hcl hK hM,
    halm_min := fun h5 => by omega, hz_prop := fun _ h5 => by omega }, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
abbrev fArr4_4 {V : Type} (k0 k1 k2 k3 u0 u1 u2 u3 : V) (idx : Fin 8) : V := match idx.1 with | 0 => k0 | 1 => k1 | 2 => k2 | 3 => k3 | 4 => u0 | 5 => u1 | 6 => u2 | _ => u3
abbrev eb4_4 {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj] (σ : Equiv.Perm V) (k0 k1 k2 k3 u0 u1 u2 u3 : V) : List Bool := [decide (G.Adj (σ k0) (σ u0)), decide (G.Adj (σ k0) (σ u1)), decide (G.Adj (σ k0) (σ u2)), decide (G.Adj (σ k0) (σ u3)), decide (G.Adj (σ k1) (σ u0)), decide (G.Adj (σ k1) (σ u1)), decide (G.Adj (σ k1) (σ u2)), decide (G.Adj (σ k1) (σ u3)), decide (G.Adj (σ k2) (σ u0)), decide (G.Adj (σ k2) (σ u1)), decide (G.Adj (σ k2) (σ u2)), decide (G.Adj (σ k2) (σ u3)), decide (G.Adj (σ k3) (σ u0)), decide (G.Adj (σ k3) (σ u1)), decide (G.Adj (σ k3) (σ u2)), decide (G.Adj (σ k3) (σ u3))]
private lemma wSum_eb4_4 {V : Type} [Fintype V] [DecidableEq V] {C : SimpleGraph V} (G : SimpleGraph V) [DecidableRel G.Adj] (σ : Equiv.Perm V) (w0 w1 w2 w3 : ℕ) (k0 k1 k2 k3 u0 u1 u2 u3 : V) (hM : IsComp4 C u0 u1 u2 u3) :
    wSumBool [w0, w0, w0, w0, w1, w1, w1, w1, w2, w2, w2, w2, w3, w3, w3, w3] (eb4_4 G σ k0 k1 k2 k3 u0 u1 u2 u3) = w0 * rCount G σ k0 {u0, u1, u2, u3} + w1 * rCount G σ k1 {u0, u1, u2, u3} + w2 * rCount G σ k2 {u0, u1, u2, u3} + w3 * rCount G σ k3 {u0, u1, u2, u3} := by
  simp only [wSumBool, if_decide_eq_mul_b01, rCount_comp4 G σ _ u0 u1 u2 u3 hM]; ring
private lemma fArr4_4_inj {V : Type} [DecidableEq V] {C : SimpleGraph V}
    {k0 k1 k2 k3 u0 u1 u2 u3 : V} (hK : IsComp4 C k0 k1 k2 k3) (hM : IsComp4 C u0 u1 u2 u3)
    (hd : Dj4 k0 k1 k2 k3 {u0, u1, u2, u3}) : Function.Injective (fArr4_4 k0 k1 k2 k3 u0 u1 u2 u3) := by
  rcases hK with ⟨hk01, hk02, hk03, hk12, hk13, hk23, -⟩
  rcases hM with ⟨hm01, hm02, hm03, hm12, hm13, hm23, -⟩
  simp only [Dj4, Finset.disjoint_insert_left, Finset.disjoint_singleton_left, mem_insert, mem_singleton, not_or] at hd
  rcases hd with ⟨⟨hkm00, hkm01, hkm02, hkm03⟩, ⟨hkm10, hkm11, hkm12, hkm13⟩, ⟨hkm20, hkm21, hkm22, hkm23⟩, ⟨hkm30, hkm31, hkm32, hkm33⟩⟩
  intro i j hij; fin_cases i <;> fin_cases j <;> simp only [fArr4_4] at hij ⊢
  all_goals first | rfl | exact absurd hij (by assumption) | exact absurd hij.symm (by assumption)
private lemma fArr4_4_hcl {V : Type} {C : SimpleGraph V} {k0 k1 k2 k3 u0 u1 u2 u3 : V}
    (hK : IsComp4 C k0 k1 k2 k3) (hM : IsComp4 C u0 u1 u2 u3) :
    ∀ idx1 : Fin 8, ∀ b, C.Adj ((fArr4_4 k0 k1 k2 k3 u0 u1 u2 u3) idx1) b →
      ∃ idx2 : Fin 8, (fArr4_4 k0 k1 k2 k3 u0 u1 u2 u3) idx2 = b ∧
        hasUndirEdge (cEdgesK 4 ++ cEdgesM 4 4) idx1.1 idx2.1 = true := by
  rcases hK with ⟨_, _, _, _, _, _, hkn0, hkn1, hkn2, hkn3⟩
  rcases hM with ⟨_, _, _, _, _, _, hmn0, hmn1, hmn2, hmn3⟩
  intro idx1 b hab; fin_cases idx1 <;> dsimp [fArr4_4] at hab
  · rcases (hkn0 b).1 hab with rfl | rfl
    · exact ⟨⟨3, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨1, by decide⟩, rfl, rfl⟩
  · rcases (hkn1 b).1 hab with rfl | rfl
    · exact ⟨⟨0, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨2, by decide⟩, rfl, rfl⟩
  · rcases (hkn2 b).1 hab with rfl | rfl
    · exact ⟨⟨1, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨3, by decide⟩, rfl, rfl⟩
  · rcases (hkn3 b).1 hab with rfl | rfl
    · exact ⟨⟨2, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨0, by decide⟩, rfl, rfl⟩
  · rcases (hmn0 b).1 hab with rfl | rfl
    · exact ⟨⟨7, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨5, by decide⟩, rfl, rfl⟩
  · rcases (hmn1 b).1 hab with rfl | rfl
    · exact ⟨⟨4, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨6, by decide⟩, rfl, rfl⟩
  · rcases (hmn2 b).1 hab with rfl | rfl
    · exact ⟨⟨5, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨7, by decide⟩, rfl, rfl⟩
  · rcases (hmn3 b).1 hab with rfl | rfl
    · exact ⟨⟨6, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨4, by decide⟩, rfl, rfl⟩
private lemma fArr4_4_hm {V : Type} [DecidableEq V] {C G : SimpleGraph V} {k0 k1 k2 k3 u0 u1 u2 u3 : V}
    {σ : Equiv.Perm V} (hM : IsComp4 C u0 u1 u2 u3) (hd : Dj4 k0 k1 k2 k3 {u0, u1, u2, u3})
    (hσ : AlmOn C G k3 k0 σ) : ∀ j1 j2 (hj12 : j1 < j2) (hj2 : j2 < 4),
      (j2 = j1 + 1 ∨ (j1 = 0 ∧ j2 = 4 - 1)) →
      ¬ G.Adj (σ ((fArr4_4 k0 k1 k2 k3 u0 u1 u2 u3) ⟨4 + j1, by omega⟩)) (σ ((fArr4_4 k0 k1 k2 k3 u0 u1 u2 u3) ⟨4 + j2, by omega⟩)) := by
  obtain ⟨m0, m1, m2, m3⟩ := comp4_m_nonadj (by simp : k3 ∈ ({k0, k1, k2, k3} : Finset V)) hM hd hσ
  intro j1 j2 hj12 hj2 hcond
  interval_cases j2 <;> interval_cases j1 <;> (try dsimp [fArr4_4]) <;> first | omega | exact m0 | exact m1 | exact m2 | exact adj_symm_not G m3
private lemma mkCtx4_4 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 w u0 u1 u2 u3 : V)
    (hK : IsComp4 C k0 k1 k2 k3) (hM : IsComp4 C u0 u1 u2 u3)
    (hd : Dj4 k0 k1 k2 k3 {u0, u1, u2, u3}) (σ : Equiv.Perm V) (hσ : AlmOn C G k3 k0 σ)
    (hnp : ¬ Packs C G) (e0_mask sc0 : ℕ) (has_nw1 has_z : Bool) (σ1 σ2 σ3 : Equiv.Perm V)
    (hne_0_2 : e0_mask.testBit 2 = false → ¬ G.Adj (σ k0) (σ k2))
    (hne_0_3 : e0_mask.testBit 3 = false → ¬ G.Adj (σ k0) (σ k3))
    (hne_1_3 : e0_mask.testBit 8 = false → ¬ G.Adj (σ k1) (σ k3))
    (hnw_false : has_nw1 = false)
    : ∃ ctx : ReflCtx V, ctx.L0 = 4 ∧ ctx.m = 4 ∧ ctx.e0_mask = e0_mask ∧ ctx.sc0 = sc0 ∧ ctx.has_nw1 = has_nw1 ∧ ctx.has_z = has_z ∧ ctx.ebL = (eb4_4 G σ k0 k1 k2 k3 u0 u1 u2 u3) :=
  ⟨{
    C := C, G := G, decG := inferInstance, L0 := 4, m := 4,
    e0_mask := e0_mask, sc0 := sc0, has_nw1 := has_nw1, has_z := has_z,
    ebL := (eb4_4 G σ k0 k1 k2 k3 u0 u1 u2 u3), hL0_pos := by decide, hm_pos := by decide,
    f := (fArr4_4 k0 k1 k2 k3 u0 u1 u2 u3), hf := fArr4_4_inj hK hM hd, kV := (kV4 k0 k1 k2 k3 w),
    hkV_eq := by intro i hi; interval_cases i <;> rfl,
    σ := σ, σr := (fun r => match r with | 1 => σ1 | 2 => σ2 | 3 => σ3 | _ => σ),
    hnp := hnp,
    hrow_spec := row_spec4 hnw_false,
    hσr0 := fun _ => rfl,
    hσr_alm := by rintro r (rfl | ⟨hnw, -⟩); exact hσ; (rw [hnw_false] at hnw; simp at hnw),
    hσr_k := by rintro r (rfl | ⟨hnw, -⟩) i hi; (interval_cases i <;> rfl); (rw [hnw_false] at hnw; simp at hnw),
    hσr_m := by rintro r (rfl | ⟨hnw, -⟩) j hj; (interval_cases j <;> rfl); (rw [hnw_false] at hnw; simp at hnw),
    hk_path := k_path4 hK hσ,
    hk_e0 := k_e0_4 hne_0_2 hne_0_3 hne_1_3,
    hnw1 := fun h => by rw [hnw_false] at h; simp at h,
    hm_edge := fArr4_4_hm hM hd hσ,
    heb := by rintro ru j hj (hlt | ⟨hnw, -⟩); (interval_cases ru <;> interval_cases j <;> rfl); (rw [hnw_false] at hnw; simp at hnw),
    hcl_pack := fArr4_4_hcl hK hM,
    halm_min := fun h5 => by omega, hz_prop := fun _ h5 => by omega }, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
abbrev fArr4_5 {V : Type} (k0 k1 k2 k3 u0 u1 u2 u3 u4 : V) (idx : Fin 9) : V := match idx.1 with | 0 => k0 | 1 => k1 | 2 => k2 | 3 => k3 | 4 => u0 | 5 => u1 | 6 => u2 | 7 => u3 | _ => u4
abbrev eb4_5 {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj] (σ : Equiv.Perm V) (k0 k1 k2 k3 u0 u1 u2 u3 u4 : V) : List Bool := [decide (G.Adj (σ k0) (σ u0)), decide (G.Adj (σ k0) (σ u1)), decide (G.Adj (σ k0) (σ u2)), decide (G.Adj (σ k0) (σ u3)), decide (G.Adj (σ k0) (σ u4)), decide (G.Adj (σ k1) (σ u0)), decide (G.Adj (σ k1) (σ u1)), decide (G.Adj (σ k1) (σ u2)), decide (G.Adj (σ k1) (σ u3)), decide (G.Adj (σ k1) (σ u4)), decide (G.Adj (σ k2) (σ u0)), decide (G.Adj (σ k2) (σ u1)), decide (G.Adj (σ k2) (σ u2)), decide (G.Adj (σ k2) (σ u3)), decide (G.Adj (σ k2) (σ u4)), decide (G.Adj (σ k3) (σ u0)), decide (G.Adj (σ k3) (σ u1)), decide (G.Adj (σ k3) (σ u2)), decide (G.Adj (σ k3) (σ u3)), decide (G.Adj (σ k3) (σ u4))]
private lemma wSum_eb4_5 {V : Type} [Fintype V] [DecidableEq V] {C : SimpleGraph V} (G : SimpleGraph V) [DecidableRel G.Adj] (σ : Equiv.Perm V) (w0 w1 w2 w3 : ℕ) (k0 k1 k2 k3 u0 u1 u2 u3 u4 : V) (hM : IsComp5 C u0 u1 u2 u3 u4) :
    wSumBool [w0, w0, w0, w0, w0, w1, w1, w1, w1, w1, w2, w2, w2, w2, w2, w3, w3, w3, w3, w3] (eb4_5 G σ k0 k1 k2 k3 u0 u1 u2 u3 u4) = w0 * rCount G σ k0 {u0, u1, u2, u3, u4} + w1 * rCount G σ k1 {u0, u1, u2, u3, u4} + w2 * rCount G σ k2 {u0, u1, u2, u3, u4} + w3 * rCount G σ k3 {u0, u1, u2, u3, u4} := by
  simp only [wSumBool, if_decide_eq_mul_b01, rCount_comp5 G σ _ u0 u1 u2 u3 u4 hM]; ring
private lemma fArr4_5_inj {V : Type} [DecidableEq V] {C : SimpleGraph V}
    {k0 k1 k2 k3 u0 u1 u2 u3 u4 : V} (hK : IsComp4 C k0 k1 k2 k3) (hM : IsComp5 C u0 u1 u2 u3 u4)
    (hd : Dj4 k0 k1 k2 k3 {u0, u1, u2, u3, u4}) : Function.Injective (fArr4_5 k0 k1 k2 k3 u0 u1 u2 u3 u4) := by
  rcases hK with ⟨hk01, hk02, hk03, hk12, hk13, hk23, -⟩
  rcases hM with ⟨hm01, hm02, hm03, hm04, hm12, hm13, hm14, hm23, hm24, hm34, -⟩
  simp only [Dj4, Finset.disjoint_insert_left, Finset.disjoint_singleton_left, mem_insert, mem_singleton, not_or] at hd
  rcases hd with ⟨⟨hkm00, hkm01, hkm02, hkm03, hkm04⟩, ⟨hkm10, hkm11, hkm12, hkm13, hkm14⟩, ⟨hkm20, hkm21, hkm22, hkm23, hkm24⟩, ⟨hkm30, hkm31, hkm32, hkm33, hkm34⟩⟩
  intro i j hij; fin_cases i <;> fin_cases j <;> simp only [fArr4_5] at hij ⊢
  all_goals first | rfl | exact absurd hij (by assumption) | exact absurd hij.symm (by assumption)
private lemma fArr4_5_hcl {V : Type} {C : SimpleGraph V} {k0 k1 k2 k3 u0 u1 u2 u3 u4 : V}
    (hK : IsComp4 C k0 k1 k2 k3) (hM : IsComp5 C u0 u1 u2 u3 u4) :
    ∀ idx1 : Fin 9, ∀ b, C.Adj ((fArr4_5 k0 k1 k2 k3 u0 u1 u2 u3 u4) idx1) b →
      ∃ idx2 : Fin 9, (fArr4_5 k0 k1 k2 k3 u0 u1 u2 u3 u4) idx2 = b ∧
        hasUndirEdge (cEdgesK 4 ++ cEdgesM 4 5) idx1.1 idx2.1 = true := by
  rcases hK with ⟨_, _, _, _, _, _, hkn0, hkn1, hkn2, hkn3⟩
  rcases hM with ⟨_, _, _, _, _, _, _, _, _, _, hmn0, hmn1, hmn2, hmn3, hmn4⟩
  intro idx1 b hab; fin_cases idx1 <;> dsimp [fArr4_5] at hab
  · rcases (hkn0 b).1 hab with rfl | rfl
    · exact ⟨⟨3, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨1, by decide⟩, rfl, rfl⟩
  · rcases (hkn1 b).1 hab with rfl | rfl
    · exact ⟨⟨0, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨2, by decide⟩, rfl, rfl⟩
  · rcases (hkn2 b).1 hab with rfl | rfl
    · exact ⟨⟨1, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨3, by decide⟩, rfl, rfl⟩
  · rcases (hkn3 b).1 hab with rfl | rfl
    · exact ⟨⟨2, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨0, by decide⟩, rfl, rfl⟩
  · rcases (hmn0 b).1 hab with rfl | rfl
    · exact ⟨⟨8, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨5, by decide⟩, rfl, rfl⟩
  · rcases (hmn1 b).1 hab with rfl | rfl
    · exact ⟨⟨4, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨6, by decide⟩, rfl, rfl⟩
  · rcases (hmn2 b).1 hab with rfl | rfl
    · exact ⟨⟨5, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨7, by decide⟩, rfl, rfl⟩
  · rcases (hmn3 b).1 hab with rfl | rfl
    · exact ⟨⟨6, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨8, by decide⟩, rfl, rfl⟩
  · rcases (hmn4 b).1 hab with rfl | rfl
    · exact ⟨⟨7, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨4, by decide⟩, rfl, rfl⟩
private lemma fArr4_5_hm {V : Type} [DecidableEq V] {C G : SimpleGraph V} {k0 k1 k2 k3 u0 u1 u2 u3 u4 : V}
    {σ : Equiv.Perm V} (hM : IsComp5 C u0 u1 u2 u3 u4) (hd : Dj4 k0 k1 k2 k3 {u0, u1, u2, u3, u4})
    (hσ : AlmOn C G k3 k0 σ) : ∀ j1 j2 (hj12 : j1 < j2) (hj2 : j2 < 5),
      (j2 = j1 + 1 ∨ (j1 = 0 ∧ j2 = 5 - 1)) →
      ¬ G.Adj (σ ((fArr4_5 k0 k1 k2 k3 u0 u1 u2 u3 u4) ⟨4 + j1, by omega⟩)) (σ ((fArr4_5 k0 k1 k2 k3 u0 u1 u2 u3 u4) ⟨4 + j2, by omega⟩)) := by
  obtain ⟨m0, m1, m2, m3, m4⟩ := comp5_m_nonadj (by simp : k3 ∈ ({k0, k1, k2, k3} : Finset V)) hM hd hσ
  intro j1 j2 hj12 hj2 hcond
  interval_cases j2 <;> interval_cases j1 <;> (try dsimp [fArr4_5]) <;> first | omega | exact m0 | exact m1 | exact m2 | exact m3 | exact adj_symm_not G m4
private lemma mkCtx4_5 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 w u0 u1 u2 u3 u4 : V)
    (hK : IsComp4 C k0 k1 k2 k3) (hM : IsComp5 C u0 u1 u2 u3 u4)
    (hd : Dj4 k0 k1 k2 k3 {u0, u1, u2, u3, u4}) (σ : Equiv.Perm V) (hσ : AlmOn C G k3 k0 σ)
    (hnp : ¬ Packs C G) (e0_mask sc0 : ℕ) (has_nw1 has_z : Bool) (σ1 σ2 σ3 : Equiv.Perm V)
    (hne_0_2 : e0_mask.testBit 2 = false → ¬ G.Adj (σ k0) (σ k2))
    (hne_0_3 : e0_mask.testBit 3 = false → ¬ G.Adj (σ k0) (σ k3))
    (hne_1_3 : e0_mask.testBit 8 = false → ¬ G.Adj (σ k1) (σ k3))
    (hnw_false : has_nw1 = false)
    : ∃ ctx : ReflCtx V, ctx.L0 = 4 ∧ ctx.m = 5 ∧ ctx.e0_mask = e0_mask ∧ ctx.sc0 = sc0 ∧ ctx.has_nw1 = has_nw1 ∧ ctx.has_z = has_z ∧ ctx.ebL = (eb4_5 G σ k0 k1 k2 k3 u0 u1 u2 u3 u4) :=
  ⟨{
    C := C, G := G, decG := inferInstance, L0 := 4, m := 5,
    e0_mask := e0_mask, sc0 := sc0, has_nw1 := has_nw1, has_z := has_z,
    ebL := (eb4_5 G σ k0 k1 k2 k3 u0 u1 u2 u3 u4), hL0_pos := by decide, hm_pos := by decide,
    f := (fArr4_5 k0 k1 k2 k3 u0 u1 u2 u3 u4), hf := fArr4_5_inj hK hM hd, kV := (kV4 k0 k1 k2 k3 w),
    hkV_eq := by intro i hi; interval_cases i <;> rfl,
    σ := σ, σr := (fun r => match r with | 1 => σ1 | 2 => σ2 | 3 => σ3 | _ => σ),
    hnp := hnp,
    hrow_spec := row_spec4 hnw_false,
    hσr0 := fun _ => rfl,
    hσr_alm := by rintro r (rfl | ⟨hnw, -⟩); exact hσ; (rw [hnw_false] at hnw; simp at hnw),
    hσr_k := by rintro r (rfl | ⟨hnw, -⟩) i hi; (interval_cases i <;> rfl); (rw [hnw_false] at hnw; simp at hnw),
    hσr_m := by rintro r (rfl | ⟨hnw, -⟩) j hj; (interval_cases j <;> rfl); (rw [hnw_false] at hnw; simp at hnw),
    hk_path := k_path4 hK hσ,
    hk_e0 := k_e0_4 hne_0_2 hne_0_3 hne_1_3,
    hnw1 := fun h => by rw [hnw_false] at h; simp at h,
    hm_edge := fArr4_5_hm hM hd hσ,
    heb := by rintro ru j hj (hlt | ⟨hnw, -⟩); (interval_cases ru <;> interval_cases j <;> rfl); (rw [hnw_false] at hnw; simp at hnw),
    hcl_pack := fArr4_5_hcl hK hM,
    halm_min := fun h5 => by omega, hz_prop := fun _ h5 => by omega }, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
abbrev fArr5_1 {V : Type} (k0 k1 k2 k3 k4 u0 : V) (idx : Fin 6) : V := match idx.1 with | 0 => k0 | 1 => k1 | 2 => k2 | 3 => k3 | 4 => k4 | _ => u0
abbrev eb5_1 {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj] (σ : Equiv.Perm V) (k0 k1 k2 k3 k4 w u0 : V) : List Bool := [decide (G.Adj (σ k0) (σ u0)), decide (G.Adj (σ k1) (σ u0)), decide (G.Adj (σ k2) (σ u0)), decide (G.Adj (σ k3) (σ u0)), decide (G.Adj (σ k4) (σ u0)), decide (G.Adj (σ w) (σ u0))]
private lemma wSum_eb5_1 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (σ : Equiv.Perm V) (w0 w1 w2 w3 w4 w5 : ℕ) (k0 k1 k2 k3 k4 w u0 : V) :
    wSumBool [w0, w1, w2, w3, w4, w5] (eb5_1 G σ k0 k1 k2 k3 k4 w u0) = w0 * rCount G σ k0 {u0} + w1 * rCount G σ k1 {u0} + w2 * rCount G σ k2 {u0} + w3 * rCount G σ k3 {u0} + w4 * rCount G σ k4 {u0} + w5 * rCount G σ w {u0} := by
  simp only [wSumBool, if_decide_eq_mul_b01, rCount_1]; ring
private lemma fArr5_1_inj {V : Type} [DecidableEq V] {C : SimpleGraph V}
    {k0 k1 k2 k3 k4 u0 : V} (hK : IsComp5 C k0 k1 k2 k3 k4) (_hM : IsComp1 C u0)
    (hd : Dj5 k0 k1 k2 k3 k4 {u0}) : Function.Injective (fArr5_1 k0 k1 k2 k3 k4 u0) := by
  rcases hK with ⟨hk01, hk02, hk03, hk04, hk12, hk13, hk14, hk23, hk24, hk34, -⟩
  simp only [Dj5, Finset.disjoint_insert_left, Finset.disjoint_singleton_left, mem_singleton] at hd
  rcases hd with ⟨hkm00, hkm10, hkm20, hkm30, hkm40⟩
  intro i j hij; fin_cases i <;> fin_cases j <;> simp only [fArr5_1] at hij ⊢
  all_goals first | rfl | exact absurd hij (by assumption) | exact absurd hij.symm (by assumption)
private lemma fArr5_1_hcl {V : Type} {C : SimpleGraph V} {k0 k1 k2 k3 k4 u0 : V}
    (hK : IsComp5 C k0 k1 k2 k3 k4) (hM : IsComp1 C u0) :
    ∀ idx1 : Fin 6, ∀ b, C.Adj ((fArr5_1 k0 k1 k2 k3 k4 u0) idx1) b →
      ∃ idx2 : Fin 6, (fArr5_1 k0 k1 k2 k3 k4 u0) idx2 = b ∧
        hasUndirEdge (cEdgesK 5 ++ cEdgesM 5 1) idx1.1 idx2.1 = true := by
  rcases hK with ⟨_, _, _, _, _, _, _, _, _, _, hkn0, hkn1, hkn2, hkn3, hkn4⟩
  intro idx1 b hab; fin_cases idx1 <;> dsimp [fArr5_1] at hab
  · rcases (hkn0 b).1 hab with rfl | rfl
    · exact ⟨⟨4, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨1, by decide⟩, rfl, rfl⟩
  · rcases (hkn1 b).1 hab with rfl | rfl
    · exact ⟨⟨0, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨2, by decide⟩, rfl, rfl⟩
  · rcases (hkn2 b).1 hab with rfl | rfl
    · exact ⟨⟨1, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨3, by decide⟩, rfl, rfl⟩
  · rcases (hkn3 b).1 hab with rfl | rfl
    · exact ⟨⟨2, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨4, by decide⟩, rfl, rfl⟩
  · rcases (hkn4 b).1 hab with rfl | rfl
    · exact ⟨⟨3, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨0, by decide⟩, rfl, rfl⟩
  · exact absurd hab (hM b)
private lemma mkCtx5_1 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 k4 w u0 : V)
    (hK : IsComp5 C k0 k1 k2 k3 k4) (hM : IsComp1 C u0)
    (hd : Dj5 k0 k1 k2 k3 k4 {u0}) (σ : Equiv.Perm V) (hσ : AlmOn C G k4 k0 σ)
    (hnp : ¬ Packs C G) (e0_mask sc0 : ℕ) (has_nw1 has_z : Bool) (σ1 σ2 σ3 : Equiv.Perm V)
    (hne_0_2 : e0_mask.testBit 2 = false → ¬ G.Adj (σ k0) (σ k2))
    (hne_0_3 : e0_mask.testBit 3 = false → ¬ G.Adj (σ k0) (σ k3))
    (hne_0_4 : e0_mask.testBit 4 = false → ¬ G.Adj (σ k0) (σ k4))
    (hne_1_3 : e0_mask.testBit 8 = false → ¬ G.Adj (σ k1) (σ k3))
    (hne_1_4 : e0_mask.testBit 9 = false → ¬ G.Adj (σ k1) (σ k4))
    (hne_2_4 : e0_mask.testBit 14 = false → ¬ G.Adj (σ k2) (σ k4))
    (hnw1 : has_nw1 = true → ¬ G.Adj (σ k1) (σ w))
    (hremap : has_nw1 = true →
      (AlmOn C G k4 k0 σ1 ∧ Fix5 σ1 σ w k1 k2 k3 k4 k0 k1 k2 k3 k4 ∧ EqOn σ1 σ {u0}) ∧
      (AlmOn C G k4 k0 σ2 ∧ Fix5 σ2 σ w k1 k0 k3 k4 k0 k1 k2 k3 k4 ∧ EqOn σ2 σ {u0}) ∧
      (AlmOn C G k4 k0 σ3 ∧ Fix5 σ3 σ w k1 k2 k3 k0 k0 k1 k2 k3 k4 ∧ EqOn σ3 σ {u0}))
    (halm : 0 < sc0 → sc0 ≤ kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4) ∧ MinSc C G k0 k1 k2 k3 k4 σ)
    (hz0 : has_z = true → ZProp C G k0 k1 k2 k3 k4 σ {u0})
    : ∃ ctx : ReflCtx V, ctx.L0 = 5 ∧ ctx.m = 1 ∧ ctx.e0_mask = e0_mask ∧ ctx.sc0 = sc0 ∧ ctx.has_nw1 = has_nw1 ∧ ctx.has_z = has_z ∧ ctx.ebL = (eb5_1 G σ k0 k1 k2 k3 k4 w u0) :=
  ⟨{
    C := C, G := G, decG := inferInstance, L0 := 5, m := 1,
    e0_mask := e0_mask, sc0 := sc0, has_nw1 := has_nw1, has_z := has_z,
    ebL := (eb5_1 G σ k0 k1 k2 k3 k4 w u0), hL0_pos := by decide, hm_pos := by decide,
    f := (fArr5_1 k0 k1 k2 k3 k4 u0), hf := fArr5_1_inj hK hM hd, kV := (kV5 k0 k1 k2 k3 k4 w),
    hkV_eq := by intro i hi; interval_cases i <;> rfl,
    σ := σ, σr := (fun r => match r with | 1 => σ1 | 2 => σ2 | 3 => σ3 | _ => σ),
    hnp := hnp,
    hrow_spec := row_spec5,
    hσr0 := fun _ => rfl,
    hσr_alm := by rintro r (rfl | ⟨hnw, rfl | rfl | rfl⟩); exact hσ; exact (hremap hnw).1.1; exact (hremap hnw).2.1.1; exact (hremap hnw).2.2.1,
    hσr_k := by
      rintro r (rfl | ⟨hnw, rfl | rfl | rfl⟩) i hi
      · interval_cases i <;> rfl
      · have hk := (hremap hnw).1.2.1; interval_cases i <;> (try dsimp [rowOf, fArr5_1]) <;> first | exact hk.1 | exact hk.2.1 | exact hk.2.2.1 | exact hk.2.2.2.1 | exact hk.2.2.2.2
      · have hk := (hremap hnw).2.1.2.1; interval_cases i <;> (try dsimp [rowOf, fArr5_1]) <;> first | exact hk.1 | exact hk.2.1 | exact hk.2.2.1 | exact hk.2.2.2.1 | exact hk.2.2.2.2
      · have hk := (hremap hnw).2.2.2.1; interval_cases i <;> (try dsimp [rowOf, fArr5_1]) <;> first | exact hk.1 | exact hk.2.1 | exact hk.2.2.1 | exact hk.2.2.2.1 | exact hk.2.2.2.2,
    hσr_m := by
      rintro r (rfl | ⟨hnw, rfl | rfl | rfl⟩) j hj
      · interval_cases j; rfl
      · have hu := (hremap hnw).1.2.2; interval_cases j; exact hu u0 (mem_singleton_self _)
      · have hu := (hremap hnw).2.1.2.2; interval_cases j; exact hu u0 (mem_singleton_self _)
      · have hu := (hremap hnw).2.2.2.2; interval_cases j; exact hu u0 (mem_singleton_self _),
    hk_path := k_path5 hK hσ,
    hk_e0 := k_e0_5 hne_0_2 hne_0_3 hne_0_4 hne_1_3 hne_1_4 hne_2_4,
    hnw1 := hnw1,
    hm_edge := fun j1 j2 hj12 hj2 _ => by omega,
    heb := by rintro ru j hj (hlt | ⟨_, rfl⟩); (interval_cases ru <;> interval_cases j <;> rfl); (interval_cases j; rfl),
    hcl_pack := fArr5_1_hcl hK hM,
    halm_min := fun _ hpos => halm hpos,
    hz_prop := by intro hhz _ j hj; interval_cases j; exact ⟨fun _ => hM, fun hle => absurd le_rfl hle, hz0 hhz u0 (mem_singleton_self _)⟩ }, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
abbrev fArr5_3 {V : Type} (k0 k1 k2 k3 k4 u0 u1 u2 : V) (idx : Fin 8) : V := match idx.1 with | 0 => k0 | 1 => k1 | 2 => k2 | 3 => k3 | 4 => k4 | 5 => u0 | 6 => u1 | _ => u2
abbrev eb5_3 {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj] (σ : Equiv.Perm V) (k0 k1 k2 k3 k4 w u0 u1 u2 : V) : List Bool := [decide (G.Adj (σ k0) (σ u0)), decide (G.Adj (σ k0) (σ u1)), decide (G.Adj (σ k0) (σ u2)), decide (G.Adj (σ k1) (σ u0)), decide (G.Adj (σ k1) (σ u1)), decide (G.Adj (σ k1) (σ u2)), decide (G.Adj (σ k2) (σ u0)), decide (G.Adj (σ k2) (σ u1)), decide (G.Adj (σ k2) (σ u2)), decide (G.Adj (σ k3) (σ u0)), decide (G.Adj (σ k3) (σ u1)), decide (G.Adj (σ k3) (σ u2)), decide (G.Adj (σ k4) (σ u0)), decide (G.Adj (σ k4) (σ u1)), decide (G.Adj (σ k4) (σ u2)), decide (G.Adj (σ w) (σ u0)), decide (G.Adj (σ w) (σ u1)), decide (G.Adj (σ w) (σ u2))]
private lemma wSum_eb5_3 {V : Type} [Fintype V] [DecidableEq V] {C : SimpleGraph V} (G : SimpleGraph V) [DecidableRel G.Adj] (σ : Equiv.Perm V) (w0 w1 w2 w3 w4 w5 : ℕ) (k0 k1 k2 k3 k4 w u0 u1 u2 : V) (hM : IsComp3 C u0 u1 u2) :
    wSumBool [w0, w0, w0, w1, w1, w1, w2, w2, w2, w3, w3, w3, w4, w4, w4, w5, w5, w5] (eb5_3 G σ k0 k1 k2 k3 k4 w u0 u1 u2) = w0 * rCount G σ k0 {u0, u1, u2} + w1 * rCount G σ k1 {u0, u1, u2} + w2 * rCount G σ k2 {u0, u1, u2} + w3 * rCount G σ k3 {u0, u1, u2} + w4 * rCount G σ k4 {u0, u1, u2} + w5 * rCount G σ w {u0, u1, u2} := by
  simp only [wSumBool, if_decide_eq_mul_b01, rCount_comp3 G σ _ u0 u1 u2 hM]; ring
private lemma fArr5_3_inj {V : Type} [DecidableEq V] {C : SimpleGraph V}
    {k0 k1 k2 k3 k4 u0 u1 u2 : V} (hK : IsComp5 C k0 k1 k2 k3 k4) (hM : IsComp3 C u0 u1 u2)
    (hd : Dj5 k0 k1 k2 k3 k4 {u0, u1, u2}) : Function.Injective (fArr5_3 k0 k1 k2 k3 k4 u0 u1 u2) := by
  rcases hK with ⟨hk01, hk02, hk03, hk04, hk12, hk13, hk14, hk23, hk24, hk34, -⟩
  rcases hM with ⟨hm01, hm02, hm12, -⟩
  simp only [Dj5, Finset.disjoint_insert_left, Finset.disjoint_singleton_left, mem_insert, mem_singleton, not_or] at hd
  rcases hd with ⟨⟨hkm00, hkm01, hkm02⟩, ⟨hkm10, hkm11, hkm12⟩, ⟨hkm20, hkm21, hkm22⟩, ⟨hkm30, hkm31, hkm32⟩, ⟨hkm40, hkm41, hkm42⟩⟩
  intro i j hij; fin_cases i <;> fin_cases j <;> simp only [fArr5_3] at hij ⊢
  all_goals first | rfl | exact absurd hij (by assumption) | exact absurd hij.symm (by assumption)
private lemma fArr5_3_hcl {V : Type} {C : SimpleGraph V} {k0 k1 k2 k3 k4 u0 u1 u2 : V}
    (hK : IsComp5 C k0 k1 k2 k3 k4) (hM : IsComp3 C u0 u1 u2) :
    ∀ idx1 : Fin 8, ∀ b, C.Adj ((fArr5_3 k0 k1 k2 k3 k4 u0 u1 u2) idx1) b →
      ∃ idx2 : Fin 8, (fArr5_3 k0 k1 k2 k3 k4 u0 u1 u2) idx2 = b ∧
        hasUndirEdge (cEdgesK 5 ++ cEdgesM 5 3) idx1.1 idx2.1 = true := by
  rcases hK with ⟨_, _, _, _, _, _, _, _, _, _, hkn0, hkn1, hkn2, hkn3, hkn4⟩
  rcases hM with ⟨_, _, _, hmn0, hmn1, hmn2⟩
  intro idx1 b hab; fin_cases idx1 <;> dsimp [fArr5_3] at hab
  · rcases (hkn0 b).1 hab with rfl | rfl
    · exact ⟨⟨4, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨1, by decide⟩, rfl, rfl⟩
  · rcases (hkn1 b).1 hab with rfl | rfl
    · exact ⟨⟨0, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨2, by decide⟩, rfl, rfl⟩
  · rcases (hkn2 b).1 hab with rfl | rfl
    · exact ⟨⟨1, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨3, by decide⟩, rfl, rfl⟩
  · rcases (hkn3 b).1 hab with rfl | rfl
    · exact ⟨⟨2, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨4, by decide⟩, rfl, rfl⟩
  · rcases (hkn4 b).1 hab with rfl | rfl
    · exact ⟨⟨3, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨0, by decide⟩, rfl, rfl⟩
  · rcases (hmn0 b).1 hab with rfl | rfl
    · exact ⟨⟨7, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨6, by decide⟩, rfl, rfl⟩
  · rcases (hmn1 b).1 hab with rfl | rfl
    · exact ⟨⟨5, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨7, by decide⟩, rfl, rfl⟩
  · rcases (hmn2 b).1 hab with rfl | rfl
    · exact ⟨⟨6, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨5, by decide⟩, rfl, rfl⟩
private lemma fArr5_3_hm {V : Type} [DecidableEq V] {C G : SimpleGraph V} {k0 k1 k2 k3 k4 u0 u1 u2 : V}
    {σ : Equiv.Perm V} (hM : IsComp3 C u0 u1 u2) (hd : Dj5 k0 k1 k2 k3 k4 {u0, u1, u2})
    (hσ : AlmOn C G k4 k0 σ) : ∀ j1 j2 (hj12 : j1 < j2) (hj2 : j2 < 3),
      (j2 = j1 + 1 ∨ (j1 = 0 ∧ j2 = 3 - 1)) →
      ¬ G.Adj (σ ((fArr5_3 k0 k1 k2 k3 k4 u0 u1 u2) ⟨5 + j1, by omega⟩)) (σ ((fArr5_3 k0 k1 k2 k3 k4 u0 u1 u2) ⟨5 + j2, by omega⟩)) := by
  obtain ⟨m0, m1, m2⟩ := comp3_m_nonadj (by simp : k4 ∈ ({k0, k1, k2, k3, k4} : Finset V)) hM hd hσ
  intro j1 j2 hj12 hj2 hcond
  interval_cases j2 <;> interval_cases j1 <;> (try dsimp [fArr5_3]) <;> first | omega | exact m0 | exact m1 | exact adj_symm_not G m2
private lemma mkCtx5_3 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 k4 w u0 u1 u2 : V)
    (hK : IsComp5 C k0 k1 k2 k3 k4) (hM : IsComp3 C u0 u1 u2)
    (hd : Dj5 k0 k1 k2 k3 k4 {u0, u1, u2}) (σ : Equiv.Perm V) (hσ : AlmOn C G k4 k0 σ)
    (hnp : ¬ Packs C G) (e0_mask sc0 : ℕ) (has_nw1 has_z : Bool) (σ1 σ2 σ3 : Equiv.Perm V)
    (hne_0_2 : e0_mask.testBit 2 = false → ¬ G.Adj (σ k0) (σ k2))
    (hne_0_3 : e0_mask.testBit 3 = false → ¬ G.Adj (σ k0) (σ k3))
    (hne_0_4 : e0_mask.testBit 4 = false → ¬ G.Adj (σ k0) (σ k4))
    (hne_1_3 : e0_mask.testBit 8 = false → ¬ G.Adj (σ k1) (σ k3))
    (hne_1_4 : e0_mask.testBit 9 = false → ¬ G.Adj (σ k1) (σ k4))
    (hne_2_4 : e0_mask.testBit 14 = false → ¬ G.Adj (σ k2) (σ k4))
    (hnw1 : has_nw1 = true → ¬ G.Adj (σ k1) (σ w))
    (hremap : has_nw1 = true →
      (AlmOn C G k4 k0 σ1 ∧ Fix5 σ1 σ w k1 k2 k3 k4 k0 k1 k2 k3 k4 ∧ EqOn σ1 σ {u0, u1, u2}) ∧
      (AlmOn C G k4 k0 σ2 ∧ Fix5 σ2 σ w k1 k0 k3 k4 k0 k1 k2 k3 k4 ∧ EqOn σ2 σ {u0, u1, u2}) ∧
      (AlmOn C G k4 k0 σ3 ∧ Fix5 σ3 σ w k1 k2 k3 k0 k0 k1 k2 k3 k4 ∧ EqOn σ3 σ {u0, u1, u2}))
    (halm : 0 < sc0 → sc0 ≤ kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4) ∧ MinSc C G k0 k1 k2 k3 k4 σ)
    (hz0 : has_z = true → ZProp C G k0 k1 k2 k3 k4 σ {u0, u1, u2})
    : ∃ ctx : ReflCtx V, ctx.L0 = 5 ∧ ctx.m = 3 ∧ ctx.e0_mask = e0_mask ∧ ctx.sc0 = sc0 ∧ ctx.has_nw1 = has_nw1 ∧ ctx.has_z = has_z ∧ ctx.ebL = (eb5_3 G σ k0 k1 k2 k3 k4 w u0 u1 u2) :=
  ⟨{
    C := C, G := G, decG := inferInstance, L0 := 5, m := 3,
    e0_mask := e0_mask, sc0 := sc0, has_nw1 := has_nw1, has_z := has_z,
    ebL := (eb5_3 G σ k0 k1 k2 k3 k4 w u0 u1 u2), hL0_pos := by decide, hm_pos := by decide,
    f := (fArr5_3 k0 k1 k2 k3 k4 u0 u1 u2), hf := fArr5_3_inj hK hM hd, kV := (kV5 k0 k1 k2 k3 k4 w),
    hkV_eq := by intro i hi; interval_cases i <;> rfl,
    σ := σ, σr := (fun r => match r with | 1 => σ1 | 2 => σ2 | 3 => σ3 | _ => σ),
    hnp := hnp,
    hrow_spec := row_spec5,
    hσr0 := fun _ => rfl,
    hσr_alm := by rintro r (rfl | ⟨hnw, rfl | rfl | rfl⟩); exact hσ; exact (hremap hnw).1.1; exact (hremap hnw).2.1.1; exact (hremap hnw).2.2.1,
    hσr_k := by
      rintro r (rfl | ⟨hnw, rfl | rfl | rfl⟩) i hi
      · interval_cases i <;> rfl
      · have hk := (hremap hnw).1.2.1; interval_cases i <;> (try dsimp [rowOf, fArr5_3]) <;> first | exact hk.1 | exact hk.2.1 | exact hk.2.2.1 | exact hk.2.2.2.1 | exact hk.2.2.2.2
      · have hk := (hremap hnw).2.1.2.1; interval_cases i <;> (try dsimp [rowOf, fArr5_3]) <;> first | exact hk.1 | exact hk.2.1 | exact hk.2.2.1 | exact hk.2.2.2.1 | exact hk.2.2.2.2
      · have hk := (hremap hnw).2.2.2.1; interval_cases i <;> (try dsimp [rowOf, fArr5_3]) <;> first | exact hk.1 | exact hk.2.1 | exact hk.2.2.1 | exact hk.2.2.2.1 | exact hk.2.2.2.2,
    hσr_m := by
      rintro r (rfl | ⟨hnw, rfl | rfl | rfl⟩) j hj
      · interval_cases j <;> rfl
      · have hu := (hremap hnw).1.2.2; interval_cases j <;> exact hu _ (by clear * -; simp [fArr5_3])
      · have hu := (hremap hnw).2.1.2.2; interval_cases j <;> exact hu _ (by clear * -; simp [fArr5_3])
      · have hu := (hremap hnw).2.2.2.2; interval_cases j <;> exact hu _ (by clear * -; simp [fArr5_3]),
    hk_path := k_path5 hK hσ,
    hk_e0 := k_e0_5 hne_0_2 hne_0_3 hne_0_4 hne_1_3 hne_1_4 hne_2_4,
    hnw1 := hnw1,
    hm_edge := fArr5_3_hm hM hd hσ,
    heb := by rintro ru j hj (hlt | ⟨_, rfl⟩); (interval_cases ru <;> interval_cases j <;> rfl); (interval_cases j <;> rfl),
    hcl_pack := fArr5_3_hcl hK hM,
    halm_min := fun _ hpos => halm hpos,
    hz_prop := by
      rcases hM with ⟨_, _, _, hmn0, hmn1, hmn2⟩
      intro hhz _ j hj; interval_cases j
      · exact ⟨fun hle => by omega, fun _ => hmn0, hz0 hhz u0 (by clear * -; simp)⟩
      · exact ⟨fun hle => by omega, fun _ => hmn1, hz0 hhz u1 (by clear * -; simp)⟩
      · exact ⟨fun hle => by omega, fun _ => hmn2, hz0 hhz u2 (by clear * -; simp)⟩ }, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
abbrev fArr5_5 {V : Type} (k0 k1 k2 k3 k4 u0 u1 u2 u3 u4 : V) (idx : Fin 10) : V := match idx.1 with | 0 => k0 | 1 => k1 | 2 => k2 | 3 => k3 | 4 => k4 | 5 => u0 | 6 => u1 | 7 => u2 | 8 => u3 | _ => u4
abbrev eb5_5 {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj] (σ : Equiv.Perm V) (k0 k1 k2 k3 k4 w u0 u1 u2 u3 u4 : V) : List Bool := [decide (G.Adj (σ k0) (σ u0)), decide (G.Adj (σ k0) (σ u1)), decide (G.Adj (σ k0) (σ u2)), decide (G.Adj (σ k0) (σ u3)), decide (G.Adj (σ k0) (σ u4)), decide (G.Adj (σ k1) (σ u0)), decide (G.Adj (σ k1) (σ u1)), decide (G.Adj (σ k1) (σ u2)), decide (G.Adj (σ k1) (σ u3)), decide (G.Adj (σ k1) (σ u4)), decide (G.Adj (σ k2) (σ u0)), decide (G.Adj (σ k2) (σ u1)), decide (G.Adj (σ k2) (σ u2)), decide (G.Adj (σ k2) (σ u3)), decide (G.Adj (σ k2) (σ u4)), decide (G.Adj (σ k3) (σ u0)), decide (G.Adj (σ k3) (σ u1)), decide (G.Adj (σ k3) (σ u2)), decide (G.Adj (σ k3) (σ u3)), decide (G.Adj (σ k3) (σ u4)), decide (G.Adj (σ k4) (σ u0)), decide (G.Adj (σ k4) (σ u1)), decide (G.Adj (σ k4) (σ u2)), decide (G.Adj (σ k4) (σ u3)), decide (G.Adj (σ k4) (σ u4)), decide (G.Adj (σ w) (σ u0)), decide (G.Adj (σ w) (σ u1)), decide (G.Adj (σ w) (σ u2)), decide (G.Adj (σ w) (σ u3)), decide (G.Adj (σ w) (σ u4))]
private lemma wSum_eb5_5 {V : Type} [Fintype V] [DecidableEq V] {C : SimpleGraph V} (G : SimpleGraph V) [DecidableRel G.Adj] (σ : Equiv.Perm V) (w0 w1 w2 w3 w4 w5 : ℕ) (k0 k1 k2 k3 k4 w u0 u1 u2 u3 u4 : V) (hM : IsComp5 C u0 u1 u2 u3 u4) :
    wSumBool [w0, w0, w0, w0, w0, w1, w1, w1, w1, w1, w2, w2, w2, w2, w2, w3, w3, w3, w3, w3, w4, w4, w4, w4, w4, w5, w5, w5, w5, w5] (eb5_5 G σ k0 k1 k2 k3 k4 w u0 u1 u2 u3 u4) = w0 * rCount G σ k0 {u0, u1, u2, u3, u4} + w1 * rCount G σ k1 {u0, u1, u2, u3, u4} + w2 * rCount G σ k2 {u0, u1, u2, u3, u4} + w3 * rCount G σ k3 {u0, u1, u2, u3, u4} + w4 * rCount G σ k4 {u0, u1, u2, u3, u4} + w5 * rCount G σ w {u0, u1, u2, u3, u4} := by
  simp only [wSumBool, if_decide_eq_mul_b01, rCount_comp5 G σ _ u0 u1 u2 u3 u4 hM]; ring
private lemma fArr5_5_inj {V : Type} [DecidableEq V] {C : SimpleGraph V}
    {k0 k1 k2 k3 k4 u0 u1 u2 u3 u4 : V} (hK : IsComp5 C k0 k1 k2 k3 k4) (hM : IsComp5 C u0 u1 u2 u3 u4)
    (hd : Dj5 k0 k1 k2 k3 k4 {u0, u1, u2, u3, u4}) : Function.Injective (fArr5_5 k0 k1 k2 k3 k4 u0 u1 u2 u3 u4) := by
  rcases hK with ⟨hk01, hk02, hk03, hk04, hk12, hk13, hk14, hk23, hk24, hk34, -⟩
  rcases hM with ⟨hm01, hm02, hm03, hm04, hm12, hm13, hm14, hm23, hm24, hm34, -⟩
  simp only [Dj5, Finset.disjoint_insert_left, Finset.disjoint_singleton_left, mem_insert, mem_singleton, not_or] at hd
  rcases hd with ⟨⟨hkm00, hkm01, hkm02, hkm03, hkm04⟩, ⟨hkm10, hkm11, hkm12, hkm13, hkm14⟩, ⟨hkm20, hkm21, hkm22, hkm23, hkm24⟩, ⟨hkm30, hkm31, hkm32, hkm33, hkm34⟩, ⟨hkm40, hkm41, hkm42, hkm43, hkm44⟩⟩
  intro i j hij; fin_cases i <;> fin_cases j <;> simp only [fArr5_5] at hij ⊢
  all_goals first | rfl | exact absurd hij (by assumption) | exact absurd hij.symm (by assumption)
private lemma fArr5_5_hcl {V : Type} {C : SimpleGraph V} {k0 k1 k2 k3 k4 u0 u1 u2 u3 u4 : V}
    (hK : IsComp5 C k0 k1 k2 k3 k4) (hM : IsComp5 C u0 u1 u2 u3 u4) :
    ∀ idx1 : Fin 10, ∀ b, C.Adj ((fArr5_5 k0 k1 k2 k3 k4 u0 u1 u2 u3 u4) idx1) b →
      ∃ idx2 : Fin 10, (fArr5_5 k0 k1 k2 k3 k4 u0 u1 u2 u3 u4) idx2 = b ∧
        hasUndirEdge (cEdgesK 5 ++ cEdgesM 5 5) idx1.1 idx2.1 = true := by
  rcases hK with ⟨_, _, _, _, _, _, _, _, _, _, hkn0, hkn1, hkn2, hkn3, hkn4⟩
  rcases hM with ⟨_, _, _, _, _, _, _, _, _, _, hmn0, hmn1, hmn2, hmn3, hmn4⟩
  intro idx1 b hab; fin_cases idx1 <;> dsimp [fArr5_5] at hab
  · rcases (hkn0 b).1 hab with rfl | rfl
    · exact ⟨⟨4, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨1, by decide⟩, rfl, rfl⟩
  · rcases (hkn1 b).1 hab with rfl | rfl
    · exact ⟨⟨0, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨2, by decide⟩, rfl, rfl⟩
  · rcases (hkn2 b).1 hab with rfl | rfl
    · exact ⟨⟨1, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨3, by decide⟩, rfl, rfl⟩
  · rcases (hkn3 b).1 hab with rfl | rfl
    · exact ⟨⟨2, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨4, by decide⟩, rfl, rfl⟩
  · rcases (hkn4 b).1 hab with rfl | rfl
    · exact ⟨⟨3, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨0, by decide⟩, rfl, rfl⟩
  · rcases (hmn0 b).1 hab with rfl | rfl
    · exact ⟨⟨9, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨6, by decide⟩, rfl, rfl⟩
  · rcases (hmn1 b).1 hab with rfl | rfl
    · exact ⟨⟨5, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨7, by decide⟩, rfl, rfl⟩
  · rcases (hmn2 b).1 hab with rfl | rfl
    · exact ⟨⟨6, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨8, by decide⟩, rfl, rfl⟩
  · rcases (hmn3 b).1 hab with rfl | rfl
    · exact ⟨⟨7, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨9, by decide⟩, rfl, rfl⟩
  · rcases (hmn4 b).1 hab with rfl | rfl
    · exact ⟨⟨8, by decide⟩, rfl, rfl⟩
    · exact ⟨⟨5, by decide⟩, rfl, rfl⟩
private lemma fArr5_5_hm {V : Type} [DecidableEq V] {C G : SimpleGraph V} {k0 k1 k2 k3 k4 u0 u1 u2 u3 u4 : V}
    {σ : Equiv.Perm V} (hM : IsComp5 C u0 u1 u2 u3 u4) (hd : Dj5 k0 k1 k2 k3 k4 {u0, u1, u2, u3, u4})
    (hσ : AlmOn C G k4 k0 σ) : ∀ j1 j2 (hj12 : j1 < j2) (hj2 : j2 < 5),
      (j2 = j1 + 1 ∨ (j1 = 0 ∧ j2 = 5 - 1)) →
      ¬ G.Adj (σ ((fArr5_5 k0 k1 k2 k3 k4 u0 u1 u2 u3 u4) ⟨5 + j1, by omega⟩)) (σ ((fArr5_5 k0 k1 k2 k3 k4 u0 u1 u2 u3 u4) ⟨5 + j2, by omega⟩)) := by
  obtain ⟨m0, m1, m2, m3, m4⟩ := comp5_m_nonadj (by simp : k4 ∈ ({k0, k1, k2, k3, k4} : Finset V)) hM hd hσ
  intro j1 j2 hj12 hj2 hcond
  interval_cases j2 <;> interval_cases j1 <;> (try dsimp [fArr5_5]) <;> first | omega | exact m0 | exact m1 | exact m2 | exact m3 | exact adj_symm_not G m4
private lemma mkCtx5_5 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 k4 w u0 u1 u2 u3 u4 : V)
    (hK : IsComp5 C k0 k1 k2 k3 k4) (hM : IsComp5 C u0 u1 u2 u3 u4)
    (hd : Dj5 k0 k1 k2 k3 k4 {u0, u1, u2, u3, u4}) (σ : Equiv.Perm V) (hσ : AlmOn C G k4 k0 σ)
    (hnp : ¬ Packs C G) (e0_mask sc0 : ℕ) (has_nw1 has_z : Bool) (σ1 σ2 σ3 : Equiv.Perm V)
    (hne_0_2 : e0_mask.testBit 2 = false → ¬ G.Adj (σ k0) (σ k2))
    (hne_0_3 : e0_mask.testBit 3 = false → ¬ G.Adj (σ k0) (σ k3))
    (hne_0_4 : e0_mask.testBit 4 = false → ¬ G.Adj (σ k0) (σ k4))
    (hne_1_3 : e0_mask.testBit 8 = false → ¬ G.Adj (σ k1) (σ k3))
    (hne_1_4 : e0_mask.testBit 9 = false → ¬ G.Adj (σ k1) (σ k4))
    (hne_2_4 : e0_mask.testBit 14 = false → ¬ G.Adj (σ k2) (σ k4))
    (hnw1 : has_nw1 = true → ¬ G.Adj (σ k1) (σ w))
    (hremap : has_nw1 = true →
      (AlmOn C G k4 k0 σ1 ∧ Fix5 σ1 σ w k1 k2 k3 k4 k0 k1 k2 k3 k4 ∧ EqOn σ1 σ {u0, u1, u2, u3, u4}) ∧
      (AlmOn C G k4 k0 σ2 ∧ Fix5 σ2 σ w k1 k0 k3 k4 k0 k1 k2 k3 k4 ∧ EqOn σ2 σ {u0, u1, u2, u3, u4}) ∧
      (AlmOn C G k4 k0 σ3 ∧ Fix5 σ3 σ w k1 k2 k3 k0 k0 k1 k2 k3 k4 ∧ EqOn σ3 σ {u0, u1, u2, u3, u4}))
    (halm : 0 < sc0 → sc0 ≤ kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4) ∧ MinSc C G k0 k1 k2 k3 k4 σ)
    (hz0 : has_z = true → ZProp C G k0 k1 k2 k3 k4 σ {u0, u1, u2, u3, u4})
    : ∃ ctx : ReflCtx V, ctx.L0 = 5 ∧ ctx.m = 5 ∧ ctx.e0_mask = e0_mask ∧ ctx.sc0 = sc0 ∧ ctx.has_nw1 = has_nw1 ∧ ctx.has_z = has_z ∧ ctx.ebL = (eb5_5 G σ k0 k1 k2 k3 k4 w u0 u1 u2 u3 u4) :=
  ⟨{
    C := C, G := G, decG := inferInstance, L0 := 5, m := 5,
    e0_mask := e0_mask, sc0 := sc0, has_nw1 := has_nw1, has_z := has_z,
    ebL := (eb5_5 G σ k0 k1 k2 k3 k4 w u0 u1 u2 u3 u4), hL0_pos := by decide, hm_pos := by decide,
    f := (fArr5_5 k0 k1 k2 k3 k4 u0 u1 u2 u3 u4), hf := fArr5_5_inj hK hM hd, kV := (kV5 k0 k1 k2 k3 k4 w),
    hkV_eq := by intro i hi; interval_cases i <;> rfl,
    σ := σ, σr := (fun r => match r with | 1 => σ1 | 2 => σ2 | 3 => σ3 | _ => σ),
    hnp := hnp,
    hrow_spec := row_spec5,
    hσr0 := fun _ => rfl,
    hσr_alm := by rintro r (rfl | ⟨hnw, rfl | rfl | rfl⟩); exact hσ; exact (hremap hnw).1.1; exact (hremap hnw).2.1.1; exact (hremap hnw).2.2.1,
    hσr_k := by
      rintro r (rfl | ⟨hnw, rfl | rfl | rfl⟩) i hi
      · interval_cases i <;> rfl
      · have hk := (hremap hnw).1.2.1; interval_cases i <;> (try dsimp [rowOf, fArr5_5]) <;> first | exact hk.1 | exact hk.2.1 | exact hk.2.2.1 | exact hk.2.2.2.1 | exact hk.2.2.2.2
      · have hk := (hremap hnw).2.1.2.1; interval_cases i <;> (try dsimp [rowOf, fArr5_5]) <;> first | exact hk.1 | exact hk.2.1 | exact hk.2.2.1 | exact hk.2.2.2.1 | exact hk.2.2.2.2
      · have hk := (hremap hnw).2.2.2.1; interval_cases i <;> (try dsimp [rowOf, fArr5_5]) <;> first | exact hk.1 | exact hk.2.1 | exact hk.2.2.1 | exact hk.2.2.2.1 | exact hk.2.2.2.2,
    hσr_m := by
      rintro r (rfl | ⟨hnw, rfl | rfl | rfl⟩) j hj
      · interval_cases j <;> rfl
      · have hu := (hremap hnw).1.2.2; interval_cases j <;> exact hu _ (by clear * -; simp [fArr5_5])
      · have hu := (hremap hnw).2.1.2.2; interval_cases j <;> exact hu _ (by clear * -; simp [fArr5_5])
      · have hu := (hremap hnw).2.2.2.2; interval_cases j <;> exact hu _ (by clear * -; simp [fArr5_5]),
    hk_path := k_path5 hK hσ,
    hk_e0 := k_e0_5 hne_0_2 hne_0_3 hne_0_4 hne_1_3 hne_1_4 hne_2_4,
    hnw1 := hnw1,
    hm_edge := fArr5_5_hm hM hd hσ,
    heb := by rintro ru j hj (hlt | ⟨_, rfl⟩); (interval_cases ru <;> interval_cases j <;> rfl); (interval_cases j <;> rfl),
    hcl_pack := fArr5_5_hcl hK hM,
    halm_min := fun _ hpos => halm hpos,
    hz_prop := by
      rcases hM with ⟨_, _, _, _, _, _, _, _, _, _, hmn0, hmn1, hmn2, hmn3, hmn4⟩
      intro hhz _ j hj; interval_cases j
      · exact ⟨fun hle => by omega, fun _ => hmn0, hz0 hhz u0 (by clear * -; simp)⟩
      · exact ⟨fun hle => by omega, fun _ => hmn1, hz0 hhz u1 (by clear * -; simp)⟩
      · exact ⟨fun hle => by omega, fun _ => hmn2, hz0 hhz u2 (by clear * -; simp)⟩
      · exact ⟨fun hle => by omega, fun _ => hmn3, hz0 hhz u3 (by clear * -; simp)⟩
      · exact ⟨fun hle => by omega, fun _ => hmn4, hz0 hhz u4 (by clear * -; simp)⟩ }, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
private abbrev pt4_1 : List ℕ := [0x34210,0x4321]
private abbrev pt4_3 : List ℕ := [0x5436210,0x5406321,0x6104532,0x6405321,0x6435210,0x6504321,0x6534210,0x4106532,0x4216350,0x4325610,0x4326510,0x5326410,0x6325410]
private abbrev pt4_4 : List ℕ := [0x62107453,0x65104732,0x74506321,0x72106543,0x74105632,0x65107432,0x65407321,0x42107653,0x52106743,0x67105432,0x67405321,0x74106532,0x76104532,0x76105432,0x76504321,0x45106732,0x45107632,0x54106732,0x54107632,0x56107432,0x67104532]
private abbrev pt4_5 : List ℕ := [0x453218760,0x543218760,0x845607321,0x483217650,0x562107843,0x672108453,0x673218450,0x762108453,0x784506321,0x876504321,0x487326510,0x542108763,0x548327610,0x765438210,0x782106543,0x784536210,0x456327810,0x563217840,0x567108432,0x567328410,0x652107843,0x654108732,0x678104532,0x678405321,0x763218450,0x765408321,0x783216540,0x784105632,0x842107653,0x845637210,0x876104532,0x876105432,0x876325410,0x452108763,0x456328710,0x482107653,0x548106732,0x548107632,0x653217840,0x654327810,0x654328710,0x678105432,0x678435210,0x765104832,0x765328410,0x784325610,0x843217650,0x845106732,0x845107632,0x845326710,0x872106543,0x873216540,0x876534210]
private abbrev pt5_1 : List ℕ := [0x452310,0x154320,0x251430,0x253410,0x254310,0x432150,0x43521,0x450132,0x453210,0x52341,0x54321]
private abbrev pt5_3 : List ℕ := [0x65074321,0x76054321,0x75064321,0x76043521,0x71065432,0x75043621,0x21057643,0x65043721,0x76052341,0x21067543,0x21076543,0x51076432,0x64357210,0x64375210,0x65273410,0x71056432,0x71065234,0x73046521,0x76034521,0x21065743,0x21075643,0x32146750,0x32174560,0x32174650,0x32175460,0x32176450,0x43172560,0x43172650,0x52176430,0x53276410,0x64157230,0x73045621,0x73256410,0x76453210,0x21056743,0x31046752,0x31067452,0x31074562,0x31076452,0x32145760,0x32167450,0x43126750,0x43167250,0x43175260,0x43176250,0x51067432,0x51076234,0x53046721,0x53047621,0x54321670,0x61043572,0x61057432,0x61075234,0x61075432,0x62157430,0x63045721,0x63241570,0x63257410,0x63275410,0x64175230,0x64321570,0x65034721,0x65072341,0x65147230,0x65341270,0x65347210,0x65473210,0x72156430,0x73056412,0x74156230,0x74356210,0x75062341,0x76043251,0x76043512,0x76053412,0x76253410,0x76451230]
private abbrev pt5_5 : List ℕ := [0x9567084321,0x8956074321,0x8231095674,0x8765094321,0x9431087652,0x9561087432,0x9876054321,0x7231089564,0x9567034821,0x6591087432,0x7431089562,0x8956034721,0x7321089564,0x7651098432,0x9561078432,0x8951067432,0x9321087654,0x9567082341,0x9821056743,0x8951076432,0x9821076543,0x7621059843,0x7891065432,0x6591078432,0x7651089432,0x9567043821,0x6721059843,0x6781059432,0x6781095432,0x7895064321,0x8956043721,0x9231087654,0x9521067843,0x9541087632,0x6431078952,0x6521078943,0x8321095674,0x8431095672,0x8765034921,0x8956072341,0x6521098743,0x6721089543,0x6741059832,0x7891056432,0x9841056732,0x9871065432,0x6321078954,0x7621089543,0x8721095643,0x8921056743,0x9341087652,0x9876043521,0x9876052341,0x5231098764,0x5321098764,0x5431098762,0x6231078954,0x7612059843,0x7841095632,0x8721065943,0x8761095432,0x9812056743,0x9823056741,0x7341089562,0x8765092341,0x8912056743,0x8921076543,0x8941076532,0x9512067843,0x9563047821,0x5674398012,0x6743089521,0x7612089543,0x7623059841,0x7623089541,0x7641059832,0x7812065943,0x7821065943,0x7895043621,0x8743065921,0x8761059432,0x8765043921,0x8923056741,0x8943056721,0x9512087643,0x9521087643,0x9523087641,0x9561087234,0x9563048721,0x9812076543,0x5673298014,0x6341078952,0x6512078943,0x6512098743,0x6541078932,0x6712059843,0x6712089543,0x7653298014,0x7821095643,0x7823065941,0x7895062341,0x8143095672,0x8341095672,0x8723095641,0x8741095632,0x9843076521,0x9871056432,0x5672143890,0x6593048721,0x6594387012,0x6723059841,0x7123089564,0x7143089562,0x7641089532,0x7643059821,0x7643089521,0x7653049821,0x7654398012,0x7812095643,0x7841065932,0x7843065921,0x7843095621,0x7895034621,0x8741065932,0x8763045921,0x8763049521,0x8912076543,0x8953046721,0x9541067832,0x9543087621,0x9548067321,0x9563287014,0x9567083412,0x9873046521,0x9876034521,0x2351098764,0x3461078952,0x3641078952,0x5341098762,0x5621098743,0x5981067432,0x5982143670,0x5984376012,0x6523078941,0x6523098741,0x6541098732,0x6543078921,0x6593047821,0x6593287014,0x6723089541,0x6783049521,0x6784321590,0x7651098234,0x7652143890,0x7653048921,0x7823095641,0x8712065943,0x8712095643,0x8723065941,0x8743095621,0x8765234190,0x8941056732,0x8943076521,0x8947056321,0x9478065321,0x9548076321,0x9562143780,0x9823076541,0x3251098764,0x3271089564,0x3491087652,0x3521098764,0x3541098762,0x3941087652,0x5123098764,0x5143098762,0x5621078943,0x5623078941,0x5672143980,0x5674321890,0x5943087621,0x5982134760,0x5983047621,0x5983276014,0x6123078954,0x6143078952,0x6432078951,0x6543098721,0x6591087234,0x6592143870,0x6784359012,0x7456089321,0x7654321890,0x7891065234,0x7893046521,0x7894365012,0x7895046321,0x8123095674,0x8467059321,0x8952143760,0x8953047621,0x8953276014,0x8954376012,0x8956047321,0x8956073412,0x9123087654,0x9143087652,0x9287065341,0x9432087651,0x9465078321,0x9465087321,0x9543067821,0x9567048321,0x9567234180,0x9841076532,0x9843056721,0x9873045621,0x9874365012,0x9876045321,0x2361078954,0x2371089564,0x2381095674,0x2391087654,0x3261078954,0x3451098762,0x3471089562,0x3621078954,0x3721089564,0x3741089562,0x3821095674,0x3841095672,0x5612078943,0x5612098743,0x5623098741,0x5671089432,0x5671098234,0x5671098432,0x5673048921,0x5673049821,0x5673248901,0x5674132890,0x5674389012,0x5674389210,0x5921067843,0x5923067841,0x5941067832,0x5981076432,0x5982134670,0x5982143760,0x5983241760,0x5983247601,0x5984123670,0x5984123760,0x5984132670,0x5984132760,0x5984321670,0x5984321760,0x5984367012,0x5984367210,0x6592143780,0x6593087412,0x6593241780,0x6741089532,0x6743059821,0x6781095234,0x6782143590,0x6783045921,0x6783059412,0x6783295014,0x6784123590,0x6784359210,0x6784395012,0x7432089561,0x7456098321,0x7652143980,0x7653241980,0x7653289410,0x7654389012,0x7832094651,0x7846095321,0x7891043562,0x7891043652,0x7893041652,0x7893045621,0x7893256410,0x7893265014,0x7894156230,0x7894321560,0x7895234160,0x7895341260,0x7895432160,0x7895432601,0x8432095671,0x8467095321,0x8732064951,0x8763295014,0x8764359210,0x8764395012,0x8765049321,0x8765341290,0x8765432190,0x8923076541,0x8947065321,0x8952143670,0x8952174360,0x8953241670,0x8954321670,0x8954321760,0x8956234170,0x8956432170,0x8956432701,0x9256078341,0x9256087341,0x9387065214,0x9465037821,0x9465038721,0x9478056321,0x9523067841,0x9526087341,0x9536087214,0x9562143870,0x9563087412,0x9564387012,0x9567432180,0x9567480132,0x9827056341,0x9827065341,0x9832074561,0x9837065214,0x9871065234,0x9873056412,0x9873256410,0x9873265014,0x9874321560,0x9874356012,0x9874356210,0x9876043251,0x9876043512,0x9876053412,0x9876234150,0x9876432150,0x9876432501]
private abbrev wl0 : List ℕ := [2,1,1,2]
private abbrev wl1 : List ℕ := [2,2,2,1,1,1,1,1,1,2,2,2]
private abbrev wl2 : List ℕ := [2,2,2,2,1,1,1,1,1,1,1,1,2,2,2,2]
private abbrev wl3 : List ℕ := [2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2]
private abbrev wl4 : List ℕ := [2,1,0,1,2,0]
private abbrev wl5 : List ℕ := [2,2,2,1,1,1,0,0,0,1,1,1,2,2,2,0,0,0]
private abbrev wl6 : List ℕ := [2,2,2,2,2,1,1,1,1,1,0,0,0,0,0,1,1,1,1,1,2,2,2,2,2,0,0,0,0,0]
private abbrev wl7 : List ℕ := [2,0,0,0,1,0]
private abbrev wl8 : List ℕ := [2,2,2,0,0,0,0,0,0,0,0,0,1,1,1,0,0,0]
private abbrev wl9 : List ℕ := [2,2,2,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,0,0,0,0,0]
private abbrev wl10 : List ℕ := [2,1,1,1,1,0]
private abbrev wl11 : List ℕ := [2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,0,0,0]
private abbrev wl12 : List ℕ := [2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,0,0,0,0]
private abbrev wl13 : List ℕ := [3,1,3,2,0,0]
private abbrev wl14 : List ℕ := [3,3,3,1,1,1,3,3,3,2,2,2,0,0,0,0,0,0]
private abbrev wl15 : List ℕ := [3,3,3,3,3,1,1,1,1,1,3,3,3,3,3,2,2,2,2,2,0,0,0,0,0,0,0,0,0,0]
private abbrev wl16 : List ℕ := [1,1,1,1,1,0,0,0,0,0,1,1,1,1,1,0,0,0,0,0,1,1,1,1,1,0,0,0,0,0]
private abbrev wl17 : List ℕ := [9,3,9,3,9,0]
private abbrev wl18 : List ℕ := [9,9,9,3,3,3,9,9,9,3,3,3,9,9,9,0,0,0]
private abbrev wl19 : List ℕ := [9,9,9,9,9,3,3,3,3,3,9,9,9,9,9,3,3,3,3,3,9,9,9,9,9,0,0,0,0,0]
private abbrev wl20 : List ℕ := [2,0,2,0,2,3]
private abbrev wl21 : List ℕ := [2,2,2,0,0,0,2,2,2,0,0,0,2,2,2,3,3,3]
private abbrev wl22 : List ℕ := [2,2,2,2,2,0,0,0,0,0,2,2,2,2,2,0,0,0,0,0,2,2,2,2,2,3,3,3,3,3]
private lemma f4_1_all {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 u0 : V)
    (hK : IsComp4 C k0 k1 k2 k3) (hM : IsComp1 C u0)
    (hd : Dj4 k0 k1 k2 k3 {u0}) (σ : Equiv.Perm V) (hσ : AlmOn C G k3 k0 σ) (hnp : ¬ Packs C G)
    : 2 ≤ 2 * rCount G σ k0 {u0} + rCount G σ k1 {u0} + rCount G σ k2 {u0} + 2 * rCount G σ k3 {u0} := by
  have hev : evalDT 4 1 268 0 false false pt4_1 wl0 2 (n 0 b (n 2 (n 3 b (n 1 b (p 4))) (p 0))) 0 0 = true := rfl
  have hsum : 2 ≤ wSumBool wl0 (eb4_1 G σ k0 k1 k2 k3 u0) := evalDT_sound (mkCtx4_1 C G k0 k1 k2 k3 k0 u0 hK hM hd σ hσ hnp 268 0 false false σ σ σ fd fd fd rfl) pt4_1 wl0 2 rfl (n 0 b (n 2 (n 3 b (n 1 b (p 4))) (p 0))) 0 0 mz mz hev
  dsimp only [wl0] at hsum; rw [wSum_eb4_1 G σ 2 1 1 2 k0 k1 k2 k3 u0] at hsum; clear hev; omega
set_option maxHeartbeats 800000 in
private lemma f4_3 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 u0 u1 u2 : V)
    (hK : IsComp4 C k0 k1 k2 k3) (hM : IsComp3 C u0 u1 u2)
    (hd : Dj4 k0 k1 k2 k3 {u0, u1, u2}) (σ : Equiv.Perm V) (hσ : AlmOn C G k3 k0 σ) (hnp : ¬ Packs C G)
    : 6 ≤ 2 * rCount G σ k0 {u0, u1, u2} + rCount G σ k1 {u0, u1, u2} + rCount G σ k2 {u0, u1, u2} + 2 * rCount G σ k3 {u0, u1, u2} := by
  have run (a0 a1 a2 : V) (hMa : IsComp3 C a0 a1 a2) (hdM : Dj4 k0 k1 k2 k3 {a0, a1, a2})
      (tr : DT) (tm fm : ℕ) (ht : ∀ i, tm.testBit i = true → (eb4_3 G σ k0 k1 k2 k3 a0 a1 a2).getD i false = true)
      (hf : ∀ i, fm.testBit i = true → (eb4_3 G σ k0 k1 k2 k3 a0 a1 a2).getD i false = false)
      (hev : evalDT 4 3 268 0 false false pt4_3 wl1 6 tr tm fm = true) : 6 ≤ 2 * rCount G σ k0 {a0, a1, a2} + rCount G σ k1 {a0, a1, a2} + rCount G σ k2 {a0, a1, a2} + 2 * rCount G σ k3 {a0, a1, a2} := by
    have hsum : 6 ≤ wSumBool wl1 (eb4_3 G σ k0 k1 k2 k3 a0 a1 a2) := evalDT_sound (mkCtx4_3 C G k0 k1 k2 k3 k0 a0 a1 a2 hK hMa hdM σ hσ hnp 268 0 false false σ σ σ fd fd fd rfl) pt4_3 wl1 6 rfl tr tm fm ht hf hev
    dsimp only [wl1] at hsum; rw [wSum_eb4_3 G σ 2 1 1 2 k0 k1 k2 k3 a0 a1 a2 hMa] at hsum; clear tr tm fm ht hf hev; omega
  refine sym2_m3 C G σ k0 k3 (fun M => Dj4 k0 k1 k2 k3 M → 6 ≤ 2 * rCount G σ k0 M + rCount G σ k1 M + rCount G σ k2 M + 2 * rCount G σ k3 M) ?_ ?_ ?_ ?_ ?_ u0 u1 u2 hM hd
  · intro a0 a1 a2 hMa t0 t1 hdM; exact run a0 a1 a2 hMa hdM (n 2 b (n 9 b (n 10 b (n 8 (n 5 b (n 6 b (p 8))) (p 0))))) (1<<<0|||1<<<1) (0) (mo (mt 0 t0) (mt 1 t1)) mz rfl
  · intro a0 a1 a2 hMa t0 n1 n2 hdM; exact run a0 a1 a2 hMa hdM (n 9 (n 10 b (n 3 (n 6 b (n 5 b (p 8))) (n 7 (n 11 b (n 6 b (p 32))) (p 44)))) (n 3 (n 6 (n 7 (n 8 b (n 10 b (p 0))) (n 11 b (p 16))) (n 4 (n 5 (n 10 b (n 8 b (p 0))) (p 36)) (p 40))) (p 20))) (1<<<0) (1<<<1|||1<<<2) (mt 0 t0) (mo (mf 1 n1) (mf 2 n2)) rfl
  · intro a0 a1 a2 hMa n0 n1 n2 t9 t10 hdM; exact run a0 a1 a2 hMa hdM (n 11 b (n 5 (n 3 b (n 8 b (p 48))) (p 4))) (1<<<9|||1<<<10) (1<<<0|||1<<<1|||1<<<2) (mo (mt 9 t9) (mt 10 t10)) (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) rfl
  · intro a0 a1 a2 hMa n0 n1 n2 t9 n10 n11 hdM; exact run a0 a1 a2 hMa hdM (n 6 (n 4 (n 5 (n 3 b (n 8 b (p 28))) (p 4)) (p 12)) (p 24)) (1<<<9) (1<<<0|||1<<<1|||1<<<2|||1<<<10|||1<<<11) (mt 9 t9) (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 10 n10)) (mf 11 n11)) rfl
  · intro a0 a1 a2 hMa n0 n1 n2 n9 n10 n11 hdM; exact run a0 a1 a2 hMa hdM (n 3 (n 4 (n 5 (n 8 (n 6 (n 7 b (p 16)) (p 24)) (p 0)) (p 4)) (p 12)) (p 20)) (0) (1<<<0|||1<<<1|||1<<<2|||1<<<9|||1<<<10|||1<<<11) mz (mo (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 9 n9)) (mf 10 n10)) (mf 11 n11)) rfl
set_option maxHeartbeats 800000 in
private lemma f4_4 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 u0 u1 u2 u3 : V)
    (hK : IsComp4 C k0 k1 k2 k3) (hM : IsComp4 C u0 u1 u2 u3)
    (hd : Dj4 k0 k1 k2 k3 {u0, u1, u2, u3}) (σ : Equiv.Perm V) (hσ : AlmOn C G k3 k0 σ) (hnp : ¬ Packs C G)
    : 8 ≤ 2 * rCount G σ k0 {u0, u1, u2, u3} + rCount G σ k1 {u0, u1, u2, u3} + rCount G σ k2 {u0, u1, u2, u3} + 2 * rCount G σ k3 {u0, u1, u2, u3} := by
  have run (a0 a1 a2 a3 : V) (hMa : IsComp4 C a0 a1 a2 a3) (hdM : Dj4 k0 k1 k2 k3 {a0, a1, a2, a3})
      (tr : DT) (tm fm : ℕ) (ht : ∀ i, tm.testBit i = true → (eb4_4 G σ k0 k1 k2 k3 a0 a1 a2 a3).getD i false = true)
      (hf : ∀ i, fm.testBit i = true → (eb4_4 G σ k0 k1 k2 k3 a0 a1 a2 a3).getD i false = false)
      (hev : evalDT 4 4 268 0 false false pt4_4 wl2 8 tr tm fm = true) : 8 ≤ 2 * rCount G σ k0 {a0, a1, a2, a3} + rCount G σ k1 {a0, a1, a2, a3} + rCount G σ k2 {a0, a1, a2, a3} + 2 * rCount G σ k3 {a0, a1, a2, a3} := by
    have hsum : 8 ≤ wSumBool wl2 (eb4_4 G σ k0 k1 k2 k3 a0 a1 a2 a3) := evalDT_sound (mkCtx4_4 C G k0 k1 k2 k3 k0 a0 a1 a2 a3 hK hMa hdM σ hσ hnp 268 0 false false σ σ σ fd fd fd rfl) pt4_4 wl2 8 rfl tr tm fm ht hf hev
    dsimp only [wl2] at hsum; rw [wSum_eb4_4 G σ 2 1 1 2 k0 k1 k2 k3 a0 a1 a2 a3 hMa] at hsum; clear tr tm fm ht hf hev; omega
  refine sym2_m4 C G σ k0 k3 (fun M => Dj4 k0 k1 k2 k3 M → 8 ≤ 2 * rCount G σ k0 M + rCount G σ k1 M + rCount G σ k2 M + 2 * rCount G σ k3 M) ?_ ?_ ?_ ?_ ?_ u0 u1 u2 u3 hM hd
  · intro a0 a1 a2 a3 hMa t0 t1 hdM; exact run a0 a1 a2 a3 hMa hdM (n 2 (n 3 b (n 12 b (n 14 b (n 11 (n 9 b (n 4 b (p 16))) (p 12))))) (n 12 (n 13 b (n 15 b (n 10 (n 8 b (n 5 b (p 4))) (p 0)))) (n 9 (n 11 (n 13 b (n 15 b (n 10 (n 8 b (n 5 b (p 4))) (p 0)))) (n 5 (n 3 b (n 14 b (p 12))) (p 20))) (n 7 (n 3 (n 5 b (n 11 b (p 20))) (n 6 (n 14 b (n 11 (n 4 b (p 16)) (p 12))) (p 52))) (p 36))))) (1<<<0|||1<<<1) (0) (mo (mt 0 t0) (mt 1 t1)) mz rfl
  · intro a0 a1 a2 a3 hMa t0 n1 n3 hdM; exact run a0 a1 a2 a3 hMa hdM (n 12 (n 14 (n 13 b (n 8 (n 10 b (n 4 b (p 44))) (n 6 (n 2 b (n 7 b (p 80))) (p 48)))) (n 6 (n 4 (n 2 b (n 13 b (n 15 b (n 10 (n 8 b (n 5 b (p 4))) (p 0))))) (n 9 (n 11 (n 10 b (n 13 b (p 44))) (p 72)) (p 16))) (p 8))) (n 4 (n 14 (n 6 (n 2 b (n 5 (n 7 b (n 9 b (p 36))) (n 11 (n 15 b (n 8 b (p 4))) (p 20)))) (n 9 (n 11 (n 8 b (n 13 b (p 48))) (p 76)) (p 52))) (n 6 (n 9 (n 11 (n 2 b (n 13 b (n 15 b (n 10 (n 8 b (n 5 b (p 4))) (p 0))))) (p 12)) (p 32)) (p 8))) (p 56))) (1<<<0) (1<<<1|||1<<<3) (mt 0 t0) (mo (mf 1 n1) (mf 3 n3)) rfl
  · intro a0 a1 a2 a3 hMa n0 n1 n2 n3 t12 t13 hdM; exact run a0 a1 a2 a3 hMa hdM (n 15 (n 14 b (n 6 (n 4 b (n 9 b (p 16))) (p 8))) (n 7 (n 5 (n 6 (n 4 b (n 10 b (p 68))) (n 14 b (p 8))) (n 8 (n 10 (n 14 b (n 11 b (p 64))) (p 60)) (p 4))) (p 24))) (1<<<12|||1<<<13) (1<<<0|||1<<<1|||1<<<2|||1<<<3) (mo (mt 12 t12) (mt 13 t13)) (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 3 n3)) rfl
  · intro a0 a1 a2 a3 hMa n0 n1 n2 n3 t12 n13 n15 hdM; exact run a0 a1 a2 a3 hMa hdM (n 8 (n 10 (n 5 (n 7 (n 14 b (n 6 (n 4 b (n 9 b (p 16))) (p 8))) (p 24)) (p 40)) (p 0)) (p 28)) (1<<<12) (1<<<0|||1<<<1|||1<<<2|||1<<<3|||1<<<13|||1<<<15) (mt 12 t12) (mo (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 3 n3)) (mf 13 n13)) (mf 15 n15)) rfl
  · intro a0 a1 a2 a3 hMa n0 n1 n2 n3 n12 n13 n14 n15 hdM; exact run a0 a1 a2 a3 hMa hdM (n 4 (n 5 (n 6 (n 7 (n 8 (n 9 (n 10 (n 11 b (p 12)) (p 0)) (p 32)) (p 28)) (p 24)) (p 8)) (p 40)) (p 56)) (0) (1<<<0|||1<<<1|||1<<<2|||1<<<3|||1<<<12|||1<<<13|||1<<<14|||1<<<15) mz (mo (mo (mo (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 3 n3)) (mf 12 n12)) (mf 13 n13)) (mf 14 n14)) (mf 15 n15)) rfl
set_option maxHeartbeats 800000 in
private lemma f4_5 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 u0 u1 u2 u3 u4 : V)
    (hK : IsComp4 C k0 k1 k2 k3) (hM : IsComp5 C u0 u1 u2 u3 u4)
    (hd : Dj4 k0 k1 k2 k3 {u0, u1, u2, u3, u4}) (σ : Equiv.Perm V) (hσ : AlmOn C G k3 k0 σ) (hnp : ¬ Packs C G)
    : 10 ≤ 2 * rCount G σ k0 {u0, u1, u2, u3, u4} + rCount G σ k1 {u0, u1, u2, u3, u4} + rCount G σ k2 {u0, u1, u2, u3, u4} + 2 * rCount G σ k3 {u0, u1, u2, u3, u4} := by
  have run (a0 a1 a2 a3 a4 : V) (hMa : IsComp5 C a0 a1 a2 a3 a4) (hdM : Dj4 k0 k1 k2 k3 {a0, a1, a2, a3, a4})
      (tr : DT) (tm fm : ℕ) (ht : ∀ i, tm.testBit i = true → (eb4_5 G σ k0 k1 k2 k3 a0 a1 a2 a3 a4).getD i false = true)
      (hf : ∀ i, fm.testBit i = true → (eb4_5 G σ k0 k1 k2 k3 a0 a1 a2 a3 a4).getD i false = false)
      (hev : evalDT 4 5 268 0 false false pt4_5 wl3 10 tr tm fm = true) : 10 ≤ 2 * rCount G σ k0 {a0, a1, a2, a3, a4} + rCount G σ k1 {a0, a1, a2, a3, a4} + rCount G σ k2 {a0, a1, a2, a3, a4} + 2 * rCount G σ k3 {a0, a1, a2, a3, a4} := by
    have hsum : 10 ≤ wSumBool wl3 (eb4_5 G σ k0 k1 k2 k3 a0 a1 a2 a3 a4) := evalDT_sound (mkCtx4_5 C G k0 k1 k2 k3 k0 a0 a1 a2 a3 a4 hK hMa hdM σ hσ hnp 268 0 false false σ σ σ fd fd fd rfl) pt4_5 wl3 10 rfl tr tm fm ht hf hev
    dsimp only [wl3] at hsum; rw [wSum_eb4_5 G σ 2 1 1 2 k0 k1 k2 k3 a0 a1 a2 a3 a4 hMa] at hsum; clear tr tm fm ht hf hev; omega
  refine sym2_m5 C G σ k0 k3 (fun M => Dj4 k0 k1 k2 k3 M → 10 ≤ 2 * rCount G σ k0 M + rCount G σ k1 M + rCount G σ k2 M + 2 * rCount G σ k3 M) ?_ ?_ ?_ ?_ ?_ u0 u1 u2 u3 u4 hM hd
  · intro a0 a1 a2 a3 a4 hMa t0 t1 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 2 (n 3 (n 4 b (n 15 b (n 18 b (n 14 (n 11 b (n 5 b (p 76))) (p 52))))) (n 19 (n 15 b (n 14 (n 12 b (n 9 b (p 156))) (n 17 b (p 56)))) (n 17 (n 16 b (n 12 (n 7 b (n 11 b (p 48))) (p 28))) (n 13 (n 10 (n 11 (n 15 b (n 14 b (p 56))) (n 5 (n 7 b (p 48)) (p 108))) (n 9 (n 6 (n 11 b (n 7 b (p 48))) (p 172)) (p 64))) (p 116))))) (n 18 (n 16 (n 15 b (n 6 (n 11 b (n 9 b (p 164))) (n 4 b (p 4)))) (n 4 (n 19 b (n 13 (n 3 b (n 12 b (p 28))) (p 20))) (n 5 (n 10 (n 15 b (n 6 (n 11 b (n 7 b (p 124))) (p 4))) (n 9 (n 7 (n 8 b (n 17 b (p 136))) (p 120)) (p 88))) (p 0)))) (n 4 (n 16 (n 15 b (n 11 (n 6 b (n 10 b (p 40))) (p 80))) (n 12 (n 14 (n 10 (n 19 b (n 13 b (p 20))) (n 9 (n 6 b (p 40)) (p 88))) (n 8 (n 5 (n 10 b (n 6 b (p 40))) (p 84)) (p 196))) (p 60))) (n 8 (n 15 (n 16 (n 5 b (n 11 b (p 76))) (n 5 (n 10 (n 12 b (p 60)) (p 112)) (p 0))) (n 6 (n 11 (n 14 (n 16 b (n 10 (n 5 b (p 0)) (p 112))) (p 52)) (p 80)) (p 4))) (p 8))))) (1<<<0|||1<<<1) (0) (mo (mt 0 t0) (mt 1 t1)) mz rfl
  · intro a0 a1 a2 a3 a4 hMa t0 n1 n4 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 17 (n 18 (n 15 (n 5 (n 10 b (n 16 b (n 7 b (p 120)))) (n 16 b (n 2 b (p 0)))) (n 5 (n 7 (n 8 (n 2 b (n 6 b (p 4))) (n 12 (n 14 b (p 72)) (p 160))) (n 11 (n 13 (n 8 b (n 14 b (p 72))) (p 180)) (p 124))) (p 36))) (n 7 (n 15 (n 12 (n 2 b (n 8 (n 5 b (n 16 b (p 0))) (p 8))) (n 9 (n 6 (n 2 b (n 16 b (p 60))) (p 188)) (p 144))) (n 12 (n 5 (n 14 (n 2 b (n 6 (n 8 b (p 8)) (p 4))) (p 52)) (p 36)) (p 16))) (p 24))) (n 8 (n 15 (n 3 (n 13 (n 18 b (n 7 (n 5 b (n 14 b (p 128))) (p 24))) (n 6 (n 9 (n 5 b (n 16 b (p 176))) (p 148)) (p 192))) (n 7 (n 19 (n 5 (n 9 b (n 10 b (p 64))) (n 11 (n 14 b (p 128)) (p 108))) (n 5 (n 10 (n 13 (n 16 b (n 12 b (p 28))) (p 116)) (p 44)) (p 12))) (p 32))) (n 5 (n 13 (n 11 (n 3 (n 18 b (n 12 (n 7 b (p 24)) (p 16))) (n 9 (n 7 (n 14 (n 18 b (n 12 b (p 16))) (p 56)) (p 32)) (p 184))) (p 168)) (p 200)) (p 36))) (p 96))) (1<<<0) (1<<<1|||1<<<4) (mt 0 t0) (mo (mf 1 n1) (mf 4 n4)) rfl
  · intro a0 a1 a2 a3 a4 hMa n0 n1 n2 n3 n4 t15 t16 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 18 (n 17 (n 19 b (n 8 (n 5 b (p 12)) (p 104))) (n 8 (n 6 (n 7 (n 19 b (n 5 b (p 12))) (p 32)) (p 68)) (p 96))) (n 8 (n 9 (n 7 (n 5 (n 6 (n 17 b (n 19 b (n 10 b (p 44)))) (n 17 b (p 68))) (n 19 (n 14 b (p 84)) (p 12))) (p 24)) (p 204)) (p 8))) (1<<<15|||1<<<16) (1<<<0|||1<<<1|||1<<<2|||1<<<3|||1<<<4) (mo (mt 15 t15) (mt 16 t16)) (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 3 n3)) (mf 4 n4)) rfl
  · intro a0 a1 a2 a3 a4 hMa n0 n1 n2 n3 n4 t15 n16 n19 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 5 (n 10 (n 6 (n 7 (n 8 (n 9 (n 12 (n 13 b (p 20)) (p 28)) (p 100)) (p 104)) (p 152)) (p 92)) (p 208)) (p 0)) (1<<<15) (1<<<0|||1<<<1|||1<<<2|||1<<<3|||1<<<4|||1<<<16|||1<<<19) (mt 15 t15) (mo (mo (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 3 n3)) (mf 4 n4)) (mf 16 n16)) (mf 19 n19)) rfl
  · intro a0 a1 a2 a3 a4 hMa n0 n1 n2 n3 n4 n15 n16 n17 n18 n19 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 5 (n 6 (n 7 (n 8 (n 9 (n 10 (n 11 (n 12 (n 13 (n 14 b (p 140)) (p 20)) (p 16)) (p 132)) (p 44)) (p 100)) (p 8)) (p 32)) (p 92)) (p 36)) (0) (1<<<0|||1<<<1|||1<<<2|||1<<<3|||1<<<4|||1<<<15|||1<<<16|||1<<<17|||1<<<18|||1<<<19) mz (mo (mo (mo (mo (mo (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 3 n3)) (mf 4 n4)) (mf 15 n15)) (mf 16 n16)) (mf 17 n17)) (mf 18 n18)) (mf 19 n19)) rfl
private lemma fno02_1_all {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 k4 u0 : V)
    (hK : IsComp5 C k0 k1 k2 k3 k4) (hM : IsComp1 C u0)
    (hd : Dj5 k0 k1 k2 k3 k4 {u0}) (σ : Equiv.Perm V) (hσ : AlmOn C G k4 k0 σ) (hnp : ¬ Packs C G)
    (ne02 : ¬ G.Adj (σ k0) (σ k2))
    : 2 ≤ 2 * rCount G σ k0 {u0} + 1 * rCount G σ k1 {u0} + 0 * rCount G σ k2 {u0} + 1 * rCount G σ k3 {u0} + 2 * rCount G σ k4 {u0} := by
  have hev : evalDT 5 1 17176 0 false false pt5_1 wl4 2 (n 0 b (n 4 b (p 4))) 0 0 = true := rfl
  have hsum : 2 ≤ wSumBool wl4 (eb5_1 G σ k0 k1 k2 k3 k4 k0 u0) := evalDT_sound (mkCtx5_1 C G k0 k1 k2 k3 k4 k0 u0 hK hM hd σ hσ hnp 17176 0 false false σ σ σ (fun _ => ne02) fd fd fd fd fd ff ff fz ff) pt5_1 wl4 2 rfl (n 0 b (n 4 b (p 4))) 0 0 mz mz hev
  dsimp only [wl4] at hsum; rw [wSum_eb5_1 G σ 2 1 0 1 2 0 k0 k1 k2 k3 k4 k0 u0] at hsum; clear hev; omega
set_option maxHeartbeats 800000 in
private lemma fno02_3 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 k4 u0 u1 u2 : V)
    (hK : IsComp5 C k0 k1 k2 k3 k4) (hM : IsComp3 C u0 u1 u2)
    (hd : Dj5 k0 k1 k2 k3 k4 {u0, u1, u2}) (σ : Equiv.Perm V) (hσ : AlmOn C G k4 k0 σ) (hnp : ¬ Packs C G)
    (ne02 : ¬ G.Adj (σ k0) (σ k2))
    : 6 ≤ 2 * rCount G σ k0 {u0, u1, u2} + 1 * rCount G σ k1 {u0, u1, u2} + 0 * rCount G σ k2 {u0, u1, u2} + 1 * rCount G σ k3 {u0, u1, u2} + 2 * rCount G σ k4 {u0, u1, u2} := by
  have run (a0 a1 a2 : V) (hMa : IsComp3 C a0 a1 a2) (hdM : Dj5 k0 k1 k2 k3 k4 {a0, a1, a2})
      (tr : DT) (tm fm : ℕ) (ht : ∀ i, tm.testBit i = true → (eb5_3 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2).getD i false = true)
      (hf : ∀ i, fm.testBit i = true → (eb5_3 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2).getD i false = false)
      (hev : evalDT 5 3 17176 0 false false pt5_3 wl5 6 tr tm fm = true) : 6 ≤ 2 * rCount G σ k0 {a0, a1, a2} + 1 * rCount G σ k1 {a0, a1, a2} + 0 * rCount G σ k2 {a0, a1, a2} + 1 * rCount G σ k3 {a0, a1, a2} + 2 * rCount G σ k4 {a0, a1, a2} := by
    have hsum : 6 ≤ wSumBool wl5 (eb5_3 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2) := evalDT_sound (mkCtx5_3 C G k0 k1 k2 k3 k4 k0 a0 a1 a2 hK hMa hdM σ hσ hnp 17176 0 false false σ σ σ (fun _ => ne02) fd fd fd fd fd ff ff fz ff) pt5_3 wl5 6 rfl tr tm fm ht hf hev
    dsimp only [wl5] at hsum; rw [wSum_eb5_3 G σ 2 1 0 1 2 0 k0 k1 k2 k3 k4 k0 a0 a1 a2 hMa] at hsum; clear tr tm fm ht hf hev; omega
  refine sym2_m3 C G σ k0 k4 (fun M => Dj5 k0 k1 k2 k3 k4 M → 6 ≤ 2 * rCount G σ k0 M + 1 * rCount G σ k1 M + 0 * rCount G σ k2 M + 1 * rCount G σ k3 M + 2 * rCount G σ k4 M) ?_ ?_ ?_ ?_ ?_ u0 u1 u2 hM hd
  · intro a0 a1 a2 hMa t0 t1 hdM; exact run a0 a1 a2 hMa hdM (n 12 b (n 10 (n 11 b (p 40)) (p 36))) (1<<<0|||1<<<1) (0) (mo (mt 0 t0) (mt 1 t1)) mz rfl
  · intro a0 a1 a2 hMa t0 n1 n2 hdM; exact run a0 a1 a2 hMa hdM (n 12 (n 13 b (n 11 (n 9 b (p 24)) (p 80))) (n 3 (n 10 (n 11 (n 9 b (n 13 b (p 24))) (p 40)) (p 36)) (p 4))) (1<<<0) (1<<<1|||1<<<2) (mt 0 t0) (mo (mf 1 n1) (mf 2 n2)) rfl
  · intro a0 a1 a2 hMa n0 n1 n2 t12 t13 hdM; exact run a0 a1 a2 hMa hdM (n 14 b (n 9 (n 10 b (p 76)) (p 136))) (1<<<12|||1<<<13) (1<<<0|||1<<<1|||1<<<2) (mo (mt 12 t12) (mt 13 t13)) (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) rfl
  · intro a0 a1 a2 hMa n0 n1 n2 t12 n13 n14 hdM; exact run a0 a1 a2 hMa hdM (n 9 (n 10 (n 11 (n 4 b (p 8)) (p 80)) (p 76)) (p 24)) (1<<<12) (1<<<0|||1<<<1|||1<<<2|||1<<<13|||1<<<14) (mt 12 t12) (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 13 n13)) (mf 14 n14)) rfl
  · intro a0 a1 a2 hMa n0 n1 n2 n12 n13 n14 hdM; exact run a0 a1 a2 hMa hdM (n 9 (n 10 (n 11 (n 3 (n 4 (n 5 b (p 0)) (p 8)) (p 4)) (p 40)) (p 36)) (p 24)) (0) (1<<<0|||1<<<1|||1<<<2|||1<<<12|||1<<<13|||1<<<14) mz (mo (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 12 n12)) (mf 13 n13)) (mf 14 n14)) rfl
set_option maxHeartbeats 800000 in
private lemma fno02_5 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 k4 u0 u1 u2 u3 u4 : V)
    (hK : IsComp5 C k0 k1 k2 k3 k4) (hM : IsComp5 C u0 u1 u2 u3 u4)
    (hd : Dj5 k0 k1 k2 k3 k4 {u0, u1, u2, u3, u4}) (σ : Equiv.Perm V) (hσ : AlmOn C G k4 k0 σ) (hnp : ¬ Packs C G)
    (ne02 : ¬ G.Adj (σ k0) (σ k2))
    : 10 ≤ 2 * rCount G σ k0 {u0, u1, u2, u3, u4} + 1 * rCount G σ k1 {u0, u1, u2, u3, u4} + 0 * rCount G σ k2 {u0, u1, u2, u3, u4} + 1 * rCount G σ k3 {u0, u1, u2, u3, u4} + 2 * rCount G σ k4 {u0, u1, u2, u3, u4} := by
  have run (a0 a1 a2 a3 a4 : V) (hMa : IsComp5 C a0 a1 a2 a3 a4) (hdM : Dj5 k0 k1 k2 k3 k4 {a0, a1, a2, a3, a4})
      (tr : DT) (tm fm : ℕ) (ht : ∀ i, tm.testBit i = true → (eb5_5 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4).getD i false = true)
      (hf : ∀ i, fm.testBit i = true → (eb5_5 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4).getD i false = false)
      (hev : evalDT 5 5 17176 0 false false pt5_5 wl6 10 tr tm fm = true) : 10 ≤ 2 * rCount G σ k0 {a0, a1, a2, a3, a4} + 1 * rCount G σ k1 {a0, a1, a2, a3, a4} + 0 * rCount G σ k2 {a0, a1, a2, a3, a4} + 1 * rCount G σ k3 {a0, a1, a2, a3, a4} + 2 * rCount G σ k4 {a0, a1, a2, a3, a4} := by
    have hsum : 10 ≤ wSumBool wl6 (eb5_5 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4) := evalDT_sound (mkCtx5_5 C G k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4 hK hMa hdM σ hσ hnp 17176 0 false false σ σ σ (fun _ => ne02) fd fd fd fd fd ff ff fz ff) pt5_5 wl6 10 rfl tr tm fm ht hf hev
    dsimp only [wl6] at hsum; rw [wSum_eb5_5 G σ 2 1 0 1 2 0 k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4 hMa] at hsum; clear tr tm fm ht hf hev; omega
  refine sym2_m5 C G σ k0 k4 (fun M => Dj5 k0 k1 k2 k3 k4 M → 10 ≤ 2 * rCount G σ k0 M + 1 * rCount G σ k1 M + 0 * rCount G σ k2 M + 1 * rCount G σ k3 M + 2 * rCount G σ k4 M) ?_ ?_ ?_ ?_ ?_ u0 u1 u2 u3 u4 hM hd
  · intro a0 a1 a2 a3 a4 hMa t0 t1 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 23 (n 22 (n 21 b (n 19 (n 18 b (n 5 b (n 4 b (p 336)))) (n 3 b (n 7 (n 12 (n 2 b (n 8 b (p 472))) (p 192)) (p 628))))) (n 3 (n 6 (n 15 b (n 4 b (n 8 b (p 244)))) (n 2 b (n 8 (n 20 b (n 18 b (p 288))) (p 1088)))) (n 24 (n 15 (n 11 (n 6 b (n 20 b (n 16 b (p 876)))) (n 5 b (p 60))) (n 9 (n 14 (n 4 b (n 8 b (p 244))) (p 196)) (p 260))) (n 18 (n 15 (n 16 (n 5 b (n 11 (n 21 b (n 12 (n 17 b (n 6 b (p 1176))) (p 76))) (p 60))) (n 7 (n 12 (n 5 b (n 2 b (p 652))) (p 236)) (p 624))) (n 9 (n 14 (n 6 (n 5 b (n 21 b (p 540))) (n 4 b (p 656))) (p 196)) (p 260))) (p 144))))) (n 2 (n 4 (n 3 b (n 9 (n 24 b (n 22 b (n 18 b (p 144)))) (n 7 (n 20 b (n 19 b (p 888))) (p 1168)))) (n 20 (n 5 (n 6 b (n 12 (n 22 b (n 13 (n 10 (n 15 b (n 8 b (p 244))) (n 16 b (p 128))) (p 20))) (p 56))) (n 16 (n 21 b (n 18 b (p 336))) (p 272))) (n 19 (n 17 (n 16 (n 6 b (n 12 (n 22 b (n 13 (n 18 b (n 7 b (p 1308))) (p 20))) (p 56))) (n 5 (n 10 (n 7 b (n 3 b (p 660))) (p 128)) (p 272))) (n 8 (n 13 (n 3 b (n 6 (n 9 b (p 504)) (p 520))) (p 80)) (p 356))) (p 64)))) (n 4 (n 21 (n 6 (n 5 b (n 14 (n 24 b (n 13 (n 11 (n 16 b (n 8 b (p 304))) (n 15 b (p 84))) (p 96))) (p 52))) (n 15 (n 20 b (n 18 b (p 288))) (p 228))) (n 17 (n 19 (n 15 (n 5 b (n 14 (n 24 b (n 13 (n 18 b (n 9 b (p 1112))) (p 96))) (p 52))) (n 6 (n 11 (n 9 b (n 3 b (p 1172))) (p 84)) (p 228))) (n 8 (n 13 (n 3 b (n 5 (n 7 b (p 628)) (p 792))) (p 392)) (p 472))) (p 48))) (n 8 (n 5 (n 6 (n 20 (n 21 b (n 17 b (p 48))) (n 19 (n 11 (n 17 (n 16 b (n 10 (n 3 b (n 7 b (p 660))) (p 128))) (n 21 b (p 48))) (n 9 (n 7 b (p 180)) (p 88))) (p 64))) (n 15 (n 12 (n 20 (n 21 b (n 17 b (p 48))) (n 18 (n 19 (n 17 b (n 3 b (p 520))) (p 64)) (p 288))) (p 56)) (p 228))) (n 16 (n 14 (n 21 (n 6 (n 20 b (n 19 b (p 64))) (n 15 (n 12 (n 20 b (n 19 b (p 64))) (p 56)) (p 228))) (n 18 (n 17 (n 15 (n 19 b (n 3 b (p 792))) (n 6 (n 24 b (p 540)) (p 228))) (p 48)) (p 336))) (p 52)) (p 272))) (p 0))))) (1<<<0|||1<<<1) (0) (mo (mt 0 t0) (mt 1 t1)) mz rfl
  · intro a0 a1 a2 a3 a4 hMa t0 n1 n4 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 20 (n 22 (n 23 (n 21 b (n 5 (n 10 (n 19 b (n 2 b (n 8 b (p 472)))) (n 7 b (p 424))) (n 18 (n 7 b (p 744)) (p 336)))) (n 15 (n 2 (n 16 b (n 5 b (p 272))) (n 8 (n 5 (n 21 b (n 17 b (p 48))) (n 16 (n 14 (n 21 b (n 17 b (p 48))) (p 52)) (p 272))) (p 0))) (n 7 (n 12 (n 2 (n 16 b (n 5 b (p 272))) (n 8 (n 6 (n 11 (n 21 b (n 9 b (p 1116))) (p 84)) (p 228)) (p 0))) (p 104)) (p 380)))) (n 15 (n 3 (n 19 (n 13 (n 24 b (n 8 (n 17 b (n 5 b (p 368))) (n 18 (n 5 b (p 832)) (p 884)))) (n 9 (n 6 b (p 20)) (p 36))) (n 5 (n 10 (n 13 (n 8 (n 23 b (n 12 (n 21 b (n 17 b (n 2 b (p 48)))) (n 9 b (p 92)))) (n 2 b (n 23 b (p 0)))) (n 6 (n 9 b (p 36)) (p 20))) (p 160)) (p 372))) (n 7 (n 5 (n 24 (n 13 (n 10 (n 23 b (n 2 b (n 8 b (p 0)))) (n 19 b (p 160))) (n 9 b (p 36))) (n 18 (n 10 (n 13 (n 16 (n 23 b (n 12 (n 2 b (n 8 b (p 0))) (n 6 b (p 56)))) (n 12 (n 2 b (n 8 (n 23 b (n 21 b (n 17 b (p 48)))) (p 304))) (p 236))) (n 6 (n 9 b (p 36)) (p 20))) (n 8 (n 17 b (p 140)) (p 108))) (p 144))) (n 19 (n 11 (n 24 (n 21 b (n 18 b (p 336))) (n 18 (n 16 (n 17 b (p 368)) (p 1264)) (p 144))) (p 60)) (p 372))) (p 4))) (n 8 (n 13 (n 3 (n 23 (n 19 b (n 5 b (p 372))) (n 7 (n 12 (n 2 b (n 6 (n 11 (n 5 b (n 16 b (p 272))) (p 84)) (p 228))) (p 104)) (p 380))) (n 7 (n 9 (n 14 (n 5 (n 24 b (n 6 (n 18 b (p 144)) (p 656))) (n 19 (n 11 (n 24 b (n 21 b (p 540))) (p 60)) (p 372))) (p 196)) (p 260)) (p 4))) (p 72)) (p 244)))) (n 5 (n 22 (n 23 (n 17 (n 18 (n 8 b (n 14 (n 24 b (n 10 (n 16 b (n 2 b (p 304))) (p 108))) (p 112))) (n 7 (n 12 (n 2 b (n 6 b (p 288))) (p 164)) (p 384))) (n 8 (n 13 (n 3 b (n 9 (n 14 (n 7 b (n 18 b (p 384))) (p 264)) (p 504))) (p 80)) (p 356))) (n 19 (n 7 (n 12 (n 17 (n 2 b (n 8 (n 11 (n 6 b (n 18 b (p 288))) (n 9 b (p 88))) (p 0))) (n 8 (n 13 (n 3 b (n 9 (n 6 b (p 520)) (p 504))) (p 80)) (p 356))) (n 9 (n 6 (n 18 b (p 164)) (p 56)) (p 92))) (n 18 (n 15 (n 11 (n 17 (n 3 b (n 16 b (p 660))) (n 8 (n 21 b (p 880)) (p 356))) (p 180)) (p 380)) (p 384))) (p 64))) (n 16 (n 15 (n 7 (n 17 (n 19 (n 18 (n 13 (n 8 b (n 14 (n 2 b (n 23 b (p 0))) (p 112))) (n 6 b (p 20))) (n 12 (n 2 b (n 9 (n 6 b (p 288)) (p 1092))) (p 164))) (n 23 (n 10 (n 8 b (n 2 b (p 764))) (p 160)) (p 64))) (n 8 (n 13 (n 3 (n 10 (n 23 b (n 19 b (p 64))) (n 24 b (p 140))) (n 9 (n 14 (n 23 b (n 6 (n 19 b (p 64)) (p 520))) (p 264)) (p 504))) (p 80)) (p 356))) (n 3 (n 18 (n 11 (n 8 (n 13 (n 19 b (n 23 b (p 64))) (n 17 b (p 80))) (n 17 (n 14 (n 2 b (n 19 b (p 764))) (p 112)) (p 356))) (p 180)) (p 384)) (p 4))) (n 8 (n 13 (n 23 (n 3 (n 18 b (n 7 b (p 384))) (n 7 (n 9 (n 14 (n 24 b (n 6 b (p 656))) (p 196)) (p 260)) (p 4))) (n 7 (n 19 (n 12 (n 2 (n 3 b (n 9 b (p 260))) (n 6 (n 11 (n 9 (n 3 b (n 14 (n 24 b (n 18 b (p 144))) (p 196))) (n 3 b (p 260))) (p 84)) (p 228))) (p 104)) (p 64)) (p 380))) (p 72)) (p 244))) (p 184))) (p 24))) (1<<<0) (1<<<1|||1<<<4) (mt 0 t0) (mo (mf 1 n1) (mf 4 n4)) rfl
  · intro a0 a1 a2 a3 a4 hMa n0 n1 n2 n3 n4 t20 t21 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 22 (n 24 (n 23 b (n 8 (n 15 b (n 7 b (p 380))) (p 0))) (n 9 (n 17 (n 16 (n 8 b (n 23 b (p 0))) (n 7 (n 8 b (p 304)) (p 624))) (n 6 (n 5 (n 10 (n 11 (n 16 b (n 8 b (p 304))) (p 704)) (p 140)) (p 368)) (p 924))) (p 12))) (n 7 (n 24 (n 19 (n 15 (n 8 b (n 23 b (p 0))) (n 9 (n 8 b (p 244)) (p 260))) (n 5 (n 6 (n 11 (n 10 (n 15 b (n 8 b (p 244))) (p 160)) (p 556)) (p 928)) (p 372))) (n 9 (n 18 (n 8 (n 5 (n 6 b (n 15 b (p 1208))) (n 16 (n 17 b (p 368)) (p 652))) (n 23 (n 15 b (p 244)) (p 0))) (p 144)) (p 12))) (p 4))) (1<<<20|||1<<<21) (1<<<0|||1<<<1|||1<<<2|||1<<<3|||1<<<4) (mo (mt 20 t20) (mt 21 t21)) (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 3 n3)) (mf 4 n4)) rfl
  · intro a0 a1 a2 a3 a4 hMa n0 n1 n2 n3 n4 t20 n21 n24 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 15 (n 9 (n 6 (n 7 (n 8 (n 5 (n 17 (n 18 b (n 22 b (p 144))) (n 23 b (p 48))) (n 17 (n 18 (n 12 (n 13 (n 22 b (n 16 b (p 652))) (p 96)) (p 76)) (p 336)) (p 368))) (n 5 (n 17 (n 16 (n 19 b (p 472)) (p 304)) (p 840)) (p 832))) (n 16 (n 18 (n 19 (n 5 (n 22 b (p 4)) (p 744)) (p 628)) (p 836)) (p 624))) (p 116)) (p 12)) (p 216)) (1<<<20) (1<<<0|||1<<<1|||1<<<2|||1<<<3|||1<<<4|||1<<<21|||1<<<24) (mt 20 t20) (mo (mo (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 3 n3)) (mf 4 n4)) (mf 21 n21)) (mf 24 n24)) rfl
  · intro a0 a1 a2 a3 a4 hMa n0 n1 n2 n3 n4 n20 n21 n22 n23 n24 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 15 (n 16 (n 17 (n 18 (n 19 (n 5 (n 9 (n 8 (n 6 (n 7 b (p 4)) (p 116)) (p 0)) (p 12)) (p 24)) (p 64)) (p 144)) (p 48)) (p 184)) (p 216)) (0) (1<<<0|||1<<<1|||1<<<2|||1<<<3|||1<<<4|||1<<<20|||1<<<21|||1<<<22|||1<<<23|||1<<<24) mz (mo (mo (mo (mo (mo (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 3 n3)) (mf 4 n4)) (mf 20 n20)) (mf 21 n21)) (mf 22 n22)) (mf 23 n23)) (mf 24 n24)) rfl
private lemma fred03_1_all {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 k4 u0 : V)
    (hK : IsComp5 C k0 k1 k2 k3 k4) (hM : IsComp1 C u0)
    (hd : Dj5 k0 k1 k2 k3 k4 {u0}) (σ : Equiv.Perm V) (hσ : AlmOn C G k4 k0 σ) (hnp : ¬ Packs C G)
    (hsc0 : 9 ≤ kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4)) (hmin : MinSc C G k0 k1 k2 k3 k4 σ)
    (ne13 : ¬ G.Adj (σ k1) (σ k3))
    (ne14 : ¬ G.Adj (σ k1) (σ k4))
    : 1 ≤ 2 * rCount G σ k0 {u0} + 0 * rCount G σ k1 {u0} + 0 * rCount G σ k2 {u0} + 0 * rCount G σ k3 {u0} + 1 * rCount G σ k4 {u0} := by
  have hev : evalDT 5 1 16412 9 false false pt5_1 wl7 1 (n 4 b (a 10)) 0 0 = true := rfl
  have hsum : 1 ≤ wSumBool wl7 (eb5_1 G σ k0 k1 k2 k3 k4 k0 u0) := evalDT_sound (mkCtx5_1 C G k0 k1 k2 k3 k4 k0 u0 hK hM hd σ hσ hnp 16412 9 false false σ σ σ fd fd fd (fun _ => ne13) (fun _ => ne14) fd ff ff (fun _ => ⟨hsc0, hmin⟩) ff) pt5_1 wl7 1 rfl (n 4 b (a 10)) 0 0 mz mz hev
  dsimp only [wl7] at hsum; rw [wSum_eb5_1 G σ 2 0 0 0 1 0 k0 k1 k2 k3 k4 k0 u0] at hsum; clear hev; omega
set_option maxHeartbeats 800000 in
private lemma fred03_3 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 k4 u0 u1 u2 : V)
    (hK : IsComp5 C k0 k1 k2 k3 k4) (hM : IsComp3 C u0 u1 u2)
    (hd : Dj5 k0 k1 k2 k3 k4 {u0, u1, u2}) (σ : Equiv.Perm V) (hσ : AlmOn C G k4 k0 σ) (hnp : ¬ Packs C G)
    (hsc0 : 9 ≤ kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4)) (hmin : MinSc C G k0 k1 k2 k3 k4 σ)
    (ne13 : ¬ G.Adj (σ k1) (σ k3))
    (ne14 : ¬ G.Adj (σ k1) (σ k4))
    : 3 ≤ 2 * rCount G σ k0 {u0, u1, u2} + 0 * rCount G σ k1 {u0, u1, u2} + 0 * rCount G σ k2 {u0, u1, u2} + 0 * rCount G σ k3 {u0, u1, u2} + 1 * rCount G σ k4 {u0, u1, u2} := by
  have run (a0 a1 a2 : V) (hMa : IsComp3 C a0 a1 a2) (hdM : Dj5 k0 k1 k2 k3 k4 {a0, a1, a2})
      (tr : DT) (tm fm : ℕ) (ht : ∀ i, tm.testBit i = true → (eb5_3 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2).getD i false = true)
      (hf : ∀ i, fm.testBit i = true → (eb5_3 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2).getD i false = false)
      (hev : evalDT 5 3 16412 9 false false pt5_3 wl8 3 tr tm fm = true) : 3 ≤ 2 * rCount G σ k0 {a0, a1, a2} + 0 * rCount G σ k1 {a0, a1, a2} + 0 * rCount G σ k2 {a0, a1, a2} + 0 * rCount G σ k3 {a0, a1, a2} + 1 * rCount G σ k4 {a0, a1, a2} := by
    have hsum : 3 ≤ wSumBool wl8 (eb5_3 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2) := evalDT_sound (mkCtx5_3 C G k0 k1 k2 k3 k4 k0 a0 a1 a2 hK hMa hdM σ hσ hnp 16412 9 false false σ σ σ fd fd fd (fun _ => ne13) (fun _ => ne14) fd ff ff (fun _ => ⟨hsc0, hmin⟩) ff) pt5_3 wl8 3 rfl tr tm fm ht hf hev
    dsimp only [wl8] at hsum; rw [wSum_eb5_3 G σ 2 0 0 0 1 0 k0 k1 k2 k3 k4 k0 a0 a1 a2 hMa] at hsum; clear tr tm fm ht hf hev; omega
  refine sym2_m3 C G σ k0 k4 (fun M => Dj5 k0 k1 k2 k3 k4 M → 3 ≤ 2 * rCount G σ k0 M + 0 * rCount G σ k1 M + 0 * rCount G σ k2 M + 0 * rCount G σ k3 M + 1 * rCount G σ k4 M) ?_ ?_ ?_ ?_ ?_ u0 u1 u2 hM hd
  · intro a0 a1 a2 hMa t0 t1 hdM; exact run a0 a1 a2 hMa hdM b (1<<<0|||1<<<1) (0) (mo (mt 0 t0) (mt 1 t1)) mz rfl
  · intro a0 a1 a2 hMa t0 n1 n2 hdM; exact run a0 a1 a2 hMa hdM (n 12 b (a 1)) (1<<<0) (1<<<1|||1<<<2) (mt 0 t0) (mo (mf 1 n1) (mf 2 n2)) rfl
  · intro a0 a1 a2 hMa n0 n1 n2 t12 t13 hdM; exact run a0 a1 a2 hMa hdM (n 14 b (a 0)) (1<<<12|||1<<<13) (1<<<0|||1<<<1|||1<<<2) (mo (mt 12 t12) (mt 13 t13)) (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) rfl
  · intro a0 a1 a2 hMa n0 n1 n2 t12 n13 n14 hdM; exact run a0 a1 a2 hMa hdM (a 0) (1<<<12) (1<<<0|||1<<<1|||1<<<2|||1<<<13|||1<<<14) (mt 12 t12) (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 13 n13)) (mf 14 n14)) rfl
  · intro a0 a1 a2 hMa n0 n1 n2 n12 n13 n14 hdM; exact run a0 a1 a2 hMa hdM (a 0) (0) (1<<<0|||1<<<1|||1<<<2|||1<<<12|||1<<<13|||1<<<14) mz (mo (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 12 n12)) (mf 13 n13)) (mf 14 n14)) rfl
set_option maxHeartbeats 800000 in
private lemma fred03_5 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 k4 u0 u1 u2 u3 u4 : V)
    (hK : IsComp5 C k0 k1 k2 k3 k4) (hM : IsComp5 C u0 u1 u2 u3 u4)
    (hd : Dj5 k0 k1 k2 k3 k4 {u0, u1, u2, u3, u4}) (σ : Equiv.Perm V) (hσ : AlmOn C G k4 k0 σ) (hnp : ¬ Packs C G)
    (hsc0 : 9 ≤ kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4)) (hmin : MinSc C G k0 k1 k2 k3 k4 σ)
    (ne13 : ¬ G.Adj (σ k1) (σ k3))
    (ne14 : ¬ G.Adj (σ k1) (σ k4))
    : 5 ≤ 2 * rCount G σ k0 {u0, u1, u2, u3, u4} + 0 * rCount G σ k1 {u0, u1, u2, u3, u4} + 0 * rCount G σ k2 {u0, u1, u2, u3, u4} + 0 * rCount G σ k3 {u0, u1, u2, u3, u4} + 1 * rCount G σ k4 {u0, u1, u2, u3, u4} := by
  have run (a0 a1 a2 a3 a4 : V) (hMa : IsComp5 C a0 a1 a2 a3 a4) (hdM : Dj5 k0 k1 k2 k3 k4 {a0, a1, a2, a3, a4})
      (tr : DT) (tm fm : ℕ) (ht : ∀ i, tm.testBit i = true → (eb5_5 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4).getD i false = true)
      (hf : ∀ i, fm.testBit i = true → (eb5_5 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4).getD i false = false)
      (hev : evalDT 5 5 16412 9 false false pt5_5 wl9 5 tr tm fm = true) : 5 ≤ 2 * rCount G σ k0 {a0, a1, a2, a3, a4} + 0 * rCount G σ k1 {a0, a1, a2, a3, a4} + 0 * rCount G σ k2 {a0, a1, a2, a3, a4} + 0 * rCount G σ k3 {a0, a1, a2, a3, a4} + 1 * rCount G σ k4 {a0, a1, a2, a3, a4} := by
    have hsum : 5 ≤ wSumBool wl9 (eb5_5 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4) := evalDT_sound (mkCtx5_5 C G k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4 hK hMa hdM σ hσ hnp 16412 9 false false σ σ σ fd fd fd (fun _ => ne13) (fun _ => ne14) fd ff ff (fun _ => ⟨hsc0, hmin⟩) ff) pt5_5 wl9 5 rfl tr tm fm ht hf hev
    dsimp only [wl9] at hsum; rw [wSum_eb5_5 G σ 2 0 0 0 1 0 k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4 hMa] at hsum; clear tr tm fm ht hf hev; omega
  refine sym2_m5 C G σ k0 k4 (fun M => Dj5 k0 k1 k2 k3 k4 M → 5 ≤ 2 * rCount G σ k0 M + 0 * rCount G σ k1 M + 0 * rCount G σ k2 M + 0 * rCount G σ k3 M + 1 * rCount G σ k4 M) ?_ ?_ ?_ ?_ ?_ u0 u1 u2 u3 u4 hM hd
  · intro a0 a1 a2 a3 a4 hMa t0 t1 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 2 b (n 4 b (n 23 b (a 0)))) (1<<<0|||1<<<1) (0) (mo (mt 0 t0) (mt 1 t1)) mz rfl
  · intro a0 a1 a2 a3 a4 hMa t0 n1 n4 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 20 (n 10 (n 2 b (n 23 (n 13 (n 3 b (n 22 b (a 1))) (a 17)) (a 0))) (a 52)) (a 6)) (1<<<0) (1<<<1|||1<<<4) (mt 0 t0) (mo (mf 1 n1) (mf 4 n4)) rfl
  · intro a0 a1 a2 a3 a4 hMa n0 n1 n2 n3 n4 t20 t21 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 22 (n 23 (n 24 b (a 3)) (a 0)) (a 1)) (1<<<20|||1<<<21) (1<<<0|||1<<<1|||1<<<2|||1<<<3|||1<<<4) (mo (mt 20 t20) (mt 21 t21)) (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 3 n3)) (mf 4 n4)) rfl
  · intro a0 a1 a2 a3 a4 hMa n0 n1 n2 n3 n4 t20 n21 n24 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (a 3) (1<<<20) (1<<<0|||1<<<1|||1<<<2|||1<<<3|||1<<<4|||1<<<21|||1<<<24) (mt 20 t20) (mo (mo (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 3 n3)) (mf 4 n4)) (mf 21 n21)) (mf 24 n24)) rfl
  · intro a0 a1 a2 a3 a4 hMa n0 n1 n2 n3 n4 n20 n21 n22 n23 n24 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (a 3) (0) (1<<<0|||1<<<1|||1<<<2|||1<<<3|||1<<<4|||1<<<20|||1<<<21|||1<<<22|||1<<<23|||1<<<24) mz (mo (mo (mo (mo (mo (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 3 n3)) (mf 4 n4)) (mf 20 n20)) (mf 21 n21)) (mf 22 n22)) (mf 23 n23)) (mf 24 n24)) rfl
private lemma fred13_1_all {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 k4 u0 : V)
    (hK : IsComp5 C k0 k1 k2 k3 k4) (hM : IsComp1 C u0)
    (hd : Dj5 k0 k1 k2 k3 k4 {u0}) (σ : Equiv.Perm V) (hσ : AlmOn C G k4 k0 σ) (hnp : ¬ Packs C G)
    (hsc0 : 9 ≤ kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4)) (hmin : MinSc C G k0 k1 k2 k3 k4 σ)
    (ne03 : ¬ G.Adj (σ k0) (σ k3))
    (ne14 : ¬ G.Adj (σ k1) (σ k4))
    : 2 ≤ 2 * rCount G σ k0 {u0} + 1 * rCount G σ k1 {u0} + 1 * rCount G σ k2 {u0} + 1 * rCount G σ k3 {u0} + 1 * rCount G σ k4 {u0} := by
  have hev : evalDT 5 1 16660 9 false false pt5_1 wl10 2 (n 1 (n 3 b (n 0 b (p 12))) (n 0 b (p 8))) 0 0 = true := rfl
  have hsum : 2 ≤ wSumBool wl10 (eb5_1 G σ k0 k1 k2 k3 k4 k0 u0) := evalDT_sound (mkCtx5_1 C G k0 k1 k2 k3 k4 k0 u0 hK hM hd σ hσ hnp 16660 9 false false σ σ σ fd (fun _ => ne03) fd fd (fun _ => ne14) fd ff ff (fun _ => ⟨hsc0, hmin⟩) ff) pt5_1 wl10 2 rfl (n 1 (n 3 b (n 0 b (p 12))) (n 0 b (p 8))) 0 0 mz mz hev
  dsimp only [wl10] at hsum; rw [wSum_eb5_1 G σ 2 1 1 1 1 0 k0 k1 k2 k3 k4 k0 u0] at hsum; clear hev; omega
set_option maxHeartbeats 800000 in
private lemma fred13_3 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 k4 u0 u1 u2 : V)
    (hK : IsComp5 C k0 k1 k2 k3 k4) (hM : IsComp3 C u0 u1 u2)
    (hd : Dj5 k0 k1 k2 k3 k4 {u0, u1, u2}) (σ : Equiv.Perm V) (hσ : AlmOn C G k4 k0 σ) (hnp : ¬ Packs C G)
    (hsc0 : 9 ≤ kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4)) (hmin : MinSc C G k0 k1 k2 k3 k4 σ)
    (ne03 : ¬ G.Adj (σ k0) (σ k3))
    (ne14 : ¬ G.Adj (σ k1) (σ k4))
    : 6 ≤ 2 * rCount G σ k0 {u0, u1, u2} + 1 * rCount G σ k1 {u0, u1, u2} + 1 * rCount G σ k2 {u0, u1, u2} + 1 * rCount G σ k3 {u0, u1, u2} + 1 * rCount G σ k4 {u0, u1, u2} := by
  have run (a0 a1 a2 : V) (hMa : IsComp3 C a0 a1 a2) (hdM : Dj5 k0 k1 k2 k3 k4 {a0, a1, a2})
      (tr : DT) (tm fm : ℕ) (ht : ∀ i, tm.testBit i = true → (eb5_3 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2).getD i false = true)
      (hf : ∀ i, fm.testBit i = true → (eb5_3 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2).getD i false = false)
      (hev : evalDT 5 3 16660 9 false false pt5_3 wl11 6 tr tm fm = true) : 6 ≤ 2 * rCount G σ k0 {a0, a1, a2} + 1 * rCount G σ k1 {a0, a1, a2} + 1 * rCount G σ k2 {a0, a1, a2} + 1 * rCount G σ k3 {a0, a1, a2} + 1 * rCount G σ k4 {a0, a1, a2} := by
    have hsum : 6 ≤ wSumBool wl11 (eb5_3 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2) := evalDT_sound (mkCtx5_3 C G k0 k1 k2 k3 k4 k0 a0 a1 a2 hK hMa hdM σ hσ hnp 16660 9 false false σ σ σ fd (fun _ => ne03) fd fd (fun _ => ne14) fd ff ff (fun _ => ⟨hsc0, hmin⟩) ff) pt5_3 wl11 6 rfl tr tm fm ht hf hev
    dsimp only [wl11] at hsum; rw [wSum_eb5_3 G σ 2 1 1 1 1 0 k0 k1 k2 k3 k4 k0 a0 a1 a2 hMa] at hsum; clear tr tm fm ht hf hev; omega
  refine sym2_m3 C G σ k0 k4 (fun M => Dj5 k0 k1 k2 k3 k4 M → 6 ≤ 2 * rCount G σ k0 M + 1 * rCount G σ k1 M + 1 * rCount G σ k2 M + 1 * rCount G σ k3 M + 1 * rCount G σ k4 M) ?_ ?_ ?_ ?_ ?_ u0 u1 u2 hM hd
  · intro a0 a1 a2 hMa t0 t1 hdM; exact run a0 a1 a2 hMa hdM (n 2 b (n 6 (n 12 b (n 7 b (n 5 b (p 16)))) (n 13 (n 7 b (n 11 b (p 56))) (n 5 (n 11 b (p 68)) (p 60))))) (1<<<0|||1<<<1) (0) (mo (mt 0 t0) (mt 1 t1)) mz rfl
  · intro a0 a1 a2 hMa t0 n1 n2 hdM; exact run a0 a1 a2 hMa hdM (n 12 (n 6 (n 3 (n 9 b (n 4 b (n 11 b (n 8 b (n 13 b (a 30)))))) (n 4 (n 5 b (n 10 b (n 8 b (n 13 b (a 12))))) (n 11 (n 5 b (n 10 b (n 8 b (n 13 b (a 12))))) (n 8 (n 7 b (n 13 b (a 68))) (n 13 (n 14 b (a 63)) (a 32)))))) (n 9 (n 3 (n 13 b (n 10 b (p 52))) (p 32)) (p 12))) (n 9 (n 3 (n 7 (n 8 b (n 10 b (p 220))) (n 10 (n 11 b (p 124)) (p 232))) (p 4)) (a 1))) (1<<<0) (1<<<1|||1<<<2) (mt 0 t0) (mo (mf 1 n1) (mf 2 n2)) rfl
  · intro a0 a1 a2 hMa n0 n1 n2 t12 t13 hdM; exact run a0 a1 a2 hMa hdM (n 14 (n 6 (n 7 (n 8 b (n 11 b (p 28))) (n 10 (n 4 b (p 284)) (p 20))) (n 9 (n 3 (n 7 b (n 10 b (p 20))) (p 32)) (p 12))) (n 11 (n 5 (n 6 (n 7 b (n 10 b (p 20))) (n 9 (n 3 b (p 32)) (p 12))) (p 0)) (a 0))) (1<<<12|||1<<<13) (1<<<0|||1<<<1|||1<<<2) (mo (mt 12 t12) (mt 13 t13)) (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) rfl
  · intro a0 a1 a2 hMa n0 n1 n2 t12 n13 n14 hdM; exact run a0 a1 a2 hMa hdM (n 3 (n 9 (n 10 (n 11 (n 4 b (p 8)) (a 0)) (a 2)) (p 132)) (p 304)) (1<<<12) (1<<<0|||1<<<1|||1<<<2|||1<<<13|||1<<<14) (mt 12 t12) (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 13 n13)) (mf 14 n14)) rfl
  · intro a0 a1 a2 hMa n0 n1 n2 n12 n13 n14 hdM; exact run a0 a1 a2 hMa hdM (n 3 (n 9 (n 10 (n 11 (n 4 (n 5 b (p 0)) (p 8)) (a 0)) (a 2)) (a 1)) (p 4)) (0) (1<<<0|||1<<<1|||1<<<2|||1<<<12|||1<<<13|||1<<<14) mz (mo (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 12 n12)) (mf 13 n13)) (mf 14 n14)) rfl
set_option maxHeartbeats 800000 in
private lemma fred13_5 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 k4 u0 u1 u2 u3 u4 : V)
    (hK : IsComp5 C k0 k1 k2 k3 k4) (hM : IsComp5 C u0 u1 u2 u3 u4)
    (hd : Dj5 k0 k1 k2 k3 k4 {u0, u1, u2, u3, u4}) (σ : Equiv.Perm V) (hσ : AlmOn C G k4 k0 σ) (hnp : ¬ Packs C G)
    (hsc0 : 9 ≤ kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4)) (hmin : MinSc C G k0 k1 k2 k3 k4 σ)
    (ne03 : ¬ G.Adj (σ k0) (σ k3))
    (ne14 : ¬ G.Adj (σ k1) (σ k4))
    : 10 ≤ 2 * rCount G σ k0 {u0, u1, u2, u3, u4} + 1 * rCount G σ k1 {u0, u1, u2, u3, u4} + 1 * rCount G σ k2 {u0, u1, u2, u3, u4} + 1 * rCount G σ k3 {u0, u1, u2, u3, u4} + 1 * rCount G σ k4 {u0, u1, u2, u3, u4} := by
  have run (a0 a1 a2 a3 a4 : V) (hMa : IsComp5 C a0 a1 a2 a3 a4) (hdM : Dj5 k0 k1 k2 k3 k4 {a0, a1, a2, a3, a4})
      (tr : DT) (tm fm : ℕ) (ht : ∀ i, tm.testBit i = true → (eb5_5 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4).getD i false = true)
      (hf : ∀ i, fm.testBit i = true → (eb5_5 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4).getD i false = false)
      (hev : evalDT 5 5 16660 9 false false pt5_5 wl12 10 tr tm fm = true) : 10 ≤ 2 * rCount G σ k0 {a0, a1, a2, a3, a4} + 1 * rCount G σ k1 {a0, a1, a2, a3, a4} + 1 * rCount G σ k2 {a0, a1, a2, a3, a4} + 1 * rCount G σ k3 {a0, a1, a2, a3, a4} + 1 * rCount G σ k4 {a0, a1, a2, a3, a4} := by
    have hsum : 10 ≤ wSumBool wl12 (eb5_5 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4) := evalDT_sound (mkCtx5_5 C G k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4 hK hMa hdM σ hσ hnp 16660 9 false false σ σ σ fd (fun _ => ne03) fd fd (fun _ => ne14) fd ff ff (fun _ => ⟨hsc0, hmin⟩) ff) pt5_5 wl12 10 rfl tr tm fm ht hf hev
    dsimp only [wl12] at hsum; rw [wSum_eb5_5 G σ 2 1 1 1 1 0 k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4 hMa] at hsum; clear tr tm fm ht hf hev; omega
  refine sym2_m5 C G σ k0 k4 (fun M => Dj5 k0 k1 k2 k3 k4 M → 10 ≤ 2 * rCount G σ k0 M + 1 * rCount G σ k1 M + 1 * rCount G σ k2 M + 1 * rCount G σ k3 M + 1 * rCount G σ k4 M) ?_ ?_ ?_ ?_ ?_ u0 u1 u2 u3 u4 hM hd
  · intro a0 a1 a2 a3 a4 hMa t0 t1 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 2 (n 3 (n 4 b (n 10 (n 20 b (n 13 b (n 16 b (p 132)))) (n 23 (n 21 b (n 8 b (p 344))) (n 16 (n 17 b (p 176)) (p 128))))) (n 12 (n 22 (n 10 (n 20 b (n 14 b (n 17 b (p 264)))) (n 24 (n 4 b (n 7 b (n 23 b (p 420)))) (n 17 (n 7 b (p 648)) (p 644)))) (n 14 (n 11 (n 24 b (n 8 b (p 788))) (n 9 (n 19 b (p 492)) (p 636))) (n 16 (n 6 (n 5 b (p 328)) (p 316)) (p 416)))) (n 24 (n 21 (n 14 (n 4 b (n 23 b (n 16 b (p 352)))) (n 8 (n 18 b (p 408)) (p 404))) (n 5 (n 15 (n 9 b (p 412)) (p 508)) (p 76))) (n 16 (n 6 (n 5 (n 15 b (p 268)) (p 332)) (p 632)) (p 236))))) (n 13 (n 23 (n 10 (n 20 (n 3 b (n 12 (n 22 b (n 14 b (n 5 b (p 328)))) (n 24 (n 21 b (n 5 b (p 76))) (n 5 (n 15 b (p 268)) (p 332))))) (n 11 (n 3 b (n 14 (n 24 b (n 12 b (n 16 b (p 236)))) (n 16 (n 6 b (p 240)) (p 496)))) (n 8 (n 18 (n 9 b (p 88)) (p 188)) (p 296)))) (n 21 (n 11 (n 3 b (n 24 (n 14 b (n 6 b (n 22 b (p 316)))) (n 16 (n 6 b (p 320)) (p 500)))) (n 20 (n 9 (n 19 b (n 6 b (a 282))) (n 16 (n 15 b (a 280)) (a 281))) (n 8 (n 18 (n 9 b (p 88)) (p 188)) (p 296)))) (n 8 (n 18 (n 9 (n 19 b (p 776)) (p 172)) (p 300)) (p 460)))) (n 11 (n 14 (n 4 (n 21 b (n 17 b (p 48))) (n 8 (n 18 (n 12 b (n 5 b (p 860))) (a 0)) (p 0))) (n 16 (n 6 (n 5 (n 15 b (p 616)) (p 52)) (p 480)) (p 232))) (n 5 (n 15 (n 9 (n 19 (n 4 b (n 8 b (p 0))) (p 476)) (p 484)) (p 84)) (p 292)))) (n 24 (n 21 (n 4 (n 11 (n 14 b (n 23 b (n 16 b (p 232)))) (n 17 (n 7 b (p 448)) (p 252))) (n 8 (n 18 (n 22 (n 20 b (n 16 b (p 132))) (n 16 (n 6 b (p 20)) (p 276))) (p 100)) (p 68))) (n 9 (n 19 (n 5 (n 15 (n 4 b (n 8 b (p 68))) (p 452)) (p 456)) (p 392)) (p 620))) (n 16 (n 6 (n 5 (n 15 (n 10 (n 11 b (n 17 b (p 252))) (n 9 (n 19 b (p 692)) (p 680))) (p 464)) (p 96)) (p 396)) (p 308))))) (1<<<0|||1<<<1) (0) (mo (mt 0 t0) (mt 1 t1)) mz rfl
  · intro a0 a1 a2 a3 a4 hMa t0 n1 n4 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 10 (n 20 (n 12 (n 22 (n 2 (n 5 (n 15 b (n 7 b (n 11 b (n 16 b (n 24 b (a 286)))))) (n 14 (n 11 b (n 17 b (n 6 b (n 21 b (a 330))))) (n 9 (n 6 b (n 17 b (n 21 b (a 331)))) (n 18 (n 16 b (n 23 b (a 270))) (n 24 (n 21 b (a 296)) (a 267)))))) (n 13 (n 23 (n 3 b (n 11 (n 14 b (n 6 b (n 18 b (a 189)))) (n 9 (n 19 b (n 7 b (a 261))) (n 17 (n 18 b (a 320)) (a 166))))) (n 8 (n 18 (n 11 b (n 5 b (p 292))) (a 0)) (p 0))) (n 8 (n 18 (n 5 (n 15 b (n 6 b (a 305))) (n 21 (n 24 b (p 96)) (p 456))) (p 100)) (p 68)))) (n 13 (n 3 (n 23 (n 11 b (n 5 b (n 19 b (n 6 b (a 335))))) (n 2 b (n 8 (n 18 b (a 0)) (p 0)))) (n 17 (n 7 (n 5 (n 15 b (n 8 b (a 179))) (n 14 (n 11 b (p 60)) (p 328))) (p 4)) (a 1))) (n 5 (n 15 (n 9 (n 19 (n 16 b (p 276)) (p 588)) (p 36)) (p 72)) (p 248)))) (n 23 (n 3 (n 13 (n 22 (n 21 b (n 5 b (n 19 b (n 6 b (a 284))))) (n 8 (n 18 b (n 17 b (n 9 b (a 9)))) (n 7 (n 9 b (n 15 b (n 24 b (a 276)))) (n 19 (n 16 b (a 321)) (a 260))))) (n 22 (n 2 b (n 8 (n 18 b (p 100)) (p 68))) (n 5 (n 15 (n 16 b (p 276)) (p 72)) (p 248)))) (n 17 (n 7 (n 5 (n 15 (n 24 b (n 16 b (p 236))) (n 9 (n 24 b (p 268)) (a 275))) (n 24 (n 21 (n 19 b (a 178)) (p 76)) (p 332))) (p 156)) (p 120))) (n 5 (n 15 (n 16 (n 9 (n 19 (n 6 b (p 56)) (p 432)) (p 92)) (p 352)) (p 104)) (p 440)))) (n 5 (n 15 (n 12 (n 13 (n 11 (n 14 (n 22 b (n 16 b (p 184))) (n 17 (n 7 b (p 584)) (p 580))) (n 8 (n 18 (n 17 b (p 864)) (p 512)) (p 516))) (n 17 (n 7 (n 16 (n 6 b (p 844)) (p 132)) (p 668)) (p 80))) (n 8 (n 18 (n 9 (n 19 (n 7 b (n 3 b (p 156))) (p 376)) (p 748)) (p 164)) (p 596))) (a 6)) (p 24))) (n 5 (n 15 (n 7 (n 17 (n 22 (n 12 (n 8 (n 18 b (n 24 b (p 600))) (n 24 (n 21 b (p 344)) (p 108))) (n 16 (n 6 (n 20 b (n 8 b (p 596))) (p 740)) (p 364))) (n 8 (n 18 (n 9 (n 19 b (p 160)) (p 576)) (p 168)) (p 284))) (n 23 (n 21 (n 24 (n 8 (n 22 b (n 3 b (a 1))) (n 2 b (a 199))) (p 140)) (p 532)) (p 176))) (n 23 (n 21 (n 24 (n 22 (n 20 (n 18 b (n 2 b (a 249))) (n 11 (n 14 b (p 584)) (p 180))) (n 3 (n 8 b (p 284)) (p 4))) (p 572)) (p 424)) (p 420))) (p 204)) (p 208))) (1<<<0) (1<<<1|||1<<<4) (mt 0 t0) (mo (mf 1 n1) (mf 4 n4)) rfl
  · intro a0 a1 a2 a3 a4 hMa n0 n1 n2 n3 n4 t20 t21 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 23 (n 13 (n 10 (n 11 (n 12 (n 14 (n 22 (n 24 b (n 9 b (p 12))) (n 17 (n 7 b (p 4)) (a 1))) (n 9 (n 19 (n 22 b (n 6 b (p 316))) (p 324)) (p 256))) (n 17 (n 7 (n 24 (n 14 b (n 9 b (p 256))) (n 5 (n 15 b (p 268)) (p 332))) (p 156)) (p 120))) (n 16 (n 6 (n 22 (n 24 (n 14 b (n 9 b (p 256))) (n 8 (n 18 b (p 980)) (p 720))) (n 9 (n 19 (n 5 b (p 60)) (p 556)) (p 932))) (p 400)) (p 312))) (n 5 (n 15 (n 24 (n 22 (n 12 (n 7 b (n 18 b (a 153))) (n 17 (n 7 b (p 156)) (p 120))) (n 8 (n 18 (n 9 b (p 576)) (p 168)) (p 284))) (n 7 (n 17 (n 8 (n 9 b (p 12)) (p 108)) (p 140)) (p 572))) (p 204)) (p 208))) (n 8 (n 18 (n 22 (n 24 (n 10 (n 11 (n 5 b (n 16 b (a 141))) (n 16 (n 6 b (p 400)) (p 312))) (n 5 (n 15 (n 9 b (p 824)) (p 204)) (p 208))) (n 6 (n 16 (n 5 (n 15 b (p 464)) (p 96)) (p 308)) (p 396))) (n 5 (n 15 (n 6 (n 16 (n 9 b (p 36)) (p 276)) (p 20)) (p 72)) (p 248))) (p 100)) (p 68))) (n 8 (n 18 (n 12 (n 14 (n 10 (n 11 (n 5 (n 6 b (n 15 b (a 269))) (n 16 (n 17 b (a 252)) (a 251))) (n 5 (n 15 (n 9 b (p 484)) (p 84)) (p 292))) (n 5 (n 15 (n 17 (n 7 b (p 420)) (p 176)) (p 204)) (p 208))) (n 6 (n 16 (n 9 (n 19 (n 17 b (p 948)) (p 324)) (p 256)) (p 972)) (p 976))) (n 5 (n 15 (n 6 (n 16 (n 9 (n 19 b (p 432)) (p 92)) (p 352)) (p 56)) (p 104)) (p 440))) (a 0)) (p 0))) (1<<<20|||1<<<21) (1<<<0|||1<<<1|||1<<<2|||1<<<3|||1<<<4) (mo (mt 20 t20) (mt 21 t21)) (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 3 n3)) (mf 4 n4)) rfl
  · intro a0 a1 a2 a3 a4 hMa n0 n1 n2 n3 n4 t20 n21 n24 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 5 (n 15 (n 16 (n 19 (n 9 (n 6 (n 10 (n 7 (n 8 b (n 17 b (p 840))) (n 18 (n 11 b (p 708)) (p 836))) (n 8 (n 18 (n 17 b (p 140)) (p 340)) (p 108))) (p 116)) (p 12)) (a 3)) (a 29)) (p 216)) (p 696)) (1<<<20) (1<<<0|||1<<<1|||1<<<2|||1<<<3|||1<<<4|||1<<<21|||1<<<24) (mt 20 t20) (mo (mo (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 3 n3)) (mf 4 n4)) (mf 21 n21)) (mf 24 n24)) rfl
  · intro a0 a1 a2 a3 a4 hMa n0 n1 n2 n3 n4 n20 n21 n22 n23 n24 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 5 (n 7 (n 8 (n 6 (n 9 (n 15 (n 16 (n 17 (n 18 (n 19 b (p 64)) (p 144)) (p 48)) (p 184)) (p 216)) (p 820)) (p 736)) (p 788)) (p 444)) (p 696)) (0) (1<<<0|||1<<<1|||1<<<2|||1<<<3|||1<<<4|||1<<<20|||1<<<21|||1<<<22|||1<<<23|||1<<<24) mz (mo (mo (mo (mo (mo (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 3 n3)) (mf 4 n4)) (mf 20 n20)) (mf 21 n21)) (mf 22 n22)) (mf 23 n23)) (mf 24 n24)) rfl
private lemma fred0313_1_all {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 k4 u0 : V)
    (hK : IsComp5 C k0 k1 k2 k3 k4) (hM : IsComp1 C u0)
    (hd : Dj5 k0 k1 k2 k3 k4 {u0}) (σ : Equiv.Perm V) (hσ : AlmOn C G k4 k0 σ) (hnp : ¬ Packs C G)
    (hsc0 : 11 ≤ kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4)) (hmin : MinSc C G k0 k1 k2 k3 k4 σ)
    (ne14 : ¬ G.Adj (σ k1) (σ k4))
    : 3 ≤ 3 * rCount G σ k0 {u0} + 1 * rCount G σ k1 {u0} + 3 * rCount G σ k2 {u0} + 2 * rCount G σ k3 {u0} + 0 * rCount G σ k4 {u0} := by
  have hev : evalDT 5 1 16668 11 false false pt5_1 wl13 3 (n 3 (n 1 b (n 2 b (p 36))) (n 2 b (p 24))) 0 0 = true := rfl
  have hsum : 3 ≤ wSumBool wl13 (eb5_1 G σ k0 k1 k2 k3 k4 k0 u0) := evalDT_sound (mkCtx5_1 C G k0 k1 k2 k3 k4 k0 u0 hK hM hd σ hσ hnp 16668 11 false false σ σ σ fd fd fd fd (fun _ => ne14) fd ff ff (fun _ => ⟨hsc0, hmin⟩) ff) pt5_1 wl13 3 rfl (n 3 (n 1 b (n 2 b (p 36))) (n 2 b (p 24))) 0 0 mz mz hev
  dsimp only [wl13] at hsum; rw [wSum_eb5_1 G σ 3 1 3 2 0 0 k0 k1 k2 k3 k4 k0 u0] at hsum; clear hev; omega
set_option maxHeartbeats 800000 in
private lemma fred0313_3 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 k4 u0 u1 u2 : V)
    (hK : IsComp5 C k0 k1 k2 k3 k4) (hM : IsComp3 C u0 u1 u2)
    (hd : Dj5 k0 k1 k2 k3 k4 {u0, u1, u2}) (σ : Equiv.Perm V) (hσ : AlmOn C G k4 k0 σ) (hnp : ¬ Packs C G)
    (hsc0 : 11 ≤ kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4)) (hmin : MinSc C G k0 k1 k2 k3 k4 σ)
    (ne14 : ¬ G.Adj (σ k1) (σ k4))
    : 9 ≤ 3 * rCount G σ k0 {u0, u1, u2} + 1 * rCount G σ k1 {u0, u1, u2} + 3 * rCount G σ k2 {u0, u1, u2} + 2 * rCount G σ k3 {u0, u1, u2} + 0 * rCount G σ k4 {u0, u1, u2} := by
  have run (a0 a1 a2 : V) (hMa : IsComp3 C a0 a1 a2) (hdM : Dj5 k0 k1 k2 k3 k4 {a0, a1, a2})
      (tr : DT) (tm fm : ℕ) (ht : ∀ i, tm.testBit i = true → (eb5_3 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2).getD i false = true)
      (hf : ∀ i, fm.testBit i = true → (eb5_3 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2).getD i false = false)
      (hev : evalDT 5 3 16668 11 false false pt5_3 wl14 9 tr tm fm = true) : 9 ≤ 3 * rCount G σ k0 {a0, a1, a2} + 1 * rCount G σ k1 {a0, a1, a2} + 3 * rCount G σ k2 {a0, a1, a2} + 2 * rCount G σ k3 {a0, a1, a2} + 0 * rCount G σ k4 {a0, a1, a2} := by
    have hsum : 9 ≤ wSumBool wl14 (eb5_3 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2) := evalDT_sound (mkCtx5_3 C G k0 k1 k2 k3 k4 k0 a0 a1 a2 hK hMa hdM σ hσ hnp 16668 11 false false σ σ σ fd fd fd fd (fun _ => ne14) fd ff ff (fun _ => ⟨hsc0, hmin⟩) ff) pt5_3 wl14 9 rfl tr tm fm ht hf hev
    dsimp only [wl14] at hsum; rw [wSum_eb5_3 G σ 3 1 3 2 0 0 k0 k1 k2 k3 k4 k0 a0 a1 a2 hMa] at hsum; clear tr tm fm ht hf hev; omega
  refine sym2_m3 C G σ k0 k2 (fun M => Dj5 k0 k1 k2 k3 k4 M → 9 ≤ 3 * rCount G σ k0 M + 1 * rCount G σ k1 M + 3 * rCount G σ k2 M + 2 * rCount G σ k3 M + 0 * rCount G σ k4 M) ?_ ?_ ?_ ?_ ?_ u0 u1 u2 hM hd
  · intro a0 a1 a2 hMa t0 t1 hdM; exact run a0 a1 a2 hMa hdM (n 2 b (n 6 b (n 5 (n 11 b (n 7 b (p 56))) (n 7 b (a 16))))) (1<<<0|||1<<<1) (0) (mo (mt 0 t0) (mt 1 t1)) mz rfl
  · intro a0 a1 a2 hMa t0 n1 n2 hdM; exact run a0 a1 a2 hMa hdM (n 9 (n 6 (n 3 b (n 12 (n 10 b (n 7 b (n 5 b (a 56)))) (p 4))) (n 3 (n 12 (n 7 b (n 11 (n 5 b (a 16)) (p 56))) (a 1)) (p 32))) (n 6 (n 12 (n 3 (n 10 b (n 5 (n 8 b (n 14 (n 11 b (n 4 b (a 50))) (a 65))) (n 8 b (a 64)))) (a 74)) (a 1)) (p 12))) (1<<<0) (1<<<1|||1<<<2) (mt 0 t0) (mo (mf 1 n1) (mf 2 n2)) rfl
  · intro a0 a1 a2 hMa n0 n1 n2 t6 t7 hdM; exact run a0 a1 a2 hMa hdM (n 8 b (n 11 (n 5 b (p 248)) (p 28))) (1<<<6|||1<<<7) (1<<<0|||1<<<1|||1<<<2) (mo (mt 6 t6) (mt 7 t7)) (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) rfl
  · intro a0 a1 a2 hMa n0 n1 n2 t6 n7 n8 hdM; exact run a0 a1 a2 hMa hdM (n 10 (n 11 (n 9 b (p 300)) (p 28)) (p 20)) (1<<<6) (1<<<0|||1<<<1|||1<<<2|||1<<<7|||1<<<8) (mt 6 t6) (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 7 n7)) (mf 8 n8)) rfl
  · intro a0 a1 a2 hMa n0 n1 n2 n6 n7 n8 hdM; exact run a0 a1 a2 hMa hdM (n 9 (n 10 (n 11 (n 3 (n 4 (n 5 b (a 16)) (a 52)) (a 46)) (p 28)) (p 20)) (p 12)) (0) (1<<<0|||1<<<1|||1<<<2|||1<<<6|||1<<<7|||1<<<8) mz (mo (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 6 n6)) (mf 7 n7)) (mf 8 n8)) rfl
set_option maxHeartbeats 800000 in
private lemma fred0313_5 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 k4 u0 u1 u2 u3 u4 : V)
    (hK : IsComp5 C k0 k1 k2 k3 k4) (hM : IsComp5 C u0 u1 u2 u3 u4)
    (hd : Dj5 k0 k1 k2 k3 k4 {u0, u1, u2, u3, u4}) (σ : Equiv.Perm V) (hσ : AlmOn C G k4 k0 σ) (hnp : ¬ Packs C G)
    (hsc0 : 11 ≤ kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4)) (hmin : MinSc C G k0 k1 k2 k3 k4 σ)
    (ne14 : ¬ G.Adj (σ k1) (σ k4))
    : 15 ≤ 3 * rCount G σ k0 {u0, u1, u2, u3, u4} + 1 * rCount G σ k1 {u0, u1, u2, u3, u4} + 3 * rCount G σ k2 {u0, u1, u2, u3, u4} + 2 * rCount G σ k3 {u0, u1, u2, u3, u4} + 0 * rCount G σ k4 {u0, u1, u2, u3, u4} := by
  have run (a0 a1 a2 a3 a4 : V) (hMa : IsComp5 C a0 a1 a2 a3 a4) (hdM : Dj5 k0 k1 k2 k3 k4 {a0, a1, a2, a3, a4})
      (tr : DT) (tm fm : ℕ) (ht : ∀ i, tm.testBit i = true → (eb5_5 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4).getD i false = true)
      (hf : ∀ i, fm.testBit i = true → (eb5_5 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4).getD i false = false)
      (hev : evalDT 5 5 16668 11 false false pt5_5 wl15 15 tr tm fm = true) : 15 ≤ 3 * rCount G σ k0 {a0, a1, a2, a3, a4} + 1 * rCount G σ k1 {a0, a1, a2, a3, a4} + 3 * rCount G σ k2 {a0, a1, a2, a3, a4} + 2 * rCount G σ k3 {a0, a1, a2, a3, a4} + 0 * rCount G σ k4 {a0, a1, a2, a3, a4} := by
    have hsum : 15 ≤ wSumBool wl15 (eb5_5 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4) := evalDT_sound (mkCtx5_5 C G k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4 hK hMa hdM σ hσ hnp 16668 11 false false σ σ σ fd fd fd fd (fun _ => ne14) fd ff ff (fun _ => ⟨hsc0, hmin⟩) ff) pt5_5 wl15 15 rfl tr tm fm ht hf hev
    dsimp only [wl15] at hsum; rw [wSum_eb5_5 G σ 3 1 3 2 0 0 k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4 hMa] at hsum; clear tr tm fm ht hf hev; omega
  refine sym2_m5 C G σ k0 k2 (fun M => Dj5 k0 k1 k2 k3 k4 M → 15 ≤ 3 * rCount G σ k0 M + 1 * rCount G σ k1 M + 3 * rCount G σ k2 M + 2 * rCount G σ k3 M + 0 * rCount G σ k4 M) ?_ ?_ ?_ ?_ ?_ u0 u1 u2 u3 u4 hM hd
  · intro a0 a1 a2 a3 a4 hMa t0 t1 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 2 (n 3 (n 4 b (n 10 b (n 13 b (n 19 (n 9 b (a 160)) (p 200))))) (n 4 (n 12 b (n 14 b (n 18 (n 8 b (a 213)) (p 408)))) (n 15 (n 17 (n 5 (n 7 b (n 10 b (n 18 b (a 153)))) (n 12 b (n 18 b (a 107)))) (n 10 (n 20 (n 12 b (n 5 b (n 18 b (a 107)))) (a 117)) (a 90))) (n 12 (n 22 (n 17 (n 10 b (n 7 b (n 19 b (a 274)))) (n 10 b (a 90))) (a 70)) (a 97))))) (n 4 (n 3 (n 11 b (n 13 b (n 17 (n 7 b (a 308)) (p 252)))) (n 16 (n 19 (n 6 (n 9 b (n 11 b (n 17 b (a 166)))) (n 14 b (n 17 b (a 259)))) (n 11 (n 21 (n 14 b (n 6 b (n 18 b (a 189)))) (a 322)) (a 148))) (n 14 (n 24 (n 19 (n 11 b (n 9 b (n 17 b (a 166)))) (n 11 b (a 148))) (a 109)) (a 131)))) (n 18 (n 13 (n 23 (n 3 (n 10 b (n 11 b (n 9 b (a 193)))) (n 17 (n 15 b (n 12 b (a 97))) (n 10 (n 20 (n 14 b (n 16 b (a 131))) (a 117)) (a 90)))) (n 8 (n 5 (n 15 b (n 11 b (p 84))) (n 14 b (p 52))) (p 0))) (n 23 (n 8 (n 5 (n 15 (n 10 b (n 19 (n 9 b (a 160)) (p 200))) (n 21 (n 22 (n 6 (n 16 (n 10 b (n 19 b (p 200))) (n 20 (n 12 (n 14 b (a 207)) (a 326)) (p 132))) (n 20 (n 12 (n 14 b (p 828)) (a 87)) (a 265))) (p 72)) (p 452))) (n 14 (n 24 (n 16 (n 3 b (n 22 (n 19 b (n 21 (n 10 b (p 200)) (p 392))) (a 240))) (n 21 (n 20 (n 12 b (p 1300)) (p 132)) (a 141))) (p 96)) (a 152))) (p 68)) (a 0))) (n 13 (n 23 (n 8 (n 10 (n 11 b (n 20 (n 3 b (n 19 b (a 148))) (p 188))) (n 21 (n 11 (n 3 b (n 17 b (a 90))) (n 20 (n 19 (n 17 (n 9 b (a 193)) (a 328)) (a 313)) (p 188))) (p 340))) (a 132)) (a 0)) (p 100))))) (1<<<0|||1<<<1) (0) (mo (mt 0 t0) (mt 1 t1)) mz rfl
  · intro a0 a1 a2 a3 a4 hMa t0 n1 n4 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 5 (n 15 (n 10 (n 20 (n 2 (n 3 b (n 12 b (n 17 (n 7 b (p 156)) (p 120)))) (n 18 (n 13 (n 8 b (n 23 (n 3 b (n 12 b (n 14 b (a 213)))) (p 0))) (n 8 (n 23 (n 12 b (n 6 (n 9 (n 3 b (n 7 b (p 156))) (a 188)) (a 87))) (a 0)) (p 68))) (n 13 (n 23 (n 8 (n 3 b (n 12 b (n 17 b (p 120)))) (a 132)) (a 0)) (p 100)))) (n 17 (n 18 (n 16 b (n 13 b (p 132))) (n 2 (n 12 b (p 164)) (a 202))) (n 3 (n 13 b (p 80)) (a 117)))) (n 20 (n 17 (n 18 (n 16 (n 19 (n 7 b (n 11 b (a 329))) (n 13 b (p 200))) (n 12 (n 23 (n 8 (n 13 b (n 19 b (p 200))) (n 2 b (a 303))) (p 128)) (p 364))) (n 2 (n 22 (n 21 (n 7 (n 12 b (n 16 (n 6 b (a 288)) (p 364))) (n 3 (n 14 b (p 1244)) (a 153))) (p 340)) (p 168)) (a 183))) (n 3 (n 23 (n 24 (n 18 (n 8 (n 13 b (n 19 (n 9 b (a 160)) (p 200))) (n 2 (n 11 b (p 1272)) (a 199))) (n 2 (n 22 (n 14 b (a 312)) (p 168)) (a 183))) (p 140)) (p 176)) (a 90))) (a 6))) (n 10 (n 20 (n 2 (n 3 (n 12 b (n 23 (n 13 b (n 22 (n 16 b (a 319)) (p 72))) (p 104))) (n 12 (n 22 (n 7 (n 6 b (n 17 b (n 11 b (a 289)))) (n 17 b (a 204))) (a 70)) (a 97))) (n 13 (n 23 (n 3 (n 8 (n 9 b (n 18 b (n 14 b (a 299)))) (n 18 b (a 132))) (n 12 (n 22 (n 16 b (n 14 b (a 131))) (a 70)) (a 97))) (a 142)) (a 201))) (a 6)) (p 204))) (n 10 (n 15 (n 20 (n 2 (n 3 (n 12 b (n 23 (n 13 b (n 6 b (a 87))) (n 18 b (a 107)))) (n 12 (n 22 (n 17 b (n 7 b (a 204))) (n 17 b (a 1))) (n 17 (n 19 b (a 178)) (p 120)))) (n 13 (n 23 (n 18 (n 3 b (n 12 b (n 17 b (p 120)))) (n 8 (n 3 b (n 12 b (a 107))) (a 132))) (n 12 (n 11 b (a 253)) (a 254))) (n 17 (n 16 (n 18 (n 22 (n 21 (n 14 b (a 152)) (a 247)) (a 181)) (p 100)) (a 141)) (a 248)))) (p 24)) (a 338)) (p 208))) (1<<<0) (1<<<1|||1<<<4) (mt 0 t0) (mo (mf 1 n1) (mf 4 n4)) rfl
  · intro a0 a1 a2 a3 a4 hMa n0 n1 n2 n3 n4 t10 t11 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 13 (n 12 (n 14 b (n 16 (n 19 b (p 324)) (a 131))) (n 15 (n 17 (n 19 b (a 285)) (p 120)) (a 97))) (n 15 (n 16 (n 18 (n 8 (n 23 (n 17 b (n 12 b (p 120))) (a 0)) (p 68)) (p 100)) (a 295)) (a 201))) (1<<<10|||1<<<11) (1<<<0|||1<<<1|||1<<<2|||1<<<3|||1<<<4) (mo (mt 10 t10) (mt 11 t11)) (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 3 n3)) (mf 4 n4)) rfl
  · intro a0 a1 a2 a3 a4 hMa n0 n1 n2 n3 n4 t10 n11 n14 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 16 (n 19 (n 17 (n 15 (n 18 (n 5 (n 9 b (p 256)) (a 339)) (a 268)) (p 552)) (a 332)) (p 324)) (p 312)) (1<<<10) (1<<<0|||1<<<1|||1<<<2|||1<<<3|||1<<<4|||1<<<11|||1<<<14) (mt 10 t10) (mo (mo (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 3 n3)) (mf 4 n4)) (mf 11 n11)) (mf 14 n14)) rfl
  · intro a0 a1 a2 a3 a4 hMa n0 n1 n2 n3 n4 n10 n11 n12 n13 n14 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 15 (n 17 (n 18 (n 16 (n 19 (n 5 (n 7 (n 8 (n 6 (n 9 b (a 188)) (a 87)) (a 264)) (a 235)) (a 152)) (p 200)) (p 364)) (p 408)) (p 252)) (p 552)) (0) (1<<<0|||1<<<1|||1<<<2|||1<<<3|||1<<<4|||1<<<10|||1<<<11|||1<<<12|||1<<<13|||1<<<14) mz (mo (mo (mo (mo (mo (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 3 n3)) (mf 4 n4)) (mf 10 n10)) (mf 11 n11)) (mf 12 n12)) (mf 13 n13)) (mf 14 n14)) rfl
private lemma fred0314_1_all {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 k4 u0 : V)
    (hK : IsComp5 C k0 k1 k2 k3 k4) (hM : IsComp1 C u0)
    (hd : Dj5 k0 k1 k2 k3 k4 {u0}) (σ : Equiv.Perm V) (hσ : AlmOn C G k4 k0 σ) (hnp : ¬ Packs C G)
    (hsc0 : 11 ≤ kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4)) (hmin : MinSc C G k0 k1 k2 k3 k4 σ)
    (ne13 : ¬ G.Adj (σ k1) (σ k3))
    : 1 ≤ 2 * rCount G σ k0 {u0} + 0 * rCount G σ k1 {u0} + 0 * rCount G σ k2 {u0} + 0 * rCount G σ k3 {u0} + 1 * rCount G σ k4 {u0} := by
  have hev : evalDT 5 1 16924 11 false false pt5_1 wl7 1 (n 0 b (a 7)) 0 0 = true := rfl
  have hsum : 1 ≤ wSumBool wl7 (eb5_1 G σ k0 k1 k2 k3 k4 k0 u0) := evalDT_sound (mkCtx5_1 C G k0 k1 k2 k3 k4 k0 u0 hK hM hd σ hσ hnp 16924 11 false false σ σ σ fd fd fd (fun _ => ne13) fd fd ff ff (fun _ => ⟨hsc0, hmin⟩) ff) pt5_1 wl7 1 rfl (n 0 b (a 7)) 0 0 mz mz hev
  dsimp only [wl7] at hsum; rw [wSum_eb5_1 G σ 2 0 0 0 1 0 k0 k1 k2 k3 k4 k0 u0] at hsum; clear hev; omega
set_option maxHeartbeats 800000 in
private lemma fred0314_3 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 k4 u0 u1 u2 : V)
    (hK : IsComp5 C k0 k1 k2 k3 k4) (hM : IsComp3 C u0 u1 u2)
    (hd : Dj5 k0 k1 k2 k3 k4 {u0, u1, u2}) (σ : Equiv.Perm V) (hσ : AlmOn C G k4 k0 σ) (hnp : ¬ Packs C G)
    (hsc0 : 11 ≤ kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4)) (hmin : MinSc C G k0 k1 k2 k3 k4 σ)
    (ne13 : ¬ G.Adj (σ k1) (σ k3))
    : 3 ≤ 2 * rCount G σ k0 {u0, u1, u2} + 0 * rCount G σ k1 {u0, u1, u2} + 0 * rCount G σ k2 {u0, u1, u2} + 0 * rCount G σ k3 {u0, u1, u2} + 1 * rCount G σ k4 {u0, u1, u2} := by
  have run (a0 a1 a2 : V) (hMa : IsComp3 C a0 a1 a2) (hdM : Dj5 k0 k1 k2 k3 k4 {a0, a1, a2})
      (tr : DT) (tm fm : ℕ) (ht : ∀ i, tm.testBit i = true → (eb5_3 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2).getD i false = true)
      (hf : ∀ i, fm.testBit i = true → (eb5_3 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2).getD i false = false)
      (hev : evalDT 5 3 16924 11 false false pt5_3 wl8 3 tr tm fm = true) : 3 ≤ 2 * rCount G σ k0 {a0, a1, a2} + 0 * rCount G σ k1 {a0, a1, a2} + 0 * rCount G σ k2 {a0, a1, a2} + 0 * rCount G σ k3 {a0, a1, a2} + 1 * rCount G σ k4 {a0, a1, a2} := by
    have hsum : 3 ≤ wSumBool wl8 (eb5_3 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2) := evalDT_sound (mkCtx5_3 C G k0 k1 k2 k3 k4 k0 a0 a1 a2 hK hMa hdM σ hσ hnp 16924 11 false false σ σ σ fd fd fd (fun _ => ne13) fd fd ff ff (fun _ => ⟨hsc0, hmin⟩) ff) pt5_3 wl8 3 rfl tr tm fm ht hf hev
    dsimp only [wl8] at hsum; rw [wSum_eb5_3 G σ 2 0 0 0 1 0 k0 k1 k2 k3 k4 k0 a0 a1 a2 hMa] at hsum; clear tr tm fm ht hf hev; omega
  refine sym2_m3 C G σ k0 k4 (fun M => Dj5 k0 k1 k2 k3 k4 M → 3 ≤ 2 * rCount G σ k0 M + 0 * rCount G σ k1 M + 0 * rCount G σ k2 M + 0 * rCount G σ k3 M + 1 * rCount G σ k4 M) ?_ ?_ ?_ ?_ ?_ u0 u1 u2 hM hd
  · intro a0 a1 a2 hMa t0 t1 hdM; exact run a0 a1 a2 hMa hdM b (1<<<0|||1<<<1) (0) (mo (mt 0 t0) (mt 1 t1)) mz rfl
  · intro a0 a1 a2 hMa t0 n1 n2 hdM; exact run a0 a1 a2 hMa hdM (n 12 b (a 1)) (1<<<0) (1<<<1|||1<<<2) (mt 0 t0) (mo (mf 1 n1) (mf 2 n2)) rfl
  · intro a0 a1 a2 hMa n0 n1 n2 t12 t13 hdM; exact run a0 a1 a2 hMa hdM (n 14 b (a 0)) (1<<<12|||1<<<13) (1<<<0|||1<<<1|||1<<<2) (mo (mt 12 t12) (mt 13 t13)) (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) rfl
  · intro a0 a1 a2 hMa n0 n1 n2 t12 n13 n14 hdM; exact run a0 a1 a2 hMa hdM (a 0) (1<<<12) (1<<<0|||1<<<1|||1<<<2|||1<<<13|||1<<<14) (mt 12 t12) (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 13 n13)) (mf 14 n14)) rfl
  · intro a0 a1 a2 hMa n0 n1 n2 n12 n13 n14 hdM; exact run a0 a1 a2 hMa hdM (a 0) (0) (1<<<0|||1<<<1|||1<<<2|||1<<<12|||1<<<13|||1<<<14) mz (mo (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 12 n12)) (mf 13 n13)) (mf 14 n14)) rfl
set_option maxHeartbeats 800000 in
private lemma fred0314_5 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 k4 u0 u1 u2 u3 u4 : V)
    (hK : IsComp5 C k0 k1 k2 k3 k4) (hM : IsComp5 C u0 u1 u2 u3 u4)
    (hd : Dj5 k0 k1 k2 k3 k4 {u0, u1, u2, u3, u4}) (σ : Equiv.Perm V) (hσ : AlmOn C G k4 k0 σ) (hnp : ¬ Packs C G)
    (hsc0 : 11 ≤ kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4)) (hmin : MinSc C G k0 k1 k2 k3 k4 σ)
    (ne13 : ¬ G.Adj (σ k1) (σ k3))
    : 5 ≤ 2 * rCount G σ k0 {u0, u1, u2, u3, u4} + 0 * rCount G σ k1 {u0, u1, u2, u3, u4} + 0 * rCount G σ k2 {u0, u1, u2, u3, u4} + 0 * rCount G σ k3 {u0, u1, u2, u3, u4} + 1 * rCount G σ k4 {u0, u1, u2, u3, u4} := by
  have run (a0 a1 a2 a3 a4 : V) (hMa : IsComp5 C a0 a1 a2 a3 a4) (hdM : Dj5 k0 k1 k2 k3 k4 {a0, a1, a2, a3, a4})
      (tr : DT) (tm fm : ℕ) (ht : ∀ i, tm.testBit i = true → (eb5_5 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4).getD i false = true)
      (hf : ∀ i, fm.testBit i = true → (eb5_5 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4).getD i false = false)
      (hev : evalDT 5 5 16924 11 false false pt5_5 wl9 5 tr tm fm = true) : 5 ≤ 2 * rCount G σ k0 {a0, a1, a2, a3, a4} + 0 * rCount G σ k1 {a0, a1, a2, a3, a4} + 0 * rCount G σ k2 {a0, a1, a2, a3, a4} + 0 * rCount G σ k3 {a0, a1, a2, a3, a4} + 1 * rCount G σ k4 {a0, a1, a2, a3, a4} := by
    have hsum : 5 ≤ wSumBool wl9 (eb5_5 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4) := evalDT_sound (mkCtx5_5 C G k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4 hK hMa hdM σ hσ hnp 16924 11 false false σ σ σ fd fd fd (fun _ => ne13) fd fd ff ff (fun _ => ⟨hsc0, hmin⟩) ff) pt5_5 wl9 5 rfl tr tm fm ht hf hev
    dsimp only [wl9] at hsum; rw [wSum_eb5_5 G σ 2 0 0 0 1 0 k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4 hMa] at hsum; clear tr tm fm ht hf hev; omega
  refine sym2_m5 C G σ k0 k4 (fun M => Dj5 k0 k1 k2 k3 k4 M → 5 ≤ 2 * rCount G σ k0 M + 0 * rCount G σ k1 M + 0 * rCount G σ k2 M + 0 * rCount G σ k3 M + 1 * rCount G σ k4 M) ?_ ?_ ?_ ?_ ?_ u0 u1 u2 u3 u4 hM hd
  · intro a0 a1 a2 a3 a4 hMa t0 t1 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 3 b (n 24 b (n 22 b (a 324)))) (1<<<0|||1<<<1) (0) (mo (mt 0 t0) (mt 1 t1)) mz rfl
  · intro a0 a1 a2 a3 a4 hMa t0 n1 n4 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 20 (n 2 b (n 23 (n 3 b (n 22 b (a 1))) (a 0))) (a 6)) (1<<<0) (1<<<1|||1<<<4) (mt 0 t0) (mo (mf 1 n1) (mf 4 n4)) rfl
  · intro a0 a1 a2 a3 a4 hMa n0 n1 n2 n3 n4 t20 t21 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 23 (n 24 (n 22 b (a 1)) (a 3)) (a 0)) (1<<<20|||1<<<21) (1<<<0|||1<<<1|||1<<<2|||1<<<3|||1<<<4) (mo (mt 20 t20) (mt 21 t21)) (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 3 n3)) (mf 4 n4)) rfl
  · intro a0 a1 a2 a3 a4 hMa n0 n1 n2 n3 n4 t20 n21 n24 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (a 3) (1<<<20) (1<<<0|||1<<<1|||1<<<2|||1<<<3|||1<<<4|||1<<<21|||1<<<24) (mt 20 t20) (mo (mo (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 3 n3)) (mf 4 n4)) (mf 21 n21)) (mf 24 n24)) rfl
  · intro a0 a1 a2 a3 a4 hMa n0 n1 n2 n3 n4 n20 n21 n22 n23 n24 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (a 3) (0) (1<<<0|||1<<<1|||1<<<2|||1<<<3|||1<<<4|||1<<<20|||1<<<21|||1<<<22|||1<<<23|||1<<<24) mz (mo (mo (mo (mo (mo (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 3 n3)) (mf 4 n4)) (mf 20 n20)) (mf 21 n21)) (mf 22 n22)) (mf 23 n23)) (mf 24 n24)) rfl
private lemma fredall_1_all {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 k4 u0 : V)
    (hK : IsComp5 C k0 k1 k2 k3 k4) (hM : IsComp1 C u0)
    (hd : Dj5 k0 k1 k2 k3 k4 {u0}) (σ : Equiv.Perm V) (hσ : AlmOn C G k4 k0 σ) (hnp : ¬ Packs C G)
    (hsc0 : 13 ≤ kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4)) (hmin : MinSc C G k0 k1 k2 k3 k4 σ)
    : 2 ≤ 2 * rCount G σ k0 {u0} + 1 * rCount G σ k1 {u0} + 0 * rCount G σ k2 {u0} + 1 * rCount G σ k3 {u0} + 2 * rCount G σ k4 {u0} := by
  have hev : evalDT 5 1 17180 13 false false pt5_1 wl4 2 (n 1 (n 3 b (n 0 b (p 32))) (n 0 b (a 5))) 0 0 = true := rfl
  have hsum : 2 ≤ wSumBool wl4 (eb5_1 G σ k0 k1 k2 k3 k4 k0 u0) := evalDT_sound (mkCtx5_1 C G k0 k1 k2 k3 k4 k0 u0 hK hM hd σ hσ hnp 17180 13 false false σ σ σ fd fd fd fd fd fd ff ff (fun _ => ⟨hsc0, hmin⟩) ff) pt5_1 wl4 2 rfl (n 1 (n 3 b (n 0 b (p 32))) (n 0 b (a 5))) 0 0 mz mz hev
  dsimp only [wl4] at hsum; rw [wSum_eb5_1 G σ 2 1 0 1 2 0 k0 k1 k2 k3 k4 k0 u0] at hsum; clear hev; omega
set_option maxHeartbeats 800000 in
private lemma fredall_3 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 k4 u0 u1 u2 : V)
    (hK : IsComp5 C k0 k1 k2 k3 k4) (hM : IsComp3 C u0 u1 u2)
    (hd : Dj5 k0 k1 k2 k3 k4 {u0, u1, u2}) (σ : Equiv.Perm V) (hσ : AlmOn C G k4 k0 σ) (hnp : ¬ Packs C G)
    (hsc0 : 13 ≤ kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4)) (hmin : MinSc C G k0 k1 k2 k3 k4 σ)
    : 6 ≤ 2 * rCount G σ k0 {u0, u1, u2} + 1 * rCount G σ k1 {u0, u1, u2} + 0 * rCount G σ k2 {u0, u1, u2} + 1 * rCount G σ k3 {u0, u1, u2} + 2 * rCount G σ k4 {u0, u1, u2} := by
  have run (a0 a1 a2 : V) (hMa : IsComp3 C a0 a1 a2) (hdM : Dj5 k0 k1 k2 k3 k4 {a0, a1, a2})
      (tr : DT) (tm fm : ℕ) (ht : ∀ i, tm.testBit i = true → (eb5_3 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2).getD i false = true)
      (hf : ∀ i, fm.testBit i = true → (eb5_3 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2).getD i false = false)
      (hev : evalDT 5 3 17180 13 false false pt5_3 wl5 6 tr tm fm = true) : 6 ≤ 2 * rCount G σ k0 {a0, a1, a2} + 1 * rCount G σ k1 {a0, a1, a2} + 0 * rCount G σ k2 {a0, a1, a2} + 1 * rCount G σ k3 {a0, a1, a2} + 2 * rCount G σ k4 {a0, a1, a2} := by
    have hsum : 6 ≤ wSumBool wl5 (eb5_3 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2) := evalDT_sound (mkCtx5_3 C G k0 k1 k2 k3 k4 k0 a0 a1 a2 hK hMa hdM σ hσ hnp 17180 13 false false σ σ σ fd fd fd fd fd fd ff ff (fun _ => ⟨hsc0, hmin⟩) ff) pt5_3 wl5 6 rfl tr tm fm ht hf hev
    dsimp only [wl5] at hsum; rw [wSum_eb5_3 G σ 2 1 0 1 2 0 k0 k1 k2 k3 k4 k0 a0 a1 a2 hMa] at hsum; clear tr tm fm ht hf hev; omega
  refine sym2_m3 C G σ k0 k4 (fun M => Dj5 k0 k1 k2 k3 k4 M → 6 ≤ 2 * rCount G σ k0 M + 1 * rCount G σ k1 M + 0 * rCount G σ k2 M + 1 * rCount G σ k3 M + 2 * rCount G σ k4 M) ?_ ?_ ?_ ?_ ?_ u0 u1 u2 hM hd
  · intro a0 a1 a2 hMa t0 t1 hdM; exact run a0 a1 a2 hMa hdM (n 2 b (n 5 (n 12 b (n 9 b (n 4 b (a 49)))) (n 12 b (n 13 b (a 4))))) (1<<<0|||1<<<1) (0) (mo (mt 0 t0) (mt 1 t1)) mz rfl
  · intro a0 a1 a2 hMa t0 n1 n2 hdM; exact run a0 a1 a2 hMa hdM (n 12 (n 6 (n 9 (n 13 b (n 10 b (n 3 b (a 60)))) (n 3 (n 4 b (n 14 b (a 51))) (a 73))) (n 9 (n 3 b (a 72)) (a 3))) (n 9 (n 3 (n 6 (n 13 b (n 5 (n 11 b (p 264)) (a 4))) (a 1)) (p 4)) (a 1))) (1<<<0) (1<<<1|||1<<<2) (mt 0 t0) (mo (mf 1 n1) (mf 2 n2)) rfl
  · intro a0 a1 a2 hMa n0 n1 n2 t12 t13 hdM; exact run a0 a1 a2 hMa hdM (n 14 b (n 11 (n 5 b (p 0)) (a 0))) (1<<<12|||1<<<13) (1<<<0|||1<<<1|||1<<<2) (mo (mt 12 t12) (mt 13 t13)) (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) rfl
  · intro a0 a1 a2 hMa n0 n1 n2 t12 n13 n14 hdM; exact run a0 a1 a2 hMa hdM (n 3 (n 9 (n 10 (n 11 b (a 0)) (a 2)) (p 132)) (a 11)) (1<<<12) (1<<<0|||1<<<1|||1<<<2|||1<<<13|||1<<<14) (mt 12 t12) (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 13 n13)) (mf 14 n14)) rfl
  · intro a0 a1 a2 hMa n0 n1 n2 n12 n13 n14 hdM; exact run a0 a1 a2 hMa hdM (n 3 (n 9 (n 4 (n 5 (n 10 (n 11 b (a 0)) (a 2)) (a 4)) (a 53)) (a 1)) (a 11)) (0) (1<<<0|||1<<<1|||1<<<2|||1<<<12|||1<<<13|||1<<<14) mz (mo (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 12 n12)) (mf 13 n13)) (mf 14 n14)) rfl
set_option maxHeartbeats 800000 in
private lemma fredall_5 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 k4 u0 u1 u2 u3 u4 : V)
    (hK : IsComp5 C k0 k1 k2 k3 k4) (hM : IsComp5 C u0 u1 u2 u3 u4)
    (hd : Dj5 k0 k1 k2 k3 k4 {u0, u1, u2, u3, u4}) (σ : Equiv.Perm V) (hσ : AlmOn C G k4 k0 σ) (hnp : ¬ Packs C G)
    (hsc0 : 13 ≤ kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4)) (hmin : MinSc C G k0 k1 k2 k3 k4 σ)
    : 10 ≤ 2 * rCount G σ k0 {u0, u1, u2, u3, u4} + 1 * rCount G σ k1 {u0, u1, u2, u3, u4} + 0 * rCount G σ k2 {u0, u1, u2, u3, u4} + 1 * rCount G σ k3 {u0, u1, u2, u3, u4} + 2 * rCount G σ k4 {u0, u1, u2, u3, u4} := by
  have run (a0 a1 a2 a3 a4 : V) (hMa : IsComp5 C a0 a1 a2 a3 a4) (hdM : Dj5 k0 k1 k2 k3 k4 {a0, a1, a2, a3, a4})
      (tr : DT) (tm fm : ℕ) (ht : ∀ i, tm.testBit i = true → (eb5_5 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4).getD i false = true)
      (hf : ∀ i, fm.testBit i = true → (eb5_5 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4).getD i false = false)
      (hev : evalDT 5 5 17180 13 false false pt5_5 wl6 10 tr tm fm = true) : 10 ≤ 2 * rCount G σ k0 {a0, a1, a2, a3, a4} + 1 * rCount G σ k1 {a0, a1, a2, a3, a4} + 0 * rCount G σ k2 {a0, a1, a2, a3, a4} + 1 * rCount G σ k3 {a0, a1, a2, a3, a4} + 2 * rCount G σ k4 {a0, a1, a2, a3, a4} := by
    have hsum : 10 ≤ wSumBool wl6 (eb5_5 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4) := evalDT_sound (mkCtx5_5 C G k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4 hK hMa hdM σ hσ hnp 17180 13 false false σ σ σ fd fd fd fd fd fd ff ff (fun _ => ⟨hsc0, hmin⟩) ff) pt5_5 wl6 10 rfl tr tm fm ht hf hev
    dsimp only [wl6] at hsum; rw [wSum_eb5_5 G σ 2 1 0 1 2 0 k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4 hMa] at hsum; clear tr tm fm ht hf hev; omega
  refine sym2_m5 C G σ k0 k4 (fun M => Dj5 k0 k1 k2 k3 k4 M → 10 ≤ 2 * rCount G σ k0 M + 1 * rCount G σ k1 M + 0 * rCount G σ k2 M + 1 * rCount G σ k3 M + 2 * rCount G σ k4 M) ?_ ?_ ?_ ?_ ?_ u0 u1 u2 u3 u4 hM hd
  · intro a0 a1 a2 a3 a4 hMa t0 t1 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 2 (n 3 (n 4 b (n 6 (n 7 b (n 20 b (n 21 b (a 45)))) (n 23 b (n 22 b (a 5))))) (n 6 (n 5 (n 22 b (n 15 (n 24 b (n 8 b (a 323))) (n 4 b (a 70)))) (n 22 (n 12 (n 21 b (n 17 b (a 19))) (n 21 b (p 76))) (n 12 (n 11 (n 17 (n 16 (n 21 b (a 19)) (a 15)) (a 15)) (p 60)) (a 15)))) (n 24 (n 20 b (n 19 (n 14 (n 15 b (a 60)) (p 240)) (a 60))) (n 20 (n 10 (n 15 (n 19 b (a 80)) (a 80)) (p 320)) (a 60))))) (n 23 (n 9 (n 24 (n 18 b (n 20 b (n 6 b (a 306)))) (n 5 (n 16 (n 3 b (n 6 b (n 20 b (a 60)))) (n 3 b (a 109))) (n 18 (n 13 (n 19 (n 14 (n 16 b (n 3 b (a 109))) (a 24)) (a 24)) (p 96)) (a 24)))) (n 20 (n 21 b (n 10 (n 15 (n 16 b (a 43)) (a 43)) (p 172))) (n 21 (n 11 (n 16 (n 15 b (a 22)) (a 22)) (p 88)) (a 22)))) (n 4 (n 5 (n 21 (n 15 b (n 11 (n 6 b (a 255)) (p 84))) (n 7 (n 17 (n 12 (n 9 b (n 11 (n 16 b (a 43)) (a 43))) (a 310)) (p 48)) (a 309))) (n 24 (n 14 (n 19 (n 18 b (a 13)) (a 13)) (p 52)) (a 13))) (n 18 (n 13 (n 8 (n 5 (n 6 (n 15 (n 16 b (n 9 b (a 190))) (n 7 (n 11 (n 12 (n 9 b (n 20 b (a 22))) (a 258)) (p 84)) (a 257))) (n 22 (n 17 b (a 14)) (a 5))) (n 24 (n 19 (n 16 b (a 151)) (a 13)) (a 13))) (p 0)) (a 0)) (a 0))))) (1<<<0|||1<<<1) (0) (mo (mt 0 t0) (mt 1 t1)) mz rfl
  · intro a0 a1 a2 a3 a4 hMa t0 n1 n4 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 20 (n 10 (n 5 (n 22 (n 23 (n 12 (n 8 b (n 24 b (n 15 b (a 27)))) (n 6 b (n 13 (n 17 b (a 87)) (a 87)))) (n 15 (n 9 (n 2 b (n 8 b (p 0))) (n 17 (n 16 b (a 190)) (a 23))) (n 2 (n 12 (n 7 b (a 256)) (p 104)) (a 142)))) (n 15 (n 6 (n 9 (n 3 b (n 7 (n 12 (n 17 b (a 1)) (a 1)) (p 4))) (n 23 (n 18 b (a 9)) (a 9))) (n 23 (n 18 (n 19 b (a 334)) (a 5)) (a 5))) (n 3 (n 13 (n 8 (n 9 (n 14 (n 23 b (n 6 b (a 5))) (a 242)) (a 241)) (a 179)) (p 72)) (a 70)))) (n 15 (n 22 (n 23 (n 24 b (n 17 b (a 287))) (n 16 (n 2 b (n 18 (n 19 b (a 13)) (a 13))) (a 151))) (n 19 (n 3 (n 13 (n 23 b (n 16 (n 6 b (a 5)) (a 151))) (n 2 b (a 181))) (n 16 (n 17 (n 12 (n 21 b (a 19)) (a 15)) (a 15)) (a 15))) (a 333))) (a 337))) (n 5 (n 15 (n 22 (n 23 b (n 16 (n 17 b (n 3 b (a 239))) (p 128))) (n 19 (n 18 (n 17 (n 8 b (n 16 b (a 304))) (n 3 b (a 1))) (n 2 (n 6 b (a 5)) (a 250))) (p 160))) (a 51)) (a 336))) (n 10 (n 5 (n 15 (n 22 (n 17 (n 18 (n 23 b (n 19 (n 9 b (a 300)) (p 64))) (n 2 (n 12 (n 7 b (a 307)) (p 164)) (a 202))) (n 3 (n 9 (n 8 b (a 192)) (a 277)) (a 117))) (n 6 (n 11 (n 16 (n 9 (n 17 (n 8 (n 7 b (n 21 b (a 45))) (n 19 (n 24 b (a 28)) (a 28))) (n 3 (n 8 b (a 192)) (a 1))) (n 23 (n 17 (n 18 b (a 9)) (a 9)) (a 9))) (p 184)) (a 291)) (a 290))) (a 6)) (p 24)) (a 6))) (1<<<0) (1<<<1|||1<<<4) (mt 0 t0) (mo (mf 1 n1) (mf 4 n4)) rfl
  · intro a0 a1 a2 a3 a4 hMa n0 n1 n2 n3 n4 t20 t21 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 23 (n 22 (n 24 b (n 16 (n 17 b (a 195)) (a 109))) (n 15 (n 17 (n 19 (n 7 b (p 4)) (a 217)) (a 1)) (a 70))) (n 15 (n 16 (n 18 (n 8 (n 13 (n 17 (n 19 b (n 22 b (a 217))) (n 22 b (a 1))) (a 0)) (p 0)) (a 0)) (a 271)) (a 142))) (1<<<20|||1<<<21) (1<<<0|||1<<<1|||1<<<2|||1<<<3|||1<<<4) (mo (mt 20 t20) (mt 21 t21)) (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 3 n3)) (mf 4 n4)) rfl
  · intro a0 a1 a2 a3 a4 hMa n0 n1 n2 n3 n4 t20 n21 n24 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 10 (n 15 (n 16 (n 19 (n 17 (n 18 (n 5 (n 9 (n 6 b (p 116)) (p 12)) (a 340)) (a 297)) (a 195)) (a 3)) (a 29)) (p 216)) (a 341)) (1<<<20) (1<<<0|||1<<<1|||1<<<2|||1<<<3|||1<<<4|||1<<<21|||1<<<24) (mt 20 t20) (mo (mo (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 3 n3)) (mf 4 n4)) (mf 21 n21)) (mf 24 n24)) rfl
  · intro a0 a1 a2 a3 a4 hMa n0 n1 n2 n3 n4 n20 n21 n22 n23 n24 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 5 (n 7 (n 8 (n 6 (n 9 (n 15 (n 16 (n 17 (n 18 (n 19 b (p 64)) (p 144)) (p 48)) (p 184)) (p 216)) (a 9)) (a 5)) (a 28)) (a 236)) (a 13)) (0) (1<<<0|||1<<<1|||1<<<2|||1<<<3|||1<<<4|||1<<<20|||1<<<21|||1<<<22|||1<<<23|||1<<<24) mz (mo (mo (mo (mo (mo (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 3 n3)) (mf 4 n4)) (mf 20 n20)) (mf 21 n21)) (mf 22 n22)) (mf 23 n23)) (mf 24 n24)) rfl
set_option maxHeartbeats 800000 in
private lemma fminA_5 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 k4 u0 u1 u2 u3 u4 : V)
    (hK : IsComp5 C k0 k1 k2 k3 k4) (hM : IsComp5 C u0 u1 u2 u3 u4)
    (hd : Dj5 k0 k1 k2 k3 k4 {u0, u1, u2, u3, u4}) (σ : Equiv.Perm V) (hσ : AlmOn C G k4 k0 σ) (hnp : ¬ Packs C G)
    (hsc0 : 7 ≤ kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4)) (hmin : MinSc C G k0 k1 k2 k3 k4 σ)
    (ne03 : ¬ G.Adj (σ k0) (σ k3))
    (ne13 : ¬ G.Adj (σ k1) (σ k3))
    (ne14 : ¬ G.Adj (σ k1) (σ k4))
    : 2 ≤ rCount G σ k0 {u0, u1, u2, u3, u4} + rCount G σ k2 {u0, u1, u2, u3, u4} + rCount G σ k4 {u0, u1, u2, u3, u4} := by
  have run (a0 a1 a2 a3 a4 : V) (hMa : IsComp5 C a0 a1 a2 a3 a4) (hdM : Dj5 k0 k1 k2 k3 k4 {a0, a1, a2, a3, a4})
      (tr : DT) (tm fm : ℕ) (ht : ∀ i, tm.testBit i = true → (eb5_5 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4).getD i false = true)
      (hf : ∀ i, fm.testBit i = true → (eb5_5 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4).getD i false = false)
      (hev : evalDT 5 5 16404 7 false false pt5_5 wl16 2 tr tm fm = true) : 2 ≤ rCount G σ k0 {a0, a1, a2, a3, a4} + rCount G σ k2 {a0, a1, a2, a3, a4} + rCount G σ k4 {a0, a1, a2, a3, a4} := by
    have hsum : 2 ≤ wSumBool wl16 (eb5_5 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4) := evalDT_sound (mkCtx5_5 C G k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4 hK hMa hdM σ hσ hnp 16404 7 false false σ σ σ fd (fun _ => ne03) fd (fun _ => ne13) (fun _ => ne14) fd ff ff (fun _ => ⟨hsc0, hmin⟩) ff) pt5_5 wl16 2 rfl tr tm fm ht hf hev
    dsimp only [wl16] at hsum; rw [wSum_eb5_5 G σ 1 0 1 0 1 0 k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4 hMa] at hsum; clear tr tm fm ht hf hev; omega
  refine sym2_m5 C G σ k0 k4 (fun M => Dj5 k0 k1 k2 k3 k4 M → 2 ≤ rCount G σ k0 M + rCount G σ k2 M + rCount G σ k4 M) ?_ ?_ ?_ ?_ ?_ u0 u1 u2 u3 u4 hM hd
  · intro a0 a1 a2 a3 a4 hMa t0 t1 hdM; exact run a0 a1 a2 a3 a4 hMa hdM b (1<<<0|||1<<<1) (0) (mo (mt 0 t0) (mt 1 t1)) mz rfl
  · intro a0 a1 a2 a3 a4 hMa t0 n1 n4 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 10 b (n 20 b (a 6))) (1<<<0) (1<<<1|||1<<<4) (mt 0 t0) (mo (mf 1 n1) (mf 4 n4)) rfl
  · intro a0 a1 a2 a3 a4 hMa n0 n1 n2 n3 n4 t20 t21 hdM; exact run a0 a1 a2 a3 a4 hMa hdM b (1<<<20|||1<<<21) (1<<<0|||1<<<1|||1<<<2|||1<<<3|||1<<<4) (mo (mt 20 t20) (mt 21 t21)) (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 3 n3)) (mf 4 n4)) rfl
  · intro a0 a1 a2 a3 a4 hMa n0 n1 n2 n3 n4 t20 n21 n24 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 10 b (p 212)) (1<<<20) (1<<<0|||1<<<1|||1<<<2|||1<<<3|||1<<<4|||1<<<21|||1<<<24) (mt 20 t20) (mo (mo (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 3 n3)) (mf 4 n4)) (mf 21 n21)) (mf 24 n24)) rfl
  · intro a0 a1 a2 a3 a4 hMa n0 n1 n2 n3 n4 n20 n21 n22 n23 n24 hdM; exact run a0 a1 a2 a3 a4 hMa hdM (n 10 (n 12 b (p 28)) (p 212)) (0) (1<<<0|||1<<<1|||1<<<2|||1<<<3|||1<<<4|||1<<<20|||1<<<21|||1<<<22|||1<<<23|||1<<<24) mz (mo (mo (mo (mo (mo (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 3 n3)) (mf 4 n4)) (mf 20 n20)) (mf 21 n21)) (mf 22 n22)) (mf 23 n23)) (mf 24 n24)) rfl
private lemma fminZ_1_all {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 k4 u0 : V)
    (hK : IsComp5 C k0 k1 k2 k3 k4) (hM : IsComp1 C u0)
    (hd : Dj5 k0 k1 k2 k3 k4 {u0}) (σ : Equiv.Perm V) (hσ : AlmOn C G k4 k0 σ) (hnp : ¬ Packs C G)
    (hsc0 : 7 ≤ kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4)) (hmin : MinSc C G k0 k1 k2 k3 k4 σ)
    (hz0 : ZProp C G k0 k1 k2 k3 k4 σ {u0})
    (ne03 : ¬ G.Adj (σ k0) (σ k3))
    (ne13 : ¬ G.Adj (σ k1) (σ k3))
    (ne14 : ¬ G.Adj (σ k1) (σ k4))
    : 11 ≤ 9 * rCount G σ k0 {u0} + 3 * rCount G σ k1 {u0} + 9 * rCount G σ k2 {u0} + 3 * rCount G σ k3 {u0} + 9 * rCount G σ k4 {u0} := by
  have hev : evalDT 5 1 16404 7 false true pt5_1 wl17 11 (n 1 (n 3 (n 0 b (n 2 b (p 0))) (z 0 3)) (z 0 1)) 0 0 = true := rfl
  have hsum : 11 ≤ wSumBool wl17 (eb5_1 G σ k0 k1 k2 k3 k4 k0 u0) := evalDT_sound (mkCtx5_1 C G k0 k1 k2 k3 k4 k0 u0 hK hM hd σ hσ hnp 16404 7 false true σ σ σ fd (fun _ => ne03) fd (fun _ => ne13) (fun _ => ne14) fd ff ff (fun _ => ⟨hsc0, hmin⟩) (fun _ => hz0)) pt5_1 wl17 11 rfl (n 1 (n 3 (n 0 b (n 2 b (p 0))) (z 0 3)) (z 0 1)) 0 0 mz mz hev
  dsimp only [wl17] at hsum; rw [wSum_eb5_1 G σ 9 3 9 3 9 0 k0 k1 k2 k3 k4 k0 u0] at hsum; clear hev; omega
set_option maxHeartbeats 800000 in
private lemma fminZ_3 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 k4 u0 u1 u2 : V)
    (hK : IsComp5 C k0 k1 k2 k3 k4) (hM : IsComp3 C u0 u1 u2)
    (hd : Dj5 k0 k1 k2 k3 k4 {u0, u1, u2}) (σ : Equiv.Perm V) (hσ : AlmOn C G k4 k0 σ) (hnp : ¬ Packs C G)
    (hsc0 : 7 ≤ kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4)) (hmin : MinSc C G k0 k1 k2 k3 k4 σ)
    (hz0 : ZProp C G k0 k1 k2 k3 k4 σ {u0, u1, u2})
    (ne03 : ¬ G.Adj (σ k0) (σ k3))
    (ne13 : ¬ G.Adj (σ k1) (σ k3))
    (ne14 : ¬ G.Adj (σ k1) (σ k4))
    : 33 ≤ 9 * rCount G σ k0 {u0, u1, u2} + 3 * rCount G σ k1 {u0, u1, u2} + 9 * rCount G σ k2 {u0, u1, u2} + 3 * rCount G σ k3 {u0, u1, u2} + 9 * rCount G σ k4 {u0, u1, u2} := by
  have run (a0 a1 a2 : V) (hMa : IsComp3 C a0 a1 a2) (hdM : Dj5 k0 k1 k2 k3 k4 {a0, a1, a2}) (hzM : ZProp C G k0 k1 k2 k3 k4 σ {a0, a1, a2})
      (tr : DT) (tm fm : ℕ) (ht : ∀ i, tm.testBit i = true → (eb5_3 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2).getD i false = true)
      (hf : ∀ i, fm.testBit i = true → (eb5_3 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2).getD i false = false)
      (hev : evalDT 5 3 16404 7 false true pt5_3 wl18 33 tr tm fm = true) : 33 ≤ 9 * rCount G σ k0 {a0, a1, a2} + 3 * rCount G σ k1 {a0, a1, a2} + 9 * rCount G σ k2 {a0, a1, a2} + 3 * rCount G σ k3 {a0, a1, a2} + 9 * rCount G σ k4 {a0, a1, a2} := by
    have hsum : 33 ≤ wSumBool wl18 (eb5_3 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2) := evalDT_sound (mkCtx5_3 C G k0 k1 k2 k3 k4 k0 a0 a1 a2 hK hMa hdM σ hσ hnp 16404 7 false true σ σ σ fd (fun _ => ne03) fd (fun _ => ne13) (fun _ => ne14) fd ff ff (fun _ => ⟨hsc0, hmin⟩) (fun _ => hzM)) pt5_3 wl18 33 rfl tr tm fm ht hf hev
    dsimp only [wl18] at hsum; rw [wSum_eb5_3 G σ 9 3 9 3 9 0 k0 k1 k2 k3 k4 k0 a0 a1 a2 hMa] at hsum; clear tr tm fm ht hf hev; omega
  refine sym2_m3 C G σ k0 k2 (fun M => Dj5 k0 k1 k2 k3 k4 M → (ZProp C G k0 k1 k2 k3 k4 σ M) → 33 ≤ 9 * rCount G σ k0 M + 3 * rCount G σ k1 M + 9 * rCount G σ k2 M + 3 * rCount G σ k3 M + 9 * rCount G σ k4 M) ?_ ?_ ?_ ?_ ?_ u0 u1 u2 hM hd hz0
  · intro a0 a1 a2 hMa t0 t1 hdM hzM; exact run a0 a1 a2 hMa hdM hzM (n 6 (n 12 b (n 7 b (n 2 b (n 5 (n 11 b (p 124)) (p 16))))) (n 13 (n 7 b (n 14 b (n 12 b (p 144)))) (n 2 (n 8 b (n 7 b (a 35))) (n 5 (n 11 (n 9 (n 10 (n 3 b (p 112)) (p 52)) (p 116)) (p 68)) (p 60))))) (1<<<0|||1<<<1) (0) (mo (mt 0 t0) (mt 1 t1)) mz rfl
  · intro a0 a1 a2 hMa t0 n1 n2 hdM hzM; exact run a0 a1 a2 hMa hdM hzM (n 6 (n 12 (n 7 b (n 8 b (n 13 b (n 14 b (n 9 (n 3 b (z 0 1)) (z 0 3)))))) (n 13 (n 14 b (p 88)) (p 96))) (n 12 (n 8 (n 7 b (p 172)) (p 104)) (a 1))) (1<<<0) (1<<<1|||1<<<2) (mt 0 t0) (mo (mf 1 n1) (mf 2 n2)) rfl
  · intro a0 a1 a2 hMa n0 n1 n2 t6 t7 hdM hzM; exact run a0 a1 a2 hMa hdM hzM (n 12 (n 13 b (a 21)) (a 39)) (1<<<6|||1<<<7) (1<<<0|||1<<<1|||1<<<2) (mo (mt 6 t6) (mt 7 t7)) (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) rfl
  · intro a0 a1 a2 hMa n0 n1 n2 t6 n7 n8 hdM hzM; exact run a0 a1 a2 hMa hdM hzM (p 108) (1<<<6) (1<<<0|||1<<<1|||1<<<2|||1<<<7|||1<<<8) (mt 6 t6) (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 7 n7)) (mf 8 n8)) rfl
  · intro a0 a1 a2 hMa n0 n1 n2 n6 n7 n8 hdM hzM; exact run a0 a1 a2 hMa hdM hzM (p 176) (0) (1<<<0|||1<<<1|||1<<<2|||1<<<6|||1<<<7|||1<<<8) mz (mo (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 6 n6)) (mf 7 n7)) (mf 8 n8)) rfl
set_option maxHeartbeats 800000 in
private lemma fminZ_5 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 k4 u0 u1 u2 u3 u4 : V)
    (hK : IsComp5 C k0 k1 k2 k3 k4) (hM : IsComp5 C u0 u1 u2 u3 u4)
    (hd : Dj5 k0 k1 k2 k3 k4 {u0, u1, u2, u3, u4}) (σ : Equiv.Perm V) (hσ : AlmOn C G k4 k0 σ) (hnp : ¬ Packs C G)
    (hsc0 : 7 ≤ kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4)) (hmin : MinSc C G k0 k1 k2 k3 k4 σ)
    (hz0 : ZProp C G k0 k1 k2 k3 k4 σ {u0, u1, u2, u3, u4})
    (ne03 : ¬ G.Adj (σ k0) (σ k3))
    (ne13 : ¬ G.Adj (σ k1) (σ k3))
    (ne14 : ¬ G.Adj (σ k1) (σ k4))
    : 55 ≤ 9 * rCount G σ k0 {u0, u1, u2, u3, u4} + 3 * rCount G σ k1 {u0, u1, u2, u3, u4} + 9 * rCount G σ k2 {u0, u1, u2, u3, u4} + 3 * rCount G σ k3 {u0, u1, u2, u3, u4} + 9 * rCount G σ k4 {u0, u1, u2, u3, u4} := by
  have run (a0 a1 a2 a3 a4 : V) (hMa : IsComp5 C a0 a1 a2 a3 a4) (hdM : Dj5 k0 k1 k2 k3 k4 {a0, a1, a2, a3, a4}) (hzM : ZProp C G k0 k1 k2 k3 k4 σ {a0, a1, a2, a3, a4})
      (tr : DT) (tm fm : ℕ) (ht : ∀ i, tm.testBit i = true → (eb5_5 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4).getD i false = true)
      (hf : ∀ i, fm.testBit i = true → (eb5_5 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4).getD i false = false)
      (hev : evalDT 5 5 16404 7 false true pt5_5 wl19 55 tr tm fm = true) : 55 ≤ 9 * rCount G σ k0 {a0, a1, a2, a3, a4} + 3 * rCount G σ k1 {a0, a1, a2, a3, a4} + 9 * rCount G σ k2 {a0, a1, a2, a3, a4} + 3 * rCount G σ k3 {a0, a1, a2, a3, a4} + 9 * rCount G σ k4 {a0, a1, a2, a3, a4} := by
    have hsum : 55 ≤ wSumBool wl19 (eb5_5 G σ k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4) := evalDT_sound (mkCtx5_5 C G k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4 hK hMa hdM σ hσ hnp 16404 7 false true σ σ σ fd (fun _ => ne03) fd (fun _ => ne13) (fun _ => ne14) fd ff ff (fun _ => ⟨hsc0, hmin⟩) (fun _ => hzM)) pt5_5 wl19 55 rfl tr tm fm ht hf hev
    dsimp only [wl19] at hsum; rw [wSum_eb5_5 G σ 9 3 9 3 9 0 k0 k1 k2 k3 k4 k0 a0 a1 a2 a3 a4 hMa] at hsum; clear tr tm fm ht hf hev; omega
  refine sym2_m5 C G σ k0 k2 (fun M => Dj5 k0 k1 k2 k3 k4 M → (ZProp C G k0 k1 k2 k3 k4 σ M) → 55 ≤ 9 * rCount G σ k0 M + 3 * rCount G σ k1 M + 9 * rCount G σ k2 M + 3 * rCount G σ k3 M + 9 * rCount G σ k4 M) ?_ ?_ ?_ ?_ ?_ u0 u1 u2 u3 u4 hM hd hz0
  · intro a0 a1 a2 a3 a4 hMa t0 t1 hdM hzM; exact run a0 a1 a2 a3 a4 hMa hdM hzM (n 2 (n 3 (n 4 (n 10 (n 11 b (n 20 b (n 14 b (n 5 b (p 896))))) (n 21 (n 24 b (n 13 b (n 9 b (p 680)))) (n 12 (n 24 b (n 5 b (p 672))) (n 16 (n 6 (n 23 b (n 17 (n 7 b (p 676)) (p 908))) (p 544)) (p 548))))) (n 10 (n 20 (n 13 b (n 22 b (n 5 b (p 248)))) (n 13 (n 11 b (n 8 b (p 516))) (n 16 (n 6 (n 17 (n 7 b (p 668)) (p 80)) (p 844)) (p 132)))) (n 23 (n 21 (n 13 b (n 24 b (p 16))) (n 8 (n 18 (n 17 (n 7 b (p 424)) (p 532)) (p 340)) (p 344))) (n 16 (n 6 (n 17 (n 7 (n 13 b (n 24 b (p 16))) (p 420)) (p 176)) (p 1268)) (p 128))))) (n 12 (n 22 (n 10 (n 20 b (n 14 b (n 17 b (p 264)))) (n 24 (n 4 b (n 23 b (n 17 b (p 176)))) (n 17 (n 7 (n 16 (n 6 b (p 320)) (p 500)) (p 648)) (p 644)))) (n 11 (n 14 (n 24 b (n 13 b (p 8))) (n 16 (n 6 (n 5 (n 15 b (p 196)) (p 328)) (p 316)) (p 416))) (n 9 (n 19 (n 5 (n 15 (n 24 b (n 13 b (p 8))) (p 800)) (p 60)) (p 492)) (p 636)))) (n 21 (n 24 (n 14 (n 4 b (n 23 b (n 16 b (p 352)))) (n 23 (n 8 b (p 404)) (p 148))) (n 16 (n 6 (n 5 (n 15 (n 22 b (n 13 b (p 8))) (p 268)) (p 332)) (p 632)) (p 236))) (n 9 (n 5 (n 15 (n 19 (n 14 (n 10 b (n 16 (n 6 (n 4 b (n 8 b (p 344))) (p 544)) (p 548))) (n 23 (n 8 (n 18 (n 20 b (n 16 b (p 496))) (p 408)) (p 404)) (p 148))) (p 192)) (p 508)) (p 76)) (p 412))))) (n 13 (n 23 (n 10 (n 20 (n 3 b (n 12 b (n 24 b (n 16 b (p 236))))) (n 11 (n 3 b (n 14 b (n 16 b (p 496)))) (n 8 (n 18 (n 9 (n 19 b (p 1132)) (p 88)) (p 188)) (p 296)))) (n 21 (n 3 (n 11 b (n 20 b (n 8 b (p 296)))) (n 24 (n 14 b (n 20 b (n 16 b (p 496)))) (n 16 (n 6 (n 17 (n 7 b (p 648)) (p 644)) (p 320)) (p 500)))) (n 8 (n 18 (n 9 (n 19 (n 24 b (n 5 (n 15 (n 3 b (n 16 b (p 500))) (p 684)) (p 672))) (p 776)) (p 172)) (p 300)) (p 460)))) (n 11 (n 14 (n 21 (n 4 b (n 8 b (p 0))) (n 12 (n 17 b (p 48)) (p 28))) (n 5 (n 6 (n 16 (n 15 (n 12 b (n 21 b (p 28))) (p 616)) (p 232)) (p 480)) (p 52))) (n 5 (n 15 (n 9 (n 19 (n 21 (n 20 b (n 8 (n 18 (n 4 b (n 14 b (p 124))) (p 188)) (p 296))) (n 12 (n 17 (n 7 (n 4 b (n 8 b (p 0))) (p 444)) (p 48)) (p 28))) (p 476)) (p 484)) (p 84)) (p 292)))) (n 21 (n 24 (n 4 (n 11 (n 14 b (n 23 b (n 16 b (p 232)))) (n 22 (n 17 b (p 252)) (p 40))) (n 23 (n 8 (n 18 (n 22 b (n 11 b (p 40))) (p 100)) (p 68)) (a 0))) (n 16 (n 6 (n 5 (n 15 (n 4 (n 22 b (n 11 b (p 40))) (n 23 (n 10 b (p 16)) (a 0))) (p 464)) (p 96)) (p 396)) (p 308))) (n 5 (n 15 (n 9 (n 19 (n 23 (n 11 (n 10 b (n 8 (n 18 (n 4 b (n 24 b (p 16))) (p 300)) (p 460))) (n 22 (n 17 (n 7 (n 4 b (n 8 b (p 68))) (p 448)) (p 252)) (p 40))) (n 4 (n 12 (n 17 (n 7 (n 24 b (n 16 b (p 308))) (p 444)) (p 48)) (p 28)) (a 0))) (p 392)) (p 620)) (p 452)) (p 456))))) (1<<<0|||1<<<1) (0) (mo (mt 0 t0) (mt 1 t1)) mz rfl
  · intro a0 a1 a2 a3 a4 hMa t0 n1 n4 hdM hzM; exact run a0 a1 a2 a3 a4 hMa hdM hzM (n 10 (n 20 (n 12 (n 13 (n 2 (n 22 b (n 3 b (n 17 b (a 1)))) (n 23 (n 3 b (n 22 b (n 17 b (a 1)))) (n 8 (n 18 (n 11 b (n 5 (n 15 b (p 84)) (p 292))) (a 0)) (p 0)))) (n 22 (n 2 (n 11 b (n 21 b (n 3 b (n 23 b (n 17 b (z 2 3)))))) (n 23 (n 8 b (p 68)) (a 0))) (n 5 (n 15 (n 9 (n 16 (n 19 (n 6 (n 2 b (n 11 b (p 40))) (p 20)) (p 588)) (p 276)) (p 36)) (p 72)) (p 248)))) (n 23 (n 3 (n 13 (n 14 b (n 24 b (n 2 b (n 22 b (n 8 b (z 3 1)))))) (n 22 (n 2 b (n 8 b (p 68))) (n 5 (n 15 (n 16 (n 9 b (p 36)) (p 276)) (p 72)) (p 248)))) (n 22 (n 17 (n 7 (n 21 b (n 5 (n 15 b (p 508)) (p 76))) (p 156)) (p 120)) (a 1))) (n 5 (n 15 (n 16 (n 9 (n 19 (n 6 (n 2 (n 3 b (n 22 b (a 1))) (n 13 (n 21 b (p 28)) (a 0))) (p 56)) (p 432)) (p 92)) (p 352)) (p 104)) (p 440)))) (n 5 (n 15 (n 11 (n 14 (n 12 (n 13 b (n 17 (n 7 b (p 668)) (p 80))) (n 8 (n 18 (n 9 (n 19 (n 13 b (n 16 b (p 132))) (p 376)) (p 748)) (p 164)) (p 596))) (n 23 (n 8 (n 18 (n 17 (n 7 (n 13 b (n 16 b (p 132))) (p 584)) (p 580)) (p 1064)) (p 112)) (p 124))) (n 22 (n 17 (n 7 (n 8 (n 18 (n 23 (n 2 b (n 9 b (p 88))) (n 14 (n 9 b (p 820)) (p 124))) (p 512)) (p 516)) (p 180)) (p 864)) (p 224))) (a 6)) (p 24))) (n 20 (n 5 (n 15 (n 21 (n 24 (n 22 (n 23 b (n 17 (n 7 b (p 420)) (p 176))) (n 8 (n 18 (n 9 (n 19 (n 23 b (n 16 b (p 128))) (p 160)) (p 576)) (p 168)) (p 284))) (n 13 (n 8 (n 18 (n 17 (n 7 (n 23 b (n 16 b (p 128))) (p 572)) (p 140)) (p 600)) (p 108)) (p 16))) (n 12 (n 17 (n 7 (n 8 (n 18 (n 13 (n 2 b (n 9 b (p 172))) (n 24 (n 9 b (p 824)) (p 16))) (p 340)) (p 344)) (p 424)) (p 532)) (p 136))) (p 204)) (p 208)) (a 6))) (1<<<0) (1<<<1|||1<<<4) (mt 0 t0) (mo (mf 1 n1) (mf 4 n4)) rfl
  · intro a0 a1 a2 a3 a4 hMa n0 n1 n2 n3 n4 t10 t11 hdM hzM; exact run a0 a1 a2 a3 a4 hMa hdM hzM (n 13 (n 12 (n 14 (n 20 (n 22 b (n 17 b (a 1))) (n 5 (n 15 (n 22 b (n 17 (n 7 b (p 4)) (a 1))) (a 6)) (p 24))) (n 24 (n 9 (n 19 (n 20 b (n 23 b (p 124))) (p 324)) (p 256)) (a 3))) (n 22 (n 17 (n 7 (n 23 (n 21 b (n 9 (n 19 b (p 192)) (p 412))) (n 14 (n 21 b (p 28)) (p 148))) (p 156)) (p 120)) (a 1))) (n 23 (n 8 (n 18 (n 22 (n 24 (n 20 b (n 5 (n 15 b (a 6)) (p 24))) (n 14 (n 6 (n 16 b (p 308)) (p 396)) (a 3))) (n 12 (n 24 (n 5 (n 15 b (p 72)) (p 248)) (p 8)) (a 1))) (p 100)) (p 68)) (a 0))) (1<<<10|||1<<<11) (1<<<0|||1<<<1|||1<<<2|||1<<<3|||1<<<4) (mo (mt 10 t10) (mt 11 t11)) (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 3 n3)) (mf 4 n4)) rfl
  · intro a0 a1 a2 a3 a4 hMa n0 n1 n2 n3 n4 t10 n11 n14 hdM hzM; exact run a0 a1 a2 a3 a4 hMa hdM hzM (n 20 (n 21 (n 24 (n 5 (n 15 (n 16 (n 9 (n 19 (n 6 (n 22 b (n 12 b (a 1))) (p 400)) (p 324)) (p 256)) (p 312)) (p 552)) (p 700)) (a 3)) (a 29)) (p 220)) (1<<<10) (1<<<0|||1<<<1|||1<<<2|||1<<<3|||1<<<4|||1<<<11|||1<<<14) (mt 10 t10) (mo (mo (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 3 n3)) (mf 4 n4)) (mf 11 n11)) (mf 14 n14)) rfl
  · intro a0 a1 a2 a3 a4 hMa n0 n1 n2 n3 n4 n10 n11 n12 n13 n14 hdM hzM; exact run a0 a1 a2 a3 a4 hMa hdM hzM (n 20 (n 22 (n 23 (n 21 (n 24 (n 5 (n 7 (n 8 (n 6 b (p 740)) (p 404)) (p 448)) (p 700)) (p 16)) (p 136)) (p 148)) (p 40)) (p 220)) (0) (1<<<0|||1<<<1|||1<<<2|||1<<<3|||1<<<4|||1<<<10|||1<<<11|||1<<<12|||1<<<13|||1<<<14) mz (mo (mo (mo (mo (mo (mo (mo (mo (mo (mf 0 n0) (mf 1 n1)) (mf 2 n2)) (mf 3 n3)) (mf 4 n4)) (mf 10 n10)) (mf 11 n11)) (mf 12 n12)) (mf 13 n13)) (mf 14 n14)) rfl
private lemma fminW_1_all {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 k4 w u0 : V)
    (hK : IsComp5 C k0 k1 k2 k3 k4) (hM : IsComp1 C u0)
    (hd : Dj5 k0 k1 k2 k3 k4 {u0}) (σ : Equiv.Perm V) (hσ : AlmOn C G k4 k0 σ) (hnp : ¬ Packs C G)
    (hsc0 : 7 ≤ kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4)) (hmin : MinSc C G k0 k1 k2 k3 k4 σ)
    (nw1 : ¬ G.Adj (σ k1) (σ w))
    (σ1 : Equiv.Perm V) (hσ1 : AlmOn C G k4 k0 σ1) (hk1 : Fix5 σ1 σ w k1 k2 k3 k4 k0 k1 k2 k3 k4) (hu1 : EqOn σ1 σ {u0})
    (σ2 : Equiv.Perm V) (hσ2 : AlmOn C G k4 k0 σ2) (hk2 : Fix5 σ2 σ w k1 k0 k3 k4 k0 k1 k2 k3 k4) (hu2 : EqOn σ2 σ {u0})
    (σ3 : Equiv.Perm V) (hσ3 : AlmOn C G k4 k0 σ3) (hk3 : Fix5 σ3 σ w k1 k2 k3 k0 k0 k1 k2 k3 k4) (hu3 : EqOn σ3 σ {u0})
    (ne03 : ¬ G.Adj (σ k0) (σ k3))
    (ne13 : ¬ G.Adj (σ k1) (σ k3))
    (ne14 : ¬ G.Adj (σ k1) (σ k4))
    : 3 ≤ 3 * rCount G σ w {u0} + 2 * (rCount G σ k0 {u0} + rCount G σ k2 {u0} + rCount G σ k4 {u0}) := by
  have hev : evalDT 5 1 16404 7 true false pt5_1 wl20 3 (n 0 (n 2 b (n 5 b (p 1))) (n 5 b (p 19))) 0 0 = true := rfl
  have hsum : 3 ≤ wSumBool wl20 (eb5_1 G σ k0 k1 k2 k3 k4 w u0) := evalDT_sound (mkCtx5_1 C G k0 k1 k2 k3 k4 w u0 hK hM hd σ hσ hnp 16404 7 true false σ1 σ2 σ3 fd (fun _ => ne03) fd (fun _ => ne13) (fun _ => ne14) fd (fun _ => nw1) (fun _ => ⟨⟨hσ1, hk1, hu1⟩, ⟨hσ2, hk2, hu2⟩, ⟨hσ3, hk3, hu3⟩⟩) (fun _ => ⟨hsc0, hmin⟩) ff) pt5_1 wl20 3 rfl (n 0 (n 2 b (n 5 b (p 1))) (n 5 b (p 19))) 0 0 mz mz hev
  dsimp only [wl20] at hsum; rw [wSum_eb5_1 G σ 2 0 2 0 2 3 k0 k1 k2 k3 k4 w u0] at hsum; clear hev; omega
set_option maxHeartbeats 800000 in
private lemma fminW_3 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 k4 w u0 u1 u2 : V)
    (hK : IsComp5 C k0 k1 k2 k3 k4) (hM : IsComp3 C u0 u1 u2)
    (hd : Dj5 k0 k1 k2 k3 k4 {u0, u1, u2}) (σ : Equiv.Perm V) (hσ : AlmOn C G k4 k0 σ) (hnp : ¬ Packs C G)
    (hsc0 : 7 ≤ kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4)) (hmin : MinSc C G k0 k1 k2 k3 k4 σ)
    (nw1 : ¬ G.Adj (σ k1) (σ w))
    (σ1 : Equiv.Perm V) (hσ1 : AlmOn C G k4 k0 σ1) (hk1 : Fix5 σ1 σ w k1 k2 k3 k4 k0 k1 k2 k3 k4) (hu1 : EqOn σ1 σ {u0, u1, u2})
    (σ2 : Equiv.Perm V) (hσ2 : AlmOn C G k4 k0 σ2) (hk2 : Fix5 σ2 σ w k1 k0 k3 k4 k0 k1 k2 k3 k4) (hu2 : EqOn σ2 σ {u0, u1, u2})
    (σ3 : Equiv.Perm V) (hσ3 : AlmOn C G k4 k0 σ3) (hk3 : Fix5 σ3 σ w k1 k2 k3 k0 k0 k1 k2 k3 k4) (hu3 : EqOn σ3 σ {u0, u1, u2})
    (ne03 : ¬ G.Adj (σ k0) (σ k3))
    (ne13 : ¬ G.Adj (σ k1) (σ k3))
    (ne14 : ¬ G.Adj (σ k1) (σ k4))
    : 9 ≤ 3 * rCount G σ w {u0, u1, u2} + 2 * (rCount G σ k0 {u0, u1, u2} + rCount G σ k2 {u0, u1, u2} + rCount G σ k4 {u0, u1, u2}) := by
  have run (a0 a1 a2 : V) (hMa : IsComp3 C a0 a1 a2) (hdM : Dj5 k0 k1 k2 k3 k4 {a0, a1, a2}) (hu1M : EqOn σ1 σ {a0, a1, a2}) (hu2M : EqOn σ2 σ {a0, a1, a2}) (hu3M : EqOn σ3 σ {a0, a1, a2})
      (tr : DT) (tm fm : ℕ) (ht : ∀ i, tm.testBit i = true → (eb5_3 G σ k0 k1 k2 k3 k4 w a0 a1 a2).getD i false = true)
      (hf : ∀ i, fm.testBit i = true → (eb5_3 G σ k0 k1 k2 k3 k4 w a0 a1 a2).getD i false = false)
      (hev : evalDT 5 3 16404 7 true false pt5_3 wl21 9 tr tm fm = true) : 9 ≤ 3 * rCount G σ w {a0, a1, a2} + 2 * (rCount G σ k0 {a0, a1, a2} + rCount G σ k2 {a0, a1, a2} + rCount G σ k4 {a0, a1, a2}) := by
    have hsum : 9 ≤ wSumBool wl21 (eb5_3 G σ k0 k1 k2 k3 k4 w a0 a1 a2) := evalDT_sound (mkCtx5_3 C G k0 k1 k2 k3 k4 w a0 a1 a2 hK hMa hdM σ hσ hnp 16404 7 true false σ1 σ2 σ3 fd (fun _ => ne03) fd (fun _ => ne13) (fun _ => ne14) fd (fun _ => nw1) (fun _ => ⟨⟨hσ1, hk1, hu1M⟩, ⟨hσ2, hk2, hu2M⟩, ⟨hσ3, hk3, hu3M⟩⟩) (fun _ => ⟨hsc0, hmin⟩) ff) pt5_3 wl21 9 rfl tr tm fm ht hf hev
    dsimp only [wl21] at hsum; rw [wSum_eb5_3 G σ 2 0 2 0 2 3 k0 k1 k2 k3 k4 w a0 a1 a2 hMa] at hsum; clear tr tm fm ht hf hev; omega
  refine sym2_m3 C G σ w k0 (fun M => Dj5 k0 k1 k2 k3 k4 M → (EqOn σ1 σ M) → (EqOn σ2 σ M) → (EqOn σ3 σ M) → 9 ≤ 3 * rCount G σ w M + 2 * (rCount G σ k0 M + rCount G σ k2 M + rCount G σ k4 M)) ?_ ?_ ?_ ?_ ?_ u0 u1 u2 hM hd hu1 hu2 hu3
  · intro a0 a1 a2 hMa t15 t16 hdM hu1M hu2M hu3M; exact run a0 a1 a2 hMa hdM hu1M hu2M hu3M (n 0 (n 6 b (n 13 b (n 2 b (n 5 (n 9 (n 10 (n 11 (n 3 (n 4 (n 12 b (n 8 b (p 152))) (p 236)) (p 112)) (p 68)) (p 52)) (p 116)) (p 60))))) (n 7 (n 13 b (n 8 b (n 5 (n 9 (n 10 (n 11 (n 3 (n 4 (n 1 b (n 2 b (a 21))) (p 120)) (p 44)) (p 128)) (p 48)) (p 188)) (p 268)))) (n 2 (n 14 b (n 5 (n 9 (n 10 (n 11 (n 3 (n 4 (n 12 b (n 8 b (p 148))) (p 216)) (p 180)) (p 280)) (p 228)) (p 192)) (p 276))) (n 1 (n 13 b (a 2)) (a 41))))) (1<<<15|||1<<<16) (0) (mo (mt 15 t15) (mt 16 t16)) mz rfl
  · intro a0 a1 a2 hMa t15 n16 n17 hdM hu1M hu2M hu3M; exact run a0 a1 a2 hMa hdM hu1M hu2M hu3M (n 0 (n 6 (n 12 b (n 13 b (p 97))) (n 12 (n 8 b (p 105)) (p 73))) (n 6 (n 12 (n 2 b (p 91)) (p 74)) (p 75))) (1<<<15) (1<<<16|||1<<<17) (mt 15 t15) (mo (mf 16 n16) (mf 17 n17)) rfl
  · intro a0 a1 a2 hMa n15 n16 n17 t0 t1 hdM hu1M hu2M hu3M; exact run a0 a1 a2 hMa hdM hu1M hu2M hu3M (n 8 (n 12 (n 13 b (n 14 b (p 93))) (n 13 (n 14 b (p 161)) (p 101))) (n 6 (n 7 (n 2 b (p 247)) (p 109)) (p 169))) (1<<<0|||1<<<1) (1<<<15|||1<<<16|||1<<<17) (mo (mt 0 t0) (mt 1 t1)) (mo (mo (mf 15 n15) (mf 16 n16)) (mf 17 n17)) rfl
  · intro a0 a1 a2 hMa n15 n16 n17 t0 n1 n2 hdM hu1M hu2M hu3M; exact run a0 a1 a2 hMa hdM hu1M hu2M hu3M (p 95) (1<<<0) (1<<<15|||1<<<16|||1<<<17|||1<<<1|||1<<<2) (mt 0 t0) (mo (mo (mo (mo (mf 15 n15) (mf 16 n16)) (mf 17 n17)) (mf 1 n1)) (mf 2 n2)) rfl
  · intro a0 a1 a2 hMa n15 n16 n17 n0 n1 n2 hdM hu1M hu2M hu3M; exact run a0 a1 a2 hMa hdM hu1M hu2M hu3M (p 103) (0) (1<<<15|||1<<<16|||1<<<17|||1<<<0|||1<<<1|||1<<<2) mz (mo (mo (mo (mo (mo (mf 15 n15) (mf 16 n16)) (mf 17 n17)) (mf 0 n0)) (mf 1 n1)) (mf 2 n2)) rfl
set_option maxHeartbeats 800000 in
private lemma fminW_5 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj] (k0 k1 k2 k3 k4 w u0 u1 u2 u3 u4 : V)
    (hK : IsComp5 C k0 k1 k2 k3 k4) (hM : IsComp5 C u0 u1 u2 u3 u4)
    (hd : Dj5 k0 k1 k2 k3 k4 {u0, u1, u2, u3, u4}) (σ : Equiv.Perm V) (hσ : AlmOn C G k4 k0 σ) (hnp : ¬ Packs C G)
    (hsc0 : 7 ≤ kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4)) (hmin : MinSc C G k0 k1 k2 k3 k4 σ)
    (nw1 : ¬ G.Adj (σ k1) (σ w))
    (σ1 : Equiv.Perm V) (hσ1 : AlmOn C G k4 k0 σ1) (hk1 : Fix5 σ1 σ w k1 k2 k3 k4 k0 k1 k2 k3 k4) (hu1 : EqOn σ1 σ {u0, u1, u2, u3, u4})
    (σ2 : Equiv.Perm V) (hσ2 : AlmOn C G k4 k0 σ2) (hk2 : Fix5 σ2 σ w k1 k0 k3 k4 k0 k1 k2 k3 k4) (hu2 : EqOn σ2 σ {u0, u1, u2, u3, u4})
    (σ3 : Equiv.Perm V) (hσ3 : AlmOn C G k4 k0 σ3) (hk3 : Fix5 σ3 σ w k1 k2 k3 k0 k0 k1 k2 k3 k4) (hu3 : EqOn σ3 σ {u0, u1, u2, u3, u4})
    (ne03 : ¬ G.Adj (σ k0) (σ k3))
    (ne13 : ¬ G.Adj (σ k1) (σ k3))
    (ne14 : ¬ G.Adj (σ k1) (σ k4))
    : 15 ≤ 3 * rCount G σ w {u0, u1, u2, u3, u4} + 2 * (rCount G σ k0 {u0, u1, u2, u3, u4} + rCount G σ k2 {u0, u1, u2, u3, u4} + rCount G σ k4 {u0, u1, u2, u3, u4}) := by
  have run (a0 a1 a2 a3 a4 : V) (hMa : IsComp5 C a0 a1 a2 a3 a4) (hdM : Dj5 k0 k1 k2 k3 k4 {a0, a1, a2, a3, a4}) (hu1M : EqOn σ1 σ {a0, a1, a2, a3, a4}) (hu2M : EqOn σ2 σ {a0, a1, a2, a3, a4}) (hu3M : EqOn σ3 σ {a0, a1, a2, a3, a4})
      (tr : DT) (tm fm : ℕ) (ht : ∀ i, tm.testBit i = true → (eb5_5 G σ k0 k1 k2 k3 k4 w a0 a1 a2 a3 a4).getD i false = true)
      (hf : ∀ i, fm.testBit i = true → (eb5_5 G σ k0 k1 k2 k3 k4 w a0 a1 a2 a3 a4).getD i false = false)
      (hev : evalDT 5 5 16404 7 true false pt5_5 wl22 15 tr tm fm = true) : 15 ≤ 3 * rCount G σ w {a0, a1, a2, a3, a4} + 2 * (rCount G σ k0 {a0, a1, a2, a3, a4} + rCount G σ k2 {a0, a1, a2, a3, a4} + rCount G σ k4 {a0, a1, a2, a3, a4}) := by
    have hsum : 15 ≤ wSumBool wl22 (eb5_5 G σ k0 k1 k2 k3 k4 w a0 a1 a2 a3 a4) := evalDT_sound (mkCtx5_5 C G k0 k1 k2 k3 k4 w a0 a1 a2 a3 a4 hK hMa hdM σ hσ hnp 16404 7 true false σ1 σ2 σ3 fd (fun _ => ne03) fd (fun _ => ne13) (fun _ => ne14) fd (fun _ => nw1) (fun _ => ⟨⟨hσ1, hk1, hu1M⟩, ⟨hσ2, hk2, hu2M⟩, ⟨hσ3, hk3, hu3M⟩⟩) (fun _ => ⟨hsc0, hmin⟩) ff) pt5_5 wl22 15 rfl tr tm fm ht hf hev
    dsimp only [wl22] at hsum; rw [wSum_eb5_5 G σ 2 0 2 0 2 3 k0 k1 k2 k3 k4 w a0 a1 a2 a3 a4 hMa] at hsum; clear tr tm fm ht hf hev; omega
  refine sym2_m5 C G σ w k0 (fun M => Dj5 k0 k1 k2 k3 k4 M → (EqOn σ1 σ M) → (EqOn σ2 σ M) → (EqOn σ3 σ M) → 15 ≤ 3 * rCount G σ w M + 2 * (rCount G σ k0 M + rCount G σ k2 M + rCount G σ k4 M)) ?_ ?_ ?_ ?_ ?_ u0 u1 u2 u3 u4 hM hd hu1 hu2 hu3
  · intro a0 a1 a2 a3 a4 hMa t25 t26 hdM hu1M hu2M hu3M; exact run a0 a1 a2 a3 a4 hMa hdM hu1M hu2M hu3M (n 3 (n 13 (n 23 (n 28 b (n 2 (n 12 b (n 1 b (n 19 (n 5 (n 10 b (n 21 b (p 136))) (p 79)) (p 195)))) (n 11 (n 21 b (n 19 (n 5 (n 10 b (n 18 (n 8 (n 9 (n 24 b (n 15 (n 0 b (p 212)) (p 684))) (p 172)) (p 460)) (p 300))) (p 78)) (p 194))) (n 19 (n 5 (n 0 (n 20 b (n 18 (n 8 (n 9 (n 14 b (n 15 (n 16 (n 17 (n 6 (n 7 (n 1 b (n 22 b (p 224))) (n 29 b (p 181))) (p 241)) (p 265)) (p 419)) (p 688))) (p 88)) (p 296)) (p 188))) (n 21 (n 16 (n 6 (n 18 (n 24 b (n 17 (n 15 (n 8 (n 7 (n 9 (n 20 b (n 14 b (p 220))) (n 27 b (p 91))) (p 708)) (p 720)) (p 270)) (p 704))) (n 20 b (p 188))) (p 400)) (p 312)) (a 29))) (p 63)) (p 495))))) (n 2 (n 12 (n 27 b (n 1 b (n 19 (n 15 (n 18 (n 4 b (n 16 (n 5 (n 20 b (n 10 b (a 6))) (p 54)) (p 234))) (n 10 b (p 303))) (p 86)) (p 478)))) (n 1 (n 4 b (n 16 (n 6 (n 15 (n 5 (n 20 b (n 29 b (p 126))) (p 860)) (p 856)) (p 56)) (p 352))) (n 19 (n 15 (n 5 (n 9 (n 14 (n 10 b (n 21 b (p 136))) (n 18 (n 28 b (p 149)) (p 920))) (p 92)) (p 440)) (p 104)) (p 432)))) (n 11 (n 21 (n 14 b (n 16 (n 6 (n 15 (n 5 (n 20 b (n 29 b (p 125))) (p 52)) (p 616)) (p 480)) (p 232))) (n 12 (n 27 b (p 30)) (p 28))) (n 19 (n 15 (n 5 (n 9 (n 21 (n 4 (n 14 b (n 16 (n 6 (n 20 b (n 0 b (p 220))) (p 480)) (p 232))) (n 28 b (p 150))) (n 0 (n 17 (n 27 b (p 30)) (p 48)) (a 29))) (p 484)) (p 292)) (p 84)) (p 476))))) (n 2 (n 22 (n 27 b (n 29 b (n 23 (n 18 (n 8 (n 10 b (n 24 b (p 17))) (p 69)) (p 101)) (p 33)))) (n 1 (n 4 (n 24 b (n 28 b (p 9))) (n 16 (n 6 (n 15 (n 5 (n 10 (n 11 b (n 27 b (p 41))) (n 29 b (p 19))) (p 248)) (p 72)) (p 20)) (p 276))) (n 19 (n 15 (n 5 (n 9 (n 20 (n 10 (n 24 b (n 28 b (p 9))) (n 18 (n 8 (n 24 (n 29 b (n 4 b (p 19))) (n 28 b (p 9))) (p 284)) (p 168))) (n 16 (n 11 (n 6 (n 18 (n 17 (n 8 (n 7 (n 10 (n 28 b (n 24 b (p 9))) (n 4 (n 24 b (n 29 b (p 17))) (a 6))) (n 29 b (p 182))) (n 10 (n 14 b (p 112)) (p 284))) (n 4 (n 29 b (p 81)) (p 80))) (n 10 (n 29 b (p 514)) (p 168))) (p 736)) (p 224)) (p 184))) (p 36)) (p 1052)) (p 1048)) (p 588)))) (n 4 (n 24 (n 21 (n 11 b (n 22 b (p 40))) (n 19 (n 9 (n 15 (n 5 (n 23 (n 11 b (n 0 b (a 29))) (n 27 b (p 30))) (p 456)) (p 452)) (p 620)) (p 392))) (n 15 (n 5 (n 16 (n 6 (n 11 (n 10 (n 0 b (n 17 (n 7 (n 22 b (n 18 (n 28 b (p 9)) (p 916))) (p 936)) (p 952))) (n 19 (n 29 b (p 17)) (p 692))) (n 17 (n 22 (n 27 b (p 43)) (p 40)) (p 252))) (p 396)) (p 308)) (p 96)) (p 464))) (n 23 (n 28 (n 18 (n 8 (n 22 b (n 11 b (p 40))) (p 68)) (p 100)) (p 11)) (a 0))))) (n 12 (n 22 (n 27 (n 0 b (n 14 b (n 24 b (a 3)))) (n 29 (n 14 b (n 16 (n 5 (n 20 b (n 17 (n 7 (n 6 (n 11 b (n 15 (n 0 b (p 220)) (p 688))) (p 240)) (p 1204)) (p 264))) (p 55)) (p 235))) (n 13 (n 23 (n 18 (n 8 (n 0 b (n 24 b (p 18))) (p 3)) (p 851)) (p 34)) (p 35)))) (n 11 (n 14 (n 24 (n 29 b (n 6 (n 15 (n 27 b (n 1 b (p 42))) (p 74)) (p 22))) (n 28 b (p 10))) (n 16 (n 6 (n 5 (n 15 (n 24 (n 1 (n 0 b (n 29 b (p 127))) (n 17 (n 27 b (p 42)) (a 1))) (n 0 (n 13 (n 28 b (p 10)) (p 8)) (a 3))) (p 196)) (p 328)) (p 316)) (p 416))) (n 19 (n 15 (n 5 (n 9 (n 13 (n 20 (n 0 (n 24 b (n 28 b (p 10))) (n 18 (n 8 (n 24 (n 29 b (n 14 b (p 127))) (n 28 b (p 10))) (p 560)) (p 728))) (n 16 (n 1 (n 6 (n 18 (n 17 (n 8 (n 7 (n 0 (n 28 b (n 24 b (p 10))) (n 14 (n 24 b (n 29 b (p 18))) (p 220))) (n 29 b (p 181))) (n 0 (n 4 b (p 516)) (p 560))) (n 14 (n 29 b (p 82)) (p 264))) (n 0 (n 29 b (p 513)) (p 728))) (p 892)) (p 224)) (p 904))) (n 24 (n 17 (n 2 (n 27 b (p 41)) (p 40)) (p 912)) (p 8))) (p 636)) (p 60)) (p 800)) (p 492)))) (n 14 (n 24 (n 21 (n 1 (n 29 b (n 6 (n 15 (n 27 b (n 13 b (p 35))) (p 859)) (p 59))) (n 22 (n 27 b (p 31)) (a 1))) (n 19 (n 15 (n 9 (n 5 (n 1 (n 23 (n 10 b (n 16 (n 6 (n 18 (n 4 b (n 17 (n 8 (n 7 (n 29 b (n 13 b (p 19))) (p 424)) (p 344)) (p 532))) (n 29 b (p 341))) (p 544)) (p 548))) (n 2 (n 27 b (p 29)) (p 28))) (n 10 (n 27 b (p 31)) (p 136))) (p 76)) (p 412)) (p 508)) (p 192))) (n 15 (n 16 (n 5 (n 6 (n 1 (n 21 (n 22 (n 0 b (n 29 b (p 18))) (n 13 (n 28 b (p 10)) (p 8))) (n 19 (n 9 (n 0 (n 23 (n 22 b (n 13 b (p 8))) (n 2 (n 27 b (p 29)) (p 28))) (n 29 (n 10 b (p 212)) (p 18))) (p 412)) (p 192))) (n 17 (n 22 (n 27 (n 7 (n 19 (n 10 b (n 18 (n 21 b (p 136)) (p 600))) (n 21 b (p 192))) (p 156)) (p 31)) (a 1)) (p 120))) (p 632)) (p 332)) (p 236)) (p 268))) (n 23 (n 28 (n 18 (n 8 (n 22 (n 24 b (n 0 b (a 3))) (n 1 (n 6 (n 16 (n 5 (n 15 (n 0 b (n 24 b (a 3))) (p 196)) (p 328)) (p 416)) (p 316)) (a 1))) (p 404)) (p 408)) (p 151)) (p 148))))) (1<<<25|||1<<<26) (0) (mo (mt 25 t25) (mt 26 t26)) mz rfl
  · intro a0 a1 a2 a3 a4 hMa t25 n26 n29 hdM hu1M hu2M hu3M; exact run a0 a1 a2 a3 a4 hMa hdM hu1M hu2M hu3M (n 0 (n 10 (n 20 (n 2 (n 12 (n 22 b (n 3 b (n 15 (n 9 (n 6 (n 27 b (n 13 b (p 35))) (p 22)) (p 38)) (p 74)))) (n 3 (n 23 b (n 15 (n 9 (n 6 (n 27 b (n 13 b (p 33))) (p 57)) (p 93)) (p 105))) (n 15 (n 9 (n 6 (n 27 (n 28 b (n 22 b (p 45))) (n 13 (n 23 b (p 34)) (p 35))) (p 59)) (p 95)) (p 107)))) (n 28 (n 13 (n 23 b (n 15 (n 6 (n 9 (n 27 b (n 3 b (p 34))) (p 94)) (p 58)) (p 106))) (n 15 (n 9 (n 6 (n 27 b (n 3 (n 23 b (p 33)) (p 35))) (p 23)) (p 39)) (p 75))) (n 12 (n 22 (n 17 (n 7 (n 15 (n 13 b (n 4 b (p 11))) (n 13 b (p 75))) (p 7)) (p 815)) (p 46)) (p 47)))) (n 5 (n 15 (n 22 (n 17 (n 23 (n 18 (n 2 (n 12 b (n 19 (n 8 (n 3 b (n 16 (n 6 (n 9 (n 7 (n 27 b (n 1 b (p 31))) (n 1 b (p 156))) (p 95)) (p 59)) (p 134))) (n 14 b (p 113))) (p 377))) (n 19 (n 8 (n 13 (n 28 b (n 12 b (p 47))) (n 16 (n 9 (n 6 (n 7 (n 27 (n 28 b (n 12 b (p 47))) (n 3 (n 11 b (p 43)) (p 35))) (n 11 (n 28 b (p 7)) (p 448))) (p 23)) (p 39)) (p 133))) (n 4 (n 14 b (p 113)) (p 114))) (p 378))) (n 2 (n 12 b (p 165)) (p 166))) (n 4 (n 14 (n 19 (n 27 b (n 3 b (p 34))) (p 65)) (p 125)) (p 126))) (n 3 (n 13 (n 4 b (p 582)) (p 81)) (p 82))) (n 1 (n 11 (n 16 (n 28 (n 23 b (n 4 b (p 126))) (n 2 (n 12 b (p 45)) (p 46))) (p 185)) (p 225)) (p 226))) (p 873)) (p 25))) (n 20 (n 5 (n 15 (n 12 (n 17 (n 13 (n 18 (n 2 (n 22 b (n 19 (n 8 (n 3 b (n 16 (n 6 (n 9 (n 7 (n 27 b (n 1 b (p 42))) (n 1 b (p 4))) (p 38)) (p 22)) (p 131))) (n 24 b (p 109))) (p 161))) (n 19 (n 8 (n 23 (n 28 b (n 22 b (p 46))) (n 16 (n 9 (n 6 (n 7 (n 27 (n 28 b (n 22 b (p 46))) (n 3 (n 21 b (p 30)) (p 34))) (n 21 (n 28 b (p 7)) (p 444))) (p 58)) (p 94)) (p 129))) (n 4 (n 24 b (p 109)) (p 111))) (p 163))) (n 2 (n 22 b (p 169)) (p 171))) (n 24 (n 4 (n 19 (n 27 b (n 3 b (p 35))) (p 201)) (p 19)) (p 17))) (n 3 (n 23 (n 24 b (p 141)) (p 177)) (p 179))) (n 1 (n 21 (n 16 (n 28 (n 13 b (n 24 b (p 17))) (n 2 (n 22 b (p 45)) (p 47))) (p 365)) (p 137)) (p 139))) (p 205)) (p 209)) (p 537))) (n 10 (n 20 (n 5 (n 15 (n 2 (n 17 (n 3 (n 18 (n 12 (n 22 b (n 19 (n 8 (n 13 b (n 16 (n 6 (n 9 (n 7 (n 27 b (n 11 b (p 41))) (n 11 b (p 900))) (p 37)) (p 21)) (p 135))) (n 24 b (p 110))) (p 162))) (n 19 (n 8 (n 23 (n 28 b (n 22 b (p 45))) (n 16 (n 9 (n 6 (n 7 (n 27 (n 28 b (n 22 b (p 45))) (n 13 (n 21 b (p 29)) (p 33))) (n 21 (n 28 b (p 157)) (p 676))) (p 57)) (p 93)) (p 130))) (n 14 (n 24 b (p 110)) (p 115))) (p 379))) (n 12 (n 22 b (p 170)) (p 167))) (n 24 (n 14 (n 19 (n 27 b (n 13 b (p 35))) (p 67)) (p 127)) (p 18))) (n 13 (n 23 (n 24 b (p 142)) (p 178)) (p 83))) (n 11 (n 21 (n 16 (n 28 (n 3 b (n 24 b (p 18))) (n 12 (n 22 b (p 46)) (p 47))) (p 187)) (p 138)) (p 227))) (p 875)) (p 27)) (p 538)) (p 539))) (1<<<25) (1<<<26|||1<<<29) (mt 25 t25) (mo (mf 26 n26) (mf 29 n29)) rfl
  · intro a0 a1 a2 a3 a4 hMa n25 n26 n27 n28 n29 t0 t1 hdM hu1M hu2M hu3M; exact run a0 a1 a2 a3 a4 hMa hdM hu1M hu2M hu3M (n 2 (n 3 (n 10 (n 13 (n 14 (n 11 b (n 21 b (p 489))) (n 4 (n 24 b (p 153)) (p 155))) (n 23 (n 18 (n 8 (n 22 (n 4 b (n 14 b (p 155))) (n 15 (n 11 (n 12 b (p 45)) (p 41)) (p 73))) (p 69)) (p 101)) (p 33))) (n 20 (n 15 (n 5 (n 24 (n 4 (n 21 b (n 12 b (p 137))) (n 17 (n 13 (n 14 b (p 155)) (p 19)) (p 143))) (n 21 (n 13 (n 4 b (p 154)) (p 17)) (p 213))) (p 209)) (p 205)) (p 537))) (n 13 (n 23 (n 18 (n 8 (n 14 (n 24 (n 12 b (n 22 b (p 45))) (n 22 (n 4 b (p 154)) (p 10))) (n 12 (n 24 (n 4 b (p 155)) (p 153)) (p 151))) (p 3)) (p 851)) (p 34)) (p 35))) (n 12 (n 22 (n 17 (n 7 (n 13 (n 23 (n 11 (n 21 b (n 16 (n 19 (n 6 (n 8 (n 5 (n 18 (n 15 (n 9 (n 24 b (n 10 b (p 213))) (n 10 b (p 172))) (n 24 b (p 217))) (n 10 b (p 300))) (p 78)) (p 986)) (p 117)) (p 194)) (p 785))) (n 21 (n 16 (n 19 (n 6 (n 8 (n 5 (n 18 (n 15 (n 9 (n 14 b (n 24 b (p 153))) (n 20 b (p 88))) (n 14 b (p 199))) (n 20 b (p 188))) (p 63)) (p 563)) (p 401)) (p 559)) (p 313)) (p 489))) (n 21 (n 4 (n 3 b (p 34)) (p 150)) (p 30))) (n 4 (n 11 (n 23 (n 3 b (p 35)) (p 33)) (p 43)) (p 11))) (p 7)) (p 815)) (p 46)) (p 47))) (1<<<0|||1<<<1) (1<<<25|||1<<<26|||1<<<27|||1<<<28|||1<<<29) (mo (mt 0 t0) (mt 1 t1)) (mo (mo (mo (mo (mf 25 n25) (mf 26 n26)) (mf 27 n27)) (mf 28 n28)) (mf 29 n29)) rfl
  · intro a0 a1 a2 a3 a4 hMa n25 n26 n27 n28 n29 t0 n1 n4 hdM hu1M hu2M hu3M; exact run a0 a1 a2 a3 a4 hMa hdM hu1M hu2M hu3M (n 10 (n 20 (n 15 (n 11 (n 21 (n 16 (n 14 (n 24 (n 19 (n 9 (n 6 (n 17 (n 18 (n 12 b (n 22 b (p 45))) (n 12 b (p 1263))) (n 13 b (p 1259))) (p 119)) (p 15)) (p 1195)) (p 154)) (p 155)) (p 787)) (p 490)) (p 491)) (p 219)) (p 222)) (p 215)) (1<<<0) (1<<<25|||1<<<26|||1<<<27|||1<<<28|||1<<<29|||1<<<1|||1<<<4) (mt 0 t0) (mo (mo (mo (mo (mo (mo (mf 25 n25) (mf 26 n26)) (mf 27 n27)) (mf 28 n28)) (mf 29 n29)) (mf 1 n1)) (mf 4 n4)) rfl
  · intro a0 a1 a2 a3 a4 hMa n25 n26 n27 n28 n29 n0 n1 n2 n3 n4 hdM hu1M hu2M hu3M; exact run a0 a1 a2 a3 a4 hMa hdM hu1M hu2M hu3M (n 10 (n 20 (n 12 (n 22 (n 13 (n 23 (n 11 (n 21 b (p 138)) (p 227)) (p 150)) (p 11)) (p 42)) (p 31)) (p 222)) (p 215)) (0) (1<<<25|||1<<<26|||1<<<27|||1<<<28|||1<<<29|||1<<<0|||1<<<1|||1<<<2|||1<<<3|||1<<<4) mz (mo (mo (mo (mo (mo (mo (mo (mo (mo (mf 25 n25) (mf 26 n26)) (mf 27 n27)) (mf 28 n28)) (mf 29 n29)) (mf 0 n0)) (mf 1 n1)) (mf 2 n2)) (mf 3 n3)) (mf 4 n4)) rfl
end PureDTReflection
section MainShortCycles
lemma card_of_isComp3 {V : Type} [DecidableEq V] {C : SimpleGraph V} {u0 u1 u2 : V}
    (h : IsComp3 C u0 u1 u2) : ({u0, u1, u2} : Finset V).card = 3 := by
  rcases h with ⟨h01, h02, h12, -⟩; simp [h01, h02, h12]
lemma card_of_isComp4 {V : Type} [DecidableEq V] {C : SimpleGraph V} {u0 u1 u2 u3 : V}
    (h : IsComp4 C u0 u1 u2 u3) : ({u0, u1, u2, u3} : Finset V).card = 4 := by
  rcases h with ⟨h01, h02, h03, h12, h13, h23, -⟩; simp [h01, h02, h03, h12, h13, h23]
lemma card_of_isComp5 {V : Type} [DecidableEq V] {C : SimpleGraph V} {u0 u1 u2 u3 u4 : V}
    (h : IsComp5 C u0 u1 u2 u3 u4) : ({u0, u1, u2, u3, u4} : Finset V).card = 5 := by
  rcases h with ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34, -⟩
  simp [h01, h02, h03, h04, h12, h13, h14, h23, h24, h34]
lemma compSet_eq_of_isComp4 {V : Type} [Fintype V] [DecidableEq V] (C : SimpleGraph V)
    {k0 k1 k2 k3 : V} (hK : IsComp4 C k0 k1 k2 k3) :
    compSet C k0 = {k0, k1, k2, k3} := by
  rcases hK with ⟨_, _, _, _, _, _, n0, n1, n2, n3⟩
  have hcl : ∀ a b, (a = k0 ∨ a = k1 ∨ a = k2 ∨ a = k3) → C.Adj a b →
      (b = k0 ∨ b = k1 ∨ b = k2 ∨ b = k3) := by
    rintro a b (rfl | rfl | rfl | rfl) hab
    · rcases (n0 b).1 hab with rfl | rfl <;> tauto
    · rcases (n1 b).1 hab with rfl | rfl <;> tauto
    · rcases (n2 b).1 hab with rfl | rfl <;> tauto
    · rcases (n3 b).1 hab with rfl | rfl <;> tauto
  have hwalk : ∀ a, (a = k0 ∨ a = k1 ∨ a = k2 ∨ a = k3) → ∀ {u}, C.Walk a u →
      (u = k0 ∨ u = k1 ∨ u = k2 ∨ u = k3) := by
    intro a ha u w
    induction w with
    | nil => exact ha
    | @cons x y _ hxy _ ih => exact ih (hcl x y ha hxy)
  have e01 : C.Adj k0 k1 := (n0 k1).2 (Or.inr rfl)
  have e12 : C.Adj k1 k2 := (n1 k2).2 (Or.inr rfl)
  have e23 : C.Adj k2 k3 := (n2 k3).2 (Or.inr rfl)
  ext u; rw [mem_compSet]; simp only [mem_insert, mem_singleton]
  constructor
  · rintro ⟨w⟩; exact hwalk k0 (Or.inl rfl) w
  · rintro (rfl | rfl | rfl | rfl)
    · exact Reachable.refl _
    · exact e01.reachable
    · exact e01.reachable.trans e12.reachable
    · exact (e01.reachable.trans e12.reachable).trans e23.reachable
lemma compSet_eq_of_isComp5 {V : Type} [Fintype V] [DecidableEq V] (C : SimpleGraph V)
    {k0 k1 k2 k3 k4 : V} (hK : IsComp5 C k0 k1 k2 k3 k4) :
    compSet C k0 = {k0, k1, k2, k3, k4} := by
  rcases hK with ⟨_, _, _, _, _, _, _, _, _, _, n0, n1, n2, n3, n4⟩
  have hcl : ∀ a b, (a = k0 ∨ a = k1 ∨ a = k2 ∨ a = k3 ∨ a = k4) → C.Adj a b →
      (b = k0 ∨ b = k1 ∨ b = k2 ∨ b = k3 ∨ b = k4) := by
    rintro a b (rfl | rfl | rfl | rfl | rfl) hab
    · rcases (n0 b).1 hab with rfl | rfl <;> tauto
    · rcases (n1 b).1 hab with rfl | rfl <;> tauto
    · rcases (n2 b).1 hab with rfl | rfl <;> tauto
    · rcases (n3 b).1 hab with rfl | rfl <;> tauto
    · rcases (n4 b).1 hab with rfl | rfl <;> tauto
  have hwalk : ∀ a, (a = k0 ∨ a = k1 ∨ a = k2 ∨ a = k3 ∨ a = k4) → ∀ {u}, C.Walk a u →
      (u = k0 ∨ u = k1 ∨ u = k2 ∨ u = k3 ∨ u = k4) := by
    intro a ha u w
    induction w with
    | nil => exact ha
    | @cons x y _ hxy _ ih => exact ih (hcl x y ha hxy)
  have e01 : C.Adj k0 k1 := (n0 k1).2 (Or.inr rfl)
  have e12 : C.Adj k1 k2 := (n1 k2).2 (Or.inr rfl)
  have e23 : C.Adj k2 k3 := (n2 k3).2 (Or.inr rfl)
  have e34 : C.Adj k3 k4 := (n3 k4).2 (Or.inr rfl)
  ext u; rw [mem_compSet]; simp only [mem_insert, mem_singleton]
  constructor
  · rintro ⟨w⟩; exact hwalk k0 (Or.inl rfl) w
  · rintro (rfl | rfl | rfl | rfl | rfl)
    · exact Reachable.refl _
    · exact e01.reachable
    · exact e01.reachable.trans e12.reachable
    · exact (e01.reachable.trans e12.reachable).trans e23.reachable
    · exact ((e01.reachable.trans e12.reachable).trans e23.reachable).trans e34.reachable
lemma reachable_mono_sub {V : Type} {G' C : SimpleGraph V}
    (hsub : ∀ a b, G'.Adj a b → C.Adj a b) {v u : V} (h : G'.Reachable v u) :
    C.Reachable v u := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact Reachable.refl _
  | cons hab _ ih => exact (hsub _ _ hab).reachable.trans ih
lemma short_of_sub {V : Type} [Fintype V] {G' C : SimpleGraph V}
    (hsub : ∀ a b, G'.Adj a b → C.Adj a b)
    (hshort : ∀ v, Set.ncard {u | C.Reachable v u} ≤ 5) (v : V) :
    Set.ncard {u | G'.Reachable v u} ≤ 5 :=
  le_trans (Set.ncard_le_ncard (fun _ hu => reachable_mono_sub hsub hu) (Set.toFinite _)) (hshort v)
lemma almost_packing_short {V : Type} [Fintype V] (C G : SimpleGraph V)
    (hdeg : ∀ v a b c, C.Adj v a → C.Adj v b → C.Adj v c → a = b ∨ a = c ∨ b = c)
    (hshort : ∀ v, Set.ncard {u | C.Reachable v u} ≤ 5)
    (hIH : ∀ G' : SimpleGraph V,
      (∀ v a b c, G'.Adj v a → G'.Adj v b → G'.Adj v c → a = b ∨ a = c ∨ b = c) →
      (∀ v, Set.ncard {u | G'.Reachable v u} ≤ 5) →
      Set.ncard {p : V × V | G'.Adj p.1 p.2} < Set.ncard {p : V × V | C.Adj p.1 p.2} →
      Packs G' G)
    (x y : V) (hxy : C.Adj x y) :
    ∃ σ : Equiv.Perm V, ∀ a b, C.Adj a b → ¬(a = x ∧ b = y) → ¬(a = y ∧ b = x) →
      ¬ G.Adj (σ a) (σ b) := by
  let G' : SimpleGraph V :=
    { Adj := fun a b => C.Adj a b ∧ ¬(a = x ∧ b = y) ∧ ¬(a = y ∧ b = x)
      symm := ⟨fun a b h => ⟨h.1.symm, fun e => h.2.2 ⟨e.2, e.1⟩, fun e => h.2.1 ⟨e.2, e.1⟩⟩⟩
      loopless := ⟨fun a h => C.loopless.irrefl a h.1⟩ }
  have hdeg' : ∀ v a b c, G'.Adj v a → G'.Adj v b → G'.Adj v c → a = b ∨ a = c ∨ b = c :=
    fun v a b c ha hb hc => hdeg v a b c ha.1 hb.1 hc.1
  have hshort' := short_of_sub (G' := G') (C := C) (fun _ _ h => h.1) hshort
  have hss : {p : V × V | G'.Adj p.1 p.2} ⊂ {p : V × V | C.Adj p.1 p.2} :=
    (Set.ssubset_iff_of_subset (fun _ hp => hp.1)).2 ⟨(x, y), hxy, fun hp => hp.2.1 ⟨rfl, rfl⟩⟩
  obtain ⟨σ, hσ⟩ := hIH G' hdeg' hshort' (Set.ncard_lt_ncard hss (Set.toFinite _))
  exact ⟨σ, fun a b hab h1 h2 => hσ a b ⟨hab, h1, h2⟩⟩
private lemma pack_of_has_c4 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj]
    (hd : 3 * (G.maxDegree + 1) ≤ Fintype.card V + 1)
    (hdeg : ∀ v a b c, C.Adj v a → C.Adj v b → C.Adj v c → a = b ∨ a = c ∨ b = c)
    (hnl : ∀ x y, C.Adj x y → ∃ z, z ≠ y ∧ C.Adj x z)
    (hshort : ∀ v, Set.ncard {u | C.Reachable v u} ≤ 5)
    (hIH : ∀ G' : SimpleGraph V,
      (∀ v a b c, G'.Adj v a → G'.Adj v b → G'.Adj v c → a = b ∨ a = c ∨ b = c) →
      (∀ v, Set.ncard {u | G'.Reachable v u} ≤ 5) →
      Set.ncard {p : V × V | G'.Adj p.1 p.2} < Set.ncard {p : V × V | C.Adj p.1 p.2} →
      Packs G' G)
    {k0 k1 k2 k3 : V} (hK : IsComp4 C k0 k1 k2 k3) : Packs C G := by
  classical
  have hk30 : C.Adj k3 k0 := (hK.2.2.2.2.2.2.2.2.2 k0).2 (Or.inr rfl)
  obtain ⟨σ, hσ⟩ := almost_packing_short C G hdeg hshort hIH k3 k0 hk30
  by_contra hnp
  have e03 : G.Adj (σ k0) (σ k3) := by
    by_contra hn03
    exact hnp (OMA.packs_of_almost C G k3 k0 σ hσ (adj_symm_not G hn03))
  obtain ⟨c0, _, c2⟩ := comp4_c_nonadj hK σ hσ
  have e02_or_13 : G.Adj (σ k0) (σ k2) ∨ G.Adj (σ k1) (σ k3) := by
    by_contra hnor; push Not at hnor
    exact hnp (pack4_0 C G k0 k1 k2 k3 hK σ hσ ![0, 1, 3, 2] c0 hnor.2 (adj_symm_not G c2) (adj_symm_not G hnor.1))
  have hK_set : compSet C k0 = {k0, k1, k2, k3} := compSet_eq_of_isComp4 C hK
  have hK_card : (compSet C k0).card = 4 := by rw [hK_set]; exact card_of_isComp4 hK
  have hK_deg : 7 ≤ 2 * rCount G σ k0 (compSet C k0) + rCount G σ k1 (compSet C k0) +
      rCount G σ k2 (compSet C k0) + 2 * rCount G σ k3 (compSet C k0) := by
    rw [hK_set, rCount_comp4 G σ k0 _ _ _ _ hK, rCount_comp4 G σ k1 _ _ _ _ hK,
        rCount_comp4 G σ k2 _ _ _ _ hK, rCount_comp4 G σ k3 _ _ _ _ hK]
    have := b01_eq_one e03; have := b01_eq_one e03.symm
    rcases e02_or_13 with e02 | e13
    · have := b01_eq_one e02; have := b01_eq_one e02.symm; omega
    · have := b01_eq_one e13; have := b01_eq_one e13.symm; omega
  refine sum4_contradiction C G hd k0 k1 k2 k3 hK_card σ hK_deg (fun M hM_mem => ?_)
  have hne : M ≠ compSet C k0 := (mem_erase.1 hM_mem).1
  have hdM : Disjoint ({k0, k1, k2, k3} : Finset V) M :=
    hK_set ▸ compSet_disjoint C (mem_image_of_mem _ (mem_univ k0)) (mem_of_mem_erase hM_mem) hne.symm
  obtain ⟨v, -, rfl⟩ := mem_image.1 (mem_of_mem_erase hM_mem)
  rcases compSet_classify C hdeg hnl hshort v with
    ⟨u0, hMeq, hMc⟩ | ⟨u0, u1, u2, hMeq, hMc⟩ |
    ⟨u0, u1, u2, u3, hMeq, hMc⟩ | ⟨u0, u1, u2, u3, u4, hMeq, hMc⟩
  · rw [hMeq] at hdM ⊢; rw [card_singleton]
    exact f4_1_all C G k0 k1 k2 k3 u0 hK hMc hdM σ hσ hnp
  · rw [hMeq] at hdM ⊢; rw [card_of_isComp3 hMc]
    exact f4_3 C G k0 k1 k2 k3 u0 u1 u2 hK hMc hdM σ hσ hnp
  · rw [hMeq] at hdM ⊢; rw [card_of_isComp4 hMc]
    exact f4_4 C G k0 k1 k2 k3 u0 u1 u2 u3 hK hMc hdM σ hσ hnp
  · rw [hMeq] at hdM ⊢; rw [card_of_isComp5 hMc]
    exact f4_5 C G k0 k1 k2 k3 u0 u1 u2 u3 u4 hK hMc hdM σ hσ hnp
private lemma rCount_self5 {V : Type} [Fintype V] [DecidableEq V] (C G : SimpleGraph V)
    [DecidableRel G.Adj] (σ : Equiv.Perm V) {k0 k1 k2 k3 k4 : V} (hK : IsComp5 C k0 k1 k2 k3 k4)
    (z : V) :
    rCount G σ z (compSet C k0) =
      b01 (G.Adj (σ z) (σ k0)) + b01 (G.Adj (σ z) (σ k1)) + b01 (G.Adj (σ z) (σ k2)) +
      b01 (G.Adj (σ z) (σ k3)) + b01 (G.Adj (σ z) (σ k4)) := by
  rw [compSet_eq_of_isComp5 C hK, rCount_comp5 G σ z _ _ _ _ _ hK]
private lemma close_sum5_helper {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj]
    (hd : 3 * (G.maxDegree + 1) ≤ Fintype.card V + 1)
    (hno4 : ∀ a0 a1 a2 a3, ¬ IsComp4 C a0 a1 a2 a3)
    (hdeg : ∀ v a b c, C.Adj v a → C.Adj v b → C.Adj v c → a = b ∨ a = c ∨ b = c)
    (hnl : ∀ x y, C.Adj x y → ∃ z, z ≠ y ∧ C.Adj x z)
    (hshort : ∀ v, Set.ncard {u | C.Reachable v u} ≤ 5)
    (k0 k1 k2 k3 k4 : V) (hK : IsComp5 C k0 k1 k2 k3 k4) (σ : Equiv.Perm V)
    (w0 w1 w2 w3 w4 S : ℕ) (hwS : w0 + w1 + w2 + w3 + w4 = 3 * S)
    (hK_deg : 3 * S < w0 * rCount G σ k0 (compSet C k0) + w1 * rCount G σ k1 (compSet C k0) +
      w2 * rCount G σ k2 (compSet C k0) + w3 * rCount G σ k3 (compSet C k0) +
      w4 * rCount G σ k4 (compSet C k0))
    (b1 : ∀ u0, IsComp1 C u0 → Disjoint ({k0, k1, k2, k3, k4} : Finset V) {u0} →
      {u0} ∈ (univ.image (compSet C)).erase (compSet C k0) →
      S * 1 ≤ w0 * rCount G σ k0 {u0} + w1 * rCount G σ k1 {u0} +
        w2 * rCount G σ k2 {u0} + w3 * rCount G σ k3 {u0} + w4 * rCount G σ k4 {u0})
    (b3 : ∀ u0 u1 u2, IsComp3 C u0 u1 u2 → Disjoint ({k0, k1, k2, k3, k4} : Finset V) {u0, u1, u2} →
      {u0, u1, u2} ∈ (univ.image (compSet C)).erase (compSet C k0) →
      S * 3 ≤ w0 * rCount G σ k0 {u0, u1, u2} + w1 * rCount G σ k1 {u0, u1, u2} +
        w2 * rCount G σ k2 {u0, u1, u2} + w3 * rCount G σ k3 {u0, u1, u2} + w4 * rCount G σ k4 {u0, u1, u2})
    (b5 : ∀ u0 u1 u2 u3 u4, IsComp5 C u0 u1 u2 u3 u4 →
      Disjoint ({k0, k1, k2, k3, k4} : Finset V) {u0, u1, u2, u3, u4} →
      {u0, u1, u2, u3, u4} ∈ (univ.image (compSet C)).erase (compSet C k0) →
      S * 5 ≤ w0 * rCount G σ k0 {u0, u1, u2, u3, u4} + w1 * rCount G σ k1 {u0, u1, u2, u3, u4} +
        w2 * rCount G σ k2 {u0, u1, u2, u3, u4} + w3 * rCount G σ k3 {u0, u1, u2, u3, u4} +
        w4 * rCount G σ k4 {u0, u1, u2, u3, u4}) : False := by
  have hK_set : compSet C k0 = {k0, k1, k2, k3, k4} := compSet_eq_of_isComp5 C hK
  have hK_card : (compSet C k0).card = 5 := by rw [hK_set]; exact card_of_isComp5 hK
  refine sum5_contradiction C G hd k0 k1 k2 k3 k4 hK_card σ w0 w1 w2 w3 w4 S hwS hK_deg (fun M hM_mem => ?_)
  have hne : M ≠ compSet C k0 := (mem_erase.1 hM_mem).1
  have hdM : Disjoint ({k0, k1, k2, k3, k4} : Finset V) M :=
    hK_set ▸ compSet_disjoint C (mem_image_of_mem _ (mem_univ k0)) (mem_of_mem_erase hM_mem) hne.symm
  obtain ⟨v, -, rfl⟩ := mem_image.1 (mem_of_mem_erase hM_mem)
  rcases compSet_classify C hdeg hnl hshort v with
    ⟨u0, hMeq, hMc⟩ | ⟨u0, u1, u2, hMeq, hMc⟩ |
    ⟨u0, u1, u2, u3, _, hMc⟩ | ⟨u0, u1, u2, u3, u4, hMeq, hMc⟩
  · rw [hMeq] at hdM hM_mem ⊢; rw [card_singleton]; exact b1 u0 hMc hdM hM_mem
  · rw [hMeq] at hdM hM_mem ⊢; rw [card_of_isComp3 hMc]; exact b3 u0 u1 u2 hMc hdM hM_mem
  · exact False.elim (hno4 u0 u1 u2 u3 hMc)
  · rw [hMeq] at hdM hM_mem ⊢; rw [card_of_isComp5 hMc]; exact b5 u0 u1 u2 u3 u4 hMc hdM hM_mem
private lemma close_fno02 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj]
    (hd : 3 * (G.maxDegree + 1) ≤ Fintype.card V + 1)
    (hno4 : ∀ a0 a1 a2 a3, ¬ IsComp4 C a0 a1 a2 a3)
    (hdeg : ∀ v a b c, C.Adj v a → C.Adj v b → C.Adj v c → a = b ∨ a = c ∨ b = c)
    (hnl : ∀ x y, C.Adj x y → ∃ z, z ≠ y ∧ C.Adj x z)
    (hshort : ∀ v, Set.ncard {u | C.Reachable v u} ≤ 5)
    (k0 k1 k2 k3 k4 : V) (hK : IsComp5 C k0 k1 k2 k3 k4) (σ : Equiv.Perm V)
    (hσ : ∀ a b, C.Adj a b → ¬(a = k4 ∧ b = k0) → ¬(a = k0 ∧ b = k4) → ¬ G.Adj (σ a) (σ b))
    (hnp : ¬ Packs C G) (ne02 : ¬ G.Adj (σ k0) (σ k2))
    (hK_deg : 3 * 2 < 2 * rCount G σ k0 (compSet C k0) + 1 * rCount G σ k1 (compSet C k0) +
      0 * rCount G σ k2 (compSet C k0) + 1 * rCount G σ k3 (compSet C k0) +
      2 * rCount G σ k4 (compSet C k0)) : False :=
  close_sum5_helper C G hd hno4 hdeg hnl hshort k0 k1 k2 k3 k4 hK σ 2 1 0 1 2 2 rfl hK_deg
    (fun u0 hMc hdM _ => fno02_1_all C G k0 k1 k2 k3 k4 u0 hK hMc hdM σ hσ hnp ne02)
    (fun u0 u1 u2 hMc hdM _ => fno02_3 C G k0 k1 k2 k3 k4 u0 u1 u2 hK hMc hdM σ hσ hnp ne02)
    (fun u0 u1 u2 u3 u4 hMc hdM _ => fno02_5 C G k0 k1 k2 k3 k4 u0 u1 u2 u3 u4 hK hMc hdM σ hσ hnp ne02)
private lemma close_fred03 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj]
    (hd : 3 * (G.maxDegree + 1) ≤ Fintype.card V + 1)
    (hno4 : ∀ a0 a1 a2 a3, ¬ IsComp4 C a0 a1 a2 a3)
    (hdeg : ∀ v a b c, C.Adj v a → C.Adj v b → C.Adj v c → a = b ∨ a = c ∨ b = c)
    (hnl : ∀ x y, C.Adj x y → ∃ z, z ≠ y ∧ C.Adj x z)
    (hshort : ∀ v, Set.ncard {u | C.Reachable v u} ≤ 5)
    (k0 k1 k2 k3 k4 : V) (hK : IsComp5 C k0 k1 k2 k3 k4) (σ : Equiv.Perm V)
    (hσ : ∀ a b, C.Adj a b → ¬(a = k4 ∧ b = k0) → ¬(a = k0 ∧ b = k4) → ¬ G.Adj (σ a) (σ b))
    (hnp : ¬ Packs C G) (hsc0 : 9 ≤ kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4))
    (hmin : ∀ τ : Equiv.Perm V, (∀ a b, C.Adj a b → ¬(a = k4 ∧ b = k0) → ¬(a = k0 ∧ b = k4) → ¬ G.Adj (τ a) (τ b)) → kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4) ≤ kScore G (τ k0) (τ k1) (τ k2) (τ k3) (τ k4))
    (ne13 : ¬ G.Adj (σ k1) (σ k3)) (ne14 : ¬ G.Adj (σ k1) (σ k4))
    (hK_deg : 3 * 1 < 2 * rCount G σ k0 (compSet C k0) + 1 * rCount G σ k4 (compSet C k0)) : False :=
  close_sum5_helper C G hd hno4 hdeg hnl hshort k0 k1 k2 k3 k4 hK σ 2 0 0 0 1 1 rfl (by omega)
    (fun u0 hMc hdM _ => fred03_1_all C G k0 k1 k2 k3 k4 u0 hK hMc hdM σ hσ hnp hsc0 hmin ne13 ne14)
    (fun u0 u1 u2 hMc hdM _ => fred03_3 C G k0 k1 k2 k3 k4 u0 u1 u2 hK hMc hdM σ hσ hnp hsc0 hmin ne13 ne14)
    (fun u0 u1 u2 u3 u4 hMc hdM _ => fred03_5 C G k0 k1 k2 k3 k4 u0 u1 u2 u3 u4 hK hMc hdM σ hσ hnp hsc0 hmin ne13 ne14)
private lemma close_fred13 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj]
    (hd : 3 * (G.maxDegree + 1) ≤ Fintype.card V + 1)
    (hno4 : ∀ a0 a1 a2 a3, ¬ IsComp4 C a0 a1 a2 a3)
    (hdeg : ∀ v a b c, C.Adj v a → C.Adj v b → C.Adj v c → a = b ∨ a = c ∨ b = c)
    (hnl : ∀ x y, C.Adj x y → ∃ z, z ≠ y ∧ C.Adj x z)
    (hshort : ∀ v, Set.ncard {u | C.Reachable v u} ≤ 5)
    (k0 k1 k2 k3 k4 : V) (hK : IsComp5 C k0 k1 k2 k3 k4) (σ : Equiv.Perm V)
    (hσ : ∀ a b, C.Adj a b → ¬(a = k4 ∧ b = k0) → ¬(a = k0 ∧ b = k4) → ¬ G.Adj (σ a) (σ b))
    (hnp : ¬ Packs C G) (hsc0 : 9 ≤ kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4))
    (hmin : ∀ τ : Equiv.Perm V, (∀ a b, C.Adj a b → ¬(a = k4 ∧ b = k0) → ¬(a = k0 ∧ b = k4) → ¬ G.Adj (τ a) (τ b)) → kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4) ≤ kScore G (τ k0) (τ k1) (τ k2) (τ k3) (τ k4))
    (ne03 : ¬ G.Adj (σ k0) (σ k3)) (ne14 : ¬ G.Adj (σ k1) (σ k4))
    (hK_deg : 3 * 2 < 2 * rCount G σ k0 (compSet C k0) + 1 * rCount G σ k1 (compSet C k0) +
      1 * rCount G σ k2 (compSet C k0) + 1 * rCount G σ k3 (compSet C k0) +
      1 * rCount G σ k4 (compSet C k0)) : False :=
  close_sum5_helper C G hd hno4 hdeg hnl hshort k0 k1 k2 k3 k4 hK σ 2 1 1 1 1 2 rfl hK_deg
    (fun u0 hMc hdM _ => fred13_1_all C G k0 k1 k2 k3 k4 u0 hK hMc hdM σ hσ hnp hsc0 hmin ne03 ne14)
    (fun u0 u1 u2 hMc hdM _ => fred13_3 C G k0 k1 k2 k3 k4 u0 u1 u2 hK hMc hdM σ hσ hnp hsc0 hmin ne03 ne14)
    (fun u0 u1 u2 u3 u4 hMc hdM _ => fred13_5 C G k0 k1 k2 k3 k4 u0 u1 u2 u3 u4 hK hMc hdM σ hσ hnp hsc0 hmin ne03 ne14)
private lemma close_fred0313 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj]
    (hd : 3 * (G.maxDegree + 1) ≤ Fintype.card V + 1)
    (hno4 : ∀ a0 a1 a2 a3, ¬ IsComp4 C a0 a1 a2 a3)
    (hdeg : ∀ v a b c, C.Adj v a → C.Adj v b → C.Adj v c → a = b ∨ a = c ∨ b = c)
    (hnl : ∀ x y, C.Adj x y → ∃ z, z ≠ y ∧ C.Adj x z)
    (hshort : ∀ v, Set.ncard {u | C.Reachable v u} ≤ 5)
    (k0 k1 k2 k3 k4 : V) (hK : IsComp5 C k0 k1 k2 k3 k4) (σ : Equiv.Perm V)
    (hσ : ∀ a b, C.Adj a b → ¬(a = k4 ∧ b = k0) → ¬(a = k0 ∧ b = k4) → ¬ G.Adj (σ a) (σ b))
    (hnp : ¬ Packs C G) (hsc0 : 11 ≤ kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4))
    (hmin : ∀ τ : Equiv.Perm V, (∀ a b, C.Adj a b → ¬(a = k4 ∧ b = k0) → ¬(a = k0 ∧ b = k4) → ¬ G.Adj (τ a) (τ b)) → kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4) ≤ kScore G (τ k0) (τ k1) (τ k2) (τ k3) (τ k4))
    (ne14 : ¬ G.Adj (σ k1) (σ k4))
    (hK_deg : 3 * 3 < 3 * rCount G σ k0 (compSet C k0) + 1 * rCount G σ k1 (compSet C k0) +
      3 * rCount G σ k2 (compSet C k0) + 2 * rCount G σ k3 (compSet C k0)) : False :=
  close_sum5_helper C G hd hno4 hdeg hnl hshort k0 k1 k2 k3 k4 hK σ 3 1 3 2 0 3 rfl (by omega)
    (fun u0 hMc hdM _ => fred0313_1_all C G k0 k1 k2 k3 k4 u0 hK hMc hdM σ hσ hnp hsc0 hmin ne14)
    (fun u0 u1 u2 hMc hdM _ => fred0313_3 C G k0 k1 k2 k3 k4 u0 u1 u2 hK hMc hdM σ hσ hnp hsc0 hmin ne14)
    (fun u0 u1 u2 u3 u4 hMc hdM _ => fred0313_5 C G k0 k1 k2 k3 k4 u0 u1 u2 u3 u4 hK hMc hdM σ hσ hnp hsc0 hmin ne14)
private lemma close_fred0314 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj]
    (hd : 3 * (G.maxDegree + 1) ≤ Fintype.card V + 1)
    (hno4 : ∀ a0 a1 a2 a3, ¬ IsComp4 C a0 a1 a2 a3)
    (hdeg : ∀ v a b c, C.Adj v a → C.Adj v b → C.Adj v c → a = b ∨ a = c ∨ b = c)
    (hnl : ∀ x y, C.Adj x y → ∃ z, z ≠ y ∧ C.Adj x z)
    (hshort : ∀ v, Set.ncard {u | C.Reachable v u} ≤ 5)
    (k0 k1 k2 k3 k4 : V) (hK : IsComp5 C k0 k1 k2 k3 k4) (σ : Equiv.Perm V)
    (hσ : ∀ a b, C.Adj a b → ¬(a = k4 ∧ b = k0) → ¬(a = k0 ∧ b = k4) → ¬ G.Adj (σ a) (σ b))
    (hnp : ¬ Packs C G) (hsc0 : 11 ≤ kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4))
    (hmin : ∀ τ : Equiv.Perm V, (∀ a b, C.Adj a b → ¬(a = k4 ∧ b = k0) → ¬(a = k0 ∧ b = k4) → ¬ G.Adj (τ a) (τ b)) → kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4) ≤ kScore G (τ k0) (τ k1) (τ k2) (τ k3) (τ k4))
    (ne13 : ¬ G.Adj (σ k1) (σ k3))
    (hK_deg : 3 * 1 < 2 * rCount G σ k0 (compSet C k0) + 1 * rCount G σ k4 (compSet C k0)) : False :=
  close_sum5_helper C G hd hno4 hdeg hnl hshort k0 k1 k2 k3 k4 hK σ 2 0 0 0 1 1 rfl (by omega)
    (fun u0 hMc hdM _ => fred0314_1_all C G k0 k1 k2 k3 k4 u0 hK hMc hdM σ hσ hnp hsc0 hmin ne13)
    (fun u0 u1 u2 hMc hdM _ => fred0314_3 C G k0 k1 k2 k3 k4 u0 u1 u2 hK hMc hdM σ hσ hnp hsc0 hmin ne13)
    (fun u0 u1 u2 u3 u4 hMc hdM _ => fred0314_5 C G k0 k1 k2 k3 k4 u0 u1 u2 u3 u4 hK hMc hdM σ hσ hnp hsc0 hmin ne13)
private lemma close_fredall {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj]
    (hd : 3 * (G.maxDegree + 1) ≤ Fintype.card V + 1)
    (hno4 : ∀ a0 a1 a2 a3, ¬ IsComp4 C a0 a1 a2 a3)
    (hdeg : ∀ v a b c, C.Adj v a → C.Adj v b → C.Adj v c → a = b ∨ a = c ∨ b = c)
    (hnl : ∀ x y, C.Adj x y → ∃ z, z ≠ y ∧ C.Adj x z)
    (hshort : ∀ v, Set.ncard {u | C.Reachable v u} ≤ 5)
    (k0 k1 k2 k3 k4 : V) (hK : IsComp5 C k0 k1 k2 k3 k4) (σ : Equiv.Perm V)
    (hσ : ∀ a b, C.Adj a b → ¬(a = k4 ∧ b = k0) → ¬(a = k0 ∧ b = k4) → ¬ G.Adj (σ a) (σ b))
    (hnp : ¬ Packs C G) (hsc0 : 13 ≤ kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4))
    (hmin : ∀ τ : Equiv.Perm V, (∀ a b, C.Adj a b → ¬(a = k4 ∧ b = k0) → ¬(a = k0 ∧ b = k4) → ¬ G.Adj (τ a) (τ b)) → kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4) ≤ kScore G (τ k0) (τ k1) (τ k2) (τ k3) (τ k4))
    (hK_deg : 3 * 2 < 2 * rCount G σ k0 (compSet C k0) + 1 * rCount G σ k1 (compSet C k0) +
      1 * rCount G σ k3 (compSet C k0) + 2 * rCount G σ k4 (compSet C k0)) : False :=
  close_sum5_helper C G hd hno4 hdeg hnl hshort k0 k1 k2 k3 k4 hK σ 2 1 0 1 2 2 rfl (by omega)
    (fun u0 hMc hdM _ => fredall_1_all C G k0 k1 k2 k3 k4 u0 hK hMc hdM σ hσ hnp hsc0 hmin)
    (fun u0 u1 u2 hMc hdM _ => fredall_3 C G k0 k1 k2 k3 k4 u0 u1 u2 hK hMc hdM σ hσ hnp hsc0 hmin)
    (fun u0 u1 u2 u3 u4 hMc hdM _ => fredall_5 C G k0 k1 k2 k3 k4 u0 u1 u2 u3 u4 hK hMc hdM σ hσ hnp hsc0 hmin)
private lemma e0min_with_w {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj]
    (hd : 3 * (G.maxDegree + 1) ≤ Fintype.card V + 1)
    (hno4 : ∀ a0 a1 a2 a3, ¬ IsComp4 C a0 a1 a2 a3)
    (hdeg : ∀ v a b c, C.Adj v a → C.Adj v b → C.Adj v c → a = b ∨ a = c ∨ b = c)
    (hnl : ∀ x y, C.Adj x y → ∃ z, z ≠ y ∧ C.Adj x z)
    (hshort : ∀ v, Set.ncard {u | C.Reachable v u} ≤ 5)
    (k0 k1 k2 k3 k4 w : V) (hK : IsComp5 C k0 k1 k2 k3 k4) (σ : Equiv.Perm V)
    (hσ : ∀ a b, C.Adj a b → ¬(a = k4 ∧ b = k0) → ¬(a = k0 ∧ b = k4) → ¬ G.Adj (σ a) (σ b))
    (hnp : ¬ Packs C G) (hsc0 : 7 ≤ kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4))
    (hmin : ∀ τ : Equiv.Perm V, (∀ a b, C.Adj a b → ¬(a = k4 ∧ b = k0) → ¬(a = k0 ∧ b = k4) → ¬ G.Adj (τ a) (τ b)) → kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4) ≤ kScore G (τ k0) (τ k1) (τ k2) (τ k3) (τ k4))
    (e02 : G.Adj (σ k0) (σ k2)) (ne03 : ¬ G.Adj (σ k0) (σ k3)) (e04 : G.Adj (σ k0) (σ k4))
    (ne13 : ¬ G.Adj (σ k1) (σ k3)) (ne14 : ¬ G.Adj (σ k1) (σ k4)) (e24 : G.Adj (σ k2) (σ k4))
    (hw_out : w ∉ compSet C k0) (nw1 : ¬ G.Adj (σ k1) (σ w))
    (hwnb0 : ∀ b, C.Adj w b → ¬ G.Adj (σ k0) (σ b))
    (hwnb2 : ∀ b, C.Adj w b → ¬ G.Adj (σ k2) (σ b))
    (hwnb4 : ∀ b, C.Adj w b → ¬ G.Adj (σ k4) (σ b)) : False := by
  have hK_set : compSet C k0 = {k0, k1, k2, k3, k4} := compSet_eq_of_isComp5 C hK
  have hK_card : (compSet C k0).card = 5 := by rw [hK_set]; exact card_of_isComp5 hK
  have hwK : w ∉ ({k0, k1, k2, k3, k4} : Finset V) := hK_set ▸ hw_out
  have b04 := b01_eq_one e04; have b40 := b01_eq_one e04.symm
  obtain ⟨c0, c1, c2, c3⟩ := comp5_c_nonadj hK σ hσ
  obtain ⟨σ1, hσ1, h1i, h1o⟩ := k0_w_almost C G k0 k1 k2 k3 k4 w hK hwK σ hσ ![5,1,2,3,4,0]
    (adj_symm_not G nw1) c1 c2 c3 hwnb0
  obtain ⟨σ2, hσ2, h2i, h2o⟩ := k0_w_almost C G k0 k1 k2 k3 k4 w hK hwK σ hσ ![5,1,0,3,4,2]
    (adj_symm_not G nw1) (adj_symm_not G c0) ne03 c3 hwnb2
  obtain ⟨σ3, hσ3, h3i, h3o⟩ := k0_w_almost C G k0 k1 k2 k3 k4 w hK hwK σ hσ ![5,1,2,3,0,4]
    (adj_symm_not G nw1) c1 c2 (adj_symm_not G ne03) hwnb4
  obtain ⟨σ4, hσ4, h4i, _⟩ := k0_w_almost C G k0 k1 k2 k3 k4 w hK hwK σ hσ ![5,1,4,3,2,0]
    (adj_symm_not G nw1) ne14 (adj_symm_not G c3) (adj_symm_not G c2) hwnb0
  have ew4 : G.Adj (σ w) (σ k4) := by
    by_contra hn
    have e4 : σ1 k4 = σ k4 := h1i 4; have e0 : σ1 k0 = σ w := h1i 0
    have h40 : ¬ G.Adj (σ1 k4) (σ1 k0) := by rw [e4, e0]; exact adj_symm_not G hn
    exact hnp (OMA.packs_of_almost C G k4 k0 σ1 hσ1 h40)
  have ew0 : G.Adj (σ w) (σ k0) := by
    by_contra hn
    have e4 : σ3 k4 = σ k0 := h3i 4; have e0 : σ3 k0 = σ w := h3i 0
    have h40 : ¬ G.Adj (σ3 k4) (σ3 k0) := by rw [e4, e0]; exact adj_symm_not G hn
    exact hnp (OMA.packs_of_almost C G k4 k0 σ3 hσ3 h40)
  have ew2 : G.Adj (σ w) (σ k2) := by
    by_contra hn
    have e4 : σ4 k4 = σ k2 := h4i 4; have e0 : σ4 k0 = σ w := h4i 0
    have h40 : ¬ G.Adj (σ4 k4) (σ4 k0) := by rw [e4, e0]; exact adj_symm_not G hn
    exact hnp (OMA.packs_of_almost C G k4 k0 σ4 hσ4 h40)
  have hwK_cnt : 3 ≤ rCount G σ w (compSet C k0) := by
    rw [hK_set, rCount_comp5 G σ w _ _ _ _ _ hK]
    have := b01_eq_one ew0; have := b01_eq_one ew2; have := b01_eq_one ew4; omega
  have hK_A : 6 ≤ rCount G σ k0 (compSet C k0) + rCount G σ k2 (compSet C k0) +
      rCount G σ k4 (compSet C k0) := by
    rw [hK_set, rCount_comp5 G σ k0 _ _ _ _ _ hK, rCount_comp5 G σ k2 _ _ _ _ _ hK,
        rCount_comp5 G σ k4 _ _ _ _ _ hK]
    have := b01_eq_one e02; have := b01_eq_one e02.symm
    have := b01_eq_one e04; have := b01_eq_one e04.symm
    have := b01_eq_one e24; have := b01_eq_one e24.symm; omega
  let Mw := compSet C w
  have hMw_ne : Mw ≠ compSet C k0 := fun heq => hw_out (heq ▸ self_mem_compSet C w)
  have hMw_mem : Mw ∈ (univ.image (compSet C)).erase (compSet C k0) :=
    mem_erase.2 ⟨hMw_ne, mem_image_of_mem _ (mem_univ w)⟩
  have hMw_A : 3 * Mw.card < 2 * (rCount G σ k0 Mw + rCount G σ k2 Mw + rCount G σ k4 Mw) + 12 := by
    have hdMw : Disjoint ({k0, k1, k2, k3, k4} : Finset V) Mw :=
      hK_set ▸ compSet_disjoint C (mem_image_of_mem _ (mem_univ k0)) (mem_image_of_mem _ (mem_univ w)) hMw_ne.symm
    rcases compSet_classify C hdeg hnl hshort w with
      ⟨u0, hMeq, _⟩ | ⟨u0, u1, u2, hMeq, hMc⟩ |
      ⟨u0, u1, u2, u3, _, hMc⟩ | ⟨u0, u1, u2, u3, u4, hMeq, hMc⟩
    · change 3 * (compSet C w).card < _; rw [hMeq, card_singleton]; omega
    · change 3 * (compSet C w).card < _; rw [hMeq, card_of_isComp3 hMc]; omega
    · exact False.elim (hno4 u0 u1 u2 u3 hMc)
    · dsimp only [Mw] at hdMw ⊢
      rw [hMeq] at hdMw ⊢; rw [card_of_isComp5 hMc]
      have hA2 := fminA_5 C G k0 k1 k2 k3 k4 u0 u1 u2 u3 u4 hK hMc hdMw σ hσ hnp hsc0 hmin ne03 ne13 ne14
      omega
  have hk1_eq : σ1 k0 = σ w ∧ σ1 k1 = σ k1 ∧ σ1 k2 = σ k2 ∧ σ1 k3 = σ k3 ∧ σ1 k4 = σ k4 :=
    ⟨h1i 0, h1i 1, h1i 2, h1i 3, h1i 4⟩
  have hk2_eq : σ2 k0 = σ w ∧ σ2 k1 = σ k1 ∧ σ2 k2 = σ k0 ∧ σ2 k3 = σ k3 ∧ σ2 k4 = σ k4 :=
    ⟨h2i 0, h2i 1, h2i 2, h2i 3, h2i 4⟩
  have hk3_eq : σ3 k0 = σ w ∧ σ3 k1 = σ k1 ∧ σ3 k2 = σ k2 ∧ σ3 k3 = σ k3 ∧ σ3 k4 = σ k0 :=
    ⟨h3i 0, h3i 1, h3i 2, h3i 3, h3i 4⟩
  refine sum5_erase_Mw_contradiction C G hd k0 k2 k4 w hK_card σ Mw hMw_mem hwK_cnt hK_A hMw_A (fun M hM_er => ?_)
  have hM_ne_Mw : M ≠ Mw := (mem_erase.1 hM_er).1
  have hM_mem : M ∈ (univ.image (compSet C)).erase (compSet C k0) := (mem_erase.1 hM_er).2
  have hne : M ≠ compSet C k0 := (mem_erase.1 hM_mem).1
  have hdM : Disjoint ({k0, k1, k2, k3, k4} : Finset V) M :=
    hK_set ▸ compSet_disjoint C (mem_image_of_mem _ (mem_univ k0)) (mem_of_mem_erase hM_mem) hne.symm
  obtain ⟨v, -, hMv⟩ := mem_image.1 (mem_of_mem_erase hM_mem)
  have hu_out : ∀ u ∈ M, u ∉ ({k0, k1, k2, k3, k4, w} : Finset V) := by
    intro u hu h_in
    simp only [mem_insert, mem_singleton] at h_in
    rcases h_in with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Finset.disjoint_left.1 hdM (by simp) hu
    · exact Finset.disjoint_left.1 hdM (by simp) hu
    · exact Finset.disjoint_left.1 hdM (by simp) hu
    · exact Finset.disjoint_left.1 hdM (by simp) hu
    · exact Finset.disjoint_left.1 hdM (by simp) hu
    · rw [← hMv] at hu; exact hM_ne_Mw (hMv ▸ compSet_eq_of_mem C hu).symm
  have hu1 : ∀ u ∈ M, σ1 u = σ u := fun u hu => h1o u (hu_out u hu)
  have hu2 : ∀ u ∈ M, σ2 u = σ u := fun u hu => h2o u (hu_out u hu)
  have hu3 : ∀ u ∈ M, σ3 u = σ u := fun u hu => h3o u (hu_out u hu)
  rw [← hMv] at hdM hu1 hu2 hu3 ⊢
  rcases compSet_classify C hdeg hnl hshort v with
    ⟨u0, hMeq, hMc⟩ | ⟨u0, u1, u2, hMeq, hMc⟩ |
    ⟨u0, u1, u2, u3, _, hMc⟩ | ⟨u0, u1, u2, u3, u4, hMeq, hMc⟩
  · rw [hMeq] at hdM hu1 hu2 hu3 ⊢; rw [card_singleton]
    exact fminW_1_all C G k0 k1 k2 k3 k4 w u0 hK hMc hdM σ hσ hnp hsc0 hmin nw1 σ1 hσ1 hk1_eq hu1 σ2 hσ2 hk2_eq hu2 σ3 hσ3 hk3_eq hu3 ne03 ne13 ne14
  · rw [hMeq] at hdM hu1 hu2 hu3 ⊢; rw [card_of_isComp3 hMc]
    exact fminW_3 C G k0 k1 k2 k3 k4 w u0 u1 u2 hK hMc hdM σ hσ hnp hsc0 hmin nw1 σ1 hσ1 hk1_eq hu1 σ2 hσ2 hk2_eq hu2 σ3 hσ3 hk3_eq hu3 ne03 ne13 ne14
  · exact False.elim (hno4 u0 u1 u2 u3 hMc)
  · rw [hMeq] at hdM hu1 hu2 hu3 ⊢; rw [card_of_isComp5 hMc]
    exact fminW_5 C G k0 k1 k2 k3 k4 w u0 u1 u2 u3 u4 hK hMc hdM σ hσ hnp hsc0 hmin nw1 σ1 hσ1 hk1_eq hu1 σ2 hσ2 hk2_eq hu2 σ3 hσ3 hk3_eq hu3 ne03 ne13 ne14
private lemma close_e0min {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj]
    (hd : 3 * (G.maxDegree + 1) ≤ Fintype.card V + 1)
    (hno4 : ∀ a0 a1 a2 a3, ¬ IsComp4 C a0 a1 a2 a3)
    (hdeg : ∀ v a b c, C.Adj v a → C.Adj v b → C.Adj v c → a = b ∨ a = c ∨ b = c)
    (hnl : ∀ x y, C.Adj x y → ∃ z, z ≠ y ∧ C.Adj x z)
    (hshort : ∀ v, Set.ncard {u | C.Reachable v u} ≤ 5)
    (k0 k1 k2 k3 k4 : V) (hK : IsComp5 C k0 k1 k2 k3 k4) (σ : Equiv.Perm V)
    (hσ : ∀ a b, C.Adj a b → ¬(a = k4 ∧ b = k0) → ¬(a = k0 ∧ b = k4) → ¬ G.Adj (σ a) (σ b))
    (hσ_rev : ∀ a b, C.Adj a b → ¬(a = k0 ∧ b = k4) → ¬(a = k4 ∧ b = k0) → ¬ G.Adj (σ a) (σ b))
    (hnp : ¬ Packs C G)
    (hsc0 : 7 ≤ kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4))
    (hsc0_rev : 7 ≤ kScore G (σ k4) (σ k3) (σ k2) (σ k1) (σ k0))
    (hmin : ∀ τ : Equiv.Perm V, (∀ a b, C.Adj a b → ¬(a = k4 ∧ b = k0) → ¬(a = k0 ∧ b = k4) → ¬ G.Adj (τ a) (τ b)) → kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4) ≤ kScore G (τ k0) (τ k1) (τ k2) (τ k3) (τ k4))
    (e02 : G.Adj (σ k0) (σ k2)) (ne03 : ¬ G.Adj (σ k0) (σ k3)) (e04 : G.Adj (σ k0) (σ k4))
    (ne13 : ¬ G.Adj (σ k1) (σ k3)) (ne14 : ¬ G.Adj (σ k1) (σ k4)) (e24 : G.Adj (σ k2) (σ k4)) :
    False := by
  have hmin_r : ∀ τ : Equiv.Perm V,
      (∀ a b, C.Adj a b → ¬(a = k0 ∧ b = k4) → ¬(a = k4 ∧ b = k0) → ¬ G.Adj (τ a) (τ b)) →
      kScore G (σ k4) (σ k3) (σ k2) (σ k1) (σ k0) ≤ kScore G (τ k4) (τ k3) (τ k2) (τ k1) (τ k0) := by
    intro τ hτ
    rw [kScore_rev G (σ k0), kScore_rev G (τ k0)]
    exact hmin τ (fun a b hab h1 h2 => hτ a b hab h2 h1)
  have hex_w : ∃ w, w ∉ compSet C k0 ∧ ¬(G.Adj (σ k1) (σ w) ∧ G.Adj (σ k3) (σ w)) ∧
      ∀ b, C.Adj w b → ¬(G.Adj (σ k0) (σ b) ∨ G.Adj (σ k2) (σ b) ∨ G.Adj (σ k4) (σ b)) := by
    by_contra hno_w
    have hall_z : ∀ w, w ∉ compSet C k0 → (G.Adj (σ k1) (σ w) ∧ G.Adj (σ k3) (σ w)) ∨
        ∃ b, C.Adj w b ∧ (G.Adj (σ k0) (σ b) ∨ G.Adj (σ k2) (σ b) ∨ G.Adj (σ k4) (σ b)) := by
      intro w hw_out
      by_contra hnw
      apply hno_w
      refine ⟨w, hw_out, fun h13 => hnw (Or.inl h13), fun b hwb h024 => hnw (Or.inr ⟨b, hwb, h024⟩)⟩
    have hK_deg : 3 * 11 < 9 * rCount G σ k0 (compSet C k0) + 3 * rCount G σ k1 (compSet C k0) +
        9 * rCount G σ k2 (compSet C k0) + 3 * rCount G σ k3 (compSet C k0) +
        9 * rCount G σ k4 (compSet C k0) := by
      simp only [rCount_self5 C G σ hK]
      have := b01_eq_one e02; have := b01_eq_one e02.symm
      have := b01_eq_one e04; have := b01_eq_one e04.symm
      have := b01_eq_one e24; have := b01_eq_one e24.symm; omega
    have hz_mem : ∀ {M : Finset V}, M ∈ (univ.image (compSet C)).erase (compSet C k0) →
        ∀ u ∈ M, (G.Adj (σ k1) (σ u) ∧ G.Adj (σ k3) (σ u)) ∨
          ∃ b, C.Adj u b ∧ (G.Adj (σ k0) (σ b) ∨ G.Adj (σ k2) (σ b) ∨ G.Adj (σ k4) (σ b)) := by
      intro M hMm u huM
      apply hall_z u (fun huk0 => ?_)
      have hd_kM := compSet_disjoint C (mem_image_of_mem _ (mem_univ k0)) (mem_of_mem_erase hMm) (mem_erase.1 hMm).1.symm
      exact Finset.disjoint_left.1 hd_kM huk0 huM
    exact close_sum5_helper C G hd hno4 hdeg hnl hshort k0 k1 k2 k3 k4 hK σ 9 3 9 3 9 11 rfl hK_deg
      (fun u0 hMc hdM hMm => fminZ_1_all C G k0 k1 k2 k3 k4 u0 hK hMc hdM σ hσ hnp hsc0 hmin (hz_mem hMm) ne03 ne13 ne14)
      (fun u0 u1 u2 hMc hdM hMm => fminZ_3 C G k0 k1 k2 k3 k4 u0 u1 u2 hK hMc hdM σ hσ hnp hsc0 hmin (hz_mem hMm) ne03 ne13 ne14)
      (fun u0 u1 u2 u3 u4 hMc hdM hMm => fminZ_5 C G k0 k1 k2 k3 k4 u0 u1 u2 u3 u4 hK hMc hdM σ hσ hnp hsc0 hmin (hz_mem hMm) ne03 ne13 ne14)
  obtain ⟨w, hw_out, hnot13, hwnb⟩ := hex_w
  have hwnb0 : ∀ b, C.Adj w b → ¬ G.Adj (σ k0) (σ b) := fun b hb h => hwnb b hb (Or.inl h)
  have hwnb2 : ∀ b, C.Adj w b → ¬ G.Adj (σ k2) (σ b) := fun b hb h => hwnb b hb (Or.inr (Or.inl h))
  have hwnb4 : ∀ b, C.Adj w b → ¬ G.Adj (σ k4) (σ b) := fun b hb h => hwnb b hb (Or.inr (Or.inr h))
  by_cases nw1 : G.Adj (σ k1) (σ w)
  · have nw3 : ¬ G.Adj (σ k3) (σ w) := fun h3 => hnot13 ⟨nw1, h3⟩
    have hw_out_rev : w ∉ compSet C k4 := by
      rw [compSet_eq_of_isComp5 C hK.revK]; rw [compSet_eq_of_isComp5 C hK] at hw_out
      intro h; apply hw_out; simp only [mem_insert, mem_singleton] at h ⊢; tauto
    exact e0min_with_w C G hd hno4 hdeg hnl hshort k4 k3 k2 k1 k0 w hK.revK σ hσ_rev hnp hsc0_rev hmin_r
      e24.symm (adj_symm_not G ne14) e04.symm (adj_symm_not G ne13) (adj_symm_not G ne03) e02.symm
      hw_out_rev nw3 hwnb4 hwnb2 hwnb0
  · exact e0min_with_w C G hd hno4 hdeg hnl hshort k0 k1 k2 k3 k4 w hK σ hσ hnp hsc0 hmin
      e02 ne03 e04 ne13 ne14 e24 hw_out nw1 hwnb0 hwnb2 hwnb4
set_option maxHeartbeats 1600000 in
private lemma pack_of_no_c4_has_c5 {V : Type} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) [DecidableRel G.Adj]
    (hd : 3 * (G.maxDegree + 1) ≤ Fintype.card V + 1)
    (hno4 : ∀ a0 a1 a2 a3, ¬ IsComp4 C a0 a1 a2 a3)
    (hdeg : ∀ v a b c, C.Adj v a → C.Adj v b → C.Adj v c → a = b ∨ a = c ∨ b = c)
    (hnl : ∀ x y, C.Adj x y → ∃ z, z ≠ y ∧ C.Adj x z)
    (hshort : ∀ v, Set.ncard {u | C.Reachable v u} ≤ 5)
    (hIH : ∀ G' : SimpleGraph V,
      (∀ v a b c, G'.Adj v a → G'.Adj v b → G'.Adj v c → a = b ∨ a = c ∨ b = c) →
      (∀ v, Set.ncard {u | G'.Reachable v u} ≤ 5) →
      Set.ncard {p : V × V | G'.Adj p.1 p.2} < Set.ncard {p : V × V | C.Adj p.1 p.2} →
      Packs G' G)
    {k0 k1 k2 k3 k4 : V} (hK : IsComp5 C k0 k1 k2 k3 k4) : Packs C G := by
  classical
  have hk40 : C.Adj k4 k0 := (hK.2.2.2.2.2.2.2.2.2.2.2.2.2.2 k0).2 (Or.inr rfl)
  obtain ⟨σ0, hσ0⟩ := almost_packing_short C G hdeg hshort hIH k4 k0 hk40
  let Alm (τ : Equiv.Perm V) : Prop :=
    ∀ a b, C.Adj a b → ¬(a = k4 ∧ b = k0) → ¬(a = k0 ∧ b = k4) → ¬ G.Adj (τ a) (τ b)
  obtain ⟨s_min, ⟨σ, hσ, rfl⟩, hmin_s⟩ := wellFounded_lt.has_min
    {s : ℕ | ∃ τ : Equiv.Perm V, Alm τ ∧ kScore G (τ k0) (τ k1) (τ k2) (τ k3) (τ k4) = s}
    ⟨_, σ0, hσ0, rfl⟩
  have hmin : ∀ τ : Equiv.Perm V, Alm τ →
      kScore G (σ k0) (σ k1) (σ k2) (σ k3) (σ k4) ≤ kScore G (τ k0) (τ k1) (τ k2) (τ k3) (τ k4) :=
    fun τ hτ => not_lt.1 (hmin_s _ ⟨τ, hτ, rfl⟩)
  have hσ_rev : ∀ a b, C.Adj a b → ¬(a = k0 ∧ b = k4) → ¬(a = k4 ∧ b = k0) → ¬ G.Adj (σ a) (σ b) :=
    fun a b hab h1 h2 => hσ a b hab h2 h1
  have hmin_rev : ∀ τ : Equiv.Perm V,
      (∀ a b, C.Adj a b → ¬(a = k0 ∧ b = k4) → ¬(a = k4 ∧ b = k0) → ¬ G.Adj (τ a) (τ b)) →
      kScore G (σ k4) (σ k3) (σ k2) (σ k1) (σ k0) ≤ kScore G (τ k4) (τ k3) (τ k2) (τ k1) (τ k0) := by
    intro τ hτ
    rw [kScore_rev G (σ k0), kScore_rev G (τ k0)]
    exact hmin τ (fun a b hab h1 h2 => hτ a b hab h2 h1)
  by_contra hnp
  have e04 : G.Adj (σ k0) (σ k4) := by
    by_contra hn04
    exact hnp (OMA.packs_of_almost C G k4 k0 σ hσ (adj_symm_not G hn04))
  have b04 := b01_eq_one e04; have b40 := b01_eq_one e04.symm
  obtain ⟨c0, c1, c2, c3⟩ := comp5_c_nonadj hK σ hσ
  by_cases e02 : G.Adj (σ k0) (σ k2)
  ·
    by_cases e03 : G.Adj (σ k0) (σ k3)
    ·
      by_cases e13 : G.Adj (σ k1) (σ k3)
      ·
        by_cases e14 : G.Adj (σ k1) (σ k4)
        ·
          by_cases e24 : G.Adj (σ k2) (σ k4)
          ·
              exact close_fredall C G hd hno4 hdeg hnl hshort k0 k1 k2 k3 k4 hK σ hσ hnp (by unfold kScore; have := b01_eq_one e02; have := b01_eq_one e02.symm; have := b01_eq_one e03; have := b01_eq_one e03.symm; have := b01_eq_one e13; have := b01_eq_one e13.symm; have := b01_eq_one e14; have := b01_eq_one e14.symm; have := b01_eq_one e24; have := b01_eq_one e24.symm; have := b01_eq_one (show G.Adj (σ k0) (σ k2) ∧ G.Adj (σ k0) (σ k4) ∧ G.Adj (σ k2) (σ k4) from ⟨e02, e04, e24⟩); omega) hmin
                (by simp only [rCount_self5 C G σ hK]; have := b01_eq_one e02; have := b01_eq_one e02.symm; have := b01_eq_one e03; have := b01_eq_one e03.symm; have := b01_eq_one e13; have := b01_eq_one e13.symm; have := b01_eq_one e14; have := b01_eq_one e14.symm; have := b01_eq_one e24; have := b01_eq_one e24.symm; omega)
          ·
              exact close_fno02 C G hd hno4 hdeg hnl hshort k4 k3 k2 k1 k0 hK.revK σ hσ_rev hnp (adj_symm_not G e24)
                (by simp only [rCount_self5 C G σ hK.revK]; have := b01_eq_one e02; have := b01_eq_one e02.symm; have := b01_eq_one e03; have := b01_eq_one e03.symm; have := b01_eq_one e13; have := b01_eq_one e13.symm; have := b01_eq_one e14; have := b01_eq_one e14.symm; omega)
        ·
          by_cases e24 : G.Adj (σ k2) (σ k4)
          ·
              exact close_fred0313 C G hd hno4 hdeg hnl hshort k0 k1 k2 k3 k4 hK σ hσ hnp (by unfold kScore; have := b01_eq_one e02; have := b01_eq_one e02.symm; have := b01_eq_one e03; have := b01_eq_one e03.symm; have := b01_eq_one e13; have := b01_eq_one e13.symm; have := b01_eq_one e24; have := b01_eq_one e24.symm; have := b01_eq_one (show G.Adj (σ k0) (σ k2) ∧ G.Adj (σ k0) (σ k4) ∧ G.Adj (σ k2) (σ k4) from ⟨e02, e04, e24⟩); omega) hmin e14
                (by simp only [rCount_self5 C G σ hK]; have := b01_eq_one e02; have := b01_eq_one e02.symm; have := b01_eq_one e03; have := b01_eq_one e03.symm; have := b01_eq_one e13; have := b01_eq_one e13.symm; have := b01_eq_one e24; have := b01_eq_one e24.symm; omega)
          ·
              exact close_fno02 C G hd hno4 hdeg hnl hshort k4 k3 k2 k1 k0 hK.revK σ hσ_rev hnp (adj_symm_not G e24)
                (by simp only [rCount_self5 C G σ hK.revK]; have := b01_eq_one e02; have := b01_eq_one e02.symm; have := b01_eq_one e03; have := b01_eq_one e03.symm; have := b01_eq_one e13; have := b01_eq_one e13.symm; omega)
      ·
        by_cases e14 : G.Adj (σ k1) (σ k4)
        ·
          by_cases e24 : G.Adj (σ k2) (σ k4)
          ·
              exact close_fred0314 C G hd hno4 hdeg hnl hshort k0 k1 k2 k3 k4 hK σ hσ hnp (by unfold kScore; have := b01_eq_one e02; have := b01_eq_one e02.symm; have := b01_eq_one e03; have := b01_eq_one e03.symm; have := b01_eq_one e14; have := b01_eq_one e14.symm; have := b01_eq_one e24; have := b01_eq_one e24.symm; have := b01_eq_one (show G.Adj (σ k0) (σ k2) ∧ G.Adj (σ k0) (σ k4) ∧ G.Adj (σ k2) (σ k4) from ⟨e02, e04, e24⟩); omega) hmin e13
                (by simp only [rCount_self5 C G σ hK]; have := b01_eq_one e02; have := b01_eq_one e02.symm; have := b01_eq_one e03; have := b01_eq_one e03.symm; have := b01_eq_one e14; have := b01_eq_one e14.symm; have := b01_eq_one e24; have := b01_eq_one e24.symm; omega)
          ·
              exact close_fno02 C G hd hno4 hdeg hnl hshort k4 k3 k2 k1 k0 hK.revK σ hσ_rev hnp (adj_symm_not G e24)
                (by simp only [rCount_self5 C G σ hK.revK]; have := b01_eq_one e02; have := b01_eq_one e02.symm; have := b01_eq_one e03; have := b01_eq_one e03.symm; have := b01_eq_one e14; have := b01_eq_one e14.symm; omega)
        ·
          by_cases e24 : G.Adj (σ k2) (σ k4)
          ·
              exact close_fred03 C G hd hno4 hdeg hnl hshort k0 k1 k2 k3 k4 hK σ hσ hnp (by unfold kScore; have := b01_eq_one e02; have := b01_eq_one e02.symm; have := b01_eq_one e03; have := b01_eq_one e03.symm; have := b01_eq_one e24; have := b01_eq_one e24.symm; have := b01_eq_one (show G.Adj (σ k0) (σ k2) ∧ G.Adj (σ k0) (σ k4) ∧ G.Adj (σ k2) (σ k4) from ⟨e02, e04, e24⟩); omega) hmin e13 e14
                (by simp only [rCount_self5 C G σ hK]; have := b01_eq_one e02; have := b01_eq_one e02.symm; have := b01_eq_one e03; have := b01_eq_one e03.symm; have := b01_eq_one e24; have := b01_eq_one e24.symm; omega)
          ·
              exact close_fno02 C G hd hno4 hdeg hnl hshort k4 k3 k2 k1 k0 hK.revK σ hσ_rev hnp (adj_symm_not G e24)
                (by simp only [rCount_self5 C G σ hK.revK]; have := b01_eq_one e02; have := b01_eq_one e02.symm; have := b01_eq_one e03; have := b01_eq_one e03.symm; omega)
    ·
      by_cases e13 : G.Adj (σ k1) (σ k3)
      ·
        by_cases e14 : G.Adj (σ k1) (σ k4)
        ·
          by_cases e24 : G.Adj (σ k2) (σ k4)
          ·
              exact close_fred0313 C G hd hno4 hdeg hnl hshort k4 k3 k2 k1 k0 hK.revK σ hσ_rev hnp (by unfold kScore; have := b01_eq_one e02; have := b01_eq_one e02.symm; have := b01_eq_one e13; have := b01_eq_one e13.symm; have := b01_eq_one e14; have := b01_eq_one e14.symm; have := b01_eq_one e24; have := b01_eq_one e24.symm; have := b01_eq_one (show G.Adj (σ k4) (σ k2) ∧ G.Adj (σ k4) (σ k0) ∧ G.Adj (σ k2) (σ k0) from ⟨e24.symm, e04.symm, e02.symm⟩); omega) hmin_rev (adj_symm_not G e03)
                (by simp only [rCount_self5 C G σ hK.revK]; have := b01_eq_one e02; have := b01_eq_one e02.symm; have := b01_eq_one e13; have := b01_eq_one e13.symm; have := b01_eq_one e14; have := b01_eq_one e14.symm; have := b01_eq_one e24; have := b01_eq_one e24.symm; omega)
          ·
              exact hnp (pack5_0 C G k0 k1 k2 k3 k4 hK σ hσ ![0,1,2,4,3] c0 c1 e24 (adj_symm_not G c3) (adj_symm_not G e03))
        ·
          by_cases e24 : G.Adj (σ k2) (σ k4)
          ·
              exact close_fred13 C G hd hno4 hdeg hnl hshort k0 k1 k2 k3 k4 hK σ hσ hnp (by unfold kScore; have := b01_eq_one e02; have := b01_eq_one e02.symm; have := b01_eq_one e13; have := b01_eq_one e13.symm; have := b01_eq_one e24; have := b01_eq_one e24.symm; have := b01_eq_one (show G.Adj (σ k0) (σ k2) ∧ G.Adj (σ k0) (σ k4) ∧ G.Adj (σ k2) (σ k4) from ⟨e02, e04, e24⟩); omega) hmin e03 e14
                (by simp only [rCount_self5 C G σ hK]; have := b01_eq_one e02; have := b01_eq_one e02.symm; have := b01_eq_one e13; have := b01_eq_one e13.symm; have := b01_eq_one e24; have := b01_eq_one e24.symm; omega)
          ·
              exact hnp (pack5_0 C G k0 k1 k2 k3 k4 hK σ hσ ![0,1,2,4,3] c0 c1 e24 (adj_symm_not G c3) (adj_symm_not G e03))
      ·
        by_cases e14 : G.Adj (σ k1) (σ k4)
        ·
          by_cases e24 : G.Adj (σ k2) (σ k4)
          ·
              exact close_fred03 C G hd hno4 hdeg hnl hshort k4 k3 k2 k1 k0 hK.revK σ hσ_rev hnp (by unfold kScore; have := b01_eq_one e02; have := b01_eq_one e02.symm; have := b01_eq_one e14; have := b01_eq_one e14.symm; have := b01_eq_one e24; have := b01_eq_one e24.symm; have := b01_eq_one (show G.Adj (σ k4) (σ k2) ∧ G.Adj (σ k4) (σ k0) ∧ G.Adj (σ k2) (σ k0) from ⟨e24.symm, e04.symm, e02.symm⟩); omega) hmin_rev (adj_symm_not G e13) (adj_symm_not G e03)
                (by simp only [rCount_self5 C G σ hK.revK]; have := b01_eq_one e02; have := b01_eq_one e02.symm; have := b01_eq_one e14; have := b01_eq_one e14.symm; have := b01_eq_one e24; have := b01_eq_one e24.symm; omega)
          ·
              exact hnp (pack5_0 C G k0 k1 k2 k3 k4 hK σ hσ ![0,1,2,4,3] c0 c1 e24 (adj_symm_not G c3) (adj_symm_not G e03))
        ·
          by_cases e24 : G.Adj (σ k2) (σ k4)
          ·
              exact close_e0min C G hd hno4 hdeg hnl hshort k0 k1 k2 k3 k4 hK σ hσ hσ_rev hnp (by unfold kScore; have := b01_eq_one e02; have := b01_eq_one e02.symm; have := b01_eq_one e24; have := b01_eq_one e24.symm; have := b01_eq_one (show G.Adj (σ k0) (σ k2) ∧ G.Adj (σ k0) (σ k4) ∧ G.Adj (σ k2) (σ k4) from ⟨e02, e04, e24⟩); omega) (by unfold kScore; have := b01_eq_one e02; have := b01_eq_one e02.symm; have := b01_eq_one e24; have := b01_eq_one e24.symm; have := b01_eq_one (show G.Adj (σ k4) (σ k2) ∧ G.Adj (σ k4) (σ k0) ∧ G.Adj (σ k2) (σ k0) from ⟨e24.symm, e04.symm, e02.symm⟩); omega) hmin e02 e03 e04 e13 e14 e24
          ·
              exact hnp (pack5_0 C G k0 k1 k2 k3 k4 hK σ hσ ![0,1,2,4,3] c0 c1 e24 (adj_symm_not G c3) (adj_symm_not G e03))
  ·
    by_cases e03 : G.Adj (σ k0) (σ k3)
    ·
      by_cases e13 : G.Adj (σ k1) (σ k3)
      ·
        by_cases e14 : G.Adj (σ k1) (σ k4)
        ·
          by_cases e24 : G.Adj (σ k2) (σ k4)
          ·
              exact close_fno02 C G hd hno4 hdeg hnl hshort k0 k1 k2 k3 k4 hK σ hσ hnp e02
                (by simp only [rCount_self5 C G σ hK]; have := b01_eq_one e03; have := b01_eq_one e03.symm; have := b01_eq_one e13; have := b01_eq_one e13.symm; have := b01_eq_one e14; have := b01_eq_one e14.symm; have := b01_eq_one e24; have := b01_eq_one e24.symm; omega)
          ·
              exact close_fno02 C G hd hno4 hdeg hnl hshort k0 k1 k2 k3 k4 hK σ hσ hnp e02
                (by simp only [rCount_self5 C G σ hK]; have := b01_eq_one e03; have := b01_eq_one e03.symm; have := b01_eq_one e13; have := b01_eq_one e13.symm; have := b01_eq_one e14; have := b01_eq_one e14.symm; omega)
        ·
          by_cases e24 : G.Adj (σ k2) (σ k4)
          ·
              exact hnp (pack5_0 C G k0 k1 k2 k3 k4 hK σ hσ ![0,1,4,3,2] c0 e14 (adj_symm_not G c3) (adj_symm_not G c2) (adj_symm_not G e02))
          ·
              exact hnp (pack5_0 C G k0 k1 k2 k3 k4 hK σ hσ ![0,1,4,3,2] c0 e14 (adj_symm_not G c3) (adj_symm_not G c2) (adj_symm_not G e02))
      ·
        by_cases e14 : G.Adj (σ k1) (σ k4)
        ·
          by_cases e24 : G.Adj (σ k2) (σ k4)
          ·
              exact close_fno02 C G hd hno4 hdeg hnl hshort k0 k1 k2 k3 k4 hK σ hσ hnp e02
                (by simp only [rCount_self5 C G σ hK]; have := b01_eq_one e03; have := b01_eq_one e03.symm; have := b01_eq_one e14; have := b01_eq_one e14.symm; have := b01_eq_one e24; have := b01_eq_one e24.symm; omega)
          ·
              exact hnp (pack5_0 C G k0 k1 k2 k3 k4 hK σ hσ ![0,1,3,4,2] c0 e13 c3 (adj_symm_not G e24) (adj_symm_not G e02))
        ·
          by_cases e24 : G.Adj (σ k2) (σ k4)
          ·
              exact hnp (pack5_0 C G k0 k1 k2 k3 k4 hK σ hσ ![0,1,4,3,2] c0 e14 (adj_symm_not G c3) (adj_symm_not G c2) (adj_symm_not G e02))
          ·
              exact hnp (pack5_0 C G k0 k1 k2 k3 k4 hK σ hσ ![0,1,3,4,2] c0 e13 c3 (adj_symm_not G e24) (adj_symm_not G e02))
    ·
      by_cases e13 : G.Adj (σ k1) (σ k3)
      ·
        by_cases e14 : G.Adj (σ k1) (σ k4)
        ·
          by_cases e24 : G.Adj (σ k2) (σ k4)
          ·
              exact close_fno02 C G hd hno4 hdeg hnl hshort k0 k1 k2 k3 k4 hK σ hσ hnp e02
                (by simp only [rCount_self5 C G σ hK]; have := b01_eq_one e13; have := b01_eq_one e13.symm; have := b01_eq_one e14; have := b01_eq_one e14.symm; have := b01_eq_one e24; have := b01_eq_one e24.symm; omega)
          ·
              exact hnp (pack5_0 C G k0 k1 k2 k3 k4 hK σ hσ ![0,1,2,4,3] c0 c1 e24 (adj_symm_not G c3) (adj_symm_not G e03))
        ·
          by_cases e24 : G.Adj (σ k2) (σ k4)
          ·
              exact hnp (pack5_0 C G k0 k1 k2 k3 k4 hK σ hσ ![0,1,4,3,2] c0 e14 (adj_symm_not G c3) (adj_symm_not G c2) (adj_symm_not G e02))
          ·
              exact hnp (pack5_0 C G k0 k1 k2 k3 k4 hK σ hσ ![0,1,2,4,3] c0 c1 e24 (adj_symm_not G c3) (adj_symm_not G e03))
      ·
        by_cases e14 : G.Adj (σ k1) (σ k4)
        ·
          by_cases e24 : G.Adj (σ k2) (σ k4)
          ·
              exact close_fno02 C G hd hno4 hdeg hnl hshort k0 k1 k2 k3 k4 hK σ hσ hnp e02
                (by simp only [rCount_self5 C G σ hK]; have := b01_eq_one e14; have := b01_eq_one e14.symm; have := b01_eq_one e24; have := b01_eq_one e24.symm; omega)
          ·
              exact hnp (pack5_0 C G k0 k1 k2 k3 k4 hK σ hσ ![0,1,2,4,3] c0 c1 e24 (adj_symm_not G c3) (adj_symm_not G e03))
        ·
          by_cases e24 : G.Adj (σ k2) (σ k4)
          ·
              exact hnp (pack5_0 C G k0 k1 k2 k3 k4 hK σ hσ ![0,1,4,3,2] c0 e14 (adj_symm_not G c3) (adj_symm_not G c2) (adj_symm_not G e02))
          ·
              exact hnp (pack5_0 C G k0 k1 k2 k3 k4 hK σ hσ ![0,1,2,4,3] c0 c1 e24 (adj_symm_not G c3) (adj_symm_not G e03))
lemma pack_short {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hd : 3 * (G.maxDegree + 1) ≤ Fintype.card V + 1)
    (hTri : ∀ C' : SimpleGraph V,
      (∀ v a b c, C'.Adj v a → C'.Adj v b → C'.Adj v c → a = b ∨ a = c ∨ b = c) →
      (∀ x y, C'.Adj x y → ∃ u, C'.Adj x u ∧ C'.Adj y u) →
      Packs C' G) :
    ∀ m : ℕ, ∀ C : SimpleGraph V,
      (∀ v a b c, C.Adj v a → C.Adj v b → C.Adj v c → a = b ∨ a = c ∨ b = c) →
      (∀ v, Set.ncard {u | C.Reachable v u} ≤ 5) →
      Set.ncard {p : V × V | C.Adj p.1 p.2} = m →
      Packs C G := by
  classical
  have hn : 3 * G.maxDegree < Fintype.card V := by omega
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro C hdeg hshort hm
    by_cases hl : ∃ x y, C.Adj x y ∧ ∀ z, C.Adj x z → z = y
    · obtain ⟨x, y, hxy, hleaf⟩ := hl
      let C' : SimpleGraph V :=
        { Adj := fun a b => C.Adj a b ∧ a ≠ x ∧ b ≠ x
          symm := ⟨fun a b h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
          loopless := ⟨fun a h => C.loopless.irrefl a h.1⟩ }
      have hdeg' : ∀ v a b c, C'.Adj v a → C'.Adj v b → C'.Adj v c → a = b ∨ a = c ∨ b = c :=
        fun v a b c ha hb hc => hdeg v a b c ha.1 hb.1 hc.1
      have hshort' := short_of_sub (G' := C') (C := C) (fun _ _ h => h.1) hshort
      have hss : {p : V × V | C'.Adj p.1 p.2} ⊂ {p : V × V | C.Adj p.1 p.2} :=
        (Set.ssubset_iff_of_subset (fun _ hp => hp.1)).2 ⟨(x, y), hxy, fun hp => hp.2.1 rfl⟩
      have hlt : Set.ncard {p : V × V | C'.Adj p.1 p.2} < m := by
        rw [← hm]; exact Set.ncard_lt_ncard hss (Set.toFinite _)
      obtain ⟨σ, hσ⟩ := ih _ hlt C' hdeg' hshort' rfl
      exact OMA.leaf_step C G hdeg hn x y hxy hleaf σ (fun u v huv hux hvx => hσ u v ⟨huv, hux, hvx⟩)
    · have hnl : ∀ x y, C.Adj x y → ∃ z, z ≠ y ∧ C.Adj x z := by
        intro x y hxy; by_contra hno; apply hl
        exact ⟨x, y, hxy, fun z hz => by by_contra hzy; exact hno ⟨z, hzy, hz⟩⟩
      have hIH : ∀ G' : SimpleGraph V,
          (∀ v a b c, G'.Adj v a → G'.Adj v b → G'.Adj v c → a = b ∨ a = c ∨ b = c) →
          (∀ v, Set.ncard {u | G'.Reachable v u} ≤ 5) →
          Set.ncard {p : V × V | G'.Adj p.1 p.2} < Set.ncard {p : V × V | C.Adj p.1 p.2} →
          Packs G' G :=
        fun G' hdeg' hshort' hlt => ih _ (hm ▸ hlt) G' hdeg' hshort' rfl
      by_cases hc4 : ∃ k0 k1 k2 k3, IsComp4 C k0 k1 k2 k3
      · obtain ⟨k0, k1, k2, k3, hK⟩ := hc4
        exact pack_of_has_c4 C G hd hdeg hnl hshort hIH hK
      · have hno4 : ∀ a0 a1 a2 a3, ¬ IsComp4 C a0 a1 a2 a3 :=
          fun a0 a1 a2 a3 h => hc4 ⟨a0, a1, a2, a3, h⟩
        by_cases hc5 : ∃ k0 k1 k2 k3 k4, IsComp5 C k0 k1 k2 k3 k4
        · obtain ⟨k0, k1, k2, k3, k4, hK⟩ := hc5
          exact pack_of_no_c4_has_c5 C G hd hno4 hdeg hnl hshort hIH hK
        · refine hTri C hdeg (fun x y hxy => ?_)
          rcases compSet_classify C hdeg hnl hshort x with
            ⟨u0, hMeq, hMc⟩ | ⟨u0, u1, u2, hMeq, hMc⟩ |
            ⟨u0, u1, u2, u3, _, hMc⟩ | ⟨u0, u1, u2, u3, u4, _, hMc⟩
          · have hx0 : x = u0 := by
              have := self_mem_compSet C x; rw [hMeq, mem_singleton] at this; exact this
            exact absurd (hx0 ▸ hxy) (hMc y)
          · have hxM : x ∈ ({u0, u1, u2} : Finset V) := hMeq ▸ self_mem_compSet C x
            have hyM : y ∈ ({u0, u1, u2} : Finset V) :=
              hMeq ▸ compSet_closed C (self_mem_compSet C x) hxy
            have hxy_ne : x ≠ y := hxy.ne
            rcases hMc with ⟨h01, h02, h12, n0, n1, n2⟩
            simp only [mem_insert, mem_singleton] at hxM hyM
            rcases hxM with rfl | rfl | rfl <;> rcases hyM with rfl | rfl | rfl
            · exact absurd rfl hxy_ne
            · exact ⟨u2, (n0 u2).2 (Or.inl rfl), (n1 u2).2 (Or.inr rfl)⟩
            · exact ⟨u1, (n0 u1).2 (Or.inr rfl), (n2 u1).2 (Or.inl rfl)⟩
            · exact ⟨u2, (n1 u2).2 (Or.inr rfl), (n0 u2).2 (Or.inl rfl)⟩
            · exact absurd rfl hxy_ne
            · exact ⟨u0, (n1 u0).2 (Or.inl rfl), (n2 u0).2 (Or.inr rfl)⟩
            · exact ⟨u1, (n2 u1).2 (Or.inl rfl), (n0 u1).2 (Or.inr rfl)⟩
            · exact ⟨u0, (n2 u0).2 (Or.inr rfl), (n1 u0).2 (Or.inl rfl)⟩
            · exact absurd rfl hxy_ne
          · exact False.elim (hno4 u0 u1 u2 u3 hMc)
          · exact False.elim (hc5 ⟨u0, u1, u2, u3, u4, hMc⟩)
end MainShortCycles
end OMA.ShortCycles

theorem OMA.solution : OMA.R_BollobasEldridgeCatlinConjecture_bollobas_eldridge_catlin_conjecture_variants_maxDegree_le_two_R1_H2_R1.H1 := by
  intro V _ _ C G _ hd _ _ hdeg _ hshort
  exact OMA.ShortCycles.pack_short G hd
    (fun C' hdeg' htri' => OMA.TrianglePack.pack C' G hd hdeg' htri'
      (fun r hr => E914P.HajnalSzemeredi.hajnal_szemeredi G r hr))
    _ C hdeg hshort rfl

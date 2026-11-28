import OMAStatements.S_mo_60011
import Mathlib

/-!
# Trees in groups of exponential growth: free subsemigroups and non-amenable groups

`main` proves the positive answer in two cases and leaves the rest as `H1`, `H2`.

* Free subsemigroup of rank 2 (`of_free`): if the word map `l ↦ (l.map f).prod`,
  `f t = if t then a else b`, is injective on `List Bool`, take `S = S0 ∪ {a, b}` and
  `φ l = ((l.map f).reverse).prod`, so `φ (t :: l) = φ l * f t`.  This covers all linear groups
  of exponential growth (Tits alternative), all solvable ones (Rosenblatt 1974) and all
  elementary amenable ones (Chou 1980).
* Non-amenable groups (`of_nonAmen`): suppose there are a finite `K` and `c > 1` with
  `c * |F| ≤ |F * K|` for every finite `F` (by Følner's criterion this is non-amenability).
  Iterating gives `3 * |F| ≤ |F * K ^ n|`; Hall's marriage theorem (infinite version, in
  Mathlib) gives an injective `h : G × Fin 3 → G` with `h (g, i) ∈ g * K ^ n`; the tree has root
  `h (1, 2)` and children `h (x, 0)`, `h (x, 1)` of `x`.  This covers e.g. the free Burnside
  groups of large odd exponent (non-amenable by Adyan), which have no free subsemigroup.

Remaining: amenable groups of exponential growth without a free subsemigroup of rank 2.
`H1` is the torsion part (torsion groups never contain a free subsemigroup), `H2` the
non-torsion part.
-/

namespace OMA.R_mo_60011_R1

open OMA.S_mo_60011
open scoped Pointwise

theorem ContainsBinaryTree.mono {G : Type} [Group G] {S T : Set G} (hST : S ⊆ T)
    (h : ContainsBinaryTree S) : ContainsBinaryTree T := by
  obtain ⟨φ, hinj, hstep⟩ := h
  refine ⟨φ, hinj, fun b l => ?_⟩
  obtain ⟨s, hs, he⟩ := hstep b l
  exact ⟨s, hs.imp (fun h => hST h) (fun h => hST h), he⟩

theorem tree_of_injective {G : Type} [Group G] (K : Set G) (h : G × Fin 3 → G)
    (hinj : Function.Injective h) (hK : ∀ x, ∃ k ∈ K, h x = x.1 * k) :
    ContainsBinaryTree K := by
  refine ⟨fun l => List.rec (motive := fun _ => G) (h (1, 2))
    (fun b _ r => h (r, if b then 0 else 1)) l, ?_, ?_⟩
  · intro l1
    induction l1 with
    | nil =>
      intro l2 he
      cases l2 with
      | nil => rfl
      | cons b m =>
        exfalso
        have := (Prod.ext_iff.mp (hinj (he.trans rfl : h (1, 2) = _))).2
        cases b <;> simp at this
    | cons b m ih =>
      intro l2 he
      cases l2 with
      | nil =>
        exfalso
        have := (Prod.ext_iff.mp (hinj (he : h _ = h (1, 2)))).2
        cases b <;> simp at this
      | cons b' m' =>
        have h2 := Prod.ext_iff.mp (hinj (he : h _ = h _))
        have hm : m = m' := ih h2.1
        have hb : b = b' := by
          have := h2.2
          cases b <;> cases b' <;> simp_all
        rw [hm, hb]
  · intro b l
    obtain ⟨k, hk, he⟩ := hK (List.rec (motive := fun _ => G) (h (1, 2))
      (fun b _ r => h (r, if b then 0 else 1)) l, if b then 0 else 1)
    exact ⟨k, Or.inl hk, he⟩

/-- Iterating the isoperimetric inequality. -/
theorem iterate_iso {G : Type} [Group G] [DecidableEq G] (K : Finset G) (c : ℝ) (hc : 1 < c)
    (hK : ∀ F : Finset G, c * (F.card : ℝ) ≤ ((F * K).card : ℝ)) (n : ℕ) (F : Finset G) :
    c ^ n * (F.card : ℝ) ≤ ((F * K ^ n).card : ℝ) := by
  induction n generalizing F with
  | zero => simp
  | succ n ih =>
    rw [show F * K ^ (n + 1) = (F * K ^ n) * K by rw [pow_succ, mul_assoc]]
    calc c ^ (n + 1) * (F.card : ℝ) = c * (c ^ n * F.card) := by ring
      _ ≤ c * ((F * K ^ n).card : ℝ) := by
          exact mul_le_mul_of_nonneg_left (ih F) (by linarith)
      _ ≤ _ := hK _

/-- Non-amenable groups: a binary tree for a finite set. -/
theorem tree_of_nonAmen {G : Type} [Group G] [DecidableEq G] (hG : (∃ K : Finset G, ∃ c : ℝ, 1 < c ∧ ∀ F : Finset G, c * (F.card : ℝ) ≤ ((F * K).card : ℝ))) :
    ∃ K : Finset G, ContainsBinaryTree (K : Set G) := by
  obtain ⟨K, c, hc, hK⟩ := hG
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (3 : ℝ) hc
  set L := K ^ n with hL
  have h3 : ∀ F : Finset G, 3 * F.card ≤ (F * L).card := by
    intro F
    have := iterate_iso K c hc hK n F
    have h0 : (0 : ℝ) ≤ F.card := Nat.cast_nonneg _
    have : (3 : ℝ) * F.card ≤ ((F * L).card : ℝ) := by nlinarith
    exact_mod_cast this
  set t : G × Fin 3 → Finset G := fun x => {x.1} * L with ht
  have hall : ∀ s : Finset (G × Fin 3), s.card ≤ (s.biUnion t).card := by
    intro s
    set F := s.image Prod.fst with hF
    have hs : s ⊆ F ×ˢ (Finset.univ : Finset (Fin 3)) := by
      intro x hx
      simp only [Finset.mem_product, Finset.mem_univ, and_true, hF]
      exact Finset.mem_image_of_mem _ hx
    have hsub : F * L ⊆ s.biUnion t := by
      intro y hy
      obtain ⟨g, hg, k, hk, rfl⟩ := Finset.mem_mul.mp hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
      exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_mul.mpr ⟨x.1, by simp, k, hk, rfl⟩⟩
    calc s.card ≤ (F ×ˢ (Finset.univ : Finset (Fin 3))).card := Finset.card_le_card hs
      _ = 3 * F.card := by simp [Finset.card_product, mul_comm]
      _ ≤ (F * L).card := h3 F
      _ ≤ _ := Finset.card_le_card hsub
  obtain ⟨h, hinj, hmem⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hall
  refine ⟨L, tree_of_injective _ h hinj fun x => ?_⟩
  obtain ⟨g, hg, k, hk, he⟩ := Finset.mem_mul.mp (hmem x)
  rw [Finset.mem_singleton] at hg
  subst hg
  exact ⟨k, hk, he.symm⟩

/-- Adding a finite set to a generating set. -/
theorem of_finite_tree {G : Type} [Group G] [DecidableEq G] (hfg : Group.FG G) (K : Finset G)
    (hK : ContainsBinaryTree (K : Set G)) :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧ ContainsBinaryTree (S : Set G) := by
  obtain ⟨S0, hS0⟩ := hfg.out
  refine ⟨S0 ∪ K, ?_, ContainsBinaryTree.mono (by intro x hx; simp [hx]) hK⟩
  rw [eq_top_iff, ← hS0]
  exact Subgroup.closure_mono (by intro x hx; simp [hx])

/-- The positive answer holds for every finitely generated non-amenable group. -/
theorem of_nonAmen {G : Type} [Group G] [DecidableEq G] (hfg : Group.FG G) (hG : (∃ K : Finset G, ∃ c : ℝ, 1 < c ∧ ∀ F : Finset G, c * (F.card : ℝ) ≤ ((F * K).card : ℝ))) :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧ ContainsBinaryTree (S : Set G) := by
  obtain ⟨K, hK⟩ := tree_of_nonAmen hG
  exact of_finite_tree hfg K hK

/-- A free subsemigroup of rank 2 gives a binary tree. -/
theorem of_free {G : Type} [Group G] (hfg : Group.FG G) (a b : G)
    (hinj : Function.Injective
      (fun l : List Bool => (l.map (fun t => if t then a else b)).prod)) :
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧ ContainsBinaryTree (S : Set G) := by
  classical
  obtain ⟨S0, hS0⟩ := hfg.out
  set f : Bool → G := fun t => if t then a else b with hf
  refine ⟨insert a (insert b S0), ?_, ?_⟩
  · rw [eq_top_iff, ← hS0]
    apply Subgroup.closure_mono
    intro x hx
    simp [hx]
  · refine ⟨fun l => ((l.map f).reverse).prod, ?_, ?_⟩
    · intro l1 l2 h
      have h' : (l1.reverse.map f).prod = (l2.reverse.map f).prod := by
        simpa [List.map_reverse] using h
      exact List.reverse_injective (hinj h')
    · intro t l
      refine ⟨f t, Or.inl ?_, ?_⟩
      · cases t <;> simp [hf]
      · simp [List.prod_append]

/-- Remaining case 1: torsion groups of exponential growth that are amenable, i.e. fail the
strong isoperimetric inequality (torsion groups never contain a free subsemigroup). -/
def H1 : Prop :=
  ∀ (G : Type) [Group G] [DecidableEq G], Group.FG G → ExponentialGrowth G → IsMulTorsion G →
    ¬ (∃ K : Finset G, ∃ c : ℝ, 1 < c ∧ ∀ F : Finset G, c * (F.card : ℝ) ≤ ((F * K).card : ℝ)) →
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧ ContainsBinaryTree (S : Set G)

/-- Remaining case 2: amenable non-torsion groups of exponential growth without a free
subsemigroup of rank 2. -/
def H2 : Prop :=
  ∀ (G : Type) [Group G] [DecidableEq G], Group.FG G → ExponentialGrowth G → ¬ IsMulTorsion G →
    ¬ (∃ K : Finset G, ∃ c : ℝ, 1 < c ∧ ∀ F : Finset G, c * (F.card : ℝ) ≤ ((F * K).card : ℝ)) →
    (¬ ∃ a b : G, Function.Injective
        (fun l : List Bool => (l.map (fun t => if t then a else b)).prod)) →
    ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤ ∧ ContainsBinaryTree (S : Set G)

theorem main : H1 → H2 → type_of% @OMA.S_mo_60011.main := by
  intro h1 h2 G _ hfg hexp
  classical
  by_cases hN : (∃ K : Finset G, ∃ c : ℝ, 1 < c ∧ ∀ F : Finset G, c * (F.card : ℝ) ≤ ((F * K).card : ℝ))
  · exact of_nonAmen hfg hN
  · by_cases ht : IsMulTorsion G
    · exact h1 G hfg hexp ht hN
    · by_cases hF : ∃ a b : G, Function.Injective
          (fun l : List Bool => (l.map (fun t => if t then a else b)).prod)
      · obtain ⟨a, b, hinj⟩ := hF
        exact of_free hfg a b hinj
      · exact h2 G hfg hexp ht hN hF

end OMA.R_mo_60011_R1

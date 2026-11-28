import FormalConjectures.Wikipedia.SumnerUniversalTournamentConjecture
import Mathlib

/-! Oriented stars embed by counting arcs in induced subtournaments.
The remaining proof separates bounded-degree trees from the high-degree
non-stars. -/
open Finset Digraph
open scoped BigOperators
namespace SumnerStars

theorem ordered_arc_count {V : Type*} [DecidableEq V] (R : V → V → Prop) [DecidableRel R]
    (irr : ∀ v, ¬ R v v) (orientation : ∀ u v, u ≠ v → (R u v ↔ ¬ R v u))
    (A : Finset V) :
    A.card*(A.card-1) = 2*(∑ a ∈ A, (A.filter (R a)).card) := by
  classical
  let F := (A ×ˢ A).filter (fun p : V × V ↦ R p.1 p.2)
  let B := (A ×ˢ A).filter (fun p : V × V ↦ R p.2 p.1)
  have disjoint : Disjoint F B := by
    apply disjoint_left.mpr
    rintro ⟨u,v⟩ hF hB
    have f := (mem_filter.mp hF).2
    have b := (mem_filter.mp hB).2
    have ne : u ≠ v := fun h ↦ irr u (h ▸ f)
    exact (orientation u v ne).mp f b
  have cover : F ∪ B = A.offDiag := by
    ext p
    rcases p with ⟨u,v⟩
    simp only [F,B,mem_union,mem_filter,mem_product,mem_offDiag]
    constructor
    · rintro (⟨⟨hu,hv⟩,h⟩|⟨⟨hu,hv⟩,h⟩)
      · exact ⟨hu,hv,fun e ↦ irr u (e ▸ h)⟩
      · exact ⟨hu,hv,fun e ↦ irr v (e ▸ h)⟩
    · rintro ⟨hu,hv,ne⟩
      by_cases h : R v u
      · exact Or.inr ⟨⟨hu,hv⟩,h⟩
      · exact Or.inl ⟨⟨hu,hv⟩,(orientation u v ne).mpr h⟩
  have flip : B.card = F.card := by
    apply card_bij' (fun p _ ↦ p.swap) (fun p _ ↦ p.swap)
    · intro p _
      exact Prod.swap_swap p
    · intro p _
      exact Prod.swap_swap p
    · rintro ⟨u,v⟩ h
      simpa [B,F,and_comm, and_left_comm, and_assoc] using h
    · rintro ⟨u,v⟩ h
      simpa [B,F,and_comm, and_left_comm, and_assoc] using h
  have rows : ∀ a ∈ A, (F.filter (fun p ↦ p.1 = a)).card = (A.filter (R a)).card := by
    intro a ha
    symm
    apply card_bij (fun v _ ↦ (a,v))
    · intro v hv
      obtain ⟨hv,hav⟩ := mem_filter.mp hv
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨ha,hv⟩,hav⟩,rfl⟩
    · intro u hu v hv e
      exact congrArg Prod.snd e
    · rintro ⟨u,v⟩ h
      obtain ⟨h,e⟩ := mem_filter.mp h
      change u=a at e
      subst u
      obtain ⟨pair,hav⟩ := mem_filter.mp h
      exact ⟨v,mem_filter.mpr ⟨(mem_product.mp pair).2,hav⟩,rfl⟩
  have count : F.card = ∑ a ∈ A, (A.filter (R a)).card := by
    rw [card_eq_sum_card_fiberwise (f:=Prod.fst) (t:=A)
      (fun p hp ↦ (mem_product.mp (mem_filter.mp hp).1).1)]
    exact sum_congr rfl rows
  have half := card_union_of_disjoint disjoint
  rw [cover,offDiag_card,← Nat.mul_sub_one,flip,count] at half
  omega

theorem small_side {V : Type*} [DecidableEq V] (R : V → V → Prop) [DecidableRel R]
    (irr : ∀ v, ¬ R v v) (orientation : ∀ u v, u ≠ v → (R u v ↔ ¬ R v u))
    (A : Finset V) (k : ℕ) (limit : ∀ a∈A, (A.filter (R a)).card < k) :
    A.card ≤ 2*k ∧ (A.Nonempty → A.card < 2*k) := by
  have strict (hA : A.Nonempty) : A.card < 2*k := by
    have hp := card_pos.mpr hA
    obtain ⟨a,ha⟩ := hA
    have hk : 0 < k := (Nat.zero_le _).trans_lt (limit a ha)
    have rowBound (v : V) (hv : v ∈ A) : (A.filter (R v)).card ≤ k-1 := by
      have := limit v hv
      omega
    have hsum : (∑ v ∈ A, (A.filter (R v)).card) ≤ A.card*(k-1) := by
      simpa only [sum_const,smul_eq_mul] using sum_le_sum rowBound
    have hdiv : A.card*(A.card-1) ≤ A.card*(2*(k-1)) := calc
      _ = 2*(∑ v ∈ A, (A.filter (R v)).card) := ordered_arc_count R irr orientation A
      _ ≤ 2*(A.card*(k-1)) := Nat.mul_le_mul_left 2 hsum
      _ = _ := by ring
    have h := Nat.le_of_mul_le_mul_left hdiv hp
    omega
  refine ⟨?_,strict⟩
  by_cases hA : A.Nonempty
  · exact (strict hA).le
  · simp [not_nonempty_iff_eq_empty.mp hA]

theorem center {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V)
    [DecidableRel G.Adj] (tour : G.IsTournament) (k l : ℕ)
    (hpos : 0 < Fintype.card V) (hn : 2*(k+l) ≤ Fintype.card V) :
    ∃ v : V, k ≤ ((univ : Finset V).filter (G.Adj v)).card ∧
      l ≤ ((univ : Finset V).filter (fun w ↦ G.Adj w v)).card := by
  classical
  let out (v : V) := ((univ : Finset V).filter (G.Adj v)).card
  let inn (v : V) := ((univ : Finset V).filter (fun w ↦ G.Adj w v)).card
  by_contra absent
  let L := (univ : Finset V).filter (fun v ↦ out v < k)
  let M := (univ : Finset V) \ L
  have lo (v : V) (hv : v ∈ L) : (L.filter (G.Adj v)).card < k :=
    (card_le_card (filter_subset_filter _ (subset_univ L))).trans_lt (mem_filter.mp hv).2
  have hi (v : V) (hv : v ∈ M) : (M.filter (fun w ↦ G.Adj w v)).card < l := by
    have hlo : k ≤ out v := by
      by_contra! h
      exact (mem_sdiff.mp hv).2 (mem_filter.mpr ⟨mem_univ _,h⟩)
    have hhi : inn v < l := by
      by_contra! h
      exact absent ⟨v,hlo,h⟩
    exact (card_le_card (filter_subset_filter _ (subset_univ M))).trans_lt hhi
  have lb := small_side G.Adj tour.1 tour.2 L k lo
  have hb := small_side (fun a b ↦ G.Adj b a) tour.1 (fun a b ne ↦ tour.2 b a ne.symm) M l hi
  have total : L.card + M.card = Fintype.card V := by
    dsimp [M]
    rw [card_sdiff_of_subset (subset_univ L),card_univ]
    have := card_le_univ L
    omega
  by_cases hl : L.Nonempty
  · have := lb.2 hl
    omega
  · have hz : L.card=0 := by simp [not_nonempty_iff_eq_empty.mp hl]
    have hm : M.Nonempty := card_pos.mp (by omega)
    have := hb.2 hm
    omega

end SumnerStars

/- The image of each leaf is selected independently inside the appropriate
neighbourhood of one tournament vertex. -/
open Finset Digraph SumnerUniversalTournamentConjecture
namespace SumnerStars

theorem embeds_star {W V : Type} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
    (D : Digraph W) [DecidableRel D.Adj] (G : Digraph V) [DecidableRel G.Adj]
    (tree : IsOrientedTree D) (tour : G.IsTournament)
    (x : W) (star : ∀ u v, D.Adj u v → u = x ∨ v = x)
    (hW : 2 ≤ Fintype.card W) (hV : Fintype.card V = 2 * Fintype.card W - 2) :
    Embeds D G := by
  classical
  obtain ⟨T, _, orient⟩ := tree
  have irr (w : W) : ¬ D.Adj w w := fun h ↦ T.loopless.irrefl w (orient.1 w w h)
  have asym (u v : W) (h : D.Adj u v) : ¬ D.Adj v u :=
    (orient.2 u v (orient.1 u v h)).mp h
  let above := (univ : Finset W).filter (D.Adj x)
  let leaves := (univ : Finset W).erase x
  let below := leaves \ above
  have asub : above ⊆ leaves := by
    intro w hw
    have adj := (mem_filter.mp hw).2
    refine mem_erase.mpr ⟨?_, mem_univ w⟩
    intro e
    exact irr x (e ▸ adj)
  have total : above.card + below.card = Fintype.card W - 1 := by
    have face : leaves.card = Fintype.card W - 1 := by
      simp [leaves, card_erase_of_mem (mem_univ x)]
    have h := card_le_card asub
    dsimp [below]
    rw [card_sdiff_of_subset asub]
    omega
  obtain ⟨c, hcOut, hcIn⟩ := center G tour above.card below.card (by omega) (by omega)
  let out := (univ : Finset V).filter (G.Adj c)
  let inn := (univ : Finset V).filter (fun v ↦ G.Adj v c)
  obtain ⟨embOut⟩ : Nonempty (above ↪ out) :=
    Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_coe] using hcOut)
  obtain ⟨embIn⟩ : Nonempty (below ↪ inn) :=
    Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_coe] using hcIn)
  have memBelow {v : W} (hne : v ≠ x) (h : v ∉ above) : v ∈ below :=
    mem_sdiff.mpr ⟨mem_erase.mpr ⟨hne,mem_univ v⟩,h⟩
  let f (v : W) : V :=
    if hc : v = x then c
    else if ha : v ∈ above then (embOut ⟨v,ha⟩).val
    else (embIn ⟨v,memBelow hc ha⟩).val
  have fCenter : f x = c := dif_pos rfl
  have fOut {v : W} (hv : v ∈ above) : f v = (embOut ⟨v,hv⟩).val := by
    have ne := (mem_erase.mp (asub hv)).1
    simp only [f,dif_neg ne,dif_pos hv]
  have fIn {v : W} (hv : v ∈ below) : f v = (embIn ⟨v,hv⟩).val := by
    have ne := (mem_erase.mp (mem_sdiff.mp hv).1).1
    have hn := (mem_sdiff.mp hv).2
    simp only [f,dif_neg ne,dif_neg hn]
  have outAdj {v : W} (hv : v ∈ above) : G.Adj c (f v) := by
    rw [fOut hv]
    exact (mem_filter.mp (embOut ⟨v,hv⟩).property).2
  have inAdj {v : W} (hv : v ∈ below) : G.Adj (f v) c := by
    rw [fIn hv]
    exact (mem_filter.mp (embIn ⟨v,hv⟩).property).2
  have centerOnly {v : W} (h : f v = c) : v = x := by
    by_contra hn
    by_cases ha : v ∈ above
    · exact tour.1 c (h ▸ outAdj ha)
    · exact tour.1 c (h ▸ inAdj (memBelow hn ha))
  have noOut {v : W} (hv : v ∈ below) : ¬ G.Adj c (f v) := by
    have ne : c ≠ f v := fun h ↦ tour.1 c (h.symm ▸ inAdj hv)
    intro he
    exact (tour.2 c (f v) ne).mp he (inAdj hv)
  refine ⟨⟨f, ?_⟩, ?_⟩
  · intro u v huv
    change G.Adj (f u) (f v)
    rcases star u v huv with hu | hv
    · rw [hu, fCenter]
      have adj : D.Adj x v := hu ▸ huv
      exact outAdj (mem_filter.mpr ⟨mem_univ v,adj⟩)
    · rw [hv, fCenter]
      have adj : D.Adj u x := hv ▸ huv
      have ne : u ≠ x := fun h ↦ irr x (h ▸ adj)
      have na : u ∉ above := fun h ↦ asym u x adj (mem_filter.mp h).2
      exact inAdj (memBelow ne na)
  · intro u v eq
    change f u = f v at eq
    by_cases hu : u = x
    · subst u
      exact (centerOnly (eq.symm.trans fCenter)).symm
    by_cases hv : v = x
    · subst v
      exact centerOnly (eq.trans fCenter)
    by_cases au : u ∈ above
    · by_cases av : v ∈ above
      · rw [fOut au, fOut av] at eq
        exact congrArg Subtype.val (embOut.injective (Subtype.ext eq))
      · exact (noOut (memBelow hv av) (eq ▸ outAdj au)).elim
    · by_cases av : v ∈ above
      · exact (noOut (memBelow hu au) (eq.symm ▸ outAdj av)).elim
      · let bu := memBelow hu au
        let bv := memBelow hv av
        rw [fIn bu, fIn bv] at eq
        exact congrArg Subtype.val (embIn.injective (Subtype.ext eq))

end SumnerStars

open SumnerUniversalTournamentConjecture Digraph
namespace OMA.R_SumnerUniversalTournamentConjecture_sumner_conjecture_variants_large_n_R1

/-- The bounded-degree part of the approximate theorem of Kühn, Mycroft and Osthus. -/
def H1 : Prop := ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
  ∀ {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj],
    Fintype.card W = n → IsOrientedTree D →
    (∀ x : W, {w | D.Adj x w ∨ D.Adj w x}.ncard ≤ 3) →
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj],
      Fintype.card V = 2*n-2 → G.IsTournament → Embeds D G

/-- The remaining trees have a vertex of degree above three and arcs off every star. -/
def H2 : Prop := ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
  ∀ {W : Type} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj],
    Fintype.card W = n → IsOrientedTree D →
    (¬ ∃ c : W, ∀ u v, D.Adj u v → u=c ∨ v=c) →
    (∃ x : W, 3 < {w | D.Adj x w ∨ D.Adj w x}.ncard) →
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj],
      Fintype.card V = 2*n-2 → G.IsTournament → Embeds D G

theorem main : H1 → H2 →
    type_of% @SumnerUniversalTournamentConjecture.sumner_conjecture.variants.large_n := by
  intro small general
  obtain ⟨N₁,small⟩ := small
  obtain ⟨N₂,general⟩ := general
  refine ⟨max 2 (max N₁ N₂),?_⟩
  intro n hn W _ _ D _ hW tree V _ _ G _ hV tour
  have h₂ : 2 ≤ n := (le_max_left _ _).trans hn
  have hn₁ : N₁ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn₂ : N₂ ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  by_cases hs : ∃ c : W, ∀ u v, D.Adj u v → u=c ∨ v=c
  · obtain ⟨x, hx⟩ := hs
    apply SumnerStars.embeds_star D G tree tour x hx
    · simpa only [hW] using h₂
    · simpa only [hW] using hV
  · by_cases hd : ∀ x : W, {w | D.Adj x w ∨ D.Adj w x}.ncard ≤ 3
    · exact small n hn₁ D hW tree hd G hV tour
    · push Not at hd
      exact general n hn₂ D hW tree hs hd G hV tour

end OMA.R_SumnerUniversalTournamentConjecture_sumner_conjecture_variants_large_n_R1

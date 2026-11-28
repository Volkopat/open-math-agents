import OMAReductions.R_Erdos19_erdos_19_variants_large_n_R1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.ModEq
import Mathlib.Logic.Equiv.Basic
import Mathlib.Order.Fin.Basic

/-!
For a pairwise balanced design, call its blocks of size at least three the
large blocks. It suffices to color two kinds of designs. In the first, one
large block meets at least three other large blocks. In the second, every
large block meets at most two others, but some nonempty subfamily has no
vertex of degree less than two. In that subfamily every component is a cycle.

The path ordering and its consecutive labeling extend the endpoint-sum
coloring from the project's reduction Erdos19.erdos_19.R1 (PR #1479) by @zarnab222-dev, which treats a common
interval order and constructs such an order for at most two large blocks.
The small-rank design formulation is the H1 of @mucoucah's large-n reduction.

For a published theorem implying the linear-forest coloring case, see
B. Jackson, G. Sethuraman and C. Whitehead,
Discrete Mathematics 307 (2007), 911–915, https://doi.org/10.1016/j.disc.2005.11.053.
-/

namespace Erdos19ForestOrder

open Finset

private theorem degree_mono {α : Type*} [DecidableEq α] {T S : Finset (Finset α)}
    (hTS : T ⊆ S) (u : Finset α) :
    ((T.erase u).filter fun v => (u ∩ v).Nonempty).card ≤
    ((S.erase u).filter fun v => (u ∩ v).Nonempty).card := by
  exact card_le_card (filter_subset_filter _ (erase_subset_erase _ hTS))

private theorem from_leaf {α : Type*} [DecidableEq α] (S : Finset (Finset α)) :
    (∀ u ∈ S, ((S.erase u).filter fun v => (u ∩ v).Nonempty).card ≤ 2) →
    (∀ T ⊆ S, T.Nonempty → ∃ u ∈ T,
      ((T.erase u).filter fun v => (u ∩ v).Nonempty).card ≤ 1) →
    ∀ x ∈ S, ((S.erase x).filter fun v => (x ∩ v).Nonempty).card ≤ 1 →
    ∃ L : List (Finset α), (x :: L).Nodup ∧ (x :: L).toFinset = S ∧
      ∀ (p : List (Finset α)) (u : Finset α) (t : List (Finset α)),
        x :: L = p ++ u :: t → ∀ v ∈ t.tail, Disjoint u v := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro hmax hleaf x hx hxdeg
    let T := S.erase x
    have hTS : T ⊆ S := erase_subset _ _
    have hxT : x ∉ T := notMem_erase _ _
    by_cases hne : T.Nonempty
    · have choose_next : ∃ y ∈ T,
          ((T.erase y).filter fun v => (y ∩ v).Nonempty).card ≤ 1 ∧
          ∀ z ∈ T, (x ∩ z).Nonempty → z = y := by
        by_cases hn : ∃ y ∈ T, (x ∩ y).Nonempty
        · obtain ⟨y, hy, hxy⟩ := hn
          refine ⟨y, hy, ?_, ?_⟩
          · let N := (T.erase y).filter fun v => (y ∩ v).Nonempty
            have hxn : x ∉ N := fun h => hxT (mem_of_mem_erase (mem_filter.mp h).1)
            have hxs : x ∈ (S.erase y).filter fun v => (y ∩ v).Nonempty := by
              exact mem_filter.mpr ⟨mem_erase.mpr ⟨(ne_of_mem_erase hy).symm, hx⟩,
                by simpa [inter_comm] using hxy⟩
            have hsub : insert x N ⊆ (S.erase y).filter fun v => (y ∩ v).Nonempty :=
              insert_subset hxs (filter_subset_filter _ (erase_subset_erase _ hTS))
            have hj := (card_le_card hsub).trans (hmax y (hTS hy))
            rw [card_insert_of_notMem hxn] at hj
            change N.card ≤ 1
            omega
          · intro z hz hxz
            exact card_le_one.mp hxdeg z (mem_filter.mpr ⟨hz, hxz⟩)
              y (mem_filter.mpr ⟨hy, hxy⟩)
        · obtain ⟨y, hy, hd⟩ := hleaf T hTS hne
          exact ⟨y, hy, hd, fun z hz h => (hn ⟨z, hz, h⟩).elim⟩
      obtain ⟨y, hy, hd, huniq⟩ := choose_next
      obtain ⟨L, hn, hL, hf⟩ := ih T (erase_ssubset hx)
        (fun u hu => (degree_mono hTS u).trans (hmax u (hTS hu)))
        (fun U hU => hleaf U (Subset.trans hU hTS)) y hy hd
      have hxL : x ∉ y :: L := by
        intro hg
        exact hxT (hL ▸ List.mem_toFinset.mpr hg)
      refine ⟨y :: L, List.nodup_cons.mpr ⟨hxL, hn⟩, ?_, ?_⟩
      · rw [List.toFinset_cons, hL, insert_erase hx]
      · intro p u t he
        cases p with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          intro z hz
          apply disjoint_iff_inter_eq_empty.mpr
          by_contra h
          have hzT : z ∈ T := hL ▸ List.mem_toFinset.mpr (List.mem_cons_of_mem _ hz)
          have hzy := huniq z hzT (nonempty_iff_ne_empty.mpr h)
          exact (List.nodup_cons.mp hn).1 (hzy ▸ hz)
        | cons a p => exact hf p u t (List.cons.inj he).2
    · have hT : T = ∅ := not_nonempty_iff_eq_empty.mp hne
      refine ⟨[], by simp, ?_, ?_⟩
      · rw [← insert_erase hx, show S.erase x = ∅ from hT]
        simp
      · intro p u t he
        have hlen := congrArg List.length he
        simp at hlen
        have ht : t = [] := List.length_eq_zero_iff.mp (by omega)
        simp [ht]

theorem path_forest_order {α : Type*} [DecidableEq α] (S : Finset (Finset α))
    (hmax : ∀ u ∈ S, ((S.erase u).filter fun v => (u ∩ v).Nonempty).card ≤ 2)
    (hleaf : ∀ T ⊆ S, T.Nonempty → ∃ u ∈ T,
      ((T.erase u).filter fun v => (u ∩ v).Nonempty).card ≤ 1) :
    ∃ L : List (Finset α), L.Nodup ∧ L.toFinset = S ∧
      ∀ (p : List (Finset α)) (u : Finset α) (t : List (Finset α)),
        L = p ++ u :: t → ∀ v ∈ t.tail, Disjoint u v := by
  classical
  by_cases hn : S.Nonempty
  · obtain ⟨x, hx, hd⟩ := hleaf S (Subset.rfl) hn
    obtain ⟨L, hL⟩ := from_leaf S hmax hleaf x hx hd
    exact ⟨x :: L, hL⟩
  · refine ⟨[], by simp, ?_, ?_⟩
    · simp [not_nonempty_iff_eq_empty.mp hn]
    · intro p u t h
      have := congrArg List.length h
      simp at this

end Erdos19ForestOrder

namespace DisjointBlockColoring

/-- Enumerate D by consecutive labels, assigning zero to the designated
singleton when it is present. -/
theorem pinnedBin {α : Type*} [DecidableEq α] (D P : Finset α)
    (hP : P ⊆ D) (hcard : P.card ≤ 1) :
    ∃ g : α → ℕ, (∀ x ∈ D, g x < D.card) ∧
      (∀ x ∈ D, ∀ y ∈ D, g x = g y → x = y) ∧ ∀ x ∈ P, g x = 0 := by
  classical
  have hex : ∃ e : D ≃ Fin D.card, ∀ x (hx : x ∈ P), (e ⟨x,hP hx⟩).val = 0 := by
    by_cases hne : P.Nonempty
    · obtain ⟨z,hz⟩ := hne
      have hd : 0 < D.card := Finset.card_pos.mpr ⟨z,hP hz⟩
      let i := D.equivFin ⟨z,hP hz⟩
      let e := D.equivFin.trans (Equiv.swap i (⟨0,hd⟩ : Fin D.card))
      refine ⟨e,?_⟩
      intro x hx
      have hxz : x = z := Finset.card_le_one_iff.mp hcard hx hz
      subst x
      exact congrArg Fin.val (Equiv.swap_apply_left i (⟨0,hd⟩ : Fin D.card))
    · exact ⟨D.equivFin,fun x hx => (hne ⟨x,hx⟩).elim⟩
  obtain ⟨e,he⟩ := hex
  let g (x : α) := if hx : x ∈ D then (e ⟨x,hx⟩).val else 0
  refine ⟨g,?_,?_,?_⟩
  · intro x hx
    simp [g,hx]
  · intro x hx y hy hxy
    have hv : (e ⟨x,hx⟩).val = (e ⟨y,hy⟩).val := by simpa [g,hx,hy] using hxy
    exact congrArg Subtype.val (e.injective (Fin.ext hv))
  · intro x hx
    simpa [g,hP hx] using he x hx


end DisjointBlockColoring

namespace DisjointBlockColoring

/-- An initial labeling of a block and a shifted labeling of its complement
give an injective labeling of the whole finite set. -/
theorem prependBin {α : Type*} [DecidableEq α] (U D : Finset α) (hD : D ⊆ U)
    (g f : α → ℕ) (hgb : ∀ x ∈ D, g x < D.card)
    (hgi : ∀ x ∈ D, ∀ y ∈ D, g x = g y → x = y)
    (hfb : ∀ x ∈ U \ D, f x < (U \ D).card)
    (hfi : ∀ x ∈ U \ D, ∀ y ∈ U \ D, f x = f y → x = y) :
    let w := fun x => if x ∈ D then g x else D.card + f x
    (∀ x ∈ U, w x < U.card) ∧ (∀ x ∈ U, ∀ y ∈ U, w x = w y → x = y) := by
  dsimp only
  constructor
  · intro x hx
    by_cases hd : x ∈ D
    · simpa only [if_pos hd] using (hgb x hd).trans_le (Finset.card_le_card hD)
    · rw [if_neg hd]
      have := hfb x (Finset.mem_sdiff.mpr ⟨hx, hd⟩)
      have := Finset.card_sdiff_add_card_eq_card hD
      omega
  · intro x hx y hy heq
    by_cases hdx : x ∈ D <;> by_cases hdy : y ∈ D
    · exact hgi x hdx y hdy (by simpa only [if_pos hdx, if_pos hdy] using heq)
    · simp only [if_pos hdx, if_neg hdy] at heq
      have := hgb x hdx
      omega
    · simp only [if_neg hdx, if_pos hdy] at heq
      have := hgb y hdy
      omega
    · apply hfi x (Finset.mem_sdiff.mpr ⟨hx, hdx⟩) y (Finset.mem_sdiff.mpr ⟨hy, hdy⟩)
      exact Nat.add_left_cancel (by simpa only [if_neg hdx, if_neg hdy] using heq)

end DisjointBlockColoring

namespace DisjointBlockColoring
open Finset

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
private theorem head_or_tail {C : Finset α} {L : List (Finset α)} (h : C ∈ L) :
    C = L.headD ∅ ∨ C ∈ L.tail := by
  cases L with
  | nil => simp at h
  | cons B T => exact List.mem_cons.mp h

/-- Pack a path starting at its specified incoming point, if one is specified. -/
private theorem packPath (L : List (Finset α)) (U P : Finset α) (hpath : ∀ (p : List (Finset α)) (A : Finset α) (t : List (Finset α)), L = p ++ A :: t →
      (∀ B ∈ t, (A ∩ B).card ≤ 1) ∧ (∀ B ∈ t.tail, Disjoint A B))
    (hU : ∀ A ∈ L, A ⊆ U) (hP : P ⊆ L.headD ∅) (hPc : P.card ≤ 1)
    (hfree : ∀ B ∈ L.tail, Disjoint P B) :
    ∃ f : α → ℕ, (∀ x ∈ U, f x < U.card) ∧ (∀ x ∈ U, ∀ y ∈ U, f x=f y → x=y) ∧
      (∀ x ∈ P, f x = 0) ∧ ∀ B ∈ L, ∃ l, l+B.card ≤ U.card ∧
      ∀ x ∈ U, x ∈ B ↔ l ≤ f x ∧ f x < l+B.card := by
  classical
  induction L generalizing U P with
  | nil =>
    have hp : P ⊆ U := by have : P = ∅ := Finset.subset_empty.mp hP; simp [this]
    obtain ⟨f,hb,hi,hp0⟩ := pinnedBin U P hp hPc
    exact ⟨f,hb,hi,hp0,by simp⟩
  | cons A L ih =>
    obtain ⟨hcap,hsep⟩ := hpath [] A L rfl
    have hpath' (p : List (Finset α)) (B : Finset α) (t : List (Finset α))
        (he : L = p ++ B :: t) := hpath (A::p) B t (by simp [he])
    let B := L.headD ∅
    let J := A ∩ B
    let D := A \ B
    have hAU : A ⊆ U := hU A (by simp)
    have hDU : D ⊆ U := (sdiff_subset : D ⊆ A).trans hAU
    have hJB : J ⊆ L.headD ∅ := inter_subset_right
    have hJc : J.card ≤ 1 := by
      cases L with
      | nil => simp [J,B]
      | cons b T => exact hcap b (by simp)
    have hrest : ∀ C ∈ L, C ⊆ U \ D := by
      intro C hc x hx
      refine mem_sdiff.mpr ⟨hU C (List.mem_cons_of_mem _ hc) hx,?_,⟩
      intro hd
      rcases head_or_tail hc with hev | ht
      · exact (mem_sdiff.mp hd).2 (show x ∈ L.headD ∅ from hev ▸ hx)
      · exact disjoint_left.mp (hsep C ht) (mem_sdiff.mp hd).1 hx
    have hJfree : ∀ C ∈ L.tail, Disjoint J C := fun C hc =>
      (hsep C hc).mono_left (inter_subset_left : J ⊆ A)
    have hPD : P ⊆ D := by
      intro x hx
      refine mem_sdiff.mpr ⟨hP hx,?_⟩
      cases L with
      | nil => simp [B]
      | cons b T => exact fun hb => disjoint_left.mp (hfree b (by simp)) hx hb
    obtain ⟨g,hgb,hgi,hpin⟩ := pinnedBin D P hPD hPc
    obtain ⟨f,hfb,hfi,hentry,hblocks⟩ := ih (U \ D) J hpath' hrest hJB hJc hJfree
    let w (x : α) := if x ∈ D then g x else D.card + f x
    obtain ⟨hwbound,hwinj⟩ := prependBin U D hDU g f hgb hgi hfb hfi
    have hsize : D.card + J.card = A.card := Finset.card_sdiff_add_card_inter A B
    have htotal := card_sdiff_add_card_eq_card hDU
    refine ⟨w,hwbound,hwinj,fun x hx => by simpa [w,hPD hx] using hpin x hx,?_⟩
    intro C hc
    rcases List.mem_cons.mp hc with he|hc
    · subst C
      refine ⟨0, by simpa using card_le_card hAU, ?_⟩
      intro x hx
      by_cases hd : x ∈ D
      · have ha : x ∈ A := (mem_sdiff.mp hd).1
        have := hgb x hd
        simp only [ha,w,if_pos hd,Nat.zero_le,true_and,Nat.zero_add,true_iff]
        omega
      · have hxu : x ∈ U \ D := mem_sdiff.mpr ⟨hx,hd⟩
        simp only [w,if_neg hd,Nat.zero_le,true_and,Nat.zero_add]
        constructor
        · intro ha
          have hb : x ∈ B := by by_contra hn; exact hd (mem_sdiff.mpr ⟨ha,hn⟩)
          have hJ : x ∈ J := mem_inter.mpr ⟨ha,hb⟩
          have hcpos : 0 < J.card := Finset.card_pos.mpr ⟨x,hJ⟩
          have hz := hentry x hJ
          omega
        · intro hlt
          have hcpos : 0 < J.card := by omega
          obtain ⟨z,hz⟩ := Finset.card_pos.mp hcpos
          have hzA : z ∈ A := (mem_inter.mp hz).1
          have hzR : z ∈ U \ D := mem_sdiff.mpr ⟨hAU hzA, fun hh => (mem_sdiff.mp hh).2 (mem_inter.mp hz).2⟩
          have hzz := hentry z hz
          have hxe := hfi x hxu z hzR (by omega)
          simpa only [hxe] using hzA
    · obtain ⟨l,hl,hC⟩ := hblocks C hc
      refine ⟨D.card+l,by omega,?_⟩
      intro x hx
      by_cases hd : x ∈ D
      · have hn : x ∉ C := fun h => (mem_sdiff.mp (hrest C hc h)).2 hd
        have := hgb x hd
        simp only [w,if_pos hd,hn,false_iff]
        omega
      · rw [hC x (mem_sdiff.mpr ⟨hx,hd⟩)]
        simp only [w,if_neg hd]
        omega

/-- A union of path components admits a labeling in which every block is an interval.
A list can concatenate components in any order, without explicit separators. -/
theorem pathIntervalLabels {n : ℕ} (L : List (Finset (Fin n))) (hp : ∀ (p : List (Finset (Fin n))) (A : Finset (Fin n)) (t : List (Finset (Fin n))),
      L = p ++ A :: t → (∀ B ∈ t, (A ∩ B).card ≤ 1) ∧ (∀ B ∈ t.tail, Disjoint A B)) :
    ∃ e : Fin n ≃ Fin n, ∀ A ∈ L, ∃ l : ℕ, l+A.card ≤ n ∧
      ∀ x, x ∈ A ↔ l ≤ (e x).val ∧ (e x).val < l+A.card := by
  classical
  obtain ⟨f,hb,hi,_,hs⟩ := packPath L univ ∅ hp (fun _ _ => subset_univ _)
    (empty_subset _) (by simp) (by simp)
  let g (x : Fin n) : Fin n := ⟨f x, by simpa using hb x (mem_univ x)⟩
  have hg : Function.Injective g := fun x y h =>
    hi x (mem_univ _) y (mem_univ _) (congrArg Fin.val h)
  refine ⟨Equiv.ofBijective g ⟨hg, Finite.surjective_of_injective hg⟩, ?_⟩
  intro A hA
  obtain ⟨l,hl,h⟩ := hs A hA
  exact ⟨l,by simpa using hl, fun x => h x (mem_univ x)⟩

/-- A path ordering of a linear block family gives the required interval labels. -/
theorem pathIntervalLabels_of_linear {n : ℕ} (S : Finset (Finset (Fin n)))
    (hlin : ∀ ⦃A B⦄, A ∈ S → B ∈ S → ∀ ⦃i j : Fin n⦄, i ≠ j →
      i ∈ A → j ∈ A → i ∈ B → j ∈ B → A = B)
    (L : List (Finset (Fin n))) (hn : L.Nodup) (he : L.toFinset = S)
    (hfar : ∀ (p : List (Finset (Fin n))) (A : Finset (Fin n)) (t : List (Finset (Fin n))),
      L = p ++ A :: t → ∀ B ∈ t.tail, Disjoint A B) :
    ∃ e : Fin n ≃ Fin n, ∀ A ∈ S, ∃ l : ℕ, l+A.card ≤ n ∧
      ∀ x, x ∈ A ↔ l ≤ (e x).val ∧ (e x).val < l+A.card := by
  have hmem (C : Finset (Fin n)) : C ∈ S ↔ C ∈ L := by rw [← he, List.mem_toFinset]
  obtain ⟨e,h⟩ := pathIntervalLabels L (by
    intro p A t hLt
    refine ⟨?_,hfar p A t hLt⟩
    intro B hB
    have hnd : (p ++ A :: t).Nodup := hLt ▸ hn
    have hne : A ≠ B := fun h => (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1 (h ▸ hB)
    have ha : A ∈ S := (hmem _).mpr (by rw [hLt]; simp)
    have hb : B ∈ S := (hmem _).mpr (by rw [hLt]; simp [hB])
    apply Finset.card_le_one_iff.mpr
    intro x y hx hy
    rcases Finset.mem_inter.mp hx with ⟨hxA,hxB⟩
    rcases Finset.mem_inter.mp hy with ⟨hyA,hyB⟩
    exact Classical.byContradiction (fun hxy => hne (hlin ha hb hxy hxA hyA hxB hyB)))
  exact ⟨e,fun A hA => h A ((hmem _).mp hA)⟩

end DisjointBlockColoring

namespace Erdos19IntervalColors

/-- For one label inside [l,r] and one outside, their sum never equals the
endpoint sum modulo the number of labels. -/
theorem crossing_pair {n : ℕ} (l r u v : Fin n)
    (hu : l ≤ u ∧ u ≤ r) (hv : ¬(l ≤ v ∧ v ≤ r)) : u+v ≠ l+r := by
  intro h
  have he : u.val + v.val ≡ l.val + r.val [MOD n] := by
    simpa only [Nat.ModEq, Fin.val_add] using congrArg Fin.val h
  change l.val ≤ u.val ∧ u.val ≤ r.val at hu
  change ¬(l.val ≤ v.val ∧ v.val ≤ r.val) at hv
  by_cases hleft : v.val < l.val
  · have hh := he.add_le_of_lt (by omega : u.val + v.val < l.val + r.val)
    omega
  · have hh := he.symm.add_le_of_lt (by omega : l.val + r.val < u.val + v.val)
    omega


theorem crossing_pair_half_open {n l s : ℕ} (u v : Fin n)
    (hs : 0<s) (hls : l+s ≤ n)
    (hu : l ≤ u.val ∧ u.val < l+s) (hv : ¬(l ≤ v.val ∧ v.val < l+s)) :
    u+v ≠ ((⟨l, by omega⟩ : Fin n) + ⟨l+s-1, by omega⟩) := by
  apply crossing_pair
  · change l ≤ u.val ∧ u.val ≤ l+s-1
    omega
  · change ¬ (l ≤ v.val ∧ v.val ≤ l+s-1)
    omega

theorem labeled_crossing_pair {α : Type*} {n l s : ℕ} (e : α → Fin n) (A : Finset α)
    (hs : 0<s) (hls : l+s ≤ n)
    (interval : ∀ x, x ∈ A ↔ l ≤ (e x).val ∧ (e x).val < l+s)
    {u v : α} (hu : u ∈ A) (hv : v ∉ A) : e u+e v ≠ ((⟨l, by omega⟩ : Fin n) + ⟨l+s-1, by omega⟩) :=
  crossing_pair_half_open (e u) (e v) hs hls ((interval u).mp hu) (fun h => hv ((interval v).mpr h))

/-- Two intervals meeting in a common endpoint have distinct colors whenever
their other endpoints differ. This also covers one interval of length one. -/
theorem touching_intervals {n : ℕ} {a b : Fin n} (t : Fin n) (hab : a ≠ b) :
    a+t ≠ t+b := by
  intro he
  have hr : a.val + t.val ≡ b.val + t.val [MOD n] := by
    simpa only [Nat.ModEq, Fin.val_add, Nat.add_comm t.val b.val] using congrArg Fin.val he
  have h := Nat.ModEq.add_right_cancel' t.val hr
  exact hab (Fin.ext (by simpa only [Nat.ModEq, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using h))


end Erdos19IntervalColors

namespace Erdos19IntervalColors

/-- Nondegenerate intervals with a singleton intersection meet end to start. -/
theorem endpoints_of_unique_intersection {α : Type*} [LinearOrder α] {a b c d x : α}
    (hab : a < b) (hcd : c < d) (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ x ∧ x ≤ d)
    (hu : ∀ u v, (a ≤ u ∧ u ≤ b) → (c ≤ u ∧ u ≤ d) →
      (a ≤ v ∧ v ≤ b) → (c ≤ v ∧ v ≤ d) → u = v) : b = c ∨ d = a := by
  have h : max a c ≤ min b d := (max_le hx.1 hy.1).trans (le_min hx.2 hy.2)
  have he := hu (max a c) (min b d)
    ⟨le_max_left .., h.trans (min_le_left ..)⟩
    ⟨le_max_right .., h.trans (min_le_right ..)⟩
    ⟨(le_max_left ..).trans h, min_le_left ..⟩
    ⟨(le_max_right ..).trans h, min_le_right ..⟩
  rcases le_total a c with hl|hl <;> rcases le_total b d with hr|hr
  · rw [max_eq_right hl, min_eq_left hr] at he; exact Or.inl he.symm
  · rw [max_eq_right hl, min_eq_right hr] at he; exact (hcd.ne he).elim
  · rw [max_eq_left hl, min_eq_left hr] at he; exact (hab.ne he).elim
  · rw [max_eq_left hl, min_eq_right hr] at he; exact Or.inr he.symm

/-- The endpoint sums of two intersecting labeled intervals are distinct when their
common point is unique. -/
theorem labeled_interval_colors_ne {n : ℕ} (e : Fin n ≃ Fin n) (A B : Finset (Fin n))
    {l k : ℕ} (hsA : 2 ≤ A.card) (hsB : 2 ≤ B.card)
    (hl : l+A.card ≤ n) (hk : k+B.card ≤ n)
    (hA : ∀ x, x∈A ↔ l ≤ (e x).val ∧ (e x).val < l+A.card)
    (hB : ∀ x, x∈B ↔ k ≤ (e x).val ∧ (e x).val < k+B.card)
    (hm : (A ∩ B).Nonempty) (hu : ∀ x∈A, ∀ y∈A, x∈B → y∈B → x=y) :
    ((⟨l, by omega⟩ : Fin n) + ⟨l+A.card-1, by omega⟩) ≠ ((⟨k, by omega⟩ : Fin n) + ⟨k+B.card-1, by omega⟩) := by
  let a : Fin n := ⟨l,by omega⟩
  let b : Fin n := ⟨l+A.card-1,by omega⟩
  let c : Fin n := ⟨k,by omega⟩
  let d : Fin n := ⟨k+B.card-1,by omega⟩
  have hab : a < b := by change l < l+A.card-1; omega
  have hcd : c < d := by change k < k+B.card-1; omega
  have hA' (t : Fin n) : e.symm t ∈ A ↔ a ≤ t ∧ t ≤ b := by
    rw [hA,e.apply_symm_apply]
    change l ≤ t.val ∧ t.val < l+A.card ↔ l ≤ t.val ∧ t.val ≤ l+A.card-1
    omega
  have hB' (t : Fin n) : e.symm t ∈ B ↔ c ≤ t ∧ t ≤ d := by
    rw [hB,e.apply_symm_apply]
    change k ≤ t.val ∧ t.val < k+B.card ↔ k ≤ t.val ∧ t.val ≤ k+B.card-1
    omega
  obtain ⟨x,hx⟩ := hm
  obtain ⟨hxA,hxB⟩ := Finset.mem_inter.mp hx
  have he := endpoints_of_unique_intersection hab hcd
    ((hA' (e x)).mp (by simpa using hxA)) ((hB' (e x)).mp (by simpa using hxB))
    (fun u v huA huB hvA hvB => e.symm.injective
      (hu _ ((hA' _).mpr huA) _ ((hA' _).mpr hvA) ((hB' _).mpr huB) ((hB' _).mpr hvB)))
  change a+b ≠ c+d
  rcases he with he|he
  · rw [←he] at hcd ⊢
    exact touching_intervals b (hab.trans hcd).ne
  · rw [he] at hcd ⊢
    exact fun h => touching_intervals a (hcd.trans hab).ne h.symm

end Erdos19IntervalColors

open Finset
namespace DisjointBlockColoring

private theorem other_endpoint {n : ℕ} {A : Finset (Fin n)} {i : Fin n}
    (hi : i ∈ A) (hA : A.card = 2) : ∃ j ≠ i, A = {i,j} := by
  have h1 : (A.erase i).card = 1 := by rw [card_erase_of_mem hi, hA]
  obtain ⟨j, hj⟩ := card_eq_one.mp h1
  have hjA : j ∈ A.erase i := by simp [hj]
  exact ⟨j, (mem_erase.mp hjA).1, by rw [← insert_erase hi, hj]⟩

/-- Given a vertex labeling and a reserved color for each large block,
the pair colors are the sums of their endpoint labels. -/
theorem color_of_crossing_reservations {n : ℕ} [NeZero n] (K : Finset (Finset (Fin n)))
    (hs : ∀ A ∈ K, 2 ≤ A.card)
    (hlin : ∀ ⦃A B⦄, A ∈ K → B ∈ K → ∀ ⦃i j : Fin n⦄, i ≠ j →
      i ∈ A → j ∈ A → i ∈ B → j ∈ B → A = B)
    (e : Fin n ≃ Fin n) (g : Finset (Fin n) → Fin n)
    (hbig : ∀ A ∈ K, 3 ≤ A.card → ∀ B ∈ K, 3 ≤ B.card → A ≠ B →
      (A ∩ B).Nonempty → g A ≠ g B)
    (hc : ∀ A ∈ K, 3 ≤ A.card → ∀ i ∈ A, ∀ j ∉ A, e i + e j ≠ g A) :
    ∃ c : Finset (Fin n) → Fin n, ∀ A ∈ K, ∀ B ∈ K, A ≠ B →
      (A ∩ B).Nonempty → c A ≠ c B := by
  classical
  let c (A : Finset (Fin n)) : Fin n := if 3 ≤ A.card then g A else ∑ x ∈ A, e x
  have mixed {A B : Finset (Fin n)} (hA : A ∈ K) (hB : B ∈ K) (ha : A.card = 2)
      (hb : 3 ≤ B.card) (hne : A ≠ B) (hm : (A ∩ B).Nonempty) : c A ≠ c B := by
    obtain ⟨i, hi⟩ := hm
    obtain ⟨hiA, hiB⟩ := mem_inter.mp hi
    obtain ⟨j,hj,hpair⟩ := other_endpoint hiA ha
    have hjA : j ∈ A := by simp [hpair]
    have hjB : j ∉ B := fun h => hne (hlin hA hB hj.symm hiA hjA hiB h)
    dsimp only [c]
    rw [if_neg (by omega : ¬ 3 ≤ A.card), if_pos hb, hpair, sum_pair hj.symm]
    exact hc B hB hb i hiB j hjB
  refine ⟨c, ?_⟩
  intro A hA B hB hne hm
  by_cases ha : 3 ≤ A.card
  · by_cases hb : 3 ≤ B.card
    · simpa only [c, if_pos ha, if_pos hb] using hbig A hA ha B hB hb hne hm
    · exact (mixed hB hA (by have := hs B hB; omega) ha hne.symm (by rwa [inter_comm])).symm
  · have ha2 : A.card = 2 := by have := hs A hA; omega
    by_cases hb : 3 ≤ B.card
    · exact mixed hA hB ha2 hb hne hm
    · have hb2 : B.card = 2 := by have := hs B hB; omega
      obtain ⟨i,hi⟩ := hm
      obtain ⟨j,hj,hAj⟩ := other_endpoint (mem_inter.mp hi).1 ha2
      obtain ⟨k,hk,hBk⟩ := other_endpoint (mem_inter.mp hi).2 hb2
      intro heq
      dsimp only [c] at heq
      rw [if_neg ha, if_neg hb, hAj, hBk, sum_pair hj.symm, sum_pair hk.symm] at heq
      exact hne (hAj.trans ((congrArg (fun v => ({i,v} : Finset (Fin n)))
        (e.injective (add_left_cancel heq))).trans hBk.symm))

end DisjointBlockColoring

open Finset
namespace DisjointBlockColoring

/-- Common consecutive labels suffice even when distinct large blocks meet. -/
theorem color_interval_large_blocks {n : ℕ} [NeZero n] (K : Finset (Finset (Fin n)))
    (hs : ∀ A ∈ K, 2 ≤ A.card)
    (hlin : ∀ ⦃A B⦄, A ∈ K → B ∈ K → ∀ ⦃i j : Fin n⦄, i ≠ j →
      i ∈ A → j ∈ A → i ∈ B → j ∈ B → A = B)
    (e : Fin n ≃ Fin n)
    (hl : ∀ A ∈ K, 3 ≤ A.card → ∃ l : ℕ, l+A.card ≤ n ∧
      ∀ x, x ∈ A ↔ l ≤ (e x).val ∧ (e x).val < l+A.card) :
    ∃ c : Finset (Fin n) → Fin n, ∀ A ∈ K, ∀ B ∈ K, A ≠ B →
      (A ∩ B).Nonempty → c A ≠ c B := by
  classical
  let big := K.filter fun A => 3 ≤ A.card
  have he (A) (h : A ∈ big) := hl A (mem_filter.mp h).1 (mem_filter.mp h).2
  let g (A : Finset (Fin n)) : Fin n := if h : A ∈ big then
    (let l := (he A h).choose
     have hsize : 3 ≤ A.card := (mem_filter.mp h).2
     have hend : l + A.card ≤ n := (he A h).choose_spec.1
     (⟨l, by omega⟩ : Fin n) + ⟨l + A.card - 1, by omega⟩) else 0
  apply color_of_crossing_reservations K hs hlin e g
  · intro A hA ha B hB hb hne hm
    have hbA : A ∈ big := mem_filter.mpr ⟨hA,ha⟩
    have hbB : B ∈ big := mem_filter.mpr ⟨hB,hb⟩
    simp only [g, dif_pos hbA, dif_pos hbB]
    apply Erdos19IntervalColors.labeled_interval_colors_ne e A B (hs A hA) (hs B hB)
      (he A hbA).choose_spec.1 (he B hbB).choose_spec.1
      (he A hbA).choose_spec.2 (he B hbB).choose_spec.2 hm
    intro x hxA y hyA hxB hyB
    exact Classical.byContradiction fun hxy => hne (hlin hA hB hxy hxA hyA hxB hyB)
  · intro A hA ha i hi j hj
    have hb : A ∈ big := mem_filter.mpr ⟨hA,ha⟩
    simp only [g, dif_pos hb]
    exact Erdos19IntervalColors.labeled_crossing_pair e A (by omega)
      (he A hb).choose_spec.1 (he A hb).choose_spec.2 hi hj

end DisjointBlockColoring

namespace OMA.R_Erdos19_erdos_19_variants_large_n_R1_H1_R2

open Finset Filter
open scoped Classical

private theorem design_linear {n : ℕ} {K : Finset (Finset (Fin n))}
    (hp : ∀ i j : Fin n, i ≠ j → ∃! A, A ∈ K ∧ i ∈ A ∧ j ∈ A)
    {A B : Finset (Fin n)} (ha : A ∈ K) (hb : B ∈ K)
    {i j : Fin n} (hne : i ≠ j) (hiA : i ∈ A) (hjA : j ∈ A) (hiB : i ∈ B) (hjB : j ∈ B) :
    A = B :=
  (hp i j hne).unique ⟨ha,hiA,hjA⟩ ⟨hb,hiB,hjB⟩

/-- A large block meets at least three distinct other large blocks. -/
def H1 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ K : Finset (Finset (Fin n)),
    (∀ A ∈ K, 2 ≤ A.card ∧ A.card * A.card ≤ n) →
    (∀ i j : Fin n, i ≠ j → ∃! A, A ∈ K ∧ i ∈ A ∧ j ∈ A) →
    let S := K.filter fun A => 3 ≤ A.card
    (∃ A ∈ S, 3 ≤ ((S.erase A).filter fun B => (A ∩ B).Nonempty).card) →
    ∃ c : K → Fin n, ∀ A B : K, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B

/-- Maximum overlap degree two, with a nonempty subfamily of minimum overlap
degree two. -/
def H2 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ K : Finset (Finset (Fin n)),
    (∀ A ∈ K, 2 ≤ A.card ∧ A.card * A.card ≤ n) →
    (∀ i j : Fin n, i ≠ j → ∃! A, A ∈ K ∧ i ∈ A ∧ j ∈ A) →
    let S := K.filter fun A => 3 ≤ A.card
    (∀ A ∈ S, ((S.erase A).filter fun B => (A ∩ B).Nonempty).card ≤ 2) →
    (∃ T ⊆ S, T.Nonempty ∧ ∀ A ∈ T, 2 ≤ ((T.erase A).filter fun B => (A ∩ B).Nonempty).card) →
    ∃ c : K → Fin n, ∀ A B : K, A ≠ B → (A.val ∩ B.val).Nonempty → c A ≠ c B

theorem main : H1 → H2 → OMA.R_Erdos19_erdos_19_variants_large_n_R1.H1 := by
  classical
  intro high cycle
  unfold H1 at high
  unfold H2 at cycle
  unfold OMA.R_Erdos19_erdos_19_variants_large_n_R1.H1
  filter_upwards [eventually_ge_atTop (1 : ℕ), high, cycle] with n hn hhigh hcycle
  intro K hsize hp
  let S := K.filter fun A => 3 ≤ A.card
  by_cases h₁ : ∃ A ∈ S, 3 ≤ ((S.erase A).filter fun B => (A ∩ B).Nonempty).card
  · exact hhigh K hsize hp h₁
  have hlow (A) (hA : A ∈ S) : ((S.erase A).filter fun B => (A ∩ B).Nonempty).card ≤ 2 := by
    by_contra! h
    exact h₁ ⟨A, hA, h⟩
  by_cases h₂ : ∃ T ⊆ S, T.Nonempty ∧ ∀ A ∈ T, 2 ≤ ((T.erase A).filter fun B => (A ∩ B).Nonempty).card
  · exact hcycle K hsize hp hlow h₂
  have leaf (T : Finset (Finset (Fin n))) (hT : T ⊆ S) (nonempty : T.Nonempty) :
      ∃ A ∈ T, ((T.erase A).filter fun B => (A ∩ B).Nonempty).card ≤ 1 := by
    by_contra! h
    exact h₂ ⟨T, hT, nonempty, h⟩
  let : NeZero n := ⟨by omega⟩
  obtain ⟨L, hnL, hLS, far⟩ := Erdos19ForestOrder.path_forest_order S hlow leaf
  obtain ⟨e,he⟩ := DisjointBlockColoring.pathIntervalLabels_of_linear S
    (fun {_ _} hA hB {_ _} => design_linear hp (mem_filter.mp hA).1 (mem_filter.mp hB).1)
    L hnL hLS far
  obtain ⟨c,hc⟩ := DisjointBlockColoring.color_interval_large_blocks K
    (fun A hA => (hsize A hA).1) (fun {_ _} hA hB {_ _} => design_linear hp hA hB) e
    (fun A hA hbig => he A (mem_filter.mpr ⟨hA,hbig⟩))
  exact ⟨fun A => c A.val, fun A B hne => hc A.val A.property B.val B.property
    (fun h => hne (Subtype.ext h))⟩

end OMA.R_Erdos19_erdos_19_variants_large_n_R1_H1_R2

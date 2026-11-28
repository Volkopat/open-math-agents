import OMAReductions.R_Erdos651_erdos_651_R1_H1_R1_H1_R1_H2_R1
import Mathlib.Analysis.Convex.Between
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Antichain
import Mathlib.Analysis.Convex.Join

/-!
Middle-cluster selection from the two signed cones in Proposition 3.1 and the
following chain and antichain argument of Pohoata and Zakharov, "Convex polytopes
from fewer points", Section 3. https://arxiv.org/html/2208.04878#S3
-/

/-! The three separating inequalities used in the ordered cluster selection. -/

namespace OMA.Erdos651ClusterOrder

open Set
open scoped Affine

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

private theorem affine_nonpos_of_wbtw {a b c : V} (f : V →ᵃ[ℝ] ℝ)
    (h : Wbtw ℝ a b c) (ha : f a ≤ 0) (hc : f c ≤ 0) : f b ≤ 0 :=
  (convex_Iic (𝕜 := ℝ) (0 : ℝ)).mem_of_wbtw (h.map f) ha hc

/-- If each set has a positive affine separator that is nonpositive on the other two,
no collinear triple can take one point from each set. -/
theorem not_collinear_of_three_separators {A B C : Set V} (f g h : V →ᵃ[ℝ] ℝ)
    (hf₁ : ∀ a ∈ A, 0 < f a) (hf₂ : ∀ a ∈ B ∪ C, f a ≤ 0)
    (hg₁ : ∀ b ∈ B, 0 < g b) (hg₂ : ∀ b ∈ C ∪ A, g b ≤ 0)
    (hh₁ : ∀ c ∈ C, 0 < h c) (hh₂ : ∀ c ∈ A ∪ B, h c ≤ 0)
    {a b c : V} (ha : a ∈ A) (hb : b ∈ B) (hc : c ∈ C) :
    ¬ Collinear ℝ ({a, b, c} : Set V) := by
  intro hcol
  rcases hcol.wbtw_or_wbtw_or_wbtw with habc | hbca | hcab
  · exact (not_le_of_gt (hg₁ b hb))
      (affine_nonpos_of_wbtw g habc (hg₂ a (Or.inr ha)) (hg₂ c (Or.inl hc)))
  · exact (not_le_of_gt (hh₁ c hc))
      (affine_nonpos_of_wbtw h hbca (hh₂ b (Or.inr hb)) (hh₂ a (Or.inl ha)))
  · exact (not_le_of_gt (hf₁ a ha))
      (affine_nonpos_of_wbtw f hcab (hf₂ c (Or.inr hc)) (hf₂ b (Or.inl hb)))

/-- Opposite closed cones separated by positive margins admit no common line with
the intervening sign region. -/
theorem signed_cones_no_common_line (f₀ f₁ f₂ : V →ᵃ[ℝ] ℝ) {ε : ℝ} (hε : 0 < ε) :
    let U := {x : V | f₀ x ≤ 0 ∧ ε ≤ f₁ x ∧ ε ≤ f₂ x}
    let D := {x : V | f₀ x ≤ 0 ∧ f₁ x ≤ -ε ∧ f₂ x ≤ -ε}
    let M := {x : V | 0 < f₀ x ∧ f₁ x < 0 ∧ 0 < f₂ x}
    ∀ u ∈ U, ∀ d ∈ D, ∀ m ∈ M, ∀ x y : V,
      u ∈ line[ℝ, x, y] → d ∈ line[ℝ, x, y] → m ∈ line[ℝ, x, y] → False := by
  dsimp only
  intro u hu d hd m hm x y hux hdx hmx
  have hnε : -ε ≤ 0 := neg_nonpos.mpr hε.le
  have hcol := collinear_triple_of_mem_affineSpan_pair hux hdx hmx
  refine not_collinear_of_three_separators (A := {x : V | f₀ x ≤ 0 ∧ ε ≤ f₁ x ∧ ε ≤ f₂ x})
    (B := {x : V | f₀ x ≤ 0 ∧ f₁ x ≤ -ε ∧ f₂ x ≤ -ε})
    (C := {x : V | 0 < f₀ x ∧ f₁ x < 0 ∧ 0 < f₂ x}) f₁ (-f₂) f₀
    (fun _ hv => hε.trans_le hv.2.1) ?_ ?_ ?_ (fun _ hv => hv.1) ?_ hu hd hm hcol
  · rintro v (hv | hv)
    · exact hv.2.1.trans hnε
    · exact hv.2.1.le
  · intro v hv
    change 0 < -f₂ v
    exact neg_pos.mpr (hv.2.2.trans_lt (neg_lt_zero.mpr hε))
  · rintro v (hv | hv)
    · exact neg_nonpos.mpr hv.2.2.le
    · exact neg_nonpos.mpr (hε.le.trans hv.2.2)
  · rintro v (hv | hv) <;> exact hv.1

end OMA.Erdos651ClusterOrder

/-! Finite chain and antichain selection by longest-chain ranks. -/

namespace OMA.Erdos651ClusterOrder

open Finset

/-- A finite strict partial order has a chain or an antichain with size at least the
square root of the number of points. The relation only needs to be ordered on `S`. -/
theorem exists_chain_or_antichain_square {V : Type*} (S : Finset V) (r : V → V → Prop)
    (hirr : ∀ x ∈ S, ¬ r x x)
    (htrans : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, r x y → r y z → r x z) :
    ∃ T ⊆ S, S.card ≤ T.card ^ 2 ∧
      (IsChain r (T : Set V) ∨ IsAntichain r (T : Set V)) := by
  classical
  let good := S.powerset.filter fun (T : Finset V) =>
    IsChain r (T : Set V) ∨ IsAntichain r (T : Set V)
  have hempty : ∅ ∈ good := by simp [good]
  obtain ⟨T, hT, hmax⟩ := exists_max_image good card ⟨∅, hempty⟩
  have hTspec := mem_filter.mp hT
  let below (x : V) := S.powerset.filter fun (D : Finset V) =>
    IsChain r (D : Set V) ∧ ∀ y ∈ D, r y x
  let rank (x : V) := (below x).sup card
  have below_spec {x : V} {D : Finset V} (hD : D ∈ below x) :
      D ⊆ S ∧ IsChain r (D : Set V) ∧ ∀ y ∈ D, r y x := by
    have h := mem_filter.mp hD
    exact ⟨mem_powerset.mp h.1, h.2⟩
  have rank_attains (x : V) : ∃ D ∈ below x, D.card = rank x := by
    have hn : (below x).Nonempty := ⟨∅, by simp [below]⟩
    obtain ⟨D, hD, hbest⟩ := exists_max_image (below x) card hn
    exact ⟨D, hD, le_antisymm (le_sup hD) (Finset.sup_le hbest)⟩
  have add_end {x : V} (hx : x ∈ S) {D : Finset V} (hD : D ∈ below x) :
      x ∉ D ∧ insert x D ⊆ S ∧ IsChain r ((insert x D : Finset V) : Set V) := by
    obtain ⟨hS, hchain, hbelow⟩ := below_spec hD
    refine ⟨fun hxD => hirr x hx (hbelow x hxD), insert_subset hx hS, ?_⟩
    rw [coe_insert]
    exact hchain.insert fun y hy _ => Or.inr (hbelow y hy)
  have rank_lt {x y : V} (hx : x ∈ S) (hy : y ∈ S) (hxy : r x y) : rank x < rank y := by
    obtain ⟨D, hD, hcard⟩ := rank_attains x
    obtain ⟨hxD, hS, hchain⟩ := add_end hx hD
    have hbelow (z : V) (hz : z ∈ insert x D) : r z y := by
      rcases mem_insert.mp hz with rfl | hzD
      · exact hxy
      · have h := below_spec hD
        exact htrans z (h.1 hzD) x hx y hy (h.2.2 z hzD) hxy
    have hs : insert x D ∈ below y :=
      mem_filter.mpr ⟨mem_powerset.mpr hS, hchain, hbelow⟩
    have hle : (insert x D).card ≤ rank y := le_sup hs
    rw [card_insert_of_notMem hxD, hcard] at hle
    omega
  have maps_to (x : V) (hx : x ∈ S) : rank x ∈ range T.card := by
    obtain ⟨D, hD, hcard⟩ := rank_attains x
    obtain ⟨hxD, hS, hchain⟩ := add_end hx hD
    have hins : insert x D ∈ good := mem_filter.mpr ⟨mem_powerset.mpr hS, Or.inl hchain⟩
    have hle := hmax _ hins
    rw [card_insert_of_notMem hxD, hcard] at hle
    exact mem_range.mpr (by omega)
  have fiber_le (b : ℕ) : (S.filter (fun x => rank x = b)).card ≤ T.card := by
    refine hmax _ (mem_filter.mpr ⟨mem_powerset.mpr (filter_subset _ _), Or.inr ?_⟩)
    intro x hx y hy _ hxy
    have hx' := mem_filter.mp hx
    have hy' := mem_filter.mp hy
    have hlt := rank_lt hx'.1 hy'.1 hxy
    omega
  have hcount := card_le_mul_card_image_of_maps_to maps_to T.card (fun b _ => fiber_le b)
  exact ⟨T, mem_powerset.mp hTspec.1, by simpa only [card_range, pow_two] using hcount, hTspec.2⟩

end OMA.Erdos651ClusterOrder

/-! Selecting a large middle-cluster subset whose secant lines avoid one of two cones. -/

namespace OMA.Erdos651ClusterOrder

open Set
open scoped Affine

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

private theorem affine_lt_of_wbtw {a b c : V} (f : V →ᵃ[ℝ] ℝ)
    (h : Wbtw ℝ a b c) (hab : a ≠ b) (hac : f c < f a) : f b < f a := by
  obtain ⟨t, ht, htb⟩ := h
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (by
    intro htzero
    apply hab
    rwa [← htzero, AffineMap.lineMap_apply_zero] at htb)
  have he := congrArg f htb
  rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_module', smul_eq_mul] at he
  exact he ▸ add_lt_of_neg_left _ (mul_neg_of_pos_of_neg htpos (sub_neg.mpr hac))

private theorem wbtw_of_mem_added_hull {P : Set V} (hPc : Convex ℝ P) (hPn : P.Nonempty)
    {x y : V} (hx : x ∈ convexHull ℝ (insert y P)) : ∃ z ∈ P, Wbtw ℝ y x z := by
  rw [convexHull_insert hPn, hPc.convexHull_eq] at hx
  obtain ⟨y', hy', z, hz, hseg⟩ := mem_convexJoin.mp hx
  obtain rfl := mem_singleton_iff.mp hy'
  exact ⟨z, hz, mem_segment_iff_wbtw.mp hseg⟩

private theorem mem_added_hull_of_wbtw {P : Set V} {x y z : V} (hz : z ∈ P)
    (h : Wbtw ℝ y x z) : x ∈ convexHull ℝ (insert y P) :=
  (convex_convexHull ℝ (insert y P)).mem_of_wbtw h
    (subset_convexHull ℝ _ (mem_insert _ _))
    (subset_convexHull ℝ _ (mem_insert_of_mem _ hz))

/-- A finite set on the positive side of a convex cone admits a large subset
whose secants all avoid the cone, or all avoid the other separated set. -/
theorem select_middle_cluster (S : Finset V) (P Q : Set V) (f : V →ᵃ[ℝ] ℝ)
    (hPc : Convex ℝ P) (hPn : P.Nonempty)
    (hS : ∀ x ∈ S, 0 < f x) (hP : ∀ z ∈ P, f z ≤ 0)
    (hsep : ∀ x ∈ S, ∀ y : V, ∀ u ∈ P, ∀ d ∈ Q,
      u ∈ line[ℝ, x, y] → d ∈ line[ℝ, x, y] → False) :
    ∃ T ⊆ S, S.card ≤ T.card ^ 2 ∧
      ((∀ x ∈ T, ∀ y ∈ T, x ≠ y → Disjoint (line[ℝ, x, y] : Set V) P) ∨
       (∀ x ∈ T, ∀ y ∈ T, x ≠ y → Disjoint (line[ℝ, x, y] : Set V) Q)) := by
  let r (x y : V) := f x < f y ∧ x ∈ convexHull ℝ (insert y P)
  have rtrans {x y z : V} (hxy : r x y) (hyz : r y z) : r x z := by
    refine ⟨hxy.1.trans hyz.1, ?_⟩
    apply convexHull_min _ (convex_convexHull ℝ _) hxy.2
    exact insert_subset_iff.mpr ⟨hyz.2, fun w hw =>
      subset_convexHull ℝ _ (mem_insert_of_mem _ hw)⟩
  have of_between {x y z : V} (hy : y ∈ S) (hz : z ∈ P) (hne : x ≠ y)
      (h : Wbtw ℝ y x z) : r x y :=
    ⟨affine_lt_of_wbtw f h hne.symm ((hP z hz).trans_lt (hS y hy)),
     mem_added_hull_of_wbtw hz h⟩
  obtain ⟨T, hTS, hcard, hchain | hanti⟩ := exists_chain_or_antichain_square S r
    (fun x _ hx => (lt_irrefl (f x)) hx.1) (fun _ _ _ _ _ _ => rtrans)
  · refine ⟨T, hTS, hcard, Or.inr ?_⟩
    intro x hx y hy hne
    apply disjoint_left.mpr
    intro d hd hdQ
    rcases hchain hx hy hne with hxy | hyx
    · obtain ⟨u, hu, hub⟩ := wbtw_of_mem_added_hull hPc hPn hxy.2
      have hul := hub.right_mem_affineSpan_of_left_ne hne.symm
      rw [Set.pair_comm y x] at hul
      exact hsep x (hTS hx) y u hu d hdQ hul hd
    · obtain ⟨u, hu, hub⟩ := wbtw_of_mem_added_hull hPc hPn hyx.2
      exact hsep x (hTS hx) y u hu d hdQ (hub.right_mem_affineSpan_of_left_ne hne) hd
  · refine ⟨T, hTS, hcard, Or.inl ?_⟩
    intro x hx y hy hne
    apply disjoint_left.mpr
    intro u hu huP
    have hcol := collinear_triple_of_mem_affineSpan_pair
      (left_mem_affineSpan_pair ℝ x y) (right_mem_affineSpan_pair ℝ x y) hu
    rcases hcol.wbtw_or_wbtw_or_wbtw with hxyu | hyux | huxy
    · exact hanti hy hx hne.symm (of_between (hTS hx) huP hne.symm hxyu)
    · have hfu : 0 < f u := (convex_Ioi (𝕜 := ℝ) (0 : ℝ)).mem_of_wbtw
        (hyux.map f) (hS y (hTS hy)) (hS x (hTS hx))
      exact (not_le_of_gt hfu) (hP u huP)
    · exact hanti hx hy hne (of_between (hTS hy) huP hne huxy.symm)

/-- For the two signed cones, one of the two line-avoidance alternatives holds on
a subset whose squared cardinality is at least the middle cluster's size. -/
theorem select_from_signed_cones (S : Finset V) (f₀ f₁ f₂ : V →ᵃ[ℝ] ℝ) {ε : ℝ}
    (hε : 0 < ε) (hS : ∀ x ∈ S, 0 < f₀ x ∧ f₁ x < 0 ∧ 0 < f₂ x) :
    let U := {z : V | f₀ z ≤ 0 ∧ ε ≤ f₁ z ∧ ε ≤ f₂ z}
    let D := {z : V | f₀ z ≤ 0 ∧ f₁ z ≤ -ε ∧ f₂ z ≤ -ε}
    ∃ T ⊆ S, S.card ≤ T.card ^ 2 ∧
      ((∀ x ∈ T, ∀ y ∈ T, x ≠ y → Disjoint (line[ℝ, x, y] : Set V) U) ∨
       (∀ x ∈ T, ∀ y ∈ T, x ≠ y → Disjoint (line[ℝ, x, y] : Set V) D)) := by
  dsimp only
  let U := {z : V | f₀ z ≤ 0 ∧ ε ≤ f₁ z ∧ ε ≤ f₂ z}
  let D := {z : V | f₀ z ≤ 0 ∧ f₁ z ≤ -ε ∧ f₂ z ≤ -ε}
  change ∃ T ⊆ S, S.card ≤ T.card ^ 2 ∧
    ((∀ x ∈ T, ∀ y ∈ T, x ≠ y → Disjoint (line[ℝ, x, y] : Set V) U) ∨
     (∀ x ∈ T, ∀ y ∈ T, x ≠ y → Disjoint (line[ℝ, x, y] : Set V) D))
  by_cases hUn : U.Nonempty
  · have hUc : Convex ℝ U := ((convex_Iic (𝕜 := ℝ) (0 : ℝ)).affine_preimage f₀).inter
      (((convex_Ici (𝕜 := ℝ) ε).affine_preimage f₁).inter
       ((convex_Ici (𝕜 := ℝ) ε).affine_preimage f₂))
    refine select_middle_cluster S U D f₀ hUc hUn (fun x hx => (hS x hx).1)
      (fun _ hz => hz.1) ?_
    intro x hx y u hu d hd hul hdl
    exact signed_cones_no_common_line f₀ f₁ f₂ hε u hu d hd x (hS x hx) x y hul hdl
      (left_mem_affineSpan_pair ℝ x y)
  · refine ⟨S, le_rfl, ?_, Or.inl ?_⟩
    · cases hs : S.card with
      | zero => simp
      | succ n => simpa only [pow_two] using Nat.le_mul_of_pos_right (n+1) (Nat.succ_pos n)
    · intro x _ y _ _
      rw [not_nonempty_iff_eq_empty.mp hUn]
      exact disjoint_bot_right

end OMA.Erdos651ClusterOrder

theorem OMA.solution : OMA.R_Erdos651_erdos_651_R1_H1_R1_H1_R1_H2_R1.H2 := by
  intro S f₀ f₁ f₂ ε hε hS
  exact OMA.Erdos651ClusterOrder.select_from_signed_cones S f₀ f₁ f₂ hε hS

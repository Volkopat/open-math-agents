import OMAReductions.R_Erdos723_erdos_723_variants_eq_12_R1
import Mathlib

/-! Count incident lines at each point. A point of degree 12 directly determines
a missing line. In the 143-line case without such a point, every degree is 11
or 13. The common-neighbor counts for uncovered pairs then produce a 13-point
line of degree-11 points that meets every existing line exactly once. -/

open Finset

namespace OMA.OrderTwelveCompletion

abbrev Point := Fin 157
abbrev Line := Finset Point

structure Bundle where
  lines : Finset Line
  size_eq : ∀ L ∈ lines, L.card = 13
  meet_eq : ∀ L ∈ lines, ∀ M ∈ lines, L ≠ M → (L ∩ M).card = 1

namespace Bundle

variable (B : Bundle)

def through (x : Point) : Finset Line := B.lines.filter (x ∈ ·)

def degree (x : Point) : ℕ := (B.through x).card

def joined (x : Point) : Finset Point := (B.through x).biUnion (fun L => L.erase x)

def missing (x : Point) : Finset Point := univ \ insert x (B.joined x)

def deficit (x : Point) : ℝ := 13 - (B.degree x : ℝ)

theorem mem_through {L : Line} {x : Point} :
    L ∈ B.through x ↔ L ∈ B.lines ∧ x ∈ L := mem_filter

theorem mem_joined {x y : Point} :
    y ∈ B.joined x ↔ y ≠ x ∧ ∃ L ∈ B.lines, x ∈ L ∧ y ∈ L := by
  simp only [joined,mem_biUnion,B.mem_through,mem_erase]
  tauto

theorem self_not_joined (x : Point) : x ∉ B.joined x := fun h => (B.mem_joined.mp h).1 rfl

theorem self_not_missing (x : Point) : x ∉ B.missing x := by simp [missing]

theorem mem_missing {x y : Point} :
    y ∈ B.missing x ↔ y ≠ x ∧ y ∉ B.joined x := by simp [missing]

theorem joined_symm {x y : Point} : y ∈ B.joined x ↔ x ∈ B.joined y := by
  rw [B.mem_joined,B.mem_joined]
  constructor <;> rintro ⟨hne,L,hL,hx,hy⟩ <;> exact ⟨hne.symm,L,hL,hy,hx⟩

theorem missing_symm {x y : Point} : y ∈ B.missing x ↔ x ∈ B.missing y := by
  rw [B.mem_missing,B.mem_missing,B.joined_symm,ne_comm]

theorem intersection_unique {L M : Line} (hL : L ∈ B.lines) (hM : M ∈ B.lines)
    (hne : L ≠ M) {x y : Point} (hxL : x ∈ L) (hxM : x ∈ M)
    (hyL : y ∈ L) (hyM : y ∈ M) : x = y := by
  apply card_le_one.mp (B.meet_eq L hL M hM hne).le x (mem_inter.mpr ⟨hxL,hxM⟩)
    y (mem_inter.mpr ⟨hyL,hyM⟩)

theorem line_unique {L M : Line} (hL : L ∈ B.lines) (hM : M ∈ B.lines)
    {x y : Point} (hne : x ≠ y) (hxL : x ∈ L) (hxM : x ∈ M) (hyL : y ∈ L) (hyM : y ∈ M) :
    L = M := by
  by_contra h
  exact hne (B.intersection_unique hL hM h hxL hxM hyL hyM)

theorem joined_card (x : Point) : (B.joined x).card = 12 * B.degree x := by
  classical
  rw [joined,card_biUnion]
  · have hc (L : Line) (hL : L ∈ B.through x) : (L.erase x).card = 12 := by
      obtain ⟨hl,hx⟩ := B.mem_through.mp hL
      rw [card_erase_of_mem hx,B.size_eq L hl]
    rw [sum_congr rfl hc,sum_const,nsmul_eq_mul,degree,mul_comm]
    rfl
  · intro L hL M hM hne
    obtain ⟨hl,hxL⟩ := B.mem_through.mp hL
    obtain ⟨hm,hxM⟩ := B.mem_through.mp hM
    apply disjoint_left.mpr
    intro y hyL hyM
    exact (mem_erase.mp hyL).1
      (B.intersection_unique hl hm hne (mem_erase.mp hyL).2 (mem_erase.mp hyM).2 hxL hxM)

theorem degree_le (x : Point) : B.degree x ≤ 13 := by
  have hsub : B.joined x ⊆ (univ : Finset Point).erase x := by
    intro y hy
    exact mem_erase.mpr ⟨(B.mem_joined.mp hy).1,mem_univ _⟩
  have h := card_le_card hsub
  have hU : ((univ : Finset Point).erase x).card = 156 := by
    rw [card_erase_of_mem (mem_univ x),card_univ,Fintype.card_fin]
  rw [B.joined_card,hU] at h
  omega

theorem missing_card (x : Point) : (B.missing x).card = 12 * (13-B.degree x) := by
  rw [missing,card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin,
    card_insert_of_notMem (B.self_not_joined x),B.joined_card]
  have := B.degree_le x
  omega

theorem degree_sum_weighted (W : Finset Point) (w : Point → ℝ) :
    (∑ x ∈ W, w x*(B.degree x : ℝ)) = ∑ L ∈ B.lines, ∑ x ∈ W ∩ L,w x := by
  have hd (x : Point) : (B.degree x : ℝ) = ∑ L ∈ B.lines, if x ∈ L then 1 else 0 := by
    unfold degree through
    rw [card_eq_sum_ones,Nat.cast_sum]
    simp only [sum_filter,Nat.cast_one]
  simp_rw [hd,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro L _
  rw [← filter_mem_eq_inter, sum_filter]
  apply sum_congr rfl
  intro x _
  by_cases hx : x ∈ L <;> simp [hx]

theorem degree_sum :
    (∑ x : Point, (B.degree x : ℝ)) = 13 * B.lines.card := by
  have he := B.degree_sum_weighted univ (fun _ => 1)
  calc
    _ = ∑ L ∈ B.lines, (L.card : ℝ) := by simpa using he
    _ = ∑ _L ∈ B.lines, (13 : ℝ) := by
      apply sum_congr rfl
      intro L hL
      rw [B.size_eq L hL]
      norm_num
    _ = _ := by simp [mul_comm]

theorem degree_sum_on_line {L : Line} (hL : L ∈ B.lines) :
    (∑ x ∈ L, (B.degree x : ℝ)) = (B.lines.card : ℝ) + 12 := by
  have he := B.degree_sum_weighted L (fun _ => 1)
  have he' : (∑ x ∈ L, (B.degree x : ℝ)) = ∑ K ∈ B.lines, ((L ∩ K).card : ℝ) := by
    simpa using he
  rw [he',← sum_erase_add _ _ hL]
  have hsum : (∑ K ∈ B.lines.erase L, ((L ∩ K).card : ℝ)) = (B.lines.erase L).card := by
    calc
      _ = ∑ _K ∈ B.lines.erase L, (1 : ℝ) := by
        apply sum_congr rfl
        intro K hK
        obtain ⟨hne,hK'⟩ := mem_erase.mp hK
        rw [B.meet_eq L hL K hK' hne.symm]
        norm_num
      _ = _ := by simp
  rw [hsum,inter_self,B.size_eq L hL]
  have hcard := card_erase_add_one hL
  have hR : ((B.lines.erase L).card : ℝ) + 1 = B.lines.card := by exact_mod_cast hcard
  norm_num only [Nat.cast_ofNat]
  linarith

theorem deficit_total :
    (∑ x : Point, B.deficit x) = 13*(157-(B.lines.card : ℝ)) := by
  simp only [deficit,sum_sub_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,
    B.degree_sum]
  ring

theorem deficit_on_line {L : Line} (hL : L ∈ B.lines) :
    (∑ x ∈ L, B.deficit x) = 157-(B.lines.card : ℝ) := by
  simp only [deficit,sum_sub_distrib,sum_const,B.size_eq L hL,nsmul_eq_mul,B.degree_sum_on_line hL]
  ring

theorem degree_boundary (hb : 143 ≤ B.lines.card) (ht : B.lines.card < 157)
    (hNo : ∀ x, B.degree x ≠ 12) :
    B.lines.card = 143 ∧ ∀ x, B.degree x = 13 ∨ B.degree x = 11 := by
  let t := 157-(B.lines.card : ℝ)
  have ht0 : 0 < t := sub_pos.mpr (by exact_mod_cast ht)
  have hbR : (143 : ℝ) ≤ B.lines.card := by exact_mod_cast hb
  have hEq : (∑ x : Point,B.deficit x*(B.degree x : ℝ)) = (B.lines.card : ℝ)*t := by
    rw [B.degree_sum_weighted]
    calc
      _ = ∑ _L ∈ B.lines,t := by
        apply sum_congr rfl
        intro L hL
        simpa using B.deficit_on_line hL
      _ = _ := by rw [sum_const,nsmul_eq_mul]
  have hTerm (x : Point) : B.deficit x*(B.degree x : ℝ) ≤ 11*B.deficit x := by
    have hx := B.degree_le x
    by_cases h : B.degree x = 13
    · simp [deficit,h]
    have hd : B.degree x ≤ 11 := by have := hNo x; omega
    have hdR : (B.degree x : ℝ) ≤ 11 := by exact_mod_cast hd
    have hpos : 0 ≤ B.deficit x := sub_nonneg.mpr (by exact_mod_cast hx)
    calc
      _ ≤ B.deficit x*11 := mul_le_mul_of_nonneg_left hdR hpos
      _ = _ := by ring
  have hUpper : (∑ x : Point,11*B.deficit x) = 143*t := by
    rw [← mul_sum,B.deficit_total]
    dsimp [t]
    ring
  have hsum := sum_le_sum (fun x (_ : x ∈ (univ : Finset Point)) => hTerm x)
  rw [hEq,hUpper] at hsum
  have hB := le_of_mul_le_mul_right hsum ht0
  have hb' : B.lines.card = 143 := by exact_mod_cast le_antisymm hB hbR
  refine ⟨hb',fun x => ?_⟩
  by_cases h : B.degree x = 13
  · exact Or.inl h
  right
  by_contra h11
  have hn := hNo x
  have hd : B.degree x < 11 := by have := B.degree_le x; omega
  have hStrict : B.deficit x*(B.degree x : ℝ) < 11*B.deficit x := by
    rw [mul_comm 11]
    exact mul_lt_mul_of_pos_left (by exact_mod_cast hd)
      (sub_pos.mpr (by exact_mod_cast (show B.degree x < 13 by omega)))
  have hs := sum_lt_sum (fun y (_ : y ∈ (univ : Finset Point)) => hTerm y)
    ⟨x,mem_univ _,hStrict⟩
  rw [hEq,hUpper,hb'] at hs
  norm_num at hs

def grid (X Y : Finset Line) : Finset Point := (X ×ˢ Y).biUnion fun t => t.1 ∩ t.2

theorem mem_grid {X Y : Finset Line} {z : Point} :
    z ∈ grid X Y ↔ ∃ L ∈ X, ∃ M ∈ Y, z ∈ L ∧ z ∈ M := by
  simp only [grid,mem_biUnion,mem_product,mem_inter,Prod.exists]
  tauto

theorem grid_card {x y : Point} {X Y : Finset Line}
    (hx : ∀ L ∈ X, L ∈ B.through x ∧ y ∉ L)
    (hy : ∀ M ∈ Y, M ∈ B.through y ∧ x ∉ M) :
    (grid X Y).card = X.card*Y.card := by
  rw [grid,card_biUnion]
  · have h (t : Line × Line) (ht : t ∈ X ×ˢ Y) : (t.1∩t.2).card = 1 := by
      obtain ⟨hL,hM⟩ := mem_product.mp ht
      obtain ⟨hL',hyL⟩ := hx t.1 hL
      obtain ⟨hM',_⟩ := hy t.2 hM
      exact B.meet_eq _ (B.mem_through.mp hL').1 _ (B.mem_through.mp hM').1
        (fun eq => hyL (eq ▸ (B.mem_through.mp hM').2))
    rw [sum_congr rfl h,sum_const,nsmul_eq_mul,mul_one,card_product]
    rfl
  · intro t ht u hu hne
    obtain ⟨hL,hM⟩ := mem_product.mp ht
    obtain ⟨hL',hM'⟩ := mem_product.mp hu
    obtain ⟨hLt,hyL⟩ := hx t.1 hL
    obtain ⟨hMt,hxM⟩ := hy t.2 hM
    obtain ⟨hLu,_⟩ := hx u.1 hL'
    obtain ⟨hMu,_⟩ := hy u.2 hM'
    apply disjoint_left.mpr
    intro z hz hz'
    obtain ⟨hzL,hzM⟩ := mem_inter.mp hz
    obtain ⟨hzL',hzM'⟩ := mem_inter.mp hz'
    have hzx : z ≠ x := fun eq => hxM (eq ▸ hzM)
    have hzy : z ≠ y := fun eq => hyL (eq ▸ hzL)
    refine hne (Prod.ext ?_ ?_)
    · exact B.line_unique (B.mem_through.mp hLt).1 (B.mem_through.mp hLu).1 hzx
        hzL hzL' (B.mem_through.mp hLt).2 (B.mem_through.mp hLu).2
    · exact B.line_unique (B.mem_through.mp hMt).1 (B.mem_through.mp hMu).1 hzy
        hzM hzM' (B.mem_through.mp hMt).2 (B.mem_through.mp hMu).2

theorem common_joined_uncovered {x y : Point} (hxy : y ∈ B.missing x) :
    (B.joined x ∩ B.joined y).card = B.degree x * B.degree y := by
  have hNe := (B.mem_missing.mp hxy).1
  have hNot := (B.mem_missing.mp hxy).2
  have hX (L : Line) (hL : L ∈ B.through x) : L ∈ B.through x ∧ y ∉ L :=
    ⟨hL,fun hy => hNot (B.mem_joined.mpr
      ⟨hNe,L,(B.mem_through.mp hL).1,(B.mem_through.mp hL).2,hy⟩)⟩
  have hY (M : Line) (hM : M ∈ B.through y) : M ∈ B.through y ∧ x ∉ M :=
    ⟨hM,fun hx => hNot (B.mem_joined.mpr
      ⟨hNe,M,(B.mem_through.mp hM).1,hx,(B.mem_through.mp hM).2⟩)⟩
  have hEq : B.joined x ∩ B.joined y = grid (B.through x) (B.through y) := by
    ext z
    rw [mem_inter,mem_grid]
    constructor
    · rintro ⟨hzX,hzY⟩
      obtain ⟨_,L,hL,hxL,hzL⟩ := B.mem_joined.mp hzX
      obtain ⟨_,M,hM,hyM,hzM⟩ := B.mem_joined.mp hzY
      exact ⟨L,B.mem_through.mpr ⟨hL,hxL⟩,M,B.mem_through.mpr ⟨hM,hyM⟩,hzL,hzM⟩
    · rintro ⟨L,hL,M,hM,hzL,hzM⟩
      refine ⟨B.mem_joined.mpr ⟨fun eq => (hY _ hM).2 (eq ▸ hzM),L,?_⟩,
        B.mem_joined.mpr ⟨fun eq => (hX _ hL).2 (eq ▸ hzL),M,?_⟩⟩
      · exact ⟨(B.mem_through.mp hL).1,(B.mem_through.mp hL).2,hzL⟩
      · exact ⟨(B.mem_through.mp hM).1,(B.mem_through.mp hM).2,hzM⟩
  rw [hEq,B.grid_card hX hY]
  rfl

theorem common_joined_covered {x y : Point} (hxy : y ∈ B.joined x) :
    (B.joined x ∩ B.joined y).card =
      (B.degree x-1)*(B.degree y-1)+11 := by
  obtain ⟨hne,L,hL,hx,hy⟩ := B.mem_joined.mp hxy
  let X := (B.through x).erase L
  let Y := (B.through y).erase L
  have hX (K : Line) (hK : K ∈ X) : K ∈ B.through x ∧ y ∉ K := by
    obtain ⟨hKL,hK⟩ := mem_erase.mp hK
    refine ⟨hK,fun hbad => hKL ?_⟩
    exact B.line_unique (B.mem_through.mp hK).1 hL hne hbad hy (B.mem_through.mp hK).2 hx
  have hY (K : Line) (hK : K ∈ Y) : K ∈ B.through y ∧ x ∉ K := by
    obtain ⟨hKL,hK⟩ := mem_erase.mp hK
    refine ⟨hK,fun hbad => hKL ?_⟩
    exact B.line_unique (B.mem_through.mp hK).1 hL hne (B.mem_through.mp hK).2 hy hbad hx
  let R := (L.erase x).erase y
  have hEq : B.joined x ∩ B.joined y = grid X Y ∪ R := by
    ext z
    rw [mem_inter,mem_union]
    constructor
    · rintro ⟨hzX,hzY⟩
      obtain ⟨hzx,K,hK,hxK,hzK⟩ := B.mem_joined.mp hzX
      obtain ⟨hzy,M,hM,hyM,hzM⟩ := B.mem_joined.mp hzY
      by_cases hZL : z ∈ L
      · exact Or.inr (mem_erase.mpr ⟨hzy,mem_erase.mpr ⟨hzx,hZL⟩⟩)
      · exact Or.inl (mem_grid.mpr ⟨K,mem_erase.mpr ⟨fun h => hZL (h ▸ hzK),
          B.mem_through.mpr ⟨hK,hxK⟩⟩,
          M,mem_erase.mpr ⟨fun h => hZL (h ▸ hzM),B.mem_through.mpr ⟨hM,hyM⟩⟩,hzK,hzM⟩)
    · rintro (hg|hr)
      · obtain ⟨K,hK,M,hM,hzK,hzM⟩ := mem_grid.mp hg
        obtain ⟨hK',hyK⟩ := hX K hK
        obtain ⟨hM',hxM⟩ := hY M hM
        exact ⟨B.mem_joined.mpr ⟨fun eq => hxM (eq ▸ hzM),K,
          (B.mem_through.mp hK').1,(B.mem_through.mp hK').2,hzK⟩,
          B.mem_joined.mpr ⟨fun eq => hyK (eq ▸ hzK),M,
            (B.mem_through.mp hM').1,(B.mem_through.mp hM').2,hzM⟩⟩
      · obtain ⟨hzy,hr'⟩ := mem_erase.mp hr
        obtain ⟨hzx,hzL⟩ := mem_erase.mp hr'
        exact ⟨B.mem_joined.mpr ⟨hzx,L,hL,hx,hzL⟩, B.mem_joined.mpr ⟨hzy,L,hL,hy,hzL⟩⟩
  have hDj : Disjoint (grid X Y) R := by
    apply disjoint_left.mpr
    intro z hz hR
    obtain ⟨K,hK,M,hM,hzK,hzM⟩ := mem_grid.mp hz
    have hzL := (mem_erase.mp (mem_erase.mp hR).2).2
    have hzx := (mem_erase.mp (mem_erase.mp hR).2).1
    have hKT := (hX K hK).1
    have hKL := (mem_erase.mp hK).1
    exact hzx (B.intersection_unique (B.mem_through.mp hKT).1 hL hKL
      hzK hzL (B.mem_through.mp hKT).2 hx)
  have hRc : R.card = 11 := by
    dsimp [R]
    rw [card_erase_of_mem (mem_erase.mpr ⟨hne,hy⟩),card_erase_of_mem hx,B.size_eq L hL]
  rw [hEq,card_union_of_disjoint hDj,B.grid_card hX hY,hRc]
  dsimp [X,Y,degree]
  rw [card_erase_of_mem (B.mem_through.mpr ⟨hL,hx⟩), card_erase_of_mem (B.mem_through.mpr ⟨hL,hy⟩)]

theorem common_missing {x y : Point} (hx : B.degree x = 11) (hy : B.degree y = 11)
    (hne : y ≠ x) :
    (B.missing x ∩ B.missing y).card = if y ∈ B.joined x then 4 else 12 := by
  let X := insert x (B.joined x)
  let Y := insert y (B.joined y)
  have hX : X.card = 133 := by rw [show X = insert x (B.joined x) from rfl,
    card_insert_of_notMem (B.self_not_joined x),B.joined_card,hx]
  have hY : Y.card = 133 := by rw [show Y = insert y (B.joined y) from rfl,
    card_insert_of_notMem (B.self_not_joined y),B.joined_card,hy]
  have hcomp : B.missing x ∩ B.missing y = univ \ (X∪Y) := by
    ext z
    simp only [missing,mem_inter,mem_sdiff,mem_univ,true_and,mem_union,X,Y]
    tauto
  have hC := card_union_add_card_inter X Y
  rw [hX,hY] at hC
  rw [hcomp,card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin]
  by_cases hJ : y ∈ B.joined x
  · rw [if_pos hJ]
    have hK := B.joined_symm.mp hJ
    have hEq : X∩Y = insert x (insert y (B.joined x ∩ B.joined y)) := by
      ext z
      simp only [X,Y,mem_inter,mem_insert]
      by_cases hzx : z=x
      · subst z; simp [hK]
      by_cases hzy : z=y
      · subst z; simp [hJ]
      simp [hzx,hzy]
    have hNotX : x ∉ insert y (B.joined x ∩ B.joined y) := by
      simp [hne.symm,B.self_not_joined]
    have hNotY : y ∉ B.joined x ∩ B.joined y := by simp [B.self_not_joined]
    have h : (X∩Y).card = 113 := by
      rw [hEq,card_insert_of_notMem hNotX,card_insert_of_notMem hNotY,
        B.common_joined_covered hJ,hx,hy]
    omega
  · rw [if_neg hJ]
    have hK : x ∉ B.joined y := fun h => hJ (B.joined_symm.mpr h)
    have hEq : X∩Y = B.joined x ∩ B.joined y := by
      ext z
      simp only [X,Y,mem_inter,mem_insert]
      by_cases hzx : z=x
      · subst z; simp [hne.symm,hK]
      by_cases hzy : z=y
      · subst z; simp [hne,hJ]
      simp [hzx,hzy]
    have h : (X∩Y).card = 121 := by
      rw [hEq,B.common_joined_uncovered (B.mem_missing.mpr ⟨hne,hJ⟩),hx,hy]
    omega

theorem joined_away_from_line {x : Point} {L : Line} (hL : L ∈ B.lines) (hx : x ∉ L) :
    (B.joined x ∩ L).card = B.degree x := by
  have hEq : B.joined x ∩ L = (B.through x).biUnion (fun K => K ∩ L) := by
    ext y
    rw [mem_inter, mem_biUnion]
    constructor
    · rintro ⟨hJ,hYL⟩
      obtain ⟨_,K,hK,hXK,hYK⟩ := B.mem_joined.mp hJ
      exact ⟨K,B.mem_through.mpr ⟨hK,hXK⟩,mem_inter.mpr ⟨hYK,hYL⟩⟩
    · rintro ⟨K,hK,hYK⟩
      obtain ⟨hK',hXK⟩ := B.mem_through.mp hK
      obtain ⟨hyK,hyL⟩ := mem_inter.mp hYK
      exact ⟨B.mem_joined.mpr ⟨fun h => hx (h ▸ hyL),K,hK',hXK,hyK⟩,hyL⟩
  rw [hEq,card_biUnion]
  · have hc (K : Line) (hK : K ∈ B.through x) : (K ∩ L).card = 1 := by
      obtain ⟨hK',hxK⟩ := B.mem_through.mp hK
      exact B.meet_eq K hK' L hL (fun h => hx (h ▸ hxK))
    rw [sum_congr rfl hc,sum_const,nsmul_eq_mul,mul_one,degree]
    rfl
  · intro K hK M hM hne
    obtain ⟨hk,hxK⟩ := B.mem_through.mp hK
    obtain ⟨hm,hxM⟩ := B.mem_through.mp hM
    apply disjoint_left.mpr
    intro y hyK hyM
    have hY := B.intersection_unique hk hm hne
      (mem_inter.mp hyK).1 (mem_inter.mp hyM).1 hxK hxM
    exact hx (hY ▸ (mem_inter.mp hyK).2)

theorem line_of_degree_twelve {x : Point} (hx : B.degree x = 12) :
    ∃ M : Line, M.card = 13 ∧ ∀ L ∈ B.lines, (M∩L).card = 1 := by
  let M := insert x (B.missing x)
  have hCard : M.card = 13 := by
    dsimp [M]
    rw [card_insert_of_notMem (B.self_not_missing x),B.missing_card,hx]
  refine ⟨M,hCard,?_⟩
  intro L hL
  by_cases hxL : x ∈ L
  · have hEq : M∩L = {x} := by
      ext y
      simp only [M,mem_inter,mem_insert,mem_singleton]
      constructor
      · rintro ⟨hy|hy,hyL⟩
        · exact hy
        · exact ((B.mem_missing.mp hy).2 (B.mem_joined.mpr
            ⟨(B.mem_missing.mp hy).1,L,hL,hxL,hyL⟩)).elim
      · rintro rfl
        exact ⟨Or.inl rfl,hxL⟩
    rw [hEq,card_singleton]
  · have hEq : M∩L = L \ B.joined x := by
      ext y
      simp only [M,mem_inter,mem_insert,mem_sdiff,B.mem_missing]
      by_cases hy : y=x
      · subst y; simp [hxL]
      · simp [hy,and_comm]
    rw [hEq,card_sdiff,B.size_eq L hL,B.joined_away_from_line hL hxL,hx]

theorem missing_degree_eleven {x : Point}
    (hTypes : ∀ v, B.degree v = 13 ∨ B.degree v = 11) {a : Point} (ha : a ∈ B.missing x) :
    B.degree a = 11 := by
  have ha' := B.missing_symm.mp ha
  have hPos : 0 < (B.missing a).card := card_pos.mpr ⟨x,ha'⟩
  rw [B.missing_card] at hPos
  exact (hTypes a).resolve_left (fun h => by simp [h] at hPos)

theorem regular_neighborhood {x : Point} (hx : B.degree x = 11)
    (hTypes : ∀ v, B.degree v = 13 ∨ B.degree v = 11) {a : Point} (ha : a ∈ B.missing x) :
    ((B.missing x).filter (· ∈ B.joined a)).card = 11 := by
  let U := B.missing x
  have hU : U.card = 24 := by dsimp [U]; rw [B.missing_card,hx]
  have hA := B.missing_degree_eleven hTypes ha
  have hCommon : (U ∩ B.missing a).card = 12 := by
    dsimp [U]
    rw [B.common_missing hx hA (B.mem_missing.mp ha).1,if_neg (B.mem_missing.mp ha).2]
  have hSdif : (U.filter (· ∈ B.joined a)) = U.erase a \ B.missing a := by
    ext z
    simp only [mem_filter,mem_erase,mem_sdiff]
    by_cases hz : z=a
    · subst z; simp [B.self_not_joined]
    · simp [B.mem_missing,hz]
  have hEq : U.erase a ∩ B.missing a = U ∩ B.missing a := by
    ext z
    simp only [mem_erase,mem_inter]
    constructor
    · tauto
    · rintro ⟨hU',hM⟩
      exact ⟨⟨(B.mem_missing.mp hM).1,hU'⟩,hM⟩
  change (U.filter (· ∈ B.joined a)).card = 11
  rw [hSdif,card_sdiff, inter_comm (B.missing a) (U.erase a),hEq,hCommon,card_erase_of_mem ha,hU]

theorem neighborhood_no_triangle {x : Point} (hx : B.degree x = 11)
    (hTypes : ∀ v, B.degree v = 13 ∨ B.degree v = 11)
    {a b c : Point} (ha : a ∈ B.missing x) (hb : b ∈ B.missing x) (hc : c ∈ B.missing x)
    (hab : b ∈ B.joined a) (hac : c ∈ B.joined a) (hbc : c ∈ B.joined b) : False := by
  let U := B.missing x
  have hU : U.card = 24 := by dsimp [U]; rw [B.missing_card,hx]
  let Q (p : Point) := insert p (U ∩ B.missing p)
  have hSub {p : Point} (hp : p ∈ U) : Q p ⊆ U := insert_subset_iff.mpr ⟨hp,inter_subset_left⟩
  have hCard {p : Point} (hp : p ∈ U) : (Q p).card = 13 := by
    have hno : p ∉ U ∩ B.missing p := by simp [B.self_not_missing]
    dsimp [Q]
    rw [card_insert_of_notMem hno,B.common_missing hx (B.missing_degree_eleven hTypes hp)
      (B.mem_missing.mp hp).1,if_neg (B.mem_missing.mp hp).2]
  have hInt {p q : Point} (hp : p ∈ U) (hq : q ∈ U) (hpq : q ∈ B.joined p) :
      (Q p ∩ Q q).card ≤ 3 := by
    have hC : (B.missing p ∩ B.missing q).card = 4 := by
      rw [B.common_missing (B.missing_degree_eleven hTypes hp)
        (B.missing_degree_eleven hTypes hq) (B.mem_joined.mp hpq).1,if_pos hpq]
    have hX : x ∈ B.missing p ∩ B.missing q :=
      mem_inter.mpr ⟨B.missing_symm.mp hp,B.missing_symm.mp hq⟩
    have hS : Q p ∩ Q q ⊆ (B.missing p ∩ B.missing q).erase x := by
      intro z hz
      obtain ⟨hzP,hzQ⟩ := mem_inter.mp hz
      have hzU := hSub hp hzP
      obtain hzP' | hzP' := mem_insert.mp hzP
      · subst z
        obtain hpq' | hpq' := mem_insert.mp hzQ
        · exact ((B.mem_joined.mp hpq).1 hpq'.symm).elim
        · exact ((B.mem_missing.mp (mem_inter.mp hpq').2).2
            (B.joined_symm.mp hpq)).elim
      obtain hzQ' | hzQ' := mem_insert.mp hzQ
      · subst z
        exact ((B.mem_missing.mp (mem_inter.mp hzP').2).2 hpq).elim
      exact mem_erase.mpr ⟨(B.mem_missing.mp hzU).1,
        mem_inter.mpr ⟨(mem_inter.mp hzP').2,(mem_inter.mp hzQ').2⟩⟩
    have h := card_le_card hS
    rw [card_erase_of_mem hX,hC] at h
    exact h
  have hUnion : Q a ∪ Q b ∪ Q c ⊆ U := union_subset (union_subset (hSub ha) (hSub hb)) (hSub hc)
  have hSize := card_le_card hUnion
  have habC := card_union_add_card_inter (Q a) (Q b)
  have habcC := card_union_add_card_inter (Q a ∪ Q b) (Q c)
  have hThree : ((Q a ∪ Q b) ∩ Q c).card ≤ 6 := by
    rw [union_inter_distrib_right]
    exact (card_union_le _ _).trans (by have := hInt ha hc hac; have := hInt hb hc hbc; omega)
  rw [hCard ha,hCard hb] at habC
  rw [hCard hc] at habcC
  have := hInt ha hb hab
  omega

end Bundle

theorem independent_in_dense_triangle_free
    (U : Finset Point) (hU : U.card = 24) (R : Point → Point → Prop) [DecidableRel R]
    (hSym : ∀ a b, R a b → R b a)
    (hReg : ∀ a ∈ U, (U.filter (R a)).card = 11)
    (hTriangle : ∀ a ∈ U, ∀ b ∈ U, ∀ c ∈ U, R a b → R a c → R b c → False) :
    ∃ I ⊆ U, I.card = 12 ∧ ∀ a ∈ I, ∀ b ∈ I, ¬ R a b := by
  let N (x : Point) := U.filter (R x)
  have hNS (x : Point) : N x ⊆ U := filter_subset _ _
  have hN {x y : Point} : y ∈ N x ↔ y ∈ U ∧ R x y := mem_filter
  have hDisj {a b : Point} (ha : a ∈ U) (hb : b ∈ U) (hab : R a b) :
      Disjoint (N a) (N b) := by
    apply disjoint_left.mpr
    intro z hza hzb
    exact hTriangle a ha b hb z (hN.mp hza).1 hab (hN.mp hza).2 (hN.mp hzb).2
  obtain ⟨x,hx⟩ : U.Nonempty := card_pos.mp (by omega)
  obtain ⟨y,hy⟩ : (N x).Nonempty := card_pos.mp (by change 0 < (U.filter (R x)).card; rw [hReg x hx]; decide)
  have hyU := (hN.mp hy).1
  let A := N x
  let B := N y
  let C := U \ (A∪B)
  have haC : A.card = 11 := hReg x hx
  have hbC : B.card = 11 := hReg y hyU
  have hAB : Disjoint A B := hDisj hx hyU (hN.mp hy).2
  have hABsub : A∪B ⊆ U := union_subset (hNS _) (hNS _)
  have hcC : C.card = 2 := by
    dsimp [C]
    rw [card_sdiff_of_subset hABsub,hU,card_union_of_disjoint hAB,haC,hbC]
  have hCS : C ⊆ U := sdiff_subset
  have hCover : U ⊆ A ∪ B ∪ C := by
    intro z hz
    by_cases h : z ∈ A∪B
    · exact mem_union_left _ h
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hz,h⟩)
  have hAi {a b : Point} (ha : a ∈ A) (hb : b ∈ A) : ¬ R a b :=
    hTriangle x hx a (hN.mp ha).1 b (hN.mp hb).1 (hN.mp ha).2 (hN.mp hb).2
  have hBi {a b : Point} (ha : a ∈ B) (hb : b ∈ B) : ¬ R a b :=
    hTriangle y hyU a (hN.mp ha).1 b (hN.mp hb).1 (hN.mp ha).2 (hN.mp hb).2
  have hMany {S T : Finset Point} (hPart : U ⊆ S ∪ T ∪ C) {z : Point} (hz : z ∈ U)
      (hNo : Disjoint (N z) S) : 9 ≤ (N z ∩ T).card := by
    have hsub : N z ⊆ (N z ∩ T) ∪ C := by
      intro w hw
      obtain hAB'|hC := mem_union.mp (hPart (hNS z hw))
      · obtain hS|hT := mem_union.mp hAB'
        · exact (disjoint_left.mp hNo hw hS).elim
        · exact mem_union_left _ (mem_inter.mpr ⟨hw,hT⟩)
      · exact mem_union_right _ hC
    have hSize := (card_le_card hsub).trans (card_union_le _ _)
    change (U.filter (R z)).card ≤ _ at hSize
    rw [hReg z hz,hcC] at hSize
    omega
  have hCover' : U ⊆ B ∪ A ∪ C := by simpa only [union_comm A B] using hCover
  have hAN {a : Point} (ha : a ∈ A) : 9 ≤ (N a ∩ B).card :=
    hMany hCover (hNS x ha) (disjoint_left.mpr (fun _ hw hA => hAi ha hA (hN.mp hw).2))
  have hBN {b : Point} (hb : b ∈ B) : 9 ≤ (N b ∩ A).card :=
    hMany hCover' (hNS y hb) (disjoint_left.mpr (fun _ hw hB => hBi hb hB (hN.mp hw).2))
  have hAtMostTwo {D : Finset Point} (hD : D.card = 11) {a z : Point}
      (ha : a ∈ U) (hz : z ∈ U) (hza : R z a) (hMany' : 9 ≤ (N a∩D).card) :
      (N z∩D).card ≤ 2 := by
    have hj : Disjoint (N z∩D) (N a∩D) := (hDisj hz ha hza).mono inter_subset_left inter_subset_left
    have hc := card_le_card (show (N z∩D)∪(N a∩D) ⊆ D from union_subset inter_subset_right inter_subset_right)
    rw [card_union_of_disjoint hj,hD] at hc
    omega
  have hNoMix {z : Point} (hz : z ∈ C) :
      Disjoint (N z) A ∨ Disjoint (N z) B := by
    by_contra! h
    have hZU := hCS hz
    obtain ⟨a,haN,haA⟩ := not_disjoint_iff.mp h.1
    obtain ⟨b,hbN,hbB⟩ := not_disjoint_iff.mp h.2
    have hA2 := hAtMostTwo haC (hNS y hbB) hZU (hN.mp hbN).2 (hBN hbB)
    have hB2 := hAtMostTwo hbC (hNS x haA) hZU (hN.mp haN).2 (hAN haA)
    have hSub : N z ⊆ (N z∩A)∪(N z∩B)∪C := by
      intro w hw
      obtain (hAB'|hC) := mem_union.mp (hCover (hNS z hw))
      · obtain (hA|hB) := mem_union.mp hAB'
        · exact mem_union_left _ (mem_union_left _ (mem_inter.mpr ⟨hw,hA⟩))
        · exact mem_union_left _ (mem_union_right _ (mem_inter.mpr ⟨hw,hB⟩))
      · exact mem_union_right _ hC
    have hcard := (card_le_card hSub).trans (card_union_le _ _)
    change (U.filter (R z)).card ≤ _ at hcard
    rw [hReg z hZU,hcC] at hcard
    have hAdd := card_union_le (N z∩A) (N z∩B)
    omega
  classical
  let C₁ := C.filter (fun z => Disjoint (N z) A)
  let C₂ := C \ C₁
  have hC₁ {z : Point} (hz : z ∈ C₁) : z ∈ U ∧ Disjoint (N z) A :=
    ⟨hCS (mem_filter.mp hz).1,(mem_filter.mp hz).2⟩
  have hC₂ {z : Point} (hz : z ∈ C₂) : z ∈ U ∧ Disjoint (N z) B := by
    obtain ⟨hzC,hno⟩ := mem_sdiff.mp hz
    exact ⟨hCS hzC,(hNoMix hzC).resolve_left (fun h => hno (mem_filter.mpr ⟨hzC,h⟩))⟩
  have hExtend {S T D : Finset Point} (hPart : U ⊆ S∪T∪C)
      (hTc : T.card = 11) (hS : S ⊆ U)
      (hInd : ∀ a ∈ S, ∀ b ∈ S, ¬R a b)
      (hD : ∀ z ∈ D, z ∈ U ∧ Disjoint (N z) S) :
      ∀ a ∈ S∪D, ∀ b ∈ S∪D, ¬ R a b := by
    intro a ha b hb hab
    rcases mem_union.mp ha with ha|ha <;> rcases mem_union.mp hb with hb|hb
    · exact hInd a ha b hb hab
    · exact disjoint_left.mp (hD b hb).2 (hN.mpr ⟨hS ha,hSym a b hab⟩) ha
    · exact disjoint_left.mp (hD a ha).2 (hN.mpr ⟨hS hb,hab⟩) hb
    · have hA := hMany hPart (hD a ha).1 (hD a ha).2
      have hB := hMany hPart (hD b hb).1 (hD b hb).2
      have hSub : (N a∩T)∪(N b∩T) ⊆ T := union_subset inter_subset_right inter_subset_right
      have hCard := card_le_card hSub
      rw [card_union_of_disjoint ((hDisj (hD a ha).1 (hD b hb).1 hab).mono inter_subset_left inter_subset_left),hTc] at hCard
      omega
  let X := A∪C₁
  let Y := B∪C₂
  have hX : X ⊆ U := union_subset (hNS x) (fun _ h => (hC₁ h).1)
  have hY : Y ⊆ U := union_subset (hNS y) (fun _ h => (hC₂ h).1)
  have hXi : ∀ a ∈ X, ∀ b ∈ X, ¬R a b :=
    hExtend hCover hbC (hNS x) (fun _ ha _ hb => hAi ha hb) (fun _ h => hC₁ h)
  have hYi : ∀ a ∈ Y, ∀ b ∈ Y, ¬R a b :=
    hExtend hCover' haC (hNS y) (fun _ ha _ hb => hBi ha hb) (fun _ h => hC₂ h)
  have hTotal : U ⊆ X∪Y := by
    intro z hz
    rcases mem_union.mp (hCover hz) with h|hC
    · rcases mem_union.mp h with hA|hB
      · exact mem_union_left _ (mem_union_left _ hA)
      · exact mem_union_right _ (mem_union_left _ hB)
    · by_cases h : z ∈ C₁
      · exact mem_union_left _ (mem_union_right _ h)
      · exact mem_union_right _ (mem_union_right _ (mem_sdiff.mpr ⟨hC,h⟩))
  have hCards := (card_le_card hTotal).trans (card_union_le X Y)
  rw [hU] at hCards
  by_cases h : 12 ≤ X.card
  · obtain ⟨I,hI,hIC⟩ := exists_subset_card_eq h
    exact ⟨I,hI.trans hX,hIC,fun a ha b hb => hXi a (hI ha) b (hI hb)⟩
  · obtain ⟨I,hI,hIC⟩ := exists_subset_card_eq (show 12 ≤ Y.card by omega)
    exact ⟨I,hI.trans hY,hIC,fun a ha b hb => hYi a (hI ha) b (hI hb)⟩

theorem boundary_line (B : Bundle) (hb : B.lines.card = 143)
    (hTypes : ∀ v, B.degree v = 13 ∨ B.degree v = 11) :
    ∃ M : Line, M.card = 13 ∧ ∀ L ∈ B.lines, (M∩L).card = 1 := by
  have hX : ∃ x, B.degree x = 11 := by
    by_contra! h
    have hAll (x : Point) : B.degree x = 13 := (hTypes x).resolve_right (h x)
    have he := B.deficit_total
    have hZero (x : Point) : B.deficit x = 0 := by simp [Bundle.deficit,hAll x]
    norm_num [hZero,hb] at he
  obtain ⟨x,hx⟩ := hX
  let U := B.missing x
  have hU : U.card = 24 := by dsimp [U]; rw [B.missing_card,hx]
  obtain ⟨I,hIU,hIcard,hI⟩ := independent_in_dense_triangle_free U hU
    (fun a b => b ∈ B.joined a)
    (fun _ _ h => B.joined_symm.mp h)
    (fun _ ha => B.regular_neighborhood hx hTypes ha)
    (fun _ ha _ hb _ hc => B.neighborhood_no_triangle hx hTypes ha hb hc)
  let M := insert x I
  have hxI : x ∉ I := fun h => B.self_not_missing x (hIU h)
  have hM : M.card = 13 := by dsimp [M]; rw [card_insert_of_notMem hxI,hIcard]
  have hDeg {a : Point} (ha : a ∈ M) : B.degree a = 11 := by
    rcases mem_insert.mp ha with h|h
    · rwa [h]
    · exact B.missing_degree_eleven hTypes (hIU h)
  have hNo {a b : Point} (ha : a ∈ M) (hb : b ∈ M) : b ∉ B.joined a := by
    rcases mem_insert.mp (show a ∈ insert x I from ha) with hax|haI
    · subst a
      rcases mem_insert.mp (show b ∈ insert x I from hb) with hbx|hbI
      · subst b
        exact B.self_not_joined _
      · exact (B.mem_missing.mp (hIU hbI)).2
    · rcases mem_insert.mp (show b ∈ insert x I from hb) with hbx|hbI
      · subst b
        intro h
        exact (B.mem_missing.mp (hIU haI)).2 (B.joined_symm.mp h)
      · exact hI a haI b hbI
  have hAtMost (L : Line) (hL : L ∈ B.lines) : (M∩L).card ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    by_contra hne
    obtain ⟨haM,haL⟩ := mem_inter.mp ha
    obtain ⟨hbM,hbL⟩ := mem_inter.mp hb
    exact hNo haM hbM (B.mem_joined.mpr ⟨Ne.symm hne,L,hL,haL,hbL⟩)
  have he := B.degree_sum_weighted M (fun _ => 1)
  have he' : (∑ a ∈ M, (B.degree a : ℝ)) =
      ∑ L ∈ B.lines, ((M∩L).card : ℝ) := by simpa using he
  have hSum : (∑ L ∈ B.lines, ((M∩L).card : ℝ)) = B.lines.card := by
    rw [← he',hb]
    calc
      _ = ∑ _ ∈ M, (11 : ℝ) := by
        apply sum_congr rfl
        intro a ha
        rw [hDeg ha]
        norm_num
      _ = _ := by
        rw [sum_const,nsmul_eq_mul,hM]
        norm_num
  refine ⟨M,hM,?_⟩
  intro L hL
  by_contra hne
  have hZ : (M∩L).card = 0 := by have := hAtMost L hL; omega
  have hLt : (∑ K ∈ B.lines, ((M∩K).card : ℝ)) < ∑ _ ∈ B.lines,(1 : ℝ) :=
    sum_lt_sum (fun K hK => by exact_mod_cast hAtMost K hK)
      ⟨L,hL,by simp [hZ]⟩
  rw [hSum,sum_const,nsmul_eq_mul,mul_one] at hLt
  exact (lt_irrefl _) hLt

theorem one_more_line (B : Bundle) (hb : 143 ≤ B.lines.card) (ht : B.lines.card < 157) :
    ∃ M : Line, M.card = 13 ∧ ∀ L ∈ B.lines, (M∩L).card = 1 := by
  by_cases ex : ∃ x, B.degree x = 12
  · obtain ⟨x,hx⟩ := ex
    exact B.line_of_degree_twelve hx
  have all : ∀ x, B.degree x ≠ 12 := fun x h => ex ⟨x,h⟩
  obtain ⟨hb',hTypes⟩ := B.degree_boundary hb ht all
  exact boundary_line B hb' hTypes

theorem extend (S : Finset Line) (hb : 143 ≤ S.card) (ht : S.card < 157)
    (hs : ∀ b ∈ S, b.card = 13)
    (hm : ∀ b ∈ S, ∀ c ∈ S, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c) :
    ∃ T : Finset Line, S ⊆ T ∧ T.card = S.card+1 ∧
      (∀ b ∈ T, b.card = 13) ∧
      ∀ b ∈ T, ∀ c ∈ T, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c := by
  have hMeet (b : Line) (hb : b ∈ S) (c : Line) (hc : c ∈ S) (hne : b ≠ c) :
      (b∩c).card = 1 := by
    obtain ⟨x,hx,hUn⟩ := hm b hb c hc hne
    apply card_eq_one.mpr
    refine ⟨x,?_⟩
    ext z
    simp only [mem_inter,mem_singleton]
    exact ⟨fun hz => hUn z hz,fun h => h.symm ▸ hx⟩
  let B : Bundle := ⟨S,hs,hMeet⟩
  obtain ⟨M,hM,hMC⟩ := one_more_line B hb ht
  have hOut : M ∉ S := by
    intro hIn
    have h := hMC M hIn
    rw [inter_self,hM] at h
    omega
  have witness {b c : Line} (h : (b∩c).card=1) : ∃! x, x∈b ∧ x∈c := by
    obtain ⟨x,hx⟩ := card_eq_one.mp h
    refine ⟨x,mem_inter.mp (by simp [hx]),fun y hy => ?_⟩
    have hY := mem_inter.mpr hy
    simpa [hx] using hY
  refine ⟨insert M S,subset_insert _ _,card_insert_of_notMem hOut,?_,?_⟩
  · intro b hb
    rcases mem_insert.mp hb with rfl|h
    · exact hM
    · exact hs b h
  · intro b hb c hc hne
    rcases mem_insert.mp hb with hbM|hbS
    · subst b
      rcases mem_insert.mp hc with hcM|hcS
      · exact (hne hcM.symm).elim
      · exact witness (hMC c hcS)
    · rcases mem_insert.mp hc with hcM|hcS
      · subst c
        exact witness (by rw [inter_comm]; exact hMC b hbS)
      · exact hm b hbS c hcS hne

end OMA.OrderTwelveCompletion


theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_eq_12_R1.H2 :=
  OMA.OrderTwelveCompletion.extend

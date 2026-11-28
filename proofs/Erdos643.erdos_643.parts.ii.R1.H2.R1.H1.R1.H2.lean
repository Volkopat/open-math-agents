import OMAReductions.R_Erdos643_erdos_643_parts_ii_R1_H2_R1_H1_R1
import Mathlib

/-!
# A graph-deletion lemma with compatibility (HMY, Lemma 6.1)

Bipartite graph `H ⊆ X × Y`, with a symmetric compatibility relation on `X`.
Given target pairs `PX` (in `X`) and `PY` (in `Y`) such that every diagonal outside the targets
is compatible, delete at most `|PX| + |PY| + |𝒯(H)|` edges so that every incompatible target
pair in `X` has no common neighbour.
-/

namespace OMA_DL

open Finset

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

section Defs

variable (H : Finset (X × Y))

def NY (x : X) : Finset Y := univ.filter (fun y => (x, y) ∈ H)
def NX (y : Y) : Finset X := univ.filter (fun x => (x, y) ∈ H)
def cdX (x x' : X) : ℕ := (NY H x ∩ NY H x').card
def cdY (y y' : Y) : ℕ := (NX H y ∩ NX H y').card

@[simp] lemma mem_NY {x : X} {y : Y} : y ∈ NY H x ↔ (x, y) ∈ H := by simp [NY]
@[simp] lemma mem_NX {x : X} {y : Y} : x ∈ NX H y ↔ (x, y) ∈ H := by simp [NX]

lemma cdX_comm (x x' : X) : cdX H x x' = cdX H x' x := by simp [cdX, inter_comm]
lemma cdY_comm (y y' : Y) : cdY H y y' = cdY H y' y := by simp [cdY, inter_comm]

variable (compat : X → X → Prop)

/-- Every diagonal outside the targets is compatible. -/
def Inv (PX : Finset (Sym2 X)) (PY : Finset (Sym2 Y)) : Prop :=
  (∀ a b : X, a ≠ b → 2 ≤ cdX H a b → s(a, b) ∉ PX → compat a b) ∧
  (∀ c d : Y, c ≠ d → 2 ≤ cdY H c d → s(c, d) ∉ PY →
    ∀ a ∈ NX H c ∩ NX H d, ∀ b ∈ NX H c ∩ NX H d, a ≠ b → compat a b)

open scoped Classical in
/-- Ordered compatible chains `x₁ ↔ x₂ ↔ x₃` of diagonals with a common neighbour. -/
noncomputable def Tset : Finset (X × X × X) :=
  univ.filter (fun p : X × X × X => p.1 ≠ p.2.1 ∧ p.2.1 ≠ p.2.2 ∧ p.1 ≠ p.2.2 ∧
    2 ≤ cdX H p.1 p.2.1 ∧ 2 ≤ cdX H p.2.1 p.2.2 ∧ compat p.1 p.2.1 ∧ compat p.2.1 p.2.2 ∧
    (NY H p.1 ∩ NY H p.2.1 ∩ NY H p.2.2).Nonempty)

end Defs

lemma NY_mono {H H' : Finset (X × Y)} (h : H' ⊆ H) (x : X) : NY H' x ⊆ NY H x := by
  intro y; simp only [mem_NY]; exact fun hy => h hy
lemma NX_mono {H H' : Finset (X × Y)} (h : H' ⊆ H) (y : Y) : NX H' y ⊆ NX H y := by
  intro x; simp only [mem_NX]; exact fun hx => h hx
lemma cdX_mono {H H' : Finset (X × Y)} (h : H' ⊆ H) (x x' : X) : cdX H' x x' ≤ cdX H x x' :=
  card_le_card (inter_subset_inter (NY_mono h x) (NY_mono h x'))
lemma cdY_mono {H H' : Finset (X × Y)} (h : H' ⊆ H) (y y' : Y) : cdY H' y y' ≤ cdY H y y' :=
  card_le_card (inter_subset_inter (NX_mono h y) (NX_mono h y'))

open scoped Classical in
lemma Tset_mono {compat : X → X → Prop} {H H' : Finset (X × Y)} (h : H' ⊆ H) :
    Tset H' compat ⊆ Tset H compat := by
  intro p hp
  simp only [Tset, mem_filter, mem_univ, true_and] at hp ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hp
  refine ⟨h1, h2, h3, h4.trans (cdX_mono h _ _), h5.trans (cdX_mono h _ _), h6, h7, ?_⟩
  obtain ⟨w, hw⟩ := h8
  exact ⟨w, inter_subset_inter (inter_subset_inter (NY_mono h _) (NY_mono h _))
    (NY_mono h _) hw⟩

/-- Two distinct elements in a set of size at least two: one avoids a given point. -/
lemma exists_ne_of_two_le {α : Type*} [DecidableEq α] {s : Finset α} (hs : 2 ≤ s.card) (a : α) :
    ∃ b ∈ s, b ≠ a := by
  by_contra h
  push_neg at h
  have : s ⊆ {a} := fun b hb => mem_singleton.2 (h b hb)
  have := card_le_card this
  simp at this
  omega

lemma two_le_card_of_ne {α : Type*} [DecidableEq α] {s : Finset α} {a b : α} (ha : a ∈ s)
    (hb : b ∈ s) (hab : a ≠ b) : 2 ≤ s.card := by
  have : ({a, b} : Finset α) ⊆ s := by
    intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption
  have h2 := card_le_card this
  rw [card_pair hab] at h2
  exact h2

/-! ## One deletion step -/

section Step

variable {compat : X → X → Prop} (hcs : ∀ a b, compat a b → compat b a)
  {H : Finset (X × Y)} {PX : Finset (Sym2 X)} {PY : Finset (Sym2 Y)}
  (hInv : Inv H compat PX PY)
  {x x' : X} {y : Y} (hxx' : x ≠ x') (hP : s(x, x') ∈ PX) (hxy : (x, y) ∈ H)
  (hx'y : (x', y) ∈ H)

open scoped Classical

/-- The sets of Case 3. -/
noncomputable def sU (PX : Finset (Sym2 X)) (H : Finset (X × Y)) (x : X) (y : Y) : Finset X :=
  univ.filter (fun u => u ≠ x ∧ s(x, u) ∈ PX ∧ (u, y) ∈ H)
noncomputable def sU' (PX : Finset (Sym2 X)) (H : Finset (X × Y)) (x : X) (y : Y) : Finset X :=
  univ.filter (fun u => u ≠ x ∧ s(x, u) ∉ PX ∧ 2 ≤ cdX H x u ∧ (u, y) ∈ H)
noncomputable def sV (PY : Finset (Sym2 Y)) (H : Finset (X × Y)) (x : X) (y : Y) : Finset Y :=
  univ.filter (fun v => v ≠ y ∧ s(y, v) ∈ PY ∧ (x, v) ∈ H)
noncomputable def sV' (PY : Finset (Sym2 Y)) (H : Finset (X × Y)) (x : X) (y : Y) : Finset Y :=
  univ.filter (fun v => v ≠ y ∧ s(y, v) ∉ PY ∧ 2 ≤ cdY H y v ∧ (x, v) ∈ H)
noncomputable def sU'' (compat : X → X → Prop) (PX : Finset (Sym2 X)) (H : Finset (X × Y))
    (x : X) (y : Y) : Finset X :=
  (sU' PX H x y).filter (fun u => ∃ u₂ ∈ sU' PX H x y, u₂ ≠ u ∧ ¬ compat u u₂)
noncomputable def sT (compat : X → X → Prop) (PX : Finset (Sym2 X)) (H : Finset (X × Y))
    (x : X) (y : Y) : Finset (X × X × X) :=
  ((sU' PX H x y ×ˢ sU' PX H x y).filter (fun p => p.1 ≠ p.2 ∧ ¬ compat p.1 p.2)).image
    (fun p => (p.1, x, p.2))
noncomputable def sR (compat : X → X → Prop) (PX : Finset (Sym2 X)) (PY : Finset (Sym2 Y))
    (H : Finset (X × Y)) (x : X) (y : Y) : Finset (X × Y) :=
  (sV PY H x y).image (fun v => (x, v)) ∪
    (sU PX H x y ∪ sU'' compat PX H x y).image (fun u => (u, y))
noncomputable def sPX (PX : Finset (Sym2 X)) (H : Finset (X × Y)) (x : X) (y : Y) :
    Finset (Sym2 X) :=
  PX \ (sU PX H x y).image (fun u => s(x, u))
noncomputable def sPY (PY : Finset (Sym2 Y)) (H : Finset (X × Y)) (x : X) (y : Y) :
    Finset (Sym2 Y) :=
  PY \ (sV PY H x y).image (fun v => s(y, v))

lemma mem_sR {a : X} {b : Y} :
    (a, b) ∈ sR compat PX PY H x y ↔ (a = x ∧ b ∈ sV PY H x y) ∨
      (b = y ∧ (a ∈ sU PX H x y ∨ a ∈ sU'' compat PX H x y)) := by
  simp only [sR, mem_union, mem_image, Prod.mk.injEq]
  constructor
  · rintro (⟨v, hv, rfl, rfl⟩ | ⟨u, hu, rfl, rfl⟩)
    · exact Or.inl ⟨rfl, hv⟩
    · exact Or.inr ⟨rfl, hu⟩
  · rintro (⟨rfl, hb⟩ | ⟨rfl, ha⟩)
    · exact Or.inl ⟨b, hb, rfl, rfl⟩
    · exact Or.inr ⟨a, ha, rfl, rfl⟩

lemma mem_sR_diff {a : X} {b : Y} :
    (a, b) ∈ H \ sR compat PX PY H x y ↔ (a, b) ∈ H ∧ ¬ (a = x ∧ b ∈ sV PY H x y) ∧
      ¬ (b = y ∧ a ∈ sU PX H x y ∪ sU'' compat PX H x y) := by
  rw [mem_sdiff, mem_sR, mem_union]
  tauto

include hInv in
/-- Common neighbours of `x` and a vertex `u` adjacent to `y`: `y` itself, or in `V ∪ V'`. -/
lemma cn_x {u : X} (hux : u ≠ x) (huy : (u, y) ∈ H) (hxy : (x, y) ∈ H) {w : Y}
    (hxw : (x, w) ∈ H) (huw : (u, w) ∈ H) (hwy : w ≠ y) :
    w ∈ sV PY H x y ∨ w ∈ sV' PY H x y := by
  have h2 : 2 ≤ cdY H y w :=
    two_le_card_of_ne (a := x) (b := u) (by simp [hxy, hxw]) (by simp [huy, huw]) hux.symm
  by_cases hp : s(y, w) ∈ PY
  · left; simp [sV, hwy, hp, hxw]
  · right; simp [sV', hwy, hp, h2, hxw]

include hInv in
lemma cn_y {v : Y} (hvy : v ≠ y) (hxv : (x, v) ∈ H) (hxy : (x, y) ∈ H) {z : X}
    (hzy : (z, y) ∈ H) (hzv : (z, v) ∈ H) (hzx : z ≠ x) :
    z ∈ sU PX H x y ∨ z ∈ sU' PX H x y := by
  have h2 : 2 ≤ cdX H x z :=
    two_le_card_of_ne (a := y) (b := v) (by simp [hxy, hzy]) (by simp [hxv, hzv]) hvy.symm
  by_cases hp : s(x, z) ∈ PX
  · left; simp [sU, hzx, hp, hzy]
  · right; simp [sU', hzx, hp, h2, hzy]

include hInv in
/-- The key compatibility fact: common neighbours of `y` and `w ∈ V'` are compatible. -/
lemma kc {w : Y} (hw : w ∈ sV' PY H x y) {a b : X} (hay : (a, y) ∈ H) (haw : (a, w) ∈ H)
    (hby : (b, y) ∈ H) (hbw : (b, w) ∈ H) (hab : a ≠ b) : compat a b := by
  simp only [sV', mem_filter, mem_univ, true_and] at hw
  exact hInv.2 y w hw.1.symm hw.2.2.1 hw.2.1 a (by simp [hay, haw]) b (by simp [hby, hbw]) hab

include hInv in
/-- No common neighbour of `x` and `u ∈ U` survives except through compatibility. -/
lemma step_cd_zero {u : X} (hu : u ∈ sU PX H x y) (hxy : (x, y) ∈ H) (hnc : ¬ compat x u) :
    cdX (H \ sR compat PX PY H x y) x u = 0 := by
  rw [cdX, card_eq_zero, eq_empty_iff_forall_notMem]
  intro w hw
  simp only [mem_inter, mem_NY, mem_sR_diff] at hw
  obtain ⟨⟨hxw, hxV, -⟩, ⟨huw, -, huU⟩⟩ := hw
  have hu' := hu
  simp only [sU, mem_filter, mem_univ, true_and] at hu'
  have hwy : w ≠ y := fun h => huU ⟨h, mem_union_left _ hu⟩
  rcases cn_x hInv hu'.1 hu'.2.2 hxy hxw huw hwy with hV | hV'
  · exact hxV (by simp [hV])
  · exact hnc (kc hInv hV' hxy hxw hu'.2.2 huw hu'.1.symm)

include hInv hcs in
lemma step_inv (hxy : (x, y) ∈ H) :
    Inv (H \ sR compat PX PY H x y) compat (sPX PX H x y) (sPY PY H x y) := by
  constructor
  · intro a b hab h2 hnot
    by_cases hPa : s(a, b) ∈ PX
    · -- `s(a,b) = s(x,u)` with `u ∈ U`
      have : s(a, b) ∈ (sU PX H x y).image (fun u => s(x, u)) := by
        by_contra h; exact hnot (mem_sdiff.2 ⟨hPa, h⟩)
      obtain ⟨u, hu, hue⟩ := mem_image.1 this
      have hu' := hu
      simp only [sU, mem_filter, mem_univ, true_and] at hu'
      have key : compat x u := by
        have h2' : 2 ≤ cdX (H \ sR compat PX PY H x y) x u := by
          rcases Sym2.eq_iff.1 hue with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact h2
          · rwa [cdX_comm]
        obtain ⟨w, hw, hwy⟩ := exists_ne_of_two_le h2' y
        simp only [mem_inter, mem_NY, mem_sR_diff] at hw
        obtain ⟨⟨hxw, hxV, -⟩, ⟨huw, -, -⟩⟩ := hw
        rcases cn_x hInv hu'.1 hu'.2.2 hxy hxw huw hwy with hV | hV'
        · exact absurd (by simp [hV]) hxV
        · exact kc hInv hV' hxy hxw hu'.2.2 huw hu'.1.symm
      rcases Sym2.eq_iff.1 hue with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact key
      · exact hcs _ _ key
    · exact hInv.1 a b hab (h2.trans (cdX_mono sdiff_subset _ _)) hPa
  · intro c d hcd h2 hnot a ha b hb hab
    by_cases hPc : s(c, d) ∈ PY
    · have : s(c, d) ∈ (sV PY H x y).image (fun v => s(y, v)) := by
        by_contra h; exact hnot (mem_sdiff.2 ⟨hPc, h⟩)
      obtain ⟨v, hv, hve⟩ := mem_image.1 this
      have hv' := hv
      simp only [sV, mem_filter, mem_univ, true_and] at hv'
      -- both `a` and `b` lie in `U' \ U''`
      have hin : ∀ z ∈ NX (H \ sR compat PX PY H x y) c ∩ NX (H \ sR compat PX PY H x y) d,
          z ∈ sU' PX H x y ∧ z ∉ sU'' compat PX H x y := by
        intro z hz
        have hz' : (z, y) ∈ H \ sR compat PX PY H x y ∧ (z, v) ∈ H \ sR compat PX PY H x y := by
          simp only [mem_inter, mem_NX] at hz
          rcases Sym2.eq_iff.1 hve with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hz
          · exact ⟨hz.2, hz.1⟩
        rw [mem_sR_diff, mem_sR_diff] at hz'
        obtain ⟨⟨hzy, -, hzU⟩, ⟨hzv, hzV, -⟩⟩ := hz'
        have hzx : z ≠ x := fun h => hzV ⟨h, hv⟩
        have hzU' : z ∉ sU PX H x y ∪ sU'' compat PX H x y := fun h => hzU ⟨rfl, h⟩
        rcases cn_y hInv hv'.1 hv'.2.2 hxy hzy hzv hzx with h | h
        · exact absurd (mem_union_left _ h) hzU'
        · exact ⟨h, fun h' => hzU' (mem_union_right _ h')⟩
      obtain ⟨haU', haU''⟩ := hin a ha
      obtain ⟨hbU', -⟩ := hin b hb
      by_contra hnc
      exact haU'' (mem_filter.2 ⟨haU', b, hbU', hab.symm, hnc⟩)
    · have hsub : NX (H \ sR compat PX PY H x y) c ∩ NX (H \ sR compat PX PY H x y) d ⊆
          NX H c ∩ NX H d := inter_subset_inter (NX_mono sdiff_subset _) (NX_mono sdiff_subset _)
      exact hInv.2 c d hcd (h2.trans (cdY_mono sdiff_subset _ _)) hPc a (hsub ha) b (hsub hb) hab

include hInv hcs in
lemma step_T (hxy : (x, y) ∈ H) :
    (sT compat PX H x y).card + (Tset (H \ sR compat PX PY H x y) compat).card ≤
      (Tset H compat).card := by
  rw [← card_union_of_disjoint]
  · apply card_le_card
    apply union_subset _ (Tset_mono sdiff_subset)
    intro p hp
    obtain ⟨⟨u₁, u₂⟩, hq, rfl⟩ := mem_image.1 hp
    simp only [mem_filter, mem_product] at hq
    obtain ⟨⟨h1, h2⟩, hne, hnc⟩ := hq
    simp only [sU', mem_filter, mem_univ, true_and] at h1 h2
    simp only [Tset, mem_filter, mem_univ, true_and]
    refine ⟨h1.1, h2.1.symm, hne, by rw [cdX_comm]; exact h1.2.2.1, h2.2.2.1,
      hcs _ _ (hInv.1 x u₁ h1.1.symm h1.2.2.1 h1.2.1), hInv.1 x u₂ h2.1.symm h2.2.2.1 h2.2.1,
      ⟨y, by simp [h1.2.2.2, hxy, h2.2.2.2]⟩⟩
  · rw [disjoint_left]
    intro p hp hpT
    obtain ⟨⟨u₁, u₂⟩, hq, rfl⟩ := mem_image.1 hp
    simp only [mem_filter, mem_product] at hq
    obtain ⟨⟨h1, h2⟩, hne, hnc⟩ := hq
    have hu₁'' : u₁ ∈ sU'' compat PX H x y := mem_filter.2 ⟨h1, u₂, h2, hne.symm, hnc⟩
    simp only [sU', mem_filter, mem_univ, true_and] at h1 h2
    simp only [Tset, mem_filter, mem_univ, true_and] at hpT
    obtain ⟨w, hw⟩ := hpT.2.2.2.2.2.2.2
    simp only [mem_inter, mem_NY, mem_sR_diff] at hw
    obtain ⟨⟨⟨hu₁w, -, hu₁U⟩, ⟨hxw, hxV, -⟩⟩, ⟨hu₂w, -, -⟩⟩ := hw
    have hwy : w ≠ y := fun h => hu₁U ⟨h, mem_union_right _ hu₁''⟩
    rcases cn_x hInv h1.1 h1.2.2.2 hxy hxw hu₁w hwy with hV | hV'
    · exact hxV (by simp [hV])
    · exact hnc (kc hInv hV' h1.2.2.2 hu₁w h2.2.2.2 hu₂w hne)

lemma step_cost :
    (sR compat PX PY H x y).card + (sPX PX H x y).card + (sPY PY H x y).card ≤
      PX.card + PY.card + (sT compat PX H x y).card := by
  have hR : (sR compat PX PY H x y).card ≤ (sV PY H x y).card + (sU PX H x y).card +
      (sU'' compat PX H x y).card := by
    calc _ ≤ ((sV PY H x y).image (fun v => (x, v))).card +
          ((sU PX H x y ∪ sU'' compat PX H x y).image (fun u => (u, y))).card :=
          card_union_le _ _
      _ ≤ (sV PY H x y).card + (sU PX H x y ∪ sU'' compat PX H x y).card :=
          add_le_add card_image_le card_image_le
      _ ≤ _ := by
          have := card_union_le (sU PX H x y) (sU'' compat PX H x y); omega
  have hU'' : (sU'' compat PX H x y).card ≤ (sT compat PX H x y).card := by
    calc _ ≤ ((sT compat PX H x y).image (fun p => p.1)).card := by
          apply card_le_card
          intro u hu
          obtain ⟨hu', u₂, hu₂, hne, hnc⟩ := mem_filter.1 hu
          exact mem_image.2 ⟨(u, x, u₂), mem_image.2 ⟨(u, u₂), by
            simp only [mem_filter, mem_product]; exact ⟨⟨hu', hu₂⟩, hne.symm, hnc⟩, rfl⟩, rfl⟩
      _ ≤ _ := card_image_le
  have hPX : (sPX PX H x y).card + (sU PX H x y).card = PX.card := by
    have hsub : (sU PX H x y).image (fun u => s(x, u)) ⊆ PX := by
      intro p hp
      obtain ⟨u, hu, rfl⟩ := mem_image.1 hp
      exact (mem_filter.1 hu).2.2.1
    have hinj : ((sU PX H x y).image (fun u => s(x, u))).card = (sU PX H x y).card :=
      card_image_of_injective _ (fun u u' h => by
        simpa using (Sym2.congr_right.1 h))
    rw [sPX, card_sdiff_of_subset hsub, hinj]
    have := card_le_card hsub
    omega
  have hPY : (sPY PY H x y).card + (sV PY H x y).card = PY.card := by
    have hsub : (sV PY H x y).image (fun v => s(y, v)) ⊆ PY := by
      intro p hp
      obtain ⟨v, hv, rfl⟩ := mem_image.1 hp
      exact (mem_filter.1 hv).2.2.1
    have hinj : ((sV PY H x y).image (fun v => s(y, v))).card = (sV PY H x y).card :=
      card_image_of_injective _ (fun v v' h => by
        simpa using (Sym2.congr_right.1 h))
    rw [sPY, card_sdiff_of_subset hsub, hinj]
    have := card_le_card hsub
    omega
  omega

lemma step_sR_sub (hxy : (x, y) ∈ H) : sR compat PX PY H x y ⊆ H := by
  intro e he
  simp only [sR, mem_union, mem_image] at he
  rcases he with ⟨v, hv, rfl⟩ | ⟨u, hu, rfl⟩
  · exact (mem_filter.1 hv).2.2.2
  · rcases hu with hu | hu
    · exact (mem_filter.1 hu).2.2.2
    · exact (mem_filter.1 (mem_filter.1 hu).1).2.2.2.2

lemma step_lt (hxx' : x ≠ x') (hP : s(x, x') ∈ PX) (hx'y : (x', y) ∈ H) :
    (sPX PX H x y).card < PX.card := by
  apply card_lt_card
  refine ⟨sdiff_subset, fun h => ?_⟩
  have hx' : x' ∈ sU PX H x y := by simp [sU, hxx'.symm, hP, hx'y]
  have := h hP
  simp only [sPX, mem_sdiff, mem_image] at this
  exact this.2 ⟨x', hx', rfl⟩

lemma step_removed {a b : X} (ha : s(a, b) ∈ PX) (hb : s(a, b) ∉ sPX PX H x y) :
    ∃ u ∈ sU PX H x y, s(a, b) = s(x, u) := by
  simp only [sPX, mem_sdiff, mem_image, not_and, not_not] at hb
  obtain ⟨u, hu, he⟩ := hb ha
  exact ⟨u, hu, he.symm⟩

end Step

/-! ## The lemma -/

open scoped Classical in
theorem graph_deletion {compat : X → X → Prop} (hcs : ∀ a b, compat a b → compat b a) :
    ∀ (k : ℕ) (H : Finset (X × Y)) (PX : Finset (Sym2 X)) (PY : Finset (Sym2 Y)),
      PX.card ≤ k → Inv H compat PX PY →
      ∃ R ⊆ H, R.card ≤ PX.card + PY.card + (Tset H compat).card ∧
        ∀ a b : X, s(a, b) ∈ PX → a ≠ b → ¬ compat a b → cdX (H \ R) a b = 0 := by
  intro k
  induction k with
  | zero =>
    intro H PX PY hk _
    refine ⟨∅, empty_subset _, by simp, ?_⟩
    intro a b hab
    rw [card_eq_zero.1 (Nat.le_zero.1 hk)] at hab
    simp at hab
  | succ k ih =>
    intro H PX PY hk hInv
    by_cases hex : ∃ x x' : X, s(x, x') ∈ PX ∧ x ≠ x' ∧ ¬ compat x x'
    swap
    · push_neg at hex
      refine ⟨∅, empty_subset _, by simp, ?_⟩
      intro a b hab hne hnc
      exact absurd (hex a b hab hne) hnc
    obtain ⟨x, x', hP, hxx', hnc⟩ := hex
    by_cases hcd : cdX H x x' = 0
    · -- Case 1: drop the pair
      set PX' := PX.erase s(x, x')
      have hlt : PX'.card < PX.card := card_erase_lt_of_mem hP
      have hInv' : Inv H compat PX' PY := by
        refine ⟨fun a b hab h2 hnot => ?_, hInv.2⟩
        by_cases he : s(a, b) = s(x, x')
        · exfalso
          rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · omega
          · rw [cdX_comm] at h2; omega
        · exact hInv.1 a b hab h2 (fun h => hnot (mem_erase.2 ⟨he, h⟩))
      obtain ⟨R, hRH, hRc, hR⟩ := ih H PX' PY (by omega) hInv'
      refine ⟨R, hRH, by omega, ?_⟩
      intro a b hab hne hnc'
      by_cases he : s(a, b) = s(x, x')
      · have h0 : cdX H a b = 0 := by
          rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hcd
          · rw [cdX_comm]; exact hcd
        exact Nat.eq_zero_of_le_zero (h0 ▸ cdX_mono sdiff_subset a b)
      · exact hR a b (mem_erase.2 ⟨he, hab⟩) hne hnc'
    · -- Case 3 (including Case 2)
      obtain ⟨y, hy⟩ := card_pos.1 (Nat.pos_of_ne_zero hcd)
      simp only [mem_inter, mem_NY] at hy
      obtain ⟨hxy, hx'y⟩ := hy
      set Hs := H \ sR compat PX PY H x y
      have hlt := step_lt (H := H) (y := y) hxx' hP hx'y
      obtain ⟨R, hRH, hRc, hR⟩ := ih Hs (sPX PX H x y) (sPY PY H x y) (by omega)
        (step_inv hcs hInv hxy)
      refine ⟨sR compat PX PY H x y ∪ R, union_subset (step_sR_sub hxy)
        (hRH.trans sdiff_subset), ?_, ?_⟩
      · have h1 : (sR compat PX PY H x y).card + (sPX PX H x y).card + (sPY PY H x y).card ≤
            PX.card + PY.card + (sT compat PX H x y).card := step_cost
        have h2 : (sT compat PX H x y).card + (Tset Hs compat).card ≤ (Tset H compat).card :=
          step_T hcs hInv hxy
        have h3 := card_union_le (sR compat PX PY H x y) R
        omega
      · intro a b hab hne hnc'
        have hsub : H \ (sR compat PX PY H x y ∪ R) = Hs \ R := by
          rw [sdiff_union_distrib]; ext e; simp [Hs]; tauto
        rw [hsub]
        by_cases hin : s(a, b) ∈ sPX PX H x y
        · exact hR a b hin hne hnc'
        · obtain ⟨u, hu, he⟩ := step_removed hab hin
          have hnc'' : ¬ compat x u := by
            rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hnc'
            · exact fun h => hnc' (hcs _ _ h)
          have h0 := step_cd_zero hInv hu hxy hnc''
          have h0' : cdX Hs a b = 0 := by
            rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact h0
            · rw [cdX_comm]; exact h0
          exact Nat.eq_zero_of_le_zero (h0' ▸ cdX_mono sdiff_subset a b)

end OMA_DL

/-!
# The deletion lemma for bipartite 3-graphs: definitions and the Y-link pass (HMY §6.3)

`F ⊆ X × Sym2 (Fin m)`: an edge `(x, s(y, y'))` is the triple `x y y'`.
-/

namespace OMA_DL

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X] {m : ℕ}

section Defs

variable (F : Finset (X × Sym2 (Fin m)))

/-- Neighbourhood of a `Y`-pair. -/
def Nb (e : Sym2 (Fin m)) : Finset X := univ.filter (fun x => (x, e) ∈ F)
/-- Common neighbourhood of two `X`-vertices: a graph on `Y`. -/
def CNX (x x' : X) : Finset (Sym2 (Fin m)) := univ.filter (fun e => (x, e) ∈ F ∧ (x', e) ∈ F)
/-- The link of `y ∈ Y`: a bipartite graph between `X` and `Y`. -/
def Lk (y : Fin m) : Finset (X × Fin m) := univ.filter (fun p => (p.1, s(y, p.2)) ∈ F)

@[simp] lemma mem_Nb {e : Sym2 (Fin m)} {x : X} : x ∈ Nb F e ↔ (x, e) ∈ F := by simp [Nb]
@[simp] lemma mem_CNX {x x' : X} {e : Sym2 (Fin m)} :
    e ∈ CNX F x x' ↔ (x, e) ∈ F ∧ (x', e) ∈ F := by simp [CNX]
@[simp] lemma mem_Lk {y : Fin m} {p : X × Fin m} : p ∈ Lk F y ↔ (p.1, s(y, p.2)) ∈ F := by
  simp [Lk]

lemma CNX_comm (x x' : X) : CNX F x x' = CNX F x' x := by ext e; simp [and_comm]

/-- A star of `Y`-pairs: some vertex lies in every edge. -/
def IsStarE (S : Finset (Sym2 (Fin m))) : Prop := ∃ c, ∀ e ∈ S, c ∈ e

/-- The triangle `abc` as a set of three `Y`-pairs. -/
def tri (a b c : Fin m) : Finset (Sym2 (Fin m)) := {s(a, b), s(b, c), s(a, c)}

def IsTri (S : Finset (Sym2 (Fin m))) : Prop := ∃ a b c : Fin m, a < b ∧ b < c ∧ S = tri a b c

end Defs

lemma CNX_mono {F F' : Finset (X × Sym2 (Fin m))} (h : F' ⊆ F) (x x' : X) :
    CNX F' x x' ⊆ CNX F x x' := by
  intro e; simp only [mem_CNX]; exact fun ⟨h1, h2⟩ => ⟨h h1, h h2⟩
lemma Nb_mono {F F' : Finset (X × Sym2 (Fin m))} (h : F' ⊆ F) (e : Sym2 (Fin m)) :
    Nb F' e ⊆ Nb F e := by
  intro x; simp only [mem_Nb]; exact fun h1 => h h1
lemma Lk_mono {F F' : Finset (X × Sym2 (Fin m))} (h : F' ⊆ F) (y : Fin m) :
    Lk F' y ⊆ Lk F y := by
  intro p; simp only [mem_Lk]; exact fun h1 => h h1

/-! ## Triangles -/

lemma mem_tri {a b c : Fin m} {e : Sym2 (Fin m)} :
    e ∈ tri a b c ↔ e = s(a, b) ∨ e = s(b, c) ∨ e = s(a, c) := by simp [tri]

lemma verts_of_tri {a b c a' b' c' : Fin m} (h1 : a < b) (h2 : b < c) (h1' : a' < b')
    (h2' : b' < c') (h : tri a b c = tri a' b' c') : a = a' ∧ b = b' ∧ c = c' := by
  have hab : s(a, b) ∈ tri a' b' c' := h ▸ (by simp [tri])
  have hbc : s(b, c) ∈ tri a' b' c' := h ▸ (by simp [tri])
  have hac : s(a, c) ∈ tri a' b' c' := h ▸ (by simp [tri])
  simp only [mem_tri, Sym2.eq_iff] at hab hbc hac
  omega

lemma not_star_tri {a b c : Fin m} (h1 : a < b) (h2 : b < c) : ¬ IsStarE (tri a b c) := by
  rintro ⟨z, hz⟩
  have hab := hz _ (show s(a, b) ∈ tri a b c by simp [tri])
  have hbc := hz _ (show s(b, c) ∈ tri a b c by simp [tri])
  have hac := hz _ (show s(a, c) ∈ tri a b c by simp [tri])
  simp only [Sym2.mem_iff] at hab hbc hac
  omega

/-- Two distinct pairs through `y` determine the centre of a star. -/
lemma star_center_eq {S : Finset (Sym2 (Fin m))} {y y₁ y₂ c : Fin m} (h1 : s(y, y₁) ∈ S)
    (h2 : s(y, y₂) ∈ S) (hne : y₁ ≠ y₂) (hc : ∀ e ∈ S, c ∈ e) : c = y := by
  have := hc _ h1
  have := hc _ h2
  simp only [Sym2.mem_iff] at *
  omega

/-! ## The assignment of `X`-pairs to links -/

open scoped Classical in
/-- The link assigned to a common neighbourhood: the least vertex of a triangle, or a centre. -/
noncomputable def gS (S : Finset (Sym2 (Fin m))) (h0 : Fin m) : Fin m :=
  if h : IsTri S then h.choose else if h' : IsStarE S then h'.choose else h0

lemma gS_tri {S : Finset (Sym2 (Fin m))} {a b c : Fin m} (h1 : a < b) (h2 : b < c)
    (hS : S = tri a b c) (h0 : Fin m) : gS S h0 = a := by
  classical
  have ht : IsTri S := ⟨a, b, c, h1, h2, hS⟩
  rw [gS, dif_pos ht]
  obtain ⟨b', c', h1', h2', hS'⟩ := ht.choose_spec
  exact (verts_of_tri h1' h2' h1 h2 (hS'.symm.trans hS)).1

lemma gS_star {S : Finset (Sym2 (Fin m))} (hs : IsStarE S) (ht : ¬ IsTri S) (h0 : Fin m) :
    ∀ e ∈ S, gS S h0 ∈ e := by
  classical
  rw [gS, dif_neg ht, dif_pos hs]
  exact hs.choose_spec

/-! ## The Y-link pass -/

section Pass

variable (compat : X → X → Prop)

/-- `Y`-diagonals: two common neighbours in some link. -/
def YDiag (F : Finset (X × Sym2 (Fin m))) (u v : Fin m) : Prop :=
  ∃ y, 2 ≤ (Nb F s(u, y) ∩ Nb F s(v, y)).card

def CompatSet (A : Finset X) : Prop := ∀ a ∈ A, ∀ b ∈ A, a ≠ b → compat a b

/-- Goodness (3) for a `Y`-pair `q` with witness `w`. -/
def G3 (F : Finset (X × Sym2 (Fin m))) (q : Sym2 (Fin m)) (w : Fin m) : Prop :=
  ∀ u v y : Fin m, q = s(u, v) → y ≠ u → y ≠ v → y ≠ w →
    CompatSet compat (Nb F s(u, y) ∩ Nb F s(v, y))

open scoped Classical in
noncomputable def wY (F : Finset (X × Sym2 (Fin m))) (q : Sym2 (Fin m)) (h0 : Fin m) : Fin m :=
  if h : ∃ w, G3 compat F q w then h.choose else h0

open scoped Classical in
/-- `X`-targets of the link `k`. -/
noncomputable def TX (F : Finset (X × Sym2 (Fin m))) (E0 : Finset (Sym2 X)) (h0 k : Fin m) :
    Finset (Sym2 X) :=
  ((univ : Finset X).offDiag.filter (fun p => ¬ compat p.1 p.2 ∧ (CNX F p.1 p.2).Nonempty ∧
    s(p.1, p.2) ∉ E0 ∧ gS (CNX F p.1 p.2) h0 = k)).image (fun p => s(p.1, p.2))

open scoped Classical in
/-- `Y`-targets of the link `k`. -/
noncomputable def TY (F : Finset (X × Sym2 (Fin m))) (h0 k : Fin m) : Finset (Sym2 (Fin m)) :=
  ((univ : Finset (Fin m)).offDiag.filter (fun p => YDiag F p.1 p.2 ∧
    wY compat F s(p.1, p.2) h0 = k)).image (fun p => s(p.1, p.2))

variable {compat}

lemma mem_TX (hcs : ∀ a b, compat a b → compat b a) {F : Finset (X × Sym2 (Fin m))}
    {E0 : Finset (Sym2 X)} {h0 k : Fin m} {a b : X} :
    s(a, b) ∈ TX compat F E0 h0 k ↔ a ≠ b ∧ ¬ compat a b ∧ (CNX F a b).Nonempty ∧
      s(a, b) ∉ E0 ∧ gS (CNX F a b) h0 = k := by
  classical
  constructor
  · intro h
    obtain ⟨⟨p1, p2⟩, hp, he⟩ := mem_image.1 h
    simp only [mem_filter, mem_offDiag, mem_univ, true_and] at hp
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2⟩
    · refine ⟨hp.1.symm, fun h => hp.2.1 (hcs _ _ h), ?_, ?_, ?_⟩
      · rw [CNX_comm]; exact hp.2.2.1
      · rw [Sym2.eq_swap]; exact hp.2.2.2.1
      · rw [CNX_comm]; exact hp.2.2.2.2
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact mem_image.2 ⟨(a, b), by simp [h1, h2, h3, h4, h5], rfl⟩

lemma mem_TY {F : Finset (X × Sym2 (Fin m))} {h0 k : Fin m} {c d : Fin m} :
    s(c, d) ∈ TY compat F h0 k ↔ c ≠ d ∧ (YDiag F c d ∨ YDiag F d c) ∧
      wY compat F s(c, d) h0 = k := by
  classical
  constructor
  · intro h
    obtain ⟨⟨p1, p2⟩, hp, he⟩ := mem_image.1 h
    simp only [mem_filter, mem_offDiag, mem_univ, true_and] at hp
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hp.1, Or.inl hp.2.1, hp.2.2⟩
    · exact ⟨hp.1.symm, Or.inr hp.2.1, by rw [Sym2.eq_swap]; exact hp.2.2⟩
  · rintro ⟨h1, h2 | h2, h3⟩
    · exact mem_image.2 ⟨(c, d), by simp [h1, h2, h3], rfl⟩
    · exact mem_image.2 ⟨(d, c), by simp [h1.symm, h2, Sym2.eq_swap, h3], Sym2.eq_swap⟩

lemma two_le_cdX_Lk {F : Finset (X × Sym2 (Fin m))} {y : Fin m} {a b : X}
    (h : 2 ≤ cdX (Lk F y) a b) : ∃ y₁ y₂, y₁ ≠ y₂ ∧ s(y, y₁) ∈ CNX F a b ∧ s(y, y₂) ∈ CNX F a b := by
  rw [cdX] at h
  obtain ⟨y₁, h1, y₂, h2, hne⟩ :=
    one_lt_card.1 (show 1 < (NY (Lk F y) a ∩ NY (Lk F y) b).card by omega)
  simp only [mem_inter, mem_NY, mem_Lk] at h1 h2
  exact ⟨y₁, y₂, hne, by simp [h1.1, h1.2], by simp [h2.1, h2.2]⟩

lemma Lk_sdiff_image {F : Finset (X × Sym2 (Fin m))} {y : Fin m} {R : Finset (X × Fin m)} :
    Lk (F \ R.image (fun p => (p.1, s(y, p.2)))) y = Lk F y \ R := by
  ext ⟨x, y'⟩
  simp only [mem_Lk, mem_sdiff, mem_image, Prod.mk.injEq, not_exists, not_and]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h => h2 (x, y') h rfl rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun q hq hx hy => ?_⟩
    have : q.2 = y' := Sym2.congr_right.1 hy
    exact h2 (by rw [← hx, ← this]; exact hq)

/-- The pass over the first `k` links. -/
theorem pass (hcs : ∀ a b, compat a b → compat b a) (F0 : Finset (X × Sym2 (Fin m)))
    (E0 : Finset (Sym2 X)) (h0 : Fin m) (hnd : ∀ p ∈ F0, ¬ p.2.IsDiag)
    (hg1 : ∀ x x', x ≠ x' → ¬ compat x x' → IsStarE (CNX F0 x x') ∨ IsTri (CNX F0 x x'))
    (hg3 : ∀ u v, u ≠ v → YDiag F0 u v → ∃ w, G3 compat F0 s(u, v) w)
    (hE0 : ∀ x x', s(x, x') ∈ E0 → (CNX F0 x x').card ≤ 1) :
    ∀ k ≤ m, ∃ Fk ⊆ F0, F0.card ≤ Fk.card + ∑ j ∈ (univ : Finset (Fin m)).filter (·.val < k),
        ((TX compat F0 E0 h0 j).card + (TY compat F0 h0 j).card + (Tset (Lk F0 j) compat).card) ∧
      ∀ x x', x ≠ x' → ¬ compat x x' → (CNX F0 x x').Nonempty → s(x, x') ∉ E0 →
        (gS (CNX F0 x x') h0).val < k → ∀ e ∈ CNX Fk x x', gS (CNX F0 x x') h0 ∉ e := by
  classical
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨F0, subset_refl _, by simp, fun x x' _ _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hk
    obtain ⟨Fk, hFk, hcost, hI2⟩ := ih (by omega)
    set yk : Fin m := ⟨k, by omega⟩ with hyk
    set L := Lk Fk yk with hL
    have hLsub : L ⊆ Lk F0 yk := Lk_mono hFk yk
    -- the hypothesis of the one-link lemma
    have hInv : Inv L compat (TX compat F0 E0 h0 yk) (TY compat F0 h0 yk) := by
      constructor
      · intro a b hab h2 hnot
        by_contra hnc
        obtain ⟨y₁, y₂, hne, h1, h2'⟩ := two_le_cdX_Lk h2
        have h1' := CNX_mono hFk a b h1
        have h2'' := CNX_mono hFk a b h2'
        have hne' : (CNX F0 a b).Nonempty := ⟨_, h1'⟩
        have hE : s(a, b) ∉ E0 := by
          intro hE
          have := hE0 a b hE
          have h12 : s(yk, y₁) ≠ s(yk, y₂) := fun h => hne (Sym2.congr_right.1 h)
          have : 2 ≤ (CNX F0 a b).card := two_le_card_of_ne h1' h2'' h12
          omega
        have hg : gS (CNX F0 a b) h0 ≠ yk := fun hg =>
          hnot ((mem_TX hcs).2 ⟨hab, hnc, hne', hE, hg⟩)
        by_cases htri : IsTri (CNX F0 a b)
        · obtain ⟨a', b', c', ha', hb', hS⟩ := htri
          have hga := gS_tri ha' hb' hS h0
          rw [hga] at hg
          have hlt : a' < yk := by
            have m1 := hS ▸ h1'
            simp only [mem_tri, Sym2.eq_iff] at m1
            rcases lt_or_gt_of_ne hg with h | h
            · exact h
            · exfalso; omega
          have hI := hI2 a b hab hnc hne' hE (by rw [hga]; exact hlt)
          rw [hga] at hI
          have n1 := hI _ h1
          have n2 := hI _ h2'
          have m1 := hS ▸ h1'
          have m2 := hS ▸ h2''
          simp only [mem_tri, Sym2.eq_iff, Sym2.mem_iff] at m1 m2 n1 n2
          omega
        · rcases hg1 a b hab hnc with hs | ht
          · have := star_center_eq h1' h2'' hne (gS_star hs htri h0)
            exact hg this
          · exact htri ht
      · intro c d hcd h2 hnot a ha b hb hab
        have hsub : NX L c ∩ NX L d ⊆ Nb F0 s(c, yk) ∩ Nb F0 s(d, yk) := by
          intro z hz
          simp only [mem_inter, mem_NX, hL, mem_Lk, mem_Nb] at hz ⊢
          exact ⟨Sym2.eq_swap ▸ hFk hz.1, Sym2.eq_swap ▸ hFk hz.2⟩
        have hdiag : YDiag F0 c d := ⟨yk, h2.trans (card_le_card hsub)⟩
        obtain ⟨w, hw⟩ := hg3 c d hcd hdiag
        have hex : ∃ w, G3 compat F0 s(c, d) w := ⟨w, hw⟩
        have hwk : wY compat F0 s(c, d) h0 ≠ yk := fun h =>
          hnot (mem_TY.2 ⟨hcd, Or.inl hdiag, h⟩)
        have haL := ha
        simp only [mem_inter, mem_NX, hL, mem_Lk] at haL
        have hkc : yk ≠ c := fun h => hnd _ (hFk haL.1) (by simp [h])
        have hkd : yk ≠ d := fun h => hnd _ (hFk haL.2) (by simp [h])
        have hspec : G3 compat F0 s(c, d) (wY compat F0 s(c, d) h0) := by
          rw [wY, dif_pos hex]; exact hex.choose_spec
        exact hspec c d yk rfl hkc hkd (Ne.symm hwk) a (hsub ha) b (hsub hb) hab
    obtain ⟨R, hRL, hRc, hR⟩ := graph_deletion hcs (TX compat F0 E0 h0 yk).card L _ _ le_rfl hInv
    set Fk1 := Fk \ R.image (fun p => (p.1, s(yk, p.2))) with hFk1
    refine ⟨Fk1, sdiff_subset.trans hFk, ?_, ?_⟩
    · have hfil : (univ : Finset (Fin m)).filter (·.val < k + 1) =
          insert yk ((univ : Finset (Fin m)).filter (·.val < k)) := by
        ext j; simp only [mem_filter, mem_univ, true_and, mem_insert, hyk, Fin.ext_iff]; omega
      have hnot : yk ∉ (univ : Finset (Fin m)).filter (·.val < k) := by simp [hyk]
      rw [hfil, sum_insert hnot]
      have h1 : Fk.card ≤ Fk1.card + R.card := by
        have := card_sdiff_add_card_inter Fk (R.image (fun p => (p.1, s(yk, p.2))))
        have h2 := card_le_card (inter_subset_right (s₁ := Fk)
          (s₂ := R.image (fun p => (p.1, s(yk, p.2)))))
        have h3 := card_image_le (s := R) (f := fun p => (p.1, s(yk, p.2)))
        rw [hFk1]; omega
      have h2 : (Tset L compat).card ≤ (Tset (Lk F0 yk) compat).card :=
        card_le_card (Tset_mono hLsub)
      omega
    · intro x x' hxx' hnc hne hE hlt e he
      have he' : e ∈ CNX Fk x x' := CNX_mono sdiff_subset x x' he
      by_cases hj : (gS (CNX F0 x x') h0).val < k
      · exact hI2 x x' hxx' hnc hne hE hj e he'
      · have hgk : gS (CNX F0 x x') h0 = yk := by
          rw [Fin.ext_iff, hyk]; simp only; omega
        rw [hgk]
        intro hke
        have hT : s(x, x') ∈ TX compat F0 E0 h0 yk := (mem_TX hcs).2 ⟨hxx', hnc, hne, hE, hgk⟩
        have h0' := hR x x' hT hxx' hnc
        obtain ⟨y', rfl⟩ : ∃ y', e = s(yk, y') := by
          obtain ⟨y', hy'⟩ := Sym2.mem_iff_exists.1 hke
          exact ⟨y', hy'⟩
        have hLk : Lk Fk1 yk = L \ R := Lk_sdiff_image
        have hmem : y' ∈ NY (L \ R) x ∩ NY (L \ R) x' := by
          rw [← hLk]
          simp only [mem_CNX] at he
          simp [he.1, he.2]
        rw [cdX, card_eq_zero] at h0'
        rw [h0'] at hmem
        exact absurd hmem (notMem_empty _)

end Pass

/-! ## Counting the cost of the pass -/

section Count

variable {compat : X → X → Prop}

open scoped Classical in
/-- Ordered compatible pairs whose common neighbourhood is not a star. -/
noncomputable def alphaO (compat : X → X → Prop) (F : Finset (X × Sym2 (Fin m))) : Finset (X × X) :=
  (univ : Finset X).offDiag.filter (fun p => compat p.1 p.2 ∧ ¬ IsStarE (CNX F p.1 p.2))

open scoped Classical in
noncomputable def cnb (compat : X → X → Prop) (x : X) : Finset X :=
  univ.filter (fun x' => x' ≠ x ∧ compat x x')

open scoped Classical in
lemma T_sum {D : ℕ} (hD : ∀ x, (cnb compat x).card ≤ D) (F : Finset (X × Sym2 (Fin m))) :
    ∑ j : Fin m, (Tset (Lk F j) compat).card ≤
      Fintype.card X * D * D + m * (D * (alphaO compat F).card) := by
  set C : Finset (X × X × X) := univ.filter (fun p => p.1 ≠ p.2.1 ∧ p.2.1 ≠ p.2.2 ∧
    compat p.1 p.2.1 ∧ compat p.2.1 p.2.2) with hC
  have hTC : ∀ j, Tset (Lk F j) compat ⊆ C := by
    intro j p hp
    simp only [Tset, mem_filter, mem_univ, true_and] at hp
    simp only [hC, mem_filter, mem_univ, true_and]
    exact ⟨hp.1, hp.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1⟩
  set N : X × X × X → ℕ := fun p => (univ.filter (fun j : Fin m => p ∈ Tset (Lk F j) compat)).card
  have hswap : ∑ j : Fin m, (Tset (Lk F j) compat).card = ∑ p ∈ C, N p := by
    have h1 : ∀ j : Fin m, (Tset (Lk F j) compat).card =
        ∑ p ∈ C, if p ∈ Tset (Lk F j) compat then 1 else 0 := by
      intro j
      rw [← card_filter]
      congr 1
      ext p
      simp only [mem_filter]
      exact ⟨fun h => ⟨hTC j h, h⟩, fun h => h.2⟩
    rw [sum_congr rfl (fun j _ => h1 j), sum_comm]
    apply sum_congr rfl
    intro p _
    simp only [N, card_filter]
  have hN : ∀ p ∈ C, N p ≤ 1 + if (p.1, p.2.1) ∈ alphaO compat F then m else 0 := by
    intro p hp
    split_ifs with ha
    · calc N p ≤ (univ : Finset (Fin m)).card := card_le_card (filter_subset _ _)
        _ = m := by simp
        _ ≤ 1 + m := by omega
    · by_contra hlt
      push_neg at hlt
      obtain ⟨j₁, hj₁, j₂, hj₂, hne⟩ := one_lt_card.1 (show 1 < N p by omega)
      simp only [mem_filter, mem_univ, true_and, Tset] at hj₁ hj₂
      obtain ⟨y₁, y₂, hy, e1, e2⟩ := two_le_cdX_Lk hj₁.2.2.2.1
      obtain ⟨z₁, z₂, hz, f1, f2⟩ := two_le_cdX_Lk hj₂.2.2.2.1
      apply ha
      simp only [alphaO, mem_filter, mem_offDiag, mem_univ, true_and]
      refine ⟨hj₁.1, hj₁.2.2.2.2.2.1, ?_⟩
      rintro ⟨c, hc⟩
      exact hne ((star_center_eq e1 e2 hy hc).symm.trans (star_center_eq f1 f2 hz hc))
  have hCc : C.card ≤ Fintype.card X * D * D := by
    calc C.card ≤ ((univ : Finset X).biUnion (fun x₁ => (cnb compat x₁).biUnion
          (fun x₂ => (cnb compat x₂).image (fun x₃ => (x₁, x₂, x₃))))).card := by
          apply card_le_card
          intro p hp
          simp only [hC, mem_filter, mem_univ, true_and] at hp
          simp only [mem_biUnion, mem_univ, true_and, mem_image, cnb, mem_filter]
          exact ⟨p.1, p.2.1, ⟨hp.1.symm, hp.2.2.1⟩, p.2.2, ⟨hp.2.1.symm, hp.2.2.2⟩, rfl⟩
      _ ≤ ∑ x₁ : X, ((cnb compat x₁).biUnion
          (fun x₂ => (cnb compat x₂).image (fun x₃ => (x₁, x₂, x₃)))).card := card_biUnion_le
      _ ≤ ∑ _x₁ : X, D * D := by
          apply sum_le_sum
          intro x₁ _
          calc _ ≤ ∑ x₂ ∈ cnb compat x₁, ((cnb compat x₂).image (fun x₃ => (x₁, x₂, x₃))).card :=
                card_biUnion_le
            _ ≤ ∑ _x₂ ∈ cnb compat x₁, D :=
                sum_le_sum (fun x₂ _ => card_image_le.trans (hD x₂))
            _ ≤ D * D := by rw [sum_const, smul_eq_mul]; exact Nat.mul_le_mul_right _ (hD x₁)
      _ = Fintype.card X * D * D := by rw [sum_const, card_univ, smul_eq_mul, mul_assoc]
  have hCa : (C.filter (fun p => (p.1, p.2.1) ∈ alphaO compat F)).card ≤
      D * (alphaO compat F).card := by
    calc _ ≤ ((alphaO compat F).biUnion (fun q => (cnb compat q.2).image
          (fun x₃ => (q.1, q.2, x₃)))).card := by
          apply card_le_card
          intro p hp
          simp only [hC, mem_filter, mem_univ, true_and] at hp
          simp only [mem_biUnion, mem_image, cnb, mem_filter, mem_univ, true_and]
          exact ⟨(p.1, p.2.1), hp.2, p.2.2, ⟨hp.1.2.1.symm, hp.1.2.2.2⟩, rfl⟩
      _ ≤ ∑ q ∈ alphaO compat F, ((cnb compat q.2).image (fun x₃ => (q.1, q.2, x₃))).card :=
          card_biUnion_le
      _ ≤ ∑ _q ∈ alphaO compat F, D := sum_le_sum (fun q _ => card_image_le.trans (hD q.2))
      _ = D * (alphaO compat F).card := by rw [sum_const, smul_eq_mul, mul_comm]
  rw [hswap]
  calc ∑ p ∈ C, N p ≤ ∑ p ∈ C, (1 + if (p.1, p.2.1) ∈ alphaO compat F then m else 0) :=
        sum_le_sum hN
    _ = C.card + m * (C.filter (fun p => (p.1, p.2.1) ∈ alphaO compat F)).card := by
        rw [sum_add_distrib, sum_ite, sum_const_zero, add_zero]; simp [mul_comm]
    _ ≤ _ := add_le_add hCc (Nat.mul_le_mul_left _ hCa)

open scoped Classical in
/-- Incompatible `X`-pairs with a nonempty common neighbourhood. -/
noncomputable def CXI (compat : X → X → Prop) (F : Finset (X × Sym2 (Fin m))) : Finset (Sym2 X) :=
  ((univ : Finset X).offDiag.filter (fun p => ¬ compat p.1 p.2 ∧
    (CNX F p.1 p.2).Nonempty)).image (fun p => s(p.1, p.2))

open scoped Classical in
/-- `Y`-diagonals. -/
noncomputable def DYs (F : Finset (X × Sym2 (Fin m))) : Finset (Sym2 (Fin m)) :=
  ((univ : Finset (Fin m)).offDiag.filter (fun p => YDiag F p.1 p.2)).image (fun p => s(p.1, p.2))

lemma sum_TX (hcs : ∀ a b, compat a b → compat b a) (F : Finset (X × Sym2 (Fin m)))
    (E0 : Finset (Sym2 X)) (h0 : Fin m) :
    ∑ j : Fin m, (TX compat F E0 h0 j).card ≤ (CXI compat F \ E0).card := by
  classical
  rw [← card_biUnion]
  · apply card_le_card
    intro q hq
    obtain ⟨j, -, hj⟩ := mem_biUnion.1 hq
    obtain ⟨⟨a, b⟩, -, rfl⟩ := mem_image.1 hj
    obtain ⟨h1, h2, h3, h4, -⟩ := (mem_TX hcs).1 hj
    exact mem_sdiff.2 ⟨mem_image.2 ⟨(a, b), by simp [h1, h2, h3], rfl⟩, h4⟩
  · intro j _ j' _ hne
    rw [Function.onFun, disjoint_left]
    intro q hq hq'
    obtain ⟨⟨a, b⟩, -, rfl⟩ := mem_image.1 hq
    exact hne (((mem_TX hcs).1 hq).2.2.2.2.symm.trans ((mem_TX hcs).1 hq').2.2.2.2)

lemma sum_TY (F : Finset (X × Sym2 (Fin m))) (h0 : Fin m) :
    ∑ j : Fin m, (TY compat F h0 j).card ≤ (DYs F).card := by
  classical
  rw [← card_biUnion]
  · apply card_le_card
    intro q hq
    obtain ⟨j, -, hj⟩ := mem_biUnion.1 hq
    obtain ⟨⟨c, d⟩, -, rfl⟩ := mem_image.1 hj
    obtain ⟨h1, h2, -⟩ := mem_TY.1 hj
    rcases h2 with h2 | h2
    · exact mem_image.2 ⟨(c, d), by simp [h1, h2], rfl⟩
    · exact mem_image.2 ⟨(d, c), by simp [h1.symm, h2], Sym2.eq_swap⟩
  · intro j _ j' _ hne
    rw [Function.onFun, disjoint_left]
    intro q hq hq'
    obtain ⟨⟨c, d⟩, -, rfl⟩ := mem_image.1 hq
    exact hne ((mem_TY.1 hq).2.2.symm.trans (mem_TY.1 hq').2.2)

end Count

/-! ## β-triangles and kernels -/

section Beta

variable {compat : X → X → Prop}

/-- The kernel of a set of `Y`-pairs: the `X`-vertices adjacent to all of them. -/
def Ker (F : Finset (X × Sym2 (Fin m))) (τ : Finset (Sym2 (Fin m))) : Finset X :=
  univ.filter (fun x => ∀ e ∈ τ, (x, e) ∈ F)

@[simp] lemma mem_Ker {F : Finset (X × Sym2 (Fin m))} {τ : Finset (Sym2 (Fin m))} {x : X} :
    x ∈ Ker F τ ↔ ∀ e ∈ τ, (x, e) ∈ F := by simp [Ker]

lemma Ker_mono {F F' : Finset (X × Sym2 (Fin m))} (h : F' ⊆ F) (τ : Finset (Sym2 (Fin m))) :
    Ker F' τ ⊆ Ker F τ := by
  intro x; simp only [mem_Ker]; exact fun hx e he => h (hx e he)

lemma card_tri {a b c : Fin m} (h1 : a < b) (h2 : b < c) : (tri a b c).card = 3 := by
  rw [tri, card_insert_of_notMem, card_pair]
  · intro h; rw [Sym2.eq_iff] at h; omega
  · simp only [mem_insert, mem_singleton, Sym2.eq_iff]; omega

lemma IsTri.card_eq {S : Finset (Sym2 (Fin m))} (h : IsTri S) : S.card = 3 := by
  obtain ⟨a, b, c, h1, h2, rfl⟩ := h
  exact card_tri h1 h2

lemma IsTri.not_star {S : Finset (Sym2 (Fin m))} (h : IsTri S) : ¬ IsStarE S := by
  obtain ⟨a, b, c, h1, h2, rfl⟩ := h
  exact not_star_tri h1 h2

lemma star_mono' {S T : Finset (Sym2 (Fin m))} (h : T ⊆ S) (hs : IsStarE S) : IsStarE T := by
  obtain ⟨c, hc⟩ := hs
  exact ⟨c, fun e he => hc e (h he)⟩

/-- Goodness (1). -/
def Good1 (compat : X → X → Prop) (F : Finset (X × Sym2 (Fin m))) : Prop :=
  ∀ x x', x ≠ x' → ¬ compat x x' → IsStarE (CNX F x x') ∨ IsTri (CNX F x x')

lemma Good1.mono {F F' : Finset (X × Sym2 (Fin m))} (h : F' ⊆ F) (hg : Good1 compat F) :
    Good1 compat F' := by
  intro x x' hxx' hnc
  rcases hg x x' hxx' hnc with hs | ht
  · exact Or.inl (star_mono' (CNX_mono h x x') hs)
  · by_cases hs : IsStarE (CNX F' x x')
    · exact Or.inl hs
    · rcases (show IsStarE (CNX F' x x') ∨ IsTri (CNX F' x x') from by
        obtain ⟨a, b, c, h1, h2, hS⟩ := ht
        by_cases heq : CNX F' x x' = CNX F x x'
        · exact Or.inr ⟨a, b, c, h1, h2, heq.trans hS⟩
        · -- a proper subset of a triangle is a star
          left
          have hsub := CNX_mono h x x'
          rw [hS] at hsub heq
          obtain ⟨e, he, hne⟩ : ∃ e ∈ tri a b c, e ∉ CNX F' x x' := by
            by_contra hall
            push_neg at hall
            exact heq (eq_of_subset_of_card_le hsub (card_le_card hall))
          simp only [mem_tri] at he
          rcases he with rfl | rfl | rfl
          · refine ⟨c, fun f hf => ?_⟩
            have := hsub hf
            simp only [mem_tri] at this
            rcases this with rfl | rfl | rfl
            · exact absurd hf hne
            · simp
            · simp
          · refine ⟨a, fun f hf => ?_⟩
            have := hsub hf
            simp only [mem_tri] at this
            rcases this with rfl | rfl | rfl
            · simp
            · exact absurd hf hne
            · simp
          · refine ⟨b, fun f hf => ?_⟩
            have := hsub hf
            simp only [mem_tri] at this
            rcases this with rfl | rfl | rfl
            · simp
            · simp
            · exact absurd hf hne) with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'

/-- Two incompatible kernel vertices have exactly the triangle as common neighbourhood. -/
lemma CNX_eq_of_ker {F : Finset (X × Sym2 (Fin m))} (hg : Good1 compat F)
    {τ : Finset (Sym2 (Fin m))} (hτ : IsTri τ) {x x' : X} (hx : x ∈ Ker F τ) (hx' : x' ∈ Ker F τ)
    (hxx' : x ≠ x') (hnc : ¬ compat x x') : CNX F x x' = τ := by
  have hsub : τ ⊆ CNX F x x' := by
    intro e he
    rw [mem_CNX]
    exact ⟨mem_Ker.1 hx e he, mem_Ker.1 hx' e he⟩
  rcases hg x x' hxx' hnc with hs | ht
  · exact absurd (star_mono' hsub hs) hτ.not_star
  · symm
    exact eq_of_subset_of_card_le hsub (by rw [ht.card_eq, hτ.card_eq])

/-- A `β`-pair: incompatible with a triangle as common neighbourhood. -/
def BetaPair (compat : X → X → Prop) (F : Finset (X × Sym2 (Fin m))) (x x' : X) : Prop :=
  x ≠ x' ∧ ¬ compat x x' ∧ IsTri (CNX F x x')

/-- `β`-pairs of a subgraph are `β`-pairs of the graph, with the same triangle. -/
lemma BetaPair.of_sub {F F' : Finset (X × Sym2 (Fin m))} (h : F' ⊆ F) (hg : Good1 compat F)
    {x x' : X} (hb : BetaPair compat F' x x') : CNX F x x' = CNX F' x x' := by
  obtain ⟨hxx', hnc, ht⟩ := hb
  refine (CNX_eq_of_ker hg ht ?_ ?_ hxx' hnc)
  · rw [mem_Ker]; intro e he; exact h ((mem_CNX F').1 he).1
  · rw [mem_Ker]; intro e he; exact h ((mem_CNX F').1 he).2

/-- Goodness (2): `β`-triangles are edge-disjoint. -/
def Good2 (compat : X → X → Prop) (F : Finset (X × Sym2 (Fin m))) : Prop :=
  ∀ x₁ x₁' x₂ x₂', BetaPair compat F x₁ x₁' → BetaPair compat F x₂ x₂' →
    (CNX F x₁ x₁' ∩ CNX F x₂ x₂').Nonempty → CNX F x₁ x₁' = CNX F x₂ x₂'

lemma BetaPair.mono_of_sub {F F' : Finset (X × Sym2 (Fin m))} (h : F' ⊆ F)
    (hg : Good1 compat F) {x x' : X} (hb : BetaPair compat F' x x') : BetaPair compat F x x' :=
  ⟨hb.1, hb.2.1, (hb.of_sub h hg) ▸ hb.2.2⟩

lemma Good2.mono {F F' : Finset (X × Sym2 (Fin m))} (h : F' ⊆ F) (hg1 : Good1 compat F)
    (hg : Good2 compat F) : Good2 compat F' := by
  intro x₁ x₁' x₂ x₂' h1 h2 hne
  rw [← h1.of_sub h hg1, ← h2.of_sub h hg1] at hne ⊢
  exact hg _ _ _ _ (h1.mono_of_sub h hg1) (h2.mono_of_sub h hg1) hne

open scoped Classical in
/-- The `β`-triangles of a graph. -/
noncomputable def BT (compat : X → X → Prop) (F : Finset (X × Sym2 (Fin m))) :
    Finset (Finset (Sym2 (Fin m))) :=
  univ.filter (fun τ => ∃ p q, BetaPair compat F p q ∧ CNX F p q = τ)

lemma mem_BT {F : Finset (X × Sym2 (Fin m))} {τ : Finset (Sym2 (Fin m))} :
    τ ∈ BT compat F ↔ ∃ p q, BetaPair compat F p q ∧ CNX F p q = τ := by
  classical
  simp [BT]

/-- Every vertex of a `β`-pair lies in the kernel of its triangle. -/
lemma BetaPair.mem_ker {F : Finset (X × Sym2 (Fin m))} {x x' : X}
    (hb : BetaPair compat F x x') : x ∈ Ker F (CNX F x x') ∧ x' ∈ Ker F (CNX F x x') := by
  constructor <;> (rw [mem_Ker]; intro e he; rw [mem_CNX] at he)
  · exact he.1
  · exact he.2

end Beta

/-! ## Preparing the β-triangles, stage 1: mixed kernels -/

section Stage1

variable {compat : X → X → Prop}

open scoped Classical in
noncomputable def Mix (compat : X → X → Prop) (F : Finset (X × Sym2 (Fin m))) : Finset (X × X × X) :=
  univ.filter (fun t => t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2 ∧ ¬ compat t.1 t.2.1 ∧
    compat t.2.1 t.2.2 ∧ IsTri (CNX F t.1 t.2.1) ∧ t.2.2 ∈ Ker F (CNX F t.1 t.2.1))

open scoped Classical in
noncomputable def stage1 (compat : X → X → Prop) (F : Finset (X × Sym2 (Fin m))) :
    Finset (X × Sym2 (Fin m)) :=
  F \ (Mix compat F).biUnion (fun t => ({t.1, t.2.1, t.2.2} : Finset X) ×ˢ CNX F t.1 t.2.1)

lemma stage1_sub (F : Finset (X × Sym2 (Fin m))) : stage1 compat F ⊆ F := sdiff_subset

lemma stage1_cost (F : Finset (X × Sym2 (Fin m))) :
    F.card ≤ (stage1 compat F).card + 9 * (Fintype.card X * (alphaO compat F).card) := by
  set D := (Mix compat F).biUnion (fun t => ({t.1, t.2.1, t.2.2} : Finset X) ×ˢ CNX F t.1 t.2.1)
  have h1 : F.card ≤ (stage1 compat F).card + D.card := by
    have := card_sdiff_add_card_inter F D
    have h2 : (F ∩ D).card ≤ D.card := card_le_card inter_subset_right
    have h3 : (stage1 compat F).card = (F \ D).card := by unfold stage1; convert rfl
    omega
  have h2 : D.card ≤ 9 * (Mix compat F).card := by
    calc D.card ≤ ∑ t ∈ Mix compat F, (({t.1, t.2.1, t.2.2} : Finset X) ×ˢ CNX F t.1 t.2.1).card :=
          card_biUnion_le
      _ ≤ ∑ _t ∈ Mix compat F, 9 := by
          apply sum_le_sum
          intro t ht
          simp only [Mix, mem_filter, mem_univ, true_and] at ht
          rw [card_product, ht.2.2.2.2.2.1.card_eq]
          have : ({t.1, t.2.1, t.2.2} : Finset X).card ≤ 3 := card_le_three
          omega
      _ = 9 * (Mix compat F).card := by rw [sum_const, smul_eq_mul, mul_comm]
  have h3 : (Mix compat F).card ≤ Fintype.card X * (alphaO compat F).card := by
    calc (Mix compat F).card ≤ ((univ : Finset X) ×ˢ alphaO compat F).card := by
          apply card_le_card_of_injOn (fun t => (t.1, (t.2.1, t.2.2)))
          · intro t ht
            simp only [Mix, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at ht
            simp only [coe_product, coe_univ, Set.mem_prod, Set.mem_univ, true_and, mem_coe,
              alphaO, mem_filter, mem_offDiag]
            refine ⟨⟨mem_univ _, mem_univ _, ht.2.1⟩, ht.2.2.2.2.1, fun hs => ?_⟩
            apply ht.2.2.2.2.2.1.not_star
            refine star_mono' (fun e he => ?_) hs
            rw [mem_CNX]
            exact ⟨((mem_CNX F).1 he).2, mem_Ker.1 ht.2.2.2.2.2.2 e he⟩
          · intro t _ t' _ h
            simp only [Prod.mk.injEq] at h
            exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)
      _ = _ := by rw [card_product, card_univ]
  omega

/-- After stage 1, every `β`-triangle has a pairwise incompatible kernel. -/
lemma stage1_ker (hcs : ∀ a b, compat a b → compat b a) {F : Finset (X × Sym2 (Fin m))}
    (hg : Good1 compat F) {p q : X} (hb : BetaPair compat (stage1 compat F) p q)
    {a b : X} (ha : a ∈ Ker (stage1 compat F) (CNX (stage1 compat F) p q))
    (hb' : b ∈ Ker (stage1 compat F) (CNX (stage1 compat F) p q)) (hab : a ≠ b) :
    ¬ compat a b := by
  classical
  set F1 := stage1 compat F
  set τ := CNX F1 p q with hτ
  have hτt : IsTri τ := hb.2.2
  have hτF : CNX F p q = τ := hb.of_sub (stage1_sub F) hg
  obtain ⟨hp, hq⟩ := hb.mem_ker
  have hKF : ∀ z, z ∈ Ker F1 τ → z ∈ Ker F τ := fun z hz => Ker_mono (stage1_sub F) τ hz
  -- a configuration with triangle `τ` removes its three vertices from the kernel
  have kill : ∀ t ∈ Mix compat F, CNX F t.1 t.2.1 = τ →
      ∀ z ∈ ({t.1, t.2.1, t.2.2} : Finset X), z ∉ Ker F1 τ := by
    intro t ht hct z hz hzK
    obtain ⟨e, he⟩ : τ.Nonempty := by rw [← card_pos, hτt.card_eq]; norm_num
    have h1 := mem_Ker.1 hzK e he
    simp only [F1, stage1, mem_sdiff, mem_biUnion, mem_product, not_exists, not_and] at h1
    exact h1.2 t ht hz (by rw [hct]; exact he)
  have mk : ∀ x x' x'', x ∈ Ker F1 τ → x' ∈ Ker F1 τ → x'' ∈ Ker F1 τ → x ≠ x' → x' ≠ x'' →
      x ≠ x'' → ¬ compat x x' → compat x' x'' → False := by
    intro x x' x'' hx hx' hx'' h1 h2 h3 hnc hc
    have hct : CNX F x x' = τ := CNX_eq_of_ker hg hτt (hKF x hx) (hKF x' hx') h1 hnc
    have ht : (x, x', x'') ∈ Mix compat F := by
      simp only [Mix, mem_filter, mem_univ, true_and]
      exact ⟨h1, h2, h3, hnc, hc, hct ▸ hτt, hct ▸ hKF x'' hx''⟩
    exact kill _ ht hct x (by simp) hx
  intro hc
  have hpq : p ≠ q := hb.1
  have hnpq : ¬ compat p q := hb.2.1
  by_cases hpa : p = a
  · subst hpa
    have hqb : q ≠ b := fun h => hnpq (h ▸ hc)
    exact mk q p b hq hp hb' hpq.symm hab hqb (fun h => hnpq (hcs _ _ h)) hc
  · by_cases hcpa : compat p a
    · have hqa : q ≠ a := fun h => hnpq (h ▸ hcpa)
      exact mk q p a hq hp ha hpq.symm hpa hqa (fun h => hnpq (hcs _ _ h)) hcpa
    · have hpb : p ≠ b := fun h => hcpa (h ▸ hcs _ _ hc)
      exact mk p a b hp ha hb' hpa hab hpb hcpa hc

end Stage1

/-! ## Stage 2: truncating large kernels -/

section Stage2

variable {compat : X → X → Prop}

open scoped Classical in
noncomputable def keep3 (K : Finset X) : Finset X :=
  if h : 3 ≤ K.card then (exists_subset_card_eq h).choose else K

lemma keep3_sub (K : Finset X) : keep3 K ⊆ K := by
  classical
  unfold keep3; split_ifs with h
  · exact (exists_subset_card_eq h).choose_spec.1
  · exact subset_refl _

lemma keep3_card_le (K : Finset X) : (keep3 K).card ≤ 3 := by
  classical
  unfold keep3; split_ifs with h
  · exact (exists_subset_card_eq h).choose_spec.2.le
  · omega

lemma keep3_card (K : Finset X) (h : 3 ≤ K.card) : (keep3 K).card = 3 := by
  classical
  unfold keep3; rw [dif_pos h]; exact (exists_subset_card_eq h).choose_spec.2

lemma sdiff_keep3_empty (K : Finset X) (h : K.card < 3) : K \ keep3 K = ∅ := by
  classical
  unfold keep3; rw [dif_neg (by omega)]; simp

open scoped Classical in
noncomputable def stage2 (compat : X → X → Prop) (F : Finset (X × Sym2 (Fin m))) :
    Finset (X × Sym2 (Fin m)) :=
  F \ (BT compat F).biUnion (fun τ => (Ker F τ \ keep3 (Ker F τ)) ×ˢ τ)

lemma stage2_sub (F : Finset (X × Sym2 (Fin m))) : stage2 compat F ⊆ F := sdiff_subset

lemma mem_CXI (hcs : ∀ a b, compat a b → compat b a) {F : Finset (X × Sym2 (Fin m))} {a b : X} :
    s(a, b) ∈ CXI compat F ↔ a ≠ b ∧ ¬ compat a b ∧ (CNX F a b).Nonempty := by
  classical
  constructor
  · intro h
    obtain ⟨⟨p1, p2⟩, hp, he⟩ := mem_image.1 h
    simp only [mem_filter, mem_offDiag, mem_univ, true_and] at hp
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hp
    · exact ⟨hp.1.symm, fun h => hp.2.1 (hcs _ _ h), by rw [CNX_comm]; exact hp.2.2⟩
  · rintro ⟨h1, h2, h3⟩
    exact mem_image.2 ⟨(a, b), by simp [h1, h2, h3], rfl⟩

lemma CXI_mono (hcs : ∀ a b, compat a b → compat b a) {F F' : Finset (X × Sym2 (Fin m))}
    (h : F' ⊆ F) : CXI compat F' ⊆ CXI compat F := by
  intro q hq
  obtain ⟨⟨a, b⟩, -, rfl⟩ := mem_image.1 hq
  obtain ⟨h1, h2, ⟨e, he⟩⟩ := (mem_CXI hcs).1 hq
  exact (mem_CXI hcs).2 ⟨h1, h2, ⟨e, CNX_mono h a b he⟩⟩

lemma stage2_cost (hcs : ∀ a b, compat a b → compat b a) {F : Finset (X × Sym2 (Fin m))}
    (hg : Good1 compat F) :
    (stage1 compat F).card + (CXI compat (stage2 compat (stage1 compat F))).card ≤
      (stage2 compat (stage1 compat F)).card + (CXI compat (stage1 compat F)).card := by
  classical
  set F1 := stage1 compat F
  set F2 := stage2 compat F1
  have hg1 : Good1 compat F1 := hg.mono (stage1_sub F)
  set D := (BT compat F1).biUnion (fun τ => (Ker F1 τ \ keep3 (Ker F1 τ)) ×ˢ τ)
  have hF2 : F2.card = (F1 \ D).card := by unfold F2 stage2; convert rfl
  have h1 : F1.card ≤ F2.card + D.card := by
    have := card_sdiff_add_card_inter F1 D
    have h2 : (F1 ∩ D).card ≤ D.card := card_le_card inter_subset_right
    omega
  set P := (BT compat F1).biUnion (fun τ =>
    ((Ker F1 τ \ keep3 (Ker F1 τ)) ×ˢ keep3 (Ker F1 τ)).image (fun p => s(p.1, p.2)))
  -- facts about a β-triangle of `F1`
  have hfacts : ∀ τ ∈ BT compat F1, IsTri τ ∧ ∀ z ∈ Ker F1 τ, ∀ w ∈ Ker F1 τ, z ≠ w →
      ¬ compat z w ∧ CNX F1 z w = τ := by
    intro τ hτ
    obtain ⟨p, q, hpq, rfl⟩ := mem_BT.1 hτ
    refine ⟨hpq.2.2, fun z hz w hw hzw => ?_⟩
    have hnc := stage1_ker hcs hg hpq hz hw hzw
    exact ⟨hnc, CNX_eq_of_ker hg1 hpq.2.2 hz hw hzw hnc⟩
  have hD : D.card ≤ P.card := by
    calc D.card ≤ ∑ τ ∈ BT compat F1, ((Ker F1 τ \ keep3 (Ker F1 τ)) ×ˢ τ).card := card_biUnion_le
      _ ≤ ∑ τ ∈ BT compat F1, (((Ker F1 τ \ keep3 (Ker F1 τ)) ×ˢ keep3 (Ker F1 τ)).image
            (fun p => s(p.1, p.2))).card := by
          apply sum_le_sum
          intro τ hτ
          rw [card_image_of_injOn]
          · rw [card_product, card_product]
            by_cases h3 : 3 ≤ (Ker F1 τ).card
            · rw [keep3_card _ h3, (hfacts τ hτ).1.card_eq]
            · rw [sdiff_keep3_empty _ (by omega)]; simp
          · intro p hp p' hp' h
            simp only [coe_product, Set.mem_prod, mem_coe, mem_sdiff] at hp hp'
            rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Prod.ext h1 h2
            · exact absurd (h1 ▸ hp'.2) hp.1.2
      _ = P.card := by
          rw [card_biUnion]
          intro τ hτ τ' hτ' hne
          rw [Function.onFun, disjoint_left]
          intro q hq hq'
          obtain ⟨⟨z, w⟩, hzw, rfl⟩ := mem_image.1 hq
          obtain ⟨⟨z', w'⟩, hzw', he⟩ := mem_image.1 hq'
          simp only [mem_product, mem_sdiff] at hzw hzw'
          have hzw_ne : z ≠ w := fun h => hzw.1.2 (h ▸ hzw.2)
          have hzw_ne' : z' ≠ w' := fun h => hzw'.1.2 (h ▸ hzw'.2)
          have e1 := ((hfacts τ hτ).2 z hzw.1.1 w (keep3_sub _ hzw.2) hzw_ne).2
          have e2 := ((hfacts τ' hτ').2 z' hzw'.1.1 w' (keep3_sub _ hzw'.2) hzw_ne').2
          apply hne
          rw [← e1, ← e2]
          rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rfl
          · exact CNX_comm _ _ _
  have hPsub : P ⊆ CXI compat F1 \ CXI compat F2 := by
    intro q hq
    obtain ⟨τ, hτ, hq⟩ := mem_biUnion.1 hq
    obtain ⟨⟨z, w⟩, hzw, rfl⟩ := mem_image.1 hq
    simp only [mem_product, mem_sdiff] at hzw
    have hzw_ne : z ≠ w := fun h => hzw.1.2 (h ▸ hzw.2)
    obtain ⟨hnc, hct⟩ := (hfacts τ hτ).2 z hzw.1.1 w (keep3_sub _ hzw.2) hzw_ne
    have hτne : τ.Nonempty := by rw [← card_pos, (hfacts τ hτ).1.card_eq]; norm_num
    refine mem_sdiff.2 ⟨(mem_CXI hcs).2 ⟨hzw_ne, hnc, hct ▸ hτne⟩, fun h => ?_⟩
    obtain ⟨-, -, ⟨e, he⟩⟩ := (mem_CXI hcs).1 h
    have he1 : e ∈ τ := hct ▸ CNX_mono (stage2_sub F1) z w he
    have hzF2 : (z, e) ∈ F2 := ((mem_CNX F2).1 he).1
    have : (z, e) ∈ D := mem_biUnion.2 ⟨τ, hτ, mem_product.2 ⟨mem_sdiff.2 hzw.1, he1⟩⟩
    have hz' : (z, e) ∈ F1 \ D := by
      unfold F2 stage2 at hzF2; convert hzF2 using 2
    exact (mem_sdiff.1 hz').2 this
  have hP := card_le_card hPsub
  have hmono : CXI compat F2 ⊆ CXI compat F1 := CXI_mono hcs (stage2_sub F1)
  rw [card_sdiff_of_subset hmono] at hP
  have := card_le_card hmono
  omega

/-- After stages 1 and 2: kernels of `β`-triangles are pairwise incompatible of size at most 3. -/
lemma stage2_ker (hcs : ∀ a b, compat a b → compat b a) {F : Finset (X × Sym2 (Fin m))}
    (hg : Good1 compat F) {p q : X}
    (hb : BetaPair compat (stage2 compat (stage1 compat F)) p q) :
    (∀ a ∈ Ker (stage2 compat (stage1 compat F)) (CNX (stage2 compat (stage1 compat F)) p q),
      ∀ b ∈ Ker (stage2 compat (stage1 compat F)) (CNX (stage2 compat (stage1 compat F)) p q),
        a ≠ b → ¬ compat a b) ∧
    (Ker (stage2 compat (stage1 compat F)) (CNX (stage2 compat (stage1 compat F)) p q)).card ≤ 3 := by
  classical
  set F1 := stage1 compat F
  set F2 := stage2 compat F1
  have hg1 : Good1 compat F1 := hg.mono (stage1_sub F)
  have hb1 : BetaPair compat F1 p q := hb.mono_of_sub (stage2_sub F1) hg1
  have hτ : CNX F1 p q = CNX F2 p q := hb.of_sub (stage2_sub F1) hg1
  have hKsub : Ker F2 (CNX F2 p q) ⊆ Ker F1 (CNX F1 p q) := by
    rw [hτ]; exact Ker_mono (stage2_sub F1) _
  refine ⟨fun a ha b hb' hab => stage1_ker hcs hg hb1 (hKsub ha) (hKsub hb') hab, ?_⟩
  have hBT : CNX F1 p q ∈ BT compat F1 := mem_BT.2 ⟨p, q, hb1, rfl⟩
  have hsub : Ker F2 (CNX F2 p q) ⊆ keep3 (Ker F1 (CNX F1 p q)) := by
    intro z hz
    by_contra hzk
    obtain ⟨e, he⟩ : (CNX F1 p q).Nonempty := by rw [← card_pos, hb1.2.2.card_eq]; norm_num
    have h1 : (z, e) ∈ F2 := mem_Ker.1 hz e (hτ ▸ he)
    have h2 : (z, e) ∈ (BT compat F1).biUnion (fun τ => (Ker F1 τ \ keep3 (Ker F1 τ)) ×ˢ τ) :=
      mem_biUnion.2 ⟨_, hBT, mem_product.2 ⟨mem_sdiff.2 ⟨hKsub hz, hzk⟩, he⟩⟩
    have h3 : (z, e) ∈ F1 \ (BT compat F1).biUnion (fun τ => (Ker F1 τ \ keep3 (Ker F1 τ)) ×ˢ τ) := by
      unfold F2 stage2 at h1; convert h1 using 2
    exact (mem_sdiff.1 h3).2 h2
  exact (card_le_card hsub).trans (keep3_card_le _)

end Stage2

/-! ## Stage 3: compatible bridges -/

section Stage3

variable {compat : X → X → Prop}

/-- A compatible chain between two kernel vertices. -/
def Chainy (compat : X → X → Prop) (F : Finset (X × Sym2 (Fin m))) (τ : Finset (Sym2 (Fin m))) :
    Prop :=
  ∃ x ∈ Ker F τ, ∃ x'' ∈ Ker F τ, ∃ x', x ≠ x'' ∧ x ≠ x' ∧ x' ≠ x'' ∧ compat x x' ∧ compat x' x''

open scoped Classical in
noncomputable def stage3 (compat : X → X → Prop) (F : Finset (X × Sym2 (Fin m))) :
    Finset (X × Sym2 (Fin m)) :=
  F \ ((BT compat F).filter (Chainy compat F)).biUnion (fun τ => Ker F τ ×ˢ τ)

lemma stage3_sub (F : Finset (X × Sym2 (Fin m))) : stage3 compat F ⊆ F := sdiff_subset

open scoped Classical in
lemma chains_card {D : ℕ} (hD : ∀ x, (cnb compat x).card ≤ D) :
    ((univ : Finset (X × X × X)).filter (fun p => p.1 ≠ p.2.1 ∧ p.2.1 ≠ p.2.2 ∧
      compat p.1 p.2.1 ∧ compat p.2.1 p.2.2)).card ≤ Fintype.card X * D * D := by
  calc _ ≤ ((univ : Finset X).biUnion (fun x₁ => (cnb compat x₁).biUnion
        (fun x₂ => (cnb compat x₂).image (fun x₃ => (x₁, x₂, x₃))))).card := by
        apply card_le_card
        intro p hp
        simp only [mem_filter, mem_univ, true_and] at hp
        simp only [mem_biUnion, mem_univ, true_and, mem_image, cnb, mem_filter]
        exact ⟨p.1, p.2.1, ⟨hp.1.symm, hp.2.2.1⟩, p.2.2, ⟨hp.2.1.symm, hp.2.2.2⟩, rfl⟩
    _ ≤ ∑ x₁ : X, ((cnb compat x₁).biUnion
        (fun x₂ => (cnb compat x₂).image (fun x₃ => (x₁, x₂, x₃)))).card := card_biUnion_le
    _ ≤ ∑ _x₁ : X, D * D := by
        apply sum_le_sum
        intro x₁ _
        calc _ ≤ ∑ x₂ ∈ cnb compat x₁, ((cnb compat x₂).image (fun x₃ => (x₁, x₂, x₃))).card :=
              card_biUnion_le
          _ ≤ ∑ _x₂ ∈ cnb compat x₁, D :=
              sum_le_sum (fun x₂ _ => card_image_le.trans (hD x₂))
          _ ≤ D * D := by rw [sum_const, smul_eq_mul]; exact Nat.mul_le_mul_right _ (hD x₁)
    _ = Fintype.card X * D * D := by rw [sum_const, card_univ, smul_eq_mul, mul_assoc]

lemma stage3_cost (hcs : ∀ a b, compat a b → compat b a) {D : ℕ}
    (hD : ∀ x, (cnb compat x).card ≤ D) {F : Finset (X × Sym2 (Fin m))} (hg : Good1 compat F) :
    (stage2 compat (stage1 compat F)).card ≤
      (stage3 compat (stage2 compat (stage1 compat F))).card + 9 * (Fintype.card X * D * D) := by
  classical
  set F2 := stage2 compat (stage1 compat F)
  have hg2 : Good1 compat F2 := (hg.mono (stage1_sub F)).mono (stage2_sub _)
  set Bad := (BT compat F2).filter (Chainy compat F2)
  set Dl := Bad.biUnion (fun τ => Ker F2 τ ×ˢ τ)
  have hF3 : (stage3 compat F2).card = (F2 \ Dl).card := by unfold stage3; convert rfl
  have h1 : F2.card ≤ (stage3 compat F2).card + Dl.card := by
    have := card_sdiff_add_card_inter F2 Dl
    have h2 : (F2 ∩ Dl).card ≤ Dl.card := card_le_card inter_subset_right
    omega
  have hker : ∀ τ ∈ BT compat F2, IsTri τ ∧ (Ker F2 τ).card ≤ 3 ∧
      ∀ z ∈ Ker F2 τ, ∀ w ∈ Ker F2 τ, z ≠ w → CNX F2 z w = τ := by
    intro τ hτ
    obtain ⟨p, q, hpq, rfl⟩ := mem_BT.1 hτ
    obtain ⟨hinc, hc3⟩ := stage2_ker hcs hg hpq
    exact ⟨hpq.2.2, hc3, fun z hz w hw hzw =>
      CNX_eq_of_ker hg2 hpq.2.2 hz hw hzw (hinc z hz w hw hzw)⟩
  have h2 : Dl.card ≤ 9 * Bad.card := by
    calc Dl.card ≤ ∑ τ ∈ Bad, (Ker F2 τ ×ˢ τ).card := card_biUnion_le
      _ ≤ ∑ _τ ∈ Bad, 9 := by
          apply sum_le_sum
          intro τ hτ
          have := hker τ (mem_filter.1 hτ).1
          rw [card_product, this.1.card_eq]
          omega
      _ = 9 * Bad.card := by rw [sum_const, smul_eq_mul, mul_comm]
  have h3 : Bad.card ≤ Fintype.card X * D * D := by
    have hch : ∀ τ ∈ Bad, ∃ t : X × X × X, t.1 ∈ Ker F2 τ ∧ t.2.2 ∈ Ker F2 τ ∧ t.1 ≠ t.2.2 ∧
        t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ compat t.1 t.2.1 ∧ compat t.2.1 t.2.2 := by
      intro τ hτ
      obtain ⟨x, hx, x'', hx'', x', h1, h2, h3, h4, h5⟩ := (mem_filter.1 hτ).2
      exact ⟨(x, x', x''), hx, hx'', h1, h2, h3, h4, h5⟩
    rcases Bad.eq_empty_or_nonempty with hBad | ⟨τ0, hτ0⟩
    · rw [hBad]; simp
    obtain ⟨t0, -⟩ := hch τ0 hτ0
    haveI : Nonempty (X × X × X) := ⟨t0⟩
    choose! f hf using hch
    refine le_trans ?_ (chains_card hD)
    apply card_le_card_of_injOn f
    · intro τ hτ
      obtain ⟨-, -, -, h1, h2, h3, h4⟩ := hf τ hτ
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
      exact ⟨h1, h2, h3, h4⟩
    · intro τ hτ τ' hτ' h
      obtain ⟨a1, a2, a3, -⟩ := hf τ hτ
      obtain ⟨b1, b2, -⟩ := hf τ' hτ'
      have e1 := (hker τ (mem_filter.1 hτ).1).2.2 _ a1 _ a2 a3
      have e2 := (hker τ' (mem_filter.1 hτ').1).2.2 _ b1 _ b2 (h ▸ a3)
      rw [← e1, ← e2, h]
  omega

/-- After the three stages: kernels of `β`-triangles have size 2 or 3, are pairwise
incompatible, and admit no compatible bridge. -/
lemma stage3_ker (hcs : ∀ a b, compat a b → compat b a) {F : Finset (X × Sym2 (Fin m))}
    (hg : Good1 compat F) {p q : X}
    (hb : BetaPair compat (stage3 compat (stage2 compat (stage1 compat F))) p q) :
    let F3 := stage3 compat (stage2 compat (stage1 compat F))
    (∀ a ∈ Ker F3 (CNX F3 p q), ∀ b ∈ Ker F3 (CNX F3 p q), a ≠ b → ¬ compat a b) ∧
    (Ker F3 (CNX F3 p q)).card ≤ 3 ∧ ¬ Chainy compat F3 (CNX F3 p q) := by
  classical
  intro F3
  set F2 := stage2 compat (stage1 compat F)
  have hg2 : Good1 compat F2 := (hg.mono (stage1_sub F)).mono (stage2_sub _)
  have hb2 : BetaPair compat F2 p q := hb.mono_of_sub (stage3_sub F2) hg2
  have hτ : CNX F2 p q = CNX F3 p q := hb.of_sub (stage3_sub F2) hg2
  have hKsub : Ker F3 (CNX F3 p q) ⊆ Ker F2 (CNX F2 p q) := by
    rw [hτ]; exact Ker_mono (stage3_sub F2) _
  obtain ⟨hinc, hc3⟩ := stage2_ker hcs hg hb2
  refine ⟨fun a ha b hb' hab => hinc a (hKsub ha) b (hKsub hb') hab,
    (card_le_card hKsub).trans hc3, ?_⟩
  rintro ⟨x, hx, x'', hx'', x', h1, h2, h3, h4, h5⟩
  have hbad : CNX F2 p q ∈ (BT compat F2).filter (Chainy compat F2) :=
    mem_filter.2 ⟨mem_BT.2 ⟨p, q, hb2, rfl⟩, x, hKsub hx, x'', hKsub hx'', x', h1, h2, h3, h4, h5⟩
  obtain ⟨e, he⟩ : (CNX F2 p q).Nonempty := by rw [← card_pos, hb2.2.2.card_eq]; norm_num
  have hp3 : (p, e) ∈ F3 := ((mem_CNX F3).1 (hτ ▸ he)).1
  have hp3' : (p, e) ∈ F2 \ ((BT compat F2).filter (Chainy compat F2)).biUnion
      (fun τ => Ker F2 τ ×ˢ τ) := by
    unfold F3 stage3 at hp3; convert hp3 using 2
  apply (mem_sdiff.1 hp3').2
  exact mem_biUnion.2 ⟨_, hbad, mem_product.2 ⟨hb2.mem_ker.1, he⟩⟩

end Stage3

/-! ## DL3: normalising the three-vertex kernels -/

section DL3

variable {compat : X → X → Prop}

lemma BT_disj {G : Finset (X × Sym2 (Fin m))} (hg2 : Good2 compat G)
    {τ τ' : Finset (Sym2 (Fin m))} (hτ : τ ∈ BT compat G) (hτ' : τ' ∈ BT compat G)
    (hne : (τ ∩ τ').Nonempty) : τ = τ' := by
  obtain ⟨p, q, hpq, rfl⟩ := mem_BT.1 hτ
  obtain ⟨p', q', hpq', rfl⟩ := mem_BT.1 hτ'
  exact hg2 _ _ _ _ hpq hpq' hne

lemma BT_tri {G : Finset (X × Sym2 (Fin m))} {τ : Finset (Sym2 (Fin m))}
    (hτ : τ ∈ BT compat G) : IsTri τ := by
  obtain ⟨p, q, hpq, rfl⟩ := mem_BT.1 hτ
  exact hpq.2.2

open scoped Classical in
/-- Ordered vertices of a triangle. -/
noncomputable def triV (h0 : Fin m) (τ : Finset (Sym2 (Fin m))) : Fin m × Fin m × Fin m :=
  if h : IsTri τ then (h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose)
  else (h0, h0, h0)

lemma triV_spec (h0 : Fin m) {τ : Finset (Sym2 (Fin m))} (h : IsTri τ) :
    (triV h0 τ).1 < (triV h0 τ).2.1 ∧ (triV h0 τ).2.1 < (triV h0 τ).2.2 ∧
      τ = tri (triV h0 τ).1 (triV h0 τ).2.1 (triV h0 τ).2.2 := by
  classical
  rw [triV, dif_pos h]
  exact h.choose_spec.choose_spec.choose_spec

/-- A compatible pair inside a set. -/
def HasCompatPair (compat : X → X → Prop) (A : Finset X) : Prop :=
  ∃ u ∈ A, ∃ v ∈ A, u ≠ v ∧ compat u v

open scoped Classical in
noncomputable def keepE (compat : X → X → Prop) (G : Finset (X × Sym2 (Fin m))) (h0 : Fin m)
    (τ : Finset (Sym2 (Fin m))) : Sym2 (Fin m) :=
  if HasCompatPair compat (Nb G s((triV h0 τ).1, (triV h0 τ).2.1)) then
    s((triV h0 τ).1, (triV h0 τ).2.1) else s((triV h0 τ).1, (triV h0 τ).2.2)

open scoped Classical in
noncomputable def xpp (G : Finset (X × Sym2 (Fin m))) (x0 : X) (τ : Finset (Sym2 (Fin m))) : X :=
  if h : (Ker G τ).Nonempty then h.choose else x0

lemma xpp_mem {G : Finset (X × Sym2 (Fin m))} (x0 : X) {τ : Finset (Sym2 (Fin m))}
    (h : (Ker G τ).Nonempty) : xpp G x0 τ ∈ Ker G τ := by
  classical
  rw [xpp, dif_pos h]; exact h.choose_spec

open scoped Classical in
noncomputable def BT3 (compat : X → X → Prop) (G : Finset (X × Sym2 (Fin m))) :
    Finset (Finset (Sym2 (Fin m))) :=
  (BT compat G).filter (fun τ => (Ker G τ).card = 3)

open scoped Classical in
noncomputable def Del3 (compat : X → X → Prop) (G : Finset (X × Sym2 (Fin m))) (h0 : Fin m)
    (x0 : X) : Finset (X × Sym2 (Fin m)) :=
  (BT3 compat G).biUnion (fun τ => {xpp G x0 τ} ×ˢ (τ.erase (keepE compat G h0 τ)))

open scoped Classical in
noncomputable def E0s (compat : X → X → Prop) (G : Finset (X × Sym2 (Fin m))) (x0 : X) :
    Finset (Sym2 X) :=
  (BT3 compat G).biUnion (fun τ => ((Ker G τ).erase (xpp G x0 τ)).image
    (fun w => s(w, xpp G x0 τ)))

lemma keepE_mem (h0 : Fin m) {G : Finset (X × Sym2 (Fin m))} {τ : Finset (Sym2 (Fin m))}
    (h : IsTri τ) : keepE compat G h0 τ ∈ τ := by
  classical
  obtain ⟨h1, h2, h3⟩ := triV_spec h0 h
  unfold keepE
  rcases hT : triV h0 τ with ⟨a, b, c⟩
  rw [hT] at h1 h2 h3
  simp only at h1 h2 h3 ⊢
  split_ifs
  · rw [h3]; simp [tri]
  · rw [h3]; simp [tri]

lemma keepE_ne_bc (h0 : Fin m) {G : Finset (X × Sym2 (Fin m))} {τ : Finset (Sym2 (Fin m))}
    (h : IsTri τ) : keepE compat G h0 τ ≠ s((triV h0 τ).2.1, (triV h0 τ).2.2) := by
  classical
  obtain ⟨h1, h2, -⟩ := triV_spec h0 h
  unfold keepE
  rcases hT : triV h0 τ with ⟨a, b, c⟩
  rw [hT] at h1 h2
  simp only at h1 h2 ⊢
  split_ifs
  · intro he; rw [Sym2.eq_iff] at he; omega
  · intro he; rw [Sym2.eq_iff] at he; omega

/-- Membership in `G \ Del3` for an edge of a `β`-triangle. -/
lemma mem_F0_tri {G : Finset (X × Sym2 (Fin m))} (hg2 : Good2 compat G) (h0 : Fin m) (x0 : X)
    {τ : Finset (Sym2 (Fin m))} (hτ : τ ∈ BT compat G) {z : X} {e : Sym2 (Fin m)}
    (he : e ∈ τ) :
    (z, e) ∈ G \ Del3 compat G h0 x0 ↔ (z, e) ∈ G ∧
      ¬ (τ ∈ BT3 compat G ∧ z = xpp G x0 τ ∧ e ≠ keepE compat G h0 τ) := by
  classical
  rw [mem_sdiff]
  apply and_congr_right
  intro _
  constructor
  · intro hnot ⟨h3, hz, hke⟩
    apply hnot
    exact mem_biUnion.2 ⟨τ, h3, mem_product.2 ⟨by simp [hz], mem_erase.2 ⟨hke, he⟩⟩⟩
  · intro hnot hD
    obtain ⟨τ', hτ', hm⟩ := mem_biUnion.1 hD
    rw [mem_product, mem_singleton, mem_erase] at hm
    have hτ'BT : τ' ∈ BT compat G := (mem_filter.1 hτ').1
    have heq : τ' = τ := BT_disj hg2 hτ'BT hτ ⟨e, mem_inter.2 ⟨hm.2.2, he⟩⟩
    subst heq
    exact hnot ⟨hτ', hm.1, hm.2.1⟩

lemma mem_F0_off {G : Finset (X × Sym2 (Fin m))} (h0 : Fin m) (x0 : X) {z : X}
    {e : Sym2 (Fin m)} (he : ∀ τ ∈ BT compat G, e ∉ τ) :
    (z, e) ∈ G \ Del3 compat G h0 x0 ↔ (z, e) ∈ G := by
  classical
  rw [mem_sdiff]
  refine ⟨fun h => h.1, fun h => ⟨h, fun hD => ?_⟩⟩
  obtain ⟨τ', hτ', hm⟩ := mem_biUnion.1 hD
  rw [mem_product, mem_singleton, mem_erase] at hm
  exact he τ' (mem_filter.1 hτ').1 hm.2.2

/-- Kernel property after the three stages. -/
def KerProp (compat : X → X → Prop) (G : Finset (X × Sym2 (Fin m))) : Prop :=
  ∀ σ ∈ BT compat G, (∀ a ∈ Ker G σ, ∀ b ∈ Ker G σ, a ≠ b → ¬ compat a b) ∧
    (Ker G σ).card ≤ 3 ∧ ¬ Chainy compat G σ

lemma dl3_cost {G : Finset (X × Sym2 (Fin m))} (hg1 : Good1 compat G) (hg2 : Good2 compat G)
    (hKP : KerProp compat G) (h0 : Fin m) (x0 : X) :
    G.card ≤ (G \ Del3 compat G h0 x0).card + (E0s compat G x0).card := by
  classical
  have h1 : G.card ≤ (G \ Del3 compat G h0 x0).card + (Del3 compat G h0 x0).card := by
    have := card_sdiff_add_card_inter G (Del3 compat G h0 x0)
    have h2 := card_le_card (inter_subset_right (s₁ := G) (s₂ := Del3 compat G h0 x0))
    omega
  have h2 : (Del3 compat G h0 x0).card ≤ ∑ _τ ∈ BT3 compat G, 2 := by
    calc _ ≤ ∑ τ ∈ BT3 compat G, ({xpp G x0 τ} ×ˢ (τ.erase (keepE compat G h0 τ))).card :=
          card_biUnion_le
      _ ≤ _ := by
          apply sum_le_sum
          intro τ hτ
          have ht := BT_tri (mem_filter.1 hτ).1
          rw [card_product, card_singleton, card_erase_of_mem (keepE_mem h0 ht), ht.card_eq]
  have h3 : (E0s compat G x0).card = ∑ _τ ∈ BT3 compat G, 2 := by
    rw [E0s, card_biUnion]
    · apply sum_congr rfl
      intro τ hτ
      have hK := (mem_filter.1 hτ).2
      have hne : (Ker G τ).Nonempty := by rw [← card_pos, hK]; norm_num
      rw [card_image_of_injOn, card_erase_of_mem (xpp_mem x0 hne), hK]
      intro w _ w' _ h
      simpa using Sym2.congr_right.1 (by simpa [Sym2.eq_swap] using h)
    · intro τ hτ τ' hτ' hne
      rw [Function.onFun, disjoint_left]
      intro q hq hq'
      obtain ⟨w, hw, rfl⟩ := mem_image.1 hq
      obtain ⟨w', hw', he⟩ := mem_image.1 hq'
      have hb : ∀ σ ∈ BT3 compat G, ∀ v ∈ (Ker G σ).erase (xpp G x0 σ),
          CNX G v (xpp G x0 σ) = σ := by
        intro σ hσ v hv
        have hσBT := (mem_filter.1 hσ).1
        have hne : (Ker G σ).Nonempty := by
          rw [← card_pos, (mem_filter.1 hσ).2]; norm_num
        exact CNX_eq_of_ker hg1 (BT_tri hσBT) (mem_of_mem_erase hv) (xpp_mem x0 hne)
          (ne_of_mem_erase hv) ((hKP σ hσBT).1 _ (mem_of_mem_erase hv) _ (xpp_mem x0 hne)
            (ne_of_mem_erase hv))
      apply hne
      rw [← hb τ hτ w hw, ← hb τ' hτ' w' hw']
      rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2, CNX_comm]
  omega

/-- Facts about `E0s`: each member comes from a three-kernel triangle and its extra vertex. -/
lemma mem_E0s {G : Finset (X × Sym2 (Fin m))} (x0 : X) {q : Sym2 X} :
    q ∈ E0s compat G x0 ↔ ∃ τ ∈ BT3 compat G, ∃ w ∈ (Ker G τ).erase (xpp G x0 τ),
      q = s(w, xpp G x0 τ) := by
  classical
  simp only [E0s, mem_biUnion, mem_image]
  constructor
  · rintro ⟨τ, hτ, w, hw, rfl⟩; exact ⟨τ, hτ, w, hw, rfl⟩
  · rintro ⟨τ, hτ, w, hw, rfl⟩; exact ⟨τ, hτ, w, hw, rfl⟩

lemma ker_nonempty_of_BT3 {G : Finset (X × Sym2 (Fin m))} {τ : Finset (Sym2 (Fin m))}
    (hτ : τ ∈ BT3 compat G) : (Ker G τ).Nonempty := by
  rw [← card_pos, (mem_filter.1 hτ).2]; norm_num

/-- The common neighbourhood of an `E0` pair in `F0` lies in the kept edge. -/
lemma E0_CNX {G : Finset (X × Sym2 (Fin m))} (hg1 : Good1 compat G) (hg2 : Good2 compat G)
    (hKP : KerProp compat G) (h0 : Fin m) (x0 : X) {τ : Finset (Sym2 (Fin m))}
    (hτ : τ ∈ BT3 compat G) {w : X} (hw : w ∈ (Ker G τ).erase (xpp G x0 τ)) :
    CNX G w (xpp G x0 τ) = τ ∧
    CNX (G \ Del3 compat G h0 x0) w (xpp G x0 τ) ⊆ {keepE compat G h0 τ} ∧
    keepE compat G h0 τ ∈ CNX (G \ Del3 compat G h0 x0) w (xpp G x0 τ) := by
  classical
  have hτBT := (mem_filter.1 hτ).1
  have ht := BT_tri hτBT
  have hne := ker_nonempty_of_BT3 hτ
  have hxk := xpp_mem x0 hne
  have hwk := mem_of_mem_erase hw
  have hwx := ne_of_mem_erase hw
  have hct : CNX G w (xpp G x0 τ) = τ := CNX_eq_of_ker hg1 ht hwk hxk hwx
    ((hKP τ hτBT).1 _ hwk _ hxk hwx)
  refine ⟨hct, ?_, ?_⟩
  · intro e he
    rw [mem_singleton]
    have he' : e ∈ τ := hct ▸ CNX_mono sdiff_subset _ _ he
    rw [mem_CNX] at he
    by_contra hk
    have := (mem_F0_tri hg2 h0 x0 hτBT he').1 he.2
    exact this.2 ⟨hτ, rfl, hk⟩
  · have hk := keepE_mem (compat := compat) (G := G) h0 ht
    rw [mem_CNX, mem_F0_tri hg2 h0 x0 hτBT hk, mem_F0_tri hg2 h0 x0 hτBT hk]
    refine ⟨⟨mem_Ker.1 hwk _ hk, fun h => hwx h.2.1⟩, ⟨mem_Ker.1 hxk _ hk, fun h => h.2.2 rfl⟩⟩

/-- `β`-pairs not in `E0s` keep their triangle. -/
lemma beta_F0 {G : Finset (X × Sym2 (Fin m))} (hg1 : Good1 compat G) (hg2 : Good2 compat G)
    (hKP : KerProp compat G) (hcs : ∀ a b, compat a b → compat b a) (h0 : Fin m) (x0 : X)
    {x x' : X} (hb : BetaPair compat G x x') (hE : s(x, x') ∉ E0s compat G x0) :
    CNX (G \ Del3 compat G h0 x0) x x' = CNX G x x' := by
  classical
  have hτBT : CNX G x x' ∈ BT compat G := mem_BT.2 ⟨x, x', hb, rfl⟩
  obtain ⟨hxk, hx'k⟩ := hb.mem_ker
  apply Subset.antisymm (CNX_mono sdiff_subset x x')
  intro e he
  rw [mem_CNX, mem_F0_tri hg2 h0 x0 hτBT he, mem_F0_tri hg2 h0 x0 hτBT he]
  rw [mem_CNX] at he
  refine ⟨⟨he.1, fun ⟨h3, hx, _⟩ => ?_⟩, ⟨he.2, fun ⟨h3, hx, _⟩ => ?_⟩⟩
  · apply hE; rw [mem_E0s]
    refine ⟨_, h3, x', mem_erase.2 ⟨fun h => hb.1 (hx.trans h.symm), hx'k⟩, ?_⟩
    rw [Sym2.eq_swap, ← hx]
  · apply hE; rw [mem_E0s]
    exact ⟨_, h3, x, mem_erase.2 ⟨fun h => hb.1 (h.trans hx.symm), hxk⟩, by rw [← hx]⟩

end DL3

/-! ## DL5: the structure after the pass -/

section DL5

variable {compat : X → X → Prop} (hcs : ∀ a b, compat a b → compat b a)
  {G : Finset (X × Sym2 (Fin m))} (hg1 : Good1 compat G) (hg2 : Good2 compat G)
  (hKP : KerProp compat G) (h0 : Fin m) (x0 : X) {Fn : Finset (X × Sym2 (Fin m))}
  (hFn0 : Fn ⊆ G \ Del3 compat G h0 x0)
  (hFn : ∀ x x', x ≠ x' → ¬ compat x x' → (CNX (G \ Del3 compat G h0 x0) x x').Nonempty →
    s(x, x') ∉ E0s compat G x0 → ∀ e ∈ CNX Fn x x', gS (CNX (G \ Del3 compat G h0 x0) x x') h0 ∉ e)

include hcs hg1 hg2 hKP hFn0 hFn in
/-- Every surviving incompatible pair is a `β`-pair of `G`, surviving on `bc` or the kept edge. -/
lemma cn_Fn {x x' : X} (hxx' : x ≠ x') (hnc : ¬ compat x x') {e : Sym2 (Fin m)}
    (he : e ∈ CNX Fn x x') :
    BetaPair compat G x x' ∧ e ∈ CNX G x x' ∧
      (s(x, x') ∈ E0s compat G x0 → e = keepE compat G h0 (CNX G x x')) ∧
      (s(x, x') ∉ E0s compat G x0 →
        e = s((triV h0 (CNX G x x')).2.1, (triV h0 (CNX G x x')).2.2)) := by
  classical
  set F0 := G \ Del3 compat G h0 x0
  have heF0 : e ∈ CNX F0 x x' := CNX_mono hFn0 x x' he
  have heG : e ∈ CNX G x x' := CNX_mono sdiff_subset x x' heF0
  by_cases hE : s(x, x') ∈ E0s compat G x0
  · obtain ⟨τ, hτ, w, hw, hq⟩ := (mem_E0s x0).1 hE
    obtain ⟨hct, hsub, -⟩ := E0_CNX hg1 hg2 hKP h0 x0 hτ hw
    have hor : CNX G x x' = CNX G w (xpp G x0 τ) ∧
        CNX F0 x x' = CNX F0 w (xpp G x0 τ) := by
      rcases Sym2.eq_iff.1 hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
      · exact ⟨CNX_comm _ _ _, CNX_comm _ _ _⟩
    have hτt := BT_tri (mem_filter.1 hτ).1
    have hτx : IsTri (CNX G x x') := by rw [hor.1, hct]; exact hτt
    refine ⟨⟨hxx', hnc, hτx⟩, heG, fun _ => ?_, fun h => absurd hE h⟩
    have := hsub (hor.2 ▸ heF0)
    rw [mem_singleton] at this
    rw [hor.1, hct]; exact this
  · have hne : (CNX F0 x x').Nonempty := ⟨e, heF0⟩
    have hav := hFn x x' hxx' hnc hne hE e he
    by_cases ht : IsTri (CNX F0 x x')
    · obtain ⟨a, b, c, h1, h2, hS⟩ := ht
      have hb0 : BetaPair compat F0 x x' := ⟨hxx', hnc, ⟨a, b, c, h1, h2, hS⟩⟩
      have hGeq : CNX G x x' = CNX F0 x x' := hb0.of_sub sdiff_subset hg1
      have hga := gS_tri h1 h2 hS h0
      rw [hga] at hav
      have hspec := triV_spec h0 (show IsTri (CNX G x x') from hGeq ▸ ⟨a, b, c, h1, h2, hS⟩)
      obtain ⟨g1, g2, g3⟩ := hspec
      have hv := verts_of_tri g1 g2 h1 h2 (g3.symm.trans (hGeq.trans hS))
      refine ⟨hb0.mono_of_sub sdiff_subset hg1, heG, fun h => absurd h hE, fun _ => ?_⟩
      rw [hv.2.1, hv.2.2]
      have hm := hS ▸ heF0
      simp only [mem_tri] at hm
      rcases hm with rfl | rfl | rfl
      · exact absurd (Sym2.mem_mk_left a b) hav
      · rfl
      · exact absurd (Sym2.mem_mk_left a c) hav
    · exfalso
      have hg0 : Good1 compat F0 := hg1.mono sdiff_subset
      rcases hg0 x x' hxx' hnc with hs | ht'
      · exact hav (gS_star hs ht h0 e heF0)
      · exact ht ht'

include hcs hg1 hg2 hKP hFn0 hFn in
/-- A non-compatible neighbourhood lies in the kernel of the `β`-triangle through `e`. -/
lemma yn_structure {e : Sym2 (Fin m)} (hnc : ¬ CompatSet compat (Nb Fn e)) :
    ∃ x x', x ∈ Nb Fn e ∧ x' ∈ Nb Fn e ∧ x ≠ x' ∧ ¬ compat x x' ∧
      BetaPair compat G x x' ∧ e ∈ CNX G x x' ∧ Nb Fn e ⊆ Ker G (CNX G x x') := by
  classical
  simp only [CompatSet, not_forall] at hnc
  obtain ⟨x, hx, x', hx', hxx', hnc'⟩ := hnc
  have he : e ∈ CNX Fn x x' := by rw [mem_CNX]; exact ⟨(mem_Nb Fn).1 hx, (mem_Nb Fn).1 hx'⟩
  obtain ⟨hb, heG, -, -⟩ := cn_Fn hcs hg1 hg2 hKP h0 x0 hFn0 hFn hxx' hnc' he
  have hτBT : CNX G x x' ∈ BT compat G := mem_BT.2 ⟨x, x', hb, rfl⟩
  obtain ⟨hxk, hx'k⟩ := hb.mem_ker
  refine ⟨x, x', hx, hx', hxx', hnc', hb, heG, fun v hv => ?_⟩
  by_cases hvx : v = x
  · rw [hvx]; exact hxk
  by_cases hvx' : v = x'
  · rw [hvx']; exact hx'k
  have hsame : ∀ w, w ∈ Nb Fn e → v ≠ w → ¬ compat v w → v ∈ Ker G (CNX G x x') := by
    intro w hw hvw hncw
    have he' : e ∈ CNX Fn v w := by rw [mem_CNX]; exact ⟨(mem_Nb Fn).1 hv, (mem_Nb Fn).1 hw⟩
    obtain ⟨hb', heG', -, -⟩ := cn_Fn hcs hg1 hg2 hKP h0 x0 hFn0 hFn hvw hncw he'
    have hτ' : CNX G v w ∈ BT compat G := mem_BT.2 ⟨v, w, hb', rfl⟩
    have heq := BT_disj hg2 hτ' hτBT ⟨e, mem_inter.2 ⟨heG', heG⟩⟩
    rw [← heq]; exact hb'.mem_ker.1
  by_cases hc1 : compat v x
  · by_cases hc2 : compat v x'
    · exfalso
      exact (hKP _ hτBT).2.2 ⟨x, hxk, x', hx'k, v, hxx', Ne.symm hvx, hvx', hcs _ _ hc1, hc2⟩
    · exact hsame x' hx' hvx' hc2
  · exact hsame x hx hvx hc1

include hcs hg1 hg2 hKP hFn0 hFn in
/-- A non-compatible neighbourhood is exactly a `β`-pair. -/
lemma yn_pair {e : Sym2 (Fin m)} (hnc : ¬ CompatSet compat (Nb Fn e)) :
    ∃ x x', Nb Fn e = {x, x'} ∧ BetaPair compat G x x' ∧ e ∈ CNX G x x' := by
  classical
  obtain ⟨x, x', hx, hx', hxx', hnc', hb, heG, hsub⟩ :=
    yn_structure hcs hg1 hg2 hKP h0 x0 hFn0 hFn hnc
  refine ⟨x, x', ?_, hb, heG⟩
  set τ := CNX G x x' with hτdef
  have hτBT : τ ∈ BT compat G := mem_BT.2 ⟨x, x', hb, rfl⟩
  have hK3 := (hKP τ hτBT).2.1
  have hpair : ({x, x'} : Finset X) ⊆ Nb Fn e := by
    intro z hz; simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  by_contra hneq
  have hlt : ({x, x'} : Finset X).card < (Nb Fn e).card :=
    card_lt_card (ssubset_of_subset_of_ne hpair (Ne.symm hneq))
  rw [card_pair hxx'] at hlt
  have hN3 : (Nb Fn e).card = 3 := by have := card_le_card hsub; omega
  have hNK : Nb Fn e = Ker G τ := eq_of_subset_of_card_le hsub (by omega)
  have hτ3 : τ ∈ BT3 compat G := mem_filter.2 ⟨hτBT, by rw [← hNK, hN3]⟩
  have hKne := ker_nonempty_of_BT3 hτ3
  set z := xpp G x0 τ
  have hz : z ∈ Ker G τ := xpp_mem x0 hKne
  -- the two other kernel vertices
  have h1lt : 1 < ((Ker G τ).erase z).card := by
    rw [card_erase_of_mem hz, ← hNK, hN3]; norm_num
  obtain ⟨y₁, hy₁, y₂, hy₂, hy⟩ := one_lt_card.1 h1lt
  have hy₁k := mem_of_mem_erase hy₁
  have hy₂k := mem_of_mem_erase hy₂
  have hinc := (hKP τ hτBT).1 _ hy₁k _ hy₂k hy
  have hct : CNX G y₁ y₂ = τ := CNX_eq_of_ker hg1 (BT_tri hτBT) hy₁k hy₂k hy hinc
  have hE : s(y₁, y₂) ∉ E0s compat G x0 := by
    intro hE
    obtain ⟨σ, hσ, w, hw, hq⟩ := (mem_E0s x0).1 hE
    obtain ⟨hcσ, -, -⟩ := E0_CNX hg1 hg2 hKP h0 x0 hσ hw
    have hστ : σ = τ := by
      rw [← hcσ, ← hct]
      rcases Sym2.eq_iff.1 hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2, CNX_comm]
    rcases Sym2.eq_iff.1 hq with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact ne_of_mem_erase hy₂ (by rw [h2, hστ])
    · exact ne_of_mem_erase hy₁ (by rw [h1, hστ])
  have hey : e ∈ CNX Fn y₁ y₂ := by
    rw [mem_CNX]
    exact ⟨(mem_Nb Fn).1 (hNK ▸ hy₁k), (mem_Nb Fn).1 (hNK ▸ hy₂k)⟩
  obtain ⟨-, -, -, hbc⟩ := cn_Fn hcs hg1 hg2 hKP h0 x0 hFn0 hFn hy hinc hey
  have hbc' := hbc hE
  rw [hct] at hbc'
  have hzF : (z, e) ∈ G \ Del3 compat G h0 x0 := hFn0 ((mem_Nb Fn).1 (hNK ▸ hz))
  have heτ : e ∈ τ := hτdef ▸ heG
  have := ((mem_F0_tri hg2 h0 x0 hτBT heτ).1 hzF).2
  apply this
  refine ⟨hτ3, rfl, ?_⟩
  rw [hbc']
  exact (keepE_ne_bc h0 (BT_tri hτBT)).symm

include hcs hg1 hg2 hKP hFn0 hFn in
/-- Which edges of a `β`-triangle can carry a non-compatible neighbourhood. -/
lemma tri_status {τ : Finset (Sym2 (Fin m))} (hτ : τ ∈ BT compat G) {e : Sym2 (Fin m)}
    (he : e ∈ τ) (hnc : ¬ CompatSet compat (Nb Fn e)) :
    e = s((triV h0 τ).2.1, (triV h0 τ).2.2) ∨
      (τ ∈ BT3 compat G ∧ e = keepE compat G h0 τ) := by
  classical
  obtain ⟨x, x', hx, hx', hxx', hnc', hb, heG, -⟩ :=
    yn_structure hcs hg1 hg2 hKP h0 x0 hFn0 hFn hnc
  have hτ' : CNX G x x' ∈ BT compat G := mem_BT.2 ⟨x, x', hb, rfl⟩
  have heq : CNX G x x' = τ := BT_disj hg2 hτ' hτ ⟨e, mem_inter.2 ⟨heG, he⟩⟩
  have he' : e ∈ CNX Fn x x' := by rw [mem_CNX]; exact ⟨(mem_Nb Fn).1 hx, (mem_Nb Fn).1 hx'⟩
  obtain ⟨-, -, hk, hbc⟩ := cn_Fn hcs hg1 hg2 hKP h0 x0 hFn0 hFn hxx' hnc' he'
  rw [heq] at hk hbc
  by_cases hE : s(x, x') ∈ E0s compat G x0
  · right
    refine ⟨?_, hk hE⟩
    obtain ⟨σ, hσ, w, hw, hq⟩ := (mem_E0s x0).1 hE
    obtain ⟨hcσ, -, -⟩ := E0_CNX hg1 hg2 hKP h0 x0 hσ hw
    have : σ = τ := by
      rw [← hcσ, ← heq]
      rcases Sym2.eq_iff.1 hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2, CNX_comm]
    rw [← this]; exact hσ
  · exact Or.inl (hbc hE)

/-- The "moreover" alternative for a triangle. -/
def Moreover (compat : X → X → Prop) (N : Sym2 (Fin m) → Finset X) (a b c : Fin m) : Prop :=
  (N s(a, b)).card ≤ 1 ∨ (N s(b, c)).card ≤ 1 ∨ (N s(a, c)).card ≤ 1 ∨
    (CompatSet compat (N s(a, b)) ∧ CompatSet compat (N s(b, c))) ∨
    (CompatSet compat (N s(a, b)) ∧ CompatSet compat (N s(a, c))) ∨
    (CompatSet compat (N s(b, c)) ∧ CompatSet compat (N s(a, c)))

lemma card_le_one_of_compat {A B : Finset X} (hA : CompatSet compat A)
    (hB : ¬ HasCompatPair compat B) (h : A ⊆ B) : A.card ≤ 1 := by
  rw [card_le_one]
  intro u hu v hv
  by_contra huv
  exact hB ⟨u, h hu, v, h hv, huv, hA u hu v hv huv⟩

open scoped Classical in
lemma keepE_eq (h0 : Fin m) (G : Finset (X × Sym2 (Fin m))) (τ : Finset (Sym2 (Fin m))) :
    keepE compat G h0 τ = if HasCompatPair compat (Nb G s((triV h0 τ).1, (triV h0 τ).2.1)) then
      s((triV h0 τ).1, (triV h0 τ).2.1) else s((triV h0 τ).1, (triV h0 τ).2.2) := by
  classical
  unfold keepE; congr 1

include hcs hg1 hg2 hKP hFn0 hFn in
lemma moreover_Fn {τ : Finset (Sym2 (Fin m))} (hτ : τ ∈ BT compat G)
    (hU : ¬ (τ ∈ BT3 compat G ∧
      HasCompatPair compat (Nb G s((triV h0 τ).1, (triV h0 τ).2.1)) ∧
      ¬ CompatSet compat (Nb Fn s((triV h0 τ).1, (triV h0 τ).2.1)))) :
    Moreover compat (Nb Fn) (triV h0 τ).1 (triV h0 τ).2.1 (triV h0 τ).2.2 := by
  classical
  obtain ⟨h1, h2, h3⟩ := triV_spec h0 (BT_tri hτ)
  set a := (triV h0 τ).1
  set b := (triV h0 τ).2.1
  set c := (triV h0 τ).2.2
  have hab : s(a, b) ∈ τ := by rw [h3]; simp [tri]
  have hac : s(a, c) ∈ τ := by rw [h3]; simp [tri]
  have n1 : s(a, b) ≠ s(b, c) := by intro h; rw [Sym2.eq_iff] at h; omega
  have n2 : s(a, c) ≠ s(b, c) := by intro h; rw [Sym2.eq_iff] at h; omega
  have n3 : s(a, b) ≠ s(a, c) := by intro h; rw [Sym2.eq_iff] at h; omega
  have hk := keepE_eq (compat := compat) h0 G τ
  have st := fun {e} (he : e ∈ τ) (hnc : ¬ CompatSet compat (Nb Fn e)) =>
    tri_status hcs hg1 hg2 hKP h0 x0 hFn0 hFn hτ he hnc
  unfold Moreover
  by_cases h3k : τ ∈ BT3 compat G
  · by_cases hcp : HasCompatPair compat (Nb G s(a, b))
    · rw [if_pos hcp] at hk
      have cac : CompatSet compat (Nb Fn s(a, c)) := by
        by_contra hn
        rcases st hac hn with h | ⟨-, h⟩
        · exact n2 h
        · exact n3 (hk ▸ h).symm
      have cab : CompatSet compat (Nb Fn s(a, b)) := by
        by_contra hn
        exact hU ⟨h3k, hcp, hn⟩
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨cab, cac⟩))))
    · rw [if_neg hcp] at hk
      have cab : CompatSet compat (Nb Fn s(a, b)) := by
        by_contra hn
        rcases st hab hn with h | ⟨-, h⟩
        · exact n1 h
        · exact n3 (hk ▸ h)
      left
      exact card_le_one_of_compat cab hcp (Nb_mono (hFn0.trans sdiff_subset) _)
  · have cab : CompatSet compat (Nb Fn s(a, b)) := by
      by_contra hn
      rcases st hab hn with h | ⟨h, -⟩
      · exact n1 h
      · exact h3k h
    have cac : CompatSet compat (Nb Fn s(a, c)) := by
      by_contra hn
      rcases st hac hn with h | ⟨h, -⟩
      · exact n2 h
      · exact h3k h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨cab, cac⟩))))

omit [Fintype X] [DecidableEq X] in
lemma triV_edges (h0 : Fin m) {τ : Finset (Sym2 (Fin m))} (h : IsTri τ) :
    s((triV h0 τ).1, (triV h0 τ).2.1) ∈ τ ∧ s((triV h0 τ).2.1, (triV h0 τ).2.2) ∈ τ ∧
      s((triV h0 τ).1, (triV h0 τ).2.2) ∈ τ := by
  obtain ⟨h1, h2, h3⟩ := triV_spec h0 h
  rcases hT : triV h0 τ with ⟨a, b, c⟩
  rw [hT] at h1 h2 h3
  simp only at h1 h2 h3 ⊢
  rw [h3]; simp [tri]

include hcs hg1 hg2 hKP hFn0 hFn in
/-- The final edge exchange. -/
theorem exchange : ∃ Fs ⊆ G, Fn.card ≤ Fs.card ∧
    (∀ e, CompatSet compat (Nb Fs e) ∨
      ∃ x x', Nb Fs e = {x, x'} ∧ BetaPair compat G x x' ∧ e ∈ CNX G x x') ∧
    (∀ τ ∈ BT compat G, Moreover compat (Nb Fs) (triV h0 τ).1 (triV h0 τ).2.1 (triV h0 τ).2.2) ∧
    (∀ e, (∀ τ ∈ BT compat G, e ∉ τ) → Nb Fs e = Nb Fn e) := by
  classical
  haveI : Nonempty X := ⟨x0⟩
  set abE : Finset (Sym2 (Fin m)) → Sym2 (Fin m) := fun τ => s((triV h0 τ).1, (triV h0 τ).2.1)
    with habE
  set Unres := (BT3 compat G).filter (fun τ => HasCompatPair compat (Nb G (abE τ)) ∧
    ¬ CompatSet compat (Nb Fn (abE τ))) with hUnres
  have hUBT : ∀ τ ∈ Unres, τ ∈ BT compat G := fun τ h => (mem_filter.1 (mem_filter.1 h).1).1
  have hab_mem : ∀ τ ∈ BT compat G, abE τ ∈ τ := by
    intro τ hτ
    exact (triV_edges h0 (BT_tri hτ)).1
  have hab_inj : ∀ τ ∈ Unres, ∀ τ' ∈ BT compat G, abE τ ∈ τ' → τ = τ' := fun τ h τ' h' hm =>
    BT_disj hg2 (hUBT τ h) h' ⟨abE τ, mem_inter.2 ⟨hab_mem τ (hUBT τ h), hm⟩⟩
  have hpair : ∀ τ ∈ Unres, ∃ uv : X × X, uv.1 ∈ Nb G (abE τ) ∧ uv.2 ∈ Nb G (abE τ) ∧
      uv.1 ≠ uv.2 ∧ compat uv.1 uv.2 := by
    intro τ h
    obtain ⟨u, hu, v, hv, huv, hc⟩ := (mem_filter.1 h).2.1
    exact ⟨(u, v), hu, hv, huv, hc⟩
  choose! UV hUV using hpair
  set U : Finset (Sym2 (Fin m)) → Finset X := fun τ => {(UV τ).1, (UV τ).2} with hUdef
  set Rem := Unres.biUnion (fun τ => Nb Fn (abE τ) ×ˢ {abE τ}) with hRem
  set Add := Unres.biUnion (fun τ => U τ ×ˢ {abE τ}) with hAdd
  set Fs := (Fn \ Rem) ∪ Add with hFs
  have hFnG : Fn ⊆ G := hFn0.trans sdiff_subset
  -- neighbourhoods in `Fs`
  have hNU : ∀ τ ∈ Unres, Nb Fs (abE τ) = U τ := by
    intro τ hτ
    ext z
    simp only [mem_Nb, hFs, mem_union, mem_sdiff, hRem, hAdd, mem_biUnion, mem_product,
      mem_singleton]
    constructor
    · rintro (⟨hz, hnot⟩ | ⟨τ', hτ', hz, he⟩)
      · exact absurd ⟨τ, hτ, hz, rfl⟩ hnot
      · have := hab_inj τ' hτ' τ (hUBT τ hτ) (he ▸ hab_mem τ (hUBT τ hτ))
        rw [this] at hz; exact hz
    · intro hz; exact Or.inr ⟨τ, hτ, hz, rfl⟩
  have hNoff : ∀ e, (∀ τ ∈ Unres, e ≠ abE τ) → Nb Fs e = Nb Fn e := by
    intro e he
    ext z
    simp only [mem_Nb, hFs, mem_union, mem_sdiff, hRem, hAdd, mem_biUnion, mem_product,
      mem_singleton]
    constructor
    · rintro (⟨hz, -⟩ | ⟨τ', hτ', -, he'⟩)
      · exact hz
      · exact absurd he' (he τ' hτ')
    · intro hz; exact Or.inl ⟨hz, fun ⟨τ', hτ', _, he'⟩ => he τ' hτ' he'⟩
  have hUc : ∀ τ ∈ Unres, CompatSet compat (U τ) := by
    intro τ hτ a ha b hb hab
    obtain ⟨-, -, hne, hc⟩ := hUV τ hτ
    simp only [hUdef, mem_insert, mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact hc
    · exact hcs _ _ hc
    · exact absurd rfl hab
  refine ⟨Fs, ?_, ?_, ?_, ?_, ?_⟩
  · apply union_subset (sdiff_subset.trans hFnG)
    rintro ⟨z, e⟩ hp
    obtain ⟨τ, hτ, hp⟩ := mem_biUnion.1 hp
    rw [mem_product, mem_singleton] at hp
    obtain ⟨hz, he⟩ := hp
    simp only at hz he
    subst he
    obtain ⟨h1, h2, -, -⟩ := hUV τ hτ
    simp only [hUdef, mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact (mem_Nb G).1 h1
    · exact (mem_Nb G).1 h2
  · -- the size does not drop
    have hdisj : Disjoint (Fn \ Rem) Add := by
      rw [disjoint_left]
      intro p hp hpA
      obtain ⟨τ, hτ, hpA⟩ := mem_biUnion.1 hpA
      rw [mem_product, mem_singleton] at hpA
      apply (mem_sdiff.1 hp).2
      refine mem_biUnion.2 ⟨τ, hτ, mem_product.2 ⟨?_, mem_singleton.2 hpA.2⟩⟩
      rw [mem_Nb, ← hpA.2]
      exact (mem_sdiff.1 hp).1
    have hcard : Fs.card = (Fn \ Rem).card + Add.card := card_union_of_disjoint hdisj
    have h1 : Fn.card ≤ (Fn \ Rem).card + Rem.card := by
      have := card_sdiff_add_card_inter Fn Rem
      have h2 := card_le_card (inter_subset_right (s₁ := Fn) (s₂ := Rem))
      omega
    have h2 : Rem.card ≤ ∑ _τ ∈ Unres, 2 := by
      calc Rem.card ≤ ∑ τ ∈ Unres, (Nb Fn (abE τ) ×ˢ {abE τ}).card := card_biUnion_le
        _ ≤ _ := by
            apply sum_le_sum
            intro τ hτ
            rw [card_product, card_singleton, mul_one]
            obtain ⟨x, x', hxx, hb, -⟩ :=
              yn_pair hcs hg1 hg2 hKP h0 x0 hFn0 hFn (mem_filter.1 hτ).2.2
            rw [hxx]; exact card_le_two
    have h3 : Add.card = ∑ _τ ∈ Unres, 2 := by
      rw [hAdd, card_biUnion]
      · apply sum_congr rfl
        intro τ hτ
        rw [card_product, card_singleton, mul_one, hUdef]
        exact card_pair (hUV τ hτ).2.2.1
      · intro τ hτ τ' hτ' hne
        rw [Function.onFun, disjoint_left]
        intro p hp hp'
        rw [mem_product, mem_singleton] at hp hp'
        apply hne
        exact hab_inj τ hτ τ' (hUBT τ' hτ') (hp.2 ▸ hp'.2 ▸ hab_mem τ' (hUBT τ' hτ'))
    omega
  · intro e
    by_cases he : ∃ τ ∈ Unres, e = abE τ
    · obtain ⟨τ, hτ, rfl⟩ := he
      left; rw [hNU τ hτ]; exact hUc τ hτ
    · push_neg at he
      rw [hNoff e he]
      by_cases hc : CompatSet compat (Nb Fn e)
      · exact Or.inl hc
      · exact Or.inr (yn_pair hcs hg1 hg2 hKP h0 x0 hFn0 hFn hc)
  · intro τ hτ
    obtain ⟨t1, t2, t3⟩ := triV_spec h0 (BT_tri hτ)
    have hedge : ∀ e ∈ τ, (∀ τ' ∈ Unres, e ≠ abE τ') ∨ τ ∈ Unres ∧ e = abE τ := by
      intro e he
      by_cases hex : ∃ τ' ∈ Unres, e = abE τ'
      · obtain ⟨τ', hτ', rfl⟩ := hex
        have := hab_inj τ' hτ' τ hτ he
        subst this
        exact Or.inr ⟨hτ', rfl⟩
      · push_neg at hex; exact Or.inl hex
    by_cases hU : τ ∈ Unres
    · -- after the exchange: `ab` and `ac` are compatible
      set a := (triV h0 τ).1
      set b := (triV h0 τ).2.1
      set c := (triV h0 τ).2.2
      have hac : s(a, c) ∈ τ := by rw [t3]; simp [tri]
      have n3 : s(a, b) ≠ s(a, c) := by intro h; rw [Sym2.eq_iff] at h; omega
      have n2 : s(a, c) ≠ s(b, c) := by intro h; rw [Sym2.eq_iff] at h; omega
      have hacoff : ∀ τ' ∈ Unres, s(a, c) ≠ abE τ' := by
        rcases hedge _ hac with h | ⟨-, h⟩
        · exact h
        · exact absurd h n3.symm
      have cab : CompatSet compat (Nb Fs s(a, b)) := by
        have := hNU τ hU; simp only [habE] at this; rw [this]; exact hUc τ hU
      have cac : CompatSet compat (Nb Fs s(a, c)) := by
        rw [hNoff _ hacoff]
        by_contra hn
        rcases tri_status hcs hg1 hg2 hKP h0 x0 hFn0 hFn hτ hac hn with h | ⟨-, h⟩
        · exact n2 h
        · have hk := keepE_eq (compat := compat) h0 G τ
          rw [if_pos (mem_filter.1 hU).2.1] at hk
          exact n3 (hk ▸ h).symm
      unfold Moreover
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨cab, cac⟩))))
    · have hall : ∀ e ∈ τ, Nb Fs e = Nb Fn e := by
        intro e he
        rcases hedge e he with h | ⟨h, -⟩
        · exact hNoff e h
        · exact absurd h hU
      have hmo := moreover_Fn hcs hg1 hg2 hKP h0 x0 hFn0 hFn hτ (by
        intro ⟨h1, h2, h3⟩
        exact hU (mem_filter.2 ⟨h1, h2, h3⟩))
      obtain ⟨e1, e2, e3⟩ := triV_edges h0 (BT_tri hτ)
      unfold Moreover at hmo ⊢
      rw [hall _ e1, hall _ e2, hall _ e3]
      exact hmo
  · intro e he
    exact hNoff e (fun τ' hτ' h => he τ' (hUBT τ' hτ') (h ▸ hab_mem τ' (hUBT τ' hτ')))

end DL5

/-! ## The deletion lemma -/

section Main

variable {compat : X → X → Prop}

lemma G3_mono {F F' : Finset (X × Sym2 (Fin m))} (h : F' ⊆ F) {q : Sym2 (Fin m)} {w : Fin m}
    (hw : G3 compat F q w) : G3 compat F' q w := by
  intro u v y hq h1 h2 h3 a ha b hb hab
  exact hw u v y hq h1 h2 h3 a (inter_subset_inter (Nb_mono h _) (Nb_mono h _) ha) b
    (inter_subset_inter (Nb_mono h _) (Nb_mono h _) hb) hab

lemma YDiag_mono {F F' : Finset (X × Sym2 (Fin m))} (h : F' ⊆ F) {u v : Fin m}
    (hd : YDiag F' u v) : YDiag F u v := by
  obtain ⟨y, hy⟩ := hd
  exact ⟨y, hy.trans (card_le_card (inter_subset_inter (Nb_mono h _) (Nb_mono h _)))⟩

lemma alphaO_mono {F F' : Finset (X × Sym2 (Fin m))} (h : F' ⊆ F) :
    alphaO compat F' ⊆ alphaO compat F := by
  classical
  intro p hp
  simp only [alphaO, mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.1, fun hs => hp.2.2 (star_mono' (CNX_mono h _ _) hs)⟩

lemma card_sym2_image_le {α : Type*} [Fintype α] [DecidableEq α] (P : α × α → Prop)
    [DecidablePred P] :
    (((univ : Finset α).offDiag.filter P).image (fun p => s(p.1, p.2))).card ≤
      (Fintype.card α).choose 2 := by
  calc _ ≤ ((univ : Finset α).offDiag.image (fun p => s(p.1, p.2))).card :=
        card_le_card (image_subset_image (filter_subset _ _))
    _ = (Fintype.card α).choose 2 := by
        rw [← card_univ]
        convert Sym2.card_image_offDiag (univ : Finset α) using 3
        rfl

/-- **The deletion lemma** (HMY Lemma 3.1 / `lem:3-graph-deletion`), with explicit constants. -/
theorem deletion_lemma (hcs : ∀ a b, compat a b → compat b a) {D : ℕ}
    (hD : ∀ x, (cnb compat x).card ≤ D) (F : Finset (X × Sym2 (Fin m)))
    (hnd : ∀ p ∈ F, ¬ p.2.IsDiag) (hg1 : Good1 compat F) (hg2 : Good2 compat F)
    (hg3 : ∀ u v, u ≠ v → YDiag F u v → ∃ w, G3 compat F s(u, v) w) (h0 : Fin m) (x0 : X) :
    ∃ Fs ⊆ F, F.card ≤ Fs.card + (Fintype.card X).choose 2 + m.choose 2 +
        9 * (Fintype.card X * (alphaO compat F).card) + 10 * (Fintype.card X * D * D) +
        m * (D * (alphaO compat F).card) ∧
      (∀ e, CompatSet compat (Nb Fs e) ∨
        ∃ x x', Nb Fs e = {x, x'} ∧ BetaPair compat F x x' ∧ e ∈ CNX F x x') ∧
      (∀ x x' a b c, BetaPair compat F x x' → a < b → b < c → CNX F x x' = tri a b c →
        Moreover compat (Nb Fs) a b c) := by
  classical
  set F1 := stage1 compat F
  set F2 := stage2 compat F1
  set G := stage3 compat F2 with hGdef
  have hGF : G ⊆ F := (stage3_sub _).trans ((stage2_sub _).trans (stage1_sub _))
  have hg1G : Good1 compat G := hg1.mono hGF
  have hg2G : Good2 compat G := hg2.mono hGF hg1
  have hKP : KerProp compat G := by
    intro σ hσ
    obtain ⟨p, q, hpq, rfl⟩ := mem_BT.1 hσ
    exact stage3_ker hcs hg1 hpq
  set F0 := G \ Del3 compat G h0 x0 with hF0
  set E0 := E0s compat G x0 with hE0def
  have hF0G : F0 ⊆ G := sdiff_subset
  have hnd0 : ∀ p ∈ F0, ¬ p.2.IsDiag := fun p hp => hnd p (hGF (hF0G hp))
  have hg10 : Good1 compat F0 := hg1G.mono hF0G
  have hg30 : ∀ u v, u ≠ v → YDiag F0 u v → ∃ w, G3 compat F0 s(u, v) w := by
    intro u v huv hd
    obtain ⟨w, hw⟩ := hg3 u v huv (YDiag_mono (hF0G.trans hGF) hd)
    exact ⟨w, G3_mono (hF0G.trans hGF) hw⟩
  have hE0 : ∀ x x', s(x, x') ∈ E0 → (CNX F0 x x').card ≤ 1 := by
    intro x x' hq
    obtain ⟨τ, hτ, w, hw, he⟩ := (mem_E0s x0).1 hq
    obtain ⟨-, hsub, -⟩ := E0_CNX hg1G hg2G hKP h0 x0 hτ hw
    have : CNX F0 x x' = CNX F0 w (xpp G x0 τ) := by
      rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact CNX_comm _ _ _
    rw [this]
    exact (card_le_card hsub).trans (by simp)
  have hE0sub : E0 ⊆ CXI compat F0 := by
    intro q hq
    obtain ⟨τ, hτ, w, hw, rfl⟩ := (mem_E0s x0).1 hq
    obtain ⟨-, -, hk⟩ := E0_CNX hg1G hg2G hKP h0 x0 hτ hw
    have hτBT := (mem_filter.1 hτ).1
    have hne := ker_nonempty_of_BT3 hτ
    exact (mem_CXI hcs).2 ⟨ne_of_mem_erase hw, (hKP _ hτBT).1 _ (mem_of_mem_erase hw) _
      (xpp_mem x0 hne) (ne_of_mem_erase hw), ⟨_, hk⟩⟩
  obtain ⟨Fn, hFnF0, hcost, hFnP⟩ := pass hcs F0 E0 h0 hnd0
    (fun x x' h1 h2 => hg10 x x' h1 h2) hg30 hE0 m le_rfl
  have hFn : ∀ x x', x ≠ x' → ¬ compat x x' → (CNX F0 x x').Nonempty →
      s(x, x') ∉ E0 → ∀ e ∈ CNX Fn x x', gS (CNX F0 x x') h0 ∉ e :=
    fun x x' h1 h2 h3 h4 => hFnP x x' h1 h2 h3 h4 (gS _ h0).isLt
  obtain ⟨Fs, hFsG, hFsc, hS, hM, hoff⟩ := exchange hcs hg1G hg2G hKP h0 x0 hFnF0 hFn
  refine ⟨Fs, hFsG.trans hGF, ?_, ?_, ?_⟩
  · -- the cost
    have c1 := stage1_cost (compat := compat) F
    have c2 := stage2_cost hcs hg1
    have c3 := stage3_cost hcs hD hg1
    have c4 := dl3_cost hg1G hg2G hKP h0 x0
    have hfil : (univ : Finset (Fin m)).filter (·.val < m) = univ := by
      ext j; simp [j.isLt]
    rw [hfil, sum_add_distrib, sum_add_distrib] at hcost
    have c6 := sum_TX hcs F0 E0 h0
    have c7 := sum_TY (compat := compat) F0 h0
    have c8 := T_sum hD F0
    have c9 : (CXI compat F0 \ E0).card + E0.card = (CXI compat F0).card := by
      rw [card_sdiff_of_subset hE0sub]; have := card_le_card hE0sub; omega
    have c10 : (CXI compat F0).card ≤ (CXI compat F2).card :=
      card_le_card ((CXI_mono hcs hF0G).trans (CXI_mono hcs (stage3_sub _)))
    have c11 : (CXI compat F1).card ≤ (Fintype.card X).choose 2 :=
      (card_le_card (CXI_mono hcs (stage1_sub F))).trans (card_sym2_image_le _)
    have c12 : (DYs F0).card ≤ m.choose 2 := by
      have := card_sym2_image_le (α := Fin m) (fun p => YDiag F0 p.1 p.2)
      simpa [DYs, Fintype.card_fin] using this
    have c13 : (alphaO compat F0).card ≤ (alphaO compat F).card :=
      card_le_card (alphaO_mono (hF0G.trans hGF))
    have c14 : m * (D * (alphaO compat F0).card) ≤ m * (D * (alphaO compat F).card) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ c13)
    have s1 : F.card + (CXI compat F2).card ≤ G.card + (CXI compat F1).card +
        9 * (Fintype.card X * (alphaO compat F).card) + 9 * (Fintype.card X * D * D) := by
      have a1 : F.card ≤ F1.card + 9 * (Fintype.card X * (alphaO compat F).card) := c1
      have a2 : F1.card + (CXI compat F2).card ≤ F2.card + (CXI compat F1).card := c2
      have a3 : F2.card ≤ G.card + 9 * (Fintype.card X * D * D) := c3
      omega
    have hc' : F0.card ≤ Fn.card + (∑ j : Fin m, (TX compat F0 E0 h0 j).card +
        ∑ j : Fin m, (TY compat F0 h0 j).card + ∑ j : Fin m, (Tset (Lk F0 j) compat).card) := hcost
    have s2 : F0.card ≤ Fn.card + (CXI compat F0 \ E0).card + (DYs F0).card +
        (Fintype.card X * D * D + m * (D * (alphaO compat F0).card)) := by
      calc F0.card ≤ _ := hc'
        _ ≤ Fn.card + ((CXI compat F0 \ E0).card + (DYs F0).card +
            (Fintype.card X * D * D + m * (D * (alphaO compat F0).card))) := by
          gcongr
        _ = _ := by ring
    have b4 : G.card ≤ F0.card + E0.card := c4
    have b9 : (CXI compat F0 \ E0).card + E0.card = (CXI compat F0).card := c9
    have b10 : (CXI compat F0).card ≤ (CXI compat F2).card := c10
    have b11 : (CXI compat F1).card ≤ (Fintype.card X).choose 2 := c11
    have b12 : (DYs F0).card ≤ m.choose 2 := c12
    have b14 : m * (D * (alphaO compat F0).card) ≤ m * (D * (alphaO compat F).card) := c14
    have b15 : Fn.card ≤ Fs.card := hFsc
    omega
  · intro e
    rcases hS e with h | ⟨x, x', hxx, hb, he⟩
    · exact Or.inl h
    · refine Or.inr ⟨x, x', hxx, hb.mono_of_sub hGF hg1, ?_⟩
      exact CNX_mono hGF x x' he
  · intro x x' a b c hb h1 h2 hτ
    by_cases hBT : tri a b c ∈ BT compat G
    · have hM' := hM _ hBT
      obtain ⟨t1, t2, t3⟩ := triV_spec h0 (BT_tri hBT)
      have hv := verts_of_tri t1 t2 h1 h2 t3.symm
      rw [hv.1, hv.2.1, hv.2.2] at hM'
      exact hM'
    · -- the three neighbourhoods are unchanged and compatible
      have hnot : ∀ e ∈ tri a b c, ∀ τ' ∈ BT compat G, e ∉ τ' := by
        intro e he τ' hτ' he'
        obtain ⟨p, q, hpq, rfl⟩ := mem_BT.1 hτ'
        have hF : CNX F p q = CNX G p q := hpq.of_sub hGF hg1
        have := hg2 x x' p q hb (hpq.mono_of_sub hGF hg1)
          ⟨e, mem_inter.2 ⟨hτ ▸ he, hF ▸ he'⟩⟩
        apply hBT
        rw [← hτ, this, hF]
        exact mem_BT.2 ⟨p, q, hpq, rfl⟩
      have hcomp : ∀ e ∈ tri a b c, CompatSet compat (Nb Fs e) := by
        intro e he
        rw [hoff e (hnot e he)]
        by_contra hn
        obtain ⟨y, y', -, -, -, -, hb', he', -⟩ :=
          yn_structure hcs hg1G hg2G hKP h0 x0 hFnF0 hFn hn
        exact hnot e he _ (mem_BT.2 ⟨y, y', hb', rfl⟩) he'
      unfold Moreover
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hcomp _ (by simp [tri]), hcomp _ (by simp [tri])⟩)))

end Main

end OMA_DL

/-!
# Erdős 643, CN-stability: the projection to a bipartite 3-graph (HMY §5.2)
-/

namespace OMA_H2

open Finset OMA_DL

variable {n : ℕ}

/-! ## Intersecting graphs are stars or triangles -/

lemma tri_perm_ab (a b c : Fin n) : tri a b c = tri b a c := by
  ext e; simp only [tri, mem_insert, mem_singleton]
  constructor <;> rintro (h | h | h) <;> simp_all [Sym2.eq_swap]

lemma tri_perm_bc (a b c : Fin n) : tri a b c = tri a c b := by
  ext e; simp only [tri, mem_insert, mem_singleton]
  constructor <;> rintro (h | h | h) <;> simp_all [Sym2.eq_swap]

lemma isTri_of_distinct {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    IsTri (tri a b c) := by
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hbc with h2 | h2 <;>
    rcases lt_or_gt_of_ne hac with h3 | h3
  · exact ⟨a, b, c, h1, h2, rfl⟩
  · exact absurd (h1.trans h2) (not_lt.2 h3.le)
  · exact ⟨a, c, b, h3, h2, tri_perm_bc a b c⟩
  · exact ⟨c, a, b, h3, h1, by rw [tri_perm_bc, tri_perm_ab, tri_perm_bc]⟩
  · exact ⟨b, a, c, h1, h3, tri_perm_ab a b c⟩
  · exact ⟨b, c, a, h2, h3, by rw [tri_perm_ab, tri_perm_bc]⟩
  · exact absurd (h2.trans h1) (not_lt.2 h3.le)
  · exact ⟨c, b, a, h2, h1, by rw [tri_perm_ab, tri_perm_bc, tri_perm_ab]⟩

lemma exists_other {e : Sym2 (Fin n)} {a : Fin n} (h : a ∈ e) : ∃ b, e = s(a, b) := by
  obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 h
  exact ⟨b, hb⟩

/-- An intersecting family of edges is a star or a triangle. -/
lemma star_or_tri (h0 : Fin n) (S : Finset (Sym2 (Fin n))) (hnd : ∀ e ∈ S, ¬ e.IsDiag)
    (hint : ∀ e ∈ S, ∀ e' ∈ S, ∃ z, z ∈ e ∧ z ∈ e') : IsStarE S ∨ IsTri S := by
  classical
  rcases S.eq_empty_or_nonempty with hS | ⟨e0, he0⟩
  · left; exact ⟨h0, by simp [hS]⟩
  obtain ⟨⟨a, b⟩, rfl⟩ := Quot.exists_rep e0
  change s(a, b) ∈ S at he0
  have hab : a ≠ b := fun h => hnd _ he0 (by simp [h])
  by_cases ha : ∀ e ∈ S, a ∈ e
  · exact Or.inl ⟨a, ha⟩
  by_cases hb : ∀ e ∈ S, b ∈ e
  · exact Or.inl ⟨b, hb⟩
  push_neg at ha hb
  obtain ⟨e1, he1, hae1⟩ := ha
  obtain ⟨e2, he2, hbe2⟩ := hb
  obtain ⟨z1, hz1, hz1'⟩ := hint e1 he1 _ he0
  have hz1b : z1 = b := by
    rw [Sym2.mem_iff] at hz1'
    rcases hz1' with rfl | rfl
    · exact absurd hz1 hae1
    · rfl
  subst hz1b
  obtain ⟨c, rfl⟩ := exists_other hz1
  obtain ⟨z2, hz2, hz2'⟩ := hint e2 he2 _ he0
  have hz2a : z2 = a := by
    rw [Sym2.mem_iff] at hz2'
    rcases hz2' with rfl | rfl
    · rfl
    · exact absurd hz2 hbe2
  subst hz2a
  obtain ⟨d, rfl⟩ := exists_other hz2
  have hca : c ≠ z2 := fun h => hae1 (by simp [h])
  have hcb : c ≠ z1 := fun h => hnd _ he1 (by simp [h])
  have hdb : d ≠ z1 := fun h => hbe2 (by simp [h])
  obtain ⟨z3, hz3, hz3'⟩ := hint _ he1 _ he2
  simp only [Sym2.mem_iff] at hz3 hz3' hae1 hbe2
  have hcd : c = d := by
    rcases hz3 with rfl | rfl <;> rcases hz3' with h | h
    · exact absurd h hab.symm
    · exact absurd h hdb.symm
    · exact absurd h hca
    · exact h
  subst hcd
  set a := z2
  set b := z1
  have hsub : S ⊆ tri a b c := by
    intro f hf
    obtain ⟨⟨p, q⟩, rfl⟩ := Quot.exists_rep f
    change s(p, q) ∈ S at hf
    obtain ⟨y0, hy0, hy0'⟩ := hint _ hf _ he0
    obtain ⟨y1, hy1, hy1'⟩ := hint _ hf _ he1
    obtain ⟨y2, hy2, hy2'⟩ := hint _ hf _ he2
    have hpq : p ≠ q := fun h => hnd _ hf (by simp [h])
    simp only [Sym2.mem_iff] at hy0 hy0' hy1 hy1' hy2 hy2'
    simp only [tri, mem_insert, mem_singleton, Sym2.eq_iff]
    rcases hy0' with rfl | rfl <;> rcases hy1' with rfl | rfl <;> rcases hy2' with rfl | rfl <;>
      rcases hy0 with h0 | h0 <;> rcases hy1 with h1 | h1 <;> rcases hy2 with h2 | h2 <;>
      subst_vars <;> first | omega | tauto
  have hsup : tri a b c ⊆ S := by
    intro f hf
    simp only [tri, mem_insert, mem_singleton] at hf
    rcases hf with rfl | rfl | rfl
    · exact he0
    · exact he1
    · exact he2
  right
  rw [Subset.antisymm hsub hsup]
  exact isTri_of_distinct hab hcb.symm hca.symm

/-! ## The projection -/

/-- The local-star hypothesis, in the form of the target statement. -/
def LocStar (t : ℕ) (G : Finset (Finset (Fin n))) : Prop :=
  ∀ x y : Fin n, x ≠ y → ∃ v : Fin n, ∀ S : Finset (Fin n), S.card = t - 1 → x ∉ S → y ∉ S →
    insert x S ∈ G → insert y S ∈ G → v ∈ S

/-- `A ∪ {u, v} ∈ G` with `u, v ∉ A`. -/
def PEdge (G : Finset (Finset (Fin n))) (A : Finset (Fin n)) (e : Sym2 (Fin n)) : Prop :=
  ∃ u v, e = s(u, v) ∧ u ≠ v ∧ u ∉ A ∧ v ∉ A ∧ insert u (insert v A) ∈ G

lemma PEdge_mk {G : Finset (Finset (Fin n))} {A : Finset (Fin n)} {u v : Fin n} :
    PEdge G A s(u, v) ↔ u ≠ v ∧ u ∉ A ∧ v ∉ A ∧ insert u (insert v A) ∈ G := by
  constructor
  · rintro ⟨u', v', he, h1, h2, h3, h4⟩
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨h1, h2, h3, h4⟩
    · exact ⟨h1.symm, h3, h2, by rw [insert_comm]; exact h4⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨u, v, rfl, h1, h2, h3, h4⟩

open scoped Classical in
/-- The bipartite 3-graph of a block: triples `A u v` with `A ∪ {u, v} ∈ G`. -/
noncomputable def proj (G : Finset (Finset (Fin n))) (B : Finset (Finset (Fin n))) :
    Finset (↥B × Sym2 (Fin n)) :=
  univ.filter (fun p => PEdge G p.1.1 p.2)

lemma mem_proj {G : Finset (Finset (Fin n))} {B : Finset (Finset (Fin n))} {A : ↥B}
    {e : Sym2 (Fin n)} : (A, e) ∈ proj G B ↔ PEdge G A.1 e := by
  classical
  simp [proj]

/-- Compatibility of block members: they intersect. -/
def cmp (B : Finset (Finset (Fin n))) (A A' : ↥B) : Prop := (A.1 ∩ A'.1).Nonempty

lemma cmp_symm (B : Finset (Finset (Fin n))) : ∀ A A' : ↥B, cmp B A A' → cmp B A' A := by
  intro A A' h; rw [cmp, inter_comm]; exact h

lemma ne_of_mem_not_mem {α : Type*} {X Y : Finset α} {a : α} (h1 : a ∈ X) (h2 : a ∉ Y) :
    X ≠ Y := fun h => h2 (h ▸ h1)

section Good

variable {t : ℕ} {G : Finset (Finset (Fin n))} {B : Finset (Finset (Fin n))}
  (ht : 4 ≤ t) (hB : ∀ A ∈ B, A.card = t - 2)
  (hR : ¬ G.HasRepeatedDisjointUnion) (hL : LocStar t G)

lemma proj_nd : ∀ p ∈ proj G B, ¬ p.2.IsDiag := by
  rintro ⟨A, e⟩ hp
  rw [mem_proj] at hp
  obtain ⟨u, v, rfl, huv, -⟩ := hp
  simpa using huv

include ht hB hR in
lemma proj_good1 (h0 : Fin n) : Good1 (cmp B) (proj G B) := by
  classical
  intro x x' hxx' hnc
  have hdisj : x.1 ∩ x'.1 = ∅ := by
    rw [← not_nonempty_iff_eq_empty]; exact hnc
  have hxne : x.1.Nonempty := by rw [← card_pos, hB _ x.2]; omega
  have hx'ne : x'.1.Nonempty := by rw [← card_pos, hB _ x'.2]; omega
  apply star_or_tri h0
  · intro e he
    rw [mem_CNX, mem_proj] at he
    obtain ⟨u, v, rfl, huv, -⟩ := he.1
    simpa using huv
  · intro e he e' he'
    rw [mem_CNX, mem_proj, mem_proj] at he he'
    obtain ⟨u, v, rfl, huv, hu, hv, hP⟩ := he.1
    obtain ⟨-, hu', hv', hQ'⟩ := PEdge_mk.1 he.2
    obtain ⟨w, z, rfl, hwz, hw, hz, hC⟩ := he'.1
    obtain ⟨-, hw', hz', hQ⟩ := PEdge_mk.1 he'.2
    by_contra hno
    push_neg at hno
    simp only [Sym2.mem_iff] at hno
    have nuw : u ≠ w := fun h => hno u (Or.inl rfl) (Or.inl h)
    have nuz : u ≠ z := fun h => hno u (Or.inl rfl) (Or.inr h)
    have nvw : v ≠ w := fun h => hno v (Or.inr rfl) (Or.inl h)
    have nvz : v ≠ z := fun h => hno v (Or.inr rfl) (Or.inr h)
    have hxx : x.1 ≠ x'.1 := by
      intro h; obtain ⟨a, ha⟩ := hxne
      have : a ∈ x.1 ∩ x'.1 := mem_inter.2 ⟨ha, h ▸ ha⟩
      rw [hdisj] at this; exact absurd this (notMem_empty _)
    have hdis : ∀ a, a ∈ x.1 → a ∉ x'.1 := by
      intro a ha ha'
      have : a ∈ x.1 ∩ x'.1 := mem_inter.2 ⟨ha, ha'⟩
      rw [hdisj] at this; exact absurd this (notMem_empty _)
    apply hR
    refine ⟨insert u (insert v x.1), hP, insert w (insert z x'.1), hQ,
      insert w (insert z x.1), hC, insert u (insert v x'.1), hQ', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [disjoint_left]; intro a ha hb
      simp only [mem_insert] at ha hb
      rcases ha with rfl | rfl | ha <;> rcases hb with h | h | hb <;> simp_all
    · rw [disjoint_left]; intro a ha hb
      simp only [mem_insert] at ha hb
      rcases ha with rfl | rfl | ha <;> rcases hb with h | h | hb <;> simp_all
    · ext a; simp only [mem_union, mem_insert]; tauto
    · exact ne_of_mem_not_mem (mem_insert_self u _) (by simp [nuw, nuz, hu'])
    · exact ne_of_mem_not_mem (mem_insert_self w _) (by simp [nuw.symm, nvw.symm, hw'])
    · exact ne_of_mem_not_mem (mem_insert_self u _) (by simp [nuw, nuz, hu])
    · obtain ⟨a, ha⟩ := hxne
      refine ne_of_mem_not_mem (a := a) (by simp [ha]) ?_
      simp only [mem_insert, not_or]
      exact ⟨fun h => hu (h ▸ ha), fun h => hv (h ▸ ha), hdis a ha⟩
    · obtain ⟨a, ha⟩ := hx'ne
      refine ne_of_mem_not_mem (a := a) (by simp [ha]) ?_
      simp only [mem_insert, not_or]
      exact ⟨fun h => hw' (h ▸ ha), fun h => hz' (h ▸ ha), fun h => hdis a h ha⟩
    · exact ne_of_mem_not_mem (mem_insert_self w _) (by simp [nuw.symm, nvw.symm, hw'])

lemma tri_edge {T : Finset (Sym2 (Fin n))} (hT : IsTri T) {e : Sym2 (Fin n)} (he : e ∈ T) :
    ∃ p q r, p ≠ q ∧ q ≠ r ∧ p ≠ r ∧ e = s(p, q) ∧ T = tri p q r := by
  obtain ⟨a, b, c, h1, h2, rfl⟩ := hT
  simp only [mem_tri] at he
  rcases he with rfl | rfl | rfl
  · exact ⟨a, b, c, h1.ne, h2.ne, (h1.trans h2).ne, rfl, rfl⟩
  · refine ⟨b, c, a, h2.ne, (h1.trans h2).ne', h1.ne', rfl, ?_⟩
    rw [tri_perm_bc, tri_perm_ab, tri_perm_bc, tri_perm_ab]
  · exact ⟨a, c, b, (h1.trans h2).ne, h2.ne', h1.ne, rfl, tri_perm_bc a b c⟩

include ht hB in
/-- The third vertex of a `β`-triangle through `pq` is every centre of `CN(p, q)`. -/
lemma center_eq_third {x x' : ↥B} (hnc : ¬ cmp B x x') {p q r : Fin n} (hpq : p ≠ q)
    (hqr : q ≠ r) (hpr : p ≠ r) (hT : CNX (proj G B) x x' = tri p q r) {v : Fin n}
    (hv : ∀ S : Finset (Fin n), S.card = t - 1 → p ∉ S → q ∉ S → insert p S ∈ G →
      insert q S ∈ G → v ∈ S) : v = r := by
  classical
  have hm : ∀ e ∈ tri p q r, (x, e) ∈ proj G B ∧ (x', e) ∈ proj G B := by
    intro e he; rw [← hT, mem_CNX] at he; exact he
  have key : ∀ y : ↥B, (y, s(p, r)) ∈ proj G B → (y, s(q, r)) ∈ proj G B → v ∈ insert r y.1 := by
    intro y h1 h2
    rw [mem_proj, PEdge_mk] at h1 h2
    obtain ⟨-, hp, hr, h1⟩ := h1
    obtain ⟨-, hq, -, h2⟩ := h2
    apply hv
    · rw [card_insert_of_notMem hr, hB _ y.2]; omega
    · simp [hpr, hp]
    · simp [hqr, hq]
    · exact h1
    · exact h2
  have e1 : s(p, r) ∈ tri p q r := by simp [tri]
  have e2 : s(q, r) ∈ tri p q r := by simp [tri]
  have k1 := key x (hm _ e1).1 (hm _ e2).1
  have k2 := key x' (hm _ e1).2 (hm _ e2).2
  rw [mem_insert] at k1 k2
  rcases k1 with h | h
  · exact h
  rcases k2 with h' | h'
  · exact h'
  exact absurd ⟨v, mem_inter.2 ⟨h, h'⟩⟩ hnc

include ht hB hL in
lemma proj_good2 : Good2 (cmp B) (proj G B) := by
  intro x₁ x₁' x₂ x₂' h1 h2 hne
  obtain ⟨e, he⟩ := hne
  rw [mem_inter] at he
  obtain ⟨p, q, r, hpq, hqr, hpr, rfl, hT1⟩ := tri_edge h1.2.2 he.1
  obtain ⟨p', q', r', hpq', hqr', hpr', he', hT2⟩ := tri_edge h2.2.2 he.2
  obtain ⟨v, hv⟩ := hL p q hpq
  have hr := center_eq_third ht hB h1.2.1 hpq hqr hpr hT1 hv
  rcases Sym2.eq_iff.1 he' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hr' := center_eq_third ht hB h2.2.1 hpq hqr' hpr' hT2 hv
    rw [hT1, hT2, ← hr, ← hr']
  · have hv' : ∀ S : Finset (Fin n), S.card = t - 1 → q ∉ S → p ∉ S → insert q S ∈ G →
        insert p S ∈ G → v ∈ S := fun S h1 h2 h3 h4 h5 => hv S h1 h3 h2 h5 h4
    have hr' := center_eq_third ht hB h2.2.1 hpq' hqr' hpr' hT2 hv'
    rw [hT1, hT2, ← hr, ← hr', tri_perm_ab]

include ht hB hL in
lemma proj_G3 {u v : Fin n} (huv : u ≠ v) : ∃ w, G3 (cmp B) (proj G B) s(u, v) w := by
  obtain ⟨w, hw⟩ := hL u v huv
  refine ⟨w, ?_⟩
  intro u' v' y he hyu hyv hyw A hA A' hA' hAA'
  rw [mem_inter, mem_Nb, mem_Nb, mem_proj, mem_proj, PEdge_mk, PEdge_mk] at hA hA'
  obtain ⟨⟨-, hu1, hy1, hA1⟩, ⟨-, hv1, -, hA2⟩⟩ := hA
  obtain ⟨⟨-, hu2, hy2, hA3⟩, ⟨-, hv2, -, hA4⟩⟩ := hA'
  have mem : ∀ X : ↥B, u' ∉ X.1 → v' ∉ X.1 → y ∉ X.1 → insert u' (insert y X.1) ∈ G →
      insert v' (insert y X.1) ∈ G → w ∈ X.1 := by
    intro X h1 h2 h3 h4 h5
    have hcard : (insert y X.1).card = t - 1 := by
      rw [card_insert_of_notMem h3, hB _ X.2]; omega
    have hu' : u' ∉ insert y X.1 := by simp [Ne.symm hyu, h1]
    have hv' : v' ∉ insert y X.1 := by simp [Ne.symm hyv, h2]
    have : w ∈ insert y X.1 := by
      rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hw _ hcard hu' hv' h4 h5
      · exact hw _ hcard hv' hu' h5 h4
    rw [mem_insert] at this
    rcases this with h | h
    · exact absurd h.symm hyw
    · exact h
  exact ⟨w, mem_inter.2 ⟨mem A hu1 hv1 hy1 hA1 hA2, mem A' hu2 hv2 hy2 hA3 hA4⟩⟩

end Good

/-! ## The cluster lemma: block basics and forbidden rainbow configurations -/

/-- `c` is a centre of the common link of `v` and `v'`. -/
def Ctr (t : ℕ) (G : Finset (Finset (Fin n))) (v v' c : Fin n) : Prop :=
  ∀ S : Finset (Fin n), S.card = t - 1 → v ∉ S → v' ∉ S → insert v S ∈ G → insert v' S ∈ G → c ∈ S

section Cluster

variable {t : ℕ} {G : Finset (Finset (Fin n))} {B : Finset (Finset (Fin n))}
  (ht : 4 ≤ t) (hB : ∀ A ∈ B, A.card = t - 2)
  (col : ↥B → Fin (t - 2)) (hcol : ∀ A A' : ↥B, col A = col A' → A = A' ∨ Disjoint A.1 A'.1)
  {Fs : Finset (↥B × Sym2 (Fin n))} (hFs : ∀ p ∈ Fs, PEdge G p.1.1 p.2)

include hcol in
/-- A compatible family in a block has at most `t - 2` members. -/
lemma compat_card_le {S : Finset ↥B} (hS : CompatSet (cmp B) S) : S.card ≤ t - 2 := by
  classical
  calc S.card ≤ (univ : Finset (Fin (t - 2))).card := by
        apply card_le_card_of_injOn col (fun _ _ => mem_coe.2 (mem_univ _))
        intro A hA A' hA' h
        rcases hcol A A' h with h' | h'
        · exact h'
        · by_contra hne
          have := hS A hA A' hA' hne
          exact absurd (disjoint_iff_inter_eq_empty.1 h') (nonempty_iff_ne_empty.1 this)
    _ = t - 2 := by simp

include hcol in
/-- Members of a block through a common vertex: at most `t - 2`. -/
lemma vertex_deg_le {S : Finset ↥B} {z : Fin n} (hz : ∀ T ∈ S, z ∈ T.1) : S.card ≤ t - 2 :=
  compat_card_le col hcol (fun A hA A' hA' _ => ⟨z, mem_inter.2 ⟨hz A hA, hz A' hA'⟩⟩)

include hcol in
/-- Two distinct `(t-2)`-families cannot share a common vertex in all their members. -/
lemma two_families {S₁ S₂ : Finset ↥B} (h1 : S₁.card = t - 2) (h2 : S₂.card = t - 2)
    (hne : S₁ ≠ S₂) {c : Fin n} (hc1 : ∀ T ∈ S₁, c ∈ T.1) (hc2 : ∀ T ∈ S₂, c ∈ T.1) : False := by
  classical
  have hle := vertex_deg_le col hcol (S := S₁ ∪ S₂) (z := c) (by
    intro T hT; rcases mem_union.1 hT with h | h
    · exact hc1 T h
    · exact hc2 T h)
  have hsub : S₁ ⊆ S₁ ∪ S₂ := subset_union_left
  have heq : S₁ = S₁ ∪ S₂ := eq_of_subset_of_card_le hsub (by omega)
  have h21 : S₂ ⊆ S₁ := heq ▸ subset_union_right
  exact hne (eq_of_subset_of_card_le h21 (by omega)).symm

include ht hB hFs in
/-- The common link of `v`, `v'` contains `T ∪ {w}`. -/
lemma ctr_mem {v v' w c : Fin n} (hc : Ctr t G v v' c) (hvv' : v ≠ v') {T : ↥B}
    (h1 : (T, s(v, w)) ∈ Fs) (h2 : (T, s(v', w)) ∈ Fs) : c ∈ insert w T.1 := by
  obtain ⟨hvw, hv, hw, hG1⟩ := PEdge_mk.1 (hFs _ h1)
  obtain ⟨hv'w, hv', -, hG2⟩ := PEdge_mk.1 (hFs _ h2)
  apply hc
  · rw [card_insert_of_notMem hw, hB _ T.2]; omega
  · simp [hvw, hv]
  · simp [hv'w, hv']
  · exact hG1
  · exact hG2

include ht hB hFs in
lemma ctr_family {v v' w c : Fin n} (hc : Ctr t G v v' c) (hvv' : v ≠ v') {S : Finset ↥B}
    (hS : ∀ T ∈ S, (T, s(v, w)) ∈ Fs ∧ (T, s(v', w)) ∈ Fs) : c = w ∨ ∀ T ∈ S, c ∈ T.1 := by
  by_cases hcw : c = w
  · exact Or.inl hcw
  · right
    intro T hT
    have := ctr_mem ht hB hFs hc hvv' (hS T hT).1 (hS T hT).2
    rw [mem_insert] at this
    exact this.resolve_left hcw

include ht hB hcol hFs in
/-- No rainbow `K_{2,3}`. -/
lemma rainbow3 {v₁ v₂ c : Fin n} (hc : Ctr t G v₁ v₂ c) (hv : v₁ ≠ v₂) {w₁ w₂ w₃ : Fin n}
    (h12 : w₁ ≠ w₂) (h13 : w₁ ≠ w₃) (h23 : w₂ ≠ w₃) {S₁ S₂ S₃ : Finset ↥B}
    (c1 : S₁.card = t - 2) (c2 : S₂.card = t - 2) (c3 : S₃.card = t - 2)
    (n12 : S₁ ≠ S₂) (n13 : S₁ ≠ S₃) (n23 : S₂ ≠ S₃)
    (e1 : ∀ T ∈ S₁, (T, s(v₁, w₁)) ∈ Fs ∧ (T, s(v₂, w₁)) ∈ Fs)
    (e2 : ∀ T ∈ S₂, (T, s(v₁, w₂)) ∈ Fs ∧ (T, s(v₂, w₂)) ∈ Fs)
    (e3 : ∀ T ∈ S₃, (T, s(v₁, w₃)) ∈ Fs ∧ (T, s(v₂, w₃)) ∈ Fs) : False := by
  rcases ctr_family ht hB hFs hc hv e1 with h1 | h1 <;>
  rcases ctr_family ht hB hFs hc hv e2 with h2 | h2 <;>
  rcases ctr_family ht hB hFs hc hv e3 with h3 | h3
  · exact h12 (h1.symm.trans h2)
  · exact h12 (h1.symm.trans h2)
  · exact h13 (h1.symm.trans h3)
  · exact two_families col hcol c2 c3 n23 h2 h3
  · exact h23 (h2.symm.trans h3)
  · exact two_families col hcol c1 c3 n13 h1 h3
  · exact two_families col hcol c1 c2 n12 h1 h2
  · exact two_families col hcol c1 c2 n12 h1 h2

include ht hB hcol hFs in
/-- No rainbow `C_4` whose right vertices avoid the other family's intersection. -/
lemma rainbow2 {v₁ v₂ c : Fin n} (hc : Ctr t G v₁ v₂ c) (hv : v₁ ≠ v₂) {w₁ w₂ : Fin n}
    (h12 : w₁ ≠ w₂) {S₁ S₂ : Finset ↥B} (c1 : S₁.card = t - 2) (c2 : S₂.card = t - 2)
    (n12 : S₁ ≠ S₂) (o1 : ¬ ∀ T ∈ S₂, w₁ ∈ T.1) (o2 : ¬ ∀ T ∈ S₁, w₂ ∈ T.1)
    (e1 : ∀ T ∈ S₁, (T, s(v₁, w₁)) ∈ Fs ∧ (T, s(v₂, w₁)) ∈ Fs)
    (e2 : ∀ T ∈ S₂, (T, s(v₁, w₂)) ∈ Fs ∧ (T, s(v₂, w₂)) ∈ Fs) : False := by
  rcases ctr_family ht hB hFs hc hv e1 with h1 | h1 <;>
  rcases ctr_family ht hB hFs hc hv e2 with h2 | h2
  · exact h12 (h1.symm.trans h2)
  · exact o1 (h1 ▸ h2)
  · exact o2 (h2 ▸ h1)
  · exact two_families col hcol c1 c2 n12 h1 h2

include ht hB hcol hFs in
/-- **Monochromatic `K_{2,t}`.** All but `|Fam|²` common neighbours see one colour. -/
lemma mono_K2t (hL : LocStar t G) {v v' : Fin n} (hvv' : v ≠ v') (W0 : Finset (Fin n))
    (hvW : v ∉ W0) (hv'W : v' ∉ W0) (Fam : Finset (Finset ↥B))
    (hFam : ∀ S ∈ Fam, S.card = t - 2)
    (hcolr : ∀ w ∈ W0, Nb Fs s(v, w) ∈ Fam ∧ Nb Fs s(v', w) ∈ Fam)
    (hout : ∀ S ∈ Fam, ∀ z, (z = v ∨ z = v' ∨ z ∈ W0) → ¬ ∀ T ∈ S, z ∈ T.1) :
    ∃ S, W0.card ≤ (W0.filter (fun w => Nb Fs s(v, w) = S ∧ Nb Fs s(v', w) = S)).card +
      Fam.card * Fam.card := by
  classical
  set Woff := W0.filter (fun w => Nb Fs s(v, w) ≠ Nb Fs s(v', w))
  set Wd := W0.filter (fun w => Nb Fs s(v, w) = Nb Fs s(v', w))
  have hsplit : W0.card = Woff.card + Wd.card := by
    rw [add_comm]; exact (card_filter_add_card_filter_not _).symm
  -- edges of a colour class
  have hedge : ∀ w ∈ W0, ∀ T ∈ Nb Fs s(v, w), (T, s(w, v)) ∈ Fs := by
    intro w _ T hT; rw [Sym2.eq_swap]; exact (mem_Nb Fs).1 hT
  have hedge' : ∀ w ∈ W0, ∀ T ∈ Nb Fs s(v', w), (T, s(w, v')) ∈ Fs := by
    intro w _ T hT; rw [Sym2.eq_swap]; exact (mem_Nb Fs).1 hT
  have hoff : Woff.card ≤ Fam.card * Fam.card := by
    rw [← card_product]
    apply card_le_card_of_injOn (fun w => (Nb Fs s(v, w), Nb Fs s(v', w)))
    · intro w hw
      have hw' := (mem_filter.1 hw).1
      exact mem_coe.2 (mem_product.2 (hcolr w hw'))
    · intro a ha b hb hab
      by_contra hne
      simp only [Prod.mk.injEq] at hab
      have ha' := mem_filter.1 ha
      have hb' := mem_filter.1 hb
      obtain ⟨c, hc⟩ := hL a b hne
      exact rainbow2 ht hB col hcol hFs hc hne hvv' (hFam _ (hcolr a ha'.1).1)
        (hFam _ (hcolr a ha'.1).2) ha'.2
        (hout _ (hcolr a ha'.1).2 v (Or.inl rfl)) (hout _ (hcolr a ha'.1).1 v' (Or.inr (Or.inl rfl)))
        (fun T hT => ⟨hedge a ha'.1 T hT, hedge b hb'.1 T (by rw [← hab.1]; exact hT)⟩)
        (fun T hT => ⟨hedge' a ha'.1 T hT, hedge' b hb'.1 T (by rw [← hab.2]; exact hT)⟩)
  rcases Wd.eq_empty_or_nonempty with he | ⟨w0, hw0⟩
  · refine ⟨∅, ?_⟩
    rw [hsplit, he, card_empty]; omega
  · refine ⟨Nb Fs s(v, w0), ?_⟩
    have hw0' := mem_filter.1 hw0
    have hsub : Wd ⊆ W0.filter (fun w => Nb Fs s(v, w) = Nb Fs s(v, w0) ∧
        Nb Fs s(v', w) = Nb Fs s(v, w0)) := by
      intro w hw
      have hw' := mem_filter.1 hw
      by_cases heq : Nb Fs s(v, w) = Nb Fs s(v, w0)
      · exact mem_filter.2 ⟨hw'.1, heq, hw'.2 ▸ heq⟩
      · exfalso
        have hww0 : w ≠ w0 := fun h => heq (by rw [h])
        obtain ⟨c, hc⟩ := hL v v' hvv'
        exact rainbow2 ht hB col hcol hFs hc hvv' hww0 (hFam _ (hcolr w hw'.1).1)
          (hFam _ (hcolr w0 hw0'.1).1) heq
          (hout _ (hcolr w0 hw0'.1).1 w (Or.inr (Or.inr hw'.1)))
          (hout _ (hcolr w hw'.1).1 w0 (Or.inr (Or.inr hw0'.1)))
          (fun T hT => ⟨(mem_Nb Fs).1 hT, (mem_Nb Fs).1 (hw'.2 ▸ hT)⟩)
          (fun T hT => ⟨(mem_Nb Fs).1 hT, (mem_Nb Fs).1 (hw0'.2 ▸ hT)⟩)
    have := card_le_card hsub
    omega

include ht hB hFs in
/-- The translation back to `G`: every centre of `CN(w, w')` lies in every member of `S`. -/
lemma ctr_in_family {v v' w w' c : Fin n} (hc : Ctr t G w w' c) (hww' : w ≠ w') (hvv' : v ≠ v')
    {S : Finset ↥B}
    (hS : ∀ T ∈ S, (T, s(v, w)) ∈ Fs ∧ (T, s(v', w)) ∈ Fs ∧ (T, s(v, w')) ∈ Fs ∧
      (T, s(v', w')) ∈ Fs) : ∀ T ∈ S, c ∈ T.1 := by
  intro T hT
  obtain ⟨h1, h2, h3, h4⟩ := hS T hT
  have m1 := ctr_mem ht hB hFs hc hww' (by rw [Sym2.eq_swap]; exact h1)
    (by rw [Sym2.eq_swap]; exact h3)
  have m2 := ctr_mem ht hB hFs hc hww' (by rw [Sym2.eq_swap]; exact h2)
    (by rw [Sym2.eq_swap]; exact h4)
  rw [mem_insert] at m1 m2
  rcases m1 with rfl | m1
  · rcases m2 with h | m2
    · exact absurd h hvv'
    · exact m2
  · exact m1

include hcol in
/-- Compatibility degree in a block is at most `(t-2)²`. -/
lemma cnb_card_le (A : ↥B) (hA : A.1.card = t - 2) :
    (cnb (cmp B) A).card ≤ (t - 2) * (t - 2) := by
  classical
  calc (cnb (cmp B) A).card ≤ (A.1.attach.biUnion (fun z =>
        (univ : Finset ↥B).filter (fun A' => z.1 ∈ A'.1))).card := by
        apply card_le_card
        intro A' hA'
        simp only [cnb, mem_filter, mem_univ, true_and] at hA'
        obtain ⟨z, hz⟩ := hA'.2
        rw [mem_inter] at hz
        exact mem_biUnion.2 ⟨⟨z, hz.1⟩, mem_attach _ _, mem_filter.2 ⟨mem_univ _, hz.2⟩⟩
    _ ≤ ∑ z ∈ A.1.attach, ((univ : Finset ↥B).filter (fun A' => z.1 ∈ A'.1)).card :=
        card_biUnion_le
    _ ≤ ∑ _z ∈ A.1.attach, (t - 2) := by
        apply sum_le_sum
        intro z _
        exact vertex_deg_le col hcol (fun T hT => (mem_filter.1 hT).2)
    _ = (t - 2) * (t - 2) := by rw [sum_const, card_attach, hA, smul_eq_mul]

include ht hcol in
/-- Every `Y`-pair neighbourhood has at most `t - 2` members. -/
lemma Nb_card_le (hS : ∀ e, CompatSet (cmp B) (Nb Fs e) ∨ (Nb Fs e).card ≤ 2) (e : Sym2 (Fin n)) :
    (Nb Fs e).card ≤ t - 2 := by
  rcases hS e with h | h
  · exact compat_card_le col hcol h
  · omega

lemma card_nondiag : ((univ : Finset (Sym2 (Fin n))).filter (fun e => ¬ e.IsDiag)).card =
    n.choose 2 := by
  classical
  rw [← Fintype.card_subtype, Sym2.card_subtype_not_diag, Fintype.card_fin]

/-- `|Fs| + #(non-maximum pairs) ≤ (t-2) C(n,2)`. -/
lemma notmax_card (hnd : ∀ p ∈ Fs, ¬ p.2.IsDiag) (hle : ∀ e, (Nb Fs e).card ≤ t - 2) :
    Fs.card + ((univ : Finset (Sym2 (Fin n))).filter (fun e => ¬ e.IsDiag ∧
      (Nb Fs e).card < t - 2)).card ≤ (t - 2) * n.choose 2 := by
  classical
  have hsum : Fs.card = ∑ e : Sym2 (Fin n), (Nb Fs e).card := by
    rw [card_eq_sum_card_fiberwise (f := Prod.snd) (t := univ) (fun _ _ => mem_univ _)]
    apply sum_congr rfl
    intro e _
    rw [Nb]
    apply card_bij (fun p _ => p.1)
    · intro p hp; simp only [mem_filter] at hp ⊢; rw [← hp.2]; exact ⟨mem_univ _, hp.1⟩
    · intro p hp p' hp' h
      simp only [mem_filter] at hp hp'
      exact Prod.ext h (hp.2.trans hp'.2.symm)
    · intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      exact ⟨(x, e), mem_filter.2 ⟨hx, rfl⟩, rfl⟩
  have hdiag : ∀ e : Sym2 (Fin n), e.IsDiag → (Nb Fs e).card = 0 := by
    intro e he
    rw [card_eq_zero, eq_empty_iff_forall_notMem]
    intro x hx
    exact hnd _ ((mem_Nb Fs).1 hx) he
  rw [hsum, card_filter]
  have hpt : ∀ e : Sym2 (Fin n), (Nb Fs e).card +
      (if ¬ e.IsDiag ∧ (Nb Fs e).card < t - 2 then 1 else 0) ≤
      (t - 2) * (if ¬ e.IsDiag then 1 else 0) := by
    intro e
    by_cases hd : e.IsDiag
    · simp [hd, hdiag e hd]
    · have := hle e
      split_ifs with h <;> simp_all <;> omega
  calc ∑ e : Sym2 (Fin n), (Nb Fs e).card +
        ∑ e : Sym2 (Fin n), (if ¬ e.IsDiag ∧ (Nb Fs e).card < t - 2 then 1 else 0)
      = ∑ e : Sym2 (Fin n), ((Nb Fs e).card +
          (if ¬ e.IsDiag ∧ (Nb Fs e).card < t - 2 then 1 else 0)) := by rw [sum_add_distrib]
    _ ≤ ∑ e : Sym2 (Fin n), (t - 2) * (if ¬ e.IsDiag then 1 else 0) := sum_le_sum (fun e _ => hpt e)
    _ = (t - 2) * n.choose 2 := by
        rw [← mul_sum, ← card_filter, card_nondiag]

include hB hcol in
/-- A block has at most `n` members. -/
lemma block_card_le : (univ : Finset ↥B).card * (t - 2) ≤ n * (t - 2) := by
  classical
  have h1 : ∑ A : ↥B, A.1.card = (univ : Finset ↥B).card * (t - 2) := by
    rw [sum_congr rfl (fun A _ => hB A.1 A.2), sum_const, smul_eq_mul]
  have h2 : ∑ A : ↥B, A.1.card = ∑ z : Fin n, ((univ : Finset ↥B).filter (fun A => z ∈ A.1)).card := by
    simp_rw [card_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro A _
    rw [← card_filter]
    simp
  rw [← h1, h2]
  calc _ ≤ ∑ _z : Fin n, (t - 2) := sum_le_sum (fun z _ =>
        vertex_deg_le col hcol (fun T hT => (mem_filter.1 hT).2))
    _ = n * (t - 2) := by simp

open scoped Classical in
/-- Compatible `(t-2)`-families of a block. -/
noncomputable def FamC (B : Finset (Finset (Fin n))) (t : ℕ) : Finset (Finset ↥B) :=
  univ.filter (fun S => S.card = t - 2 ∧ CompatSet (cmp B) S)

include ht hB hcol in
lemma famC_sub_powerset {S : Finset ↥B} (hS : S ∈ FamC B t) {A : ↥B} (hA : A ∈ S) :
    S ⊆ insert A (cnb (cmp B) A) := by
  classical
  intro A' hA'
  by_cases h : A' = A
  · rw [h]; exact mem_insert_self _ _
  · simp only [FamC, mem_filter, mem_univ, true_and] at hS
    exact mem_insert_of_mem (by simp [cnb, h, hS.2 A hA A' hA' (Ne.symm h)])

open scoped Classical in
/-- The colour class of a family: the pairs whose neighbourhood is exactly that family. -/
noncomputable def cls (Fs : Finset (↥B × Sym2 (Fin n))) (S : Finset ↥B) : Finset (Sym2 (Fin n)) :=
  univ.filter (fun e => Nb Fs e = S)

open scoped Classical in
noncomputable def J1 (Fs : Finset (↥B × Sym2 (Fin n))) (t : ℕ) : Finset (Finset ↥B) :=
  (FamC B t).filter (fun S => IsStarE (cls Fs S))

open scoped Classical in
noncomputable def ctrS (Fs : Finset (↥B × Sym2 (Fin n))) (h0 : Fin n) (S : Finset ↥B) : Fin n :=
  if h : IsStarE (cls Fs S) then h.choose else h0

open scoped Classical in
/-- Leaves of a star colour class. -/
noncomputable def leaves (Fs : Finset (↥B × Sym2 (Fin n))) (h0 : Fin n) (S : Finset ↥B) :
    Finset (Fin n) :=
  univ.filter (fun v => s(ctrS Fs h0 S, v) ∈ cls Fs S)

lemma mem_cls {S : Finset ↥B} {e : Sym2 (Fin n)} : e ∈ cls Fs S ↔ Nb Fs e = S := by
  classical
  simp [cls]

lemma cls_card_le_leaves (h0 : Fin n) {S : Finset ↥B} (hS : IsStarE (cls Fs S)) :
    (cls Fs S).card ≤ (leaves Fs h0 S).card := by
  classical
  have hc : ∀ e ∈ cls Fs S, ctrS Fs h0 S ∈ e := by
    rw [ctrS, dif_pos hS]; exact hS.choose_spec
  calc (cls Fs S).card ≤ ((leaves Fs h0 S).image (fun v => s(ctrS Fs h0 S, v))).card := by
        apply card_le_card
        intro e he
        obtain ⟨v, rfl⟩ := exists_other (hc e he)
        exact mem_image.2 ⟨v, by simp [leaves, he], rfl⟩
    _ ≤ _ := card_image_le

include ht hB hcol hFs in
/-- Two vertices are common leaves of at most two star colours. -/
lemma common_leaves_le (hL : LocStar t G) (h0 : Fin n) {v₁ v₂ : Fin n} (hv : v₁ ≠ v₂) :
    ((J1 Fs t).filter (fun S => v₁ ∈ leaves Fs h0 S ∧ v₂ ∈ leaves Fs h0 S)).card ≤ 2 := by
  classical
  by_contra hlt
  push_neg at hlt
  obtain ⟨S₁, h1, S₂, h2, S₃, h3, n12, n13, n23⟩ := two_lt_card.1 hlt
  have info : ∀ S ∈ (J1 Fs t).filter (fun S => v₁ ∈ leaves Fs h0 S ∧ v₂ ∈ leaves Fs h0 S),
      S.card = t - 2 ∧ (∀ T ∈ S, (T, s(v₁, ctrS Fs h0 S)) ∈ Fs ∧ (T, s(v₂, ctrS Fs h0 S)) ∈ Fs) ∧
      s(ctrS Fs h0 S, v₁) ∈ cls Fs S := by
    intro S hS
    simp only [J1, FamC, leaves, mem_filter, mem_univ, true_and] at hS
    refine ⟨hS.1.1.1, fun T hT => ⟨?_, ?_⟩, hS.2.1⟩
    · rw [Sym2.eq_swap]; exact (mem_Nb Fs).1 ((mem_cls.1 hS.2.1).symm ▸ hT)
    · rw [Sym2.eq_swap]; exact (mem_Nb Fs).1 ((mem_cls.1 hS.2.2).symm ▸ hT)
  obtain ⟨c1, e1, m1⟩ := info S₁ h1
  obtain ⟨c2, e2, m2⟩ := info S₂ h2
  obtain ⟨c3, e3, m3⟩ := info S₃ h3
  have hz : ∀ {S S'}, s(ctrS Fs h0 S, v₁) ∈ cls Fs S → s(ctrS Fs h0 S', v₁) ∈ cls Fs S' → S ≠ S' →
      ctrS Fs h0 S ≠ ctrS Fs h0 S' := by
    intro S S' hS hS' hne heq
    rw [heq] at hS
    exact hne ((mem_cls.1 hS).symm.trans (mem_cls.1 hS'))
  obtain ⟨c, hc⟩ := hL v₁ v₂ hv
  exact rainbow3 ht hB col hcol hFs hc hv (hz m1 m2 n12) (hz m1 m3 n13) (hz m2 m3 n23)
    c1 c2 c3 n12 n13 n23 e1 e2 e3

include hcol in
/-- Number of compatible `(t-2)`-families: at most `|B| · 2^(D+1)`. -/
lemma famC_card_le (ht : 4 ≤ t) (hB : ∀ A ∈ B, A.card = t - 2) :
    (FamC B t).card ≤ (univ : Finset ↥B).card * 2 ^ ((t - 2) * (t - 2) + 1) := by
  classical
  calc (FamC B t).card ≤ ((univ : Finset ↥B).biUnion
        (fun A => (insert A (cnb (cmp B) A)).powerset)).card := by
        apply card_le_card
        intro S hS
        have hne : S.Nonempty := by
          rw [← card_pos, (mem_filter.1 hS).2.1]; omega
        obtain ⟨A, hA⟩ := hne
        exact mem_biUnion.2 ⟨A, mem_univ _, mem_powerset.2 (famC_sub_powerset ht hB col hcol hS hA)⟩
    _ ≤ ∑ A : ↥B, (insert A (cnb (cmp B) A)).powerset.card := card_biUnion_le
    _ ≤ ∑ _A : ↥B, 2 ^ ((t - 2) * (t - 2) + 1) := by
        apply sum_le_sum
        intro A _
        rw [card_powerset]
        apply Nat.pow_le_pow_right (by norm_num)
        exact (card_insert_le _ _).trans (by
          have := cnb_card_le col hcol A (hB A.1 A.2); omega)
    _ = _ := by rw [sum_const, smul_eq_mul]

include ht hB hcol hFs in
/-- **Star colours are sparse**: `(∑ |L_S|)² ≤ |J1| (2 n² + |J1| n)`. -/
lemma leaves_sq (hL : LocStar t G) (h0 : Fin n) :
    (∑ S ∈ J1 Fs t, (leaves Fs h0 S).card) ^ 2 ≤
      (J1 Fs t).card * (2 * (n * n) + (J1 Fs t).card * n) := by
  classical
  set J := J1 Fs t
  have hCS := sq_sum_le_card_mul_sum_sq (s := J) (f := fun S => (leaves Fs h0 S).card)
  have hsq : ∀ S, (leaves Fs h0 S).card ^ 2 = ((leaves Fs h0 S).offDiag).card +
      (leaves Fs h0 S).card := by
    intro S; rw [offDiag_card, sq]; have := Nat.le_mul_self (leaves Fs h0 S).card; omega
  have hoff : ∑ S ∈ J, ((leaves Fs h0 S).offDiag).card ≤ 2 * (n * n) := by
    have h1 : ∑ S ∈ J, ((leaves Fs h0 S).offDiag).card =
        ∑ p ∈ (univ : Finset (Fin n)).offDiag,
          (J.filter (fun S => p.1 ∈ leaves Fs h0 S ∧ p.2 ∈ leaves Fs h0 S)).card := by
      have : ∀ S ∈ J, ((leaves Fs h0 S).offDiag).card = ∑ p ∈ (univ : Finset (Fin n)).offDiag,
          if p.1 ∈ leaves Fs h0 S ∧ p.2 ∈ leaves Fs h0 S then 1 else 0 := by
        intro S _
        rw [← card_filter]
        congr 1
        ext p
        simp only [mem_offDiag, mem_filter, mem_univ, true_and]
        tauto
      rw [sum_congr rfl this, sum_comm]
      apply sum_congr rfl
      intro p _
      rw [card_filter]
    rw [h1]
    calc _ ≤ ∑ _p ∈ (univ : Finset (Fin n)).offDiag, 2 := by
          apply sum_le_sum
          intro p hp
          exact common_leaves_le ht hB col hcol hFs hL h0 (mem_offDiag.1 hp).2.2
      _ ≤ 2 * (n * n) := by
          rw [sum_const, smul_eq_mul, offDiag_card, card_univ, Fintype.card_fin, mul_comm]
          exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have hsum : ∑ S ∈ J, (leaves Fs h0 S).card ≤ J.card * n := by
    calc _ ≤ ∑ _S ∈ J, n := sum_le_sum (fun S _ =>
          (card_le_card (subset_univ _)).trans (by simp))
      _ = J.card * n := by rw [sum_const, smul_eq_mul]
  calc _ ≤ J.card * ∑ S ∈ J, (leaves Fs h0 S).card ^ 2 := hCS
    _ = J.card * (∑ S ∈ J, ((leaves Fs h0 S).offDiag).card + ∑ S ∈ J, (leaves Fs h0 S).card) := by
        rw [sum_congr rfl (fun S _ => hsq S), sum_add_distrib]
    _ ≤ _ := Nat.mul_le_mul_left _ (add_le_add hoff hsum)

open scoped Classical in
noncomputable def J2 (Fs : Finset (↥B × Sym2 (Fin n))) (t : ℕ) : Finset (Finset ↥B) :=
  (FamC B t).filter (fun S => ¬ IsStarE (cls Fs S))

open scoped Classical in
/-- The bad vertices: common vertices of the non-star colours. -/
noncomputable def Bst (Fs : Finset (↥B × Sym2 (Fin n))) (t : ℕ) : Finset (Fin n) :=
  univ.filter (fun z => ∃ S ∈ J2 Fs t, ∀ T ∈ S, z ∈ T.1)

include ht hB hcol in
/-- Non-star colours are few. -/
lemma J2_card_le {H : Finset (↥B × Sym2 (Fin n))} (hFsH : Fs ⊆ H) :
    (J2 Fs t).card ≤ (alphaO (cmp B) H).card * 2 ^ ((t - 2) * (t - 2) + 1) := by
  classical
  have key : ∀ S ∈ J2 Fs t, ∃ p ∈ alphaO (cmp B) H, S ∈ (insert p.1 (cnb (cmp B) p.1)).powerset := by
    intro S hS
    simp only [J2, mem_filter] at hS
    have h2 : 1 < S.card := by rw [(mem_filter.1 hS.1).2.1]; omega
    obtain ⟨A, hA, A', hA', hne⟩ := one_lt_card.1 h2
    refine ⟨(A, A'), ?_, mem_powerset.2 (famC_sub_powerset ht hB col hcol hS.1 hA)⟩
    simp only [alphaO, mem_filter, mem_offDiag, mem_univ, true_and]
    refine ⟨hne, (mem_filter.1 hS.1).2.2 A hA A' hA' hne, fun hst => hS.2 ?_⟩
    refine star_mono' (fun e he => ?_) hst
    rw [mem_cls] at he
    rw [mem_CNX]
    exact ⟨hFsH ((mem_Nb Fs).1 (he ▸ hA)), hFsH ((mem_Nb Fs).1 (he ▸ hA'))⟩
  calc (J2 Fs t).card ≤ ((alphaO (cmp B) H).biUnion
        (fun p => (insert p.1 (cnb (cmp B) p.1)).powerset)).card := by
        apply card_le_card
        intro S hS
        obtain ⟨p, hp, hS'⟩ := key S hS
        exact mem_biUnion.2 ⟨p, hp, hS'⟩
    _ ≤ ∑ p ∈ alphaO (cmp B) H, (insert p.1 (cnb (cmp B) p.1)).powerset.card := card_biUnion_le
    _ ≤ ∑ _p ∈ alphaO (cmp B) H, 2 ^ ((t - 2) * (t - 2) + 1) := by
        apply sum_le_sum
        intro p _
        rw [card_powerset]
        apply Nat.pow_le_pow_right (by norm_num)
        exact (card_insert_le _ _).trans (by
          have := cnb_card_le col hcol p.1 (hB p.1.1 p.1.2); omega)
    _ = _ := by rw [sum_const, smul_eq_mul]

include ht hB in
lemma Bst_card_le : (Bst Fs t).card ≤ (J2 Fs t).card * (t - 2) := by
  classical
  calc (Bst Fs t).card ≤ ((J2 Fs t).biUnion (fun S =>
        if h : S.Nonempty then h.choose.1 else ∅)).card := by
        apply card_le_card
        intro z hz
        simp only [Bst, mem_filter, mem_univ, true_and] at hz
        obtain ⟨S, hS, hz⟩ := hz
        have hne : S.Nonempty := by
          rw [← card_pos]
          have := (mem_filter.1 (mem_filter.1 hS).1).2.1
          omega
        exact mem_biUnion.2 ⟨S, hS, by rw [dif_pos hne]; exact hz _ hne.choose_spec⟩
    _ ≤ ∑ S ∈ J2 Fs t, (if h : S.Nonempty then h.choose.1 else ∅).card := card_biUnion_le
    _ ≤ ∑ _S ∈ J2 Fs t, (t - 2) := by
        apply sum_le_sum
        intro S _
        split_ifs with h
        · exact (hB _ h.choose.2).le
        · simp
    _ = _ := by rw [sum_const, smul_eq_mul]

/-! ### The pairs with an incompatible neighbourhood (only for `t = 4`) -/

open scoped Classical in
noncomputable def Gmax (Fs : Finset (↥B × Sym2 (Fin n))) (t : ℕ) : Finset (Sym2 (Fin n)) :=
  univ.filter (fun e => (Nb Fs e).card = t - 2)

open scoped Classical in
noncomputable def G0 (Fs : Finset (↥B × Sym2 (Fin n))) (t : ℕ) : Finset (Sym2 (Fin n)) :=
  (Gmax Fs t).filter (fun e => ¬ CompatSet (cmp B) (Nb Fs e))

open scoped Classical in
/-- Incompatible pairs that are the only incompatible edge of their `β`-triangle. -/
noncomputable def G0b (Fs : Finset (↥B × Sym2 (Fin n))) (H : Finset (↥B × Sym2 (Fin n))) (t : ℕ) :
    Finset (Sym2 (Fin n)) :=
  (G0 Fs t).filter (fun e => ∀ x x', BetaPair (cmp B) H x x' → e ∈ CNX H x x' →
    ∀ f ∈ CNX H x x', f ≠ e → CompatSet (cmp B) (Nb Fs f))

open scoped Classical in
noncomputable def Low (Fs : Finset (↥B × Sym2 (Fin n))) : Finset (Sym2 (Fin n)) :=
  univ.filter (fun e => ¬ e.IsDiag ∧ (Nb Fs e).card ≤ 1)

open scoped Classical in
noncomputable def TriEdges (H : Finset (↥B × Sym2 (Fin n))) (f : Sym2 (Fin n)) :
    Finset (Sym2 (Fin n)) :=
  univ.filter (fun e => ∃ x x', BetaPair (cmp B) H x x' ∧ f ∈ CNX H x x' ∧ e ∈ CNX H x x')

lemma TriEdges_card {H : Finset (↥B × Sym2 (Fin n))} (hg2 : Good2 (cmp B) H) (f : Sym2 (Fin n)) :
    (TriEdges H f).card ≤ 3 := by
  classical
  rcases (TriEdges H f).eq_empty_or_nonempty with he | ⟨e0, he0⟩
  · rw [he]; simp
  simp only [TriEdges, mem_filter, mem_univ, true_and] at he0
  obtain ⟨x0, x0', hb0, hf0, -⟩ := he0
  calc (TriEdges H f).card ≤ (CNX H x0 x0').card := by
        apply card_le_card
        intro e he
        simp only [TriEdges, mem_filter, mem_univ, true_and] at he
        obtain ⟨x, x', hb, hf, he⟩ := he
        rw [hg2 _ _ _ _ hb hb0 ⟨f, mem_inter.2 ⟨hf, hf0⟩⟩] at he
        exact he
    _ = 3 := hb0.2.2.card_eq

/-- The structural input from the deletion lemma. -/
def DLStruct (Fs H : Finset (↥B × Sym2 (Fin n))) : Prop :=
  ∀ e, CompatSet (cmp B) (Nb Fs e) ∨
    ∃ x x', Nb Fs e = {x, x'} ∧ BetaPair (cmp B) H x x' ∧ e ∈ CNX H x x'

def DLMore (Fs H : Finset (↥B × Sym2 (Fin n))) : Prop :=
  ∀ x x' a b c, BetaPair (cmp B) H x x' → a < b → b < c → CNX H x x' = tri a b c →
    Moreover (cmp B) (Nb Fs) a b c

lemma G0_beta {H : Finset (↥B × Sym2 (Fin n))} (hS : DLStruct Fs H) {e : Sym2 (Fin n)}
    (he : e ∈ G0 Fs t) : ∃ x x', BetaPair (cmp B) H x x' ∧ e ∈ CNX H x x' := by
  classical
  have hnc := (mem_filter.1 he).2
  rcases hS e with h | ⟨x, x', -, hb, hex⟩
  · exact absurd h hnc
  · exact ⟨x, x', hb, hex⟩

/-- Few incompatible pairs share their triangle with a low pair. -/
lemma G0a_card {H : Finset (↥B × Sym2 (Fin n))} (hg2 : Good2 (cmp B) H) (hS : DLStruct Fs H)
    (hM : DLMore Fs H) : (G0 Fs t \ G0b Fs H t).card ≤ 3 * (Low Fs).card := by
  classical
  have hsub : G0 Fs t \ G0b Fs H t ⊆ (Low Fs).biUnion (TriEdges H) := by
    intro e he
    rw [mem_sdiff] at he
    obtain ⟨he0, he1⟩ := he
    simp only [G0b, mem_filter, not_and, not_forall, exists_prop] at he1
    obtain ⟨x, x', hb, hex, f, hf, hfe, hfnc⟩ := he1 he0
    have hence := (mem_filter.1 he0).2
    obtain ⟨a, b, c, h1, h2, hτ⟩ := hb.2.2
    have hmo := hM x x' a b c hb h1 h2 hτ
    rw [hτ] at hex hf
    simp only [mem_tri] at hex hf
    have hlow : ∃ g ∈ tri a b c, (Nb Fs g).card ≤ 1 := by
      unfold Moreover at hmo
      rcases hmo with h | h | h | ⟨c1, c2⟩ | ⟨c1, c2⟩ | ⟨c1, c2⟩
      · exact ⟨_, by simp [tri], h⟩
      · exact ⟨_, by simp [tri], h⟩
      · exact ⟨_, by simp [tri], h⟩
      all_goals exfalso
      all_goals rcases hex with rfl | rfl | rfl <;> rcases hf with rfl | rfl | rfl <;>
        first | exact hfe rfl | exact hence c1 | exact hence c2 | exact hfnc c1 | exact hfnc c2
    obtain ⟨g, hg, hgl⟩ := hlow
    have hgnd : ¬ g.IsDiag := by
      simp only [mem_tri] at hg
      rcases hg with rfl | rfl | rfl <;> simp <;> omega
    refine mem_biUnion.2 ⟨g, by simp [Low, hgnd, hgl], ?_⟩
    simp only [TriEdges, mem_filter, mem_univ, true_and]
    refine ⟨x, x', hb, hτ ▸ hg, ?_⟩
    rw [hτ]; simp only [mem_tri]; exact hex
  calc _ ≤ ((Low Fs).biUnion (TriEdges H)).card := card_le_card hsub
    _ ≤ ∑ f ∈ Low Fs, (TriEdges H f).card := card_biUnion_le
    _ ≤ ∑ _f ∈ Low Fs, 3 := sum_le_sum (fun f _ => TriEdges_card hg2 f)
    _ = 3 * (Low Fs).card := by rw [sum_const, smul_eq_mul, mul_comm]

/-- The third vertex of the `β`-triangle through an edge. -/
lemma third_vertex {H : Finset (↥B × Sym2 (Fin n))} {x x' : ↥B} (hb : BetaPair (cmp B) H x x')
    {v u : Fin n} (he : s(v, u) ∈ CNX H x x') :
    ∃ w, w ≠ v ∧ w ≠ u ∧ CNX H x x' = tri v u w := by
  obtain ⟨p, q, r, hpq, hqr, hpr, hpe, hT⟩ := tri_edge hb.2.2 he
  rcases Sym2.eq_iff.1 hpe with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨r, hpr.symm, hqr.symm, hT⟩
  · exact ⟨r, hqr.symm, hpr.symm, by rw [hT, tri_perm_ab]⟩

lemma tri_mem_edges {v u w : Fin n} : s(v, u) ∈ tri v u w ∧ s(v, w) ∈ tri v u w ∧
    s(u, w) ∈ tri v u w := by
  simp [tri]

include ht hFs in
/-- Every vertex meets at most `n / 2` pairs of `G0b`. -/
lemma G0b_half {H : Finset (↥B × Sym2 (Fin n))} (hg2 : Good2 (cmp B) H) (hS : DLStruct Fs H)
    (v : Fin n) : 2 * ((univ : Finset (Fin n)).filter (fun u => s(v, u) ∈ G0b Fs H t)).card ≤ n := by
  classical
  set E := (univ : Finset (Fin n)).filter (fun u => s(v, u) ∈ G0b Fs H t)
  have hw : ∀ u ∈ E, ∃ w, w ∉ E ∧ w ≠ v ∧ ∃ x x', BetaPair (cmp B) H x x' ∧
      CNX H x x' = tri v u w := by
    intro u hu
    have hu' := (mem_filter.1 hu).2
    have hG0 := (mem_filter.1 hu').1
    obtain ⟨x, x', hb, hex⟩ := G0_beta hS hG0
    obtain ⟨w, hwv, hwu, hT⟩ := third_vertex hb hex
    refine ⟨w, fun hwE => ?_, hwv, x, x', hb, hT⟩
    have hcomp := (mem_filter.1 hu').2 x x' hb hex (s(v, w)) (hT ▸ tri_mem_edges.2.1)
      (fun h => hwu (Sym2.congr_right.1 h))
    have := (mem_filter.1 (mem_filter.1 (mem_filter.1 hwE).2).1).2
    exact this hcomp
  rcases E.eq_empty_or_nonempty with hE | ⟨u0, hu0⟩
  · rw [hE]; simp
  haveI : Nonempty (Fin n) := ⟨v⟩
  choose! f hf using hw
  have hinj : Set.InjOn f E := by
    intro u1 h1 u2 h2 heq
    obtain ⟨-, -, x1, x1', hb1, hT1⟩ := hf u1 h1
    obtain ⟨-, -, x2, x2', hb2, hT2⟩ := hf u2 h2
    have hsame : CNX H x1 x1' = CNX H x2 x2' := hg2 _ _ _ _ hb1 hb2
      ⟨s(v, f u1), mem_inter.2 ⟨hT1 ▸ tri_mem_edges.2.1, heq ▸ hT2 ▸ tri_mem_edges.2.1⟩⟩
    have hu1 := (mem_filter.1 h1).2
    by_contra hne
    have h2' : s(v, u2) ∈ CNX H x1 x1' := hsame ▸ hT2 ▸ tri_mem_edges.1
    have := (mem_filter.1 hu1).2 x1 x1' hb1 (hT1 ▸ tri_mem_edges.1) _ h2'
      (fun h => hne (Sym2.congr_right.1 h).symm)
    exact (mem_filter.1 (mem_filter.1 (mem_filter.1 h2).2).1).2 this
  have hdisj : Disjoint E (E.image f) := by
    rw [disjoint_left]
    intro u hu hu'
    obtain ⟨u', hu'E, rfl⟩ := mem_image.1 hu'
    exact (hf u' hu'E).1 hu
  have hv1 : v ∉ E ∪ E.image f := by
    rw [mem_union, not_or]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hc : (Nb Fs s(v, v)).card = t - 2 :=
        (mem_filter.1 (mem_filter.1 (mem_filter.1 (mem_filter.1 h).2).1).1).2
      have hnd : (Nb Fs s(v, v)).card = 0 := by
        rw [card_eq_zero, eq_empty_iff_forall_notMem]
        intro x hx
        exact (PEdge_mk.1 (hFs _ ((mem_Nb Fs).1 hx))).1 rfl
      omega
    · obtain ⟨u', hu'E, hfu⟩ := mem_image.1 h
      exact (hf u' hu'E).2.1 hfu
  have hcard : (E ∪ E.image f).card + 1 ≤ n := by
    have := card_le_card (subset_univ (insert v (E ∪ E.image f)))
    rw [card_insert_of_notMem hv1, card_univ, Fintype.card_fin] at this
    exact this
  rw [card_union_of_disjoint hdisj, card_image_of_injOn hinj] at hcard
  omega

lemma incl_excl3 (A B' C : Finset (Fin n)) :
    A.card + B'.card + C.card ≤ (A ∩ B').card + (A ∩ C).card + (B' ∩ C).card + n := by
  classical
  have h1 := card_union_add_card_inter A B'
  have h2 := card_union_add_card_inter (A ∪ B') C
  have h3 : ((A ∪ B') ∩ C).card ≤ (A ∩ C).card + (B' ∩ C).card := by
    rw [union_inter_distrib_right]; exact card_union_le _ _
  have h4 : ((A ∪ B') ∪ C).card ≤ n := (card_le_card (subset_univ _)).trans (by simp)
  omega

include ht hB hcol hFs in
/-- A `β`-triangle has no pair with many common good neighbours of a single colour family. -/
lemma beta_pair_contra (hL : LocStar t G) (h0 : Fin n) (hR : ¬ G.HasRepeatedDisjointUnion)
    {H : Finset (↥B × Sym2 (Fin n))} (hHp : H ⊆ proj G B) {x x' : ↥B}
    (hb : BetaPair (cmp B) H x x') {p q r : Fin n} (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r)
    (hT : CNX H x x' = tri p q r) (hp : p ∉ Bst Fs t) (hq : q ∉ Bst Fs t) (hr : r ∉ Bst Fs t)
    (N2 : Fin n → Finset (Fin n))
    (hN2 : ∀ v w, w ∈ N2 v → Nb Fs s(v, w) ∈ J2 Fs t ∧ w ∉ Bst Fs t ∧ w ≠ v)
    (hbig : (J2 Fs t).card * (J2 Fs t).card + 2 ≤ (N2 p ∩ N2 q).card) : False := by
  classical
  have hJ2 : ∀ S ∈ J2 Fs t, S.card = t - 2 := fun S hS => (mem_filter.1 (mem_filter.1 hS).1).2.1
  have hBst : ∀ z, z ∉ Bst Fs t → ∀ S ∈ J2 Fs t, ¬ ∀ T ∈ S, z ∈ T.1 := by
    intro z hz S hS hall
    exact hz (mem_filter.2 ⟨mem_univ _, S, hS, hall⟩)
  have hpW : p ∉ N2 p ∩ N2 q := fun h => (hN2 p p (mem_inter.1 h).1).2.2 rfl
  have hqW : q ∉ N2 p ∩ N2 q := fun h => (hN2 q q (mem_inter.1 h).2).2.2 rfl
  obtain ⟨S, hSc⟩ := mono_K2t ht hB col hcol hFs hL hpq (N2 p ∩ N2 q) hpW hqW (J2 Fs t) hJ2
    (fun w hw => ⟨(hN2 p w (mem_inter.1 hw).1).1, (hN2 q w (mem_inter.1 hw).2).1⟩)
    (fun S hS z hz => by
      rcases hz with rfl | rfl | hz
      · exact hBst _ hp S hS
      · exact hBst _ hq S hS
      · exact hBst _ (hN2 p z (mem_inter.1 hz).1).2.1 S hS)
  set Wm := (N2 p ∩ N2 q).filter (fun w => Nb Fs s(p, w) = S ∧ Nb Fs s(q, w) = S)
  obtain ⟨w1, hw1, w2, hw2, hw12⟩ := one_lt_card.1 (show 1 < Wm.card by omega)
  have hm1 := (mem_filter.1 hw1).2
  have hm2 := (mem_filter.1 hw2).2
  have hS2 : S ∈ J2 Fs t := hm1.1 ▸ (hN2 p w1 (mem_inter.1 (mem_filter.1 hw1).1).1).1
  have hedges : ∀ w, Nb Fs s(p, w) = S → Nb Fs s(q, w) = S →
      ∀ T ∈ S, (T, s(p, w)) ∈ Fs ∧ (T, s(q, w)) ∈ Fs := by
    intro w h1 h2 T hT
    exact ⟨(mem_Nb Fs).1 (h1 ▸ hT), (mem_Nb Fs).1 (h2 ▸ hT)⟩
  obtain ⟨c0, hc0⟩ := hL p q hpq
  have hin : ∀ T ∈ S, c0 ∈ T.1 := by
    rcases ctr_family ht hB hFs hc0 hpq (hedges w1 hm1.1 hm1.2) with h | h
    · rcases ctr_family ht hB hFs hc0 hpq (hedges w2 hm2.1 hm2.2) with h' | h'
      · exact absurd (h.symm.trans h') hw12
      · exact h'
    · exact h
  have hc0B : c0 ∈ Bst Fs t := mem_filter.2 ⟨mem_univ _, S, hS2, hin⟩
  have hTp : CNX (proj G B) x x' = tri p q r := by
    rw [hb.of_sub hHp (proj_good1 ht hB hR h0)]; exact hT
  have := center_eq_third ht hB hb.2.1 hpq hqr hpr hTp hc0
  exact hr (this ▸ hc0B)

include ht hB hcol hFs in
/-- No `β`-triangle has all three vertices of large good degree. -/
lemma no_beta_in_V (hL : LocStar t G) (h0 : Fin n) (hR : ¬ G.HasRepeatedDisjointUnion)
    {H : Finset (↥B × Sym2 (Fin n))} (hHp : H ⊆ proj G B) {x x' : ↥B}
    (hb : BetaPair (cmp B) H x x') {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hT : CNX H x x' = tri a b c) (ha : a ∉ Bst Fs t) (hb' : b ∉ Bst Fs t) (hc : c ∉ Bst Fs t)
    (N2 : Fin n → Finset (Fin n))
    (hN2 : ∀ v w, w ∈ N2 v → Nb Fs s(v, w) ∈ J2 Fs t ∧ w ∉ Bst Fs t ∧ w ≠ v)
    (hdeg : 9 * n ≤ 8 * ((N2 a).card + (N2 b).card + (N2 c).card))
    (hn : 24 * ((J2 Fs t).card * (J2 Fs t).card + 2) ≤ n) : False := by
  have hie := incl_excl3 (N2 a) (N2 b) (N2 c)
  have key : 24 * ((J2 Fs t).card * (J2 Fs t).card + 2) ≤
      24 * max (N2 a ∩ N2 b).card (max (N2 a ∩ N2 c).card (N2 b ∩ N2 c).card) := by
    have := le_max_left (N2 a ∩ N2 b).card (max (N2 a ∩ N2 c).card (N2 b ∩ N2 c).card)
    have := le_max_left (N2 a ∩ N2 c).card (N2 b ∩ N2 c).card
    have := le_max_right (N2 a ∩ N2 c).card (N2 b ∩ N2 c).card
    have := le_max_right (N2 a ∩ N2 b).card (max (N2 a ∩ N2 c).card (N2 b ∩ N2 c).card)
    omega
  rcases le_total (max (N2 a ∩ N2 c).card (N2 b ∩ N2 c).card) (N2 a ∩ N2 b).card with h | h
  · rw [max_eq_left h] at key
    exact beta_pair_contra ht hB col hcol hFs hL h0 hR hHp hb hab hbc hac hT ha hb' hc N2 hN2
      (by omega)
  · rw [max_eq_right h] at key
    rcases le_total (N2 b ∩ N2 c).card (N2 a ∩ N2 c).card with h' | h'
    · rw [max_eq_left h'] at key
      exact beta_pair_contra ht hB col hcol hFs hL h0 hR hHp hb hac hbc.symm hab hT' ha hc hb'
        N2 hN2 (by omega)
    · rw [max_eq_right h'] at key
      exact beta_pair_contra ht hB col hcol hFs hL h0 hR hHp hb hbc hac.symm hab.symm hT'' hb' hc ha
        N2 hN2 (by omega)
  where
    hT' : CNX H x x' = tri a c b := by rw [hT, tri_perm_bc]
    hT'' : CNX H x x' = tri b c a := by rw [hT, tri_perm_ab, tri_perm_bc]

/-- Inside a set `V` containing no `β`-triangle, `G0b`-degrees are bounded by `|Vᶜ|`. -/
lemma G0b_deg_V {H : Finset (↥B × Sym2 (Fin n))} (hg2 : Good2 (cmp B) H) (hS : DLStruct Fs H)
    (V : Finset (Fin n))
    (hV : ∀ x x' a b c, BetaPair (cmp B) H x x' → CNX H x x' = tri a b c → a ∈ V → b ∈ V →
      c ∈ V → False)
    {v : Fin n} (hv : v ∈ V) :
    ((univ : Finset (Fin n)).filter (fun u => s(v, u) ∈ G0b Fs H t)).card ≤ (univ \ V).card := by
  classical
  set E := (univ : Finset (Fin n)).filter (fun u => s(v, u) ∈ G0b Fs H t)
  have hw : ∀ u ∈ E, ∃ z, z ∉ V ∧ ∃ x x' w, BetaPair (cmp B) H x x' ∧
      CNX H x x' = tri v u w ∧ (z = u ∨ z = w) := by
    intro u hu
    have hu' := (mem_filter.1 hu).2
    obtain ⟨x, x', hb, hex⟩ := G0_beta hS (mem_filter.1 hu').1
    obtain ⟨w, -, -, hT⟩ := third_vertex hb hex
    by_cases huV : u ∈ V
    · by_cases hwV : w ∈ V
      · exact absurd (hV x x' v u w hb hT hv huV hwV) id
      · exact ⟨w, hwV, x, x', w, hb, hT, Or.inr rfl⟩
    · exact ⟨u, huV, x, x', w, hb, hT, Or.inl rfl⟩
  rcases E.eq_empty_or_nonempty with hE | ⟨u0, -⟩
  · rw [hE]; simp
  haveI : Nonempty (Fin n) := ⟨v⟩
  choose! f hf using hw
  calc E.card ≤ (univ \ V).card := by
        apply card_le_card_of_injOn f
        · intro u hu
          exact mem_coe.2 (mem_sdiff.2 ⟨mem_univ _, (hf u hu).1⟩)
        · intro u1 h1 u2 h2 heq
          obtain ⟨hz1, x1, x1', w1, hb1, hT1, hzu1⟩ := hf u1 h1
          obtain ⟨-, x2, x2', w2, hb2, hT2, hzu2⟩ := hf u2 h2
          have hzv : f u1 ≠ v := fun h => hz1 (h ▸ hv)
          have m1 : s(v, f u1) ∈ CNX H x1 x1' := by
            rw [hT1]; rcases hzu1 with h | h <;> rw [h] <;> simp [tri]
          have m2 : s(v, f u1) ∈ CNX H x2 x2' := by
            rw [hT2, heq]; rcases hzu2 with h | h <;> rw [h] <;> simp [tri]
          have hsame := hg2 _ _ _ _ hb1 hb2 ⟨_, mem_inter.2 ⟨m1, m2⟩⟩
          by_contra hne
          have hu1 := (mem_filter.1 h1).2
          have e2 : s(v, u2) ∈ CNX H x1 x1' := by rw [hsame, hT2]; simp [tri]
          have := (mem_filter.1 hu1).2 x1 x1' hb1 (by rw [hT1]; simp [tri]) _ e2
            (fun h => hne (Sym2.congr_right.1 h).symm)
          exact (mem_filter.1 (mem_filter.1 (mem_filter.1 h2).2).1).2 this
    _ = _ := rfl

/-- Handshake lemma for a set of non-diagonal pairs. -/
lemma handshake (Q : Finset (Sym2 (Fin n))) (hQ : ∀ e ∈ Q, ¬ e.IsDiag) :
    ∑ v : Fin n, ((univ : Finset (Fin n)).filter (fun u => s(v, u) ∈ Q)).card = 2 * Q.card := by
  classical
  have h1 : ∑ v : Fin n, ((univ : Finset (Fin n)).filter (fun u => s(v, u) ∈ Q)).card =
      ((univ : Finset (Fin n × Fin n)).filter (fun p => s(p.1, p.2) ∈ Q)).card := by
    rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) (fun _ _ => mem_univ _)]
    apply sum_congr rfl
    intro v _
    apply card_bij (fun u _ => (v, u))
    · intro u hu; simp only [mem_filter, mem_univ, true_and] at hu ⊢; simp_all
    · intro u _ u' _ h; simpa using h
    · intro p hp
      simp only [mem_filter, mem_univ, true_and] at hp
      exact ⟨p.2, by simp only [mem_filter, mem_univ, true_and]; rw [← hp.2]; exact hp.1,
        by rw [← hp.2]⟩
  rw [h1, card_eq_sum_card_fiberwise
    (s := (univ : Finset (Fin n × Fin n)).filter (fun p => s(p.1, p.2) ∈ Q))
    (f := fun p : Fin n × Fin n => s(p.1, p.2)) (t := Q) (fun p hp => (mem_filter.1 hp).2)]
  rw [mul_comm, ← smul_eq_mul, ← sum_const]
  apply sum_congr rfl
  intro e he
  obtain ⟨⟨a, b⟩, rfl⟩ := Quot.exists_rep e
  have hab : a ≠ b := fun h => hQ _ he (by simp [h])
  have : ((univ : Finset (Fin n × Fin n)).filter (fun p => s(p.1, p.2) ∈ Q)).filter
      (fun p => s(p.1, p.2) = Quot.mk _ (a, b)) = {(a, b), (b, a)} := by
    ext ⟨p, q⟩
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨-, h⟩
      have h' : s(p, q) = s(a, b) := h
      rcases Sym2.eq_iff.1 h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨he, rfl⟩
      · exact ⟨by rw [Sym2.eq_swap]; exact he, Sym2.eq_swap⟩
  rw [this, card_pair (by simp [hab])]

include ht hB hcol hFs in
/-- **The cluster lemma** for a single block, with explicit error terms. -/
theorem cluster (hL : LocStar t G) (h0 : Fin n) (hR : ¬ G.HasRepeatedDisjointUnion)
    {H : Finset (↥B × Sym2 (Fin n))} (hFsH : Fs ⊆ H) (hHp : H ⊆ proj G B)
    (hg2 : Good2 (cmp B) H) (hS : DLStruct Fs H) (hM : DLMore Fs H) (δN : ℕ)
    (hdens : (t - 2) * n.choose 2 ≤ Fs.card + δN)
    (hn24 : 24 * ((J2 Fs t).card * (J2 Fs t).card + 2) ≤ n)
    (hV3 : 16 * (4 * δN + (∑ S ∈ J1 Fs t, (leaves Fs h0 S).card) + (Bst Fs t).card * n) +
      (n - 8) * (Bst Fs t).card + 3 * (n - 8) ≤ (n - 8) * n) :
    ∃ S : Finset ↥B, ∃ v v' : Fin n, ∃ W : Finset (Fin n), ∃ x m : ℕ,
      v ≠ v' ∧ v ∉ W ∧ v' ∉ W ∧ (∀ w ∈ W, Nb Fs s(v, w) = S ∧ Nb Fs s(v', w) = S) ∧
      (W.Nonempty → S ∈ FamC B t) ∧
      n ≤ W.card + (J2 Fs t).card * (J2 Fs t).card + 2 + 2 * m + 2 * x ∧
      (n - x - 1) * m ≤
        2 * (4 * δN + (∑ S ∈ J1 Fs t, (leaves Fs h0 S).card) + (Bst Fs t).card * n) ∧
      (n - 8) * x ≤
        16 * (4 * δN + (∑ S ∈ J1 Fs t, (leaves Fs h0 S).card) + (Bst Fs t).card * n) +
          (n - 8) * (Bst Fs t).card := by
  classical
  set Λ := ∑ S ∈ J1 Fs t, (leaves Fs h0 S).card with hΛ
  set b := (Bst Fs t).card with hb
  set j2 := (J2 Fs t).card with hj2
  set Mis := 4 * δN + Λ + b * n with hMis
  -- basic facts
  have hnd : ∀ p ∈ Fs, ¬ p.2.IsDiag := by
    rintro ⟨A, e⟩ hp
    obtain ⟨u, v, rfl, huv, -⟩ := hFs _ hp
    simpa using huv
  have hS' : ∀ e, CompatSet (cmp B) (Nb Fs e) ∨ (Nb Fs e).card ≤ 2 := by
    intro e
    rcases hS e with h | ⟨x, x', hxx, -, -⟩
    · exact Or.inl h
    · right; rw [hxx]; exact card_le_two
  have hle := Nb_card_le ht col hcol hS'
  have hNM := notmax_card hnd hle
  set NotMax := (univ : Finset (Sym2 (Fin n))).filter
    (fun e => ¬ e.IsDiag ∧ (Nb Fs e).card < t - 2) with hNotMax
  have hNMc : NotMax.card ≤ δN := by omega
  have hLow : Low Fs ⊆ NotMax := by
    intro e he
    simp only [Low, mem_filter, mem_univ, true_and] at he
    simp only [hNotMax, mem_filter, mem_univ, true_and]
    exact ⟨he.1, by omega⟩
  have hG0a := G0a_card hg2 hS hM (t := t)
  have hLowc := card_le_card hLow
  have hGMnd : ∀ e ∈ Gmax Fs t, ¬ e.IsDiag := by
    intro e he hd
    have hc := (mem_filter.1 he).2
    have h0' : (Nb Fs e).card = 0 := by
      rw [card_eq_zero, eq_empty_iff_forall_notMem]
      intro x hx; exact hnd _ ((mem_Nb Fs).1 hx) hd
    omega
  -- the good graph `Q`
  set G2s := (Gmax Fs t).filter (fun e => Nb Fs e ∈ J2 Fs t ∧ ∀ z ∈ e, z ∉ Bst Fs t) with hG2s
  set G0s := (G0b Fs H t).filter (fun e => ∀ z ∈ e, z ∉ Bst Fs t) with hG0s
  set Q := G2s ∪ G0s with hQ
  have hQnd : ∀ e ∈ Q, ¬ e.IsDiag := by
    intro e he
    rcases mem_union.1 he with h | h
    · exact hGMnd e (mem_filter.1 h).1
    · exact hGMnd e (mem_filter.1 (mem_filter.1 (mem_filter.1 h).1).1).1
  -- covering all pairs
  set ND := (univ : Finset (Sym2 (Fin n))).filter (fun e => ¬ e.IsDiag) with hND
  set G1 := (Gmax Fs t).filter (fun e => Nb Fs e ∈ J1 Fs t) with hG1
  set Touch := (Bst Fs t).biUnion (fun z => (univ : Finset (Fin n)).image (fun u => s(z, u)))
    with hTouch
  have hcover : ND ⊆ NotMax ∪ G1 ∪ (G0 Fs t \ G0b Fs H t) ∪ Touch ∪ Q := by
    intro e he
    have hend := (mem_filter.1 he).2
    by_cases hlt : (Nb Fs e).card < t - 2
    · simp [hNotMax, hend, hlt]
    have hGM : e ∈ Gmax Fs t := mem_filter.2 ⟨mem_univ _, by have := hle e; omega⟩
    by_cases htc : ∃ z ∈ e, z ∈ Bst Fs t
    · obtain ⟨z, hz, hzB⟩ := htc
      obtain ⟨u, rfl⟩ := exists_other hz
      simp only [mem_union]
      exact Or.inl (Or.inr (mem_biUnion.2 ⟨z, hzB, mem_image.2 ⟨u, mem_univ _, rfl⟩⟩))
    push_neg at htc
    by_cases hc : CompatSet (cmp B) (Nb Fs e)
    · have hF : Nb Fs e ∈ FamC B t := by
        simp only [FamC, mem_filter, mem_univ, true_and]
        exact ⟨(mem_filter.1 hGM).2, hc⟩
      by_cases hst : IsStarE (cls Fs (Nb Fs e))
      · have : e ∈ G1 := mem_filter.2 ⟨hGM, mem_filter.2 ⟨hF, hst⟩⟩
        simp [this]
      · have : e ∈ Q := mem_union_left _ (mem_filter.2 ⟨hGM, mem_filter.2 ⟨hF, hst⟩, htc⟩)
        simp [this]
    · have hG0 : e ∈ G0 Fs t := mem_filter.2 ⟨hGM, hc⟩
      by_cases hb0 : e ∈ G0b Fs H t
      · have : e ∈ Q := mem_union_right _ (mem_filter.2 ⟨hb0, htc⟩)
        simp [this]
      · have : e ∈ G0 Fs t \ G0b Fs H t := mem_sdiff.2 ⟨hG0, hb0⟩
        simp [this]
  have hG1c : G1.card ≤ Λ := by
    calc G1.card ≤ ((J1 Fs t).biUnion (cls Fs)).card := by
          apply card_le_card
          intro e he
          exact mem_biUnion.2 ⟨_, (mem_filter.1 he).2, mem_cls.2 rfl⟩
      _ ≤ ∑ S ∈ J1 Fs t, (cls Fs S).card := card_biUnion_le
      _ ≤ Λ := sum_le_sum (fun S hS => cls_card_le_leaves h0 (mem_filter.1 hS).2)
  have hTc : Touch.card ≤ b * n := by
    calc Touch.card ≤ ∑ z ∈ Bst Fs t, ((univ : Finset (Fin n)).image (fun u => s(z, u))).card :=
          card_biUnion_le
      _ ≤ ∑ _z ∈ Bst Fs t, n := sum_le_sum (fun z _ => card_image_le.trans (by simp))
      _ = b * n := by rw [sum_const, smul_eq_mul]
  have hNDc : ND.card = n.choose 2 := card_nondiag
  have hQbig : n.choose 2 ≤ Mis + Q.card := by
    have := card_le_card hcover
    have h1 := card_union_le (NotMax ∪ G1 ∪ (G0 Fs t \ G0b Fs H t) ∪ Touch) Q
    have h2 := card_union_le (NotMax ∪ G1 ∪ (G0 Fs t \ G0b Fs H t)) Touch
    have h3 := card_union_le (NotMax ∪ G1) (G0 Fs t \ G0b Fs H t)
    have h4 := card_union_le NotMax G1
    omega
  -- degrees
  set dQ : Fin n → ℕ := fun v => ((univ : Finset (Fin n)).filter (fun u => s(v, u) ∈ Q)).card
    with hdQ
  have hhs := handshake Q hQnd
  have hhsND := handshake ND (fun e he => (mem_filter.1 he).2)
  have hNDdeg : ∀ v : Fin n, ((univ : Finset (Fin n)).filter (fun u => s(v, u) ∈ ND)).card =
      n - 1 := by
    intro v
    have : (univ : Finset (Fin n)).filter (fun u => s(v, u) ∈ ND) = univ.erase v := by
      ext u; simp [hND, eq_comm]
    rw [this, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  rw [sum_congr rfl (fun v _ => hNDdeg v), sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul, hNDc] at hhsND
  have hdQle : ∀ v, dQ v ≤ n - 1 := by
    intro v
    rw [← hNDdeg v]
    apply card_le_card
    intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu ⊢
    exact mem_filter.2 ⟨mem_univ _, hQnd _ hu⟩
  set mm : Fin n → ℕ := fun v => n - 1 - dQ v with hmm
  have hsum_m : ∑ v : Fin n, mm v ≤ 2 * Mis := by
    have h1 : ∑ v : Fin n, mm v + ∑ v : Fin n, dQ v = ∑ _v : Fin n, (n - 1) := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro v _
      simp only [hmm]; have := hdQle v; omega
    rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h1
    have h2 : ∑ v : Fin n, dQ v = 2 * Q.card := hhs
    omega
  -- `G2` neighbourhoods
  set N2 : Fin n → Finset (Fin n) := fun v => (univ : Finset (Fin n)).filter (fun u => s(v, u) ∈ G2s)
    with hN2def
  have hN2 : ∀ v w, w ∈ N2 v → Nb Fs s(v, w) ∈ J2 Fs t ∧ w ∉ Bst Fs t ∧ w ≠ v := by
    intro v w hw
    simp only [hN2def, mem_filter, mem_univ, true_and, hG2s] at hw
    refine ⟨hw.2.1, hw.2.2 w (by simp), fun h => hGMnd _ hw.1 (by simp [h])⟩
  set E0 : Fin n → Finset (Fin n) := fun v =>
    (univ : Finset (Fin n)).filter (fun u => s(v, u) ∈ G0b Fs H t) with hE0def
  have hdQ_split : ∀ v, dQ v ≤ (N2 v).card + (E0 v).card := by
    intro v
    calc dQ v ≤ (N2 v ∪ E0 v).card := by
          apply card_le_card
          intro u hu
          simp only [hdQ, mem_filter, mem_univ, true_and, hQ, mem_union, hG0s] at hu
          rcases hu with h | h
          · exact mem_union_left _ (by simp [hN2def, h])
          · exact mem_union_right _ (by simp [hE0def, h.1])
      _ ≤ _ := card_union_le _ _
  have hE0half : ∀ v, 2 * (E0 v).card ≤ n := fun v => G0b_half ht hFs hg2 hS v
  -- the set `V`
  set V := (univ : Finset (Fin n)).filter (fun v => v ∉ Bst Fs t ∧ 7 * n ≤ 8 * dQ v) with hVdef
  have hV2 : ∀ v ∈ V, 3 * n ≤ 8 * (N2 v).card := by
    intro v hv
    have h1 := (mem_filter.1 hv).2.2
    have h2 := hdQ_split v
    have h3 := hE0half v
    omega
  have hnoV : ∀ x x' a b' c, BetaPair (cmp B) H x x' → CNX H x x' = tri a b' c → a ∈ V →
      b' ∈ V → c ∈ V → False := by
    intro x x' a b' c hbt hT ha hb' hc
    have hd : ∀ {p q : Fin n}, s(p, q) ∈ CNX H x x' → p ≠ q := by
      intro p q h hpq
      rw [mem_CNX] at h
      exact (PEdge_mk.1 ((mem_proj).1 (hHp h.1))).1 hpq
    have hab : a ≠ b' := hd (hT ▸ (by simp [tri]))
    have hbc : b' ≠ c := hd (hT ▸ (by simp [tri]))
    have hac : a ≠ c := hd (hT ▸ (by simp [tri]))
    exact no_beta_in_V ht hB col hcol hFs hL h0 hR hHp hbt hab hbc hac hT
      (mem_filter.1 ha).2.1 (mem_filter.1 hb').2.1 (mem_filter.1 hc).2.1 N2 hN2
      (by have := hV2 a ha; have := hV2 b' hb'; have := hV2 c hc; omega) hn24
  have hE0V : ∀ v ∈ V, (E0 v).card ≤ (univ \ V).card := fun v hv => G0b_deg_V hg2 hS V hnoV hv
  set x := (univ \ V).card with hx
  -- vertices outside `V`
  have hxb : (n - 8) * x ≤ 16 * Mis + (n - 8) * b := by
    set Lo := (univ : Finset (Fin n)).filter (fun v => 8 * dQ v < 7 * n)
    have hsub : univ \ V ⊆ Bst Fs t ∪ Lo := by
      intro v hv
      simp only [mem_sdiff, mem_univ, true_and, hVdef, mem_filter, not_and_or, not_not,
        not_le] at hv
      rcases hv with h | h
      · exact mem_union_left _ h
      · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, h⟩)
    have hLo : (n - 8) * Lo.card ≤ 16 * Mis := by
      calc (n - 8) * Lo.card = ∑ _v ∈ Lo, (n - 8) := by rw [sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ v ∈ Lo, 8 * mm v := by
            apply sum_le_sum
            intro v hv
            have := (mem_filter.1 hv).2
            have := hdQle v
            simp only [hmm]; omega
        _ ≤ ∑ v : Fin n, 8 * mm v := sum_le_sum_of_subset (subset_univ _)
        _ = 8 * ∑ v : Fin n, mm v := by rw [mul_sum]
        _ ≤ 16 * Mis := by omega
    have := card_le_card hsub
    have := card_union_le (Bst Fs t) Lo
    have : (n - 8) * x ≤ (n - 8) * (b + Lo.card) := Nat.mul_le_mul_left _ (by omega)
    rw [mul_add] at this
    omega
  have hVc : V.card + x = n := by
    rw [hx, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
    have := card_le_card (subset_univ V); simp at this; omega
  have hV3' : 3 ≤ V.card := by
    have h1 : (n - 8) * (x + 3) ≤ (n - 8) * n := by rw [mul_add]; omega
    rcases Nat.eq_zero_or_pos (n - 8) with h | h
    · omega
    · have := Nat.le_of_mul_le_mul_left h1 h; omega
  -- two vertices of `V` with the smallest missing degree
  obtain ⟨v, hv, hvmin⟩ := exists_min_image V mm (card_pos.1 (by omega))
  obtain ⟨v', hv', hv'min⟩ := exists_min_image (V.erase v) mm
    (card_pos.1 (by rw [card_erase_of_mem hv]; omega))
  have hvv' : v ≠ v' := fun h => (mem_erase.1 hv').1 h.symm
  have hv'V := (mem_erase.1 hv').2
  have hmv : mm v ≤ mm v' := hvmin v' hv'V
  have ho2 : (n - x - 1) * mm v' ≤ 2 * Mis := by
    calc (n - x - 1) * mm v' = ∑ _u ∈ V.erase v, mm v' := by
          rw [sum_const, smul_eq_mul, card_erase_of_mem hv]; congr 1; omega
      _ ≤ ∑ u ∈ V.erase v, mm u := sum_le_sum (fun u hu => hv'min u hu)
      _ ≤ ∑ u : Fin n, mm u := sum_le_sum_of_subset (subset_univ _)
      _ ≤ 2 * Mis := hsum_m
  -- the common neighbourhood and the monochromatic part
  have hN2v : ∀ u ∈ V, n - 1 - mm u ≤ (N2 u).card + x := by
    intro u hu
    have h1 := hdQ_split u
    have h2 := hE0V u hu
    have h3 := hdQle u
    simp only [hmm]; omega
  have hW0c : (N2 v).card + (N2 v').card ≤ (N2 v ∩ N2 v').card + n := by
    have e1 := card_union_add_card_inter (N2 v) (N2 v')
    have e2 : (N2 v ∪ N2 v').card ≤ n := (card_le_card (subset_univ _)).trans (by simp)
    omega
  set W0 := N2 v ∩ N2 v' with hW0
  have hvW0 : v ∉ W0 := fun h => (hN2 v v (mem_inter.1 h).1).2.2 rfl
  have hv'W0 : v' ∉ W0 := fun h => (hN2 v' v' (mem_inter.1 h).2).2.2 rfl
  have hBst_out : ∀ z, z ∉ Bst Fs t → ∀ S ∈ J2 Fs t, ¬ ∀ T ∈ S, z ∈ T.1 := by
    intro z hz S hS hall
    exact hz (mem_filter.2 ⟨mem_univ _, S, hS, hall⟩)
  obtain ⟨S, hSc⟩ := mono_K2t ht hB col hcol hFs hL hvv' W0 hvW0 hv'W0 (J2 Fs t)
    (fun S hS => (mem_filter.1 (mem_filter.1 hS).1).2.1)
    (fun w hw => ⟨(hN2 v w (mem_inter.1 hw).1).1, (hN2 v' w (mem_inter.1 hw).2).1⟩)
    (fun S hS z hz => by
      rcases hz with rfl | rfl | hz
      · exact hBst_out _ (mem_filter.1 hv).2.1 S hS
      · exact hBst_out _ (mem_filter.1 hv'V).2.1 S hS
      · exact hBst_out _ (hN2 v z (mem_inter.1 hz).1).2.1 S hS)
  set W := W0.filter (fun w => Nb Fs s(v, w) = S ∧ Nb Fs s(v', w) = S) with hW
  refine ⟨S, v, v', W, x, mm v', hvv', fun h => hvW0 (mem_filter.1 h).1,
    fun h => hv'W0 (mem_filter.1 h).1, fun w hw => (mem_filter.1 hw).2, ?_, ?_, ho2, hxb⟩
  · rintro ⟨w, hw⟩
    have hw' := mem_filter.1 hw
    rw [← hw'.2.1]
    exact (mem_filter.1 (hN2 v w (mem_inter.1 hw'.1).1).1).1
  · have h1 := hN2v v hv
    have h2 := hN2v v' hv'V
    have h3 := hdQle v
    have h4 := hdQle v'
    have k1 : (N2 v).card + (N2 v').card ≤ W.card + j2 * j2 + n := by
      have e1 := hSc; rw [← hj2] at e1; have := hW0c; omega
    have k2 : dQ v ≤ (N2 v).card + x := by simp only [hmm] at h1; omega
    have k3 : dQ v' ≤ (N2 v').card + x := by simp only [hmm] at h2; omega
    have k4 : dQ v' ≤ dQ v := by simp only [hmm] at hmv; omega
    show n ≤ W.card + j2 * j2 + 2 + 2 * (n - 1 - dQ v') + 2 * x
    omega

end Cluster

end OMA_H2

/-!
# Erdős 643, CN-stability: averaging over permutations (replacing the random permutation)
-/

namespace OMA_H2

open Finset OMA_DL

variable {n : ℕ}

/-- Two colourings with the same fibre sizes differ by a permutation. -/
lemma exists_perm_of_fibres {C : Type*} [Fintype C] [DecidableEq C] (p ψ : Fin n → C)
    (h : ∀ c, (univ.filter (fun v => p v = c)).card = (univ.filter (fun v => ψ v = c)).card) :
    ∃ τ : Equiv.Perm (Fin n), ∀ v, ψ (τ v) = p v := by
  classical
  have e : ∀ c, {v // p v = c} ≃ {v // ψ v = c} := fun c =>
    Fintype.equivOfCardEq (by rw [Fintype.card_subtype, Fintype.card_subtype, h c])
  let τ : Equiv.Perm (Fin n) := (Equiv.sigmaFiberEquiv p).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv ψ))
  exact ⟨τ, fun v => (e (p v) ⟨v, rfl⟩).2⟩

/-- The image of a set under a permutation. -/
def img (σ : Equiv.Perm (Fin n)) (A : Finset (Fin n)) : Finset (Fin n) := A.map σ.toEmbedding

@[simp] lemma mem_img {σ : Equiv.Perm (Fin n)} {A : Finset (Fin n)} {v : Fin n} :
    v ∈ img σ A ↔ σ.symm v ∈ A := by
  simp only [img, mem_map_equiv]

lemma img_mul (σ τ : Equiv.Perm (Fin n)) (A : Finset (Fin n)) :
    img (τ * σ) A = img τ (img σ A) := by
  ext v; simp [Equiv.Perm.mul_def, Equiv.symm_trans_apply]

lemma img_one (A : Finset (Fin n)) : img (1 : Equiv.Perm (Fin n)) A = A := by
  ext v; rw [mem_img]; exact Iff.rfl

lemma card_img (σ : Equiv.Perm (Fin n)) (A : Finset (Fin n)) : (img σ A).card = A.card := by
  simp [img]

lemma img_inter (σ : Equiv.Perm (Fin n)) (A A' : Finset (Fin n)) :
    img σ (A ∩ A') = img σ A ∩ img σ A' := by
  ext v; simp

/-- The colouring recording a pair of sets. -/
def pcol (A A' : Finset (Fin n)) (v : Fin n) : Fin 4 :=
  if v ∈ A then (if v ∈ A' then 2 else 0) else (if v ∈ A' then 1 else 3)

lemma pcol_card (A A' : Finset (Fin n)) (c : Fin 4) :
    ((univ : Finset (Fin n)).filter (fun v => pcol A A' v = c)).card =
      if c = 0 then (A \ A').card else if c = 1 then (A' \ A).card else
      if c = 2 then (A ∩ A').card else (univ \ (A ∪ A')).card := by
  classical
  fin_cases c <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, ↓reduceIte,
    Fin.reduceEq] <;> congr 1 <;> ext v <;> rw [mem_filter] <;> by_cases h1 : v ∈ A <;>
    by_cases h2 : v ∈ A' <;> simp [pcol, h1, h2]

/-- The ordered pairs of sets with the same sizes and intersection size as `(A, A')`. -/
noncomputable def Pj (A A' : Finset (Fin n)) : Finset (Finset (Fin n) × Finset (Fin n)) := by
  classical
  exact univ.filter (fun P => P.1.card = A.card ∧ P.2.card = A'.card ∧
    (P.1 ∩ P.2).card = (A ∩ A').card)

lemma mem_Pj {A A' : Finset (Fin n)} {P : Finset (Fin n) × Finset (Fin n)} :
    P ∈ Pj A A' ↔ P.1.card = A.card ∧ P.2.card = A'.card ∧ (P.1 ∩ P.2).card = (A ∩ A').card := by
  classical
  simp [Pj]

lemma img_mem_Pj (σ : Equiv.Perm (Fin n)) (A A' : Finset (Fin n)) :
    (img σ A, img σ A') ∈ Pj A A' := by
  rw [mem_Pj]
  refine ⟨card_img _ _, card_img _ _, ?_⟩
  simp only; rw [← img_inter, card_img]

/-- For a pair in `Pj A A'` there is a permutation carrying `(A, A')` to it. -/
lemma exists_perm_pair {A A' : Finset (Fin n)} {P : Finset (Fin n) × Finset (Fin n)}
    (hP : P ∈ Pj A A') : ∃ τ : Equiv.Perm (Fin n), img τ A = P.1 ∧ img τ A' = P.2 := by
  classical
  rw [mem_Pj] at hP
  obtain ⟨h1, h2, h3⟩ := hP
  have hc : ∀ c, ((univ : Finset (Fin n)).filter (fun v => pcol A A' v = c)).card =
      ((univ : Finset (Fin n)).filter (fun v => pcol P.1 P.2 v = c)).card := by
    intro c
    rw [pcol_card, pcol_card]
    have e1 : (A \ A').card = A.card - (A ∩ A').card := by
      rw [card_sdiff]; congr 1; rw [inter_comm]
    have e2 : (A' \ A).card = A'.card - (A ∩ A').card := by
      rw [card_sdiff]
    have f1 : (P.1 \ P.2).card = P.1.card - (P.1 ∩ P.2).card := by
      rw [card_sdiff]; congr 1; rw [inter_comm]
    have f2 : (P.2 \ P.1).card = P.2.card - (P.1 ∩ P.2).card := by
      rw [card_sdiff]
    have g1 : (univ \ (A ∪ A')).card = n - (A.card + A'.card - (A ∩ A').card) := by
      rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
      have := card_union_add_card_inter A A'; congr 1; omega
    have g2 : (univ \ (P.1 ∪ P.2)).card = n - (P.1.card + P.2.card - (P.1 ∩ P.2).card) := by
      rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
      have := card_union_add_card_inter P.1 P.2; congr 1; omega
    split_ifs
    · rw [e1, f1, h1, h3]
    · rw [e2, f2, h2, h3]
    · exact h3.symm
    · rw [g1, g2, h1, h2, h3]
  obtain ⟨τ, hτ⟩ := exists_perm_of_fibres (pcol A A') (pcol P.1 P.2) hc
  refine ⟨τ, ?_, ?_⟩
  · ext v
    rw [mem_img]
    have := hτ (τ.symm v)
    simp only [Equiv.apply_symm_apply, pcol] at this
    by_contra hne
    split_ifs at this <;> simp_all
  · ext v
    rw [mem_img]
    have := hτ (τ.symm v)
    simp only [Equiv.apply_symm_apply, pcol] at this
    by_contra hne
    split_ifs at this <;> simp_all

lemma img_symm_of {τ : Equiv.Perm (Fin n)} {A B : Finset (Fin n)} (h : img τ A = B) :
    img τ⁻¹ B = A := by
  rw [← h, ← img_mul]; simp [img_one]

/-- **Averaging over permutations.** -/
theorem perm_avg (A A' : Finset (Fin n)) (g : Finset (Fin n) × Finset (Fin n) → ℕ) :
    (∑ σ : Equiv.Perm (Fin n), g (img σ A, img σ A')) * (Pj A A').card =
      Fintype.card (Equiv.Perm (Fin n)) * ∑ P ∈ Pj A A', g P := by
  classical
  set fib : Finset (Fin n) × Finset (Fin n) → Finset (Equiv.Perm (Fin n)) :=
    fun P => univ.filter (fun σ => (img σ A, img σ A') = P) with hfib
  set K := (fib (A, A')).card with hK
  have hconst : ∀ P ∈ Pj A A', (fib P).card = K := by
    intro P hP
    obtain ⟨τ, h1, h2⟩ := exists_perm_pair hP
    symm
    apply card_bij (fun σ _ => τ * σ)
    · intro σ hσ
      simp only [hfib, mem_filter, mem_univ, true_and, Prod.mk.injEq] at hσ ⊢
      rw [img_mul, img_mul, hσ.1, hσ.2]
      exact Prod.ext h1 h2
    · intro σ _ σ' _ h; exact mul_left_cancel h
    · intro σ' hσ'
      refine ⟨τ⁻¹ * σ', ?_, by simp⟩
      simp only [hfib, mem_filter, mem_univ, true_and, Prod.mk.injEq] at hσ' ⊢
      rw [img_mul, img_mul]
      have e1 : img σ' A = P.1 := by rw [← hσ']
      have e2 : img σ' A' = P.2 := by rw [← hσ']
      rw [e1, e2]
      exact ⟨img_symm_of h1, img_symm_of h2⟩
  have hmaps : ∀ σ ∈ (univ : Finset (Equiv.Perm (Fin n))), (img σ A, img σ A') ∈ Pj A A' :=
    fun σ _ => img_mem_Pj σ A A'
  have hsum : ∑ σ : Equiv.Perm (Fin n), g (img σ A, img σ A') = K * ∑ P ∈ Pj A A', g P := by
    rw [← sum_fiberwise_of_maps_to hmaps, mul_sum]
    apply sum_congr rfl
    intro P hP
    rw [← hconst P hP, card_eq_sum_ones, sum_mul, one_mul]
    apply sum_congr rfl
    intro σ hσ
    rw [(mem_filter.1 hσ).2]
  have hcard : Fintype.card (Equiv.Perm (Fin n)) = K * (Pj A A').card := by
    have := hsum.symm.trans rfl
    have h1 := sum_fiberwise_of_maps_to hmaps (fun _ => (1 : ℕ))
    rw [← card_univ, card_eq_sum_ones, ← h1]
    rw [mul_comm, card_eq_sum_ones, sum_mul, one_mul]
    apply sum_congr rfl
    intro P hP
    rw [← card_eq_sum_ones]
    exact hconst P hP
  rw [hsum, hcard]; ring

/-! ## Common links of disjoint sets and the cleaning function -/

open scoped Classical in
/-- `CN_G(S, S')`: sets `T` disjoint from `S ∪ S'` with `S ∪ T, S' ∪ T ∈ G`. -/
noncomputable def CNG (G : Finset (Finset (Fin n))) (S S' : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  univ.filter (fun T => Disjoint T S ∧ Disjoint T S' ∧ S ∪ T ∈ G ∧ S' ∪ T ∈ G)

lemma mem_CNG {G : Finset (Finset (Fin n))} {S S' T : Finset (Fin n)} :
    T ∈ CNG G S S' ↔ Disjoint T S ∧ Disjoint T S' ∧ S ∪ T ∈ G ∧ S' ∪ T ∈ G := by
  classical
  simp [CNG]

/-- A family of sets with a common vertex. -/
def StarF (F : Finset (Finset (Fin n))) : Prop := ∃ c, ∀ T ∈ F, c ∈ T

open scoped Classical in
/-- The chosen centre of `CN_G(S, S')` (arbitrary if it is not a star). -/
noncomputable def frc (G : Finset (Finset (Fin n))) (h0 : Fin n) (S S' : Finset (Fin n)) : Fin n :=
  if h : StarF (CNG G S S') then h.choose else h0

lemma frc_spec {G : Finset (Finset (Fin n))} (h0 : Fin n) {S S' : Finset (Fin n)}
    (h : StarF (CNG G S S')) : ∀ T ∈ CNG G S S', frc G h0 S S' ∈ T := by
  classical
  rw [frc, dif_pos h]; exact h.choose_spec

/-- Common links of disjoint nonempty sets are intersecting. -/
lemma CNG_intersecting {G : Finset (Finset (Fin n))} (hR : ¬ G.HasRepeatedDisjointUnion)
    {S S' : Finset (Fin n)} (hSS' : Disjoint S S') (hS : S.Nonempty) (hS' : S'.Nonempty)
    {T T' : Finset (Fin n)} (hT : T ∈ CNG G S S') (hT' : T' ∈ CNG G S S') (hTne : T.Nonempty) :
    (T ∩ T').Nonempty := by
  classical
  rw [mem_CNG] at hT hT'
  obtain ⟨d1, d2, g1, g2⟩ := hT
  obtain ⟨d1', d2', g1', g2'⟩ := hT'
  by_contra hdis
  rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at hdis
  obtain ⟨a, ha⟩ := hS
  obtain ⟨b, hb⟩ := hS'
  obtain ⟨c, hc⟩ := hTne
  have hab : a ∉ S' := disjoint_left.1 hSS' ha
  have hba : b ∉ S := disjoint_right.1 hSS' hb
  have hcS : c ∉ S := disjoint_left.1 d1 hc
  have hcS' : c ∉ S' := disjoint_left.1 d2 hc
  have hcT' : c ∉ T' := disjoint_left.1 hdis hc
  have haT : a ∉ T := disjoint_right.1 d1 ha
  have haT' : a ∉ T' := disjoint_right.1 d1' ha
  have hbT' : b ∉ T' := disjoint_right.1 d2' hb
  apply hR
  refine ⟨S ∪ T, g1, S' ∪ T', g2', S ∪ T', g1', S' ∪ T, g2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
    exact ⟨⟨hSS', d1'.symm⟩, ⟨d2, hdis⟩⟩
  · rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
    exact ⟨⟨hSS', d1.symm⟩, ⟨d2', hdis.symm⟩⟩
  · ext v; simp only [mem_union]; tauto
  · exact ne_of_mem_not_mem (mem_union_left _ ha) (by simp [hab, haT'])
  · exact ne_of_mem_not_mem (mem_union_left _ ha) (by simp [hab, haT])
  · exact ne_of_mem_not_mem (mem_union_right _ hc) (by simp [hcS, hcT'])
  · exact ne_of_mem_not_mem (mem_union_left _ ha) (by simp [hab, haT])
  · exact ne_of_mem_not_mem (mem_union_left _ hb) (by simp [hba, hbT'])
  · exact (ne_of_mem_not_mem (mem_union_right _ hc) (by simp [hcS', hcT'])).symm

/-! ## Crude counting -/

lemma card_supersets_le' (k : ℕ) (T : Finset (Fin n)) :
    ((univ.powersetCard k).filter (fun S : Finset (Fin n) => T ⊆ S)).card ≤
      n ^ (k - T.card) := by
  classical
  calc ((univ.powersetCard k).filter (fun S : Finset (Fin n) => T ⊆ S)).card
      ≤ (univ.powersetCard (k - T.card) : Finset (Finset (Fin n))).card := by
        apply card_le_card_of_injOn (fun S => S \ T)
        · intro S hS
          rw [mem_coe, mem_filter, mem_powersetCard] at hS
          rw [mem_coe, mem_powersetCard]
          refine ⟨subset_univ _, ?_⟩
          rw [card_sdiff_of_subset hS.2, hS.1.2]
        · intro S hS S' hS' h
          rw [mem_coe, mem_filter, mem_powersetCard] at hS hS'
          have h' : S \ T = S' \ T := h
          rw [← sdiff_union_of_subset hS.2, ← sdiff_union_of_subset hS'.2, h']
    _ = n.choose (k - T.card) := by simp
    _ ≤ n ^ (k - T.card) := Nat.choose_le_pow _ _

/-- A nonstar intersecting family of `q`-sets has at most `q² n^(q-2)` members. -/
lemma nonstar_card {q : ℕ} (F : Finset (Finset (Fin n))) (hcard : ∀ T ∈ F, T.card = q)
    (hint : ∀ T ∈ F, ∀ T' ∈ F, (T ∩ T').Nonempty) (hns : ¬ StarF F) :
    F.card ≤ q * q * n ^ (q - 2) := by
  classical
  rcases F.eq_empty_or_nonempty with he | ⟨T1, hT1⟩
  · rw [he]; simp
  simp only [StarF, not_exists, not_forall, exists_prop] at hns
  choose! T2 hT2 hT2' using hns
  have hsub : F ⊆ T1.biUnion (fun a => (T2 a).biUnion (fun b =>
      (univ.powersetCard q).filter (fun T : Finset (Fin n) => ({a, b} : Finset (Fin n)) ⊆ T))) := by
    intro T hT
    obtain ⟨a, ha⟩ := hint T hT T1 hT1
    obtain ⟨b, hb⟩ := hint T hT (T2 a) (hT2 a)
    rw [mem_inter] at ha hb
    refine mem_biUnion.2 ⟨a, ha.2, mem_biUnion.2 ⟨b, hb.2, mem_filter.2 ⟨?_, ?_⟩⟩⟩
    · exact mem_powersetCard.2 ⟨subset_univ _, hcard T hT⟩
    · intro z hz; simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl
      exacts [ha.1, hb.1]
  calc F.card ≤ _ := card_le_card hsub
    _ ≤ ∑ a ∈ T1, ((T2 a).biUnion (fun b => (univ.powersetCard q).filter
          (fun T : Finset (Fin n) => ({a, b} : Finset (Fin n)) ⊆ T))).card := card_biUnion_le
    _ ≤ ∑ _a ∈ T1, q * n ^ (q - 2) := by
        apply sum_le_sum
        intro a _
        calc _ ≤ ∑ b ∈ T2 a, ((univ.powersetCard q).filter
              (fun T : Finset (Fin n) => ({a, b} : Finset (Fin n)) ⊆ T)).card := card_biUnion_le
          _ ≤ ∑ _b ∈ T2 a, n ^ (q - 2) := by
              apply sum_le_sum
              intro b hb
              have hab : a ≠ b := fun h => hT2' a (h ▸ hb)
              have := card_supersets_le' q ({a, b} : Finset (Fin n))
              rwa [card_pair hab] at this
          _ = q * n ^ (q - 2) := by rw [sum_const, smul_eq_mul, hcard _ (hT2 a)]
    _ = q * q * n ^ (q - 2) := by rw [sum_const, smul_eq_mul, hcard _ hT1, mul_assoc]

/-! ## The cleaning cost of a pair -/

open scoped Classical in
/-- Vertex set of a `Y`-pair. -/
noncomputable def vset (e : Sym2 (Fin n)) : Finset (Fin n) := univ.filter (· ∈ e)

lemma vset_mk (u v : Fin n) : vset s(u, v) = {u, v} := by
  classical
  ext z; simp [vset]

open scoped Classical in
/-- The edges deleted for the pair `(B₁, B₂)`. -/
noncomputable def gam (G : Finset (Finset (Fin n))) (h0 : Fin n) (B₁ B₂ : Finset (Fin n)) : ℕ :=
  (univ.filter (fun e : Sym2 (Fin n) => PEdge G B₁ e ∧ PEdge G B₂ e ∧
    frc G h0 (B₁ \ B₂) (B₂ \ B₁) ∉ e ∧ frc G h0 (B₁ \ B₂) (B₂ \ B₁) ∉ B₁ ∩ B₂)).card

open scoped Classical in
/-- The cleaning cost of a pair is at most the number of non-star common links through `B₁ ∩ B₂`. -/
lemma gam_le (G : Finset (Finset (Fin n))) (h0 : Fin n) (B₁ B₂ : Finset (Fin n)) :
    gam G h0 B₁ B₂ ≤ ((if StarF (CNG G (B₁ \ B₂) (B₂ \ B₁)) then ∅ else
      CNG G (B₁ \ B₂) (B₂ \ B₁)).filter (fun R => B₁ ∩ B₂ ⊆ R)).card := by
  set f := frc G h0 (B₁ \ B₂) (B₂ \ B₁)
  apply card_le_card_of_injOn (fun e => (B₁ ∩ B₂) ∪ vset e)
  · intro e he
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at he
    obtain ⟨h1, h2, hf1, hf2⟩ := he
    obtain ⟨u, v, rfl, huv, hu1, hv1, hG1⟩ := h1
    obtain ⟨-, hu2, hv2, hG2⟩ := PEdge_mk.1 h2
    show B₁ ∩ B₂ ∪ vset s(u, v) ∈ _
    rw [vset_mk]
    have hmem : (B₁ ∩ B₂) ∪ {u, v} ∈ CNG G (B₁ \ B₂) (B₂ \ B₁) := by
      rw [mem_CNG]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [disjoint_left]; intro z hz hz'
        simp only [mem_union, mem_inter, mem_insert, mem_singleton, mem_sdiff] at hz hz'
        rcases hz with h | rfl | rfl <;> simp_all
      · rw [disjoint_left]; intro z hz hz'
        simp only [mem_union, mem_inter, mem_insert, mem_singleton, mem_sdiff] at hz hz'
        rcases hz with h | rfl | rfl <;> simp_all
      · convert hG1 using 1; ext z; simp only [mem_union, mem_sdiff, mem_inter, mem_insert,
          mem_singleton]; tauto
      · convert hG2 using 1; ext z; simp only [mem_union, mem_sdiff, mem_inter, mem_insert,
          mem_singleton]; tauto
    rw [mem_coe, mem_filter]
    refine ⟨?_, subset_union_left⟩
    split_ifs with hst
    · exfalso
      have := frc_spec h0 hst _ hmem
      simp only [mem_union, mem_insert, mem_singleton] at this
      rcases this with h | h | h
      · exact hf2 h
      · exact hf1 (h ▸ Sym2.mem_mk_left _ _)
      · exact hf1 (h ▸ Sym2.mem_mk_right _ _)
    · exact hmem
  · intro e he e' he' h
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at he he'
    obtain ⟨u, v, rfl, -, hu1, hv1, -⟩ := he.1
    obtain ⟨u', v', rfl, -, hu1', hv1', -⟩ := he'.1
    simp only [vset_mk] at h
    have key : ∀ z, z ∈ ({u, v} : Finset (Fin n)) ↔ z ∈ ({u', v'} : Finset (Fin n)) := by
      intro z
      have hz := congrArg (z ∈ ·) h
      simp only [mem_union, mem_inter, eq_iff_iff] at hz
      constructor
      · intro hm
        have : z ∉ B₁ := by simp only [mem_insert, mem_singleton] at hm; rcases hm with rfl | rfl
                                <;> assumption
        rcases hz.1 (Or.inr hm) with h | h
        · exact absurd h.1 this
        · exact h
      · intro hm
        have : z ∉ B₁ := by simp only [mem_insert, mem_singleton] at hm; rcases hm with rfl | rfl
                                <;> assumption
        rcases hz.2 (Or.inr hm) with h | h
        · exact absurd h.1 this
        · exact h
    have hu := (key u).1 (by simp)
    have hv := (key v).1 (by simp)
    have hu' := (key u').2 (by simp)
    simp only [mem_insert, mem_singleton] at hu hv hu'
    rw [Sym2.eq_iff]
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp_all

/-! ## Reindexing pairs by `(S, S', J)` -/

open scoped Classical in
/-- Ordered pairs of disjoint `k'`-sets. -/
noncomputable def Dk (k' : ℕ) : Finset (Finset (Fin n) × Finset (Fin n)) :=
  univ.filter (fun SS => SS.1.card = k' ∧ SS.2.card = k' ∧ Disjoint SS.1 SS.2)

lemma un_sdiff {S S' J : Finset (Fin n)} (hd : Disjoint S S') (hJ1 : Disjoint J S)
    (hJ2 : Disjoint J S') : (S ∪ J) \ (S' ∪ J) = S := by
  ext z; simp only [mem_sdiff, mem_union, not_or]
  constructor
  · rintro ⟨h | h, -, hn⟩
    · exact h
    · exact absurd h hn
  · intro h
    exact ⟨Or.inl h, fun h' => disjoint_left.1 hd h h', fun h' => disjoint_left.1 hJ1 h' h⟩

lemma un_inter {S S' J : Finset (Fin n)} (hd : Disjoint S S') :
    (S ∪ J) ∩ (S' ∪ J) = J := by
  ext z; simp only [mem_inter, mem_union]
  constructor
  · rintro ⟨h | h, h' | h'⟩
    · exact absurd h' (disjoint_left.1 hd h)
    · exact h'
    · exact h
    · exact h
  · intro h; exact ⟨Or.inr h, Or.inr h⟩

lemma disj_of_sub_compl {S S' J : Finset (Fin n)} (h : J ⊆ univ \ (S ∪ S')) :
    Disjoint J S ∧ Disjoint J S' := by
  have key : ∀ z ∈ J, z ∉ S ∧ z ∉ S' := by
    intro z hz
    have := h hz
    simp only [mem_sdiff, mem_univ, true_and, mem_union, not_or] at this
    exact this
  exact ⟨disjoint_left.2 (fun z hz => (key z hz).1), disjoint_left.2 (fun z hz => (key z hz).2)⟩

lemma sum_Pj_eq {A A' : Finset (Fin n)} (hAA' : A.card = A'.card)
    (f : Finset (Fin n) × Finset (Fin n) → ℕ) :
    ∑ P ∈ Pj A A', f P = ∑ SS ∈ Dk (A \ A').card, ∑ J ∈ (univ \ (SS.1 ∪ SS.2)).powersetCard
      (A ∩ A').card, f (SS.1 ∪ J, SS.2 ∪ J) := by
  classical
  have hk1 : (A \ A').card + (A ∩ A').card = A.card := card_sdiff_add_card_inter A A'
  have hk2 : (A' \ A).card + (A ∩ A').card = A'.card := by
    rw [inter_comm]; exact card_sdiff_add_card_inter A' A
  rw [sum_sigma']
  symm
  refine sum_bij' (fun x _ => (x.1.1 ∪ x.2, x.1.2 ∪ x.2))
    (fun P _ => ⟨(P.1 \ P.2, P.2 \ P.1), P.1 ∩ P.2⟩) (fun x hx => ?_) (fun P hP => ?_)
    (fun x hx => ?_) (fun P hP => ?_) (fun x _ => rfl)
  · rw [mem_sigma] at hx
    obtain ⟨hSS, hJ⟩ := hx
    rw [Dk, mem_filter] at hSS
    obtain ⟨-, h1, h2, hd⟩ := hSS
    rw [mem_powersetCard] at hJ
    obtain ⟨hJs, hJc⟩ := hJ
    obtain ⟨hJ1, hJ2⟩ := disj_of_sub_compl hJs
    rw [mem_Pj]
    refine ⟨?_, ?_, ?_⟩
    · show (x.1.1 ∪ x.2).card = A.card
      rw [card_union_of_disjoint hJ1.symm, h1, hJc]; omega
    · show (x.1.2 ∪ x.2).card = A'.card
      rw [card_union_of_disjoint hJ2.symm, h2, hJc]; omega
    · show ((x.1.1 ∪ x.2) ∩ (x.1.2 ∪ x.2)).card = _
      rw [un_inter hd, hJc]
  · rw [mem_Pj] at hP
    obtain ⟨h1, h2, h3⟩ := hP
    have c1 : (P.1 \ P.2).card = P.1.card - (P.1 ∩ P.2).card := by
      rw [card_sdiff]; congr 1; rw [inter_comm]
    have c2 : (P.2 \ P.1).card = P.2.card - (P.1 ∩ P.2).card := by rw [card_sdiff]
    rw [mem_sigma]
    refine ⟨?_, ?_⟩
    · rw [Dk, mem_filter]
      refine ⟨mem_univ _, ?_, ?_, ?_⟩
      · show (P.1 \ P.2).card = _; rw [c1, h1, h3]; omega
      · show (P.2 \ P.1).card = _; rw [c2, h2, h3]; omega
      · show Disjoint (P.1 \ P.2) (P.2 \ P.1)
        rw [disjoint_left]; intro z hz hz'; rw [mem_sdiff] at hz hz'; exact hz.2 hz'.1
    · rw [mem_powersetCard]
      refine ⟨?_, h3⟩
      intro z hz
      rw [mem_inter] at hz
      simp only [mem_sdiff, mem_univ, true_and, mem_union, not_or]
      exact ⟨fun h => h.2 hz.2, fun h => h.2 hz.1⟩
  · rw [mem_sigma] at hx
    obtain ⟨hSS, hJ⟩ := hx
    rw [Dk, mem_filter] at hSS
    obtain ⟨-, -, -, hd⟩ := hSS
    obtain ⟨hJ1, hJ2⟩ := disj_of_sub_compl (mem_powersetCard.1 hJ).1
    have e1 := un_sdiff hd hJ1 hJ2
    have e2 := un_sdiff hd.symm hJ2 hJ1
    have e3 := un_inter (J := x.2) hd
    simp only [e1, e2, e3]
  · ext1
    · show P.1 \ P.2 ∪ P.1 ∩ P.2 = P.1
      exact sdiff_union_inter P.1 P.2
    · show P.2 \ P.1 ∪ P.1 ∩ P.2 = P.2
      rw [inter_comm]; exact sdiff_union_inter P.2 P.1

/-! ## Expected cleaning cost -/

lemma power_le_binomial' {n k : ℕ} (hn : 0 < n) (hlarge : 2 * k ≤ n) :
    n ^ k ≤ 2 ^ k * k.factorial * (n - 1).choose k := by
  have hbase : n ≤ 2 * (n - k) := by omega
  have hpow : (n - k) ^ k ≤ (n - 1).descFactorial k := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ n by omega)] using
      (n - 1).pow_sub_le_descFactorial k
  calc
    n ^ k ≤ (2 * (n - k)) ^ k := Nat.pow_le_pow_left hbase k
    _ = 2 ^ k * (n - k) ^ k := mul_pow _ _ _
    _ ≤ 2 ^ k * (n - 1).descFactorial k := Nat.mul_le_mul_left _ hpow
    _ = _ := by rw [Nat.descFactorial_eq_factorial_mul_choose, mul_assoc]

/-- `n^j ≤ 4^j j! C(m, j)` when `m` is at least half of `n` and `2j ≤ m`. -/
lemma pow_le_choose_of_half {n m j : ℕ} (hm : n ≤ 2 * m) (hj : 2 * j ≤ m) (hm0 : 0 < m) :
    n ^ j ≤ 4 ^ j * j.factorial * m.choose j := by
  have h1 := power_le_binomial' hm0 hj
  have h2 : (m - 1).choose j ≤ m.choose j := Nat.choose_le_choose j (Nat.sub_le m 1)
  calc n ^ j ≤ (2 * m) ^ j := Nat.pow_le_pow_left hm j
    _ = 2 ^ j * m ^ j := mul_pow _ _ _
    _ ≤ 2 ^ j * (2 ^ j * j.factorial * m.choose j) := by
        apply Nat.mul_le_mul_left
        calc m ^ j ≤ 2 ^ j * j.factorial * (m - 1).choose j := h1
          _ ≤ _ := Nat.mul_le_mul_left _ h2
    _ = 4 ^ j * j.factorial * m.choose j := by
        rw [show (4 : ℕ) ^ j = 2 ^ j * 2 ^ j by rw [← mul_pow]; norm_num]; ring

open scoped Classical in
lemma card_CNG_mem {G : Finset (Finset (Fin n))} {t : ℕ} (hGt : ∀ E ∈ G, E.card = t)
    {S S' T : Finset (Fin n)} (hT : T ∈ CNG G S S') : T.card = t - S.card := by
  rw [mem_CNG] at hT
  have := hGt _ hT.2.2.1
  rw [card_union_of_disjoint hT.1.symm] at this
  omega

/-- The constant in the expected cleaning cost. -/
def cG (t : ℕ) : ℕ := t * t * 2 ^ t * (4 ^ t * t.factorial)

open scoped Classical in
lemma Gamma_card {G : Finset (Finset (Fin n))} {t : ℕ} (hGt : ∀ E ∈ G, E.card = t)
    (hR : ¬ G.HasRepeatedDisjointUnion) {S S' : Finset (Fin n)} (hd : Disjoint S S')
    (hS : S.Nonempty) (hS' : S'.Nonempty) (hq : S.card < t) :
    (if StarF (CNG G S S') then ∅ else CNG G S S').card ≤
      (t - S.card) * (t - S.card) * n ^ (t - S.card - 2) := by
  split_ifs with hst
  · simp
  · apply nonstar_card _ (fun T hT => card_CNG_mem hGt hT) _ hst
    intro T hT T' hT'
    have hTc := card_CNG_mem hGt hT
    exact CNG_intersecting hR hd hS hS' hT hT' (by rw [← card_pos, hTc]; omega)

open scoped Classical in
/-- **Expected cleaning cost** of a compatible pair: `O(1)` on average over its pattern class. -/
theorem gam_sum {G : Finset (Finset (Fin n))} {t : ℕ} (ht : 4 ≤ t)
    (hGt : ∀ E ∈ G, E.card = t) (hR : ¬ G.HasRepeatedDisjointUnion) (h0 : Fin n)
    {A A' : Finset (Fin n)} (hA : A.card = t - 2) (hA' : A'.card = t - 2) (hne : A ≠ A')
    (hint : (A ∩ A').Nonempty) (hn : 4 * t ≤ n) :
    ∑ P ∈ Pj A A', gam G h0 P.1 P.2 ≤ cG t * (Pj A A').card := by
  have hAA : A.card = A'.card := by rw [hA, hA']
  have hk1 : (A \ A').card + (A ∩ A').card = A.card := card_sdiff_add_card_inter A A'
  have hk'pos : 0 < (A \ A').card := by
    rw [card_pos]
    by_contra h
    rw [not_nonempty_iff_eq_empty, sdiff_eq_empty_iff_subset] at h
    exact hne (eq_of_subset_of_card_le h (by omega))
  have hjpos : 0 < (A ∩ A').card := card_pos.2 hint
  set k' := (A \ A').card with hk'
  set j := (A ∩ A').card with hj
  rw [sum_Pj_eq hAA, show (Pj A A').card = ∑ P ∈ Pj A A', 1 from card_eq_sum_ones _,
    sum_Pj_eq hAA (fun _ => 1), mul_sum]
  apply sum_le_sum
  intro SS hSS
  rw [Dk, mem_filter] at hSS
  obtain ⟨-, h1, h2, hd⟩ := hSS
  have hS : SS.1.Nonempty := by rw [← card_pos, h1]; exact hk'pos
  have hS' : SS.2.Nonempty := by rw [← card_pos, h2]; exact hk'pos
  set PC := (univ \ (SS.1 ∪ SS.2)).powersetCard j with hPC
  set Γs := if StarF (CNG G SS.1 SS.2) then ∅ else CNG G SS.1 SS.2 with hΓs
  have step1 : ∀ J ∈ PC, gam G h0 (SS.1 ∪ J) (SS.2 ∪ J) ≤ (Γs.filter (fun R => J ⊆ R)).card := by
    intro J hJ
    obtain ⟨hJ1, hJ2⟩ := disj_of_sub_compl (mem_powersetCard.1 hJ).1
    have := gam_le G h0 (SS.1 ∪ J) (SS.2 ∪ J)
    rwa [un_sdiff hd hJ1 hJ2, un_sdiff hd.symm hJ2 hJ1, un_inter hd] at this
  have step2 : ∑ J ∈ PC, (Γs.filter (fun R => J ⊆ R)).card =
      ∑ R ∈ Γs, (PC.filter (fun J => J ⊆ R)).card := by
    simp_rw [card_filter]
    exact sum_comm
  have step3 : ∀ R ∈ Γs, (PC.filter (fun J => J ⊆ R)).card ≤ 2 ^ t := by
    intro R hR'
    have hRc : R.card = t - k' := by
      have hRm : R ∈ CNG G SS.1 SS.2 := by
        rw [hΓs] at hR'; split_ifs at hR' with h
        · simp at hR'
        · exact hR'
      rw [card_CNG_mem hGt hRm, h1]
    calc (PC.filter (fun J => J ⊆ R)).card ≤ (R.powersetCard j).card := by
          apply card_le_card
          intro J hJ
          rw [mem_filter, mem_powersetCard] at hJ
          exact mem_powersetCard.2 ⟨hJ.2, hJ.1.2⟩
      _ = R.card.choose j := card_powersetCard _ _
      _ ≤ 2 ^ R.card := Nat.choose_le_two_pow _ _
      _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hΓc : Γs.card ≤ t * t * n ^ j := by
    have := Gamma_card hGt hR hd hS hS' (by rw [h1]; omega)
    rw [h1] at this
    have e1 : t - k' - 2 = j := by omega
    rw [e1] at this
    calc Γs.card ≤ (t - k') * (t - k') * n ^ j := this
      _ ≤ t * t * n ^ j := by gcongr <;> omega
  have hPCc : PC.card = (n - 2 * k').choose j := by
    rw [hPC, card_powersetCard, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin,
      card_union_of_disjoint hd, h1, h2]
    congr 1; omega
  have hbin : n ^ j ≤ 4 ^ t * t.factorial * PC.card := by
    rw [hPCc]
    have := pow_le_choose_of_half (n := n) (m := n - 2 * k') (j := j) (by omega) (by omega)
      (by omega)
    calc n ^ j ≤ 4 ^ j * j.factorial * (n - 2 * k').choose j := this
      _ ≤ 4 ^ t * t.factorial * (n - 2 * k').choose j := by
          apply Nat.mul_le_mul_right
          apply Nat.mul_le_mul
          · exact Nat.pow_le_pow_right (by norm_num) (by omega)
          · exact Nat.factorial_le (by omega)
  calc ∑ J ∈ PC, gam G h0 (SS.1 ∪ J) (SS.2 ∪ J) ≤ ∑ J ∈ PC, (Γs.filter (fun R => J ⊆ R)).card :=
        sum_le_sum step1
    _ = ∑ R ∈ Γs, (PC.filter (fun J => J ⊆ R)).card := step2
    _ ≤ ∑ _R ∈ Γs, 2 ^ t := sum_le_sum step3
    _ = Γs.card * 2 ^ t := by rw [sum_const, smul_eq_mul]
    _ ≤ t * t * n ^ j * 2 ^ t := Nat.mul_le_mul_right _ hΓc
    _ ≤ t * t * (4 ^ t * t.factorial * PC.card) * 2 ^ t := by gcongr
    _ = cG t * ∑ _J ∈ PC, 1 := by rw [cG, ← card_eq_sum_ones]; ring

/-! ## Expected exceptional pairs -/

lemma card_powersetCard_mem {U : Finset (Fin n)} {f : Fin n} (hf : f ∈ U) {j : ℕ} (hj : 1 ≤ j) :
    ((U.powersetCard j).filter (fun J => f ∈ J)).card * U.card = j * (U.powersetCard j).card := by
  classical
  have hc : ((U.powersetCard j).filter (fun J => f ∈ J)).card =
      ((U.erase f).powersetCard (j - 1)).card := by
    symm
    apply card_bij (fun J _ => insert f J)
    · intro J hJ
      rw [mem_powersetCard] at hJ
      rw [mem_filter, mem_powersetCard]
      have hfJ : f ∉ J := fun h => by have := hJ.1 h; simp at this
      refine ⟨⟨insert_subset hf (hJ.1.trans (erase_subset _ _)), ?_⟩, mem_insert_self _ _⟩
      rw [card_insert_of_notMem hfJ, hJ.2]; omega
    · intro J hJ J' hJ' h
      have hfJ : f ∉ J := fun h' => by have := (mem_powersetCard.1 hJ).1 h'; simp at this
      have hfJ' : f ∉ J' := fun h' => by have := (mem_powersetCard.1 hJ').1 h'; simp at this
      rw [← erase_insert hfJ, ← erase_insert hfJ', h]
    · intro J hJ
      rw [mem_filter, mem_powersetCard] at hJ
      refine ⟨J.erase f, ?_, insert_erase hJ.2⟩
      rw [mem_powersetCard]
      exact ⟨erase_subset_erase _ hJ.1.1, by rw [card_erase_of_mem hJ.2, hJ.1.2]⟩
  rw [hc, card_powersetCard, card_powersetCard, card_erase_of_mem hf]
  obtain ⟨m, hm⟩ : ∃ m, U.card = m + 1 := ⟨U.card - 1, by
    have := card_pos.2 ⟨f, hf⟩; omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rw [hm]
  simp only [Nat.add_sub_cancel]
  have := Nat.add_one_mul_choose_eq m j'; linarith

open scoped Classical in
/-- **Expected exceptional pairs**: the centre lands in the intersection with probability
`≤ j/(n - 2k')`. -/
theorem alph_sum {G : Finset (Finset (Fin n))} (h0 : Fin n) {A A' : Finset (Fin n)}
    (hAA : A.card = A'.card) (hint : (A ∩ A').Nonempty) :
    (∑ P ∈ Pj A A', if frc G h0 (P.1 \ P.2) (P.2 \ P.1) ∈ P.1 ∩ P.2 then 1 else 0) *
      (n - 2 * (A \ A').card) ≤ (A ∩ A').card * (Pj A A').card := by
  have hjpos : 1 ≤ (A ∩ A').card := card_pos.2 hint
  rw [sum_Pj_eq hAA, show (Pj A A').card = ∑ P ∈ Pj A A', 1 from card_eq_sum_ones _,
    sum_Pj_eq hAA (fun _ => 1), mul_sum, sum_mul]
  apply sum_le_sum
  intro SS hSS
  rw [Dk, mem_filter] at hSS
  obtain ⟨-, h1, h2, hd⟩ := hSS
  set U := univ \ (SS.1 ∪ SS.2)
  have hU : U.card = n - 2 * (A \ A').card := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin,
      card_union_of_disjoint hd, h1, h2]; ring_nf
  set f := frc G h0 SS.1 SS.2
  have hrw : ∀ J ∈ U.powersetCard (A ∩ A').card,
      (if frc G h0 ((SS.1 ∪ J, SS.2 ∪ J).1 \ (SS.1 ∪ J, SS.2 ∪ J).2)
        ((SS.1 ∪ J, SS.2 ∪ J).2 \ (SS.1 ∪ J, SS.2 ∪ J).1) ∈
        (SS.1 ∪ J, SS.2 ∪ J).1 ∩ (SS.1 ∪ J, SS.2 ∪ J).2 then 1 else 0) =
      if f ∈ J then 1 else 0 := by
    intro J hJ
    obtain ⟨hJ1, hJ2⟩ := disj_of_sub_compl (mem_powersetCard.1 hJ).1
    simp only [un_sdiff hd hJ1 hJ2, un_sdiff hd.symm hJ2 hJ1, un_inter hd, f]
  rw [sum_congr rfl hrw, ← card_filter, ← hU, ← card_eq_sum_ones]
  by_cases hf : f ∈ U
  · rw [card_powersetCard_mem hf hjpos]
  · have : (U.powersetCard (A ∩ A').card).filter (fun J => f ∈ J) = ∅ := by
      rw [filter_eq_empty_iff]
      intro J hJ hfJ
      exact hf ((mem_powersetCard.1 hJ).1 hfJ)
    rw [this]; simp

/-! ## Expected degrees -/

open scoped Classical in
noncomputable def pdeg (G : Finset (Finset (Fin n))) (B : Finset (Fin n)) : ℕ :=
  (univ.filter (fun e => PEdge G B e)).card

open scoped Classical in
lemma sum_pdeg {G : Finset (Finset (Fin n))} {t : ℕ} (ht : 2 ≤ t) (hGt : ∀ E ∈ G, E.card = t) :
    G.card * t.choose 2 ≤ ∑ B ∈ (univ : Finset (Fin n)).powersetCard (t - 2), pdeg G B := by
  have hdom : (G.sigma (fun E => E.offDiag.image (fun p => s(p.1, p.2)))).card =
      G.card * t.choose 2 := by
    rw [card_sigma, sum_congr rfl (fun E hE => by
      rw [show (E.offDiag.image (fun p => s(p.1, p.2))) = E.offDiag.image Sym2.mk.uncurry from rfl,
        Sym2.card_image_offDiag, hGt E hE]), sum_const, smul_eq_mul]
  rw [← hdom]
  simp only [pdeg]
  rw [← card_sigma]
  apply card_le_card_of_injOn (fun x => ⟨x.1 \ vset x.2, x.2⟩)
  · intro x hx
    simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_image, mem_offDiag] at hx
    obtain ⟨hE, ⟨u, v⟩, ⟨hu, hv, huv⟩, he⟩ := hx
    simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_powersetCard, subset_univ, true_and,
      mem_filter, mem_univ]
    rw [← he, vset_mk]
    have hsub : ({u, v} : Finset (Fin n)) ⊆ x.1 := by
      intro z hz; simp only [mem_insert, mem_singleton] at hz; rcases hz with rfl | rfl <;> assumption
    refine ⟨?_, ?_⟩
    · rw [card_sdiff_of_subset hsub, card_pair huv, hGt _ hE]
    · rw [PEdge_mk]
      refine ⟨huv, by simp, by simp, ?_⟩
      convert hE using 1
      ext z; simp only [mem_insert, mem_sdiff, mem_singleton]
      constructor
      · rintro (rfl | rfl | ⟨h, -⟩) <;> assumption
      · intro h; by_cases h1 : z = u
        · exact Or.inl h1
        · by_cases h2 : z = v
          · exact Or.inr (Or.inl h2)
          · exact Or.inr (Or.inr ⟨h, by tauto⟩)
  · intro x hx y hy h
    simp only [Sigma.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h2' : x.2 = y.2 := eq_of_heq h2
    simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_image, mem_offDiag] at hx hy
    obtain ⟨-, ⟨u, v⟩, ⟨hu, hv, -⟩, he⟩ := hx
    obtain ⟨-, ⟨u', v'⟩, ⟨hu', hv', -⟩, he'⟩ := hy
    have hsub : vset x.2 ⊆ x.1 := by
      rw [← he, vset_mk]; intro z hz; simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    have hsub' : vset y.2 ⊆ y.1 := by
      rw [← he', vset_mk]; intro z hz; simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    have : x.1 = y.1 := by
      rw [← sdiff_union_of_subset hsub, ← sdiff_union_of_subset hsub', h1, h2']
    exact Sigma.ext this (heq_of_eq h2')

/-! ## Transversal blocks (replacing Baranyai's theorem) -/

section Blocks

variable {k q : ℕ}

/-- The point in row `i` and column `a`. -/
def pt (hkq : k * q ≤ n) (i : Fin k) (a : Fin q) : Fin n :=
  ⟨i.val * q + a.val, by
    have h1 : i.val * q + a.val < (i.val + 1) * q := by rw [add_mul, one_mul]; omega
    have h2 : (i.val + 1) * q ≤ k * q := Nat.mul_le_mul_right _ (by omega)
    omega⟩

lemma pt_inj (hkq : k * q ≤ n) {i i' : Fin k} {a a' : Fin q} (h : pt hkq i a = pt hkq i' a') : i = i' ∧ a = a' := by
  simp only [pt, Fin.mk.injEq] at h
  have ha : a.val < q := a.isLt
  have ha' : a'.val < q := a'.isLt
  have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le _) ha
  have h1 : (i.val * q + a.val) / q = i.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt ha, zero_add]
  have h2 : (i'.val * q + a'.val) / q = i'.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt ha', zero_add]
  have hi : i.val = i'.val := by rw [← h1, ← h2, h]
  refine ⟨Fin.ext hi, Fin.ext ?_⟩
  rw [hi] at h; omega

/-- The transversal of `x : Fin k → Fin q`. -/
def trv (hkq : k * q ≤ n) (x : Fin k → Fin q) : Finset (Fin n) := univ.image (fun i => pt hkq i (x i))

lemma mem_trv (hkq : k * q ≤ n) {x : Fin k → Fin q} {v : Fin n} : v ∈ trv hkq x ↔ ∃ i, pt hkq i (x i) = v := by
  simp [trv]

lemma trv_card (hkq : k * q ≤ n) (x : Fin k → Fin q) : (trv hkq x).card = k := by
  rw [trv, card_image_of_injective, card_univ, Fintype.card_fin]
  intro i i' h
  exact (pt_inj hkq h).1

lemma trv_meet (hkq : k * q ≤ n) {x y : Fin k → Fin q} (h : (trv hkq x ∩ trv hkq y).Nonempty) : ∃ i, x i = y i := by
  obtain ⟨v, hv⟩ := h
  rw [mem_inter, mem_trv, mem_trv] at hv
  obtain ⟨⟨i, hi⟩, ⟨i', hi'⟩⟩ := hv
  obtain ⟨h1, h2⟩ := pt_inj hkq (hi.trans hi'.symm)
  subst h1
  exact ⟨i, h2⟩

lemma trv_eq (hkq : k * q ≤ n) {x y : Fin k → Fin q} (h : trv hkq x = trv hkq y) : x = y := by
  funext i
  have : pt hkq i (x i) ∈ trv hkq y := h ▸ (mem_trv hkq).2 ⟨i, rfl⟩
  obtain ⟨i', hi'⟩ := (mem_trv hkq).1 this
  obtain ⟨h1, h2⟩ := pt_inj hkq hi'
  subst h1
  exact h2.symm

/-- The cyclic shift of a transversal pattern. -/
def shift (c : Fin k → Fin q) (s : Fin q) : Fin k → Fin q := fun i => c i + s

/-- Shifts of one pattern are pairwise disjoint transversals (a perfect matching). -/
lemma shift_disjoint (hkq : k * q ≤ n) {c : Fin k → Fin q} {s s' : Fin q} (hne : s ≠ s') :
    Disjoint (trv hkq (shift c s)) (trv hkq (shift c s')) := by
  rw [disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty]
  intro h
  obtain ⟨i, hi⟩ := trv_meet hkq h
  simp only [shift] at hi
  exact hne (add_left_cancel hi)

/-- The matching generated by a pattern. -/
def mat (hkq : k * q ≤ n) (c : Fin k → Fin q) : Finset (Finset (Fin n)) :=
  univ.image (fun s => trv hkq (shift c s))

lemma mat_card (hkq : k * q ≤ n) (c : Fin k → Fin q) (hk : 0 < k) : (mat hkq c).card = q := by
  rw [mat, card_image_of_injective, card_univ, Fintype.card_fin]
  intro s s' h
  have := congrFun (trv_eq hkq h) ⟨0, hk⟩
  simpa [shift] using this

/-- Patterns normalised to vanish in row `0`. -/
def Reps (hk : 0 < k) (hq : 0 < q) : Finset (Fin k → Fin q) :=
  univ.filter (fun c => c ⟨0, hk⟩ = ⟨0, hq⟩)

/-- Each member of a block determines its pattern. -/
lemma rep_unique (hkq : k * q ≤ n) (hk : 0 < k) (hq : 0 < q) {c c' : Fin k → Fin q}
    (hc : c ∈ Reps hk hq) (hc' : c' ∈ Reps hk hq) {A : Finset (Fin n)} (h1 : A ∈ mat hkq c)
    (h2 : A ∈ mat hkq c') : c = c' := by
  simp only [mat, mem_image, mem_univ, true_and] at h1 h2
  obtain ⟨s, rfl⟩ := h1
  obtain ⟨s', hs'⟩ := h2
  have h := trv_eq hkq hs'
  have h0 := congrFun h ⟨0, hk⟩
  simp only [Reps, mem_filter, mem_univ, true_and] at hc hc'
  simp only [shift, hc, hc'] at h0
  have hss : s' = s := add_left_cancel h0
  subst hss
  funext i
  have := congrFun h i
  simp only [shift] at this
  exact (add_right_cancel this).symm

lemma mat_compat (hkq : k * q ≤ n) {c : Fin k → Fin q} {A A' : Finset (Fin n)}
    (hA : A ∈ mat hkq c) (hA' : A' ∈ mat hkq c) : A = A' ∨ Disjoint A A' := by
  simp only [mat, mem_image, mem_univ, true_and] at hA hA'
  obtain ⟨s, rfl⟩ := hA
  obtain ⟨s', rfl⟩ := hA'
  by_cases h : s = s'
  · left; rw [h]
  · right; exact shift_disjoint hkq h

lemma reps_card_ge (hk : 0 < k) (hq : 0 < q) : q ^ (k - 1) ≤ (Reps hk hq).card := by
  classical
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  calc q ^ (k' + 1 - 1) = (univ : Finset (Fin k' → Fin q)).card := by simp
    _ ≤ (Reps hk hq).card := by
        apply card_le_card_of_injOn
          (fun y : Fin k' → Fin q => (Fin.cons ⟨0, hq⟩ y : Fin (k' + 1) → Fin q))
        · intro y _
          simp only [Reps, coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
          rfl
        · intro y _ y' _ h
          exact Fin.cons_right_injective _ h

/-- The `β`-th block: the matchings of `k` consecutive patterns. -/
noncomputable def blk (hkq : k * q ≤ n) (hk : 0 < k) (hq : 0 < q)
    (β : Fin ((Reps hk hq).card / k)) : Finset (Finset (Fin n)) :=
  (univ : Finset (Fin k)).biUnion (fun l => mat hkq ((Reps hk hq).equivFin.symm
    ⟨β.val * k + l.val, by
      have h1 : β.val * k + l.val < (β.val + 1) * k := by rw [add_mul, one_mul]; omega
      have h2 : (β.val + 1) * k ≤ (Reps hk hq).card / k * k := Nat.mul_le_mul_right _ (by omega)
      have h3 := Nat.div_mul_le_self (Reps hk hq).card k
      omega⟩).1)

lemma idx_inj {k N : ℕ} {β β' : Fin (N / k)} {l l' : Fin k} (h : β.val * k + l.val = β'.val * k + l'.val) :
    β = β' ∧ l = l' := by
  have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le _) l.isLt
  have h1 : (β.val * k + l.val) / k = β.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt l.isLt, zero_add]
  have h2 : (β'.val * k + l'.val) / k = β'.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt l'.isLt, zero_add]
  have hb : β.val = β'.val := by rw [← h1, ← h2, h]
  refine ⟨Fin.ext hb, Fin.ext ?_⟩
  rw [hb] at h; omega

lemma mem_blk {hkq : k * q ≤ n} {hk : 0 < k} {hq : 0 < q} {β : Fin ((Reps hk hq).card / k)}
    {A : Finset (Fin n)} : A ∈ blk hkq hk hq β ↔ ∃ l : Fin k, A ∈ mat hkq ((Reps hk hq).equivFin.symm
      ⟨β.val * k + l.val, by
        have h1 : β.val * k + l.val < (β.val + 1) * k := by rw [add_mul, one_mul]; omega
        have h2 : (β.val + 1) * k ≤ (Reps hk hq).card / k * k := Nat.mul_le_mul_right _ (by omega)
        have h3 := Nat.div_mul_le_self (Reps hk hq).card k
        omega⟩).1 := by
  simp [blk]

lemma blk_mem_card {hkq : k * q ≤ n} {hk : 0 < k} {hq : 0 < q} {β : Fin ((Reps hk hq).card / k)}
    {A : Finset (Fin n)} (hA : A ∈ blk hkq hk hq β) : A.card = k := by
  obtain ⟨l, hl⟩ := mem_blk.1 hA
  simp only [mat, mem_image, mem_univ, true_and] at hl
  obtain ⟨s, rfl⟩ := hl
  exact trv_card hkq _

lemma blk_rep_eq {hkq : k * q ≤ n} {hk : 0 < k} {hq : 0 < q} {β β' : Fin ((Reps hk hq).card / k)}
    {l l' : Fin k} {A : Finset (Fin n)}
    (h1 : A ∈ mat hkq ((Reps hk hq).equivFin.symm ⟨β.val * k + l.val, by
        have h1 : β.val * k + l.val < (β.val + 1) * k := by rw [add_mul, one_mul]; omega
        have h2 : (β.val + 1) * k ≤ (Reps hk hq).card / k * k := Nat.mul_le_mul_right _ (by omega)
        have h3 := Nat.div_mul_le_self (Reps hk hq).card k
        omega⟩).1)
    (h2 : A ∈ mat hkq ((Reps hk hq).equivFin.symm ⟨β'.val * k + l'.val, by
        have h1 : β'.val * k + l'.val < (β'.val + 1) * k := by rw [add_mul, one_mul]; omega
        have h2 : (β'.val + 1) * k ≤ (Reps hk hq).card / k * k := Nat.mul_le_mul_right _ (by omega)
        have h3 := Nat.div_mul_le_self (Reps hk hq).card k
        omega⟩).1) : β = β' ∧ l = l' := by
  have := rep_unique hkq hk hq (Subtype.mem _) (Subtype.mem _) h1 h2
  have h' := (Reps hk hq).equivFin.symm.injective (Subtype.ext this)
  simp only [Fin.mk.injEq] at h'
  exact idx_inj h'

lemma blk_disjoint {hkq : k * q ≤ n} {hk : 0 < k} {hq : 0 < q} {β β' : Fin ((Reps hk hq).card / k)}
    (hne : β ≠ β') : Disjoint (blk hkq hk hq β) (blk hkq hk hq β') := by
  rw [disjoint_left]
  intro A hA hA'
  obtain ⟨l, hl⟩ := mem_blk.1 hA
  obtain ⟨l', hl'⟩ := mem_blk.1 hA'
  exact hne (blk_rep_eq hl hl').1

lemma blk_card {hkq : k * q ≤ n} {hk : 0 < k} {hq : 0 < q} (β : Fin ((Reps hk hq).card / k)) :
    (blk hkq hk hq β).card = k * q := by
  rw [blk, card_biUnion]
  · rw [sum_congr rfl (fun l _ => mat_card hkq _ hk), sum_const, card_univ, Fintype.card_fin,
      smul_eq_mul]
  · intro l _ l' _ hne
    rw [Function.onFun, disjoint_left]
    intro A h1 h2
    exact hne (blk_rep_eq h1 h2).2

/-- The matching colouring of a block. -/
lemma blk_col {hkq : k * q ≤ n} {hk : 0 < k} {hq : 0 < q} (β : Fin ((Reps hk hq).card / k)) :
    ∃ col : ↥(blk hkq hk hq β) → Fin k,
      ∀ A A' : ↥(blk hkq hk hq β), col A = col A' → A = A' ∨ Disjoint A.1 A'.1 := by
  choose col hcol using fun A : ↥(blk hkq hk hq β) => mem_blk.1 A.2
  refine ⟨col, fun A A' h => ?_⟩
  have h1 := hcol A
  have h2 := hcol A'
  rw [h] at h1
  rcases mat_compat hkq h1 h2 with h' | h'
  · exact Or.inl (Subtype.ext h')
  · exact Or.inr h'

end Blocks

/-! ## Images of blocks -/

lemma img_injective (σ : Equiv.Perm (Fin n)) : Function.Injective (img σ) := by
  intro A B h
  rw [← img_symm_of (rfl : img σ A = img σ A), h, img_symm_of rfl]

lemma img_disjoint (σ : Equiv.Perm (Fin n)) {A A' : Finset (Fin n)} (h : Disjoint A A') :
    Disjoint (img σ A) (img σ A') := by
  rw [disjoint_left]; intro v hv hv'; rw [mem_img] at hv hv'; exact disjoint_left.1 h hv hv'

noncomputable def imgB (σ : Equiv.Perm (Fin n)) (B : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n)) := B.image (img σ)

lemma imgB_card (σ : Equiv.Perm (Fin n)) (B : Finset (Finset (Fin n))) :
    (imgB σ B).card = B.card := card_image_of_injective _ (img_injective σ)

lemma imgB_disjoint (σ : Equiv.Perm (Fin n)) {B B' : Finset (Finset (Fin n))} (h : Disjoint B B') :
    Disjoint (imgB σ B) (imgB σ B') := by
  rw [disjoint_left]
  intro A hA hA'
  obtain ⟨A1, h1, rfl⟩ := mem_image.1 hA
  obtain ⟨A2, h2, he⟩ := mem_image.1 hA'
  rw [img_injective σ he] at h2
  exact disjoint_left.1 h h1 h2

lemma imgB_mem_card (σ : Equiv.Perm (Fin n)) {B : Finset (Finset (Fin n))} {k : ℕ}
    (hB : ∀ A ∈ B, A.card = k) : ∀ A ∈ imgB σ B, A.card = k := by
  intro A hA
  obtain ⟨A1, h1, rfl⟩ := mem_image.1 hA
  rw [card_img]; exact hB A1 h1

lemma imgB_col (σ : Equiv.Perm (Fin n)) {B : Finset (Finset (Fin n))} {k : ℕ}
    (h : ∃ col : ↥B → Fin k, ∀ A A' : ↥B, col A = col A' → A = A' ∨ Disjoint A.1 A'.1) :
    ∃ col : ↥(imgB σ B) → Fin k,
      ∀ A A' : ↥(imgB σ B), col A = col A' → A = A' ∨ Disjoint A.1 A'.1 := by
  obtain ⟨col, hcol⟩ := h
  have hpre : ∀ A : ↥(imgB σ B), img σ⁻¹ A.1 ∈ B := by
    intro A
    obtain ⟨A1, h1, he⟩ := mem_image.1 A.2
    rw [← he, ← img_mul]; simpa [img_one] using h1
  refine ⟨fun A => col ⟨img σ⁻¹ A.1, hpre A⟩, fun A A' hc => ?_⟩
  have himg : ∀ A : ↥(imgB σ B), img σ (img σ⁻¹ A.1) = A.1 := by
    intro A; rw [← img_mul]; simp [img_one]
  rcases hcol _ _ hc with h' | h'
  · left
    apply Subtype.ext
    rw [← himg A, ← himg A']
    exact congrArg (fun X : ↥B => img σ X.1) h'
  · right
    rw [← himg A, ← himg A']
    exact img_disjoint σ h'

/-! ## Compatible pairs of a block and the cleaned graph -/

open scoped Classical in
noncomputable def CPs (X : Finset (Finset (Fin n))) : Finset (Finset (Fin n) × Finset (Fin n)) :=
  (X ×ˢ X).filter (fun p => p.1 ≠ p.2 ∧ (p.1 ∩ p.2).Nonempty)

lemma CPs_img (σ : Equiv.Perm (Fin n)) (B : Finset (Finset (Fin n))) (g : Finset (Fin n) × Finset (Fin n) → ℕ) :
    ∑ p ∈ CPs (imgB σ B), g p = ∑ p ∈ CPs B, g (img σ p.1, img σ p.2) := by
  classical
  symm
  apply sum_nbij' (fun p => (img σ p.1, img σ p.2)) (fun p => (img σ⁻¹ p.1, img σ⁻¹ p.2))
  · intro p hp
    simp only [CPs, mem_filter, mem_product, imgB] at hp ⊢
    refine ⟨⟨mem_image_of_mem _ hp.1.1, mem_image_of_mem _ hp.1.2⟩,
      fun h => hp.2.1 (img_injective σ h), ?_⟩
    rw [← img_inter]; obtain ⟨v, hv⟩ := hp.2.2; exact ⟨σ v, by simp [hv]⟩
  · intro p hp
    simp only [CPs, mem_filter, mem_product, imgB] at hp ⊢
    have h1 : img σ⁻¹ p.1 ∈ B := by
      obtain ⟨A, hA, he⟩ := mem_image.1 hp.1.1
      rw [← he, ← img_mul]; simpa [img_one] using hA
    have h2 : img σ⁻¹ p.2 ∈ B := by
      obtain ⟨A, hA, he⟩ := mem_image.1 hp.1.2
      rw [← he, ← img_mul]; simpa [img_one] using hA
    refine ⟨⟨h1, h2⟩, fun h => hp.2.1 (img_injective σ⁻¹ h), ?_⟩
    rw [← img_inter]; obtain ⟨v, hv⟩ := hp.2.2
    exact ⟨σ⁻¹ v, by simpa [Equiv.Perm.inv_def] using hv⟩
  · intro p _; simp [← img_mul, img_one]
  · intro p _; simp [← img_mul, img_one]
  · intro p _; rfl

open scoped Classical in
/-- Edges `(A, e)` that obstruct a star for some compatible partner `A'`. -/
noncomputable def badE (G : Finset (Finset (Fin n))) (h0 : Fin n) (X : Finset (Finset (Fin n))) :
    Finset (↥X × Sym2 (Fin n)) :=
  univ.filter (fun p => ∃ A' ∈ X, A' ≠ p.1.1 ∧ (p.1.1 ∩ A').Nonempty ∧ PEdge G p.1.1 p.2 ∧
    PEdge G A' p.2 ∧ frc G h0 (p.1.1 \ A') (A' \ p.1.1) ∉ p.2 ∧
    frc G h0 (p.1.1 \ A') (A' \ p.1.1) ∉ p.1.1 ∩ A')

/-- The cleaned graph. -/
noncomputable def Hc (G : Finset (Finset (Fin n))) (h0 : Fin n) (X : Finset (Finset (Fin n))) :
    Finset (↥X × Sym2 (Fin n)) :=
  proj G X \ badE G h0 X

lemma Hc_sub (G : Finset (Finset (Fin n))) (h0 : Fin n) (X : Finset (Finset (Fin n))) :
    Hc G h0 X ⊆ proj G X := sdiff_subset

lemma Hc_cost (G : Finset (Finset (Fin n))) (h0 : Fin n) (X : Finset (Finset (Fin n))) :
    (proj G X).card ≤ (Hc G h0 X).card + ∑ p ∈ CPs X, gam G h0 p.1 p.2 := by
  classical
  have h1 : (proj G X).card ≤ (Hc G h0 X).card + (badE G h0 X).card := by
    have := card_sdiff_add_card_inter (proj G X) (badE G h0 X)
    have h2 := card_le_card (inter_subset_right (s₁ := proj G X) (s₂ := badE G h0 X))
    rw [Hc]; omega
  have hmem : ∀ p ∈ CPs X, p.1 ∈ X := fun p hp => (mem_product.1 (mem_filter.1 hp).1).1
  have h2 : (badE G h0 X).card ≤ ∑ p ∈ CPs X, gam G h0 p.1 p.2 := by
    rw [← sum_attach]
    calc (badE G h0 X).card ≤ ((CPs X).attach.biUnion (fun p =>
          (univ.filter (fun e : Sym2 (Fin n) => PEdge G p.1.1 e ∧ PEdge G p.1.2 e ∧
            frc G h0 (p.1.1 \ p.1.2) (p.1.2 \ p.1.1) ∉ e ∧
            frc G h0 (p.1.1 \ p.1.2) (p.1.2 \ p.1.1) ∉ p.1.1 ∩ p.1.2)).image
          (fun e => ((⟨p.1.1, hmem p.1 p.2⟩ : ↥X), e)))).card := by
          apply card_le_card
          rintro ⟨A, e⟩ hAe
          simp only [badE, mem_filter, mem_univ, true_and] at hAe
          obtain ⟨A', hA'X, hne, hint, h1, h2, h3, h4⟩ := hAe
          have hp : (A.1, A') ∈ CPs X := by
            simp only [CPs, mem_filter, mem_product]
            exact ⟨⟨A.2, hA'X⟩, Ne.symm hne, hint⟩
          refine mem_biUnion.2 ⟨⟨(A.1, A'), hp⟩, mem_attach _ _, mem_image.2 ⟨e, ?_, rfl⟩⟩
          simp only [mem_filter, mem_univ, true_and]
          exact ⟨h1, h2, h3, h4⟩
      _ ≤ ∑ p ∈ (CPs X).attach, (univ.filter (fun e : Sym2 (Fin n) => PEdge G p.1.1 e ∧
            PEdge G p.1.2 e ∧ frc G h0 (p.1.1 \ p.1.2) (p.1.2 \ p.1.1) ∉ e ∧
            frc G h0 (p.1.1 \ p.1.2) (p.1.2 \ p.1.1) ∉ p.1.1 ∩ p.1.2)).card :=
          card_biUnion_le.trans (sum_le_sum (fun p _ => card_image_le))
      _ = _ := by rfl
  omega

lemma Hc_alpha (G : Finset (Finset (Fin n))) (h0 : Fin n) (X : Finset (Finset (Fin n))) :
    (OMA_DL.alphaO (cmp X) (Hc G h0 X)).card ≤
      ((CPs X).filter (fun p => frc G h0 (p.1 \ p.2) (p.2 \ p.1) ∈ p.1 ∩ p.2)).card := by
  classical
  apply card_le_card_of_injOn (fun p => (p.1.1, p.2.1))
  · rintro ⟨A, A'⟩ hp
    simp only [OMA_DL.alphaO, coe_filter, mem_offDiag, mem_univ, true_and, Set.mem_setOf_eq] at hp
    obtain ⟨hne, hc, hns⟩ := hp
    simp only [coe_filter, CPs, mem_filter, mem_product, Set.mem_setOf_eq]
    refine ⟨⟨⟨A.2, A'.2⟩, fun h => hne (Subtype.ext h), hc⟩, ?_⟩
    by_contra hf
    apply hns
    refine ⟨frc G h0 (A.1 \ A'.1) (A'.1 \ A.1), fun e he => ?_⟩
    rw [mem_CNX] at he
    obtain ⟨h1, h2⟩ := he
    by_contra hfe
    have h1' := (mem_sdiff.1 h1)
    have h2p : PEdge G A'.1 e := mem_proj.1 (mem_sdiff.1 h2).1
    apply h1'.2
    simp only [badE, mem_filter, mem_univ, true_and]
    exact ⟨A'.1, A'.2, fun h => hne (Subtype.ext h.symm), hc, mem_proj.1 h1'.1, h2p, hfe, hf⟩
  · intro p _ p' _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)

end OMA_H2

/-!
# Erdős 643, CN-stability: assembly
-/

namespace OMA_H2

open Finset OMA_DL

variable {n : ℕ}

/-- The constant `2^(D+1)` with `D = (t-2)²`. -/
def cJ (t : ℕ) : ℕ := 2 ^ ((t - 2) * (t - 2) + 1)

/-- The bound for the leaves sum. -/
def ΛB (n t : ℕ) : ℕ := Nat.sqrt (n * cJ t * (2 * (n * n) + n * cJ t * n)) + 1

lemma lt_sqrt_succ {a b : ℕ} (h : a * a ≤ b) : a < Nat.sqrt b + 1 := by
  have := Nat.le_sqrt.2 h
  omega

open scoped Classical in
/-- **Per-block theorem**: cleaning, the deletion lemma, and the cluster lemma. -/
theorem block_cluster {t : ℕ} (ht : 4 ≤ t) {G : Finset (Finset (Fin n))}
    (hR : ¬ G.HasRepeatedDisjointUnion) (hL : LocStar t G) (h0 : Fin n)
    {X : Finset (Finset (Fin n))} (hX : ∀ A ∈ X, A.card = t - 2)
    (hcolX : ∃ col : ↥X → Fin (t - 2), ∀ A A' : ↥X, col A = col A' → A = A' ∨ Disjoint A.1 A'.1)
    (hXn : X.card ≤ n) (x0 : ↥X) {Kα : ℕ} (hα : (alphaO (cmp X) (Hc G h0 X)).card ≤ Kα)
    (δN : ℕ)
    (hδ : t * n.choose 2 + ∑ p ∈ CPs X, gam G h0 p.1 p.2 +
      (9 * (n * (alphaO (cmp X) (Hc G h0 X)).card) +
        10 * (n * ((t - 2) * (t - 2)) * ((t - 2) * (t - 2))) +
        n * ((t - 2) * (t - 2) * (alphaO (cmp X) (Hc G h0 X)).card)) ≤ (proj G X).card + δN)
    (hn24 : 24 * ((Kα * cJ t) * (Kα * cJ t) + 2) ≤ n)
    (hV3 : 16 * (4 * δN + ΛB n t + (Kα * cJ t * (t - 2)) * n) + (n - 8) * (Kα * cJ t * (t - 2)) +
      3 * (n - 8) ≤ (n - 8) * n) :
    ∃ S : Finset ↥X, ∃ W : Finset (Fin n), ∃ x m : ℕ,
      (W.Nonempty → S.card = t - 2) ∧
      (∀ w ∈ W, ∀ w' ∈ W, w ≠ w' → ∀ c, Ctr t G w w' c → ∀ T ∈ S, c ∈ T.1) ∧
      n ≤ W.card + (Kα * cJ t) * (Kα * cJ t) + 2 + 2 * m + 2 * x ∧
      (n - x - 1) * m ≤ 2 * (4 * δN + ΛB n t + (Kα * cJ t * (t - 2)) * n) ∧
      (n - 8) * x ≤ 16 * (4 * δN + ΛB n t + (Kα * cJ t * (t - 2)) * n) +
        (n - 8) * (Kα * cJ t * (t - 2)) := by
  obtain ⟨col, hcol⟩ := hcolX
  set D := (t - 2) * (t - 2) with hD
  set F := Hc G h0 X with hF
  have hFp : F ⊆ proj G X := Hc_sub G h0 X
  have hg1p := proj_good1 ht hX hR h0 (G := G)
  have hg1 : Good1 (cmp X) F := hg1p.mono hFp
  have hg2 : Good2 (cmp X) F := (proj_good2 ht hX hL).mono hFp hg1p
  have hg3 : ∀ u v, u ≠ v → YDiag F u v → ∃ w, G3 (cmp X) F s(u, v) w := by
    intro u v huv _
    obtain ⟨w, hw⟩ := proj_G3 ht hX hL huv (B := X)
    exact ⟨w, G3_mono hFp hw⟩
  have hnd : ∀ p ∈ F, ¬ p.2.IsDiag := fun p hp => proj_nd p (hFp hp)
  have hDb : ∀ A, (cnb (cmp X) A).card ≤ D := fun A => cnb_card_le col hcol A (hX A.1 A.2)
  obtain ⟨Fs, hFsF, hcost, hS, hM⟩ :=
    deletion_lemma (cmp_symm X) hDb F hnd hg1 hg2 hg3 h0 x0
  have hFs : ∀ p ∈ Fs, PEdge G p.1.1 p.2 := fun p hp => mem_proj.1 (hFp (hFsF hp))
  -- density
  have hXc : Fintype.card ↥X ≤ n := by rw [Fintype.card_coe]; exact hXn
  have hch : (Fintype.card ↥X).choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 hXc
  have hpr : (proj G X).card ≤ F.card + ∑ p ∈ CPs X, gam G h0 p.1 p.2 := Hc_cost G h0 X
  have hdens : (t - 2) * n.choose 2 ≤ Fs.card + δN := by
    have e1 : 9 * (Fintype.card ↥X * (alphaO (cmp X) F).card) ≤ 9 * (n * (alphaO (cmp X) F).card) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hXc)
    have e2 : 10 * (Fintype.card ↥X * D * D) ≤ 10 * (n * D * D) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hXc))
    have ht2 : t * n.choose 2 = (t - 2) * n.choose 2 + 2 * n.choose 2 := by
      rw [← add_mul]; congr 1; omega
    omega
  -- bounds for the cluster lemma
  have hj2 : (J2 Fs t).card ≤ Kα * cJ t :=
    (J2_card_le ht hX col hcol hFsF).trans (Nat.mul_le_mul_right _ hα)
  have hb : (Bst Fs t).card ≤ Kα * cJ t * (t - 2) :=
    (Bst_card_le ht hX).trans (Nat.mul_le_mul_right _ hj2)
  have hJ1 : (J1 Fs t).card ≤ n * cJ t := by
    calc (J1 Fs t).card ≤ (FamC X t).card := card_le_card (filter_subset _ _)
      _ ≤ (univ : Finset ↥X).card * cJ t := famC_card_le col hcol ht hX
      _ ≤ n * cJ t := by
          apply Nat.mul_le_mul_right; rw [card_univ]; exact hXc
  have hΛ : ∑ S ∈ J1 Fs t, (leaves Fs h0 S).card ≤ ΛB n t := by
    have hsq := leaves_sq ht hX col hcol hFs hL h0
    have : (∑ S ∈ J1 Fs t, (leaves Fs h0 S).card) * (∑ S ∈ J1 Fs t, (leaves Fs h0 S).card) ≤
        n * cJ t * (2 * (n * n) + n * cJ t * n) := by
      rw [← sq]
      refine hsq.trans ?_
      exact Nat.mul_le_mul hJ1 (Nat.add_le_add_left (Nat.mul_le_mul_right _ hJ1) _)
    exact (lt_sqrt_succ this).le
  have hn24' : 24 * ((J2 Fs t).card * (J2 Fs t).card + 2) ≤ n :=
    le_trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul hj2 hj2) _)) hn24
  have hMis : 4 * δN + (∑ S ∈ J1 Fs t, (leaves Fs h0 S).card) + (Bst Fs t).card * n ≤
      4 * δN + ΛB n t + (Kα * cJ t * (t - 2)) * n := by
    have := Nat.mul_le_mul_right n hb
    omega
  have hV3' : 16 * (4 * δN + (∑ S ∈ J1 Fs t, (leaves Fs h0 S).card) + (Bst Fs t).card * n) +
      (n - 8) * (Bst Fs t).card + 3 * (n - 8) ≤ (n - 8) * n := by
    have := Nat.mul_le_mul_left (n - 8) hb
    omega
  obtain ⟨S, v, v', W, x, m, hvv', hvW, hv'W, hWS, hFam, h1, h2, h3⟩ :=
    cluster ht hX col hcol hFs hL h0 hR hFsF hFp hg2 hS hM δN hdens hn24' hV3'
  refine ⟨S, W, x, m, fun hne => (mem_filter.1 (hFam hne)).2.1, ?_, ?_, ?_, ?_⟩
  · intro w hw w' hw' hww' c hc
    apply ctr_in_family ht hX hFs hc hww' hvv'
    intro T hT
    have e1 := hWS w hw
    have e2 := hWS w' hw'
    refine ⟨(mem_Nb Fs).1 (e1.1 ▸ hT), (mem_Nb Fs).1 (e1.2 ▸ hT), (mem_Nb Fs).1 (e2.1 ▸ hT),
      (mem_Nb Fs).1 (e2.2 ▸ hT)⟩
  · have := Nat.mul_le_mul hj2 hj2; omega
  · exact h2.trans (Nat.mul_le_mul_left _ hMis)
  · have := Nat.mul_le_mul_left 16 hMis
    have := Nat.mul_le_mul_left (n - 8) hb
    omega

open scoped Classical in
/-- On every block, `|proj| ≤ t C(n,2) + cleaning cost + error`. -/
theorem block_proj_le {t : ℕ} (ht : 4 ≤ t) {G : Finset (Finset (Fin n))}
    (hR : ¬ G.HasRepeatedDisjointUnion) (hL : LocStar t G) (h0 : Fin n)
    {X : Finset (Finset (Fin n))} (hX : ∀ A ∈ X, A.card = t - 2)
    (hcolX : ∃ col : ↥X → Fin (t - 2), ∀ A A' : ↥X, col A = col A' → A = A' ∨ Disjoint A.1 A'.1)
    (hXn : X.card ≤ n) (x0 : ↥X) :
    (proj G X).card ≤ t * n.choose 2 + ∑ p ∈ CPs X, gam G h0 p.1 p.2 +
      (9 * (n * (alphaO (cmp X) (Hc G h0 X)).card) +
        10 * (n * ((t - 2) * (t - 2)) * ((t - 2) * (t - 2))) +
        n * ((t - 2) * (t - 2) * (alphaO (cmp X) (Hc G h0 X)).card)) := by
  obtain ⟨col, hcol⟩ := hcolX
  set D := (t - 2) * (t - 2) with hD
  set F := Hc G h0 X with hF
  have hFp : F ⊆ proj G X := Hc_sub G h0 X
  have hg1p := proj_good1 ht hX hR h0 (G := G)
  have hg1 : Good1 (cmp X) F := hg1p.mono hFp
  have hg2 : Good2 (cmp X) F := (proj_good2 ht hX hL).mono hFp hg1p
  have hg3 : ∀ u v, u ≠ v → YDiag F u v → ∃ w, G3 (cmp X) F s(u, v) w := by
    intro u v huv _
    obtain ⟨w, hw⟩ := proj_G3 ht hX hL huv (B := X)
    exact ⟨w, G3_mono hFp hw⟩
  have hnd : ∀ p ∈ F, ¬ p.2.IsDiag := fun p hp => proj_nd p (hFp hp)
  have hDb : ∀ A, (cnb (cmp X) A).card ≤ D := fun A => cnb_card_le col hcol A (hX A.1 A.2)
  obtain ⟨Fs, hFsF, hcost, hS, -⟩ :=
    deletion_lemma (cmp_symm X) hDb F hnd hg1 hg2 hg3 h0 x0
  have hFs : ∀ p ∈ Fs, PEdge G p.1.1 p.2 := fun p hp => mem_proj.1 (hFp (hFsF hp))
  have hndFs : ∀ p ∈ Fs, ¬ p.2.IsDiag := fun p hp => hnd p (hFsF hp)
  have hS' : ∀ e, CompatSet (cmp X) (Nb Fs e) ∨ (Nb Fs e).card ≤ 2 := by
    intro e
    rcases hS e with h | ⟨x, x', hxx, -, -⟩
    · exact Or.inl h
    · right; rw [hxx]; exact card_le_two
  have hFsc := notmax_card hndFs (Nb_card_le ht col hcol hS')
  have hXc : Fintype.card ↥X ≤ n := by rw [Fintype.card_coe]; exact hXn
  have hch : (Fintype.card ↥X).choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 hXc
  have hpr : (proj G X).card ≤ F.card + ∑ p ∈ CPs X, gam G h0 p.1 p.2 := Hc_cost G h0 X
  have e1 : 9 * (Fintype.card ↥X * (alphaO (cmp X) F).card) ≤ 9 * (n * (alphaO (cmp X) F).card) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hXc)
  have e2 : 10 * (Fintype.card ↥X * D * D) ≤ 10 * (n * D * D) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hXc))
  have ht2 : t * n.choose 2 = (t - 2) * n.choose 2 + 2 * n.choose 2 := by
    rw [← add_mul]; congr 1; omega
  omega

/-! ## Averages over permutations for a base block -/

open scoped Classical in
lemma proj_card_eq (G : Finset (Finset (Fin n))) (X : Finset (Finset (Fin n))) :
    (proj G X).card = ∑ A ∈ X, pdeg G A := by
  rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) (fun _ _ => mem_univ _)]
  rw [← sum_coe_sort X (pdeg G)]
  apply sum_congr rfl
  intro A _
  rw [pdeg]
  apply card_bij (fun p _ => p.2)
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp ⊢
    rw [← hp.2]; exact mem_proj.1 hp.1
  · intro p hp p' hp' h
    simp only [mem_filter] at hp hp'
    exact Prod.ext (hp.2.trans hp'.2.symm) h
  · intro e he
    simp only [mem_filter, mem_univ, true_and] at he
    exact ⟨(A, e), mem_filter.2 ⟨mem_proj.2 he, rfl⟩, rfl⟩

lemma sum_imgB (σ : Equiv.Perm (Fin n)) (B : Finset (Finset (Fin n))) (f : Finset (Fin n) → ℕ) :
    ∑ A ∈ imgB σ B, f A = ∑ A ∈ B, f (img σ A) :=
  sum_image (fun A _ A' _ h => img_injective σ h)

lemma Pj_self_card (A : Finset (Fin n)) : (Pj A A).card = n.choose A.card := by
  classical
  have : Pj A A = (univ.powersetCard A.card).image (fun B => (B, B)) := by
    ext ⟨B1, B2⟩
    simp only [mem_Pj, mem_image, mem_powersetCard, subset_univ, true_and, Prod.mk.injEq, inter_self]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have e1 : B1 ∩ B2 = B1 := eq_of_subset_of_card_le inter_subset_left (by omega)
      have e2 : B1 ∩ B2 = B2 := eq_of_subset_of_card_le inter_subset_right (by omega)
      exact ⟨B1, h1, rfl, e1.symm.trans e2⟩
    · rintro ⟨B, hB, rfl, rfl⟩; simp [hB]
  rw [this, card_image_of_injective _ (fun B B' h => by simpa using h), card_powersetCard,
    card_univ, Fintype.card_fin]

lemma Pj_self_sum (A : Finset (Fin n)) (f : Finset (Fin n) → ℕ) :
    ∑ P ∈ Pj A A, f P.1 = ∑ B ∈ (univ : Finset (Fin n)).powersetCard A.card, f B := by
  classical
  have : Pj A A = (univ.powersetCard A.card).image (fun B => (B, B)) := by
    ext ⟨B1, B2⟩
    simp only [mem_Pj, mem_image, mem_powersetCard, subset_univ, true_and, Prod.mk.injEq, inter_self]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have e1 : B1 ∩ B2 = B1 := eq_of_subset_of_card_le inter_subset_left (by omega)
      have e2 : B1 ∩ B2 = B2 := eq_of_subset_of_card_le inter_subset_right (by omega)
      exact ⟨B1, h1, rfl, e1.symm.trans e2⟩
    · rintro ⟨B, hB, rfl, rfl⟩; simp [hB]
  rw [this, sum_image (fun B _ B' _ h => by simpa using h)]

/-- `Σ_σ |proj(σ B₀)| · C(n, t-2) ≥ n! · |B₀| · |G| C(t,2)`. -/
theorem avg_proj {t : ℕ} (ht : 4 ≤ t) {G : Finset (Finset (Fin n))} (hGt : ∀ E ∈ G, E.card = t)
    {B0 : Finset (Finset (Fin n))} (hB0 : ∀ A ∈ B0, A.card = t - 2) :
    Fintype.card (Equiv.Perm (Fin n)) * B0.card * (G.card * t.choose 2) ≤
      (∑ σ : Equiv.Perm (Fin n), (proj G (imgB σ B0)).card) * n.choose (t - 2) := by
  simp_rw [proj_card_eq, sum_imgB]
  rw [sum_comm, sum_mul]
  rw [mul_comm (Fintype.card _) B0.card, mul_assoc, card_eq_sum_ones B0, sum_mul, one_mul]
  apply sum_le_sum
  intro A hA
  have h1 := perm_avg A A (fun P => pdeg G P.1)
  simp only at h1
  rw [Pj_self_card, hB0 A hA, Pj_self_sum, hB0 A hA] at h1
  rw [h1]
  exact Nat.mul_le_mul_left _ (sum_pdeg (by omega) hGt)

lemma mem_CPs {X : Finset (Finset (Fin n))} {p : Finset (Fin n) × Finset (Fin n)} :
    p ∈ CPs X ↔ p.1 ∈ X ∧ p.2 ∈ X ∧ p.1 ≠ p.2 ∧ (p.1 ∩ p.2).Nonempty := by
  classical
  simp [CPs, and_assoc]

/-- `Σ_σ Σ_{CP(σB₀)} gam ≤ n! · |CP(B₀)| · cG`. -/
theorem avg_gam {t : ℕ} (ht : 4 ≤ t) {G : Finset (Finset (Fin n))} (hGt : ∀ E ∈ G, E.card = t)
    (hR : ¬ G.HasRepeatedDisjointUnion) (h0 : Fin n) (hn : 4 * t ≤ n)
    {B0 : Finset (Finset (Fin n))} (hB0 : ∀ A ∈ B0, A.card = t - 2) :
    ∑ σ : Equiv.Perm (Fin n), ∑ p ∈ CPs (imgB σ B0), gam G h0 p.1 p.2 ≤
      Fintype.card (Equiv.Perm (Fin n)) * (CPs B0).card * cG t := by
  rw [sum_congr rfl (fun σ _ => CPs_img σ B0 (fun p => gam G h0 p.1 p.2))]
  rw [sum_comm, mul_assoc, mul_comm (CPs B0).card, ← mul_assoc, card_eq_sum_ones (CPs B0),
    mul_sum]
  apply sum_le_sum
  intro p hp
  rw [mem_CPs] at hp
  obtain ⟨h1, h2, hne, hint⟩ := hp
  have hav := perm_avg p.1 p.2 (fun P => gam G h0 P.1 P.2)
  have hgs := gam_sum ht hGt hR h0 (hB0 _ h1) (hB0 _ h2) hne hint hn
  have hpos : 0 < (Pj p.1 p.2).card := card_pos.2 ⟨_, img_mem_Pj 1 p.1 p.2⟩
  have : (∑ σ : Equiv.Perm (Fin n), gam G h0 (img σ p.1) (img σ p.2)) * (Pj p.1 p.2).card ≤
      (Fintype.card (Equiv.Perm (Fin n)) * cG t * 1) * (Pj p.1 p.2).card := by
    rw [hav, mul_one, mul_assoc]; exact Nat.mul_le_mul_left _ hgs
  exact Nat.le_of_mul_le_mul_right this hpos

/-- `Σ_σ |αO(Hc(σB₀))| · (n - 2t) ≤ n! · |CP(B₀)| · t`. -/
theorem avg_alpha {t : ℕ} {G : Finset (Finset (Fin n))} (h0 : Fin n)
    {B0 : Finset (Finset (Fin n))} (hB0 : ∀ A ∈ B0, A.card = t - 2) :
    (∑ σ : Equiv.Perm (Fin n), (alphaO (cmp (imgB σ B0)) (Hc G h0 (imgB σ B0))).card) * (n - 2 * t) ≤
      Fintype.card (Equiv.Perm (Fin n)) * (CPs B0).card * t := by
  classical
  set g : Finset (Fin n) × Finset (Fin n) → ℕ :=
    fun P => if frc G h0 (P.1 \ P.2) (P.2 \ P.1) ∈ P.1 ∩ P.2 then 1 else 0 with hg
  have hstep : ∀ σ : Equiv.Perm (Fin n), (alphaO (cmp (imgB σ B0)) (Hc G h0 (imgB σ B0))).card ≤
      ∑ p ∈ CPs B0, g (img σ p.1, img σ p.2) := by
    intro σ
    refine (Hc_alpha G h0 (imgB σ B0)).trans ?_
    rw [card_filter, ← CPs_img σ B0 g]
  have hper : ∀ p ∈ CPs B0, (∑ σ : Equiv.Perm (Fin n), g (img σ p.1, img σ p.2)) * (n - 2 * t) ≤
      Fintype.card (Equiv.Perm (Fin n)) * t := by
    intro p hp
    rw [mem_CPs] at hp
    obtain ⟨h1, h2, hne, hint⟩ := hp
    have hAA : p.1.card = p.2.card := by rw [hB0 _ h1, hB0 _ h2]
    have hav := perm_avg p.1 p.2 g
    have hal := alph_sum (G := G) h0 hAA hint
    have hk' : (p.1 \ p.2).card ≤ t := (card_le_card sdiff_subset).trans (by rw [hB0 _ h1]; omega)
    have hj : (p.1 ∩ p.2).card ≤ t := (card_le_card inter_subset_left).trans (by rw [hB0 _ h1]; omega)
    have hpos : 0 < (Pj p.1 p.2).card := card_pos.2 ⟨_, img_mem_Pj 1 p.1 p.2⟩
    have key : (∑ σ : Equiv.Perm (Fin n), g (img σ p.1, img σ p.2)) * (n - 2 * t) *
        (Pj p.1 p.2).card ≤ Fintype.card (Equiv.Perm (Fin n)) * t * (Pj p.1 p.2).card := by
      calc _ = (∑ σ : Equiv.Perm (Fin n), g (img σ p.1, img σ p.2)) * (Pj p.1 p.2).card *
            (n - 2 * t) := by ring
        _ = Fintype.card (Equiv.Perm (Fin n)) * (∑ P ∈ Pj p.1 p.2, g P) * (n - 2 * t) := by
            rw [hav]
        _ ≤ Fintype.card (Equiv.Perm (Fin n)) * (∑ P ∈ Pj p.1 p.2, g P) *
            (n - 2 * (p.1 \ p.2).card) := Nat.mul_le_mul_left _ (by omega)
        _ = Fintype.card (Equiv.Perm (Fin n)) * ((∑ P ∈ Pj p.1 p.2, g P) *
            (n - 2 * (p.1 \ p.2).card)) := by ring
        _ ≤ Fintype.card (Equiv.Perm (Fin n)) * ((p.1 ∩ p.2).card * (Pj p.1 p.2).card) :=
            Nat.mul_le_mul_left _ hal
        _ ≤ Fintype.card (Equiv.Perm (Fin n)) * (t * (Pj p.1 p.2).card) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hj)
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right key hpos
  calc (∑ σ : Equiv.Perm (Fin n), (alphaO (cmp (imgB σ B0)) (Hc G h0 (imgB σ B0))).card) *
        (n - 2 * t) ≤ (∑ σ : Equiv.Perm (Fin n), ∑ p ∈ CPs B0, g (img σ p.1, img σ p.2)) *
        (n - 2 * t) := Nat.mul_le_mul_right _ (sum_le_sum (fun σ _ => hstep σ))
    _ = ∑ p ∈ CPs B0, (∑ σ : Equiv.Perm (Fin n), g (img σ p.1, img σ p.2)) * (n - 2 * t) := by
        rw [sum_comm, sum_mul]
    _ ≤ ∑ _p ∈ CPs B0, Fintype.card (Equiv.Perm (Fin n)) * t := sum_le_sum hper
    _ = _ := by rw [sum_const, smul_eq_mul]; ring

/-! ## Helper facts for the assembly -/

lemma binom_identity (n t : ℕ) (ht : 2 ≤ t) (hn : t ≤ n) :
    2 * n * (t.choose 2 * (n - 1).choose (t - 1)) =
      t * (n - t + 2) * (n - t + 1) * n.choose (t - 2) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel, show s + 2 - 1 = s + 1 by omega]
  have e1 := Nat.add_one_mul_choose_eq m (s + 1)
  have e2 := Nat.choose_succ_right_eq (m + 1) (s + 1)
  have e3 := Nat.choose_succ_right_eq (m + 1) s
  have hc2 : (s + 2).choose 2 * 2 = (s + 2) * (s + 1) := by
    have := Nat.choose_two_right (s + 2)
    have hev : 2 ∣ (s + 2) * (s + 2 - 1) := (Nat.even_mul_pred_self _).two_dvd
    rw [this, Nat.div_mul_cancel hev]; simp
  have q1 : m + 1 - (s + 1) = m + 1 - (s + 2) + 1 := by omega
  have q2 : m + 1 - s = m + 1 - (s + 2) + 2 := by omega
  rw [q1] at e2
  rw [q2] at e3
  rw [show m + 1 - (s + 2) + 2 = (m + 1 - (s + 2)) + 2 from rfl]
  set a := m + 1 - (s + 2) with ha
  zify at e1 e2 e3 hc2 ⊢
  linear_combination (2 * ((s + 2).choose 2 : ℤ)) * e1 +
    (((m + 1).choose (s + 1 + 1) : ℤ) * (s + 1 + 1)) * hc2 +
    ((s + 2 : ℤ) * (s + 1)) * e2 + ((s + 2 : ℤ) * (a + 1)) * e3

lemma CPs_card_le {t : ℕ} (ht : 4 ≤ t) {B : Finset (Finset (Fin n))} (hB : ∀ A ∈ B, A.card = t - 2)
    (hcol : ∃ col : ↥B → Fin (t - 2), ∀ A A' : ↥B, col A = col A' → A = A' ∨ Disjoint A.1 A'.1) :
    (CPs B).card ≤ B.card * ((t - 2) * (t - 2)) := by
  classical
  obtain ⟨col, hcol⟩ := hcol
  calc (CPs B).card ≤ ((univ : Finset ↥B).biUnion (fun A => (cnb (cmp B) A).image
        (fun A' => (A.1, A'.1)))).card := by
        apply card_le_card
        intro p hp
        rw [mem_CPs] at hp
        obtain ⟨h1, h2, hne, hint⟩ := hp
        refine mem_biUnion.2 ⟨⟨p.1, h1⟩, mem_univ _, mem_image.2 ⟨⟨p.2, h2⟩, ?_, rfl⟩⟩
        simp only [cnb, mem_filter, mem_univ, true_and, ne_eq, Subtype.mk.injEq]
        exact ⟨fun h => hne h.symm, hint⟩
    _ ≤ ∑ A : ↥B, ((cnb (cmp B) A).image (fun A' => (A.1, A'.1))).card := card_biUnion_le
    _ ≤ ∑ _A : ↥B, (t - 2) * (t - 2) := sum_le_sum (fun A _ =>
        card_image_le.trans (cnb_card_le col hcol A (hB A.1 A.2)))
    _ = B.card * ((t - 2) * (t - 2)) := by rw [sum_const, card_univ, Fintype.card_coe, smul_eq_mul]

/-- Arithmetic of the cluster output. -/
lemma W_bound {n Wc j2 x m Mis b L : ℕ} (hL : 1000 ≤ L) (hn : 16 ≤ n) (hb : 4 * (b + 1) ≤ n)
    (hMis : L * Mis ≤ 6 * (n * n))
    (h1 : n ≤ Wc + j2 * j2 + 2 + 2 * m + 2 * x) (h2 : (n - x - 1) * m ≤ 2 * Mis)
    (h3 : (n - 8) * x ≤ 16 * Mis + (n - 8) * b) :
    (n : ℝ) - Wc ≤ 432 * n / L + (j2 * j2 + 2 + 2 * b : ℕ) := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hn8 : (n : ℝ) / 2 ≤ ((n - 8 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast
    have : (16 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hMisR : (L : ℝ) * Mis ≤ 6 * (n * n) := by exact_mod_cast hMis
  -- bound on `x`
  have hx : (x : ℝ) ≤ 192 * n / L + b := by
    have h3R : ((n - 8 : ℕ) : ℝ) * x ≤ 16 * Mis + ((n - 8 : ℕ) : ℝ) * b := by exact_mod_cast h3
    have hn8pos : (0 : ℝ) < ((n - 8 : ℕ) : ℝ) := by
      have : (0 : ℝ) < (n : ℝ) / 2 := by
        have : (16 : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      linarith
    have h4 : (x : ℝ) ≤ 16 * Mis / ((n - 8 : ℕ) : ℝ) + b := by
      rw [div_add' _ _ _ hn8pos.ne', le_div_iff₀ hn8pos]; linarith
    have h5 : 16 * (Mis : ℝ) / ((n - 8 : ℕ) : ℝ) ≤ 192 * n / L := by
      rw [div_le_div_iff₀ hn8pos hLpos]
      have hn0 : (0 : ℝ) ≤ n := by positivity
      nlinarith
    linarith
  -- `n - x - 1 ≥ n / 2`
  have hbR : 4 * ((b : ℝ) + 1) ≤ n := by exact_mod_cast hb
  have hLR : (1000 : ℝ) ≤ L := by exact_mod_cast hL
  have h192 : 192 * (n : ℝ) / L ≤ 192 * n / 1000 := by
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num) hLR
  have hxn : (x : ℝ) + 1 ≤ n / 2 := by linarith
  have hxn' : x + 1 ≤ n := by
    have : ((x + 1 : ℕ) : ℝ) ≤ n := by push_cast; linarith
    exact_mod_cast this
  have hnx : (n : ℝ) / 2 ≤ ((n - x - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; linarith
  -- bound on `m`
  have hm : (m : ℝ) ≤ 24 * n / L := by
    have h2R : ((n - x - 1 : ℕ) : ℝ) * m ≤ 2 * Mis := by exact_mod_cast h2
    have hpos : (0 : ℝ) < (n : ℝ) / 2 := by
      have : (16 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hm0 : (0 : ℝ) ≤ m := by positivity
    have h6 : (n : ℝ) / 2 * m ≤ 2 * Mis := le_trans (by nlinarith) h2R
    rw [le_div_iff₀ hLpos]
    have hn0 : (0 : ℝ) < n := by linarith
    nlinarith
  have h1R : (n : ℝ) ≤ Wc + (j2 * j2 + 2 + 2 * b : ℕ) + 2 * m + 2 * x - 2 * b := by
    have : (n : ℝ) ≤ Wc + j2 * j2 + 2 + 2 * m + 2 * x := by exact_mod_cast h1
    push_cast; linarith
  have : 432 * (n : ℝ) / L = 2 * (24 * n / L) + 2 * (192 * n / L) := by ring
  linarith

/-! ## Markov for one base block -/

/-- The quantities attached to a placed block. -/
noncomputable def aQ (G : Finset (Finset (Fin n))) (h0 : Fin n) (t : ℕ) (X : Finset (Finset (Fin n))) : ℕ :=
  t * n.choose 2 + ∑ p ∈ CPs X, gam G h0 p.1 p.2 +
    (9 * (n * (alphaO (cmp X) (Hc G h0 X)).card) +
      10 * (n * ((t - 2) * (t - 2)) * ((t - 2) * (t - 2))) +
      n * ((t - 2) * (t - 2) * (alphaO (cmp X) (Hc G h0 X)).card))

noncomputable def dQ (G : Finset (Finset (Fin n))) (h0 : Fin n) (t : ℕ) (X : Finset (Finset (Fin n))) : ℕ :=
  aQ G h0 t X - (proj G X).card

/-- The real arithmetic behind the Markov bound (pure real inequalities). -/
lemma markov_real {n t L Kα N B0c Gc SAl SGm Sa SP cnt c2t cn1 cnk cg : ℝ}
    (ht : 4 ≤ t) (hL1 : 1 ≤ L) (hn4 : 4 * t ≤ n) (hN : 0 ≤ N) (hcg : 0 ≤ cg) (hSAl0 : 0 ≤ SAl)
    (hc2t : 0 ≤ c2t) (hcnk : 0 < cnk) (hGc : 0 ≤ Gc) (hcn1 : 0 ≤ cn1) (hcnt0 : 0 ≤ cnt)
    (hKα : 16 * t * ((t - 2) * (t - 2)) ≤ Kα)
    (hnC : 128 * (2 * t * (t - 2) + 10 * ((t - 2) * (t - 2)) * ((t - 2) * (t - 2)) +
      (t - 2) * (t - 2) * cg + (9 + (t - 2) * (t - 2)) * (2 * ((t - 2) * (t - 2)) * t) +
      t * (t - 2) ^ 3) * L ≤ n)
    (hB0big : n - (t - 2) ≤ B0c)
    (hSa : Sa = N * (t * (n * (n - 1) / 2)) + SGm + (9 * n + n * ((t - 2) * (t - 2))) * SAl +
      N * (10 * (n * ((t - 2) * (t - 2)) * ((t - 2) * (t - 2)))))
    (hAl : SAl * (n - 2 * t) ≤ N * (n * ((t - 2) * (t - 2))) * t)
    (hGm : SGm ≤ N * (n * ((t - 2) * (t - 2))) * cg)
    (hP : N * B0c * (Gc * c2t) ≤ SP * cnk)
    (hbin : 2 * n * (c2t * cn1) = t * (n - (t - 2)) * (n - (t - 2) - 1) * cnk)
    (hG : (1 - 1 / (64 * t * L)) * cn1 ≤ Gc)
    (hcnt : cnt * (n * n * Kα) ≤ L * Kα * (Sa - SP) + n * n * SAl) :
    5 * cnt ≤ N := by
  have hn0 : 0 < n := by linarith
  set k := t - 2 with hk
  have hk2 : 2 ≤ k := by linarith
  set ε : ℝ := 1 / (64 * t * L) with hε
  have hεpos : 0 < ε := by positivity
  have hεt : ε * t * L = 1 / 64 := by rw [hε]; field_simp
  -- (1) the α-sum
  have hSA : SAl ≤ 2 * N * (k * k) * t := by
    have h2 : n / 2 ≤ n - 2 * t := by linarith
    have h3 : SAl * (n / 2) ≤ N * (n * (k * k)) * t :=
      le_trans (mul_le_mul_of_nonneg_left h2 hSAl0) hAl
    have : SAl * n ≤ (2 * N * (k * k) * t) * n := by linarith
    exact le_of_mul_le_mul_right this hn0
  -- (2) the projection sum
  set Q : ℝ := t * (n - k) * (n - k - 1) / (2 * n) with hQ
  have hQkey : c2t * cn1 = Q * cnk := by
    rw [hQ, div_mul_eq_mul_div, eq_div_iff (by positivity)]
    linarith
  have hnk : 0 ≤ n - k := by linarith
  have hSPlow : N * (n - k) * ((1 - ε) * Q) ≤ SP := by
    have h1 : N * (n - k) * ((1 - ε) * Q) * cnk ≤ N * B0c * (Gc * c2t) := by
      have e1 : (1 - ε) * Q * cnk = c2t * ((1 - ε) * cn1) := by
        rw [mul_assoc, ← hQkey]; ring
      have e2 : c2t * ((1 - ε) * cn1) ≤ c2t * Gc := mul_le_mul_of_nonneg_left hG hc2t
      calc N * (n - k) * ((1 - ε) * Q) * cnk = N * (n - k) * ((1 - ε) * Q * cnk) := by ring
        _ = N * (n - k) * (c2t * ((1 - ε) * cn1)) := by rw [e1]
        _ ≤ N * (n - k) * (c2t * Gc) := mul_le_mul_of_nonneg_left e2 (mul_nonneg hN hnk)
        _ ≤ N * B0c * (c2t * Gc) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB0big hN) (mul_nonneg hc2t hGc)
        _ = _ := by ring
    exact le_of_mul_le_mul_right (h1.trans hP) hcnk
  -- (3) polynomial estimates
  have hpoly : t * (n * (n - 1) / 2) - (n - k) * Q ≤ 2 * t * k * n + t * k ^ 3 := by
    rw [hQ]
    have e : t * (n * (n - 1) / 2) - (n - k) * (t * (n - k) * (n - k - 1) / (2 * n)) =
        t * (3 * k * n ^ 2 - (3 * k ^ 2 + 2 * k) * n + k ^ 2 * (k + 1)) / (2 * n) := by
      field_simp; ring
    rw [e, div_le_iff₀ (by positivity)]
    have hk0 : 0 ≤ k := by linarith
    have h2 : k ^ 2 * (k + 1) ≤ 2 * k ^ 3 * n := by
      have a1 : k + 1 ≤ 2 * k * n := by nlinarith
      have a2 := mul_le_mul_of_nonneg_left a1 (by positivity : (0 : ℝ) ≤ k ^ 2)
      linarith
    have ht0 : 0 ≤ t := by linarith
    have hpos : 0 ≤ t * (k * n ^ 2 + (3 * k ^ 2 + 2 * k) * n + (2 * k ^ 3 * n - k ^ 2 * (k + 1))) := by
      apply mul_nonneg ht0
      have : 0 ≤ 2 * k ^ 3 * n - k ^ 2 * (k + 1) := by linarith
      positivity
    have key : (2 * t * k * n + t * k ^ 3) * (2 * n) -
        t * (3 * k * n ^ 2 - (3 * k ^ 2 + 2 * k) * n + k ^ 2 * (k + 1)) =
        t * (k * n ^ 2 + (3 * k ^ 2 + 2 * k) * n + (2 * k ^ 3 * n - k ^ 2 * (k + 1))) := by ring
    linarith
  have hεQ : (n - k) * (ε * Q) ≤ ε * t * (n * n) / 2 := by
    rw [hQ]
    have hnt1 : 0 ≤ n - k - 1 := by linarith
    have h1 : (n - k) * (t * (n - k) * (n - k - 1) / (2 * n)) ≤ t * (n * n) / 2 := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      have a1 : n - k ≤ n := by linarith
      have a2 : n - k - 1 ≤ n := by linarith
      have hq : (n - k) * (n - k - 1) ≤ n * n := mul_le_mul a1 a2 hnt1 hn0.le
      have hr : (n - k) * ((n - k) * (n - k - 1)) ≤ n * (n * n) :=
        mul_le_mul a1 hq (mul_nonneg hnk hnt1) hn0.le
      have ht0 : 0 ≤ t := by linarith
      calc (n - k) * (t * (n - k) * (n - k - 1)) = t * ((n - k) * ((n - k) * (n - k - 1))) := by ring
        _ ≤ t * (n * (n * n)) := mul_le_mul_of_nonneg_left hr ht0
        _ = t * (n * n) / 2 * (2 * n) := by ring
    calc (n - k) * (ε * (t * (n - k) * (n - k - 1) / (2 * n)))
        = ε * ((n - k) * (t * (n - k) * (n - k - 1) / (2 * n))) := by ring
      _ ≤ ε * (t * (n * n) / 2) := mul_le_mul_of_nonneg_left h1 hεpos.le
      _ = _ := by ring
  -- (4) the deficit sum
  set C1 : ℝ := 2 * t * k + 10 * (k * k) * (k * k) + k * k * cg + (9 + k * k) * (2 * (k * k) * t) +
    t * k ^ 3 with hC1
  have hdef : Sa - SP ≤ N * (ε * t * (n * n) / 2 + C1 * n) := by
    have hn1 : 1 ≤ n := by linarith
    have ht0 : 0 ≤ t := by linarith
    have hk0 : 0 ≤ k := by linarith
    have hk3 : 0 ≤ t * k ^ 3 := by positivity
    have e1 : N * (n - k) * ((1 - ε) * Q) = N * ((n - k) * Q) - N * ((n - k) * (ε * Q)) := by ring
    have hA := mul_le_mul_of_nonneg_left hpoly hN
    have hB := mul_le_mul_of_nonneg_left hεQ hN
    have hC : (9 * n + n * (k * k)) * SAl ≤ (9 * n + n * (k * k)) * (2 * N * (k * k) * t) :=
      mul_le_mul_of_nonneg_left hSA (by positivity)
    have hD3 : N * (t * k ^ 3) ≤ N * (t * k ^ 3 * n) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hk3 hn1) hN
    rw [hSa, hC1]
    linarith [hSPlow, hGm, e1, hA, hB, hC, hD3]
  -- (5) conclude
  have hKpos : 0 < Kα := by
    have ht0 : 0 < t := by linarith
    have hk0 : 0 < k := by linarith
    have : 0 < 16 * t * (k * k) := by positivity
    linarith
  have hCL : C1 * L ≤ n / 128 := by rw [hC1]; linarith
  have hDK : 2 * (k * k) * t ≤ Kα / 8 := by linarith
  have hnn : 0 < n * n * Kα := by positivity
  have h2 : L * Kα * (N * (ε * t * (n * n) / 2 + C1 * n)) + n * n * (2 * N * (k * k) * t) ≤
      (N / 5) * (n * n * Kα) := by
    have e1 : L * Kα * (N * (ε * t * (n * n) / 2 + C1 * n)) =
        N * Kα * (n * n) * ((ε * t * L) / 2) + N * Kα * n * (C1 * L) := by ring
    rw [e1, hεt]
    have e2 : N * Kα * n * (C1 * L) ≤ N * Kα * n * (n / 128) :=
      mul_le_mul_of_nonneg_left hCL (by positivity)
    have e3 : n * n * (2 * N * (k * k) * t) ≤ n * n * N * (Kα / 8) := by
      have := mul_le_mul_of_nonneg_left hDK (by positivity : (0 : ℝ) ≤ n * n * N)
      linarith
    have e4 : 0 ≤ N * Kα * (n * n) := by positivity
    linarith
  have h1 : cnt * (n * n * Kα) ≤ L * Kα * (N * (ε * t * (n * n) / 2 + C1 * n)) +
      n * n * (2 * N * (k * k) * t) := by
    have hLK : 0 ≤ L * Kα := by positivity
    have := add_le_add (mul_le_mul_of_nonneg_left hdef hLK)
      (mul_le_mul_of_nonneg_left hSA (by positivity : (0 : ℝ) ≤ n * n))
    linarith
  have h4 := le_of_mul_le_mul_right (h1.trans h2) hnn
  linarith

/-- The real arithmetic behind the Markov bound. -/
lemma markov_arith {n t L Kα N k D B0c Gc SAl SGm Sa SP cnt : ℕ} (ht : 4 ≤ t) (hL1 : 1 ≤ L)
    (hKα : 16 * t * D ≤ Kα) (hn4 : 4 * t ≤ n)
    (hnC : 128 * (2 * t * k + 10 * D * D + D * cG t + (9 + D) * (2 * D * t) + t * k ^ 3) * L ≤ n)
    (hD : D = (t - 2) * (t - 2)) (hk : k = t - 2)
    (hB0big : n - k ≤ B0c) (hSPa : SP ≤ Sa)
    (hSa : Sa = N * (t * n.choose 2) + SGm + (9 * n + n * D) * SAl + N * (10 * (n * D * D)))
    (hAl : SAl * (n - 2 * t) ≤ N * (n * D) * t) (hGm : SGm ≤ N * (n * D) * cG t)
    (hP : N * B0c * (Gc * t.choose 2) ≤ SP * n.choose k)
    (hbin : 2 * n * (t.choose 2 * (n - 1).choose (t - 1)) =
      t * (n - k) * (n - k - 1) * n.choose k)
    (hCnk : 0 < n.choose k)
    (hG : (1 - 1 / (64 * t * L : ℝ)) * (((n - 1).choose (t - 1) : ℕ) : ℝ) ≤ (Gc : ℝ))
    (hcnt : cnt * (n * n * Kα) ≤ L * Kα * (Sa - SP) + n * n * SAl) :
    5 * cnt ≤ N := by
  subst hD hk
  have ht2 : 2 ≤ t := by omega
  have hk2 : ((t - 2 : ℕ) : ℝ) = (t : ℝ) - 2 := by rw [Nat.cast_sub ht2]; norm_num
  have hn2t : ((n - 2 * t : ℕ) : ℝ) = n - 2 * t := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hnk : ((n - (t - 2) : ℕ) : ℝ) = n - ((t : ℝ) - 2) := by rw [Nat.cast_sub (by omega), hk2]
  have hnk1 : ((n - (t - 2) - 1 : ℕ) : ℝ) = n - ((t : ℝ) - 2) - 1 := by
    rw [Nat.cast_sub (by omega), hnk]; norm_num
  have hsub : ((Sa - SP : ℕ) : ℝ) = (Sa : ℝ) - SP := Nat.cast_sub hSPa
  have r1 : (cnt : ℝ) * (n * n * Kα) ≤ L * Kα * ((Sa - SP : ℕ) : ℝ) + n * n * SAl := by
    exact_mod_cast hcnt
  have r2 : ((16 * t * ((t - 2) * (t - 2)) : ℕ) : ℝ) ≤ Kα := by exact_mod_cast hKα
  have r3 : ((128 * (2 * t * (t - 2) + 10 * ((t - 2) * (t - 2)) * ((t - 2) * (t - 2)) +
      (t - 2) * (t - 2) * cG t + (9 + (t - 2) * (t - 2)) * (2 * ((t - 2) * (t - 2)) * t) +
      t * (t - 2) ^ 3) * L : ℕ) : ℝ) ≤ n := by exact_mod_cast hnC
  have r4 : (Sa : ℝ) = ((N * (t * n.choose 2) + SGm + (9 * n + n * ((t - 2) * (t - 2))) * SAl +
      N * (10 * (n * ((t - 2) * (t - 2)) * ((t - 2) * (t - 2)))) : ℕ) : ℝ) := by
    exact_mod_cast hSa
  have r5 : ((SAl * (n - 2 * t) : ℕ) : ℝ) ≤ ((N * (n * ((t - 2) * (t - 2))) * t : ℕ) : ℝ) := by
    exact_mod_cast hAl
  have r6 : (SGm : ℝ) ≤ ((N * (n * ((t - 2) * (t - 2))) * cG t : ℕ) : ℝ) := by exact_mod_cast hGm
  have r7 : ((N * B0c * (Gc * t.choose 2) : ℕ) : ℝ) ≤ ((SP * n.choose (t - 2) : ℕ) : ℝ) := by
    exact_mod_cast hP
  have r8 : ((2 * n * (t.choose 2 * (n - 1).choose (t - 1)) : ℕ) : ℝ) =
      ((t * (n - (t - 2)) * (n - (t - 2) - 1) * n.choose (t - 2) : ℕ) : ℝ) := by
    exact_mod_cast hbin
  have r9 : ((n - (t - 2) : ℕ) : ℝ) ≤ B0c := by exact_mod_cast hB0big
  have r10 : (0 : ℝ) < (n.choose (t - 2) : ℕ) := by exact_mod_cast hCnk
  push_cast at r2 r3 r4 r5 r6 r7 r8
  rw [hsub] at r1
  rw [hk2] at r2 r3 r4 r5 r6
  rw [hn2t] at r5
  rw [hnk, hnk1] at r8
  rw [hnk] at r9
  rw [Nat.cast_choose_two] at r4
  have := markov_real (n := n) (t := t) (L := L) (Kα := Kα) (N := N) (B0c := B0c) (Gc := Gc)
    (SAl := SAl) (SGm := SGm) (Sa := Sa) (SP := SP) (cnt := cnt) (c2t := (t.choose 2 : ℕ))
    (cn1 := ((n - 1).choose (t - 1) : ℕ)) (cnk := (n.choose (t - 2) : ℕ)) (cg := cG t)
    (by exact_mod_cast ht) (by exact_mod_cast hL1) (by exact_mod_cast hn4) (by positivity)
    (by positivity) (by positivity) (by positivity) r10 (by positivity) (by positivity)
    (by positivity) r2 r3 r9 r4 r5 r6 r7 r8 hG r1
  exact_mod_cast this

open scoped Classical in
theorem bad_count {t : ℕ} (ht : 4 ≤ t) {G : Finset (Finset (Fin n))} (hGt : ∀ E ∈ G, E.card = t)
    (hR : ¬ G.HasRepeatedDisjointUnion) (hL : LocStar t G) (h0 : Fin n) {L Kα : ℕ}
    (hL1 : 1 ≤ L) (hKα : 16 * t * ((t - 2) * (t - 2)) ≤ Kα)
    {B0 : Finset (Finset (Fin n))} (hB0 : ∀ A ∈ B0, A.card = t - 2)
    (hcol : ∃ col : ↥B0 → Fin (t - 2), ∀ A A' : ↥B0, col A = col A' → A = A' ∨ Disjoint A.1 A'.1)
    (hB0n : B0.card ≤ n) (hB0big : n - (t - 2) ≤ B0.card) (hB0ne : B0.Nonempty)
    (hn4 : 4 * t ≤ n)
    (hnC : 128 * (2 * t * (t - 2) + 10 * ((t - 2) * (t - 2)) * ((t - 2) * (t - 2)) +
      (t - 2) * (t - 2) * cG t + (9 + (t - 2) * (t - 2)) * (2 * ((t - 2) * (t - 2)) * t) +
      t * (t - 2) ^ 3) * L ≤ n)
    (hG : (1 - 1 / (64 * t * L : ℝ)) * (((n - 1).choose (t - 1) : ℕ) : ℝ) ≤ (G.card : ℝ)) :
    5 * ((univ : Finset (Equiv.Perm (Fin n))).filter (fun σ =>
      n * n < L * dQ G h0 t (imgB σ B0) ∨ Kα < (alphaO (cmp (imgB σ B0)) (Hc G h0 (imgB σ B0))).card)).card ≤
      Fintype.card (Equiv.Perm (Fin n)) := by
  set N := Fintype.card (Equiv.Perm (Fin n)) with hN
  set D := (t - 2) * (t - 2) with hD
  set k := t - 2 with hk
  set X : Equiv.Perm (Fin n) → Finset (Finset (Fin n)) := fun σ => imgB σ B0 with hX
  set Al : Equiv.Perm (Fin n) → ℕ := fun σ => (alphaO (cmp (X σ)) (Hc G h0 (X σ))).card with hAl
  set Gm : Equiv.Perm (Fin n) → ℕ := fun σ => ∑ p ∈ CPs (X σ), gam G h0 p.1 p.2 with hGm
  set P : Equiv.Perm (Fin n) → ℕ := fun σ => (proj G (X σ)).card with hP
  -- every placed block satisfies `P ≤ a`
  have hXprops : ∀ σ, (∀ A ∈ X σ, A.card = t - 2) ∧
      (∃ col : ↥(X σ) → Fin (t - 2), ∀ A A' : ↥(X σ), col A = col A' → A = A' ∨ Disjoint A.1 A'.1) ∧
      (X σ).card ≤ n ∧ (X σ).Nonempty := by
    intro σ
    refine ⟨imgB_mem_card σ hB0, imgB_col σ hcol, by rw [imgB_card]; exact hB0n, ?_⟩
    obtain ⟨A, hA⟩ := hB0ne
    exact ⟨img σ A, mem_image_of_mem _ hA⟩
  have hPa : ∀ σ, P σ ≤ aQ G h0 t (X σ) := by
    intro σ
    obtain ⟨h1, h2, h3, ⟨A, hA⟩⟩ := hXprops σ
    exact block_proj_le ht hR hL h0 h1 h2 h3 ⟨A, hA⟩
  -- per-σ Markov
  have hbad : ((univ : Finset (Equiv.Perm (Fin n))).filter (fun σ =>
      n * n < L * dQ G h0 t (X σ) ∨ Kα < Al σ)).card * (n * n * Kα) ≤
      L * Kα * ∑ σ, dQ G h0 t (X σ) + n * n * ∑ σ, Al σ := by
    rw [card_eq_sum_ones, sum_mul, sum_filter, mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro σ _
    split_ifs with h
    · rw [one_mul]
      rcases h with h | h
      · have : n * n * Kα ≤ L * dQ G h0 t (X σ) * Kα := Nat.mul_le_mul_right _ h.le
        rw [show L * dQ G h0 t (X σ) * Kα = L * Kα * dQ G h0 t (X σ) by ring] at this
        exact le_trans this (Nat.le_add_right _ _)
      · have : n * n * Kα ≤ n * n * Al σ := Nat.mul_le_mul_left _ h.le
        exact le_trans this (Nat.le_add_left _ _)
    · positivity
  -- averages
  have hCP : (CPs B0).card ≤ n * D := (CPs_card_le ht hB0 hcol).trans (Nat.mul_le_mul_right _ hB0n)
  have hAlsum : (∑ σ, Al σ) * (n - 2 * t) ≤ N * (n * D) * t :=
    (avg_alpha h0 hB0).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hCP))
  have hGmsum : ∑ σ, Gm σ ≤ N * (n * D) * cG t :=
    (avg_gam ht hGt hR h0 hn4 hB0).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hCP))
  have hPsum := avg_proj ht hGt hB0
  -- the sum of the deficits
  have hSd : ∑ σ, dQ G h0 t (X σ) = ∑ σ, aQ G h0 t (X σ) - ∑ σ, P σ :=
    sum_tsub_distrib _ (fun σ _ => hPa σ)
  have hpt : ∀ σ, aQ G h0 t (X σ) = t * n.choose 2 + Gm σ +
      (9 * (n * Al σ) + 10 * (n * D * D) + n * (D * Al σ)) := fun σ => rfl
  have hSa : ∑ σ, aQ G h0 t (X σ) = N * (t * n.choose 2) + ∑ σ, Gm σ +
      (9 * n + n * D) * ∑ σ, Al σ + N * (10 * (n * D * D)) := by
    rw [sum_congr rfl (fun σ _ => hpt σ)]
    simp only [sum_add_distrib, sum_const, card_univ, smul_eq_mul, ← hN]
    rw [← mul_sum, ← mul_sum, ← mul_sum, ← mul_sum]
    ring
  have hSPa : ∑ σ, P σ ≤ ∑ σ, aQ G h0 t (X σ) := sum_le_sum (fun σ _ => hPa σ)
  have hbin := binom_identity n t (by omega) (by omega)
  have hnk : n - t + 2 = n - k := by omega
  have hnk1 : n - t + 1 = n - k - 1 := by omega
  rw [hnk, hnk1] at hbin
  have hCnk : 0 < n.choose k := Nat.choose_pos (by omega)
  have hG' : (1 - 1 / (64 * t * L : ℝ)) * (((n - 1).choose (t - 1) : ℕ) : ℝ) ≤ (G.card : ℝ) := hG
  show 5 * ((univ : Finset (Equiv.Perm (Fin n))).filter (fun σ =>
    n * n < L * dQ G h0 t (X σ) ∨ Kα < Al σ)).card ≤ N
  have hD' : D = (t - 2) * (t - 2) := by rw [hD, hk]
  have hPsum' : N * B0.card * (G.card * t.choose 2) ≤ (∑ σ, P σ) * n.choose k := by
    rw [hk]; exact hPsum
  have hbin' : 2 * n * (t.choose 2 * (n - 1).choose (t - 1)) =
      t * (n - k) * (n - k - 1) * n.choose k := by rw [hk]; rw [hk] at hbin; exact hbin
  clear_value N D k X Al Gm P
  exact markov_arith ht hL1 hKα hn4 hnC hD' hk hB0big hSPa hSa hAlsum hGmsum hPsum' hbin' hCnk hG'
    (hSd ▸ hbad)


/-! ## Final assembly helpers -/

lemma exists_few_bad {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] (P : α → β → Prop)
    [∀ a b, Decidable (P a b)]
    (h : ∀ b, 5 * (univ.filter (fun a => P a b)).card ≤ Fintype.card α) :
    ∃ a, 5 * (univ.filter (fun b => P a b)).card ≤ Fintype.card β := by
  classical
  by_contra hcon
  push_neg at hcon
  have h1 : ∑ _a : α, Fintype.card β < ∑ a : α, 5 * (univ.filter (fun b => P a b)).card :=
    sum_lt_sum_of_nonempty univ_nonempty (fun a _ => hcon a)
  have h2 : ∑ a : α, (univ.filter (fun b => P a b)).card =
      ∑ b : β, (univ.filter (fun a => P a b)).card := by
    simp only [card_eq_sum_ones, sum_filter]; exact sum_comm
  have h3 : ∑ b : β, 5 * (univ.filter (fun a => P a b)).card ≤ ∑ _b : β, Fintype.card α :=
    sum_le_sum (fun b _ => h b)
  rw [← mul_sum, h2, mul_sum] at h1
  simp only [sum_const, card_univ, smul_eq_mul] at h1 h3
  have := lt_of_lt_of_le h1 h3
  rw [mul_comm] at this
  exact lt_irrefl _ this

open scoped Classical in
lemma card_meet_two (T1 : Finset (Fin n)) (k : ℕ) (hT1 : T1.card = k) :
    ((univ.powersetCard k).filter (fun T : Finset (Fin n) => 2 ≤ (T1 ∩ T).card)).card ≤
      k * k * n ^ (k - 2) := by
  have hsub : (univ.powersetCard k).filter (fun T : Finset (Fin n) => 2 ≤ (T1 ∩ T).card) ⊆
      T1.offDiag.biUnion (fun p => (univ.powersetCard k).filter
        (fun T : Finset (Fin n) => ({p.1, p.2} : Finset (Fin n)) ⊆ T)) := by
    intro T hT
    rw [mem_filter] at hT
    obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.1 (by omega : 1 < (T1 ∩ T).card)
    rw [mem_inter] at ha hb
    rw [mem_biUnion]
    refine ⟨(a, b), mem_offDiag.2 ⟨ha.1, hb.1, hab⟩, mem_filter.2 ⟨hT.1, ?_⟩⟩
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha.2
    · exact hb.2
  calc _ ≤ _ := card_le_card hsub
    _ ≤ ∑ p ∈ T1.offDiag, ((univ.powersetCard k).filter
          (fun T : Finset (Fin n) => ({p.1, p.2} : Finset (Fin n)) ⊆ T)).card := card_biUnion_le
    _ ≤ ∑ p ∈ T1.offDiag, n ^ (k - 2) := by
        apply sum_le_sum
        intro p hp
        have h2 : ({p.1, p.2} : Finset (Fin n)).card = 2 := card_pair (mem_offDiag.1 hp).2.2
        have := card_supersets_le' k ({p.1, p.2} : Finset (Fin n))
        rw [h2] at this
        convert this using 2
    _ ≤ k * k * n ^ (k - 2) := by
        rw [sum_const, smul_eq_mul, offDiag_card, hT1]
        exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)

lemma many_blocks {n k q : ℕ} (hk : 2 ≤ k) (hq0 : 5 * k ^ 3 * (2 * k) ^ (k - 2) + 6 * k ≤ q)
    (hn : n ≤ 2 * k * q) : k * (5 * (k * k * n ^ (k - 2)) + 6) ≤ q ^ (k - 1) := by
  have h1 : n ^ (k - 2) ≤ (2 * k) ^ (k - 2) * q ^ (k - 2) := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left hn _
  have h2 : 1 ≤ q ^ (k - 2) := Nat.one_le_pow _ _ (by omega)
  have h3 : q ^ (k - 1) = q * q ^ (k - 2) := by
    rw [← pow_succ']; congr 1; omega
  rw [h3]
  calc k * (5 * (k * k * n ^ (k - 2)) + 6)
      ≤ k * (5 * (k * k * ((2 * k) ^ (k - 2) * q ^ (k - 2))) + 6 * q ^ (k - 2)) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1))
          (by omega))
    _ = (5 * k ^ 3 * (2 * k) ^ (k - 2) + 6 * k) * q ^ (k - 2) := by ring
    _ ≤ q * q ^ (k - 2) := Nat.mul_le_mul_right _ hq0

lemma sqrt_bound {M P n : ℕ} (h : M * M * P ≤ n) : M * Nat.sqrt (P * n ^ 3) ≤ n * n := by
  have hs := Nat.sqrt_le (P * n ^ 3)
  have : (M * Nat.sqrt (P * n ^ 3)) * (M * Nat.sqrt (P * n ^ 3)) ≤ (n * n) * (n * n) := by
    calc (M * Nat.sqrt (P * n ^ 3)) * (M * Nat.sqrt (P * n ^ 3))
        = M * M * (Nat.sqrt (P * n ^ 3) * Nat.sqrt (P * n ^ 3)) := by ring
      _ ≤ M * M * (P * n ^ 3) := Nat.mul_le_mul_left _ hs
      _ = (M * M * P) * n ^ 3 := by ring
      _ ≤ n * n ^ 3 := Nat.mul_le_mul_right _ h
      _ = (n * n) * (n * n) := by ring
  exact Nat.mul_self_le_mul_self_iff.1 this

lemma size_conds {n L δ s b : ℕ} (hL : 1000 ≤ L) (hδ : L * δ ≤ n * n) (hs : L * s ≤ n * n)
    (hn : L * (b + 1) + 40 * b + 100 ≤ n) :
    16 * (4 * δ + (s + 1) + b * n) + (n - 8) * b + 3 * (n - 8) ≤ (n - 8) * n ∧
    L * (4 * δ + (s + 1) + b * n) ≤ 6 * (n * n) := by
  have hδ' : 1000 * δ ≤ n * n := le_trans (Nat.mul_le_mul_right _ hL) hδ
  have hs' : 1000 * s ≤ n * n := le_trans (Nat.mul_le_mul_right _ hL) hs
  constructor
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    rw [Nat.add_sub_cancel]
    have hm : 40 * b + 92 ≤ m := by omega
    have e2 : 40 * b * m ≤ m * m := Nat.mul_le_mul_right _ (by omega)
    have e3 : 92 * m ≤ m * m := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  · have a1 : L * (b + 1) ≤ n := by omega
    have a2 : L * (b + 1) * n ≤ n * n := Nat.mul_le_mul_right _ a1
    have hn1 : 1 ≤ n := by omega
    have a3 : L * 1 ≤ L * n := Nat.mul_le_mul_left _ hn1
    nlinarith

end OMA_H2

open Finset OMA_DL OMA_H2 in
open scoped Classical in
set_option maxHeartbeats 1600000 in
theorem OMA.solution : OMA.R_Erdos643_erdos_643_parts_ii_R1_H2_R1_H1_R1.H2 := by
  intro t ht γ hγ
  have ht2 : 2 ≤ t - 2 := by omega
  have hk0 : 0 < t - 2 := by omega
  obtain ⟨L, hLdef⟩ : ∃ L : ℕ, L = ⌈1728 / γ⌉₊ + 1000 := ⟨_, rfl⟩
  have hL1000 : 1000 ≤ L := by omega
  have hL1 : 1 ≤ L := by omega
  have hLγ : 1728 / γ ≤ (L : ℝ) := by
    have := Nat.le_ceil (1728 / γ)
    rw [hLdef]; push_cast; linarith
  obtain ⟨Kα, hKαdef⟩ : ∃ Kα : ℕ, Kα = 16 * t * ((t - 2) * (t - 2)) := ⟨_, rfl⟩
  have hKα : 16 * t * ((t - 2) * (t - 2)) ≤ Kα := hKαdef.ge
  obtain ⟨j2, hj2⟩ : ∃ j2 : ℕ, j2 = Kα * cJ t := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, b = Kα * cJ t * (t - 2) := ⟨_, rfl⟩
  obtain ⟨c0, hc0⟩ : ∃ c0 : ℕ, c0 = j2 * j2 + 2 + 2 * b := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℕ, P = cJ t * (2 + cJ t) := ⟨_, rfl⟩
  obtain ⟨Cn, hCn⟩ : ∃ Cn : ℕ, Cn = 128 * (2 * t * (t - 2) + 10 * ((t - 2) * (t - 2)) * ((t - 2) * (t - 2)) +
      (t - 2) * (t - 2) * cG t + (9 + (t - 2) * (t - 2)) * (2 * ((t - 2) * (t - 2)) * t) +
      t * (t - 2) ^ 3) * L := ⟨_, rfl⟩
  obtain ⟨q0, hq0⟩ : ∃ q0 : ℕ, q0 = 5 * (t - 2) ^ 3 * (2 * (t - 2)) ^ (t - 2 - 2) + 6 * (t - 2) :=
    ⟨_, rfl⟩
  obtain ⟨N24, hN24⟩ : ∃ N24 : ℕ, N24 = 24 * (j2 * j2 + 2) := ⟨_, rfl⟩
  obtain ⟨NLP, hNLP⟩ : ∃ NLP : ℕ, NLP = L * L * P := ⟨_, rfl⟩
  obtain ⟨NLb, hNLb⟩ : ∃ NLb : ℕ, NLb = L * (b + 1) := ⟨_, rfl⟩
  obtain ⟨Nq, hNq⟩ : ∃ Nq : ℕ, Nq = (t - 2) * (q0 + 1) := ⟨_, rfl⟩
  refine ⟨1 / (64 * t * L : ℝ), by positivity, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨4 * t + Cn + N24 + NLP + NLb + 40 * b + 100 + Nq + ⌈4 * (c0 : ℝ) / γ⌉₊ + 2 * c0 + 1,
    fun n hn => ?_⟩
  intro G hGu hR hG hLS
  have hGt : ∀ E ∈ G, E.card = t := fun E hE => hGu E hE
  have hL : LocStar t G := hLS
  have hn4 : 4 * t ≤ n := by omega
  have hnC : 128 * (2 * t * (t - 2) + 10 * ((t - 2) * (t - 2)) * ((t - 2) * (t - 2)) +
      (t - 2) * (t - 2) * cG t + (9 + (t - 2) * (t - 2)) * (2 * ((t - 2) * (t - 2)) * t) +
      t * (t - 2) ^ 3) * L ≤ n := by rw [← hCn]; omega
  have hn24 : 24 * ((Kα * cJ t) * (Kα * cJ t) + 2) ≤ n := by rw [← hj2, ← hN24]; omega
  have hnLP : L * L * P ≤ n := by rw [← hNLP]; omega
  have hnLb : L * (b + 1) + 40 * b + 100 ≤ n := by rw [← hNLb]; omega
  have hn16 : 16 ≤ n := by omega
  have hb4 : 4 * (b + 1) ≤ n := by
    have : 1000 * (b + 1) ≤ L * (b + 1) := Nat.mul_le_mul_right _ hL1000
    omega
  have hnc0 : 2 * c0 + 1 ≤ n := by omega
  have hnγ : 4 * (c0 : ℝ) ≤ γ * n := by
    have h1 := Nat.le_ceil (4 * (c0 : ℝ) / γ)
    have h2 : (⌈4 * (c0 : ℝ) / γ⌉₊ : ℝ) ≤ n := by exact_mod_cast (by omega : ⌈4 * (c0 : ℝ) / γ⌉₊ ≤ n)
    rw [div_le_iff₀ hγ] at h1
    nlinarith
  have hn0 : 0 < n := by omega
  -- blocks
  set q := n / (t - 2) with hqdef
  have hqq0 : q0 ≤ q := by
    rw [hqdef, Nat.le_div_iff_mul_le hk0]
    have : (t - 2) * (q0 + 1) ≤ n := by rw [← hNq]; omega
    nlinarith
  have hq : 0 < q := by omega
  have hkq : (t - 2) * q ≤ n := Nat.mul_div_le n (t - 2)
  have hnlt : n < (t - 2) * (q + 1) := by
    have := Nat.lt_mul_div_succ n hk0
    rw [hqdef]; linarith
  have hn2kq : n ≤ 2 * (t - 2) * q := by
    have h1 : t - 2 ≤ (t - 2) * q := Nat.le_mul_of_pos_right _ hq
    have h2 : n < (t - 2) * q + (t - 2) := by rw [mul_add, mul_one] at hnlt; exact hnlt
    have e : 2 * (t - 2) * q = (t - 2) * q + (t - 2) * q := by ring
    omega
  have hB0big : n - (t - 2) ≤ (t - 2) * q := by
    have : n < (t - 2) * q + (t - 2) := by rw [mul_add, mul_one] at hnlt; exact hnlt
    omega
  set M := (Reps hk0 hq).card / (t - 2) with hM
  obtain ⟨Zb, hZb⟩ : ∃ Zb : ℕ, Zb = (t - 2) * (t - 2) * n ^ (t - 2 - 2) := ⟨_, rfl⟩
  have hMbig : 5 * Zb + 6 ≤ M := by
    have h1 := many_blocks ht2 (hq0 ▸ hqq0) hn2kq
    have h2 := reps_card_ge hk0 hq
    have h3 := Nat.div_add_mod (Reps hk0 hq).card (t - 2)
    have h4 := Nat.mod_lt (Reps hk0 hq).card hk0
    rw [← hZb] at h1
    rw [← hM] at h3
    by_contra hcon
    push_neg at hcon
    have : (t - 2) * M + (t - 2) ≤ (t - 2) * (5 * Zb + 6) := by
      rw [← mul_add_one]; exact Nat.mul_le_mul_left _ (by omega)
    omega
  let h0 : Fin n := ⟨0, hn0⟩
  let XB : Equiv.Perm (Fin n) → Fin M → Finset (Finset (Fin n)) := fun σ β =>
    imgB σ (blk hkq hk0 hq β)
  let bad : Equiv.Perm (Fin n) → Fin M → Prop := fun σ β =>
    n * n < L * dQ G h0 t (XB σ β) ∨ Kα < (alphaO (cmp (XB σ β)) (Hc G h0 (XB σ β))).card
  have hblkne : ∀ β : Fin M, (blk hkq hk0 hq β).Nonempty := fun β =>
    card_pos.1 (by rw [blk_card]; positivity)
  have hbc : ∀ β, 5 * (univ.filter (fun σ => bad σ β)).card ≤ Fintype.card (Equiv.Perm (Fin n)) := by
    intro β
    exact bad_count ht hGt hR hL h0 hL1 hKα (B0 := blk hkq hk0 hq β) (fun A hA => blk_mem_card hA)
      (blk_col β) (by rw [blk_card]; exact hkq) (by rw [blk_card]; exact hB0big) (hblkne β) hn4 hnC hG
  obtain ⟨σ, hσ⟩ := exists_few_bad bad (h := hbc)
  rw [Fintype.card_fin] at hσ
  -- per-block outcome
  have hgood : ∀ β, ¬ bad σ β → ∃ S : Finset (Finset (Fin n)), ∃ W : Finset (Fin n),
      S ⊆ XB σ β ∧ (W.Nonempty → S.card = t - 2) ∧
      (∀ w ∈ W, ∀ w' ∈ W, w ≠ w' → ∀ c, Ctr t G w w' c → ∀ T ∈ S, c ∈ T) ∧
      (n : ℝ) - W.card ≤ 432 * n / L + (c0 : ℝ) := by
    intro β hβ
    simp only [bad, not_or, not_lt] at hβ
    obtain ⟨hβ1, hβ2⟩ := hβ
    have hXm : ∀ A ∈ XB σ β, A.card = t - 2 := imgB_mem_card σ (fun A hA => blk_mem_card hA)
    have hXc := imgB_col σ (blk_col (hkq := hkq) (hk := hk0) (hq := hq) β)
    have hXn : (XB σ β).card ≤ n := by
      show (imgB σ (blk hkq hk0 hq β)).card ≤ n
      rw [imgB_card, blk_card]; exact hkq
    obtain ⟨A, hA⟩ := hblkne β
    have hδ' : aQ G h0 t (XB σ β) ≤ (proj G (XB σ β)).card + dQ G h0 t (XB σ β) := by
      unfold dQ; omega
    have hsq : L * Nat.sqrt (n * cJ t * (2 * (n * n) + n * cJ t * n)) ≤ n * n := by
      have e : n * cJ t * (2 * (n * n) + n * cJ t * n) = P * n ^ 3 := by rw [hP]; ring
      rw [e]; exact sqrt_bound hnLP
    obtain ⟨hV3, hMis⟩ := size_conds hL1000 hβ1 hsq hnLb
    rw [hb] at hV3 hMis
    obtain ⟨S, W, x, m, h1, h2, h3, h4, h5⟩ := block_cluster ht hR hL h0 hXm hXc hXn
      ⟨img σ A, mem_image_of_mem _ hA⟩ hβ2 (dQ G h0 t (XB σ β)) hδ' hn24 hV3
    refine ⟨S.map (Function.Embedding.subtype _), W, ?_, ?_, ?_, ?_⟩
    · intro T hT
      obtain ⟨T', _, rfl⟩ := mem_map.1 hT
      exact T'.2
    · intro hW; rw [card_map]; exact h1 hW
    · intro w hw w' hw' hne c hc T hT
      obtain ⟨T', hT', rfl⟩ := mem_map.1 hT
      exact h2 w hw w' hw' hne c hc T' hT'
    · have := W_bound hL1000 hn16 (hb ▸ hb4) hMis h3 h4 h5
      rw [hc0, ← hj2, ← hb] at *
      convert this using 3 <;> simp [hj2, hb]
  choose! Sf Wf hSX hSc hctr hWb using hgood
  -- good blocks
  set Good := (univ : Finset (Fin M)).filter (fun β => ¬ bad σ β) with hGood
  have hGoodc : 4 * M ≤ 5 * Good.card := by
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin M))) (fun β => bad σ β)
    rw [card_univ, Fintype.card_fin] at this
    have hσ' : 5 * ((univ : Finset (Fin M)).filter (fun β => bad σ β)).card ≤ M := by
      convert hσ using 4
    rw [hGood]
    omega
  have hGne : Good.Nonempty := card_pos.1 (by omega)
  obtain ⟨β1, hβ1⟩ := hGne
  have hβ1' : ¬ bad σ β1 := (mem_filter.1 hβ1).2
  -- the first block is nonempty in `W`
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have h432 : 432 * (n : ℝ) / L ≤ 432 * n / 1000 := by
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
    exact_mod_cast hL1000
  have hW1ne : (Wf β1).Nonempty := by
    rw [← card_pos]
    have h1 := hWb β1 hβ1'
    have h2 : (2 * c0 + 1 : ℝ) ≤ n := by exact_mod_cast hnc0
    have : (0 : ℝ) < (Wf β1).card := by nlinarith
    exact_mod_cast this
  have hS1c := hSc β1 hβ1' hW1ne
  obtain ⟨T1, hT1⟩ : (Sf β1).Nonempty := card_pos.1 (by omega)
  have hT1c : T1.card = t - 2 := imgB_mem_card σ (fun A hA => blk_mem_card hA) T1 (hSX β1 hβ1' hT1)
  let I : Fin M → Finset (Fin n) := fun β => univ.filter (fun c => ∀ T ∈ Sf β, c ∈ T)
  set Z := Good.filter (fun β => (Wf β).Nonempty ∧ 2 ≤ (I β1 ∩ I β).card) with hZ
  have hZc : Z.card ≤ Zb := by
    have hex : ∀ β ∈ Z, ∃ T ∈ Sf β, True := by
      intro β hβ
      rw [mem_filter] at hβ
      have hg : ¬ bad σ β := (mem_filter.1 hβ.1).2
      have := hSc β hg hβ.2.1
      obtain ⟨T, hT⟩ := card_pos.1 (by omega : 0 < (Sf β).card)
      exact ⟨T, hT, trivial⟩
    choose! Tf hTf _ using hex
    rw [hZb]
    refine le_trans ?_ (card_meet_two T1 (t - 2) hT1c)
    apply card_le_card_of_injOn Tf
    · intro β hβ
      have hβ' := hβ
      rw [mem_coe, mem_filter] at hβ'
      have hg : ¬ bad σ β := (mem_filter.1 hβ'.1).2
      have hTX := hSX β hg (hTf β hβ)
      rw [mem_coe, mem_filter, mem_powersetCard]
      refine ⟨⟨subset_univ _, imgB_mem_card σ (fun A hA => blk_mem_card hA) _ hTX⟩, ?_⟩
      refine le_trans hβ'.2.2 (card_le_card ?_)
      intro c hc
      rw [mem_inter] at hc ⊢
      exact ⟨(mem_filter.1 hc.1).2 T1 hT1, (mem_filter.1 hc.2).2 _ (hTf β hβ)⟩
    · intro β hβ β' hβ' heq
      by_contra hne
      have hd := imgB_disjoint σ (blk_disjoint (hkq := hkq) (hk := hk0) (hq := hq) hne)
      have hg : ¬ bad σ β := (mem_filter.1 (mem_filter.1 hβ).1).2
      have hg' : ¬ bad σ β' := (mem_filter.1 (mem_filter.1 hβ').1).2
      have a1 := hSX β hg (hTf β hβ)
      have a2 := hSX β' hg' (hTf β' hβ')
      rw [heq] at a1
      exact disjoint_left.1 hd a1 a2
  obtain ⟨β2, hβ2G, hβ2Z⟩ : ∃ β2 ∈ Good, β2 ∉ Z := by
    by_contra hcon
    push_neg at hcon
    have : Good ⊆ Z := fun β hβ => hcon β hβ
    have := card_le_card this
    omega
  have hβ2' : ¬ bad σ β2 := (mem_filter.1 hβ2G).2
  -- the centre and the final set
  refine ⟨if h : (I β1 ∩ I β2).Nonempty then h.choose else h0, Wf β1 ∩ Wf β2, ?_, ?_⟩
  · have h1 := hWb β1 hβ1'
    have h2 := hWb β2 hβ2'
    have hu : (Wf β1 ∪ Wf β2).card ≤ n := by
      have := card_le_univ (Wf β1 ∪ Wf β2); rwa [Fintype.card_fin] at this
    have hui := card_union_add_card_inter (Wf β1) (Wf β2)
    have hR1 : ((Wf β1).card : ℝ) + (Wf β2).card ≤ n + (Wf β1 ∩ Wf β2).card := by
      exact_mod_cast (by omega : (Wf β1).card + (Wf β2).card ≤ n + (Wf β1 ∩ Wf β2).card)
    have hLg : 864 * (n : ℝ) / L ≤ γ * n / 2 := by
      rw [div_le_iff₀ hLpos]
      rw [div_le_iff₀ hγ] at hLγ
      have : (0 : ℝ) ≤ n := by positivity
      nlinarith
    have e : 432 * (n : ℝ) / L + 432 * n / L = 864 * n / L := by ring
    linarith
  · intro x hx y hy hxy
    rw [mem_inter] at hx hy
    obtain ⟨c, hc⟩ := hL x y hxy
    have hc1 : c ∈ I β1 := mem_filter.2 ⟨mem_univ _, hctr β1 hβ1' x hx.1 y hy.1 hxy c hc⟩
    have hc2 : c ∈ I β2 := mem_filter.2 ⟨mem_univ _, hctr β2 hβ2' x hx.2 y hy.2 hxy c hc⟩
    have hne : (I β1 ∩ I β2).Nonempty := ⟨c, mem_inter.2 ⟨hc1, hc2⟩⟩
    have hle : (I β1 ∩ I β2).card ≤ 1 := by
      by_contra h
      exact hβ2Z (mem_filter.2 ⟨hβ2G, ⟨x, hx.2⟩, by omega⟩)
    rw [dif_pos hne]
    have := card_le_one.1 hle c (mem_inter.2 ⟨hc1, hc2⟩) _ hne.choose_spec
    rw [← this]
    exact hc

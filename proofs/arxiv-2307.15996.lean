import OMAStatements.S_arxiv_2307_15996
import Mathlib

namespace OMA.P_arxiv_2307_15996

open OMA.S_arxiv_2307_15996

abbrev Cell := Fin 4 × Fin 6

private def adjB (u v : Cell) : Bool :=
  (u.1 == v.1 && (u.2.val + 1 == v.2.val || v.2.val + 1 == u.2.val)) ||
  (u.2 == v.2 && (u.1.val + 1 == v.1.val || v.1.val + 1 == u.1.val))

private lemma adjB_iff (u v : Cell) : adjB u v = true ↔ gridAdj u v := by
  unfold adjB gridAdj
  simp [Bool.or_eq_true, Bool.and_eq_true]

private def conn3B (a b c : Cell) : Bool :=
  (adjB a b && adjB b c) || (adjB b a && adjB a c) || (adjB a c && adjB c b)

private lemma gridAdj_symm {u v : Cell} (h : gridAdj u v) : gridAdj v u := by
  unfold gridAdj at h ⊢
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · exact Or.inl ⟨h1.symm, Or.inr h2⟩
  · exact Or.inl ⟨h1.symm, Or.inl h2⟩
  · exact Or.inr ⟨h1.symm, Or.inr h2⟩
  · exact Or.inr ⟨h1.symm, Or.inl h2⟩

private lemma isPolyomino3_of_triple (a b c : Cell)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hconn : conn3B a b c = true) :
    IsPolyomino 3 ({a, b, c} : Finset Cell) := by
  have hcard : ({a, b, c} : Finset Cell).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
        Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
  refine ⟨hcard, ⟨a, by simp⟩, ?_⟩
  let R : Cell → Cell → Prop := fun x y =>
    x ∈ ({a, b, c} : Finset Cell) ∧ y ∈ ({a, b, c} : Finset Cell) ∧ gridAdj x y
  have step : ∀ x y, x ∈ ({a, b, c} : Finset Cell) → y ∈ ({a, b, c} : Finset Cell) →
      gridAdj x y → Relation.ReflTransGen R x y :=
    fun x y hx hy hxy => Relation.ReflTransGen.single ⟨hx, hy, hxy⟩
  have ha : a ∈ ({a, b, c} : Finset Cell) := by simp
  have hb : b ∈ ({a, b, c} : Finset Cell) := by simp
  have hc : c ∈ ({a, b, c} : Finset Cell) := by simp
  have h3 : (gridAdj a b ∧ gridAdj b c) ∨ (gridAdj b a ∧ gridAdj a c) ∨ (gridAdj a c ∧ gridAdj c b) := by
    unfold conn3B at hconn
    simp only [Bool.or_eq_true, Bool.and_eq_true, adjB_iff] at hconn
    rcases hconn with (h1 | h2) | h3
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr h3)
  intro u hu v hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases h3 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have rab := step a b ha hb h1
    have rba := step b a hb ha (gridAdj_symm h1)
    have rbc := step b c hb hc h2
    have rcb := step c b hc hb (gridAdj_symm h2)
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    · exact .refl
    · exact rab
    · exact rab.trans rbc
    · exact rba
    · exact .refl
    · exact rbc
    · exact rcb.trans rba
    · exact rcb
    · exact .refl
  · have rba := step b a hb ha h1
    have rab := step a b ha hb (gridAdj_symm h1)
    have rac := step a c ha hc h2
    have rca := step c a hc ha (gridAdj_symm h2)
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    · exact .refl
    · exact rab
    · exact rac
    · exact rba
    · exact .refl
    · exact rba.trans rac
    · exact rca
    · exact rca.trans rab
    · exact .refl
  · have rac := step a c ha hc h1
    have rca := step c a hc ha (gridAdj_symm h1)
    have rcb := step c b hc hb h2
    have rbc := step b c hb hc (gridAdj_symm h2)
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    · exact .refl
    · exact rac.trans rcb
    · exact rac
    · exact rbc.trans rca
    · exact .refl
    · exact rbc
    · exact rca
    · exact rcb
    · exact .refl

private lemma conn3B_of_isPolyomino {a b c : Cell} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hP : IsPolyomino 3 ({a, b, c} : Finset Cell)) : conn3B a b c = true := by
  have hpath : ∀ u ∈ ({a, b, c} : Finset Cell), ∀ v ∈ ({a, b, c} : Finset Cell),
      u ≠ v → ∃ w ∈ ({a, b, c} : Finset Cell), w ≠ u ∧ gridAdj u w := by
    intro u hu v hv huv
    have hr := hP.2.2 u hu v hv
    rcases Relation.ReflTransGen.cases_head hr with rfl | ⟨y, ⟨_, hy, hxy⟩, _⟩
    · exact absurd rfl huv
    · have hne : y ≠ u := by
        intro heq; subst heq
        unfold gridAdj at hxy
        omega
      exact ⟨y, hy, hne, hxy⟩
  obtain ⟨wa, hwa, hwa_ne, hadja⟩ := hpath a (by simp) b (by simp) hab
  obtain ⟨wb, hwb, hwb_ne, hadjb⟩ := hpath b (by simp) a (by simp) hab.symm
  obtain ⟨wc, hwc, hwc_ne, hadjc⟩ := hpath c (by simp) a (by simp) hac.symm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hwa hwb hwc
  unfold conn3B
  simp only [Bool.or_eq_true, Bool.and_eq_true, adjB_iff]
  rcases hwa with rfl | rfl | rfl
  · exact absurd rfl hwa_ne
  · rcases hwc with rfl | rfl | rfl
    · exact Or.inl (Or.inr ⟨gridAdj_symm hadja, gridAdj_symm hadjc⟩)
    · exact Or.inl (Or.inl ⟨hadja, gridAdj_symm hadjc⟩)
    · exact absurd rfl hwc_ne
  · rcases hwb with rfl | rfl | rfl
    · exact Or.inl (Or.inr ⟨hadjb, hadja⟩)
    · exact absurd rfl hwb_ne
    · exact Or.inr ⟨hadja, gridAdj_symm hadjb⟩

/-- Explicit locked 8-tile 3-omino tiling of the `4 × 6` grid:
```
A C C C G G
A D D F F G
A B D F H H
B B E E E H
```
-/
private def tileL (k : Fin 8) : Cell × Cell × Cell :=
  match k.val with
  | 0 => ((0, 0), (1, 0), (2, 0))
  | 1 => ((2, 1), (3, 0), (3, 1))
  | 2 => ((0, 1), (0, 2), (0, 3))
  | 3 => ((1, 1), (1, 2), (2, 2))
  | 4 => ((3, 2), (3, 3), (3, 4))
  | 5 => ((1, 3), (1, 4), (2, 3))
  | 6 => ((0, 4), (0, 5), (1, 5))
  | 7 => ((2, 4), (2, 5), (3, 5))
  | _ => ((0, 0), (0, 1), (0, 2))

private def tileSet (t : Cell × Cell × Cell) : Finset Cell :=
  {t.1, t.2.1, t.2.2}

def T_locked : Finset (Finset Cell) :=
  Finset.univ.image (fun k : Fin 8 => tileSet (tileL k))

private def tileB (k : Fin 8) : Cell × Cell × Cell :=
  match k.val with
  | 0 => ((0, 0), (0, 1), (0, 2))
  | 1 => ((0, 3), (0, 4), (0, 5))
  | 2 => ((1, 0), (1, 1), (1, 2))
  | 3 => ((1, 3), (1, 4), (1, 5))
  | 4 => ((2, 0), (2, 1), (2, 2))
  | 5 => ((2, 3), (2, 4), (2, 5))
  | 6 => ((3, 0), (3, 1), (3, 2))
  | 7 => ((3, 3), (3, 4), (3, 5))
  | _ => ((0, 0), (0, 1), (0, 2))

def T_bars : Finset (Finset Cell) :=
  Finset.univ.image (fun k : Fin 8 => tileSet (tileB k))

lemma T_locked_valid : IsTiling 3 T_locked := by
  refine ⟨?_, ?_, ?_⟩
  · intro P hP
    rw [T_locked, Finset.mem_image] at hP
    obtain ⟨k, _, rfl⟩ := hP
    have hk : ∀ i : Fin 8,
        (tileL i).1 ≠ (tileL i).2.1 ∧ (tileL i).1 ≠ (tileL i).2.2 ∧
        (tileL i).2.1 ≠ (tileL i).2.2 ∧
        conn3B (tileL i).1 (tileL i).2.1 (tileL i).2.2 = true := by decide
    obtain ⟨h1, h2, h3, hc⟩ := hk k
    exact isPolyomino3_of_triple _ _ _ h1 h2 h3 hc
  · intro P hP Q hQ hne
    rw [T_locked, Finset.mem_image] at hP hQ
    obtain ⟨i, _, rfl⟩ := hP
    obtain ⟨j, _, rfl⟩ := hQ
    have hij : i ≠ j := fun h => hne (by rw [h])
    have hdisj : ∀ a b : Fin 8, a ≠ b → Disjoint (tileSet (tileL a)) (tileSet (tileL b)) := by
      decide
    exact hdisj i j hij
  · intro x
    have hcov : ∀ c : Cell, ∃ k : Fin 8, c ∈ tileSet (tileL k) := by decide
    obtain ⟨k, hk⟩ := hcov x
    exact ⟨tileSet (tileL k), Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩, hk⟩

lemma T_bars_valid : IsTiling 3 T_bars := by
  refine ⟨?_, ?_, ?_⟩
  · intro P hP
    rw [T_bars, Finset.mem_image] at hP
    obtain ⟨k, _, rfl⟩ := hP
    have hk : ∀ i : Fin 8,
        (tileB i).1 ≠ (tileB i).2.1 ∧ (tileB i).1 ≠ (tileB i).2.2 ∧
        (tileB i).2.1 ≠ (tileB i).2.2 ∧
        conn3B (tileB i).1 (tileB i).2.1 (tileB i).2.2 = true := by decide
    obtain ⟨h1, h2, h3, hc⟩ := hk k
    exact isPolyomino3_of_triple _ _ _ h1 h2 h3 hc
  · intro P hP Q hQ hne
    rw [T_bars, Finset.mem_image] at hP hQ
    obtain ⟨i, _, rfl⟩ := hP
    obtain ⟨j, _, rfl⟩ := hQ
    have hij : i ≠ j := fun h => hne (by rw [h])
    have hdisj : ∀ a b : Fin 8, a ≠ b → Disjoint (tileSet (tileB a)) (tileSet (tileB b)) := by
      decide
    exact hdisj i j hij
  · intro x
    have hcov : ∀ c : Cell, ∃ k : Fin 8, c ∈ tileSet (tileB k) := by decide
    obtain ⟨k, hk⟩ := hcov x
    exact ⟨tileSet (tileB k), Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩, hk⟩

lemma T_locked_ne_T_bars : T_locked ≠ T_bars := by
  intro h
  have hmem : tileSet (tileL 0) ∈ T_bars := by
    rw [← h]; exact Finset.mem_image.mpr ⟨0, Finset.mem_univ 0, rfl⟩
  have hnot : tileSet (tileL 0) ∉ T_bars := by decide
  exact hnot hmem

private lemma locked_triples_check :
    ∀ i j : Fin 8, i < j →
      let t1 := tileL i; let t2 := tileL j
      let c0 := t1.1; let c1 := t1.2.1; let c2 := t1.2.2
      let c3 := t2.1; let c4 := t2.2.1; let c5 := t2.2.2
      (conn3B c0 c1 c3 && conn3B c2 c4 c5) = false ∧
      (conn3B c0 c1 c4 && conn3B c2 c3 c5) = false ∧
      (conn3B c0 c1 c5 && conn3B c2 c3 c4) = false ∧
      (conn3B c0 c2 c3 && conn3B c1 c4 c5) = false ∧
      (conn3B c0 c2 c4 && conn3B c1 c3 c5) = false ∧
      (conn3B c0 c2 c5 && conn3B c1 c3 c4) = false ∧
      (conn3B c0 c3 c4 && conn3B c1 c2 c5) = false ∧
      (conn3B c0 c3 c5 && conn3B c1 c2 c4) = false ∧
      (conn3B c0 c4 c5 && conn3B c1 c2 c3) = false := by
  decide

private lemma pair_distinct_check :
    ∀ i j : Fin 8, i < j →
      let t1 := tileL i; let t2 := tileL j
      let c0 := t1.1; let c1 := t1.2.1; let c2 := t1.2.2
      let c3 := t2.1; let c4 := t2.2.1; let c5 := t2.2.2
      c0 ≠ c1 ∧ c0 ≠ c2 ∧ c0 ≠ c3 ∧ c0 ≠ c4 ∧ c0 ≠ c5 ∧
      c1 ≠ c2 ∧ c1 ≠ c3 ∧ c1 ≠ c4 ∧ c1 ≠ c5 ∧
      c2 ≠ c3 ∧ c2 ≠ c4 ∧ c2 ≠ c5 ∧
      c3 ≠ c4 ∧ c3 ≠ c5 ∧ c4 ≠ c5 := by
  decide

private lemma pair_disj_decide :
    ∀ i j : Fin 8, i ≠ j → Disjoint (tileSet (tileL i)) (tileSet (tileL j)) := by
  decide

private lemma sdiff_six {a b c d e f : Cell}
    (hda : d ≠ a) (hdb : d ≠ b) (hdc : d ≠ c)
    (hea : e ≠ a) (heb : e ≠ b) (hec : e ≠ c)
    (hfa : f ≠ a) (hfb : f ≠ b) (hfc : f ≠ c) :
    ({a, b, c, d, e, f} : Finset Cell) \ {a, b, c} = {d, e, f} := by
  ext z
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨rfl | rfl | rfl | rfl | rfl | rfl, hnot⟩ <;> simp_all
  · rintro (rfl | rfl | rfl) <;> simp_all

private lemma kill_split {a b c d e f : Cell} {A' B' : Finset Cell}
    (hA' : IsPolyomino 3 A') (hB' : IsPolyomino 3 B')
    (hAe : A' = {a, b, c}) (hBe : B' = {d, e, f})
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f)
    (hfalse : (conn3B a b c && conn3B d e f) = false) : False := by
  rw [hAe] at hA'; rw [hBe] at hB'
  have h1 := conn3B_of_isPolyomino hab hac hbc hA'
  have h2 := conn3B_of_isPolyomino hde hdf hef hB'
  rw [h1, h2] at hfalse
  exact Bool.noConfusion hfalse

private lemma pair_locked_six {c0 c1 c2 c3 c4 c5 : Cell} {A' B' : Finset Cell}
    (h01 : c0 ≠ c1) (h02 : c0 ≠ c2) (h03 : c0 ≠ c3) (h04 : c0 ≠ c4) (h05 : c0 ≠ c5)
    (h12 : c1 ≠ c2) (h13 : c1 ≠ c3) (h14 : c1 ≠ c4) (h15 : c1 ≠ c5)
    (h23 : c2 ≠ c3) (h24 : c2 ≠ c4) (h25 : c2 ≠ c5)
    (h34 : c3 ≠ c4) (h35 : c3 ≠ c5) (h45 : c4 ≠ c5)
    (hf1 : (conn3B c0 c1 c3 && conn3B c2 c4 c5) = false)
    (hf2 : (conn3B c0 c1 c4 && conn3B c2 c3 c5) = false)
    (hf3 : (conn3B c0 c1 c5 && conn3B c2 c3 c4) = false)
    (hf4 : (conn3B c0 c2 c3 && conn3B c1 c4 c5) = false)
    (hf5 : (conn3B c0 c2 c4 && conn3B c1 c3 c5) = false)
    (hf6 : (conn3B c0 c2 c5 && conn3B c1 c3 c4) = false)
    (hf7 : (conn3B c0 c3 c4 && conn3B c1 c2 c5) = false)
    (hf8 : (conn3B c0 c3 c5 && conn3B c1 c2 c4) = false)
    (hf9 : (conn3B c0 c4 c5 && conn3B c1 c2 c3) = false)
    (hA' : IsPolyomino 3 A') (hB' : IsPolyomino 3 B')
    (hdisj : Disjoint A' B')
    (hunion : A' ∪ B' = ({c0, c1, c2, c3, c4, c5} : Finset Cell))
    (hc0 : c0 ∈ A') :
    A' = ({c0, c1, c2} : Finset Cell) := by
  have hBeq : B' = ({c0, c1, c2, c3, c4, c5} : Finset Cell) \ A' := by
    rw [← hunion, Finset.union_sdiff_cancel_left hdisj]
  have herase_card : (A'.erase c0).card = 2 := by
    rw [Finset.card_erase_of_mem hc0, hA'.1]
  obtain ⟨x, y, hxy, herase⟩ := Finset.card_eq_two.mp herase_card
  have hAeq : A' = ({c0, x, y} : Finset Cell) := by
    rw [← Finset.insert_erase hc0, herase]
  have hx_mem : x ∈ ({c1, c2, c3, c4, c5} : Finset Cell) := by
    have hx1 : x ∈ A'.erase c0 := by rw [herase]; simp only [Finset.mem_insert, Finset.mem_singleton, true_or]
    have hxne : x ≠ c0 := (Finset.mem_erase.mp hx1).1
    have hxA : x ∈ A' := (Finset.mem_erase.mp hx1).2
    have hxU : x ∈ ({c0, c1, c2, c3, c4, c5} : Finset Cell) := by
      rw [← hunion]; exact Finset.mem_union_left _ hxA
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxU ⊢
    rcases hxU with rfl | hrest
    · exact absurd rfl hxne
    · exact hrest
  have hy_mem : y ∈ ({c1, c2, c3, c4, c5} : Finset Cell) := by
    have hy1 : y ∈ A'.erase c0 := by rw [herase]; simp only [Finset.mem_insert, Finset.mem_singleton, or_true]
    have hyne : y ≠ c0 := (Finset.mem_erase.mp hy1).1
    have hyA : y ∈ A' := (Finset.mem_erase.mp hy1).2
    have hyU : y ∈ ({c0, c1, c2, c3, c4, c5} : Finset Cell) := by
      rw [← hunion]; exact Finset.mem_union_left _ hyA
    simp only [Finset.mem_insert, Finset.mem_singleton] at hyU ⊢
    rcases hyU with rfl | hrest
    · exact absurd rfl hyne
    · exact hrest
  have hkill : ∀ a b c d e f : Cell,
      ({c0, x, y} : Finset Cell) = {a, b, c} →
      ({c0, c1, c2, c3, c4, c5} : Finset Cell) = {a, b, c, d, e, f} →
      a ≠ b → a ≠ c → b ≠ c → d ≠ e → d ≠ f → e ≠ f →
      d ≠ a → d ≠ b → d ≠ c → e ≠ a → e ≠ b → e ≠ c → f ≠ a → f ≠ b → f ≠ c →
      (conn3B a b c && conn3B d e f) = false → False := by
    intro a b c d e f hAa hUu hab hac hbc hde hdf hef hda hdb hdc hea heb hec hfa hfb hfc hff
    have hA'e : A' = {a, b, c} := hAeq.trans hAa
    have hB'e : B' = {d, e, f} := by
      rw [hBeq, hA'e, hUu]
      exact sdiff_six hda hdb hdc hea heb hec hfa hfb hfc
    exact kill_split hA' hB' hA'e hB'e hab hac hbc hde hdf hef hff
  have hU1 : ({c0, c1, c2, c3, c4, c5} : Finset Cell) = {c0, c1, c3, c2, c4, c5} := by
    rw [Finset.insert_comm c2 c3]
  have hU2 : ({c0, c1, c2, c3, c4, c5} : Finset Cell) = {c0, c1, c4, c2, c3, c5} := by
    rw [Finset.insert_comm c3 c4, Finset.insert_comm c2 c4]
  have hU3 : ({c0, c1, c2, c3, c4, c5} : Finset Cell) = {c0, c1, c5, c2, c3, c4} := by
    rw [Finset.pair_comm c4 c5, Finset.insert_comm c3 c5, Finset.insert_comm c2 c5]
  have hU4 : ({c0, c1, c2, c3, c4, c5} : Finset Cell) = {c0, c2, c3, c1, c4, c5} := by
    rw [Finset.insert_comm c1 c2, Finset.insert_comm c1 c3]
  have hU5 : ({c0, c1, c2, c3, c4, c5} : Finset Cell) = {c0, c2, c4, c1, c3, c5} := by
    rw [Finset.insert_comm c1 c2, Finset.insert_comm c3 c4, Finset.insert_comm c1 c4]
  have hU6 : ({c0, c1, c2, c3, c4, c5} : Finset Cell) = {c0, c2, c5, c1, c3, c4} := by
    rw [Finset.insert_comm c1 c2, Finset.pair_comm c4 c5, Finset.insert_comm c3 c5,
      Finset.insert_comm c1 c5]
  have hU7 : ({c0, c1, c2, c3, c4, c5} : Finset Cell) = {c0, c3, c4, c1, c2, c5} := by
    rw [Finset.insert_comm c2 c3, Finset.insert_comm c1 c3, Finset.insert_comm c2 c4,
      Finset.insert_comm c1 c4]
  have hU8 : ({c0, c1, c2, c3, c4, c5} : Finset Cell) = {c0, c3, c5, c1, c2, c4} := by
    rw [Finset.insert_comm c2 c3, Finset.insert_comm c1 c3, Finset.pair_comm c4 c5,
      Finset.insert_comm c2 c5, Finset.insert_comm c1 c5]
  have hU9 : ({c0, c1, c2, c3, c4, c5} : Finset Cell) = {c0, c4, c5, c1, c2, c3} := by
    rw [Finset.insert_comm c3 c4, Finset.insert_comm c2 c4, Finset.insert_comm c1 c4,
      Finset.pair_comm c3 c5, Finset.insert_comm c2 c5, Finset.insert_comm c1 c5]
  have hswap : ∀ p q : Cell, ({c0, p, q} : Finset Cell) = {c0, q, p} :=
    fun p q => by rw [Finset.pair_comm]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx_mem hy_mem
  rcases hx_mem with hx | hx | hx | hx | hx <;>
    rcases hy_mem with hy | hy | hy | hy | hy
  · exact absurd (hx.trans hy.symm) hxy
  · rw [hAeq, hx, hy]
  · exact False.elim (hkill c0 c1 c3 c2 c4 c5 (by rw [hx, hy]) hU1 h01 h03 h13 h24 h25 h45 h02.symm h12.symm h23 h04.symm h14.symm h34.symm h05.symm h15.symm h35.symm hf1)
  · exact False.elim (hkill c0 c1 c4 c2 c3 c5 (by rw [hx, hy]) hU2 h01 h04 h14 h23 h25 h35 h02.symm h12.symm h24 h03.symm h13.symm h34 h05.symm h15.symm h45.symm hf2)
  · exact False.elim (hkill c0 c1 c5 c2 c3 c4 (by rw [hx, hy]) hU3 h01 h05 h15 h23 h24 h34 h02.symm h12.symm h25 h03.symm h13.symm h35 h04.symm h14.symm h45 hf3)
  · rw [hAeq, hx, hy, hswap]
  · exact absurd (hx.trans hy.symm) hxy
  · exact False.elim (hkill c0 c2 c3 c1 c4 c5 (by rw [hx, hy]) hU4 h02 h03 h23 h14 h15 h45 h01.symm h12 h13 h04.symm h24.symm h34.symm h05.symm h25.symm h35.symm hf4)
  · exact False.elim (hkill c0 c2 c4 c1 c3 c5 (by rw [hx, hy]) hU5 h02 h04 h24 h13 h15 h35 h01.symm h12 h14 h03.symm h23.symm h34 h05.symm h25.symm h45.symm hf5)
  · exact False.elim (hkill c0 c2 c5 c1 c3 c4 (by rw [hx, hy]) hU6 h02 h05 h25 h13 h14 h34 h01.symm h12 h15 h03.symm h23.symm h35 h04.symm h24.symm h45 hf6)
  · exact False.elim (hkill c0 c1 c3 c2 c4 c5 (by rw [hx, hy, hswap]) hU1 h01 h03 h13 h24 h25 h45 h02.symm h12.symm h23 h04.symm h14.symm h34.symm h05.symm h15.symm h35.symm hf1)
  · exact False.elim (hkill c0 c2 c3 c1 c4 c5 (by rw [hx, hy, hswap]) hU4 h02 h03 h23 h14 h15 h45 h01.symm h12 h13 h04.symm h24.symm h34.symm h05.symm h25.symm h35.symm hf4)
  · exact absurd (hx.trans hy.symm) hxy
  · exact False.elim (hkill c0 c3 c4 c1 c2 c5 (by rw [hx, hy]) hU7 h03 h04 h34 h12 h15 h25 h01.symm h13 h14 h02.symm h23 h24 h05.symm h35.symm h45.symm hf7)
  · exact False.elim (hkill c0 c3 c5 c1 c2 c4 (by rw [hx, hy]) hU8 h03 h05 h35 h12 h14 h24 h01.symm h13 h15 h02.symm h23 h25 h04.symm h34.symm h45 hf8)
  · exact False.elim (hkill c0 c1 c4 c2 c3 c5 (by rw [hx, hy, hswap]) hU2 h01 h04 h14 h23 h25 h35 h02.symm h12.symm h24 h03.symm h13.symm h34 h05.symm h15.symm h45.symm hf2)
  · exact False.elim (hkill c0 c2 c4 c1 c3 c5 (by rw [hx, hy, hswap]) hU5 h02 h04 h24 h13 h15 h35 h01.symm h12 h14 h03.symm h23.symm h34 h05.symm h25.symm h45.symm hf5)
  · exact False.elim (hkill c0 c3 c4 c1 c2 c5 (by rw [hx, hy, hswap]) hU7 h03 h04 h34 h12 h15 h25 h01.symm h13 h14 h02.symm h23 h24 h05.symm h35.symm h45.symm hf7)
  · exact absurd (hx.trans hy.symm) hxy
  · exact False.elim (hkill c0 c4 c5 c1 c2 c3 (by rw [hx, hy]) hU9 h04 h05 h45 h12 h13 h23 h01.symm h14 h15 h02.symm h24 h25 h03.symm h34 h35 hf9)
  · exact False.elim (hkill c0 c1 c5 c2 c3 c4 (by rw [hx, hy, hswap]) hU3 h01 h05 h15 h23 h24 h34 h02.symm h12.symm h25 h03.symm h13.symm h35 h04.symm h14.symm h45 hf3)
  · exact False.elim (hkill c0 c2 c5 c1 c3 c4 (by rw [hx, hy, hswap]) hU6 h02 h05 h25 h13 h14 h34 h01.symm h12 h15 h03.symm h23.symm h35 h04.symm h24.symm h45 hf6)
  · exact False.elim (hkill c0 c3 c5 c1 c2 c4 (by rw [hx, hy, hswap]) hU8 h03 h05 h35 h12 h14 h24 h01.symm h13 h15 h02.symm h23 h25 h04.symm h34.symm h45 hf8)
  · exact False.elim (hkill c0 c4 c5 c1 c2 c3 (by rw [hx, hy, hswap]) hU9 h04 h05 h45 h12 h13 h23 h01.symm h14 h15 h02.symm h24 h25 h03.symm h34 h35 hf9)
  · exact absurd (hx.trans hy.symm) hxy

private lemma pair_locked_ordered {i j : Fin 8} (hij : i < j) {A' B' : Finset Cell}
    (hA' : IsPolyomino 3 A') (hB' : IsPolyomino 3 B')
    (hdisj : Disjoint A' B')
    (hunion : A' ∪ B' = tileSet (tileL i) ∪ tileSet (tileL j))
    (hc0 : (tileL i).1 ∈ A') :
    A' = tileSet (tileL i) := by
  obtain ⟨h01, h02, h03, h04, h05, h12, h13, h14, h15, h23, h24, h25, h34, h35, h45⟩ :=
    pair_distinct_check i j hij
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9⟩ := locked_triples_check i j hij
  have hU : tileSet (tileL i) ∪ tileSet (tileL j) =
      ({(tileL i).1, (tileL i).2.1, (tileL i).2.2, (tileL j).1, (tileL j).2.1, (tileL j).2.2} : Finset Cell) := by
    simp only [tileSet, Finset.insert_union, Finset.singleton_union]
  exact pair_locked_six h01 h02 h03 h04 h05 h12 h13 h14 h15 h23 h24 h25 h34 h35 h45
    hf1 hf2 hf3 hf4 hf5 hf6 hf7 hf8 hf9 hA' hB' hdisj (hunion.trans hU) hc0

private lemma pair_locked_any {i j : Fin 8} (hij : i ≠ j) {A' B' : Finset Cell}
    (hA' : IsPolyomino 3 A') (hB' : IsPolyomino 3 B')
    (hdisj : Disjoint A' B')
    (hunion : A' ∪ B' = tileSet (tileL i) ∪ tileSet (tileL j)) :
    A' = tileSet (tileL i) ∨ A' = tileSet (tileL j) := by
  have hlt_or : i < j ∨ j < i := lt_or_gt_of_ne hij
  rcases hlt_or with hlt | hgt
  · have hc0 : (tileL i).1 ∈ A' ∪ B' := by
      rw [hunion]; exact Finset.mem_union_left _ (by simp [tileSet])
    rcases Finset.mem_union.mp hc0 with hcA | hcB
    · exact Or.inl (pair_locked_ordered hlt hA' hB' hdisj hunion hcA)
    · have hBeq : B' = tileSet (tileL i) :=
        pair_locked_ordered hlt hB' hA' hdisj.symm (by rw [Finset.union_comm, hunion]) hcB
      have hdisj_ij := pair_disj_decide i j hij
      right
      calc A' = (A' ∪ B') \ B' := (Finset.union_sdiff_cancel_right hdisj).symm
        _ = (tileSet (tileL i) ∪ tileSet (tileL j)) \ tileSet (tileL i) := by rw [hunion, hBeq]
        _ = tileSet (tileL j) := Finset.union_sdiff_cancel_left hdisj_ij
  · have hunion' : A' ∪ B' = tileSet (tileL j) ∪ tileSet (tileL i) := by
      rw [hunion, Finset.union_comm]
    have hc0 : (tileL j).1 ∈ A' ∪ B' := by
      rw [hunion']; exact Finset.mem_union_left _ (by simp [tileSet])
    rcases Finset.mem_union.mp hc0 with hcA | hcB
    · exact Or.inr (pair_locked_ordered hgt hA' hB' hdisj hunion' hcA)
    · have hBeq : B' = tileSet (tileL j) :=
        pair_locked_ordered hgt hB' hA' hdisj.symm (by rw [Finset.union_comm, hunion']) hcB
      have hdisj_ji := pair_disj_decide j i hij.symm
      left
      calc A' = (A' ∪ B') \ B' := (Finset.union_sdiff_cancel_right hdisj).symm
        _ = (tileSet (tileL j) ∪ tileSet (tileL i)) \ tileSet (tileL j) := by rw [hunion', hBeq]
        _ = tileSet (tileL i) := Finset.union_sdiff_cancel_left hdisj_ji

lemma recom_step_from_locked {T' : Finset (Finset Cell)}
    (hstep : ReComStep 3 T_locked T') : T' = T_locked := by
  obtain ⟨A, hA, B, hB, hAB, A', B', hA', hB', hdisj, hunion, rfl⟩ := hstep
  rw [T_locked, Finset.mem_image] at hA hB
  obtain ⟨i, _, rfl⟩ := hA
  obtain ⟨j, _, rfl⟩ := hB
  have hij : i ≠ j := fun h => hAB (by rw [h])
  have hB'_eq : B' = (tileSet (tileL i) ∪ tileSet (tileL j)) \ A' := by
    rw [hunion, Finset.union_sdiff_cancel_left hdisj]
  have hcases := pair_locked_any hij hA' hB' hdisj hunion.symm
  have hdisj_ij := pair_disj_decide i j hij
  have hi_mem : tileSet (tileL i) ∈ T_locked :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hj_mem : tileSet (tileL j) ∈ T_locked :=
    Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
  rcases hcases with rfl | rfl
  · have hB'_j : B' = tileSet (tileL j) := by
      rw [hB'_eq, Finset.union_sdiff_cancel_left hdisj_ij]
    rw [hB'_j]
    ext X
    simp only [Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro (rfl | rfl | ⟨_, _, hX⟩)
      · exact hi_mem
      · exact hj_mem
      · exact hX
    · intro hX
      by_cases hXi : X = tileSet (tileL i)
      · exact Or.inl hXi
      · by_cases hXj : X = tileSet (tileL j)
        · exact Or.inr (Or.inl hXj)
        · exact Or.inr (Or.inr ⟨hXj, hXi, hX⟩)
  · have hB'_i : B' = tileSet (tileL i) := by
      rw [hB'_eq, Finset.union_comm, Finset.union_sdiff_cancel_left hdisj_ij.symm]
    rw [hB'_i]
    ext X
    simp only [Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro (rfl | rfl | ⟨_, _, hX⟩)
      · exact hj_mem
      · exact hi_mem
      · exact hX
    · intro hX
      by_cases hXj : X = tileSet (tileL j)
      · exact Or.inl hXj
      · by_cases hXi : X = tileSet (tileL i)
        · exact Or.inr (Or.inl hXi)
        · exact Or.inr (Or.inr ⟨hXj, hXi, hX⟩)

lemma recom_reach_from_locked {T' : Finset (Finset Cell)}
    (hreach : Relation.ReflTransGen (ReComStep 3) T_locked T') : T' = T_locked := by
  induction hreach with
  | refl => rfl
  | tail _ hstep ih =>
    subst ih
    exact recom_step_from_locked hstep

end OMA.P_arxiv_2307_15996

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2307_15996.main) := by
  intro h
  have hreach := h 4 6 3 (by norm_num) (by norm_num) (by norm_num)
    OMA.P_arxiv_2307_15996.T_locked OMA.P_arxiv_2307_15996.T_bars
    OMA.P_arxiv_2307_15996.T_locked_valid OMA.P_arxiv_2307_15996.T_bars_valid
  have heq := OMA.P_arxiv_2307_15996.recom_reach_from_locked hreach
  exact OMA.P_arxiv_2307_15996.T_locked_ne_T_bars heq.symm

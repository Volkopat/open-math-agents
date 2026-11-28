import OMAStatements.S_wp_conjecture

/-!
The construction is the complement of the 243-vertex ternary Golay graph used by
Adamczewski and Klostermeyer, *A Counterexample to an Eternal Domination Conjecture*
(arXiv:2609.11500). The direction vectors and the mathematical structure of the direct strategy
and three-colour obstruction are also described at github.com/tadamcz/gamma-theta.
-/

namespace OMA.GolayCounterexample

abbrev Vertex := Fin 5 → ZMod 3

def generators : List Vertex :=
  [![1, 0, 0, 0, 0], ![1, 1, 0, 0, 2], ![2, 2, 1, 0, 1], ![1, 0, 2, 1, 0],
   ![0, 0, 2, 1, 2], ![0, 1, 2, 0, 0], ![0, 0, 1, 0, 1], ![2, 0, 0, 2, 1],
   ![2, 2, 1, 2, 0], ![0, 1, 0, 1, 2], ![0, 2, 0, 2, 0]]

def directions : Finset Vertex := (generators ++ generators.map Neg.neg).toFinset

lemma mem_directions {x : Vertex} :
    x ∈ directions ↔ x ∈ generators ∨ -x ∈ generators := by
  simp only [directions, List.mem_toFinset, List.mem_append, List.mem_map]
  constructor
  · rintro (h | ⟨y, hy, he⟩)
    · exact Or.inl h
    · exact Or.inr (by rwa [← he, neg_neg])
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨-x, h, neg_neg _⟩

lemma neg_mem_directions {x : Vertex} : -x ∈ directions ↔ x ∈ directions := by
  rw [mem_directions, mem_directions, neg_neg, or_comm]

private lemma directions_no_zero : (0 : Vertex) ∉ directions := by decide +kernel

private lemma card_directions : directions.card = 22 := by decide +kernel

def H : SimpleGraph Vertex where
  Adj a b := b - a ∈ directions
  symm := ⟨by
    intro a b hab
    simpa only [neg_sub] using neg_mem_directions.mpr hab⟩
  loopless := ⟨by
    intro a ha
    exact directions_no_zero (by simpa only [sub_self] using ha)⟩

instance : DecidableRel H.Adj := fun _ _ ↦ inferInstanceAs (Decidable (_ ∈ directions))

@[simp] lemma adj_iff {a b : Vertex} : H.Adj a b ↔ b - a ∈ directions := Iff.rfl

def shift (a : Vertex) : Vertex ↪ Vertex := ⟨fun d => a + d, add_right_injective a⟩

@[simp] lemma shift_apply (a d : Vertex) : shift a d = a + d := rfl

def nbr (a : Vertex) : Finset Vertex := directions.map (shift a)

@[simp] lemma mem_nbr {a b : Vertex} : b ∈ nbr a ↔ H.Adj a b := by
  rw [nbr, Finset.mem_map, adj_iff]
  constructor
  · rintro ⟨d, hd, rfl⟩
    simpa [shift_apply] using hd
  · intro hb
    exact ⟨b - a, hb, by simp [shift_apply]⟩

@[simp] lemma card_nbr (a : Vertex) : (nbr a).card = 22 := by
  rw [nbr, Finset.card_map, card_directions]

def both (a b : Vertex) : Finset Vertex := nbr a ∩ nbr b

@[simp] lemma mem_both {a b z : Vertex} : z ∈ both a b ↔ H.Adj a z ∧ H.Adj b z := by
  simp [both]

def differenceCount (d : Vertex) : ℕ :=
  (directions.filter fun z => z - d ∈ directions).card

private def expectedCount (d : Vertex) : ℕ :=
  if d = 0 then 22 else if d ∈ directions then 1 else 2

-- The first two coordinates partition the finite count into nine checks, each with 27 cases.

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma differenceCount_zero_zero : ∀ c d e : ZMod 3,
    differenceCount ![0,0,c,d,e] = expectedCount ![0,0,c,d,e] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma differenceCount_zero_one : ∀ c d e : ZMod 3,
    differenceCount ![0,1,c,d,e] = expectedCount ![0,1,c,d,e] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma differenceCount_zero_two : ∀ c d e : ZMod 3,
    differenceCount ![0,2,c,d,e] = expectedCount ![0,2,c,d,e] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma differenceCount_one_zero : ∀ c d e : ZMod 3,
    differenceCount ![1,0,c,d,e] = expectedCount ![1,0,c,d,e] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma differenceCount_one_one : ∀ c d e : ZMod 3,
    differenceCount ![1,1,c,d,e] = expectedCount ![1,1,c,d,e] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma differenceCount_one_two : ∀ c d e : ZMod 3,
    differenceCount ![1,2,c,d,e] = expectedCount ![1,2,c,d,e] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma differenceCount_two_zero : ∀ c d e : ZMod 3,
    differenceCount ![2,0,c,d,e] = expectedCount ![2,0,c,d,e] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma differenceCount_two_one : ∀ c d e : ZMod 3,
    differenceCount ![2,1,c,d,e] = expectedCount ![2,1,c,d,e] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma differenceCount_two_two : ∀ c d e : ZMod 3,
    differenceCount ![2,2,c,d,e] = expectedCount ![2,2,c,d,e] := by
  decide +kernel

private lemma compute_differenceCount : ∀ a b c d e : ZMod 3,
    differenceCount ![a,b,c,d,e] =
      if (![a,b,c,d,e] : Vertex) = 0 then 22
      else if (![a,b,c,d,e] : Vertex) ∈ directions then 1 else 2 := by
  intro a b
  change ∀ c d e : ZMod 3,
    differenceCount ![a,b,c,d,e] = expectedCount ![a,b,c,d,e]
  fin_cases a <;> fin_cases b
  · exact differenceCount_zero_zero
  · exact differenceCount_zero_one
  · exact differenceCount_zero_two
  · exact differenceCount_one_zero
  · exact differenceCount_one_one
  · exact differenceCount_one_two
  · exact differenceCount_two_zero
  · exact differenceCount_two_one
  · exact differenceCount_two_two

private lemma differenceCount_eq (d : Vertex) :
    differenceCount d = if d = 0 then 22 else if d ∈ directions then 1 else 2 := by
  have hd : (![d 0, d 1, d 2, d 3, d 4] : Vertex) = d := by
    ext i
    fin_cases i <;> rfl
  simpa only [hd] using compute_differenceCount (d 0) (d 1) (d 2) (d 3) (d 4)

lemma card_both (a b : Vertex) (hne : a ≠ b) :
    (both a b).card = if H.Adj a b then 1 else 2 := by
  have hc : (directions.filter fun z => z - (b - a) ∈ directions).map
      (shift a) = both a b := by
    ext z
    simp only [Finset.mem_map, Finset.mem_filter, shift_apply,
      mem_both, adj_iff]
    constructor
    · rintro ⟨d, ⟨hd, hd'⟩, rfl⟩
      have h1 : a + d - a = d := by abel
      have h2 : a + d - b = d - (b - a) := by abel
      rwa [h1, h2, and_iff_right hd]
    · rintro ⟨h1, h2⟩
      refine ⟨z - a, ⟨h1, ?_⟩, by abel⟩
      convert h2 using 1
      abel
  rw [← hc, Finset.card_map, ← differenceCount, differenceCount_eq]
  rw [if_neg (sub_ne_zero.mpr hne.symm)]
  rfl


lemma common_exists {a b : Vertex} (hne : a ≠ b) :
    ∃ z, H.Adj a z ∧ H.Adj b z := by
  have hpos : 0 < (both a b).card := by
    rw [card_both a b hne]
    split <;> decide
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
  exact ⟨z, mem_both.mp hz⟩

lemma common_unique {a b x y : Vertex} (hab : H.Adj a b)
    (hax : H.Adj a x) (hbx : H.Adj b x) (hay : H.Adj a y) (hby : H.Adj b y) :
    x = y := by
  have hs : (both a b).card = 1 := by rw [card_both a b (H.ne_of_adj hab), if_pos hab]
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hs
  have hx : x ∈ both a b := mem_both.mpr ⟨hax, hbx⟩
  have hy : y ∈ both a b := mem_both.mpr ⟨hay, hby⟩
  rw [hz, Finset.mem_singleton] at hx hy
  exact hx.trans hy.symm

lemma reflecting_common {a b z : Vertex} (haz : H.Adj a z) (hbz : H.Adj b z) :
    H.Adj a (a + b - z) ∧ H.Adj b (a + b - z) := by
  rw [adj_iff, adj_iff]
  have ha : a + b - z - a = b - z := by abel
  have hb : a + b - z - b = a - z := by abel
  rw [ha, hb]
  exact ⟨adj_iff.mp (H.adj_symm hbz), adj_iff.mp (H.adj_symm haz)⟩

lemma doubled_injective : Function.Injective (fun v : Vertex => v + v) := by
  have localInjective : Function.Injective (fun x : ZMod 3 => x + x) := by decide +kernel
  intro a b hab
  funext i
  exact localInjective (congrFun hab i)

private lemma two_mem_exhaust {S : Finset Vertex} (hS : S.card ≤ 2)
    {x y z : Vertex} (hxy : x ≠ y) (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) :
    z = x ∨ z = y := by
  by_contra! hn
  have hsub : ({z, x, y} : Finset Vertex) ⊆ S := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    exacts [hz, hx, hy]
  have hc : ({z, x, y} : Finset Vertex).card = 3 := by simp [Finset.card_insert_of_notMem,
    hn.1, hn.2, hxy]
  have := Finset.card_le_card hsub
  omega

lemma common_pair_sum {a b x y : Vertex} (hab : a ≠ b) (hxy : x ≠ y)
    (hax : H.Adj a x) (hbx : H.Adj b x) (hay : H.Adj a y) (hby : H.Adj b y) :
    y = a + b - x := by
  have hc : (both a b).card ≤ 2 := by rw [card_both a b hab]; split <;> decide
  have hx : x ∈ both a b := mem_both.mpr ⟨hax, hbx⟩
  have hy : y ∈ both a b := mem_both.mpr ⟨hay, hby⟩
  have hrx : a + b - x ∈ both a b := mem_both.mpr (reflecting_common hax hbx)
  have hry : a + b - y ∈ both a b := mem_both.mpr (reflecting_common hay hby)
  rcases two_mem_exhaust hc hxy hx hy hrx with hxx | hyy
  · rcases two_mem_exhaust hc hxy hx hy hry with hyx | hyy
    · have he : a + b - x = a + b - y := hxx.trans hyx.symm
      have h : x = y := by
        calc
          x = a + b - (a + b - x) := by abel
          _ = a + b - (a + b - y) := by rw [he]
          _ = y := by abel
      exact (hxy h).elim
    · have hdouble : x + x = y + y := by
        calc
          x + x = (a + b - x) + x := by rw [hxx]
          _ = a + b := by abel
          _ = (a + b - y) + y := by abel
          _ = y + y := by rw [hyy]
      exact (hxy (doubled_injective hdouble)).elim
  · exact hyy.symm


open OMA.S_wp_conjecture

abbrev G := Hᶜ

lemma dom_iff {D : Finset Vertex} :
    IsDominating G D ↔ ∀ z, ¬ ∀ u ∈ D, H.Adj z u := by
  classical
  constructor
  · intro hd z hall
    rcases hd z with hz | ⟨u, hu, hg⟩
    · exact H.loopless.irrefl z (hall z hz)
    · exact ((H.compl_adj u z).mp hg).2 (H.adj_symm (hall u hu))
  · intro h z
    by_cases hz : z ∈ D
    · exact Or.inl hz
    · have hw := h z
      push Not at hw
      obtain ⟨u, hu, hzu⟩ := hw
      have hne : u ≠ z := fun he => hz (he ▸ hu)
      exact Or.inr ⟨u, hu, (H.compl_adj u z).mpr ⟨hne, fun hadj => hzu (H.adj_symm hadj)⟩⟩

lemma triple_dom_iff {a b c : Vertex} :
    IsDominating G {a,b,c} ↔ ∀ z, H.Adj z a → H.Adj z b → H.Adj z c → False := by
  rw [dom_iff]
  constructor
  · intro hd z ha hb hc
    apply hd z
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    exacts [ha, hb, hc]
  · intro hd z hz
    exact hd z (hz a (by simp)) (hz b (by simp)) (hz c (by simp))

lemma failure_witness {a b c : Vertex} (h : ¬ IsDominating G {a,b,c}) :
    ∃ z, H.Adj z a ∧ H.Adj z b ∧ H.Adj z c := by
  rw [triple_dom_iff] at h
  push Not at h
  simpa only [and_true] using h

private lemma dominates_two_adjacent_to_attack {r b c : Vertex} (hbc : b ≠ c)
    (hrb : H.Adj r b) (hrc : H.Adj r c) : IsDominating G {r,b,c} := by
  apply triple_dom_iff.mpr
  intro z hzr hzb hzc
  exact hbc (common_unique (H.adj_symm hzr) hrb hzb hrc hzc)

private lemma dominates_after_one_neighbor {r a b c : Vertex}
    (h : IsDominating G {a,b,c}) (hrb : H.Adj r b) :
    IsDominating G {r,b,c} ∨ IsDominating G {r,a,b} := by
  by_contra! hb
  obtain ⟨p, hpr, hpb, hpc⟩ := failure_witness hb.1
  obtain ⟨q, hqr, hqa, hqb⟩ := failure_witness hb.2
  have hpq : p = q := common_unique hrb (H.adj_symm hpr) (H.adj_symm hpb)
    (H.adj_symm hqr) (H.adj_symm hqb)
  exact triple_dom_iff.mp h p (hpq.symm ▸ hqa) hpb hpc

private lemma dominates_after_no_neighbors {r a b c : Vertex} (hrc : r ≠ c)
    (hra : r ≠ a) (hrb : r ≠ b) (h : IsDominating G {a,b,c}) :
    IsDominating G {r,b,c} ∨ IsDominating G {r,a,c} ∨ IsDominating G {r,a,b} := by
  by_contra! hb
  obtain ⟨p, hpr, hpb, hpc⟩ := failure_witness hb.1
  obtain ⟨q, hqr, hqa, hqc⟩ := failure_witness hb.2.1
  obtain ⟨s, hsr, hsa, hsb⟩ := failure_witness hb.2.2
  have hpq : p ≠ q := fun e => triple_dom_iff.mp h q hqa (e ▸ hpb) hqc
  have hps : p ≠ s := fun e => triple_dom_iff.mp h s hsa hsb (e ▸ hpc)
  have hqs : q ≠ s := fun e => triple_dom_iff.mp h s hsa hsb (e ▸ hqc)
  have ha : a = q + s - r := common_pair_sum hqs hra hqr hsr hqa hsa
  have hb : b = p + s - r := common_pair_sum hps hrb hpr hsr hpb hsb
  have hc : c = p + q - r := common_pair_sum hpq hrc hpr hqr hpc hqc
  let v := p + q + s - r - r
  have hva : a - v = r - p := by dsimp [v]; rw [ha]; abel
  have hvb : b - v = r - q := by dsimp [v]; rw [hb]; abel
  have hvc : c - v = r - s := by dsimp [v]; rw [hc]; abel
  exact triple_dom_iff.mp h v (adj_iff.mpr (hva.symm ▸ adj_iff.mp hpr))
    (adj_iff.mpr (hvb.symm ▸ adj_iff.mp hqr)) (adj_iff.mpr (hvc.symm ▸ adj_iff.mp hsr))

private lemma permute_dom {a b c a' b' c' : Vertex}
    (h : IsDominating G {a,b,c}) (he : ({a,b,c} : Finset Vertex) = {a',b',c'}) :
    IsDominating G {a',b',c'} := he ▸ h

private lemma choose_defender {r a b c : Vertex} (hra : r ≠ a)
    (hrb : r ≠ b) (hrc : r ≠ c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : IsDominating G {a,b,c}) :
    (¬ H.Adj r a ∧ IsDominating G {r,b,c}) ∨
      (¬ H.Adj r b ∧ IsDominating G {r,a,c}) ∨
      (¬ H.Adj r c ∧ IsDominating G {r,a,b}) := by
  by_cases ha : H.Adj r a <;> by_cases hb : H.Adj r b <;> by_cases hc : H.Adj r c
  · exact (triple_dom_iff.mp h r ha hb hc).elim
  · exact Or.inr (Or.inr ⟨hc, dominates_two_adjacent_to_attack hab ha hb⟩)
  · exact Or.inr (Or.inl ⟨hb, dominates_two_adjacent_to_attack hac ha hc⟩)
  · have hp : IsDominating G {b,a,c} := permute_dom h (by
      ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
    rcases dominates_after_one_neighbor hp ha with h1 | h2
    · exact Or.inr (Or.inl ⟨hb, h1⟩)
    · exact Or.inr (Or.inr ⟨hc, permute_dom h2 (by
        ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)⟩)
  · exact Or.inl ⟨ha, dominates_two_adjacent_to_attack hbc hb hc⟩
  · rcases dominates_after_one_neighbor h hb with h1 | h2
    · exact Or.inl ⟨ha, h1⟩
    · exact Or.inr (Or.inr ⟨hc, h2⟩)
  · have hp : IsDominating G {a,c,b} := permute_dom h (by
      ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
    rcases dominates_after_one_neighbor hp hc with h1 | h2
    · exact Or.inl ⟨ha, permute_dom h1 (by
        ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)⟩
    · exact Or.inr (Or.inl ⟨hb, h2⟩)
  · rcases dominates_after_no_neighbors hrc hra hrb h with h1 | h2 | h3
    · exact Or.inl ⟨ha, h1⟩
    · exact Or.inr (Or.inl ⟨hb, h2⟩)
    · exact Or.inr (Or.inr ⟨hc, h3⟩)

lemma nonempty_dom_triples : {D : Finset Vertex | D.card = 3 ∧ IsDominating G D}.Nonempty := by
  let a : Vertex := 0
  let b : Vertex := ![1,0,0,0,0]
  have hab : H.Adj a b := by decide +kernel
  obtain ⟨c, hac, hbc⟩ := common_exists (H.ne_of_adj hab)
  refine ⟨{a,b,c}, ?_, ?_⟩
  · exact Finset.card_eq_three.mpr
      ⟨a, b, c, H.ne_of_adj hab, H.ne_of_adj hac, H.ne_of_adj hbc, rfl⟩
  · apply triple_dom_iff.mpr
    intro z hza hzb hzc
    have he := common_unique hab hac hbc (H.adj_symm hza) (H.adj_symm hzb)
    exact (H.ne_of_adj hzc) he.symm

lemma dominates_three_guard_family :
    IsEternalFamily G 3 {D : Finset Vertex | D.card = 3 ∧ IsDominating G D} := by
  classical
  refine ⟨nonempty_dom_triples, fun _ h => h, ?_⟩
  intro D hD r hr
  obtain ⟨hcard, hdom⟩ := hD
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcard
  have hra : r ≠ a := fun e => hr (by simp [e])
  have hrb : r ≠ b := fun e => hr (by simp [e])
  have hrc : r ≠ c := fun e => hr (by simp [e])
  have flipMove : ∀ u, r ≠ u → ¬ H.Adj r u → G.Adj u r :=
    fun u hne hnon => (H.compl_adj u r).mpr ⟨hne.symm, fun hu => hnon (H.adj_symm hu)⟩
  rcases choose_defender hra hrb hrc hab hac hbc hdom with ha | hb | hc
  · refine ⟨a, by simp, flipMove a hra ha.1, ?_⟩
    change (insert r (({a,b,c} : Finset Vertex).erase a)).card = 3 ∧ _
    have he : ({a,b,c} : Finset Vertex).erase a = {b,c} := by
      simp [Finset.erase_insert, Finset.erase_eq_of_notMem, hab, hac]
    simpa only [he] using And.intro
      (Finset.card_eq_three.mpr ⟨r,b,c,hrb,hrc,hbc,rfl⟩) ha.2
  · refine ⟨b, by simp, flipMove b hrb hb.1, ?_⟩
    change (insert r (({a,b,c} : Finset Vertex).erase b)).card = 3 ∧ _
    have he : ({a,b,c} : Finset Vertex).erase b = {a,c} := by
      simp [Finset.erase_insert_of_ne, Finset.erase_insert, Finset.erase_eq_of_notMem,
        hab, hbc]
    simpa only [he] using And.intro
      (Finset.card_eq_three.mpr ⟨r,a,c,hra,hrc,hac,rfl⟩) hb.2
  · refine ⟨c, by simp, flipMove c hrc hc.1, ?_⟩
    change (insert r (({a,b,c} : Finset Vertex).erase c)).card = 3 ∧ _
    have he : ({a,b,c} : Finset Vertex).erase c = {a,b} := by
      simp [Finset.erase_insert_of_ne, hac, hbc]
    simpa only [he] using And.intro
      (Finset.card_eq_three.mpr ⟨r,a,b,hra,hrb,hab,rfl⟩) hc.2

lemma card_ge_three_of_dom {D : Finset Vertex} (hDom : IsDominating G D) : 3 ≤ D.card := by
  by_contra! hc
  have disallow := dom_iff.mp hDom
  rcases (show D.card = 0 ∨ D.card = 1 ∨ D.card = 2 by omega) with h0 | h1 | h2
  · have he := Finset.card_eq_zero.mp h0
    subst D
    exact disallow 0 (by simp)
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
    obtain ⟨z, hz⟩ := Finset.card_pos.mp (by rw [card_nbr]; decide : 0 < (nbr a).card)
    exact disallow z (by simpa using H.adj_symm (mem_nbr.mp hz))
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
    obtain ⟨z, hza, hzb⟩ := common_exists hab
    apply disallow z
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    exacts [H.adj_symm hza, H.adj_symm hzb]

lemma domination_three : dominationNumber G = 3 := by
  obtain ⟨D, hc, hd⟩ := nonempty_dom_triples
  apply le_antisymm
  · exact Nat.sInf_le ⟨D, hc, hd⟩
  · exact le_csInf ⟨3, D, hc, hd⟩ fun _ ⟨E, hE, hdE⟩ => hE ▸ card_ge_three_of_dom hdE

lemma everlasting_three : eternalDominationNumber G = 3 := by
  let F : Set (Finset Vertex) := {D | D.card = 3 ∧ IsDominating G D}
  apply le_antisymm
  · exact Nat.sInf_le ⟨F, dominates_three_guard_family⟩
  · refine le_csInf ⟨3, F, dominates_three_guard_family⟩ ?_
    rintro k ⟨J, hnon, hdom, -⟩
    obtain ⟨D, hD⟩ := hnon
    obtain ⟨hc, hd⟩ := hdom D hD
    exact hc ▸ card_ge_three_of_dom hd

end OMA.GolayCounterexample


/-! Two incidence counts ruling out a three-coloring of the ternary Golay graph. -/

namespace OMA.GolayColoring

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (H : SimpleGraph V) [DecidableRel H.Adj] (nbr : V → Finset V)
variable (hmem : ∀ {a b}, b ∈ nbr a ↔ H.Adj a b)
  (hdeg : ∀ a, (nbr a).card = 22)
  (hcommon : ∀ a b, a ≠ b → (nbr a ∩ nbr b).card = if H.Adj a b then 1 else 2)

private theorem third_color (a b c i : Fin 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hai : a ≠ i) (hbi : b ≠ i) : c = i := by
  have neVal {u v : Fin 3} (h : u ≠ v) : u.val ≠ v.val := fun he => h (Fin.ext he)
  have h₁ := neVal hab
  have h₂ := neVal hac
  have h₃ := neVal hbc
  have h₄ := neVal hai
  have h₅ := neVal hbi
  apply Fin.ext
  omega

omit [Fintype V] in
include hmem hdeg hcommon in
private theorem card_neighbors_of_other_color
    (c : V → Fin 3) (hc : ∀ a b, H.Adj a b → c a ≠ c b)
    (a : V) (i : Fin 3) (hai : c a ≠ i) :
    ((nbr a).filter fun b => c b = i).card = 11 := by
  classical
  have hmate (u : V) (hu : u ∈ nbr a) : ∃ z, z ∈ nbr a ∧ z ∈ nbr u := by
    have hau := hmem.mp hu
    have hz : (nbr a ∩ nbr u).card = 1 := by
      rw [hcommon a u (H.ne_of_adj hau), if_pos hau]
    obtain ⟨z, hz'⟩ := Finset.card_pos.mp (by omega : 0 < (nbr a ∩ nbr u).card)
    exact ⟨z, Finset.mem_inter.mp hz'⟩
  choose mate hmate using hmate
  have huniq (u : V) (hu : u ∈ nbr a) {z w : V}
      (hz : z ∈ nbr a ∩ nbr u) (hw : w ∈ nbr a ∩ nbr u) : z = w := by
    have hau := hmem.mp hu
    have h1 : (nbr a ∩ nbr u).card = 1 := by
      rw [hcommon a u (H.ne_of_adj hau), if_pos hau]
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h1
    rw [hv, Finset.mem_singleton] at hz hw
    exact hz.trans hw.symm
  have hinvol (u : V) (hu : u ∈ nbr a) : mate (mate u hu) (hmate u hu).1 = u := by
    apply huniq (mate u hu) (hmate u hu).1
    · exact Finset.mem_inter.mpr (hmate _ _)
    · exact Finset.mem_inter.mpr ⟨hu, hmem.mpr ((hmem.mp (hmate u hu).2).symm)⟩
  have hcolor (u : V) (hu : u ∈ nbr a) : c (mate u hu) = i ↔ c u ≠ i := by
    have hau := hc _ _ (hmem.mp hu)
    have haz := hc _ _ (hmem.mp (hmate u hu).1)
    have huz := hc _ _ (hmem.mp (hmate u hu).2)
    constructor
    · intro he hu'
      exact huz (hu'.trans he.symm)
    · intro hu'
      exact third_color (c a) (c u) (c (mate u hu)) i hau haz huz hai hu'
  let s := (nbr a).filter fun b => c b = i
  let t := (nbr a).filter fun b => c b ≠ i
  have heq : s.card = t.card := by
    refine Finset.card_bij'
      (fun u hu => mate u (Finset.mem_filter.mp hu).1)
      (fun u hu => mate u (Finset.mem_filter.mp hu).1) ?_ ?_ ?_ ?_
    · intro u hu
      obtain ⟨huN, huI⟩ := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr ⟨(hmate u huN).1,
        fun he => ((hcolor u huN).mp he) huI⟩
    · intro u hu
      obtain ⟨huN, huI⟩ := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr ⟨(hmate u huN).1, (hcolor u huN).mpr huI⟩
    · intro u hu
      exact hinvol u (Finset.mem_filter.mp hu).1
    · intro u hu
      exact hinvol u (Finset.mem_filter.mp hu).1
  have hsum : s.card + t.card = (nbr a).card :=
    Finset.card_filter_add_card_filter_not _
  rw [hdeg] at hsum
  change s.card = 11
  omega

omit [Fintype V] in
include hmem in
private theorem sum_card_inter_comm (A B : Finset V) :
    ∑ u ∈ A, (nbr u ∩ B).card = ∑ v ∈ B, (nbr v ∩ A).card := by
  classical
  have he (u : V) (T : Finset V) : nbr u ∩ T = T.filter (H.Adj u) := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_filter, hmem, and_comm]
  simp_rw [he, Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro u _
  simp only [H.adj_comm (u := u) (v := v)]

include hmem hdeg hcommon in
/-- A 243-vertex graph with Golay intersection numbers has no three-coloring. -/
theorem no_three_coloring (hsize : Fintype.card V = 243) :
    ¬ ∃ c : V → Fin 3, ∀ a b, H.Adj a b → c a ≠ c b := by
  classical
  rintro ⟨c, hc⟩
  have hnon : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨x⟩ := hnon
  let i := c x
  let C : Finset V := univ.filter fun y => c y = i
  let O : Finset V := univ.filter fun y => c y ≠ i
  have hC (y : V) : y ∈ C ↔ c y = i := by simp [C]
  have hO (y : V) : y ∈ O ↔ c y ≠ i := by simp [O]
  have hXC : x ∈ C := (hC x).mpr rfl
  have hpart : C.card + O.card = 243 := by
    simpa [C, O, hsize] using
      (Finset.card_filter_add_card_filter_not (s := (univ : Finset V)) (fun y => c y = i))
  have hInside (y : V) (hy : y ∈ C) : nbr y ∩ O = nbr y := by
    apply Finset.inter_eq_left.mpr
    intro u hu
    exact (hO u).mpr (fun he => (hc _ _ (hmem.mp hu)) (((hC y).mp hy).trans he.symm))
  have hOutside (u : V) (hu : u ∈ O) : (nbr u ∩ C).card = 11 := by
    have he : nbr u ∩ C = (nbr u).filter (fun y => c y = i) := by
      ext y
      simp only [Finset.mem_inter, Finset.mem_filter, hC]
    rw [he]
    exact card_neighbors_of_other_color H nbr hmem hdeg hcommon c hc u i ((hO u).mp hu)
  have hh := sum_card_inter_comm H nbr hmem C O
  rw [Finset.sum_const_nat (m := 22) (fun v hv => by rw [hInside v hv, hdeg]),
    Finset.sum_const_nat (m := 11) hOutside] at hh
  have hCcard : C.card = 81 := by omega
  have hLeft (u : V) (hu : u ∈ nbr x) : (nbr u ∩ C.erase x).card = 10 := by
    have huo : u ∈ O := (hO u).mpr (fun he => hc _ _ (hmem.mp hu) he.symm)
    have hxe : x ∈ nbr u ∩ C := Finset.mem_inter.mpr ⟨hmem.mpr ((hmem.mp hu).symm), hXC⟩
    have hEr : nbr u ∩ C.erase x = (nbr u ∩ C).erase x := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_erase]
      tauto
    rw [hEr, Finset.card_erase_of_mem hxe, hOutside u huo]
  have hRight (v : V) (hv : v ∈ C.erase x) : (nbr v ∩ nbr x).card = 2 := by
    obtain ⟨hvx, hvC⟩ := Finset.mem_erase.mp hv
    have hn : ¬ H.Adj v x := fun ha => (hc _ _ ha) ((hC v).mp hvC)
    rw [hcommon v x hvx, if_neg hn]
  have h₂ := sum_card_inter_comm H nbr hmem (nbr x) (C.erase x)
  rw [Finset.sum_const_nat (m := 10) hLeft, Finset.sum_const_nat (m := 2) hRight,
    hdeg, Finset.card_erase_of_mem hXC, hCcard] at h₂
  norm_num at h₂

end OMA.GolayColoring



/-! A lower clique-cover bound from the non-colorability of the complementary graph. -/

namespace GammaThetaCliqueBound

open OMA.S_wp_conjecture

variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem clique_cover_gt_three (H : SimpleGraph V)
    (h : ¬ ∃ c : V → Fin 3, ∀ u v, H.Adj u v → c u ≠ c v) :
    3 < cliqueCoverNumber Hᶜ := by
  let K : Set ℕ := {k | ∃ f : V → Fin k, ∀ u v : V, u ≠ v → f u = f v → Hᶜ.Adj u v}
  have hNonempty : K.Nonempty := by
    refine ⟨Fintype.card V, Fintype.equivFin V, ?_⟩
    intro u v huv huvColor
    exact (huv ((Fintype.equivFin V).injective huvColor)).elim
  have hs : sInf K ∈ K := Nat.sInf_mem hNonempty
  by_contra! hSmall
  change sInf K ≤ 3 at hSmall
  obtain ⟨f, hf⟩ := hs
  apply h
  refine ⟨Fin.castLE hSmall ∘ f, ?_⟩
  intro u v hadj heq
  have hfEq : f u = f v := (Fin.castLE_injective hSmall) heq
  exact ((H.compl_adj u v).mp (hf u v (H.ne_of_adj hadj) hfEq)).2 hadj

end GammaThetaCliqueBound



open OMA.GolayCounterexample

theorem OMA.solution : type_of% @OMA.S_wp_conjecture.main := by
  have hsize : Fintype.card Vertex = 243 := by
    norm_num [Vertex, Fintype.card_fun, ZMod.card]
  have hnocolor := OMA.GolayColoring.no_three_coloring H nbr
    (fun {a b} => mem_nbr (a := a) (b := b)) card_nbr
    (fun a b h => card_both a b h) hsize
  have hclique := GammaThetaCliqueBound.clique_cover_gt_three H hnocolor
  exact ⟨Vertex, inferInstance, inferInstance, G, domination_three.trans everlasting_three.symm,
    domination_three.symm ▸ hclique⟩

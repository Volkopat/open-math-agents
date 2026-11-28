import FormalConjectures.Paper.ApproximatelyStableMatching
import Mathlib.Tactic

-- === FanelliMoscardelli/MatchingTools.lean ===


namespace FanelliMoscardelliProof

variable {V : Type*} [DecidableEq V]

/-- An involution restricted to a finite set, with an assignment constraint on that set. -/
def Pairs (S : Finset V) (E : V → V → Prop) : Prop :=
  ∃ f : V → V, ∀ i ∈ S, f i ∈ S ∧ f (f i) = i ∧ E i (f i)

namespace Pairs
variable {S T : Finset V} {E D : V → V → Prop} {a b : V}

theorem empty : Pairs ∅ E := ⟨id, by simp⟩

theorem single (h : E a a) : Pairs {a} E := ⟨id, by simpa using h⟩

theorem pair (h : E a b) (h' : E b a) : Pairs {a,b} E := by
  refine ⟨Equiv.swap a b, ?_⟩
  simp [h, h']

theorem mono (h : Pairs S E) (hd : ∀ i ∈ S, ∀ j ∈ S, E i j → D i j) : Pairs S D := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, fun i hi ↦ ⟨(hf i hi).1, (hf i hi).2.1, hd i hi _ (hf i hi).1 (hf i hi).2.2⟩⟩

theorem union (hs : Pairs S E) (ht : Pairs T E) (hd : Disjoint S T) : Pairs (S ∪ T) E := by
  obtain ⟨f, hf⟩ := hs
  obtain ⟨g, hg⟩ := ht
  rw [Finset.disjoint_left] at hd
  refine ⟨fun i ↦ if i ∈ S then f i else g i, ?_⟩
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · simpa [hi, (hf _ hi).1] using (hf i hi).2
  · have hi' : i ∉ S := fun h ↦ hd h hi
    have hg' : g i ∉ S := fun h ↦ hd h (hg i hi).1
    simp [hi', hg', (hg i hi).1, (hg i hi).2]

theorem sdiff (h : Pairs S E) (hT : ∀ i ∈ T, ∀ j ∈ S, E i j → j ∈ T) :
    Pairs (S \ T) E := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f, fun i hi ↦ ?_⟩
  obtain ⟨his, hit⟩ := Finset.mem_sdiff.mp hi
  obtain ⟨hfs, hff, he⟩ := hf i his
  have : f i ∉ T := by
    intro ht
    exact hit (hff ▸ hT _ ht _ (hf _ hfs).1 (hf _ hfs).2.2)
  exact ⟨Finset.mem_sdiff.mpr ⟨hfs, this⟩, hff, he⟩

theorem card_even (h : Pairs S E) (hirr : ∀ i ∈ S, ¬ E i i) : Even S.card := by
  obtain ⟨f, hf⟩ := h
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    rcases S.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · simp
    obtain ⟨hb, hba, he⟩ := hf a ha
    have hab : f a ≠ a := fun hh ↦ hirr a ha (by simpa only [hh] using he)
    let T := (S.erase a).erase (f a)
    have hsub : T ⊆ S := (Finset.erase_subset ..).trans (Finset.erase_subset ..)
    have hlt : T ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h ↦ by
      have : a ∈ T := h ▸ ha
      simp [T] at this⟩
    have hc : Even T.card := ih T hlt (fun i hi ↦ hirr i (hsub hi)) (by
      intro i hi
      obtain ⟨hfi, hii, hei⟩ := hf i (hsub hi)
      refine ⟨?_, hii, hei⟩
      simp only [T, Finset.mem_erase] at hi ⊢
      grind)
    have hc' : T.card + 2 = S.card := by
      dsimp [T]
      have h₁ := Finset.card_erase_add_one ha
      have h₂ := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hab, hb⟩)
      omega
    obtain ⟨k,hk⟩ := hc
    exact ⟨k+1, by omega⟩

theorem of_even (h : Even S.card) : Pairs S (· ≠ ·) := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    rcases S.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · exact empty
    obtain ⟨k,hk⟩ := h
    have h₁ := Finset.card_erase_add_one ha
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < (S.erase a).card by omega)
    let T := (S.erase a).erase b
    have h₂ := Finset.card_erase_add_one hb
    have hlt : T ⊂ S := (Finset.erase_ssubset hb).trans (Finset.erase_ssubset ha)
    have ht := ih T hlt ⟨k-1, by dsimp [T]; omega⟩
    have hba := (Finset.mem_erase.mp hb).1
    have heq : T ∪ {a,b} = S := by ext i; simp [T]; grind
    rw [← heq]
    exact ht.union (pair hba.symm hba) (by simp [Finset.disjoint_right, T])

theorem toMatching [Fintype V] (h : Pairs Finset.univ E) :
    ∃ μ : Roommates.Matching V, ∀ i, E i (μ.val i) := by
  obtain ⟨f, hf⟩ := h
  have hinv : Function.Involutive f := fun i ↦ (hf i (Finset.mem_univ i)).2.1
  exact ⟨⟨hinv.toPerm f, hinv⟩, fun i ↦ (hf i (Finset.mem_univ i)).2.2⟩

end Pairs
end FanelliMoscardelliProof

-- === FanelliMoscardelli/Market.lean ===

namespace FanelliMoscardelliProof
open Roommates
abbrev Agent (m : ℕ) := Fin (2*m+1)
abbrev Market (m : ℕ) := CompleteProfile (2*m+1)

namespace Market
variable {m : ℕ} (p : Market m)

def choice (i : (Agent m)) (k : Fin (2*m+1)) : (Agent m) := (p.rank i).symm k
def mid (i : (Agent m)) := choice p i ⟨m, by omega⟩
def first (i : (Agent m)) := choice p i 0
def Edge (i j : (Agent m)) : Prop := p.partnerRank i j ≤ m ∧ p.partnerRank j i ≤ m
def Solved := ∃ μ : Matching (Agent m), IsKStable ⊤ p.partnerRank m μ

theorem rank_mid (i : (Agent m)) : p.partnerRank i (mid p i) = m+1 := by
  simp [mid, choice, CompleteProfile.partnerRank]
theorem rank_first (i : (Agent m)) : p.partnerRank i (first p i) = 1 := by
  simp [first, choice, CompleteProfile.partnerRank]
theorem rank_inj (i : (Agent m)) : Function.Injective (p.partnerRank i) := by
  intro j k h
  apply (p.rank i).injective
  exact Fin.ext (Nat.succ.inj h)
theorem rank_pos (i j : (Agent m)) : 0 < p.partnerRank i j := Nat.zero_lt_succ _
theorem rank_other {i j : (Agent m)} (h : j ≠ i) : p.partnerRank i j ≤ 2*m := by
  have hb := p.partnerRank_le i j
  have hn : p.partnerRank i j ≠ p.partnerRank i i := fun e ↦ h (rank_inj p i e)
  simp only [CompleteProfile.partnerRank_self] at hn
  omega
theorem mid_ne (hm : 0 < m) (i : (Agent m)) : mid p i ≠ i := by
  intro h
  have := rank_mid p i
  rw [h, CompleteProfile.partnerRank_self] at this
  omega
theorem edge_symm {i j : (Agent m)} (h : Edge p i j) : Edge p j i := h.symm
theorem edge_irrefl (i : (Agent m)) : ¬Edge p i i := by simp [Edge]; omega

/-- A blocking pair outside the mutual-top graph must involve the single agent
and that agent's middle choice. -/
theorem criterion {D : (Agent m) → (Agent m) → Prop} {u : (Agent m)} (h : Pairs Finset.univ D)
    (hs : ∀ i, D i i → i = u)
    (hg : ∀ i j k l, Edge p i j → D i k → D j l →
      p.partnerRank i k < p.partnerRank i j + m ∨ p.partnerRank j l < p.partnerRank j i + m)
    (hx : ∀ l, D (mid p u) l → p.partnerRank (mid p u) l < p.partnerRank (mid p u) u + m) : Solved p := by
  obtain ⟨μ, hμ⟩ := h.toMatching
  refine ⟨μ, fun i ↦ ?_, ?_⟩
  · by_cases hi : μ.val i = i
    · exact Or.inl hi
    · exact Or.inr ((SimpleGraph.top_adj ..).mpr (Ne.symm hi))
  intro i j hb
  obtain ⟨hij, _, hi, hj⟩ := hb
  have hm₁ := p.partnerRank_le i (μ.val i)
  have hm₂ := p.partnerRank_le j (μ.val j)
  by_cases he : Edge p i j
  · rcases hg i j _ _ he (hμ _) (hμ _) with h | h <;> omega
  have extra : ∀ a b, p.partnerRank a b > m → p.partnerRank a b + m ≤ p.partnerRank a (μ.val a) →
      a = u ∧ b = mid p u := by
    intro a b hgt hbl
    have hbound := p.partnerRank_le a (μ.val a)
    have heq : μ.val a = a := by
      by_contra hn
      have := rank_other p hn
      omega
    have hau := hs a (by simpa only [heq] using hμ a)
    subst a
    exact ⟨rfl, rank_inj p _ (by rw [rank_mid]; omega)⟩
  unfold Edge at he
  push Not at he
  by_cases hi' : m < p.partnerRank i j
  · obtain ⟨rfl, rfl⟩ := extra i j hi' hi
    have := hx _ (hμ _)
    omega
  · obtain ⟨rfl, e⟩ := extra j i (he (by omega)) hj
    subst i
    have := hx _ (hμ _)
    omega

/-- Cardinality of an initial segment of an agent's preference order. -/
theorem card_choices (i : (Agent m)) {k : ℕ} (hk : k ≤ 2*m+1) :
    (Finset.univ.filter (fun j ↦ p.partnerRank i j ≤ k)).card = k := by
  classical
  let e : {j : (Agent m) // p.partnerRank i j ≤ k} ≃ Fin k :=
    { toFun := fun j ↦ ⟨(p.rank i j).val, j.property⟩
      invFun := fun t ↦ ⟨choice p i ⟨t.val, lt_of_lt_of_le t.isLt hk⟩, by
        simp [choice, CompleteProfile.partnerRank]⟩
      left_inv := fun j ↦ by simp [choice]
      right_inv := fun t ↦ by simp [choice] }
  simpa [Fintype.card_subtype] using Fintype.card_congr e

end Market
end FanelliMoscardelliProof

-- === FanelliMoscardelli/Residual.lean ===

namespace FanelliMoscardelliProof.Market
open Roommates Finset
variable {m : ℕ} {p : Market m}

variable (p) in
structure Packed (W : Finset (Agent m)) : Prop where
  cover : Pairs Wᶜ (Edge p)
  indep : ∀ i ∈ W, ∀ j ∈ W, ¬(Edge p) i j

variable {W : Finset (Agent m)}

theorem Packed.even_erase (h : Packed p W) {u : (Agent m)} (hu : u ∈ W) :
    Even (W.erase u).card := by
  obtain ⟨k,hk⟩ := h.cover.card_even (fun i _ ↦ edge_irrefl p i)
  have hc := Finset.card_compl_add_card W
  simp only [Fintype.card_fin] at hc
  have := Finset.card_erase_add_one hu
  exact ⟨m-k, by omega⟩

/-- If a completion fails, the middle choice of the single must belong to the
uncovered set and must prefer the single by at least the threshold. -/
theorem Packed.obstruction (h : Packed p W) (hm : 0 < m) (bad : ¬ Solved p)
    {u : (Agent m)} (hu : u ∈ W) {B : (Agent m) → (Agent m) → Prop} (fill : Pairs (W.erase u) B)
    (hne : ∀ i ∈ W.erase u, ¬B i i) :
    (mid p) u ∈ W.erase u ∧ ∃ b ∈ W.erase u, B ((mid p) u) b ∧ p.partnerRank ((mid p) u) u + m ≤ p.partnerRank ((mid p) u) b := by
  classical
  let D i j := (i ∉ W ∧ (Edge p) i j) ∨ (i = u ∧ j = u) ∨
    (i ∈ W.erase u ∧ j ∈ W.erase u ∧ B i j)
  have h₁ : Pairs Wᶜ D := h.cover.mono (by simp [D]; grind [rank_mid, rank_first, rank_pos, rank_other])
  have h₂ : Pairs {u} D := Pairs.single (by simp [D])
  have h₃ : Pairs (W.erase u) D := fill.mono (by simp [D]; grind [rank_mid, rank_first, rank_pos, rank_other])
  have hall : Wᶜ ∪ {u} ∪ W.erase u = univ := by ext; simp; grind [rank_mid, rank_first, rank_pos, rank_other]
  have hp : Pairs univ D := hall ▸ (h₁.union h₂ (by simpa using hu)).union h₃ (by
    simp [Finset.disjoint_left]; grind [rank_mid, rank_first, rank_pos, rank_other])
  by_contra hno
  apply bad
  apply criterion p (u := u) hp
  · intro i hi
    have := edge_irrefl p i
    simp only [D] at hi
    grind [rank_mid, rank_first, rank_pos, rank_other]
  · intro i j k l he hik hjl
    have hind := h.indep i
    have hi' := rank_pos p i j
    have hj' := rank_pos p j i
    simp only [D, mem_erase, Edge] at hik hjl
    by_cases hi : i ∈ W
    · have hj : j ∉ W := fun hj ↦ hind hi j hj he
      grind [rank_mid, rank_first, rank_pos, rank_other]
    · grind [rank_mid, rank_first, rank_pos, rank_other]
  · intro l hl
    have hx := mid_ne p hm u
    have hr := rank_pos p ((mid p) u) u
    simp only [D, Edge] at hl
    grind [rank_mid, rank_first, rank_pos, rank_other]

theorem force_pair {S : Finset (Agent m)} (hc : Even S.card)
    {a b : (Agent m)} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    Pairs S (fun i j ↦ i ≠ j ∧ (i = a → j = b)) := by
  let T := (S.erase a).erase b
  have hb' := mem_erase.mpr ⟨hab.symm,hb⟩
  have ht : Even T.card := by
    obtain ⟨k,hk⟩ := hc
    have := card_erase_add_one ha
    have := card_erase_add_one hb'
    exact ⟨k-1, by dsimp [T]; omega⟩
  have heq : T ∪ {a,b} = S := by ext; simp [T]; grind [rank_mid, rank_first, rank_pos, rank_other]
  rw [← heq]
  refine Pairs.union ?_ (Pairs.pair (a := a) (b := b) (by simp [hab]) (by simp [hab.symm])) ?_
  · apply (Pairs.of_even ht).mono
    simp [T]; grind [rank_mid, rank_first, rank_pos, rank_other]
  · simp [Finset.disjoint_right, T]

theorem Packed.forced (h : Packed p W) (hm : 0 < m) (bad : ¬Solved p) {u : (Agent m)} (hu : u ∈ W) :
    (mid p) u ∈ W ∧ p.partnerRank ((mid p) u) u ≤ m ∧
    ∀ v ∈ W, v ≠ u → v ≠ (mid p) u → p.partnerRank ((mid p) u) u + m ≤ p.partnerRank ((mid p) u) v := by
  have hc := h.even_erase hu
  obtain ⟨hx,b,_,hxb,hbd⟩ := h.obstruction hm bad hu (Pairs.of_even hc) (by simp)
  refine ⟨(mem_erase.mp hx).2, ?_, ?_⟩
  · have := rank_other p hxb.symm
    omega
  intro v hv hvu hvx
  have hpair := force_pair hc hx (mem_erase.mpr ⟨hvu,hv⟩) hvx.symm
  obtain ⟨_,z,_,hz,hbound⟩ := h.obstruction hm bad hu hpair (by simp)
  simpa only [hz.2 rfl] using hbound

variable (p) in
structure Cycles (W : Finset (Agent m)) : Prop where
  mid_mem : ∀ u ∈ W, (mid p) u ∈ W
  first_mid : ∀ u ∈ W, (first p) ((mid p) u) = u
  first_mem : ∀ u ∈ W, (first p) u ∈ W
  mid_first : ∀ u ∈ W, (mid p) ((first p) u) = u
  other : ∀ u ∈ W, ∀ v ∈ W, v ≠ (first p) u → m < p.partnerRank u v

theorem Packed.cycles (h : Packed p W) (hm : 0 < m) (bad : ¬Solved p) : Cycles p W := by
  have H := fun (u : (Agent m)) (hu : u ∈ W) ↦ h.forced hm bad hu
  have inv : ∀ u ∈ W, (first p) ((mid p) u) = u := by
    intro u hu
    have hu' := H u hu
    have huu := H _ hu'.1
    have hne : (mid p) ((mid p) u) ≠ u := by
      intro he
      have hh := huu.2.1
      rw [he, rank_mid] at hh
      omega
    have hh := hu'.2.2 _ huu.1 hne (mid_ne p hm _)
    rw [rank_mid] at hh
    apply rank_inj p _
    rw [rank_first]
    have := rank_pos p ((mid p) u) u
    omega
  have onto : ∀ v ∈ W, ∃ u ∈ W, (mid p) u = v := by
    let g (u : ↥W) : ↥W := ⟨(mid p) u, (H _ u.property).1⟩
    have inj : Function.Injective g := by
      intro a b eq
      have eq' := congrArg Subtype.val eq
      change (mid p) a.val = (mid p) b.val at eq'
      apply Subtype.ext
      simpa only [inv _ a.property, inv _ b.property] using congrArg (first p) eq'
    intro v hv
    obtain ⟨u, e⟩ := Finite.surjective_of_injective inj (⟨v,hv⟩ : ↥W)
    exact ⟨u,u.property,congrArg Subtype.val e⟩
  refine ⟨fun u hu ↦ (H _ hu).1, inv, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨u,hu,rfl⟩ := onto _ hv
    rwa [inv _ hu]
  · intro v hv
    obtain ⟨u,hu,rfl⟩ := onto _ hv
    rw [inv _ hu]
  · intro v hv a ha hne
    obtain ⟨u,hu,rfl⟩ := onto _ hv
    rw [inv _ hu] at hne
    by_cases he : a = (mid p) u
    · subst a; simp; omega
    · have := (H _ hu).2.2 a ha hne he
      have := rank_pos p ((mid p) u) u
      omega

end FanelliMoscardelliProof.Market

-- === FanelliMoscardelli/Component.lean ===

namespace FanelliMoscardelliProof.Market
open Roommates Finset
variable {m : ℕ} {p : Market m}

theorem extend {S : Finset (Agent m)} (h : Pairs S (Edge p)) :
    ∃ T : Finset (Agent m), Disjoint S T ∧ Pairs T (Edge p) ∧ Packed p (S ∪ T)ᶜ := by
  classical
  let A := univ.filter (fun T : Finset (Agent m) ↦ Disjoint S T ∧ Pairs T (Edge p))
  obtain ⟨T, hT, hmax⟩ := exists_max_image A card
    (⟨∅, by simp [A, Pairs.empty]⟩ : A.Nonempty)
  obtain ⟨hd, ht⟩ := (mem_filter.mp hT).2
  refine ⟨T,hd,ht,⟨by simpa using h.union ht hd, ?_⟩⟩
  intro a ha b hb he
  simp only [mem_compl, mem_union, not_or] at ha hb
  have hab : a ≠ b := fun eq ↦ edge_irrefl p b (eq ▸ he)
  let U := T ∪ {a,b}
  have hU : U ∈ A := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_, ht.union (Pairs.pair he (edge_symm p he)) ?_⟩
    · exact Finset.disjoint_union_right.mpr ⟨hd, by simp [Finset.disjoint_right, ha, hb]⟩
    · simp [Finset.disjoint_right, ha, hb]
  have hlt : T ⊂ U := Finset.ssubset_iff_subset_ne.mpr ⟨subset_union_left, fun eq ↦ ha.2
    (eq ▸ (show a ∈ U by simp [U]))⟩
  exact (not_lt_of_ge (hmax _ hU)) (card_lt_card hlt)

/-- The alternating exchange covers a vertex and then forces its two consecutive
predecessors to compete for the only newly exposed vertex. -/
theorem Packed.isolated {W : Finset (Agent m)} (h : Packed p W) (hm : 0 < m)
    (bad : ¬Solved p) {w : (Agent m)} (hw : w ∈ W) (y : (Agent m)) : ¬ (Edge p) w y := by
  intro hwy
  have hy : y ∉ W := fun hy ↦ h.indep _ hw _ hy hwy
  obtain ⟨g,hg⟩ := h.cover
  let z := g y
  obtain ⟨hz,hzy,hyz⟩ := hg y (mem_compl.mpr hy)
  change z ∈ Wᶜ at hz
  change g z = y at hzy
  change (Edge p) y z at hyz
  let R := Wᶜ \ {y,z}
  have hr : Pairs R (Edge p) := by
    refine ⟨g, fun i hi ↦ ?_⟩
    obtain ⟨hi',hne⟩ := mem_sdiff.mp hi
    obtain ⟨hgi,hii,hei⟩ := hg i hi'
    refine ⟨mem_sdiff.mpr ⟨hgi,?_⟩,hii,hei⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hne ⊢
    change g z = y at hzy
    have : g y = z := rfl
    grind [rank_mid, rank_first, rank_pos, rank_other]
  let S := R ∪ {w,y}
  have hS : Pairs S (Edge p) := hr.union (Pairs.pair hwy (edge_symm p hwy)) (by
    simp [Finset.disjoint_right,R,hw])
  obtain ⟨T, hd, hT, hp⟩ := extend hS
  have cy := h.cycles hm bad
  have cy' := hp.cycles hm bad
  let a := (first p) w
  let b := (first p) a
  have ha : a ∈ W := cy.first_mem w hw
  have hb : b ∈ W := cy.first_mem a ha
  have hxa : (mid p) a = w := cy.mid_first w hw
  have hxb : (mid p) b = a := cy.mid_first a ha
  have haw : a ≠ w := fun e ↦ mid_ne p hm a (hxa.trans e.symm)
  have hba : b ≠ a := fun e ↦ mid_ne p hm b (hxb.trans e.symm)
  have hbw : b ≠ w := by
    intro he
    have hh := rank_first p a
    change p.partnerRank a b = 1 at hh
    rw [he, ← hxa, rank_mid] at hh
    omega
  have hwt : w ∈ S ∪ T := by simp [S]
  have back : ∀ v, (mid p) v ∈ S ∪ T → v ∈ S ∪ T := by
    intro v hv
    by_contra hn
    exact (mem_compl.mp (cy'.mid_mem _ (mem_compl.mpr hn))) hv
  have hat : a ∈ T := by
    have := back a (hxa ▸ hwt)
    simp [S,R,ha,haw] at this
    grind [rank_mid, rank_first, rank_pos, rank_other]
  have hbt : b ∈ T := by
    have := back b (hxb ▸ mem_union_right S hat)
    simp [S,R,hb,hbw] at this
    grind [rank_mid, rank_first, rank_pos, rank_other]
  obtain ⟨t,ht⟩ := hT
  have onlyZ : ∀ v ∈ W, v ∈ T → t v = z := by
    intro v hv hvt
    obtain ⟨htv,_,he⟩ := ht v hvt
    have h₁ : t v ∉ W := fun hmem ↦ h.indep v hv _ hmem he
    have h₂ : t v ∉ S := fun hmem ↦ Finset.disjoint_left.mp hd hmem htv
    simp [S,R,h₁] at h₂
    tauto
  have h₁ := (ht a hat).2.1
  have h₂ := (ht b hbt).2.1
  rw [onlyZ a ha hat] at h₁
  rw [onlyZ b hb hbt] at h₂
  exact hba (h₂.symm.trans h₁)

variable (p) in
noncomputable def active : Finset (Agent m) := by
  classical
  exact univ.filter (fun i ↦ ∃ j, (Edge p) i j)

@[simp] theorem mem_active {i : (Agent m)} : i ∈ active p ↔ ∃ j, (Edge p) i j := by classical simp [active]

theorem packed_iff_compl {W : Finset (Agent m)} (h : Packed p W) (hm : 0 < m) (bad : ¬Solved p) :
    Wᶜ = active p := by
  obtain ⟨g,hg⟩ := h.cover
  ext i
  simp only [mem_compl, mem_active]
  exact ⟨fun hn ↦ ⟨g i, (hg _ (mem_compl.mpr hn)).2.2⟩,
    fun ⟨y,he⟩ hi ↦ h.isolated hm bad hi y he⟩

theorem residual_packed (hm : 0 < m) (bad : ¬Solved p) : Packed p (active p)ᶜ := by
  obtain ⟨T,_,_,hp⟩ := extend (p := p) Pairs.empty
  have eq := packed_iff_compl hp hm bad
  rw [← eq, compl_compl]
  exact hp

/-- Every prescribed partial graph matching extends over all active vertices. -/
theorem residual_extend (hm : 0 < m) (bad : ¬Solved p) {S : Finset (Agent m)} (hs : Pairs S (Edge p)) :
    Pairs (active p \ S) (Edge p) := by
  obtain ⟨T,hd,hT,hp⟩ := extend hs
  have eq := packed_iff_compl hp hm bad
  rw [compl_compl] at eq
  have : (S ∪ T) \ S = T := by ext; simp only [mem_sdiff,mem_union]; have := Finset.disjoint_left.mp hd; grind [rank_mid, rank_first, rank_pos, rank_other]
  rwa [← eq, this]

end FanelliMoscardelliProof.Market

-- === FanelliMoscardelli/RandomMatching.lean ===

namespace FanelliMoscardelliProof.Market
open Roommates Finset
open scoped Classical
variable {m : ℕ} {p : Market m}

/-- An alternating switch on a perfect matching leaves two endpoints; random
matchability forces the endpoints to be adjacent. -/
structure Frame (p : Market m) where
  g : (Agent m) → (Agent m)
  inv : Function.Involutive g
  adj : ∀ i ∈ active p, Edge p i (g i)
  finish : ∀ {S : Finset (Agent m)}, Pairs S (Edge p) → Pairs (active p \ S) (Edge p)

theorem frame (hm : 0 < m) (bad : ¬Solved p) : Nonempty (Frame p) := by
  have h := residual_extend hm bad (S := ∅) (p := p) Pairs.empty
  rw [sdiff_empty] at h
  obtain ⟨g,hg⟩ := h
  classical
  refine ⟨⟨fun i ↦ if i ∈ (active p) then g i else i, ?_, ?_, residual_extend hm bad⟩⟩
  · intro i
    by_cases hi : i ∈ (active p) <;> simp [hi, (fun h : i ∈ (active p) ↦ (hg i h).1), (fun h : i ∈ (active p) ↦ (hg i h).2.1)]
  · intro i hi
    simpa [hi] using (hg i hi).2.2

namespace Frame
variable (F : Frame p)

theorem twice (i : (Agent m)) : F.g (F.g i) = i := F.inv i
theorem g_mem {i : (Agent m)} (hi : i ∈ (active p)) : F.g i ∈ (active p) := mem_active.mpr ⟨i,edge_symm p (F.adj _ hi)⟩
theorem g_ne {i : (Agent m)} (hi : i ∈ (active p)) : F.g i ≠ i := by
  intro eq
  have he := F.adj i hi
  rw [eq] at he
  exact edge_irrefl p i he

private theorem close {S : Finset (Agent m)} {a b : (Agent m)}
    (ha : a ∈ S) (hb : b ∈ S) (hS : S ⊆ (active p)) (hg : ∀ i ∈ S, F.g i ∈ S)
    (hp : Pairs (S \ {a,b}) (Edge p)) : (Edge p) a b := by
  have hr : Pairs ((active p) \ S) (Edge p) := by
    refine ⟨F.g, fun i hi ↦ ?_⟩
    obtain ⟨hij,his⟩ := mem_sdiff.mp hi
    refine ⟨mem_sdiff.mpr ⟨F.g_mem hij, fun h ↦ his (F.inv i ▸ hg _ h)⟩,F.inv i,F.adj _ hij⟩
  have h := F.finish (hr.union hp (by simp [Finset.disjoint_left]; grind [rank_mid, rank_first, rank_pos, rank_other, Frame.twice]))
  have eq : (active p) \ (((active p) \ S) ∪ (S \ {a,b})) = {a,b} := by
    ext i; simp only [mem_sdiff,mem_union,mem_insert,mem_singleton]; have := hS ha; have := hS hb; grind [rank_mid, rank_first, rank_pos, rank_other, Frame.twice]
  rw [eq] at h
  obtain ⟨t,ht⟩ := h
  obtain ⟨ht',_,he⟩ := ht a (by simp)
  simp only [mem_insert, mem_singleton] at ht'
  rcases ht' with e | e
  · rw [e] at he; exact (edge_irrefl p a he).elim
  · rwa [e] at he

theorem flip {a b : (Agent m)} (he : (Edge p) a b) : (Edge p) (F.g a) (F.g b) := by
  have ha := mem_active.mpr ⟨b,he⟩
  have hb := mem_active.mpr ⟨a,edge_symm p he⟩
  have hab : a ≠ b := fun e ↦ edge_irrefl p b (e ▸ he)
  by_cases h : F.g a = b
  · rw [← h, F.inv]; rw [h]; exact edge_symm p he
  have h₁ := F.g_ne ha
  have h₂ := F.g_ne hb
  have hn : F.g b ≠ a := fun e ↦ h ((congrArg F.g e).symm.trans (F.inv b))
  let S : Finset (Agent m) := {a,F.g a,b,F.g b}
  have eq : S \ {F.g a,F.g b} = {a,b} := by ext; simp [S]; grind [rank_mid, rank_first, rank_pos, rank_other, Frame.twice]
  apply F.close (S := S) (by simp [S]) (by simp [S])
    (by have := F.g_mem ha; have := F.g_mem hb; intro i; simp only [S,mem_insert,mem_singleton]; grind [rank_mid, rank_first, rank_pos, rank_other, Frame.twice]) (by simp [S,F.twice])
  rw [eq]
  exact Pairs.pair he (edge_symm p he)

/-- On the active vertices, two vertices are in the same component exactly
when the first is adjacent to an endpoint of the second's matched pair. -/
def Related (a b : (Agent m)) := (Edge p) a b ∨ (Edge p) a (F.g b)

theorem self {a : (Agent m)} (ha : a ∈ (active p)) : F.Related a a := Or.inr (F.adj a ha)
theorem symm {a b : (Agent m)} (h : F.Related a b) : F.Related b a := by
  rcases h with h|h
  · exact Or.inl (edge_symm p h)
  · exact Or.inr (by simpa [F.twice] using edge_symm p (F.flip h))
@[simp] theorem related_g (a b : (Agent m)) : F.Related a (F.g b) ↔ F.Related a b := by
  simp [Related,F.twice,or_comm]

private theorem chain {a b c : (Agent m)} (h₁ : (Edge p) a b) (h₂ : (Edge p) (F.g b) c) : F.Related a c := by
  have ha := mem_active.mpr ⟨b,h₁⟩
  have hb := mem_active.mpr ⟨a,edge_symm p h₁⟩
  have hc := mem_active.mpr ⟨F.g b,edge_symm p h₂⟩
  by_contra hn
  have na := F.g_ne ha
  have nb := F.g_ne hb
  have nc := F.g_ne hc
  have hac : a ≠ c := by intro e; subst c; exact hn (F.self ha)
  have hac' : a ≠ F.g c := by
    intro e; apply hn; left; rw [e]; exact edge_symm p (F.adj c hc)
  have hab : a ≠ b := fun e ↦ edge_irrefl p b (e ▸ h₁)
  have hbc : F.g b ≠ c := fun e ↦ edge_irrefl p c (e ▸ h₂)
  by_cases hab' : a = F.g b
  · exact hn (Or.inl (hab' ▸ h₂))
  by_cases hbc' : b = c
  · exact hn (Or.inl (hbc' ▸ h₁))
  have := F.inv a
  have := F.inv b
  have := F.inv c
  let S : Finset (Agent m) := {a,F.g a,b,F.g b,c,F.g c}
  have eq : S \ {F.g a,F.g c} = {a,b} ∪ {F.g b,c} := by ext; simp [S]; grind [rank_mid, rank_first, rank_pos, rank_other, Frame.twice]
  have hclose : (Edge p) (F.g a) (F.g c) := by
    apply F.close (S := S) (by simp [S]) (by simp [S])
      (by have := F.g_mem ha; have := F.g_mem hb; have := F.g_mem hc; intro i; simp only [S,mem_insert,mem_singleton]; grind [rank_mid, rank_first, rank_pos, rank_other, Frame.twice]) (by simp [S,F.twice])
    rw [eq]
    exact (Pairs.pair h₁ (edge_symm p h₁)).union (Pairs.pair h₂ (edge_symm p h₂))
      (by simp [Finset.disjoint_right]; grind [rank_mid, rank_first, rank_pos, rank_other, Frame.twice])
  exact hn (Or.inl (by simpa [F.twice] using F.flip hclose))

theorem trans {a b c : (Agent m)} (h₁ : F.Related a b) (h₂ : F.Related b c) : F.Related a c := by
  have go : ∀ {i j k}, (Edge p) i j → (Edge p) j k → F.Related i k := by
    intro i j k hij hjk
    exact (F.related_g i k).mp (F.chain hij (F.flip hjk))
  rcases h₁ with h₁|h₁ <;> rcases h₂ with h₂|h₂
  · exact go h₁ h₂
  · exact (F.related_g ..).mp (go h₁ h₂)
  · exact F.chain h₁ (by simpa [F.twice] using h₂)
  · exact (F.related_g ..).mp (F.chain h₁ (by simpa [F.twice] using h₂))

/-- At least half of a component consists of neighbors of any of its vertices. -/
theorem size_le_twice_degree (i : (Agent m)) :
    ((active p).filter (F.Related i)).card ≤ 2 * ((active p).filter ((Edge p) i)).card := by
  classical
  let N := (active p).filter ((Edge p) i)
  have hsub : (active p).filter (F.Related i) ⊆ N ∪ N.image F.g := by
    intro j hj
    obtain ⟨hj, h|h⟩ := mem_filter.mp hj
    · exact mem_union_left _ (mem_filter.mpr ⟨hj,h⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨F.g j, mem_filter.mpr ⟨F.g_mem hj,h⟩,F.inv _⟩)
  have h := (card_le_card hsub).trans (card_union_le ..)
  have h' : (N.image F.g).card ≤ N.card := card_image_le
  change _ ≤ 2*N.card
  omega

end Frame
end FanelliMoscardelliProof.Market

-- === FanelliMoscardelli/Repairs.lean ===

namespace FanelliMoscardelliProof.Market
open Roommates Finset
open scoped Classical
variable {m : ℕ} {p : Market m}

theorem isolate_count (hm : 0 < m) (bad : ¬ Solved p) : 3 ≤ (((active p)ᶜ)).card := by
  have hp := residual_packed hm bad
  have hc := hp.cycles hm bad
  have evt := hp.cover.card_even (fun i _ ↦ edge_irrefl p i)
  rw [compl_compl] at evt
  obtain ⟨k,hk⟩ := evt
  have hcard := card_compl_add_card (active p)
  simp only [Fintype.card_fin] at hcard
  obtain ⟨w,hw⟩ := card_pos.mp (show 0 < (((active p)ᶜ)).card by omega)
  have h₁ := hc.first_mem w hw
  have h₂ := hc.mid_mem w hw
  have h₃ := mid_ne p hm w
  have h₄ : (first p) w ≠ w := by
    intro h
    have := rank_first p w
    rw [h,CompleteProfile.partnerRank_self] at this
    omega
  have h₅ : (first p) w ≠ (mid p) w := by
    intro h
    have := rank_first p w
    rw [h,rank_mid] at this
    omega
  have hsub : ({w,(first p) w,(mid p) w} : Finset (Agent m)) ⊆ ((active p)ᶜ) := by intro a; simp only [mem_insert,mem_singleton]; grind [rank_mid, rank_first, rank_pos, rank_other]
  simpa [Finset.card_insert_of_notMem,Ne.symm h₄,Ne.symm h₃,h₅] using card_le_card hsub

theorem active_nonempty (hm : 3 ≤ m) (bad : ¬Solved p) : ((active p)).Nonempty := by
  have hcm := residual_packed (by omega : 0 < m) bad
  have cy := hcm.cycles (by omega) bad
  by_contra hn
  have hem := not_nonempty_iff_eq_empty.mp hn
  have hall : ∀ v : (Agent m), v ∈ ((active p)ᶜ) := by simp [hem]
  let u : (Agent m) := 0
  have hsub : univ.filter (fun j ↦ p.partnerRank u j ≤ m) ⊆ {(first p) u} := by
    intro j hj
    have h := cy.other u (hall _) j (hall _)
    have := (mem_filter.mp hj).2
    simp only [mem_singleton]; by_contra hne; have := h hne; omega
  have := card_le_card hsub
  rw [card_choices p u (by omega),card_singleton] at this
  omega

private theorem fill_isolates (hm : 0 < m) (bad : ¬Solved p) {s w : (Agent m)}
    (hs : s ∈ (active p)) (hw : w ∈ ((active p)ᶜ)) :
    Pairs ((((active p)ᶜ)).erase w) (fun i j ↦ i ≠ j ∧ (i = (mid p) s → p.partnerRank i j < p.partnerRank i s + m)) := by
  have hp := residual_packed hm bad
  have cy := hp.cycles hm bad
  have even := hp.even_erase hw
  by_cases hxs : (mid p) s ∈ (((active p)ᶜ)).erase w
  · obtain ⟨hne,hi⟩ := mem_erase.mp hxs
    have hs' := rank_pos p ((mid p) s) s
    have hfs : (first p) ((mid p) s) ≠ s := by
      have := mem_compl.mp (cy.first_mem _ hi)
      grind [rank_mid, rank_first, rank_pos, rank_other]
    have hr : 1 < p.partnerRank ((mid p) s) s := by
      have h := rank_first p ((mid p) s)
      have h' : p.partnerRank ((mid p) s) ((first p) ((mid p) s)) ≠ p.partnerRank ((mid p) s) s := fun e ↦ hfs (rank_inj p _ e)
      omega
    have hh : ∃ a ∈ (((active p)ᶜ)).erase w, (mid p) s ≠ a ∧ p.partnerRank ((mid p) s) a < p.partnerRank ((mid p) s) s + m := by
      by_cases he : (first p) ((mid p) s) = w
      · refine ⟨(mid p) ((mid p) s), mem_erase.mpr ⟨?_,cy.mid_mem _ hi⟩,(mid_ne p hm _).symm,?_⟩
        · intro e
          have hh := rank_mid p ((mid p) s)
          rw [e, ← he, rank_first] at hh
          omega
        · rw [rank_mid]; omega
      · refine ⟨(first p) ((mid p) s), mem_erase.mpr ⟨he,cy.first_mem _ hi⟩,?_,?_⟩
        · intro e
          have hh := rank_first p ((mid p) s)
          rw [← e, CompleteProfile.partnerRank_self] at hh
          omega
        · rw [rank_first]; omega
    obtain ⟨a,ha,hne',har⟩ := hh
    apply (force_pair even hxs ha hne').mono
    intro i hi j hj hij
    exact ⟨hij.1, fun e ↦ by subst i; rwa [hij.2 rfl]⟩
  · apply (Pairs.of_even even).mono
    intro i hi j hj hij
    exact ⟨hij,fun eq ↦ False.elim (hxs (eq ▸ hi))⟩

/-- Put a prescribed local repair beside a graph matching and a protected
pairing of the isolates. Failure can only come from the special assignments. -/
private theorem local_failure (hm : 0 < m) (bad : ¬Solved p)
    {s w : (Agent m)} {K : Finset (Agent m)} {D : (Agent m) → (Agent m) → Prop} (hs : s ∈ (active p)) (hw : w ∈ ((active p)ᶜ))
    (hK : K ⊆ (active p)) (cover : Pairs ((active p) \ K) (Edge p)) (repair : Pairs (insert w K) D)
    (single : ∀ i, D i i → i = s)
    (safe : ∀ i j a b, (Edge p) i j → D i a → D j b → p.partnerRank i a < p.partnerRank i j+m ∨ p.partnerRank j b < p.partnerRank j i+m) :
    ∃ a, D ((mid p) s) a ∧ p.partnerRank ((mid p) s) s + m ≤ p.partnerRank ((mid p) s) a := by
  let R i j := (i ∈ (active p) \ K ∧ (Edge p) i j) ∨ D i j ∨
    (i ∈ (((active p)ᶜ)).erase w ∧ i ≠ j ∧ (i = (mid p) s → p.partnerRank i j < p.partnerRank i s + m))
  have h₁ : Pairs ((active p) \ K) R := cover.mono (by intro i hi j hj he; exact Or.inl ⟨hi,he⟩)
  have h₂ : Pairs (insert w K) R := repair.mono (by intro i hi j hj hd; exact Or.inr (Or.inl hd))
  have h₃ : Pairs ((((active p)ᶜ)).erase w) R := (fill_isolates hm bad hs hw).mono (by
    intro i hi j hj hd; exact Or.inr (Or.inr ⟨hi,hd⟩))
  have hw' := mem_compl.mp hw
  have eq : (((active p) \ K) ∪ insert w K) ∪ (((active p)ᶜ)).erase w = univ := by
    ext i; simp only [mem_union,mem_sdiff,mem_insert,mem_erase,mem_compl,mem_univ,iff_true]; grind [rank_mid, rank_first, rank_pos, rank_other]
  have h₁₂ : Disjoint ((active p) \ K) (insert w K) := by
    simp only [Finset.disjoint_left,mem_sdiff,mem_insert]; grind [rank_mid, rank_first, rank_pos, rank_other]
  have h₁₂₃ : Disjoint (((active p) \ K) ∪ insert w K) ((((active p)ᶜ)).erase w) := by
    simp only [Finset.disjoint_left,mem_sdiff,mem_union,mem_insert,mem_erase,mem_compl]
    have hh := fun i (hi : i ∈ K) ↦ hK hi
    grind [rank_mid, rank_first, rank_pos, rank_other]
  by_contra hn
  apply bad
  apply criterion p (u := s) (eq ▸ (h₁.union h₂ h₁₂).union h₃ h₁₂₃)
  · intro i hi
    have := edge_irrefl p i
    simp only [R] at hi
    grind [rank_mid, rank_first, rank_pos, rank_other]
  · intro i j a b he hir hjr
    have hi := mem_active.mpr ⟨j,he⟩
    have hj := mem_active.mpr ⟨i,edge_symm p he⟩
    have pos₁ := rank_pos p i j
    have pos₂ := rank_pos p j i
    simp only [R,mem_erase,mem_compl] at hir hjr
    rcases hir with ⟨_,hh⟩ | hh | hh
    · exact Or.inl (by have := hh.1; omega)
    · rcases hjr with ⟨_,hh'⟩ | hh' | hh'
      · exact Or.inr (by have := hh'.1; omega)
      · exact safe _ _ _ _ he hh hh'
      · exact (hh'.1.2 hj).elim
    · exact (hh.1.2 hi).elim
  · intro a ha
    have := rank_pos p ((mid p) s) s
    rcases ha with ⟨_,hh⟩ | hh | hh
    · have := hh.1; omega
    · by_contra hge; exact hn ⟨a,hh,by omega⟩
    · exact hh.2.2 rfl

theorem repair_one (hm : 0 < m) (bad : ¬Solved p) {u y w : (Agent m)} (he : (Edge p) u y) (hw : w ∈ ((active p)ᶜ))
    (hclose : p.partnerRank y w < p.partnerRank y u + m) :
    (mid p) u = w ∧ p.partnerRank w u + m ≤ p.partnerRank w y := by
  have hu := mem_active.mpr ⟨y,he⟩
  have hy := mem_active.mpr ⟨u,edge_symm p he⟩
  have hw' := mem_compl.mp hw
  have huy : u ≠ y := fun e ↦ edge_irrefl p y (e ▸ he)
  let D i j := (i = u ∧ j = u) ∨ (i = y ∧ j = w) ∨ (i = w ∧ j = y)
  let K : Finset (Agent m) := {u,y}
  have hK : K ⊆ (active p) := by intro i; simp only [K,mem_insert,mem_singleton]; grind [rank_mid, rank_first, rank_pos, rank_other]
  have hcover := residual_extend hm bad (Pairs.pair he (edge_symm p he))
  have hr : Pairs (insert w K) D := by
    have eq : insert w K = {u} ∪ ({y,w} : Finset (Agent m)) := by ext; simp [K]; tauto
    rw [eq]
    exact (Pairs.single (a := u) (by simp [D])).union
      (Pairs.pair (a := y) (b := w) (by simp [D]) (by simp [D]))
      (by simp; grind [rank_mid, rank_first, rank_pos, rank_other])
  obtain ⟨a,ha,hblock⟩ := local_failure hm bad hu hw hK hcover hr (by simp [D]; grind [rank_mid, rank_first, rank_pos, rank_other]) (by
    intro i j a b hij hi hj
    have hiJ := mem_active.mpr ⟨j,hij⟩
    have hjJ := mem_active.mpr ⟨i,edge_symm p hij⟩
    have hneq : i ≠ j := fun e ↦ edge_irrefl p j (e ▸ hij)
    simp only [D] at hi hj
    grind [rank_mid, rank_first, rank_pos, rank_other])
  have hx := mid_ne p hm u
  have hxy : (mid p) u ≠ y := by
    intro e
    have hh := he.1
    rw [← e,rank_mid] at hh
    omega
  simp only [D] at ha
  grind [rank_mid, rank_first, rank_pos, rank_other]

theorem repair_two_either (F : Frame p) (hm : 0 < m) (bad : ¬Solved p)
    {s e q t w : (Agent m)} (he : (Edge p) s e) (hq : (Edge p) q t) (hw : w ∈ ((active p)ᶜ)) (far : ¬ F.Related e q)
    (hc₁ : p.partnerRank e q < p.partnerRank e s + m) (hc₂ : p.partnerRank q e < p.partnerRank q t + m ∨ p.partnerRank t w < p.partnerRank t q + m) (hwx : w ≠ (mid p) s) :
    ((mid p) s = q ∧ p.partnerRank q s + m ≤ p.partnerRank q e) ∨ ((mid p) s = t ∧ p.partnerRank t s + m ≤ p.partnerRank t w) := by
  have hs := mem_active.mpr ⟨e,he⟩
  have heJ := mem_active.mpr ⟨s,edge_symm p he⟩
  have hqJ := mem_active.mpr ⟨t,hq⟩
  have ht := mem_active.mpr ⟨q,edge_symm p hq⟩
  have hw' := mem_compl.mp hw
  have h₁ : F.Related e s := Or.inl (edge_symm p he)
  have h₂ : F.Related t q := Or.inl (edge_symm p hq)
  have cross : ∀ i ∈ ({s,e} : Finset (Agent m)), ∀ j ∈ ({q,t} : Finset (Agent m)), ¬F.Related i j := by
    intro i hi j hj h
    have hr₁ : F.Related e i := by
      simp only [mem_insert,mem_singleton] at hi
      rcases hi with rfl|rfl
      · exact h₁
      · exact F.self heJ
    have hr₂ : F.Related j q := by
      simp only [mem_insert,mem_singleton] at hj
      rcases hj with rfl|rfl
      · exact F.self hqJ
      · exact h₂
    exact far (F.trans (F.trans hr₁ h) hr₂)
  have dis : Disjoint ({s,e} : Finset (Agent m)) {q,t} := by
    apply Finset.disjoint_left.mpr
    intro i hi hj; apply cross _ hi _ hj
    simp only [mem_insert,mem_singleton] at hi
    rcases hi with rfl|rfl
    · exact F.self hs
    · exact F.self heJ
  have hd := Finset.disjoint_left.mp dis
  simp only [mem_insert,mem_singleton] at hd cross
  have hse : s ≠ e := fun eq ↦ edge_irrefl p e (eq ▸ he)
  have hqt : q ≠ t := fun eq ↦ edge_irrefl p t (eq ▸ hq)
  let K : Finset (Agent m) := {s,e} ∪ {q,t}
  let D i j := (i = s ∧ j = s) ∨ (i = e ∧ j = q) ∨ (i = q ∧ j = e) ∨
    (i = t ∧ j = w) ∨ (i = w ∧ j = t)
  have hK : K ⊆ (active p) := by intro i; simp only [K,mem_union,mem_insert,mem_singleton]; grind [rank_mid, rank_first, rank_pos, rank_other]
  have cover := F.finish ((Pairs.pair he (edge_symm p he)).union (Pairs.pair hq (edge_symm p hq)) dis)
  have repair : Pairs (insert w K) D := by
    have eq : insert w K = ({s} ∪ {e,q}) ∪ ({t,w} : Finset (Agent m)) := by ext; simp [K]; tauto
    rw [eq]
    refine ((Pairs.single (a := s) (by simp [D])).union
      (Pairs.pair (a := e) (b := q) (by simp [D]) (by simp [D])) ?_).union
      (Pairs.pair (a := t) (b := w) (by simp [D]) (by simp [D])) ?_ <;>
      simp only [Finset.disjoint_left,mem_union,mem_insert,mem_singleton] <;> grind [rank_mid, rank_first, rank_pos, rank_other]
  obtain ⟨a,ha,hh⟩ := local_failure hm bad hs hw hK cover repair (by simp [D]; grind [rank_mid, rank_first, rank_pos, rank_other]) (by
    intro i j a b hij hi hj
    have hiJ := mem_active.mpr ⟨j,hij⟩
    have hjJ := mem_active.mpr ⟨i,edge_symm p hij⟩
    have hneq : i ≠ j := fun eq ↦ edge_irrefl p j (eq ▸ hij)
    have hr₁ : F.Related i j := Or.inl hij
    have hr₂ := F.symm hr₁
    simp only [D] at hi hj
    grind [rank_mid, rank_first, rank_pos, rank_other])
  have hx := mid_ne p hm s
  have hxe : (mid p) s ≠ e := by intro eq; have := he.1; rw [← eq,rank_mid] at this; omega
  simp only [D] at ha
  grind [rank_mid, rank_first, rank_pos, rank_other]

theorem repair_two (F : Frame p) (hm : 0 < m) (bad : ¬Solved p)
    {s e q t w : (Agent m)} (he : (Edge p) s e) (hq : (Edge p) q t) (hw : w ∈ ((active p)ᶜ)) (far : ¬ F.Related e q)
    (hc₁ : p.partnerRank e q < p.partnerRank e s + m) (hc₂ : p.partnerRank q e < p.partnerRank q t + m) (hwx : w ≠ (mid p) s) :
    ((mid p) s = q ∧ p.partnerRank q s + m ≤ p.partnerRank q e) ∨ ((mid p) s = t ∧ p.partnerRank t s + m ≤ p.partnerRank t w) :=
  repair_two_either F hm bad he hq hw far hc₁ (Or.inl hc₂) hwx

theorem other_isolate (hm : 0 < m) (bad : ¬Solved p) (z : (Agent m)) : ∃ w ∈ ((active p)ᶜ), w ≠ z := by
  by_contra! hn
  have hsub : ((active p)ᶜ) ⊆ {z} := by simpa only [Finset.subset_iff,mem_singleton] using hn
  have hcard := card_le_card hsub
  have := isolate_count hm bad
  simp only [card_singleton] at hcard
  omega

end FanelliMoscardelliProof.Market

-- === FanelliMoscardelli/Arcs.lean ===

namespace FanelliMoscardelliProof.Market
open Roommates Finset
open scoped Classical
variable {m : ℕ} {p : Market m}

private theorem exists_worst {i : (Agent m)} (hi : i ∈ (active p)) :
    ∃ u, (Edge p) i u ∧ ∀ v, (Edge p) i v → p.partnerRank i v ≤ p.partnerRank i u := by
  obtain ⟨v,hv⟩ := mem_active.mp hi
  let N := univ.filter ((Edge p) i)
  obtain ⟨u, hu, hd⟩ := exists_max_image N (p.partnerRank i) ⟨v,mem_filter.mpr ⟨mem_univ _,hv⟩⟩
  exact ⟨u,(mem_filter.mp hu).2,fun a ha ↦ hd _ (mem_filter.mpr ⟨mem_univ _,ha⟩)⟩

variable (p) in
noncomputable def worst (i : (Agent m)) := if h : i ∈ (active p) then (exists_worst h).choose else i
variable (p) in
noncomputable def d (i : (Agent m)) := p.partnerRank i (worst p i)
theorem worst_edge {i : (Agent m)} (hi : i ∈ (active p)) : (Edge p) i (worst p i) := by
  simpa only [worst,dif_pos hi] using (exists_worst hi).choose_spec.1
theorem le_d {i v : (Agent m)} (he : (Edge p) i v) : p.partnerRank i v ≤ d p i := by
  have hi := mem_active.mpr ⟨_,he⟩
  simpa only [d,worst,dif_pos hi] using (exists_worst hi).choose_spec.2 v he
theorem d_le {i : (Agent m)} (hi : i ∈ (active p)) : d p i ≤ m := (worst_edge hi).1

variable (p) in
def Accept (i j : (Agent m)) := p.partnerRank i j < d p i + m
def Eligible (q i y : (Agent m)) := Edge p q y ∧ p.partnerRank q i < p.partnerRank q y + m

namespace Frame
variable (F : Frame p)

def Small (i : (Agent m)) := ∀ j, (Edge p) i j → j = F.g i

theorem small_neighbor {i j : (Agent m)} (hi : F.Small i) (h : (Edge p) i j) : F.Small j := by
  intro k hk
  have hji := hi j h
  have h' := F.flip hk
  rw [hji,F.twice] at h'
  have heq := hi _ h'
  have := F.inv.injective heq
  rw [hji,F.twice]; assumption

theorem small_component {i j : (Agent m)} (hi : F.Small i) (hr : F.Related i j) : j = i ∨ j = F.g i := by
  rcases hr with h|h
  · exact Or.inr (hi _ h)
  · exact Or.inl (F.inv.injective (hi _ h))

theorem rank_two {i : (Agent m)} (hi : ¬F.Small i) : 2 ≤ d p i := by
  by_contra! hn
  apply hi
  intro j hj
  have hgi := F.adj _ (mem_active.mpr ⟨j,hj⟩)
  have h₁ := le_d hj
  have h₂ := le_d hgi
  apply rank_inj p i
  have := rank_pos p i j
  have := rank_pos p i (F.g i)
  omega

/-- Any acceptable isolated vertex identifies the unique neighbor of the source
and forces that neighbor's middle choice. -/
theorem isolate_rule (hm : 0 < m) (bad : ¬Solved p) {y w : (Agent m)} (hy : y ∈ (active p))
    (hw : w ∈ ((active p)ᶜ)) (ha : Accept p y w) :
    F.Small y ∧ (mid p) (F.g y) = w ∧ p.partnerRank w (F.g y) ≤ m ∧ m < p.partnerRank w y := by
  let u := worst p y
  have he : (Edge p) y u := worst_edge hy
  have hC : p.partnerRank y w < p.partnerRank y u + m := ha
  obtain ⟨hxu,hr⟩ := repair_one hm bad (edge_symm p he) hw hC
  have hu := mem_active.mpr ⟨y,edge_symm p he⟩
  have hwy : y ≠ w := by have := mem_compl.mp hw; grind [rank_mid, rank_first, rank_pos, rank_other, Frame.twice]
  have hru : p.partnerRank w u ≤ m := by have := rank_other p hwy; omega
  have hry : m < p.partnerRank w y := by have := rank_pos p w u; omega
  have hmid : p.partnerRank u w = m + 1 := by rw [← hxu,rank_mid]
  have hfirst : p.partnerRank u y = 1 := by
    have hh := rank_pos p u y
    by_contra! hn
    obtain ⟨_,hh'⟩ := repair_one hm bad he hw (by omega : p.partnerRank u w < p.partnerRank u y + m)
    omega
  have hunique : ∀ v, (Edge p) u v → v = y := by
    intro v hv
    by_contra hn
    have hne : p.partnerRank u v ≠ p.partnerRank u y := fun h ↦ hn (rank_inj p _ h)
    have := rank_pos p u v
    obtain ⟨_,hh⟩ := repair_one hm bad (edge_symm p hv) hw (by omega : p.partnerRank u w < p.partnerRank u v+m)
    have := rank_pos p w v
    omega
  have hgu := hunique _ (F.adj _ hu)
  have hgy : F.g y = u := hgu ▸ F.inv u
  have sm : F.Small u := fun v hv ↦ (hunique _ hv).trans hgu.symm
  exact ⟨F.small_neighbor sm (edge_symm p he), hgy ▸ hxu,hgy ▸ hru,hry⟩

/-- Both orientations of the two-edge repair determine the middle choices. -/
theorem good_rule (hm : 0 < m) (bad : ¬Solved p) {i q u y : (Agent m)} (far : ¬F.Related i q)
    (htop : p.partnerRank i q ≤ m) (hu : (Edge p) i u) (hy : Eligible (p := p) q i y) :
    (mid p) y = u ∧ p.partnerRank u y ≤ m ∧ (mid p) u = q ∧ p.partnerRank q u + m ≤ p.partnerRank q i := by
  obtain ⟨w,hw,hwx⟩ := other_isolate hm bad ((mid p) y)
  have hiq : p.partnerRank i q < p.partnerRank i u+m := by have := rank_pos p i u; omega
  have far' : ¬F.Related q i := fun h ↦ far (F.symm h)
  have hb := repair_two F hm bad (edge_symm p hy.1) hu hw far' hy.2 hiq hwx
  have h₁ : (mid p) y = u ∧ p.partnerRank u y ≤ m := by
    rcases hb with ⟨_,hh⟩ | ⟨he,hh⟩
    · have := rank_pos p i y; omega
    · have huJ := mem_active.mpr ⟨i,edge_symm p hu⟩
      have hwu : w ≠ u := by have := mem_compl.mp hw; grind [rank_mid, rank_first, rank_pos, rank_other, Frame.twice]
      have := rank_other p hwu
      exact ⟨he,by omega⟩
  obtain ⟨v,hv,hvx⟩ := other_isolate hm bad ((mid p) u)
  have hb' := repair_two F hm bad (edge_symm p hu) hy.1 hv far hiq hy.2 hvx
  rcases hb' with hh|⟨hxy,_⟩
  · exact ⟨h₁.1,h₁.2,hh⟩
  · have h := h₁.2
    rw [← hxy,rank_mid] at h
    omega

theorem no_good_big (hm : 0 < m) (bad : ¬Solved p) {i q : (Agent m)} (hi : i ∈ (active p)) (hq : q ∈ (active p))
    (far : ¬F.Related i q) (ht : p.partnerRank i q ≤ m) (ha : Accept p q i) : F.Small q := by
  by_contra big
  let u := F.g i
  have hu : (Edge p) i u := F.adj _ hi
  have process : ∀ y, Eligible (p := p) q i y →
      (mid p) i = y ∧ (mid p) q = i := by
    intro y hy
    have h := F.good_rule hm bad far ht hu hy
    have hbig : ¬ F.Small y := fun hs ↦ big (F.small_neighbor hs (edge_symm p hy.1))
    have hmid : p.partnerRank y u = m+1 := by rw [← h.1,rank_mid]
    have far' : ¬F.Related u y := fun hh ↦ far (F.trans (Or.inl hu) (F.trans hh (Or.inl (edge_symm p hy.1))))
    let z := worst p y
    have hyJ := mem_active.mpr ⟨q,edge_symm p hy.1⟩
    have hzy : (Edge p) y z := worst_edge hyJ
    have hd₂ := F.rank_two hbig
    have hyz : Eligible (p := p) y u z := ⟨hzy, by change _ < d p y + m; omega⟩
    have h' := F.good_rule hm bad far' h.2.1 (edge_symm p hu) hyz
    have hf : p.partnerRank y i = 1 := by have := h'.2.2.2; have := rank_pos p y i; omega
    have hqi : q ≠ i := by intro eq; exact far (by simpa only [← eq] using F.self hi)
    have hne : p.partnerRank y q ≠ p.partnerRank y i := fun eq ↦ hqi (rank_inj p _ eq)
    have hyq : Eligible (p := p) y u q := ⟨edge_symm p hy.1,by have := rank_pos p y q; omega⟩
    have h'' := F.good_rule hm bad far' h.2.1 (edge_symm p hu) hyq
    exact ⟨h'.2.2.1,h''.1⟩
  let y := worst p q
  have hy : Eligible (p := p) q i y := ⟨worst_edge hq,ha⟩
  have hh := process y hy
  have hmid : p.partnerRank q i = m+1 := by rw [← hh.2,rank_mid]
  have hstart := F.good_rule hm bad far ht hu hy
  have first : p.partnerRank q u = 1 := by have := hstart.2.2.2; have := rank_pos p q u; omega
  have all : ∀ z, (Edge p) q z → (mid p) i = z := by
    intro z hz
    have hzu : z ≠ u := by
      intro e
      apply far
      exact F.trans (Or.inl hu) (Or.inl (edge_symm p (e ▸ hz)))
    have hne : p.partnerRank q z ≠ p.partnerRank q u := fun eq ↦ hzu (rank_inj p _ eq)
    exact (process z ⟨hz,by have := rank_pos p q z; omega⟩).1
  exact big (fun z hz ↦ (all z hz).symm.trans (all _ (F.adj _ hq)))

theorem mutual_rule (hm : 0 < m) (bad : ¬Solved p) {i q : (Agent m)} (hi : i ∈ (active p)) (hq : q ∈ (active p))
    (far : ¬F.Related i q) (h₁ : Accept p i q) (h₂ : Accept p q i) :
    F.Small i ∧ F.Related ((mid p) (F.g i)) q := by
  let s := worst p i
  let t := worst p q
  have hs : (Edge p) i s := worst_edge hi
  have ht : (Edge p) q t := worst_edge hq
  obtain ⟨w,hw,hwx⟩ := other_isolate hm bad ((mid p) s)
  have hh := repair_two F hm bad (edge_symm p hs) ht hw far h₁ h₂ hwx
  have hsJ := mem_active.mpr ⟨i,edge_symm p hs⟩
  have hdata : F.Related ((mid p) s) q ∧ p.partnerRank ((mid p) s) s ≤ m := by
    rcases hh with ⟨e,hb⟩|⟨e,hb⟩
    · rw [e]
      have hiq : i ≠ q := by intro eq; exact far (by simpa only [← eq] using F.self hi)
      have := rank_other p hiq
      exact ⟨F.self hq,by omega⟩
    · rw [e]
      have htJ := mem_active.mpr ⟨q,edge_symm p ht⟩
      have hwt : w ≠ t := by have := mem_compl.mp hw; grind [rank_mid, rank_first, rank_pos, rank_other, Frame.twice]
      have := rank_other p hwt
      exact ⟨Or.inl (edge_symm p ht),by omega⟩
  have sm : F.Small i := by
    by_contra hn
    have bigs : ¬F.Small s := fun h ↦ hn (F.small_neighbor h (edge_symm p hs))
    have hfar : ¬F.Related ((mid p) s) s := fun h ↦ far (F.trans (Or.inl hs) (F.trans (F.symm h) hdata.1))
    have hxJ : (mid p) s ∈ (active p) := by rcases hh with ⟨e,_⟩|⟨e,_⟩; rw [e]; exact hq; rw [e]; exact mem_active.mpr ⟨q,edge_symm p ht⟩
    have hacc : Accept p s ((mid p) s) := by unfold Accept; rw [rank_mid]; have := F.rank_two bigs; omega
    exact bigs (F.no_good_big hm bad hxJ hsJ hfar hdata.2 hacc)
  exact ⟨sm, sm _ hs ▸ hdata.1⟩

end Frame
end FanelliMoscardelliProof.Market

-- === FanelliMoscardelli/Counting.lean ===

namespace FanelliMoscardelliProof.Market.Frame
open Roommates Finset
open scoped Classical
variable {m : ℕ} {p : Market m} (F : Frame p)
noncomputable def comp (i : (Agent m)) := ((active p)).filter (F.Related i)
noncomputable def outside (i : (Agent m)) := ((active p)).filter (fun j ↦ ¬F.Related i j)
noncomputable def out (i : (Agent m)) := (F.outside i).filter ((Accept p) i)
noncomputable def incoming (i : (Agent m)) := (F.outside i).filter (fun j ↦ (Accept p) j i)
noncomputable def both (i : (Agent m)) := F.out i ∩ F.incoming i
variable (p) in
noncomputable def exc (i : (Agent m)) := (((active p)ᶜ)).filter ((Accept p) i)

private theorem both_rule (hm : 0 < m) (bad : ¬Solved p) {i j : (Agent m)} (hi : i ∈ (active p))
    (hb : j ∈ F.both i) : F.Small i ∧ F.Small j ∧ F.Related ((mid p) (F.g i)) j := by
  simp only [both,out,incoming,outside,mem_inter,mem_filter] at hb
  have h₁ := F.mutual_rule hm bad hi hb.1.1.1 hb.1.1.2 hb.1.2 hb.2.2
  have h₂ := F.mutual_rule hm bad hb.1.1.1 hi (fun h ↦ hb.1.1.2 (F.symm h)) hb.2.2 hb.1.2
  exact ⟨h₁.1,h₂.1,h₁.2⟩

/-- An acceptable isolate consumes both units of the row's allowance for
mutual pairs. Vertices in larger components have neither kind of partner. -/
private theorem row_caps (hm : 0 < m) (bad : ¬Solved p) {i : (Agent m)} (hi : i ∈ (active p)) :
    2*(exc p i).card + (F.both i).card ≤ 2 ∧
    (¬F.Small i → (exc p i).card = 0 ∧ (F.both i).card = 0) := by
  have hr := fun (j : (Agent m)) (hj : j ∈ F.both i) ↦ F.both_rule hm bad hi hj
  have hs := fun (w : (Agent m)) (hw : w ∈ exc p i) ↦
    F.isolate_rule hm bad hi (mem_filter.mp hw).1 (mem_filter.mp hw).2
  have hex : (exc p i).card ≤ 1 := card_le_one.mpr (fun a ha b hb ↦ (hs a ha).2.1.symm.trans (hs b hb).2.1)
  refine ⟨?_, fun hn ↦ ⟨?_,?_⟩⟩
  · rcases (F.both i).eq_empty_or_nonempty with he|⟨j,hj⟩
    · rw [he,card_empty]; omega
    have hj' := hr j hj
    have hxJ : (mid p) (F.g i) ∈ (active p) := by
      rcases hj'.2.2 with h|h <;> exact mem_active.mpr ⟨_,h⟩
    have hem : exc p i = ∅ := eq_empty_iff_forall_notMem.mpr (fun w hw ↦
      (mem_compl.mp (mem_filter.mp hw).1) ((hs w hw).2.1 ▸ hxJ))
    have hsub : F.both i ⊆ {j,F.g j} := by
      intro k hk
      exact mem_insert.mpr (by
        simpa only [mem_singleton] using F.small_component hj'.2.1 (F.trans (F.symm hj'.2.2) (hr _ hk).2.2))
    have hh := card_le_card hsub
    have hl := card_insert_le j ({F.g j} : Finset (Agent m))
    rw [card_singleton] at hl
    rw [hem,card_empty]
    omega
  · exact card_eq_zero.mpr (eq_empty_iff_forall_notMem.mpr (fun w hw ↦ hn (hs w hw).1))
  · exact card_eq_zero.mpr (eq_empty_iff_forall_notMem.mpr (fun j hj ↦ hn (hr j hj).1))

private theorem row_size {i : (Agent m)} (hi : i ∈ (active p)) :
    d p i + m ≤ (exc p i).card + (F.comp i).card + (F.out i).card := by
  have hd := d_le hi
  have hpos : 0 < d p i := rank_pos p i _
  let B := univ.filter ((Accept p) i)
  have eq : B = univ.filter (fun j ↦ p.partnerRank i j ≤ d p i + m - 1) := by
    ext j; simp only [B,mem_filter,mem_univ,true_and,Accept]; omega
  have hc : B.card = d p i + m - 1 := by rw [eq,card_choices p i (by omega)]
  have hnot : i ∉ B := by simp only [B,mem_filter,mem_univ,true_and,Accept,CompleteProfile.partnerRank_self]; omega
  have hsub : insert i B ⊆ (exc p i ∪ F.comp i) ∪ F.out i := by
    have hre := F.self hi
    intro j
    simp only [B,exc,comp,out,outside,mem_insert,mem_filter,mem_compl,mem_univ,true_and,mem_union]
    grind [rank_mid, rank_first, rank_pos, rank_other, Frame.twice]
  have h := ((card_le_card hsub).trans (card_union_le ..))
  have h' := card_union_le (exc p i) (F.comp i)
  rw [card_insert_of_notMem hnot,hc] at h
  omega

private theorem two_d {i : (Agent m)} (hi : i ∈ (active p)) : (F.comp i).card ≤ 2*d p i := by
  have hd := d_le hi
  have hsub : ((active p)).filter ((Edge p) i) ⊆ univ.filter (fun j ↦ p.partnerRank i j ≤ d p i) := by
    intro j hj
    exact mem_filter.mpr ⟨mem_univ _,le_d (mem_filter.mp hj).2⟩
  have h := card_le_card hsub
  rw [card_choices p i (by omega)] at h
  exact (F.size_le_twice_degree i).trans (by omega)

theorem small_size {i : (Agent m)} (hi : i ∈ (active p)) (hs : F.Small i) : (F.comp i).card = 2 := by
  have eq : F.comp i = {i,F.g i} := by
    ext j
    simp only [comp,mem_filter,mem_insert,mem_singleton]
    constructor
    · exact fun h ↦ F.small_component hs h.2
    · rintro (rfl|rfl)
      · exact ⟨hi,F.self hi⟩
      · exact ⟨F.g_mem hi,Or.inl (F.adj _ hi)⟩
  rw [eq]
  simp [Ne.symm (F.g_ne hi)]

private theorem row_bound (hm : 0 < m) (bad : ¬Solved p) {i : (Agent m)} (hi : i ∈ (active p)) :
    (F.outside i).card + (F.both i).card ≤ 2*(F.out i).card := by
  have hc := card_filter_add_card_filter_not (s := (active p)) (F.Related i)
  change (F.comp i).card + (F.outside i).card = ((active p)).card at hc
  have hsize := F.row_size hi
  have hdeg := F.two_d hi
  have hn := card_compl_add_card (active p)
  simp only [Fintype.card_fin] at hn
  have ht := isolate_count hm bad
  have hcap := (F.row_caps hm bad hi).1
  omega

private theorem arc_balance : ∑ i ∈ (active p), (F.out i).card = ∑ j ∈ (active p), (F.incoming j).card := by
  classical
  have hout (i : (Agent m)) : (F.out i).card = ∑ j ∈ (active p), if ¬F.Related i j ∧ (Accept p) i j then 1 else 0 := by
    simp [out,outside,filter_filter,Finset.sum_boole]
  have hin (j : (Agent m)) : (F.incoming j).card = ∑ i ∈ (active p), if ¬F.Related i j ∧ (Accept p) i j then 1 else 0 := by
    simp only [incoming,outside,filter_filter,Finset.sum_boole]
    congr 1
    ext i
    simp only [mem_filter]
    have h₁ := F.symm (a := i) (b := j)
    have h₂ := F.symm (a := j) (b := i)
    tauto
  simp_rw [hout,hin]
  exact sum_comm

/-- Every row has outdegree at least its indegree. Summing over all rows
forces equality at each vertex and exhausts all cross-component pairs. -/
private theorem row_eq (hm : 0 < m) (bad : ¬Solved p) {i : (Agent m)} (hi : i ∈ (active p)) :
    (F.outside i).card + (F.both i).card = 2*(F.out i).card ∧
    F.outside i ⊆ F.out i ∪ F.incoming i := by
  have localCount (j : (Agent m)) : (F.out j ∪ F.incoming j).card + (F.both j).card =
      (F.out j).card + (F.incoming j).card := card_union_add_card_inter ..
  have sub (j : (Agent m)) : F.out j ∪ F.incoming j ⊆ F.outside j :=
    union_subset (filter_subset ..) (filter_subset ..)
  have le (j : (Agent m)) (hj : j ∈ (active p)) : (F.incoming j).card ≤ (F.out j).card := by
    have := F.row_bound hm bad hj
    have := card_le_card (sub j)
    have := localCount j
    omega
  have h := le i hi
  have eq : (F.incoming i).card = (F.out i).card := by
    by_contra hn
    have hlt := sum_lt_sum le ⟨i,hi,lt_of_le_of_ne h hn⟩
    exact hlt.ne F.arc_balance.symm
  have hr := F.row_bound hm bad hi
  have hh := localCount i
  have hs := card_le_card (sub i)
  exact ⟨by omega, (eq_of_subset_of_card_le (sub i) (by omega)).ge⟩

theorem row_rigid (hm : 0 < m) (bad : ¬Solved p) {i : (Agent m)} (hi : i ∈ (active p)) :
    F.Small i ∧ d p i = 1 ∧ (((active p)ᶜ)).card = 3 := by
  have he := (F.row_eq hm bad hi).1
  have hc := card_filter_add_card_filter_not (s := (active p)) (F.Related i)
  change (F.comp i).card + (F.outside i).card = ((active p)).card at hc
  have hsize := F.row_size hi
  have hdeg := F.two_d hi
  have hn := card_compl_add_card (active p)
  simp only [Fintype.card_fin] at hn
  have ht := isolate_count hm bad
  have hcap := F.row_caps hm bad hi
  have hs : F.Small i := by
    by_contra hh
    obtain ⟨h₁,h₂⟩ := hcap.2 hh
    omega
  have h₂ := F.small_size hi hs
  have hp : 0 < d p i := rank_pos p i _
  exact ⟨hs,by omega,by omega⟩

include F in
theorem accept_iff_top (hm : 0 < m) (bad : ¬Solved p) {i : (Agent m)} (hi : i ∈ (active p)) (j : (Agent m)) :
    (Accept p) i j ↔ p.partnerRank i j ≤ m := by
  unfold Accept
  rw [(F.row_rigid hm bad hi).2.1]
  omega

include F in
theorem has_exception (hm : 0 < m) (bad : ¬Solved p) {i : (Agent m)} (hi : i ∈ (active p)) :
    ∃ w ∈ ((active p)ᶜ), (Accept p) i w := by
  have hem : F.both i = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro j hj
    simp only [both,out,incoming,outside,mem_inter,mem_filter] at hj
    apply hj.1.1.2
    exact Or.inl ⟨(F.accept_iff_top hm bad hi j).mp hj.1.2,
      (F.accept_iff_top hm bad hj.1.1.1 i).mp hj.2.2⟩
  have he := (F.row_eq hm bad hi).1
  rw [hem,card_empty] at he
  have hc := card_filter_add_card_filter_not (s := (active p)) (F.Related i)
  change (F.comp i).card + (F.outside i).card = ((active p)).card at hc
  obtain ⟨hs,hd,hI⟩ := F.row_rigid hm bad hi
  have hsize := F.row_size hi
  have hn := card_compl_add_card (active p)
  simp only [Fintype.card_fin] at hn
  have h₂ := F.small_size hi hs
  obtain ⟨w,hw⟩ := card_pos.mp (show 0 < (exc p i).card by omega)
  exact ⟨w,(mem_filter.mp hw).1,(mem_filter.mp hw).2⟩

theorem tournament (hm : 0 < m) (bad : ¬Solved p) {i j : (Agent m)} (hi : i ∈ (active p)) (hj : j ∈ (active p))
    (far : ¬F.Related i j) : p.partnerRank i j ≤ m ∨ p.partnerRank j i ≤ m := by
  have h := (F.row_eq hm bad hi).2 (mem_filter.mpr ⟨hj,far⟩)
  rcases mem_union.mp h with ho|hin
  · exact Or.inl ((F.accept_iff_top hm bad hi _).mp (mem_filter.mp ho).2)
  · exact Or.inr ((F.accept_iff_top hm bad hj _).mp (mem_filter.mp hin).2)

end FanelliMoscardelliProof.Market.Frame

-- === FanelliMoscardelli.lean ===

/-!
# Odd-market stability threshold

A maximal mutual-top matching either admits a stable completion or forces the
isolated agents into cycles. In the latter case, local repairs and a row count
force every nontrivial component to be a mutual first-choice pair. The final
color argument below rules out this remaining case for markets of size at least seven.
-/

namespace FanelliMoscardelliProof
open Roommates Finset

namespace Market.Frame
variable {m : ℕ} {p : Market m} (F : Frame p)

private theorem color (hm : 0 < m) (bad : ¬Solved p) {i : (Agent m)} (hi : i ∈ (active p)) :
    (mid p) i ∈ ((active p)ᶜ) ∧ p.partnerRank ((mid p) i) i ≤ m ∧ m < p.partnerRank ((mid p) i) (F.g i) ∧ p.partnerRank (F.g i) ((mid p) i) ≤ m := by
  have hg := F.g_mem hi
  obtain ⟨w,hw,ha⟩ := F.has_exception hm bad hg
  obtain ⟨_,he,h₁,h₂⟩ := F.isolate_rule hm bad hg hw ha
  rw [F.twice] at he h₁
  rw [he]
  exact ⟨hw,h₁,h₂,(F.accept_iff_top hm bad hg _).mp ha⟩

private theorem partner_colors (hm : 0 < m) (bad : ¬Solved p) {i : (Agent m)} (hi : i ∈ (active p)) :
    (mid p) i ≠ (mid p) (F.g i) := by
  intro eq
  have h₁ := (F.color hm bad hi).2.2.1
  have h₂ := (F.color hm bad (F.g_mem hi)).2.1
  rw [eq] at h₁
  omega

/-- A top choice in a different component must have the color of the
source's partner, since otherwise the two-edge repair is stable. -/
private theorem arc_color (hm : 0 < m) (bad : ¬Solved p) {i a : (Agent m)} (hi : i ∈ (active p))
    (ha : a ∈ (active p)) (far : ¬F.Related i a) (htop : p.partnerRank i a ≤ m) : (mid p) a = (mid p) (F.g i) := by
  by_contra hne
  have hca := F.color hm bad ha
  have hci := F.color hm bad (F.g_mem hi)
  have h₁ : p.partnerRank i a < p.partnerRank i (F.g i) + m := by have := rank_pos p i (F.g i); omega
  have h₂ : p.partnerRank (F.g a) ((mid p) a) < p.partnerRank (F.g a) a + m := by
    have := rank_pos p (F.g a) a
    have := hca.2.2.2
    omega
  have hh := repair_two_either F hm bad (edge_symm p (F.adj _ hi)) (F.adj _ ha)
    hca.1 far h₁ (Or.inr h₂) hne
  have hn := mem_compl.mp hci.1
  have hg := F.g_mem ha
  rcases hh with ⟨e,_⟩|⟨e,_⟩ <;> rw [e] at hn <;> contradiction

include F in
private theorem finish_odd (hm : 3 ≤ m) (bad : ¬Solved p) : False := by
  classical
  have hm' : 0 < m := by omega
  obtain ⟨i,hi⟩ := active_nonempty hm bad
  have hI := (F.row_rigid hm' bad hi).2.2
  have hcomp := F.small_size hi (F.row_rigid hm' bad hi).1
  have hn := card_compl_add_card (active p)
  simp only [Fintype.card_fin] at hn
  have hc := card_filter_add_card_filter_not (s := (active p)) (F.Related i)
  change (F.comp i).card + (F.outside i).card = ((active p)).card at hc
  obtain ⟨a,ha⟩ := card_pos.mp (show 0 < (F.outside i).card by omega)
  obtain ⟨haJ,hfar⟩ := mem_filter.mp ha
  have contradiction_of_arc : ∀ z ∈ (active p), ∀ b ∈ (active p), ¬F.Related z b → p.partnerRank z b ≤ m → False := by
    intro z hz b hb hzb ht
    have he := F.arc_color hm' bad hz hb hzb ht
    have hgb := F.g_mem hb
    have hfar' : ¬ F.Related z (F.g b) := fun h ↦ hzb ((F.related_g ..).mp h)
    rcases F.tournament hm' bad hz hgb hfar' with h | h
    · have he' := F.arc_color hm' bad hz hgb hfar' h
      exact F.partner_colors hm' bad hb (he.trans he'.symm)
    · have he' := F.arc_color hm' bad hgb hz (fun hh ↦ hfar' (F.symm hh)) h
      rw [F.twice] at he'
      exact F.partner_colors hm' bad hz (he'.trans he)
  rcases F.tournament hm' bad hi haJ hfar with h | h
  · exact contradiction_of_arc i hi a haJ hfar h
  · exact contradiction_of_arc a haJ i hi (fun hh ↦ hfar (F.symm hh)) h

end Market.Frame

/-- Every complete strict profile on an odd market of size at least seven
admits an `m`-stable matching. -/
theorem stabilityThreshold_odd_le (m : ℕ) (hm : 3 ≤ m) :
    Roommates.stabilityThreshold (2 * m + 1) ≤ m := by
  apply Roommates.stabilityThreshold_le (by omega)
  intro p
  change Market.Solved p
  by_contra bad
  obtain ⟨F⟩ := Market.frame (by omega : 0 < m) bad
  exact F.finish_odd hm bad

/-- Refutes the proposed eventual equality for the stability threshold. -/
theorem not_stability_threshold_tight :
    ¬ (∃ N₀ : ℕ, 3 ≤ N₀ ∧
        ∀ N ≥ N₀, Roommates.stabilityThreshold N = (N + 1) / 2) := by
  rintro ⟨N₀, h₀, tight⟩
  have upper := stabilityThreshold_odd_le N₀ h₀
  rw [tight (2*N₀+1) (by omega)] at upper
  omega

end FanelliMoscardelliProof

theorem OMA.disproof : ¬ (type_of% @FanelliMoscardelli.stability_threshold_tight) :=
  FanelliMoscardelliProof.not_stability_threshold_tight

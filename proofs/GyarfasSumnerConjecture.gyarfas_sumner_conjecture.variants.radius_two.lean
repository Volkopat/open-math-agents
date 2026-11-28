import FormalConjectures.Wikipedia.GyarfasSumnerConjecture
import Mathlib

/-!
Kierstead and Penrice (1994): trees of radius two specify chi-bounded classes.

Proof outline (formalized below, following the template method as presented by Scott and
Seymour, Polynomial bounds for chromatic number V, arXiv 2202.05557, Sections 3 and 4, with a
self-contained Rodl-type base case and with all polynomial bookkeeping replaced by existence):
* every tree of radius at most two is an induced subgraph of the complete radius-two tree H_s;
* Theorem A, by induction on the clique number: H_s-free graphs have chromatic number bounded
  by a function of the clique number;
* inner induction on d: no stable (t,d)-core forces bounded chromatic number; the base d = 2 is a
  Rodl-type argument (Ramsey, pigeonhole, pure pairs), the step uses a greedy template sequence
  and the chain of 1-nice ... 8-nice reductions, each Hs-finding step ending in one embedding lemma.
Credit: @peyton-thalman (agent claude-code / claude-opus-5-5).
-/


/-! # Toolbox for the Kierstead–Penrice theorem (radius-two trees are χ-bounding). -/

open Finset

namespace GS

section Generic
variable {α : Type*} [DecidableEq α]

/-- A proper colouring of `X` for the relation `E`, with natural-number colours `< k`. -/
def PCol (E : α → α → Prop) (X : Finset α) (k : ℕ) : Prop :=
  ∃ c : α → ℕ, (∀ x ∈ X, c x < k) ∧ ∀ x ∈ X, ∀ y ∈ X, E x y → c x ≠ c y

theorem PCol.mono {E : α → α → Prop} {X Y : Finset α} {k k' : ℕ} (h : PCol E X k)
    (hY : Y ⊆ X) (hk : k ≤ k') : PCol E Y k' := by
  obtain ⟨c, hc, hp⟩ := h
  exact ⟨c, fun x hx => (hc x (hY hx)).trans_le hk, fun x hx y hy => hp x (hY hx) y (hY hy)⟩

/-- Degeneracy colouring. -/
theorem deg_col (E : α → α → Prop) [DecidableRel E] (hirr : ∀ x, ¬ E x x)
    (hsym : ∀ x y, E x y → E y x) (D : ℕ) :
    ∀ X : Finset α, (∀ Y ⊆ X, Y.Nonempty → ∃ y ∈ Y, (Y.filter (E y)).card < D) →
      PCol E X D := by
  intro X
  induction X using Finset.strongInduction with
  | H X ih =>
    intro hdeg
    rcases X.eq_empty_or_nonempty with rfl | hne
    · exact ⟨fun _ => 0, by simp, by simp⟩
    obtain ⟨y, hy, hyd⟩ := hdeg X subset_rfl hne
    obtain ⟨c, hc, hp⟩ := ih (X.erase y) (erase_ssubset hy)
      (fun Y hY hYne => hdeg Y (hY.trans (erase_subset _ _)) hYne)
    have himg : ((X.filter (E y)).image c).card < D := card_image_le.trans_lt hyd
    obtain ⟨m, hm, hmn⟩ : ∃ m ∈ range D, m ∉ (X.filter (E y)).image c := by
      by_contra hcon
      push_neg at hcon
      have := card_le_card (show range D ⊆ (X.filter (E y)).image c from fun m hm => hcon m hm)
      simp only [card_range] at this
      omega
    refine ⟨Function.update c y m, ?_, ?_⟩
    · intro x hx
      by_cases hxy : x = y
      · subst hxy; simpa using hm
      · rw [Function.update_of_ne hxy]; exact hc x (mem_erase.mpr ⟨hxy, hx⟩)
    · intro x hx z hz hE
      by_cases hxy : x = y
      · subst hxy
        have hzy : z ≠ x := fun h => hirr x (h ▸ hE)
        rw [Function.update_self, Function.update_of_ne hzy]
        intro h; apply hmn; exact mem_image.mpr ⟨z, mem_filter.mpr ⟨hz, hE⟩, h.symm⟩
      · by_cases hzy : z = y
        · subst hzy
          rw [Function.update_self, Function.update_of_ne hxy]
          intro h; apply hmn
          exact mem_image.mpr ⟨x, mem_filter.mpr ⟨hx, hsym _ _ hE⟩, h⟩
        · rw [Function.update_of_ne hxy, Function.update_of_ne hzy]
          exact hp x (mem_erase.mpr ⟨hxy, hx⟩) z (mem_erase.mpr ⟨hzy, hz⟩) hE

/-- Bounded degree colouring. -/
theorem col_of_deg_lt (E : α → α → Prop) [DecidableRel E] (hirr : ∀ x, ¬ E x x)
    (hsym : ∀ x y, E x y → E y x) (D : ℕ) (X : Finset α)
    (h : ∀ x ∈ X, (X.filter (E x)).card < D) : PCol E X D :=
  deg_col E hirr hsym D X fun Y hY ⟨y, hy⟩ =>
    ⟨y, hy, (card_le_card (filter_subset_filter _ hY)).trans_lt (h y (hY hy))⟩

/-- Out-degree partition: a relation with out-degrees `< D` splits into `2D-1` arc-free classes. -/
theorem outdeg_col (A : α → α → Prop) [DecidableRel A] (D : ℕ) (X : Finset α)
    (h : ∀ x ∈ X, (X.filter (fun y => y ≠ x ∧ A x y)).card < D) :
    PCol (fun x y => x ≠ y ∧ A x y) X (2 * D - 1) := by
  classical
  let E : α → α → Prop := fun x y => x ≠ y ∧ (A x y ∨ A y x)
  have hE : PCol E X (2 * D - 1) := by
    refine deg_col E (fun x h => h.1 rfl) (fun x y h => ⟨h.1.symm, h.2.symm⟩) _ X ?_
    intro Y hY hYne
    by_contra hcon
    push_neg at hcon
    have hD : 1 ≤ D := by
      obtain ⟨y, hy⟩ := hYne
      have := h y (hY hy); omega
    -- double counting
    have hout : ∀ y ∈ Y, (Y.filter (fun z => z ≠ y ∧ A y z)).card ≤ D - 1 := fun y hy => by
      have := (card_le_card (filter_subset_filter (fun z => z ≠ y ∧ A y z) hY)).trans_lt (h y (hY hy))
      omega
    have hsplit : ∀ y ∈ Y, (Y.filter (E y)).card ≤
        (Y.filter (fun z => z ≠ y ∧ A y z)).card + (Y.filter (fun z => z ≠ y ∧ A z y)).card := by
      intro y _
      refine (card_le_card ?_).trans (card_union_le _ _)
      intro z hz
      obtain ⟨hzY, hne, hA⟩ := mem_filter.mp hz
      rcases hA with hA | hA
      · exact mem_union_left _ (mem_filter.mpr ⟨hzY, hne.symm, hA⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨hzY, hne.symm, hA⟩)
    have hswap : ∑ y ∈ Y, (Y.filter (fun z => z ≠ y ∧ A z y)).card =
        ∑ y ∈ Y, (Y.filter (fun z => z ≠ y ∧ A y z)).card := by
      simp only [card_filter]
      rw [Finset.sum_comm]
      refine sum_congr rfl fun y _ => sum_congr rfl fun z _ => ?_
      simp only [ne_comm]
    have hsum : ∑ y ∈ Y, (Y.filter (E y)).card ≤ ∑ y ∈ Y, 2 * (D - 1) := by
      calc ∑ y ∈ Y, (Y.filter (E y)).card
          ≤ ∑ y ∈ Y, ((Y.filter (fun z => z ≠ y ∧ A y z)).card +
              (Y.filter (fun z => z ≠ y ∧ A z y)).card) := sum_le_sum hsplit
        _ = 2 * ∑ y ∈ Y, (Y.filter (fun z => z ≠ y ∧ A y z)).card := by
              rw [sum_add_distrib, hswap]; ring
        _ ≤ 2 * ∑ y ∈ Y, (D - 1) := Nat.mul_le_mul_left _ (sum_le_sum hout)
        _ = ∑ y ∈ Y, 2 * (D - 1) := by rw [mul_sum]
    have hlt : ∑ y ∈ Y, 2 * (D - 1) < ∑ y ∈ Y, (Y.filter (E y)).card :=
      sum_lt_sum_of_nonempty hYne fun y hy => by have := hcon y hy; omega
    omega
  obtain ⟨c, hc, hp⟩ := hE
  exact ⟨c, hc, fun x hx y hy hA => hp x hx y hy ⟨hA.1, Or.inl hA.2⟩⟩

/-- A large arc-free subset. -/
theorem outdeg_arcfree (A : α → α → Prop) [DecidableRel A] (D m : ℕ) (X : Finset α)
    (hD : 1 ≤ D) (h : ∀ x ∈ X, (X.filter (fun y => y ≠ x ∧ A x y)).card < D)
    (hX : (2 * D - 1) * m ≤ X.card) :
    ∃ I ⊆ X, I.card = m ∧ ∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬ A x y := by
  classical
  obtain ⟨c, hc, hp⟩ := outdeg_col A D X h
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨∅, empty_subset _, rfl, by simp⟩
  have hne : (range (2 * D - 1)).Nonempty := by
    rcases X.eq_empty_or_nonempty with hX0 | ⟨x, hx⟩
    · exfalso; rw [hX0, card_empty] at hX
      have : 1 ≤ (2 * D - 1) * m := Nat.mul_pos (by omega) hm
      omega
    · exact ⟨c x, mem_range.mpr (hc x hx)⟩
  obtain ⟨k, _, hk⟩ := exists_le_card_fiber_of_mul_le_card_of_maps_to
    (f := c) (s := X) (t := range (2 * D - 1)) (n := m)
    (fun x hx => mem_range.mpr (hc x hx)) hne (by simpa [card_range] using hX)
  obtain ⟨I, hIsub, hIcard⟩ := exists_subset_card_eq hk
  refine ⟨I, hIsub.trans (filter_subset _ _), hIcard, fun x hx y hy hxy hA => ?_⟩
  have hx' := mem_filter.mp (hIsub hx)
  have hy' := mem_filter.mp (hIsub hy)
  exact hp x hx'.1 y hy'.1 ⟨hxy, hA⟩ (hx'.2.trans hy'.2.symm)

end Generic

section Graph
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `S` is properly `k`-colourable (colours are naturals `< k`). -/
def col (S : Finset V) (k : ℕ) : Prop := PCol G.Adj S k

def IsStab (X : Finset V) : Prop := ∀ u ∈ X, ∀ v ∈ X, ¬ G.Adj u v
def IsClq (X : Finset V) : Prop := ∀ u ∈ X, ∀ v ∈ X, u ≠ v → G.Adj u v
/-- `S` contains no clique with more than `ω` vertices. -/
def Small (S : Finset V) (ω : ℕ) : Prop := ∀ X ⊆ S, IsClq G X → X.card ≤ ω
def nb (x : V) : Finset V := univ.filter (G.Adj x)

variable {G}

@[simp] theorem mem_nb {x y : V} : y ∈ nb G x ↔ G.Adj x y := by simp [nb]

theorem col.mono {S T : Finset V} {k k' : ℕ} (h : col G S k) (hT : T ⊆ S) (hk : k ≤ k') :
    col G T k' := PCol.mono h hT hk

theorem col_union {S T : Finset V} {a b : ℕ} (hS : col G S a) (hT : col G T b) :
    col G (S ∪ T) (a + b) := by
  obtain ⟨c₁, h₁, p₁⟩ := hS
  obtain ⟨c₂, h₂, p₂⟩ := hT
  refine ⟨fun v => if v ∈ S then c₁ v else a + c₂ v, ?_, ?_⟩
  · intro v hv
    by_cases hvS : v ∈ S
    · simp only [hvS, if_true]; have := h₁ v hvS; omega
    · simp only [hvS, if_false]
      have := h₂ v ((mem_union.mp hv).resolve_left hvS); omega
  · intro u hu v hv huv
    by_cases huS : u ∈ S <;> by_cases hvS : v ∈ S <;> simp only [huS, hvS, if_true, if_false]
    · exact p₁ u huS v hvS huv
    · have := h₁ u huS; omega
    · have := h₁ v hvS; omega
    · have hu' := (mem_union.mp hu).resolve_left huS
      have hv' := (mem_union.mp hv).resolve_left hvS
      have := p₂ u hu' v hv' huv; omega

theorem col_empty (k : ℕ) : col G ∅ k := ⟨fun _ => 0, by simp, by simp⟩

theorem col_biUnion {ι : Type*} [DecidableEq ι] (I : Finset ι) (P : ι → Finset V) (k : ℕ)
    (h : ∀ i ∈ I, col G (P i) k) : col G (I.biUnion P) (I.card * k) := by
  induction I using Finset.induction_on with
  | empty => simpa using col_empty 0
  | insert i I hi ih =>
    rw [biUnion_insert, card_insert_of_notMem hi]
    have := col_union (h i (mem_insert_self _ _)) (ih fun j hj => h j (mem_insert_of_mem hj))
    exact this.mono subset_rfl (by ring_nf; omega)

theorem col_singleton (x : V) : col G {x} 1 :=
  ⟨fun _ => 0, by simp, by simp⟩

/-- Product colouring (T3): a colouring proper on "same block" edges and one proper on the others. -/
theorem col_prod {S : Finset V} (same : V → V → Prop) {a b : ℕ}
    (h₁ : PCol (fun u v => G.Adj u v ∧ same u v) S a)
    (h₂ : PCol (fun u v => G.Adj u v ∧ ¬ same u v) S b) : col G S (a * b) := by
  obtain ⟨c₁, hc₁, p₁⟩ := h₁
  obtain ⟨c₂, hc₂, p₂⟩ := h₂
  refine ⟨fun v => c₁ v * b + c₂ v, ?_, ?_⟩
  · intro v hv
    have h1 := hc₁ v hv; have h2 := hc₂ v hv
    calc c₁ v * b + c₂ v < c₁ v * b + b := by omega
      _ = (c₁ v + 1) * b := by ring
      _ ≤ a * b := Nat.mul_le_mul_right _ h1
  · intro u hu v hv huv heq
    have hu2 := hc₂ u hu; have hv2 := hc₂ v hv
    dsimp only at heq
    have e1 : c₁ u = c₁ v := by
      rcases lt_trichotomy (c₁ u) (c₁ v) with h | h | h
      · exfalso
        have : (c₁ u + 1) * b ≤ c₁ v * b := Nat.mul_le_mul_right _ h
        nlinarith
      · exact h
      · exfalso
        have : (c₁ v + 1) * b ≤ c₁ u * b := Nat.mul_le_mul_right _ h
        nlinarith
    have e2 : c₂ u = c₂ v := by rw [e1] at heq; omega
    by_cases hs : same u v
    · exact p₁ u hu v hv ⟨huv, hs⟩ e1
    · exact p₂ u hu v hv ⟨huv, hs⟩ e2

/-! ### Ramsey -/

theorem ramsey_aux : ∀ n a b : ℕ, a + b = n → ∀ X : Finset V, 2 ^ (a + b) ≤ X.card →
    (∃ Y ⊆ X, Y.card = a ∧ IsClq G Y) ∨ (∃ Y ⊆ X, Y.card = b ∧ IsStab G Y) := by
  intro n
  induction n with
  | zero =>
    intro a b hab X _
    left; exact ⟨∅, empty_subset _, by simp; omega, by simp [IsClq]⟩
  | succ n ih =>
    intro a b hab X hX
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · left; exact ⟨∅, empty_subset _, by simp, by simp [IsClq]⟩
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · right; exact ⟨∅, empty_subset _, by simp, by simp [IsStab]⟩
    have hXne : X.Nonempty := card_pos.mp (lt_of_lt_of_le (Nat.one_le_two_pow) hX)
    obtain ⟨x, hx⟩ := hXne
    let A := (X.erase x).filter (G.Adj x)
    let B := (X.erase x).filter (fun y => ¬ G.Adj x y)
    have hAB : A.card + B.card = X.card - 1 := by
      rw [card_filter_add_card_filter_not, card_erase_of_mem hx]
    have hpow : 2 ^ (a + b) = 2 ^ (a - 1 + b) + 2 ^ (a + (b - 1)) := by
      have e1 : a + b = (a - 1 + b) + 1 := by omega
      have e2 : a - 1 + b = a + (b - 1) := by omega
      rw [e1, pow_succ, ← e2]; ring
    by_cases hA : 2 ^ (a - 1 + b) ≤ A.card
    · rcases ih (a - 1) b (by omega) A hA with ⟨Y, hY, hYc, hYq⟩ | ⟨Y, hY, hYc, hYs⟩
      · left
        have hxY : x ∉ Y := fun h => by have := hY h; simp [A] at this
        refine ⟨insert x Y, insert_subset hx (hY.trans ((filter_subset _ _).trans (erase_subset _ _))),
          by rw [card_insert_of_notMem hxY, hYc]; omega, ?_⟩
        have hxadj : ∀ y ∈ Y, G.Adj x y := fun y hy => (mem_filter.mp (hY hy)).2
        intro u hu v hv huv
        rcases mem_insert.mp hu with h1 | h1 <;> rcases mem_insert.mp hv with h2 | h2
        · exact absurd (h1.trans h2.symm) huv
        · rw [h1]; exact hxadj v h2
        · rw [h2]; exact (hxadj u h1).symm
        · exact hYq u h1 v h2 huv
      · right
        exact ⟨Y, hY.trans ((filter_subset _ _).trans (erase_subset _ _)), hYc, hYs⟩
    · have hB : 2 ^ (a + (b - 1)) ≤ B.card := by omega
      rcases ih a (b - 1) (by omega) B hB with ⟨Y, hY, hYc, hYq⟩ | ⟨Y, hY, hYc, hYs⟩
      · left
        exact ⟨Y, hY.trans ((filter_subset _ _).trans (erase_subset _ _)), hYc, hYq⟩
      · right
        have hxY : x ∉ Y := fun h => by have := hY h; simp [B] at this
        refine ⟨insert x Y, insert_subset hx (hY.trans ((filter_subset _ _).trans (erase_subset _ _))),
          by rw [card_insert_of_notMem hxY, hYc]; omega, ?_⟩
        have hxn : ∀ y ∈ Y, ¬ G.Adj x y := fun y hy => (mem_filter.mp (hY hy)).2
        intro u hu v hv
        rcases mem_insert.mp hu with h1 | h1 <;> rcases mem_insert.mp hv with h2 | h2
        · rw [h1, h2]; exact G.irrefl
        · rw [h1]; exact hxn v h2
        · rw [h2]; exact fun h => hxn u h1 h.symm
        · exact hYs u h1 v h2

/-- The Ramsey number bound used throughout: `r ω b = 2^(ω+1+b)`. -/
def rr (ω b : ℕ) : ℕ := 2 ^ (ω + 1 + b)

/-- (R): inside an `ω`-small set, `rr ω b` vertices contain a stable `b`-set. -/
theorem ramsey_stable {S X : Finset V} {ω b : ℕ} (hS : Small G S ω) (hX : X ⊆ S)
    (hc : rr ω b ≤ X.card) : ∃ Y ⊆ X, Y.card = b ∧ IsStab G Y := by
  rcases ramsey_aux (G := G) _ (ω + 1) b rfl X hc with ⟨Y, hY, hYc, hYq⟩ | h
  · have := hS Y (hY.trans hX) hYq; omega
  · exact h

theorem IsStab.mono {X Y : Finset V} (h : IsStab G X) (hY : Y ⊆ X) : IsStab G Y :=
  fun u hu v hv => h u (hY hu) v (hY hv)

theorem Small.mono {S T : Finset V} {ω : ℕ} (h : Small G S ω) (hT : T ⊆ S) : Small G T ω :=
  fun X hX hq => h X (hX.trans hT) hq

/-- Neighbourhoods inside an `(ω+1)`-small set are `ω`-small. -/
theorem Small.nb {S : Finset V} {ω : ℕ} (h : Small G S (ω + 1)) {x : V} (hx : x ∈ S) :
    Small G (nb G x ∩ S) ω := by
  intro X hX hq
  have hxX : x ∉ X := fun hxX => G.irrefl (mem_nb.mp (mem_inter.mp (hX hxX)).1)
  have := h (insert x X) (insert_subset hx (hX.trans inter_subset_right)) ?_
  · rw [card_insert_of_notMem hxX] at this; omega
  intro u hu v hv huv
  have hadj : ∀ y ∈ X, G.Adj x y := fun y hy => mem_nb.mp (mem_inter.mp (hX hy)).1
  rcases mem_insert.mp hu with h1 | h1 <;> rcases mem_insert.mp hv with h2 | h2
  · exact absurd (h1.trans h2.symm) huv
  · rw [h1]; exact hadj v h2
  · rw [h2]; exact (hadj u h1).symm
  · exact hq u h1 v h2 huv

/-- T6: a set covered by `k` closed neighbourhoods inside `S` is `k(ℓ+1)`-colourable, given
colourings of the neighbourhoods. -/
theorem col_nbhds {S P K : Finset V} {ℓ : ℕ} (hOIH : ∀ x ∈ S, col G (nb G x ∩ S) ℓ)
    (hK : K ⊆ S) (hP : P ⊆ S) (hcov : ∀ v ∈ P, v ∈ K ∨ ∃ x ∈ K, G.Adj x v) :
    col G P (K.card * (ℓ + 1)) := by
  have hsub : P ⊆ K.biUnion (fun x => insert x (nb G x ∩ S)) := by
    intro v hv
    rcases hcov v hv with h | ⟨x, hx, hxv⟩
    · exact mem_biUnion.mpr ⟨v, h, mem_insert_self _ _⟩
    · exact mem_biUnion.mpr ⟨x, hx, mem_insert_of_mem (mem_inter.mpr ⟨mem_nb.mpr hxv, hP hv⟩)⟩
  refine (col_biUnion K _ (ℓ + 1) fun x hx => ?_).mono hsub le_rfl
  have : insert x (nb G x ∩ S) = {x} ∪ (nb G x ∩ S) := by rw [insert_eq]
  rw [this]
  exact (col_union (col_singleton x) (hOIH x (hK hx))).mono subset_rfl (by omega)

end Graph

end GS


open Finset

namespace GS

/-! ## The complete radius-two tree `H_s` -/

abbrev HV (s : ℕ) := Unit ⊕ Fin s ⊕ (Fin s × Fin s)

def HAdj {s : ℕ} : HV s → HV s → Prop
  | .inl _, .inr (.inl _) => True
  | .inr (.inl _), .inl _ => True
  | .inr (.inl i), .inr (.inr p) => p.1 = i
  | .inr (.inr p), .inr (.inl i) => p.1 = i
  | _, _ => False

def Hs (s : ℕ) : SimpleGraph (HV s) where
  Adj := HAdj
  symm := ⟨fun x y h => by
    rcases x with _ | i | p <;> rcases y with _ | j | q <;> simp_all [HAdj]⟩
  loopless := ⟨fun x h => by rcases x with _ | i | p <;> simp_all [HAdj]⟩

section Embed
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def embF {s : ℕ} (r : V) (a : Fin s → V) (y : Fin s → Fin s → V) : HV s → V
  | .inl _ => r
  | .inr (.inl i) => a i
  | .inr (.inr p) => y p.1 p.2

/-- T8, functional form. -/
theorem embed_Hs {s : ℕ} (r : V) (a : Fin s → V) (y : Fin s → Fin s → V)
    (h1 : ∀ i, G.Adj r (a i))
    (h2 : ∀ i j, i ≠ j → ¬ G.Adj (a i) (a j))
    (h2' : Function.Injective a)
    (h3a : ∀ i j, G.Adj (a i) (y i j))
    (h3b : ∀ i j, ¬ G.Adj r (y i j))
    (h3c : ∀ i j, y i j ≠ r)
    (h3d : ∀ i j k, ¬ G.Adj (y i j) (y i k))
    (h3e : ∀ i, Function.Injective (y i))
    (h4 : ∀ i j k, i ≠ j → ¬ G.Adj (a j) (y i k))
    (h5 : ∀ i j k l, i ≠ j → ¬ G.Adj (y i k) (y j l)) : (Hs s).IsIndContained G := by
  have hra : ∀ i, a i ≠ r := fun i h => G.irrefl (h ▸ h1 i)
  have hya : ∀ i j k, y i j ≠ a k := by
    intro i j k h
    by_cases hik : i = k
    · subst hik; exact G.irrefl (h ▸ h3a i j)
    · exact h2 i k hik (h ▸ h3a i j)
  have hyy : ∀ i j i' k, i ≠ i' → y i j ≠ y i' k := by
    intro i j i' k hii h
    exact h4 i i' j hii (h ▸ h3a i' k)
  have hiff : ∀ x z, G.Adj (embF r a y x) (embF r a y z) ↔ (Hs s).Adj x z := by
    intro x z
    rcases x with _ | i | ⟨i, j⟩ <;> rcases z with _ | k | ⟨k, l⟩ <;>
      simp only [embF, Hs, HAdj]
    · simp [G.irrefl]
    · simp [h1 k]
    · simp [h3b k l]
    · simp [(h1 i).symm]
    · simp only [iff_false]
      by_cases hik : i = k
      · subst hik; exact G.irrefl
      · exact h2 i k hik
    · constructor
      · intro h
        by_contra hki
        exact h4 k i l hki h
      · intro h; subst h; exact h3a k l
    · simp only [iff_false]; exact fun h => h3b i j h.symm
    · constructor
      · intro h
        by_contra hik
        exact h4 i k j hik h.symm
      · intro h; subst h; exact (h3a i j).symm
    · simp only [iff_false]
      by_cases hik : i = k
      · subst hik; exact h3d i j l
      · exact h5 i k j l hik
  have hinj : Function.Injective (embF r a y) := by
    intro x z hxz
    rcases x with _ | i | ⟨i, j⟩ <;> rcases z with _ | k | ⟨k, l⟩ <;> simp only [embF] at hxz
    · rfl
    · exact absurd hxz.symm (hra k)
    · exact absurd hxz.symm (h3c k l)
    · exact absurd hxz (hra i)
    · rw [h2' hxz]
    · exact absurd hxz.symm (hya k l i)
    · exact absurd hxz (h3c i j)
    · exact absurd hxz (hya i j k)
    · by_cases hik : i = k
      · subst hik; rw [h3e i hxz]
      · exact absurd hxz (hyy i j k l hik)
  exact ⟨⟨⟨embF r a y, hinj⟩, fun {x z} => hiff x z⟩⟩

theorem exists_enum {Y : Finset V} {s : ℕ} (h : Y.card = s) :
    ∃ f : Fin s → V, Function.Injective f ∧ ∀ j, f j ∈ Y := by
  refine ⟨fun j => (Y.equivFin.symm (Fin.cast h.symm j)).1, ?_, fun j => (Y.equivFin.symm _).2⟩
  intro j k hjk
  have := Subtype.val_injective hjk
  have := Y.equivFin.symm.injective this
  exact Fin.cast_injective _ this

theorem exists_enum' {ι : Type*} {I : Finset ι} {s : ℕ} (h : I.card = s) :
    ∃ f : Fin s → ι, Function.Injective f ∧ ∀ j, f j ∈ I := by
  classical
  refine ⟨fun j => (I.equivFin.symm (Fin.cast h.symm j)).1, ?_, fun j => (I.equivFin.symm _).2⟩
  intro j k hjk
  have := Subtype.val_injective hjk
  have := I.equivFin.symm.injective this
  exact Fin.cast_injective _ this

/-- T8, Finset form: root `r`, children `a i` (`i ∈ I`), leaf sets `Y i`. -/
theorem embed_HsF {ι : Type*} [DecidableEq ι] {s : ℕ} (I : Finset ι) (hI : I.card = s)
    (r : V) (a : ι → V) (Y : ι → Finset V)
    (hY : ∀ i ∈ I, (Y i).card = s)
    (h1 : ∀ i ∈ I, G.Adj r (a i))
    (h2 : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ¬ G.Adj (a i) (a j) ∧ a i ≠ a j)
    (h3 : ∀ i ∈ I, ∀ y ∈ Y i, G.Adj (a i) y ∧ ¬ G.Adj r y ∧ y ≠ r)
    (h3s : ∀ i ∈ I, IsStab G (Y i))
    (h4 : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ y ∈ Y i, ¬ G.Adj (a j) y)
    (h5 : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ y ∈ Y i, ∀ z ∈ Y j, ¬ G.Adj y z) : (Hs s).IsIndContained G := by
  obtain ⟨e, he, heI⟩ := exists_enum' hI
  have hy : ∀ i : Fin s, ∃ f : Fin s → V, Function.Injective f ∧ ∀ j, f j ∈ Y (e i) :=
    fun i => exists_enum (hY (e i) (heI i))
  choose y hyinj hyY using hy
  refine embed_Hs r (a ∘ e) y (fun i => h1 _ (heI i))
    (fun i j hij => (h2 _ (heI i) _ (heI j) (he.ne hij)).1)
    (fun i j hij => by
      by_contra hne
      exact (h2 _ (heI i) _ (heI j) (fun h => hne (he h))).2 hij)
    (fun i j => (h3 _ (heI i) _ (hyY i j)).1)
    (fun i j => (h3 _ (heI i) _ (hyY i j)).2.1)
    (fun i j => (h3 _ (heI i) _ (hyY i j)).2.2)
    (fun i j k => h3s _ (heI i) _ (hyY i j) _ (hyY i k))
    hyinj
    (fun i j k hij => h4 _ (heI i) _ (heI j) (he.ne hij) _ (hyY i k))
    (fun i j k l hij => h5 _ (heI i) _ (heI j) (he.ne hij) _ (hyY i k) _ (hyY j l))

end Embed

/-! ## Reduction of a radius-≤2 tree to `H_s` -/

section Tree
variable {W : Type} [Fintype W] [DecidableEq W] {T : SimpleGraph W}

theorem bridge_false (hT : T.IsAcyclic) {u v : W} (huv : T.Adj u v)
    (h : (T.deleteEdges {s(u, v)}).Reachable u v) : False :=
  (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT huv) h

theorem del_adj {u v a b : W} (hab : T.Adj a b)
    (hne : ¬ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) :
    (T.deleteEdges {s(u, v)}).Adj a b := by
  rw [SimpleGraph.deleteEdges_adj]
  refine ⟨hab, ?_⟩
  rw [Set.mem_singleton_iff, Sym2.eq_iff]
  exact hne

theorem tree_le_Hs (hT : T.IsTree) (c : W) (hc : ∀ w, T.dist c w ≤ 2) (s : ℕ)
    (hs : Fintype.card W ≤ s) : T.IsIndContained (Hs s) := by
  classical
  have hconn := hT.isConnected
  have hacyc := hT.IsAcyclic
  have hpar : ∀ w, w ≠ c → ¬ T.Adj c w → ∃ u, T.Adj c u ∧ T.Adj u w := by
    intro w hwc hcw
    have hd : T.dist c w = 2 := by
      have h0 : T.dist c w ≠ 0 := fun h => hwc ((hconn.dist_eq_zero_iff).mp h).symm
      have h1 : T.dist c w ≠ 1 := fun h => hcw (SimpleGraph.dist_eq_one_iff_adj.mp h)
      have := hc w; omega
    obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist c w
    rw [hd] at hp
    cases p with
    | nil => simp at hp
    | cons h p =>
      cases p with
      | nil => simp at hp
      | cons h' p =>
        cases p with
        | nil => exact ⟨_, h, h'⟩
        | cons _ _ => simp at hp
  let par : W → W := fun w => if h : w ≠ c ∧ ¬ T.Adj c w then Classical.choose (hpar w h.1 h.2) else c
  have hpar1 : ∀ w, w ≠ c → ¬ T.Adj c w → T.Adj c (par w) ∧ T.Adj (par w) w := by
    intro w h1 h2
    have := Classical.choose_spec (hpar w h1 h2)
    simp only [par, dif_pos (show w ≠ c ∧ ¬ T.Adj c w from ⟨h1, h2⟩)]
    exact this
  -- tree facts
  have fa : ∀ u u', T.Adj c u → T.Adj c u' → ¬ T.Adj u u' := by
    intro u u' hu hu' huu
    apply bridge_false hacyc huu
    have hcu : c ≠ u := T.ne_of_adj hu
    have hcu' : c ≠ u' := T.ne_of_adj hu'
    refine (SimpleGraph.Adj.reachable (del_adj hu.symm ?_)).trans
      (SimpleGraph.Adj.reachable (del_adj hu' ?_))
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact hcu' h
      · exact (T.ne_of_adj huu) h
    · rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact hcu h
      · exact hcu' h
  have fb : ∀ w u, w ≠ c → ¬ T.Adj c w → T.Adj c u → T.Adj u w → u = par w := by
    intro w u hwc hcw hcu huw
    by_contra hne
    obtain ⟨hp1, hp2⟩ := hpar1 w hwc hcw
    apply bridge_false hacyc huw
    have hcu' : c ≠ u := T.ne_of_adj hcu
    refine (SimpleGraph.Adj.reachable (del_adj hcu.symm ?_)).trans
      ((SimpleGraph.Adj.reachable (del_adj hp1 ?_)).trans
        (SimpleGraph.Adj.reachable (del_adj hp2 ?_)))
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact hwc h.symm
      · exact (T.ne_of_adj huw) h
    · rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact hcu' h
      · exact hwc h.symm
    · rintro (⟨h, _⟩ | ⟨_, h⟩)
      · exact hne h.symm
      · exact (T.ne_of_adj huw) h.symm
  have fc : ∀ w w', w ≠ c → ¬ T.Adj c w → w' ≠ c → ¬ T.Adj c w' → ¬ T.Adj w w' := by
    intro w w' hwc hcw hwc' hcw' hww
    obtain ⟨hp1, hp2⟩ := hpar1 w hwc hcw
    obtain ⟨hq1, hq2⟩ := hpar1 w' hwc' hcw'
    apply bridge_false hacyc hww
    refine (SimpleGraph.Adj.reachable (del_adj hp2.symm ?_)).trans
      ((SimpleGraph.Adj.reachable (del_adj hp1.symm ?_)).trans
        ((SimpleGraph.Adj.reachable (del_adj hq1 ?_)).trans
          (SimpleGraph.Adj.reachable (del_adj hq2 ?_))))
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact hcw' (h ▸ hp1)
      · exact (T.ne_of_adj hww) h
    · rintro (⟨_, h⟩ | ⟨_, h⟩)
      · exact hwc' h.symm
      · exact hwc h.symm
    · rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact hwc h.symm
      · exact hwc' h.symm
    · rintro (⟨h, _⟩ | ⟨_, h⟩)
      · exact hcw (h ▸ hq1)
      · exact (T.ne_of_adj hww) h.symm
  -- the embedding
  let ι : W ↪ Fin s := (Fintype.equivFin W).toEmbedding.trans (Fin.castLEEmb hs)
  let φ : W → HV s := fun w =>
    if w = c then .inl () else if T.Adj c w then .inr (.inl (ι w)) else .inr (.inr (ι (par w), ι w))
  have trich : ∀ x, x = c ∨ (x ≠ c ∧ T.Adj c x) ∨ (x ≠ c ∧ ¬ T.Adj c x) := by
    intro x; by_cases h : x = c
    · exact Or.inl h
    · by_cases h' : T.Adj c x
      · exact Or.inr (Or.inl ⟨h, h'⟩)
      · exact Or.inr (Or.inr ⟨h, h'⟩)
  have hφ0 : φ c = .inl () := by simp [φ]
  have hφ1 : ∀ x, x ≠ c → T.Adj c x → φ x = .inr (.inl (ι x)) := by
    intro x h1 h2; simp [φ, h1, h2]
  have hφ2 : ∀ x, x ≠ c → ¬ T.Adj c x → φ x = .inr (.inr (ι (par x), ι x)) := by
    intro x h1 h2; simp [φ, h1, h2]
  have hinj : Function.Injective φ := by
    intro x z hxz
    rcases trich x with hx | ⟨hx, hx'⟩ | ⟨hx, hx'⟩ <;>
    rcases trich z with hz | ⟨hz, hz'⟩ | ⟨hz, hz'⟩
    · rw [hx, hz]
    · rw [hx, hφ0, hφ1 z hz hz'] at hxz; cases hxz
    · rw [hx, hφ0, hφ2 z hz hz'] at hxz; cases hxz
    · rw [hz, hφ0, hφ1 x hx hx'] at hxz; cases hxz
    · rw [hφ1 x hx hx', hφ1 z hz hz'] at hxz
      simp only [Sum.inr.injEq, Sum.inl.injEq] at hxz
      exact ι.injective hxz
    · rw [hφ1 x hx hx', hφ2 z hz hz'] at hxz; simp at hxz
    · rw [hz, hφ0, hφ2 x hx hx'] at hxz; cases hxz
    · rw [hφ2 x hx hx', hφ1 z hz hz'] at hxz; simp at hxz
    · rw [hφ2 x hx hx', hφ2 z hz hz'] at hxz
      simp only [Sum.inr.injEq, Prod.mk.injEq] at hxz
      exact ι.injective hxz.2
  have hiff : ∀ x z, (Hs s).Adj (φ x) (φ z) ↔ T.Adj x z := by
    intro x z
    rcases trich x with hx | ⟨hx, hx'⟩ | ⟨hx, hx'⟩ <;>
    rcases trich z with hz | ⟨hz, hz'⟩ | ⟨hz, hz'⟩
    · rw [hx, hz, hφ0]; simp [Hs, HAdj, T.irrefl]
    · rw [hx, hφ0, hφ1 z hz hz']; simp [Hs, HAdj, hz']
    · rw [hx, hφ0, hφ2 z hz hz']; simp [Hs, HAdj, hz']
    · rw [hz, hφ0, hφ1 x hx hx']; simp [Hs, HAdj, hx'.symm]
    · rw [hφ1 x hx hx', hφ1 z hz hz']; simp only [Hs, HAdj, false_iff]; exact fa x z hx' hz'
    · rw [hφ1 x hx hx', hφ2 z hz hz']; simp only [Hs, HAdj]
      constructor
      · intro h
        have := ι.injective h
        rw [← this]; exact (hpar1 z hz hz').2
      · intro h
        rw [fb z x hz hz' hx' h]
    · rw [hz, hφ0, hφ2 x hx hx']; simp only [Hs, HAdj, false_iff]; exact fun h => hx' h.symm
    · rw [hφ2 x hx hx', hφ1 z hz hz']; simp only [Hs, HAdj]
      constructor
      · intro h
        have := ι.injective h
        rw [← this]; exact (hpar1 x hx hx').2.symm
      · intro h
        rw [fb x z hx hx' hz' h.symm]
    · rw [hφ2 x hx hx', hφ2 z hz hz']; simp only [Hs, HAdj, false_iff]
      exact fc x z hx hx' hz hz'
  exact ⟨⟨⟨φ, hinj⟩, fun {x z} => hiff x z⟩⟩

end Tree

end GS


open Finset

namespace GS

section Defs
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def Compl (X Y : Finset V) : Prop := ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y
def Anti (X Y : Finset V) : Prop := ∀ x ∈ X, ∀ y ∈ Y, ¬ G.Adj x y

/-- No "K-pair": two disjoint `T₀`-subsets of `S`, complete to each other. -/
def NoKPair (S : Finset V) (T₀ : ℕ) : Prop :=
  ∀ X ⊆ S, ∀ Y ⊆ S, Disjoint X Y → X.card = T₀ → Y.card = T₀ → ¬ Compl G X Y

/-- A stable `(w,d)`-core inside `S`. -/
def HasCore (S : Finset V) (w d : ℕ) : Prop :=
  ∃ A : Fin d → Finset V, (∀ i, A i ⊆ S ∧ (A i).card = w ∧ IsStab G (A i)) ∧
    ∀ i j, i ≠ j → Disjoint (A i) (A j) ∧ Compl G (A i) (A j)

end Defs

section Lemmas
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Anti.symm {X Y : Finset V} (h : Anti G X Y) : Anti G Y X :=
  fun y hy x hx hyx => h x hx y hy hyx.symm

theorem Anti.mono {X Y X' Y' : Finset V} (h : Anti G X Y) (hX : X' ⊆ X) (hY : Y' ⊆ Y) :
    Anti G X' Y' := fun x hx y hy => h x (hX hx) y (hY hy)

theorem Compl.mono {X Y X' Y' : Finset V} (h : Compl G X Y) (hX : X' ⊆ X) (hY : Y' ⊆ Y) :
    Compl G X' Y' := fun x hx y hy => h x (hX hx) y (hY hy)

/-- T7: in an `ω`-small set with no stable `(t,2)`-core there is no K-pair for `rr ω t`. -/
theorem noKPair_of_noCore {S : Finset V} {ω t : ℕ} (hS : Small G S ω) (hc : ¬ HasCore G S t 2) :
    NoKPair G S (rr ω t) := by
  intro X hX Y hY hXY hXc hYc hcomp
  obtain ⟨X', hX', hX'c, hX's⟩ := ramsey_stable hS hX hXc.ge
  obtain ⟨Y', hY', hY'c, hY's⟩ := ramsey_stable hS hY hYc.ge
  apply hc
  refine ⟨![X', Y'], ?_, ?_⟩
  · intro i
    fin_cases i
    · exact ⟨hX'.trans hX, hX'c, hX's⟩
    · exact ⟨hY'.trans hY, hY'c, hY's⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact ⟨Disjoint.mono hX' hY' hXY, hcomp.mono hX' hY'⟩
    · exact ⟨(Disjoint.mono hX' hY' hXY).symm,
        fun y hy x hx => (hcomp x (hX' hx) y (hY' hy)).symm⟩
    · exact absurd rfl hij

/-- Lemma 5.1 (bipartite pure pair). -/
theorem br_lemma {S X Y : Finset V} {T₀ p : ℕ} (hK : NoKPair G S T₀) (hX : X ⊆ S) (hY : Y ⊆ S)
    (hXY : Disjoint X Y) (hXc : X.card = p + T₀ - 1) (hT : 1 ≤ T₀)
    (hYc : max p T₀ * 2 ^ X.card ≤ Y.card) :
    ∃ X' ⊆ X, ∃ Y' ⊆ Y, X'.card = p ∧ Y'.card = p ∧ Anti G X' Y' := by
  obtain ⟨Wt, hWt, hfib⟩ := exists_le_card_fiber_of_mul_le_card_of_maps_to
    (f := fun y => X.filter (G.Adj y)) (s := Y) (t := X.powerset) (n := max p T₀)
    (fun y _ => mem_powerset.mpr (filter_subset _ _)) ⟨∅, empty_mem_powerset _⟩
    (by rw [card_powerset, mul_comm]; exact hYc)
  set F := Y.filter (fun y => X.filter (G.Adj y) = Wt) with hF
  have hWtX : Wt ⊆ X := mem_powerset.mp hWt
  have hFW : ∀ y ∈ F, ∀ x ∈ X, G.Adj y x ↔ x ∈ Wt := by
    intro y hy x hx
    have := (mem_filter.mp hy).2
    rw [← this]; simp [hx]
  have hWsmall : Wt.card < T₀ := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨W₁, hW₁, hW₁c⟩ := exists_subset_card_eq hcon
    obtain ⟨F₁, hF₁, hF₁c⟩ := exists_subset_card_eq ((le_max_right p T₀).trans hfib)
    apply hK W₁ ((hW₁.trans hWtX).trans hX) F₁ ((hF₁.trans (filter_subset _ _)).trans hY)
      (Disjoint.mono (hW₁.trans hWtX) (hF₁.trans (filter_subset _ _)) hXY) hW₁c hF₁c
    intro x hx y hy
    exact ((hFW y (hF₁ hy) x (hWtX (hW₁ hx))).mpr (hW₁ hx)).symm
  have hcomp : p ≤ (X \ Wt).card := by
    rw [card_sdiff_of_subset hWtX]; omega
  obtain ⟨X', hX', hX'c⟩ := exists_subset_card_eq hcomp
  obtain ⟨Y', hY', hY'c⟩ := exists_subset_card_eq ((le_max_left p T₀).trans hfib)
  refine ⟨X', hX'.trans sdiff_subset, Y', hY'.trans (filter_subset _ _), hX'c, hY'c, ?_⟩
  intro x hx y hy hxy
  have hx' := mem_sdiff.mp (hX' hx)
  exact hx'.2 ((hFW y (hY' hy) x hx'.1).mp hxy.symm)

/-- Iterated bipartite pure pairs against `m` sets. -/
theorem iter_lemma (T₀ : ℕ) (hT : 1 ≤ T₀) : ∀ m M : ℕ, ∃ L : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S X : Finset V) (Z : Fin m → Finset V),
    NoKPair G S T₀ → X ⊆ S → (∀ i, Z i ⊆ S) → (∀ i, Disjoint X (Z i)) →
    L ≤ X.card → (∀ i, L ≤ (Z i).card) →
    ∃ X' ⊆ X, ∃ Z' : Fin m → Finset V, M ≤ X'.card ∧
      ∀ i, Z' i ⊆ Z i ∧ M ≤ (Z' i).card ∧ Anti G X' (Z' i) := by
  intro m
  induction m with
  | zero =>
    intro M
    refine ⟨M, fun G _ S X Z _ _ _ _ hX _ => ⟨X, subset_rfl, Z, hX, fun i => i.elim0⟩⟩
  | succ m ih =>
    intro M
    obtain ⟨L', hL'⟩ := ih M
    set p := max L' M
    refine ⟨max L' (max (p + T₀ - 1) (max p T₀ * 2 ^ (p + T₀ - 1))), ?_⟩
    intro V _ _ G _ S X Z hK hX hZ hXZ hXc hZc
    obtain ⟨X₀, hX₀, hX₀c⟩ := exists_subset_card_eq
      ((le_max_left _ _).trans ((le_max_right L' _).trans hXc))
    obtain ⟨X₁, hX₁, Zl, hZl, hX₁c, hZlc, hanti⟩ := br_lemma hK (hX₀.trans hX) (hZ (Fin.last m))
      (Disjoint.mono_left hX₀ (hXZ _)) hX₀c hT
      (by rw [hX₀c]; exact (le_max_right _ _).trans ((le_max_right L' _).trans (hZc _)))
    obtain ⟨X', hX', Z', hX'c, hZ'⟩ := hL' G S X₁ (fun i => Z (Fin.castSucc i)) hK
      ((hX₁.trans hX₀).trans hX) (fun i => hZ _) (fun i => Disjoint.mono_left (hX₁.trans hX₀) (hXZ _))
      (by rw [hX₁c]; exact le_max_left _ _) (fun i => (le_max_left _ _).trans (hZc _))
    refine ⟨X', hX'.trans (hX₁.trans hX₀), Fin.lastCases Zl Z', hX'c, ?_⟩
    intro i
    induction i using Fin.lastCases with
    | last =>
      simp only [Fin.lastCases_last]
      exact ⟨hZl, by rw [hZlc]; exact le_max_right _ _, hanti.mono hX' subset_rfl⟩
    | cast i =>
      simp only [Fin.lastCases_castSucc]
      exact hZ' i

/-- Lemma 5.2: many pairwise anticomplete `p`-sets. -/
theorem ma_lemma (T₀ p : ℕ) (hT : 1 ≤ T₀) : ∀ k : ℕ, ∃ N : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (Z : Fin k → Finset V),
    NoKPair G S T₀ → (∀ i, Z i ⊆ S) → (∀ i j, i ≠ j → Disjoint (Z i) (Z j)) →
    (∀ i, N ≤ (Z i).card) →
    ∃ Y : Fin k → Finset V, (∀ i, Y i ⊆ Z i ∧ (Y i).card = p) ∧
      ∀ i j, i ≠ j → Anti G (Y i) (Y j) := by
  intro k
  induction k with
  | zero => exact ⟨0, fun G _ S Z _ _ _ _ => ⟨Z, fun i => i.elim0, fun i => i.elim0⟩⟩
  | succ k ih =>
    obtain ⟨Nk, hNk⟩ := ih
    obtain ⟨L, hL⟩ := iter_lemma T₀ hT k (max Nk p)
    refine ⟨L, ?_⟩
    intro V _ _ G _ S Z hK hZ hdisj hZc
    obtain ⟨X', hX', Z', hX'c, hZ'⟩ := hL G S (Z (Fin.last k)) (fun i => Z (Fin.castSucc i)) hK
      (hZ _) (fun i => hZ _)
      (fun i => hdisj _ _ (Fin.castSucc_lt_last i).ne') (hZc _) (fun i => hZc _)
    obtain ⟨Y, hY, hYa⟩ := hNk G S Z' hK (fun i => (hZ' i).1.trans (hZ _))
      (fun i j hij => Disjoint.mono (hZ' i).1 (hZ' j).1 (hdisj _ _ (fun h => hij (Fin.castSucc_injective _ h))))
      (fun i => (le_max_left _ _).trans (hZ' i).2.1)
    obtain ⟨Yl, hYl, hYlc⟩ := exists_subset_card_eq ((le_max_right Nk p).trans hX'c)
    refine ⟨Fin.lastCases Yl Y, ?_, ?_⟩
    · intro i
      induction i using Fin.lastCases with
      | last => simp only [Fin.lastCases_last]; exact ⟨hYl.trans hX', hYlc⟩
      | cast i => simp only [Fin.lastCases_castSucc]; exact ⟨(hY i).1.trans (hZ' i).1, (hY i).2⟩
    · intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd rfl hij
        | cast j =>
          simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
          exact (hZ' j).2.2.mono hYl (hY j).1
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
          exact ((hZ' i).2.2.mono hYl (hY i).1).symm
        | cast j =>
          simp only [Fin.lastCases_castSucc]
          exact hYa i j (fun h => hij (by rw [h]))

end Lemmas

section Base
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- T4a: a set that is not `D`-colourable contains a nonempty subset of minimum degree `≥ D`. -/
theorem exists_minDeg_of_not_col {S : Finset V} {D : ℕ} (h : ¬ col G S D) :
    ∃ S' ⊆ S, S'.Nonempty ∧ ∀ v ∈ S', D ≤ (S'.filter (G.Adj v)).card := by
  by_contra hcon
  push_neg at hcon
  exact h (deg_col G.Adj (fun x => G.irrefl) (fun x y h => h.symm) D S hcon)

end Base

/-- The base case S(2) (Rödl-type). -/
theorem base_S2 (s ω t : ℕ) (hs : 2 ≤ s) (ht : 1 ≤ t) : ∃ g : ℕ, ∀ {V : Type} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj], ¬ (Hs s).IsIndContained G →
    ∀ S : Finset V, Small G S ω → ¬ HasCore G S t 2 → col G S g := by
  set T₀ := rr ω t with hT₀
  have hT₀1 : 1 ≤ T₀ := Nat.one_le_two_pow
  obtain ⟨Ns, hNs⟩ := ma_lemma T₀ s hT₀1 s
  set n₂ := max Ns T₀
  set m := (2 * T₀ - 1) * s
  set n₁ := 2 ^ m * n₂
  set K := rr ω n₁
  set M := m + T₀ - 1
  set D := max (rr ω M) (T₀ * K + T₀)
  refine ⟨D, ?_⟩
  intro V _ _ G _ hfree S hS hcore
  have hK := noKPair_of_noCore hS hcore
  rw [← hT₀] at hK
  by_contra hcol
  obtain ⟨S', hS'S, hS'ne, hdeg⟩ := exists_minDeg_of_not_col hcol
  obtain ⟨r, hrS', hrmin⟩ := exists_min_image S' (fun v => (S'.filter (G.Adj v)).card) hS'ne
  set Nr := S'.filter (G.Adj r) with hNr
  have hδ : D ≤ Nr.card := hdeg r hrS'
  -- Step 1
  obtain ⟨C₀, hC₀, hC₀c, hC₀s⟩ := ramsey_stable hS ((filter_subset _ _).trans hS'S)
    ((le_max_left _ _).trans hδ : rr ω M ≤ Nr.card)
  -- Step 2
  let Z : V → Finset V := fun c => S'.filter (G.Adj c) \ insert r Nr
  have hZS' : ∀ c, Z c ⊆ S' := fun c => sdiff_subset.trans (filter_subset _ _)
  have hZadj : ∀ c, ∀ z ∈ Z c, G.Adj c z := fun c z hz => (mem_filter.mp (mem_sdiff.mp hz).1).2
  have hZr : ∀ c, ∀ z ∈ Z c, ¬ G.Adj r z ∧ z ≠ r := by
    intro c z hz
    have h := (mem_sdiff.mp hz)
    refine ⟨fun hrz => h.2 (mem_insert_of_mem (mem_filter.mpr ⟨h.1 |> (mem_filter.mp ·) |>.1, hrz⟩)),
      fun hzr => h.2 (hzr ▸ mem_insert_self _ _)⟩
  have hbad : (C₀.filter (fun c => (Z c).card < K)).card < T₀ := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨X, hX, hXc⟩ := exists_subset_card_eq hcon
    have hXC : X ⊆ C₀ := hX.trans (filter_subset _ _)
    let Wt := Nr.filter (fun u => ∀ x ∈ X, G.Adj x u)
    -- each x ∈ X misses at most K vertices of Nr
    have hmiss : ∀ x ∈ X, (Nr \ S'.filter (G.Adj x)).card ≤ K := by
      intro x hx
      have hxZ : (Z x).card < K := (mem_filter.mp (hX hx)).2
      have hxS' : x ∈ S' := (mem_filter.mp (hC₀ (hXC hx))).1
      have hcover : S'.filter (G.Adj x) ⊆ (Nr ∩ S'.filter (G.Adj x)) ∪ ({r} ∪ Z x) := by
        intro u hu
        by_cases hur : u = r
        · exact mem_union_right _ (mem_union_left _ (mem_singleton.mpr hur))
        · by_cases hru : G.Adj r u
          · exact mem_union_left _ (mem_inter.mpr ⟨mem_filter.mpr ⟨(mem_filter.mp hu).1, hru⟩, hu⟩)
          · refine mem_union_right _ (mem_union_right _ (mem_sdiff.mpr ⟨hu, ?_⟩))
            rintro hmem
            rcases mem_insert.mp hmem with h | h
            · exact hur h
            · exact hru (mem_filter.mp h).2
      have h1 := card_le_card hcover
      have h2 := h1.trans ((card_union_le _ _).trans (Nat.add_le_add_left (card_union_le {r} (Z x)) _))
      have h3 : (Nr ∩ S'.filter (G.Adj x)).card + (Nr \ S'.filter (G.Adj x)).card = Nr.card :=
        card_inter_add_card_sdiff _ _
      have h4 := hrmin x hxS'
      simp only [card_singleton] at h2
      omega
    have hWt : T₀ ≤ Wt.card := by
      have hsub : Nr \ Wt ⊆ X.biUnion (fun x => Nr \ S'.filter (G.Adj x)) := by
        intro u hu
        obtain ⟨huN, huW⟩ := mem_sdiff.mp hu
        have : ¬ ∀ x ∈ X, G.Adj x u := fun h => huW (mem_filter.mpr ⟨huN, h⟩)
        push_neg at this
        obtain ⟨x, hx, hxu⟩ := this
        exact mem_biUnion.mpr ⟨x, hx, mem_sdiff.mpr ⟨huN, fun h => hxu (mem_filter.mp h).2⟩⟩
      have h1 := (card_le_card hsub).trans (card_biUnion_le_card_mul _ _ _ hmiss)
      have h2 : (Nr \ Wt).card + Wt.card = Nr.card := card_sdiff_add_card_eq_card (filter_subset _ _)
      rw [hXc] at h1
      have h3 : T₀ * K + T₀ ≤ Nr.card := (le_max_right _ _).trans hδ
      omega
    obtain ⟨W₁, hW₁, hW₁c⟩ := exists_subset_card_eq hWt
    have hWN : W₁ ⊆ Nr := hW₁.trans (filter_subset _ _)
    apply hK X (hXC.trans (hC₀.trans ((filter_subset _ _).trans hS'S))) W₁
      (hWN.trans ((filter_subset _ _).trans hS'S)) ?_ hXc hW₁c
    · intro x hx u hu
      exact (mem_filter.mp (hW₁ hu)).2 x hx
    · rw [disjoint_left]
      intro x hx hxW
      exact G.irrefl ((mem_filter.mp (hW₁ hxW)).2 x hx)
  have hC₁ : m ≤ (C₀.filter (fun c => K ≤ (Z c).card)).card := by
    have := card_filter_add_card_filter_not (s := C₀) (fun c => K ≤ (Z c).card)
    have e : C₀.filter (fun c => ¬ K ≤ (Z c).card) = C₀.filter (fun c => (Z c).card < K) := by
      congr 1; ext c; simp
    rw [e] at this
    omega
  obtain ⟨C, hC, hCc⟩ := exists_subset_card_eq hC₁
  have hCC₀ : C ⊆ C₀ := hC.trans (filter_subset _ _)
  have hCK : ∀ c ∈ C, K ≤ (Z c).card := fun c hc => (mem_filter.mp (hC hc)).2
  have hCN : C ⊆ Nr := hCC₀.trans hC₀
  -- Step 3
  have hstep3 : ∀ c, ∃ Z2 : Finset V, ∃ F : Finset V, c ∈ C →
      Z2 ⊆ Z c ∧ n₂ ≤ Z2.card ∧ IsStab G Z2 ∧ F ⊆ C ∧ ∀ z ∈ Z2, C.filter (G.Adj z) = F := by
    intro c
    by_cases hc : c ∈ C
    · obtain ⟨Z1, hZ1, hZ1c, hZ1s⟩ := ramsey_stable hS ((hZS' c).trans hS'S) (hCK c hc)
      obtain ⟨F, hF, hFc⟩ := exists_le_card_fiber_of_mul_le_card_of_maps_to
        (f := fun z => C.filter (G.Adj z)) (s := Z1) (t := C.powerset) (n := n₂)
        (fun z _ => mem_powerset.mpr (filter_subset _ _)) ⟨∅, empty_mem_powerset _⟩
        (by rw [card_powerset, hCc, hZ1c])
      refine ⟨Z1.filter (fun z => C.filter (G.Adj z) = F), F, fun _ => ⟨(filter_subset _ _).trans hZ1,
        hFc, hZ1s.mono (filter_subset _ _), mem_powerset.mp hF, fun z hz => (mem_filter.mp hz).2⟩⟩
    · exact ⟨∅, ∅, fun h => absurd h hc⟩
  choose Z2 F hZF using hstep3
  have hFsmall : ∀ c ∈ C, (F c).card < T₀ := by
    intro c hc
    obtain ⟨hZ2, hZ2c, -, hFC, hlab⟩ := hZF c hc
    by_contra hcon
    push_neg at hcon
    obtain ⟨F₁, hF₁, hF₁c⟩ := exists_subset_card_eq hcon
    obtain ⟨Z₁, hZ₁, hZ₁c⟩ := exists_subset_card_eq ((le_max_right _ _).trans hZ2c : T₀ ≤ (Z2 c).card)
    have hZ₁S : Z₁ ⊆ S := (hZ₁.trans hZ2).trans ((hZS' c).trans hS'S)
    apply hK Z₁ hZ₁S F₁ (((hF₁.trans hFC).trans hCN).trans ((filter_subset _ _).trans hS'S)) ?_ hZ₁c hF₁c
    · intro z hz f hf
      have := hlab z (hZ₁ hz)
      have hfF : f ∈ F c := hF₁ hf
      rw [← this] at hfF
      exact (mem_filter.mp hfF).2
    · rw [disjoint_left]
      intro z hz hzF
      have hzN : z ∈ Nr := hCN (hFC (hF₁ hzF))
      exact (hZr c z (hZ2 (hZ₁ hz))).1 (mem_filter.mp hzN).2
  -- Step 4
  obtain ⟨I, hI, hIc, hIfree⟩ := outdeg_arcfree (fun c c' => c' ∈ F c) T₀ s C hT₀1
    (fun c hc => (card_le_card (fun c' hc' => (mem_filter.mp hc').2.2)).trans_lt (hFsmall c hc))
    (by rw [hCc])
  have hIC : I ⊆ C := hI
  have hnadj : ∀ c ∈ I, ∀ c' ∈ I, c ≠ c' → ∀ z ∈ Z2 c, ¬ G.Adj z c' := by
    intro c hc c' hc' hcc z hz hzc
    obtain ⟨-, -, -, -, hlab⟩ := hZF c (hIC hc)
    apply hIfree c hc c' hc' hcc
    rw [← hlab z hz]
    exact mem_filter.mpr ⟨hIC hc', hzc⟩
  -- Step 5
  obtain ⟨e, he, heI⟩ := exists_enum' hIc
  obtain ⟨Y, hY, hYa⟩ := hNs G S (fun i => Z2 (e i)) hK
    (fun i => ((hZF _ (hIC (heI i))).1.trans (hZS' _)).trans hS'S)
    (fun i j hij => by
      rw [disjoint_left]
      intro z hz hz'
      have hzZ : z ∈ Z (e j) := (hZF _ (hIC (heI j))).1 hz'
      exact hnadj _ (heI i) _ (heI j) (he.ne hij) z hz (hZadj _ z hzZ).symm)
    (fun i => (le_max_left _ _).trans (hZF _ (hIC (heI i))).2.1)
  -- Step 6
  apply hfree
  refine embed_HsF (univ : Finset (Fin s)) (by simp) r e Y (fun i _ => (hY i).2)
    (fun i _ => (mem_filter.mp (hCN (hIC (heI i)))).2)
    (fun i _ j _ hij => ⟨hC₀s _ (hCC₀ (hIC (heI i))) _ (hCC₀ (hIC (heI j))), he.ne hij⟩)
    (fun i _ y hy => ?_) (fun i _ => (hZF _ (hIC (heI i))).2.2.1.mono (hY i).1)
    (fun i _ j _ hij y hy hadj => hnadj _ (heI i) _ (heI j) (he.ne hij) y ((hY i).1 hy) hadj.symm)
    (fun i _ j _ hij y hy z hz => hYa i j hij y hy z hz)
  have hyZ : y ∈ Z (e i) := (hZF _ (hIC (heI i))).1 ((hY i).1 hy)
  exact ⟨hZadj _ y hyZ, (hZr _ y hyZ).1, (hZr _ y hyZ).2⟩

end GS


open Finset

namespace GS

section Defs
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def IsCore (S : Finset V) (w d : ℕ) (A : Fin d → Finset V) : Prop :=
  (∀ i, A i ⊆ S ∧ (A i).card = w ∧ IsStab G (A i)) ∧
    ∀ i j, i ≠ j → Disjoint (A i) (A j) ∧ Compl G (A i) (A j)

def VC {d : ℕ} (A : Fin d → Finset V) : Finset V := univ.biUnion A

/-- `v` is nearly complete to every part of `A`. -/
def InQ (μ : ℕ) {d : ℕ} (A : Fin d → Finset V) (v : V) : Prop :=
  ∀ p, ((A p).filter (fun a => ¬ G.Adj v a)).card < μ

def Absorbed (κ μ : ℕ) {d : ℕ} (A : Fin d → Finset V) (v : V) : Prop :=
  v ∉ VC A ∧ ¬ InQ G μ A v ∧ ∃ p, κ ≤ ((A p).filter (G.Adj v)).card

/-- The greedy template sequence, relative to `R ⊆ S`. -/
structure SeqP (S R : Finset V) (d w κ μ n : ℕ) (A : ℕ → Fin d → Finset V) (P : ℕ → Finset V) :
    Prop where
  core : ∀ i < n, IsCore G S w d (A i)
  vcP : ∀ i < n, VC (A i) ⊆ P i
  PR : ∀ i < n, P i ⊆ R
  disj : ∀ i < n, ∀ j < n, i ≠ j → Disjoint (P i) (P j)
  absorb : ∀ i < n, ∀ v ∈ P i, v ∉ VC (A i) → Absorbed G κ μ (A i) v
  noabs : ∀ i < n, ∀ j < n, i < j → ∀ v ∈ P j, ¬ Absorbed G κ μ (A i) v
  left : ¬ HasCore G (R \ (range n).biUnion P) w d

end Defs

section Lemmas
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem hasCore_iff {S : Finset V} {w d : ℕ} : HasCore G S w d ↔ ∃ A, IsCore G S w d A := Iff.rfl

theorem mem_VC {d : ℕ} {A : Fin d → Finset V} {v : V} : v ∈ VC A ↔ ∃ p, v ∈ A p := by
  simp [VC]

theorem IsCore.mono {S S' : Finset V} {w d : ℕ} {A : Fin d → Finset V} (h : IsCore G S w d A)
    (hS : S ⊆ S') : IsCore G S' w d A :=
  ⟨fun i => ⟨(h.1 i).1.trans hS, (h.1 i).2⟩, h.2⟩

theorem IsCore.VC_sub {S : Finset V} {w d : ℕ} {A : Fin d → Finset V} (h : IsCore G S w d A) :
    VC A ⊆ S := by
  intro v hv
  obtain ⟨p, hp⟩ := mem_VC.mp hv
  exact (h.1 p).1 hp

theorem IsCore.card_VC {S : Finset V} {w d : ℕ} {A : Fin d → Finset V} (h : IsCore G S w d A) :
    (VC A).card = d * w := by
  rw [VC, card_biUnion]
  · simp [(h.1 _).2.1]
  · intro i _ j _ hij
    exact (h.2 i j hij).1

theorem IsCore.adj_of_ne {S : Finset V} {w d : ℕ} {A : Fin d → Finset V} (h : IsCore G S w d A)
    {p q : Fin d} (hpq : p ≠ q) {x y : V} (hx : x ∈ A p) (hy : y ∈ A q) : G.Adj x y :=
  (h.2 p q hpq).2 x hx y hy

theorem IsCore.VC_nonempty {S : Finset V} {w d : ℕ} {A : Fin d → Finset V} (h : IsCore G S w d A)
    (hw : 1 ≤ w) (hd : 1 ≤ d) : (VC A).Nonempty := by
  rw [← card_pos, h.card_VC]; exact Nat.mul_pos hd hw

/-- Existence of the greedy template sequence (Lemma 7.2). -/
theorem greedy (S : Finset V) (d w κ μ : ℕ) (hw : 1 ≤ w) (hd : 1 ≤ d) :
    ∀ R : Finset V, R ⊆ S → ∃ n A P, SeqP G S R d w κ μ n A P := by
  classical
  intro R
  induction R using Finset.strongInduction with
  | H R ih =>
    intro hRS
    by_cases hc : HasCore G R w d
    · obtain ⟨A0, hA0'⟩ := hc
      have hA0 : IsCore G R w d A0 := hA0'
      set P0 := VC A0 ∪ R.filter (Absorbed G κ μ A0) with hP0
      have hVCR : VC A0 ⊆ R := hA0.VC_sub
      have hP0R : P0 ⊆ R := union_subset hVCR (filter_subset _ _)
      have hne : P0.Nonempty := (hA0.VC_nonempty hw hd).mono subset_union_left
      obtain ⟨n, A, P, h⟩ := ih (R \ P0) (sdiff_ssubset hP0R hne) (sdiff_subset.trans hRS)
      refine ⟨n + 1, fun i => if i = 0 then A0 else A (i - 1),
        fun i => if i = 0 then P0 else P (i - 1), ?_⟩
      have hPR : ∀ i < n, P i ⊆ R \ P0 := h.PR
      constructor
      · intro i hi
        rcases i with _ | i
        · simpa using hA0.mono hRS
        · simpa using h.core i (by omega)
      · intro i hi
        rcases i with _ | i
        · simp [P0]
        · simpa using h.vcP i (by omega)
      · intro i hi
        rcases i with _ | i
        · simpa using hP0R
        · simpa using (hPR i (by omega)).trans sdiff_subset
      · intro i hi j hj hij
        rcases i with _ | i <;> rcases j with _ | j
        · exact absurd rfl hij
        · simp only [if_true, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
          exact disjoint_of_subset_right (hPR j (by omega)) disjoint_sdiff
        · simp only [if_true, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
          exact disjoint_of_subset_left (hPR i (by omega)) sdiff_disjoint
        · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
          exact h.disj i (by omega) j (by omega) (by omega)
      · intro i hi v hv hvC
        rcases i with _ | i
        · simp only [if_true] at hv hvC ⊢
          rcases mem_union.mp hv with h1 | h1
          · exact absurd h1 hvC
          · exact (mem_filter.mp h1).2
        · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at hv hvC ⊢
          exact h.absorb i (by omega) v hv hvC
      · intro i hi j hj hij v hv
        rcases j with _ | j
        · omega
        simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at hv
        rcases i with _ | i
        · simp only [if_true]
          intro habs
          have hvR := hPR j (by omega) hv
          exact (mem_sdiff.mp hvR).2 (mem_union_right _ (mem_filter.mpr ⟨(mem_sdiff.mp hvR).1, habs⟩))
        · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
          exact h.noabs i (by omega) j (by omega) (by omega) v hv
      · have heq : R \ (range (n + 1)).biUnion (fun i => if i = 0 then P0 else P (i - 1)) =
            (R \ P0) \ (range n).biUnion P := by
          ext x
          simp only [mem_sdiff, mem_biUnion, mem_range, not_exists, not_and]
          constructor
          · rintro ⟨hxR, hx⟩
            refine ⟨⟨hxR, fun h0 => hx 0 (by omega) (by simpa using h0)⟩, fun i hi hxi => ?_⟩
            exact hx (i + 1) (by omega) (by simpa using hxi)
          · rintro ⟨⟨hxR, hx0⟩, hx⟩
            refine ⟨hxR, fun i hi hxi => ?_⟩
            rcases i with _ | i
            · exact hx0 (by simpa using hxi)
            · exact hx i (by omega) (by simpa using hxi)
        rw [heq]; exact h.left
    · refine ⟨0, fun _ _ => ∅, fun _ => ∅, ⟨fun i hi => absurd hi (Nat.not_lt_zero _),
        fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => absurd hi (Nat.not_lt_zero _),
        fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => absurd hi (Nat.not_lt_zero _),
        fun i hi => absurd hi (Nat.not_lt_zero _), by simpa using hc⟩⟩

open scoped Classical in
/-- Lemma 7.1: few vertices are nearly complete to a core. -/
theorem card_Q_lt {S : Finset V} {ω t w d μ : ℕ} (hS : Small G S ω)
    (hcore : ¬ HasCore G S t (d + 1)) {A : Fin d → Finset V} (hA : IsCore G S w d A)
    (htw : t * μ ≤ w) (hμ : 1 ≤ μ) :
    (S.filter (fun v => v ∉ VC A ∧ InQ G μ A v)).card < rr ω t := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨T', hT', hT'c, hT's⟩ := ramsey_stable hS (filter_subset _ _) hcon
  have hgood : ∀ p, ∃ B ⊆ A p, B.card = t ∧ ∀ a ∈ B, ∀ x ∈ T', G.Adj x a := by
    intro p
    set Bad := (A p).filter (fun a => ∃ x ∈ T', ¬ G.Adj x a)
    have hBad : Bad ⊆ T'.biUnion (fun x => (A p).filter (fun a => ¬ G.Adj x a)) := by
      intro a ha
      obtain ⟨haA, x, hx, hxa⟩ := mem_filter.mp ha
      exact mem_biUnion.mpr ⟨x, hx, mem_filter.mpr ⟨haA, hxa⟩⟩
    have hle : Bad.card ≤ t * (μ - 1) := by
      refine (card_le_card hBad).trans ((card_biUnion_le_card_mul _ _ _ fun x hx => ?_).trans
        (by rw [hT'c]))
      have := (mem_filter.mp (hT' hx)).2.2 p
      omega
    have hcard : t ≤ (A p \ Bad).card := by
      have h2 : (A p \ Bad).card + Bad.card = w := by
        rw [card_sdiff_add_card_eq_card (filter_subset _ _), (hA.1 p).2.1]
      have : t * (μ - 1) + t ≤ w := by
        have e : t * (μ - 1) + t = t * μ := by
          rw [Nat.mul_sub_one]; have := Nat.le_mul_of_pos_right t hμ; omega
        omega
      omega
    obtain ⟨B, hB, hBc⟩ := exists_subset_card_eq hcard
    refine ⟨B, hB.trans sdiff_subset, hBc, fun a ha x hx => ?_⟩
    by_contra hxa
    exact (mem_sdiff.mp (hB ha)).2 (mem_filter.mpr ⟨(mem_sdiff.mp (hB ha)).1, x, hx, hxa⟩)
  choose B hB hBc hBadj using hgood
  have hT'VC : ∀ x ∈ T', x ∉ VC A := fun x hx => (mem_filter.mp (hT' hx)).2.1
  apply hcore
  refine ⟨Fin.lastCases T' B, ?_, ?_⟩
  · intro i
    induction i using Fin.lastCases with
    | last => simp only [Fin.lastCases_last]; exact ⟨hT'.trans (filter_subset _ _), hT'c, hT's⟩
    | cast p =>
      simp only [Fin.lastCases_castSucc]
      exact ⟨(hB p).trans (hA.1 p).1, hBc p, (hA.1 p).2.2.mono (hB p)⟩
  · intro i j hij
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact absurd rfl hij
      | cast q =>
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
        refine ⟨?_, fun x hx a ha => hBadj q a ha x hx⟩
        rw [disjoint_left]
        intro x hx hxB
        exact hT'VC x hx (mem_VC.mpr ⟨q, hB q hxB⟩)
    | cast p =>
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
        refine ⟨?_, fun a ha x hx => (hBadj p a ha x hx).symm⟩
        rw [disjoint_left]
        intro x hxB hx
        exact hT'VC x hx (mem_VC.mpr ⟨p, hB p hxB⟩)
      | cast q =>
        simp only [Fin.lastCases_castSucc]
        have hpq : p ≠ q := fun h => hij (by rw [h])
        exact ⟨Disjoint.mono (hB p) (hB q) (hA.2 p q hpq).1,
          (hA.2 p q hpq).2.mono (hB p) (hB q)⟩

/-- Counting indices whose (disjoint) sets meet `X`. -/
theorem card_hits {ι : Type*} [DecidableEq ι] (J : Finset ι) (P : ι → Finset V) (X : Finset V)
    (hdisj : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (P i) (P j)) :
    (J.filter (fun j => (P j ∩ X).Nonempty)).card ≤ X.card := by
  set J' := J.filter (fun j => (P j ∩ X).Nonempty)
  have h1 : (J'.biUnion (fun j => P j ∩ X)).card = ∑ j ∈ J', (P j ∩ X).card := by
    apply card_biUnion
    intro i hi j hj hij
    exact Disjoint.mono inter_subset_left inter_subset_left
      (hdisj i (mem_filter.mp hi).1 j (mem_filter.mp hj).1 hij)
  have h2 : J'.card ≤ ∑ j ∈ J', (P j ∩ X).card := by
    rw [card_eq_sum_ones]
    exact sum_le_sum fun j hj => card_pos.mpr (mem_filter.mp hj).2
  have h3 : (J'.biUnion (fun j => P j ∩ X)).card ≤ X.card :=
    card_le_card (biUnion_subset.mpr fun j _ => inter_subset_right)
  omega

/-- Partition step (F2 + T4c). -/
theorem col_partition (J : Finset ℕ) (P : ℕ → Finset V) (A : ℕ → ℕ → Prop) [DecidableRel A]
    (D k : ℕ) (hout : ∀ i ∈ J, (J.filter (fun j => j ≠ i ∧ A i j)).card < D)
    (hcol : ∀ J' ⊆ J, (∀ i ∈ J', ∀ j ∈ J', i ≠ j → ¬ A i j) → col G (J'.biUnion P) k) :
    col G (J.biUnion P) ((2 * D - 1) * k) := by
  obtain ⟨c, hc, hp⟩ := outdeg_col A D J hout
  have hsub : J.biUnion P ⊆ (range (2 * D - 1)).biUnion
      (fun m => (J.filter (fun j => c j = m)).biUnion P) := by
    intro v hv
    obtain ⟨j, hj, hvj⟩ := mem_biUnion.mp hv
    exact mem_biUnion.mpr ⟨c j, mem_range.mpr (hc j hj),
      mem_biUnion.mpr ⟨j, mem_filter.mpr ⟨hj, rfl⟩, hvj⟩⟩
  refine (col_biUnion _ _ k fun m _ => hcol _ (filter_subset _ _) ?_).mono hsub
    (by rw [card_range])
  intro i hi j hj hij hA
  exact hp i (mem_filter.mp hi).1 j (mem_filter.mp hj).1 ⟨hij, hA⟩
    ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm)

/-- Sequential choice of pairwise anticomplete objects. -/
theorem seq_choice {β : Type*} (vs : β → Finset V) (Good : ℕ → β → Prop) : ∀ m : ℕ,
    (∀ k < m, ∀ prev : Fin k → β, (∀ k' : Fin k, Good k' (prev k')) →
      ∃ o, Good k o ∧ ∀ k' : Fin k, Anti G (vs o) (vs (prev k'))) →
    ∃ os : Fin m → β, (∀ k : Fin m, Good k (os k)) ∧
      ∀ k k' : Fin m, k ≠ k' → Anti G (vs (os k)) (vs (os k')) := by
  intro m
  induction m with
  | zero => intro _; exact ⟨fun k => k.elim0, fun k => k.elim0, fun k => k.elim0⟩
  | succ m ih =>
    intro hstep
    obtain ⟨os, hgood, hanti⟩ := ih (fun k hk prev hprev => hstep k (by omega) prev hprev)
    obtain ⟨o, hgo, hao⟩ := hstep m (by omega) os hgood
    refine ⟨Fin.lastCases o os, ?_, ?_⟩
    · intro k
      induction k using Fin.lastCases with
      | last => simpa using hgo
      | cast k => simpa using hgood k
    · intro k k' hkk
      induction k using Fin.lastCases with
      | last =>
        induction k' using Fin.lastCases with
        | last => exact absurd rfl hkk
        | cast k' => simpa using hao k'
      | cast k =>
        induction k' using Fin.lastCases with
        | last => simpa using (hao k).symm
        | cast k' =>
          simp only [Fin.lastCases_castSucc]
          exact hanti k k' (fun h => hkk (by rw [h]))

end Lemmas

end GS


open Finset

namespace GS

section Nice
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def Nice1 (μ : ℕ) {d : ℕ} (A : ℕ → Fin d → Finset V) (P : ℕ → Finset V) (J : Finset ℕ) : Prop :=
  ∀ i ∈ J, ∀ v ∈ J.biUnion P, v ∉ VC (A i) → ¬ InQ G μ (A i) v

end Nice

section Lemmas
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {S : Finset V} {d w κ μ n : ℕ} {A : ℕ → Fin d → Finset V} {P : ℕ → Finset V}

theorem Nice1.mono {J J' : Finset ℕ} (h : Nice1 G μ A P J) (hJ : J' ⊆ J) : Nice1 G μ A P J' :=
  fun i hi v hv hvC => h i (hJ hi) v (biUnion_subset_biUnion_of_subset_left _ hJ hv) hvC

theorem SeqP.notin_VC (hseq : SeqP G S S d w κ μ n A P) {i j : ℕ} (hi : i < n) (hj : j < n)
    (hij : i ≠ j) {v : V} (hv : v ∈ P j) : v ∉ VC (A i) := fun h =>
  disjoint_left.mp (hseq.disj i hi j hj hij) (hseq.vcP i hi h) hv

/-- 7.4(a). -/
theorem nice1_nonnbrs {J : Finset ℕ} (h1 : Nice1 G μ A P J) {i : ℕ} (hi : i ∈ J) {v : V}
    (hv : v ∈ J.biUnion P) (hvC : v ∉ VC (A i)) :
    ∃ p, μ ≤ ((A i p).filter (fun a => ¬ G.Adj v a)).card := by
  have := h1 i hi v hv hvC
  simp only [InQ, not_forall, not_lt] at this
  exact this

/-- 7.4(b): vertices of later templates have few neighbours in every part of an earlier core. -/
theorem nice1_later (hseq : SeqP G S S d w κ μ n A P) {J : Finset ℕ} (hJ : J ⊆ range n)
    (h1 : Nice1 G μ A P J) {i j : ℕ} (hi : i ∈ J) (hj : j ∈ J) (hij : i < j) {v : V}
    (hv : v ∈ P j) (p : Fin d) : ((A i p).filter (G.Adj v)).card < κ := by
  have hin := mem_range.mp (hJ hi)
  have hjn := mem_range.mp (hJ hj)
  by_contra hcon
  push_neg at hcon
  have hvC := hseq.notin_VC hin hjn hij.ne hv
  exact hseq.noabs i hin j hjn hij v hv
    ⟨hvC, h1 i hi v (mem_biUnion.mpr ⟨j, hj, hv⟩) hvC, p, hcon⟩

/-- Two different parts, one with many neighbours of `v` and one with many non-neighbours. -/
theorem two_parts {S : Finset V} {B : Fin d → Finset V} (hB : IsCore G S w d B) (hd : 2 ≤ d)
    {κ₂ μ : ℕ} (hw : κ₂ + μ ≤ w) {v : V}
    (hp : ∃ p, κ₂ ≤ ((B p).filter (G.Adj v)).card)
    (hq : ∃ q, μ ≤ ((B q).filter (fun a => ¬ G.Adj v a)).card) :
    ∃ α β, α ≠ β ∧ κ₂ ≤ ((B α).filter (G.Adj v)).card ∧
      μ ≤ ((B β).filter (fun a => ¬ G.Adj v a)).card := by
  obtain ⟨p, hp⟩ := hp
  obtain ⟨q, hq⟩ := hq
  by_cases hpq : p = q
  · subst hpq
    obtain ⟨p', hp'⟩ : ∃ p' : Fin d, p' ≠ p := by
      by_cases h0 : p = ⟨0, by omega⟩
      · exact ⟨⟨1, by omega⟩, by rw [h0]; simp [Fin.ext_iff]⟩
      · exact ⟨⟨0, by omega⟩, fun h => h0 h.symm⟩
    by_cases hk : κ₂ ≤ ((B p').filter (G.Adj v)).card
    · exact ⟨p', p, hp', hk, hq⟩
    · refine ⟨p, p', hp'.symm, hp, ?_⟩
      have := card_filter_add_card_filter_not (s := B p') (G.Adj v)
      rw [(hB.1 p').2.1] at this
      omega
  · exact ⟨p, q, hpq, hp, hq⟩

/-- The decreasing enumeration of a finite set of naturals. -/
theorem exists_anti_enum {I : Finset ℕ} {s : ℕ} (h : I.card = s) :
    ∃ e : Fin s → ℕ, (∀ k, e k ∈ I) ∧ ∀ k k', k < k' → e k' < e k := by
  refine ⟨fun k => I.orderEmbOfFin h k.rev, fun k => orderEmbOfFin_mem _ _ _, ?_⟩
  intro k k' hkk
  apply (I.orderEmbOfFin h).strictMono
  rw [Fin.rev_lt_rev]; exact hkk

/-- Killing bound: a forbidden set whose members have `< κ` neighbours in `X` kills few of `X`. -/
theorem card_kill (F X : Finset V) {κ : ℕ} (h : ∀ x ∈ F, (X.filter (G.Adj x)).card < κ) :
    (F.biUnion (fun x => X.filter (G.Adj x))).card ≤ F.card * (κ - 1) :=
  card_biUnion_le_card_mul _ _ _ fun x hx => by have := h x hx; omega

/-- 7.5: every 1-nice family is 2-nice. -/
theorem nice1_two (s : ℕ) (hfree : ¬ (Hs s).IsIndContained G) (hseq : SeqP G S S d w κ μ n A P)
    {J : Finset ℕ} (hJ : J ⊆ range n) (h1 : Nice1 G μ A P J) (hd : 2 ≤ d) {κ₂ : ℕ}
    (hκ₂ : (s * s - 1) * (κ - 1) + 1 ≤ κ₂) (hμ : (s * s - 1) * (κ - 1) + s ≤ μ)
    (hw : κ₂ + μ ≤ w) {v : V} (hv : v ∈ J.biUnion P) :
    (J.filter (fun i => v ∉ VC (A i) ∧ ∃ p, κ₂ ≤ ((A i p).filter (G.Adj v)).card)).card < s := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨I, hI, hIc⟩ := exists_subset_card_eq hcon
  obtain ⟨e, heI, hanti⟩ := exists_anti_enum hIc
  have heJ : ∀ k, e k ∈ J := fun k => (mem_filter.mp (hI (heI k))).1
  have hen : ∀ k, e k < n := fun k => mem_range.mp (hJ (heJ k))
  have heinj : Function.Injective e := by
    intro k k' h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hl | hl
    · exact absurd h (hanti k k' hl).ne'
    · exact absurd h (hanti k' k hl).ne
  have hvC : ∀ k, v ∉ VC (A (e k)) := fun k => (mem_filter.mp (hI (heI k))).2.1
  have hparts : ∀ k, ∃ α β, α ≠ β ∧ κ₂ ≤ ((A (e k) α).filter (G.Adj v)).card ∧
      μ ≤ ((A (e k) β).filter (fun a => ¬ G.Adj v a)).card := fun k =>
    two_parts (hseq.core _ (hen k)) hd hw (mem_filter.mp (hI (heI k))).2.2
      (nice1_nonnbrs h1 (heJ k) hv (hvC k))
  choose α β hαβ hα hβ using hparts
  -- sequential choice
  let Good : ℕ → V × Finset V → Prop := fun k o => ∀ hk : k < s,
    o.1 ∈ (A (e ⟨k, hk⟩) (α ⟨k, hk⟩)).filter (G.Adj v) ∧
    o.2 ⊆ (A (e ⟨k, hk⟩) (β ⟨k, hk⟩)).filter (fun a => ¬ G.Adj v a) ∧ o.2.card = s
  have hvsP : ∀ (k : Fin s) (o : V × Finset V), Good k o → insert o.1 o.2 ⊆ P (e k) := by
    intro k o ho
    obtain ⟨ha, hY, -⟩ := ho k.2
    refine insert_subset ((hseq.vcP _ (hen k)) (mem_VC.mpr ⟨_, (mem_filter.mp ha).1⟩)) ?_
    intro y hy
    exact (hseq.vcP _ (hen k)) (mem_VC.mpr ⟨_, (mem_filter.mp (hY hy)).1⟩)
  obtain ⟨os, hgood, hosanti⟩ := seq_choice (G := G) (fun o : V × Finset V => insert o.1 o.2)
    Good s (by
      intro k hk prev hprev
      set kk : Fin s := ⟨k, hk⟩
      set Fb := univ.biUnion (fun k' : Fin k => insert (prev k').1 (prev k').2)
      have hFb : Fb.card ≤ (s * s - 1) := by
        refine (card_biUnion_le).trans ?_
        have : ∀ k' : Fin k, (insert (prev k').1 (prev k').2).card ≤ s + 1 := fun k' =>
          (card_insert_le _ _).trans (by rw [(hprev k' (by omega)).2.2])
        refine (sum_le_sum fun k' _ => this k').trans ?_
        simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
        have : k * (s + 1) ≤ (s - 1) * (s + 1) := Nat.mul_le_mul_right _ (by omega)
        refine this.trans (le_of_eq ?_)
        obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
        rw [Nat.add_sub_cancel]
        exact (Nat.sub_eq_of_eq_add (by ring)).symm
      have hkill : ∀ x ∈ Fb, ∀ p, ((A (e kk) p).filter (G.Adj x)).card < κ := by
        intro x hx p
        obtain ⟨k', -, hxk⟩ := mem_biUnion.mp hx
        have hk'k : (⟨k', by omega⟩ : Fin s) < kk := by
          show (k' : ℕ) < k; exact k'.2
        have hxP := hvsP ⟨k', by omega⟩ (prev k') (hprev k') hxk
        exact nice1_later hseq hJ h1 (heJ kk) (heJ _) (hanti _ _ hk'k) hxP p
      -- choose a
      set Ca := (A (e kk) (α kk)).filter (G.Adj v)
      set KA := Fb.biUnion (fun x => Ca.filter (G.Adj x))
      have hKA : KA.card ≤ (s * s - 1) * (κ - 1) :=
        (card_kill Fb Ca fun x hx => (card_le_card (filter_subset_filter _ (filter_subset _ _))).trans_lt
          (hkill x hx _)).trans (Nat.mul_le_mul_right _ hFb)
      have hCa : (s * s - 1) * (κ - 1) + 1 ≤ Ca.card := hκ₂.trans (hα kk)
      obtain ⟨a, ha⟩ : (Ca \ KA).Nonempty := by
        rw [← card_pos]
        have := le_card_sdiff KA Ca
        omega
      set CY := (A (e kk) (β kk)).filter (fun a => ¬ G.Adj v a)
      set KY := Fb.biUnion (fun x => CY.filter (G.Adj x))
      have hKY : KY.card ≤ (s * s - 1) * (κ - 1) :=
        (card_kill Fb CY fun x hx => (card_le_card (filter_subset_filter _ (filter_subset _ _))).trans_lt
          (hkill x hx _)).trans (Nat.mul_le_mul_right _ hFb)
      have hCY : s ≤ (CY \ KY).card := by
        have h1 := le_card_sdiff KY CY
        have h2 : (s * s - 1) * (κ - 1) + s ≤ CY.card := hμ.trans (hβ kk)
        omega
      obtain ⟨Y, hY, hYc⟩ := exists_subset_card_eq hCY
      refine ⟨(a, Y), fun _ => ⟨(mem_sdiff.mp ha).1, hY.trans sdiff_subset, hYc⟩, ?_⟩
      intro k' z hz x hx hzx
      have hxF : x ∈ Fb := mem_biUnion.mpr ⟨k', mem_univ _, hx⟩
      rcases mem_insert.mp hz with hz | hz
      · subst hz
        exact (mem_sdiff.mp ha).2 (mem_biUnion.mpr ⟨x, hxF, mem_filter.mpr ⟨(mem_sdiff.mp ha).1, hzx.symm⟩⟩)
      · have hzY := hY hz
        exact (mem_sdiff.mp hzY).2 (mem_biUnion.mpr ⟨x, hxF, mem_filter.mpr ⟨(mem_sdiff.mp hzY).1, hzx.symm⟩⟩))
  have hg : ∀ k : Fin s, (os k).1 ∈ (A (e k) (α k)).filter (G.Adj v) ∧
      (os k).2 ⊆ (A (e k) (β k)).filter (fun a => ¬ G.Adj v a) ∧ (os k).2.card = s :=
    fun k => hgood k k.2
  apply hfree
  refine embed_HsF (univ : Finset (Fin s)) (by simp) v (fun k => (os k).1) (fun k => (os k).2)
    (fun k _ => (hg k).2.2) (fun k _ => (mem_filter.mp (hg k).1).2) ?_ ?_ ?_ ?_ ?_
  · intro k _ k' _ hkk
    refine ⟨hosanti k k' hkk _ (mem_insert_self _ _) _ (mem_insert_self _ _), fun h => ?_⟩
    have h1 := hvsP k (os k) (hgood k) (mem_insert_self _ _)
    have h2 := hvsP k' (os k') (hgood k') (mem_insert_self _ _)
    rw [h] at h1
    exact disjoint_left.mp (hseq.disj _ (hen k) _ (hen k') (heinj.ne hkk)) h1 h2
  · intro k _ y hy
    have hyB := hg k
    have hy' := mem_filter.mp (hyB.2.1 hy)
    refine ⟨(hseq.core _ (hen k)).adj_of_ne (hαβ k) (mem_filter.mp hyB.1).1 hy'.1, hy'.2, ?_⟩
    intro hyv
    exact hvC k (hyv ▸ mem_VC.mpr ⟨_, hy'.1⟩)
  · intro k _
    exact ((hseq.core _ (hen k)).1 _).2.2.mono ((hg k).2.1.trans (filter_subset _ _))
  · intro k _ k' _ hkk y hy hadj
    exact hosanti k k' hkk y (mem_insert_of_mem hy) _ (mem_insert_self _ _) hadj.symm
  · intro k _ k' _ hkk y hy z hz
    exact hosanti k k' hkk y (mem_insert_of_mem hy) z (mem_insert_of_mem hz)

end Lemmas

section Nice35
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def Nice3 (μ κ₂ : ℕ) {d : ℕ} (A : ℕ → Fin d → Finset V) (P : ℕ → Finset V) (J : Finset ℕ) : Prop :=
  Nice1 G μ A P J ∧ ∀ i ∈ J, ∀ j ∈ J, i ≠ j → ∀ x ∈ VC (A i), ∀ p,
    ((A j p).filter (G.Adj x)).card < κ₂

def Nice5 (μ κ₂ : ℕ) {d : ℕ} (A : ℕ → Fin d → Finset V) (P : ℕ → Finset V) (J : Finset ℕ) : Prop :=
  Nice3 G μ κ₂ A P J ∧ ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Anti G (VC (A i)) (VC (A j))

end Nice35

section Lemmas2
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {S : Finset V} {d w κ μ n : ℕ} {A : ℕ → Fin d → Finset V} {P : ℕ → Finset V}

theorem Nice3.mono {κ₂ : ℕ} {J J' : Finset ℕ} (h : Nice3 G μ κ₂ A P J) (hJ : J' ⊆ J) :
    Nice3 G μ κ₂ A P J' :=
  ⟨h.1.mono hJ, fun i hi j hj hij => h.2 i (hJ hi) j (hJ hj) hij⟩

theorem Nice5.mono {κ₂ : ℕ} {J J' : Finset ℕ} (h : Nice5 G μ κ₂ A P J) (hJ : J' ⊆ J) :
    Nice5 G μ κ₂ A P J' :=
  ⟨h.1.mono hJ, fun i hi j hj hij => h.2 i (hJ hi) j (hJ hj) hij⟩

/-- Extract `m` indices on which an injective vertex choice is stable (Ramsey). -/
theorem stable_indices {ω m : ℕ} (hS : Small G S ω) (I : Finset ℕ) (a : ℕ → V)
    (hinj : Set.InjOn a I) (haS : ∀ i ∈ I, a i ∈ S) (hI : rr ω m ≤ I.card) :
    ∃ I' ⊆ I, I'.card = m ∧ ∀ i ∈ I', ∀ j ∈ I', ¬ G.Adj (a i) (a j) := by
  obtain ⟨T, hT, hTc, hTs⟩ := ramsey_stable hS (image_subset_iff.mpr haS)
    (by rw [card_image_of_injOn hinj]; exact hI)
  refine ⟨I.filter (fun i => a i ∈ T), filter_subset _ _, ?_, fun i hi j hj =>
    hTs _ (mem_filter.mp hi).2 _ (mem_filter.mp hj).2⟩
  rw [← hTc, ← card_image_of_injOn (hinj.mono (filter_subset _ _ : I.filter _ ⊆ I))]
  congr 1
  ext x
  simp only [mem_image, mem_filter]
  constructor
  · rintro ⟨i, ⟨_, hi⟩, rfl⟩; exact hi
  · intro hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp (hT hx)
    exact ⟨i, ⟨hi, hx⟩, rfl⟩

/-- 7.7: every 3-nice family is 4-nice. -/
theorem nice3_four (s ω : ℕ) (hs : 1 ≤ s) (hfree : ¬ (Hs s).IsIndContained G) (hS : Small G S ω)
    (hseq : SeqP G S S d w κ μ n A P)
    {J : Finset ℕ} (hJ : J ⊆ range n) {κ₂ : ℕ} (h3 : Nice3 G μ κ₂ A P J) (hd : 2 ≤ d)
    (hκ₂ : (s * s - 1) * (κ - 1) + 1 ≤ κ₂) (hμ : (s * s - 1) * (κ - 1) + s ≤ μ)
    (hw : κ₂ + μ ≤ w) (hw7 : κ₂ + s * κ₂ + s * s * κ + s ≤ w) {v : V} (hv : v ∈ J.biUnion P) :
    (J.filter (fun i => v ∉ P i ∧ ∃ x ∈ VC (A i), G.Adj v x)).card < rr ω s + s - 1 := by
  by_contra hcon
  push_neg at hcon
  set I₀ := J.filter (fun i => v ∉ P i ∧ ∃ x ∈ VC (A i), G.Adj v x)
  set Ib := J.filter (fun i => v ∉ VC (A i) ∧ ∃ p, κ₂ ≤ ((A i p).filter (G.Adj v)).card)
  have hIb := nice1_two s hfree hseq hJ h3.1 hd hκ₂ hμ hw hv
  set I₁ := I₀ \ Ib
  have hI₁ : rr ω s ≤ I₁.card := by
    have h1 : I₀.card - Ib.card ≤ I₁.card := le_card_sdiff Ib I₀
    have h2 : Ib.card < s := hIb
    have h3 : rr ω s + s - 1 ≤ I₀.card := hcon
    omega
  have hI₁J : I₁ ⊆ J := sdiff_subset.trans (filter_subset _ _)
  have hn : ∀ i ∈ I₁, i < n := fun i hi => mem_range.mp (hJ (hI₁J hi))
  have hvP : ∀ i ∈ I₁, v ∉ P i := fun i hi => (mem_filter.mp (mem_sdiff.mp hi).1).2.1
  have hvVC : ∀ i ∈ I₁, v ∉ VC (A i) := fun i hi h => hvP i hi (hseq.vcP i (hn i hi) h)
  have hfew : ∀ i ∈ I₁, ∀ p, ((A i p).filter (G.Adj v)).card < κ₂ := by
    intro i hi p
    by_contra hc
    push_neg at hc
    exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨hI₁J hi, hvVC i hi, p, hc⟩)
  have hex : ∀ i, ∃ x, i ∈ I₁ → x ∈ VC (A i) ∧ G.Adj v x := by
    intro i
    by_cases hi : i ∈ I₁
    · obtain ⟨x, hx, hvx⟩ := (mem_filter.mp (mem_sdiff.mp hi).1).2.2
      exact ⟨x, fun _ => ⟨hx, hvx⟩⟩
    · exact ⟨v, fun h => absurd h hi⟩
  choose a ha using hex
  have haP : ∀ i ∈ I₁, a i ∈ P i := fun i hi => hseq.vcP i (hn i hi) (ha i hi).1
  have hainj : Set.InjOn a I₁ := by
    intro i hi j hj hij
    by_contra hne
    exact disjoint_left.mp (hseq.disj i (hn i hi) j (hn j hj) hne) (haP i hi) (hij ▸ haP j hj)
  obtain ⟨I₂, hI₂, hI₂c, hI₂s⟩ := stable_indices hS I₁ a hainj
    (fun i hi => (hseq.PR i (hn i hi)) (haP i hi)) hI₁
  obtain ⟨e, heI, hanti⟩ := exists_anti_enum hI₂c
  have he1 : ∀ k, e k ∈ I₁ := fun k => hI₂ (heI k)
  have heJ : ∀ k, e k ∈ J := fun k => hI₁J (he1 k)
  have hen : ∀ k, e k < n := fun k => hn _ (he1 k)
  have heinj : Function.Injective e := by
    intro k k' h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hl | hl
    · exact absurd h (hanti k k' hl).ne'
    · exact absurd h (hanti k' k hl).ne
  -- the part containing a and another part
  have hpart : ∀ k, ∃ q, a (e k) ∉ A (e k) q ∧ ∀ y ∈ A (e k) q, G.Adj (a (e k)) y := by
    intro k
    obtain ⟨p, hp⟩ := mem_VC.mp (ha _ (he1 k)).1
    obtain ⟨q, hq⟩ : ∃ q : Fin d, q ≠ p := by
      by_cases h0 : p = ⟨0, by omega⟩
      · exact ⟨⟨1, by omega⟩, by rw [h0]; simp [Fin.ext_iff]⟩
      · exact ⟨⟨0, by omega⟩, fun h => h0 h.symm⟩
    refine ⟨q, fun h => disjoint_left.mp ((hseq.core _ (hen k)).2 p q hq.symm).1 hp h,
      fun y hy => (hseq.core _ (hen k)).adj_of_ne hq.symm hp hy⟩
  choose q hq hqadj using hpart
  let Cand : Fin s → Finset V := fun k => ((A (e k) (q k)).filter (fun y => ¬ G.Adj v y)) \
    (univ.filter (fun j : Fin s => j ≠ k)).biUnion (fun j => (A (e k) (q k)).filter (G.Adj (a (e j))))
  let Good : ℕ → Finset V → Prop := fun k Y => ∀ hk : k < s, Y ⊆ Cand ⟨k, hk⟩ ∧ Y.card = s
  obtain ⟨Ys, hgood, hYanti⟩ := seq_choice (G := G) id Good s (by
    intro k hk prev hprev
    set kk : Fin s := ⟨k, hk⟩
    set Fb := univ.biUnion prev
    have hFb : Fb.card ≤ s * s := by
      refine card_biUnion_le.trans ?_
      refine (sum_le_sum fun k' _ => (hprev k' (by omega)).2.le).trans ?_
      simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (by omega)
    have hkill : ∀ x ∈ Fb, ((A (e kk) (q kk)).filter (G.Adj x)).card < κ := by
      intro x hx
      obtain ⟨k', -, hxk⟩ := mem_biUnion.mp hx
      have hk'k : (⟨k', by omega⟩ : Fin s) < kk := by show (k' : ℕ) < k; exact k'.2
      have hxC := ((hprev k' (by omega)).1 hxk)
      have hxA : x ∈ A (e ⟨k', by omega⟩) (q ⟨k', by omega⟩) :=
        (mem_filter.mp (mem_sdiff.mp hxC).1).1
      have hxP : x ∈ P (e ⟨k', by omega⟩) :=
        hseq.vcP _ (hen _) (mem_VC.mpr ⟨_, hxA⟩)
      exact nice1_later hseq hJ h3.1 (heJ kk) (heJ _) (hanti _ _ hk'k) hxP _
    set B := A (e kk) (q kk)
    set Kv := B.filter (G.Adj v)
    set Ka := (univ.filter (fun j : Fin s => j ≠ kk)).biUnion (fun j => B.filter (G.Adj (a (e j))))
    set Kp := Fb.biUnion (fun x => B.filter (G.Adj x))
    have hKv : Kv.card ≤ κ₂ := (hfew _ (he1 kk) _).le
    have hKa : Ka.card ≤ s * κ₂ := by
      refine (card_biUnion_le_card_mul _ _ κ₂ fun j hj => ?_).trans ?_
      · exact (h3.2 _ (heJ j) _ (heJ kk) (heinj.ne (mem_filter.mp hj).2) _ (ha _ (he1 j)).1 _).le
      · exact Nat.mul_le_mul_right _ ((card_le_univ _).trans (by simp))
    have hKp : Kp.card ≤ s * s * κ :=
      (card_biUnion_le_card_mul _ _ _ fun x hx => (hkill x hx).le).trans (Nat.mul_le_mul_right _ hFb)
    have hBc : B.card = w := ((hseq.core _ (hen kk)).1 _).2.1
    have hsub : B \ (Kv ∪ Ka ∪ Kp) ⊆ Cand kk \ Kp := by
      intro y hy
      simp only [mem_sdiff, mem_union, not_or] at hy
      refine mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨mem_filter.mpr ⟨hy.1, fun h => hy.2.1.1 (mem_filter.mpr ⟨hy.1, h⟩)⟩,
        hy.2.1.2⟩, hy.2.2⟩
    have hcard : s ≤ (Cand kk \ Kp).card := by
      have h1 := le_card_sdiff (Kv ∪ Ka ∪ Kp) B
      have h2 := card_le_card hsub
      have h3 : (Kv ∪ Ka ∪ Kp).card ≤ κ₂ + s * κ₂ + s * s * κ :=
        (card_union_le _ _).trans (add_le_add ((card_union_le _ _).trans (add_le_add hKv hKa)) hKp)
      have h5 : (B \ (Kv ∪ Ka ∪ Kp)).card ≤ (Cand kk \ Kp).card := h2
      have h6 : B.card - (Kv ∪ Ka ∪ Kp).card ≤ (B \ (Kv ∪ Ka ∪ Kp)).card := h1
      rw [hBc] at h6
      omega
    obtain ⟨Y, hY, hYc⟩ := exists_subset_card_eq hcard
    refine ⟨Y, fun _ => ⟨hY.trans sdiff_subset, hYc⟩, fun k' y hy x hx hyx => ?_⟩
    have hxF : x ∈ Fb := mem_biUnion.mpr ⟨k', mem_univ _, hx⟩
    have hyB : y ∈ B := (mem_filter.mp (mem_sdiff.mp (mem_sdiff.mp (hY hy)).1).1).1
    exact (mem_sdiff.mp (hY hy)).2 (mem_biUnion.mpr ⟨x, hxF, mem_filter.mpr ⟨hyB, hyx.symm⟩⟩))
  have hg : ∀ k : Fin s, Ys k ⊆ Cand k ∧ (Ys k).card = s := fun k => hgood k k.2
  apply hfree
  refine embed_HsF (univ : Finset (Fin s)) (by simp) v (fun k => a (e k)) Ys
    (fun k _ => (hg k).2) (fun k _ => (ha _ (he1 k)).2) ?_ ?_ ?_ ?_ ?_
  · intro k _ k' _ hkk
    exact ⟨hI₂s _ (heI k) _ (heI k'), fun h => heinj.ne hkk (hainj (he1 k) (he1 k') h)⟩
  · intro k _ y hy
    have hyC := (hg k).1 hy
    have hyA := mem_filter.mp (mem_sdiff.mp hyC).1
    refine ⟨hqadj k y hyA.1, hyA.2, fun hyv => ?_⟩
    exact hvP _ (he1 k) (hyv ▸ hseq.vcP _ (hen k) (mem_VC.mpr ⟨_, hyA.1⟩))
  · intro k _
    exact ((hseq.core _ (hen k)).1 _).2.2.mono
      (((hg k).1.trans sdiff_subset).trans (filter_subset _ _))
  · intro k _ k' _ hkk y hy hadj
    have hyC := (hg k).1 hy
    exact (mem_sdiff.mp hyC).2 (mem_biUnion.mpr ⟨k', mem_filter.mpr ⟨mem_univ _, Ne.symm hkk⟩,
      mem_filter.mpr ⟨(mem_filter.mp (mem_sdiff.mp hyC).1).1, hadj⟩⟩)
  · intro k _ k' _ hkk y hy z hz
    exact hYanti k k' hkk y hy z hz

end Lemmas2

end GS


open Finset

namespace GS

section Lemmas3
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {S : Finset V} {d w κ μ n : ℕ} {A : ℕ → Fin d → Finset V} {P : ℕ → Finset V}

/-- 7.9: every 5-nice family is 6-nice. -/
theorem nice5_six (s ω : ℕ) (hs : 1 ≤ s) (hfree : ¬ (Hs s).IsIndContained G) (hS : Small G S ω)
    (hseq : SeqP G S S d w κ μ n A P)
    {J : Finset ℕ} (hJ : J ⊆ range n) {κ₂ : ℕ} (h5 : Nice5 G μ κ₂ A P J) (hd : 2 ≤ d)
    (hκ₂ : (s * s - 1) * (κ - 1) + 1 ≤ κ₂) (hμ : (s * s - 1) * (κ - 1) + s ≤ μ)
    (hw : κ₂ + μ ≤ w) (hw7 : κ₂ + s * κ₂ + s * s * κ + s ≤ w) (hκs : s ≤ κ)
    {v : V} (hv : v ∈ J.biUnion P) :
    (J.filter (fun i => v ∉ P i ∧ ∃ x ∈ P i, G.Adj v x)).card <
      (rr ω s + s - 1) + (2 * (rr ω s + s - 1) - 1) * rr ω s := by
  set ρ' := rr ω s + s - 1
  have hρ' : 1 ≤ ρ' := by have : 1 ≤ rr ω s := Nat.one_le_two_pow; omega
  have hfour := fun {u : V} (hu : u ∈ J.biUnion P) =>
    nice3_four s ω hs hfree hS hseq hJ h5.1 hd hκ₂ hμ hw hw7 hu
  by_contra hcon
  push_neg at hcon
  set I₀ := J.filter (fun i => v ∉ P i ∧ ∃ x ∈ P i, G.Adj v x)
  set It := J.filter (fun i => v ∉ P i ∧ ∃ x ∈ VC (A i), G.Adj v x)
  have hIt : It.card < ρ' := hfour hv
  set I₁ := I₀ \ It
  have hI₁ : (2 * ρ' - 1) * rr ω s ≤ I₁.card := by
    have h1 : I₀.card - It.card ≤ I₁.card := le_card_sdiff It I₀
    have h3 : ρ' + (2 * ρ' - 1) * rr ω s ≤ I₀.card := hcon
    omega
  have hI₁J : I₁ ⊆ J := sdiff_subset.trans (filter_subset _ _)
  have hn : ∀ i ∈ I₁, i < n := fun i hi => mem_range.mp (hJ (hI₁J hi))
  have hvP : ∀ i ∈ I₁, v ∉ P i := fun i hi => (mem_filter.mp (mem_sdiff.mp hi).1).2.1
  have hvanti : ∀ i ∈ I₁, ∀ x ∈ VC (A i), ¬ G.Adj v x := fun i hi x hx hvx =>
    (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨hI₁J hi, hvP i hi, x, hx, hvx⟩)
  have hex : ∀ i, ∃ x, i ∈ I₁ → x ∈ P i ∧ G.Adj v x := by
    intro i
    by_cases hi : i ∈ I₁
    · obtain ⟨x, hx, hvx⟩ := (mem_filter.mp (mem_sdiff.mp hi).1).2.2
      exact ⟨x, fun _ => ⟨hx, hvx⟩⟩
    · exact ⟨v, fun h => absurd h hi⟩
  choose a ha using hex
  have haVC : ∀ i ∈ I₁, a i ∉ VC (A i) := fun i hi h => hvanti i hi _ h (ha i hi).2
  have haJ : ∀ i ∈ I₁, a i ∈ J.biUnion P := fun i hi => mem_biUnion.mpr ⟨i, hI₁J hi, (ha i hi).1⟩
  have hainj : Set.InjOn a I₁ := by
    intro i hi j hj hij
    by_contra hne
    exact disjoint_left.mp (hseq.disj i (hn i hi) j (hn j hj) hne) (ha i hi).1 (hij ▸ (ha j hj).1)
  -- arcs
  obtain ⟨I₂, hI₂, hI₂c, hI₂free⟩ := outdeg_arcfree (fun i j => ∃ x ∈ VC (A j), G.Adj (a i) x)
    ρ' (rr ω s) I₁ hρ' (by
      intro i hi
      refine lt_of_le_of_lt (card_le_card ?_) (hfour (haJ i hi))
      intro j hj
      obtain ⟨hjI, hji, x, hx, hax⟩ := mem_filter.mp hj
      refine mem_filter.mpr ⟨hI₁J hjI, fun h => ?_, x, hx, hax⟩
      exact disjoint_left.mp (hseq.disj i (hn i hi) j (hn j hjI) (Ne.symm hji)) (ha i hi).1 h) hI₁
  obtain ⟨I₃, hI₃, hI₃c, hI₃s⟩ := stable_indices hS I₂ a (hainj.mono hI₂)
    (fun i hi => hseq.PR i (hn i (hI₂ hi)) (ha i (hI₂ hi)).1) (by rw [hI₂c])
  have hI₃₁ : I₃ ⊆ I₁ := hI₃.trans hI₂
  have hY : ∀ i, ∃ Y : Finset V, i ∈ I₃ → ∃ p, Y ⊆ (A i p).filter (G.Adj (a i)) ∧ Y.card = s := by
    intro i
    by_cases hi : i ∈ I₃
    · obtain ⟨-, -, p, hp⟩ := hseq.absorb i (hn i (hI₃₁ hi)) (a i) (ha i (hI₃₁ hi)).1 (haVC i (hI₃₁ hi))
      obtain ⟨Y, hY, hYc⟩ := exists_subset_card_eq (hκs.trans hp)
      exact ⟨Y, fun _ => ⟨p, hY, hYc⟩⟩
    · exact ⟨∅, fun h => absurd h hi⟩
  choose Y hYp using hY
  have hYVC : ∀ i ∈ I₃, Y i ⊆ VC (A i) := by
    intro i hi y hy
    obtain ⟨p, hsub, -⟩ := hYp i hi
    exact mem_VC.mpr ⟨p, (mem_filter.mp (hsub hy)).1⟩
  apply hfree
  refine embed_HsF I₃ hI₃c v a Y (fun i hi => (hYp i hi).choose_spec.2)
    (fun i hi => (ha i (hI₃₁ hi)).2) ?_ ?_ ?_ ?_ ?_
  · intro i hi j hj hij
    exact ⟨hI₃s i hi j hj, fun h => hij (hainj (hI₃₁ hi) (hI₃₁ hj) h)⟩
  · intro i hi y hy
    obtain ⟨p, hsub, -⟩ := hYp i hi
    refine ⟨(mem_filter.mp (hsub hy)).2, hvanti i (hI₃₁ hi) y (hYVC i hi hy), fun hyv => ?_⟩
    exact hvP i (hI₃₁ hi) (hyv ▸ hseq.vcP i (hn i (hI₃₁ hi)) (hYVC i hi hy))
  · intro i hi
    obtain ⟨p, hsub, -⟩ := hYp i hi
    exact ((hseq.core i (hn i (hI₃₁ hi))).1 p).2.2.mono (hsub.trans (filter_subset _ _))
  · intro i hi j hj hij y hy hadj
    exact hI₂free j (hI₃ hj) i (hI₃ hi) (Ne.symm hij) ⟨y, hYVC i hi hy, hadj⟩
  · intro i hi j hj hij y hy z hz
    exact h5.2 i (hI₁J (hI₃₁ hi)) j (hI₁J (hI₃₁ hj)) hij y (hYVC i hi hy) z (hYVC j hj hz)

/-- 7.10: every 5-nice (hence 6-nice) family is 7-nice. -/
theorem nice5_seven (s ω : ℕ) (hs : 1 ≤ s) (hfree : ¬ (Hs s).IsIndContained G) (hS : Small G S ω)
    (hseq : SeqP G S S d w κ μ n A P)
    {J : Finset ℕ} (hJ : J ⊆ range n) {κ₂ : ℕ} (h5 : Nice5 G μ κ₂ A P J) (hd : 2 ≤ d)
    (hκ₂ : (s * s - 1) * (κ - 1) + 1 ≤ κ₂) (hμ : (s * s - 1) * (κ - 1) + s ≤ μ)
    (hw : κ₂ + μ ≤ w) (hw7 : κ₂ + s * κ₂ + s * s * κ + s ≤ w) (hκs : s ≤ κ)
    (lam : ℕ) (hlam : lam = (rr ω s + s - 1) + (2 * (rr ω s + s - 1) - 1) * rr ω s)
    {h : ℕ} (hh : h ∈ J) :
    (J.filter (fun i => i ≠ h ∧ ∃ v ∈ P h, rr ω s ≤ ((P i).filter (G.Adj v)).card)).card <
      (2 * lam - 1) * (d * w + d * w * ((2 * s * lam - 1) * rr ω s + lam)) := by
  set ρs := rr ω s
  set σ := (2 * s * lam - 1) * ρs
  have hρs : 1 ≤ ρs := Nat.one_le_two_pow
  have hlam1 : 1 ≤ lam := by rw [hlam]; have : 1 ≤ rr ω s := Nat.one_le_two_pow; omega
  have hsix := fun {u : V} (hu : u ∈ J.biUnion P) =>
    nice5_six s ω hs hfree hS hseq hJ h5 hd hκ₂ hμ hw hw7 hκs hu
  rw [← hlam] at hsix
  have hhn : h < n := mem_range.mp (hJ hh)
  have hcoreh := hseq.core h hhn
  by_contra hcon
  push_neg at hcon
  set I₁ := J.filter (fun i => i ≠ h ∧ ∃ v ∈ P h, ρs ≤ ((P i).filter (G.Adj v)).card)
  have hI₁J : I₁ ⊆ J := filter_subset _ _
  have hn : ∀ i ∈ I₁, i < n := fun i hi => mem_range.mp (hJ (hI₁J hi))
  have hih : ∀ i ∈ I₁, i ≠ h := fun i hi => (mem_filter.mp hi).2.1
  have hVCne : (VC (A h)).Nonempty := hcoreh.VC_nonempty (by omega) (by omega)
  obtain ⟨x0, -⟩ := id hVCne
  have hex : ∀ i, ∃ x, i ∈ I₁ → x ∈ P h ∧ ρs ≤ ((P i).filter (G.Adj x)).card := by
    intro i
    by_cases hi : i ∈ I₁
    · obtain ⟨x, hx, hc⟩ := (mem_filter.mp hi).2.2
      exact ⟨x, fun _ => ⟨hx, hc⟩⟩
    · exact ⟨x0, fun h' => absurd h' hi⟩
  choose a ha using hex
  have haJ : ∀ i ∈ I₁, a i ∈ J.biUnion P := fun i hi => mem_biUnion.mpr ⟨h, hh, (ha i hi).1⟩
  have haPi : ∀ i ∈ I₁, a i ∉ P i := fun i hi hP =>
    disjoint_left.mp (hseq.disj h hhn i (hn i hi) (hih i hi).symm) (ha i hi).1 hP
  -- Step 1
  obtain ⟨I₂, hI₂, hI₂c, hI₂free⟩ := outdeg_arcfree (fun i j => ∃ x ∈ P j, G.Adj (a i) x)
    lam (d * w + d * w * (σ + lam)) I₁ hlam1 (by
      intro i hi
      refine lt_of_le_of_lt (card_le_card ?_) (hsix (haJ i hi))
      intro j hj
      obtain ⟨hjI, -, x, hx, hax⟩ := mem_filter.mp hj
      exact mem_filter.mpr ⟨hI₁J hjI, haPi j hjI |> fun _ => fun hP =>
        disjoint_left.mp (hseq.disj h hhn j (hn j hjI) (hih j hjI).symm) (ha i hi).1 hP, x, hx, hax⟩)
      hcon
  have hI₂₁ : I₂ ⊆ I₁ := hI₂
  have hainj : Set.InjOn a I₂ := by
    intro i hi j hj hij
    by_contra hne
    have hpos : 0 < ((P j).filter (G.Adj (a j))).card := lt_of_lt_of_le hρs (ha j (hI₂₁ hj)).2
    obtain ⟨x, hx⟩ := card_pos.mp hpos
    exact hI₂free i hi j hj hne ⟨x, (mem_filter.mp hx).1, hij ▸ (mem_filter.mp hx).2⟩
  -- Step 2
  set I₃ := I₂.filter (fun i => a i ∉ VC (A h))
  have hI₃ : d * w * (σ + lam) ≤ I₃.card := by
    have hsplit := card_filter_add_card_filter_not (s := I₂) (fun i => a i ∉ VC (A h))
    have hbad : (I₂.filter (fun i => ¬ a i ∉ VC (A h))).card ≤ d * w := by
      rw [← hcoreh.card_VC]
      refine card_le_card_of_injOn a (fun i hi => ?_) (hainj.mono (filter_subset _ _))
      exact not_not.mp (mem_filter.mp hi).2
    have : I₃.card + (I₂.filter (fun i => ¬ a i ∉ VC (A h))).card = I₂.card := hsplit
    omega
  have hI₃₂ : I₃ ⊆ I₂ := filter_subset _ _
  have hcex : ∀ i, ∃ c, i ∈ I₃ → c ∈ VC (A h) ∧ G.Adj (a i) c := by
    intro i
    by_cases hi : i ∈ I₃
    · have hi2 := hI₃₂ hi
      obtain ⟨-, -, p, hp⟩ := hseq.absorb h hhn (a i) (ha i (hI₂₁ hi2)).1 (mem_filter.mp hi).2
      obtain ⟨c, hc⟩ := card_pos.mp (lt_of_lt_of_le (by omega : 0 < κ) hp)
      exact ⟨c, fun _ => ⟨mem_VC.mpr ⟨p, (mem_filter.mp hc).1⟩, (mem_filter.mp hc).2⟩⟩
    · exact ⟨a i, fun h' => absurd h' hi⟩
  choose cc hcc using hcex
  -- Step 3
  obtain ⟨c, hcVC, hfib⟩ := exists_le_card_fiber_of_mul_le_card_of_maps_to
    (f := cc) (s := I₃) (t := VC (A h)) (n := σ + lam) (fun i hi => (hcc i hi).1) hVCne
    (by rw [hcoreh.card_VC]; exact hI₃)
  set I₄ := I₃.filter (fun i => cc i = c)
  have hI₄₃ : I₄ ⊆ I₃ := filter_subset _ _
  have hI₄c : ∀ i ∈ I₄, G.Adj (a i) c := fun i hi =>
    (mem_filter.mp hi).2 ▸ (hcc i (hI₄₃ hi)).2
  -- Step 4
  have hcP : c ∈ P h := hseq.vcP h hhn hcVC
  set Ic := J.filter (fun i => c ∉ P i ∧ ∃ x ∈ P i, G.Adj c x)
  have hIc : Ic.card < lam := hsix (mem_biUnion.mpr ⟨h, hh, hcP⟩)
  set I₅ := I₄ \ Ic
  have hI₅ : σ ≤ I₅.card := by
    have h1 : I₄.card - Ic.card ≤ I₅.card := le_card_sdiff Ic I₄
    have h2 : σ + lam ≤ I₄.card := hfib
    omega
  have hI₅₁ : I₅ ⊆ I₁ := ((sdiff_subset.trans hI₄₃).trans hI₃₂).trans hI₂₁
  have hcanti : ∀ i ∈ I₅, ∀ x ∈ P i, ¬ G.Adj c x := by
    intro i hi x hx hcx
    have hcPi : c ∉ P i := fun hP =>
      disjoint_left.mp (hseq.disj h hhn i (hn i (hI₅₁ hi)) (hih i (hI₅₁ hi)).symm) hcP hP
    exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨hI₁J (hI₅₁ hi), hcPi, x, hx, hcx⟩)
  -- Step 5
  have hYex : ∀ i, ∃ Y : Finset V, i ∈ I₅ → Y ⊆ (P i).filter (G.Adj (a i)) ∧ Y.card = s ∧
      IsStab G Y := by
    intro i
    by_cases hi : i ∈ I₅
    · obtain ⟨Y, hY, hYc, hYs⟩ := ramsey_stable hS
        ((filter_subset _ _).trans (hseq.PR i (hn i (hI₅₁ hi)))) (ha i (hI₅₁ hi)).2
      exact ⟨Y, fun _ => ⟨hY, hYc, hYs⟩⟩
    · exact ⟨∅, fun h' => absurd h' hi⟩
  choose Y hY using hYex
  have hYP : ∀ i ∈ I₅, Y i ⊆ P i := fun i hi => (hY i hi).1.trans (filter_subset _ _)
  obtain ⟨I₆, hI₆, hI₆c, hI₆free⟩ := outdeg_arcfree
    (fun i j => ∃ y ∈ Y i, ∃ x ∈ P j, G.Adj y x) (s * lam) ρs I₅ (Nat.mul_pos hs hlam1) (by
      intro i hi
      have hsub : I₅.filter (fun j => j ≠ i ∧ ∃ y ∈ Y i, ∃ x ∈ P j, G.Adj y x) ⊆
          (Y i).biUnion (fun y => J.filter (fun j => y ∉ P j ∧ ∃ x ∈ P j, G.Adj y x)) := by
        intro j hj
        obtain ⟨hjI, hji, y, hy, x, hx, hyx⟩ := mem_filter.mp hj
        refine mem_biUnion.mpr ⟨y, hy, mem_filter.mpr ⟨hI₁J (hI₅₁ hjI), fun hP => ?_, x, hx, hyx⟩⟩
        exact disjoint_left.mp (hseq.disj i (hn i (hI₅₁ hi)) j (hn j (hI₅₁ hjI)) (Ne.symm hji))
          (hYP i hi hy) hP
      refine lt_of_le_of_lt ((card_le_card hsub).trans (card_biUnion_le_card_mul _ _ (lam - 1)
        fun y hy => ?_)) ?_
      · have := hsix (mem_biUnion.mpr ⟨i, hI₁J (hI₅₁ hi), hYP i hi hy⟩); omega
      · rw [(hY i hi).2.1]
        calc s * (lam - 1) < s * lam := Nat.mul_lt_mul_of_pos_left (by omega) hs
          _ = s * lam := rfl) (by show (2 * (s * lam) - 1) * ρs ≤ I₅.card; rw [← mul_assoc]; exact hI₅)
  have hI₆₅ : I₆ ⊆ I₅ := hI₆
  -- Step 6
  obtain ⟨I₇, hI₇, hI₇c, hI₇s⟩ := stable_indices hS I₆ a
    (hainj.mono (((hI₆₅.trans sdiff_subset).trans hI₄₃).trans hI₃₂))
    (fun i hi => hseq.PR h hhn (ha i (hI₅₁ (hI₆₅ hi))).1) (by rw [hI₆c])
  have hI₇₅ : I₇ ⊆ I₅ := hI₇.trans hI₆₅
  have hI₇₂ : I₇ ⊆ I₂ := ((hI₇₅.trans sdiff_subset).trans hI₄₃).trans hI₃₂
  apply hfree
  refine embed_HsF I₇ hI₇c c a Y (fun i hi => (hY i (hI₇₅ hi)).2.1)
    (fun i hi => (hI₄c i ((sdiff_subset) (hI₇₅ hi))).symm) ?_ ?_ ?_ ?_ ?_
  · intro i hi j hj hij
    exact ⟨hI₇s i hi j hj, fun h' => hij (hainj (hI₇₂ hi) (hI₇₂ hj) h')⟩
  · intro i hi y hy
    have hyP := hYP i (hI₇₅ hi) hy
    refine ⟨(mem_filter.mp ((hY i (hI₇₅ hi)).1 hy)).2, hcanti i (hI₇₅ hi) y hyP, fun hyc => ?_⟩
    exact disjoint_left.mp (hseq.disj h hhn i (hn i (hI₅₁ (hI₇₅ hi))) (hih i (hI₅₁ (hI₇₅ hi))).symm)
      hcP (hyc ▸ hyP)
  · intro i hi
    exact (hY i (hI₇₅ hi)).2.2
  · intro i hi j hj hij y hy hadj
    exact hI₂free j (hI₇₂ hj) i (hI₇₂ hi) (Ne.symm hij) ⟨y, hYP i (hI₇₅ hi) hy, hadj⟩
  · intro i hi j hj hij y hy z hz hyz
    exact hI₆free i (hI₇ hi) j (hI₇ hj) hij ⟨y, hy, z, hYP j (hI₇₅ hj) hz, hyz⟩

/-- (F1) each template is colourable from neighbourhood colourings. -/
theorem template_col (hseq : SeqP G S S d w κ μ n A P) (hκ : 1 ≤ κ) {ℓ : ℕ}
    (hOIH : ∀ x ∈ S, col G (nb G x ∩ S) ℓ) {i : ℕ} (hi : i < n) :
    col G (P i) (d * w * (ℓ + 1)) := by
  rw [← (hseq.core i hi).card_VC]
  refine col_nbhds hOIH (hseq.core i hi).VC_sub (hseq.PR i hi) fun v hv => ?_
  by_cases hvC : v ∈ VC (A i)
  · exact Or.inl hvC
  · obtain ⟨-, -, p, hp⟩ := hseq.absorb i hi v hv hvC
    obtain ⟨x, hx⟩ := card_pos.mp (lt_of_lt_of_le hκ hp)
    exact Or.inr ⟨x, mem_VC.mpr ⟨p, (mem_filter.mp hx).1⟩, ((mem_filter.mp hx).2).symm⟩

/-- 7.12: blocks of bounded outside degree. -/
theorem nice8_col (J : Finset ℕ) (hdisj : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (P i) (P j))
    {c₀ L : ℕ} (hcol : ∀ i ∈ J, col G (P i) c₀)
    (hdeg : ∀ i ∈ J, ∀ v ∈ P i, ((J.biUnion P \ P i).filter (G.Adj v)).card < L) :
    col G (J.biUnion P) (c₀ * L) := by
  classical
  let same : V → V → Prop := fun u v => ∃ i ∈ J, u ∈ P i ∧ v ∈ P i
  have hidx : ∀ v, ∃ i, v ∈ J.biUnion P → i ∈ J ∧ v ∈ P i := by
    intro v
    by_cases hv : v ∈ J.biUnion P
    · obtain ⟨i, hi, hvi⟩ := mem_biUnion.mp hv
      exact ⟨i, fun _ => ⟨hi, hvi⟩⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose idx hidx using hidx
  have huniq : ∀ i ∈ J, ∀ v ∈ P i, idx v = i := by
    intro i hi v hv
    have hvU : v ∈ J.biUnion P := mem_biUnion.mpr ⟨i, hi, hv⟩
    by_contra hne
    exact disjoint_left.mp (hdisj _ (hidx v hvU).1 i hi hne) (hidx v hvU).2 hv
  have hc : ∀ i, ∃ c : V → ℕ, i ∈ J → (∀ x ∈ P i, c x < c₀) ∧
      ∀ x ∈ P i, ∀ y ∈ P i, G.Adj x y → c x ≠ c y := by
    intro i
    by_cases hi : i ∈ J
    · obtain ⟨c, h1, h2⟩ := hcol i hi
      exact ⟨c, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ => 0, fun h => absurd h hi⟩
  choose cs hcs using hc
  refine col_prod same ⟨fun v => cs (idx v) v, ?_, ?_⟩ ?_
  · intro v hv
    exact (hcs _ (hidx v hv).1).1 v (hidx v hv).2
  · rintro u hu v hv ⟨huv, i, hi, hui, hvi⟩
    simp only
    rw [huniq i hi u hui, huniq i hi v hvi]
    exact (hcs i hi).2 u hui v hvi huv
  · refine col_of_deg_lt _ (fun x h => G.irrefl h.1)
      (fun x y h => ⟨h.1.symm, fun ⟨i, hi, h1, h2⟩ => h.2 ⟨i, hi, h2, h1⟩⟩) L _ ?_
    intro v hv
    obtain ⟨hi, hvi⟩ := hidx v hv
    refine lt_of_le_of_lt (card_le_card ?_) (hdeg _ hi v hvi)
    intro y hy
    obtain ⟨hyU, hadj, hns⟩ := mem_filter.mp hy
    exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨hyU, fun hyP => hns ⟨idx v, hi, hvi, hyP⟩⟩, hadj⟩

/-- The partition chain 7.3–7.12. -/
theorem chain (s ω ℓ t : ℕ) (hs : 1 ≤ s) (hfree : ¬ (Hs s).IsIndContained G) (hS : Small G S ω)
    (hOIH : ∀ x ∈ S, col G (nb G x ∩ S) ℓ) (hcore : ¬ HasCore G S t (d + 1))
    (hseq : SeqP G S S d w κ μ n A P) (hd : 2 ≤ d) {κ₂ : ℕ}
    (hκ₂ : (s * s - 1) * (κ - 1) + 1 ≤ κ₂) (hμ : (s * s - 1) * (κ - 1) + s ≤ μ)
    (hw : κ₂ + μ ≤ w) (hw7 : κ₂ + s * κ₂ + s * s * κ + s ≤ w) (hκs : s ≤ κ)
    (htw : t * μ ≤ w) (hμ1 : 1 ≤ μ) {g₀ : ℕ} (hleft : col G (S \ (range n).biUnion P) g₀) :
    let ρs := rr ω s
    let ρ' := ρs + s - 1
    let lam := ρ' + (2 * ρ' - 1) * ρs
    let k₈ := d * w * (ℓ + 1) * (lam * ρs)
    let k₇ := (2 * ((2 * lam - 1) * (d * w + d * w * ((2 * s * lam - 1) * ρs + lam))) - 1) * k₈
    let k₄ := (2 * (d * w * ρ') - 1) * k₇
    let k₂ := (2 * (d * w * (s - 1) + 1) - 1) * k₄
    col G S (g₀ + (2 * rr ω t - 1) * k₂) := by
  classical
  intro ρs ρ' lam k₈ k₇ k₄ k₂
  have hρs : 1 ≤ ρs := Nat.one_le_two_pow
  have hρ' : 1 ≤ ρ' := by omega
  have hlam : 1 ≤ lam := by omega
  have hw1 : 1 ≤ w := by omega
  have hdw : 1 ≤ d * w := Nat.mul_pos (by omega) hw1
  have hdisj : ∀ J ⊆ range n, ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (P i) (P j) :=
    fun J hJ i hi j hj hij => hseq.disj i (mem_range.mp (hJ hi)) j (mem_range.mp (hJ hj)) hij
  -- 7.11 + 7.12
  have L711 : ∀ J ⊆ range n, Nice5 G μ κ₂ A P J → col G (J.biUnion P) k₇ := by
    intro J hJ h5
    refine col_partition J P (fun i j => ∃ v ∈ P i, ρs ≤ ((P j).filter (G.Adj v)).card) _ k₈
      (fun i hi => nice5_seven s ω hs hfree hS hseq hJ h5 hd hκ₂ hμ hw hw7 hκs lam rfl hi) ?_
    intro J' hJ' hfree'
    have h5' := h5.mono hJ'
    have hJ'n := hJ'.trans hJ
    refine nice8_col J' (hdisj J' hJ'n)
      (fun i hi => template_col hseq (by omega) hOIH (mem_range.mp (hJ'n hi))) ?_
    intro i hi v hv
    have hvU : v ∈ J'.biUnion P := mem_biUnion.mpr ⟨i, hi, hv⟩
    set Jv := J'.filter (fun j => v ∉ P j ∧ ∃ x ∈ P j, G.Adj v x)
    have hJv : Jv.card < lam := nice5_six s ω hs hfree hS hseq hJ'n h5' hd hκ₂ hμ hw hw7 hκs hvU
    have hsub : (J'.biUnion P \ P i).filter (G.Adj v) ⊆ Jv.biUnion (fun j => (P j).filter (G.Adj v)) := by
      intro y hy
      obtain ⟨hyU, hvy⟩ := mem_filter.mp hy
      obtain ⟨j, hj, hyj⟩ := mem_biUnion.mp (mem_sdiff.mp hyU).1
      have hji : j ≠ i := fun h => (mem_sdiff.mp hyU).2 (h ▸ hyj)
      refine mem_biUnion.mpr ⟨j, mem_filter.mpr ⟨hj, fun hvj => ?_, y, hyj, hvy⟩, mem_filter.mpr ⟨hyj, hvy⟩⟩
      exact disjoint_left.mp (hdisj J' hJ'n i hi j hj hji.symm) hv hvj
    have hbound : ∀ j ∈ Jv, ((P j).filter (G.Adj v)).card ≤ ρs - 1 := by
      intro j hj
      obtain ⟨hjJ, hvj, -⟩ := mem_filter.mp hj
      have hji : i ≠ j := fun h => hvj (h ▸ hv)
      have := hfree' i hi j hjJ hji
      push_neg at this
      have := this v hv
      omega
    calc ((J'.biUnion P \ P i).filter (G.Adj v)).card
        ≤ Jv.card * (ρs - 1) := (card_le_card hsub).trans (card_biUnion_le_card_mul _ _ _ hbound)
      _ ≤ Jv.card * ρs := Nat.mul_le_mul_left _ (by omega)
      _ < lam * ρs := Nat.mul_lt_mul_of_pos_right hJv (by omega)
  -- 7.8
  have L78 : ∀ J ⊆ range n, Nice3 G μ κ₂ A P J → col G (J.biUnion P) k₄ := by
    intro J hJ h3
    refine col_partition J P (fun i j => ∃ x ∈ VC (A i), ∃ y ∈ VC (A j), G.Adj x y) (d * w * ρ') k₇
      ?_ ?_
    · intro i hi
      have hin := mem_range.mp (hJ hi)
      have hsub : J.filter (fun j => j ≠ i ∧ ∃ x ∈ VC (A i), ∃ y ∈ VC (A j), G.Adj x y) ⊆
          (VC (A i)).biUnion (fun x => J.filter (fun j => x ∉ P j ∧ ∃ y ∈ VC (A j), G.Adj x y)) := by
        intro j hj
        obtain ⟨hjJ, hji, x, hx, y, hy, hxy⟩ := mem_filter.mp hj
        refine mem_biUnion.mpr ⟨x, hx, mem_filter.mpr ⟨hjJ, fun hxj => ?_, y, hy, hxy⟩⟩
        exact disjoint_left.mp (hseq.disj i hin j (mem_range.mp (hJ hjJ)) (Ne.symm hji))
          (hseq.vcP i hin hx) hxj
      refine lt_of_le_of_lt ((card_le_card hsub).trans (card_biUnion_le_card_mul _ _ (ρ' - 1)
        fun x hx => ?_)) ?_
      · have := nice3_four s ω hs hfree hS hseq hJ h3 hd hκ₂ hμ hw hw7
          (mem_biUnion.mpr ⟨i, hi, hseq.vcP i hin hx⟩)
        omega
      · rw [(hseq.core i hin).card_VC]
        exact Nat.mul_lt_mul_of_pos_left (by omega) hdw
    · intro J' hJ' hfree'
      exact L711 J' (hJ'.trans hJ) ⟨h3.mono hJ', fun i hi j hj hij x hx y hy hxy =>
        hfree' i hi j hj hij ⟨x, hx, y, hy, hxy⟩⟩
  -- 7.6
  have L76 : ∀ J ⊆ range n, Nice1 G μ A P J → col G (J.biUnion P) k₂ := by
    intro J hJ h1
    refine col_partition J P (fun i j => ∃ x ∈ VC (A i), ∃ p, κ₂ ≤ ((A j p).filter (G.Adj x)).card)
      (d * w * (s - 1) + 1) k₄ ?_ ?_
    · intro i hi
      have hin := mem_range.mp (hJ hi)
      have hsub : J.filter (fun j => j ≠ i ∧ ∃ x ∈ VC (A i), ∃ p, κ₂ ≤ ((A j p).filter (G.Adj x)).card) ⊆
          (VC (A i)).biUnion (fun x => J.filter (fun j => x ∉ VC (A j) ∧
            ∃ p, κ₂ ≤ ((A j p).filter (G.Adj x)).card)) := by
        intro j hj
        obtain ⟨hjJ, hji, x, hx, p, hp⟩ := mem_filter.mp hj
        exact mem_biUnion.mpr ⟨x, hx, mem_filter.mpr ⟨hjJ,
          hseq.notin_VC (mem_range.mp (hJ hjJ)) hin hji (hseq.vcP i hin hx), p, hp⟩⟩
      refine lt_of_le_of_lt ((card_le_card hsub).trans (card_biUnion_le_card_mul _ _ (s - 1)
        fun x hx => ?_)) ?_
      · have := nice1_two s hfree hseq hJ h1 hd hκ₂ hμ hw
          (mem_biUnion.mpr ⟨i, hi, hseq.vcP i hin hx⟩)
        omega
      · rw [(hseq.core i hin).card_VC]; omega
    · intro J' hJ' hfree'
      refine L78 J' (hJ'.trans hJ) ⟨h1.mono hJ', fun i hi j hj hij x hx p => ?_⟩
      by_contra hc
      push_neg at hc
      exact hfree' i hi j hj hij ⟨x, hx, p, hc⟩
  -- 7.3
  have Lall : col G ((range n).biUnion P) ((2 * rr ω t - 1) * k₂) := by
    refine col_partition (range n) P
      (fun i j => (P j ∩ S.filter (fun v => v ∉ VC (A i) ∧ InQ G μ (A i) v)).Nonempty) _ k₂ ?_ ?_
    · intro i hi
      have hin := mem_range.mp hi
      refine lt_of_le_of_lt ?_ (card_Q_lt hS hcore (hseq.core i hin) htw hμ1)
      refine (card_le_card ?_).trans (card_hits (range n) P _
        (fun i hi j hj hij => hseq.disj i (mem_range.mp hi) j (mem_range.mp hj) hij))
      intro j hj
      exact mem_filter.mpr ⟨(mem_filter.mp hj).1, (mem_filter.mp hj).2.2⟩
    · intro J' hJ' hfree'
      refine L76 J' hJ' fun i hi v hv hvC hQ => ?_
      obtain ⟨j, hj, hvj⟩ := mem_biUnion.mp hv
      have hjn := mem_range.mp (hJ' hj)
      by_cases hji : j = i
      · subst hji
        exact (hseq.absorb j hjn v hvj hvC).2.1 hQ
      · exact hfree' i hi j hj (Ne.symm hji)
          ⟨v, mem_inter.mpr ⟨hvj, mem_filter.mpr ⟨hseq.PR j hjn hvj, hvC, hQ⟩⟩⟩
  have hsub : S ⊆ (S \ (range n).biUnion P) ∪ (range n).biUnion P := by
    intro v hv
    by_cases h : v ∈ (range n).biUnion P
    · exact mem_union_right _ h
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hv, h⟩)
  exact (col_union hleft Lall).mono hsub le_rfl

end Lemmas3

theorem consts (s t : ℕ) (hs : 2 ≤ s) (ht : 1 ≤ t) :
    (s * s - 1) * (s - 1) + 1 ≤ s * s * s ∧ (s * s - 1) * (s - 1) + s ≤ s * s * s * s * s ∧
    s * s * s + s * s * s * s * s ≤ (t + 1) * (s * s * s * s * s) ∧
    s * s * s + s * (s * s * s) + s * s * s + s ≤ (t + 1) * (s * s * s * s * s) ∧
    t * (s * s * s * s * s) ≤ (t + 1) * (s * s * s * s * s) ∧ 1 ≤ s * s * s * s * s := by
  obtain ⟨u, rfl⟩ : ∃ u, s = u + 2 := ⟨s - 2, by omega⟩
  have e1 : (u + 2) * (u + 2) - 1 = u * u + 4 * u + 3 := Nat.sub_eq_of_eq_add (by ring)
  have e2 : u + 2 - 1 = u + 1 := by omega
  rw [e1, e2]
  have hX : 2 * ((u + 2) * (u + 2) * (u + 2) * (u + 2) * (u + 2)) ≤
      (t + 1) * ((u + 2) * (u + 2) * (u + 2) * (u + 2) * (u + 2)) := Nat.mul_le_mul_right _ (by omega)
  refine ⟨?_, ?_, ?_, ?_, Nat.mul_le_mul_right _ (by omega), Nat.succ_le_of_lt (by positivity)⟩
  · calc _ ≤ (u * u + 4 * u + 3) * (u + 1) + 1 + (u * u + 5 * u + 4) := Nat.le_add_right _ _
      _ = _ := by ring
  · calc _ ≤ (u * u + 4 * u + 3) * (u + 1) + (u + 2) +
          (u ^ 5 + 10 * u ^ 4 + 39 * u ^ 3 + 75 * u ^ 2 + 72 * u + 27) := Nat.le_add_right _ _
      _ = _ := by ring
  · have h1 : (u + 2) * (u + 2) * (u + 2) ≤ (u + 2) * (u + 2) * (u + 2) * (u + 2) :=
      Nat.le_mul_of_pos_right _ (by omega)
    have h2 : (u + 2) * (u + 2) * (u + 2) * (u + 2) ≤ (u + 2) * (u + 2) * (u + 2) * (u + 2) * (u + 2) :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega
  · calc _ ≤ (u + 2) * (u + 2) * (u + 2) + (u + 2) * ((u + 2) * (u + 2) * (u + 2)) +
          (u + 2) * (u + 2) * (u + 2) + (u + 2) +
          (2 * u ^ 5 + 19 * u ^ 4 + 70 * u ^ 3 + 124 * u ^ 2 + 103 * u + 30) := Nat.le_add_right _ _
      _ = 2 * ((u + 2) * (u + 2) * (u + 2) * (u + 2) * (u + 2)) := by ring
      _ ≤ _ := hX

/-- The template step S(d) ⇒ S(d+1). -/
theorem step_S (s ω ℓ d : ℕ) (hs : 2 ≤ s) (hd : 2 ≤ d) (gd : ℕ → ℕ)
    (hgd : ∀ t, 1 ≤ t → ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], ¬ (Hs s).IsIndContained G → ∀ S : Finset V, Small G S ω →
      (∀ x ∈ S, col G (nb G x ∩ S) ℓ) → ¬ HasCore G S t d → col G S (gd t)) :
    ∀ t, 1 ≤ t → ∃ g : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], ¬ (Hs s).IsIndContained G → ∀ S : Finset V, Small G S ω →
      (∀ x ∈ S, col G (nb G x ∩ S) ℓ) → ¬ HasCore G S t (d + 1) → col G S g := by
  intro t ht
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := consts s t hs ht
  refine ⟨?_, ?_⟩
  rotate_left
  · intro V _ _ G _ hfree S hS hOIH hcore
    have hw1 : 1 ≤ (t + 1) * (s * s * s * s * s) := le_trans c6 (Nat.le_mul_of_pos_left _ (by omega))
    obtain ⟨n, A, P, hseq⟩ := greedy (G := G) S d ((t + 1) * (s * s * s * s * s)) s
      (s * s * s * s * s) hw1 (by omega) S subset_rfl
    have hleft := hgd _ hw1 G hfree (S \ (range n).biUnion P) (hS.mono sdiff_subset)
      (fun x hx => (hOIH x (mem_sdiff.mp hx).1).mono (fun y hy =>
        mem_inter.mpr ⟨(mem_inter.mp hy).1, (mem_sdiff.mp (mem_inter.mp hy).2).1⟩) le_rfl) hseq.left
    exact chain s ω ℓ t (by omega) hfree hS hOIH hcore hseq hd c1 c2 c3 c4 le_rfl c5 c6 hleft

/-- A stable `(1,d)`-core is a `d`-clique. -/
theorem clique_of_core {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {S : Finset V} {d : ℕ} (h : HasCore G S 1 d) : ∃ X ⊆ S, IsClq G X ∧ X.card = d := by
  obtain ⟨A, hA'⟩ := h
  have hA : IsCore G S 1 d A := hA'
  refine ⟨VC A, hA.VC_sub, ?_, by rw [hA.card_VC, mul_one]⟩
  intro x hx y hy hxy
  obtain ⟨p, hp⟩ := mem_VC.mp hx
  obtain ⟨q, hq⟩ := mem_VC.mp hy
  by_cases hpq : p = q
  · subst hpq
    exact absurd (card_le_one.mp (hA.1 p).2.1.le x hp y hq) hxy
  · exact hA.adj_of_ne hpq hp hq

/-- Theorem A: `H_s`-free graphs have chromatic number bounded in terms of the clique number. -/
theorem thmA (s : ℕ) (hs : 2 ≤ s) : ∀ ω : ℕ, ∃ F : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj], ¬ (Hs s).IsIndContained G →
    ∀ S : Finset V, Small G S ω → col G S F := by
  intro ω
  induction ω with
  | zero =>
    refine ⟨0, ?_⟩
    intro V _ _ G _ _ S hS
    have hSe : S = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro x hx
      have := hS {x} (singleton_subset_iff.mpr hx) (fun u hu v hv huv => by
        rw [mem_singleton.mp hu, mem_singleton.mp hv] at huv; exact absurd rfl huv)
      simp at this
    rw [hSe]; exact col_empty 0
  | succ ω ih =>
    obtain ⟨ℓ, hℓ⟩ := ih
    have inner : ∀ d, 2 ≤ d → ∀ t, 1 ≤ t → ∃ g : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj], ¬ (Hs s).IsIndContained G →
        ∀ S : Finset V, Small G S (ω + 1) → (∀ x ∈ S, col G (nb G x ∩ S) ℓ) →
        ¬ HasCore G S t d → col G S g := by
      intro d hd
      induction d, hd using Nat.le_induction with
      | base =>
        intro t ht
        obtain ⟨g, hg⟩ := base_S2 s (ω + 1) t hs ht
        refine ⟨g, ?_⟩
        intro V _ _ G _ hf S hS _ hc
        exact hg G hf S hS hc
      | succ d hd ih =>
        let gd : ℕ → ℕ := fun t => if ht : 1 ≤ t then Classical.choose (ih t ht) else 0
        refine step_S s (ω + 1) ℓ d hs hd gd (fun t ht => ?_)
        rw [show gd t = Classical.choose (ih t ht) from dif_pos ht]
        exact Classical.choose_spec (ih t ht)
    obtain ⟨g, hg⟩ := inner (ω + 2) (by omega) 1 le_rfl
    refine ⟨g, ?_⟩
    intro V _ _ G _ hf S hS
    refine hg G hf S hS (fun x hx => hℓ G hf _ (hS.nb hx)) ?_
    intro hc
    obtain ⟨X, hX, hXq, hXc⟩ := clique_of_core hc
    have := hS X hX hXq
    omega


end GS


theorem OMA.solution : type_of% @GyarfasSumnerConjecture.gyarfas_sumner_conjecture.variants.radius_two := by
  intro W _ _ T _ hT hrad
  obtain ⟨c, hc⟩ := hrad
  have hs : 2 ≤ max 2 (Fintype.card W) := le_max_left _ _
  have hTH : T.IsIndContained (GS.Hs (max 2 (Fintype.card W))) :=
    GS.tree_le_Hs hT c hc _ (le_max_right _ _)
  choose F hF using GS.thmA _ hs
  refine ⟨F, ?_⟩
  intro V _ _ G _ hTG
  have hsmall : GS.Small G Finset.univ G.cliqueNum := fun X _ hX =>
    SimpleGraph.IsClique.card_le_cliqueNum (tc := fun u hu v hv huv => hX u hu v hv huv)
  obtain ⟨col, hcl, hp⟩ := hF G.cliqueNum G (fun h => hTG (hTH.trans h)) Finset.univ hsmall
  exact (show G.Colorable (F G.cliqueNum) from
    ⟨SimpleGraph.Coloring.mk (fun v => ⟨col v, hcl v (Finset.mem_univ v)⟩)
      (fun {u v} h heq => hp u (Finset.mem_univ u) v (Finset.mem_univ v) h (congrArg Fin.val heq))⟩).chromaticNumber_le

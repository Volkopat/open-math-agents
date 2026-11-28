import OMAStatements.S_wp_implicit_graph_conjecture

-- Problem: Implicit graph conjecture
-- Upstream: formal-conjectures statements/wp-implicit-graph-conjecture.lean:0 (declaration OMA.S_wp_implicit_graph_conjecture.main)
-- Credit: @marcusbuffett (the owner of the agent is credited as the solver)

/-!
# Disproof of the implicit graph conjecture

The counterexample follows H. Hatami and P. Hatami, The implicit graph conjecture is false,
arXiv:2111.13198 (2021). Their sparse-graph counting idea is specialised here to logarithmic
labels; the Lean code below is original.

Outline.
* Step 1 (`host`): for every `t ≥ 2` a first-moment count over bipartite graphs in which each
  of `t^8` left vertices picks one neighbour in each of `t` blocks of `t^7` right vertices shows
  that at least half of these `(t^7)^(t^9)` graphs are `Sparse t`: every induced subgraph on
  `m ≤ t` vertices is coded by `3m` ordered pairs.
* Step 2 (`exists_bad_tuple`): a decoder restricted to labels of bounded length is one Boolean
  table on `Q × Q`; each table represents at most `Q^N` graphs, so some tuple of `T > Q^2`
  sparse graphs is not represented by any single table.
* Step 3 (`Pfam`): the hereditary closure of the selected tuples over stages `j ≥ 16` has at
  most `n^(12 n)` members on `n` vertices.
* Step 4 (`OMA.disproof`): a decoder with label constant `k` fails at stage `max 16 k`.
-/

open Finset

namespace IGC

open Classical Finset

/-! ## Encoding bit strings as natural numbers -/

def enc : List Bool → ℕ
  | [] => 1
  | b :: l => 2 * enc l + b.toNat

theorem enc_pos (l : List Bool) : 1 ≤ enc l := by
  induction l with
  | nil => simp [enc]
  | cons b l ih => simp only [enc]; omega

theorem enc_lt (l : List Bool) : enc l < 2 ^ (l.length + 1) := by
  induction l with
  | nil => simp [enc]
  | cons b l ih =>
    simp only [enc, List.length_cons, pow_succ] at *
    have : b.toNat ≤ 1 := Bool.toNat_le b
    omega

theorem enc_injective : Function.Injective enc := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 h
    cases l2 with
    | nil => rfl
    | cons b l => simp only [enc] at h; have := enc_pos l; omega
  | cons b l ih =>
    intro l2 h
    cases l2 with
    | nil => simp only [enc] at h; have := enc_pos l; omega
    | cons b' l' =>
      simp only [enc] at h
      have hb : b = b' := by
        cases b <;> cases b' <;> simp at h ⊢ <;> omega
      subst hb
      have : enc l = enc l' := by omega
      rw [ih this]

/-! ## Graphs coded by a short list of ordered pairs -/

def codeGraph (m : ℕ) (g : Fin (3 * m) → Fin m × Fin m) : SimpleGraph (Fin m) :=
  SimpleGraph.fromRel fun a b => ∃ i, g i = (a, b)

theorem fromRel_congr {W : Type*} (r s : W → W → Prop)
    (h : ∀ a b, a ≠ b → (r a b ↔ s a b)) : SimpleGraph.fromRel r = SimpleGraph.fromRel s := by
  ext a b
  simp only [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hab, h1⟩
    exact ⟨hab, h1.imp (h a b hab).1 (h b a (Ne.symm hab)).1⟩
  · rintro ⟨hab, h1⟩
    exact ⟨hab, h1.imp (h a b hab).2 (h b a (Ne.symm hab)).2⟩

theorem fromRel_mem_codeGraph {m : ℕ} (hm : 1 ≤ m) (Z : Finset (Fin m × Fin m))
    (hZ : Z.card ≤ 3 * m) :
    ∃ g, SimpleGraph.fromRel (fun a b => (a, b) ∈ Z) = codeGraph m g := by
  let z0 : Fin m × Fin m := (⟨0, hm⟩, ⟨0, hm⟩)
  let e := Z.equivFin
  refine ⟨fun i => if h : i.val < Z.card then (e.symm ⟨i.val, h⟩).val else z0, ?_⟩
  unfold codeGraph
  apply fromRel_congr
  intro a b hab
  constructor
  · intro hz
    refine ⟨⟨(e ⟨(a, b), hz⟩).val, by have := (e ⟨(a, b), hz⟩).isLt; omega⟩, ?_⟩
    simp
  · rintro ⟨i, hi⟩
    by_cases h : i.val < Z.card
    · simp only [h, dite_true] at hi
      rw [← hi]; exact (e.symm ⟨i.val, h⟩).property
    · simp only [h, dite_false, z0, Prod.mk.injEq] at hi
      exact absurd (hi.1.symm.trans hi.2) hab

/-! ## Counting functions with prescribed values -/

theorem card_prescribed {ι α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    (D : Finset ι) (q : ι → α × β) (hq : Set.InjOn (fun p => (q p).1) D) :
    (univ.filter fun h : α → β => ∀ p ∈ D, h (q p).1 = (q p).2).card
      * Fintype.card β ^ D.card ≤ Fintype.card β ^ Fintype.card α := by
  set C : Finset α := D.image fun p => (q p).1 with hC
  have hCcard : C.card = D.card := card_image_of_injOn hq
  have hle : (univ.filter fun h : α → β => ∀ p ∈ D, h (q p).1 = (q p).2).card
      ≤ Fintype.card β ^ (Fintype.card α - C.card) := by
    have h1 : Fintype.card ({a // a ∉ C} → β) = Fintype.card β ^ (Fintype.card α - C.card) := by
      rw [Fintype.card_fun]
      congr 1
      rw [Fintype.card_subtype_compl, Fintype.card_coe]
    rw [← h1, ← card_univ]
    apply card_le_card_of_injOn (fun h a => h a.val)
    · intro _ _; exact mem_univ _
    · intro h1' hh1 h2' hh2 heq
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hh1 hh2
      funext a
      by_cases ha : a ∈ C
      · obtain ⟨p, hp, rfl⟩ := mem_image.1 ha
        rw [hh1 p hp, hh2 p hp]
      · exact congrFun heq ⟨a, ha⟩
  have hCle : C.card ≤ Fintype.card α := card_le_univ C
  calc _ ≤ Fintype.card β ^ (Fintype.card α - C.card) * Fintype.card β ^ D.card :=
        Nat.mul_le_mul_right _ hle
    _ = Fintype.card β ^ Fintype.card α := by
        rw [← pow_add, ← hCcard, Nat.sub_add_cancel hCle]

/-! ## Step 2: a tuple of graphs that no single table represents -/

noncomputable def reprSet (N Q : ℕ) (τ : Fin Q → Fin Q → Bool) : Finset (SimpleGraph (Fin N)) :=
  (univ : Finset (Fin N → Fin Q)).image fun lab =>
    SimpleGraph.fromRel fun u v => τ (lab u) (lab v) = true

theorem exists_bad_tuple (N Q T : ℕ) (S : Finset (SimpleGraph (Fin N)))
    (hQ0 : 0 < Q) (hT : Q * Q < T) (hS : 2 * Q ^ N ≤ S.card) :
    ∃ F : Fin T → SimpleGraph (Fin N), (∀ i, F i ∈ S) ∧
      ∀ τ : Fin Q → Fin Q → Bool, ∃ i, F i ∉ reprSet N Q τ := by
  by_contra hcon
  push Not at hcon
  have hsub : Fintype.piFinset (fun _ : Fin T => S) ⊆
      (univ : Finset (Fin Q → Fin Q → Bool)).biUnion
        (fun τ => Fintype.piFinset fun _ : Fin T => reprSet N Q τ) := by
    intro F hF
    rw [Fintype.mem_piFinset] at hF
    obtain ⟨τ, hτ⟩ := hcon F hF
    exact mem_biUnion.2 ⟨τ, mem_univ _, Fintype.mem_piFinset.2 hτ⟩
  have h1 := card_le_card hsub
  rw [Fintype.card_piFinset_const] at h1
  have h2 : ((univ : Finset (Fin Q → Fin Q → Bool)).biUnion
        (fun τ => Fintype.piFinset fun _ : Fin T => reprSet N Q τ)).card ≤ 2 ^ (Q * Q) * (Q ^ N) ^ T := by
    refine (card_biUnion_le).trans ?_
    have : ∀ τ ∈ (univ : Finset (Fin Q → Fin Q → Bool)),
        (Fintype.piFinset fun _ : Fin T => reprSet N Q τ).card ≤ (Q ^ N) ^ T := by
      intro τ _
      rw [Fintype.card_piFinset_const]
      apply Nat.pow_le_pow_left
      refine card_image_le.trans ?_
      simp
    refine (sum_le_card_nsmul _ _ _ this).trans ?_
    simp [pow_mul]
  have hQ : 0 < Q ^ N := pow_pos hQ0 _
  have h3 : 2 ^ (Q * Q) * (Q ^ N) ^ T < (2 * Q ^ N) ^ T := by
    rw [mul_pow]
    exact Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right (by norm_num) hT) (pow_pos hQ _)
  have h4 : (2 * Q ^ N) ^ T ≤ S.card ^ T := Nat.pow_le_pow_left hS _
  omega


/-! ## Step 1: a host whose small vertex sets span few edges -/

def Sparse {W : Type*} (t : ℕ) (G : SimpleGraph W) : Prop :=
  ∀ m, 1 ≤ m → m ≤ t → ∀ f : Fin m → W, Function.Injective f → ∃ g, G.comap f = codeGraph m g

abbrev Vtx (t : ℕ) := Fin (t ^ 8) ⊕ (Fin t × Fin (t ^ 7))
abbrev Cell (t : ℕ) := Fin (t ^ 8) × Fin t

def pt (t : ℕ) : Vtx t → Vtx t → Option (Cell t × Fin (t ^ 7))
  | .inl v, .inr (β, x) => some ((v, β), x)
  | _, _ => none

theorem pt_inj {t : ℕ} {u w u' w' : Vtx t} {q : Cell t × Fin (t ^ 7)}
    (h1 : pt t u w = some q) (h2 : pt t u' w' = some q) : u = u' ∧ w = w' := by
  rcases u with v | ⟨β, x⟩ <;> rcases w with v' | ⟨β', x'⟩ <;>
    rcases u' with v2 | ⟨β2, x2⟩ <;> rcases w' with v2' | ⟨β2', x2'⟩ <;>
    simp_all [pt]
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
  simp_all

def Rh (t : ℕ) (h : Cell t → Fin (t ^ 7)) (u w : Vtx t) : Prop :=
  ∃ q, pt t u w = some q ∧ h q.1 = q.2

def hostG (t : ℕ) (h : Cell t → Fin (t ^ 7)) : SimpleGraph (Vtx t) :=
  SimpleGraph.fromRel (Rh t h)

theorem hostG_comap {t m : ℕ} (h : Cell t → Fin (t ^ 7)) (f : Fin m → Vtx t)
    (hf : Function.Injective f) :
    (hostG t h).comap f = SimpleGraph.fromRel (fun a b =>
      (a, b) ∈ (univ.filter fun p : Fin m × Fin m => Rh t h (f p.1) (f p.2))) := by
  ext a b
  simp only [SimpleGraph.comap_adj, hostG, SimpleGraph.fromRel_adj, mem_filter, mem_univ,
    true_and, ne_eq, hf.eq_iff]

theorem hostG_injective (t : ℕ) : Function.Injective (hostG t) := by
  intro h h' heq
  funext c
  obtain ⟨v, β⟩ := c
  have hadj : (hostG t h).Adj (.inl v) (.inr (β, h (v, β))) := by
    simp only [hostG, SimpleGraph.fromRel_adj]
    exact ⟨by simp, Or.inl ⟨((v, β), h (v, β)), rfl, rfl⟩⟩
  rw [heq] at hadj
  simp only [hostG, SimpleGraph.fromRel_adj] at hadj
  rcases hadj.2 with ⟨q, hq, hq2⟩ | ⟨q, hq, hq2⟩
  · simp only [pt, Option.some.injEq] at hq
    subst hq
    exact hq2.symm
  · simp [pt] at hq

noncomputable def badM (t m : ℕ) : Finset (Cell t → Fin (t ^ 7)) :=
  (univ.filter fun f : Fin m → Vtx t => Function.Injective f).biUnion fun f =>
    (powersetCard (3 * m + 1) (univ : Finset (Fin m × Fin m))).biUnion fun D =>
      univ.filter fun h => ∀ p ∈ D, Rh t h (f p.1) (f p.2)

theorem card_badFD {t m : ℕ} (f : Fin m → Vtx t) (hf : Function.Injective f)
    (D : Finset (Fin m × Fin m)) :
    (univ.filter fun h : Cell t → Fin (t ^ 7) => ∀ p ∈ D, Rh t h (f p.1) (f p.2)).card
      * (t ^ 7) ^ D.card ≤ (t ^ 7) ^ (t ^ 8 * t) := by
  have hK : Fintype.card (Fin (t ^ 7)) = t ^ 7 := Fintype.card_fin _
  have hC : Fintype.card (Cell t) = t ^ 8 * t := by simp
  rcases (univ.filter fun h : Cell t → Fin (t ^ 7) => ∀ p ∈ D, Rh t h (f p.1) (f p.2)).eq_empty_or_nonempty
    with he | ⟨h0, hh0⟩
  · rw [he]; simp
  rcases D.eq_empty_or_nonempty with hD | ⟨p0, hp0⟩
  · subst hD
    simp only [card_empty, pow_zero, mul_one]
    refine (card_le_univ _).trans ?_
    simp
  simp only [mem_filter, mem_univ, true_and] at hh0
  obtain ⟨q0, -, -⟩ := hh0 p0 hp0
  let q : Fin m × Fin m → Cell t × Fin (t ^ 7) := fun p => (pt t (f p.1) (f p.2)).getD q0
  have hq : ∀ p ∈ D, pt t (f p.1) (f p.2) = some (q p) ∧ h0 (q p).1 = (q p).2 := by
    intro p hp
    obtain ⟨r, hr, hr2⟩ := hh0 p hp
    simp only [q, hr, Option.getD_some, true_and]
    exact hr2
  have hinj : Set.InjOn (fun p => (q p).1) D := by
    intro p hp p' hp' heq
    obtain ⟨h1, h1'⟩ := hq p hp
    obtain ⟨h2, h2'⟩ := hq p' hp'
    simp only at heq
    have hqq : q p = q p' := Prod.ext heq (by rw [← h1', ← h2', heq])
    rw [hqq] at h1
    obtain ⟨e1, e2⟩ := pt_inj h1 h2
    exact Prod.ext (hf e1) (hf e2)
  have := card_prescribed D q hinj
  rw [hK, hC] at this
  refine le_trans (Nat.mul_le_mul_right _ (card_le_card ?_)) this
  intro h hh
  simp only [mem_filter, mem_univ, true_and] at hh ⊢
  intro p hp
  obtain ⟨r, hr, hr2⟩ := hh p hp
  rw [(hq p hp).1, Option.some.injEq] at hr
  rw [hr]; exact hr2

theorem arith_badM {t m : ℕ} (ht : 2 ≤ t) (hm1 : 1 ≤ m) (hmt : m ≤ t) :
    (t ^ 8 + t * t ^ 7) ^ m * (m * m) ^ (3 * m + 1) * t ^ 2 ≤ (t ^ 7) ^ (3 * m + 1) := by
  have h1 : t ^ 8 + t * t ^ 7 ≤ t ^ 9 := by
    have : t * t ^ 7 = t ^ 8 := by ring
    rw [this]
    have : t ^ 9 = t * t ^ 8 := by ring
    rw [this]; nlinarith [pow_pos (by omega : 0 < t) 8]
  have h2 : m * m ≤ t ^ 2 := by nlinarith
  calc (t ^ 8 + t * t ^ 7) ^ m * (m * m) ^ (3 * m + 1) * t ^ 2
      ≤ (t ^ 9) ^ m * (t ^ 2) ^ (3 * m + 1) * t ^ 2 := by
        gcongr
    _ = t ^ (15 * m + 4) := by
        rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]; congr 1; ring
    _ ≤ t ^ (7 * (3 * m + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
    _ = (t ^ 7) ^ (3 * m + 1) := by rw [pow_mul]

theorem card_badM {t m : ℕ} (ht : 2 ≤ t) (hm1 : 1 ≤ m) (hmt : m ≤ t) :
    (badM t m).card * t ^ 2 ≤ (t ^ 7) ^ (t ^ 8 * t) := by
  set K := t ^ 7
  set C := t ^ 8 * t
  set Finj := (univ.filter fun f : Fin m → Vtx t => Function.Injective f)
  set PC := powersetCard (3 * m + 1) (univ : Finset (Fin m × Fin m))
  have hA : (badM t m).card * K ^ (3 * m + 1) ≤ Finj.card * PC.card * K ^ C := by
    calc (badM t m).card * K ^ (3 * m + 1)
        ≤ (∑ f ∈ Finj, ∑ D ∈ PC,
            (univ.filter fun h : Cell t → Fin (t ^ 7) => ∀ p ∈ D, Rh t h (f p.1) (f p.2)).card)
            * K ^ (3 * m + 1) :=
          Nat.mul_le_mul_right _ (card_biUnion_le.trans (sum_le_sum fun f _ => card_biUnion_le))
      _ = ∑ f ∈ Finj, ∑ D ∈ PC,
            (univ.filter fun h : Cell t → Fin (t ^ 7) => ∀ p ∈ D, Rh t h (f p.1) (f p.2)).card
            * K ^ (3 * m + 1) := by
          rw [sum_mul]; congr 1; ext f; rw [sum_mul]
      _ ≤ ∑ f ∈ Finj, ∑ D ∈ PC, K ^ C := by
          refine sum_le_sum fun f hf => sum_le_sum fun D hD => ?_
          have hfi : Function.Injective f := (mem_filter.1 hf).2
          have := card_badFD f hfi D
          rw [(mem_powersetCard.1 hD).2] at this
          exact this
      _ = Finj.card * PC.card * K ^ C := by simp [sum_const, mul_assoc]
  have hF : Finj.card ≤ (t ^ 8 + t * t ^ 7) ^ m := by
    refine (card_le_univ _).trans ?_
    simp
  have hP : PC.card ≤ (m * m) ^ (3 * m + 1) := by
    simp only [PC, card_powersetCard, card_univ, Fintype.card_prod, Fintype.card_fin]
    exact Nat.choose_le_pow _ _
  have hB := arith_badM ht hm1 hmt
  have hKpos : 0 < K ^ (3 * m + 1) := pow_pos (pow_pos (by omega) _) _
  refine Nat.le_of_mul_le_mul_right ?_ hKpos
  calc (badM t m).card * t ^ 2 * K ^ (3 * m + 1)
      = (badM t m).card * K ^ (3 * m + 1) * t ^ 2 := by ring
    _ ≤ Finj.card * PC.card * K ^ C * t ^ 2 := Nat.mul_le_mul_right _ hA
    _ ≤ (t ^ 8 + t * t ^ 7) ^ m * (m * m) ^ (3 * m + 1) * K ^ C * t ^ 2 := by gcongr
    _ = ((t ^ 8 + t * t ^ 7) ^ m * (m * m) ^ (3 * m + 1) * t ^ 2) * K ^ C := by ring
    _ ≤ K ^ (3 * m + 1) * K ^ C := Nat.mul_le_mul_right _ hB
    _ = K ^ C * K ^ (3 * m + 1) := by ring

noncomputable def badSet (t : ℕ) : Finset (Cell t → Fin (t ^ 7)) :=
  (Icc 1 t).biUnion (badM t)

theorem card_badSet {t : ℕ} (ht : 2 ≤ t) :
    (badSet t).card * t ≤ (t ^ 7) ^ (t ^ 8 * t) := by
  have h1 : (badSet t).card * t ^ 2 ≤ t * (t ^ 7) ^ (t ^ 8 * t) := by
    calc (badSet t).card * t ^ 2 ≤ (∑ m ∈ Icc 1 t, (badM t m).card) * t ^ 2 :=
          Nat.mul_le_mul_right _ card_biUnion_le
      _ = ∑ m ∈ Icc 1 t, (badM t m).card * t ^ 2 := sum_mul _ _ _
      _ ≤ ∑ m ∈ Icc 1 t, (t ^ 7) ^ (t ^ 8 * t) := by
          refine sum_le_sum fun m hm => ?_
          obtain ⟨h1, h2⟩ := mem_Icc.1 hm
          exact card_badM ht h1 h2
      _ = t * (t ^ 7) ^ (t ^ 8 * t) := by simp
  have : (badSet t).card * t * t ≤ (t ^ 7) ^ (t ^ 8 * t) * t := by
    calc (badSet t).card * t * t = (badSet t).card * t ^ 2 := by ring
      _ ≤ _ := h1
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right this (by omega)

theorem mem_badSet {t : ℕ} (h : Cell t → Fin (t ^ 7)) (hns : ¬ Sparse t (hostG t h)) :
    h ∈ badSet t := by
  simp only [Sparse, not_forall, exists_prop] at hns
  obtain ⟨m, hm1, hmt, f, hf, hg⟩ := hns
  set Z := (univ.filter fun p : Fin m × Fin m => Rh t h (f p.1) (f p.2))
  by_cases hZ : Z.card ≤ 3 * m
  · exfalso
    obtain ⟨g, hg'⟩ := fromRel_mem_codeGraph hm1 Z hZ
    exact hg ⟨g, (hostG_comap h f hf).trans hg'⟩
  · obtain ⟨D, hDZ, hD⟩ := exists_subset_card_eq (s := Z) (n := 3 * m + 1) (by omega)
    simp only [badSet, badM, mem_biUnion, mem_Icc, mem_filter, mem_univ, true_and,
      mem_powersetCard, subset_univ]
    refine ⟨m, ⟨hm1, hmt⟩, f, hf, D, hD, ?_⟩
    intro p hp
    have := hDZ hp
    simp only [Z, mem_filter, mem_univ, true_and] at this
    exact this

theorem host (t : ℕ) (ht : 2 ≤ t) :
    ∃ S : Finset (SimpleGraph (Fin (2 * t ^ 8))), (∀ G ∈ S, Sparse t G) ∧
      (t ^ 7) ^ (t ^ 8 * t) ≤ 2 * S.card := by
  have hcard : Fintype.card (Vtx t) = 2 * t ^ 8 := by simp; ring
  let e := Fintype.equivFinOfCardEq hcard
  let S0 := (univ : Finset (Cell t → Fin (t ^ 7))).filter fun h => Sparse t (hostG t h)
  refine ⟨S0.image fun h => (hostG t h).comap e.symm, ?_, ?_⟩
  · intro G hG
    obtain ⟨h, hh, rfl⟩ := mem_image.1 hG
    have hs := (mem_filter.1 hh).2
    intro m hm1 hmt f hf
    obtain ⟨g, hg⟩ := hs m hm1 hmt (e.symm ∘ f) (e.symm.injective.comp hf)
    exact ⟨g, hg⟩
  · have hinj : Function.Injective fun h : Cell t → Fin (t ^ 7) => (hostG t h).comap e.symm := by
      intro h h' heq
      apply hostG_injective t
      ext u v
      have := congrArg (fun H : SimpleGraph (Fin (2 * t ^ 8)) => H.Adj (e u) (e v)) heq
      simpa using this
    rw [card_image_of_injective _ hinj]
    have hcov : (univ : Finset (Cell t → Fin (t ^ 7))) ⊆ S0 ∪ badSet t := by
      intro h _
      by_cases hs : Sparse t (hostG t h)
      · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, hs⟩)
      · exact mem_union_right _ (mem_badSet h hs)
    have h1 := (card_le_card hcov).trans (card_union_le _ _)
    have h2 := card_badSet ht
    have h3 : (univ : Finset (Cell t → Fin (t ^ 7))).card = (t ^ 7) ^ (t ^ 8 * t) := by simp
    have h4 : (badSet t).card * 2 ≤ (badSet t).card * t := Nat.mul_le_mul_left _ ht
    omega


/-! ## Parameters of stage `j` -/

theorem two_pow_ge (j : ℕ) (hj : 16 ≤ j) : 17 * j ^ 2 ≤ 2 ^ j := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    calc 17 * (j + 1) ^ 2 ≤ 2 * (17 * j ^ 2) := by nlinarith
      _ ≤ 2 * 2 ^ j := by omega
      _ = 2 ^ (j + 1) := by ring

def Lj (j : ℕ) : ℕ := j * (8 * j + 2)
def Qj (j : ℕ) : ℕ := 2 ^ (Lj j + 1)
def Tj (j : ℕ) : ℕ := 2 ^ (2 ^ j)

theorem param_t (j : ℕ) (hj : 16 ≤ j) : 2 * (Lj j + 1) + 1 ≤ 2 ^ j := by
  have := two_pow_ge j hj
  unfold Lj
  nlinarith

theorem param_count {t b : ℕ} (hb : 1 ≤ b) (ht : 2 * b + 1 ≤ t) :
    2 * (2 ^ b) ^ (2 * t ^ 8) * 2 ≤ (t ^ 7) ^ (t ^ 8 * t) := by
  have ht2 : 2 ≤ t ^ 7 := by
    calc 2 ≤ t := by omega
      _ ≤ t ^ 7 := Nat.le_self_pow (by norm_num) t
  have h8 : 2 ≤ t ^ 8 := by
    calc 2 ≤ t := by omega
      _ ≤ t ^ 8 := Nat.le_self_pow (by norm_num) t
  calc 2 * (2 ^ b) ^ (2 * t ^ 8) * 2 = 2 ^ (b * (2 * t ^ 8) + 2) := by
        rw [← pow_mul]; ring
    _ ≤ 2 ^ (t ^ 8 * t) := by
        apply Nat.pow_le_pow_right (by norm_num)
        nlinarith
    _ ≤ (t ^ 7) ^ (t ^ 8 * t) := Nat.pow_le_pow_left ht2 _

theorem stage_exists (j : ℕ) (hj : 16 ≤ j) :
    ∃ F : Fin (Tj j) → SimpleGraph (Fin (2 * (2 ^ j) ^ 8)), (∀ i, Sparse (2 ^ j) (F i)) ∧
      ∀ τ : Fin (Qj j) → Fin (Qj j) → Bool, ∃ i, F i ∉ reprSet _ (Qj j) τ := by
  have hpt := param_t j hj
  obtain ⟨S, hSp, hSc⟩ := host (2 ^ j) (by omega)
  have hQ0 : 0 < Qj j := by unfold Qj; positivity
  have hT : Qj j * Qj j < Tj j := by
    unfold Qj Tj
    rw [← pow_add]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hS : 2 * Qj j ^ (2 * (2 ^ j) ^ 8) ≤ S.card := by
    have := param_count (t := 2 ^ j) (b := Lj j + 1) (by omega) hpt
    unfold Qj
    omega
  obtain ⟨F, hF, hrep⟩ := exists_bad_tuple _ _ _ S hQ0 hT hS
  exact ⟨F, fun i => hSp _ (hF i), hrep⟩

noncomputable def Fsel (j : ℕ) (hj : 16 ≤ j) : Fin (Tj j) → SimpleGraph (Fin (2 * (2 ^ j) ^ 8)) :=
  Classical.choose (stage_exists j hj)

theorem Fsel_sparse (j : ℕ) (hj : 16 ≤ j) (i) : Sparse (2 ^ j) (Fsel j hj i) :=
  (Classical.choose_spec (stage_exists j hj)).1 i

theorem Fsel_bad (j : ℕ) (hj : 16 ≤ j) (τ : Fin (Qj j) → Fin (Qj j) → Bool) :
    ∃ i, Fsel j hj i ∉ reprSet _ (Qj j) τ :=
  (Classical.choose_spec (stage_exists j hj)).2 τ

/-! ## Step 3: the hereditary family -/

def Pfam (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ j, ∃ hj : 16 ≤ j, ∃ i, ∃ f : Fin n ↪ Fin (2 * (2 ^ j) ^ 8), G = (Fsel j hj i).comap f

theorem arith_growth {n : ℕ} (hn : 2 ≤ n) :
    (n * n) ^ (3 * n) + n * (2 ^ n * (2 * n ^ 8) ^ n) ≤ n ^ (12 * n) := by
  have hnn : n ≤ n ^ n := Nat.le_self_pow (by omega) n
  have h2n : 2 ^ n ≤ n ^ n := Nat.pow_le_pow_left hn n
  have h9 : 2 * n ^ 8 ≤ n ^ 9 := by
    have : n ^ 9 = n * n ^ 8 := by ring
    rw [this]; exact Nat.mul_le_mul_right _ hn
  have hA : (n * n) ^ (3 * n) ≤ n ^ (11 * n) := by
    rw [← pow_two, ← pow_mul]; exact Nat.pow_le_pow_right (by omega) (by omega)
  have hB : n * (2 ^ n * (2 * n ^ 8) ^ n) ≤ n ^ (11 * n) := by
    calc n * (2 ^ n * (2 * n ^ 8) ^ n) ≤ n ^ n * (n ^ n * (n ^ 9) ^ n) := by
          gcongr
      _ = n ^ (11 * n) := by rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; ring
  calc _ ≤ n ^ (11 * n) + n ^ (11 * n) := Nat.add_le_add hA hB
    _ = 2 * n ^ (11 * n) := by ring
    _ ≤ n ^ n * n ^ (11 * n) := Nat.mul_le_mul_right _ (hn.trans hnn)
    _ = n ^ (12 * n) := by rw [← pow_add]; congr 1; ring

theorem card_Pfam {n : ℕ} (hn : 2 ≤ n) :
    (univ.filter fun G : SimpleGraph (Fin n) => Pfam n G).card ≤ n ^ (12 * n) := by
  set A := (univ : Finset (Fin (3 * n) → Fin n × Fin n)).image (codeGraph n)
  set B := ((range n).filter fun j => 2 ^ j < n).biUnion fun j =>
    if hj : 16 ≤ j then (univ : Finset (Fin (Tj j))).biUnion fun i =>
      (univ : Finset (Fin n → Fin (2 * (2 ^ j) ^ 8))).image fun f => (Fsel j hj i).comap f
    else ∅
  have hsub : (univ.filter fun G : SimpleGraph (Fin n) => Pfam n G) ⊆ A ∪ B := by
    intro G hG
    obtain ⟨j, hj, i, f, rfl⟩ := (mem_filter.1 hG).2
    rw [mem_union]
    by_cases hjn : n ≤ 2 ^ j
    · left
      obtain ⟨g, hg⟩ := Fsel_sparse j hj i n (by omega) hjn f f.injective
      exact mem_image.2 ⟨g, mem_univ _, hg.symm⟩
    · right
      push Not at hjn
      have hjlt : j < n := (Nat.lt_two_pow_self).trans hjn
      refine mem_biUnion.2 ⟨j, mem_filter.2 ⟨mem_range.2 hjlt, hjn⟩, ?_⟩
      rw [dif_pos hj]
      exact mem_biUnion.2 ⟨i, mem_univ _, mem_image.2 ⟨f, mem_univ _, rfl⟩⟩
  have hA : A.card ≤ (n * n) ^ (3 * n) := by
    refine card_image_le.trans ?_
    simp
  have hB : B.card ≤ n * (2 ^ n * (2 * n ^ 8) ^ n) := by
    refine card_biUnion_le.trans ?_
    have : ∀ j ∈ (range n).filter (fun j => 2 ^ j < n),
        (if hj : 16 ≤ j then (univ : Finset (Fin (Tj j))).biUnion fun i =>
          (univ : Finset (Fin n → Fin (2 * (2 ^ j) ^ 8))).image fun f => (Fsel j hj i).comap f
        else ∅).card ≤ 2 ^ n * (2 * n ^ 8) ^ n := by
      intro j hjm
      have hjn := (mem_filter.1 hjm).2
      split_ifs with hj
      · refine card_biUnion_le.trans ?_
        have hterm : ∀ i ∈ (univ : Finset (Fin (Tj j))),
            ((univ : Finset (Fin n → Fin (2 * (2 ^ j) ^ 8))).image
              fun f => (Fsel j hj i).comap f).card ≤ (2 * n ^ 8) ^ n := by
          intro i _
          refine card_image_le.trans ?_
          simp only [card_univ, Fintype.card_fun, Fintype.card_fin]
          apply Nat.pow_le_pow_left
          have : (2 ^ j) ^ 8 ≤ n ^ 8 := Nat.pow_le_pow_left hjn.le 8
          omega
        refine (sum_le_card_nsmul _ _ _ hterm).trans ?_
        simp only [card_univ, Fintype.card_fin, smul_eq_mul]
        apply Nat.mul_le_mul_right
        unfold Tj
        exact Nat.pow_le_pow_right (by norm_num) hjn.le
      · simp
    refine (sum_le_card_nsmul _ _ _ this).trans ?_
    simp only [smul_eq_mul]
    apply Nat.mul_le_mul_right
    exact (card_filter_le _ _).trans (by simp)
  calc _ ≤ (A ∪ B).card := card_le_card hsub
    _ ≤ A.card + B.card := card_union_le _ _
    _ ≤ _ := (Nat.add_le_add hA hB).trans (arith_growth hn)

open OMA.S_wp_implicit_graph_conjecture in
theorem Pfam_hereditary : Hereditary Pfam := by
  intro m n f G ⟨j, hj, i, g, hG⟩
  exact ⟨j, hj, i, f.trans g, by rw [hG]; rfl⟩

open OMA.S_wp_implicit_graph_conjecture in
theorem Pfam_growth : SmallGrowth Pfam := by
  refine ⟨12, fun n hn => ?_⟩
  have hpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hpow : (2 : ℝ) ^ (12 * (n : ℝ) * Real.logb 2 n) = (n : ℝ) ^ (12 * n) := by
    rw [show (12 : ℝ) * n * Real.logb 2 n = Real.logb 2 n * ((12 * n : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hpos,
      Real.rpow_natCast]
  rw [hpow]
  exact_mod_cast card_Pfam hn

end IGC

open Classical IGC in
theorem OMA.disproof : ¬ (type_of% @OMA.S_wp_implicit_graph_conjecture.main) := by
  intro hmain
  obtain ⟨D, k, -, hrep⟩ := hmain Pfam Pfam_hereditary Pfam_growth
  set j := max 16 k with hjdef
  have hj : 16 ≤ j := le_max_left _ _
  have hk : k ≤ j := le_max_right _ _
  let τ : Fin (Qj j) → Fin (Qj j) → Bool := fun a b =>
    D (Function.invFun enc a.val, Function.invFun enc b.val)
  obtain ⟨i, hi⟩ := Fsel_bad j hj τ
  have hP : Pfam _ (Fsel j hj i) := ⟨j, hj, i, Function.Embedding.refl _, by ext; rfl⟩
  obtain ⟨label, hlen, hadj⟩ := hrep _ _ hP
  have hlog : Nat.log 2 (2 * (2 ^ j) ^ 8) = 8 * j + 1 := by
    rw [show 2 * (2 ^ j) ^ 8 = 2 ^ (8 * j + 1) by ring]
    exact Nat.log_pow (by norm_num) _
  have hlab : ∀ v, enc (label v) < Qj j := by
    intro v
    have h1 := hlen v
    rw [hlog] at h1
    have h2 : (label v).length ≤ Lj j := by
      unfold Lj
      calc (label v).length ≤ k * (8 * j + 1 + 1) := h1
        _ ≤ j * (8 * j + 2) := Nat.mul_le_mul hk (by omega)
    calc enc (label v) < 2 ^ ((label v).length + 1) := enc_lt _
      _ ≤ Qj j := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hinv : ∀ l, Function.invFun enc (enc l) = l :=
    Function.leftInverse_invFun enc_injective
  apply hi
  unfold reprSet
  refine Finset.mem_image.2 ⟨fun v => ⟨enc (label v), hlab v⟩, Finset.mem_univ _, ?_⟩
  ext u v
  simp only [SimpleGraph.fromRel_adj, τ, hinv]
  constructor
  · rintro ⟨huv, h | h⟩
    · exact (hadj u v huv).2 h
    · exact ((hadj v u (Ne.symm huv)).2 h).symm
  · intro hA
    have huv : u ≠ v := (Fsel j hj i).ne_of_adj hA
    exact ⟨huv, Or.inl ((hadj u v huv).1 hA)⟩

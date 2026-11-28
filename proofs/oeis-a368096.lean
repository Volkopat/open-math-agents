import OMAStatements.S_oeis_a368096
import Mathlib

namespace OMA.A368096Proof

open OMA.S_oeis_a368096

theorem card_image_congr {α β γ : Type*} [DecidableEq β] [DecidableEq γ] (X : Finset α)
    (f : α → β) (g : α → γ) (h : ∀ x ∈ X, ∀ y ∈ X, f x = f y ↔ g x = g y) :
    (X.image f).card = (X.image g).card := by
  have e1 : (X.image (fun x => (f x, g x))).image Prod.fst = X.image f := Finset.image_image
  have e2 : (X.image (fun x => (f x, g x))).image Prod.snd = X.image g := Finset.image_image
  have i1 : Set.InjOn Prod.fst ((X.image (fun x => (f x, g x)) : Finset (β × γ)) : Set (β × γ)) := by
    intro u hu v hv huv
    rw [Finset.mem_coe, Finset.mem_image] at hu hv
    obtain ⟨x, hx, rfl⟩ := hu
    obtain ⟨y, hy, rfl⟩ := hv
    exact Prod.ext huv ((h x hx y hy).1 huv)
  have i2 : Set.InjOn Prod.snd ((X.image (fun x => (f x, g x)) : Finset (β × γ)) : Set (β × γ)) := by
    intro u hu v hv huv
    rw [Finset.mem_coe, Finset.mem_image] at hu hv
    obtain ⟨x, hx, rfl⟩ := hu
    obtain ⟨y, hy, rfl⟩ := hv
    exact Prod.ext ((h x hx y hy).2 huv) huv
  rw [← e1, ← e2, Finset.card_image_of_injOn i1, Finset.card_image_of_injOn i2]

/-- The action of a permutation on a set-system. -/
def act {n : ℕ} (σ : Equiv.Perm (Fin n)) (S : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  S.image (fun s => s.map σ.toEmbedding)

theorem mem_orb {n : ℕ} (S X : Finset (Finset (Fin n))) :
    X ∈ orb n S ↔ ∃ σ : Equiv.Perm (Fin n), act σ S = X := by
  simp only [orb, act, Finset.mem_image, Finset.mem_univ, true_and]

theorem act_trans {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (S : Finset (Finset (Fin n))) :
    act τ (act σ S) = act (σ.trans τ) S := by
  simp only [act, Finset.image_image, Function.comp_def, Finset.map_map, Equiv.trans_toEmbedding]

theorem act_refl {n : ℕ} (S : Finset (Finset (Fin n))) : act (Equiv.refl (Fin n)) S = S := by
  simp [act]

theorem orb_eq_of_act {n : ℕ} (σ : Equiv.Perm (Fin n)) (S : Finset (Finset (Fin n))) :
    orb n (act σ S) = orb n S := by
  ext X
  rw [mem_orb, mem_orb]
  constructor
  · rintro ⟨τ, rfl⟩
    exact ⟨σ.trans τ, (act_trans σ τ S).symm⟩
  · rintro ⟨τ, rfl⟩
    refine ⟨σ.symm.trans τ, ?_⟩
    rw [act_trans, ← Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.refl_trans]

theorem orb_eq_iff {n : ℕ} (S S' : Finset (Finset (Fin n))) :
    orb n S = orb n S' ↔ ∃ σ : Equiv.Perm (Fin n), act σ S = S' := by
  constructor
  · intro h
    have hm : S' ∈ orb n S := by
      rw [h, mem_orb]
      exact ⟨Equiv.refl _, act_refl S'⟩
    exact (mem_orb S S').1 hm
  · rintro ⟨σ, rfl⟩
    exact (orb_eq_of_act σ S).symm

/-- The set-system of an ordered pair. -/
def pr {n : ℕ} (p : Finset (Fin n) × Finset (Fin n)) : Finset (Finset (Fin n)) := {p.1, p.2}

/-- Region sizes of an ordered pair: `(|A ∩ B|, |A \ B|, |B \ A|)`. -/
def rsz {n : ℕ} (p : Finset (Fin n) × Finset (Fin n)) : ℕ × ℕ × ℕ :=
  ((p.1 ∩ p.2).card, (p.1 \ p.2).card, (p.2 \ p.1).card)

/-- Ordered pairs giving the two-block systems of weight `n`, the smaller block first. -/
def Good (n : ℕ) : Finset (Finset (Fin n) × Finset (Fin n)) :=
  Finset.univ.filter (fun p => p.1.Nonempty ∧ p.2.Nonempty ∧ p.1 ≠ p.2 ∧
    p.1.card + p.2.card = n ∧ p.1.card ≤ p.2.card)

theorem act_pr {n : ℕ} (σ : Equiv.Perm (Fin n)) (A B : Finset (Fin n)) :
    act σ {A, B} = {A.map σ.toEmbedding, B.map σ.toEmbedding} := by
  simp only [act, Finset.image_insert, Finset.image_singleton]

theorem rsz_map {n : ℕ} (σ : Equiv.Perm (Fin n)) (A B : Finset (Fin n)) :
    rsz (A.map σ.toEmbedding, B.map σ.toEmbedding) = rsz (A, B) := by
  simp only [rsz, ← Finset.map_inter, ← Finset.map_sdiff, Finset.card_map]

theorem rsz_eq_of_orb {n : ℕ} {p q : Finset (Fin n) × Finset (Fin n)} (hp : p ∈ Good n)
    (hq : q ∈ Good n) (h : orb n (pr p) = orb n (pr q)) : rsz p = rsz q := by
  obtain ⟨A, B⟩ := p
  obtain ⟨A', B'⟩ := q
  simp only [Good, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
  obtain ⟨σ, hσ⟩ := (orb_eq_iff _ _).1 h
  simp only [pr, act_pr] at hσ
  have h1 : A.map σ.toEmbedding ∈ ({A', B'} : Finset (Finset (Fin n))) := by
    rw [← hσ]
    exact Finset.mem_insert_self _ _
  have h2 : A' ∈ ({A.map σ.toEmbedding, B.map σ.toEmbedding} : Finset (Finset (Fin n))) := by
    rw [hσ]
    exact Finset.mem_insert_self _ _
  have h3 : B' ∈ ({A.map σ.toEmbedding, B.map σ.toEmbedding} : Finset (Finset (Fin n))) := by
    rw [hσ]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [Finset.mem_insert, Finset.mem_singleton] at h1 h2 h3
  rcases h1 with e1 | e1
  · rcases h3 with e3 | e3
    · exact absurd (e1.symm.trans e3.symm) hq.2.2.1
    · rw [← e1, e3, rsz_map]
  · rcases h2 with e2 | e2
    · exact absurd (e2.trans e1) hq.2.2.1
    · have hc : B.card ≤ A.card := by
        have hh := hq.2.2.2.2
        rw [e2, ← e1, Finset.card_map, Finset.card_map] at hh
        exact hh
      have k1 := Finset.card_sdiff_add_card_inter A B
      have k2 := Finset.card_sdiff_add_card_inter B A
      rw [Finset.inter_comm B A] at k2
      have hd : (A \ B).card = (B \ A).card := by
        have := hp.2.2.2.2
        omega
      rw [← e1, e2, rsz_map]
      simp only [rsz, Finset.inter_comm B A, hd]

/-- The region label of a vertex. -/
def lab {n : ℕ} (A B : Finset (Fin n)) (x : Fin n) : Bool × Bool := (decide (x ∈ A), decide (x ∈ B))

theorem iff_of_decide {p q : Prop} [Decidable p] [Decidable q] (h : decide p = decide q) : p ↔ q := by
  by_cases hp : p <;> by_cases hq : q <;> simp_all

theorem lab_eq_iff {n : ℕ} {A B A' B' : Finset (Fin n)} {x y : Fin n} (h : lab A' B' y = lab A B x) :
    (y ∈ A' ↔ x ∈ A) ∧ (y ∈ B' ↔ x ∈ B) := by
  unfold lab at h
  rw [Prod.mk.injEq] at h
  exact ⟨iff_of_decide h.1, iff_of_decide h.2⟩

theorem fib_tt {n : ℕ} (A B : Finset (Fin n)) :
    Fintype.card {x // lab A B x = (true, true)} = (A ∩ B).card := by
  rw [Fintype.card_subtype]
  congr 1
  ext x
  simp [lab]

theorem fib_tf {n : ℕ} (A B : Finset (Fin n)) :
    Fintype.card {x // lab A B x = (true, false)} = (A \ B).card := by
  rw [Fintype.card_subtype]
  congr 1
  ext x
  simp [lab]

theorem fib_ft {n : ℕ} (A B : Finset (Fin n)) :
    Fintype.card {x // lab A B x = (false, true)} = (B \ A).card := by
  rw [Fintype.card_subtype]
  congr 1
  ext x
  simp [lab]
  tauto

theorem fib_ff {n : ℕ} (A B : Finset (Fin n)) :
    Fintype.card {x // lab A B x = (false, false)} = ((A ∪ B)ᶜ).card := by
  rw [Fintype.card_subtype]
  congr 1
  ext x
  simp [lab]

theorem exists_perm_of_rsz {n : ℕ} {A B A' B' : Finset (Fin n)} (h : rsz (A, B) = rsz (A', B')) :
    ∃ σ : Equiv.Perm (Fin n), A.map σ.toEmbedding = A' ∧ B.map σ.toEmbedding = B' := by
  simp only [rsz, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hU : (A ∪ B).card = (A' ∪ B').card := by
    have k1 := Finset.card_union_add_card_inter A B
    have k2 := Finset.card_union_add_card_inter A' B'
    have k3 := Finset.card_sdiff_add_card_inter A B
    have k4 := Finset.card_sdiff_add_card_inter A' B'
    have k5 := Finset.card_sdiff_add_card_inter B A
    have k6 := Finset.card_sdiff_add_card_inter B' A'
    rw [Finset.inter_comm B A] at k5
    rw [Finset.inter_comm B' A'] at k6
    omega
  have hf : ∀ c : Bool × Bool,
      Fintype.card {x // lab A B x = c} = Fintype.card {x // lab A' B' x = c} := by
    intro c
    rcases c with ⟨_ | _, _ | _⟩
    · rw [fib_ff, fib_ff, Finset.card_compl, Finset.card_compl, hU]
    · rw [fib_ft, fib_ft, h3]
    · rw [fib_tf, fib_tf, h2]
    · rw [fib_tt, fib_tt, h1]
  let e : ∀ c : Bool × Bool, {x // lab A B x = c} ≃ {x // lab A' B' x = c} :=
    fun c => Fintype.equivOfCardEq (hf c)
  have key : ∀ x, lab A' B' (Equiv.ofFiberEquiv e x) = lab A B x := Equiv.ofFiberEquiv_map e
  refine ⟨Equiv.ofFiberEquiv e, ?_, ?_⟩
  · ext y
    rw [Finset.mem_map_equiv]
    have k := lab_eq_iff (key ((Equiv.ofFiberEquiv e).symm y))
    rw [Equiv.apply_symm_apply] at k
    exact k.1.symm
  · ext y
    rw [Finset.mem_map_equiv]
    have k := lab_eq_iff (key ((Equiv.ofFiberEquiv e).symm y))
    rw [Equiv.apply_symm_apply] at k
    exact k.2.symm

theorem orb_eq_of_rsz {n : ℕ} {p q : Finset (Fin n) × Finset (Fin n)} (h : rsz p = rsz q) :
    orb n (pr p) = orb n (pr q) := by
  obtain ⟨A, B⟩ := p
  obtain ⟨A', B'⟩ := q
  obtain ⟨σ, h1, h2⟩ := exists_perm_of_rsz h
  rw [orb_eq_iff]
  exact ⟨σ, by simp only [pr, act_pr, h1, h2]⟩

theorem sys_eq (n : ℕ) : Finset.univ.filter (IsSys n 2) = (Good n).image pr := by
  ext S
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Good, Prod.exists,
    IsSys]
  constructor
  · rintro ⟨hne, hc, hs⟩
    obtain ⟨A, B, hAB, rfl⟩ := Finset.card_eq_two.1 hc
    rw [Finset.sum_pair hAB] at hs
    have hA : A.Nonempty := hne A (by simp)
    have hB : B.Nonempty := hne B (by simp)
    rcases le_total A.card B.card with hle | hle
    · exact ⟨A, B, ⟨hA, hB, hAB, hs, hle⟩, rfl⟩
    · exact ⟨B, A, ⟨hB, hA, hAB.symm, by omega, hle⟩, Finset.pair_comm B A⟩
  · rintro ⟨A, B, ⟨hA, hB, hAB, hs, _⟩, rfl⟩
    refine ⟨?_, Finset.card_pair hAB, ?_⟩
    · intro s hs'
      simp only [pr, Finset.mem_insert, Finset.mem_singleton] at hs'
      rcases hs' with rfl | rfl
      · exact hA
      · exact hB
    · simp only [pr]
      rw [Finset.sum_pair hAB]
      exact hs

theorem T_two_eq (n : ℕ) : T n 2 = ((Good n).image rsz).card := by
  unfold T
  rw [sys_eq, Finset.image_image]
  apply card_image_congr
  intro p hp q hq
  exact ⟨rsz_eq_of_orb hp hq, orb_eq_of_rsz⟩

/-- The admissible region-size triples `(c, a, b)`. -/
def Q (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (n + 1)) ×ˢ ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1)))).filter
    (fun t => t.2.1 ≤ t.2.2 ∧ t.2.1 + t.2.2 + 2 * t.1 = n ∧ 1 ≤ t.2.1 + t.1 ∧ 1 ≤ t.2.1 + t.2.2)

theorem mem_Q (n c a b : ℕ) :
    (c, a, b) ∈ Q n ↔ (a ≤ b ∧ a + b + 2 * c = n ∧ 1 ≤ a + c ∧ 1 ≤ a + b) := by
  simp only [Q, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨by omega, by omega, by omega⟩, h1, h2, h3, h4⟩

theorem card_Iv (n lo hi : ℕ) (h : hi ≤ n) :
    (Finset.univ.filter (fun x : Fin n => lo ≤ x.val ∧ x.val < hi)).card = hi - lo := by
  rw [← Finset.card_map Fin.valEmbedding, ← Nat.card_Ico lo hi]
  congr 1
  ext k
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
    Finset.mem_Ico]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hk
    exact ⟨⟨k, by omega⟩, hk, rfl⟩

theorem realize (n c a b : ℕ) (h1 : a ≤ b) (h2 : a + b + 2 * c = n) (h3 : 1 ≤ a + c)
    (h4 : 1 ≤ a + b) :
    ∃ A B : Finset (Fin n), (A.Nonempty ∧ B.Nonempty ∧ A ≠ B ∧ A.card + B.card = n ∧
      A.card ≤ B.card) ∧ rsz (A, B) = (c, a, b) := by
  obtain ⟨A, hA⟩ : ∃ A : Finset (Fin n), A = Finset.univ.filter (fun x : Fin n => x.val < a + c) :=
    ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Finset (Fin n),
      B = Finset.univ.filter (fun x : Fin n => a ≤ x.val ∧ x.val < a + c + b) := ⟨_, rfl⟩
  have eI : A ∩ B = Finset.univ.filter (fun x : Fin n => a ≤ x.val ∧ x.val < a + c) := by
    ext x
    simp only [hA, hB, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro h <;> omega
  have eD1 : A \ B = Finset.univ.filter (fun x : Fin n => 0 ≤ x.val ∧ x.val < a) := by
    ext x
    simp only [hA, hB, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro h <;> omega
  have eD2 : B \ A = Finset.univ.filter (fun x : Fin n => a + c ≤ x.val ∧ x.val < a + c + b) := by
    ext x
    simp only [hA, hB, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro h <;> omega
  have cI : (A ∩ B).card = c := by
    have := card_Iv n a (a + c) (by omega)
    rw [← eI] at this
    omega
  have cD1 : (A \ B).card = a := by
    have := card_Iv n 0 a (by omega)
    rw [← eD1] at this
    omega
  have cD2 : (B \ A).card = b := by
    have := card_Iv n (a + c) (a + c + b) (by omega)
    rw [← eD2] at this
    omega
  have k1 := Finset.card_sdiff_add_card_inter A B
  have k2 := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at k2
  refine ⟨A, B, ⟨Finset.card_pos.1 (by omega), Finset.card_pos.1 (by omega), ?_, by omega,
    by omega⟩, ?_⟩
  · intro hAB
    rw [hAB, Finset.sdiff_self, Finset.card_empty] at cD1 cD2
    omega
  · simp only [rsz, cI, cD1, cD2]

theorem image_rsz (n : ℕ) : (Good n).image rsz = Q n := by
  ext ⟨c, a, b⟩
  rw [mem_Q]
  simp only [Finset.mem_image, Good, Finset.mem_filter, Finset.mem_univ, true_and, Prod.exists]
  constructor
  · rintro ⟨A, B, ⟨hA, hB, hAB, hs, hle⟩, he⟩
    simp only [rsz, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    have k1 := Finset.card_sdiff_add_card_inter A B
    have k2 := Finset.card_sdiff_add_card_inter B A
    rw [Finset.inter_comm B A] at k2
    have hA' := Finset.card_pos.2 hA
    have hab : 1 ≤ (A \ B).card + (B \ A).card := by
      by_contra hc
      apply hAB
      have e1 : A \ B = ∅ := Finset.card_eq_zero.1 (by omega)
      have e2 : B \ A = ∅ := Finset.card_eq_zero.1 (by omega)
      exact Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.1 e1)
        (Finset.sdiff_eq_empty_iff_subset.1 e2)
    exact ⟨by omega, by omega, by omega, hab⟩
  · rintro ⟨h1, h2, h3, h4⟩
    obtain ⟨A, B, hg, he⟩ := realize n c a b h1 h2 h3 h4
    exact ⟨A, B, hg, he⟩

theorem Q_filter_not (n : ℕ) :
    (Q (n + 2)).filter (fun t : ℕ × ℕ × ℕ => ¬ (t.1 = 0 ∨ (t.1 = 1 ∧ t.2.1 = 0))) =
      (Q n).image (fun t : ℕ × ℕ × ℕ => (t.1 + 1, t.2.1, t.2.2)) := by
  ext ⟨c, a, b⟩
  simp only [Finset.mem_filter, Finset.mem_image, mem_Q, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
    exact ⟨c - 1, a, b, ⟨h1, by omega, by omega, h4⟩, by omega, rfl, rfl⟩
  · rintro ⟨c', a', b', ⟨h1, h2, h3, h4⟩, rfl, rfl, rfl⟩
    exact ⟨⟨h1, by omega, by omega, h4⟩, by omega⟩

theorem Q_filter (n : ℕ) (hn : 1 ≤ n) :
    (Q (n + 2)).filter (fun t : ℕ × ℕ × ℕ => t.1 = 0 ∨ (t.1 = 1 ∧ t.2.1 = 0)) =
      insert (1, 0, n) ((Finset.Icc 1 ((n + 2) / 2)).image (fun a : ℕ => ((0 : ℕ), a, n + 2 - a))) := by
  ext ⟨c, a, b⟩
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_image, Finset.mem_Icc, mem_Q,
    Prod.mk.injEq]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
    rcases h5 with h5 | ⟨h5, h6⟩
    · right
      exact ⟨a, ⟨by omega, by omega⟩, by omega, rfl, by omega⟩
    · left
      exact ⟨h5, h6, by omega⟩
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨x, ⟨hx1, hx2⟩, rfl, rfl, rfl⟩)
    · exact ⟨⟨by omega, by omega, by omega, by omega⟩, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨⟨by omega, by omega, by omega, by omega⟩, Or.inl rfl⟩

theorem Q_card_step (n : ℕ) (hn : 1 ≤ n) :
    (Q (n + 2)).card = (Q n).card + (n + 2) / 2 + 1 := by
  have inj1 : Function.Injective (fun t : ℕ × ℕ × ℕ => (t.1 + 1, t.2.1, t.2.2)) := by
    intro x y h
    have h1 : x.1 + 1 = y.1 + 1 := congrArg Prod.fst h
    have h2 : x.2.1 = y.2.1 := congrArg (fun t => t.2.1) h
    have h3 : x.2.2 = y.2.2 := congrArg (fun t => t.2.2) h
    exact Prod.ext (by omega) (Prod.ext h2 h3)
  have inj2 : Function.Injective (fun a : ℕ => ((0 : ℕ), a, n + 2 - a)) := by
    intro x y h
    exact congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) h
  have hnm : (1, 0, n) ∉ (Finset.Icc 1 ((n + 2) / 2)).image (fun a : ℕ => ((0 : ℕ), a, n + 2 - a)) := by
    intro hm
    rw [Finset.mem_image] at hm
    obtain ⟨x, _, hx⟩ := hm
    have h0 : (0 : ℕ) = 1 := congrArg Prod.fst hx
    omega
  have hsplit := Finset.card_filter_add_card_filter_not (s := Q (n + 2))
    (fun t : ℕ × ℕ × ℕ => t.1 = 0 ∨ (t.1 = 1 ∧ t.2.1 = 0))
  rw [Q_filter n hn, Q_filter_not n, Finset.card_insert_of_notMem hnm,
    Finset.card_image_of_injective _ inj2, Finset.card_image_of_injective _ inj1,
    Nat.card_Icc] at hsplit
  omega

theorem Q_two : Q 2 = {(0, 1, 1)} := by
  ext ⟨c, a, b⟩
  rw [mem_Q]
  simp only [Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · intro h
    omega
  · intro h
    omega

theorem Q_three : Q 3 = {(0, 1, 2), (1, 0, 1)} := by
  ext ⟨c, a, b⟩
  rw [mem_Q]
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · intro h
    omega
  · intro h
    omega

theorem A_step (k : ℕ) : A101881 (k + 2) = A101881 k + k / 2 + 3 := by
  unfold A101881
  rw [show (k + 2) / 2 = k / 2 + 1 by omega, show (k + 2) % 2 = k % 2 by omega]
  have hs : st (k / 2 + 1) = st (k / 2) + k / 2 + 3 := rfl
  rw [hs]
  omega

theorem Q_card (m : ℕ) :
    (Q (m + 2)).card = A101881 m ∧ (Q (m + 3)).card = A101881 (m + 1) := by
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · show (Q 2).card = A101881 0
      rw [Q_two]
      decide
    · show (Q 3).card = A101881 1
      rw [Q_three]
      decide
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have hstep := Q_card_step (k + 2) (by omega)
    have hA := A_step k
    have e : k + 1 + 1 = k + 2 := by omega
    rw [show k + 1 + 3 = k + 2 + 2 by omega, hstep, ih.1, e, hA]
    omega

theorem main_proof (n : ℕ) (hn : 2 ≤ n) : T n 2 = A101881 (n - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [T_two_eq, image_rsz, Nat.add_sub_cancel]
  exact (Q_card m).1

end OMA.A368096Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a368096.main := by
  intro n hn
  exact OMA.A368096Proof.main_proof n hn

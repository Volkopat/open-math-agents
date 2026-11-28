import FormalConjectures.Other.EquationalTheories_677_255

/-!
A congruence reduction of the finite E677 -> E255 problem.

H1 is the genuinely nonlinear congruence-simple case. H2 is extension closure along a proper
congruence, assuming E255 in the strictly smaller quotient. The quotient is
constructed explicitly and the cardinal decrease is proved, rather than
assuming a minimal counterexample. The additional lemmas show that each
left translation, and its restriction between congruence classes, is a
bijection. We also prove the additively separated case and its extension obstruction
(blueprint Lemmas 13.3 and 13.4). Thus the outstanding extension problem can
focus on transport that cannot be separated additively in the two inputs.

These are unresolved hypotheses, not a proof of the original implication.
Basic row invertibility follows the Equational Theories Project blueprint,
Chapter 13, Lemmas 13.1, 13.3 and 13.4:
https://teorth.github.io/equational_theories/blueprint/677-chapter.html
No unproved upstream theorem is used.
-/

namespace OMA.R_EquationalTheories_677_255_Finite_Equation677_implies_Equation255_R1

open EquationalTheories_677_255

/-- The finite congruence-simple case. -/
def H1 : Prop :=
  ∀ (G : Type) [Magma G] [Finite G], Equation677 G →
    (∀ r : Setoid G,
      (∀ a b c d, r.r a c → r.r b d → r.r (a ◇ b) (c ◇ d)) →
      r = ⊥ ∨ r = ⊤) →
    ¬ (∀ a b x : G, a ◇ x = b ◇ x → ∀ z, a ◇ z = b ◇ z) → Equation255 G

/-- Lift E255 from a proper quotient. Both indiscrete and equality
congruences are excluded; neither can yield the induction step. -/
def H2 : Prop :=
  ∀ (G : Type) [Magma G] [Finite G], Equation677 G →
    ∀ r : Setoid G,
      (∀ a b c d, r.r a c → r.r b d → r.r (a ◇ b) (c ◇ d)) →
      r ≠ ⊥ → r ≠ ⊤ →
      (∀ x : G, r.r x (((x ◇ x) ◇ x) ◇ x)) → Equation255 G

lemma left_surjective {G : Type} [Magma G] (h : Equation677 G) (y : G) :
    Function.Surjective (fun x : G => y ◇ x) := by
  intro x
  exact ⟨x ◇ ((y ◇ x) ◇ y), (h x y).symm⟩

lemma left_injective {G : Type} [Magma G] [Finite G]
    (h : Equation677 G) (y : G) :
    Function.Injective (fun x : G => y ◇ x) :=
  (Finite.injective_iff_surjective).mpr (left_surjective h y)

/-- The inverse is an explicit term, so congruences preserve left division. -/
lemma inverse_left {G : Type} [Magma G] [Finite G]
    (h : Equation677 G) (y x : G) :
    (y ◇ x) ◇ ((y ◇ (y ◇ x)) ◇ y) = x := by
  apply left_injective h y
  exact (h (y ◇ x) y).symm

/-- A column's diagonal entry has at most one preimage; this is the local
obstruction behind the extension step. -/
lemma diagonal_preimage {G : Type} [Magma G] [Finite G]
    (h : Equation677 G) {x y : G} (hy : y ◇ x = x) :
    y = (x ◇ x) ◇ x := by
  have hx : x ◇ (x ◇ y) = x := by
    have hh := h x y
    rw [hy] at hh
    exact left_injective h y (hh.symm.trans hy.symm)
  apply left_injective h x
  apply left_injective h x
  exact hx.trans (h x x)

/-- Every row transports a congruence class bijectively to its image class.
The displayed formula gives the inverse on the whole image class. -/
lemma fibre_transport {G : Type} [Magma G] [Finite G]
    (h : Equation677 G) (r : Setoid G)
    (hc : ∀ a b c d, r.r a c → r.r b d → r.r (a ◇ b) (c ◇ d))
    (y a : G) :
    Function.Bijective
      (fun x : {x : G // r.r x a} =>
        (⟨y ◇ x.val, hc y x.val y a (r.refl y) x.property⟩ :
          {z : G // r.r z (y ◇ a)})) := by
  constructor
  · intro x z hxz
    exact Subtype.ext (left_injective h y (congrArg Subtype.val hxz))
  · intro z
    let t : G := z.val ◇ ((y ◇ z.val) ◇ y)
    have ht : r.r t a := by
      have hh : r.r t ((y ◇ a) ◇ ((y ◇ (y ◇ a)) ◇ y)) :=
        hc _ _ _ _ z.property
          (hc _ _ _ _ (hc _ _ _ _ (r.refl y) z.property) (r.refl y))
      simpa only [inverse_left h y a] using hh
    refine ⟨⟨t, ht⟩, Subtype.ext ?_⟩
    exact (h z.val y).symm

/-- Distinct elements cannot index identical rows. -/
lemma row_faithful {G : Type} [Magma G] [Finite G]
    (h : Equation677 G) {y z : G} (hr : ∀ t, y ◇ t = z ◇ t) : y = z := by
  have he := (h y y).symm.trans (h y z)
  rw [← hr (y ◇ ((z ◇ y) ◇ z)), ← hr y] at he
  exact left_injective h (y ◇ y) (left_injective h y (left_injective h y he))

/-- If meeting rows coincide, every column is bijective and E255 follows.
This isolates the genuinely nonlinear case of H1. -/
lemma equation255_of_row_separation {G : Type} [Magma G] [Finite G]
    (h : Equation677 G)
    (hs : ∀ a b x : G, a ◇ x = b ◇ x → ∀ z, a ◇ z = b ◇ z) :
    Equation255 G := by
  intro x
  have hi : Function.Injective (fun y : G => y ◇ x) := by
    intro a b hab
    exact row_faithful h (hs a b x hab)
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hi) x
  rw [diagonal_preimage h hy] at hy
  exact hy.symm

/-- Additively separated finite models cannot be counterexamples. The
coordinate maps need not be homomorphisms; the affine case is included. -/
lemma equation255_of_separated_sum {G : Type} [AddCommGroup G] [Magma G] [Finite G]
    (h : Equation677 G) (α β : G → G) (c : G)
    (hl : ∀ x y : G, x ◇ y = α x + β y + c) : Equation255 G := by
  apply equation255_of_row_separation h
  intro a b x hab z
  simp only [hl] at hab ⊢
  have he : α a = α b := add_right_cancel (add_right_cancel hab)
  rw [he]

/-- Additively separated extensions of solved finite bases cannot be
counterexamples. The coordinate maps are arbitrary functions. This extends
the affine obstruction of blueprint Lemma 13.4 beyond homomorphisms. -/
lemma equation255_of_separated_extension
    {G M : Type} [Magma G] [Finite G] [AddCommGroup M] [Finite M]
    [Magma (G × M)] (h : Equation677 (G × M)) (hg : Equation255 G)
    (A B : G → G → M → M) (c : G → G → M)
    (hl : ∀ p q : G × M, p ◇ q =
      (p.1 ◇ q.1, A p.1 q.1 p.2 + B p.1 q.1 q.2 + c p.1 q.1)) :
    Equation255 (G × M) := by
  have hfst (p q : G × M) : (p ◇ q).1 = p.1 ◇ q.1 := by rw [hl]
  have hg677 : Equation677 G := by
    intro x y
    have he := congrArg Prod.fst (h (x, 0) (y, 0))
    simpa only [hfst] using he
  intro q
  let a : G := (q.1 ◇ q.1) ◇ q.1
  have ha : a ◇ q.1 = q.1 := (hg q.1).symm
  have ht : q.1 ◇ (q.1 ◇ a) = q.1 := (hg677 q.1 q.1).symm
  have hinj : Function.Injective (A a q.1) := by
    intro s t hst
    let p : G × M := (a, s)
    let p' : G × M := (a, t)
    have hrow : ∀ v : G × M, v.1 = q.1 → p ◇ v = p' ◇ v := by
      intro v hv
      simp only [hl, p, p', hv, hst]
    have hpq : p ◇ q = p' ◇ q := hrow q rfl
    have hv : (q ◇ ((p' ◇ q) ◇ p')).1 = q.1 := by
      simp only [hfst, p', ha, ht]
    have he := (h q p).symm.trans (h q p')
    rw [← hrow (q ◇ ((p' ◇ q) ◇ p')) hv, ← hpq] at he
    have he' : p = p' := left_injective h (p ◇ q)
      (left_injective h q (left_injective h p he))
    exact congrArg Prod.snd he'
  obtain ⟨s, hs⟩ := (Finite.injective_iff_surjective.mp hinj)
    (q.2 - B a q.1 q.2 - c a q.1)
  have hp : (a, s) ◇ q = q := by
    rw [hl]
    apply Prod.ext
    · exact ha
    · dsimp
      rw [hs]
      abel
  have he := diagonal_preimage h hp
  exact (congrArg (fun z : G × M => z ◇ q) he).symm.trans hp |>.symm

lemma quotient_card_lt {G : Type} [Fintype G] (r : Setoid G)
    [Fintype (Quotient r)] (hr : r ≠ ⊥) :
    Fintype.card (Quotient r) < Fintype.card G := by
  have hs : Function.Surjective (Quotient.mk r) := Quotient.mk_surjective
  have hn : ¬ Function.Injective (Quotient.mk r) := by
    intro hi
    apply hr
    apply Setoid.ext
    intro a b
    constructor
    · intro hab
      exact hi (Quotient.sound hab)
    · intro hab
      subst b
      exact r.refl a
  have hle := Fintype.card_le_of_surjective (Quotient.mk r) hs
  by_contra hlt
  have heq : Fintype.card G = Fintype.card (Quotient r) := by omega
  exact hn ((Fintype.bijective_iff_surjective_and_card _).2 ⟨hs, heq⟩).injective

lemma by_card (h1 : H1) (h2 : H2) (k : ℕ) :
    ∀ (G : Type) [Magma G] [Fintype G], Fintype.card G = k →
      Equation677 G → Equation255 G := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro G inst fintype hcard h677
    by_cases hsep : ∀ a b x : G, a ◇ x = b ◇ x → ∀ z, a ◇ z = b ◇ z
    · exact equation255_of_row_separation h677 hsep
    by_cases hs : ∀ r : Setoid G,
        (∀ a b c d, r.r a c → r.r b d → r.r (a ◇ b) (c ◇ d)) →
        r = ⊥ ∨ r = ⊤
    · exact h1 G h677 hs hsep
    push Not at hs
    obtain ⟨r, hc, hb, ht⟩ := hs
    let : Magma (Quotient r) := ⟨fun x y =>
      Quotient.liftOn₂ x y (fun a b => Quotient.mk r (a ◇ b))
        (fun a b c d hac hbd => Quotient.sound (hc a b c d hac hbd))⟩
    let : Fintype (Quotient r) := Fintype.ofFinite _
    have hq677 : Equation677 (Quotient r) := by
      intro x y
      induction x using Quotient.inductionOn with
      | h x =>
        induction y using Quotient.inductionOn with
        | h y => exact congrArg (Quotient.mk r) (h677 x y)
    have hlt : Fintype.card (Quotient r) < k := by
      rw [← hcard]
      exact quotient_card_lt r hb
    have hq255 : Equation255 (Quotient r) :=
      ih (Fintype.card (Quotient r)) hlt (Quotient r) rfl hq677
    apply h2 G h677 r hc hb ht
    intro x
    exact Quotient.exact (hq255 (Quotient.mk r x))

theorem main : H1 → H2 →
    type_of% @EquationalTheories_677_255.Finite.Equation677_implies_Equation255 := by
  intro h1 h2 G inst hf h677
  let : Finite G := hf
  let : Fintype G := Fintype.ofFinite G
  exact by_card h1 h2 (Fintype.card G) G rfl h677

end OMA.R_EquationalTheories_677_255_Finite_Equation677_implies_Equation255_R1

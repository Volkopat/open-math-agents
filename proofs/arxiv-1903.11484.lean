import OMAStatements.S_arxiv_1903_11484

namespace OMA.P_arxiv_1903_11484

open OMA.S_arxiv_1903_11484 SimpleGraph

/-! ### Part 1: Basic properties of `ClosedAdj` and `CopWinFrom` -/

private lemma closedAdj_refl {V : Type*} (G : SimpleGraph V) (u : V) : ClosedAdj G u u :=
  Or.inl rfl

private lemma closedAdj_symm {V : Type*} {G : SimpleGraph V} {u v : V} (h : ClosedAdj G u v) :
    ClosedAdj G v u :=
  h.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)

private lemma copWinFrom_symm {V : Type*} {G : SimpleGraph V} {c₁ c₂ r : V}
    (h : CopWinFrom G (c₁, c₂) r) : CopWinFrom G (c₂, c₁) r := by
  generalize hpair : (c₁, c₂) = p at h
  induction h generalizing c₁ c₂ with
  | caught hc =>
    cases hpair
    exact CopWinFrom.caught hc.symm
  | capture hm₁ hm₂ hcap =>
    cases hpair
    exact CopWinFrom.capture hm₂ hm₁ hcap.symm
  | step hm₁ hm₂ hnext ih =>
    cases hpair
    exact CopWinFrom.step hm₂ hm₁ fun r' hr' => ih r' hr' rfl

private lemma copWinFrom_of_closedAdj {V : Type*} {G : SimpleGraph V} {c₁ c₂ r : V}
    (h : ClosedAdj G c₁ r ∨ ClosedAdj G c₂ r) : CopWinFrom G (c₁, c₂) r := by
  rcases h with h1 | h2
  · exact CopWinFrom.capture h1 (closedAdj_refl G c₂) (Or.inl rfl)
  · exact CopWinFrom.capture (closedAdj_refl G c₁) h2 (Or.inr rfl)

private lemma copWinFrom_of_trap {V : Type*} {G : SimpleGraph V} {u x₁ x₂ : V}
    (htrap : ∀ w, ClosedAdj G u w → ClosedAdj G x₁ w ∨ ClosedAdj G x₂ w) :
    ∀ r', ClosedAdj G u r' → CopWinFrom G (x₁, x₂) r' :=
  fun r' hr' => copWinFrom_of_closedAdj (htrap r' hr')

private lemma copWinFrom_walk_to_dominated {V : Type*} {G : SimpleGraph V}
    {u v : V} (hdom : ∀ w, G.Adj v w → ClosedAdj G u w) :
    ∀ {x : V} (_ : G.Walk x v), CopWinFrom G (u, x) v
  | _, .nil => CopWinFrom.caught (Or.inr rfl)
  | x, .cons hadj q => by
    refine CopWinFrom.step (closedAdj_refl G u) (Or.inr hadj) fun r' hr' => ?_
    rcases hr' with rfl | hadjv
    · exact copWinFrom_walk_to_dominated hdom q
    · exact copWinFrom_of_closedAdj (Or.inl (hdom r' hadjv))

private lemma copWinFrom_of_dominated_cop {V : Type*} {G : SimpleGraph V} (hconn : G.Connected)
    {u v x : V} (hdom : ∀ w, G.Adj v w → ClosedAdj G u w) :
    CopWinFrom G (u, x) v := by
  obtain ⟨p⟩ := hconn x v
  exact copWinFrom_walk_to_dominated hdom p

private lemma shadow_win {V : Type*} {G : SimpleGraph V} (hconn : G.Connected)
    {u v : V} (huv : u ≠ v) (hdom : ∀ w, G.Adj v w → ClosedAdj G u w)
    (hsub : CopNumberLeTwo (G.induce {x : V | x ≠ v})) : CopNumberLeTwo G := by
  let S : Set V := {x : V | x ≠ v}
  let G' := G.induce S
  let u' : S := ⟨u, huv⟩
  have hlift : ∀ {c₁ c₂ r : S}, CopWinFrom G' (c₁, c₂) r →
      CopWinFrom G (c₁.val, c₂.val) r.val ∧ (r = u' → CopWinFrom G (c₁.val, c₂.val) v) := by
    intro c₁ c₂ r h
    generalize hp : (c₁, c₂) = pair at h
    induction h generalizing c₁ c₂ with
    | caught hc =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
      refine ⟨CopWinFrom.caught (hc.imp (congrArg Subtype.val) (congrArg Subtype.val)), ?_⟩
      intro hr
      subst hr
      rcases hc with rfl | rfl
      · exact copWinFrom_of_dominated_cop hconn hdom
      · exact copWinFrom_symm (copWinFrom_of_dominated_cop hconn hdom)
    | @capture a b r0 c₁' c₂' hm₁ hm₂ hcap =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
      have hm₁' : ClosedAdj G c₁.val c₁'.val := hm₁.imp (congrArg Subtype.val) id
      have hm₂' : ClosedAdj G c₂.val c₂'.val := hm₂.imp (congrArg Subtype.val) id
      constructor
      · exact CopWinFrom.capture hm₁' hm₂' (hcap.imp (congrArg Subtype.val) (congrArg Subtype.val))
      · intro hr
        subst hr
        refine CopWinFrom.step hm₁' hm₂' fun r' hr' => ?_
        rcases hcap with h1 | h2
        · rcases hr' with rfl | hadjv
          · rw [h1]; exact copWinFrom_of_dominated_cop hconn hdom
          · rw [h1]; exact copWinFrom_of_closedAdj (Or.inl (hdom r' hadjv))
        · rcases hr' with rfl | hadjv
          · rw [h2]; exact copWinFrom_symm (copWinFrom_of_dominated_cop hconn hdom)
          · rw [h2]; exact copWinFrom_of_closedAdj (Or.inr (hdom r' hadjv))
    | @step a b r0 c₁' c₂' hm₁ hm₂ hnext ih =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
      have hm₁' : ClosedAdj G c₁.val c₁'.val := hm₁.imp (congrArg Subtype.val) id
      have hm₂' : ClosedAdj G c₂.val c₂'.val := hm₂.imp (congrArg Subtype.val) id
      constructor
      · refine CopWinFrom.step hm₁' hm₂' fun r' hr' => ?_
        by_cases hrv : r' = v
        · subst r'
          have hadj : G.Adj v r0.val := by
            rcases hr' with heq | hadj
            · exact absurd heq r0.property
            · exact hadj.symm
          have hcu : ClosedAdj G' r0 u' := by
            rcases hdom r0.val hadj with heq | hadju
            · exact Or.inl (Subtype.ext heq.symm)
            · exact Or.inr hadju.symm
          exact (ih u' hcu rfl).2 rfl
        · have hcr : ClosedAdj G' r0 ⟨r', hrv⟩ :=
            hr'.imp (fun heq => Subtype.ext heq) id
          exact (ih ⟨r', hrv⟩ hcr rfl).1
      · intro hr
        subst hr
        refine CopWinFrom.step hm₁' hm₂' fun r' hr' => ?_
        rcases hr' with rfl | hadjv
        · exact (ih u' (closedAdj_refl G' u') rfl).2 rfl
        · have hrv : r' ≠ v := hadjv.ne.symm
          have hcu : ClosedAdj G' u' ⟨r', hrv⟩ :=
            (hdom r' hadjv).imp (fun heq => Subtype.ext heq) id
          exact (ih ⟨r', hrv⟩ hcu rfl).1
  obtain ⟨c₁, c₂, hwin⟩ := hsub
  refine ⟨c₁.val, c₂.val, fun r => ?_⟩
  by_cases hrv : r = v
  · subst hrv
    exact (hlift (hwin u')).2 rfl
  · exact (hlift (hwin ⟨r, hrv⟩)).1

/-! ### Part 2: Structural lemmas for `2K_2`-free graphs -/

private lemma isTwoK2Free_induce {V : Type*} {G : SimpleGraph V} (h2k2 : IsTwoK2Free G)
    (S : Set V) : IsTwoK2Free (G.induce S) := by
  intro a b c d hab hcd hac had hbc hbd
  exact h2k2 a.val b.val c.val d.val hab hcd
    (fun h => hac (Subtype.ext h)) (fun h => had (Subtype.ext h))
    (fun h => hbc (Subtype.ext h)) (fun h => hbd (Subtype.ext h))

private lemma cantmove {V : Type*} {G : SimpleGraph V} (h2k2 : IsTwoK2Free G)
    {u v w x : V} (hv : ¬ ClosedAdj G u v) (hw : ¬ ClosedAdj G u w)
    (hvw : G.Adj v w) (hux : G.Adj u x) : G.Adj x v ∨ G.Adj x w := by
  have huv : u ≠ v := fun h => hv (Or.inl h)
  have huw : u ≠ w := fun h => hw (Or.inl h)
  have hxv : x ≠ v := fun h => hv (Or.inr (h ▸ hux))
  have hxw : x ≠ w := fun h => hw (Or.inr (h ▸ hux))
  rcases h2k2 u x v w hux hvw huv huw hxv hxw with h1 | h2 | h3 | h4
  · exact absurd (Or.inr h1) hv
  · exact absurd (Or.inr h2) hw
  · exact Or.inl h3
  · exact Or.inr h4

private lemma reachable_of_edges {V : Type*} {G : SimpleGraph V} (h2k2 : IsTwoK2Free G)
    {a b c d : V} (hab : G.Adj a b) (hcd : G.Adj c d) : G.Reachable a c := by
  by_cases hac : a = c
  · subst hac; exact Reachable.refl _
  by_cases had : a = d
  · subst had; exact hcd.symm.reachable
  by_cases hbc : b = c
  · subst hbc; exact hab.reachable
  by_cases hbd : b = d
  · subst hbd; exact hab.reachable.trans hcd.symm.reachable
  rcases h2k2 a b c d hab hcd hac had hbc hbd with h1 | h2 | h3 | h4
  · exact h1.reachable
  · exact h2.reachable.trans hcd.symm.reachable
  · exact hab.reachable.trans h3.reachable
  · exact hab.reachable.trans (h4.reachable.trans hcd.symm.reachable)

private lemma connected_of_no_isolated {V : Type*} [Nonempty V] {G : SimpleGraph V}
    (h2k2 : IsTwoK2Free G) (hnoiso : ∀ v : V, ∃ w : V, G.Adj v w) : G.Connected := by
  constructor
  intro u v
  obtain ⟨u', hu'⟩ := hnoiso u
  obtain ⟨v', hv'⟩ := hnoiso v
  exact reachable_of_edges h2k2 hu' hv'

private lemma exists_walk_length_le_three {V : Type*} {G : SimpleGraph V}
    (h2k2 : IsTwoK2Free G) (hconn : G.Connected) (x y : V) :
    ∃ p : G.Walk x y, p.length ≤ 3 := by
  classical
  have hex : ∃ n : ℕ, ∃ p : G.Walk x y, p.length = n := by
    obtain ⟨p⟩ := hconn x y
    exact ⟨p.length, p, rfl⟩
  let n := Nat.find hex
  obtain ⟨p, hp⟩ := Nat.find_spec hex
  have hmin : ∀ (q : G.Walk x y), n ≤ q.length := fun q => Nat.find_min' hex ⟨q, rfl⟩
  by_contra hgt
  push Not at hgt
  have hn4 : 4 ≤ n := by
    have : 3 < p.length := hgt p
    omega
  -- Unpack first 4 edges of p: x - a - b - c - d ... y
  cases p with
  | nil => simp at hp; omega
  | @cons _ a _ hxa p1 =>
    cases p1 with
    | nil => simp at hp; omega
    | @cons _ b _ hab p2 =>
      cases p2 with
      | nil => simp at hp; omega
      | @cons _ c _ hbc p3 =>
        cases p3 with
        | nil => simp at hp; omega
        | @cons _ d _ hcd p4 =>
          have hlen_p4 : p4.length + 4 = n := by simp [Walk.length_cons] at hp; omega
          have hxc : x ≠ c := by
            intro h; subst h
            have hq : (Walk.cons hcd p4).length < n := by simp [Walk.length_cons]; omega
            exact absurd (hmin (Walk.cons hcd p4)) (by omega)
          have hxd : x ≠ d := by
            intro h; subst h
            exact absurd (hmin p4) (by omega)
          have hac : a ≠ c := by
            intro h; subst h
            have hq : (Walk.cons hxa (Walk.cons hcd p4)).length < n := by simp [Walk.length_cons]; omega
            exact absurd (hmin (Walk.cons hxa (Walk.cons hcd p4))) (by omega)
          have had : a ≠ d := by
            intro h; subst h
            have hq : (Walk.cons hxa p4).length < n := by simp [Walk.length_cons]; omega
            exact absurd (hmin (Walk.cons hxa p4)) (by omega)
          rcases h2k2 x a c d hxa hcd hxc hxd hac had with h1 | h2 | h3 | h4
          · have hq : (Walk.cons h1 (Walk.cons hcd p4)).length < n := by simp [Walk.length_cons]; omega
            exact absurd (hmin (Walk.cons h1 (Walk.cons hcd p4))) (by omega)
          · have hq : (Walk.cons h2 p4).length < n := by simp [Walk.length_cons]; omega
            exact absurd (hmin (Walk.cons h2 p4)) (by omega)
          · have hq : (Walk.cons hxa (Walk.cons h3 (Walk.cons hcd p4))).length < n := by
              simp [Walk.length_cons]; omega
            exact absurd (hmin (Walk.cons hxa (Walk.cons h3 (Walk.cons hcd p4)))) (by omega)
          · have hq : (Walk.cons hxa (Walk.cons h4 p4)).length < n := by
              simp [Walk.length_cons]; omega
            exact absurd (hmin (Walk.cons hxa (Walk.cons h4 p4))) (by omega)

/-! ### Part 3: Traps, `C_5`, and existence of connected traps (Turcotte Section 3) -/

private def IsTrappedBy {V : Type*} (G : SimpleGraph V) (u x₁ x₂ : V) : Prop :=
  x₁ ≠ u ∧ x₂ ≠ u ∧ ∀ w, ClosedAdj G u w → ClosedAdj G x₁ w ∨ ClosedAdj G x₂ w

private def HasConnectedTrap {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ u x₁ x₂ : V, IsTrappedBy G u x₁ x₂ ∧ G.Adj x₁ x₂

private def IsC5 {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ a : Fin 5 → V, Function.Bijective a ∧
    ∀ i j : Fin 5, G.Adj (a i) (a j) ↔ (i + 1 = j ∨ j + 1 = i)

private lemma trap_of_C5_complement {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hconn : G.Connected) (h2k2 : IsTwoK2Free G) (u : V)
    (hC5 : IsC5 (G.induce {v : V | ¬ ClosedAdj G u v})) : HasConnectedTrap G := by
  classical
  let R : Set V := {v : V | ¬ ClosedAdj G u v}
  obtain ⟨a', ha'_bij, ha'_adj⟩ := hC5
  let a : Fin 5 → V := fun i => (a' i).val
  have ha_mem : ∀ i : Fin 5, ¬ ClosedAdj G u (a i) := fun i => (a' i).property
  have ha_inj : Function.Injective a := fun i j h => ha'_bij.1 (Subtype.ext h)
  have ha_adj : ∀ i j : Fin 5, G.Adj (a i) (a j) ↔ (i + 1 = j ∨ j + 1 = i) := ha'_adj
  have ha_surj : ∀ v : V, ¬ ClosedAdj G u v → ∃ i : Fin 5, a i = v := by
    intro v hv
    obtain ⟨i, hi⟩ := ha'_bij.2 ⟨v, hv⟩
    exact ⟨i, congrArg Subtype.val hi⟩
  -- Every neighbor x of u is adjacent to a_i or a_{i+1} for every i : Fin 5
  have hcover : ∀ x : V, G.Adj u x → ∀ i : Fin 5, G.Adj x (a i) ∨ G.Adj x (a (i + 1)) := by
    intro x hux i
    exact cantmove h2k2 (ha_mem i) (ha_mem (i + 1)) ((ha_adj i (i + 1)).mpr (Or.inl rfl)) hux
  -- Case 1: Some x ∈ N(u) is adjacent to 3 consecutive vertices a_{i-1}, a_i, a_{i+1}
  by_cases h3consec : ∃ x : V, G.Adj u x ∧ ∃ i : Fin 5,
      G.Adj x (a (i - 1)) ∧ G.Adj x (a i) ∧ G.Adj x (a (i + 1))
  · obtain ⟨x, hux, i, hx1, hx2, hx3⟩ := h3consec
    refine ⟨a i, u, x, ⟨fun h => ha_mem i (Or.inl h), fun h => ha_mem i (Or.inr (h ▸ hux)), ?_⟩, hux⟩
    intro w hw
    by_cases hwu : ClosedAdj G u w
    · exact Or.inl hwu
    · obtain ⟨j, rfl⟩ := ha_surj w hwu
      have hj : j = i ∨ j = i - 1 ∨ j = i + 1 := by
        rcases hw with heq | hadj
        · exact Or.inl (ha_inj heq.symm)
        · rw [ha_adj] at hadj
          rcases hadj with h1 | h2
          · exact Or.inr (Or.inr h1.symm)
          · right; left; exact eq_sub_of_add_eq h2
      rcases hj with rfl | rfl | rfl
      · exact Or.inr (Or.inr hx2)
      · exact Or.inr (Or.inr hx1)
      · exact Or.inr (Or.inr hx3)
  · -- For every x ∈ N(u), x has a unique index i : Fin 5 such that x is adjacent to {a i, a (i+2), a (i+3)}
    -- and NOT adjacent to a (i+1), a (i+4)!
    have hshape : ∀ x : V, G.Adj u x → ∃ i : Fin 5,
        G.Adj x (a i) ∧ ¬ G.Adj x (a (i + 1)) ∧ G.Adj x (a (i + 2)) ∧
        G.Adj x (a (i + 3)) ∧ ¬ G.Adj x (a (i + 4)) := by
      intro x hux
      have hno3 : ∀ i : Fin 5, ¬ (G.Adj x (a (i - 1)) ∧ G.Adj x (a i) ∧ G.Adj x (a (i + 1))) :=
        fun i h => h3consec ⟨x, hux, i, h⟩
      have hc := hcover x hux
      have hex_not : ∃ k : Fin 5, ¬ G.Adj x (a k) := by
        by_contra hall
        push Not at hall
        exact hno3 1 ⟨hall 0, hall 1, hall 2⟩
      obtain ⟨k, hnk⟩ := hex_not
      have hk1 : G.Adj x (a (k + 1)) := (hc k).resolve_left hnk
      have hkm1 : G.Adj x (a (k - 1)) := by
        have h := hc (k - 1)
        rw [sub_add_cancel] at h
        exact h.resolve_right hnk
      by_cases hk2 : G.Adj x (a (k + 2))
      · have hnk3 : ¬ G.Adj x (a (k + 3)) := by
          intro hk3
          apply hno3 (k + 2)
          refine ⟨?_, hk2, ?_⟩
          · rw [show k + 2 - 1 = k + 1 by fin_cases k <;> decide]; exact hk1
          · rw [show k + 2 + 1 = k + 3 by fin_cases k <;> decide]; exact hk3
        refine ⟨k + 4, ?_, ?_, ?_, ?_, ?_⟩
        · rw [show k + 4 = k - 1 by fin_cases k <;> decide]; exact hkm1
        · rw [show k + 4 + 1 = k by fin_cases k <;> decide]; exact hnk
        · rw [show k + 4 + 2 = k + 1 by fin_cases k <;> decide]; exact hk1
        · rw [show k + 4 + 3 = k + 2 by fin_cases k <;> decide]; exact hk2
        · rw [show k + 4 + 4 = k + 3 by fin_cases k <;> decide]; exact hnk3
      · have hk3 : G.Adj x (a (k + 3)) := by
          have h := hc (k + 2)
          rw [show k + 2 + 1 = k + 3 by fin_cases k <;> decide] at h
          exact h.resolve_left hk2
        refine ⟨k + 1, hk1, ?_, ?_, ?_, ?_⟩
        · rw [show k + 1 + 1 = k + 2 by fin_cases k <;> decide]; exact hk2
        · rw [show k + 1 + 2 = k + 3 by fin_cases k <;> decide]; exact hk3
        · rw [show k + 1 + 3 = k - 1 by fin_cases k <;> decide]; exact hkm1
        · rw [show k + 1 + 4 = k by fin_cases k <;> decide]; exact hnk
    -- Case 2: Two distinct neighbors x₁, x₂ of u have the same neighborhood in R
    by_cases hdup : ∃ x₁ x₂ : V, G.Adj u x₁ ∧ G.Adj u x₂ ∧ x₁ ≠ x₂ ∧
        ∀ i : Fin 5, G.Adj x₁ (a i) ↔ G.Adj x₂ (a i)
    · obtain ⟨x₁, x₂, hux₁, hux₂, hne, hsame⟩ := hdup
      refine ⟨x₁, x₂, u, ⟨hne.symm, hux₁.ne, ?_⟩, hux₂.symm⟩
      intro w hw
      by_cases hwu : ClosedAdj G u w
      · exact Or.inr hwu
      · obtain ⟨j, rfl⟩ := ha_surj w hwu
        rcases hw with rfl | hadj
        · exact absurd (Or.inr hux₁) hwu
        · exact Or.inl (Or.inr ((hsame j).mp hadj))
    · -- Every neighbor x of u has a distinct type i ∈ Fin 5!
      -- First, N(u) is nonempty (since G is connected and a 0 ∉ N[u])
      have hNu_ne : ∃ x : V, G.Adj u x := by
        have hstep : ∀ w0 : V, a 0 = w0 → G.Walk u w0 → ∃ x : V, G.Adj u x := by
          intro w0 hw0 p
          cases p with
          | nil => exact absurd (Or.inl hw0.symm) (ha_mem 0)
          | @cons _ x _ hadj _ => exact ⟨x, hadj⟩
        obtain ⟨p⟩ := hconn u (a 0)
        exact hstep (a 0) rfl p
      obtain ⟨x₀, hux₀⟩ := hNu_ne
      obtain ⟨i₀, hx₀0, hx₀1, hx₀2, hx₀3, hx₀4⟩ := hshape x₀ hux₀
      -- Claim: u is c-trapped by x₀ and a i₀!
      refine ⟨u, x₀, a i₀, ⟨hux₀.ne.symm, fun h => ha_mem i₀ (Or.inl h.symm), ?_⟩, hx₀0⟩
      intro w hw
      rcases hw with rfl | huw
      · exact Or.inl (Or.inr hux₀.symm)
      · obtain ⟨j, hj0, hj1, hj2, hj3, hj4⟩ := hshape w huw
        -- If j = i₀, then w = x₀ (since no duplicates!)
        by_cases heq : j = i₀
        · subst heq
          have hwx : w = x₀ := by
            by_contra hne
            apply hdup
            refine ⟨w, x₀, huw, hux₀, hne, fun k => ?_⟩
            have hk : k = j ∨ k = j + 1 ∨ k = j + 2 ∨ k = j + 3 ∨ k = j + 4 := by
              fin_cases k <;> fin_cases j <;> decide
            rcases hk with rfl | rfl | rfl | rfl | rfl <;> tauto
          exact Or.inl (Or.inl hwx.symm)
        · -- Check the 4 remaining values of j relative to i₀:
          have hrel : j = i₀ + 1 ∨ j = i₀ + 2 ∨ j = i₀ + 3 ∨ j = i₀ + 4 := by
            revert heq; fin_cases j <;> fin_cases i₀ <;> decide
          rcases hrel with rfl | rfl | rfl | rfl
          · -- j = i₀ + 1: compare edges x₀ - a(i₀+2) and w - a(i₀+4)
            have h1 : G.Adj x₀ (a (i₀ + 2)) := hx₀2
            have h2 : G.Adj w (a (i₀ + 1 + 3)) := hj3
            have heq4 : i₀ + 1 + 3 = i₀ + 4 := by fin_cases i₀ <;> decide
            rw [heq4] at h2
            have hxw : x₀ ≠ w := fun h => hx₀1 (h ▸ hj0)
            have hxa4 : x₀ ≠ a (i₀ + 4) := fun h => ha_mem (i₀ + 4) (Or.inr (h ▸ hux₀))
            have ha2w : a (i₀ + 2) ≠ w := fun h => ha_mem (i₀ + 2) (Or.inr (h.symm ▸ huw))
            have ha24 : a (i₀ + 2) ≠ a (i₀ + 4) := fun h => by
              have h' := ha_inj h
              revert h'; fin_cases i₀ <;> decide
            have hno_a24 : ¬ G.Adj (a (i₀ + 2)) (a (i₀ + 4)) := by
              rw [ha_adj]; fin_cases i₀ <;> decide
            have hno_wa2 : ¬ G.Adj w (a (i₀ + 2)) := by
              have : i₀ + 1 + 1 = i₀ + 2 := by fin_cases i₀ <;> decide
              rw [← this]; exact hj1
            rcases h2k2 x₀ (a (i₀ + 2)) w (a (i₀ + 4)) h1 h2 hxw hxa4 ha2w ha24 with c1 | c2 | c3 | c4
            · exact Or.inl (Or.inr c1)
            · exact absurd c2 hx₀4
            · exact absurd c3.symm hno_wa2
            · exact absurd c4 hno_a24
          · -- j = i₀ + 2: j + 3 = i₀, so G.Adj w (a i₀)!
            have : i₀ + 2 + 3 = i₀ := by fin_cases i₀ <;> decide
            rw [this] at hj3
            exact Or.inr (Or.inr hj3.symm)
          · -- j = i₀ + 3: j + 2 = i₀, so G.Adj w (a i₀)!
            have : i₀ + 3 + 2 = i₀ := by fin_cases i₀ <;> decide
            rw [this] at hj2
            exact Or.inr (Or.inr hj2.symm)
          · -- j = i₀ + 4: compare edges x₀ - a(i₀+3) and w - a(i₀+1)
            have h1 : G.Adj x₀ (a (i₀ + 3)) := hx₀3
            have h2 : G.Adj w (a (i₀ + 4 + 2)) := hj2
            have heq1 : i₀ + 4 + 2 = i₀ + 1 := by fin_cases i₀ <;> decide
            rw [heq1] at h2
            have hxw : x₀ ≠ w := fun h => hx₀4 (h ▸ hj0)
            have hxa1 : x₀ ≠ a (i₀ + 1) := fun h => ha_mem (i₀ + 1) (Or.inr (h ▸ hux₀))
            have ha3w : a (i₀ + 3) ≠ w := fun h => ha_mem (i₀ + 3) (Or.inr (h.symm ▸ huw))
            have ha31 : a (i₀ + 3) ≠ a (i₀ + 1) := fun h => by
              have h' := ha_inj h
              revert h'; fin_cases i₀ <;> decide
            have hno_a31 : ¬ G.Adj (a (i₀ + 3)) (a (i₀ + 1)) := by
              rw [ha_adj]; fin_cases i₀ <;> decide
            have hno_wa3 : ¬ G.Adj w (a (i₀ + 3)) := by
              have : i₀ + 4 + 4 = i₀ + 3 := by fin_cases i₀ <;> decide
              rw [← this]; exact hj4
            rcases h2k2 x₀ (a (i₀ + 3)) w (a (i₀ + 1)) h1 h2 hxw hxa1 ha3w ha31 with c1 | c2 | c3 | c4
            · exact Or.inl (Or.inr c1)
            · exact absurd c2 hx₀1
            · exact absurd c3.symm hno_wa3
            · exact absurd c4 hno_a31

private lemma exists_connectedTrap_or_small :
    ∀ (n : ℕ) {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V),
      Fintype.card V = n → G.Connected → IsTwoK2Free G →
      Fintype.card V ≤ 2 ∨ IsC5 G ∨ HasConnectedTrap G := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ G hcard hconn h2k2
    classical
    by_cases hle2 : Fintype.card V ≤ 2
    · exact Or.inl hle2
    have hge3 : 3 ≤ Fintype.card V := by omega
    obtain ⟨u⟩ := ‹Nonempty V›
    let R : Set V := {v : V | ¬ ClosedAdj G u v}
    let GR := G.induce R
    -- Case 1: R is empty (u dominates G)
    by_cases hRempty : IsEmpty R
    · -- u has at least 2 distinct neighbors x₁, x₂
      have hcard_ne : 2 ≤ Fintype.card {x : V // x ≠ u} := by
        rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
        omega
      have hgt1 : 1 < Fintype.card {x : V // x ≠ u} := by omega
      obtain ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩, hne⟩ := Fintype.exists_pair_of_one_lt_card hgt1
      have hne' : x₁ ≠ x₂ := fun h => hne (Subtype.ext h)
      have hux₁ : G.Adj u x₁ := by
        have hmem : ClosedAdj G u x₁ := by
          by_contra hnot
          exact hRempty.false ⟨x₁, hnot⟩
        exact hmem.resolve_left hx₁.symm
      have hux₂ : G.Adj u x₂ := by
        have hmem : ClosedAdj G u x₂ := by
          by_contra hnot
          exact hRempty.false ⟨x₂, hnot⟩
        exact hmem.resolve_left hx₂.symm
      refine Or.inr (Or.inr ⟨x₁, u, x₂, ⟨hx₁.symm, hne'.symm, ?_⟩, hux₂⟩)
      intro w _
      by_contra hnot
      push Not at hnot
      exact hRempty.false ⟨w, hnot.1⟩
    · have : Nonempty R := not_isEmpty_iff.mp hRempty
      -- Case 2: R has an isolated vertex y
      by_cases hiso : ∃ y : R, ∀ z : R, ¬ GR.Adj y z
      · obtain ⟨⟨y, hy⟩, hy_iso⟩ := hiso
        -- y has at least one neighbor x in G (since G is connected and y ≠ u); x must be in N(u)!
        have hyu : y ≠ u := fun h => hy (Or.inl h.symm)
        obtain ⟨p⟩ := hconn y u
        cases p with
        | nil => exact absurd rfl hyu
        | @cons _ x _ hyx _ =>
          have hxu : ClosedAdj G u x := by
            by_contra hnot
            exact hy_iso ⟨x, hnot⟩ hyx
          have hux : G.Adj u x := hxu.resolve_left (fun h => hy (Or.inr (h ▸ hyx.symm)))
          refine Or.inr (Or.inr ⟨y, u, x, ⟨hyu.symm, hyx.ne.symm, ?_⟩, hux⟩)
          intro w hw
          rcases hw with rfl | hyw
          · exact Or.inr (Or.inr hyx.symm)
          · by_contra hnot
            push Not at hnot
            exact hy_iso ⟨w, hnot.1⟩ hyw
      · -- R has no isolated vertex, so GR is connected and |R| >= 2
        push Not at hiso
        have hGR_2k2 : IsTwoK2Free GR := isTwoK2Free_induce h2k2 R
        have hGR_conn : GR.Connected := connected_of_no_isolated hGR_2k2 hiso
        have hR_lt : Fintype.card R < Fintype.card V := by
          have hle := Fintype.card_subtype_le (p := fun v : V => ¬ ClosedAdj G u v)
          have hlt : Fintype.card {v : V // ¬ ClosedAdj G u v} < Fintype.card V := by
            apply Fintype.card_lt_of_injective_not_surjective Subtype.val Subtype.val_injective
            intro hsurj
            obtain ⟨⟨w, hw⟩, hwu⟩ := hsurj u
            exact hw (Or.inl hwu.symm)
          exact hlt
        have hR_ge2 : 2 ≤ Fintype.card R := by
          obtain ⟨y⟩ := ‹Nonempty R›
          obtain ⟨z, hyz⟩ := hiso y
          have hne : y ≠ z := hyz.ne
          have hsub : ({y, z} : Finset R) ⊆ Finset.univ := Finset.subset_univ _
          have := Finset.card_le_card hsub
          rw [Finset.card_pair hne, Finset.card_univ] at this
          exact this
        -- Case 3: |R| = 2 (GR is an edge v₁v₂)
        by_cases hR2 : Fintype.card R = 2
        · obtain ⟨v₁⟩ := ‹Nonempty R›
          obtain ⟨v₂, hv₁₂⟩ := hiso v₁
          have hne12 : v₁ ≠ v₂ := hv₁₂.ne
          have hR_eq : ∀ z : R, z = v₁ ∨ z = v₂ := by
            have hcard_pair : ({v₁, v₂} : Finset R).card = Fintype.card R := by
              rw [Finset.card_pair hne12, hR2]
            have huniv : ({v₁, v₂} : Finset R) = Finset.univ :=
              Finset.eq_univ_of_card _ hcard_pair
            intro z
            have hz : z ∈ ({v₁, v₂} : Finset R) := by rw [huniv]; exact Finset.mem_univ z
            simpa using hz
          -- Subcase 3a: v₁ and v₂ share a common neighbor t ∈ N(u)
          by_cases hcom : ∃ t : V, G.Adj u t ∧ G.Adj t v₁.val ∧ G.Adj t v₂.val
          · obtain ⟨t, hut, htv₁, htv₂⟩ := hcom
            refine Or.inr (Or.inr ⟨v₁.val, t, u, ⟨htv₁.ne, fun h => v₁.property (Or.inl h), ?_⟩, hut.symm⟩)
            intro w hw
            by_cases hwu : ClosedAdj G u w
            · exact Or.inr hwu
            · rcases hR_eq ⟨w, hwu⟩ with h1 | h2
              · have : w = v₁.val := congrArg Subtype.val h1
                rw [this]; exact Or.inl (Or.inr htv₁)
              · have : w = v₂.val := congrArg Subtype.val h2
                rw [this]; exact Or.inl (Or.inr htv₂)
          · -- Subcase 3b: No common neighbor in N(u). Partition N(u) into A (adj v₁) and B (adj v₂).
            push Not at hcom
            have hAB : ∀ x : V, G.Adj u x → G.Adj x v₁.val ∨ G.Adj x v₂.val := fun x hux =>
              cantmove h2k2 v₁.property v₂.property hv₁₂ hux
            -- If A has >= 2 distinct vertices a₁, a₂, then a₁ is c-trapped by a₂ and u!
            by_cases hA2 : ∃ a₁ a₂ : V, G.Adj u a₁ ∧ G.Adj u a₂ ∧ a₁ ≠ a₂ ∧
                G.Adj a₁ v₁.val ∧ G.Adj a₂ v₁.val
            · obtain ⟨a₁, a₂, hua₁, hua₂, hne, ha₁v₁, ha₂v₁⟩ := hA2
              refine Or.inr (Or.inr ⟨a₁, a₂, u, ⟨hne.symm, hua₁.ne, ?_⟩, hua₂.symm⟩)
              intro w hw
              by_cases hwu : ClosedAdj G u w
              · exact Or.inr hwu
              · rcases hR_eq ⟨w, hwu⟩ with h1 | h2
                · have : w = v₁.val := congrArg Subtype.val h1
                  rw [this]; exact Or.inl (Or.inr ha₂v₁)
                · have : w = v₂.val := congrArg Subtype.val h2
                  rw [this] at hw
                  rcases hw with heq | hadj
                  · exact absurd (Or.inr hua₁) (heq ▸ v₂.property)
                  · exact absurd hadj (hcom a₁ hua₁ ha₁v₁)
            -- Symmetrically if B has >= 2 distinct vertices b₁, b₂
            by_cases hB2 : ∃ b₁ b₂ : V, G.Adj u b₁ ∧ G.Adj u b₂ ∧ b₁ ≠ b₂ ∧
                G.Adj b₁ v₂.val ∧ G.Adj b₂ v₂.val
            · obtain ⟨b₁, b₂, hub₁, hub₂, hne, hb₁v₂, hb₂v₂⟩ := hB2
              refine Or.inr (Or.inr ⟨b₁, b₂, u, ⟨hne.symm, hub₁.ne, ?_⟩, hub₂.symm⟩)
              intro w hw
              by_cases hwu : ClosedAdj G u w
              · exact Or.inr hwu
              · rcases hR_eq ⟨w, hwu⟩ with h1 | h2
                · have : w = v₁.val := congrArg Subtype.val h1
                  rw [this] at hw
                  rcases hw with heq | hadj
                  · exact absurd (Or.inr hub₁) (heq ▸ v₁.property)
                  · exact absurd hb₁v₂ (hcom b₁ hub₁ hadj)
                · have : w = v₂.val := congrArg Subtype.val h2
                  rw [this]; exact Or.inl (Or.inr hb₂v₂)
            -- Now |A| <= 1 and |B| <= 1, and |A| + |B| >= 1 (since G is connected).
            push Not at hA2 hB2
            have hA_or_B : (∃ a : V, G.Adj u a ∧ G.Adj a v₁.val) ∨
                (∃ b : V, G.Adj u b ∧ G.Adj b v₂.val) := by
              have hstep : ∀ w1 : V, v₁.val = w1 → G.Walk u w1 → ∃ x : V, G.Adj u x := by
                intro w1 hw1 p
                cases p with
                | nil => exact absurd (Or.inl hw1.symm) v₁.property
                | @cons _ x _ hux _ => exact ⟨x, hux⟩
              obtain ⟨p⟩ := hconn u v₁.val
              obtain ⟨x, hux⟩ := hstep v₁.val rfl p
              rcases hAB x hux with h1 | h2
              · exact Or.inl ⟨x, hux, h1⟩
              · exact Or.inr ⟨x, hux, h2⟩
            by_cases hboth : (∃ a : V, G.Adj u a ∧ G.Adj a v₁.val) ∧
                (∃ b : V, G.Adj u b ∧ G.Adj b v₂.val)
            · obtain ⟨⟨a, hua, hav₁⟩, ⟨b, hub, hbv₂⟩⟩ := hboth
              have hab_ne : a ≠ b := fun h => hcom a hua hav₁ (h ▸ hbv₂)
              -- Every neighbor of u is a or b
              have hNu_ab : ∀ x : V, G.Adj u x → x = a ∨ x = b := by
                intro x hux
                rcases hAB x hux with hx1 | hx2
                · left; by_contra hne; exact hA2 x a hux hua hne hx1 hav₁
                · right; by_contra hne; exact hB2 x b hux hub hne hx2 hbv₂
              by_cases hab_adj : G.Adj a b
              · -- u is c-trapped by a and b!
                refine Or.inr (Or.inr ⟨u, a, b, ⟨hua.ne.symm, hub.ne.symm, ?_⟩, hab_adj⟩)
                intro w hw
                rcases hw with rfl | huw
                · exact Or.inl (Or.inr hua.symm)
                · rcases hNu_ab w huw with rfl | rfl
                  · exact Or.inl (Or.inl rfl)
                  · exact Or.inr (Or.inl rfl)
              · -- G ≃ C_5 with vertices (u, a, v₁, v₂, b)!
                refine Or.inr (Or.inl ?_)
                let f : Fin 5 → V := ![u, a, v₁.val, v₂.val, b]
                have hav₂ : ¬ G.Adj a v₂.val := hcom a hua hav₁
                have hbv₁ : ¬ G.Adj b v₁.val := fun h => hcom b hub h hbv₂
                have hu_ne_a : u ≠ a := hua.ne
                have hu_ne_b : u ≠ b := hub.ne
                have hu_ne_v1 : u ≠ v₁.val := fun h => v₁.property (Or.inl h)
                have hu_ne_v2 : u ≠ v₂.val := fun h => v₂.property (Or.inl h)
                have ha_ne_v1 : a ≠ v₁.val := hav₁.ne
                have ha_ne_v2 : a ≠ v₂.val := fun h => v₂.property (Or.inr (h ▸ hua))
                have hb_ne_v1 : b ≠ v₁.val := fun h => v₁.property (Or.inr (h ▸ hub))
                have hb_ne_v2 : b ≠ v₂.val := hbv₂.ne
                have hv1_ne_v2 : v₁.val ≠ v₂.val := fun h => hne12 (Subtype.ext h)
                have hno_uv1 : ¬ G.Adj u v₁.val := fun h => v₁.property (Or.inr h)
                have hno_uv2 : ¬ G.Adj u v₂.val := fun h => v₂.property (Or.inr h)
                refine ⟨f, ⟨?_, ?_⟩, ?_⟩
                · intro i j hij
                  fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢ <;>
                    try first
                      | rfl
                      | exact absurd hij hu_ne_a | exact absurd hij.symm hu_ne_a
                      | exact absurd hij hu_ne_b | exact absurd hij.symm hu_ne_b
                      | exact absurd hij hu_ne_v1 | exact absurd hij.symm hu_ne_v1
                      | exact absurd hij hu_ne_v2 | exact absurd hij.symm hu_ne_v2
                      | exact absurd hij ha_ne_v1 | exact absurd hij.symm ha_ne_v1
                      | exact absurd hij ha_ne_v2 | exact absurd hij.symm ha_ne_v2
                      | exact absurd hij hb_ne_v1 | exact absurd hij.symm hb_ne_v1
                      | exact absurd hij hb_ne_v2 | exact absurd hij.symm hb_ne_v2
                      | exact absurd hij hab_ne | exact absurd hij.symm hab_ne
                      | exact absurd hij hv1_ne_v2 | exact absurd hij.symm hv1_ne_v2
                · intro w
                  by_cases hwu : ClosedAdj G u w
                  · rcases hwu with rfl | huw
                    · exact ⟨0, rfl⟩
                    · rcases hNu_ab w huw with rfl | rfl
                      · exact ⟨1, rfl⟩
                      · exact ⟨4, rfl⟩
                  · rcases hR_eq ⟨w, hwu⟩ with h1 | h2
                    · exact ⟨2, (congrArg Subtype.val h1).symm⟩
                    · exact ⟨3, (congrArg Subtype.val h2).symm⟩
                · intro i j
                  fin_cases i <;> fin_cases j <;> simp [f] <;>
                    first
                      | exact G.loopless _
                      | exact hua | exact hua.symm | exact hub | exact hub.symm
                      | exact hav₁ | exact hav₁.symm | exact hbv₂ | exact hbv₂.symm
                      | exact hv₁₂ | exact hv₁₂.symm
                      | exact hno_uv1 | exact (fun h => hno_uv1 h.symm)
                      | exact hno_uv2 | exact (fun h => hno_uv2 h.symm)
                      | exact hab_adj | exact (fun h => hab_adj h.symm)
                      | exact hav₂ | exact (fun h => hav₂ h.symm)
                      | exact hbv₁ | exact (fun h => hbv₁ h.symm)
            · -- Exactly one of A, B is nonempty (and has size 1): G is P_4, has a connected trap!
              rcases hA_or_B with ⟨a, hua, hav₁⟩ | ⟨b, hub, hbv₂⟩
              · have hBempty : ∀ x : V, G.Adj u x → ¬ G.Adj x v₂.val :=
                  fun x hux hxv₂ => hboth ⟨⟨a, hua, hav₁⟩, ⟨x, hux, hxv₂⟩⟩
                -- v₂ has ONLY neighbor v₁! So v₂ is c-trapped by v₁ and a!
                refine Or.inr (Or.inr ⟨v₂.val, v₁.val, a, ⟨fun h => hv₁₂.ne (Subtype.ext h), fun h => v₂.property (Or.inr (h ▸ hua)), ?_⟩, hav₁.symm⟩)
                intro w hw
                rcases hw with rfl | hv₂w
                · exact Or.inl (Or.inr hv₁₂)
                · by_cases hwu : ClosedAdj G u w
                  · rcases hwu with rfl | huw
                    · exact absurd (Or.inr hv₂w.symm) v₂.property
                    · exact absurd hv₂w.symm (hBempty w huw)
                  · rcases hR_eq ⟨w, hwu⟩ with h1 | h2
                    · exact Or.inl (Or.inl (congrArg Subtype.val h1).symm)
                    · exact absurd (congrArg Subtype.val h2) hv₂w.ne.symm
              · have hAempty : ∀ x : V, G.Adj u x → ¬ G.Adj x v₁.val :=
                  fun x hux hxv₁ => hboth ⟨⟨x, hux, hxv₁⟩, ⟨b, hub, hbv₂⟩⟩
                -- v₁ has ONLY neighbor v₂! So v₁ is c-trapped by v₂ and b!
                refine Or.inr (Or.inr ⟨v₁.val, v₂.val, b, ⟨fun h => hv₁₂.ne.symm (Subtype.ext h), fun h => v₁.property (Or.inr (h ▸ hub)), ?_⟩, hbv₂.symm⟩)
                intro w hw
                rcases hw with rfl | hv₁w
                · exact Or.inl (Or.inr hv₁₂.symm)
                · by_cases hwu : ClosedAdj G u w
                  · rcases hwu with rfl | huw
                    · exact absurd (Or.inr hv₁w.symm) v₁.property
                    · exact absurd hv₁w.symm (hAempty w huw)
                  · rcases hR_eq ⟨w, hwu⟩ with h1 | h2
                    · exact absurd (congrArg Subtype.val h1) hv₁w.ne.symm
                    · exact Or.inl (Or.inl (congrArg Subtype.val h2).symm)
        · -- Case 4: |R| >= 3! Apply IH to GR!
          have hR_ge3 : 3 ≤ Fintype.card R := by omega
          rcases ih (Fintype.card R) (hcard ▸ hR_lt) GR rfl hGR_conn hGR_2k2 with hsmall | hC5 | htrap
          · omega
          · exact Or.inr (Or.inr (trap_of_C5_complement hconn h2k2 u hC5))
          · obtain ⟨v, w₁, w₂, ⟨hw₁v, hw₂v, hdomR⟩, hw₁₂⟩ := htrap
            refine Or.inr (Or.inr ⟨v.val, w₁.val, w₂.val,
              ⟨fun h => hw₁v (Subtype.ext h), fun h => hw₂v (Subtype.ext h), ?_⟩, hw₁₂⟩)
            intro z hz
            by_cases hzu : ClosedAdj G u z
            · rcases hzu with rfl | huz
              · rcases hz with heq | hadj
                · exact absurd (Or.inl heq.symm) v.property
                · exact absurd (Or.inr hadj.symm) v.property
              · rcases cantmove h2k2 w₁.property w₂.property hw₁₂ huz with h1 | h2
                · exact Or.inl (Or.inr h1.symm)
                · exact Or.inr (Or.inr h2.symm)
            · have hzR : ClosedAdj GR v ⟨z, hzu⟩ := hz.imp (fun h => Subtype.ext h) id
              rcases hdomR ⟨z, hzu⟩ hzR with h1 | h2
              · exact Or.inl (h1.imp (congrArg Subtype.val) id)
              · exact Or.inr (h2.imp (congrArg Subtype.val) id)

/-! ### Part 4: Minimal counterexample elimination (Turcotte Section 4) -/

private lemma copNumberLeTwo_of_card_le_two {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (hle : Fintype.card V ≤ 2) : CopNumberLeTwo G := by
  classical
  obtain ⟨v₀⟩ := ‹Nonempty V›
  by_cases hex : ∃ v₁ : V, v₁ ≠ v₀
  · obtain ⟨v₁, hv₁⟩ := hex
    refine ⟨v₀, v₁, fun r => CopWinFrom.caught ?_⟩
    have hcard : ({v₀, v₁} : Finset V).card = 2 := Finset.card_pair hv₁.symm
    have hle2 : Fintype.card V = 2 := by
      have := Finset.card_le_univ ({v₀, v₁} : Finset V)
      omega
    have huniv : ({v₀, v₁} : Finset V) = Finset.univ := Finset.eq_univ_of_card _ (by omega)
    have hr : r ∈ ({v₀, v₁} : Finset V) := by rw [huniv]; exact Finset.mem_univ r
    simpa [eq_comm] using hr
  · push Not at hex
    exact ⟨v₀, v₀, fun r => CopWinFrom.caught (Or.inl (hex r).symm)⟩

private lemma copNumberLeTwo_of_isC5 {V : Type*} {G : SimpleGraph V} (hC5 : IsC5 G) :
    CopNumberLeTwo G := by
  obtain ⟨a, ha_bij, ha_adj⟩ := hC5
  refine ⟨a 0, a 2, fun r => ?_⟩
  obtain ⟨i, rfl⟩ := ha_bij.2 r
  apply copWinFrom_of_closedAdj
  fin_cases i
  · exact Or.inl (Or.inl rfl)
  · exact Or.inl (Or.inr ((ha_adj 0 1).mpr (Or.inl rfl)))
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ((ha_adj 2 3).mpr (Or.inl rfl)))
  · exact Or.inl (Or.inr ((ha_adj 0 4).mpr (Or.inr rfl)))

private lemma win_of_edge_win {V : Type*} {G : SimpleGraph V}
    (h2k2 : IsTwoK2Free G) {u : V}
    (hGu_win : CopNumberLeTwo (G.induce {x : V | x ≠ u}))
    (hR_conn : (G.induce {x : V | ¬ ClosedAdj G u x}).Connected)
    (hR_noiso : ∀ v : {x : V | ¬ ClosedAdj G u x}, ∃ w : {x : V | ¬ ClosedAdj G u x},
      (G.induce {x : V | ¬ ClosedAdj G u x}).Adj v w)
    {v₀ w₀ : V} (hv₀ : ¬ ClosedAdj G u v₀) (hw₀ : ¬ ClosedAdj G u w₀) (hv₀w₀ : G.Adj v₀ w₀)
    (hwin_edge : CopWinFrom G (v₀, w₀) u) : CopNumberLeTwo G := by
  classical
  let R : Set V := {x : V | ¬ ClosedAdj G u x}
  let GR := G.induce R
  have hGR_2k2 : IsTwoK2Free GR := isTwoK2Free_induce h2k2 R
  -- Step 1: Moving cops from any valid position into an edge (a, b) ∈ E(GR) where CopWinFrom G (a, b) u wins!
  have hstep_to_edge : ∀ {z₁ z₂ a b : V}, ClosedAdj G z₁ a → ClosedAdj G z₂ b →
      ¬ ClosedAdj G u a → ¬ ClosedAdj G u b → G.Adj a b → CopWinFrom G (a, b) u →
      CopWinFrom G (z₁, z₂) u := by
    intro z₁ z₂ a b hm₁ hm₂ ha hb hab hwin
    refine CopWinFrom.step hm₁ hm₂ fun r' hr' => ?_
    rcases hr' with rfl | hur'
    · exact hwin
    · rcases cantmove h2k2 ha hb hab hur' with h1 | h2
      · exact copWinFrom_of_closedAdj (Or.inl (Or.inr h1.symm))
      · exact copWinFrom_of_closedAdj (Or.inr (Or.inr h2.symm))
  -- Step 2: Every edge (a, b) in GR satisfies CopWinFrom G (a, b) u!
  have hall_edges : ∀ a b : R, GR.Adj a b → CopWinFrom G (a.val, b.val) u := by
    have hwalk : ∀ {x y : R} (_ : GR.Walk x y),
        (∀ z : R, GR.Adj z y → CopWinFrom G (z.val, y.val) u) →
        ∀ z : R, GR.Adj z x → CopWinFrom G (z.val, x.val) u := by
      intro x y p
      induction p with
      | nil => intro hbase z hz; exact hbase z hz
      | @cons x m y hxm q ih =>
        intro hbase z hz
        have hwin_xm : CopWinFrom G (x.val, m.val) u := ih hbase x hxm
        exact hstep_to_edge (Or.inr hz) (Or.inr hxm) x.property m.property hxm hwin_xm
    intro a b hab
    obtain ⟨p⟩ := hR_conn b ⟨v₀, hv₀⟩
    exact hwalk p (fun z hz => hstep_to_edge (Or.inr hz) (Or.inr hv₀w₀) hv₀ hw₀ hv₀w₀ hwin_edge) a hab
  -- Step 3: Every pair (z₁, z₂) in R × R satisfies CopWinFrom G (z₁, z₂) u!
  have hall_R : ∀ z₁ z₂ : R, CopWinFrom G (z₁.val, z₂.val) u := by
    intro z₁ z₂
    obtain ⟨p, hp⟩ := exists_walk_length_le_three hGR_2k2 hR_conn z₁ z₂
    cases p with
    | nil =>
      obtain ⟨w, hw⟩ := hR_noiso z₁
      exact hstep_to_edge (closedAdj_refl G z₁.val) (Or.inr hw) z₁.property w.property hw
        (hall_edges z₁ w hw)
    | @cons _ m1 _ h1 p1 =>
      cases p1 with
      | nil => exact hall_edges z₁ z₂ h1
      | @cons _ m2 _ h2 p2 =>
        cases p2 with
        | nil =>
          exact hstep_to_edge (closedAdj_refl G z₁.val) (Or.inr h2.symm)
            z₁.property m1.property h1 (hall_edges z₁ m1 h1)
        | @cons _ m3 _ h3 p3 =>
          cases p3 with
          | nil =>
            exact hstep_to_edge (Or.inr h1) (Or.inr h3.symm)
              m1.property m2.property h2 (hall_edges m1 m2 h2)
          | cons _ _ =>
            simp [Walk.length_cons] at hp; omega
  -- Step 4: Every pair (z₁, z₂) in V × V satisfies CopWinFrom G (z₁, z₂) u!
  have hall_V : ∀ z₁ z₂ : V, CopWinFrom G (z₁, z₂) u := by
    intro z₁ z₂
    by_cases h1 : ClosedAdj G u z₁
    · exact copWinFrom_of_closedAdj (Or.inl (closedAdj_symm h1))
    by_cases h2 : ClosedAdj G u z₂
    · exact copWinFrom_of_closedAdj (Or.inr (closedAdj_symm h2))
    exact hall_R ⟨z₁, h1⟩ ⟨z₂, h2⟩
  -- Step 5: Lift the winning strategy on G - u to G!
  let S : Set V := {x : V | x ≠ u}
  let Gu := G.induce S
  have hlift : ∀ {c₁ c₂ r : S}, CopWinFrom Gu (c₁, c₂) r → CopWinFrom G (c₁.val, c₂.val) r.val := by
    intro c₁ c₂ r h
    generalize hpair : (c₁, c₂) = pair at h
    induction h generalizing c₁ c₂ with
    | caught hc =>
      cases hpair
      exact CopWinFrom.caught (hc.imp (congrArg Subtype.val) (congrArg Subtype.val))
    | capture hm₁ hm₂ hcap =>
      cases hpair
      exact CopWinFrom.capture (hm₁.imp (congrArg Subtype.val) id) (hm₂.imp (congrArg Subtype.val) id)
        (hcap.imp (congrArg Subtype.val) (congrArg Subtype.val))
    | step hm₁ hm₂ hnext ih =>
      cases hpair
      rename_i r0 c₁' c₂'
      refine CopWinFrom.step (hm₁.imp (congrArg Subtype.val) id) (hm₂.imp (congrArg Subtype.val) id) fun r' hr' => ?_
      by_cases hru : r' = u
      · subst hru; exact hall_V c₁'.val c₂'.val
      · exact ih ⟨r', hru⟩ (hr'.imp (fun heq => Subtype.ext heq) id) rfl
  obtain ⟨c₁, c₂, hwin⟩ := hGu_win
  refine ⟨c₁.val, c₂.val, fun r => ?_⟩
  by_cases hru : r = u
  · subst hru; exact hall_V c₁.val c₂.val
  · exact hlift (hwin ⟨r, hru⟩)

private lemma bipartite_universal {V : Type*} [Fintype V] {G : SimpleGraph V}
    (h2k2 : IsTwoK2Free G) (hconn : G.Connected)
    (A B : Set V) (hpart : ∀ v : V, v ∈ A ∨ v ∈ B) (hdisj : ∀ v : V, ¬ (v ∈ A ∧ v ∈ B))
    (hA_ind : ∀ x ∈ A, ∀ y ∈ A, ¬ G.Adj x y) (hB_ind : ∀ x ∈ B, ∀ y ∈ B, ¬ G.Adj x y)
    (hB_ne : B.Nonempty) :
    ∃ b ∈ B, ∀ a ∈ A, G.Adj b a := by
  classical
  -- Choose b ∈ B maximizing (G.neighborFinset b).card!
  let Bfin : Finset V := Finset.univ.filter (fun v => v ∈ B)
  have hBfin_ne : Bfin.Nonempty := by
    obtain ⟨b0, hb0⟩ := hB_ne
    exact ⟨b0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb0⟩⟩
  obtain ⟨b, hb_mem, hb_max⟩ := Finset.exists_max_image Bfin (fun v => (G.neighborFinset v).card) hBfin_ne
  have hbB : b ∈ B := (Finset.mem_filter.mp hb_mem).2
  refine ⟨b, hbB, fun a haA => ?_⟩
  by_contra hno
  -- Since G is connected and B is nonempty, a must have some neighbor b' (necessarily in B)
  have hab_ne : a ≠ b := fun h => hdisj a ⟨haA, h ▸ hbB⟩
  obtain ⟨p⟩ := hconn a b
  cases p with
  | nil => exact absurd rfl hab_ne
  | @cons _ b' _ hab' _ =>
    have hb'B : b' ∈ B := by
      rcases hpart b' with h1 | h2
      · exact absurd hab' (hA_ind a haA b' h1)
      · exact h2
    -- Every neighbor x of b is in A, and by 2K_2-freeness is also adjacent to b'!
    have hsub : G.neighborFinset b ⊆ G.neighborFinset b' := by
      intro x hx
      rw [G.mem_neighborFinset] at hx ⊢
      have hxA : x ∈ A := by
        rcases hpart x with h1 | h2
        · exact h1
        · exact absurd hx (hB_ind b hbB x h2)
      have hba : b ≠ a := hab_ne.symm
      have hbb' : b ≠ b' := fun h => hno (h ▸ hab'.symm)
      have hxa : x ≠ a := fun h => hno (h ▸ hx)
      have hxb' : x ≠ b' := fun h => hdisj x ⟨hxA, h ▸ hb'B⟩
      rcases h2k2 b x b' a hx hab'.symm hbb' hba hxb' hxa with c1 | c2 | c3 | c4
      · exact absurd c1 (hB_ind b hbB b' hb'B)
      · exact absurd c2 hno
      · exact c3.symm
      · exact absurd c4 (hA_ind x hxA a haA)
    have ha_in : a ∈ G.neighborFinset b' := (G.mem_neighborFinset b' a).mpr hab'.symm
    have ha_not : a ∉ G.neighborFinset b := fun h => hno ((G.mem_neighborFinset b a).mp h)
    have hssub : G.neighborFinset b ⊂ G.neighborFinset b' :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => ha_not (h ▸ ha_in)⟩
    have hlt := Finset.card_lt_card hssub
    have hle := hb_max b' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb'B⟩)
    omega

/-! ### Part 5: Main Theorem (Strong Induction on `Fintype.card V`) -/

private theorem copNumberLeTwo_aux :
    ∀ (n : ℕ) {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V),
      Fintype.card V = n → G.Connected → IsTwoK2Free G → CopNumberLeTwo G := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ G hcard hconn h2k2
    classical
    by_contra hnot_win
    -- Helper: every proper connected induced subgraph is 2-cop-win!
    have hmin : ∀ (S : Set V) [Fintype S] [Nonempty S], Fintype.card S < Fintype.card V →
        (G.induce S).Connected → CopNumberLeTwo (G.induce S) := by
      intro S _ _ hlt hSconn
      exact ih (Fintype.card S) (hcard ▸ hlt) (G.induce S) rfl hSconn (isTwoK2Free_induce h2k2 S)
    -- Lemma 4.1a: G - u is connected and 2-cop-win for every u ∈ V
    have hGu_conn : ∀ u : V, (G.induce {x : V | x ≠ u}).Connected := by
      intro u
      have hV_ge3 : 3 ≤ Fintype.card V := by
        by_contra hlt
        exact hnot_win (copNumberLeTwo_of_card_le_two G (by omega))
      have hGu_ne : Nonempty {x : V | x ≠ u} := by
        have : 1 < Fintype.card V := by omega
        obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card this
        by_cases hau : a = u
        · exact ⟨⟨b, fun h => hab (hau.trans h.symm)⟩⟩
        · exact ⟨⟨a, hau⟩⟩
      by_contra hdisc
      -- Since G - u is 2K_2-free and disconnected, some vertex x is isolated in G - u!
      have hiso : ∃ x : {v : V | v ≠ u}, ∀ y : {v : V | v ≠ u}, ¬ (G.induce {v : V | v ≠ u}).Adj x y := by
        by_contra hall
        push Not at hall
        exact hdisc (connected_of_no_isolated (isTwoK2Free_induce h2k2 _) hall)
      obtain ⟨⟨x, hxu⟩, hx_iso⟩ := hiso
      -- Then every neighbor of x in G is u!
      have hx_only : ∀ w : V, G.Adj x w → w = u := by
        intro w hxw
        by_contra hwu
        exact hx_iso ⟨w, hwu⟩ hxw
      have hdom : ∀ w : V, G.Adj x w → ClosedAdj G u w := fun w hxw => Or.inl (hx_only w hxw).symm
      -- And G - x is connected!
      have hGx_ne : Nonempty {v : V | v ≠ x} := ⟨⟨u, hxu.symm⟩⟩
      have hGx_conn : (G.induce {v : V | v ≠ x}).Connected := by
        constructor
        intro a b
        obtain ⟨p⟩ := hconn a.val b.val
        have havoid : ∀ (len : ℕ) {y z : V} (q : G.Walk y z), q.length = len →
            ∀ (hy : y ≠ x) (hz : z ≠ x), (G.induce {v : V | v ≠ x}).Reachable ⟨y, hy⟩ ⟨z, hz⟩ := by
          intro len
          induction len using Nat.strong_induction_on with
          | h len ihq =>
            intro y z q hlen hy hz
            cases q with
            | nil => exact Reachable.refl _
            | @cons _ w _ hyw q' =>
              by_cases hwx : w = x
              · subst w
                have hyu : y = u := hx_only y hyw.symm
                cases q' with
                | nil => exact absurd rfl hz
                | @cons _ w2 _ hxw2 q'' =>
                  have hw2u : w2 = u := hx_only w2 hxw2
                  have hw2x : w2 ≠ x := hw2u.symm ▸ hxu.symm
                  have heq : (⟨y, hy⟩ : {v : V | v ≠ x}) = ⟨w2, hw2x⟩ := Subtype.ext (hyu.trans hw2u.symm)
                  rw [heq]
                  have hlt : q''.length < len := by simp [Walk.length_cons] at hlen; omega
                  exact ihq q''.length hlt q'' rfl hw2x hz
              · have hlt : q'.length < len := by simp [Walk.length_cons] at hlen; omega
                exact (show (G.induce {v : V | v ≠ x}).Adj ⟨y, hy⟩ ⟨w, hwx⟩ from hyw).reachable.trans
                  (ihq q'.length hlt q' rfl hwx hz)
        exact havoid p.length p rfl a.property b.property
      have hGx_lt : Fintype.card {v : V | v ≠ x} < Fintype.card V := by
        apply Fintype.card_lt_of_injective_not_surjective Subtype.val Subtype.val_injective
        intro hsurj; obtain ⟨⟨w, hw⟩, hwx⟩ := hsurj x; exact hw hwx
      have hGx_win : CopNumberLeTwo (G.induce {v : V | v ≠ x}) := hmin _ hGx_lt hGx_conn
      exact hnot_win (shadow_win hconn hxu.symm hdom hGx_win)
    have hGu_win : ∀ u : V, CopNumberLeTwo (G.induce {x : V | x ≠ u}) := by
      intro u
      have hV_ge3 : 3 ≤ Fintype.card V := by
        by_contra hlt
        exact hnot_win (copNumberLeTwo_of_card_le_two G (by omega))
      have : Nonempty {x : V | x ≠ u} := by
        have : 1 < Fintype.card V := by omega
        obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card this
        by_cases hau : a = u
        · exact ⟨⟨b, fun h => hab (hau.trans h.symm)⟩⟩
        · exact ⟨⟨a, hau⟩⟩
      have hlt : Fintype.card {x : V | x ≠ u} < Fintype.card V := by
        apply Fintype.card_lt_of_injective_not_surjective Subtype.val Subtype.val_injective
        intro hsurj; obtain ⟨⟨w, hw⟩, hwu⟩ := hsurj u; exact hw hwu
      exact hmin _ hlt (hGu_conn u)
    -- Lemma 4.1b: G - N[u] is nonempty, has no isolated vertex, and is connected!
    have hR_props : ∀ u : V,
        Nonempty {x : V | ¬ ClosedAdj G u x} ∧
        (∀ v : {x : V | ¬ ClosedAdj G u x}, ∃ w : {x : V | ¬ ClosedAdj G u x},
          (G.induce {x : V | ¬ ClosedAdj G u x}).Adj v w) ∧
        (G.induce {x : V | ¬ ClosedAdj G u x}).Connected := by
      intro u
      have hne : Nonempty {x : V | ¬ ClosedAdj G u x} := by
        by_contra hempty
        rw [not_nonempty_iff] at hempty
        apply hnot_win
        refine ⟨u, u, fun r => copWinFrom_of_closedAdj (Or.inl ?_)⟩
        by_contra hnot
        exact hempty.false ⟨r, hnot⟩
      have hnoiso : ∀ v : {x : V | ¬ ClosedAdj G u x}, ∃ w : {x : V | ¬ ClosedAdj G u x},
          (G.induce {x : V | ¬ ClosedAdj G u x}).Adj v w := by
        intro v
        by_contra hiso
        push Not at hiso
        have hdom : ∀ w : V, G.Adj v.val w → ClosedAdj G u w := by
          intro w hvw
          by_contra hnot
          exact hiso ⟨w, hnot⟩ hvw
        have huv : u ≠ v.val := fun h => v.property (Or.inl h)
        exact hnot_win (shadow_win hconn huv hdom (hGu_win v.val))
      exact ⟨hne, hnoiso, connected_of_no_isolated (isTwoK2Free_induce h2k2 _) hnoiso⟩
    -- Lemma 4.3: G has no type-I trap!
    have hno_typeI : ∀ u x v : V, IsTrappedBy G u x v → G.Adj u x → ¬ ClosedAdj G u v → False := by
      intro u x v htrap hux hvR
      obtain ⟨_, hR_noiso, hR_conn⟩ := hR_props u
      obtain ⟨⟨w, hwR⟩, hvw⟩ := hR_noiso ⟨v, hvR⟩
      have hwin_vw : CopWinFrom G (v, w) u := by
        by_cases hwx : G.Adj w x
        · exact CopWinFrom.step (closedAdj_refl G v) (Or.inr hwx)
            (copWinFrom_of_trap (fun z hz => (htrap.2.2 z hz).symm))
        · have hxv : G.Adj x v := (cantmove h2k2 hvR hwR hvw hux).resolve_right (fun h => hwx h.symm)
          exact CopWinFrom.step (Or.inr hxv.symm) (Or.inr hvw.symm)
            (copWinFrom_of_trap htrap.2.2)
      exact hnot_win (win_of_edge_win h2k2 (hGu_win u) hR_conn hR_noiso hvR hwR hvw hwin_vw)
    -- Lemma 4.5: G has no type-II trap!
    have hno_typeII : ∀ u x₁ x₂ : V, IsTrappedBy G u x₁ x₂ → G.Adj u x₁ → G.Adj u x₂ → False := by
      intro u x₁ x₂ htrap hux₁ hux₂
      obtain ⟨hR_ne, hR_noiso, hR_conn⟩ := hR_props u
      -- Every w ∈ R is adjacent to x₁ iff adjacent to x₂
      have hsame_adj : ∀ w : V, ¬ ClosedAdj G u w → (G.Adj x₁ w ↔ G.Adj x₂ w) := by
        have hone : ∀ (y₁ y₂ : V), IsTrappedBy G u y₁ y₂ → G.Adj u y₁ → G.Adj u y₂ →
            ∀ w : V, ¬ ClosedAdj G u w → G.Adj y₁ w → G.Adj y₂ w := by
          intro y₁ y₂ htr huy₁ huy₂ w hwR hy₁w
          by_contra hno
          obtain ⟨⟨v, hvR⟩, hwv⟩ := hR_noiso ⟨w, hwR⟩
          have hy₂v : G.Adj y₂ v := (cantmove h2k2 hwR hvR hwv huy₂).resolve_left hno
          have hwin_wv : CopWinFrom G (w, v) u :=
            CopWinFrom.step (Or.inr hy₁w.symm) (Or.inr hy₂v.symm)
              (copWinFrom_of_trap htr.2.2)
          exact hnot_win (win_of_edge_win h2k2 (hGu_win u) hR_conn hR_noiso hwR hvR hwv hwin_wv)
        intro w hwR
        refine ⟨hone x₁ x₂ htrap hux₁ hux₂ w hwR,
          hone x₂ x₁ ⟨htrap.2.1, htrap.1, fun z hz => (htrap.2.2 z hz).symm⟩ hux₂ hux₁ w hwR⟩
      let R : Set V := {x : V | ¬ ClosedAdj G u x}
      let GR := G.induce R
      let A : Set R := {w : R | G.Adj x₁ w.val}
      let B : Set R := {w : R | ¬ G.Adj x₁ w.val}
      have hpart : ∀ w : R, w ∈ A ∨ w ∈ B := fun w => em _
      have hdisj : ∀ w : R, ¬ (w ∈ A ∧ w ∈ B) := fun _ ⟨h1, h2⟩ => h2 h1
      have hB_ind : ∀ w₁ ∈ B, ∀ w₂ ∈ B, ¬ GR.Adj w₁ w₂ := by
        intro w₁ hw₁ w₂ hw₂ hadj
        rcases cantmove h2k2 w₁.property w₂.property hadj hux₁ with h1 | h2
        · exact hw₁ h1
        · exact hw₂ h2
      have hA_ind : ∀ w₁ ∈ A, ∀ w₂ ∈ A, ¬ GR.Adj w₁ w₂ := by
        intro w₁ hw₁ w₂ hw₂ hadj
        have hx₂w₂ : G.Adj x₂ w₂.val := (hsame_adj w₂.val w₂.property).mp hw₂
        have hwin_12 : CopWinFrom G (w₁.val, w₂.val) u :=
          CopWinFrom.step (Or.inr hw₁.symm) (Or.inr hx₂w₂.symm)
            (copWinFrom_of_trap htrap.2.2)
        exact hnot_win (win_of_edge_win h2k2 (hGu_win u) hR_conn hR_noiso
          w₁.property w₂.property hadj hwin_12)
      have hB_ne : B.Nonempty := by
        obtain ⟨w⟩ := hR_ne
        by_cases hwA : w ∈ A
        · obtain ⟨z, hwz⟩ := hR_noiso w
          exact ⟨z, fun hzA => hA_ind w hwA z hzA hwz⟩
        · exact ⟨w, hwA⟩
      obtain ⟨b, hbB, hb_univ⟩ :=
        bipartite_universal (isTwoK2Free_induce h2k2 R) hR_conn A B hpart hdisj hA_ind hB_ind hB_ne
      -- Then x₁ is a type-I trap, trapped by u and b.val!
      have htrap_x1 : IsTrappedBy G x₁ u b.val := by
        refine ⟨hux₁.ne, fun h => b.property (Or.inr (h ▸ hux₁)), fun z hz => ?_⟩
        by_cases hzu : ClosedAdj G u z
        · exact Or.inl hzu
        · rcases hz with rfl | hx₁z
          · exact Or.inl (Or.inr hux₁)
          · exact Or.inr (Or.inr (hb_univ ⟨z, hzu⟩ hx₁z))
      have hb_not_x1 : ¬ ClosedAdj G x₁ b.val := by
        rintro (heq | hadj)
        · exact b.property (Or.inr (heq ▸ hux₁))
        · exact hbB hadj
      exact hno_typeI x₁ u b.val htrap_x1 hux₁.symm hb_not_x1
    -- Finally, G has no trap at all, hence no connected trap!
    have hno_trap : ¬ HasConnectedTrap G := by
      rintro ⟨u, x₁, x₂, htrap, _⟩
      -- Note u ∈ N[u] ⊆ N[x₁] ∪ N[x₂], so at least one of x₁, x₂ is adjacent to u!
      have hu_cov := htrap.2.2 u (closedAdj_refl G u)
      have hadj_or : G.Adj u x₁ ∨ G.Adj u x₂ := by
        rcases hu_cov with h1 | h2
        · exact Or.inl (h1.resolve_left htrap.1).symm
        · exact Or.inr (h2.resolve_left htrap.2.1).symm
      by_cases h1 : G.Adj u x₁
      · by_cases h2 : G.Adj u x₂
        · exact hno_typeII u x₁ x₂ htrap h1 h2
        · exact hno_typeI u x₁ x₂ htrap h1 (fun h => h2 (h.resolve_left htrap.2.1.symm))
      · have h2 : G.Adj u x₂ := hadj_or.resolve_left h1
        have htrap' : IsTrappedBy G u x₂ x₁ := ⟨htrap.2.1, htrap.1, fun z hz => (htrap.2.2 z hz).symm⟩
        exact hno_typeI u x₂ x₁ htrap' h2 (fun h => h1 (h.resolve_left htrap.1.symm))
    -- By Proposition 3.4, |V| ≤ 2 or G ≃ C_5, contradiction!
    rcases exists_connectedTrap_or_small n G hcard hconn h2k2 with hle2 | hC5 | hct
    · exact hnot_win (copNumberLeTwo_of_card_le_two G hle2)
    · exact hnot_win (copNumberLeTwo_of_isC5 hC5)
    · exact hno_trap hct

private theorem main_proof : type_of% @OMA.S_arxiv_1903_11484.main := by
  intro V _ _ G hconn h2k2
  exact copNumberLeTwo_aux (Fintype.card V) G rfl hconn h2k2

end OMA.P_arxiv_1903_11484

theorem OMA.solution : type_of% @OMA.S_arxiv_1903_11484.main :=
  OMA.P_arxiv_1903_11484.main_proof

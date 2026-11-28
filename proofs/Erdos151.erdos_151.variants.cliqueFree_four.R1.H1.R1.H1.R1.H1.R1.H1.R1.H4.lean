import OMAReductions.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1_H1_R1_H1_R1

-- Credit: @TienDat8605

/-! The seven-vertex link extension and the edge/triangle inequality for
edge-minimal triangle Ramsey graphs. The link proof is from SanskarX10's
merged ancestor H4. The incidence-matrix density proof and oriented triangle
count are from princek0's R2.H1, also used in mythintios's PR #9753.
The bridge below identifies the two representations of an edge coloring. -/

namespace Erdos151Seven

private abbrev V := Fin 7

private def TF (G : SimpleGraph V) : Prop :=
  ∀ x y z, G.Adj x y → G.Adj y z → G.Adj z x → False

private def Saturated (G : SimpleGraph V) : Prop :=
  ∀ x y, x ≠ y → ¬ G.Adj x y → ∃ z, G.Adj x z ∧ G.Adj y z

private def Bip (G : SimpleGraph V) : Prop :=
  ∃ d : V → Bool, ∀ x y, G.Adj x y → d x ≠ d y

private def HasC5 (G : SimpleGraph V) (a : Equiv.Perm V) : Prop :=
  G.Adj (a 0) (a 1) ∧ G.Adj (a 1) (a 2) ∧ G.Adj (a 2) (a 3) ∧
    G.Adj (a 3) (a 4) ∧ G.Adj (a 4) (a 0)

private def onCycle (i : Fin 5) : V :=
  Fin.castLE (show 5 ≤ 7 by decide) i

private def OutsideTwo (G : SimpleGraph V) (a : Equiv.Perm V) : Prop :=
  ∀ u : V, (u = a 5 ∨ u = a 6) →
    ∃ i j : Fin 5, i ≠ j ∧
      ∀ l : Fin 5, G.Adj u (a (onCycle l)) ↔ l = i ∨ l = j

private lemma exists_maximal_tf (k : ℕ) (L : SimpleGraph (Fin k))
    (hk : k ≤ 7) (ht : L.CliqueFree 3) :
    ∃ (f : Fin k ↪ V) (M : SimpleGraph V),
      TF M ∧ Saturated M ∧ ∀ x y, L.Adj x y → M.Adj (f x) (f y) := by
  classical
    let f : Fin k ↪ V :=
      ⟨Fin.castLE hk, Fin.castLE_injective hk⟩
    let B : V → V → Prop :=
      fun x y => ∃ i j, f i = x ∧ f j = y ∧ L.Adj i j
    have hBsym : ∀ x y, B x y → B y x := by
      intro x y h
      rcases h with ⟨i, j, hix, hjy, hij⟩
      exact ⟨j, i, hjy, hix, L.symm.symm i j hij⟩
    have hBloopy : ∀ x, ¬ B x x := by
      intro x h
      rcases h with ⟨i, j, hix, hjx, hij⟩
      have heq : i = j := f.injective (hix.trans hjx.symm)
      subst j
      exact L.loopless.irrefl i hij
    have hBtf : ∀ x y z, B x y → B y z → B z x → False := by
      intro x y z hxy hyz hzx
      rcases hxy with ⟨i, j, hix, hjy, hij⟩
      rcases hyz with ⟨j', l, hj'y, hlz, hjl⟩
      rcases hzx with ⟨l', i', hl'z, hix', hli⟩
      have hj : j = j' := f.injective (hjy.trans hj'y.symm)
      have hl : l = l' := f.injective (hlz.trans hl'z.symm)
      have hi : i' = i := f.injective (hix'.trans hix.symm)
      subst j'
      subst l'
      subst i'
      have hneij : i ≠ j := by
        intro heq
        subst j
        exact L.loopless.irrefl i hij
      have hnejl : j ≠ l := by
        intro heq
        subst l
        exact L.loopless.irrefl j hjl
      have hneil : i ≠ l := by
        intro heq
        subst l
        exact L.loopless.irrefl i hli
      have hji : L.Adj j i := L.symm.symm i j hij
      have hlj : L.Adj l j := L.symm.symm j l hjl
      have hil : L.Adj i l := L.symm.symm l i hli
      have hClique : L.IsClique (↑({i, j, l} : Finset (Fin k))) := by
        intro a ha b hb hab
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
        rcases ha with rfl | rfl | rfl <;>
          rcases hb with rfl | rfl | rfl <;>
          first
          | exact False.elim (hab rfl)
          | exact hij
          | exact hji
          | exact hjl
          | exact hlj
          | exact hli
          | exact hil
      have hcard : ({i, j, l} : Finset (Fin k)).card = 3 := by
        simp [hneij, hnejl, hneil]
      have hNC : L.IsNClique 3 ({i, j, l} : Finset (Fin k)) :=
        ⟨hClique, hcard⟩
      exact (ht {i, j, l}) hNC
    let S₀ : Finset (V × V) := Finset.univ.filter fun p => B p.1 p.2
    have hS₀sym : ∀ x y, (x, y) ∈ S₀ → (y, x) ∈ S₀ := by
      intro x y h
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, hBsym x y (Finset.mem_filter.mp h).2⟩
    have hS₀loop : ∀ x, (x, x) ∉ S₀ := by
      intro x h
      exact hBloopy x (Finset.mem_filter.mp h).2
    have hS₀tf : ∀ x y z, (x, y) ∈ S₀ → (y, z) ∈ S₀ → (z, x) ∈ S₀ → False := by
      intro x y z hxy hyz hzx
      exact hBtf x y z
        (Finset.mem_filter.mp hxy).2
        (Finset.mem_filter.mp hyz).2
        (Finset.mem_filter.mp hzx).2
    have hS₀base : ∀ i j, L.Adj i j → (f i, f j) ∈ S₀ := by
      intro i j hij
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, ⟨i, j, rfl, rfl, hij⟩⟩
    let Good (s : Finset (V × V)) : Prop :=
      (∀ x y, (x, y) ∈ s → (y, x) ∈ s) ∧
      (∀ x, (x, x) ∉ s) ∧
      (∀ x y z, (x, y) ∈ s → (y, z) ∈ s → (z, x) ∈ s → False) ∧
      (∀ i j, L.Adj i j → (f i, f j) ∈ s)
    let C : Finset (Finset (V × V)) := Finset.univ.powerset.filter Good
    have hC : C.Nonempty := by
      refine ⟨S₀, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
      · exact Finset.mem_powerset.mpr (by intro p hp; exact Finset.mem_univ p)
      · exact ⟨hS₀sym, hS₀loop, hS₀tf, hS₀base⟩
    have hnset : (C.image Finset.card).Nonempty := by
      rcases hC with ⟨s, hs⟩
      exact ⟨s.card, Finset.mem_image.mpr ⟨s, hs, rfl⟩⟩
    let n : ℕ := (C.image Finset.card).max' hnset
    have hnmem : n ∈ C.image Finset.card := Finset.max'_mem _ _
    obtain ⟨S, hSC, hSn⟩ := Finset.mem_image.mp hnmem
    have hSgood : Good S := (Finset.mem_filter.mp hSC).2
    have hSmax (T : Finset (V × V)) (hT : Good T) : T.card ≤ S.card := by
      have hTm : T ∈ C := Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (by intro p hp; exact Finset.mem_univ p), hT⟩
      have hcard : T.card ∈ C.image Finset.card :=
        Finset.mem_image.mpr ⟨T, hTm, rfl⟩
      calc
        T.card ≤ n := Finset.le_max' _ _ hcard
        _ = S.card := hSn.symm
    let M : SimpleGraph V :=
      { Adj := fun x y => (x, y) ∈ S
        symm := ⟨by
          intro x y h
          exact hSgood.1 x y h⟩
        loopless := ⟨by
          intro x h
          exact hSgood.2.1 x h⟩ }
    refine ⟨f, M, ?_, ?_, ?_⟩
    · intro x y z hxy hyz hzx
      exact hSgood.2.2.1 x y z hxy hyz hzx
    · intro x y hxy hnot
      by_contra hsat
      have hNoCommon : ∀ z, ¬ ((x, z) ∈ S ∧ (y, z) ∈ S) := by
        intro z hz
        apply hsat
        exact ⟨z, by simpa [M] using hz.1, by simpa [M] using hz.2⟩
      let T : Finset (V × V) := S ∪ {(x, y), (y, x)}
      let Extra (a b : V) : Prop :=
        (a = x ∧ b = y) ∨ (a = y ∧ b = x)
      have memT (a b : V) :
          (a, b) ∈ T ↔ (a, b) ∈ S ∨ Extra a b := by
        simp [T, Extra, Prod.mk.injEq]
        tauto
      have hextra (a b : V) : Extra a b → Extra b a := by
        intro h
        rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact Or.inr ⟨hb, ha⟩
        · exact Or.inl ⟨hb, ha⟩
      have hTloop : ∀ a, (a, a) ∉ T := by
        intro a ha
        rcases (memT a a).mp ha with hs | he
        · exact hSgood.2.1 a hs
        · rcases he with ⟨ha, hb⟩ | ⟨ha, hb⟩
          · exact hxy (ha.symm.trans hb)
          · exact hxy.symm (ha.symm.trans hb)
      have htwoNew : ∀ a b c, Extra a b → Extra b c → c = a := by
        intro a b c hab hbc
        rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · subst a
          subst b
          rcases hbc with ⟨hbx, hcy⟩ | ⟨hby, hcx⟩
          · exact False.elim (hxy.symm hbx)
          · exact hcx
        · subst a
          subst b
          rcases hbc with ⟨hbx, hcy⟩ | ⟨hby, hcx⟩
          · exact hcy
          · exact False.elim (hxy hby)
      have hsingleNew : ∀ a b c, Extra a b →
          (b, c) ∈ S → (c, a) ∈ S → False := by
        intro a b c hab hbc hca
        rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · subst a
          subst b
          exact hNoCommon c ⟨hSgood.1 c x hca, hbc⟩
        · subst a
          subst b
          exact hNoCommon c ⟨hbc, hSgood.1 c y hca⟩
      have hExtraLoop : ∀ a, ¬ Extra a a := by
        intro a he
        rcases he with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact hxy (ha.symm.trans hb)
        · exact hxy.symm (ha.symm.trans hb)
      have hTgood : Good T := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro a b hab
          rcases (memT a b).mp hab with hs | he
          · exact (memT b a).mpr (Or.inl (hSgood.1 a b hs))
          · exact (memT b a).mpr (Or.inr (hextra a b he))
        · exact hTloop
        · intro a b c hab hbc hca
          rcases (memT a b).mp hab with habS | habE
          · rcases (memT b c).mp hbc with hbcS | hbcE
            · rcases (memT c a).mp hca with hcaS | hcaE
              · exact hSgood.2.2.1 a b c habS hbcS hcaS
              · exact hsingleNew c a b hcaE habS hbcS
            · rcases (memT c a).mp hca with hcaS | hcaE
              · exact hsingleNew b c a hbcE hcaS habS
              · have heq : a = b := htwoNew b c a hbcE hcaE
                subst a
                exact hSgood.2.1 b habS
          · rcases (memT b c).mp hbc with hbcS | hbcE
            · rcases (memT c a).mp hca with hcaS | hcaE
              · exact hsingleNew a b c habE hbcS hcaS
              · have heq : b = c := htwoNew c a b hcaE habE
                subst c
                exact hSgood.2.1 b hbcS
            · rcases (memT c a).mp hca with hcaS | hcaE
              · have heq : c = a := htwoNew a b c habE hbcE
                subst c
                exact hSgood.2.1 a hcaS
              · have heq : c = a := htwoNew a b c habE hbcE
                subst c
                exact hExtraLoop a hcaE
        · intro i j hij
          exact (memT (f i) (f j)).mpr
            (Or.inl (hSgood.2.2.2 i j hij))
      have hnew : (x, y) ∉ S := by
        simpa [M] using hnot
      have hstrict : S ⊂ T := by
        refine ⟨Finset.subset_union_left, ?_⟩
        intro hTS
        have hxyT : (x, y) ∈ T :=
          (memT x y).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
        exact hnew (hTS hxyT)
      have hcard : S.card < T.card := Finset.card_lt_card hstrict
      exact (not_le_of_gt hcard) (hSmax T hTgood)
    · intro i j hij
      exact hSgood.2.2.2 i j hij

private lemma exists_c5_of_not_bipartite (M : SimpleGraph V)
    (ht : TF M) (hs : Saturated M) (hb : ¬ Bip M) :
    ∃ a : Equiv.Perm V, HasC5 M a := by
  classical
    by_contra hno
    have swapAt (p : Equiv.Perm V) (i b : V) :
        (Equiv.swap (p i) b * p) i = b := by
      simp
    have swapKeep (p : Equiv.Perm V) (i j b : V) (hij : i ≠ j)
        (hb : b ≠ p j) :
        (Equiv.swap (p i) b * p) j = p j := by
      have hp : p j ≠ p i := by
        intro h
        exact hij (p.injective h).symm
      change Equiv.swap (p i) b (p j) = p j
      simp [Equiv.swap_apply_def, hp, hb.symm]
    let d : V → Bool := fun x => if M.Adj 0 x then true else false
    have hB : Bip M := by
      refine ⟨d, ?_⟩
      intro x y hxy
      by_cases hx : M.Adj 0 x
      · by_cases hy : M.Adj 0 y
        · have htri : False := ht 0 x y hx hxy (M.symm.symm 0 y hy)
          exact False.elim htri
        · simp [d, hx, hy]
      · by_cases hy : M.Adj 0 y
        · simp [d, hx, hy]
        · have hx0 : x ≠ 0 := by
            intro h
            subst x
            exact hy hxy
          have hy0 : y ≠ 0 := by
            intro h
            subst y
            exact hx (M.symm.symm x 0 hxy)
          have hxy' : x ≠ y := by
            intro h
            subst y
            exact M.loopless.irrefl x hxy
          obtain ⟨z, h0z, hxz⟩ := hs 0 x hx0.symm hx
          obtain ⟨w, h0w, hyw⟩ := hs 0 y hy0.symm hy
          have hz0 : z ≠ 0 := by
            intro h
            subst z
            exact M.loopless.irrefl 0 h0z
          have hzx : z ≠ x := by
            intro h
            subst z
            exact M.loopless.irrefl x hxz
          have hzy : z ≠ y := by
            intro h
            subst z
            exact hy h0z
          have hw0 : w ≠ 0 := by
            intro h
            subst w
            exact M.loopless.irrefl 0 h0w
          have hwx : w ≠ x := by
            intro h
            subst w
            exact hx h0w
          have hwy : w ≠ y := by
            intro h
            subst w
            exact M.loopless.irrefl y hyw
          have hzw : z ≠ w := by
            intro h
            subst w
            exact ht x y z hxy hyw (M.symm.symm x z hxz)
          let p0 : Equiv.Perm V := 1
          have hp00 : p0 0 = 0 := by simp [p0]
          let p1 : Equiv.Perm V := Equiv.swap (p0 1) z * p0
          have hp10 : p1 0 = 0 := by
            change (Equiv.swap (p0 1) z * p0) 0 = 0
            rw [swapKeep p0 1 0 z (by decide) (by simpa [hp00] using hz0)]
            exact hp00
          have hp11 : p1 1 = z := by
            change (Equiv.swap (p0 1) z * p0) 1 = z
            exact swapAt p0 1 z
          let p2 : Equiv.Perm V := Equiv.swap (p1 2) x * p1
          have hp20 : p2 0 = 0 := by
            change (Equiv.swap (p1 2) x * p1) 0 = 0
            rw [swapKeep p1 2 0 x (by decide) (by simpa [hp10] using hx0)]
            exact hp10
          have hp21 : p2 1 = z := by
            change (Equiv.swap (p1 2) x * p1) 1 = z
            rw [swapKeep p1 2 1 x (by decide) (by simpa [hp11] using hzx.symm)]
            exact hp11
          have hp22 : p2 2 = x := by
            change (Equiv.swap (p1 2) x * p1) 2 = x
            exact swapAt p1 2 x
          let p3 : Equiv.Perm V := Equiv.swap (p2 3) y * p2
          have hp30 : p3 0 = 0 := by
            change (Equiv.swap (p2 3) y * p2) 0 = 0
            rw [swapKeep p2 3 0 y (by decide) (by simpa [hp20] using hy0)]
            exact hp20
          have hp31 : p3 1 = z := by
            change (Equiv.swap (p2 3) y * p2) 1 = z
            rw [swapKeep p2 3 1 y (by decide) (by simpa [hp21] using hzy.symm)]
            exact hp21
          have hp32 : p3 2 = x := by
            change (Equiv.swap (p2 3) y * p2) 2 = x
            rw [swapKeep p2 3 2 y (by decide) (by simpa [hp22] using hxy'.symm)]
            exact hp22
          have hp33 : p3 3 = y := by
            change (Equiv.swap (p2 3) y * p2) 3 = y
            exact swapAt p2 3 y
          let p4 : Equiv.Perm V := Equiv.swap (p3 4) w * p3
          have hp40 : p4 0 = 0 := by
            change (Equiv.swap (p3 4) w * p3) 0 = 0
            rw [swapKeep p3 4 0 w (by decide) (by simpa [hp30] using hw0)]
            exact hp30
          have hp41 : p4 1 = z := by
            change (Equiv.swap (p3 4) w * p3) 1 = z
            rw [swapKeep p3 4 1 w (by decide) (by simpa [hp31] using hzw.symm)]
            exact hp31
          have hp42 : p4 2 = x := by
            change (Equiv.swap (p3 4) w * p3) 2 = x
            rw [swapKeep p3 4 2 w (by decide) (by simpa [hp32] using hwx)]
            exact hp32
          have hp43 : p4 3 = y := by
            change (Equiv.swap (p3 4) w * p3) 3 = y
            rw [swapKeep p3 4 3 w (by decide) (by simpa [hp33] using hwy)]
            exact hp33
          have hp44 : p4 4 = w := by
            change (Equiv.swap (p3 4) w * p3) 4 = w
            exact swapAt p3 4 w
          have hcycle : HasC5 M p4 := by
            change M.Adj (p4 0) (p4 1) ∧ M.Adj (p4 1) (p4 2) ∧
              M.Adj (p4 2) (p4 3) ∧ M.Adj (p4 3) (p4 4) ∧
              M.Adj (p4 4) (p4 0)
            rw [hp40, hp41, hp42, hp43, hp44]
            exact ⟨h0z, M.symm.symm x z hxz, hxy, hyw,
              M.symm.symm 0 w h0w⟩
          exact False.elim (hno ⟨p4, hcycle⟩)
    exact hb hB

private lemma outside_deg_two_in_c5 (M : SimpleGraph V)
    (ht : TF M) (hs : Saturated M) (a : Equiv.Perm V) (ha : HasC5 M a) :
    OutsideTwo M a := by
  intro u hu
  let x : Fin 5 → V := fun i => a (onCycle i)
  let P : Fin 5 → Prop := fun i => M.Adj u (x i)
  have five (i : Fin 5) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
    have hi : i.val < 5 := i.isLt
    have hv : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 := by omega
    rcases hv with h | h | h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h))))
  have idx (r : Fin 5) :
      (r + 1) + 1 = r + 2 ∧ (r + 2) + 1 = r + 3 ∧
      (r + 3) + 2 = r ∧ (r + 4) + 1 = r ∧
      r + 2 ≠ r ∧ r + 3 ≠ r := by
    rcases five r with rfl | rfl | rfl | rfl | rfl <;> decide
  have offsets (r l : Fin 5) :
      l = r ∨ l = r + 1 ∨ l = r + 2 ∨ l = r + 3 ∨ l = r + 4 := by
    rcases five r with rfl | rfl | rfl | rfl | rfl <;>
      rcases five l with rfl | rfl | rfl | rfl | rfl <;> decide
  have rev {b c : V} (h : M.Adj b c) : M.Adj c b := M.symm.symm b c h
  obtain ⟨h01, h12, h23, h34, h40⟩ := ha
  have edge (r : Fin 5) : M.Adj (x r) (x (r + 1)) := by
    rcases five r with rfl | rfl | rfl | rfl | rfl
    · exact h01
    · exact h12
    · exact h23
    · exact h34
    · exact h40
  have edge23 (r : Fin 5) : M.Adj (x (r + 2)) (x (r + 3)) := by
    rw [← (idx r).2.1]
    exact edge (r + 2)
  have edge40 (r : Fin 5) : M.Adj (x (r + 4)) (x r) := by
    have h := edge (r + 4)
    rw [(idx r).2.2.2.1] at h
    exact h
  have chord (r : Fin 5) : ¬ M.Adj (x r) (x (r + 2)) := by
    intro h
    have hnext := edge (r + 1)
    rw [(idx r).1] at hnext
    exact ht (x r) (x (r + 1)) (x (r + 2)) (edge r) hnext (rev h)
  have ind (i j : Fin 5) (e : M.Adj (x i) (x j)) (hi : P i) (hj : P j) : False :=
    ht u (x i) (x j) hi e (rev (show M.Adj u (x j) from hj))
  have cover (z : V) : (∃ i : Fin 5, z = x i) ∨ z = a 5 ∨ z = a 6 := by
    let w : V := a.symm z
    have hw : a w = z := a.apply_symm_apply z
    have hwlt : w.val < 7 := w.isLt
    by_cases h : w.val < 5
    · let i : Fin 5 := ⟨w.val, h⟩
      have he : w = onCycle i := Fin.ext rfl
      exact Or.inl ⟨i, hw.symm.trans (congrArg (fun b : V => a b) he)⟩
    · have hv : w.val = 5 ∨ w.val = 6 := by omega
      rcases hv with h5 | h6
      · have he : w = 5 := Fin.ext h5
        exact Or.inr (Or.inl (hw.symm.trans (congrArg (fun b : V => a b) he)))
      · have he : w = 6 := Fin.ext h6
        exact Or.inr (Or.inr (hw.symm.trans (congrArg (fun b : V => a b) he)))
  have une (i : Fin 5) : u ≠ x i := by
    intro he
    have hi : i.val < 5 := i.isLt
    rcases hu with h | h
    · have hv := congrArg (fun b : V => b.val) (a.injective (h.symm.trans he))
      change 5 = i.val at hv
      omega
    · have hv := congrArg (fun b : V => b.val) (a.injective (h.symm.trans he))
      change 6 = i.val at hv
      omega
  obtain ⟨v, hv⟩ : ∃ v : V, ∀ z : V,
      (z = a 5 ∨ z = a 6) → z ≠ u → z = v := by
    rcases hu with h | h
    · refine ⟨a 6, ?_⟩
      intro z hz hn
      exact hz.elim (fun hz5 => False.elim (hn (hz5.trans h.symm))) id
    · refine ⟨a 5, ?_⟩
      intro z hz hn
      exact hz.elim id (fun hz6 => False.elim (hn (hz6.trans h.symm)))
  have force (i : Fin 5) (hi : ¬ P i)
      (hn : ∀ j : Fin 5, P j → ¬ M.Adj (x i) (x j)) : M.Adj v (x i) := by
    obtain ⟨z, huz, hiz⟩ := hs u (x i) (une i) hi
    rcases cover z with ⟨j, hj⟩ | hz
    · rw [hj] at huz hiz
      exact False.elim (hn j huz hiz)
    · have hzu : z ≠ u := by
        intro he
        rw [he] at huz
        exact M.loopless.irrefl u huz
      rw [hv z hz hzu] at hiz
      exact rev hiz
  have pair : ∃ i j : Fin 5, i ≠ j ∧ P i ∧ P j := by
    classical
    apply Classical.byContradiction
    intro hn
    by_cases hex : ∃ r : Fin 5, P r
    · obtain ⟨r, hr⟩ := hex
      have unique (j : Fin 5) (hj : P j) : j = r := by
        apply Classical.byContradiction
        intro hne
        exact hn ⟨j, r, hne, hj, hr⟩
      have nv2 : ¬ P (r + 2) := fun h => (idx r).2.2.2.2.1 (unique _ h)
      have nv3 : ¬ P (r + 3) := fun h => (idx r).2.2.2.2.2 (unique _ h)
      have e2 := force (r + 2) nv2 (by
        intro j hj he
        rw [unique j hj] at he
        exact chord r (rev he))
      have e3 := force (r + 3) nv3 (by
        intro j hj he
        rw [unique j hj] at he
        apply chord (r + 3)
        rw [(idx r).2.2.1]
        exact he)
      exact ht v (x (r + 2)) (x (r + 3)) e2 (edge23 r) (rev e3)
    · have empty (i : Fin 5) : ¬ P i := fun hi => hex ⟨i, hi⟩
      have e0 := force 0 (empty 0) (fun j hj => False.elim (empty j hj))
      have e1 := force 1 (empty 1) (fun j hj => False.elim (empty j hj))
      exact ht v (x 0) (x 1) e0 h01 (rev e1)
  have pack (r : Fin 5) (hr : P r) (hr2 : P (r + 2)) :
      ∃ i j : Fin 5, i ≠ j ∧ ∀ l : Fin 5, P l ↔ l = i ∨ l = j := by
    refine ⟨r, r + 2, (idx r).2.2.2.2.1.symm, ?_⟩
    intro l
    constructor
    · intro hl
      rcases offsets r l with h | h | h | h | h
      · exact Or.inl h
      · rw [h] at hl
        exact False.elim (ind r (r + 1) (edge r) hr hl)
      · exact Or.inr h
      · rw [h] at hl
        exact False.elim (ind (r + 2) (r + 3) (edge23 r) hr2 hl)
      · rw [h] at hl
        exact False.elim (ind (r + 4) r (edge40 r) hl hr)
    · intro hl
      exact hl.elim (fun h => h.symm ▸ hr) (fun h => h.symm ▸ hr2)
  obtain ⟨i, j, hij, hi, hj⟩ := pair
  rcases offsets i j with h | h | h | h | h
  · exact False.elim (hij h.symm)
  · rw [h] at hj
    exact False.elim (ind i (i + 1) (edge i) hi hj)
  · rw [h] at hj
    exact pack i hi hj
  · apply pack j hj
    rw [h, (idx i).2.2.1]
    exact hi
  · rw [h] at hj
    exact False.elim (ind (i + 4) i (edge40 i) hj hi)

private def cycleEdges : List (V × V) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]

private def templateEdges (t : Fin 3) : List (V × V) :=
  cycleEdges ++
    (match t.val with
      | 0 => [(5, 0), (5, 2), (6, 0), (6, 2)]
      | 1 => [(5, 0), (5, 2), (6, 1), (6, 3), (5, 6)]
      | _ => [(5, 0), (5, 2), (6, 2), (6, 4)])

private def TemplateAdj (t : Fin 3) (x y : V) : Prop :=
  (x, y) ∈ templateEdges t ∨ (y, x) ∈ templateEdges t

private abbrev CoverStep (i j : Fin 5) : Prop := j = i + 1 ∨ i = j + 1

private abbrev CoverDisjoint (i j k l : Fin 5) : Prop :=
  i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l

private def coverPattern (i j k l : Fin 5) : List (V × V) :=
  cycleEdges ++
    ([(5, onCycle i), (5, onCycle j), (6, onCycle k), (6, onCycle l)] ++
      (if CoverDisjoint i j k l then [(5, 6)] else []))

private def coverRelabel (r : Fin 5) (b : Bool) (x : V) : V :=
  if h : x.val < 5 then
    let m : Fin 5 := ⟨x.val, h⟩
    onCycle (if b then r - m else r + m)
  else x

private def coverInverse (r : Fin 5) (b : Bool) : Fin 5 :=
  if b then r else 0 - r

local instance (t : Fin 3) (x y : V) : Decidable (TemplateAdj t x y) := by
  unfold TemplateAdj
  infer_instance

private theorem cover_relabel_inverse :
    (∀ (r : Fin 5) (b : Bool) (x : V),
       coverRelabel (coverInverse r b) b (coverRelabel r b x) = x) ∧
    (∀ (r : Fin 5) (b : Bool) (x : V),
       coverRelabel r b (coverRelabel (coverInverse r b) b x) = x) := by
  constructor <;> decide

private theorem cover_cycle_facts :
    (∀ m : Fin 5, m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4) ∧
    (∀ m : Fin 5, (onCycle m, onCycle (m + 1)) ∈ cycleEdges) ∧
    (∀ m n : Fin 5, m ≠ n → ¬ CoverStep m n →
       ∃ z : Fin 5, CoverStep m z ∧ CoverStep n z) := by
  constructor
  · decide
  · constructor <;> decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem cover_pattern_certificate :
    ∀ i j k l : Fin 5, i ≠ j → k ≠ l → ¬ CoverStep i j → ¬ CoverStep k l →
      ∃ (r : Fin 5) (b : Bool) (t : Fin 3),
        (coverPattern i j k l).all (fun e =>
          decide (TemplateAdj t (coverRelabel r b e.1) (coverRelabel r b e.2))) = true := by
  decide

private lemma three_templates_cover (M : SimpleGraph V)
    (ht : TF M) (_hs : Saturated M) (a : Equiv.Perm V)
    (ha : HasC5 M a) (ho : OutsideTwo M a) :
    ∃ (t : Fin 3) (e : Equiv.Perm V),
      ∀ x y, M.Adj x y → TemplateAdj t (e x) (e y) := by
  obtain ⟨i, j, hij, h5⟩ := ho (a 5) (Or.inl rfl)
  obtain ⟨k, l, hkl, h6⟩ := ho (a 6) (Or.inr rfl)
  have rev {u v : V} (h : M.Adj u v) : M.Adj v u := M.symm.symm u v h
  have edge (m : Fin 5) : M.Adj (a (onCycle m)) (a (onCycle (m + 1))) := by
    rcases cover_cycle_facts.1 m with rfl | rfl | rfl | rfl | rfl
    · exact ha.1
    · exact ha.2.1
    · exact ha.2.2.1
    · exact ha.2.2.2.1
    · exact ha.2.2.2.2
  have stepEdge {m n : Fin 5} (h : CoverStep m n) :
      M.Adj (a (onCycle m)) (a (onCycle n)) := by
    rcases h with h | h
    · rw [h]
      exact edge m
    · rw [h]
      exact rev (edge n)
  have notStep (u : V) {m n : Fin 5}
      (hm : M.Adj u (a (onCycle m))) (hn : M.Adj u (a (onCycle n))) :
      ¬ CoverStep m n := by
    intro h
    exact ht u (a (onCycle m)) (a (onCycle n)) hm (stepEdge h) (rev hn)
  have n5 : ¬ CoverStep i j :=
    notStep (a 5) ((h5 i).2 (Or.inl rfl)) ((h5 j).2 (Or.inr rfl))
  have n6 : ¬ CoverStep k l :=
    notStep (a 6) ((h6 k).2 (Or.inl rfl)) ((h6 l).2 (Or.inr rfl))
  obtain ⟨r, b, t, hcert⟩ := cover_pattern_certificate i j k l hij hkl n5 n6
  let P := coverPattern i j k l
  have base (p : V × V) (h : p ∈ cycleEdges) : p ∈ P :=
    List.mem_append.mpr (Or.inl h)
  have leg (p : V × V)
      (h : p ∈ ([(5, onCycle i), (5, onCycle j),
                   (6, onCycle k), (6, onCycle l)] : List (V × V))) : p ∈ P :=
    List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl h)))
  have cross (h : M.Adj (a 5) (a 6)) : ((5, 6) : V × V) ∈ P := by
    have noCommon (m : Fin 5) (hm : m = i ∨ m = j) (hn : m = k ∨ m = l) : False :=
      ht (a 5) (a 6) (a (onCycle m)) h ((h6 m).2 hn) (rev ((h5 m).2 hm))
    have hd : CoverDisjoint i j k l :=
      ⟨fun e => noCommon i (Or.inl rfl) (Or.inl e),
       fun e => noCommon i (Or.inl rfl) (Or.inr e),
       fun e => noCommon j (Or.inr rfl) (Or.inl e),
       fun e => noCommon j (Or.inr rfl) (Or.inr e)⟩
    change ((5, 6) : V × V) ∈ coverPattern i j k l
    unfold coverPattern
    rw [if_pos hd]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr (by simp))))
  have attach5 (m : Fin 5) (h : M.Adj (a 5) (a (onCycle m))) : (5, onCycle m) ∈ P := by
    apply leg
    rcases (h5 m).1 h with rfl | rfl <;> simp
  have attach6 (m : Fin 5) (h : M.Adj (a 6) (a (onCycle m))) : (6, onCycle m) ∈ P := by
    apply leg
    rcases (h6 m).1 h with rfl | rfl <;> simp
  have cycleSupport (m n : Fin 5) (h : M.Adj (a (onCycle m)) (a (onCycle n))) :
      (onCycle m, onCycle n) ∈ P ∨ (onCycle n, onCycle m) ∈ P := by
    by_cases hs' : CoverStep m n
    · rcases hs' with hmn | hnm
      · exact Or.inl (base _ (hmn.symm ▸ cover_cycle_facts.2.1 m))
      · exact Or.inr (base _ (hnm.symm ▸ cover_cycle_facts.2.1 n))
    · have hne : m ≠ n := by
        intro he
        subst n
        exact M.loopless.irrefl _ h
      obtain ⟨z, hmz, hnz⟩ := cover_cycle_facts.2.2 m n hne hs'
      exact False.elim (ht _ _ _ h (stepEdge hnz) (rev (stepEdge hmz)))
  have classify (p : V) : (∃ m : Fin 5, p = onCycle m) ∨ p = 5 ∨ p = 6 := by
    by_cases hp : p.val < 5
    · exact Or.inl ⟨⟨p.val, hp⟩, Fin.ext rfl⟩
    · have hv : p.val = 5 ∨ p.val = 6 := by
        have hb := p.isLt
        omega
      exact Or.inr (hv.elim (fun h => Or.inl (Fin.ext h)) (fun h => Or.inr (Fin.ext h)))
  have support (p q : V) (h : M.Adj (a p) (a q)) : (p, q) ∈ P ∨ (q, p) ∈ P := by
    rcases classify p with ⟨m, rfl⟩ | rfl | rfl <;>
      rcases classify q with ⟨n, rfl⟩ | rfl | rfl
    · exact cycleSupport m n h
    · exact Or.inr (attach5 m (rev h))
    · exact Or.inr (attach6 m (rev h))
    · exact Or.inl (attach5 n h)
    · exact False.elim (M.loopless.irrefl _ h)
    · exact Or.inl (cross h)
    · exact Or.inl (attach6 n h)
    · exact Or.inr (cross (rev h))
    · exact False.elim (M.loopless.irrefl _ h)
  have covered (p q : V) (h : (p, q) ∈ P) :
      TemplateAdj t (coverRelabel r b p) (coverRelabel r b q) := by
    exact of_decide_eq_true (List.all_eq_true.mp hcert (p, q) h)
  let p : Equiv.Perm V :=
    { toFun := coverRelabel r b
      invFun := coverRelabel (coverInverse r b) b
      left_inv := cover_relabel_inverse.1 r b
      right_inv := cover_relabel_inverse.2 r b }
  refine ⟨t, a.symm.trans p, ?_⟩
  intro x y hxy
  have h' : M.Adj (a (a.symm x)) (a (a.symm y)) := by
    simpa only [Equiv.apply_symm_apply] using hxy
  change TemplateAdj t (coverRelabel r b (a.symm x)) (coverRelabel r b (a.symm y))
  rcases support (a.symm x) (a.symm y) h' with h | h
  · exact covered _ _ h
  · exact (covered _ _ h).elim Or.inr Or.inl

private def vertexAssignments : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
    let ds := vertexAssignments n
    ds.map (fun d => false :: d) ++ ds.map (fun d => true :: d)

private abbrev ColoredEdge := (V × V) × Bool

private def edgeAssignments : List (V × V) → List (List ColoredEdge)
  | [] => [[]]
  | e :: es =>
    let cs := edgeAssignments es
    cs.map (fun c => (e, false) :: c) ++ cs.map (fun c => (e, true) :: c)

private lemma edgeAssignments_mem (es : List (V × V)) (c : V → V → Bool) :
    es.map (fun e => (e, c e.1 e.2)) ∈ edgeAssignments es := by
  induction es with
  | nil => simp [edgeAssignments]
  | cons e es ih =>
    change (e, c e.1 e.2) :: es.map (fun p => (p, c p.1 p.2)) ∈
      (edgeAssignments es).map (fun cs => (e, false) :: cs) ++
      (edgeAssignments es).map (fun cs => (e, true) :: cs)
    rw [List.mem_append]
    cases c e.1 e.2 with
    | false =>
      exact Or.inl (List.mem_map.mpr ⟨_, ih, rfl⟩)
    | true =>
      exact Or.inr (List.mem_map.mpr ⟨_, ih, rfl⟩)

private def vertexBit (ds : List Bool) (x : V) : Bool :=
  (ds[x.val]?).getD false

private def edgeOK (ds : List Bool) (p : ColoredEdge) : Bool :=
  !((vertexBit ds p.1.1 == p.2) && (vertexBit ds p.1.2 == p.2))

private def templateCheck (t : Fin 3) : Bool :=
  (edgeAssignments (templateEdges t)).all fun cs =>
    (vertexAssignments 7).any fun ds => cs.all (edgeOK ds)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private lemma template_certificate (t : Fin 3) : templateCheck t = true := by
  fin_cases t <;> rfl

private lemma templates_colorable (t : Fin 3) (c : V → V → Bool)
    (hc : ∀ x y, c x y = c y x) :
    ∃ d : V → Bool, ∀ x y, TemplateAdj t x y →
      ¬ (d x = c x y ∧ d y = c x y) := by
  let cs := (templateEdges t).map (fun e => (e, c e.1 e.2))
  have hm : cs ∈ edgeAssignments (templateEdges t) :=
    edgeAssignments_mem (templateEdges t) c
  have hall : (edgeAssignments (templateEdges t)).all
      (fun bs => (vertexAssignments 7).any (fun ds => bs.all (edgeOK ds))) = true :=
    template_certificate t
  have hany : (vertexAssignments 7).any (fun ds => cs.all (edgeOK ds)) = true :=
    List.all_eq_true.mp hall cs hm
  obtain ⟨ds, _, hd⟩ := List.any_eq_true.mp hany
  have oriented (x y : V) (hxy : (x, y) ∈ templateEdges t) :
      ¬ (vertexBit ds x = c x y ∧ vertexBit ds y = c x y) := by
    have hp : ((x, y), c x y) ∈ cs := List.mem_map.mpr ⟨(x, y), hxy, rfl⟩
    have hok : edgeOK ds ((x, y), c x y) = true :=
      List.all_eq_true.mp hd _ hp
    intro hbad
    simp [edgeOK, hbad.1, hbad.2] at hok
  refine ⟨vertexBit ds, ?_⟩
  intro x y hxy
  rcases hxy with hxy | hyx
  · exact oriented x y hxy
  · intro hbad
    exact oriented y x hyx ⟨hbad.2.trans (hc x y), hbad.1.trans (hc x y)⟩

private theorem link_extension : OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1_H1_R1.H4 := by
  classical
  intro k L hk ht c hc
  obtain ⟨f, M, htM, hsM, hmap⟩ := exists_maximal_tf k L hk ht
  by_cases hb : Bip M
  · obtain ⟨d, hd⟩ := hb
    refine ⟨fun i => d (f i), ?_⟩
    intro i j hij hbad
    exact hd (f i) (f j) (hmap i j hij) (hbad.1.trans hbad.2.symm)
  · obtain ⟨a, ha⟩ := exists_c5_of_not_bipartite M htM hsM hb
    have ho := outside_deg_two_in_c5 M htM hsM a ha
    obtain ⟨t, e, he⟩ := three_templates_cover M htM hsM a ha ho
    let g : Fin k → V := fun i => e (f i)
    have hg : Function.Injective g := fun _ _ h => f.injective (e.injective h)
    let C (x y : V) : Bool :=
      if h : ∃ i j : Fin k, g i = x ∧ g j = y then
        c (Classical.choose h) (Classical.choose (Classical.choose_spec h))
      else false
    have C_eq (i j : Fin k) : C (g i) (g j) = c i j := by
      have h : ∃ u v : Fin k, g u = g i ∧ g v = g j := ⟨i, j, rfl, rfl⟩
      have hs := Classical.choose_spec (Classical.choose_spec h)
      have hi : Classical.choose h = i := hg hs.1
      have hj : Classical.choose (Classical.choose_spec h) = j := hg hs.2
      simp only [C, dif_pos h]
      exact (congrArg (fun u => c u (Classical.choose (Classical.choose_spec h))) hi).trans
        (congrArg (c i) hj)
    have C_sym (x y : V) : C x y = C y x := by
      by_cases h : ∃ i j : Fin k, g i = x ∧ g j = y
      · obtain ⟨i, j, rfl, rfl⟩ := h
        simpa only [C_eq] using hc i j
      · have h' : ¬ ∃ i j : Fin k, g i = y ∧ g j = x := by
          rintro ⟨j, i, hj, hi⟩
          exact h ⟨i, j, hi, hj⟩
        simp only [C, dif_neg h, dif_neg h']
    obtain ⟨d, hd⟩ := templates_colorable t C C_sym
    refine ⟨fun i => d (g i), ?_⟩
    intro i j hij
    have hEdge : TemplateAdj t (g i) (g j) := he (f i) (f j) (hmap i j hij)
    simpa only [C_eq] using hd (g i) (g j) hEdge

end Erdos151Seven

namespace Erdos151Research.CoreDensity

open Finset
open scoped BigOperators

def Bichromatic {E : Type*} (c : E → Bool) (s : Finset E) : Prop :=
  (∃ i ∈ s, c i = true) ∧ ∃ j ∈ s, c j = false

private theorem has_both_signs {E : Type*} (s : Finset E) (z : E → ℚ)
    (total : ∑ i ∈ s, z i = 0) (nonzero : ∃ i ∈ s, z i ≠ 0) :
    (∃ i ∈ s, 0 < z i) ∧ ∃ j ∈ s, z j < 0 := by
  obtain ⟨i, hi, hne⟩ := nonzero
  constructor
  · by_contra! neg
    have sum_neg : ∑ j ∈ s, -z j = 0 := by simp [total]
    have zero := (sum_eq_zero_iff_of_nonneg (fun j hj => neg_nonneg.mpr (neg j hj))).mp sum_neg i hi
    exact hne (neg_eq_zero.mp zero)
  · by_contra! pos
    exact hne ((sum_eq_zero_iff_of_nonneg pos).mp total i hi)

theorem density {E T : Type*} [Fintype E] [Fintype T] (row : T → Finset E)
    (ramsey : ¬ ∃ c : E → Bool, ∀ t, Bichromatic c (row t))
    (minimal : ∀ e : E, ∃ c : E → Bool, ∀ t, e ∉ row t → Bichromatic c (row t)) :
    Fintype.card E ≤ Fintype.card T := by
  classical
  let A : (E → ℚ) →ₗ[ℚ] (T → ℚ) :=
    { toFun := fun f t => ∑ i ∈ row t, f i
      map_add' := by intros; ext; simp [Finset.sum_add_distrib]
      map_smul' := by intros; ext; simp [Finset.mul_sum] }
  have trivial : ∀ z, A z = 0 → z = 0 := by
    intro z hz
    by_contra hne
    obtain ⟨e, he⟩ : ∃ e, z e ≠ 0 := by
      by_contra! all
      exact hne (funext all)
    obtain ⟨c, hc⟩ := minimal e
    let newColor (i : E) : Bool := if z i = 0 then c i else decide (0 < z i)
    apply ramsey
    refine ⟨newColor, fun t => ?_⟩
    by_cases zero : ∀ i ∈ row t, z i = 0
    · obtain ⟨⟨i, hi, hci⟩, j, hj, hcj⟩ := hc t (fun h => he (zero e h))
      exact ⟨⟨i, hi, by simp [newColor, zero i hi, hci]⟩,
             ⟨j, hj, by simp [newColor, zero j hj, hcj]⟩⟩
    · push Not at zero
      have total : ∑ i ∈ row t, z i = 0 := congrFun hz t
      obtain ⟨⟨i, hi, hpos⟩, j, hj, hneg⟩ := has_both_signs (row t) z total zero
      exact ⟨⟨i, hi, by simp [newColor, hpos.ne', hpos]⟩,
             ⟨j, hj, by simp [newColor, hneg.ne, hneg.not_gt]⟩⟩
  have inj : Function.Injective A := by
    intro x y hxy
    exact sub_eq_zero.mp (trivial (x-y) (by simp [map_sub, hxy]))
  simpa only [Module.finrank_pi] using LinearMap.finrank_le_finrank_of_injective inj

open SimpleGraph

variable {V : Type*} [DecidableEq V]

def pairs (s : Finset V) : Finset (Sym2 V) := s.sym2.filter (fun e => ¬e.IsDiag)

theorem mk_mem_pairs {a b : V} {s : Finset V} :
    s(a,b) ∈ pairs s ↔ a ∈ s ∧ b ∈ s ∧ a ≠ b := by
  simp [pairs, and_assoc]

theorem pairs_are_edges (C : SimpleGraph V) {s : Finset V} (hs : C.IsClique s)
    {e : Sym2 V} (he : e ∈ pairs s) : e ∈ C.edgeSet := by
  induction e using Sym2.inductionOn with
  | _ a b =>
    obtain ⟨ha, hb, hab⟩ := mk_mem_pairs.mp he
    exact hs ha hb hab

def GoodColoring (C : SimpleGraph V) (c : Sym2 V → Bool) : Prop :=
  ∀ t : Finset V, C.IsNClique 3 t → Bichromatic c (pairs t)

def Arrow (C : SimpleGraph V) : Prop := ¬ ∃ c, GoodColoring C c

theorem colorable_below {C D : SimpleGraph V} (hmin : Minimal Arrow C) (hlt : D < C) :
    ∃ c, GoodColoring D c := by
  by_contra notColorable
  exact hlt.not_ge (hmin.2 (show Arrow D from notColorable) hlt.le)

theorem colorable_delete {C : SimpleGraph V} (hmin : Minimal Arrow C)
    {e : Sym2 V} (he : e ∈ C.edgeSet) : ∃ c, GoodColoring (C.deleteEdges {e}) c := by
  apply colorable_below hmin
  refine lt_of_le_of_ne (C.deleteEdges_le _) ?_
  intro eqn
  have absent : e ∉ (C.deleteEdges {e}).edgeSet := by simp [SimpleGraph.edgeSet_deleteEdges]
  rw [eqn] at absent
  exact absent he

theorem triangle_survives_delete {C : SimpleGraph V} {t : Finset V} (htri : C.IsNClique 3 t)
    {e : Sym2 V} (missing : e ∉ pairs t) : (C.deleteEdges {e}).IsNClique 3 t := by
  refine ⟨?_, htri.card_eq⟩
  intro a ha b hb hab
  apply SimpleGraph.deleteEdges_adj.mpr
  refine ⟨htri.isClique ha hb hab, ?_⟩
  intro eqn
  change s(a,b) = e at eqn
  exact missing (eqn ▸ mk_mem_pairs.mpr ⟨ha,hb,hab⟩)

theorem minimal_core_density [Fintype V] (C : SimpleGraph V) (hmin : Minimal Arrow C) :
    Nat.card C.edgeSet ≤ Nat.card (C.cliqueSet 3) := by
  classical
  let E := C.edgeSet
  let T := C.cliqueSet 3
  let : Fintype E := Fintype.ofFinite E
  let : Fintype T := Fintype.ofFinite T
  let row (t : T) : Finset E := (pairs t.val).subtype (· ∈ C.edgeSet)
  have hArrow : ¬ ∃ c : E → Bool, ∀ t, Bichromatic c (row t) := by
    rintro ⟨c, hc⟩
    apply hmin.1
    refine ⟨fun e => if h : e ∈ C.edgeSet then c ⟨e,h⟩ else false, ?_⟩
    intro t ht
    obtain ⟨⟨e, he, ce⟩, f, hf, cf⟩ := hc ⟨t,ht⟩
    exact ⟨⟨e.val, Finset.mem_subtype.mp he, by simpa [e.property] using ce⟩,
           ⟨f.val, Finset.mem_subtype.mp hf, by simpa [f.property] using cf⟩⟩
  have minimal (e : E) : ∃ c : E → Bool, ∀ t, e ∉ row t → Bichromatic c (row t) := by
    obtain ⟨c, hc⟩ := colorable_delete hmin e.property
    refine ⟨fun x => c x.val, ?_⟩
    intro t missing
    have htri : C.IsNClique 3 t.val := t.property
    have survives := triangle_survives_delete htri (fun h => missing (Finset.mem_subtype.mpr h))
    obtain ⟨⟨a, ha, ca⟩, b, hb, cb⟩ := hc t.val survives
    exact ⟨⟨⟨a,pairs_are_edges C htri.isClique ha⟩, Finset.mem_subtype.mpr ha, ca⟩,
           ⟨⟨b,pairs_are_edges C htri.isClique hb⟩, Finset.mem_subtype.mpr hb, cb⟩⟩
  have result := density row hArrow minimal
  simpa only [Nat.card_eq_fintype_card] using result

end Erdos151Research.CoreDensity

namespace Erdos151.DenseLink

open SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- Common neighbors of an edge biject with triangles containing that edge. -/
theorem common_neighbors_count {v u : V} (hvu : G.Adj v u) :
    ((G.neighborFinset v).filter (G.Adj u)).card =
      ((G.cliqueFinset 3).filter fun t => v ∈ t ∧ u ∈ t).card := by
  classical
  refine Finset.card_bij (fun x _ => {v, u, x}) ?_ ?_ ?_
  · intro x hx
    obtain ⟨hx₁, hx₂⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_filter.mpr ⟨mem_cliqueFinset_iff.mpr ?_, by simp⟩
    exact is3Clique_triple_iff.mpr ⟨hvu, (G.mem_neighborFinset v x).mp hx₁, hx₂⟩
  · intro a ha b _ heq
    obtain ⟨hva, hua⟩ := Finset.mem_filter.mp ha
    have h₁ := ((G.mem_neighborFinset v a).mp hva).ne.symm
    have h₂ := hua.ne.symm
    have hab : a ∈ ({v, u, b} : Finset V) := heq ▸ (by simp)
    simpa [h₁, h₂] using hab
  · intro t ht
    obtain ⟨ht, hvt, hut⟩ := Finset.mem_filter.mp ht
    have htc := mem_cliqueFinset_iff.mp ht
    have hsub : ({v,u} : Finset V) ⊆ t :=
      Finset.insert_subset_iff.mpr ⟨hvt, Finset.singleton_subset_iff.mpr hut⟩
    have hsize : (t \ {v,u}).card = 1 := by
      rw [Finset.card_sdiff_of_subset hsub, htc.2]
      simp [hvu.ne]
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hsize
    have hxt : x ∈ t \ {v,u} := by rw [hx]; simp
    obtain ⟨hxt, hxn⟩ := Finset.mem_sdiff.mp hxt
    have hxv : v ≠ x := by rintro rfl; exact hxn (by simp)
    have hxu : u ≠ x := by rintro rfl; exact hxn (by simp)
    refine ⟨x, Finset.mem_filter.mpr ⟨(G.mem_neighborFinset v x).mpr
      (htc.1 hvt hxt hxv), htc.1 hut hxt hxu⟩, ?_⟩
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.insert_subset_iff.mpr
        ⟨hvt, Finset.insert_subset_iff.mpr ⟨hut, Finset.singleton_subset_iff.mpr hxt⟩⟩
    · rw [htc.2]
      simp [hvu.ne, hxv, hxu]

/-- For fixed center `v`, each triangle through the center has two other corners. -/
theorem link_count (v : V) :
    (∑ u ∈ G.neighborFinset v, ((G.neighborFinset v).filter (G.Adj u)).card) =
      2 * ((G.cliqueFinset 3).filter fun t => v ∈ t).card := by
  classical
  let Ts := (G.cliqueFinset 3).filter fun t => v ∈ t
  calc
    _ = ∑ u ∈ G.neighborFinset v, (Ts.filter fun t => u ∈ t).card := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [common_neighbors_count G ((G.mem_neighborFinset v u).mp hu)]
      simp [Ts, Finset.filter_filter]
    _ = ∑ t ∈ Ts, ((G.neighborFinset v).filter fun u => u ∈ t).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    _ = ∑ _t ∈ Ts, 2 := by
      apply Finset.sum_congr rfl
      intro t ht
      obtain ⟨ht, hvt⟩ := Finset.mem_filter.mp ht
      have htc := mem_cliqueFinset_iff.mp ht
      have eqf : (G.neighborFinset v).filter (fun u => u ∈ t) = t.erase v := by
        ext x
        simp only [Finset.mem_filter, mem_neighborFinset, Finset.mem_erase]
        exact ⟨fun h => ⟨h.1.ne.symm, h.2⟩, fun h => ⟨htc.1 hvt h.2 h.1.symm, h.2⟩⟩
      rw [eqf, Finset.card_erase_of_mem hvt, htc.2]
    _ = _ := by simp [Ts, Nat.mul_comm]


/-- Across all centers, the two orientations of every triangle are counted at each of
its three vertices. -/
theorem sum_link_count :
    (∑ v, ∑ u ∈ G.neighborFinset v, ((G.neighborFinset v).filter (G.Adj u)).card) =
      6 * (G.cliqueFinset 3).card := by
  classical
  simp_rw [link_count]
  have htranspose : (∑ v : V, ((G.cliqueFinset 3).filter fun t => v ∈ t).card) =
      ∑ t ∈ G.cliqueFinset 3, (Finset.univ.filter fun v => v ∈ t).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [← Finset.mul_sum, htranspose]
  have hc : (∑ t ∈ G.cliqueFinset 3, (Finset.univ.filter fun v => v ∈ t).card)
      = ∑ _t ∈ G.cliqueFinset 3, 3 := by
    apply Finset.sum_congr rfl
    intro t ht
    have eqf : Finset.univ.filter (fun v => v ∈ t) = t := by ext; simp
    rw [eqf, (mem_cliqueFinset_iff.mp ht).2]
  rw [hc]
  simp [Nat.mul_comm]
  omega

end Erdos151.DenseLink

namespace Erdos151PairColoring

open Finset SimpleGraph Erdos151Research.CoreDensity

section

variable {V : Type*} [DecidableEq V]

private def PairColorable (F : SimpleGraph V) : Prop :=
  ∃ c : V → V → Bool, (∀ x y, c x y = c y x) ∧
    ∀ x y z, F.Adj x y → F.Adj x z → F.Adj y z → ¬ (c x y = c x z ∧ c x y = c y z)

private lemma triangle_pairs (x y z : V) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    pairs {x, y, z} = {s(x,y), s(x,z), s(y,z)} := by
  ext e
  induction e using Sym2.inductionOn with
  | _ a b =>
    simp only [mk_mem_pairs, mem_insert, mem_singleton, Sym2.eq_iff]
    grind

private lemma bichromatic_three {E : Type*} [DecidableEq E] (c : E → Bool) (a b d : E) :
    Bichromatic c {a, b, d} ↔ ¬ (c a = c b ∧ c a = c d) := by
  cases ha : c a <;> cases hb : c b <;> cases hd : c d <;> simp [Bichromatic, ha, hb, hd]

private lemma colorable_iff (F : SimpleGraph V) :
    PairColorable F ↔ ∃ c, GoodColoring F c := by
  constructor
  · rintro ⟨c, hs, h⟩
    let f := Sym2.lift ⟨c, hs⟩
    refine ⟨f, fun t ht => ?_⟩
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := is3Clique_iff.mp ht
    rw [triangle_pairs x y z hxy.ne hxz.ne hyz.ne, bichromatic_three]
    exact h x y z hxy hxz hyz
  · rintro ⟨c, h⟩
    refine ⟨fun x y => c s(x,y), fun x y => congrArg c Sym2.eq_swap, ?_⟩
    intro x y z hxy hxz hyz
    have hh := h _ (is3Clique_triple_iff.mpr ⟨hxy, hxz, hyz⟩)
    rwa [triangle_pairs x y z hxy.ne hxz.ne hyz.ne, bichromatic_three] at hh

private lemma density_from_pair_coloring [Fintype V] (F : SimpleGraph V)
    (hbad : ¬ PairColorable F) (hproper : ∀ F' < F, PairColorable F') :
    Nat.card F.edgeSet ≤ Nat.card (F.cliqueSet 3) := by
  apply minimal_core_density
  refine ⟨fun h => hbad ((colorable_iff F).mpr h), ?_⟩
  intro F' hF' hle
  by_contra h
  exact hF' ((colorable_iff F').mp (hproper F' (lt_of_le_not_ge hle h)))

end

open scoped Classical in
private lemma ordered_density {V : Type*} [Fintype V] (F : SimpleGraph V)
    (h : Nat.card F.edgeSet ≤ Nat.card (F.cliqueSet 3)) :
    3 * (∑ v, (univ.filter (F.Adj v)).card) ≤
      ∑ v, ∑ u ∈ univ.filter (F.Adj v), (univ.filter fun z => F.Adj v z ∧ F.Adj u z).card := by
  rw [← F.coe_edgeFinset, ← F.coe_cliqueFinset 3] at h
  simp only [Nat.card_coe_set_eq, Set.ncard_coe_finset] at h
  calc
    _ = 3 * (2 * F.edgeFinset.card) := by
      congr 1
      simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
        using F.sum_degrees_eq_twice_card_edges
    _ = 6 * F.edgeFinset.card := by omega
    _ ≤ 6 * (F.cliqueFinset 3).card := Nat.mul_le_mul_left 6 h
    _ = ∑ v, ∑ u ∈ F.neighborFinset v, ((F.neighborFinset v).filter (F.Adj u)).card :=
      (Erdos151.DenseLink.sum_link_count F).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr (by ext u; simp)
      intro u _
      apply congrArg Finset.card
      ext z
      simp

end Erdos151PairColoring

theorem OMA.solution : OMA.R_Erdos151_erdos_151_variants_cliqueFree_four_R1_H1_R1_H1_R1_H1_R1_H1_R1.H4 := by
  refine ⟨Erdos151Seven.link_extension, ?_⟩
  intro n F hbad hproper
  exact Erdos151PairColoring.ordered_density F
    (Erdos151PairColoring.density_from_pair_coloring F hbad hproper)

import OMAStatements.S_mo_233932

/-!
Retains @connoranderson’s proof from #31937 and its earlier companion linked in #22563.
Uses standard finite-set counting APIs; pending @artnoage #36700 was also inspected.

The radius-r ball volume is the sum of the numbers of ways to choose the
moved positions and derange them. A cover requires enough total ball volume.
Choosing a representative for every ordered prefix gives an explicit cover.
For a second bound, count center tuples failing to cover a fixed permutation,
then sum the counts over all permutations.
-/

namespace OMA.S_mo_233932
open Finset Equiv

private abbrev P (n : ℕ) := Perm (Fin n)
private abbrev distP {n : ℕ} (x y : P n) := hammingDist (fun i => x i) (fun i => y i)

private lemma support_fiber {n : ℕ} (s : Finset (Fin n)) :
    (univ.filter (fun p : P n => p.support=s)).card=numDerangements s.card := by
  classical
  let E := (derangements.subtypeEquiv (fun i => i∈s)).trans <|
    Equiv.subtypeEquivRight (q := fun p : P n => p.support=s) (fun p => by
      simp only [Finset.ext_iff,Equiv.Perm.mem_support,Function.mem_fixedPoints_iff]
      constructor
      · intro h i
        exact not_iff_comm.mp (h i)
      · intro h i
        exact (not_iff_comm.mpr (h i)))
  rw [← Fintype.card_subtype, ← Fintype.card_congr E,
    card_derangements_eq_numDerangements, Fintype.card_coe]


private lemma shell_card (n j : ℕ) :
    (univ.filter (fun p : P n => p.support.card=j)).card=n.choose j*numDerangements j := by
  classical
  let t := univ.filter (fun p : P n => p.support.card=j)
  let S := (univ : Finset (Fin n)).powersetCard j
  have ht : (t : Set (P n)).MapsTo Equiv.Perm.support S := by
    intro p hp
    exact mem_powersetCard.mpr ⟨subset_univ _,(mem_filter.mp hp).2⟩
  change t.card=_
  rw [card_eq_sum_card_fiberwise ht]
  calc
    _ = ∑ _s ∈ S, numDerangements j := by
      apply sum_congr rfl
      intro s hs
      have hsj := (mem_powersetCard.mp hs).2
      have hb : t.filter (fun p => p.support=s)=univ.filter (fun p => p.support=s) := by
        ext p
        simp [t]
        grind
      rw [hb,support_fiber,hsj]
    _ = _ := by simp [S]

private lemma radius_card (n r : ℕ) :
    (univ.filter (fun p : P n => p.support.card≤r)).card=volume n r := by
  classical
  let t := univ.filter (fun p : P n => p.support.card≤r)
  have ht : (t : Set (P n)).MapsTo (fun p => p.support.card) (range (r+1)) :=
    fun p hp => mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hp).2)
  change t.card=_
  rw [card_eq_sum_card_fiberwise ht]
  apply sum_congr rfl
  intro j hj
  have hjr := Nat.le_of_lt_succ (mem_range.mp hj)
  have he : t.filter (fun p => p.support.card=j)=univ.filter (fun p => p.support.card=j) := by
    ext p
    simp [t]
    omega
  rw [he,shell_card]

private lemma dist_left {n : ℕ} (x u : P n) : distP x (x*u)=u.support.card := by
  apply congrArg Finset.card
  ext i
  simp [Equiv.Perm.mul_apply,ne_comm]

private lemma ball_card {n : ℕ} (x : P n) (r : ℕ) :
    (univ.filter (fun y => distP x y ≤ r)).card = volume n r := by
  classical
  let e : P n ≃ P n := Equiv.mulLeft x
  have he (u : P n) : u.support.card≤r ↔ distP x (e u)≤r := by rw [show e u=x*u from rfl,dist_left]
  let E := e.subtypeEquiv (p:=fun u => u.support.card≤r) (q:=fun y => distP x y≤r) he
  simpa only [Fintype.card_subtype, radius_card] using Fintype.card_congr E.symm


private lemma prefix_cover (n r : ℕ) (hr : r≤n) :
    ∃ C : Finset (P n), C.card ≤ n.factorial/r.factorial ∧ covers C r := by
  classical
  let t := n-r
  have ht : t≤n := Nat.sub_le .. 
  let firstEntries (p : P n) : Fin t ↪ Fin n := ⟨fun i => p (Fin.castLE ht i),
    fun i j h => Fin.ext (congrArg (fun z : Fin n => z.val) (p.injective h))⟩
  let rep := Function.invFun firstEntries
  let C := (univ : Finset (Fin t ↪ Fin n)).image rep
  refine ⟨C,?_,?_⟩
  · calc
      _ ≤ Fintype.card (Fin t ↪ Fin n) := card_image_le.trans_eq card_univ
      _ = n.factorial/r.factorial := by
        simp [Nat.descFactorial_eq_div ht,show n-t=r by dsimp [t]; omega]
  · intro p
    let c := rep (firstEntries p)
    refine ⟨c,mem_image_of_mem _ (mem_univ _),?_⟩
    have he : firstEntries c=firstEntries p := Function.apply_invFun_apply
    let D := univ.filter (fun i : Fin n => p i≠c i)
    have hsub : D ⊆ (univ.filter (fun i : Fin n => i.val < t))ᶜ := by
      intro i hi
      simp only [mem_compl, mem_filter, mem_univ, true_and, not_lt]
      by_contra! h
      have hh := congrArg (fun f : Fin t ↪ Fin n => f ⟨i,h⟩) he
      exact (mem_filter.mp hi).2 hh.symm
    change D.card ≤ r
    have hc := card_le_card hsub
    rw [card_compl, Fintype.card_fin, Fin.card_filter_val_lt, Nat.min_eq_right ht] at hc
    simpa only [t, Nat.sub_sub_self hr] using hc


private lemma ball_lower {n r : ℕ} (C : Finset (P n)) (h : covers C r) :
    n.factorial≤C.card*volume n r := by
  classical
  let B (c : P n) := univ.filter (fun p : P n => distP c p≤r)
  have hs : univ ⊆ C.biUnion B := by
    intro p _
    obtain ⟨c,hc,hp⟩ := h p
    exact mem_biUnion.mpr ⟨c,hc,mem_filter.mpr ⟨mem_univ _,by
      simpa only [distP,hammingDist_comm] using hp⟩⟩
  calc
    _ = (univ : Finset (P n)).card := by simp [Fintype.card_perm]
    _ ≤ (C.biUnion B).card := card_le_card hs
    _ ≤ ∑ c ∈ C, (B c).card := card_biUnion_le
    _ = _ := by simp [B,ball_card]

private lemma random_cover {n r K : ℕ}
    (h : n.factorial*(n.factorial-volume n r)^K < n.factorial^K) :
    ∃ C : Finset (P n), C.card≤K ∧ covers C r := by
  classical
  let outside (x : P n) := univ.filter (fun c => ¬distP x c≤r)
  have hn : Fintype.card (P n)=n.factorial := by simp [Fintype.card_perm]
  have ho (x : P n) : (outside x).card=n.factorial-volume n r := by
    have ht := card_filter_add_card_filter_not (s:=univ) (fun c => distP x c≤r)
    rw [ball_card,card_univ,hn] at ht
    change (univ.filter (fun c => ¬distP x c≤r)).card=_
    omega
  let bad (x : P n) := Fintype.piFinset (fun _ : Fin K => outside x)
  have hs : (univ.biUnion bad).card < (univ : Finset (Fin K → P n)).card := calc
    _ ≤ ∑ x : P n, (bad x).card := card_biUnion_le
    _ = n.factorial*(n.factorial-volume n r)^K := by simp [bad,Fintype.card_piFinset,ho,hn]
    _ < _ := by simpa [hn] using h
  obtain ⟨v,_,hv⟩ := Finset.exists_mem_notMem_of_card_lt_card hs
  refine ⟨univ.image v,card_image_le.trans (by simp),?_⟩
  intro x
  by_contra! hx
  apply hv
  apply mem_biUnion.mpr
  refine ⟨x,mem_univ _,Fintype.mem_piFinset.mpr ?_⟩
  intro i
  exact mem_filter.mpr ⟨mem_univ _,not_le.mpr (hx (v i) (mem_image_of_mem _ (mem_univ i)))⟩

end OMA.S_mo_233932

open OMA.S_mo_233932 Finset in
theorem OMA.solution : type_of% @OMA.S_mo_233932.main := by
  intro n r hr
  classical
  refine ⟨fun C hC => ball_lower C hC,?_⟩
  intro K hK hk
  have he : ∃ D : Finset (P n), D.card≤K ∧ covers D r := by
    rcases hk with hp|hp
    · obtain ⟨D,hD,hd⟩ := prefix_cover n r hr
      exact ⟨D,hD.trans hp,hd⟩
    · exact random_cover hp
  obtain ⟨D,hD,hd⟩ := he
  obtain ⟨C,hDC,_,hcard⟩ := exists_subsuperset_card_eq (subset_univ D) hD (by
    simpa [Fintype.card_perm] using hK)
  exact ⟨C,hcard,fun p => by obtain ⟨c,hc,hx⟩ := hd p; exact ⟨c,hDC hc,hx⟩⟩

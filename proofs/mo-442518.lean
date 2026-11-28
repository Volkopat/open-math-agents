import OMAStatements.S_mo_442518

/-!
A small version of Teo Miklethun's counterexample in MathOverflow answer 486337.
The endpoints are 0 and 1. Each of the two branch vertices has its own pair
of mutually adjacent vertices. The reverse arcs from 1 into each pair and
from each pair to 0 preserve strong connectivity after a deletion.
-/
namespace DirectedPathCounterexample
open OMA.S_mo_442518

private def arcs (a b : Fin 8) : Bool :=
  if a = b then false
  else if a = 0 then b = 1 || b = 2 || b = 3
  else if a = 1 then true
  else if a = 2 then b = 0 || b = 1 || b = 4 || b = 5
  else if a = 3 then b = 0 || b = 1 || b = 6 || b = 7
  else if a ≤ 5 then b = 0 || b = 2 || b = 4 || b = 5
  else b = 0 || b = 3 || b = 6 || b = 7

private def G : Digraph (Fin 8) := ⟨fun a b => arcs a b = true⟩

private instance instAdj : DecidableRel G.Adj := fun a b =>
  inferInstanceAs (Decidable (arcs a b = true))

private theorem no_loop : ∀ v, ¬ G.Adj v v := by decide +kernel

private theorem degree : ∀ v, 3 ≤ outdegree G v ∧ 3 ≤ indegree G v := by
  decide +kernel

private def restricted (S : Finset (Fin 8)) (a b : Fin 8) : Prop :=
  G.Adj a b ∧ a ∉ S ∧ b ∉ S

private instance instRestricted (S : Finset (Fin 8)) : DecidableRel (restricted S) :=
  fun a b => inferInstanceAs (Decidable (G.Adj a b ∧ a ∉ S ∧ b ∉ S))

private def TwoSteps (S : Finset (Fin 8)) (a b : Fin 8) : Prop :=
  a = b ∨ restricted S a b ∨ ∃ v, restricted S a v ∧ restricted S v b

private instance (S : Finset (Fin 8)) (a b : Fin 8) : Decidable (TwoSteps S a b) := by
  unfold TwoSteps
  infer_instance

private theorem reach {S : Finset (Fin 8)} {a b : Fin 8} (h : TwoSteps S a b) :
    Relation.ReflTransGen (restricted S) a b := by
  rcases h with (rfl | h | ⟨v, ha, hb⟩)
  · exact .refl
  · exact .single h
  · exact (Relation.ReflTransGen.single ha).tail hb

private theorem emptyBoth :
    ∀ u : Fin 8, TwoSteps ∅ u 0 ∧ TwoSteps ∅ 0 u := by decide +kernel

private theorem singleBoth :
    ∀ x u : Fin 8, u ≠ x →
      TwoSteps {x} u (if x = 0 then 1 else 0) ∧
      TwoSteps {x} (if x = 0 then 1 else 0) u := by decide +kernel

private theorem strongTwo : IsKStrong G 2 := by
  refine ⟨by decide, ?_⟩
  intro S hS
  have hs : S.card ≤ 1 := by omega
  rcases S.eq_empty_or_nonempty with rfl | hne
  · intro a b _ _
    exact (reach (emptyBoth a).1).trans (reach (emptyBoth b).2)
  · have hpos := Finset.card_pos.mpr hne
    obtain ⟨v,rfl⟩ := Finset.card_eq_one.mp (show S.card = 1 by omega)
    intro a b ha hb
    have ha' : a ≠ v := by simpa using ha
    have hb' : b ≠ v := by simpa using hb
    exact (reach (singleBoth v a ha').1).trans (reach (singleBoth v b hb').2)

private def inPair (h v : Fin 8) : Prop :=
  (h = 2 ∧ (v = 4 ∨ v = 5)) ∨ (h = 3 ∧ (v = 6 ∨ v = 7))

private instance (h v : Fin 8) : Decidable (inPair h v) := by
  unfold inPair
  infer_instance

private theorem firstStep :
    ∀ h : Fin 8, G.Adj 0 h → h ≠ 1 → h = 2 ∨ h = 3 := by decide +kernel

private theorem secondStep :
    ∀ h x : Fin 8, h = 2 ∨ h = 3 → G.Adj h x → x ≠ 0 → x ≠ 1 →
      inPair h x := by decide +kernel

private theorem stayInPair :
    ∀ h x y : Fin 8, inPair h x → G.Adj x y → y ≠ 0 → y ≠ h →
      inPair h y := by decide +kernel

private theorem targetOutside : ∀ h : Fin 8, ¬ inPair h 1 := by decide +kernel

private theorem noLongPath : ¬ HasPathOfLengthAtLeast G 0 1 3 := by
  rintro ⟨l, hl, p, hinj, hs, ht, he⟩
  let h := p (⟨1, by omega⟩ : Fin (l+1))
  have avoidsSource (j : ℕ) (hj : j < l+1) (hj0 : 0 < j) : p ⟨j,hj⟩ ≠ 0 := by
    intro H
    have H' := congrArg Fin.val (hinj (H.trans hs.symm))
    simp at H'
    omega
  have avoidsTarget (j : ℕ) (hj : j < l+1) (hjl : j < l) : p ⟨j,hj⟩ ≠ 1 := by
    intro H
    have H' := congrArg Fin.val (hinj (H.trans ht.symm))
    simp at H'
    omega
  have avoidsHub (j : ℕ) (hj : j < l+1) (hj1 : 1 < j) : p ⟨j,hj⟩ ≠ h := by
    intro H
    have H' := congrArg Fin.val (hinj H)
    simp at H'
    omega
  let i0 : Fin l := ⟨0, by omega⟩
  have hi0 : i0.castSucc = (0 : Fin (l+1)) := by
    apply Fin.ext
    simp [i0]
  have hi1 : p i0.succ = h := rfl
  have hE := he i0
  rw [hi0, hs, hi1] at hE
  have hh : h = 2 ∨ h = 3 :=
    firstStep h hE (avoidsTarget 1 (by omega) (by omega))
  have trap (j : ℕ) (hj : 2 ≤ j) (hjl : j < l+1) : inPair h (p ⟨j,hjl⟩) := by
    induction j, hj using Nat.le_induction with
    | base =>
      exact secondStep h _ hh (he ⟨1,by omega⟩)
        (avoidsSource 2 _ (by omega)) (avoidsTarget 2 _ (by omega))
    | succ j hj ih =>
      exact stayInPair h _ _ (ih (by omega)) (he ⟨j,by omega⟩)
        (avoidsSource (j+1) _ (by omega)) (avoidsHub (j+1) _ (by omega))
  have hlast : inPair h (p (Fin.last l)) := trap l (by omega) (by omega)
  rw [ht] at hlast
  exact targetOutside h hlast

theorem disproof : ¬ (type_of% @OMA.S_mo_442518.main) := by
  intro h
  exact noLongPath (h (Fin 8) G 3 no_loop strongTwo degree 0 1 (by decide))

end DirectedPathCounterexample

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_442518.main) :=
  DirectedPathCounterexample.disproof

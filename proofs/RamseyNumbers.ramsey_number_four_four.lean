import FormalConjectures.Wikipedia.RamseyNumbers

/-! Shorter proof of R(4,4) = 18 via parity for R(3,4) ≤ 9 and the Paley(17) graph. -/

open SimpleGraph Finset RamseyNumbers
namespace OMA.Ramsey44

private lemma two (l : ℕ) : IsGraphRamsey l 2 l := fun G ⟨hg, hc⟩ => by
  rw [cliqueFree_two] at hg; subst G
  exact hc univ ⟨fun _ _ _ _ h => by simpa using h, by simp⟩

private lemma deg {n k l r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hR : IsGraphRamsey r k l) (hG : G.CliqueFree (k + 1)) (hGc : Gᶜ.CliqueFree l) (v : Fin n) :
    G.degree v < r := by
  classical
  by_contra! h
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset
    (s := G.neighborFinset v) (α := Fin r) (by simpa using h)
  exact hR (G.comap e) ⟨fun s hs => hG (insert v (s.map e)) <|
      (IsNClique.mono (map_comap_le e G) hs.map).insert fun w hw => by
        obtain ⟨i, _, rfl⟩ := mem_map.mp hw
        exact (G.mem_neighborFinset v _).mp (he ⟨i, rfl⟩),
    CliqueFree.comap (Embedding.complEquiv (Embedding.comap e G)).isContained hGc⟩

private lemma sdeg {n k l r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hR : IsGraphRamsey r l k) (hG : G.CliqueFree k) (hGc : Gᶜ.CliqueFree (l + 1)) (v : Fin n) :
    n - 1 - G.degree v < r := by
  classical have h := deg Gᶜ hR hGc (by simpa using hG) v; simpa [degree_compl] using h

private lemma r33 : IsGraphRamsey 6 3 3 := fun G ⟨h1, h2⟩ => by
  classical have := deg G (two 3) h1 h2 0; have := sdeg G (two 3) h1 h2 0; omega

private lemma r34 : IsGraphRamsey 9 3 4 := fun G ⟨h1, h2⟩ => by
  classical
  have hd (v : Fin 9) : G.degree v = 3 := by
    have := deg G (two 4) h1 h2 v; have := sdeg G r33 h1 h2 v; omega
  have := G.sum_degrees_eq_twice_card_edges; simp [hd] at this; omega

private lemma upper : IsGraphRamsey 18 4 4 := fun G ⟨h1, h2⟩ => by
  classical have := deg G r34 h1 h2 0; have := sdeg G r34 h1 h2 0; omega

private def adj (x y : Fin 17) : Bool := Nat.testBit 107286 ((17 + y.val - x.val) % 17)

private def P : SimpleGraph (Fin 17) where
  Adj x y := adj x y = true
  symm := ⟨by
    have h : ∀ x y, adj x y = adj y x := by decide +kernel
    intro x y hx; rwa [← h]⟩
  loopless := ⟨fun x => by
    have h : ∀ y, adj y y = false := by decide +kernel
    simp [h]⟩

private def find (a : Fin 17 → Fin 17 → Bool) : ℕ → List (Fin 17) → Bool
  | 0, _ => true
  | n + 1, L => L.any fun u => find a n (L.filter fun v => decide (u < v) && a u v)

private lemma find_ok (G : SimpleGraph (Fin 17)) (a : Fin 17 → Fin 17 → Bool)
    (ha : ∀ ⦃u v⦄, G.Adj u v → a u v = true) {n : ℕ} {s : Finset (Fin 17)} {L : List (Fin 17)}
    (hs : G.IsNClique n s) (hL : ∀ x ∈ s, x ∈ L) : find a n L = true := by
  induction n generalizing s L with
  | zero => rfl
  | succ n ih =>
    have hne : s.Nonempty := card_pos.mp (hs.card_eq ▸ Nat.succ_pos _)
    let u := s.min' hne
    have hu := s.min'_mem hne
    refine List.any_eq_true.mpr ⟨u, hL u hu, ih (by simpa using hs.erase_of_mem hu) fun x hx => ?_⟩
    obtain ⟨hne', hxs⟩ := mem_erase.mp hx
    exact List.mem_filter.mpr ⟨hL x hxs, by
      simp [u, lt_of_le_of_ne (s.min'_le x hxs) hne'.symm, ha (hs.isClique hu hxs hne'.symm)]⟩

private def na (u v : Fin 17) : Bool := decide (u ≠ v) && !adj u v

private lemma lower : ¬ IsGraphRamsey 17 4 4 := fun h => h P
  ⟨fun _ hs => by
    have t : find adj 4 (List.finRange 17) = false := by decide +kernel
    have := find_ok P adj (fun _ _ h => h) hs (fun _ _ => List.mem_finRange _)
    simp_all,
   fun _ hs => by
    have t : find na 4 (List.finRange 17) = false := by decide +kernel
    have := find_ok Pᶜ na (fun _ _ ⟨h1, h2⟩ => by simp [na, h1, Bool.eq_false_iff.mpr h2]) hs
      (fun _ _ => List.mem_finRange _)
    simp_all⟩

end OMA.Ramsey44

open OMA.Ramsey44 in
theorem OMA.solution : type_of% @RamseyNumbers.ramsey_number_four_four := by
  rw [classicalRamsey_eq_sInf]
  refine le_antisymm (Nat.sInf_le upper) ?_
  by_contra! h
  exact lower (monotone_nat_of_le_succ (f := fun n => IsGraphRamsey n 4 4)
    (fun n => IsGraphRamsey.succ n 4 4) (show sInf {n | IsGraphRamsey n 4 4} ≤ 17 by omega)
    (Nat.sInf_mem (s := {n | IsGraphRamsey n 4 4}) ⟨18, upper⟩))

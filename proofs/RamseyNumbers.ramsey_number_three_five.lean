import FormalConjectures.Wikipedia.RamseyNumbers

/-! Shorter proof of R(3,5) = 14 via the circulant C(13; 1, 5) and degree bounds. -/

open SimpleGraph Finset RamseyNumbers
namespace OMA.Ramsey35

private def adj (x y : Fin 13) : Bool := Nat.testBit 4386 ((13 + y.val - x.val) % 13)

private def P : SimpleGraph (Fin 13) where
  Adj x y := adj x y = true
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩

private def find (a : Fin 13 → Fin 13 → Bool) : ℕ → List (Fin 13) → Bool
  | 0, _ => true
  | n + 1, L => L.any fun u => find a n (L.filter fun v => decide (u < v) && a u v)

private lemma find_ok (G : SimpleGraph (Fin 13)) (a : Fin 13 → Fin 13 → Bool)
    (ha : ∀ ⦃u v⦄, G.Adj u v → a u v = true) {n : ℕ} {s : Finset (Fin 13)} {L : List (Fin 13)}
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

private def na (u v : Fin 13) : Bool := decide (u ≠ v) && !adj u v

private lemma lower : ¬ IsGraphRamsey 13 3 5 := fun h => h P
  ⟨fun _ hs => by
    have t : find adj 3 (List.finRange 13) = false := by decide +kernel
    have := find_ok P adj (fun _ _ h => h) hs (fun _ _ => List.mem_finRange _)
    simp_all,
   fun _ hs => by
    have t : find na 5 (List.finRange 13) = false := by decide +kernel
    have := find_ok Pᶜ na (fun _ _ ⟨h1, h2⟩ => by simp [na, h1, Bool.eq_false_iff.mpr h2]) hs
      (fun _ _ => List.mem_finRange _)
    simp_all⟩

private lemma dlt {n k : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) (hc : Gᶜ.CliqueFree k) (v : Fin n) : G.degree v < k := by
  by_contra! h
  exact hc.mono h (G.neighborFinset v) ⟨by
    rw [G.coe_neighborFinset, G.isClique_compl]; exact G.isIndepSet_neighborSet_of_triangleFree hG v,
    rfl⟩

private lemma nlt {n k m : ℕ} (hr : IsGraphRamsey m 3 k) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : G.CliqueFree 3) (hc : Gᶜ.CliqueFree (k + 1)) (v : Fin n) :
    n - 1 - G.degree v < m := by
  classical
  by_contra! h
  have h' : m ≤ Gᶜ.degree v := by simpa [G.degree_compl] using h
  obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset (α := Fin m)
    (s := Gᶜ.neighborFinset v) (by simpa using h')
  exact hr (G.comap f) ⟨CliqueFree.comap (Embedding.comap f G).isContained hG, fun t ht =>
    hc (insert v (t.map f)) <| IsNClique.insert (a := v)
      ⟨fun x hx y hy hxy => by
        obtain ⟨i, hi, rfl⟩ := mem_map.mp hx; obtain ⟨j, hj, rfl⟩ := mem_map.mp hy
        exact (Embedding.complEquiv (Embedding.comap f G)).map_adj_iff.mpr
          (ht.isClique hi hj fun e => hxy (congrArg f e)),
       (card_map _).trans ht.card_eq⟩
      fun w hw => by
        obtain ⟨i, _, rfl⟩ := mem_map.mp hw; exact (Gᶜ.mem_neighborFinset v _).mp (hf ⟨i, rfl⟩)⟩

private lemma r33 : IsGraphRamsey 6 3 3 := fun G ⟨hG, hc⟩ => by
  classical
  have := dlt G hG hc 0
  have h := dlt Gᶜ hc (by simpa using hG) 0
  simp [G.degree_compl] at h; omega

private lemma r34 : IsGraphRamsey 9 3 4 := fun G ⟨hG, hc⟩ => by
  classical
  have hd (v : Fin 9) : G.degree v = 3 := by
    have := dlt G hG hc v; have := nlt r33 G hG hc v; omega
  have := G.sum_degrees_eq_twice_card_edges; simp [hd] at this; omega

private lemma r35 : IsGraphRamsey 14 3 5 := fun G ⟨hG, hc⟩ => by
  classical have := dlt G hG hc 0; have := nlt r34 G hG hc 0; omega

end OMA.Ramsey35

open OMA.Ramsey35 in
theorem OMA.solution : type_of% @RamseyNumbers.ramsey_number_three_five := by
  rw [classicalRamsey_eq_sInf]
  refine IsLeast.csInf_eq ⟨r35, fun n hn => ?_⟩
  by_contra! h
  exact lower (monotone_nat_of_le_succ (f := fun m => IsGraphRamsey m 3 5)
    (fun m => IsGraphRamsey.succ m 3 5) (show n ≤ 13 by omega) hn)

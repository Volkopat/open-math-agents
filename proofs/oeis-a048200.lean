import OMAStatements.S_oeis_a048200
import Mathlib

-- Credit: @rpinho
-- The exact minimum is the sum of two independent lower bounds. The rotation
-- bound tracks the lifted positions of the tokens as the cursor goes forwards.
-- The swap bound counts pairs whose relative order must change on the circle.
-- A block reversal schedule attains both bounds at once.

namespace Reversal

private def slot (n : ℕ) (x : ℤ) : ℕ := (x % (n : ℤ)).toNat

private lemma slot_lt {n : ℕ} (hn : 0 < n) (x : ℤ) : slot n x < n := by
  have pos : (0 : ℤ) < n := by exact_mod_cast hn
  unfold slot
  have lower := Int.emod_nonneg x pos.ne'
  have upper := Int.emod_lt_of_pos x pos
  omega

private lemma coe_slot {n : ℕ} (hn : 0 < n) (x : ℤ) :
    (slot n x : ℤ) = x % (n : ℤ) := by
  unfold slot
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hn.ne'))

private lemma slot_mod {n : ℕ} (hn : 0 < n) (x : ℤ) :
    (slot n x : ℤ) ≡ x [ZMOD n] := by
  rw [coe_slot hn]
  exact Int.mod_modEq x n

private lemma slot_of_mod {n : ℕ} {x y : ℤ} (h : x ≡ y [ZMOD n]) :
    slot n x = slot n y := congrArg Int.toNat h

private lemma slot_nat {n j : ℕ} : slot n (j : ℤ) = j % n := by
  simp only [slot, ← Int.natCast_emod, Int.toNat_natCast]

private lemma slot_in_range {n j : ℕ} (hj : j < n) : slot n (j : ℤ) = j := by
  simpa only [slot_nat] using Nat.mod_eq_of_lt hj

private def exchange : List ℕ → List ℕ
  | x :: y :: tail => y :: x :: tail
  | list => list

private lemma length_exchange (l : List ℕ) : (exchange l).length = l.length := by
  rcases l with _ | ⟨x, _ | ⟨y, ys⟩⟩ <;> rfl

private def op (l : List ℕ) (b : Bool) : List ℕ := if b then l.rotate 1 else exchange l

private def shift (n : ℕ) (r : ℕ) (p : ℤ) : ℤ :=
  if slot n (p - (r : ℤ)) = 0 then p + 1
  else if slot n (p - (r : ℤ)) = 1 then p - 1
  else p

private def nextIndex (j : ℕ) : ℕ := if j = 0 then 1 else if j = 1 then 0 else j

private lemma exchange_get {l : List ℕ} (h : 2 ≤ l.length) (j : ℕ) (hj : j < l.length) :
    (exchange l)[nextIndex j]'(by
      rw [length_exchange]; unfold nextIndex; split <;> (try split) <;> omega) = l[j] := by
  rcases l with _ | ⟨x, _ | ⟨y, ys⟩⟩
  · simp at h
  · simp at h
  cases j with
  | zero => rfl
  | succ j =>
    cases j with
    | zero => rfl
    | succ j => rfl

private lemma slot_shift {n r : ℕ} (hn : 2 ≤ n) (p : ℤ) :
    slot n (shift n r p - (r : ℤ)) = nextIndex (slot n (p - (r : ℤ))) := by
  have hm := slot_mod (by omega : 0 < n) (p - (r : ℤ))
  simp only [shift, nextIndex]
  split
  next h =>
    have same : (p + 1 - (r : ℤ)) ≡ 1 [ZMOD n] := by
      have h' := hm.symm.add (Int.ModEq.refl 1)
      rw [h, Nat.cast_zero, zero_add] at h'
      convert h' using 1 <;> ring
    rw [slot_of_mod same]
    exact slot_in_range (by omega : 1 < n)
  next h =>
    split
    next hh =>
      have same : (p - 1 - (r : ℤ)) ≡ 0 [ZMOD n] := by
        have h' := hm.symm.sub (Int.ModEq.refl 1)
        rw [hh, Nat.cast_one, sub_self] at h'
        convert h' using 1 <;> ring
      rw [slot_of_mod same]
      exact slot_in_range (by omega : 0 < n)
    next _ => rfl

private structure Track (n : ℕ) (hn : 2 ≤ n) (p : Fin n → ℤ) (r : ℕ) (l : List ℕ) : Prop where
  len : l.length = n
  get : ∀ i : Fin n, l[slot n (p i - (r : ℤ))]'(by
    rw [len]; exact slot_lt (by omega) _) = i.val

private lemma Track.start {n : ℕ} (hn : 2 ≤ n) : Track n hn (fun i => i.val) 0 (List.range n) := by
  refine ⟨List.length_range, fun i => ?_⟩
  simp only [Nat.cast_zero, sub_zero, slot_in_range i.isLt, List.getElem_range]

private lemma Track.rotated {n : ℕ} {hn : 2 ≤ n} {p : Fin n → ℤ} {r : ℕ} {l : List ℕ}
    (h : Track n hn p r l) : Track n hn p (r+1) (l.rotate 1) := by
  refine ⟨(List.length_rotate _ _).trans h.len, fun i => ?_⟩
  simp only [List.getElem_rotate]
  have hm := (slot_mod (by omega : 0 < n) (p i - ((r+1 : ℕ) : ℤ))).add (Int.ModEq.refl 1)
  have hm' : ((slot n (p i - ((r+1 : ℕ) : ℤ)) + 1 : ℕ) : ℤ) ≡ p i - (r : ℤ) [ZMOD n] := by
    convert hm using 1 <;> push_cast <;> ring
  have hs := slot_of_mod hm'
  rw [slot_nat] at hs
  simpa only [h.len, hs] using h.get i

private lemma Track.exchanged {n : ℕ} {hn : 2 ≤ n} {p : Fin n → ℤ} {r : ℕ} {l : List ℕ}
    (h : Track n hn p r l) : Track n hn (fun i => shift n r (p i)) r (exchange l) := by
  refine ⟨(length_exchange _).trans h.len, fun i => ?_⟩
  simp only [slot_shift hn]
  have len : 2 ≤ l.length := h.len ▸ hn
  rw [exchange_get len _ (by rw [h.len]; exact slot_lt (by omega) _)]
  exact h.get i

private lemma Track.slot_injective {n : ℕ} {hn : 2 ≤ n} {p : Fin n → ℤ} {r : ℕ} {l : List ℕ}
    (h : Track n hn p r l) : Function.Injective (fun i => slot n (p i - (r : ℤ))) := by
  intro i j hij
  apply Fin.ext
  rw [← h.get i, ← h.get j]
  congr

private lemma Track.final {n : ℕ} {hn : 2 ≤ n} {p : Fin n → ℤ} {r : ℕ}
    (h : Track n hn p r (List.range n).reverse) (i : Fin n) :
    p i ≡ (r : ℤ) + (n : ℤ) - 1 - i.val [ZMOD n] := by
  have he := h.get i
  simp only [List.getElem_reverse, List.length_range, List.getElem_range] at he
  have hs : slot n (p i - (r : ℤ)) < n := slot_lt (by omega) _
  have hm := (slot_mod (by omega : 0 < n) (p i - (r : ℤ))).symm.add (Int.ModEq.refl (r : ℤ))
  convert hm using 1 <;> omega

private def firstEdge (n : ℕ) (i : ℤ) : ℤ := slot n (i - 1)

private def needed (n : ℕ) (i d : ℤ) : ℤ := firstEdge n i + (d - 1) * ((n : ℤ) - 1)

private lemma needed_mod {n : ℕ} (hn : 0 < n) (i d : ℤ) : needed n i d ≡ i - d [ZMOD n] := by
  have extra : (d-1)*((n:ℤ)-1) ≡ -(d-1) [ZMOD n] := by
    apply Int.modEq_iff_dvd.2
    refine ⟨1-d, by ring⟩
  have h := (slot_mod hn (i-1)).add extra
  unfold needed firstEdge
  convert h using 1 <;> ring

private lemma bound_from_mod {n : ℕ} (a b : ℤ) (h : a ≡ b [ZMOD n])
    (lower : b - n < a) : b ≤ a := by
  by_contra! bad
  rcases h.dvd with ⟨k, hk⟩
  have hkpos : 0 < k := by
    by_contra! kneg
    have := mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg n) kneg
    omega
  have minimum := mul_nonneg (Int.natCast_nonneg n) (show 0 ≤ k - 1 by omega)
  nlinarith

private def BackwardBound (n r : ℕ) (p : Fin n → ℤ) : Prop :=
  ∀ (i : Fin n) (d : ℤ), 1 ≤ d → p i ≤ (i.val : ℤ) - d → needed n i.val d ≤ (r : ℤ)

private lemma BackwardBound.start (n : ℕ) : BackwardBound n 0 (fun i => i.val) := by
  intro i d hd hp
  dsimp at hp
  omega

private lemma BackwardBound.rotated {n r : ℕ} {p : Fin n → ℤ} (h : BackwardBound n r p) :
    BackwardBound n (r+1) p := fun i d hd hp => by
  have := h i d hd hp
  omega

private lemma BackwardBound.exchanged {n r : ℕ} {p : Fin n → ℤ} (hn : 2 ≤ n)
    (h : BackwardBound n r p) : BackwardBound n r (fun i => shift n r (p i)) := by
  intro i d hd hp
  dsimp only at hp
  by_cases old : p i ≤ (i.val : ℤ) - d
  · exact h i d hd old
  have edge1 : slot n (p i - (r : ℤ)) = 1 := by
    by_contra neq
    simp only [shift, if_neg neq] at hp
    split at hp <;> omega
  have edge0 : slot n (p i - (r : ℤ)) ≠ 0 := by omega
  have exact_pos : p i - 1 = (i.val : ℤ) - d := by
    simp only [shift, if_neg edge0, if_pos edge1] at hp
    omega
  have hr : (r : ℤ) ≡ (i.val : ℤ) - d [ZMOD n] := by
    have hm := (slot_mod (by omega : 0 < n) (p i - (r : ℤ))).symm
    rw [edge1, Nat.cast_one] at hm
    have hm' := hm.sub (Int.ModEq.refl 1)
    rw [sub_self] at hm'
    have div := hm'.symm.dvd
    apply Int.modEq_iff_dvd.mpr
    convert div using 1 <;> omega
  apply bound_from_mod (r : ℤ) (needed n i.val d) (hr.trans (needed_mod (by omega) _ _).symm)
  by_cases first : d = 1
  · have hlt := slot_lt (by omega : 0 < n) ((i.val : ℤ)-1)
    simp only [needed, first, sub_self, zero_mul, add_zero, firstEdge]
    omega
  · have hprev := h i (d-1) (by omega) (by omega)
    have change : needed n i.val d = needed n i.val (d-1) + ((n : ℤ) - 1) := by
      unfold needed
      ring
    rw [change]
    omega

private lemma Track.slot_exists {n : ℕ} {hn : 2 ≤ n} {p : Fin n → ℤ} {r : ℕ} {l : List ℕ}
    (h : Track n hn p r l) (j : ℕ) (hj : j < n) : ∃ i : Fin n, slot n (p i - (r : ℤ)) = j := by
  let f (i : Fin n) : Fin n := ⟨slot n (p i - (r : ℤ)), slot_lt (by omega) _⟩
  have hf : Function.Injective f := fun i j hij => h.slot_injective (congrArg Fin.val hij)
  obtain ⟨i, eq⟩ := (Finite.surjective_of_injective hf) ⟨j, hj⟩
  exact ⟨i, congrArg Fin.val eq⟩

private lemma Track.sum_exchange {n : ℕ} {hn : 2 ≤ n} {p : Fin n → ℤ} {r : ℕ} {l : List ℕ}
    (h : Track n hn p r l) : ∑ i, shift n r (p i) = ∑ i, p i := by
  obtain ⟨u, hu⟩ := h.slot_exists 0 (by omega)
  obtain ⟨v, hv⟩ := h.slot_exists 1 (by omega)
  have point (i : Fin n) : shift n r (p i) =
      p i + (if i = u then (1 : ℤ) else 0) - (if i = v then (1 : ℤ) else 0) := by
    have h0 : slot n (p i - (r : ℤ)) = 0 ↔ i = u := by
      constructor
      · intro hz; exact h.slot_injective (hz.trans hu.symm)
      · intro hi; simpa [hi] using hu
    have h1 : slot n (p i - (r : ℤ)) = 1 ↔ i = v := by
      constructor
      · intro hz; exact h.slot_injective (hz.trans hv.symm)
      · intro hi; simpa [hi] using hv
    have uv : u ≠ v := by
      intro eq
      rw [eq, hv] at hu
      omega
    simp only [shift, h0, h1]
    by_cases iu : i = u <;> by_cases iv : i = v <;> simp [iu, iv] <;> omega
  simp only [point, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Int.add_sub_cancel]

private def orderedClose (n : ℕ) (a b : ℤ) : Prop := 0 < b - a ∧ b - a < (n : ℤ)

private noncomputable def crossed (n : ℕ) (p : Fin n → ℤ) : Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.filter fun (i,j) =>
    (i < j ∧ ¬ orderedClose n (p i) (p j)) ∨ (j < i ∧ ¬ orderedClose n (p j) (p i))

private lemma mem_crossed {n : ℕ} {p : Fin n → ℤ} {i j : Fin n} :
    (i,j) ∈ crossed n p ↔
      (i < j ∧ ¬ orderedClose n (p i) (p j)) ∨ (j < i ∧ ¬ orderedClose n (p j) (p i)) := by
  classical
  simp [crossed]

private lemma crossed_empty (n : ℕ) : crossed n (fun i => i.val) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  rintro ⟨i,j⟩ h
  rcases mem_crossed.mp h with ⟨ij, bad⟩ | ⟨ji, bad⟩ <;>
    apply bad <;> unfold orderedClose <;> omega

private lemma Track.mod_ne {n : ℕ} {hn : 2 ≤ n} {p : Fin n → ℤ} {r : ℕ} {l : List ℕ}
    (h : Track n hn p r l) {a b : Fin n} (hne : a ≠ b) : ¬ p a ≡ p b [ZMOD n] := by
  intro hm
  exact hne (h.slot_injective (slot_of_mod (hm.sub (Int.ModEq.refl (r : ℤ)))))

private lemma Track.crossed_swap {n : ℕ} {hn : 2 ≤ n} {p : Fin n → ℤ} {r : ℕ} {l : List ℕ}
    (h : Track n hn p r l) : (crossed n (fun i => shift n r (p i))).card ≤ (crossed n p).card + 2 := by
  obtain ⟨u, hu⟩ := h.slot_exists 0 (by omega)
  obtain ⟨v, hv⟩ := h.slot_exists 1 (by omega)
  have opposite (i j : Fin n) (hne : i ≠ j)
      (old : orderedClose n (p i) (p j)) (new : ¬ orderedClose n (shift n r (p i)) (shift n r (p j))) :
      (i = u ∧ j = v) ∨ (i = v ∧ j = u) := by
    let si := slot n (p i - (r : ℤ))
    let sj := slot n (p j - (r : ℤ))
    have si0 (s : si = 0) : i = u := h.slot_injective (s.trans hu.symm)
    have si1 (s : si = 1) : i = v := h.slot_injective (s.trans hv.symm)
    have sj0 (s : sj = 0) : j = u := h.slot_injective (s.trans hu.symm)
    have sj1 (s : sj = 1) : j = v := h.slot_injective (s.trans hv.symm)
    have hnmod : ¬ shift n r (p i) ≡ shift n r (p j) [ZMOD n] := h.exchanged.mod_ne hne
    have nz : shift n r (p j) - shift n r (p i) ≠ 0 := by
      intro hz
      apply hnmod
      have eq : shift n r (p i) = shift n r (p j) := by omega
      rw [eq]
    have nn : shift n r (p j) - shift n r (p i) ≠ (n : ℤ) := by
      intro hz
      apply hnmod
      exact Int.modEq_iff_dvd.mpr ⟨1, by simpa using hz⟩
    have move_i : shift n r (p i) = if si = 0 then p i+1 else if si = 1 then p i-1 else p i := rfl
    have move_j : shift n r (p j) = if sj = 0 then p j+1 else if sj = 1 then p j-1 else p j := rfl
    by_cases siZero : si = 0
    · by_cases sjOne : sj = 1
      · exact Or.inl ⟨si0 siZero, sj1 sjOne⟩
      have sjNotZero : sj ≠ 0 := fun z => hne ((si0 siZero).trans (sj0 z).symm)
      exfalso
      apply new
      unfold orderedClose at old ⊢
      simp only [move_i, move_j, if_pos siZero, if_neg sjOne, if_neg sjNotZero] at nz nn ⊢
      omega
    by_cases siOne : si = 1
    · by_cases sjZero : sj = 0
      · exact Or.inr ⟨si1 siOne, sj0 sjZero⟩
      have sjNotOne : sj ≠ 1 := fun z => hne ((si1 siOne).trans (sj1 z).symm)
      exfalso
      apply new
      unfold orderedClose at old ⊢
      simp only [move_i, move_j, if_neg siZero, if_pos siOne, if_neg sjZero, if_neg sjNotOne] at nz nn ⊢
      omega
    exfalso
    apply new
    unfold orderedClose at old ⊢
    have still_i : shift n r (p i) = p i := by simp only [move_i, if_neg siZero, if_neg siOne]
    have one_step : -1 ≤ shift n r (p j) - p j ∧ shift n r (p j) - p j ≤ 1 := by
      rw [move_j]
      split <;> (try split) <;> omega
    rw [still_i] at nz nn ⊢
    omega
  have subset : crossed n (fun i => shift n r (p i)) ⊆
      insert (u,v) (insert (v,u) (crossed n p)) := by
    rintro ⟨i,j⟩ hj
    simp only [mem_crossed, Finset.mem_insert, Prod.mk.injEq] at hj ⊢
    rcases hj with ⟨ij, bad⟩ | ⟨ji, bad⟩
    · by_cases old : orderedClose n (p i) (p j)
      · rcases opposite i j (ne_of_lt ij) old bad with edge | edge
        · exact Or.inl edge
        · exact Or.inr (Or.inl edge)
      · exact Or.inr (Or.inr (Or.inl ⟨ij, old⟩))
    · by_cases old : orderedClose n (p j) (p i)
      · rcases opposite j i (ne_of_lt ji) old bad with edge | edge
        · exact Or.inr (Or.inl ⟨edge.2, edge.1⟩)
        · exact Or.inl ⟨edge.2, edge.1⟩
      · exact Or.inr (Or.inr (Or.inr ⟨ji, old⟩))
  have hcard := Finset.card_mono subset
  have c1 := Finset.card_insert_le (u,v) (insert (v,u) (crossed n p))
  have c2 := Finset.card_insert_le (v,u) (crossed n p)
  omega

private def read {n : ℕ} (word : List Bool) (p : Fin n → ℤ) (r : ℕ) (l : List ℕ) :
    (Fin n → ℤ) × ℕ × List ℕ :=
  match word with
  | [] => (p,r,l)
  | true :: tail => read tail p (r+1) (l.rotate 1)
  | false :: tail => read tail (fun i => shift n r (p i)) r (exchange l)

private lemma read_tracker {n r : ℕ} {p : Fin n → ℤ} {l : List ℕ} {hn : 2 ≤ n}
    (word : List Bool) (track : Track n hn p r l) (back : BackwardBound n r p) :
    let z := read word p r l
    Track n hn z.1 z.2.1 z.2.2 ∧ BackwardBound n z.2.1 z.1 ∧ z.2.1 = r + word.count true ∧
      (∑ i, z.1 i) = ∑ i, p i ∧
      (crossed n z.1).card ≤ (crossed n p).card + 2 * word.count false := by
  induction word generalizing p r l with
  | nil =>
    simp [read, track, back]
  | cons b rest ih =>
    cases b
    · have result :=  ih track.exchanged (back.exchanged hn)
      dsimp only at result ⊢
      rcases result with ⟨ht, hb, hr, hs, hc⟩
      simp only [read, List.count_cons, Bool.false_eq_true, ↓reduceIte, add_zero, BEq.rfl]
      refine ⟨ht, hb, hr, hs.trans track.sum_exchange, ?_⟩
      have hc' := track.crossed_swap
      omega
    · have result :=  ih track.rotated back.rotated
      dsimp only at result ⊢
      rcases result with ⟨ht, hb, hr, hs, hc⟩
      simp only [read, List.count_cons, Bool.true_eq_false, ↓reduceIte, add_zero, BEq.rfl]
      refine ⟨ht, hb, ?_, hs, hc⟩
      omega

private lemma read_list {n r : ℕ} (word : List Bool) (p : Fin n → ℤ) (l : List ℕ) :
    (read word p r l).2.2 = word.foldl op l := by
  induction word generalizing p r l with
  | nil => rfl
  | cons b rest ih => cases b <;> simp [read, op, ih]

private lemma count_swaps {n r s : ℕ} {p : Fin n → ℤ} {hn : 2 ≤ n}
    (t : Track n hn p r (List.range n).reverse) (hc : (crossed n p).card ≤ 2 * s) :
    (n : ℤ)^2 - 2*n ≤ 4*s := by
  classical
  have lift (i : Fin n) : ∃ k : ℤ,
      p i = (r : ℤ) + n - 1 - i.val + n*k := by
    obtain ⟨k,hk⟩ := (t.final i).dvd
    exact ⟨-k, by push_cast at *; linarith⟩
  choose k hk using lift
  let even := (Finset.univ : Finset (Fin n)).filter (fun i => k i % 2 = 0)
  let odd := (Finset.univ : Finset (Fin n)).filter (fun i => k i % 2 ≠ 0)
  have hcard : even.card + odd.card = n := by
    simpa [even, odd] using
      Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (fun i => k i % 2 = 0)
  have disj : Disjoint even.offDiag odd.offDiag := by
    rw [Finset.disjoint_left]
    rintro ⟨i,j⟩ he ho
    have e := (Finset.mem_offDiag.mp he).1
    have o := (Finset.mem_offDiag.mp ho).1
    exact (Finset.mem_filter.mp o).2 (Finset.mem_filter.mp e).2
  have same (i j : Fin n) (ij : i < j) (parity : k i % 2 = k j % 2) :
      ¬ orderedClose n (p i) (p j) := by
    intro h
    unfold orderedClose at h
    rw [hk i, hk j] at h
    have hj : (j.val : ℤ) < n := by exact_mod_cast j.isLt
    have hi : (i.val : ℤ) < j.val := by exact_mod_cast ij
    have low : 0 ≤ k j - k i - 1 := by
      by_contra! h'
      have t' := mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg n) (show k j - k i ≤ 0 by omega)
      nlinarith only [h.1, hi, t']
    have high : k j - k i - 1 ≤ 0 := by
      by_contra! h'
      have t' := mul_nonneg (Int.natCast_nonneg n) (show 0 ≤ k j - k i - 2 by omega)
      nlinarith only [h.2, hj, Int.natCast_nonneg i.val, t']
    omega
  have all : even.offDiag ∪ odd.offDiag ⊆ crossed n p := by
    rintro ⟨i,j⟩ h
    have hp : i ≠ j ∧ k i % 2 = k j % 2 := by
      rcases (Finset.mem_union.mp h) with he | ho
      · obtain ⟨hi,hj,hne⟩ := Finset.mem_offDiag.mp he
        exact ⟨hne, ((Finset.mem_filter.mp hi).2).trans (Finset.mem_filter.mp hj).2.symm⟩
      · obtain ⟨hi,hj,hne⟩ := Finset.mem_offDiag.mp ho
        exact ⟨hne, by
          have a := (Finset.mem_filter.mp hi).2
          have b := (Finset.mem_filter.mp hj).2
          change k i % 2 ≠ 0 at a
          change k j % 2 ≠ 0 at b
          omega⟩
    rcases lt_or_gt_of_ne hp.1 with ij | ji
    · exact mem_crossed.mpr (Or.inl ⟨ij, same i j ij hp.2⟩)
    · exact mem_crossed.mpr (Or.inr ⟨ji, same j i ji hp.2.symm⟩)
  have limit := (Finset.card_mono all).trans hc
  rw [Finset.card_union_of_disjoint disj, Finset.offDiag_card, Finset.offDiag_card] at limit
  have e : even.card ≤ even.card * even.card := by
    cases h : even.card with
    | zero => simp
    | succ d => nlinarith [Nat.zero_le (d*d)]
  have o : odd.card ≤ odd.card * odd.card := by
    cases h : odd.card with
    | zero => simp
    | succ d => nlinarith [Nat.zero_le (d*d)]
  zify [e, o] at limit hcard
  nlinarith only [limit, congrArg (fun x : ℤ => x^2) hcard,
    sq_nonneg ((even.card : ℤ) - (odd.card : ℤ)), hcard]

private lemma cast_slot_bounds {n : ℕ} (hn : 0 < n) (z : ℤ) :
    0 ≤ (slot n z : ℤ) ∧ (slot n z : ℤ) < n :=
  ⟨Int.natCast_nonneg _, by exact_mod_cast slot_lt hn z⟩

private def reflIndex (n : ℕ) (hn : 0 < n) (c : ℤ) : Equiv.Perm (Fin n) where
  toFun i := ⟨slot n (c-i.val), slot_lt hn _⟩
  invFun i := ⟨slot n (c-i.val), slot_lt hn _⟩
  left_inv i := by
    apply Fin.ext
    change slot n (c-(slot n (c-i.val) : ℤ)) = i.val
    have mod := (Int.ModEq.refl c).sub (slot_mod hn (c-i.val))
    have e : c - (c - (i.val : ℤ)) = i.val := by ring
    rw [e] at mod
    rw [slot_of_mod mod, slot_in_range i.isLt]
  right_inv i := by
    apply Fin.ext
    change slot n (c-(slot n (c-i.val) : ℤ)) = i.val
    have mod := (Int.ModEq.refl c).sub (slot_mod hn (c-i.val))
    have e : c - (c - (i.val : ℤ)) = i.val := by ring
    rw [e] at mod
    rw [slot_of_mod mod, slot_in_range i.isLt]

private def remainder (n : ℕ) (z : ℤ) (i : Fin n) : ℤ := slot n (z - 2*i.val)

private lemma sum_remainders {n : ℕ} (hn : 0 < n) (z c C : ℤ)
    (total : 2*z - 2*c = C)
    (inRange : ∀ i : Fin n, 0 ≤ C - remainder n z i ∧ C - remainder n z i < n) :
    2 * (∑ i, remainder n z i) = (n : ℤ) * C := by
  let reflect := reflIndex n hn c
  have point (i : Fin n) : remainder n z (reflect i) = C - remainder n z i := by
    have idx : ((reflect i).val : ℤ) ≡ c - (i.val : ℤ) [ZMOD n] := slot_mod hn _
    have a := (Int.ModEq.refl z).sub (idx.mul_left 2)
    have b := slot_mod hn (z - 2 * (reflect i).val)
    have d := a.sub (Int.ModEq.refl 0)
    rw [sub_zero, sub_zero] at d
    have qi : remainder n z i ≡ z - 2*i.val [ZMOD n] := slot_mod hn _
    have eq1 : z - 2 * (c - (i.val : ℤ)) = C - (z - 2 * (i.val : ℤ)) := by linarith
    rw [eq1] at d
    have heq : remainder n z (reflect i) ≡ C - remainder n z i [ZMOD n] :=
      b.trans (d.trans ((Int.ModEq.refl C).sub qi.symm))
    obtain ⟨b0,bn⟩ := cast_slot_bounds hn (z - 2*(reflect i).val)
    obtain ⟨c0,cn⟩ := inRange i
    change 0 ≤ remainder n z (reflect i) at b0
    change remainder n z (reflect i) < (n : ℤ) at bn
    exact le_antisymm (bound_from_mod _ _ heq.symm (by omega))
      (bound_from_mod _ _ heq (by omega))
  have pairSum : (∑ i : Fin n, (remainder n z i + remainder n z (reflect i))) =
      (n : ℤ)*C := by
    simp only [point, add_sub_cancel, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.sum_add_distrib, Equiv.sum_comp reflect (remainder n z)] at pairSum
  linarith

private lemma shift_residue {n r : ℕ} {hn : 2 ≤ n} {p : Fin n → ℤ}
    (h : Track n hn p r (List.range n).reverse) (d : ℤ) (i : Fin n) :
    p i - (i.val : ℤ) + d ≡ remainder n ((r : ℤ)-1+d) i [ZMOD n] := by
  have hmod := ((h.final i).sub (Int.ModEq.refl (i.val : ℤ))).add (Int.ModEq.refl d)
  have normal : (r : ℤ)+n-1-i.val-i.val+d ≡ (r : ℤ)-1+d-2*i.val [ZMOD n] := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-1, by ring⟩
  exact hmod.trans (normal.trans (slot_mod (by omega) _).symm)

private lemma minimal_digits {n r : ℕ} {hn : 2 ≤ n} {p : Fin n → ℤ}
    (h : Track n hn p r (List.range n).reverse) (hs : (∑ i, p i) = ∑ i : Fin n, (i.val : ℤ))
    (d : ℤ) (nonneg : ∀ i : Fin n, 0 ≤ p i - (i.val : ℤ)+d)
    (rate : (n : ℤ)*d ≤ ∑ i, remainder n ((r : ℤ)-1+d) i) :
    (∑ i, remainder n ((r : ℤ)-1+d) i) = (n : ℤ)*d ∧
      ∀ i : Fin n, p i - (i.val : ℤ)+d = remainder n ((r : ℤ)-1+d) i := by
  let q := remainder n ((r : ℤ)-1+d)
  have each (i : Fin n) : q i ≤ p i - (i.val : ℤ)+d := by
    have bnd : q i < (n : ℤ) := (cast_slot_bounds (by omega) _).2
    exact bound_from_mod _ _ (shift_residue h d i) (by linarith [nonneg i])
  have total : ∑ i, (p i - (i.val : ℤ)+d) = (n : ℤ)*d := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, hs, sub_self, zero_add,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have equality : ∑ i, q i = (n : ℤ)*d :=
    le_antisymm ((Finset.sum_le_sum fun i _ => each i).trans_eq total) rate
  refine ⟨equality, fun i => le_antisymm ?_ (each i)⟩
  by_contra! strict
  have sumStrict := Finset.sum_lt_sum (fun j (_ : j ∈ Finset.univ) => each j)
    ⟨i, Finset.mem_univ i, strict⟩
  rw [equality, total] at sumStrict
  omega

private lemma finish_bound {n r : ℕ} {hn : 2 ≤ n} {p : Fin n → ℤ}
    (h : Track n hn p r (List.range n).reverse) (hb : BackwardBound n r p)
    (i : Fin n) (d : ℤ) (hd : 1 ≤ d) (position : p i = (i.val : ℤ)-d) :
    let a := firstEdge n i.val
    a + (d-1)*((n:ℤ)-1) + (slot n (a+2) : ℤ) ≤ r := by
  dsimp
  have least := hb i d hd position.le
  have final := (h.final i).dvd
  rw [position] at final
  have rr : (r : ℤ) ≡ 2*i.val+1-d [ZMOD n] := by
    apply Int.modEq_iff_dvd.mpr
    have := Int.dvd_sub (dvd_refl (n : ℤ)) final
    convert this using 1 <;> ring
  have diff := rr.sub (needed_mod (by omega : 0 < n) (i.val : ℤ) d)
  have rhs : 2*(i.val : ℤ)+1-d-((i.val:ℤ)-d) = i.val+1 := by ring
  rw [rhs] at diff
  have aa := (slot_mod (by omega : 0 < n) ((i.val : ℤ)-1)).add (Int.ModEq.refl 2)
  have aa' : firstEdge n i.val + 2 ≡ (i.val : ℤ)+1 [ZMOD n] := by unfold firstEdge; convert aa using 1 <;> ring
  have residue : (r : ℤ) - needed n i.val d ≡ (slot n (firstEdge n i.val + 2) : ℤ) [ZMOD n] :=
    diff.trans (aa'.symm.trans (slot_mod (by omega) _).symm)
  have lt := (cast_slot_bounds (by omega : 0 < n) (firstEdge n i.val + 2)).2
  have more := bound_from_mod _ _ residue (by omega)
  unfold needed at more
  linarith

private lemma no_long_step {n r : ℕ} {p : Fin n → ℤ} {d : ℤ}
    (back : BackwardBound n r p) (hd : 0 ≤ d) (short : (r : ℤ) < d * ((n : ℤ)-1)) :
    ∀ i : Fin n, 0 ≤ p i-(i.val : ℤ)+d := by
  intro i
  by_contra! neg
  have long := back i (d+1) (by omega) (by omega)
  unfold needed at long
  have nonneg : 0 ≤ firstEdge n i.val := Int.natCast_nonneg _
  nlinarith

private lemma exact_slot {n : ℕ} (hn : 0 < n) {z : ℤ} (h₀ : 0 ≤ z) (hn' : z < n) :
    (slot n z : ℤ) = z := by
  rw [coe_slot hn, Int.emod_eq_of_lt h₀ hn']

private lemma rotations_odd (m : ℕ) (hm : 2 ≤ m) {r : ℕ}
    {p : Fin (2*m+1) → ℤ} {hn : 2 ≤ 2*m+1}
    (h : Track (2*m+1) hn p r (List.range (2*m+1)).reverse)
    (back : BackwardBound (2*m+1) r p)
    (sum : (∑ i, p i) = ∑ i : Fin (2*m+1), (i.val : ℤ)) : 2*(m : ℤ)^2-2*m+2 ≤ r := by
  by_contra! short
  let n := 2*m+1
  let z : ℤ := (r : ℤ)-1+m
  let c : ℤ := (r : ℤ)-1
  have pos : 0 < n := by simp [n]
  have hnm : (n : ℤ) = 2*(m : ℤ)+1 := by simp [n]
  have modsum := sum_remainders pos z c (2*m)
    (by dsimp [z,c]; ring) (fun i => by
      have b := cast_slot_bounds pos (z - 2*i.val)
      change 0 ≤ remainder n z i ∧ remainder n z i < (n : ℤ) at b
      rw [hnm] at b ⊢
      omega)
  have exactsum : ∑ i, remainder n z i = (n : ℤ)*m := by nlinarith
  have noTooLong : (r : ℤ) < (m : ℤ)*((n : ℤ)-1) := by
    rw [hnm]
    linarith
  have info := minimal_digits h sum (m : ℤ) (no_long_step back (by positivity) noTooLong) exactsum.ge
  let i : Fin n := ⟨slot n (((m : ℤ)+1)*z), slot_lt pos _⟩
  have zero : remainder n z i = 0 := by
    have mi : (i.val : ℤ) ≡ ((m : ℤ)+1)*z [ZMOD n] := slot_mod pos _
    have a := (Int.ModEq.refl z).sub (mi.mul_left 2)
    have b : z-2*(((m : ℤ)+1)*z) ≡ 0 [ZMOD n] := by
      apply Int.modEq_iff_dvd.mpr
      refine ⟨z, ?_⟩
      rw [hnm]
      ring
    unfold remainder
    rw [slot_of_mod (a.trans b), exact_slot pos (by omega) (by exact_mod_cast pos)]
  have x := info.2 i
  change p i - (i.val : ℤ) + (m : ℤ) = remainder n z i at x
  rw [zero] at x
  have lb := finish_bound h back i (m : ℤ) (by omega) (by omega)
  let a := firstEdge n i.val
  change a + ((m : ℤ)-1)*((n : ℤ)-1) + (slot n (a+2) : ℤ) ≤ r at lb
  have a0 : 0 ≤ a := Int.natCast_nonneg _
  have s0 : 0 ≤ (slot n (a+2) : ℤ) := Int.natCast_nonneg _
  have ha : a + (slot n (a+2) : ℤ) ≥ 2 := by
    by_cases already : 2 ≤ a
    · omega
    have eq := exact_slot pos (z := a+2) (by omega) (by omega)
    omega
  rw [hnm] at lb
  nlinarith

private lemma rotations_even (m : ℕ) (hm : 2 ≤ m) {r : ℕ}
    {p : Fin (2*m) → ℤ} {hn : 2 ≤ 2*m}
    (h : Track (2*m) hn p r (List.range (2*m)).reverse)
    (back : BackwardBound (2*m) r p)
    (sum : (∑ i, p i) = ∑ i : Fin (2*m), (i.val : ℤ)) : 2*(m : ℤ)^2-3*m ≤ r := by
  by_contra! short
  let n := 2*m
  let d : ℤ := (m : ℤ)-1
  let z : ℤ := (r : ℤ)-1+d
  let η := z % 2
  let c : ℤ := (r : ℤ)-1-η
  have pos : 0 < n := by dsimp [n]; omega
  have hnm : (n : ℤ) = 2*(m : ℤ) := by simp [n]
  have en (i : Fin n) : remainder n z i % 2 = η := by
    have two : (2 : ℤ) ∣ (n : ℤ) := ⟨m, hnm⟩
    have hq := (slot_mod pos (z - 2*i.val)).of_dvd two
    change remainder n z i % 2 = (z - 2*i.val) % 2 at hq
    dsimp [η]
    omega
  have ηs : 0 ≤ η ∧ η ≤ 1 := by dsimp [η]; omega
  have modsum := sum_remainders pos z c (2*d+2*η) (by dsimp [z,c]; ring)
    (fun i => by
      have b := cast_slot_bounds pos (z - 2*i.val)
      change 0 ≤ remainder n z i ∧ remainder n z i < (n : ℤ) at b
      have parity := en i
      dsimp only [d]
      rw [hnm] at b ⊢
      omega)
  have exactsum : ∑ i, remainder n z i = (n : ℤ)*(d+η) := by nlinarith
  have n₀ : (0 : ℤ) < n := by exact_mod_cast pos
  have noTooLong : (r : ℤ) < d*((n : ℤ)-1) := by
    rw [hnm]; dsimp [d]; nlinarith
  have greater : (n : ℤ)*d ≤ ∑ i, remainder n z i := by
    rw [exactsum]
    gcongr
    linarith only [ηs.1]
  have info := minimal_digits h sum d (no_long_step back (by dsimp [d]; omega) noTooLong) greater
  have exactsum' : ∑ i, remainder n z i = (n : ℤ)*d := info.1
  have zeroη : η = 0 := by
    by_contra hη
    have positive : 0 < η := by omega
    nlinarith [mul_pos n₀ positive]
  let b := z / 2
  have hb : z = 2*b := by
    change z % 2 = 0 at zeroη
    dsimp [b]
    omega
  let a : ℤ := (m : ℤ)+(b-1)%(m : ℤ)
  have ma : (m : ℤ) ≤ a := by
    have low := Int.emod_nonneg (b-1) (by omega : (m : ℤ) ≠ 0)
    dsimp [a]
    omega
  have an : a < (n : ℤ) := by
    have high := Int.emod_lt_of_pos (b-1) (by omega : (0 : ℤ) < m)
    rw [hnm]
    dsimp [a]
    omega
  let i : Fin n := ⟨slot n (a+1), slot_lt pos _⟩
  have mi : (i.val : ℤ) ≡ a+1 [ZMOD n] := slot_mod pos _
  have fir : firstEdge n i.val = a := by
    have eq := mi.sub (Int.ModEq.refl 1)
    rw [add_sub_cancel_right] at eq
    unfold firstEdge
    rw [slot_of_mod eq, exact_slot pos (by omega) an]
  have zero : remainder n z i = 0 := by
    have t := (Int.ModEq.refl z).sub (mi.mul_left 2)
    have to0 : z - 2*(a+1) ≡ 0 [ZMOD n] := by
      apply Int.modEq_iff_dvd.mpr
      refine ⟨1-(b-1)/(m : ℤ), ?_⟩
      rw [hb, hnm]
      dsimp [a]
      have div := Int.emod_add_mul_ediv (b-1) (m : ℤ)
      nlinarith only [div]
    unfold remainder
    rw [slot_of_mod (t.trans to0), exact_slot pos (by omega) (by exact_mod_cast pos)]
  have x := info.2 i
  change p i - (i.val : ℤ) + d = remainder n z i at x
  rw [zero] at x
  have lb := finish_bound h back i d (by dsimp [d]; omega) (by omega)
  dsimp only at lb
  rw [fir] at lb
  have aa : (n : ℤ)-2 ≤ a + (slot n (a+2) : ℤ) := by
    by_cases close : (n : ℤ)-2 ≤ a
    · linarith [Int.natCast_nonneg (slot n (a+2))]
    rw [exact_slot pos (z := a+2) (by omega) (by omega), hnm]
    omega
  rw [hnm] at aa lb
  dsimp [d] at lb
  nlinarith

private def play (w : List Bool) (l : List ℕ) : List ℕ := w.foldl op l

private lemma play_append (w v : List Bool) (l : List ℕ) :
    play (w ++ v) l = play v (play w l) := List.foldl_append

private lemma rotate_word (k : ℕ) (l : List ℕ) :
    play (List.replicate k true) l = l.rotate k := by
  induction k generalizing l with
  | zero => simp [play]
  | succ k ih =>
    simp only [List.replicate_succ, play, List.foldl_cons, op, ↓reduceIte] at ih ⊢
    rw [ih, List.rotate_rotate, Nat.add_comm 1]

private def scan : ℕ → List Bool
  | 0 => []
  | k+1 => false :: true :: scan k

private lemma scan_length (k : ℕ) : (scan k).length = 2*k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [scan, ih]; omega

private lemma rotate_cons (a : ℕ) (l : List ℕ) : (a :: l).rotate 1 = l ++ [a] := by simp

private lemma scan_pass (a : ℕ) (active tail : List ℕ) :
    play (scan active.length) ((a :: active) ++ tail) = (a :: tail) ++ active := by
  induction active generalizing tail with
  | nil => simp [play, scan]
  | cons b rest ih =>
    change play (scan rest.length) ((b :: a :: (rest ++ tail)).rotate 1) =
      a :: (tail ++ b :: rest)
    rw [rotate_cons]
    simpa only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using ih (tail ++ [b])

private def pass (a f : ℕ) : List Bool := scan a ++ List.replicate (f+1) true

private lemma pass_length (a f : ℕ) : (pass a f).length = 2*a+f+1 := by
  simp [pass, scan_length, Nat.add_assoc]

private lemma pass_correct (a : ℕ) (active fixed tail : List ℕ) :
    play (pass active.length fixed.length) ((a :: active) ++ fixed ++ tail) =
      tail ++ active ++ (a :: fixed) := by
  unfold pass
  rw [play_append]
  rw [List.append_assoc (a::active), scan_pass, rotate_word]
  have rel := List.rotate_append_length_eq (a :: fixed) (tail ++ active)
  simpa only [List.cons_append, List.append_assoc, List.length_cons] using rel

private lemma full_sweeps (A B a b F G : List ℕ) (hs : A.length = B.length) :
    ∃ w : List Bool,
      play w (A ++ a ++ F ++ B ++ b ++ G) =
        a ++ A.reverse ++ F ++ b ++ B.reverse ++ G ∧
      w.length + A.length =
        A.length * ((A ++ a ++ F ++ B ++ b ++ G).length + A.length + a.length + b.length) := by
  induction A generalizing B F G with
  | nil =>
    have emp : B = [] := List.eq_nil_of_length_eq_zero (by simpa using hs.symm)
    simp [emp, play]
  | cons x A ih =>
    cases B with
    | nil => simp at hs
    | cons y B =>
      have equal : A.length = B.length := by simpa using hs
      obtain ⟨w, hw, lw⟩ := ih B (x :: F) (y :: G) equal
      let p := pass (A ++ a).length F.length
      let q := pass (B ++ b).length G.length
      refine ⟨p ++ q ++ w, ?_, ?_⟩
      · have pActs := pass_correct x (A ++ a) F ((y :: B) ++ b ++ G)
        change play p _ = _ at pActs
        have qActs := pass_correct y (B ++ b) G ((A ++ a) ++ x :: F)
        change play q _ = _ at qActs
        simp only [List.cons_append, List.append_assoc] at pActs qActs hw
        simp only [play_append, List.cons_append, List.append_assoc, List.reverse_cons]
        rw [pActs, qActs, hw]
        simp only [List.nil_append]
      · simp only [List.length_append, List.length_cons, p, q, pass_length] at lw ⊢
        nlinarith only [lw, equal, congrArg (fun x : ℕ => x*A.length) equal]

private lemma split_list (l : List ℕ) (k : ℕ) (hk : k ≤ l.length) :
    ∃ first rest : List ℕ, l = first ++ rest ∧ first.length = k ∧ rest.length = l.length-k := by
  exact ⟨l.take k,l.drop k,(List.take_append_drop k l).symm,
    by simp [Nat.min_eq_left hk], List.length_drop⟩

private lemma two_list (l : List ℕ) (h : l.length = 2) : ∃ a b : ℕ, l = [a,b] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp_all

private lemma one_list (l : List ℕ) (h : l.length = 1) : ∃ a : ℕ, l = [a] := by
  rcases l with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp_all

private lemma play_reversal_even (l : List ℕ) (m : ℕ) (hm : 2 ≤ m) (hl : l.length = 2*m) :
    ∃ w : List Bool, play w l = l.reverse ∧ (w.length : ℤ) = 3*(m : ℤ)^2-4*m := by
  obtain ⟨L,R,whole,lenL,lenR'⟩ := split_list l m (by omega)
  have lenR : R.length = m := by omega
  let k := m-2
  obtain ⟨A,a,left,lenA,lena⟩ := split_list L k (by dsimp [k]; omega)
  obtain ⟨B,b,right,lenB,lenb⟩ := split_list R k (by dsimp [k]; omega)
  obtain ⟨a₁,a₂,ha⟩ := two_list a (by dsimp [k] at lena; omega)
  obtain ⟨b₁,b₂,hb⟩ := two_list b (by dsimp [k] at lenb; omega)
  obtain ⟨w, into, wn⟩ := full_sweeps A B [a₁,a₂] [b₁,b₂] [] [] (by omega)
  refine ⟨w ++ pass 1 k ++ [false], ?_, ?_⟩
  · have shape : l = A ++ [a₁,a₂] ++ (B ++ [b₁,b₂]) := by rw [whole,left,right,ha,hb]
    have shape' : play w l = [a₁,a₂] ++ A.reverse ++ [b₁,b₂] ++ B.reverse := by
      simpa only [List.append_nil, List.append_assoc, shape] using into
    have passActs := pass_correct a₁ [a₂] A.reverse ([b₁,b₂] ++ B.reverse)
    simp only [List.length_singleton, List.length_reverse, lenA] at passActs
    rw [play_append, play_append, shape']
    simp only [List.append_assoc] at passActs ⊢
    rw [passActs, shape]
    simp [play, op, exchange, List.append_assoc]
  · simp only [List.length_append, List.length_cons, List.length_nil, List.append_nil, lenA, lenB] at wn
    simp only [List.length_append, pass_length, List.length_singleton]
    zify at wn
    push_cast
    have hk : (k : ℤ) = (m : ℤ)-2 := by
      dsimp [k]
      have h := Nat.sub_add_cancel hm
      zify at h
      omega
    nlinarith only [wn, hk, congrArg (fun x : ℤ => x*(k:ℤ)) hk, congrArg (fun x : ℤ => x*(m:ℤ)) hk]

private lemma play_reversal_odd (l : List ℕ) (m : ℕ) (hm : 2 ≤ m) (hl : l.length = 2*m+1) :
    ∃ w : List Bool, play w l = l.reverse ∧ (w.length : ℤ) = 3*(m : ℤ)^2-2*m+2 := by
  obtain ⟨Q,t,whole,lenQ,lenT⟩ := split_list l 2 (by omega)
  obtain ⟨z₁,z₂,hz⟩ := two_list Q lenQ
  obtain ⟨L,R,both,lenL,lenR⟩ := split_list t m (by omega)
  let k := m-2
  obtain ⟨A,a,left,lenA,lena⟩ := split_list L k (by dsimp [k]; omega)
  obtain ⟨B,b,right,lenB,lenb⟩ := split_list R k (by dsimp [k]; omega)
  obtain ⟨a₁,a₂,ha⟩ := two_list a (by dsimp [k] at lena; omega)
  obtain ⟨b₁,hb⟩ := one_list b (by dsimp [k] at lenb; omega)
  obtain ⟨w, into, wn⟩ := full_sweeps A B [a₁,a₂] [b₁,z₂,z₁] [] [] (by omega)
  refine ⟨[false,true,true] ++ w ++ pass 1 k ++ scan 2, ?_, ?_⟩
  · have shape : l = [z₁,z₂] ++ (A ++ [a₁,a₂] ++ (B ++ [b₁])) := by
      rw [whole,both,left,right,hz,ha,hb]
    have first : play [false,true,true] l = A ++ [a₁,a₂] ++ B ++ [b₁,z₂,z₁] := by
      rw [shape]
      simp [play, op, exchange, rotate_cons, List.append_assoc]
    have sweep : play w (A ++ [a₁,a₂] ++ B ++ [b₁,z₂,z₁]) =
        [a₁,a₂] ++ A.reverse ++ [b₁,z₂,z₁] ++ B.reverse := by simpa using into
    have act := pass_correct a₁ [a₂] A.reverse ([b₁,z₂,z₁] ++ B.reverse)
    simp only [List.length_singleton, List.length_reverse, lenA] at act
    simp only [play_append]
    rw [first, sweep]
    have eq : [a₁,a₂] ++ A.reverse ++ [b₁,z₂,z₁] ++ B.reverse =
         (a₁ :: [a₂]) ++ A.reverse ++ ([b₁,z₂,z₁] ++ B.reverse) := by simp [List.append_assoc]
    rw [eq, act, shape]
    have finish := scan_pass b₁ [z₂,z₁] (B.reverse ++ [a₂,a₁] ++ A.reverse)
    simp only [List.length_cons, List.length_nil] at finish
    simpa [List.append_assoc] using finish
  · simp only [List.length_append, List.length_cons, List.length_nil, List.append_nil, lenA, lenB] at wn
    simp only [List.length_append, pass_length, scan_length, List.length_cons, List.length_nil]
    zify at wn
    push_cast
    have hk : (k : ℤ) = (m : ℤ)-2 := by
      dsimp [k]
      have h := Nat.sub_add_cancel hm
      zify at h
      omega
    nlinarith only [wn, hk, congrArg (fun x : ℤ => x*(k:ℤ)) hk, congrArg (fun x : ℤ => x*(m:ℤ)) hk]

private lemma at_reversal (n : ℕ) (hn : 2 ≤ n) (w : List Bool)
    (finish : play w (List.range n) = (List.range n).reverse) :
    ∃ p : Fin n → ℤ,
      Track n hn p (w.count true) (List.range n).reverse ∧
      BackwardBound n (w.count true) p ∧
      (∑ i, p i) = (∑ i : Fin n, (i.val : ℤ)) ∧
      (crossed n p).card ≤ 2 * w.count false := by
  let z := read w (fun (i : Fin n) => (i.val : ℤ)) 0 (List.range n)
  have h := read_tracker w (Track.start hn) (BackwardBound.start n)
  dsimp only at h
  change Track n hn z.1 z.2.1 z.2.2 ∧
    BackwardBound n z.2.1 z.1 ∧ z.2.1 = 0 + w.count true ∧
    (∑ i, z.1 i) = (∑ i : Fin n, (i.val : ℤ)) ∧
    (crossed n z.1).card ≤ (crossed n (fun i => (i.val : ℤ))).card + 2*w.count false at h
  obtain ⟨track,back,r,sum,cross⟩ := h
  have last : z.2.2 = (List.range n).reverse := (read_list w _ _).trans finish
  simp only [Nat.zero_add] at r
  rw [r,last] at track
  rw [r] at back
  simpa only [crossed_empty, Finset.card_empty, Nat.zero_add] using
    (show ∃ p, Track n hn p (w.count true) (List.range n).reverse ∧
      BackwardBound n (w.count true) p ∧
      (∑ i, p i) = (∑ i : Fin n, (i.val : ℤ)) ∧
      (crossed n p).card ≤ (crossed n (fun i => (i.val : ℤ))).card + 2*w.count false from
      ⟨z.1,track,back,sum,cross⟩)

private lemma lower_even (m : ℕ) (hm : 2 ≤ m) (w : List Bool)
    (finish : play w (List.range (2*m)) = (List.range (2*m)).reverse) :
    3*(m : ℤ)^2-4*m ≤ (w.length : ℤ) := by
  obtain ⟨p,t,back,sum,cross⟩ := at_reversal (2*m) (by omega) w finish
  have rot := rotations_even m hm t back sum
  have swaps := count_swaps t cross
  simp only [Nat.cast_mul, Nat.cast_ofNat] at swaps
  have length := w.count_true_add_count_false
  zify at length
  nlinarith only [rot, swaps, length]

private lemma lower_odd (m : ℕ) (hm : 2 ≤ m) (w : List Bool)
    (finish : play w (List.range (2*m+1)) = (List.range (2*m+1)).reverse) :
    3*(m : ℤ)^2-2*m+2 ≤ (w.length : ℤ) := by
  obtain ⟨p,t,back,sum,cross⟩ := at_reversal (2*m+1) (by omega) w finish
  have rot := rotations_odd m hm t back sum
  have swaps := count_swaps t cross
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at swaps
  have near : 4*(m : ℤ)^2-1 ≤ 4*(w.count false : ℤ) := by nlinarith only [swaps]
  have swapCount : (m : ℤ)^2 ≤ (w.count false : ℤ) := by omega
  have length := w.count_true_add_count_false
  zify at length
  nlinarith only [rot, swapCount, length]

private lemma exact_minimum (n : ℕ) (v : ℤ)
    (hi : ∃ w : List Bool,
      play w (List.range n) = (List.range n).reverse ∧ (w.length : ℤ) = v)
    (lo : ∀ w : List Bool, play w (List.range n) = (List.range n).reverse → v ≤ (w.length : ℤ)) :
    (OMA.S_oeis_a048200.a n : ℤ) = v := by
  unfold OMA.S_oeis_a048200.a
  let S := {k : ℕ | ∃ w : List Bool, w.length = k ∧
    OMA.S_oeis_a048200.run w (List.range n) = (List.range n).reverse}
  change ((sInf S : ℕ) : ℤ) = v
  obtain ⟨w, hw, lw⟩ := hi
  have mw : w.length ∈ S := ⟨w,rfl,hw⟩
  have best := Nat.sInf_mem (show S.Nonempty from ⟨w.length,mw⟩)
  obtain ⟨u, hu, run⟩ := best
  have up : ((sInf S : ℕ) : ℤ) ≤ w.length := by exact_mod_cast Nat.sInf_le mw
  have low := lo u run
  rw [hu] at low
  omega

end Reversal

open Reversal

theorem OMA.solution : type_of% @OMA.S_oeis_a048200.main := by
  intro n hn
  constructor
  · intro he
    obtain ⟨m,hm⟩ := he
    have eq : n = 2*m := by omega
    rw [eq] at hn ⊢
    have ge : 2 ≤ m := by omega
    have ans := exact_minimum (2*m) (3*(m : ℤ)^2-4*m)
      (play_reversal_even (List.range (2*m)) m ge List.length_range) (lower_even m ge)
    zify
    push_cast
    nlinarith only [ans]
  · intro ho
    obtain ⟨m,hm⟩ := ho
    have eq : n = 2*m+1 := by omega
    rw [eq] at hn ⊢
    have ge : 2 ≤ m := by omega
    have ans := exact_minimum (2*m+1) (3*(m : ℤ)^2-2*m+2)
      (play_reversal_odd (List.range (2*m+1)) m ge List.length_range) (lower_odd m ge)
    zify
    push_cast
    nlinarith only [ans]

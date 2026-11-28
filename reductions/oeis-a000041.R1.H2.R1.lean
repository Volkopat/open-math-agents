import OMAReductions.R_oeis_a000041_R1

/-!
# Divisibility and local growth of partition numbers
Credit: @witeg4. The nine seed weights and the interval-overlap method are
due to @EmadY in the parent reduction. A reproducible independent computation
on the problem board (note 134875) checks the finite construction to index 8192.
-/

namespace OMA.R_oeis_a000041_R1_H2_R1
open Finset

/-- An infinite divisibility antichain. Below the experimental cutoff each added
weight fits the accumulated total. Above it the requirement concerns only how
far apart successive indices are, independent of subset sums. -/
def H1 : Prop :=
  ∃ f : ℕ → ℕ, let w := fun i => OMA.S_oeis_a000041.a (f i) + 2
    StrictMono f ∧ (∀ i, 0 < f i) ∧ (∀ i j, i ≠ j → ¬ w i ∣ w j) ∧
    (∀ i < 9, w i = ([7,9,13,17,24,32,44,58,79] : List ℕ)[i]?.getD 0) ∧
    ∀ i, 8 ≤ i →
      if f i < 8191 then w (i+1) + 119 ≤ ∑ j ∈ range (i+1), w j
      else f (i+1) ≤ f i + Nat.sqrt (f i) / 2

/-- An analytic estimate on the ordinary partition function, independent
of divisibility or the choice of antichain. -/
def H2 : Prop :=
  ∀ k j : ℕ, 8191 ≤ k → k ≤ j → j ≤ k + Nat.sqrt k / 2 →
    OMA.S_oeis_a000041.a j + 2 ≤ 2 * (OMA.S_oeis_a000041.a k + 2)

theorem main : H1 → H2 → OMA.R_oeis_a000041_R1.H2 := by
  classical
  rintro ⟨f, hf, hp, hanti, hseed, hgap⟩ hlocal n hn
  let w := fun i => OMA.S_oeis_a000041.a (f i) + 2
  let seed := fun i : ℕ => ([7,9,13,17,24,32,44,58,79] : List ℕ)[i]?.getD 0
  have seed_sum (s : Finset ℕ) (hs : s ⊆ range 9) :
      ∑ i ∈ s, w i = ∑ i ∈ s, seed i :=
    Finset.sum_congr rfl fun i hi => hseed i (mem_range.mp (hs hi))
  have mass : ∑ i ∈ range 9, w i = 283 := (seed_sum _ Subset.rfl).trans (by decide +kernel)
  have room : ∀ i, 8 ≤ i → w i + 119 ≤ ∑ j ∈ range i, w j := by
    intro i hi
    induction i, hi using Nat.le_induction with
    | base =>
      rw [seed_sum _ (range_mono (by decide : 8 ≤ 9)),show w 8 = seed 8 from hseed _ (by decide)]
      decide +kernel
    | succ i hi ih =>
      have h := hgap i hi
      split at h
      · exact h
      · rename_i hbig
        have hb : w (i+1) ≤ 2 * w i := hlocal _ _ (by omega) (hf.monotone (Nat.le_succ i)) h
        rw [sum_range_succ]
        omega
  have base : ∀ d : Fin 164, ∃ s ∈ (range 9).powerset, ∑ i ∈ s, seed i = d.val + 60 := by
    decide +kernel
  have cover : ∀ k, 9 ≤ k → ∀ z, 60 ≤ z → z + 60 ≤ ∑ i ∈ range k, w i →
      ∃ s ⊆ range k, ∑ i ∈ s, w i = z := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      intro z ha hb
      rw [mass] at hb
      obtain ⟨s, hs, hz⟩ := base ⟨z-60,by omega⟩
      have hsub := mem_powerset.mp hs
      exact ⟨s,hsub,(seed_sum _ hsub).trans (hz.trans (by simp; omega))⟩
    | succ k hk ih =>
      intro z ha hb
      rw [sum_range_succ] at hb
      by_cases hold : z + 60 ≤ ∑ i ∈ range k, w i
      · obtain ⟨s,hs,hz⟩ := ih z ha hold
        exact ⟨s,hs.trans (range_mono (Nat.le_succ k)),hz⟩
      · have hr := room k (by omega)
        obtain ⟨s,hs,hz⟩ := ih (z-w k) (by omega) (by omega)
        have hnmem : k ∉ s := fun hm => (Nat.lt_irrefl k) (mem_range.mp (hs hm))
        refine ⟨insert k s,?_,?_⟩
        · rw [range_add_one]; exact insert_subset_insert k hs
        · rw [sum_insert hnmem,hz]; omega
  let k := n + 60
  have hm : k ≤ ∑ i ∈ range k, w i := by
    calc
      k = ∑ _i ∈ range k, 1 := by simp
      _ ≤ _ := sum_le_sum fun i _ => by dsimp [w]; omega
  obtain ⟨s,_,hs⟩ := cover k (by dsimp [k]; omega) n (by omega) hm
  let e := s.equivFin.symm
  refine ⟨s.card, fun i => w (e i), ?_, ?_, ?_⟩
  · intro i; exact ⟨f (e i),hp _,rfl⟩
  · intro i j hij; exact hanti _ _ (fun he => hij (e.injective (Subtype.ext he)))
  · calc
      ∑ i, w (e i) = ∑ j : s, w j := Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = ∑ j ∈ s, w j := Finset.sum_coe_sort s w
      _ = n := hs

end OMA.R_oeis_a000041_R1_H2_R1

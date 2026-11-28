import FormalConjectures.ErdosProblems.«883»
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-! Window bounds for triangles and pentagons at the sharp coprime-graph threshold. -/

-- Credit: @MrSeizy

open Finset SimpleGraph Erdos883
namespace OMA.R_Erdos883_erdos_883_parts_i_R1

-- The cyclic-order to cycleGraph construction also occurs in t1125-883's
-- Open Proof Network reduction for Erdős 883 (25 November 2026, CC BY 4.0).
-- Adapted to forward cyclic steps: https://openproofnetwork.org/nodes/erdos-883/erdos-883--h1/
private theorem order_cycle {l : ℕ} {A : Finset ℕ} (hl : 2 < l) (ho : Odd l)
    (f : Fin l → ℕ) (hf : ∀ i, f i ∈ A) (hinj : Function.Injective f)
    (hstep : ∀ i j : Fin l, (i.val+1)%l = j.val → (f i).Coprime (f j)) :
    l ∈ (coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  let g : cycleGraph l →g coprimeGraph.induce (A : Set ℕ) :=
    { toFun := fun i => ⟨f i, hf i⟩
      map_rel' := by
        intro i j h
        change coprimeGraph.Adj (f i) (f j)
        rw [coprimeGraph, fromRel_adj]
        refine ⟨fun e => h.ne (hinj e), ?_⟩
        rcases cycleGraph_adj'.mp h with hh | hh
        · right
          apply hstep
          have hz : NeZero l := ⟨by omega⟩
          have h1 : (1 : Fin l).val = 1 := by change 1 % l = 1; exact Nat.mod_eq_of_lt (by omega)
          have eq1 : _ - _ = (1 : Fin l) := Fin.ext (hh.trans h1.symm)
          have eq2 := congrArg Fin.val (sub_eq_iff_eq_add.mp eq1)
          simpa [Fin.val_add, h1, Nat.add_comm] using eq2.symm
        · left
          apply hstep
          have hz : NeZero l := ⟨by omega⟩
          have h1 : (1 : Fin l).val = 1 := by change 1 % l = 1; exact Nat.mod_eq_of_lt (by omega)
          have eq1 : _ - _ = (1 : Fin l) := Fin.ext (hh.trans h1.symm)
          have eq2 := congrArg Fin.val (sub_eq_iff_eq_add.mp eq1)
          simpa [Fin.val_add, h1, Nat.add_comm] using eq2.symm }
  exact ⟨(cycleGraph_isContained_iff hl).mp ⟨⟨g, fun _ _ h => hinj (congrArg Subtype.val h)⟩⟩, ho⟩


set_option maxHeartbeats 5000000 in
/-- Every admissible length three or five occurs at the strict density threshold. -/
theorem short_cycles {n l : ℕ} {A : Finset ℕ} (hA : A ⊆ Icc 1 n)
    (hd : n/2+n/3-n/6 < A.card) (hlen : l = 3 ∨ l = 5) (hupper : l ≤ n/3+1) :
    l ∈ (coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  -- A period of zero denotes an unshifted numerical interval.
  let edge (p r i j : ℕ) : Bool :=
    decide ((max i j - min i j) ∣ p^4 ∧ (r+i).Coprime (r+j))

  have edge_sound {p r i j t : ℕ} (h : edge p r i j) :
      (r + p*t + i).Coprime (r + p*t + j) := by
    obtain ⟨hd, hc⟩ := of_decide_eq_true h
    by_contra hn
    obtain ⟨q, hq, hi, hj⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
    have hdif : q ∣ max i j - min i j := by
      rcases le_total i j with hij | hji
      · rw [max_eq_right hij, min_eq_left hij]
        simpa [Nat.add_sub_add_left] using Nat.dvd_sub hj hi
      · rw [max_eq_left hji, min_eq_right hji]
        simpa [Nat.add_sub_add_left] using Nat.dvd_sub hi hj
    have hqp : q ∣ p := hq.dvd_of_dvd_pow (hdif.trans hd)
    have ht := dvd_mul_of_dvd_left hqp t
    apply (Nat.Prime.not_coprime_iff_dvd.mpr ?_) hc
    exact ⟨q, hq, (Nat.dvd_add_iff_left ht).mpr (by simpa [Nat.add_right_comm] using hi),
      (Nat.dvd_add_iff_left ht).mpr (by simpa [Nat.add_right_comm] using hj)⟩

  -- Each list gives the offsets in cyclic order, with no repeated closing vertex.
  let valid (p r l : ℕ) (row : List ℕ) : Bool :=
    decide (row.length = l) && decide row.Nodup &&
    (List.range l).all fun i => edge p r row[i]! row[(i+1)%l]!

  let Has (A : Finset ℕ) (l : ℕ) : Prop :=
    l ∈ (coprimeGraph.induce (A : Set ℕ)).oddCycleLengths

  have valid_sound {p r t l : ℕ} {row : List ℕ} {A : Finset ℕ}
      (hl : 2 < l) (ho : Odd l) (hc : valid p r l row)
      (hm : ∀ i ∈ row, r+p*t+i ∈ A) : Has A l := by
    simp only [valid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_range] at hc
    obtain ⟨⟨hlen,hnd⟩,he⟩ := hc
    let f (i : Fin l) := r+p*t+row[i.val]!
    have hv (i : Fin l) : i.val < row.length := hlen ▸ i.isLt
    have hfi (i : Fin l) : row[i.val]! = row[i.val]'(hv i) := by simp [List.getElem?_eq_getElem (hv i)]
    have hf (i : Fin l) : f i ∈ A := hm _ (hfi i ▸ List.getElem_mem (hv i))
    have hinj : Function.Injective f := by
      intro i j hij
      have hh : row[i.val]! = row[j.val]! := Nat.add_left_cancel hij
      rw [hfi i, hfi j] at hh
      exact Fin.ext (List.Nodup.getElem_inj_iff hnd |>.mp hh)
    have hstep (i j : Fin l) (h : (i.val+1)%l = j.val) : (f i).Coprime (f j) := by
      have h' := he i.val i.isLt
      rw [h] at h'
      exact edge_sound h'
    exact order_cycle hl ho f hf hinj hstep

  -- A hitting set must meet the first row. In each branch, remove one
  -- of its elements and continue with the rows disjoint from that element.
  let covers (w k : ℕ) : List (List ℕ) → Bool :=
    Nat.rec (motive := fun _ => List (List ℕ) → Bool) (fun rows => !rows.isEmpty)
      (fun _ prev rows => match rows with
        | [] => false
        | row :: rest => (row.filter (· < w)).all fun x => prev (rest.filter fun a => !a.contains x)) k

  have covers_sound {w k : ℕ} {rows : List (List ℕ)} (h : covers w k rows)
      {D : Finset ℕ} (hD : D.card ≤ k) :
      ∃ row ∈ rows, ∀ x ∈ row, x < w → x ∉ D := by
    induction k generalizing rows D with
    | zero =>
      have h0 : D = ∅ := card_eq_zero.mp (by omega)
      cases rows with
      | nil => contradiction
      | cons a as => exact ⟨a, by simp, by simp [h0]⟩
    | succ k ih =>
      cases rows with
      | nil => contradiction
      | cons a as =>
        by_cases ha : ∀ x ∈ a, x < w → x ∉ D
        · exact ⟨a, by simp, ha⟩
        push Not at ha
        obtain ⟨x,hx,hw,hd⟩ := ha
        have h' := List.all_eq_true.mp h x (List.mem_filter.mpr ⟨hx, by simpa⟩)
        have hk : (D.erase x).card ≤ k := by rw [card_erase_of_mem hd]; omega
        obtain ⟨b, hb, hfree⟩ := ih h' hk
        obtain ⟨hb, hnx⟩ := List.mem_filter.mp hb
        refine ⟨b, by simp [hb], ?_⟩
        intro y hy hyw hyd
        have hne : y ≠ x := by
          rintro rfl
          exact (show y ∉ b by simpa using hnx) hy
        exact hfree y hy hyw (mem_erase.mpr ⟨hne,hyd⟩)

  let block (s w : ℕ) := Ico s (s+w)

  have apply_cover {p r t w k l : ℕ} {A : Finset ℕ} {rows : List (List ℕ)}
      (ho : Odd l) (hl : 2 < l) (hc : covers w k rows)
      (hv : rows.all (valid p r l))
      (extra : ∀ row ∈ rows, ∀ x ∈ row, w ≤ x → r+p*t+x ∈ A)
      (hd : ((block (r+p*t) w) \ A).card ≤ k) : Has A l := by
    let D := (range w).filter fun i => r+p*t+i ∉ A
    have hD : D.card ≤ k := by
      refine le_trans (card_le_card_of_injOn (fun i => r+p*t+i) (t := block (r+p*t) w \ A) ?_ ?_) hd
      · intro i hi
        obtain ⟨hi,hm⟩ := mem_filter.mp hi
        exact mem_sdiff.mpr ⟨mem_Ico.mpr ⟨Nat.le_add_right _ _, Nat.add_lt_add_left (mem_range.mp hi) _⟩, hm⟩
      · intro i _ j _ he
        exact Nat.add_left_cancel he
    obtain ⟨row, hr, hs⟩ := covers_sound hc hD
    apply valid_sound hl ho (List.all_eq_true.mp hv row hr) (t := t)
    intro x hx
    by_cases h : x < w
    · by_contra hn
      exact hs x hx h (mem_filter.mpr ⟨mem_range.mpr h, hn⟩)
    · exact extra row hr x hx (by omega)

  let pop (A : Finset ℕ) (s w : ℕ) := ((block s w) ∩ A).card

  have pop_add (A : Finset ℕ) (s w v : ℕ) :
      pop A s (w+v) = pop A s w + pop A (s+w) v := by
    unfold pop
    rw [← card_union_of_disjoint]
    · congr 1
      ext x
      by_cases h : x ∈ A
      · simp [block, h]; omega
      · simp [block, h]
    · rw [Finset.disjoint_left]
      intro x hx hy
      have h1 := (mem_Ico.mp (mem_inter.mp hx).1).2
      have h2 := (mem_Ico.mp (mem_inter.mp hy).1).1
      omega

  have pop_one (A : Finset ℕ) (s : ℕ) : pop A s 1 ≤ 1 := by
    exact (card_le_card inter_subset_left).trans (by simp [block])

  let cert (p r w k l e : ℕ) (rows : List (List ℕ)) : Bool :=
    covers w k rows && rows.all (valid p r l) &&
    rows.all fun row => row.all fun x => decide (x < w ∨ x = e)

  have cert_bound {p s w k l e : ℕ} {rows : List (List ℕ)} {A : Finset ℕ}
      (hc : cert p (s%p) w k l e rows) (hl : 2 < l) (ho : Odd l)
      (he : w ≤ e → s+e ∈ A) (hn : ¬ Has A l) :
      pop A s w ≤ w - (k+1) := by
    simp only [cert, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hh,hv⟩,hx⟩ := hc
    by_contra! h
    have hcard := card_sdiff_add_card_inter (block s w) A
    change (block s w \ A).card + pop A s w = _ at hcard
    rw [show (block s w).card = w by simp [block]] at hcard
    have hs := Nat.mod_add_div s p
    apply hn
    apply apply_cover (t := s/p) ho hl hh (List.all_eq_true.mpr hv)
    · intro row hr x hm hw
      rw [hs]
      have hh' := hx row hr x hm
      obtain rfl : x = e := by omega
      exact he hw
    · rw [hs]
      omega

  -- Cyclic witnesses for the twelve-point windows. The shift has period 30,
  -- except for the class 14 modulo 30, where prime 7 is also needed.
  let deck : ℕ → ℕ → List (List ℕ)
    | 30, 0 => [[1,4,3,2,5], [6,7,9,8,11], [1,2,7,10,9], [1,3,8,11,10], [4,5,11,10,7],
        [3,5,4,9,8], [1,6,5,2,11], [1,4,3,7,6], [2,3,7,6,5], [1,6,5,9,10],
        [2,3,4,9,11], [2,5,9,8,11], [1,4,7,2,5], [1,2,3,4,9], [1,6,11,2,7],
        [1,2,11,8,9], [2,5,4,3,11], [2,7,4,3,11], [2,3,4,9,7], [2,5,9,4,7]]
    | 30, 6 => [[0,1,3,2,5], [6,7,9,8,11], [1,4,3,7,10], [2,5,10,9,11], [1,4,5,11,6],
        [4,5,9,8,7], [1,3,8,9,10], [2,3,11,6,7], [0,1,10,7,5], [2,3,8,9,7],
        [3,4,5,6,11], [1,2,11,10,9], [2,5,4,3,7], [1,2,11,8,3], [0,1,9,8,5],
        [1,6,11,2,7], [1,2,7,8,9], [2,3,8,9,5], [2,3,8,9,11], [2,7,4,5,11]]
    | 30, 12 => [[0,1,3,2,5], [4,7,6,11,9], [1,7,8,5,10], [2,3,11,8,7], [1,3,4,9,10],
        [2,5,10,9,11], [0,1,11,6,5], [3,4,9,8,5], [1,3,2,11,6], [1,2,7,8,9],
        [5,6,7,10,9], [1,6,11,8,7], [3,4,7,6,5], [0,1,9,4,5], [1,4,3,2,7],
        [1,2,11,8,9], [2,5,4,3,11], [2,3,4,9,7], [2,3,4,9,11], [2,7,4,5,11]]
    | 30, 18 => [[0,1,3,2,5], [4,7,6,11,9], [1,3,8,7,10], [2,5,9,8,11], [1,9,4,5,10],
        [5,10,7,6,11], [1,3,8,11,6], [3,7,4,9,8], [1,2,11,10,7], [3,4,9,10,11],
        [0,1,7,6,5], [2,3,7,4,5], [1,2,3,4,9], [2,3,7,6,11], [2,3,8,9,5],
        [0,1,11,2,5], [1,2,11,8,9], [1,4,9,8,7], [2,5,4,3,11], [4,7,6,5,9]]
    | 30, 24 => [[0,1,3,2,5], [4,7,11,8,9], [1,7,6,5,10], [2,3,11,10,7], [1,3,4,9,10],
        [2,5,9,8,11], [3,4,7,6,5], [0,1,10,11,5], [1,2,7,9,4], [1,2,11,8,3],
        [3,7,10,9,8], [0,1,9,8,5], [1,2,11,8,7], [3,4,5,10,11], [1,4,3,7,10],
        [2,7,4,5,11], [1,2,11,8,9], [2,3,4,9,5], [2,3,4,9,11], [2,5,9,4,7]]
    | 30, 2 => [[0,3,2,1,5], [6,9,8,7,11], [3,4,9,10,5], [0,1,11,10,9], [1,5,8,7,6],
        [2,7,6,3,11], [2,3,9,8,7], [2,5,4,9,11], [3,4,5,8,11], [0,1,6,7,3],
        [2,3,9,6,11], [0,1,2,7,5], [0,1,11,2,3], [0,3,2,1,9], [0,5,2,1,9],
        [0,1,2,7,9], [0,1,11,2,5], [0,3,7,2,5], [0,5,2,7,9], [1,6,7,2,11],
        [2,7,6,5,11]]
    | 30, 8 => [[0,3,2,1,5], [6,9,8,7,11], [3,4,9,10,5], [0,1,11,10,9], [1,3,8,7,6],
        [2,5,7,6,11], [2,3,9,8,11], [0,1,9,4,5], [3,4,5,10,11], [0,3,7,6,9],
        [5,8,7,9,10], [0,1,11,2,3], [0,1,11,8,5], [1,2,3,4,9], [2,5,4,9,11],
        [0,1,6,7,5], [0,1,6,7,9], [0,3,7,6,5], [1,2,11,7,6], [2,3,7,6,11]]
    | 210, 14 => [[0,3,2,1,5], [4,9,6,7,11], [1,8,3,10,9], [2,7,8,5,11], [0,5,11,10,9],
        [3,4,5,7,6], [0,1,8,11,3], [0,1,2,7,9], [1,2,11,4,5], [2,9,6,3,11],
        [5,8,7,9,10], [2,7,3,4,11], [0,1,8,7,5], [0,5,2,1,9], [0,1,2,7,3],
        [0,1,2,11,9], [0,5,3,2,9], [0,3,7,2,9], [0,3,11,2,5], [1,2,11,7,8]]
    | 210, 44 => [[0,3,2,1,5], [4,9,6,7,11], [1,8,3,10,9], [0,5,11,8,7], [2,7,3,10,11],
        [3,6,5,4,9], [1,8,7,2,9], [0,1,9,10,5], [1,3,4,11,8], [0,5,10,3,7],
        [1,2,11,4,5], [0,3,11,2,9], [1,2,7,6,3], [0,5,1,2,7], [0,1,2,11,7],
        [0,1,2,11,9], [0,7,3,2,9], [0,3,11,2,5], [0,7,5,2,9], [0,5,11,2,9]]
    | 210, 74 => [[0,3,2,1,5], [4,9,6,7,11], [1,8,5,10,9], [0,3,11,8,7], [2,3,11,10,9],
        [3,4,5,7,6], [1,5,2,11,8], [0,7,2,1,9], [0,5,11,4,9], [0,1,9,6,3],
        [0,7,5,2,9], [1,2,7,6,3], [0,1,5,6,7], [0,1,8,11,3], [0,1,2,11,7],
        [0,1,2,11,9], [0,5,3,2,9], [0,7,3,2,9], [0,3,11,2,5], [0,5,11,2,7]]
    | 210, 104 => [[0,3,2,1,5], [4,9,6,7,11], [3,9,8,5,10], [0,1,9,8,7], [2,7,3,10,11],
        [1,2,11,4,5], [0,3,11,4,5], [2,7,6,5,9], [0,1,3,6,7], [0,1,2,11,9],
        [5,8,7,11,10], [1,2,9,4,3], [0,1,9,4,5], [0,3,11,4,9], [1,2,7,6,5],
        [0,1,2,11,3], [0,1,2,11,7], [0,5,3,2,7], [0,7,3,2,9], [0,5,11,2,9]]
    | 210, 134 => [[0,3,2,1,5], [4,9,6,7,11], [1,8,3,10,9], [0,5,11,8,7], [2,7,3,10,11],
        [3,6,5,4,9], [1,8,7,2,9], [0,1,9,10,5], [1,3,4,11,8], [0,5,10,3,7],
        [1,2,11,4,5], [0,3,11,2,9], [1,2,7,6,3], [0,5,1,2,7], [0,1,2,11,7],
        [0,1,2,11,9], [0,7,3,2,9], [0,3,11,2,5], [0,7,5,2,9], [0,5,11,2,9]]
    | 210, 164 => [[0,3,2,1,5], [6,7,11,8,9], [3,9,4,5,10], [1,2,11,10,9], [0,3,10,11,7],
        [1,5,6,7,8], [0,7,5,4,9], [1,2,9,4,3], [3,6,5,11,8], [1,3,2,7,8],
        [0,1,2,11,5], [0,7,6,3,9], [0,1,9,4,5], [0,1,8,11,3], [2,5,4,3,7],
        [0,7,2,1,9], [0,1,2,11,7], [0,3,11,2,9], [0,5,11,2,7], [0,5,11,2,9]]
    | 210, 194 => [[0,3,2,1,5], [4,9,6,7,11], [1,8,3,10,9], [0,5,11,8,7], [2,7,3,10,11],
        [3,6,5,4,9], [1,2,7,9,8], [0,1,9,10,5], [1,3,4,11,8], [0,5,10,3,7],
        [1,2,11,4,5], [0,3,2,11,9], [1,2,7,6,3], [0,5,1,2,7], [0,1,2,11,7],
        [0,1,2,11,9], [0,7,2,3,9], [0,3,11,2,5], [0,7,2,5,9], [0,5,2,11,9]]
    | 30, 20 => [[0,3,2,1,9], [5,8,7,6,11], [3,4,9,10,11], [1,5,4,3,6], [1,2,7,8,11],
        [2,5,4,9,7], [0,1,11,10,9], [0,3,8,7,9], [2,5,6,3,11], [1,6,5,8,9],
        [0,1,2,7,3], [0,1,11,8,3], [1,6,5,2,11], [1,2,7,9,6], [2,5,4,3,7],
        [0,3,2,5,9], [1,5,2,7,6], [2,7,6,3,11], [2,5,4,9,11], [2,7,9,6,11]]
    | 30, 26 => [[0,3,2,1,5], [6,9,8,7,11], [3,4,5,10,9], [0,1,11,10,9], [1,3,8,7,6],
        [2,7,5,10,11], [2,3,9,6,11], [0,1,2,7,9], [3,4,5,11,8], [0,1,6,7,5],
        [2,3,9,8,7], [1,2,5,9,6], [0,1,11,2,3], [0,3,2,1,9], [0,1,11,2,5],
        [0,3,7,2,5], [0,5,2,7,9], [0,5,2,11,9], [1,6,7,2,11], [2,7,6,3,11]]
    | _, _ => []

  have twelve {A : Finset ℕ} {s : ℕ} (hs : s%6 = 0 ∨ s%6 = 2)
      (hn : ¬ Has A 5) : pop A s 12 ≤ 8 := by
    by_cases hbad : s%30 = 14
    ·
      apply cert_bound (p := 210) (e := 0) (k := 3) (rows := deck 210 (s%210)) (l := 5) (by
        have h : s%210 = 14 ∨ s%210 = 44 ∨ s%210 = 74 ∨ s%210 = 104 ∨ s%210 = 134 ∨ s%210 = 164 ∨ s%210 = 194 := by omega
        rcases h with h | h | h | h | h | h | h
        all_goals rw [h]
        all_goals decide +kernel) (by decide) (by decide) (by omega) hn
    ·
      apply cert_bound (p := 30) (e := 0) (k := 3) (rows := deck 30 (s%30)) (l := 5) (by
        have h : s%30 = 0 ∨ s%30 = 2 ∨ s%30 = 6 ∨ s%30 = 8 ∨ s%30 = 12 ∨ s%30 = 18 ∨ s%30 = 20 ∨ s%30 = 24 ∨ s%30 = 26 := by omega
        rcases h with h | h | h | h | h | h | h | h | h
        all_goals rw [h]
        all_goals decide +kernel) (by decide) (by decide) (by omega) hn
  have triBase6 {A : Finset ℕ} (hn : ¬ Has A 3) :
      pop A 1 6 ≤ 4 :=
    cert_bound (p := 0) (e := 0) (k := 1)
      (rows := [[0,1,2], [0,3,4], [1,2,4]])
      (by decide +kernel) (by decide) (by decide) (by omega) hn

  have triBase7 {A : Finset ℕ} (hn : ¬ Has A 3) :
      pop A 1 7 ≤ 4 :=
    cert_bound (p := 0) (e := 0) (k := 2)
      (rows := [[0,1,2], [3,4,6], [0,4,5], [0,3,6], [1,2,4], [1,2,6]])
      (by decide +kernel) (by decide) (by decide) (by omega) hn

  have triBase11 {A : Finset ℕ} (hn : ¬ Has A 3) :
      pop A 1 11 ≤ 7 :=
    cert_bound (p := 0) (e := 0) (k := 3)
      (rows := [[0,1,2], [3,4,6], [7,8,10], [0,4,5], [2,6,9], [0,1,6], [1,2,4]])
      (by decide +kernel) (by decide) (by decide) (by omega) hn

  have pentBase12 {A : Finset ℕ} (hn : ¬ Has A 5) :
      pop A 1 12 ≤ 8 :=
    cert_bound (p := 0) (e := 0) (k := 3)
      (rows := [[0,3,2,1,4], [5,6,8,7,10], [0,9,2,6,11], [1,4,10,9,8], [0,8,3,10,11],
          [0,6,5,4,7], [2,6,3,8,9], [2,7,4,11,10], [1,2,6,5,4], [0,8,7,2,9],
          [0,3,10,1,6], [0,3,8,1,6], [0,3,2,1,10], [0,3,8,1,4], [0,3,10,1,4],
          [1,4,2,3,8], [1,6,3,2,10], [1,8,3,2,10], [1,6,4,3,8], [1,6,4,3,10]])
      (by decide +kernel) (by decide) (by decide) (by omega) hn

  have path13at1 {A : Finset ℕ} (hp : 13 ∈ A) (hn : ¬ Has A 5) :
      pop A 1 12 ≤ 7 :=
    cert_bound (p := 0) (e := 12) (k := 4)
      (rows := [[0,1,2,3,12], [4,5,6,7,12], [8,9,10,11,12], [0,1,4,8,12], [2,3,4,8,12],
          [0,5,6,9,12], [2,7,10,11,12], [1,6,3,10,12], [4,7,0,9,12], [2,7,8,9,12],
          [0,5,10,11,12], [1,2,6,5,12], [0,3,8,7,12], [3,4,2,9,12], [1,4,3,8,12],
          [1,4,10,9,12], [1,6,3,8,12]])
      (by decide +kernel) (by decide) (by decide) (fun _ => hp) hn

  have path17at1 {A : Finset ℕ} (hp : 17 ∈ A) (hn : ¬ Has A 5) :
      pop A 1 12 ≤ 7 :=
    cert_bound (p := 0) (e := 16) (k := 4)
      (rows := [[0,1,2,3,16], [4,5,6,7,16], [8,9,10,11,16], [0,1,4,8,16], [2,3,4,8,16],
          [0,5,6,9,16], [2,7,10,11,16], [1,6,3,10,16], [4,7,0,9,16], [2,7,8,9,16],
          [0,5,10,11,16], [1,2,6,5,16], [0,3,8,7,16], [3,4,2,9,16], [1,4,3,8,16],
          [1,4,10,9,16], [1,6,3,8,16]])
      (by decide +kernel) (by decide) (by decide) (fun _ => hp) hn

  have path17at13 {A : Finset ℕ} (hp : 17 ∈ A) (hn : ¬ Has A 5) :
      pop A 13 4 ≤ 3 :=
    cert_bound (p := 0) (e := 4) (k := 0)
      (rows := [[0,1,2,3,4]])
      (by decide +kernel) (by decide) (by decide) (fun _ => hp) hn

  have path19at1 {A : Finset ℕ} (hp : 19 ∈ A) (hn : ¬ Has A 5) :
      pop A 1 12 ≤ 7 :=
    cert_bound (p := 0) (e := 18) (k := 4)
      (rows := [[0,1,2,3,18], [4,5,6,7,18], [8,9,10,11,18], [0,1,4,8,18], [2,3,4,8,18],
          [0,5,6,9,18], [2,7,10,11,18], [1,6,3,10,18], [4,7,0,9,18], [2,7,8,9,18],
          [0,5,10,11,18], [1,2,6,5,18], [0,3,8,7,18], [3,4,2,9,18], [1,4,3,8,18],
          [1,4,10,9,18], [1,6,3,8,18]])
      (by decide +kernel) (by decide) (by decide) (fun _ => hp) hn

  have path19at13 {A : Finset ℕ} (hp : 19 ∈ A) (hn : ¬ Has A 5) :
      pop A 13 6 ≤ 4 :=
    cert_bound (p := 0) (e := 6) (k := 1)
      (rows := [[0,1,2,3,6], [0,1,4,5,6], [2,3,4,5,6]])
      (by decide +kernel) (by decide) (by decide) (fun _ => hp) hn

  have path23at1 {A : Finset ℕ} (hp : 23 ∈ A) (hn : ¬ Has A 5) :
      pop A 1 12 ≤ 7 :=
    cert_bound (p := 0) (e := 22) (k := 4)
      (rows := [[0,1,2,3,22], [4,5,6,7,22], [8,9,10,11,22], [0,1,4,8,22], [2,3,4,8,22],
          [0,5,6,9,22], [2,7,10,11,22], [1,6,3,10,22], [4,7,0,9,22], [2,7,8,9,22],
          [0,5,10,11,22], [1,2,6,5,22], [0,3,8,7,22], [3,4,2,9,22], [1,4,3,8,22],
          [1,4,10,9,22], [1,6,3,8,22]])
      (by decide +kernel) (by decide) (by decide) (fun _ => hp) hn

  have path23at13 {A : Finset ℕ} (hp : 23 ∈ A) (hn : ¬ Has A 5) :
      pop A 13 6 ≤ 4 :=
    cert_bound (p := 0) (e := 10) (k := 1)
      (rows := [[0,1,2,3,10], [0,1,4,5,10], [2,3,4,5,10]])
      (by decide +kernel) (by decide) (by decide) (fun _ => hp) hn

  have path23at19 {A : Finset ℕ} (hp : 23 ∈ A) (hn : ¬ Has A 5) :
      pop A 19 4 ≤ 3 :=
    cert_bound (p := 0) (e := 4) (k := 0)
      (rows := [[0,1,2,3,4]])
      (by decide +kernel) (by decide) (by decide) (fun _ => hp) hn

  have six {A : Finset ℕ} {s : ℕ} (hs : s%6 = 0 ∨ s%6 = 2)
      (hn : ¬ Has A 3) : pop A s 6 ≤ 4 := by
    rcases hs with h | h
    · exact cert_bound (p := 6) (k := 1) (e := 0) (rows := [[1,2,3], [1,4,5], [2,3,5]])
        (by rw [h]; decide +kernel) (by decide) (by decide) (by omega) hn
    · exact cert_bound (p := 6) (k := 1) (e := 0) (rows := [[0,1,3], [1,2,5], [2,3,5]])
        (by rw [h]; decide +kernel) (by decide) (by decide) (by omega) hn

  let threshold (n : ℕ) := n/2 + n/3 - n/6

  have one_absent {A : Finset ℕ} {s : ℕ} (h : s ∉ A) : pop A s 1 = 0 := by
    simp [pop, block, Nat.Ico_succ_singleton, singleton_inter_of_notMem h]

  have propagate {A : Finset ℕ} {b : ℕ} (hb : b = 6 ∨ b = 12)
      (hstart : pop A 1 b ≤ threshold b)
      (hsmall : ∀ n, b < n → n < 2*b → (n%6 = 1 ∨ n%6 = 5) →
        pop A 1 (n-1) ≤ threshold (n-1) → pop A 1 n ≤ threshold n)
      (hwin : ∀ s, s%6 = 0 ∨ s%6 = 2 → pop A s b ≤ b/3*2) :
      ∀ n, b ≤ n → pop A 1 n ≤ threshold n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hbn
      obtain rfl | hn := eq_or_lt_of_le hbn
      · exact hstart
      have hprev := ih (n-1) (by omega) (by omega)
      by_cases hr : n%6 = 1 ∨ n%6 = 5
      · by_cases hsmallN : n < 2*b
        · exact hsmall n hn hsmallN hr hprev
        have hleft := ih (n-b) (by rcases hb with rfl | rfl <;> omega) (by omega)
        have hright := hwin (1+(n-b)) (by rcases hb with rfl | rfl <;> omega)
        have hsplit := pop_add A 1 (n-b) b
        rw [Nat.sub_add_cancel hbn] at hsplit
        unfold threshold at *
        rcases hb with rfl | rfl <;> omega
      · have hsplit := pop_add A 1 (n-1) 1
        have hright := pop_one A (1+(n-1))
        rw [Nat.sub_add_cancel (by omega)] at hsplit
        unfold threshold at *
        have hr' : n%6 = 0 ∨ n%6 = 2 ∨ n%6 = 3 ∨ n%6 = 4 := by omega
        rcases hr' with h | h | h | h <;> omega

  have triangle_bound {A : Finset ℕ} (hn : ¬ Has A 3) :
      ∀ n, 6 ≤ n → pop A 1 n ≤ threshold n := by
    apply propagate (Or.inl rfl) (triBase6 hn) _ (fun _ h => six h hn)
    intro n h1 h2 hr _
    have hh : n=7 ∨ n=11 := by omega
    rcases hh with rfl | rfl
    · exact triBase7 hn
    · exact triBase11 hn

  have pentagon_bound {A : Finset ℕ} (hn : ¬ Has A 5) :
      ∀ n, 12 ≤ n → pop A 1 n ≤ threshold n := by
    apply propagate (Or.inr rfl) (pentBase12 hn) _ (fun _ h => twelve h hn)
    intro n h1 h2 hr hprev
    by_cases hp : n ∈ A
    · have hlast := pop_one A n
      have hh : n=13 ∨ n=17 ∨ n=19 ∨ n=23 := by omega
      rcases hh with rfl | rfl | rfl | rfl
      · rw [show 13 = 12+1 by rfl, pop_add]
        exact Nat.add_le_add (path13at1 hp hn) hlast
      · rw [show 17 = (12+4)+1 by rfl, pop_add, pop_add]
        exact Nat.add_le_add (Nat.add_le_add (path17at1 hp hn) (path17at13 hp hn)) hlast
      · rw [show 19 = (12+6)+1 by rfl, pop_add, pop_add]
        exact Nat.add_le_add (Nat.add_le_add (path19at1 hp hn) (path19at13 hp hn)) hlast
      · rw [show 23 = ((12+6)+4)+1 by rfl, pop_add, pop_add, pop_add]
        exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (path23at1 hp hn)
          (path23at13 hp hn)) (path23at19 hp hn)) hlast
    · have hsplit := pop_add A 1 (n-1) 1
      rw [show n-1+1=n by omega, show 1+(n-1)=n by omega, one_absent hp] at hsplit
      unfold threshold at *
      rcases hr with hr | hr <;> omega

  have pop_full {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Icc 1 n) :
      pop A 1 n = A.card := by
    have hsub : A ⊆ block 1 n := by
      intro a ha
      have := mem_Icc.mp (hA ha)
      exact mem_Ico.mpr ⟨by omega, by omega⟩
    simp [pop, inter_eq_right.mpr hsub]
  rcases hlen with rfl | rfl
  · by_contra hn
    have h := triangle_bound hn n (by omega)
    rw [pop_full hA] at h
    exact hd.not_ge h
  · by_contra hn
    have h := pentagon_bound hn n (by omega)
    rw [pop_full hA] at h
    exact hd.not_ge h

set_option maxHeartbeats 800000 in
/-- The odd multiples of three, the indicated even connectors, and 2 suffice at every length. -/
theorem core_cycle {n k : ℕ} {A : Finset ℕ} (hA : A ⊆ Icc 1 n)
    (hd : n/2+n/3-n/6 < A.card) (hk : 0 < k)
    (h2 : 2 ∈ A) (h3 : ∀ i < k, 6*i+3 ∈ A)
    (hb : ∀ i, i+1 < k → (if (6*i+4)%5 = 0 then 6*i+8 else 6*i+4) ∈ A) :
    2*k+1 ∈ (coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  let Has (A : Finset ℕ) (l : ℕ) : Prop :=
    l ∈ (coprimeGraph.induce (A : Set ℕ)).oddCycleLengths


  -- An alternating path on the odd multiples of three. Of the two possible
  -- even connectors in each gap, one avoids the only possible obstruction, 5.
  let connector (i : ℕ) := if (6*i+4)%5 = 0 then 6*i+8 else 6*i+4

  have five_gap (a : ℕ) (ha : a%5 ≠ 0) : a.Coprime (a+5) := by
    apply (Nat.coprime_sub_self_right (Nat.le_add_right a 5)).mp
    rw [Nat.add_sub_cancel_left]
    exact (Nat.prime_five.coprime_iff_not_dvd.mpr (fun h => ha (Nat.mod_eq_zero_of_dvd h))).symm

  have connector_edges (i : ℕ) :
      (6*i+3).Coprime (connector i) ∧ (connector i).Coprime (6*(i+1)+3) := by
    unfold connector
    split_ifs with h
    · exact ⟨five_gap _ (by omega), by
        rw [show 6*(i+1)+3 = (6*i+8)+1 by omega]
        exact Nat.coprime_self_add_right.mpr (by simp)⟩
    · exact ⟨by change (6*i+3).Coprime ((6*i+3)+1); simp,
        by convert five_gap (6*i+4) h using 1; omega⟩

  have connector_bounds (i : ℕ) :
      6*i+4 ≤ connector i ∧ connector i ≤ 6*i+8 ∧ connector i % 2 = 0 := by
    unfold connector
    split <;> omega

  let ringVertex (k x i : ℕ) :=
    if i = 0 then x else if i = 2*k then 2 else
    if i%2 = 1 then 6*(i/2)+3 else connector (i/2-1)

  have ring_inj {k x : ℕ} (hx : x%2=1) (hx3 : x%3 ≠ 0) :
      Function.Injective (fun i : Fin (2*k+1) => ringVertex k x i.val) := by
    intro i j h
    change ringVertex k x i.val = ringVertex k x j.val at h
    have h₁ := connector_bounds (i.val/2-1)
    have h₂ := connector_bounds (j.val/2-1)
    have hi := i.isLt
    have hj := j.isLt
    apply Fin.ext
    unfold ringVertex at h
    split_ifs at h <;> omega

  have ring_step {k x : ℕ} (hk : 0 < k) (hx : x.Coprime 2) (hx3 : x.Coprime 3)
      (i : Fin (2*k+1)) :
      (ringVertex k x i.val).Coprime (ringVertex k x ((i.val+1)%(2*k+1))) := by
    have hi := i.isLt
    by_cases hlast : i.val=2*k
    · simp [ringVertex, hlast, show 2*k ≠ 0 by omega, Nat.coprime_two_right.mp hx]
    rw [Nat.mod_eq_of_lt (show i.val+1 < 2*k+1 by omega)]
    by_cases hzero : i.val=0
    · simpa [ringVertex, hzero, show 1 ≠ 2*k by omega] using hx3
    by_cases hpen : i.val+1=2*k
    · have hodd : i.val%2=1 := by omega
      simp only [ringVertex, if_neg hzero, if_neg hlast, if_pos hodd, hpen,
        if_neg (show 2*k ≠ 0 by omega), if_true]
      exact Nat.coprime_two_right.mpr (by exact ⟨3*(i.val/2)+1, by omega⟩)
    simp only [ringVertex, if_neg hzero, if_neg hlast, if_neg hpen,
      if_neg (Nat.succ_ne_zero _)]
    by_cases ho : i.val%2=1
    · simp only [if_pos ho, if_neg (show (i.val+1)%2 ≠ 1 by omega)]
      rw [show (i.val+1)/2-1=i.val/2 by omega]
      exact (connector_edges _).1
    · simp only [if_neg ho, if_pos (show (i.val+1)%2=1 by omega)]
      rw [show (i.val+1)/2=i.val/2-1+1 by omega]
      exact (connector_edges _).2

  let core (k : ℕ) (A : Finset ℕ) : Prop :=
    2 ∈ A ∧ (∀ i < k, 6*i+3 ∈ A) ∧ (∀ i, i+1 < k → connector i ∈ A)

  have ring_cycle {k x : ℕ} {A : Finset ℕ} (hk : 0 < k) (hc : core k A)
      (hxA : x ∈ A) (hx : x%2=1) (hx3 : x%3 ≠ 0) : Has A (2*k+1) := by
    have hx2c := Nat.prime_two.coprime_iff_not_dvd.mpr
      (show ¬ 2 ∣ x from fun h => by have := Nat.mod_eq_zero_of_dvd h; omega)
    have hx3c := Nat.prime_three.coprime_iff_not_dvd.mpr
      (show ¬ 3 ∣ x from fun h => hx3 (Nat.mod_eq_zero_of_dvd h))
    refine order_cycle (by omega) ⟨k,rfl⟩ (fun i => ringVertex k x i.val) ?_ (ring_inj hx hx3) ?_
    · intro i
      have hi := i.isLt
      unfold ringVertex
      split_ifs
      · exact hxA
      · exact hc.1
      · exact hc.2.1 _ (by omega)
      · exact hc.2.2 _ (by omega)
    · intro i j h
      rw [← h]
      exact ring_step hk hx2c.symm hx3c.symm i
  let threshold (n : ℕ) := n/2 + n/3 - n/6


  let multiples (n : ℕ) := (Icc 1 n).filter (fun x => 2 ∣ x ∨ 3 ∣ x)

  have multiples_card (n : ℕ) : (multiples n).card = threshold n := by
    induction n with
    | zero => decide
    | succ n ih =>
      by_cases h : 2 ∣ n+1 ∨ 3 ∣ n+1
      · have he : multiples (n+1) = insert (n+1) (multiples n) := by
          ext x
          simp only [multiples, mem_filter, mem_Icc, mem_insert]
          by_cases hx : x = n+1
          · subst x; simp [h]
          · omega
        have hn : n+1 ∉ multiples n := by simp [multiples]
        rw [he, card_insert_of_notMem hn, ih]
        unfold threshold
        have hmod := Nat.mod_lt n (by decide : 0 < 6)
        interval_cases hv : n%6 <;> omega
      · have he : multiples (n+1) = multiples n := by
          ext x
          simp only [multiples, mem_filter, mem_Icc]
          by_cases hx : x = n+1
          · subst x; simp [h]
          · omega
        rw [he, ih]
        unfold threshold
        have hmod := Nat.mod_lt n (by decide : 0 < 6)
        interval_cases hv : n%6 <;> omega

  have outside {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Icc 1 n)
      (hc : threshold n < A.card) : ∃ x ∈ A, x%2=1 ∧ x%3 ≠ 0 := by
    by_contra! hn
    have hsub : A ⊆ multiples n := by
      intro x hx
      refine mem_filter.mpr ⟨hA hx, ?_⟩
      have := hn x hx
      omega
    have := card_le_card hsub
    rw [multiples_card] at this
    omega

  obtain ⟨x,hx,hx2,hx3⟩ := outside hA hd
  exact ring_cycle hk ⟨h2, h3, hb⟩ hx hx2 hx3


private theorem transfer_cycle {A B : Finset ℕ} {l : ℕ} (hl : 2 < l)
    (f : ℕ → ℕ) (hm : ∀ a ∈ B, f a ∈ A) (hi : Set.InjOn f (B : Set ℕ))
    (hc : ∀ a ∈ B, ∀ b ∈ B, a ≠ b → a.Coprime b → (f a).Coprime (f b))
    (h : l ∈ (coprimeGraph.induce (B : Set ℕ)).oddCycleLengths) :
    l ∈ (coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  let g : coprimeGraph.induce (B : Set ℕ) →g coprimeGraph.induce (A : Set ℕ) :=
    { toFun := fun x => ⟨f x, hm x x.property⟩
      map_rel' := by
        intro x y hxy
        change coprimeGraph.Adj x.val y.val at hxy
        change coprimeGraph.Adj (f x.val) (f y.val)
        rw [coprimeGraph, fromRel_adj] at hxy ⊢
        refine ⟨fun e => hxy.1 (hi x.property y.property e), Or.inl ?_⟩
        obtain hab | hab := hxy.2
        · exact hc _ x.property _ y.property hxy.1 hab
        · exact hc _ x.property _ y.property hxy.1 hab.symm }
  have hcopy : (coprimeGraph.induce (B : Set ℕ)).IsContained
      (coprimeGraph.induce (A : Set ℕ)) :=
    ⟨⟨g, fun a b e => Subtype.ext (hi a.property b.property (congrArg Subtype.val e))⟩⟩
  exact ⟨(cycleGraph_isContained_iff hl).mp (((cycleGraph_isContained_iff hl).mpr h.1).trans hcopy), h.2⟩

private theorem swap_cycle {A : Finset ℕ} {l u v : ℕ} (hl : 2 < l) (hu : u ∈ A)
    (hd : ∀ z ∈ A, z ≠ u → v.Coprime z → u.Coprime z)
    (h : l ∈ (coprimeGraph.induce (↑(insert v (A.erase u)) : Set ℕ)).oddCycleLengths) :
    l ∈ (coprimeGraph.induce (A : Set ℕ)).oddCycleLengths := by
  let f (a : ℕ) := if a = v then u else a
  have om {a : ℕ} (ha : a ∈ insert v (A.erase u)) (hne : a ≠ v) : a ≠ u ∧ a ∈ A :=
    mem_erase.mp ((mem_insert.mp ha).resolve_left hne)
  refine transfer_cycle hl f ?_ ?_ ?_ h
  · intro a ha
    by_cases hv : a = v
    · simpa [f,hv] using hu
    · simpa [f,hv] using (om ha hv).2
  · intro a ha b hb he
    change f a = f b at he
    by_cases hav : a = v <;> by_cases hbv : b = v
    · exact hav.trans hbv.symm
    · exact False.elim ((om hb hbv).1 (by simpa [f,hav,hbv] using he.symm))
    · exact False.elim ((om ha hav).1 (by simpa [f,hav,hbv] using he))
    · simpa [f,hav,hbv] using he
  · intro a ha b hb hab he
    by_cases hav : a = v
    · subst a
      have hbv := hab.symm
      simpa [f,hbv] using hd b (om hb hbv).2 (om hb hbv).1 he
    by_cases hbv : b = v
    · subst b
      simpa [f,hav] using (hd a (om ha hav).2 (om ha hav).1 he.symm).symm
    · simpa [f,hav,hbv] using he

def H1 : Prop :=
  ∀ n : ℕ, n < 200000 → ∀ A : Finset ℕ, A ⊆ Icc 1 n →
    A.card = n/2+n/3-n/6+1 → ∀ k : ℕ, 3 ≤ k → 6*k ≤ n →
    ¬ (2 ∈ A ∧ (∀ i < k, 6*i+3 ∈ A) ∧
      (∀ i, i+1 < k → (if (6*i+4)%5=0 then 6*i+8 else 6*i+4) ∈ A)) →
    (∀ u ∈ A, ¬ (2 ∣ u ∨ 3 ∣ u) →
      ∀ v ∈ (Icc 1 n).filter (fun v => 2 ∣ v ∨ 3 ∣ v), v ∉ A →
      ∃ z ∈ A, z ≠ u ∧ v.Coprime z ∧ ¬ u.Coprime z) →
    2*k+1 ∈ (coprimeGraph.induce (A : Set ℕ)).oddCycleLengths

def H2 : Prop :=
  ∀ n : ℕ, 200000 ≤ n → ∀ A : Finset ℕ, A ⊆ Icc 1 n →
    A.card = n/2+n/3-n/6+1 → ∀ k : ℕ, 3 ≤ k → 6*k ≤ n →
    ¬ (2 ∈ A ∧ (∀ i < k, 6*i+3 ∈ A) ∧
      (∀ i, i+1 < k → (if (6*i+4)%5=0 then 6*i+8 else 6*i+4) ∈ A)) →
    (∀ u ∈ A, ¬ (2 ∣ u ∨ 3 ∣ u) →
      ∀ v ∈ (Icc 1 n).filter (fun v => 2 ∣ v ∨ 3 ∣ v), v ∉ A →
      ∃ z ∈ A, z ≠ u ∧ v.Coprime z ∧ ¬ u.Coprime z) →
    2*k+1 ∈ (coprimeGraph.induce (A : Set ℕ)).oddCycleLengths

theorem main : H1 → H2 → type_of% @Erdos883.erdos_883.parts.i := by
  intro hsmall hlarge n A hA hd l ho hlo hhi
  by_cases hs : l = 3 ∨ l = 5
  · exact short_cycles hA hd hs hhi
  obtain ⟨k, rfl⟩ := ho
  have hk : 3 ≤ k := by omega
  have hn : 6*k ≤ n := by omega
  let D := (Icc 1 n).filter fun v => 2 ∣ v ∨ 3 ∣ v
  let goal (B : Finset ℕ) := 2*k+1 ∈ (coprimeGraph.induce (B : Set ℕ)).oddCycleLengths
  have solve : ∀ m (B : Finset ℕ), (D \ B).card = m → B ⊆ Icc 1 n →
      B.card = (n/2+n/3-n/6)+1 → goal B := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro B hm hB hb
      by_cases hcore : 2 ∈ B ∧ (∀ i < k, 6*i+3 ∈ B) ∧
          (∀ i, i+1 < k → (if (6*i+4)%5=0 then 6*i+8 else 6*i+4) ∈ B)
      · exact core_cycle hB (by omega) (by omega) hcore.1 hcore.2.1 hcore.2.2
      by_cases hblock : ∀ u ∈ B, ¬ (2 ∣ u ∨ 3 ∣ u) → ∀ v ∈ D, v ∉ B →
          ∃ z ∈ B, z ≠ u ∧ v.Coprime z ∧ ¬ u.Coprime z
      · by_cases hcut : n < 200000
        · exact hsmall n hcut B hB hb k hk hn hcore hblock
        · exact hlarge n (by omega) B hB hb k hk hn hcore hblock
      push Not at hblock
      obtain ⟨u, hu, hother, v, hv, hmiss, hdom⟩ := hblock
      have huD : u ∉ D := fun huD => ((mem_filter.mp huD).2).elim hother.1 hother.2
      let C := insert v (B.erase u)
      have hC : C ⊆ Icc 1 n := by
        intro x hx
        obtain h | h := mem_insert.mp hx
        · simpa [h] using (mem_filter.mp hv).1
        · exact hB (mem_erase.mp h).2
      have hCc : C.card = B.card := by
        have hnot : v ∉ B.erase u := fun h => hmiss (mem_erase.mp h).2
        rw [show C = insert v (B.erase u) by rfl, card_insert_of_notMem hnot,
          card_erase_of_mem hu, Nat.sub_add_cancel (card_pos.mpr ⟨u,hu⟩)]
      have he : D \ C = (D \ B).erase v := by
        ext x
        simp only [C, mem_sdiff, mem_insert, mem_erase]
        by_cases hx : x=u
        · subst x; simp [huD]
        · tauto
      have hvm : v ∈ D \ B := mem_sdiff.mpr ⟨hv,hmiss⟩
      have hlt : (D \ C).card < m := by
        rw [he, card_erase_of_mem hvm, hm]
        have hp := card_pos.mpr ⟨v,hvm⟩
        omega
      exact swap_cycle (by omega) hu hdom (ih _ hlt C rfl hC (hCc.trans hb))
  obtain ⟨B, hsub, hcard⟩ := exists_subset_card_eq (s := A)
    (show n/2+n/3-n/6+1 ≤ A.card by omega)
  exact transfer_cycle (by omega) id (fun _ h => hsub h) (fun _ _ _ _ h => h)
    (fun _ _ _ _ _ h => h) (solve _ B rfl (hsub.trans hA) hcard)

end OMA.R_Erdos883_erdos_883_parts_i_R1

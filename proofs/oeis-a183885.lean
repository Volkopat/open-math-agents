import OMAStatements.S_oeis_a183885
import Mathlib

open Finset OMA.S_oeis_a183885
namespace WordCounts

private abbrev Digit := Fin 3
private abbrev State := Digit → Fin 5

private def bag {N : ℕ} (w : Fin N → Digit) := univ.val.map w

private def cap (s : Multiset Digit) : State := fun d =>
  ⟨min 4 (s.count d), by omega⟩

private def step (q : State) (x : Digit) : State := fun d =>
  ⟨min 4 ((q d).val + if x = d then 1 else 0), by omega⟩

private lemma cap_cons (x : Digit) (s : Multiset Digit) :
    cap (x ::ₘ s) = step (cap s) x := by
  funext d
  apply Fin.ext
  simp only [cap, step, Multiset.count_cons]
  by_cases h : x = d <;> simp_all [eq_comm] <;> omega

private def good (q : State) : Prop :=
  ∀ d : Digit, 0 < (q d).val → ∃ x y z : Digit,
    (x.val + y.val + z.val) % 3 = d.val ∧
    ∀ e : Digit, ({d,x,y,z} : Multiset Digit).count e ≤ (q e).val

private instance (q : State) : Decidable (good q) := by unfold good; infer_instance

private lemma fits (d x y z : Digit) (s : Multiset Digit) :
    (∀ e : Digit, ({d,x,y,z} : Multiset Digit).count e ≤ (cap s e).val) ↔
      ({d,x,y,z} : Multiset Digit) ≤ s := by
  rw [Multiset.le_iff_count]
  simp only [cap, le_min_iff]
  constructor
  · exact fun h e => (h e).2
  · intro h e
    exact ⟨(Multiset.count_le_card _ _).trans (by simp), h e⟩

private lemma lift_sub {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β)
    (t : Multiset β) (s : Multiset α) (h : t ≤ s.map f) :
    ∃ u ≤ s, u.map f = t := by
  induction t using Multiset.induction_on generalizing s with
  | empty => exact ⟨0, by simp, by simp⟩
  | cons b t ih =>
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp (Multiset.subset_of_le h (Multiset.mem_cons_self b t))
    rw [← Multiset.cons_erase ha, Multiset.map_cons, Multiset.cons_le_cons_iff] at h
    obtain ⟨u, hu, he⟩ := ih _ h
    exact ⟨a ::ₘ u, by simpa [Multiset.cons_erase ha] using Multiset.cons_le_cons a hu,
      by simp [he]⟩

private lemma witness {N : ℕ} (w : Fin N → Digit) (i : Fin N) :
    (∃ t : Finset (Fin N), t.card = 3 ∧ i ∉ t ∧ (∑ j ∈ t, (w j).val) % 3 = (w i).val) ↔
      ∃ x y z : Digit, (x.val+y.val+z.val)%3 = (w i).val ∧
        ({w i,x,y,z} : Multiset Digit) ≤ bag w := by
  have hb : bag w = w i ::ₘ ((univ.erase i).val.map w) := by
    unfold bag
    rw [← Multiset.map_cons]
    congr 1
    exact (Multiset.cons_erase (Finset.mem_univ i)).symm
  rw [hb]
  constructor
  · rintro ⟨t, ht, hi, hs⟩
    obtain ⟨x,y,z,hxyz⟩ := Multiset.card_eq_three.mp (show (t.val.map w).card = 3 by simpa using ht)
    refine ⟨x,y,z, ?_, ?_⟩
    · have hsum := congrArg (fun v : Multiset Digit => (v.map Fin.val).sum) hxyz
      change ((t.val.map (fun j => (w j).val)).sum) % 3 = _ at hs
      simp [Multiset.map_map] at hsum
      simpa [hsum, add_assoc] using hs
    · change w i ::ₘ _ ≤ w i ::ₘ _
      apply Multiset.cons_le_cons
      rw [← hxyz]
      apply Multiset.map_le_map
      exact Finset.val_le_iff.mpr (Finset.subset_erase.mpr ⟨Finset.subset_univ _, hi⟩)
  · rintro ⟨x,y,z,hs,ht⟩
    obtain ⟨u,hu,he⟩ := lift_sub w ({x,y,z} : Multiset Digit) _
      ((Multiset.cons_le_cons_iff _).mp ht)
    let t : Finset (Fin N) := ⟨u, Multiset.nodup_of_le hu (univ.erase i).nodup⟩
    have hs' : t ⊆ univ.erase i := Finset.val_le_iff.mp hu
    refine ⟨t, ?_, fun hi => Finset.notMem_erase i univ (hs' hi), ?_⟩
    · simpa [t] using congrArg Multiset.card he
    · change ((t.val.map (fun j => (w j).val)).sum)%3 = _
      have e := congrArg (fun v : Multiset Digit => (v.map Fin.val).sum) he
      simp [Multiset.map_map] at e
      simpa [t, e, add_assoc] using hs

private lemma valid_iff {N : ℕ} (w : Fin N → Digit) : Valid w ↔ good (cap (bag w)) := by
  unfold Valid good
  simp only [fits]
  constructor
  · intro h d hd
    have hm : d ∈ bag w := Multiset.count_pos.mp (by simpa [cap] using hd)
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hm
    exact (witness w i).mp (h i)
  · intro h i
    apply (witness w i).mpr
    apply h
    have hm : w i ∈ bag w := Multiset.mem_map_of_mem _ (Finset.mem_univ i)
    simpa [cap] using Multiset.count_pos.mpr hm

private def ways : ℕ → State → ℤ
  | 0, q => if good q then 1 else 0
  | n+1, q => ∑ d : Digit, ways n (step q d)

private lemma ways_words (n : ℕ) (s : Multiset Digit) :
    ways n (cap s) =
      ∑ w : Fin n → Digit, if good (cap (s + bag w)) then (1 : ℤ) else 0 := by
  induction n generalizing s with
  | zero => simp [ways, bag]
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Digit)).sum_comp, Fintype.sum_prod_type]
    simp only [ways]
    apply Finset.sum_congr rfl
    intro d _
    rw [← cap_cons, ih]
    apply Finset.sum_congr rfl
    intro w _
    have hb : bag (Fin.cons d w) = d ::ₘ bag w := by
      unfold bag
      rw [Fin.univ_succ]
      simp [Finset.map_val, Function.comp_def]
    change (if good (cap ((d ::ₘ s) + bag w)) then _ else _) =
      (if good (cap (s + bag (Fin.cons d w))) then _ else _)
    rw [hb, Multiset.cons_add, Multiset.add_cons]

private lemma a_eq (n : ℕ) (hn : n ≠ 0) : a n = ways (n+3) (cap 0) := by
  rw [ways_words, a, if_neg hn, Finset.card_filter]
  push_cast
  simp [valid_iff]


/-- The next letter acts linearly on functions of the three truncated multiplicities. -/
private def defect (n : ℕ) (q : State) : ℤ :=
  ways (n+4) q - 6*ways (n+3) q + 12*ways (n+2) q - 10*ways (n+1) q + 3*ways n q

private lemma defect_succ (n : ℕ) (q : State) :
    defect (n+1) q = ∑ d : Digit, defect n (step q d) := by
  change (∑ d : Digit, ways (n+4) (step q d)) - 6*(∑ d : Digit, ways (n+3) (step q d)) +
    12*(∑ d : Digit, ways (n+2) (step q d)) - 10*(∑ d : Digit, ways (n+1) (step q d)) +
    3*(∑ d : Digit, ways n (step q d)) = _
  simp only [defect, Fin.sum_univ_three]
  ring

private lemma cases_state (P : State → Prop)
    (h : ∀ i j k : Fin 5, P ![i,j,k]) (q : State) : P q := by
  have e : ![q 0,q 1,q 2] = q := by funext d; fin_cases d <;> rfl
  rw [← e]
  exact h _ _ _

/- Encode the three multiplicities in base five. The six sparse rows give the
fourth-order recurrence residual after zero through five further letters.
Each transition is checked for all 125 states. -/
private def row0 (q : State) : ℤ :=
  match (q 0).val * 25 + (q 1).val * 5 + (q 2).val with
  | 0 => 4
  | 1 | 5 => 40
  | 2 | 10 => -7
  | 6 => -2
  | 7 | 11 | 26 | 30 => -21
  | 12 => 13
  | 25 => 35
  | 27 | 31 | 35 => -4
  | 32 | 36 | 52 | 60 => 7
  | 37 | 77 | 85 => -3
  | 50 => 19
  | 51 | 55 => -14
  | 75 => -27
  | 76 | 80 => 10
  | _ => 0

private def row1 (q : State) : ℤ :=
  match (q 0).val * 25 + (q 1).val * 5 + (q 2).val with
  | 0 => 115
  | 1 | 5 => -30
  | 2 | 10 => -25
  | 6 => -46
  | 7 | 11 | 75 => 20
  | 12 | 32 | 36 | 52 | 60 | 76 | 80 => -3
  | 25 => -23
  | 26 | 30 => -22
  | 27 | 31 | 35 => 14
  | 50 => -55
  | 51 | 55 => 17
  | _ => 0

private def row2 (q : State) : ℤ :=
  match (q 0).val * 25 + (q 1).val * 5 + (q 2).val with
  | 0 => -83
  | 1 | 5 => -93
  | 2 | 10 => 34
  | 6 | 50 => 54
  | 7 | 11 | 27 | 31 | 35 | 51 | 55 | 75 => -6
  | 25 => -99
  | 26 | 30 => 45
  | _ => 0

private def row3 (q : State) : ℤ :=
  match (q 0).val * 25 + (q 1).val * 5 + (q 2).val with
  | 0 => -285
  | 1 | 5 => 133
  | 2 | 10 => -12
  | 6 | 26 | 30 | 50 => -18
  | 25 => 144
  | _ => 0

private def row4 (q : State) : ℤ :=
  match (q 0).val * 25 + (q 1).val * 5 + (q 2).val with
  | 0 => 410
  | 1 | 5 => -48
  | 25 => -54
  | _ => 0

private def row5 (q : State) : ℤ :=
  match (q 0).val * 25 + (q 1).val * 5 + (q 2).val with
  | 0 => -150
  | _ => 0

/- The initial layers count valid completions by zero through four letters,
in the same base-five order. They keep each finite verification to one step. -/
private def layer0 (q : State) : ℤ :=
  (#[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,1,1,
    0,0,0,0,0,0,0,0,1,1,0,0,0,1,1,0,1,1,1,1,0,1,1,1,1,
    0,0,0,1,1,0,0,1,1,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
    0,0,0,1,1,0,0,1,1,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
    1,0,1,1,1,0,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] : Array ℤ)[(q 0).val*25 + (q 1).val*5 + (q 2).val]!

private lemma layer_eq0 (q : State) : ways 0 q = layer0 q := by
  apply cases_state (fun r => ways 0 r = layer0 r) _ q
  decide +kernel

private def layer1 (q : State) : ℤ :=
  (#[0,0,0,0,0,0,0,0,1,1,0,0,0,2,2,0,1,2,3,3,0,1,2,3,3,
    0,0,0,2,2,0,0,2,3,3,0,2,3,3,3,2,3,3,3,3,2,3,3,3,3,
    0,0,2,3,3,0,2,3,3,3,2,3,3,3,3,3,3,3,3,3,3,3,3,3,3,
    1,0,3,3,3,0,2,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,
    1,1,3,3,3,1,2,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3] : Array ℤ)[(q 0).val*25 + (q 1).val*5 + (q 2).val]!

private lemma layer_eq1 (q : State) : ways 1 q = layer1 q := by
  change (∑ d : Digit, ways 0 (step q d)) = _
  simp only [layer_eq0]
  apply cases_state (fun r => (∑ d : Digit, layer0 (step r d)) = layer1 r) _ q
  decide +kernel

private def layer2 (q : State) : ℤ :=
  (#[0,0,0,3,3,0,0,3,6,6,0,3,7,8,8,3,6,8,9,9,3,6,8,9,9,
    0,0,6,8,8,0,6,9,9,9,6,9,9,9,9,8,9,9,9,9,8,9,9,9,9,
    1,4,9,9,9,4,8,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,
    1,6,9,9,9,6,8,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,
    3,6,9,9,9,6,8,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9] : Array ℤ)[(q 0).val*25 + (q 1).val*5 + (q 2).val]!

private lemma layer_eq2 (q : State) : ways 2 q = layer2 q := by
  change (∑ d : Digit, ways 1 (step q d)) = _
  simp only [layer_eq1]
  apply cases_state (fun r => (∑ d : Digit, layer1 (step r d)) = layer2 r) _ q
  decide +kernel

private def layer3 (q : State) : ℤ :=
  (#[0,0,12,17,17,0,12,22,23,23,12,22,25,26,26,17,23,26,27,27,17,23,26,27,27,
    1,16,26,26,26,16,26,27,27,27,26,27,27,27,27,26,27,27,27,27,26,27,27,27,27,
    9,23,27,27,27,23,26,27,27,27,27,27,27,27,27,27,27,27,27,27,27,27,27,27,27,
    15,23,27,27,27,23,26,27,27,27,27,27,27,27,27,27,27,27,27,27,27,27,27,27,27,
    15,23,27,27,27,23,26,27,27,27,27,27,27,27,27,27,27,27,27,27,27,27,27,27,27] : Array ℤ)[(q 0).val*25 + (q 1).val*5 + (q 2).val]!

private lemma layer_eq3 (q : State) : ways 3 q = layer3 q := by
  change (∑ d : Digit, ways 2 (step q d)) = _
  simp only [layer_eq2]
  apply cases_state (fun r => (∑ d : Digit, layer2 (step r d)) = layer3 r) _ q
  decide +kernel

private def layer4 (q : State) : ℤ :=
  (#[1,40,65,66,66,40,70,75,76,76,65,75,79,80,80,66,76,80,81,81,66,76,80,81,81,
    41,75,80,80,80,75,80,81,81,81,80,81,81,81,81,80,81,81,81,81,80,81,81,81,81,
    61,76,81,81,81,76,80,81,81,81,81,81,81,81,81,81,81,81,81,81,81,81,81,81,81,
    61,76,81,81,81,76,80,81,81,81,81,81,81,81,81,81,81,81,81,81,81,81,81,81,81,
    61,76,81,81,81,76,80,81,81,81,81,81,81,81,81,81,81,81,81,81,81,81,81,81,81] : Array ℤ)[(q 0).val*25 + (q 1).val*5 + (q 2).val]!

private lemma layer_eq4 (q : State) : ways 4 q = layer4 q := by
  change (∑ d : Digit, ways 3 (step q d)) = _
  simp only [layer_eq3]
  apply cases_state (fun r => (∑ d : Digit, layer3 (step r d)) = layer4 r) _ q
  decide +kernel

private lemma defect_zero (q : State) : defect 0 q = row0 q := by
  change ways 4 q - 6*ways 3 q + 12*ways 2 q - 10*ways 1 q + 3*ways 0 q = _
  rw [layer_eq4, layer_eq3, layer_eq2, layer_eq1, layer_eq0]
  apply cases_state (fun r => layer4 r - 6*layer3 r + 12*layer2 r - 10*layer1 r + 3*layer0 r = row0 r) _ q
  decide +kernel

private lemma defect_one (q : State) : defect 1 q = row1 q := by
  change defect (0+1) q = _
  rw [defect_succ]
  simp only [defect_zero]
  apply cases_state (fun r => (∑ d : Digit, row0 (step r d)) = row1 r) _ q
  decide +kernel

private lemma defect_two (q : State) : defect 2 q = row2 q := by
  change defect (1+1) q = _
  rw [defect_succ]
  simp only [defect_one]
  apply cases_state (fun r => (∑ d : Digit, row1 (step r d)) = row2 r) _ q
  decide +kernel

private lemma defect_three (q : State) : defect 3 q = row3 q := by
  change defect (2+1) q = _
  rw [defect_succ]
  simp only [defect_two]
  apply cases_state (fun r => (∑ d : Digit, row2 (step r d)) = row3 r) _ q
  decide +kernel

private lemma defect_four (q : State) : defect 4 q = row4 q := by
  change defect (3+1) q = _
  rw [defect_succ]
  simp only [defect_three]
  apply cases_state (fun r => (∑ d : Digit, row3 (step r d)) = row4 r) _ q
  decide +kernel

private lemma defect_five (q : State) : defect 5 q = row5 q := by
  change defect (4+1) q = _
  rw [defect_succ]
  simp only [defect_four]
  apply cases_state (fun r => (∑ d : Digit, row4 (step r d)) = row5 r) _ q
  decide +kernel

private lemma defect_six (q : State) : defect 6 q = 0 := by
  change defect (5+1) q = _
  rw [defect_succ]
  simp only [defect_five]
  apply cases_state (fun r => (∑ d : Digit, row5 (step r d)) = 0) _ q
  decide +kernel


private lemma defect_vanish (n : ℕ) (q : State) : defect (n+6) q = 0 := by
  induction n generalizing q with
  | zero => exact defect_six q
  | succ n ih =>
    change defect ((n+6)+1) q = 0
    rw [defect_succ]
    simp only [ih, Finset.sum_const_zero]

private lemma rec (n : ℕ) (h : 6 < n) :
    a n = 6*a (n-1) - 12*a (n-2) + 10*a (n-3) - 3*a (n-4) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k+7 := ⟨n-7, by omega⟩
  simp only [a_eq _ (by omega : k+7 ≠ 0),
    show k+7-2 = k+5 by omega, show k+7-3 = k+4 by omega,
    show k+7-4 = k+3 by omega, show k+7-1 = k+6 by omega]
  repeat rw [a_eq _ (by omega)]
  have H := defect_vanish k (cap 0)
  change ways (k+10) _ - 6*ways (k+9) _ + 12*ways (k+8) _ - 10*ways (k+7) _ + 3*ways (k+6) _ = 0 at H
  change ways (k+10) _ = 6*ways (k+9) _ - 12*ways (k+8) _ + 10*ways (k+7) _ - 3*ways (k+6) _
  linarith

set_option maxRecDepth 4096 in
private lemma initial :
    a 0 = 0 ∧ a 1 = 1 ∧ a 2 = 121 ∧ a 3 = 631 ∧
    a 4 = 2059 ∧ a 5 = 6399 ∧ a 6 = 19483 := by
  have h0 : ways 0 (cap 0) = 1 := by
    rw [layer_eq0]
    decide
  have h1 : ways 1 (cap 0) = 0 := by
    rw [layer_eq1]
    decide
  have h2 : ways 2 (cap 0) = 0 := by
    rw [layer_eq2]
    decide
  have h3 : ways 3 (cap 0) = 0 := by
    rw [layer_eq3]
    decide
  have h4 : ways 4 (cap 0) = 1 := by
    have h := defect_zero (cap 0)
    norm_num [defect, row0, cap, h0, h1, h2, h3] at h
    omega
  have h5 : ways 5 (cap 0) = 121 := by
    have h := defect_one (cap 0)
    norm_num [defect, row1, cap, h1, h2, h3, h4] at h
    omega
  have h6 : ways 6 (cap 0) = 631 := by
    have h := defect_two (cap 0)
    norm_num [defect, row2, cap, h2, h3, h4, h5] at h
    omega
  have h7 : ways 7 (cap 0) = 2059 := by
    have h := defect_three (cap 0)
    norm_num [defect, row3, cap, h3, h4, h5, h6] at h
    omega
  have h8 : ways 8 (cap 0) = 6399 := by
    have h := defect_four (cap 0)
    norm_num [defect, row4, cap, h4, h5, h6, h7] at h
    omega
  have h9 : ways 9 (cap 0) = 19483 := by
    have h := defect_five (cap 0)
    norm_num [defect, row5, cap, h5, h6, h7, h8] at h
    omega
  exact ⟨by simp [a], (a_eq 1 (by decide)).trans h4, (a_eq 2 (by decide)).trans h5, (a_eq 3 (by decide)).trans h6, (a_eq 4 (by decide)).trans h7, (a_eq 5 (by decide)).trans h8, (a_eq 6 (by decide)).trans h9⟩

private def formula (n : ℕ) : ℤ := 3^(n+3) - 2*((n:ℤ)+4)^2

private lemma closed_form (n : ℕ) (hn : 3 ≤ n) : a n = formula n := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6⟩ := initial
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases small : n ≤ 6
    · interval_cases n <;> norm_num [formula, h3,h4,h5,h6]
    · obtain ⟨k,rfl⟩ : ∃ k, n = k+7 := ⟨n-7, by omega⟩
      rw [rec _ (by omega)]
      rw [ih _ (by omega) (by omega), ih _ (by omega) (by omega),
          ih _ (by omega) (by omega), ih _ (by omega) (by omega)]
      change 6*formula (k+6) - 12*formula (k+5) + 10*formula (k+4) - 3*formula (k+3)
        = formula (k+7)
      simp only [formula, pow_add, Nat.cast_add, Nat.cast_ofNat]
      ring

open PowerSeries in
private lemma series_eq :
    mk a * ((1-X)^3 * (1-3*X)) =
      X*(1+115*X-83*X^2-285*X^3+410*X^4-150*X^5) := by
  let A := mk a
  change A * _ = _
  rw [show A*((1-X)^3*(1-3*X)) =
      A-C 6*(A*X^1)+C 12*(A*X^2)-C 10*(A*X^3)+C 3*(A*X^4) by
      simp only [map_ofNat]; ring,
    show (X*(1+115*X-83*X^2-285*X^3+410*X^4-150*X^5) : ℤ⟦X⟧) =
      C 1*X^1+C 115*X^2-C 83*X^3-C 285*X^4+C 410*X^5-C 150*X^6 by
      simp only [map_one, map_ofNat]; ring]
  ext n
  simp only [map_sub, map_add, coeff_C_mul_X_pow, coeff_C_mul, coeff_mul_X_pow', coeff_C, A, coeff_mk]
  by_cases small : n ≤ 6
  · obtain ⟨h0,h1,h2,h3,h4,h5,h6⟩ := initial
    interval_cases n <;> norm_num [h0,h1,h2,h3,h4,h5,h6]
  · simp (disch := omega) only [if_pos, if_neg]
    linarith [rec n (by omega)]

end WordCounts

theorem OMA.solution : type_of% @OMA.S_oeis_a183885.main := by
  exact ⟨WordCounts.closed_form, WordCounts.series_eq, WordCounts.rec⟩

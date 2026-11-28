import OMAStatements.S_oeis_a389592
import Mathlib

-- Problem: A389592: in each 2-dense sublist of the divisors of n, the sum of the non-smallest terms
-- equals the sublist sum minus the k-th term of A379288.
-- Credit: @theterabites
--
-- Proof: the heads of the 2-dense sublists are exactly the divisors d whose predecessor is
-- below d / 2; such a d is never even (d / 2 would be a divisor in between), and for odd d this
-- is the A379288 condition. So the list of block heads is row 379288 of n, and since each block
-- is strictly increasing, the sum of its non-smallest terms is its sum minus its head.
-- The gap lemma follows the divisor-block argument of the merged proof of A379379.

open OMA.S_oeis_a389592
open scoped Classical

namespace OMA.A389592

private abbrev small (b d : ℕ) := decide (d ≤ 2 * b)

/-- The divisors following a gap (previous divisor less than half). -/
private def gapList (b : ℕ) (xs : List ℕ) : List ℕ :=
  (((b :: xs).zip xs).filter (fun p => decide (2 * p.1 < p.2))).map Prod.snd

private lemma gapList_cons (b d : ℕ) (xs : List ℕ) :
    gapList b (d :: xs) = (if 2 * b < d then [d] else []) ++ gapList d xs := by
  by_cases h : 2 * b < d <;> simp [gapList, h]

private lemma loop_heads (xs : List ℕ) (b : ℕ) (run : List ℕ) (acc : List (List ℕ)) :
    (List.splitBy.loop small xs b run acc).map (fun r => r.headD 0) =
      (acc.map (fun r => r.headD 0)).reverse ++ [(b :: run).getLast?.getD 0] ++ gapList b xs := by
  induction xs generalizing b run acc with
  | nil =>
    simp [List.splitBy.loop, gapList, List.map_reverse, List.head?_reverse, List.headD_eq_head?_getD,
      List.getLast?_cons]
  | cons d xs ih =>
    rw [List.splitBy.loop, gapList_cons]
    by_cases h : d ≤ 2 * b
    · have hs : small b d = true := by simp [small, h]
      simp only [hs]
      rw [ih]
      simp [not_lt_of_ge h, List.getLast?_cons_cons]
    · have hs : small b d = false := by simp [small, h]
      simp only [hs]
      rw [ih]
      simp [show 2 * b < d by omega, List.headD_eq_head?_getD, List.head?_reverse, List.getLast?_cons]

private abbrev starts (D : Finset ℕ) (d : ℕ) := ∀ j ∈ D, j < d → 2 * j < d

private lemma remaining_gaps (D : Finset ℕ) (xs : List ℕ) (b : ℕ) (hb : b ∈ D)
    (inside : ∀ j ∈ xs, j ∈ D) (cover : ∀ j ∈ D, j ≤ b ∨ j ∈ xs)
    (order : (b :: xs).Pairwise (· < ·)) :
    gapList b xs = xs.filter fun d => decide (starts D d) := by
  induction xs generalizing b with
  | nil => rfl
  | cons d tail ih =>
    obtain ⟨hbefore, htail⟩ := List.pairwise_cons.mp order
    have hbd : b < d := hbefore d (by simp)
    have hd : d ∈ D := inside d (by simp)
    have hinside : ∀ j ∈ tail, j ∈ D := fun j hj => inside j (by simp [hj])
    have hcover : ∀ j ∈ D, j ≤ d ∨ j ∈ tail := by
      intro j hj
      rcases cover j hj with h | h
      · exact Or.inl (by omega)
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inl le_rfl
        · exact Or.inr h
    have criterion : starts D d ↔ 2 * b < d := by
      constructor
      · intro hs
        exact hs b hb hbd
      · intro h j hj hjd
        rcases cover j hj with hle | hmem
        · omega
        · rcases List.mem_cons.mp hmem with rfl | ht
          · omega
          · have := (List.pairwise_cons.mp htail).1 j ht
            omega
    rw [gapList_cons, ih d hd hinside hcover htail, List.filter_cons]
    by_cases h : 2 * b < d
    · rw [if_pos h, if_pos (by simpa using criterion.mpr h)]
      rfl
    · rw [if_neg h, if_neg (by simpa using fun hs => h (criterion.mp hs))]
      rfl

private lemma heads_eq (D : Finset ℕ) (_pos : ∀ d ∈ D, 0 < d) :
    ((D.sort (· ≤ ·)).splitBy small).map (fun r => r.headD 0) =
      (D.sort (· ≤ ·)).filter fun d => decide (starts D d) := by
  have hsort : (D.sort (· ≤ ·)).Pairwise (· < ·) := D.sortedLT_sort.pairwise
  have mem (j : ℕ) : j ∈ D.sort (· ≤ ·) ↔ j ∈ D := Finset.mem_sort _
  generalize hl : D.sort (· ≤ ·) = xs at hsort mem
  cases xs with
  | nil => rfl
  | cons d tail =>
    have hd : d ∈ D := (mem d).mp (by simp)
    have hi : ∀ j ∈ tail, j ∈ D := fun j hj => (mem j).mp (by simp [hj])
    have hc : ∀ j ∈ D, j ≤ d ∨ j ∈ tail := by
      intro j hj
      rcases List.mem_cons.mp ((mem j).mpr hj) with rfl | h
      · exact Or.inl le_rfl
      · exact Or.inr h
    have hs : starts D d := by
      intro j hj hjd
      rcases List.mem_cons.mp ((mem j).mpr hj) with rfl | h
      · omega
      · have := (List.pairwise_cons.mp hsort).1 j h
        omega
    rw [List.splitBy, loop_heads, remaining_gaps D tail d hd hi hc hsort, List.filter_cons,
      if_pos (by simpa using hs)]
    simp

private lemma start_iff (n d : ℕ) (hd : d ∈ n.divisors) :
    starts n.divisors d ↔ (Odd d ∧ ¬ ∃ j ∈ n.divisors, j < d ∧ d < 2 * j) := by
  constructor
  · intro hs
    refine ⟨Nat.not_even_iff_odd.mp ?_, ?_⟩
    · rintro ⟨u, hu⟩
      have hud : u ∣ d := ⟨2, by omega⟩
      obtain ⟨hdn, hn⟩ := Nat.mem_divisors.mp hd
      have hum : u ∈ n.divisors := Nat.mem_divisors.mpr ⟨hud.trans hdn, hn⟩
      have hpos := Nat.pos_of_mem_divisors hd
      have := hs u hum (by omega)
      omega
    · rintro ⟨j, hj, hlt, hcut⟩
      have := hs j hj hlt
      omega
  · rintro ⟨⟨t, ht⟩, hw⟩ j hj hlt
    by_contra hc
    apply hw
    refine ⟨j, hj, hlt, ?_⟩
    omega

/-- Sorting commutes with filtering. -/
private lemma sort_filter (D : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (D.filter p).sort (· ≤ ·) = (D.sort (· ≤ ·)).filter (fun d => decide (p d)) := by
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (Finset.pairwise_sort _ _)
    ((Finset.pairwise_sort _ _).filter _)
  apply List.perm_of_nodup_nodup_toFinset_eq (Finset.sort_nodup _ _)
    ((Finset.sort_nodup _ _).filter _)
  ext x
  simp

/-- Each block is a strictly increasing run of divisors. -/
private lemma block_sorted {xs b : List ℕ} (hx : xs.Pairwise (· < ·)) (hb : b ∈ xs.splitBy small) :
    b.Pairwise (· < ·) := by
  have hsub : List.Sublist b (xs.splitBy small).flatten := List.sublist_flatten_of_mem hb
  rw [List.flatten_splitBy] at hsub
  exact hx.sublist hsub

private lemma block_value {h : ℕ} {t : List ℕ} (hb : (h :: t).Pairwise (· < ·)) :
    ((h :: t).filter (fun x => decide (∃ y ∈ h :: t, y < x))).sum = (h :: t).sum - h := by
  have hlt : ∀ x ∈ t, h < x := (List.pairwise_cons.mp hb).1
  have hft : t.filter (fun x => decide (∃ y ∈ h :: t, y < x)) = t := by
    apply List.filter_eq_self.mpr
    intro x hx
    simp [hlt x hx]
  have hh : ¬ ∃ y ∈ h :: t, y < h := by
    rintro ⟨y, hy, hyh⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · omega
    · have := hlt y hy; omega
  rw [List.filter_cons, if_neg (by simpa using hh), hft, List.sum_cons]
  omega

end OMA.A389592

open OMA.A389592

theorem OMA.A389592.main_proof : ∀ n : ℕ, 1 ≤ n → ∀ k < (blocks n).length,
    T n k = A384149 n k - A379288 n k := by
  intro n _ k hk
  have hpos : ∀ d ∈ n.divisors, 0 < d := fun _ hd => Nat.pos_of_mem_divisors hd
  have hheads : (blocks n).map (fun r => r.headD 0) = row379288 n := by
    unfold blocks row379288
    rw [sort_filter, heads_eq n.divisors hpos]
    apply List.filter_congr
    intro d hd
    simp only [decide_eq_decide]
    exact start_iff n d ((Finset.mem_sort _).mp hd)
  have hmem : (blocks n)[k] ∈ blocks n := List.getElem_mem hk
  have hblk : blk n k = (blocks n)[k] := by simp [blk, hk]
  have hrow : A379288 n k = ((blocks n)[k]).headD 0 := by
    simp [A379288, ← hheads, hk]
  have hsorted := block_sorted (n.divisors.sortedLT_sort.pairwise) hmem
  have hne := List.ne_nil_of_mem_splitBy hmem
  unfold T A384149
  rw [hrow, hblk]
  generalize (blocks n)[k] = b at hsorted hne
  obtain ⟨h, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [block_value hsorted]
  simp

theorem OMA.solution : type_of% @OMA.S_oeis_a389592.main := by
  exact OMA.A389592.main_proof

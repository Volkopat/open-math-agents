import OMAStatements.S_oeis_a391538

-- Problem: A391538: Guaranteed win if opponent chooses one of three baskets and the player chooses the coins with values from 1 to n (see Comments for
-- Credit: @sobrien032

/-!
# The three-basket game

Ruediger Jehn posed the general formula in OEIS A391538.
Fabien Nießen and Silas Rathke studied the 2025-coin game.
Herman Palmgren formalized the problem statement.

The lower bound reserves the largest coin and partitions the smaller coins
into three groups. The upper bound follows by choosing a least-loaded basket.
-/

namespace BasketWork

private theorem partition_extend (n : ℕ) (hn : 4 < n) (c : ℕ → Fin 3)
    (hc : ∀ i, n * (n - 1) / 6 ≤ ∑ x ∈ (Finset.Ico 1 n).filter (fun x => c x = i), x) :
    ∃ e : ℕ → Fin 3, ∀ i, (n + 6) * (n + 6 - 1) / 6 ≤
      ∑ x ∈ (Finset.Ico 1 (n + 6)).filter (fun x => e x = i), x := by
  let e : ℕ → Fin 3 := fun x => if x < n then c x else
    ([0, 1, 2, 2, 1, 0] : List (Fin 3))[x - n]?.getD 0
  refine ⟨e, fun i => ?_⟩
  have h_old :
      (∑ x ∈ Finset.Ico 1 n, if e x = i then x else 0) =
        ∑ x ∈ (Finset.Ico 1 n).filter (fun x => c x = i), x := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x hx => ?_
    simp [e, (Finset.mem_Ico.mp hx).2]
  have h_new : (∑ x ∈ Finset.Ico n (n + 6), if e x = i then x else 0) =
      2 * n + 5 := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    fin_cases i <;> norm_num [e, Finset.sum_range_succ] <;> simp +decide <;> omega
  have h_prod : (n + 6) * (n + 6 - 1) = n * (n - 1) + 6 * (2 * n + 5) := by
    rw [show n + 6 - 1 = n + 5 by omega]
    have h_pred : n - 1 + 1 = n := by omega
    nlinarith [congrArg (n * ·) h_pred]
  rw [Finset.sum_filter, ← Finset.sum_Ico_consecutive _ (show 1 ≤ n by omega)
    (show n ≤ n + 6 by omega), h_old, h_new, h_prod]
  have := hc i
  omega

theorem partition (n : ℕ) (hn : 4 < n) : ∃ c : ℕ → Fin 3, ∀ i,
    n * (n - 1) / 6 ≤ ∑ x ∈ (Finset.Ico 1 n).filter (fun x => c x = i), x := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h_large : 11 ≤ n
    · obtain ⟨c, hc⟩ := ih (n - 6) (by omega) (by omega)
      simpa only [Nat.sub_add_cancel (show 6 ≤ n by omega)] using
        partition_extend (n - 6) (by omega) c hc
    · have h_upper : n ≤ 10 := by omega
      interval_cases n
      · exact ⟨fun x => ([0, 0, 0, 1, 2] : List (Fin 3))[x]?.getD 0, by decide⟩
      · exact ⟨fun x => ([0, 0, 1, 1, 0, 2] : List (Fin 3))[x]?.getD 0, by decide⟩
      · exact ⟨fun x => ([0, 0, 1, 2, 2, 1, 0] : List (Fin 3))[x]?.getD 0, by decide⟩
      · exact ⟨fun x => ([0, 0, 0, 1, 2, 2, 0, 1] : List (Fin 3))[x]?.getD 0, by decide⟩
      · exact ⟨fun x => ([0, 0, 0, 0, 1, 2, 0, 2, 1] : List (Fin 3))[x]?.getD 0, by decide⟩
      · exact ⟨fun x => ([0, 0, 0, 0, 0, 0, 1, 2, 2, 1] : List (Fin 3))[x]?.getD 0, by decide⟩

end BasketWork

namespace BasketWork

open OMA.S_oeis_a391538

private theorem keepPlaying (t : ℕ) (s : Finset ℕ) (b : Fin 3 → ℕ)
    (h : ∃ j, t ≤ b j) : CanForce t s b := by
  classical
  induction s using Finset.strongInductionOn generalizing b with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨x, hx⟩ := hs
      refine CanForce.turn (fun _ => x) (fun _ => hx) (fun i => ?_)
      apply ih _ (Finset.erase_ssubset hx)
      obtain ⟨j, hj⟩ := h
      refine ⟨j, ?_⟩
      by_cases he : j = i
      · subst j
        simpa using hj.trans (Nat.le_add_right (b i) x)
      · simpa [Function.update_of_ne he] using hj
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
      exact CanForce.finish h

private theorem playReserved (n t : ℕ) (c : ℕ → Fin 3) (s : Finset ℕ)
    (b : Fin 3 → ℕ) (hn : n ∉ s)
    (hb : ∀ i, t ≤ b i + ∑ x ∈ s.filter (fun x => c x = i), x) :
    CanForce (n + t) (insert n s) b := by
  classical
  induction s using Finset.strongInductionOn generalizing b with
  | _ s ih =>
    have act (i : Fin 3) : ∃ x ∈ insert n s, CanForce (n + t) ((insert n s).erase x)
        (Function.update b i (b i + x)) := by
      by_cases hs : (s.filter (fun x => c x = i)).Nonempty
      · obtain ⟨x, hx⟩ := hs
        obtain ⟨hxs, hxi⟩ := Finset.mem_filter.mp hx
        refine ⟨x, Finset.mem_insert_of_mem hxs, ?_⟩
        have hnx : n ≠ x := by
          rintro rfl
          exact hn hxs
        rw [Finset.erase_insert_of_ne hnx]
        apply ih _ (Finset.erase_ssubset hxs) _ (fun h => hn (Finset.mem_of_mem_erase h))
        intro j
        rw [Finset.filter_erase]
        by_cases he : j = i
        · subst j
          rw [Function.update_self]
          have hsum := Finset.sum_erase_add (s.filter (fun x => c x = i)) (fun x => x) hx
          have hi := hb i
          omega
        · have hout : x ∉ s.filter (fun y => c y = j) :=
            fun h => he ((Finset.mem_filter.mp h).2.symm.trans hxi)
          rw [Function.update_of_ne he, Finset.erase_eq_of_notMem hout]
          exact hb j
      · have hsc : t ≤ b i := by
          simpa [Finset.not_nonempty_iff_eq_empty.mp hs] using hb i
        refine ⟨n, Finset.mem_insert_self _ _, keepPlaying _ _ _ ⟨i, ?_⟩⟩
        rw [Function.update_self]
        omega
    choose x hx hplay using act
    exact CanForce.turn x hx hplay

theorem lower (n : ℕ) (hn : 4 < n) (c : ℕ → Fin 3)
    (hc : ∀ i, n * (n - 1) / 6 ≤ ∑ x ∈ (Finset.Ico 1 n).filter (fun x => c x = i), x) :
    CanForce (n + n * (n - 1) / 6) (Finset.Icc 1 n) (fun _ => 0) := by
  rw [← Finset.Ico_insert_right (show 1 ≤ n by omega)]
  exact playReserved _ _ c _ _ (by simp) (by simpa using hc)

end BasketWork

namespace BasketWork

open OMA.S_oeis_a391538

private theorem least_basket_bound {t n total : ℕ} {coins : Finset ℕ}
    {score : Fin 3 → ℕ} (win : CanForce t coins score)
    (mass : (∑ i, score i) + (∑ c ∈ coins, c) = total)
    (sizes : ∀ c ∈ coins, c ≤ n)
    (safe : ∀ i, 3 * score i ≤ total + 2 * n) : 3 * t ≤ total + 2 * n := by
  induction win with
  | finish reached =>
    obtain ⟨i, hi⟩ := reached
    exact (Nat.mul_le_mul_left 3 hi).trans (safe i)
  | @turn coins score choice legal play ih =>
    obtain ⟨i, _, least⟩ := Finset.univ.exists_min_image score Finset.univ_nonempty
    have hmin : 3 * score i ≤ ∑ j, score j := by
      rw [Fin.sum_univ_three]
      have h₀ := least 0 (Finset.mem_univ _)
      have h₁ := least 1 (Finset.mem_univ _)
      have h₂ := least 2 (Finset.mem_univ _)
      omega
    have erase := coins.sum_erase_add (fun c => c) (legal i)
    have update : (∑ j, Function.update score i (score i + choice i) j) =
        (∑ j, score j) + choice i := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
      have ei := Finset.univ.sum_erase_add score (Finset.mem_univ i)
      omega
    apply ih i
    · rw [update]
      omega
    · exact fun c hc => sizes c (Finset.mem_of_mem_erase hc)
    · intro j
      by_cases hj : j = i
      · subst j
        rw [Function.update_self]
        have hsize := sizes (choice i) (legal i)
        omega
      · rw [Function.update_of_ne hj]
        exact safe j

theorem upper (n t : ℕ) (_hn : 4 < n)
    (h : CanForce t (Finset.Icc 1 n) (fun _ => 0)) : t ≤ n + n * (n - 1) / 6 := by
  have bound := least_basket_bound (n := n) (total := ∑ c ∈ Finset.Icc 1 n, c)
    h (by simp) (fun _ hc => (Finset.mem_Icc.mp hc).2) (by simp)
  have hset : Finset.Icc 1 n = (Finset.range (n + 1)).erase 0 := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]
    omega
  have hzero := (Finset.range (n + 1)).sum_erase_add (fun c : ℕ => c)
    (show 0 ∈ Finset.range (n + 1) by simp)
  simp only [Nat.add_zero, Finset.sum_range_succ] at hzero
  rw [hset, hzero] at bound
  have gauss := Finset.sum_range_id_mul_two n
  omega

end BasketWork

theorem OMA.solution : type_of% @OMA.S_oeis_a391538.main := by
  intro n hn
  obtain ⟨c, hc⟩ := BasketWork.partition n hn
  exact ⟨BasketWork.lower n hn c hc, fun t ht => BasketWork.upper n t hn ht⟩

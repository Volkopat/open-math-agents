import FormalConjectures.ErdosProblems.«1198»

/-! Shorter proof of `Erdos1198.erdos_1198.variants.hindman`. -/

open Hindman Finset

private def cut (q : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => cut q n + (∑ j ∈ range (cut q n), q j) + 1

theorem OMA.solution : type_of% @Erdos1198.erdos_1198.variants.hindman := by
  classical
  intro c
  let part (d : Fin 2) := {n : ℕ | 0 < n ∧ c n = d}
  let ones : Stream' ℕ := fun _ => 1
  have pos : ∀ {s : Stream' ℕ}, (∀ i, 0 < s.get i) → ∀ {m}, m ∈ FS s → 0 < m := by
    intro s hall m hm
    induction hm with
    | head' s => exact hall 0
    | tail' s m _ ih => exact ih fun i => hall (i + 1)
    | cons' s m _ _ => exact Nat.add_pos_left (hall 0) _
  obtain ⟨_, ⟨d, rfl⟩, s, hs⟩ := FS_partition_regular ones _ (Set.finite_range part) fun n hn =>
    Set.mem_sUnion.2 ⟨part (c n), ⟨c n, rfl⟩, pos (s := ones) (fun _ => Nat.zero_lt_one) hn, rfl⟩
  have hq (i : ℕ) : 0 < s.get i := (hs (FS.singleton s i)).1
  let B (i : ℕ) := Ico (cut s.get i) (cut s.get (i + 1))
  have step (i : ℕ) : cut s.get i < cut s.get (i + 1) := by rw [cut]; omega
  have mono := strictMono_nat_of_lt_succ step
  have hdisj {i j} (hij : i < j) : Disjoint (B i) (B j) := disjoint_left.2 fun x hx hy =>
    (mem_Ico.1 hx).2.not_ge ((mono.monotone hij).trans (mem_Ico.1 hy).1)
  refine ⟨fun i => ∑ j ∈ B i, s.get j, strictMono_nat_of_lt_succ fun i => ?_,
    sum_pos (fun j _ => hq j) ⟨cut s.get 0, mem_Ico.2 ⟨le_rfl, step 0⟩⟩, d, fun T hT => ?_⟩
  · have hlo : (B (i + 1)).card ≤ ∑ j ∈ B (i + 1), s.get j :=
      (by simp : (B (i + 1)).card = ∑ _ ∈ B (i + 1), 1) ▸ sum_le_sum fun j _ => hq j
    have hhi : ∑ j ∈ B i, s.get j ≤ ∑ j ∈ range (cut s.get (i + 1)), s.get j :=
      sum_le_sum_of_subset_of_nonneg (fun j hj => mem_range.2 (mem_Ico.1 hj).2) fun _ _ _ => by omega
    rw [show (B (i + 1)).card = (∑ j ∈ range (cut s.get (i + 1)), s.get j) + 1 by
      simp [B, Nat.card_Ico, cut]; omega] at hlo
    omega
  · obtain ⟨t, ht⟩ := hT
    have hne : (T.biUnion B).Nonempty :=
      ⟨cut s.get t, mem_biUnion.2 ⟨t, ht, mem_Ico.2 ⟨le_rfl, step t⟩⟩⟩
    have hit := (hs (FS.finsetSum s _ hne)).2
    rwa [sum_biUnion fun i _ j _ hij => (lt_or_gt_of_ne hij).elim hdisj fun h => (hdisj h).symm] at hit

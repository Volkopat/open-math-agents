import OMAStatements.S_oeis_a242258
import Mathlib

namespace A242258Proof

open OMA.S_oeis_a242258

lemma exists_mem {n : ℕ} (P : Nat.Partition (n + 1)) : ∃ k, k ∈ P.parts := by
  by_contra h
  have h0 : P.parts = 0 := Multiset.eq_zero_of_forall_notMem (fun k hk => h ⟨k, hk⟩)
  have h1 := P.parts_sum
  rw [h0] at h1
  simp at h1

def minPart {n : ℕ} (P : Nat.Partition (n + 1)) : ℕ := Nat.find (exists_mem P)

lemma minPart_mem {n : ℕ} (P : Nat.Partition (n + 1)) : minPart P ∈ P.parts :=
  Nat.find_spec (exists_mem P)

lemma minPart_le {n : ℕ} (P : Nat.Partition (n + 1)) {x : ℕ} (hx : x ∈ P.parts) :
    minPart P ≤ x :=
  Nat.find_min' (exists_mem P) hx

def removeOne {n : ℕ} (P : Nat.Partition (n + 1)) (h : 1 ∈ P.parts) : Nat.Partition n where
  parts := P.parts.erase 1
  parts_pos := fun hi => P.parts_pos (Multiset.mem_of_mem_erase hi)
  parts_sum := by
    have hs := Multiset.sum_erase h
    rw [P.parts_sum] at hs
    omega

def decrMin {n : ℕ} (P : Nat.Partition (n + 1)) (h : 1 ∉ P.parts) : Nat.Partition n where
  parts := (minPart P - 1) ::ₘ P.parts.erase (minPart P)
  parts_pos := by
    intro i hi
    rcases Multiset.mem_cons.1 hi with rfl | hi'
    · have h1 := P.parts_pos (minPart_mem P)
      have h2 : minPart P ≠ 1 := fun e => h (by have hm := minPart_mem P; rw [e] at hm; exact hm)
      omega
    · exact P.parts_pos (Multiset.mem_of_mem_erase hi')
  parts_sum := by
    have h1 := P.parts_pos (minPart_mem P)
    have hs := Multiset.sum_erase (minPart_mem P)
    rw [P.parts_sum] at hs
    rw [Multiset.sum_cons]
    omega

lemma decrMin_parts {n : ℕ} (P : Nat.Partition (n + 1)) (h : 1 ∉ P.parts) :
    (decrMin P h).parts = (minPart P - 1) ::ₘ P.parts.erase (minPart P) := rfl

def allOnes (n : ℕ) : Nat.Partition n where
  parts := Multiset.replicate n 1
  parts_pos := by
    intro i hi
    rw [Multiset.eq_of_mem_replicate hi]
    exact Nat.one_pos
  parts_sum := by simp

def stepMap {n : ℕ} (P : Nat.Partition (n + 1)) : Nat.Partition n × Bool :=
  if h : 1 ∈ P.parts then (removeOne P h, true) else (decrMin P h, false)

lemma decrMin_lower {n : ℕ} (P : Nat.Partition (n + 1)) :
    ∀ x ∈ (minPart P - 1) ::ₘ P.parts.erase (minPart P), minPart P - 1 ≤ x := by
  intro x hx
  rcases Multiset.mem_cons.1 hx with rfl | hx'
  · exact le_rfl
  · have := minPart_le P (Multiset.mem_of_mem_erase hx')
    omega

lemma stepMap_inj (n : ℕ) : Function.Injective (@stepMap n) := by
  intro P Q hPQ
  unfold stepMap at hPQ
  by_cases hP : 1 ∈ P.parts
  · by_cases hQ : 1 ∈ Q.parts
    · rw [dif_pos hP, dif_pos hQ] at hPQ
      have e : (removeOne P hP).parts = (removeOne Q hQ).parts := congrArg (fun x => x.1.parts) hPQ
      change P.parts.erase 1 = Q.parts.erase 1 at e
      apply Nat.Partition.ext
      calc P.parts = 1 ::ₘ P.parts.erase 1 := (Multiset.cons_erase hP).symm
        _ = 1 ::ₘ Q.parts.erase 1 := by rw [e]
        _ = Q.parts := Multiset.cons_erase hQ
    · rw [dif_pos hP, dif_neg hQ] at hPQ
      simp at hPQ
  · by_cases hQ : 1 ∈ Q.parts
    · rw [dif_neg hP, dif_pos hQ] at hPQ
      simp at hPQ
    · rw [dif_neg hP, dif_neg hQ] at hPQ
      have e : (decrMin P hP).parts = (decrMin Q hQ).parts := congrArg (fun x => x.1.parts) hPQ
      rw [decrMin_parts, decrMin_parts] at e
      have h1 : minPart P - 1 ≤ minPart Q - 1 :=
        decrMin_lower P _ (by rw [e]; exact Multiset.mem_cons.2 (Or.inl rfl))
      have h2 : minPart Q - 1 ≤ minPart P - 1 :=
        decrMin_lower Q _ (by rw [← e]; exact Multiset.mem_cons.2 (Or.inl rfl))
      have hp1 := P.parts_pos (minPart_mem P)
      have hq1 := Q.parts_pos (minPart_mem Q)
      have heq : minPart P = minPart Q := by omega
      rw [heq] at e
      have e2 : P.parts.erase (minPart Q) = Q.parts.erase (minPart Q) :=
        (Multiset.cons_inj_right _).1 e
      apply Nat.Partition.ext
      calc P.parts = minPart P ::ₘ P.parts.erase (minPart P) := (Multiset.cons_erase (minPart_mem P)).symm
        _ = minPart Q ::ₘ Q.parts.erase (minPart Q) := by rw [heq, e2]
        _ = Q.parts := Multiset.cons_erase (minPart_mem Q)

lemma stepMap_not_surj (n : ℕ) (hn : 2 ≤ n) : ¬ Function.Surjective (@stepMap n) := by
  intro hs
  obtain ⟨P, hP⟩ := hs (allOnes n, false)
  unfold stepMap at hP
  by_cases h : 1 ∈ P.parts
  · rw [dif_pos h] at hP
    simp at hP
  · rw [dif_neg h] at hP
    have e : (decrMin P h).parts = (allOnes n).parts := congrArg (fun x => x.1.parts) hP
    rw [decrMin_parts] at e
    change _ = Multiset.replicate n 1 at e
    have hz : P.parts.erase (minPart P) = 0 := by
      apply Multiset.eq_zero_of_forall_notMem
      intro x hx
      have hx2 : x ∈ Multiset.replicate n 1 := by
        rw [← e]
        exact Multiset.mem_cons_of_mem hx
      have hx1 := Multiset.eq_of_mem_replicate hx2
      subst hx1
      exact h (Multiset.mem_of_mem_erase hx)
    rw [hz] at e
    have hc := congrArg Multiset.card e
    simp only [Multiset.card_cons, Multiset.card_zero, Multiset.card_replicate] at hc
    omega

lemma s_succ_le (m : ℕ) : s (m + 1) ≤ 2 * s m := by
  have h := Fintype.card_le_of_injective (@stepMap m) (stepMap_inj m)
  rw [Fintype.card_prod, Fintype.card_bool] at h
  show Fintype.card (Nat.Partition (m + 1)) ≤ 2 * Fintype.card (Nat.Partition m)
  omega

lemma s_succ_lt (m : ℕ) (hm : 2 ≤ m) : s (m + 1) < 2 * s m := by
  have h := Fintype.card_lt_of_injective_not_surjective (@stepMap m) (stepMap_inj m)
    (stepMap_not_surj m hm)
  rw [Fintype.card_prod, Fintype.card_bool] at h
  show Fintype.card (Nat.Partition (m + 1)) < 2 * Fintype.card (Nat.Partition m)
  omega

def revList (k : ℕ) : List ℕ := ((List.range k).map (· + 1)).reverse

lemma revList_succ (k : ℕ) : revList (k + 1) = (k + 1) :: revList k := by
  simp [revList, List.range_succ]

lemma key (k : ℕ) : ∀ r, r < s (k + 1) → List.foldl greedyStep r (revList k) = 0 := by
  induction k with
  | zero =>
    intro r hr
    have h1 : s (0 + 1) = 1 := by
      show Fintype.card (Nat.Partition 1) = 1
      exact Fintype.card_unique
    rw [h1] at hr
    have hr0 : r = 0 := by omega
    subst hr0
    rfl
  | succ k ih =>
    intro r hr
    rw [revList_succ, List.foldl_cons]
    apply ih
    have h2 := s_succ_le (k + 1)
    unfold greedyStep
    split_ifs with h <;> omega

end A242258Proof

open OMA.S_oeis_a242258 A242258Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a242258.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hk : k + 2 - 1 = k + 1 := by omega
  unfold greedyResidue
  rw [hk]
  change List.foldl greedyStep (s (k + 2)) (revList (k + 1)) = 0
  rw [revList_succ, List.foldl_cons]
  apply key
  have h3 : s (k + 2) < 2 * s (k + 1) := s_succ_lt (k + 1) (by omega)
  unfold greedyStep
  split_ifs with h <;> omega

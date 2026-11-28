import OMAStatements.S_oeis_a237666
import Mathlib.Tactic

open OMA.S_oeis_a237666 Finset

namespace PartitionConjugation

private def transpose {n : ℕ} (p : Code n) : Code n :=
  ⟨p.1, fun i => (p.2 i.rev).swap⟩

private lemma twice {n : ℕ} (p : Code n) : transpose (transpose p) = p := by
  rcases p with ⟨k, u⟩
  simp [transpose]

private lemma rev_sum {k : ℕ} (f : Fin k → ℕ) :
    (∑ i : Fin k, f i.rev) = ∑ i : Fin k, f i :=
  Equiv.sum_comp Fin.revPerm f

private lemma weight_transpose {n : ℕ} (p : Code n) : weight (transpose p) = weight p := by
  rcases p with ⟨k, u⟩
  let f (i j : Fin k.val) :=
    if i ≤ j then ((u i).1.val + 1) * ((u j).2.val + 1) else 0
  calc
    weight (transpose ⟨k, u⟩) = ∑ i : Fin k.val, ∑ j : Fin k.val, f j.rev i.rev := by
      change (∑ i : Fin k.val, ∑ j : Fin k.val,
        if i ≤ j then ((u i.rev).2.val + 1) * ((u j.rev).1.val + 1) else 0) = _
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      simp [f, Nat.mul_comm]
    _ = ∑ j : Fin k.val, ∑ i : Fin k.val, f j.rev i.rev := sum_comm
    _ = ∑ j : Fin k.val, ∑ i : Fin k.val, f j i := by
      simp_rw [rev_sum]
      exact rev_sum (fun j => ∑ i, f j i)
    _ = weight ⟨k, u⟩ := rfl

private lemma repeats_transpose {n : ℕ} (p : Code n) :
    repeats (transpose p) ↔ ¬ hasConsecutive p := by
  rcases p with ⟨k,u⟩
  change (∀ i : Fin k.val, i.val+1 < k.val → 0 < (u i.rev).1.val) ↔
    ¬ ∃ i : Fin k.val, 0 < i.val ∧ (u i).1.val = 0
  constructor
  · intro h
    rintro ⟨i, hi, hz⟩
    have hp := h i.rev (by rw [Fin.val_rev]; omega)
    simp [hz] at hp
  · intro h i hi
    by_contra! hz
    apply h
    refine ⟨i.rev, ?_, by omega⟩
    rw [Fin.val_rev]
    omega

private lemma part_transpose {n : ℕ} (p : Code n) :
    transpose p ∈ partitions n ↔ p ∈ partitions n := by
  classical
  simp [partitions, weight_transpose]

end PartitionConjugation

open PartitionConjugation

theorem OMA.solution : type_of% @OMA.S_oeis_a237666.main := by
  classical
  intro n _
  have complement :
      ((partitions n).filter fun p => ¬ hasConsecutive p).card =
      ((partitions n).filter repeats).card := by
    apply card_bij (fun p _ => transpose p)
    · intro p hp
      obtain ⟨hpart, hno⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨(part_transpose p).2 hpart, (repeats_transpose p).2 hno⟩
    · intro p _ q _ heq
      simpa only [twice] using congrArg transpose heq
    · intro q hq
      obtain ⟨hpart, hrep⟩ := mem_filter.mp hq
      refine ⟨transpose q, mem_filter.mpr ⟨(part_transpose q).2 hpart, ?_⟩, twice q⟩
      apply (repeats_transpose (transpose q)).1
      simpa only [twice] using hrep
  have split := card_filter_add_card_filter_not (s := partitions n) hasConsecutive
  unfold countWith
  omega

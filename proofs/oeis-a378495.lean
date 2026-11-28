import OMAStatements.S_oeis_a378495
import Mathlib

/-!
# OEIS A378495: 2*(T(n,n-2) - T(n,n)) = (n-3)!*(n-4)*(n-1) for n >= 5, where T(n,k) counts derangements with no k-cycle

Credit: @Squee451. The proof was found with Claude (claude-fable-5-2) and Codex; the Lean text was
written by Codex.

Outline. Let D be the number of derangements. (1) A derangement with an n-cycle is an n-cycle, and there are
(n-1)! of them, so T(n,n) = D - (n-1)!. (2) Since n-2 > n/2, a permutation has at most one
(n-2)-cycle; a derangement with one consists of that cycle and a transposition on the two remaining
points: binomial(n,2)*(n-3)! permutations, so T(n,n-2) = D - binomial(n,2)*(n-3)!. (3) Subtract:
(n-1)! - binomial(n,2)*(n-3)! = (n-3)!*((n-1)(n-2) - n(n-1)/2) = (n-3)!*(n-4)*(n-1)/2.
-/

open OMA.S_oeis_a378495

namespace OMA.A378495Proof

lemma sum_cycleType_eq_iff {n : ℕ} (p : Equiv.Perm (Fin n)) :
    p.cycleType.sum = n ↔ ∀ i, p i ≠ i := by
  rw [Equiv.Perm.sum_cycleType]
  simpa only [Fintype.card_fin, Finset.eq_univ_iff_forall, Equiv.Perm.mem_support]
    using Finset.card_eq_iff_eq_univ p.support

lemma multiset_eq_zero {s : Multiset ℕ} (hs : s.sum = 0)
    (hparts : ∀ a ∈ s, 2 ≤ a) : s = 0 := by
  by_contra h
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero h
  have := hparts a ha
  have := Multiset.sum_eq_zero_iff.mp hs a ha
  omega

lemma multiset_eq_two {s : Multiset ℕ} (hs : s.sum = 2)
    (hparts : ∀ a ∈ s, 2 ≤ a) : s = {2} := by
  have hn : s ≠ 0 := by intro h; simp [h] at hs
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hn
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem ha
  have ha2 : 2 ≤ a := hparts a (by simp)
  have ht : t.sum = 0 := by simp only [Multiset.sum_cons] at hs; omega
  have ht0 : t = 0 := multiset_eq_zero ht (fun b hb => hparts b (by simp [hb]))
  subst t
  simpa using hs

lemma full_cycle_iff {n : ℕ} (p : Equiv.Perm (Fin n)) :
    ((∀ i, p i ≠ i) ∧ n ∈ p.cycleType) ↔ p.cycleType = {n} := by
  constructor
  · rintro ⟨hd, hm⟩
    have hs := (sum_cycleType_eq_iff p).mpr hd
    obtain ⟨s, he⟩ := Multiset.exists_cons_of_mem hm
    have hz : s.sum = 0 := by rw [he, Multiset.sum_cons] at hs; omega
    have hzero : s = 0 := multiset_eq_zero hz (by
      intro a ha
      apply Equiv.Perm.two_le_of_mem_cycleType (σ := p)
      rw [he]
      simp [ha])
    simpa [hzero] using he
  · intro h
    refine ⟨(sum_cycleType_eq_iff p).mp ?_, ?_⟩ <;> simp [h]

lemma almost_full_cycle_iff (m : ℕ) (p : Equiv.Perm (Fin (m + 5))) :
    ((∀ i, p i ≠ i) ∧ m + 3 ∈ p.cycleType) ↔ p.cycleType = {m + 3, 2} := by
  constructor
  · rintro ⟨hd, hm⟩
    have hs := (sum_cycleType_eq_iff p).mpr hd
    obtain ⟨s, he⟩ := Multiset.exists_cons_of_mem hm
    have htwo : s.sum = 2 := by rw [he, Multiset.sum_cons] at hs; omega
    have hs2 : s = {2} := multiset_eq_two htwo (by
      intro a ha
      apply Equiv.Perm.two_le_of_mem_cycleType (σ := p)
      rw [he]
      simp [ha])
    simpa [hs2] using he
  · intro h
    refine ⟨(sum_cycleType_eq_iff p).mp ?_, ?_⟩ <;> simp [h, Nat.add_assoc]

def cycleCount (n : ℕ) (s : Multiset ℕ) : ℕ :=
  (Finset.univ.filter fun p : Equiv.Perm (Fin n) => p.cycleType = s).card

def derangementCount (n : ℕ) : ℕ :=
  (Finset.univ.filter fun p : Equiv.Perm (Fin n) => ∀ i, p i ≠ i).card

lemma count_partition (n k : ℕ) (s : Multiset ℕ)
    (hs : ∀ p : Equiv.Perm (Fin n),
      ((∀ i, p i ≠ i) ∧ k ∈ p.cycleType) ↔ p.cycleType = s) :
    T n k + cycleCount n s = derangementCount n := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun p : Equiv.Perm (Fin n) => ∀ i, p i ≠ i)
    (fun p => k ∈ p.cycleType)
  simp only [Finset.filter_filter] at h
  simp_rw [hs] at h
  simpa [T, cycleCount, derangementCount, Nat.add_comm] using h

lemma full_cycle_count (m : ℕ) :
    cycleCount (m + 5) {m + 5} = (m + 4).factorial := by
  have h := Equiv.Perm.card_of_cycleType_singleton
    (α := Fin (m + 5)) (n := m + 5) (by omega) (by simp)
  simpa [cycleCount] using h

lemma almost_full_cycle_count_mul (m : ℕ) :
    cycleCount (m + 5) {m + 3, 2} * ((m + 3) * 2) = (m + 5).factorial := by
  have h := Equiv.Perm.card_of_cycleType_mul_eq (Fin (m + 5)) {m + 3, 2}
  have hne : m + 3 ≠ 2 := by omega
  have hge : 2 ≤ m + 3 := by omega
  simpa [cycleCount, hne, Ne.symm hne, hge, Nat.add_assoc] using h

lemma almost_full_cycle_count_twice (m : ℕ) :
    2 * cycleCount (m + 5) {m + 3, 2} =
      (m + 5) * (m + 4) * (m + 2).factorial := by
  apply Nat.mul_left_cancel (by omega : 0 < m + 3)
  calc
    (m + 3) * (2 * cycleCount (m + 5) {m + 3, 2}) =
        cycleCount (m + 5) {m + 3, 2} * ((m + 3) * 2) := by ring
    _ = (m + 5).factorial := almost_full_cycle_count_mul m
    _ = (m + 3) * ((m + 5) * (m + 4) * (m + 2).factorial) := by
      rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
      ring

lemma factorial_expand (m : ℕ) :
    (m + 4).factorial = (m + 4) * (m + 3) * (m + 2).factorial := by
  rw [Nat.factorial_succ, Nat.factorial_succ]
  ring

end OMA.A378495Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a378495.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have hfull := OMA.A378495Proof.count_partition (m + 5) (m + 5) {m + 5}
    (fun p => OMA.A378495Proof.full_cycle_iff p)
  have hpart := OMA.A378495Proof.count_partition (m + 5) (m + 3) {m + 3, 2}
    (OMA.A378495Proof.almost_full_cycle_iff m)
  rw [OMA.A378495Proof.full_cycle_count] at hfull
  have htwice := OMA.A378495Proof.almost_full_cycle_count_twice m
  have hfactor := OMA.A378495Proof.factorial_expand m
  have hfullZ := congrArg (fun a : ℕ => (a : ℤ)) hfull
  have hpartZ := congrArg (fun a : ℕ => (a : ℤ)) hpart
  have htwiceZ := congrArg (fun a : ℕ => (a : ℤ)) htwice
  have hfactorZ := congrArg (fun a : ℕ => (a : ℤ)) hfactor
  push_cast at hfullZ hpartZ htwiceZ hfactorZ
  have hsub2 : m + 5 - 2 = m + 3 := by omega
  have hsub3 : m + 5 - 3 = m + 2 := by omega
  rw [hsub2, hsub3]
  push_cast
  nlinarith [hfullZ, hpartZ, htwiceZ, hfactorZ]

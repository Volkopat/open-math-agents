import OMAStatements.S_oeis_a039671
import Mathlib

-- Problem: A039671: Row sums up to the main diagonal of the "postage stamp" array (n,m) defined in A007059.
-- Upstream: formal-conjectures statements/oeis-a039671.lean:0 (declaration OMA.S_oeis_a039671.main)
-- Credit: @npnelson (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Proof. Let S k n be the finite set of lists of integers in [1, k] with sum n, built by the
-- same recursion as the array: a list of sum n + 1 is (j + 1) :: t with j < min (n + 1) k and t
-- of sum n - j. Then S k n has postage k n elements, and the blocks of a composition give a
-- bijection between compositions of n with parts at most k and S k n. Finally postage 0 n = 0
-- for n > 0, so the two sums agree term by term.

namespace Postage039671Proof
open OMA.S_oeis_a039671 Finset

def S (k : ℕ) : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | n+1 => (Finset.univ : Finset (Fin (min (n+1) k))).biUnion
      fun j => (S k (n - j.val)).image (List.cons (j.val + 1))
termination_by n => n
decreasing_by omega

lemma S_zero (k : ℕ) : S k 0 = {[]} := by rw [S]

lemma S_succ (k n : ℕ) : S k (n+1) = (Finset.univ : Finset (Fin (min (n+1) k))).biUnion
    fun j => (S k (n - j.val)).image (List.cons (j.val + 1)) := by rw [S]

lemma postage_zero (k : ℕ) : postage k 0 = 1 := by rw [postage]

lemma postage_succ (k n : ℕ) :
    postage k (n+1) = ∑ j : Fin (min (n+1) k), postage k (n - j.val) := by rw [postage]

lemma card_S (k : ℕ) : ∀ n, (S k n).card = postage k n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => rw [S_zero, postage_zero]; simp
    | succ m =>
      rw [S_succ, postage_succ, Finset.card_biUnion]
      · apply Finset.sum_congr rfl
        intro j _
        rw [Finset.card_image_of_injective _ (List.cons_injective), ih (m - j.val) (by omega)]
      · intro i _ j _ hij
        rw [Function.onFun, Finset.disjoint_left]
        intro l hl hl'
        rw [Finset.mem_image] at hl hl'
        obtain ⟨t, _, rfl⟩ := hl
        obtain ⟨t', _, h⟩ := hl'
        have h1 := (List.cons.inj h).1
        exact hij (Fin.ext (by omega))

lemma mem_S (k : ℕ) : ∀ n (l : List ℕ),
    l ∈ S k n ↔ (∀ a ∈ l, 0 < a ∧ a ≤ k) ∧ l.sum = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l
    cases n with
    | zero =>
      rw [S_zero, Finset.mem_singleton]
      constructor
      · rintro rfl
        simp
      · rintro ⟨h1, h2⟩
        cases l with
        | nil => rfl
        | cons b t =>
          have hb := (h1 b (by simp)).1
          rw [List.sum_cons] at h2
          omega
    | succ m =>
      rw [S_succ, Finset.mem_biUnion]
      constructor
      · rintro ⟨j, _, hl⟩
        rw [Finset.mem_image] at hl
        obtain ⟨t, ht, rfl⟩ := hl
        obtain ⟨h1, h2⟩ := (ih (m - j.val) (by omega) t).mp ht
        have hj := lt_min_iff.mp j.isLt
        refine ⟨?_, ?_⟩
        · intro a ha
          rw [List.mem_cons] at ha
          rcases ha with rfl | ha
          · omega
          · exact h1 a ha
        · rw [List.sum_cons, h2]
          omega
      · rintro ⟨h1, h2⟩
        cases l with
        | nil => simp at h2
        | cons b t =>
          have hb := h1 b (by simp)
          rw [List.sum_cons] at h2
          have hlt : b - 1 < min (m+1) k := lt_min_iff.mpr ⟨by omega, by omega⟩
          refine ⟨⟨b - 1, hlt⟩, Finset.mem_univ _, ?_⟩
          rw [Finset.mem_image]
          refine ⟨t, (ih (m - (b - 1)) (by omega) t).mpr
            ⟨fun a ha => h1 a (List.mem_cons_of_mem _ ha), by omega⟩, ?_⟩
          show (b - 1 + 1) :: t = b :: t
          rw [Nat.sub_add_cancel hb.1]

lemma card_bounded (n k : ℕ) : Nat.card (Bounded n k) = (S k n).card := by
  rw [← Nat.card_eq_finsetCard (S k n)]
  apply Nat.card_congr
  exact
    { toFun := fun c => ⟨c.1.blocks,
        (mem_S k n _).mpr ⟨fun a ha => ⟨c.1.blocks_pos ha, c.2 a ha⟩, c.1.blocks_sum⟩⟩
      invFun := fun l =>
        ⟨⟨l.1, fun {i} hi => (((mem_S k n _).mp l.2).1 i hi).1, ((mem_S k n _).mp l.2).2⟩,
          fun a ha => (((mem_S k n _).mp l.2).1 a ha).2⟩
      left_inv := fun c => rfl
      right_inv := fun l => rfl }

end Postage039671Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a039671.main := by
  intro n hn
  rw [Finset.sum_range_succ']
  have h0 : OMA.S_oeis_a039671.postage 0 n = 0 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Postage039671Proof.postage_succ]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    have hj := lt_min_iff.mp j.isLt
    omega
  rw [h0, add_zero]
  apply Finset.sum_congr rfl
  intro j _
  rw [Postage039671Proof.card_bounded, Postage039671Proof.card_S]

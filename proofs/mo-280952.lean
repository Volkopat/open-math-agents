import OMAStatements.S_mo_280952

/-!
# mo-280952: for a convex game, the core of the quotient game is the image of the core

The result is known: Ron Peretz answered the MathOverflow question in 2017 using Shapley's
theorem that the extreme points of the core of a convex game are its marginal vectors
(L. S. Shapley, Cores of convex games, 1971). The proof below is elementary and does not use
that theorem: players are released from their unions one at a time, and each release moves
an amount `t` between two members of one union; supermodularity shows a suitable `t` exists.
-/

namespace CoreQ

open Finset OMA.S_mo_280952

/-- Summing union totals over a set of unions is summing over the players of those unions. -/
lemma sum_blocks {N M : Type*} [Fintype N] [DecidableEq M] (b : N → M) (x : N → ℝ)
    (T : Finset M) :
    ∑ k ∈ T, ∑ i with b i = k, x i = ∑ i with b i ∈ T, x i := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

/-- Finitely many lower bounds, each below every upper bound, leave room for a number. -/
lemma exists_between {ι : Type*} [Fintype ι] (P Q : ι → Prop) (lo hi : ι → ℝ)
    (h : ∀ s s', P s → Q s' → lo s ≤ hi s') (hP : ∃ s, P s) :
    ∃ t, (∀ s, P s → lo s ≤ t) ∧ (∀ s, Q s → t ≤ hi s) := by
  classical
  obtain ⟨s0, hs0⟩ := hP
  have hne : (Finset.univ.filter P).Nonempty := ⟨s0, by simp [hs0]⟩
  refine ⟨(Finset.univ.filter P).sup' hne lo, ?_, ?_⟩
  · intro s hs
    exact Finset.le_sup' lo (by simp [hs])
  · intro s' hs'
    apply Finset.sup'_le
    intro s hs
    exact h s s' (by simpa using hs) hs'

/-- `S` treats the not yet released players (those outside `A`) of each union as one lump:
it contains all of them or none. -/
def Adm {N M : Type*} (b : N → M) (A S : Finset N) : Prop :=
  ∀ j j', b j = b j' → j ∉ A → j' ∉ A → j ∈ S → j' ∈ S

/-- Releasing the players one at a time. -/
lemma lift_step {N M : Type*} [Fintype N] [DecidableEq N] [Fintype M] [DecidableEq M]
    (v : Finset N → ℝ) (hconv : IsConvexGame v) (b : N → M) (hb : Function.Surjective b)
    (y : M → ℝ) (hy : y ∈ core (quotientGame v b)) (A : Finset N) :
    ∃ x : N → ℝ, (∀ k, ∑ i with b i = k, x i = y k) ∧
      ∀ S, Adm b A S → v S ≤ ∑ i ∈ S, x i := by
  refine Finset.induction_on A ?_ ?_
  · -- nothing released: split each union's total equally
    have hsum : ∀ k, ∑ i with b i = k,
        y (b i) / ((univ.filter fun j => b j = b i).card : ℝ) = y k := by
      intro k
      have h1 : ∀ i ∈ univ.filter (fun i => b i = k),
          y (b i) / ((univ.filter fun j => b j = b i).card : ℝ)
            = y k / ((univ.filter fun j => b j = k).card : ℝ) := by
        intro i hi
        have hk : b i = k := (Finset.mem_filter.mp hi).2
        subst hk
        rfl
      rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
      have hpos : ((univ.filter fun j => b j = k).card : ℝ) ≠ 0 := by
        obtain ⟨i, hi⟩ := hb k
        have hne : (univ.filter fun j => b j = k).Nonempty := ⟨i, by simp [hi]⟩
        exact_mod_cast hne.card_pos.ne'
      field_simp
    refine ⟨fun i => y (b i) / ((univ.filter fun j => b j = b i).card : ℝ), hsum, ?_⟩
    intro S hS
    have hSeq : S = univ.filter (fun i => b i ∈ S.image b) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hj
        exact ⟨j, hj, rfl⟩
      · rintro ⟨j', hj', hbj⟩
        exact hS j' j hbj (by simp) (by simp) hj'
    have h2 := hy.2 (S.image b)
    have h3 := sum_blocks b (fun i => y (b i) / ((univ.filter fun j => b j = b i).card : ℝ))
      (S.image b)
    simp only [hsum] at h3
    unfold quotientGame at h2
    rw [← hSeq] at h2 h3
    linarith
  · intro i A hiA ih
    obtain ⟨x, hx1, hx2⟩ := ih
    by_cases hj : ∃ j0, j0 ∉ A ∧ j0 ≠ i ∧ b j0 = b i
    · obtain ⟨j0, hj0A, hj0i, hbj0⟩ := hj
      have hj0' : j0 ∉ insert i A := by simp [hj0i, hj0A]
      have hstep : ∀ j, j ∉ A → j ≠ i → j ∉ insert i A := by
        intro j h1 h2
        simp [h1, h2]
      obtain ⟨t, ht1, ht2⟩ := exists_between
        (fun S : Finset N => Adm b (insert i A) S ∧ i ∈ S ∧ j0 ∉ S)
        (fun S : Finset N => Adm b (insert i A) S ∧ i ∉ S ∧ j0 ∈ S)
        (fun S => v S - ∑ j ∈ S, x j) (fun S => ∑ j ∈ S, x j - v S)
        (by
          rintro S S' ⟨hS, hiS, hjS⟩ ⟨hS', hiS', hjS'⟩
          have hU : Adm b A (S ∪ S') := by
            intro j j' hbj hjA hj'A hjm
            by_cases e' : j' = i
            · subst e'
              exact Finset.mem_union_left _ hiS
            · by_cases e : j = i
              · subst e
                exact Finset.mem_union_right _
                  (hS' j0 j' (hbj0.trans hbj) hj0' (hstep j' hj'A e') hjS')
              · rcases Finset.mem_union.mp hjm with h | h
                · exact Finset.mem_union_left _
                    (hS j j' hbj (hstep j hjA e) (hstep j' hj'A e') h)
                · exact Finset.mem_union_right _
                    (hS' j j' hbj (hstep j hjA e) (hstep j' hj'A e') h)
          have hI : Adm b A (S ∩ S') := by
            intro j j' hbj hjA hj'A hjm
            obtain ⟨hjS1, hjS2⟩ := Finset.mem_inter.mp hjm
            have e : j ≠ i := by
              rintro rfl
              exact hiS' hjS2
            by_cases e' : j' = i
            · subst e'
              exact absurd (hS j j0 (hbj.trans hbj0.symm) (hstep j hjA e) hj0' hjS1) hjS
            · exact Finset.mem_inter.mpr
                ⟨hS j j' hbj (hstep j hjA e) (hstep j' hj'A e') hjS1,
                  hS' j j' hbj (hstep j hjA e) (hstep j' hj'A e') hjS2⟩
          have h1 := hx2 _ hU
          have h2 := hx2 _ hI
          have h3 := hconv S S'
          have h4 := Finset.sum_union_inter (s₁ := S) (s₂ := S') (f := x)
          linarith)
        ⟨{i}, by
          intro j j' _ hjA _ hjm
          rw [Finset.mem_singleton] at hjm
          subst hjm
          exact absurd (Finset.mem_insert_self _ _) hjA,
          by simp, by simp [hj0i]⟩
      refine ⟨fun j => x j + (if j = i then t else 0) - (if j = j0 then t else 0), ?_, ?_⟩
      · intro k
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hx1 k]
        simp [hbj0]
      · intro S hS
        have hsum : ∑ j ∈ S, (x j + (if j = i then t else 0) - (if j = j0 then t else 0))
            = ∑ j ∈ S, x j + (if i ∈ S then t else 0) - (if j0 ∈ S then t else 0) := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
          simp
        rw [hsum]
        by_cases hiS : i ∈ S <;> by_cases hjS : j0 ∈ S
        · -- both in: `S` was already admissible
          have hadm : Adm b A S := by
            intro j j' hbj hjA hj'A hjm
            by_cases e' : j' = i
            · subst e'
              exact hiS
            · by_cases e : j = i
              · subst e
                exact hS j0 j' (hbj0.trans hbj) hj0' (hstep j' hj'A e') hjS
              · exact hS j j' hbj (hstep j hjA e) (hstep j' hj'A e') hjm
          have := hx2 S hadm
          simp only [hiS, hjS, if_true]
          linarith
        · have := ht1 S ⟨hS, hiS, hjS⟩
          simp only [hiS, hjS, if_true, if_false]
          linarith
        · have := ht2 S ⟨hS, hiS, hjS⟩
          simp only [hiS, hjS, if_true, if_false]
          linarith
        · -- neither in: `S` was already admissible
          have hadm : Adm b A S := by
            intro j j' hbj hjA hj'A hjm
            have e : j ≠ i := by
              rintro rfl
              exact hiS hjm
            by_cases e' : j' = i
            · subst e'
              exact absurd (hS j j0 (hbj.trans hbj0.symm) (hstep j hjA e) hj0' hjm) hjS
            · exact hS j j' hbj (hstep j hjA e) (hstep j' hj'A e') hjm
          have := hx2 S hadm
          simp only [hiS, hjS, if_false]
          linarith
    · -- `i` was the last unreleased player of its union: nothing changes
      refine ⟨x, hx1, ?_⟩
      intro S hS
      apply hx2 S
      intro j j' hbj hjA hj'A hjm
      by_cases e' : j' = i
      · by_cases e : j = i
        · rw [e'] ; rw [e] at hjm ; exact hjm
        · exact absurd ⟨j, hjA, e, by rw [hbj, e']⟩ hj
      · by_cases e : j = i
        · exact absurd ⟨j', hj'A, e', by rw [← hbj, e]⟩ hj
        · exact hS j j' hbj (by simp [hjA, e]) (by simp [hj'A, e']) hjm

theorem core_quotient_eq {N M : Type*} [Fintype N] [DecidableEq N] [Fintype M] [DecidableEq M]
    (v : Finset N → ℝ) (hv0 : v ∅ = 0) (hconv : IsConvexGame v)
    (b : N → M) (hb : Function.Surjective b) :
    core (quotientGame v b) = unionTotals b '' core v := by
  apply Set.eq_of_subset_of_subset
  · -- every core allocation of the quotient game lifts
    intro y hy
    obtain ⟨x, hx1, hx2⟩ := lift_step v hconv b hb y hy univ
    refine ⟨x, ⟨?_, ?_⟩, ?_⟩
    · have h := sum_blocks b x univ
      simp only [hx1, Finset.mem_univ, Finset.filter_true] at h
      have h' := hy.1
      unfold quotientGame at h'
      simp only [Finset.mem_univ, Finset.filter_true] at h'
      linarith
    · intro S
      exact hx2 S (fun j _ _ hjA => absurd (Finset.mem_univ j) hjA)
    · funext k
      exact hx1 k
  · -- the easy inclusion
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · have h := sum_blocks b x univ
      simp only [Finset.mem_univ, Finset.filter_true] at h
      unfold unionTotals quotientGame
      simp only [Finset.mem_univ, Finset.filter_true]
      rw [h]
      exact hx.1
    · intro T
      unfold unionTotals quotientGame
      rw [sum_blocks b x T]
      exact hx.2 _

end CoreQ

theorem OMA.solution : type_of% @OMA.S_mo_280952.main := by
  intro N M _ _ _ _ v hv0 hconv b hb
  exact CoreQ.core_quotient_eq v hv0 hconv b hb

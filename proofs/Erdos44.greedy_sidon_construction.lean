import FormalConjectures.ErdosProblems.«44»
open Finset

-- Problem: Erdős Problem 44: Extending Sidon Sets — greedy sidon construction
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/44.lean:138 (declaration Erdos44.greedy_sidon_construction)
-- Credit: @Rahul-007afk (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-- If `A` is Sidon, `x ∉ A`, and adding `x` destroys the Sidon property, then `x` is pinned down
by elements of `A`: either `x + a = b + c` with `a ≠ b`, or `2 * x = b + c` with `b ≠ c`. -/
lemma OMA.sidon_blocked {A : Finset ℕ} (hA : IsSidon (A : Set ℕ)) {x : ℕ} (hx : x ∉ A)
    (hins : ¬ IsSidon ((insert x A : Finset ℕ) : Set ℕ)) :
    (∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a ≠ b ∧ x + a = b + c) ∨
      (∃ b ∈ A, ∃ c ∈ A, b ≠ c ∧ 2 * x = b + c) := by
  let P : Prop :=
    (∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a ≠ b ∧ x + a = b + c) ∨
      (∃ b ∈ A, ∃ c ∈ A, b ≠ c ∧ 2 * x = b + c)
  change P
  have one : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, x + a = b + c → P := by
    intro a ha b hb c hc h
    by_cases hab : a = b
    · exact absurd ((show x = c by omega) ▸ hc) hx
    · exact Or.inl ⟨a, ha, b, hb, c, hc, hab, h⟩
  have two : ∀ b ∈ A, ∀ c ∈ A, 2 * x = b + c → P := by
    intro b hb c hc h
    by_cases hbc : b = c
    · exact absurd ((show x = b by omega) ▸ hb) hx
    · exact Or.inr ⟨b, hb, c, hc, hbc, h⟩
  have mem_abs : ∀ a ∈ A, a = x → False := fun a ha h => hx (h ▸ ha)
  unfold IsSidon at hins
  push_neg at hins
  obtain ⟨i1, hi1, j1, hj1, i2, hi2, j2, hj2, heq, hne1, hne2⟩ := hins
  simp only [Finset.coe_insert, Set.mem_insert_iff, mem_coe] at hi1 hj1 hi2 hj2
  rcases hi1 with e1 | m1 <;> rcases hj1 with e2 | m2 <;> rcases hi2 with e3 | m3 <;>
    rcases hj2 with e4 | m4
  · exfalso; omega
  · exact (mem_abs j2 m4 (by omega)).elim
  · exact (mem_abs i2 m3 (by omega)).elim
  · exfalso; omega
  · exact (mem_abs j1 m2 (by omega)).elim
  · exact two j1 m2 j2 m4 (by omega)
  · exfalso; omega
  · exact one i2 m3 j1 m2 j2 m4 (by omega)
  · exact (mem_abs i1 m1 (by omega)).elim
  · exfalso; omega
  · exact two i1 m1 i2 m3 (by omega)
  · exact one j2 m4 i1 m1 i2 m3 (by omega)
  · exfalso; omega
  · exact one i1 m1 j1 m2 j2 m4 (by omega)
  · exact one j1 m2 i1 m1 i2 m3 (by omega)
  · exfalso
    rcases hA i1 m1 j1 m2 i2 m3 j2 m4 heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hne1 h1 h2
    · exact hne2 h1 h2

/-- The map sending a triple of elements of a maximal Sidon set to the integer it blocks. -/
def OMA.blocked (t : ℕ × ℕ × ℕ) : ℕ :=
  if t.1 = t.2.1 then (if t.2.1 = t.2.2 then t.1 else (t.2.1 + t.2.2) / 2)
  else t.2.1 + t.2.2 - t.1

theorem OMA.solution : type_of% @Erdos44.greedy_sidon_construction := by
  intro N hN
  classical
  have hS : ((Finset.Icc 1 N).powerset.filter
      (fun A : Finset ℕ => IsSidon (A : Set ℕ))).Nonempty := by
    refine ⟨∅, ?_⟩
    simp [IsSidon]
  obtain ⟨A, hAS, hmax⟩ := exists_max_image _ Finset.card hS
  rw [mem_filter, mem_powerset] at hAS
  obtain ⟨hAsub, hAsid⟩ := hAS
  refine ⟨A, hAsub, hAsid, ?_⟩
  have hcover : Finset.Icc 1 N ⊆ (A ×ˢ A ×ˢ A).image OMA.blocked := by
    intro x hx
    rw [mem_image]
    by_cases hxA : x ∈ A
    · exact ⟨(x, x, x), by simp [hxA], by simp [OMA.blocked]⟩
    · have hins : ¬ IsSidon ((insert x A : Finset ℕ) : Set ℕ) := by
        intro hs
        have hmem : insert x A ∈ (Finset.Icc 1 N).powerset.filter
            (fun A : Finset ℕ => IsSidon (A : Set ℕ)) := by
          rw [mem_filter, mem_powerset]
          exact ⟨insert_subset hx hAsub, hs⟩
        have hle := hmax _ hmem
        rw [card_insert_of_notMem hxA] at hle
        omega
      rcases OMA.sidon_blocked hAsid hxA hins with
        ⟨a, ha, b, hb, c, hc, hab, h⟩ | ⟨b, hb, c, hc, hbc, h⟩
      · refine ⟨(a, b, c), by simp [ha, hb, hc], ?_⟩
        simp only [OMA.blocked, if_neg hab]
        omega
      · refine ⟨(b, b, c), by simp [hb, hc], ?_⟩
        simp only [OMA.blocked, if_true, if_neg hbc]
        omega
  calc N = (Finset.Icc 1 N).card := by simp
    _ ≤ ((A ×ˢ A ×ˢ A).image OMA.blocked).card := card_le_card hcover
    _ ≤ (A ×ˢ A ×ˢ A).card := card_image_le
    _ = A.card ^ 3 := by simp only [card_product]; ring

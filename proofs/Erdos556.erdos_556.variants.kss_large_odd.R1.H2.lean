import OMAReductions.R_Erdos556_erdos_556_variants_kss_large_odd_R1

-- Step Erdos556.erdos_556.variants.kss_large_odd.R1.H2: hypothesis H2 of reduction Erdos556.erdos_556.variants.kss_large_odd.R1
-- Credit: @Albin0903
-- H2 := ∀ᶠ n : ℕ in atTop, Odd n → 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3

/-!
# The five-point step `Erdos556.erdos_556.variants.kss_large_odd.R1.H2`

H2 asks, for all sufficiently large odd `n`,
`4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3`, i.e. the matched lower bound of the
Bondy-Erdos conjecture. This file isolates that lower bound as a step of the reduction
`R1`, which is the `odd_lower_bound` variant of Erdos Problem 556.

REUSE AND CREDIT. Nothing new is proved here: the two combinatorial lemmas below
(`oddCycleRamseySetNonempty`, the existence of a finite three-colour Ramsey witness, and
`oddCycleBadColoring`, the standard `Bool x Bool x Fin (n - 1)` blow-up colouring of the
complete graph on at most `4 * (n - 1)` vertices with no monochromatic odd `C_n`) are the
ones already formalised in the merged proof
`proofs/Erdos556.erdos_556.variants.odd_lower_bound.lean` of this repository. Only the
`atTop` packaging needed by the step `H2` is added.
-/

open SimpleGraph
open scoped SimpleGraph
open Filter

namespace OMA

lemma oddCycleRamseySetNonempty (n : ℕ) :
    {N : ℕ | ∀ c : Fin 3 → SimpleGraph (Fin N),
      (⊤ : SimpleGraph (Fin N)).IsEdgeColouring c →
        ∃ i, (cycleGraph n).IsContained (c i)}.Nonempty := by
  classical
  let M := Nat.choose (n + n) n
  let N := Nat.choose (M + n) M
  refine ⟨N, ?_⟩
  intro c hc
  let test (i : Fin 3) (S : Finset (Fin N)) : Bool :=
    decide (∀ a ∈ S, ∀ b ∈ S, a ≠ b → (c i).Adj a b)
  have test_pair (i : Fin 3) (a b : Fin N) (hab : a ≠ b) :
      test i {a, b} = true ↔ (c i).Adj a b := by
    simp only [test, decide_eq_true_eq]
    constructor
    · intro h
      exact h a (by simp) b (by simp) hab
    · intro h x hx y hy hxy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact (hxy rfl).elim
      · exact h
      · exact h.symm
      · exact (hxy rfl).elim
  have copy_of_clique (S : Finset (Fin N)) (hcard : S.card = n) (i : Fin 3)
      (h : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → (c i).Adj a b) :
      (cycleGraph n).IsContained (c i) := by
    let e := (Finset.equivFinOfCardEq hcard).symm
    let f : Fin n → Fin N := fun x => (e x).val
    have hf : Function.Injective f := Subtype.val_injective.comp e.injective
    refine ⟨⟨⟨f, ?_⟩, hf⟩⟩
    intro a b hab
    exact h (f a) (e a).property (f b) (e b).property (hf.ne hab.ne)
  have adjacency_exists (a b : Fin N) (hab : a ≠ b) : ∃ i, (c i).Adj a b := by
    apply iSup_adj.mp
    rw [← hc.1]
    exact (top_adj a b).mpr hab
  have pair_subset (S : Finset (Fin N)) {a b : Fin N} (ha : a ∈ S) (hb : b ∈ S) :
      {a, b} ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  rcases Combinatorics.Diagonal.hasRamseyProperty_choose M n (test 0) Finset.univ
      (by simp [N]) with ⟨S, _, hS, hSmono⟩ | ⟨S, _, hS, hSmono⟩
  · rcases Combinatorics.Diagonal.hasRamseyProperty_choose n n (test 1) S
        (by rw [hS]) with ⟨T, hTS, hT, hTmono⟩ | ⟨T, _, hT, hTmono⟩
    · refine ⟨2, copy_of_clique T hT 2 ?_⟩
      intro a ha b hb hab
      have hpair := Finset.card_pair_eq_two_iff.mpr hab
      have hzero : ¬ (c 0).Adj a b := by
        intro h
        have ht := (test_pair 0 a b hab).mpr h
        rw [hSmono _ (pair_subset S (hTS ha) (hTS hb)) hpair] at ht
        contradiction
      have hone : ¬ (c 1).Adj a b := by
        intro h
        have ht := (test_pair 1 a b hab).mpr h
        rw [hTmono _ (pair_subset T ha hb) hpair] at ht
        contradiction
      obtain ⟨i, hi⟩ := adjacency_exists a b hab
      fin_cases i
      · exact (hzero hi).elim
      · exact (hone hi).elim
      · exact hi
    · refine ⟨1, copy_of_clique T hT 1 ?_⟩
      intro a ha b hb hab
      exact (test_pair 1 a b hab).mp
        (hTmono _ (pair_subset T ha hb) (Finset.card_pair_eq_two_iff.mpr hab))
  · refine ⟨0, copy_of_clique S hS 0 ?_⟩
    intro a ha b hb hab
    exact (test_pair 0 a b hab).mp
      (hSmono _ (pair_subset S ha hb) (Finset.card_pair_eq_two_iff.mpr hab))

lemma oddCycleBadColoring (n N : ℕ) (hn : 3 ≤ n) (hodd : Odd n)
    (hN : N ≤ 4 * (n - 1)) :
    ∃ c : Fin 3 → SimpleGraph (Fin N),
      (⊤ : SimpleGraph (Fin N)).IsEdgeColouring c ∧
      ∀ i, ¬ (cycleGraph n).IsContained (c i) := by
  classical
  obtain ⟨e⟩ : Nonempty (Fin N ↪ Bool × Bool × Fin (n - 1)) :=
    Function.Embedding.nonempty_of_card_le (by simpa [Fintype.card_prod, ← mul_assoc] using hN)
  let color (x y : Fin N) : Fin 3 :=
    if (e x).1 = (e y).1 then
      if (e x).2.1 = (e y).2.1 then 2 else 1
    else 0
  have hsym (x y : Fin N) : color x y = color y x := by
    unfold color
    by_cases h₁ : (e x).1 = (e y).1
    · rw [if_pos h₁, if_pos h₁.symm]
      by_cases h₂ : (e x).2.1 = (e y).2.1
      · rw [if_pos h₂, if_pos h₂.symm]
      · rw [if_neg h₂, if_neg (Ne.symm h₂)]
    · rw [if_neg h₁, if_neg (Ne.symm h₁)]
  let c (i : Fin 3) : SimpleGraph (Fin N) :=
    { Adj := fun x y => x ≠ y ∧ color x y = i
      symm := ⟨fun x y h => ⟨h.1.symm, (hsym x y).symm.trans h.2⟩⟩
      loopless := ⟨fun _ h => h.1 rfl⟩ }
  refine ⟨c, ⟨?_, ?_⟩, ?_⟩
  · ext x y
    rw [top_adj, iSup_adj]
    constructor
    · intro h
      exact ⟨color x y, h, rfl⟩
    · rintro ⟨i, hi⟩
      exact hi.1
  · intro i j hij
    apply disjoint_iff_inf_le.mpr
    intro x y h
    exact (hij (h.1.2.symm.trans h.2.2)).elim
  · have twoColorImpossible (f : (cycleGraph n).Coloring Bool) : False := by
      have hle : (cycleGraph n).chromaticNumber ≤ 2 := by
        simpa using f.colorable.chromaticNumber_le
      rw [chromaticNumber_cycleGraph_of_odd n (by omega) hodd] at hle
      norm_num at hle
    intro i
    rintro ⟨f⟩
    have adjacency_color {a b : Fin n} (hab : (cycleGraph n).Adj a b) :
        color (f a) (f b) = i := (f.toHom.map_adj hab).2
    fin_cases i
    · apply twoColorImpossible
      apply Coloring.mk fun a => (e (f a)).1
      intro a b hab h
      have heq : color (f a) (f b) = 0 := adjacency_color hab
      dsimp [color] at heq
      by_cases h₂ : (e (f a)).2.1 = (e (f b)).2.1 <;> simp [h, h₂] at heq
    · apply twoColorImpossible
      apply Coloring.mk fun a => (e (f a)).2.1
      intro a b hab h
      have heq : color (f a) (f b) = 1 := adjacency_color hab
      dsimp [color] at heq
      by_cases h₁ : (e (f a)).1 = (e (f b)).1 <;> simp [h, h₁] at heq
    · let block (a : Fin n) := ((e (f a)).1, (e (f a)).2.1)
      have edge_block {a b : Fin n} (hab : (cycleGraph n).Adj a b) : block a = block b := by
        have heq : color (f a) (f b) = 2 := adjacency_color hab
        dsimp [color] at heq
        by_cases h₁ : (e (f a)).1 = (e (f b)).1
        · by_cases h₂ : (e (f a)).2.1 = (e (f b)).2.1
          · exact Prod.ext h₁ h₂
          · simp [h₁, h₂] at heq
        · simp [h₁] at heq
      have walk_block {a b : Fin n} (w : (cycleGraph n).Walk a b) : block a = block b := by
        induction w with
        | nil => rfl
        | cons h _ ih => exact (edge_block h).trans ih
      have block_const (a b : Fin n) : block a = block b := by
        obtain ⟨w⟩ := cycleGraph_preconnected a b
        exact walk_block w
      have hf : Function.Injective (fun a : Fin n => (e (f a)).2.2) := by
        intro a b hab
        apply f.injective
        apply e.injective
        have h₁ : (e (f a)).1 = (e (f b)).1 :=
          congrArg (fun t : Bool × Bool => t.1) (block_const a b)
        have h₂ : (e (f a)).2.1 = (e (f b)).2.1 :=
          congrArg (fun t : Bool × Bool => t.2) (block_const a b)
        exact Prod.ext h₁ (Prod.ext h₂ hab)
      have hcard := Fintype.card_le_of_injective _ hf
      simp only [Fintype.card_fin] at hcard
      omega


private lemma oddCycleLowerBound (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n) :
    4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3 := by
  let S : Set ℕ := {N : ℕ | ∀ c : Fin 3 → SimpleGraph (Fin N),
    (⊤ : SimpleGraph (Fin N)).IsEdgeColouring c →
      ∃ i, (cycleGraph n).IsContained (c i)}
  change 4 * n - 3 ≤ sInf S
  have hS : sInf S ∈ S := Nat.sInf_mem (oddCycleRamseySetNonempty n)
  by_contra h
  have hN : sInf S ≤ 4 * (n - 1) := by omega
  obtain ⟨c, hc, hno⟩ := oddCycleBadColoring n (sInf S) hn hodd hN
  obtain ⟨i, hi⟩ := hS c hc
  exact hno i hi

end OMA

theorem OMA.solution : OMA.R_Erdos556_erdos_556_variants_kss_large_odd_R1.H2 := by
  show ∀ᶠ n : ℕ in atTop, Odd n → 4 * n - 3 ≤ multicolourRamsey (cycleGraph n) 3
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn hodd
  exact OMA.oddCycleLowerBound n hn hodd

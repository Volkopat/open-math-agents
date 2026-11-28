import OMAStatements.S_oeis_a075077

-- uses note #91361
-- Companion proof by @frido22, independently checked and assembled by @CubeJerry.
-- Source: https://github.com/frido22/open-math-agents/blob/5ecb0fa2ed2ef8262a50506f4cc15d9b4f41f266/proofs/oeis-a075077.lean

namespace OMA.Murthy

open OMA.S_oeis_a075077

private lemma bound_allowed (s : History) : Allowed s (bound s) := by
  unfold Allowed bound
  refine ⟨by omega, ?_, by omega, Nat.not_prime_of_dvd_of_lt (m := 2) (by omega) (by decide) (by omega), ?_⟩
  · intro h
    have hle := Finset.le_sup (f := id) h
    simp only [id_eq] at hle
    omega
  · intro h
    have hle := Finset.le_sup (f := id) h
    simp only [id_eq] at hle
    omega

private lemma leastAllowed (s : History) (x : ℕ) (ok : Allowed s x)
    (least : ∀ y, Allowed s y → x ≤ y) : next s = x := by
  have hb : bound s ∈ candidates s := Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr le_rfl, bound_allowed s⟩
  have hn : (candidates s).Nonempty := ⟨_, hb⟩
  have hx : x ∈ candidates s := Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr (least _ (bound_allowed s)), ok⟩
  rw [next, dif_pos hn]
  exact le_antisymm ((candidates s).min'_le x hx) (least _ (Finset.mem_filter.mp ((candidates s).min'_mem hn)).2)

private lemma nextAbove {s : History} {k x : ℕ}
    (filled : ∀ y, 0 < y → y ≤ k → y ∈ s.terms) (ok : Allowed s x)
    (skip : ∀ y, k < y → y < x → ¬ Allowed s y) : next s = x := by
  apply leastAllowed s x ok
  intro y hy
  have hky : k < y := by
    by_contra! h
    exact hy.2.1 (filled y hy.1 h)
  by_contra! hyx
  exact skip y hky hyx hy

/-- At a block boundary the first k positive integers have all been used. -/
private structure Boundary (k : ℕ) (s : History) : Prop where
  large : 9 ≤ k
  terms : ∀ x, x ∈ s.terms ↔ 0 < x ∧ x ≤ k
  sums : ∀ e ∈ s.sums, e < 2 * k
  lastLo : k ≤ s.last + 2
  lastHi : s.last ≤ k
  residue : s.last + 2 = k → ¬ 3 ∣ 2 * k + 1

private lemma one {k s} (b : Boundary k s) : Boundary (k + 1) (record s (k + 1)) := by
  have large := b.large
  have upper := b.lastHi
  refine ⟨by omega, ?_, ?_, by simp [record], by simp [record], by simp [record]⟩
  · intro x; simp only [record, Finset.mem_insert, b.terms]; omega
  · intro e he
    by_cases old : e ∈ s.sums
    · have := b.sums e old; omega
    · simp only [record, Finset.mem_insert, old, or_false] at he; omega

private lemma pair {k s} (b : Boundary k s) :
    Boundary (k + 2) (record (record s (k + 2)) (k + 1)) := by
  have large := b.large
  have upper := b.lastHi
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
  · intro x; simp only [record, Finset.mem_insert, b.terms]; omega
  · intro e he
    by_cases old : e ∈ s.sums
    · have := b.sums e old; omega
    · simp only [record, Finset.mem_insert, old, or_false] at he; omega
  · dsimp [record]; omega
  · dsimp [record]; omega
  · dsimp [record]; omega

private lemma triple {k s} (b : Boundary k s) (hmod : ¬ 3 ∣ 2 * k + 1) :
    Boundary (k + 3) (record (record (record s (k + 2)) (k + 3)) (k + 1)) := by
  have large := b.large
  have upper := b.lastHi
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
  · intro x; simp only [record, Finset.mem_insert, b.terms]; omega
  · intro e he
    by_cases old : e ∈ s.sums
    · have := b.sums e old; omega
    · simp only [record, Finset.mem_insert, old, or_false] at he; omega
  · dsimp [record]; omega
  · dsimp [record]; omega
  · omega

private lemma oldAllowed {s : History} {k x : ℕ} (b : Boundary k s)
    (hx : k < x) (fresh : 2*k ≤ s.last+x) (hc : ¬ (s.last+x).Prime) : Allowed s x := by
  have large := b.large
  refine ⟨by omega, fun h => ?_, by omega, hc, fun h => ?_⟩
  · have := ((b.terms x).mp h).2; omega
  · have := b.sums _ h; omega

private lemma evenComposite {x : ℕ} (h : 2 < x) (even : 2 ∣ x) : ¬ x.Prime :=
  Nat.not_prime_of_dvd_of_lt even (by decide) h

/-- Every boundary begins a singleton, a transposed pair, or a three-letter block. -/
private lemma blocks {k s} (b : Boundary k s) :
    next s = k+1 ∨ (next s = k+2 ∧ (next (record s (k+2)) = k+1 ∨
      (next (record s (k+2)) = k+3 ∧ next (record (record s (k+2)) (k+3)) = k+1 ∧ ¬ 3 ∣ 2*k+1))) := by
  have large := b.large
  have lo := b.lastLo
  have hi := b.lastHi
  have filled (y : ℕ) (hy : 0 < y) (hk : y ≤ k) : y ∈ s.terms := (b.terms _).mpr ⟨hy, hk⟩
  by_cases first : Allowed s (k+1)
  · exact .inl (nextAbove filled first (by omega))
  have middle : s.last + 1 ≠ k := by
    intro h
    exact first (oldAllowed b (by omega) (by omega) (evenComposite (by omega) (by omega)))
  have residue : ¬ 3 ∣ 2*k+1 := by
    by_cases h : s.last + 2 = k
    · exact b.residue h
    · have top : s.last = k := by omega
      intro hd
      apply first
      apply oldAllowed b (by omega) (by omega)
      exact Nat.not_prime_of_dvd_of_lt (m := 3) (by omega) (by decide) (by omega)
  have firstTwo : next s = k+2 := by
    apply nextAbove filled (oldAllowed b (by omega) (by omega) (evenComposite (by omega) (by omega)))
    intro y hy hlt
    have eq : y = k+1 := by omega
    exact eq.symm ▸ first
  refine .inr ⟨firstTwo, ?_⟩
  let s₁ := record s (k+2)
  have filled₁ (y : ℕ) (hy : 0 < y) (hk : y ≤ k) : y ∈ s₁.terms := Finset.mem_insert_of_mem (filled y hy hk)
  by_cases second : Allowed s₁ (k+1)
  · exact .inl (nextAbove filled₁ second (by omega))
  have lowerFresh (x : ℕ) (hx : k < x) (hne : x ≠ k+2) (hc : ¬ (k+2+x).Prime) : Allowed s₁ x := by
    refine ⟨by omega, ?_, by change 1 < k+2+x; omega, hc, ?_⟩
    · simp only [s₁, record, Finset.mem_insert, b.terms]; omega
    · have old : k+2+x ∉ s.sums := fun h => by have := b.sums _ h; omega
      simp only [s₁, record, Finset.mem_insert, old, or_false]; omega
  have secondPrime : (k+2+(k+1)).Prime := by
    by_contra hn; exact second (lowerFresh _ (by omega) (by omega) hn)
  have noThree : ¬ 3 ∣ k+2+(k+1) := fun h =>
    (Nat.not_prime_of_dvd_of_lt h (by decide : 2 ≤ 3) (by omega)) secondPrime
  have three : 3 ∣ k+2+(k+3) := by
    have hk := Nat.mod_add_div k 3
    rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with h | h | h
    · exact False.elim (noThree ⟨2*(k/3)+1, by omega⟩)
    · exact False.elim (residue ⟨2*(k/3)+1, by omega⟩)
    · exact ⟨2*(k/3)+3, by omega⟩
  have feasible : Allowed s₁ (k+3) := lowerFresh _ (by omega) (by omega)
    (Nat.not_prime_of_dvd_of_lt three (by decide) (by omega))
  have pickThree : next s₁ = k+3 := by
    apply nextAbove filled₁ feasible
    intro y hy hlt allowed
    have used : k+2 ∈ s₁.terms := Finset.mem_insert_self _ _
    rcases (show y = k+1 ∨ y = k+2 by omega) with rfl | rfl
    · exact second allowed
    · exact allowed.2.1 used
  let s₂ := record s₁ (k+3)
  have filled₂ (y : ℕ) (hy : 0 < y) (hk : y ≤ k) : y ∈ s₂.terms := Finset.mem_insert_of_mem (filled₁ y hy hk)
  have finish : Allowed s₂ (k+1) := by
    refine ⟨by omega, ?_, by change 1 < k+3+(k+1); omega, ?_, ?_⟩
    · simp only [s₂, s₁, record, Finset.mem_insert, b.terms]; omega
    · change ¬ (k+3+(k+1)).Prime; exact evenComposite (by omega) (by omega)
    · have old : k+3+(k+1) ∉ s.sums := fun h => by have := b.sums _ h; omega
      simp only [s₂, s₁, record, Finset.mem_insert, old, or_false]; omega
  exact .inr ⟨pickThree, nextAbove filled₂ finish (by omega), residue⟩

private lemma stateStep {k : ℕ} (hk : 0 < k) : state (k+1) = record (state k) (next (state k)) := by
  cases k with
  | zero => omega
  | succ k => rfl

private lemma ahead (d : ℕ) : ∀ k, Boundary k (state k) →
    k+d-2 ≤ a (k+d) ∧ a (k+d) ≤ k+d+1 := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro k b
    have large := b.large
    by_cases dz : d = 0
    · subst d
      simp only [Nat.add_zero, a]
      have := b.lastLo
      have := b.lastHi
      omega
    rcases blocks b with single | ⟨firstTwo, more⟩
    · have new : state (k+1) = record (state k) (k+1) := by rw [stateStep (by omega), single]
      have B := one b
      rw [← new] at B
      have result := ih (d-1) (by omega) (k+1) B
      simpa only [show k+1+(d-1) = k+d by omega] using result
    · have new₁ : state (k+1) = record (state k) (k+2) := by rw [stateStep (by omega), firstTwo]
      by_cases d1 : d = 1
      · subst d; simp only [a, new₁, record]; omega
      rcases more with lastPair | ⟨middle, lastTriple, residue⟩
      · have new₂ : state (k+2) = record (record (state k) (k+2)) (k+1) := by
          rw [show k+2 = (k+1)+1 by omega, stateStep (k := k+1) (by omega), new₁, lastPair]
        have B := pair b
        rw [← new₂] at B
        have result := ih (d-2) (by omega) (k+2) B
        simpa only [show k+2+(d-2) = k+d by omega] using result
      · have new₂ : state (k+2) = record (record (state k) (k+2)) (k+3) := by
          rw [show k+2 = (k+1)+1 by omega, stateStep (k := k+1) (by omega), new₁, middle]
        by_cases d2 : d = 2
        · subst d; simp only [a, new₂, record]; omega
        have new₃ : state (k+3) = record (record (record (state k) (k+2)) (k+3)) (k+1) := by
          rw [show k+3 = (k+2)+1 by omega, stateStep (k := k+2) (by omega), new₂, lastTriple]
        have B := triple b residue
        rw [← new₃] at B
        have result := ih (d-3) (by omega) (k+3) B
        simpa only [show k+3+(d-3) = k+d by omega] using result

private def nine : History := ⟨7, Finset.Icc 1 9, {4, 8, 9, 6, 10, 14, 15, 16}⟩

set_option maxRecDepth 4000 in
private lemma atNine : state 9 = nine := by
  change History.mk (state 9).last (state 9).terms (state 9).sums = History.mk nine.last nine.terms nine.sums
  congr 1 <;> decide +kernel

private lemma initial : Boundary 9 (state 9) := by
  rw [atNine]
  refine ⟨by decide, ?_, ?_, by decide, by decide, ?_⟩
  · intro x; change x ∈ Finset.Icc 1 9 ↔ _; exact Finset.mem_Icc
  · decide +kernel
  · decide +kernel

end OMA.Murthy

open OMA.S_oeis_a075077 OMA.Murthy

set_option maxRecDepth 4000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a075077.main := by
  intro n hn
  by_cases h : 9 ≤ n
  · have bound := ahead (n-9) 9 initial
    simpa only [show 9+(n-9) = n by omega] using bound
  · interval_cases n <;> decide +kernel

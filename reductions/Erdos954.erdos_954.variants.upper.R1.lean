import FormalConjectures.ErdosProblems.«954»

-- Reduction Erdos954.erdos_954.variants.upper.R1 of the upper bound in Erdős Problem 954
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Rosen's sequence: the upper bound from the growth of the sequence

Let `a = rosen` and let `R x = solutionCount x`. The target is `R x ≤ (1 + o(1)) x`.

The construction gives one exact fact: the pairs with both indices at most `k + 1` and sum at
most `a (k + 2)` number fewer than `a (k + 2)` (`rosen_spec`). The sequence is strictly
increasing (`rosen_strictMono`). So for `x < a (k + 2)` only indices up to `k + 1` count, and
`R x < a (k + 2)` (`solutionCount_lt`). Hence `R x` is below the next term of the sequence, and
the target follows once consecutive terms have ratio tending to `1`. This is split in two:

* `H1` (order of magnitude, elementary): `k ^ 2 ≤ 100 * a k`. Proof sketch: the pairs with sum
  in `(a m, a n]` number at most `a n - a m - 1`, by `rosen_spec` and minimality. Pair the
  lower half of any `M` consecutive terms below `a n` with the first `M / 20` terms; this gives
  `M ^ 2 ≤ 100 * (a n - a (n - M))` by strong induction on `M`.
* `H2` (regularity, the open core): the gaps `a (k + 1) - a k` are `o(k ^ 2)`.

`H2` is not stronger than the target. With the proved lower bound `x ≤ R x`, the target gives
`R x ∼ x`, and the Hardy–Littlewood–Karamata Tauberian theorem then gives
`a k ∼ (π / 8) k ^ 2`, which implies `H2`. That converse is not formalised here.
-/

namespace OMA.R_Erdos954_erdos_954_variants_upper_R1

open Filter Erdos954

/-- Rosen's sequence grows at least quadratically. -/
def H1 : Prop :=
  ∀ k : ℕ, k ^ 2 ≤ 100 * rosen k

/-- The gaps of Rosen's sequence are `o(k ^ 2)`. -/
def H2 : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ k : ℕ in atTop, (rosen (k + 1) : ℝ) ≤ rosen k + ε * (k : ℝ) ^ 2

lemma rosenAux_succ_of_ne (k i : ℕ) (h : i ≠ k + 2) : rosenAux (k + 1) i = rosenAux k i := by
  show (if i = k + 2 then _ else rosenAux k i) = rosenAux k i
  rw [if_neg h]

lemma rosenAux_stable : ∀ k i : ℕ, i ≤ k + 1 → rosenAux k i = rosen i := by
  intro k
  induction k with
  | zero =>
    intro i hi
    have h : i = 0 ∨ i = 1 := by omega
    rcases h with rfl | rfl
    · rfl
    · show rosenAux 0 1 = rosenAux (0 + 1) 1
      rw [rosenAux_succ_of_ne 0 1 (by omega)]
  | succ k ih =>
    intro i hi
    by_cases h : i = k + 2
    · subst h
      show rosenAux (k + 1) (k + 2) = rosenAux (k + 1 + 1) (k + 2)
      rw [rosenAux_succ_of_ne (k + 1) (k + 2) (by omega)]
    · exact (rosenAux_succ_of_ne k i h).trans (ih i (by omega))

lemma pairCount_congr {a b : ℕ → ℕ} {m : ℕ} (h : ∀ i, i ≤ m → a i = b i) (n : ℕ) :
    pairCount a m n = pairCount b m n := by
  unfold pairCount
  apply congrArg
  apply Finset.filter_congr
  intro p hp
  simp only [Finset.mem_product, Finset.mem_range] at hp
  rw [h p.1 (by omega), h p.2 (by omega)]

lemma rosen_add_two (k : ℕ) :
    rosen (k + 2) = sInf {n : ℕ | pairCount rosen (k + 1) n < n} := by
  rw [← rosenAux_stable (k + 1) (k + 2) (by omega)]
  show (if k + 2 = k + 2 then _ else rosenAux k (k + 2)) = _
  rw [if_pos rfl]
  simp only [pairCount_congr (rosenAux_stable k)]

lemma pairCount_le_sq (a : ℕ → ℕ) (m n : ℕ) : pairCount a m n ≤ (m + 1) * (m + 1) := by
  unfold pairCount
  refine (Finset.card_filter_le _ _).trans ?_
  simp [Finset.card_product]

lemma pairCount_mono (a : ℕ → ℕ) (m : ℕ) {n n' : ℕ} (h : n ≤ n') :
    pairCount a m n ≤ pairCount a m n' := by
  unfold pairCount
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.trans h⟩

lemma pairCount_le_succ (a : ℕ → ℕ) (m n : ℕ) : pairCount a m n ≤ pairCount a (m + 1) n := by
  unfold pairCount
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
  exact ⟨⟨by omega, by omega⟩, hp.2⟩

/-- The new pair `(0, m + 1)` is counted as soon as `a (m + 1) ≤ n`. -/
lemma pairCount_succ_ge (a : ℕ → ℕ) (m n : ℕ) (h0 : a 0 = 0) (h : a (m + 1) ≤ n) :
    pairCount a m n + 1 ≤ pairCount a (m + 1) n := by
  unfold pairCount
  rw [← Finset.card_insert_of_notMem (a := ((0 : ℕ), m + 1)) (by simp)]
  apply Finset.card_le_card
  intro p hp
  rcases Finset.mem_insert.mp hp with rfl | hp
  · simp [h0, h]
  · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
    exact ⟨⟨by omega, by omega⟩, hp.2⟩

/-- The defining property of `rosen (k + 2)`. -/
lemma rosen_spec (k : ℕ) : pairCount rosen (k + 1) (rosen (k + 2)) < rosen (k + 2) := by
  have hne : {n : ℕ | pairCount rosen (k + 1) n < n}.Nonempty :=
    ⟨(k + 1 + 1) * (k + 1 + 1) + 1,
      Nat.lt_succ_of_le (pairCount_le_sq rosen (k + 1) ((k + 1 + 1) * (k + 1 + 1) + 1))⟩
  have := Nat.sInf_mem hne
  rw [← rosen_add_two] at this
  exact this

/-- Minimality of `rosen (k + 2)`. -/
lemma rosen_min (k n : ℕ) (h : n < rosen (k + 2)) : n ≤ pairCount rosen (k + 1) n := by
  rw [rosen_add_two] at h
  have := Nat.notMem_of_lt_sInf h
  simpa using this

lemma le_pairCount_of_le (k n : ℕ) (h : n ≤ rosen (k + 2)) :
    n ≤ pairCount rosen (k + 2) n := by
  rcases Nat.lt_or_ge n (rosen (k + 2)) with hlt | hge
  · exact (rosen_min k n hlt).trans (pairCount_le_succ rosen (k + 1) n)
  · rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact Nat.zero_le _
    · have h1 := rosen_min k (n - 1) (by omega)
      have h2 := pairCount_mono rosen (k + 1) (Nat.sub_le n 1)
      have h3 : pairCount rosen (k + 1) n + 1 ≤ pairCount rosen (k + 2) n :=
        pairCount_succ_ge rosen (k + 1) n rosen_zero hge
      omega

lemma rosen_lt_succ (k : ℕ) : rosen k < rosen (k + 1) := by
  rcases k with _ | _ | k
  · rw [rosen_zero, rosen_one]
    exact Nat.zero_lt_one
  · rw [rosen_one, rosen_two]
    norm_num
  · by_contra hcon
    exact absurd (le_pairCount_of_le k (rosen (k + 3)) (not_lt.mp hcon))
      (not_le.mpr (rosen_spec (k + 1)))

lemma rosen_strictMono : StrictMono rosen := strictMono_nat_of_lt_succ rosen_lt_succ

/-- Below `rosen (k + 2)` the number of solutions is less than `rosen (k + 2)`. -/
lemma solutionCount_lt (x k : ℕ) (h : x < rosen (k + 2)) : solutionCount x < rosen (k + 2) := by
  have h1 : solutionCount x ≤ pairCount rosen (k + 1) x := by
    unfold solutionCount pairCount
    apply Finset.card_le_card
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
    obtain ⟨_, h12, hpos, hsum⟩ := hp
    have h2 : rosen p.2 < rosen (k + 2) := by omega
    have h3 := rosen_strictMono.lt_iff_lt.mp h2
    exact ⟨⟨by omega, by omega⟩, h12, hpos, hsum⟩
  exact h1.trans_lt ((pairCount_mono rosen (k + 1) h.le).trans_lt (rosen_spec k))

/-- Every large `x` lies in a gap `[rosen (j + 1), rosen (j + 2))` with `j` large. -/
lemma exists_index (x K : ℕ) (hx : rosen (K + 1) ≤ x) :
    ∃ j, K ≤ j ∧ rosen (j + 1) ≤ x ∧ x < rosen (j + 2) := by
  obtain ⟨k, hk⟩ : ∃ k, k = Nat.findGreatest (fun j => rosen j ≤ x) x := ⟨_, rfl⟩
  have hKx : K + 1 ≤ x := rosen_strictMono.le_apply.trans hx
  have hk1 : K + 1 ≤ k := hk ▸ Nat.le_findGreatest (P := fun j => rosen j ≤ x) hKx hx
  have hkx : rosen k ≤ x := hk ▸ Nat.findGreatest_spec (P := fun j => rosen j ≤ x) hKx hx
  have hlt : x < rosen (k + 1) := by
    by_contra hcon
    have hle : rosen (k + 1) ≤ x := not_lt.mp hcon
    have hk1x : k + 1 ≤ x := rosen_strictMono.le_apply.trans hle
    have := Nat.le_findGreatest (P := fun j => rosen j ≤ x) hk1x hle
    omega
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact ⟨j, by omega, hkx, hlt⟩

theorem main : H1 → H2 → type_of% @Erdos954.erdos_954.variants.upper := by
  intro h1 h2 ε hε
  obtain ⟨K, hK⟩ := eventually_atTop.mp (h2 (ε / 100) (by positivity))
  refine eventually_atTop.mpr ⟨rosen (K + 1), fun x hx => ?_⟩
  obtain ⟨j, hKj, hjx, hxj⟩ := exists_index x K hx
  have hsol : (solutionCount x : ℝ) ≤ rosen (j + 2) := by
    exact_mod_cast (solutionCount_lt x j hxj).le
  have hgap : (rosen (j + 2) : ℝ) ≤ rosen (j + 1) + ε / 100 * ((j + 1 : ℕ) : ℝ) ^ 2 :=
    hK (j + 1) (by omega)
  have h1R : ((j + 1 : ℕ) : ℝ) ^ 2 ≤ 100 * (rosen (j + 1) : ℝ) := by
    exact_mod_cast h1 (j + 1)
  have hgrow : ε / 100 * ((j + 1 : ℕ) : ℝ) ^ 2 ≤ ε * rosen (j + 1) := by
    have h := mul_le_mul_of_nonneg_left h1R (by positivity : (0 : ℝ) ≤ ε / 100)
    have e : ε / 100 * (100 * (rosen (j + 1) : ℝ)) = ε * rosen (j + 1) := by ring
    linarith
  have hxR : (rosen (j + 1) : ℝ) ≤ x := by exact_mod_cast hjx
  have hmul : (1 + ε) * (rosen (j + 1) : ℝ) ≤ (1 + ε) * x :=
    mul_le_mul_of_nonneg_left hxR (by linarith)
  linarith

end OMA.R_Erdos954_erdos_954_variants_upper_R1

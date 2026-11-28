import OMAReductions.R_Erdos128_erdos_128_R1_H2_R1
import Mathlib

-- Reduction Erdos128.erdos_128.R1.H2.R1.H1.R1 of step Erdos128.erdos_128.R1.H2.R1.H1
-- Credit: @rickmanelius

/-!
# Erdős 128, lower middle range: a split by the independence number

The step asks for a sparse half (a set `V'` with `2 |V'| + 1 ≥ n` spanning at most `n ^ 2 / 50`
edges) in every triangle-free graph on `n` vertices with `n ^ 2 / 12 < e ≤ 3 n ^ 2 / 20` edges.

Proved below, with no hypothesis (`large_indep_regime`): the regime `α(G) ≥ 5 n / 12`. Let `I` be
an independent set of size `s ≥ 5 n / 12`, `X` its complement and `k = ⌊n / 2⌋`. If `s ≥ k`, any `k`
vertices of `I` span no edge. Otherwise compare two averaged candidates, a `k`-subset of `X` and `I`
together with a `(k - s)`-subset of `X`, each with at most its proportional share of the relevant
edge counts (the exact averaging lemma `avg_two` of the parent reduction). One of them is sparse as
soon as `50 e (k - s) k (k - 1) ≤ n ^ 2 (n - s) (k (k - 1) + (k - s) (n - k))`, and this holds
whenever `20 e ≤ 3 n ^ 2` and `12 s ≥ 5 n` (`key_ineq`). This is the averaging that the parent
reduction runs for `e ≤ n ^ 2 / 12` with the neighbourhood of a vertex of maximum degree; here it
runs with a large independent set and the upper edge bound. Since every neighbourhood is
independent, this regime contains all graphs with a vertex of degree at least `5 n / 12`.
At `e = 3 n ^ 2 / 20` the inequality needs `s` above about `0.406 n` and fails at `s = 2 n / 5`.

The rest of the range is left as two hypotheses, each the step restricted to one regime of the
independence number:
* `H1`: `2 n / 5 ≤ α(G) < 5 n / 12`. The balanced blow-up of the Petersen graph (`α = 2 n / 5`,
  `e = 3 n ^ 2 / 20`), one of the two known graphs whose sparsest half has exactly `n ^ 2 / 50`
  edges, lies in this regime.
* `H2`: `α(G) < 2 n / 5`.
-/

namespace OMA.R_Erdos128_erdos_128_R1_H2_R1_H1_R1

open Finset OMA.R_Erdos128_erdos_128_R1 OMA.R_Erdos128_erdos_128_R1_H2_R1

/-- The lower middle range when the independence number lies in `[2 n / 5, 5 n / 12)`. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.CliqueFree 3 →
    Fintype.card V ^ 2 < 12 * G.edgeSet.ncard →
    20 * G.edgeSet.ncard ≤ 3 * Fintype.card V ^ 2 →
    (∃ I : Set V, G.IsIndepSet I ∧ 2 * Fintype.card V ≤ 5 * I.ncard) →
    (∀ I : Set V, G.IsIndepSet I → 12 * I.ncard < 5 * Fintype.card V) →
      ∃ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V ∧
        50 * (G.induce V').edgeSet.ncard ≤ Fintype.card V ^ 2

/-- The lower middle range when the independence number is below `2 n / 5`. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.CliqueFree 3 →
    Fintype.card V ^ 2 < 12 * G.edgeSet.ncard →
    20 * G.edgeSet.ncard ≤ 3 * Fintype.card V ^ 2 →
    (∀ I : Set V, G.IsIndepSet I → 5 * I.ncard < 2 * Fintype.card V) →
      ∃ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V ∧
        50 * (G.induce V').edgeSet.ncard ≤ Fintype.card V ^ 2

-- The key inequality, first at the worst edge count `e = 3 n ^ 2 / 20`.

/-- Even `n = 2 k`, with `t = k - s` and `6 t ≤ k` (that is `12 s ≥ 5 n`). -/
lemma worst_even (k t : ℝ) (ht : 0 ≤ t) (h6 : 6 * t ≤ k) (hk : 1 ≤ k) :
    15 * t * (k * (k - 1)) ≤ 2 * (k + t) * (k * (k - 1) + t * k) := by
  have h1 : 0 ≤ k * ((k - 1) * (2 * k - 12 * t)) :=
    mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
  have h2 : 0 ≤ k * ((k + 1) * t) := mul_nonneg (by linarith) (mul_nonneg (by linarith) ht)
  have h3 : 0 ≤ k * (t * t) := mul_nonneg (by linarith) (mul_nonneg ht ht)
  nlinarith [h1, h2, h3]

/-- Odd `n = 2 k + 1`, with `t = k - s` and `12 t ≤ 2 k - 5` (that is `12 s ≥ 5 n`). -/
lemma worst_odd (k t : ℝ) (ht : 0 ≤ t) (h12 : 12 * t ≤ 2 * k - 5) (hk : 1 ≤ k) :
    15 * t * (k * (k - 1)) ≤ 2 * (k + 1 + t) * (k * (k - 1) + t * (k + 1)) := by
  have hkk : 0 ≤ k * (k - 1) := mul_nonneg (by linarith) (by linarith)
  have h1 : 0 ≤ k * (k - 1) * (2 * k - 12 * t - 5) := mul_nonneg hkk (by linarith)
  have h2 : 0 ≤ t * (k ^ 2 + 5 * k + 2) := mul_nonneg ht (by positivity)
  have h3 : 0 ≤ t * t * (k + 1) := mul_nonneg (mul_nonneg ht ht) (by linarith)
  nlinarith [h1, h2, h3, hkk]

/-- The inequality that makes one of the two averaged halves sparse:
`50 e (k - s) k (k - 1) ≤ n ^ 2 (n - s) (k (k - 1) + (k - s) (n - k))`, for `k = ⌊n / 2⌋`,
`s ≤ k - 1`, `20 e ≤ 3 n ^ 2` and `12 s ≥ 5 n`. -/
lemma key_ineq (n k s e : ℝ) (hpar : n = 2 * k ∨ n = 2 * k + 1) (hs0 : 0 ≤ s) (hsk : s + 1 ≤ k)
    (h20 : 20 * e ≤ 3 * n ^ 2) (h512 : 5 * n ≤ 12 * s) :
    50 * e * (k - s) * (k * (k - 1)) ≤ n ^ 2 * (n - s) * (k * (k - 1) + (k - s) * (n - k)) := by
  have hk : 1 ≤ k := by linarith
  have hP : 0 ≤ (k - s) * (k * (k - 1)) :=
    mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
  have hworst : 15 * (k - s) * (k * (k - 1)) ≤
      2 * (n - s) * (k * (k - 1) + (k - s) * (n - k)) := by
    rcases hpar with h | h
    · have := worst_even k (k - s) (by linarith) (by rw [h] at h512; linarith) hk
      rw [h]
      have e1 : 2 * k - s = k + (k - s) := by ring
      have e2 : 2 * k - k = k := by ring
      rw [e1, e2]
      linarith
    · have := worst_odd k (k - s) (by linarith) (by rw [h] at h512; linarith) hk
      rw [h]
      have e1 : 2 * k + 1 - s = k + 1 + (k - s) := by ring
      have e2 : 2 * k + 1 - k = k + 1 := by ring
      rw [e1, e2]
      linarith
  have a : 50 * e * ((k - s) * (k * (k - 1))) ≤
      50 * (3 * n ^ 2 / 20) * ((k - s) * (k * (k - 1))) :=
    mul_le_mul_of_nonneg_right (by linarith) hP
  have b := mul_le_mul_of_nonneg_left hworst (sq_nonneg n)
  nlinarith [a, b]

/-- Real endgame: the averaged half inside `X` or the averaged half containing `I` is sparse.
Here `DX = 2 e(X)` and `aX = e(I, X)`, so `2 e = DX + 2 aX`; `DA` and `T` are the degree sums of the
two candidates, bounded by their averages `hA` and `hB`. -/
lemma endgame (n k s e DX aX DA T : ℝ) (hpar : n = 2 * k ∨ n = 2 * k + 1) (hs0 : 0 ≤ s)
    (hsk : s + 1 ≤ k) (he : 2 * e = DX + 2 * aX) (h20 : 20 * e ≤ 3 * n ^ 2) (h512 : 5 * n ≤ 12 * s)
    (hA : DA * ((n - s) * (n - s - 1)) ≤ k * (k - 1) * DX)
    (hB : T * ((n - s) * (n - s - 1)) ≤
      2 * (k - s) * (n - s - 1) * aX + (k - s) * (k - s - 1) * DX) :
    25 * DA ≤ n ^ 2 ∨ 25 * T ≤ n ^ 2 := by
  have hk : 1 ≤ k := by linarith
  have hnk : k ≤ n - k := by rcases hpar with h | h <;> linarith
  have hx1 : 1 ≤ n - s - 1 := by linarith
  have hN : 0 < (n - s) * (n - s - 1) := by nlinarith
  by_cases hc : 25 * (k * (k - 1)) * DX ≤ n ^ 2 * ((n - s) * (n - s - 1))
  · left
    have h1 : 25 * DA * ((n - s) * (n - s - 1)) ≤ n ^ 2 * ((n - s) * (n - s - 1)) := by nlinarith
    exact le_of_mul_le_mul_right h1 hN
  · right
    rw [not_le] at hc
    have hkk0 : 0 ≤ k * (k - 1) := mul_nonneg (by linarith) (by linarith)
    have hkk : 0 < k * (k - 1) := by
      rcases hkk0.lt_or_eq with h | h
      · exact h
      · exfalso
        rw [← h] at hc
        nlinarith [mul_nonneg (sq_nonneg n) hN.le]
    -- the bound for `T`, with `2 aX = 2 e - DX`
    have eq1 : 2 * (k - s) * (n - s - 1) * aX + (k - s) * (k - s - 1) * DX =
        2 * e * (k - s) * (n - s - 1) - (k - s) * (n - k) * DX := by
      have h2a : 2 * aX = 2 * e - DX := by linarith
      have : 2 * (k - s) * (n - s - 1) * aX = (k - s) * (n - s - 1) * (2 * e - DX) := by
        rw [← h2a]; ring
      rw [this]; ring
    have hB2 : T * ((n - s) * (n - s - 1)) ≤
        2 * e * (k - s) * (n - s - 1) - (k - s) * (n - k) * DX := by
      rw [← eq1]; exact hB
    have hy0 : 0 ≤ (k - s) * (n - k) := mul_nonneg (by linarith) (by linarith)
    have s1 : (k - s) * (n - k) * (n ^ 2 * ((n - s) * (n - s - 1))) ≤
        (k - s) * (n - k) * (25 * (k * (k - 1)) * DX) := mul_le_mul_of_nonneg_left hc.le hy0
    have key := key_ineq n k s e hpar hs0 hsk h20 h512
    have s2 := mul_le_mul_of_nonneg_left hB2 (by positivity : (0 : ℝ) ≤ 25 * (k * (k - 1)))
    have s3 := mul_le_mul_of_nonneg_right key (by linarith : (0 : ℝ) ≤ n - s - 1)
    have s4 : (k * (k - 1)) * (25 * T * ((n - s) * (n - s - 1))) ≤
        (k * (k - 1)) * (n ^ 2 * ((n - s) * (n - s - 1))) := by
      nlinarith [s1, s2, s3]
    have s5 := le_of_mul_le_mul_left s4 hkk
    have s6 : 25 * T * ((n - s) * (n - s - 1)) = (25 * T) * ((n - s) * (n - s - 1)) := by ring
    rw [s6] at s5
    exact le_of_mul_le_mul_right s5 hN

-- The graph argument.

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The regime `α(G) ≥ 5 n / 12`: a set `I` of at least `5 n / 12` pairwise non-adjacent vertices
gives a sparse half whenever `20 e ≤ 3 n ^ 2` (no triangle condition is needed once `I` is given). -/
lemma large_indep_regime (h20 : 20 * G.edgeSet.ncard ≤ 3 * Fintype.card V ^ 2)
    (I : Finset V) (hI : ∀ u ∈ I, ∀ w ∈ I, ¬ G.Adj u w) (hs : 5 * Fintype.card V ≤ 12 * I.card) :
    ∃ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V ∧
      50 * (G.induce V').edgeSet.ncard ≤ Fintype.card V ^ 2 := by
  set n := Fintype.card V with hn
  have half : ∀ S : Finset V, S.card = n / 2 → 25 * ∑ u ∈ S, (S.filter (G.Adj u)).card ≤ n ^ 2 →
      ∃ V' : Set V, 2 * V'.ncard + 1 ≥ n ∧ 50 * (G.induce V').edgeSet.ncard ≤ n ^ 2 := by
    intro S hS hD
    refine ⟨(S : Set V), by rw [Set.ncard_coe_finset, hS]; omega, ?_⟩
    have := two_mul_induce G S
    omega
  rcases le_or_gt (n / 2) I.card with hk | hk
  · obtain ⟨S, hSI, hS⟩ := Finset.exists_subset_card_eq hk
    refine half S hS ?_
    rw [D_indep G S fun u hu w hw => hI u (hSI hu) w (hSI hw)]
    simp
  · have hIn : I.card ≤ n := by rw [hn, ← Finset.card_univ]; exact Finset.card_le_univ I
    set X := (univ : Finset V) \ I with hX
    have hXc : X.card = n - I.card := by
      rw [hX, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    have hdisj : Disjoint I X := Finset.disjoint_sdiff
    have hunion : I ∪ X = univ := Finset.union_sdiff_of_subset (Finset.subset_univ _)
    have hDU := D_union G I X hdisj hI
    rw [hunion] at hDU
    have hD2e := deg_sum_univ G
    -- candidate A: an averaged half inside `X`
    obtain ⟨YA, -, hYA, hA⟩ := avg_two G X ∅ (n / 2) (by omega) (by omega)
    simp only [Finset.filter_empty, Finset.card_empty, Finset.sum_const_zero, mul_zero,
      zero_add] at hA
    -- candidate B: `I` together with an averaged `(n / 2 - |I|)`-subset of `X`
    obtain ⟨YB, hYBX, hYB, hB⟩ := avg_two G X I (n / 2 - I.card) (by omega) (by omega)
    have hdisjB : Disjoint I YB := Finset.disjoint_of_subset_right hYBX hdisj
    have hDB := D_union G I YB hdisjB hI
    have hcardB : (I ∪ YB).card = n / 2 := by
      rw [Finset.card_union_of_disjoint hdisjB, hYB]; omega
    generalize hDXd : ∑ u ∈ X, (X.filter (G.Adj u)).card = DX at hA hB hDU
    generalize haXd : ∑ u ∈ X, (I.filter (G.Adj u)).card = aX at hB hDU
    generalize hDAd : ∑ u ∈ YA, (YA.filter (G.Adj u)).card = DA at hA
    generalize hTd : 2 * ∑ u ∈ YB, (I.filter (G.Adj u)).card +
      ∑ u ∈ YB, (YB.filter (G.Adj u)).card = T at hB
    have hT : ∑ u ∈ I ∪ YB, ((I ∪ YB).filter (G.Adj u)).card = T := by rw [hDB, ← hTd]; ring
    generalize hsd : I.card = s at hk hIn hXc hYB hcardB hB hs
    generalize hkd : n / 2 = k at hk hA hB hYA hcardB hYB half
    rw [hXc] at hA hB
    have hpar : n = 2 * k ∨ n = 2 * k + 1 := by omega
    have hA' : (DA : ℝ) * (((n : ℝ) - s) * ((n : ℝ) - s - 1)) ≤ (k : ℝ) * ((k : ℝ) - 1) * DX := by
      have := (Nat.cast_le (α := ℝ)).mpr hA
      push_cast [Nat.cast_sub hIn, Nat.cast_sub (show 1 ≤ n - s by omega),
        Nat.cast_sub (show 1 ≤ k by omega)] at this
      linarith
    have hB' : (T : ℝ) * (((n : ℝ) - s) * ((n : ℝ) - s - 1)) ≤
        2 * ((k : ℝ) - s) * ((n : ℝ) - s - 1) * aX + ((k : ℝ) - s) * ((k : ℝ) - s - 1) * DX := by
      have := (Nat.cast_le (α := ℝ)).mpr hB
      push_cast [Nat.cast_sub hIn, Nat.cast_sub (show 1 ≤ n - s by omega),
        Nat.cast_sub (show s ≤ k by omega), Nat.cast_sub (show 1 ≤ k - s by omega)] at this
      linarith
    have hpar' : (n : ℝ) = 2 * k ∨ (n : ℝ) = 2 * k + 1 := by
      rcases hpar with h | h
      · left; exact_mod_cast h
      · right; exact_mod_cast h
    have he' : 2 * (G.edgeSet.ncard : ℝ) = DX + 2 * aX := by
      have : 2 * G.edgeSet.ncard = DX + 2 * aX := by rw [← hD2e, hDU]
      exact_mod_cast this
    have h20' : 20 * (G.edgeSet.ncard : ℝ) ≤ 3 * (n : ℝ) ^ 2 := by exact_mod_cast h20
    have h512' : 5 * (n : ℝ) ≤ 12 * (s : ℝ) := by exact_mod_cast hs
    have hsk : (s : ℝ) + 1 ≤ k := by exact_mod_cast (show s + 1 ≤ k by omega)
    rcases endgame (n : ℝ) k s (G.edgeSet.ncard) DX aX DA T hpar' (by positivity) hsk
        he' h20' h512' hA' hB' with hfin | hfin
    · refine half YA hYA ?_
      rw [hDAd]; exact_mod_cast hfin
    · refine half (I ∪ YB) hcardB ?_
      rw [hT]; exact_mod_cast hfin

theorem main : H1 → H2 → OMA.R_Erdos128_erdos_128_R1_H2_R1.H1 := by
  intro h1 h2 V _ G hcf hlow hhigh
  classical
  by_cases hbig : ∃ I : Set V, G.IsIndepSet I ∧ 5 * Fintype.card V ≤ 12 * I.ncard
  · obtain ⟨I, hI, hIc⟩ := hbig
    refine large_indep_regime G hhigh I.toFinset ?_ ?_
    · intro u hu w hw huw
      rw [Set.mem_toFinset] at hu hw
      by_cases h : u = w
      · subst h
        exact G.loopless.irrefl _ huw
      · exact hI hu hw h huw
    · rw [← Set.ncard_eq_toFinset_card']
      exact hIc
  · push Not at hbig
    by_cases hmid : ∃ I : Set V, G.IsIndepSet I ∧ 2 * Fintype.card V ≤ 5 * I.ncard
    · exact h1 V G hcf hlow hhigh hmid hbig
    · push Not at hmid
      exact h2 V G hcf hlow hhigh hmid

end OMA.R_Erdos128_erdos_128_R1_H2_R1_H1_R1

import FormalConjectures.ErdosProblems.«657»
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Combinatorics.SimpleGraph.Triangle.Tripartite
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal

/-! Shorter proof of `Erdos657.erdos_657.variants.dim_one`. -/

open Finset Filter SimpleGraph TripartiteFromTriangles
open scoped Pointwise

private def idx (A : Finset ℝ) [DecidableEq ℝ] : Finset (↥(A - A) × ↥A × ↥(A + A)) :=
  univ.map ⟨fun ab : ↥A × ↥A =>
    (⟨ab.1.1 - ab.2.1, mem_sub.mpr ⟨_, ab.1.2, _, ab.2.2, rfl⟩⟩, ab.1,
     ⟨ab.1.1 + ab.2.1, mem_add.mpr ⟨_, ab.1.2, _, ab.2.2, rfl⟩⟩),
    fun x y h => by
      have h1 : x.1 = y.1 := congrArg (fun v => v.2.1) h
      have h2 : x.1.1 + x.2.1 = y.1.1 + y.2.1 := congrArg (fun v => v.2.2.1) h
      exact Prod.ext h1 (Subtype.ext (by rw [h1] at h2; linarith))⟩

private lemma mem_idx {A : Finset ℝ} [DecidableEq ℝ] {l : ↥(A - A)} {m : ↥A} {r : ↥(A + A)} :
    (l, m, r) ∈ idx A ↔ m.1 - l.1 ∈ A ∧ r.1 = m.1 + (m.1 - l.1) := by
  constructor
  · intro ht; rw [idx, Finset.mem_map] at ht; obtain ⟨⟨a, b⟩, -, h⟩ := ht
    have hl : a.1 - b.1 = l.1 := congrArg (fun x => x.1.1) h
    have hm : a = m := congrArg (fun x => x.2.1) h
    have hr : a.1 + b.1 = r.1 := congrArg (fun x => x.2.2.1) h
    subst a; rw [show m.1 - l.1 = b.1 by linarith, hr]; exact ⟨b.2, rfl⟩
  · rintro ⟨hb, hr⟩; rw [idx, Finset.mem_map]
    exact ⟨(m, ⟨m.1 - l.1, hb⟩), mem_univ _,
      Prod.ext (Subtype.ext (by change m.1 - (m.1 - l.1) = l.1; ring)) (Prod.ext rfl (Subtype.ext hr.symm))⟩

private instance idx_disj (A : Finset ℝ) [DecidableEq ℝ] : ExplicitDisjoint (idx A) :=
  ⟨fun _ _ _ _ h h' => Subtype.ext (by have := (mem_idx.mp h).2; have := (mem_idx.mp h').2; linarith),
   fun _ _ _ _ h h' => Subtype.ext (by have := (mem_idx.mp h).2; have := (mem_idx.mp h').2; linarith),
   fun _ _ _ _ h h' => Subtype.ext ((mem_idx.mp h).2.trans (mem_idx.mp h').2.symm)⟩

private lemma bnd_size (C : ℝ) (hC : 0 ≤ C) :
    ∃ B : ℕ, ∀ A : Finset ℝ, B ≤ A.card → (A : Set ℝ).IsIsoscelesFree →
      C * A.card ≤ distinctDistances A := by
  classical
  let K := 2 * C + 1; let M := K ^ 2 + K + 1; let ε := 1 / M ^ 2
  have hK : 0 < K := by dsimp [K]; linarith
  have hM : 0 < M := by dsimp [M]; positivity
  have he : 0 < ε := by dsimp [ε]; positivity
  let δ := triangleRemovalBound ε
  have hd : 0 < δ := triangleRemovalBound_pos he
  obtain ⟨B, hB⟩ := exists_nat_gt (max 0 (1 / δ))
  refine ⟨B, fun A hcard hfree => ?_⟩
  by_contra! hsmall
  have hN : (0 : ℝ) < A.card := (lt_of_le_of_lt (le_max_left 0 (1 / δ)) hB).trans_le (by exact_mod_cast hcard)
  have hN1 : (1 : ℝ) ≤ A.card := by exact_mod_cast Nat.succ_le_of_lt (show 0 < A.card by exact_mod_cast hN)
  have hDb : (A - A).card ≤ 2 * distinctDistances A + 1 := by
    let D := distanceSet A
    have hs : A - A ⊆ insert 0 (D ∪ -D) := fun x hx => by
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_sub.mp hx
      by_cases h : a = b
      · simp [h]
      have hd' : dist a b ∈ D := mem_image.mpr ⟨(a, b), mem_offDiag.mpr ⟨ha, hb, h⟩, rfl⟩
      rcases le_total 0 (a - b) with hp | hn
      · exact mem_insert_of_mem (mem_union_left _ (by simpa [Real.dist_eq, abs_of_nonneg hp] using hd'))
      · exact mem_insert_of_mem (mem_union_right _ (by simpa [Real.dist_eq, abs_of_nonpos hn] using hd'))
    have hcu := card_union_le D (-D); rw [card_neg] at hcu
    have := (card_le_card hs).trans (card_insert_le _ _)
    change _ ≤ 2 * D.card + 1; omega
  have hDiff : ((A - A).card : ℝ) ≤ K * A.card := by
    have : ((A - A).card : ℝ) ≤ 2 * (distinctDistances A : ℝ) + 1 := by exact_mod_cast hDb
    dsimp [K]; nlinarith
  have hSum : ((A + A).card : ℝ) ≤ K ^ 2 * A.card := by
    have hR := NNRat.cast_le (K := ℝ).mpr (pluennecke_ruzsa_inequality_nsmul_sub (card_pos.mp (by exact_mod_cast hN)) A 2)
    have hsb : ((A + A).card : ℝ) ≤ (((A - A).card : ℝ) / A.card) ^ 2 * A.card := by
      simpa only [two_nsmul, NNRat.cast_natCast, NNRat.cast_div, NNRat.cast_pow, NNRat.cast_mul] using hR
    refine hsb.trans ?_; gcongr; exact (div_le_iff₀ hN).mpr hDiff
  let t := idx A
  have htcard : t.card = A.card ^ 2 := by simp [t, idx, Fintype.card_prod, sq]
  let : NoAccidental t := ⟨fun _ _ _ _ _ _ ha hb hc => by
    obtain ⟨h1, ha'⟩ := mem_idx.mp ha; obtain ⟨h2, hb'⟩ := mem_idx.mp hb; obtain ⟨h3, -⟩ := mem_idx.mp hc
    have h3ap : ThreeAPFree (A : Set ℝ) := fun a ha b hb c hc habc => by
      by_contra hab
      exact hfree ha hb hc hab (fun e => hab (by linarith)) (fun e => hab (by linarith))
        (Or.inl (by rw [Real.dist_eq, Real.dist_eq, show a - b = b - c by linarith]))
    have := h3ap h1 h2 h3 (by linarith); left; exact Subtype.ext (by linarith)⟩
  let v := (A - A).card + A.card + (A + A).card
  have hvu : (v : ℝ) ≤ M * A.card := by dsimp [v, M]; push_cast; nlinarith
  have hvl : (A.card : ℝ) ≤ v := by exact_mod_cast (show A.card ≤ v by dsimp [v]; omega)
  have hcnt : ε * ((v ^ 2 : ℕ) : ℝ) ≤ t.card := by
    rw [htcard]; push_cast
    calc ε * (v : ℝ) ^ 2 ≤ ε * (M * A.card) ^ 2 := by gcongr
      _ = (A.card : ℝ) ^ 2 := by dsimp [ε]; field_simp
  have htri := (farFromTriangleFree t (by simpa [v] using hcnt)).le_card_cliqueFinset
  rw [card_triangles, htcard] at htri
  have htri' : δ * (v : ℝ) ^ 3 ≤ (A.card : ℝ) ^ 2 := by
    simpa [δ, v, Fintype.card_sum, Nat.cast_add, add_assoc] using htri
  have hcancel : (A.card : ℝ) * δ ≤ 1 := le_of_mul_le_mul_right (a := (A.card : ℝ) ^ 2) (by
    rw [one_mul]; calc (A.card : ℝ) * δ * (A.card : ℝ) ^ 2 = δ * (A.card : ℝ) ^ 3 := by ring
      _ ≤ δ * (v : ℝ) ^ 3 := by gcongr
      _ ≤ _ := htri') (pow_pos hN 2)
  exact (not_lt_of_ge ((le_div_iff₀ hd).mpr hcancel)) <|
    (lt_of_le_of_lt (le_max_right 0 (1 / δ)) hB).trans_le (by exact_mod_cast hcard)

theorem OMA.solution : type_of% @Erdos657.erdos_657.variants.dim_one := by
  classical
  let S (n : ℕ) : Set ℕ :=
    {d | ∃ A : Finset ℝ, A.card = n ∧ (A : Set ℝ).IsIsoscelesFree ∧ distinctDistances A = d}
  let f (n : ℕ) : ℝ := if (S n).Nonempty then ((sInf (S n) : ℕ) : ℝ) / n else n
  refine ⟨f, tendsto_atTop.2 fun C => ?_, fun n A hn hA => ?_⟩
  · obtain ⟨B, hB⟩ := bnd_size (max C 0) (le_max_right _ _)
    obtain ⟨B', hB'⟩ := exists_nat_gt (max C 0)
    filter_upwards [eventually_ge_atTop (max B B')] with n hn
    have hCn : max C 0 < (n : ℝ) := hB'.trans_le (by exact_mod_cast (le_max_right B B').trans hn)
    have hnpos : (0 : ℝ) < n := (le_max_right C 0).trans_lt hCn
    by_cases h : (S n).Nonempty
    · obtain ⟨A, hcard, hA, hdist⟩ := Nat.sInf_mem h
      simp only [f, if_pos h]; rw [← hdist, le_div_iff₀ hnpos, ← hcard]
      exact (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans
        (hB A (hcard ▸ (le_max_left B B').trans hn) hA)
    · simp only [f, if_neg h]; exact (le_max_left C 0).trans hCn.le
  · have hmem : distinctDistances A ∈ S n := ⟨A, hn, hA, rfl⟩
    simp only [f, if_pos (show (S n).Nonempty from ⟨_, hmem⟩)]
    by_cases hn0 : n = 0
    · simp [hn0]
    · rw [div_mul_cancel₀ _ (by exact_mod_cast hn0 : (n : ℝ) ≠ 0)]; exact_mod_cast Nat.sInf_le hmem

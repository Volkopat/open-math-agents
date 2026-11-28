import OMAReductions.R_Erdos1020_erdos_1020_R1_H2_R1
import Mathlib

/-!
# Frankl's theorem on the Erdős Matching Conjecture (step H1 of Erdős Problem 1020)

Target: step `Erdos1020.erdos_1020.R1.H2.R1.H1`. With `s = k - 1`: an `r`-uniform family on
`n ≥ (2 s + 1) r - s` points with no `s + 1` pairwise disjoint members has at most
`C(n, r) - C(n - s, r)` members (P. Frankl, Improved bounds for Erdős' Matching Conjecture,
J. Combin. Theory Ser. A 120 (2013), 1068-1072).

Families are `Finset (Finset ℕ)`; the ground set is `range n`.

Structure of the proof (a known result; this is a formalization, written as six lemmas and an assembly).
* `exists_shifted`: pass to a shifted family.
* `trace_split`: split a shifted family by its trace on the first `s + 1` points
  `T = range (s + 1)`: traces of size at least two, the empty trace `F0`, and the singleton
  traces `{i}`, which give families `Fam i` of `(r - 1)`-sets on `Y = Ico (s + 1) n`.
* `shadow_bound`: `|F0| ≤ s |∂ F0|`, and `∂ F0 ⊆ Fam s`.
* `cross_dependent_bound` (from `nested_no_sdr`):
  `|Fam 0| + ... + |Fam (s - 1)| + (s + 1) |Fam s| ≤ s C(|Y|, r - 1)`.
* `count_bound`: the sets with trace of size at least two, plus `s C(n - s - 1, r - 1)`, plus
  `C(n - s, r)`, number at most `C(n, r)`.
-/

open Finset
open scoped FinsetFamily

namespace OMA.Frankl

/-- `F` is shifted from `m` on: replacing an element `j` of a member by a smaller element
`i ≥ m` not in that member gives a member. -/
def Shifted (m : ℕ) (F : Finset (Finset ℕ)) : Prop :=
  ∀ A ∈ F, ∀ j ∈ A, ∀ i, m ≤ i → i < j → i ∉ A → insert i (A.erase j) ∈ F

/- Part A: `exists_shifted` -/
/-- The image of a member under the `i ← j` shift of the family `F`. -/
def A_phi (i j : ℕ) (F : Finset (Finset ℕ)) (a : Finset ℕ) : Finset ℕ :=
  if j ∈ a ∧ i ∉ a ∧ insert i (a.erase j) ∉ F then insert i (a.erase j) else a

/-- The `i ← j` shift of a family. -/
def A_step (i j : ℕ) (F : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  F.image (A_phi i j F)

/-- The measure: the sum over members of the sum of their elements. -/
def A_mu (F : Finset (Finset ℕ)) : ℕ := ∑ A ∈ F, ∑ x ∈ A, x

lemma A_erase_insert_eq {i j : ℕ} {a b : Finset ℕ} (hja : j ∈ a) (hia : i ∉ a)
    (hjb : j ∈ b) (hib : i ∉ b) (h : insert i (a.erase j) = insert i (b.erase j)) : a = b := by
  have h1 : (insert i (a.erase j)).erase i = (insert i (b.erase j)).erase i := by rw [h]
  rw [erase_insert (fun hm => hia (mem_of_mem_erase hm)),
    erase_insert (fun hm => hib (mem_of_mem_erase hm))] at h1
  rw [← insert_erase hja, ← insert_erase hjb, h1]

lemma A_phi_injOn (i j : ℕ) (F : Finset (Finset ℕ)) :
    Set.InjOn (A_phi i j F) F := by
  intro a ha b hb hab
  simp only [A_phi] at hab
  split_ifs at hab with h1 h2 h2
  · exact A_erase_insert_eq h1.1 h1.2.1 h2.1 h2.2.1 hab
  · exact absurd (hab ▸ hb) h1.2.2
  · exact absurd (hab ▸ ha) h2.2.2
  · exact hab

lemma A_card_step (i j : ℕ) (F : Finset (Finset ℕ)) :
    (A_step i j F).card = F.card :=
  card_image_of_injOn (A_phi_injOn i j F)

lemma A_sub_step (n r i j : ℕ) (hij : i < j) (F : Finset (Finset ℕ))
    (hF : F ⊆ (range n).powersetCard r) : A_step i j F ⊆ (range n).powersetCard r := by
  intro B hB
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hB
  have h := mem_powersetCard.mp (hF ha)
  simp only [A_phi]
  split_ifs with h1
  · rw [mem_powersetCard]
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact mem_range.mpr (lt_trans hij (mem_range.mp (h.1 h1.1)))
      · exact h.1 (mem_of_mem_erase hx)
    · rw [card_insert_of_notMem (fun hm => h1.2.1 (mem_of_mem_erase hm)),
        card_erase_of_mem h1.1, h.2]
      have : 0 < r := h.2 ▸ card_pos.mpr ⟨j, h1.1⟩
      omega
  · exact hF ha

lemma A_sum_shift {i j : ℕ} {a : Finset ℕ} (hij : i < j) (hja : j ∈ a) (hia : i ∉ a) :
    ∑ x ∈ insert i (a.erase j), x < ∑ x ∈ a, x := by
  rw [sum_insert (fun hm => hia (mem_of_mem_erase hm)), ← sum_erase_add a _ hja]
  omega

lemma A_mu_step_lt (i j : ℕ) (hij : i < j) (F : Finset (Finset ℕ)) (A : Finset ℕ) (hA : A ∈ F)
    (hjA : j ∈ A) (hiA : i ∉ A) (hnot : insert i (A.erase j) ∉ F) :
    A_mu (A_step i j F) < A_mu F := by
  unfold A_mu A_step
  rw [sum_image (A_phi_injOn i j F)]
  apply sum_lt_sum
  · intro a _
    simp only [A_phi]
    split_ifs with h1
    · exact (A_sum_shift hij h1.1 h1.2.1).le
    · exact le_rfl
  · refine ⟨A, hA, ?_⟩
    simp only [A_phi]
    rw [if_pos ⟨hjA, hiA, hnot⟩]
    exact A_sum_shift hij hjA hiA

lemma A_new (i j : ℕ) (hij : i ≠ j) (F : Finset (Finset ℕ)) (B : Finset ℕ)
    (hB : B ∈ A_step i j F) (hBF : B ∉ F) :
    i ∈ B ∧ j ∉ B ∧ insert j (B.erase i) ∈ F := by
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hB
  simp only [A_phi] at hBF ⊢
  split_ifs with h1
  · refine ⟨mem_insert_self _ _, ?_, ?_⟩
    · intro hm
      rcases mem_insert.mp hm with h | h
      · exact hij h.symm
      · exact (notMem_erase j a) h
    · rw [erase_insert (fun hm => h1.2.1 (mem_of_mem_erase hm)), insert_erase h1.1]
      exact ha
  · rw [if_neg h1] at hBF
    exact absurd ha hBF

lemma A_old (i j : ℕ) (F : Finset (Finset ℕ)) (B : Finset ℕ)
    (hB : B ∈ A_step i j F) (hBF : B ∈ F) (hjB : j ∈ B) (hiB : i ∉ B) :
    insert i (B.erase j) ∈ F := by
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hB
  simp only [A_phi] at hBF hjB hiB ⊢
  split_ifs at hBF hjB hiB ⊢ with h1
  · exact absurd hBF h1.2.2
  · by_contra hc
    exact h1 ⟨hjB, hiB, hc⟩

lemma A_swap_fix {i j : ℕ} {C : Finset ℕ} (hi : i ∉ C) (hj : j ∉ C) :
    C.map (Equiv.swap i j).toEmbedding = C := by
  ext x
  rw [mem_map_equiv, Equiv.symm_swap, Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; exact ⟨fun h => absurd h hj, fun h => absurd h hi⟩
  · subst h2; exact ⟨fun h => absurd h hi, fun h => absurd h hj⟩
  · exact Iff.rfl

lemma A_swap_one {i j : ℕ} {C : Finset ℕ} (hij : i ≠ j) (hi : i ∈ C) (hj : j ∉ C) :
    C.map (Equiv.swap i j).toEmbedding = insert j (C.erase i) := by
  ext x
  rw [mem_map_equiv, Equiv.symm_swap, Equiv.swap_apply_def, mem_insert, mem_erase]
  split_ifs with h1 h2
  · subst h1
    exact ⟨fun h => absurd h hj, fun h => by
      rcases h with h | h
      · exact absurd h hij
      · exact absurd rfl h.1⟩
  · subst h2; exact ⟨fun _ => Or.inl rfl, fun _ => hi⟩
  · constructor
    · intro h; exact Or.inr ⟨h1, h⟩
    · intro h
      rcases h with h | h
      · exact absurd h h2
      · exact h.2

lemma A_noMatch (k i j : ℕ) (hij : i ≠ j) (F : Finset (Finset ℕ))
    (hM : ¬ F.HasHypergraphMatching k) : ¬ (A_step i j F).HasHypergraphMatching k := by
  rintro ⟨M, hMsub, hMcard, hMdisj⟩
  apply hM
  by_cases hall : M ⊆ F
  · exact ⟨M, hall, hMcard, hMdisj⟩
  obtain ⟨B1, hB1M, hB1F⟩ := not_subset.mp hall
  obtain ⟨hiB1, hjB1, hold1⟩ := A_new i j hij F B1 (hMsub hB1M) hB1F
  let σ : ℕ ≃ ℕ := Equiv.swap i j
  let τ : Finset ℕ → Finset ℕ := fun C => C.map σ.toEmbedding
  have hτinj : Function.Injective τ := map_injective _
  -- members other than `B1` do not contain `i` and are old
  have hother : ∀ C ∈ M, C ≠ B1 → i ∉ C ∧ C ∈ F := by
    intro C hC hne
    have hd : Disjoint C B1 := hMdisj (mem_coe.mpr hC) (mem_coe.mpr hB1M) hne
    have hiC : i ∉ C := fun h => disjoint_left.mp hd h hiB1
    refine ⟨hiC, ?_⟩
    by_contra hCF
    exact hiC (A_new i j hij F C (hMsub hC) hCF).1
  have hτF : ∀ C ∈ M, τ C ∈ F := by
    intro C hC
    by_cases hne : C = B1
    · subst hne
      show C.map (Equiv.swap i j).toEmbedding ∈ F
      rw [A_swap_one hij hiB1 hjB1]
      exact hold1
    · obtain ⟨hiC, hCF⟩ := hother C hC hne
      show C.map (Equiv.swap i j).toEmbedding ∈ F
      by_cases hjC : j ∈ C
      · rw [Equiv.swap_comm, A_swap_one hij.symm hjC hiC]
        exact A_old i j F C (hMsub hC) hCF hjC hiC
      · rw [A_swap_fix hiC hjC]
        exact hCF
  refine ⟨M.image τ, ?_, ?_, ?_⟩
  · intro X hX
    obtain ⟨C, hC, rfl⟩ := mem_image.mp hX
    exact hτF C hC
  · rw [card_image_of_injective _ hτinj, hMcard]
  · intro X hX Y hY hXY
    obtain ⟨C, hC, rfl⟩ := mem_image.mp (mem_coe.mp hX)
    obtain ⟨D, hD, rfl⟩ := mem_image.mp (mem_coe.mp hY)
    have hCD : C ≠ D := fun h => hXY (h ▸ rfl)
    exact (disjoint_map _).mpr (hMdisj (mem_coe.mpr hC) (mem_coe.mpr hD) hCD)

lemma A_main (n r k : ℕ) : ∀ w : ℕ, ∀ F : Finset (Finset ℕ), A_mu F = w →
    F ⊆ (range n).powersetCard r → ¬ F.HasHypergraphMatching k →
    ∃ G : Finset (Finset ℕ), G ⊆ (range n).powersetCard r ∧ ¬ G.HasHypergraphMatching k ∧
      G.card = F.card ∧ Shifted 0 G := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro F hw hF hM
    by_cases hs : Shifted 0 F
    · exact ⟨F, hF, hM, rfl, hs⟩
    · unfold Shifted at hs
      push Not at hs
      obtain ⟨A, hA, j, hjA, i, -, hij, hiA, hnot⟩ := hs
      have hlt := A_mu_step_lt i j hij F A hA hjA hiA hnot
      obtain ⟨G, hG, hGM, hGc, hGs⟩ := ih (A_mu (A_step i j F)) (hw ▸ hlt) (A_step i j F) rfl
        (A_sub_step n r i j hij F hF) (A_noMatch k i j hij.ne F hM)
      exact ⟨G, hG, hGM, hGc.trans (A_card_step i j F), hGs⟩

/-- **Lemma A (shifting).** A family of `r`-subsets of `range n` with no `k` pairwise disjoint
members can be replaced by a shifted one of the same size with the same properties. -/
lemma exists_shifted (n r k : ℕ) (F : Finset (Finset ℕ)) (hF : F ⊆ (range n).powersetCard r)
    (hM : ¬ F.HasHypergraphMatching k) :
    ∃ G : Finset (Finset ℕ), G ⊆ (range n).powersetCard r ∧ ¬ G.HasHypergraphMatching k ∧
      G.card = F.card ∧ Shifted 0 G :=
  A_main n r k (A_mu F) F rfl hF hM

/- Part F: `count_bound` -/
/-- The `r`-subsets of `range n` with trace `{i}` on `range (s + 1)`, as images. -/
lemma F_card_image (n r s i : ℕ) (hi : i < s + 1) :
    (((Ico (s + 1) n).powersetCard (r - 1)).image (insert i)).card =
      (n - s - 1).choose (r - 1) := by
  rw [card_image_of_injOn]
  · rw [card_powersetCard, Nat.card_Ico, Nat.sub_sub]
  · intro B hB C hC hBC
    have hB' := (mem_powersetCard.mp (mem_coe.mp hB)).1
    have hC' := (mem_powersetCard.mp (mem_coe.mp hC)).1
    have hiB : i ∉ B := fun h => by have := mem_Ico.mp (hB' h); omega
    have hiC : i ∉ C := fun h => by have := mem_Ico.mp (hC' h); omega
    rw [← erase_insert hiB, ← erase_insert hiC, hBC]

lemma F_pairwise (n r s : ℕ) :
    (↑(range (s + 1)) : Set ℕ).PairwiseDisjoint
      (fun i => ((Ico (s + 1) n).powersetCard (r - 1)).image (insert i)) := by
  intro i _ j hj hij
  simp only [Function.onFun]
  rw [disjoint_left]
  intro A hAi hAj
  obtain ⟨B, hB, rfl⟩ := mem_image.mp hAi
  obtain ⟨C, hC, hCB⟩ := mem_image.mp hAj
  have hC' := (mem_powersetCard.mp hC).1
  have hiC : i ∈ insert j C := by rw [hCB]; exact mem_insert_self i B
  rcases mem_insert.mp hiC with h | h
  · exact hij h
  · have := mem_Ico.mp (hC' h)
    have := mem_range.mp (mem_coe.mp ‹i ∈ (↑(range (s + 1)) : Set ℕ)›)
    omega

lemma F_disjoint (n r s : ℕ) :
    Disjoint ((Ico (s + 1) n).powersetCard r)
      ((range (s + 1)).biUnion
        (fun i => ((Ico (s + 1) n).powersetCard (r - 1)).image (insert i))) := by
  rw [disjoint_left]
  intro A hA hA'
  obtain ⟨i, hi, hAi⟩ := mem_biUnion.mp hA'
  obtain ⟨B, -, rfl⟩ := mem_image.mp hAi
  have := mem_Ico.mp ((mem_powersetCard.mp hA).1 (mem_insert_self i B))
  have := mem_range.mp hi
  omega

lemma F_subset (n r s : ℕ) (hr : 1 ≤ r) (hsn : s + 1 ≤ n) :
    (Ico (s + 1) n).powersetCard r ∪
      (range (s + 1)).biUnion
        (fun i => ((Ico (s + 1) n).powersetCard (r - 1)).image (insert i)) ⊆
      ((range n).powersetCard r).filter (fun A => ¬ 2 ≤ (A ∩ range (s + 1)).card) := by
  intro A hA
  rcases mem_union.mp hA with h | h
  · obtain ⟨h1, h2⟩ := mem_powersetCard.mp h
    refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨?_, h2⟩, ?_⟩
    · intro x hx
      have := mem_Ico.mp (h1 hx)
      exact mem_range.mpr this.2
    · have : A ∩ range (s + 1) = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro x hx
        have := mem_Ico.mp (h1 (mem_inter.mp hx).1)
        have := mem_range.mp (mem_inter.mp hx).2
        omega
      rw [this, card_empty]
      omega
  · obtain ⟨i, hi, hAi⟩ := mem_biUnion.mp h
    obtain ⟨B, hB, rfl⟩ := mem_image.mp hAi
    obtain ⟨h1, h2⟩ := mem_powersetCard.mp hB
    have hi' := mem_range.mp hi
    have hiB : i ∉ B := fun h => by have := mem_Ico.mp (h1 h); omega
    refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
    · intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact mem_range.mpr (by omega)
      · exact mem_range.mpr (mem_Ico.mp (h1 hx)).2
    · rw [card_insert_of_notMem hiB, h2]
      omega
    · have : insert i B ∩ range (s + 1) ⊆ {i} := by
        intro x hx
        rcases mem_insert.mp (mem_inter.mp hx).1 with rfl | hxB
        · exact mem_singleton_self x
        · have := mem_Ico.mp (h1 hxB)
          have := mem_range.mp (mem_inter.mp hx).2
          omega
      have := card_le_card this
      rw [card_singleton] at this
      omega

/-- **Lemma F (counting).** Among the `r`-subsets of `range n`, those meeting
`T = range (s + 1)` in at least two points, plus `s C(n - s - 1, r - 1)`, plus `C(n - s, r)`,
number at most (in fact exactly) `C(n, r)`.

Sketch. Classify the `r`-subsets `A` of `range n` by `A ∩ T`: empty trace gives
`C(n - s - 1, r)` sets, trace `{i}` gives `C(n - s - 1, r - 1)` sets for each of the `s + 1`
values of `i`. Pascal's rule gives `C(n - s, r) = C(n - s - 1, r) + C(n - s - 1, r - 1)`. -/
lemma count_bound (n r s : ℕ) (hr : 1 ≤ r) (hsn : s + 1 ≤ n) :
    (((range n).powersetCard r).filter (fun A => 2 ≤ (A ∩ range (s + 1)).card)).card +
      s * (n - s - 1).choose (r - 1) + (n - s).choose r ≤ n.choose r := by
  have htot := card_filter_add_card_filter_not
    (s := (range n).powersetCard r) (fun A => 2 ≤ (A ∩ range (s + 1)).card)
  rw [card_powersetCard, card_range] at htot
  have hsub := card_le_card (F_subset n r s hr hsn)
  rw [card_union_of_disjoint (F_disjoint n r s), card_biUnion (F_pairwise n r s),
    sum_congr rfl (fun i hi => F_card_image n r s i (mem_range.mp hi)), sum_const, card_range,
    smul_eq_mul, card_powersetCard, Nat.card_Ico] at hsub
  have hpascal : (n - s).choose r = (n - s - 1).choose r + (n - s - 1).choose (r - 1) := by
    obtain ⟨q, hq⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
    obtain ⟨m, hm⟩ : ∃ m, n - s = m + 1 := ⟨n - s - 1, by omega⟩
    subst hq
    rw [hm, Nat.choose_succ_succ, Nat.add_sub_cancel, Nat.add_sub_cancel]
    ring
  have e : n - (s + 1) = n - s - 1 := by omega
  rw [e] at hsub
  have e2 : (s + 1) * (n - s - 1).choose (r - 1) =
      s * (n - s - 1).choose (r - 1) + (n - s - 1).choose (r - 1) := by ring
  omega

/- Part C: `nested_no_sdr` -/
/-- Greedy choice of distinct representatives, downwards from index `s`, when every `N i`
(`i ≤ s`) has more than `s - i` elements. -/
lemma C_greedy (s : ℕ) (N : ℕ → Finset ℕ) (hbig : ∀ i ≤ s, s - i < (N i).card) :
    ∀ k ≤ s + 1, ∃ c : ℕ → ℕ, (∀ i, s + 1 - k ≤ i → i ≤ s → c i ∈ N i) ∧
      ∀ i j, s + 1 - k ≤ i → i ≤ s → s + 1 - k ≤ j → j ≤ s → i ≠ j → c i ≠ c j := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨fun _ => 0, fun i h1 h2 => by omega, fun i j h1 h2 _ _ _ => by omega⟩
  | succ k ih =>
    intro hk
    obtain ⟨c, hc, hinj⟩ := ih (by omega)
    have hcard : ((Icc (s + 1 - k) s).image c).card < (N (s - k)).card := by
      calc ((Icc (s + 1 - k) s).image c).card ≤ (Icc (s + 1 - k) s).card := card_image_le
        _ = k := by rw [Nat.card_Icc]; omega
        _ < (N (s - k)).card := by have := hbig (s - k) (by omega); omega
    obtain ⟨x, hxN, hxn⟩ := exists_mem_notMem_of_card_lt_card hcard
    have hold : ∀ j, s + 1 - k ≤ j → j ≤ s → c j ≠ x := by
      intro j h1 h2 hx
      apply hxn
      rw [← hx]
      exact mem_image_of_mem c (mem_Icc.mpr ⟨h1, h2⟩)
    refine ⟨Function.update c (s - k) x, ?_, ?_⟩
    · intro i h1 h2
      by_cases him : i = s - k
      · rw [him, Function.update_self]; exact hxN
      · rw [Function.update_of_ne him]; exact hc i (by omega) h2
    · intro i j h1 h2 h3 h4 hij
      by_cases him : i = s - k
      · have hjm : j ≠ s - k := fun h => hij (him.trans h.symm)
        rw [him, Function.update_self, Function.update_of_ne hjm]
        exact fun h => hold j (by omega) h4 h.symm
      · by_cases hjm : j = s - k
        · rw [hjm, Function.update_self, Function.update_of_ne him]
          exact hold i (by omega) h2
        · rw [Function.update_of_ne him, Function.update_of_ne hjm]
          exact hinj i j (by omega) h2 (by omega) h4 hij

/-- Nested sets: `N i ⊆ N i0` for `i0 ≤ i ≤ s`. -/
lemma C_nest (s : ℕ) (N : ℕ → Finset ℕ) (hnest : ∀ i < s, N (i + 1) ⊆ N i) (i0 : ℕ) :
    ∀ d, i0 + d ≤ s → N (i0 + d) ⊆ N i0 := by
  intro d
  induction d with
  | zero => intro _; exact subset_refl _
  | succ d ih =>
    intro hd
    exact (hnest (i0 + d) (by omega)).trans (ih (by omega))

/-- **Lemma C (nested sets without distinct representatives).** Nested subsets
`N 0 ⊇ N 1 ⊇ ... ⊇ N s` of `range t`, `t ≥ 2 s + 1`, with no system of distinct
representatives satisfy `|N 0| + ... + |N (s - 1)| + (s + 1) |N s| ≤ s t`.

Sketch. Some `i0 ≤ s` has `|N i0| ≤ s - i0`: otherwise choose representatives greedily for
`i = s, s - 1, ..., 0`, at step `i` avoiding the `s - i` chosen so far. Then `|N i| ≤ t` for
`i < i0` and `|N i| ≤ s - i0` for `i ≥ i0`, so the sum is at most
`i0 t + (s - i0)(s - i0) + (s + 1)(s - i0) = i0 t + (s - i0)(2 s + 1 - i0) ≤ s t`. -/
lemma nested_no_sdr (s t : ℕ) (ht : 2 * s + 1 ≤ t) (N : ℕ → Finset ℕ)
    (hsub : ∀ i ≤ s, N i ⊆ range t) (hnest : ∀ i < s, N (i + 1) ⊆ N i)
    (hno : ¬ ∃ c : ℕ → ℕ, (∀ i ≤ s, c i ∈ N i) ∧ ∀ i ≤ s, ∀ j ≤ s, i ≠ j → c i ≠ c j) :
    ∑ i ∈ range s, (N i).card + (s + 1) * (N s).card ≤ s * t := by
  -- some `N i0` is small
  obtain ⟨i0, hi0s, hi0⟩ : ∃ i0 ≤ s, (N i0).card ≤ s - i0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨c, hc, hinj⟩ := C_greedy s N hcon (s + 1) le_rfl
    exact hno ⟨c, fun i hi => hc i (by omega) hi,
      fun i hi j hj hij => hinj i j (by omega) hi (by omega) hj hij⟩
  -- every `N i` with `i0 ≤ i ≤ s` is small
  have hsmall : ∀ i, i0 ≤ i → i ≤ s → (N i).card ≤ s - i0 := by
    intro i h1 h2
    have := C_nest s N hnest i0 (i - i0) (by omega)
    rw [Nat.add_sub_cancel' h1] at this
    exact (card_le_card this).trans hi0
  have hle_t : ∀ i ≤ s, (N i).card ≤ t := by
    intro i hi
    have := card_le_card (hsub i hi)
    rwa [card_range] at this
  have hA : ∑ i ∈ range i0, (N i).card ≤ i0 * t := by
    calc ∑ i ∈ range i0, (N i).card ≤ ∑ _i ∈ range i0, t :=
          sum_le_sum fun i hi => hle_t i (by rw [mem_range] at hi; omega)
      _ = i0 * t := by rw [sum_const, card_range, smul_eq_mul]
  have hB : ∑ i ∈ Ico i0 s, (N i).card ≤ (s - i0) * (s - i0) := by
    calc ∑ i ∈ Ico i0 s, (N i).card ≤ ∑ _i ∈ Ico i0 s, (s - i0) :=
          sum_le_sum fun i hi => by rw [mem_Ico] at hi; exact hsmall i hi.1 (by omega)
      _ = (s - i0) * (s - i0) := by rw [sum_const, Nat.card_Ico, smul_eq_mul]
  have hsplit := sum_range_add_sum_Ico (fun i => (N i).card) hi0s
  have hS : (s + 1) * (N s).card ≤ (s + 1) * (s - i0) :=
    Nat.mul_le_mul_left _ (hsmall s hi0s le_rfl)
  -- arithmetic: `i0 t + d d + (s + 1) d ≤ s t` with `d = s - i0`
  obtain ⟨d, hd⟩ : ∃ d, s = i0 + d := ⟨s - i0, by omega⟩
  have hd' : s - i0 = d := by omega
  rw [hd'] at hB hS
  have key : d * (d + (s + 1)) ≤ d * t := Nat.mul_le_mul_left _ (by omega)
  have e1 : s * t = i0 * t + d * t := by rw [hd, Nat.add_mul]
  have e2 : d * (d + (s + 1)) = d * d + (s + 1) * d := by ring
  omega

/- Part D: `cross_dependent_bound` -/
/-- The number of permutations of `α` that carry `B` onto `A`. -/
noncomputable def D_cnt {α : Type*} [Fintype α] [DecidableEq α] (B A : Finset α) : ℕ :=
  (univ.filter (fun π : Equiv.Perm α => B.map π.toEmbedding = A)).card

/-- Two sets of the same size are carried one onto the other by a permutation. -/
lemma D_exists_perm {α : Type*} [Fintype α] [DecidableEq α] (A A' : Finset α)
    (h : A.card = A'.card) : ∃ σ : Equiv.Perm α, A.map σ.toEmbedding = A' := by
  classical
  let e : {x // x ∈ A} ≃ {x // x ∈ A'} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, h])
  refine ⟨e.extendSubtype, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    have h1 : e.extendSubtype y = e ⟨y, hy⟩ := e.extendSubtype_apply_of_mem y hy
    rw [Equiv.coe_toEmbedding, h1]
    exact (e ⟨y, hy⟩).2
  · rw [Finset.card_map, h]

/-- The count `D_cnt B A` does not depend on `A` among sets of a given size. -/
lemma D_cnt_eq {α : Type*} [Fintype α] [DecidableEq α] (B A A' : Finset α)
    (h : A.card = A'.card) : D_cnt B A = D_cnt B A' := by
  obtain ⟨σ, rfl⟩ := D_exists_perm A A' h
  unfold D_cnt
  apply Finset.card_bij (fun π _ => π.trans σ)
  · intro π hπ
    simp only [mem_filter, mem_univ, true_and] at hπ ⊢
    rw [← hπ, Finset.map_map]
    rfl
  · intro π _ π' _ hh
    ext x
    have h2 := congrArg (fun τ : Equiv.Perm α => τ x) hh
    simpa using h2
  · intro τ hτ
    simp only [mem_filter, mem_univ, true_and] at hτ
    refine ⟨τ.trans σ.symm, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]
      apply Finset.map_injective σ.toEmbedding
      rw [← hτ, Finset.map_map]
      congr 1
      ext x
      simp
    · ext x
      simp

/-- Summing `D_cnt B A` over all `l`-sets `A` counts every permutation once. -/
lemma D_cnt_sum {α : Type*} [Fintype α] [DecidableEq α] (B : Finset α) (l : ℕ)
    (hB : B.card = l) :
    ∑ A ∈ (univ : Finset α).powersetCard l, D_cnt B A = (Fintype.card α).factorial := by
  have h1 := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Equiv.Perm α)))
    (t := (univ : Finset α).powersetCard l) (f := fun π : Equiv.Perm α => B.map π.toEmbedding)
    (by
      intro π _
      exact Finset.mem_coe.mpr (Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, by rw [Finset.card_map, hB]⟩))
  rw [Finset.card_univ, Fintype.card_perm] at h1
  rw [h1]
  rfl

/-- `D_cnt B A` times the number of `l`-sets is the number of permutations. -/
lemma D_cnt_mul {α : Type*} [Fintype α] [DecidableEq α] (B A : Finset α) (l : ℕ)
    (hB : B.card = l) (hA : A.card = l) :
    D_cnt B A * (Fintype.card α).choose l = (Fintype.card α).factorial := by
  rw [← D_cnt_sum B l hB]
  have h1 : ∀ A' ∈ (univ : Finset α).powersetCard l, D_cnt B A' = D_cnt B A := by
    intro A' hA'
    exact D_cnt_eq B A' A (by rw [(Finset.mem_powersetCard.mp hA').2, hA])
  rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
    smul_eq_mul, Nat.mul_comm]

/-- The number of permutations carrying `B` into the family `F`. -/
lemma D_cnt_family {α : Type*} [Fintype α] [DecidableEq α] (B : Finset α)
    (F : Finset (Finset α)) (c : ℕ) (hc : ∀ A ∈ F, D_cnt B A = c) :
    (univ.filter (fun π : Equiv.Perm α => B.map π.toEmbedding ∈ F)).card = F.card * c := by
  have h1 := Finset.card_eq_sum_card_fiberwise
    (s := univ.filter (fun π : Equiv.Perm α => B.map π.toEmbedding ∈ F))
    (t := F) (f := fun π : Equiv.Perm α => B.map π.toEmbedding)
    (by
      intro π hπ
      exact (Finset.mem_filter.mp hπ).2)
  rw [h1]
  have h2 : ∀ A ∈ F, ((univ.filter (fun π : Equiv.Perm α => B.map π.toEmbedding ∈ F)).filter
      (fun π : Equiv.Perm α => B.map π.toEmbedding = A)).card = c := by
    intro A hA
    rw [← hc A hA]
    unfold D_cnt
    congr 1
    ext π
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h ▸ hA, h⟩
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul]

/-- Pairwise disjoint blocks of a given size. -/
lemma D_exists_blocks {α : Type*} [Fintype α] [DecidableEq α] (t l : ℕ)
    (h : t * l ≤ Fintype.card α) :
    ∃ B : ℕ → Finset α, (∀ j < t, (B j).card = l) ∧
      ∀ j < t, ∀ j' < t, j ≠ j' → Disjoint (B j) (B j') := by
  obtain ⟨f⟩ : Nonempty (Fin t × Fin l ↪ α) :=
    Function.Embedding.nonempty_of_card_le (by simpa using h)
  refine ⟨fun j => if hj : j < t then
    (univ : Finset (Fin l)).image (fun x => f (⟨j, hj⟩, x)) else ∅, ?_, ?_⟩
  · intro j hj
    simp only [dif_pos hj]
    rw [Finset.card_image_of_injective]
    · simp
    · intro x y hxy
      have := f.injective hxy
      simpa using this
  · intro j hj j' hj' hne
    simp only [dif_pos hj, dif_pos hj']
    rw [Finset.disjoint_left]
    intro a ha ha'
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, -, hy⟩ := Finset.mem_image.mp ha'
    have := f.injective hy
    simp only [Prod.mk.injEq, Fin.mk.injEq] at this
    exact hne this.1.symm

/-- Lemma D on a finite type. -/
lemma D_fintype {α : Type*} [Fintype α] [DecidableEq α] (l s : ℕ)
    (hcard : (2 * s + 1) * l ≤ Fintype.card α) (Fam : ℕ → Finset (Finset α))
    (hsub : ∀ i ≤ s, ∀ A ∈ Fam i, A.card = l) (hnest : ∀ i < s, Fam (i + 1) ⊆ Fam i)
    (hcross : ¬ ∃ g : ℕ → Finset α, (∀ i ≤ s, g i ∈ Fam i) ∧
      ∀ i ≤ s, ∀ j ≤ s, i ≠ j → Disjoint (g i) (g j)) :
    ∑ i ∈ range s, (Fam i).card + (s + 1) * (Fam s).card ≤
      s * (Fintype.card α).choose l := by
  obtain ⟨B, hBcard, hBdisj⟩ := D_exists_blocks (α := α) (2 * s + 1) l hcard
  set t := 2 * s + 1 with ht
  -- the index sets attached to a permutation
  let N : Equiv.Perm α → ℕ → Finset ℕ := fun π i =>
    (range t).filter (fun j => (B j).map π.toEmbedding ∈ Fam i)
  -- the bound of lemma C for every permutation
  have hC : ∀ π : Equiv.Perm α,
      ∑ i ∈ range s, (N π i).card + (s + 1) * (N π s).card ≤ s * t := by
    intro π
    apply nested_no_sdr s t (le_of_eq ht.symm) (N π)
    · intro i _
      exact Finset.filter_subset _ _
    · intro i hi j hj
      have hj' := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨hj'.1, hnest i hi hj'.2⟩
    · rintro ⟨c, hc, hinj⟩
      apply hcross
      refine ⟨fun i => (B (c i)).map π.toEmbedding, ?_, ?_⟩
      · intro i hi
        exact (Finset.mem_filter.mp (hc i hi)).2
      · intro i hi j hj hij
        rw [Finset.disjoint_map]
        exact hBdisj _ (Finset.mem_range.mp (Finset.mem_filter.mp (hc i hi)).1) _
          (Finset.mem_range.mp (Finset.mem_filter.mp (hc j hj)).1) (hinj i hi j hj hij)
  -- the common value of the counts
  set c := D_cnt (B 0) (B 0) with hc
  have hB0 : (B 0).card = l := hBcard 0 (by omega)
  have hcC : c * (Fintype.card α).choose l = (Fintype.card α).factorial :=
    D_cnt_mul (B 0) (B 0) l hB0 hB0
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [h0, Nat.zero_mul] at hcC
      exact absurd hcC.symm (Nat.factorial_ne_zero _)
    · exact h0
  have hChpos : 0 < (Fintype.card α).choose l := by
    rcases Nat.eq_zero_or_pos ((Fintype.card α).choose l) with h0 | h0
    · rw [h0, Nat.mul_zero] at hcC
      exact absurd hcC.symm (Nat.factorial_ne_zero _)
    · exact h0
  have hall : ∀ j < t, ∀ A : Finset α, A.card = l → D_cnt (B j) A = c := by
    intro j hj A hA
    have h1 := D_cnt_mul (B j) A l (hBcard j hj) hA
    exact Nat.eq_of_mul_eq_mul_right hChpos (h1.trans hcC.symm)
  -- the sum over all permutations of one index set
  have hsum : ∀ i ≤ s, ∑ π : Equiv.Perm α, (N π i).card = t * ((Fam i).card * c) := by
    intro i hi
    have h1 : ∀ π : Equiv.Perm α, (N π i).card =
        ∑ j ∈ range t, if (B j).map π.toEmbedding ∈ Fam i then 1 else 0 := by
      intro π
      exact Finset.card_filter _ _
    rw [Finset.sum_congr rfl (fun π _ => h1 π), Finset.sum_comm]
    have h2 : ∀ j ∈ range t, (∑ π : Equiv.Perm α,
        if (B j).map π.toEmbedding ∈ Fam i then 1 else 0) = (Fam i).card * c := by
      intro j hj
      rw [← Finset.card_filter]
      exact D_cnt_family (B j) (Fam i) c
        (fun A hA => hall j (Finset.mem_range.mp hj) A (hsub i hi A hA))
    rw [Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_range, smul_eq_mul]
  -- add the bounds of lemma C over all permutations
  have htotal : ∑ π : Equiv.Perm α, (∑ i ∈ range s, (N π i).card + (s + 1) * (N π s).card) ≤
      (Fintype.card α).factorial * (s * t) := by
    calc ∑ π : Equiv.Perm α, (∑ i ∈ range s, (N π i).card + (s + 1) * (N π s).card)
        ≤ ∑ _π : Equiv.Perm α, s * t := Finset.sum_le_sum (fun π _ => hC π)
      _ = (Fintype.card α).factorial * (s * t) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, smul_eq_mul]
  have hleft : ∑ π : Equiv.Perm α, (∑ i ∈ range s, (N π i).card + (s + 1) * (N π s).card) =
      (t * c) * (∑ i ∈ range s, (Fam i).card + (s + 1) * (Fam s).card) := by
    rw [Finset.sum_add_distrib, Finset.sum_comm, ← Finset.mul_sum, hsum s le_rfl,
      Finset.sum_congr rfl (fun i hi => hsum i (le_of_lt (Finset.mem_range.mp hi))),
      Nat.mul_add, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      ring
    · ring
  rw [hleft, ← hcC] at htotal
  have h3 : (t * c) * (∑ i ∈ range s, (Fam i).card + (s + 1) * (Fam s).card) ≤
      (t * c) * (s * (Fintype.card α).choose l) := by
    calc (t * c) * (∑ i ∈ range s, (Fam i).card + (s + 1) * (Fam s).card)
        ≤ c * (Fintype.card α).choose l * (s * t) := htotal
      _ = (t * c) * (s * (Fintype.card α).choose l) := by ring
  exact Nat.le_of_mul_le_mul_left h3 (Nat.mul_pos (by omega) hcpos)

/-- **Lemma D (nested cross-dependent families; Frankl).** Let `Fam 0 ⊇ ... ⊇ Fam s` be
families of `l`-subsets of `Y`, `|Y| ≥ (2 s + 1) l`, with no pairwise disjoint choice
`g i ∈ Fam i`. Then `|Fam 0| + ... + |Fam (s - 1)| + (s + 1) |Fam s| ≤ s C(|Y|, l)`. -/
lemma cross_dependent_bound (Y : Finset ℕ) (l s : ℕ) (hl : 1 ≤ l)
    (hY : (2 * s + 1) * l ≤ Y.card) (Fam : ℕ → Finset (Finset ℕ))
    (hsub : ∀ i ≤ s, Fam i ⊆ Y.powersetCard l) (hnest : ∀ i < s, Fam (i + 1) ⊆ Fam i)
    (hcross : ¬ ∃ g : ℕ → Finset ℕ, (∀ i ≤ s, g i ∈ Fam i) ∧
      ∀ i ≤ s, ∀ j ≤ s, i ≠ j → Disjoint (g i) (g j)) :
    ∑ i ∈ range s, (Fam i).card + (s + 1) * (Fam s).card ≤ s * Y.card.choose l := by
  classical
  let e : {x // x ∈ Y} ↪ ℕ := Function.Embedding.subtype (fun x => x ∈ Y)
  let Fam' : ℕ → Finset (Finset {x // x ∈ Y}) := fun i =>
    univ.filter (fun A => A.map e ∈ Fam i)
  have hmap : ∀ i ≤ s, (Fam' i).card = (Fam i).card := by
    intro i hi
    have h1 : (Fam' i).image (fun A => A.map e) = Fam i := by
      ext A
      constructor
      · intro hA
        obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp hA
        exact (Finset.mem_filter.mp hA').2
      · intro hA
        have hAY : A ⊆ Y := (Finset.mem_powersetCard.mp (hsub i hi hA)).1
        have h2 : (A.subtype (fun x => x ∈ Y)).map e = A :=
          Finset.subtype_map_of_mem (fun x hx => hAY hx)
        exact Finset.mem_image.mpr
          ⟨A.subtype (fun x => x ∈ Y), Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [h2]; exact hA⟩, h2⟩
    rw [← h1, Finset.card_image_of_injective _ (Finset.map_injective e)]
  have hmain := D_fintype (α := {x // x ∈ Y}) l s (by rw [Fintype.card_coe]; exact hY) Fam'
    (by
      intro i hi A hA
      have h1 := (Finset.mem_powersetCard.mp (hsub i hi (Finset.mem_filter.mp hA).2)).2
      rwa [Finset.card_map] at h1)
    (by
      intro i hi A hA
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnest i hi (Finset.mem_filter.mp hA).2⟩)
    (by
      rintro ⟨g, hg, hdisj⟩
      apply hcross
      refine ⟨fun i => (g i).map e, fun i hi => (Finset.mem_filter.mp (hg i hi)).2, ?_⟩
      intro i hi j hj hij
      rw [Finset.disjoint_map]
      exact hdisj i hi j hj hij)
  rw [Fintype.card_coe, hmap s le_rfl,
    Finset.sum_congr rfl (fun i hi => hmap i (le_of_lt (Finset.mem_range.mp hi)))] at hmain
  exact hmain

/- Part E: `trace_split` -/
/-- A set meeting `T` exactly in `{i}` is `insert i (A \ T)`. -/
lemma E_eq_insert (T A : Finset ℕ) (i : ℕ) (h : A ∩ T = {i}) : A = insert i (A \ T) := by
  have hi : i ∈ A ∩ T := by rw [h]; exact mem_singleton_self i
  ext x
  simp only [mem_insert, mem_sdiff]
  constructor
  · intro hx
    by_cases hxT : x ∈ T
    · left
      have hx' : x ∈ A ∩ T := mem_inter.mpr ⟨hx, hxT⟩
      rw [h] at hx'
      exact mem_singleton.mp hx'
    · exact Or.inr ⟨hx, hxT⟩
  · rintro (rfl | ⟨hx, -⟩)
    · exact (mem_inter.mp hi).1
    · exact hx

/-- For `i ∈ T` and `B` disjoint from `T`, the set `insert i B` has trace `{i}` on `T` and
remainder `B`. -/
lemma E_trace_insert (T B : Finset ℕ) (i : ℕ) (hi : i ∈ T) (hB : Disjoint B T) :
    insert i B ∩ T = {i} ∧ insert i B \ T = B := by
  constructor
  · ext x
    simp only [mem_inter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨rfl | hx, hxT⟩
      · rfl
      · exact absurd hxT (disjoint_left.mp hB hx)
    · rintro rfl
      exact ⟨Or.inl rfl, hi⟩
  · ext x
    simp only [mem_sdiff, mem_insert]
    constructor
    · rintro ⟨rfl | hx, hxT⟩
      · exact absurd hi hxT
      · exact hx
    · intro hx
      exact ⟨Or.inr hx, disjoint_left.mp hB hx⟩

/-- Membership in the family of remainders of the members with trace `{i}`. -/
lemma E_mem_fam (s : ℕ) (F : Finset (Finset ℕ)) (i : ℕ) (hi : i ≤ s) (B : Finset ℕ) :
    B ∈ (F.filter (fun A => A ∩ range (s + 1) = {i})).image (fun A => A \ range (s + 1)) ↔
      Disjoint B (range (s + 1)) ∧ insert i B ∈ F := by
  have hiT : i ∈ range (s + 1) := mem_range.mpr (by omega)
  constructor
  · intro h
    obtain ⟨A, hA, rfl⟩ := mem_image.mp h
    obtain ⟨hAF, hAt⟩ := mem_filter.mp hA
    refine ⟨sdiff_disjoint, ?_⟩
    rw [← E_eq_insert _ A i hAt]
    exact hAF
  · rintro ⟨hd, hB⟩
    obtain ⟨h1, h2⟩ := E_trace_insert (range (s + 1)) B i hiT hd
    exact mem_image.mpr ⟨insert i B, mem_filter.mpr ⟨hB, h1⟩, h2⟩

/-- **Lemma E (split by the trace on the first `s + 1` points).** For a shifted family `F` of
`r`-subsets of `range n` with no `s + 1` pairwise disjoint members, with `T = range (s + 1)`:
`F0 = {A ∈ F | A ∩ T = ∅}` and `Fam i = {A \ T | A ∈ F, A ∩ T = {i}}` have the listed
properties. -/
lemma trace_split (n r s : ℕ) (hr : 1 ≤ r) (F : Finset (Finset ℕ))
    (hF : F ⊆ (range n).powersetCard r) (hsh : Shifted 0 F)
    (hM : ¬ F.HasHypergraphMatching (s + 1)) :
    ∃ (F0 : Finset (Finset ℕ)) (Fam : ℕ → Finset (Finset ℕ)),
      F0 ⊆ (Ico (s + 1) n).powersetCard r ∧ Shifted (s + 1) F0 ∧
      ¬ F0.HasHypergraphMatching (s + 1) ∧ ∂ F0 ⊆ Fam s ∧
      (∀ i ≤ s, Fam i ⊆ (Ico (s + 1) n).powersetCard (r - 1)) ∧
      (∀ i < s, Fam (i + 1) ⊆ Fam i) ∧
      (¬ ∃ g : ℕ → Finset ℕ, (∀ i ≤ s, g i ∈ Fam i) ∧
        ∀ i ≤ s, ∀ j ≤ s, i ≠ j → Disjoint (g i) (g j)) ∧
      F.card ≤ (((range n).powersetCard r).filter
          (fun A => 2 ≤ (A ∩ range (s + 1)).card)).card + F0.card +
        ∑ i ∈ range (s + 1), (Fam i).card := by
  classical
  refine ⟨F.filter (fun A => Disjoint A (range (s + 1))),
    fun i => (F.filter (fun A => A ∩ range (s + 1) = {i})).image (fun A => A \ range (s + 1)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `F0` consists of `r`-subsets of `Ico (s + 1) n`
    intro A hA
    obtain ⟨hAF, hd⟩ := mem_filter.mp hA
    obtain ⟨hAn, hAc⟩ := mem_powersetCard.mp (hF hAF)
    refine mem_powersetCard.mpr ⟨fun x hx => ?_, hAc⟩
    have h1 := mem_range.mp (hAn hx)
    have h2 : x ∉ range (s + 1) := disjoint_left.mp hd hx
    rw [mem_range] at h2
    exact mem_Ico.mpr ⟨by omega, h1⟩
  · -- `F0` is shifted from `s + 1` on
    intro A hA j hj i hi hij hiA
    obtain ⟨hAF, hd⟩ := mem_filter.mp hA
    refine mem_filter.mpr ⟨hsh A hAF j hj i (Nat.zero_le _) hij hiA, ?_⟩
    rw [disjoint_insert_left]
    refine ⟨?_, hd.mono_left (erase_subset _ _)⟩
    rw [mem_range]
    omega
  · -- `F0` has no `s + 1` pairwise disjoint members
    rintro ⟨M, hM1, hM2, hM3⟩
    exact hM ⟨M, hM1.trans (filter_subset _ _), hM2, hM3⟩
  · -- the shadow of `F0` lies in `Fam s`
    intro B hB
    obtain ⟨A, hA, x, hx, rfl⟩ := mem_shadow_iff.mp hB
    obtain ⟨hAF, hd⟩ := mem_filter.mp hA
    have hxT : x ∉ range (s + 1) := disjoint_left.mp hd hx
    have hsT : s ∈ range (s + 1) := mem_range.mpr (Nat.lt_succ_self s)
    rw [mem_range] at hxT
    refine (E_mem_fam s F s le_rfl _).mpr
      ⟨hd.mono_left (erase_subset _ _), hsh A hAF x hx s (Nat.zero_le _) (by omega) ?_⟩
    exact fun h => disjoint_left.mp hd h hsT
  · -- `Fam i` consists of `(r - 1)`-subsets of `Ico (s + 1) n`
    intro i hi B hB
    obtain ⟨hd, hBF⟩ := (E_mem_fam s F i hi B).mp hB
    obtain ⟨hn, hc⟩ := mem_powersetCard.mp (hF hBF)
    have hiB : i ∉ B := fun h => disjoint_left.mp hd h (mem_range.mpr (by omega))
    rw [card_insert_of_notMem hiB] at hc
    refine mem_powersetCard.mpr ⟨fun x hx => ?_, by omega⟩
    have h1 := mem_range.mp (hn (mem_insert_of_mem hx))
    have h2 : x ∉ range (s + 1) := disjoint_left.mp hd hx
    rw [mem_range] at h2
    exact mem_Ico.mpr ⟨by omega, h1⟩
  · -- nested
    intro i hi B hB
    obtain ⟨hd, hBF⟩ := (E_mem_fam s F (i + 1) (by omega) B).mp hB
    refine (E_mem_fam s F i (by omega) B).mpr ⟨hd, ?_⟩
    have h1 : i + 1 ∉ B := fun h => disjoint_left.mp hd h (mem_range.mpr (by omega))
    have h0 : i ∉ B := fun h => disjoint_left.mp hd h (mem_range.mpr (by omega))
    have h3 : i ∉ insert (i + 1) B := by
      rw [mem_insert]
      rintro (h | h)
      · omega
      · exact h0 h
    have h2 := hsh _ hBF (i + 1) (mem_insert_self _ _) i (Nat.zero_le _) (Nat.lt_succ_self i) h3
    rwa [erase_insert h1] at h2
  · -- cross-dependent
    rintro ⟨g, hg, hdis⟩
    apply hM
    have hg' : ∀ i ≤ s, Disjoint (g i) (range (s + 1)) ∧ insert i (g i) ∈ F :=
      fun i hi => (E_mem_fam s F i hi (g i)).mp (hg i hi)
    have hnot : ∀ i ≤ s, ∀ j ≤ s, i ∉ g j := fun i hi j hj h =>
      disjoint_left.mp (hg' j hj).1 h (mem_range.mpr (by omega))
    have hle : ∀ i ∈ range (s + 1), i ≤ s := fun i hi => by
      have := mem_range.mp hi
      omega
    have hinj : Set.InjOn (fun i => insert i (g i)) (range (s + 1) : Set ℕ) := by
      intro i hi j hj h
      have hi' : i ≤ s := hle i (mem_coe.mp hi)
      have hj' : j ≤ s := hle j (mem_coe.mp hj)
      have h' : insert i (g i) = insert j (g j) := h
      have hmem : i ∈ insert j (g j) := by
        rw [← h']
        exact mem_insert_self _ _
      rcases mem_insert.mp hmem with h | h
      · exact h
      · exact absurd h (hnot i hi' j hj')
    refine ⟨(range (s + 1)).image (fun i => insert i (g i)), ?_, ?_, ?_⟩
    · intro A hA
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hA
      exact (hg' i (hle i hi)).2
    · rw [card_image_of_injOn hinj, card_range]
    · intro A hA A' hA' hne
      obtain ⟨i, hi, rfl⟩ := mem_image.mp (mem_coe.mp hA)
      obtain ⟨j, hj, rfl⟩ := mem_image.mp (mem_coe.mp hA')
      have hi' : i ≤ s := hle i hi
      have hj' : j ≤ s := hle j hj
      have hij : i ≠ j := fun h => hne (by rw [h])
      show Disjoint (insert i (g i)) (insert j (g j))
      rw [disjoint_insert_left, disjoint_insert_right, mem_insert]
      exact ⟨fun h => h.elim hij (hnot i hi' j hj'), hnot j hj' i hi', hdis i hi' j hj' hij⟩
  · -- counting
    have hcover : F ⊆ (((range n).powersetCard r).filter
          (fun A => 2 ≤ (A ∩ range (s + 1)).card)) ∪
        F.filter (fun A => Disjoint A (range (s + 1))) ∪
        (range (s + 1)).biUnion (fun i => F.filter (fun A => A ∩ range (s + 1) = {i})) := by
      intro A hA
      rcases Nat.lt_or_ge (A ∩ range (s + 1)).card 2 with h | h
      · have h01 : (A ∩ range (s + 1)).card = 0 ∨ (A ∩ range (s + 1)).card = 1 := by omega
        rcases h01 with h0 | h1
        · apply mem_union_left
          apply mem_union_right
          exact mem_filter.mpr ⟨hA, disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp h0)⟩
        · apply mem_union_right
          obtain ⟨i, hi⟩ := card_eq_one.mp h1
          have hmem : i ∈ A ∩ range (s + 1) := by
            rw [hi]
            exact mem_singleton_self i
          exact mem_biUnion.mpr ⟨i, (mem_inter.mp hmem).2, mem_filter.mpr ⟨hA, hi⟩⟩
      · apply mem_union_left
        apply mem_union_left
        exact mem_filter.mpr ⟨hF hA, h⟩
    have hcard : ∀ i, (F.filter (fun A => A ∩ range (s + 1) = {i})).card =
        ((F.filter (fun A => A ∩ range (s + 1) = {i})).image
          (fun A => A \ range (s + 1))).card := by
      intro i
      symm
      apply card_image_of_injOn
      intro A hA A' hA' h
      have h1 := (mem_filter.mp (mem_coe.mp hA)).2
      have h2 := (mem_filter.mp (mem_coe.mp hA')).2
      have h' : A \ range (s + 1) = A' \ range (s + 1) := h
      calc A = insert i (A \ range (s + 1)) := E_eq_insert _ A i h1
        _ = insert i (A' \ range (s + 1)) := by rw [h']
        _ = A' := (E_eq_insert _ A' i h2).symm
    have k1 := card_le_card hcover
    have k2 := card_union_le
      ((((range n).powersetCard r).filter (fun A => 2 ≤ (A ∩ range (s + 1)).card)) ∪
        F.filter (fun A => Disjoint A (range (s + 1))))
      ((range (s + 1)).biUnion (fun i => F.filter (fun A => A ∩ range (s + 1) = {i})))
    have k3 := card_union_le
      (((range n).powersetCard r).filter (fun A => 2 ≤ (A ∩ range (s + 1)).card))
      (F.filter (fun A => Disjoint A (range (s + 1))))
    have k4 : ((range (s + 1)).biUnion
        (fun i => F.filter (fun A => A ∩ range (s + 1) = {i}))).card ≤
        ∑ i ∈ range (s + 1), (F.filter (fun A => A ∩ range (s + 1) = {i})).card :=
      card_biUnion_le
    have k5 : ∑ i ∈ range (s + 1), (F.filter (fun A => A ∩ range (s + 1) = {i})).card =
        ∑ i ∈ range (s + 1), ((F.filter (fun A => A ∩ range (s + 1) = {i})).image
          (fun A => A \ range (s + 1))).card :=
      sum_congr rfl (fun i _ => hcard i)
    beta_reduce
    omega

/- Part B: `shadow_bound` -/
/-- Having no `k` pairwise disjoint members passes to subfamilies. -/
lemma B_no_matching_mono {F F' : Finset (Finset ℕ)} (k : ℕ) (h : F' ⊆ F)
    (hM : ¬ F.HasHypergraphMatching k) : ¬ F'.HasHypergraphMatching k := by
  rintro ⟨M, hMF, hMc, hMd⟩
  exact hM ⟨M, hMF.trans h, hMc, hMd⟩

/-- The case `r = 1`: the members are pairwise disjoint singletons. -/
lemma B_r_one (s : ℕ) (X : Finset ℕ) (F : Finset (Finset ℕ))
    (hF : F ⊆ X.powersetCard 1) (hM : ¬ F.HasHypergraphMatching (s + 1)) :
    F.card ≤ s * (∂ F).card := by
  rcases F.eq_empty_or_nonempty with rfl | ⟨A, hA⟩
  · simp
  have hcard : F.card ≤ s := by
    by_contra h
    obtain ⟨M, hMF, hMc⟩ := Finset.exists_subset_card_eq (show s + 1 ≤ F.card by omega)
    apply hM
    refine ⟨M, hMF, hMc, ?_⟩
    intro B hB C hC hne
    obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp (Finset.mem_powersetCard.mp (hF (hMF hB))).2
    obtain ⟨c, rfl⟩ := Finset.card_eq_one.mp (Finset.mem_powersetCard.mp (hF (hMF hC))).2
    rw [Finset.disjoint_singleton]
    rintro rfl
    exact hne rfl
  have hsh : 1 ≤ (∂ F).card := by
    rw [Finset.one_le_card]
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp (Finset.mem_powersetCard.mp (hF hA)).2
    exact ⟨({a} : Finset ℕ).erase a,
      Finset.mem_shadow_iff.mpr ⟨{a}, hA, a, Finset.mem_singleton_self a, rfl⟩⟩
  calc F.card ≤ s * 1 := by omega
    _ ≤ s * (∂ F).card := Nat.mul_le_mul_left s hsh

/-- The case of a small ground set: double counting of pairs `B ⊂ A`. -/
lemma B_double_count (m N r s : ℕ) (hr : 1 ≤ r) (F : Finset (Finset ℕ))
    (hF : F ⊆ (Ico m N).powersetCard r) (hg : N - m + 1 ≤ r * (s + 1)) :
    F.card ≤ s * (∂ F).card := by
  have key : F.card * r ≤ (∂ F).card * (r * s) := by
    refine Finset.card_mul_le_card_mul (fun (A B : Finset ℕ) => B ⊆ A) ?_ ?_
    · intro A hA
      have hAc := (Finset.mem_powersetCard.mp (hF hA)).2
      have hsub : A.image (fun x => A.erase x) ⊆
          (∂ F).bipartiteAbove (fun (A B : Finset ℕ) => B ⊆ A) A := by
        intro B hB
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hB
        exact (Finset.mem_bipartiteAbove _).mpr
          ⟨Finset.mem_shadow_iff.mpr ⟨A, hA, x, hx, rfl⟩, Finset.erase_subset x A⟩
      have hinj : Set.InjOn (fun x => A.erase x) (A : Set ℕ) := by
        intro x hx y hy h
        by_contra hne
        have h1 : x ∈ A.erase y := Finset.mem_erase.mpr ⟨hne, hx⟩
        have h2 : A.erase x = A.erase y := h
        rw [← h2] at h1
        exact Finset.notMem_erase x A h1
      calc r = (A.image (fun x => A.erase x)).card := by
            rw [Finset.card_image_of_injOn hinj, hAc]
        _ ≤ _ := Finset.card_le_card hsub
    · intro B hB
      obtain ⟨A', hA', a, ha, rfl⟩ := Finset.mem_shadow_iff.mp hB
      obtain ⟨hA'sub, hA'c⟩ := Finset.mem_powersetCard.mp (hF hA')
      have hBc : (A'.erase a).card = r - 1 := by rw [Finset.card_erase_of_mem ha, hA'c]
      have hBsub : A'.erase a ⊆ Ico m N := (Finset.erase_subset _ _).trans hA'sub
      have hsub : F.bipartiteBelow (fun (A B : Finset ℕ) => B ⊆ A) (A'.erase a) ⊆
          (Ico m N \ A'.erase a).image (fun x => insert x (A'.erase a)) := by
        intro A hA
        obtain ⟨hAF, hBA⟩ := (Finset.mem_bipartiteBelow _).mp hA
        obtain ⟨hAsub, hAc⟩ := Finset.mem_powersetCard.mp (hF hAF)
        have h1 : (A \ A'.erase a).card = 1 := by
          rw [Finset.card_sdiff_of_subset hBA, hAc, hBc]; omega
        obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
        have hxm : x ∈ A \ A'.erase a := by rw [hx]; exact Finset.mem_singleton_self x
        rw [Finset.mem_sdiff] at hxm
        refine Finset.mem_image.mpr ⟨x, Finset.mem_sdiff.mpr ⟨hAsub hxm.1, hxm.2⟩, ?_⟩
        show insert x (A'.erase a) = A
        rw [Finset.insert_eq, ← hx, Finset.sdiff_union_of_subset hBA]
      calc (F.bipartiteBelow (fun (A B : Finset ℕ) => B ⊆ A) (A'.erase a)).card
          ≤ ((Ico m N \ A'.erase a).image (fun x => insert x (A'.erase a))).card :=
            Finset.card_le_card hsub
        _ ≤ (Ico m N \ A'.erase a).card := Finset.card_image_le
        _ = (N - m) - (r - 1) := by
            rw [Finset.card_sdiff_of_subset hBsub, Nat.card_Ico, hBc]
        _ ≤ r * s := by
            have e : r * (s + 1) = r * s + r := by ring
            omega
  have key' : r * F.card ≤ r * (s * (∂ F).card) := by
    calc r * F.card = F.card * r := by ring
      _ ≤ (∂ F).card * (r * s) := key
      _ = r * (s * (∂ F).card) := by ring
  exact Nat.le_of_mul_le_mul_left key' hr

/-- Membership in the link `F1 = {A.erase N | N ∈ A ∈ F}`. -/
lemma B_mem_F1 (F : Finset (Finset ℕ)) (N : ℕ) (G : Finset ℕ) :
    G ∈ (F.filter (fun A => N ∈ A)).image (fun A => A.erase N) ↔
      N ∉ G ∧ insert N G ∈ F := by
  constructor
  · intro h
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hAF, hNA⟩ := Finset.mem_filter.mp hA
    exact ⟨Finset.notMem_erase N A, by rwa [Finset.insert_erase hNA]⟩
  · rintro ⟨h1, h2⟩
    exact Finset.mem_image.mpr
      ⟨insert N G, Finset.mem_filter.mpr ⟨h2, Finset.mem_insert_self N G⟩,
        Finset.erase_insert h1⟩

lemma B_F0_sub (m N r : ℕ) (F : Finset (Finset ℕ))
    (hF : F ⊆ (Ico m (N + 1)).powersetCard r) :
    F.filter (fun A => N ∉ A) ⊆ (Ico m N).powersetCard r := by
  intro A hA
  obtain ⟨hAF, hNA⟩ := Finset.mem_filter.mp hA
  obtain ⟨h1, h2⟩ := Finset.mem_powersetCard.mp (hF hAF)
  refine Finset.mem_powersetCard.mpr ⟨fun y hy => ?_, h2⟩
  have h3 := h1 hy
  rw [Finset.mem_Ico] at h3 ⊢
  have h4 : y ≠ N := fun h => hNA (h ▸ hy)
  omega

lemma B_F0_shifted (m N r : ℕ) (F : Finset (Finset ℕ))
    (hF : F ⊆ (Ico m (N + 1)).powersetCard r) (hsh : Shifted m F) :
    Shifted m (F.filter (fun A => N ∉ A)) := by
  intro A hA j hj i hmi hij hiA
  obtain ⟨hAF, hNA⟩ := Finset.mem_filter.mp hA
  refine Finset.mem_filter.mpr ⟨hsh A hAF j hj i hmi hij hiA, ?_⟩
  have h1 := (Finset.mem_powersetCard.mp (hF hAF)).1 hj
  rw [Finset.mem_Ico] at h1
  rw [Finset.mem_insert, Finset.mem_erase]
  rintro (h | h)
  · omega
  · exact hNA h.2

lemma B_F1_sub (m N r : ℕ) (F : Finset (Finset ℕ))
    (hF : F ⊆ (Ico m (N + 1)).powersetCard r) :
    (F.filter (fun A => N ∈ A)).image (fun A => A.erase N) ⊆
      (Ico m N).powersetCard (r - 1) := by
  intro G hG
  rw [B_mem_F1] at hG
  obtain ⟨hNG, hGF⟩ := hG
  obtain ⟨h1, h2⟩ := Finset.mem_powersetCard.mp (hF hGF)
  rw [Finset.card_insert_of_notMem hNG] at h2
  refine Finset.mem_powersetCard.mpr ⟨fun y hy => ?_, by omega⟩
  have h3 := h1 (Finset.mem_insert_of_mem hy)
  rw [Finset.mem_Ico] at h3 ⊢
  have h4 : y ≠ N := fun h => hNG (h ▸ hy)
  omega

lemma B_F1_shifted (m N r : ℕ) (F : Finset (Finset ℕ))
    (hF : F ⊆ (Ico m (N + 1)).powersetCard r) (hsh : Shifted m F) :
    Shifted m ((F.filter (fun A => N ∈ A)).image (fun A => A.erase N)) := by
  intro G hG j hj i hmi hij hiG
  rw [B_mem_F1] at hG ⊢
  obtain ⟨hNG, hGF⟩ := hG
  have hjN : j < N := by
    have h1 := (Finset.mem_powersetCard.mp (hF hGF)).1 (Finset.mem_insert_of_mem hj)
    rw [Finset.mem_Ico] at h1
    have h2 : j ≠ N := fun h => hNG (h ▸ hj)
    omega
  refine ⟨?_, ?_⟩
  · rw [Finset.mem_insert, Finset.mem_erase]
    rintro (h | h)
    · omega
    · exact hNG h.2
  · have h1 := hsh (insert N G) hGF j (Finset.mem_insert_of_mem hj) i hmi hij (by
      rw [Finset.mem_insert]
      rintro (h | h)
      · omega
      · exact hiG h)
    have e : insert N (insert i (G.erase j)) = insert i ((insert N G).erase j) := by
      rw [Finset.erase_insert_of_ne (by omega : N ≠ j), Finset.insert_comm N i]
    rw [e]
    exact h1

/-- Lifting a matching of the link to a matching of `F`, given enough free points. -/
lemma B_lift (m N s : ℕ) (F M : Finset (Finset ℕ)) (T : Finset ℕ) (hsh : Shifted m F)
    (hMc : M.card = s + 1) (hMd : (M : Set (Finset ℕ)).Pairwise Disjoint)
    (hMF : ∀ G ∈ M, N ∉ G ∧ insert N G ∈ F)
    (hT : ∀ t ∈ T, m ≤ t ∧ t < N ∧ ∀ G ∈ M, t ∉ G) (hTc : s ≤ T.card) :
    F.HasHypergraphMatching (s + 1) := by
  classical
  obtain ⟨G0, hG0⟩ : M.Nonempty := Finset.card_pos.mp (by omega)
  have hc : Fintype.card ↥(M.erase G0) ≤ T.card := by
    rw [Fintype.card_coe, Finset.card_erase_of_mem hG0]; omega
  obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset hc
  let p : Finset ℕ → ℕ := fun G => if h : G ∈ M.erase G0 then f ⟨G, h⟩ else N
  have hpT : ∀ G, G ∈ M.erase G0 → p G ∈ T := by
    intro G h
    simp only [p, dif_pos h]
    exact hf (Set.mem_range_self _)
  have hpN : ∀ G, G ∉ M.erase G0 → p G = N := by
    intro G h
    simp only [p, dif_neg h]
  have hpinj : ∀ G ∈ M, ∀ G' ∈ M, p G = p G' → G = G' := by
    intro G hG G' hG' h
    by_cases h1 : G ∈ M.erase G0 <;> by_cases h2 : G' ∈ M.erase G0
    · simp only [p, dif_pos h1, dif_pos h2] at h
      exact congrArg Subtype.val (f.injective h)
    · have h3 := hpT G h1
      rw [h, hpN G' h2] at h3
      exact absurd (hT N h3).2.1 (lt_irrefl N)
    · have h3 := hpT G' h2
      rw [← h, hpN G h1] at h3
      exact absurd (hT N h3).2.1 (lt_irrefl N)
    · have e1 : G = G0 := by
        by_contra hne
        exact h1 (Finset.mem_erase.mpr ⟨hne, hG⟩)
      have e2 : G' = G0 := by
        by_contra hne
        exact h2 (Finset.mem_erase.mpr ⟨hne, hG'⟩)
      rw [e1, e2]
  have hpmem : ∀ G ∈ M, insert (p G) G ∈ F := by
    intro G hG
    by_cases h1 : G ∈ M.erase G0
    · have ht := hT _ (hpT G h1)
      have h2 := hsh (insert N G) (hMF G hG).2 N (Finset.mem_insert_self _ _) (p G) ht.1
        ht.2.1 (by
          rw [Finset.mem_insert]
          rintro (h | h)
          · omega
          · exact ht.2.2 G hG h)
      rwa [Finset.erase_insert (hMF G hG).1] at h2
    · rw [hpN G h1]
      exact (hMF G hG).2
  have hpnot : ∀ G ∈ M, ∀ G' ∈ M, p G ∉ G' := by
    intro G hG G' hG'
    by_cases h1 : G ∈ M.erase G0
    · exact (hT _ (hpT G h1)).2.2 G' hG'
    · rw [hpN G h1]
      exact (hMF G' hG').1
  have hdisj : ∀ G ∈ M, ∀ G' ∈ M, G ≠ G' →
      Disjoint (insert (p G) G) (insert (p G') G') := by
    intro G hG G' hG' hne
    rw [Finset.disjoint_insert_left, Finset.disjoint_insert_right, Finset.mem_insert]
    refine ⟨?_, hpnot G' hG' G hG, hMd (Finset.mem_coe.mpr hG) (Finset.mem_coe.mpr hG') hne⟩
    rintro (h | h)
    · exact hne (hpinj G hG G' hG' h)
    · exact hpnot G hG G' hG' h
  have hinj : Set.InjOn (fun G => insert (p G) G) (M : Set (Finset ℕ)) := by
    intro G hG G' hG' h
    by_contra hne
    have h1 := hdisj G (Finset.mem_coe.mp hG) G' (Finset.mem_coe.mp hG') hne
    have h2 : insert (p G) G = insert (p G') G' := h
    rw [← h2, Finset.disjoint_self_iff_empty] at h1
    exact Finset.insert_ne_empty _ _ h1
  refine ⟨M.image (fun G => insert (p G) G), ?_, ?_, ?_⟩
  · intro X hX
    obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hX
    exact hpmem G hG
  · rw [Finset.card_image_of_injOn hinj, hMc]
  · intro X hX Y hY hXY
    obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hX)
    obtain ⟨G', hG', rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hY)
    exact hdisj G hG G' hG' (fun h => hXY (by rw [h]))

/-- On a large ground set the link has no `s + 1` pairwise disjoint members. -/
lemma B_F1_no_matching (m N r s : ℕ) (hr : 1 ≤ r) (F : Finset (Finset ℕ))
    (hF : F ⊆ (Ico m (N + 1)).powersetCard r) (hsh : Shifted m F)
    (hbig : r * (s + 1) ≤ N + 1 - m) (hM : ¬ F.HasHypergraphMatching (s + 1)) :
    ¬ ((F.filter (fun A => N ∈ A)).image
      (fun A => A.erase N)).HasHypergraphMatching (s + 1) := by
  rintro ⟨M, hMF, hMc, hMd⟩
  apply hM
  have hmem : ∀ G ∈ M, N ∉ G ∧ insert N G ∈ F := fun G hG => (B_mem_F1 F N G).mp (hMF hG)
  have hcardG : ∀ G ∈ M, (id G : Finset ℕ).card ≤ r - 1 := by
    intro G hG
    have h1 := (Finset.mem_powersetCard.mp (hF (hmem G hG).2)).2
    rw [Finset.card_insert_of_notMem (hmem G hG).1] at h1
    simp only [id]
    omega
  have hU : (M.biUnion id).card ≤ (s + 1) * (r - 1) := by
    have h1 := Finset.card_biUnion_le_card_mul M id (r - 1) hcardG
    rwa [hMc] at h1
  refine B_lift m N s F M (Ico m N \ M.biUnion id) hsh hMc hMd hmem ?_ ?_
  · intro t ht
    rw [Finset.mem_sdiff, Finset.mem_Ico] at ht
    exact ⟨ht.1.1, ht.1.2, fun G hG htG => ht.2 (Finset.mem_biUnion.mpr ⟨G, hG, htG⟩)⟩
  · have h1 := Finset.le_card_sdiff (M.biUnion id) (Ico m N)
    rw [Nat.card_Ico] at h1
    obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
    have e : (q + 1) * (s + 1) = (s + 1) * q + s + 1 := by ring
    rw [e] at hbig
    rw [Nat.add_sub_cancel] at hU
    omega

/-- The shadow of `F` contains the shadow of `F0` and a disjoint copy of the shadow of the
link. -/
lemma B_shadow_split (N : ℕ) (F : Finset (Finset ℕ)) :
    (∂ (F.filter (fun A => N ∉ A))).card +
      (∂ ((F.filter (fun A => N ∈ A)).image (fun A => A.erase N))).card ≤ (∂ F).card := by
  have hN1 : ∀ H ∈ ∂ ((F.filter (fun A => N ∈ A)).image (fun A => A.erase N)), N ∉ H := by
    intro H hH
    obtain ⟨G, hG, y, hy, rfl⟩ := Finset.mem_shadow_iff.mp hH
    rw [B_mem_F1] at hG
    exact fun h => hG.1 (Finset.mem_of_mem_erase h)
  have hinj : Set.InjOn (fun H : Finset ℕ => insert N H)
      (∂ ((F.filter (fun A => N ∈ A)).image (fun A => A.erase N)) : Set (Finset ℕ)) := by
    intro H hH H' hH' h
    have h2 : insert N H = insert N H' := h
    calc H = (insert N H).erase N := (Finset.erase_insert (hN1 H (Finset.mem_coe.mp hH))).symm
      _ = (insert N H').erase N := by rw [h2]
      _ = H' := Finset.erase_insert (hN1 H' (Finset.mem_coe.mp hH'))
  have hdisj : Disjoint (∂ (F.filter (fun A => N ∉ A)))
      ((∂ ((F.filter (fun A => N ∈ A)).image (fun A => A.erase N))).image
        (fun H => insert N H)) := by
    rw [Finset.disjoint_left]
    intro H hH0 hH1
    obtain ⟨H', -, rfl⟩ := Finset.mem_image.mp hH1
    obtain ⟨A, hA, y, hy, h⟩ := Finset.mem_shadow_iff.mp hH0
    have hNA := (Finset.mem_filter.mp hA).2
    have h3 : N ∈ A.erase y := by
      rw [h]
      exact Finset.mem_insert_self N H'
    exact hNA (Finset.mem_of_mem_erase h3)
  have hsub : ∂ (F.filter (fun A => N ∉ A)) ∪
      (∂ ((F.filter (fun A => N ∈ A)).image (fun A => A.erase N))).image
        (fun H => insert N H) ⊆ ∂ F := by
    apply Finset.union_subset
    · exact Finset.shadow_monotone (Finset.filter_subset _ _)
    · intro X hX
      obtain ⟨H, hH, rfl⟩ := Finset.mem_image.mp hX
      obtain ⟨G, hG, y, hy, rfl⟩ := Finset.mem_shadow_iff.mp hH
      rw [B_mem_F1] at hG
      have hne : N ≠ y := fun h => hG.1 (h ▸ hy)
      show insert N (G.erase y) ∈ ∂ F
      rw [← Finset.erase_insert_of_ne hne]
      exact Finset.mem_shadow_iff.mpr ⟨insert N G, hG.2, y, Finset.mem_insert_of_mem hy, rfl⟩
  calc (∂ (F.filter (fun A => N ∉ A))).card +
        (∂ ((F.filter (fun A => N ∈ A)).image (fun A => A.erase N))).card
      = (∂ (F.filter (fun A => N ∉ A)) ∪
          (∂ ((F.filter (fun A => N ∈ A)).image (fun A => A.erase N))).image
            (fun H => insert N H)).card := by
        rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj]
    _ ≤ (∂ F).card := Finset.card_le_card hsub

/-- The shadow bound, in the form used for the induction on `N`. -/
lemma B_main (m s : ℕ) : ∀ (N r : ℕ), 1 ≤ r → ∀ F : Finset (Finset ℕ),
    F ⊆ (Ico m N).powersetCard r → Shifted m F → ¬ F.HasHypergraphMatching (s + 1) →
    F.card ≤ s * (∂ F).card := by
  intro N
  induction N with
  | zero =>
    intro r hr F hF _ _
    refine B_double_count m 0 r s hr F hF ?_
    have h1 : 1 ≤ r * (s + 1) := Nat.mul_pos hr (Nat.succ_pos s)
    omega
  | succ N ih =>
    intro r hr F hF hsh hM
    by_cases hg : N + 1 - m + 1 ≤ r * (s + 1)
    · exact B_double_count m (N + 1) r s hr F hF hg
    by_cases hr1 : r = 1
    · subst hr1
      exact B_r_one s _ F hF hM
    have hbig : r * (s + 1) ≤ N + 1 - m := by omega
    have h0 := ih r hr _ (B_F0_sub m N r F hF) (B_F0_shifted m N r F hF hsh)
      (B_no_matching_mono (s + 1) (Finset.filter_subset _ _) hM)
    have h1 := ih (r - 1) (by omega) _ (B_F1_sub m N r F hF) (B_F1_shifted m N r F hF hsh)
      (B_F1_no_matching m N r s hr F hF hsh hbig hM)
    have hsplit := Nat.mul_le_mul_left s (B_shadow_split N F)
    rw [Nat.mul_add] at hsplit
    have hinj : Set.InjOn (fun A : Finset ℕ => A.erase N)
        (F.filter (fun A => N ∈ A) : Set (Finset ℕ)) := by
      intro A hA A' hA' h
      have hNA := (Finset.mem_filter.mp (Finset.mem_coe.mp hA)).2
      have hNA' := (Finset.mem_filter.mp (Finset.mem_coe.mp hA')).2
      have h2 : A.erase N = A'.erase N := h
      calc A = insert N (A.erase N) := (Finset.insert_erase hNA).symm
        _ = insert N (A'.erase N) := by rw [h2]
        _ = A' := Finset.insert_erase hNA'
    have hc : F.card = (F.filter (fun A => N ∉ A)).card +
        ((F.filter (fun A => N ∈ A)).image (fun A => A.erase N)).card := by
      rw [Finset.card_image_of_injOn hinj, add_comm,
        Finset.card_filter_add_card_filter_not]
    omega

/-- **Lemma B (shadow bound; Frankl).** A shifted family of `r`-subsets of `Ico m N` with no
`s + 1` pairwise disjoint members has at most `s` times as many members as its shadow. -/
lemma shadow_bound (m N r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) (F : Finset (Finset ℕ))
    (hF : F ⊆ (Ico m N).powersetCard r) (hsh : Shifted m F)
    (hM : ¬ F.HasHypergraphMatching (s + 1)) : F.card ≤ s * (∂ F).card := by
  have _hs := hs
  exact B_main m s N r hr F hF hsh hM

/-- **Lemma G (transfer to `Fin n`).** A bound for all families of `r`-subsets of `range n`
bounds the extremal number of the statement. -/
lemma f_le_of_forall (n r k B : ℕ)
    (h : ∀ F : Finset (Finset ℕ), F ⊆ (range n).powersetCard r →
      ¬ F.HasHypergraphMatching k → F.card ≤ B) : Erdos1020.f n r k ≤ B := by
  classical
  unfold Erdos1020.f Hypergraph.extremalNumber
  apply Finset.sup_le
  intro H hH
  rw [@Finset.mem_filter _ (fun X : Finset (Finset (Fin n)) => ¬ X.HasHypergraphMatching k)
    (fun X => Classical.propDecidable (¬ X.HasHypergraphMatching k))] at hH
  obtain ⟨hsub, hnot⟩ := hH
  rw [Finset.mem_powerset] at hsub
  let e : Finset (Fin n) ↪ Finset ℕ := (Finset.mapEmbedding Fin.valEmbedding).toEmbedding
  have he : ∀ A : Finset (Fin n), e A = A.map Fin.valEmbedding := fun A => rfl
  rw [← Finset.card_map e]
  apply h
  · intro A hA
    obtain ⟨A', hA', rfl⟩ := Finset.mem_map.mp hA
    have h1 := Finset.mem_powersetCard.mp (hsub hA')
    rw [Finset.mem_powersetCard, he, Finset.card_map]
    refine ⟨?_, h1.2⟩
    intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_range.mpr y.isLt
  · rintro ⟨M, hMsub, hMcard, hMdisj⟩
    apply hnot
    have hM : M = (H.filter (fun A => e A ∈ M)).map e := by
      ext B
      constructor
      · intro hB
        obtain ⟨A, hA, rfl⟩ := Finset.mem_map.mp (hMsub hB)
        exact Finset.mem_map.mpr ⟨A, Finset.mem_filter.mpr ⟨hA, hB⟩, rfl⟩
      · intro hB
        obtain ⟨A, hA, rfl⟩ := Finset.mem_map.mp hB
        exact (Finset.mem_filter.mp hA).2
    refine ⟨H.filter (fun A => e A ∈ M), Finset.filter_subset _ _, ?_, ?_⟩
    · rw [← hMcard, hM, Finset.card_map, ← hM]
    · intro A hA A' hA' hne
      have h1 : e A ∈ M := (Finset.mem_filter.mp (Finset.mem_coe.mp hA)).2
      have h2 : e A' ∈ M := (Finset.mem_filter.mp (Finset.mem_coe.mp hA')).2
      have h3 := hMdisj (Finset.mem_coe.mpr h1) (Finset.mem_coe.mpr h2) (e.injective.ne hne)
      exact (Finset.disjoint_map Fin.valEmbedding).mp h3

/-- Frankl's theorem in the form of the step. -/
theorem main : OMA.R_Erdos1020_erdos_1020_R1_H2_R1.H1 := by
  intro r hr n k hk hn
  obtain ⟨s, rfl⟩ : ∃ s, k = s + 1 := ⟨k - 1, by omega⟩
  have h3 : (2 * s + 1) * 3 ≤ (2 * s + 1) * r := Nat.mul_le_mul_left _ hr
  have e0 : 2 * (s + 1) - 1 = 2 * s + 1 := by omega
  rw [e0] at hn
  have hn' : (2 * s + 1) * r ≤ n + s := by omega
  have hsn : s + 1 ≤ n := by omega
  refine le_trans ?_ (le_max_right _ _)
  have e1 : n - (s + 1) + 1 = n - s := by omega
  rw [e1]
  apply f_le_of_forall
  intro F hF hM
  obtain ⟨G, hG, hGM, hGc, hGs⟩ := exists_shifted n r (s + 1) F hF hM
  rw [← hGc]
  obtain ⟨F0, Fam, hF0, hF0s, hF0M, hsh, hFam, hnest, hcross, hcount⟩ :=
    trace_split n r s (by omega) G hG hGs hGM
  have hB := shadow_bound (s + 1) n r s (by omega) (by omega) F0 hF0 hF0s hF0M
  have e2 : (2 * s + 1) * (r - 1) + (2 * s + 1) = (2 * s + 1) * r := by
    obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
    rw [Nat.add_sub_cancel]; ring
  have hD := cross_dependent_bound (Ico (s + 1) n) (r - 1) s (by omega)
    (by rw [Nat.card_Ico]; omega) Fam hFam hnest hcross
  have hC := count_bound n r s (by omega) hsn
  have hsh' : s * (∂ F0).card ≤ s * (Fam s).card :=
    Nat.mul_le_mul_left _ (Finset.card_le_card hsh)
  rw [Finset.sum_range_succ] at hcount
  rw [Nat.card_Ico] at hD
  have e3 : n - (s + 1) = n - s - 1 := by omega
  rw [e3] at hD
  have e4 : (s + 1) * (Fam s).card = s * (Fam s).card + (Fam s).card := by ring
  omega

end OMA.Frankl

theorem OMA.solution : OMA.R_Erdos1020_erdos_1020_R1_H2_R1.H1 := OMA.Frankl.main

import OMAReductions.R_Erdos1020_erdos_1020_R1_H2_R1
import Mathlib

/-! Frankl's 2013 range of the matching bound, reduced to its threshold points.

The step: for r ≥ 3, k ≥ 3 and n ≥ (2 k - 1) r - k + 1, an r-uniform family on n vertices with no
k pairwise disjoint edges has at most max (C(r k - 1, r), C(n, r) - C(n - k + 1, r)) edges.
Proved here: the star bound C(n, r) - C(n - k + 1, r) at the single point n0(r) = (2 k - 1) r - k + 1
for every uniformity 3, 4, ..., r implies it for every n ≥ n0(r) (`from_points`).

Shifting (`exists_shifted`): the (i, j)-shift of Mathlib (`UV.compression {i} {j}`) keeps the size,
the uniformity and the absence of a k-matching (`nomatch_compression`: apply the transposition of
i and j to every edge of a matching of the shifted family), and strictly lowers the total weight.

Upward induction (`trace_step`): for a shifted r-uniform family F with no k-matching let F_m be
its edges inside [m]. Then |F_(m+1)| = |F_m| + |L_m|, where the link L_m of the top vertex m is a
shifted (r-1)-uniform family inside [m] with no k-matching once m ≥ r k (`link_nomatch`). So the
star bound for uniformity r - 1 on [n0(r-1), n] and the base point n0(r) give it for uniformity r
on [n0(r), n] (`support_step`), since n0(r) - n0(r-1) = 2 k - 1. The graph case r = 2 holds outright
for m ≥ 3 k - 1 = n0(2) (`eg_shifted`: a shifted graph with no k-matching misses some pair
{t, 2 k - 1 - t}, hence every edge meets [t] or lies in [t, 2 k - 1 - t)). The base points are read
off f by transport to Fin m (`transport`), and at n = 5 k - 2 the star term is the maximum
(`clique_le_star`).

Left open: H1, the matching conjecture at the single point n = 5 k - 2 for triple systems, and H2,
the star bound at the single point n = (2 k - 1) r - k + 1 for r ≥ 4. Both are instances of
Frankl's 2013 theorem.
-/

namespace OMA.SH

open Finset UV FinsetFamily

section General

variable {α : Type*} [DecidableEq α]

theorem swap_map_of_mem_notMem (i j : α) (B : Finset α) (hi : i ∈ B) (hj : j ∉ B) :
    B.map (Equiv.swap i j).toEmbedding = (B ∪ {j}) \ {i} := by
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  ext x
  simp only [mem_map_equiv, Equiv.symm_swap, mem_sdiff, mem_union, mem_singleton]
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; simp [hj, hij.symm]
  · subst h2; simp [hi, hij, Ne.symm hij]
  · simp [h1, h2]

theorem swap_map_of_notMem_mem (i j : α) (B : Finset α) (hi : i ∉ B) (hj : j ∈ B) :
    B.map (Equiv.swap i j).toEmbedding = (B ∪ {i}) \ {j} := by
  rw [Equiv.swap_comm]
  exact swap_map_of_mem_notMem j i B hj hi

theorem swap_map_of_notMem_notMem (i j : α) (B : Finset α) (hi : i ∉ B) (hj : j ∉ B) :
    B.map (Equiv.swap i j).toEmbedding = B := by
  ext x
  simp only [mem_map_equiv, Equiv.symm_swap]
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · subst h1; simp [hi, hj]
  · subst h2; simp [hi, hj]
  · rfl

theorem matching_image (M : Finset (Finset α)) (hMd : (M : Set (Finset α)).Pairwise Disjoint)
    (τ : Equiv.Perm α) :
    ((M.image (fun B => B.map τ.toEmbedding) : Finset (Finset α)) : Set (Finset α)).Pairwise
      Disjoint := by
  rw [coe_image]
  rintro x ⟨B, hB, rfl⟩ y ⟨C, hC, rfl⟩ hxy
  rw [disjoint_map]
  exact hMd hB hC (fun h => hxy (by rw [h]))

/-- The (i, j)-shift does not create a k-matching. -/
theorem nomatch_compression (i j : α) (hij : i ≠ j) (F : Finset (Finset α)) (k : ℕ)
    (hF : ¬ F.HasHypergraphMatching k) : ¬ (𝓒 {i} {j} F).HasHypergraphMatching k := by
  rintro ⟨M, hMC, hMc, hMd⟩
  by_cases hN : ∀ B ∈ M, B ∈ F
  · exact hF ⟨M, hN, hMc, hMd⟩
  push Not at hN
  obtain ⟨B0, hB0M, hB0F⟩ := hN
  have hB0C := hMC hB0M
  have hiB0 : i ∈ B0 := singleton_subset_iff.mp (le_of_mem_compression_of_notMem hB0C hB0F)
  have hjB0 : j ∉ B0 := disjoint_singleton_left.mp (disjoint_of_mem_compression_of_notMem hB0C hB0F)
  set τ := Equiv.swap i j
  have hτ : ∀ B ∈ M, B.map τ.toEmbedding ∈ F := by
    intro B hB
    by_cases hBB0 : B = B0
    · subst hBB0
      rw [swap_map_of_mem_notMem i j B hiB0 hjB0]
      have := sup_sdiff_mem_of_mem_compression_of_notMem hB0C hB0F
      simpa using this
    have hdis : Disjoint B B0 := hMd hB hB0M hBB0
    have hiB : i ∉ B := fun h => disjoint_left.mp hdis h hiB0
    by_cases hjB : j ∈ B
    · rw [swap_map_of_notMem_mem i j B hiB hjB]
      have := sup_sdiff_mem_of_mem_compression (hMC hB) (singleton_subset_iff.mpr hjB)
        (disjoint_singleton_left.mpr hiB)
      simpa using this
    · rw [swap_map_of_notMem_notMem i j B hiB hjB]
      by_contra hBF
      exact hiB (singleton_subset_iff.mp (le_of_mem_compression_of_notMem (hMC hB) hBF))
  apply hF
  refine ⟨M.image (fun B => B.map τ.toEmbedding), ?_, ?_, matching_image M hMd τ⟩
  · intro x hx
    obtain ⟨B, hB, rfl⟩ := mem_image.mp hx
    exact hτ B hB
  · rw [card_image_of_injective _ (map_injective τ.toEmbedding), hMc]

end General

section FinN

variable {n : ℕ}

/-- total weight of a family on Fin n -/
theorem weight_compress (i j : Fin n) (A : Finset (Fin n)) (hi : i ∉ A) (hj : j ∈ A) :
    (∑ x ∈ (A ∪ {i}) \ {j}, (x : ℕ)) + (j : ℕ) = (∑ x ∈ A, (x : ℕ)) + (i : ℕ) := by
  have hij : i ≠ j := fun h => hi (h ▸ hj)
  have hset : (A ∪ {i}) \ {j} = insert i (A.erase j) := by
    ext x
    simp only [mem_sdiff, mem_union, mem_singleton, mem_insert, mem_erase]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact Or.inr ⟨h2, h1⟩
      · exact Or.inl h1
    · rintro (h | ⟨h1, h2⟩)
      · exact ⟨Or.inr h, h ▸ hij⟩
      · exact ⟨Or.inl h2, h1⟩
  rw [hset, sum_insert (fun h => hi (mem_of_mem_erase h))]
  have := sum_erase_add A (fun x : Fin n => (x : ℕ)) hj
  omega

theorem weight_lt (i j : Fin n) (hij : i < j) (F : Finset (Finset (Fin n)))
    (hne : 𝓒 {i} {j} F ≠ F) :
    ∑ A ∈ 𝓒 {i} {j} F, ∑ x ∈ A, (x : ℕ) < ∑ A ∈ F, ∑ x ∈ A, (x : ℕ) := by
  set D := F.filter (fun a => compress {i} {j} a ∉ F) with hD
  set K := F.filter (fun a => compress {i} {j} a ∈ F) with hK
  have hC : 𝓒 {i} {j} F = K ∪ D.image (compress {i} {j}) := by
    rw [compression, filter_image]
  have hDne : D.Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro hDe
    apply hne
    rw [hC, hDe, image_empty, union_empty, hK]
    apply filter_true_of_mem
    intro a ha
    by_contra hca
    have : a ∈ D := mem_filter.mpr ⟨ha, hca⟩
    rw [hDe] at this
    simp at this
  have hdisj : Disjoint K (D.image (compress {i} {j})) := by
    rw [disjoint_left]
    intro a haK haD
    obtain ⟨b, hb, rfl⟩ := mem_image.mp haD
    exact (mem_filter.mp hb).2 (mem_filter.mp haK).1
  have hinj : Set.InjOn (compress {i} {j}) (D : Set (Finset (Fin n))) := compress_injOn
  rw [hC, sum_union hdisj, sum_image hinj]
  rw [← sum_filter_add_sum_filter_not F (fun a => compress {i} {j} a ∈ F)]
  apply Nat.add_lt_add_left
  apply sum_lt_sum_of_nonempty hDne
  intro A hA
  have hAF := (mem_filter.mp hA).1
  have hcA := (mem_filter.mp hA).2
  unfold compress at hcA ⊢
  split_ifs with h
  · have hiA : i ∉ A := disjoint_singleton_left.mp h.1
    have hjA : j ∈ A := singleton_subset_iff.mp h.2
    have := weight_compress i j A hiA hjA
    have hlt : (i : ℕ) < (j : ℕ) := hij
    simp only [sup_eq_union] at this ⊢
    omega
  · rw [if_neg h] at hcA
    exact absurd hAF hcA

theorem exists_shifted_aux (r k : ℕ) : ∀ w : ℕ, ∀ F : Finset (Finset (Fin n)),
    ∑ A ∈ F, ∑ x ∈ A, (x : ℕ) = w → (∀ e ∈ F, e.card = r) → ¬ F.HasHypergraphMatching k →
    ∃ G : Finset (Finset (Fin n)), G.card = F.card ∧ (∀ e ∈ G, e.card = r) ∧
      ¬ G.HasHypergraphMatching k ∧ ∀ i j : Fin n, i < j → 𝓒 {i} {j} G = G := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro F hw hF hM
    by_cases hs : ∀ i j : Fin n, i < j → 𝓒 {i} {j} F = F
    · exact ⟨F, rfl, hF, hM, hs⟩
    push Not at hs
    obtain ⟨i, j, hij, hne⟩ := hs
    have hlt := weight_lt i j hij F hne
    have hF' : ∀ e ∈ 𝓒 {i} {j} F, e.card = r := by
      have hsz : (F : Set (Finset (Fin n))).Sized r := fun e he => hF e he
      have := hsz.uvCompression (u := {i}) (v := {j}) (by simp)
      exact fun e he => this he
    obtain ⟨G, hGc, hG⟩ := ih _ (hw ▸ hlt) (𝓒 {i} {j} F) rfl hF'
      (nomatch_compression i j (ne_of_lt hij) F k hM)
    exact ⟨G, by rw [hGc, card_compression], hG⟩

/-- Every r-uniform family on Fin n with no k-matching has a shifted counterpart of the same
size, still r-uniform and with no k-matching. -/
theorem exists_shifted (r k : ℕ) (F : Finset (Finset (Fin n))) (hF : ∀ e ∈ F, e.card = r)
    (hM : ¬ F.HasHypergraphMatching k) :
    ∃ G : Finset (Finset (Fin n)), G.card = F.card ∧ (∀ e ∈ G, e.card = r) ∧
      ¬ G.HasHypergraphMatching k ∧ ∀ i j : Fin n, i < j → 𝓒 {i} {j} G = G :=
  exists_shifted_aux r k _ F rfl hF hM

/-- In a shifted family, replacing an element by a smaller absent one stays in the family. -/
theorem shifted_mem (G : Finset (Finset (Fin n)))
    (hG : ∀ i j : Fin n, i < j → 𝓒 {i} {j} G = G) (A : Finset (Fin n)) (hA : A ∈ G)
    (i j : Fin n) (hij : i < j) (hi : i ∉ A) (hj : j ∈ A) : (A ∪ {i}) \ {j} ∈ G := by
  have hA' : A ∈ 𝓒 {i} {j} G := by rw [hG i j hij]; exact hA
  have := sup_sdiff_mem_of_mem_compression hA' (singleton_subset_iff.mpr hj)
    (disjoint_singleton_left.mpr hi)
  simpa using this

end FinN

end OMA.SH

namespace OMA.SH

open Finset UV FinsetFamily

section Induct

variable {n : ℕ}

theorem card_lt (m : ℕ) (h : m ≤ n) :
    ((univ : Finset (Fin n)).filter (fun x : Fin n => (x : ℕ) < m)).card = m := by
  rw [Fin.card_filter_val_lt]
  omega

theorem card_Ico (a b : ℕ) (hab : a ≤ b) (h : b ≤ n) :
    ((univ : Finset (Fin n)).filter (fun x : Fin n => a ≤ (x : ℕ) ∧ (x : ℕ) < b)).card = b - a := by
  have h1 : (univ : Finset (Fin n)).filter (fun x : Fin n => a ≤ (x : ℕ) ∧ (x : ℕ) < b) =
      (univ.filter (fun x : Fin n => (x : ℕ) < b)) \ (univ.filter (fun x : Fin n => (x : ℕ) < a)) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_sdiff, not_lt]
    tauto
  have h2 : (univ.filter (fun x : Fin n => (x : ℕ) < a)) ⊆ (univ.filter (fun x : Fin n => (x : ℕ) < b)) := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    omega
  rw [h1, card_sdiff_of_subset h2, card_lt b h, card_lt a (by omega)]

theorem choose2_step (a B : ℕ) (hB : B ≤ a) : ∀ d, a.choose 2 + d * B ≤ (a + d).choose 2
  | 0 => by simp
  | d + 1 => by
    have ih := choose2_step a B hB d
    have h3 : (a + d + 1).choose 2 = (a + d).choose 1 + (a + d).choose 2 :=
      Nat.choose_succ_succ' (a + d) 1
    rw [show a + (d + 1) = a + d + 1 by ring, h3, Nat.choose_one_right, add_mul, one_mul]
    omega

theorem choose2_odd (d : ℕ) : (2 * d + 1).choose 2 = d * (2 * d + 1) := by
  rw [Nat.choose_two_right, show 2 * d + 1 - 1 = 2 * d by omega]
  rw [show (2 * d + 1) * (2 * d) = 2 * (d * (2 * d + 1)) by ring]
  omega

/-- pairs within [m] meeting [t] -/
theorem count_meet (m t : ℕ) (htm : t ≤ m) (hmn : m ≤ n) :
    ((((univ : Finset (Fin n)).filter (fun x : Fin n => (x : ℕ) < m)).powersetCard 2).filter
      (fun e : Finset (Fin n) => ∃ x ∈ e, (x : ℕ) < t)).card + (m - t).choose 2 ≤ m.choose 2 := by
  set Rm := (univ : Finset (Fin n)).filter (fun x : Fin n => (x : ℕ) < m)
  set Q := (univ : Finset (Fin n)).filter (fun x : Fin n => t ≤ (x : ℕ) ∧ (x : ℕ) < m)
  have hQ : Q.card = m - t := card_Ico t m htm hmn
  have hQR : Q ⊆ Rm := by
    intro x hx
    simp only [Q, Rm, mem_filter, mem_univ, true_and] at hx ⊢
    exact hx.2
  have hdis : Disjoint ((Rm.powersetCard 2).filter (fun e : Finset (Fin n) => ∃ x ∈ e, (x : ℕ) < t))
      (Q.powersetCard 2) := by
    rw [disjoint_left]
    intro e he he2
    obtain ⟨-, x, hx, hxt⟩ := mem_filter.mp he
    have := (mem_powersetCard.mp he2).1 hx
    simp only [Q, mem_filter, mem_univ, true_and] at this
    omega
  have hU := card_le_card (union_subset
    (filter_subset (fun e : Finset (Fin n) => ∃ x ∈ e, (x : ℕ) < t) (Rm.powersetCard 2))
    (powersetCard_mono hQR (n := 2)))
  rw [card_union_of_disjoint hdis, card_powersetCard, card_powersetCard, hQ,
    card_lt m hmn] at hU
  exact hU

/-- Erdős–Gallai for shifted graphs inside [m], in the star regime. -/
theorem eg_shifted (m s : ℕ) (hm : 3 * s + 2 ≤ m) (hmn : m ≤ n) (L : Finset (Finset (Fin n)))
    (hL : ∀ e ∈ L, e.card = 2 ∧ ∀ x ∈ e, (x : ℕ) < m)
    (hsh : ∀ e ∈ L, ∀ i j : Fin n, i < j → i ∉ e → j ∈ e → (e ∪ {i}) \ {j} ∈ L)
    (hM : ¬ L.HasHypergraphMatching (s + 1)) :
    L.card + (m - s).choose 2 ≤ m.choose 2 := by
  -- some pattern pair {t, 2s+1-t} is missing
  have hpat : ∃ t, t ≤ s ∧ ∀ (ht1 : t < n) (ht2 : 2 * s + 1 - t < n),
      ({⟨t, ht1⟩, ⟨2 * s + 1 - t, ht2⟩} : Finset (Fin n)) ∉ L := by
    by_contra hcon
    push Not at hcon
    choose h1 h2 hmem using hcon
    apply hM
    let g : Fin (s + 1) → Finset (Fin n) := fun t =>
      {⟨t, h1 t (by omega)⟩, ⟨2 * s + 1 - t, h2 t (by omega)⟩}
    have hg : ∀ (t t' : Fin (s + 1)), t ≠ t' → Disjoint (g t) (g t') := by
      intro t t' htt
      have htt' : (t : ℕ) ≠ t' := fun h => htt (Fin.ext h)
      rw [disjoint_left]
      intro x hx hx'
      simp only [g, mem_insert, mem_singleton, Fin.ext_iff] at hx hx'
      have := t.isLt
      have := t'.isLt
      omega
    have hginj : Function.Injective g := by
      intro t t' h
      by_contra hne
      have hd := hg t t' hne
      rw [h, disjoint_self_iff_empty] at hd
      have : (⟨(t' : ℕ), h1 t' (by omega)⟩ : Fin n) ∈ g t' := by simp [g]
      rw [hd] at this
      simp at this
    refine ⟨univ.image g, ?_, ?_, ?_⟩
    · intro e he
      obtain ⟨t, -, rfl⟩ := mem_image.mp he
      exact hmem t (by omega)
    · rw [card_image_of_injective _ hginj, card_univ, Fintype.card_fin]
    · rw [coe_image]
      rintro x ⟨t, -, rfl⟩ y ⟨t', -, rfl⟩ hxy
      exact hg t t' (fun h => hxy (by rw [h]))
  obtain ⟨t, hts, hmiss⟩ := hpat
  have htn : t < n := by omega
  have hqn : 2 * s + 1 - t < n := by omega
  -- every edge meets [t] or lies in [t, 2s+1-t)
  have hcover : ∀ e ∈ L, (∃ x ∈ e, (x : ℕ) < t) ∨
      ∀ x ∈ e, t ≤ (x : ℕ) ∧ (x : ℕ) < 2 * s + 1 - t := by
    intro e he
    by_contra hcon
    push Not at hcon
    obtain ⟨hnot, y, hy, hyc⟩ := hcon
    obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp (hL e he).1
    -- order the pair
    wlog hlt : a < b generalizing a b
    · exact this b a (Ne.symm hab) (by rw [pair_comm]; exact he) (by
        intro x hx; exact hnot x (by rw [pair_comm]; exact hx)) (by rw [pair_comm]; exact hy)
        (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hab))
    have hat : t ≤ (a : ℕ) := hnot a (by simp)
    have hbt : t ≤ (b : ℕ) := hnot b (by simp)
    have hab' : (a : ℕ) < b := hlt
    have hbq : 2 * s + 1 - t ≤ (b : ℕ) := by
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl
      · have := hyc (hnot y (by simp)); omega
      · exact hyc (hnot y (by simp))
    set p : Fin n := ⟨t, htn⟩
    set q : Fin n := ⟨2 * s + 1 - t, hqn⟩
    -- step 1: move a down to t
    have h1 : ({p, b} : Finset (Fin n)) ∈ L := by
      by_cases hap : (a : ℕ) = t
      · have : a = p := Fin.ext hap
        rw [← this]; exact he
      · have hpa : p < a := by
          show (t : ℕ) < a
          omega
        have := hsh {a, b} he p a hpa (by
          simp only [mem_insert, mem_singleton, not_or, Fin.ext_iff]
          constructor <;> simp [p] <;> omega) (by simp)
        convert this using 1
        ext x
        simp only [mem_insert, mem_singleton, mem_sdiff, mem_union, Fin.ext_iff]
        simp only [p] at *
        omega
    -- step 2: move b down to 2s+1-t
    have h2 : ({p, q} : Finset (Fin n)) ∈ L := by
      by_cases hbq' : (b : ℕ) = 2 * s + 1 - t
      · have : b = q := Fin.ext hbq'
        rw [← this]; exact h1
      · have hqb : q < b := by
          show 2 * s + 1 - t < (b : ℕ)
          omega
        have := hsh {p, b} h1 q b hqb (by
          simp only [mem_insert, mem_singleton, not_or, Fin.ext_iff]
          simp only [p, q]
          omega) (by simp)
        convert this using 1
        ext x
        simp only [mem_insert, mem_singleton, mem_sdiff, mem_union, Fin.ext_iff]
        simp only [p, q] at *
        omega
    exact hmiss htn hqn h2
  -- count
  have hX := count_meet m t (by omega) hmn
  set Rm := (univ : Finset (Fin n)).filter (fun x : Fin n => (x : ℕ) < m)
  set X := (Rm.powersetCard 2).filter (fun e : Finset (Fin n) => ∃ x ∈ e, (x : ℕ) < t)
  set I := (univ : Finset (Fin n)).filter (fun x : Fin n => t ≤ (x : ℕ) ∧ (x : ℕ) < 2 * s + 1 - t)
  have hLXY : L ⊆ X ∪ I.powersetCard 2 := by
    intro e he
    rw [mem_union]
    rcases hcover e he with h | h
    · left
      rw [mem_filter, mem_powersetCard]
      refine ⟨⟨?_, (hL e he).1⟩, h⟩
      intro x hx
      simp only [Rm, mem_filter, mem_univ, true_and]
      exact (hL e he).2 x hx
    · right
      rw [mem_powersetCard]
      refine ⟨?_, (hL e he).1⟩
      intro x hx
      simp only [I, mem_filter, mem_univ, true_and]
      exact h x hx
  have hI : I.card = 2 * (s - t) + 1 := by
    rw [card_Ico t (2 * s + 1 - t) (by omega) (by omega)]
    omega
  have hcardL := (card_le_card hLXY).trans (card_union_le _ _)
  rw [card_powersetCard, hI, choose2_odd] at hcardL
  have hstep := choose2_step (m - s) (2 * (s - t) + 1) (by omega) (s - t)
  rw [show m - s + (s - t) = m - t by omega] at hstep
  have e1 : (s - t) * (2 * (s - t) + 1) = (s - t) * (2 * (s - t) + 1) := rfl
  generalize (s - t) * (2 * (s - t) + 1) = P at hcardL hstep
  omega

end Induct

end OMA.SH

namespace OMA.SH

open Finset UV FinsetFamily

section Gen

variable {n : ℕ}

theorem map_preimage_eq (m : ℕ) (hmn : m ≤ n) (e : Finset (Fin n)) (he : ∀ x ∈ e, (x : ℕ) < m) :
    (e.preimage (Fin.castLEEmb hmn) (Fin.castLEEmb hmn).injective.injOn).map
      (Fin.castLEEmb hmn) = e := by
  ext x
  simp only [mem_map, mem_preimage]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    refine ⟨⟨x, he x hx⟩, ?_, ?_⟩
    · have : Fin.castLEEmb hmn ⟨x, he x hx⟩ = x := Fin.ext rfl
      rw [this]; exact hx
    · exact Fin.ext rfl

/-- A family on Fin n supported on [m] is counted by f m. -/
theorem transport (m r k : ℕ) (hmn : m ≤ n) (G : Finset (Finset (Fin n)))
    (hG : ∀ e ∈ G, e.card = r ∧ ∀ x ∈ e, (x : ℕ) < m) (hM : ¬ G.HasHypergraphMatching k) :
    G.card ≤ Erdos1020.f m r k := by
  classical
  set emb := Fin.castLEEmb hmn
  let pre : Finset (Fin n) → Finset (Fin m) := fun e => e.preimage emb emb.injective.injOn
  have hpre : ∀ e ∈ G, (pre e).map emb = e := fun e he => map_preimage_eq m hmn e (hG e he).2
  set G' := G.image pre
  have hinj : Set.InjOn pre (G : Set (Finset (Fin n))) := by
    intro a ha b hb hab
    rw [← hpre a ha, ← hpre b hb]
    simp only [pre] at hab ⊢
    rw [hab]
  have hcard : G'.card = G.card := card_image_of_injOn hinj
  have hG'r : ∀ e' ∈ G', e'.card = r := by
    intro e' he'
    obtain ⟨e, he, rfl⟩ := mem_image.mp he'
    rw [← card_map emb, hpre e he]
    exact (hG e he).1
  have hM' : ¬ G'.HasHypergraphMatching k := by
    rintro ⟨M', hM'G, hM'c, hM'd⟩
    apply hM
    refine ⟨M'.image (fun e' => e'.map emb), ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨e', he', rfl⟩ := mem_image.mp hx
      obtain ⟨e, he, rfl⟩ := mem_image.mp (hM'G he')
      rw [hpre e he]; exact he
    · rw [card_image_of_injective _ (map_injective emb), hM'c]
    · rw [coe_image]
      rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩ hxy
      rw [disjoint_map]
      exact hM'd ha hb (fun h => hxy (by rw [h]))
  rw [← hcard]
  unfold Erdos1020.f Hypergraph.extremalNumber
  apply le_sup (f := Finset.card)
  rw [@Finset.mem_filter _ (fun X : Finset (Finset (Fin m)) => ¬ X.HasHypergraphMatching k)
    (fun X => Classical.propDecidable (¬ X.HasHypergraphMatching k))]
  refine ⟨?_, hM'⟩
  rw [mem_powerset]
  intro e he
  rw [mem_powersetCard]
  exact ⟨subset_univ _, hG'r e he⟩

/-- the link of the top vertex v = m of a shifted family has no k-matching once 3k ≤ m -/
theorem link_nomatch (m k r : ℕ) (hm : (r + 1) * k ≤ m) (hmn : m < n) (G : Finset (Finset (Fin n)))
    (hG : ∀ A ∈ G, ∀ i j : Fin n, i < j → i ∉ A → j ∈ A → (A ∪ {i}) \ {j} ∈ G) (hM : ¬ G.HasHypergraphMatching k)
    (L : Finset (Finset (Fin n)))
    (hL : ∀ e ∈ L, e.card = r ∧ (∀ x ∈ e, (x : ℕ) < m) ∧ insert (⟨m, hmn⟩ : Fin n) e ∈ G) :
    ¬ L.HasHypergraphMatching k := by
  classical
  rintro ⟨M, hML, hMc, hMd⟩
  set v : Fin n := ⟨m, hmn⟩ with hv
  set U := M.biUnion id with hUdef
  have hU : U.card ≤ r * k := by
    calc U.card ≤ ∑ e ∈ M, (id e).card := card_biUnion_le
      _ = ∑ _e ∈ M, r := sum_congr rfl (fun e he => (hL e (hML he)).1)
      _ = r * k := by rw [sum_const, smul_eq_mul, hMc, mul_comm]
  set Rm := (univ : Finset (Fin n)).filter (fun x : Fin n => (x : ℕ) < m)
  have hAv : k ≤ (Rm \ U).card := by
    have h1 := le_card_sdiff U Rm
    rw [card_lt m hmn.le] at h1
    have : (r + 1) * k = r * k + k := by ring
    generalize r * k = P at hU hm this
    omega
  obtain ⟨C, hCA, hCc⟩ := exists_subset_card_eq hAv
  have hcardeq : Fintype.card {x // x ∈ M} = Fintype.card {x // x ∈ C} := by
    rw [Fintype.card_coe, Fintype.card_coe, hMc, hCc]
  let g : {x // x ∈ M} ≃ {x // x ∈ C} := Fintype.equivOfCardEq hcardeq
  have hgC : ∀ e : {x // x ∈ M}, (g e).1 ∈ Rm ∧ (g e).1 ∉ U := by
    intro e
    have := hCA (g e).2
    exact mem_sdiff.mp this
  have hgnot : ∀ e e' : {x // x ∈ M}, (g e).1 ∉ e'.1 := by
    intro e e' hc
    exact (hgC e).2 (mem_biUnion.mpr ⟨e'.1, e'.2, hc⟩)
  let φ : {x // x ∈ M} → Finset (Fin n) := fun e => insert (g e).1 e.1
  have hφd : ∀ e1 e2 : {x // x ∈ M}, e1 ≠ e2 → Disjoint (φ e1) (φ e2) := by
    intro e1 e2 hne
    rw [disjoint_left]
    intro x hx1 hx2
    simp only [φ, mem_insert] at hx1 hx2
    rcases hx1 with h1 | h1 <;> rcases hx2 with h2 | h2
    · exact hne (g.injective (Subtype.ext (h1.symm.trans h2)))
    · exact hgnot e1 e2 (h1 ▸ h2)
    · exact hgnot e2 e1 (h2 ▸ h1)
    · exact disjoint_left.mp (hMd e1.2 e2.2 (fun h => hne (Subtype.ext h))) h1 h2
  have hφinj : Function.Injective φ := by
    intro e1 e2 h
    by_contra hne
    have hd := hφd e1 e2 hne
    rw [h, disjoint_self_iff_empty] at hd
    have : (g e2).1 ∈ φ e2 := mem_insert_self _ _
    rw [hd] at this
    simp at this
  have hφG : ∀ e : {x // x ∈ M}, φ e ∈ G := by
    intro e
    obtain ⟨-, hlt, hins⟩ := hL e.1 (hML e.2)
    set c := (g e).1
    have hcm : (c : ℕ) < m := by
      have := (hgC e).1
      simp only [Rm, mem_filter, mem_univ, true_and] at this
      exact this
    have hcv : c < v := by
      show (c : ℕ) < m
      exact hcm
    have hvnot : v ∉ e.1 := by
      intro hve
      have := hlt v hve
      simp [hv] at this
    have hcnot : c ∉ insert v e.1 := by
      rw [mem_insert, not_or]
      exact ⟨ne_of_lt hcv, hgnot e e⟩
    have := hG (insert v e.1) hins c v hcv hcnot (mem_insert_self _ _)
    convert this using 1
    ext x
    simp only [φ, mem_insert, mem_sdiff, mem_union, mem_singleton]
    constructor
    · rintro (h | h)
      · refine ⟨Or.inr h, ?_⟩
        rw [h]; exact ne_of_lt hcv
      · refine ⟨Or.inl (Or.inr h), ?_⟩
        rintro rfl; exact hvnot h
    · rintro ⟨(h | h) | h, hx⟩
      · exact absurd h hx
      · exact Or.inr h
      · exact Or.inl h
  apply hM
  refine ⟨M.attach.image φ, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨e, -, rfl⟩ := mem_image.mp hx
    exact hφG e
  · rw [card_image_of_injective _ hφinj, card_attach, hMc]
  · rw [coe_image]
    rintro x ⟨a, -, rfl⟩ y ⟨b, -, rfl⟩ hxy
    exact hφd a b (fun h => hxy (by rw [h]))

theorem trace_step (k r : ℕ) (hk : 1 ≤ k) (a m0 : ℕ) (ham : a ≤ m0) (hm0 : (r + 1) * k ≤ m0)
    (hprev : ∀ m, a ≤ m → m ≤ n → ∀ L : Finset (Finset (Fin n)),
      (∀ e ∈ L, e.card = r ∧ ∀ x ∈ e, (x : ℕ) < m) →
      (∀ A ∈ L, ∀ i j : Fin n, i < j → i ∉ A → j ∈ A → (A ∪ {i}) \ {j} ∈ L) →
      ¬ L.HasHypergraphMatching k → L.card + (m - (k - 1)).choose r ≤ m.choose r)
    (hbase : Erdos1020.f m0 (r + 1) k + (m0 - (k - 1)).choose (r + 1) ≤ m0.choose (r + 1))
    (G : Finset (Finset (Fin n))) (hG3 : ∀ e ∈ G, e.card = r + 1)
    (hGM : ¬ G.HasHypergraphMatching k)
    (hG : ∀ A ∈ G, ∀ i j : Fin n, i < j → i ∉ A → j ∈ A → (A ∪ {i}) \ {j} ∈ G) :
    ∀ m, m0 ≤ m → m ≤ n →
      (G.filter (fun A : Finset (Fin n) => ∀ x ∈ A, (x : ℕ) < m)).card +
        (m - (k - 1)).choose (r + 1) ≤ m.choose (r + 1) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro hmn
    have := transport m0 (r + 1) k hmn (G.filter (fun A : Finset (Fin n) => ∀ x ∈ A, (x : ℕ) < m0))
      (fun e he => ⟨hG3 e (filter_subset _ _ he), (mem_filter.mp he).2⟩)
      (fun ⟨M, hMG, hMc, hMd⟩ => hGM ⟨M, hMG.trans (filter_subset _ _), hMc, hMd⟩)
    omega
  | succ m hm ih =>
    intro hmn
    have ih := ih (by omega)
    have hmlt : m < n := by omega
    set v : Fin n := ⟨m, hmlt⟩ with hv
    set Fm := G.filter (fun A : Finset (Fin n) => ∀ x ∈ A, (x : ℕ) < m) with hFm
    set Fm1 := G.filter (fun A : Finset (Fin n) => ∀ x ∈ A, (x : ℕ) < m + 1) with hFm1
    set Top := Fm1.filter (fun A => v ∈ A) with hTop
    have hrest : Fm1.filter (fun A => ¬ v ∈ A) = Fm := by
      ext A
      simp only [hFm, hFm1, mem_filter]
      constructor
      · rintro ⟨⟨hAG, hA⟩, hvA⟩
        refine ⟨hAG, fun x hx => ?_⟩
        have h1 := hA x hx
        have h2 : x ≠ v := fun h => hvA (h ▸ hx)
        have h3 : (x : ℕ) ≠ m := fun h => h2 (Fin.ext h)
        omega
      · rintro ⟨hAG, hA⟩
        refine ⟨⟨hAG, fun x hx => by have := hA x hx; omega⟩, fun hvA => ?_⟩
        have := hA v hvA
        simp [hv] at this
    have hsplit : Top.card + Fm.card = Fm1.card := by
      rw [← hrest]
      exact card_filter_add_card_filter_not _
    set L := Top.image (fun A => A.erase v) with hLdef
    have hLc : L.card = Top.card := by
      apply card_image_of_injOn
      intro A hA B hB h
      have hvA := (mem_filter.mp hA).2
      have hvB := (mem_filter.mp hB).2
      simp only at h
      rw [← insert_erase hvA, ← insert_erase hvB, h]
    have hL : ∀ e ∈ L, e.card = r ∧ (∀ x ∈ e, (x : ℕ) < m) ∧ insert v e ∈ G := by
      intro e he
      obtain ⟨A, hA, rfl⟩ := mem_image.mp he
      have hvA := (mem_filter.mp hA).2
      have hA1 := (mem_filter.mp hA).1
      have hAG := (mem_filter.mp hA1).1
      have hAlt := (mem_filter.mp hA1).2
      refine ⟨?_, ?_, ?_⟩
      · rw [card_erase_of_mem hvA, hG3 A hAG, Nat.add_sub_cancel]
      · intro x hx
        have h1 := hAlt x (mem_of_mem_erase hx)
        have h2 : x ≠ v := ne_of_mem_erase hx
        have h3 : (x : ℕ) ≠ m := fun h => h2 (Fin.ext h)
        omega
      · rw [insert_erase hvA]; exact hAG
    have hLnm := link_nomatch m k r (by omega) hmlt G hG hGM L hL
    have hLsh : ∀ e ∈ L, ∀ i j : Fin n, i < j → i ∉ e → j ∈ e → (e ∪ {i}) \ {j} ∈ L := by
      intro e he i j hij hie hje
      obtain ⟨he2, hlt, hins⟩ := hL e he
      have hjm : (j : ℕ) < m := hlt j hje
      have hiv : i ≠ v := by
        intro h
        have : (i : ℕ) = m := by rw [h]
        have : (i : ℕ) < j := hij
        omega
      have hjv : j ≠ v := by
        intro h
        have : (j : ℕ) = m := by rw [h]
        omega
      have hvnot : v ∉ e := by
        intro hve
        have := hlt v hve
        simp [hv] at this
      have hA' := hG (insert v e) hins i j hij
        (by rw [mem_insert, not_or]; exact ⟨hiv, hie⟩) (mem_insert_of_mem hje)
      rw [hLdef, mem_image]
      refine ⟨(insert v e ∪ {i}) \ {j}, ?_, ?_⟩
      · rw [hTop, mem_filter, hFm1, mem_filter]
        refine ⟨⟨hA', ?_⟩, ?_⟩
        · intro x hx
          simp only [mem_sdiff, mem_union, mem_insert, mem_singleton] at hx
          rcases hx.1 with (h | h) | h
          · rw [h]; simp [hv]
          · have := hlt x h; omega
          · rw [h]; have : (i : ℕ) < j := hij; omega
        · simp only [mem_sdiff, mem_union, mem_insert, mem_singleton]
          refine ⟨by simp, ?_⟩
          intro h
          exact hjv h.symm
      · ext x
        simp only [mem_erase, mem_sdiff, mem_union, mem_insert, mem_singleton]
        constructor
        · rintro ⟨hxv, (h | h) | h, hxj⟩
          · exact absurd h hxv
          · exact ⟨Or.inl h, hxj⟩
          · exact ⟨Or.inr h, hxj⟩
        · rintro ⟨h | h, hxj⟩
          · exact ⟨fun hx => hvnot (hx ▸ h), Or.inl (Or.inr h), hxj⟩
          · exact ⟨fun hx => hiv (h ▸ hx), Or.inr h, hxj⟩
    have hEG := hprev m (by omega) (by omega) L
      (fun e he => ⟨(hL e he).1, (hL e he).2.1⟩) hLsh hLnm
    have p1 : (m + 1).choose (r + 1) = m.choose r + m.choose (r + 1) := Nat.choose_succ_succ' m r
    have hkr : k ≤ (r + 1) * k := Nat.le_mul_of_pos_left k (by omega)
    have p2 : (m + 1 - (k - 1)).choose (r + 1) =
        (m - (k - 1)).choose r + (m - (k - 1)).choose (r + 1) := by
      rw [show m + 1 - (k - 1) = (m - (k - 1)) + 1 by omega]
      exact Nat.choose_succ_succ' _ r
    omega

theorem f_le_forall (n r k B : ℕ)
    (h : ∀ H : Finset (Finset (Fin n)), H ⊆ (univ : Finset (Fin n)).powersetCard r →
      ¬ H.HasHypergraphMatching k → H.card ≤ B) : Erdos1020.f n r k ≤ B := by
  classical
  unfold Erdos1020.f Hypergraph.extremalNumber
  apply Finset.sup_le
  intro H hH
  rw [@Finset.mem_filter _ (fun X : Finset (Finset (Fin n)) => ¬ X.HasHypergraphMatching k)
    (fun X => Classical.propDecidable (¬ X.HasHypergraphMatching k))] at hH
  exact h H (mem_powerset.mp hH.1) hH.2


/-- support form of the step: the claim for r on [a, n] and the base at m0 give the claim for r+1 -/
theorem support_step (k r : ℕ) (hk : 1 ≤ k) (a m0 : ℕ) (ham : a ≤ m0) (hm0 : (r + 1) * k ≤ m0)
    (hprev : ∀ m, a ≤ m → m ≤ n → ∀ L : Finset (Finset (Fin n)),
      (∀ e ∈ L, e.card = r ∧ ∀ x ∈ e, (x : ℕ) < m) →
      (∀ A ∈ L, ∀ i j : Fin n, i < j → i ∉ A → j ∈ A → (A ∪ {i}) \ {j} ∈ L) →
      ¬ L.HasHypergraphMatching k → L.card + (m - (k - 1)).choose r ≤ m.choose r)
    (hbase : Erdos1020.f m0 (r + 1) k + (m0 - (k - 1)).choose (r + 1) ≤ m0.choose (r + 1)) :
    ∀ m, m0 ≤ m → m ≤ n → ∀ L : Finset (Finset (Fin n)),
      (∀ e ∈ L, e.card = r + 1 ∧ ∀ x ∈ e, (x : ℕ) < m) →
      (∀ A ∈ L, ∀ i j : Fin n, i < j → i ∉ A → j ∈ A → (A ∪ {i}) \ {j} ∈ L) →
      ¬ L.HasHypergraphMatching k → L.card + (m - (k - 1)).choose (r + 1) ≤ m.choose (r + 1) := by
  intro m hm hmn L hL hLsh hLM
  have := trace_step k r hk a m0 ham hm0 hprev hbase L (fun e he => (hL e he).1) hLM hLsh m hm hmn
  rwa [filter_true_of_mem (fun A hA => (hL A hA).2)] at this

/-- the graph case, unconditionally -/
theorem support_two (k : ℕ) (hk : 1 ≤ k) :
    ∀ m, 2 * k + (k - 1) * (2 - 1) ≤ m → m ≤ n → ∀ L : Finset (Finset (Fin n)),
      (∀ e ∈ L, e.card = 2 ∧ ∀ x ∈ e, (x : ℕ) < m) →
      (∀ A ∈ L, ∀ i j : Fin n, i < j → i ∉ A → j ∈ A → (A ∪ {i}) \ {j} ∈ L) →
      ¬ L.HasHypergraphMatching k → L.card + (m - (k - 1)).choose 2 ≤ m.choose 2 := by
  intro m hm hmn L hL hLsh hLM
  exact eg_shifted m (k - 1) (by omega) hmn L hL hLsh (by rwa [show k - 1 + 1 = k by omega])

/-- all uniformities, from the star bound at the single points N(r) = r k + (k-1)(r-1) -/
theorem support_all (k : ℕ) (hk : 1 ≤ k)
    (hyp : ∀ r, 3 ≤ r → Erdos1020.f (r * k + (k - 1) * (r - 1)) r k ≤
      (r * k + (k - 1) * (r - 1)).choose r - (r * k + (k - 1) * (r - 1) - k + 1).choose r) :
    ∀ r, 2 ≤ r → ∀ m, r * k + (k - 1) * (r - 1) ≤ m → m ≤ n → ∀ L : Finset (Finset (Fin n)),
      (∀ e ∈ L, e.card = r ∧ ∀ x ∈ e, (x : ℕ) < m) →
      (∀ A ∈ L, ∀ i j : Fin n, i < j → i ∉ A → j ∈ A → (A ∪ {i}) \ {j} ∈ L) →
      ¬ L.HasHypergraphMatching k → L.card + (m - (k - 1)).choose r ≤ m.choose r := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base => exact support_two k hk
  | succ r hr ih =>
    have e1 : (r + 1) * k = r * k + k := by ring
    have e2 : (k - 1) * (r + 1 - 1) = (k - 1) * (r - 1) + (k - 1) := by
      rw [show r + 1 - 1 = (r - 1) + 1 by omega]; ring
    have hb := hyp (r + 1) (by omega)
    have hle : ((r + 1) * k + (k - 1) * (r + 1 - 1) - k + 1).choose (r + 1) ≤
        ((r + 1) * k + (k - 1) * (r + 1 - 1)).choose (r + 1) :=
      Nat.choose_le_choose _ (by omega)
    refine support_step k r hk _ _ ?_ ?_ ih ?_
    · rw [e1, e2]; omega
    · rw [e2]; omega
    · rw [show (r + 1) * k + (k - 1) * (r + 1 - 1) - (k - 1) =
          (r + 1) * k + (k - 1) * (r + 1 - 1) - k + 1 by
        rw [e1, e2]; omega]
      omega

/-- from the support form to the extremal number -/
theorem f_of_support (r k : ℕ) (n : ℕ)
    (hS : ∀ L : Finset (Finset (Fin n)),
      (∀ e ∈ L, e.card = r ∧ ∀ x ∈ e, (x : ℕ) < n) →
      (∀ A ∈ L, ∀ i j : Fin n, i < j → i ∉ A → j ∈ A → (A ∪ {i}) \ {j} ∈ L) →
      ¬ L.HasHypergraphMatching k → L.card + (n - (k - 1)).choose r ≤ n.choose r) (hk : 1 ≤ k)
    (hkn : k ≤ n) :
    Erdos1020.f n r k ≤ n.choose r - (n - k + 1).choose r := by
  apply f_le_forall
  intro H hH hM
  obtain ⟨G, hGc, hG3, hGM, hGs⟩ :=
    exists_shifted r k H (fun e he => (mem_powersetCard.mp (hH he)).2) hM
  have key := hS G (fun e he => ⟨hG3 e he, fun x _ => x.isLt⟩)
    (fun A hA i j hij hi hj => shifted_mem G hGs A hA i j hij hi hj) hGM
  rw [hGc, show n - (k - 1) = n - k + 1 by omega] at key
  omega

/-- triple systems: the star bound at one point m0 ≥ 3k propagates upward -/
theorem from_base (k : ℕ) (hk : 1 ≤ k) (m0 : ℕ) (hm0 : 3 * k ≤ m0)
    (hbase : Erdos1020.f m0 3 k ≤ m0.choose 3 - (m0 - k + 1).choose 3) (n : ℕ) (hn : m0 ≤ n) :
    Erdos1020.f n 3 k ≤ n.choose 3 - (n - k + 1).choose 3 := by
  have hle : (m0 - k + 1).choose 3 ≤ m0.choose 3 := Nat.choose_le_choose 3 (by omega)
  have hb' : Erdos1020.f m0 (2 + 1) k + (m0 - (k - 1)).choose (2 + 1) ≤ m0.choose (2 + 1) := by
    rw [show m0 - (k - 1) = m0 - k + 1 by omega]
    show Erdos1020.f m0 3 k + (m0 - k + 1).choose 3 ≤ m0.choose 3
    omega
  apply f_of_support 3 k n _ hk (by omega)
  intro L hL hLsh hLM
  exact support_step (n := n) k 2 hk (2 * k + (k - 1) * (2 - 1)) m0 (by omega) (by omega)
    (support_two k hk) hb' n hn le_rfl L hL hLsh hLM

/-- all uniformities r ≥ 3 -/
theorem from_points (k : ℕ) (hk : 1 ≤ k)
    (hyp : ∀ r, 3 ≤ r → Erdos1020.f (r * k + (k - 1) * (r - 1)) r k ≤
      (r * k + (k - 1) * (r - 1)).choose r - (r * k + (k - 1) * (r - 1) - k + 1).choose r)
    (r : ℕ) (hr : 2 ≤ r) (n : ℕ) (hn : r * k + (k - 1) * (r - 1) ≤ n) :
    Erdos1020.f n r k ≤ n.choose r - (n - k + 1).choose r := by
  have hkr : k ≤ r * k := Nat.le_mul_of_pos_left k (by omega)
  exact f_of_support r k n
    (fun L hL hLsh hLM => support_all (n := n) k hk hyp r hr n hn le_rfl L hL hLsh hLM) hk
    (by omega)

theorem choose3_step (a B : ℕ) (hB : B ≤ a.choose 2) :
    ∀ d, a.choose 3 + d * B ≤ (a + d).choose 3
  | 0 => by simp
  | d + 1 => by
    have ih := choose3_step a B hB d
    have h2 : a.choose 2 ≤ (a + d).choose 2 := Nat.choose_le_choose 2 (by omega)
    have h3 : (a + d + 1).choose 3 = (a + d).choose 2 + (a + d).choose 3 :=
      Nat.choose_succ_succ' (a + d) 2
    rw [show a + (d + 1) = a + d + 1 by ring, h3, add_mul, one_mul]
    linarith

/-- At n = 5k - 2 the star term is the larger one. -/
theorem clique_le_star (k : ℕ) (hk : 1 ≤ k) :
    (3 * k - 1).choose 3 ≤ (5 * k - 2).choose 3 - (5 * k - 2 - k + 1).choose 3 := by
  have key := choose3_step (4 * k - 1) ((4 * k - 1).choose 2) le_rfl (k - 1)
  rw [show 4 * k - 1 + (k - 1) = 5 * k - 2 by omega] at key
  rw [show 5 * k - 2 - k + 1 = 4 * k - 1 by omega]
  have h3 := Nat.choose_succ_right_eq (3 * k - 1) 2
  rw [show 3 * k - 1 - 2 = 3 * (k - 1) by omega] at h3
  have h4 : (3 * k - 1).choose 3 = (k - 1) * (3 * k - 1).choose 2 := by
    have : (3 * k - 1).choose (2 + 1) * 3 = 3 * ((k - 1) * (3 * k - 1).choose 2) := by
      rw [h3]; ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 3) (by rw [this]; ring)
  have h5 : (k - 1) * (3 * k - 1).choose 2 ≤ (k - 1) * (4 * k - 1).choose 2 :=
    Nat.mul_le_mul_left _ (Nat.choose_le_choose 2 (by omega))
  generalize (k - 1) * (4 * k - 1).choose 2 = P at key h5
  generalize (k - 1) * (3 * k - 1).choose 2 = Q at h4 h5
  omega

end Gen

end OMA.SH

namespace OMA.R_Erdos1020_erdos_1020_R1_H2_R1_H1_R1

open Erdos1020

def H1 : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    f (5 * k - 2) 3 k ≤ max ((3 * k - 1).choose 3)
      ((5 * k - 2).choose 3 - (5 * k - 2 - k + 1).choose 3)

def H2 : Prop :=
  ∀ r : ℕ, 4 ≤ r → ∀ k : ℕ, 3 ≤ k →
    f ((2 * k - 1) * r - k + 1) r k ≤
      ((2 * k - 1) * r - k + 1).choose r - ((2 * k - 1) * r - k + 1 - k + 1).choose r

theorem n0_eq (r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) :
    (2 * k - 1) * r - k + 1 = r * k + (k - 1) * (r - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
  rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega, Nat.add_sub_cancel, Nat.add_sub_cancel]
  have e1 : (2 * j + 1) * (q + 1) = 2 * (j * q) + 2 * j + q + 1 := by ring
  have e2 : (q + 1) * (j + 1) + j * q = 2 * (j * q) + q + j + 1 := by ring
  rw [e1, e2]
  omega

theorem main : H1 → H2 → OMA.R_Erdos1020_erdos_1020_R1_H2_R1.H1 := by
  intro h1 h2 r hr n k hk hn
  have hyp : ∀ r', 3 ≤ r' → f (r' * k + (k - 1) * (r' - 1)) r' k ≤
      (r' * k + (k - 1) * (r' - 1)).choose r' -
        (r' * k + (k - 1) * (r' - 1) - k + 1).choose r' := by
    intro r' hr'
    rw [← n0_eq r' k (by omega) (by omega)]
    rcases (show r' = 3 ∨ 4 ≤ r' by omega) with rfl | hr4
    · have hb := h1 k hk
      rw [max_eq_right (OMA.SH.clique_le_star k (by omega))] at hb
      rw [show (2 * k - 1) * 3 - k + 1 = 5 * k - 2 by omega]
      exact hb
    · exact h2 r' hr4 k hk
  have hn' : r * k + (k - 1) * (r - 1) ≤ n := by
    rw [← n0_eq r k (by omega) (by omega)]; exact hn
  exact le_trans (OMA.SH.from_points k (by omega) hyp r (by omega) n hn') (le_max_right _ _)

end OMA.R_Erdos1020_erdos_1020_R1_H2_R1_H1_R1

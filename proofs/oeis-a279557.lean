import OMAStatements.S_oeis_a279557

namespace OeisA279557Proof

open Finset
open OMA.S_oeis_a279557

/-! ### Part A: Ballot triangle G and Catalan identities -/

def G : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _ + 1, 0 => 0
  | m + 1, d + 1 => G (m + 1) d + G m (d + 2)
termination_by m d => (m, d)

@[simp] lemma G_zero_left (d : ℕ) : G 0 d = 1 := by simp [G]

@[simp] lemma G_succ_zero (m : ℕ) : G (m + 1) 0 = 0 := by simp [G]

lemma G_succ_succ (m d : ℕ) : G (m + 1) (d + 1) = G (m + 1) d + G m (d + 2) := by
  rw [G]

lemma G_succ_right (m d : ℕ) :
    G m (d + 1) = ∑ i ∈ Finset.range (m + 1), catalan i * G (m - i) d := by
  induction m using Nat.strongRecOn generalizing d with
  | ind m ih =>
    cases m with
    | zero =>
      simp [catalan_zero]
    | succ m =>
      have h_zero : ∀ k ≤ m, G k 1 = catalan k := by
        intro k hk
        rw [ih k (by omega) 0]
        rw [Finset.sum_eq_single k]
        · simp
        · intro i hi hne
          have hlt : i < k := by
            have := Finset.mem_range.mp hi
            omega
          have hsub : k - i = (k - i - 1) + 1 := by omega
          rw [hsub, G_succ_zero, mul_zero]
        · intro hk_not
          exfalso
          exact hk_not (Finset.mem_range.mpr (by omega))
      induction d with
      | zero =>
        have hlhs : G (m + 1) 1 = catalan (m + 1) := by
          rw [G_succ_succ, G_succ_zero, zero_add, ih m (by omega) 1]
          have hcongr : ∑ i ∈ Finset.range (m + 1), catalan i * G (m - i) 1 =
              ∑ i ∈ Finset.range (m + 1), catalan i * catalan (m - i) := by
            refine Finset.sum_congr rfl fun i hi => ?_
            have := Finset.mem_range.mp hi
            rw [h_zero (m - i) (by omega)]
          rw [hcongr, catalan_succ, Finset.sum_range]
        rw [hlhs]
        symm
        rw [Finset.sum_eq_single (m + 1)]
        · simp
        · intro i hi hne
          have hlt : i < m + 1 := by
            have := Finset.mem_range.mp hi
            omega
          have hsub : m + 1 - i = (m - i) + 1 := by omega
          rw [hsub, G_succ_zero, mul_zero]
        · intro hnot
          exfalso
          exact hnot (Finset.mem_range.mpr (by omega))
      | succ d ih_d =>
        rw [G_succ_succ, ih_d, ih m (by omega) (d + 2)]
        rw [Finset.sum_range_succ (fun i => catalan i * G (m + 1 - i) d) (m + 1)]
        rw [Finset.sum_range_succ (fun i => catalan i * G (m + 1 - i) (d + 1)) (m + 1)]
        simp only [Nat.sub_self, G_zero_left, mul_one]
        rw [add_right_comm, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun i hi => ?_
        have hlt : i < m + 1 := Finset.mem_range.mp hi
        have hsub : m + 1 - i = (m - i) + 1 := by omega
        rw [hsub, ← mul_add, ← G_succ_succ]

lemma G_one (m : ℕ) : G m 1 = catalan m := by
  rw [G_succ_right m 0, Finset.sum_eq_single m]
  · simp
  · intro i hi hne
    have hlt : i < m := by
      have := Finset.mem_range.mp hi
      omega
    have hsub : m - i = (m - i - 1) + 1 := by omega
    rw [hsub, G_succ_zero, mul_zero]
  · intro hnot
    exfalso
    exact hnot (Finset.mem_range.mpr (by omega))

lemma G_horiz_sum (m a L : ℕ) :
    G (m + 1) a + ∑ j ∈ Finset.range L, G m (a + 2 + j) = G (m + 1) (a + L) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih]
    have h1 : a + 2 + L = a + L + 2 := by omega
    have h2 : a + (L + 1) = (a + L) + 1 := by omega
    rw [h1, h2, ← G_succ_succ]

lemma G_diag_sum (M c : ℕ) :
    1 + ∑ k ∈ Finset.range M, G (M - k) (c + k) = G M (c + 1) := by
  induction M generalizing c with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.sub_zero, add_zero]
    have hcongr : ∑ k ∈ Finset.range M, G (M + 1 - (k + 1)) (c + (k + 1)) =
        ∑ k ∈ Finset.range M, G (M - k) ((c + 1) + k) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      have h1 : M + 1 - (k + 1) = M - k := by omega
      have h2 : c + (k + 1) = (c + 1) + k := by omega
      rw [h1, h2]
    rw [hcongr]
    calc
      1 + (∑ k ∈ Finset.range M, G (M - k) ((c + 1) + k) + G (M + 1) c)
          = G (M + 1) c + (1 + ∑ k ∈ Finset.range M, G (M - k) ((c + 1) + k)) := by ring
      _ = G (M + 1) c + G M (c + 2) := by rw [ih (c + 1)]
      _ = G (M + 1) (c + 1) := (G_succ_succ M c).symm

lemma G_double_sum (M p₁ : ℕ) :
    G M 1 + ∑ k ∈ Finset.range M, ∑ j ∈ Finset.range p₁, G (M - 1 - k) (k + 2 + j) =
      G M (p₁ + 1) := by
  have h0 : 1 + ∑ k ∈ Finset.range M, G (M - k) k = G M 1 := by
    simpa using G_diag_sum M 0
  rw [← h0, add_assoc, ← Finset.sum_add_distrib]
  have hcongr : ∑ k ∈ Finset.range M,
      (G (M - k) k + ∑ j ∈ Finset.range p₁, G (M - 1 - k) (k + 2 + j)) =
      ∑ k ∈ Finset.range M, G (M - k) (p₁ + k) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hlt : k < M := Finset.mem_range.mp hk
    have hsub : M - k = (M - 1 - k) + 1 := by omega
    rw [hsub, G_horiz_sum (M - 1 - k) k p₁, add_comm k p₁]
  rw [hcongr, G_diag_sum M p₁]

lemma algebraic_main {n : ℕ} (hn : 1 ≤ n) :
    (1 + ∑ p₁ ∈ Finset.Ico 1 n, ∑ k ∈ Finset.range (n - p₁), ∑ j ∈ Finset.range p₁,
      G (n - p₁ - 1 - k) (k + 2 + j)) + ∑ i ∈ Finset.Icc 1 n, catalan i = catalan (n + 1) := by
  have hcat_sum : ∑ i ∈ Finset.Icc 1 n, catalan i =
      (∑ p₁ ∈ Finset.Ico 1 n, G (n - p₁) 1) + G n 1 := by
    have hsplit : Finset.Icc 1 n = insert n (Finset.Ico 1 n) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]
      omega
    have hnotmem : n ∉ Finset.Ico 1 n := by simp
    rw [hsplit, Finset.sum_insert hnotmem, add_comm, ← G_one n]
    congr 1
    refine Finset.sum_nbij (fun i => n - i) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_Ico] at hi ⊢
      omega
    · intro a ha b hb hab
      dsimp only at hab
      simp only [Finset.mem_coe, Finset.mem_Ico] at ha hb
      omega
    · intro y hy
      simp only [Finset.mem_coe, Finset.mem_Ico] at hy
      refine ⟨n - y, ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_Ico]
        omega
      · dsimp only
        omega
    · intro i hi
      simp only [Finset.mem_Ico] at hi
      rw [← G_one i]
      have : n - (n - i) = i := by omega
      rw [this]
  rw [hcat_sum]
  have hcombine :
      (1 + ∑ p₁ ∈ Finset.Ico 1 n, ∑ k ∈ Finset.range (n - p₁), ∑ j ∈ Finset.range p₁,
        G (n - p₁ - 1 - k) (k + 2 + j)) + ((∑ p₁ ∈ Finset.Ico 1 n, G (n - p₁) 1) + G n 1) =
      1 + (G n 1 + ∑ p₁ ∈ Finset.Ico 1 n, G (n - p₁) (p₁ + 1)) := by
    have hsum_eq :
        (∑ p₁ ∈ Finset.Ico 1 n, G (n - p₁) 1) +
        (∑ p₁ ∈ Finset.Ico 1 n, ∑ k ∈ Finset.range (n - p₁), ∑ j ∈ Finset.range p₁,
          G (n - p₁ - 1 - k) (k + 2 + j)) =
        ∑ p₁ ∈ Finset.Ico 1 n, G (n - p₁) (p₁ + 1) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p₁ _ => G_double_sum (n - p₁) p₁
    linarith
  rw [hcombine]
  have hdiag_reindex :
      G n 1 + ∑ p₁ ∈ Finset.Ico 1 n, G (n - p₁) (p₁ + 1) =
      ∑ k ∈ Finset.range n, G (n - k) (1 + k) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Finset.sum_range_succ']
    simp only [Nat.sub_zero, add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_nbij (fun p₁ => p₁ - 1) ?_ ?_ ?_ ?_
    · intro p₁ hp₁
      simp only [Finset.mem_Ico, Finset.mem_range] at hp₁ ⊢
      omega
    · intro a ha b hb hab
      dsimp only at hab
      simp only [Finset.mem_coe, Finset.mem_Ico] at ha hb
      omega
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_range] at hk
      refine ⟨k + 1, ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_Ico]
        omega
      · dsimp only
        omega
    · intro p₁ hp₁
      simp only [Finset.mem_Ico] at hp₁
      have h1 : m + 1 - (p₁ - 1 + 1) = m + 1 - p₁ := by omega
      have h2 : 1 + (p₁ - 1 + 1) = p₁ + 1 := by omega
      rw [h1, h2]
  rw [hdiag_reindex, G_diag_sum n 1, ← G_one (n + 1), G_succ_succ, G_succ_zero, zero_add]

/-! ### Part B: Monotone bounded suffixes SSet and cardinality G -/

def SSet (m k v : ℕ) : Finset (Fin m → ℕ) :=
  (Fintype.piFinset fun t : Fin m => Finset.Icc v (k + t.val)).filter Monotone

lemma mem_SSet {m k v : ℕ} {f : Fin m → ℕ} :
    f ∈ SSet m k v ↔ (∀ t : Fin m, v ≤ f t ∧ f t ≤ k + t.val) ∧ Monotone f := by
  simp [SSet, Fintype.mem_piFinset, Finset.mem_Icc]

lemma card_SSet (m : ℕ) : ∀ k v : ℕ, v ≤ k + 1 → (SSet m k v).card = G m (k + 1 - v) := by
  induction m with
  | zero =>
    intro k v _
    have huniv : SSet 0 k v = Finset.univ := by
      ext f
      simp only [mem_SSet, Finset.mem_univ, iff_true]
      refine ⟨fun t => Fin.elim0 t, fun a => Fin.elim0 a⟩
    rw [huniv, Finset.card_univ, Fintype.card_unique, G_zero_left]
  | succ m ihm =>
    intro k v hvk
    generalize hd : k + 1 - v = d
    induction d generalizing k v with
    | zero =>
      have hveq : v = k + 1 := by omega
      subst hveq
      have hempty : SSet (m + 1) k (k + 1) = ∅ := by
        ext f
        simp only [mem_SSet, Finset.notMem_empty, iff_false, not_and]
        intro hbounds _
        have h0 := hbounds 0
        simp only [Fin.val_zero, add_zero] at h0
        omega
      rw [hempty, Finset.card_empty, G_succ_zero]
    | succ d ihd =>
      have hvle : v ≤ k := by omega
      have hsplit := (Finset.card_filter_add_card_filter_not (s := SSet (m + 1) k v)
        (fun f => v + 1 ≤ f 0)).symm
      rw [hsplit]
      have hleft : (SSet (m + 1) k v).filter (fun f => v + 1 ≤ f 0) = SSet (m + 1) k (v + 1) := by
        ext f
        simp only [Finset.mem_filter, mem_SSet]
        constructor
        · rintro ⟨⟨hb, hmono⟩, h0⟩
          refine ⟨fun t => ⟨?_, (hb t).2⟩, hmono⟩
          have h0t : f 0 ≤ f t := hmono (Fin.zero_le t)
          omega
        · rintro ⟨hb, hmono⟩
          refine ⟨⟨fun t => ⟨?_, (hb t).2⟩, hmono⟩, (hb 0).1⟩
          have := (hb t).1
          omega
      have hright : ((SSet (m + 1) k v).filter (fun f => ¬ v + 1 ≤ f 0)).card =
          (SSet m (k + 1) v).card := by
        refine Finset.card_bij (fun f _ => fun t : Fin m => f t.succ) ?_ ?_ ?_
        · intro f hf
          simp only [Finset.mem_filter, mem_SSet] at hf ⊢
          rcases hf with ⟨⟨hb, hmono⟩, _⟩
          refine ⟨fun t => ?_, fun a b hab => hmono (Fin.succ_le_succ_iff.mpr hab)⟩
          have ht := hb t.succ
          simp only [Fin.val_succ] at ht
          omega
        · intro f₁ hf₁ f₂ hf₂ heq
          simp only [Finset.mem_filter, mem_SSet] at hf₁ hf₂
          have hf10 : f₁ 0 = v := by
            have := (hf₁.1.1 0).1
            omega
          have hf20 : f₂ 0 = v := by
            have := (hf₂.1.1 0).1
            omega
          funext i
          refine Fin.cases ?_ ?_ i
          · rw [hf10, hf20]
          · intro t
            exact congr_fun heq t
        · intro s hs
          rw [mem_SSet] at hs
          refine ⟨Fin.cons v s, ?_, ?_⟩
          · simp only [Finset.mem_filter, mem_SSet, Fin.cons_zero]
            refine ⟨⟨?_, ?_⟩, by omega⟩
            · intro i
              refine Fin.cases ?_ ?_ i
              · simp only [Fin.cons_zero, Fin.val_zero, add_zero]
                omega
              · intro t
                simp only [Fin.cons_succ, Fin.val_succ]
                have ht := hs.1 t
                omega
            · intro a b
              refine Fin.cases ?_ (fun a' => ?_) a
              · refine Fin.cases ?_ (fun b' => ?_) b
                · intro _
                  simp
                · intro _
                  simp only [Fin.cons_zero, Fin.cons_succ]
                  exact (hs.1 b').1
              · refine Fin.cases ?_ (fun b' => ?_) b
                · intro hab
                  exfalso
                  exact Nat.not_succ_le_zero a'.val hab
                · intro hab
                  simp only [Fin.cons_succ]
                  exact hs.2 (Fin.succ_le_succ_iff.mp hab)
          · funext t
            simp
      rw [hleft, hright, ihd k (v + 1) (by omega) (by omega), ihm (k + 1) v (by omega)]
      have hd2 : k + 1 + 1 - v = d + 2 := by omega
      rw [hd2, G_succ_succ]

/-! ### Part C: Structural characterization of Avoids -/

def Good {n : ℕ} (e : InversionSeq n) : Prop :=
  (∀ u w : Fin n, u < w → 0 < (e u).val → 0 < (e w).val → (e u).val ≤ (e w).val) ∧
  (∀ u w z : Fin n, u < w → w < z → 0 < (e u).val → 0 < (e w).val → 0 < (e z).val)

lemma avoids_iff_good {n : ℕ} (e : InversionSeq n) : Avoids e ↔ Good e := by
  constructor
  · intro h
    have h1 : ∀ u w : Fin n, u < w → 0 < (e u).val → 0 < (e w).val → (e u).val ≤ (e w).val := by
      intro u w huw hu hw
      by_contra hlt
      push Not at hlt
      have hu_pos : 0 < u.val := by
        by_contra h0
        have hu0 : u.val = 0 := by omega
        have := (e u).isLt
        omega
      let z0 : Fin n := ⟨0, by omega⟩
      have hz0_val : (e z0).val = 0 := by
        have hlt0 := (e z0).isLt
        have hz00 : z0.val = 0 := rfl
        omega
      have hz0u : z0 < u := hu_pos
      have heq := h z0 u w hz0u huw (by omega) hlt
      omega
    refine ⟨h1, ?_⟩
    intro u w z huw hwz hu hw
    by_contra hz0
    have hzeq : (e z).val = 0 := by omega
    have hle : (e u).val ≤ (e w).val := h1 u w huw hu hw
    have heq := h u w z huw hwz hle (by omega)
    omega
  · rintro ⟨h1, h2⟩ i j k hij hjk hle hlt
    have hj : 0 < (e j).val := by omega
    have hk0 : (e k).val = 0 := by
      by_contra hk
      have hkpos : 0 < (e k).val := by omega
      have := h1 j k hjk hj hkpos
      omega
    have hi0 : (e i).val = 0 := by
      by_contra hi
      have hipos : 0 < (e i).val := by omega
      have := h2 i j k hij hjk hipos hj
      omega
    omega

/-! ### Part D: Bijection for count n and main proof -/

def zeroSeq (n : ℕ) : InversionSeq n := fun _ => ⟨0, Nat.zero_lt_succ _⟩

lemma avoids_zeroSeq (n : ℕ) : Avoids (zeroSeq n) := by
  rw [avoids_iff_good]
  exact ⟨fun u _ _ hu => by simp [zeroSeq] at hu, fun u _ _ _ _ hu => by simp [zeroSeq] at hu⟩

def ParamSet (n : ℕ) :=
  (Finset.Ico 1 n).sigma fun p₁ =>
    (Finset.Icc 1 p₁).sigma fun v =>
      (Finset.Icc (p₁ + 1) n).sigma fun p₂ =>
        SSet (n - p₂) p₂ v

abbrev Param (n : ℕ) := Σ _p₁ : ℕ, Σ _v : ℕ, Σ p₂ : ℕ, (Fin (n - p₂) → ℕ)

lemma mem_ParamSet {n : ℕ} {x : Param n} :
    x ∈ ParamSet n ↔
      (1 ≤ x.1 ∧ x.1 < n) ∧
      (1 ≤ x.2.1 ∧ x.2.1 ≤ x.1) ∧
      (x.1 + 1 ≤ x.2.2.1 ∧ x.2.2.1 ≤ n) ∧
      x.2.2.2 ∈ SSet (n - x.2.2.1) x.2.2.1 x.2.1 := by
  simp [ParamSet, Finset.mem_sigma, Finset.mem_Ico, Finset.mem_Icc]

def mkSeq {n : ℕ} (x : Param n)
    (hx : x ∈ ParamSet n) : InversionSeq n := fun i =>
  if h1 : i.val = x.1 then
    ⟨x.2.1, by
      have h := (mem_ParamSet.mp hx).2.1.2
      omega⟩
  else if h2 : x.2.2.1 ≤ i.val then
    ⟨x.2.2.2 ⟨i.val - x.2.2.1, by omega⟩, by
      have hs := (mem_SSet.mp (mem_ParamSet.mp hx).2.2.2).1 ⟨i.val - x.2.2.1, by omega⟩
      have hle := hs.2
      dsimp only at hle
      omega⟩
  else
    ⟨0, Nat.zero_lt_succ _⟩

lemma mkSeq_val_at_p1 {n : ℕ} (x : Param n)
    (hx : x ∈ ParamSet n) (hlt : x.1 < n) :
    (mkSeq x hx ⟨x.1, hlt⟩).val = x.2.1 := by
  simp [mkSeq]

lemma mkSeq_val_lt_p1 {n : ℕ} (x : Param n)
    (hx : x ∈ ParamSet n) (i : Fin n) (hi : i.val < x.1) :
    (mkSeq x hx i).val = 0 := by
  have hp := (mem_ParamSet.mp hx).2.2.1.1
  have h1 : i.val ≠ x.1 := by omega
  have h2 : ¬ x.2.2.1 ≤ i.val := by omega
  simp [mkSeq, h1, h2]

lemma mkSeq_val_between {n : ℕ} (x : Param n)
    (hx : x ∈ ParamSet n) (i : Fin n) (hi1 : x.1 < i.val) (hi2 : i.val < x.2.2.1) :
    (mkSeq x hx i).val = 0 := by
  have h1 : i.val ≠ x.1 := by omega
  have h2 : ¬ x.2.2.1 ≤ i.val := by omega
  simp [mkSeq, h1, h2]

lemma mkSeq_val_ge_p2 {n : ℕ} (x : Param n)
    (hx : x ∈ ParamSet n) (i : Fin n) (hi : x.2.2.1 ≤ i.val) :
    (mkSeq x hx i).val = x.2.2.2 ⟨i.val - x.2.2.1, by omega⟩ := by
  have hp := (mem_ParamSet.mp hx).2.2.1.1
  have h1 : i.val ≠ x.1 := by omega
  simp [mkSeq, h1, hi]

lemma mkSeq_good {n : ℕ} (x : Param n)
    (hx : x ∈ ParamSet n) : Good (mkSeq x hx) := by
  have hmem := mem_ParamSet.mp hx
  have hs := mem_SSet.mp hmem.2.2.2
  have hpos_cases : ∀ u : Fin n, 0 < (mkSeq x hx u).val → u.val = x.1 ∨ x.2.2.1 ≤ u.val := by
    intro u hu
    by_contra hnot
    push Not at hnot
    by_cases hlt : u.val < x.1
    · rw [mkSeq_val_lt_p1 x hx u hlt] at hu
      omega
    · rw [mkSeq_val_between x hx u (by omega) hnot.2] at hu
      omega
  refine ⟨?_, ?_⟩
  · intro u w huw hu hw
    rcases hpos_cases u hu with hu1 | hu2
    · rcases hpos_cases w hw with hw1 | hw2
      · exfalso
        have : u.val < w.val := huw
        omega
      · have hval_u : (mkSeq x hx u).val = x.2.1 := by
          have : u = ⟨x.1, hmem.1.2⟩ := Fin.ext hu1
          rw [this, mkSeq_val_at_p1]
        rw [hval_u, mkSeq_val_ge_p2 x hx w hw2]
        exact (hs.1 ⟨w.val - x.2.2.1, by omega⟩).1
    · have hw2 : x.2.2.1 ≤ w.val := by
        have : u.val < w.val := huw
        omega
      rw [mkSeq_val_ge_p2 x hx u hu2, mkSeq_val_ge_p2 x hx w hw2]
      exact hs.2 (show (⟨u.val - x.2.2.1, by omega⟩ : Fin (n - x.2.2.1)) ≤
        ⟨w.val - x.2.2.1, by omega⟩ from by
        change u.val - x.2.2.1 ≤ w.val - x.2.2.1
        have : u.val < w.val := huw
        omega)
  · intro u w z huw hwz hu hw
    have hu' : u.val < w.val := huw
    have hw' : w.val < z.val := hwz
    have hw2 : x.2.2.1 ≤ w.val := by
      rcases hpos_cases u hu with hu1 | hu2
      · rcases hpos_cases w hw with hw1 | hw2
        · omega
        · exact hw2
      · omega
    have hz2 : x.2.2.1 ≤ z.val := by omega
    rw [mkSeq_val_ge_p2 x hx z hz2]
    have hge := (hs.1 ⟨z.val - x.2.2.1, by omega⟩).1
    have hv1 := hmem.2.1.1
    omega

lemma mkSeq_ne_zeroSeq {n : ℕ} (x : Param n)
    (hx : x ∈ ParamSet n) : mkSeq x hx ≠ zeroSeq n := by
  intro heq
  have hmem := mem_ParamSet.mp hx
  have hval := congr_arg (fun f : InversionSeq n => (f ⟨x.1, hmem.1.2⟩).val) heq
  rw [mkSeq_val_at_p1] at hval
  simp only [zeroSeq] at hval
  omega

lemma card_erase_eq_card_ParamSet (n : ℕ) :
    open scoped Classical in
    ((Finset.univ.filter (Avoids (n := n))).erase (zeroSeq n)).card = (ParamSet n).card := by
  open scoped Classical in
  symm
  refine Finset.card_bij (fun x hx => mkSeq x hx) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨mkSeq_ne_zeroSeq x hx, (avoids_iff_good _).mpr (mkSeq_good x hx)⟩
  · intro x hx y hy heq
    have hxm := mem_ParamSet.mp hx
    have hym := mem_ParamSet.mp hy
    rcases x with ⟨p₁, v, p₂, s⟩
    rcases y with ⟨p₁', v', p₂', s'⟩
    dsimp only at hxm hym
    have hp1 : p₁ = p₁' := by
      rcases lt_trichotomy p₁ p₁' with hlt | heq1 | hgt
      · exfalso
        have hv := congr_arg (fun f : InversionSeq n => (f ⟨p₁, hxm.1.2⟩).val) heq
        rw [mkSeq_val_at_p1 _ hx hxm.1.2, mkSeq_val_lt_p1 _ hy ⟨p₁, hxm.1.2⟩ hlt] at hv
        dsimp only at hv
        omega
      · exact heq1
      · exfalso
        have hv := congr_arg (fun f : InversionSeq n => (f ⟨p₁', hym.1.2⟩).val) heq
        rw [mkSeq_val_lt_p1 _ hx ⟨p₁', hym.1.2⟩ hgt, mkSeq_val_at_p1 _ hy hym.1.2] at hv
        dsimp only at hv
        omega
    subst hp1
    have hv : v = v' := by
      have hval := congr_arg (fun f : InversionSeq n => (f ⟨p₁, hxm.1.2⟩).val) heq
      rw [mkSeq_val_at_p1 _ hx hxm.1.2, mkSeq_val_at_p1 _ hy hym.1.2] at hval
      exact hval
    subst hv
    have hp2 : p₂ = p₂' := by
      rcases lt_trichotomy p₂ p₂' with hlt | heq2 | hgt
      · exfalso
        have hlt_n : p₂ < n := by omega
        have hval := congr_arg (fun f : InversionSeq n => (f ⟨p₂, hlt_n⟩).val) heq
        rw [mkSeq_val_ge_p2 _ hx ⟨p₂, hlt_n⟩ le_rfl,
          mkSeq_val_between _ hy ⟨p₂, hlt_n⟩ (show p₁ < p₂ by omega) hlt] at hval
        dsimp only at hval
        have hs0 := (mem_SSet.mp hxm.2.2.2).1 ⟨p₂ - p₂, by omega⟩
        omega
      · exact heq2
      · exfalso
        have hlt_n : p₂' < n := by omega
        have hval := congr_arg (fun f : InversionSeq n => (f ⟨p₂', hlt_n⟩).val) heq
        rw [mkSeq_val_between _ hx ⟨p₂', hlt_n⟩ (show p₁ < p₂' by omega) hgt,
          mkSeq_val_ge_p2 _ hy ⟨p₂', hlt_n⟩ le_rfl] at hval
        dsimp only at hval
        have hs0 := (mem_SSet.mp hym.2.2.2).1 ⟨p₂' - p₂', by omega⟩
        omega
    subst hp2
    have hs : s = s' := by
      funext t
      have ht_lt := t.isLt
      have hlt_n : p₂ + t.val < n := by omega
      have hval := congr_arg (fun f : InversionSeq n => (f ⟨p₂ + t.val, hlt_n⟩).val) heq
      rw [mkSeq_val_ge_p2 _ hx ⟨p₂ + t.val, hlt_n⟩ (show p₂ ≤ p₂ + t.val by omega),
        mkSeq_val_ge_p2 _ hy ⟨p₂ + t.val, hlt_n⟩ (show p₂ ≤ p₂ + t.val by omega)] at hval
      dsimp only at hval
      have hidx : (⟨p₂ + t.val - p₂, by omega⟩ : Fin (n - p₂)) = t := by
        ext
        dsimp only
        omega
      simpa [hidx] using hval
    subst hs
    rfl
  · intro e he
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at he
    rcases he with ⟨hne_zero, havoids⟩
    have hgood : Good e := (avoids_iff_good e).mp havoids
    let P : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => 0 < (e i).val)
    have hPne : P.Nonempty := by
      by_contra hPe
      rw [Finset.not_nonempty_iff_eq_empty] at hPe
      apply hne_zero
      funext i
      apply Fin.ext
      have hi : i ∉ P := by rw [hPe]; simp
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and, not_lt, Nat.le_zero] at hi
      exact hi
    let i₁ : Fin n := P.min' hPne
    have hi₁_mem : i₁ ∈ P := Finset.min'_mem P hPne
    have hi₁_pos : 0 < (e i₁).val := (Finset.mem_filter.mp hi₁_mem).2
    have hp₁_pos : 1 ≤ i₁.val := by
      by_contra h0
      have hval0 : i₁.val = 0 := by omega
      have := (e i₁).isLt
      omega
    let p₁ : ℕ := i₁.val
    let v : ℕ := (e i₁).val
    have hv_le : v ≤ p₁ := by
      have := (e i₁).isLt
      omega
    let P' : Finset (Fin n) := P.erase i₁
    let p₂ : ℕ := if h' : P'.Nonempty then (P'.min' h').val else n
    have hp₂_bounds : p₁ + 1 ≤ p₂ ∧ p₂ ≤ n := by
      by_cases h' : P'.Nonempty
      · simp only [p₂, h', dif_pos]
        have hm := Finset.min'_mem P' h'
        have hmP : P'.min' h' ∈ P := (Finset.mem_erase.mp hm).2
        have hmne : P'.min' h' ≠ i₁ := (Finset.mem_erase.mp hm).1
        have hle : i₁ ≤ P'.min' h' := Finset.min'_le P _ hmP
        have hlt : i₁ < P'.min' h' := lt_of_le_of_ne hle hmne.symm
        exact ⟨hlt, Nat.le_of_lt (P'.min' h').isLt⟩
      · simp only [p₂, h', dif_neg, not_false_eq_true]
        exact ⟨i₁.isLt, le_rfl⟩
    let s : Fin (n - p₂) → ℕ := fun t => (e ⟨p₂ + t.val, by have := t.isLt; omega⟩).val
    have hs_mem : s ∈ SSet (n - p₂) p₂ v := by
      rw [mem_SSet]
      have hpos_all : ∀ t : Fin (n - p₂), 0 < (e ⟨p₂ + t.val, by have := t.isLt; omega⟩).val := by
        intro t
        have ht_lt := t.isLt
        have hp₂_lt : p₂ < n := by omega
        have h' : P'.Nonempty := by
          by_contra hne'
          simp only [p₂, hne', dif_neg, not_false_eq_true] at hp₂_lt
          omega
        let i₂ : Fin n := P'.min' h'
        have hi₂_val : i₂.val = p₂ := by simp only [p₂, h', dif_pos, i₂]
        have hi₂_mem : i₂ ∈ P := (Finset.mem_erase.mp (Finset.min'_mem P' h')).2
        have hi₂_pos : 0 < (e i₂).val := (Finset.mem_filter.mp hi₂_mem).2
        have hi₁_lt_i₂ : i₁ < i₂ := by
          change i₁.val < i₂.val
          omega
        by_cases ht0 : t.val = 0
        · have heq_idx : (⟨p₂ + t.val, by omega⟩ : Fin n) = i₂ := by
            ext
            dsimp only
            omega
          rw [heq_idx]
          exact hi₂_pos
        · have hi₂_lt : i₂ < ⟨p₂ + t.val, by omega⟩ := by
            change i₂.val < p₂ + t.val
            omega
          exact hgood.2 i₁ i₂ ⟨p₂ + t.val, by omega⟩ hi₁_lt_i₂ hi₂_lt hi₁_pos hi₂_pos
      refine ⟨fun t => ⟨?_, ?_⟩, ?_⟩
      · have hi₁_lt : i₁ < ⟨p₂ + t.val, by have := t.isLt; omega⟩ := by
          change i₁.val < p₂ + t.val
          omega
        exact hgood.1 i₁ ⟨p₂ + t.val, by have := t.isLt; omega⟩ hi₁_lt hi₁_pos (hpos_all t)
      · have hlt := (e ⟨p₂ + t.val, by have := t.isLt; omega⟩).isLt
        dsimp only [s] at hlt ⊢
        omega
      · intro a b hab
        by_cases heq_ab : a = b
        · subst heq_ab
          exact le_rfl
        · have hlt_ab : (⟨p₂ + a.val, by have := a.isLt; omega⟩ : Fin n) <
              ⟨p₂ + b.val, by have := b.isLt; omega⟩ := by
            change p₂ + a.val < p₂ + b.val
            have : a.val < b.val := lt_of_le_of_ne hab (fun h => heq_ab (Fin.ext h))
            omega
          exact hgood.1 _ _ hlt_ab (hpos_all a) (hpos_all b)
    let x : Param n := ⟨p₁, v, p₂, s⟩
    have hx : x ∈ ParamSet n := by
      rw [mem_ParamSet]
      exact ⟨⟨hp₁_pos, i₁.isLt⟩, ⟨hi₁_pos, hv_le⟩, hp₂_bounds, hs_mem⟩
    refine ⟨x, hx, ?_⟩
    funext i
    apply Fin.ext
    by_cases h1 : i.val = p₁
    · have hi_eq : i = i₁ := Fin.ext h1
      subst hi_eq
      exact mkSeq_val_at_p1 x hx i₁.isLt
    · by_cases hlt1 : i.val < p₁
      · rw [mkSeq_val_lt_p1 x hx i hlt1]
        by_contra hne0
        have hiP : i ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
        have hle := Finset.min'_le P i hiP
        have : i₁.val ≤ i.val := hle
        omega
      · by_cases hge2 : p₂ ≤ i.val
        · rw [mkSeq_val_ge_p2 x hx i hge2]
          dsimp only [x, s]
          have hidx : (⟨p₂ + (i.val - p₂), by have := i.isLt; omega⟩ : Fin n) = i :=
            Fin.ext (by dsimp only; omega)
          exact congr_arg (fun j : Fin n => (e j).val) hidx
        · rw [mkSeq_val_between x hx i (show x.1 < i.val by dsimp only [x]; omega)
            (show i.val < x.2.2.1 by dsimp only [x]; omega)]
          by_contra hne0
          have hiP : i ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
          have hi_ne : i ≠ i₁ := fun h => h1 (congr_arg Fin.val h)
          have hiP' : i ∈ P' := Finset.mem_erase.mpr ⟨hi_ne, hiP⟩
          have h' : P'.Nonempty := ⟨i, hiP'⟩
          have hle : P'.min' h' ≤ i := Finset.min'_le P' i hiP'
          have hp₂_eq : p₂ = (P'.min' h').val := by simp only [p₂, h', dif_pos]
          have : (P'.min' h').val ≤ i.val := hle
          omega

lemma card_ParamSet (n : ℕ) :
    (ParamSet n).card =
      ∑ p₁ ∈ Finset.Ico 1 n, ∑ k ∈ Finset.range (n - p₁), ∑ j ∈ Finset.range p₁,
        G (n - p₁ - 1 - k) (k + 2 + j) := by
  simp only [ParamSet, Finset.card_sigma]
  refine Finset.sum_congr rfl fun p₁ hp₁ => ?_
  have hp₁_bounds := Finset.mem_Ico.mp hp₁
  have hinner :
      ∑ v ∈ Finset.Icc 1 p₁, ∑ p₂ ∈ Finset.Icc (p₁ + 1) n, (SSet (n - p₂) p₂ v).card =
      ∑ v ∈ Finset.Icc 1 p₁, ∑ p₂ ∈ Finset.Icc (p₁ + 1) n, G (n - p₂) (p₂ + 1 - v) := by
    refine Finset.sum_congr rfl fun v hv => Finset.sum_congr rfl fun p₂ hp₂ => ?_
    have hv_b := Finset.mem_Icc.mp hv
    have hp₂_b := Finset.mem_Icc.mp hp₂
    exact card_SSet (n - p₂) p₂ v (by omega)
  rw [hinner, Finset.sum_comm]
  refine Finset.sum_nbij (fun p₂ => p₂ - (p₁ + 1)) ?_ ?_ ?_ ?_
  · intro p₂ hp₂
    have hp₂_b := Finset.mem_Icc.mp hp₂
    exact Finset.mem_range.mpr (by omega)
  · intro a ha b hb hab
    dsimp only at hab
    have ha_b := Finset.mem_Icc.mp ha
    have hb_b := Finset.mem_Icc.mp hb
    omega
  · intro k hk
    simp only [Finset.mem_coe, Finset.mem_range] at hk
    refine ⟨p₁ + 1 + k, ?_, ?_⟩
    · simp only [Finset.mem_coe, Finset.mem_Icc]
      omega
    · dsimp only
      omega
  · intro p₂ hp₂
    have hp₂_b := Finset.mem_Icc.mp hp₂
    refine Finset.sum_nbij (fun v => p₁ - v) ?_ ?_ ?_ ?_
    · intro v hv
      have hv_b := Finset.mem_Icc.mp hv
      exact Finset.mem_range.mpr (by omega)
    · intro a ha b hb hab
      dsimp only at hab
      have ha_b := Finset.mem_Icc.mp ha
      have hb_b := Finset.mem_Icc.mp hb
      omega
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_range] at hj
      refine ⟨p₁ - j, ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_Icc]
        omega
      · dsimp only
        omega
    · intro v hv
      have hv_b := Finset.mem_Icc.mp hv
      have h1 : n - p₂ = n - p₁ - 1 - (p₂ - (p₁ + 1)) := by omega
      have h2 : p₂ + 1 - v = (p₂ - (p₁ + 1)) + 2 + (p₁ - v) := by omega
      rw [h1, h2]

lemma main_proof : ∀ n : ℕ, count n + ∑ i ∈ Finset.Icc 1 n, catalan i = catalan (n + 1) := by
  intro n
  cases n with
  | zero =>
    have hcnt : count 0 = 1 := by
      unfold count
      open scoped Classical in
      have hfilt : (Finset.univ : Finset (InversionSeq 0)).filter Avoids = Finset.univ := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        intro i
        exact Fin.elim0 i
      rw [hfilt, Finset.card_univ, Fintype.card_pi]
      simp
    rw [hcnt]
    simp [catalan_one]
  | succ m =>
    have hcnt : count (m + 1) = 1 + (ParamSet (m + 1)).card := by
      unfold count
      open scoped Classical in
      have hmem : zeroSeq (m + 1) ∈ (Finset.univ : Finset (InversionSeq (m + 1))).filter Avoids :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, avoids_zeroSeq (m + 1)⟩
      have herase := Finset.card_erase_add_one hmem
      rw [← herase, add_comm, card_erase_eq_card_ParamSet (m + 1)]
    rw [hcnt, card_ParamSet (m + 1)]
    exact algebraic_main (Nat.succ_pos m)

end OeisA279557Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a279557.main := OeisA279557Proof.main_proof

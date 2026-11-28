import OMAStatements.S_oeis_a223756

-- Problem: A223756: Number of n x 2 0..3 arrays with rows, antidiagonals and columns unimodal.
-- Credit: @ceejcake
-- Proof:
-- 1. In an n x 2 array, every row and every antidiagonal has length <= 2, hence is automatically unimodal.
-- 2. Thus valid arrays biject with pairs of unimodal length-n words over Fin 4, so a(n) = U(n)^2.
-- 3. Partitioning unimodal words by (max value m in 0..3, first peak index p) and applying the
--    binomial convolution identity sum_{p < n} C(p+a, a) * C(n-1-p+b, b) = C(n+a+b, a+b+1) gives
--    U(n) = 1 + C(n+1, 2) + C(n+3, 4) + C(n+5, 6), a degree-6 polynomial in n.
-- 4. Therefore a(n) = U(n)^2 is a degree-12 polynomial in n, yielding both the order-13 recurrence
--    and the rational generating function.

namespace ProofA223756

open OMA.S_oeis_a223756
open scoped Classical
noncomputable section

-- Step 1: Any list of length <= 2 is unimodal
private lemma isUnimodal_of_length_le_two (L : List (Fin 4)) (hL : L.length ≤ 2) : IsUnimodal L := by
  by_cases h1 : L.length ≤ 1
  · refine ⟨⟨0, by omega⟩, fun i j _ hj => ?_, fun i j _ hij => ?_⟩
    · have : i = j := Fin.ext (by have := i.2; have := j.2; omega)
      rw [this]
    · have : i = j := Fin.ext (by have := i.2; have := j.2; omega)
      rw [this]
  · have h2 : L.length = 2 := by omega
    by_cases hle : L[0]'(by omega) ≤ L[1]'(by omega)
    · refine ⟨⟨2, by omega⟩, fun i j hij _ => ?_, fun i j hi _ => ?_⟩
      · have hi2 := i.2; have hj2 := j.2
        have hle' : i.1 ≤ j.1 := hij
        by_cases heq : i.1 = j.1
        · rw [Fin.ext heq]
        · have hi0 : i.1 = 0 := by omega
          have hj1 : j.1 = 1 := by omega
          simpa [hi0, hj1] using hle
      · exfalso; dsimp only at hi; have := i.2; omega
    · have hge : L[1]'(by omega) ≤ L[0]'(by omega) := le_of_not_ge hle
      refine ⟨⟨0, by omega⟩, fun i j hij hj => ?_, fun i j _ hij => ?_⟩
      · dsimp only at hj; have : i = j := Fin.ext (by have := hij; omega)
        rw [this]
      · have hi2 := i.2; have hj2 := j.2
        have hle' : i.1 ≤ j.1 := hij
        by_cases heq : i.1 = j.1
        · rw [Fin.ext heq]
        · have hi0 : i.1 = 0 := by omega
          have hj1 : j.1 = 1 := by omega
          simpa [hi0, hj1] using hge

private lemma row_isUnimodal (n : ℕ) (x : Fin n → Fin 2 → Fin 4) (i : Fin n) :
    IsUnimodal (row n x i) :=
  isUnimodal_of_length_le_two _ (by simp [row])

private lemma antidiag_length_le_two (n : ℕ) (x : Fin n → Fin 2 → Fin 4) (d : Fin (n + 1)) :
    (antidiag n x d).length ≤ 2 := by
  unfold antidiag
  have hlen : ∀ (l : List (Fin n)) (f : Fin n → Option (Fin 4)) (p : Fin n → Prop) [DecidablePred p],
      (∀ a, (f a).isSome → p a) → (l.filterMap f).length ≤ (l.filter (fun a => decide (p a))).length := by
    intro l f p _ hfp
    induction l with
    | nil => simp
    | cons a t ih =>
      simp only [List.filterMap_cons, List.filter_cons]
      cases hfa : f a with
      | none =>
        split_ifs <;> simp <;> omega
      | some v =>
        have hpa : p a := hfp a (by simp [hfa])
        simp only [decide_eq_true hpa, ↓reduceIte, List.length_cons]
        omega
  have h1 := hlen (List.finRange n)
    (fun i => if h : i.val ≤ d.val ∧ d.val - i.val < 2 then some (x i ⟨d.val - i.val, h.2⟩) else none)
    (fun i => i.val ≤ d.val ∧ d.val - i.val < 2)
    (fun i hi => by split_ifs at hi with h; exact h; simp at hi)
  have hsub : (((List.finRange n).filter (fun i => decide (i.val ≤ d.val ∧ d.val - i.val < 2))).toFinset).image Fin.val ⊆
      ({d.val, d.val - 1} : Finset ℕ) := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨i, hi, rfl⟩
    simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at hi
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hnodup : ((List.finRange n).filter (fun i => decide (i.val ≤ d.val ∧ d.val - i.val < 2))).Nodup :=
    (List.nodup_finRange n).filter _
  have hcard : ((List.finRange n).filter (fun i => decide (i.val ≤ d.val ∧ d.val - i.val < 2))).length =
      (((List.finRange n).filter (fun i => decide (i.val ≤ d.val ∧ d.val - i.val < 2))).toFinset.image Fin.val).card := by
    rw [Finset.card_image_of_injective _ Fin.val_injective, List.toFinset_card_of_nodup hnodup]
  have hle2 : ({d.val, d.val - 1} : Finset ℕ).card ≤ 2 := Finset.card_le_two
  have hle3 := Finset.card_le_card hsub
  omega

private lemma antidiag_isUnimodal (n : ℕ) (x : Fin n → Fin 2 → Fin 4) (d : Fin (n + 1)) :
    IsUnimodal (antidiag n x d) :=
  isUnimodal_of_length_le_two _ (antidiag_length_le_two n x d)

-- Step 2: a(n) = U(n)^2 where U(n) counts unimodal length-n words over Fin 4
private def Uset (n : ℕ) : Finset (Fin n → Fin 4) :=
  Finset.univ.filter (fun w => IsUnimodal (List.ofFn w))

private lemma a_eq_U_sq (n : ℕ) : a n = (Uset n).card ^ 2 := by
  unfold a
  rw [pow_two, ← Finset.card_product]
  refine Finset.card_bij (fun x _ => (fun i => x i 0, fun i => x i 1)) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, valid] at hx
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.2.2 0⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.2.2 1⟩⟩
  · intro x1 _ x2 _ h
    simp only [Prod.mk.injEq] at h
    funext i j; match j with
    | 0 => exact congr_fun h.1 i
    | 1 => exact congr_fun h.2 i
  · intro ⟨c0, c1⟩ h
    simp only [Finset.mem_product, Uset, Finset.mem_filter, Finset.mem_univ, true_and] at h
    refine ⟨fun i j => if j = 0 then c0 i else c1 i, ?_, by ext i <;> simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, valid]
    refine ⟨row_isUnimodal n _, antidiag_isUnimodal n _, fun j => ?_⟩
    match j with
    | 0 => simpa [col] using h.1
    | 1 => simpa [col] using h.2

-- Step 3: Count nondecreasing words of length L over Fin k
private def nondecSet (L k : ℕ) : Finset (Fin L → Fin k) :=
  Finset.univ.filter (fun w => ∀ i j : Fin L, i ≤ j → w i ≤ w j)

private lemma card_nondecSet : ∀ (s L k : ℕ), L + k = s → 1 ≤ k →
    (nondecSet L k).card = Nat.choose (L + k - 1) (k - 1) := by
  intro s
  induction s with
  | zero => intro L k h hk; omega
  | succ s ih =>
    intro L k hsum hk
    cases L with
    | zero =>
      have : nondecSet 0 k = Finset.univ := by
        ext w; simp only [nondecSet, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        intro i; exact Fin.elim0 i
      rw [this, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, pow_zero]
      simp [Nat.choose_self]
    | succ L =>
      match k with
      | 0 => omega
      | 1 =>
        have : nondecSet (L + 1) 1 = Finset.univ := by
          ext w; simp only [nondecSet, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          intro i j _; exact le_of_eq (Subsingleton.elim _ _)
        rw [this, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, one_pow]
        simp
      | k + 2 =>
        -- Split by whether last entry = k + 1 or < k + 1
        let A := (nondecSet (L + 1) (k + 2)).filter (fun w => w ⟨L, by omega⟩ = ⟨k + 1, by omega⟩)
        let B := (nondecSet (L + 1) (k + 2)).filter (fun w => w ⟨L, by omega⟩ ≠ ⟨k + 1, by omega⟩)
        have hpart := Finset.card_filter_add_card_filter_not (s := nondecSet (L + 1) (k + 2))
          (p := fun w => w ⟨L, by omega⟩ = ⟨k + 1, by omega⟩)
        have hA : A.card = (nondecSet L (k + 2)).card := by
          refine Finset.card_bij (fun w _ i => w ⟨i.1, by omega⟩) ?_ ?_ ?_
          · intro w hw
            simp only [A, nondecSet, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
            intro i j hij; exact hw.1 ⟨i.1, by omega⟩ ⟨j.1, by omega⟩ hij
          · intro w1 hw1 w2 hw2 h
            simp only [A, nondecSet, Finset.mem_filter, Finset.mem_univ, true_and] at hw1 hw2
            funext i
            by_cases hi : i.1 < L
            · exact congr_fun h ⟨i.1, hi⟩
            · have heq : i = ⟨L, by omega⟩ := Fin.ext (by dsimp only; have := i.2; omega)
              rw [heq, hw1.2, hw2.2]
          · intro w hw
            simp only [nondecSet, Finset.mem_filter, Finset.mem_univ, true_and] at hw
            refine ⟨fun i => if hi : i.1 < L then w ⟨i.1, hi⟩ else ⟨k + 1, by omega⟩, ?_, ?_⟩
            · simp only [A, nondecSet, Finset.mem_filter, Finset.mem_univ, true_and]
              refine ⟨fun i j hij => ?_, by simp⟩
              by_cases hj : j.1 < L
              · have hi : i.1 < L := by have : i.1 ≤ j.1 := hij; omega
                simp only [hi, hj, ↓reduceDIte]
                exact hw ⟨i.1, hi⟩ ⟨j.1, hj⟩ hij
              · simp only [hj, ↓reduceDIte]
                split_ifs with hi
                · exact Nat.le_of_lt_succ (w ⟨i.1, hi⟩).2
                · exact le_refl _
            · funext i; simp [i.2]
        have hB : B.card = (nondecSet (L + 1) (k + 1)).card := by
          refine Finset.card_bij (fun w hw i => ⟨(w i).1, by
              simp only [B, nondecSet, Finset.mem_filter, Finset.mem_univ, true_and] at hw
              have hle : (w i).1 ≤ (w ⟨L, by omega⟩).1 := hw.1 i ⟨L, by omega⟩ (Fin.le_def.mpr (by dsimp only; have := i.2; omega))
              have hlt : (w ⟨L, by omega⟩).1 < k + 2 := (w ⟨L, by omega⟩).2
              have hne : (w ⟨L, by omega⟩).1 ≠ k + 1 := fun e => hw.2 (Fin.ext e)
              omega⟩) ?_ ?_ ?_
          · intro w hw
            simp only [B, nondecSet, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
            intro i j hij; exact hw.1 i j hij
          · intro w1 _ w2 _ h
            funext i; exact Fin.ext (Fin.mk.inj (congr_fun h i))
          · intro w hw
            simp only [nondecSet, Finset.mem_filter, Finset.mem_univ, true_and] at hw
            refine ⟨fun i => ⟨(w i).1, by have := (w i).2; omega⟩, ?_, by funext i; exact Fin.ext rfl⟩
            simp only [B, nondecSet, Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨fun i j hij => hw i j hij, fun h => ?_⟩
            have hv := congr_arg Fin.val h; dsimp only at hv
            have := (w ⟨L, by omega⟩).2; omega
        have h1 := ih L (k + 2) (by omega) (by omega)
        have h2 := ih (L + 1) (k + 1) (by omega) (by omega)
        have htot : (nondecSet (L + 1) (k + 2)).card = A.card + B.card := hpart.symm
        rw [htot, hA, hB, h1, h2]
        have e1 : L + (k + 2) - 1 = L + k + 1 := by omega
        have e2 : L + 1 + (k + 1) - 1 = L + k + 1 := by omega
        have e3 : L + 1 + (k + 2) - 1 = L + k + 2 := by omega
        have e4 : k + 2 - 1 = k + 1 := by omega
        have e5 : k + 1 - 1 = k := by omega
        rw [e1, e2, e3, e4, e5, add_comm, ← Nat.choose_succ_succ]

-- Step 4: Binomial convolution identity sum_{p < n} C(p+a, a) * C(n-1-p+b, b) = C(n+a+b, a+b+1)
private lemma sum_choose_mul_choose (a : ℕ) : ∀ (b n : ℕ),
    ∑ p ∈ Finset.range n, Nat.choose (p + a) a * Nat.choose (n - 1 - p + b) b =
      Nat.choose (n + a + b) (a + b + 1) := by
  intro b
  induction b with
  | zero =>
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      simp only [Nat.choose_zero_right, mul_one, add_zero] at ih ⊢
      rw [ih, add_comm (Nat.choose (n + a) (a + 1)), show n + 1 + a = (n + a) + 1 by omega,
        Nat.choose_succ_succ]
  | succ b ihb =>
    intro n
    induction n with
    | zero => simp
    | succ n ihn =>
      rw [Finset.sum_range_succ]
      have hlast : Nat.choose (n + a) a * Nat.choose (n + 1 - 1 - n + (b + 1)) (b + 1) =
          Nat.choose (n + a) a * Nat.choose (n - n + b) b := by simp
      have hsplit : ∀ p ∈ Finset.range n,
          Nat.choose (p + a) a * Nat.choose (n + 1 - 1 - p + (b + 1)) (b + 1) =
          Nat.choose (p + a) a * Nat.choose (n - 1 - p + (b + 1)) (b + 1) +
          Nat.choose (p + a) a * Nat.choose (n - p + b) b := by
        intro p hp
        have hpn : p < n := Finset.mem_range.mp hp
        have h1 : n + 1 - 1 - p + (b + 1) = (n - 1 - p + (b + 1)) + 1 := by omega
        have h2 : n - 1 - p + (b + 1) = n - p + b := by omega
        rw [h1, Nat.choose_succ_succ, h2]; ring
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ihn, add_assoc]
      have hcomb : ∑ p ∈ Finset.range n, Nat.choose (p + a) a * Nat.choose (n - p + b) b +
          Nat.choose (n + a) a * Nat.choose (n + 1 - 1 - n + (b + 1)) (b + 1) =
          ∑ p ∈ Finset.range (n + 1), Nat.choose (p + a) a * Nat.choose (n + 1 - 1 - p + b) b := by
        rw [Finset.sum_range_succ, hlast]; rfl
      rw [hcomb, ihb (n + 1)]
      have e1 : n + 1 + a + (b + 1) = (n + a + (b + 1)) + 1 := by omega
      have e2 : n + 1 + a + b = n + a + (b + 1) := by omega
      have e3 : a + (b + 1) + 1 = (a + b + 1) + 1 := by omega
      rw [e1, e2, e3, Nat.choose_succ_succ, add_comm]

-- Step 5: Exact count of Uset n for n >= 1 via (maxVal, firstPeak) partition
private lemma isUnimodal_ofFn_iff {n : ℕ} (w : Fin n → Fin 4) :
    IsUnimodal (List.ofFn w) ↔
      ∃ p : Fin (n + 1),
        (∀ i j : Fin n, i ≤ j → j.1 ≤ p.1 → w i ≤ w j) ∧
        (∀ i j : Fin n, p.1 ≤ i.1 → i ≤ j → w j ≤ w i) := by
  unfold IsUnimodal
  constructor
  · rintro ⟨p, h1, h2⟩
    refine ⟨⟨p.1, by simpa using p.2⟩, fun i j hij hjp => ?_, fun i j hpi hij => ?_⟩
    · have := h1 ⟨i.1, by simp⟩ ⟨j.1, by simp⟩ hij hjp
      simpa using this
    · have := h2 ⟨i.1, by simp⟩ ⟨j.1, by simp⟩ hpi hij
      simpa using this
  · rintro ⟨p, h1, h2⟩
    refine ⟨⟨p.1, by simp only [List.length_ofFn]; exact p.2⟩, fun i j hij hjp => ?_, fun i j hpi hij => ?_⟩
    · have := h1 ⟨i.1, by simpa using i.2⟩ ⟨j.1, by simpa using j.2⟩ hij hjp
      simpa using this
    · have := h2 ⟨i.1, by simpa using i.2⟩ ⟨j.1, by simpa using j.2⟩ hpi hij
      simpa using this

private lemma card_Uset (n : ℕ) (hn : 1 ≤ n) :
    (Uset n).card = 1 + Nat.choose (n + 1) 2 + Nat.choose (n + 3) 4 + Nat.choose (n + 5) 6 := by
  -- Partition Uset n into zero-word (m=0) and (m ∈ {1,2,3}, first peak p : Fin n)
  let U0 := (Uset n).filter (fun w => ∀ i : Fin n, w i = 0)
  let Up (m : Fin 3) (p : Fin n) := (Uset n).filter (fun w =>
    (∀ i : Fin n, w i ≤ ⟨m.1 + 1, by omega⟩) ∧
    w p = ⟨m.1 + 1, by omega⟩ ∧
    (∀ i : Fin n, i.1 < p.1 → w i < ⟨m.1 + 1, by omega⟩))
  have hunion : Uset n = U0 ∪ (Finset.univ : Finset (Fin 3 × Fin n)).biUnion (fun mp => Up mp.1 mp.2) := by
    ext w; simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and, U0, Up, Finset.mem_filter]
    constructor
    · intro hw
      by_cases hz : ∀ i : Fin n, w i = 0
      · left; exact ⟨hw, hz⟩
      · right
        let img := Finset.univ.image w
        have hne : img.Nonempty := ⟨w ⟨0, by omega⟩, Finset.mem_image_of_mem w (Finset.mem_univ _)⟩
        let mv := img.max' hne
        have hmv_mem : mv ∈ img := Finset.max'_mem img hne
        have hmv_le : ∀ i : Fin n, w i ≤ mv := fun i => Finset.le_max' img _ (Finset.mem_image_of_mem w (Finset.mem_univ i))
        have hmv_pos : 0 < mv.1 := by
          by_contra h0; apply hz; intro i
          have := hmv_le i; exact Fin.ext (by omega)
        let idx := Finset.univ.filter (fun i : Fin n => w i = mv)
        have hidx_ne : idx.Nonempty := by
          rcases Finset.mem_image.mp hmv_mem with ⟨i0, _, hi0⟩
          exact ⟨i0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi0⟩⟩
        let p := idx.min' hidx_ne
        have hp_mem : p ∈ idx := Finset.min'_mem idx hidx_ne
        have hp_eq : w p = mv := (Finset.mem_filter.mp hp_mem).2
        refine ⟨(⟨mv.1 - 1, by have := mv.2; omega⟩, p), hw, ?_, ?_, ?_⟩
        · intro i; have := hmv_le i; change (w i).1 ≤ mv.1 - 1 + 1; omega
        · exact hp_eq.trans (Fin.ext (by dsimp only; omega))
        · intro i hip
          dsimp only at hip
          have hle := hmv_le i
          have hne' : w i ≠ mv := by
            intro hwi
            have hle_p : p ≤ i := Finset.min'_le idx i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwi⟩)
            have : p.1 ≤ i.1 := hle_p
            omega
          exact Fin.lt_def.mpr (by dsimp only; have : (w i).1 ≠ mv.1 := fun e => hne' (Fin.ext e); omega)
    · rintro (⟨hw, _⟩ | ⟨_, hw, _, _, _⟩) <;> exact hw
  have hdisj0 : Disjoint U0 ((Finset.univ : Finset (Fin 3 × Fin n)).biUnion (fun mp => Up mp.1 mp.2)) := by
    rw [Finset.disjoint_left]; intro w h0 h1
    simp only [U0, Up, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter] at h0 h1
    rcases h1 with ⟨⟨m, p⟩, _, _, hp, _⟩
    have := h0.2 p; rw [this] at hp; have := congr_arg Fin.val hp; dsimp only at this; omega
  have hdisj_p : Set.PairwiseDisjoint ((Finset.univ : Finset (Fin 3 × Fin n)) : Set (Fin 3 × Fin n)) (fun mp : Fin 3 × Fin n => Up mp.1 mp.2) := by
    rintro ⟨m1, p1⟩ _ ⟨m2, p2⟩ _ hne
    change Disjoint (Up m1 p1) (Up m2 p2)
    rw [Finset.disjoint_left]; intro w h1 h2
    simp only [Up, Finset.mem_filter] at h1 h2
    have hm : m1 = m2 := by
      have a := h1.2.1 p2; rw [h2.2.2.1] at a
      have b := h2.2.1 p1; rw [h1.2.2.1] at b
      exact Fin.ext (by have : m2.1 + 1 ≤ m1.1 + 1 := a; have : m1.1 + 1 ≤ m2.1 + 1 := b; omega)
    subst hm
    have hp : p1 = p2 := by
      rcases lt_trichotomy p1.1 p2.1 with hlt | heq | hgt
      · have := h2.2.2.2 p1 hlt; rw [h1.2.2.1] at this; exact absurd this (lt_irrefl _)
      · exact Fin.ext heq
      · have := h1.2.2.2 p2 hgt; rw [h2.2.2.1] at this; exact absurd this (lt_irrefl _)
    exact hne (by rw [hp])
  have c0 : U0.card = 1 := by
    have heq : U0 = {fun _ => 0} := by
      ext w; simp only [U0, Uset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h; funext i; exact h.2 i
      · rintro rfl; refine ⟨?_, fun _ => rfl⟩
        rw [isUnimodal_ofFn_iff]; exact ⟨⟨0, by omega⟩, fun _ _ _ _ => le_refl _, fun _ _ _ _ => le_refl _⟩
    rw [heq]; simp
  have cUp : ∀ (m : Fin 3) (p : Fin n),
      (Up m p).card = Nat.choose (p.1 + m.1) m.1 * Nat.choose (n - 1 - p.1 + (m.1 + 1)) (m.1 + 1) := by
    intro m p
    have hnd1 := card_nondecSet (p.1 + (m.1 + 1)) p.1 (m.1 + 1) rfl (by omega)
    have hnd2 := card_nondecSet ((n - 1 - p.1) + (m.1 + 2)) (n - 1 - p.1) (m.1 + 2) rfl (by omega)
    have e1 : p.1 + (m.1 + 1) - 1 = p.1 + m.1 := by omega
    have e2 : m.1 + 1 - 1 = m.1 := by omega
    have e3 : n - 1 - p.1 + (m.1 + 2) - 1 = n - 1 - p.1 + (m.1 + 1) := by omega
    have e4 : m.1 + 2 - 1 = m.1 + 1 := by omega
    rw [e1, e2] at hnd1; rw [e3, e4] at hnd2
    rw [← hnd1, ← hnd2, ← Finset.card_product]
    refine Finset.card_bij
      (fun w hw =>
        (fun i : Fin p.1 => ⟨(w ⟨i.1, by omega⟩).1, by
            simp only [Up, Finset.mem_filter] at hw
            exact hw.2.2.2 ⟨i.1, by omega⟩ i.2⟩,
         fun j : Fin (n - 1 - p.1) => ⟨(w ⟨n - 1 - j.1, by omega⟩).1, by
            simp only [Up, Finset.mem_filter] at hw
            have := hw.2.1 ⟨n - 1 - j.1, by omega⟩; exact Nat.lt_succ_of_le this⟩)) ?_ ?_ ?_
    · intro w hw
      simp only [Up, Uset, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      rw [isUnimodal_ofFn_iff] at hw
      rcases hw.1 with ⟨pk, hinc, hdec⟩
      -- Note: w is nondecreasing on [0..p] and nonincreasing on [p..n-1]!
      have hinc_p : ∀ i j : Fin n, i ≤ j → j.1 ≤ p.1 → w i ≤ w j := by
        intro i j hij hjp
        by_cases hpk : j.1 ≤ pk.1
        · exact hinc i j hij hpk
        · -- pk < j <= p: then w j >= w p = m + 1, so j = p (since i < p => w i < m + 1), impossible unless i < p and...
          have h1 : w p ≤ w j := hdec j p (by omega) (by exact hjp)
          rw [hw.2.2.1] at h1
          have h2 := hw.2.1 j
          have hjeq : w j = ⟨m.1 + 1, by omega⟩ := le_antisymm h2 h1
          rw [hjeq]; exact hw.2.1 i
      have hdec_p : ∀ i j : Fin n, p.1 ≤ i.1 → i ≤ j → w j ≤ w i := by
        intro i j hpi hij
        by_cases hpk : pk.1 ≤ i.1
        · exact hdec i j hpk hij
        · -- i < pk: then p <= i < pk, so w p <= w i <= m+1 => w i = m+1 => w j <= m+1 = w i!
          have h1 : w p ≤ w i := hinc p i hpi (by omega)
          rw [hw.2.2.1] at h1
          have h2 := hw.2.1 i
          have hieq : w i = ⟨m.1 + 1, by omega⟩ := le_antisymm h2 h1
          rw [hieq]; exact hw.2.1 j
      refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · simp only [nondecSet, Finset.mem_filter, Finset.mem_univ, true_and]
        intro i j hij; exact hinc_p ⟨i.1, by omega⟩ ⟨j.1, by omega⟩ hij (by dsimp only; have := j.2; omega)
      · simp only [nondecSet, Finset.mem_filter, Finset.mem_univ, true_and]
        intro i j hij
        exact hdec_p ⟨n - 1 - j.1, by omega⟩ ⟨n - 1 - i.1, by omega⟩ (by dsimp only; have := j.2; omega)
          (Fin.le_def.mpr (by dsimp only; have : i.1 ≤ j.1 := hij; have := j.2; omega))
    · intro w1 hw1 w2 hw2 h
      simp only [Up, Finset.mem_filter] at hw1 hw2
      simp only [Prod.mk.injEq] at h
      funext i
      rcases lt_trichotomy i.1 p.1 with hlt | heq | hgt
      · have hi := congr_arg Fin.val (congr_fun h.1 ⟨i.1, hlt⟩)
        exact Fin.ext hi
      · have hp : i = p := Fin.ext heq
        rw [hp, hw1.2.2.1, hw2.2.2.1]
      · have hj := congr_arg Fin.val (congr_fun h.2 ⟨n - 1 - i.1, by have := i.2; omega⟩)
        dsimp only at hj
        have hidx : (⟨n - 1 - (n - 1 - i.1), by omega⟩ : Fin n) = i := Fin.ext (by dsimp only; have := i.2; omega)
        rw [hidx] at hj; exact Fin.ext hj
    · intro ⟨u, v⟩ huv
      simp only [Finset.mem_product, nondecSet, Finset.mem_filter, Finset.mem_univ, true_and] at huv
      let w : Fin n → Fin 4 := fun i =>
        if hlt : i.1 < p.1 then ⟨(u ⟨i.1, hlt⟩).1, by have := (u ⟨i.1, hlt⟩).2; omega⟩
        else if heq : i.1 = p.1 then ⟨m.1 + 1, by omega⟩
        else ⟨(v ⟨n - 1 - i.1, by have := i.2; omega⟩).1, by have := (v ⟨n - 1 - i.1, by have := i.2; omega⟩).2; omega⟩
      refine ⟨w, ?_, ?_⟩
      · simp only [Up, Uset, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [isUnimodal_ofFn_iff]
          refine ⟨⟨p.1, by omega⟩, fun i j hij hjp => ?_, fun i j hpi hij => ?_⟩
          · dsimp only at hjp
            by_cases hjp' : j.1 < p.1
            · have hip' : i.1 < p.1 := by have : i.1 ≤ j.1 := hij; omega
              simp only [w, hip', hjp', ↓reduceDIte]
              exact huv.1 ⟨i.1, hip'⟩ ⟨j.1, hjp'⟩ hij
            · have hjeq : j.1 = p.1 := by omega
              simp only [w, hjeq, lt_irrefl, ↓reduceDIte]
              split_ifs with hip' hieq
              · have := (u ⟨i.1, hip'⟩).2; change (u ⟨i.1, hip'⟩).1 ≤ m.1 + 1; omega
              · exact le_refl _
              · have : i.1 ≤ j.1 := hij; omega
          · dsimp only at hpi
            by_cases hip' : i.1 = p.1
            · simp only [w, hip', lt_irrefl, ↓reduceDIte]
              split_ifs with hjp' hjeq
              · omega
              · exact le_refl _
              · have := (v ⟨n - 1 - j.1, by have := j.2; omega⟩).2
                change (v ⟨n - 1 - j.1, by have := j.2; omega⟩).1 ≤ m.1 + 1; omega
            · have hi_gt : p.1 < i.1 := by omega
              have hj_gt : p.1 < j.1 := by have : i.1 ≤ j.1 := hij; omega
              simp only [w, show ¬ (i.1 < p.1) by omega, show ¬ (i.1 = p.1) by omega,
                show ¬ (j.1 < p.1) by omega, show ¬ (j.1 = p.1) by omega, ↓reduceDIte]
              exact huv.2 ⟨n - 1 - j.1, by have := j.2; omega⟩ ⟨n - 1 - i.1, by have := i.2; omega⟩
                (Fin.le_def.mpr (by dsimp only; have : i.1 ≤ j.1 := hij; have := j.2; omega))
        · intro i; dsimp only [w]
          split_ifs with hlt heq
          · have := (u ⟨i.1, hlt⟩).2; change (u ⟨i.1, hlt⟩).1 ≤ m.1 + 1; omega
          · exact le_refl _
          · have := (v ⟨n - 1 - i.1, by have := i.2; omega⟩).2
            change (v ⟨n - 1 - i.1, by have := i.2; omega⟩).1 ≤ m.1 + 1; omega
        · simp [w]
        · intro i hip; simp only [w, hip, ↓reduceDIte]
          exact Fin.lt_def.mpr (by dsimp only; exact (u ⟨i.1, hip⟩).2)
      · ext i
        · simp only [w, show (⟨i.1, by omega⟩ : Fin n).1 < p.1 from i.2, ↓reduceDIte]
        · simp only [w, show ¬ (n - 1 - i.1 < p.1) by have := i.2; omega,
            show ¬ (n - 1 - i.1 = p.1) by have := i.2; omega, ↓reduceDIte]
          have hidx : (⟨n - 1 - (n - 1 - i.1), by omega⟩ : Fin (n - 1 - p.1)) = i :=
            Fin.ext (by dsimp only; have := i.2; omega)
          rw [hidx]
  rw [hunion, Finset.card_union_of_disjoint hdisj0, Finset.card_biUnion hdisj_p, c0]
  rw [Fintype.sum_prod_type]
  have hsum_m : ∀ m : Fin 3,
      ∑ p : Fin n, (Up m p).card = Nat.choose (n + 2 * m.1 + 1) (2 * m.1 + 2) := by
    intro m
    calc ∑ p : Fin n, (Up m p).card
        = ∑ p : Fin n, Nat.choose (p.1 + m.1) m.1 * Nat.choose (n - 1 - p.1 + (m.1 + 1)) (m.1 + 1) :=
          Finset.sum_congr rfl fun p _ => cUp m p
      _ = ∑ p ∈ Finset.range n, Nat.choose (p + m.1) m.1 * Nat.choose (n - 1 - p + (m.1 + 1)) (m.1 + 1) :=
          Fin.sum_univ_eq_sum_range (fun q => Nat.choose (q + m.1) m.1 * Nat.choose (n - 1 - q + (m.1 + 1)) (m.1 + 1)) n
      _ = Nat.choose (n + m.1 + (m.1 + 1)) (m.1 + (m.1 + 1) + 1) := sum_choose_mul_choose m.1 (m.1 + 1) n
      _ = Nat.choose (n + 2 * m.1 + 1) (2 * m.1 + 2) := by congr 1 <;> omega
  simp only [Fin.sum_univ_three, hsum_m, Fin.val_zero, Fin.val_one, Fin.val_two]
  ring_nf

-- Step 6: Polynomial closed form for U(n) and a(n) in ℚ
private lemma choose_two_rat (m : ℕ) : (Nat.choose m 2 : ℚ) = (m : ℚ) * ((m : ℚ) - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]; push_cast; rw [ih]; ring

private lemma choose_three_rat (m : ℕ) :
    (Nat.choose m 3 : ℚ) = (m : ℚ) * ((m : ℚ) - 1) * ((m : ℚ) - 2) / 6 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ]; push_cast; rw [ih, choose_two_rat]; ring

private lemma choose_four_rat (m : ℕ) :
    (Nat.choose m 4 : ℚ) = (m : ℚ) * ((m : ℚ) - 1) * ((m : ℚ) - 2) * ((m : ℚ) - 3) / 24 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ]; push_cast; rw [ih, choose_three_rat]; ring

private lemma choose_five_rat (m : ℕ) :
    (Nat.choose m 5 : ℚ) = (m : ℚ) * ((m : ℚ) - 1) * ((m : ℚ) - 2) * ((m : ℚ) - 3) * ((m : ℚ) - 4) / 120 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ]; push_cast; rw [ih, choose_four_rat]; ring

private lemma choose_six_rat (m : ℕ) :
    (Nat.choose m 6 : ℚ) =
      (m : ℚ) * ((m : ℚ) - 1) * ((m : ℚ) - 2) * ((m : ℚ) - 3) * ((m : ℚ) - 4) * ((m : ℚ) - 5) / 720 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ]; push_cast; rw [ih, choose_five_rat]; ring

private def UPoly (x : ℚ) : ℚ :=
  (x ^ 6 + 15 * x ^ 5 + 115 * x ^ 4 + 405 * x ^ 3 + 964 * x ^ 2 + 660 * x + 720) / 720

private lemma a_rat_eq_poly (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = (UPoly (n : ℚ)) ^ 2 := by
  rw [a_eq_U_sq n, card_Uset n hn]
  push_cast
  rw [choose_two_rat, choose_four_rat, choose_six_rat]
  push_cast
  unfold UPoly
  ring

private lemma a_rec_rat (n : ℕ) (hn : 13 < n) :
    (a n : ℚ) =
      13 * (a (n - 1) : ℚ) - 78 * (a (n - 2) : ℚ) + 286 * (a (n - 3) : ℚ) -
      715 * (a (n - 4) : ℚ) + 1287 * (a (n - 5) : ℚ) - 1716 * (a (n - 6) : ℚ) +
      1716 * (a (n - 7) : ℚ) - 1287 * (a (n - 8) : ℚ) + 715 * (a (n - 9) : ℚ) -
      286 * (a (n - 10) : ℚ) + 78 * (a (n - 11) : ℚ) - 13 * (a (n - 12) : ℚ) +
      (a (n - 13) : ℚ) := by
  have h0 := a_rat_eq_poly n (by omega)
  have h1 := a_rat_eq_poly (n - 1) (by omega)
  have h2 := a_rat_eq_poly (n - 2) (by omega)
  have h3 := a_rat_eq_poly (n - 3) (by omega)
  have h4 := a_rat_eq_poly (n - 4) (by omega)
  have h5 := a_rat_eq_poly (n - 5) (by omega)
  have h6 := a_rat_eq_poly (n - 6) (by omega)
  have h7 := a_rat_eq_poly (n - 7) (by omega)
  have h8 := a_rat_eq_poly (n - 8) (by omega)
  have h9 := a_rat_eq_poly (n - 9) (by omega)
  have h10 := a_rat_eq_poly (n - 10) (by omega)
  have h11 := a_rat_eq_poly (n - 11) (by omega)
  have h12 := a_rat_eq_poly (n - 12) (by omega)
  have h13 := a_rat_eq_poly (n - 13) (by omega)
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  have c1 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by exact_mod_cast (by omega : (n - 1 : ℕ) = (n : ℤ) - 1)
  have c2 : ((n - 2 : ℕ) : ℚ) = (n : ℚ) - 2 := by exact_mod_cast (by omega : (n - 2 : ℕ) = (n : ℤ) - 2)
  have c3 : ((n - 3 : ℕ) : ℚ) = (n : ℚ) - 3 := by exact_mod_cast (by omega : (n - 3 : ℕ) = (n : ℤ) - 3)
  have c4 : ((n - 4 : ℕ) : ℚ) = (n : ℚ) - 4 := by exact_mod_cast (by omega : (n - 4 : ℕ) = (n : ℤ) - 4)
  have c5 : ((n - 5 : ℕ) : ℚ) = (n : ℚ) - 5 := by exact_mod_cast (by omega : (n - 5 : ℕ) = (n : ℤ) - 5)
  have c6 : ((n - 6 : ℕ) : ℚ) = (n : ℚ) - 6 := by exact_mod_cast (by omega : (n - 6 : ℕ) = (n : ℤ) - 6)
  have c7 : ((n - 7 : ℕ) : ℚ) = (n : ℚ) - 7 := by exact_mod_cast (by omega : (n - 7 : ℕ) = (n : ℤ) - 7)
  have c8 : ((n - 8 : ℕ) : ℚ) = (n : ℚ) - 8 := by exact_mod_cast (by omega : (n - 8 : ℕ) = (n : ℤ) - 8)
  have c9 : ((n - 9 : ℕ) : ℚ) = (n : ℚ) - 9 := by exact_mod_cast (by omega : (n - 9 : ℕ) = (n : ℤ) - 9)
  have c10 : ((n - 10 : ℕ) : ℚ) = (n : ℚ) - 10 := by exact_mod_cast (by omega : (n - 10 : ℕ) = (n : ℤ) - 10)
  have c11 : ((n - 11 : ℕ) : ℚ) = (n : ℚ) - 11 := by exact_mod_cast (by omega : (n - 11 : ℕ) = (n : ℤ) - 11)
  have c12 : ((n - 12 : ℕ) : ℚ) = (n : ℚ) - 12 := by exact_mod_cast (by omega : (n - 12 : ℕ) = (n : ℤ) - 12)
  have c13 : ((n - 13 : ℕ) : ℚ) = (n : ℚ) - 13 := by exact_mod_cast (by omega : (n - 13 : ℕ) = (n : ℤ) - 13)
  rw [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13]
  unfold UPoly
  ring

theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - PowerSeries.X) ^ 13 =
      PowerSeries.X * (16 + 48 * PowerSeries.X + 420 * PowerSeries.X ^ 2 -
        208 * PowerSeries.X ^ 3 + 1140 * PowerSeries.X ^ 4 - 1260 * PowerSeries.X ^ 5 +
        1401 * PowerSeries.X ^ 6 - 1044 * PowerSeries.X ^ 7 + 597 * PowerSeries.X ^ 8 -
        244 * PowerSeries.X ^ 9 + 69 * PowerSeries.X ^ 10 - 12 * PowerSeries.X ^ 11 +
        PowerSeries.X ^ 12) ∧
    ∀ n : ℕ, 13 < n →
      (a n : ℤ) = 13 * (a (n - 1) : ℤ) - 78 * (a (n - 2) : ℤ) + 286 * (a (n - 3) : ℤ) -
        715 * (a (n - 4) : ℤ) + 1287 * (a (n - 5) : ℤ) - 1716 * (a (n - 6) : ℤ) +
        1716 * (a (n - 7) : ℤ) - 1287 * (a (n - 8) : ℤ) + 715 * (a (n - 9) : ℤ) -
        286 * (a (n - 10) : ℤ) + 78 * (a (n - 11) : ℤ) - 13 * (a (n - 12) : ℤ) +
        (a (n - 13) : ℤ) := by
  have hrec_int : ∀ n : ℕ, 13 < n →
      (a n : ℤ) = 13 * (a (n - 1) : ℤ) - 78 * (a (n - 2) : ℤ) + 286 * (a (n - 3) : ℤ) -
        715 * (a (n - 4) : ℤ) + 1287 * (a (n - 5) : ℤ) - 1716 * (a (n - 6) : ℤ) +
        1716 * (a (n - 7) : ℤ) - 1287 * (a (n - 8) : ℤ) + 715 * (a (n - 9) : ℤ) -
        286 * (a (n - 10) : ℤ) + 78 * (a (n - 11) : ℤ) - 13 * (a (n - 12) : ℤ) +
        (a (n - 13) : ℤ) := by
    intro n hn; exact_mod_cast a_rec_rat n hn
  refine ⟨?_, hrec_int⟩
  let f : PowerSeries ℚ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
  have hlhs : f * (1 - PowerSeries.X) ^ 13 =
      f - PowerSeries.C 13 * (PowerSeries.X ^ 1 * f) + PowerSeries.C 78 * (PowerSeries.X ^ 2 * f) -
        PowerSeries.C 286 * (PowerSeries.X ^ 3 * f) + PowerSeries.C 715 * (PowerSeries.X ^ 4 * f) -
        PowerSeries.C 1287 * (PowerSeries.X ^ 5 * f) + PowerSeries.C 1716 * (PowerSeries.X ^ 6 * f) -
        PowerSeries.C 1716 * (PowerSeries.X ^ 7 * f) + PowerSeries.C 1287 * (PowerSeries.X ^ 8 * f) -
        PowerSeries.C 715 * (PowerSeries.X ^ 9 * f) + PowerSeries.C 286 * (PowerSeries.X ^ 10 * f) -
        PowerSeries.C 78 * (PowerSeries.X ^ 11 * f) + PowerSeries.C 13 * (PowerSeries.X ^ 12 * f) -
        PowerSeries.X ^ 13 * f := by
    simp only [map_ofNat]; ring
  have hrhs : PowerSeries.X * (16 + 48 * PowerSeries.X + 420 * PowerSeries.X ^ 2 -
        208 * PowerSeries.X ^ 3 + 1140 * PowerSeries.X ^ 4 - 1260 * PowerSeries.X ^ 5 +
        1401 * PowerSeries.X ^ 6 - 1044 * PowerSeries.X ^ 7 + 597 * PowerSeries.X ^ 8 -
        244 * PowerSeries.X ^ 9 + 69 * PowerSeries.X ^ 10 - 12 * PowerSeries.X ^ 11 +
        PowerSeries.X ^ 12 : PowerSeries ℚ) =
      PowerSeries.C 16 * PowerSeries.X ^ 1 + PowerSeries.C 48 * PowerSeries.X ^ 2 +
        PowerSeries.C 420 * PowerSeries.X ^ 3 - PowerSeries.C 208 * PowerSeries.X ^ 4 +
        PowerSeries.C 1140 * PowerSeries.X ^ 5 - PowerSeries.C 1260 * PowerSeries.X ^ 6 +
        PowerSeries.C 1401 * PowerSeries.X ^ 7 - PowerSeries.C 1044 * PowerSeries.X ^ 8 +
        PowerSeries.C 597 * PowerSeries.X ^ 9 - PowerSeries.C 244 * PowerSeries.X ^ 10 +
        PowerSeries.C 69 * PowerSeries.X ^ 11 - PowerSeries.C 12 * PowerSeries.X ^ 12 +
        PowerSeries.X ^ 13 := by
    simp only [map_ofNat]; ring
  rw [hlhs, hrhs]
  have ha1 : (a 1 : ℚ) = 16 := by rw [a_rat_eq_poly 1 (by omega)]; unfold UPoly; norm_num
  have ha2 : (a 2 : ℚ) = 256 := by rw [a_rat_eq_poly 2 (by omega)]; unfold UPoly; norm_num
  have ha3 : (a 3 : ℚ) = 2500 := by rw [a_rat_eq_poly 3 (by omega)]; unfold UPoly; norm_num
  have ha4 : (a 4 : ℚ) = 16900 := by rw [a_rat_eq_poly 4 (by omega)]; unfold UPoly; norm_num
  have ha5 : (a 5 : ℚ) = 87616 := by rw [a_rat_eq_poly 5 (by omega)]; unfold UPoly; norm_num
  have ha6 : (a 6 : ℚ) = 372100 := by rw [a_rat_eq_poly 6 (by omega)]; unfold UPoly; norm_num
  have ha7 : (a 7 : ℚ) = 1352569 := by rw [a_rat_eq_poly 7 (by omega)]; unfold UPoly; norm_num
  have ha8 : (a 8 : ℚ) = 4338889 := by rw [a_rat_eq_poly 8 (by omega)]; unfold UPoly; norm_num
  have ha9 : (a 9 : ℚ) = 12559936 := by rw [a_rat_eq_poly 9 (by omega)]; unfold UPoly; norm_num
  have ha10 : (a 10 : ℚ) = 33362176 := by rw [a_rat_eq_poly 10 (by omega)]; unfold UPoly; norm_num
  have ha11 : (a 11 : ℚ) = 82373776 := by rw [a_rat_eq_poly 11 (by omega)]; unfold UPoly; norm_num
  have ha12 : (a 12 : ℚ) = 190992400 := by rw [a_rat_eq_poly 12 (by omega)]; unfold UPoly; norm_num
  have ha13 : (a 13 : ℚ) = 419266576 := by rw [a_rat_eq_poly 13 (by omega)]; unfold UPoly; norm_num
  ext k
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_X_pow, f, PowerSeries.coeff_mk]
  match k with
  | 0 => norm_num
  | 1 => norm_num [ha1]
  | 2 => norm_num [ha1, ha2]
  | 3 => norm_num [ha1, ha2, ha3]
  | 4 => norm_num [ha1, ha2, ha3, ha4]
  | 5 => norm_num [ha1, ha2, ha3, ha4, ha5]
  | 6 => norm_num [ha1, ha2, ha3, ha4, ha5, ha6]
  | 7 => norm_num [ha1, ha2, ha3, ha4, ha5, ha6, ha7]
  | 8 => norm_num [ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8]
  | 9 => norm_num [ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9]
  | 10 => norm_num [ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10]
  | 11 => norm_num [ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11]
  | 12 => norm_num [ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12]
  | 13 => norm_num [ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13]
  | m + 14 =>
    have hr := a_rec_rat (m + 14) (by omega)
    simp only [show m + 14 ≠ 0 by omega, show m + 14 ≠ 1 by omega, show m + 14 ≠ 2 by omega,
      show m + 14 ≠ 3 by omega, show m + 14 ≠ 4 by omega, show m + 14 ≠ 5 by omega,
      show m + 14 ≠ 6 by omega, show m + 14 ≠ 7 by omega, show m + 14 ≠ 8 by omega,
      show m + 14 ≠ 9 by omega, show m + 14 ≠ 10 by omega, show m + 14 ≠ 11 by omega,
      show m + 14 ≠ 12 by omega, show m + 14 ≠ 13 by omega,
      show 1 ≤ m + 14 by omega, show 2 ≤ m + 14 by omega, show 3 ≤ m + 14 by omega,
      show 4 ≤ m + 14 by omega, show 5 ≤ m + 14 by omega, show 6 ≤ m + 14 by omega,
      show 7 ≤ m + 14 by omega, show 8 ≤ m + 14 by omega, show 9 ≤ m + 14 by omega,
      show 10 ≤ m + 14 by omega, show 11 ≤ m + 14 by omega, show 12 ≤ m + 14 by omega,
      show 13 ≤ m + 14 by omega,
      show m + 14 - 1 ≠ 0 by omega, show m + 14 - 2 ≠ 0 by omega, show m + 14 - 3 ≠ 0 by omega,
      show m + 14 - 4 ≠ 0 by omega, show m + 14 - 5 ≠ 0 by omega, show m + 14 - 6 ≠ 0 by omega,
      show m + 14 - 7 ≠ 0 by omega, show m + 14 - 8 ≠ 0 by omega, show m + 14 - 9 ≠ 0 by omega,
      show m + 14 - 10 ≠ 0 by omega, show m + 14 - 11 ≠ 0 by omega, show m + 14 - 12 ≠ 0 by omega,
      show m + 14 - 13 ≠ 0 by omega,
      ↓reduceIte, mul_zero, sub_zero, add_zero]
    linarith

end
end ProofA223756

theorem OMA.solution : type_of% @OMA.S_oeis_a223756.main :=
  ProofA223756.main

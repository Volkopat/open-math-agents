import OMAStatements.S_oeis_a212732

/-!
OEIS A212732 (R. H. Hardin, May 25 2012): Number of 0..2 arrays of length 2*n+2 with sum less than 2*n in any length 2n subsequence (=less than 50% duty cycle).
From Vaclav Kotesovec, Jul 31 2013: Empirical: n*(2*n-1)*(59040*n^4 - 630664*n^3 + 2419338*n^2 - 3925427*n + 2259783)*a(n) = (2243520*n^6 - 26740112*n^5 + 122386084*n^4 - 271040464*n^3 + 300314759*n^2 - 153351297*n + 26751060)*a(n-1) + 81*(n-3)*(2*n-7)*(59040*n^4 - 394504*n^3 + 881586*n^2 - 742583*n + 182070)*a(n-3) - 9*(1298880*n^6 - 16413328*n^5 + 81293588*n^4 - 199839104*n^3 + 252840847*n^2 - 150974403*n + 30574530)*a(n-2) Conjecture: a(n) ~ 9/2*9^n.

Proof. Every window of 2n entries contains the middle part (positions k to 2n - 1), so the array
splits into k outer pairs (x t, x (2n + t)) and the middle part (`po`, `pm`, `glue`, `window`), and
a(n) = sum_m tri(2n - k, m) F(2n - 1 - m) (`a_gen`), where tri counts the 0..2 arrays by their sum
and F(c) counts the outer pairs whose window parts are at most c (computed by the recursion `F2`).
With the symmetry of tri, a(n) = 3^k 9^n / 2 + ts(2n - k) (`a_split`, `rep`), ts a fixed combination
of the central coefficients T_j(L) = tri(L, L + j). These reduce to T_0, T_1 by (L + j + 1) T_(j+1)
= -j T_j + (L - j + 1) T_(j-1) (`tri_rec`, `T_up`), and (T_0, T_1) moves up one level by (T_0 + 2
T_1, (L + 1)(2 T_0 + T_1)/(L + 2)) (`sh1`); the recurrence is then an identity of rational functions
(`key`). The central coefficients satisfy (L + 2) p(L + 2)^3 <= ... with p(L) = T_0(L)/3^L
non-increasing and (L + 2) p(L)^3 <= 2, so p -> 0 (`P_tendsto`), which gives the asymptotic
(`asymp`).
-/

namespace OMA.S_oeis_a212732

open Finset Filter Topology


/-- The number of 0..2 arrays of length L with sum m (0 for m < 0). -/
def tri : ℕ → ℤ → ℕ
  | 0, m => if m = 0 then 1 else 0
  | L + 1, m => tri L m + tri L (m - 1) + tri L (m - 2)

lemma tri_zero (m : ℤ) : tri 0 m = if m = 0 then 1 else 0 := rfl

lemma tri_succ (L : ℕ) (m : ℤ) : tri (L + 1) m = tri L m + tri L (m - 1) + tri L (m - 2) := rfl

lemma tri_neg (L : ℕ) (m : ℤ) (h : m < 0) : tri L m = 0 := by
  induction L generalizing m with
  | zero => rw [tri_zero, if_neg (by omega)]
  | succ L ih => rw [tri_succ, ih m h, ih (m - 1) (by omega), ih (m - 2) (by omega)]

lemma tri_big (L : ℕ) (m : ℤ) (h : 2 * (L : ℤ) < m) : tri L m = 0 := by
  induction L generalizing m with
  | zero => rw [tri_zero, if_neg (by omega)]
  | succ L ih =>
    push_cast at h
    rw [tri_succ, ih m (by omega), ih (m - 1) (by omega), ih (m - 2) (by omega)]

lemma tri_symm (L : ℕ) (m m' : ℤ) (h : m + m' = 2 * L) : tri L m = tri L m' := by
  induction L generalizing m m' with
  | zero =>
    rw [tri_zero, tri_zero]
    push_cast at h
    split_ifs <;> omega
  | succ L ih =>
    push_cast at h
    rw [tri_succ, tri_succ, ih m (m' - 2) (by omega), ih (m - 1) (m' - 1) (by omega),
      ih (m - 2) m' (by omega)]
    ring

/-- The coefficients of (1 + x + x^2)^L satisfy
(m + 1) c(m + 1) = (L - m) c(m) + (2L - m + 1) c(m - 1). -/
lemma tri_rec (L : ℕ) (m : ℤ) :
    (m + 1) * (tri L (m + 1) : ℤ) = ((L : ℤ) - m) * tri L m + (2 * L - m + 1) * tri L (m - 1) := by
  induction L generalizing m with
  | zero =>
    simp only [tri_zero]
    by_cases h1 : m + 1 = 0
    · have : m = -1 := by omega
      subst this
      norm_num
    · by_cases h2 : m = 0
      · subst h2
        norm_num
      · by_cases h3 : m - 1 = 0
        · have : m = 1 := by omega
          subst this
          norm_num
        · rw [if_neg h1, if_neg h2, if_neg h3]
          simp
  | succ L ih =>
    have e1 := ih m
    have e2 := ih (m - 1)
    have e3 := ih (m - 2)
    rw [show m - 1 + 1 = m by ring, show m - 1 - 1 = m - 2 by ring] at e2
    rw [show m - 2 + 1 = m - 1 by ring, show m - 2 - 1 = m - 3 by ring] at e3
    rw [tri_succ, tri_succ, tri_succ]
    rw [show m + 1 - 1 = m by ring, show m + 1 - 2 = m - 1 by ring, show m - 1 - 1 = m - 2 by ring,
      show m - 1 - 2 = m - 3 by ring]
    push_cast
    linear_combination e1 + e2 + e3

/-- tri L m counts the 0..2 arrays of length L with sum m. -/
lemma card_sum (L : ℕ) (m : ℤ) :
    ((univ : Finset (Fin L → Fin 3)).filter
      (fun y => ((∑ i, (y i : ℕ) : ℕ) : ℤ) = m)).card = tri L m := by
  induction L generalizing m with
  | zero =>
    rw [tri_zero]
    split_ifs with h
    · subst h
      rw [filter_true_of_mem (fun y _ => by simp)]
      rfl
    · rw [card_eq_zero, filter_eq_empty_iff]
      intro y _ hy
      simp only [univ_eq_empty, sum_empty, CharP.cast_eq_zero] at hy
      exact h hy.symm
  | succ L ih =>
    have hf : ∀ v : Fin 3, (((univ : Finset (Fin (L + 1) → Fin 3)).filter
        (fun y => ((∑ i, (y i : ℕ) : ℕ) : ℤ) = m)).filter (fun y => y 0 = v)).card =
        ((univ : Finset (Fin L → Fin 3)).filter
          (fun y => ((∑ i, (y i : ℕ) : ℕ) : ℤ) = m - (v : ℕ))).card := by
      intro v
      refine card_bij' (fun y _ => Fin.tail y) (fun y _ => Fin.cons v y) ?_ ?_ ?_ ?_
      · intro y hy
        simp only [mem_filter, mem_univ, true_and] at hy ⊢
        obtain ⟨h1, h2⟩ := hy
        rw [Fin.sum_univ_succ, h2] at h1
        simp only [Fin.tail]
        push_cast at h1 ⊢
        linarith
      · intro y hy
        simp only [mem_filter, mem_univ, true_and] at hy ⊢
        refine ⟨?_, Fin.cons_zero _ _⟩
        rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        push_cast at hy ⊢
        linarith
      · intro y hy
        simp only [mem_filter, mem_univ, true_and] at hy
        rw [← hy.2]
        exact Fin.cons_self_tail y
      · intro y _
        exact Fin.tail_cons _ _
    rw [card_eq_sum_card_fiberwise (f := fun y : Fin (L + 1) → Fin 3 => y 0) (t := univ)
      (fun _ _ => mem_univ _), Fin.sum_univ_three, hf 0, hf 1, hf 2, tri_succ, ← ih m,
      ← ih (m - 1), ← ih (m - 2)]
    simp

lemma sum_tri (L : ℕ) : ∑ m ∈ range (2 * L + 1), tri L m = 3 ^ L := by
  have h := card_eq_sum_card_fiberwise (f := fun y : Fin L → Fin 3 => ∑ i, (y i : ℕ))
    (s := univ) (t := range (2 * L + 1)) (fun y _ => by
      simp only [coe_range, Set.mem_Iio]
      have : ∑ i, (y i : ℕ) ≤ ∑ _i : Fin L, 2 :=
        sum_le_sum (fun i _ => by have := (y i).isLt; omega)
      simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at this
      omega)
  rw [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h
  rw [h]
  refine sum_congr rfl (fun m _ => ?_)
  rw [← card_sum L m]
  congr 1
  ext y
  simp only [mem_filter, mem_univ, true_and, Nat.cast_inj]

/-- The 0..2 arrays of length L with sum below L - j, counted through tri. -/
def Gm (L j : ℕ) : ℕ := ∑ m ∈ range (2 * L + 1), if m + j < L then tri L m else 0

lemma Gm_zero (L : ℕ) : 2 * Gm L 0 + tri L L = 3 ^ L := by
  have hr : ∑ m ∈ range (2 * L + 1), (if L < m then tri L m else 0) = Gm L 0 := by
    unfold Gm
    refine sum_nbij' (fun m => 2 * L - m) (fun m => 2 * L - m) ?_ ?_ ?_ ?_ ?_
    · intro m hm
      simp only [mem_range] at hm ⊢
      omega
    · intro m hm
      simp only [mem_range] at hm ⊢
      omega
    · intro m hm
      simp only [mem_range] at hm
      omega
    · intro m hm
      simp only [mem_range] at hm
      omega
    · intro m hm
      simp only [mem_range] at hm
      by_cases h : L < m
      · rw [if_pos h, if_pos (by omega)]
        exact tri_symm L m (2 * L - m : ℕ) (by omega)
      · rw [if_neg h, if_neg (by omega)]
  have hsplit : ∑ m ∈ range (2 * L + 1), tri L m =
      Gm L 0 + tri L L + ∑ m ∈ range (2 * L + 1), (if L < m then tri L m else 0) := by
    unfold Gm
    rw [show tri L L = ∑ m ∈ range (2 * L + 1), (if m = L then tri L m else 0) by
      rw [sum_ite_eq', if_pos (by simp only [mem_range]; omega)]]
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl (fun m _ => ?_)
    split_ifs <;> omega
  rw [← sum_tri L, hsplit, hr]
  ring

lemma Gm_succ (L j : ℕ) : (Gm L j : ℤ) = Gm L (j + 1) + tri L ((L : ℤ) - j - 1) := by
  unfold Gm
  have hp : ∀ m ∈ range (2 * L + 1), (if m + j < L then tri L m else 0) =
      (if m + (j + 1) < L then tri L m else 0) + (if m + (j + 1) = L then tri L m else 0) := by
    intro m _
    split_ifs <;> omega
  rw [sum_congr rfl hp, sum_add_distrib]
  push_cast
  congr 1
  by_cases h : j + 1 ≤ L
  · rw [sum_eq_single (L - (j + 1))]
    · rw [if_pos (by omega)]
      congr 2
      omega
    · intro m _ hm
      rw [if_neg (by omega)]
    · intro hm
      simp only [mem_range] at hm
      omega
  · rw [sum_eq_zero (fun m _ => by rw [if_neg (by omega)]), tri_neg L _ (by omega)]
    simp

/-- T L j = tri L (L + j): the trinomial coefficients around the center, as rationals. -/
def T (L : ℕ) (j : ℤ) : ℚ := (tri L (L + j) : ℚ)

lemma T_neg (L : ℕ) (j : ℤ) : T L (-j) = T L j := by
  unfold T
  rw [tri_symm L (L + -j) (L + j) (by ring)]

lemma T_succ0 (L : ℕ) : T (L + 1) 0 = T L 0 + 2 * T L 1 := by
  unfold T
  rw [show ((L + 1 : ℕ) : ℤ) + 0 = (L : ℤ) + 1 by push_cast; ring, tri_succ,
    show (L : ℤ) + 1 - 1 = L + 0 by ring, show (L : ℤ) + 1 - 2 = L + -1 by ring,
    tri_symm L (L + -1) (L + 1) (by ring)]
  push_cast
  ring

lemma T_up (L : ℕ) (j : ℤ) :
    ((L : ℚ) + j + 1) * T L (j + 1) = -(j : ℚ) * T L j + ((L : ℚ) - j + 1) * T L (j - 1) := by
  unfold T
  have h := tri_rec L (L + j)
  rw [show (L : ℤ) + j + 1 = L + (j + 1) by ring, show (L : ℤ) + j - 1 = L + (j - 1) by ring] at h
  have h' := congrArg (fun z : ℤ => (z : ℚ)) h
  push_cast at h'
  linear_combination h'

lemma T_succ1 (L : ℕ) : ((L : ℚ) + 2) * T (L + 1) 1 = ((L : ℚ) + 1) * (2 * T L 0 + T L 1) := by
  have h2 := T_up L 1
  have hs : T (L + 1) 1 = T L 2 + T L 1 + T L 0 := by
    unfold T
    rw [show ((L + 1 : ℕ) : ℤ) + 1 = (L : ℤ) + 2 by push_cast; ring, tri_succ,
      show (L : ℤ) + 2 - 1 = L + 1 by ring, show (L : ℤ) + 2 - 2 = L + 0 by ring]
    push_cast
    ring
  rw [hs]
  norm_num at h2 ⊢
  linear_combination h2

lemma Gm_eq (L j : ℕ) : (Gm L j : ℚ) = (3 ^ L - T L 0) / 2 - ∑ i ∈ range j, T L (i + 1) := by
  induction j with
  | zero =>
    have h := Gm_zero L
    simp only [sum_range_zero, sub_zero]
    unfold T
    rw [add_zero]
    have h' : ((2 * Gm L 0 + tri L L : ℕ) : ℚ) = ((3 ^ L : ℕ) : ℚ) := by rw [h]
    push_cast at h'
    linarith
  | succ j ih =>
    have h := Gm_succ L j
    have h' : ((Gm L j : ℤ) : ℚ) = ((Gm L (j + 1) + tri L ((L : ℤ) - j - 1) : ℤ) : ℚ) := by rw [h]
    push_cast at h'
    rw [sum_range_succ]
    have hT : (tri L ((L : ℤ) - j - 1) : ℚ) = T L ((j : ℤ) + 1) := by
      rw [← T_neg]
      unfold T
      congr 2
      ring
    push_cast
    linarith


/-- The entries of an array as a function on ℕ (0 beyond its length). -/
def ext {L : ℕ} (x : Fin L → Fin 3) (t : ℕ) : ℕ := if h : t < L then (x ⟨t, h⟩ : ℕ) else 0

lemma ext_fin {L : ℕ} (x : Fin L → Fin 3) (t : Fin L) : ext x t = (x t : ℕ) := by
  simp [ext, t.isLt]

lemma sum_fin_filter (L : ℕ) (f : ℕ → ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ((univ.filter (fun t : Fin L => P t)).sum fun t => f t) = ((range L).filter P).sum f := by
  rw [sum_filter, sum_filter]
  exact Fin.sum_univ_eq_sum_range (fun t => if P t then f t else 0) L

/-- The outer pairs (x t, x (2n + t)), t < k, of an array of length 2n + k. -/
def po {n k : ℕ} (x : Fin (2 * n + k) → Fin 3) : Fin k → Fin 3 × Fin 3 :=
  fun t => (x ⟨t, by omega⟩, x ⟨2 * n + t, by omega⟩)

/-- The middle part x (k + j), j < 2n - k, of an array of length 2n + k. -/
def pm {n k : ℕ} (x : Fin (2 * n + k) → Fin 3) : Fin (2 * n - k) → Fin 3 :=
  fun j => x ⟨k + j, by omega⟩

/-- The array with outer pairs p and middle part mid. -/
def glue {n k : ℕ} (p : Fin k → Fin 3 × Fin 3) (mid : Fin (2 * n - k) → Fin 3) :
    Fin (2 * n + k) → Fin 3 :=
  fun t => if h1 : (t : ℕ) < k then (p ⟨t, h1⟩).1 else
    if h2 : (t : ℕ) < 2 * n then mid ⟨t - k, by omega⟩ else (p ⟨t - 2 * n, by omega⟩).2

lemma po_glue {n k : ℕ} (hk : k ≤ 2 * n) (p : Fin k → Fin 3 × Fin 3) (mid : Fin (2 * n - k) → Fin 3) :
    po (glue p mid) = p := by
  funext t
  have ht := t.isLt
  apply Prod.ext
  · simp only [po, glue, dif_pos ht, Fin.eta]
  · simp only [po, glue]
    rw [dif_neg (by omega), dif_neg (by omega)]
    congr 2
    exact Fin.ext (by simp)

lemma pm_glue {n k : ℕ} (hk : k ≤ 2 * n) (p : Fin k → Fin 3 × Fin 3) (mid : Fin (2 * n - k) → Fin 3) :
    pm (glue p mid) = mid := by
  funext j
  have hj := j.isLt
  simp only [pm, glue]
  rw [dif_neg (by omega), dif_pos (by omega)]
  congr 1
  ext
  simp only
  omega

lemma glue_po {n k : ℕ} (hk : k ≤ 2 * n) (x : Fin (2 * n + k) → Fin 3) : glue (po x) (pm x) = x := by
  funext t
  have ht := t.isLt
  simp only [glue, po, pm]
  split_ifs with h1 h2
  · rfl
  · congr 1
    ext
    simp only
    omega
  · congr 1
    ext
    simp only
    omega

/-- The entries of the window starting at i that lie outside the middle part. -/
def A {k : ℕ} (p : Fin k → Fin 3 × Fin 3) (i : ℕ) : ℕ :=
  ((univ.filter (fun t : Fin k => i ≤ (t : ℕ))).sum fun t => ((p t).1 : ℕ)) +
    (univ.filter (fun t : Fin k => (t : ℕ) < i)).sum fun t => ((p t).2 : ℕ)

lemma window {n k : ℕ} (hk : k ≤ 2 * n) (x : Fin (2 * n + k) → Fin 3) (i : ℕ) (hi : i ≤ k) :
    ((univ.filter (fun t : Fin (2 * n + k) => i ≤ (t : ℕ) ∧ (t : ℕ) < i + 2 * n)).sum
      fun t => (x t : ℕ)) = A (po x) i + ∑ j, (pm x j : ℕ) := by
  have e0 : ((univ.filter (fun t : Fin (2 * n + k) => i ≤ (t : ℕ) ∧ (t : ℕ) < i + 2 * n)).sum
      fun t => (x t : ℕ)) = ∑ t ∈ Ico i (i + 2 * n), ext x t := by
    rw [← sum_congr rfl (fun t _ => ext_fin x t), sum_fin_filter (2 * n + k) (ext x)
      (fun t => i ≤ t ∧ t < i + 2 * n)]
    congr 1
    ext t
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  have e1 : ((univ.filter (fun t : Fin k => i ≤ (t : ℕ))).sum fun t => ((po x t).1 : ℕ)) =
      ∑ t ∈ Ico i k, ext x t := by
    rw [show Ico i k = (range k).filter (fun t => i ≤ t) by
      ext t
      simp only [mem_Ico, mem_filter, mem_range]
      omega]
    rw [← sum_fin_filter k (ext x) (fun t => i ≤ t)]
    refine sum_congr rfl (fun t _ => ?_)
    have := t.isLt
    simp only [po, ext]
    rw [dif_pos (by omega)]
  have e2 : ((univ.filter (fun t : Fin k => (t : ℕ) < i)).sum fun t => ((po x t).2 : ℕ)) =
      ∑ t ∈ Ico (2 * n) (2 * n + i), ext x t := by
    rw [sum_Ico_eq_sum_range, show 2 * n + i - 2 * n = i by omega]
    rw [show ((univ.filter (fun t : Fin k => (t : ℕ) < i)).sum fun t => ((po x t).2 : ℕ)) =
        ((univ.filter (fun t : Fin k => (t : ℕ) < i)).sum fun t => ext x (2 * n + t)) from
      sum_congr rfl (fun t _ => by simp only [po, ext]; rw [dif_pos (by omega)])]
    rw [sum_fin_filter k (fun t => ext x (2 * n + t)) (fun t => t < i)]
    congr 1
    ext t
    simp only [mem_filter, mem_range]
    omega
  have e3 : ∑ j, (pm x j : ℕ) = ∑ t ∈ Ico k (2 * n), ext x t := by
    rw [sum_Ico_eq_sum_range]
    rw [show ∑ j, (pm x j : ℕ) = ∑ j : Fin (2 * n - k), ext x (k + j) from
      sum_congr rfl (fun j _ => by simp only [pm, ext]; rw [dif_pos (by omega)])]
    exact Fin.sum_univ_eq_sum_range (fun j => ext x (k + j)) (2 * n - k)
  unfold A
  rw [e0, e1, e2, e3, ← sum_Ico_consecutive _ (show i ≤ k by omega) (show k ≤ i + 2 * n by omega),
    ← sum_Ico_consecutive _ (show k ≤ 2 * n by omega) (show 2 * n ≤ i + 2 * n by omega),
    show i + 2 * n = 2 * n + i by ring]
  ring

/-- Every window has its outer entries at most c. -/
def W {k : ℕ} (p : Fin k → Fin 3 × Fin 3) (c : ℤ) : Prop := ∀ i ≤ k, (A p i : ℤ) ≤ c

instance {k : ℕ} (c : ℤ) : DecidablePred (fun p : Fin k → Fin 3 × Fin 3 => W p c) := fun p => by
  unfold W
  infer_instance

/-- The number of outer pair sequences of length k with every window excess at most c. -/
def F (k : ℕ) (c : ℤ) : ℕ := ((univ : Finset (Fin k → Fin 3 × Fin 3)).filter (fun p => W p c)).card

lemma duty_iff {n k : ℕ} (hk : k ≤ 2 * n) (x : Fin (2 * n + k) → Fin 3) :
    duty n x ↔ W (po x) (2 * n - 1 - ((∑ j, (pm x j : ℕ) : ℕ) : ℤ)) := by
  unfold duty W
  constructor
  · intro h i hi
    have := h ⟨i, by omega⟩ (by simp only; omega)
    simp only at this
    rw [window hk x i hi] at this
    omega
  · intro h i hi
    have hi' : (i : ℕ) ≤ k := by omega
    have := h i hi'
    rw [window hk x i hi']
    omega

lemma sum_ite_tri (L d e : ℕ) :
    ∑ m ∈ range (2 * L + 1), (if m + d = e then tri L m else 0) = tri L ((e : ℤ) - d) := by
  by_cases h1 : d ≤ e
  · by_cases h2 : e - d < 2 * L + 1
    · rw [sum_eq_single (e - d)]
      · rw [if_pos (by omega)]
        congr 1
        omega
      · intro m _ hm
        rw [if_neg (by omega)]
      · intro hm
        rw [mem_range] at hm
        omega
    · rw [sum_eq_zero (fun m hm => by rw [mem_range] at hm; rw [if_neg (by omega)]),
        tri_big L _ (by omega)]
  · rw [sum_eq_zero (fun m _ => if_neg (by omega)), tri_neg L _ (by omega)]

lemma a_gen (k n : ℕ) (hk : k ≤ 2 * n) :
    ((univ : Finset (Fin (2 * n + k) → Fin 3)).filter (duty n)).card =
      ∑ m ∈ range (2 * (2 * n - k) + 1), tri (2 * n - k) m * F k (2 * n - 1 - m) := by
  have h3 : ((univ : Finset (Fin (2 * n + k) → Fin 3)).filter (duty n)).card =
      ((univ : Finset ((Fin k → Fin 3 × Fin 3) × (Fin (2 * n - k) → Fin 3))).filter
        (fun q => W q.1 (2 * n - 1 - ((∑ j, (q.2 j : ℕ) : ℕ) : ℤ)))).card := by
    refine card_bij' (fun x _ => (po x, pm x)) (fun q _ => glue q.1 q.2) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx ⊢
      exact (duty_iff hk x).mp hx
    · intro q hq
      simp only [mem_filter, mem_univ, true_and] at hq ⊢
      rw [duty_iff hk, po_glue hk, pm_glue hk]
      exact hq
    · intro x _
      exact glue_po hk x
    · intro q _
      rw [po_glue hk, pm_glue hk]
  rw [h3, card_filter, Fintype.sum_prod_type, sum_comm]
  have h4 : ∀ mid : Fin (2 * n - k) → Fin 3,
      (∑ p : Fin k → Fin 3 × Fin 3, if W p (2 * n - 1 - ((∑ j, (mid j : ℕ) : ℕ) : ℤ)) then 1 else 0) =
        F k (2 * n - 1 - ((∑ j, (mid j : ℕ) : ℕ) : ℤ)) := by
    intro mid
    unfold F
    rw [card_filter]
  rw [sum_congr rfl (fun mid _ => h4 mid)]
  rw [← sum_fiberwise_of_maps_to (g := fun mid : Fin (2 * n - k) → Fin 3 => ∑ j, (mid j : ℕ))
    (t := range (2 * (2 * n - k) + 1)) (fun mid _ => by
      simp only [mem_range]
      have : ∑ j, (mid j : ℕ) ≤ ∑ _j : Fin (2 * n - k), 2 :=
        sum_le_sum (fun j _ => by have := (mid j).isLt; omega)
      simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at this
      omega)]
  refine sum_congr rfl (fun m _ => ?_)
  rw [sum_congr rfl (fun mid hmid => by
    rw [(mem_filter.mp hmid).2]), sum_const, smul_eq_mul]
  congr 1
  rw [← card_sum (2 * n - k) m]
  congr 1
  ext mid
  simp only [mem_filter, mem_univ, true_and, Nat.cast_inj]

lemma A_zero {k : ℕ} (p : Fin k → Fin 3 × Fin 3) : A p 0 = ∑ t, ((p t).1 : ℕ) := by
  unfold A
  rw [filter_true_of_mem (fun t _ => Nat.zero_le _),
    filter_false_of_mem (fun t _ => Nat.not_lt_zero _), sum_empty, add_zero]

lemma A_cons_succ {k : ℕ} (q : Fin 3 × Fin 3) (p : Fin k → Fin 3 × Fin 3) (i : ℕ) :
    A (Fin.cons q p : Fin (k + 1) → Fin 3 × Fin 3) (i + 1) = (q.2 : ℕ) + A p i := by
  unfold A
  rw [sum_filter, sum_filter, sum_filter, sum_filter, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ, add_le_add_iff_right,
    add_lt_add_iff_right]
  split_ifs <;> omega

lemma W_cons {k : ℕ} (q : Fin 3 × Fin 3) (p : Fin k → Fin 3 × Fin 3) (c : ℤ) :
    W (Fin.cons q p : Fin (k + 1) → Fin 3 × Fin 3) c ↔
      ((q.1 : ℕ) : ℤ) + ((∑ t, ((p t).1 : ℕ) : ℕ) : ℤ) ≤ c ∧ W p (c - (q.2 : ℕ)) := by
  unfold W
  constructor
  · intro h
    refine ⟨?_, fun i hi => ?_⟩
    · have := h 0 (Nat.zero_le _)
      rw [A_zero, Fin.sum_univ_succ] at this
      simp only [Fin.cons_zero, Fin.cons_succ] at this
      push_cast at this ⊢
      linarith
    · have := h (i + 1) (by omega)
      rw [A_cons_succ] at this
      push_cast at this
      linarith
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero =>
      rw [A_zero, Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      push_cast at h0 ⊢
      linarith
    | succ i =>
      rw [A_cons_succ]
      have := h i (by omega)
      push_cast at this ⊢
      linarith

/-- The number of outer pair sequences of length k with first-entry sum at most a and every
window excess at most b, by the first pair. -/
def F2 : ℕ → ℤ → ℤ → ℕ
  | 0, a, b => if 0 ≤ a ∧ 0 ≤ b then 1 else 0
  | k + 1, a, b =>
    F2 k (min a b) b + F2 k (min a b) (b - 1) + F2 k (min a b) (b - 2) +
      (F2 k (min a b - 1) b + F2 k (min a b - 1) (b - 1) + F2 k (min a b - 1) (b - 2)) +
      (F2 k (min a b - 2) b + F2 k (min a b - 2) (b - 1) + F2 k (min a b - 2) (b - 2))

lemma card_F2 (k : ℕ) (a b : ℤ) :
    ((univ : Finset (Fin k → Fin 3 × Fin 3)).filter
      (fun p => ((∑ t, ((p t).1 : ℕ) : ℕ) : ℤ) ≤ a ∧ W p b)).card = F2 k a b := by
  induction k generalizing a b with
  | zero =>
    simp only [F2]
    have hW : ∀ p : Fin 0 → Fin 3 × Fin 3, W p b ↔ 0 ≤ b := by
      intro p
      unfold W
      constructor
      · intro h
        have := h 0 le_rfl
        rw [A_zero] at this
        simpa using this
      · intro h i hi
        have : i = 0 := by omega
        subst this
        rw [A_zero]
        simpa using h
    split_ifs with h
    · rw [filter_true_of_mem (fun p _ => ⟨by simpa using h.1, (hW p).mpr h.2⟩)]
      rfl
    · rw [card_eq_zero, filter_eq_empty_iff]
      intro p _ hp
      apply h
      refine ⟨?_, (hW p).mp hp.2⟩
      simpa using hp.1
  | succ k ih =>
    have hf : ∀ q : Fin 3 × Fin 3, ((univ.filter (fun p : Fin (k + 1) → Fin 3 × Fin 3 =>
        ((∑ t, ((p t).1 : ℕ) : ℕ) : ℤ) ≤ a ∧ W p b)).filter (fun p => p 0 = q)).card =
        F2 k (min a b - (q.1 : ℕ)) (b - (q.2 : ℕ)) := by
      intro q
      rw [← ih]
      refine card_bij' (fun p _ => Fin.tail p) (fun p _ => Fin.cons q p) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [mem_filter, mem_univ, true_and] at hp ⊢
        obtain ⟨⟨h1, h2⟩, h3⟩ := hp
        have e : p = Fin.cons q (Fin.tail p) := by
          rw [← h3]
          exact (Fin.cons_self_tail p).symm
        rw [e, W_cons] at h2
        rw [e, Fin.sum_univ_succ] at h1
        simp only [Fin.cons_zero, Fin.cons_succ] at h1
        refine ⟨?_, h2.2⟩
        push_cast at h1 h2 ⊢
        omega
      · intro p hp
        simp only [mem_filter, mem_univ, true_and] at hp ⊢
        refine ⟨⟨?_, (W_cons q p b).mpr ⟨?_, hp.2⟩⟩, Fin.cons_zero _ _⟩
        · rw [Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          push_cast at hp ⊢
          omega
        · push_cast at hp ⊢
          omega
      · intro p hp
        simp only [mem_filter, mem_univ, true_and] at hp
        rw [← hp.2]
        exact Fin.cons_self_tail p
      · intro p _
        exact Fin.tail_cons _ _
    rw [card_eq_sum_card_fiberwise (f := fun p : Fin (k + 1) → Fin 3 × Fin 3 => p 0) (t := univ)
      (fun _ _ => mem_univ _), sum_congr rfl (fun q _ => hf q), Fintype.sum_prod_type]
    simp only [Fin.sum_univ_three, F2]
    simp

lemma F_eq (k : ℕ) (c : ℤ) : F k c = F2 k c c := by
  rw [← card_F2]
  unfold F
  congr 1
  ext p
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro h
    refine ⟨?_, h⟩
    have := h 0 (Nat.zero_le _)
    rw [A_zero] at this
    exact this
  · exact fun h => h.2

lemma A_le {k : ℕ} (p : Fin k → Fin 3 × Fin 3) (i : ℕ) : A p i ≤ 2 * k := by
  unfold A
  have h1 : ((univ.filter (fun t : Fin k => i ≤ (t : ℕ))).sum fun t => ((p t).1 : ℕ)) ≤
      (univ.filter (fun t : Fin k => i ≤ (t : ℕ))).card • 2 :=
    sum_le_card_nsmul _ _ _ (fun t _ => by have := (p t).1.isLt; omega)
  have h2 : ((univ.filter (fun t : Fin k => (t : ℕ) < i)).sum fun t => ((p t).2 : ℕ)) ≤
      (univ.filter (fun t : Fin k => (t : ℕ) < i)).card • 2 :=
    sum_le_card_nsmul _ _ _ (fun t _ => by have := (p t).2.isLt; omega)
  have h3 := card_filter_add_card_filter_not (s := (univ : Finset (Fin k)))
    (fun t : Fin k => i ≤ (t : ℕ))
  simp only [not_le, card_univ, Fintype.card_fin] at h3
  simp only [smul_eq_mul] at h1 h2
  omega

lemma F_big (k : ℕ) (c : ℤ) (hc : 2 * (k : ℤ) ≤ c) : F k c = 9 ^ k := by
  unfold F
  rw [filter_true_of_mem (fun p _ i _ => by have := A_le p i; omega), card_univ,
    Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

lemma F_neg (k : ℕ) (c : ℤ) (hc : c < 0) : F k c = 0 := by
  unfold F
  rw [card_eq_zero, filter_eq_empty_iff]
  intro p _ hp
  have := hp 0 (Nat.zero_le _)
  omega

lemma a_split (k n : ℕ) (hk : k ≤ 2 * n) :
    ((univ : Finset (Fin (2 * n + k) → Fin 3)).filter (duty n)).card =
      9 ^ k * Gm (2 * n - k) k +
        ∑ c ∈ range (2 * k), F k c * tri (2 * n - k) (2 * (n : ℤ) - 1 - c) := by
  rw [a_gen k n hk]
  have hp : ∀ m ∈ range (2 * (2 * n - k) + 1), tri (2 * n - k) m * F k (2 * n - 1 - m) =
      9 ^ k * (if m + k < 2 * n - k then tri (2 * n - k) m else 0) +
        ∑ c ∈ range (2 * k), F k c * (if m + (c + 1) = 2 * n then tri (2 * n - k) m else 0) := by
    intro m _
    by_cases h1 : m + 2 * k < 2 * n
    · rw [F_big k _ (by omega), if_pos (by omega),
        sum_eq_zero (fun c hc => by rw [mem_range] at hc; rw [if_neg (by omega), mul_zero])]
      ring
    · by_cases h2 : 2 * n ≤ m
      · rw [F_neg k _ (by omega), if_neg (by omega),
          sum_eq_zero (fun c hc => by rw [if_neg (by omega), mul_zero])]
        ring
      · rw [if_neg (by omega), sum_eq_single (2 * n - 1 - m)]
        · rw [if_pos (by omega), show ((2 * n - 1 - m : ℕ) : ℤ) = 2 * n - 1 - m by omega]
          ring
        · intro c _ hc
          rw [if_neg (by omega), mul_zero]
        · intro hc
          rw [mem_range] at hc
          omega
  rw [sum_congr rfl hp, sum_add_distrib, ← mul_sum, sum_comm]
  congr 1
  refine sum_congr rfl (fun c _ => ?_)
  rw [← mul_sum, sum_ite_tri]
  congr 2
  push_cast
  ring

lemma tri_T (B : ℕ) (m j : ℤ) (h : m = (B : ℤ) + j) : (tri B m : ℚ) = T B j := by
  unfold T
  rw [h]

lemma T_nonneg (L : ℕ) (j : ℤ) : 0 ≤ T L j := by
  unfold T
  positivity

lemma T_pascal (L : ℕ) (j : ℤ) : T L (j + 1) ≤ T (L + 1) j := by
  unfold T
  rw [show ((L + 1 : ℕ) : ℤ) + j = (L : ℤ) + (j + 1) by push_cast; ring, tri_succ]
  push_cast
  have h1 : (0 : ℚ) ≤ (tri L (L + (j + 1) - 1) : ℚ) := by positivity
  have h2 : (0 : ℚ) ≤ (tri L (L + (j + 1) - 2) : ℚ) := by positivity
  linarith

lemma T0_mono (L d : ℕ) : T L 0 ≤ T (L + d) 0 := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← add_assoc, T_succ0]
    have := T_nonneg (L + d) 1
    linarith

lemma T_le_top (L j d : ℕ) (hj : j ≤ d) : T L j ≤ T (L + d) 0 := by
  induction j generalizing L d with
  | zero =>
    exact T0_mono L d
  | succ j ih =>
    have h1 := T_pascal L j
    have h2 := ih (L + 1) (d - 1) (by omega)
    rw [show L + 1 + (d - 1) = L + d by omega] at h2
    push_cast
    linarith

lemma central (L : ℕ) :
    ((L : ℚ) + 2) * T (L + 2) 0 = (2 * L + 3) * T (L + 1) 0 + 3 * (L + 1) * T L 0 := by
  have h1 := T_succ0 (L + 1)
  have h2 := T_succ1 L
  have h3 := T_succ0 L
  rw [show L + 1 + 1 = L + 2 by ring] at h1
  linear_combination ((L : ℚ) + 2) * h1 + 2 * h2 - ((L : ℚ) + 1) * h3

/-- The central trinomial coefficients are o(3^L). -/
lemma P_tendsto : Tendsto (fun L : ℕ => (T L 0 : ℝ) / 3 ^ L) atTop (𝓝 0) := by
  set P : ℕ → ℝ := fun L => (T L 0 : ℝ) / 3 ^ L with hP
  have hpos : ∀ L, 0 ≤ P L := fun L => div_nonneg (by exact_mod_cast T_nonneg L 0) (by positivity)
  have hq : ∀ L, P L * 3 ^ L = T L 0 := fun L => div_mul_cancel₀ _ (by positivity)
  have hR : ∀ L : ℕ, 3 * ((L : ℝ) + 2) * P (L + 2) = (2 * L + 3) * P (L + 1) + (L + 1) * P L := by
    intro L
    have h := central L
    have h' : ((((L : ℚ) + 2) * T (L + 2) 0 : ℚ) : ℝ) =
        (((2 * L + 3) * T (L + 1) 0 + 3 * (L + 1) * T L 0 : ℚ) : ℝ) := by rw [h]
    push_cast at h'
    have q0 := hq L
    have q1 := hq (L + 1)
    have q2 := hq (L + 2)
    rw [pow_succ] at q1
    rw [pow_succ, pow_succ] at q2
    apply mul_right_cancel₀ (show (3 : ℝ) ^ L * 3 ≠ 0 by positivity)
    linear_combination ((L : ℝ) + 2) * q2 - (2 * L + 3) * q1 - 3 * ((L : ℝ) + 1) * q0 + h'
  have hP0 : P 0 = 1 := by
    simp only [hP, T, tri_zero]
    norm_num
  have hP1 : P 1 = 1 / 3 := by
    simp only [hP, T, tri_succ, tri_zero]
    norm_num
  have hS : ∀ L : ℕ, P (L + 1) ≤ P L ∧ (3 * (L : ℝ) + 1) * P L ≤ 3 * (L + 1) * P (L + 1) := by
    intro L
    induction L with
    | zero =>
      rw [hP0, show (0 : ℕ) + 1 = 1 from rfl, hP1]
      norm_num
    | succ L ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hr := hR L
      have hp0 := hpos L
      have hp1 := hpos (L + 1)
      have hL : (0 : ℝ) ≤ L := by positivity
      push_cast
      rw [show L + 1 + 1 = L + 2 by ring]
      have key : ((L : ℝ) + 1) * P L ≤ ((L : ℝ) + 3) * P (L + 1) := by
        nlinarith [mul_le_mul_of_nonneg_left ih2 (show (0 : ℝ) ≤ L + 1 by positivity)]
      constructor
      · nlinarith
      · nlinarith
  have hD : ∀ L : ℕ, 3 * ((L : ℝ) + 2) * P (L + 2) ≤ (3 * L + 4) * P L := by
    intro L
    have := hR L
    have := (hS L).1
    nlinarith [hpos L, hpos (L + 1)]
  have hQ : ∀ L : ℕ, ((L : ℝ) + 2) * P L ^ 3 ≤ 2 ∧ ((L : ℝ) + 3) * P (L + 1) ^ 3 ≤ 2 := by
    intro L
    induction L with
    | zero =>
      rw [hP0, show (0 : ℕ) + 1 = 1 from rfl, hP1]
      norm_num
    | succ L ih =>
      refine ⟨by push_cast; linarith [ih.2], ?_⟩
      have hd := hD L
      have ha := hpos (L + 2)
      have hb := hpos L
      have hL : (0 : ℝ) ≤ L := by positivity
      have h1 : P (L + 2) ≤ (3 * L + 4) / (3 * L + 6) * P L := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        linarith
      have h2 : P (L + 2) ^ 3 ≤ ((3 * L + 4) / (3 * L + 6)) ^ 3 * P L ^ 3 := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ ha h1 3
      have h3 : ((L : ℝ) + 4) * ((3 * L + 4) / (3 * L + 6)) ^ 3 ≤ L + 2 := by
        rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg (L : ℝ), mul_nonneg hL (sq_nonneg (L : ℝ))]
      have h4 : ((L : ℝ) + 4) * P (L + 2) ^ 3 ≤ ((L : ℝ) + 2) * P L ^ 3 := by
        calc ((L : ℝ) + 4) * P (L + 2) ^ 3
            ≤ ((L : ℝ) + 4) * (((3 * L + 4) / (3 * L + 6)) ^ 3 * P L ^ 3) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = (((L : ℝ) + 4) * ((3 * L + 4) / (3 * L + 6)) ^ 3) * P L ^ 3 := by ring
          _ ≤ ((L : ℝ) + 2) * P L ^ 3 := mul_le_mul_of_nonneg_right h3 (by positivity)
      push_cast
      rw [show L + 1 + 1 = L + 2 by ring]
      linarith [ih.1]
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε ^ 3)
  refine ⟨N, fun L hL => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hpos L)]
  by_contra h
  have h1 : ε ^ 3 ≤ P L ^ 3 := pow_le_pow_left₀ hε.le (not_lt.mp h) 3
  have h2 : (2 : ℝ) / ε ^ 3 < L + 2 := by
    have : (N : ℝ) ≤ L := Nat.cast_le.mpr hL
    linarith
  rw [div_lt_iff₀ (by positivity)] at h2
  have h3 := (hQ L).1
  nlinarith [mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ L + 2 by positivity)]

lemma T2 (L : ℕ) : T L 2 = (((L : ℚ)) * T L 0 + (-1) * T L 1) / (((L : ℚ) + 2)) := by
  have h := T_up L 1
  rw [eq_div_iff (by positivity)]
  norm_num at h
  linear_combination h

lemma sh1 (L : ℕ) : T (L + 1) 0 = T L 0 + 2 * T L 1 ∧
    T (L + 1) 1 = ((2 + 2 * (L : ℚ)) * T L 0 + (1 + (L : ℚ)) * T L 1) / (((L : ℚ) + 2)) := by
  refine ⟨T_succ0 L, ?_⟩
  rw [eq_div_iff (by positivity)]
  linear_combination T_succ1 L

lemma sh2 (L : ℕ) : T (L + 2) 0 = ((6 + 5 * (L : ℚ)) * T L 0 + (6 + 4 * (L : ℚ)) * T L 1) / (((L : ℚ) + 2)) ∧
      T (L + 2) 1 = ((6 + 4 * (L : ℚ)) * T L 0 + (9 + 5 * (L : ℚ)) * T L 1) / (((L : ℚ) + 3)) := by
  obtain ⟨a1, b1⟩ := sh1 (L + 1)
  obtain ⟨a0, b0⟩ := sh1 L
  rw [show L + 1 + 1 = L + 2 by ring] at a1 b1
  rw [a1, b1, a0, b0]
  push_cast
  have h2 : (L : ℚ) + 2 ≠ 0 := by positivity
  have h3 : (L : ℚ) + 3 ≠ 0 := by positivity
  constructor
  · field_simp
    ring
  · field_simp
    ring

lemma sh4 (L : ℕ) : T (L + 4) 0 = ((456 + 670 * (L : ℚ) + 297 * (L : ℚ) ^ 2 + 41 * (L : ℚ) ^ 3) * T L 0 + (540 + 716 * (L : ℚ) + 300 * (L : ℚ) ^ 2 + 40 * (L : ℚ) ^ 3) * T L 1) / (((L : ℚ) + 2) * ((L : ℚ) + 3) * ((L : ℚ) + 4)) ∧
      T (L + 4) 1 = ((480 + 692 * (L : ℚ) + 300 * (L : ℚ) ^ 2 + 40 * (L : ℚ) ^ 3) * T L 0 + (594 + 775 * (L : ℚ) + 318 * (L : ℚ) ^ 2 + 41 * (L : ℚ) ^ 3) * T L 1) / (((L : ℚ) + 2) * ((L : ℚ) + 3) * ((L : ℚ) + 5)) := by
  obtain ⟨a1, b1⟩ := sh2 (L + 2)
  obtain ⟨a0, b0⟩ := sh2 L
  rw [show L + 2 + 2 = L + 4 by ring] at a1 b1
  rw [a1, b1, a0, b0]
  push_cast
  have h2 : (L : ℚ) + 2 ≠ 0 := by positivity
  have h3 : (L : ℚ) + 3 ≠ 0 := by positivity
  have h4 : (L : ℚ) + 4 ≠ 0 := by positivity
  have h5 : (L : ℚ) + 5 ≠ 0 := by positivity
  constructor
  · field_simp
    ring
  · field_simp
    ring

lemma sh6 (L : ℕ) : T (L + 6) 0 = ((101520 + 189492 * (L : ℚ) + 129676 * (L : ℚ) ^ 2 + 41515 * (L : ℚ) ^ 3 + 6296 * (L : ℚ) ^ 4 + 365 * (L : ℚ) ^ 5) * T L 0 + (122472 + 211392 * (L : ℚ) + 138026 * (L : ℚ) ^ 2 + 42872 * (L : ℚ) ^ 3 + 6370 * (L : ℚ) ^ 4 + 364 * (L : ℚ) ^ 5) * T L 1) / (((L : ℚ) + 2) * ((L : ℚ) + 3) * ((L : ℚ) + 4) * ((L : ℚ) + 5) * ((L : ℚ) + 6)) ∧
      T (L + 6) 1 = ((105840 + 196644 * (L : ℚ) + 133742 * (L : ℚ) ^ 2 + 42464 * (L : ℚ) ^ 3 + 6370 * (L : ℚ) ^ 4 + 364 * (L : ℚ) ^ 5) * T L 0 + (128304 + 220446 * (L : ℚ) + 143065 * (L : ℚ) ^ 2 + 44077 * (L : ℚ) ^ 3 + 6479 * (L : ℚ) ^ 4 + 365 * (L : ℚ) ^ 5) * T L 1) / (((L : ℚ) + 2) * ((L : ℚ) + 3) * ((L : ℚ) + 4) * ((L : ℚ) + 5) * ((L : ℚ) + 7)) := by
  obtain ⟨a1, b1⟩ := sh2 (L + 4)
  obtain ⟨a0, b0⟩ := sh4 L
  rw [show L + 4 + 2 = L + 6 by ring] at a1 b1
  rw [a1, b1, a0, b0]
  push_cast
  have h2 : (L : ℚ) + 2 ≠ 0 := by positivity
  have h3 : (L : ℚ) + 3 ≠ 0 := by positivity
  have h4 : (L : ℚ) + 4 ≠ 0 := by positivity
  have h5 : (L : ℚ) + 5 ≠ 0 := by positivity
  have h6 : (L : ℚ) + 6 ≠ 0 := by positivity
  have h7 : (L : ℚ) + 7 ≠ 0 := by positivity
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- The part of a(n) beyond 3^k 9^n / 2, at L = 2n - k. -/
def ts (L : ℕ) : ℚ := (-(65 / 2)) * T L 0 + (-49) * T L 1 + (-21) * T L 2

lemma ts_eq (L : ℕ) : ts L = ((-65 - (107 / 2) * (L : ℚ)) * T L 0 + (-77 - 49 * (L : ℚ)) * T L 1) / (((L : ℚ) + 2)) := by
  unfold ts
  rw [T2 L]
  have h2 : (L : ℚ) + 2 ≠ 0 := by positivity
  field_simp
  ring

lemma ts2 (L : ℕ) : ts (L + 2) = ((-5196 - 7613 * (L : ℚ) - (6739 / 2) * (L : ℚ) ^ 2 - (927 / 2) * (L : ℚ) ^ 3) * T L 0 + (-6246 - 8266 * (L : ℚ) - 3457 * (L : ℚ) ^ 2 - 459 * (L : ℚ) ^ 3) * T L 1) / (((L : ℚ) + 2) * ((L : ℚ) + 3) * ((L : ℚ) + 4)) := by
  rw [ts_eq (L + 2)]
  obtain ⟨h0, h1⟩ := sh2 L
  rw [h0, h1]
  push_cast
  have h2 : (L : ℚ) + 2 ≠ 0 := by positivity
  have h3 : (L : ℚ) + 3 ≠ 0 := by positivity
  have h4 : (L : ℚ) + 4 ≠ 0 := by positivity
  field_simp
  ring

lemma ts4 (L : ℕ) : ts (L + 4) = ((-1160280 - 2164638 * (L : ℚ) - 1480534 * (L : ℚ) ^ 2 - (947277 / 2) * (L : ℚ) ^ 3 - 71756 * (L : ℚ) ^ 4 - (8307 / 2) * (L : ℚ) ^ 5) * T L 0 + (-1401948 - 2418816 * (L : ℚ) - 1578521 * (L : ℚ) ^ 2 - 489945 * (L : ℚ) ^ 3 - 72721 * (L : ℚ) ^ 4 - 4149 * (L : ℚ) ^ 5) * T L 1) / (((L : ℚ) + 2) * ((L : ℚ) + 3) * ((L : ℚ) + 4) * ((L : ℚ) + 5) * ((L : ℚ) + 6)) := by
  rw [ts_eq (L + 4)]
  obtain ⟨h0, h1⟩ := sh4 L
  rw [h0, h1]
  push_cast
  have h2 : (L : ℚ) + 2 ≠ 0 := by positivity
  have h3 : (L : ℚ) + 3 ≠ 0 := by positivity
  have h4 : (L : ℚ) + 4 ≠ 0 := by positivity
  have h5 : (L : ℚ) + 5 ≠ 0 := by positivity
  have h6 : (L : ℚ) + 6 ≠ 0 := by positivity
  field_simp
  ring

lemma ts6 (L : ℕ) : ts (L + 6) = ((-509906880 - 1097326488 * (L : ℚ) - 933588650 * (L : ℚ) ^ 2 - 414028800 * (L : ℚ) ^ 3 - (208986307 / 2) * (L : ℚ) ^ 4 - (30244881 / 2) * (L : ℚ) ^ 5 - (2337217 / 2) * (L : ℚ) ^ 6 - (74727 / 2) * (L : ℚ) ^ 7) * T L 0 + (-616524048 - 1240356096 * (L : ℚ) - 1011608296 * (L : ℚ) ^ 2 - 436173870 * (L : ℚ) ^ 3 - 107943931 * (L : ℚ) ^ 4 - 15402363 * (L : ℚ) ^ 5 - 1177813 * (L : ℚ) ^ 6 - 37359 * (L : ℚ) ^ 7) * T L 1) / (((L : ℚ) + 2) * ((L : ℚ) + 3) * ((L : ℚ) + 4) * ((L : ℚ) + 5) * ((L : ℚ) + 6) * ((L : ℚ) + 7) * ((L : ℚ) + 8)) := by
  rw [ts_eq (L + 6)]
  obtain ⟨h0, h1⟩ := sh6 L
  rw [h0, h1]
  push_cast
  have h2 : (L : ℚ) + 2 ≠ 0 := by positivity
  have h3 : (L : ℚ) + 3 ≠ 0 := by positivity
  have h4 : (L : ℚ) + 4 ≠ 0 := by positivity
  have h5 : (L : ℚ) + 5 ≠ 0 := by positivity
  have h6 : (L : ℚ) + 6 ≠ 0 := by positivity
  have h7 : (L : ℚ) + 7 ≠ 0 := by positivity
  have h8 : (L : ℚ) + 8 ≠ 0 := by positivity
  field_simp
  ring

/-- Kotesovec's recurrence for the part beyond 3^k 9^n / 2, with x = 2n - k - 6, as an identity of
rational functions. -/
lemma key (x u v : ℚ) (hx : 0 ≤ x) :
    (538356 + (7894465 / 2) * x + (18651009 / 4) * x ^ 2 + 2140346 * x ^ 3 + (1850295 / 4) * x ^ 4 + (94597 / 2) * x ^ 5 + 1845 * x ^ 6) * (((-509906880 - 1097326488 * x - 933588650 * x ^ 2 - 414028800 * x ^ 3 - (208986307 / 2) * x ^ 4 - (30244881 / 2) * x ^ 5 - (2337217 / 2) * x ^ 6 - (74727 / 2) * x ^ 7) * u + (-616524048 - 1240356096 * x - 1011608296 * x ^ 2 - 436173870 * x ^ 3 - 107943931 * x ^ 4 - 15402363 * x ^ 5 - 1177813 * x ^ 6 - 37359 * x ^ 7) * v) / ((x + 2) * (x + 3) * (x + 4) * (x + 5) * (x + 6) * (x + 7) * (x + 8))) - (10213056 + (126905527 / 2) * x + (298338375 / 4) * x ^ 2 + 35053070 * x ^ 3 + (31507161 / 4) * x ^ 4 + (1694023 / 2) * x ^ 5 + 35055 * x ^ 6) * (((-1160280 - 2164638 * x - 1480534 * x ^ 2 - (947277 / 2) * x ^ 3 - 71756 * x ^ 4 - (8307 / 2) * x ^ 5) * u + (-1401948 - 2418816 * x - 1578521 * x ^ 2 - 489945 * x ^ 3 - 72721 * x ^ 4 - 4149 * x ^ 5) * v) / ((x + 2) * (x + 3) * (x + 4) * (x + 5) * (x + 6))) - (-58958550 - (557035101 / 2) * x - (1279127943 / 4) * x ^ 2 - 154453752 * x ^ 3 - (145706013 / 4) * x ^ 4 - (8302383 / 2) * x ^ 5 - 182655 * x ^ 6) * (((-5196 - 7613 * x - (6739 / 2) * x ^ 2 - (927 / 2) * x ^ 3) * u + (-6246 - 8266 * x - 3457 * x ^ 2 - 459 * x ^ 3) * v) / ((x + 2) * (x + 3) * (x + 4))) - (95830938 + (489033207 / 2) * x + (943328673 / 4) * x ^ 2 + 111097332 * x ^ 3 + (108139131 / 4) * x ^ 4 + (6466797 / 2) * x ^ 5 + 149445 * x ^ 6) * (((-65 - (107 / 2) * x) * u + (-77 - 49 * x) * v) / ((x + 2))) = 0 := by
  have h2 : x + 2 ≠ 0 := by positivity
  have h3 : x + 3 ≠ 0 := by positivity
  have h4 : x + 4 ≠ 0 := by positivity
  have h5 : x + 5 ≠ 0 := by positivity
  have h6 : x + 6 ≠ 0 := by positivity
  have h7 : x + 7 ≠ 0 := by positivity
  have h8 : x + 8 ≠ 0 := by positivity
  field_simp
  ring

/-- The outer pair counts for window parts below 2k. -/
lemma Fv : F 2 0 = 1 ∧ F 2 1 = 8 ∧ F 2 2 = 31 ∧ F 2 3 = 60 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [F_eq] <;> decide +kernel

/-- a(n) = 3^k 9^n / 2 + ts (2n - k). -/
lemma rep (n : ℕ) (hn : 2 ≤ 2 * n) : (a n : ℚ) = 3 ^ 2 / 2 * 9 ^ n + ts (2 * n - 2) := by
  obtain ⟨f0, f1, f2, f3⟩ := Fv
  have h := a_split 2 n hn
  have h' : (a n : ℚ) = ((9 ^ 2 * Gm (2 * n - 2) 2 + ∑ c ∈ range (2 * 2),
      F 2 c * tri (2 * n - 2) (2 * (n : ℤ) - 1 - c) : ℕ) : ℚ) := by
    unfold a
    rw [h]
  rw [h']
  push_cast
  rw [sum_congr rfl (fun c _ => by
    rw [tri_T (2 * n - 2) (2 * (n : ℤ) - 1 - c) (2 - 1 - c) (by omega)]), Gm_eq]
  simp only [sum_range_succ, sum_range_zero, zero_add]
  norm_num [f0, f1, f2, f3, T_neg]
  have h3 : (3 : ℚ) ^ (2 * n - 2) * 3 ^ 2 = 9 ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hn, pow_mul]
    norm_num
  unfold ts
  linear_combination ((3 : ℚ) ^ 2 / 2) * h3

/-- Controls: the entry's listed terms, a(1) to a(18). -/
theorem controls :
    a 1 = 8 ∧ a 2 = 148 ∧ a 3 = 1669 ∧ a 4 = 16878 ∧
    a 5 = 163495 ∧ a 6 = 1549297 ∧ a 7 = 14492156 ∧ a 8 = 134429604 ∧
    a 9 = 1239807015 ∧ a 10 = 11386939467 ∧ a 11 = 104257566078 ∧ a 12 = 952281922551 ∧
    a 13 = 8681609266794 ∧ a 14 = 79026329849968 ∧ a 15 = 718456060049941 ∧ a 16 = 6524950672498742 ∧
    a 17 = 59207190970359999 ∧ a 18 = 536844632687526915 := by
  have u0 : T 0 0 = 1 := by simp [T, tri_zero]
  have v0 : T 0 1 = 0 := by simp [T, tri_zero]
  have u1 : T 1 0 = 1 := by
    have h := (sh1 0).1
    norm_num [u0, v0] at h
    exact h
  have v1 : T 1 1 = 1 := by
    have h := (sh1 0).2
    norm_num [u0, v0] at h
    exact h
  have u2 : T 2 0 = 3 := by
    have h := (sh1 1).1
    norm_num [u1, v1] at h
    exact h
  have v2 : T 2 1 = 2 := by
    have h := (sh1 1).2
    norm_num [u1, v1] at h
    exact h
  have u3 : T 3 0 = 7 := by
    have h := (sh1 2).1
    norm_num [u2, v2] at h
    exact h
  have v3 : T 3 1 = 6 := by
    have h := (sh1 2).2
    norm_num [u2, v2] at h
    exact h
  have u4 : T 4 0 = 19 := by
    have h := (sh1 3).1
    norm_num [u3, v3] at h
    exact h
  have v4 : T 4 1 = 16 := by
    have h := (sh1 3).2
    norm_num [u3, v3] at h
    exact h
  have u5 : T 5 0 = 51 := by
    have h := (sh1 4).1
    norm_num [u4, v4] at h
    exact h
  have v5 : T 5 1 = 45 := by
    have h := (sh1 4).2
    norm_num [u4, v4] at h
    exact h
  have u6 : T 6 0 = 141 := by
    have h := (sh1 5).1
    norm_num [u5, v5] at h
    exact h
  have v6 : T 6 1 = 126 := by
    have h := (sh1 5).2
    norm_num [u5, v5] at h
    exact h
  have u7 : T 7 0 = 393 := by
    have h := (sh1 6).1
    norm_num [u6, v6] at h
    exact h
  have v7 : T 7 1 = 357 := by
    have h := (sh1 6).2
    norm_num [u6, v6] at h
    exact h
  have u8 : T 8 0 = 1107 := by
    have h := (sh1 7).1
    norm_num [u7, v7] at h
    exact h
  have v8 : T 8 1 = 1016 := by
    have h := (sh1 7).2
    norm_num [u7, v7] at h
    exact h
  have u9 : T 9 0 = 3139 := by
    have h := (sh1 8).1
    norm_num [u8, v8] at h
    exact h
  have v9 : T 9 1 = 2907 := by
    have h := (sh1 8).2
    norm_num [u8, v8] at h
    exact h
  have u10 : T 10 0 = 8953 := by
    have h := (sh1 9).1
    norm_num [u9, v9] at h
    exact h
  have v10 : T 10 1 = 8350 := by
    have h := (sh1 9).2
    norm_num [u9, v9] at h
    exact h
  have u11 : T 11 0 = 25653 := by
    have h := (sh1 10).1
    norm_num [u10, v10] at h
    exact h
  have v11 : T 11 1 = 24068 := by
    have h := (sh1 10).2
    norm_num [u10, v10] at h
    exact h
  have u12 : T 12 0 = 73789 := by
    have h := (sh1 11).1
    norm_num [u11, v11] at h
    exact h
  have v12 : T 12 1 = 69576 := by
    have h := (sh1 11).2
    norm_num [u11, v11] at h
    exact h
  have u13 : T 13 0 = 212941 := by
    have h := (sh1 12).1
    norm_num [u12, v12] at h
    exact h
  have v13 : T 13 1 = 201643 := by
    have h := (sh1 12).2
    norm_num [u12, v12] at h
    exact h
  have u14 : T 14 0 = 616227 := by
    have h := (sh1 13).1
    norm_num [u13, v13] at h
    exact h
  have v14 : T 14 1 = 585690 := by
    have h := (sh1 13).2
    norm_num [u13, v13] at h
    exact h
  have u15 : T 15 0 = 1787607 := by
    have h := (sh1 14).1
    norm_num [u14, v14] at h
    exact h
  have v15 : T 15 1 = 1704510 := by
    have h := (sh1 14).2
    norm_num [u14, v14] at h
    exact h
  have u16 : T 16 0 = 5196627 := by
    have h := (sh1 15).1
    norm_num [u15, v15] at h
    exact h
  have v16 : T 16 1 = 4969152 := by
    have h := (sh1 15).2
    norm_num [u15, v15] at h
    exact h
  have u17 : T 17 0 = 15134931 := by
    have h := (sh1 16).1
    norm_num [u16, v16] at h
    exact h
  have v17 : T 17 1 = 14508939 := by
    have h := (sh1 16).2
    norm_num [u16, v16] at h
    exact h
  have u18 : T 18 0 = 44152809 := by
    have h := (sh1 17).1
    norm_num [u17, v17] at h
    exact h
  have v18 : T 18 1 = 42422022 := by
    have h := (sh1 17).2
    norm_num [u17, v17] at h
    exact h
  have u19 : T 19 0 = 128996853 := by
    have h := (sh1 18).1
    norm_num [u18, v18] at h
    exact h
  have v19 : T 19 1 = 124191258 := by
    have h := (sh1 18).2
    norm_num [u18, v18] at h
    exact h
  have u20 : T 20 0 = 377379369 := by
    have h := (sh1 19).1
    norm_num [u19, v19] at h
    exact h
  have v20 : T 20 1 = 363985680 := by
    have h := (sh1 19).2
    norm_num [u19, v19] at h
    exact h
  have u21 : T 21 0 = 1105350729 := by
    have h := (sh1 20).1
    norm_num [u20, v20] at h
    exact h
  have v21 : T 21 1 = 1067892399 := by
    have h := (sh1 20).2
    norm_num [u20, v20] at h
    exact h
  have u22 : T 22 0 = 3241135527 := by
    have h := (sh1 21).1
    norm_num [u21, v21] at h
    exact h
  have v22 : T 22 1 = 3136046298 := by
    have h := (sh1 21).2
    norm_num [u21, v21] at h
    exact h
  have u23 : T 23 0 = 9513228123 := by
    have h := (sh1 22).1
    norm_num [u22, v22] at h
    exact h
  have v23 : T 23 1 = 9217554129 := by
    have h := (sh1 22).2
    norm_num [u22, v22] at h
    exact h
  have u24 : T 24 0 = 27948336381 := by
    have h := (sh1 23).1
    norm_num [u23, v23] at h
    exact h
  have v24 : T 24 1 = 27114249960 := by
    have h := (sh1 23).2
    norm_num [u23, v23] at h
    exact h
  have u25 : T 25 0 = 82176836301 := by
    have h := (sh1 24).1
    norm_num [u24, v24] at h
    exact h
  have v25 : T 25 1 = 79818194925 := by
    have h := (sh1 24).2
    norm_num [u24, v24] at h
    exact h
  have u26 : T 26 0 = 241813226151 := by
    have h := (sh1 25).1
    norm_num [u25, v25] at h
    exact h
  have v26 : T 26 1 = 235128465026 := by
    have h := (sh1 25).2
    norm_num [u25, v25] at h
    exact h
  have u27 : T 27 0 = 712070156203 := by
    have h := (sh1 26).1
    norm_num [u26, v26] at h
    exact h
  have v27 : T 27 1 = 693085098852 := by
    have h := (sh1 26).2
    norm_num [u26, v26] at h
    exact h
  have u28 : T 28 0 = 2098240353907 := by
    have h := (sh1 27).1
    norm_num [u27, v27] at h
    exact h
  have v28 : T 28 1 = 2044217638456 := by
    have h := (sh1 27).2
    norm_num [u27, v27] at h
    exact h
  have u29 : T 29 0 = 6186675630819 := by
    have h := (sh1 28).1
    norm_num [u28, v28] at h
    exact h
  have v29 : T 29 1 = 6032675068061 := by
    have h := (sh1 28).2
    norm_num [u28, v28] at h
    exact h
  have u30 : T 30 0 = 18252025766941 := by
    have h := (sh1 29).1
    norm_num [u29, v29] at h
    exact h
  have v30 : T 30 1 = 17812283544870 := by
    have h := (sh1 29).2
    norm_num [u29, v29] at h
    exact h
  have u31 : T 31 0 = 53876592856681 := by
    have h := (sh1 30).1
    norm_num [u30, v30] at h
    exact h
  have v31 : T 31 1 = 52618949607541 := by
    have h := (sh1 30).2
    norm_num [u30, v30] at h
    exact h
  have u32 : T 32 0 = 159114492071763 := by
    have h := (sh1 31).1
    norm_num [u31, v31] at h
    exact h
  have v32 : T 32 1 = 155512373644512 := by
    have h := (sh1 31).2
    norm_num [u31, v31] at h
    exact h
  have u33 : T 33 0 = 470139239360787 := by
    have h := (sh1 32).1
    norm_num [u32, v32] at h
    exact h
  have v33 : T 33 1 = 459807788441331 := by
    have h := (sh1 32).2
    norm_num [u32, v32] at h
    exact h
  have u34 : T 34 0 = 1389754816243449 := by
    have h := (sh1 33).1
    norm_num [u33, v33] at h
    exact h
  have v34 : T 34 1 = 1360083802386822 := by
    have h := (sh1 33).2
    norm_num [u33, v33] at h
    exact h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := rep 1 (by norm_num)
    rw [show 2 * 1 - 2 = 0 from rfl, ts_eq, u0, v0] at h
    have e : (a 1 : ℚ) = 8 := by
      rw [h]
      norm_num
    exact_mod_cast e
  · have h := rep 2 (by norm_num)
    rw [show 2 * 2 - 2 = 2 from rfl, ts_eq, u2, v2] at h
    have e : (a 2 : ℚ) = 148 := by
      rw [h]
      norm_num
    exact_mod_cast e
  · have h := rep 3 (by norm_num)
    rw [show 2 * 3 - 2 = 4 from rfl, ts_eq, u4, v4] at h
    have e : (a 3 : ℚ) = 1669 := by
      rw [h]
      norm_num
    exact_mod_cast e
  · have h := rep 4 (by norm_num)
    rw [show 2 * 4 - 2 = 6 from rfl, ts_eq, u6, v6] at h
    have e : (a 4 : ℚ) = 16878 := by
      rw [h]
      norm_num
    exact_mod_cast e
  · have h := rep 5 (by norm_num)
    rw [show 2 * 5 - 2 = 8 from rfl, ts_eq, u8, v8] at h
    have e : (a 5 : ℚ) = 163495 := by
      rw [h]
      norm_num
    exact_mod_cast e
  · have h := rep 6 (by norm_num)
    rw [show 2 * 6 - 2 = 10 from rfl, ts_eq, u10, v10] at h
    have e : (a 6 : ℚ) = 1549297 := by
      rw [h]
      norm_num
    exact_mod_cast e
  · have h := rep 7 (by norm_num)
    rw [show 2 * 7 - 2 = 12 from rfl, ts_eq, u12, v12] at h
    have e : (a 7 : ℚ) = 14492156 := by
      rw [h]
      norm_num
    exact_mod_cast e
  · have h := rep 8 (by norm_num)
    rw [show 2 * 8 - 2 = 14 from rfl, ts_eq, u14, v14] at h
    have e : (a 8 : ℚ) = 134429604 := by
      rw [h]
      norm_num
    exact_mod_cast e
  · have h := rep 9 (by norm_num)
    rw [show 2 * 9 - 2 = 16 from rfl, ts_eq, u16, v16] at h
    have e : (a 9 : ℚ) = 1239807015 := by
      rw [h]
      norm_num
    exact_mod_cast e
  · have h := rep 10 (by norm_num)
    rw [show 2 * 10 - 2 = 18 from rfl, ts_eq, u18, v18] at h
    have e : (a 10 : ℚ) = 11386939467 := by
      rw [h]
      norm_num
    exact_mod_cast e
  · have h := rep 11 (by norm_num)
    rw [show 2 * 11 - 2 = 20 from rfl, ts_eq, u20, v20] at h
    have e : (a 11 : ℚ) = 104257566078 := by
      rw [h]
      norm_num
    exact_mod_cast e
  · have h := rep 12 (by norm_num)
    rw [show 2 * 12 - 2 = 22 from rfl, ts_eq, u22, v22] at h
    have e : (a 12 : ℚ) = 952281922551 := by
      rw [h]
      norm_num
    exact_mod_cast e
  · have h := rep 13 (by norm_num)
    rw [show 2 * 13 - 2 = 24 from rfl, ts_eq, u24, v24] at h
    have e : (a 13 : ℚ) = 8681609266794 := by
      rw [h]
      norm_num
    exact_mod_cast e
  · have h := rep 14 (by norm_num)
    rw [show 2 * 14 - 2 = 26 from rfl, ts_eq, u26, v26] at h
    have e : (a 14 : ℚ) = 79026329849968 := by
      rw [h]
      norm_num
    exact_mod_cast e
  · have h := rep 15 (by norm_num)
    rw [show 2 * 15 - 2 = 28 from rfl, ts_eq, u28, v28] at h
    have e : (a 15 : ℚ) = 718456060049941 := by
      rw [h]
      norm_num
    exact_mod_cast e
  · have h := rep 16 (by norm_num)
    rw [show 2 * 16 - 2 = 30 from rfl, ts_eq, u30, v30] at h
    have e : (a 16 : ℚ) = 6524950672498742 := by
      rw [h]
      norm_num
    exact_mod_cast e
  · have h := rep 17 (by norm_num)
    rw [show 2 * 17 - 2 = 32 from rfl, ts_eq, u32, v32] at h
    have e : (a 17 : ℚ) = 59207190970359999 := by
      rw [h]
      norm_num
    exact_mod_cast e
  · have h := rep 18 (by norm_num)
    rw [show 2 * 18 - 2 = 34 from rfl, ts_eq, u34, v34] at h
    have e : (a 18 : ℚ) = 536844632687526915 := by
      rw [h]
      norm_num
    exact_mod_cast e

/-- Kotesovec's recurrence. -/
theorem recur : ∀ n : ℕ, 4 ≤ n →
    (n : ℤ) * (2 * (n : ℤ) - 1) * (59040 * (n : ℤ) ^ 4 - 630664 * (n : ℤ) ^ 3 + 2419338 * (n : ℤ) ^ 2 - 3925427 * (n : ℤ) + 2259783) * (a n : ℤ) =
        (2243520 * (n : ℤ) ^ 6 - 26740112 * (n : ℤ) ^ 5 + 122386084 * (n : ℤ) ^ 4 - 271040464 * (n : ℤ) ^ 3 + 300314759 * (n : ℤ) ^ 2 - 153351297 * (n : ℤ) + 26751060) * (a (n - 1) : ℤ)
          + 81 * ((n : ℤ) - 3) * (2 * (n : ℤ) - 7) * (59040 * (n : ℤ) ^ 4 - 394504 * (n : ℤ) ^ 3 + 881586 * (n : ℤ) ^ 2 - 742583 * (n : ℤ) + 182070) * (a (n - 3) : ℤ)
          - 9 * (1298880 * (n : ℤ) ^ 6 - 16413328 * (n : ℤ) ^ 5 + 81293588 * (n : ℤ) ^ 4 - 199839104 * (n : ℤ) ^ 3 + 252840847 * (n : ℤ) ^ 2 - 150974403 * (n : ℤ) + 30574530) * (a (n - 2) : ℤ) := by
  intro n hn
  have r0 := rep n (by omega)
  have r1 := rep (n - 1) (by omega)
  have r2 := rep (n - 2) (by omega)
  have r3 := rep (n - 3) (by omega)
  obtain ⟨x, hx⟩ : ∃ x, 2 * n - 2 = x + 6 := ⟨2 * n - 2 - 6, by omega⟩
  rw [hx, ts6 x] at r0
  rw [show 2 * (n - 1) - 2 = x + 4 by omega, ts4 x] at r1
  rw [show 2 * (n - 2) - 2 = x + 2 by omega, ts2 x] at r2
  rw [show 2 * (n - 3) - 2 = x by omega, ts_eq x] at r3
  have hxq : (x : ℚ) = 2 * (n : ℚ) - 8 := by
    have h := congrArg (fun m : ℕ => (m : ℚ)) hx
    push_cast [Nat.cast_sub (show 2 ≤ 2 * n by omega)] at h
    linarith
  have kq := key (x : ℚ) (T x 0) (T x 1) (by positivity)
  have p1 : (9 : ℚ) ^ n = 9 ^ (n - 3) * 9 ^ 3 := by
    rw [← pow_add, Nat.sub_add_cancel (by omega)]
  have p2 : (9 : ℚ) ^ (n - 1) = 9 ^ (n - 3) * 9 ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  have p3 : (9 : ℚ) ^ (n - 2) = 9 ^ (n - 3) * 9 ^ 1 := by
    rw [← pow_add]
    congr 1
    omega
  have goal : (n : ℚ) * (2 * (n : ℚ) - 1) * (59040 * (n : ℚ) ^ 4 - 630664 * (n : ℚ) ^ 3 + 2419338 * (n : ℚ) ^ 2 - 3925427 * (n : ℚ) + 2259783) * (a n : ℚ) =
        (2243520 * (n : ℚ) ^ 6 - 26740112 * (n : ℚ) ^ 5 + 122386084 * (n : ℚ) ^ 4 - 271040464 * (n : ℚ) ^ 3 + 300314759 * (n : ℚ) ^ 2 - 153351297 * (n : ℚ) + 26751060) * (a (n - 1) : ℚ)
          + 81 * ((n : ℚ) - 3) * (2 * (n : ℚ) - 7) * (59040 * (n : ℚ) ^ 4 - 394504 * (n : ℚ) ^ 3 + 881586 * (n : ℚ) ^ 2 - 742583 * (n : ℚ) + 182070) * (a (n - 3) : ℚ)
          - 9 * (1298880 * (n : ℚ) ^ 6 - 16413328 * (n : ℚ) ^ 5 + 81293588 * (n : ℚ) ^ 4 - 199839104 * (n : ℚ) ^ 3 + 252840847 * (n : ℚ) ^ 2 - 150974403 * (n : ℚ) + 30574530) * (a (n - 2) : ℚ) := by
    rw [r0, r1, r2, r3, p1, p2, p3]
    rw [hxq] at kq ⊢
    linear_combination kq
  exact_mod_cast goal

/-- Kotesovec's asymptotic. -/
theorem asymp : Asymptotics.IsEquivalent atTop (fun n : ℕ => (a n : ℝ))
    (fun n : ℕ => 9 / 2 * (9 : ℝ) ^ n) := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  have hb : ∀ n : ℕ, 2 ≤ n →
      |(a n : ℝ) / (9 / 2 * 9 ^ n) - 1| ≤ (205 / 9) * ((T (2 * n) 0 : ℝ) / 3 ^ (2 * n)) := by
    intro n hn
    have r := rep n (by omega)
    have hT : ∀ j : ℕ, j ≤ 2 → T (2 * n - 2) j ≤ T (2 * n) 0 := by
      intro j hj
      have := T_le_top (2 * n - 2) j 2 hj
      rwa [show 2 * n - 2 + 2 = 2 * n by omega] at this
    have t0 := hT 0 (by norm_num)
    have z0 := T_nonneg (2 * n - 2) 0
    have t1 := hT 1 (by norm_num)
    have z1 := T_nonneg (2 * n - 2) 1
    have t2 := hT 2 (by norm_num)
    have z2 := T_nonneg (2 * n - 2) 2
    have hts1 : -(205 / 2) * T (2 * n) 0 ≤ ts (2 * n - 2) := by
      unfold ts
      push_cast at *
      linarith [t0, z0, t1, z1, t2, z2]
    have hts2 : ts (2 * n - 2) ≤ 0 := by
      unfold ts
      push_cast at *
      linarith [t0, z0, t1, z1, t2, z2]
    have r' := congrArg (fun q : ℚ => (q : ℝ)) r
    have hts1' := (Rat.cast_le (K := ℝ)).mpr hts1
    have hts2' := (Rat.cast_le (K := ℝ)).mpr hts2
    push_cast at r' hts1' hts2'
    have h9 : (9 : ℝ) ^ n = 3 ^ (2 * n) := by
      rw [pow_mul]
      norm_num
    have hc : (0 : ℝ) < 9 / 2 * 9 ^ n := by positivity
    have e1 : (a n : ℝ) / (9 / 2 * 9 ^ n) - 1 = (ts (2 * n - 2) : ℝ) / (9 / 2 * 9 ^ n) := by
      rw [r']
      field_simp
      ring
    rw [e1, abs_div, abs_of_pos hc, div_le_iff₀ hc, h9]
    have e2 : (205 / 9) * ((T (2 * n) 0 : ℝ) / 3 ^ (2 * n)) * (9 / 2 * 3 ^ (2 * n)) =
        (205 / 2) * (T (2 * n) 0 : ℝ) := by
      field_simp
      all_goals ring
    rw [e2, abs_le]
    constructor <;> linarith [T_nonneg (2 * n) 0]
  have hp : Tendsto (fun n : ℕ => (T (2 * n) 0 : ℝ) / 3 ^ (2 * n)) atTop (𝓝 0) :=
    P_tendsto.comp (tendsto_atTop_atTop.2 fun b => ⟨b, fun m hm => by omega⟩)
  have h0 : Tendsto (fun n : ℕ => (a n : ℝ) / (9 / 2 * 9 ^ n) - 1) atTop (𝓝 0) := by
    have hp' := hp.const_mul ((205 / 9) : ℝ)
    rw [mul_zero] at hp'
    refine squeeze_zero_norm' ?_ hp'
    filter_upwards [eventually_ge_atTop 2] with n hn
    rw [Real.norm_eq_abs]
    exact hb n hn
  have h1 := h0.add_const 1
  simp only [sub_add_cancel, zero_add] at h1
  exact h1

/-- Kotesovec's conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 4 ≤ n →
      (n : ℤ) * (2 * (n : ℤ) - 1) * (59040 * (n : ℤ) ^ 4 - 630664 * (n : ℤ) ^ 3 + 2419338 * (n : ℤ) ^ 2 - 3925427 * (n : ℤ) + 2259783) * (a n : ℤ) =
          (2243520 * (n : ℤ) ^ 6 - 26740112 * (n : ℤ) ^ 5 + 122386084 * (n : ℤ) ^ 4 - 271040464 * (n : ℤ) ^ 3 + 300314759 * (n : ℤ) ^ 2 - 153351297 * (n : ℤ) + 26751060) * (a (n - 1) : ℤ)
            + 81 * ((n : ℤ) - 3) * (2 * (n : ℤ) - 7) * (59040 * (n : ℤ) ^ 4 - 394504 * (n : ℤ) ^ 3 + 881586 * (n : ℤ) ^ 2 - 742583 * (n : ℤ) + 182070) * (a (n - 3) : ℤ)
            - 9 * (1298880 * (n : ℤ) ^ 6 - 16413328 * (n : ℤ) ^ 5 + 81293588 * (n : ℤ) ^ 4 - 199839104 * (n : ℤ) ^ 3 + 252840847 * (n : ℤ) ^ 2 - 150974403 * (n : ℤ) + 30574530) * (a (n - 2) : ℤ)) ∧
    Asymptotics.IsEquivalent Filter.atTop (fun n : ℕ => (a n : ℝ))
      (fun n : ℕ => 9 / 2 * (9 : ℝ) ^ n) :=
  ⟨recur, asymp⟩

end OMA.S_oeis_a212732

theorem OMA.solution : type_of% @OMA.S_oeis_a212732.main :=
  OMA.S_oeis_a212732.conjecture

import OMAStatements.S_oeis_a202753

namespace OMA.S_oeis_a202753

open PowerSeries Finset



/-- The row with increment vector s: 0, s 0, s 0 + s 1, ... . -/
def pre (s : Fin 4 → Fin 2) : Fin 5 → ℕ :=
  ![0, (s 0).val, (s 0).val + (s 1).val, (s 0).val + (s 1).val + (s 2).val,
    (s 0).val + (s 1).val + (s 2).val + (s 3).val]

/-- Row pre s' may follow row pre s: every column steps by 0 or 1. -/
def stp (s s' : Fin 4 → Fin 2) : Prop := ∀ j, pre s' j = pre s j ∨ pre s' j = pre s j + 1

instance (s s' : Fin 4 → Fin 2) : Decidable (stp s s') := by unfold stp; infer_instance

/-- The array whose rows have the increment vectors B. -/
def enc {n : ℕ} (B : Fin n → Fin 4 → Fin 2) : Fin n → Fin 5 → ℕ := fun i j => pre (B i) j

/-- The increment vectors of the arrays of the family. -/
def goodB {n : ℕ} (B : Fin n → Fin 4 → Fin 2) : Prop :=
  (∀ i, i.val = 0 → B i = 0) ∧ (∀ i i', i'.val = i.val + 1 → stp (B i) (B i'))

instance {n : ℕ} : DecidablePred (@goodB n) := fun B => by unfold goodB; infer_instance

lemma pre_zero (s : Fin 4 → Fin 2) (j : Fin 5) (h : j.val = 0) : pre s j = 0 := by
  have e : j = 0 := Fin.ext h
  subst e
  rfl

lemma pre_step : ∀ (s : Fin 4 → Fin 2) (j j' : Fin 5),
    j'.val = j.val + 1 → pre s j' = pre s j ∨ pre s j' = pre s j + 1 := by
  decide

lemma pre_eq_zero : ∀ s : Fin 4 → Fin 2, (∀ j, pre s j = 0) ↔ s = 0 := by
  decide

lemma pre_inj : ∀ s s' : Fin 4 → Fin 2, (∀ j, pre s j = pre s' j) → s = s' := by
  decide

lemma good_enc {n : ℕ} (B : Fin n → Fin 4 → Fin 2) : good (enc B) ↔ goodB B := by
  unfold good goodB enc stp
  constructor
  · rintro ⟨-, h0, -, h1⟩
    exact ⟨fun i hi => (pre_eq_zero (B i)).1 (fun j => h0 i j hi), fun i i' h j => h1 i i' j h⟩
  · rintro ⟨h0, h1⟩
    refine ⟨fun i j hj => pre_zero _ j hj, fun i j hi => ?_, fun i j j' h => pre_step _ j j' h,
      fun i i' j h => h1 i i' h j⟩
    rw [h0 i hi]
    exact (pre_eq_zero 0).2 rfl j

lemma enc_inj {n : ℕ} : Function.Injective (@enc n) := by
  intro B B' h
  funext i
  exact pre_inj _ _ (fun j => congrFun (congrFun h i) j)

lemma exists_enc {n : ℕ} (f : Fin n → Fin 5 → ℕ) (hf : good f) : ∃ B, enc B = f := by
  obtain ⟨hr0, -, hr, -⟩ := hf
  refine ⟨fun i => ![if f i 1 = f i 0 then 0 else 1, if f i 2 = f i 1 then 0 else 1,
    if f i 3 = f i 2 then 0 else 1, if f i 4 = f i 3 then 0 else 1], ?_⟩
  funext i j
  have e01 := hr i 0 1 rfl
  have e12 := hr i 1 2 rfl
  have e23 := hr i 2 3 rfl
  have e34 := hr i 3 4 rfl
  have z := hr0 i 0 rfl
  fin_cases j <;> simp [enc, pre] <;> (try split_ifs) <;> (try simp) <;> omega

lemma a_eq_card (n : ℕ) : a n = ((univ : Finset (Fin n → Fin 4 → Fin 2)).filter goodB).card := by
  have e : {f : Fin n → Fin 5 → ℕ | good f} =
      enc '' ((((univ : Finset (Fin n → Fin 4 → Fin 2)).filter goodB) : Finset _) :
        Set (Fin n → Fin 4 → Fin 2)) := by
    ext f
    simp only [Set.mem_setOf_eq, Set.mem_image, Finset.coe_filter, Finset.mem_univ, true_and]
    constructor
    · intro hf
      obtain ⟨B, rfl⟩ := exists_enc f hf
      exact ⟨B, (good_enc B).1 hf, rfl⟩
    · rintro ⟨B, hB, rfl⟩
      exact (good_enc B).2 hB
  unfold a
  rw [e, Set.ncard_image_of_injective _ enc_inj, Set.ncard_coe_finset]

/-- A chain of increment vectors g, each allowed after the previous one, starting after s. -/
def V (s : Fin 4 → Fin 2) {m : ℕ} (g : Fin m → Fin 4 → Fin 2) : Prop :=
  (∀ t, t.val = 0 → stp s (g t)) ∧ (∀ t t', t'.val = t.val + 1 → stp (g t) (g t'))

instance (s : Fin 4 → Fin 2) {m : ℕ} : DecidablePred (@V s m) := fun g => by
  unfold V; infer_instance

lemma V_cons (s : Fin 4 → Fin 2) {m : ℕ} (v : Fin 4 → Fin 2) (g : Fin m → Fin 4 → Fin 2) :
    V s (Fin.cons v g : Fin (m + 1) → Fin 4 → Fin 2) ↔ stp s v ∧ V v g := by
  unfold V
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨by simpa using h0 0 rfl, fun t ht => ?_, fun t t' h => ?_⟩
    · have := h1 0 t.succ (by simp [ht])
      simpa using this
    · have := h1 t.succ t'.succ (by simp [h])
      simpa using this
  · rintro ⟨hs, h0, h1⟩
    refine ⟨fun t ht => ?_, fun t t' h => ?_⟩
    · have e : t = 0 := Fin.ext ht
      subst e
      simpa using hs
    · induction t using Fin.cases with
      | zero =>
        induction t' using Fin.cases with
        | zero => simp at h
        | succ t' => simpa using h0 t' (by simpa using h)
      | succ t =>
        induction t' using Fin.cases with
        | zero => simp at h
        | succ t' => simpa using h1 t t' (by simpa using h)

lemma goodB_cons {m : ℕ} (v : Fin 4 → Fin 2) (g : Fin m → Fin 4 → Fin 2) :
    goodB (Fin.cons v g : Fin (m + 1) → Fin 4 → Fin 2) ↔ v = 0 ∧ V v g := by
  unfold goodB V
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨by simpa using h0 0 rfl, fun t ht => ?_, fun t t' h => ?_⟩
    · have := h1 0 t.succ (by simp [ht])
      simpa using this
    · have := h1 t.succ t'.succ (by simp [h])
      simpa using this
  · rintro ⟨hv, h0, h1⟩
    refine ⟨fun t ht => ?_, fun t t' h => ?_⟩
    · have e : t = 0 := Fin.ext ht
      subst e
      simpa using hv
    · induction t using Fin.cases with
      | zero =>
        induction t' using Fin.cases with
        | zero => simp at h
        | succ t' => simpa using h0 t' (by simpa using h)
      | succ t =>
        induction t' using Fin.cases with
        | zero => simp at h
        | succ t' => simpa using h1 t t' (by simpa using h)

/-- W(m, s): the chains of m increment vectors after s. -/
def W (m : ℕ) (s : Fin 4 → Fin 2) : ℕ := ((univ : Finset (Fin m → Fin 4 → Fin 2)).filter (V s)).card

lemma W_zero (s : Fin 4 → Fin 2) : W 0 s = 1 := by
  have e : (univ : Finset (Fin 0 → Fin 4 → Fin 2)).filter (V s) = univ :=
    Finset.filter_true_of_mem (fun g _ => ⟨fun t => Fin.elim0 t, fun t => Fin.elim0 t⟩)
  rw [W, e]
  simp

lemma W_succ (m : ℕ) (s : Fin 4 → Fin 2) :
    W (m + 1) s = ∑ v : Fin 4 → Fin 2, if stp s v then W m v else 0 := by
  unfold W
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g => g 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  split_ifs with hv
  · refine Finset.card_bij' (fun g _ => Fin.tail g) (fun g' _ => Fin.cons v g') ?_ ?_ ?_ ?_
    · intro g hg
      simp only [mem_filter, mem_univ, true_and] at hg ⊢
      have e : g = Fin.cons v (Fin.tail g) := by
        rw [← hg.2]
        exact (Fin.cons_self_tail g).symm
      have h1 := hg.1
      rw [e, V_cons] at h1
      exact h1.2
    · intro g' hg'
      simp only [mem_filter, mem_univ, true_and] at hg' ⊢
      exact ⟨(V_cons s v g').2 ⟨hv, hg'⟩, by simp⟩
    · intro g hg
      simp only [mem_filter, mem_univ, true_and] at hg
      rw [← hg.2]
      exact Fin.cons_self_tail g
    · intro g' _
      simp
  · rw [Finset.card_eq_zero]
    ext g
    simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]
    intro hg h0
    have e : g = Fin.cons v (Fin.tail g) := by
      rw [← h0]
      exact (Fin.cons_self_tail g).symm
    rw [e, V_cons] at hg
    exact hv hg.1

lemma a_succ (m : ℕ) : a (m + 1) = W m 0 := by
  rw [a_eq_card]
  unfold W
  refine Finset.card_bij' (fun B _ => Fin.tail B) (fun g _ => Fin.cons 0 g) ?_ ?_ ?_ ?_
  · intro B hB
    simp only [mem_filter, mem_univ, true_and] at hB ⊢
    rw [← Fin.cons_self_tail B, goodB_cons] at hB
    rw [← hB.1]
    exact hB.2
  · intro g hg
    simp only [mem_filter, mem_univ, true_and] at hg ⊢
    exact (goodB_cons 0 g).2 ⟨rfl, hg⟩
  · intro B hB
    simp only [mem_filter, mem_univ, true_and] at hB
    have h0 := hB.1 0 rfl
    rw [← h0]
    exact Fin.cons_self_tail B
  · intro g _
    simp

lemma sum_cons {j : ℕ} (G : (Fin (j + 1) → Fin 2) → ℕ) :
    ∑ v, G v = ∑ x : Fin 2, ∑ w : Fin j → Fin 2, G (Fin.cons x w) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 2) _ _ (fun p => rfl)).symm

/-- The sum over Fin 2 written out, for cheap kernel evaluation. -/
def sum2 (g : Fin 2 → ℕ) : ℕ := g 0 + g 1

lemma sum2_eq (g : Fin 2 → ℕ) : sum2 g = ∑ x, g x := by
  unfold sum2
  rw [Fin.sum_univ_two]

/-- The sum over all vectors in {0,1}^j, entry by entry. -/
def nest : (j : ℕ) → ((Fin j → Fin 2) → ℕ) → ℕ
  | 0, F => F Fin.elim0
  | j + 1, F => sum2 fun x => nest j (fun w => F (Fin.cons x w))

lemma ssum_nest : ∀ (j : ℕ) (F : (Fin j → Fin 2) → ℕ), (∑ v, F v) = nest j F := by
  intro j
  induction j with
  | zero =>
    intro F
    rw [Fintype.sum_unique]
    exact congrArg F (Subsingleton.elim _ _)
  | succ j ih =>
    intro F
    rw [sum_cons]
    simp only [nest]
    rw [sum2_eq]
    exact Finset.sum_congr rfl (fun x _ => ih _)

lemma vec_eta (s : Fin 4 → Fin 2) : s = ![s 0, s 1, s 2, s 3] := by
  ext j
  fin_cases j <;> rfl

def T1 : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℕ :=
  ![![![![5, 7], ![8, 7]], ![![7, 8], ![7, 5]]], ![![![4, 5], ![5, 4]], ![![3, 3], ![2, 1]]]]

def T2 : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℕ :=
  ![![![![31, 46], ![51, 41]], ![![39, 40], ![29, 15]]], ![![![17, 20], ![17, 10]], ![![8, 6], ![3, 1]]]]

def T3 : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℕ :=
  ![![![![184, 254], ![254, 172]], ![![170, 145], ![88, 35]]], ![![![62, 61], ![44, 20]], ![![17, 10], ![4, 1]]]]

def T4 : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℕ :=
  ![![![![924, 1118], ![996, 565]], ![![587, 420], ![218, 70]]], ![![![184, 152], ![95, 35]], ![![31, 15], ![5, 1]]]]

def T5 : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℕ :=
  ![![![![3809, 4022], ![3217, 1555]], ![![1687, 1036], ![469, 126]]], ![![![462, 328], ![181, 56]], ![![51, 21], ![6, 1]]]]

def T6 : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℕ :=
  ![![![![13197, 12307], ![8935, 3751]], ![![4214, 2268], ![910, 210]]], ![![![1022, 637], ![315, 84]], ![![78, 28], ![7, 1]]]]

def T7 : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℕ :=
  ![![![![39675, 33134], ![22052, 8175]], ![![9444, 4530], ![1632, 330]]], ![![![2052, 1142], ![512, 120]], ![![113, 36], ![8, 1]]]]

def T8 : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℕ :=
  ![![![![106357, 80529], ![49539, 16441]], ![![19425, 8415], ![2751, 495]]], ![![![3819, 1923], ![789, 165]], ![![157, 45], ![9, 1]]]]

def T9 : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℕ :=
  ![![![![259669, 180091], ![103102, 30979]], ![![37279, 14740], ![4411, 715]]], ![![![6688, 3079], ![1165, 220]], ![![211, 55], ![10, 1]]]]

def T10 : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℕ :=
  ![![![![586829, 375958], ![201443, 55309]], ![![67573, 24596], ![6787, 1001]]], ![![![11143, 4730], ![1661, 286]], ![![276, 66], ![11, 1]]]]

set_option maxHeartbeats 4000000 in
/-- Every kernel computation in one theorem: the tables are W(1), ..., W(10), and the base
relation holds. -/
lemma check_all : ∀ b0 b1 b2 b3 : Fin 2,
    (nest 4 (fun v => if stp ![b0, b1, b2, b3] v then 1 else 0) = T1 b0 b1 b2 b3) ∧
    (nest 4 (fun v => if stp ![b0, b1, b2, b3] v then T1 (v 0) (v 1) (v 2) (v 3) else 0) = T2 b0 b1 b2 b3) ∧
    (nest 4 (fun v => if stp ![b0, b1, b2, b3] v then T2 (v 0) (v 1) (v 2) (v 3) else 0) = T3 b0 b1 b2 b3) ∧
    (nest 4 (fun v => if stp ![b0, b1, b2, b3] v then T3 (v 0) (v 1) (v 2) (v 3) else 0) = T4 b0 b1 b2 b3) ∧
    (nest 4 (fun v => if stp ![b0, b1, b2, b3] v then T4 (v 0) (v 1) (v 2) (v 3) else 0) = T5 b0 b1 b2 b3) ∧
    (nest 4 (fun v => if stp ![b0, b1, b2, b3] v then T5 (v 0) (v 1) (v 2) (v 3) else 0) = T6 b0 b1 b2 b3) ∧
    (nest 4 (fun v => if stp ![b0, b1, b2, b3] v then T6 (v 0) (v 1) (v 2) (v 3) else 0) = T7 b0 b1 b2 b3) ∧
    (nest 4 (fun v => if stp ![b0, b1, b2, b3] v then T7 (v 0) (v 1) (v 2) (v 3) else 0) = T8 b0 b1 b2 b3) ∧
    (nest 4 (fun v => if stp ![b0, b1, b2, b3] v then T8 (v 0) (v 1) (v 2) (v 3) else 0) = T9 b0 b1 b2 b3) ∧
    (nest 4 (fun v => if stp ![b0, b1, b2, b3] v then T9 (v 0) (v 1) (v 2) (v 3) else 0) = T10 b0 b1 b2 b3) ∧
    (nest 4 (fun v => if stp ![b0, b1, b2, b3] v then T10 (v 0) (v 1) (v 2) (v 3) else 0) + 11 * T1 b0 b1 b2 b3 + 165 * T3 b0 b1 b2 b3 + 462 * T5 b0 b1 b2 b3 + 330 * T7 b0 b1 b2 b3 + 55 * T9 b0 b1 b2 b3 = 1 + 55 * T2 b0 b1 b2 b3 + 330 * T4 b0 b1 b2 b3 + 462 * T6 b0 b1 b2 b3 + 165 * T8 b0 b1 b2 b3 + 11 * T10 b0 b1 b2 b3) := by
  decide +kernel

lemma W1 (s : Fin 4 → Fin 2) : W 1 s = T1 (s 0) (s 1) (s 2) (s 3) := by
  rw [W_succ]
  simp only [W_zero]
  rw [ssum_nest, vec_eta s]
  exact (check_all _ _ _ _).1

lemma W2 (s : Fin 4 → Fin 2) : W 2 s = T2 (s 0) (s 1) (s 2) (s 3) := by
  rw [W_succ]
  simp only [W1]
  rw [ssum_nest, vec_eta s]
  exact (check_all _ _ _ _).2.1

lemma W3 (s : Fin 4 → Fin 2) : W 3 s = T3 (s 0) (s 1) (s 2) (s 3) := by
  rw [W_succ]
  simp only [W2]
  rw [ssum_nest, vec_eta s]
  exact (check_all _ _ _ _).2.2.1

lemma W4 (s : Fin 4 → Fin 2) : W 4 s = T4 (s 0) (s 1) (s 2) (s 3) := by
  rw [W_succ]
  simp only [W3]
  rw [ssum_nest, vec_eta s]
  exact (check_all _ _ _ _).2.2.2.1

lemma W5 (s : Fin 4 → Fin 2) : W 5 s = T5 (s 0) (s 1) (s 2) (s 3) := by
  rw [W_succ]
  simp only [W4]
  rw [ssum_nest, vec_eta s]
  exact (check_all _ _ _ _).2.2.2.2.1

lemma W6 (s : Fin 4 → Fin 2) : W 6 s = T6 (s 0) (s 1) (s 2) (s 3) := by
  rw [W_succ]
  simp only [W5]
  rw [ssum_nest, vec_eta s]
  exact (check_all _ _ _ _).2.2.2.2.2.1

lemma W7 (s : Fin 4 → Fin 2) : W 7 s = T7 (s 0) (s 1) (s 2) (s 3) := by
  rw [W_succ]
  simp only [W6]
  rw [ssum_nest, vec_eta s]
  exact (check_all _ _ _ _).2.2.2.2.2.2.1

lemma W8 (s : Fin 4 → Fin 2) : W 8 s = T8 (s 0) (s 1) (s 2) (s 3) := by
  rw [W_succ]
  simp only [W7]
  rw [ssum_nest, vec_eta s]
  exact (check_all _ _ _ _).2.2.2.2.2.2.2.1

lemma W9 (s : Fin 4 → Fin 2) : W 9 s = T9 (s 0) (s 1) (s 2) (s 3) := by
  rw [W_succ]
  simp only [W8]
  rw [ssum_nest, vec_eta s]
  exact (check_all _ _ _ _).2.2.2.2.2.2.2.2.1

lemma W10 (s : Fin 4 → Fin 2) : W 10 s = T10 (s 0) (s 1) (s 2) (s 3) := by
  rw [W_succ]
  simp only [W9]
  rw [ssum_nest, vec_eta s]
  exact (check_all _ _ _ _).2.2.2.2.2.2.2.2.2.1

lemma W_rec (n : ℕ) (s : Fin 4 → Fin 2) :
    W (n + 11) s + 11 * W (n + 1) s + 165 * W (n + 3) s + 462 * W (n + 5) s + 330 * W (n + 7) s + 55 * W (n + 9) s = W n s + 55 * W (n + 2) s + 330 * W (n + 4) s + 462 * W (n + 6) s + 165 * W (n + 8) s + 11 * W (n + 10) s := by
  induction n generalizing s with
  | zero =>
    rw [show (0 : ℕ) + 11 = 10 + 1 from rfl, W_succ 10 s]
    simp only [W10, W1, W3, W5, W7, W9, W_zero, W2, W4, W6, W8, W10, Nat.zero_add]
    rw [ssum_nest, vec_eta s]
    exact (check_all _ _ _ _).2.2.2.2.2.2.2.2.2.2
  | succ n ih =>
    rw [W_succ (n + 11), W_succ (n + 1), W_succ (n + 3), W_succ (n + 5), W_succ (n + 7), W_succ (n + 9), W_succ n, W_succ (n + 2), W_succ (n + 4), W_succ (n + 6), W_succ (n + 8), W_succ (n + 10)]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    by_cases hv : stp s v
    · simp only [if_pos hv]
      exact ih _
    · simp [hv]

lemma a_rec (n : ℕ) : a (n + 12) + 11 * a (n + 2) + 165 * a (n + 4) + 462 * a (n + 6) + 330 * a (n + 8) + 55 * a (n + 10) = a (n + 1) + 55 * a (n + 3) + 330 * a (n + 5) + 462 * a (n + 7) + 165 * a (n + 9) + 11 * a (n + 11) := by
  rw [a_succ, a_succ, a_succ, a_succ, a_succ, a_succ, a_succ, a_succ, a_succ, a_succ, a_succ, a_succ]
  exact W_rec n 0

lemma a_1 : a 1 = 1 := by rw [a_succ, W_zero]
lemma a_2 : a 2 = 5 := by rw [a_succ, W1]; rfl
lemma a_3 : a 3 = 31 := by rw [a_succ, W2]; rfl
lemma a_4 : a 4 = 184 := by rw [a_succ, W3]; rfl
lemma a_5 : a 5 = 924 := by rw [a_succ, W4]; rfl
lemma a_6 : a 6 = 3809 := by rw [a_succ, W5]; rfl
lemma a_7 : a 7 = 13197 := by rw [a_succ, W6]; rfl
lemma a_8 : a 8 = 39675 := by rw [a_succ, W7]; rfl
lemma a_9 : a 9 = 106357 := by rw [a_succ, W8]; rfl
lemma a_10 : a 10 = 259669 := by rw [a_succ, W9]; rfl
lemma a_11 : a 11 = 586829 := by rw [a_succ, W10]; rfl

lemma a_rec_z (n : ℕ) : (a (n + 12) : ℤ) + 11 * (a (n + 2) : ℤ) + 165 * (a (n + 4) : ℤ) + 462 * (a (n + 6) : ℤ) + 330 * (a (n + 8) : ℤ) + 55 * (a (n + 10) : ℤ) = (a (n + 1) : ℤ) + 55 * (a (n + 3) : ℤ) + 330 * (a (n + 5) : ℤ) + 462 * (a (n + 7) : ℤ) + 165 * (a (n + 9) : ℤ) + 11 * (a (n + 11) : ℤ) := by
  exact_mod_cast a_rec n

/-- The recurrence of the entry, for n > 11. -/
theorem recur : ∀ n : ℕ, 11 < n → (a n : ℤ) = 11 * a (n - 1) - 55 * a (n - 2) + 165 * a (n - 3) - 330 * a (n - 4) + 462 * a (n - 5) - 462 * a (n - 6) + 330 * a (n - 7) - 165 * a (n - 8) + 55 * a (n - 9) - 11 * a (n - 10) + a (n - 11) := by
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 12 := ⟨n - 12, by omega⟩
  have h := a_rec_z j
  simp only [show j + 12 - 1 = j + 11 by omega, show j + 12 - 2 = j + 10 by omega, show j + 12 - 3 = j + 9 by omega, show j + 12 - 4 = j + 8 by omega, show j + 12 - 5 = j + 7 by omega, show j + 12 - 6 = j + 6 by omega, show j + 12 - 7 = j + 5 by omega, show j + 12 - 8 = j + 4 by omega, show j + 12 - 9 = j + 3 by omega, show j + 12 - 10 = j + 2 by omega, show j + 12 - 11 = j + 1 by omega]
  linear_combination h

/-- Barker's g.f. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - X) ^ 11 = X * (1 - 6 * X + 31 * X ^ 2 - 47 * X ^ 3 + 110 * X ^ 4 - 162 * X ^ 5 + 140 * X ^ 6 - 79 * X ^ 7 + 31 * X ^ 8 - 8 * X ^ 9 + X ^ 10) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 11 = A - A * X ^ 1 * C 11 + A * X ^ 2 * C 55 - A * X ^ 3 * C 165 + A * X ^ 4 * C 330 - A * X ^ 5 * C 462 + A * X ^ 6 * C 462 - A * X ^ 7 * C 330 + A * X ^ 8 * C 165 - A * X ^ 9 * C 55 + A * X ^ 10 * C 11 - A * X ^ 11 := by
    rw [show (C (11 : ℚ) : ℚ⟦X⟧) = 11 from map_ofNat C 11, show (C (55 : ℚ) : ℚ⟦X⟧) = 55 from map_ofNat C 55, show (C (165 : ℚ) : ℚ⟦X⟧) = 165 from map_ofNat C 165, show (C (330 : ℚ) : ℚ⟦X⟧) = 330 from map_ofNat C 330, show (C (462 : ℚ) : ℚ⟦X⟧) = 462 from map_ofNat C 462]
    ring
  have e2 : (X * (1 - 6 * X + 31 * X ^ 2 - 47 * X ^ 3 + 110 * X ^ 4 - 162 * X ^ 5 + 140 * X ^ 6 - 79 * X ^ 7 + 31 * X ^ 8 - 8 * X ^ 9 + X ^ 10) : ℚ⟦X⟧) = X ^ 1 - X ^ 2 * C 6 + X ^ 3 * C 31 - X ^ 4 * C 47 + X ^ 5 * C 110 - X ^ 6 * C 162 + X ^ 7 * C 140 - X ^ 8 * C 79 + X ^ 9 * C 31 - X ^ 10 * C 8 + X ^ 11 := by
    rw [show (C (6 : ℚ) : ℚ⟦X⟧) = 6 from map_ofNat C 6, show (C (8 : ℚ) : ℚ⟦X⟧) = 8 from map_ofNat C 8, show (C (31 : ℚ) : ℚ⟦X⟧) = 31 from map_ofNat C 31, show (C (47 : ℚ) : ℚ⟦X⟧) = 47 from map_ofNat C 47, show (C (79 : ℚ) : ℚ⟦X⟧) = 79 from map_ofNat C 79, show (C (110 : ℚ) : ℚ⟦X⟧) = 110 from map_ofNat C 110, show (C (140 : ℚ) : ℚ⟦X⟧) = 140 from map_ofNat C 140, show (C (162 : ℚ) : ℚ⟦X⟧) = 162 from map_ofNat C 162]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
  · simp
  · simp [a_1] <;> norm_num
  · simp [a_1, a_2] <;> norm_num
  · simp [a_1, a_2, a_3] <;> norm_num
  · simp [a_1, a_2, a_3, a_4] <;> norm_num
  · simp [a_1, a_2, a_3, a_4, a_5] <;> norm_num
  · simp [a_1, a_2, a_3, a_4, a_5, a_6] <;> norm_num
  · simp [a_1, a_2, a_3, a_4, a_5, a_6, a_7] <;> norm_num
  · simp [a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8] <;> norm_num
  · simp [a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9] <;> norm_num
  · simp [a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9, a_10] <;> norm_num
  · simp [a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9, a_10, a_11] <;> norm_num
  · have hz := a_rec_z (n + 0)
    have hq : (a (n + 0 + 12) : ℚ) + 11 * (a (n + 0 + 2) : ℚ) + 165 * (a (n + 0 + 4) : ℚ) + 462 * (a (n + 0 + 6) : ℚ) + 330 * (a (n + 0 + 8) : ℚ) + 55 * (a (n + 0 + 10) : ℚ) = (a (n + 0 + 1) : ℚ) + 55 * (a (n + 0 + 3) : ℚ) + 330 * (a (n + 0 + 5) : ℚ) + 462 * (a (n + 0 + 7) : ℚ) + 165 * (a (n + 0 + 9) : ℚ) + 11 * (a (n + 0 + 11) : ℚ) := by
      exact_mod_cast hz
    simp only [show n + 0 + 12 = n + 12 by omega, show n + 0 + 2 = n + 2 by omega, show n + 0 + 4 = n + 4 by omega, show n + 0 + 6 = n + 6 by omega, show n + 0 + 8 = n + 8 by omega, show n + 0 + 10 = n + 10 by omega, show n + 0 + 1 = n + 1 by omega, show n + 0 + 3 = n + 3 by omega, show n + 0 + 5 = n + 5 by omega, show n + 0 + 7 = n + 7 by omega, show n + 0 + 9 = n + 9 by omega, show n + 0 + 11 = n + 11 by omega] at hq
    simp only [if_false, if_true, show ¬ (n + 12 = 0) by omega,
      show 1 ≤ n + 12 by omega,
      show ¬ (n + 12 - 1 = 0) by omega,
      show n + 12 - 1 = n + 11 by omega,
      show ¬ (n + 11 = 0) by omega,
      show 2 ≤ n + 12 by omega,
      show ¬ (n + 12 - 2 = 0) by omega,
      show n + 12 - 2 = n + 10 by omega,
      show ¬ (n + 10 = 0) by omega,
      show 3 ≤ n + 12 by omega,
      show ¬ (n + 12 - 3 = 0) by omega,
      show n + 12 - 3 = n + 9 by omega,
      show ¬ (n + 9 = 0) by omega,
      show 4 ≤ n + 12 by omega,
      show ¬ (n + 12 - 4 = 0) by omega,
      show n + 12 - 4 = n + 8 by omega,
      show ¬ (n + 8 = 0) by omega,
      show 5 ≤ n + 12 by omega,
      show ¬ (n + 12 - 5 = 0) by omega,
      show n + 12 - 5 = n + 7 by omega,
      show ¬ (n + 7 = 0) by omega,
      show 6 ≤ n + 12 by omega,
      show ¬ (n + 12 - 6 = 0) by omega,
      show n + 12 - 6 = n + 6 by omega,
      show ¬ (n + 6 = 0) by omega,
      show 7 ≤ n + 12 by omega,
      show ¬ (n + 12 - 7 = 0) by omega,
      show n + 12 - 7 = n + 5 by omega,
      show ¬ (n + 5 = 0) by omega,
      show 8 ≤ n + 12 by omega,
      show ¬ (n + 12 - 8 = 0) by omega,
      show n + 12 - 8 = n + 4 by omega,
      show ¬ (n + 4 = 0) by omega,
      show 9 ≤ n + 12 by omega,
      show ¬ (n + 12 - 9 = 0) by omega,
      show n + 12 - 9 = n + 3 by omega,
      show ¬ (n + 3 = 0) by omega,
      show 10 ≤ n + 12 by omega,
      show ¬ (n + 12 - 10 = 0) by omega,
      show n + 12 - 10 = n + 2 by omega,
      show ¬ (n + 2 = 0) by omega,
      show 11 ≤ n + 12 by omega,
      show ¬ (n + 12 - 11 = 0) by omega,
      show n + 12 - 11 = n + 1 by omega,
      show ¬ (n + 1 = 0) by omega,
      show ¬ (n + 12 = 1) by omega,
      show ¬ (n + 12 = 2) by omega,
      show ¬ (n + 12 = 3) by omega,
      show ¬ (n + 12 = 4) by omega,
      show ¬ (n + 12 = 5) by omega,
      show ¬ (n + 12 = 6) by omega,
      show ¬ (n + 12 = 7) by omega,
      show ¬ (n + 12 = 8) by omega,
      show ¬ (n + 12 = 9) by omega,
      show ¬ (n + 12 = 10) by omega,
      show ¬ (n + 12 = 11) by omega]
    linear_combination hq

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      (1 - X) ^ 11 = X * (1 - 6 * X + 31 * X ^ 2 - 47 * X ^ 3 + 110 * X ^ 4 - 162 * X ^ 5 + 140 * X ^ 6 - 79 * X ^ 7 + 31 * X ^ 8 - 8 * X ^ 9 + X ^ 10) ∧
    ∀ n : ℕ, 11 < n → (a n : ℤ) = 11 * a (n - 1) - 55 * a (n - 2) + 165 * a (n - 3) - 330 * a (n - 4) + 462 * a (n - 5) - 462 * a (n - 6) + 330 * a (n - 7) - 165 * a (n - 8) + 55 * a (n - 9) - 11 * a (n - 10) + a (n - 11) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a202753

theorem OMA.solution : type_of% @OMA.S_oeis_a202753.main :=
  OMA.S_oeis_a202753.conjecture

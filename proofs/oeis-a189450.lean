import OMAStatements.S_oeis_a189450

open OMA.S_oeis_a189450 PowerSeries

namespace A189450Proof

-- A column letter: the move code of the element in each of the two rows.
-- Code 0 stays, 1 moves left, 2 moves right, 3 moves along the main diagonal.
abbrev L := Fin 2 → Fin 4

-- The target, in row and integer column, of an element in row r, column i with code k.
def tgt (r : Fin 2) (i : ℤ) (k : Fin 4) : Fin 2 × ℤ :=
  if k.val = 0 then (r, i) else if k.val = 1 then (r, i - 1) else if k.val = 2 then (r, i + 1)
  else if r.val = 0 then (1, i + 1) else (0, i - 1)

theorem tgt_snd (r : Fin 2) (i : ℤ) (k : Fin 4) :
    (tgt r i k).2 = i ∨ (tgt r i k).2 = i - 1 ∨ (tgt r i k).2 = i + 1 := by
  unfold tgt; split_ifs <;> simp

theorem tgt_add_one (r : Fin 2) (i : ℤ) (k : Fin 4) :
    tgt r (i + 1) k = ((tgt r i k).1, (tgt r i k).2 + 1) := by
  unfold tgt; split_ifs <;> simp

-- The number of elements of a block of columns hitting the cell q.
def hits {n : ℕ} (B : Fin n → L) (q : Fin 2 × ℤ) : ℕ :=
  ∑ i : Fin n, ∑ r : Fin 2, if tgt r (i.val : ℤ) (B i r) = q then 1 else 0

-- Hits of a single column at relative position 0.
def col0 (x : L) (q : Fin 2 × ℤ) : ℕ := ∑ r : Fin 2, if tgt r 0 (x r) = q then 1 else 0

def lft (x : L) (r : Fin 2) : ℕ := col0 x (r, -1)
def st (x : L) (r : Fin 2) : ℕ := col0 x (r, 0)
def rt (x : L) (r : Fin 2) : ℕ := col0 x (r, 1)

theorem col0_eq (x : L) (r : Fin 2) (c : ℤ) :
    col0 x (r, c) = (if c = -1 then lft x r else 0) + (if c = 0 then st x r else 0) +
      (if c = 1 then rt x r else 0) := by
  by_cases h1 : c = -1
  · subst h1; simp [lft]
  by_cases h2 : c = 0
  · subst h2; simp [st]
  by_cases h3 : c = 1
  · subst h3; simp [rt]
  rw [if_neg h1, if_neg h2, if_neg h3]
  refine Finset.sum_eq_zero fun r' _ => if_neg fun h => ?_
  have := tgt_snd r' 0 (x r')
  rw [h] at this
  simp at this
  omega

theorem hits_low {n : ℕ} (B : Fin n → L) (r : Fin 2) (c : ℤ) (hc : c < -1) :
    hits B (r, c) = 0 := by
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun r' _ => if_neg fun h => ?_
  have := tgt_snd r' (i.val : ℤ) (B i r')
  rw [h] at this
  simp at this
  omega

theorem hits_cons {n : ℕ} (x : L) (B : Fin n → L) (r : Fin 2) (c : ℤ) :
    hits (Fin.cons x B : Fin (n + 1) → L) (r, c) = col0 x (r, c) + hits B (r, c - 1) := by
  unfold hits col0
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ, Nat.cast_zero]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r' _ => ?_
  push_cast
  rw [tgt_add_one]
  congr 1
  apply propext
  simp only [Prod.ext_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩

-- Pre-hits a and b of the column before the block and of its first column.
def pre (a b : Fin 2 → ℕ) (r : Fin 2) (c : ℤ) : ℕ :=
  (if c = -1 then a r else 0) + (if c = 0 then b r else 0)

-- Every cell of the column before the block and of the block is hit exactly once, no other
-- cell is hit.
def ExtOK (a b : Fin 2 → ℕ) {n : ℕ} (B : Fin n → L) : Prop :=
  ∀ r : Fin 2, ∀ c : ℤ, pre a b r c + hits B (r, c) = if -1 ≤ c ∧ c < (n : ℤ) then 1 else 0

def rowOK (a b : Fin 2 → ℕ) (x : L) : Prop :=
  (∀ r, a r + lft x r = 1) ∧ (∀ r, b r + st x r ≤ 1) ∧ (∀ r, rt x r ≤ 1)

instance (a b : Fin 2 → ℕ) (x : L) : Decidable (rowOK a b x) := by
  unfold rowOK; infer_instance

theorem ext_cons (a b : Fin 2 → ℕ) {n : ℕ} (x : L) (B : Fin n → L) :
    ExtOK a b (Fin.cons x B : Fin (n + 1) → L) ↔
      rowOK a b x ∧ ExtOK (fun r => b r + st x r) (rt x) B := by
  unfold ExtOK rowOK
  constructor
  · intro H
    have H' : ∀ r d, pre (fun r => b r + st x r) (rt x) r d + hits B (r, d) =
        if -1 ≤ d ∧ d < (n : ℤ) then 1 else 0 := by
      intro r d
      by_cases hd : d < -1
      · rw [hits_low B r d hd]; unfold pre; beta_reduce; split_ifs <;> omega
      · have h1 := H r (d + 1)
        rw [hits_cons, col0_eq, add_sub_cancel_right] at h1
        unfold pre at h1 ⊢
        beta_reduce
        push_cast at h1
        split_ifs at h1 ⊢ <;> omega
    refine ⟨⟨fun r => ?_, fun r => ?_, fun r => ?_⟩, H'⟩
    · have h1 := H r (-1)
      rw [hits_cons, col0_eq, hits_low B r _ (by norm_num)] at h1
      unfold pre at h1
      simp at h1
      omega
    · have h1 := H' r (-1)
      unfold pre at h1
      simp at h1
      split_ifs at h1 <;> omega
    · have h1 := H' r 0
      unfold pre at h1
      simp at h1
      split_ifs at h1 <;> omega
  · rintro ⟨⟨hl, -, -⟩, H'⟩ r c
    have h1 := H' r (c - 1)
    have h2 := hl r
    rw [hits_cons, col0_eq]
    unfold pre at h1 ⊢
    beta_reduce at h1
    push_cast
    split_ifs at h1 ⊢ <;> omega

open Classical in
noncomputable def F (a b : Fin 2 → ℕ) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun B : Fin n → L => ExtOK a b B).card

theorem F_succ (a b : Fin 2 → ℕ) (n : ℕ) :
    F a b (n + 1) = ∑ x : L, if rowOK a b x then F (fun r => b r + st x r) (rt x) n else 0 := by
  classical
  rw [F, Finset.card_filter, ← (Fin.consEquiv fun _ => L).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, ext_cons]
  by_cases h : rowOK a b x
  · rw [if_pos h, F, Finset.card_filter]
    exact Finset.sum_congr rfl fun B _ => by simp [h]
  · simp [h]

def cnt : ℕ → (Fin 2 → ℕ) → (Fin 2 → ℕ) → ℕ
  | 0, a, b => if ∀ r, a r = 1 ∧ b r = 0 then 1 else 0
  | n + 1, a, b => ∑ x : L, if rowOK a b x then cnt n (fun r => b r + st x r) (rt x) else 0

theorem cnt_succ (n : ℕ) (a b : Fin 2 → ℕ) :
    cnt (n + 1) a b = ∑ x : L, if rowOK a b x then cnt n (fun r => b r + st x r) (rt x) else 0 := by
  rw [cnt]

theorem F_zero (a b : Fin 2 → ℕ) : F a b 0 = cnt 0 a b := by
  classical
  have h : ∀ B : Fin 0 → L, ExtOK a b B ↔ ∀ r, a r = 1 ∧ b r = 0 := by
    intro B
    have hz : ∀ q, hits B q = 0 := fun q => by simp [hits]
    unfold ExtOK
    simp only [hz, add_zero, Nat.cast_zero]
    constructor
    · intro H r
      have h1 := H r (-1)
      have h2 := H r 0
      unfold pre at h1 h2
      simp at h1 h2
      exact ⟨h1, h2⟩
    · intro H r c
      obtain ⟨h1, h2⟩ := H r
      unfold pre
      split_ifs <;> omega
  rw [F, cnt]
  by_cases hab : ∀ r, a r = 1 ∧ b r = 0
  · rw [if_pos hab, Finset.card_eq_one]
    refine ⟨fun i => i.elim0, ?_⟩
    ext B
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun _ => funext fun i => i.elim0, fun _ => (h B).2 hab⟩
  · rw [if_neg hab, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun B _ hB => hab ((h B).1 hB)

theorem F_eq (n : ℕ) : ∀ a b, F a b n = cnt n a b := by
  induction n with
  | zero => exact F_zero
  | succ n ih =>
    intro a b
    rw [F_succ, cnt_succ]
    simp only [ih]

def W (n : ℕ) (a b : Fin 2 → ℕ) : ℤ :=
  (cnt (n + 4) a b : ℤ) - 4 * cnt (n + 3) a b + 4 * cnt (n + 1) a b - cnt n a b

theorem W_succ (n : ℕ) (a b : Fin 2 → ℕ) :
    W (n + 1) a b = ∑ x : L, if rowOK a b x then W n (fun r => b r + st x r) (rt x) else 0 := by
  simp only [W, show n + 1 + 4 = n + 4 + 1 by ring, show n + 1 + 3 = n + 3 + 1 by ring]
  rw [cnt_succ (n + 4), cnt_succ (n + 3), cnt_succ (n + 1), cnt_succ n]
  push_cast [Nat.cast_sum, Nat.cast_ite]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : rowOK a b x
  · rw [if_pos h, if_pos h, if_pos h, if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, if_neg h, if_neg h, if_neg h]; ring

theorem W_base : ∀ a b : Fin 2 → Fin 2,
    W 0 (fun r => (a r).val) (fun r => (b r).val) = 0 := by
  decide +kernel

theorem W_zero (n : ℕ) : ∀ a b : Fin 2 → ℕ, (∀ r, a r ≤ 1) → (∀ r, b r ≤ 1) → W n a b = 0 := by
  induction n with
  | zero =>
    intro a b ha hb
    have := W_base (fun r => ⟨a r, by have := ha r; omega⟩) (fun r => ⟨b r, by have := hb r; omega⟩)
    exact this
  | succ n ih =>
    intro a b ha hb
    rw [W_succ]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases h : rowOK a b x
    · rw [if_pos h]; exact ih _ _ h.2.1 h.2.2
    · rw [if_neg h]

theorem cnt_rec (n : ℕ) : (cnt (n + 4) (fun _ => 1) 0 : ℤ) =
    4 * cnt (n + 3) (fun _ => 1) 0 - 4 * cnt (n + 1) (fun _ => 1) 0 + cnt n (fun _ => 1) 0 := by
  have := W_zero n (fun _ => 1) 0 (fun _ => le_refl 1) (fun _ => Nat.zero_le 1)
  simp only [W] at this
  linarith

theorem c0 : cnt 0 (fun _ => 1) 0 = 1 := by decide +kernel
theorem c1 : cnt 1 (fun _ => 1) 0 = 1 := by decide +kernel
theorem c2 : cnt 2 (fun _ => 1) 0 = 5 := by decide +kernel
theorem c3 : cnt 3 (fun _ => 1) 0 = 16 := by decide +kernel


-- The bridge between permutations and code arrays.
def e {n : ℕ} (p : Fin 2 × Fin n) : Fin 2 × ℤ := (p.1, (p.2.val : ℤ))

theorem e_inj {n : ℕ} {p q : Fin 2 × Fin n} (h : e p = e q) : p = q := by
  simp only [e, Prod.ext_iff, Nat.cast_inj] at h
  exact Prod.ext h.1 (Fin.ext h.2)

def g {n : ℕ} (B : Fin n → L) (p : Fin 2 × Fin n) : Fin 2 × ℤ := tgt p.1 (p.2.val : ℤ) (B p.2 p.1)

def codeOf {n : ℕ} (p q : Fin 2 × Fin n) : Fin 4 :=
  if q.1 = p.1 then (if q.2.val = p.2.val then 0 else if q.2.val + 1 = p.2.val then 1 else 2)
  else 3

theorem move_tgt {n : ℕ} (p q : Fin 2 × Fin n) (h : Step p q) :
    tgt p.1 (p.2.val : ℤ) (codeOf p q) = e q := by
  obtain ⟨r, i, hi⟩ := p
  obtain ⟨s, j, hj⟩ := q
  unfold Step at h
  simp only [Prod.mk.injEq, Fin.mk.injEq, Fin.val_mk] at h
  unfold codeOf tgt e
  simp only [Fin.val_mk]
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩
  · simp
  · have h3 : ¬ (i + 1 + 1 = i) := by omega
    have h4 : ¬ (i + 1 = i) := by omega
    simp [h3, h4]
  · have h3 : ¬ (j = j + 1) := by omega
    simp [h3]
  · fin_cases r <;> fin_cases s <;> simp at h1 ⊢
  · fin_cases r <;> fin_cases s <;> simp at h1 ⊢

theorem tgt_code {n : ℕ} (p q : Fin 2 × Fin n) (k : Fin 4) (h : tgt p.1 (p.2.val : ℤ) k = e q) :
    codeOf p q = k ∧ Step p q := by
  obtain ⟨r, i, hi⟩ := p
  obtain ⟨s, j, hj⟩ := q
  unfold Step codeOf
  unfold tgt e at h
  simp only [Prod.mk.injEq, Fin.mk.injEq, Fin.val_mk] at h ⊢
  fin_cases k <;> simp at h
  · obtain ⟨rfl, h2⟩ := h
    have h3 : i = j := by omega
    subst h3
    simp
  · obtain ⟨rfl, h2⟩ := h
    have h3 : i = j + 1 := by omega
    subst h3
    simp
  · obtain ⟨rfl, h2⟩ := h
    have h3 : j = i + 1 := by omega
    subst h3
    have h4 : ¬ (i + 1 + 1 = i) := by omega
    simp [h4]
  · fin_cases r <;> fin_cases s <;> simp at h ⊢ <;> omega

theorem hits_eq_card {n : ℕ} (B : Fin n → L) (q : Fin 2 × ℤ) :
    hits B q = (Finset.univ.filter fun p => g B p = q).card := by
  rw [Finset.card_filter, Fintype.sum_prod_type_right]
  rfl

theorem valid_iff {n : ℕ} (B : Fin n → L) : ExtOK (fun _ => 1) 0 B ↔
    ∀ q : Fin 2 × ℤ, (Finset.univ.filter fun p => g B p = q).card =
      if 0 ≤ q.2 ∧ q.2 < (n : ℤ) then 1 else 0 := by
  unfold ExtOK pre
  simp only [hits_eq_card, Pi.zero_apply]
  constructor
  · rintro H ⟨r, c⟩
    have h := H r c
    simp only [Pi.zero_apply, ite_self, add_zero] at h ⊢
    by_cases h1 : c = -1
    · subst h1
      simp only [if_true] at h
      rw [if_neg (by omega)]
      split_ifs at h <;> omega
    · rw [if_neg h1, zero_add] at h
      rw [h]
      by_cases h2 : 0 ≤ c ∧ c < (n : ℤ)
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]
  · intro H r c
    have h := H (r, c)
    simp only [Pi.zero_apply, ite_self, add_zero] at h ⊢
    rw [h]
    by_cases h1 : c = -1
    · subst h1
      rw [if_pos rfl, if_neg (by omega), if_pos (by omega)]
    · rw [if_neg h1, zero_add]
      by_cases h2 : 0 ≤ c ∧ c < (n : ℤ)
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

def toB {n : ℕ} (σ : Equiv.Perm (Fin 2 × Fin n)) : Fin n → L :=
  fun i r => codeOf (r, i) (σ (r, i))

theorem g_toB {n : ℕ} (σ : Equiv.Perm (Fin 2 × Fin n)) (h : ∀ p, Step p (σ p)) (p) :
    g (toB σ) p = e (σ p) := move_tgt p (σ p) (h p)

theorem toB_valid {n : ℕ} (σ : Equiv.Perm (Fin 2 × Fin n)) (h : ∀ p, Step p (σ p)) :
    ExtOK (fun _ => 1) 0 (toB σ) := by
  rw [valid_iff]
  intro q
  simp only [g_toB σ h]
  by_cases hq : 0 ≤ q.2 ∧ q.2 < (n : ℤ)
  · rw [if_pos hq, Finset.card_eq_one]
    let q0 : Fin 2 × Fin n := (q.1, ⟨q.2.toNat, by omega⟩)
    have he : e q0 = q := Prod.ext rfl (by show ((q.2.toNat : ℕ) : ℤ) = q.2; omega)
    refine ⟨σ.symm q0, ?_⟩
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hp
      rw [← he] at hp
      rw [← e_inj hp, Equiv.symm_apply_apply]
    · rintro rfl
      rw [Equiv.apply_symm_apply, he]
  · rw [if_neg hq, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _ hp
    apply hq
    rw [← hp]
    simp only [e]
    omega

theorem in_range {n : ℕ} (B : Fin n → L) (hB : ExtOK (fun _ => 1) 0 B) (p : Fin 2 × Fin n) :
    0 ≤ (g B p).2 ∧ (g B p).2 < (n : ℤ) := by
  have h := (valid_iff B).1 hB (g B p)
  have hp : p ∈ Finset.univ.filter fun p' => g B p' = g B p := by simp
  have := Finset.card_pos.2 ⟨p, hp⟩
  by_contra hc
  rw [if_neg hc] at h
  omega

def fB {n : ℕ} (B : Fin n → L) (p : Fin 2 × Fin n) : Fin 2 × Fin n :=
  if h : 0 ≤ (g B p).2 ∧ (g B p).2 < (n : ℤ) then ((g B p).1, ⟨(g B p).2.toNat, by omega⟩) else p

theorem e_fB {n : ℕ} (B : Fin n → L) (hB : ExtOK (fun _ => 1) 0 B) (p : Fin 2 × Fin n) :
    e (fB B p) = g B p := by
  have h := in_range B hB p
  rw [fB, dif_pos h]
  simp only [e]
  ext
  · rfl
  · simp; omega

theorem fB_inj {n : ℕ} (B : Fin n → L) (hB : ExtOK (fun _ => 1) 0 B) :
    Function.Injective (fB B) := by
  intro p p' hpp
  have hg : g B p' = g B p := by rw [← e_fB B hB, ← e_fB B hB, hpp]
  have h := (valid_iff B).1 hB (g B p)
  rw [if_pos (in_range B hB p)] at h
  exact Finset.card_le_one.1 h.le p (by simp) p' (by simp [hg])

noncomputable def permEquiv (n : ℕ) :
    {σ : Equiv.Perm (Fin 2 × Fin n) // ∀ p, Step p (σ p)} ≃ {B : Fin n → L // ExtOK (fun _ => 1) 0 B} where
  toFun σ := ⟨toB σ.1, toB_valid σ.1 σ.2⟩
  invFun B := ⟨Equiv.ofBijective (fB B.1) (Finite.injective_iff_bijective.1 (fB_inj B.1 B.2)),
    fun p => (tgt_code p _ (B.1 p.2 p.1) (e_fB B.1 B.2 p).symm).2⟩
  left_inv σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro p
    apply e_inj
    simp only [Equiv.ofBijective_apply]
    rw [e_fB _ (toB_valid σ.1 σ.2), g_toB σ.1 σ.2]
  right_inv B := by
    apply Subtype.ext
    funext i r
    exact (tgt_code (r, i) _ (B.1 i r) (e_fB B.1 B.2 (r, i)).symm).1

theorem a_eq (n : ℕ) : a n = cnt n (fun _ => 1) 0 := by
  classical
  rw [← F_eq, a, F]
  have h := Nat.card_congr (permEquiv n)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Fintype.card_subtype] at h
  convert h

theorem a_rec (n : ℕ) : (a (n + 4) : ℤ) = 4 * a (n + 3) - 4 * a (n + 1) + a n := by
  simp only [a_eq]; exact cnt_rec n

theorem a1 : a 1 = 1 := by rw [a_eq, c1]
theorem a2 : a 2 = 5 := by rw [a_eq, c2]
theorem a3 : a 3 = 16 := by rw [a_eq, c3]
theorem a4 : a 4 = 61 := by
  have e0 : a 0 = 1 := by rw [a_eq, c0]
  have h : (a 4 : ℤ) = 4 * a 3 - 4 * a 1 + a 0 := a_rec 0
  rw [a3, a1, e0] at h
  omega


theorem gf :
    mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - X) * (1 + X) * (1 - 4 * X + X ^ 2)) =
      X * (1 + X - 4 * X ^ 2 + X ^ 3) := by
  set s : PowerSeries ℚ := mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hs
  have hd : s * ((1 - X) * (1 + X) * (1 - 4 * X + X ^ 2)) =
      s - (s * C (4 : ℚ)) * X ^ 1 + (s * C (4 : ℚ)) * X ^ 3 - s * X ^ 4 := by
    simp only [pow_one, map_ofNat]
    ring
  have hn : (X * (1 + X - 4 * X ^ 2 + X ^ 3) : PowerSeries ℚ) =
      C (1 : ℚ) * X ^ 1 + C (1 : ℚ) * X ^ 2 - C (4 : ℚ) * X ^ 3 + C (1 : ℚ) * X ^ 4 := by
    simp only [pow_one, map_ofNat, map_one]
    ring
  rw [hd, hn]
  ext n
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_mul_C, coeff_C, hs, coeff_mk]
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n) with h | h | h | h | h | h
  · subst h; simp
  · subst h; norm_num [a1]
  · subst h; norm_num [a1, a2]
  · subst h; norm_num [a1, a2, a3]
  · subst h; norm_num [a1, a2, a3, a4]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have h0 := a_rec (m + 1)
    have h1 : (a (m + 1 + 4) : ℚ) = 4 * a (m + 1 + 3) - 4 * a (m + 1 + 1) + a (m + 1) := by
      exact_mod_cast h0
    simp only [show m + 5 - 1 = m + 1 + 3 by omega, show m + 5 - 3 = m + 1 + 1 by omega,
      show m + 5 - 4 = m + 1 by omega, show m + 5 = m + 1 + 4 by omega]
    simp
    linarith

noncomputable def u (n : ℕ) : ℝ := (2 - Real.sqrt 3) ^ n + (2 + Real.sqrt 3) ^ n

noncomputable def f (n : ℕ) : ℝ := (u (n + 1) + 3 + 5 * (-1) ^ n) / 12

theorem u_rec (j : ℕ) : u (j + 2) = 4 * u (j + 1) - u j := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h1 : (2 - Real.sqrt 3) ^ (j + 2) = 4 * (2 - Real.sqrt 3) ^ (j + 1) - (2 - Real.sqrt 3) ^ j := by
    rw [pow_succ, pow_succ]; linear_combination (2 - Real.sqrt 3) ^ j * hs
  have h2 : (2 + Real.sqrt 3) ^ (j + 2) = 4 * (2 + Real.sqrt 3) ^ (j + 1) - (2 + Real.sqrt 3) ^ j := by
    rw [pow_succ, pow_succ]; linear_combination (2 + Real.sqrt 3) ^ j * hs
  unfold u; rw [h1, h2]; ring

theorem f_rec (j : ℕ) : f (j + 4) = 4 * f (j + 3) - 4 * f (j + 1) + f j := by
  have h1 : u (j + 5) = 4 * u (j + 4) - u (j + 3) := u_rec (j + 3)
  have h2 : u (j + 3) = 4 * u (j + 2) - u (j + 1) := u_rec (j + 1)
  have p : ∀ k, (-1 : ℝ) ^ (j + k) = (-1) ^ j * (-1) ^ k := fun k => pow_add _ _ _
  simp only [f, show j + 4 + 1 = j + 5 from rfl, show j + 3 + 1 = j + 4 from rfl,
    show j + 1 + 1 = j + 2 from rfl, p 4, p 3, p 1]
  linear_combination (h1 - h2) / 12

theorem u1 : u 1 = 4 := by unfold u; ring
theorem u2 : u 2 = 14 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold u; linear_combination 2 * hs

theorem a_f (m : ℕ) : (a m : ℝ) = f m ∧ (a (m + 1) : ℝ) = f (m + 1) ∧
    (a (m + 2) : ℝ) = f (m + 2) ∧ (a (m + 3) : ℝ) = f (m + 3) := by
  induction m with
  | zero =>
    have h3 : u 3 = 4 * u 2 - u 1 := u_rec 1
    have h4 : u 4 = 4 * u 3 - u 2 := u_rec 2
    rw [u1, u2] at h3
    rw [u2, h3] at h4
    have e0 : a 0 = 1 := by rw [a_eq, c0]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [f, e0, a1, a2, a3, zero_add] <;>
      norm_num [u1, u2, h3, h4]
  | succ m ih =>
    obtain ⟨h0, h1, h2, h3⟩ := ih
    refine ⟨h1, h2, h3, ?_⟩
    have hr : (a (m + 4) : ℝ) = 4 * a (m + 3) - 4 * a (m + 1) + a m := by exact_mod_cast a_rec m
    rw [show m + 1 + 3 = m + 4 by ring, hr, h0, h1, h3, f_rec]

end A189450Proof

open A189450Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a189450.main := by
  refine ⟨gf, fun n _ hn => ?_, fun n _ hn => ?_⟩
  · rw [(a_f n).1, f, hn.neg_one_pow, u]; ring
  · rw [(a_f n).1, f, hn.neg_one_pow, u, add_comm 1 n]; ring

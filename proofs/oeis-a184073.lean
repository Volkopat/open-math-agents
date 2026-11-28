import OMAStatements.S_oeis_a184073
import Mathlib

namespace TMEngine2

open Finset

/-- One transfer step on weight vectors: `W f N w s = ∑ k < N, w (f s k)`. -/
def W (f : ℕ → ℕ → ℕ) (N : ℕ) (w : ℕ → ℕ) (s : ℕ) : ℕ := ∑ k ∈ range N, w (f s k)

theorem sum_sem {α : Type*} [Fintype α] {N : ℕ} (e : α ≃ Fin N)
    (sem : ∀ n : ℕ, (Fin (n + 1) → α) → ℕ) (f : ℕ → ℕ → ℕ) (ι : ℕ → ℕ)
    (h0 : ∀ x : Fin 1 → α, sem 0 x = ι (e (x 0)))
    (hs : ∀ n (x : Fin (n + 2) → α), sem (n + 1) x = f (sem n (Fin.init x)) (e (x (Fin.last _)))) :
    ∀ n (w : ℕ → ℕ), ∑ x : Fin (n + 1) → α, w (sem n x) = ∑ k ∈ range N, (W f N)^[n] w (ι k) := by
  intro n
  induction n with
  | zero =>
    intro w
    rw [← (Equiv.funUnique (Fin 1) α).symm.sum_comp]
    simp only [Function.iterate_zero, id]
    rw [← Fin.sum_univ_eq_sum_range (fun k => w (ι k)), ← e.sum_comp]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [h0]; rfl
  | succ n ih =>
    intro w
    rw [← (Fin.snocEquiv (fun _ => α)).sum_comp, Fintype.sum_prod_type_right]
    have : ∀ y : Fin (n + 1) → α, ∑ c : α, w (sem (n + 1) ((Fin.snocEquiv fun _ => α) (c, y)))
        = W f N w (sem n y) := by
      intro y
      unfold W
      rw [← Fin.sum_univ_eq_sum_range (fun k => w (f (sem n y) k)), ← e.sum_comp]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hs, show ((Fin.snocEquiv fun _ => α) (c, y)) = Fin.snoc y c from
        funext fun i => Fin.snocEquiv_apply _ _ i, Fin.init_snoc, Fin.snoc_last]
    simp_rw [this]
    rw [ih, Function.iterate_succ_apply]

/-- Packed table lookup: field `s` of width `B` bits of the number `V`. -/
def pk (B V s : ℕ) : ℕ := V / 2 ^ (B * s) % 2 ^ B

theorem list_sum_filter (l : List ℕ) (w : ℕ → ℕ) (d : ℕ) (hd : w d = 0) :
    ((l.filter (fun t => t != d)).map w).sum = (l.map w).sum := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    by_cases h : t = d
    · subst h; simp [List.filter_cons, hd, ih]
    · simp [List.filter_cons, h, ih]

theorem sum_range_list (N : ℕ) (g : ℕ → ℕ) : ∑ k ∈ range N, g k = ((List.range N).map g).sum := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]; simp

/-- The transfer step on a live state, through its list of live successors. -/
theorem W_list (f : ℕ → ℕ → ℕ) (N d : ℕ) (w : ℕ → ℕ) (hd : w d = 0) (s : ℕ) (L : List ℕ)
    (hL : ((List.range N).map (f s)).filter (fun t => t != d) = L) :
    W f N w s = (L.map w).sum := by
  unfold W
  rw [← hL, list_sum_filter _ _ _ hd, List.map_map, sum_range_list]
  rfl

theorem iter_dead (f : ℕ → ℕ → ℕ) (N d : ℕ) (hfd : ∀ k < N, f d k = d) (w : ℕ → ℕ) (hw : w d = 0) :
    ∀ j, (W f N)^[j] w d = 0 := by
  intro j
  induction j with
  | zero => exact hw
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    unfold W
    exact Finset.sum_eq_zero fun k hk => by rw [hfd k (Finset.mem_range.mp hk)]; exact ih

section
variable (f : ℕ → ℕ → ℕ) (N d : ℕ) (D : List (ℕ × List ℕ))
  (hD : ∀ p ∈ D, ((List.range N).map (f p.1)).filter (fun t => t != d) = p.2)
  (hcl : ∀ p ∈ D, ∀ t ∈ p.2, t ∈ D.map Prod.fst)
  (hfd : ∀ k < N, f d k = d)

include hD hcl hfd in
theorem iter_table (w : ℕ → ℕ) (hw : w d = 0) (T : ℕ → ℕ → ℕ) (h0 : ∀ p ∈ D, w p.1 = T 0 p.1)
    (J : ℕ) (hT : ∀ j < J, ∀ p ∈ D, (p.2.map (T j)).sum = T (j + 1) p.1) :
    ∀ j ≤ J, ∀ p ∈ D, (W f N)^[j] w p.1 = T j p.1 := by
  intro j
  induction j with
  | zero => intro _ p hp; exact h0 p hp
  | succ j ih =>
    intro hj p hp
    rw [Function.iterate_succ_apply', W_list f N d _ (iter_dead f N d hfd w hw j) p.1 p.2 (hD p hp),
      ← hT j (by omega) p hp]
    congr 1
    apply List.map_congr_left
    intro t ht
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (hcl p hp t ht)
    exact ih (by omega) q hq

/-- A nonnegative linear combination `∑ c * V (m + i) s` over a list of pairs `(c, i)`. -/
def lin (V : ℕ → ℕ → ℕ) (P : List (ℕ × ℕ)) (m s : ℕ) : ℕ := (P.map fun p => p.1 * V (m + p.2) s).sum

theorem lin_succ (w : ℕ → ℕ) (P : List (ℕ × ℕ)) (m s : ℕ) :
    lin (fun j => (W f N)^[j] w) P (m + 1) s
      = ∑ k ∈ range N, lin (fun j => (W f N)^[j] w) P m (f s k) := by
  induction P with
  | nil => simp [lin]
  | cons p P ih =>
    simp only [lin, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, Finset.sum_add_distrib, ← Finset.mul_sum,
      show m + 1 + p.2 = (m + p.2) + 1 by omega, Function.iterate_succ_apply']
    rfl

include hD hcl hfd in
theorem rec_lift (w : ℕ → ℕ) (hw : w d = 0) (P Q : List (ℕ × ℕ)) (m0 : ℕ)
    (hbase : ∀ p ∈ D, lin (fun j => (W f N)^[j] w) P m0 p.1 = lin (fun j => (W f N)^[j] w) Q m0 p.1) :
    ∀ m, m0 ≤ m → ∀ p ∈ D,
      lin (fun j => (W f N)^[j] w) P m p.1 = lin (fun j => (W f N)^[j] w) Q m p.1 := by
  have hlin0 : ∀ (P : List (ℕ × ℕ)) m, lin (fun j => (W f N)^[j] w) P m d = 0 := by
    intro P m
    unfold lin
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hx
    dsimp only
    rw [iter_dead f N d hfd w hw, mul_zero]
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact hbase
  | succ m _ ih =>
    intro p hp
    rw [lin_succ, lin_succ]
    have e1 := W_list f N d (lin (fun j => (W f N)^[j] w) P m) (hlin0 P m) p.1 p.2 (hD p hp)
    have e2 := W_list f N d (lin (fun j => (W f N)^[j] w) Q m) (hlin0 Q m) p.1 p.2 (hD p hp)
    change W f N (lin (fun j => (W f N)^[j] w) P m) p.1 = W f N (lin (fun j => (W f N)^[j] w) Q m) p.1
    rw [e1, e2]
    congr 1
    apply List.map_congr_left
    intro t ht
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (hcl p hp t ht)
    exact ih q hq
end

theorem lin_sum (V : ℕ → ℕ → ℕ) (ι : ℕ → ℕ) (N : ℕ) (P : List (ℕ × ℕ)) (m : ℕ) :
    (P.map fun p => p.1 * ∑ k ∈ range N, V (m + p.2) (ι k)).sum
      = ∑ k ∈ range N, lin V P m (ι k) := by
  induction P with
  | nil => simp [lin]
  | cons p P ih =>
    simp only [lin, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, Finset.sum_add_distrib, Finset.mul_sum]

end TMEngine2

namespace TMEngine2

theorem forall_pair_snoc {n : ℕ} (P : Fin (n + 2) → Fin (n + 2) → Prop) :
    (∀ i j : Fin (n + 2), j.val = i.val + 1 → P i j) ↔
      (∀ i j : Fin (n + 1), j.val = i.val + 1 → P i.castSucc j.castSucc) ∧
        P (Fin.last n).castSucc (Fin.last (n + 1)) := by
  constructor
  · intro H
    exact ⟨fun i j h => H _ _ (by simpa using h), H _ _ (by simp)⟩
  · rintro ⟨H, Hl⟩ i j h
    by_cases hj : j.val < n + 1
    · exact H ⟨i.val, by omega⟩ ⟨j.val, hj⟩ h
    · have hj' : j = Fin.last _ := Fin.ext (by have := j.isLt; simp; omega)
      have hi' : i = (Fin.last n).castSucc := Fin.ext (by simp; omega)
      subst hj' hi'
      exact Hl

theorem forall_triple_snoc {n : ℕ} (P : Fin (n + 2) → Fin (n + 2) → Fin (n + 2) → Prop) :
    (∀ i j l : Fin (n + 2), j.val = i.val + 1 → l.val = j.val + 1 → P i j l) ↔
      (∀ i j l : Fin (n + 1), j.val = i.val + 1 → l.val = j.val + 1 → P i.castSucc j.castSucc l.castSucc) ∧
        (∀ i j : Fin (n + 2), j.val = i.val + 1 → j.val = n → P i j (Fin.last (n + 1))) := by
  constructor
  · intro H
    refine ⟨fun i j l h1 h2 => H _ _ _ (by simpa using h1) (by simpa using h2), fun i j h1 h2 => H _ _ _ h1 ?_⟩
    simp; omega
  · rintro ⟨H, Hl⟩ i j l h1 h2
    by_cases hl : l.val < n + 1
    · exact H ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ ⟨l.val, hl⟩ h1 h2
    · have hl' : l = Fin.last _ := Fin.ext (by have := l.isLt; simp; omega)
      subst hl'
      exact Hl i j h1 (by simp at h2; omega)

end TMEngine2

namespace A184073P

open Finset TMEngine2 OMA.S_oeis_a184073

abbrev Row := (Fin 3) × (Fin 3)
abbrev Fl := Bool
abbrev St := Option (Option Row × Row × Fl)

def encR (r : Row) : ℕ := (r.1).val + 3 * (r.2).val
def encF (g : Fl) : ℕ := (g).toNat

def enc : St → ℕ
  | none => 180
  | some (none, v, g) => encR v + 90 * encF g
  | some (some u, v, g) => encR v + 9 * (1 + encR u) + 90 * encF g

def decR (k : ℕ) : Row := ((⟨k / 1 % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3), (⟨k / 3 % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3))
def decF (k : ℕ) : Fl := (decide (k / 1 % 2 = 1))

def dec (s : ℕ) : St :=
  if s < 180 then
    (if s / 9 % 10 = 0 then some (none, decR s, decF (s / 90))
     else some (some (decR (s / 9 % 10 - 1)), decR s, decF (s / 90)))
  else none

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem dec_enc : ∀ t : St, dec (enc t) = t := by decide +kernel

def vec (r : Row) : Fin 2 → (Fin 3) := ![r.1, r.2]

theorem vec_eq (c : Fin 2 → (Fin 3)) : vec (c 0, c 1) = c := by
  funext i; fin_cases i <;> rfl

def bsv (u v : Fin 2 → (Fin 3)) (j : Fin 1) : ℕ :=
  (u j.castSucc).val + (u j.succ).val + (v j.castSucc).val + (v j.succ).val

def close (p q : ℕ) : Prop := p ≤ q + 1 ∧ q ≤ p + 1

instance (p q : ℕ) : Decidable (close p q) := inferInstanceAs (Decidable (p ≤ q + 1 ∧ q ≤ p + 1))

def PairOK (u v : Fin 2 → (Fin 3)) : Prop :=
  List.ofFn u ≤ List.ofFn v ∧ ∀ j j' : Fin 1, j'.val = j.val + 1 → close (bsv u v j) (bsv u v j')

instance (u v : Fin 2 → (Fin 3)) : Decidable (PairOK u v) :=
  inferInstanceAs (Decidable (List.ofFn u ≤ List.ofFn v ∧
    ∀ j j' : Fin 1, j'.val = j.val + 1 → close (bsv u v j) (bsv u v j')))

def TriOK (u v w : Fin 2 → (Fin 3)) : Prop := ∀ j : Fin 1, close (bsv u v j) (bsv v w j)

instance (u v w : Fin 2 → (Fin 3)) : Decidable (TriOK u v w) :=
  inferInstanceAs (Decidable (∀ j : Fin 1, close (bsv u v j) (bsv v w j)))

def triP : Option Row → Row → Row → Prop
  | none, _, _ => True
  | some u, v, c => TriOK (vec u) (vec v) (vec c)

instance triPDec : ∀ p v c, Decidable (triP p v c)
  | none, _, _ => instDecidableTrue
  | some u, v, c => inferInstanceAs (Decidable (TriOK (vec u) (vec v) (vec c)))

def updC (f : Bool) (a b : (Fin 3)) : Option Bool :=
  if f = true then some true else if a = b then some false
  else if a < b then some true else none

def updAll (fl : Fl) (c : Fin 2 → (Fin 3)) : Option Fl :=
  match updC fl (c 0) (c 1) with
  | some g0 => some (g0)
  | _ => none

def step : St → Row → St
  | none, _ => none
  | some (p, v, fl), c =>
    if PairOK (vec v) (vec c) ∧ triP p v c then
      match updAll fl (vec c) with
      | some g => some (some v, c, g)
      | none => none
    else none

def start (c : Row) : St :=
  match updAll (false) (vec c) with
  | some g => some (none, c, g)
  | none => none

def f (s k : ℕ) : ℕ := enc (step (dec s) (decR k))
def ι (k : ℕ) : ℕ := enc (start (decR k))
def acc (s : ℕ) : ℕ := if s < 180 then 1 else 0

def eR (c : Fin 2 → (Fin 3)) : Fin 9 := ⟨encR (c 0, c 1), by
  show (c 0).val + 3 * (c 1).val < 9
  have := (c 0).isLt; have := (c 1).isLt
  omega⟩

theorem vec_decR_eR : ∀ c : Fin 2 → (Fin 3), vec (decR (eR c)) = c := by decide +kernel
theorem eR_vec_decR : ∀ k : Fin 9, eR (vec (decR k)) = k := by decide +kernel

def e : (Fin 2 → (Fin 3)) ≃ Fin 9 where
  toFun := eR
  invFun k := vec (decR k)
  left_inv c := vec_decR_eR c
  right_inv k := eR_vec_decR k

theorem decR_eR : ∀ c : Fin 2 → (Fin 3), decR (eR c) = (c 0, c 1) := by decide +kernel

theorem decR_e (c : Fin 2 → (Fin 3)) : decR (e c) = (c 0, c 1) := decR_eR c

/-! Lex order on lists with one more entry. -/

theorem lt_snoc (l1 l2 : List (Fin 3)) (h : l1.length = l2.length) (a b : (Fin 3)) :
    l1 ++ [a] < l2 ++ [b] ↔ l1 < l2 ∨ (l1 = l2 ∧ a < b) := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => simp [List.cons_lt_cons_iff, List.not_lt_nil]
    | cons y l2 => simp at h
  | cons x l1 ih =>
    cases l2 with
    | nil => simp at h
    | cons y l2 =>
      simp only [List.cons_append, List.cons_lt_cons_iff, List.cons.injEq]
      rw [ih l2 (by simpa using h)]
      tauto

theorem le_snoc (l1 l2 : List (Fin 3)) (h : l1.length = l2.length) (a b : (Fin 3)) :
    l1 ++ [a] ≤ l2 ++ [b] ↔ l1 < l2 ∨ (l1 = l2 ∧ a ≤ b) := by
  rw [le_iff_lt_or_eq, lt_snoc l1 l2 h, le_iff_lt_or_eq]
  constructor
  · rintro ((h1 | ⟨h1, h2⟩) | h3)
    · exact Or.inl h1
    · exact Or.inr ⟨h1, Or.inl h2⟩
    · have := List.append_inj h3 h
      exact Or.inr ⟨this.1, Or.inr (by simpa using this.2)⟩
  · rintro (h1 | ⟨h1, h2 | h2⟩)
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr ⟨h1, h2⟩)
    · exact Or.inr (by rw [h1, h2])

/-! Column properties. -/

def colL {m : ℕ} (x : Fin m → Fin 2 → (Fin 3)) (j : Fin 2) : List (Fin 3) := List.ofFn (fun i => x i j)

def CL {m : ℕ} (x : Fin m → Fin 2 → (Fin 3)) (j : Fin 1) : Prop := colL x j.castSucc < colL x j.succ
def CLE {m : ℕ} (x : Fin m → Fin 2 → (Fin 3)) (j : Fin 1) : Prop := colL x j.castSucc ≤ colL x j.succ

instance {m : ℕ} (x : Fin m → Fin 2 → (Fin 3)) (j : Fin 1) : Decidable (CL x j) :=
  inferInstanceAs (Decidable (colL x j.castSucc < colL x j.succ))

theorem bool_nle (a b : (Fin 3)) (h1 : a ≠ b) (h2 : ¬ a < b) : ¬ a ≤ b :=
  fun h => h2 (lt_of_le_of_ne h h1)

theorem colL_snoc {n : ℕ} (x : Fin (n + 2) → Fin 2 → (Fin 3)) (j : Fin 2) :
    colL x j = colL (Fin.init x) j ++ [x (Fin.last _) j] := by
  unfold colL
  rw [List.ofFn_succ', List.concat_eq_append]
  rfl

theorem CL_snoc {n : ℕ} (x : Fin (n + 2) → Fin 2 → (Fin 3)) (j : Fin 1) :
    CL x j ↔ CL (Fin.init x) j ∨ (colL (Fin.init x) j.castSucc = colL (Fin.init x) j.succ ∧
      x (Fin.last _) j.castSucc < x (Fin.last _) j.succ) := by
  unfold CL
  rw [colL_snoc, colL_snoc, lt_snoc _ _ (by simp [colL])]

theorem CLE_snoc {n : ℕ} (x : Fin (n + 2) → Fin 2 → (Fin 3)) (j : Fin 1) :
    CLE x j ↔ CL (Fin.init x) j ∨ (colL (Fin.init x) j.castSucc = colL (Fin.init x) j.succ ∧
      x (Fin.last _) j.castSucc ≤ x (Fin.last _) j.succ) := by
  unfold CLE CL
  rw [colL_snoc, colL_snoc, le_snoc _ _ (by simp [colL])]


theorem upd_snoc {n : ℕ} (x : Fin (n + 2) → Fin 2 → (Fin 3)) (j : Fin 1) (hy : CLE (Fin.init x) j) :
    updC (decide (CL (Fin.init x) j)) (x (Fin.last _) j.castSucc) (x (Fin.last _) j.succ) =
      @ite _ (CLE x j) (Classical.propDecidable _) (some (decide (CL x j))) none := by
  have hL := CL_snoc x j
  have hLE := CLE_snoc x j
  have hy' : CL (Fin.init x) j ∨ colL (Fin.init x) j.castSucc = colL (Fin.init x) j.succ := by
    unfold CLE at hy; unfold CL; exact le_iff_lt_or_eq.mp hy
  set a := x (Fin.last _) j.castSucc
  set b := x (Fin.last _) j.succ
  unfold updC
  by_cases hc : CL (Fin.init x) j
  · rw [if_pos (by simpa using hc), if_pos (hLE.mpr (Or.inl hc))]
    simp [hL.mpr (Or.inl hc)]
  · have he := hy'.resolve_left hc
    rw [if_neg (by simpa using hc)]
    by_cases hab : a = b
    · rw [if_pos hab, if_pos (hLE.mpr (Or.inr ⟨he, le_of_eq hab⟩))]
      have : ¬ CL x j := by
        rw [hL]; rintro (h | ⟨_, h⟩)
        · exact hc h
        · rw [hab] at h; exact lt_irrefl _ h
      simp [this]
    · rw [if_neg hab]
      by_cases hlt : a < b
      · have hlt' : a < b := hlt
        rw [if_pos hlt, if_pos (hLE.mpr (Or.inr ⟨he, le_of_lt hlt'⟩))]
        simp [hL.mpr (Or.inr ⟨he, hlt'⟩)]
      · rw [if_neg hlt, if_neg]
        rw [hLE]; rintro (h | ⟨_, h⟩)
        · exact hc h
        · exact bool_nle a b hab hlt h

/-! The array conditions in local form. -/

def Good' {m : ℕ} (x : Fin m → Fin 2 → (Fin 3)) : Prop :=
  (∀ i i' : Fin m, i'.val = i.val + 1 → PairOK (x i) (x i')) ∧
    (∀ i j l : Fin m, j.val = i.val + 1 → l.val = j.val + 1 → TriOK (x i) (x j) (x l)) ∧
    ∀ j : Fin 1, CLE x j

theorem CLE_init {n : ℕ} (x : Fin (n + 2) → Fin 2 → (Fin 3)) (j : Fin 1) (h : CLE x j) :
    CLE (Fin.init x) j := by
  rcases (CLE_snoc x j).mp h with h | ⟨h, _⟩
  · exact le_of_lt h
  · exact le_of_eq h

theorem Good_snoc {n : ℕ} (x : Fin (n + 2) → Fin 2 → (Fin 3)) :
    Good' x ↔ Good' (Fin.init x) ∧ PairOK (x (Fin.last n).castSucc) (x (Fin.last _)) ∧
      (∀ i j : Fin (n + 2), j.val = i.val + 1 → j.val = n → TriOK (x i) (x j) (x (Fin.last _))) ∧
      ∀ j : Fin 1, CLE x j := by
  unfold Good'
  rw [forall_pair_snoc (fun i i' => PairOK (x i) (x i')),
    forall_triple_snoc (fun i j l => TriOK (x i) (x j) (x l))]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩
    exact ⟨⟨h1, h3, fun j => CLE_init x j (h5 j)⟩, h2, h4, h5⟩
  · rintro ⟨⟨h1, h3, _⟩, h2, h4, h5⟩
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩

open Classical in
noncomputable def semS : {n : ℕ} → (Fin (n + 1) → Fin 2 → (Fin 3)) → St
  | 0, x => if Good' x then some (none, (x 0 0, x 0 1), (decide (CL x 0))) else none
  | n + 1, x =>
    if Good' x then some (some (x (Fin.last n).castSucc 0, x (Fin.last n).castSucc 1), (x (Fin.last _) 0, x (Fin.last _) 1), (decide (CL x 0)))
    else none

noncomputable def sem (n : ℕ) (x : Fin (n + 1) → Fin 2 → (Fin 3)) : ℕ := enc (semS x)

theorem match_none (o0 : Option Bool) (p : Option Row) (c : Row) (h : o0 = none) :
    (match (match o0 with
      | some g0 => some (g0)
      | _ => none) with
      | some g => some (p, c, g)
      | none => (none : St)) = none := by
  rcases h with rfl <;> (try cases o0) <;> rfl

theorem tri_vec (v c u : Fin 2 → (Fin 3)) (r : Row) (hr : vec r = u) :
    TriOK (vec r) v c ↔ TriOK u v c := by rw [hr]

theorem allCLE {m : ℕ} (x : Fin m → Fin 2 → (Fin 3)) :
    (∀ j : Fin 1, CLE x j) ↔ CLE x 0 := by
  constructor
  · intro h; exact h 0
  · intro h j; fin_cases j <;> simp_all

open Classical in
theorem semS_succ {n : ℕ} (x : Fin (n + 2) → Fin 2 → (Fin 3)) :
    semS x = step (semS (Fin.init x)) (x (Fin.last _) 0, x (Fin.last _) 1) := by
  cases n with
  | zero =>
    have hT : (∀ i j : Fin 2, j.val = i.val + 1 → j.val = 0 → TriOK (x i) (x j) (x (Fin.last _))) := by
      intro i j h1 h2; omega
    simp only [semS, step]
    by_cases hy : Good' (Fin.init x)
    · have key : Good' x ↔ PairOK (Fin.init x (Fin.last 0)) (x (Fin.last _)) ∧ CLE x 0 := by
        rw [Good_snoc, ← allCLE]; tauto
      rw [if_pos hy]
      have u0 := upd_snoc x 0 (hy.2.2 0)
      simp only [show (((0 : Fin 1).castSucc : Fin 2)) = 0 from rfl, show (((0 : Fin 1).succ : Fin 2)) = 1 from rfl] at u0
      simp only [vec_eq, triP, and_true, updAll, u0]
      split_ifs <;> simp_all <;> simp [Fin.init]
    · rw [if_neg hy, if_neg (fun h => hy ((Good_snoc x).mp h).1)]
  | succ m =>
    have hT : (∀ i j : Fin (m + 3), j.val = i.val + 1 → j.val = m + 1 → TriOK (x i) (x j) (x (Fin.last _))) ↔
        TriOK (x ⟨m, by omega⟩) (x ⟨m + 1, by omega⟩) (x (Fin.last _)) := by
      constructor
      · intro H; exact H _ _ rfl rfl
      · intro H i j h1 h2
        obtain ⟨i, hi⟩ := i
        obtain ⟨j, hj⟩ := j
        simp only at h1 h2
        subst h2
        obtain rfl : i = m := by omega
        exact H
    simp only [semS, step]
    by_cases hy : Good' (Fin.init x)
    · have key : Good' x ↔ (PairOK (Fin.init x (Fin.last (m + 1))) (x (Fin.last _)) ∧
          TriOK (Fin.init x (Fin.last m).castSucc) (Fin.init x (Fin.last (m + 1))) (x (Fin.last _))) ∧
          CLE x 0 := by
        rw [Good_snoc, ← allCLE]
        constructor
        · rintro ⟨_, h2, h3, h4⟩; exact ⟨⟨h2, hT.mp h3⟩, h4⟩
        · rintro ⟨⟨h2, h3⟩, h4⟩; exact ⟨hy, h2, hT.mpr h3, h4⟩
      rw [if_pos hy]
      have u0 := upd_snoc x 0 (hy.2.2 0)
      simp only [show (((0 : Fin 1).castSucc : Fin 2)) = 0 from rfl, show (((0 : Fin 1).succ : Fin 2)) = 1 from rfl] at u0
      simp only [vec_eq, triP, updAll, u0]
      split_ifs <;> simp_all <;> simp [Fin.init]
    · rw [if_neg hy, if_neg (fun h => hy ((Good_snoc x).mp h).1)]

theorem sem_succ (n : ℕ) (x : Fin (n + 2) → Fin 2 → (Fin 3)) :
    sem (n + 1) x = f (sem n (Fin.init x)) (e (x (Fin.last _))) := by
  unfold sem f
  rw [dec_enc, decR_e, semS_succ]

theorem singles : ∀ a b : (Fin 3), ([a] < [b] ↔ a < b) ∧ ([a] ≤ [b] ↔ a ≤ b) := by decide

theorem colL_one (x : Fin 1 → Fin 2 → (Fin 3)) (j : Fin 2) : colL x j = [x 0 j] := by
  simp [colL]

theorem upd_one (x : Fin 1 → Fin 2 → (Fin 3)) (j : Fin 1) :
    updC false (x 0 j.castSucc) (x 0 j.succ) =
      @ite _ (CLE x j) (Classical.propDecidable _) (some (decide (CL x j))) none := by
  have hL : CL x j ↔ x 0 j.castSucc < x 0 j.succ := by
    unfold CL; rw [colL_one, colL_one]; exact (singles _ _).1
  have hLE : CLE x j ↔ x 0 j.castSucc ≤ x 0 j.succ := by
    unfold CLE; rw [colL_one, colL_one]; exact (singles _ _).2
  have key : ∀ a b : (Fin 3), updC false a b =
      @ite _ (a ≤ b) (Classical.propDecidable _) (some (decide (a < b))) none := by
    intro a b; fin_cases a <;> fin_cases b <;> simp [updC]
  rw [key]
  by_cases h : x 0 j.castSucc ≤ x 0 j.succ
  · rw [if_pos h, if_pos (hLE.mpr h)]
    congr 2
    exact propext hL.symm
  · rw [if_neg h, if_neg (fun h' => h (hLE.mp h'))]

open Classical in
theorem sem_zero (x : Fin 1 → Fin 2 → (Fin 3)) : sem 0 x = ι (e (x 0)) := by
  unfold sem ι
  rw [decR_e]
  congr 1
  have hg : Good' x ↔ ∀ j : Fin 1, CLE x j := by
    unfold Good'
    constructor
    · exact fun h => h.2.2
    · intro h
      refine ⟨fun i i' hh => ?_, fun i j l h1 h2 => ?_, h⟩
      · have := i.isLt; have := i'.isLt; omega
      · have := i.isLt; have := j.isLt; omega
  have u0 := upd_one x 0
  simp only [show (((0 : Fin 1).castSucc : Fin 2)) = 0 from rfl, show (((0 : Fin 1).succ : Fin 2)) = 1 from rfl] at u0
  simp only [semS, start, updAll, vec_eq]
  rw [u0]
  by_cases hc : ∀ j : Fin 1, CLE x j
  · rw [if_pos (hg.mpr hc), if_pos (hc 0)]
  · rw [if_neg (fun h => hc (hg.mp h))]
    symm
    apply match_none
    push_neg at hc
    obtain ⟨j, hj⟩ := hc
    fin_cases j
    · rw [if_neg (by simpa using hj)]

/-! The statement's conditions in local form. -/

theorem fin_pair_iff {n : ℕ} (P : Fin (n + 1) → Fin (n + 1) → Prop) :
    (∀ i : Fin n, P i.castSucc i.succ) ↔ ∀ i i' : Fin (n + 1), i'.val = i.val + 1 → P i i' := by
  constructor
  · intro H i i' h
    have hk : i.val < n := by have := i'.isLt; omega
    have e1 : i = (⟨i.val, hk⟩ : Fin n).castSucc := Fin.ext rfl
    have e2 : i' = (⟨i.val, hk⟩ : Fin n).succ := Fin.ext (by simp; omega)
    rw [e1, e2]; exact H _
  · intro H i; exact H _ _ (by simp)

theorem fin_triple_iff {n : ℕ} (Q : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Prop) :
    (∀ i i' : Fin n, i'.val = i.val + 1 → Q i.castSucc i.succ i'.succ) ↔
      ∀ a b c : Fin (n + 1), b.val = a.val + 1 → c.val = b.val + 1 → Q a b c := by
  constructor
  · intro H a b c h1 h2
    have hk : a.val < n := by have := c.isLt; omega
    have hk' : b.val < n := by have := c.isLt; omega
    have e1 : a = (⟨a.val, hk⟩ : Fin n).castSucc := Fin.ext rfl
    have e2 : b = (⟨a.val, hk⟩ : Fin n).succ := Fin.ext (by simp; omega)
    have e3 : c = (⟨b.val, hk'⟩ : Fin n).succ := Fin.ext (by simp; omega)
    rw [e1, e2, e3]; exact H _ _ (by simp; omega)
  · intro H i i' h; exact H _ _ _ (by simp) (by simp; omega)

theorem valid_iff {n : ℕ} (A : Fin (n + 1) → Fin 2 → (Fin 3)) : IsValid A ↔ Good' A := by
  have hsm : SmoothSubblocks A ↔
      (∀ i : Fin n, ∀ j j' : Fin 1, j'.val = j.val + 1 →
        close (bsv (A i.castSucc) (A i.succ) j) (bsv (A i.castSucc) (A i.succ) j')) ∧
      (∀ i i' : Fin n, i'.val = i.val + 1 → ∀ j : Fin 1,
        close (bsv (A i.castSucc) (A i.succ) j) (bsv (A i'.castSucc) (A i'.succ) j)) := by
    unfold SmoothSubblocks Neighbors
    constructor
    · intro H
      exact ⟨fun i j j' h => H (i, j) (i, j') (Or.inl ⟨rfl, h.symm⟩),
        fun i i' h j => H (i, j) (i', j) (Or.inr ⟨h.symm, rfl⟩)⟩
    · rintro ⟨Hh, Hv⟩ ⟨i, j⟩ ⟨i', j'⟩ (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · simp only at h1 h2; subst h1; exact Hh i j j' h2.symm
      · simp only at h1 h2; subst h2; exact Hv i i' h1.symm j
  have hcast : ∀ i i' : Fin n, i'.val = i.val + 1 → i'.castSucc = i.succ := fun i i' h => Fin.ext (by simp; omega)
  unfold IsValid Good' RowsNondecreasing ColsNondecreasing
  rw [hsm, ← fin_pair_iff (fun i i' => PairOK (A i) (A i')),
    ← fin_triple_iff (fun a b c => TriOK (A a) (A b) (A c))]
  unfold PairOK TriOK
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun i => ⟨h1 i, h3 i⟩, fun i i' h j => ?_, h2⟩
    have := h4 i i' h j
    rw [hcast i i' h] at this
    exact this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i => (h1 i).1, h3, fun i => (h1 i).2, fun i i' h j => ?_⟩
    rw [hcast i i' h]
    exact h2 i i' h j

theorem enc_some_lt : ∀ t : Option Row × Row × Fl, enc (some t) < 180 := by decide +kernel

open Classical in
theorem acc_sem (n : ℕ) (x : Fin (n + 1) → Fin 2 → (Fin 3)) :
    acc (sem n x) = if IsValid x then 1 else 0 := by
  unfold acc sem
  rw [propext (valid_iff x)]
  by_cases hg : Good' x
  · cases n with
    | zero => simp only [semS, hg, if_true]; rw [if_pos (enc_some_lt _)]
    | succ n => simp only [semS, hg, if_true]; rw [if_pos (enc_some_lt _)]
  · cases n with
    | zero => simp only [semS, hg, if_false]; decide
    | succ n => simp only [semS, hg, if_false]; decide

theorem a_eq (n : ℕ) : a n = ∑ k ∈ range 9, (W f 9)^[n] acc (ι k) := by
  classical
  unfold a
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    ← sum_sem e sem f ι sem_zero sem_succ n acc]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [acc_sem]
  try congr 1

/-! Kernel tables: live states with their live successors, and packed level vectors. -/

def B : ℕ := 18

def T : ℕ → ℕ → ℕ
  | 0 => pk B 8291746752422484088839896573518128990138204401701432039976528123035862867555513263478942737351929135513563777963740727322442862443355638774320804279122776613226177764115136992715827571746379680128643968242541622332977513279560380810407540668721105605973386892713466007320407169464875440319422223967712873477776264506897902012480579284540690620938947896982779067203784680527412418927663743331709300039988301729818701064036302754662506585463222106041314726328396070633741682567897657587167856659073325267175275011224586225193967140798048311815311904153212666670865995008202064368144905006490210968192207522894384744712214148063476503366327794841437994897828763308298569276819456499857936964257349401167347930847459848238773358004704030772497638678952397339144002073192782390777351807314827770308775042675794730998216162942671486364855769786828298943994274775963637335699249266193079585500644808793575266763718975955301391051762761472648562214244179334827491084772176822273
  | 1 => pk B 8291746752422484088839896573518128990138204401701432056208379762443005009886129104315898030339860564000497775515393525641737576067753956972758689497085735580969871343748116941364119470146919804717339011599806022705054082055858453763044689270508870051448951000550942840500980541123250863192799192009603371993108760526157286509986493471662018587241030251828611016794139403745859084255181434775234616765948992365386873826960456344847143557818801523326664533155710151227215608007894746875489161883495231046602075640838555522440377256635765446140580267479481270030587416974496508390009253177770156757520500970638088608990944587270045261000208887199777504294966659121268737854066641247296561069507568709500188419148336335260713363923051332863127015464294282820514637871495903529295845279863149925479358260566068200088643959785421816315651340059002391284921840837068031958307152728124229897234504166480023266136395910089582751542968170444923244080549384288606019018958162624518
  | 2 => pk B 8291746752422484088839896573518128990138204401701432088672083041178554451529049269183541740430675300246457917406136432018539577445330886806195956892158797403199900093717496482929091541534606035150351598647883604691521507583492574634010118897303248524239606619843167185207804934722086223029489338036419025719693540151299041300464588360291294401181551205486208447082645636488685040818076888099486684500383960480472006279167041488875619283700484157249403672563343585453264020569189443463028367534732792290797658958351631692915697239225195884748876138971064047574706753973307506338279430474572006411265694626043562611442349182069893078003334283299718324540663840715209583977239973248451483260756349577082722207330409231802301041875620396917689804667974344888260169808720014827790545616653535385258350393387414087232958562798017841522492306495601694528389287318770827196893951805478359239509333061954235586545109689209022174805765103875833874789852087735277861537044536229893
  | 3 => pk B 8291746752422484088839896573518128990138204401701432126546403533023572992942737553716512997446008688227420733739196830218741306614894627840713679461056360783549335947341120823391458665367583088363866478051327681619442384351638281642992586055150430501830689478186897220664365729466535013587452350631706703499358549885648577178167332459447079608911715393591500083654394594198839624487984713322807358792002959683486438674254914544815406002166651401707621150738675596566468284668024977670227681471463495055458090079810667332605786295605574877342439982321745643635333636202951234888092385096949861718476754987661758526071884260912335403515560699113148488632657767655504302254717246024539080532420385237049687310577383010423011270396802151150881425007548733462315488700255631202971208577755679753249939001108222550183789717214085222605099170183102254758152646376062558366402078089394604783684920231622355476385645978366907316577807750747088057362865791044424248235570359173137
  | 4 => pk B 8291746752422484088839896573518128990138204401701432180652575664196998833668730175392158005440727475121282645590772241804000113330970597430105077525576091092575533241888985018957547730185875161846894958921286204954464683157172159755412284987176986658183781538684342357016247920865395285335089406889193369591786042198744117820944047984797091210428288874448902778443844174217888282010278002963317497125078152904236637009446853154235596922000186116424597350432250265798163216067262224069043621080644183210088715162111123117600914681184469687195206000579341617770468812182473790731728890029114847063263694217920335158021078451321367480146909650101141680464794818329956057819218001262835341242139250137467287646893421585395769754763379094688413861662542229492047995680238775002925005487162529104657838993670907791141533494829161952893429776488065107263052410105289112448055044301783002167035688650566549587095722254578696129762854034786364458480447240140086549104301657030696
  | 5 => pk B 8291746752422484088839896573518128990138204401701432256401216647808301073477795245134480755421682090146202790173492862165487816639975293569540026475123026967989426720405603473411597636799414600201828480549568104400644409723369919291577530815524022754753853420642817923181687513953104887538292001992183409341022830230045807094356475922074796292520665872909497134548470034821320195937131374776688775078749144477798969053718848748091600919043168580647415506906558746429750823802616936357130434552917975868345702611664042401740215856901357141759192362440729168207811110844419916517740149925502107702996397066083860328140699187745527850687659842300003377896425175132215878931511951788352831475149159295601809173593834731177252249155575327728678239733606140415006854880396527815527119238149945448243355763792085397308881132077353936583389447907088146569019713871259881066340790941017703567212082536385418140029575263584428029043514817365874578322452259185231124901884076228718
  | 6 => pk B 8291746752422484088839896573518128990138204401701432359202943696966948812140700873867485238395722962520340371781245769878346088342173719721983350568301485339593220366629398018137311895851402275343544115936241988421193456124590627765911306197211513139952683978184906573635231785105609768946401002747911096825882611772138591056629869008884245581057614054646546268157578002573849094381612585772712461809544054072788821661107078261302706132944027481990710867810819732344756378433305266771505951381438413883034332471578603300139547887868109468563706293389115424948613292686433220234444222210570761576925471998298375783475194981800955374524088640936324237501825175149910044034261335048485346407872936772554626468659847344664474321234449332798426885034438581398553152420295344341225005536061986808908845749394577910695229434183509541868542740413044522156653257003578321656757459110002262834351807296308822581532755843645209618845266513933487204108532903667960795408981863432465
  | 7 => pk B 8291746752422484088839896573518128990138204401701432494468374024782411149428215172515175445369700521461854654727989991635097719259006411012605530952694356886616884214127424540475780807612089967310381819470121140505616472838841000417396527061760879027663436383154904665095185319474919695765557136774666887980444969413847381511496637154007714231299581069983399157928777413757096376325554936282680443241717542372871703403407042650555927262885776255710582640210595820782175602084665909040848885528397747282642622449622769213055536698485848703097906475168183479318981849596268471504095434863208781646391865018266649032305682927274030654319755712538661252042481113243747366500682415663168929213609519872325137265829706103359545988954327513972226711957872762453929122891111955210402847456486855521828533924506384514541430972133264847915826658079274492797649599129405113909752764813299718660216528753802886975789907877514051739481373741448802398089301071406052486575755098063500
  | 8 => pk B 8291746752422484088839896573518128990138204401701432667608124844364157185111106252001555367350465196188904984531311307445412820431108424093307768385898063394521456917411118000422230092290282096858339648766784577000858655498004338758619929189206783784312887777186322915238755577628974097094358744336448616988494509313854184810730550631509298128899208138710463959382215202071139751525517543160675381102811797939091457770511725413690356266424069684033888915050997514216752395781946411631911229760942385378125417937644624747724317017023437604790409829364686814144085098369925932561391981076469137034471786833692591372885750369888234574490384157534062054587917104655463124683906969444528379732316705035765124247449950505087872587305572360704276508688761624605582928395641240402708500650233466169815280568972127517861903917029143876718570433327905108502756972944833533025958553638254701824390419069108653777591927047930309712447688931371154618758943176413626369629291011900852
  | 9 => pk B 8291746752422484088839896573518128990138204401701432884032813368821656018960142223250628995344867415919650809095977055835875024316328329859236928739073050267169548031323700984896540985748706161181399276709909606885476798425899544547331774946062241971631714134003273720426249252126041920554115755408980189014541301879105184662133486269910482166305606205209079116975768546374292104918209282616875491479223702338846037828437809553874770935780540849194625734737077245427242218475312355468782819628980896195355008675142255950548906386214509304943474374863005114484867241223495267260228385815762876213483208639326781649051355964816608443905373435947604433645351527264494770363289466776763662174244524382610798589928987629107333683796536031486282389746571434710017805699794240304513540751850260011054733027554689734746137434750663457633380618029117107678786640300664226033670882856152470567266313760873728150293953910542820917517536436672169896507245003977943608684706967587834
  | 10 => pk B 8291746752422484088839896573518128990138204401701433149153056811264376750746091197186400320359757609872251703428083406583042052854083704476054665620666771931796390718946883098129895106937966791730884040465607901182334979301378290182846207784285694270593480063733108583214396074903294974446390568448662526200651440647550662787552231312474264971009511931175396942916408357947590422794862350581567530497659361390861865338821849629403251543692373757340434365449138115439387026228051054755170892051765069111349948046641015945061386606506171511643733313228423012150348580065501098919387414852942288282148552889556475061684096564019069488989429200626866315257584491547932911961854895283516180862598384748473271345992925169885039513624240491593285400819425085654800210789702771570643986771487342077759277917321101800758165341727735928476487205009173081664267542766493767201501740039164992898835941449305344723335101737797582111423065494930428117542947563400202520495495661492156
  | 11 => pk B 8291746752422484088839896573518128990138204401701433468379472384801788480239721284732873333401986207264867397879795100979800652396053118717960720120309170136781444888026851188167544097049083434133849527469765072009824874946460345527282254503250048286532333559230305649659781032391814223864320507797091196931839041260732570279619512666067006392083503245480703249766263734828760773683268533078401797559299114389954557414640802843799952774294849505154293210513373792516595918984895282388456155947398574161348838393876611810885123117245695152924375396149054210383229061252581279024156580908817528263953379899681033147490198474104397719096670035325906799258933843022543385812566701760072299645636555404679483526846657772757687307632884486526761484996033138664712914787696927372616493924719923011580210545200090892730446309715673242196177142226325194576266105694141229862556349394078298230328429451743034515704218268876890441429193925742214774051366652463600682424542844431541
  | 12 => pk B 8291746752422484088839896573518128990138204401701433847122677302543360307211800596814052025478403637315657809924677659635015895503204625616470397672880645142220550755919550409487704030384611650210506698388383761271610708239507061151645475274713685235439405684411607356413365945270288508184216536653775158372771002411734562505913419256067164051471454170704596623901917510760425336876191279085422966553584581946807756729809286902923445980307582171694785637053471132227674774977235279688054149216409302919874745811038009878781067855992609087969076743755671132008934894960598690411780488791693007041822923380302028101064126576372736892212278848314660262548981486823482279416295535002791383236745554454605456165182834983273885651427585778843374411514056441700742879903981013357142538792525357529133299261033399227518274347540447608169017818028661798270382600707100013044445495242345709619695375738859225534540879217783911797032415516044543290830762455420478571715848491258002
  | 13 => pk B 8291746752422484088839896573518128990138204401701434290793288777598561331433097244353940387595860329242783079463622057806474849609160746419946222042752519803298632843055256121736574596948348042090677547050930238984898826153433008006750261430793432511437915204602408187607081369769665147363932902549691042278535850654009310409229385204790085266481408645877450926885463026297317471544866668362410555478539313078001801300305932365761046807795160617958334988148807078620948152821987310160610656390521475858935907891324156616862191136143622516147989282638700234338247993303287408568660261419509846544238328009257274616205704800694452309036766672179645542243891824074325770634369471168145638741036983900143721639981339122016815014010767076057762268143444157937593744100833470638663119703606071410992922471442980715280843287782863797167573095907952282215935471542702161299442292076011567921940777759696110558060811391666640143022590053495952650324760235621225451225606080465844
  | 14 => pk B 8291746752422484088839896573518128990138204401701434804801924023076860652674379338276542410761206712264403607661361868267124612549899954863883766428199996546462954394922436624579483056753618798429283297356684511247231908918955773518982781014939502135436978158894392541533469777441011904474502392254307414082227990956597901052658901550898020649936053064968584611805852249617270819376306366723062844894534592181523969854481197215603543229772912376666798052724871406534116741370887017024559961257763601086508397893068512283060088083057796713676090972381643134113657971330534044667211288613180700797914442145528042422459641444881188163507916620481892211565064089703036646758586403293759035627009363371946797544041901396705592584308594077307738118323291038305412743146156337149676495231250668907509956039836184142855089006370298239047314477163549498088345028173682416129092830619050059135294108643747115611994943271475211477151680974609908649640937923238493348849918375160360
  | 15 => pk B 8291746752422484088839896573518128990138204401701435394559200252087727370706414989505862085981293215598680099313582871704604714959794659751951661685987607238396922232570906728668152965850151862720865137154093937841807810312883914110904572095912395084964122374514422707119360970298849771891531873048713435262098684891256140258169124227264525694434967250656560441649065374580748433673115661230558055638411966532992038810199011378290739029928505814783808265401546865069193637366975844216574708775048369368446408793685394518927805168869387727684202989430183685789576455038395093970290540548703243462161018789548702692846352831204967177815475751937985961324880381358489367401569276613832582401818512517088564375192484563373709553954874066470285424170757772081421898733199798672621483696925512454808588797871031262788433103044660042200429969890409098880727914135829237397590129323663756234224831288291302648731280907046536055659251600884960734818511137871130109965051826896095
  | _ => fun _ => 0

def D : List (ℕ × List ℕ) := [(0, [9, 102, 13, 105, 106, 17]), (4, [49, 142, 53]), (8, [89]), (9, [9, 102]), (13, []), (17, []), (49, [49, 142]), (53, []), (89, [89]), (93, [127, 128, 129, 130, 131, 132, 133, 134]), (96, [154, 155, 157, 158, 159, 160, 161]), (97, [164, 167, 169, 170]), (102, [127, 129]), (105, [154]), (106, []), (109, [109, 110, 112]), (110, [119]), (112, [137, 139]), (113, []), (115, [164]), (119, [119, 122]), (122, [149]), (125, []), (127, [109, 110, 112]), (128, [119]), (129, [127, 128, 129, 130, 132]), (130, [137, 139]), (131, []), (132, [154, 155, 157, 159]), (133, [164]), (134, []), (137, [119, 122]), (139, [137, 139, 140, 142]), (140, [149]), (142, [164, 167, 169]), (149, [149, 152]), (152, [179]), (154, [109, 110, 112, 113, 115]), (155, [119, 122]), (157, [137, 139, 140, 142]), (158, [149]), (159, [154, 155, 157, 158, 159, 160]), (160, [164, 167, 169]), (161, []), (164, [119, 122, 125]), (167, [149, 152]), (169, [164, 167, 169, 170]), (170, [179]), (179, [179])]

def I0 : List ℕ := [0, 93, 4, 96, 97, 8]


set_option maxRecDepth 100000 in
theorem hD : ∀ p ∈ D, ((List.range 9).map (f p.1)).filter (fun t => t != 180) = p.2 := by decide +kernel

set_option maxRecDepth 100000 in
theorem hcl : ∀ p ∈ D, ∀ t ∈ p.2, t ∈ D.map Prod.fst := by decide +kernel

set_option maxRecDepth 100000 in
theorem hfd : ∀ k < 9, f 180 k = 180 := by decide +kernel

set_option maxRecDepth 100000 in
theorem hI : ((List.range 9).map ι).filter (fun t => t != 180) = I0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem hIcl : ∀ t ∈ I0, t ∈ D.map Prod.fst := by decide +kernel

theorem hacc : acc 180 = 0 := by decide

set_option maxRecDepth 100000 in
theorem hT0 : ∀ p ∈ D, acc p.1 = T 0 p.1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem hT : ∀ j < 15, ∀ p ∈ D, (p.2.map (T j)).sum = T (j + 1) p.1 := by decide +kernel

theorem V_eq : ∀ j ≤ 15, ∀ p ∈ D, (W f 9)^[j] acc p.1 = T j p.1 :=
  iter_table f 9 180 D hD hcl hfd acc hacc T hT0 15 hT

theorem sum_I0 (g : ℕ → ℕ) (hg : g 180 = 0) : ∑ k ∈ range 9, g (ι k) = (I0.map g).sum := by
  rw [sum_range_list, ← hI, list_sum_filter _ _ _ hg, List.map_map]
  rfl

theorem a_list (m : ℕ) : a m = (I0.map ((W f 9)^[m] acc)).sum := by
  rw [a_eq, sum_I0 _ (iter_dead f 9 180 hfd acc hacc m)]

theorem a_val (m : ℕ) (hm : m ≤ 15) : a m = (I0.map (T m)).sum := by
  rw [a_list]
  congr 1
  apply List.map_congr_left
  intro t ht
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (hIcl t ht)
  exact V_eq m hm q hq

theorem hv1 : a 1 = 29 := by
  rw [a_val 1 (by norm_num)]
  decide +kernel

theorem hv2 : a 2 = 58 := by
  rw [a_val 2 (by norm_num)]
  decide +kernel

theorem hv3 : a 3 = 150 := by
  rw [a_val 3 (by norm_num)]
  decide +kernel

theorem hv4 : a 4 = 335 := by
  rw [a_val 4 (by norm_num)]
  decide +kernel

theorem hv5 : a 5 = 728 := by
  rw [a_val 5 (by norm_num)]
  decide +kernel

theorem hv6 : a 6 = 1499 := by
  rw [a_val 6 (by norm_num)]
  decide +kernel

theorem hv7 : a 7 = 2968 := by
  rw [a_val 7 (by norm_num)]
  decide +kernel

theorem hv8 : a 8 = 5645 := by
  rw [a_val 8 (by norm_num)]
  decide +kernel

theorem hv9 : a 9 = 10331 := by
  rw [a_val 9 (by norm_num)]
  decide +kernel

theorem hv10 : a 10 = 18242 := by
  rw [a_val 10 (by norm_num)]
  decide +kernel

theorem hv11 : a 11 = 31173 := by
  rw [a_val 11 (by norm_num)]
  decide +kernel

theorem hv12 : a 12 = 51709 := by
  rw [a_val 12 (by norm_num)]
  decide +kernel

theorem hv13 : a 13 = 83492 := by
  rw [a_val 13 (by norm_num)]
  decide +kernel

theorem hv14 : a 14 = 131554 := by
  rw [a_val 14 (by norm_num)]
  decide +kernel

theorem hv15 : a 15 = 202727 := by
  rw [a_val 15 (by norm_num)]
  decide +kernel

def P : List (ℕ × ℕ) := [(1, 9), (36, 7), (126, 5), (84, 3), (9, 1)]
def Q : List (ℕ × ℕ) := [(9, 8), (84, 6), (126, 4), (36, 2), (1, 0)]

theorem lin_T (L : List (ℕ × ℕ)) (hL : ∀ q ∈ L, 6 + q.2 ≤ 15) (p : ℕ × List ℕ) (hp : p ∈ D) :
    lin (fun j => (W f 9)^[j] acc) L 6 p.1 = (L.map fun q => q.1 * T (6 + q.2) p.1).sum := by
  unfold lin
  congr 1
  apply List.map_congr_left
  intro q hq
  dsimp only
  rw [V_eq _ (hL q hq) p hp]

set_option maxRecDepth 100000 in
theorem base : ∀ p ∈ D, lin (fun j => (W f 9)^[j] acc) P 6 p.1 = lin (fun j => (W f 9)^[j] acc) Q 6 p.1 := by
  intro p hp
  rw [lin_T P (by decide) p hp, lin_T Q (by decide) p hp]
  revert p
  decide +kernel

theorem lin_dead (L : List (ℕ × ℕ)) (m : ℕ) : lin (fun j => (W f 9)^[j] acc) L m 180 = 0 := by
  unfold lin
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hx
  dsimp only
  rw [iter_dead f 9 180 hfd acc hacc, mul_zero]

theorem urec (m : ℕ) (hm : 6 ≤ m) :
    (P.map fun q => q.1 * a (m + q.2)).sum = (Q.map fun q => q.1 * a (m + q.2)).sum := by
  simp only [a_eq]
  rw [TMEngine2.lin_sum (fun j => (W f 9)^[j] acc) ι 9 P m, TMEngine2.lin_sum (fun j => (W f 9)^[j] acc) ι 9 Q m,
    sum_I0 _ (lin_dead P m), sum_I0 _ (lin_dead Q m)]
  congr 1
  apply List.map_congr_left
  intro t ht
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (hIcl t ht)
  exact rec_lift f 9 180 D hD hcl hfd acc hacc P Q 6 base m hm q hq


theorem urecZ (m : ℕ) (hm : 6 ≤ m) :
    (a (m + 9) : ℤ) = 9 * a (m + 8) - 36 * a (m + 7) + 84 * a (m + 6) - 126 * a (m + 5) + 126 * a (m + 4) - 84 * a (m + 3) + 36 * a (m + 2) - 9 * a (m + 1) + a (m) := by
  have hr := urec m hm
  simp only [P, Q, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_assoc, Nat.reduceAdd, add_zero] at hr
  have := congrArg (fun t : ℕ => (t : ℤ)) hr
  push_cast at this
  linarith

theorem closedZ (n : ℕ) (hn : 6 ≤ n) : 40320 * (a n : ℤ) = 1290240 - 1768560 * ((n : ℕ) : ℤ) + 1559788 * ((n : ℕ) : ℤ) ^ 2 - 343756 * ((n : ℕ) : ℤ) ^ 3 + 72569 * ((n : ℕ) : ℤ) ^ 4 - 4480 * ((n : ℕ) : ℤ) ^ 5 + 602 * ((n : ℕ) : ℤ) ^ 6 - 4 * ((n : ℕ) : ℤ) ^ 7 + ((n : ℕ) : ℤ) ^ 8 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases (show n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ 15 ≤ n by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hbig
    · rw [hv6]; norm_num
    · rw [hv7]; norm_num
    · rw [hv8]; norm_num
    · rw [hv9]; norm_num
    · rw [hv10]; norm_num
    · rw [hv11]; norm_num
    · rw [hv12]; norm_num
    · rw [hv13]; norm_num
    · rw [hv14]; norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
      rw [urecZ m (by omega)]
      have h8 := ih (m + 8) (by omega) (by omega)
      have h7 := ih (m + 7) (by omega) (by omega)
      have h6 := ih (m + 6) (by omega) (by omega)
      have h5 := ih (m + 5) (by omega) (by omega)
      have h4 := ih (m + 4) (by omega) (by omega)
      have h3 := ih (m + 3) (by omega) (by omega)
      have h2 := ih (m + 2) (by omega) (by omega)
      have h1 := ih (m + 1) (by omega) (by omega)
      have h0 := ih (m) (by omega) (by omega)
      push_cast at h0 h1 h2 h3 h4 h5 h6 h7 h8 ⊢
      linear_combination 9 * h8 - 36 * h7 + 84 * h6 - 126 * h5 + 126 * h4 - 84 * h3 + 36 * h2 - 9 * h1 + h0

end A184073P

theorem OMA.solution : type_of% @OMA.S_oeis_a184073.main := by
  open A184073P OMA.S_oeis_a184073 PowerSeries in
  refine ⟨?_, fun n hn => closedZ n (by omega), fun n hn => ?_⟩
  · set Fs := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) with hFs
    rw [show Fs * (1 - X) ^ 9 = Fs - 9 * (Fs * X ^ 1) + 36 * (Fs * X ^ 2) - 84 * (Fs * X ^ 3) + 126 * (Fs * X ^ 4) - 126 * (Fs * X ^ 5) + 84 * (Fs * X ^ 6) - 36 * (Fs * X ^ 7) + 9 * (Fs * X ^ 8) - (Fs * X ^ 9) by ring]
    rw [show (X * (29 - 203 * X + 672 * X ^ 2 - 1363 * X ^ 3 + 1895 * X ^ 4 - 1939 * X ^ 5 + 1573 * X ^ 6 - 1117 * X ^ 7 + 749 * X ^ 8 - 450 * X ^ 9 + 209 * X ^ 10 - 65 * X ^ 11 + 12 * X ^ 12 - X ^ 13) : PowerSeries ℤ) = 29 * X ^ 1 - 203 * X ^ 2 + 672 * X ^ 3 - 1363 * X ^ 4 + 1895 * X ^ 5 - 1939 * X ^ 6 + 1573 * X ^ 7 - 1117 * X ^ 8 + 749 * X ^ 9 - 450 * X ^ 10 + 209 * X ^ 11 - 65 * X ^ 12 + 12 * X ^ 13 - X ^ 14 by ring]
    rw [show (1939 : PowerSeries ℤ) = C (1939 : ℤ) from (map_ofNat C 1939).symm, show (1895 : PowerSeries ℤ) = C (1895 : ℤ) from (map_ofNat C 1895).symm, show (1573 : PowerSeries ℤ) = C (1573 : ℤ) from (map_ofNat C 1573).symm, show (1363 : PowerSeries ℤ) = C (1363 : ℤ) from (map_ofNat C 1363).symm, show (1117 : PowerSeries ℤ) = C (1117 : ℤ) from (map_ofNat C 1117).symm, show (749 : PowerSeries ℤ) = C (749 : ℤ) from (map_ofNat C 749).symm, show (672 : PowerSeries ℤ) = C (672 : ℤ) from (map_ofNat C 672).symm, show (450 : PowerSeries ℤ) = C (450 : ℤ) from (map_ofNat C 450).symm, show (209 : PowerSeries ℤ) = C (209 : ℤ) from (map_ofNat C 209).symm, show (203 : PowerSeries ℤ) = C (203 : ℤ) from (map_ofNat C 203).symm, show (126 : PowerSeries ℤ) = C (126 : ℤ) from (map_ofNat C 126).symm, show (84 : PowerSeries ℤ) = C (84 : ℤ) from (map_ofNat C 84).symm, show (65 : PowerSeries ℤ) = C (65 : ℤ) from (map_ofNat C 65).symm, show (36 : PowerSeries ℤ) = C (36 : ℤ) from (map_ofNat C 36).symm, show (29 : PowerSeries ℤ) = C (29 : ℤ) from (map_ofNat C 29).symm, show (12 : PowerSeries ℤ) = C (12 : ℤ) from (map_ofNat C 12).symm, show (9 : PowerSeries ℤ) = C (9 : ℤ) from (map_ofNat C 9).symm]
    ext n
    simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_X_pow]
    simp only [coeff_mul_X_pow', hFs, coeff_mk]
    rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ 15 ≤ n by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hbig
    · norm_num [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15]
    · norm_num [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15]
    · norm_num [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15]
    · norm_num [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15]
    · norm_num [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15]
    · norm_num [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15]
    · norm_num [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15]
    · norm_num [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15]
    · norm_num [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15]
    · norm_num [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15]
    · norm_num [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15]
    · norm_num [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15]
    · norm_num [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15]
    · norm_num [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15]
    · norm_num [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 15 := ⟨n - 15, by omega⟩
      simp only [show m + 15 ≠ 0 by omega, show 1 ≤ m + 15 by omega, show m + 15 - 1 = m + 14 by omega, show m + 14 ≠ 0 by omega, show 2 ≤ m + 15 by omega, show m + 15 - 2 = m + 13 by omega, show m + 13 ≠ 0 by omega, show 3 ≤ m + 15 by omega, show m + 15 - 3 = m + 12 by omega, show m + 12 ≠ 0 by omega, show 4 ≤ m + 15 by omega, show m + 15 - 4 = m + 11 by omega, show m + 11 ≠ 0 by omega, show 5 ≤ m + 15 by omega, show m + 15 - 5 = m + 10 by omega, show m + 10 ≠ 0 by omega, show 6 ≤ m + 15 by omega, show m + 15 - 6 = m + 9 by omega, show m + 9 ≠ 0 by omega, show 7 ≤ m + 15 by omega, show m + 15 - 7 = m + 8 by omega, show m + 8 ≠ 0 by omega, show 8 ≤ m + 15 by omega, show m + 15 - 8 = m + 7 by omega, show m + 7 ≠ 0 by omega, show 9 ≤ m + 15 by omega, show m + 15 - 9 = m + 6 by omega, show m + 6 ≠ 0 by omega, show m + 15 ≠ 1 by omega, show m + 15 ≠ 2 by omega, show m + 15 ≠ 3 by omega, show m + 15 ≠ 4 by omega, show m + 15 ≠ 5 by omega, show m + 15 ≠ 6 by omega, show m + 15 ≠ 7 by omega, show m + 15 ≠ 8 by omega, show m + 15 ≠ 9 by omega, show m + 15 ≠ 10 by omega, show m + 15 ≠ 11 by omega, show m + 15 ≠ 12 by omega, show m + 15 ≠ 13 by omega, show m + 15 ≠ 14 by omega, if_true, if_false]
      have h := urecZ (m + 6) (by omega)
      simp only [add_assoc, Nat.reduceAdd, add_zero] at h
      linarith
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
    rw [show m + 9 - 1 = m + 8 by omega, show m + 9 - 2 = m + 7 by omega, show m + 9 - 3 = m + 6 by omega, show m + 9 - 4 = m + 5 by omega, show m + 9 - 5 = m + 4 by omega, show m + 9 - 6 = m + 3 by omega, show m + 9 - 7 = m + 2 by omega, show m + 9 - 8 = m + 1 by omega, show m + 9 - 9 = m by omega]
    exact urecZ m (by omega)

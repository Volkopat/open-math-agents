import OMAStatements.S_oeis_a184064
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

namespace A184064P

open Finset TMEngine2 OMA.S_oeis_a184064

abbrev Row := Bool × Bool × Bool
abbrev Fl := Bool × Bool
abbrev St := Option (Option Row × Row × Fl)

def encR (r : Row) : ℕ := (r.1).toNat + 2 * (r.2.1).toNat + 4 * (r.2.2).toNat
def encF (g : Fl) : ℕ := (g.1).toNat + 2 * (g.2).toNat

def enc : St → ℕ
  | none => 288
  | some (none, v, g) => encR v + 72 * encF g
  | some (some u, v, g) => encR v + 8 * (1 + encR u) + 72 * encF g

def decR (k : ℕ) : Row := (decide (k / 1 % 2 = 1), decide (k / 2 % 2 = 1), decide (k / 4 % 2 = 1))
def decF (k : ℕ) : Fl := (decide (k / 1 % 2 = 1), decide (k / 2 % 2 = 1))

def dec (s : ℕ) : St :=
  if s < 288 then
    (if s / 8 % 9 = 0 then some (none, decR s, decF (s / 72))
     else some (some (decR (s / 8 % 9 - 1)), decR s, decF (s / 72)))
  else none

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem dec_enc : ∀ t : St, dec (enc t) = t := by decide +kernel

def vec (r : Row) : Fin 3 → Bool := ![r.1, r.2.1, r.2.2]

theorem vec_eq (c : Fin 3 → Bool) : vec (c 0, c 1, c 2) = c := by
  funext i; fin_cases i <;> rfl

def bsv (u v : Fin 3 → Bool) (j : Fin 2) : ℕ :=
  (u j.castSucc).toNat + (u j.succ).toNat + (v j.castSucc).toNat + (v j.succ).toNat

def close (p q : ℕ) : Prop := p ≤ q + 1 ∧ q ≤ p + 1

instance (p q : ℕ) : Decidable (close p q) := inferInstanceAs (Decidable (p ≤ q + 1 ∧ q ≤ p + 1))

def PairOK (u v : Fin 3 → Bool) : Prop :=
  List.ofFn u ≤ List.ofFn v ∧ ∀ j j' : Fin 2, j'.val = j.val + 1 → close (bsv u v j) (bsv u v j')

instance (u v : Fin 3 → Bool) : Decidable (PairOK u v) :=
  inferInstanceAs (Decidable (List.ofFn u ≤ List.ofFn v ∧
    ∀ j j' : Fin 2, j'.val = j.val + 1 → close (bsv u v j) (bsv u v j')))

def TriOK (u v w : Fin 3 → Bool) : Prop := ∀ j : Fin 2, close (bsv u v j) (bsv v w j)

instance (u v w : Fin 3 → Bool) : Decidable (TriOK u v w) :=
  inferInstanceAs (Decidable (∀ j : Fin 2, close (bsv u v j) (bsv v w j)))

def triP : Option Row → Row → Row → Prop
  | none, _, _ => True
  | some u, v, c => TriOK (vec u) (vec v) (vec c)

instance triPDec : ∀ p v c, Decidable (triP p v c)
  | none, _, _ => instDecidableTrue
  | some u, v, c => inferInstanceAs (Decidable (TriOK (vec u) (vec v) (vec c)))

def updC (f a b : Bool) : Option Bool :=
  if f = true then some true else if a = b then some false
  else if a = false ∧ b = true then some true else none

def updAll (fl : Fl) (c : Fin 3 → Bool) : Option Fl :=
  match updC fl.1 (c 0) (c 1), updC fl.2 (c 1) (c 2) with
  | some g0, some g1 => some (g0, g1)
  | _, _ => none

def step : St → Row → St
  | none, _ => none
  | some (p, v, fl), c =>
    if PairOK (vec v) (vec c) ∧ triP p v c then
      match updAll fl (vec c) with
      | some g => some (some v, c, g)
      | none => none
    else none

def start (c : Row) : St :=
  match updAll (false, false) (vec c) with
  | some g => some (none, c, g)
  | none => none

def f (s k : ℕ) : ℕ := enc (step (dec s) (decR k))
def ι (k : ℕ) : ℕ := enc (start (decR k))
def acc (s : ℕ) : ℕ := if s < 288 then 1 else 0

def eR (c : Fin 3 → Bool) : Fin 8 := ⟨encR (c 0, c 1, c 2), by
  show (c 0).toNat + 2 * (c 1).toNat + 4 * (c 2).toNat < 8
  have := Bool.toNat_le (c 0); have := Bool.toNat_le (c 1); have := Bool.toNat_le (c 2)
  omega⟩

theorem vec_decR_eR : ∀ c : Fin 3 → Bool, vec (decR (eR c)) = c := by decide +kernel
theorem eR_vec_decR : ∀ k : Fin 8, eR (vec (decR k)) = k := by decide +kernel

def e : (Fin 3 → Bool) ≃ Fin 8 where
  toFun := eR
  invFun k := vec (decR k)
  left_inv c := vec_decR_eR c
  right_inv k := eR_vec_decR k

theorem decR_eR : ∀ c : Fin 3 → Bool, decR (eR c) = (c 0, c 1, c 2) := by decide +kernel

theorem decR_e (c : Fin 3 → Bool) : decR (e c) = (c 0, c 1, c 2) := decR_eR c

/-! Lex order on lists with one more entry. -/

theorem lt_snoc (l1 l2 : List Bool) (h : l1.length = l2.length) (a b : Bool) :
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

theorem le_snoc (l1 l2 : List Bool) (h : l1.length = l2.length) (a b : Bool) :
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

def colL {m : ℕ} (x : Fin m → Fin 3 → Bool) (j : Fin 3) : List Bool := List.ofFn (fun i => x i j)

def CL {m : ℕ} (x : Fin m → Fin 3 → Bool) (j : Fin 2) : Prop := colL x j.castSucc < colL x j.succ
def CLE {m : ℕ} (x : Fin m → Fin 3 → Bool) (j : Fin 2) : Prop := colL x j.castSucc ≤ colL x j.succ

instance {m : ℕ} (x : Fin m → Fin 3 → Bool) (j : Fin 2) : Decidable (CL x j) :=
  inferInstanceAs (Decidable (colL x j.castSucc < colL x j.succ))

theorem bool_nle (a b : Bool) (h1 : a ≠ b) (h2 : ¬ (a = false ∧ b = true)) : ¬ a ≤ b := by
  revert a b; decide

theorem colL_snoc {n : ℕ} (x : Fin (n + 2) → Fin 3 → Bool) (j : Fin 3) :
    colL x j = colL (Fin.init x) j ++ [x (Fin.last _) j] := by
  unfold colL
  rw [List.ofFn_succ', List.concat_eq_append]
  rfl

theorem CL_snoc {n : ℕ} (x : Fin (n + 2) → Fin 3 → Bool) (j : Fin 2) :
    CL x j ↔ CL (Fin.init x) j ∨ (colL (Fin.init x) j.castSucc = colL (Fin.init x) j.succ ∧
      x (Fin.last _) j.castSucc < x (Fin.last _) j.succ) := by
  unfold CL
  rw [colL_snoc, colL_snoc, lt_snoc _ _ (by simp [colL])]

theorem CLE_snoc {n : ℕ} (x : Fin (n + 2) → Fin 3 → Bool) (j : Fin 2) :
    CLE x j ↔ CL (Fin.init x) j ∨ (colL (Fin.init x) j.castSucc = colL (Fin.init x) j.succ ∧
      x (Fin.last _) j.castSucc ≤ x (Fin.last _) j.succ) := by
  unfold CLE CL
  rw [colL_snoc, colL_snoc, le_snoc _ _ (by simp [colL])]

theorem bool_lt (a b : Bool) : a < b ↔ a = false ∧ b = true := by
  cases a <;> cases b <;> decide

theorem upd_snoc {n : ℕ} (x : Fin (n + 2) → Fin 3 → Bool) (j : Fin 2) (hy : CLE (Fin.init x) j) :
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
      by_cases hlt : a = false ∧ b = true
      · have hlt' : a < b := (bool_lt a b).mpr hlt
        rw [if_pos hlt, if_pos (hLE.mpr (Or.inr ⟨he, le_of_lt hlt'⟩))]
        simp [hL.mpr (Or.inr ⟨he, hlt'⟩)]
      · rw [if_neg hlt, if_neg]
        rw [hLE]; rintro (h | ⟨_, h⟩)
        · exact hc h
        · exact bool_nle a b hab hlt h

/-! The array conditions in local form. -/

def Good' {m : ℕ} (x : Fin m → Fin 3 → Bool) : Prop :=
  (∀ i i' : Fin m, i'.val = i.val + 1 → PairOK (x i) (x i')) ∧
    (∀ i j l : Fin m, j.val = i.val + 1 → l.val = j.val + 1 → TriOK (x i) (x j) (x l)) ∧
    ∀ j : Fin 2, CLE x j

theorem CLE_init {n : ℕ} (x : Fin (n + 2) → Fin 3 → Bool) (j : Fin 2) (h : CLE x j) :
    CLE (Fin.init x) j := by
  rcases (CLE_snoc x j).mp h with h | ⟨h, _⟩
  · exact le_of_lt h
  · exact le_of_eq h

theorem Good_snoc {n : ℕ} (x : Fin (n + 2) → Fin 3 → Bool) :
    Good' x ↔ Good' (Fin.init x) ∧ PairOK (x (Fin.last n).castSucc) (x (Fin.last _)) ∧
      (∀ i j : Fin (n + 2), j.val = i.val + 1 → j.val = n → TriOK (x i) (x j) (x (Fin.last _))) ∧
      ∀ j : Fin 2, CLE x j := by
  unfold Good'
  rw [forall_pair_snoc (fun i i' => PairOK (x i) (x i')),
    forall_triple_snoc (fun i j l => TriOK (x i) (x j) (x l))]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩
    exact ⟨⟨h1, h3, fun j => CLE_init x j (h5 j)⟩, h2, h4, h5⟩
  · rintro ⟨⟨h1, h3, _⟩, h2, h4, h5⟩
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩

open Classical in
noncomputable def semS : {n : ℕ} → (Fin (n + 1) → Fin 3 → Bool) → St
  | 0, x => if Good' x then some (none, (x 0 0, x 0 1, x 0 2), (decide (CL x 0), decide (CL x 1))) else none
  | n + 1, x =>
    if Good' x then some (some (x (Fin.last n).castSucc 0, x (Fin.last n).castSucc 1, x (Fin.last n).castSucc 2), (x (Fin.last _) 0, x (Fin.last _) 1, x (Fin.last _) 2), (decide (CL x 0), decide (CL x 1)))
    else none

noncomputable def sem (n : ℕ) (x : Fin (n + 1) → Fin 3 → Bool) : ℕ := enc (semS x)

theorem match_none (o0 : Option Bool) (o1 : Option Bool) (p : Option Row) (c : Row) (h : o0 = none ∨ o1 = none) :
    (match (match o0, o1 with
      | some g0, some g1 => some (g0, g1)
      | _, _ => none) with
      | some g => some (p, c, g)
      | none => (none : St)) = none := by
  rcases h with rfl | rfl <;> (try cases o0) <;> (try cases o1) <;> rfl

theorem tri_vec (v c u : Fin 3 → Bool) (r : Row) (hr : vec r = u) :
    TriOK (vec r) v c ↔ TriOK u v c := by rw [hr]

theorem allCLE {m : ℕ} (x : Fin m → Fin 3 → Bool) :
    (∀ j : Fin 2, CLE x j) ↔ CLE x 0 ∧ CLE x 1 := by
  constructor
  · intro h; exact ⟨h 0, h 1⟩
  · intro h j; fin_cases j <;> simp_all

open Classical in
theorem semS_succ {n : ℕ} (x : Fin (n + 2) → Fin 3 → Bool) :
    semS x = step (semS (Fin.init x)) (x (Fin.last _) 0, x (Fin.last _) 1, x (Fin.last _) 2) := by
  cases n with
  | zero =>
    have hT : (∀ i j : Fin 2, j.val = i.val + 1 → j.val = 0 → TriOK (x i) (x j) (x (Fin.last _))) := by
      intro i j h1 h2; omega
    simp only [semS, step]
    by_cases hy : Good' (Fin.init x)
    · have key : Good' x ↔ PairOK (Fin.init x (Fin.last 0)) (x (Fin.last _)) ∧ CLE x 0 ∧ CLE x 1 := by
        rw [Good_snoc, ← allCLE]; tauto
      rw [if_pos hy]
      have u0 := upd_snoc x 0 (hy.2.2 0)
      have u1 := upd_snoc x 1 (hy.2.2 1)
      simp only [show (((0 : Fin 2).castSucc : Fin 3)) = 0 from rfl, show (((0 : Fin 2).succ : Fin 3)) = 1 from rfl, show (((1 : Fin 2).castSucc : Fin 3)) = 1 from rfl, show (((1 : Fin 2).succ : Fin 3)) = 2 from rfl] at u0 u1
      simp only [vec_eq, triP, and_true, updAll, u0, u1]
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
          CLE x 0 ∧ CLE x 1 := by
        rw [Good_snoc, ← allCLE]
        constructor
        · rintro ⟨_, h2, h3, h4⟩; exact ⟨⟨h2, hT.mp h3⟩, h4⟩
        · rintro ⟨⟨h2, h3⟩, h4⟩; exact ⟨hy, h2, hT.mpr h3, h4⟩
      rw [if_pos hy]
      have u0 := upd_snoc x 0 (hy.2.2 0)
      have u1 := upd_snoc x 1 (hy.2.2 1)
      simp only [show (((0 : Fin 2).castSucc : Fin 3)) = 0 from rfl, show (((0 : Fin 2).succ : Fin 3)) = 1 from rfl, show (((1 : Fin 2).castSucc : Fin 3)) = 1 from rfl, show (((1 : Fin 2).succ : Fin 3)) = 2 from rfl] at u0 u1
      simp only [vec_eq, triP, updAll, u0, u1]
      split_ifs <;> simp_all <;> simp [Fin.init]
    · rw [if_neg hy, if_neg (fun h => hy ((Good_snoc x).mp h).1)]

theorem sem_succ (n : ℕ) (x : Fin (n + 2) → Fin 3 → Bool) :
    sem (n + 1) x = f (sem n (Fin.init x)) (e (x (Fin.last _))) := by
  unfold sem f
  rw [dec_enc, decR_e, semS_succ]

theorem singles : ∀ a b : Bool, ([a] < [b] ↔ a < b) ∧ ([a] ≤ [b] ↔ a ≤ b) := by decide

theorem colL_one (x : Fin 1 → Fin 3 → Bool) (j : Fin 3) : colL x j = [x 0 j] := by
  simp [colL]

theorem upd_one (x : Fin 1 → Fin 3 → Bool) (j : Fin 2) :
    updC false (x 0 j.castSucc) (x 0 j.succ) =
      @ite _ (CLE x j) (Classical.propDecidable _) (some (decide (CL x j))) none := by
  have hL : CL x j ↔ x 0 j.castSucc < x 0 j.succ := by
    unfold CL; rw [colL_one, colL_one]; exact (singles _ _).1
  have hLE : CLE x j ↔ x 0 j.castSucc ≤ x 0 j.succ := by
    unfold CLE; rw [colL_one, colL_one]; exact (singles _ _).2
  have key : ∀ a b : Bool, updC false a b =
      @ite _ (a ≤ b) (Classical.propDecidable _) (some (decide (a < b))) none := by
    intro a b; cases a <;> cases b <;> simp [updC]
  rw [key]
  by_cases h : x 0 j.castSucc ≤ x 0 j.succ
  · rw [if_pos h, if_pos (hLE.mpr h)]
    congr 2
    exact propext hL.symm
  · rw [if_neg h, if_neg (fun h' => h (hLE.mp h'))]

open Classical in
theorem sem_zero (x : Fin 1 → Fin 3 → Bool) : sem 0 x = ι (e (x 0)) := by
  unfold sem ι
  rw [decR_e]
  congr 1
  have hg : Good' x ↔ ∀ j : Fin 2, CLE x j := by
    unfold Good'
    constructor
    · exact fun h => h.2.2
    · intro h
      refine ⟨fun i i' hh => ?_, fun i j l h1 h2 => ?_, h⟩
      · have := i.isLt; have := i'.isLt; omega
      · have := i.isLt; have := j.isLt; omega
  have u0 := upd_one x 0
  have u1 := upd_one x 1
  simp only [show (((0 : Fin 2).castSucc : Fin 3)) = 0 from rfl, show (((0 : Fin 2).succ : Fin 3)) = 1 from rfl, show (((1 : Fin 2).castSucc : Fin 3)) = 1 from rfl, show (((1 : Fin 2).succ : Fin 3)) = 2 from rfl] at u0 u1
  simp only [semS, start, updAll, vec_eq]
  rw [u0, u1]
  by_cases hc : ∀ j : Fin 2, CLE x j
  · rw [if_pos (hg.mpr hc), if_pos (hc 0), if_pos (hc 1)]
  · rw [if_neg (fun h => hc (hg.mp h))]
    symm
    apply match_none
    push_neg at hc
    obtain ⟨j, hj⟩ := hc
    fin_cases j
    · left; rw [if_neg (by simpa using hj)]
    · right; rw [if_neg (by simpa using hj)]

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

theorem valid_iff {n : ℕ} (A : Fin (n + 1) → Fin 3 → Bool) : IsValid A ↔ Good' A := by
  have hsm : SmoothSubblocks A ↔
      (∀ i : Fin n, ∀ j j' : Fin 2, j'.val = j.val + 1 →
        close (bsv (A i.castSucc) (A i.succ) j) (bsv (A i.castSucc) (A i.succ) j')) ∧
      (∀ i i' : Fin n, i'.val = i.val + 1 → ∀ j : Fin 2,
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

theorem enc_some_lt : ∀ t : Option Row × Row × Fl, enc (some t) < 288 := by decide +kernel

open Classical in
theorem acc_sem (n : ℕ) (x : Fin (n + 1) → Fin 3 → Bool) :
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

theorem a_eq (n : ℕ) : a n = ∑ k ∈ range 8, (W f 8)^[n] acc (ι k) := by
  classical
  unfold a
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    ← sum_sem e sem f ι sem_zero sem_succ n acc]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [acc_sem]
  try congr 1

/-! Kernel tables: live states with their live successors, and packed level vectors. -/

def B : ℕ := 10

def T : ℕ → ℕ → ℕ
  | 0 => pk B 903831671688523357917782891200301899633180258766004527930335873439829810694108789027729552869648494800271254101138971567587115406091403951158952992946676304606343945029593045659026433634957107135864472806245281143251741321771446703142948709249368329102279118901710239641076091399768066233745689226105150886096354070021819094004354360860948922684955177407644871792883612645475740076692167331225852820078540160779437846658314624936375373212739824659351620771423607362047532687457215169431611571752796223434087971841535614108397541385140993188428088741673085105819062185095633023163810600189101724846681092169403911380570344013045669622284433228115254625383122622095588615407757829330584194418294832068062524090046672182406107946030200349414963037484964260130016839865020052931823968180609629733690433743629143915550222308157351333650674730022257370538975281371152385
  | 1 => pk B 903831671688523357917782891201727894574572165001004187882877709537691860387806886113994165275935372212793423282741612930460849128315502998726537331274185522675570792963347069026257187626528579161061284332190957895345237933913532990959338671053156844913090712006004700467344266223950806610298700241705430863495469110232230297062750774085100732890965604324173714915641176434950882124731869210558110801775241165205448790508453639541387577784821290512910265056612528248760399481973795121272543463259491268713982312527592375481964700618229006742248188584961928263382813942735352040193656546585268990043718044042654662947140776047384070172219916428116133209566648237230591694989804167962453480696673150225242586327348606705694219661224604572459337188569507763492825906687983752978860104863057865204514928389319887093333162960565550007087474922866862724360072329686941700
  | 2 => pk B 903831671688523357917782891203153889515963422768581872662287214487000045724199659632116156510062977226942420656073182156677291638012984059291165235073869802436745254439609438031326594523898330316804536564019093010512111184035487650988555662908066495801382759013713795251259124956590562376179854348531693765759271784370581529910231554715175718228938385619796985363787301226400192080148788189628779252378621414180434874476237120732327994595774114071056379557839786611573723137476376110576487020580568082885680317968042606352745343488489442626832949461619741356563732368597029895024168555463658706685387202495879693977165227817778782402715036125515155544857394938565690715494092421021863558398557415531807530719632805394855423617241667847130225360103625228550780166265438502533182163340987126563837681838195288689814294320178298585238616309248059737815948621747585029
  | 3 => pk B 903831671688523357917782891204579884457355977471003507787961381733415959775203080286532931400736201111910945669485877837991878834718737002787907475897883606354608502349331760616810007038901876254109266499403902536365550515203337041123288039414558820734687359930832477352822081089078679385216305892411293486992194481726367768039658327195592711054069920635877604077489382744254951785097442266861333176286567447746435828744856263804695053855820869551094201039608836594229196522596385915426892661778879526991317103884700835387965869662213784224098357422366248485459570025487652118266510541884742458756549250529397434682456086170638194842453986243005799877627753762074077820892228497384651501584462055025922372696249013508027025192283166722621023369949128150112007125706415901992519119294884666604304811617314857223310437827010556742840165470532798373667395455076532236
  | 4 => pk B 903831671688523357917782891206005879398748532173425142913635548979831873826206500940952432380617160446614666118195425571245407965917037552123024323236039522134189129647571123334857635538627531391752003002045593232213297099016518381337240373793297690915476348239129177137345899697309355496545629799652171880207148323722286468313482530910120923690310160416560547144597970158855927337763670386759396095565527111513334147906706183074160804433669035311959132104918681612191333936552481399300988891114586337491132296817207939565201271336316895115093683629789595399415543995742463946186053447834396352065392090627874678887465770027015613586284030088852380971441041578045756094660821103841847607594567961301193641219943498419216462800257813645113775537750334299084613970303843020369998635090063192543971165212137419974450403489929748201079092112748796432042853226814373917
  | 5 => pk B 903831671688523357917782891207431874340141086875846778039309716226247787877209921595375568146108433714298647147300776040416614840182441753243476775879159064618001477071077754799244893062608961957426213547453737358161424726547666372935595396143634972381194216037408010962154311331348397761974118632647007562744736097889183638155526516048416642730493565091095268687558850345349467540575395445842328966533430855786904928917451470994756501109558761279294255809869279350122176221446590464009301772101297157279773033893176103088698884158386805518863646756504103632333539457770809838694577284916858062846686821388421636227723072963111484083924403252798502404022924268791453687003793148251330858858740693416546166894966732771359105966148110893872223361341415668926186708097537955053818125068325082131805381085466912585737258568023379204110772026697893244795122188650807360
  | 6 => pk B 903831671688523357917782891208857869281533641578268413164983883472663701928213342249802338697210020914962888756801929245505499457514949606149264833827242233806045544619851655009971779610846167951131898135628334914209933397796781015918353106465570665131840963325668978827247315991195806181501772391395800534604957804227059277565790282610479868174620134659481768706372023303735572393532617444110212665854706557324511467343200784245155252734606029836659901725563535998963932877328886723950392489938975963974153181181441823180803340984187500390790383199475947662412859751765741171283357626353263708395876850464925000989191082693221001356949649668693951569922133470414999039370885110046337611608332504308631089567505733200758230750690663510419934389555868632866240624340870387458812399310386793189852964019235929850411112485209107088344071268571942597779334669489143929
  | 7 => pk B 903831671688523357917782891210283864222926196280690048290658050719079615979216762904232744033921922048607390946698885186512061817914561110840388497080289029698321332293892823967038295183339149372869056766569385900358823112763862310285513504759104769167416590103912080732624913676851580755128591075898550795787813442735913386544273830596310600022689869121720047201037489034014241896635336381563047193529354216126153763183954122825357059308810840984056069852001451558716603904199370179124261044627622757574272738682005099841514641813718979730873892958705127489653504877727257943952394472143613288712962177857384773171869799217344165405359769336538728469138669182916392151762096989226867865843343393977448409237560499707413837153885471494756908622393693190904775719033840317584981457816248325718113914013444471768471965241486931853778989838380615897552407702727033040
  | 8 => pk B 903831671688523357917782891211709859164318750983111683416332217965495530030220183558666784156244137115232153716991643863436301921381276267316847765638299452294828840093201261670444439780087906222637689440276890316608093871448910256037076591024237284487921096372137316678287104388315721482854574686155258346293303013415745965090977160005908838274702768477810104171555247536185476049883552258200832549557373832191831816439711486735361920832173194721482760189183026029380189302058040829530907436167237538080131706394865933070832786646981243539114176034191643114055474835655360156701687822287906803797942803565800952775759222535480976229154762256332833101672531406295633024177428785792921621563773362422998125905131032291325925175732534846883146059854889343041791992176447745432325300585909679716588231068092538339919816836856853500415527736133584550671258321762124109
  | _ => fun _ => 0

def D : List (ℕ × List ℕ) := [(0, [8, 156, 86, 15]), (7, [71]), (8, [8, 156]), (15, []), (71, [71]), (78, [129, 277, 135]), (86, [129, 277]), (95, []), (129, [237, 95]), (135, [143]), (143, [143]), (148, [258, 187, 191]), (156, [258]), (187, []), (191, []), (237, [267, 269]), (239, []), (241, [237, 239]), (242, [241, 242, 243, 245, 246, 247]), (243, [255]), (245, [267, 269, 271]), (246, [273, 275, 277, 279]), (247, [287]), (255, [287]), (258, [241, 242, 245, 246]), (267, [255]), (269, [267, 269, 271]), (271, [287]), (273, [237, 239]), (275, [255]), (277, [267, 269, 271]), (279, [287]), (287, [287])]

def I0 : List ℕ := [0, 148, 78, 7]


set_option maxRecDepth 100000 in
theorem hD : ∀ p ∈ D, ((List.range 8).map (f p.1)).filter (fun t => t != 288) = p.2 := by decide +kernel

set_option maxRecDepth 100000 in
theorem hcl : ∀ p ∈ D, ∀ t ∈ p.2, t ∈ D.map Prod.fst := by decide +kernel

set_option maxRecDepth 100000 in
theorem hfd : ∀ k < 8, f 288 k = 288 := by decide +kernel

set_option maxRecDepth 100000 in
theorem hI : ((List.range 8).map ι).filter (fun t => t != 288) = I0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem hIcl : ∀ t ∈ I0, t ∈ D.map Prod.fst := by decide +kernel

theorem hacc : acc 288 = 0 := by decide

set_option maxRecDepth 100000 in
theorem hT0 : ∀ p ∈ D, acc p.1 = T 0 p.1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem hT : ∀ j < 8, ∀ p ∈ D, (p.2.map (T j)).sum = T (j + 1) p.1 := by decide +kernel

theorem V_eq : ∀ j ≤ 8, ∀ p ∈ D, (W f 8)^[j] acc p.1 = T j p.1 :=
  iter_table f 8 288 D hD hcl hfd acc hacc T hT0 8 hT

theorem sum_I0 (g : ℕ → ℕ) (hg : g 288 = 0) : ∑ k ∈ range 8, g (ι k) = (I0.map g).sum := by
  rw [sum_range_list, ← hI, list_sum_filter _ _ _ hg, List.map_map]
  rfl

theorem a_list (m : ℕ) : a m = (I0.map ((W f 8)^[m] acc)).sum := by
  rw [a_eq, sum_I0 _ (iter_dead f 8 288 hfd acc hacc m)]

theorem a_val (m : ℕ) (hm : m ≤ 8) : a m = (I0.map (T m)).sum := by
  rw [a_list]
  congr 1
  apply List.map_congr_left
  intro t ht
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (hIcl t ht)
  exact V_eq m hm q hq

theorem hv1 : a 1 = 11 := by
  rw [a_val 1 (by norm_num)]
  decide +kernel

theorem hv2 : a 2 = 16 := by
  rw [a_val 2 (by norm_num)]
  decide +kernel

theorem hv3 : a 3 = 36 := by
  rw [a_val 3 (by norm_num)]
  decide +kernel

theorem hv4 : a 4 = 73 := by
  rw [a_val 4 (by norm_num)]
  decide +kernel

theorem hv5 : a 5 = 134 := by
  rw [a_val 5 (by norm_num)]
  decide +kernel

theorem hv6 : a 6 = 225 := by
  rw [a_val 6 (by norm_num)]
  decide +kernel

theorem hv7 : a 7 = 354 := by
  rw [a_val 7 (by norm_num)]
  decide +kernel

theorem hv8 : a 8 = 529 := by
  rw [a_val 8 (by norm_num)]
  decide +kernel

def P : List (ℕ × ℕ) := [(1, 4), (6, 2), (1, 0)]
def Q : List (ℕ × ℕ) := [(4, 3), (4, 1)]

theorem lin_T (L : List (ℕ × ℕ)) (hL : ∀ q ∈ L, 4 + q.2 ≤ 8) (p : ℕ × List ℕ) (hp : p ∈ D) :
    lin (fun j => (W f 8)^[j] acc) L 4 p.1 = (L.map fun q => q.1 * T (4 + q.2) p.1).sum := by
  unfold lin
  congr 1
  apply List.map_congr_left
  intro q hq
  dsimp only
  rw [V_eq _ (hL q hq) p hp]

set_option maxRecDepth 100000 in
theorem base : ∀ p ∈ D, lin (fun j => (W f 8)^[j] acc) P 4 p.1 = lin (fun j => (W f 8)^[j] acc) Q 4 p.1 := by
  intro p hp
  rw [lin_T P (by decide) p hp, lin_T Q (by decide) p hp]
  revert p
  decide +kernel

theorem lin_dead (L : List (ℕ × ℕ)) (m : ℕ) : lin (fun j => (W f 8)^[j] acc) L m 288 = 0 := by
  unfold lin
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hx
  dsimp only
  rw [iter_dead f 8 288 hfd acc hacc, mul_zero]

theorem urec (m : ℕ) (hm : 4 ≤ m) :
    (P.map fun q => q.1 * a (m + q.2)).sum = (Q.map fun q => q.1 * a (m + q.2)).sum := by
  simp only [a_eq]
  rw [TMEngine2.lin_sum (fun j => (W f 8)^[j] acc) ι 8 P m, TMEngine2.lin_sum (fun j => (W f 8)^[j] acc) ι 8 Q m,
    sum_I0 _ (lin_dead P m), sum_I0 _ (lin_dead Q m)]
  congr 1
  apply List.map_congr_left
  intro t ht
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (hIcl t ht)
  exact rec_lift f 8 288 D hD hcl hfd acc hacc P Q 4 base m hm q hq


theorem urecZ (m : ℕ) (hm : 4 ≤ m) :
    (a (m + 4) : ℤ) = 4 * a (m + 3) - 6 * a (m + 2) + 4 * a (m + 1) - a m := by
  have hr := urec m hm
  simp only [P, Q, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_assoc, Nat.reduceAdd, add_zero] at hr
  have := congrArg (fun t : ℕ => (t : ℤ)) hr
  push_cast at this
  linarith

theorem closedZ (n : ℕ) (hn : 4 ≤ n) : 3 * (a n : ℤ) = 4 * ((n : ℕ) : ℤ) ^ 3 - 15 * ((n : ℕ) : ℤ) ^ 2 + 74 * ((n : ℕ) : ℤ) - 93 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases (show n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ 8 ≤ n by omega) with rfl | rfl | rfl | rfl | hbig
    · rw [hv4]; norm_num
    · rw [hv5]; norm_num
    · rw [hv6]; norm_num
    · rw [hv7]; norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      rw [urecZ m (by omega)]
      have h3 := ih (m + 3) (by omega) (by omega)
      have h2 := ih (m + 2) (by omega) (by omega)
      have h1 := ih (m + 1) (by omega) (by omega)
      have h0 := ih m (by omega) (by omega)
      push_cast at h3 h2 h1 h0 ⊢
      linear_combination 4 * h3 - 6 * h2 + 4 * h1 - h0

end A184064P

theorem OMA.solution : type_of% @OMA.S_oeis_a184064.main := by
  open A184064P OMA.S_oeis_a184064 PowerSeries in
  refine ⟨?_, fun n hn => closedZ n (by omega), fun n hn => ?_⟩
  · set Fs := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) with hFs
    rw [show Fs * (1 - X) ^ 4 = Fs - 4 * (Fs * X ^ 1) + 6 * (Fs * X ^ 2) - 4 * (Fs * X ^ 3) + (Fs * X ^ 4) by ring]
    rw [show (X * (11 - 28 * X + 38 * X ^ 2 - 19 * X ^ 3 + 5 * X ^ 4 - X ^ 5 + 2 * X ^ 6) : PowerSeries ℤ) = 11 * X ^ 1 - 28 * X ^ 2 + 38 * X ^ 3 - 19 * X ^ 4 + 5 * X ^ 5 - X ^ 6 + 2 * X ^ 7 by ring]
    rw [show (38 : PowerSeries ℤ) = C (38 : ℤ) from (map_ofNat C 38).symm, show (28 : PowerSeries ℤ) = C (28 : ℤ) from (map_ofNat C 28).symm, show (19 : PowerSeries ℤ) = C (19 : ℤ) from (map_ofNat C 19).symm, show (11 : PowerSeries ℤ) = C (11 : ℤ) from (map_ofNat C 11).symm, show (6 : PowerSeries ℤ) = C (6 : ℤ) from (map_ofNat C 6).symm, show (5 : PowerSeries ℤ) = C (5 : ℤ) from (map_ofNat C 5).symm, show (4 : PowerSeries ℤ) = C (4 : ℤ) from (map_ofNat C 4).symm, show (2 : PowerSeries ℤ) = C (2 : ℤ) from (map_ofNat C 2).symm]
    ext n
    simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_X_pow]
    simp only [coeff_mul_X_pow', hFs, coeff_mk]
    rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ 8 ≤ n by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hbig
    · norm_num [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8]
    · norm_num [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8]
    · norm_num [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8]
    · norm_num [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8]
    · norm_num [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8]
    · norm_num [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8]
    · norm_num [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8]
    · norm_num [hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
      simp only [show m + 8 ≠ 0 by omega, show 1 ≤ m + 8 by omega, show m + 8 - 1 = m + 7 by omega, show m + 7 ≠ 0 by omega, show 2 ≤ m + 8 by omega, show m + 8 - 2 = m + 6 by omega, show m + 6 ≠ 0 by omega, show 3 ≤ m + 8 by omega, show m + 8 - 3 = m + 5 by omega, show m + 5 ≠ 0 by omega, show 4 ≤ m + 8 by omega, show m + 8 - 4 = m + 4 by omega, show m + 4 ≠ 0 by omega, show m + 8 ≠ 1 by omega, show m + 8 ≠ 2 by omega, show m + 8 ≠ 3 by omega, show m + 8 ≠ 4 by omega, show m + 8 ≠ 5 by omega, show m + 8 ≠ 6 by omega, show m + 8 ≠ 7 by omega, if_true, if_false]
      have h := urecZ (m + 4) (by omega)
      simp only [add_assoc, Nat.reduceAdd, add_zero] at h
      linarith
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega,
      show m + 4 - 4 = m by omega]
    exact urecZ m (by omega)

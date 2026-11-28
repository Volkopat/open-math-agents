import OMAStatements.S_oeis_a224410
import Mathlib
namespace OMA.S_oeis_a224410
open Finset

section generic
variable {α P Q : Type} [Fintype α] [DecidableEq α]
variable (lf : α → P) (δ : Q → α → Q) (T : Q → P → α → Option α → Bool)

def Lc {n : ℕ} (p : P) (x : Fin (n+1) → α) : Fin (n+1) → P :=
  Fin.cons (α := fun _ => P) p (fun k : Fin n => lf (x k.castSucc))
def Rc {n : ℕ} (x : Fin (n+1) → α) : Fin (n+1) → Option α :=
  Fin.snoc (α := fun _ => Option α) (fun k : Fin n => some (x k.succ)) none
def st {n : ℕ} (q : Q) (x : Fin (n+1) → α) (j : Fin (n+1)) : Q :=
  ((List.ofFn x).take j.val).foldl δ q
def Gd {n : ℕ} (q : Q) (p : P) (x : Fin (n+1) → α) : Prop :=
  ∀ j, T (st δ q x j) (Lc lf p x j) (x j) (Rc x j) = true

theorem st_zero {n : ℕ} (q : Q) (x : Fin (n+1) → α) : st δ q x 0 = q := by
  simp [st]

theorem st_succ {n : ℕ} (q : Q) (c : α) (y : Fin (n+1) → α) (j : Fin (n+1)) :
    st δ q (Fin.cons (α := fun _ => α) c y : Fin (n+2) → α) j.succ = st δ (δ q c) y j := by
  unfold st
  rw [List.ofFn_succ]
  simp [List.take_succ_cons]

theorem gd_cons {n : ℕ} (q : Q) (p : P) (c : α) (y : Fin (n+1) → α) :
    Gd lf δ T q p (Fin.cons (α := fun _ => α) c y : Fin (n+2) → α) ↔
      T q p c (some (y 0)) = true ∧ Gd lf δ T (δ q c) (lf c) y := by
  unfold Gd
  rw [Fin.forall_fin_succ]
  apply and_congr
  · have h1 : Lc lf p (Fin.cons (α := fun _ => α) c y : Fin (n+2) → α) 0 = p := by simp [Lc]
    have h2 : Rc (Fin.cons (α := fun _ => α) c y : Fin (n+2) → α) 0 = some (y 0) := by
      have : (0 : Fin (n+2)) = Fin.castSucc (0 : Fin (n+1)) := rfl
      rw [this]; simp [Rc]
    rw [h1, h2, st_zero]; simp
  · apply forall_congr'
    intro j
    have h1 : Lc lf p (Fin.cons (α := fun _ => α) c y : Fin (n+2) → α) j.succ = Lc lf (lf c) y j := by
      refine Fin.cases ?_ (fun k => ?_) j
      · simp [Lc]
      · simp [Lc]
    have h2 : Rc (Fin.cons (α := fun _ => α) c y : Fin (n+2) → α) j.succ = Rc y j := by
      refine Fin.lastCases ?_ (fun k => ?_) j
      · simp [Rc]
      · simp [Rc]; rw [Fin.succ_castSucc, Fin.snoc_castSucc]
    rw [h1, h2, st_succ]; simp

def W : ℕ → Q → P → α → ℕ
  | 0, q, p, c => if T q p c none = true then 1 else 0
  | n + 1, q, p, c => ∑ d, if T q p c (some d) = true then W n (δ q c) (lf c) d else 0

theorem gd_zero (q : Q) (p : P) (x : Fin 1 → α) : Gd lf δ T q p x ↔ T q p (x 0) none = true := by
  unfold Gd
  rw [Fin.forall_fin_one]
  have h1 : Lc lf p x 0 = p := by simp [Lc]
  have h2 : Rc x 0 = none := by
    show Fin.snoc (α := fun _ => Option α) _ none (Fin.last 0) = none
    exact Fin.snoc_last _ _
  rw [h1, h2, st_zero]

open Classical in
theorem cardW (n : ℕ) : ∀ (q : Q) (p : P) (c : α),
    (Finset.univ.filter (fun x : Fin (n+1) → α => x 0 = c ∧ Gd lf δ T q p x)).card = W lf δ T n q p c := by
  induction n with
  | zero =>
    intro q p c
    simp only [W]
    by_cases h : T q p c none = true
    · rw [if_pos h, Finset.card_eq_one]
      refine ⟨fun _ => c, ?_⟩
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, gd_zero]
      constructor
      · rintro ⟨h0, -⟩
        funext i
        rw [Fin.fin_one_eq_zero i]; exact h0
      · rintro rfl
        exact ⟨rfl, h⟩
    · rw [if_neg h, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _ hx
      apply h
      rw [← hx.1]
      exact (gd_zero lf δ T q p x).1 hx.2
  | succ n ih =>
    intro q p c
    have e : (Finset.univ.filter (fun x : Fin (n+2) → α => x 0 = c ∧ Gd lf δ T q p x)).card =
        (Finset.univ.filter (fun y : Fin (n+1) → α =>
          T q p c (some (y 0)) = true ∧ Gd lf δ T (δ q c) (lf c) y)).card := by
      apply Finset.card_bij (fun x _ => Fin.tail x)
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        obtain ⟨h0, hg⟩ := hx
        have : x = Fin.cons c (Fin.tail x) := by rw [← h0]; exact (Fin.cons_self_tail x).symm
        rw [this, gd_cons] at hg
        exact hg
      · intro x hx x' hx' h
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
        rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail x', hx.1, hx'.1, h]
      · intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        refine ⟨Fin.cons c y, ?_, by simp⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨by simp, (gd_cons lf δ T q p c y).2 hy⟩
    rw [e, Finset.card_eq_sum_card_fiberwise (f := fun y : Fin (n+1) → α => y 0) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    simp only [W]
    apply Finset.sum_congr rfl
    intro d _
    by_cases h : T q p c (some d) = true
    · rw [if_pos h, ← ih (δ q c) (lf c) d]
      congr 1
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨by rw [h1]; exact h, h2⟩, h1⟩
    · rw [if_neg h, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro y hyP hy0
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hyP
      apply h
      rw [← hy0]
      exact hyP.1

theorem rec_gen (K s : ℕ) (cf : ℕ → ℤ)
    (h0 : ∀ q p c, ∑ j ∈ Finset.range (K+1), cf j * (W lf δ T (s + j) q p c : ℤ) = 0) :
    ∀ n q p c, ∑ j ∈ Finset.range (K+1), cf j * (W lf δ T (s + n + j) q p c : ℤ) = 0 := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    intro q p c
    have : ∀ j, (W lf δ T (s + (n+1) + j) q p c : ℤ) =
        ∑ d, if T q p c (some d) = true then (W lf δ T (s + n + j) (δ q c) (lf c) d : ℤ) else 0 := by
      intro j
      rw [show s + (n+1) + j = (s+n+j) + 1 by omega]
      simp [W]
    simp only [this, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro d _
    by_cases h : T q p c (some d) = true
    · have := ih (δ q c) (lf c) d
      simp only [h, if_true]
      simpa [← Finset.mul_sum] using this
    · simp [h]
end generic
open PowerSeries in
theorem gf_gen (b : ℕ → ℚ) (m q : ℕ) (d p : ℕ → ℚ) (D N : PowerSeries ℚ)
    (hD : D = ∑ j ∈ Finset.range (m + 1), C (d j) * X ^ j)
    (hN : N = ∑ j ∈ Finset.range (q + 1), C (p j) * X ^ j) (hD0 : d 0 ≠ 0) (hp : ∀ n, q < n → p n = 0)
    (hb : ∀ n, ∑ j ∈ Finset.range (m + 1), d j * (if j ≤ n then b (n - j) else 0) =
      if n ≤ q then p n else 0) :
    mk b = N * D⁻¹ := by
  have hc : constantCoeff D ≠ 0 := by
    rw [hD]
    simp only [map_sum, map_mul, map_pow, constantCoeff_C, constantCoeff_X]
    rw [Finset.sum_eq_single 0]
    · simpa using hD0
    · intro j _ hj; simp [hj]
    · intro h; exfalso; exact h (by simp)
  rw [eq_mul_inv_iff_mul_eq hc, hD, hN]
  ext n
  simp only [Finset.mul_sum, map_sum]
  have : ∀ j ∈ Finset.range (m + 1), coeff n (mk b * (C (d j) * X ^ j)) =
      d j * (if j ≤ n then b (n - j) else 0) := by
    intro j _
    rw [mul_left_comm, coeff_C_mul, coeff_mul_X_pow']
    simp
  rw [Finset.sum_congr rfl this, hb n]
  simp only [coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single n]
  · by_cases h : n ≤ q
    · simp [h]
    · simp [h, hp n (by omega)]
  · intro j _ hj; simp [Ne.symm hj]
  · intro h; simp at h; simp [hp n (by omega)]
abbrev Col := Fin 3 → Fin 2
abbrev Fl := Fin 3 → Fin 3
def dl (q : Fl) (c : Col) : Fl := fun i =>
  if c i = 1 then (if q i = 2 then 2 else 1) else (if q i = 0 then 0 else 2)
def TU (q : Fl) (_ : Unit) (c : Col) (d : Option Col) : Bool :=
  decide (∀ i, ¬ (q i = 2 ∧ c i = 1)) &&
  (match d with | none => true | some e => decide (∀ i : Fin 2, e i.castSucc ≤ c i.succ))
def q0 : Fl := fun _ => 0

def stN {n : ℕ} (q : Fl) (x : Fin (n+1) → Col) (j : ℕ) : Fl := ((List.ofFn x).take j).foldl dl q

theorem stN_succ {n : ℕ} (q : Fl) (x : Fin (n+1) → Col) (j : ℕ) (hj : j < n + 1) :
    stN q x (j + 1) = dl (stN q x j) (x ⟨j, hj⟩) := by
  unfold stN
  rw [List.take_succ]
  have : (List.ofFn x)[j]? = some (x ⟨j, hj⟩) := by rw [List.getElem?_ofFn]; simp [hj]
  rw [this]
  simp [List.foldl_append]

theorem stN_zero {n : ℕ} (q : Fl) (x : Fin (n+1) → Col) : stN q x 0 = q := by
  simp [stN]

def AA {n : ℕ} (x : Fin (n+1) → Col) (i : Fin 3) (j : ℕ) : Prop :=
  ∃ k : Fin (n+1), k.val < j ∧ x k i = 1
def BB {n : ℕ} (x : Fin (n+1) → Col) (i : Fin 3) (j : ℕ) : Prop :=
  ∃ k1 k2 : Fin (n+1), k1 < k2 ∧ k2.val < j ∧ x k1 i = 1 ∧ x k2 i = 0

theorem inv_row {n : ℕ} (x : Fin (n+1) → Col) (i : Fin 3) :
    ∀ j, j ≤ n + 1 → ((stN q0 x j i = 0 ↔ ¬ AA x i j) ∧ (stN q0 x j i = 2 ↔ BB x i j) ∧
      (stN q0 x j i = 1 ↔ AA x i j ∧ ¬ BB x i j)) := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [stN_zero]
    refine ⟨?_, ?_, ?_⟩
    · simp [q0, AA]
    · simp [q0, BB]
    · simp [q0, AA]
  | succ j ih =>
    intro hj
    have hjn : j < n + 1 := by omega
    obtain ⟨h0, h2, h1⟩ := ih (by omega)
    rw [stN_succ _ _ _ hjn]
    have hA : AA x i (j + 1) ↔ AA x i j ∨ x ⟨j, hjn⟩ i = 1 := by
      constructor
      · rintro ⟨k, hk, hx⟩
        by_cases hkj : k.val < j
        · exact Or.inl ⟨k, hkj, hx⟩
        · right
          have : k = ⟨j, hjn⟩ := Fin.ext (by show _ = j; omega)
          rw [← this]; exact hx
      · rintro (⟨k, hk, hx⟩ | h)
        · exact ⟨k, by omega, hx⟩
        · exact ⟨⟨j, hjn⟩, by simp, h⟩
    have hB : BB x i (j + 1) ↔ BB x i j ∨ (AA x i j ∧ x ⟨j, hjn⟩ i = 0) := by
      constructor
      · rintro ⟨k1, k2, hlt, hk2, hx1, hx2⟩
        by_cases hkj : k2.val < j
        · exact Or.inl ⟨k1, k2, hlt, hkj, hx1, hx2⟩
        · right
          have : k2 = ⟨j, hjn⟩ := Fin.ext (by show _ = j; omega)
          subst this
          exact ⟨⟨k1, by simpa [Fin.lt_def] using hlt, hx1⟩, hx2⟩
      · rintro (⟨k1, k2, hlt, hk2, hx1, hx2⟩ | ⟨⟨k, hk, hx⟩, h⟩)
        · exact ⟨k1, k2, hlt, by omega, hx1, hx2⟩
        · exact ⟨k, ⟨j, hjn⟩, by simpa [Fin.lt_def] using hk, by simp, hx, h⟩
    have hv : x ⟨j, hjn⟩ i = 0 ∨ x ⟨j, hjn⟩ i = 1 := by
      have := (x ⟨j, hjn⟩ i).2
      rcases (x ⟨j, hjn⟩ i) with ⟨v, hv⟩
      simp only [Fin.ext_iff]
      omega
    have hr : stN q0 x j i = 0 ∨ stN q0 x j i = 1 ∨ stN q0 x j i = 2 := by
      rcases (stN q0 x j i) with ⟨v, hv⟩
      simp only [Fin.ext_iff]
      omega
    rw [hA, hB]
    simp only [dl]
    rcases hv with hv | hv <;> rcases hr with hr | hr | hr <;> simp [hv, hr] <;>
      simp_all <;> tauto

theorem unimodal_iff {m : ℕ} (x : Fin 3 → Fin (m+1) → Fin 2) :
    RowsUnimodal x ↔ ∀ (j : Fin (m+1)) (i : Fin 3),
      ¬ (st dl q0 (fun j i => x i j) j i = 2 ∧ x i j = 1) := by
  have key : ∀ (j : Fin (m+1)) (i : Fin 3), st dl q0 (fun j i => x i j) j i = 2 ↔
      BB (fun j i => x i j) i j.val := fun j i =>
    (inv_row (fun j i => x i j) i j.val (by have := j.2; omega)).2.1
  constructor
  · intro U j i ⟨h2, h1⟩
    obtain ⟨k1, k2, hlt, hk2, hx1, hx2⟩ := (key j i).1 h2
    apply U i k1 k2 j hlt (by rw [Fin.lt_def]; exact hk2)
    simp only at hx1 hx2
    rw [hx1, hx2, h1]
    exact ⟨by decide, by decide⟩
  · intro H i j1 j2 j3 h12 h23 ⟨hv1, hv2⟩
    apply H j3 i
    rw [Fin.lt_def] at hv1 hv2
    have a1 := (x i j1).2
    have a2 := (x i j2).2
    have a3 := (x i j3).2
    refine ⟨(key j3 i).2 ⟨j1, j2, h12, h23, ?_, ?_⟩, ?_⟩
    · exact Fin.ext (by simp; omega)
    · exact Fin.ext (by simp; omega)
    · exact Fin.ext (by simp; omega)

theorem anti_iff {m : ℕ} (x : Fin 3 → Fin (m+1) → Fin 2) :
    AntidiagsNondecreasing x ↔ ∀ (k : Fin m) (i : Fin 2), x i.castSucc k.succ ≤ x i.succ k.castSucc := by
  unfold AntidiagsNondecreasing
  constructor
  · intro h k i
    exact h i.castSucc i.succ k.succ k.castSucc (by simp) (by simp)
  · intro h i i' j j' hi hj
    have hj' : j'.val < m := by have := j.2; omega
    have hi2 : i.val < 2 := by have := i'.2; omega
    have e1 : i = (⟨i.val, hi2⟩ : Fin 2).castSucc := Fin.ext rfl
    have e2 : i' = (⟨i.val, hi2⟩ : Fin 2).succ := Fin.ext (by simp [hi])
    have e3 : j' = (⟨j'.val, hj'⟩ : Fin m).castSucc := Fin.ext rfl
    have e4 : j = (⟨j'.val, hj'⟩ : Fin m).succ := Fin.ext (by simp [hj])
    rw [e1, e2, e3, e4]
    exact h _ _

theorem gd_iff {m : ℕ} (x : Fin 3 → Fin (m+1) → Fin 2) :
    Gd (fun _ : Col => ()) dl TU q0 () (fun j i => x i j) ↔ RowsUnimodal x ∧ AntidiagsNondecreasing x := by
  rw [unimodal_iff, anti_iff]
  unfold Gd TU
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [forall_and]
  apply and_congr Iff.rfl
  constructor
  · intro h k i
    have := h k.castSucc
    simp only [Rc, Fin.snoc_castSucc] at this
    exact of_decide_eq_true this i
  · intro h j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [Rc]
    · simp only [Rc, Fin.snoc_castSucc]
      exact decide_eq_true (fun i => h k i)

def S (m : ℕ) : ℕ := ∑ c : Col, W (fun _ : Col => ()) dl TU m q0 () c

open Classical in
theorem a_eq (m : ℕ) : a (m + 1) = S m := by
  unfold a S
  have e : ((Finset.univ : Finset (Fin 3 → Fin (m+1) → Fin 2)).filter good).card =
      ((Finset.univ : Finset (Fin (m+1) → Col)).filter (fun y => Gd (fun _ : Col => ()) dl TU q0 () y)).card := by
    apply Finset.card_equiv (Equiv.piComm (fun (_ : Fin 3) (_ : Fin (m+1)) => Fin 2))
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.piComm_apply]
    exact (gd_iff x).symm
  rw [e, Finset.card_eq_sum_card_fiberwise (f := fun y : Fin (m+1) → Col => y 0) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro c _
  rw [← cardW (fun _ : Col => ()) dl TU m q0 () c]
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩

theorem rec_S (n : ℕ) (cf : ℕ → ℤ)
    (h0 : ∀ q p c, ∑ j ∈ Finset.range 8, cf j * (W (fun _ : Col => ()) dl TU (1 + j) q p c : ℤ) = 0) :
    ∑ j ∈ Finset.range 8, cf j * (S (1 + n + j) : ℤ) = 0 := by
  have h := rec_gen (fun _ : Col => ()) dl TU 7 1 cf h0 n q0 ()
  simp only [S, Nat.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro c _
  exact h c

def cf : ℕ → ℤ := fun j => [(-1 : ℤ), 7, -21, 35, -35, 21, -7, 1].getD j 0

def ix (q : Fl) (c : Col) : ℕ :=
  ((q 0).val * 9 + (q 1).val * 3 + (q 2).val) * 8 + ((c 0).val * 4 + (c 1).val * 2 + (c 2).val)

def tb0 : List ℕ := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]

def tb1 : List ℕ := [2, 4, 4, 8, 2, 4, 4, 8, 1, 4, 2, 8, 1, 4, 2, 8, 1, 0, 2, 0, 1, 0, 2, 0, 2, 2, 4, 8, 2, 2, 4, 8, 1, 2, 2, 8, 1, 2, 2, 8, 1, 0, 2, 0, 1, 0, 2, 0, 2, 2, 0, 0, 2, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 4, 2, 4, 2, 4, 4, 8, 1, 4, 1, 4, 1, 4, 2, 8, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2, 2, 4, 2, 2, 4, 8, 1, 2, 1, 4, 1, 2, 2, 8, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2, 0, 0, 2, 2, 0, 0, 1, 2, 0, 0, 1, 2, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 4, 2, 4, 0, 0, 0, 0, 1, 4, 1, 4, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 2, 2, 2, 4, 0, 0, 0, 0, 1, 2, 1, 4, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]

def tb2 : List ℕ := [6, 15, 8, 26, 6, 10, 8, 21, 1, 15, 2, 26, 1, 10, 2, 21, 1, 0, 2, 0, 1, 0, 2, 0, 4, 3, 8, 26, 4, 3, 8, 21, 1, 3, 2, 26, 1, 3, 2, 21, 1, 0, 2, 0, 1, 0, 2, 0, 4, 3, 0, 0, 4, 3, 0, 0, 1, 3, 0, 0, 1, 3, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 6, 10, 4, 8, 6, 10, 8, 21, 1, 10, 1, 8, 1, 10, 2, 21, 1, 0, 1, 0, 1, 0, 2, 0, 4, 3, 4, 8, 4, 3, 8, 21, 1, 3, 1, 8, 1, 3, 2, 21, 1, 0, 1, 0, 1, 0, 2, 0, 4, 3, 0, 0, 4, 3, 0, 0, 1, 3, 0, 0, 1, 3, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 6, 10, 4, 8, 0, 0, 0, 0, 1, 10, 1, 8, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 4, 3, 4, 8, 0, 0, 0, 0, 1, 3, 1, 8, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 4, 3, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]

def tb3 : List ℕ := [21, 44, 14, 59, 16, 20, 14, 40, 1, 44, 2, 59, 1, 20, 2, 40, 1, 0, 2, 0, 1, 0, 2, 0, 7, 4, 14, 59, 7, 4, 14, 40, 1, 4, 2, 59, 1, 4, 2, 40, 1, 0, 2, 0, 1, 0, 2, 0, 7, 4, 0, 0, 7, 4, 0, 0, 1, 4, 0, 0, 1, 4, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 16, 20, 7, 13, 16, 20, 14, 40, 1, 20, 1, 13, 1, 20, 2, 40, 1, 0, 1, 0, 1, 0, 2, 0, 7, 4, 7, 13, 7, 4, 14, 40, 1, 4, 1, 13, 1, 4, 2, 40, 1, 0, 1, 0, 1, 0, 2, 0, 7, 4, 0, 0, 7, 4, 0, 0, 1, 4, 0, 0, 1, 4, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 16, 20, 7, 13, 0, 0, 0, 0, 1, 20, 1, 13, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 7, 4, 7, 13, 0, 0, 0, 0, 1, 4, 1, 13, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 7, 4, 0, 0, 0, 0, 0, 0, 1, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]

def tb4 : List ℕ := [65, 106, 22, 113, 36, 35, 22, 66, 1, 106, 2, 113, 1, 35, 2, 66, 1, 0, 2, 0, 1, 0, 2, 0, 11, 5, 22, 113, 11, 5, 22, 66, 1, 5, 2, 113, 1, 5, 2, 66, 1, 0, 2, 0, 1, 0, 2, 0, 11, 5, 0, 0, 11, 5, 0, 0, 1, 5, 0, 0, 1, 5, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 36, 35, 11, 19, 36, 35, 22, 66, 1, 35, 1, 19, 1, 35, 2, 66, 1, 0, 1, 0, 1, 0, 2, 0, 11, 5, 11, 19, 11, 5, 22, 66, 1, 5, 1, 19, 1, 5, 2, 66, 1, 0, 1, 0, 1, 0, 2, 0, 11, 5, 0, 0, 11, 5, 0, 0, 1, 5, 0, 0, 1, 5, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 36, 35, 11, 19, 0, 0, 0, 0, 1, 35, 1, 19, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 11, 5, 11, 19, 0, 0, 0, 0, 1, 5, 1, 19, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 11, 5, 0, 0, 0, 0, 0, 0, 1, 5, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]

def tb5 : List ℕ := [171, 222, 32, 195, 71, 56, 32, 100, 1, 222, 2, 195, 1, 56, 2, 100, 1, 0, 2, 0, 1, 0, 2, 0, 16, 6, 32, 195, 16, 6, 32, 100, 1, 6, 2, 195, 1, 6, 2, 100, 1, 0, 2, 0, 1, 0, 2, 0, 16, 6, 0, 0, 16, 6, 0, 0, 1, 6, 0, 0, 1, 6, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 71, 56, 16, 26, 71, 56, 32, 100, 1, 56, 1, 26, 1, 56, 2, 100, 1, 0, 1, 0, 1, 0, 2, 0, 16, 6, 16, 26, 16, 6, 32, 100, 1, 6, 1, 26, 1, 6, 2, 100, 1, 0, 1, 0, 1, 0, 2, 0, 16, 6, 0, 0, 16, 6, 0, 0, 1, 6, 0, 0, 1, 6, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 71, 56, 16, 26, 0, 0, 0, 0, 1, 56, 1, 26, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 16, 6, 16, 26, 0, 0, 0, 0, 1, 6, 1, 26, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 16, 6, 0, 0, 0, 0, 0, 0, 1, 6, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]

def tb6 : List ℕ := [393, 420, 44, 313, 127, 84, 44, 143, 1, 420, 2, 313, 1, 84, 2, 143, 1, 0, 2, 0, 1, 0, 2, 0, 22, 7, 44, 313, 22, 7, 44, 143, 1, 7, 2, 313, 1, 7, 2, 143, 1, 0, 2, 0, 1, 0, 2, 0, 22, 7, 0, 0, 22, 7, 0, 0, 1, 7, 0, 0, 1, 7, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 127, 84, 22, 34, 127, 84, 44, 143, 1, 84, 1, 34, 1, 84, 2, 143, 1, 0, 1, 0, 1, 0, 2, 0, 22, 7, 22, 34, 22, 7, 44, 143, 1, 7, 1, 34, 1, 7, 2, 143, 1, 0, 1, 0, 1, 0, 2, 0, 22, 7, 0, 0, 22, 7, 0, 0, 1, 7, 0, 0, 1, 7, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 127, 84, 22, 34, 0, 0, 0, 0, 1, 84, 1, 34, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 22, 7, 22, 34, 0, 0, 0, 0, 1, 7, 1, 34, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 22, 7, 0, 0, 0, 0, 0, 0, 1, 7, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]

def tb7 : List ℕ := [813, 736, 58, 476, 211, 120, 58, 196, 1, 736, 2, 476, 1, 120, 2, 196, 1, 0, 2, 0, 1, 0, 2, 0, 29, 8, 58, 476, 29, 8, 58, 196, 1, 8, 2, 476, 1, 8, 2, 196, 1, 0, 2, 0, 1, 0, 2, 0, 29, 8, 0, 0, 29, 8, 0, 0, 1, 8, 0, 0, 1, 8, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 211, 120, 29, 43, 211, 120, 58, 196, 1, 120, 1, 43, 1, 120, 2, 196, 1, 0, 1, 0, 1, 0, 2, 0, 29, 8, 29, 43, 29, 8, 58, 196, 1, 8, 1, 43, 1, 8, 2, 196, 1, 0, 1, 0, 1, 0, 2, 0, 29, 8, 0, 0, 29, 8, 0, 0, 1, 8, 0, 0, 1, 8, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 211, 120, 29, 43, 0, 0, 0, 0, 1, 120, 1, 43, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 29, 8, 29, 43, 0, 0, 0, 0, 1, 8, 1, 43, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 29, 8, 0, 0, 0, 0, 0, 0, 1, 8, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]

def tb8 : List ℕ := [1549, 1215, 74, 694, 331, 165, 74, 260, 1, 1215, 2, 694, 1, 165, 2, 260, 1, 0, 2, 0, 1, 0, 2, 0, 37, 9, 74, 694, 37, 9, 74, 260, 1, 9, 2, 694, 1, 9, 2, 260, 1, 0, 2, 0, 1, 0, 2, 0, 37, 9, 0, 0, 37, 9, 0, 0, 1, 9, 0, 0, 1, 9, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 331, 165, 37, 53, 331, 165, 74, 260, 1, 165, 1, 53, 1, 165, 2, 260, 1, 0, 1, 0, 1, 0, 2, 0, 37, 9, 37, 53, 37, 9, 74, 260, 1, 9, 1, 53, 1, 9, 2, 260, 1, 0, 1, 0, 1, 0, 2, 0, 37, 9, 0, 0, 37, 9, 0, 0, 1, 9, 0, 0, 1, 9, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 331, 165, 37, 53, 0, 0, 0, 0, 1, 165, 1, 53, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 37, 9, 37, 53, 0, 0, 0, 0, 1, 9, 1, 53, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 37, 9, 0, 0, 0, 0, 0, 0, 1, 9, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]

theorem Wstep (n : ℕ) (q : Fl) (c : Col) : W (fun _ : Col => ()) dl TU (n+1) q () c =
    ∑ d : Col, if TU q () c (some d) = true then W (fun _ : Col => ()) dl TU n (dl q c) () d else 0 := rfl
theorem L0 : ∀ (q : Fl) (c : Col), W (fun _ : Col => ()) dl TU 0 q () c = tb0.getD (ix q c) 0 := by
  decide +kernel

theorem L1 : ∀ (q : Fl) (c : Col), W (fun _ : Col => ()) dl TU 1 q () c = tb1.getD (ix q c) 0 := by
  intro q c
  rw [Wstep]
  simp only [L0]
  revert q c
  decide +kernel

theorem L2 : ∀ (q : Fl) (c : Col), W (fun _ : Col => ()) dl TU 2 q () c = tb2.getD (ix q c) 0 := by
  intro q c
  rw [Wstep]
  simp only [L1]
  revert q c
  decide +kernel

theorem L3 : ∀ (q : Fl) (c : Col), W (fun _ : Col => ()) dl TU 3 q () c = tb3.getD (ix q c) 0 := by
  intro q c
  rw [Wstep]
  simp only [L2]
  revert q c
  decide +kernel

theorem L4 : ∀ (q : Fl) (c : Col), W (fun _ : Col => ()) dl TU 4 q () c = tb4.getD (ix q c) 0 := by
  intro q c
  rw [Wstep]
  simp only [L3]
  revert q c
  decide +kernel

theorem L5 : ∀ (q : Fl) (c : Col), W (fun _ : Col => ()) dl TU 5 q () c = tb5.getD (ix q c) 0 := by
  intro q c
  rw [Wstep]
  simp only [L4]
  revert q c
  decide +kernel

theorem L6 : ∀ (q : Fl) (c : Col), W (fun _ : Col => ()) dl TU 6 q () c = tb6.getD (ix q c) 0 := by
  intro q c
  rw [Wstep]
  simp only [L5]
  revert q c
  decide +kernel

theorem L7 : ∀ (q : Fl) (c : Col), W (fun _ : Col => ()) dl TU 7 q () c = tb7.getD (ix q c) 0 := by
  intro q c
  rw [Wstep]
  simp only [L6]
  revert q c
  decide +kernel

theorem L8 : ∀ (q : Fl) (c : Col), W (fun _ : Col => ()) dl TU 8 q () c = tb8.getD (ix q c) 0 := by
  intro q c
  rw [Wstep]
  simp only [L7]
  revert q c
  decide +kernel

def tbl (k : ℕ) : List ℕ := [tb0, tb1, tb2, tb3, tb4, tb5, tb6, tb7, tb8].getD k []
theorem key : ∀ j, j < 8 → ∀ (q : Fl) (c : Col), W (fun _ : Col => ()) dl TU (1 + j) q () c = (tbl (1 + j)).getD (ix q c) 0 := by
  intro j hj q c
  interval_cases j
  · exact L1 q c
  · exact L2 q c
  · exact L3 q c
  · exact L4 q c
  · exact L5 q c
  · exact L6 q c
  · exact L7 q c
  · exact L8 q c
theorem h0chk : ∀ (q : Fl) (c : Col), ∑ j ∈ Finset.range 8, cf j * (((tbl (1 + j)).getD (ix q c) 0 : ℕ) : ℤ) = 0 := by
  decide +kernel
theorem h0 : ∀ q p c, ∑ j ∈ Finset.range 8, cf j * (W (fun _ : Col => ()) dl TU (1 + j) q p c : ℤ) = 0 := by
  intro q p c
  cases p
  rw [Finset.sum_congr rfl (fun j hj => by rw [key j (Finset.mem_range.1 hj) q c])]
  exact h0chk q c

theorem sv0 : S 0 = 8 := by
  unfold S
  simp only [L0]
  decide +kernel

theorem sv1 : S 1 = 36 := by
  unfold S
  simp only [L1]
  decide +kernel

theorem sv2 : S 2 = 100 := by
  unfold S
  simp only [L2]
  decide +kernel

theorem sv3 : S 3 = 228 := by
  unfold S
  simp only [L3]
  decide +kernel

theorem sv4 : S 4 = 465 := by
  unfold S
  simp only [L4]
  decide +kernel

theorem sv5 : S 5 = 879 := by
  unfold S
  simp only [L5]
  decide +kernel

theorem sv6 : S 6 = 1568 := by
  unfold S
  simp only [L6]
  decide +kernel

theorem sv7 : S 7 = 2668 := by
  unfold S
  simp only [L7]
  decide +kernel
theorem recS (m : ℕ) : (S (m + 7) : ℤ) = 7 * S (m + 6) - 21 * S (m + 5) + 35 * S (m + 4) - 35 * S (m + 3)
    + 21 * S (m + 2) - 7 * S (m + 1) + S m := by
  rcases m with _ | m
  · simp only [Nat.zero_add]
    rw [show (7:ℕ) = 7 from rfl, sv7, sv6, sv5, sv4, sv3, sv2, sv1, sv0]; norm_num
  · have h := rec_S m cf h0
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, cf, List.getD_cons_zero, List.getD_cons_succ,
      zero_add, Nat.add_zero] at h
    have e : ∀ k, 1 + m + k = m + 1 + k := fun k => by omega
    simp only [e] at h
    rw [Nat.add_comm 1 m] at h
    linarith

theorem a_rec (n : ℕ) (hn : 7 < n) : (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4)
    + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  have f1 : m + 8 - 1 = (m + 6) + 1 := by omega
  have f2 : m + 8 - 2 = (m + 5) + 1 := by omega
  have f3 : m + 8 - 3 = (m + 4) + 1 := by omega
  have f4 : m + 8 - 4 = (m + 3) + 1 := by omega
  have f5 : m + 8 - 5 = (m + 2) + 1 := by omega
  have f6 : m + 8 - 6 = (m + 1) + 1 := by omega
  have f7 : m + 8 - 7 = m + 1 := by omega
  rw [f1, f2, f3, f4, f5, f6, f7, show m + 8 = (m + 7) + 1 from rfl, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq]
  exact recS m

theorem v1 : a 1 = 8 := (a_eq 0).trans sv0
theorem v2 : a 2 = 36 := (a_eq 1).trans sv1
theorem v3 : a 3 = 100 := (a_eq 2).trans sv2
theorem v4 : a 4 = 228 := (a_eq 3).trans sv3
theorem v5 : a 5 = 465 := (a_eq 4).trans sv4
theorem v6 : a 6 = 879 := (a_eq 5).trans sv5
theorem v7 : a 7 = 1568 := (a_eq 6).trans sv6

theorem gfthm : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - PowerSeries.X) ^ 7 =
    PowerSeries.X * (8 - 20 * PowerSeries.X + 16 * PowerSeries.X ^ 2 + 4 * PowerSeries.X ^ 3 -
      11 * PowerSeries.X ^ 4 + 4 * PowerSeries.X ^ 5) := by
  have h := gf_gen (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) 7 6
    (fun j => [(1 : ℚ), -7, 21, -35, 35, -21, 7, -1].getD j 0)
    (fun j => [(0 : ℚ), 8, -20, 16, 4, -11, 4].getD j 0)
    ((1 - PowerSeries.X) ^ 7)
    (PowerSeries.X * (8 - 20 * PowerSeries.X + 16 * PowerSeries.X ^ 2 + 4 * PowerSeries.X ^ 3 -
      11 * PowerSeries.X ^ 4 + 4 * PowerSeries.X ^ 5) : PowerSeries ℚ)
    (by simp [Finset.sum_range_succ, map_ofNat PowerSeries.C]; ring)
    (by simp [Finset.sum_range_succ, map_ofNat PowerSeries.C]; ring) (by norm_num) ?_ ?_
  · rw [h, mul_assoc, PowerSeries.inv_mul_cancel _ (by simp), mul_one]
  · intro n hn
    simp only [List.getD_eq_getElem?_getD]
    rcases n with _ | _ | _ | _ | _ | _ | _ | k <;> simp_all
  · intro n
    by_cases hn : n ≤ 7
    · interval_cases n <;> simp [Finset.sum_range_succ, v1, v2, v3, v4, v5, v6, v7] <;> norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
      have r : (a (k + 8) : ℚ) = 7 * a (k + 7) - 21 * a (k + 6) + 35 * a (k + 5) - 35 * a (k + 4)
          + 21 * a (k + 3) - 7 * a (k + 2) + a (k + 1) := by
        have := a_rec (k + 8) (by omega)
        have e1 : k + 8 - 1 = k + 7 := by omega
        have e2 : k + 8 - 2 = k + 6 := by omega
        have e3 : k + 8 - 3 = k + 5 := by omega
        have e4 : k + 8 - 4 = k + 4 := by omega
        have e5 : k + 8 - 5 = k + 3 := by omega
        have e6 : k + 8 - 6 = k + 2 := by omega
        have e7 : k + 8 - 7 = k + 1 := by omega
        rw [e1, e2, e3, e4, e5, e6, e7] at this
        exact_mod_cast this
      have g0 : k + 8 - 0 = k + 8 := by omega
      have g1 : k + 8 - 1 = k + 7 := by omega
      have g2 : k + 8 - 2 = k + 6 := by omega
      have g3 : k + 8 - 3 = k + 5 := by omega
      have g4 : k + 8 - 4 = k + 4 := by omega
      have g5 : k + 8 - 5 = k + 3 := by omega
      have g6 : k + 8 - 6 = k + 2 := by omega
      have g7 : k + 8 - 7 = k + 1 := by omega
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, g0, g1, g2, g3, g4, g5, g6, g7]
      simp only [if_neg hn, if_pos (show 0 ≤ k + 8 by omega), if_pos (show 1 ≤ k + 8 by omega),
        if_pos (show 2 ≤ k + 8 by omega), if_pos (show 3 ≤ k + 8 by omega),
        if_pos (show 4 ≤ k + 8 by omega), if_pos (show 5 ≤ k + 8 by omega),
        if_pos (show 6 ≤ k + 8 by omega), if_pos (show 7 ≤ k + 8 by omega)]
      simp only [show k + 8 ≠ 0 by omega, show k + 7 ≠ 0 by omega, show k + 6 ≠ 0 by omega,
        show k + 5 ≠ 0 by omega, show k + 4 ≠ 0 by omega, show k + 3 ≠ 0 by omega,
        show k + 2 ≠ 0 by omega, show k + 1 ≠ 0 by omega, if_false]
      norm_num [List.getD]
      linarith
end OMA.S_oeis_a224410

theorem OMA.solution : type_of% @OMA.S_oeis_a224410.main := by
  refine ⟨OMA.S_oeis_a224410.gfthm, ?_⟩
  intro n hn
  exact OMA.S_oeis_a224410.a_rec n hn

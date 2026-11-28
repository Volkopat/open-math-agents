import OMAStatements.S_oeis_a208639
import Mathlib
namespace OMA.S_oeis_a208639
open Finset

section generic
variable {α : Type} [Fintype α] [DecidableEq α] (T : Option α → α → Option α → Bool)

def Lc {n : ℕ} (p : Option α) (x : Fin (n+1) → α) : Fin (n+1) → Option α :=
  Fin.cons (α := fun _ => Option α) p (fun k : Fin n => some (x k.castSucc))
def Rc {n : ℕ} (x : Fin (n+1) → α) : Fin (n+1) → Option α :=
  Fin.snoc (α := fun _ => Option α) (fun k : Fin n => some (x k.succ)) none
def Gd {n : ℕ} (p : Option α) (x : Fin (n+1) → α) : Prop := ∀ j, T (Lc p x j) (x j) (Rc x j) = true

theorem gd_cons {n : ℕ} (p : Option α) (c : α) (y : Fin (n+1) → α) :
    Gd T p (Fin.cons (α := fun _ => α) c y : Fin (n+2) → α) ↔ T p c (some (y 0)) = true ∧ Gd T (some c) y := by
  unfold Gd
  rw [Fin.forall_fin_succ]
  apply and_congr
  · have h1 : Lc p (Fin.cons (α := fun _ => α) c y : Fin (n+2) → α) 0 = p := by simp [Lc]
    have h2 : Rc (Fin.cons (α := fun _ => α) c y : Fin (n+2) → α) 0 = some (y 0) := by
      have : (0 : Fin (n+2)) = Fin.castSucc (0 : Fin (n+1)) := rfl
      rw [this]; simp [Rc]
    rw [h1, h2]; simp
  · apply forall_congr'
    intro j
    have h1 : Lc p (Fin.cons (α := fun _ => α) c y : Fin (n+2) → α) j.succ = Lc (some c) y j := by
      refine Fin.cases ?_ (fun k => ?_) j
      · simp [Lc]
      · simp [Lc]
    have h2 : Rc (Fin.cons (α := fun _ => α) c y : Fin (n+2) → α) j.succ = Rc y j := by
      refine Fin.lastCases ?_ (fun k => ?_) j
      · simp [Rc]
      · simp [Rc]; rw [Fin.succ_castSucc, Fin.snoc_castSucc]
    rw [h1, h2]; simp

def W : ℕ → Option α → α → ℕ
  | 0, p, c => if T p c none = true then 1 else 0
  | n + 1, p, c => ∑ d, if T p c (some d) = true then W (n) (some c) d else 0

theorem gd_zero (p : Option α) (x : Fin 1 → α) : Gd T p x ↔ T p (x 0) none = true := by
  unfold Gd
  rw [Fin.forall_fin_one]
  have h1 : Lc p x 0 = p := by simp [Lc]
  have h2 : Rc x 0 = none := by
    show Fin.snoc (α := fun _ => Option α) _ none (Fin.last 0) = none
    exact Fin.snoc_last _ _
  rw [h1, h2]

open Classical in
theorem cardW (n : ℕ) : ∀ (p : Option α) (c : α),
    (Finset.univ.filter (fun x : Fin (n+1) → α => x 0 = c ∧ Gd T p x)).card = W T n p c := by
  induction n with
  | zero =>
    intro p c
    simp only [W]
    by_cases h : T p c none = true
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
      exact (gd_zero T p x).1 hx.2
  | succ n ih =>
    intro p c
    have e : (Finset.univ.filter (fun x : Fin (n+2) → α => x 0 = c ∧ Gd T p x)).card =
        (Finset.univ.filter (fun y : Fin (n+1) → α => T p c (some (y 0)) = true ∧ Gd T (some c) y)).card := by
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
        exact ⟨by simp, (gd_cons T p c y).2 hy⟩
    rw [e, Finset.card_eq_sum_card_fiberwise (f := fun y : Fin (n+1) → α => y 0) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    simp only [W]
    apply Finset.sum_congr rfl
    intro d _
    by_cases h : T p c (some d) = true
    · rw [if_pos h, ← ih (some c) d]
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
    (h0 : ∀ p c, ∑ j ∈ Finset.range (K+1), cf j * (W T (s + j) p c : ℤ) = 0) :
    ∀ n p c, ∑ j ∈ Finset.range (K+1), cf j * (W T (s + n + j) p c : ℤ) = 0 := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    intro p c
    have : ∀ j, (W T (s + (n+1) + j) p c : ℤ) =
        ∑ d, if T p c (some d) = true then (W T (s + n + j) (some c) d : ℤ) else 0 := by
      intro j
      rw [show s + (n+1) + j = (s+n+j) + 1 by omega]
      simp [W]
    simp only [this, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro d _
    by_cases h : T p c (some d) = true
    · have := ih (some c) d
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
theorem sum_single' {ι : Type} [Fintype ι] (P : ι → Prop) [DecidablePred P] (q : ι)
    (hq : ∀ p, P p → p = q) : (∑ p, if P p then (1:ℕ) else 0) = if P q then 1 else 0 := by
  rw [Finset.sum_eq_single q]
  · intro p _ hp; rw [if_neg]; intro h; exact hp (hq p h)
  · intro h; exact absurd (Finset.mem_univ q) h

theorem sum_none' {ι : Type} [Fintype ι] (P : ι → Prop) [DecidablePred P] (h : ∀ p, ¬ P p) :
    (∑ p, if P p then (1:ℕ) else 0) = 0 := by
  apply Finset.sum_eq_zero; intro p _; rw [if_neg (h p)]

theorem eqNbrs_eq {R C K : ℕ} (x : Fin R → Fin C → Fin K) (i : Fin R) (j : Fin C) :
    eqNbrs x i j =
      (if h : 1 ≤ j.val then (if x i ⟨j.val - 1, by omega⟩ = x i j then 1 else 0) else 0) +
      (if h : 1 ≤ i.val then (if x ⟨i.val - 1, by omega⟩ j = x i j then 1 else 0) else 0) +
      (if h : 1 ≤ i.val ∧ j.val + 1 < C then
        (if x ⟨i.val - 1, by omega⟩ ⟨j.val + 1, h.2⟩ = x i j then 1 else 0) else 0) := by
  unfold eqNbrs
  rw [Finset.card_filter]
  have hsplit : ∀ p : Fin R × Fin C, (if (((p.1 = i ∧ p.2.val + 1 = j.val) ∨
      (p.1.val + 1 = i.val ∧ p.2 = j) ∨ (p.1.val + 1 = i.val ∧ p.2.val = j.val + 1)) ∧
      x p.1 p.2 = x i j) then 1 else 0 : ℕ) =
      (if ((p.1 = i ∧ p.2.val + 1 = j.val) ∧ x p.1 p.2 = x i j) then 1 else 0) +
      (if ((p.1.val + 1 = i.val ∧ p.2 = j) ∧ x p.1 p.2 = x i j) then 1 else 0) +
      (if ((p.1.val + 1 = i.val ∧ p.2.val = j.val + 1) ∧ x p.1 p.2 = x i j) then 1 else 0) := by
    intro p
    obtain ⟨a, b⟩ := p
    simp only [Fin.ext_iff]
    split_ifs <;> first | rfl | omega | (exfalso; omega) | (simp_all; done) | skip
  simp only [hsplit, Finset.sum_add_distrib]
  congr 1
  congr 1
  · by_cases h : 1 ≤ j.val
    · rw [dif_pos h, sum_single' _ (i, ⟨j.val - 1, by omega⟩)]
      · have e : j.val - 1 + 1 = j.val := by omega
        simp [e]
      · intro p hp
        obtain ⟨⟨h1, h2⟩, _⟩ := hp
        exact Prod.ext h1 (Fin.ext (by simp; omega))
    · rw [dif_neg h, sum_none']
      intro p hp; omega
  · by_cases h : 1 ≤ i.val
    · rw [dif_pos h, sum_single' _ (⟨i.val - 1, by omega⟩, j)]
      · have e : i.val - 1 + 1 = i.val := by omega
        simp [e]
      · intro p hp
        obtain ⟨⟨h1, h2⟩, _⟩ := hp
        exact Prod.ext (Fin.ext (by simp; omega)) h2
    · rw [dif_neg h, sum_none']
      intro p hp; omega
  · by_cases h : 1 ≤ i.val ∧ j.val + 1 < C
    · rw [dif_pos h, sum_single' _ (⟨i.val - 1, by omega⟩, ⟨j.val + 1, h.2⟩)]
      · have e : i.val - 1 + 1 = i.val := by omega
        simp [e]
      · intro p hp
        obtain ⟨⟨h1, h2⟩, _⟩ := hp
        exact Prod.ext (Fin.ext (by simp; omega)) (Fin.ext (by simp; omega))
    · rw [dif_neg h, sum_none']
      intro p hp
      have := p.2.2
      omega
abbrev Col := Fin 4 → Fin 2
def cget (c : Col) (r : ℕ) : Option (Fin 2) := if h : r < 4 then some (c ⟨r, h⟩) else none
def cntL (p : Option Col) (c : Col) (i : Fin 4) : ℕ :=
  match p with | none => 0 | some q => if q i = c i then 1 else 0
def cntU (c : Col) (i : Fin 4) : ℕ := if 1 ≤ i.val ∧ cget c (i.val - 1) = some (c i) then 1 else 0
def cntR (d : Option Col) (c : Col) (i : Fin 4) : ℕ :=
  match d with | none => 0 | some e => if 1 ≤ i.val ∧ cget e (i.val - 1) = some (c i) then 1 else 0
def TT (p : Option Col) (c : Col) (d : Option Col) : Bool :=
  decide (∀ i, cntL p c i + cntU c i + cntR d c i ≤ 1)

theorem cget_eq (c : Col) (r : ℕ) (h : r < 4) : cget c r = some (c ⟨r, h⟩) := by
  simp [cget, h]

theorem lemU {m : ℕ} (x : Fin 4 → Fin (m+1) → Fin 2) (j : Fin (m+1)) (i : Fin 4) :
    cntU (fun i => x i j) i =
      (if h : 1 ≤ i.val then (if x ⟨i.val - 1, by omega⟩ j = x i j then 1 else 0) else 0) := by
  unfold cntU
  by_cases h : 1 ≤ i.val
  · rw [dif_pos h, cget_eq _ _ (by omega)]
    simp [h]
  · rw [dif_neg h]; simp [h]

theorem lemL {m : ℕ} (x : Fin 4 → Fin (m+1) → Fin 2) (j : Fin (m+1)) (i : Fin 4) :
    cntL (Lc none (fun j i => x i j) j) (fun i => x i j) i =
      (if h : 1 ≤ j.val then (if x i ⟨j.val - 1, by omega⟩ = x i j then 1 else 0) else 0) := by
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [cntL, Lc]
  · have e : (⟨(k.succ : Fin (m+1)).val - 1, by omega⟩ : Fin (m+1)) = k.castSucc := Fin.ext (by simp)
    have h1 : 1 ≤ (k.succ : Fin (m+1)).val := by simp
    simp only [Lc, Fin.cons_succ, cntL, dif_pos h1, e]

theorem lemR {m : ℕ} (x : Fin 4 → Fin (m+1) → Fin 2) (j : Fin (m+1)) (i : Fin 4) :
    cntR (Rc (fun j i => x i j) j) (fun i => x i j) i =
      (if h : 1 ≤ i.val ∧ j.val + 1 < m + 1 then
        (if x ⟨i.val - 1, by omega⟩ ⟨j.val + 1, h.2⟩ = x i j then 1 else 0) else 0) := by
  refine Fin.lastCases ?_ (fun k => ?_) j
  · have : ¬ (1 ≤ i.val ∧ (Fin.last m).val + 1 < m + 1) := by simp
    rw [dif_neg this]
    simp [cntR, Rc]
  · have h2 : (k.castSucc : Fin (m+1)).val + 1 < m + 1 := by simp
    have e : (⟨(k.castSucc : Fin (m+1)).val + 1, h2⟩ : Fin (m+1)) = k.succ := Fin.ext (by simp)
    simp only [Rc, Fin.snoc_castSucc, cntR]
    by_cases h : 1 ≤ i.val
    · rw [dif_pos ⟨h, h2⟩, cget_eq _ _ (by omega)]
      simp only [e, h, true_and]
      simp
    · rw [dif_neg (fun hh => h hh.1)]
      simp [h]

theorem eq_cnt {m : ℕ} (x : Fin 4 → Fin (m+1) → Fin 2) (i : Fin 4) (j : Fin (m+1)) :
    eqNbrs x i j = cntL (Lc none (fun j i => x i j) j) (fun i => x i j) i + cntU (fun i => x i j) i +
      cntR (Rc (fun j i => x i j) j) (fun i => x i j) i := by
  rw [eqNbrs_eq, lemL, lemU, lemR]

theorem cond_iff {m : ℕ} (x : Fin 4 → Fin (m+1) → Fin 2) :
    Cond x ↔ Gd TT none (fun j i => x i j) := by
  unfold Cond Gd TT
  constructor
  · intro h j
    simp only [decide_eq_true_eq]
    intro i
    rw [← eq_cnt]; exact h i j
  · intro h i j
    have := h j
    simp only [decide_eq_true_eq] at this
    rw [eq_cnt]; exact this i

theorem rmn_iff {m : ℕ} (x : Fin 4 → Fin (m+1) → Fin 2) : RowMajorNew x ↔ x 0 0 = 0 := by
  unfold RowMajorNew
  constructor
  · intro h
    by_contra hne
    have h1 : x 0 0 = 1 := by omega
    obtain ⟨i', j', hij, _⟩ := h 0 0 0 (by rw [h1]; exact Fin.zero_lt_one)
    rcases hij with h | ⟨_, h⟩
    · exact absurd h (by simp)
    · exact absurd h (by simp)
  · intro h i j u hu
    have hx : x i j = 1 := by
      have := (x i j).2
      have := u.2
      omega
    have hu0 : u = 0 := by
      have := (x i j).2
      have := u.2
      omega
    refine ⟨0, 0, ?_, by rw [hu0, h]⟩
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · subst hi; subst hj; rw [h] at hx; exact absurd hx (by simp)
      · right; exact ⟨hi.symm, Fin.pos_iff_ne_zero.mpr hj⟩
    · left; exact Fin.pos_iff_ne_zero.mpr hi

def S (m : ℕ) : ℕ := ∑ c : Col, if c 0 = 0 then W TT m none c else 0

open Classical in
theorem a_eq (m : ℕ) : a (m + 1) = S m := by
  unfold a S
  have e : ((Finset.univ : Finset (Fin 4 → Fin (m+1) → Fin 2)).filter (fun x => Cond x ∧ RowMajorNew x)).card =
      ((Finset.univ : Finset (Fin (m+1) → Col)).filter (fun y => Gd TT none y ∧ y 0 0 = 0)).card := by
    apply Finset.card_equiv (Equiv.piComm (fun (_ : Fin 4) (_ : Fin (m+1)) => Fin 2))
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.piComm_apply]
    rw [cond_iff, rmn_iff]; exact Iff.rfl
  rw [e, Finset.card_eq_sum_card_fiberwise (f := fun y : Fin (m+1) → Col => y 0) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro c _
  by_cases h : c 0 = 0
  · rw [if_pos h, ← cardW TT m none c]
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h3, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h2, by rw [h1]; exact h⟩, h1⟩
  · rw [if_neg h, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y hyP hy0
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hyP
    apply h
    rw [← hy0]
    exact hyP.2

theorem rec_S (n : ℕ) (cf : ℕ → ℤ)
    (h0 : ∀ p c, ∑ j ∈ Finset.range 5, cf j * (W TT (1 + j) p c : ℤ) = 0) :
    ∑ j ∈ Finset.range 5, cf j * (S (1 + n + j) : ℤ) = 0 := by
  have h := rec_gen TT 4 1 cf h0 n none
  have e : ∀ m, (S m : ℤ) = ∑ c : Col, if c 0 = 0 then (W TT m none c : ℤ) else 0 := by
    intro m; unfold S; push_cast; apply Finset.sum_congr rfl; intro c _; split_ifs <;> simp
  simp only [e, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro c _
  by_cases hc : c 0 = 0
  · simp only [hc, if_true]
    simpa [← Finset.mul_sum] using h c
  · simp [hc]

def cf : ℕ → ℤ := fun j => [(2 : ℤ), -7, 9, -5, 1].getD j 0

theorem h0 : ∀ p c, ∑ j ∈ Finset.range 5, cf j * (W TT (1 + j) p c : ℤ) = 0 := by
  decide +kernel

theorem hrecA (n : ℕ) : (a (n + 6) : ℚ) = 5 * a (n + 5) - 9 * a (n + 4) + 7 * a (n + 3) - 2 * a (n + 2) := by
  have h := rec_S n cf h0
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cf, List.getD_cons_zero, List.getD_cons_succ,
    zero_add, Nat.add_zero] at h
  have e1 : a (n + 6) = S (1 + n + 4) := by rw [show n + 6 = (1 + n + 4) + 1 by omega]; exact a_eq _
  have e2 : a (n + 5) = S (1 + n + 3) := by rw [show n + 5 = (1 + n + 3) + 1 by omega]; exact a_eq _
  have e3 : a (n + 4) = S (1 + n + 2) := by rw [show n + 4 = (1 + n + 2) + 1 by omega]; exact a_eq _
  have e4 : a (n + 3) = S (1 + n + 1) := by rw [show n + 3 = (1 + n + 1) + 1 by omega]; exact a_eq _
  have e5 : a (n + 2) = S (1 + n) := by rw [show n + 2 = (1 + n) + 1 by omega]; exact a_eq _
  rw [e1, e2, e3, e4, e5]
  have h2 : (S (1 + n + 4) : ℤ) = 5 * S (1 + n + 3) - 9 * S (1 + n + 2) + 7 * S (1 + n + 1) - 2 * S (1 + n) := by
    linarith
  exact_mod_cast h2

theorem v1 : a 1 = 8 := by rw [a_eq 0]; decide +kernel
theorem v2 : a 2 = 34 := by rw [a_eq 1]; decide +kernel
theorem v3 : a 3 = 95 := by rw [a_eq 2]; decide +kernel
theorem v4 : a 4 = 225 := by rw [a_eq 3]; decide +kernel
theorem v5 : a 5 = 494 := by rw [a_eq 4]; decide +kernel

theorem closedKey (k : ℕ) :
    (a (k + 2) : ℚ) = (-42 + 35 * 2 ^ (k + 2) - 13 * ((k + 2 : ℕ) : ℚ) - ((k + 2 : ℕ) : ℚ) ^ 2) / 2 ∧
    (a (k + 3) : ℚ) = (-42 + 35 * 2 ^ (k + 3) - 13 * ((k + 3 : ℕ) : ℚ) - ((k + 3 : ℕ) : ℚ) ^ 2) / 2 ∧
    (a (k + 4) : ℚ) = (-42 + 35 * 2 ^ (k + 4) - 13 * ((k + 4 : ℕ) : ℚ) - ((k + 4 : ℕ) : ℚ) ^ 2) / 2 ∧
    (a (k + 5) : ℚ) = (-42 + 35 * 2 ^ (k + 5) - 13 * ((k + 5 : ℕ) : ℚ) - ((k + 5 : ℕ) : ℚ) ^ 2) / 2 := by
  induction k with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [show 0 + 2 = 2 from rfl, v2]; norm_num
    · rw [show 0 + 3 = 3 from rfl, v3]; norm_num
    · rw [show 0 + 4 = 4 from rfl, v4]; norm_num
    · rw [show 0 + 5 = 5 from rfl, v5]; norm_num
  | succ k ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [show k + 1 + 2 = k + 3 by omega]; exact h2
    · rw [show k + 1 + 3 = k + 4 by omega]; exact h3
    · rw [show k + 1 + 4 = k + 5 by omega]; exact h4
    · rw [show k + 1 + 5 = k + 6 by omega, hrecA k, h1, h2, h3, h4]
      push_cast
      ring

theorem closed (n : ℕ) (hn : 1 < n) : (a n : ℚ) = (-42 + 35 * 2 ^ n - 13 * n - n ^ 2) / 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have := (closedKey k).1
  push_cast at this ⊢
  exact this

theorem hrQ (n : ℕ) (hn : 6 ≤ n) : (a n : ℚ) = 5 * a (n - 1) - 9 * a (n - 2) + 7 * a (n - 3) - 2 * a (n - 4) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  have f1 : k + 6 - 1 = k + 5 := by omega
  have f2 : k + 6 - 2 = k + 4 := by omega
  have f3 : k + 6 - 3 = k + 3 := by omega
  have f4 : k + 6 - 4 = k + 2 := by omega
  rw [f1, f2, f3, f4]
  exact hrecA k

theorem gfthm : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - PowerSeries.X) ^ 3 * (1 - 2 * PowerSeries.X)) =
    PowerSeries.X * (8 - 6 * PowerSeries.X - 3 * PowerSeries.X ^ 2 + 2 * PowerSeries.X ^ 4) := by
  have h := gf_gen (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) 4 5
    (fun j => [(1 : ℚ), -5, 9, -7, 2].getD j 0) (fun j => [(0 : ℚ), 8, -6, -3, 0, 2].getD j 0)
    ((1 - PowerSeries.X) ^ 3 * (1 - 2 * PowerSeries.X))
    (PowerSeries.X * (8 - 6 * PowerSeries.X - 3 * PowerSeries.X ^ 2 + 2 * PowerSeries.X ^ 4) : PowerSeries ℚ)
    (by simp [Finset.sum_range_succ, map_ofNat PowerSeries.C]; ring)
    (by simp [Finset.sum_range_succ, map_ofNat PowerSeries.C]; ring) (by norm_num) ?_ ?_
  · rw [h, mul_assoc, PowerSeries.inv_mul_cancel _ (by simp), mul_one]
  · intro n hn
    simp only [List.getD_eq_getElem?_getD]
    rcases n with _ | _ | _ | _ | _ | _ | k <;> simp_all
  · intro n
    by_cases hn : n ≤ 5
    · interval_cases n <;> simp [Finset.sum_range_succ, v1, v2, v3, v4, v5] <;> norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
      have r := hrecA k
      have g0 : k + 6 - 0 = k + 6 := by omega
      have g1 : k + 6 - 1 = k + 5 := by omega
      have g2 : k + 6 - 2 = k + 4 := by omega
      have g3 : k + 6 - 3 = k + 3 := by omega
      have g4 : k + 6 - 4 = k + 2 := by omega
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, g0, g1, g2, g3, g4]
      simp only [if_neg hn, if_pos (show 0 ≤ k + 6 by omega), if_pos (show 1 ≤ k + 6 by omega),
        if_pos (show 2 ≤ k + 6 by omega), if_pos (show 3 ≤ k + 6 by omega), if_pos (show 4 ≤ k + 6 by omega)]
      simp only [show k + 6 ≠ 0 by omega, show k + 5 ≠ 0 by omega, show k + 4 ≠ 0 by omega,
        show k + 3 ≠ 0 by omega, show k + 2 ≠ 0 by omega, if_false]
      norm_num [List.getD]
      linarith
end OMA.S_oeis_a208639

theorem OMA.solution : type_of% @OMA.S_oeis_a208639.main := by
  refine ⟨OMA.S_oeis_a208639.gfthm, ?_⟩
  intro n hn
  exact OMA.S_oeis_a208639.closed n hn

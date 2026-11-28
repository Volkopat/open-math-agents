import OMAStatements.S_oeis_a229582
import Mathlib

/-!
# A229582: proof of the closed form and g.f.

Values introduced in row major order: with u = the number of values used so far, a row σ is
admissible iff each entry is at most the current u, where u increases by one
whenever an entry equals it.
So the arrays are counted by a transfer recursion on the state (u, previous row, remaining
mistakes), restricted to the reachable states. Every state count is D G = (α + β m) 9^m + (terms at m = 0, 1), with integer
tables checked by `decide` against the transfer step; the start state gives
81 a(n) = (64 n - 12) 9^n for n ≥ 2.
-/


open OMA.S_oeis_a229582

namespace OMA.P_a229582

open Finset

abbrev Row := Fin 4 → Fin 3

def Aext {n : ℕ} (A : Fin n → Row) (i : ℕ) : Row := if h : i < n then A ⟨i, h⟩ else fun _ => 0

lemma Aext_fin {n : ℕ} (A : Fin n → Row) (r : Fin n) : A r = Aext A r.1 := by simp [Aext]

lemma Aext_cons0 {m : ℕ} (σ : Row) (B : Fin m → Row) :
    Aext (Fin.cons σ B : Fin (m + 1) → Row) 0 = σ := by simp [Aext]

lemma Aext_cons_succ {m : ℕ} (σ : Row) (B : Fin m → Row) (i : ℕ) :
    Aext (Fin.cons σ B : Fin (m + 1) → Row) (i + 1) = Aext B i := by
  unfold Aext
  by_cases h : i < m
  · rw [dif_pos (by omega), dif_pos h]
    exact Fin.cons_succ (α := fun _ => Row) σ B ⟨i, h⟩
  · rw [dif_neg (by omega), dif_neg h]

def loc (σ : Row) : ℕ := ∑ c : Fin 3, if σ ⟨c.1, by omega⟩ = σ ⟨c.1 + 1, by omega⟩ then 1 else 0
def pair (ρ σ : Row) : ℕ := ∑ c : Fin 3, if ρ ⟨c.1 + 1, by omega⟩ = σ ⟨c.1, by omega⟩ then 1 else 0

def mG {n : ℕ} (A : Fin n → Row) : ℕ :=
  (∑ r ∈ range n, loc (Aext A r)) + ∑ r ∈ range (n - 1), pair (Aext A r) (Aext A (r + 1))

lemma mist_eq {n : ℕ} (A : Fin n → Row) : mistakes n A = mG A := by
  unfold mistakes mG
  rw [Finset.sum_range, Finset.sum_range]
  simp only [Aext_fin A]
  rfl

lemma mG_cons {m : ℕ} (σ : Row) (B : Fin m → Row) :
    mG (Fin.cons σ B : Fin (m + 1) → Row) = loc σ + (if 0 < m then pair σ (Aext B 0) else 0) + mG B := by
  unfold mG
  rcases m with _ | k
  · simp [Aext_cons0]
  · simp only [Finset.sum_range_succ', Aext_cons0, Aext_cons_succ, show k + 1 + 1 - 1 = k + 1 by omega,
      show k + 1 - 1 = k by omega, if_pos (Nat.succ_pos k)]
    ring

def fl {n : ℕ} (A : Fin n → Row) (i : ℕ) : ℕ := (Aext A (i / 4) ⟨i % 4, Nat.mod_lt _ (by norm_num)⟩).val

def RGN (u N : ℕ) (s : ℕ → ℕ) : Prop := ∀ i < N, ∀ v < s i, v < u ∨ ∃ j < i, s j = v

lemma fl_eq {n : ℕ} (A : Fin n → Row) (i : ℕ) (_hi : i < 4 * n) (p1 : i / 4 < n) (p2 : i % 4 < 4) :
    (A ⟨i / 4, p1⟩ ⟨i % 4, p2⟩).val = fl A i := by
  simp [fl, Aext, p1]

lemma rm_iff {n : ℕ} (A : Fin n → Row) : isRowMajor n A ↔ RGN 0 (4 * n) (fl A) := by
  unfold isRowMajor RGN
  constructor
  · intro h i hi v hv
    right
    have := h ⟨i, hi⟩ v (by rw [fl_eq A i hi]; exact hv)
    obtain ⟨j, hj, e⟩ := this
    exact ⟨j.1, hj, by rw [← fl_eq A j.1 j.2]; exact e⟩
  · intro h i v hv
    rw [fl_eq A i.1 i.2] at hv
    rcases h i.1 i.2 v hv with h0 | ⟨j, hj, e⟩
    · omega
    · exact ⟨⟨j, by omega⟩, hj, by rw [fl_eq A j (by omega)]; exact e⟩

lemma RGN_succ (u N : ℕ) (s : ℕ → ℕ) :
    RGN u (N + 1) s ↔ s 0 ≤ u ∧ RGN (if s 0 = u then u + 1 else u) N (fun i => s (i + 1)) := by
  unfold RGN
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · by_contra hc
      rcases h 0 (by omega) u (by omega) with h1 | ⟨j, hj, -⟩
      · omega
      · omega
    · intro i hi v hv
      have h0 : s 0 ≤ u := by
        by_contra hc
        rcases h 0 (by omega) u (by omega) with h1 | ⟨j, hj, -⟩
        · omega
        · omega
      rcases h (i + 1) (by omega) v hv with h1 | ⟨j, hj, e⟩
      · left; split_ifs <;> omega
      · rcases j with _ | j
        · left; split_ifs <;> omega
        · right; exact ⟨j, by omega, e⟩
  · rintro ⟨h0, h⟩ i hi v hv
    rcases i with _ | i
    · left; omega
    · rcases h i (by omega) v hv with h1 | ⟨j, hj, e⟩
      · split_ifs at h1 with hu
        · by_cases hv' : v < u
          · left; exact hv'
          · right; exact ⟨0, by omega, by omega⟩
        · left; exact h1
      · right; exact ⟨j + 1, by omega, e⟩

lemma fl_cons_ss {m : ℕ} (σ : Row) (B : Fin m → Row) (i : ℕ) :
    fl (Fin.cons σ B : Fin (m + 1) → Row) (i + 4) = fl B i := by
  unfold fl
  have e1 : (i + 4) / 4 = i / 4 + 1 := by omega
  have e2 : (⟨(i + 4) % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4) = ⟨i % 4, Nat.mod_lt _ (by norm_num)⟩ :=
    Fin.ext (by simp only; omega)
  rw [e1, e2, Aext_cons_succ]

def st (u : ℕ) (x : Fin 3) : ℕ := if x.val = u then u + 1 else u
def okR (u : ℕ) (σ : Row) : Prop := (σ 0).val ≤ u ∧ (σ 1).val ≤ st u (σ 0) ∧ (σ 2).val ≤ st (st u (σ 0)) (σ 1) ∧ (σ 3).val ≤ st (st (st u (σ 0)) (σ 1)) (σ 2)
def nx (u : ℕ) (σ : Row) : ℕ := st (st (st (st u (σ 0)) (σ 1)) (σ 2)) (σ 3)

instance (u : ℕ) (σ : Row) : Decidable (okR u σ) := by unfold okR; infer_instance

lemma rm_cons {m : ℕ} (u : ℕ) (σ : Row) (B : Fin m → Row) :
    RGN u (4 * (m + 1)) (fl (Fin.cons σ B : Fin (m + 1) → Row)) ↔ okR u σ ∧ RGN (nx u σ) (4 * m) (fl B) := by
  rw [show 4 * (m + 1) = 4 * m + 1 + 1 + 1 + 1 by ring, RGN_succ, RGN_succ, RGN_succ, RGN_succ]
  have f0 : fl (Fin.cons σ B : Fin (m + 1) → Row) (0) = (σ 0).val := by simp [fl, Aext]
  have f1 : fl (Fin.cons σ B : Fin (m + 1) → Row) (0 + 1) = (σ 1).val := by simp [fl, Aext]
  have f2 : fl (Fin.cons σ B : Fin (m + 1) → Row) (0 + 1 + 1) = (σ 2).val := by simp [fl, Aext]
  have f3 : fl (Fin.cons σ B : Fin (m + 1) → Row) (0 + 1 + 1 + 1) = (σ 3).val := by simp [fl, Aext]
  simp only [f0, f1, f2, f3, fl_cons_ss, okR, nx, st, and_assoc]
  exact Iff.rfl

def cntF (m : ℕ) (P : (Fin m → Row) → Prop) [DecidablePred P] : ℕ := ((univ : Finset (Fin m → Row)).filter P).card

lemma cntF_succ (m : ℕ) (P : (Fin (m + 1) → Row) → Prop) [DecidablePred P] :
    cntF (m + 1) P = ∑ σ : Row, cntF m (fun B => P (Fin.cons σ B)) := by
  unfold cntF
  rw [Finset.card_filter, ← (Fin.consEquiv (fun _ => Row)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.card_filter]
  rfl

lemma cntF_congr (m : ℕ) (P Q : (Fin m → Row) → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ B, P B ↔ Q B) : cntF m P = cntF m Q := by
  unfold cntF; congr 1; ext B; simp [h]

def pairO (p : Option Row) (σ : Row) : ℕ :=
  match p with
  | none => 0
  | some ρ => pair ρ σ

def Mx {m : ℕ} (p : Option Row) (B : Fin m → Row) : ℕ := mG B + (if 0 < m then pairO p (Aext B 0) else 0)

lemma Mx_cons {m : ℕ} (p : Option Row) (σ : Row) (B : Fin m → Row) :
    Mx p (Fin.cons σ B : Fin (m + 1) → Row) = loc σ + pairO p σ + Mx (some σ) B := by
  unfold Mx
  rw [mG_cons, if_pos (Nat.succ_pos m), Aext_cons0]
  simp only [pairO]
  ring

instance (u N : ℕ) (s : ℕ → ℕ) : Decidable (RGN u N s) := by unfold RGN; infer_instance

def G (m u : ℕ) (p : Option Row) (c : ℕ) : ℕ := cntF m (fun B => RGN u (4 * m) (fl B) ∧ Mx p B = c)

lemma G_succ (m u : ℕ) (p : Option Row) (c : ℕ) :
    G (m + 1) u p c = ∑ σ : Row, if okR u σ ∧ loc σ + pairO p σ ≤ c then
      G m (nx u σ) (some σ) (c - (loc σ + pairO p σ)) else 0 := by
  unfold G
  rw [cntF_succ]
  refine Finset.sum_congr rfl fun σ _ => ?_
  split_ifs with h
  · refine cntF_congr _ _ _ fun B => ?_
    rw [rm_cons, Mx_cons]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h2, by omega⟩
    · rintro ⟨h2, h3⟩; exact ⟨⟨h.1, h2⟩, by omega⟩
  · unfold cntF
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro B _
    rw [rm_cons, Mx_cons]
    intro hh
    exact h ⟨hh.1.1, by omega⟩

lemma G_zero (u : ℕ) (p : Option Row) (c : ℕ) : G 0 u p c = if c = 0 then 1 else 0 := by
  unfold G cntF
  have hR : ∀ B : Fin 0 → Row, RGN u (4 * 0) (fl B) := fun B i hi => by omega
  have hM : ∀ B : Fin 0 → Row, Mx p B = 0 := fun B => by simp [Mx, mG]
  split_ifs with hc
  · rw [Finset.card_eq_one]
    refine ⟨fun i => i.elim0, ?_⟩
    ext B
    simp only [mem_filter, mem_univ, true_and, mem_singleton, hR, hM, hc]
    constructor
    · intro _; funext i; exact i.elim0
    · intro _; trivial
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro B _
    simp [hM, Ne.symm hc]

lemma a_eq (n : ℕ) (hn : 1 ≤ n) : a n = G n 0 none 1 := by
  unfold a
  rw [if_neg (by omega), Fintype.card_subtype]
  unfold G cntF
  congr 1
  apply Finset.filter_congr
  intro A _
  rw [mist_eq, rm_iff]
  simp only [Mx, pairO]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, by simpa using h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨by simpa using h2, h1⟩


def dec (k : Fin 81) : Row := fun t => ⟨k.val / 3 ^ t.val % 3, Nat.mod_lt _ (by norm_num)⟩

def encR : Row ≃ Fin 81 where
  toFun σ := ⟨1 * (σ 0).val + 3 * (σ 1).val + 9 * (σ 2).val + 27 * (σ 3).val, by omega⟩
  invFun := dec
  left_inv := by decide +kernel
  right_inv := by decide +kernel

lemma sumR (g : Row → ℤ) : ∑ σ : Row, g σ = ∑ k : Fin 81, g (dec k) := by
  rw [← encR.symm.sum_comp]
  rfl

def decO (p : ℕ) : Option Row := if h : p < 81 then some (dec ⟨p, h⟩) else none

def TA0 : List (List (List ℤ)) := [[[0, 18], [0, 18], [0, 18], [18, 9], [18, 9], [18, 9], [18, 9], [18, 9], [18, 9], [0, 0], [0, 0], [0, 0], [0, 36], [0, 36], [0, 36], [0, 36], [0, 36], [0, 36], [0, 18], [0, 18], [0, 18], [18, 27], [18, 27], [18, 27], [18, 27], [18, 27], [18, 27], [0, 36], [0, 36], [0, 36], [36, -42], [36, -42], [36, -42], [36, -42], [36, -42], [36, -42], [0, 0], [0, 0], [0, 0], [0, 36], [0, 36], [0, 36], [0, 36], [0, 36], [0, 36], [0, 36], [0, 36], [0, 36], [36, -42], [36, -42], [36, -42], [36, -42], [36, -42], [36, -42], [0, 18], [0, 18], [0, 18], [18, 9], [18, 9], [18, 9], [18, 9], [18, 9], [18, 9], [0, 0], [0, 0], [0, 0], [0, 36], [0, 36], [0, 36], [0, 36], [0, 36], [0, 36], [0, 18], [0, 18], [0, 18], [18, 27], [18, 27], [18, 27], [18, 27], [18, 27], [18, 27], [36, -12]], [[18, 81], [18, 81], [18, 81], [18, 27], [18, 27], [18, 27], [36, 72], [36, 72], [36, 72], [54, -33], [54, -33], [54, -33], [0, 90], [0, 90], [0, 90], [54, 3], [54, 3], [54, 3], [36, 12], [36, 12], [36, 12], [18, 63], [18, 63], [18, 63], [54, 21], [54, 21], [54, 21], [18, 99], [18, 99], [18, 99], [36, -24], [36, -24], [36, -24], [54, 21], [54, 21], [54, 21], [36, 18], [36, 18], [36, 18], [0, 72], [0, 72], [0, 72], [36, 54], [36, 54], [36, 54], [18, 99], [18, 99], [18, 99], [36, -24], [36, -24], [36, -24], [54, 21], [54, 21], [54, 21], [36, 12], [36, 12], [36, 12], [18, 45], [18, 45], [18, 45], [54, 3], [54, 3], [54, 3], [54, -33], [54, -33], [54, -33], [0, 90], [0, 90], [0, 90], [54, 3], [54, 3], [54, 3], [18, 81], [18, 81], [18, 81], [18, 45], [18, 45], [18, 45], [36, 90], [36, 90], [36, 90], [108, -36]], [[36, 162], [36, 162], [36, 162], [54, 99], [54, 99], [54, 99], [54, 99], [54, 99], [54, 99], [90, -21], [90, -21], [90, -21], [54, 111], [54, 111], [54, 111], [72, 66], [72, 66], [72, 66], [90, -21], [90, -21], [90, -21], [72, 66], [72, 66], [72, 66], [54, 111], [54, 111], [54, 111], [54, 111], [54, 111], [54, 111], [90, -21], [90, -21], [90, -21], [72, 66], [72, 66], [72, 66], [54, 99], [54, 99], [54, 99], [36, 162], [36, 162], [36, 162], [54, 99], [54, 99], [54, 99], [72, 66], [72, 66], [72, 66], [90, -21], [90, -21], [90, -21], [54, 111], [54, 111], [54, 111], [54, 111], [54, 111], [54, 111], [72, 66], [72, 66], [72, 66], [90, -21], [90, -21], [90, -21], [72, 66], [72, 66], [72, 66], [54, 111], [54, 111], [54, 111], [90, -21], [90, -21], [90, -21], [54, 99], [54, 99], [54, 99], [54, 99], [54, 99], [54, 99], [36, 162], [36, 162], [36, 162], [216, -72]], [[36, 162], [36, 162], [36, 162], [54, 99], [54, 99], [54, 99], [54, 99], [54, 99], [54, 99], [90, -21], [90, -21], [90, -21], [54, 111], [54, 111], [54, 111], [72, 66], [72, 66], [72, 66], [90, -21], [90, -21], [90, -21], [72, 66], [72, 66], [72, 66], [54, 111], [54, 111], [54, 111], [54, 111], [54, 111], [54, 111], [90, -21], [90, -21], [90, -21], [72, 66], [72, 66], [72, 66], [54, 99], [54, 99], [54, 99], [36, 162], [36, 162], [36, 162], [54, 99], [54, 99], [54, 99], [72, 66], [72, 66], [72, 66], [90, -21], [90, -21], [90, -21], [54, 111], [54, 111], [54, 111], [54, 111], [54, 111], [54, 111], [72, 66], [72, 66], [72, 66], [90, -21], [90, -21], [90, -21], [72, 66], [72, 66], [72, 66], [54, 111], [54, 111], [54, 111], [90, -21], [90, -21], [90, -21], [54, 99], [54, 99], [54, 99], [54, 99], [54, 99], [54, 99], [36, 162], [36, 162], [36, 162], [216, -72]]]
def TA1 : List (List (List ℤ)) := [[[0, 0], [0, 0], [0, 0], [0, 32], [0, 32], [0, 32], [0, 32], [0, 32], [0, 32], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 32], [0, 32], [0, 32], [0, 32], [0, 32], [0, 32], [0, 0], [0, 0], [0, 0], [0, 64], [0, 64], [0, 64], [0, 64], [0, 64], [0, 64], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 64], [0, 64], [0, 64], [0, 64], [0, 64], [0, 64], [0, 0], [0, 0], [0, 0], [0, 32], [0, 32], [0, 32], [0, 32], [0, 32], [0, 32], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 32], [0, 32], [0, 32], [0, 32], [0, 32], [0, 32], [0, 64]], [[0, 32], [0, 32], [0, 32], [0, 32], [0, 32], [0, 32], [0, 64], [0, 64], [0, 64], [0, 96], [0, 96], [0, 96], [0, 0], [0, 0], [0, 0], [0, 96], [0, 96], [0, 96], [0, 64], [0, 64], [0, 64], [0, 32], [0, 32], [0, 32], [0, 96], [0, 96], [0, 96], [0, 32], [0, 32], [0, 32], [0, 64], [0, 64], [0, 64], [0, 96], [0, 96], [0, 96], [0, 64], [0, 64], [0, 64], [0, 0], [0, 0], [0, 0], [0, 64], [0, 64], [0, 64], [0, 32], [0, 32], [0, 32], [0, 64], [0, 64], [0, 64], [0, 96], [0, 96], [0, 96], [0, 64], [0, 64], [0, 64], [0, 32], [0, 32], [0, 32], [0, 96], [0, 96], [0, 96], [0, 96], [0, 96], [0, 96], [0, 0], [0, 0], [0, 0], [0, 96], [0, 96], [0, 96], [0, 32], [0, 32], [0, 32], [0, 32], [0, 32], [0, 32], [0, 64], [0, 64], [0, 64], [0, 192]], [[0, 64], [0, 64], [0, 64], [0, 96], [0, 96], [0, 96], [0, 96], [0, 96], [0, 96], [0, 160], [0, 160], [0, 160], [0, 96], [0, 96], [0, 96], [0, 128], [0, 128], [0, 128], [0, 160], [0, 160], [0, 160], [0, 128], [0, 128], [0, 128], [0, 96], [0, 96], [0, 96], [0, 96], [0, 96], [0, 96], [0, 160], [0, 160], [0, 160], [0, 128], [0, 128], [0, 128], [0, 96], [0, 96], [0, 96], [0, 64], [0, 64], [0, 64], [0, 96], [0, 96], [0, 96], [0, 128], [0, 128], [0, 128], [0, 160], [0, 160], [0, 160], [0, 96], [0, 96], [0, 96], [0, 96], [0, 96], [0, 96], [0, 128], [0, 128], [0, 128], [0, 160], [0, 160], [0, 160], [0, 128], [0, 128], [0, 128], [0, 96], [0, 96], [0, 96], [0, 160], [0, 160], [0, 160], [0, 96], [0, 96], [0, 96], [0, 96], [0, 96], [0, 96], [0, 64], [0, 64], [0, 64], [0, 384]], [[0, 64], [0, 64], [0, 64], [0, 96], [0, 96], [0, 96], [0, 96], [0, 96], [0, 96], [0, 160], [0, 160], [0, 160], [0, 96], [0, 96], [0, 96], [0, 128], [0, 128], [0, 128], [0, 160], [0, 160], [0, 160], [0, 128], [0, 128], [0, 128], [0, 96], [0, 96], [0, 96], [0, 96], [0, 96], [0, 96], [0, 160], [0, 160], [0, 160], [0, 128], [0, 128], [0, 128], [0, 96], [0, 96], [0, 96], [0, 64], [0, 64], [0, 64], [0, 96], [0, 96], [0, 96], [0, 128], [0, 128], [0, 128], [0, 160], [0, 160], [0, 160], [0, 96], [0, 96], [0, 96], [0, 96], [0, 96], [0, 96], [0, 128], [0, 128], [0, 128], [0, 160], [0, 160], [0, 160], [0, 128], [0, 128], [0, 128], [0, 96], [0, 96], [0, 96], [0, 160], [0, 160], [0, 160], [0, 96], [0, 96], [0, 96], [0, 96], [0, 96], [0, 96], [0, 64], [0, 64], [0, 64], [0, 384]]]
def TD0 : List (List (List ℤ)) := [[[81, -18], [81, -18], [81, -18], [63, -9], [63, -9], [63, -9], [63, -9], [63, -9], [63, -9], [81, 0], [81, 0], [81, 0], [81, -36], [81, -36], [81, -36], [81, -36], [81, -36], [81, -36], [81, -18], [81, -18], [81, -18], [63, -27], [63, -27], [63, -27], [63, -27], [63, -27], [63, -27], [81, -36], [81, -36], [81, -36], [45, 42], [45, 42], [45, 42], [45, 42], [45, 42], [45, 42], [81, 0], [81, 0], [81, 0], [81, -36], [81, -36], [81, -36], [81, -36], [81, -36], [81, -36], [81, -36], [81, -36], [81, -36], [45, 42], [45, 42], [45, 42], [45, 42], [45, 42], [45, 42], [81, -18], [81, -18], [81, -18], [63, -9], [63, -9], [63, -9], [63, -9], [63, -9], [63, -9], [81, 0], [81, 0], [81, 0], [81, -36], [81, -36], [81, -36], [81, -36], [81, -36], [81, -36], [81, -18], [81, -18], [81, -18], [63, -27], [63, -27], [63, -27], [63, -27], [63, -27], [63, -27], [45, 12]], [[63, -81], [63, -81], [63, -81], [63, -27], [63, -27], [63, -27], [45, -72], [45, -72], [45, -72], [27, 33], [27, 33], [27, 33], [81, -90], [81, -90], [81, -90], [27, -3], [27, -3], [27, -3], [45, -12], [45, -12], [45, -12], [63, -63], [63, -63], [63, -63], [27, -21], [27, -21], [27, -21], [63, -99], [63, -99], [63, -99], [45, 24], [45, 24], [45, 24], [27, -21], [27, -21], [27, -21], [45, -18], [45, -18], [45, -18], [81, -72], [81, -72], [81, -72], [45, -54], [45, -54], [45, -54], [63, -99], [63, -99], [63, -99], [45, 24], [45, 24], [45, 24], [27, -21], [27, -21], [27, -21], [45, -12], [45, -12], [45, -12], [63, -45], [63, -45], [63, -45], [27, -3], [27, -3], [27, -3], [27, 33], [27, 33], [27, 33], [81, -90], [81, -90], [81, -90], [27, -3], [27, -3], [27, -3], [63, -81], [63, -81], [63, -81], [63, -45], [63, -45], [63, -45], [45, -90], [45, -90], [45, -90], [-27, 36]], [[45, -162], [45, -162], [45, -162], [27, -99], [27, -99], [27, -99], [27, -99], [27, -99], [27, -99], [-9, 21], [-9, 21], [-9, 21], [27, -111], [27, -111], [27, -111], [9, -66], [9, -66], [9, -66], [-9, 21], [-9, 21], [-9, 21], [9, -66], [9, -66], [9, -66], [27, -111], [27, -111], [27, -111], [27, -111], [27, -111], [27, -111], [-9, 21], [-9, 21], [-9, 21], [9, -66], [9, -66], [9, -66], [27, -99], [27, -99], [27, -99], [45, -162], [45, -162], [45, -162], [27, -99], [27, -99], [27, -99], [9, -66], [9, -66], [9, -66], [-9, 21], [-9, 21], [-9, 21], [27, -111], [27, -111], [27, -111], [27, -111], [27, -111], [27, -111], [9, -66], [9, -66], [9, -66], [-9, 21], [-9, 21], [-9, 21], [9, -66], [9, -66], [9, -66], [27, -111], [27, -111], [27, -111], [-9, 21], [-9, 21], [-9, 21], [27, -99], [27, -99], [27, -99], [27, -99], [27, -99], [27, -99], [45, -162], [45, -162], [45, -162], [-135, 72]], [[45, -162], [45, -162], [45, -162], [27, -99], [27, -99], [27, -99], [27, -99], [27, -99], [27, -99], [-9, 21], [-9, 21], [-9, 21], [27, -111], [27, -111], [27, -111], [9, -66], [9, -66], [9, -66], [-9, 21], [-9, 21], [-9, 21], [9, -66], [9, -66], [9, -66], [27, -111], [27, -111], [27, -111], [27, -111], [27, -111], [27, -111], [-9, 21], [-9, 21], [-9, 21], [9, -66], [9, -66], [9, -66], [27, -99], [27, -99], [27, -99], [45, -162], [45, -162], [45, -162], [27, -99], [27, -99], [27, -99], [9, -66], [9, -66], [9, -66], [-9, 21], [-9, 21], [-9, 21], [27, -111], [27, -111], [27, -111], [27, -111], [27, -111], [27, -111], [9, -66], [9, -66], [9, -66], [-9, 21], [-9, 21], [-9, 21], [9, -66], [9, -66], [9, -66], [27, -111], [27, -111], [27, -111], [-9, 21], [-9, 21], [-9, 21], [27, -99], [27, -99], [27, -99], [27, -99], [27, -99], [27, -99], [45, -162], [45, -162], [45, -162], [-135, 72]]]
def TD1 : List (List (List ℤ)) := [[[0, 0], [0, 0], [0, 0], [0, 36], [0, 36], [0, 36], [0, 36], [0, 36], [0, 36], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 36], [0, 36], [0, 36], [0, 36], [0, 36], [0, 36], [0, 0], [0, 0], [0, 0], [0, -36], [0, -36], [0, -36], [0, -36], [0, -36], [0, -36], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -36], [0, -36], [0, -36], [0, -36], [0, -36], [0, -36], [0, 0], [0, 0], [0, 0], [0, 36], [0, 36], [0, 36], [0, 36], [0, 36], [0, 36], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 36], [0, 36], [0, 36], [0, 36], [0, 36], [0, 36], [0, 18]], [[0, 36], [0, 36], [0, 36], [0, 36], [0, 36], [0, 36], [0, 72], [0, 72], [0, 72], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -36], [0, -36], [0, -36], [0, 36], [0, 36], [0, 36], [0, 0], [0, 0], [0, 0], [0, 36], [0, 36], [0, 36], [0, -36], [0, -36], [0, -36], [0, 0], [0, 0], [0, 0], [0, 72], [0, 72], [0, 72], [0, 0], [0, 0], [0, 0], [0, 72], [0, 72], [0, 72], [0, 36], [0, 36], [0, 36], [0, -36], [0, -36], [0, -36], [0, 0], [0, 0], [0, 0], [0, -36], [0, -36], [0, -36], [0, 36], [0, 36], [0, 36], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 36], [0, 36], [0, 36], [0, 36], [0, 36], [0, 36], [0, 72], [0, 72], [0, 72], [0, 54]], [[0, 72], [0, 72], [0, 72], [0, 108], [0, 108], [0, 108], [0, 108], [0, 108], [0, 108], [0, -36], [0, -36], [0, -36], [0, 0], [0, 0], [0, 0], [0, 36], [0, 36], [0, 36], [0, -36], [0, -36], [0, -36], [0, 36], [0, 36], [0, 36], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -36], [0, -36], [0, -36], [0, 36], [0, 36], [0, 36], [0, 108], [0, 108], [0, 108], [0, 72], [0, 72], [0, 72], [0, 108], [0, 108], [0, 108], [0, 36], [0, 36], [0, 36], [0, -36], [0, -36], [0, -36], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 36], [0, 36], [0, 36], [0, -36], [0, -36], [0, -36], [0, 36], [0, 36], [0, 36], [0, 0], [0, 0], [0, 0], [0, -36], [0, -36], [0, -36], [0, 108], [0, 108], [0, 108], [0, 108], [0, 108], [0, 108], [0, 72], [0, 72], [0, 72], [0, 108]], [[0, 72], [0, 72], [0, 72], [0, 108], [0, 108], [0, 108], [0, 108], [0, 108], [0, 108], [0, -36], [0, -36], [0, -36], [0, 0], [0, 0], [0, 0], [0, 36], [0, 36], [0, 36], [0, -36], [0, -36], [0, -36], [0, 36], [0, 36], [0, 36], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, -36], [0, -36], [0, -36], [0, 36], [0, 36], [0, 36], [0, 108], [0, 108], [0, 108], [0, 72], [0, 72], [0, 72], [0, 108], [0, 108], [0, 108], [0, 36], [0, 36], [0, 36], [0, -36], [0, -36], [0, -36], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 36], [0, 36], [0, 36], [0, -36], [0, -36], [0, -36], [0, 36], [0, 36], [0, 36], [0, 0], [0, 0], [0, 0], [0, -36], [0, -36], [0, -36], [0, 108], [0, 108], [0, 108], [0, 108], [0, 108], [0, 108], [0, 72], [0, 72], [0, 72], [0, 108]]]

def tk (u p c : ℕ) : ℕ := u * 164 + p * 2 + c

def CA0 (u p c : ℕ) : ℤ := ((TA0.getD u []).getD p []).getD c 0
def CA1 (u p c : ℕ) : ℤ := ((TA1.getD u []).getD p []).getD c 0
def CD0 (u p c : ℕ) : ℤ := ((TD0.getD u []).getD p []).getD c 0
def CD1 (u p c : ℕ) : ℤ := ((TD1.getD u []).getD p []).getD c 0

def locE (σ : Row) : ℕ := (if σ 0 = σ 1 then 1 else 0) + (if σ 1 = σ 2 then 1 else 0) + (if σ 2 = σ 3 then 1 else 0)
def pairE (ρ σ : Row) : ℕ := (if ρ 1 = σ 0 then 1 else 0) + (if ρ 2 = σ 1 then 1 else 0) + (if ρ 3 = σ 2 then 1 else 0)
def pairOE (p : Option Row) (σ : Row) : ℕ :=
  match p with
  | none => 0
  | some ρ => pairE ρ σ

lemma loc_eq (σ : Row) : loc σ = locE σ := by
  unfold loc locE
  try simp only [Fin.sum_univ_two, Fin.sum_univ_three]
  try rfl

lemma pairO_eq (p : Option Row) (σ : Row) : pairO p σ = pairOE p σ := by
  cases p with
  | none => rfl
  | some ρ =>
    unfold pairO pairOE pair pairE
    try simp only [Fin.sum_univ_two, Fin.sum_univ_three]
    try rfl

def TT (u p c : ℕ) (k : Fin 81) : ℤ :=
  if okR u (dec k) ∧ locE (dec k) + pairOE (decO p) (dec k) ≤ c then 1 else 0

def kk (p : ℕ) (k : Fin 81) : ℕ := locE (dec k) + pairOE (decO p) (dec k)

def Vld (u p : ℕ) : Prop := (u = 0 ∧ p = 81) ∨ (1 ≤ u ∧ p < 81 ∧ ∀ t < 4, p / 3 ^ t % 3 < u)

instance (u p : ℕ) : Decidable (Vld u p) := by unfold Vld; infer_instance

lemma vld_next : ∀ u : Fin 4, ∀ k : Fin 81, okR u (dec k) → Vld (nx u (dec k)) k.val := by
  decide +kernel

lemma coA0 : ∀ u : Fin 4, ∀ p : Fin 82, ∀ c : Fin 2, Vld u p →
    ∑ k : Fin 81, TT u p c k * CA0 (nx u (dec k)) k.val (c - kk p k) = 9 * CA0 u.val p.val c.val + 9 * CA1 u.val p.val c.val := by
  decide +kernel
lemma coA1 : ∀ u : Fin 4, ∀ p : Fin 82, ∀ c : Fin 2, Vld u p →
    ∑ k : Fin 81, TT u p c k * CA1 (nx u (dec k)) k.val (c - kk p k) = 9 * CA1 u.val p.val c.val := by
  decide +kernel
lemma coD0 : ∀ u : Fin 4, ∀ p : Fin 82, ∀ c : Fin 2, Vld u p →
    ∑ k : Fin 81, TT u p c k * CD0 (nx u (dec k)) k.val (c - kk p k) = CD1 u.val p.val c.val := by
  decide +kernel
lemma coD1 : ∀ u : Fin 4, ∀ p : Fin 82, ∀ c : Fin 2, Vld u p →
    ∑ k : Fin 81, TT u p c k * CD1 (nx u (dec k)) k.val (c - kk p k) = 0 := by
  decide +kernel
lemma co_base : ∀ u : Fin 4, ∀ p : Fin 82, ∀ c : Fin 2,
    (if c.val = 0 then (81 : ℤ) else 0) = CA0 u p c + CD0 u p c := by decide +kernel

lemma nx_le (u : ℕ) (hu : u ≤ 3) (σ : Row) (h : okR u σ) : nx u σ ≤ 3 := by
  unfold okR at h
  unfold nx st
  have := (σ 0).isLt
  have := (σ 1).isLt
  have := (σ 2).isLt
  have := (σ 3).isLt
  split_ifs <;> omega

def del (t m : ℕ) : ℤ := if m = t then 1 else 0

def EE (m u p c : ℕ) : ℤ :=
  (CA0 u p c * (m : ℤ) ^ 0 + CA1 u p c * (m : ℤ) ^ 1) * 9 ^ m + CD0 u p c * del 0 m + CD1 u p c * del 1 m

lemma decO_k (k : Fin 81) : decO k.val = some (dec k) := by simp [decO]

lemma G_closed (m : ℕ) : ∀ u : Fin 4, ∀ p : Fin 82, ∀ c : Fin 2, Vld u p →
    (81 : ℤ) * G m u (decO p) c = EE m u p c := by
  induction m with
  | zero =>
    intro u p c _
    rw [G_zero]
    have := co_base u p c
    simp only [EE, del]
    by_cases hc : (c : ℕ) = 0
    · simp only [hc, if_true] at this ⊢
      push_cast
      simp only [pow_zero, mul_one, if_true, Nat.cast_zero]
      simp
      linarith
    · simp only [hc, if_false] at this ⊢
      push_cast
      simp
      linarith
  | succ m ih =>
    intro u p c hv
    rw [G_succ]
    push_cast
    rw [Finset.mul_sum, sumR]
    have e : ∀ k : Fin 81, (81 : ℤ) * (if okR u (dec k) ∧ loc (dec k) + pairO (decO p) (dec k) ≤ c then
        (G m (nx u (dec k)) (some (dec k)) (c - (loc (dec k) + pairO (decO p) (dec k))) : ℤ) else 0) =
        TT u p c k * EE m (nx u (dec k)) k.val (c - kk p k) := by
      intro k
      rw [loc_eq, pairO_eq]
      unfold TT kk
      split_ifs with h
      · have hu := nx_le u (by omega) (dec k) h.1
        have := ih ⟨nx u (dec k), by omega⟩ ⟨k.val, by omega⟩ ⟨c - (locE (dec k) + pairOE (decO p) (dec k)), by omega⟩
          (vld_next ⟨u, by omega⟩ k h.1)
        simp only [decO_k] at this
        rw [this]; ring
      · ring
    simp only [e]
    have hs : ∀ k : Fin 81, TT u p c k * EE m (nx u (dec k)) k.val (c - kk p k) =
        (TT u p c k * CA0 (nx u (dec k)) k.val (c - kk p k)) * ((m : ℤ) ^ 0 * 9 ^ m) + (TT u p c k * CA1 (nx u (dec k)) k.val (c - kk p k)) * ((m : ℤ) ^ 1 * 9 ^ m) + (TT u p c k * CD0 (nx u (dec k)) k.val (c - kk p k)) * del 0 m + (TT u p c k * CD1 (nx u (dec k)) k.val (c - kk p k)) * del 1 m := by
      intro k; simp only [EE]; ring
    simp only [hs, Finset.sum_add_distrib, ← Finset.sum_mul, coA0 u p c hv, coA1 u p c hv, coD0 u p c hv, coD1 u p c hv]
    have d0 : del 0 (m + 1) = 0 := by simp [del]
    have d1 : del 1 (m + 1) = del 0 m := by simp [del]
    simp only [EE, d0, d1]
    push_cast
    ring

lemma start_vals : CA0 0 81 1 = -12 ∧ CA1 0 81 1 = 64 ∧ CD0 0 81 1 = 12 ∧ CD1 0 81 1 = 18 := by
  decide +kernel

lemma a_form (n : ℕ) (hn : 1 ≤ n) :
    (81 : ℚ) * a n = (64 * n - 12) * 9 ^ n + 12 * del 0 n + 18 * del 1 n := by
  have h : (81 : ℤ) * G n 0 (decO 81) 1 = EE n 0 81 1 := G_closed n 0 81 1 (by decide)
  have hd : decO 81 = none := by simp [decO]
  rw [hd, ← a_eq n hn] at h
  obtain ⟨e0, e1, e2, e3⟩ := start_vals
  simp only [EE, e0, e1, e2, e3] at h
  have h' : ((81 * a n : ℤ) : ℚ) = (((-12 + 64 * (n : ℤ) ^ 1) * 9 ^ n + 12 * del 0 n + 18 * del 1 n : ℤ) : ℚ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) (by simpa using h)
  push_cast at h'
  rw [h']
  ring

lemma a_big (n : ℕ) (hn : 2 ≤ n) : (a n : ℚ) = (64 * n - 12) * 9 ^ n / 81 := by
  have := a_form n (by omega)
  simp only [del, show n ≠ 0 by omega, show n ≠ 1 by omega, if_false] at this
  push_cast at this
  linarith

lemma cnum (c : ℕ) [c.AtLeastTwo] (p : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n ((no_index (OfNat.ofNat c : PowerSeries ℚ)) * p) =
      (OfNat.ofNat c : ℚ) * PowerSeries.coeff n p := by
  rw [← map_ofNat (PowerSeries.C (R := ℚ)) c, PowerSeries.coeff_C_mul]

lemma cnum0 (c : ℕ) [c.AtLeastTwo] (n : ℕ) :
    PowerSeries.coeff n (no_index (OfNat.ofNat c : PowerSeries ℚ)) =
      if n = 0 then (OfNat.ofNat c : ℚ) else 0 := by
  rw [← map_ofNat (PowerSeries.C (R := ℚ)) c, PowerSeries.coeff_C]

open PowerSeries in
theorem mainP :
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - 9 * PowerSeries.X) ^ 2 = 2 * PowerSeries.X * (3 + 4 * PowerSeries.X + 9 * PowerSeries.X ^ 2) ∧
    ∀ n : ℕ, 1 < n → (a n : ℤ) = 4 * 9 ^ (n - 2) * (16 * (n : ℤ) - 3) := by
  have v0 : (a 0 : ℚ) = 0 := by simp [a]
  have v1 : (a 1 : ℚ) = 6 := by
    have := a_form 1 (by norm_num)
    simp only [del, show (1 : ℕ) ≠ 0 by norm_num, if_true, if_false] at this
    push_cast at this
    linarith
  have hb := a_big
  generalize a = f at v0 v1 hb ⊢
  refine ⟨?_, ?_⟩
  · have hL : ∀ S : PowerSeries ℚ, S * (1 - 9 * X) ^ 2 = S - 18 * (S * X ^ 1) + 81 * (S * X ^ 2) :=
      fun S => by ring
    have hR : (2 * X * (3 + 4 * X + 9 * X ^ 2) : PowerSeries ℚ) = X ^ 1 * (6 + 8 * X + 18 * X ^ 2) := by ring
    rw [hL, hR]
    ext n
    simp only [map_add, map_sub, coeff_mul_X_pow', cnum, coeff_mk]
    rcases lt_or_ge n 4 with hn | hn
    · have v2 := hb 2 (by norm_num)
      have v3 := hb 3 (by norm_num)
      norm_num at v2 v3
      interval_cases n <;> simp [coeff_X_pow, coeff_X_pow_mul', coeff_X, cnum, cnum0, map_ofNat, v0, v1, v2, v3] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have hR0 : coeff (m + 4) (X ^ 1 * (6 + 8 * X + 18 * X ^ 2) : PowerSeries ℚ) = 0 := by
        simp [coeff_X_pow, coeff_X_pow_mul', coeff_X, cnum, cnum0]
      rw [hR0]
      simp only [show 1 ≤ m + 4 by omega, show 2 ≤ m + 4 by omega, if_true]
      rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
        hb (m + 4) (by omega), hb (m + 3) (by omega), hb (m + 2) (by omega)]
      push_cast
      ring
  · intro n hn
    have h := hb n (by omega)
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [show k + 2 - 2 = k by omega]
    refine Int.cast_injective (α := ℚ) ?_
    push_cast
    rw [h]
    push_cast
    ring

end OMA.P_a229582

theorem OMA.solution : type_of% @OMA.S_oeis_a229582.main := OMA.P_a229582.mainP

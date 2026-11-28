import OMAStatements.S_oeis_a207450
import Mathlib

namespace OMA.S_oeis_a207450

section generic
variable {S : Type} [Fintype S] [DecidableEq S] (R : S → S → Prop) [DecidableRel R]

def Chain (n : ℕ) := {y : Fin (n + 1) → S // ∀ i : Fin n, R (y i.castSucc) (y i.succ)}

instance (n : ℕ) : Fintype (Chain R n) := by unfold Chain; infer_instance

def V : ℕ → S → ℕ
  | 0, _ => 1
  | n + 1, s => ∑ t, if R s t then V n t else 0

theorem cardStart (n : ℕ) (s : S) :
    Fintype.card {y : Chain R n // y.1 0 = s} = V R n s := by
  induction n generalizing s with
  | zero =>
    simp only [V]
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨⟨fun _ => s, fun i => i.elim0⟩, rfl⟩, ?_⟩
    rintro ⟨⟨y, hy⟩, h0⟩
    apply Subtype.ext; apply Subtype.ext
    funext j
    have : j = 0 := Fin.ext (by have := j.2; omega)
    subst this; exact h0
  | succ n ih =>
    have e : {y : Chain R (n + 1) // y.1 0 = s} ≃
        Σ t : S, {z : Chain R n // z.1 0 = t ∧ R s t} :=
      { toFun := fun y => ⟨y.1.1 1, ⟨⟨fun j => y.1.1 j.succ, fun i => y.1.2 i.succ⟩, rfl, by
          have h := y.1.2 0
          have h0 : y.1.1 (Fin.castSucc 0) = s := y.2
          rw [h0] at h
          exact h⟩⟩
        invFun := fun p => ⟨⟨Fin.cons s p.2.1.1, by
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · have h2 := p.2.2.2
            rw [← p.2.2.1] at h2
            simpa using h2
          · simpa using p.2.1.2 j⟩, rfl⟩
        left_inv := by
          rintro ⟨⟨y, hy⟩, h0⟩
          apply Subtype.ext; apply Subtype.ext
          funext j
          refine Fin.cases ?_ (fun k => ?_) j
          · simpa using h0.symm
          · simp
        right_inv := by
          rintro ⟨t, ⟨⟨z, hz⟩, h1, h2⟩⟩
          simp only [Fin.cons_succ]
          have : (Fin.cons s z : Fin (n + 2) → S) 1 = t := by
            have : (1 : Fin (n + 2)) = Fin.succ 0 := rfl
            rw [this, Fin.cons_succ]; exact h1
          subst this
          rfl }
    rw [Fintype.card_congr e, Fintype.card_sigma]
    simp only [V]
    apply Finset.sum_congr rfl
    intro t _
    by_cases h : R s t
    · simp only [h, if_true, and_true]
      exact ih t
    · simp only [h, if_false, and_false]
      simp [Fintype.card_eq_zero_iff]

theorem cardChain (n : ℕ) : Fintype.card (Chain R n) = ∑ s, V R n s := by
  rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv (fun y : Chain R n => y.1 0)), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro s _
  exact cardStart R n s

theorem rec_gen (m : ℕ) (c : ℕ → ℤ)
    (h0 : ∀ s, ∑ j ∈ Finset.range (m + 1), c j * (V R j s : ℤ) = 0) :
    ∀ n s, ∑ j ∈ Finset.range (m + 1), c j * (V R (n + j) s : ℤ) = 0 := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    intro s
    have : ∀ j, (V R (n + 1 + j) s : ℤ) = ∑ t, if R s t then (V R (n + j) t : ℤ) else 0 := by
      intro j
      rw [show n + 1 + j = (n + j) + 1 by omega]
      simp [V]
    simp only [this, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro t _
    by_cases h : R s t
    · have := ih t
      simp only [h, if_true]
      simpa [← Finset.mul_sum] using this
    · simp [h]

theorem rec_total (m : ℕ) (c : ℕ → ℤ)
    (h0 : ∀ s, ∑ j ∈ Finset.range (m + 1), c j * (V R j s : ℤ) = 0) (n : ℕ) :
    ∑ j ∈ Finset.range (m + 1), c j * (∑ s, (V R (n + j) s : ℤ)) = 0 := by
  have h := Finset.sum_eq_zero (s := (Finset.univ : Finset S)) (fun s _ => rec_gen R m c h0 n s)
  rw [Finset.sum_comm] at h
  simpa [Finset.mul_sum] using h
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


abbrev Row := Fin 5 → Fin 2
def rowOK (s : Row) : Prop := ∀ j < 5 - 2,
  (get (fun _ : Fin 1 => s) 0 j, get (fun _ : Fin 1 => s) 0 (j + 1), get (fun _ : Fin 1 => s) 0 (j + 2)) ≠ (0, 0, 0) ∧
  (get (fun _ : Fin 1 => s) 0 j, get (fun _ : Fin 1 => s) 0 (j + 1), get (fun _ : Fin 1 => s) 0 (j + 2)) ≠ (0, 0, 1)
instance : DecidablePred rowOK := fun s => by unfold rowOK; infer_instance
abbrev St := {s : Row // rowOK s}
def Vt (s t : St) : Prop := ∀ j : Fin 5, ¬ (s.1 j = 0 ∧ t.1 j = 1)
instance : DecidableRel Vt := fun s t => by unfold Vt; infer_instance

theorem get_eq {r : ℕ} (x : Fin r → Fin 5 → Fin 2) (i j : ℕ) (hi : i < r) (hj : j < 5) :
    get x i j = (x ⟨i, hi⟩ ⟨j, hj⟩ : ℕ) := by simp [get, hi, hj]

theorem avoids_iff {r : ℕ} (x : Fin r → Fin 5 → Fin 2) :
    avoids x = true ↔ (∀ i : Fin r, rowOK (x i)) ∧
      ∀ i i' : Fin r, i.val + 1 = i'.val → 1 ≤ i.val → ∀ j : Fin 5, ¬ (x i j = 0 ∧ x i' j = 1) := by
  unfold avoids rowOK
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨hh, hv⟩
    refine ⟨fun i j hj => ?_, fun i i' hi hi1 j => ?_⟩
    · have h := hh i.val i.2 j hj
      have e : ∀ k, k < 5 → get (fun _ : Fin 1 => x i) 0 k = get x i.val k := by
        intro k hk
        rw [get_eq _ 0 k (by omega) hk, get_eq x i.val k i.2 hk]
      rw [e j (by omega), e (j+1) (by omega), e (j+2) (by omega)]
      exact h
    · have h := hv (i.val - 1) (by omega) j j.2
      have h1 := get_eq x (i.val - 1) j (by omega) j.2
      have h2 := get_eq x (i.val - 1 + 1) j (by omega) j.2
      have h3 := get_eq x (i.val - 1 + 2) j (by omega) j.2
      have e2 : (⟨i.val - 1 + 1, by omega⟩ : Fin r) = i := Fin.ext (by simp; omega)
      have e3 : (⟨i.val - 1 + 2, by omega⟩ : Fin r) = i' := Fin.ext (by simp; omega)
      simp only [Fin.eta] at h1 h2 h3
      rw [e2] at h2
      rw [e3] at h3
      rw [h1, h2, h3] at h
      have hl : ((x ⟨i.val - 1, by omega⟩ j : Fin 2) : ℕ) < 2 := (x ⟨i.val - 1, by omega⟩ j).2
      simp only [ne_eq, Prod.mk.injEq] at h
      rintro ⟨a, b⟩
      have a' : ((x i j : Fin 2) : ℕ) = 0 := by simp [a]
      have b' : ((x i' j : Fin 2) : ℕ) = 1 := by simp [b]
      omega
  · rintro ⟨hh, hv⟩
    refine ⟨fun i hi j hj => ?_, fun i hi j hj => ?_⟩
    · have h := hh ⟨i, hi⟩ j hj
      have e : ∀ k, k < 5 → get (fun _ : Fin 1 => x ⟨i, hi⟩) 0 k = get x i k := by
        intro k hk
        rw [get_eq _ 0 k (by omega) hk, get_eq x i k hi hk]
      rw [e j (by omega), e (j+1) (by omega), e (j+2) (by omega)] at h
      exact h
    · have h := hv ⟨i + 1, by omega⟩ ⟨i + 2, by omega⟩ rfl (by simp) ⟨j, hj⟩
      rw [get_eq x i j (by omega) hj, get_eq x (i+1) j (by omega) hj, get_eq x (i+2) j (by omega) hj]
      simp only [ne_eq, Prod.mk.injEq]
      have hv' : ¬ ((x ⟨i + 1, by omega⟩ ⟨j, hj⟩ : ℕ) = 0 ∧ (x ⟨i + 2, by omega⟩ ⟨j, hj⟩ : ℕ) = 1) :=
        fun ⟨a, b⟩ => h ⟨Fin.ext (by simpa using a), Fin.ext (by simpa using b)⟩
      have hl : ((x ⟨i, by omega⟩ ⟨j, hj⟩ : Fin 2) : ℕ) < 2 := (x ⟨i, by omega⟩ ⟨j, hj⟩).2
      omega



def PP {n : ℕ} (x : Fin n → Row) : Prop :=
  (∀ i : Fin n, rowOK (x i)) ∧
      ∀ i i' : Fin n, i.val + 1 = i'.val → 1 ≤ i.val → ∀ j : Fin 5, ¬ (x i j = 0 ∧ x i' j = 1)

instance {n : ℕ} : DecidablePred (@PP n) := fun x => by unfold PP; infer_instance

theorem a_card (n : ℕ) : a n = (Fintype.card {x : Fin n → Row // PP x} : ℤ) := by
  unfold a
  rw [Fintype.card_subtype]
  congr 2
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact avoids_iff x

def toF (m : ℕ) : {x : Fin (m + 2) → Row // PP x} → St × Chain Vt m := fun x =>
  (⟨x.1 0, x.2.1 0⟩,
   ⟨fun i => ⟨x.1 i.succ, x.2.1 i.succ⟩, fun i => by
      intro j
      exact x.2.2 i.castSucc.succ i.succ.succ (by simp) (by simp) j⟩)

def ofF (m : ℕ) : St × Chain Vt m → {x : Fin (m + 2) → Row // PP x} := fun p =>
  ⟨(Fin.cons p.1.1 (fun i => (p.2.1 i).1) : Fin (m + 2) → Row), by
    constructor
    · intro i
      refine Fin.cases ?_ (fun k => ?_) i
      · simpa using p.1.2
      · simpa using (p.2.1 k).2
    · intro i i' h1 h2 j
      obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.mpr (show i ≠ 0 from fun h => by simp [h] at h2)
      obtain ⟨k', rfl⟩ := Fin.exists_succ_eq.mpr (show i' ≠ 0 from fun h => by simp [h] at h1)
      simp only [Fin.val_succ] at h1
      have hl : k.val < m := by have := k'.2; omega
      obtain ⟨l, rfl, rfl⟩ : ∃ l : Fin m, k = l.castSucc ∧ k' = l.succ :=
        ⟨⟨k.val, hl⟩, Fin.ext rfl, Fin.ext (by simp; omega)⟩
      have := p.2.2 l j
      simp only [Fin.cons_succ]
      exact this⟩

def eqF (m : ℕ) : {x : Fin (m + 2) → Row // PP x} ≃ St × Chain Vt m where
  toFun := toF m
  invFun := ofF m
  left_inv := by
    intro x
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [ofF, toF]
    · simp [ofF, toF]
  right_inv := by
    intro p
    simp only [toF, ofF]
    refine Prod.ext ?_ ?_
    · apply Subtype.ext; simp
    · apply Subtype.ext; funext i; apply Subtype.ext; simp

theorem a_eq2 (m : ℕ) : a (m + 2) = (Fintype.card St : ℤ) * ∑ s, (V Vt m s : ℤ) := by
  rw [a_card, Fintype.card_congr (eqF m), Fintype.card_prod, cardChain]
  push_cast
  rfl



def cc : ℕ → ℤ := fun j => [(1 : ℤ), (-4 : ℤ), (6 : ℤ), (-4 : ℤ), (1 : ℤ)].getD j 0

theorem hN : Fintype.card St = 16 := by decide +kernel

theorem hrecB (k : ℕ) : (∑ s, (V Vt (k + 4) s : ℤ)) = (-1 : ℤ) * ∑ s, (V Vt (k + 0) s : ℤ) + (4 : ℤ) * ∑ s, (V Vt (k + 1) s : ℤ) + (-6 : ℤ) * ∑ s, (V Vt (k + 2) s : ℤ) + (4 : ℤ) * ∑ s, (V Vt (k + 3) s : ℤ) := by
  have h := rec_total Vt 4 cc (by decide +kernel) k
  have e0 : cc 0 = 1 := rfl
  have e1 : cc 1 = -4 := rfl
  have e2 : cc 2 = 6 := rfl
  have e3 : cc 3 = -4 := rfl
  have e4 : cc 4 = 1 := rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, e3, e4] at h
  simp only [Nat.add_zero, zero_add] at h ⊢
  linarith

theorem hrecA (k : ℕ) : a (k + 4 + 2) = (-1 : ℤ) * a (k + 0 + 2) + (4 : ℤ) * a (k + 1 + 2) + (-6 : ℤ) * a (k + 2 + 2) + (4 : ℤ) * a (k + 3 + 2) := by
  have h := hrecB k
  simp only [a_eq2, hN]
  push_cast
  rw [← sub_eq_zero] at h ⊢
  linear_combination (16 : ℤ) * h

theorem v0 : a 0 = 1 := by decide +kernel
theorem v1 : a 1 = 16 := by decide +kernel
theorem v2 : a 2 = 256 := by rw [show 2 = 0 + 2 from rfl, a_eq2, hN]; decide +kernel
theorem v3 : a 3 = 1008 := by rw [show 3 = 1 + 2 from rfl, a_eq2, hN]; decide +kernel
theorem v4 : a 4 = 2560 := by rw [show 4 = 2 + 2 from rfl, a_eq2, hN]; decide +kernel
theorem v5 : a 5 = 5200 := by rw [show 5 = 3 + 2 from rfl, a_eq2, hN]; decide +kernel

theorem hrQ (n : ℕ) (hn : 6 ≤ n) : (a n : ℚ) = (-1 : ℚ) * a (n - 4) + (4 : ℚ) * a (n - 3) + (-6 : ℚ) * a (n - 2) + (4 : ℚ) * a (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 + 2 := ⟨n - 6, by omega⟩
  have f0 : k + 4 + 2 - 4 = k + 0 + 2 := by omega
  have f1 : k + 4 + 2 - 3 = k + 1 + 2 := by omega
  have f2 : k + 4 + 2 - 2 = k + 2 + 2 := by omega
  have f3 : k + 4 + 2 - 1 = k + 3 + 2 := by omega
  rw [f0, f1, f2, f3]
  exact_mod_cast hrecA k

theorem hrec' (n : ℕ) (hn : 5 ≤ n) : (a n : ℚ) = (-1 : ℚ) * a (n - 4) + (4 : ℚ) * a (n - 3) + (-6 : ℚ) * a (n - 2) + (4 : ℚ) * a (n - 1) := by
  by_cases h : 6 ≤ n
  · exact hrQ n h
  · have h2 : n ≤ 5 := by omega
    interval_cases n <;> simp [v0, v1, v2, v3, v4, v5] <;> norm_num

theorem gfthm : PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - PowerSeries.X) ^ 4 : PowerSeries ℚ) = 16 * PowerSeries.X * (1 + 12 * PowerSeries.X + 5 * PowerSeries.X ^ 2) := by
  have h := gf_gen (fun n => if n < 1 then 0 else (a n : ℚ)) 4 3 (fun j => [(1 : ℚ), (-4 : ℚ), (6 : ℚ), (-4 : ℚ), (1 : ℚ)].getD j 0) (fun j => [(0 : ℚ), (16 : ℚ), (192 : ℚ), (80 : ℚ)].getD j 0) ((1 - PowerSeries.X) ^ 4) (16 * PowerSeries.X * (1 + 12 * PowerSeries.X + 5 * PowerSeries.X ^ 2) : PowerSeries ℚ)
    (by simp [Finset.sum_range_succ, map_ofNat PowerSeries.C]; ring) (by simp [Finset.sum_range_succ, map_ofNat PowerSeries.C]; ring) (by norm_num) ?_ ?_
  · rw [h, mul_assoc, PowerSeries.inv_mul_cancel _ (by simp), mul_one]
  · intro n hn
    simp only [List.getD_eq_getElem?_getD]
    rcases n with _ | _ | _ | _ | k <;> simp_all
  · intro n
    by_cases hn : n ≤ 5
    · interval_cases n <;> simp [Finset.sum_range_succ, v0, v1, v2, v3, v4, v5] <;> norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 + 2 := ⟨n - 6, by omega⟩
      have r := hrecA k
      have g0 : k + 4 + 2 - 0 = k + 4 + 2 := by omega
      have g1 : k + 4 + 2 - 1 = k + 3 + 2 := by omega
      have g2 : k + 4 + 2 - 2 = k + 2 + 2 := by omega
      have g3 : k + 4 + 2 - 3 = k + 1 + 2 := by omega
      have g4 : k + 4 + 2 - 4 = k + 0 + 2 := by omega
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, g0, g1, g2, g3, g4]
      simp only [if_neg hn, if_pos (show 0 ≤ k + 4 + 2 by omega), if_neg (show ¬ (k + 4 + 2 < 1) by omega), if_pos (show 1 ≤ k + 4 + 2 by omega), if_neg (show ¬ (k + 3 + 2 < 1) by omega), if_pos (show 2 ≤ k + 4 + 2 by omega), if_neg (show ¬ (k + 2 + 2 < 1) by omega), if_pos (show 3 ≤ k + 4 + 2 by omega), if_neg (show ¬ (k + 1 + 2 < 1) by omega), if_pos (show 4 ≤ k + 4 + 2 by omega), if_neg (show ¬ (k + 0 + 2 < 1) by omega)]
      have r' : (a (k + 4 + 2) : ℚ) = (-1 : ℚ) * a (k + 0 + 2) + (4 : ℚ) * a (k + 1 + 2) + (-6 : ℚ) * a (k + 2 + 2) + (4 : ℚ) * a (k + 3 + 2) := by exact_mod_cast r
      norm_num [List.getD]
      linarith

end OMA.S_oeis_a207450

theorem OMA.solution : type_of% @OMA.S_oeis_a207450.main :=
  ⟨OMA.S_oeis_a207450.gfthm, fun n hn => by have := OMA.S_oeis_a207450.hrec' n hn; linarith⟩

import OMAStatements.S_oeis_a190035

namespace A190035Proof

open OMA.S_oeis_a190035

abbrev Digit := Fin 4

def valid2 (x y z : Digit) : Prop :=
  y ≤ z ∧ (z = x ∨ z = y ∨ (z : ℕ) = (x : ℕ) + (y : ℕ))

instance (x y z : Digit) : Decidable (valid2 x y z) := by unfold valid2; infer_instance

def valid3 (x y z t : Digit) : Prop :=
  z ≤ t ∧ (t = x ∨ t = y ∨ t = z ∨
    (t : ℕ) = (x : ℕ) + (y : ℕ) ∨ (t : ℕ) = (x : ℕ) + (z : ℕ) ∨
    (t : ℕ) = (y : ℕ) + (z : ℕ))

instance (x y z t : Digit) : Decidable (valid3 x y z t) := by unfold valid3; infer_instance

def F : ℕ → Digit → Digit → Digit → ℤ
  | 0, _, _, z => if z = 3 then 1 else 0
  | n+1, x, y, z => ∑ t : Digit, if valid3 x y z t then F n y z t else 0

def total (k : ℕ) : ℤ :=
  ∑ x : Digit, ∑ y : Digit, ∑ z : Digit,
    if x ≤ y ∧ valid2 x y z then F k x y z else 0

private def value {m : ℕ} (s : Fin m → Digit) (i : ℕ) : Digit :=
  if h : i < m then s ⟨i,h⟩ else 0

private theorem value_fin {m : ℕ} (s : Fin m → Digit) (i : Fin m) : value s i.val = s i := by
  simp [value,i.isLt]

private theorem value_cons_zero {m : ℕ} (x : Digit) (s : Fin m → Digit) :
    value (Fin.cons x s) 0 = x := by simp [value]

private theorem value_cons_succ {m : ℕ} (x : Digit) (s : Fin m → Digit) (i : ℕ) :
    value (Fin.cons x s) (i+1) = value s i := by
  by_cases h : i < m
  · simp only [value,h, Nat.succ_lt_succ h,dite_true]
    exact Fin.cons_succ (α := fun _ => Digit) x s ⟨i,h⟩
  · simp [value,h,show ¬ i+1 < m+1 by omega]

private def Allowed (f : ℕ → Digit) (i : ℕ) : Prop :=
  (∃ j, j < i ∧ i ≤ j+3 ∧ f i = f j) ∨
  ∃ j k, j < k ∧ k < i ∧ i ≤ j+3 ∧ (f i : ℕ) = (f j : ℕ) + (f k : ℕ)

private theorem valid_two (f : ℕ → Digit) :
    valid2 (f 0) (f 1) (f 2) ↔ f 1 ≤ f 2 ∧ Allowed f 2 := by
  unfold valid2 Allowed
  apply and_congr_right; intro _
  constructor
  · rintro (h|h|h)
    · exact Or.inl ⟨0,by decide,by decide,h⟩
    · exact Or.inl ⟨1,by decide,by decide,h⟩
    · exact Or.inr ⟨0,1,by decide,by decide,by decide,h⟩
  · rintro (⟨j,hj,_,h⟩|⟨j,k,hj,hk,_,h⟩)
    · interval_cases j <;> tauto
    · have h0 : j = 0 := by omega
      have h1 : k = 1 := by omega
      exact Or.inr (Or.inr (by simpa [h0,h1] using h))

private theorem valid_three (f : ℕ → Digit) (i : ℕ) :
    valid3 (f i) (f (i+1)) (f (i+2)) (f (i+3)) ↔ f (i+2) ≤ f (i+3) ∧ Allowed f (i+3) := by
  unfold valid3 Allowed
  apply and_congr_right; intro _
  constructor
  · rintro (h|h|h|h|h|h)
    · exact Or.inl ⟨i,by omega,by omega,h⟩
    · exact Or.inl ⟨i+1,by omega,by omega,h⟩
    · exact Or.inl ⟨i+2,by omega,by omega,h⟩
    · exact Or.inr ⟨i,i+1,by omega,by omega,by omega,h⟩
    · exact Or.inr ⟨i,i+2,by omega,by omega,by omega,h⟩
    · exact Or.inr ⟨i+1,i+2,by omega,by omega,by omega,h⟩
  · rintro (⟨j,hl,hh,h⟩|⟨j,k,hj,hk,hh,h⟩)
    · have hcase : j = i ∨ j = i+1 ∨ j = i+2 := by omega
      rcases hcase with rfl|rfl|rfl <;> tauto
    · have hcase : (j=i ∧ k=i+1) ∨ (j=i ∧ k=i+2) ∨ (j=i+1 ∧ k=i+2) := by omega
      rcases hcase with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> tauto

private theorem allowed_fin {m : ℕ} (s : Fin m → Digit) (i : Fin m) :
    Allowed (value s) i.val ↔
    (∃ j : Fin m, j < i ∧ i.val ≤ j.val+3 ∧ s i = s j) ∨
    ∃ j k : Fin m, j < k ∧ k < i ∧ i.val ≤ j.val+3 ∧ (s i:ℕ) = (s j:ℕ)+(s k:ℕ) := by
  constructor
  · rintro (⟨j,hl,hh,h⟩|⟨j,k,hj,hk,hh,h⟩)
    · have hj : j < m := by omega
      exact Or.inl ⟨⟨j,hj⟩,hl,hh,by simpa [value,i.isLt,hj] using h⟩
    · have hj' : j < m := by omega
      have hk' : k < m := by omega
      exact Or.inr ⟨⟨j,hj'⟩,⟨k,hk'⟩,hj,hk,hh,by simpa [value,i.isLt,hj',hk'] using h⟩
  · rintro (⟨j,hj,hh,h⟩|⟨j,k,hj,hk,hh,h⟩)
    · exact Or.inl ⟨j.val,hj,hh,by simpa only [value_fin] using h⟩
    · exact Or.inr ⟨j.val,k.val,hj,hk,hh,by simpa only [value_fin] using h⟩

private def Walk (k : ℕ) (f : ℕ → Digit) : Prop :=
  f (k+2) = 3 ∧ ∀ i < k, valid3 (f i) (f (i+1)) (f (i+2)) (f (i+3))

private theorem arrangement_iff (k : ℕ) (s : Fin (k+3) → Digit) :
    IsArrangement (k+1) s ↔
    (value s 0 ≤ value s 1 ∧ valid2 (value s 0) (value s 1) (value s 2)) ∧ Walk k (value s) := by
  let f := value s
  have last : f (k+2) = s (Fin.last (k+2)) := value_fin s (Fin.last (k+2))
  change _ ↔ (f 0 ≤ f 1 ∧ valid2 (f 0) (f 1) (f 2)) ∧ Walk k f
  rw [valid_two]
  constructor
  · rintro ⟨hm,he,ha⟩
    have hallowed (i : ℕ) (hi : i < k+3) (hmin : 2 ≤ i) : Allowed f i :=
      (allowed_fin s ⟨i,hi⟩).mpr (ha ⟨i,hi⟩ hmin)
    have hle (i : ℕ) (hi : i+1 < k+3) : f i ≤ f (i+1) := by
      have h0 : i < k+3 := by omega
      exact (by simpa only [f,value,h0,hi,dite_true] using
        (hm ⟨i,h0⟩ ⟨i+1,hi⟩ (by change i ≤ i+1; omega)))
    refine ⟨⟨hle 0 (by omega),hle 1 (by omega),hallowed 2 (by omega) le_rfl⟩,last.trans he,?_⟩
    intro i hi
    exact (valid_three f i).mpr ⟨hle (i+2) (by omega),hallowed (i+3) (by omega) (by omega)⟩
  · rintro ⟨⟨h0,h1,h2⟩,he,hs⟩
    have hmono : Monotone s := by
      apply Fin.monotone_iff_le_succ.mpr
      intro i
      have hle : f i.val ≤ f (i.val+1) := by
        rcases Nat.lt_or_ge i.val 2 with h | h
        · have hi : i.val = 0 ∨ i.val = 1 := by omega
          rcases hi with hi|hi <;> simp only [hi] <;> assumption
        · obtain ⟨j,hj⟩ : ∃ j, i.val=j+2 := ⟨i.val-2,by omega⟩
          rw [hj]
          exact ((valid_three f j).mp (hs j (by omega))).1
      have hcast : f i.val = s i.castSucc := value_fin s i.castSucc
      have hsucc : f (i.val+1) = s i.succ := value_fin s i.succ
      rw [hcast,hsucc] at hle
      exact hle
    refine ⟨fun i j hij => hmono hij, last ▸ he, ?_⟩
    intro i hi
    apply (allowed_fin s i).mp
    by_cases heq : i.val = 2
    · rw [heq]; exact h2
    · obtain ⟨j,hj⟩ : ∃ j, i.val = j+3 := ⟨i.val-3,by omega⟩
      rw [hj]
      exact ((valid_three f j).mp (hs j (by omega))).2

private theorem walk_succ (k : ℕ) (f : ℕ → Digit) : Walk (k+1) f ↔
    valid3 (f 0) (f 1) (f 2) (f 3) ∧ Walk k (fun j => f (j+1)) := by
  constructor
  · rintro ⟨hl,h⟩
    exact ⟨h 0 (by omega),hl,fun j hj => h (j+1) (by omega)⟩
  · rintro ⟨h0,hl,h⟩
    refine ⟨hl,?_⟩
    rintro (_|j) hj
    · exact h0
    · exact h j (by omega)

private abbrev front {k : ℕ} (x y z : Digit) (s : Fin k → Digit) : Fin (k+3) → Digit :=
  Fin.cons x (Fin.cons y (Fin.cons z s))

private theorem walk_front {k : ℕ} (x y z t : Digit) (s : Fin k → Digit) :
    Walk (k+1) (value (front x y z (Fin.cons t s))) ↔
    valid3 x y z t ∧ Walk k (value (front y z t s)) := by
  rw [walk_succ]
  simp only [front, value_cons_succ, value_cons_zero]

private theorem sum_digits {k : ℕ} (f : (Fin (k+1) → Digit) → ℤ) :
    (∑ s, f s) = ∑ t : Digit, ∑ s : Fin k → Digit, f (Fin.cons t s) := by
  rw [← (Fin.consEquiv (fun _ : Fin (k+1) => Digit)).sum_comp f, Fintype.sum_prod_type]
  rfl

private noncomputable def tails (k : ℕ) (x y z : Digit) : ℤ := by
  classical
  exact ∑ s : Fin k → Digit, if Walk k (value (front x y z s)) then 1 else 0

private theorem tails_eq (k : ℕ) (x y z : Digit) : tails k x y z = F k x y z := by
  classical
  induction k generalizing x y z with
  | zero => simp [tails,Walk,front,value_cons_succ,value_cons_zero,F]
  | succ k ih =>
    unfold tails
    rw [sum_digits]
    simp only [walk_front, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
    change (∑ t : Digit, if valid3 x y z t then tails k y z t else 0) = _
    simp only [ih,F]

theorem count_arrays (k : ℕ) : (a (k+1) : ℤ) = total k := by
  classical
  rw [a, ← Finset.sum_boole, sum_digits]
  apply Finset.sum_congr rfl
  intro x _
  rw [sum_digits]
  apply Finset.sum_congr rfl
  intro y _
  rw [sum_digits]
  apply Finset.sum_congr rfl
  intro z _
  change (∑ s : Fin k → Digit, if IsArrangement (k+1) (front x y z s) then (1:ℤ) else 0) = _
  simp only [arrangement_iff, front,value_cons_succ,value_cons_zero,ite_and,
    Finset.sum_ite_irrel,Finset.sum_const_zero]
  change (if x ≤ y then if valid2 x y z then tails k x y z else 0 else 0) = _
  rw [tails_eq]

open PowerSeries

-- After three steps the second difference vanishes on every nondecreasing state.
private theorem state_initial : ∀ x y z : Digit, x ≤ y → y ≤ z →
    F 5 x y z = 2 * F 4 x y z - F 3 x y z := by
  decide +kernel

private theorem state_rec (k : ℕ) (x y z : Digit) (hxy : x ≤ y) (hyz : y ≤ z) :
    F (k+5) x y z = 2 * F (k+4) x y z - F (k+3) x y z := by
  induction k generalizing x y z with
  | zero => exact state_initial x y z hxy hyz
  | succ k ih =>
    change (∑ t : Digit, if valid3 x y z t then F (k+5) y z t else 0) =
      2 * (∑ t : Digit, if valid3 x y z t then F (k+4) y z t else 0) -
        (∑ t : Digit, if valid3 x y z t then F (k+3) y z t else 0)
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _
    by_cases h : valid3 x y z t
    · simpa only [if_pos h] using ih y z t hyz h.1
    · simp [h]

private theorem total_rec (k : ℕ) :
    total (k+5) = 2 * total (k+4) - total (k+3) := by
  simp only [total, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  by_cases h : x ≤ y ∧ valid2 x y z
  · simpa only [if_pos h] using state_rec k x y z h.1 h.2.1
  · simp [h]

private theorem initial :
    total 0 = 5 ∧ total 1 = 7 ∧ total 2 = 10 ∧ total 3 = 14 ∧ total 4 = 18 := by
  decide +kernel

private theorem total_formula (k : ℕ) : total (k+2) = 4 * (k : ℤ) + 10 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k < 3
    · interval_cases k <;> norm_num [initial.2.2.1, initial.2.2.2.1, initial.2.2.2.2]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k-3, by omega⟩
      rw [show j+3+2 = j+5 by omega, total_rec,
        show j+4 = (j+2)+2 by omega, ih (j+2) (by omega),
        show j+3 = (j+1)+2 by omega, ih (j+1) (by omega)]
      push_cast
      ring

private def term (n : ℕ) : ℤ :=
  if n = 0 then 0 else if n = 1 then 5 else if n = 2 then 7 else 4 * (n : ℤ) - 2

private theorem term_series : mk term * (1-X)^2 = X*(5-3*X+X^2+X^3) := by
  let A := mk term
  change A * _ = _
  rw [show A * (1-X)^2 = A - C 2 * (A * X^1) + A * X^2 by simp only [map_ofNat]; ring,
      show (X*(5-3*X+X^2+X^3) : PowerSeries ℤ) = C 5*X^1 - C 3*X^2 + X^3 + X^4 by
        simp only [map_ofNat]; ring]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_C, A, coeff_mk]
  by_cases hn : n ≤ 4
  · interval_cases n <;> norm_num [term]
  · simp (disch := omega) only [term, if_pos, if_neg, Nat.cast_sub, Nat.cast_ofNat]
    ring

theorem solutionOfCount (ha : ∀ k : ℕ, (a (k+1) : ℤ) = total k) :
    type_of% @OMA.S_oeis_a190035.main := by
  have ht (n : ℕ) (hn : 0 < n) : (a n : ℤ) = term n := by
    by_cases hm : n ≤ 2
    · interval_cases n
      · simpa [term, initial.1] using ha 0
      · simpa [term, initial.2.1] using ha 1
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n-3, by omega⟩
      rw [show k+3 = (k+2)+1 by omega, ha, total_formula]
      simp (disch := omega) only [term, if_neg, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
      ring
  constructor
  · convert term_series using 2
    apply congrArg mk
    funext n
    by_cases hn : n = 0
    · simp [term, hn]
    · simp [hn, ht n (by omega)]
  · intro n hn
    rw [ht n (by omega), ht (n-1) (by omega), ht (n-2) (by omega)]
    simp (disch := omega) only [term, if_neg, Nat.cast_sub, Nat.cast_ofNat, Nat.cast_one]
    ring

end A190035Proof

open A190035Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a190035.main :=
  solutionOfCount count_arrays

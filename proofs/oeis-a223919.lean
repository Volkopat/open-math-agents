import OMAStatements.S_oeis_a223919
import Mathlib

namespace OMA.S_oeis_a223919

section kit
variable {S A : Type} [Fintype A]

def RunAcc (ok : S → A → Prop) (nx : S → A → S) : S → List A → Prop
  | _, [] => True
  | s, a :: l => ok s a ∧ RunAcc ok nx (nx s a) l

def V (ok : S → A → Prop) [∀ s a, Decidable (ok s a)] (nx : S → A → S) : ℕ → S → ℕ
  | 0, _ => 1
  | n + 1, s => ∑ a, if ok s a then V ok nx n (nx s a) else 0

instance finLen (A : Type) [Fintype A] (n : ℕ) (P : List A → Prop) :
    Finite {l : List A // l.length = n ∧ P l} := by
  have : Finite {l : List A // l.length = n} := inferInstanceAs (Finite (List.Vector A n))
  exact Finite.of_injective (fun x : {l : List A // l.length = n ∧ P l} =>
    (⟨x.1, x.2.1⟩ : {l : List A // l.length = n})) (fun x y h => by
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext h)

theorem cnt (ok : S → A → Prop) [∀ s a, Decidable (ok s a)] (nx : S → A → S) (n : ℕ) (s : S) :
    Nat.card {l : List A // l.length = n ∧ RunAcc ok nx s l} = V ok nx n s := by
  induction n generalizing s with
  | zero =>
    simp only [V]
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => ?_⟩, ⟨⟨[], rfl, trivial⟩⟩⟩
    apply Subtype.ext
    have h1 := List.length_eq_zero_iff.mp x.2.1
    have h2 := List.length_eq_zero_iff.mp y.2.1
    rw [h1, h2]
  | succ n ih =>
    have e : {l : List A // l.length = n + 1 ∧ RunAcc ok nx s l} ≃
        Σ a : A, {l : List A // l.length = n ∧ (ok s a ∧ RunAcc ok nx (nx s a) l)} :=
      { toFun := fun x => match x with
          | ⟨[], h, _⟩ => absurd h (by simp)
          | ⟨a :: l, h, hacc⟩ => ⟨a, ⟨l, by simpa using h, hacc⟩⟩
        invFun := fun p => ⟨p.1 :: p.2.1, by simp [p.2.2.1], p.2.2.2⟩
        left_inv := by
          rintro ⟨l, h, hacc⟩
          cases l with
          | nil => simp at h
          | cons a l => rfl
        right_inv := by
          rintro ⟨a, l, h⟩
          rfl }
    rw [Nat.card_congr e, Nat.card_sigma]
    simp only [V]
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : ok s a
    · simp only [h, if_true, true_and]
      exact ih _
    · simp only [h, if_false, false_and]
      simp

theorem rec_gen (ok : S → A → Prop) [∀ s a, Decidable (ok s a)] (nx : S → A → S)
    (T : S → Prop) (hT : ∀ s a, T s → ok s a → T (nx s a)) (n0 m : ℕ) (c : ℕ → ℤ)
    (h0 : ∀ s, T s → ∑ j ∈ Finset.range (m + 1), c j * (V ok nx (n0 + j) s : ℤ) = 0) :
    ∀ n s, T s → ∑ j ∈ Finset.range (m + 1), c j * (V ok nx (n0 + n + j) s : ℤ) = 0 := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    intro s hs
    have : ∀ j, (V ok nx (n0 + (n + 1) + j) s : ℤ) =
        ∑ a, if ok s a then (V ok nx (n0 + n + j) (nx s a) : ℤ) else 0 := by
      intro j
      rw [show n0 + (n + 1) + j = (n0 + n + j) + 1 by omega]
      simp [V]
    simp only [this, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro a _
    by_cases h : ok s a
    · have := ih (nx s a) (hT s a hs h)
      simp only [h, if_true]
      simpa [← Finset.mul_sum] using this
    · simp [h]

theorem rec_next (ok : S → A → Prop) [∀ s a, Decidable (ok s a)] (nx : S → A → S)
    (T : S → Prop) (hT : ∀ s a, T s → ok s a → T (nx s a)) (n0 m : ℕ) (c : ℕ → ℤ)
    (h0 : ∀ s, T s → ∑ j ∈ Finset.range (m + 1), c j * (V ok nx (n0 + j) s : ℤ) = 0)
    (s : S) (hs : ∀ a, ok s a → T (nx s a)) (n : ℕ) :
    ∑ j ∈ Finset.range (m + 1), c j * (V ok nx (n0 + n + 1 + j) s : ℤ) = 0 := by
  have : ∀ j, (V ok nx (n0 + n + 1 + j) s : ℤ) =
      ∑ a, if ok s a then (V ok nx (n0 + n + j) (nx s a) : ℤ) else 0 := by
    intro j
    rw [show n0 + n + 1 + j = (n0 + n + j) + 1 by omega]
    simp [V]
  simp only [this, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro a _
  by_cases h : ok s a
  · have := rec_gen ok nx T hT n0 m c h0 n (nx s a) (hs a h)
    simp only [h, if_true]
    simpa [← Finset.mul_sum] using this
  · simp [h]
end kit

section ofn

theorem card_ofFn {A : Type} (n : ℕ) (P : List A → Prop) :
    Nat.card {y : Fin n → A // P (List.ofFn y)} = Nat.card {l : List A // l.length = n ∧ P l} := by
  apply Nat.card_congr
  exact
    { toFun := fun y => ⟨List.ofFn y.1, by simp, y.2⟩
      invFun := fun l => ⟨fun i => l.1.get (i.cast l.2.1.symm), by
        have : List.ofFn (fun i : Fin n => l.1.get (i.cast l.2.1.symm)) = l.1 := by
          apply List.ext_getElem
          · simp [l.2.1]
          · intro i h1 h2; simp
        rw [this]; exact l.2.2⟩
      left_inv := by
        intro y; apply Subtype.ext; funext i; simp
      right_inv := by
        intro l; apply Subtype.ext
        apply List.ext_getElem
        · simp [l.2.1]
        · intro i h1 h2; simp }

end ofn

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



section rows
abbrev RS := Fin 3 × Bool
def rok (s : RS) (b : Fin 3) : Prop := s.2 = true → b ≤ s.1
instance (s : RS) (b : Fin 3) : Decidable (rok s b) := by unfold rok; infer_instance
def rnx (s : RS) (b : Fin 3) : RS := (b, s.2 || decide (b < s.1))

def NV {L : ℕ} (g : Fin L → Fin 3) : Prop := ∀ a b c : Fin L, a < b → b < c → ¬ (g b < g a ∧ g b < g c)
def ND {L : ℕ} (m : Fin 3) (g : Fin L → Fin 3) : Prop := (∀ a, g a ≤ m) ∧ ∀ a b, a < b → g b ≤ g a
def specR (s : RS) {L : ℕ} (g : Fin L → Fin 3) : Prop :=
  if s.2 = true then ND s.1 g else NV (Fin.cons s.1 g : Fin (L+1) → Fin 3)

theorem nd_step {L : ℕ} (m b : Fin 3) (g : Fin L → Fin 3) :
    ND m (Fin.cons b g : Fin (L+1) → Fin 3) ↔ b ≤ m ∧ ND b g := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by simpa using h1 0, fun a => by simpa using h2 0 a.succ (Fin.succ_pos a), fun a c hac => ?_⟩
    simpa using h2 a.succ c.succ (Fin.succ_lt_succ_iff.2 hac)
  · rintro ⟨hbm, h1, h3⟩
    refine ⟨fun a => ?_, fun a c hac => ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) a
      · simpa using hbm
      · simpa using (h1 i).trans hbm
    · cases a using Fin.cases with
      | zero =>
        cases c using Fin.cases with
        | zero => exact absurd hac (lt_irrefl _)
        | succ j => simpa using h1 j
      | succ i =>
        cases c using Fin.cases with
        | zero => exact absurd hac (by simp)
        | succ j => simpa using h3 i j (Fin.succ_lt_succ_iff.1 hac)

theorem nd_nv {L : ℕ} (m : Fin 3) (g : Fin L → Fin 3) (h : ND m g) : NV g := by
  intro a b c hab hbc hh
  exact absurd (h.2 b c hbc) (not_le.2 hh.2)

theorem nv_cons {L : ℕ} (m : Fin 3) (g : Fin L → Fin 3) :
    NV (Fin.cons m g : Fin (L+1) → Fin 3) ↔
      NV g ∧ ∀ j k : Fin L, j < k → ¬ (g j < m ∧ g j < g k) := by
  constructor
  · intro h
    refine ⟨fun a b c hab hbc => ?_, fun j k hjk => ?_⟩
    · simpa using h a.succ b.succ c.succ (Fin.succ_lt_succ_iff.2 hab) (Fin.succ_lt_succ_iff.2 hbc)
    · simpa using h 0 j.succ k.succ (Fin.succ_pos j) (Fin.succ_lt_succ_iff.2 hjk)
  · rintro ⟨h1, h2⟩ a b c hab hbc
    refine Fin.cases ?_ (fun a' => ?_) a hab hbc
    · intro hab hbc
      revert hab hbc
      refine Fin.cases (fun h => absurd h (lt_irrefl _)) (fun j => ?_) b
      refine Fin.cases (fun h1 h2 => absurd h2 (by simp)) (fun k hab hbc => ?_) c
      simpa using h2 j k (Fin.succ_lt_succ_iff.1 hbc)
    · intro hab hbc
      revert hab hbc
      refine Fin.cases (fun h => absurd h (by simp)) (fun j => ?_) b
      refine Fin.cases (fun h1 h2 => absurd h2 (by simp)) (fun k hab hbc => ?_) c
      simpa using h1 a' j k (Fin.succ_lt_succ_iff.1 hab) (Fin.succ_lt_succ_iff.1 hbc)

theorem nv_ge {L : ℕ} (m b : Fin 3) (g : Fin L → Fin 3) (hmb : m ≤ b) :
    NV (Fin.cons m (Fin.cons b g : Fin (L+1) → Fin 3) : Fin (L+2) → Fin 3) ↔
      NV (Fin.cons b g : Fin (L+1) → Fin 3) := by
  rw [nv_cons]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, fun j k hjk => ?_⟩
    refine Fin.cases ?_ (fun j' => ?_) j hjk
    · intro _ hh
      have := hh.1
      simp at this
      omega
    · refine Fin.cases (fun h => absurd h (by simp)) (fun k' hjk hh => ?_) k
      have h' := (nv_cons b g).1 h
      simp at hh
      have := h'.2 j' k' (Fin.succ_lt_succ_iff.1 hjk)
      exact this ⟨lt_of_lt_of_le hh.1 hmb, hh.2⟩

theorem nv_lt {L : ℕ} (m b : Fin 3) (g : Fin L → Fin 3) (hmb : b < m) :
    NV (Fin.cons m (Fin.cons b g : Fin (L+1) → Fin 3) : Fin (L+2) → Fin 3) ↔ ND b g := by
  constructor
  · intro h
    have h1 : ∀ a, g a ≤ b := by
      intro a
      by_contra hc
      exact h 0 1 a.succ.succ (by simp) (by simp [Fin.lt_def]) (by simpa using ⟨hmb, not_le.1 hc⟩)
    refine ⟨h1, fun a c hac => ?_⟩
    by_contra hc
    exact h 0 a.succ.succ c.succ.succ (Fin.succ_pos _) (Fin.succ_lt_succ_iff.2 (Fin.succ_lt_succ_iff.2 hac))
      (by simpa using ⟨lt_of_le_of_lt (h1 a) hmb, not_le.1 hc⟩)
  · intro h
    have hd : ND m (Fin.cons b g : Fin (L+1) → Fin 3) := (nd_step m b g).2 ⟨hmb.le, h⟩
    rw [nv_cons]
    refine ⟨nd_nv _ _ ((nd_step b b g).2 ⟨le_refl _, h⟩), fun j k hjk hh => ?_⟩
    exact absurd (hd.2 j k hjk) (not_le.2 hh.2)

theorem nv_zero {L : ℕ} (g : Fin L → Fin 3) :
    NV (Fin.cons 0 g : Fin (L+1) → Fin 3) ↔ NV g := by
  rw [nv_cons]
  refine ⟨fun h => h.1, fun h => ⟨h, fun j k _ hh => ?_⟩⟩
  have := hh.1
  omega


theorem specR_nil (s : RS) (g : Fin 0 → Fin 3) : specR s g := by
  unfold specR
  split_ifs
  · exact ⟨fun a => a.elim0, fun a => a.elim0⟩
  · intro a b c hab hbc
    have h1 := c.2
    rw [Fin.lt_def] at hab hbc
    omega

theorem specR_step (s : RS) {L : ℕ} (b : Fin 3) (g : Fin L → Fin 3) :
    specR s (Fin.cons b g : Fin (L+1) → Fin 3) ↔ rok s b ∧ specR (rnx s b) g := by
  obtain ⟨m, d⟩ := s
  cases d
  · simp only [specR, rok, rnx, Bool.false_or, Bool.false_eq_true, if_false, false_implies, true_and]
    rcases le_or_gt m b with h | h
    · rw [nv_ge m b g h]
      have : ¬ b < m := not_lt.2 h
      simp [this]
    · rw [nv_lt m b g h]
      simp [h]
  · simp only [specR, rok, rnx, Bool.true_or, if_true, true_implies]
    exact nd_step m b g

theorem runR : ∀ (L : ℕ) (s : RS) (g : Fin L → Fin 3), RunAcc rok rnx s (List.ofFn g) ↔ specR s g := by
  intro L
  induction L with
  | zero => intro s g; simp only [List.ofFn_zero, RunAcc]; exact ⟨fun _ => specR_nil s g, fun _ => trivial⟩
  | succ L ih =>
    intro s g
    rw [List.ofFn_succ, RunAcc, ih]
    have : g = (Fin.cons (g 0) (fun i => g i.succ) : Fin (L+1) → Fin 3) := (Fin.cons_self_tail g).symm
    conv_rhs => rw [this]
    rw [specR_step]

theorem runR0 {L : ℕ} (g : Fin L → Fin 3) : RunAcc rok rnx (0, false) (List.ofFn g) ↔ NV g := by
  rw [runR]
  show NV (Fin.cons 0 g : Fin (L+1) → Fin 3) ↔ _
  exact nv_zero g
end rows

abbrev AL := Fin 3 × Fin 3
abbrev SS := RS × RS
def okP (s : SS) (c : AL) : Prop := c.1 ≤ c.2 ∧ rok s.1 c.1 ∧ rok s.2 c.2
instance (s : SS) (c : AL) : Decidable (okP s c) := by unfold okP; infer_instance
def nxP (s : SS) (c : AL) : SS := (rnx s.1 c.1, rnx s.2 c.2)
def s0 : SS := ((0, false), (0, false))

theorem acc2 : ∀ (l : List AL) (s : SS), RunAcc okP nxP s l ↔
    ((∀ c ∈ l, c.1 ≤ c.2) ∧ RunAcc rok rnx s.1 (l.map (fun c => c.1)) ∧
      RunAcc rok rnx s.2 (l.map (fun c => c.2))) := by
  intro l
  induction l with
  | nil => intro s; simp [RunAcc]
  | cons c l ih =>
    intro s
    simp only [RunAcc, ih, okP, nxP, List.map_cons, List.mem_cons, forall_eq_or_imp]
    tauto

theorem good_cols {n : ℕ} (x : Fin 2 → Fin n → Fin 3) :
    Good x ↔ RunAcc okP nxP s0 (List.ofFn fun j => (x 0 j, x 1 j)) := by
  rw [acc2]
  simp only [List.map_ofFn]
  have e0 : ((fun c : AL => c.1) ∘ fun j => (x 0 j, x 1 j)) = x 0 := rfl
  have e1 : ((fun c : AL => c.2) ∘ fun j => (x 0 j, x 1 j)) = x 1 := rfl
  rw [e0, e1]
  show _ ↔ _ ∧ RunAcc rok rnx (0, false) _ ∧ RunAcc rok rnx (0, false) _
  rw [runR0, runR0]
  have hA : AntidiagUnimodal x := by
    intro i₁ i₂ i₃ j₁ j₂ j₃ h12 h23 e1 e2
    have := i₁.2
    rw [Fin.lt_def] at h12 h23
    omega
  have hM : ∀ j, Monotone (fun i => x i j) ↔ x 0 j ≤ x 1 j := by
    intro j
    constructor
    · intro h; exact h (by decide)
    · intro h i i' hii
      fin_cases i <;> fin_cases i' <;> simp_all
  unfold Good Unimodal
  simp only [hM, List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff, Fin.forall_fin_two]
  constructor
  · rintro ⟨⟨h0, h1⟩, _, h3⟩
    exact ⟨h3, h0, h1⟩
  · rintro ⟨h3, h0, h1⟩
    exact ⟨⟨h0, h1⟩, hA, h3⟩

def colEquiv {n : ℕ} : (Fin 2 → Fin n → Fin 3) ≃ (Fin n → AL) where
  toFun x j := (x 0 j, x 1 j)
  invFun y i j := if i = 0 then (y j).1 else (y j).2
  left_inv x := by
    funext i j
    fin_cases i <;> simp
  right_inv y := by
    funext j
    simp

theorem a_eq (n : ℕ) : a n = V okP nxP n s0 := by
  have h1 : a n = Nat.card {x : Fin 2 → Fin n → Fin 3 // Good x} := by
    unfold a; rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [h1, ← cnt okP nxP n s0, ← card_ofFn n (fun l => RunAcc okP nxP s0 l)]
  exact Nat.card_congr (Equiv.subtypeEquiv colEquiv (fun x => good_cols x))

def code (s : SS) : ℕ := (s.1.1 : ℕ) + 3 * (if s.1.2 then 1 else 0) + 6 * (s.2.1 : ℕ) + 18 * (if s.2.2 then 1 else 0)

def toF (k : ℕ) : Fin 3 := if k = 0 then 0 else if k = 1 then 1 else 2
def dec (c : ℕ) : SS := ((toF (c % 3), decide (c / 3 % 2 = 1)), (toF (c / 6 % 3), decide (c / 18 = 1)))
def decA (k : ℕ) : AL := (toF (k / 3), toF (k % 3))

theorem dec_code : ∀ s : SS, dec (code s) = s := by decide +kernel
theorem code_lt : ∀ s : SS, code s < 36 := by decide +kernel

def stepT (l : List ℕ) : List ℕ := (List.range 36).map (fun c =>
  ∑ k ∈ Finset.range 9, if okP (dec c) (decA k) then l.getD (code (nxP (dec c) (decA k))) 0 else 0)
def Vv : ℕ → List ℕ
  | 0 => List.replicate 36 1
  | n + 1 => stepT (Vv n)

theorem getD_stepT (l : List ℕ) (i : ℕ) (hi : i < 36) : (stepT l).getD i 0 =
    ∑ k ∈ Finset.range 9, if okP (dec i) (decA k) then l.getD (code (nxP (dec i) (decA k))) 0 else 0 := by
  unfold stepT
  simp [List.getD_eq_getElem?_getD, hi]

theorem sum_AL (F : AL → ℕ) : ∑ a : AL, F a = ∑ k ∈ Finset.range 9, F (decA k) := by
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_three, Finset.sum_range_succ, Finset.sum_range_zero]
  have e0 : decA 0 = (0, 0) := by decide
  have e1 : decA 1 = (0, 1) := by decide
  have e2 : decA 2 = (0, 2) := by decide
  have e3 : decA 3 = (1, 0) := by decide
  have e4 : decA 4 = (1, 1) := by decide
  have e5 : decA 5 = (1, 2) := by decide
  have e6 : decA 6 = (2, 0) := by decide
  have e7 : decA 7 = (2, 1) := by decide
  have e8 : decA 8 = (2, 2) := by decide
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8]
  ring

theorem rep1 : ∀ s : SS, (List.replicate 36 1).getD (code s) 0 = 1 := by decide +kernel

theorem V_tab : ∀ (n : ℕ) (s : SS), V okP nxP n s = (Vv n).getD (code s) 0 := by
  intro n
  induction n with
  | zero => intro s; simp only [V, Vv]; exact (rep1 s).symm
  | succ n ih =>
    intro s
    simp only [V, Vv]
    rw [getD_stepT _ _ (code_lt s), dec_code, sum_AL]
    apply Finset.sum_congr rfl
    intro k _
    by_cases h : okP s (decA k)
    · simp only [h, if_true]
      exact ih _
    · simp only [h, if_false]
def Tset (s : SS) : Prop := code s ∈ [0, 6, 7, 9, 12, 13, 14, 15, 16, 18, 21, 24, 25, 27, 28]
instance (s : SS) : Decidable (Tset s) := by unfold Tset; infer_instance
theorem hT : ∀ s a, Tset s → okP s a → Tset (nxP s a) := by decide +kernel
theorem hs0 : ∀ a, okP s0 a → Tset (nxP s0 a) := by decide +kernel
def cc : ℕ → ℤ := fun j => [-1, 9, -36, 84, -126, 126, -84, 36, -9, 1].getD j 0
theorem h0 : ∀ s, Tset s → ∑ j ∈ Finset.range (10), cc j * (V okP nxP (0 + j) s : ℤ) = 0 := by
  intro s hs
  have key : ∀ c ∈ [0, 6, 7, 9, 12, 13, 14, 15, 16, 18, 21, 24, 25, 27, 28], ∑ j ∈ Finset.range (10), cc j * (((Vv j).getD c 0 : ℕ) : ℤ) = 0 := by decide +kernel
  have e : ∀ j, V okP nxP (0 + j) s = (Vv j).getD (code s) 0 := fun j => by rw [zero_add]; exact V_tab j s
  simp only [e]
  exact key (code s) hs
theorem hrecV (n : ℕ) : ∑ j ∈ Finset.range (10), cc j * (a (0 + n + 1 + j) : ℤ) = 0 := by
  have := rec_next okP nxP Tset hT 0 9 cc h0 s0 hs0 n
  simp only [a_eq]
  exact this
theorem hrecA (k : ℕ) : (a (0 + k + 1 + 9) : ℚ) = (1 : ℚ) * a (0 + k + 1 + 0) + (-9 : ℚ) * a (0 + k + 1 + 1) + (36 : ℚ) * a (0 + k + 1 + 2) + (-84 : ℚ) * a (0 + k + 1 + 3) + (126 : ℚ) * a (0 + k + 1 + 4) + (-126 : ℚ) * a (0 + k + 1 + 5) + (84 : ℚ) * a (0 + k + 1 + 6) + (-36 : ℚ) * a (0 + k + 1 + 7) + (9 : ℚ) * a (0 + k + 1 + 8) := by
  have h := hrecV k
  have e0 : cc 0 = -1 := rfl
  have e1 : cc 1 = 9 := rfl
  have e2 : cc 2 = -36 := rfl
  have e3 : cc 3 = 84 := rfl
  have e4 : cc 4 = -126 := rfl
  have e5 : cc 5 = 126 := rfl
  have e6 : cc 6 = -84 := rfl
  have e7 : cc 7 = 36 := rfl
  have e8 : cc 8 = -9 := rfl
  have e9 : cc 9 = 1 := rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9] at h
  have h' := congrArg (Int.cast : ℤ → ℚ) h
  push_cast at h'
  linarith
theorem v0 : a 0 = 1 := by rw [a_eq, V_tab]; decide +kernel
theorem v1 : a 1 = 6 := by rw [a_eq, V_tab]; decide +kernel
theorem v2 : a 2 = 36 := by rw [a_eq, V_tab]; decide +kernel
theorem v3 : a 3 = 158 := by rw [a_eq, V_tab]; decide +kernel
theorem v4 : a 4 = 548 := by rw [a_eq, V_tab]; decide +kernel
theorem v5 : a 5 = 1600 := by rw [a_eq, V_tab]; decide +kernel
theorem v6 : a 6 = 4102 := by rw [a_eq, V_tab]; decide +kernel
theorem v7 : a 7 = 9503 := by rw [a_eq, V_tab]; decide +kernel
theorem v8 : a 8 = 20299 := by rw [a_eq, V_tab]; decide +kernel
theorem v9 : a 9 = 40570 := by rw [a_eq, V_tab]; decide +kernel
theorem v10 : a 10 = 76704 := by rw [a_eq, V_tab]; decide +kernel
def Pq (x : ℚ) : ℚ := (1 : ℚ) + (481/420 : ℚ) * x^1 + (4877/2520 : ℚ) * x^2 + (173/144 : ℚ) * x^3 + (259/480 : ℚ) * x^4 + (109/720 : ℚ) * x^5 + (1/40 : ℚ) * x^6 + (1/504 : ℚ) * x^7 + (1/10080 : ℚ) * x^8
theorem closed (n : ℕ) (hn : 0 ≤ n) : (a n : ℚ) = Pq (n : ℚ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 10
    · interval_cases n
      · rw [v0]; norm_num [Pq]
      · rw [v1]; norm_num [Pq]
      · rw [v2]; norm_num [Pq]
      · rw [v3]; norm_num [Pq]
      · rw [v4]; norm_num [Pq]
      · rw [v5]; norm_num [Pq]
      · rw [v6]; norm_num [Pq]
      · rw [v7]; norm_num [Pq]
      · rw [v8]; norm_num [Pq]
      · rw [v9]; norm_num [Pq]
    · obtain ⟨k, rfl⟩ : ∃ k, n = 0 + k + 1 + 9 := ⟨n - 10, by omega⟩
      rw [hrecA k]
      rw [ih (0 + k + 1 + 0) (by omega) (by omega)]
      rw [ih (0 + k + 1 + 1) (by omega) (by omega)]
      rw [ih (0 + k + 1 + 2) (by omega) (by omega)]
      rw [ih (0 + k + 1 + 3) (by omega) (by omega)]
      rw [ih (0 + k + 1 + 4) (by omega) (by omega)]
      rw [ih (0 + k + 1 + 5) (by omega) (by omega)]
      rw [ih (0 + k + 1 + 6) (by omega) (by omega)]
      rw [ih (0 + k + 1 + 7) (by omega) (by omega)]
      rw [ih (0 + k + 1 + 8) (by omega) (by omega)]
      push_cast
      simp only [Pq]
      ring
noncomputable def bq (n : ℕ) : ℚ := if n = 0 then 0 else (a n : ℚ)
theorem bq_closed (n : ℕ) (hn : 1 ≤ n) : bq n = Pq ((n : ℚ) + 0) := by
  unfold bq
  have := closed (n + 0) (by omega)
  push_cast at this
  first | (simp only [show n ≠ 0 by omega, if_false]; exact this) | exact this
theorem hb_all : ∀ n, ∑ j ∈ Finset.range (10), ([(1 : ℚ), (-9 : ℚ), (36 : ℚ), (-84 : ℚ), (126 : ℚ), (-126 : ℚ), (84 : ℚ), (-36 : ℚ), (9 : ℚ), (-1 : ℚ)] : List ℚ).getD j 0 * (if j ≤ n then bq (n - j) else 0) = if n ≤ 9 then ([(0 : ℚ), (6 : ℚ), (-18 : ℚ), (50 : ℚ), (-82 : ℚ), (88 : ℚ), (-62 : ℚ), (29 : ℚ), (-8 : ℚ), (1 : ℚ)] : List ℚ).getD n 0 else 0 := by
  intro n
  by_cases hn : n ≤ 9
  · interval_cases n <;> simp [Finset.sum_range_succ, bq, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] <;> norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
    rw [if_neg (by omega)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    have t0 : bq (k + 10 - 0) = Pq ((k : ℚ) + 10) := by
      rw [bq_closed _ (by omega), show k + 10 - 0 = k + 10 by omega]; push_cast; ring_nf
    have t1 : bq (k + 10 - 1) = Pq ((k : ℚ) + 9) := by
      rw [bq_closed _ (by omega), show k + 10 - 1 = k + 9 by omega]; push_cast; ring_nf
    have t2 : bq (k + 10 - 2) = Pq ((k : ℚ) + 8) := by
      rw [bq_closed _ (by omega), show k + 10 - 2 = k + 8 by omega]; push_cast; ring_nf
    have t3 : bq (k + 10 - 3) = Pq ((k : ℚ) + 7) := by
      rw [bq_closed _ (by omega), show k + 10 - 3 = k + 7 by omega]; push_cast; ring_nf
    have t4 : bq (k + 10 - 4) = Pq ((k : ℚ) + 6) := by
      rw [bq_closed _ (by omega), show k + 10 - 4 = k + 6 by omega]; push_cast; ring_nf
    have t5 : bq (k + 10 - 5) = Pq ((k : ℚ) + 5) := by
      rw [bq_closed _ (by omega), show k + 10 - 5 = k + 5 by omega]; push_cast; ring_nf
    have t6 : bq (k + 10 - 6) = Pq ((k : ℚ) + 4) := by
      rw [bq_closed _ (by omega), show k + 10 - 6 = k + 4 by omega]; push_cast; ring_nf
    have t7 : bq (k + 10 - 7) = Pq ((k : ℚ) + 3) := by
      rw [bq_closed _ (by omega), show k + 10 - 7 = k + 3 by omega]; push_cast; ring_nf
    have t8 : bq (k + 10 - 8) = Pq ((k : ℚ) + 2) := by
      rw [bq_closed _ (by omega), show k + 10 - 8 = k + 2 by omega]; push_cast; ring_nf
    have t9 : bq (k + 10 - 9) = Pq ((k : ℚ) + 1) := by
      rw [bq_closed _ (by omega), show k + 10 - 9 = k + 1 by omega]; push_cast; ring_nf
    rw [if_pos (show 0 ≤ k + 10 by omega), t0, if_pos (show 1 ≤ k + 10 by omega), t1, if_pos (show 2 ≤ k + 10 by omega), t2, if_pos (show 3 ≤ k + 10 by omega), t3, if_pos (show 4 ≤ k + 10 by omega), t4, if_pos (show 5 ≤ k + 10 by omega), t5, if_pos (show 6 ≤ k + 10 by omega), t6, if_pos (show 7 ≤ k + 10 by omega), t7, if_pos (show 8 ≤ k + 10 by omega), t8, if_pos (show 9 ≤ k + 10 by omega), t9]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Pq]
    ring
theorem recS (n : ℕ) (hn : 9 < n) : (a n : ℤ) = (9 : ℤ) * (a (n - 1) : ℤ) + (-36 : ℤ) * (a (n - 2) : ℤ) + (84 : ℤ) * (a (n - 3) : ℤ) + (-126 : ℤ) * (a (n - 4) : ℤ) + (126 : ℤ) * (a (n - 5) : ℤ) + (-84 : ℤ) * (a (n - 6) : ℤ) + (36 : ℤ) * (a (n - 7) : ℤ) + (-9 : ℤ) * (a (n - 8) : ℤ) + (1 : ℤ) * (a (n - 9) : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
  have h0 := closed (k + 10) (by omega)
  have e1 : k + 10 - 1 = k + 9 := by omega
  have h1 := closed (k + 9) (by omega)
  have e2 : k + 10 - 2 = k + 8 := by omega
  have h2 := closed (k + 8) (by omega)
  have e3 : k + 10 - 3 = k + 7 := by omega
  have h3 := closed (k + 7) (by omega)
  have e4 : k + 10 - 4 = k + 6 := by omega
  have h4 := closed (k + 6) (by omega)
  have e5 : k + 10 - 5 = k + 5 := by omega
  have h5 := closed (k + 5) (by omega)
  have e6 : k + 10 - 6 = k + 4 := by omega
  have h6 := closed (k + 4) (by omega)
  have e7 : k + 10 - 7 = k + 3 := by omega
  have h7 := closed (k + 3) (by omega)
  have e8 : k + 10 - 8 = k + 2 := by omega
  have h8 := closed (k + 2) (by omega)
  have e9 : k + 10 - 9 = k + 1 := by omega
  have h9 := closed (k + 1) (by omega)
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9]
  have key : (a (k + 10) : ℚ) = (9 : ℚ) * (a (k + 9) : ℚ) + (-36 : ℚ) * (a (k + 8) : ℚ) + (84 : ℚ) * (a (k + 7) : ℚ) + (-126 : ℚ) * (a (k + 6) : ℚ) + (126 : ℚ) * (a (k + 5) : ℚ) + (-84 : ℚ) * (a (k + 4) : ℚ) + (36 : ℚ) * (a (k + 3) : ℚ) + (-9 : ℚ) * (a (k + 2) : ℚ) + (1 : ℚ) * (a (k + 1) : ℚ) := by
    rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
    simp only [Pq]
    push_cast
    ring
  exact_mod_cast key

theorem gf_main : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - PowerSeries.X) ^ 9 =
    PowerSeries.X * (6 - 18 * PowerSeries.X + 50 * PowerSeries.X ^ 2 - 82 * PowerSeries.X ^ 3 + 88 * PowerSeries.X ^ 4 - 62 * PowerSeries.X ^ 5 + 29 * PowerSeries.X ^ 6 - 8 * PowerSeries.X ^ 7 + PowerSeries.X ^ 8) := by
  have h : PowerSeries.mk bq = (PowerSeries.X * (6 - 18 * PowerSeries.X + 50 * PowerSeries.X ^ 2 - 82 * PowerSeries.X ^ 3 + 88 * PowerSeries.X ^ 4 - 62 * PowerSeries.X ^ 5 + 29 * PowerSeries.X ^ 6 - 8 * PowerSeries.X ^ 7 + PowerSeries.X ^ 8)) * ((1 - PowerSeries.X) ^ 9)⁻¹ := by
    apply gf_gen bq 9 9 (fun j => [(1 : ℚ), -9, 36, -84, 126, -126, 84, -36, 9, -1].getD j 0) (fun j => [(0 : ℚ), 6, -18, 50, -82, 88, -62, 29, -8, 1].getD j 0)
    · simp [Finset.sum_range_succ, map_ofNat PowerSeries.C]
      ring
    · simp [Finset.sum_range_succ, map_ofNat PowerSeries.C]
      ring
    · norm_num
    · intro n hn
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by simp; omega)]
      rfl
    · exact hb_all
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)] at h
  exact h

end OMA.S_oeis_a223919

theorem OMA.solution : type_of% @OMA.S_oeis_a223919.main := by
  refine ⟨?_, OMA.S_oeis_a223919.gf_main, ?_⟩
  · intro n hn
    rw [OMA.S_oeis_a223919.closed n (by omega)]
    simp only [OMA.S_oeis_a223919.Pq]
    ring
  · intro n hn
    have := OMA.S_oeis_a223919.recS n hn
    linarith

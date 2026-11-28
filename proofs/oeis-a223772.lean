import OMAStatements.S_oeis_a223772
import Mathlib

namespace OMA.S_oeis_a223772

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


section flags

def KUni (s : List ℕ) : Prop := ∃ m, (s.take m).Pairwise (· ≤ ·) ∧ (s.drop m).Pairwise (· ≥ ·)

def fok (f : Fin 3) (b : Fin 2) : Prop := ¬ (f = 2 ∧ b = 1)
instance (f : Fin 3) (b : Fin 2) : Decidable (fok f b) := by unfold fok; infer_instance
def fnx (f : Fin 3) (b : Fin 2) : Fin 3 := if b = 1 then 1 else if f = 0 then 0 else 2

def runOK : Fin 3 → List (Fin 2) → Prop
  | _, [] => True
  | f, b :: l => fok f b ∧ runOK (fnx f b) l

def lmap (l : List (Fin 2)) : List ℕ := l.map Fin.val

def spec : Fin 3 → List (Fin 2) → Prop
  | 0, l => KUni (lmap l)
  | 1, l => (lmap l).Pairwise (· ≥ ·)
  | 2, l => ∀ b ∈ l, b = 0

theorem pw_const (l : List ℕ) (c : ℕ) (h : ∀ x ∈ l, x = c) : l.Pairwise (· ≥ ·) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a l ih =>
    refine List.pairwise_cons.mpr ⟨fun x hx => ?_, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩
    rw [h x (List.mem_cons_of_mem _ hx), h a (List.mem_cons_self)]

theorem kuni0 (s : List ℕ) : KUni (0 :: s) ↔ KUni s := by
  constructor
  · rintro ⟨m, h1, h2⟩
    cases m with
    | zero =>
      simp only [List.drop_zero, List.pairwise_cons] at h2
      exact ⟨0, by simp, by simpa using h2.2⟩
    | succ k =>
      simp only [List.take_succ_cons, List.drop_succ_cons, List.pairwise_cons] at h1 h2
      exact ⟨k, h1.2, h2⟩
  · rintro ⟨m, h1, h2⟩
    refine ⟨m + 1, ?_, ?_⟩
    · simp only [List.take_succ_cons, List.pairwise_cons]
      exact ⟨fun x _ => Nat.zero_le x, h1⟩
    · simpa using h2

theorem kuni1 (s : List ℕ) (hs : ∀ x ∈ s, x ≤ 1) : KUni (1 :: s) ↔ s.Pairwise (· ≥ ·) := by
  constructor
  · rintro ⟨m, h1, h2⟩
    cases m with
    | zero =>
      simp only [List.drop_zero, List.pairwise_cons] at h2
      exact h2.2
    | succ k =>
      simp only [List.take_succ_cons, List.drop_succ_cons, List.pairwise_cons] at h1 h2
      rw [← List.take_append_drop k s, List.pairwise_append]
      refine ⟨pw_const _ 1 (fun x hx => ?_), h2, fun a ha b hb => ?_⟩
      · have := h1.1 x hx
        have := hs x (List.mem_of_mem_take hx)
        omega
      · have := h1.1 a ha
        have := hs a (List.mem_of_mem_take ha)
        have := hs b (List.mem_of_mem_drop hb)
        omega
  · intro h
    refine ⟨0, by simp, ?_⟩
    simp only [List.drop_zero, List.pairwise_cons]
    exact ⟨fun x hx => hs x hx, h⟩

theorem ge1 (s : List ℕ) (hs : ∀ x ∈ s, x ≤ 1) : (1 :: s).Pairwise (· ≥ ·) ↔ s.Pairwise (· ≥ ·) := by
  rw [List.pairwise_cons]
  exact ⟨fun h => h.2, fun h => ⟨fun x hx => hs x hx, h⟩⟩

theorem ge0 (s : List ℕ) : (0 :: s).Pairwise (· ≥ ·) ↔ ∀ x ∈ s, x = 0 := by
  rw [List.pairwise_cons]
  exact ⟨fun h x hx => by have := h.1 x hx; omega,
    fun h => ⟨fun x hx => by have := h x hx; omega, pw_const s 0 h⟩⟩

theorem lmap_le (l : List (Fin 2)) : ∀ x ∈ lmap l, x ≤ 1 := by
  intro x hx
  simp only [lmap, List.mem_map] at hx
  obtain ⟨b, _, rfl⟩ := hx
  have := b.2
  omega

theorem lz (l : List (Fin 2)) : (∀ b ∈ l, b = 0) ↔ ∀ x ∈ lmap l, x = 0 := by
  constructor
  · intro h x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    simp [h b hb]
  · intro h b hb
    have := h b (List.mem_map_of_mem hb)
    exact Fin.ext (by simpa using this)

theorem runOK_iff : ∀ (l : List (Fin 2)) (f : Fin 3), runOK f l ↔ spec f l := by
  intro l
  induction l with
  | nil =>
    intro f
    fin_cases f
    · exact ⟨fun _ => ⟨0, by simp [lmap]⟩, fun _ => trivial⟩
    · exact ⟨fun _ => by simp [spec, lmap], fun _ => trivial⟩
    · exact ⟨fun _ => by simp [spec], fun _ => trivial⟩
  | cons b l ih =>
    intro f
    have hl := lmap_le l
    fin_cases f <;> fin_cases b
    · have h1 : fnx 0 0 = 0 := by decide
      have h2 : fok 0 0 := by decide
      show (fok 0 0 ∧ runOK (fnx 0 0) l) ↔ KUni ((0:ℕ) :: lmap l)
      rw [h1, kuni0]
      exact ⟨fun h => (ih 0).mp h.2, fun h => ⟨h2, (ih 0).mpr h⟩⟩
    · have h1 : fnx 0 1 = 1 := by decide
      have h2 : fok 0 1 := by decide
      show (fok 0 1 ∧ runOK (fnx 0 1) l) ↔ KUni ((1:ℕ) :: lmap l)
      rw [h1, kuni1 _ hl]
      exact ⟨fun h => (ih 1).mp h.2, fun h => ⟨h2, (ih 1).mpr h⟩⟩
    · have h1 : fnx 1 0 = 2 := by decide
      have h2 : fok 1 0 := by decide
      show (fok 1 0 ∧ runOK (fnx 1 0) l) ↔ ((0:ℕ) :: lmap l).Pairwise (· ≥ ·)
      rw [h1, ge0, ← lz]
      exact ⟨fun h => (ih 2).mp h.2, fun h => ⟨h2, (ih 2).mpr h⟩⟩
    · have h1 : fnx 1 1 = 1 := by decide
      have h2 : fok 1 1 := by decide
      show (fok 1 1 ∧ runOK (fnx 1 1) l) ↔ ((1:ℕ) :: lmap l).Pairwise (· ≥ ·)
      rw [h1, ge1 _ hl]
      exact ⟨fun h => (ih 1).mp h.2, fun h => ⟨h2, (ih 1).mpr h⟩⟩
    · have h1 : fnx 2 0 = 2 := by decide
      have h2 : fok 2 0 := by decide
      show (fok 2 0 ∧ runOK (fnx 2 0) l) ↔ ∀ x ∈ (0 :: l : List (Fin 2)), x = 0
      rw [h1, List.forall_mem_cons]
      exact ⟨fun h => ⟨rfl, (ih 2).mp h.2⟩, fun h => ⟨h2, (ih 2).mpr h.2⟩⟩
    · show (fok 2 1 ∧ runOK (fnx 2 1) l) ↔ ∀ x ∈ (1 :: l : List (Fin 2)), x = 0
      constructor
      · intro h; exact absurd ⟨rfl, rfl⟩ h.1
      · intro h; exact absurd (h 1 List.mem_cons_self) (by decide)
end flags


section extra

instance rokDec : ∀ (f : Fin 3) (l : List (Fin 2)), Decidable (runOK f l)
  | f, [] => isTrue trivial
  | f, b :: l => by
    haveI := rokDec (fnx f b) l
    unfold runOK; infer_instance

def pbk (f : Fin 3 → Fin 3) : Fin 3 → Fin 2 := fun j => if f j = 1 then 1 else 0
def nxk (f : Fin 3 → Fin 3) (c : Fin 3 → Fin 2) : Fin 3 → Fin 3 := fun j => fnx (f j) (c j)

theorem pbk_nxk (f : Fin 3 → Fin 3) (c : Fin 3 → Fin 2) : pbk (nxk f c) = c := by
  funext j
  unfold pbk nxk fnx
  have := (c j).2
  by_cases h : c j = 1
  · simp [h]
  · have : c j = 0 := by omega
    simp [this]
    split_ifs <;> decide

theorem uni_run (l : List (Fin 2)) : KUni (l.map Fin.val) ↔ runOK 0 l := by
  rw [runOK_iff]; exact Iff.rfl

theorem mono3 (v : Fin 3 → Fin 2) : Monotone v ↔ (v 0 ≤ v 1 ∧ v 1 ≤ v 2) := by
  constructor
  · intro h; exact ⟨h (by decide), h (by decide)⟩
  · rintro ⟨h1, h2⟩ a b hab
    fin_cases a <;> fin_cases b <;> simp at hab ⊢
    · exact h1
    · exact le_trans h1 h2
    · exact h2

end extra


section win

abbrev Col := Fin 3 → Fin 2

def Win : List Col → Prop
  | a :: b :: c :: t => ¬ (b 1 < a 2 ∧ b 1 < c 0) ∧ Win (b :: c :: t)
  | _ => True

def TC : Fin 2 → Col → List Col → Prop
  | _, _, [] => True
  | u, v, w :: l => ¬ (v 1 < u ∧ v 1 < w 0) ∧ TC (v 2) w l

def mkU (u : Fin 2) : Col := fun i => if i = 2 then u else 0

theorem win_congr (a a' b : Col) (l : List Col) (h : a 2 = a' 2) :
    Win (a :: b :: l) ↔ Win (a' :: b :: l) := by
  cases l with
  | nil => simp [Win]
  | cons c t => simp only [Win, h]

theorem tc_win : ∀ (l : List Col) (u : Fin 2) (v : Col), TC u v l ↔ Win (mkU u :: v :: l) := by
  intro l
  induction l with
  | nil => intro u v; simp [TC, Win]
  | cons w l ih =>
    intro u v
    rw [TC, ih]
    show _ ↔ ¬ (v 1 < (mkU u) 2 ∧ v 1 < w 0) ∧ Win (v :: w :: l)
    rw [win_congr (mkU (v 2)) v w l (by simp [mkU])]
    simp [mkU]

theorem win_zero (l : List Col) : Win (mkU 0 :: l) ↔ Win l := by
  cases l with
  | nil => simp [Win]
  | cons b t =>
    cases t with
    | nil => simp [Win]
    | cons c r =>
      show (¬ (b 1 < (mkU 0) 2 ∧ b 1 < c 0) ∧ Win (b :: c :: r)) ↔ Win (b :: c :: r)
      simp [mkU]

theorem tc_zero (l : List Col) : TC 0 (fun _ => 0) l ↔ Win l := by
  have : (fun _ : Fin 3 => (0 : Fin 2)) = mkU 0 := by
    funext i; simp [mkU]
  rw [this, tc_win, win_zero, win_zero]

theorem win_idx : ∀ l : List Col, Win l ↔
    ∀ (j : ℕ) (h : j + 2 < l.length), ¬ (l[j + 1] 1 < l[j] 2 ∧ l[j + 1] 1 < l[j + 2] 0) := by
  intro l
  induction l with
  | nil => simp [Win]
  | cons a t ih =>
    cases t with
    | nil => simp [Win]
    | cons b t' =>
      cases t' with
      | nil => simp [Win]
      | cons c r =>
        have ih' := ih
        rw [show Win (a :: b :: c :: r) ↔ ¬ (b 1 < a 2 ∧ b 1 < c 0) ∧ Win (b :: c :: r) from Iff.rfl, ih']
        constructor
        · rintro ⟨h0, h1⟩ j hj
          cases j with
          | zero => exact h0
          | succ j => exact h1 j (by simpa using hj)
        · intro h
          refine ⟨h 0 (by simp), fun j hj => ?_⟩
          exact h (j + 1) (by simpa using hj)

end win

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


def bit (f : Fin 3) : ℕ := if f = 1 then 1 else 0

def okP (s : Fin 3 → Fin 3) (r : Fin 3 → Fin 2) : Prop :=
  runOK 0 (List.ofFn r) ∧ (∀ j, fok (s j) (r j)) ∧ (∀ j : Fin 2, bit (s j.succ) ≤ (r j.castSucc : ℕ))
instance (s : Fin 3 → Fin 3) (r : Fin 3 → Fin 2) : Decidable (okP s r) := by unfold okP; infer_instance
def nxP (s : Fin 3 → Fin 3) (r : Fin 3 → Fin 2) : Fin 3 → Fin 3 := fun j => fnx (s j) (r j)

def pb (s : Fin 3 → Fin 3) : Fin 3 → Fin 2 := fun j => if s j = 1 then 1 else 0

def RR : (Fin 3 → Fin 2) → (Fin 3 → Fin 2) → Prop := fun r s => ∀ j : Fin 2, r j.succ ≤ s j.castSucc

theorem pb_nx (s : Fin 3 → Fin 3) (r : Fin 3 → Fin 2) : pb (nxP s r) = r := by
  funext j
  unfold pb nxP fnx
  have := (r j).2
  by_cases h : r j = 1 <;> simp [h]
  · have : r j = 0 := by omega
    simp [this]
    split_ifs <;> decide

theorem pb_le (f : Fin 3) (b : Fin 2) :
    (if f = 1 then (1 : Fin 2) else 0) ≤ b ↔ bit f ≤ (b : ℕ) := by
  unfold bit
  split_ifs <;> simp [Fin.le_def]

theorem acc_iff : ∀ (l : List (Fin 3 → Fin 2)) (s : Fin 3 → Fin 3),
    RunAcc okP nxP s l ↔ ((∀ r ∈ l, runOK 0 (List.ofFn r)) ∧
      (∀ j, runOK (s j) (l.map (fun r => r j))) ∧ (pb s :: l).IsChain RR) := by
  intro l
  induction l with
  | nil => intro s; simp [RunAcc, runOK]
  | cons a l ih =>
    intro s
    simp only [RunAcc, ih, pb_nx, okP, List.mem_cons, forall_eq_or_imp, List.map_cons, runOK,
      forall_and, List.isChain_cons_cons]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩
      exact ⟨⟨h1, h4⟩, ⟨h2, h5⟩, ⟨fun j => by simpa [RR, pb, pb_le] using h3 j, h6⟩⟩
    · rintro ⟨⟨h1, h4⟩, ⟨h2, h5⟩, ⟨h3, h6⟩⟩
      exact ⟨⟨h1, h2, fun j => by simpa [RR, pb, pb_le] using h3 j⟩, h4, h5, h6⟩

theorem sol_iff (l : List (Fin 3 → Fin 2)) :
    IsSolution l ↔ RunAcc okP nxP (fun _ => 0) l := by
  rw [acc_iff]
  unfold IsSolution
  have hrow : ∀ r : Fin 3 → Fin 2, Unimodal (List.ofFn fun j => (r j : ℕ)) ↔ runOK 0 (List.ofFn r) := by
    intro r
    rw [← uni_run, List.map_ofFn]; rfl
  have hcol : ∀ j : Fin 3, Unimodal (l.map fun r => (r j : ℕ)) ↔ runOK 0 (l.map fun r => r j) := by
    intro j
    rw [← uni_run, List.map_map]; rfl
  have hch : l.IsChain RR ↔ (pb (fun _ => 0) :: l).IsChain RR := by
    cases l with
    | nil => simp
    | cons a l =>
      rw [List.isChain_cons_cons]
      have : RR (pb fun _ => 0) a := by
        intro j; simp [pb]
      simp [this]
  have hch' : l.IsChain (fun r s => ∀ j : Fin 2, r j.succ ≤ s j.castSucc) ↔
      (pb (fun _ => 0) :: l).IsChain RR := hch
  rw [hch']
  simp only [hrow, hcol]

theorem a_eq (n : ℕ) : a n = V okP nxP n (fun _ => 0) := by
  unfold a
  rw [← cnt okP nxP n (fun _ => 0)]
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun l => by rw [sol_iff])

abbrev SS := Fin 3 → Fin 3
def s0 : SS := fun _ => 0
def code (s : SS) : ℕ := s 0 + 3 * s 1 + 9 * s 2

def Tset (s : SS) : Prop := code s ∈ [0, 1, 2, 3, 4, 5, 7, 8, 9, 11, 12, 13, 14, 17, 21, 22, 23, 25, 26]
instance (s : SS) : Decidable (Tset s) := by unfold Tset; infer_instance
theorem hT : ∀ s a, Tset s → okP s a → Tset (nxP s a) := by decide +kernel
theorem hs0 : ∀ a, okP s0 a → Tset (nxP s0 a) := by decide +kernel
def cc : ℕ → ℤ := fun j => [0, 0, -1, 7, -21, 35, -35, 21, -7, 1].getD j 0
def tb0 : List ℕ := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

def tb1 : List ℕ := [7, 7, 4, 3, 3, 0, 3, 3, 2, 4, 4, 2, 2, 2, 0, 0, 0, 0, 4, 4, 2, 2, 2, 0, 2, 2, 1]

def tb2 : List ℕ := [28, 18, 6, 8, 8, 0, 6, 5, 2, 8, 4, 0, 4, 4, 0, 0, 0, 0, 12, 8, 2, 4, 4, 0, 4, 3, 1]

def tb3 : List ℕ := [78, 36, 6, 17, 17, 0, 11, 7, 2, 16, 8, 0, 8, 8, 0, 0, 0, 0, 28, 14, 2, 7, 7, 0, 7, 4, 1]

def tb4 : List ℕ := [180, 67, 6, 32, 32, 0, 18, 9, 2, 30, 15, 0, 15, 15, 0, 0, 0, 0, 56, 23, 2, 11, 11, 0, 11, 5, 1]

def tb5 : List ℕ := [371, 120, 6, 56, 56, 0, 27, 11, 2, 52, 26, 0, 26, 26, 0, 0, 0, 0, 101, 36, 2, 16, 16, 0, 16, 6, 1]

def tb6 : List ℕ := [707, 208, 6, 93, 93, 0, 38, 13, 2, 84, 42, 0, 42, 42, 0, 0, 0, 0, 169, 54, 2, 22, 22, 0, 22, 7, 1]

def tb7 : List ℕ := [1269, 349, 6, 148, 148, 0, 51, 15, 2, 128, 64, 0, 64, 64, 0, 0, 0, 0, 267, 78, 2, 29, 29, 0, 29, 8, 1]

def tb8 : List ℕ := [2170, 567, 6, 227, 227, 0, 66, 17, 2, 186, 93, 0, 93, 93, 0, 0, 0, 0, 403, 109, 2, 37, 37, 0, 37, 9, 1]

def tb9 : List ℕ := [3563, 893, 6, 337, 337, 0, 83, 19, 2, 260, 130, 0, 130, 130, 0, 0, 0, 0, 586, 148, 2, 46, 46, 0, 46, 10, 1]

def tb10 : List ℕ := [5650, 1366, 6, 486, 486, 0, 102, 21, 2, 352, 176, 0, 176, 176, 0, 0, 0, 0, 826, 196, 2, 56, 56, 0, 56, 11, 1]

theorem Vstep (n : ℕ) (s : SS) : V okP nxP (n+1) s = ∑ r : Fin 3 → Fin 2, if okP s r then V okP nxP n (nxP s r) else 0 := rfl
theorem L0 : ∀ s : SS, V okP nxP 0 s = tb0.getD (code s) 0 := by
  decide +kernel

theorem L1 : ∀ s : SS, V okP nxP 1 s = tb1.getD (code s) 0 := by
  intro s
  rw [Vstep]
  simp only [L0]
  revert s
  decide +kernel

theorem L2 : ∀ s : SS, V okP nxP 2 s = tb2.getD (code s) 0 := by
  intro s
  rw [Vstep]
  simp only [L1]
  revert s
  decide +kernel

theorem L3 : ∀ s : SS, V okP nxP 3 s = tb3.getD (code s) 0 := by
  intro s
  rw [Vstep]
  simp only [L2]
  revert s
  decide +kernel

theorem L4 : ∀ s : SS, V okP nxP 4 s = tb4.getD (code s) 0 := by
  intro s
  rw [Vstep]
  simp only [L3]
  revert s
  decide +kernel

theorem L5 : ∀ s : SS, V okP nxP 5 s = tb5.getD (code s) 0 := by
  intro s
  rw [Vstep]
  simp only [L4]
  revert s
  decide +kernel

theorem L6 : ∀ s : SS, V okP nxP 6 s = tb6.getD (code s) 0 := by
  intro s
  rw [Vstep]
  simp only [L5]
  revert s
  decide +kernel

theorem L7 : ∀ s : SS, V okP nxP 7 s = tb7.getD (code s) 0 := by
  intro s
  rw [Vstep]
  simp only [L6]
  revert s
  decide +kernel

theorem L8 : ∀ s : SS, V okP nxP 8 s = tb8.getD (code s) 0 := by
  intro s
  rw [Vstep]
  simp only [L7]
  revert s
  decide +kernel

theorem L9 : ∀ s : SS, V okP nxP 9 s = tb9.getD (code s) 0 := by
  intro s
  rw [Vstep]
  simp only [L8]
  revert s
  decide +kernel

theorem L10 : ∀ s : SS, V okP nxP 10 s = tb10.getD (code s) 0 := by
  intro s
  rw [Vstep]
  simp only [L9]
  revert s
  decide +kernel

def tbl (k : ℕ) : List ℕ := [tb0, tb1, tb2, tb3, tb4, tb5, tb6, tb7, tb8, tb9, tb10].getD k []
theorem key : ∀ j, j < 10 → ∀ s : SS, V okP nxP (0 + j) s = (tbl (0 + j)).getD (code s) 0 := by
  intro j hj s
  interval_cases j
  · exact L0 s
  · exact L1 s
  · exact L2 s
  · exact L3 s
  · exact L4 s
  · exact L5 s
  · exact L6 s
  · exact L7 s
  · exact L8 s
  · exact L9 s
theorem h0chk : ∀ s : SS, Tset s → ∑ j ∈ Finset.range 10, cc j * (((tbl (0 + j)).getD (code s) 0 : ℕ) : ℤ) = 0 := by
  decide +kernel
theorem h0 : ∀ s, Tset s → ∑ j ∈ Finset.range (10), cc j * (V okP nxP (0 + j) s : ℤ) = 0 := by
  intro s hs
  rw [Finset.sum_congr rfl (fun j hj => by rw [key j (Finset.mem_range.1 hj) s])]
  exact h0chk s hs
theorem hrecV (n : ℕ) : ∑ j ∈ Finset.range (10), cc j * (a (0 + n + 1 + j) : ℤ) = 0 := by
  have := rec_next okP nxP Tset hT 0 9 cc h0 s0 hs0 n
  simp only [a_eq]
  exact this
theorem hrecA (k : ℕ) : (a (0 + k + 1 + 9) : ℚ) = (1 : ℚ) * a (0 + k + 1 + 2) + (-7 : ℚ) * a (0 + k + 1 + 3) + (21 : ℚ) * a (0 + k + 1 + 4) + (-35 : ℚ) * a (0 + k + 1 + 5) + (35 : ℚ) * a (0 + k + 1 + 6) + (-21 : ℚ) * a (0 + k + 1 + 7) + (7 : ℚ) * a (0 + k + 1 + 8) := by
  have h := hrecV k
  have e0 : cc 0 = 0 := rfl
  have e1 : cc 1 = 0 := rfl
  have e2 : cc 2 = -1 := rfl
  have e3 : cc 3 = 7 := rfl
  have e4 : cc 4 = -21 := rfl
  have e5 : cc 5 = 35 := rfl
  have e6 : cc 6 = -35 := rfl
  have e7 : cc 7 = 21 := rfl
  have e8 : cc 8 = -7 := rfl
  have e9 : cc 9 = 1 := rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9] at h
  have h' := congrArg (Int.cast : ℤ → ℚ) h
  push_cast at h'
  linarith
theorem v0 : a 0 = 1 := by rw [a_eq, L0]; decide +kernel
theorem v1 : a 1 = 7 := by rw [a_eq, L1]; decide +kernel
theorem v2 : a 2 = 28 := by rw [a_eq, L2]; decide +kernel
theorem v3 : a 3 = 78 := by rw [a_eq, L3]; decide +kernel
theorem v4 : a 4 = 180 := by rw [a_eq, L4]; decide +kernel
theorem v5 : a 5 = 371 := by rw [a_eq, L5]; decide +kernel
theorem v6 : a 6 = 707 := by rw [a_eq, L6]; decide +kernel
theorem v7 : a 7 = 1269 := by rw [a_eq, L7]; decide +kernel
theorem v8 : a 8 = 2170 := by rw [a_eq, L8]; decide +kernel
theorem v9 : a 9 = 3563 := by rw [a_eq, L9]; decide +kernel
theorem v10 : a 10 = 5650 := by rw [a_eq, L10]; decide +kernel
def Pq (x : ℚ) : ℚ := (2 : ℚ) + (-8/15 : ℚ) * x^1 + (1727/360 : ℚ) * x^2 + (25/48 : ℚ) * x^3 + (29/144 : ℚ) * x^4 + (1/80 : ℚ) * x^5 + (1/720 : ℚ) * x^6
theorem closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = Pq (n : ℚ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 10
    · interval_cases n
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
noncomputable def bq (n : ℕ) : ℚ := (a (n + 1) : ℚ)
theorem bq_closed (n : ℕ) (hn : 0 ≤ n) : bq n = Pq ((n : ℚ) + 1) := by
  unfold bq
  have := closed (n + 1) (by omega)
  push_cast at this
  first | (simp only [show n ≠ 0 by omega, if_false]; exact this) | exact this
theorem hb_all : ∀ n, ∑ j ∈ Finset.range (8), ([(1 : ℚ), (-7 : ℚ), (21 : ℚ), (-35 : ℚ), (35 : ℚ), (-21 : ℚ), (7 : ℚ), (-1 : ℚ)] : List ℚ).getD j 0 * (if j ≤ n then bq (n - j) else 0) = if n ≤ 6 then ([(7 : ℚ), (-21 : ℚ), (29 : ℚ), (-23 : ℚ), (14 : ℚ), (-7 : ℚ), (2 : ℚ)] : List ℚ).getD n 0 else 0 := by
  intro n
  by_cases hn : n ≤ 7
  · interval_cases n <;> simp [Finset.sum_range_succ, bq, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] <;> norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
    rw [if_neg (by omega)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    have t0 : bq (k + 8 - 0) = Pq ((k : ℚ) + 9) := by
      rw [bq_closed _ (by omega), show k + 8 - 0 = k + 8 by omega]; push_cast; ring_nf
    have t1 : bq (k + 8 - 1) = Pq ((k : ℚ) + 8) := by
      rw [bq_closed _ (by omega), show k + 8 - 1 = k + 7 by omega]; push_cast; ring_nf
    have t2 : bq (k + 8 - 2) = Pq ((k : ℚ) + 7) := by
      rw [bq_closed _ (by omega), show k + 8 - 2 = k + 6 by omega]; push_cast; ring_nf
    have t3 : bq (k + 8 - 3) = Pq ((k : ℚ) + 6) := by
      rw [bq_closed _ (by omega), show k + 8 - 3 = k + 5 by omega]; push_cast; ring_nf
    have t4 : bq (k + 8 - 4) = Pq ((k : ℚ) + 5) := by
      rw [bq_closed _ (by omega), show k + 8 - 4 = k + 4 by omega]; push_cast; ring_nf
    have t5 : bq (k + 8 - 5) = Pq ((k : ℚ) + 4) := by
      rw [bq_closed _ (by omega), show k + 8 - 5 = k + 3 by omega]; push_cast; ring_nf
    have t6 : bq (k + 8 - 6) = Pq ((k : ℚ) + 3) := by
      rw [bq_closed _ (by omega), show k + 8 - 6 = k + 2 by omega]; push_cast; ring_nf
    have t7 : bq (k + 8 - 7) = Pq ((k : ℚ) + 2) := by
      rw [bq_closed _ (by omega), show k + 8 - 7 = k + 1 by omega]; push_cast; ring_nf
    rw [if_pos (show 0 ≤ k + 8 by omega), t0, if_pos (show 1 ≤ k + 8 by omega), t1, if_pos (show 2 ≤ k + 8 by omega), t2, if_pos (show 3 ≤ k + 8 by omega), t3, if_pos (show 4 ≤ k + 8 by omega), t4, if_pos (show 5 ≤ k + 8 by omega), t5, if_pos (show 6 ≤ k + 8 by omega), t6, if_pos (show 7 ≤ k + 8 by omega), t7]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Pq]
    ring
theorem recS (n : ℕ) (hn : 7 < n) : (a n : ℤ) = (7 : ℤ) * (a (n - 1) : ℤ) + (-21 : ℤ) * (a (n - 2) : ℤ) + (35 : ℤ) * (a (n - 3) : ℤ) + (-35 : ℤ) * (a (n - 4) : ℤ) + (21 : ℤ) * (a (n - 5) : ℤ) + (-7 : ℤ) * (a (n - 6) : ℤ) + (1 : ℤ) * (a (n - 7) : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
  have h0 := closed (k + 8) (by omega)
  have e1 : k + 8 - 1 = k + 7 := by omega
  have h1 := closed (k + 7) (by omega)
  have e2 : k + 8 - 2 = k + 6 := by omega
  have h2 := closed (k + 6) (by omega)
  have e3 : k + 8 - 3 = k + 5 := by omega
  have h3 := closed (k + 5) (by omega)
  have e4 : k + 8 - 4 = k + 4 := by omega
  have h4 := closed (k + 4) (by omega)
  have e5 : k + 8 - 5 = k + 3 := by omega
  have h5 := closed (k + 3) (by omega)
  have e6 : k + 8 - 6 = k + 2 := by omega
  have h6 := closed (k + 2) (by omega)
  have e7 : k + 8 - 7 = k + 1 := by omega
  have h7 := closed (k + 1) (by omega)
  rw [e1, e2, e3, e4, e5, e6, e7]
  have key : (a (k + 8) : ℚ) = (7 : ℚ) * (a (k + 7) : ℚ) + (-21 : ℚ) * (a (k + 6) : ℚ) + (35 : ℚ) * (a (k + 5) : ℚ) + (-35 : ℚ) * (a (k + 4) : ℚ) + (21 : ℚ) * (a (k + 3) : ℚ) + (-7 : ℚ) * (a (k + 2) : ℚ) + (1 : ℚ) * (a (k + 1) : ℚ) := by
    rw [h0, h1, h2, h3, h4, h5, h6, h7]
    simp only [Pq]
    push_cast
    ring
  exact_mod_cast key


theorem gf_main : PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - PowerSeries.X) ^ 7 =
    7 - 21 * PowerSeries.X ^ 1 + 29 * PowerSeries.X ^ 2 - 23 * PowerSeries.X ^ 3 + 14 * PowerSeries.X ^ 4 - 7 * PowerSeries.X ^ 5 + 2 * PowerSeries.X ^ 6 := by
  have h : PowerSeries.mk bq = (7 - 21 * PowerSeries.X ^ 1 + 29 * PowerSeries.X ^ 2 - 23 * PowerSeries.X ^ 3 + 14 * PowerSeries.X ^ 4 - 7 * PowerSeries.X ^ 5 + 2 * PowerSeries.X ^ 6) * ((1 - PowerSeries.X) ^ 7)⁻¹ := by
    apply gf_gen bq 7 6 (fun j => [(1 : ℚ), -7, 21, -35, 35, -21, 7, -1].getD j 0) (fun j => [(7 : ℚ), -21, 29, -23, 14, -7, 2].getD j 0)
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

end OMA.S_oeis_a223772

theorem OMA.solution : type_of% @OMA.S_oeis_a223772.main := by
  refine ⟨OMA.S_oeis_a223772.gf_main, ?_⟩
  intro n hn
  have := OMA.S_oeis_a223772.recS n hn
  linarith

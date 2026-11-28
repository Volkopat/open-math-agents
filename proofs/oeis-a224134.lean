import OMAStatements.S_oeis_a224134
import Mathlib

namespace OMA.S_oeis_a224134

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


section win2

variable {A : Type}

def Tri (T : A → A → A → Prop) : List A → Prop
  | a :: b :: c :: t => T a b c ∧ Tri T (b :: c :: t)
  | _ => True

theorem tri_idx (T : A → A → A → Prop) : ∀ l : List A, Tri T l ↔
    ∀ (j : ℕ) (h : j + 2 < l.length), T l[j] l[j + 1] l[j + 2] := by
  intro l
  induction l with
  | nil => simp [Tri]
  | cons a t ih =>
    cases t with
    | nil => simp [Tri]
    | cons b t' =>
      cases t' with
      | nil => simp [Tri]
      | cons c r =>
        have ih' := ih
        rw [show Tri T (a :: b :: c :: r) ↔ T a b c ∧ Tri T (b :: c :: r) from Iff.rfl, ih']
        constructor
        · rintro ⟨h0, h1⟩ j hj
          cases j with
          | zero => exact h0
          | succ j => exact h1 j (by simpa using hj)
        · intro h
          refine ⟨h 0 (by simp), fun j hj => ?_⟩
          exact h (j + 1) (by simpa using hj)

variable (U : A → Prop) (B : A → A → Prop) (T : A → A → A → Prop)

def okW (s : Option A × Option A) (c : A) : Prop :=
  U c ∧ (match s.2 with | none => True | some b => B b c) ∧
    (match s.1, s.2 with | some a, some b => T a b c | _, _ => True)

def nxW (s : Option A × Option A) (c : A) : Option A × Option A := (s.2, some c)

instance okWDec [DecidablePred U] [∀ a b, Decidable (B a b)] [∀ a b c, Decidable (T a b c)]
    (s : Option A × Option A) (c : A) : Decidable (okW U B T s c) := by
  unfold okW
  rcases s with ⟨p2, p1⟩
  cases p2 <;> cases p1 <;> dsimp only <;> infer_instance

def TsetW (s : Option A × Option A) : Prop :=
  match s.2 with
  | none => False
  | some b => U b ∧ (match s.1 with | none => True | some a => U a ∧ B a b)

instance tsetWDec [DecidablePred U] [∀ a b, Decidable (B a b)] (s : Option A × Option A) :
    Decidable (TsetW U B s) := by
  unfold TsetW
  rcases s with ⟨p2, p1⟩
  cases p2 <;> cases p1 <;> dsimp only <;> infer_instance

theorem hT_W (s : Option A × Option A) (c : A) (hs : TsetW U B s) (h : okW U B T s c) :
    TsetW U B (nxW s c) := by
  rcases s with ⟨p2, p1⟩
  cases p1 with
  | none => exact absurd hs (by simp [TsetW])
  | some b =>
    simp only [TsetW, okW, nxW] at hs h ⊢
    exact ⟨h.1, hs.1, h.2.1⟩

theorem hs0_W (c : A) (h : okW U B T (none, none) c) : TsetW U B (nxW (none, none) c) := by
  simp only [TsetW, okW, nxW] at h ⊢
  exact ⟨h.1, trivial⟩

theorem acc_S2 : ∀ (l : List A) (a b : A), RunAcc (okW U B T) nxW (some a, some b) l ↔
    ((∀ c ∈ l, U c) ∧ (b :: l).IsChain B ∧ Tri T (a :: b :: l)) := by
  intro l
  induction l with
  | nil => intro a b; simp [RunAcc, Tri]
  | cons c l ih =>
    intro a b
    rw [RunAcc]
    show (okW U B T (some a, some b) c ∧ RunAcc (okW U B T) nxW (some b, some c) l) ↔ _
    rw [ih b c]
    simp only [okW, nxW, List.mem_cons, forall_eq_or_imp, List.isChain_cons_cons]
    show _ ↔ _ ∧ _ ∧ (T a b c ∧ Tri T (b :: c :: l))
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩
      exact ⟨⟨h1, h4⟩, ⟨h2, h5⟩, h3, h6⟩
    · rintro ⟨⟨h1, h4⟩, ⟨h2, h5⟩, h3, h6⟩
      exact ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩

theorem acc_Q : ∀ (l : List A) (b : A), RunAcc (okW U B T) nxW (none, some b) l ↔
    ((∀ c ∈ l, U c) ∧ (b :: l).IsChain B ∧ Tri T (b :: l)) := by
  intro l b
  cases l with
  | nil => simp [RunAcc, Tri]
  | cons c l =>
    rw [RunAcc]
    show (okW U B T (none, some b) c ∧ RunAcc (okW U B T) nxW (some b, some c) l) ↔ _
    rw [acc_S2 U B T l b c]
    simp only [okW, List.mem_cons, forall_eq_or_imp, List.isChain_cons_cons]
    constructor
    · rintro ⟨⟨h1, h2, _⟩, h4, h5, h6⟩
      exact ⟨⟨h1, h4⟩, ⟨h2, h5⟩, h6⟩
    · rintro ⟨⟨h1, h4⟩, ⟨h2, h5⟩, h6⟩
      exact ⟨⟨h1, h2, trivial⟩, h4, h5, h6⟩

theorem acc_R : ∀ (l : List A), RunAcc (okW U B T) nxW (none, none) l ↔
    ((∀ c ∈ l, U c) ∧ l.IsChain B ∧ Tri T l) := by
  intro l
  cases l with
  | nil => simp [RunAcc, Tri]
  | cons c l =>
    rw [RunAcc]
    show (okW U B T (none, none) c ∧ RunAcc (okW U B T) nxW (none, some c) l) ↔ _
    rw [acc_Q U B T l c]
    simp only [okW, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨⟨h1, _, _⟩, h4, h5, h6⟩
      exact ⟨⟨h1, h4⟩, h5, h6⟩
    · rintro ⟨⟨h1, h4⟩, h5, h6⟩
      exact ⟨⟨h1, trivial, trivial⟩, h4, h5, h6⟩

theorem good_iff {n : ℕ} (x : Fin n → A) :
    ((∀ i, U (x i)) ∧ (∀ i j : Fin n, j.val = i.val + 1 → B (x i) (x j)) ∧
      (∀ i j l : Fin n, j.val = i.val + 1 → l.val = j.val + 1 → T (x i) (x j) (x l))) ↔
    RunAcc (okW U B T) nxW (none, none) (List.ofFn x) := by
  rw [acc_R, List.isChain_ofFn, tri_idx]
  simp only [List.getElem_ofFn, List.length_ofFn]
  have h1 : (∀ c ∈ List.ofFn x, U c) ↔ ∀ i, U (x i) := by
    simp [List.mem_ofFn']
  rw [h1]
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · constructor
    · intro h i hi
      exact h ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl
    · intro h i j hij
      obtain ⟨iv, hiv⟩ := i
      obtain ⟨jv, hjv⟩ := j
      have e : jv = iv + 1 := hij
      subst e
      exact h iv hjv
  · constructor
    · intro h i hi
      exact h ⟨i, by omega⟩ ⟨i + 1, by omega⟩ ⟨i + 2, hi⟩ rfl rfl
    · intro h i j l hij hjl
      obtain ⟨iv, hiv⟩ := i
      obtain ⟨jv, hjv⟩ := j
      obtain ⟨lv, hlv⟩ := l
      have e1 : jv = iv + 1 := hij
      have e2 : lv = jv + 1 := hjl
      subst e1
      subst e2
      exact h iv hlv

end win2


abbrev AL := Fin 3 → Fin 2
instance : DecidableRel BlockOK := fun u v => by unfold BlockOK; infer_instance
instance : ∀ u v w, Decidable (TriOK u v w) := fun u v w => by unfold TriOK; infer_instance
abbrev U0 : AL → Prop := fun _ => True
instance : DecidablePred U0 := fun a => by unfold U0; infer_instance
abbrev SS := Option AL × Option AL
abbrev okP : SS → AL → Prop := okW U0 BlockOK TriOK
abbrev nxP : SS → AL → SS := nxW
def s0 : SS := (none, none)

theorem a_eq (n : ℕ) : a n = V okP nxP n s0 := by
  unfold a
  rw [← cnt okP nxP n s0, ← card_ofFn n (fun l => RunAcc okP nxP s0 l)]
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun x => by
    have h := good_iff U0 BlockOK TriOK x
    unfold Good
    exact ⟨fun hg => h.mp ⟨fun _ => trivial, hg⟩, fun hr => (h.mpr hr).2⟩)

def Tset (s : SS) : Prop := TsetW U0 BlockOK s
instance (s : SS) : Decidable (Tset s) := by unfold Tset; infer_instance
theorem hT : ∀ s a, Tset s → okP s a → Tset (nxP s a) := fun s a h1 h2 => hT_W U0 BlockOK TriOK s a h1 h2
theorem hs0 : ∀ a, okP s0 a → Tset (nxP s0 a) := fun a h => hs0_W U0 BlockOK TriOK a h
def cc : ℕ → ℤ := fun j => [0, 0, 1, -4, 6, -4, 1].getD j 0
theorem h0 : ∀ s, Tset s → ∑ j ∈ Finset.range (7), cc j * (V okP nxP (0 + j) s : ℤ) = 0 := by decide +kernel
theorem hrecV (n : ℕ) : ∑ j ∈ Finset.range (7), cc j * (a (0 + n + 1 + j) : ℤ) = 0 := by
  have := rec_next okP nxP Tset hT 0 6 cc h0 s0 hs0 n
  simp only [a_eq]
  exact this
theorem hrecA (k : ℕ) : (a (0 + k + 1 + 6) : ℚ) = (-1 : ℚ) * a (0 + k + 1 + 2) + (4 : ℚ) * a (0 + k + 1 + 3) + (-6 : ℚ) * a (0 + k + 1 + 4) + (4 : ℚ) * a (0 + k + 1 + 5) := by
  have h := hrecV k
  have e0 : cc 0 = 0 := rfl
  have e1 : cc 1 = 0 := rfl
  have e2 : cc 2 = 1 := rfl
  have e3 : cc 3 = -4 := rfl
  have e4 : cc 4 = 6 := rfl
  have e5 : cc 5 = -4 := rfl
  have e6 : cc 6 = 1 := rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, e3, e4, e5, e6] at h
  have h' := congrArg (Int.cast : ℤ → ℚ) h
  push_cast at h'
  linarith
theorem v0 : a 0 = 1 := by rw [a_eq]; decide +kernel
theorem v1 : a 1 = 8 := by rw [a_eq]; decide +kernel
theorem v2 : a 2 = 27 := by rw [a_eq]; decide +kernel
theorem v3 : a 3 = 58 := by rw [a_eq]; decide +kernel
theorem v4 : a 4 = 106 := by rw [a_eq]; decide +kernel
theorem v5 : a 5 = 175 := by rw [a_eq]; decide +kernel
theorem v6 : a 6 = 269 := by rw [a_eq]; decide +kernel
theorem v7 : a 7 = 392 := by rw [a_eq]; decide +kernel
def Pq (x : ℚ) : ℚ := (35/6 : ℚ) * x^1 + (5/2 : ℚ) * x^2 + (2/3 : ℚ) * x^3
theorem closed (n : ℕ) (hn : 2 ≤ n) : (a n : ℚ) = Pq (n : ℚ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 7
    · interval_cases n
      · rw [v2]; norm_num [Pq]
      · rw [v3]; norm_num [Pq]
      · rw [v4]; norm_num [Pq]
      · rw [v5]; norm_num [Pq]
      · rw [v6]; norm_num [Pq]
    · obtain ⟨k, rfl⟩ : ∃ k, n = 0 + k + 1 + 6 := ⟨n - 7, by omega⟩
      rw [hrecA k]
      rw [ih (0 + k + 1 + 2) (by omega) (by omega)]
      rw [ih (0 + k + 1 + 3) (by omega) (by omega)]
      rw [ih (0 + k + 1 + 4) (by omega) (by omega)]
      rw [ih (0 + k + 1 + 5) (by omega) (by omega)]
      push_cast
      simp only [Pq]
      ring
noncomputable def bq (n : ℕ) : ℚ := if n = 0 then 0 else (a n : ℚ)
theorem bq_closed (n : ℕ) (hn : 2 ≤ n) : bq n = Pq ((n : ℚ) + 0) := by
  unfold bq
  have := closed (n + 0) (by omega)
  push_cast at this
  first | (simp only [show n ≠ 0 by omega, if_false]; exact this) | exact this
theorem hb_all : ∀ n, ∑ j ∈ Finset.range (5), ([(1 : ℚ), (-4 : ℚ), (6 : ℚ), (-4 : ℚ), (1 : ℚ)] : List ℚ).getD j 0 * (if j ≤ n then bq (n - j) else 0) = if n ≤ 5 then ([(0 : ℚ), (8 : ℚ), (-5 : ℚ), (-2 : ℚ), (4 : ℚ), (-1 : ℚ)] : List ℚ).getD n 0 else 0 := by
  intro n
  by_cases hn : n ≤ 5
  · interval_cases n <;> simp [Finset.sum_range_succ, bq, v0, v1, v2, v3, v4, v5, v6, v7] <;> norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
    rw [if_neg (by omega)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    have t0 : bq (k + 6 - 0) = Pq ((k : ℚ) + 6) := by
      rw [bq_closed _ (by omega), show k + 6 - 0 = k + 6 by omega]; push_cast; ring_nf
    have t1 : bq (k + 6 - 1) = Pq ((k : ℚ) + 5) := by
      rw [bq_closed _ (by omega), show k + 6 - 1 = k + 5 by omega]; push_cast; ring_nf
    have t2 : bq (k + 6 - 2) = Pq ((k : ℚ) + 4) := by
      rw [bq_closed _ (by omega), show k + 6 - 2 = k + 4 by omega]; push_cast; ring_nf
    have t3 : bq (k + 6 - 3) = Pq ((k : ℚ) + 3) := by
      rw [bq_closed _ (by omega), show k + 6 - 3 = k + 3 by omega]; push_cast; ring_nf
    have t4 : bq (k + 6 - 4) = Pq ((k : ℚ) + 2) := by
      rw [bq_closed _ (by omega), show k + 6 - 4 = k + 2 by omega]; push_cast; ring_nf
    rw [if_pos (show 0 ≤ k + 6 by omega), t0, if_pos (show 1 ≤ k + 6 by omega), t1, if_pos (show 2 ≤ k + 6 by omega), t2, if_pos (show 3 ≤ k + 6 by omega), t3, if_pos (show 4 ≤ k + 6 by omega), t4]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Pq]
    ring
theorem recS (n : ℕ) (hn : 5 < n) : (a n : ℤ) = (4 : ℤ) * (a (n - 1) : ℤ) + (-6 : ℤ) * (a (n - 2) : ℤ) + (4 : ℤ) * (a (n - 3) : ℤ) + (-1 : ℤ) * (a (n - 4) : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  have h0 := closed (k + 6) (by omega)
  have e1 : k + 6 - 1 = k + 5 := by omega
  have h1 := closed (k + 5) (by omega)
  have e2 : k + 6 - 2 = k + 4 := by omega
  have h2 := closed (k + 4) (by omega)
  have e3 : k + 6 - 3 = k + 3 := by omega
  have h3 := closed (k + 3) (by omega)
  have e4 : k + 6 - 4 = k + 2 := by omega
  have h4 := closed (k + 2) (by omega)
  rw [e1, e2, e3, e4]
  have key : (a (k + 6) : ℚ) = (4 : ℚ) * (a (k + 5) : ℚ) + (-6 : ℚ) * (a (k + 4) : ℚ) + (4 : ℚ) * (a (k + 3) : ℚ) + (-1 : ℚ) * (a (k + 2) : ℚ) := by
    rw [h0, h1, h2, h3, h4]
    simp only [Pq]
    push_cast
    ring
  exact_mod_cast key


theorem gf_main : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  unfold G
  apply gf_gen bq 4 5 (fun j => [(1 : ℚ), -4, 6, -4, 1].getD j 0) (fun j => [(0 : ℚ), 8, -5, -2, 4, -1].getD j 0)
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

end OMA.S_oeis_a224134

theorem OMA.solution : type_of% @OMA.S_oeis_a224134.main := by
  refine ⟨?_, OMA.S_oeis_a224134.gf_main, ?_⟩
  · intro n hn
    have := OMA.S_oeis_a224134.recS n (by omega)
    linarith
  · intro n hn
    rw [OMA.S_oeis_a224134.closed n (by omega)]
    simp only [OMA.S_oeis_a224134.Pq]
    ring

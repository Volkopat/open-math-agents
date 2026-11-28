import OMAStatements.S_oeis_a224147
import Mathlib

namespace OMA.S_oeis_a224147

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


section finuni

def specF : Fin 3 → ∀ {L : ℕ}, (Fin L → Fin 2) → Prop
  | 0, _, g => ∀ a b c : Fin _, a < b → b < c → ¬ (g b < g a ∧ g b < g c)
  | 1, _, g => ∀ a b : Fin _, a < b → ¬ (g a < g b)
  | 2, _, g => ∀ a, g a = 0

theorem specF_nil (f : Fin 3) (g : Fin 0 → Fin 2) : specF f g := by
  fin_cases f
  · intro a; exact a.elim0
  · intro a; exact a.elim0
  · intro a; exact a.elim0

theorem sF0_0 {L : ℕ} (g : Fin (L + 1) → Fin 2) (h : g 0 = 0) :
    specF 0 g ↔ specF 0 (fun i => g i.succ) := by
  simp [specF, Fin.forall_fin_succ, h]

theorem sF0_1 {L : ℕ} (g : Fin (L + 1) → Fin 2) (h : g 0 = 1) :
    specF 0 g ↔ specF 1 (fun i => g i.succ) := by
  simp only [specF, Fin.forall_fin_succ, h]
  simp
  constructor
  · rintro ⟨h1, _⟩ a b hab
    by_cases ha : g a.succ = 0
    · exact h1 a b hab ha
    · have := (g b.succ).2
      have := (g a.succ).2
      have hv : (g a.succ).val ≠ 0 := fun hh => ha (Fin.ext hh)
      rw [Fin.le_def]; omega
  · intro h
    exact ⟨fun i j hij _ => h i j hij, fun i j k hij hjk _ => h j k hjk⟩

theorem sF1_1 {L : ℕ} (g : Fin (L + 1) → Fin 2) (h : g 0 = 1) :
    specF 1 g ↔ specF 1 (fun i => g i.succ) := by
  simp [specF, Fin.forall_fin_succ, h]
  intro _ i
  have := (g i.succ).2
  exact Fin.le_def.mpr (by simp; omega)

theorem sF1_0 {L : ℕ} (g : Fin (L + 1) → Fin 2) (h : g 0 = 0) :
    specF 1 g ↔ specF 2 (fun i => g i.succ) := by
  simp [specF, Fin.forall_fin_succ, h]
  intro hh i j _
  rw [hh i, hh j]

theorem sF2_0 {L : ℕ} (g : Fin (L + 1) → Fin 2) (h : g 0 = 0) :
    specF 2 g ↔ specF 2 (fun i => g i.succ) := by
  simp [specF, Fin.forall_fin_succ, h]

theorem sF2_1 {L : ℕ} (g : Fin (L + 1) → Fin 2) (h : g 0 = 1) : ¬ specF 2 g := by
  intro hh; have := hh 0; simp [h] at this

theorem runF : ∀ (L : ℕ) (f : Fin 3) (g : Fin L → Fin 2), runOK f (List.ofFn g) ↔ specF f g := by
  intro L
  induction L with
  | zero => intro f g; simp only [List.ofFn_zero, runOK]; exact ⟨fun _ => specF_nil f g, fun _ => trivial⟩
  | succ L ih =>
    intro f g
    rw [List.ofFn_succ, runOK]
    have hg : g 0 = 0 ∨ g 0 = 1 := by
      have := (g 0).2
      rcases Fin.exists_fin_two.mp ⟨g 0, rfl⟩ with h | h <;> simp [h]
    rcases hg with h | h
    · rw [h]
      fin_cases f
      · have h1 : fnx 0 0 = 0 := by decide
        have h2 : fok 0 0 := by decide
        show (fok 0 0 ∧ runOK (fnx 0 0) (List.ofFn fun i => g i.succ)) ↔ specF 0 g
        rw [sF0_0 g h, ← ih 0 (fun i => g i.succ), h1]
        exact ⟨fun hh => hh.2, fun hh => ⟨h2, hh⟩⟩
      · have h1 : fnx 1 0 = 2 := by decide
        have h2 : fok 1 0 := by decide
        show (fok 1 0 ∧ runOK (fnx 1 0) (List.ofFn fun i => g i.succ)) ↔ specF 1 g
        rw [sF1_0 g h, ← ih 2 (fun i => g i.succ), h1]
        exact ⟨fun hh => hh.2, fun hh => ⟨h2, hh⟩⟩
      · have h1 : fnx 2 0 = 2 := by decide
        have h2 : fok 2 0 := by decide
        show (fok 2 0 ∧ runOK (fnx 2 0) (List.ofFn fun i => g i.succ)) ↔ specF 2 g
        rw [sF2_0 g h, ← ih 2 (fun i => g i.succ), h1]
        exact ⟨fun hh => hh.2, fun hh => ⟨h2, hh⟩⟩
    · rw [h]
      fin_cases f
      · have h1 : fnx 0 1 = 1 := by decide
        have h2 : fok 0 1 := by decide
        show (fok 0 1 ∧ runOK (fnx 0 1) (List.ofFn fun i => g i.succ)) ↔ specF 0 g
        rw [sF0_1 g h, ← ih 1 (fun i => g i.succ), h1]
        exact ⟨fun hh => hh.2, fun hh => ⟨h2, hh⟩⟩
      · have h1 : fnx 1 1 = 1 := by decide
        have h2 : fok 1 1 := by decide
        show (fok 1 1 ∧ runOK (fnx 1 1) (List.ofFn fun i => g i.succ)) ↔ specF 1 g
        rw [sF1_1 g h, ← ih 1 (fun i => g i.succ), h1]
        exact ⟨fun hh => hh.2, fun hh => ⟨h2, hh⟩⟩
      · constructor
        · intro hh; exact absurd ⟨rfl, rfl⟩ hh.1
        · intro hh; exact absurd hh (sF2_1 g h)

theorem uniF_run {L : ℕ} (g : Fin L → Fin 2) :
    (∀ a b c : Fin L, a < b → b < c → ¬ (g b < g a ∧ g b < g c)) ↔ runOK 0 (List.ofFn g) := by
  rw [runF]; rfl

end finuni


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


def Mono3 (c : Col) : Prop := c 0 ≤ c 1 ∧ c 1 ≤ c 2

instance : DecidablePred Mono3 := fun c => by unfold Mono3; infer_instance

abbrev SS := (Fin 3 → Fin 3) × Fin 2

def okP (s : SS) (c : Fin 3 → Fin 2) : Prop :=
  Mono3 c ∧ (∀ i, fok (s.1 i) (c i)) ∧
    ¬ (pbk s.1 1 < s.2 ∧ pbk s.1 1 < c 0)
instance (s : SS) (c : Fin 3 → Fin 2) : Decidable (okP s c) := by unfold okP; infer_instance
def nxP (s : SS) (c : Fin 3 → Fin 2) : SS := (nxk s.1 c, pbk s.1 2)

theorem acc_iff : ∀ (l : List Col) (s : SS),
    RunAcc okP nxP s l ↔ ((∀ c ∈ l, Mono3 c) ∧
      (∀ i, runOK (s.1 i) (l.map (fun c => c i))) ∧ TC s.2 (pbk s.1) l) := by
  intro l
  induction l with
  | nil => intro s; simp [RunAcc, runOK, TC]
  | cons a l ih =>
    intro s
    simp only [RunAcc, ih, nxP, pbk_nxk, okP, List.mem_cons, forall_eq_or_imp, List.map_cons, runOK,
      forall_and, TC, nxk]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩
      exact ⟨⟨h1, h4⟩, ⟨h2, h5⟩, ⟨h3, h6⟩⟩
    · rintro ⟨⟨h1, h4⟩, ⟨h2, h5⟩, ⟨h3, h6⟩⟩
      exact ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩

def s0 : SS := (fun _ => 0, 0)
def code (s : SS) : ℕ := s.1 0 + 3 * s.1 1 + 9 * s.1 2 + 27 * s.2

theorem sol_iff {n : ℕ} (x : Fin 3 → Fin n → Fin 2) :
    Good x ↔ RunAcc okP nxP s0 (List.ofFn fun j i => x i j) := by
  rw [acc_iff]
  unfold Good
  have hmono : (∀ j, Monotone (fun i => x i j)) ↔
      ∀ c ∈ List.ofFn (fun j i => x i j), Mono3 c := by
    simp only [List.mem_ofFn', Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    exact forall_congr' (fun j => mono3 _)
  have hrow : ∀ i, Unimodal (x i) ↔ runOK (s0.1 i) (List.map (fun c => c i) (List.ofFn fun j i => x i j)) := by
    intro i
    show _ ↔ runOK 0 _
    rw [List.map_ofFn]
    exact uniF_run (x i)
  have hanti : AntidiagUnimodal x ↔ TC s0.2 (pbk s0.1) (List.ofFn fun j i => x i j) := by
    have e : pbk s0.1 = fun _ => 0 := by funext i; simp [pbk, s0]
    show _ ↔ TC 0 (pbk (fun _ => 0)) _
    have e' : pbk (fun _ : Fin 3 => (0 : Fin 3)) = fun _ => 0 := by funext i; simp [pbk]
    rw [e', tc_zero, win_idx]
    simp only [List.getElem_ofFn, List.length_ofFn]
    unfold AntidiagUnimodal
    constructor
    · intro h j hj
      exact h 2 1 0 ⟨j, by omega⟩ ⟨j + 1, by omega⟩ ⟨j + 2, by omega⟩ (by simp [Fin.lt_def]) (by simp [Fin.lt_def]) (by simp <;> omega) (by simp <;> omega)
    · intro h i₁ i₂ i₃ j₁ j₂ j₃ h1 h2 h3 h4
      obtain ⟨jv1, hj1⟩ := j₁
      obtain ⟨jv2, hj2⟩ := j₂
      obtain ⟨jv3, hj3⟩ := j₃
      have a1 := i₁.2; have a2 := i₂.2; have a3 := i₃.2
      simp only [Fin.mk_lt_mk, Fin.val_mk] at h1 h2 h3 h4
      have e1 : i₁ = 2 := Fin.ext (by simp; omega)
      have e2 : i₂ = 1 := Fin.ext (by simp; omega)
      have e3 : i₃ = 0 := Fin.ext (by simp; omega)
      have f2 : jv2 = jv1 + 1 := by omega
      have f3 : jv3 = jv1 + 2 := by omega
      subst e1 e2 e3 f2 f3
      exact h jv1 hj3
  rw [← hanti, ← hmono]
  simp only [hrow]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h3, h1, h2⟩
  · rintro ⟨h3, h1, h2⟩; exact ⟨h1, h2, h3⟩

theorem a_eq (n : ℕ) : a n = V okP nxP n s0 := by
  have h1 : a n = Nat.card {x : Fin 3 → Fin n → Fin 2 // Good x} := by
    unfold a; rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [h1, ← cnt okP nxP n s0, ← card_ofFn n (fun l => RunAcc okP nxP s0 l)]
  exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.piComm _) (fun x => by rw [sol_iff]; rfl))

def Tset (s : SS) : Prop := code s ∈ [0, 9, 12, 13, 18, 24, 26, 36, 39, 40, 41, 42, 44, 45, 51, 53]
instance (s : SS) : Decidable (Tset s) := by unfold Tset; infer_instance
theorem hT : ∀ s a, Tset s → okP s a → Tset (nxP s a) := by decide +kernel
theorem hs0 : ∀ a, okP s0 a → Tset (nxP s0 a) := by decide +kernel
def cc : ℕ → ℤ := fun j => [-1, 7, -21, 35, -35, 21, -7, 1].getD j 0
theorem h0 : ∀ s, Tset s → ∑ j ∈ Finset.range (8), cc j * (V okP nxP (0 + j) s : ℤ) = 0 := by decide +kernel
theorem hrecV (n : ℕ) : ∑ j ∈ Finset.range (8), cc j * (a (0 + n + 1 + j) : ℤ) = 0 := by
  have := rec_next okP nxP Tset hT 0 7 cc h0 s0 hs0 n
  simp only [a_eq]
  exact this
theorem hrecA (k : ℕ) : (a (0 + k + 1 + 7) : ℚ) = (1 : ℚ) * a (0 + k + 1 + 0) + (-7 : ℚ) * a (0 + k + 1 + 1) + (21 : ℚ) * a (0 + k + 1 + 2) + (-35 : ℚ) * a (0 + k + 1 + 3) + (35 : ℚ) * a (0 + k + 1 + 4) + (-21 : ℚ) * a (0 + k + 1 + 5) + (7 : ℚ) * a (0 + k + 1 + 6) := by
  have h := hrecV k
  have e0 : cc 0 = -1 := rfl
  have e1 : cc 1 = 7 := rfl
  have e2 : cc 2 = -21 := rfl
  have e3 : cc 3 = 35 := rfl
  have e4 : cc 4 = -35 := rfl
  have e5 : cc 5 = 21 := rfl
  have e6 : cc 6 = -7 := rfl
  have e7 : cc 7 = 1 := rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, e3, e4, e5, e6, e7] at h
  have h' := congrArg (Int.cast : ℤ → ℚ) h
  push_cast at h'
  linarith
theorem v0 : a 0 = 1 := by rw [a_eq]; decide +kernel
theorem v1 : a 1 = 4 := by rw [a_eq]; decide +kernel
theorem v2 : a 2 = 16 := by rw [a_eq]; decide +kernel
theorem v3 : a 3 = 49 := by rw [a_eq]; decide +kernel
theorem v4 : a 4 = 124 := by rw [a_eq]; decide +kernel
theorem v5 : a 5 = 275 := by rw [a_eq]; decide +kernel
theorem v6 : a 6 = 554 := by rw [a_eq]; decide +kernel
theorem v7 : a 7 = 1037 := by rw [a_eq]; decide +kernel
theorem v8 : a 8 = 1831 := by rw [a_eq]; decide +kernel
def Pq (x : ℚ) : ℚ := (1 : ℚ) + (53/60 : ℚ) * x^1 + (241/180 : ℚ) * x^2 + (29/48 : ℚ) * x^3 + (23/144 : ℚ) * x^4 + (1/80 : ℚ) * x^5 + (1/720 : ℚ) * x^6
theorem closed (n : ℕ) (hn : 0 ≤ n) : (a n : ℚ) = Pq (n : ℚ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 8
    · interval_cases n
      · rw [v0]; norm_num [Pq]
      · rw [v1]; norm_num [Pq]
      · rw [v2]; norm_num [Pq]
      · rw [v3]; norm_num [Pq]
      · rw [v4]; norm_num [Pq]
      · rw [v5]; norm_num [Pq]
      · rw [v6]; norm_num [Pq]
      · rw [v7]; norm_num [Pq]
    · obtain ⟨k, rfl⟩ : ∃ k, n = 0 + k + 1 + 7 := ⟨n - 8, by omega⟩
      rw [hrecA k]
      rw [ih (0 + k + 1 + 0) (by omega) (by omega)]
      rw [ih (0 + k + 1 + 1) (by omega) (by omega)]
      rw [ih (0 + k + 1 + 2) (by omega) (by omega)]
      rw [ih (0 + k + 1 + 3) (by omega) (by omega)]
      rw [ih (0 + k + 1 + 4) (by omega) (by omega)]
      rw [ih (0 + k + 1 + 5) (by omega) (by omega)]
      rw [ih (0 + k + 1 + 6) (by omega) (by omega)]
      push_cast
      simp only [Pq]
      ring
noncomputable def bq (n : ℕ) : ℚ := if n = 0 then 0 else (a n : ℚ)
theorem bq_closed (n : ℕ) (hn : 1 ≤ n) : bq n = Pq ((n : ℚ) + 0) := by
  unfold bq
  have := closed (n + 0) (by omega)
  push_cast at this
  first | (simp only [show n ≠ 0 by omega, if_false]; exact this) | exact this
theorem hb_all : ∀ n, ∑ j ∈ Finset.range (8), ([(1 : ℚ), (-7 : ℚ), (21 : ℚ), (-35 : ℚ), (35 : ℚ), (-21 : ℚ), (7 : ℚ), (-1 : ℚ)] : List ℚ).getD j 0 * (if j ≤ n then bq (n - j) else 0) = if n ≤ 7 then ([(0 : ℚ), (4 : ℚ), (-12 : ℚ), (21 : ℚ), (-23 : ℚ), (16 : ℚ), (-6 : ℚ), (1 : ℚ)] : List ℚ).getD n 0 else 0 := by
  intro n
  by_cases hn : n ≤ 7
  · interval_cases n <;> simp [Finset.sum_range_succ, bq, v0, v1, v2, v3, v4, v5, v6, v7, v8] <;> norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
    rw [if_neg (by omega)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    have t0 : bq (k + 8 - 0) = Pq ((k : ℚ) + 8) := by
      rw [bq_closed _ (by omega), show k + 8 - 0 = k + 8 by omega]; push_cast; ring_nf
    have t1 : bq (k + 8 - 1) = Pq ((k : ℚ) + 7) := by
      rw [bq_closed _ (by omega), show k + 8 - 1 = k + 7 by omega]; push_cast; ring_nf
    have t2 : bq (k + 8 - 2) = Pq ((k : ℚ) + 6) := by
      rw [bq_closed _ (by omega), show k + 8 - 2 = k + 6 by omega]; push_cast; ring_nf
    have t3 : bq (k + 8 - 3) = Pq ((k : ℚ) + 5) := by
      rw [bq_closed _ (by omega), show k + 8 - 3 = k + 5 by omega]; push_cast; ring_nf
    have t4 : bq (k + 8 - 4) = Pq ((k : ℚ) + 4) := by
      rw [bq_closed _ (by omega), show k + 8 - 4 = k + 4 by omega]; push_cast; ring_nf
    have t5 : bq (k + 8 - 5) = Pq ((k : ℚ) + 3) := by
      rw [bq_closed _ (by omega), show k + 8 - 5 = k + 3 by omega]; push_cast; ring_nf
    have t6 : bq (k + 8 - 6) = Pq ((k : ℚ) + 2) := by
      rw [bq_closed _ (by omega), show k + 8 - 6 = k + 2 by omega]; push_cast; ring_nf
    have t7 : bq (k + 8 - 7) = Pq ((k : ℚ) + 1) := by
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


theorem gf_main : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - PowerSeries.X) ^ 7 =
    PowerSeries.X * (4 - 12 * PowerSeries.X + 21 * PowerSeries.X ^ 2 - 23 * PowerSeries.X ^ 3 + 16 * PowerSeries.X ^ 4 - 6 * PowerSeries.X ^ 5 + PowerSeries.X ^ 6) := by
  have h : PowerSeries.mk bq = (PowerSeries.X * (4 - 12 * PowerSeries.X + 21 * PowerSeries.X ^ 2 - 23 * PowerSeries.X ^ 3 + 16 * PowerSeries.X ^ 4 - 6 * PowerSeries.X ^ 5 + PowerSeries.X ^ 6)) * ((1 - PowerSeries.X) ^ 7)⁻¹ := by
    apply gf_gen bq 7 7 (fun j => [(1 : ℚ), -7, 21, -35, 35, -21, 7, -1].getD j 0) (fun j => [(0 : ℚ), 4, -12, 21, -23, 16, -6, 1].getD j 0)
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

end OMA.S_oeis_a224147

theorem OMA.solution : type_of% @OMA.S_oeis_a224147.main := by
  refine ⟨?_, OMA.S_oeis_a224147.gf_main, ?_⟩
  · intro n hn
    rw [OMA.S_oeis_a224147.closed n (by omega)]
    simp only [OMA.S_oeis_a224147.Pq]
    ring
  · intro n hn
    have := OMA.S_oeis_a224147.recS n hn
    linarith

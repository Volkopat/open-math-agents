import OMAStatements.S_oeis_a223670
import Mathlib

namespace OMA.S_oeis_a223670
/-
UNIMODAL / WINDOW KIT (Hardin-style counts). Paste after `import OMAStatements.S_<id>`, `import Mathlib`, `namespace OMA.S_<id>`.
1. Deterministic automaton: RunAcc ok nx s l; `cnt` : Nat.card {l // l.length = n ∧ RunAcc ok nx s l} = V ok nx n s;
   `card_ofFn` turns {x : Fin n → A // P (ofFn x)} into list form (Equiv.piComm for Fin r → Fin n → _ arrays).
2. Unimodal 0/1 line = 3-state flag (fok/fnx/runOK: 0 no 1 yet, 1 in 1-block, 2 zeros after): `uni_run` (take/drop form),
   `uniF_run` (Fin no-valley form); state = one flag per line, row bit = (flag = 1) (`pbk`, `nxk`, `pbk_nxk`).
3. Local windows (block B, triple T, row predicate U): okW/nxW/TsetW + `good_iff`; if T is trivial use okC/nxC + `good_iff_chain`.
4. Generator hardin/unimodal_gen/gen_unimodal.py: tail(model, deg, gf=.., win=|chain=|split=) emits Tset, cc, h0 (decide +kernel),
   hrecA, values, closed form Pq, hb_all (g.f.), recS; f*/sol*.lean = g.f./main glue; p*.lean = per-problem bridge (examples).
5. Cost: h0/values dominate (kernel); split=True = one theorem per state; keep states small (peak RSS grows with every decide).
-/
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


section chain2

variable {A : Type} (U : A → Prop) (B : A → A → Prop)

def okC (s : Option A) (c : A) : Prop := U c ∧ (match s with | none => True | some b => B b c)
def nxC (_ : Option A) (c : A) : Option A := some c

instance okCDec [DecidablePred U] [∀ a b, Decidable (B a b)] (s : Option A) (c : A) :
    Decidable (okC U B s c) := by
  unfold okC
  cases s <;> dsimp only <;> infer_instance

def TsetC (s : Option A) : Prop :=
  match s with
  | none => False
  | some b => U b

instance tsetCDec [DecidablePred U] (s : Option A) : Decidable (TsetC U s) := by
  unfold TsetC
  cases s <;> dsimp only <;> infer_instance

theorem hT_C (s : Option A) (c : A) (_ : TsetC U s) (h : okC U B s c) : TsetC U (nxC s c) := h.1

theorem hs0_C (c : A) (h : okC U B none c) : TsetC U (nxC none c) := h.1

theorem acc_C : ∀ (l : List A) (b : A), RunAcc (okC U B) nxC (some b) l ↔
    ((∀ c ∈ l, U c) ∧ (b :: l).IsChain B) := by
  intro l
  induction l with
  | nil => intro b; simp [RunAcc]
  | cons c l ih =>
    intro b
    rw [RunAcc]
    show (okC U B (some b) c ∧ RunAcc (okC U B) nxC (some c) l) ↔ _
    rw [ih c]
    simp only [okC, List.mem_cons, forall_eq_or_imp, List.isChain_cons_cons]
    constructor
    · rintro ⟨⟨h1, h2⟩, h4, h5⟩
      exact ⟨⟨h1, h4⟩, h2, h5⟩
    · rintro ⟨⟨h1, h4⟩, h2, h5⟩
      exact ⟨⟨h1, h2⟩, h4, h5⟩

theorem acc_C0 : ∀ (l : List A), RunAcc (okC U B) nxC none l ↔
    ((∀ c ∈ l, U c) ∧ l.IsChain B) := by
  intro l
  cases l with
  | nil => simp [RunAcc]
  | cons c l =>
    rw [RunAcc]
    show (okC U B none c ∧ RunAcc (okC U B) nxC (some c) l) ↔ _
    rw [acc_C U B l c]
    simp only [okC, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨⟨h1, _⟩, h4, h5⟩
      exact ⟨⟨h1, h4⟩, h5⟩
    · rintro ⟨⟨h1, h4⟩, h5⟩
      exact ⟨⟨h1, trivial⟩, h4, h5⟩

theorem good_iff_chain {n : ℕ} (x : Fin n → A) :
    ((∀ i, U (x i)) ∧ (∀ i j : Fin n, j.val = i.val + 1 → B (x i) (x j))) ↔
    RunAcc (okC U B) nxC none (List.ofFn x) := by
  rw [acc_C0, List.isChain_ofFn]
  have h1 : (∀ c ∈ List.ofFn x, U c) ↔ ∀ i, U (x i) := by
    simp [List.mem_ofFn']
  rw [h1]
  refine and_congr Iff.rfl ?_
  constructor
  · intro h i hi
    exact h ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl
  · intro h i j hij
    obtain ⟨iv, hiv⟩ := i
    obtain ⟨jv, hjv⟩ := j
    have e : jv = iv + 1 := hij
    subst e
    exact h iv hjv

end chain2



abbrev SS := (Fin 3 → Fin 3) × Fin 2 × Fin 2

def okP (s : SS) (c : Fin 3 → Fin 2) : Prop :=
  (∀ i, fok (s.1 i) (c i)) ∧ ¬ (pbk s.1 1 < s.2.2 ∧ pbk s.1 1 < c 0) ∧
    ¬ (pbk s.1 1 < s.2.1 ∧ pbk s.1 1 < c 2)
instance (s : SS) (c : Fin 3 → Fin 2) : Decidable (okP s c) := by unfold okP; infer_instance
def nxP (s : SS) (c : Fin 3 → Fin 2) : SS := (nxk s.1 c, pbk s.1 0, pbk s.1 2)

def T3 (a b c : Col) : Prop := ¬ (b 1 < a 2 ∧ b 1 < c 0) ∧ ¬ (b 1 < a 0 ∧ b 1 < c 2)

def TD : Fin 2 × Fin 2 → Col → List Col → Prop
  | _, _, [] => True
  | u, v, w :: l => ¬ (v 1 < u.2 ∧ v 1 < w 0) ∧ ¬ (v 1 < u.1 ∧ v 1 < w 2) ∧ TD (v 0, v 2) w l

def mkU2 (u : Fin 2 × Fin 2) : Col := fun i => if i = 0 then u.1 else if i = 2 then u.2 else 0

theorem tri_congr (a a' b : Col) (l : List Col) (h0 : a 0 = a' 0) (h2 : a 2 = a' 2) :
    Tri T3 (a :: b :: l) ↔ Tri T3 (a' :: b :: l) := by
  cases l with
  | nil => simp [Tri]
  | cons c t => simp only [Tri, T3, h0, h2]

theorem td_tri : ∀ (l : List Col) (u : Fin 2 × Fin 2) (v : Col),
    TD u v l ↔ Tri T3 (mkU2 u :: v :: l) := by
  intro l
  induction l with
  | nil => intro u v; simp [TD, Tri]
  | cons w l ih =>
    intro u v
    rw [TD, ih]
    show _ ↔ T3 (mkU2 u) v w ∧ Tri T3 (v :: w :: l)
    rw [tri_congr (mkU2 (v 0, v 2)) v w l (by simp [mkU2]) (by simp [mkU2])]
    simp [T3, mkU2, and_assoc]

theorem td_zero (l : List Col) : TD (0, 0) (fun _ => 0) l ↔ Tri T3 l := by
  have e : (fun _ : Fin 3 => (0 : Fin 2)) = mkU2 (0, 0) := by
    funext i; fin_cases i <;> simp [mkU2]
  rw [e, td_tri]
  cases l with
  | nil => simp [Tri]
  | cons b t =>
    cases t with
    | nil => simp [Tri, T3, mkU2]
    | cons c r =>
      simp [Tri, T3, mkU2]

theorem acc_iff : ∀ (l : List Col) (s : SS),
    RunAcc okP nxP s l ↔ ((∀ i, runOK (s.1 i) (l.map (fun c => c i))) ∧ TD s.2 (pbk s.1) l) := by
  intro l
  induction l with
  | nil => intro s; simp [RunAcc, runOK, TD]
  | cons a l ih =>
    intro s
    simp only [RunAcc, ih, nxP, pbk_nxk, okP, List.map_cons, runOK, forall_and, TD, nxk]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4, h5⟩
      exact ⟨⟨h1, h4⟩, h2, h3, h5⟩
    · rintro ⟨⟨h1, h4⟩, h2, h3, h5⟩
      exact ⟨⟨h1, h2, h3⟩, h4, h5⟩

def s0 : SS := (fun _ => 0, 0, 0)
def code (s : SS) : ℕ := s.1 0 + 3 * s.1 1 + 9 * s.1 2 + 27 * s.2.1 + 54 * s.2.2

theorem anti_iff {n : ℕ} (x : Fin 3 → Fin n → Fin 2) : AntidiagsUnimodal x ↔
    ∀ (j : ℕ) (h : j + 2 < n), ¬ (x 1 ⟨j + 1, by omega⟩ < x 2 ⟨j, by omega⟩ ∧
      x 1 ⟨j + 1, by omega⟩ < x 0 ⟨j + 2, h⟩) := by
  constructor
  · intro h j hj hh
    exact h 0 1 2 ⟨j + 2, hj⟩ ⟨j + 1, by omega⟩ ⟨j, by omega⟩ (by simp [Fin.lt_def]) (by simp [Fin.lt_def])
      (by simp <;> omega) (by simp <;> omega) ⟨hh.2, hh.1⟩
  · intro h i₁ i₂ i₃ j₁ j₂ j₃ h1 h2 h3 h4 hh
    rw [Fin.lt_def] at h1 h2
    have a3 := i₃.2
    have e1 : i₁ = 0 := Fin.ext (by simp; omega)
    have e2 : i₂ = 1 := Fin.ext (by simp; omega)
    have e3 : i₃ = 2 := Fin.ext (by simp; omega)
    subst e1 e2 e3
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at h3 h4
    have f2 : j₂ = ⟨j₃.1 + 1, by omega⟩ := Fin.ext (by simp; omega)
    have f1 : j₁ = ⟨j₃.1 + 2, by omega⟩ := Fin.ext (by simp; omega)
    have c1 : x 1 j₂ = x 1 ⟨j₃.1 + 1, by omega⟩ := congrArg (x 1) f2
    have c2 : x 0 j₁ = x 0 ⟨j₃.1 + 2, by omega⟩ := congrArg (x 0) f1
    rw [c1, c2] at hh
    exact h j₃.1 (by omega) ⟨hh.2, hh.1⟩

theorem diag_iff {n : ℕ} (x : Fin 3 → Fin n → Fin 2) : DiagsUnimodal x ↔
    ∀ (j : ℕ) (h : j + 2 < n), ¬ (x 1 ⟨j + 1, by omega⟩ < x 0 ⟨j, by omega⟩ ∧
      x 1 ⟨j + 1, by omega⟩ < x 2 ⟨j + 2, h⟩) := by
  constructor
  · intro h j hj hh
    exact h 0 1 2 ⟨j, by omega⟩ ⟨j + 1, by omega⟩ ⟨j + 2, hj⟩ (by simp [Fin.lt_def]) (by simp [Fin.lt_def])
      (by simp; omega) (by simp; omega) hh
  · intro h i₁ i₂ i₃ j₁ j₂ j₃ h1 h2 h3 h4 hh
    rw [Fin.lt_def] at h1 h2
    have a3 := i₃.2
    have e1 : i₁ = 0 := Fin.ext (by simp; omega)
    have e2 : i₂ = 1 := Fin.ext (by simp; omega)
    have e3 : i₃ = 2 := Fin.ext (by simp; omega)
    subst e1 e2 e3
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at h3 h4
    have f2 : j₂ = ⟨j₁.1 + 1, by omega⟩ := Fin.ext (by simp; omega)
    have f3 : j₃ = ⟨j₁.1 + 2, by omega⟩ := Fin.ext (by simp; omega)
    have c1 : x 1 j₂ = x 1 ⟨j₁.1 + 1, by omega⟩ := congrArg (x 1) f2
    have c2 : x 2 j₃ = x 2 ⟨j₁.1 + 2, by omega⟩ := congrArg (x 2) f3
    rw [c1, c2] at hh
    have c0 : x 0 j₁ = x 0 ⟨j₁.1, by omega⟩ := rfl
    rw [c0] at hh
    exact h j₁.1 (by omega) hh

theorem sol_iff {n : ℕ} (x : Fin 3 → Fin n → Fin 2) :
    good x ↔ RunAcc okP nxP s0 (List.ofFn fun j i => x i j) := by
  rw [acc_iff]
  unfold good
  have hrow : RowsUnimodal x ↔
      ∀ i, runOK (s0.1 i) (List.map (fun c => c i) (List.ofFn fun j i => x i j)) := by
    unfold RowsUnimodal
    refine forall_congr' (fun i => ?_)
    show _ ↔ runOK 0 _
    rw [List.map_ofFn]
    exact uniF_run (x i)
  have htri : (DiagsUnimodal x ∧ AntidiagsUnimodal x) ↔
      TD s0.2 (pbk s0.1) (List.ofFn fun j i => x i j) := by
    have e' : pbk (fun _ : Fin 3 => (0 : Fin 3)) = fun _ => 0 := by funext i; simp [pbk]
    show _ ↔ TD (0, 0) (pbk (fun _ => 0)) _
    rw [e', td_zero, tri_idx]
    simp only [List.getElem_ofFn, List.length_ofFn]
    rw [diag_iff, anti_iff]
    constructor
    · rintro ⟨hd, ha⟩ j hj
      exact ⟨ha j hj, hd j hj⟩
    · intro h
      exact ⟨fun j hj => (h j hj).2, fun j hj => (h j hj).1⟩
  rw [← hrow, ← htri]

theorem a_eq (n : ℕ) : a n = V okP nxP n s0 := by
  have h1 : a n = Nat.card {x : Fin 3 → Fin n → Fin 2 // good x} := by
    unfold a; rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [h1, ← cnt okP nxP n s0, ← card_ofFn n (fun l => RunAcc okP nxP s0 l)]
  exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.piComm _) (fun x => by rw [sol_iff]; rfl))

def Tset (s : SS) : Prop := code s ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 28, 29, 31, 32, 34, 35, 37, 38, 40, 41, 43, 44, 46, 47, 49, 50, 52, 53, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 91, 92, 94, 95, 97, 98, 100, 101, 103, 104, 106, 107]
instance (s : SS) : Decidable (Tset s) := by unfold Tset; infer_instance
theorem hT : ∀ s a, Tset s → okP s a → Tset (nxP s a) := by decide +kernel
theorem hs0 : ∀ a, okP s0 a → Tset (nxP s0 a) := by decide +kernel
def LL : List (List ℕ) := [[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [8, 8, 4, 8, 8, 4, 4, 4, 2, 8, 8, 4, 8, 8, 4, 4, 4, 2, 4, 4, 2, 4, 4, 2, 2, 2, 1, 4, 4, 2, 8, 8, 4, 2, 2, 1, 4, 4, 2, 8, 8, 4, 2, 2, 1, 4, 4, 2, 4, 4, 2, 2, 2, 1, 4, 4, 4, 8, 8, 4, 2, 2, 2, 4, 4, 4, 8, 8, 4, 2, 2, 2, 2, 2, 2, 4, 4, 2, 1, 1, 1, 2, 2, 2, 8, 8, 4, 1, 1, 1, 2, 2, 2, 8, 8, 4, 1, 1, 1, 2, 2, 2, 4, 4, 2, 1, 1, 1],
  [64, 36, 16, 48, 30, 12, 16, 6, 4, 36, 26, 12, 30, 22, 9, 6, 4, 3, 16, 12, 4, 12, 9, 3, 4, 3, 1, 32, 18, 8, 48, 30, 12, 8, 3, 2, 12, 10, 4, 30, 22, 9, 2, 2, 1, 16, 12, 4, 12, 9, 3, 4, 3, 1, 32, 12, 16, 48, 30, 12, 8, 2, 4, 18, 10, 12, 30, 22, 9, 3, 2, 3, 8, 4, 4, 12, 9, 3, 2, 1, 1, 16, 6, 8, 48, 30, 12, 4, 1, 2, 6, 4, 4, 30, 22, 9, 1, 1, 1, 8, 4, 4, 12, 9, 3, 2, 1, 1],
  [292, 113, 49, 162, 81, 28, 32, 8, 7, 113, 59, 28, 81, 47, 16, 8, 4, 4, 49, 28, 7, 28, 16, 4, 7, 4, 1, 178, 68, 28, 162, 81, 28, 22, 5, 4, 33, 20, 7, 81, 47, 16, 3, 2, 1, 49, 28, 7, 28, 16, 4, 7, 4, 1, 178, 33, 49, 162, 81, 28, 22, 3, 7, 68, 20, 28, 81, 47, 16, 5, 2, 4, 28, 7, 7, 28, 16, 4, 4, 1, 1, 112, 20, 28, 162, 81, 28, 16, 2, 4, 20, 7, 7, 81, 47, 16, 2, 1, 1, 28, 7, 7, 28, 16, 4, 4, 1, 1],
  [948, 295, 121, 423, 184, 55, 52, 12, 11, 295, 111, 55, 184, 87, 25, 12, 4, 5, 121, 55, 11, 55, 25, 5, 11, 5, 1, 648, 205, 77, 423, 184, 55, 40, 9, 7, 79, 34, 11, 184, 87, 25, 5, 2, 1, 121, 55, 11, 55, 25, 5, 11, 5, 1, 648, 79, 121, 423, 184, 55, 40, 5, 11, 205, 34, 55, 184, 87, 25, 9, 2, 5, 77, 11, 11, 55, 25, 5, 7, 1, 1, 454, 56, 77, 423, 184, 55, 32, 4, 7, 56, 11, 11, 184, 87, 25, 4, 1, 1, 77, 11, 11, 55, 25, 5, 7, 1, 1],
  [2527, 678, 256, 958, 370, 96, 80, 19, 16, 678, 186, 96, 370, 146, 36, 19, 4, 6, 256, 96, 16, 96, 36, 6, 16, 6, 1, 1850, 521, 176, 958, 370, 96, 64, 16, 11, 168, 52, 16, 370, 146, 36, 8, 2, 1, 256, 96, 16, 96, 36, 6, 16, 6, 1, 1850, 168, 256, 958, 370, 96, 64, 8, 16, 521, 52, 96, 370, 146, 36, 16, 2, 6, 176, 16, 16, 96, 36, 6, 11, 1, 1, 1371, 132, 176, 958, 370, 96, 52, 7, 11, 132, 16, 16, 370, 146, 36, 7, 1, 1, 176, 16, 16, 96, 36, 6, 11, 1, 1],
  [5913, 1413, 484, 1966, 678, 154, 122, 30, 22, 1413, 288, 154, 678, 228, 49, 30, 4, 7, 484, 154, 22, 154, 49, 7, 22, 7, 1, 4533, 1163, 352, 1966, 678, 154, 99, 27, 16, 324, 74, 22, 678, 228, 49, 12, 2, 1, 484, 154, 22, 154, 49, 7, 22, 7, 1, 4533, 324, 484, 1966, 678, 154, 99, 12, 22, 1163, 74, 154, 678, 228, 49, 27, 2, 7, 352, 22, 22, 154, 49, 7, 16, 1, 1, 3485, 272, 352, 1966, 678, 154, 80, 11, 16, 272, 22, 22, 678, 228, 49, 11, 1, 1, 352, 22, 22, 154, 49, 7, 16, 1, 1],
  [12577, 2720, 841, 3736, 1155, 232, 186, 46, 29, 2720, 421, 232, 1155, 337, 64, 46, 4, 8, 841, 232, 29, 232, 64, 8, 29, 8, 1, 9970, 2347, 638, 3736, 1155, 232, 152, 43, 22, 577, 100, 29, 1155, 337, 64, 17, 2, 1, 841, 232, 29, 232, 64, 8, 29, 8, 1, 9970, 577, 841, 3736, 1155, 232, 152, 17, 29, 2347, 100, 232, 1155, 337, 64, 43, 2, 8, 638, 29, 29, 232, 64, 8, 22, 1, 1, 7879, 506, 638, 3736, 1155, 232, 122, 16, 22, 506, 29, 29, 1155, 337, 64, 16, 1, 1, 638, 29, 29, 232, 64, 8, 22, 1, 1],
  [24821, 4902, 1369, 6665, 1856, 333, 282, 68, 37, 4902, 589, 333, 1856, 477, 81, 68, 4, 9, 1369, 333, 37, 333, 81, 9, 37, 9, 1, 20188, 4372, 1073, 6665, 1856, 333, 232, 65, 29, 963, 130, 37, 1856, 477, 81, 23, 2, 1, 1369, 333, 37, 333, 81, 9, 37, 9, 1, 20188, 963, 1369, 6665, 1856, 333, 232, 23, 37, 4372, 130, 333, 1856, 477, 81, 65, 2, 9, 1073, 37, 37, 333, 81, 9, 29, 1, 1, 16313, 870, 1073, 6665, 1856, 333, 186, 22, 29, 870, 37, 37, 1856, 477, 81, 22, 1, 1, 1073, 37, 37, 333, 81, 9, 29, 1, 1],
  [46068, 8359, 2116, 11276, 2844, 460, 422, 97, 46, 8359, 796, 460, 2844, 652, 100, 97, 4, 10, 2116, 460, 46, 460, 100, 10, 46, 10, 1, 38244, 7634, 1702, 11276, 2844, 460, 350, 94, 37, 1524, 164, 46, 2844, 652, 100, 30, 2, 1, 2116, 460, 46, 460, 100, 10, 46, 10, 1, 38244, 1524, 2116, 11276, 2844, 460, 350, 30, 46, 7634, 164, 460, 2844, 652, 100, 94, 2, 10, 1702, 46, 46, 460, 100, 10, 37, 1, 1, 31486, 1406, 1702, 11276, 2844, 460, 282, 29, 37, 1406, 46, 46, 2844, 652, 100, 29, 1, 1, 1702, 46, 46, 460, 100, 10, 37, 1, 1],
  [81198, 13602, 3136, 18236, 4190, 616, 620, 134, 56, 13602, 1046, 616, 4190, 866, 121, 134, 4, 11, 3136, 616, 56, 616, 121, 11, 56, 11, 1, 68547, 12640, 2576, 18236, 4190, 616, 519, 131, 46, 2308, 202, 56, 4190, 866, 121, 38, 2, 1, 3136, 616, 56, 616, 121, 11, 56, 11, 1, 68547, 2308, 3136, 18236, 4190, 616, 519, 38, 56, 12640, 202, 616, 4190, 866, 121, 131, 2, 11, 2576, 56, 56, 616, 121, 11, 46, 1, 1, 57344, 2162, 2576, 18236, 4190, 616, 422, 37, 46, 2162, 56, 56, 4190, 866, 121, 37, 1, 1, 2576, 56, 56, 616, 121, 11, 46, 1, 1],
  [136930, 21267, 4489, 28374, 5973, 804, 892, 180, 67, 21267, 1343, 804, 5973, 1123, 144, 180, 4, 12, 4489, 804, 67, 804, 144, 12, 67, 12, 1, 117226, 20022, 3752, 28374, 5973, 804, 754, 177, 56, 3369, 244, 67, 5973, 1123, 144, 47, 2, 1, 4489, 804, 67, 804, 144, 12, 67, 12, 1, 117226, 3369, 4489, 28374, 5973, 804, 754, 47, 67, 20022, 244, 804, 5973, 1123, 144, 177, 2, 12, 3752, 67, 67, 804, 144, 12, 56, 1, 1, 99434, 3192, 3752, 28374, 5973, 804, 620, 46, 56, 3192, 67, 67, 5973, 1123, 144, 46, 1, 1, 3752, 67, 67, 804, 144, 12, 56, 1, 1],
  [222250, 32129, 6241, 42699, 8280, 1027, 1256, 236, 79, 32129, 1691, 1027, 8280, 1427, 169, 236, 4, 13, 6241, 1027, 79, 1027, 169, 13, 79, 13, 1, 192544, 30551, 5293, 42699, 8280, 1027, 1072, 233, 67, 4767, 290, 79, 8280, 1427, 169, 57, 2, 1, 6241, 1027, 79, 1027, 169, 13, 79, 13, 1, 192544, 4767, 6241, 42699, 8280, 1027, 1072, 57, 79, 30551, 290, 1027, 8280, 1427, 169, 233, 2, 13, 5293, 79, 79, 1027, 169, 13, 67, 1, 1, 165304, 4556, 5293, 42699, 8280, 1027, 892, 56, 67, 4556, 79, 79, 8280, 1427, 169, 56, 1, 1, 5293, 79, 79, 1027, 169, 13, 67, 1, 1],
  [348885, 47116, 8464, 62418, 11206, 1288, 1732, 303, 92, 47116, 2094, 1288, 11206, 1782, 196, 303, 4, 14, 8464, 1288, 92, 1288, 196, 14, 92, 14, 1, 305358, 45151, 7268, 62418, 11206, 1288, 1492, 300, 79, 6568, 340, 92, 11206, 1782, 196, 68, 2, 1, 8464, 1288, 92, 1288, 196, 14, 92, 14, 1, 305358, 6568, 8464, 62418, 11206, 1288, 1492, 68, 92, 45151, 340, 1288, 11206, 1782, 196, 300, 2, 14, 7268, 92, 92, 1288, 196, 14, 79, 1, 1, 264949, 6320, 7268, 62418, 11206, 1288, 1256, 67, 79, 6320, 92, 92, 11206, 1782, 196, 67, 1, 1, 7268, 92, 92, 1288, 196, 14, 79, 1, 1]]
def Lit (n : ℕ) (s : SS) : ℕ := (LL.getD n []).getD (code s) 0
theorem hL0 : ∀ s : SS, Lit 0 s = 1 := by decide +kernel
theorem hLs : ∀ n, n < 13 → ∀ s : SS, ∑ a, (if okP s a then Lit n (nxP s a) else 0) = Lit (n + 1) s := by decide +kernel
theorem hVL : ∀ n, n ≤ 13 → ∀ s : SS, V okP nxP n s = Lit n s := by
  intro n
  induction n with
  | zero => intro _ s; rw [hL0]; rfl
  | succ n ih =>
    intro h s
    rw [← hLs n (by omega) s]
    show (∑ a, if okP s a then V okP nxP n (nxP s a) else 0) = _
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [ih (by omega)]
def cc : ℕ → ℤ := fun j => [0, 0, -1, 7, -21, 35, -35, 21, -7, 1].getD j 0
theorem h0L : ∀ s, Tset s → ∑ j ∈ Finset.range (10), cc j * (Lit (0 + j) s : ℤ) = 0 := by decide +kernel
theorem h0 : ∀ s, Tset s → ∑ j ∈ Finset.range (10), cc j * (V okP nxP (0 + j) s : ℤ) = 0 := by
  intro s hs
  rw [← h0L s hs]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [hVL (0 + j) (by simp at hj; omega) s]
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
theorem v0 : a 0 = 1 := by rw [a_eq, hVL 0 (by norm_num)]; decide +kernel
theorem v1 : a 1 = 8 := by rw [a_eq, hVL 1 (by norm_num)]; decide +kernel
theorem v2 : a 2 = 64 := by rw [a_eq, hVL 2 (by norm_num)]; decide +kernel
theorem v3 : a 3 = 292 := by rw [a_eq, hVL 3 (by norm_num)]; decide +kernel
theorem v4 : a 4 = 948 := by rw [a_eq, hVL 4 (by norm_num)]; decide +kernel
theorem v5 : a 5 = 2527 := by rw [a_eq, hVL 5 (by norm_num)]; decide +kernel
theorem v6 : a 6 = 5913 := by rw [a_eq, hVL 6 (by norm_num)]; decide +kernel
theorem v7 : a 7 = 12577 := by rw [a_eq, hVL 7 (by norm_num)]; decide +kernel
theorem v8 : a 8 = 24821 := by rw [a_eq, hVL 8 (by norm_num)]; decide +kernel
theorem v9 : a 9 = 46068 := by rw [a_eq, hVL 9 (by norm_num)]; decide +kernel
theorem v10 : a 10 = 81198 := by rw [a_eq, hVL 10 (by norm_num)]; decide +kernel
def Pq (x : ℚ) : ℚ := (-9 : ℚ) + (997/60 : ℚ) * x^1 + (-3103/360 : ℚ) * x^2 + (119/24 : ℚ) * x^3 + (37/18 : ℚ) * x^4 + (-3/40 : ℚ) * x^5 + (23/360 : ℚ) * x^6
theorem closed (n : ℕ) (hn : 2 ≤ n) : (a n : ℚ) = Pq (n : ℚ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 10
    · interval_cases n
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
noncomputable def bq (n : ℕ) : ℚ := if n = 0 then 0 else (a n : ℚ)
theorem bq_closed (n : ℕ) (hn : 2 ≤ n) : bq n = Pq ((n : ℚ) + 0) := by
  unfold bq
  have := closed (n + 0) (by omega)
  push_cast at this
  first | (simp only [show n ≠ 0 by omega, if_false]; exact this) | exact this
theorem hb_all : ∀ n, ∑ j ∈ Finset.range (8), ([(1 : ℚ), (-7 : ℚ), (21 : ℚ), (-35 : ℚ), (35 : ℚ), (-21 : ℚ), (7 : ℚ), (-1 : ℚ)] : List ℚ).getD j 0 * (if j ≤ n then bq (n - j) else 0) = if n ≤ 8 then ([(0 : ℚ), (8 : ℚ), (8 : ℚ), (12 : ℚ), (-32 : ℚ), (63 : ℚ), (-16 : ℚ), (5 : ℚ), (-2 : ℚ)] : List ℚ).getD n 0 else 0 := by
  intro n
  by_cases hn : n ≤ 8
  · interval_cases n <;> simp [Finset.sum_range_succ, bq, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] <;> norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
    rw [if_neg (by omega)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    have t0 : bq (k + 9 - 0) = Pq ((k : ℚ) + 9) := by
      rw [bq_closed _ (by omega), show k + 9 - 0 = k + 9 by omega]; push_cast; ring_nf
    have t1 : bq (k + 9 - 1) = Pq ((k : ℚ) + 8) := by
      rw [bq_closed _ (by omega), show k + 9 - 1 = k + 8 by omega]; push_cast; ring_nf
    have t2 : bq (k + 9 - 2) = Pq ((k : ℚ) + 7) := by
      rw [bq_closed _ (by omega), show k + 9 - 2 = k + 7 by omega]; push_cast; ring_nf
    have t3 : bq (k + 9 - 3) = Pq ((k : ℚ) + 6) := by
      rw [bq_closed _ (by omega), show k + 9 - 3 = k + 6 by omega]; push_cast; ring_nf
    have t4 : bq (k + 9 - 4) = Pq ((k : ℚ) + 5) := by
      rw [bq_closed _ (by omega), show k + 9 - 4 = k + 5 by omega]; push_cast; ring_nf
    have t5 : bq (k + 9 - 5) = Pq ((k : ℚ) + 4) := by
      rw [bq_closed _ (by omega), show k + 9 - 5 = k + 4 by omega]; push_cast; ring_nf
    have t6 : bq (k + 9 - 6) = Pq ((k : ℚ) + 3) := by
      rw [bq_closed _ (by omega), show k + 9 - 6 = k + 3 by omega]; push_cast; ring_nf
    have t7 : bq (k + 9 - 7) = Pq ((k : ℚ) + 2) := by
      rw [bq_closed _ (by omega), show k + 9 - 7 = k + 2 by omega]; push_cast; ring_nf
    rw [if_pos (show 0 ≤ k + 9 by omega), t0, if_pos (show 1 ≤ k + 9 by omega), t1, if_pos (show 2 ≤ k + 9 by omega), t2, if_pos (show 3 ≤ k + 9 by omega), t3, if_pos (show 4 ≤ k + 9 by omega), t4, if_pos (show 5 ≤ k + 9 by omega), t5, if_pos (show 6 ≤ k + 9 by omega), t6, if_pos (show 7 ≤ k + 9 by omega), t7]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Pq]
    ring
theorem recS (n : ℕ) (hn : 8 < n) : (a n : ℤ) = (7 : ℤ) * (a (n - 1) : ℤ) + (-21 : ℤ) * (a (n - 2) : ℤ) + (35 : ℤ) * (a (n - 3) : ℤ) + (-35 : ℤ) * (a (n - 4) : ℤ) + (21 : ℤ) * (a (n - 5) : ℤ) + (-7 : ℤ) * (a (n - 6) : ℤ) + (1 : ℤ) * (a (n - 7) : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
  have h0 := closed (k + 9) (by omega)
  have e1 : k + 9 - 1 = k + 8 := by omega
  have h1 := closed (k + 8) (by omega)
  have e2 : k + 9 - 2 = k + 7 := by omega
  have h2 := closed (k + 7) (by omega)
  have e3 : k + 9 - 3 = k + 6 := by omega
  have h3 := closed (k + 6) (by omega)
  have e4 : k + 9 - 4 = k + 5 := by omega
  have h4 := closed (k + 5) (by omega)
  have e5 : k + 9 - 5 = k + 4 := by omega
  have h5 := closed (k + 4) (by omega)
  have e6 : k + 9 - 6 = k + 3 := by omega
  have h6 := closed (k + 3) (by omega)
  have e7 : k + 9 - 7 = k + 2 := by omega
  have h7 := closed (k + 2) (by omega)
  rw [e1, e2, e3, e4, e5, e6, e7]
  have key : (a (k + 9) : ℚ) = (7 : ℚ) * (a (k + 8) : ℚ) + (-21 : ℚ) * (a (k + 7) : ℚ) + (35 : ℚ) * (a (k + 6) : ℚ) + (-35 : ℚ) * (a (k + 5) : ℚ) + (21 : ℚ) * (a (k + 4) : ℚ) + (-7 : ℚ) * (a (k + 3) : ℚ) + (1 : ℚ) * (a (k + 2) : ℚ) := by
    rw [h0, h1, h2, h3, h4, h5, h6, h7]
    simp only [Pq]
    push_cast
    ring
  exact_mod_cast key


theorem gf_main : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - PowerSeries.X) ^ 7 =
    PowerSeries.X * (8 + 8 * PowerSeries.X + 12 * PowerSeries.X ^ 2 - 32 * PowerSeries.X ^ 3 + 63 * PowerSeries.X ^ 4 - 16 * PowerSeries.X ^ 5 + 5 * PowerSeries.X ^ 6 - 2 * PowerSeries.X ^ 7) := by
  have h : PowerSeries.mk bq = (PowerSeries.X * (8 + 8 * PowerSeries.X + 12 * PowerSeries.X ^ 2 - 32 * PowerSeries.X ^ 3 + 63 * PowerSeries.X ^ 4 - 16 * PowerSeries.X ^ 5 + 5 * PowerSeries.X ^ 6 - 2 * PowerSeries.X ^ 7)) * ((1 - PowerSeries.X) ^ 7)⁻¹ := by
    apply gf_gen bq 7 8 (fun j => [(1 : ℚ), -7, 21, -35, 35, -21, 7, -1].getD j 0) (fun j => [(0 : ℚ), 8, 8, 12, -32, 63, -16, 5, -2].getD j 0)
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

end OMA.S_oeis_a223670

theorem OMA.solution : type_of% @OMA.S_oeis_a223670.main := by
  refine ⟨OMA.S_oeis_a223670.gf_main, ?_⟩
  intro n hn
  have := OMA.S_oeis_a223670.recS n hn
  linarith

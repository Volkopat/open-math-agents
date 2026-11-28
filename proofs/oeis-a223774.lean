import OMAStatements.S_oeis_a223774
import Mathlib

namespace OMA.S_oeis_a223774
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



def bit (f : Fin 3) : ℕ := if f = 1 then 1 else 0

def okP (s : Fin 5 → Fin 3) (r : Fin 5 → Fin 2) : Prop :=
  runOK 0 (List.ofFn r) ∧ (∀ j, fok (s j) (r j)) ∧ (∀ j : Fin 4, bit (s j.succ) ≤ (r j.castSucc : ℕ))
instance (s : Fin 5 → Fin 3) (r : Fin 5 → Fin 2) : Decidable (okP s r) := by unfold okP; infer_instance
def nxP (s : Fin 5 → Fin 3) (r : Fin 5 → Fin 2) : Fin 5 → Fin 3 := fun j => fnx (s j) (r j)

def pb (s : Fin 5 → Fin 3) : Fin 5 → Fin 2 := fun j => if s j = 1 then 1 else 0

def RR : (Fin 5 → Fin 2) → (Fin 5 → Fin 2) → Prop := fun r s => ∀ j : Fin 4, r j.succ ≤ s j.castSucc

theorem pb_nx (s : Fin 5 → Fin 3) (r : Fin 5 → Fin 2) : pb (nxP s r) = r := by
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

theorem acc_iff : ∀ (l : List (Fin 5 → Fin 2)) (s : Fin 5 → Fin 3),
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

theorem sol_iff (l : List (Fin 5 → Fin 2)) :
    IsSolution l ↔ RunAcc okP nxP (fun _ => 0) l := by
  rw [acc_iff]
  unfold IsSolution
  have hrow : ∀ r : Fin 5 → Fin 2, Unimodal (List.ofFn fun j => (r j : ℕ)) ↔ runOK 0 (List.ofFn r) := by
    intro r
    rw [← uni_run, List.map_ofFn]; rfl
  have hcol : ∀ j : Fin 5, Unimodal (l.map fun r => (r j : ℕ)) ↔ runOK 0 (l.map fun r => r j) := by
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
  have hch' : l.IsChain (fun r s => ∀ j : Fin 4, r j.succ ≤ s j.castSucc) ↔
      (pb (fun _ => 0) :: l).IsChain RR := hch
  rw [hch']
  simp only [hrow, hcol]

theorem a_eq (n : ℕ) : a n = V okP nxP n (fun _ => 0) := by
  unfold a
  rw [← cnt okP nxP n (fun _ => 0)]
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun l => by rw [sol_iff])

abbrev SS := Fin 5 → Fin 3
def s0 : SS := fun _ => 0
def code (s : SS) : ℕ := s 0 + 3 * s 1 + 9 * s 2 + 27 * s 3 + 81 * s 4

def Tset (s : SS) : Prop := code s ∈ [0, 1, 2, 3, 4, 5, 7, 8, 9, 11, 12, 13, 14, 17, 21, 22, 23, 25, 26, 27, 29, 35, 36, 38, 39, 40, 41, 44, 53, 63, 65, 66, 67, 68, 71, 75, 76, 77, 79, 80, 81, 83, 89, 107, 108, 110, 116, 117, 119, 120, 121, 122, 125, 134, 161, 189, 191, 197, 198, 200, 201, 202, 203, 206, 215, 225, 227, 228, 229, 230, 233, 237, 238, 239, 241, 242]
instance (s : SS) : Decidable (Tset s) := by unfold Tset; infer_instance
theorem hT : ∀ s a, Tset s → okP s a → Tset (nxP s a) := by decide +kernel
theorem hs0 : ∀ a, okP s0 a → Tset (nxP s0 a) := by decide +kernel
def LL : List (List ℕ) := [[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  [16, 16, 11, 5, 5, 0, 8, 8, 7, 8, 8, 4, 4, 4, 0, 0, 0, 0, 7, 7, 5, 2, 2, 0, 5, 5, 4, 9, 9, 6, 3, 3, 0, 3, 3, 3, 6, 6, 3, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 8, 5, 3, 3, 0, 4, 4, 3, 4, 4, 2, 2, 2, 0, 0, 0, 0, 5, 5, 3, 2, 2, 0, 3, 3, 2, 8, 8, 6, 2, 2, 0, 4, 4, 4, 4, 4, 2, 2, 2, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 2, 2, 2, 6, 6, 4, 2, 2, 0, 2, 2, 2, 4, 4, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 11, 7, 4, 4, 0, 5, 5, 4, 6, 6, 3, 3, 3, 0, 0, 0, 0, 5, 5, 3, 2, 2, 0, 3, 3, 2, 6, 6, 4, 2, 2, 0, 2, 2, 2, 4, 4, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 7, 4, 3, 3, 0, 3, 3, 2, 4, 4, 2, 2, 2, 0, 0, 0, 0, 4, 4, 2, 2, 2, 0, 2, 2, 1],
  [101, 66, 36, 22, 22, 0, 25, 24, 16, 22, 11, 0, 11, 11, 0, 0, 0, 0, 20, 16, 7, 7, 7, 0, 12, 11, 6, 28, 14, 7, 7, 7, 0, 0, 0, 0, 14, 7, 0, 7, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30, 20, 7, 9, 9, 0, 8, 7, 3, 8, 4, 0, 4, 4, 0, 0, 0, 0, 14, 10, 3, 5, 5, 0, 6, 5, 2, 28, 16, 12, 4, 4, 0, 4, 4, 4, 8, 4, 0, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 8, 4, 4, 4, 0, 0, 0, 0, 8, 4, 0, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 56, 36, 16, 14, 14, 0, 12, 11, 6, 14, 7, 0, 7, 7, 0, 0, 0, 0, 14, 10, 3, 5, 5, 0, 6, 5, 2, 16, 8, 4, 4, 4, 0, 0, 0, 0, 8, 4, 0, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28, 18, 6, 8, 8, 0, 6, 5, 2, 8, 4, 0, 4, 4, 0, 0, 0, 0, 12, 8, 2, 4, 4, 0, 4, 3, 1],
  [371, 169, 59, 68, 68, 0, 53, 44, 20, 58, 29, 0, 29, 29, 0, 0, 0, 0, 50, 30, 7, 18, 18, 0, 23, 17, 6, 60, 15, 0, 15, 15, 0, 0, 0, 0, 30, 15, 0, 15, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 84, 40, 7, 20, 20, 0, 15, 10, 3, 18, 9, 0, 9, 9, 0, 0, 0, 0, 34, 18, 3, 10, 10, 0, 11, 7, 2, 64, 16, 8, 8, 8, 0, 0, 0, 0, 16, 8, 0, 8, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 8, 0, 8, 8, 0, 0, 0, 0, 16, 8, 0, 8, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 180, 81, 20, 36, 36, 0, 23, 17, 6, 32, 16, 0, 16, 16, 0, 0, 0, 0, 34, 18, 3, 10, 10, 0, 11, 7, 2, 32, 8, 0, 8, 8, 0, 0, 0, 0, 16, 8, 0, 8, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 78, 36, 6, 17, 17, 0, 11, 7, 2, 16, 8, 0, 8, 8, 0, 0, 0, 0, 28, 14, 2, 7, 7, 0, 7, 4, 1],
  [1040, 356, 67, 164, 164, 0, 97, 64, 20, 140, 70, 0, 70, 70, 0, 0, 0, 0, 116, 55, 7, 35, 35, 0, 40, 23, 6, 128, 32, 0, 32, 32, 0, 0, 0, 0, 64, 32, 0, 32, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 200, 76, 7, 39, 39, 0, 25, 13, 3, 38, 19, 0, 19, 19, 0, 0, 0, 0, 72, 31, 3, 17, 17, 0, 18, 9, 2, 128, 16, 0, 16, 16, 0, 0, 0, 0, 32, 16, 0, 16, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64, 16, 0, 16, 16, 0, 0, 0, 0, 32, 16, 0, 16, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 461, 161, 20, 77, 77, 0, 40, 23, 6, 68, 34, 0, 34, 34, 0, 0, 0, 0, 72, 31, 3, 17, 17, 0, 18, 9, 2, 64, 16, 0, 16, 16, 0, 0, 0, 0, 32, 16, 0, 16, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 180, 67, 6, 32, 32, 0, 18, 9, 2, 30, 15, 0, 15, 15, 0, 0, 0, 0, 56, 23, 2, 11, 11, 0, 11, 5, 1],
  [2516, 705, 67, 346, 346, 0, 161, 84, 20, 306, 153, 0, 153, 153, 0, 0, 0, 0, 241, 97, 7, 58, 58, 0, 63, 29, 6, 268, 67, 0, 67, 67, 0, 0, 0, 0, 134, 67, 0, 67, 67, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 430, 141, 7, 71, 71, 0, 38, 16, 3, 72, 36, 0, 36, 36, 0, 0, 0, 0, 137, 51, 3, 26, 26, 0, 27, 11, 2, 256, 32, 0, 32, 32, 0, 0, 0, 0, 64, 32, 0, 32, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 32, 0, 32, 32, 0, 0, 0, 0, 64, 32, 0, 32, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1040, 308, 20, 150, 150, 0, 63, 29, 6, 134, 67, 0, 67, 67, 0, 0, 0, 0, 137, 51, 3, 26, 26, 0, 27, 11, 2, 124, 31, 0, 31, 31, 0, 0, 0, 0, 62, 31, 0, 31, 31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 371, 120, 6, 56, 56, 0, 27, 11, 2, 52, 26, 0, 26, 26, 0, 0, 0, 0, 101, 36, 2, 16, 16, 0, 16, 6, 1],
  [5573, 1370, 67, 682, 682, 0, 245, 104, 20, 620, 310, 0, 310, 310, 0, 0, 0, 0, 454, 162, 7, 87, 87, 0, 92, 35, 6, 540, 135, 0, 135, 135, 0, 0, 0, 0, 270, 135, 0, 135, 135, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 857, 255, 7, 123, 123, 0, 54, 19, 3, 124, 62, 0, 62, 62, 0, 0, 0, 0, 240, 80, 3, 37, 37, 0, 38, 13, 2, 504, 63, 0, 63, 63, 0, 0, 0, 0, 126, 63, 0, 63, 63, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 252, 63, 0, 63, 63, 0, 0, 0, 0, 126, 63, 0, 63, 63, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2164, 576, 20, 277, 277, 0, 92, 35, 6, 248, 124, 0, 124, 124, 0, 0, 0, 0, 240, 80, 3, 37, 37, 0, 38, 13, 2, 228, 57, 0, 57, 57, 0, 0, 0, 0, 114, 57, 0, 57, 57, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 707, 208, 6, 93, 93, 0, 38, 13, 2, 84, 42, 0, 42, 42, 0, 0, 0, 0, 169, 54, 2, 22, 22, 0, 22, 7, 1],
  [11635, 2627, 67, 1294, 1294, 0, 349, 124, 20, 1190, 595, 0, 595, 595, 0, 0, 0, 0, 790, 256, 7, 122, 122, 0, 127, 41, 6, 1040, 260, 0, 260, 260, 0, 0, 0, 0, 520, 260, 0, 260, 260, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1606, 447, 7, 204, 204, 0, 73, 22, 3, 198, 99, 0, 99, 99, 0, 0, 0, 0, 394, 120, 3, 50, 50, 0, 51, 15, 2, 960, 120, 0, 120, 120, 0, 0, 0, 0, 240, 120, 0, 120, 120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 480, 120, 0, 120, 120, 0, 0, 0, 0, 240, 120, 0, 120, 120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4246, 1054, 20, 493, 493, 0, 127, 41, 6, 436, 218, 0, 218, 218, 0, 0, 0, 0, 394, 120, 3, 50, 50, 0, 51, 15, 2, 396, 99, 0, 99, 99, 0, 0, 0, 0, 198, 99, 0, 99, 99, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1269, 349, 6, 148, 148, 0, 51, 15, 2, 128, 64, 0, 64, 64, 0, 0, 0, 0, 267, 78, 2, 29, 29, 0, 29, 8, 1],
  [23230, 4963, 67, 2393, 2393, 0, 473, 144, 20, 2194, 1097, 0, 1097, 1097, 0, 0, 0, 0, 1290, 385, 7, 163, 163, 0, 168, 47, 6, 1916, 479, 0, 479, 479, 0, 0, 0, 0, 958, 479, 0, 479, 479, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2857, 757, 7, 325, 325, 0, 95, 25, 3, 298, 149, 0, 149, 149, 0, 0, 0, 0, 614, 173, 3, 65, 65, 0, 66, 17, 2, 1752, 219, 0, 219, 219, 0, 0, 0, 0, 438, 219, 0, 219, 219, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 876, 219, 0, 219, 219, 0, 0, 0, 0, 438, 219, 0, 219, 219, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7950, 1884, 20, 851, 851, 0, 168, 47, 6, 734, 367, 0, 367, 367, 0, 0, 0, 0, 614, 173, 3, 65, 65, 0, 66, 17, 2, 652, 163, 0, 163, 163, 0, 0, 0, 0, 326, 163, 0, 163, 163, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2170, 567, 6, 227, 227, 0, 66, 17, 2, 186, 93, 0, 93, 93, 0, 0, 0, 0, 403, 109, 2, 37, 37, 0, 37, 9, 1],
  [44703, 9218, 67, 4332, 4332, 0, 617, 164, 20, 3916, 1958, 0, 1958, 1958, 0, 0, 0, 0, 2001, 555, 7, 210, 210, 0, 215, 53, 6, 3388, 847, 0, 847, 847, 0, 0, 0, 0, 1694, 847, 0, 847, 847, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4860, 1238, 7, 499, 499, 0, 120, 28, 3, 428, 214, 0, 214, 214, 0, 0, 0, 0, 917, 241, 3, 82, 82, 0, 83, 19, 2, 3056, 382, 0, 382, 382, 0, 0, 0, 0, 764, 382, 0, 382, 382, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1528, 382, 0, 382, 382, 0, 0, 0, 0, 764, 382, 0, 382, 382, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14308, 3285, 20, 1428, 1428, 0, 215, 53, 6, 1190, 595, 0, 595, 595, 0, 0, 0, 0, 917, 241, 3, 82, 82, 0, 83, 19, 2, 1024, 256, 0, 256, 256, 0, 0, 0, 0, 512, 256, 0, 256, 256, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3563, 893, 6, 337, 337, 0, 83, 19, 2, 260, 130, 0, 130, 130, 0, 0, 0, 0, 586, 148, 2, 46, 46, 0, 46, 10, 1],
  [83305, 16804, 67, 7683, 7683, 0, 781, 184, 20, 6794, 3397, 0, 3397, 3397, 0, 0, 0, 0, 2976, 772, 7, 263, 263, 0, 268, 59, 6, 5772, 1443, 0, 1443, 1443, 0, 0, 0, 0, 2886, 1443, 0, 1443, 1443, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7952, 1958, 7, 741, 741, 0, 148, 31, 3, 592, 296, 0, 296, 296, 0, 0, 0, 0, 1322, 326, 3, 101, 101, 0, 102, 21, 2, 5104, 638, 0, 638, 638, 0, 0, 0, 0, 1276, 638, 0, 638, 638, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2552, 638, 0, 638, 638, 0, 0, 0, 0, 1276, 638, 0, 638, 638, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24877, 5584, 20, 2332, 2332, 0, 268, 59, 6, 1866, 933, 0, 933, 933, 0, 0, 0, 0, 1322, 326, 3, 101, 101, 0, 102, 21, 2, 1544, 386, 0, 386, 386, 0, 0, 0, 0, 772, 386, 0, 386, 386, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5650, 1366, 6, 486, 486, 0, 102, 21, 2, 352, 176, 0, 176, 176, 0, 0, 0, 0, 826, 196, 2, 56, 56, 0, 56, 11, 1],
  [150815, 30032, 67, 13345, 13345, 0, 965, 204, 20, 11482, 5741, 0, 5741, 5741, 0, 0, 0, 0, 4274, 1042, 7, 322, 322, 0, 327, 65, 6, 9508, 2377, 0, 2377, 2377, 0, 0, 0, 0, 4754, 2377, 0, 2377, 2377, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12576, 3002, 7, 1068, 1068, 0, 179, 34, 3, 794, 397, 0, 397, 397, 0, 0, 0, 0, 1850, 430, 3, 122, 122, 0, 123, 23, 2, 8192, 1024, 0, 1024, 1024, 0, 0, 0, 0, 2048, 1024, 0, 1024, 1024, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4096, 1024, 0, 1024, 1024, 0, 0, 0, 0, 2048, 1024, 0, 1024, 1024, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41945, 9255, 20, 3710, 3710, 0, 327, 65, 6, 2840, 1420, 0, 1420, 1420, 0, 0, 0, 0, 1850, 430, 3, 122, 122, 0, 123, 23, 2, 2248, 562, 0, 562, 562, 0, 0, 0, 0, 1124, 562, 0, 562, 562, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8692, 2034, 6, 683, 683, 0, 123, 23, 2, 464, 232, 0, 232, 232, 0, 0, 0, 0, 1134, 254, 2, 67, 67, 0, 67, 12, 1],
  [265901, 52586, 67, 22691, 22691, 0, 1169, 224, 20, 18928, 9464, 0, 9464, 9464, 0, 0, 0, 0, 5960, 1371, 7, 387, 387, 0, 392, 71, 6, 15192, 3798, 0, 3798, 3798, 0, 0, 0, 0, 7596, 3798, 0, 3798, 3798, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19302, 4474, 7, 1499, 1499, 0, 213, 37, 3, 1038, 519, 0, 519, 519, 0, 0, 0, 0, 2524, 555, 3, 145, 145, 0, 146, 25, 2, 12688, 1586, 0, 1586, 1586, 0, 0, 0, 0, 3172, 1586, 0, 1586, 1586, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6344, 1586, 0, 1586, 1586, 0, 0, 0, 0, 3172, 1586, 0, 1586, 1586, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 68796, 14967, 20, 5757, 5757, 0, 392, 71, 6, 4208, 2104, 0, 2104, 2104, 0, 0, 0, 0, 2524, 555, 3, 145, 145, 0, 146, 25, 2, 3176, 794, 0, 794, 794, 0, 0, 0, 0, 1588, 794, 0, 794, 794, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13020, 2955, 6, 938, 938, 0, 146, 25, 2, 598, 299, 0, 299, 299, 0, 0, 0, 0, 1522, 323, 2, 79, 79, 0, 79, 13, 1],
  [457485, 90192, 67, 37763, 37763, 0, 1393, 244, 20, 30470, 15235, 0, 15235, 15235, 0, 0, 0, 0, 8105, 1765, 7, 458, 458, 0, 463, 77, 6, 23612, 5903, 0, 5903, 5903, 0, 0, 0, 0, 11806, 5903, 0, 5903, 5903, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28850, 6499, 7, 2055, 2055, 0, 250, 40, 3, 1328, 664, 0, 664, 664, 0, 0, 0, 0, 3369, 703, 3, 170, 170, 0, 171, 27, 2, 19040, 2380, 0, 2380, 2380, 0, 0, 0, 0, 4760, 2380, 0, 2380, 2380, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9520, 2380, 0, 2380, 2380, 0, 0, 0, 0, 4760, 2380, 0, 2380, 2380, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 110045, 23642, 20, 8726, 8726, 0, 463, 77, 6, 6086, 3043, 0, 3043, 3043, 0, 0, 0, 0, 3369, 703, 3, 170, 170, 0, 171, 27, 2, 4372, 1093, 0, 1093, 1093, 0, 0, 0, 0, 2186, 1093, 0, 1093, 1093, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19047, 4198, 6, 1262, 1262, 0, 171, 27, 2, 756, 378, 0, 378, 378, 0, 0, 0, 0, 2003, 404, 2, 92, 92, 0, 92, 14, 1],
  [769447, 151540, 67, 61525, 61525, 0, 1637, 264, 20, 47952, 23976, 0, 23976, 23976, 0, 0, 0, 0, 10786, 2230, 7, 535, 535, 0, 540, 83, 6, 35788, 8947, 0, 8947, 8947, 0, 0, 0, 0, 17894, 8947, 0, 8947, 8947, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 42115, 9225, 7, 2759, 2759, 0, 290, 43, 3, 1668, 834, 0, 834, 834, 0, 0, 0, 0, 4412, 876, 3, 197, 197, 0, 198, 29, 2, 27784, 3473, 0, 3473, 3473, 0, 0, 0, 0, 6946, 3473, 0, 3473, 3473, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13892, 3473, 0, 3473, 3473, 0, 0, 0, 0, 6946, 3473, 0, 3473, 3473, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 172055, 36524, 20, 12939, 12939, 0, 540, 83, 6, 8612, 4306, 0, 4306, 4306, 0, 0, 0, 0, 4412, 876, 3, 197, 197, 0, 198, 29, 2, 5884, 1471, 0, 1471, 1471, 0, 0, 0, 0, 2942, 1471, 0, 1471, 1471, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27281, 5844, 6, 1667, 1667, 0, 198, 29, 2, 940, 470, 0, 470, 470, 0, 0, 0, 0, 2591, 498, 2, 106, 106, 0, 106, 15, 1],
  [1267085, 249528, 67, 98185, 98185, 0, 1901, 284, 20, 73862, 36931, 0, 36931, 36931, 0, 0, 0, 0, 14086, 2772, 7, 618, 618, 0, 623, 89, 6, 53016, 13254, 0, 13254, 13254, 0, 0, 0, 0, 26508, 13254, 0, 13254, 13254, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 60194, 12825, 7, 3636, 3636, 0, 333, 46, 3, 2062, 1031, 0, 1031, 1031, 0, 0, 0, 0, 5682, 1076, 3, 226, 226, 0, 227, 31, 2, 39552, 4944, 0, 4944, 4944, 0, 0, 0, 0, 9888, 4944, 0, 4944, 4944, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19776, 4944, 0, 4944, 4944, 0, 0, 0, 0, 9888, 4944, 0, 4944, 4944, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 263449, 55260, 20, 18799, 18799, 0, 623, 89, 6, 11948, 5974, 0, 5974, 5974, 0, 0, 0, 0, 5682, 1076, 3, 226, 226, 0, 227, 31, 2, 7764, 1941, 0, 1941, 1941, 0, 0, 0, 0, 3882, 1941, 0, 1941, 1941, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38339, 7987, 6, 2166, 2166, 0, 227, 31, 2, 1152, 576, 0, 576, 576, 0, 0, 0, 0, 3301, 606, 2, 121, 121, 0, 121, 16, 1],
  [2045843, 402909, 67, 153598, 153598, 0, 2185, 304, 20, 111494, 55747, 0, 55747, 55747, 0, 0, 0, 0, 18094, 3397, 7, 707, 707, 0, 712, 95, 6, 76916, 19229, 0, 19229, 19229, 0, 0, 0, 0, 38458, 19229, 0, 19229, 19229, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 84415, 17499, 7, 4713, 4713, 0, 379, 49, 3, 2514, 1257, 0, 1257, 1257, 0, 0, 0, 0, 7210, 1305, 3, 257, 257, 0, 258, 33, 2, 55080, 6885, 0, 6885, 6885, 0, 0, 0, 0, 13770, 6885, 0, 6885, 6885, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27540, 6885, 0, 6885, 6885, 0, 0, 0, 0, 13770, 6885, 0, 6885, 6885, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 395731, 81994, 20, 26803, 26803, 0, 712, 95, 6, 16282, 8141, 0, 8141, 8141, 0, 0, 0, 0, 7210, 1305, 3, 257, 257, 0, 258, 33, 2, 10068, 2517, 0, 2517, 2517, 0, 0, 0, 0, 5034, 2517, 0, 2517, 2517, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 52962, 10735, 6, 2773, 2773, 0, 258, 33, 2, 1394, 697, 0, 697, 697, 0, 0, 0, 0, 4149, 729, 2, 137, 137, 0, 137, 17, 1]]
def Lit (n : ℕ) (s : SS) : ℕ := (LL.getD n []).getD (code s) 0
theorem hL0 : ∀ s : SS, Lit 0 s = 1 := by decide +kernel
theorem hLs_0 : ∀ s : SS, ∑ a, (if okP s a then Lit 0 (nxP s a) else 0) = Lit 1 s := by decide +kernel
theorem hLs_1 : ∀ s : SS, ∑ a, (if okP s a then Lit 1 (nxP s a) else 0) = Lit 2 s := by decide +kernel
theorem hLs_2 : ∀ s : SS, ∑ a, (if okP s a then Lit 2 (nxP s a) else 0) = Lit 3 s := by decide +kernel
theorem hLs_3 : ∀ s : SS, ∑ a, (if okP s a then Lit 3 (nxP s a) else 0) = Lit 4 s := by decide +kernel
theorem hLs_4 : ∀ s : SS, ∑ a, (if okP s a then Lit 4 (nxP s a) else 0) = Lit 5 s := by decide +kernel
theorem hLs_5 : ∀ s : SS, ∑ a, (if okP s a then Lit 5 (nxP s a) else 0) = Lit 6 s := by decide +kernel
theorem hLs_6 : ∀ s : SS, ∑ a, (if okP s a then Lit 6 (nxP s a) else 0) = Lit 7 s := by decide +kernel
theorem hLs_7 : ∀ s : SS, ∑ a, (if okP s a then Lit 7 (nxP s a) else 0) = Lit 8 s := by decide +kernel
theorem hLs_8 : ∀ s : SS, ∑ a, (if okP s a then Lit 8 (nxP s a) else 0) = Lit 9 s := by decide +kernel
theorem hLs_9 : ∀ s : SS, ∑ a, (if okP s a then Lit 9 (nxP s a) else 0) = Lit 10 s := by decide +kernel
theorem hLs_10 : ∀ s : SS, ∑ a, (if okP s a then Lit 10 (nxP s a) else 0) = Lit 11 s := by decide +kernel
theorem hLs_11 : ∀ s : SS, ∑ a, (if okP s a then Lit 11 (nxP s a) else 0) = Lit 12 s := by decide +kernel
theorem hLs_12 : ∀ s : SS, ∑ a, (if okP s a then Lit 12 (nxP s a) else 0) = Lit 13 s := by decide +kernel
theorem hLs_13 : ∀ s : SS, ∑ a, (if okP s a then Lit 13 (nxP s a) else 0) = Lit 14 s := by decide +kernel
theorem hLs_14 : ∀ s : SS, ∑ a, (if okP s a then Lit 14 (nxP s a) else 0) = Lit 15 s := by decide +kernel
theorem hLs_15 : ∀ s : SS, ∑ a, (if okP s a then Lit 15 (nxP s a) else 0) = Lit 16 s := by decide +kernel
theorem hLs : ∀ n, n < 16 → ∀ s : SS, ∑ a, (if okP s a then Lit n (nxP s a) else 0) = Lit (n + 1) s := by
  intro n hn
  interval_cases n
  · exact hLs_0
  · exact hLs_1
  · exact hLs_2
  · exact hLs_3
  · exact hLs_4
  · exact hLs_5
  · exact hLs_6
  · exact hLs_7
  · exact hLs_8
  · exact hLs_9
  · exact hLs_10
  · exact hLs_11
  · exact hLs_12
  · exact hLs_13
  · exact hLs_14
  · exact hLs_15
theorem hVL : ∀ n, n ≤ 16 → ∀ s : SS, V okP nxP n s = Lit n s := by
  intro n
  induction n with
  | zero => intro _ s; rw [hL0]; rfl
  | succ n ih =>
    intro h s
    rw [← hLs n (by omega) s]
    show (∑ a, if okP s a then V okP nxP n (nxP s a) else 0) = _
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [ih (by omega)]
def cc : ℕ → ℤ := fun j => [0, 0, 0, 0, -1, 11, -55, 165, -330, 462, -462, 330, -165, 55, -11, 1].getD j 0
theorem h0L : ∀ s, Tset s → ∑ j ∈ Finset.range (16), cc j * (Lit (0 + j) s : ℤ) = 0 := by decide +kernel
theorem h0 : ∀ s, Tset s → ∑ j ∈ Finset.range (16), cc j * (V okP nxP (0 + j) s : ℤ) = 0 := by
  intro s hs
  rw [← h0L s hs]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [hVL (0 + j) (by simp at hj; omega) s]
theorem hrecV (n : ℕ) : ∑ j ∈ Finset.range (16), cc j * (a (0 + n + 1 + j) : ℤ) = 0 := by
  have := rec_next okP nxP Tset hT 0 15 cc h0 s0 hs0 n
  simp only [a_eq]
  exact this
theorem hrecA (k : ℕ) : (a (0 + k + 1 + 15) : ℚ) = (1 : ℚ) * a (0 + k + 1 + 4) + (-11 : ℚ) * a (0 + k + 1 + 5) + (55 : ℚ) * a (0 + k + 1 + 6) + (-165 : ℚ) * a (0 + k + 1 + 7) + (330 : ℚ) * a (0 + k + 1 + 8) + (-462 : ℚ) * a (0 + k + 1 + 9) + (462 : ℚ) * a (0 + k + 1 + 10) + (-330 : ℚ) * a (0 + k + 1 + 11) + (165 : ℚ) * a (0 + k + 1 + 12) + (-55 : ℚ) * a (0 + k + 1 + 13) + (11 : ℚ) * a (0 + k + 1 + 14) := by
  have h := hrecV k
  have e0 : cc 0 = 0 := rfl
  have e1 : cc 1 = 0 := rfl
  have e2 : cc 2 = 0 := rfl
  have e3 : cc 3 = 0 := rfl
  have e4 : cc 4 = -1 := rfl
  have e5 : cc 5 = 11 := rfl
  have e6 : cc 6 = -55 := rfl
  have e7 : cc 7 = 165 := rfl
  have e8 : cc 8 = -330 := rfl
  have e9 : cc 9 = 462 := rfl
  have e10 : cc 10 = -462 := rfl
  have e11 : cc 11 = 330 := rfl
  have e12 : cc 12 = -165 := rfl
  have e13 : cc 13 = 55 := rfl
  have e14 : cc 14 = -11 := rfl
  have e15 : cc 15 = 1 := rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15] at h
  have h' := congrArg (Int.cast : ℤ → ℚ) h
  push_cast at h'
  linarith
theorem v0 : a 0 = 1 := by rw [a_eq, hVL 0 (by norm_num)]; decide +kernel
theorem v1 : a 1 = 16 := by rw [a_eq, hVL 1 (by norm_num)]; decide +kernel
theorem v2 : a 2 = 101 := by rw [a_eq, hVL 2 (by norm_num)]; decide +kernel
theorem v3 : a 3 = 371 := by rw [a_eq, hVL 3 (by norm_num)]; decide +kernel
theorem v4 : a 4 = 1040 := by rw [a_eq, hVL 4 (by norm_num)]; decide +kernel
theorem v5 : a 5 = 2516 := by rw [a_eq, hVL 5 (by norm_num)]; decide +kernel
theorem v6 : a 6 = 5573 := by rw [a_eq, hVL 6 (by norm_num)]; decide +kernel
theorem v7 : a 7 = 11635 := by rw [a_eq, hVL 7 (by norm_num)]; decide +kernel
theorem v8 : a 8 = 23230 := by rw [a_eq, hVL 8 (by norm_num)]; decide +kernel
theorem v9 : a 9 = 44703 := by rw [a_eq, hVL 9 (by norm_num)]; decide +kernel
theorem v10 : a 10 = 83305 := by rw [a_eq, hVL 10 (by norm_num)]; decide +kernel
theorem v11 : a 11 = 150815 := by rw [a_eq, hVL 11 (by norm_num)]; decide +kernel
theorem v12 : a 12 = 265901 := by rw [a_eq, hVL 12 (by norm_num)]; decide +kernel
theorem v13 : a 13 = 457485 := by rw [a_eq, hVL 13 (by norm_num)]; decide +kernel
theorem v14 : a 14 = 769447 := by rw [a_eq, hVL 14 (by norm_num)]; decide +kernel
theorem v15 : a 15 = 1267085 := by rw [a_eq, hVL 15 (by norm_num)]; decide +kernel
theorem v16 : a 16 = 2045843 := by rw [a_eq, hVL 16 (by norm_num)]; decide +kernel
def Pq (x : ℚ) : ℚ := (93 : ℚ) + (-16061/168 : ℚ) * x^1 + (102443/2400 : ℚ) * x^2 + (589/12096 : ℚ) * x^3 + (649763/362880 : ℚ) * x^4 + (589/11520 : ℚ) * x^5 + (4273/172800 : ℚ) * x^6 + (11/8064 : ℚ) * x^7 + (1/8640 : ℚ) * x^8 + (1/241920 : ℚ) * x^9 + (1/3628800 : ℚ) * x^10
theorem closed (n : ℕ) (hn : 3 ≤ n) : (a n : ℚ) = Pq (n : ℚ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 16
    · interval_cases n
      · rw [v3]; norm_num [Pq]
      · rw [v4]; norm_num [Pq]
      · rw [v5]; norm_num [Pq]
      · rw [v6]; norm_num [Pq]
      · rw [v7]; norm_num [Pq]
      · rw [v8]; norm_num [Pq]
      · rw [v9]; norm_num [Pq]
      · rw [v10]; norm_num [Pq]
      · rw [v11]; norm_num [Pq]
      · rw [v12]; norm_num [Pq]
      · rw [v13]; norm_num [Pq]
      · rw [v14]; norm_num [Pq]
      · rw [v15]; norm_num [Pq]
    · obtain ⟨k, rfl⟩ : ∃ k, n = 0 + k + 1 + 15 := ⟨n - 16, by omega⟩
      rw [hrecA k]
      rw [ih (0 + k + 1 + 4) (by omega) (by omega)]
      rw [ih (0 + k + 1 + 5) (by omega) (by omega)]
      rw [ih (0 + k + 1 + 6) (by omega) (by omega)]
      rw [ih (0 + k + 1 + 7) (by omega) (by omega)]
      rw [ih (0 + k + 1 + 8) (by omega) (by omega)]
      rw [ih (0 + k + 1 + 9) (by omega) (by omega)]
      rw [ih (0 + k + 1 + 10) (by omega) (by omega)]
      rw [ih (0 + k + 1 + 11) (by omega) (by omega)]
      rw [ih (0 + k + 1 + 12) (by omega) (by omega)]
      rw [ih (0 + k + 1 + 13) (by omega) (by omega)]
      rw [ih (0 + k + 1 + 14) (by omega) (by omega)]
      push_cast
      simp only [Pq]
      ring
noncomputable def bq (n : ℕ) : ℚ := (a (n + 1) : ℚ)
theorem bq_closed (n : ℕ) (hn : 2 ≤ n) : bq n = Pq ((n : ℚ) + 1) := by
  unfold bq
  have := closed (n + 1) (by omega)
  push_cast at this
  first | (simp only [show n ≠ 0 by omega, if_false]; exact this) | exact this
theorem hb_all : ∀ n, ∑ j ∈ Finset.range (12), ([(1 : ℚ), (-11 : ℚ), (55 : ℚ), (-165 : ℚ), (330 : ℚ), (-462 : ℚ), (462 : ℚ), (-330 : ℚ), (165 : ℚ), (-55 : ℚ), (11 : ℚ), (-1 : ℚ)] : List ℚ).getD j 0 * (if j ≤ n then bq (n - j) else 0) = if n ≤ 12 then ([(16 : ℚ), (-75 : ℚ), (140 : ℚ), (-126 : ℚ), (96 : ℚ), (-180 : ℚ), (272 : ℚ), (-200 : ℚ), (65 : ℚ), (-20 : ℚ), (27 : ℚ), (-18 : ℚ), (4 : ℚ)] : List ℚ).getD n 0 else 0 := by
  intro n
  by_cases hn : n ≤ 13
  · interval_cases n <;> simp [Finset.sum_range_succ, bq, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16] <;> norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 14 := ⟨n - 14, by omega⟩
    rw [if_neg (by omega)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    have t0 : bq (k + 14 - 0) = Pq ((k : ℚ) + 15) := by
      rw [bq_closed _ (by omega), show k + 14 - 0 = k + 14 by omega]; push_cast; ring_nf
    have t1 : bq (k + 14 - 1) = Pq ((k : ℚ) + 14) := by
      rw [bq_closed _ (by omega), show k + 14 - 1 = k + 13 by omega]; push_cast; ring_nf
    have t2 : bq (k + 14 - 2) = Pq ((k : ℚ) + 13) := by
      rw [bq_closed _ (by omega), show k + 14 - 2 = k + 12 by omega]; push_cast; ring_nf
    have t3 : bq (k + 14 - 3) = Pq ((k : ℚ) + 12) := by
      rw [bq_closed _ (by omega), show k + 14 - 3 = k + 11 by omega]; push_cast; ring_nf
    have t4 : bq (k + 14 - 4) = Pq ((k : ℚ) + 11) := by
      rw [bq_closed _ (by omega), show k + 14 - 4 = k + 10 by omega]; push_cast; ring_nf
    have t5 : bq (k + 14 - 5) = Pq ((k : ℚ) + 10) := by
      rw [bq_closed _ (by omega), show k + 14 - 5 = k + 9 by omega]; push_cast; ring_nf
    have t6 : bq (k + 14 - 6) = Pq ((k : ℚ) + 9) := by
      rw [bq_closed _ (by omega), show k + 14 - 6 = k + 8 by omega]; push_cast; ring_nf
    have t7 : bq (k + 14 - 7) = Pq ((k : ℚ) + 8) := by
      rw [bq_closed _ (by omega), show k + 14 - 7 = k + 7 by omega]; push_cast; ring_nf
    have t8 : bq (k + 14 - 8) = Pq ((k : ℚ) + 7) := by
      rw [bq_closed _ (by omega), show k + 14 - 8 = k + 6 by omega]; push_cast; ring_nf
    have t9 : bq (k + 14 - 9) = Pq ((k : ℚ) + 6) := by
      rw [bq_closed _ (by omega), show k + 14 - 9 = k + 5 by omega]; push_cast; ring_nf
    have t10 : bq (k + 14 - 10) = Pq ((k : ℚ) + 5) := by
      rw [bq_closed _ (by omega), show k + 14 - 10 = k + 4 by omega]; push_cast; ring_nf
    have t11 : bq (k + 14 - 11) = Pq ((k : ℚ) + 4) := by
      rw [bq_closed _ (by omega), show k + 14 - 11 = k + 3 by omega]; push_cast; ring_nf
    rw [if_pos (show 0 ≤ k + 14 by omega), t0, if_pos (show 1 ≤ k + 14 by omega), t1, if_pos (show 2 ≤ k + 14 by omega), t2, if_pos (show 3 ≤ k + 14 by omega), t3, if_pos (show 4 ≤ k + 14 by omega), t4, if_pos (show 5 ≤ k + 14 by omega), t5, if_pos (show 6 ≤ k + 14 by omega), t6, if_pos (show 7 ≤ k + 14 by omega), t7, if_pos (show 8 ≤ k + 14 by omega), t8, if_pos (show 9 ≤ k + 14 by omega), t9, if_pos (show 10 ≤ k + 14 by omega), t10, if_pos (show 11 ≤ k + 14 by omega), t11]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Pq]
    ring
theorem recS (n : ℕ) (hn : 13 < n) : (a n : ℤ) = (11 : ℤ) * (a (n - 1) : ℤ) + (-55 : ℤ) * (a (n - 2) : ℤ) + (165 : ℤ) * (a (n - 3) : ℤ) + (-330 : ℤ) * (a (n - 4) : ℤ) + (462 : ℤ) * (a (n - 5) : ℤ) + (-462 : ℤ) * (a (n - 6) : ℤ) + (330 : ℤ) * (a (n - 7) : ℤ) + (-165 : ℤ) * (a (n - 8) : ℤ) + (55 : ℤ) * (a (n - 9) : ℤ) + (-11 : ℤ) * (a (n - 10) : ℤ) + (1 : ℤ) * (a (n - 11) : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 14 := ⟨n - 14, by omega⟩
  have h0 := closed (k + 14) (by omega)
  have e1 : k + 14 - 1 = k + 13 := by omega
  have h1 := closed (k + 13) (by omega)
  have e2 : k + 14 - 2 = k + 12 := by omega
  have h2 := closed (k + 12) (by omega)
  have e3 : k + 14 - 3 = k + 11 := by omega
  have h3 := closed (k + 11) (by omega)
  have e4 : k + 14 - 4 = k + 10 := by omega
  have h4 := closed (k + 10) (by omega)
  have e5 : k + 14 - 5 = k + 9 := by omega
  have h5 := closed (k + 9) (by omega)
  have e6 : k + 14 - 6 = k + 8 := by omega
  have h6 := closed (k + 8) (by omega)
  have e7 : k + 14 - 7 = k + 7 := by omega
  have h7 := closed (k + 7) (by omega)
  have e8 : k + 14 - 8 = k + 6 := by omega
  have h8 := closed (k + 6) (by omega)
  have e9 : k + 14 - 9 = k + 5 := by omega
  have h9 := closed (k + 5) (by omega)
  have e10 : k + 14 - 10 = k + 4 := by omega
  have h10 := closed (k + 4) (by omega)
  have e11 : k + 14 - 11 = k + 3 := by omega
  have h11 := closed (k + 3) (by omega)
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
  have key : (a (k + 14) : ℚ) = (11 : ℚ) * (a (k + 13) : ℚ) + (-55 : ℚ) * (a (k + 12) : ℚ) + (165 : ℚ) * (a (k + 11) : ℚ) + (-330 : ℚ) * (a (k + 10) : ℚ) + (462 : ℚ) * (a (k + 9) : ℚ) + (-462 : ℚ) * (a (k + 8) : ℚ) + (330 : ℚ) * (a (k + 7) : ℚ) + (-165 : ℚ) * (a (k + 6) : ℚ) + (55 : ℚ) * (a (k + 5) : ℚ) + (-11 : ℚ) * (a (k + 4) : ℚ) + (1 : ℚ) * (a (k + 3) : ℚ) := by
    rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
    simp only [Pq]
    push_cast
    ring
  exact_mod_cast key


theorem gf_main : PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - PowerSeries.X) ^ 11 =
    16 - 75 * PowerSeries.X + 140 * PowerSeries.X ^ 2 - 126 * PowerSeries.X ^ 3 + 96 * PowerSeries.X ^ 4 - 180 * PowerSeries.X ^ 5 + 272 * PowerSeries.X ^ 6 - 200 * PowerSeries.X ^ 7 + 65 * PowerSeries.X ^ 8 - 20 * PowerSeries.X ^ 9 + 27 * PowerSeries.X ^ 10 - 18 * PowerSeries.X ^ 11 + 4 * PowerSeries.X ^ 12 := by
  have h : PowerSeries.mk bq = (16 - 75 * PowerSeries.X + 140 * PowerSeries.X ^ 2 - 126 * PowerSeries.X ^ 3 + 96 * PowerSeries.X ^ 4 - 180 * PowerSeries.X ^ 5 + 272 * PowerSeries.X ^ 6 - 200 * PowerSeries.X ^ 7 + 65 * PowerSeries.X ^ 8 - 20 * PowerSeries.X ^ 9 + 27 * PowerSeries.X ^ 10 - 18 * PowerSeries.X ^ 11 + 4 * PowerSeries.X ^ 12) * ((1 - PowerSeries.X) ^ 11)⁻¹ := by
    apply gf_gen bq 11 12 (fun j => [(1 : ℚ), (-11 : ℚ), (55 : ℚ), (-165 : ℚ), (330 : ℚ), (-462 : ℚ), (462 : ℚ), (-330 : ℚ), (165 : ℚ), (-55 : ℚ), (11 : ℚ), (-1 : ℚ)].getD j 0) (fun j => [(16 : ℚ), (-75 : ℚ), (140 : ℚ), (-126 : ℚ), (96 : ℚ), (-180 : ℚ), (272 : ℚ), (-200 : ℚ), (65 : ℚ), (-20 : ℚ), (27 : ℚ), (-18 : ℚ), (4 : ℚ)].getD j 0)
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

end OMA.S_oeis_a223774

theorem OMA.solution : type_of% @OMA.S_oeis_a223774.main := by
  refine ⟨OMA.S_oeis_a223774.gf_main, ?_⟩
  intro n hn
  linear_combination OMA.S_oeis_a223774.recS n hn

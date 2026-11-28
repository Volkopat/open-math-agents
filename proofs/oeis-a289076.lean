import OMAStatements.S_oeis_a289076

namespace OMA.S_oeis_a289076

open Filter Topology





/-! ### One pass -/

/-- Induction along the cases of `step`. -/
theorem step_rec {P : List ℕ → Prop} (h0 : P []) (h00 : ∀ l, P l → P (0 :: 0 :: l))
    (h01 : ∀ l, P l → P (0 :: 1 :: l)) (h10 : ∀ l, P l → P (1 :: 0 :: l)) (hz : P [0])
    (ho : P [1]) (hzy : ∀ y l, P ((y + 2) :: l) → P (0 :: (y + 2) :: l))
    (hoy : ∀ y l, P ((y + 1) :: l) → P (1 :: (y + 1) :: l))
    (hx : ∀ x l, P l → P ((x + 2) :: l)) : ∀ u, P u := by
  have key : ∀ n, ∀ u : List ℕ, u.length ≤ n → P u := by
    intro n
    induction n with
    | zero =>
      intro u hu
      cases u with
      | nil => exact h0
      | cons x l => simp at hu
    | succ n ih =>
      intro u hu
      rcases u with _ | ⟨x, l⟩
      · exact h0
      · simp only [List.length_cons] at hu
        rcases x with _ | _ | x
        · rcases l with _ | ⟨y, l⟩
          · exact hz
          · rcases y with _ | _ | y
            · exact h00 l (ih l (by simp at hu; omega))
            · exact h01 l (ih l (by simp at hu; omega))
            · exact hzy y l (ih _ (by simpa using hu))
        · rcases l with _ | ⟨y, l⟩
          · exact ho
          · rcases y with _ | y
            · exact h10 l (ih l (by simp at hu; omega))
            · exact hoy y l (ih _ (by simpa using hu))
        · exact hx x l (ih l (by omega))
  exact fun u => key u.length u le_rfl

lemma step_zero_cons (t : List ℕ) : ∃ r, step (0 :: t) = 0 :: r := by
  rcases t with _ | ⟨y, t⟩
  · exact ⟨[], rfl⟩
  · rcases y with _ | _ | y
    · exact ⟨0 :: 1 :: 0 :: step t, rfl⟩
    · exact ⟨1 :: 1 :: step t, rfl⟩
    · exact ⟨step ((y + 2) :: t), rfl⟩

lemma step_one_cons (t : List ℕ) : ∃ r, step (1 :: t) = 1 :: r := by
  rcases t with _ | ⟨y, t⟩
  · exact ⟨[], rfl⟩
  · rcases y with _ | y
    · exact ⟨0 :: 0 :: step t, rfl⟩
    · exact ⟨step ((y + 1) :: t), rfl⟩

/-- A pass maps a prefix of a word to a prefix of its image: a lone final letter is copied, and
every rule image begins with the letter it replaces. -/
lemma step_mono (u : List ℕ) : ∀ t, step u <+: step (u ++ t) := by
  refine step_rec (P := fun u => ∀ t, step u <+: step (u ++ t)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ u
  · intro t
    exact List.nil_prefix
  · intro l ih t
    obtain ⟨r, hr⟩ := ih t
    exact ⟨r, by
      show 0 :: 0 :: 1 :: 0 :: (step l ++ r) = 0 :: 0 :: 1 :: 0 :: step (l ++ t)
      rw [hr]⟩
  · intro l ih t
    obtain ⟨r, hr⟩ := ih t
    exact ⟨r, by
      show 0 :: 1 :: 1 :: (step l ++ r) = 0 :: 1 :: 1 :: step (l ++ t)
      rw [hr]⟩
  · intro l ih t
    obtain ⟨r, hr⟩ := ih t
    exact ⟨r, by
      show 1 :: 0 :: 0 :: (step l ++ r) = 1 :: 0 :: 0 :: step (l ++ t)
      rw [hr]⟩
  · intro t
    obtain ⟨r, hr⟩ := step_zero_cons t
    exact ⟨r, by
      show 0 :: r = step (0 :: t)
      rw [hr]⟩
  · intro t
    obtain ⟨r, hr⟩ := step_one_cons t
    exact ⟨r, by
      show 1 :: r = step (1 :: t)
      rw [hr]⟩
  · intro y l ih t
    obtain ⟨r, hr⟩ := ih t
    exact ⟨r, by
      show 0 :: (step ((y + 2) :: l) ++ r) = 0 :: step ((y + 2) :: l ++ t)
      rw [hr]⟩
  · intro y l ih t
    obtain ⟨r, hr⟩ := ih t
    exact ⟨r, by
      show 1 :: (step ((y + 1) :: l) ++ r) = 1 :: step ((y + 1) :: l ++ t)
      rw [hr]⟩
  · intro x l ih t
    obtain ⟨r, hr⟩ := ih t
    exact ⟨r, by
      show (x + 2) :: (step l ++ r) = (x + 2) :: step (l ++ t)
      rw [hr]⟩

lemma step_prefix {u v : List ℕ} (h : u <+: v) : step u <+: step v := by
  obtain ⟨t, rfl⟩ := h
  exact step_mono u t

/-- A pass does not shorten a word. -/
lemma step_length (u : List ℕ) : u.length ≤ (step u).length := by
  refine step_rec (P := fun u => u.length ≤ (step u).length) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ u
  · exact le_rfl
  · intro l ih
    show l.length + 2 ≤ (step l).length + 4
    omega
  · intro l ih
    show l.length + 2 ≤ (step l).length + 3
    omega
  · intro l ih
    show l.length + 2 ≤ (step l).length + 3
    omega
  · exact le_rfl
  · exact le_rfl
  · intro y l ih
    show ((y + 2) :: l).length + 1 ≤ (step ((y + 2) :: l)).length + 1
    omega
  · intro y l ih
    show ((y + 1) :: l).length + 1 ≤ (step ((y + 1) :: l)).length + 1
    omega
  · intro x l ih
    show l.length + 1 ≤ (step l).length + 1
    omega

/-- Each iterate is a prefix of the next. -/
lemma iter_prefix (n : ℕ) : iter n <+: iter (n + 1) := by
  induction n with
  | zero => exact ⟨[1, 0], rfl⟩
  | succ n ih => exact step_prefix ih

lemma iter_prefix_le {m n : ℕ} (h : m ≤ n) : iter m <+: iter n := by
  induction n, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n _ ih => exact ih.trans (iter_prefix n)

lemma iter_head (n : ℕ) : ∃ l, iter n = 0 :: 0 :: l := by
  induction n with
  | zero => exact ⟨[], rfl⟩
  | succ n ih =>
    obtain ⟨l, hl⟩ := ih
    exact ⟨1 :: 0 :: step l, by rw [show iter (n + 1) = step (iter n) from rfl, hl]; rfl⟩

lemma iter_length (n : ℕ) : n + 2 ≤ (iter n).length := by
  induction n with
  | zero => decide
  | succ n ih =>
    obtain ⟨l, hl⟩ := iter_head n
    rw [show iter (n + 1) = step (iter n) from rfl, hl]
    rw [hl] at ih
    have := step_length l
    show n + 1 + 2 ≤ (step l).length + 4
    simp only [List.length_cons] at ih
    omega

/-! ### Blocks -/

/-- The blocks A = 1, B = 101, C = 1001, D = 10001, E = 100101, G = 10000101,
H = 100001001, numbered 0 to 6. -/
def tok : ℕ → List ℕ
  | 0 => [1]
  | 1 => [1, 0, 1]
  | 2 => [1, 0, 0, 1]
  | 3 => [1, 0, 0, 0, 1]
  | 4 => [1, 0, 0, 1, 0, 1]
  | 5 => [1, 0, 0, 0, 0, 1, 0, 1]
  | _ => [1, 0, 0, 0, 0, 1, 0, 0, 1]

/-- The images of the blocks: A -> A, B -> C, C -> D A, D -> G, E -> D B A, G -> H B A,
H -> H E. -/
def tauT : ℕ → List ℕ
  | 0 => [0]
  | 1 => [2]
  | 2 => [3, 0]
  | 3 => [5]
  | 4 => [3, 1, 0]
  | 5 => [6, 1, 0]
  | _ => [6, 4]

/-- The block morphism. -/
def tau (s : List ℕ) : List ℕ := s.flatMap tauT

/-- The word of a list of blocks. -/
def flat (s : List ℕ) : List ℕ := s.flatMap tok

/-- All blocks are numbered at most 6. -/
def Valid (s : List ℕ) : Prop := ∀ k ∈ s, k ≤ 6

lemma flat_cons (k : ℕ) (s : List ℕ) : flat (k :: s) = tok k ++ flat s := by
  simp [flat]

lemma flat_append (u v : List ℕ) : flat (u ++ v) = flat u ++ flat v := by
  simp [flat]

lemma tau_cons (k : ℕ) (s : List ℕ) : tau (k :: s) = tauT k ++ tau s := by
  simp [tau]

lemma tau_append (u v : List ℕ) : tau (u ++ v) = tau u ++ tau v := by
  simp [tau]

lemma tauT_valid (k : ℕ) : Valid (tauT k) := by
  intro x hx
  rcases k with _ | _ | _ | _ | _ | _ | k <;> simp [tauT] at hx <;> omega

lemma tau_valid (s : List ℕ) : Valid (tau s) := by
  intro x hx
  simp only [tau, List.mem_flatMap] at hx
  obtain ⟨k, -, hk⟩ := hx
  exact tauT_valid k x hk

lemma valid_cons {k : ℕ} {s : List ℕ} (h : Valid (k :: s)) : k ≤ 6 ∧ Valid s :=
  ⟨h k (by simp), fun x hx => h x (by simp [hx])⟩

lemma valid_append {u v : List ℕ} (hu : Valid u) (hv : Valid v) : Valid (u ++ v) := by
  intro y hy
  rcases List.mem_append.mp hy with h | h
  · exact hu y h
  · exact hv y h

lemma tok_head (k : ℕ) : ∃ r, tok k = 1 :: r := by
  rcases k with _ | _ | _ | _ | _ | _ | k <;> exact ⟨_, rfl⟩

/-- The pass over a block, followed by a word that starts with 1, is the pass over the block
followed by the pass over the rest. -/
lemma tok_cut (k : ℕ) (hk : k ≤ 6) (w : List ℕ) :
    step (tok k ++ 1 :: w) = step (tok k) ++ step (1 :: w) := by
  interval_cases k <;> rfl

lemma step_tok (k : ℕ) (hk : k ≤ 6) : step (tok k) = flat (tauT k) := by
  interval_cases k <;> rfl

lemma step_flat : ∀ s : List ℕ, Valid s → step (flat s) = flat (tau s)
  | [], _ => rfl
  | [k], hs => by
    have hk := hs k (by simp)
    rw [show flat [k] = tok k by simp [flat], step_tok k hk, show tau [k] = tauT k by simp [tau]]
  | k :: k' :: s, hs => by
    obtain ⟨hk, hs'⟩ := valid_cons hs
    obtain ⟨r, hr⟩ := tok_head k'
    have ih := step_flat (k' :: s) hs'
    rw [flat_cons, flat_cons, hr, List.cons_append, tok_cut k hk, ← List.cons_append, ← hr,
      ← flat_cons, ih, step_tok k hk, tau_cons k (k' :: s), flat_append]

/-! ### The fixed point -/

/-- The letters before the blocks. -/
def head : List ℕ := [0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1]

/-- The blocks A D E that each pass adds after the head. -/
def P : List ℕ := [0, 3, 4]

lemma head_cut (w : List ℕ) : step (head ++ 1 :: w) = step head ++ step (1 :: w) := rfl

lemma step_head : step head = head ++ flat P := by decide

/-- T k: the blocks P tau(P) ... tau^k(P). -/
def T : ℕ → List ℕ
  | 0 => P
  | k + 1 => P ++ tau (T k)

lemma T_valid (k : ℕ) : Valid (T k) := by
  cases k with
  | zero =>
    intro y hy
    simp [T, P] at hy
    omega
  | succ k =>
    exact valid_append (by intro y hy; simp [P] at hy; omega) (tau_valid _)

/-- V k: the head followed by the word of T k. -/
def V (k : ℕ) : List ℕ := head ++ flat (T k)

lemma step_V (k : ℕ) : step (V k) = V (k + 1) := by
  have hT : ∃ s, T k = 0 :: s := by
    cases k with
    | zero => exact ⟨[3, 4], rfl⟩
    | succ k => exact ⟨3 :: 4 :: tau (T k), rfl⟩
  obtain ⟨s, hs⟩ := hT
  have e : flat (T k) = 1 :: flat s := by rw [hs, flat_cons]; rfl
  unfold V
  rw [e, head_cut, ← e, step_flat _ (T_valid k), step_head, List.append_assoc, ← flat_append]
  rfl

lemma iter_V (k : ℕ) : iter (k + 5) <+: V k := by
  induction k with
  | zero => exact ⟨[1], by decide⟩
  | succ k ih =>
    rw [show k + 1 + 5 = k + 5 + 1 by ring, show iter (k + 5 + 1) = step (iter (k + 5)) from rfl,
      ← step_V]
    exact step_prefix ih

lemma T_prefix (k : ℕ) : T k <+: T (k + 1) := by
  induction k with
  | zero => exact ⟨tau P, rfl⟩
  | succ k ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨tau t, by
      show P ++ tau (T k) ++ tau t = P ++ tau (T (k + 1))
      rw [List.append_assoc, ← tau_append, ht]⟩

lemma V_prefix_succ (k : ℕ) : V k <+: V (k + 1) := by
  obtain ⟨t, ht⟩ := T_prefix k
  exact ⟨flat t, by unfold V; rw [List.append_assoc, ← flat_append, ht]⟩

lemma V_prefix {k k' : ℕ} (h : k ≤ k') : V k <+: V k' := by
  induction k', h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ k' _ ih => exact ih.trans (V_prefix_succ k')

lemma getD_prefix {l₁ l₂ : List ℕ} (h : l₁ <+: l₂) {i : ℕ} (hi : i < l₁.length) :
    l₁.getD i 0 = l₂.getD i 0 := by
  obtain ⟨s, rfl⟩ := h
  rw [List.getD_append _ _ _ _ hi]

lemma W_eq (k i : ℕ) (hi : i < (V k).length) : W i = (V k).getD i 0 := by
  have hl : i < (iter (i + 1)).length := by
    have := iter_length (i + 1)
    omega
  have hp : iter (i + 1) <+: V (i + 1) :=
    (iter_prefix_le (show i + 1 ≤ i + 1 + 5 by omega)).trans (iter_V (i + 1))
  have hl' : i < (V (i + 1)).length := lt_of_lt_of_le hl hp.length_le
  unfold W
  rw [getD_prefix hp hl]
  rcases le_total (i + 1) k with h | h
  · exact getD_prefix (V_prefix h) hl'
  · exact (getD_prefix (V_prefix h) hi).symm

lemma tau_length (s : List ℕ) : s.length ≤ (tau s).length := by
  induction s with
  | nil => simp [tau]
  | cons k s ih =>
    rw [tau_cons, List.length_append, List.length_cons]
    have : 1 ≤ (tauT k).length := by rcases k with _ | _ | _ | _ | _ | _ | k <;> simp [tauT]
    omega

lemma T_length (k : ℕ) : k + 1 ≤ (T k).length := by
  induction k with
  | zero => decide
  | succ k ih =>
    show k + 1 + 1 ≤ (P ++ tau (T k)).length
    rw [List.length_append]
    have := tau_length (T k)
    simp only [P, List.length_cons, List.length_nil]
    omega

lemma flat_ones (s : List ℕ) : s.length ≤ (flat s).count 1 := by
  induction s with
  | nil => simp [flat]
  | cons k s ih =>
    obtain ⟨r, hr⟩ := tok_head k
    rw [flat_cons, List.count_append, hr, List.count_cons_self, List.length_cons]
    omega

lemma V_ones (k : ℕ) : k + 1 ≤ (V k).count 1 := by
  unfold V
  rw [List.count_append]
  have := flat_ones (T k)
  have := T_length k
  omega

lemma V_length (k : ℕ) : k ≤ (V k).length := by
  have h1 := V_ones k
  have h2 : (V k).count 1 ≤ (V k).length := List.count_le_length
  omega

lemma tok_letters (k : ℕ) : ∀ x ∈ tok k, x ≤ 1 := by
  intro x hx
  rcases k with _ | _ | _ | _ | _ | _ | k <;> simp [tok] at hx <;> omega

lemma V_letters (k : ℕ) : ∀ x ∈ V k, x ≤ 1 := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · simp [head] at h
    omega
  · simp only [flat, List.mem_flatMap] at h
    obtain ⟨j, -, hj⟩ := h
    exact tok_letters j x hj

/-! ### Counting along the fixed point -/

lemma W_le (i : ℕ) : W i ≤ 1 := by
  have hi : i < (V (i + 1)).length := by have := V_length (i + 1); omega
  rw [W_eq (i + 1) i hi, List.getD_eq_getElem _ _ hi]
  exact V_letters _ _ (List.getElem_mem hi)

/-- Z(N): the number of letters 0 among the first N letters of W. -/
noncomputable def Z (N : ℕ) : ℕ := Nat.count (fun i => W i = 0) N

/-- O(N): the number of letters 1 among the first N letters of W. -/
noncomputable def O (N : ℕ) : ℕ := Nat.count (fun i => W i = 1) N

lemma Z_succ (N : ℕ) : Z (N + 1) = Z N + if W N = 0 then 1 else 0 := Nat.count_succ _ _

lemma O_succ (N : ℕ) : O (N + 1) = O N + if W N = 1 then 1 else 0 := Nat.count_succ _ _

lemma counts_eq (k N : ℕ) (hN : N ≤ (V k).length) :
    Z N = ((V k).take N).count 0 ∧ O N = ((V k).take N).count 1 := by
  induction N with
  | zero => simp [Z, O]
  | succ N ih =>
    have hN' : N < (V k).length := by omega
    have hW : W N = (V k)[N] := by rw [W_eq k N hN', List.getD_eq_getElem _ _ hN']
    obtain ⟨h1, h2⟩ := ih (by omega)
    rw [Z_succ, O_succ, h1, h2, List.take_add_one, List.getElem?_eq_getElem hN',
      List.count_append, List.count_append, hW]
    constructor <;> simp [List.count_singleton]

lemma O_le (N : ℕ) : O N ≤ N := by
  induction N with
  | zero => simp [O]
  | succ N ih =>
    rw [O_succ]
    split_ifs <;> omega

lemma ones_infinite : (setOf (fun i => W i = 1)).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  have hconst : ∀ j, O (B + 1 + j) = O (B + 1) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      have hno : ¬ W (B + 1 + j) = 1 := fun h => by
        have := hB h
        omega
      rw [show B + 1 + (j + 1) = B + 1 + j + 1 by ring, O_succ, if_neg hno, ih, add_zero]
  have hle := O_le (B + 1)
  have hV := V_ones (B + 1)
  have hL := V_length (B + 1)
  have hO : O (V (B + 1)).length = (V (B + 1)).count 1 := by
    rw [(counts_eq (B + 1) _ le_rfl).2, List.take_length]
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hL
  rw [hj, hconst] at hO
  omega

/-! ### The first letters -/

lemma V14_length : 9598 ≤ (V 14).length := by decide +kernel

lemma W9597 : W 9597 = 1 := by
  rw [W_eq 14 9597 (by have := V14_length; omega)]
  decide +kernel

lemma O9597 : O 9597 = 4675 := by
  rw [(counts_eq 14 9597 (by have := V14_length; omega)).2]
  decide +kernel

lemma a4676 : a 4676 = 9598 := by
  have h := Nat.nth_count (p := fun i => W i = 1) W9597
  have e : Nat.count (fun i => W i = 1) 9597 = 4675 := O9597
  rw [e] at h
  show Nat.nth (fun i => W i = 1) (4676 - 1) + 1 = 9598
  rw [show 4676 - 1 = 4675 from rfl, h]

/-! ### Token counts -/

/-- Counts of the seven blocks in a block list. -/
structure C7 where
  n0 : ℕ
  n1 : ℕ
  n2 : ℕ
  n3 : ℕ
  n4 : ℕ
  n5 : ℕ
  n6 : ℕ
  deriving DecidableEq

/-- Integer coefficients for the seven blocks. -/
structure Z7 where
  c0 : ℤ
  c1 : ℤ
  c2 : ℤ
  c3 : ℤ
  c4 : ℤ
  c5 : ℤ
  c6 : ℤ
  deriving DecidableEq

def C7.add (u v : C7) : C7 :=
  ⟨u.n0 + v.n0, u.n1 + v.n1, u.n2 + v.n2, u.n3 + v.n3, u.n4 + v.n4, u.n5 + v.n5, u.n6 + v.n6⟩

def unit7 : ℕ → C7
  | 0 => ⟨1, 0, 0, 0, 0, 0, 0⟩
  | 1 => ⟨0, 1, 0, 0, 0, 0, 0⟩
  | 2 => ⟨0, 0, 1, 0, 0, 0, 0⟩
  | 3 => ⟨0, 0, 0, 1, 0, 0, 0⟩
  | 4 => ⟨0, 0, 0, 0, 1, 0, 0⟩
  | 5 => ⟨0, 0, 0, 0, 0, 1, 0⟩
  | _ => ⟨0, 0, 0, 0, 0, 0, 1⟩

/-- The counts of the blocks of a list. -/
def cnt : List ℕ → C7
  | [] => ⟨0, 0, 0, 0, 0, 0, 0⟩
  | x :: s => (unit7 x).add (cnt s)

/-- The counts of tau(s) from the counts of s. -/
def mulM (v : C7) : C7 :=
  ⟨v.n0 + v.n2 + v.n4 + v.n5, v.n4 + v.n5, v.n1, v.n2 + v.n4, v.n6, v.n3, v.n5 + v.n6⟩

/-- The integer combination of the counts. -/
def dotZ (f : Z7) (v : C7) : ℤ :=
  f.c0 * v.n0 + f.c1 * v.n1 + f.c2 * v.n2 + f.c3 * v.n3 + f.c4 * v.n4 + f.c5 * v.n5 + f.c6 * v.n6

/-- The coefficients of a combination of the counts of tau(s) as a combination of those of s. -/
def trans (f : Z7) : Z7 :=
  ⟨f.c0, f.c2, f.c3 + f.c0, f.c5, f.c3 + f.c1 + f.c0, f.c6 + f.c1 + f.c0, f.c6 + f.c4⟩

lemma dotZ_add (f : Z7) (u v : C7) : dotZ f (u.add v) = dotZ f u + dotZ f v := by
  simp only [dotZ, C7.add]
  push_cast
  ring

lemma dotZ_mulM (f : Z7) (v : C7) : dotZ f (mulM v) = dotZ (trans f) v := by
  simp only [dotZ, mulM, trans]
  push_cast
  ring

lemma mulM_add (u v : C7) : mulM (u.add v) = (mulM u).add (mulM v) := by
  cases u
  cases v
  simp only [mulM, C7.add]
  congr 1 <;> ring

lemma cnt_append (u v : List ℕ) : cnt (u ++ v) = (cnt u).add (cnt v) := by
  induction u with
  | nil =>
    cases h : cnt v
    simp only [List.nil_append, cnt, C7.add, Nat.zero_add, h]
  | cons x u ih =>
    show (unit7 x).add (cnt (u ++ v)) = ((unit7 x).add (cnt u)).add (cnt v)
    rw [ih]
    cases unit7 x
    cases cnt u
    cases cnt v
    simp only [C7.add]
    congr 1 <;> ring

lemma cnt_tauT (k : ℕ) (hk : k ≤ 6) : cnt (tauT k) = mulM (unit7 k) := by
  interval_cases k <;> rfl

lemma cnt_tau (s : List ℕ) (hs : Valid s) : cnt (tau s) = mulM (cnt s) := by
  induction s with
  | nil => rfl
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    rw [tau_cons, cnt_append, cnt_tauT k hk, ih hs']
    show (mulM (unit7 k)).add (mulM (cnt s)) = mulM ((unit7 k).add (cnt s))
    rw [mulM_add]

lemma cnt_tauIter (p : ℕ) : ∀ s : List ℕ, Valid s → cnt (tau^[p] s) = mulM^[p] (cnt s) := by
  induction p with
  | zero => intro s _; rfl
  | succ p ih =>
    intro s hs
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih _ (tau_valid s),
      cnt_tau s hs]

lemma tau_valid_iter (p : ℕ) (s : List ℕ) (hs : Valid s) : Valid (tau^[p] s) := by
  cases p with
  | zero => exact hs
  | succ p =>
    rw [Function.iterate_succ_apply']
    exact tau_valid _

/-- 10000 times the number of 0s minus 10527 times the number of 1s of each block. -/
def phiZ : Z7 := ⟨-10527, -11054, -1054, 8946, -1581, 18419, 28419⟩

/-- The potential that bounds the number of blocks A. -/
def betaZ : Z7 := ⟨-1, 10, 10, 11, 20, 11, 2⟩

lemma pot_tok (k : ℕ) (hk : k ≤ 6) :
    10000 * ((tok k).count 0 : ℤ) - 10527 * ((tok k).count 1 : ℤ) = dotZ phiZ (unit7 k) := by
  interval_cases k <;> decide

lemma pot_flat (s : List ℕ) (hs : Valid s) :
    10000 * ((flat s).count 0 : ℤ) - 10527 * ((flat s).count 1 : ℤ) = dotZ phiZ (cnt s) := by
  induction s with
  | nil => simp [flat, cnt, dotZ]
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    rw [flat_cons, List.count_append, List.count_append]
    show _ = dotZ phiZ ((unit7 k).add (cnt s))
    rw [dotZ_add, ← pot_tok k hk, ← ih hs']
    push_cast
    ring

/-- The coefficients of the potential of tau^p(s) in terms of the counts of s. -/
def Fco : ℕ → Z7
  | 0 => phiZ
  | p + 1 => trans (Fco p)

lemma dot_iter (p : ℕ) : ∀ v : C7, dotZ phiZ (mulM^[p] v) = dotZ (Fco p) v := by
  induction p with
  | zero => intro v; rfl
  | succ p ih =>
    intro v
    rw [Function.iterate_succ_apply, ih, dotZ_mulM]
    rfl

lemma Fco30 : Fco 30 = ⟨-10527, 175986, 1233562, 736554, 1892327, 2452895, 1955887⟩ := by
  decide +kernel

/-- The counts of T k, computed level by level. -/
def cntT : ℕ → C7
  | 0 => cnt P
  | k + 1 => (cnt P).add (mulM (cntT k))

lemma cnt_T (k : ℕ) : cnt (T k) = cntT k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show cnt (P ++ tau (T k)) = _
    rw [cnt_append, cnt_tau _ (T_valid k), ih]
    rfl

lemma pot29 : 46311 + dotZ phiZ (cntT 29) = 4595295 := by decide +kernel

lemma T_split (k p : ℕ) : T (k + p + 1) = T p ++ tau^[p + 1] (T k) := by
  induction p with
  | zero => rfl
  | succ p ih =>
    show P ++ tau (T (k + p + 1)) = (P ++ tau (T p)) ++ tau^[p + 1 + 1] (T k)
    rw [ih, tau_append, List.append_assoc, Function.iterate_succ_apply' tau (p + 1)]

lemma dotZ_mono (f g : Z7) (v : C7) (h0 : g.c0 ≤ f.c0) (h1 : g.c1 ≤ f.c1) (h2 : g.c2 ≤ f.c2)
    (h3 : g.c3 ≤ f.c3) (h4 : g.c4 ≤ f.c4) (h5 : g.c5 ≤ f.c5) (h6 : g.c6 ≤ f.c6) :
    dotZ g v ≤ dotZ f v := by
  unfold dotZ
  have := mul_le_mul_of_nonneg_right h0 (Nat.cast_nonneg (α := ℤ) v.n0)
  have := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg (α := ℤ) v.n1)
  have := mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg (α := ℤ) v.n2)
  have := mul_le_mul_of_nonneg_right h3 (Nat.cast_nonneg (α := ℤ) v.n3)
  have := mul_le_mul_of_nonneg_right h4 (Nat.cast_nonneg (α := ℤ) v.n4)
  have := mul_le_mul_of_nonneg_right h5 (Nat.cast_nonneg (α := ℤ) v.n5)
  have := mul_le_mul_of_nonneg_right h6 (Nat.cast_nonneg (α := ℤ) v.n6)
  linarith

lemma beta_T (k : ℕ) : 0 ≤ dotZ betaZ (cntT k) := by
  induction k with
  | zero => decide
  | succ k ih =>
    show 0 ≤ dotZ betaZ ((cnt P).add (mulM (cntT k)))
    rw [dotZ_add, dotZ_mulM]
    have h1 : dotZ betaZ (cntT k) ≤ dotZ (trans betaZ) (cntT k) :=
      dotZ_mono _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)
    have h2 : dotZ betaZ (cnt P) = 30 := by decide
    linarith

/-- The potential of V k: 10000 times its number of 0s minus 10527 times its number of 1s. -/
lemma pot_V (k : ℕ) :
    10000 * ((V k).count 0 : ℤ) - 10527 * ((V k).count 1 : ℤ) = 46311 + dotZ phiZ (cntT k) := by
  unfold V
  rw [List.count_append, List.count_append, ← cnt_T]
  have h := pot_flat (T k) (T_valid k)
  have h0 : head.count 0 = 12 := by decide
  have h1 : head.count 1 = 7 := by decide
  rw [h0, h1]
  push_cast
  linarith

/-- For k >= 30 the potential of V k is positive. -/
lemma pot_pos (k : ℕ) (hk : 30 ≤ k) :
    10527 * ((V k).count 1 : ℤ) < 10000 * ((V k).count 0 : ℤ) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h := pot_V (30 + j)
  have hs : T (30 + j) = T 29 ++ tau^[30] (T j) := by
    have := T_split j 29
    rw [show j + 29 + 1 = 30 + j by ring] at this
    exact this
  have hc : cntT (30 + j) = (cntT 29).add (mulM^[30] (cntT j)) := by
    rw [← cnt_T, hs, cnt_append, cnt_T, cnt_tauIter 30 _ (T_valid j), cnt_T]
  rw [hc, dotZ_add, dot_iter, Fco30] at h
  have hb := beta_T j
  have hm : 10527 * dotZ betaZ (cntT j) ≤
      dotZ ⟨-10527, 175986, 1233562, 736554, 1892327, 2452895, 1955887⟩ (cntT j) := by
    have e : 10527 * dotZ betaZ (cntT j) = dotZ ⟨-10527, 105270, 105270, 115797, 210540, 115797,
        21054⟩ (cntT j) := by
      simp only [dotZ, betaZ]
      ring
    rw [e]
    exact dotZ_mono _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have h29 := pot29
  linarith

lemma count01 : ∀ l : List ℕ, (∀ x ∈ l, x ≤ 1) → l.count 0 + l.count 1 = l.length
  | [], _ => rfl
  | x :: l, h => by
    have hx := h x (by simp)
    have ih := count01 l (fun y hy => h y (by simp [hy]))
    interval_cases x <;> simp <;> omega

/-! ### The disproof -/

/-- Kimberling's conjecture fails: there is no m = 2.05... with a(n)/n -> m and
-1 < m - a(n)/n < 0 for n >= 1. -/
theorem disproof : ¬ (∃ m : ℝ, (2.05 ≤ m ∧ m < 2.06) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 m) ∧
    ∀ n : ℕ, 1 ≤ n → -1 < m - (a n : ℝ) / n ∧ m - (a n : ℝ) / n < 0) := by
  rintro ⟨m, -, hlim, hb⟩
  have h4676 := (hb 4676 (by norm_num)).2
  rw [a4676] at h4676
  have hq : m < 9598 / 4676 := by push_cast at h4676; linarith
  have hev : ∀ᶠ n in atTop, (a n : ℝ) / n < 9598 / 4676 := hlim.eventually (gt_mem_nhds hq)
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hev
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = N0 + 22630 := ⟨_, rfl⟩
  have hpos := pot_pos k (by omega)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = (V k).count 1 := ⟨_, rfl⟩
  rw [← hn] at hpos
  have hn1 : k + 1 ≤ n := hn ▸ V_ones k
  have hlen : (V k).count 0 + n = (V k).length := by
    rw [hn]
    exact count01 _ (V_letters k)
  have hOV : O (V k).length = n := by
    rw [(counts_eq k _ le_rfl).2, List.take_length, hn]
  have hinf := ones_infinite
  have hnth : (V k).length ≤ Nat.nth (fun i => W i = 1) n := by
    by_contra h
    rw [not_le] at h
    have h1 : Nat.count (fun i => W i = 1) (Nat.nth (fun i => W i = 1) n + 1) = n + 1 := by
      rw [Nat.count_succ, Nat.count_nth_of_infinite hinf, if_pos (Nat.nth_mem_of_infinite hinf n)]
    have h2 := Nat.count_monotone (fun i => W i = 1) (show Nat.nth (fun i => W i = 1) n + 1 ≤
      (V k).length by omega)
    have h3 : Nat.count (fun i => W i = 1) (V k).length = n := hOV
    omega
  have ha : (V k).length < a (n + 1) := by
    show (V k).length < Nat.nth (fun i => W i = 1) (n + 1 - 1) + 1
    rw [show n + 1 - 1 = n by omega]
    omega
  have hlt := hN0 (n + 1) (by omega)
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  push_cast at hlt
  rw [div_lt_iff₀ hnpos] at hlt
  have ha' : ((V k).length : ℝ) < a (n + 1) := by exact_mod_cast ha
  have hpos' : (10527 : ℝ) * n < 10000 * ((V k).count 0 : ℝ) := by exact_mod_cast hpos
  have hlen' : ((V k).count 0 : ℝ) + n = (V k).length := by exact_mod_cast hlen
  have hn1' : (22630 : ℝ) ≤ n := by
    have : 22630 ≤ n := by omega
    exact_mod_cast this
  nlinarith

end OMA.S_oeis_a289076

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a289076.main) :=
  OMA.S_oeis_a289076.disproof

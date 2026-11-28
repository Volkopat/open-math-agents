import OMAStatements.S_oeis_a288467

namespace OMA.S_oeis_a288467

open Filter Topology





/-! ### One pass -/

/-- Induction along the cases of `step`. -/
theorem step_rec {P : List ℕ → Prop} (h0 : P []) (h00 : ∀ l, P l → P (0 :: 0 :: l))
    (h1 : ∀ l, P l → P (1 :: l)) (hz : P [0])
    (hzy : ∀ y l, P ((y + 1) :: l) → P (0 :: (y + 1) :: l))
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
          · rcases y with _ | y
            · exact h00 l (ih l (by simp at hu; omega))
            · exact hzy y l (ih _ (by simpa using hu))
        · exact h1 l (ih l (by omega))
        · exact hx x l (ih l (by omega))
  exact fun u => key u.length u le_rfl

lemma step_zero_cons (t : List ℕ) : ∃ r, step (0 :: t) = 0 :: r := by
  rcases t with _ | ⟨y, t⟩
  · exact ⟨[], rfl⟩
  · rcases y with _ | _ | y
    · exact ⟨1 :: 0 :: 1 :: step t, rfl⟩
    · exact ⟨step (1 :: t), rfl⟩
    · exact ⟨step ((y + 2) :: t), rfl⟩

/-- A pass maps a prefix of a word to a prefix of its image: a lone final 0 is copied, and
00 -> 0101 begins with 0. -/
lemma step_mono (u : List ℕ) : ∀ t, step u <+: step (u ++ t) := by
  refine step_rec (P := fun u => ∀ t, step u <+: step (u ++ t)) ?_ ?_ ?_ ?_ ?_ ?_ u
  · intro t
    exact List.nil_prefix
  · intro l ih t
    obtain ⟨r, hr⟩ := ih t
    exact ⟨r, by
      show 0 :: 1 :: 0 :: 1 :: (step l ++ r) = 0 :: 1 :: 0 :: 1 :: step (l ++ t)
      rw [hr]⟩
  · intro l ih t
    obtain ⟨r, hr⟩ := ih t
    exact ⟨r, by
      show 0 :: 1 :: 0 :: (step l ++ r) = 0 :: 1 :: 0 :: step (l ++ t)
      rw [hr]⟩
  · intro t
    obtain ⟨r, hr⟩ := step_zero_cons t
    exact ⟨r, by
      show 0 :: r = step (0 :: t)
      rw [hr]⟩
  · intro y l ih t
    obtain ⟨r, hr⟩ := ih t
    exact ⟨r, by
      show 0 :: (step ((y + 1) :: l) ++ r) = 0 :: step ((y + 1) :: l ++ t)
      rw [hr]⟩
  · intro x l ih t
    obtain ⟨r, hr⟩ := ih t
    exact ⟨r, by
      show (x + 2) :: (step l ++ r) = (x + 2) :: step (l ++ t)
      rw [hr]⟩

lemma step_prefix {u v : List ℕ} (h : u <+: v) : step u <+: step v := by
  obtain ⟨t, rfl⟩ := h
  exact step_mono u t

/-- The rule 1 -> 010 reads its letter alone, so the pass restarts at every letter 1. -/
lemma step_cut (u : List ℕ) : ∀ w, step (u ++ 1 :: w) = step u ++ step (1 :: w) := by
  refine step_rec (P := fun u => ∀ w, step (u ++ 1 :: w) = step u ++ step (1 :: w))
    ?_ ?_ ?_ ?_ ?_ ?_ u
  · intro w
    rfl
  · intro l ih w
    show 0 :: 1 :: 0 :: 1 :: step (l ++ 1 :: w) = 0 :: 1 :: 0 :: 1 :: step l ++ step (1 :: w)
    rw [ih]
    rfl
  · intro l ih w
    show 0 :: 1 :: 0 :: step (l ++ 1 :: w) = 0 :: 1 :: 0 :: step l ++ step (1 :: w)
    rw [ih]
    rfl
  · intro w
    rfl
  · intro y l ih w
    show 0 :: step ((y + 1) :: l ++ 1 :: w) = 0 :: step ((y + 1) :: l) ++ step (1 :: w)
    rw [ih]
    rfl
  · intro x l ih w
    show (x + 2) :: step (l ++ 1 :: w) = (x + 2) :: step l ++ step (1 :: w)
    rw [ih]
    rfl

/-- A pass does not shorten a word. -/
lemma step_length (u : List ℕ) : u.length ≤ (step u).length := by
  refine step_rec (P := fun u => u.length ≤ (step u).length) ?_ ?_ ?_ ?_ ?_ ?_ u
  · exact le_rfl
  · intro l ih
    show l.length + 2 ≤ (step l).length + 4
    omega
  · intro l ih
    show l.length + 1 ≤ (step l).length + 3
    omega
  · exact le_rfl
  · intro y l ih
    show ((y + 1) :: l).length + 1 ≤ (step ((y + 1) :: l)).length + 1
    omega
  · intro x l ih
    show l.length + 1 ≤ (step l).length + 1
    omega

/-! ### Blocks -/

/-- The blocks T0 = 10, T1 = 100, T2 = 1000. -/
def tok : ℕ → List ℕ
  | 0 => [1, 0]
  | 1 => [1, 0, 0]
  | _ => [1, 0, 0, 0]

/-- All blocks are 0, 1 or 2. -/
def Valid (s : List ℕ) : Prop := ∀ k ∈ s, k ≤ 2

/-- The word of a list of blocks. -/
def flat (s : List ℕ) : List ℕ := s.flatMap tok

/-- The shifted images of the blocks: the pass over a block followed by 0 is 0 followed by the
word of T0 -> T2, T1 -> T1 T0 T0, T2 -> T1 T0 T1. -/
def tauT : ℕ → List ℕ
  | 0 => [2]
  | 1 => [1, 0, 0]
  | _ => [1, 0, 1]

/-- The block morphism. -/
def tau (s : List ℕ) : List ℕ := s.flatMap tauT

lemma flat_cons (k : ℕ) (s : List ℕ) : flat (k :: s) = tok k ++ flat s := by
  simp [flat]

lemma flat_append (u v : List ℕ) : flat (u ++ v) = flat u ++ flat v := by
  simp [flat]

lemma tau_cons (k : ℕ) (s : List ℕ) : tau (k :: s) = tauT k ++ tau s := by
  simp [tau]

lemma tau_append (u v : List ℕ) : tau (u ++ v) = tau u ++ tau v := by
  simp [tau]

lemma tau_single (k : ℕ) : tau [k] = tauT k := by
  simp [tau]

lemma tauT_valid (k : ℕ) : Valid (tauT k) := by
  intro x hx
  rcases k with _ | _ | k <;> simp [tauT] at hx <;> omega

lemma tau_valid (s : List ℕ) : Valid (tau s) := by
  intro x hx
  simp only [tau, List.mem_flatMap] at hx
  obtain ⟨k, -, hk⟩ := hx
  exact tauT_valid k x hk

lemma valid_cons {k : ℕ} {s : List ℕ} (h : Valid (k :: s)) : k ≤ 2 ∧ Valid s :=
  ⟨h k (by simp), fun x hx => h x (by simp [hx])⟩

lemma valid_single {x : ℕ} (hx : x ≤ 2) : Valid [x] := by
  intro y hy
  simp at hy
  omega

lemma valid00 : Valid [0, 0] := by
  intro y hy
  simp at hy
  omega

lemma tok_head (k : ℕ) : ∃ r, tok k = 1 :: r := by
  rcases k with _ | _ | k <;> exact ⟨_, rfl⟩

lemma step_append_flat (u s : List ℕ) : step (u ++ flat s) = step u ++ step (flat s) := by
  rcases s with _ | ⟨j, s⟩
  · rw [show flat [] = [] from rfl, List.append_nil, show step [] = [] from rfl,
      List.append_nil]
  · obtain ⟨r, hr⟩ := tok_head j
    rw [flat_cons, hr, List.cons_append, step_cut]

/-- The pass over a block, followed by 0, is 0 followed by the word of its shifted image. -/
lemma step_tok (k : ℕ) (hk : k ≤ 2) : step (tok k) ++ [0] = [0] ++ flat (tauT k) := by
  interval_cases k <;> rfl

lemma step_flat (s : List ℕ) (hs : Valid s) : step (flat s) ++ [0] = [0] ++ flat (tau s) := by
  induction s with
  | nil => rfl
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    rw [flat_cons, step_append_flat, List.append_assoc, ih hs', ← List.append_assoc,
      step_tok k hk, tau_cons, flat_append, List.append_assoc]

lemma tauIter_append (n : ℕ) (u v : List ℕ) : tau^[n] (u ++ v) = tau^[n] u ++ tau^[n] v := by
  induction n generalizing u v with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      Function.iterate_succ_apply, tau_append, ih]

lemma tauIter_valid (n : ℕ) (s : List ℕ) (hs : Valid s) : Valid (tau^[n] s) := by
  cases n with
  | zero => exact hs
  | succ n =>
    rw [Function.iterate_succ_apply']
    exact tau_valid _

lemma tau_length_ge (s : List ℕ) : s.length ≤ (tau s).length := by
  induction s with
  | nil => simp [tau]
  | cons k s ih =>
    rw [tau_cons, List.length_append, List.length_cons]
    have : 1 ≤ (tauT k).length := by rcases k with _ | _ | k <;> simp [tauT]
    omega

lemma tauIter_length_ge (n : ℕ) (s : List ℕ) : s.length ≤ (tau^[n] s).length := by
  induction n generalizing s with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact (tau_length_ge s).trans (ih _)

lemma flat_length_ge (s : List ℕ) (hs : Valid s) : s.length ≤ (flat s).length := by
  induction s with
  | nil => simp [flat]
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    rw [flat_cons, List.length_append, List.length_cons]
    have := ih hs'
    interval_cases k <;> simp [tok] <;> omega

lemma flat_letters (s : List ℕ) : ∀ x ∈ flat s, x ≤ 1 := by
  intro x hx
  simp only [flat, List.mem_flatMap] at hx
  obtain ⟨k, -, hk⟩ := hx
  rcases k with _ | _ | k <;> simp [tok] at hk <;> omega

/-! ### The odd iterates -/

/-- S k: the blocks T0 T0 tau^2(T0 T0) ... tau^(2k)(T0 T0). -/
def S : ℕ → List ℕ
  | 0 => [0, 0]
  | k + 1 => 0 :: 0 :: tau (tau (S k))

lemma S_valid (k : ℕ) : Valid (S k) := by
  induction k with
  | zero => exact valid00
  | succ k ih =>
    intro y hy
    simp only [S, List.mem_cons] at hy
    rcases hy with rfl | rfl | hy
    · norm_num
    · norm_num
    · exact tau_valid _ y hy

lemma S_head (k : ℕ) : ∃ r, S k = 0 :: r := by
  cases k with
  | zero => exact ⟨[0], rfl⟩
  | succ k => exact ⟨0 :: tau (tau (S k)), rfl⟩

lemma S_succ' (k : ℕ) : S (k + 1) = S k ++ tau^[2 * (k + 1)] [0, 0] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    calc S (k + 1 + 1) = 0 :: 0 :: tau (tau (S k ++ tau^[2 * (k + 1)] [0, 0])) := by
          rw [← ih]; rfl
      _ = (0 :: 0 :: tau (tau (S k))) ++ tau^[2 * (k + 1 + 1)] [0, 0] := by
        rw [tau_append, tau_append, show 2 * (k + 1 + 1) = 2 * (k + 1) + 1 + 1 by ring,
          Function.iterate_succ_apply', Function.iterate_succ_apply', List.cons_append,
          List.cons_append]
      _ = S (k + 1) ++ tau^[2 * (k + 1 + 1)] [0, 0] := rfl

/-- V k: the letter 0 followed by the word of S k. -/
def V (k : ℕ) : List ℕ := 0 :: flat (S k)

lemma V_succ' (k : ℕ) : V (k + 1) = V k ++ flat (tau^[2 * (k + 1)] [0, 0]) := by
  unfold V
  rw [S_succ', flat_append, List.cons_append]

lemma step_V (k : ℕ) : step (V k) ++ [0] = 0 :: 0 :: flat (tau (S k)) := by
  obtain ⟨r, hr⟩ := S_head k
  have e : step (V k) = 0 :: step (flat (S k)) := by
    unfold V
    rw [hr, flat_cons]
    rfl
  rw [e]
  show 0 :: (step (flat (S k)) ++ [0]) = 0 :: 0 :: flat (tau (S k))
  rw [step_flat _ (S_valid k)]
  rfl

/-- Two passes map V k to a prefix of V (k + 1). -/
lemma step_step_V (k : ℕ) : step (step (V k)) <+: V (k + 1) := by
  have h1 : step (step (V k)) <+: step (step (V k) ++ [0]) := step_mono _ _
  rw [step_V] at h1
  have h2 : step (0 :: 0 :: flat (tau (S k))) = 0 :: 1 :: 0 :: 1 :: step (flat (tau (S k))) := rfl
  rw [h2] at h1
  refine h1.trans ⟨[0], ?_⟩
  have h3 := step_flat (tau (S k)) (tau_valid _)
  show 0 :: 1 :: 0 :: 1 :: (step (flat (tau (S k))) ++ [0]) = V (k + 1)
  rw [h3]
  rfl

/-- Iterate 2k + 1 is a prefix of V k. -/
lemma iter_odd_prefix (k : ℕ) : iter (2 * k + 1) <+: V k := by
  induction k with
  | zero => exact ⟨[0], rfl⟩
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring]
    exact (step_prefix (step_prefix ih)).trans (step_step_V k)

lemma V_prefix_succ (k : ℕ) : V k <+: V (k + 1) := by
  rw [V_succ']
  exact List.prefix_append _ _

lemma V_prefix {k k' : ℕ} (h : k ≤ k') : V k <+: V k' := by
  induction k', h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ k' _ ih => exact ih.trans (V_prefix_succ k')

lemma V_length (k : ℕ) : 2 * k + 5 ≤ (V k).length := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [V_succ', List.length_append]
    have h2 := flat_length_ge (tau^[2 * (k + 1)] [0, 0]) (tauIter_valid _ _ valid00)
    have h3 := tauIter_length_ge (2 * (k + 1)) [0, 0]
    simp only [List.length_cons, List.length_nil] at h3
    omega

/-- The even iterates start with 00 and the odd ones with 01. -/
lemma iter_head (n : ℕ) : ∃ l, iter n = 0 :: n % 2 :: l := by
  induction n with
  | zero => exact ⟨[], rfl⟩
  | succ n ih =>
    obtain ⟨l, hl⟩ := ih
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · rw [h] at hl
      have e : (n + 1) % 2 = 1 := by omega
      exact ⟨0 :: 1 :: step l, by rw [e, show iter (n + 1) = step (iter n) from rfl, hl]; rfl⟩
    · rw [h] at hl
      have e : (n + 1) % 2 = 0 := by omega
      exact ⟨1 :: 0 :: step l, by rw [e, show iter (n + 1) = step (iter n) from rfl, hl]; rfl⟩

lemma iter_length (n : ℕ) : n + 2 ≤ (iter n).length := by
  induction n with
  | zero => decide
  | succ n ih =>
    obtain ⟨l, hl⟩ := iter_head n
    rw [show iter (n + 1) = step (iter n) from rfl, hl]
    rw [hl] at ih
    have := step_length l
    simp only [List.length_cons] at ih
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · rw [h]
      show n + 1 + 2 ≤ (step l).length + 4
      omega
    · rw [h]
      show n + 1 + 2 ≤ (step l).length + 4
      omega

lemma getD_prefix {l₁ l₂ : List ℕ} (h : l₁ <+: l₂) {i : ℕ} (hi : i < l₁.length) :
    l₁.getD i 0 = l₂.getD i 0 := by
  obtain ⟨s, rfl⟩ := h
  rw [List.getD_append _ _ _ _ hi]

lemma W_eq (k i : ℕ) (hi : i < (V k).length) : W i = (V k).getD i 0 := by
  have hl : i < (iter (2 * (i + 1) + 1)).length := by
    have := iter_length (2 * (i + 1) + 1)
    omega
  have hp := iter_odd_prefix (i + 1)
  have hl' : i < (V (i + 1)).length := lt_of_lt_of_le hl hp.length_le
  unfold W
  rw [getD_prefix hp hl]
  rcases le_total (i + 1) k with h | h
  · exact getD_prefix (V_prefix h) hl'
  · exact (getD_prefix (V_prefix h) hi).symm

/-- Letter i is the same in every iterate 2k + 1 with k >= i. -/
lemma W_odd (k i : ℕ) (hk : i ≤ k) : W i = (iter (2 * k + 1)).getD i 0 := by
  have hl : i < (iter (2 * k + 1)).length := by
    have := iter_length (2 * k + 1)
    omega
  have hp := iter_odd_prefix k
  rw [getD_prefix hp hl]
  exact W_eq k i (lt_of_lt_of_le hl hp.length_le)

/-! ### The roots -/

lemma lam_exists : ∃ x : ℝ, 2.130395 ≤ x ∧ x ≤ 2.130396 ∧ x ^ 3 - x ^ 2 - x - 3 = 0 := by
  have hc : ContinuousOn (fun x : ℝ => x ^ 3 - x ^ 2 - x - 3) (Set.Icc 2.130395 2.130396) := by
    fun_prop
  have h := intermediate_value_Icc (show (2.130395 : ℝ) ≤ 2.130396 by norm_num) hc
  have h0 : (0 : ℝ) ∈ Set.Icc ((fun x : ℝ => x ^ 3 - x ^ 2 - x - 3) 2.130395)
      ((fun x : ℝ => x ^ 3 - x ^ 2 - x - 3) 2.130396) := by
    constructor <;> norm_num
  obtain ⟨x, ⟨hx1, hx2⟩, hx⟩ := h h0
  exact ⟨x, hx1, hx2, hx⟩

/-- The Perron root, 2.13039..., the growth rate of the iterates. -/
noncomputable def lam : ℝ := Classical.choose lam_exists

lemma lam_spec : 2.130395 ≤ lam ∧ lam ≤ 2.130396 ∧ lam ^ 3 - lam ^ 2 - lam - 3 = 0 :=
  Classical.choose_spec lam_exists

/-- The limiting number of letters 0 per letter 1, (lam^2 - 1)/2 = 1.76929... -/
noncomputable def cc : ℝ := (lam ^ 2 - 1) / 2

lemma cc_bounds : 1.769291 ≤ cc ∧ cc ≤ 1.769294 := by
  obtain ⟨h1, h2, -⟩ := lam_spec
  unfold cc
  constructor <;> nlinarith

/-- The coefficients of the quadratic factor x^2 + p x + q of x^3 - x^2 - x - 3. -/
noncomputable def pp : ℝ := lam - 1

noncomputable def qq : ℝ := lam ^ 2 - lam - 1

lemma pq_bounds : 1.130395 ≤ pp ∧ pp ≤ 1.130396 ∧ 1.408186 ≤ qq ∧ qq ≤ 1.408193 := by
  obtain ⟨h1, h2, -⟩ := lam_spec
  unfold pp qq
  refine ⟨by linarith, by linarith, by nlinarith, by nlinarith⟩

/-! ### Deviation of words and block lists -/

/-- For a word, the number of letters 0 minus c times the number of letters 1. -/
noncomputable def gL (L : List ℕ) : ℝ := (L.count 0 : ℝ) - cc * (L.count 1 : ℝ)

lemma gL_append (u v : List ℕ) : gL (u ++ v) = gL u + gL v := by
  simp only [gL, List.count_append]
  push_cast
  ring

lemma gL_eq (L : List ℕ) (z o : ℕ) (hz : L.count 0 = z) (ho : L.count 1 = o) :
    gL L = z - cc * o := by
  unfold gL
  rw [hz, ho]

/-- The deviation of a block list: the deviation of its word. -/
noncomputable def g (s : List ℕ) : ℝ := gL (flat s)

lemma g_append (u v : List ℕ) : g (u ++ v) = g u + g v := by
  unfold g
  rw [flat_append, gL_append]

lemma g_eq (s : List ℕ) (z o : ℕ) (hz : (flat s).count 0 = z) (ho : (flat s).count 1 = o) :
    g s = z - cc * o :=
  gL_eq (flat s) z o hz ho

lemma g_tok (k : ℕ) (hk : k ≤ 2) :
    g (tau (tau [k])) + pp * g (tau [k]) + qq * g [k] = 0 := by
  obtain ⟨-, -, hf⟩ := lam_spec
  interval_cases k
  · rw [g_eq _ 5 3 (by decide) (by decide), g_eq _ 3 1 (by decide) (by decide),
      g_eq _ 1 1 (by decide) (by decide)]
    unfold cc pp qq
    push_cast
    linear_combination (-1 / 2 - lam / 2) * hf
  · rw [g_eq _ 10 5 (by decide) (by decide), g_eq _ 4 3 (by decide) (by decide),
      g_eq _ 2 1 (by decide) (by decide)]
    unfold cc pp qq
    push_cast
    linear_combination (-3 / 2 - lam / 2) * hf
  · rw [g_eq _ 11 7 (by decide) (by decide), g_eq _ 5 3 (by decide) (by decide),
      g_eq _ 3 1 (by decide) (by decide)]
    unfold cc pp qq
    push_cast
    linear_combination (-3 / 2 - lam / 2) * hf

/-- The deviation has no component along the Perron root: it follows x^2 + p x + q. -/
lemma g_rec (s : List ℕ) (hs : Valid s) :
    g (tau (tau s)) + pp * g (tau s) + qq * g s = 0 := by
  induction s with
  | nil => simp [g, gL, flat, tau]
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    rw [show k :: s = [k] ++ s from rfl, tau_append, tau_append, g_append, g_append, g_append]
    linarith [g_tok k hk, ih hs']

/-! ### The quadratic form -/

/-- u x j: the deviation of tau^j(x). -/
noncomputable def u (x j : ℕ) : ℝ := g (tau^[j] [x])

lemma u_rec (x j : ℕ) (hx : x ≤ 2) : u x (j + 2) = -pp * u x (j + 1) - qq * u x j := by
  have hv : Valid (tau^[j] [x]) := tauIter_valid j _ (valid_single hx)
  have e2 : tau^[j + 2] [x] = tau (tau (tau^[j] [x])) := by
    rw [show j + 2 = j + 1 + 1 from rfl, Function.iterate_succ_apply',
      Function.iterate_succ_apply']
  have e1 : tau^[j + 1] [x] = tau (tau^[j] [x]) := Function.iterate_succ_apply' _ _ _
  have h := g_rec _ hv
  unfold u
  rw [e2, e1]
  linarith

/-- The quadratic form along the deviations. -/
noncomputable def E (x j : ℕ) : ℝ := u x (j + 1) ^ 2 + pp * u x (j + 1) * u x j + qq * u x j ^ 2

lemma E_succ (x j : ℕ) (hx : x ≤ 2) : E x (j + 1) = qq * E x j := by
  unfold E
  rw [show j + 1 + 1 = j + 2 from rfl, u_rec x j hx]
  ring

/-- The form is positive definite: it bounds the square of its second argument. -/
lemma E_ge (x j : ℕ) : 1.088 * u x j ^ 2 ≤ E x j := by
  obtain ⟨hp1, hp2, hq1, hq2⟩ := pq_bounds
  unfold E
  have h : u x (j + 1) ^ 2 + pp * u x (j + 1) * u x j + qq * u x j ^ 2 =
      (u x (j + 1) + pp / 2 * u x j) ^ 2 + (qq - pp ^ 2 / 4) * u x j ^ 2 := by ring
  rw [h]
  have h2 : 1.088 ≤ qq - pp ^ 2 / 4 := by nlinarith
  have h3 : 0 ≤ u x j ^ 2 := sq_nonneg _
  nlinarith [sq_nonneg (u x (j + 1) + pp / 2 * u x j)]

lemma E_nonneg (x j : ℕ) : 0 ≤ E x j := by
  have := E_ge x j
  have h3 : 0 ≤ u x j ^ 2 := sq_nonneg _
  linarith

/-- The bound for the form at j = 0. -/
noncomputable def E0 : ℕ → ℝ
  | 0 => 1.28
  | 1 => 1.45
  | _ => 1.8

lemma E_zero (x : ℕ) (hx : x ≤ 2) : E x 0 ≤ E0 x := by
  obtain ⟨h1, h2, hf⟩ := lam_spec
  have e : ∀ y, E y 0 = g (tau [y]) ^ 2 + pp * g (tau [y]) * g [y] + qq * g [y] ^ 2 :=
    fun y => rfl
  interval_cases x
  · have hE : E 0 0 = 1 - 2 * lam + lam ^ 2 := by
      rw [e 0, g_eq _ 3 1 (by decide) (by decide), g_eq _ 1 1 (by decide) (by decide)]
      unfold cc pp qq
      push_cast
      linear_combination (-5 / 4 - 5 / 4 * lam + 1 / 4 * lam ^ 2 + 1 / 4 * lam ^ 3) * hf
    rw [hE]
    show 1 - 2 * lam + lam ^ 2 ≤ 1.28
    nlinarith
  · have hE : E 1 0 = 2 + 4 * lam - 2 * lam ^ 2 := by
      rw [e 1, g_eq _ 4 3 (by decide) (by decide), g_eq _ 2 1 (by decide) (by decide)]
      unfold cc pp qq
      push_cast
      linear_combination (-11 / 4 - 1 / 4 * lam + 3 / 4 * lam ^ 2 + 1 / 4 * lam ^ 3) * hf
    rw [hE]
    show 2 + 4 * lam - 2 * lam ^ 2 ≤ 1.45
    nlinarith
  · have hE : E 2 0 = -7 + 2 * lam + lam ^ 2 := by
      rw [e 2, g_eq _ 5 3 (by decide) (by decide), g_eq _ 3 1 (by decide) (by decide)]
      unfold cc pp qq
      push_cast
      linear_combination (-19 / 4 - 5 / 4 * lam + 3 / 4 * lam ^ 2 + 1 / 4 * lam ^ 3) * hf
    rw [hE]
    show -7 + 2 * lam + lam ^ 2 ≤ 1.8
    nlinarith

lemma E0_nonneg (x : ℕ) : 0 ≤ E0 x := by
  rcases x with _ | _ | x <;> simp [E0] <;> norm_num

lemma E_le (x j : ℕ) (hx : x ≤ 2) : E x j ≤ E0 x * 1.4161 ^ j := by
  obtain ⟨hp1, hp2, hq1, hq2⟩ := pq_bounds
  induction j with
  | zero => simpa using E_zero x hx
  | succ j ih =>
    rw [E_succ x j hx, pow_succ]
    have h0 := E_nonneg x j
    have hE0 := E0_nonneg x
    have hp : 0 ≤ (1.4161 : ℝ) ^ j := by positivity
    nlinarith

/-- The coefficient of the bound for block x. -/
noncomputable def Cx : ℕ → ℝ
  | 0 => 1.09
  | 1 => 1.16
  | _ => 1.29

lemma Cx_nonneg (x : ℕ) : 0 ≤ Cx x := by
  rcases x with _ | _ | x <;> simp [Cx] <;> norm_num

lemma E0_le (x : ℕ) : E0 x ≤ 1.088 * Cx x ^ 2 := by
  rcases x with _ | _ | x <;> simp [E0, Cx] <;> norm_num

lemma u_bound (x j : ℕ) (hx : x ≤ 2) : |u x j| ≤ Cx x * 1.19 ^ j := by
  have hC := Cx_nonneg x
  apply abs_le_of_sq_le_sq _ (by positivity)
  have h1 := E_ge x j
  have h2 := E_le x j hx
  have h3 := E0_le x
  have e : (Cx x * (1.19 : ℝ) ^ j) ^ 2 = Cx x ^ 2 * 1.4161 ^ j := by
    rw [mul_pow, ← pow_mul, mul_comm j 2, pow_mul]
    norm_num
  rw [e]
  have hp : 0 ≤ (1.4161 : ℝ) ^ j := by positivity
  nlinarith

/-! ### Prefixes of block lists -/

lemma take_append_le (A B : List ℕ) (bA bB : ℝ) (hA : ∀ i, |g (A.take i)| ≤ bA)
    (hB : ∀ i, |g (B.take i)| ≤ bB) (i : ℕ) : |g ((A ++ B).take i)| ≤ max bA (|g A| + bB) := by
  rw [List.take_append]
  rcases le_or_gt i A.length with h | h
  · rw [show i - A.length = 0 by omega, List.take_zero, List.append_nil]
    exact le_trans (hA i) (le_max_left _ _)
  · rw [List.take_of_length_le h.le, g_append]
    have h1 := hB (i - A.length)
    have h2 := abs_add_le (g A) (g (B.take (i - A.length)))
    exact le_trans (by linarith) (le_max_right _ _)

/-- The bound for |g| over the prefixes of tau^J(x). -/
noncomputable def PB (J : ℕ) : ℝ := 11.85 * 1.19 ^ J - 10.61

lemma PB_ge (J : ℕ) : 1.24 ≤ PB J := by
  have h1 : (1 : ℝ) ≤ 1.19 ^ J := one_le_pow₀ (by norm_num)
  unfold PB
  linarith

lemma gtok_bound (x : ℕ) (hx : x ≤ 2) : |g [x]| ≤ 1.24 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  interval_cases x
  · rw [g_eq [0] 1 1 (by decide) (by decide), abs_le]; constructor <;> norm_num <;> linarith
  · rw [g_eq [1] 2 1 (by decide) (by decide), abs_le]; constructor <;> norm_num <;> linarith
  · rw [g_eq [2] 3 1 (by decide) (by decide), abs_le]; constructor <;> norm_num <;> linarith

/-- |g| over the prefixes of tau^J(x). -/
lemma prefix_bound (J : ℕ) : ∀ x, x ≤ 2 → ∀ i, |g ((tau^[J] [x]).take i)| ≤ PB J := by
  induction J with
  | zero =>
    intro x hx i
    simp only [Function.iterate_zero, id]
    have h0 : PB 0 = 1.24 := by norm_num [PB]
    rw [h0]
    rcases i with _ | i
    · norm_num [g, flat, gL]
    · rw [show [x].take (i + 1) = [x] by simp]
      exact gtok_bound x hx
  | succ J ih =>
    intro x hx i
    rw [Function.iterate_succ_apply, tau_single]
    have hp : 0 ≤ (1.19 : ℝ) ^ J := by positivity
    have hPB : PB J ≤ PB (J + 1) := by
      unfold PB
      rw [pow_succ]
      nlinarith
    have hu0 := u_bound 0 J (by norm_num)
    have hu1 := u_bound 1 J (by norm_num)
    have hsum : |u 1 J| + |u 0 J| + PB J ≤ PB (J + 1) := by
      simp only [Cx] at hu0 hu1
      unfold PB
      rw [pow_succ]
      nlinarith
    have ha0 := abs_nonneg (u 0 J)
    have ha1 := abs_nonneg (u 1 J)
    have hP0 := ih 0 (by norm_num)
    have hP1 := ih 1 (by norm_num)
    have hP2 := ih 2 (by norm_num)
    interval_cases x
    · exact le_trans (hP2 i) hPB
    · have e : tau^[J] (tauT 1) = tau^[J] [1] ++ (tau^[J] [0] ++ tau^[J] [0]) := by
        rw [show tauT 1 = [1] ++ ([0] ++ [0]) from rfl, tauIter_append, tauIter_append]
      rw [e]
      have h1 : ∀ i, |g ((tau^[J] [0] ++ tau^[J] [0]).take i)| ≤ |u 0 J| + PB J := by
        intro i
        refine le_trans (take_append_le _ _ _ _ hP0 hP0 i) (max_le ?_ le_rfl)
        linarith
      refine le_trans (take_append_le _ _ _ _ hP1 h1 i) (max_le ?_ ?_)
      · linarith
      · show |u 1 J| + (|u 0 J| + PB J) ≤ PB (J + 1)
        linarith
    · have e : tau^[J] (tauT 2) = tau^[J] [1] ++ (tau^[J] [0] ++ tau^[J] [1]) := by
        rw [show tauT 2 = [1] ++ ([0] ++ [1]) from rfl, tauIter_append, tauIter_append]
      rw [e]
      have h1 : ∀ i, |g ((tau^[J] [0] ++ tau^[J] [1]).take i)| ≤ |u 0 J| + PB J := by
        intro i
        refine le_trans (take_append_le _ _ _ _ hP0 hP1 i) (max_le ?_ le_rfl)
        linarith
      refine le_trans (take_append_le _ _ _ _ hP1 h1 i) (max_le ?_ ?_)
      · linarith
      · show |u 1 J| + (|u 0 J| + PB J) ≤ PB (J + 1)
        linarith

lemma g_pair (n : ℕ) : g (tau^[n] [0, 0]) = 2 * u 0 n := by
  rw [show ([0, 0] : List ℕ) = [0] ++ [0] from rfl, tauIter_append, g_append]
  unfold u
  ring

lemma pow_two_mul (J : ℕ) : (1.19 : ℝ) ^ (2 * J) = 1.4161 ^ J := by
  rw [pow_mul]
  norm_num

/-- The deviation of S J, the sum of the deviations of the blocks tau^(2j)(T0 T0), j <= J. -/
lemma S_dev (J : ℕ) : |g (S J)| ≤ 7.43 * 1.4161 ^ J - 5.89 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  induction J with
  | zero =>
    rw [show S 0 = [0, 0] from rfl, g_eq [0, 0] 2 2 (by decide) (by decide), abs_le]
    constructor <;> norm_num <;> linarith
  | succ J ih =>
    rw [S_succ', g_append, g_pair]
    have hu := u_bound 0 (2 * (J + 1)) (by norm_num)
    rw [pow_two_mul] at hu
    simp only [Cx] at hu
    have h := abs_add_le (g (S J)) (2 * u 0 (2 * (J + 1)))
    have h2 : |2 * u 0 (2 * (J + 1))| = 2 * |u 0 (2 * (J + 1))| := by
      rw [abs_mul]
      norm_num
    have hp : 0 ≤ (1.4161 : ℝ) ^ J := by positivity
    rw [pow_succ] at hu ⊢
    nlinarith

/-! ### Letters -/

lemma gL_tok_take (k : ℕ) (hk : k ≤ 2) (r : ℕ) : |gL ((tok k).take r)| ≤ 3 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hz : ((tok k).take r).count 0 ≤ 3 := by
    calc ((tok k).take r).count 0 ≤ (tok k).count 0 :=
          List.Sublist.count_le _ (List.take_sublist _ _)
      _ ≤ 3 := by interval_cases k <;> decide
  have ho : ((tok k).take r).count 1 ≤ 1 := by
    calc ((tok k).take r).count 1 ≤ (tok k).count 1 :=
          List.Sublist.count_le _ (List.take_sublist _ _)
      _ ≤ 1 := by interval_cases k <;> decide
  have hz' : (((tok k).take r).count 0 : ℝ) ≤ 3 := by exact_mod_cast hz
  have ho' : (((tok k).take r).count 1 : ℝ) ≤ 1 := by exact_mod_cast ho
  have hz0 : (0 : ℝ) ≤ ((tok k).take r).count 0 := Nat.cast_nonneg _
  have ho0 : (0 : ℝ) ≤ ((tok k).take r).count 1 := Nat.cast_nonneg _
  unfold gL
  rw [abs_le]
  constructor <;> nlinarith

lemma flat_split : ∀ S : List ℕ, Valid S → ∀ t,
    ∃ i, |gL ((flat S).take t) - g (S.take i)| ≤ 3 := by
  intro S
  induction S with
  | nil =>
    intro _ t
    refine ⟨0, ?_⟩
    norm_num [flat, g, gL]
  | cons k S ih =>
    intro hv t
    obtain ⟨hk, hv'⟩ := valid_cons hv
    rw [flat_cons]
    rcases le_or_gt t (tok k).length with h | h
    · refine ⟨0, ?_⟩
      rw [List.take_append_of_le_length h]
      simpa [g, flat, gL] using gL_tok_take k hk t
    · obtain ⟨i, hi⟩ := ih hv' (t - (tok k).length)
      refine ⟨i + 1, ?_⟩
      rw [List.take_append, List.take_of_length_le h.le, gL_append,
        show (k :: S).take (i + 1) = [k] ++ S.take i from rfl, g_append]
      have e : g [k] = gL (tok k) := by simp [g, flat]
      rw [e]
      have : gL (tok k) + gL ((flat S).take (t - (tok k).length)) - (gL (tok k) + g (S.take i)) =
          gL ((flat S).take (t - (tok k).length)) - g (S.take i) := by ring
      rw [this]
      exact hi

/-! ### The length of the words V k -/

/-- The Perron weight of a block: 1, c, lam. -/
noncomputable def wt : ℕ → ℝ
  | 0 => 1
  | 1 => cc
  | _ => lam

/-- The weight of a block list; tau multiplies it by lam. -/
noncomputable def Phi (s : List ℕ) : ℝ := (s.map wt).sum

lemma Phi_append (u v : List ℕ) : Phi (u ++ v) = Phi u + Phi v := by
  simp [Phi]

lemma Phi_tau (s : List ℕ) (hs : Valid s) : Phi (tau s) = lam * Phi s := by
  obtain ⟨-, -, hf⟩ := lam_spec
  induction s with
  | nil => simp [Phi, tau]
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    rw [tau_cons, Phi_append, ih hs', show k :: s = [k] ++ s from rfl, Phi_append, mul_add]
    congr 1
    interval_cases k <;> simp [Phi, tauT, wt, cc] <;>
      first | ring1 | linear_combination (-1 / 2 : ℝ) * hf

lemma Phi_iter (n : ℕ) : Phi (tau^[n] [0, 0]) = 2 * lam ^ n := by
  induction n with
  | zero => norm_num [Phi, wt]
  | succ n ih =>
    rw [Function.iterate_succ_apply', Phi_tau _ (tauIter_valid n _ valid00), ih, pow_succ]
    ring

lemma length_ge_Phi (s : List ℕ) (hs : Valid s) : 1.69 * Phi s ≤ ((flat s).length : ℝ) := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  obtain ⟨hc1, hc2⟩ := cc_bounds
  induction s with
  | nil => simp [Phi, flat]
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    rw [flat_cons, List.length_append, show k :: s = [k] ++ s from rfl, Phi_append]
    push_cast
    have := ih hs'
    have hk' : 1.69 * Phi [k] ≤ ((tok k).length : ℝ) := by
      interval_cases k <;> simp [Phi, wt, tok] <;> nlinarith
    linarith

lemma V_length_ge (J : ℕ) : 3.38 * lam ^ (2 * J) ≤ ((V J).length : ℝ) := by
  cases J with
  | zero =>
    have h : (V 0).length = 5 := by decide
    rw [h]
    norm_num
  | succ J =>
    have h := length_ge_Phi _ (tauIter_valid (2 * (J + 1)) _ valid00)
    rw [Phi_iter] at h
    rw [V_succ', List.length_append]
    push_cast
    have : (0 : ℝ) ≤ (V J).length := Nat.cast_nonneg _
    linarith

/-! ### Counting along the word -/

lemma V_letters (k : ℕ) : ∀ x ∈ V k, x ≤ 1 := by
  intro x hx
  simp only [V, List.mem_cons] at hx
  rcases hx with rfl | hx
  · norm_num
  · exact flat_letters _ x hx

lemma W_le (i : ℕ) : W i ≤ 1 := by
  have hi : i < (V i).length := by have := V_length i; omega
  rw [W_eq i i hi, List.getD_eq_getElem _ _ hi]
  exact V_letters i _ (List.getElem_mem hi)

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

/-- D(N) = Z(N) - c O(N) is the deviation over the first N letters of W. -/
noncomputable def D (N : ℕ) : ℝ := (Z N : ℝ) - cc * (O N : ℝ)

lemma D_eq (k N : ℕ) (hN : N ≤ (V k).length) : D N = gL ((V k).take N) := by
  obtain ⟨h1, h2⟩ := counts_eq k N hN
  simp [D, gL, h1, h2]

lemma O_add_Z (N : ℕ) : O N + Z N = N := by
  induction N with
  | zero => simp [O, Z]
  | succ N ih =>
    rw [O_succ, Z_succ]
    have := W_le N
    split_ifs <;> omega

lemma D_triv (N : ℕ) : |D N| ≤ cc * N := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hs : ((O N : ℕ) : ℝ) + (Z N : ℝ) = N := by exact_mod_cast O_add_Z N
  have hz : (0 : ℝ) ≤ Z N := Nat.cast_nonneg _
  have ho : (0 : ℝ) ≤ O N := Nat.cast_nonneg _
  unfold D
  rw [abs_le]
  constructor <;> nlinarith

/-! ### Level of a prefix -/

lemma pow_bound (J : ℕ) (hJ : 3 ≤ J) :
    18.19 * 1.4161 ^ (J + 1) - 12.5 < 1.69 * lam ^ (2 * J) := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  have hq : (4.5385 : ℝ) ≤ lam ^ 2 := by nlinarith
  induction J, hJ using Nat.le_induction with
  | base =>
    have h6 : (4.5385 : ℝ) ^ 3 ≤ (lam ^ 2) ^ 3 := pow_le_pow_left₀ (by norm_num) hq 3
    rw [← pow_mul] at h6
    norm_num at h6 ⊢
    linarith
  | succ J hJ ih =>
    rw [pow_succ (1.4161 : ℝ) (J + 1), show 2 * (J + 1) = 2 * J + 2 by ring, pow_add lam (2 * J) 2]
    have hp : 0 ≤ lam ^ (2 * J) := by positivity
    have hr1 : (1 : ℝ) ≤ 1.4161 ^ (J + 1) := one_le_pow₀ (by norm_num)
    have hm := mul_le_mul_of_nonneg_left hq hp
    nlinarith

lemma V3_length : (V 3).length = 441 := by decide +kernel

/-- For N > 441 there is a level J >= 3 with 3.38 lam^(2J) < N and
|D(N)| <= 18.19 * 1.4161^(J+1) - 12.5. -/
lemma level (N : ℕ) (hN : 441 < N) :
    ∃ J : ℕ, 3 ≤ J ∧ 3.38 * lam ^ (2 * J) < (N : ℝ) ∧
      |D N| ≤ 18.19 * 1.4161 ^ (J + 1) - 12.5 := by
  have hex : ∃ k, N ≤ (V k).length := ⟨N, by have := V_length N; omega⟩
  classical
  have hk : N ≤ (V (Nat.find hex)).length := Nat.find_spec hex
  have h3 := V3_length
  have hk4 : 4 ≤ Nat.find hex := by
    by_contra h
    have := (V_prefix (show Nat.find hex ≤ 3 by omega)).length_le
    omega
  have hmin : (V (Nat.find hex - 1)).length < N := by
    have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    omega
  set J := Nat.find hex - 1 with hJ
  have hJ1 : Nat.find hex = J + 1 := by omega
  rw [hJ1] at hk
  refine ⟨J, by omega, ?_, ?_⟩
  · have hl := V_length_ge J
    have : ((V J).length : ℝ) < N := by exact_mod_cast hmin
    linarith
  · rw [D_eq (J + 1) N hk, V_succ', List.take_append, List.take_of_length_le hmin.le, gL_append]
    obtain ⟨i, hi⟩ := flat_split (tau^[2 * (J + 1)] [0, 0]) (tauIter_valid _ _ valid00)
      (N - (V J).length)
    have hpre : |g ((tau^[2 * (J + 1)] [0, 0]).take i)| ≤
        |u 0 (2 * (J + 1))| + PB (2 * (J + 1)) := by
      rw [show ([0, 0] : List ℕ) = [0] ++ [0] from rfl, tauIter_append]
      refine le_trans (take_append_le _ _ _ _ (prefix_bound _ 0 (by norm_num))
        (prefix_bound _ 0 (by norm_num)) i) (max_le ?_ le_rfl)
      have := abs_nonneg (u 0 (2 * (J + 1)))
      linarith
    have hS := S_dev J
    have hV : gL (V J) = 1 + g (S J) := by
      have e : V J = [0] ++ flat (S J) := rfl
      rw [e, gL_append, gL_eq [0] 1 0 (by decide) (by decide)]
      norm_num
      rfl
    have hu := u_bound 0 (2 * (J + 1)) (by norm_num)
    simp only [Cx, pow_two_mul] at hu
    have hPB : PB (2 * (J + 1)) = 11.85 * 1.4161 ^ (J + 1) - 10.61 := by
      unfold PB
      rw [pow_two_mul]
    rw [hPB] at hpre
    rw [hV]
    have hq : 0 ≤ (1.4161 : ℝ) ^ J := by positivity
    have h1 := abs_add_le (1 + g (S J))
      (gL ((flat (tau^[2 * (J + 1)] [0, 0])).take (N - (V J).length)))
    have h2 := abs_add_le (1 : ℝ) (g (S J))
    have h3 := abs_sub_abs_le_abs_sub
      (gL ((flat (tau^[2 * (J + 1)] [0, 0])).take (N - (V J).length)))
      (g ((tau^[2 * (J + 1)] [0, 0]).take i))
    norm_num at h2
    rw [pow_succ] at hu hpre ⊢
    linarith

/-- Over every prefix of W longer than 441 letters, |D| < N/2. -/
lemma D_small (N : ℕ) (hN : 441 < N) : |D N| < (N : ℝ) / 2 := by
  obtain ⟨J, hJ, hNr, hD⟩ := level N hN
  have hp := pow_bound J hJ
  linarith

/-- D(N)^2 <= 1500 N for every N. -/
lemma D_sq (N : ℕ) : D N ^ 2 ≤ 1500 * N := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  rcases le_or_gt N 441 with h | h
  · have h1 := D_triv N
    have hN1 : (N : ℝ) ≤ 441 := by exact_mod_cast h
    have h2 : D N ^ 2 ≤ (cc * N) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have h3 : (cc * N) ^ 2 = cc ^ 2 * N * N := by ring
    have h4 : cc ^ 2 ≤ 3.1305 := by nlinarith
    have h5 : cc ^ 2 * (N : ℝ) * N ≤ 3.1305 * 441 * N := by
      have hc0 : 0 ≤ cc ^ 2 := sq_nonneg _
      have := mul_le_mul h4 hN1 hN0 (by norm_num)
      nlinarith
    nlinarith
  · obtain ⟨J, hJ, hNr, hD⟩ := level N h
    obtain ⟨hl1, hl2, -⟩ := lam_spec
    have hq1 : (1 : ℝ) ≤ 1.4161 ^ J := one_le_pow₀ (by norm_num)
    have hD' : |D N| ≤ 25.76 * 1.4161 ^ J := by
      rw [pow_succ] at hD
      nlinarith
    have h2 : D N ^ 2 ≤ (25.76 * 1.4161 ^ J) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hD' 2
    have h3 : (25.76 * (1.4161 : ℝ) ^ J) ^ 2 = 25.76 ^ 2 * ((1.4161 : ℝ) ^ 2) ^ J := by
      rw [mul_pow, ← pow_mul, mul_comm J 2, pow_mul]
    have h4 : ((1.4161 : ℝ) ^ 2) ^ J ≤ lam ^ (2 * J) := by
      rw [pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by nlinarith) J
    rw [h3] at h2
    norm_num at h2
    linarith

/-! ### The positions of 0 -/

/-- The limit, (1 + c)/c = 1.56519... -/
noncomputable def m0 : ℝ := (1 + cc) / cc

lemma m0_bounds : 1.5651 ≤ m0 ∧ m0 ≤ 1.5653 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hc : 0 < cc := by linarith
  unfold m0
  constructor
  · rw [le_div_iff₀ hc]
    linarith
  · rw [div_le_iff₀ hc]
    linarith

lemma zeros_infinite : (setOf (fun i => W i = 0)).Infinite := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  have hconst : ∀ j, Z (B + 1 + j) = Z (B + 1) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      have hno : ¬ W (B + 1 + j) = 0 := fun h => by
        have := hB h
        omega
      rw [show B + 1 + (j + 1) = B + 1 + j + 1 by ring, Z_succ, if_neg hno, ih, add_zero]
  have h := D_small (B + 1 + (4 * Z (B + 1) + 500)) (by omega)
  have hs := O_add_Z (B + 1 + (4 * Z (B + 1) + 500))
  rw [hconst] at hs
  unfold D at h
  rw [hconst, abs_lt] at h
  obtain ⟨h1, -⟩ := h
  have hO : (O (B + 1 + (4 * Z (B + 1) + 500)) : ℝ) =
      ((B + 1 + (4 * Z (B + 1) + 500) : ℕ) : ℝ) - Z (B + 1) := by
    have : (O (B + 1 + (4 * Z (B + 1) + 500)) : ℝ) + Z (B + 1) =
        ((B + 1 + (4 * Z (B + 1) + 500) : ℕ) : ℝ) := by exact_mod_cast hs
    linarith
  rw [hO] at h1
  generalize hz : (Z (B + 1) : ℝ) = z at h1
  have hz0 : 0 ≤ z := by rw [← hz]; exact Nat.cast_nonneg _
  have hz' : ((B + 1 + (4 * Z (B + 1) + 500) : ℕ) : ℝ) = (B : ℝ) + 1 + (4 * z + 500) := by
    rw [← hz]; push_cast; ring
  rw [hz'] at h1
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have hP := mul_le_mul_of_nonneg_right hc1 hz0
  have hQ := mul_le_mul_of_nonneg_right hc1 hB0
  clear hconst hs hO hz hz' hB
  nlinarith [hP, hQ]

lemma a_spec (n : ℕ) (hn : 1 ≤ n) : Z (a n) = n ∧ O (a n) = a n - n := by
  have hinf := zeros_infinite
  have hZp : Z (Nat.nth (fun i => W i = 0) (n - 1)) = n - 1 :=
    Nat.count_nth_of_infinite hinf (n - 1)
  have hWp : W (Nat.nth (fun i => W i = 0) (n - 1)) = 0 := Nat.nth_mem_of_infinite hinf (n - 1)
  have hZ1 : Z (a n) = n := by
    unfold a
    rw [Z_succ, if_pos hWp, hZp]
    omega
  refine ⟨hZ1, ?_⟩
  have := O_add_Z (a n)
  omega

/-- At the n-th 0, m n - a(n) = D/c. -/
lemma a_dev (n : ℕ) (hn : 1 ≤ n) : m0 * n - a n = D (a n) / cc := by
  obtain ⟨hc1, -⟩ := cc_bounds
  have hc : cc ≠ 0 := by linarith
  obtain ⟨hZ, hO⟩ := a_spec n hn
  have hle : n ≤ a n := by have := O_add_Z (a n); omega
  unfold D m0
  rw [hZ, hO]
  push_cast [hle]
  field_simp
  ring

/-- A linear scan of a word, checking 10 (t + 1) < 25 Z(t + 1) at each letter 0. -/
def chk : List ℕ → ℕ → ℕ → Bool
  | [], _, _ => true
  | x :: l, t, z =>
    if x = 0 then decide (10 * (t + 1) < 25 * (z + 1)) && chk l (t + 1) (z + 1)
    else chk l (t + 1) z

lemma chk_spec : ∀ (L : List ℕ) (t z : ℕ), chk L t z = true →
    ∀ i < L.length, L.getD i 0 = 0 →
      10 * (t + i + 1) < 25 * (z + (L.take (i + 1)).count 0) := by
  intro L
  induction L with
  | nil =>
    intro t z _ i hi
    simp at hi
  | cons x l ih =>
    intro t z h i hi hx
    by_cases h0 : x = 0
    · subst h0
      have h' : 10 * (t + 1) < 25 * (z + 1) ∧ chk l (t + 1) (z + 1) = true := by
        simpa [chk] using h
      rcases i with _ | i
      · simpa using h'.1
      · have := ih (t + 1) (z + 1) h'.2 i (by simp at hi; omega) (by simpa using hx)
        have e : ((0 :: l).take (i + 1 + 1)).count 0 = (l.take (i + 1)).count 0 + 1 := by
          simp [List.take_succ_cons]
        rw [e]
        omega
    · have h' : chk l (t + 1) z = true := by simpa [chk, h0] using h
      rcases i with _ | i
      · simp at hx
        exact absurd hx h0
      · have := ih (t + 1) z h' i (by simp at hi; omega) (by simpa using hx)
        have e : ((x :: l).take (i + 1 + 1)).count 0 = (l.take (i + 1)).count 0 := by
          simp [List.take_succ_cons, h0]
        rw [e]
        omega

lemma chk_word : chk (V 3) 0 0 = true := by decide +kernel

lemma bound_small (n : ℕ) (hn : 1 ≤ n) (ha : a n ≤ 441) :
    -1 < m0 - (a n : ℝ) / n ∧ m0 - (a n : ℝ) / n < 1 := by
  obtain ⟨hm1, hm2⟩ := m0_bounds
  obtain ⟨hZ, hO⟩ := a_spec n hn
  have hinf := zeros_infinite
  have hWp : W (Nat.nth (fun i => W i = 0) (n - 1)) = 0 := Nat.nth_mem_of_infinite hinf (n - 1)
  have ha' : a n = Nat.nth (fun i => W i = 0) (n - 1) + 1 := rfl
  set t := Nat.nth (fun i => W i = 0) (n - 1) with ht
  have hlen := V3_length
  have hW : (V 3).getD t 0 = 0 := by rw [← W_eq 3 t (by omega)]; exact hWp
  have hc := chk_spec (V 3) 0 0 chk_word t (by omega) hW
  have hZ' : ((V 3).take (t + 1)).count 0 = n := by
    rw [← (counts_eq 3 (t + 1) (by omega)).1, ← ha', hZ]
  rw [hZ'] at hc
  simp only [zero_add] at hc
  have hle : n ≤ a n := by have := O_add_Z (a n); omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hc' : (10 : ℝ) * (a n) < 25 * n := by
    rw [ha']
    exact_mod_cast hc
  have hle' : (n : ℝ) ≤ a n := by exact_mod_cast hle
  have h1 : (a n : ℝ) / n < 2.5 := by
    rw [div_lt_iff₀ hnpos]
    linarith
  have h2 : 1 ≤ (a n : ℝ) / n := by
    rw [le_div_iff₀ hnpos]
    linarith
  constructor <;> linarith

lemma bound_large (n : ℕ) (hn : 1 ≤ n) (ha : 441 < a n) :
    -1 < m0 - (a n : ℝ) / n ∧ m0 - (a n : ℝ) / n < 1 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hc : 0 < cc := by linarith
  have hD := D_small (a n) ha
  obtain ⟨hZ, hO⟩ := a_spec n hn
  have hle : n ≤ a n := by have := O_add_Z (a n); omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hdev := a_dev n hn
  have hDdef : D (a n) = (n : ℝ) - cc * ((a n : ℝ) - n) := by
    unfold D
    rw [hZ, hO]
    push_cast [hle]
    ring
  rw [abs_lt, hDdef] at hD
  obtain ⟨hD1, hD2⟩ := hD
  have e : m0 - (a n : ℝ) / n = (m0 * n - a n) / n := by field_simp
  rw [e, hdev, hDdef]
  have hA0 : (0 : ℝ) ≤ a n := Nat.cast_nonneg _
  have hle' : (n : ℝ) ≤ a n := by exact_mod_cast hle
  have hP : 1.769291 * (a n : ℝ) ≤ cc * a n := mul_le_mul_of_nonneg_right hc1 hA0
  have hQ1 : 1.769291 * (n : ℝ) ≤ cc * n := mul_le_mul_of_nonneg_right hc1 hnpos.le
  have hQ2 : cc * (n : ℝ) ≤ 1.769294 * n := mul_le_mul_of_nonneg_right hc2 hnpos.le
  have hE : cc * ((a n : ℝ) - n) = cc * a n - cc * n := by ring
  rw [hE] at hD1 hD2 ⊢
  constructor
  · rw [lt_div_iff₀ hnpos, lt_div_iff₀ hc]
    linarith
  · rw [div_lt_iff₀ hnpos, div_lt_iff₀ hc]
    linarith

/-- Kimberling's conjecture: a(n)/n tends to a number m = 1.56..., and -1 < m - a(n)/n < 1
for n >= 1. -/
theorem conjecture : ∃ m : ℝ, (1.56 ≤ m ∧ m < 1.57) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 m) ∧
    ∀ n : ℕ, 1 ≤ n → -1 < m - (a n : ℝ) / n ∧ m - (a n : ℝ) / n < 1 := by
  obtain ⟨hm1, hm2⟩ := m0_bounds
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hc : 0 < cc := by linarith
  have hbound : ∀ n : ℕ, 1 ≤ n → -1 < m0 - (a n : ℝ) / n ∧ m0 - (a n : ℝ) / n < 1 := by
    intro n hn
    rcases le_or_gt (a n) 441 with h | h
    · exact bound_small n hn h
    · exact bound_large n hn h
  refine ⟨m0, ⟨by linarith, by linarith⟩, ?_, hbound⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => Real.sqrt (1500 * 3 / cc ^ 2 / n)) atTop (𝓝 0) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (1500 * 3 / cc ^ 2)).sqrt
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq := D_sq (a n)
  have hb := hbound n hn
  have ha3 : (a n : ℝ) ≤ 3 * n := by
    have h1 : (a n : ℝ) / n < 2.5654 := by linarith [hb.1]
    rw [div_lt_iff₀ hnpos] at h1
    linarith
  have hdev := a_dev n hn
  rw [Real.norm_eq_abs]
  apply Real.abs_le_sqrt
  have e : (a n : ℝ) / n - m0 = -(D (a n) / cc) / n := by
    rw [← hdev]
    field_simp
    ring
  have key : ((a n : ℝ) / n - m0) ^ 2 = D (a n) ^ 2 / (cc ^ 2 * n ^ 2) := by
    rw [e]
    field_simp
  rw [key, div_le_div_iff₀ (by positivity) hnpos]
  have hD3 : D (a n) ^ 2 ≤ 1500 * (3 * n) := by
    have : (1500 : ℝ) * (a n) ≤ 1500 * (3 * n) := by linarith
    linarith
  have e2 : 1500 * 3 / cc ^ 2 * (cc ^ 2 * (n : ℝ) ^ 2) = 1500 * 3 * n ^ 2 := by
    field_simp
  rw [e2]
  nlinarith [hD3, hnpos]

end OMA.S_oeis_a288467

theorem OMA.solution : type_of% @OMA.S_oeis_a288467.main :=
  OMA.S_oeis_a288467.conjecture

import OMAStatements.S_oeis_a288218

namespace OMA.S_oeis_a288218

open Filter Topology





/-! ### One pass -/

/-- Induction along the cases of `step`. -/
theorem step_rec {P : List ℕ → Prop} (h0 : P []) (h00 : ∀ l, P l → P (0 :: 0 :: l))
    (h10 : ∀ l, P l → P (1 :: 0 :: l)) (hz : P [0]) (ho : P [1])
    (hzy : ∀ y l, P ((y + 1) :: l) → P (0 :: (y + 1) :: l))
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
          · rcases y with _ | y
            · exact h00 l (ih l (by simp at hu; omega))
            · exact hzy y l (ih _ (by simpa using hu))
        · rcases l with _ | ⟨y, l⟩
          · exact ho
          · rcases y with _ | y
            · exact h10 l (ih l (by simp at hu; omega))
            · exact hoy y l (ih _ (by simpa using hu))
        · exact hx x l (ih l (by omega))
  exact fun u => key u.length u le_rfl

/-- A pass reads a final 10 as one pair, so the pass over x 1 0 w is the pass over x 1 0
followed by the pass over w. -/
lemma step_cut (u : List ℕ) : ∀ w, step (u ++ 1 :: 0 :: w) = step (u ++ [1, 0]) ++ step w := by
  refine step_rec (P := fun u => ∀ w, step (u ++ 1 :: 0 :: w) = step (u ++ [1, 0]) ++ step w)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ u
  · intro w
    rfl
  · intro l ih w
    show 1 :: 0 :: 0 :: 0 :: step (l ++ 1 :: 0 :: w) =
      1 :: 0 :: 0 :: 0 :: step (l ++ [1, 0]) ++ step w
    rw [ih]
    rfl
  · intro l ih w
    show 0 :: 1 :: 0 :: step (l ++ 1 :: 0 :: w) = 0 :: 1 :: 0 :: step (l ++ [1, 0]) ++ step w
    rw [ih]
    rfl
  · intro w
    rfl
  · intro w
    rfl
  · intro y l ih w
    show 0 :: step ((y + 1) :: l ++ 1 :: 0 :: w) = 0 :: step ((y + 1) :: l ++ [1, 0]) ++ step w
    rw [ih]
    rfl
  · intro y l ih w
    show 1 :: step ((y + 1) :: l ++ 1 :: 0 :: w) = 1 :: step ((y + 1) :: l ++ [1, 0]) ++ step w
    rw [ih]
    rfl
  · intro x l ih w
    show (x + 2) :: step (l ++ 1 :: 0 :: w) = (x + 2) :: step (l ++ [1, 0]) ++ step w
    rw [ih]
    rfl

/-! ### Tokens -/

/-- The token j is the word 0^j 1 0. -/
def tok (j : ℕ) : List ℕ := List.replicate j 0 ++ [1, 0]

/-- The word of a list of tokens. -/
def flat (s : List ℕ) : List ℕ := s.flatMap tok

/-- The images of the tokens: 10 -> 010, 010 -> 0010, 0010 -> 10.00010, 00010 -> 10.000010,
000010 -> 10.0010.00010. -/
def tauT : ℕ → List ℕ
  | 0 => [1]
  | 1 => [2]
  | 2 => [0, 3]
  | 3 => [0, 4]
  | _ => [0, 2, 3]

/-- The token morphism. -/
def tau (s : List ℕ) : List ℕ := s.flatMap tauT

/-- All tokens are 0, 1, 2, 3 or 4. -/
def Valid (s : List ℕ) : Prop := ∀ k ∈ s, k ≤ 4

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
  rcases k with _ | _ | _ | _ | k <;> simp [tauT] at hx <;> omega

lemma tau_valid (s : List ℕ) : Valid (tau s) := by
  intro x hx
  simp only [tau, List.mem_flatMap] at hx
  obtain ⟨k, -, hk⟩ := hx
  exact tauT_valid k x hk

lemma valid_cons {k : ℕ} {s : List ℕ} (h : Valid (k :: s)) : k ≤ 4 ∧ Valid s :=
  ⟨h k (by simp), fun x hx => h x (by simp [hx])⟩

lemma valid_single {x : ℕ} (hx : x ≤ 4) : Valid [x] := by
  intro y hy
  simp at hy
  omega

lemma step_flat_append (s w : List ℕ) : step (flat s ++ w) = step (flat s) ++ step w := by
  induction s with
  | nil => rfl
  | cons k s ih =>
    have e1 : flat (k :: s) ++ w = List.replicate k 0 ++ 1 :: 0 :: (flat s ++ w) := by
      simp [flat_cons, tok]
    have e2 : flat (k :: s) = List.replicate k 0 ++ 1 :: 0 :: flat s := by
      simp [flat_cons, tok]
    rw [e1, step_cut (List.replicate k 0) (flat s ++ w), ih, e2,
      step_cut (List.replicate k 0) (flat s)]
    simp only [List.append_assoc]

lemma step_tok (k : ℕ) (hk : k ≤ 4) : step (tok k) = flat (tauT k) := by
  interval_cases k <;> rfl

lemma step_flat (s : List ℕ) (hs : Valid s) : step (flat s) = flat (tau s) := by
  induction s with
  | nil => rfl
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    have e : flat (k :: s) = flat [k] ++ flat s := by simp [flat]
    rw [e, step_flat_append, show flat [k] = tok k by simp [flat], step_tok k hk, ih hs',
      tau_cons, flat_append]

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

/-! ### The iterates -/

/-- X n: the tokens of iterate n before its last two letters 00. -/
def X : ℕ → List ℕ
  | 0 => []
  | n + 1 => tau (X n) ++ [0]

lemma X_valid (n : ℕ) : Valid (X n) := by
  induction n with
  | zero => intro x hx; simp [X] at hx
  | succ n ih =>
    intro x hx
    simp only [X, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | hx
    · exact tau_valid _ x hx
    · omega

lemma iter_eq (n : ℕ) : iter n = flat (X n) ++ [0, 0] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show iter (n + 1) = step (iter n) from rfl, ih, step_flat_append,
      step_flat _ (X_valid n), X, flat_append, List.append_assoc]
    rfl

lemma X_succ (n : ℕ) : X (n + 1) = tau^[n] [0] ++ X n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h1 : X (n + 1 + 1) = tau (X (n + 1)) ++ [0] := rfl
    rw [h1]
    conv_lhs => rw [ih]
    rw [tau_append, Function.iterate_succ_apply', List.append_assoc]
    rfl

/-- The first part of iterate n + 1 is the word of the tokens tau^n(0). -/
lemma iter_first (n : ℕ) : flat (tau^[n] [0]) <+: iter (n + 1) := by
  rw [iter_eq, X_succ, flat_append, List.append_assoc]
  exact List.prefix_append _ _

/-! ### The limiting word -/

/-- Q m: the word of the tokens tau^(3m)(2). -/
def Q (m : ℕ) : List ℕ := flat (tau^[3 * m] [2])

lemma tau_three_two : tau^[3] [2] = [2] ++ [1, 0, 2, 3] := rfl

lemma Q_prefix_succ (m : ℕ) : Q m <+: Q (m + 1) := by
  unfold Q
  rw [show 3 * (m + 1) = 3 * m + 3 by ring, Function.iterate_add_apply, tau_three_two,
    tauIter_append, flat_append]
  exact List.prefix_append _ _

lemma Q_prefix {m n : ℕ} (h : m ≤ n) : Q m <+: Q n := by
  induction n, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n _ ih => exact ih.trans (Q_prefix_succ n)

lemma flat_length_pos (s : List ℕ) (hs : s ≠ []) : 1 ≤ (flat s).length := by
  rcases s with _ | ⟨k, s⟩
  · exact absurd rfl hs
  · rw [flat_cons, List.length_append]
    simp [tok]
    omega

lemma tauT_ne_nil (k : ℕ) : tauT k ≠ [] := by
  rcases k with _ | _ | _ | _ | k <;> simp [tauT]

lemma tau_ne_nil (s : List ℕ) (hs : s ≠ []) : tau s ≠ [] := by
  rcases s with _ | ⟨k, s⟩
  · exact absurd rfl hs
  · rw [tau_cons]
    intro h
    exact tauT_ne_nil k (List.append_eq_nil_iff.mp h).1

lemma tauIter_ne_nil (n : ℕ) (s : List ℕ) (hs : s ≠ []) : tau^[n] s ≠ [] := by
  induction n generalizing s with
  | zero => exact hs
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact ih _ (tau_ne_nil s hs)

lemma tauIter_nil (n : ℕ) : tau^[n] [] = [] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

lemma Q_length_succ (m : ℕ) : (Q m).length + 1 ≤ (Q (m + 1)).length := by
  unfold Q
  rw [show 3 * (m + 1) = 3 * m + 3 by ring, Function.iterate_add_apply, tau_three_two,
    tauIter_append, flat_append, List.length_append]
  have := flat_length_pos _ (tauIter_ne_nil (3 * m) [1, 0, 2, 3] (by simp))
  omega

lemma Q_length (m : ℕ) : m + 4 ≤ (Q m).length := by
  induction m with
  | zero => decide
  | succ m ih =>
    have := Q_length_succ m
    omega

/-- Q m begins iterate 3k for every k >= m + 1. -/
lemma stable (m k : ℕ) (h : m ≤ k) : Q m <+: iter (3 * (k + 1)) := by
  have e : 3 * (k + 1) = (3 * k + 2) + 1 := by ring
  rw [e]
  refine (Q_prefix h).trans ?_
  have hq : Q k = flat (tau^[3 * k + 2] [0]) := by
    unfold Q
    rw [Function.iterate_add_apply]
    rfl
  rw [hq]
  exact iter_first _

lemma getD_prefix {l₁ l₂ : List ℕ} (h : l₁ <+: l₂) {i : ℕ} (hi : i < l₁.length) :
    l₁.getD i 0 = l₂.getD i 0 := by
  obtain ⟨s, rfl⟩ := h
  rw [List.getD_append _ _ _ _ hi]

lemma W_eq (m i : ℕ) (hi : i < (Q m).length) : W i = (Q m).getD i 0 := by
  unfold W
  have hi' : i < (Q i).length := by have := Q_length i; omega
  rw [← getD_prefix (stable i i le_rfl) hi']
  rcases le_total i m with h | h
  · exact getD_prefix (Q_prefix h) hi'
  · exact (getD_prefix (Q_prefix h) hi).symm

/-! ### The golden ratio -/

lemma phi_exists : ∃ x : ℝ, 1.618 ≤ x ∧ x ≤ 1.6181 ∧ x ^ 2 - x - 1 = 0 := by
  have hc : ContinuousOn (fun x : ℝ => x ^ 2 - x - 1) (Set.Icc 1.618 1.6181) := by
    fun_prop
  have h := intermediate_value_Icc (show (1.618 : ℝ) ≤ 1.6181 by norm_num) hc
  have h0 : (0 : ℝ) ∈ Set.Icc ((fun x : ℝ => x ^ 2 - x - 1) 1.618)
      ((fun x : ℝ => x ^ 2 - x - 1) 1.6181) := by
    constructor <;> norm_num
  obtain ⟨x, ⟨hx1, hx2⟩, hx⟩ := h h0
  exact ⟨x, hx1, hx2, hx⟩

/-- The golden ratio, the Perron root of the token morphism. -/
noncomputable def phi : ℝ := Classical.choose phi_exists

lemma phi_spec : 1.618 ≤ phi ∧ phi ≤ 1.6181 ∧ phi ^ 2 - phi - 1 = 0 :=
  Classical.choose_spec phi_exists

/-- The limiting number of letters 0 per letter 1, phi^2 = phi + 1. -/
noncomputable def cc : ℝ := phi + 1

lemma cc_bounds : 2.618 ≤ cc ∧ cc ≤ 2.6181 := by
  obtain ⟨h1, h2, -⟩ := phi_spec
  unfold cc
  constructor <;> linarith

/-! ### Deviation of token lists -/

/-- For a list of tokens, the number of letters 0 minus c times the number of letters 1. -/
noncomputable def g (s : List ℕ) : ℝ := (s.sum : ℝ) + (s.length : ℝ) - cc * (s.length : ℝ)

lemma g_append (u v : List ℕ) : g (u ++ v) = g u + g v := by
  simp only [g, List.sum_append, List.length_append]
  push_cast
  ring

lemma g_single (k : ℕ) : g [k] = k + 1 - cc := by
  simp [g]

lemma counts (s : List ℕ) (hs : Valid s) :
    s.sum = s.count 1 + 2 * s.count 2 + 3 * s.count 3 + 4 * s.count 4 ∧
      s.length = s.count 0 + s.count 1 + s.count 2 + s.count 3 + s.count 4 := by
  induction s with
  | nil => simp
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    obtain ⟨h1, h2⟩ := ih hs'
    interval_cases k <;> simp [List.count_cons] <;> omega

lemma tau_counts (s : List ℕ) (hs : Valid s) :
    (tau s).count 0 = s.count 2 + s.count 3 + s.count 4 ∧ (tau s).count 1 = s.count 0 ∧
      (tau s).count 2 = s.count 1 + s.count 4 ∧ (tau s).count 3 = s.count 2 + s.count 4 ∧
      (tau s).count 4 = s.count 3 := by
  induction s with
  | nil => simp [tau]
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    obtain ⟨h0, h1, h2, h3, h4⟩ := ih hs'
    rw [tau_cons, List.count_append, List.count_append, List.count_append, List.count_append,
      List.count_append]
    interval_cases k <;> simp [tauT, List.count_cons] <;> omega

lemma g_counts (s : List ℕ) (hs : Valid s) :
    g s = (1 - cc) * (s.count 0 : ℝ) + (2 - cc) * (s.count 1 : ℝ) + (3 - cc) * (s.count 2 : ℝ) +
      (4 - cc) * (s.count 3 : ℝ) + (5 - cc) * (s.count 4 : ℝ) := by
  obtain ⟨h1, h2⟩ := counts s hs
  unfold g
  rw [h1, h2]
  push_cast
  ring

/-- After one step the deviation is multiplied by 1 - phi = -1/phi at every step. -/
lemma g_rec (s : List ℕ) (hs : Valid s) : g (tau (tau s)) = (1 - phi) * g (tau s) := by
  obtain ⟨-, -, hp⟩ := phi_spec
  have hv := tau_valid s
  obtain ⟨a0, a1, a2, a3, a4⟩ := tau_counts s hs
  obtain ⟨b0, b1, b2, b3, b4⟩ := tau_counts (tau s) hv
  rw [g_counts _ (tau_valid _), g_counts _ hv, b0, b1, b2, b3, b4, a0, a1, a2, a3, a4]
  unfold cc
  push_cast
  linear_combination (-(s.count 0 : ℝ) - (s.count 1 : ℝ) - 2 * (s.count 2 : ℝ) -
    2 * (s.count 3 : ℝ) - 3 * (s.count 4 : ℝ)) * hp

lemma g_one (x : ℕ) (hx : x ≤ 4) : |g (tau [x])| ≤ 0.77 := by
  obtain ⟨h1, h2⟩ := cc_bounds
  have e0 : g [1] = 2 - cc := by simp [g] <;> ring
  have e1 : g [2] = 3 - cc := by simp [g] <;> ring
  have e2 : g [0, 3] = 5 - 2 * cc := by simp [g] <;> ring
  have e3 : g [0, 4] = 6 - 2 * cc := by simp [g] <;> ring
  have e4 : g [0, 2, 3] = 8 - 3 * cc := by simp [g] <;> ring
  rw [tau_single]
  interval_cases x
  · rw [show tauT 0 = [1] from rfl, e0, abs_le]; constructor <;> linarith
  · rw [show tauT 1 = [2] from rfl, e1, abs_le]; constructor <;> linarith
  · rw [show tauT 2 = [0, 3] from rfl, e2, abs_le]; constructor <;> linarith
  · rw [show tauT 3 = [0, 4] from rfl, e3, abs_le]; constructor <;> linarith
  · rw [show tauT 4 = [0, 2, 3] from rfl, e4, abs_le]; constructor <;> linarith

lemma g_decay (j x : ℕ) (hx : x ≤ 4) : |g (tau^[j + 1] [x])| ≤ 0.77 * 0.62 ^ j := by
  obtain ⟨hp1, hp2, -⟩ := phi_spec
  induction j with
  | zero =>
    simp only [zero_add, Function.iterate_one, pow_zero, mul_one]
    exact g_one x hx
  | succ j ih =>
    have hv : Valid (tau^[j] [x]) := tauIter_valid j _ (valid_single hx)
    have e : tau^[j + 1 + 1] [x] = tau (tau (tau^[j] [x])) := by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have e1 : tau^[j + 1] [x] = tau (tau^[j] [x]) := Function.iterate_succ_apply' _ _ _
    rw [e, g_rec _ hv, ← e1, abs_mul, abs_of_neg (by linarith : 1 - phi < 0), neg_sub, pow_succ]
    have hp : 0 ≤ (0.62 : ℝ) ^ j := by positivity
    have h := mul_le_mul_of_nonneg_left ih (by linarith : (0 : ℝ) ≤ phi - 1)
    have h2 : (phi - 1) * (0.77 * 0.62 ^ j) ≤ 0.62 * (0.77 * 0.62 ^ j) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith

lemma g_bound (j x : ℕ) (hx : x ≤ 4) : |g (tau^[j] [x])| ≤ 2.4 := by
  obtain ⟨h1, h2⟩ := cc_bounds
  rcases j with _ | j
  · simp only [Function.iterate_zero, id, g_single]
    have : (x : ℝ) ≤ 4 := by exact_mod_cast hx
    have h0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
    rw [abs_le]
    constructor <;> linarith
  · have h := g_decay j x hx
    have : (0.62 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith

/-! ### Prefixes of token lists -/

lemma tauIter_morph (j : ℕ) : ∀ u v, tau^[j] (u ++ v) = tau^[j] u ++ tau^[j] v :=
  tauIter_append j

/-- Splitting a prefix of the image of a token list along its tokens. -/
lemma pref_split (T : List ℕ → List ℕ) (hT : ∀ u v, T (u ++ v) = T u ++ T v) (b : ℝ)
    (hb0 : 0 ≤ b)
    (hb : ∀ y, y ≤ 4 → ∀ i ≤ (T [y]).length, |g ((T [y]).take i)| ≤ b) :
    ∀ ys : List ℕ, Valid ys → ∀ i ≤ (T ys).length,
      ∃ q ≤ ys.length, |g ((T ys).take i) - g (T (ys.take q))| ≤ b := by
  have hnil : T [] = [] := by
    have h := hT [] []
    simp only [List.append_nil] at h
    have hl := congrArg List.length h
    rw [List.length_append] at hl
    exact List.eq_nil_of_length_eq_zero (by omega)
  intro ys
  induction ys with
  | nil =>
    intro _ i hi
    rw [hnil] at hi ⊢
    simp at hi
    subst hi
    exact ⟨0, le_rfl, by simp [hnil, g, hb0]⟩
  | cons y ys ih =>
    intro hv i hi
    obtain ⟨hy, hv'⟩ := valid_cons hv
    have e : T (y :: ys) = T [y] ++ T ys := by rw [← hT]; rfl
    rw [e] at hi ⊢
    rw [List.length_append] at hi
    rcases le_or_gt i (T [y]).length with h | h
    · refine ⟨0, by omega, ?_⟩
      rw [List.take_append_of_le_length h, List.take_zero, hnil]
      simpa [g] using hb y hy i h
    · obtain ⟨q, hq, hq'⟩ := ih hv' (i - (T [y]).length) (by omega)
      refine ⟨q + 1, by simp; omega, ?_⟩
      rw [List.take_append, List.take_of_length_le h.le, g_append,
        show (y :: ys).take (q + 1) = [y] ++ ys.take q from rfl, hT, g_append]
      have : g (T [y]) + g ((T ys).take (i - (T [y]).length)) - (g (T [y]) + g (T (ys.take q)))
          = g ((T ys).take (i - (T [y]).length)) - g (T (ys.take q)) := by ring
      rw [this]
      exact hq'

/-- The deviation of the image of a short token list under tau^(J+1). -/
lemma g_short (J : ℕ) : ∀ u : List ℕ, Valid u →
    |g (tau^[J + 1] u)| ≤ u.length * (0.77 * 0.62 ^ J) := by
  intro u
  induction u with
  | nil =>
    intro _
    rw [tauIter_nil]
    simp [g]
  | cons y u ih =>
    intro hu
    obtain ⟨hy, hu'⟩ := valid_cons hu
    rw [show y :: u = [y] ++ u from rfl, tauIter_append, g_append, List.length_append]
    have a1 := g_decay J y hy
    have a2 := ih hu'
    have a3 := abs_add_le (g (tau^[J + 1] [y])) (g (tau^[J + 1] u))
    push_cast
    simp only [List.length_singleton, Nat.cast_one]
    linarith

lemma tauT_length (x : ℕ) : (tauT x).length ≤ 3 := by
  rcases x with _ | _ | _ | _ | x <;> simp [tauT]

/-- |g| over the prefixes of tau^(J+1)(x). -/
lemma prefix_bound_succ (J : ℕ) : ∀ x, x ≤ 4 → ∀ i ≤ (tau^[J + 1] [x]).length,
    |g ((tau^[J + 1] [x]).take i)| ≤ 16 - 9.9 * 0.62 ^ (J + 1) := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  induction J with
  | zero =>
    intro x hx i hi
    simp only [zero_add, Function.iterate_one, tau_single] at hi ⊢
    have hv : Valid ((tauT x).take i) := fun y hy => tauT_valid x y (List.mem_of_mem_take hy)
    have hl : ((tauT x).take i).length ≤ 3 := by
      rw [List.length_take]; have := tauT_length x; omega
    have key : ∀ u : List ℕ, Valid u → |g u| ≤ u.length * 2.4 := by
      intro u
      induction u with
      | nil => intro _; simp [g]
      | cons y u ih =>
        intro hu
        obtain ⟨hy, hu'⟩ := valid_cons hu
        rw [show y :: u = [y] ++ u from rfl, g_append, List.length_append]
        have b1 := g_bound 0 y hy
        simp only [Function.iterate_zero, id] at b1
        have b2 := ih hu'
        have b3 := abs_add_le (g [y]) (g u)
        push_cast
        simp only [List.length_singleton, Nat.cast_one]
        linarith
    have h := key _ hv
    have hl' : (((tauT x).take i).length : ℝ) ≤ 3 := by exact_mod_cast hl
    norm_num
    nlinarith
  | succ J ih =>
    intro x hx i hi
    have hp : 0 ≤ (0.62 : ℝ) ^ J := by positivity
    have e : tau^[J + 1 + 1] [x] = tau^[J + 1] (tauT x) := by
      rw [Function.iterate_succ_apply, tau_single]
    rw [e] at hi ⊢
    have hb0 : (0 : ℝ) ≤ 16 - 9.9 * 0.62 ^ (J + 1) := by
      have : (0.62 : ℝ) ^ (J + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      linarith
    obtain ⟨q, hq, hq'⟩ := pref_split (tau^[J + 1]) (tauIter_morph (J + 1)) _ hb0 ih (tauT x)
      (tauT_valid x) i hi
    have hvq : Valid ((tauT x).take q) := fun y hy => tauT_valid x y (List.mem_of_mem_take hy)
    have hfirst : |g (tau^[J + 1] ((tauT x).take q))| ≤ 3 * (0.77 * 0.62 ^ J) := by
      have h := g_short J _ hvq
      have hl : (((tauT x).take q).length : ℝ) ≤ 3 := by
        have : ((tauT x).take q).length ≤ 3 := by
          rw [List.length_take]; have := tauT_length x; omega
        exact_mod_cast this
      have hpos : 0 ≤ 0.77 * (0.62 : ℝ) ^ J := by positivity
      nlinarith
    have htri : |g ((tau^[J + 1] (tauT x)).take i)| ≤
        |g (tau^[J + 1] ((tauT x).take q))| + (16 - 9.9 * 0.62 ^ (J + 1)) := by
      have := abs_sub_abs_le_abs_sub (g ((tau^[J + 1] (tauT x)).take i))
        (g (tau^[J + 1] ((tauT x).take q)))
      linarith
    have e1 : (0.62 : ℝ) ^ (J + 1) = 0.62 ^ J * 0.62 := pow_succ _ _
    have e2 : (0.62 : ℝ) ^ (J + 1 + 1) = 0.62 ^ J * 0.62 * 0.62 := by rw [pow_succ, pow_succ]
    rw [e2]
    rw [e1] at htri
    linarith

/-- |g| <= 16 over the prefixes of tau^J(x). -/
lemma prefix_bound (J x : ℕ) (hx : x ≤ 4) (i : ℕ) (hi : i ≤ (tau^[J] [x]).length) :
    |g ((tau^[J] [x]).take i)| ≤ 16 := by
  rcases J with _ | J
  · obtain ⟨hc1, hc2⟩ := cc_bounds
    simp only [Function.iterate_zero, id, List.length_cons, List.length_nil] at hi ⊢
    interval_cases i
    · simp [g]
    · simp only [List.take_succ_cons, List.take_zero, g_single]
      have : (x : ℝ) ≤ 4 := by exact_mod_cast hx
      have h0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
      rw [abs_le]
      constructor <;> linarith
  · have h := prefix_bound_succ J x hx i hi
    have : (0 : ℝ) ≤ 0.62 ^ (J + 1) := by positivity
    linarith

/-! ### Letters -/

/-- For a word, the number of letters 0 minus c times the number of letters 1. -/
noncomputable def gL (L : List ℕ) : ℝ := (L.count 0 : ℝ) - cc * (L.count 1 : ℝ)

lemma gL_append (u v : List ℕ) : gL (u ++ v) = gL u + gL v := by
  simp only [gL, List.count_append]
  push_cast
  ring

lemma gL_tok (k : ℕ) : gL (tok k) = g [k] := by
  simp [gL, g, tok, List.count_replicate, List.count_cons] <;> ring

lemma gL_tok_take (k : ℕ) (hk : k ≤ 4) (r : ℕ) : |gL ((tok k).take r)| ≤ 5 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hz : ((tok k).take r).count 0 ≤ 5 := by
    calc ((tok k).take r).count 0 ≤ (tok k).count 0 := List.Sublist.count_le _ (List.take_sublist _ _)
      _ ≤ 5 := by simp [tok, List.count_replicate]; omega
  have ho : ((tok k).take r).count 1 ≤ 1 := by
    calc ((tok k).take r).count 1 ≤ (tok k).count 1 := List.Sublist.count_le _ (List.take_sublist _ _)
      _ ≤ 1 := by simp [tok, List.count_replicate]
  have hz' : (((tok k).take r).count 0 : ℝ) ≤ 5 := by exact_mod_cast hz
  have ho' : (((tok k).take r).count 1 : ℝ) ≤ 1 := by exact_mod_cast ho
  have hz0 : (0 : ℝ) ≤ ((tok k).take r).count 0 := Nat.cast_nonneg _
  have ho0 : (0 : ℝ) ≤ ((tok k).take r).count 1 := Nat.cast_nonneg _
  unfold gL
  rw [abs_le]
  constructor <;> nlinarith

lemma flat_split : ∀ S : List ℕ, Valid S → ∀ t ≤ (flat S).length,
    ∃ i ≤ S.length, |gL ((flat S).take t) - g (S.take i)| ≤ 5 := by
  intro S
  induction S with
  | nil =>
    intro _ t ht
    simp [flat] at ht
    subst ht
    exact ⟨0, le_rfl, by simp [gL, g]⟩
  | cons k S ih =>
    intro hv t ht
    obtain ⟨hk, hv'⟩ := valid_cons hv
    rw [flat_cons] at ht ⊢
    rw [List.length_append] at ht
    rcases le_or_gt t (tok k).length with h | h
    · refine ⟨0, by omega, ?_⟩
      rw [List.take_append_of_le_length h]
      simpa [g] using gL_tok_take k hk t
    · obtain ⟨i, hi, hi'⟩ := ih hv' (t - (tok k).length) (by omega)
      refine ⟨i + 1, by simp; omega, ?_⟩
      rw [List.take_append, List.take_of_length_le h.le, gL_append, gL_tok,
        show (k :: S).take (i + 1) = [k] ++ S.take i from rfl, g_append]
      have : g [k] + gL ((flat S).take (t - (tok k).length)) - (g [k] + g (S.take i)) =
          gL ((flat S).take (t - (tok k).length)) - g (S.take i) := by ring
      rw [this]
      exact hi'

/-- Over the prefixes of Q m, |g| <= 21. -/
lemma word_prefix_bound (m N : ℕ) (hN : N ≤ (Q m).length) : |gL ((Q m).take N)| ≤ 21 := by
  unfold Q at hN ⊢
  obtain ⟨i, hi, hi'⟩ := flat_split _ (tauIter_valid _ _ (valid_single (by norm_num))) N hN
  have h := prefix_bound (3 * m) 2 (by norm_num) i hi
  have := abs_sub_abs_le_abs_sub (gL ((flat (tau^[3 * m] [2])).take N))
    (g ((tau^[3 * m] [2]).take i))
  linarith

/-! ### Counting along the limiting word -/

lemma Q_letters (m : ℕ) : ∀ x ∈ Q m, x ≤ 1 := by
  intro x hx
  simp only [Q, flat, List.mem_flatMap, tok] at hx
  obtain ⟨k, -, hk⟩ := hx
  simp at hk
  omega

lemma W_le (i : ℕ) : W i ≤ 1 := by
  have hi : i < (Q i).length := by have := Q_length i; omega
  rw [W_eq i i hi, List.getD_eq_getElem _ _ hi]
  exact Q_letters _ _ (List.getElem_mem hi)

/-- Z(N): the number of letters 0 among the first N letters of W. -/
noncomputable def Z (N : ℕ) : ℕ := Nat.count (fun i => W i = 0) N

/-- O(N): the number of letters 1 among the first N letters of W. -/
noncomputable def O (N : ℕ) : ℕ := Nat.count (fun i => W i = 1) N

lemma Z_succ (N : ℕ) : Z (N + 1) = Z N + if W N = 0 then 1 else 0 := Nat.count_succ _ _

lemma O_succ (N : ℕ) : O (N + 1) = O N + if W N = 1 then 1 else 0 := Nat.count_succ _ _

lemma counts_eq (m N : ℕ) (hN : N ≤ (Q m).length) :
    Z N = ((Q m).take N).count 0 ∧ O N = ((Q m).take N).count 1 := by
  induction N with
  | zero => simp [Z, O]
  | succ N ih =>
    have hN' : N < (Q m).length := by omega
    have hW : W N = (Q m)[N] := by rw [W_eq m N hN', List.getD_eq_getElem _ _ hN']
    obtain ⟨h1, h2⟩ := ih (by omega)
    rw [Z_succ, O_succ, h1, h2, List.take_add_one, List.getElem?_eq_getElem hN',
      List.count_append, List.count_append, hW]
    constructor <;> simp [List.count_singleton]

/-- D(N) = Z(N) - c O(N) is the deviation over the first N letters of W. -/
noncomputable def D (N : ℕ) : ℝ := (Z N : ℝ) - cc * (O N : ℝ)

lemma D_bound (N : ℕ) : |D N| ≤ 21 := by
  have hN : N ≤ (Q N).length := by have := Q_length N; omega
  obtain ⟨h1, h2⟩ := counts_eq N N hN
  have e : D N = gL ((Q N).take N) := by simp [D, gL, h1, h2]
  rw [e]
  exact word_prefix_bound N N hN

lemma O_add_Z (N : ℕ) : O N + Z N = N := by
  induction N with
  | zero => simp [O, Z]
  | succ N ih =>
    rw [O_succ, Z_succ]
    have := W_le N
    split_ifs <;> omega

/-! ### The positions of 1 -/

/-- The limit, 1 + c = phi + 2 = (5 + sqrt 5)/2 = 3.61803... -/
noncomputable def m1 : ℝ := 1 + cc

lemma m1_bounds : 3.618 ≤ m1 ∧ m1 ≤ 3.6181 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  unfold m1
  constructor <;> linarith

lemma ones_infinite : {i | W i = 1}.Infinite := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
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
  have h := D_bound (B + 1 + (4 * O (B + 1) + 22))
  have hs := O_add_Z (B + 1 + (4 * O (B + 1) + 22))
  rw [hconst] at hs
  unfold D at h
  rw [hconst, abs_le] at h
  obtain ⟨-, h2⟩ := h
  have hZ : (Z (B + 1 + (4 * O (B + 1) + 22)) : ℝ) =
      ((B + 1 + (4 * O (B + 1) + 22) : ℕ) : ℝ) - O (B + 1) := by
    have : (O (B + 1) : ℝ) + Z (B + 1 + (4 * O (B + 1) + 22)) =
        ((B + 1 + (4 * O (B + 1) + 22) : ℕ) : ℝ) := by exact_mod_cast hs
    linarith
  rw [hZ] at h2
  generalize ho : (O (B + 1) : ℝ) = o at h2
  have ho0 : 0 ≤ o := by rw [← ho]; exact Nat.cast_nonneg _
  have hN : ((B + 1 + (4 * O (B + 1) + 22) : ℕ) : ℝ) = (B : ℝ) + 1 + (4 * o + 22) := by
    rw [← ho]; push_cast; ring
  rw [hN] at h2
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have hR : cc * o ≤ 2.6181 * o := mul_le_mul_of_nonneg_right hc2 ho0
  clear hconst hs hZ hN hB
  nlinarith [hR]

lemma a_spec (n : ℕ) (hn : 1 ≤ n) : O (a n) = n ∧ Z (a n) = a n - n := by
  have hinf := ones_infinite
  have hOp : O (Nat.nth (fun i => W i = 1) (n - 1)) = n - 1 :=
    Nat.count_nth_of_infinite hinf (n - 1)
  have hWp : W (Nat.nth (fun i => W i = 1) (n - 1)) = 1 := Nat.nth_mem_of_infinite hinf (n - 1)
  have hO1 : O (a n) = n := by
    unfold a
    rw [O_succ, if_pos hWp, hOp]
    omega
  refine ⟨hO1, ?_⟩
  have := O_add_Z (a n)
  omega

/-- At the n-th 1, m n - a(n) = -D. -/
lemma a_dev (n : ℕ) (hn : 1 ≤ n) : m1 * n - a n = -D (a n) := by
  obtain ⟨hO, hZ⟩ := a_spec n hn
  have hle : n ≤ a n := by have := O_add_Z (a n); omega
  unfold D m1
  rw [hZ, hO]
  push_cast [hle]
  ring

/-! ### The window of the deviation -/

/-- A prefix of tau(S) is the image of a prefix of S followed by a proper prefix of the image of
the next token. -/
lemma tau_take_split : ∀ (S : List ℕ) (i : ℕ), i ≤ (tau S).length →
    ∃ q r, q ≤ S.length ∧ (tau S).take i = tau (S.take q) ++ (tauT (S.getD q 0)).take r ∧
      (r = 0 ∨ (q < S.length ∧ r < (tauT (S.getD q 0)).length))
  | [], i, hi => by
    have hi0 : i = 0 := by simpa [tau] using hi
    subst hi0
    exact ⟨0, 0, le_rfl, by simp [tau], Or.inl rfl⟩
  | y :: S, i, hi => by
    rw [tau_cons, List.length_append] at hi
    rcases lt_or_ge i (tauT y).length with h | h
    · refine ⟨0, i, by simp, ?_, Or.inr ⟨by simp, by simpa using h⟩⟩
      rw [tau_cons, List.take_append_of_le_length h.le]
      simp [tau]
    · obtain ⟨q, r, hq, he, hr⟩ := tau_take_split S (i - (tauT y).length) (by omega)
      refine ⟨q + 1, r, by simp; omega, ?_, ?_⟩
      · rw [tau_cons, List.take_append, List.take_of_length_le h, he]
        simp [tau_cons, List.append_assoc]
      · rcases hr with hr | ⟨hq', hr'⟩
        · exact Or.inl hr
        · exact Or.inr ⟨by simp; omega, by simpa using hr'⟩

/-- The proper prefixes of the images of the tokens. -/
lemma proper_prefix (y : ℕ) (hy : y ≤ 4) (r : ℕ) (hr : r < (tauT y).length) :
    (tauT y).take r = [] ∨ (tauT y).take r = [0] ∨ (tauT y).take r = [0, 2] := by
  interval_cases y <;> simp only [tauT, List.length_cons, List.length_nil] at hr <;>
    interval_cases r <;> decide

lemma getD_valid {S : List ℕ} (hS : Valid S) {q : ℕ} (hq : q < S.length) : S.getD q 0 ≤ 4 :=
  hS _ (by rw [List.getD_eq_getElem _ _ hq]; exact List.getElem_mem hq)

/-- F(s) = g(tau s) is multiplied by 1 - phi under tau, and 1 - phi < 0: on every prefix of
tau^J(x), -1.4 <= F <= 0.87, because (1 - phi) [-1.4, 0.87] + [-0.8543, 0] lies in [-1.4, 0.87]
and F of a proper prefix of an image lies in [-0.8543, 0]. -/
lemma window (J : ℕ) : ∀ x, x ≤ 4 → ∀ i, i ≤ (tau^[J] [x]).length →
    -1.4 ≤ g (tau ((tau^[J] [x]).take i)) ∧ g (tau ((tau^[J] [x]).take i)) ≤ 0.87 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  obtain ⟨hp1, hp2, -⟩ := phi_spec
  induction J with
  | zero =>
    intro x hx i hi
    simp only [Function.iterate_zero, id, List.length_singleton] at hi ⊢
    rcases i with _ | i
    · norm_num [tau, g]
    · rw [List.take_of_length_le (by simp), tau_single]
      have e0 : g [1] = 2 - cc := by simp [g]; ring
      have e1 : g [2] = 3 - cc := by simp [g]; ring
      have e2 : g [0, 3] = 5 - 2 * cc := by simp [g]; ring
      have e3 : g [0, 4] = 6 - 2 * cc := by simp [g]; ring
      have e4 : g [0, 2, 3] = 8 - 3 * cc := by simp [g]; ring
      interval_cases x
      · rw [show tauT 0 = [1] from rfl, e0]; constructor <;> linarith
      · rw [show tauT 1 = [2] from rfl, e1]; constructor <;> linarith
      · rw [show tauT 2 = [0, 3] from rfl, e2]; constructor <;> linarith
      · rw [show tauT 3 = [0, 4] from rfl, e3]; constructor <;> linarith
      · rw [show tauT 4 = [0, 2, 3] from rfl, e4]; constructor <;> linarith
  | succ J ih =>
    intro x hx i hi
    rw [Function.iterate_succ_apply'] at hi ⊢
    have hv : Valid (tau^[J] [x]) := tauIter_valid J _ (valid_single hx)
    obtain ⟨q, r, hq, he, hr⟩ := tau_take_split (tau^[J] [x]) i hi
    have hvq : Valid ((tau^[J] [x]).take q) := fun y hy => hv y (List.mem_of_mem_take hy)
    rw [he, tau_append, g_append, g_rec _ hvq]
    obtain ⟨h1, h2⟩ := ih x hx q hq
    have hd : -0.8543 ≤ g (tau ((tauT ((tau^[J] [x]).getD q 0)).take r)) ∧
        g (tau ((tauT ((tau^[J] [x]).getD q 0)).take r)) ≤ 0 := by
      rcases hr with hr | ⟨hq', hr'⟩
      · subst hr
        norm_num [tau, g]
      · rcases proper_prefix _ (getD_valid hv hq') r hr' with e | e | e <;> rw [e]
        · norm_num [tau, g]
        · rw [show tau [0] = [1] from rfl, show g [1] = 2 - cc by simp [g]; ring]
          constructor <;> linarith
        · rw [show tau [0, 2] = [1, 0, 3] from rfl, show g [1, 0, 3] = 7 - 3 * cc by simp [g]; ring]
          constructor <;> linarith
    have k1 : 0 ≤ (phi - 1) * (g (tau ((tau^[J] [x]).take q)) + 1.4) :=
      mul_nonneg (by linarith) (by linarith)
    have k2 : 0 ≤ (phi - 1) * (0.87 - g (tau ((tau^[J] [x]).take q))) :=
      mul_nonneg (by linarith) (by linarith)
    obtain ⟨hd1, hd2⟩ := hd
    constructor <;> nlinarith

/-- On every prefix of tau^(J+1)(x), -3.0181 <= g <= 0.87. -/
lemma window_image (J x : ℕ) (hx : x ≤ 4) (i : ℕ) (hi : i ≤ (tau^[J + 1] [x]).length) :
    -3.0181 ≤ g ((tau^[J + 1] [x]).take i) ∧ g ((tau^[J + 1] [x]).take i) ≤ 0.87 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  rw [Function.iterate_succ_apply'] at hi ⊢
  have hv : Valid (tau^[J] [x]) := tauIter_valid J _ (valid_single hx)
  obtain ⟨q, r, hq, he, hr⟩ := tau_take_split (tau^[J] [x]) i hi
  rw [he, g_append]
  obtain ⟨h1, h2⟩ := window J x hx q hq
  have hd : -1.6181 ≤ g ((tauT ((tau^[J] [x]).getD q 0)).take r) ∧
      g ((tauT ((tau^[J] [x]).getD q 0)).take r) ≤ 0 := by
    rcases hr with hr | ⟨hq', hr'⟩
    · subst hr
      norm_num [g]
    · rcases proper_prefix _ (getD_valid hv hq') r hr' with e | e | e <;> rw [e]
      · norm_num [g]
      · rw [show g [0] = 1 - cc by simp [g]]
        constructor <;> linarith
      · rw [show g [0, 2] = 4 - 2 * cc by simp [g]; ring]
        constructor <;> linarith
  obtain ⟨hd1, hd2⟩ := hd
  constructor <;> linarith

/-! ### The deviation at the 1s -/

lemma gL_flat (s : List ℕ) : gL (flat s) = g s := by
  induction s with
  | nil => simp [gL, g, flat]
  | cons k s ih => rw [flat_cons, gL_append, gL_tok, ih, show k :: s = [k] ++ s from rfl, g_append]

lemma tok_succ (k : ℕ) : tok (k + 1) = 0 :: tok k := by
  simp [tok, List.replicate_succ]

lemma tok_getD (k : ℕ) : ∀ N, N < k + 2 → (tok k).getD N 0 = if N = k then 1 else 0 := by
  induction k with
  | zero =>
    intro N hN
    interval_cases N <;> rfl
  | succ k ih =>
    intro N hN
    rw [tok_succ]
    rcases N with _ | N
    · simp
    · rw [List.getD_cons_succ, ih N (by omega)]
      simp

lemma tok_take (k : ℕ) : (tok k).take (k + 1) ++ [0] = tok k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [tok_succ, List.take_succ_cons, List.cons_append, ih]

/-- A prefix of the word of a token list that ends with a letter 1, followed by a letter 0, is
the word of a prefix of the token list. -/
lemma one_boundary : ∀ (S : List ℕ) (N : ℕ), N < (flat S).length → (flat S).getD N 0 = 1 →
    ∃ q ≤ S.length, (flat S).take (N + 1) ++ [0] = flat (S.take q)
  | [], N, hN, _ => by simp [flat] at hN
  | k :: S, N, hN, h1 => by
    have hk : (tok k).length = k + 2 := by simp [tok]
    rw [flat_cons] at hN h1 ⊢
    rw [List.length_append, hk] at hN
    rcases lt_or_ge N (k + 2) with h | h
    · rw [List.getD_append _ _ _ _ (by omega), tok_getD k N h] at h1
      have hNk : N = k := by
        by_contra hne
        rw [if_neg hne] at h1
        exact absurd h1 (by norm_num)
      subst hNk
      refine ⟨1, by simp, ?_⟩
      rw [List.take_append_of_le_length (by omega), tok_take]
      simp [flat]
    · rw [List.getD_append_right _ _ _ _ (by omega), hk] at h1
      obtain ⟨q, hq, he⟩ := one_boundary S (N - (k + 2)) (by omega) h1
      refine ⟨q + 1, by simp; omega, ?_⟩
      rw [List.take_append, List.take_of_length_le (by omega), hk,
        show N + 1 - (k + 2) = N - (k + 2) + 1 by omega, List.append_assoc, he]
      simp [flat_cons]

/-- At the n-th 1, -4.0181 <= D <= -0.13. -/
lemma D_ones (n : ℕ) : -4.0181 ≤ D (a n) ∧ D (a n) ≤ -0.13 := by
  have hinf := ones_infinite
  have hWt : W (Nat.nth (fun i => W i = 1) (n - 1)) = 1 := Nat.nth_mem_of_infinite hinf (n - 1)
  have ha : a n = Nat.nth (fun i => W i = 1) (n - 1) + 1 := rfl
  obtain ⟨t, ht⟩ : ∃ t, t = Nat.nth (fun i => W i = 1) (n - 1) := ⟨_, rfl⟩
  rw [← ht] at hWt ha
  rw [ha]
  have hlen : t + 2 ≤ (Q (t + 1)).length := by have := Q_length (t + 1); omega
  have hWq : (flat (tau^[3 * (t + 1)] [2])).getD t 0 = 1 := by
    have := W_eq (t + 1) t (by omega)
    rw [hWt] at this
    exact this.symm
  have hlen' : t < (flat (tau^[3 * (t + 1)] [2])).length := by unfold Q at hlen; omega
  obtain ⟨q, hq, he⟩ := one_boundary _ t hlen' hWq
  have hD : D (t + 1) = gL ((Q (t + 1)).take (t + 1)) := by
    obtain ⟨h1, h2⟩ := counts_eq (t + 1) (t + 1) (by omega)
    simp [D, gL, h1, h2]
  have hg : gL ((Q (t + 1)).take (t + 1)) = g ((tau^[3 * (t + 1)] [2]).take q) - 1 := by
    have h := congrArg gL he
    rw [gL_append, gL_flat] at h
    have h0 : gL [0] = 1 := by simp [gL]
    unfold Q
    linarith
  have hw := window_image (3 * t + 2) 2 (by norm_num) q
    (by rw [show 3 * t + 2 + 1 = 3 * (t + 1) by ring]; exact hq)
  rw [show 3 * t + 2 + 1 = 3 * (t + 1) by ring] at hw
  rw [hD, hg]
  obtain ⟨hw1, hw2⟩ := hw
  constructor <;> linarith

/-! ### The first letters -/

/-- A linear scan of a word, checking 26181 (z + 1) < 10000 (t + 1) at each letter 1. -/
def chk : List ℕ → ℕ → ℕ → Bool
  | [], _, _ => true
  | x :: l, t, z =>
    if x = 1 then decide (26181 * (z + 1) < 10000 * (t + 1)) && chk l (t + 1) (z + 1)
    else chk l (t + 1) z

lemma chk_spec : ∀ (L : List ℕ) (t z : ℕ), chk L t z = true →
    ∀ i < L.length, L.getD i 0 = 1 →
      26181 * (z + (L.take (i + 1)).count 1) < 10000 * (t + i + 1) := by
  intro L
  induction L with
  | nil =>
    intro t z _ i hi
    simp at hi
  | cons x l ih =>
    intro t z h i hi hx
    by_cases h1 : x = 1
    · subst h1
      have h' : 26181 * (z + 1) < 10000 * (t + 1) ∧ chk l (t + 1) (z + 1) = true := by
        simpa [chk] using h
      rcases i with _ | i
      · simpa using h'.1
      · have := ih (t + 1) (z + 1) h'.2 i (by simp at hi; omega) (by simpa using hx)
        have e : ((1 :: l).take (i + 1 + 1)).count 1 = (l.take (i + 1)).count 1 + 1 := by
          simp [List.take_succ_cons, List.count_cons]
        rw [e]
        omega
    · have h' : chk l (t + 1) z = true := by simpa [chk, h1] using h
      rcases i with _ | i
      · simp at hx
        exact absurd hx h1
      · have := ih (t + 1) z h' i (by simp at hi; omega) (by simpa using hx)
        have e : ((x :: l).take (i + 1 + 1)).count 1 = (l.take (i + 1)).count 1 := by
          simp [List.take_succ_cons, List.count_cons, h1]
        rw [e]
        omega

lemma Q2_length : (Q 2).length = 76 := by decide +kernel

lemma chk_word : chk (Q 2) 0 0 = true := by decide +kernel

lemma Q2_ones : (Q 2).count 1 = 21 := by decide +kernel

lemma upper_small (n : ℕ) (hn : 1 ≤ n) (ha : a n ≤ 76) : m1 - (a n : ℝ) / n < 1 := by
  obtain ⟨hm1, hm2⟩ := m1_bounds
  obtain ⟨hO, -⟩ := a_spec n hn
  have hinf := ones_infinite
  have hWp : W (Nat.nth (fun i => W i = 1) (n - 1)) = 1 := Nat.nth_mem_of_infinite hinf (n - 1)
  have ha' : a n = Nat.nth (fun i => W i = 1) (n - 1) + 1 := rfl
  obtain ⟨t, ht⟩ : ∃ t, t = Nat.nth (fun i => W i = 1) (n - 1) := ⟨_, rfl⟩
  rw [← ht] at hWp ha'
  have hlen := Q2_length
  have hW : (Q 2).getD t 0 = 1 := by rw [← W_eq 2 t (by omega)]; exact hWp
  have hc := chk_spec (Q 2) 0 0 chk_word t (by omega) hW
  have hO' : ((Q 2).take (t + 1)).count 1 = n := by
    rw [← (counts_eq 2 (t + 1) (by omega)).2, ← ha', hO]
  rw [hO'] at hc
  simp only [zero_add] at hc
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hc' : (26181 : ℝ) * n < 10000 * (a n) := by
    rw [ha']
    exact_mod_cast hc
  have h1 : 2.6181 < (a n : ℝ) / n := by
    rw [lt_div_iff₀ hnpos]
    linarith
  linarith

lemma upper_large (n : ℕ) (hn : 1 ≤ n) (ha : 76 < a n) : m1 - (a n : ℝ) / n < 1 := by
  have hinf := ones_infinite
  have hOp : O (Nat.nth (fun i => W i = 1) (n - 1)) = n - 1 :=
    Nat.count_nth_of_infinite hinf (n - 1)
  have ha' : a n = Nat.nth (fun i => W i = 1) (n - 1) + 1 := rfl
  have hO76 : O 76 = 21 := by
    rw [(counts_eq 2 76 (by rw [Q2_length])).2, ← Q2_length, List.take_length, Q2_ones]
  have hmono : O 76 ≤ O (Nat.nth (fun i => W i = 1) (n - 1)) :=
    Nat.count_monotone _ (by omega)
  have hn22 : 22 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn22' : (22 : ℝ) ≤ n := by exact_mod_cast hn22
  have hdev := a_dev n hn
  have hD := D_ones n
  have e : m1 - (a n : ℝ) / n = -D (a n) / n := by
    field_simp
    linarith
  rw [e, div_lt_one hnpos]
  linarith [hD.1]

/-- Kimberling's conjecture: a(n)/n tends to a number m = 3.61..., and 0 < m - a(n)/n < 1
for n >= 1. -/
theorem conjecture : ∃ m : ℝ, (3.61 ≤ m ∧ m < 3.62) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 m) ∧
    ∀ n : ℕ, 1 ≤ n → 0 < m - (a n : ℝ) / n ∧ m - (a n : ℝ) / n < 1 := by
  obtain ⟨hm1, hm2⟩ := m1_bounds
  refine ⟨m1, ⟨by linarith, by linarith⟩, ?_, ?_⟩
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun n : ℕ => 4.0181 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 4.0181
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hdev := a_dev n hn
    obtain ⟨hD1, hD2⟩ := D_ones n
    have e : (a n : ℝ) / n - m1 = D (a n) / n := by
      field_simp
      linarith
    rw [Real.norm_eq_abs, e, abs_div, abs_of_pos hnpos]
    gcongr
    rw [abs_le]
    constructor <;> linarith
  · intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hdev := a_dev n hn
    obtain ⟨hD1, hD2⟩ := D_ones n
    have e : m1 - (a n : ℝ) / n = -D (a n) / n := by
      field_simp
      linarith
    constructor
    · rw [e]
      exact div_pos (by linarith) hnpos
    · rcases le_or_gt (a n) 76 with h | h
      · exact upper_small n hn h
      · exact upper_large n hn h

end OMA.S_oeis_a288218

theorem OMA.solution : type_of% @OMA.S_oeis_a288218.main :=
  OMA.S_oeis_a288218.conjecture

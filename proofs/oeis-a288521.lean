import OMAStatements.S_oeis_a288521

namespace OMA.S_oeis_a288521

open Filter Topology





/-! ### One pass -/

/-- A word is closed when the pass over it followed by any word is the pass over it followed by
the pass over that word. -/
def Closed (u : List ℕ) : Prop := ∀ y, step (u ++ y) = step u ++ step y

lemma closed_append {u v : List ℕ} (hu : Closed u) (hv : Closed v) : Closed (u ++ v) := by
  intro y
  rw [List.append_assoc, hu (v ++ y), hv y, hu v, List.append_assoc]

/-! ### Tokens -/

/-- The tokens T0 = 10, T1 = 010, T2 = 0010. -/
def tok : ℕ → List ℕ
  | 0 => [1, 0]
  | 1 => [0, 1, 0]
  | _ => [0, 0, 1, 0]

/-- All tokens are 0, 1 or 2. -/
def Valid (s : List ℕ) : Prop := ∀ k ∈ s, k ≤ 2

lemma tok_closed (k : ℕ) (hk : k ≤ 2) : Closed (tok k) := by
  interval_cases k <;> exact fun _ => rfl

/-- The word of a list of tokens. -/
def flat (s : List ℕ) : List ℕ := s.flatMap tok

/-- The images of the tokens under one pass: T0 -> T1, T1 -> T2, T2 -> T1 T0 T0. -/
def tauT : ℕ → List ℕ
  | 0 => [1]
  | 1 => [2]
  | _ => [1, 0, 0]

/-- The token morphism. -/
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

lemma step_tok (k : ℕ) (hk : k ≤ 2) : step (tok k) = flat (tauT k) := by
  interval_cases k <;> rfl

lemma step_flat (s : List ℕ) (hs : Valid s) : step (flat s) = flat (tau s) := by
  induction s with
  | nil => rfl
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    rw [flat_cons, tok_closed k hk, step_tok k hk, ih hs', tau_cons, flat_append]

lemma flat_closed (s : List ℕ) (hs : Valid s) : Closed (flat s) := by
  induction s with
  | nil => exact fun _ => rfl
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    rw [flat_cons]
    exact closed_append (tok_closed k hk) (ih hs')

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

/-! ### The iterates -/

/-- X n: the word of the tokens tau^n(T1). -/
def X (n : ℕ) : List ℕ := flat (tau^[n] [1])

/-- Iterate n + 1 is X n followed by a letter 1. -/
lemma iter_eq (n : ℕ) : iter (n + 1) = X n ++ [1] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hv := tauIter_valid n _ (valid_single (show 1 ≤ 2 by norm_num))
    rw [show iter (n + 1 + 1) = step (iter (n + 1)) from rfl, ih]
    unfold X
    rw [flat_closed _ hv [1], step_flat _ hv, Function.iterate_succ_apply' tau n]
    rfl

/-- X (n + 2) is X n followed by the word of tau^n(T0 T0). -/
lemma X_two (n : ℕ) : X (n + 2) = X n ++ flat (tau^[n] [0, 0]) := by
  unfold X
  rw [Function.iterate_add_apply, show tau^[2] [1] = [1] ++ [0, 0] from rfl,
    tauIter_append, flat_append]

lemma X_prefix_two (n : ℕ) : X n <+: X (n + 2) := by
  rw [X_two]
  exact List.prefix_append _ _

lemma X_length_lin (n : ℕ) : n + 3 ≤ (X n).length ∧ n + 4 ≤ (X (n + 1)).length := by
  induction n with
  | zero => decide
  | succ n ih =>
    obtain ⟨h0, h1⟩ := ih
    refine ⟨h1, ?_⟩
    rw [show n + 1 + 1 = n + 2 from rfl, X_two, List.length_append]
    have h2 := flat_length_ge (tau^[n] [0, 0]) (tauIter_valid _ _ (by intro y hy; simp at hy; omega))
    have h3 := tauIter_length_ge n [0, 0]
    simp only [List.length_cons, List.length_nil] at h3
    omega

lemma X_length (n : ℕ) : n + 3 ≤ (X n).length := (X_length_lin n).1

lemma getD_prefix {l₁ l₂ : List ℕ} (h : l₁ <+: l₂) {i : ℕ} (hi : i < l₁.length) :
    l₁.getD i 0 = l₂.getD i 0 := by
  obtain ⟨s, rfl⟩ := h
  rw [List.getD_append _ _ _ _ hi]

/-! ### The limiting word -/

/-- The residue of the words X n whose limit is W: iterate 2k + 2 is X (2k + 1) followed by 1. -/
def res : ℕ := 1

lemma res_pos : 1 ≤ res := by decide

/-- V k: the word X (2k + res). -/
def V (k : ℕ) : List ℕ := X (2 * k + res)

lemma V_prefix_succ (k : ℕ) : V k <+: V (k + 1) := by
  unfold V
  rw [show 2 * (k + 1) + res = 2 * k + res + 2 by ring]
  exact X_prefix_two _

lemma V_prefix {k k' : ℕ} (h : k ≤ k') : V k <+: V k' := by
  induction k', h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ k' _ ih => exact ih.trans (V_prefix_succ k')

lemma V_length (k : ℕ) : k + 3 ≤ (V k).length := by
  unfold V
  have := X_length (2 * k + res)
  omega

lemma iter_V (i : ℕ) : iter (2 * (i + 1)) = V i ++ [1] := by
  rw [show 2 * (i + 1) = 2 * i + res + 1 by unfold res; ring]
  exact iter_eq _

lemma W_eq (k i : ℕ) (hi : i < (V k).length) : W i = (V k).getD i 0 := by
  have hi' : i < (V i).length := by have := V_length i; omega
  have hW : W i = (V i).getD i 0 := by
    unfold W
    rw [iter_V, List.getD_append _ _ _ _ hi']
  rw [hW]
  rcases le_total i k with h | h
  · exact getD_prefix (V_prefix h) hi'
  · exact (getD_prefix (V_prefix h) hi).symm

/-! ### The Perron root -/

lemma lam_exists : ∃ x : ℝ, 1.521379 ≤ x ∧ x ≤ 1.52138 ∧ x ^ 3 - x - 2 = 0 := by
  have hc : ContinuousOn (fun x : ℝ => x ^ 3 - x - 2) (Set.Icc 1.521379 1.52138) := by
    fun_prop
  have h := intermediate_value_Icc (show (1.521379 : ℝ) ≤ 1.52138 by norm_num) hc
  have h0 : (0 : ℝ) ∈ Set.Icc ((fun x : ℝ => x ^ 3 - x - 2) 1.521379)
      ((fun x : ℝ => x ^ 3 - x - 2) 1.52138) := by
    constructor <;> norm_num
  obtain ⟨x, ⟨hx1, hx2⟩, hx⟩ := h h0
  exact ⟨x, hx1, hx2, hx⟩

/-- The Perron root, 1.52137..., the growth rate of the iterates. -/
noncomputable def lam : ℝ := Classical.choose lam_exists

lemma lam_spec : 1.521379 ≤ lam ∧ lam ≤ 1.52138 ∧ lam ^ 3 - lam - 2 = 0 :=
  Classical.choose_spec lam_exists

/-- The limiting number of letters 0 per letter 1, (lam^2 + lam)/2 = 1/(lam - 1) = 1.91798... -/
noncomputable def cc : ℝ := (lam ^ 2 + lam) / 2

lemma cc_bounds : 1.917986 ≤ cc ∧ cc ≤ 1.917989 := by
  obtain ⟨h1, h2, -⟩ := lam_spec
  unfold cc
  constructor <;> nlinarith

/-! ### Deviation of words and token lists -/

/-- For a word, the number of letters 0 minus c times the number of letters 1. -/
noncomputable def gL (L : List ℕ) : ℝ := (L.count 0 : ℝ) - cc * (L.count 1 : ℝ)

lemma gL_append (u v : List ℕ) : gL (u ++ v) = gL u + gL v := by
  simp only [gL, List.count_append]
  push_cast
  ring

/-- The deviation of a token list: the deviation of its word. -/
noncomputable def g (s : List ℕ) : ℝ := gL (flat s)

lemma g_append (u v : List ℕ) : g (u ++ v) = g u + g v := by
  unfold g
  rw [flat_append, gL_append]

lemma g_eq (s : List ℕ) (z o : ℕ) (hz : (flat s).count 0 = z) (ho : (flat s).count 1 = o) :
    g s = z - cc * o := by
  unfold g gL
  rw [hz, ho]

lemma g_tok (k : ℕ) (hk : k ≤ 2) :
    g (tau (tau [k])) + lam * g (tau [k]) + (lam ^ 2 - 1) * g [k] = 0 := by
  obtain ⟨-, -, hf⟩ := lam_spec
  interval_cases k
  · rw [g_eq _ 3 1 (by decide) (by decide), g_eq _ 2 1 (by decide) (by decide),
      g_eq _ 1 1 (by decide) (by decide)]
    unfold cc
    push_cast
    linear_combination (-1 - 1 / 2 * lam) * hf
  · rw [g_eq _ 4 3 (by decide) (by decide), g_eq _ 3 1 (by decide) (by decide),
      g_eq _ 2 1 (by decide) (by decide)]
    unfold cc
    push_cast
    linear_combination (-1 - 1 / 2 * lam) * hf
  · rw [g_eq _ 7 3 (by decide) (by decide), g_eq _ 4 3 (by decide) (by decide),
      g_eq _ 3 1 (by decide) (by decide)]
    unfold cc
    push_cast
    linear_combination (-2 - 1 / 2 * lam) * hf

/-- The deviation has no component along the Perron root: it follows f(x)/(x - lam). -/
lemma g_rec (s : List ℕ) (hs : Valid s) :
    g (tau (tau s)) + lam * g (tau s) + (lam ^ 2 - 1) * g s = 0 := by
  induction s with
  | nil => simp [g, gL, flat, tau]
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    rw [show k :: s = [k] ++ s from rfl, tau_append, tau_append, g_append, g_append, g_append]
    linarith [g_tok k hk, ih hs']

/-! ### The quadratic form -/

/-- u x j: the deviation of tau^j(x). -/
noncomputable def u (x j : ℕ) : ℝ := g (tau^[j] [x])

/-- The quadratic form along the deviations. -/
noncomputable def E (x j : ℕ) : ℝ :=
  u x (j + 1) ^ 2 + lam * u x (j + 1) * u x j + (lam ^ 2 - 1) * u x j ^ 2

lemma u_rec (x j : ℕ) (hx : x ≤ 2) :
    u x (j + 2) = -lam * u x (j + 1) - (lam ^ 2 - 1) * u x j := by
  have hv : Valid (tau^[j] [x]) := tauIter_valid j _ (valid_single hx)
  have e2 : tau^[j + 2] [x] = tau (tau (tau^[j] [x])) := by
    rw [show j + 2 = j + 1 + 1 from rfl, Function.iterate_succ_apply',
      Function.iterate_succ_apply']
  have e1 : tau^[j + 1] [x] = tau (tau^[j] [x]) := Function.iterate_succ_apply' _ _ _
  have h := g_rec _ hv
  unfold u
  rw [e2, e1]
  linarith

lemma E_succ (x j : ℕ) (hx : x ≤ 2) : E x (j + 1) = (lam ^ 2 - 1) * E x j := by
  unfold E
  rw [show j + 1 + 1 = j + 2 from rfl, u_rec x j hx]
  ring

/-- The form is positive definite: it bounds the square of its second argument. -/
lemma E_ge (x j : ℕ) : 0.7359 * u x j ^ 2 ≤ E x j := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  unfold E
  have h : u x (j + 1) ^ 2 + lam * u x (j + 1) * u x j + (lam ^ 2 - 1) * u x j ^ 2 =
      (u x (j + 1) + lam / 2 * u x j) ^ 2 + (3 / 4 * lam ^ 2 - 1) * u x j ^ 2 := by ring
  rw [h]
  have h2 : 0.7359 ≤ 3 / 4 * lam ^ 2 - 1 := by nlinarith
  have h3 : 0 ≤ u x j ^ 2 := sq_nonneg _
  nlinarith [sq_nonneg (u x (j + 1) + lam / 2 * u x j)]

lemma E_nonneg (x j : ℕ) : 0 ≤ E x j := by
  have := E_ge x j
  have h3 : 0 ≤ u x j ^ 2 := sq_nonneg _
  linarith

lemma E_zero : E 0 0 = 1 := by
  obtain ⟨-, -, hf⟩ := lam_spec
  have e : E 0 0 = u 0 1 ^ 2 + lam * u 0 1 * u 0 0 + (lam ^ 2 - 1) * u 0 0 ^ 2 := rfl
  rw [e, show u 0 1 = g [1] from rfl, show u 0 0 = g [0] from rfl,
    g_eq [1] 2 1 (by decide) (by decide), g_eq [0] 1 1 (by decide) (by decide)]
  unfold cc
  push_cast
  linear_combination (-1 + 3 / 4 * lam ^ 2 + 1 / 4 * lam ^ 3) * hf

lemma E_le (j : ℕ) : E 0 j ≤ 1.3225 ^ j := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  induction j with
  | zero => simp [E_zero]
  | succ j ih =>
    rw [E_succ 0 j (by norm_num), pow_succ (1.3225 : ℝ) j]
    have h0 := E_nonneg 0 j
    have hq : lam ^ 2 - 1 ≤ 1.3225 := by nlinarith
    have hq0 : 0 ≤ lam ^ 2 - 1 := by nlinarith
    have h1 := mul_le_mul hq ih h0 (by norm_num)
    linarith

lemma u_bound (j : ℕ) : |u 0 j| ≤ 1.17 * 1.15 ^ j := by
  apply abs_le_of_sq_le_sq _ (by positivity)
  have h1 := E_ge 0 j
  have h2 := E_le j
  have e : (1.17 * (1.15 : ℝ) ^ j) ^ 2 = 1.3689 * 1.3225 ^ j := by
    rw [mul_pow, ← pow_mul, mul_comm j 2, pow_mul]
    norm_num
  rw [e]
  have hp : 0 ≤ (1.3225 : ℝ) ^ j := by positivity
  nlinarith

lemma u_one (J : ℕ) : g (tau^[J] [1]) = u 0 (J + 1) := by
  unfold u
  rw [Function.iterate_succ_apply]
  rfl

/-! ### Prefixes of token lists -/

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

lemma gtok_bound (x : ℕ) (hx : x ≤ 2) : |g [x]| ≤ 1.1 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  interval_cases x
  · rw [g_eq [0] 1 1 (by decide) (by decide), abs_le]; constructor <;> norm_num <;> linarith
  · rw [g_eq [1] 2 1 (by decide) (by decide), abs_le]; constructor <;> norm_num <;> linarith
  · rw [g_eq [2] 3 1 (by decide) (by decide), abs_le]; constructor <;> norm_num <;> linarith

/-- |g| over the prefixes of tau^J(x). -/
lemma prefix_bound (J : ℕ) :
    ∀ x, x ≤ 2 → ∀ i, |g ((tau^[J] [x]).take i)| ≤ 16.8 * 1.15 ^ J - 15.7 := by
  induction J with
  | zero =>
    intro x hx i
    simp only [Function.iterate_zero, id, pow_zero]
    rcases i with _ | i
    · norm_num [g, flat, gL]
    · rw [show [x].take (i + 1) = [x] by simp]
      have := gtok_bound x hx
      norm_num
      linarith
  | succ J ih =>
    intro x hx i
    have hp : 0 ≤ (1.15 : ℝ) ^ J := by positivity
    have hA := u_bound J
    have hB : |g (tau^[J] [1])| ≤ 1.17 * 1.15 ^ (J + 1) := by rw [u_one]; exact u_bound (J + 1)
    rw [pow_succ] at hB
    rw [Function.iterate_succ_apply, tau_single, pow_succ]
    interval_cases x
    · exact le_trans (ih 1 (by norm_num) i) (by nlinarith)
    · exact le_trans (ih 2 (by norm_num) i) (by nlinarith)
    · rw [show tauT 2 = [1] ++ ([0] ++ [0]) from rfl, tauIter_append, tauIter_append]
      have h1 := take_append_le _ _ _ _ (ih 0 (by norm_num)) (ih 0 (by norm_num))
      have h2 := take_append_le _ _ _ _ (ih 1 (by norm_num)) h1 i
      refine le_trans h2 (max_le (by nlinarith) ?_)
      show |g (tau^[J] [1])| + max (16.8 * 1.15 ^ J - 15.7) (|u 0 J| + (16.8 * 1.15 ^ J - 15.7)) ≤
        16.8 * (1.15 ^ J * 1.15) - 15.7
      have hm : max (16.8 * (1.15 : ℝ) ^ J - 15.7) (|u 0 J| + (16.8 * 1.15 ^ J - 15.7)) ≤
          |u 0 J| + (16.8 * 1.15 ^ J - 15.7) :=
        max_le (by linarith [abs_nonneg (u 0 J)]) le_rfl
      nlinarith

/-! ### Letters -/

lemma gL_tok_take (k : ℕ) (hk : k ≤ 2) (r : ℕ) : |gL ((tok k).take r)| ≤ 3 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hz : ((tok k).take r).count 0 ≤ 3 := by
    calc ((tok k).take r).count 0 ≤ (tok k).count 0 := List.Sublist.count_le _ (List.take_sublist _ _)
      _ ≤ 3 := by interval_cases k <;> decide
  have ho : ((tok k).take r).count 1 ≤ 1 := by
    calc ((tok k).take r).count 1 ≤ (tok k).count 1 := List.Sublist.count_le _ (List.take_sublist _ _)
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

/-! ### The length of the words X n -/

/-- The Perron weight of a token: 1, lam, lam^2. -/
noncomputable def wt : ℕ → ℝ
  | 0 => 1
  | 1 => lam
  | _ => lam ^ 2

/-- The weight of a token list; tau multiplies it by lam. -/
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
    interval_cases k <;> simp [Phi, tauT, wt] <;>
      first | ring1 | linear_combination (-1 : ℝ) * hf

lemma Phi_iter (J : ℕ) : Phi (tau^[J] [1]) = lam ^ (J + 1) := by
  induction J with
  | zero => simp [Phi, wt]
  | succ J ih =>
    rw [Function.iterate_succ_apply', Phi_tau _ (tauIter_valid J _ (valid_single (by norm_num))),
      ih, pow_succ]
    ring

lemma length_ge_Phi (s : List ℕ) (hs : Valid s) : 1.72 * Phi s ≤ ((flat s).length : ℝ) := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  induction s with
  | nil => simp [Phi, flat]
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    rw [flat_cons, List.length_append, show k :: s = [k] ++ s from rfl, Phi_append]
    push_cast
    have := ih hs'
    have hk' : 1.72 * Phi [k] ≤ ((tok k).length : ℝ) := by
      interval_cases k <;> simp [Phi, wt, tok] <;> nlinarith
    linarith

lemma X_length_ge (J : ℕ) : 1.72 * lam ^ (J + 1) ≤ ((X J).length : ℝ) := by
  have h := length_ge_Phi _ (tauIter_valid J _ (valid_single (show 1 ≤ 2 by norm_num)))
  rw [Phi_iter] at h
  exact h

/-! ### Counting along the limiting word -/

lemma W_le (i : ℕ) : W i ≤ 1 := by
  have hi : i < (V i).length := by have := V_length i; omega
  rw [W_eq i i hi, List.getD_eq_getElem _ _ hi]
  exact flat_letters _ _ (List.getElem_mem hi)

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

lemma pow_bound (J : ℕ) (hJ : 13 ≤ J) : 19.4 * 1.15 ^ J < 0.24 * (1.72 * lam ^ (J + 1)) := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  induction J, hJ using Nat.le_induction with
  | base =>
    have : (1.521379 : ℝ) ^ 14 ≤ lam ^ 14 := pow_le_pow_left₀ (by norm_num) hl1 14
    norm_num at this ⊢
    linarith
  | succ J hJ ih =>
    rw [pow_succ lam (J + 1), pow_succ (1.15 : ℝ) J]
    have hp : 0 ≤ lam ^ (J + 1) := by positivity
    have h := mul_le_mul_of_nonneg_left (show (1.15 : ℝ) ≤ lam by linarith) hp
    nlinarith

lemma V6_length : (V 6).length = 672 := by decide +kernel

/-- For N > 672 there is a level J >= 13 with 1.72 lam^(J+1) < N and |D(N)| <= 19.4 * 1.15^J. -/
lemma level (N : ℕ) (hN : 672 < N) :
    ∃ J : ℕ, 13 ≤ J ∧ 1.72 * lam ^ (J + 1) < (N : ℝ) ∧ |D N| ≤ 19.4 * 1.15 ^ J := by
  have hex : ∃ k, N ≤ (V k).length := ⟨N, by have := V_length N; omega⟩
  classical
  have hk : N ≤ (V (Nat.find hex)).length := Nat.find_spec hex
  have h6 := V6_length
  have hk7 : 7 ≤ Nat.find hex := by
    by_contra h
    have := (V_prefix (show Nat.find hex ≤ 6 by omega)).length_le
    omega
  have hmin : (V (Nat.find hex - 1)).length < N := by
    have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    omega
  have h2 : 2 * Nat.find hex + res = 2 * (Nat.find hex - 1) + res + 2 := by omega
  have e : V (Nat.find hex) = X (2 * (Nat.find hex - 1) + res) ++
      flat (tau^[2 * (Nat.find hex - 1) + res] [0, 0]) := by
    rw [← X_two, ← h2]
    rfl
  have e' : V (Nat.find hex - 1) = X (2 * (Nat.find hex - 1) + res) := rfl
  set J := 2 * (Nat.find hex - 1) + res with hJ
  have hr := res_pos
  refine ⟨J, by omega, ?_, ?_⟩
  · have hl := X_length_ge J
    rw [e'] at hmin
    have : ((X J).length : ℝ) < N := by exact_mod_cast hmin
    linarith
  · rw [D_eq (Nat.find hex) N hk, e]
    rw [e'] at hmin
    rw [List.take_append, List.take_of_length_le hmin.le, gL_append]
    obtain ⟨i, hi⟩ := flat_split (tau^[J] [0, 0]) (tauIter_valid J _ (by intro y hy; simp at hy; omega))
      (N - (X J).length)
    have h00 := take_append_le _ _ _ _ (prefix_bound J 0 (by norm_num)) (prefix_bound J 0 (by norm_num)) i
    rw [← tauIter_append] at h00
    have hA : |g (tau^[J] [0])| ≤ 1.17 * 1.15 ^ J := u_bound J
    have hB : |g (tau^[J] [1])| ≤ 1.17 * 1.15 ^ (J + 1) := by rw [u_one]; exact u_bound (J + 1)
    rw [pow_succ] at hB
    have hp : (1 : ℝ) ≤ 1.15 ^ J := one_le_pow₀ (by norm_num)
    have hm : max (16.8 * (1.15 : ℝ) ^ J - 15.7) (|g (tau^[J] [0])| + (16.8 * 1.15 ^ J - 15.7)) ≤
        |g (tau^[J] [0])| + (16.8 * 1.15 ^ J - 15.7) :=
      max_le (by linarith [abs_nonneg (g (tau^[J] [0]))]) le_rfl
    have hX : gL (X J) = g (tau^[J] [1]) := rfl
    rw [hX]
    have h1 := abs_add_le (g (tau^[J] [1])) (gL ((flat (tau^[J] [0, 0])).take (N - (X J).length)))
    have h3 := abs_sub_abs_le_abs_sub (gL ((flat (tau^[J] [0, 0])).take (N - (X J).length)))
      (g ((tau^[J] [0, 0]).take i))
    have h4 : (tau^[J] [0, 0]) = tau^[J] ([0] ++ [0]) := rfl
    rw [h4] at hi h1 h3 ⊢
    linarith

/-- Over every prefix of W longer than 672 letters, |D| < 0.24 N. -/
lemma D_small (N : ℕ) (hN : 672 < N) : |D N| < 0.24 * (N : ℝ) := by
  obtain ⟨J, hJ, hNr, hD⟩ := level N hN
  have hp := pow_bound J hJ
  linarith

/-- D(N)^2 <= 4000 N for every N. -/
lemma D_sq (N : ℕ) : D N ^ 2 ≤ 4000 * (N : ℝ) := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  rcases le_or_gt N 672 with h | h
  · have h1 := D_triv N
    have hN1 : (N : ℝ) ≤ 672 := by exact_mod_cast h
    have h2 : D N ^ 2 ≤ (cc * N) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have h3 : cc ^ 2 ≤ 3.68 := by nlinarith
    have h4 : (cc * (N : ℝ)) ^ 2 ≤ 3.68 * 672 * N := by
      have : (cc * (N : ℝ)) ^ 2 = cc ^ 2 * N * N := by ring
      rw [this]
      have hc2' : 0 ≤ cc ^ 2 := sq_nonneg _
      have := mul_le_mul h3 hN1 hN0 (by norm_num)
      nlinarith
    linarith
  · obtain ⟨J, hJ, hNr, hD⟩ := level N h
    obtain ⟨hl1, hl2, -⟩ := lam_spec
    have h1 : D N ^ 2 ≤ (19.4 * 1.15 ^ J) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hD 2
    have h2 : ((1.15 : ℝ) ^ J) ^ 2 ≤ lam ^ J := by
      rw [← pow_mul, mul_comm, pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num; linarith) J
    have e : (19.4 * (1.15 : ℝ) ^ J) ^ 2 = 376.36 * ((1.15 : ℝ) ^ J) ^ 2 := by ring
    rw [e] at h1
    have hlp : 0 ≤ lam ^ J := by positivity
    have hNr' : 1.72 * (lam ^ J * lam) < (N : ℝ) := by rw [← pow_succ]; exact hNr
    nlinarith

/-! ### The positions of 0 -/

/-- The limit, (1 + c)/c = lam = 1.52137... -/
noncomputable def m0 : ℝ := (1 + cc) / cc

lemma m0_bounds : 1.52137 ≤ m0 ∧ m0 ≤ 1.52139 := by
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
  have h := D_small (B + 1 + (2 * Z (B + 1) + 1100)) (by omega)
  have hs := O_add_Z (B + 1 + (2 * Z (B + 1) + 1100))
  rw [hconst] at hs
  unfold D at h
  rw [hconst, abs_lt] at h
  obtain ⟨h1, -⟩ := h
  have hO : (O (B + 1 + (2 * Z (B + 1) + 1100)) : ℝ) =
      ((B + 1 + (2 * Z (B + 1) + 1100) : ℕ) : ℝ) - Z (B + 1) := by
    have : (O (B + 1 + (2 * Z (B + 1) + 1100)) : ℝ) + Z (B + 1) =
        ((B + 1 + (2 * Z (B + 1) + 1100) : ℕ) : ℝ) := by exact_mod_cast hs
    linarith
  rw [hO] at h1
  generalize hz : (Z (B + 1) : ℝ) = z at h1
  have hz0 : 0 ≤ z := by rw [← hz]; exact Nat.cast_nonneg _
  have hz' : ((B + 1 + (2 * Z (B + 1) + 1100) : ℕ) : ℝ) = (B : ℝ) + 1 + (2 * z + 1100) := by
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

lemma chk_word : chk (V 6) 0 0 = true := by decide +kernel

lemma bound_small (n : ℕ) (hn : 1 ≤ n) (ha : a n ≤ 672) :
    -1 < m0 - (a n : ℝ) / n ∧ m0 - (a n : ℝ) / n < 1 := by
  obtain ⟨hm1, hm2⟩ := m0_bounds
  obtain ⟨hZ, hO⟩ := a_spec n hn
  have hinf := zeros_infinite
  have hWp : W (Nat.nth (fun i => W i = 0) (n - 1)) = 0 := Nat.nth_mem_of_infinite hinf (n - 1)
  have ha' : a n = Nat.nth (fun i => W i = 0) (n - 1) + 1 := rfl
  set t := Nat.nth (fun i => W i = 0) (n - 1) with ht
  have hlen := V6_length
  have hW : (V 6).getD t 0 = 0 := by rw [← W_eq 6 t (by omega)]; exact hWp
  have hc := chk_spec (V 6) 0 0 chk_word t (by omega) hW
  have hZ' : ((V 6).take (t + 1)).count 0 = n := by
    rw [← (counts_eq 6 (t + 1) (by omega)).1, ← ha', hZ]
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

lemma bound_large (n : ℕ) (hn : 1 ≤ n) (ha : 672 < a n) :
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
  have hP : 1.917986 * (a n : ℝ) ≤ cc * a n := mul_le_mul_of_nonneg_right hc1 hA0
  have hQ1 : 1.917986 * (n : ℝ) ≤ cc * n := mul_le_mul_of_nonneg_right hc1 hnpos.le
  have hQ2 : cc * (n : ℝ) ≤ 1.917989 * n := mul_le_mul_of_nonneg_right hc2 hnpos.le
  have hE : cc * ((a n : ℝ) - n) = cc * a n - cc * n := by ring
  rw [hE] at hD1 hD2 ⊢
  constructor
  · rw [lt_div_iff₀ hnpos, lt_div_iff₀ hc]
    linarith
  · rw [div_lt_iff₀ hnpos, div_lt_iff₀ hc]
    linarith

/-- Kimberling's conjecture: a(n)/n tends to a number m = 1.52..., and -1 < m - a(n)/n < 1
for n >= 1. -/
theorem conjecture : ∃ m : ℝ, (1.52 ≤ m ∧ m < 1.53) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 m) ∧
    ∀ n : ℕ, 1 ≤ n → -1 < m - (a n : ℝ) / n ∧ m - (a n : ℝ) / n < 1 := by
  obtain ⟨hm1, hm2⟩ := m0_bounds
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hc : 0 < cc := by linarith
  have hbound : ∀ n : ℕ, 1 ≤ n → -1 < m0 - (a n : ℝ) / n ∧ m0 - (a n : ℝ) / n < 1 := by
    intro n hn
    rcases le_or_gt (a n) 672 with h | h
    · exact bound_small n hn h
    · exact bound_large n hn h
  refine ⟨m0, ⟨by linarith, by linarith⟩, ?_, hbound⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => Real.sqrt (4000 * 3 / cc ^ 2 / n)) atTop (𝓝 0) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (4000 * 3 / cc ^ 2)).sqrt
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq := D_sq (a n)
  have hb := hbound n hn
  have ha3 : (a n : ℝ) ≤ 3 * n := by
    have h1 : (a n : ℝ) / n < 2.52139 := by linarith [hb.1]
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
  have hD3 : D (a n) ^ 2 ≤ 4000 * (3 * n) := by
    have : (4000 : ℝ) * (a n) ≤ 4000 * (3 * n) := by linarith
    linarith
  have e2 : 4000 * 3 / cc ^ 2 * (cc ^ 2 * (n : ℝ) ^ 2) = 4000 * 3 * n ^ 2 := by
    field_simp
  rw [e2]
  nlinarith [hD3, hnpos]

end OMA.S_oeis_a288521

theorem OMA.solution : type_of% @OMA.S_oeis_a288521.main :=
  OMA.S_oeis_a288521.conjecture

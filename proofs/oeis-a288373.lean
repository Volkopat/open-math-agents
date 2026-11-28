import OMAStatements.S_oeis_a288373

namespace OMA.S_oeis_a288373

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

/-- The rule 1 -> 01 reads its letter alone, so the pass restarts after every letter 1. -/
lemma step_one (u : List ℕ) : ∀ w, step (u ++ 1 :: w) = step (u ++ [1]) ++ step w := by
  refine step_rec (P := fun u => ∀ w, step (u ++ 1 :: w) = step (u ++ [1]) ++ step w)
    ?_ ?_ ?_ ?_ ?_ ?_ u
  · intro w
    rfl
  · intro l ih w
    show 0 :: 0 :: 0 :: 1 :: step (l ++ 1 :: w) = 0 :: 0 :: 0 :: 1 :: step (l ++ [1]) ++ step w
    rw [ih]
    rfl
  · intro l ih w
    show 0 :: 1 :: step (l ++ 1 :: w) = 0 :: 1 :: step (l ++ [1]) ++ step w
    rw [ih]
    rfl
  · intro w
    rfl
  · intro y l ih w
    show 0 :: step ((y + 1) :: l ++ 1 :: w) = 0 :: step ((y + 1) :: l ++ [1]) ++ step w
    rw [ih]
    rfl
  · intro x l ih w
    show (x + 2) :: step (l ++ 1 :: w) = (x + 2) :: step (l ++ [1]) ++ step w
    rw [ih]
    rfl

/-! ### Tokens -/

/-- The token k is the word 0^k 1. -/
def tok (k : ℕ) : List ℕ := List.replicate k 0 ++ [1]

/-- The word of a list of tokens. -/
def flat (s : List ℕ) : List ℕ := s.flatMap tok

/-- The images of the tokens: 01 -> 001, 001 -> 0001.01, 0001 -> 0001.001. -/
def tauT : ℕ → List ℕ
  | 1 => [2]
  | 2 => [3, 1]
  | _ => [3, 2]

/-- The token morphism. -/
def tau (s : List ℕ) : List ℕ := s.flatMap tauT

/-- All tokens are 1, 2 or 3. -/
def Valid (s : List ℕ) : Prop := ∀ k ∈ s, 1 ≤ k ∧ k ≤ 3

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
  rcases k with _ | _ | _ | k <;> simp [tauT] at hx <;> omega

lemma tau_valid (s : List ℕ) : Valid (tau s) := by
  intro x hx
  simp only [tau, List.mem_flatMap] at hx
  obtain ⟨k, -, hk⟩ := hx
  exact tauT_valid k x hk

lemma valid_cons {k : ℕ} {s : List ℕ} (h : Valid (k :: s)) : (1 ≤ k ∧ k ≤ 3) ∧ Valid s :=
  ⟨h k (by simp), fun x hx => h x (by simp [hx])⟩

lemma step_tok (k : ℕ) (hk : 1 ≤ k ∧ k ≤ 3) : step (tok k) = flat (tauT k) := by
  obtain ⟨h1, h3⟩ := hk
  interval_cases k <;> rfl

lemma step_flat (s : List ℕ) (hs : Valid s) : step (flat s) = flat (tau s) := by
  induction s with
  | nil => rfl
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    rw [flat_cons, tau_cons, flat_append, tok, List.append_assoc,
      show [1] ++ flat s = 1 :: flat s from rfl, step_one, ← tok, step_tok k hk, ih hs']

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

lemma valid_three : Valid [3] := by
  intro x hx
  simp at hx
  omega

lemma iter_eq (n : ℕ) : iter (n + 1) = flat (tau^[n] [3]) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show iter (n + 1 + 1) = step (iter (n + 1)) from rfl, ih,
      step_flat _ (tauIter_valid n _ valid_three), Function.iterate_succ_apply']

/-! ### The fixed point -/

lemma tauIter_succ_three (n : ℕ) : tau^[n + 1] [3] = tau^[n] [3] ++ tau^[n] [2] := by
  rw [Function.iterate_succ_apply, tau_single, show tauT 3 = [3] ++ [2] from rfl, tauIter_append]

lemma iter_prefix_succ (n : ℕ) : iter n <+: iter (n + 1) := by
  cases n with
  | zero => exact ⟨[0, 1], rfl⟩
  | succ n =>
    rw [iter_eq n, iter_eq (n + 1), tauIter_succ_three, flat_append]
    exact List.prefix_append _ _

lemma iter_prefix {m n : ℕ} (h : m ≤ n) : iter m <+: iter n := by
  induction n, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n _ ih => exact ih.trans (iter_prefix_succ n)

lemma flat_length_pos (s : List ℕ) (hs : s ≠ []) : 1 ≤ (flat s).length := by
  rcases s with _ | ⟨k, s⟩
  · exact absurd rfl hs
  · rw [flat_cons, List.length_append]
    simp [tok]
    omega

lemma tauT_ne_nil (k : ℕ) : tauT k ≠ [] := by
  rcases k with _ | _ | _ | k <;> simp [tauT]

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

lemma iter_length (n : ℕ) : n + 2 ≤ (iter n).length := by
  induction n with
  | zero => simp [iter]
  | succ n ih =>
    cases n with
    | zero => simp [iter, step]
    | succ n =>
      rw [iter_eq (n + 1), tauIter_succ_three, flat_append, List.length_append, ← iter_eq n]
      have := flat_length_pos (tau^[n] [2]) (tauIter_ne_nil n [2] (by simp))
      omega

lemma getD_prefix {l₁ l₂ : List ℕ} (h : l₁ <+: l₂) {i : ℕ} (hi : i < l₁.length) :
    l₁.getD i 0 = l₂.getD i 0 := by
  obtain ⟨s, rfl⟩ := h
  rw [List.getD_append _ _ _ _ hi]

lemma W_eq (m i : ℕ) (hi : i < (iter m).length) : W i = (iter m).getD i 0 := by
  unfold W
  rcases le_total (i + 1) m with h | h
  · exact getD_prefix (iter_prefix h) (by have := iter_length (i + 1); omega)
  · exact (getD_prefix (iter_prefix h) hi).symm

/-! ### The Perron root -/

lemma lam_exists : ∃ x : ℝ, 1.8019 ≤ x ∧ x ≤ 1.802 ∧ x ^ 3 - x ^ 2 - 2 * x + 1 = 0 := by
  have hc : ContinuousOn (fun x : ℝ => x ^ 3 - x ^ 2 - 2 * x + 1) (Set.Icc 1.8019 1.802) := by
    fun_prop
  have h := intermediate_value_Icc (show (1.8019 : ℝ) ≤ 1.802 by norm_num) hc
  have h0 : (0 : ℝ) ∈ Set.Icc ((fun x : ℝ => x ^ 3 - x ^ 2 - 2 * x + 1) 1.8019)
      ((fun x : ℝ => x ^ 3 - x ^ 2 - 2 * x + 1) 1.802) := by
    constructor <;> norm_num
  obtain ⟨x, ⟨hx1, hx2⟩, hx⟩ := h h0
  exact ⟨x, hx1, hx2, hx⟩

/-- The Perron root of the token morphism, 2 cos(pi/7) = 1.80193... -/
noncomputable def lam : ℝ := Classical.choose lam_exists

lemma lam_spec : 1.8019 ≤ lam ∧ lam ≤ 1.802 ∧ lam ^ 3 - lam ^ 2 - 2 * lam + 1 = 0 :=
  Classical.choose_spec lam_exists

/-- The limiting number of letters 0 per letter 1. -/
noncomputable def cc : ℝ := lam ^ 2 - 1

lemma cc_bounds : 2.24684 ≤ cc ∧ cc ≤ 2.24721 := by
  obtain ⟨h1, h2, -⟩ := lam_spec
  unfold cc
  constructor <;> nlinarith

/-! ### Deviation and weight of token lists -/

/-- For a list of tokens, the number of letters 0 minus c times the number of letters 1. -/
noncomputable def g (s : List ℕ) : ℝ := (s.sum : ℝ) - cc * (s.length : ℝ)

lemma g_append (u v : List ℕ) : g (u ++ v) = g u + g v := by
  simp only [g, List.sum_append, List.length_append]
  push_cast
  ring

lemma g_single (k : ℕ) : g [k] = k - cc := by
  simp [g]

lemma counts (s : List ℕ) (hs : Valid s) :
    s.sum = s.count 1 + 2 * s.count 2 + 3 * s.count 3 ∧
      s.length = s.count 1 + s.count 2 + s.count 3 := by
  induction s with
  | nil => simp
  | cons k s ih =>
    obtain ⟨⟨hk1, hk3⟩, hs'⟩ := valid_cons hs
    obtain ⟨h1, h2⟩ := ih hs'
    interval_cases k <;> simp [List.count_cons] <;> omega

lemma tau_counts (s : List ℕ) (hs : Valid s) :
    (tau s).count 1 = s.count 2 ∧ (tau s).count 2 = s.count 1 + s.count 3 ∧
      (tau s).count 3 = s.count 2 + s.count 3 := by
  induction s with
  | nil => simp [tau]
  | cons k s ih =>
    obtain ⟨⟨hk1, hk3⟩, hs'⟩ := valid_cons hs
    obtain ⟨h1, h2, h3⟩ := ih hs'
    rw [tau_cons, List.count_append, List.count_append, List.count_append]
    interval_cases k <;> simp [tauT, List.count_cons] <;> omega

lemma g_counts (s : List ℕ) (hs : Valid s) :
    g s = (1 - cc) * (s.count 1 : ℝ) + (2 - cc) * (s.count 2 : ℝ) + (3 - cc) * (s.count 3 : ℝ) := by
  obtain ⟨h1, h2⟩ := counts s hs
  unfold g
  rw [h1, h2]
  push_cast
  ring

/-- The deviation satisfies the recurrence of the two other eigenvalues. -/
lemma g_rec (s : List ℕ) (hs : Valid s) :
    g (tau (tau s)) = (1 - lam) * g (tau s) + g s / lam := by
  obtain ⟨hl1, -, hp⟩ := lam_spec
  have hl : 0 < lam := by linarith
  have hv := tau_valid s
  obtain ⟨a1, a2, a3⟩ := tau_counts s hs
  obtain ⟨b1, b2, b3⟩ := tau_counts (tau s) hv
  have key : g (tau (tau s)) * lam = (1 - lam) * g (tau s) * lam + g s := by
    rw [g_counts _ (tau_valid _), g_counts _ hv, g_counts _ hs, b1, b2, b3, a1, a2, a3]
    unfold cc
    push_cast
    linear_combination ((s.count 1 : ℝ) * (-lam - 2) + (s.count 2 : ℝ) * (-2 * lam - 3) +
      (s.count 3 : ℝ) * (-2 * lam - 4)) * hp
  have hl0 : lam ≠ 0 := ne_of_gt hl
  field_simp
  linear_combination key

lemma g_growth : ∀ j, ∀ x, 1 ≤ x → x ≤ 3 →
    |g (tau^[j] [x])| ≤ 1.25 * 1.25 ^ j ∧ |g (tau^[j + 1] [x])| ≤ 1.25 * 1.25 ^ (j + 1) := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  obtain ⟨hc1, hc2⟩ := cc_bounds
  intro j
  induction j with
  | zero =>
    intro x hx1 hx3
    simp only [Function.iterate_zero, id, pow_zero, mul_one, zero_add, pow_one,
      Function.iterate_one, tau_single]
    interval_cases x <;> simp only [tauT, g_single] <;>
      (try rw [show ([3, 1] : List ℕ) = [3] ++ [1] from rfl, g_append, g_single, g_single]) <;>
      (try rw [show ([3, 2] : List ℕ) = [3] ++ [2] from rfl, g_append, g_single, g_single]) <;>
      (try rw [g_single]) <;> norm_num <;> rw [abs_le, abs_le] <;> constructor <;>
      constructor <;> linarith
  | succ j ih =>
    intro x hx1 hx3
    refine ⟨(ih x hx1 hx3).2, ?_⟩
    have hv : Valid (tau^[j] [x]) := tauIter_valid j _ (by intro y hy; simp at hy; omega)
    have e : tau^[j + 1 + 1] [x] = tau (tau (tau^[j] [x])) := by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have e1 : tau^[j + 1] [x] = tau (tau^[j] [x]) := Function.iterate_succ_apply' _ _ _
    rw [e, g_rec _ hv, ← e1]
    obtain ⟨h0, h1⟩ := ih x hx1 hx3
    have hl : 0 < lam := by linarith
    have hp : 0 ≤ (1.25 : ℝ) ^ j := by positivity
    have hA : (lam - 1) * |g (tau^[j + 1] [x])| ≤ (lam - 1) * (1.25 * 1.25 ^ (j + 1)) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    have hB : |g (tau^[j] [x])| / lam ≤ (1.25 * 1.25 ^ j) / lam :=
      div_le_div_of_nonneg_right h0 hl.le
    have hinv : (1.25 * 1.25 ^ j) / lam ≤ 0.555 * (1.25 * 1.25 ^ j) := by
      rw [div_le_iff₀ hl]
      nlinarith [mul_nonneg hp (sub_nonneg.mpr hl1)]
    have e1 : (1.25 : ℝ) ^ (j + 1) = 1.25 ^ j * 1.25 := pow_succ _ _
    have e2 : (1.25 : ℝ) ^ (j + 1 + 1) = 1.25 ^ j * 1.25 * 1.25 := by rw [pow_succ, pow_succ]
    have hC : (lam - 1) * (1.25 * 1.25 ^ (j + 1)) ≤ 0.802 * (1.25 * 1.25 ^ (j + 1)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    calc |(1 - lam) * g (tau^[j + 1] [x]) + g (tau^[j] [x]) / lam|
        ≤ |(1 - lam) * g (tau^[j + 1] [x])| + |g (tau^[j] [x]) / lam| := abs_add_le _ _
      _ = (lam - 1) * |g (tau^[j + 1] [x])| + |g (tau^[j] [x])| / lam := by
          rw [abs_mul, abs_div, abs_of_pos hl, abs_of_neg (by linarith : 1 - lam < 0), neg_sub]
      _ ≤ 1.25 * 1.25 ^ (j + 1 + 1) := by
          linarith [hA, hB, hinv, hC, e1, e2, hp]

/-! ### Prefixes of token lists -/

lemma tauIter_morph (j : ℕ) : ∀ u v, tau^[j] (u ++ v) = tau^[j] u ++ tau^[j] v :=
  tauIter_append j

/-- Splitting a prefix of the image of a token list along its tokens. -/
lemma pref_split (T : List ℕ → List ℕ) (hT : ∀ u v, T (u ++ v) = T u ++ T v) (b : ℝ)
    (hb0 : 0 ≤ b)
    (hb : ∀ y, 1 ≤ y → y ≤ 3 → ∀ i ≤ (T [y]).length, |g ((T [y]).take i)| ≤ b) :
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
    obtain ⟨⟨hy1, hy3⟩, hv'⟩ := valid_cons hv
    have e : T (y :: ys) = T [y] ++ T ys := by rw [← hT]; rfl
    rw [e] at hi ⊢
    rw [List.length_append] at hi
    rcases le_or_gt i (T [y]).length with h | h
    · refine ⟨0, by omega, ?_⟩
      rw [List.take_append_of_le_length h, List.take_zero, hnil]
      simpa [g] using hb y hy1 hy3 i h
    · obtain ⟨q, hq, hq'⟩ := ih hv' (i - (T [y]).length) (by omega)
      refine ⟨q + 1, by simp; omega, ?_⟩
      rw [List.take_append, List.take_of_length_le h.le, g_append,
        show (y :: ys).take (q + 1) = [y] ++ ys.take q from rfl, hT, g_append]
      have : g (T [y]) + g ((T ys).take (i - (T [y]).length)) - (g (T [y]) + g (T (ys.take q)))
          = g ((T ys).take (i - (T [y]).length)) - g (T (ys.take q)) := by ring
      rw [this]
      exact hq'

lemma g_short (J : ℕ) (u : List ℕ) (hu : Valid u) (hl : u.length ≤ 2) :
    |g (tau^[J] u)| ≤ 2 * (1.25 * 1.25 ^ J) := by
  have hp : 0 ≤ (1.25 : ℝ) ^ J := by positivity
  rcases u with _ | ⟨y1, _ | ⟨y2, _ | ⟨y3, u⟩⟩⟩
  · rw [tauIter_nil]
    simp [g]
    positivity
  · obtain ⟨⟨h1, h3⟩, -⟩ := valid_cons hu
    have := (g_growth J y1 h1 h3).1
    linarith
  · obtain ⟨⟨h1, h3⟩, hv2⟩ := valid_cons hu
    obtain ⟨⟨h1', h3'⟩, -⟩ := valid_cons hv2
    rw [show [y1, y2] = [y1] ++ [y2] from rfl, tauIter_append, g_append]
    have a1 := (g_growth J y1 h1 h3).1
    have a2 := (g_growth J y2 h1' h3').1
    calc |g (tau^[J] [y1]) + g (tau^[J] [y2])| ≤ |g (tau^[J] [y1])| + |g (tau^[J] [y2])| :=
          abs_add_le _ _
      _ ≤ 2 * (1.25 * 1.25 ^ J) := by linarith
  · simp at hl

/-- |g| over the prefixes of tau^J(x). -/
lemma prefix_bound (J : ℕ) : ∀ x, 1 ≤ x → x ≤ 3 → ∀ i ≤ (tau^[J] [x]).length,
    |g ((tau^[J] [x]).take i)| ≤ 10 * 1.25 ^ J := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  induction J with
  | zero =>
    intro x hx1 hx3 i hi
    simp only [Function.iterate_zero, id, List.length_cons, List.length_nil] at hi ⊢
    interval_cases i
    · simp [g]
    · simp only [List.take_succ_cons, List.take_zero, g_single]
      rw [abs_le]
      interval_cases x <;> norm_num <;> constructor <;> linarith
  | succ J ih =>
    intro x hx1 hx3 i hi
    have hp : 0 ≤ (1.25 : ℝ) ^ J := by positivity
    have e : tau^[J + 1] [x] = tau^[J] (tauT x) := by
      rw [Function.iterate_succ_apply, tau_single]
    rw [e] at hi ⊢
    obtain ⟨q, hq, hq'⟩ := pref_split (tau^[J]) (tauIter_morph J) _ (by positivity) ih (tauT x)
      (tauT_valid x) i hi
    have hlen : (tauT x).length ≤ 2 := by
      rcases x with _ | _ | _ | x <;> simp [tauT]
    have hvq : Valid ((tauT x).take q) := by
      intro y hy
      exact tauT_valid x y (List.mem_of_mem_take hy)
    have hfirst : |g (tau^[J] ((tauT x).take q))| ≤ 2 * (1.25 * 1.25 ^ J) :=
      g_short J _ hvq (by rw [List.length_take]; omega)
    have htri : |g ((tau^[J] (tauT x)).take i)| ≤ |g (tau^[J] ((tauT x).take q))| + 10 * 1.25 ^ J := by
      have := abs_sub_abs_le_abs_sub (g ((tau^[J] (tauT x)).take i)) (g (tau^[J] ((tauT x).take q)))
      linarith
    rw [pow_succ]
    linarith

/-! ### Letters -/

/-- For a word, the number of letters 0 minus c times the number of letters 1. -/
noncomputable def gL (L : List ℕ) : ℝ := (L.count 0 : ℝ) - cc * (L.count 1 : ℝ)

lemma gL_append (u v : List ℕ) : gL (u ++ v) = gL u + gL v := by
  simp only [gL, List.count_append]
  push_cast
  ring

lemma gL_tok (k : ℕ) : gL (tok k) = g [k] := by
  simp [gL, g, tok, List.count_replicate]

lemma gL_flat (s : List ℕ) : gL (flat s) = g s := by
  induction s with
  | nil => simp [gL, g, flat]
  | cons k s ih =>
    rw [flat_cons, gL_append, gL_tok, ih, show k :: s = [k] ++ s from rfl, g_append]

lemma gL_tok_take (k : ℕ) (hk : 1 ≤ k ∧ k ≤ 3) (r : ℕ) : |gL ((tok k).take r)| ≤ 3 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  rcases le_or_gt r k with h | h
  · have e : (tok k).take r = List.replicate r 0 := by
      rw [tok, List.take_append_of_le_length (by simp; omega), List.take_replicate,
        min_eq_left h]
    have hg : gL (List.replicate r 0) = r := by
      simp [gL, List.count_replicate]
    rw [e, hg, abs_le]
    have : (r : ℝ) ≤ 3 := by exact_mod_cast (show r ≤ 3 by omega)
    constructor <;> linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  · rw [List.take_of_length_le (by simp [tok]; omega), gL_tok, g_single]
    obtain ⟨h1, h3⟩ := hk
    have h1' : (1 : ℝ) ≤ k := by exact_mod_cast h1
    have h3' : (k : ℝ) ≤ 3 := by exact_mod_cast h3
    rw [abs_le]
    constructor <;> linarith

lemma flat_split : ∀ S : List ℕ, Valid S → ∀ t ≤ (flat S).length,
    ∃ i ≤ S.length, |gL ((flat S).take t) - g (S.take i)| ≤ 3 := by
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

/-- Over the prefixes of iterate J + 1, |g| <= 10 1.25^J + 3. -/
lemma iter_prefix_bound (J N : ℕ) (hN : N ≤ (iter (J + 1)).length) :
    |gL ((iter (J + 1)).take N)| ≤ 10 * 1.25 ^ J + 3 := by
  rw [iter_eq J] at hN ⊢
  obtain ⟨i, hi, hi'⟩ := flat_split _ (tauIter_valid J _ valid_three) N hN
  have h := prefix_bound J 3 (by norm_num) (by norm_num) i hi
  have := abs_sub_abs_le_abs_sub (gL ((flat (tau^[J] [3])).take N)) (g ((tau^[J] [3]).take i))
  linarith

/-! ### The length of the iterates -/

/-- The weight of a token: lam - 1, lam (lam - 1), lam for the tokens 1, 2, 3. -/
noncomputable def wt (k : ℕ) : ℝ := if k = 1 then lam - 1 else if k = 2 then lam * (lam - 1) else lam

/-- The weight of a token list; tau multiplies it by lam. -/
noncomputable def Phi (s : List ℕ) : ℝ := (s.map wt).sum

lemma Phi_append (u v : List ℕ) : Phi (u ++ v) = Phi u + Phi v := by
  simp [Phi]

lemma Phi_tau (s : List ℕ) (hs : Valid s) : Phi (tau s) = lam * Phi s := by
  obtain ⟨-, -, hp⟩ := lam_spec
  induction s with
  | nil => simp [Phi, tau]
  | cons k s ih =>
    obtain ⟨⟨hk1, hk3⟩, hs'⟩ := valid_cons hs
    rw [tau_cons, Phi_append, ih hs', show k :: s = [k] ++ s from rfl, Phi_append, mul_add]
    congr 1
    interval_cases k <;> simp [Phi, tauT, wt] <;>
      first | ring1 | linear_combination (-1 : ℝ) * hp | linear_combination hp

lemma Phi_iter (J : ℕ) : Phi (tau^[J] [3]) = lam ^ (J + 1) := by
  induction J with
  | zero => simp [Phi, wt]
  | succ J ih =>
    rw [Function.iterate_succ_apply', Phi_tau _ (tauIter_valid J _ valid_three), ih, pow_succ]
    ring

lemma length_ge_Phi (s : List ℕ) (hs : Valid s) : 5 / 3 * Phi s ≤ ((flat s).length : ℝ) := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  induction s with
  | nil => simp [Phi, flat]
  | cons k s ih =>
    obtain ⟨⟨hk1, hk3⟩, hs'⟩ := valid_cons hs
    rw [flat_cons, List.length_append, show k :: s = [k] ++ s from rfl, Phi_append]
    push_cast
    have := ih hs'
    have hk : 5 / 3 * Phi [k] ≤ ((tok k).length : ℝ) := by
      interval_cases k <;> simp [Phi, wt, tok] <;> norm_num <;> nlinarith
    linarith

lemma iter_length_ge (J : ℕ) : 5 / 3 * lam ^ (J + 1) ≤ ((iter (J + 1)).length : ℝ) := by
  rw [iter_eq J, ← Phi_iter J]
  exact length_ge_Phi _ (tauIter_valid J _ valid_three)

lemma iter_length_mono {m n : ℕ} (h : m ≤ n) : (iter m).length ≤ (iter n).length :=
  (iter_prefix h).length_le

/-! ### Counting along the fixed point -/

lemma iter_letters (n : ℕ) : ∀ x ∈ iter n, x ≤ 1 := by
  intro x hx
  cases n with
  | zero => simp [iter] at hx; omega
  | succ n =>
    rw [iter_eq] at hx
    simp only [flat, List.mem_flatMap, tok, List.mem_append, List.mem_replicate,
      List.mem_singleton] at hx
    obtain ⟨k, -, hk⟩ := hx
    omega

lemma W_le (i : ℕ) : W i ≤ 1 := by
  have hi : i < (iter (i + 1)).length := by have := iter_length (i + 1); omega
  rw [W_eq (i + 1) i hi, List.getD_eq_getElem _ _ hi]
  exact iter_letters _ _ (List.getElem_mem hi)

/-- Z(N): the number of letters 0 among the first N letters of W. -/
noncomputable def Z (N : ℕ) : ℕ := Nat.count (fun i => W i = 0) N

/-- O(N): the number of letters 1 among the first N letters of W. -/
noncomputable def O (N : ℕ) : ℕ := Nat.count (fun i => W i = 1) N

lemma Z_succ (N : ℕ) : Z (N + 1) = Z N + if W N = 0 then 1 else 0 := Nat.count_succ _ _

lemma O_succ (N : ℕ) : O (N + 1) = O N + if W N = 1 then 1 else 0 := Nat.count_succ _ _

lemma counts_eq (m N : ℕ) (hN : N ≤ (iter m).length) :
    Z N = ((iter m).take N).count 0 ∧ O N = ((iter m).take N).count 1 := by
  induction N with
  | zero => simp [Z, O]
  | succ N ih =>
    have hN' : N < (iter m).length := by omega
    have hW : W N = (iter m)[N] := by rw [W_eq m N hN', List.getD_eq_getElem _ _ hN']
    obtain ⟨h1, h2⟩ := ih (by omega)
    rw [Z_succ, O_succ, h1, h2, List.take_add_one, List.getElem?_eq_getElem hN',
      List.count_append, List.count_append, hW]
    constructor <;> simp [List.count_singleton]

/-- D(N) = Z(N) - c O(N) is the deviation over the first N letters of W. -/
noncomputable def D (N : ℕ) : ℝ := (Z N : ℝ) - cc * (O N : ℝ)

lemma D_eq (m N : ℕ) (hN : N ≤ (iter m).length) : D N = gL ((iter m).take N) := by
  obtain ⟨h1, h2⟩ := counts_eq m N hN
  simp [D, gL, h1, h2]

lemma O_add_Z (N : ℕ) : O N + Z N = N := by
  induction N with
  | zero => simp [O, Z]
  | succ N ih =>
    rw [O_succ, Z_succ]
    have := W_le N
    split_ifs <;> omega

lemma pow_bound (J : ℕ) (hJ : 10 ≤ J) : 30 * 1.25 ^ J + 9 < lam ^ J := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  induction J, hJ using Nat.le_induction with
  | base =>
    have : (1.8019 : ℝ) ^ 10 ≤ lam ^ 10 := pow_le_pow_left₀ (by norm_num) hl1 10
    norm_num at this ⊢
    linarith
  | succ J hJ ih =>
    rw [pow_succ, pow_succ]
    have hp : 0 ≤ lam ^ J := by positivity
    nlinarith

lemma iter10_length : (iter 10).length = 793 := by decide +kernel

/-- For N > 793 there is a level J >= 10 with (5/3) lam^J < N and |D(N)| <= 10 1.25^J + 3. -/
lemma level (N : ℕ) (hN : 793 < N) :
    ∃ J, 10 ≤ J ∧ 5 / 3 * lam ^ J < (N : ℝ) ∧ |D N| ≤ 10 * 1.25 ^ J + 3 := by
  have hex : ∃ J, N ≤ (iter (J + 1)).length := ⟨N, by have := iter_length (N + 1); omega⟩
  classical
  have hJN : N ≤ (iter (Nat.find hex + 1)).length := Nat.find_spec hex
  have h9 := iter10_length
  have hJ10 : 10 ≤ Nat.find hex := by
    by_contra h
    have := iter_length_mono (show Nat.find hex + 1 ≤ 10 by omega)
    omega
  have hmin : (iter (Nat.find hex)).length < N := by
    have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at this
    omega
  have hlen := iter_length_ge (Nat.find hex - 1)
  rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at hlen
  refine ⟨Nat.find hex, hJ10, ?_, ?_⟩
  · have : ((iter (Nat.find hex)).length : ℝ) < N := by exact_mod_cast hmin
    linarith
  · rw [D_eq (Nat.find hex + 1) N hJN]
    exact iter_prefix_bound _ N hJN

/-- Over every prefix of W longer than 793 letters, |D| < N / 5. -/
lemma D_small (N : ℕ) (hN : 793 < N) : |D N| < (N : ℝ) / 5 := by
  obtain ⟨J, hJ, hNr, hD⟩ := level N hN
  have hp := pow_bound J hJ
  linarith

/-- |D(N)|^2 <= 6084 N for every N >= 1. -/
lemma D_sq (N : ℕ) (hN : 1 ≤ N) : D N ^ 2 ≤ 6084 * N := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rcases le_or_gt N 793 with h | h
  · have h9 := iter10_length
    have hb : |gL ((iter 10).take N)| ≤ 10 * 1.25 ^ 9 + 3 :=
      iter_prefix_bound 9 N (show N ≤ (iter 10).length by omega)
    rw [D_eq 10 N (by omega)]
    have h1 : |gL ((iter 10).take N)| ≤ 78 := by
      have : (10 : ℝ) * 1.25 ^ 9 + 3 ≤ 78 := by norm_num
      linarith
    have h2 : gL ((iter 10).take N) ^ 2 ≤ 78 ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    clear hb h1 h9
    generalize gL ((iter 10).take N) = x at h2 ⊢
    nlinarith
  · obtain ⟨J, hJ, hNr, hD⟩ := level N h
    have hp : 0 ≤ (1.25 : ℝ) ^ J := by positivity
    have h1 : D N ^ 2 ≤ (10 * 1.25 ^ J + 3) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hD 2
    have h2 : ((1.25 : ℝ) ^ J) ^ 2 ≤ lam ^ J := by
      rw [← pow_mul, mul_comm, pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num; linarith) J
    nlinarith [sq_nonneg ((1.25 : ℝ) ^ J - 1)]

/-! ### The positions of 0 -/

/-- The limit, (1 + c)/c = lam^2/(lam^2 - 1) = 1.44504... -/
noncomputable def m0 : ℝ := (1 + cc) / cc

lemma m0_bounds : 1.4449 ≤ m0 ∧ m0 ≤ 1.4451 := by
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
  have h := D_small (B + 1 + (4 * Z (B + 1) + 800)) (by omega)
  have hs := O_add_Z (B + 1 + (4 * Z (B + 1) + 800))
  rw [hconst] at hs
  unfold D at h
  rw [hconst, abs_lt] at h
  obtain ⟨h1, -⟩ := h
  have hO : (O (B + 1 + (4 * Z (B + 1) + 800)) : ℝ) =
      ((B + 1 + (4 * Z (B + 1) + 800) : ℕ) : ℝ) - Z (B + 1) := by
    have : (O (B + 1 + (4 * Z (B + 1) + 800)) : ℝ) + Z (B + 1) =
        ((B + 1 + (4 * Z (B + 1) + 800) : ℕ) : ℝ) := by exact_mod_cast hs
    linarith
  rw [hO] at h1
  generalize hz : (Z (B + 1) : ℝ) = z at h1
  have hz0 : 0 ≤ z := by rw [← hz]; exact Nat.cast_nonneg _
  have hz' : ((B + 1 + (4 * Z (B + 1) + 800) : ℕ) : ℝ) = (B : ℝ) + 1 + (4 * z + 800) := by
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

/-- A linear scan of a word, checking 10000 (t + 1) < 24449 Z(t + 1) at each letter 0. -/
def chk : List ℕ → ℕ → ℕ → Bool
  | [], _, _ => true
  | x :: l, t, z =>
    if x = 0 then decide (10000 * (t + 1) < 24449 * (z + 1)) && chk l (t + 1) (z + 1)
    else chk l (t + 1) z

lemma chk_spec : ∀ (L : List ℕ) (t z : ℕ), chk L t z = true →
    ∀ i < L.length, L.getD i 0 = 0 →
      10000 * (t + i + 1) < 24449 * (z + (L.take (i + 1)).count 0) := by
  intro L
  induction L with
  | nil =>
    intro t z _ i hi
    simp at hi
  | cons x l ih =>
    intro t z h i hi hx
    by_cases h0 : x = 0
    · subst h0
      have h' : 10000 * (t + 1) < 24449 * (z + 1) ∧ chk l (t + 1) (z + 1) = true := by
        simpa [chk] using h
      rcases i with _ | i
      · simpa using h'.1
      · have := ih (t + 1) (z + 1) h'.2 i (by simp at hi; omega) (by simpa using hx)
        have e : ((0 :: l).take (i + 1 + 1)).count 0 = (l.take (i + 1)).count 0 + 1 := by
          simp [List.take_succ_cons, List.count_cons]
        rw [e]
        omega
    · have h' : chk l (t + 1) z = true := by simpa [chk, h0] using h
      rcases i with _ | i
      · simp at hx
        exact absurd hx h0
      · have := ih (t + 1) z h' i (by simp at hi; omega) (by simpa using hx)
        have e : ((x :: l).take (i + 1 + 1)).count 0 = (l.take (i + 1)).count 0 := by
          simp [List.take_succ_cons, List.count_cons, h0]
        rw [e]
        omega

lemma chk_iter : chk (iter 10) 0 0 = true := by decide +kernel

lemma check_small : ∀ t < 793, (iter 10).getD t 0 = 0 →
    10000 * (t + 1) < 24449 * ((iter 10).take (t + 1)).count 0 := by
  intro t ht hW
  have h := chk_spec (iter 10) 0 0 chk_iter t (by rw [iter10_length]; exact ht) hW
  simpa using h

lemma bound_small (n : ℕ) (hn : 1 ≤ n) (ha : a n ≤ 793) :
    -1 < m0 - (a n : ℝ) / n ∧ m0 - (a n : ℝ) / n < 1 := by
  obtain ⟨hm1, hm2⟩ := m0_bounds
  obtain ⟨hZ, hO⟩ := a_spec n hn
  have hinf := zeros_infinite
  have hWp : W (Nat.nth (fun i => W i = 0) (n - 1)) = 0 := Nat.nth_mem_of_infinite hinf (n - 1)
  have ha' : a n = Nat.nth (fun i => W i = 0) (n - 1) + 1 := rfl
  set t := Nat.nth (fun i => W i = 0) (n - 1) with ht
  have hlen := iter10_length
  have hW : (iter 10).getD t 0 = 0 := by rw [← W_eq 10 t (by omega)]; exact hWp
  have hc := check_small t (by omega) hW
  have hZ' : ((iter 10).take (t + 1)).count 0 = n := by
    rw [← (counts_eq 10 (t + 1) (by omega)).1, ← ha', hZ]
  rw [hZ'] at hc
  have hle : n ≤ a n := by have := O_add_Z (a n); omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hc' : (10000 : ℝ) * (a n) < 24449 * n := by
    rw [ha']
    exact_mod_cast hc
  have hle' : (n : ℝ) ≤ a n := by exact_mod_cast hle
  have h1 : (a n : ℝ) / n < 2.4449 := by
    rw [div_lt_iff₀ hnpos]
    linarith
  have h2 : 1 ≤ (a n : ℝ) / n := by
    rw [le_div_iff₀ hnpos]
    linarith
  constructor <;> linarith

lemma bound_large (n : ℕ) (hn : 1 ≤ n) (ha : 793 < a n) :
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
  have hP : 2.24684 * (a n : ℝ) ≤ cc * a n := mul_le_mul_of_nonneg_right hc1 hA0
  have hQ1 : 2.24684 * (n : ℝ) ≤ cc * n := mul_le_mul_of_nonneg_right hc1 hnpos.le
  have hQ2 : cc * (n : ℝ) ≤ 2.24721 * n := mul_le_mul_of_nonneg_right hc2 hnpos.le
  have hE : cc * ((a n : ℝ) - n) = cc * a n - cc * n := by ring
  rw [hE] at hD1 hD2 ⊢
  constructor
  · rw [lt_div_iff₀ hnpos, lt_div_iff₀ hc]
    linarith
  · rw [div_lt_iff₀ hnpos, div_lt_iff₀ hc]
    linarith

/-- Kimberling's conjecture: a(n)/n tends to a number m = 1.44..., and -1 < m - a(n)/n < 1
for n >= 1. -/
theorem conjecture : ∃ m : ℝ, (1.44 ≤ m ∧ m < 1.45) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 m) ∧
    ∀ n : ℕ, 1 ≤ n → -1 < m - (a n : ℝ) / n ∧ m - (a n : ℝ) / n < 1 := by
  obtain ⟨hm1, hm2⟩ := m0_bounds
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hc : 0 < cc := by linarith
  have hbound : ∀ n : ℕ, 1 ≤ n → -1 < m0 - (a n : ℝ) / n ∧ m0 - (a n : ℝ) / n < 1 := by
    intro n hn
    rcases le_or_gt (a n) 793 with h | h
    · exact bound_small n hn h
    · exact bound_large n hn h
  refine ⟨m0, ⟨by linarith, by linarith⟩, ?_, hbound⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => Real.sqrt (6084 * 3 / cc ^ 2 / n)) atTop (𝓝 0) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (6084 * 3 / cc ^ 2)).sqrt
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hZ, hO⟩ := a_spec n hn
  have hle : n ≤ a n := by have := O_add_Z (a n); omega
  have ha1 : (1 : ℝ) ≤ a n := by exact_mod_cast (le_trans hn hle)
  have hsq := D_sq (a n) (le_trans hn hle)
  have hb := hbound n hn
  have ha3 : (a n : ℝ) ≤ 3 * n := by
    have h1 : (a n : ℝ) / n < 2.4451 := by linarith [hb.1]
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
  have hD3 : D (a n) ^ 2 ≤ 6084 * (3 * n) := by
    have : (6084 : ℝ) * (a n) ≤ 6084 * (3 * n) := by linarith
    linarith
  have e2 : 6084 * 3 / cc ^ 2 * (cc ^ 2 * (n : ℝ) ^ 2) = 6084 * 3 * n ^ 2 := by
    field_simp
  rw [e2]
  nlinarith [hD3, hnpos]

end OMA.S_oeis_a288373

theorem OMA.solution : type_of% @OMA.S_oeis_a288373.main :=
  OMA.S_oeis_a288373.conjecture

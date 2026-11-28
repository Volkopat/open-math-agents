import OMAStatements.S_oeis_a288597

namespace OMA.S_oeis_a288597

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

/-- No rule reads a letter 1 as its second letter, so the pass restarts at every letter 1. -/
lemma step_cut (u : List ℕ) : ∀ w, step (u ++ 1 :: w) = step u ++ step (1 :: w) := by
  refine step_rec (P := fun u => ∀ w, step (u ++ 1 :: w) = step u ++ step (1 :: w))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ u
  · intro w
    rfl
  · intro l ih w
    show 0 :: 1 :: 0 :: 1 :: step (l ++ 1 :: w) = 0 :: 1 :: 0 :: 1 :: step l ++ step (1 :: w)
    rw [ih]
    rfl
  · intro l ih w
    show 1 :: 0 :: 0 :: 0 :: step (l ++ 1 :: w) = 1 :: 0 :: 0 :: 0 :: step l ++ step (1 :: w)
    rw [ih]
    rfl
  · intro w
    rfl
  · intro w
    rfl
  · intro y l ih w
    show 0 :: step ((y + 1) :: l ++ 1 :: w) = 0 :: step ((y + 1) :: l) ++ step (1 :: w)
    rw [ih]
    rfl
  · intro y l ih w
    show 1 :: step ((y + 1) :: l ++ 1 :: w) = 1 :: step ((y + 1) :: l) ++ step (1 :: w)
    rw [ih]
    rfl
  · intro x l ih w
    show (x + 2) :: step (l ++ 1 :: w) = (x + 2) :: step l ++ step (1 :: w)
    rw [ih]
    rfl

/-! ### Tokens -/

/-- The token k is the word 1 0^k. -/
def tok (k : ℕ) : List ℕ := 1 :: List.replicate k 0

/-- The word of a list of tokens. -/
def flat (s : List ℕ) : List ℕ := s.flatMap tok

/-- The images of the tokens: 1 -> 1, 10 -> 1000, 1000 -> 10000.10.1, 10000 -> 10000.10.10
(the token 100 does not occur). -/
def tauT : ℕ → List ℕ
  | 0 => [0]
  | 1 => [3]
  | 3 => [4, 1, 0]
  | _ => [4, 1, 1]

/-- The token morphism. -/
def tau (s : List ℕ) : List ℕ := s.flatMap tauT

/-- All tokens are 0, 1, 3 or 4. -/
def Valid (s : List ℕ) : Prop := ∀ k ∈ s, k ≤ 4 ∧ k ≠ 2

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

lemma valid_cons {k : ℕ} {s : List ℕ} (h : Valid (k :: s)) : (k ≤ 4 ∧ k ≠ 2) ∧ Valid s :=
  ⟨h k (by simp), fun x hx => h x (by simp [hx])⟩

lemma valid_single {x : ℕ} (hx : x ≤ 4 ∧ x ≠ 2) : Valid [x] := by
  intro y hy
  simp at hy
  subst hy
  exact hx

lemma step_append_flat (u s : List ℕ) : step (u ++ flat s) = step u ++ step (flat s) := by
  rcases s with _ | ⟨j, s⟩
  · rw [show flat [] = [] from rfl, List.append_nil, show step [] = [] from rfl,
      List.append_nil]
  · rw [flat_cons, show tok j ++ flat s = 1 :: (List.replicate j 0 ++ flat s) from rfl,
      step_cut]

lemma step_tok (k : ℕ) (hk : k ≤ 4 ∧ k ≠ 2) : step (tok k) = flat (tauT k) := by
  obtain ⟨h4, h2⟩ := hk
  interval_cases k <;> first | rfl | exact absurd rfl h2

lemma step_flat (s : List ℕ) (hs : Valid s) : step (flat s) = flat (tau s) := by
  induction s with
  | nil => rfl
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    rw [flat_cons, tau_cons, flat_append, step_append_flat, step_tok k hk, ih hs']

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

lemma valid_start : Valid [1, 0] := by
  intro x hx
  simp at hx
  omega

lemma valid_three : Valid [3] := valid_single (by omega)

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

lemma one_prefix_flat (s : List ℕ) (hs : s ≠ []) : [1] <+: flat s := by
  rcases s with _ | ⟨k, s⟩
  · exact absurd rfl hs
  · exact ⟨List.replicate k 0 ++ flat s, rfl⟩

/-! ### The fixed point -/

/-- Iterate n + 1 is 0 followed by the tokens tau^n(1 0). -/
lemma iter_eq (n : ℕ) : iter (n + 1) = 0 :: flat (tau^[n] [1, 0]) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show iter (n + 1 + 1) = step (iter (n + 1)) from rfl, ih,
      show 0 :: flat (tau^[n] [1, 0]) = [0] ++ flat (tau^[n] [1, 0]) from rfl, step_append_flat,
      step_flat _ (tauIter_valid n _ valid_start), Function.iterate_succ_apply']
    rfl

/-- Y n: the word of the tokens tau^n(1). -/
def Y (n : ℕ) : List ℕ := flat (tau^[n] [1])

lemma tauIter_zero (n : ℕ) : tau^[n] [0] = [0] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, tau_single]; exact ih

lemma tauIter_one_succ (n : ℕ) : tau^[n + 1] [1] = tau^[n] [3] := by
  rw [Function.iterate_succ_apply, tau_single]
  rfl

lemma tauIter_three_succ (n : ℕ) :
    tau^[n + 1] [3] = tau^[n] [4] ++ tau^[n] [1] ++ tau^[n] [0] := by
  rw [Function.iterate_succ_apply, tau_single, show tauT 3 = [4] ++ [1] ++ [0] from rfl,
    tauIter_append, tauIter_append]

lemma tauIter_four_succ (n : ℕ) :
    tau^[n + 1] [4] = tau^[n] [4] ++ tau^[n] [1] ++ tau^[n] [1] := by
  rw [Function.iterate_succ_apply, tau_single, show tauT 4 = [4] ++ [1] ++ [1] from rfl,
    tauIter_append, tauIter_append]

/-- The word of tau^n(3) is a prefix of the word of tau^n(4). -/
lemma three_four (n : ℕ) : flat (tau^[n] [3]) <+: flat (tau^[n] [4]) := by
  induction n with
  | zero => exact ⟨[0], rfl⟩
  | succ n ih =>
    rw [tauIter_three_succ, tauIter_four_succ, flat_append, flat_append, flat_append,
      flat_append, tauIter_zero]
    exact (List.prefix_append_right_inj _).mpr
      (one_prefix_flat _ (tauIter_ne_nil n _ (by simp)))

/-- The stable prefix: 0 followed by Y n. -/
def P (n : ℕ) : List ℕ := 0 :: Y n

lemma P_length (n : ℕ) : (P n).length = (Y n).length + 1 := by
  simp [P]

/-- Iterate n + 1 is 0 Y_n 1. -/
lemma iter_P (n : ℕ) : iter (n + 1) = P n ++ [1] := by
  rw [iter_eq, show ([1, 0] : List ℕ) = [1] ++ [0] from rfl, tauIter_append, flat_append,
    tauIter_zero]
  rfl

lemma Y_succ_eq (J : ℕ) : Y (J + 1) = flat (tau^[J] [3]) := by
  unfold Y
  rw [tauIter_one_succ]

lemma Y_prefix_succ (n : ℕ) : Y n <+: Y (n + 1) := by
  rcases n with _ | n
  · exact ⟨[0, 0], rfl⟩
  · rw [Y_succ_eq, Y_succ_eq, tauIter_three_succ, flat_append, flat_append]
    exact (three_four n).trans ((List.prefix_append _ _).trans (List.prefix_append _ _))

lemma Y_prefix {m n : ℕ} (h : m ≤ n) : Y m <+: Y n := by
  induction n, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n _ ih => exact ih.trans (Y_prefix_succ n)

lemma Y_length_succ_ge (n : ℕ) : (Y n).length + 1 ≤ (Y (n + 1)).length := by
  rcases n with _ | n
  · decide
  · have h3 := (three_four n).length_le
    have e1 : (Y (n + 1)).length = (flat (tau^[n] [3])).length := by rw [Y_succ_eq]
    have e2 : (Y (n + 1 + 1)).length = (flat (tau^[n] [4])).length +
        (flat (tau^[n] [1])).length + 1 := by
      rw [Y_succ_eq, tauIter_three_succ, flat_append, flat_append, List.length_append,
        List.length_append, tauIter_zero]
      rfl
    omega

lemma Y_length (n : ℕ) : n + 2 ≤ (Y n).length := by
  induction n with
  | zero => decide
  | succ n ih =>
    have := Y_length_succ_ge n
    omega

lemma getD_prefix {l₁ l₂ : List ℕ} (h : l₁ <+: l₂) {i : ℕ} (hi : i < l₁.length) :
    l₁.getD i 0 = l₂.getD i 0 := by
  obtain ⟨s, rfl⟩ := h
  rw [List.getD_append _ _ _ _ hi]

lemma P_prefix {m n : ℕ} (h : m ≤ n) : P m <+: P n := by
  obtain ⟨t, ht⟩ := Y_prefix h
  exact ⟨t, by rw [P, P, ← ht]; rfl⟩

/-- P n is a prefix of every iterate from iterate n + 1 on. -/
lemma stable (n m : ℕ) (h : n ≤ m) : P n <+: iter (m + 1) := by
  rw [iter_P]
  exact (P_prefix h).trans (List.prefix_append _ _)

lemma W_eq (n i : ℕ) (hi : i < (P n).length) : W i = (P n).getD i 0 := by
  unfold W
  have hi' : i < (P i).length := by have := Y_length i; rw [P_length]; omega
  rw [← getD_prefix (stable i i le_rfl) hi']
  rcases le_total i n with h | h
  · exact getD_prefix (P_prefix h) hi'
  · exact (getD_prefix (P_prefix h) hi).symm

/-! ### The Perron root -/

lemma lam_exists : ∃ x : ℝ, 1.8392 ≤ x ∧ x ≤ 1.8393 ∧ x ^ 3 - x ^ 2 - x - 1 = 0 := by
  have hc : ContinuousOn (fun x : ℝ => x ^ 3 - x ^ 2 - x - 1) (Set.Icc 1.8392 1.8393) := by
    fun_prop
  have h := intermediate_value_Icc (show (1.8392 : ℝ) ≤ 1.8393 by norm_num) hc
  have h0 : (0 : ℝ) ∈ Set.Icc ((fun x : ℝ => x ^ 3 - x ^ 2 - x - 1) 1.8392)
      ((fun x : ℝ => x ^ 3 - x ^ 2 - x - 1) 1.8393) := by
    constructor <;> norm_num
  obtain ⟨x, ⟨hx1, hx2⟩, hx⟩ := h h0
  exact ⟨x, hx1, hx2, hx⟩

/-- The Perron root of the token morphism, the tribonacci constant 1.83928... -/
noncomputable def lam : ℝ := Classical.choose lam_exists

lemma lam_spec : 1.8392 ≤ lam ∧ lam ≤ 1.8393 ∧ lam ^ 3 - lam ^ 2 - lam - 1 = 0 :=
  Classical.choose_spec lam_exists

/-- The limiting number of letters 0 per letter 1. -/
noncomputable def cc : ℝ := lam

lemma cc_bounds : 1.8392 ≤ cc ∧ cc ≤ 1.8393 := by
  obtain ⟨h1, h2, -⟩ := lam_spec
  exact ⟨h1, h2⟩

lemma q_bounds : 0.5433 ≤ lam ^ 2 - lam - 1 ∧ lam ^ 2 - lam - 1 ≤ 0.5439 := by
  obtain ⟨h1, h2, -⟩ := lam_spec
  constructor <;> nlinarith

/-! ### Deviation and weight of token lists -/

/-- For a list of tokens, the number of letters 0 minus c times the number of letters 1. -/
noncomputable def g (s : List ℕ) : ℝ := (s.sum : ℝ) - cc * (s.length : ℝ)

/-- For a list of tokens, the number of tokens 0 minus the number of tokens 4. -/
noncomputable def ell (s : List ℕ) : ℝ := (s.count 0 : ℝ) - (s.count 4 : ℝ)

/-- The deviation without its part along ell. -/
noncomputable def gp (s : List ℕ) : ℝ := g s + cc * ell s

lemma g_append (u v : List ℕ) : g (u ++ v) = g u + g v := by
  simp only [g, List.sum_append, List.length_append]
  push_cast
  ring

lemma g_single (k : ℕ) : g [k] = k - cc := by
  simp [g]

lemma counts (s : List ℕ) (hs : Valid s) :
    s.sum = s.count 1 + 3 * s.count 3 + 4 * s.count 4 ∧
      s.length = s.count 0 + s.count 1 + s.count 3 + s.count 4 := by
  induction s with
  | nil => simp
  | cons k s ih =>
    obtain ⟨⟨hk4, hk2⟩, hs'⟩ := valid_cons hs
    obtain ⟨h1, h2⟩ := ih hs'
    interval_cases k <;> simp [List.count_cons] <;> omega

lemma tau_counts (s : List ℕ) (hs : Valid s) :
    (tau s).count 0 = s.count 0 + s.count 3 ∧ (tau s).count 1 = s.count 3 + 2 * s.count 4 ∧
      (tau s).count 3 = s.count 1 ∧ (tau s).count 4 = s.count 3 + s.count 4 := by
  induction s with
  | nil => simp [tau]
  | cons k s ih =>
    obtain ⟨⟨hk4, hk2⟩, hs'⟩ := valid_cons hs
    obtain ⟨h0, h1, h3, h4⟩ := ih hs'
    rw [tau_cons, List.count_append, List.count_append, List.count_append, List.count_append]
    interval_cases k <;> simp [tauT, List.count_cons] <;> omega

lemma ell_tau (s : List ℕ) (hs : Valid s) : ell (tau s) = ell s := by
  obtain ⟨a0, -, -, a4⟩ := tau_counts s hs
  unfold ell
  rw [a0, a4]
  push_cast
  ring

lemma ell_iter (j : ℕ) (s : List ℕ) (hs : Valid s) : ell (tau^[j] s) = ell s := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ell_tau _ (tauIter_valid j s hs), ih]

lemma ell_single (x : ℕ) : |ell [x]| ≤ 1 := by
  rcases x with _ | _ | _ | _ | _ | x <;> simp [ell]

lemma gp_counts (s : List ℕ) (hs : Valid s) :
    gp s = (1 - cc) * (s.count 1 : ℝ) + (3 - cc) * (s.count 3 : ℝ) +
      (4 - 2 * cc) * (s.count 4 : ℝ) := by
  obtain ⟨h1, h2⟩ := counts s hs
  unfold gp g ell
  rw [h1, h2]
  push_cast
  ring

/-- The deviation without its part along ell satisfies the recurrence of the complex pair. -/
lemma gp_rec (s : List ℕ) (hs : Valid s) :
    gp (tau (tau s)) = (1 - lam) * gp (tau s) - (lam ^ 2 - lam - 1) * gp s := by
  obtain ⟨-, -, hp⟩ := lam_spec
  have hv := tau_valid s
  obtain ⟨-, a1, a3, a4⟩ := tau_counts s hs
  obtain ⟨-, b1, b3, b4⟩ := tau_counts (tau s) hv
  rw [gp_counts _ (tau_valid _), gp_counts _ hv, gp_counts _ hs, b1, b3, b4, a1, a3, a4]
  unfold cc
  push_cast
  linear_combination (-(s.count 1 : ℝ) - (s.count 3 : ℝ) - 2 * (s.count 4 : ℝ)) * hp

lemma gp_base (x : ℕ) (hx : x ≤ 4 ∧ x ≠ 2) :
    |gp [x]| ≤ 1.17 ∧ |gp (tauT x)| ≤ 1.17 * 1.3 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  obtain ⟨h4, h2⟩ := hx
  have e0 : gp [0] = 0 := by simp [gp, g, ell] <;> ring
  have e1 : gp [1] = 1 - cc := by simp [gp, g, ell] <;> ring
  have e3 : gp [3] = 3 - cc := by simp [gp, g, ell] <;> ring
  have e4 : gp [4] = 4 - 2 * cc := by simp [gp, g, ell] <;> ring
  have e5 : gp [4, 1, 0] = 5 - 3 * cc := by simp [gp, g, ell] <;> ring
  have e6 : gp [4, 1, 1] = 6 - 4 * cc := by simp [gp, g, ell] <;> ring
  interval_cases x
  · rw [show tauT 0 = [0] from rfl, e0, abs_zero]
    constructor <;> norm_num
  · rw [show tauT 1 = [3] from rfl, e1, e3, abs_le, abs_le]
    constructor <;> constructor <;> linarith
  · exact absurd rfl h2
  · rw [show tauT 3 = [4, 1, 0] from rfl, e3, e5, abs_le, abs_le]
    constructor <;> constructor <;> linarith
  · rw [show tauT 4 = [4, 1, 1] from rfl, e4, e6, abs_le, abs_le]
    constructor <;> constructor <;> linarith

lemma gp_growth : ∀ j, ∀ x, x ≤ 4 ∧ x ≠ 2 →
    |gp (tau^[j] [x])| ≤ 1.17 * 1.3 ^ j ∧ |gp (tau^[j + 1] [x])| ≤ 1.17 * 1.3 ^ (j + 1) := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  obtain ⟨hq1, hq2⟩ := q_bounds
  intro j
  induction j with
  | zero =>
    intro x hx
    have h := gp_base x hx
    simp only [Function.iterate_zero, id, pow_zero, mul_one, zero_add, pow_one,
      Function.iterate_one, tau_single]
    exact h
  | succ j ih =>
    intro x hx
    refine ⟨(ih x hx).2, ?_⟩
    have hv : Valid (tau^[j] [x]) := tauIter_valid j _ (valid_single hx)
    have e : tau^[j + 1 + 1] [x] = tau (tau (tau^[j] [x])) := by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have e1 : tau^[j + 1] [x] = tau (tau^[j] [x]) := Function.iterate_succ_apply' _ _ _
    rw [e, gp_rec _ hv, ← e1]
    obtain ⟨h0, h1⟩ := ih x hx
    have hp : 0 ≤ (1.3 : ℝ) ^ j := by positivity
    have hA : (lam - 1) * |gp (tau^[j + 1] [x])| ≤ (lam - 1) * (1.17 * 1.3 ^ (j + 1)) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    have hB : (lam ^ 2 - lam - 1) * |gp (tau^[j] [x])| ≤ (lam ^ 2 - lam - 1) * (1.17 * 1.3 ^ j) :=
      mul_le_mul_of_nonneg_left h0 (by linarith)
    have hB' : (lam ^ 2 - lam - 1) * (1.17 * 1.3 ^ j) ≤ 0.5439 * (1.17 * 1.3 ^ j) :=
      mul_le_mul_of_nonneg_right hq2 (by positivity)
    have e1' : (1.3 : ℝ) ^ (j + 1) = 1.3 ^ j * 1.3 := pow_succ _ _
    have e2' : (1.3 : ℝ) ^ (j + 1 + 1) = 1.3 ^ j * 1.3 * 1.3 := by rw [pow_succ, pow_succ]
    have hC : (lam - 1) * (1.17 * 1.3 ^ (j + 1)) ≤ 0.8393 * (1.17 * 1.3 ^ (j + 1)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    calc |(1 - lam) * gp (tau^[j + 1] [x]) - (lam ^ 2 - lam - 1) * gp (tau^[j] [x])|
        ≤ |(1 - lam) * gp (tau^[j + 1] [x])| + |(lam ^ 2 - lam - 1) * gp (tau^[j] [x])| := by
          have h := abs_add_le ((1 - lam) * gp (tau^[j + 1] [x]))
            (-((lam ^ 2 - lam - 1) * gp (tau^[j] [x])))
          rwa [← sub_eq_add_neg, abs_neg] at h
      _ = (lam - 1) * |gp (tau^[j + 1] [x])| + (lam ^ 2 - lam - 1) * |gp (tau^[j] [x])| := by
          rw [abs_mul, abs_mul, abs_of_neg (by linarith : 1 - lam < 0), neg_sub,
            abs_of_nonneg (by linarith : (0 : ℝ) ≤ lam ^ 2 - lam - 1)]
      _ ≤ 1.17 * 1.3 ^ (j + 1 + 1) := by
          linarith [hA, hB, hB', hC, e1', e2', hp]

lemma g_growth (j x : ℕ) (hx : x ≤ 4 ∧ x ≠ 2) : |g (tau^[j] [x])| ≤ 3.01 * 1.3 ^ j := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have h1 := (gp_growth j x hx).1
  have he : ell (tau^[j] [x]) = ell [x] := ell_iter j [x] (valid_single hx)
  have hs := ell_single x
  have e : g (tau^[j] [x]) = gp (tau^[j] [x]) - cc * ell (tau^[j] [x]) := by
    unfold gp
    ring
  have h3 : (1 : ℝ) ≤ 1.3 ^ j := one_le_pow₀ (by norm_num)
  rw [e, he]
  have h4 := abs_add_le (gp (tau^[j] [x])) (-(cc * ell [x]))
  rw [← sub_eq_add_neg, abs_neg, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < cc)] at h4
  have h5 : cc * |ell [x]| ≤ cc * 1 := mul_le_mul_of_nonneg_left hs (by linarith)
  linarith

/-! ### Prefixes of token lists -/

lemma tauIter_morph (j : ℕ) : ∀ u v, tau^[j] (u ++ v) = tau^[j] u ++ tau^[j] v :=
  tauIter_append j

/-- Splitting a prefix of the image of a token list along its tokens. -/
lemma pref_split (T : List ℕ → List ℕ) (hT : ∀ u v, T (u ++ v) = T u ++ T v) (b : ℝ)
    (hb0 : 0 ≤ b)
    (hb : ∀ y, y ≤ 4 ∧ y ≠ 2 → ∀ i ≤ (T [y]).length, |g ((T [y]).take i)| ≤ b) :
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

lemma g_list (J : ℕ) : ∀ u : List ℕ, Valid u →
    |g (tau^[J] u)| ≤ u.length * (3.01 * 1.3 ^ J) := by
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
    have a1 := g_growth J y hy
    have a2 := ih hu'
    have a3 := abs_add_le (g (tau^[J] [y])) (g (tau^[J] u))
    push_cast
    simp only [List.length_singleton, Nat.cast_one]
    linarith

/-- |g| over the prefixes of tau^J(x). -/
lemma prefix_bound (J : ℕ) : ∀ x, x ≤ 4 ∧ x ≠ 2 → ∀ i ≤ (tau^[J] [x]).length,
    |g ((tau^[J] [x]).take i)| ≤ 31 * 1.3 ^ J := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  induction J with
  | zero =>
    intro x hx i hi
    obtain ⟨hx4, -⟩ := hx
    simp only [Function.iterate_zero, id, List.length_cons, List.length_nil] at hi ⊢
    interval_cases i
    · simp [g]
    · simp only [List.take_succ_cons, List.take_zero, g_single]
      rw [abs_le]
      interval_cases x <;> norm_num <;> constructor <;> linarith
  | succ J ih =>
    intro x hx i hi
    have hp : 0 ≤ (1.3 : ℝ) ^ J := by positivity
    have e : tau^[J + 1] [x] = tau^[J] (tauT x) := by
      rw [Function.iterate_succ_apply, tau_single]
    rw [e] at hi ⊢
    obtain ⟨q, hq, hq'⟩ := pref_split (tau^[J]) (tauIter_morph J) _ (by positivity) ih (tauT x)
      (tauT_valid x) i hi
    have hlen : (tauT x).length ≤ 3 := by
      rcases x with _ | _ | _ | _ | x <;> simp [tauT]
    have hvq : Valid ((tauT x).take q) := by
      intro y hy
      exact tauT_valid x y (List.mem_of_mem_take hy)
    have hfirst : |g (tau^[J] ((tauT x).take q))| ≤ 3 * (3.01 * 1.3 ^ J) := by
      have h := g_list J _ hvq
      have hl : (((tauT x).take q).length : ℝ) ≤ 3 := by
        have : ((tauT x).take q).length ≤ 3 := by rw [List.length_take]; omega
        exact_mod_cast this
      have hpos : 0 ≤ 3.01 * (1.3 : ℝ) ^ J := by positivity
      nlinarith
    have htri : |g ((tau^[J] (tauT x)).take i)| ≤
        |g (tau^[J] ((tauT x).take q))| + 31 * 1.3 ^ J := by
      have := abs_sub_abs_le_abs_sub (g ((tau^[J] (tauT x)).take i))
        (g (tau^[J] ((tauT x).take q)))
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
  simp [gL, g, tok, List.count_replicate, List.count_cons]

lemma gL_flat (s : List ℕ) : gL (flat s) = g s := by
  induction s with
  | nil => simp [gL, g, flat]
  | cons k s ih =>
    rw [flat_cons, gL_append, gL_tok, ih, show k :: s = [k] ++ s from rfl, g_append]

lemma gL_tok_take (k : ℕ) (hk : k ≤ 4) (r : ℕ) : |gL ((tok k).take r)| ≤ 3 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  rcases r with _ | r
  · simp [gL]
  · obtain ⟨m, hm, e⟩ : ∃ m, m ≤ 4 ∧ (tok k).take (r + 1) = 1 :: List.replicate m 0 :=
      ⟨min r k, by omega, by simp [tok, List.take_replicate]⟩
    have hg : gL (1 :: List.replicate m 0) = m - cc := by
      simp [gL, List.count_replicate, List.count_cons]
    rw [e, hg, abs_le]
    have h2 : (m : ℝ) ≤ 4 := by exact_mod_cast hm
    have h0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
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
      simpa [g] using gL_tok_take k hk.1 t
    · obtain ⟨i, hi, hi'⟩ := ih hv' (t - (tok k).length) (by omega)
      refine ⟨i + 1, by simp; omega, ?_⟩
      rw [List.take_append, List.take_of_length_le h.le, gL_append, gL_tok,
        show (k :: S).take (i + 1) = [k] ++ S.take i from rfl, g_append]
      have : g [k] + gL ((flat S).take (t - (tok k).length)) - (g [k] + g (S.take i)) =
          gL ((flat S).take (t - (tok k).length)) - g (S.take i) := by ring
      rw [this]
      exact hi'

/-- Over the prefixes of P (J + 1), |g| <= 31 1.3^J + 4. -/
lemma word_prefix_bound (J N : ℕ) (hN : N ≤ (P (J + 1)).length) :
    |gL ((P (J + 1)).take N)| ≤ 31 * 1.3 ^ J + 4 := by
  have hp : 0 ≤ (1.3 : ℝ) ^ J := by positivity
  rw [P_length] at hN
  rcases N with _ | N
  · simp only [List.take_zero, gL, List.count_nil, Nat.cast_zero, mul_zero, sub_zero, abs_zero]
    linarith
  · rw [Y_succ_eq] at hN
    rw [P, Y_succ_eq, List.take_succ_cons, show (0 :: (flat (tau^[J] [3])).take N) =
      [0] ++ (flat (tau^[J] [3])).take N from rfl, gL_append]
    obtain ⟨i, hi, hi'⟩ := flat_split _ (tauIter_valid J _ valid_three) N (by omega)
    have h := prefix_bound J 3 (by omega) i hi
    have h0 : gL [0] = 1 := by simp [gL]
    have h1 := abs_sub_abs_le_abs_sub (gL ((flat (tau^[J] [3])).take N))
      (g ((tau^[J] [3]).take i))
    have h2 := abs_add_le (gL [0]) (gL ((flat (tau^[J] [3])).take N))
    rw [h0, abs_one] at h2
    rw [h0]
    linarith

/-! ### The length of the words Y -/

/-- The weight of a token: 0, 1, lam, lam^2 - 1 for the tokens 0, 1, 3, 4. -/
noncomputable def wt (k : ℕ) : ℝ :=
  if k = 0 then 0 else if k = 1 then 1 else if k = 3 then lam else lam ^ 2 - 1

/-- The weight of a token list; tau multiplies it by lam. -/
noncomputable def Phi (s : List ℕ) : ℝ := (s.map wt).sum

lemma Phi_append (u v : List ℕ) : Phi (u ++ v) = Phi u + Phi v := by
  simp [Phi]

lemma Phi_tau (s : List ℕ) (hs : Valid s) : Phi (tau s) = lam * Phi s := by
  obtain ⟨-, -, hp⟩ := lam_spec
  induction s with
  | nil => simp [Phi, tau]
  | cons k s ih =>
    obtain ⟨⟨hk4, hk2⟩, hs'⟩ := valid_cons hs
    rw [tau_cons, Phi_append, ih hs', show k :: s = [k] ++ s from rfl, Phi_append, mul_add]
    congr 1
    interval_cases k <;> simp [Phi, tauT, wt] <;>
      first | ring1 | linear_combination (-1 : ℝ) * hp | linear_combination hp | omega

lemma Phi_iter (J : ℕ) : Phi (tau^[J] [3]) = lam ^ (J + 1) := by
  induction J with
  | zero => simp [Phi, wt]
  | succ J ih =>
    rw [Function.iterate_succ_apply', Phi_tau _ (tauIter_valid J _ valid_three), ih, pow_succ]
    ring

lemma length_ge_Phi (s : List ℕ) (hs : Valid s) : 2 * Phi s ≤ ((flat s).length : ℝ) := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  induction s with
  | nil => simp [Phi, flat]
  | cons k s ih =>
    obtain ⟨⟨hk4, hk2⟩, hs'⟩ := valid_cons hs
    rw [flat_cons, List.length_append, show k :: s = [k] ++ s from rfl, Phi_append]
    push_cast
    have := ih hs'
    have hk' : 2 * Phi [k] ≤ ((tok k).length : ℝ) := by
      interval_cases k <;>
        first | exact absurd rfl hk2 | (simp [Phi, wt, tok] <;> norm_num <;> nlinarith)
    linarith

lemma Y_length_ge (J : ℕ) : 2 * lam ^ (J + 1) ≤ ((Y (J + 1)).length : ℝ) := by
  rw [Y_succ_eq, ← Phi_iter J]
  exact length_ge_Phi _ (tauIter_valid J _ valid_three)

lemma P_length_mono {m n : ℕ} (h : m ≤ n) : (P m).length ≤ (P n).length :=
  (P_prefix h).length_le

/-! ### Counting along the fixed point -/

lemma P_letters (n : ℕ) : ∀ x ∈ P n, x ≤ 1 := by
  intro x hx
  simp only [P, Y, List.mem_cons] at hx
  rcases hx with hx | hx
  · omega
  · simp only [flat, List.mem_flatMap, tok, List.mem_cons, List.mem_replicate] at hx
    obtain ⟨k, -, hk⟩ := hx
    omega

lemma W_le (i : ℕ) : W i ≤ 1 := by
  have hi : i < (P i).length := by have := Y_length i; rw [P_length]; omega
  rw [W_eq i i hi, List.getD_eq_getElem _ _ hi]
  exact P_letters _ _ (List.getElem_mem hi)

/-- Z(N): the number of letters 0 among the first N letters of W. -/
noncomputable def Z (N : ℕ) : ℕ := Nat.count (fun i => W i = 0) N

/-- O(N): the number of letters 1 among the first N letters of W. -/
noncomputable def O (N : ℕ) : ℕ := Nat.count (fun i => W i = 1) N

lemma Z_succ (N : ℕ) : Z (N + 1) = Z N + if W N = 0 then 1 else 0 := Nat.count_succ _ _

lemma O_succ (N : ℕ) : O (N + 1) = O N + if W N = 1 then 1 else 0 := Nat.count_succ _ _

lemma counts_eq (n N : ℕ) (hN : N ≤ (P n).length) :
    Z N = ((P n).take N).count 0 ∧ O N = ((P n).take N).count 1 := by
  induction N with
  | zero => simp [Z, O]
  | succ N ih =>
    have hN' : N < (P n).length := by omega
    have hW : W N = (P n)[N] := by rw [W_eq n N hN', List.getD_eq_getElem _ _ hN']
    obtain ⟨h1, h2⟩ := ih (by omega)
    rw [Z_succ, O_succ, h1, h2, List.take_add_one, List.getElem?_eq_getElem hN',
      List.count_append, List.count_append, hW]
    constructor <;> simp [List.count_singleton]

/-- D(N) = Z(N) - c O(N) is the deviation over the first N letters of W. -/
noncomputable def D (N : ℕ) : ℝ := (Z N : ℝ) - cc * (O N : ℝ)

lemma D_eq (n N : ℕ) (hN : N ≤ (P n).length) : D N = gL ((P n).take N) := by
  obtain ⟨h1, h2⟩ := counts_eq n N hN
  simp [D, gL, h1, h2]

lemma O_add_Z (N : ℕ) : O N + Z N = N := by
  induction N with
  | zero => simp [O, Z]
  | succ N ih =>
    rw [O_succ, Z_succ]
    have := W_le N
    split_ifs <;> omega

lemma pow_bound (J : ℕ) (hJ : 13 ≤ J) : 80 * 1.3 ^ J + 10 < lam ^ J := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  induction J, hJ using Nat.le_induction with
  | base =>
    have : (1.8392 : ℝ) ^ 13 ≤ lam ^ 13 := pow_le_pow_left₀ (by norm_num) hl1 13
    norm_num at this ⊢
    linarith
  | succ J hJ ih =>
    rw [pow_succ, pow_succ]
    have hp : 0 ≤ lam ^ J := by positivity
    nlinarith

lemma P13_length : (P 13).length = 6273 := by decide +kernel

lemma level_real (J : ℕ) (L N : ℝ) (hL : 2 * lam ^ J ≤ L) (hLN : L + 1 < N) :
    2 * lam ^ J < N := by
  linarith

/-- For N > 6273 there is a level J >= 13 with 2 lam^J < N and |D(N)| <= 31 1.3^J + 4. -/
lemma level (N : ℕ) (hN : 6273 < N) :
    ∃ J, 13 ≤ J ∧ 2 * lam ^ J < (N : ℝ) ∧ |D N| ≤ 31 * 1.3 ^ J + 4 := by
  have hex : ∃ J, N ≤ (P (J + 1)).length :=
    ⟨N, by have := Y_length (N + 1); rw [P_length]; omega⟩
  classical
  have hJN : N ≤ (P (Nat.find hex + 1)).length := Nat.find_spec hex
  have h13 := P13_length
  have hJ13 : 13 ≤ Nat.find hex := by
    by_contra h
    have := P_length_mono (show Nat.find hex + 1 ≤ 13 by omega)
    omega
  have hmin : (P (Nat.find hex)).length < N := by
    have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at this
    omega
  have hlen := Y_length_ge (Nat.find hex - 1)
  rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at hlen
  rw [P_length] at hmin
  refine ⟨Nat.find hex, hJ13, ?_, ?_⟩
  · exact level_real _ _ _ hlen
      (by exact_mod_cast (show (Y (Nat.find hex)).length + 1 < N by omega))
  · rw [D_eq (Nat.find hex + 1) N hJN]
    exact word_prefix_bound _ N hJN

/-- Over every prefix of W longer than 6273 letters, |D| < N / 5. -/
lemma D_small (N : ℕ) (hN : 6273 < N) : |D N| < (N : ℝ) / 5 := by
  obtain ⟨J, hJ, hNr, hD⟩ := level N hN
  have hp := pow_bound J hJ
  have hq : 0 ≤ (1.3 : ℝ) ^ J := by positivity
  linarith

/-- |D(N)|^2 <= 530000 N for every N >= 1. -/
lemma D_sq (N : ℕ) (hN : 1 ≤ N) : D N ^ 2 ≤ 530000 * N := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rcases le_or_gt N 6273 with h | h
  · have h13 := P13_length
    have hb : |gL ((P 13).take N)| ≤ 31 * 1.3 ^ 12 + 4 :=
      word_prefix_bound 12 N (by show N ≤ (P 13).length; omega)
    rw [D_eq 13 N (by omega)]
    have h1 : |gL ((P 13).take N)| ≤ 727 := by
      have : (31 : ℝ) * 1.3 ^ 12 + 4 ≤ 727 := by norm_num
      exact le_trans hb this
    have h2 : gL ((P 13).take N) ^ 2 ≤ 727 ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    clear hb h1 h13
    generalize gL ((P 13).take N) = x at h2 ⊢
    nlinarith
  · obtain ⟨J, hJ, hNr, hD⟩ := level N h
    have hp : 0 ≤ (1.3 : ℝ) ^ J := by positivity
    have h1 : D N ^ 2 ≤ (31 * 1.3 ^ J + 4) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hD 2
    have h2 : ((1.3 : ℝ) ^ J) ^ 2 ≤ lam ^ J := by
      rw [← pow_mul, mul_comm, pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num; linarith) J
    have h3 : (1 : ℝ) ≤ 1.3 ^ J := one_le_pow₀ (by norm_num)
    have h4 : (31 * 1.3 ^ J + 4) ^ 2 ≤ 1225 * ((1.3 : ℝ) ^ J) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h3) (by positivity : (0 : ℝ) ≤ 264 * 1.3 ^ J + 16)]
    have hlp : 0 ≤ lam ^ J := by positivity
    clear hD
    linarith

/-! ### The positions of 0 -/

/-- The limit, (1 + c)/c = 1 + 1/lam = 1.54368... -/
noncomputable def m0 : ℝ := (1 + cc) / cc

lemma m0_bounds : 1.5436 ≤ m0 ∧ m0 ≤ 1.5438 := by
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
  have h := D_small (B + 1 + (4 * Z (B + 1) + 6300)) (by omega)
  have hs := O_add_Z (B + 1 + (4 * Z (B + 1) + 6300))
  rw [hconst] at hs
  unfold D at h
  rw [hconst, abs_lt] at h
  obtain ⟨h1, -⟩ := h
  have hO : (O (B + 1 + (4 * Z (B + 1) + 6300)) : ℝ) =
      ((B + 1 + (4 * Z (B + 1) + 6300) : ℕ) : ℝ) - Z (B + 1) := by
    have : (O (B + 1 + (4 * Z (B + 1) + 6300)) : ℝ) + Z (B + 1) =
        ((B + 1 + (4 * Z (B + 1) + 6300) : ℕ) : ℝ) := by exact_mod_cast hs
    linarith
  rw [hO] at h1
  generalize hz : (Z (B + 1) : ℝ) = z at h1
  have hz0 : 0 ≤ z := by rw [← hz]; exact Nat.cast_nonneg _
  have hz' : ((B + 1 + (4 * Z (B + 1) + 6300) : ℕ) : ℝ) = (B : ℝ) + 1 + (4 * z + 6300) := by
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

/-- A linear scan of a word, checking 10000 (t + 1) < 25436 Z(t + 1) at each letter 0. -/
def chk : List ℕ → ℕ → ℕ → Bool
  | [], _, _ => true
  | x :: l, t, z =>
    if x = 0 then decide (10000 * (t + 1) < 25436 * (z + 1)) && chk l (t + 1) (z + 1)
    else chk l (t + 1) z

lemma chk_spec : ∀ (L : List ℕ) (t z : ℕ), chk L t z = true →
    ∀ i < L.length, L.getD i 0 = 0 →
      10000 * (t + i + 1) < 25436 * (z + (L.take (i + 1)).count 0) := by
  intro L
  induction L with
  | nil =>
    intro t z _ i hi
    simp at hi
  | cons x l ih =>
    intro t z h i hi hx
    by_cases h0 : x = 0
    · subst h0
      have h' : 10000 * (t + 1) < 25436 * (z + 1) ∧ chk l (t + 1) (z + 1) = true := by
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

lemma chk_word : chk (P 13) 0 0 = true := by decide +kernel

lemma bound_small (n : ℕ) (hn : 1 ≤ n) (ha : a n ≤ 6273) :
    -1 < m0 - (a n : ℝ) / n ∧ m0 - (a n : ℝ) / n < 1 := by
  obtain ⟨hm1, hm2⟩ := m0_bounds
  obtain ⟨hZ, hO⟩ := a_spec n hn
  have hinf := zeros_infinite
  have hWp : W (Nat.nth (fun i => W i = 0) (n - 1)) = 0 := Nat.nth_mem_of_infinite hinf (n - 1)
  have ha' : a n = Nat.nth (fun i => W i = 0) (n - 1) + 1 := rfl
  set t := Nat.nth (fun i => W i = 0) (n - 1) with ht
  have hlen := P13_length
  have hW : (P 13).getD t 0 = 0 := by rw [← W_eq 13 t (by omega)]; exact hWp
  have hc := chk_spec (P 13) 0 0 chk_word t (by omega) hW
  have hZ' : ((P 13).take (t + 1)).count 0 = n := by
    rw [← (counts_eq 13 (t + 1) (by omega)).1, ← ha', hZ]
  rw [hZ'] at hc
  simp only [zero_add] at hc
  have hle : n ≤ a n := by have := O_add_Z (a n); omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hc' : (10000 : ℝ) * (a n) < 25436 * n := by
    rw [ha']
    exact_mod_cast hc
  have hle' : (n : ℝ) ≤ a n := by exact_mod_cast hle
  have h1 : (a n : ℝ) / n < 2.5436 := by
    rw [div_lt_iff₀ hnpos]
    linarith
  have h2 : 1 ≤ (a n : ℝ) / n := by
    rw [le_div_iff₀ hnpos]
    linarith
  constructor <;> linarith

lemma bound_large (n : ℕ) (hn : 1 ≤ n) (ha : 6273 < a n) :
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
  have hP : 1.8392 * (a n : ℝ) ≤ cc * a n := mul_le_mul_of_nonneg_right hc1 hA0
  have hQ1 : 1.8392 * (n : ℝ) ≤ cc * n := mul_le_mul_of_nonneg_right hc1 hnpos.le
  have hQ2 : cc * (n : ℝ) ≤ 1.8393 * n := mul_le_mul_of_nonneg_right hc2 hnpos.le
  have hE : cc * ((a n : ℝ) - n) = cc * a n - cc * n := by ring
  rw [hE] at hD1 hD2 ⊢
  constructor
  · rw [lt_div_iff₀ hnpos, lt_div_iff₀ hc]
    linarith
  · rw [div_lt_iff₀ hnpos, div_lt_iff₀ hc]
    linarith

/-- Kimberling's conjecture: a(n)/n tends to a number m = 1.54..., and -1 < m - a(n)/n < 1
for n >= 1. -/
theorem conjecture : ∃ m : ℝ, (1.54 ≤ m ∧ m < 1.55) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 m) ∧
    ∀ n : ℕ, 1 ≤ n → -1 < m - (a n : ℝ) / n ∧ m - (a n : ℝ) / n < 1 := by
  obtain ⟨hm1, hm2⟩ := m0_bounds
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hc : 0 < cc := by linarith
  have hbound : ∀ n : ℕ, 1 ≤ n → -1 < m0 - (a n : ℝ) / n ∧ m0 - (a n : ℝ) / n < 1 := by
    intro n hn
    rcases le_or_gt (a n) 6273 with h | h
    · exact bound_small n hn h
    · exact bound_large n hn h
  refine ⟨m0, ⟨by linarith, by linarith⟩, ?_, hbound⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => Real.sqrt (530000 * 3 / cc ^ 2 / n)) atTop (𝓝 0) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (530000 * 3 / cc ^ 2)).sqrt
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hZ, hO⟩ := a_spec n hn
  have hle : n ≤ a n := by have := O_add_Z (a n); omega
  have hsq := D_sq (a n) (le_trans hn hle)
  have hb := hbound n hn
  have ha3 : (a n : ℝ) ≤ 3 * n := by
    have h1 : (a n : ℝ) / n < 2.5439 := by linarith [hb.1]
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
  have hD3 : D (a n) ^ 2 ≤ 530000 * (3 * n) := by
    have : (530000 : ℝ) * (a n) ≤ 530000 * (3 * n) := by linarith
    linarith
  have e2 : 530000 * 3 / cc ^ 2 * (cc ^ 2 * (n : ℝ) ^ 2) = 530000 * 3 * n ^ 2 := by
    field_simp
  rw [e2]
  nlinarith [hD3, hnpos]

end OMA.S_oeis_a288597

theorem OMA.solution : type_of% @OMA.S_oeis_a288597.main :=
  OMA.S_oeis_a288597.conjecture

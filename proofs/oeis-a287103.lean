import OMAStatements.S_oeis_a287103

namespace OMA.S_oeis_a287103

open Filter Topology





/-! ### One pass -/

/-- A word is closed when the pass over it followed by any word is the pass over it followed by
the pass over that word. -/
def Closed (u : List ℕ) : Prop := ∀ y, step (u ++ y) = step u ++ step y

lemma closed_append {u v : List ℕ} (hu : Closed u) (hv : Closed v) : Closed (u ++ v) := by
  intro y
  rw [List.append_assoc, hu (v ++ y), hv y, hu v, List.append_assoc]

/-! ### Tokens -/

/-- The tokens A = 00, B = 1000, C = 01000, D = 11000, E = 011000. -/
def tok : ℕ → List ℕ
  | 0 => [0, 0]
  | 1 => [1, 0, 0, 0]
  | 2 => [0, 1, 0, 0, 0]
  | 3 => [1, 1, 0, 0, 0]
  | _ => [0, 1, 1, 0, 0, 0]

/-- All tokens are 0, 1, 2, 3 or 4. -/
def Valid (s : List ℕ) : Prop := ∀ k ∈ s, k ≤ 4

lemma tok_closed (k : ℕ) (hk : k ≤ 4) : Closed (tok k) := by
  interval_cases k <;> exact fun _ => rfl

/-- The word of a list of tokens. -/
def flat (s : List ℕ) : List ℕ := s.flatMap tok

/-- The images of the tokens under one pass: A -> B, B -> AE, C -> AAD, D -> BD, E -> CD. -/
def tauT : ℕ → List ℕ
  | 0 => [1]
  | 1 => [0, 4]
  | 2 => [0, 0, 3]
  | 3 => [1, 3]
  | _ => [2, 3]

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

lemma step_tok (k : ℕ) (hk : k ≤ 4) : step (tok k) = flat (tauT k) := by
  interval_cases k <;> rfl

lemma step_flat (s : List ℕ) (hs : Valid s) : step (flat s) = flat (tau s) := by
  induction s with
  | nil => rfl
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    rw [flat_cons, tok_closed k hk, step_tok k hk, ih hs', tau_cons, flat_append]

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

lemma flat_length_ge (s : List ℕ) (hs : Valid s) : 2 * s.length ≤ (flat s).length := by
  induction s with
  | nil => simp [flat]
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    rw [flat_cons, List.length_append, List.length_cons]
    have := ih hs'
    interval_cases k <;> simp [tok] <;> omega

/-! ### The iterates -/

lemma iter_eq (n : ℕ) : iter n = flat (tau^[n] [0]) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show iter (n + 1) = step (iter n) from rfl, ih,
      step_flat _ (tauIter_valid n _ (valid_single (by norm_num))),
      ← Function.iterate_succ_apply' tau n]

/-- Iterate n + 2 is iterate n followed by the word of tau^n(E). -/
lemma iter_two (n : ℕ) : iter (n + 2) = iter n ++ flat (tau^[n] [4]) := by
  rw [iter_eq, iter_eq, Function.iterate_add_apply, show tau^[2] [0] = [0] ++ [4] from rfl,
    tauIter_append, flat_append]

lemma iter_prefix_two (n : ℕ) : iter n <+: iter (n + 2) := by
  rw [iter_two]
  exact List.prefix_append _ _

lemma iter_length_lin (n : ℕ) : n + 2 ≤ (iter n).length ∧ n + 3 ≤ (iter (n + 1)).length := by
  induction n with
  | zero => decide
  | succ n ih =>
    obtain ⟨h0, h1⟩ := ih
    refine ⟨h1, ?_⟩
    rw [show n + 1 + 1 = n + 2 from rfl, iter_two, List.length_append]
    have h2 := flat_length_ge (tau^[n] [4]) (tauIter_valid _ _ (valid_single (by norm_num)))
    have h3 := List.length_pos_of_ne_nil (tauIter_ne_nil n [4] (by simp))
    omega

lemma iter_length (n : ℕ) : n + 2 ≤ (iter n).length := (iter_length_lin n).1

lemma iter_letters (n : ℕ) : ∀ x ∈ iter n, x ≤ 1 := by
  intro x hx
  rw [iter_eq] at hx
  simp only [flat, List.mem_flatMap] at hx
  obtain ⟨k, -, hk⟩ := hx
  rcases k with _ | _ | _ | _ | k <;> simp [tok] at hk <;> omega

lemma getD_prefix {l₁ l₂ : List ℕ} (h : l₁ <+: l₂) {i : ℕ} (hi : i < l₁.length) :
    l₁.getD i 0 = l₂.getD i 0 := by
  obtain ⟨s, rfl⟩ := h
  rw [List.getD_append _ _ _ _ hi]

/-! ### The limiting word -/

/-- The residue mod 2 of the iterates whose limit is W. -/
def res : ℕ := 0

/-- V k: iterate 2k + res. -/
def V (k : ℕ) : List ℕ := iter (2 * k + res)

lemma V_prefix_succ (k : ℕ) : V k <+: V (k + 1) := by
  unfold V
  rw [show 2 * (k + 1) + res = 2 * k + res + 2 by ring]
  exact iter_prefix_two _

lemma V_prefix {k k' : ℕ} (h : k ≤ k') : V k <+: V k' := by
  induction k', h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ k' _ ih => exact ih.trans (V_prefix_succ k')

lemma V_length (k : ℕ) : k + 2 ≤ (V k).length := by
  unfold V
  have := iter_length (2 * k + res)
  omega

lemma W_eq (k i : ℕ) (hi : i < (V k).length) : W i = (V k).getD i 0 := by
  have hW : W i = (V (i + 1)).getD i 0 := rfl
  have hi' : i < (V (i + 1)).length := by have := V_length (i + 1); omega
  rw [hW]
  rcases le_total (i + 1) k with h | h
  · exact getD_prefix (V_prefix h) hi'
  · exact (getD_prefix (V_prefix h) hi).symm

/-! ### The real roots of x^5 - x^4 - x^3 - 3x + 2 -/

lemma lam_exists :
    ∃ x : ℝ, 1.846225 ≤ x ∧ x ≤ 1.846226 ∧ x ^ 5 - x ^ 4 - x ^ 3 - 3 * x + 2 = 0 := by
  have hc : ContinuousOn (fun x : ℝ => x ^ 5 - x ^ 4 - x ^ 3 - 3 * x + 2)
      (Set.Icc 1.846225 1.846226) := by fun_prop
  have h := intermediate_value_Icc (show (1.846225 : ℝ) ≤ 1.846226 by norm_num) hc
  have h0 : (0 : ℝ) ∈ Set.Icc ((fun x : ℝ => x ^ 5 - x ^ 4 - x ^ 3 - 3 * x + 2) 1.846225)
      ((fun x : ℝ => x ^ 5 - x ^ 4 - x ^ 3 - 3 * x + 2) 1.846226) := by
    constructor <;> norm_num
  obtain ⟨x, ⟨hx1, hx2⟩, hx⟩ := h h0
  exact ⟨x, hx1, hx2, hx⟩

lemma mu_exists :
    ∃ x : ℝ, -1.386768 ≤ x ∧ x ≤ -1.386767 ∧ x ^ 5 - x ^ 4 - x ^ 3 - 3 * x + 2 = 0 := by
  have hc : ContinuousOn (fun x : ℝ => x ^ 5 - x ^ 4 - x ^ 3 - 3 * x + 2)
      (Set.Icc (-1.386768) (-1.386767)) := by fun_prop
  have h := intermediate_value_Icc (show (-1.386768 : ℝ) ≤ -1.386767 by norm_num) hc
  have h0 : (0 : ℝ) ∈ Set.Icc ((fun x : ℝ => x ^ 5 - x ^ 4 - x ^ 3 - 3 * x + 2) (-1.386768))
      ((fun x : ℝ => x ^ 5 - x ^ 4 - x ^ 3 - 3 * x + 2) (-1.386767)) := by
    constructor <;> norm_num
  obtain ⟨x, ⟨hx1, hx2⟩, hx⟩ := h h0
  exact ⟨x, hx1, hx2, hx⟩

lemma nu_exists :
    ∃ x : ℝ, 0.584102 ≤ x ∧ x ≤ 0.584103 ∧ x ^ 5 - x ^ 4 - x ^ 3 - 3 * x + 2 = 0 := by
  have hc : ContinuousOn (fun x : ℝ => x ^ 5 - x ^ 4 - x ^ 3 - 3 * x + 2)
      (Set.Icc 0.584102 0.584103) := by fun_prop
  have h := intermediate_value_Icc' (show (0.584102 : ℝ) ≤ 0.584103 by norm_num) hc
  have h0 : (0 : ℝ) ∈ Set.Icc ((fun x : ℝ => x ^ 5 - x ^ 4 - x ^ 3 - 3 * x + 2) 0.584103)
      ((fun x : ℝ => x ^ 5 - x ^ 4 - x ^ 3 - 3 * x + 2) 0.584102) := by
    constructor <;> norm_num
  obtain ⟨x, ⟨hx1, hx2⟩, hx⟩ := h h0
  exact ⟨x, hx1, hx2, hx⟩

/-- The Perron root, 1.84622..., the growth rate of the iterates. -/
noncomputable def lam : ℝ := Classical.choose lam_exists

/-- The negative real root, -1.38676... -/
noncomputable def mu : ℝ := Classical.choose mu_exists

/-- The real root inside the unit disk, 0.58410... -/
noncomputable def nu : ℝ := Classical.choose nu_exists

lemma lam_spec :
    1.846225 ≤ lam ∧ lam ≤ 1.846226 ∧ lam ^ 5 - lam ^ 4 - lam ^ 3 - 3 * lam + 2 = 0 :=
  Classical.choose_spec lam_exists

lemma mu_spec : -1.386768 ≤ mu ∧ mu ≤ -1.386767 ∧ mu ^ 5 - mu ^ 4 - mu ^ 3 - 3 * mu + 2 = 0 :=
  Classical.choose_spec mu_exists

lemma nu_spec : 0.584102 ≤ nu ∧ nu ≤ 0.584103 ∧ nu ^ 5 - nu ^ 4 - nu ^ 3 - 3 * nu + 2 = 0 :=
  Classical.choose_spec nu_exists

lemma lam_pows : 3.4085467 ≤ lam ^ 2 ∧ lam ^ 2 ≤ 3.4085505 ∧ 6.2929442 ≤ lam ^ 3 ∧
    lam ^ 3 ≤ 6.2929545 ∧ 11.6181909 ≤ lam ^ 4 ∧ lam ^ 4 ≤ 11.6182162 := by
  obtain ⟨h1, h2, -⟩ := lam_spec
  have a2 := pow_le_pow_left₀ (by norm_num) h1 2
  have b2 := pow_le_pow_left₀ (by linarith) h2 2
  have a3 := pow_le_pow_left₀ (by norm_num) h1 3
  have b3 := pow_le_pow_left₀ (by linarith) h2 3
  have a4 := pow_le_pow_left₀ (by norm_num) h1 4
  have b4 := pow_le_pow_left₀ (by linarith) h2 4
  norm_num at a2 b2 a3 b3 a4 b4
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- The limiting number of letters 0 per letter 1, 2.53306... -/
noncomputable def cc : ℝ := -1 / 2 - lam / 4 - 3 * lam ^ 2 / 4 + lam ^ 3 / 2 + lam ^ 4 / 4

lemma cc_bounds : 2.53305 ≤ cc ∧ cc ≤ 2.53307 := by
  obtain ⟨h1, h2, -⟩ := lam_spec
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := lam_pows
  unfold cc
  constructor <;> linarith

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

lemma letter_counts (s : List ℕ) (hs : Valid s) :
    (flat s).count 0 = 2 * s.count 0 + 3 * s.count 1 + 4 * s.count 2 + 3 * s.count 3 +
      4 * s.count 4 ∧ (flat s).count 1 = s.count 1 + s.count 2 + 2 * s.count 3 + 2 * s.count 4 := by
  induction s with
  | nil => simp [flat]
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    obtain ⟨h0, h1⟩ := ih hs'
    rw [flat_cons, List.count_append, List.count_append, h0, h1]
    interval_cases k <;> simp [tok] <;> omega

lemma g_counts (s : List ℕ) (hs : Valid s) :
    g s = 2 * (s.count 0 : ℝ) + (3 - cc) * (s.count 1 : ℝ) + (4 - cc) * (s.count 2 : ℝ) +
      (3 - 2 * cc) * (s.count 3 : ℝ) + (4 - 2 * cc) * (s.count 4 : ℝ) := by
  obtain ⟨h0, h1⟩ := letter_counts s hs
  unfold g gL
  rw [h0, h1]
  push_cast
  ring

lemma tau_counts (s : List ℕ) (hs : Valid s) :
    (tau s).count 0 = s.count 1 + 2 * s.count 2 ∧ (tau s).count 1 = s.count 0 + s.count 3 ∧
      (tau s).count 2 = s.count 4 ∧ (tau s).count 3 = s.count 2 + s.count 3 + s.count 4 ∧
      (tau s).count 4 = s.count 1 := by
  induction s with
  | nil => simp [tau]
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    obtain ⟨h0, h1, h2, h3, h4⟩ := ih hs'
    rw [tau_cons, List.count_append, List.count_append, List.count_append, List.count_append,
      List.count_append]
    interval_cases k <;> simp [tauT] <;> omega

/-- The deviation has no component along the Perron root: it follows the quartic
f(x)/(x - lam). -/
lemma g_rec (s : List ℕ) (hs : Valid s) :
    g (tau (tau (tau (tau s)))) + (lam - 1) * g (tau (tau (tau s))) +
      (lam ^ 2 - lam - 1) * g (tau (tau s)) + (lam ^ 3 - lam ^ 2 - lam) * g (tau s) +
      (lam ^ 4 - lam ^ 3 - lam ^ 2 - 3) * g s = 0 := by
  obtain ⟨-, -, hf⟩ := lam_spec
  have v1 := tau_valid s
  have v2 := tau_valid (tau s)
  have v3 := tau_valid (tau (tau s))
  have v4 := tau_valid (tau (tau (tau s)))
  obtain ⟨a0, a1, a2, a3, a4⟩ := tau_counts s hs
  obtain ⟨b0, b1, b2, b3, b4⟩ := tau_counts (tau s) v1
  obtain ⟨d0, d1, d2, d3, d4⟩ := tau_counts (tau (tau s)) v2
  obtain ⟨e0, e1, e2, e3, e4⟩ := tau_counts (tau (tau (tau s))) v3
  rw [g_counts _ v4, g_counts _ v3, g_counts _ v2, g_counts _ v1, g_counts _ hs,
    e0, e1, e2, e3, e4, d0, d1, d2, d3, d4, b0, b1, b2, b3, b4, a0, a1, a2, a3, a4]
  unfold cc
  push_cast
  linear_combination ((s.count 0 : ℝ) * (-5 / 4 - lam - lam ^ 2 / 4) +
    (s.count 1 : ℝ) * (-2 - 5 * lam / 4 - lam ^ 2 - lam ^ 3 / 4) +
    (s.count 2 : ℝ) * (-3 - 3 * lam / 2 - lam ^ 2 - lam ^ 3 / 4) +
    (s.count 3 : ℝ) * (-2 - 5 * lam / 4 - 7 * lam ^ 2 / 4 - lam ^ 3 / 2) +
    (s.count 4 : ℝ) * (-9 / 4 - 5 * lam / 4 - 7 * lam ^ 2 / 4 - lam ^ 3 / 2)) * hf

/-! ### Removing the real modes -/

/-- A root of x^5 - x^4 - x^3 - 3x + 2 other than lam is a root of the quartic. -/
lemma Q_root (x : ℝ) (hx : x ^ 5 - x ^ 4 - x ^ 3 - 3 * x + 2 = 0) (hne : x ≠ lam) :
    x ^ 4 + (lam - 1) * x ^ 3 + (lam ^ 2 - lam - 1) * x ^ 2 + (lam ^ 3 - lam ^ 2 - lam) * x +
      (lam ^ 4 - lam ^ 3 - lam ^ 2 - 3) = 0 := by
  obtain ⟨-, -, hf⟩ := lam_spec
  have h : (x - lam) * (x ^ 4 + (lam - 1) * x ^ 3 + (lam ^ 2 - lam - 1) * x ^ 2 +
      (lam ^ 3 - lam ^ 2 - lam) * x + (lam ^ 4 - lam ^ 3 - lam ^ 2 - 3)) = 0 := by
    linear_combination hx - hf
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact h

/-- The coefficients of the cubic left after removing the nu-mode. -/
noncomputable def e2 : ℝ := lam - 1 + nu

noncomputable def e1 : ℝ := lam ^ 2 - lam - 1 + nu * e2

noncomputable def e0 : ℝ := lam ^ 3 - lam ^ 2 - lam + nu * e1

/-- The coefficients of the quadratic of the complex pair. -/
noncomputable def pp : ℝ := e2 + mu

noncomputable def qq : ℝ := e1 + mu * pp

lemma hQnu : lam ^ 4 - lam ^ 3 - lam ^ 2 - 3 + nu * e0 = 0 := by
  obtain ⟨hl1, -, -⟩ := lam_spec
  obtain ⟨-, hn2, hn⟩ := nu_spec
  have h := Q_root nu hn (fun h => by linarith)
  simp only [e0, e1, e2]
  linear_combination h

lemma hRmu : e0 + mu * qq = 0 := by
  obtain ⟨hl1, -, -⟩ := lam_spec
  obtain ⟨-, hm2, hm⟩ := mu_spec
  obtain ⟨hn1, hn2, hn⟩ := nu_spec
  have h1 := Q_root mu hm (fun h => by linarith)
  have h2 := Q_root nu hn (fun h => by linarith)
  have h : (mu - nu) * (e0 + mu * qq) = 0 := by
    simp only [qq, pp, e0, e1, e2]
    linear_combination h1 - h2
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (sub_eq_zero.mp h) (by linarith)
  · exact h

/-- Corner bounds for a product of a nonpositive and a nonnegative interval quantity. -/
lemma neg_pos_mul {x y x1 x2 y1 y2 : ℝ} (hx1 : x1 ≤ x) (hx2 : x ≤ x2) (hx0 : x2 ≤ 0)
    (hy1 : y1 ≤ y) (hy2 : y ≤ y2) (hy0 : 0 ≤ y1) : x1 * y2 ≤ x * y ∧ x * y ≤ x2 * y1 := by
  have a1 := mul_nonneg (sub_nonneg.2 hx1) (hy0.trans hy1)
  have a2 := mul_nonneg (neg_nonneg.2 (hx1.trans (hx2.trans hx0))) (sub_nonneg.2 hy2)
  have a3 := mul_nonneg (sub_nonneg.2 hx2) hy0
  have a4 := mul_nonneg (neg_nonneg.2 (hx2.trans hx0)) (sub_nonneg.2 hy1)
  constructor <;> nlinarith

/-- Corner bounds for a product of two nonnegative interval quantities. -/
lemma pos_pos_mul {x y x1 x2 y1 y2 : ℝ} (hx1 : x1 ≤ x) (hx2 : x ≤ x2) (hx0 : 0 ≤ x1)
    (hy1 : y1 ≤ y) (hy2 : y ≤ y2) (hy0 : 0 ≤ y1) : x1 * y1 ≤ x * y ∧ x * y ≤ x2 * y2 := by
  have a1 := mul_nonneg (sub_nonneg.2 hx1) (hy0.trans hy1)
  have a2 := mul_nonneg hx0 (sub_nonneg.2 hy1)
  have a3 := mul_nonneg (sub_nonneg.2 hx2) (hy0.trans (hy1.trans hy2))
  have a4 := mul_nonneg (hx0.trans hx1) (sub_nonneg.2 hy2)
  constructor <;> nlinarith

lemma pq_bounds : 0.043559 ≤ pp ∧ pp ≤ 0.043562 ∧ 1.33736 ≤ qq ∧ qq ≤ 1.33738 := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  obtain ⟨hm1, hm2, -⟩ := mu_spec
  obtain ⟨hn1, hn2, -⟩ := nu_spec
  obtain ⟨p1, p2, -, -, -, -⟩ := lam_pows
  have he2 : 1.430327 ≤ e2 ∧ e2 ≤ 1.430329 := by unfold e2; constructor <;> linarith
  obtain ⟨ne1, ne2⟩ := pos_pos_mul hn1 hn2 (by norm_num) he2.1 he2.2 (by norm_num)
  have he1 : 1.397777 ≤ e1 ∧ e1 ≤ 1.397786 := by unfold e1; constructor <;> linarith
  have hp : 0.043559 ≤ pp ∧ pp ≤ 0.043562 := by
    unfold pp
    constructor <;> linarith [he2.1, he2.2]
  obtain ⟨mp1, mp2⟩ := neg_pos_mul hm1 hm2 (by norm_num) hp.1 hp.2 (by norm_num)
  refine ⟨hp.1, hp.2, ?_, ?_⟩ <;> unfold qq <;> linarith [he1.1, he1.2]

/-! ### The filtered deviations -/

/-- u x j: the deviation of tau^j(x). -/
noncomputable def u (x j : ℕ) : ℝ := g (tau^[j] [x])

/-- v x j: u without its nu-mode. -/
noncomputable def v (x j : ℕ) : ℝ := u x (j + 1) - nu * u x j

/-- w x j: v without its mu-mode. -/
noncomputable def w (x j : ℕ) : ℝ := v x (j + 1) - mu * v x j

lemma u_rec (x j : ℕ) (hx : x ≤ 4) :
    u x (j + 4) + (lam - 1) * u x (j + 3) + (lam ^ 2 - lam - 1) * u x (j + 2) +
      (lam ^ 3 - lam ^ 2 - lam) * u x (j + 1) + (lam ^ 4 - lam ^ 3 - lam ^ 2 - 3) * u x j = 0 := by
  have hv : Valid (tau^[j] [x]) := tauIter_valid j _ (valid_single hx)
  have e1 : tau^[j + 1] [x] = tau (tau^[j] [x]) := Function.iterate_succ_apply' _ _ _
  have e2 : tau^[j + 2] [x] = tau (tau (tau^[j] [x])) := by
    rw [show j + 2 = j + 1 + 1 from rfl, Function.iterate_succ_apply', e1]
  have e3 : tau^[j + 3] [x] = tau (tau (tau (tau^[j] [x]))) := by
    rw [show j + 3 = j + 2 + 1 from rfl, Function.iterate_succ_apply', e2]
  have e4 : tau^[j + 4] [x] = tau (tau (tau (tau (tau^[j] [x])))) := by
    rw [show j + 4 = j + 3 + 1 from rfl, Function.iterate_succ_apply', e3]
  unfold u
  rw [e4, e3, e2, e1]
  exact g_rec _ hv

lemma v_rec (x j : ℕ) (hx : x ≤ 4) :
    v x (j + 3) + e2 * v x (j + 2) + e1 * v x (j + 1) + e0 * v x j = 0 := by
  have h := u_rec x j hx
  have hq := hQnu
  unfold v
  rw [show j + 3 + 1 = j + 4 from rfl, show j + 2 + 1 = j + 3 from rfl,
    show j + 1 + 1 = j + 2 from rfl]
  simp only [e0, e1, e2] at hq ⊢
  linear_combination h - u x j * hq

lemma w_rec (x j : ℕ) (hx : x ≤ 4) : w x (j + 2) + pp * w x (j + 1) + qq * w x j = 0 := by
  have h := v_rec x j hx
  have hr := hRmu
  unfold w
  rw [show j + 2 + 1 = j + 3 from rfl, show j + 1 + 1 = j + 2 from rfl]
  simp only [qq, pp] at hr ⊢
  linear_combination h - v x j * hr

/-! ### The quadratic form of the complex pair -/

/-- The quadratic form along w. -/
noncomputable def E (x j : ℕ) : ℝ := w x (j + 1) ^ 2 + pp * w x (j + 1) * w x j + qq * w x j ^ 2

lemma E_succ (x j : ℕ) (hx : x ≤ 4) : E x (j + 1) = qq * E x j := by
  have h := w_rec x j hx
  have e : w x (j + 2) = -(pp * w x (j + 1) + qq * w x j) := by linarith
  unfold E
  rw [show j + 1 + 1 = j + 2 from rfl, e]
  ring

lemma E_ge (x j : ℕ) : 1.336 * w x j ^ 2 ≤ E x j := by
  obtain ⟨hp1, hp2, hq1, hq2⟩ := pq_bounds
  unfold E
  have h : w x (j + 1) ^ 2 + pp * w x (j + 1) * w x j + qq * w x j ^ 2 =
      (w x (j + 1) + pp / 2 * w x j) ^ 2 + (qq - pp ^ 2 / 4) * w x j ^ 2 := by ring
  rw [h]
  have h2 : 1.336 ≤ qq - pp ^ 2 / 4 := by nlinarith
  have h3 : 0 ≤ w x j ^ 2 := sq_nonneg _
  nlinarith [sq_nonneg (w x (j + 1) + pp / 2 * w x j)]

lemma E_nonneg (x j : ℕ) : 0 ≤ E x j := by
  have := E_ge x j
  have h3 : 0 ≤ w x j ^ 2 := sq_nonneg _
  linarith

lemma E_le (x j : ℕ) (hx : x ≤ 4) (K : ℝ) (h0 : E x 0 ≤ K) : E x j ≤ K * 1.3456 ^ j := by
  obtain ⟨hp1, hp2, hq1, hq2⟩ := pq_bounds
  induction j with
  | zero => simpa using h0
  | succ j ih =>
    rw [E_succ x j hx, pow_succ (1.3456 : ℝ) j]
    have h1 := E_nonneg x j
    have h2 := mul_le_mul_of_nonneg_right (show qq ≤ 1.3456 by linarith) h1
    have h3 : 0 ≤ (1.3456 : ℝ) ^ j := by positivity
    nlinarith

lemma w_bound (x j : ℕ) (hx : x ≤ 4) (K Kw : ℝ) (h0 : E x 0 ≤ K) (hK : K ≤ 1.336 * Kw ^ 2)
    (hKw : 0 ≤ Kw) : |w x j| ≤ Kw * 1.16 ^ j := by
  apply abs_le_of_sq_le_sq _ (by positivity)
  have h1 := E_ge x j
  have h2 := E_le x j hx K h0
  have e : (Kw * (1.16 : ℝ) ^ j) ^ 2 = Kw ^ 2 * 1.3456 ^ j := by
    rw [mul_pow, ← pow_mul, mul_comm j 2, pow_mul]
    norm_num
  rw [e]
  have hp : 0 ≤ (1.3456 : ℝ) ^ j := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hK hp]

lemma v_bound (x j : ℕ) (Kw Kp Kv : ℝ) (hw : ∀ j, |w x j| ≤ Kw * 1.16 ^ j)
    (h0 : |v x 0| ≤ Kv - Kp) (hKp : Kw ≤ 0.2267 * Kp) (hKp0 : 0 ≤ Kp) :
    |v x j| ≤ Kv * 1.39 ^ j - Kp * 1.16 ^ j := by
  obtain ⟨hm1, hm2, -⟩ := mu_spec
  induction j with
  | zero => simpa using h0
  | succ j ih =>
    have e : v x (j + 1) = mu * v x j + w x j := by unfold w; ring
    rw [e, pow_succ (1.39 : ℝ) j, pow_succ (1.16 : ℝ) j]
    have h1 := abs_add_le (mu * v x j) (w x j)
    rw [abs_mul, abs_of_neg (by linarith : mu < 0)] at h1
    have h2 := mul_le_mul_of_nonneg_left ih (by linarith : (0 : ℝ) ≤ -mu)
    have h3 := hw j
    have hb : 0 ≤ Kv * 1.39 ^ j - Kp * 1.16 ^ j := le_trans (abs_nonneg _) ih
    have hs : (0 : ℝ) ≤ 1.16 ^ j := by positivity
    have hq : 0 ≤ Kp * (1.16 : ℝ) ^ j := by positivity
    have hr : 0 ≤ Kv * (1.39 : ℝ) ^ j := by linarith
    have i1 := mul_le_mul_of_nonneg_right (show -mu ≤ 1.39 by linarith) hr
    have i2 := mul_le_mul_of_nonneg_right (show (1.3867 : ℝ) ≤ -mu by linarith) hq
    have i3 := mul_le_mul_of_nonneg_right hKp hs
    linarith

lemma u_bound (x j : ℕ) (Kp Kv Ku : ℝ) (hv : ∀ j, |v x j| ≤ Kv * 1.39 ^ j - Kp * 1.16 ^ j)
    (hKp0 : 0 ≤ Kp) (h0 : |u x 0| ≤ Ku) (hKu : Kv ≤ 0.8058 * Ku) : |u x j| ≤ Ku * 1.39 ^ j := by
  obtain ⟨hn1, hn2, -⟩ := nu_spec
  induction j with
  | zero => simpa using h0
  | succ j ih =>
    have e : u x (j + 1) = nu * u x j + v x j := by unfold v; ring
    rw [e, pow_succ (1.39 : ℝ) j]
    have h1 := abs_add_le (nu * u x j) (v x j)
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < nu)] at h1
    have h2 := mul_le_mul_of_nonneg_left ih (by linarith : (0 : ℝ) ≤ nu)
    have h3 := hv j
    have hs : (0 : ℝ) ≤ 1.39 ^ j := by positivity
    have hq : 0 ≤ Kp * (1.16 : ℝ) ^ j := by positivity
    have hr : 0 ≤ Ku * (1.39 : ℝ) ^ j := le_trans (abs_nonneg _) ih
    have i1 := mul_le_mul_of_nonneg_right (show nu ≤ 0.5842 by linarith) hr
    have i2 := mul_le_mul_of_nonneg_right hKu hs
    linarith

/-! ### The starting values for B and C -/

lemma u_vals : u 1 0 = 3 - cc ∧ u 1 1 = 6 - 2 * cc ∧ u 1 2 = 10 - 4 * cc ∧ u 1 3 = 19 - 7 * cc ∧
    u 2 0 = 4 - cc ∧ u 2 1 = 7 - 2 * cc ∧ u 2 2 = 12 - 5 * cc ∧ u 2 3 = 24 - 9 * cc := by
  have k : ∀ (s : List ℕ) (z o : ℕ), (flat s).count 0 = z → (flat s).count 1 = o →
      g s = z - cc * o := by
    intro s z o hz ho
    unfold g gL
    rw [hz, ho]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show u 1 0 = g [1] from rfl, k _ 3 1 (by decide) (by decide)]; ring
  · rw [show u 1 1 = g [0, 4] from rfl, k _ 6 2 (by decide) (by decide)]; ring
  · rw [show u 1 2 = g [1, 2, 3] from rfl, k _ 10 4 (by decide) (by decide)]; ring
  · rw [show u 1 3 = g [0, 4, 0, 0, 3, 1, 3] from rfl, k _ 19 7 (by decide) (by decide)]; ring
  · rw [show u 2 0 = g [2] from rfl, k _ 4 1 (by decide) (by decide)]; ring
  · rw [show u 2 1 = g [0, 0, 3] from rfl, k _ 7 2 (by decide) (by decide)]; ring
  · rw [show u 2 2 = g [1, 1, 1, 3] from rfl, k _ 12 5 (by decide) (by decide)]; ring
  · rw [show u 2 3 = g [0, 4, 0, 4, 0, 4, 1, 3] from rfl, k _ 24 9 (by decide) (by decide)]; ring

/-- The form at the start, from bounds on w x 0 and w x 1. -/
lemma E_zero_le (x : ℕ) (W0 W1 : ℝ) (h0 : |w x 0| ≤ W0) (h1 : |w x 1| ≤ W1) :
    E x 0 ≤ W1 ^ 2 + 0.043562 * (W1 * W0) + 1.33738 * W0 ^ 2 := by
  obtain ⟨hp1, hp2, hq1, hq2⟩ := pq_bounds
  have e : E x 0 = w x 1 ^ 2 + pp * w x 1 * w x 0 + qq * w x 0 ^ 2 := rfl
  rw [e]
  have hW0 : 0 ≤ W0 := le_trans (abs_nonneg _) h0
  have hW1 : 0 ≤ W1 := le_trans (abs_nonneg _) h1
  have a0 : w x 0 ^ 2 ≤ W0 ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h0 2
  have a1 : w x 1 ^ 2 ≤ W1 ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have a2 : pp * w x 1 * w x 0 ≤ 0.043562 * (W1 * W0) := by
    have hm := mul_le_mul h1 h0 (abs_nonneg _) hW1
    have hpos : 0 ≤ |w x 1| * |w x 0| := by positivity
    have h' : |pp * w x 1 * w x 0| ≤ 0.043562 * (W1 * W0) := by
      rw [abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < pp), mul_assoc]
      have := mul_le_mul_of_nonneg_right hp2 hpos
      have := mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 0.043562)
      linarith
    exact le_trans (le_abs_self _) h'
  have a3 : qq * w x 0 ^ 2 ≤ 1.33738 * W0 ^ 2 := by
    have h2 := sq_nonneg (w x 0)
    have := mul_le_mul_of_nonneg_right hq2 h2
    have := mul_le_mul_of_nonneg_left a0 (by norm_num : (0 : ℝ) ≤ 1.33738)
    linarith
  linarith

/-- Interval bounds for the products of mu, nu and c met in the starting values. -/
lemma start_prods :
    -1.386768 * 0.584103 ≤ mu * nu ∧ mu * nu ≤ -1.386767 * 0.584102 ∧
    (-1.386768 + 0.584102) * 2.53307 ≤ (mu + nu) * cc ∧
      (mu + nu) * cc ≤ (-1.386767 + 0.584103) * 2.53305 ∧
    -1.386768 * 0.584103 * 2.53307 ≤ mu * nu * cc ∧ mu * nu * cc ≤ -1.386767 * 0.584102 * 2.53305 ∧
    0.584102 * 2.53305 ≤ nu * cc ∧ nu * cc ≤ 0.584103 * 2.53307 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  obtain ⟨hm1, hm2, -⟩ := mu_spec
  obtain ⟨hn1, hn2, -⟩ := nu_spec
  obtain ⟨t1, t2⟩ := neg_pos_mul hm1 hm2 (by norm_num) hn1 hn2 (by norm_num)
  have hs1 : -1.386768 + 0.584102 ≤ mu + nu := by linarith
  have hs2 : mu + nu ≤ -1.386767 + 0.584103 := by linarith
  obtain ⟨sc1, sc2⟩ := neg_pos_mul hs1 hs2 (by norm_num) hc1 hc2 (by norm_num)
  obtain ⟨tc1, tc2⟩ := neg_pos_mul t1 t2 (by norm_num) hc1 hc2 (by norm_num)
  obtain ⟨nc1, nc2⟩ := pos_pos_mul hn1 hn2 (by norm_num) hc1 hc2 (by norm_num)
  exact ⟨t1, t2, sc1, sc2, tc1, tc2, nc1, nc2⟩

lemma start_B : |v 1 0| ≤ 0.6612 ∧ E 1 0 ≤ 0.2459 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  obtain ⟨hm1, hm2, -⟩ := mu_spec
  obtain ⟨hn1, hn2, -⟩ := nu_spec
  obtain ⟨u0, u1, u2, u3, -, -, -, -⟩ := u_vals
  obtain ⟨t1, t2, sc1, sc2, tc1, tc2, nc1, nc2⟩ := start_prods
  have ev0 : v 1 0 = 6 - 2 * cc - 3 * nu + nu * cc := by
    show u 1 1 - nu * u 1 0 = _
    rw [u1, u0]; ring
  have ew0 : w 1 0 = 10 - 4 * cc - 6 * (mu + nu) + 2 * ((mu + nu) * cc) + 3 * (mu * nu) -
      mu * nu * cc := by
    show u 1 2 - nu * u 1 1 - mu * (u 1 1 - nu * u 1 0) = _
    rw [u2, u1, u0]; ring
  have ew1 : w 1 1 = 19 - 7 * cc - 10 * (mu + nu) + 4 * ((mu + nu) * cc) + 6 * (mu * nu) -
      2 * (mu * nu * cc) := by
    show u 1 3 - nu * u 1 2 - mu * (u 1 2 - nu * u 1 1) = _
    rw [u3, u2, u1]; ring
  have hv0 : |v 1 0| ≤ 0.6612 := by rw [ev0, abs_le]; constructor <;> linarith
  have hw0 : |w 1 0| ≤ 0.2393 := by rw [ew0, abs_le]; constructor <;> linarith
  have hw1 : |w 1 1| ≤ 0.4062 := by rw [ew1, abs_le]; constructor <;> linarith
  refine ⟨hv0, ?_⟩
  have h := E_zero_le 1 0.2393 0.4062 hw0 hw1
  norm_num at h
  linarith

lemma start_C : |v 2 0| ≤ 1.0771 ∧ E 2 0 ≤ 0.9403 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  obtain ⟨hm1, hm2, -⟩ := mu_spec
  obtain ⟨hn1, hn2, -⟩ := nu_spec
  obtain ⟨-, -, -, -, u0, u1, u2, u3⟩ := u_vals
  obtain ⟨t1, t2, sc1, sc2, tc1, tc2, nc1, nc2⟩ := start_prods
  have ev0 : v 2 0 = 7 - 2 * cc - 4 * nu + nu * cc := by
    show u 2 1 - nu * u 2 0 = _
    rw [u1, u0]; ring
  have ew0 : w 2 0 = 12 - 5 * cc - 7 * (mu + nu) + 2 * ((mu + nu) * cc) + 4 * (mu * nu) -
      mu * nu * cc := by
    show u 2 2 - nu * u 2 1 - mu * (u 2 1 - nu * u 2 0) = _
    rw [u2, u1, u0]; ring
  have ew1 : w 2 1 = 24 - 9 * cc - 12 * (mu + nu) + 5 * ((mu + nu) * cc) + 7 * (mu * nu) -
      2 * (mu * nu * cc) := by
    show u 2 3 - nu * u 2 2 - mu * (u 2 2 - nu * u 2 1) = _
    rw [u3, u2, u1]; ring
  have hv0 : |v 2 0| ≤ 1.0771 := by rw [ev0, abs_le]; constructor <;> linarith
  have hw0 : |w 2 0| ≤ 0.3014 := by rw [ew0, abs_le]; constructor <;> linarith
  have hw1 : |w 2 1| ≤ 0.8983 := by rw [ew1, abs_le]; constructor <;> linarith
  refine ⟨hv0, ?_⟩
  have h := E_zero_le 2 0.3014 0.8983 hw0 hw1
  norm_num at h
  linarith

lemma uB_bound (j : ℕ) : |u 1 j| ≤ 3.18 * 1.39 ^ j := by
  obtain ⟨hv0, hE0⟩ := start_B
  have hw : ∀ j, |w 1 j| ≤ 0.4291 * 1.16 ^ j := fun j =>
    w_bound 1 j (by norm_num) 0.2459 0.4291 hE0 (by norm_num) (by norm_num)
  have hv : ∀ j, |v 1 j| ≤ 2.556 * 1.39 ^ j - 1.894 * 1.16 ^ j := fun j =>
    v_bound 1 j 0.4291 1.894 2.556 hw (by linarith) (by norm_num) (by norm_num)
  have h0 : |u 1 0| ≤ 3.18 := by
    obtain ⟨hc1, hc2⟩ := cc_bounds
    rw [u_vals.1, abs_le]
    constructor <;> linarith
  exact u_bound 1 j 1.894 2.556 3.18 hv (by norm_num) h0 (by norm_num)

lemma uC_bound (j : ℕ) : |u 2 j| ≤ 5.94 * 1.39 ^ j := by
  obtain ⟨hv0, hE0⟩ := start_C
  have hw : ∀ j, |w 2 j| ≤ 0.839 * 1.16 ^ j := fun j =>
    w_bound 2 j (by norm_num) 0.9403 0.839 hE0 (by norm_num) (by norm_num)
  have hv : ∀ j, |v 2 j| ≤ 4.779 * 1.39 ^ j - 3.701 * 1.16 ^ j := fun j =>
    v_bound 2 j 0.839 3.701 4.779 hw (by linarith) (by norm_num) (by norm_num)
  have h0 : |u 2 0| ≤ 5.94 := by
    obtain ⟨hc1, hc2⟩ := cc_bounds
    rw [u_vals.2.2.2.2.1, abs_le]
    constructor <;> linarith
  exact u_bound 2 j 3.701 4.779 5.94 hv (by norm_num) h0 (by norm_num)

lemma uA_bound (j : ℕ) : 2 * |u 0 j| ≤ 5.94 * 1.39 ^ j := by
  rcases j with _ | j
  · have e : u 0 0 = 2 := by
      have h0 : (flat [0]).count 0 = 2 := by decide
      have h1 : (flat [0]).count 1 = 0 := by decide
      show gL (flat [0]) = 2
      unfold gL
      rw [h0, h1]
      push_cast
      ring
    rw [e]
    norm_num
  · have e : u 0 (j + 1) = u 1 j := by
      unfold u
      rw [Function.iterate_succ_apply, tau_single]
      rfl
    rw [e, pow_succ]
    have h := uB_bound j
    have hp : 0 ≤ (1.39 : ℝ) ^ j := by positivity
    nlinarith

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

lemma gtok_bound (x : ℕ) (hx : x ≤ 4) : |g [x]| ≤ 2.1 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have k : ∀ (z o : ℕ), (flat [x]).count 0 = z → (flat [x]).count 1 = o → g [x] = z - cc * o := by
    intro z o hz ho
    unfold g gL
    rw [hz, ho]
  interval_cases x
  · rw [k 2 0 (by decide) (by decide), abs_le]; constructor <;> norm_num
  · rw [k 3 1 (by decide) (by decide), abs_le]; constructor <;> norm_num <;> linarith
  · rw [k 4 1 (by decide) (by decide), abs_le]; constructor <;> norm_num <;> linarith
  · rw [k 3 2 (by decide) (by decide), abs_le]; constructor <;> norm_num <;> linarith
  · rw [k 4 2 (by decide) (by decide), abs_le]; constructor <;> norm_num <;> linarith

/-- |g| over the prefixes of tau^J(x). -/
lemma prefix_bound (J : ℕ) : ∀ x, x ≤ 4 → ∀ i, |g ((tau^[J] [x]).take i)| ≤ 15.3 * 1.39 ^ J - 13.2 := by
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
    have hp : 0 ≤ (1.39 : ℝ) ^ J := by positivity
    have hP : 0 ≤ 15.3 * (1.39 : ℝ) ^ J - 13.2 := by
      have : (1 : ℝ) ≤ 1.39 ^ J := one_le_pow₀ (by norm_num)
      linarith
    have hA := uA_bound J
    have hB := uB_bound J
    have hC := uC_bound J
    rw [Function.iterate_succ_apply, tau_single, pow_succ]
    interval_cases x
    · exact le_trans (ih 1 (by norm_num) i) (by nlinarith)
    · rw [show tauT 1 = [0] ++ [4] from rfl, tauIter_append]
      have h := take_append_le _ _ _ _ (ih 0 (by norm_num)) (ih 4 (by norm_num)) i
      refine le_trans h (max_le (by nlinarith) ?_)
      show |u 0 J| + (15.3 * 1.39 ^ J - 13.2) ≤ 15.3 * (1.39 ^ J * 1.39) - 13.2
      nlinarith
    · rw [show tauT 2 = [0] ++ ([0] ++ [3]) from rfl, tauIter_append, tauIter_append]
      have h1 := take_append_le _ _ _ _ (ih 0 (by norm_num)) (ih 3 (by norm_num))
      have h2 := take_append_le _ _ _ _ (ih 0 (by norm_num)) h1 i
      refine le_trans h2 (max_le (by nlinarith) ?_)
      have hm : max (15.3 * 1.39 ^ J - 13.2) (|g (tau^[J] [0])| + (15.3 * 1.39 ^ J - 13.2)) ≤
          |g (tau^[J] [0])| + (15.3 * 1.39 ^ J - 13.2) :=
        max_le (by linarith [abs_nonneg (g (tau^[J] [0]))]) le_rfl
      show |u 0 J| + max (15.3 * 1.39 ^ J - 13.2) (|u 0 J| + (15.3 * 1.39 ^ J - 13.2)) ≤
        15.3 * (1.39 ^ J * 1.39) - 13.2
      have hm' : max (15.3 * 1.39 ^ J - 13.2) (|u 0 J| + (15.3 * 1.39 ^ J - 13.2)) ≤
          |u 0 J| + (15.3 * 1.39 ^ J - 13.2) := hm
      nlinarith
    · rw [show tauT 3 = [1] ++ [3] from rfl, tauIter_append]
      have h := take_append_le _ _ _ _ (ih 1 (by norm_num)) (ih 3 (by norm_num)) i
      refine le_trans h (max_le (by nlinarith) ?_)
      show |u 1 J| + (15.3 * 1.39 ^ J - 13.2) ≤ 15.3 * (1.39 ^ J * 1.39) - 13.2
      nlinarith
    · rw [show tauT 4 = [2] ++ [3] from rfl, tauIter_append]
      have h := take_append_le _ _ _ _ (ih 2 (by norm_num)) (ih 3 (by norm_num)) i
      refine le_trans h (max_le (by nlinarith) ?_)
      show |u 2 J| + (15.3 * 1.39 ^ J - 13.2) ≤ 15.3 * (1.39 ^ J * 1.39) - 13.2
      nlinarith

/-! ### Letters -/

lemma gL_tok_take (k : ℕ) (hk : k ≤ 4) (r : ℕ) : |gL ((tok k).take r)| ≤ 5.07 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hz : ((tok k).take r).count 0 ≤ 4 := by
    calc ((tok k).take r).count 0 ≤ (tok k).count 0 := List.Sublist.count_le _ (List.take_sublist _ _)
      _ ≤ 4 := by interval_cases k <;> decide
  have ho : ((tok k).take r).count 1 ≤ 2 := by
    calc ((tok k).take r).count 1 ≤ (tok k).count 1 := List.Sublist.count_le _ (List.take_sublist _ _)
      _ ≤ 2 := by interval_cases k <;> decide
  have hz' : (((tok k).take r).count 0 : ℝ) ≤ 4 := by exact_mod_cast hz
  have ho' : (((tok k).take r).count 1 : ℝ) ≤ 2 := by exact_mod_cast ho
  have hz0 : (0 : ℝ) ≤ ((tok k).take r).count 0 := Nat.cast_nonneg _
  have ho0 : (0 : ℝ) ≤ ((tok k).take r).count 1 := Nat.cast_nonneg _
  unfold gL
  rw [abs_le]
  constructor <;> nlinarith

lemma flat_split : ∀ S : List ℕ, Valid S → ∀ t,
    ∃ i, |gL ((flat S).take t) - g (S.take i)| ≤ 5.07 := by
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

/-! ### The length of the iterates -/

/-- The Perron weight of a token. -/
noncomputable def wt (k : ℕ) : ℝ :=
  if k = 0 then 1 else if k = 1 then lam
  else if k = 2 then 1 - lam / 2 + lam ^ 2 / 2 + lam ^ 3 - lam ^ 4 / 2
  else if k = 3 then -1 - lam / 2 - lam ^ 2 / 2 + lam ^ 4 / 2 else lam ^ 2 - 1

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
      first | ring1 | linear_combination (-1 / 2 : ℝ) * hf | linear_combination (1 / 2 : ℝ) * hf

lemma Phi_iter (J : ℕ) : Phi (tau^[J] [0]) = lam ^ J := by
  induction J with
  | zero => simp [Phi, wt]
  | succ J ih =>
    rw [Function.iterate_succ_apply', Phi_tau _ (tauIter_valid J _ (valid_single (by norm_num))),
      ih, pow_succ]
    ring

lemma length_ge_Phi (s : List ℕ) (hs : Valid s) : 2 * Phi s ≤ ((flat s).length : ℝ) := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := lam_pows
  induction s with
  | nil => simp [Phi, flat]
  | cons k s ih =>
    obtain ⟨hk, hs'⟩ := valid_cons hs
    rw [flat_cons, List.length_append, show k :: s = [k] ++ s from rfl, Phi_append]
    push_cast
    have := ih hs'
    have hk' : 2 * Phi [k] ≤ ((tok k).length : ℝ) := by
      interval_cases k <;> simp [Phi, wt, tok] <;> linarith
    linarith

lemma iter_length_ge (J : ℕ) : 2 * lam ^ J ≤ ((iter J).length : ℝ) := by
  have h := length_ge_Phi _ (tauIter_valid J _ (valid_single (show 0 ≤ 4 by norm_num)))
  rw [Phi_iter] at h
  rw [iter_eq]
  exact h

/-! ### Counting along the limiting word -/

lemma W_le (i : ℕ) : W i ≤ 1 := by
  have hi : i < (V (i + 1)).length := by have := V_length (i + 1); omega
  rw [W_eq (i + 1) i hi, List.getD_eq_getElem _ _ hi]
  exact iter_letters _ _ (List.getElem_mem hi)

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

lemma pow_bound (J : ℕ) (hJ : 8 ≤ J) : 18.3 * 1.39 ^ J < 2 * lam ^ J := by
  obtain ⟨hl1, hl2, -⟩ := lam_spec
  induction J, hJ using Nat.le_induction with
  | base =>
    have : (1.846225 : ℝ) ^ 8 ≤ lam ^ 8 := pow_le_pow_left₀ (by norm_num) hl1 8
    norm_num at this ⊢
    linarith
  | succ J hJ ih =>
    rw [pow_succ lam J, pow_succ (1.39 : ℝ) J]
    have hp : 0 ≤ lam ^ J := by positivity
    have h := mul_le_mul_of_nonneg_left (show (1.39 : ℝ) ≤ lam by linarith) hp
    nlinarith

lemma V4_length : (V 4).length = 304 := by decide +kernel

/-- For N > 304 there is a level J >= 8 with 2 lam^J < N and |D(N)| <= 18.3 * 1.39^J. -/
lemma level (N : ℕ) (hN : 304 < N) :
    ∃ J, 8 ≤ J ∧ 2 * lam ^ J < (N : ℝ) ∧ |D N| ≤ 18.3 * 1.39 ^ J := by
  have hex : ∃ k, N ≤ (V k).length := ⟨N, by have := V_length N; omega⟩
  classical
  have hk : N ≤ (V (Nat.find hex)).length := Nat.find_spec hex
  have h4 := V4_length
  have hk5 : 5 ≤ Nat.find hex := by
    by_contra h
    have := (V_prefix (show Nat.find hex ≤ 4 by omega)).length_le
    omega
  have hmin : (V (Nat.find hex - 1)).length < N := by
    have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    omega
  have h2 : 2 * Nat.find hex + res = 2 * (Nat.find hex - 1) + res + 2 := by omega
  have e : V (Nat.find hex) = iter (2 * (Nat.find hex - 1) + res) ++
      flat (tau^[2 * (Nat.find hex - 1) + res] [4]) := by
    rw [← iter_two, ← h2]
    rfl
  have e' : V (Nat.find hex - 1) = iter (2 * (Nat.find hex - 1) + res) := rfl
  set J := 2 * (Nat.find hex - 1) + res with hJ
  refine ⟨J, by omega, ?_, ?_⟩
  · have hl := iter_length_ge J
    rw [e'] at hmin
    have : ((iter J).length : ℝ) < N := by exact_mod_cast hmin
    linarith
  · rw [D_eq (Nat.find hex) N hk, e]
    rw [e'] at hmin
    rw [List.take_append, List.take_of_length_le hmin.le, gL_append]
    obtain ⟨i, hi⟩ := flat_split (tau^[J] [4]) (tauIter_valid J _ (valid_single (by norm_num)))
      (N - (iter J).length)
    have hpre := prefix_bound J 4 (by norm_num) i
    have hA := uA_bound J
    have hu : gL (iter J) = u 0 J := by rw [iter_eq]; rfl
    rw [hu]
    have h1 := abs_add_le (u 0 J) (gL ((flat (tau^[J] [4])).take (N - (iter J).length)))
    have h3 := abs_sub_abs_le_abs_sub (gL ((flat (tau^[J] [4])).take (N - (iter J).length)))
      (g ((tau^[J] [4]).take i))
    have hp : (1 : ℝ) ≤ 1.39 ^ J := one_le_pow₀ (by norm_num)
    linarith

/-- Over every prefix of W longer than 304 letters, |D| < N. -/
lemma D_small (N : ℕ) (hN : 304 < N) : |D N| < (N : ℝ) := by
  obtain ⟨J, hJ, hNr, hD⟩ := level N hN
  have hp := pow_bound J hJ
  linarith

/-- D(N)^4 <= 500000 N^3 for every N. -/
lemma D_pow4 (N : ℕ) : D N ^ 4 ≤ 500000 * (N : ℝ) ^ 3 := by
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have e4 : D N ^ 4 = (|D N| ^ 2) ^ 2 := by rw [sq_abs]; ring
  rcases le_or_gt N 304 with h | h
  · have h1 := D_triv N
    have hN1 : (N : ℝ) ≤ 304 := by exact_mod_cast h
    have h2 : |D N| ^ 2 ≤ (cc * N) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    have h3 : (|D N| ^ 2) ^ 2 ≤ ((cc * N) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (sq_nonneg _) h2 2
    have h4 : ((cc * N) ^ 2) ^ 2 = cc ^ 4 * N * N ^ 3 := by ring
    have h5 : cc ^ 4 ≤ 42 := by
      have := pow_le_pow_left₀ (by linarith) hc2 4
      norm_num at this
      linarith
    have h6 : cc ^ 4 * (N : ℝ) * N ^ 3 ≤ 42 * 304 * N ^ 3 := by
      have hc4 : 0 ≤ cc ^ 4 := by positivity
      have hN3 : (0 : ℝ) ≤ N ^ 3 := by positivity
      have := mul_le_mul h5 hN1 hN0 (by norm_num)
      nlinarith
    rw [e4]
    nlinarith
  · obtain ⟨J, hJ, hNr, hD⟩ := level N h
    obtain ⟨hl1, hl2, -⟩ := lam_spec
    obtain ⟨-, -, p3, -, -, -⟩ := lam_pows
    have h2 : |D N| ^ 2 ≤ (18.3 * 1.39 ^ J) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hD 2
    have h3 : (|D N| ^ 2) ^ 2 ≤ ((18.3 * 1.39 ^ J) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (sq_nonneg _) h2 2
    have h4 : ((18.3 * (1.39 : ℝ) ^ J) ^ 2) ^ 2 = 18.3 ^ 4 * (1.39 ^ 4) ^ J := by
      rw [← pow_mul, mul_pow, ← pow_mul, ← pow_mul, mul_comm J (2 * 2)]
    have h5 : ((1.39 : ℝ) ^ 4) ^ J ≤ (lam ^ J) ^ 3 := by
      rw [← pow_mul lam J 3, mul_comm J 3, pow_mul lam 3 J]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num; linarith) J
    have h6 : (2 * lam ^ J) ^ 3 ≤ (N : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hNr.le 3
    have h7 : (0 : ℝ) ≤ (lam ^ J) ^ 3 := by positivity
    rw [e4]
    nlinarith

/-! ### The positions of 0 -/

/-- The limit, (1 + c)/c = 1.39477... -/
noncomputable def m0 : ℝ := (1 + cc) / cc

lemma m0_bounds : 1.3947 ≤ m0 ∧ m0 ≤ 1.3948 := by
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
  have h := D_small (B + 1 + (4 * Z (B + 1) + 400)) (by omega)
  have hs := O_add_Z (B + 1 + (4 * Z (B + 1) + 400))
  rw [hconst] at hs
  unfold D at h
  rw [hconst, abs_lt] at h
  obtain ⟨h1, -⟩ := h
  have hO : (O (B + 1 + (4 * Z (B + 1) + 400)) : ℝ) =
      ((B + 1 + (4 * Z (B + 1) + 400) : ℕ) : ℝ) - Z (B + 1) := by
    have : (O (B + 1 + (4 * Z (B + 1) + 400)) : ℝ) + Z (B + 1) =
        ((B + 1 + (4 * Z (B + 1) + 400) : ℕ) : ℝ) := by exact_mod_cast hs
    linarith
  rw [hO] at h1
  generalize hz : (Z (B + 1) : ℝ) = z at h1
  have hz0 : 0 ≤ z := by rw [← hz]; exact Nat.cast_nonneg _
  have hz' : ((B + 1 + (4 * Z (B + 1) + 400) : ℕ) : ℝ) = (B : ℝ) + 1 + (4 * z + 400) := by
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

/-- A linear scan of a word, checking 100 (t + 1) < 239 Z(t + 1) at each letter 0. -/
def chk : List ℕ → ℕ → ℕ → Bool
  | [], _, _ => true
  | x :: l, t, z =>
    if x = 0 then decide (100 * (t + 1) < 239 * (z + 1)) && chk l (t + 1) (z + 1)
    else chk l (t + 1) z

lemma chk_spec : ∀ (L : List ℕ) (t z : ℕ), chk L t z = true →
    ∀ i < L.length, L.getD i 0 = 0 →
      100 * (t + i + 1) < 239 * (z + (L.take (i + 1)).count 0) := by
  intro L
  induction L with
  | nil =>
    intro t z _ i hi
    simp at hi
  | cons x l ih =>
    intro t z h i hi hx
    by_cases h0 : x = 0
    · subst h0
      have h' : 100 * (t + 1) < 239 * (z + 1) ∧ chk l (t + 1) (z + 1) = true := by
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

lemma chk_word : chk (V 4) 0 0 = true := by decide +kernel

lemma bound_small (n : ℕ) (hn : 1 ≤ n) (ha : a n ≤ 304) :
    -1 < m0 - (a n : ℝ) / n ∧ m0 - (a n : ℝ) / n < 1 := by
  obtain ⟨hm1, hm2⟩ := m0_bounds
  obtain ⟨hZ, hO⟩ := a_spec n hn
  have hinf := zeros_infinite
  have hWp : W (Nat.nth (fun i => W i = 0) (n - 1)) = 0 := Nat.nth_mem_of_infinite hinf (n - 1)
  have ha' : a n = Nat.nth (fun i => W i = 0) (n - 1) + 1 := rfl
  set t := Nat.nth (fun i => W i = 0) (n - 1) with ht
  have hlen := V4_length
  have hW : (V 4).getD t 0 = 0 := by rw [← W_eq 4 t (by omega)]; exact hWp
  have hc := chk_spec (V 4) 0 0 chk_word t (by omega) hW
  have hZ' : ((V 4).take (t + 1)).count 0 = n := by
    rw [← (counts_eq 4 (t + 1) (by omega)).1, ← ha', hZ]
  rw [hZ'] at hc
  simp only [zero_add] at hc
  have hle : n ≤ a n := by have := O_add_Z (a n); omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hc' : (100 : ℝ) * (a n) < 239 * n := by
    rw [ha']
    exact_mod_cast hc
  have hle' : (n : ℝ) ≤ a n := by exact_mod_cast hle
  have h1 : (a n : ℝ) / n < 2.39 := by
    rw [div_lt_iff₀ hnpos]
    linarith
  have h2 : 1 ≤ (a n : ℝ) / n := by
    rw [le_div_iff₀ hnpos]
    linarith
  constructor <;> linarith

lemma bound_large (n : ℕ) (hn : 1 ≤ n) (ha : 304 < a n) :
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
  have hP : 2.53305 * (a n : ℝ) ≤ cc * a n := mul_le_mul_of_nonneg_right hc1 hA0
  have hQ1 : 2.53305 * (n : ℝ) ≤ cc * n := mul_le_mul_of_nonneg_right hc1 hnpos.le
  have hQ2 : cc * (n : ℝ) ≤ 2.53307 * n := mul_le_mul_of_nonneg_right hc2 hnpos.le
  have hE : cc * ((a n : ℝ) - n) = cc * a n - cc * n := by ring
  rw [hE] at hD1 hD2 ⊢
  constructor
  · rw [lt_div_iff₀ hnpos, lt_div_iff₀ hc]
    linarith
  · rw [div_lt_iff₀ hnpos, div_lt_iff₀ hc]
    linarith

/-- Kimberling's conjecture: a(n)/n tends to a number m = 1.39..., and -1 < m - a(n)/n < 1
for n >= 1. -/
theorem conjecture : ∃ m : ℝ, (1.39 ≤ m ∧ m < 1.40) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 m) ∧
    ∀ n : ℕ, 1 ≤ n → -1 < m - (a n : ℝ) / n ∧ m - (a n : ℝ) / n < 1 := by
  obtain ⟨hm1, hm2⟩ := m0_bounds
  obtain ⟨hc1, hc2⟩ := cc_bounds
  have hc : 0 < cc := by linarith
  have hbound : ∀ n : ℕ, 1 ≤ n → -1 < m0 - (a n : ℝ) / n ∧ m0 - (a n : ℝ) / n < 1 := by
    intro n hn
    rcases le_or_gt (a n) 304 with h | h
    · exact bound_small n hn h
    · exact bound_large n hn h
  refine ⟨m0, ⟨by linarith, by linarith⟩, ?_, hbound⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => Real.sqrt (Real.sqrt (13500000 / n))) atTop (𝓝 0) := by
    have := ((tendsto_const_div_atTop_nhds_zero_nat (13500000 : ℝ)).sqrt).sqrt
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hb := hbound n hn
  have ha3 : (a n : ℝ) ≤ 3 * n := by
    have h1 : (a n : ℝ) / n < 2.395 := by linarith [hb.1]
    rw [div_lt_iff₀ hnpos] at h1
    linarith
  have hA0 : (0 : ℝ) ≤ a n := Nat.cast_nonneg _
  have hsq := D_pow4 (a n)
  have hdev := a_dev n hn
  rw [Real.norm_eq_abs]
  apply Real.abs_le_sqrt
  have h4 : (((a n : ℝ) / n - m0) ^ 2) ^ 2 ≤ 13500000 / n := by
    have e : (a n : ℝ) / n - m0 = -(D (a n) / cc) / n := by
      rw [← hdev]
      field_simp
      ring
    have key : (((a n : ℝ) / n - m0) ^ 2) ^ 2 = D (a n) ^ 4 / (cc ^ 4 * n ^ 4) := by
      rw [e]
      field_simp
    rw [key, div_le_div_iff₀ (by positivity) hnpos]
    have hc4 : 1 ≤ cc ^ 4 := one_le_pow₀ (by linarith)
    have hA3 : (a n : ℝ) ^ 3 ≤ (3 * n) ^ 3 := pow_le_pow_left₀ hA0 ha3 3
    have hn4 : (0 : ℝ) ≤ (n : ℝ) ^ 4 := by positivity
    have h5 : D (a n) ^ 4 ≤ 500000 * (3 * n) ^ 3 := by nlinarith
    have h6 : 13500000 * (n : ℝ) ^ 4 ≤ 13500000 * (cc ^ 4 * n ^ 4) := by nlinarith
    nlinarith
  have h2 : |((a n : ℝ) / n - m0) ^ 2| ≤ Real.sqrt (13500000 / n) := Real.abs_le_sqrt h4
  rwa [abs_of_nonneg (sq_nonneg _)] at h2

end OMA.S_oeis_a287103

theorem OMA.solution : type_of% @OMA.S_oeis_a287103.main :=
  OMA.S_oeis_a287103.conjecture

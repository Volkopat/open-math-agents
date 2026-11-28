import OMAStatements.S_oeis_a400685

-- Proof credit: @pmaster (Codex); independently audited and assembled by @CubeJerry.
-- uses note #109148
-- Original proof: https://github.com/pmaster/open-math-agents/blob/c6374ce3881a0f98c73afa724aa3fbdbe180b8ed/proofs/oeis-a400685.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Proof of Felix Huber's conjecture on the exponential growth rate of
equal-area, equal-perimeter square cuts. Proof by @pmaster with Codex.
The key operation sandwiches an arbitrary middle cut between two independent
cuts of the same size and offset, preserving signed area and both endpoints.
-/


namespace OMA.S_oeis_a400685

lemma finish_nil (p : Point) : finish p [] = p := rfl
lemma finish_cons (p : Point) (d : Dir) (w : List Dir) :
    finish p (d::w) = finish (p+delta d) w := rfl

lemma finish_append (p : Point) (u v : List Dir) :
    finish p (u++v) = finish (finish p u) v := by
  simp [finish]

lemma after_append (p : Point) (u v : List Dir) :
    after p (u++v) = after p u ++ after (finish p u) v := by
  induction u generalizing p with
  | nil => rfl
  | cons d w ih => simp [after, finish_cons, ih]

lemma finish_translate (p t : Point) (w : List Dir) :
    finish (t+p) w = t+finish p w := by
  induction w generalizing p with
  | nil => rfl
  | cons d w ih => simp only [finish_cons, add_assoc, ih]

lemma after_translate (p t : Point) (w : List Dir) :
    after (t+p) w = (after p w).map (t+·) := by
  induction w generalizing p with
  | nil => rfl
  | cons d w ih => simp [after, add_assoc, ih]

lemma trail_translate (p t : Point) (w : List Dir) :
    trail (t+p) w = (trail p w).map (t+·) := by
  simp [trail, after_translate]

lemma integral_append (p : Point) (u v : List Dir) :
    integral p (u++v) = integral p u + integral (finish p u) v := by
  induction u generalizing p with
  | nil => simp [finish_nil, integral]
  | cons d w ih => simp [integral, finish_cons, ih, add_assoc]

lemma integral_translate (p t : Point) (w : List Dir) :
    integral (t+p) w = integral p w + t.1 * ((finish p w).2-p.2) := by
  induction w generalizing p with
  | nil => simp [integral, finish_nil]
  | cons d w ih =>
    simp only [integral, add_assoc, ih, finish_cons, Prod.fst_add, Prod.snd_add]
    ring

end OMA.S_oeis_a400685

namespace OMA.S_oeis_a400685

private structure Strip (N : ℕ) (p e : Point) (w : List Dir) : Prop where
  finish_eq : finish p w = e
  rise : p.2 < e.2
  nodup : (trail p w).Nodup
  horiz : ∀ z ∈ trail p w, 0 < z.1 ∧ z.1 < 2*(N : ℤ)
  lo : ∀ z ∈ after p w, p.2 < z.2
  hi : ∀ z ∈ trail p w, z = e ∨ z.2 < e.2

private lemma Strip.join {N : ℕ} {p j e : Point} {u v : List Dir}
    (hu : Strip N p j u) (hv : Strip N j e v) : Strip N p e (u ++ v) := by
  have ht : trail p (u ++ v) = trail p u ++ after j v := by
    simp [trail, after_append, hu.finish_eq]
  have memR {z : Point} (hz : z ∈ after j v) : z ∈ trail j v := List.mem_cons_of_mem _ hz
  refine ⟨by rw [finish_append, hu.finish_eq, hv.finish_eq], hu.rise.trans hv.rise, ?_, ?_, ?_, ?_⟩
  · rw [ht]
    apply hu.nodup.append (List.nodup_cons.mp hv.nodup).2
    intro z hz hz'
    rcases hu.hi z hz with rfl | h
    · exact (hv.lo z hz').false
    · exact (hv.lo z hz').asymm h
  · intro z hz
    rw [ht] at hz
    rcases List.mem_append.mp hz with h | h
    · exact hu.horiz z h
    · exact hv.horiz z (memR h)
  · intro z hz
    rw [after_append, hu.finish_eq] at hz
    rcases List.mem_append.mp hz with h | h
    · exact hu.lo z h
    · exact hu.rise.trans (hv.lo z h)
  · intro z hz
    rw [ht] at hz
    rcases List.mem_append.mp hz with h | h
    · right
      rcases hu.hi z h with rfl | hh
      · exact hv.rise
      · exact hh.trans hv.rise
    · exact hv.hi z (memR h)

private lemma strip_of_cut {n q N : ℕ} {w : List Dir} (h : IsCut n q w)
    (t : Point) (hx : 0 ≤ t.1) (hx' : t.1 + 2*(n:ℤ) ≤ 2*(N:ℤ)) :
    Strip N (t + startPt q) (t + endPt n q) w := by
  rcases h with ⟨hq, hq', _, he, hn, hi, _⟩
  have hnj : startPt q ∉ after (startPt q) w := (List.nodup_cons.mp hn).1
  refine ⟨by rw [finish_translate, he], ?_, ?_, ?_, ?_, ?_⟩
  · change t.2 + 0 < t.2 + 2*(n:ℤ)
    omega
  · rw [trail_translate]
    exact hn.map (add_right_injective t)
  · intro z hz
    rw [trail_translate] at hz
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
    change 0 < t.1 + a.1 ∧ t.1 + a.1 < 2*(N:ℤ)
    rcases hi a ha with rfl | rfl | hi'
    · simp only [startPt]
      omega
    · simp only [endPt]
      omega
    · rcases hi' with ⟨h₁, h₂, _⟩
      omega
  · intro z hz
    rw [after_translate] at hz
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
    change t.2 + 0 < t.2 + a.2
    rcases hi a (List.mem_cons_of_mem _ ha) with rfl | rfl | hi'
    · exact False.elim (hnj ha)
    · simp only [endPt]
      omega
    · have hy := hi'.2.2.1
      omega
  · intro z hz
    rw [trail_translate] at hz
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
    rcases hi a ha with rfl | rfl | hi'
    · right
      change t.2 + 0 < t.2 + 2*(n:ℤ)
      omega
    · exact Or.inl rfl
    · right
      change t.2 + a.2 < t.2 + 2*(n:ℤ)
      have hy := hi'.2.2.2
      omega

lemma sandwich_cut {n r q p : ℕ} {u v w : List Dir}
    (hu : IsCut n q u) (hv : IsCut r p v) (hw : IsCut n q w) :
    IsCut (2*n+r) (2*q+p) ((u ++ v) ++ w) := by
  let L : Point := ((q:ℤ)+p, 0)
  let M : Point := (2*(n:ℤ), 2*(n:ℤ))
  let R : Point := (2*(n:ℤ)+2*(r:ℤ)-q-p, 2*(n:ℤ)+2*(r:ℤ))
  have q0 := hu.1
  have qn := hu.2.1
  have p0 := hv.1
  have pr := hv.2.1
  have e0 : L + startPt q = startPt (2*q+p) := by
    ext <;> simp [L, startPt]
    ring
  have e1 : L + endPt n q = M + startPt p := by
    ext <;> simp [L, M, endPt, startPt]
    ring
  have e2 : M + endPt r p = R + startPt q := by
    ext <;> simp [M, R, endPt, startPt]
    ring
  have e3 : R + endPt n q = endPt (2*n+r) (2*q+p) := by
    ext <;> simp [R, endPt] <;> ring
  have SL := strip_of_cut (N := 2*n+r) hu L (by dsimp [L]; omega) (by dsimp [L]; omega)
  have SM := strip_of_cut (N := 2*n+r) hv M (by dsimp [M]; omega) (by dsimp [M]; omega)
  have SR := strip_of_cut (N := 2*n+r) hw R (by dsimp [R]; omega) (by dsimp [R]; omega)
  rw [e1] at SL
  rw [e2] at SM
  have S := (SL.join SM).join SR
  rw [e0, e3] at S
  refine ⟨by omega, by omega, ?_, S.finish_eq, S.nodup, ?_, ?_⟩
  · simp only [List.length_append, hu.2.2.1, hv.2.2.1, hw.2.2.1]
    omega
  · intro z hz
    rcases List.mem_cons.mp hz with h | h
    · exact Or.inl h
    rcases S.hi z hz with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr ⟨(S.horiz z hz).1, (S.horiz z hz).2, S.lo z h, h'⟩)
  · rw [← e0, integral_append, finish_append, SL.finish_eq, SM.finish_eq,
      integral_append, SL.finish_eq, integral_translate, integral_translate, integral_translate,
      hu.2.2.2.1, hv.2.2.2.1, hw.2.2.2.1,
      hu.2.2.2.2.2.2, hv.2.2.2.2.2.2, hw.2.2.2.2.2.2]
    simp [L, M, R, startPt, endPt]
    ring

end OMA.S_oeis_a400685

namespace OMA.S_oeis_a400685

noncomputable def atOffset (n q : ℕ) : Finset (Code n) :=
  (cuts n).filter (fun c => c.1.val = q)

noncomputable def b (n : ℕ) : ℕ :=
  (Finset.range (2*n+1)).sup (fun q => (atOffset n q).card)

lemma offset_mem {n q : ℕ} {c : Code n} :
    c ∈ atOffset n q ↔ c.1.val = q ∧ IsCut n q (List.ofFn c.2) := by
  classical
  simp only [atOffset, cuts, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h, e⟩
    exact ⟨e, e ▸ h⟩
  · rintro ⟨e, h⟩
    exact ⟨e.symm ▸ h, e⟩

lemma best_offset (n : ℕ) : ∃ q ∈ Finset.range (2*n+1), b n = (atOffset n q).card := by
  exact Finset.exists_mem_eq_sup _ ⟨0, Finset.mem_range.mpr (by omega)⟩ _

lemma count_le_four_a (n : ℕ) (hn : n ≠ 0) : (cuts n).card ≤ 4*a n := by
  classical
  let os := (cuts n).image orbit
  have hsub : cuts n ⊆ os.biUnion id := by
    intro c hc
    apply Finset.mem_biUnion.mpr
    exact ⟨orbit c, Finset.mem_image_of_mem _ hc, by simp [orbit]⟩
  have hcard : ∀ s ∈ os, s.card ≤ 4 := by
    intro s hs
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.card_le_four
  calc
    (cuts n).card ≤ (os.biUnion id).card := Finset.card_le_card hsub
    _ ≤ ∑ s ∈ os, s.card := Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ os, 4 := Finset.sum_le_sum hcard
    _ = 4 * a n := by simp [a, hn, os, Nat.mul_comm]

lemma b_le_four_a (n : ℕ) (hn : n ≠ 0) : b n ≤ 4*a n := by
  obtain ⟨q, _, e⟩ := best_offset n
  exact e ▸ (Finset.card_le_card (Finset.filter_subset _ _)).trans (count_le_four_a n hn)

lemma a_le_offset_bound (n : ℕ) (hn : n ≠ 0) : a n ≤ (2*n+1)*b n := by
  classical
  have hsum : (cuts n).card = ∑ q ∈ Finset.range (2*n+1), (atOffset n q).card :=
    Finset.card_eq_sum_card_fiberwise (f := fun c : Code n => c.1.val)
      fun c _ => Finset.mem_range.mpr c.1.isLt
  calc
    a n ≤ (cuts n).card := by simpa [a, hn] using (Finset.card_image_le (s := cuts n) (f := orbit))
    _ = _ := hsum
    _ ≤ ∑ _ ∈ Finset.range (2*n+1), b n :=
      Finset.sum_le_sum fun _ hq => Finset.le_sup (f := fun q => (atOffset n q).card) hq
    _ = _ := by simp

lemma a_le_walk_bound (n : ℕ) (hn : n ≠ 0) : a n ≤ (2*n+1)*4^(4*n) := by
  classical
  calc
    a n ≤ (cuts n).card := by simpa [a, hn] using (Finset.card_image_le (s := cuts n) (f := orbit))
    _ ≤ Fintype.card (Code n) := Finset.card_le_univ _
    _ = _ := by simp [Code, Dir, Fintype.card_prod]

end OMA.S_oeis_a400685

namespace OMA.S_oeis_a400685

abbrev Fiber (n q : ℕ) := ↥(atOffset n q)
def wordOf {n q : ℕ} (c : Fiber n q) : List Dir := List.ofFn c.val.2

lemma cut_word {n q : ℕ} (c : Fiber n q) : IsCut n q (wordOf c) :=
  (offset_mem.mp c.property).2

lemma word_injective {n q : ℕ} : Function.Injective (@wordOf n q) := by
  intro x y h
  apply Subtype.ext
  apply Prod.ext
  · exact Fin.ext ((offset_mem.mp x.property).1.trans (offset_mem.mp y.property).1.symm)
  · exact List.ofFn_injective h

def indexedWord (w : List Dir) {l : ℕ} (h : w.length = l) (j : Fin l) : Dir :=
  w.get (Fin.cast h.symm j)

lemma ofFn_indexedWord (w : List Dir) {l : ℕ} (h : w.length = l) :
    List.ofFn (indexedWord w h) = w := by
  subst l
  exact List.ofFn_get w

noncomputable def fromCut {n q : ℕ} {w : List Dir} (h : IsCut n q w) : Fiber n q :=
  ⟨(⟨q, Nat.lt_succ_of_lt h.2.1⟩, indexedWord w h.2.2.1), offset_mem.mpr
    ⟨rfl, by rw [ofFn_indexedWord]; exact h⟩⟩

lemma word_fromCut {n q : ℕ} {w : List Dir} (h : IsCut n q w) :
    wordOf (fromCut h) = w := ofFn_indexedWord w h.2.2.1

noncomputable def joinCodes {n r q p : ℕ} (x : Fiber n q × Fiber r p × Fiber n q) :
    Fiber (2*n+r) (2*q+p) :=
  fromCut (sandwich_cut (cut_word x.1) (cut_word x.2.1) (cut_word x.2.2))

lemma join_injective {n r q p : ℕ} : Function.Injective (@joinCodes n r q p) := by
  intro x y h
  have he := congrArg wordOf h
  change wordOf (fromCut _) = wordOf (fromCut _) at he
  rw [word_fromCut, word_fromCut] at he
  obtain ⟨h1, h2⟩ := List.append_inj he (by simp [wordOf])
  obtain ⟨h3, h4⟩ := List.append_inj h1 (by simp [wordOf])
  exact Prod.ext (word_injective h3) (Prod.ext (word_injective h4) (word_injective h2))

lemma b_sandwich (n r : ℕ) : b n * b r * b n ≤ b (2*n+r) := by
  classical
  obtain ⟨q, hq, eqn⟩ := best_offset n
  obtain ⟨p, hp, eqr⟩ := best_offset r
  have hc := Fintype.card_le_of_injective (@joinCodes n r q p) join_injective
  have h' : (atOffset n q).card * ((atOffset r p).card * (atOffset n q).card)
      ≤ (atOffset (2*n+r) (2*q+p)).card := by simpa [Fiber, Fintype.card_prod] using hc
  rw [eqn, eqr, Nat.mul_assoc]
  apply h'.trans
  apply Finset.le_sup (f := fun j => (atOffset (2*n+r) j).card)
  simp only [Finset.mem_range] at hq hp ⊢
  omega

lemma positive_from_cut {n q : ℕ} {w : List Dir} (h : IsCut n q w) : 0 < b n := by
  have hp : 0 < (atOffset n q).card := Finset.card_pos.mpr ⟨(fromCut h).val, (fromCut h).property⟩
  exact hp.trans_le (Finset.le_sup (f := fun j => (atOffset n j).card)
    (Finset.mem_range.mpr (Nat.lt_succ_of_lt h.2.1)))

lemma b_positive (n : ℕ) (hn : 2 ≤ n) : 0 < b n := by
  have h2 : IsCut 2 2 [0,1,0,3,3,0,1,0] := by unfold IsCut inside; decide
  have b2 := positive_from_cut h2
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.lt_or_ge n 6 with hlt | hge
    · have cases : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
      rcases cases with rfl | rfl | rfl | rfl
      · exact b2
      · apply positive_from_cut (q := 2) (w := [0,3,0,1,1,0,0,1,1,0,3,0])
        unfold IsCut inside
        decide
      · apply positive_from_cut (q := 2) (w := [0,3,0,1,1,1,0,0,0,0,1,1,1,0,3,0])
        unfold IsCut inside
        decide
      · apply positive_from_cut (q := 2) (w := [0,3,0,1,1,1,1,0,0,0,0,0,0,1,1,1,1,0,3,0])
        unfold IsCut inside
        decide
    · have hr := ih (n-4) (by omega) (by omega)
      have hcnt := b_sandwich 2 (n-4)
      rw [show 2*2+(n-4) = n by omega] at hcnt
      exact (Nat.mul_pos (Nat.mul_pos b2 hr) b2).trans_le hcnt

lemma repeated_sandwich (n r m : ℕ) :
    b n ^ (2*m) * b r ≤ b (2*m*n+r) := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc
      b n ^ (2*(m+1))*b r = b n * (b n ^ (2*m)*b r) * b n := by
        rw [show 2*(m+1)=2*m+2 by omega, pow_add]
        ring
      _ ≤ b n*b (2*m*n+r)*b n :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ih)
      _ ≤ b (2*n+(2*m*n+r)) := b_sandwich _ _
      _ = b (2*(m+1)*n+r) := by congr 1; ring

lemma growth_lower_bound (n r m : ℕ) (hr : 3 ≤ r) :
    b n ^ (2*m) ≤ 4*a (2*m*n+r) := by
  have hp := b_positive r (by omega)
  exact (Nat.le_mul_of_pos_right _ hp).trans ((repeated_sandwich n r m).trans
    (b_le_four_a _ (by omega)))

end OMA.S_oeis_a400685

open Filter Real Topology

namespace OMA.S_oeis_a400685

private lemma log_bound_from_stack (a b : ℕ → ℕ)
    (apos : ∀ n, 3 ≤ n → 0 < a n) (bpos : ∀ n, 3 ≤ n → 0 < b n)
    (stack : ∀ n m r : ℕ, 3 ≤ n → 3 ≤ r → b n ^ (2*m) ≤ 4*a (2*m*n+r))
    {n : ℕ} (hn : 3 ≤ n) :
    ∀ᶠ N : ℕ in atTop,
      log (b n) / n - (((2*n+2 : ℕ) : ℝ) * (log (b n) / n) + log 4) / N ≤
      log (a N) / N := by
  filter_upwards [eventually_ge_atTop 3] with N hN
  let m := (N-3)/(2*n)
  let r := (N-3)%(2*n)+3
  have hmod := Nat.mod_lt (N-3) (show 0 < 2*n by omega)
  have hrec := Nat.div_add_mod (N-3) (2*n)
  have hNr : N = 2*m*n+r := by
    dsimp [m, r]
    rw [show 2 * ((N-3)/(2*n)) * n = (2*n)*((N-3)/(2*n)) by ring]
    omega
  have hr : 3 ≤ r := by dsimp [r]; omega
  have hr' : r ≤ 2*n+2 := by dsimp [r]; omega
  have hnat := stack n m r hn hr
  rw [← hNr] at hnat
  have ha : 0 < (a N : ℝ) := by exact_mod_cast apos N hN
  have hb : 0 < (b n : ℝ) := by exact_mod_cast bpos n hn
  have hl := log_le_log (pow_pos hb (2*m))
    (show (b n : ℝ)^(2*m) ≤ 4*(a N : ℝ) by exact_mod_cast hnat)
  rw [log_pow, log_mul (by norm_num) ha.ne'] at hl
  have hb0 := log_nonneg (show 1 ≤ (b n : ℝ) by exact_mod_cast bpos n hn)
  have hn' : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN' : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hrR : (r : ℝ) ≤ 2*n+2 := by exact_mod_cast hr'
  have hNrR : (N:ℝ) = 2*m*n+r := by exact_mod_cast hNr
  set z : ℝ := log (b n) / n
  have hz0 : 0 ≤ z := div_nonneg hb0 hn'.le
  have hz : z * n = log (b n) := div_mul_cancel₀ _ hn'.ne'
  have hzN : z * N = (2*m : ℝ) * log (b n) + r*z := by rw [hNrR, ← hz]; ring
  have hzr := mul_le_mul_of_nonneg_right hrR hz0
  push_cast at hl ⊢
  apply (le_div_iff₀ hN').2
  rw [sub_mul, div_mul_cancel₀ _ hN'.ne', hzN]
  linarith

lemma growth_of_cut_counts (a b : ℕ → ℕ)
    (ab : ∀ n, 3 ≤ n → a n ≤ (2*n+1)*b n)
    (ba : ∀ n, 3 ≤ n → b n ≤ 4*a n)
    (walks : ∀ n, 3 ≤ n → a n ≤ (2*n+1)*4^(4*n))
    (bpos : ∀ n, 3 ≤ n → 0 < b n)
    (stack : ∀ n m r : ℕ, 3 ≤ n → 3 ≤ r → b n ^ (2*m) ≤ 4*a (2*m*n+r)) :
    ∃ c : ℝ, Tendsto (fun n : ℕ => (a n : ℝ)^((1:ℝ)/n)) atTop (𝓝 c) := by
  have ap (n : ℕ) (hn : 3 ≤ n) : 0 < a n := by
    have := bpos n hn
    have := ba n hn
    omega
  let S : Set ℝ := {x | ∃ n : ℕ, 3 ≤ n ∧ x = log (b n) / n}
  have sne : S.Nonempty := ⟨_, 3, le_rfl, rfl⟩
  have sbd : BddAbove S := by
    refine ⟨18, ?_⟩
    rintro x ⟨n, hn, rfl⟩
    have hnp : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hnl : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hnat := (ba n hn).trans (Nat.mul_le_mul_left 4 (walks n hn))
    have hprod : 0 < 2*(n:ℝ)+1 := by positivity
    have hb : 0 < (b n : ℝ) := by exact_mod_cast bpos n hn
    have hh := log_le_log hb (show (b n : ℝ) ≤ 4*((2*n+1)*4^(4*n)) by exact_mod_cast hnat)
    rw [log_mul (by norm_num) (by positivity), log_mul hprod.ne' (by positivity), log_pow] at hh
    have l1 := Real.log_le_sub_one_of_pos hprod
    have l4 := Real.log_le_sub_one_of_pos (show 0 < (4:ℝ) by norm_num)
    have hl4 : log 4 ≤ 3 := by linarith
    have hl4n := mul_le_mul_of_nonneg_left hl4 (show 0 ≤ 4*(n:ℝ) by positivity)
    push_cast at hh
    apply (div_le_iff₀ hnp).2
    linarith
  let C := sSup S
  have hlog : Tendsto (fun n : ℕ => log (a n) / n) atTop (𝓝 C) := by
    apply tendsto_order.2
    constructor
    · intro y hy
      obtain ⟨x, ⟨n, hn, rfl⟩, hyx⟩ := (lt_csSup_iff sbd sne).1 hy
      let z := log (b n) / (n : ℝ)
      let E := (((2*n+2 : ℕ) : ℝ) * z + log 4)
      have hconv : Tendsto (fun N : ℕ => z - E/N) atTop (𝓝 z) := by
        simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat E)
      filter_upwards [hconv.eventually_const_lt hyx, log_bound_from_stack a b ap bpos stack hn] with N hyN hlow
      exact hyN.trans_le hlow
    · intro y hy
      have err : Tendsto (fun n : ℕ => (log 3 + log n) / n) atTop (𝓝 0) := by
        have hh := isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
          (tendsto_natCast_atTop_atTop (R := ℝ))
        simpa [add_div, Function.comp_def] using (tendsto_const_div_atTop_nhds_zero_nat (log 3)).add hh
      have hv : Tendsto (fun n : ℕ => C + (log 3 + log n)/n) atTop (𝓝 C) := by
        simpa using tendsto_const_nhds.add err
      filter_upwards [eventually_ge_atTop 3, hv.eventually_lt_const hy] with n hn herr
      have hnp : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      have hap : 0 < (a n : ℝ) := by exact_mod_cast ap n hn
      have hbp : 0 < (b n : ℝ) := by exact_mod_cast bpos n hn
      have hle := log_le_log hap (show (a n : ℝ) ≤ (2*n+1)*b n by exact_mod_cast ab n hn)
      have hq : 0 < 2*(n:ℝ)+1 := by positivity
      rw [log_mul hq.ne' hbp.ne'] at hle
      have h3 := log_le_log hq (show 2*(n:ℝ)+1 ≤ 3*n by linarith)
      rw [log_mul (by norm_num) hnp.ne'] at h3
      have hsup : log (b n) / n ≤ C := le_csSup sbd ⟨n, hn, rfl⟩
      apply lt_of_le_of_lt _ herr
      calc
        log (a n) / n ≤ ((log 3 + log n) + log (b n)) / n :=
          div_le_div_of_nonneg_right (by linarith) hnp.le
        _ ≤ C + (log 3 + log n) / n := by rw [add_div]; linarith
  refine ⟨Real.exp C, (Real.continuous_exp.continuousAt.tendsto.comp hlog).congr' ?_⟩
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hpa : 0 < (a n : ℝ) := by exact_mod_cast ap n hn
  rw [Real.rpow_def_of_pos hpa]
  simp [div_eq_mul_inv]

end OMA.S_oeis_a400685

open OMA.S_oeis_a400685

theorem OMA.solution : type_of% @OMA.S_oeis_a400685.main := by
  apply growth_of_cut_counts a b
  · exact fun n hn => a_le_offset_bound n (by omega)
  · exact fun n hn => b_le_four_a n (by omega)
  · exact fun n hn => a_le_walk_bound n (by omega)
  · exact fun n hn => b_positive n (by omega)
  · exact fun n m r _ hr => growth_lower_bound n r m hr

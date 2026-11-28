import OMAStatements.S_oeis_a221969
import Mathlib

/-!
Proof. Put R_i = 2 * (sum of x_j for j < i) - (sum of all x_j) for i in 0..5. The conditions on
x say exactly that |R_i| + |R_(i+1)| ≤ 2n cyclically (indices mod 6), all R_i having one parity:
at a wrap-around the sum ahead minus the sum following is (R_(5) - R_0) / 2 and the last element
is -(R_0 + R_(5)) / 2, while elsewhere x_i = (R_(i+1) - R_i) / 2 and the difference is
(R_i + R_(i+1)) / 2. Even R_i = 2 u_i give cyclic integer tuples with |u_i| + |u_(i+1)| ≤ n, counted
by natural-number tuples (the absolute values) with weight 2 for each nonzero entry; odd
R_i = 2 v_i + 1 give, through |R_i| = 2 c_i + 1, 2^6 times the cyclic natural-number tuples with
c_i + c_(i+1) ≤ n - 1. A weighted cyclic count splits by the position of the first zero entry;
rotating that zero to the front leaves a path, counted by an explicit transfer recursion whose
values are polynomials (each step is a power sum, done by induction), and the tuples with no zero
entry are, after subtracting 1 from every entry, the tuples for the bound N - 2. Telescoping in N
gives a(n) as a polynomial in n for n ≥ 1, from which both conjectures follow.
-/

namespace OMA.P_oeis_a221969

open Finset
/-! ## Tuples in a box, paths and their transfer sums -/

def box (N L : ℕ) : Finset (Fin L → ℕ) := Fintype.piFinset fun _ => range (N + 1)

lemma sum_box_succ {β : Type*} [AddCommMonoid β] (N L : ℕ) (F : (Fin (L + 1) → ℕ) → β) :
    ∑ b ∈ box N (L + 1), F b = ∑ c ∈ range (N + 1), ∑ t ∈ box N L, F (Fin.cons c t) := by
  rw [← Finset.sum_product']
  symm
  apply Finset.sum_nbij' (fun x : ℕ × (Fin L → ℕ) => (Fin.cons x.1 x.2 : Fin (L + 1) → ℕ))
    (fun b => (b 0, Fin.tail b))
  · intro x hx
    simp only [box, Finset.mem_product, Fintype.mem_piFinset] at hx ⊢
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using hx.1
    · simpa using hx.2 i
  · intro b hb
    simp only [box, Finset.mem_product, Fintype.mem_piFinset] at hb ⊢
    exact ⟨hb 0, fun i => hb i.succ⟩
  · intro x _
    simp
  · intro b _
    simp
  · intro x _
    rfl

/-- A path `t` after a value `p`: consecutive sums at most `N`, entries flagged `true` positive. -/
def ok (N : ℕ) : (l : List Bool) → ℕ → (Fin l.length → ℕ) → Prop
  | [], _, _ => True
  | b :: l, p, t => p + t 0 ≤ N ∧ (b = true → 0 < t 0) ∧ ok N l (t 0) (Fin.tail t)

open Classical in
/-- The weighted number of paths after the value `p`, by the transfer recursion. -/
noncomputable def PSl (N : ℕ) (w : ℕ → ℕ) : List Bool → ℕ → ℕ
  | [], _ => 1
  | b :: l, p => ∑ c ∈ range (N + 1),
      if p + c ≤ N ∧ (b = true → 0 < c) then w c * PSl N w l c else 0

open Classical in
lemma PSl_eq (N : ℕ) (w : ℕ → ℕ) : ∀ (l : List Bool) (p : ℕ),
    ∑ t ∈ box N l.length, (if ok N l p t then ∏ i, w (t i) else 0) = PSl N w l p
  | [], p => by
    simp [box, ok, PSl]
  | b :: l, p => by
    show ∑ t ∈ box N (l.length + 1), _ = _
    rw [sum_box_succ, PSl]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [ok, Fin.cons_zero, Fin.tail_cons]
    by_cases h : p + c ≤ N ∧ (b = true → 0 < c)
    · rw [if_pos h, ← PSl_eq N w l c, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      by_cases h2 : ok N l c t
      · rw [if_pos ⟨h.1, h.2, h2⟩, if_pos h2]
        exact Fin.prod_univ_succ
          (fun i : Fin (l.length + 1) => w ((Fin.cons c t : Fin (l.length + 1) → ℕ) i))
      · simp [h2]
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun t _ => ?_
      rw [if_neg]
      tauto

lemma faulQ (Q H : ℚ → ℚ) (h0 : H 0 = 0) (hs : ∀ x : ℚ, H (x + 1) = H x + Q (x + 1)) :
    ∀ M : ℕ, ∑ i ∈ range M, Q ((i : ℚ) + 1) = H M
  | 0 => by simp [h0]
  | M + 1 => by
    rw [sum_range_succ, faulQ Q H h0 hs M]
    push_cast
    rw [hs]

open Classical in
lemma layer (N : ℕ) (w : ℕ → ℕ) (b : Bool) (l : List Bool) (p : ℕ) (hp : p ≤ N) :
    (PSl N w (b :: l) p : ℚ) = (if b = true then 0 else (w 0 : ℚ) * PSl N w l 0) +
      ∑ i ∈ range (N - p), (w (i + 1) : ℚ) * PSl N w l (i + 1) := by
  rw [PSl]
  push_cast
  have e : ∑ c ∈ range (N + 1), (if p + c ≤ N ∧ (b = true → 0 < c) then
      ((w c : ℚ) * PSl N w l c) else 0) = ∑ c ∈ range (N - p + 1),
      (if (b = true → 0 < c) then ((w c : ℚ) * PSl N w l c) else 0) := by
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext c
    simp only [Finset.mem_filter, Finset.mem_range]
    cases b <;> simp <;> omega
  rw [e, sum_range_succ']
  rw [add_comm]
  congr 1
  · cases b <;> simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [if_pos (fun _ => Nat.succ_pos i)]

lemma layer_sum (N : ℕ) (w : ℕ → ℕ) (wp : ℚ) (hw : ∀ c, (w (c + 1) : ℚ) = wp) (l : List Bool)
    (Pl : ℚ → ℚ) (hl : ∀ c ≤ N, (PSl N w l c : ℚ) = Pl c) (H : ℚ → ℚ) (h0 : H 0 = 0)
    (hs : ∀ x, H (x + 1) = H x + Pl (x + 1)) (p : ℕ) (hp : p ≤ N) :
    ∑ i ∈ range (N - p), (w (i + 1) : ℚ) * PSl N w l (i + 1) = wp * H ((N : ℚ) - p) := by
  rw [← Nat.cast_sub hp, ← faulQ Pl H h0 hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hw, hl (i + 1) (by simp at hi; omega)]
  push_cast
  rfl

lemma layerT (N : ℕ) (w : ℕ → ℕ) (wp : ℚ) (hw : ∀ c, (w (c + 1) : ℚ) = wp) (l : List Bool)
    (Pl : ℚ → ℚ) (hl : ∀ c ≤ N, (PSl N w l c : ℚ) = Pl c) (H : ℚ → ℚ) (h0 : H 0 = 0)
    (hs : ∀ x, H (x + 1) = H x + Pl (x + 1)) (p : ℕ) (hp : p ≤ N) :
    (PSl N w (true :: l) p : ℚ) = wp * H ((N : ℚ) - p) := by
  rw [layer N w true l p hp, layer_sum N w wp hw l Pl hl H h0 hs p hp]
  simp

lemma layerF (N : ℕ) (w : ℕ → ℕ) (hw0 : w 0 = 1) (wp : ℚ) (hw : ∀ c, (w (c + 1) : ℚ) = wp)
    (l : List Bool) (Pl : ℚ → ℚ) (hl : ∀ c ≤ N, (PSl N w l c : ℚ) = Pl c) (H : ℚ → ℚ)
    (h0 : H 0 = 0) (hs : ∀ x, H (x + 1) = H x + Pl (x + 1)) (p : ℕ) (hp : p ≤ N) :
    (PSl N w (false :: l) p : ℚ) = Pl 0 + wp * H ((N : ℚ) - p) := by
  rw [layer N w false l p hp, layer_sum N w wp hw l Pl hl H h0 hs p hp, hl 0 (Nat.zero_le _),
    hw0]
  simp

lemma PSl_nil (N : ℕ) (w : ℕ → ℕ) : ∀ c ≤ N, (PSl N w [] c : ℚ) = (fun _ => 1) (c : ℚ) := by
  intro c _
  simp [PSl]

/-! ## Weights -/

/-- Weight of an absolute value: the number of integers with that absolute value. -/
def w2 (c : ℕ) : ℕ := if c = 0 then 1 else 2

/-- The unit weight. -/
def w1 (_ : ℕ) : ℕ := 1

lemma w2_zero : w2 0 = 1 := rfl
lemma w2_succ (c : ℕ) : (w2 (c + 1) : ℚ) = 2 := by simp [w2]
lemma w1_zero : w1 0 = 1 := rfl
lemma w1_succ (c : ℕ) : (w1 (c + 1) : ℚ) = 1 := by simp [w1]

/-! ## Folding integer tuples onto natural-number tuples -/

lemma fold_sum (L : ℕ) (s : Finset ℤ) (t : Finset ℕ) (φ : ℤ → ℕ) (hφ : ∀ z ∈ s, φ z ∈ t)
    (F : (Fin L → ℕ) → ℕ) :
    ∑ u ∈ Fintype.piFinset (fun _ => s), F (fun i => φ (u i)) =
      ∑ b ∈ Fintype.piFinset (fun _ => t), F b * ∏ i, (s.filter (fun z => φ z = b i)).card := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun u : Fin L → ℤ => fun i => φ (u i))
    (t := Fintype.piFinset (fun _ => t))]
  · refine Finset.sum_congr rfl fun b _ => ?_
    have e : (Fintype.piFinset (fun _ => s)).filter (fun u : Fin L → ℤ => (fun i => φ (u i)) = b) =
        Fintype.piFinset (fun i => s.filter (fun z => φ z = b i)) := by
      ext u
      simp only [Finset.mem_filter, Fintype.mem_piFinset, funext_iff]
      exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩
    rw [Finset.sum_congr rfl (fun u hu => by rw [(Finset.mem_filter.1 hu).2]), Finset.sum_const, e,
      Fintype.card_piFinset, smul_eq_mul, mul_comm]
  · intro u hu
    simp only [Fintype.mem_piFinset] at hu ⊢
    exact fun i => hφ _ (hu i)

lemma fiber_abs (n m : ℕ) (hm : m ≤ n) :
    ((Icc (-(n : ℤ)) n).filter (fun z => z.natAbs = m)).card = w2 m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · have : (Icc (-(n : ℤ)) n).filter (fun z => z.natAbs = 0) = {0} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
      omega
    rw [this]
    rfl
  · have : (Icc (-(n : ℤ)) n).filter (fun z => z.natAbs = m) = {(m : ℤ), -(m : ℤ)} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [this, Finset.card_pair (by omega), w2, if_neg (by omega)]

/-- Folding an odd value `2 z + 1` to `(|2 z + 1| - 1) / 2`. -/
def oddFold (z : ℤ) : ℕ := if 0 ≤ z then z.toNat else (-z - 1).toNat

lemma fiber_odd (n m : ℕ) (hm : m ≤ n) :
    ((Icc (-(n : ℤ) - 1) n).filter (fun z => oddFold z = m)).card = 2 := by
  have : (Icc (-(n : ℤ) - 1) n).filter (fun z => oddFold z = m) = {(m : ℤ), -(m : ℤ) - 1} := by
    ext z
    rw [Finset.mem_filter]
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    unfold oddFold
    split_ifs <;> omega
  rw [this, Finset.card_pair (by omega)]
/-! ## Cyclic tuples -/

lemma forallK {P : Fin 6 → Prop} : (∀ i, P i) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 ∧ P 4 ∧ P 5 :=
  ⟨fun h => ⟨h 0, h 1, h 2, h 3, h 4, h 5⟩, fun ⟨h0, h1, h2, h3, h4, h5⟩ i => by
    fin_cases i
    exacts [h0, h1, h2, h3, h4, h5]⟩

/-- A cyclic tuple whose cyclically consecutive sums are at most `N`. -/
def cyc (N : ℕ) (b : Fin 6 → ℕ) : Prop := ∀ i, b i + b (i + 1) ≤ N

open Classical in
/-- The weighted number of cyclic tuples. -/
noncomputable def W (w : ℕ → ℕ) (N : ℕ) : ℕ :=
  ∑ b ∈ box N 6, if cyc N b then ∏ i, w (b i) else 0

open Classical in
lemma ind_split (b : Fin 6 → ℕ) :
    (∑ j : Fin 6, if (b j = 0 ∧ ∀ i < j, 0 < b i) then (1 : ℕ) else 0) +
      (if ∀ i, 0 < b i then 1 else 0) = 1 := by
  by_cases hall : ∀ i, 0 < b i
  · rw [if_pos hall, Finset.sum_eq_zero]
    intro j _
    rw [if_neg]
    intro h
    have := hall j
    omega
  · rw [if_neg hall, add_zero]
    push_neg at hall
    obtain ⟨i0, hi0⟩ := hall
    have hs : (Finset.univ.filter (fun i => b i = 0)).Nonempty := ⟨i0, by simp; omega⟩
    have hj0 : b ((Finset.univ.filter (fun i => b i = 0)).min' hs) = 0 := by
      have := (Finset.univ.filter (fun i => b i = 0)).min'_mem hs
      simpa using this
    have hmin : ∀ i < (Finset.univ.filter (fun i => b i = 0)).min' hs, 0 < b i := by
      intro i hi
      by_contra hc
      have hmem : i ∈ Finset.univ.filter (fun i => b i = 0) := by simp; omega
      exact absurd hi (not_lt.2 ((Finset.univ.filter (fun i => b i = 0)).min'_le i hmem))
    rw [Finset.sum_eq_single ((Finset.univ.filter (fun i => b i = 0)).min' hs)]
    · rw [if_pos ⟨hj0, hmin⟩]
    · intro j _ hj
      rw [if_neg]
      rintro ⟨hbj, hlt⟩
      rcases lt_trichotomy j ((Finset.univ.filter (fun i => b i = 0)).min' hs) with h | h | h
      · have := hmin j h
        omega
      · exact hj h
      · have := hlt _ h
        omega
    · intro h
      exact absurd (Finset.mem_univ _) h

open Classical in
lemma W_split (w : ℕ → ℕ) (N : ℕ) : W w N =
    ∑ j : Fin 6, (∑ b ∈ box N 6, if (b j = 0 ∧ ∀ i < j, 0 < b i) then
      (if cyc N b then ∏ i, w (b i) else 0) else 0) +
    ∑ b ∈ box N 6, if (∀ i, 0 < b i) then (if cyc N b then ∏ i, w (b i) else 0) else 0 := by
  rw [Finset.sum_comm, ← Finset.sum_add_distrib, W]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h := ind_split b
  have e : (if cyc N b then ∏ i, w (b i) else 0) =
      (if cyc N b then ∏ i, w (b i) else 0) *
        ((∑ j : Fin 6, if (b j = 0 ∧ ∀ i < j, 0 < b i) then (1 : ℕ) else 0) +
          (if ∀ i, 0 < b i then 1 else 0)) := by
    rw [h, mul_one]
  conv_lhs => rw [e]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  · split_ifs <;> simp

open Classical in
lemma piece_rot (w : ℕ → ℕ) (N : ℕ) (j : Fin 6) :
    (∑ b ∈ box N 6, if (b j = 0 ∧ ∀ i < j, 0 < b i) then
      (if cyc N b then ∏ i, w (b i) else 0) else 0) =
    ∑ c ∈ box N 6, if (c 0 = 0 ∧ ∀ i : Fin 6, 6 - (j : ℕ) ≤ (i : ℕ) → 0 < c i) then
      (if cyc N c then ∏ i, w (c i) else 0) else 0 := by
  apply Finset.sum_nbij' (fun b i => b (i + j)) (fun c i => c (i - j))
  · intro b hb
    simp only [box, Fintype.mem_piFinset] at hb ⊢
    exact fun i => hb _
  · intro c hc
    simp only [box, Fintype.mem_piFinset] at hc ⊢
    exact fun i => hc _
  · intro b _
    funext i
    simp
  · intro c _
    funext i
    simp
  · intro b _
    have hcyc : cyc N b ↔ cyc N (fun i => b (i + j)) := by
      constructor
      · intro h i
        have := h (i + j)
        rwa [add_right_comm] at this
      · intro h i
        have := h (i - j)
        beta_reduce at this
        rwa [sub_add_cancel, add_right_comm, sub_add_cancel] at this
    have hprod : ∏ i, w (b (i + j)) = ∏ i, w (b i) :=
      Equiv.prod_comp (Equiv.addRight j) (fun i => w (b i))
    have hflag : (b j = 0 ∧ ∀ i < j, 0 < b i) ↔
        (b (0 + j) = 0 ∧ ∀ i : Fin 6, 6 - (j : ℕ) ≤ (i : ℕ) → 0 < b (i + j)) := by
      rw [zero_add]
      refine and_congr Iff.rfl ⟨fun h i hi => h _ ?_, fun h i hi => ?_⟩
      · rw [Fin.lt_def, Fin.val_add]
        have := i.2
        have := j.2
        omega
      · have h2 := h (i - j) (by
          rw [Fin.val_sub]
          rw [Fin.lt_def] at hi
          have := i.2
          omega)
        rwa [sub_add_cancel] at h2
    beta_reduce
    by_cases h1 : b j = 0 ∧ ∀ i < j, 0 < b i
    · rw [if_pos h1, if_pos (hflag.1 h1)]
      by_cases h2 : cyc N b
      · rw [if_pos h2, if_pos (hcyc.1 h2), hprod]
      · rw [if_neg h2, if_neg (fun h => h2 (hcyc.2 h))]
    · rw [if_neg h1, if_neg (fun h => h1 (hflag.2 h))]

open Classical in
lemma pos_shift (w : ℕ → ℕ) (wp : ℕ) (hw : ∀ c, w (c + 1) = wp) (N : ℕ) :
    (∑ b ∈ box (N + 2) 6, if (∀ i, 0 < b i) then
      (if cyc (N + 2) b then ∏ i, w (b i) else 0) else 0) = wp ^ 6 * W w1 N := by
  rw [W, Finset.mul_sum]
  simp_rw [← ite_and, mul_ite, mul_zero]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_nbij' (fun b i => b i - 1) (fun b i => b i + 1)
  · intro b hb
    rw [Finset.mem_filter] at hb ⊢
    simp only [box, Fintype.mem_piFinset, Finset.mem_range, cyc] at hb ⊢
    obtain ⟨hb1, hb2, hb3⟩ := hb
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have := hb3 i
      have := hb2 (i + 1)
      omega
    · have := hb3 i
      have := hb2 i
      have := hb2 (i + 1)
      omega
  · intro b hb
    rw [Finset.mem_filter] at hb ⊢
    simp only [box, Fintype.mem_piFinset, Finset.mem_range, cyc] at hb ⊢
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
    · have := hb1 i
      omega
    · omega
    · have := hb2 i
      omega
  · intro b hb
    rw [Finset.mem_filter] at hb
    simp only [box, Fintype.mem_piFinset, Finset.mem_range, cyc] at hb
    funext i
    have := hb.2.1 i
    simp only
    omega
  · intro b _
    funext i
    simp
  · intro b hb
    rw [Finset.mem_filter] at hb
    simp only [box, Fintype.mem_piFinset, Finset.mem_range, cyc] at hb
    have e : ∀ i, w (b i) = wp := by
      intro i
      have := hb.2.1 i
      rw [show b i = (b i - 1) + 1 by omega, hw]
    simp [e, w1]

open Classical in
lemma pos_small (w : ℕ → ℕ) (N : ℕ) (hN : N ≤ 1) :
    (∑ b ∈ box N 6, if (∀ i, 0 < b i) then
      (if cyc N b then ∏ i, w (b i) else 0) else 0) = 0 := by
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases h : ∀ i, 0 < b i
  · rw [if_pos h, if_neg]
    intro hc
    have := hc 0
    have := h 0
    have := h (0 + 1)
    omega
  · rw [if_neg h]

lemma okL (N : ℕ) (b0 b1 b2 b3 b4 : Bool) (p : ℕ) (t : Fin 5 → ℕ) :
    ok N [b0, b1, b2, b3, b4] p t ↔
      p + t 0 ≤ N ∧ (b0 = true → 0 < t 0) ∧
      t 0 + t 1 ≤ N ∧ (b1 = true → 0 < t 1) ∧
      t 1 + t 2 ≤ N ∧ (b2 = true → 0 < t 2) ∧
      t 2 + t 3 ≤ N ∧ (b3 = true → 0 < t 3) ∧
      t 3 + t 4 ≤ N ∧ (b4 = true → 0 < t 4) ∧ True :=
  Iff.rfl

open Classical in
lemma piece_cons_0 (w : ℕ → ℕ) (N : ℕ) :
    (∑ c ∈ box N 6, if (c 0 = 0 ∧ ∀ i : Fin 6, 6 - ((0 : Fin 6) : ℕ) ≤ (i : ℕ) → 0 < c i) then
      (if cyc N c then ∏ i, w (c i) else 0) else 0) = w 0 * PSl N w [false, false, false, false, false] 0 := by
  rw [show box N 6 = box N (5 + 1) from rfl, sum_box_succ, Finset.sum_eq_single 0]
  · rw [← PSl_eq N w [false, false, false, false, false] 0, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have e : ((Fin.cons 0 t : Fin 6 → ℕ) 0 = 0 ∧ (∀ i : Fin 6, 6 - ((0 : Fin 6) : ℕ) ≤ (i : ℕ) →
        0 < (Fin.cons 0 t : Fin 6 → ℕ) i)) ∧ cyc N (Fin.cons 0 t) ↔ ok N [false, false, false, false, false] 0 t := by
      have c0 : (Fin.cons 0 t : Fin 6 → ℕ) 0 = 0 := rfl
      have c1 : (Fin.cons 0 t : Fin 6 → ℕ) 1 = t 0 := rfl
      have c2 : (Fin.cons 0 t : Fin 6 → ℕ) 2 = t 1 := rfl
      have c3 : (Fin.cons 0 t : Fin 6 → ℕ) 3 = t 2 := rfl
      have c4 : (Fin.cons 0 t : Fin 6 → ℕ) 4 = t 3 := rfl
      have c5 : (Fin.cons 0 t : Fin 6 → ℕ) 5 = t 4 := rfl
      have d0 : (Fin.cons 0 t : Fin 6 → ℕ) (0 + 1) = t 0 := rfl
      have d1 : (Fin.cons 0 t : Fin 6 → ℕ) (1 + 1) = t 1 := rfl
      have d2 : (Fin.cons 0 t : Fin 6 → ℕ) (2 + 1) = t 2 := rfl
      have d3 : (Fin.cons 0 t : Fin 6 → ℕ) (3 + 1) = t 3 := rfl
      have d4 : (Fin.cons 0 t : Fin 6 → ℕ) (4 + 1) = t 4 := rfl
      have d5 : (Fin.cons 0 t : Fin 6 → ℕ) (5 + 1) = 0 := rfl
      rw [okL]
      simp only [cyc, forallK, c0, c1, c2, c3, c4, c5, d0, d1, d2, d3, d4, d5, Fin.isValue] at *
      norm_num
      omega
    have hp : ∏ i, w ((Fin.cons 0 t : Fin 6 → ℕ) i) = w 0 * ∏ i, w (t i) :=
      Fin.prod_univ_succ (fun i : Fin 6 => w ((Fin.cons 0 t : Fin 6 → ℕ) i))
    by_cases h : ok N [false, false, false, false, false] 0 t
    · obtain ⟨⟨h1, h2⟩, h3⟩ := e.2 h
      rw [if_pos ⟨h1, h2⟩, if_pos h3, if_pos h]
      exact hp
    · rw [if_neg h, mul_zero]
      split_ifs with h1 h3
      · exact absurd (e.1 ⟨h1, h3⟩) h
      · rfl
      · rfl
  · intro c0 _ hc0
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [if_neg]
    rintro ⟨h, _⟩
    exact hc0 h
  · intro h
    exact absurd (by simp) h

open Classical in
lemma piece_cons_1 (w : ℕ → ℕ) (N : ℕ) :
    (∑ c ∈ box N 6, if (c 0 = 0 ∧ ∀ i : Fin 6, 6 - ((1 : Fin 6) : ℕ) ≤ (i : ℕ) → 0 < c i) then
      (if cyc N c then ∏ i, w (c i) else 0) else 0) = w 0 * PSl N w [false, false, false, false, true] 0 := by
  rw [show box N 6 = box N (5 + 1) from rfl, sum_box_succ, Finset.sum_eq_single 0]
  · rw [← PSl_eq N w [false, false, false, false, true] 0, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have e : ((Fin.cons 0 t : Fin 6 → ℕ) 0 = 0 ∧ (∀ i : Fin 6, 6 - ((1 : Fin 6) : ℕ) ≤ (i : ℕ) →
        0 < (Fin.cons 0 t : Fin 6 → ℕ) i)) ∧ cyc N (Fin.cons 0 t) ↔ ok N [false, false, false, false, true] 0 t := by
      have c0 : (Fin.cons 0 t : Fin 6 → ℕ) 0 = 0 := rfl
      have c1 : (Fin.cons 0 t : Fin 6 → ℕ) 1 = t 0 := rfl
      have c2 : (Fin.cons 0 t : Fin 6 → ℕ) 2 = t 1 := rfl
      have c3 : (Fin.cons 0 t : Fin 6 → ℕ) 3 = t 2 := rfl
      have c4 : (Fin.cons 0 t : Fin 6 → ℕ) 4 = t 3 := rfl
      have c5 : (Fin.cons 0 t : Fin 6 → ℕ) 5 = t 4 := rfl
      have d0 : (Fin.cons 0 t : Fin 6 → ℕ) (0 + 1) = t 0 := rfl
      have d1 : (Fin.cons 0 t : Fin 6 → ℕ) (1 + 1) = t 1 := rfl
      have d2 : (Fin.cons 0 t : Fin 6 → ℕ) (2 + 1) = t 2 := rfl
      have d3 : (Fin.cons 0 t : Fin 6 → ℕ) (3 + 1) = t 3 := rfl
      have d4 : (Fin.cons 0 t : Fin 6 → ℕ) (4 + 1) = t 4 := rfl
      have d5 : (Fin.cons 0 t : Fin 6 → ℕ) (5 + 1) = 0 := rfl
      rw [okL]
      simp only [cyc, forallK, c0, c1, c2, c3, c4, c5, d0, d1, d2, d3, d4, d5, Fin.isValue] at *
      norm_num
      omega
    have hp : ∏ i, w ((Fin.cons 0 t : Fin 6 → ℕ) i) = w 0 * ∏ i, w (t i) :=
      Fin.prod_univ_succ (fun i : Fin 6 => w ((Fin.cons 0 t : Fin 6 → ℕ) i))
    by_cases h : ok N [false, false, false, false, true] 0 t
    · obtain ⟨⟨h1, h2⟩, h3⟩ := e.2 h
      rw [if_pos ⟨h1, h2⟩, if_pos h3, if_pos h]
      exact hp
    · rw [if_neg h, mul_zero]
      split_ifs with h1 h3
      · exact absurd (e.1 ⟨h1, h3⟩) h
      · rfl
      · rfl
  · intro c0 _ hc0
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [if_neg]
    rintro ⟨h, _⟩
    exact hc0 h
  · intro h
    exact absurd (by simp) h

open Classical in
lemma piece_cons_2 (w : ℕ → ℕ) (N : ℕ) :
    (∑ c ∈ box N 6, if (c 0 = 0 ∧ ∀ i : Fin 6, 6 - ((2 : Fin 6) : ℕ) ≤ (i : ℕ) → 0 < c i) then
      (if cyc N c then ∏ i, w (c i) else 0) else 0) = w 0 * PSl N w [false, false, false, true, true] 0 := by
  rw [show box N 6 = box N (5 + 1) from rfl, sum_box_succ, Finset.sum_eq_single 0]
  · rw [← PSl_eq N w [false, false, false, true, true] 0, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have e : ((Fin.cons 0 t : Fin 6 → ℕ) 0 = 0 ∧ (∀ i : Fin 6, 6 - ((2 : Fin 6) : ℕ) ≤ (i : ℕ) →
        0 < (Fin.cons 0 t : Fin 6 → ℕ) i)) ∧ cyc N (Fin.cons 0 t) ↔ ok N [false, false, false, true, true] 0 t := by
      have c0 : (Fin.cons 0 t : Fin 6 → ℕ) 0 = 0 := rfl
      have c1 : (Fin.cons 0 t : Fin 6 → ℕ) 1 = t 0 := rfl
      have c2 : (Fin.cons 0 t : Fin 6 → ℕ) 2 = t 1 := rfl
      have c3 : (Fin.cons 0 t : Fin 6 → ℕ) 3 = t 2 := rfl
      have c4 : (Fin.cons 0 t : Fin 6 → ℕ) 4 = t 3 := rfl
      have c5 : (Fin.cons 0 t : Fin 6 → ℕ) 5 = t 4 := rfl
      have d0 : (Fin.cons 0 t : Fin 6 → ℕ) (0 + 1) = t 0 := rfl
      have d1 : (Fin.cons 0 t : Fin 6 → ℕ) (1 + 1) = t 1 := rfl
      have d2 : (Fin.cons 0 t : Fin 6 → ℕ) (2 + 1) = t 2 := rfl
      have d3 : (Fin.cons 0 t : Fin 6 → ℕ) (3 + 1) = t 3 := rfl
      have d4 : (Fin.cons 0 t : Fin 6 → ℕ) (4 + 1) = t 4 := rfl
      have d5 : (Fin.cons 0 t : Fin 6 → ℕ) (5 + 1) = 0 := rfl
      rw [okL]
      simp only [cyc, forallK, c0, c1, c2, c3, c4, c5, d0, d1, d2, d3, d4, d5, Fin.isValue] at *
      norm_num
      omega
    have hp : ∏ i, w ((Fin.cons 0 t : Fin 6 → ℕ) i) = w 0 * ∏ i, w (t i) :=
      Fin.prod_univ_succ (fun i : Fin 6 => w ((Fin.cons 0 t : Fin 6 → ℕ) i))
    by_cases h : ok N [false, false, false, true, true] 0 t
    · obtain ⟨⟨h1, h2⟩, h3⟩ := e.2 h
      rw [if_pos ⟨h1, h2⟩, if_pos h3, if_pos h]
      exact hp
    · rw [if_neg h, mul_zero]
      split_ifs with h1 h3
      · exact absurd (e.1 ⟨h1, h3⟩) h
      · rfl
      · rfl
  · intro c0 _ hc0
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [if_neg]
    rintro ⟨h, _⟩
    exact hc0 h
  · intro h
    exact absurd (by simp) h

open Classical in
lemma piece_cons_3 (w : ℕ → ℕ) (N : ℕ) :
    (∑ c ∈ box N 6, if (c 0 = 0 ∧ ∀ i : Fin 6, 6 - ((3 : Fin 6) : ℕ) ≤ (i : ℕ) → 0 < c i) then
      (if cyc N c then ∏ i, w (c i) else 0) else 0) = w 0 * PSl N w [false, false, true, true, true] 0 := by
  rw [show box N 6 = box N (5 + 1) from rfl, sum_box_succ, Finset.sum_eq_single 0]
  · rw [← PSl_eq N w [false, false, true, true, true] 0, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have e : ((Fin.cons 0 t : Fin 6 → ℕ) 0 = 0 ∧ (∀ i : Fin 6, 6 - ((3 : Fin 6) : ℕ) ≤ (i : ℕ) →
        0 < (Fin.cons 0 t : Fin 6 → ℕ) i)) ∧ cyc N (Fin.cons 0 t) ↔ ok N [false, false, true, true, true] 0 t := by
      have c0 : (Fin.cons 0 t : Fin 6 → ℕ) 0 = 0 := rfl
      have c1 : (Fin.cons 0 t : Fin 6 → ℕ) 1 = t 0 := rfl
      have c2 : (Fin.cons 0 t : Fin 6 → ℕ) 2 = t 1 := rfl
      have c3 : (Fin.cons 0 t : Fin 6 → ℕ) 3 = t 2 := rfl
      have c4 : (Fin.cons 0 t : Fin 6 → ℕ) 4 = t 3 := rfl
      have c5 : (Fin.cons 0 t : Fin 6 → ℕ) 5 = t 4 := rfl
      have d0 : (Fin.cons 0 t : Fin 6 → ℕ) (0 + 1) = t 0 := rfl
      have d1 : (Fin.cons 0 t : Fin 6 → ℕ) (1 + 1) = t 1 := rfl
      have d2 : (Fin.cons 0 t : Fin 6 → ℕ) (2 + 1) = t 2 := rfl
      have d3 : (Fin.cons 0 t : Fin 6 → ℕ) (3 + 1) = t 3 := rfl
      have d4 : (Fin.cons 0 t : Fin 6 → ℕ) (4 + 1) = t 4 := rfl
      have d5 : (Fin.cons 0 t : Fin 6 → ℕ) (5 + 1) = 0 := rfl
      rw [okL]
      simp only [cyc, forallK, c0, c1, c2, c3, c4, c5, d0, d1, d2, d3, d4, d5, Fin.isValue] at *
      norm_num
      omega
    have hp : ∏ i, w ((Fin.cons 0 t : Fin 6 → ℕ) i) = w 0 * ∏ i, w (t i) :=
      Fin.prod_univ_succ (fun i : Fin 6 => w ((Fin.cons 0 t : Fin 6 → ℕ) i))
    by_cases h : ok N [false, false, true, true, true] 0 t
    · obtain ⟨⟨h1, h2⟩, h3⟩ := e.2 h
      rw [if_pos ⟨h1, h2⟩, if_pos h3, if_pos h]
      exact hp
    · rw [if_neg h, mul_zero]
      split_ifs with h1 h3
      · exact absurd (e.1 ⟨h1, h3⟩) h
      · rfl
      · rfl
  · intro c0 _ hc0
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [if_neg]
    rintro ⟨h, _⟩
    exact hc0 h
  · intro h
    exact absurd (by simp) h

open Classical in
lemma piece_cons_4 (w : ℕ → ℕ) (N : ℕ) :
    (∑ c ∈ box N 6, if (c 0 = 0 ∧ ∀ i : Fin 6, 6 - ((4 : Fin 6) : ℕ) ≤ (i : ℕ) → 0 < c i) then
      (if cyc N c then ∏ i, w (c i) else 0) else 0) = w 0 * PSl N w [false, true, true, true, true] 0 := by
  rw [show box N 6 = box N (5 + 1) from rfl, sum_box_succ, Finset.sum_eq_single 0]
  · rw [← PSl_eq N w [false, true, true, true, true] 0, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have e : ((Fin.cons 0 t : Fin 6 → ℕ) 0 = 0 ∧ (∀ i : Fin 6, 6 - ((4 : Fin 6) : ℕ) ≤ (i : ℕ) →
        0 < (Fin.cons 0 t : Fin 6 → ℕ) i)) ∧ cyc N (Fin.cons 0 t) ↔ ok N [false, true, true, true, true] 0 t := by
      have c0 : (Fin.cons 0 t : Fin 6 → ℕ) 0 = 0 := rfl
      have c1 : (Fin.cons 0 t : Fin 6 → ℕ) 1 = t 0 := rfl
      have c2 : (Fin.cons 0 t : Fin 6 → ℕ) 2 = t 1 := rfl
      have c3 : (Fin.cons 0 t : Fin 6 → ℕ) 3 = t 2 := rfl
      have c4 : (Fin.cons 0 t : Fin 6 → ℕ) 4 = t 3 := rfl
      have c5 : (Fin.cons 0 t : Fin 6 → ℕ) 5 = t 4 := rfl
      have d0 : (Fin.cons 0 t : Fin 6 → ℕ) (0 + 1) = t 0 := rfl
      have d1 : (Fin.cons 0 t : Fin 6 → ℕ) (1 + 1) = t 1 := rfl
      have d2 : (Fin.cons 0 t : Fin 6 → ℕ) (2 + 1) = t 2 := rfl
      have d3 : (Fin.cons 0 t : Fin 6 → ℕ) (3 + 1) = t 3 := rfl
      have d4 : (Fin.cons 0 t : Fin 6 → ℕ) (4 + 1) = t 4 := rfl
      have d5 : (Fin.cons 0 t : Fin 6 → ℕ) (5 + 1) = 0 := rfl
      rw [okL]
      simp only [cyc, forallK, c0, c1, c2, c3, c4, c5, d0, d1, d2, d3, d4, d5, Fin.isValue] at *
      norm_num
      omega
    have hp : ∏ i, w ((Fin.cons 0 t : Fin 6 → ℕ) i) = w 0 * ∏ i, w (t i) :=
      Fin.prod_univ_succ (fun i : Fin 6 => w ((Fin.cons 0 t : Fin 6 → ℕ) i))
    by_cases h : ok N [false, true, true, true, true] 0 t
    · obtain ⟨⟨h1, h2⟩, h3⟩ := e.2 h
      rw [if_pos ⟨h1, h2⟩, if_pos h3, if_pos h]
      exact hp
    · rw [if_neg h, mul_zero]
      split_ifs with h1 h3
      · exact absurd (e.1 ⟨h1, h3⟩) h
      · rfl
      · rfl
  · intro c0 _ hc0
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [if_neg]
    rintro ⟨h, _⟩
    exact hc0 h
  · intro h
    exact absurd (by simp) h

open Classical in
lemma piece_cons_5 (w : ℕ → ℕ) (N : ℕ) :
    (∑ c ∈ box N 6, if (c 0 = 0 ∧ ∀ i : Fin 6, 6 - ((5 : Fin 6) : ℕ) ≤ (i : ℕ) → 0 < c i) then
      (if cyc N c then ∏ i, w (c i) else 0) else 0) = w 0 * PSl N w [true, true, true, true, true] 0 := by
  rw [show box N 6 = box N (5 + 1) from rfl, sum_box_succ, Finset.sum_eq_single 0]
  · rw [← PSl_eq N w [true, true, true, true, true] 0, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have e : ((Fin.cons 0 t : Fin 6 → ℕ) 0 = 0 ∧ (∀ i : Fin 6, 6 - ((5 : Fin 6) : ℕ) ≤ (i : ℕ) →
        0 < (Fin.cons 0 t : Fin 6 → ℕ) i)) ∧ cyc N (Fin.cons 0 t) ↔ ok N [true, true, true, true, true] 0 t := by
      have c0 : (Fin.cons 0 t : Fin 6 → ℕ) 0 = 0 := rfl
      have c1 : (Fin.cons 0 t : Fin 6 → ℕ) 1 = t 0 := rfl
      have c2 : (Fin.cons 0 t : Fin 6 → ℕ) 2 = t 1 := rfl
      have c3 : (Fin.cons 0 t : Fin 6 → ℕ) 3 = t 2 := rfl
      have c4 : (Fin.cons 0 t : Fin 6 → ℕ) 4 = t 3 := rfl
      have c5 : (Fin.cons 0 t : Fin 6 → ℕ) 5 = t 4 := rfl
      have d0 : (Fin.cons 0 t : Fin 6 → ℕ) (0 + 1) = t 0 := rfl
      have d1 : (Fin.cons 0 t : Fin 6 → ℕ) (1 + 1) = t 1 := rfl
      have d2 : (Fin.cons 0 t : Fin 6 → ℕ) (2 + 1) = t 2 := rfl
      have d3 : (Fin.cons 0 t : Fin 6 → ℕ) (3 + 1) = t 3 := rfl
      have d4 : (Fin.cons 0 t : Fin 6 → ℕ) (4 + 1) = t 4 := rfl
      have d5 : (Fin.cons 0 t : Fin 6 → ℕ) (5 + 1) = 0 := rfl
      rw [okL]
      simp only [cyc, forallK, c0, c1, c2, c3, c4, c5, d0, d1, d2, d3, d4, d5, Fin.isValue] at *
      norm_num
      omega
    have hp : ∏ i, w ((Fin.cons 0 t : Fin 6 → ℕ) i) = w 0 * ∏ i, w (t i) :=
      Fin.prod_univ_succ (fun i : Fin 6 => w ((Fin.cons 0 t : Fin 6 → ℕ) i))
    by_cases h : ok N [true, true, true, true, true] 0 t
    · obtain ⟨⟨h1, h2⟩, h3⟩ := e.2 h
      rw [if_pos ⟨h1, h2⟩, if_pos h3, if_pos h]
      exact hp
    · rw [if_neg h, mul_zero]
      split_ifs with h1 h3
      · exact absurd (e.1 ⟨h1, h3⟩) h
      · rfl
      · rfl
  · intro c0 _ hc0
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [if_neg]
    rintro ⟨h, _⟩
    exact hc0 h
  · intro h
    exact absurd (by simp) h

/-! ## Path values, weight `w2` -/

lemma PE_nil (N : ℕ) : ∀ p ≤ N, (PSl N w2 [] p : ℚ) = (fun _ => 1) (p : ℚ) := PSl_nil N w2

lemma PE_T (N : ℕ) : ∀ p ≤ N, (PSl N w2 [true] p : ℚ) = (fun x : ℚ =>
      -2 * x + 2 * (N : ℚ)) (p : ℚ) := by
  intro p hp
  rw [layerT N w2 2 w2_succ []
    (fun _ => 1)
    (PE_nil N)
    (fun x : ℚ => x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PE_F (N : ℕ) : ∀ p ≤ N, (PSl N w2 [false] p : ℚ) = (fun x : ℚ =>
      -2 * x + 2 * (N : ℚ) + 1) (p : ℚ) := by
  intro p hp
  rw [layerF N w2 w2_zero 2 w2_succ []
    (fun _ => 1)
    (PE_nil N)
    (fun x : ℚ => x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PE_FT (N : ℕ) : ∀ p ≤ N, (PSl N w2 [false, true] p : ℚ) = (fun x : ℚ =>
      -2 * x ^ 2 + 2 * x + 2 * (N : ℚ) ^ 2) (p : ℚ) := by
  intro p hp
  rw [layerF N w2 w2_zero 2 w2_succ [true]
    (fun x : ℚ => -2 * x + 2 * (N : ℚ))
    (PE_T N)
    (fun x : ℚ => -x ^ 2 + 2 * x * (N : ℚ) - x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PE_FF (N : ℕ) : ∀ p ≤ N, (PSl N w2 [false, false] p : ℚ) = (fun x : ℚ =>
      -2 * x ^ 2 + 2 * (N : ℚ) ^ 2 + 2 * (N : ℚ) + 1) (p : ℚ) := by
  intro p hp
  rw [layerF N w2 w2_zero 2 w2_succ [false]
    (fun x : ℚ => -2 * x + 2 * (N : ℚ) + 1)
    (PE_F N)
    (fun x : ℚ => -x ^ 2 + 2 * x * (N : ℚ))
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PE_TT (N : ℕ) : ∀ p ≤ N, (PSl N w2 [true, true] p : ℚ) = (fun x : ℚ =>
      -2 * x ^ 2 + 2 * x + 2 * (N : ℚ) ^ 2 - 2 * (N : ℚ)) (p : ℚ) := by
  intro p hp
  rw [layerT N w2 2 w2_succ [true]
    (fun x : ℚ => -2 * x + 2 * (N : ℚ))
    (PE_T N)
    (fun x : ℚ => -x ^ 2 + 2 * x * (N : ℚ) - x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PE_FFT (N : ℕ) : ∀ p ≤ N, (PSl N w2 [false, false, true] p : ℚ) = (fun x : ℚ =>
      (4 / 3 : ℚ) * x ^ 3 - 4 * x ^ 2 * (N : ℚ) - (4 / 3 : ℚ) * x + (8 / 3 : ℚ) * (N : ℚ) ^ 3 + 2 * (N : ℚ) ^ 2
      + (4 / 3 : ℚ) * (N : ℚ)) (p : ℚ) := by
  intro p hp
  rw [layerF N w2 w2_zero 2 w2_succ [false, true]
    (fun x : ℚ => -2 * x ^ 2 + 2 * x + 2 * (N : ℚ) ^ 2)
    (PE_FT N)
    (fun x : ℚ => -(2 / 3 : ℚ) * x ^ 3 + 2 * x * (N : ℚ) ^ 2 + (2 / 3 : ℚ) * x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PE_FFF (N : ℕ) : ∀ p ≤ N, (PSl N w2 [false, false, false] p : ℚ) = (fun x : ℚ =>
      (4 / 3 : ℚ) * x ^ 3 - 4 * x ^ 2 * (N : ℚ) - 2 * x ^ 2 - (4 / 3 : ℚ) * x + (8 / 3 : ℚ) * (N : ℚ) ^ 3
      + 4 * (N : ℚ) ^ 2 + (10 / 3 : ℚ) * (N : ℚ) + 1) (p : ℚ) := by
  intro p hp
  rw [layerF N w2 w2_zero 2 w2_succ [false, false]
    (fun x : ℚ => -2 * x ^ 2 + 2 * (N : ℚ) ^ 2 + 2 * (N : ℚ) + 1)
    (PE_FF N)
    (fun x : ℚ => -(2 / 3 : ℚ) * x ^ 3 - x ^ 2 + 2 * x * (N : ℚ) ^ 2 + 2 * x * (N : ℚ) + (2 / 3 : ℚ) * x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PE_FTT (N : ℕ) : ∀ p ≤ N, (PSl N w2 [false, true, true] p : ℚ) = (fun x : ℚ =>
      (4 / 3 : ℚ) * x ^ 3 - 4 * x ^ 2 * (N : ℚ) + 4 * x * (N : ℚ) - (4 / 3 : ℚ) * x + (8 / 3 : ℚ) * (N : ℚ) ^ 3
      - 2 * (N : ℚ) ^ 2 - (2 / 3 : ℚ) * (N : ℚ)) (p : ℚ) := by
  intro p hp
  rw [layerF N w2 w2_zero 2 w2_succ [true, true]
    (fun x : ℚ => -2 * x ^ 2 + 2 * x + 2 * (N : ℚ) ^ 2 - 2 * (N : ℚ))
    (PE_TT N)
    (fun x : ℚ => -(2 / 3 : ℚ) * x ^ 3 + 2 * x * (N : ℚ) ^ 2 - 2 * x * (N : ℚ) + (2 / 3 : ℚ) * x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PE_TTT (N : ℕ) : ∀ p ≤ N, (PSl N w2 [true, true, true] p : ℚ) = (fun x : ℚ =>
      (4 / 3 : ℚ) * x ^ 3 - 4 * x ^ 2 * (N : ℚ) + 4 * x * (N : ℚ) - (4 / 3 : ℚ) * x + (8 / 3 : ℚ) * (N : ℚ) ^ 3
      - 4 * (N : ℚ) ^ 2 + (4 / 3 : ℚ) * (N : ℚ)) (p : ℚ) := by
  intro p hp
  rw [layerT N w2 2 w2_succ [true, true]
    (fun x : ℚ => -2 * x ^ 2 + 2 * x + 2 * (N : ℚ) ^ 2 - 2 * (N : ℚ))
    (PE_TT N)
    (fun x : ℚ => -(2 / 3 : ℚ) * x ^ 3 + 2 * x * (N : ℚ) ^ 2 - 2 * x * (N : ℚ) + (2 / 3 : ℚ) * x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PE_FFTT (N : ℕ) : ∀ p ≤ N, (PSl N w2 [false, false, true, true] p : ℚ) = (fun x : ℚ =>
      (2 / 3 : ℚ) * x ^ 4 - (4 / 3 : ℚ) * x ^ 3 - 4 * x ^ 2 * (N : ℚ) ^ 2 + 4 * x ^ 2 * (N : ℚ) - (2 / 3 : ℚ) * x ^ 2
      + (4 / 3 : ℚ) * x + (10 / 3 : ℚ) * (N : ℚ) ^ 4 - (4 / 3 : ℚ) * (N : ℚ) ^ 2 - 2 * (N : ℚ)) (p : ℚ) := by
  intro p hp
  rw [layerF N w2 w2_zero 2 w2_succ [false, true, true]
    (fun x : ℚ => (4 / 3 : ℚ) * x ^ 3 - 4 * x ^ 2 * (N : ℚ) + 4 * x * (N : ℚ) - (4 / 3 : ℚ) * x + (8 / 3 : ℚ) * (N : ℚ) ^ 3
        - 2 * (N : ℚ) ^ 2 - (2 / 3 : ℚ) * (N : ℚ))
    (PE_FTT N)
    (fun x : ℚ => (1 / 3 : ℚ) * x ^ 4 - (4 / 3 : ℚ) * x ^ 3 * (N : ℚ) + (2 / 3 : ℚ) * x ^ 3 - (1 / 3 : ℚ) * x ^ 2
        + (8 / 3 : ℚ) * x * (N : ℚ) ^ 3 - 2 * x * (N : ℚ) ^ 2 + (2 / 3 : ℚ) * x * (N : ℚ) - (2 / 3 : ℚ) * x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PE_TTTT (N : ℕ) : ∀ p ≤ N, (PSl N w2 [true, true, true, true] p : ℚ) = (fun x : ℚ =>
      (2 / 3 : ℚ) * x ^ 4 - (4 / 3 : ℚ) * x ^ 3 - 4 * x ^ 2 * (N : ℚ) ^ 2 + 4 * x ^ 2 * (N : ℚ) - (2 / 3 : ℚ) * x ^ 2
      + 4 * x * (N : ℚ) ^ 2 - 4 * x * (N : ℚ) + (4 / 3 : ℚ) * x + (10 / 3 : ℚ) * (N : ℚ) ^ 4 - (20 / 3 : ℚ) * (N : ℚ) ^ 3
      + (14 / 3 : ℚ) * (N : ℚ) ^ 2 - (4 / 3 : ℚ) * (N : ℚ)) (p : ℚ) := by
  intro p hp
  rw [layerT N w2 2 w2_succ [true, true, true]
    (fun x : ℚ => (4 / 3 : ℚ) * x ^ 3 - 4 * x ^ 2 * (N : ℚ) + 4 * x * (N : ℚ) - (4 / 3 : ℚ) * x + (8 / 3 : ℚ) * (N : ℚ) ^ 3
        - 4 * (N : ℚ) ^ 2 + (4 / 3 : ℚ) * (N : ℚ))
    (PE_TTT N)
    (fun x : ℚ => (1 / 3 : ℚ) * x ^ 4 - (4 / 3 : ℚ) * x ^ 3 * (N : ℚ) + (2 / 3 : ℚ) * x ^ 3 - (1 / 3 : ℚ) * x ^ 2
        + (8 / 3 : ℚ) * x * (N : ℚ) ^ 3 - 4 * x * (N : ℚ) ^ 2 + (8 / 3 : ℚ) * x * (N : ℚ) - (2 / 3 : ℚ) * x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PE_FFFT (N : ℕ) : ∀ p ≤ N, (PSl N w2 [false, false, false, true] p : ℚ) = (fun x : ℚ =>
      (2 / 3 : ℚ) * x ^ 4 - (4 / 3 : ℚ) * x ^ 3 - 4 * x ^ 2 * (N : ℚ) ^ 2 - (2 / 3 : ℚ) * x ^ 2 + (4 / 3 : ℚ) * x
      + (10 / 3 : ℚ) * (N : ℚ) ^ 4 + 4 * (N : ℚ) ^ 3 + (8 / 3 : ℚ) * (N : ℚ) ^ 2) (p : ℚ) := by
  intro p hp
  rw [layerF N w2 w2_zero 2 w2_succ [false, false, true]
    (fun x : ℚ => (4 / 3 : ℚ) * x ^ 3 - 4 * x ^ 2 * (N : ℚ) - (4 / 3 : ℚ) * x + (8 / 3 : ℚ) * (N : ℚ) ^ 3 + 2 * (N : ℚ) ^ 2
        + (4 / 3 : ℚ) * (N : ℚ))
    (PE_FFT N)
    (fun x : ℚ => (1 / 3 : ℚ) * x ^ 4 - (4 / 3 : ℚ) * x ^ 3 * (N : ℚ) + (2 / 3 : ℚ) * x ^ 3 - 2 * x ^ 2 * (N : ℚ)
        - (1 / 3 : ℚ) * x ^ 2 + (8 / 3 : ℚ) * x * (N : ℚ) ^ 3 + 2 * x * (N : ℚ) ^ 2 + (2 / 3 : ℚ) * x * (N : ℚ)
        - (2 / 3 : ℚ) * x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PE_FTTT (N : ℕ) : ∀ p ≤ N, (PSl N w2 [false, true, true, true] p : ℚ) = (fun x : ℚ =>
      (2 / 3 : ℚ) * x ^ 4 - (4 / 3 : ℚ) * x ^ 3 - 4 * x ^ 2 * (N : ℚ) ^ 2 + 4 * x ^ 2 * (N : ℚ) - (2 / 3 : ℚ) * x ^ 2
      + 4 * x * (N : ℚ) ^ 2 - 4 * x * (N : ℚ) + (4 / 3 : ℚ) * x + (10 / 3 : ℚ) * (N : ℚ) ^ 4 - 4 * (N : ℚ) ^ 3
      + (2 / 3 : ℚ) * (N : ℚ) ^ 2) (p : ℚ) := by
  intro p hp
  rw [layerF N w2 w2_zero 2 w2_succ [true, true, true]
    (fun x : ℚ => (4 / 3 : ℚ) * x ^ 3 - 4 * x ^ 2 * (N : ℚ) + 4 * x * (N : ℚ) - (4 / 3 : ℚ) * x + (8 / 3 : ℚ) * (N : ℚ) ^ 3
        - 4 * (N : ℚ) ^ 2 + (4 / 3 : ℚ) * (N : ℚ))
    (PE_TTT N)
    (fun x : ℚ => (1 / 3 : ℚ) * x ^ 4 - (4 / 3 : ℚ) * x ^ 3 * (N : ℚ) + (2 / 3 : ℚ) * x ^ 3 - (1 / 3 : ℚ) * x ^ 2
        + (8 / 3 : ℚ) * x * (N : ℚ) ^ 3 - 4 * x * (N : ℚ) ^ 2 + (8 / 3 : ℚ) * x * (N : ℚ) - (2 / 3 : ℚ) * x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PE_FFFF (N : ℕ) : ∀ p ≤ N, (PSl N w2 [false, false, false, false] p : ℚ) = (fun x : ℚ =>
      (2 / 3 : ℚ) * x ^ 4 - 4 * x ^ 2 * (N : ℚ) ^ 2 - 4 * x ^ 2 * (N : ℚ) - (8 / 3 : ℚ) * x ^ 2 + (10 / 3 : ℚ) * (N : ℚ) ^ 4
      + (20 / 3 : ℚ) * (N : ℚ) ^ 3 + (20 / 3 : ℚ) * (N : ℚ) ^ 2 + (10 / 3 : ℚ) * (N : ℚ) + 1) (p : ℚ) := by
  intro p hp
  rw [layerF N w2 w2_zero 2 w2_succ [false, false, false]
    (fun x : ℚ => (4 / 3 : ℚ) * x ^ 3 - 4 * x ^ 2 * (N : ℚ) - 2 * x ^ 2 - (4 / 3 : ℚ) * x + (8 / 3 : ℚ) * (N : ℚ) ^ 3
        + 4 * (N : ℚ) ^ 2 + (10 / 3 : ℚ) * (N : ℚ) + 1)
    (PE_FFF N)
    (fun x : ℚ => (1 / 3 : ℚ) * x ^ 4 - (4 / 3 : ℚ) * x ^ 3 * (N : ℚ) - 2 * x ^ 2 * (N : ℚ) - (4 / 3 : ℚ) * x ^ 2
        + (8 / 3 : ℚ) * x * (N : ℚ) ^ 3 + 4 * x * (N : ℚ) ^ 2 + (8 / 3 : ℚ) * x * (N : ℚ))
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PE_FFFFF (N : ℕ) : ∀ p ≤ N, (PSl N w2 [false, false, false, false, false] p : ℚ) = (fun x : ℚ =>
      -(4 / 15 : ℚ) * x ^ 5 + (4 / 3 : ℚ) * x ^ 4 * (N : ℚ) + (2 / 3 : ℚ) * x ^ 4 + (4 / 3 : ℚ) * x ^ 3
      - (16 / 3 : ℚ) * x ^ 2 * (N : ℚ) ^ 3 - 8 * x ^ 2 * (N : ℚ) ^ 2 - 8 * x ^ 2 * (N : ℚ) - (8 / 3 : ℚ) * x ^ 2
      - (16 / 15 : ℚ) * x + (64 / 15 : ℚ) * (N : ℚ) ^ 5 + (32 / 3 : ℚ) * (N : ℚ) ^ 4 + (40 / 3 : ℚ) * (N : ℚ) ^ 3
      + (28 / 3 : ℚ) * (N : ℚ) ^ 2 + (22 / 5 : ℚ) * (N : ℚ) + 1) (p : ℚ) := by
  intro p hp
  rw [layerF N w2 w2_zero 2 w2_succ [false, false, false, false]
    (fun x : ℚ => (2 / 3 : ℚ) * x ^ 4 - 4 * x ^ 2 * (N : ℚ) ^ 2 - 4 * x ^ 2 * (N : ℚ) - (8 / 3 : ℚ) * x ^ 2
        + (10 / 3 : ℚ) * (N : ℚ) ^ 4 + (20 / 3 : ℚ) * (N : ℚ) ^ 3 + (20 / 3 : ℚ) * (N : ℚ) ^ 2 + (10 / 3 : ℚ) * (N : ℚ)
        + 1)
    (PE_FFFF N)
    (fun x : ℚ => (2 / 15 : ℚ) * x ^ 5 + (1 / 3 : ℚ) * x ^ 4 - (4 / 3 : ℚ) * x ^ 3 * (N : ℚ) ^ 2 - (4 / 3 : ℚ) * x ^ 3 * (N : ℚ)
        - (2 / 3 : ℚ) * x ^ 3 - 2 * x ^ 2 * (N : ℚ) ^ 2 - 2 * x ^ 2 * (N : ℚ) - (4 / 3 : ℚ) * x ^ 2
        + (10 / 3 : ℚ) * x * (N : ℚ) ^ 4 + (20 / 3 : ℚ) * x * (N : ℚ) ^ 3 + 6 * x * (N : ℚ) ^ 2 + (8 / 3 : ℚ) * x * (N : ℚ)
        + (8 / 15 : ℚ) * x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PE_FTTTT (N : ℕ) : ∀ p ≤ N, (PSl N w2 [false, true, true, true, true] p : ℚ) = (fun x : ℚ =>
      -(4 / 15 : ℚ) * x ^ 5 + (4 / 3 : ℚ) * x ^ 4 * (N : ℚ) - (8 / 3 : ℚ) * x ^ 3 * (N : ℚ) + (4 / 3 : ℚ) * x ^ 3
      - (16 / 3 : ℚ) * x ^ 2 * (N : ℚ) ^ 3 + 8 * x ^ 2 * (N : ℚ) ^ 2 - 4 * x ^ 2 * (N : ℚ) + (16 / 3 : ℚ) * x * (N : ℚ) ^ 3
      - 8 * x * (N : ℚ) ^ 2 + (16 / 3 : ℚ) * x * (N : ℚ) - (16 / 15 : ℚ) * x + (64 / 15 : ℚ) * (N : ℚ) ^ 5
      - (22 / 3 : ℚ) * (N : ℚ) ^ 4 + 4 * (N : ℚ) ^ 3 - (2 / 3 : ℚ) * (N : ℚ) ^ 2 - (4 / 15 : ℚ) * (N : ℚ)) (p : ℚ) := by
  intro p hp
  rw [layerF N w2 w2_zero 2 w2_succ [true, true, true, true]
    (fun x : ℚ => (2 / 3 : ℚ) * x ^ 4 - (4 / 3 : ℚ) * x ^ 3 - 4 * x ^ 2 * (N : ℚ) ^ 2 + 4 * x ^ 2 * (N : ℚ)
        - (2 / 3 : ℚ) * x ^ 2 + 4 * x * (N : ℚ) ^ 2 - 4 * x * (N : ℚ) + (4 / 3 : ℚ) * x + (10 / 3 : ℚ) * (N : ℚ) ^ 4
        - (20 / 3 : ℚ) * (N : ℚ) ^ 3 + (14 / 3 : ℚ) * (N : ℚ) ^ 2 - (4 / 3 : ℚ) * (N : ℚ))
    (PE_TTTT N)
    (fun x : ℚ => (2 / 15 : ℚ) * x ^ 5 - (4 / 3 : ℚ) * x ^ 3 * (N : ℚ) ^ 2 + (4 / 3 : ℚ) * x ^ 3 * (N : ℚ) - (2 / 3 : ℚ) * x ^ 3
        + (10 / 3 : ℚ) * x * (N : ℚ) ^ 4 - (20 / 3 : ℚ) * x * (N : ℚ) ^ 3 + 6 * x * (N : ℚ) ^ 2 - (8 / 3 : ℚ) * x * (N : ℚ)
        + (8 / 15 : ℚ) * x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PE_TTTTT (N : ℕ) : ∀ p ≤ N, (PSl N w2 [true, true, true, true, true] p : ℚ) = (fun x : ℚ =>
      -(4 / 15 : ℚ) * x ^ 5 + (4 / 3 : ℚ) * x ^ 4 * (N : ℚ) - (8 / 3 : ℚ) * x ^ 3 * (N : ℚ) + (4 / 3 : ℚ) * x ^ 3
      - (16 / 3 : ℚ) * x ^ 2 * (N : ℚ) ^ 3 + 8 * x ^ 2 * (N : ℚ) ^ 2 - 4 * x ^ 2 * (N : ℚ) + (16 / 3 : ℚ) * x * (N : ℚ) ^ 3
      - 8 * x * (N : ℚ) ^ 2 + (16 / 3 : ℚ) * x * (N : ℚ) - (16 / 15 : ℚ) * x + (64 / 15 : ℚ) * (N : ℚ) ^ 5
      - (32 / 3 : ℚ) * (N : ℚ) ^ 4 + (32 / 3 : ℚ) * (N : ℚ) ^ 3 - (16 / 3 : ℚ) * (N : ℚ) ^ 2 + (16 / 15 : ℚ) * (N : ℚ)) (p : ℚ) := by
  intro p hp
  rw [layerT N w2 2 w2_succ [true, true, true, true]
    (fun x : ℚ => (2 / 3 : ℚ) * x ^ 4 - (4 / 3 : ℚ) * x ^ 3 - 4 * x ^ 2 * (N : ℚ) ^ 2 + 4 * x ^ 2 * (N : ℚ)
        - (2 / 3 : ℚ) * x ^ 2 + 4 * x * (N : ℚ) ^ 2 - 4 * x * (N : ℚ) + (4 / 3 : ℚ) * x + (10 / 3 : ℚ) * (N : ℚ) ^ 4
        - (20 / 3 : ℚ) * (N : ℚ) ^ 3 + (14 / 3 : ℚ) * (N : ℚ) ^ 2 - (4 / 3 : ℚ) * (N : ℚ))
    (PE_TTTT N)
    (fun x : ℚ => (2 / 15 : ℚ) * x ^ 5 - (4 / 3 : ℚ) * x ^ 3 * (N : ℚ) ^ 2 + (4 / 3 : ℚ) * x ^ 3 * (N : ℚ) - (2 / 3 : ℚ) * x ^ 3
        + (10 / 3 : ℚ) * x * (N : ℚ) ^ 4 - (20 / 3 : ℚ) * x * (N : ℚ) ^ 3 + 6 * x * (N : ℚ) ^ 2 - (8 / 3 : ℚ) * x * (N : ℚ)
        + (8 / 15 : ℚ) * x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PE_FFTTT (N : ℕ) : ∀ p ≤ N, (PSl N w2 [false, false, true, true, true] p : ℚ) = (fun x : ℚ =>
      -(4 / 15 : ℚ) * x ^ 5 + (4 / 3 : ℚ) * x ^ 4 * (N : ℚ) - (8 / 3 : ℚ) * x ^ 3 * (N : ℚ) + (4 / 3 : ℚ) * x ^ 3
      - (16 / 3 : ℚ) * x ^ 2 * (N : ℚ) ^ 3 + 8 * x ^ 2 * (N : ℚ) ^ 2 - 4 * x ^ 2 * (N : ℚ) + (8 / 3 : ℚ) * x * (N : ℚ)
      - (16 / 15 : ℚ) * x + (64 / 15 : ℚ) * (N : ℚ) ^ 5 - 2 * (N : ℚ) ^ 4 - (4 / 3 : ℚ) * (N : ℚ) ^ 3
      - 2 * (N : ℚ) ^ 2 + (16 / 15 : ℚ) * (N : ℚ)) (p : ℚ) := by
  intro p hp
  rw [layerF N w2 w2_zero 2 w2_succ [false, true, true, true]
    (fun x : ℚ => (2 / 3 : ℚ) * x ^ 4 - (4 / 3 : ℚ) * x ^ 3 - 4 * x ^ 2 * (N : ℚ) ^ 2 + 4 * x ^ 2 * (N : ℚ)
        - (2 / 3 : ℚ) * x ^ 2 + 4 * x * (N : ℚ) ^ 2 - 4 * x * (N : ℚ) + (4 / 3 : ℚ) * x + (10 / 3 : ℚ) * (N : ℚ) ^ 4
        - 4 * (N : ℚ) ^ 3 + (2 / 3 : ℚ) * (N : ℚ) ^ 2)
    (PE_FTTT N)
    (fun x : ℚ => (2 / 15 : ℚ) * x ^ 5 - (4 / 3 : ℚ) * x ^ 3 * (N : ℚ) ^ 2 + (4 / 3 : ℚ) * x ^ 3 * (N : ℚ) - (2 / 3 : ℚ) * x ^ 3
        + (10 / 3 : ℚ) * x * (N : ℚ) ^ 4 - 4 * x * (N : ℚ) ^ 3 + 2 * x * (N : ℚ) ^ 2 - (4 / 3 : ℚ) * x * (N : ℚ)
        + (8 / 15 : ℚ) * x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PE_FFFTT (N : ℕ) : ∀ p ≤ N, (PSl N w2 [false, false, false, true, true] p : ℚ) = (fun x : ℚ =>
      -(4 / 15 : ℚ) * x ^ 5 + (4 / 3 : ℚ) * x ^ 4 * (N : ℚ) - (8 / 3 : ℚ) * x ^ 3 * (N : ℚ) + (4 / 3 : ℚ) * x ^ 3
      - (16 / 3 : ℚ) * x ^ 2 * (N : ℚ) ^ 3 + 4 * x ^ 2 * (N : ℚ) ^ 2 + (8 / 3 : ℚ) * x * (N : ℚ) - (16 / 15 : ℚ) * x
      + (64 / 15 : ℚ) * (N : ℚ) ^ 5 + 2 * (N : ℚ) ^ 4 - (4 / 3 : ℚ) * (N : ℚ) ^ 3 - 4 * (N : ℚ) ^ 2
      - (14 / 15 : ℚ) * (N : ℚ)) (p : ℚ) := by
  intro p hp
  rw [layerF N w2 w2_zero 2 w2_succ [false, false, true, true]
    (fun x : ℚ => (2 / 3 : ℚ) * x ^ 4 - (4 / 3 : ℚ) * x ^ 3 - 4 * x ^ 2 * (N : ℚ) ^ 2 + 4 * x ^ 2 * (N : ℚ)
        - (2 / 3 : ℚ) * x ^ 2 + (4 / 3 : ℚ) * x + (10 / 3 : ℚ) * (N : ℚ) ^ 4 - (4 / 3 : ℚ) * (N : ℚ) ^ 2
        - 2 * (N : ℚ))
    (PE_FFTT N)
    (fun x : ℚ => (2 / 15 : ℚ) * x ^ 5 - (4 / 3 : ℚ) * x ^ 3 * (N : ℚ) ^ 2 + (4 / 3 : ℚ) * x ^ 3 * (N : ℚ) - (2 / 3 : ℚ) * x ^ 3
        - 2 * x ^ 2 * (N : ℚ) ^ 2 + 2 * x ^ 2 * (N : ℚ) + (10 / 3 : ℚ) * x * (N : ℚ) ^ 4 - 2 * x * (N : ℚ) ^ 2
        - (4 / 3 : ℚ) * x * (N : ℚ) + (8 / 15 : ℚ) * x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PE_FFFFT (N : ℕ) : ∀ p ≤ N, (PSl N w2 [false, false, false, false, true] p : ℚ) = (fun x : ℚ =>
      -(4 / 15 : ℚ) * x ^ 5 + (4 / 3 : ℚ) * x ^ 4 * (N : ℚ) + (4 / 3 : ℚ) * x ^ 3 - (16 / 3 : ℚ) * x ^ 2 * (N : ℚ) ^ 3
      - 4 * x ^ 2 * (N : ℚ) ^ 2 - 4 * x ^ 2 * (N : ℚ) - (16 / 15 : ℚ) * x + (64 / 15 : ℚ) * (N : ℚ) ^ 5
      + (22 / 3 : ℚ) * (N : ℚ) ^ 4 + (20 / 3 : ℚ) * (N : ℚ) ^ 3 + (8 / 3 : ℚ) * (N : ℚ) ^ 2 + (16 / 15 : ℚ) * (N : ℚ)) (p : ℚ) := by
  intro p hp
  rw [layerF N w2 w2_zero 2 w2_succ [false, false, false, true]
    (fun x : ℚ => (2 / 3 : ℚ) * x ^ 4 - (4 / 3 : ℚ) * x ^ 3 - 4 * x ^ 2 * (N : ℚ) ^ 2 - (2 / 3 : ℚ) * x ^ 2
        + (4 / 3 : ℚ) * x + (10 / 3 : ℚ) * (N : ℚ) ^ 4 + 4 * (N : ℚ) ^ 3 + (8 / 3 : ℚ) * (N : ℚ) ^ 2)
    (PE_FFFT N)
    (fun x : ℚ => (2 / 15 : ℚ) * x ^ 5 - (4 / 3 : ℚ) * x ^ 3 * (N : ℚ) ^ 2 - (2 / 3 : ℚ) * x ^ 3 - 2 * x ^ 2 * (N : ℚ) ^ 2
        + (10 / 3 : ℚ) * x * (N : ℚ) ^ 4 + 4 * x * (N : ℚ) ^ 3 + 2 * x * (N : ℚ) ^ 2 + (8 / 15 : ℚ) * x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

open Classical in
lemma W_E (N : ℕ) : (W w2 N : ℚ) = (fun x : ℚ =>
      (128 / 5 : ℚ) * x ^ 5 + 32 * x ^ 3 + (32 / 5 : ℚ) * x + 1) (N : ℚ) +
    ((∑ b ∈ box N 6, if (∀ i, 0 < b i) then
      (if cyc N b then ∏ i, w2 (b i) else 0) else 0 : ℕ) : ℚ) := by
  rw [W_split, Fin.sum_univ_six, piece_rot w2 N 0, piece_rot w2 N 1, piece_rot w2 N 2, piece_rot w2 N 3, piece_rot w2 N 4, piece_rot w2 N 5, piece_cons_0 w2 N, piece_cons_1 w2 N, piece_cons_2 w2 N, piece_cons_3 w2 N, piece_cons_4 w2 N, piece_cons_5 w2 N]
  push_cast
  rw [PE_FFFFF N 0 (Nat.zero_le N), PE_FFFFT N 0 (Nat.zero_le N), PE_FFFTT N 0 (Nat.zero_le N), PE_FFTTT N 0 (Nat.zero_le N), PE_FTTTT N 0 (Nat.zero_le N), PE_TTTTT N 0 (Nat.zero_le N)]
  simp only [w2_zero]
  beta_reduce
  push_cast
  ring

/-! ## Path values, weight `w1` -/

lemma PO_nil (N : ℕ) : ∀ p ≤ N, (PSl N w1 [] p : ℚ) = (fun _ => 1) (p : ℚ) := PSl_nil N w1

lemma PO_T (N : ℕ) : ∀ p ≤ N, (PSl N w1 [true] p : ℚ) = (fun x : ℚ =>
      -x + (N : ℚ)) (p : ℚ) := by
  intro p hp
  rw [layerT N w1 1 w1_succ []
    (fun _ => 1)
    (PO_nil N)
    (fun x : ℚ => x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PO_F (N : ℕ) : ∀ p ≤ N, (PSl N w1 [false] p : ℚ) = (fun x : ℚ =>
      -x + (N : ℚ) + 1) (p : ℚ) := by
  intro p hp
  rw [layerF N w1 w1_zero 1 w1_succ []
    (fun _ => 1)
    (PO_nil N)
    (fun x : ℚ => x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PO_FT (N : ℕ) : ∀ p ≤ N, (PSl N w1 [false, true] p : ℚ) = (fun x : ℚ =>
      -(1 / 2 : ℚ) * x ^ 2 + (1 / 2 : ℚ) * x + (1 / 2 : ℚ) * (N : ℚ) ^ 2 + (1 / 2 : ℚ) * (N : ℚ)) (p : ℚ) := by
  intro p hp
  rw [layerF N w1 w1_zero 1 w1_succ [true]
    (fun x : ℚ => -x + (N : ℚ))
    (PO_T N)
    (fun x : ℚ => -(1 / 2 : ℚ) * x ^ 2 + x * (N : ℚ) - (1 / 2 : ℚ) * x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PO_FF (N : ℕ) : ∀ p ≤ N, (PSl N w1 [false, false] p : ℚ) = (fun x : ℚ =>
      -(1 / 2 : ℚ) * x ^ 2 - (1 / 2 : ℚ) * x + (1 / 2 : ℚ) * (N : ℚ) ^ 2 + (3 / 2 : ℚ) * (N : ℚ) + 1) (p : ℚ) := by
  intro p hp
  rw [layerF N w1 w1_zero 1 w1_succ [false]
    (fun x : ℚ => -x + (N : ℚ) + 1)
    (PO_F N)
    (fun x : ℚ => -(1 / 2 : ℚ) * x ^ 2 + x * (N : ℚ) + (1 / 2 : ℚ) * x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PO_TT (N : ℕ) : ∀ p ≤ N, (PSl N w1 [true, true] p : ℚ) = (fun x : ℚ =>
      -(1 / 2 : ℚ) * x ^ 2 + (1 / 2 : ℚ) * x + (1 / 2 : ℚ) * (N : ℚ) ^ 2 - (1 / 2 : ℚ) * (N : ℚ)) (p : ℚ) := by
  intro p hp
  rw [layerT N w1 1 w1_succ [true]
    (fun x : ℚ => -x + (N : ℚ))
    (PO_T N)
    (fun x : ℚ => -(1 / 2 : ℚ) * x ^ 2 + x * (N : ℚ) - (1 / 2 : ℚ) * x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PO_FFT (N : ℕ) : ∀ p ≤ N, (PSl N w1 [false, false, true] p : ℚ) = (fun x : ℚ =>
      (1 / 6 : ℚ) * x ^ 3 - (1 / 2 : ℚ) * x ^ 2 * (N : ℚ) - (1 / 2 : ℚ) * x * (N : ℚ) - (1 / 6 : ℚ) * x
      + (1 / 3 : ℚ) * (N : ℚ) ^ 3 + (N : ℚ) ^ 2 + (2 / 3 : ℚ) * (N : ℚ)) (p : ℚ) := by
  intro p hp
  rw [layerF N w1 w1_zero 1 w1_succ [false, true]
    (fun x : ℚ => -(1 / 2 : ℚ) * x ^ 2 + (1 / 2 : ℚ) * x + (1 / 2 : ℚ) * (N : ℚ) ^ 2 + (1 / 2 : ℚ) * (N : ℚ))
    (PO_FT N)
    (fun x : ℚ => -(1 / 6 : ℚ) * x ^ 3 + (1 / 2 : ℚ) * x * (N : ℚ) ^ 2 + (1 / 2 : ℚ) * x * (N : ℚ) + (1 / 6 : ℚ) * x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PO_FFF (N : ℕ) : ∀ p ≤ N, (PSl N w1 [false, false, false] p : ℚ) = (fun x : ℚ =>
      (1 / 6 : ℚ) * x ^ 3 - (1 / 2 : ℚ) * x ^ 2 * (N : ℚ) - (1 / 2 : ℚ) * x ^ 2 - (1 / 2 : ℚ) * x * (N : ℚ)
      - (2 / 3 : ℚ) * x + (1 / 3 : ℚ) * (N : ℚ) ^ 3 + (3 / 2 : ℚ) * (N : ℚ) ^ 2 + (13 / 6 : ℚ) * (N : ℚ)
      + 1) (p : ℚ) := by
  intro p hp
  rw [layerF N w1 w1_zero 1 w1_succ [false, false]
    (fun x : ℚ => -(1 / 2 : ℚ) * x ^ 2 - (1 / 2 : ℚ) * x + (1 / 2 : ℚ) * (N : ℚ) ^ 2 + (3 / 2 : ℚ) * (N : ℚ)
        + 1)
    (PO_FF N)
    (fun x : ℚ => -(1 / 6 : ℚ) * x ^ 3 - (1 / 2 : ℚ) * x ^ 2 + (1 / 2 : ℚ) * x * (N : ℚ) ^ 2 + (3 / 2 : ℚ) * x * (N : ℚ)
        + (2 / 3 : ℚ) * x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PO_FTT (N : ℕ) : ∀ p ≤ N, (PSl N w1 [false, true, true] p : ℚ) = (fun x : ℚ =>
      (1 / 6 : ℚ) * x ^ 3 - (1 / 2 : ℚ) * x ^ 2 * (N : ℚ) + (1 / 2 : ℚ) * x * (N : ℚ) - (1 / 6 : ℚ) * x
      + (1 / 3 : ℚ) * (N : ℚ) ^ 3 - (1 / 3 : ℚ) * (N : ℚ)) (p : ℚ) := by
  intro p hp
  rw [layerF N w1 w1_zero 1 w1_succ [true, true]
    (fun x : ℚ => -(1 / 2 : ℚ) * x ^ 2 + (1 / 2 : ℚ) * x + (1 / 2 : ℚ) * (N : ℚ) ^ 2 - (1 / 2 : ℚ) * (N : ℚ))
    (PO_TT N)
    (fun x : ℚ => -(1 / 6 : ℚ) * x ^ 3 + (1 / 2 : ℚ) * x * (N : ℚ) ^ 2 - (1 / 2 : ℚ) * x * (N : ℚ) + (1 / 6 : ℚ) * x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PO_TTT (N : ℕ) : ∀ p ≤ N, (PSl N w1 [true, true, true] p : ℚ) = (fun x : ℚ =>
      (1 / 6 : ℚ) * x ^ 3 - (1 / 2 : ℚ) * x ^ 2 * (N : ℚ) + (1 / 2 : ℚ) * x * (N : ℚ) - (1 / 6 : ℚ) * x
      + (1 / 3 : ℚ) * (N : ℚ) ^ 3 - (1 / 2 : ℚ) * (N : ℚ) ^ 2 + (1 / 6 : ℚ) * (N : ℚ)) (p : ℚ) := by
  intro p hp
  rw [layerT N w1 1 w1_succ [true, true]
    (fun x : ℚ => -(1 / 2 : ℚ) * x ^ 2 + (1 / 2 : ℚ) * x + (1 / 2 : ℚ) * (N : ℚ) ^ 2 - (1 / 2 : ℚ) * (N : ℚ))
    (PO_TT N)
    (fun x : ℚ => -(1 / 6 : ℚ) * x ^ 3 + (1 / 2 : ℚ) * x * (N : ℚ) ^ 2 - (1 / 2 : ℚ) * x * (N : ℚ) + (1 / 6 : ℚ) * x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PO_FFTT (N : ℕ) : ∀ p ≤ N, (PSl N w1 [false, false, true, true] p : ℚ) = (fun x : ℚ =>
      (1 / 24 : ℚ) * x ^ 4 - (1 / 12 : ℚ) * x ^ 3 - (1 / 4 : ℚ) * x ^ 2 * (N : ℚ) ^ 2 + (1 / 4 : ℚ) * x ^ 2 * (N : ℚ)
      - (1 / 24 : ℚ) * x ^ 2 - (1 / 4 : ℚ) * x * (N : ℚ) ^ 2 + (1 / 4 : ℚ) * x * (N : ℚ) + (1 / 12 : ℚ) * x
      + (5 / 24 : ℚ) * (N : ℚ) ^ 4 + (5 / 12 : ℚ) * (N : ℚ) ^ 3 - (5 / 24 : ℚ) * (N : ℚ) ^ 2 - (5 / 12 : ℚ) * (N : ℚ)) (p : ℚ) := by
  intro p hp
  rw [layerF N w1 w1_zero 1 w1_succ [false, true, true]
    (fun x : ℚ => (1 / 6 : ℚ) * x ^ 3 - (1 / 2 : ℚ) * x ^ 2 * (N : ℚ) + (1 / 2 : ℚ) * x * (N : ℚ) - (1 / 6 : ℚ) * x
        + (1 / 3 : ℚ) * (N : ℚ) ^ 3 - (1 / 3 : ℚ) * (N : ℚ))
    (PO_FTT N)
    (fun x : ℚ => (1 / 24 : ℚ) * x ^ 4 - (1 / 6 : ℚ) * x ^ 3 * (N : ℚ) + (1 / 12 : ℚ) * x ^ 3 - (1 / 24 : ℚ) * x ^ 2
        + (1 / 3 : ℚ) * x * (N : ℚ) ^ 3 - (1 / 6 : ℚ) * x * (N : ℚ) - (1 / 12 : ℚ) * x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PO_TTTT (N : ℕ) : ∀ p ≤ N, (PSl N w1 [true, true, true, true] p : ℚ) = (fun x : ℚ =>
      (1 / 24 : ℚ) * x ^ 4 - (1 / 12 : ℚ) * x ^ 3 - (1 / 4 : ℚ) * x ^ 2 * (N : ℚ) ^ 2 + (1 / 4 : ℚ) * x ^ 2 * (N : ℚ)
      - (1 / 24 : ℚ) * x ^ 2 + (1 / 4 : ℚ) * x * (N : ℚ) ^ 2 - (1 / 4 : ℚ) * x * (N : ℚ) + (1 / 12 : ℚ) * x
      + (5 / 24 : ℚ) * (N : ℚ) ^ 4 - (5 / 12 : ℚ) * (N : ℚ) ^ 3 + (7 / 24 : ℚ) * (N : ℚ) ^ 2 - (1 / 12 : ℚ) * (N : ℚ)) (p : ℚ) := by
  intro p hp
  rw [layerT N w1 1 w1_succ [true, true, true]
    (fun x : ℚ => (1 / 6 : ℚ) * x ^ 3 - (1 / 2 : ℚ) * x ^ 2 * (N : ℚ) + (1 / 2 : ℚ) * x * (N : ℚ) - (1 / 6 : ℚ) * x
        + (1 / 3 : ℚ) * (N : ℚ) ^ 3 - (1 / 2 : ℚ) * (N : ℚ) ^ 2 + (1 / 6 : ℚ) * (N : ℚ))
    (PO_TTT N)
    (fun x : ℚ => (1 / 24 : ℚ) * x ^ 4 - (1 / 6 : ℚ) * x ^ 3 * (N : ℚ) + (1 / 12 : ℚ) * x ^ 3 - (1 / 24 : ℚ) * x ^ 2
        + (1 / 3 : ℚ) * x * (N : ℚ) ^ 3 - (1 / 2 : ℚ) * x * (N : ℚ) ^ 2 + (1 / 3 : ℚ) * x * (N : ℚ)
        - (1 / 12 : ℚ) * x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PO_FFFT (N : ℕ) : ∀ p ≤ N, (PSl N w1 [false, false, false, true] p : ℚ) = (fun x : ℚ =>
      (1 / 24 : ℚ) * x ^ 4 - (1 / 12 : ℚ) * x ^ 3 - (1 / 4 : ℚ) * x ^ 2 * (N : ℚ) ^ 2 - (1 / 4 : ℚ) * x ^ 2 * (N : ℚ)
      - (1 / 24 : ℚ) * x ^ 2 - (1 / 4 : ℚ) * x * (N : ℚ) ^ 2 - (1 / 4 : ℚ) * x * (N : ℚ) + (1 / 12 : ℚ) * x
      + (5 / 24 : ℚ) * (N : ℚ) ^ 4 + (11 / 12 : ℚ) * (N : ℚ) ^ 3 + (31 / 24 : ℚ) * (N : ℚ) ^ 2 + (7 / 12 : ℚ) * (N : ℚ)) (p : ℚ) := by
  intro p hp
  rw [layerF N w1 w1_zero 1 w1_succ [false, false, true]
    (fun x : ℚ => (1 / 6 : ℚ) * x ^ 3 - (1 / 2 : ℚ) * x ^ 2 * (N : ℚ) - (1 / 2 : ℚ) * x * (N : ℚ) - (1 / 6 : ℚ) * x
        + (1 / 3 : ℚ) * (N : ℚ) ^ 3 + (N : ℚ) ^ 2 + (2 / 3 : ℚ) * (N : ℚ))
    (PO_FFT N)
    (fun x : ℚ => (1 / 24 : ℚ) * x ^ 4 - (1 / 6 : ℚ) * x ^ 3 * (N : ℚ) + (1 / 12 : ℚ) * x ^ 3 - (1 / 2 : ℚ) * x ^ 2 * (N : ℚ)
        - (1 / 24 : ℚ) * x ^ 2 + (1 / 3 : ℚ) * x * (N : ℚ) ^ 3 + x * (N : ℚ) ^ 2 + (1 / 3 : ℚ) * x * (N : ℚ)
        - (1 / 12 : ℚ) * x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PO_FTTT (N : ℕ) : ∀ p ≤ N, (PSl N w1 [false, true, true, true] p : ℚ) = (fun x : ℚ =>
      (1 / 24 : ℚ) * x ^ 4 - (1 / 12 : ℚ) * x ^ 3 - (1 / 4 : ℚ) * x ^ 2 * (N : ℚ) ^ 2 + (1 / 4 : ℚ) * x ^ 2 * (N : ℚ)
      - (1 / 24 : ℚ) * x ^ 2 + (1 / 4 : ℚ) * x * (N : ℚ) ^ 2 - (1 / 4 : ℚ) * x * (N : ℚ) + (1 / 12 : ℚ) * x
      + (5 / 24 : ℚ) * (N : ℚ) ^ 4 - (1 / 12 : ℚ) * (N : ℚ) ^ 3 - (5 / 24 : ℚ) * (N : ℚ) ^ 2 + (1 / 12 : ℚ) * (N : ℚ)) (p : ℚ) := by
  intro p hp
  rw [layerF N w1 w1_zero 1 w1_succ [true, true, true]
    (fun x : ℚ => (1 / 6 : ℚ) * x ^ 3 - (1 / 2 : ℚ) * x ^ 2 * (N : ℚ) + (1 / 2 : ℚ) * x * (N : ℚ) - (1 / 6 : ℚ) * x
        + (1 / 3 : ℚ) * (N : ℚ) ^ 3 - (1 / 2 : ℚ) * (N : ℚ) ^ 2 + (1 / 6 : ℚ) * (N : ℚ))
    (PO_TTT N)
    (fun x : ℚ => (1 / 24 : ℚ) * x ^ 4 - (1 / 6 : ℚ) * x ^ 3 * (N : ℚ) + (1 / 12 : ℚ) * x ^ 3 - (1 / 24 : ℚ) * x ^ 2
        + (1 / 3 : ℚ) * x * (N : ℚ) ^ 3 - (1 / 2 : ℚ) * x * (N : ℚ) ^ 2 + (1 / 3 : ℚ) * x * (N : ℚ)
        - (1 / 12 : ℚ) * x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PO_FFFF (N : ℕ) : ∀ p ≤ N, (PSl N w1 [false, false, false, false] p : ℚ) = (fun x : ℚ =>
      (1 / 24 : ℚ) * x ^ 4 + (1 / 12 : ℚ) * x ^ 3 - (1 / 4 : ℚ) * x ^ 2 * (N : ℚ) ^ 2 - (3 / 4 : ℚ) * x ^ 2 * (N : ℚ)
      - (13 / 24 : ℚ) * x ^ 2 - (1 / 4 : ℚ) * x * (N : ℚ) ^ 2 - (3 / 4 : ℚ) * x * (N : ℚ) - (7 / 12 : ℚ) * x
      + (5 / 24 : ℚ) * (N : ℚ) ^ 4 + (5 / 4 : ℚ) * (N : ℚ) ^ 3 + (67 / 24 : ℚ) * (N : ℚ) ^ 2 + (11 / 4 : ℚ) * (N : ℚ)
      + 1) (p : ℚ) := by
  intro p hp
  rw [layerF N w1 w1_zero 1 w1_succ [false, false, false]
    (fun x : ℚ => (1 / 6 : ℚ) * x ^ 3 - (1 / 2 : ℚ) * x ^ 2 * (N : ℚ) - (1 / 2 : ℚ) * x ^ 2 - (1 / 2 : ℚ) * x * (N : ℚ)
        - (2 / 3 : ℚ) * x + (1 / 3 : ℚ) * (N : ℚ) ^ 3 + (3 / 2 : ℚ) * (N : ℚ) ^ 2 + (13 / 6 : ℚ) * (N : ℚ)
        + 1)
    (PO_FFF N)
    (fun x : ℚ => (1 / 24 : ℚ) * x ^ 4 - (1 / 6 : ℚ) * x ^ 3 * (N : ℚ) - (1 / 12 : ℚ) * x ^ 3 - (1 / 2 : ℚ) * x ^ 2 * (N : ℚ)
        - (13 / 24 : ℚ) * x ^ 2 + (1 / 3 : ℚ) * x * (N : ℚ) ^ 3 + (3 / 2 : ℚ) * x * (N : ℚ) ^ 2 + (11 / 6 : ℚ) * x * (N : ℚ)
        + (7 / 12 : ℚ) * x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PO_FFFFF (N : ℕ) : ∀ p ≤ N, (PSl N w1 [false, false, false, false, false] p : ℚ) = (fun x : ℚ =>
      -(1 / 120 : ℚ) * x ^ 5 + (1 / 24 : ℚ) * x ^ 4 * (N : ℚ) + (1 / 24 : ℚ) * x ^ 4 + (1 / 12 : ℚ) * x ^ 3 * (N : ℚ)
      + (1 / 8 : ℚ) * x ^ 3 - (1 / 6 : ℚ) * x ^ 2 * (N : ℚ) ^ 3 - (3 / 4 : ℚ) * x ^ 2 * (N : ℚ) ^ 2
      - (9 / 8 : ℚ) * x ^ 2 * (N : ℚ) - (13 / 24 : ℚ) * x ^ 2 - (1 / 6 : ℚ) * x * (N : ℚ) ^ 3 - (3 / 4 : ℚ) * x * (N : ℚ) ^ 2
      - (7 / 6 : ℚ) * x * (N : ℚ) - (37 / 60 : ℚ) * x + (2 / 15 : ℚ) * (N : ℚ) ^ 5 + (N : ℚ) ^ 4 + 3 * (N : ℚ) ^ 3
      + (9 / 2 : ℚ) * (N : ℚ) ^ 2 + (101 / 30 : ℚ) * (N : ℚ) + 1) (p : ℚ) := by
  intro p hp
  rw [layerF N w1 w1_zero 1 w1_succ [false, false, false, false]
    (fun x : ℚ => (1 / 24 : ℚ) * x ^ 4 + (1 / 12 : ℚ) * x ^ 3 - (1 / 4 : ℚ) * x ^ 2 * (N : ℚ) ^ 2 - (3 / 4 : ℚ) * x ^ 2 * (N : ℚ)
        - (13 / 24 : ℚ) * x ^ 2 - (1 / 4 : ℚ) * x * (N : ℚ) ^ 2 - (3 / 4 : ℚ) * x * (N : ℚ) - (7 / 12 : ℚ) * x
        + (5 / 24 : ℚ) * (N : ℚ) ^ 4 + (5 / 4 : ℚ) * (N : ℚ) ^ 3 + (67 / 24 : ℚ) * (N : ℚ) ^ 2 + (11 / 4 : ℚ) * (N : ℚ)
        + 1)
    (PO_FFFF N)
    (fun x : ℚ => (1 / 120 : ℚ) * x ^ 5 + (1 / 24 : ℚ) * x ^ 4 - (1 / 12 : ℚ) * x ^ 3 * (N : ℚ) ^ 2 - (1 / 4 : ℚ) * x ^ 3 * (N : ℚ)
        - (1 / 8 : ℚ) * x ^ 3 - (1 / 4 : ℚ) * x ^ 2 * (N : ℚ) ^ 2 - (3 / 4 : ℚ) * x ^ 2 * (N : ℚ)
        - (13 / 24 : ℚ) * x ^ 2 + (5 / 24 : ℚ) * x * (N : ℚ) ^ 4 + (5 / 4 : ℚ) * x * (N : ℚ) ^ 3 + (21 / 8 : ℚ) * x * (N : ℚ) ^ 2
        + (9 / 4 : ℚ) * x * (N : ℚ) + (37 / 60 : ℚ) * x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PO_FTTTT (N : ℕ) : ∀ p ≤ N, (PSl N w1 [false, true, true, true, true] p : ℚ) = (fun x : ℚ =>
      -(1 / 120 : ℚ) * x ^ 5 + (1 / 24 : ℚ) * x ^ 4 * (N : ℚ) - (1 / 12 : ℚ) * x ^ 3 * (N : ℚ) + (1 / 24 : ℚ) * x ^ 3
      - (1 / 6 : ℚ) * x ^ 2 * (N : ℚ) ^ 3 + (1 / 4 : ℚ) * x ^ 2 * (N : ℚ) ^ 2 - (1 / 8 : ℚ) * x ^ 2 * (N : ℚ)
      + (1 / 6 : ℚ) * x * (N : ℚ) ^ 3 - (1 / 4 : ℚ) * x * (N : ℚ) ^ 2 + (1 / 6 : ℚ) * x * (N : ℚ)
      - (1 / 30 : ℚ) * x + (2 / 15 : ℚ) * (N : ℚ) ^ 5 - (1 / 8 : ℚ) * (N : ℚ) ^ 4 - (1 / 12 : ℚ) * (N : ℚ) ^ 3
      + (1 / 8 : ℚ) * (N : ℚ) ^ 2 - (1 / 20 : ℚ) * (N : ℚ)) (p : ℚ) := by
  intro p hp
  rw [layerF N w1 w1_zero 1 w1_succ [true, true, true, true]
    (fun x : ℚ => (1 / 24 : ℚ) * x ^ 4 - (1 / 12 : ℚ) * x ^ 3 - (1 / 4 : ℚ) * x ^ 2 * (N : ℚ) ^ 2 + (1 / 4 : ℚ) * x ^ 2 * (N : ℚ)
        - (1 / 24 : ℚ) * x ^ 2 + (1 / 4 : ℚ) * x * (N : ℚ) ^ 2 - (1 / 4 : ℚ) * x * (N : ℚ) + (1 / 12 : ℚ) * x
        + (5 / 24 : ℚ) * (N : ℚ) ^ 4 - (5 / 12 : ℚ) * (N : ℚ) ^ 3 + (7 / 24 : ℚ) * (N : ℚ) ^ 2 - (1 / 12 : ℚ) * (N : ℚ))
    (PO_TTTT N)
    (fun x : ℚ => (1 / 120 : ℚ) * x ^ 5 - (1 / 12 : ℚ) * x ^ 3 * (N : ℚ) ^ 2 + (1 / 12 : ℚ) * x ^ 3 * (N : ℚ)
        - (1 / 24 : ℚ) * x ^ 3 + (5 / 24 : ℚ) * x * (N : ℚ) ^ 4 - (5 / 12 : ℚ) * x * (N : ℚ) ^ 3 + (3 / 8 : ℚ) * x * (N : ℚ) ^ 2
        - (1 / 6 : ℚ) * x * (N : ℚ) + (1 / 30 : ℚ) * x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PO_TTTTT (N : ℕ) : ∀ p ≤ N, (PSl N w1 [true, true, true, true, true] p : ℚ) = (fun x : ℚ =>
      -(1 / 120 : ℚ) * x ^ 5 + (1 / 24 : ℚ) * x ^ 4 * (N : ℚ) - (1 / 12 : ℚ) * x ^ 3 * (N : ℚ) + (1 / 24 : ℚ) * x ^ 3
      - (1 / 6 : ℚ) * x ^ 2 * (N : ℚ) ^ 3 + (1 / 4 : ℚ) * x ^ 2 * (N : ℚ) ^ 2 - (1 / 8 : ℚ) * x ^ 2 * (N : ℚ)
      + (1 / 6 : ℚ) * x * (N : ℚ) ^ 3 - (1 / 4 : ℚ) * x * (N : ℚ) ^ 2 + (1 / 6 : ℚ) * x * (N : ℚ)
      - (1 / 30 : ℚ) * x + (2 / 15 : ℚ) * (N : ℚ) ^ 5 - (1 / 3 : ℚ) * (N : ℚ) ^ 4 + (1 / 3 : ℚ) * (N : ℚ) ^ 3
      - (1 / 6 : ℚ) * (N : ℚ) ^ 2 + (1 / 30 : ℚ) * (N : ℚ)) (p : ℚ) := by
  intro p hp
  rw [layerT N w1 1 w1_succ [true, true, true, true]
    (fun x : ℚ => (1 / 24 : ℚ) * x ^ 4 - (1 / 12 : ℚ) * x ^ 3 - (1 / 4 : ℚ) * x ^ 2 * (N : ℚ) ^ 2 + (1 / 4 : ℚ) * x ^ 2 * (N : ℚ)
        - (1 / 24 : ℚ) * x ^ 2 + (1 / 4 : ℚ) * x * (N : ℚ) ^ 2 - (1 / 4 : ℚ) * x * (N : ℚ) + (1 / 12 : ℚ) * x
        + (5 / 24 : ℚ) * (N : ℚ) ^ 4 - (5 / 12 : ℚ) * (N : ℚ) ^ 3 + (7 / 24 : ℚ) * (N : ℚ) ^ 2 - (1 / 12 : ℚ) * (N : ℚ))
    (PO_TTTT N)
    (fun x : ℚ => (1 / 120 : ℚ) * x ^ 5 - (1 / 12 : ℚ) * x ^ 3 * (N : ℚ) ^ 2 + (1 / 12 : ℚ) * x ^ 3 * (N : ℚ)
        - (1 / 24 : ℚ) * x ^ 3 + (5 / 24 : ℚ) * x * (N : ℚ) ^ 4 - (5 / 12 : ℚ) * x * (N : ℚ) ^ 3 + (3 / 8 : ℚ) * x * (N : ℚ) ^ 2
        - (1 / 6 : ℚ) * x * (N : ℚ) + (1 / 30 : ℚ) * x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PO_FFTTT (N : ℕ) : ∀ p ≤ N, (PSl N w1 [false, false, true, true, true] p : ℚ) = (fun x : ℚ =>
      -(1 / 120 : ℚ) * x ^ 5 + (1 / 24 : ℚ) * x ^ 4 * (N : ℚ) - (1 / 12 : ℚ) * x ^ 3 * (N : ℚ) + (1 / 24 : ℚ) * x ^ 3
      - (1 / 6 : ℚ) * x ^ 2 * (N : ℚ) ^ 3 + (1 / 4 : ℚ) * x ^ 2 * (N : ℚ) ^ 2 - (1 / 8 : ℚ) * x ^ 2 * (N : ℚ)
      - (1 / 6 : ℚ) * x * (N : ℚ) ^ 3 + (1 / 4 : ℚ) * x * (N : ℚ) ^ 2 - (1 / 30 : ℚ) * x + (2 / 15 : ℚ) * (N : ℚ) ^ 5
      + (5 / 24 : ℚ) * (N : ℚ) ^ 4 - (1 / 4 : ℚ) * (N : ℚ) ^ 3 - (5 / 24 : ℚ) * (N : ℚ) ^ 2 + (7 / 60 : ℚ) * (N : ℚ)) (p : ℚ) := by
  intro p hp
  rw [layerF N w1 w1_zero 1 w1_succ [false, true, true, true]
    (fun x : ℚ => (1 / 24 : ℚ) * x ^ 4 - (1 / 12 : ℚ) * x ^ 3 - (1 / 4 : ℚ) * x ^ 2 * (N : ℚ) ^ 2 + (1 / 4 : ℚ) * x ^ 2 * (N : ℚ)
        - (1 / 24 : ℚ) * x ^ 2 + (1 / 4 : ℚ) * x * (N : ℚ) ^ 2 - (1 / 4 : ℚ) * x * (N : ℚ) + (1 / 12 : ℚ) * x
        + (5 / 24 : ℚ) * (N : ℚ) ^ 4 - (1 / 12 : ℚ) * (N : ℚ) ^ 3 - (5 / 24 : ℚ) * (N : ℚ) ^ 2 + (1 / 12 : ℚ) * (N : ℚ))
    (PO_FTTT N)
    (fun x : ℚ => (1 / 120 : ℚ) * x ^ 5 - (1 / 12 : ℚ) * x ^ 3 * (N : ℚ) ^ 2 + (1 / 12 : ℚ) * x ^ 3 * (N : ℚ)
        - (1 / 24 : ℚ) * x ^ 3 + (5 / 24 : ℚ) * x * (N : ℚ) ^ 4 - (1 / 12 : ℚ) * x * (N : ℚ) ^ 3 - (1 / 8 : ℚ) * x * (N : ℚ) ^ 2
        + (1 / 30 : ℚ) * x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PO_FFFTT (N : ℕ) : ∀ p ≤ N, (PSl N w1 [false, false, false, true, true] p : ℚ) = (fun x : ℚ =>
      -(1 / 120 : ℚ) * x ^ 5 + (1 / 24 : ℚ) * x ^ 4 * (N : ℚ) - (1 / 12 : ℚ) * x ^ 3 * (N : ℚ) + (1 / 24 : ℚ) * x ^ 3
      - (1 / 6 : ℚ) * x ^ 2 * (N : ℚ) ^ 3 + (1 / 8 : ℚ) * x ^ 2 * (N : ℚ) - (1 / 6 : ℚ) * x * (N : ℚ) ^ 3
      + (1 / 4 : ℚ) * x * (N : ℚ) - (1 / 30 : ℚ) * x + (2 / 15 : ℚ) * (N : ℚ) ^ 5 + (11 / 24 : ℚ) * (N : ℚ) ^ 4
      + (1 / 4 : ℚ) * (N : ℚ) ^ 3 - (11 / 24 : ℚ) * (N : ℚ) ^ 2 - (23 / 60 : ℚ) * (N : ℚ)) (p : ℚ) := by
  intro p hp
  rw [layerF N w1 w1_zero 1 w1_succ [false, false, true, true]
    (fun x : ℚ => (1 / 24 : ℚ) * x ^ 4 - (1 / 12 : ℚ) * x ^ 3 - (1 / 4 : ℚ) * x ^ 2 * (N : ℚ) ^ 2 + (1 / 4 : ℚ) * x ^ 2 * (N : ℚ)
        - (1 / 24 : ℚ) * x ^ 2 - (1 / 4 : ℚ) * x * (N : ℚ) ^ 2 + (1 / 4 : ℚ) * x * (N : ℚ) + (1 / 12 : ℚ) * x
        + (5 / 24 : ℚ) * (N : ℚ) ^ 4 + (5 / 12 : ℚ) * (N : ℚ) ^ 3 - (5 / 24 : ℚ) * (N : ℚ) ^ 2 - (5 / 12 : ℚ) * (N : ℚ))
    (PO_FFTT N)
    (fun x : ℚ => (1 / 120 : ℚ) * x ^ 5 - (1 / 12 : ℚ) * x ^ 3 * (N : ℚ) ^ 2 + (1 / 12 : ℚ) * x ^ 3 * (N : ℚ)
        - (1 / 24 : ℚ) * x ^ 3 - (1 / 4 : ℚ) * x ^ 2 * (N : ℚ) ^ 2 + (1 / 4 : ℚ) * x ^ 2 * (N : ℚ)
        + (5 / 24 : ℚ) * x * (N : ℚ) ^ 4 + (5 / 12 : ℚ) * x * (N : ℚ) ^ 3 - (3 / 8 : ℚ) * x * (N : ℚ) ^ 2
        - (1 / 4 : ℚ) * x * (N : ℚ) + (1 / 30 : ℚ) * x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

lemma PO_FFFFT (N : ℕ) : ∀ p ≤ N, (PSl N w1 [false, false, false, false, true] p : ℚ) = (fun x : ℚ =>
      -(1 / 120 : ℚ) * x ^ 5 + (1 / 24 : ℚ) * x ^ 4 * (N : ℚ) + (1 / 12 : ℚ) * x ^ 3 * (N : ℚ) + (1 / 24 : ℚ) * x ^ 3
      - (1 / 6 : ℚ) * x ^ 2 * (N : ℚ) ^ 3 - (1 / 2 : ℚ) * x ^ 2 * (N : ℚ) ^ 2 - (3 / 8 : ℚ) * x ^ 2 * (N : ℚ)
      - (1 / 6 : ℚ) * x * (N : ℚ) ^ 3 - (1 / 2 : ℚ) * x * (N : ℚ) ^ 2 - (5 / 12 : ℚ) * x * (N : ℚ)
      - (1 / 30 : ℚ) * x + (2 / 15 : ℚ) * (N : ℚ) ^ 5 + (19 / 24 : ℚ) * (N : ℚ) ^ 4 + (7 / 4 : ℚ) * (N : ℚ) ^ 3
      + (41 / 24 : ℚ) * (N : ℚ) ^ 2 + (37 / 60 : ℚ) * (N : ℚ)) (p : ℚ) := by
  intro p hp
  rw [layerF N w1 w1_zero 1 w1_succ [false, false, false, true]
    (fun x : ℚ => (1 / 24 : ℚ) * x ^ 4 - (1 / 12 : ℚ) * x ^ 3 - (1 / 4 : ℚ) * x ^ 2 * (N : ℚ) ^ 2 - (1 / 4 : ℚ) * x ^ 2 * (N : ℚ)
        - (1 / 24 : ℚ) * x ^ 2 - (1 / 4 : ℚ) * x * (N : ℚ) ^ 2 - (1 / 4 : ℚ) * x * (N : ℚ) + (1 / 12 : ℚ) * x
        + (5 / 24 : ℚ) * (N : ℚ) ^ 4 + (11 / 12 : ℚ) * (N : ℚ) ^ 3 + (31 / 24 : ℚ) * (N : ℚ) ^ 2 + (7 / 12 : ℚ) * (N : ℚ))
    (PO_FFFT N)
    (fun x : ℚ => (1 / 120 : ℚ) * x ^ 5 - (1 / 12 : ℚ) * x ^ 3 * (N : ℚ) ^ 2 - (1 / 12 : ℚ) * x ^ 3 * (N : ℚ)
        - (1 / 24 : ℚ) * x ^ 3 - (1 / 4 : ℚ) * x ^ 2 * (N : ℚ) ^ 2 - (1 / 4 : ℚ) * x ^ 2 * (N : ℚ)
        + (5 / 24 : ℚ) * x * (N : ℚ) ^ 4 + (11 / 12 : ℚ) * x * (N : ℚ) ^ 3 + (9 / 8 : ℚ) * x * (N : ℚ) ^ 2
        + (5 / 12 : ℚ) * x * (N : ℚ) + (1 / 30 : ℚ) * x)
    (by beta_reduce; ring) (fun x => by beta_reduce; ring) p hp]
  beta_reduce
  ring

open Classical in
lemma W_O (N : ℕ) : (W w1 N : ℚ) = (fun x : ℚ =>
      (4 / 5 : ℚ) * x ^ 5 + 2 * x ^ 4 + 5 * x ^ 3 + (11 / 2 : ℚ) * x ^ 2 + (37 / 10 : ℚ) * x + 1) (N : ℚ) +
    ((∑ b ∈ box N 6, if (∀ i, 0 < b i) then
      (if cyc N b then ∏ i, w1 (b i) else 0) else 0 : ℕ) : ℚ) := by
  rw [W_split, Fin.sum_univ_six, piece_rot w1 N 0, piece_rot w1 N 1, piece_rot w1 N 2, piece_rot w1 N 3, piece_rot w1 N 4, piece_rot w1 N 5, piece_cons_0 w1 N, piece_cons_1 w1 N, piece_cons_2 w1 N, piece_cons_3 w1 N, piece_cons_4 w1 N, piece_cons_5 w1 N]
  push_cast
  rw [PO_FFFFF N 0 (Nat.zero_le N), PO_FFFFT N 0 (Nat.zero_le N), PO_FFFTT N 0 (Nat.zero_le N), PO_FFTTT N 0 (Nat.zero_le N), PO_FTTTT N 0 (Nat.zero_le N), PO_TTTTT N 0 (Nat.zero_le N)]
  simp only [w1_zero]
  beta_reduce
  push_cast
  ring

/-! ## Telescoping in the bound -/

lemma WE_small (N : ℕ) (hN : N ≤ 1) : (W w2 N : ℚ) = (fun x : ℚ =>
      (128 / 5 : ℚ) * x ^ 5 + 32 * x ^ 3 + (32 / 5 : ℚ) * x + 1) (N : ℚ) := by
  rw [W_E, pos_small w2 N hN]
  simp

lemma WE_succ2 (N : ℕ) : (W w2 (N + 2) : ℚ) = (fun x : ℚ =>
      (128 / 5 : ℚ) * x ^ 5 + 32 * x ^ 3 + (32 / 5 : ℚ) * x + 1) ((N + 2 : ℕ) : ℚ) + 2 ^ 6 * W w1 N := by
  rw [W_E, pos_shift w2 2 (fun c => by simp [w2]) N]
  push_cast
  ring

lemma WO_small (N : ℕ) (hN : N ≤ 1) : (W w1 N : ℚ) = (fun x : ℚ =>
      (4 / 5 : ℚ) * x ^ 5 + 2 * x ^ 4 + 5 * x ^ 3 + (11 / 2 : ℚ) * x ^ 2 + (37 / 10 : ℚ) * x + 1) (N : ℚ) := by
  rw [W_O, pos_small w1 N hN]
  simp

lemma WO_succ2 (N : ℕ) : (W w1 (N + 2) : ℚ) = (fun x : ℚ =>
      (4 / 5 : ℚ) * x ^ 5 + 2 * x ^ 4 + 5 * x ^ 3 + (11 / 2 : ℚ) * x ^ 2 + (37 / 10 : ℚ) * x + 1) ((N + 2 : ℕ) : ℚ) + W w1 N := by
  rw [W_O, pos_shift w1 1 (fun c => rfl) N]
  push_cast
  ring

lemma D_eq : ∀ m : ℕ, (W w1 m : ℚ) + W w1 (m + 1) = (fun x : ℚ =>
      (2 / 15 : ℚ) * x ^ 6 + (8 / 5 : ℚ) * x ^ 5 + (103 / 12 : ℚ) * x ^ 4 + 26 * x ^ 3 + (2777 / 60 : ℚ) * x ^ 2
      + (227 / 5 : ℚ) * x + 19) (m : ℚ)
  | 0 => by
    rw [WO_small 0 (by norm_num), WO_small 1 (by norm_num)]
    norm_num
  | m + 1 => by
    rw [WO_succ2 m, show m + 1 + 1 = m + 2 by omega]
    have h := D_eq m
    beta_reduce at h ⊢
    push_cast
    linear_combination h

/-- The closed form of `a n` for `n ≥ 1`. -/
noncomputable def pz (x : ℚ) : ℚ :=
  (128 / 15 : ℚ) * x ^ 6 + (128 / 5 : ℚ) * x ^ 5 + (112 / 3 : ℚ) * x ^ 4 + 32 * x ^ 3 + (272 / 15 : ℚ) * x ^ 2
      + (32 / 5 : ℚ) * x + 1

lemma W_combo (m : ℕ) : (W w2 (m + 1) : ℚ) + 2 ^ 6 * W w1 m = pz ((m + 1 : ℕ) : ℚ) := by
  rcases m with _ | m
  · rw [WE_small 1 (by norm_num), WO_small 0 (by norm_num), pz]
    norm_num
  · rw [show m + 1 + 1 = m + 2 by omega, WE_succ2 m, show m + 1 = m + 1 from rfl]
    have h := D_eq m
    beta_reduce at h ⊢
    rw [pz]
    push_cast
    linear_combination 2 ^ 6 * h

/-! ## From the arrays to the cyclic tuples -/

open OMA.S_oeis_a221969

lemma nabs_iff (a b : ℤ) (n : ℕ) : a.natAbs + b.natAbs ≤ n ↔
    (-(n : ℤ) ≤ a + b ∧ a + b ≤ n ∧ -(n : ℤ) ≤ a - b ∧ a - b ≤ n) := by
  omega

lemma ofold_iff (a b : ℤ) (m : ℕ) : oddFold a + oddFold b ≤ m ↔
    (-(m : ℤ) - 1 ≤ a + b + 1 ∧ a + b + 1 ≤ m + 1 ∧ -(m : ℤ) - 1 ≤ a - b ∧ a - b ≤ m + 1) := by
  unfold oddFold
  split_ifs <;> omega

/-- The integer box. -/
noncomputable def zbox (lo hi : ℤ) : Finset (Fin 6 → ℤ) := Fintype.piFinset fun _ => Icc lo hi

open Classical in
lemma a_card (n : ℕ) : a n = ((zbox (-(n : ℤ)) n).filter
    (fun x => ∀ i, |ahead x i - following x i| ≤ n)).card := by
  rw [a, ← Set.ncard_coe_finset]
  congr 1
  ext x
  simp [zbox, Fintype.mem_piFinset]

/-- Even total: the tuple `u`. -/
noncomputable def toU (x : Fin 6 → ℤ) : Fin 6 → ℤ := ![-((x 0 + x 1 + x 2 + x 3 + x 4 + x 5) / 2), x 0 - (x 0 + x 1 + x 2 + x 3 + x 4 + x 5) / 2, x 0 + x 1 - (x 0 + x 1 + x 2 + x 3 + x 4 + x 5) / 2, x 0 + x 1 + x 2 - (x 0 + x 1 + x 2 + x 3 + x 4 + x 5) / 2, x 0 + x 1 + x 2 + x 3 - (x 0 + x 1 + x 2 + x 3 + x 4 + x 5) / 2, x 0 + x 1 + x 2 + x 3 + x 4 - (x 0 + x 1 + x 2 + x 3 + x 4 + x 5) / 2]

noncomputable def fromU (u : Fin 6 → ℤ) : Fin 6 → ℤ := ![u 1 - u 0, u 2 - u 1, u 3 - u 2, u 4 - u 3, u 5 - u 4, -u 0 - u 5]

/-- Odd total: the tuple `v`. -/
noncomputable def toV (x : Fin 6 → ℤ) : Fin 6 → ℤ := ![-((x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + 1) / 2), x 0 - (x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + 1) / 2, x 0 + x 1 - (x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + 1) / 2, x 0 + x 1 + x 2 - (x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + 1) / 2, x 0 + x 1 + x 2 + x 3 - (x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + 1) / 2, x 0 + x 1 + x 2 + x 3 + x 4 - (x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + 1) / 2]

noncomputable def fromV (v : Fin 6 → ℤ) : Fin 6 → ℤ := ![v 1 - v 0, v 2 - v 1, v 3 - v 2, v 4 - v 3, v 5 - v 4, -v 0 - 1 - v 5]

lemma fa0 : ((0 : Fin 6) + 1) = 1 := rfl

lemma fa1 : ((1 : Fin 6) + 1) = 2 := rfl

lemma fa2 : ((2 : Fin 6) + 1) = 3 := rfl

lemma fa3 : ((3 : Fin 6) + 1) = 4 := rfl

lemma fa4 : ((4 : Fin 6) + 1) = 5 := rfl

lemma fa5 : ((5 : Fin 6) + 1) = 0 := rfl

lemma ah0 (x : Fin 6 → ℤ) : ahead x 0 = 0 := by
  simp [ahead, Finset.sum_filter, Fin.sum_univ_six]

lemma fo0 (x : Fin 6 → ℤ) : following x 0 = x 1 + x 2 + x 3 + x 4 + x 5 := by
  simp [following, Finset.sum_filter, Fin.sum_univ_six]

lemma ah1 (x : Fin 6 → ℤ) : ahead x 1 = x 0 := by
  simp [ahead, Finset.sum_filter, Fin.sum_univ_six]

lemma fo1 (x : Fin 6 → ℤ) : following x 1 = x 2 + x 3 + x 4 + x 5 := by
  simp [following, Finset.sum_filter, Fin.sum_univ_six]

lemma ah2 (x : Fin 6 → ℤ) : ahead x 2 = x 0 + x 1 := by
  simp [ahead, Finset.sum_filter, Fin.sum_univ_six]

lemma fo2 (x : Fin 6 → ℤ) : following x 2 = x 3 + x 4 + x 5 := by
  simp [following, Finset.sum_filter, Fin.sum_univ_six]

lemma ah3 (x : Fin 6 → ℤ) : ahead x 3 = x 0 + x 1 + x 2 := by
  simp [ahead, Finset.sum_filter, Fin.sum_univ_six]

lemma fo3 (x : Fin 6 → ℤ) : following x 3 = x 4 + x 5 := by
  simp [following, Finset.sum_filter, Fin.sum_univ_six]

lemma ah4 (x : Fin 6 → ℤ) : ahead x 4 = x 0 + x 1 + x 2 + x 3 := by
  simp [ahead, Finset.sum_filter, Fin.sum_univ_six]

lemma fo4 (x : Fin 6 → ℤ) : following x 4 = x 5 := by
  simp [following, Finset.sum_filter, Fin.sum_univ_six]

lemma ah5 (x : Fin 6 → ℤ) : ahead x 5 = x 0 + x 1 + x 2 + x 3 + x 4 := by
  simp [ahead, Finset.sum_filter, Fin.sum_univ_six]

lemma fo5 (x : Fin 6 → ℤ) : following x 5 = 0 := by
  simp [following, Finset.sum_filter, Fin.sum_univ_six]

lemma toU0 (x : Fin 6 → ℤ) : toU x 0 = -((x 0 + x 1 + x 2 + x 3 + x 4 + x 5) / 2) := rfl

lemma toU1 (x : Fin 6 → ℤ) : toU x 1 = x 0 - (x 0 + x 1 + x 2 + x 3 + x 4 + x 5) / 2 := rfl

lemma toU2 (x : Fin 6 → ℤ) : toU x 2 = x 0 + x 1 - (x 0 + x 1 + x 2 + x 3 + x 4 + x 5) / 2 := rfl

lemma toU3 (x : Fin 6 → ℤ) : toU x 3 = x 0 + x 1 + x 2 - (x 0 + x 1 + x 2 + x 3 + x 4 + x 5) / 2 := rfl

lemma toU4 (x : Fin 6 → ℤ) : toU x 4 = x 0 + x 1 + x 2 + x 3 - (x 0 + x 1 + x 2 + x 3 + x 4 + x 5) / 2 := rfl

lemma toU5 (x : Fin 6 → ℤ) : toU x 5 = x 0 + x 1 + x 2 + x 3 + x 4 - (x 0 + x 1 + x 2 + x 3 + x 4 + x 5) / 2 := rfl

lemma fromU0 (u : Fin 6 → ℤ) : fromU u 0 = u 1 - u 0 := rfl

lemma fromU1 (u : Fin 6 → ℤ) : fromU u 1 = u 2 - u 1 := rfl

lemma fromU2 (u : Fin 6 → ℤ) : fromU u 2 = u 3 - u 2 := rfl

lemma fromU3 (u : Fin 6 → ℤ) : fromU u 3 = u 4 - u 3 := rfl

lemma fromU4 (u : Fin 6 → ℤ) : fromU u 4 = u 5 - u 4 := rfl

lemma fromU5 (u : Fin 6 → ℤ) : fromU u 5 = -u 0 - u 5 := rfl

lemma toV0 (x : Fin 6 → ℤ) : toV x 0 = -((x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + 1) / 2) := rfl

lemma toV1 (x : Fin 6 → ℤ) : toV x 1 = x 0 - (x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + 1) / 2 := rfl

lemma toV2 (x : Fin 6 → ℤ) : toV x 2 = x 0 + x 1 - (x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + 1) / 2 := rfl

lemma toV3 (x : Fin 6 → ℤ) : toV x 3 = x 0 + x 1 + x 2 - (x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + 1) / 2 := rfl

lemma toV4 (x : Fin 6 → ℤ) : toV x 4 = x 0 + x 1 + x 2 + x 3 - (x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + 1) / 2 := rfl

lemma toV5 (x : Fin 6 → ℤ) : toV x 5 = x 0 + x 1 + x 2 + x 3 + x 4 - (x 0 + x 1 + x 2 + x 3 + x 4 + x 5 + 1) / 2 := rfl

lemma fromV0 (v : Fin 6 → ℤ) : fromV v 0 = v 1 - v 0 := rfl

lemma fromV1 (v : Fin 6 → ℤ) : fromV v 1 = v 2 - v 1 := rfl

lemma fromV2 (v : Fin 6 → ℤ) : fromV v 2 = v 3 - v 2 := rfl

lemma fromV3 (v : Fin 6 → ℤ) : fromV v 3 = v 4 - v 3 := rfl

lemma fromV4 (v : Fin 6 → ℤ) : fromV v 4 = v 5 - v 4 := rfl

lemma fromV5 (v : Fin 6 → ℤ) : fromV v 5 = -v 0 - 1 - v 5 := rfl

open Classical in
lemma card_even (n : ℕ) : (((zbox (-(n : ℤ)) n).filter
    (fun x => ∀ i, |ahead x i - following x i| ≤ n)).filter (fun x => (∑ i, x i) % 2 = 0)).card =
    ((zbox (-(n : ℤ)) n).filter (fun u => cyc n (fun i => (u i).natAbs))).card := by
  apply Finset.card_nbij' toU fromU
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_filter, Set.mem_setOf_eq, zbox, Fintype.mem_piFinset,
      Finset.mem_Icc] at hx ⊢
    simp only [forallK, cyc, fa0, fa1, fa2, fa3, fa4, fa5, ah0, ah1, ah2, ah3, ah4, ah5, fo0, fo1, fo2, fo3, fo4, fo5, toU0, toU1, toU2, toU3, toU4, toU5, nabs_iff, abs_le, Fin.sum_univ_six] at hx ⊢
    omega
  · intro u hu
    simp only [Finset.coe_filter, Finset.mem_filter, Set.mem_setOf_eq, zbox, Fintype.mem_piFinset,
      Finset.mem_Icc] at hu ⊢
    simp only [forallK, cyc, fa0, fa1, fa2, fa3, fa4, fa5, ah0, ah1, ah2, ah3, ah4, ah5, fo0, fo1, fo2, fo3, fo4, fo5, fromU0, fromU1, fromU2, fromU3, fromU4, fromU5, nabs_iff, abs_le, Fin.sum_univ_six] at hu ⊢
    omega
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Fin.sum_univ_six] at hx
    funext i
    fin_cases i <;> simp [toU, fromU] <;> omega
  · intro u _
    funext i
    fin_cases i <;> simp [toU, fromU, Fin.sum_univ_six] <;> omega

open Classical in
lemma card_odd (m : ℕ) : (((zbox (-((m + 1 : ℕ) : ℤ)) (m + 1 : ℕ)).filter
    (fun x => ∀ i, |ahead x i - following x i| ≤ (m + 1 : ℕ))).filter
      (fun x => ¬ (∑ i, x i) % 2 = 0)).card =
    ((zbox (-(m : ℤ) - 1) m).filter (fun v => cyc m (fun i => oddFold (v i)))).card := by
  apply Finset.card_nbij' toV fromV
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_filter, Set.mem_setOf_eq, zbox, Fintype.mem_piFinset,
      Finset.mem_Icc] at hx ⊢
    simp only [forallK, cyc, fa0, fa1, fa2, fa3, fa4, fa5, ah0, ah1, ah2, ah3, ah4, ah5, fo0, fo1, fo2, fo3, fo4, fo5, toV0, toV1, toV2, toV3, toV4, toV5, ofold_iff, abs_le, Fin.sum_univ_six] at hx ⊢
    push_cast at hx ⊢
    omega
  · intro v hv
    simp only [Finset.coe_filter, Finset.mem_filter, Set.mem_setOf_eq, zbox, Fintype.mem_piFinset,
      Finset.mem_Icc] at hv ⊢
    simp only [forallK, cyc, fa0, fa1, fa2, fa3, fa4, fa5, ah0, ah1, ah2, ah3, ah4, ah5, fo0, fo1, fo2, fo3, fo4, fo5, fromV0, fromV1, fromV2, fromV3, fromV4, fromV5, ofold_iff, abs_le, Fin.sum_univ_six] at hv ⊢
    push_cast at hv ⊢
    omega
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Fin.sum_univ_six] at hx
    funext i
    fin_cases i <;> simp [toV, fromV] <;> omega
  · intro v _
    funext i
    fin_cases i <;> simp [toV, fromV, Fin.sum_univ_six] <;> omega

open Classical in
lemma card_U (n : ℕ) : ((zbox (-(n : ℤ)) n).filter (fun u => cyc n (fun i => (u i).natAbs))).card =
    W w2 n := by
  rw [Finset.card_filter, zbox, fold_sum 6 _ (range (n + 1)) Int.natAbs (fun z hz => by
    simp only [Finset.mem_Icc] at hz
    simp only [Finset.mem_range]
    omega) (fun b => if cyc n b then 1 else 0), W]
  refine Finset.sum_congr rfl fun b hb => ?_
  simp only [box, Fintype.mem_piFinset, Finset.mem_range] at hb
  rw [Finset.prod_congr rfl (fun i _ => fiber_abs n (b i) (by have := hb i; omega))]
  split_ifs <;> simp

open Classical in
lemma card_V (m : ℕ) : ((zbox (-(m : ℤ) - 1) m).filter
    (fun v => cyc m (fun i => oddFold (v i)))).card = 2 ^ 6 * W w1 m := by
  rw [Finset.card_filter, zbox, fold_sum 6 _ (range (m + 1)) oddFold (fun z hz => by
    simp only [Finset.mem_Icc] at hz
    simp only [Finset.mem_range, oddFold]
    split_ifs <;> omega) (fun b => if cyc m b then 1 else 0), W, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  simp only [box, Fintype.mem_piFinset, Finset.mem_range] at hb
  rw [Finset.prod_congr rfl (fun i _ => fiber_odd m (b i) (by have := hb i; omega))]
  split_ifs <;> simp [w1]

theorem bridge (m : ℕ) : a (m + 1) = W w2 (m + 1) + 2 ^ 6 * W w1 m := by
  rw [a_card, ← Finset.card_filter_add_card_filter_not (fun x : Fin 6 → ℤ => (∑ i, x i) % 2 = 0),
    card_even, card_U, card_odd, card_V]

theorem a_val (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = pz n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [bridge, ← W_combo m]
  push_cast
  ring

/-! ## The generating function and the recurrence -/

open PowerSeries

theorem gf_core (f : ℕ → ℚ) (h0 : f 0 = 0) (hp : ∀ n : ℕ, 1 ≤ n → f n = pz n) :
    PowerSeries.mk f * (1 - X) ^ 7 = X * ((3 + X) * (43 + 453 * X + 878 * X ^ 2 + 170 * X ^ 3 - 9 * X ^ 4 + X ^ 5)) := by
  have e : PowerSeries.mk f * (1 - X) ^ 7 = PowerSeries.mk f - C 7 * (X ^ 1 * PowerSeries.mk f) + C 21 * (X ^ 2 * PowerSeries.mk f) - C 35 * (X ^ 3 * PowerSeries.mk f)
      + C 35 * (X ^ 4 * PowerSeries.mk f) - C 21 * (X ^ 5 * PowerSeries.mk f) + C 7 * (X ^ 6 * PowerSeries.mk f)
      - X ^ 7 * PowerSeries.mk f := by
    simp only [map_ofNat]
    ring
  have e2 : (X * ((3 + X) * (43 + 453 * X + 878 * X ^ 2 + 170 * X ^ 3 - 9 * X ^ 4 + X ^ 5)) : ℚ⟦X⟧) =
      C 129 * X ^ 1 + C 1402 * X ^ 2 + C 3087 * X ^ 3 + C 1388 * X ^ 4 + C 143 * X ^ 5 - C 6 * X ^ 6
      + X ^ 7 := by
    simp only [map_ofNat]
    ring
  have v1 : f 1 = 129 := by rw [hp 1 (by norm_num), pz]; norm_num
  have v2 : f 2 = 2305 := by rw [hp 2 (by norm_num), pz]; norm_num
  have v3 : f 3 = 16513 := by rw [hp 3 (by norm_num), pz]; norm_num
  have v4 : f 4 = 73089 := by rw [hp 4 (by norm_num), pz]; norm_num
  have v5 : f 5 = 241153 := by rw [hp 5 (by norm_num), pz]; norm_num
  have v6 : f 6 = 653185 := by rw [hp 6 (by norm_num), pz]; norm_num
  have v7 : f 7 = 1535745 := by rw [hp 7 (by norm_num), pz]; norm_num
  rw [e, e2]
  ext N
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow]
  rcases lt_or_ge N 8 with h | h
  · interval_cases N <;> simp [h0, v1, v2, v3, v4, v5, v6, v7] <;> norm_num
  · obtain ⟨M, rfl⟩ : ∃ M, N = M + 8 := ⟨N - 8, by omega⟩
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      show M + 8 - 1 = M + 7 by omega, show M + 8 - 2 = M + 6 by omega, show M + 8 - 3 = M + 5 by omega, show M + 8 - 4 = M + 4 by omega, show M + 8 - 5 = M + 3 by omega, show M + 8 - 6 = M + 2 by omega, show M + 8 - 7 = M + 1 by omega]
    rw [hp (M + 8) (by omega), hp (M + 7) (by omega), hp (M + 6) (by omega), hp (M + 5) (by omega), hp (M + 4) (by omega), hp (M + 3) (by omega), hp (M + 2) (by omega), hp (M + 1) (by omega)]
    simp only [pz]
    push_cast
    ring

end OMA.P_oeis_a221969

open PowerSeries OMA.S_oeis_a221969 OMA.P_oeis_a221969 in
theorem OMA.solution : type_of% @OMA.S_oeis_a221969.main := by
  refine ⟨gf_core _ (by simp) (fun n hn => by simp [show n ≠ 0 by omega, a_val n hn]), ?_⟩
  intro n hn
  obtain ⟨M, rfl⟩ : ∃ M, n = M + 8 := ⟨n - 8, by omega⟩
  rw [show M + 8 - 1 = M + 7 by omega, show M + 8 - 2 = M + 6 by omega, show M + 8 - 3 = M + 5 by omega, show M + 8 - 4 = M + 4 by omega, show M + 8 - 5 = M + 3 by omega, show M + 8 - 6 = M + 2 by omega, show M + 8 - 7 = M + 1 by omega]
  have key : (a (M + 8) : ℚ) = 7 * a (M + 7) - 21 * a (M + 6) + 35 * a (M + 5) - 35 * a (M + 4) + 21 * a (M + 3) - 7 * a (M
      + 2) + a (M + 1) := by
    rw [a_val _ (by omega), a_val _ (by omega), a_val _ (by omega), a_val _ (by omega), a_val _ (by omega), a_val _ (by omega), a_val _ (by omega), a_val _ (by omega)]
    simp only [pz]
    push_cast
    ring
  exact_mod_cast key

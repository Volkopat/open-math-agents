import OMAStatements.S_oeis_a201046

namespace OMA.S_oeis_a201046

open PowerSeries



section ChainCount

/-- The number of sequences w_1, ..., w_L of elements of s continuing v with R between consecutive
entries (v, w_1), (w_1, w_2), .... -/
def chainCnt {α : Type*} (s : Finset α) (R : α → α → Prop) [DecidableRel R] : ℕ → α → ℕ
  | 0, _ => 1
  | L + 1, v => ∑ w ∈ s.filter (R v ·), chainCnt s R L w

lemma card_piFinset_cons {α : Type*} [DecidableEq α] (s : Finset α) {L : ℕ}
    (P : (Fin (L + 1) → α) → Prop) [DecidablePred P] :
    ((Fintype.piFinset fun _ : Fin (L + 1) => s).filter P).card =
      ∑ v ∈ s, ((Fintype.piFinset fun _ : Fin L => s).filter (fun y => P (Fin.cons v y))).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x : Fin (L + 1) → α => x 0) (t := s)
    (fun x hx => by
      simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hx
      exact hx.1 0)]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  symm
  apply Finset.card_bij (fun y _ => (Fin.cons v y : Fin (L + 1) → α))
  · intro y hy
    simp only [Finset.mem_filter, Fintype.mem_piFinset] at hy ⊢
    refine ⟨⟨fun i => ?_, hy.2⟩, by simp⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hv
    · simpa using hy.1 j
  · intro y₁ _ y₂ _ e
    simpa using congrArg Fin.tail e
  · intro x hx
    simp only [Finset.mem_filter, Fintype.mem_piFinset] at hx
    obtain ⟨⟨hmem, hp⟩, h0⟩ := hx
    refine ⟨Fin.tail x, ?_, ?_⟩
    · simp only [Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨fun i => hmem i.succ, ?_⟩
      rw [← h0, Fin.cons_self_tail]
      exact hp
    · show Fin.cons v (Fin.tail x) = x
      rw [← h0, Fin.cons_self_tail]

lemma chain_cons {α : Type*} (R : α → α → Prop) {L : ℕ} (v : α) (y : Fin (L + 1) → α) :
    (∀ i : Fin (L + 1), R ((Fin.cons v y : Fin (L + 2) → α) i.castSucc)
      ((Fin.cons v y : Fin (L + 2) → α) i.succ)) ↔
      R v (y 0) ∧ ∀ i : Fin L, R (y i.castSucc) (y i.succ) := by
  rw [Fin.forall_fin_succ]
  simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.succ_zero_eq_one, Fin.cons_one,
    Fin.castSucc_succ, Fin.cons_succ]

/-- The sequences continuing v, as a filtered piFinset. -/
lemma cnt_from {α : Type*} [DecidableEq α] (s : Finset α) (R : α → α → Prop) [DecidableRel R] :
    ∀ (L : ℕ) (v : α), ((Fintype.piFinset fun _ : Fin L => s).filter
      (fun y => ∀ i : Fin L, R ((Fin.cons v y : Fin (L + 1) → α) i.castSucc)
        ((Fin.cons v y : Fin (L + 1) → α) i.succ))).card = chainCnt s R L v
  | 0, v => by
    rw [chainCnt]
    have hu : (Fintype.piFinset fun _ : Fin 0 => s) = {Fin.elim0} := by
      ext g
      simp only [Fintype.mem_piFinset, Finset.mem_singleton]
      constructor
      · intro _
        funext i
        exact i.elim0
      · intro _ i
        exact i.elim0
    rw [hu, Finset.filter_singleton]
    simp
  | L + 1, v => by
    rw [chainCnt, Finset.sum_filter, card_piFinset_cons]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    simp only [chain_cons, Fin.cons_zero]
    by_cases hw : R v w
    · rw [if_pos hw, ← cnt_from s R L w]
      congr 1
      ext z
      simp only [Finset.mem_filter, hw, true_and]
    · rw [if_neg hw, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro z _ hz
      exact hw hz.1

/-- Arrays with R between consecutive entries, counted through chainCnt. -/
theorem card_chain {α : Type*} [DecidableEq α] (s : Finset α) (R : α → α → Prop) [DecidableRel R]
    (L : ℕ) : ((Fintype.piFinset fun _ : Fin (L + 1) => s).filter
      (fun x => ∀ i : Fin L, R (x i.castSucc) (x i.succ))).card = ∑ v ∈ s, chainCnt s R L v := by
  rw [card_piFinset_cons]
  exact Finset.sum_congr rfl (fun v _ => cnt_from s R L v)

end ChainCount

section DiffCount

variable (n : ℕ)

/-- Entries in -n..n with consecutive differences in -n..n. -/
def Rd (v w : ℤ) : Prop := -(n : ℤ) ≤ w - v ∧ w - v ≤ n

instance : DecidableRel (Rd n) := fun v w => by unfold Rd; infer_instance

/-- The continuations from x and from -x are equally many (reflection). -/
lemma cnt_neg : ∀ (L : ℕ) (x : ℤ),
    chainCnt (Finset.Icc (-(n : ℤ)) n) (Rd n) L (-x) = chainCnt (Finset.Icc (-(n : ℤ)) n) (Rd n) L x
  | 0, x => rfl
  | L + 1, x => by
    rw [chainCnt, chainCnt]
    apply Finset.sum_nbij' (fun w : ℤ => -w) (fun w : ℤ => -w)
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_Icc] at hw ⊢
      unfold Rd at hw ⊢
      omega
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_Icc] at hw ⊢
      unfold Rd at hw ⊢
      omega
    · intro w _
      simp
    · intro w _
      simp
    · intro w _
      exact (cnt_neg L w).symm

lemma filter_Rd (x : ℤ) (h0 : 0 ≤ x) :
    (Finset.Icc (-(n : ℤ)) n).filter (Rd n x ·) = Finset.Icc (x - n) n := by
  ext w
  simp only [Finset.mem_filter, Finset.mem_Icc]
  unfold Rd
  omega

/-- A sum over Icc 0 n as a sum over range. -/
lemma sum_Icc_zero (g : ℤ → ℚ) :
    ∑ w ∈ Finset.Icc (0 : ℤ) n, g w = ∑ u ∈ Finset.range (n + 1), g u := by
  apply Finset.sum_nbij' (fun w : ℤ => w.toNat) (fun u : ℕ => (u : ℤ))
  · intro w hw
    simp only [Finset.mem_Icc] at hw
    simp only [Finset.mem_range]
    omega
  · intro u hu
    simp only [Finset.mem_range] at hu
    simp only [Finset.mem_Icc]
    omega
  · intro w hw
    simp only [Finset.mem_Icc] at hw
    simp only [Int.toNat_of_nonneg hw.1]
  · intro u _
    simp
  · intro w hw
    simp only [Finset.mem_Icc] at hw
    simp only [Int.toNat_of_nonneg hw.1]

/-- A sum over Icc (x - n) (-1) as a sum over range. -/
lemma sum_Icc_neg (g : ℤ → ℚ) (x : ℤ) (hx : x ≤ n) :
    ∑ w ∈ Finset.Icc (x - n) (-1), g w = ∑ u ∈ Finset.range (n - x).toNat, g (-(u + 1 : ℤ)) := by
  apply Finset.sum_nbij' (fun w : ℤ => (-w - 1).toNat) (fun u : ℕ => -((u : ℤ) + 1))
  · intro w hw
    simp only [Finset.mem_Icc] at hw
    simp only [Finset.mem_range]
    omega
  · intro u hu
    simp only [Finset.mem_range] at hu
    simp only [Finset.mem_Icc]
    omega
  · intro w hw
    simp only [Finset.mem_Icc] at hw
    omega
  · intro u _
    omega
  · intro w hw
    simp only [Finset.mem_Icc] at hw
    congr 1
    omega

/-- The split of the continuations of 0 ≤ x ≤ n into entries ≥ 0 and entries < 0. -/
lemma cnt_split (L : ℕ) (x : ℤ) (h0 : 0 ≤ x) (hx : x ≤ n) (g : ℤ → ℚ)
    (hg : ∀ w : ℤ, |w| ≤ n → (chainCnt (Finset.Icc (-(n : ℤ)) n) (Rd n) L w : ℚ) = g |w|) :
    (chainCnt (Finset.Icc (-(n : ℤ)) n) (Rd n) (L + 1) x : ℚ) =
      ∑ u ∈ Finset.range (n + 1), g u + ∑ u ∈ Finset.range (n - x).toNat, g (u + 1 : ℤ) := by
  rw [chainCnt, filter_Rd n x h0]
  push_cast
  have hsplit : Finset.Icc (x - n) n = Finset.Icc (x - n) (-1) ∪ Finset.Icc 0 (n : ℤ) := by
    ext w
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hdisj : Disjoint (Finset.Icc (x - n) (-1)) (Finset.Icc 0 (n : ℤ)) := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    simp only [Finset.mem_Icc] at h1 h2
    omega
  rw [hsplit, Finset.sum_union hdisj, add_comm]
  congr 1
  · rw [sum_Icc_zero n (fun w => (chainCnt (Finset.Icc (-(n : ℤ)) n) (Rd n) L w : ℚ))]
    refine Finset.sum_congr rfl (fun u hu => ?_)
    rw [Finset.mem_range] at hu
    rw [hg u (by rw [abs_of_nonneg (by positivity)]; omega), abs_of_nonneg (by positivity)]
  · rw [sum_Icc_neg n (fun w => (chainCnt (Finset.Icc (-(n : ℤ)) n) (Rd n) L w : ℚ)) x hx]
    refine Finset.sum_congr rfl (fun u hu => ?_)
    rw [Finset.mem_range] at hu
    rw [hg _ (by rw [abs_le]; constructor <;> omega),
      abs_of_neg (by omega : -((u : ℤ) + 1) < 0), neg_neg]

/-- The total over -n..n from the values on 0..n. -/
lemma total_split (L : ℕ) (g : ℤ → ℚ)
    (hg : ∀ w : ℤ, |w| ≤ n → (chainCnt (Finset.Icc (-(n : ℤ)) n) (Rd n) L w : ℚ) = g |w|) :
    (∑ v ∈ Finset.Icc (-(n : ℤ)) n, (chainCnt (Finset.Icc (-(n : ℤ)) n) (Rd n) L v : ℚ)) =
      2 * ∑ u ∈ Finset.range (n + 1), g u - g 0 := by
  have hsplit : Finset.Icc (-(n : ℤ)) n = Finset.Icc (-(n : ℤ)) (-1) ∪ Finset.Icc 0 (n : ℤ) := by
    ext w
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hdisj : Disjoint (Finset.Icc (-(n : ℤ)) (-1)) (Finset.Icc 0 (n : ℤ)) := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    simp only [Finset.mem_Icc] at h1 h2
    omega
  have hunion : ∑ v ∈ Finset.Icc (-(n : ℤ)) n, (chainCnt (Finset.Icc (-(n : ℤ)) n) (Rd n) L v : ℚ) =
      ∑ v ∈ Finset.Icc (-(n : ℤ)) (-1), (chainCnt (Finset.Icc (-(n : ℤ)) n) (Rd n) L v : ℚ) +
        ∑ v ∈ Finset.Icc 0 (n : ℤ), (chainCnt (Finset.Icc (-(n : ℤ)) n) (Rd n) L v : ℚ) := by
    rw [← Finset.sum_union hdisj, ← hsplit]
  have hpos : ∑ v ∈ Finset.Icc 0 (n : ℤ), (chainCnt (Finset.Icc (-(n : ℤ)) n) (Rd n) L v : ℚ) =
      ∑ u ∈ Finset.range (n + 1), g u := by
    rw [sum_Icc_zero n (fun w => (chainCnt (Finset.Icc (-(n : ℤ)) n) (Rd n) L w : ℚ))]
    refine Finset.sum_congr rfl (fun u hu => ?_)
    rw [Finset.mem_range] at hu
    rw [hg u (by rw [abs_of_nonneg (by positivity)]; omega), abs_of_nonneg (by positivity)]
  have hneg :
      ∑ v ∈ Finset.Icc (-(n : ℤ)) (-1), (chainCnt (Finset.Icc (-(n : ℤ)) n) (Rd n) L v : ℚ) =
        ∑ u ∈ Finset.range (n + 1), g u - g 0 := by
    have he : Finset.Icc (-(n : ℤ)) (-1) = Finset.Icc (0 - (n : ℤ)) (-1) := by rw [zero_sub]
    rw [he, sum_Icc_neg n _ 0 (by positivity), show ((n : ℤ) - 0).toNat = n by simp,
      Finset.sum_range_succ' (fun u : ℕ => g u)]
    simp only [Nat.cast_zero, add_sub_cancel_right]
    refine Finset.sum_congr rfl (fun u hu => ?_)
    rw [Finset.mem_range] at hu
    rw [hg _ (by rw [abs_le]; constructor <;> omega), abs_of_neg (by omega)]
    push_cast
    ring_nf
  rw [hunion, hpos, hneg]
  ring

lemma cnt_abs (L : ℕ) (w : ℤ) :
    chainCnt (Finset.Icc (-(n : ℤ)) n) (Rd n) L w =
      chainCnt (Finset.Icc (-(n : ℤ)) n) (Rd n) L |w| := by
  rcases abs_choice w with h | h <;> rw [h]
  exact (cnt_neg n L w).symm

omit n in
lemma sum_shift (g S : ℚ → ℚ) (hS : ∀ m : ℕ, ∑ u ∈ Finset.range (m + 1), g (u : ℚ) = S m) (M : ℕ) :
    ∑ u ∈ Finset.range M, g ((u : ℚ) + 1) = S M - g 0 := by
  have e := hS M
  rw [Finset.sum_range_succ'] at e
  push_cast at e
  linarith

/-- One level of the recursion: if the continuations of length L from w are g(|w|), and S is the
antiderivative of g, the continuations of length L + 1 from w are S(n) + S(n - |w|) - g(0). -/
lemma level_step (L : ℕ) (g g' S : ℚ → ℚ)
    (hg : ∀ w : ℤ, |w| ≤ n →
      (chainCnt (Finset.Icc (-(n : ℤ)) n) (Rd n) L w : ℚ) = g ((|w| : ℤ) : ℚ))
    (hS : ∀ m : ℕ, ∑ u ∈ Finset.range (m + 1), g (u : ℚ) = S m)
    (hg' : ∀ x : ℚ, g' x = S n + S (n - x) - g 0) :
    ∀ w : ℤ, |w| ≤ n →
      (chainCnt (Finset.Icc (-(n : ℤ)) n) (Rd n) (L + 1) w : ℚ) = g' ((|w| : ℤ) : ℚ) := by
  intro w hw
  rw [cnt_abs n (L + 1) w, cnt_split n L |w| (abs_nonneg w) hw (fun x : ℤ => g (x : ℚ)) hg]
  simp only [Int.cast_natCast, Int.cast_add, Int.cast_one]
  rw [hS n, sum_shift g S hS, hg']
  have hc : ((((n : ℤ) - |w|).toNat : ℕ) : ℚ) = (n : ℚ) - ((|w| : ℤ) : ℚ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    push_cast
    ring
  rw [hc]
  ring

end DiffCount

/-- Continuations of length 0 from an entry of absolute value X. -/
def g0 (_N _X : ℚ) : ℚ := 1

/-- The sum of g0 N u over u = 0..M. -/
def S0 (_N M : ℚ) : ℚ := M + 1

lemma sum0 (n m : ℕ) : ∑ u ∈ Finset.range (m + 1), g0 n (u : ℚ) = S0 n m := by
  induction m with
  | zero => simp only [zero_add, Finset.sum_range_one, Nat.cast_zero, g0, S0]
  | succ m ih => rw [Finset.sum_range_succ, ih]; simp only [g0, S0]; push_cast; ring

lemma hg0 (n : ℕ) : ∀ w : ℤ, |w| ≤ n →
    (chainCnt (Finset.Icc (-(n : ℤ)) n) (Rd n) 0 w : ℚ) = g0 n ((|w| : ℤ) : ℚ) :=
  fun w _ => by simp [chainCnt, g0]

/-- Continuations of length 1 from an entry of absolute value X. -/
def g1 (N X : ℚ) : ℚ := 2 * N - X + 1

/-- The sum of g1 N u over u = 0..M. -/
def S1 (N M : ℚ) : ℚ := 2 * N * M - 1 / 2 * M ^ 2 + 2 * N + 1 / 2 * M + 1

lemma sum1 (n m : ℕ) : ∑ u ∈ Finset.range (m + 1), g1 n (u : ℚ) = S1 n m := by
  induction m with
  | zero => simp only [zero_add, Finset.sum_range_one, Nat.cast_zero, g1, S1]; ring
  | succ m ih => rw [Finset.sum_range_succ, ih]; simp only [g1, S1]; push_cast; ring

lemma hg1 (n : ℕ) : ∀ w : ℤ, |w| ≤ n →
    (chainCnt (Finset.Icc (-(n : ℤ)) n) (Rd n) 1 w : ℚ) = g1 n ((|w| : ℤ) : ℚ) :=
  level_step n 0 (g0 n) (g1 n) (S0 n) (hg0 n) (sum0 n)
    (fun x => by simp only [g0, g1, S0]; ring)

/-- Continuations of length 2 from an entry of absolute value X. -/
def g2 (N X : ℚ) : ℚ := 3 * N ^ 2 - N * X - 1 / 2 * X ^ 2 + 3 * N - 1 / 2 * X + 1

/-- The sum of g2 N u over u = 0..M. -/
def S2 (N M : ℚ) : ℚ := 3 * N ^ 2 * M - 1 / 2 * N * M ^ 2 - 1 / 6 * M ^ 3 + 3 * N ^ 2
    + 5 / 2 * N * M - 1 / 2 * M ^ 2 + 3 * N + 2 / 3 * M + 1

lemma sum2 (n m : ℕ) : ∑ u ∈ Finset.range (m + 1), g2 n (u : ℚ) = S2 n m := by
  induction m with
  | zero => simp only [zero_add, Finset.sum_range_one, Nat.cast_zero, g2, S2]; ring
  | succ m ih => rw [Finset.sum_range_succ, ih]; simp only [g2, S2]; push_cast; ring

lemma hg2 (n : ℕ) : ∀ w : ℤ, |w| ≤ n →
    (chainCnt (Finset.Icc (-(n : ℤ)) n) (Rd n) 2 w : ℚ) = g2 n ((|w| : ℤ) : ℚ) :=
  level_step n 1 (g1 n) (g2 n) (S1 n) (hg1 n) (sum1 n)
    (fun x => by simp only [g1, g2, S1]; ring)

/-- Continuations of length 3 from an entry of absolute value X. -/
def g3 (N X : ℚ) : ℚ := 14 / 3 * N ^ 3 - 3 / 2 * N ^ 2 * X - N * X ^ 2 + 1 / 6 * X ^ 3 + 7 * N ^ 2
    - 3 / 2 * N * X - 1 / 2 * X ^ 2 + 13 / 3 * N - 2 / 3 * X + 1

/-- The sum of g3 N u over u = 0..M. -/
def S3 (N M : ℚ) : ℚ := 14 / 3 * N ^ 3 * M - 3 / 4 * N ^ 2 * M ^ 2 - 1 / 3 * N * M ^ 3
    + 1 / 24 * M ^ 4 + 14 / 3 * N ^ 3 + 25 / 4 * N ^ 2 * M - 5 / 4 * N * M ^ 2 - 1 / 12 * M ^ 3
    + 7 * N ^ 2 + 41 / 12 * N * M - 13 / 24 * M ^ 2 + 13 / 3 * N + 7 / 12 * M + 1

lemma sum3 (n m : ℕ) : ∑ u ∈ Finset.range (m + 1), g3 n (u : ℚ) = S3 n m := by
  induction m with
  | zero => simp only [zero_add, Finset.sum_range_one, Nat.cast_zero, g3, S3]; ring
  | succ m ih => rw [Finset.sum_range_succ, ih]; simp only [g3, S3]; push_cast; ring

lemma hg3 (n : ℕ) : ∀ w : ℤ, |w| ≤ n →
    (chainCnt (Finset.Icc (-(n : ℤ)) n) (Rd n) 3 w : ℚ) = g3 n ((|w| : ℤ) : ℚ) :=
  level_step n 2 (g2 n) (g3 n) (S2 n) (hg2 n) (sum2 n)
    (fun x => by simp only [g2, g3, S2]; ring)

/-- Continuations of length 4 from an entry of absolute value X. -/
def g4 (N X : ℚ) : ℚ := 29 / 4 * N ^ 4 - 7 / 3 * N ^ 3 * X - 3 / 2 * N ^ 2 * X ^ 2
    + 1 / 6 * N * X ^ 3 + 1 / 24 * X ^ 4 + 29 / 2 * N ^ 3 - 7 / 2 * N ^ 2 * X - 3 / 2 * N * X ^ 2
    + 1 / 12 * X ^ 3 + 51 / 4 * N ^ 2 - 7 / 3 * N * X - 13 / 24 * X ^ 2 + 11 / 2 * N - 7 / 12 * X
    + 1

/-- The sum of g4 N u over u = 0..M. -/
def S4 (N M : ℚ) : ℚ := 29 / 4 * N ^ 4 * M - 7 / 6 * N ^ 3 * M ^ 2 - 1 / 2 * N ^ 2 * M ^ 3
    + 1 / 24 * N * M ^ 4 + 1 / 120 * M ^ 5 + 29 / 4 * N ^ 4 + 40 / 3 * N ^ 3 * M
    - 5 / 2 * N ^ 2 * M ^ 2 - 5 / 12 * N * M ^ 3 + 1 / 24 * M ^ 4 + 29 / 2 * N ^ 3
    + 43 / 4 * N ^ 2 * M - 15 / 8 * N * M ^ 2 - 1 / 8 * M ^ 3 + 51 / 4 * N ^ 2 + 49 / 12 * N * M
    - 13 / 24 * M ^ 2 + 11 / 2 * N + 37 / 60 * M + 1

lemma sum4 (n m : ℕ) : ∑ u ∈ Finset.range (m + 1), g4 n (u : ℚ) = S4 n m := by
  induction m with
  | zero => simp only [zero_add, Finset.sum_range_one, Nat.cast_zero, g4, S4]; ring
  | succ m ih => rw [Finset.sum_range_succ, ih]; simp only [g4, S4]; push_cast; ring

lemma hg4 (n : ℕ) : ∀ w : ℤ, |w| ≤ n →
    (chainCnt (Finset.Icc (-(n : ℤ)) n) (Rd n) 4 w : ℚ) = g4 n ((|w| : ℤ) : ℚ) :=
  level_step n 3 (g3 n) (g4 n) (S3 n) (hg3 n) (sum3 n)
    (fun x => by simp only [g3, g4, S3]; ring)

/-- Continuations of length 5 from an entry of absolute value X. -/
def g5 (N X : ℚ) : ℚ := 169 / 15 * N ^ 5 - 29 / 8 * N ^ 4 * X - 7 / 3 * N ^ 3 * X ^ 2
    + 1 / 4 * N ^ 2 * X ^ 3 + 1 / 12 * N * X ^ 4 - 1 / 120 * X ^ 5 + 169 / 6 * N ^ 4
    - 29 / 4 * N ^ 3 * X - 7 / 2 * N ^ 2 * X ^ 2 + 1 / 4 * N * X ^ 3 + 1 / 24 * X ^ 4 + 32 * N ^ 3
    - 53 / 8 * N ^ 2 * X - 9 / 4 * N * X ^ 2 + 1 / 8 * X ^ 3 + 119 / 6 * N ^ 2 - 3 * N * X
    - 13 / 24 * X ^ 2 + 101 / 15 * N - 37 / 60 * X + 1

/-- The sum of g5 N u over u = 0..M. -/
def S5 (N M : ℚ) : ℚ := 169 / 15 * N ^ 5 * M - 29 / 16 * N ^ 4 * M ^ 2 - 7 / 9 * N ^ 3 * M ^ 3
    + 1 / 16 * N ^ 2 * M ^ 4 + 1 / 60 * N * M ^ 5 - 1 / 720 * M ^ 6 + 169 / 15 * N ^ 5
    + 1265 / 48 * N ^ 4 * M - 115 / 24 * N ^ 3 * M ^ 2 - 25 / 24 * N ^ 2 * M ^ 3
    + 5 / 48 * N * M ^ 4 + 1 / 240 * M ^ 5 + 169 / 6 * N ^ 4 + 2015 / 72 * N ^ 3 * M
    - 5 * N ^ 2 * M ^ 2 - 43 / 72 * N * M ^ 3 + 7 / 144 * M ^ 4 + 32 * N ^ 3
    + 255 / 16 * N ^ 2 * M - 41 / 16 * N * M ^ 2 - 5 / 48 * M ^ 3 + 119 / 6 * N ^ 2
    + 437 / 90 * N * M - 197 / 360 * M ^ 2 + 101 / 15 * N + 3 / 5 * M + 1

lemma sum5 (n m : ℕ) : ∑ u ∈ Finset.range (m + 1), g5 n (u : ℚ) = S5 n m := by
  induction m with
  | zero => simp only [zero_add, Finset.sum_range_one, Nat.cast_zero, g5, S5]; ring
  | succ m ih => rw [Finset.sum_range_succ, ih]; simp only [g5, S5]; push_cast; ring

lemma hg5 (n : ℕ) : ∀ w : ℤ, |w| ≤ n →
    (chainCnt (Finset.Icc (-(n : ℤ)) n) (Rd n) 5 w : ℚ) = g5 n ((|w| : ℤ) : ℚ) :=
  level_step n 4 (g4 n) (g5 n) (S4 n) (hg4 n) (sum4 n)
    (fun x => by simp only [g4, g5, S4]; ring)

/-- Continuations of length 6 from an entry of absolute value X. -/
def g6 (N X : ℚ) : ℚ := 2101 / 120 * N ^ 6 - 169 / 30 * N ^ 5 * X - 29 / 8 * N ^ 4 * X ^ 2
    + 7 / 18 * N ^ 3 * X ^ 3 + 1 / 8 * N ^ 2 * X ^ 4 - 1 / 120 * N * X ^ 5 - 1 / 720 * X ^ 6
    + 2101 / 40 * N ^ 5 - 169 / 12 * N ^ 4 * X - 29 / 4 * N ^ 3 * X ^ 2 + 7 / 12 * N ^ 2 * X ^ 3
    + 1 / 8 * N * X ^ 4 - 1 / 240 * X ^ 5 + 1753 / 24 * N ^ 4 - 295 / 18 * N ^ 3 * X
    - 13 / 2 * N ^ 2 * X ^ 2 + 29 / 72 * N * X ^ 3 + 7 / 144 * X ^ 4 + 1405 / 24 * N ^ 3
    - 21 / 2 * N ^ 2 * X - 23 / 8 * N * X ^ 2 + 5 / 48 * X ^ 3 + 569 / 20 * N ^ 2
    - 677 / 180 * N * X - 197 / 360 * X ^ 2 + 119 / 15 * N - 3 / 5 * X + 1

/-- The sum of g6 N u over u = 0..M. -/
def S6 (N M : ℚ) : ℚ := 2101 / 120 * N ^ 6 * M - 169 / 60 * N ^ 5 * M ^ 2
    - 29 / 24 * N ^ 4 * M ^ 3 + 7 / 72 * N ^ 3 * M ^ 4 + 1 / 40 * N ^ 2 * M ^ 5
    - 1 / 720 * N * M ^ 6 - 1 / 5040 * M ^ 7 + 2101 / 120 * N ^ 6 + 1193 / 24 * N ^ 5 * M
    - 425 / 48 * N ^ 4 * M ^ 2 - 20 / 9 * N ^ 3 * M ^ 3 + 5 / 24 * N ^ 2 * M ^ 4
    + 1 / 48 * N * M ^ 5 - 1 / 720 * M ^ 6 + 2101 / 40 * N ^ 5 + 3139 / 48 * N ^ 4 * M
    - 211 / 18 * N ^ 3 * M ^ 2 - 11 / 6 * N ^ 2 * M ^ 3 + 23 / 144 * N * M ^ 4 + 1 / 144 * M ^ 5
    + 1753 / 24 * N ^ 4 + 1769 / 36 * N ^ 3 * M - 401 / 48 * N ^ 2 * M ^ 2 - 103 / 144 * N * M ^ 3
    + 7 / 144 * M ^ 4 + 1405 / 24 * N ^ 3 + 1769 / 80 * N ^ 2 * M - 193 / 60 * N * M ^ 2
    - 41 / 360 * M ^ 3 + 569 / 20 * N ^ 2 + 401 / 72 * N * M - 197 / 360 * M ^ 2 + 119 / 15 * N
    + 17 / 28 * M + 1

lemma sum6 (n m : ℕ) : ∑ u ∈ Finset.range (m + 1), g6 n (u : ℚ) = S6 n m := by
  induction m with
  | zero => simp only [zero_add, Finset.sum_range_one, Nat.cast_zero, g6, S6]; ring
  | succ m ih => rw [Finset.sum_range_succ, ih]; simp only [g6, S6]; push_cast; ring

lemma hg6 (n : ℕ) : ∀ w : ℤ, |w| ≤ n →
    (chainCnt (Finset.Icc (-(n : ℤ)) n) (Rd n) 6 w : ℚ) = g6 n ((|w| : ℤ) : ℚ) :=
  level_step n 5 (g5 n) (g6 n) (S5 n) (hg5 n) (sum5 n)
    (fun x => by simp only [g5, g6, S5]; ring)

theorem a_eq (n : ℕ) :
    a n = ∑ v ∈ Finset.Icc (-(n : ℤ)) n, chainCnt (Finset.Icc (-(n : ℤ)) n) (Rd n) 6 v :=
  card_chain _ (Rd n) 6

/-- Hardin's polynomial, for every n. -/
theorem poly (n : ℕ) : (a n : ℚ) = 17141 / 630 * (n : ℚ) ^ 7 + 17141 / 180 * (n : ℚ) ^ 6
    + 28177 / 180 * (n : ℚ) ^ 5 + 2759 / 18 * (n : ℚ) ^ 4 + 17299 / 180 * (n : ℚ) ^ 3
    + 6929 / 180 * (n : ℚ) ^ 2 + 1921 / 210 * (n : ℚ) + 1 := by
  rw [a_eq]
  push_cast
  rw [total_split n 6 (fun x : ℤ => g6 n (x : ℚ)) (hg6 n)]
  simp only [Int.cast_natCast, Int.cast_zero]
  rw [sum6 n n]
  simp only [g6, S6]
  ring

lemma val (n v : ℕ) (h : 17141 / 630 * (n : ℚ) ^ 7 + 17141 / 180 * (n : ℚ) ^ 6
    + 28177 / 180 * (n : ℚ) ^ 5 + 2759 / 18 * (n : ℚ) ^ 4 + 17299 / 180 * (n : ℚ) ^ 3
    + 6929 / 180 * (n : ℚ) ^ 2 + 1921 / 210 * (n : ℚ) + 1 = v) : a n = v := by
  have e := poly n
  rw [h] at e
  exact_mod_cast e

/-- The values a(0..8). -/
theorem small : a 0 = 1 ∧ a 1 = 577 ∧ a 2 = 17981 ∧ a 3 = 182349 ∧ a 4 = 1042167 ∧ a 5 = 4211559 ∧
    a 6 = 13497523 ∧ a 7 = 36644243 ∧ a 8 = 87831605 :=
  ⟨val 0 1 (by norm_num), val 1 577 (by norm_num), val 2 17981 (by norm_num),
    val 3 182349 (by norm_num), val 4 1042167 (by norm_num), val 5 4211559 (by norm_num),
    val 6 13497523 (by norm_num), val 7 36644243 (by norm_num), val 8 87831605 (by norm_num)⟩

/-- Barker's recurrence, for n > 8. -/
theorem recurrence (n : ℕ) (hn : 8 < n) :
    (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 9 := ⟨n - 9, by omega⟩
  simp only [show q + 9 - 1 = q + 8 by omega, show q + 9 - 2 = q + 7 by omega, show q + 9 - 3 = q
    + 6 by omega, show q + 9 - 4 = q + 5 by omega, show q + 9 - 5 = q + 4 by omega, show q + 9
    - 6 = q + 3 by omega, show q + 9 - 7 = q + 2 by omega, show q + 9 - 8 = q + 1 by omega]
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [poly (q + 9), poly (q + 8), poly (q + 7), poly (q + 6), poly (q + 5), poly (q + 4), poly (q
    + 3), poly (q + 2), poly (q + 1)]
  push_cast
  ring

/-- Barker's g.f., as A(x) (1 - x)^8 = N(x) in Z[[x]]. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 8 =
    X * (577 + 13365 * X + 54657 * X ^ 2 + 54531 * X ^ 3 + 13449 * X ^ 4 + 541 * X ^ 5 + 9 * X ^ 6 - X ^ 7) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 8 =
      A - C 8 * (A * X ^ 1) + C 28 * (A * X ^ 2) - C 56 * (A * X ^ 3) + C 70 * (A * X ^ 4)
        - C 56 * (A * X ^ 5) + C 28 * (A * X ^ 6) - C 8 * (A * X ^ 7) + A * X ^ 8 := by
    simp only [map_ofNat]; ring
  have e2 : (X * (577 + 13365 * X + 54657 * X ^ 2 + 54531 * X ^ 3 + 13449 * X ^ 4 + 541 * X ^ 5 + 9 * X ^ 6 - X ^ 7) : ℤ⟦X⟧) =
      X ^ 1 * C 577 + X ^ 2 * C 13365 + X ^ 3 * C 54657 + X ^ 4 * C 54531 + X ^ 5 * C 13449
        + X ^ 6 * C 541 + X ^ 7 * C 9 - X ^ 8 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  have v := small
  rcases Nat.lt_or_ge n 9 with hn | hn
  · interval_cases n <;> simp_all
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 9 := ⟨n - 9, by omega⟩
    have h := recurrence (q + 9) (by omega)
    simp only [show q + 9 - 1 = q + 8 by omega, show q + 9 - 2 = q + 7 by omega, show q + 9
      - 3 = q + 6 by omega, show q + 9 - 4 = q + 5 by omega, show q + 9 - 5 = q + 4 by omega,
      show q + 9 - 6 = q + 3 by omega, show q + 9 - 7 = q + 2 by omega, show q + 9 - 8 = q
      + 1 by omega] at h ⊢
    simp only [show ¬ q + 9 = 0 by omega, show ¬ q + 8 = 0 by omega, show ¬ q + 7 = 0 by omega,
      show ¬ q + 6 = 0 by omega, show ¬ q + 5 = 0 by omega, show ¬ q + 4 = 0 by omega, show ¬ q
      + 3 = 0 by omega, show ¬ q + 2 = 0 by omega, show ¬ q + 1 = 0 by omega, show 1 ≤ q
      + 9 by omega, show 2 ≤ q + 9 by omega, show 3 ≤ q + 9 by omega, show 4 ≤ q + 9 by omega,
      show 5 ≤ q + 9 by omega, show 6 ≤ q + 9 by omega, show 7 ≤ q + 9 by omega, show 8 ≤ q
      + 9 by omega, show ¬ q + 9 = 1 by omega, show ¬ q + 9 = 2 by omega, show ¬ q
      + 9 = 3 by omega, show ¬ q + 9 = 4 by omega, show ¬ q + 9 = 5 by omega, show ¬ q
      + 9 = 6 by omega, show ¬ q + 9 = 7 by omega, show ¬ q + 9 = 8 by omega, if_true, if_false]
    rw [h]
    ring

/-- Controls: the entry's terms a(1..21). -/
theorem controls : a 1 = 577 ∧ a 2 = 17981 ∧ a 3 = 182349 ∧ a 4 = 1042167 ∧ a 5 = 4211559 ∧
    a 6 = 13497523 ∧ a 7 = 36644243 ∧ a 8 = 87831605 ∧ a 9 = 191065045 ∧ a 10 = 384593857 ∧
    a 11 = 726495089 ∧ a 12 = 1301560155 ∧ a 13 = 2229621291 ∧ a 14 = 3675454983 ∧
    a 15 = 5860399495 ∧ a 16 = 9075823625 ∧ a 17 = 13698583817 ∧ a 18 = 20208606757 ∧
    a 19 = 29208734581 ∧ a 20 = 41446969823 ∧ a 21 = 57841257231 :=
  ⟨val 1 577 (by norm_num), val 2 17981 (by norm_num), val 3 182349 (by norm_num),
    val 4 1042167 (by norm_num), val 5 4211559 (by norm_num), val 6 13497523 (by norm_num),
    val 7 36644243 (by norm_num), val 8 87831605 (by norm_num), val 9 191065045 (by norm_num),
    val 10 384593857 (by norm_num), val 11 726495089 (by norm_num),
    val 12 1301560155 (by norm_num), val 13 2229621291 (by norm_num),
    val 14 3675454983 (by norm_num), val 15 5860399495 (by norm_num),
    val 16 9075823625 (by norm_num), val 17 13698583817 (by norm_num),
    val 18 20208606757 (by norm_num), val 19 29208734581 (by norm_num),
    val 20 41446969823 (by norm_num), val 21 57841257231 (by norm_num)⟩

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 8 =
      X * (577 + 13365 * X + 54657 * X ^ 2 + 54531 * X ^ 3 + 13449 * X ^ 4 + 541 * X ^ 5 + 9 * X ^ 6 - X ^ 7) ∧
    (∀ n : ℕ, 8 < n →
      (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8)) :=
  ⟨gf, recurrence⟩

end OMA.S_oeis_a201046

theorem OMA.solution : type_of% @OMA.S_oeis_a201046.main :=
  OMA.S_oeis_a201046.conjecture

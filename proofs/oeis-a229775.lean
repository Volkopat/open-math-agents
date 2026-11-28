import OMAStatements.S_oeis_a229775

namespace OMA.S_oeis_a229775

open PowerSeries





section Patterns

variable {k : ℕ} (P : (Fin k → ℕ) → Prop) [DecidablePred P]

/-- The number of surjective patterns g : Fin k → Fin j with the property. -/
def pc (j : ℕ) : ℕ :=
  (Finset.univ.filter (fun g : Fin k → Fin j => Function.Surjective g ∧ P (fun i => (g i : ℕ)))).card

variable {P}

/-- The arrays with image S correspond to the surjective patterns onto Fin S.card. -/
theorem fiber_card (hP : ∀ (m : ℕ) (e₁ e₂ : Fin m ↪o ℕ) (g : Fin k → Fin m),
      P (fun i => e₁ (g i)) ↔ P (fun i => e₂ (g i)))
    {n : ℕ} (S : Finset (Fin (n + 1))) :
    ((Finset.univ.filter (fun x : Fin k → Fin (n + 1) => P (fun i => (x i : ℕ)))).filter
      (fun x => Finset.univ.image x = S)).card = pc P S.card := by
  symm
  unfold pc
  apply Finset.card_bij (fun g _ => fun i => S.orderEmbOfFin rfl (g i))
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    obtain ⟨hs, hp⟩ := hg
    refine ⟨?_, ?_⟩
    · have h := hP S.card ((S.orderEmbOfFin rfl).trans (Fin.valOrderEmb (n + 1)))
        (Fin.valOrderEmb S.card) g
      simp only [RelEmbedding.trans_apply, Fin.valOrderEmb_apply] at h
      exact h.2 hp
    · ext y
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩
        exact Finset.orderEmbOfFin_mem S rfl (g i)
      · intro hy
        have hy' : y ∈ Set.range (S.orderEmbOfFin rfl) := by
          rw [Finset.range_orderEmbOfFin]
          exact hy
        obtain ⟨j, hj⟩ := hy'
        obtain ⟨i, hi⟩ := hs j
        exact ⟨i, by rw [hi, hj]⟩
  · intro g₁ _ g₂ _ h
    funext i
    exact (S.orderEmbOfFin rfl).injective (congrFun h i)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨hp, himg⟩ := hx
    have hmem : ∀ i, x i ∈ S := fun i => by
      rw [← himg]
      exact Finset.mem_image_of_mem x (Finset.mem_univ i)
    have hx_eq : ∀ i, S.orderEmbOfFin rfl ((S.orderIsoOfFin rfl).symm ⟨x i, hmem i⟩) = x i := by
      intro i
      rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
    refine ⟨fun i => (S.orderIsoOfFin rfl).symm ⟨x i, hmem i⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · intro j
        have hj : S.orderEmbOfFin rfl j ∈ Finset.univ.image x := by
          rw [himg]
          exact Finset.orderEmbOfFin_mem S rfl j
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hj
        obtain ⟨i, hi⟩ := hj
        refine ⟨i, ?_⟩
        apply (S.orderEmbOfFin rfl).injective
        show S.orderEmbOfFin rfl ((S.orderIsoOfFin rfl).symm ⟨x i, hmem i⟩) = S.orderEmbOfFin rfl j
        rw [hx_eq]
        exact hi
      · have h := hP S.card ((S.orderEmbOfFin rfl).trans (Fin.valOrderEmb (n + 1)))
          (Fin.valOrderEmb S.card) (fun i => (S.orderIsoOfFin rfl).symm ⟨x i, hmem i⟩)
        simp only [RelEmbedding.trans_apply, Fin.valOrderEmb_apply, hx_eq] at h
        exact h.1 hp
    · funext i
      exact hx_eq i

/-- The count of arrays as a sum over pattern sizes. -/
theorem count_eq (hP : ∀ (m : ℕ) (e₁ e₂ : Fin m ↪o ℕ) (g : Fin k → Fin m),
      P (fun i => e₁ (g i)) ↔ P (fun i => e₂ (g i))) (n : ℕ) :
    (Finset.univ.filter (fun x : Fin k → Fin (n + 1) => P (fun i => (x i : ℕ)))).card =
      ∑ j ∈ Finset.range (k + 1), (n + 1).choose j * pc P j := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x : Fin k → Fin (n + 1) => Finset.univ.image x)
    (t := Finset.univ) (by intro x _; simp)]
  refine (Finset.sum_congr rfl (fun S _ => fiber_card hP S)).trans ?_
  rw [← Finset.powerset_univ, Finset.sum_powerset_apply_card (f := pc P)]
  simp only [Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hz : ∀ j, k < j → pc P j = 0 := by
    intro j hj
    unfold pc
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro g - ⟨hs, -⟩
    have := Fintype.card_le_of_surjective g hs
    simp only [Fintype.card_fin] at this
    omega
  have e1 : ∑ m ∈ Finset.range (n + 1 + 1), (n + 1).choose m * pc P m =
      ∑ m ∈ Finset.range (n + k + 2), (n + 1).choose m * pc P m := by
    apply Finset.sum_subset (Finset.range_subset_range.2 (by omega))
    intro m _ hm
    simp only [Finset.mem_range, not_lt] at hm
    rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]
  have e2 : ∑ m ∈ Finset.range (k + 1), (n + 1).choose m * pc P m =
      ∑ m ∈ Finset.range (n + k + 2), (n + 1).choose m * pc P m := by
    apply Finset.sum_subset (Finset.range_subset_range.2 (by omega))
    intro m _ hm
    simp only [Finset.mem_range, not_lt] at hm
    rw [hz m (by omega), mul_zero]
  rw [e1, e2]

end Patterns

section Head

variable {k : ℕ} (P : (Fin (k + 1) → ℕ) → Prop) [DecidablePred P]

/-- Splitting a count of functions on Fin (k + 1) by the value at 0. -/
theorem card_by_head {j : ℕ} (Q : (Fin (k + 1) → Fin j) → Prop) [DecidablePred Q] :
    (Finset.univ.filter Q).card =
      ∑ v : Fin j, (Finset.univ.filter (fun h : Fin k → Fin j => Q (Fin.cons v h))).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g : Fin (k + 1) → Fin j => g 0) (t := Finset.univ)
    (by intro x _; simp)]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  symm
  apply Finset.card_bij (fun h _ => (Fin.cons v h : Fin (k + 1) → Fin j))
  · intro h hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
    exact ⟨hh, by simp⟩
  · intro h₁ _ h₂ _ e
    simpa using congrArg Fin.tail e
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    obtain ⟨hq, h0⟩ := hg
    refine ⟨Fin.tail g, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← h0, Fin.cons_self_tail]
      exact hq
    · show Fin.cons v (Fin.tail g) = g
      rw [← h0, Fin.cons_self_tail]

/-- The number of surjective patterns g : Fin (k + 1) → Fin j with the property and g 0 = v. -/
def pcs (j : ℕ) (v : Fin j) : ℕ :=
  (Finset.univ.filter (fun h : Fin k → Fin j =>
    Function.Surjective (Fin.cons v h : Fin (k + 1) → Fin j) ∧
      P (fun i => ((Fin.cons v h : Fin (k + 1) → Fin j) i : ℕ)))).card

theorem pc_succ (j : ℕ) : pc P j = ∑ v : Fin j, pcs P j v := by
  unfold pc pcs
  exact card_by_head (fun g : Fin (k + 1) → Fin j => Function.Surjective g ∧ P (fun i => (g i : ℕ)))

end Head

lemma ch2 (n : ℕ) : ((n + 1).choose 2 : ℚ) = (n + 1) * n / 2 := by
  induction n with
  | zero => simp [Nat.choose]
  | succ m ih =>
    have h : (m + 1 + 1).choose 2 = (m + 1).choose 1 + (m + 1).choose 2 :=
      Nat.choose_succ_succ' (m + 1) 1
    rw [h, Nat.cast_add, ih, Nat.choose_one_right]
    push_cast
    ring

lemma ch3 (n : ℕ) : ((n + 1).choose 3 : ℚ) = (n + 1) * n * (n - 1) / 6 := by
  induction n with
  | zero => simp [Nat.choose]
  | succ m ih =>
    have h : (m + 1 + 1).choose 3 = (m + 1).choose 2 + (m + 1).choose 3 :=
      Nat.choose_succ_succ' (m + 1) 2
    rw [h, Nat.cast_add, ih, ch2]
    push_cast
    ring

lemma ch4 (n : ℕ) : ((n + 1).choose 4 : ℚ) = (n + 1) * n * (n - 1) * (n - 2) / 24 := by
  induction n with
  | zero => simp [Nat.choose]
  | succ m ih =>
    have h : (m + 1 + 1).choose 4 = (m + 1).choose 3 + (m + 1).choose 4 :=
      Nat.choose_succ_succ' (m + 1) 3
    rw [h, Nat.cast_add, ih, ch3]
    push_cast
    ring

lemma ch5 (n : ℕ) : ((n + 1).choose 5 : ℚ) = (n + 1) * n * (n - 1) * (n - 2) * (n - 3) / 120 := by
  induction n with
  | zero => simp [Nat.choose]
  | succ m ih =>
    have h : (m + 1 + 1).choose 5 = (m + 1).choose 4 + (m + 1).choose 5 :=
      Nat.choose_succ_succ' (m + 1) 4
    rw [h, Nat.cast_add, ih, ch4]
    push_cast
    ring

lemma ch6 (n : ℕ) : ((n + 1).choose 6 : ℚ) = (n + 1) * n * (n - 1) * (n - 2) * (n - 3) * (n - 4) / 720 := by
  induction n with
  | zero => simp [Nat.choose]
  | succ m ih =>
    have h : (m + 1 + 1).choose 6 = (m + 1).choose 5 + (m + 1).choose 6 :=
      Nat.choose_succ_succ' (m + 1) 5
    rw [h, Nat.cast_add, ih, ch5]
    push_cast
    ring

lemma ch7 (n : ℕ) : ((n + 1).choose 7 : ℚ) = (n + 1) * n * (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n - 5) / 5040 := by
  induction n with
  | zero => simp [Nat.choose]
  | succ m ih =>
    have h : (m + 1 + 1).choose 7 = (m + 1).choose 6 + (m + 1).choose 7 :=
      Nat.choose_succ_succ' (m + 1) 6
    rw [h, Nat.cast_add, ih, ch6]
    push_cast
    ring

lemma ch8 (n : ℕ) : ((n + 1).choose 8 : ℚ) = (n + 1) * n * (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n - 5) * (n - 6) / 40320 := by
  induction n with
  | zero => simp [Nat.choose]
  | succ m ih =>
    have h : (m + 1 + 1).choose 8 = (m + 1).choose 7 + (m + 1).choose 8 :=
      Nat.choose_succ_succ' (m + 1) 7
    rw [h, Nat.cast_add, ih, ch7]
    push_cast
    ring

lemma ch9 (n : ℕ) : ((n + 1).choose 9 : ℚ) = (n + 1) * n * (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n - 5) * (n - 6) * (n - 7) / 362880 := by
  induction n with
  | zero => simp [Nat.choose]
  | succ m ih =>
    have h : (m + 1 + 1).choose 9 = (m + 1).choose 8 + (m + 1).choose 9 :=
      Nat.choose_succ_succ' (m + 1) 8
    rw [h, Nat.cast_add, ih, ch8]
    push_cast
    ring

lemma hP : ∀ (m : ℕ) (e₁ e₂ : Fin m ↪o ℕ) (g : Fin 9 → Fin m),
    good (fun i => e₁ (g i)) ↔ good (fun i => e₂ (g i)) := by
  intro m e₁ e₂ g
  simp only [good, lexLE, OrderEmbedding.lt_iff_lt, OrderEmbedding.le_iff_le,
    EmbeddingLike.apply_eq_iff_eq]

section LexCount

/-- The state of a row-major reading of a 3 X 3 array: the last three entries and the
lexicographic comparisons so far of rows 0 and 1, rows 1 and 2, columns 0 and 1, columns 1 and 2. -/
structure St where
  a : ℕ
  b : ℕ
  c : ℕ
  o1 : Ordering
  o2 : Ordering
  o3 : Ordering
  o4 : Ordering

/-- Reading the entry v at position p (row p / 3, column p % 3). With rev the column comparisons
are reversed (columns compared right to left). -/
def step (rev : Bool) (p : ℕ) (s : St) (v : ℕ) : St :=
  ⟨s.b, s.c, v,
    if p / 3 = 1 then s.o1.then (compare s.a v) else s.o1,
    if p / 3 = 2 then s.o2.then (compare s.a v) else s.o2,
    if p % 3 = 1 then s.o3.then (if rev then compare v s.c else compare s.c v) else s.o3,
    if p % 3 = 2 then s.o4.then (if rev then compare v s.c else compare s.c v) else s.o4⟩

/-- Some comparison has gone the wrong way. -/
def bad (s : St) : Bool := s.o1 == .gt || s.o2 == .gt || s.o3 == .gt || s.o4 == .gt

def run (rev : Bool) : ℕ → St → List ℕ → St
  | _, s, [] => s
  | p, s, v :: t => run rev (p + 1) (step rev p s v) t

lemma then_gt (o : Ordering) : Ordering.gt.then o = .gt := rfl

lemma bad_step (rev : Bool) (p : ℕ) (s : St) (v : ℕ) (h : bad s = true) :
    bad (step rev p s v) = true := by
  obtain ⟨a, b, c, o1, o2, o3, o4⟩ := s
  simp only [bad, Bool.or_eq_true, beq_iff_eq] at h ⊢
  simp only [step]
  rcases h with ((h | h) | h) | h <;> subst h <;> simp [then_gt]

lemma bad_run (rev : Bool) : ∀ (l : List ℕ) (p : ℕ) (s : St), bad s = true → bad (run rev p s l) = true
  | [], _, _, h => h
  | v :: t, p, s, h => bad_run rev t (p + 1) (step rev p s v) (bad_step rev p s v h)

/-- The number of h : Fin L → Fin N whose reading from position p and state s never goes wrong.
The kernel evaluates each value once. -/
def dpL (rev : Bool) (N : ℕ) : (L p : ℕ) → St → ℕ
  | 0, _, s => if bad s then 0 else 1
  | L + 1, p, s => if bad s then 0 else ∑ v : Fin N, dpL rev N L (p + 1) (step rev p s v)

theorem dpL_eq (rev : Bool) (N : ℕ) : ∀ (L p : ℕ) (s : St), dpL rev N L p s =
    (Finset.univ.filter (fun h : Fin L → Fin N =>
      bad (run rev p s (List.ofFn (fun i => (h i : ℕ)))) = false)).card
  | 0, p, s => by
    rw [dpL]
    have hu : (Finset.univ : Finset (Fin 0 → Fin N)) = {Fin.elim0} := by
      ext g
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      funext i
      exact i.elim0
    rw [hu, Finset.filter_singleton]
    by_cases hb : bad s = true <;> simp [run, hb]
  | L + 1, p, s => by
    rw [dpL]
    by_cases hb : bad s = true
    · rw [if_pos hb]
      symm
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro h _ hc
      have := bad_run rev (List.ofFn (fun i => (h i : ℕ))) p s hb
      rw [this] at hc
      exact Bool.noConfusion hc
    · rw [if_neg hb, card_by_head]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [dpL_eq rev N L (p + 1) (step rev p s v)]
      congr 1
      ext h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [List.ofFn_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, run]

/-- The initial state. -/
def s0 : St := ⟨0, 0, 0, .eq, .eq, .eq, .eq⟩

/-- Continue with the comparison o, or stop with 0 if it has gone the wrong way. -/
def mk (o : Ordering) (f : Ordering → ℕ) : ℕ :=
  match o with
  | .lt => f .lt
  | .eq => f .eq
  | .gt => 0

lemma mk_eq (o : Ordering) (f : Ordering → ℕ) : mk o f = if o = .gt then 0 else f o := by
  cases o <;> rfl

lemma cmp_eq (a b : ℕ) :
    compare a b = if a < b then Ordering.lt else if a = b then Ordering.eq else Ordering.gt := rfl

/-- compare on ℕ through the machine comparisons, which the kernel evaluates directly. -/
def cmpN (a b : ℕ) : Ordering := if Nat.blt a b then .lt else if Nat.beq a b then .eq else .gt

lemma cmpN_eq (a b : ℕ) : cmpN a b = compare a b := by
  rw [cmpN, cmp_eq]
  by_cases h : a < b
  · simp [h, Nat.blt_eq]
  · by_cases h' : a = b
    · subst h'
      simp
    · simp [h, h', Nat.blt_eq, Nat.beq_eq]

/-- f 0 + ... + f (n - 1), by recursion on n. -/
def sumN (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumN f n + f n

lemma sumN_eq (f : ℕ → ℕ) (n : ℕ) : sumN f n = ∑ v ∈ Finset.range n, f v := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumN, ih, Finset.sum_range_succ]

/-- Whether the entry three back can still be read at position q (as the entry above, while that
row comparison is undecided); needB and needC do the same for the entries two back and one back
(one back is also read as the entry to the left while that column comparison is undecided). -/
def needA (q : ℕ) (o1 o2 : Ordering) : Bool := (q / 3 == 1 && o1 == .eq) || (q / 3 == 2 && o2 == .eq)

def needB (q : ℕ) (o1 o2 : Ordering) : Bool := needA (q + 1) o1 o2

def needC (q : ℕ) (o1 o2 o3 o4 : Ordering) : Bool :=
  (q % 3 == 1 && o3 == .eq) || (q % 3 == 2 && o4 == .eq) || needA (q + 2) o1 o2

/-- Continue with x if it can still be read, else with 0 (evaluated before the call). -/
def pick (c : Bool) (x : ℕ) (f : ℕ → ℕ) : ℕ :=
  match c with
  | true => f x
  | false => f 0

lemma pick_eq (c : Bool) (x : ℕ) (f : ℕ → ℕ) : pick c x f = f (if c = true then x else 0) := by
  cases c <;> rfl

/-- dpL with the state as separate arguments: every updated comparison is matched to a
constructor before the recursive call and the entries that can no longer be read are replaced by
0, so equal states give equal calls and the kernel evaluates each state once. -/
def dpF (rev : Bool) (N : ℕ) : (L p a b c : ℕ) → Ordering → Ordering → Ordering → Ordering → ℕ
  | 0, _, _, _, _, _, _, _, _ => 1
  | L + 1, p, a, b, c, o1, o2, o3, o4 => sumN (fun v =>
      mk (if p / 3 = 1 then o1.then (cmpN a v) else o1) (fun o1' =>
      mk (if p / 3 = 2 then o2.then (cmpN a v) else o2) (fun o2' =>
      mk (if p % 3 = 1 then o3.then (if rev then cmpN v c else cmpN c v) else o3)
        (fun o3' =>
      mk (if p % 3 = 2 then o4.then (if rev then cmpN v c else cmpN c v) else o4)
        (fun o4' => pick (needA (p + 1) o1' o2') b (fun a'' =>
          pick (needB (p + 1) o1' o2') c (fun b'' =>
          pick (needC (p + 1) o1' o2' o3' o4') v (fun c'' =>
          dpF rev N L (p + 1) a'' b'' c'' o1' o2' o3' o4')))))))) N

lemma dpL_bad (rev : Bool) (N L p : ℕ) (s : St) (h : bad s = true) : dpL rev N L p s = 0 := by
  cases L <;> simp [dpL, h]

/-- An updated comparison that is still undecided was undecided before. -/
lemma eq_of_upd (c : Prop) [Decidable c] (o x : Ordering) (h : (if c then o.then x else o) = .eq) :
    o = .eq := by
  by_cases hc : c
  · rw [if_pos hc] at h
    cases o <;> simp_all [Ordering.then]
  · rwa [if_neg hc] at h

/-- The comparison update gives the same result from any entry that agrees with the true one
whenever the comparison is undecided. -/
lemma upd_congr (c : Prop) [Decidable c] (o x x' : Ordering) (ho : o ≠ .gt)
    (h : c → o = .eq → x' = x) : (if c then o.then x' else o) = (if c then o.then x else o) := by
  by_cases hc : c
  · rw [if_pos hc, if_pos hc]
    cases o
    · rfl
    · rw [h hc rfl]
    · exact absurd rfl ho
  · rw [if_neg hc, if_neg hc]

theorem dpF_eq (rev : Bool) (N : ℕ) : ∀ (L p a' b' c' a b c : ℕ) (o1 o2 o3 o4 : Ordering),
    o1 ≠ .gt → o2 ≠ .gt → o3 ≠ .gt → o4 ≠ .gt →
    (needA p o1 o2 = true → a' = a) → (needB p o1 o2 = true → b' = b) →
    (needC p o1 o2 o3 o4 = true → c' = c) →
    dpF rev N L p a' b' c' o1 o2 o3 o4 = dpL rev N L p ⟨a, b, c, o1, o2, o3, o4⟩
  | 0, p, a', b', c', a, b, c, o1, o2, o3, o4, h1, h2, h3, h4, _, _, _ => by
    simp [dpF, dpL, bad, h1, h2, h3, h4]
  | L + 1, p, a', b', c', a, b, c, o1, o2, o3, o4, h1, h2, h3, h4, ha, hb', hc => by
    have hb : bad ⟨a, b, c, o1, o2, o3, o4⟩ = false := by simp [bad, h1, h2, h3, h4]
    rw [dpF, dpL, hb, if_neg Bool.false_ne_true, sumN_eq,
      Fin.sum_univ_eq_sum_range (fun v => dpL rev N L (p + 1) (step rev p ⟨a, b, c, o1, o2, o3, o4⟩ v)) N]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    simp only [cmpN_eq, pick_eq]
    rw [upd_congr (p / 3 = 1) o1 (compare a v) (compare a' v) h1
        (fun hp ho => by rw [ha (by simp [needA, hp, ho])]),
      upd_congr (p / 3 = 2) o2 (compare a v) (compare a' v) h2
        (fun hp ho => by rw [ha (by simp [needA, hp, ho])]),
      upd_congr (p % 3 = 1) o3 (if rev = true then compare v c else compare c v)
        (if rev = true then compare v c' else compare c' v) h3
        (fun hp ho => by rw [hc (by simp [needC, hp, ho])]),
      upd_congr (p % 3 = 2) o4 (if rev = true then compare v c else compare c v)
        (if rev = true then compare v c' else compare c' v) h4
        (fun hp ho => by rw [hc (by simp [needC, hp, ho])])]
    simp only [mk_eq, step]
    have e1 := eq_of_upd (p / 3 = 1) o1 (compare a v)
    have e2 := eq_of_upd (p / 3 = 2) o2 (compare a v)
    generalize (if p / 3 = 1 then o1.then (compare a v) else o1) = O1 at e1 ⊢
    generalize (if p / 3 = 2 then o2.then (compare a v) else o2) = O2 at e2 ⊢
    generalize (if p % 3 = 1 then o3.then (if rev = true then compare v c else compare c v)
      else o3) = O3
    generalize (if p % 3 = 2 then o4.then (if rev = true then compare v c else compare c v)
      else o4) = O4
    have hA : needA (p + 1) O1 O2 = true → (if needA (p + 1) O1 O2 = true then b' else 0) = b := by
      intro h
      rw [if_pos h]
      apply hb'
      simp only [needB, needA, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h ⊢
      rcases h with ⟨q1, q2⟩ | ⟨q1, q2⟩
      · exact Or.inl ⟨q1, e1 q2⟩
      · exact Or.inr ⟨q1, e2 q2⟩
    have hB : needB (p + 1) O1 O2 = true → (if needB (p + 1) O1 O2 = true then c' else 0) = c := by
      intro h
      rw [if_pos h]
      apply hc
      simp only [needB, needC, needA, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
        show p + 1 + 1 = p + 2 by ring] at h ⊢
      rcases h with ⟨q1, q2⟩ | ⟨q1, q2⟩
      · exact Or.inr (Or.inl ⟨q1, e1 q2⟩)
      · exact Or.inr (Or.inr ⟨q1, e2 q2⟩)
    have hC : needC (p + 1) O1 O2 O3 O4 = true →
        (if needC (p + 1) O1 O2 O3 O4 = true then v else 0) = v := fun h => if_pos h
    by_cases g1 : O1 = .gt
    · rw [if_pos g1]
      exact (dpL_bad _ _ _ _ _ (by simp [bad, g1])).symm
    rw [if_neg g1]
    by_cases g2 : O2 = .gt
    · rw [if_pos g2]
      exact (dpL_bad _ _ _ _ _ (by simp [bad, g2])).symm
    rw [if_neg g2]
    by_cases g3 : O3 = .gt
    · rw [if_pos g3]
      exact (dpL_bad _ _ _ _ _ (by simp [bad, g3])).symm
    rw [if_neg g3]
    by_cases g4 : O4 = .gt
    · rw [if_pos g4]
      exact (dpL_bad _ _ _ _ _ (by simp [bad, g4])).symm
    rw [if_neg g4]
    exact dpF_eq rev N L (p + 1) _ _ _ b c v O1 O2 O3 O4 g1 g2 g3 g4 hA hB hC

/-- Lexicographic comparison of two triples as a composite of comparisons. -/
lemma lex_iff (a0 a1 a2 b0 b1 b2 : ℕ) :
    (a0 < b0 ∨ (a0 = b0 ∧ (a1 < b1 ∨ (a1 = b1 ∧ a2 ≤ b2)))) ↔
      ((compare a0 b0).then (compare a1 b1)).then (compare a2 b2) ≠ .gt := by
  rw [cmp_eq a0 b0, cmp_eq a1 b1, cmp_eq a2 b2]
  split_ifs <;> simp only [Ordering.then, ne_eq, reduceCtorEq, not_false_eq_true, not_true_eq_false,
    iff_true, iff_false] <;> omega

/-- The arrays counted through dpF: all nine entries are read. -/
theorem count_eq_dpL (rev : Bool) (P : (Fin 9 → ℕ) → Prop) [DecidablePred P]
    (hP : ∀ x, P x ↔ bad (run rev 0 s0 (List.ofFn x)) = false) (n : ℕ) :
    (Finset.univ.filter (fun x : Fin 9 → Fin (n + 1) => P (fun i => (x i : ℕ)))).card =
      dpF rev (n + 1) 9 0 0 0 0 .eq .eq .eq .eq := by
  rw [dpF_eq rev (n + 1) 9 0 0 0 0 0 0 0 .eq .eq .eq .eq (by decide) (by decide) (by decide)
    (by decide) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)]
  rw [show (⟨0, 0, 0, .eq, .eq, .eq, .eq⟩ : St) = s0 from rfl, dpL_eq]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hP]

end LexCount

lemma hW (x : Fin 9 → ℕ) : good x ↔ bad (run true 0 s0 (List.ofFn x)) = false := by
  have e : run true 0 s0 (List.ofFn x) = ⟨x 6, x 7, x 8,
      ((compare (x 0) (x 3)).then (compare (x 1) (x 4))).then (compare (x 2) (x 5)),
      ((compare (x 3) (x 6)).then (compare (x 4) (x 7))).then (compare (x 5) (x 8)),
      ((compare (x 1) (x 0)).then (compare (x 4) (x 3))).then (compare (x 7) (x 6)),
      ((compare (x 2) (x 1)).then (compare (x 5) (x 4))).then (compare (x 8) (x 7))⟩ := rfl
  rw [e]
  simp only [good, lexLE, lex_iff, bad, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
    and_assoc]

lemma av0 : a 0 = 1 := by
  unfold a
  rw [count_eq_dpL true good hW 0]
  decide +kernel

lemma av1 : a 1 = 20 := by
  unfold a
  rw [count_eq_dpL true good hW 1]
  decide +kernel

lemma av2 : a 2 = 322 := by
  unfold a
  rw [count_eq_dpL true good hW 2]
  decide +kernel

lemma av3 : a 3 = 3232 := by
  unfold a
  rw [count_eq_dpL true good hW 3]
  decide +kernel

lemma av4 : a 4 = 21331 := by
  unfold a
  rw [count_eq_dpL true good hW 4]
  decide +kernel

lemma av5 : a 5 = 103222 := by
  unfold a
  rw [count_eq_dpL true good hW 5]
  decide +kernel

lemma av6 : a 6 = 397460 := by
  unfold a
  rw [count_eq_dpL true good hW 6]
  decide +kernel

lemma av7 : a 7 = 1287672 := by
  unfold a
  rw [count_eq_dpL true good hW 7]
  decide +kernel

lemma av8 : a 8 = 3647349 := by
  unfold a
  rw [count_eq_dpL true good hW 8]
  decide +kernel

lemma pc0 : pc good 0 = 0 := by
  decide +kernel

/-- Solving count_eq at n = 0..k-1 for the pattern counts, with the counts as variables. -/
lemma lin (p : ℕ → ℕ) (h0 : p 0 = 0) (e0 : 1 = ∑ j ∈ Finset.range (9 + 1), (0 + 1).choose j * p j)
    (e1 : 20 = ∑ j ∈ Finset.range (9 + 1), (1 + 1).choose j * p j) (e2 : 322 = ∑ j ∈ Finset.range
    (9 + 1), (2 + 1).choose j * p j) (e3 : 3232 = ∑ j ∈ Finset.range (9 + 1), (3 + 1).choose j * p
    j) (e4 : 21331 = ∑ j ∈ Finset.range (9 + 1), (4 + 1).choose j * p j) (e5 : 103222 = ∑ j ∈
    Finset.range (9 + 1), (5 + 1).choose j * p j) (e6 : 397460 = ∑ j ∈ Finset.range (9 + 1), (6 +
    1).choose j * p j) (e7 : 1287672 = ∑ j ∈ Finset.range (9 + 1), (7 + 1).choose j * p j) (e8 :
    3647349 = ∑ j ∈ Finset.range (9 + 1), (8 + 1).choose j * p j) : p 0 = 0 ∧ p 1 = 1 ∧ p 2 = 18 ∧ p
    3 = 265 ∧ p 4 = 2060 ∧ p 5 = 8196 ∧ p 6 = 17570 ∧ p 7 = 20594 ∧ p 8 = 12432 ∧ p 9 = 3024 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at e0 e1 e2 e3 e4 e5 e6 e7 e8
  norm_num [Nat.choose] at e0 e1 e2 e3 e4 e5 e6 e7 e8
  omega

lemma pcv : pc good 0 = 0 ∧ pc good 1 = 1 ∧ pc good 2 = 18 ∧ pc good 3 = 265 ∧ pc good 4 = 2060 ∧ pc
    good 5 = 8196 ∧ pc good 6 = 17570 ∧ pc good 7 = 20594 ∧ pc good 8 = 12432 ∧ pc good 9 = 3024 :=
  lin (pc good) pc0 (av0.symm.trans (count_eq hP 0)) (av1.symm.trans (count_eq hP 1))
    (av2.symm.trans (count_eq hP 2)) (av3.symm.trans (count_eq hP 3)) (av4.symm.trans (count_eq hP
    4)) (av5.symm.trans (count_eq hP 5)) (av6.symm.trans (count_eq hP 6)) (av7.symm.trans (count_eq
    hP 7)) (av8.symm.trans (count_eq hP 8))

/-- The closed form a(n) = Sum_j c_j binomial(n+1, j). -/
lemma a_eq (n : ℕ) : (a n : ℚ) =
    1 * (n + 1) + 18 * ((n + 1) * n / 2) + 265 * ((n + 1) * n * (n - 1) / 6) + 2060 * ((n + 1) * n * (n - 1) * (n - 2) / 24) + 8196 * ((n + 1) * n * (n - 1) * (n - 2) * (n - 3) / 120) + 17570 * ((n + 1) * n * (n - 1) * (n - 2) * (n - 3) * (n - 4) / 720) + 20594 * ((n + 1) * n * (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n - 5) / 5040) + 12432 * ((n + 1) * n * (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n - 5) * (n - 6) / 40320) + 3024 * ((n + 1) * n * (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n - 5) * (n - 6) * (n - 7) / 362880) := by
  have h := count_eq hP n
  unfold a
  rw [h]
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := pcv
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9]
  push_cast
  simp only [ch2, ch3, ch4, ch5, ch6, ch7, ch8, ch9]
  simp
  ring

lemma values : a 1 = 20 ∧ a 2 = 322 ∧ a 3 = 3232 ∧ a 4 = 21331 ∧ a 5 = 103222 ∧ a 6 = 397460 ∧ a 7 = 1287672 ∧ a 8 = 3647349 ∧ a 9 = 9281272 ∧ a 10 = 21642038 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [← Nat.cast_inj (R := ℚ), a_eq]
    norm_num

/-- Barker's recurrence, for n > 10. -/
theorem recurrence (n : ℕ) (hn : 10 < n) :
    (a n : ℤ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - a (n - 10) := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 11 := ⟨n - 11, by omega⟩
  simp only [show q + 11 - 1 = q + 10 by omega, show q + 11 - 2 = q + 9 by omega, show q + 11 - 3 =
    q + 8 by omega, show q + 11 - 4 = q + 7 by omega, show q + 11 - 5 = q + 6 by omega, show q +
    11 - 6 = q + 5 by omega, show q + 11 - 7 = q + 4 by omega, show q + 11 - 8 = q + 3 by omega,
    show q + 11 - 9 = q + 2 by omega, show q + 11 - 10 = q + 1 by omega]
  have h : (a (q + 11) : ℚ) = 10 * a (q + 10) - 45 * a (q + 9) + 120 * a (q + 8) - 210 * a (q + 7) + 252 * a (q + 6) - 210 * a (q + 5) + 120 * a (q + 4) - 45 * a (q + 3) + 10 * a (q + 2) - a (q + 1) := by
    rw [a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq, a_eq]
    push_cast
    ring
  exact_mod_cast h

/-- Barker's g.f., as A(x) (1 - x)^10 = N(x) in Z[[x]]. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 10 =
    X * (20 + 122 * X + 912 * X ^ 2 + 1101 * X ^ 3 + 912 * X ^ 4 - 125 * X ^ 5 + 118 * X ^ 6 - 45 * X ^ 7 + 10 * X ^ 8 - X ^ 9) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 10 =
      A - C 10 * (A * X ^ 1) + C 45 * (A * X ^ 2) - C 120 * (A * X ^ 3) + C 210 * (A * X ^ 4) - C
        252 * (A * X ^ 5) + C 210 * (A * X ^ 6) - C 120 * (A * X ^ 7) + C 45 * (A * X ^ 8) - C 10 *
        (A * X ^ 9) + A * X ^ 10 := by
    simp only [map_ofNat]; ring
  have e2 : (X * (20 + 122 * X + 912 * X ^ 2 + 1101 * X ^ 3 + 912 * X ^ 4 - 125 * X ^ 5 + 118 * X ^ 6 - 45 * X ^ 7 + 10 * X ^ 8 - X ^ 9) : ℤ⟦X⟧) =
      X ^ 1 * C 20 + X ^ 2 * C 122 + X ^ 3 * C 912 + X ^ 4 * C 1101 + X ^ 5 * C 912 - X ^ 6 * C
        125 + X ^ 7 * C 118 - X ^ 8 * C 45 + X ^ 9 * C 10 - X ^ 10 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  have v := values
  rcases Nat.lt_or_ge n 11 with hn | hn
  · interval_cases n <;> simp_all
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 11 := ⟨n - 11, by omega⟩
    have h := recurrence (q + 11) (by omega)
    simp only [show q + 11 - 1 = q + 10 by omega, show q + 11 - 2 = q + 9 by omega, show q + 11 -
      3 = q + 8 by omega, show q + 11 - 4 = q + 7 by omega, show q + 11 - 5 = q + 6 by omega, show
      q + 11 - 6 = q + 5 by omega, show q + 11 - 7 = q + 4 by omega, show q + 11 - 8 = q + 3 by
      omega, show q + 11 - 9 = q + 2 by omega, show q + 11 - 10 = q + 1 by omega] at h ⊢
    simp only [show ¬ q + 11 = 0 by omega, show ¬ q + 10 = 0 by omega, show ¬ q + 9 = 0 by omega,
      show ¬ q + 8 = 0 by omega, show ¬ q + 7 = 0 by omega, show ¬ q + 6 = 0 by omega, show ¬ q +
      5 = 0 by omega, show ¬ q + 4 = 0 by omega, show ¬ q + 3 = 0 by omega, show ¬ q + 2 = 0 by
      omega, show ¬ q + 1 = 0 by omega, show 1 ≤ q + 11 by omega, show 2 ≤ q + 11 by omega, show 3 ≤
      q + 11 by omega, show 4 ≤ q + 11 by omega, show 5 ≤ q + 11 by omega, show 6 ≤ q + 11 by omega,
      show 7 ≤ q + 11 by omega, show 8 ≤ q + 11 by omega, show 9 ≤ q + 11 by omega, show 10 ≤ q + 11
      by omega, show ¬ q + 11 = 1 by omega, show ¬ q + 11 = 2 by omega, show ¬ q + 11 = 3 by omega,
      show ¬ q + 11 = 4 by omega, show ¬ q + 11 = 5 by omega, show ¬ q + 11 = 6 by omega, show ¬ q +
      11 = 7 by omega, show ¬ q + 11 = 8 by omega, show ¬ q + 11 = 9 by omega, show ¬ q + 11 = 10 by
      omega, if_true, if_false]
    rw [h]
    ring

/-- Hardin's empirical formula, for all n. -/
theorem empirical (n : ℕ) : (a n : ℚ) = (1 / 120) * n ^ 9 + (1 / 12) * n ^ 8 + (133 / 360) * n ^ 7 + (371 / 360) * n ^ 6 + (19 / 9) * n ^ 5 + (247 / 72) * n ^ 4 + (403 / 90) * n ^ 3 + (401 / 90) * n ^ 2 + (91 / 30) * n + 1 := by
  rw [a_eq]
  ring

/-- Controls: the entry's data a(1..23). -/
theorem controls : a 1 = 20 ∧ a 2 = 322 ∧ a 3 = 3232 ∧ a 4 = 21331 ∧ a 5 = 103222 ∧ a 6 = 397460 ∧
    a 7 = 1287672 ∧ a 8 = 3647349 ∧ a 9 = 9281272 ∧ a 10 = 21642038 ∧ a 11 = 46934680 ∧
    a 12 = 95749927 ∧ a 13 = 185397226 ∧ a 14 = 343142248 ∧ a 15 = 610590224 ∧ a 16 = 1049496105 ∧
    a 17 = 1749325212 ∧ a 18 = 2836933738 ∧ a 19 = 4488787184 ∧ a 20 = 6946186555 ∧
    a 21 = 10534026910 ∧ a 22 = 15683670652 ∧ a 23 = 22960578760 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩ <;>
  · rw [← Nat.cast_inj (R := ℚ), a_eq]
    norm_num

/-- Both of Barker's conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 10 < n →
      (a n : ℤ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - a (n - 10)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 10 =
      X * (20 + 122 * X + 912 * X ^ 2 + 1101 * X ^ 3 + 912 * X ^ 4 - 125 * X ^ 5 + 118 * X ^ 6 - 45 * X ^ 7 + 10 * X ^ 8 - X ^ 9) :=
  ⟨recurrence, gf⟩

end OMA.S_oeis_a229775

theorem OMA.solution : type_of% @OMA.S_oeis_a229775.main :=
  OMA.S_oeis_a229775.conjecture

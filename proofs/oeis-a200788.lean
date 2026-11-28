import OMAStatements.S_oeis_a200788
import Mathlib



namespace Mine.S_oeis_a200788

/-- `a n` = number of arrays `x : Fin 6 → Fin (n + 1)` with no three successive positions
`i, j, k` such that `x i < x j < x k`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin 6 → Fin (n + 1))).filter fun x =>
    ∀ i j k : Fin 6, i.val + 1 = j.val → j.val + 1 = k.val → ¬(x i < x j ∧ x j < x k)).card

/-- The closed form and Colin Barker's conjectures for A200788: the closed form, the linear
recurrence for `n > 7`, and the g.f.
`x*(64 + 174*x + 126*x^2 - 30*x^3 + 21*x^4 - 7*x^5 + x^6) / (1 - x)^7`. -/
def MainProp : Prop :=
    (∀ n : ℕ, 720 * (a n : ℤ) =
      349 * (n : ℤ) ^ 6 + 2889 * (n : ℤ) ^ 5 + 9415 * (n : ℤ) ^ 4 + 15195 * (n : ℤ) ^ 3 + 12556 * (n : ℤ) ^ 2 + 4956 * (n : ℤ) + 720) ∧
    (∀ n : ℕ, 7 < n →
      (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) ∧
    (1 - PowerSeries.X) ^ 7 * PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) =
      PowerSeries.X * (64 + 174 * PowerSeries.X + 126 * PowerSeries.X ^ 2 - 30 * PowerSeries.X ^ 3 + 21 * PowerSeries.X ^ 4 - 7 * PowerSeries.X ^ 5 + PowerSeries.X ^ 6)


end Mine.S_oeis_a200788


namespace A200788
open Finset
/-- number of surjective arrays onto `Fin k` with the property `Q` -/
def cnt (m : ℕ) (Q : (Fin m → ℕ) → Prop) [DecidablePred Q] (k : ℕ) : ℕ :=
  (univ.filter fun y : Fin m → Fin k => Function.Surjective y ∧ Q (fun i => (y i).val)).card

theorem fib (m N : ℕ) (Q : (Fin m → ℕ) → Prop) [DecidablePred Q]
    (hQ : ∀ x y : Fin m → ℕ, (∀ i j, x i < x j ↔ y i < y j) → (Q x ↔ Q y))
    (S : Finset (Fin N)) :
    cnt m Q S.card =
    ((univ.filter fun x : Fin m → Fin N => Q (fun i => (x i).val)).filter
      fun x => univ.image x = S).card := by
  have hlt : ∀ a b : Fin S.card,
      ((S.orderEmbOfFin rfl a : Fin N).val < (S.orderEmbOfFin rfl b : Fin N).val) ↔
        a.val < b.val := by
    intro a b
    show (S.orderEmbOfFin rfl a) < (S.orderEmbOfFin rfl b) ↔ a < b
    exact OrderEmbedding.lt_iff_lt _
  unfold cnt
  refine Finset.card_bij (fun y _ i => S.orderEmbOfFin rfl (y i)) ?_ ?_ ?_
  · intro y hy
    obtain ⟨-, hsurj, hq⟩ := Finset.mem_filter.1 hy
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · exact (hQ (fun i => ((S.orderEmbOfFin rfl (y i) : Fin N)).val) (fun i => (y i).val)
        (fun i j => hlt (y i) (y j))).2 hq
    · ext s
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩
        exact Finset.orderEmbOfFin_mem S rfl (y i)
      · intro hs
        have h2 : s ∈ Set.range (S.orderEmbOfFin rfl) := by
          rw [Finset.range_orderEmbOfFin]; exact hs
        obtain ⟨j, rfl⟩ := h2
        obtain ⟨i, rfl⟩ := hsurj j
        exact ⟨i, rfl⟩
  · intro y1 _ y2 _ h
    funext i
    exact (S.orderEmbOfFin rfl).injective (congrFun h i)
  · intro x hx
    obtain ⟨hx1, himg⟩ := Finset.mem_filter.1 hx
    obtain ⟨-, hq⟩ := Finset.mem_filter.1 hx1
    have hmem : ∀ i, ∃ j, S.orderEmbOfFin rfl j = x i := by
      intro i
      have h1 : x i ∈ S := by
        rw [← himg]; exact Finset.mem_image_of_mem x (Finset.mem_univ i)
      have h2 : x i ∈ Set.range (S.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]; exact h1
      exact h2
    choose y hy using hmem
    refine ⟨y, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩, funext hy⟩
    · intro j
      have h1 : S.orderEmbOfFin rfl j ∈ univ.image x := by
        rw [himg]; exact Finset.orderEmbOfFin_mem S rfl j
      obtain ⟨i, -, hi⟩ := Finset.mem_image.1 h1
      exact ⟨i, (S.orderEmbOfFin rfl).injective ((hy i).trans hi)⟩
    · refine (hQ (fun i => (x i).val) (fun i => (y i).val) (fun i j => ?_)).1 hq
      have h3 := hlt (y i) (y j)
      rw [hy i, hy j] at h3
      exact h3

/-- an order-pattern property is counted by a sum of binomials -/
theorem pattern_count (m N : ℕ) (Q : (Fin m → ℕ) → Prop) [DecidablePred Q]
    (hQ : ∀ x y : Fin m → ℕ, (∀ i j, x i < x j ↔ y i < y j) → (Q x ↔ Q y)) :
    (univ.filter fun x : Fin m → Fin N => Q (fun i => (x i).val)).card =
      ∑ k ∈ range (N + 1), N.choose k * cnt m Q k := by
  have h1 := Finset.card_eq_sum_card_fiberwise (f := fun x : Fin m → Fin N => univ.image x)
    (s := univ.filter fun x : Fin m → Fin N => Q (fun i => (x i).val))
    (t := (univ : Finset (Fin N)).powerset)
    (fun x _ => Finset.mem_coe.2 (Finset.mem_powerset.2 (Finset.subset_univ _)))
  rw [h1]
  have h2 : ∀ S ∈ (univ : Finset (Fin N)).powerset,
      ((univ.filter fun x : Fin m → Fin N => Q (fun i => (x i).val)).filter
        fun x => univ.image x = S).card = cnt m Q S.card :=
    fun S _ => (fib m N Q hQ S).symm
  rw [Finset.sum_congr rfl h2, Finset.sum_powerset_apply_card]
  simp only [Finset.card_univ, Fintype.card_fin, smul_eq_mul]

theorem cnt_zero (m : ℕ) (Q : (Fin m → ℕ) → Prop) [DecidablePred Q] (k : ℕ) (hk : m < k) :
    cnt m Q k = 0 := by
  unfold cnt
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro y - ⟨hs, -⟩
  have h := Fintype.card_le_of_surjective y hs
  simp only [Fintype.card_fin] at h
  omega


/-- the pattern condition, written out -/
def Q (x : Fin 6 → ℕ) : Prop :=
  ¬(x 0 < x 1 ∧ x 1 < x 2) ∧ ¬(x 1 < x 2 ∧ x 2 < x 3) ∧ ¬(x 2 < x 3 ∧ x 3 < x 4) ∧ ¬(x 3 < x 4 ∧ x 4 < x 5)

instance : DecidablePred Q := fun x => by unfold Q; infer_instance

theorem hQ (x y : Fin 6 → ℕ) (h : ∀ i j, x i < x j ↔ y i < y j) : Q x ↔ Q y := by
  unfold Q
  rw [h 0 1, h 1 2, h 2 3, h 3 4, h 4 5]

theorem tri (x : Fin 6 → ℕ) (a b c : Fin 6) (hab : a.val + 1 = b.val)
    (hbc : b.val + 1 = c.val) (i j k : Fin 6) (hi : i.val = a.val) (hij : i.val + 1 = j.val)
    (hjk : j.val + 1 = k.val) (h : ¬(x a < x b ∧ x b < x c)) : ¬(x i < x j ∧ x j < x k) := by
  have ei : i = a := Fin.ext hi
  have ej : j = b := Fin.ext (by omega)
  have ek : k = c := Fin.ext (by omega)
  rw [ei, ej, ek]; exact h

theorem char (n : ℕ) (x : Fin 6 → Fin (n + 1)) :
    (∀ i j k : Fin 6, i.val + 1 = j.val → j.val + 1 = k.val → ¬(x i < x j ∧ x j < x k)) ↔
      Q (fun i => (x i).val) := by
  constructor
  · intro h
    exact ⟨h 0 1 2 rfl rfl, h 1 2 3 rfl rfl, h 2 3 4 rfl rfl, h 3 4 5 rfl rfl⟩
  · rintro ⟨h0, h1, h2, h3⟩ i j k hij hjk
    have hk := k.isLt
    have hi3 : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
    rcases hi3 with h | h | h | h
    · exact tri (fun i => (x i).val) 0 1 2 rfl rfl i j k h hij hjk h0
    · exact tri (fun i => (x i).val) 1 2 3 rfl rfl i j k h hij hjk h1
    · exact tri (fun i => (x i).val) 2 3 4 rfl rfl i j k h hij hjk h2
    · exact tri (fun i => (x i).val) 3 4 5 rfl rfl i j k h hij hjk h3

/-- a plain sum `f 0 + ... + f (k - 1)`, cheap for the kernel to evaluate -/
def sumTo (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => sumTo f k + f k

theorem sumTo_eq (f : ℕ → ℕ) (k : ℕ) : sumTo f k = ∑ a ∈ range k, f a := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Finset.sum_range_succ, ← ih]; rfl

/-- number of lists of `m` values below `k` passing the test `B`, by direct recursion -/
def cntL : (m : ℕ) → (k : ℕ) → (B : List ℕ → Bool) → ℕ
  | 0, _, B => cond (B []) 1 0
  | m + 1, k, B => sumTo (fun a => cntL m k (fun l => B (a :: l))) k

theorem linkL : ∀ (m k : ℕ) (B : List ℕ → Bool),
    (univ.filter fun x : Fin m → Fin k => B (List.ofFn fun i => (x i).val) = true).card =
      cntL m k B
  | 0, k, B => by
    cases h : B [] <;> simp [cntL, h]
  | m + 1, k, B => by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun x : Fin (m + 1) → Fin k => x 0)
      (t := univ) (fun x _ => Finset.mem_coe.2 (Finset.mem_univ _))]
    have hf : ∀ b : Fin k,
        (filter (fun x => x 0 = b)
          (univ.filter fun x : Fin (m + 1) → Fin k =>
            B (List.ofFn fun i => (x i).val) = true)).card =
        cntL m k (fun l => B (b.val :: l)) := by
      intro b
      rw [← linkL m k (fun l => B (b.val :: l))]
      refine Finset.card_bij (fun x _ => fun i => x i.succ) ?_ ?_ ?_
      · intro x hx
        obtain ⟨hx1, hx0⟩ := Finset.mem_filter.1 hx
        obtain ⟨-, hp⟩ := Finset.mem_filter.1 hx1
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
        rw [List.ofFn_succ, hx0] at hp
        exact hp
      · intro x1 h1 x2 h2 h
        have a1 := (Finset.mem_filter.1 h1).2
        have a2 := (Finset.mem_filter.1 h2).2
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact a1.trans a2.symm
        · exact congrFun h j
      · intro t ht
        obtain ⟨-, hp⟩ := Finset.mem_filter.1 ht
        refine ⟨Fin.cons b t, Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, ?_⟩, ?_⟩
        · rw [List.ofFn_succ]
          simpa using hp
        · simp
        · funext i
          simp
    rw [Finset.sum_congr rfl (fun b _ => hf b)]
    show _ = sumTo _ k
    rw [sumTo_eq,
      ← Fin.sum_univ_eq_sum_range (fun a => cntL m k (fun l => B (a :: l))) k]

/-- a forbidden step: into `c` from `b`, where `u` says the step into `b` was a rise -/
def bad (u : Bool) (b c : ℕ) : Bool := u && decide (b < c)

/-- the flag after stepping from `b` to `c` -/
def nxt (b c : ℕ) : Bool := decide (b < c)

/-- which lists of values are still allowed after an element `b`, where `u` records whether the
step into `b` was a rise -/
def R : ℕ → Bool → List ℕ → Bool
  | _, _, [] => true
  | b, u, c :: t => !(bad u b c) && R c (nxt b c) t

/-- the test on a whole list -/
def B0 : List ℕ → Bool
  | [] => true
  | a :: t => R a false t

theorem sumTo_congr (f g : ℕ → ℕ) (k : ℕ) (h : ∀ a, a < k → f a = g a) : sumTo f k = sumTo g k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show sumTo f k + f k = sumTo g k + g k
    rw [ih (fun a ha => h a (Nat.lt_succ_of_lt ha)), h k (Nat.lt_succ_self k)]

theorem sumTo_zero (k : ℕ) : sumTo (fun _ => 0) k = 0 := by
  induction k with
  | zero => rfl
  | succ k ihk => show sumTo (fun _ => 0) k + 0 = 0; rw [ihk]

theorem cntL_false (m k : ℕ) : cntL m k (fun _ => false) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show sumTo (fun _ => cntL m k (fun _ => false)) k = 0
    rw [ih]
    exact sumTo_zero k

theorem getD_map_range (f : ℕ → ℕ) (k b : ℕ) (hb : b < k) :
    ((List.range k).map f).getD b 0 = f b := by
  simp [List.getD_eq_getElem?_getD, hb]

/-- the table of counts, one row for each value of the flag -/
def tab (k : ℕ) : ℕ → List ℕ × List ℕ
  | 0 => ((List.range k).map (fun _ => 1), (List.range k).map (fun _ => 1))
  | m + 1 =>
    ((List.range k).map (fun b =>
        sumTo (fun c => cond (bad false b c) 0
          ((cond (nxt b c) (tab k m).2 (tab k m).1).getD c 0)) k),
     (List.range k).map (fun b =>
        sumTo (fun c => cond (bad true b c) 0
          ((cond (nxt b c) (tab k m).2 (tab k m).1).getD c 0)) k))

def look (T : List ℕ × List ℕ) (b : ℕ) (u : Bool) : ℕ := (cond u T.2 T.1).getD b 0

theorem look_zero (k b : ℕ) (u : Bool) (hb : b < k) : look (tab k 0) b u = 1 := by
  cases u
  · exact getD_map_range (fun _ => 1) k b hb
  · exact getD_map_range (fun _ => 1) k b hb

theorem look_succ (k m b : ℕ) (u : Bool) (hb : b < k) : look (tab k (m + 1)) b u =
    sumTo (fun c => cond (bad u b c) 0 (look (tab k m) c (nxt b c))) k := by
  cases u
  · exact getD_map_range (fun b => sumTo (fun c => cond (bad false b c) 0
      ((cond (nxt b c) (tab k m).2 (tab k m).1).getD c 0)) k) k b hb
  · exact getD_map_range (fun b => sumTo (fun c => cond (bad true b c) 0
      ((cond (nxt b c) (tab k m).2 (tab k m).1).getD c 0)) k) k b hb

theorem dp (k : ℕ) : ∀ (m b : ℕ) (u : Bool), b < k → cntL m k (R b u) = look (tab k m) b u
  | 0, b, u, hb => by
    rw [look_zero k b u hb]
    rfl
  | m + 1, b, u, hb => by
    rw [look_succ k m b u hb]
    show sumTo (fun c => cntL m k (fun t => R b u (c :: t))) k = _
    refine sumTo_congr _ _ k (fun c hc => ?_)
    show cntL m k (fun t => !(bad u b c) && R c (nxt b c) t) = _
    cases bad u b c
    · show cntL m k (fun t => R c (nxt b c) t) = look (tab k m) c (nxt b c)
      exact dp k m c (nxt b c) hc
    · exact cntL_false m k

theorem cnt_total (m k : ℕ) :
    cntL (m + 1) k B0 = sumTo (fun a => look (tab k m) a false) k := by
  show sumTo (fun a => cntL m k (fun t => R a false t)) k = _
  exact sumTo_congr _ _ k (fun a ha => dp k m a false ha)

theorem hQB (x : Fin 6 → ℕ) : Q x ↔ B0 (List.ofFn x) = true := by
  have e : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := by
    rfl
  rw [e]
  simp [Q, B0, R, bad, nxt]
  try omega

theorem linkQ (k : ℕ) :
    (univ.filter fun x : Fin 6 → Fin k => Q (fun i => (x i).val)).card = cntL 6 k B0 := by
  rw [← linkL]
  exact congrArg Finset.card (Finset.filter_congr fun x _ => hQB _)

theorem cnt_totalQ (k : ℕ) :
    cntL 6 k B0 = sumTo (fun a => look (tab k 5) a false) k :=
  cnt_total 5 k

theorem A0 : sumTo (fun a => look (tab 0 5) a false) 0 = 0 := by decide +kernel
theorem A1 : sumTo (fun a => look (tab 1 5) a false) 1 = 1 := by decide +kernel
theorem A2 : sumTo (fun a => look (tab 2 5) a false) 2 = 64 := by decide +kernel
theorem A3 : sumTo (fun a => look (tab 3 5) a false) 3 = 622 := by decide +kernel
theorem A4 : sumTo (fun a => look (tab 4 5) a false) 4 = 3136 := by decide +kernel
theorem A5 : sumTo (fun a => look (tab 5 5) a false) 5 = 11100 := by decide +kernel
theorem A6 : sumTo (fun a => look (tab 6 5) a false) 6 = 31395 := by decide +kernel

theorem cg0 (f : ℕ → ℕ) (hf : ∀ N, cntL 6 N B0 = ∑ j ∈ range (N + 1), N.choose j * f j) : f 0 = 0 := by
  have h := hf 0
  rw [cnt_totalQ 0, A0] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, show Nat.choose 0 0 = 1 from by decide] at h
  omega

theorem c0 : cnt 6 Q 0 = 0 :=
  cg0 (cnt 6 Q) (fun N => (linkQ N).symm.trans (pattern_count 6 N Q hQ))

theorem cg1 (f : ℕ → ℕ) (hf : ∀ N, cntL 6 N B0 = ∑ j ∈ range (N + 1), N.choose j * f j) : f 1 = 1 := by
  have h := hf 1
  rw [cnt_totalQ 1, A1] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cg0 f hf, show Nat.choose 1 0 = 1 from by decide, show Nat.choose 1 1 = 1 from by decide] at h
  omega

theorem c1 : cnt 6 Q 1 = 1 :=
  cg1 (cnt 6 Q) (fun N => (linkQ N).symm.trans (pattern_count 6 N Q hQ))

theorem cg2 (f : ℕ → ℕ) (hf : ∀ N, cntL 6 N B0 = ∑ j ∈ range (N + 1), N.choose j * f j) : f 2 = 62 := by
  have h := hf 2
  rw [cnt_totalQ 2, A2] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cg0 f hf, cg1 f hf, show Nat.choose 2 0 = 1 from by decide, show Nat.choose 2 1 = 2 from by decide, show Nat.choose 2 2 = 1 from by decide] at h
  omega

theorem c2 : cnt 6 Q 2 = 62 :=
  cg2 (cnt 6 Q) (fun N => (linkQ N).symm.trans (pattern_count 6 N Q hQ))

theorem cg3 (f : ℕ → ℕ) (hf : ∀ N, cntL 6 N B0 = ∑ j ∈ range (N + 1), N.choose j * f j) : f 3 = 433 := by
  have h := hf 3
  rw [cnt_totalQ 3, A3] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cg0 f hf, cg1 f hf, cg2 f hf, show Nat.choose 3 0 = 1 from by decide, show Nat.choose 3 1 = 3 from by decide, show Nat.choose 3 2 = 3 from by decide, show Nat.choose 3 3 = 1 from by decide] at h
  omega

theorem c3 : cnt 6 Q 3 = 433 :=
  cg3 (cnt 6 Q) (fun N => (linkQ N).symm.trans (pattern_count 6 N Q hQ))

theorem cg4 (f : ℕ → ℕ) (hf : ∀ N, cntL 6 N B0 = ∑ j ∈ range (N + 1), N.choose j * f j) : f 4 = 1028 := by
  have h := hf 4
  rw [cnt_totalQ 4, A4] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cg0 f hf, cg1 f hf, cg2 f hf, cg3 f hf, show Nat.choose 4 0 = 1 from by decide, show Nat.choose 4 1 = 4 from by decide, show Nat.choose 4 2 = 6 from by decide, show Nat.choose 4 3 = 4 from by decide, show Nat.choose 4 4 = 1 from by decide] at h
  omega

theorem c4 : cnt 6 Q 4 = 1028 :=
  cg4 (cnt 6 Q) (fun N => (linkQ N).symm.trans (pattern_count 6 N Q hQ))

theorem cg5 (f : ℕ → ℕ) (hf : ∀ N, cntL 6 N B0 = ∑ j ∈ range (N + 1), N.choose j * f j) : f 5 = 1005 := by
  have h := hf 5
  rw [cnt_totalQ 5, A5] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cg0 f hf, cg1 f hf, cg2 f hf, cg3 f hf, cg4 f hf, show Nat.choose 5 0 = 1 from by decide, show Nat.choose 5 1 = 5 from by decide, show Nat.choose 5 2 = 10 from by decide, show Nat.choose 5 3 = 10 from by decide, show Nat.choose 5 4 = 5 from by decide, show Nat.choose 5 5 = 1 from by decide] at h
  omega

theorem c5 : cnt 6 Q 5 = 1005 :=
  cg5 (cnt 6 Q) (fun N => (linkQ N).symm.trans (pattern_count 6 N Q hQ))

theorem cg6 (f : ℕ → ℕ) (hf : ∀ N, cntL 6 N B0 = ∑ j ∈ range (N + 1), N.choose j * f j) : f 6 = 349 := by
  have h := hf 6
  rw [cnt_totalQ 6, A6] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cg0 f hf, cg1 f hf, cg2 f hf, cg3 f hf, cg4 f hf, cg5 f hf, show Nat.choose 6 0 = 1 from by decide, show Nat.choose 6 1 = 6 from by decide, show Nat.choose 6 2 = 15 from by decide, show Nat.choose 6 3 = 20 from by decide, show Nat.choose 6 4 = 15 from by decide, show Nat.choose 6 5 = 6 from by decide, show Nat.choose 6 6 = 1 from by decide] at h
  omega

theorem c6 : cnt 6 Q 6 = 349 :=
  cg6 (cnt 6 Q) (fun N => (linkQ N).symm.trans (pattern_count 6 N Q hQ))

theorem a_sum (n : ℕ) : Mine.S_oeis_a200788.a n =
    (n + 1).choose 1 * 1 + (n + 1).choose 2 * 62 + (n + 1).choose 3 * 433 + (n + 1).choose 4 * 1028 + (n + 1).choose 5 * 1005 + (n + 1).choose 6 * 349 := by
  have h : Mine.S_oeis_a200788.a n =
      (univ.filter fun x : Fin 6 → Fin (n + 1) => Q (fun i => (x i).val)).card := by
    unfold Mine.S_oeis_a200788.a
    exact congrArg Finset.card (Finset.filter_congr (fun x _ => char n x))
  rw [h, pattern_count 6 (n + 1) Q hQ]
  have e1 : ∑ k ∈ range (n + 1 + 1), (n + 1).choose k * cnt 6 Q k =
      ∑ k ∈ range (n + 9), (n + 1).choose k * cnt 6 Q k := by
    refine Finset.sum_subset (Finset.range_mono (by omega)) (fun k _ hk => ?_)
    have hk' : n + 1 < k := by
      have := mt Finset.mem_range.2 hk
      omega
    rw [Nat.choose_eq_zero_of_lt hk', Nat.zero_mul]
  have e2 : ∑ k ∈ range 7, (n + 1).choose k * cnt 6 Q k =
      ∑ k ∈ range (n + 9), (n + 1).choose k * cnt 6 Q k := by
    refine Finset.sum_subset (Finset.range_mono (by omega)) (fun k _ hk => ?_)
    have hk' : 6 < k := by
      have := mt Finset.mem_range.2 hk
      omega
    rw [cnt_zero 6 Q k hk', Nat.mul_zero]
  rw [e1, ← e2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c0, c1, c2, c3, c4, c5, c6]
  ring

theorem ch1 (N : ℕ) : (1 : ℤ) * (N.choose 1 : ℤ) = N := by
  rw [Nat.choose_one_right, one_mul]

theorem ch2 (N : ℕ) : 2 * (N.choose 2 : ℤ) = (N : ℤ) * ((N : ℤ) - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have e : (N + 1).choose 2 = N.choose 1 + N.choose 2 := Nat.choose_succ_succ' N 1
    have h1 := ch1 N
    rw [e]
    push_cast
    linarith

theorem ch3 (N : ℕ) : 6 * (N.choose 3 : ℤ) = (N : ℤ) * ((N : ℤ) - 1) * ((N : ℤ) - 2) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have e : (N + 1).choose 3 = N.choose 2 + N.choose 3 := Nat.choose_succ_succ' N 2
    have h1 := ch2 N
    rw [e]
    push_cast
    linarith

theorem ch4 (N : ℕ) : 24 * (N.choose 4 : ℤ) = (N : ℤ) * ((N : ℤ) - 1) * ((N : ℤ) - 2) * ((N : ℤ) - 3) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have e : (N + 1).choose 4 = N.choose 3 + N.choose 4 := Nat.choose_succ_succ' N 3
    have h1 := ch3 N
    rw [e]
    push_cast
    linarith

theorem ch5 (N : ℕ) : 120 * (N.choose 5 : ℤ) = (N : ℤ) * ((N : ℤ) - 1) * ((N : ℤ) - 2) * ((N : ℤ) - 3) * ((N : ℤ) - 4) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have e : (N + 1).choose 5 = N.choose 4 + N.choose 5 := Nat.choose_succ_succ' N 4
    have h1 := ch4 N
    rw [e]
    push_cast
    linarith

theorem ch6 (N : ℕ) : 720 * (N.choose 6 : ℤ) = (N : ℤ) * ((N : ℤ) - 1) * ((N : ℤ) - 2) * ((N : ℤ) - 3) * ((N : ℤ) - 4) * ((N : ℤ) - 5) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have e : (N + 1).choose 6 = N.choose 5 + N.choose 6 := Nat.choose_succ_succ' N 5
    have h1 := ch5 N
    rw [e]
    push_cast
    linarith

theorem hF (n : ℕ) : 720 * (Mine.S_oeis_a200788.a n : ℤ) =
    720 * (((n : ℤ) + 1)) + 22320 * (((n : ℤ) + 1) * (((n : ℤ) + 1) - 1)) + 51960 * (((n : ℤ) + 1) * (((n : ℤ) + 1) - 1) * (((n : ℤ) + 1) - 2)) + 30840 * (((n : ℤ) + 1) * (((n : ℤ) + 1) - 1) * (((n : ℤ) + 1) - 2) * (((n : ℤ) + 1) - 3)) + 6030 * (((n : ℤ) + 1) * (((n : ℤ) + 1) - 1) * (((n : ℤ) + 1) - 2) * (((n : ℤ) + 1) - 3) * (((n : ℤ) + 1) - 4)) + 349 * (((n : ℤ) + 1) * (((n : ℤ) + 1) - 1) * (((n : ℤ) + 1) - 2) * (((n : ℤ) + 1) - 3) * (((n : ℤ) + 1) - 4) * (((n : ℤ) + 1) - 5)) := by
  have ha : (Mine.S_oeis_a200788.a n : ℤ) =
      ((n + 1).choose 1 : ℤ) * 1 + ((n + 1).choose 2 : ℤ) * 62 + ((n + 1).choose 3 : ℤ) * 433 + ((n + 1).choose 4 : ℤ) * 1028 + ((n + 1).choose 5 : ℤ) * 1005 + ((n + 1).choose 6 : ℤ) * 349 := by
    rw [a_sum]
    push_cast
    ring
  have h1 : 1 * ((n + 1).choose 1 : ℤ) = ((n : ℤ) + 1) := by
    have := ch1 (n + 1)
    push_cast at this
    linear_combination this
  have h2 : 2 * ((n + 1).choose 2 : ℤ) = ((n : ℤ) + 1) * (((n : ℤ) + 1) - 1) := by
    have := ch2 (n + 1)
    push_cast at this
    linear_combination this
  have h3 : 6 * ((n + 1).choose 3 : ℤ) = ((n : ℤ) + 1) * (((n : ℤ) + 1) - 1) * (((n : ℤ) + 1) - 2) := by
    have := ch3 (n + 1)
    push_cast at this
    linear_combination this
  have h4 : 24 * ((n + 1).choose 4 : ℤ) = ((n : ℤ) + 1) * (((n : ℤ) + 1) - 1) * (((n : ℤ) + 1) - 2) * (((n : ℤ) + 1) - 3) := by
    have := ch4 (n + 1)
    push_cast at this
    linear_combination this
  have h5 : 120 * ((n + 1).choose 5 : ℤ) = ((n : ℤ) + 1) * (((n : ℤ) + 1) - 1) * (((n : ℤ) + 1) - 2) * (((n : ℤ) + 1) - 3) * (((n : ℤ) + 1) - 4) := by
    have := ch5 (n + 1)
    push_cast at this
    linear_combination this
  have h6 : 720 * ((n + 1).choose 6 : ℤ) = ((n : ℤ) + 1) * (((n : ℤ) + 1) - 1) * (((n : ℤ) + 1) - 2) * (((n : ℤ) + 1) - 3) * (((n : ℤ) + 1) - 4) * (((n : ℤ) + 1) - 5) := by
    have := ch6 (n + 1)
    push_cast at this
    linear_combination this
  linear_combination 720 * ha + 720 * h1 + 22320 * h2 + 51960 * h3 + 30840 * h4 + 6030 * h5 + 349 * h6

theorem a_val (n : ℕ) (v : ℤ)
    (h : 720 * (((n : ℤ) + 1)) + 22320 * (((n : ℤ) + 1) * (((n : ℤ) + 1) - 1)) + 51960 * (((n : ℤ) + 1) * (((n : ℤ) + 1) - 1) * (((n : ℤ) + 1) - 2)) + 30840 * (((n : ℤ) + 1) * (((n : ℤ) + 1) - 1) * (((n : ℤ) + 1) - 2) * (((n : ℤ) + 1) - 3)) + 6030 * (((n : ℤ) + 1) * (((n : ℤ) + 1) - 1) * (((n : ℤ) + 1) - 2) * (((n : ℤ) + 1) - 3) * (((n : ℤ) + 1) - 4)) + 349 * (((n : ℤ) + 1) * (((n : ℤ) + 1) - 1) * (((n : ℤ) + 1) - 2) * (((n : ℤ) + 1) - 3) * (((n : ℤ) + 1) - 4) * (((n : ℤ) + 1) - 5)) = 720 * v) :
    (Mine.S_oeis_a200788.a n : ℤ) = v := by
  have := hF n
  linarith

/-- the coefficients of the entry's generating function (offset 1) -/
def b (n : ℕ) : ℤ := if n = 0 then (0 : ℤ) else (Mine.S_oeis_a200788.a n : ℤ)

end A200788

theorem Mine.sol : Mine.S_oeis_a200788.MainProp := by
  unfold Mine.S_oeis_a200788.MainProp
  have hrec : ∀ n : ℕ, 7 < n →
      (Mine.S_oeis_a200788.a n : ℤ) = 7 * Mine.S_oeis_a200788.a (n - 1) - 21 * Mine.S_oeis_a200788.a (n - 2) + 35 * Mine.S_oeis_a200788.a (n - 3) - 35 * Mine.S_oeis_a200788.a (n - 4) + 21 * Mine.S_oeis_a200788.a (n - 5) - 7 * Mine.S_oeis_a200788.a (n - 6) + Mine.S_oeis_a200788.a (n - 7) := by
    intro n hn
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 8 := ⟨n - 8, by omega⟩
    have e1 : j + 8 - 1 = j + 7 := by omega
    have e2 : j + 8 - 2 = j + 6 := by omega
    have e3 : j + 8 - 3 = j + 5 := by omega
    have e4 : j + 8 - 4 = j + 4 := by omega
    have e5 : j + 8 - 5 = j + 3 := by omega
    have e6 : j + 8 - 6 = j + 2 := by omega
    have e7 : j + 8 - 7 = j + 1 := by omega
    rw [e1, e2, e3, e4, e5, e6, e7]
    have g0 := A200788.hF (j + 8)
    have g1 := A200788.hF (j + 7)
    have g2 := A200788.hF (j + 6)
    have g3 := A200788.hF (j + 5)
    have g4 := A200788.hF (j + 4)
    have g5 := A200788.hF (j + 3)
    have g6 := A200788.hF (j + 2)
    have g7 := A200788.hF (j + 1)
    push_cast at g0 g1 g2 g3 g4 g5 g6 g7
    have keyF : 720 * (Mine.S_oeis_a200788.a (j + 8) : ℤ) =
        720 * (7 * (Mine.S_oeis_a200788.a (j + 7) : ℤ) - 21 * (Mine.S_oeis_a200788.a (j + 6) : ℤ) + 35 * (Mine.S_oeis_a200788.a (j + 5) : ℤ) - 35 * (Mine.S_oeis_a200788.a (j + 4) : ℤ) + 21 * (Mine.S_oeis_a200788.a (j + 3) : ℤ) - 7 * (Mine.S_oeis_a200788.a (j + 2) : ℤ) + (Mine.S_oeis_a200788.a (j + 1) : ℤ)) := by
      linear_combination g0 - 7 * g1 + 21 * g2 - 35 * g3 + 35 * g4 - 21 * g5 + 7 * g6 - g7
    linarith
  have hcf : ∀ n : ℕ, 720 * (Mine.S_oeis_a200788.a n : ℤ) =
      349 * (n : ℤ) ^ 6 + 2889 * (n : ℤ) ^ 5 + 9415 * (n : ℤ) ^ 4 + 15195 * (n : ℤ) ^ 3 + 12556 * (n : ℤ) ^ 2 + 4956 * (n : ℤ) + 720 := by
    intro n
    linear_combination A200788.hF n
  refine ⟨hcf, hrec, ?_⟩
  have v1 : (Mine.S_oeis_a200788.a 1 : ℤ) = 64 := A200788.a_val 1 64 (by norm_num)
  have v2 : (Mine.S_oeis_a200788.a 2 : ℤ) = 622 := A200788.a_val 2 622 (by norm_num)
  have v3 : (Mine.S_oeis_a200788.a 3 : ℤ) = 3136 := A200788.a_val 3 3136 (by norm_num)
  have v4 : (Mine.S_oeis_a200788.a 4 : ℤ) = 11100 := A200788.a_val 4 11100 (by norm_num)
  have v5 : (Mine.S_oeis_a200788.a 5 : ℤ) = 31395 := A200788.a_val 5 31395 (by norm_num)
  have v6 : (Mine.S_oeis_a200788.a 6 : ℤ) = 75992 := A200788.a_val 6 75992 (by norm_num)
  have v7 : (Mine.S_oeis_a200788.a 7 : ℤ) = 164004 := A200788.a_val 7 164004 (by norm_num)
  have hb : ∀ m : ℕ, 0 < m → A200788.b m = (Mine.S_oeis_a200788.a m : ℤ) :=
    fun m hm => if_neg (by omega)
  have key : ∀ n : ℕ, A200788.b n
      - 7 * (if 1 ≤ n then A200788.b (n - 1) else 0)
      + 21 * (if 2 ≤ n then A200788.b (n - 2) else 0)
      - 35 * (if 3 ≤ n then A200788.b (n - 3) else 0)
      + 35 * (if 4 ≤ n then A200788.b (n - 4) else 0)
      - 21 * (if 5 ≤ n then A200788.b (n - 5) else 0)
      + 7 * (if 6 ≤ n then A200788.b (n - 6) else 0)
      - (if 7 ≤ n then A200788.b (n - 7) else 0)
      = 64 * (if n = 1 then 1 else 0) + 174 * (if n = 2 then 1 else 0) + 126 * (if n = 3 then 1 else 0) - 30 * (if n = 4 then 1 else 0) + 21 * (if n = 5 then 1 else 0) - 7 * (if n = 6 then 1 else 0) + (if n = 7 then 1 else 0) := by
    intro n
    by_cases hn : n < 8
    · interval_cases n <;> simp [A200788.b, v1, v2, v3, v4, v5, v6, v7]
    · have h := hrec n (by omega)
      rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        hb n (by omega), hb (n - 1) (by omega), hb (n - 2) (by omega), hb (n - 3) (by omega), hb (n - 4) (by omega), hb (n - 5) (by omega), hb (n - 6) (by omega), hb (n - 7) (by omega), h]
      ring
  have k7 : (PowerSeries.C (7 : ℤ)) = 7 := map_ofNat _ 7
  have k21 : (PowerSeries.C (21 : ℤ)) = 21 := map_ofNat _ 21
  have k30 : (PowerSeries.C (30 : ℤ)) = 30 := map_ofNat _ 30
  have k35 : (PowerSeries.C (35 : ℤ)) = 35 := map_ofNat _ 35
  have k64 : (PowerSeries.C (64 : ℤ)) = 64 := map_ofNat _ 64
  have k126 : (PowerSeries.C (126 : ℤ)) = 126 := map_ofNat _ 126
  have k174 : (PowerSeries.C (174 : ℤ)) = 174 := map_ofNat _ 174
  show (1 - PowerSeries.X) ^ 7 * PowerSeries.mk A200788.b =
      PowerSeries.X * (64 + 174 * PowerSeries.X + 126 * PowerSeries.X ^ 2 - 30 * PowerSeries.X ^ 3 + 21 * PowerSeries.X ^ 4 - 7 * PowerSeries.X ^ 5 + PowerSeries.X ^ 6)
  have el : (1 - PowerSeries.X) ^ 7 * PowerSeries.mk A200788.b
      = PowerSeries.mk A200788.b
        - PowerSeries.C (7 : ℤ) * (PowerSeries.mk A200788.b * PowerSeries.X ^ 1)
        + PowerSeries.C (21 : ℤ) * (PowerSeries.mk A200788.b * PowerSeries.X ^ 2)
        - PowerSeries.C (35 : ℤ) * (PowerSeries.mk A200788.b * PowerSeries.X ^ 3)
        + PowerSeries.C (35 : ℤ) * (PowerSeries.mk A200788.b * PowerSeries.X ^ 4)
        - PowerSeries.C (21 : ℤ) * (PowerSeries.mk A200788.b * PowerSeries.X ^ 5)
        + PowerSeries.C (7 : ℤ) * (PowerSeries.mk A200788.b * PowerSeries.X ^ 6)
        - PowerSeries.mk A200788.b * PowerSeries.X ^ 7 := by
    rw [k7, k21, k35]
    ring
  have er : (PowerSeries.X : PowerSeries ℤ) * (64 + 174 * PowerSeries.X + 126 * PowerSeries.X ^ 2 - 30 * PowerSeries.X ^ 3 + 21 * PowerSeries.X ^ 4 - 7 * PowerSeries.X ^ 5 + PowerSeries.X ^ 6)
      = PowerSeries.C (64 : ℤ) * PowerSeries.X ^ 1 + PowerSeries.C (174 : ℤ) * PowerSeries.X ^ 2 + PowerSeries.C (126 : ℤ) * PowerSeries.X ^ 3 - PowerSeries.C (30 : ℤ) * PowerSeries.X ^ 4 + PowerSeries.C (21 : ℤ) * PowerSeries.X ^ 5 - PowerSeries.C (7 : ℤ) * PowerSeries.X ^ 6 + PowerSeries.X ^ 7 := by
    rw [k7, k21, k30, k64, k126, k174]
    ring
  rw [el, er]
  ext n
  have hC : ∀ (k : ℕ) (c : ℤ) (m : ℕ),
      (if k ≤ m then (if m - k = 0 then c else 0) else 0) = c * (if m = k then 1 else 0) := by
    intro k c m
    split_ifs <;> omega
  simp only [map_add, map_sub, map_neg, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mk, PowerSeries.coeff_X_pow, PowerSeries.coeff_C, hC]
  exact key n


theorem Mine.bridge (n : ℕ) (hn : n ≠ 0) : OMA.S_oeis_a200788.a n = Mine.S_oeis_a200788.a n := by
  unfold OMA.S_oeis_a200788.a Mine.S_oeis_a200788.a
  rw [if_neg hn]
  refine Fintype.card_of_subtype _ (fun x => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, OMA.S_oeis_a200788.isValid]
  constructor
  · intro h i
    exact h _ _ _ rfl rfl
  · intro h i j k hij hjk
    have h1 : i.val + 1 < 6 := by omega
    have h2 : i.val + 2 < 6 := by omega
    have ej : j = ⟨i.val + 1, h1⟩ := Fin.ext (by simp only []; omega)
    have ek : k = ⟨i.val + 2, h2⟩ := Fin.ext (by simp only []; omega)
    subst ej
    subst ek
    exact h ⟨i.val, by omega⟩

theorem OMA.solution : type_of% @OMA.S_oeis_a200788.main := by
  have hm : Mine.S_oeis_a200788.MainProp := Mine.sol
  unfold Mine.S_oeis_a200788.MainProp at hm
  obtain ⟨hcf, hrec, hgf⟩ := hm
  have e : ∀ k : ℕ, k ≠ 0 → (OMA.S_oeis_a200788.a k : ℤ) = (Mine.S_oeis_a200788.a k : ℤ) := fun k hk => by rw [Mine.bridge k hk]
  have hmk : PowerSeries.map (Int.castRingHom ℚ)
      (PowerSeries.mk fun n => if n = 0 then (0 : ℤ) else (Mine.S_oeis_a200788.a n : ℤ)) =
      PowerSeries.mk fun n => (OMA.S_oeis_a200788.a n : ℚ) := by
    ext n
    simp only [PowerSeries.coeff_map, PowerSeries.coeff_mk]
    by_cases hn : n = 0
    · subst hn
      simp [OMA.S_oeis_a200788.a]
    · rw [if_neg hn, Mine.bridge n hn]
      simp
  have h := congrArg (PowerSeries.map (Int.castRingHom ℚ)) hgf
  simp only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat, PowerSeries.map_X, hmk] at h
  refine ⟨by linear_combination h, ?_⟩
  · intro n hn
    rw [e n (by omega), e (n - 1) (by omega), e (n - 2) (by omega), e (n - 3) (by omega), e (n - 4) (by omega), e (n - 5) (by omega), e (n - 6) (by omega), e (n - 7) (by omega)]
    exact hrec n hn

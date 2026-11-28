import OMAStatements.S_oeis_a345493

-- Problem: A345493, numbers that are the sum of eight squares in six or more ways
-- (Chai Wah Wu's conjectures: a(n) = 2 a(n-1) - a(n-2) for n > 11, and the generating function).
-- Upstream: statements/oeis-a345493.lean (declaration OMA.S_oeis_a345493.main)
--
-- Proof outline. The set S of terms is exactly {56, 58, 59, 61, 62, 64, 65, 67, 68} together with
-- every n >= 70, so a(n) = 60 + n for n >= 10 and both claims follow by direct computation.
-- * n >= 427: Lagrange's four-square theorem applied to m - 27 shows that every m >= 27 is a sum
--   of seven positive squares with small parts; prefixing the largest parts L = r, r-1, ..., r-5,
--   where r = sqrt(n - 27), gives six representations of n with distinct maxima.
-- * 70 <= n < 427 and the nine sporadic terms: six explicit sorted representations each,
--   checked by the kernel.
-- * any other n < 70: every representation, once sorted, lies in an explicitly generated list of
--   nondecreasing sequences, and the kernel counts at most five of them.

namespace OMA.P345493

open OMA.S_oeis_a345493

/-- Sum of the squares of a list. -/
def sq (l : List ℕ) : ℕ := (l.map (· ^ 2)).sum

/-- Any finite family of valid representations bounds `ways n` from below. -/
lemma le_ways (n : ℕ) (F : Finset (Multiset ℕ))
    (hF : ∀ s ∈ F, Multiset.card s = 8 ∧ (∀ x ∈ s, 1 ≤ x) ∧ (s.map (· ^ 2)).sum = n) :
    F.card ≤ ways n := by
  classical
  unfold ways
  refine (Finset.card_le_card (t := (((Finset.Icc 1 n).sym 8).filter
      (fun s : Sym ℕ 8 => ((s : Multiset ℕ).map (· ^ 2)).sum = n)).image
        (fun s : Sym ℕ 8 => (s : Multiset ℕ))) ?_).trans Finset.card_image_le
  intro s hs
  obtain ⟨hc, hpos, hsum⟩ := hF s hs
  rw [Finset.mem_image]
  refine ⟨Sym.mk s hc, ?_, rfl⟩
  rw [Finset.mem_filter, Finset.mem_sym_iff]
  refine ⟨fun x hx => ?_, hsum⟩
  have hx' : x ∈ s := hx
  have h1 : x ^ 2 ≤ (s.map (· ^ 2)).sum :=
    Multiset.le_sum_of_mem (Multiset.mem_map_of_mem (fun y => y ^ 2) hx')
  have h2 := hpos x hx'
  rw [Finset.mem_Icc]
  refine ⟨h2, ?_⟩
  nlinarith

/-- All nondecreasing lists of length `k`, entries in `[lo, B]`, square sum at most `M`. -/
def gen : ℕ → ℕ → ℕ → ℕ → List (List ℕ)
  | 0, _, _, _ => [[]]
  | k + 1, lo, B, M =>
    (List.range' lo (B + 1 - lo)).flatMap fun x =>
      if x ^ 2 ≤ M then (gen k x B (M - x ^ 2)).map (x :: ·) else []

lemma mem_gen : ∀ (l : List ℕ) (lo B M : ℕ), l.Pairwise (· ≤ ·) →
    (∀ x ∈ l, lo ≤ x ∧ x ≤ B) → sq l ≤ M → l ∈ gen l.length lo B M
  | [], lo, B, M, _, _, _ => by simp [gen]
  | x :: t, lo, B, M, hs, hb, hM => by
    rw [List.pairwise_cons] at hs
    have hx := hb x List.mem_cons_self
    have hsq : sq (x :: t) = x ^ 2 + sq t := by simp [sq]
    have ih := mem_gen t x B (M - x ^ 2) hs.2
      (fun y hy => ⟨hs.1 y hy, (hb y (List.mem_cons_of_mem _ hy)).2⟩) (by omega)
    simp only [List.length_cons, gen, List.mem_flatMap, List.mem_range'_1]
    refine ⟨x, ⟨hx.1, by omega⟩, ?_⟩
    rw [if_pos (by omega)]
    exact List.mem_map_of_mem ih

/-- Sorting each representation injects them into a generated list. -/
lemma ways_le_gen (n B M : ℕ) (hB : ∀ x, x ^ 2 ≤ n → x ≤ B) (hM : n ≤ M) :
    ways n ≤ ((gen 8 1 B M).filter (fun l => sq l = n)).length := by
  classical
  unfold ways
  set F := ((Finset.Icc 1 n).sym 8).filter
      (fun s : Sym ℕ 8 => ((s : Multiset ℕ).map (· ^ 2)).sum = n)
  have hinj : Set.InjOn (fun s : Sym ℕ 8 => (s : Multiset ℕ).sort) F := by
    intro s _ t _ h
    apply Subtype.ext
    have := congrArg (fun l : List ℕ => (l : Multiset ℕ)) h
    simpa [Multiset.sort_eq] using this
  rw [← Finset.card_image_of_injOn hinj]
  refine (Finset.card_le_card ?_).trans (List.toFinset_card_le _)
  intro l hl
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hl
  rw [Finset.mem_filter, Finset.mem_sym_iff] at hs
  obtain ⟨hmem, hsum⟩ := hs
  rw [List.mem_toFinset, List.mem_filter]
  have hlen : ((s : Multiset ℕ).sort).length = 8 := by
    rw [Multiset.length_sort]; exact s.2
  have hsq : sq ((s : Multiset ℕ).sort) = n := by
    unfold sq
    rw [← Multiset.sum_coe, ← Multiset.map_coe, Multiset.sort_eq]; exact hsum
  refine ⟨?_, by simpa using hsq⟩
  have key := mem_gen ((s : Multiset ℕ).sort) 1 B M (Multiset.pairwise_sort _ _)
    (fun x hx => by
      rw [Multiset.mem_sort] at hx
      have h1 := Finset.mem_Icc.mp (hmem x hx)
      refine ⟨h1.1, hB x ?_⟩
      have : x ^ 2 ≤ ((s : Multiset ℕ).map (· ^ 2)).sum :=
        Multiset.le_sum_of_mem (Multiset.mem_map_of_mem (fun y => y ^ 2) hx)
      omega)
    (by omega)
  rwa [hlen] at key

/-- A checkable certificate: one representation. -/
def okList (n : ℕ) (l : List ℕ) : Bool :=
  l.length == 8 && l.all (fun x => 1 ≤ x) && decide (l.Pairwise (· ≤ ·)) && sq l == n

/-- A checkable certificate: six distinct sorted representations. -/
def okData (n : ℕ) (L : List (List ℕ)) : Bool :=
  decide (6 ≤ L.length) && decide L.Nodup && L.all (okList n)

lemma six_of_ok (n : ℕ) (L : List (List ℕ)) (h : okData n L = true) : 6 ≤ ways n := by
  classical
  simp only [okData, okList, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    beq_iff_eq] at h
  obtain ⟨⟨h6, hnd⟩, hall⟩ := h
  have hmapnd : (L.map (fun l : List ℕ => (l : Multiset ℕ))).Nodup := by
    refine hnd.map_on ?_
    intro x hx y hy hxy
    exact List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => Nat.le_antisymm h1 h2)
      (hall x hx).1.2 (hall y hy).1.2 (Multiset.coe_eq_coe.mp hxy)
  have hcard : (L.map (fun l : List ℕ => (l : Multiset ℕ))).toFinset.card = L.length := by
    rw [List.toFinset_card_of_nodup hmapnd, List.length_map]
  calc 6 ≤ L.length := h6
    _ = _ := hcard.symm
    _ ≤ ways n := by
      apply le_ways
      intro s hs
      rw [List.mem_toFinset, List.mem_map] at hs
      obtain ⟨l, hl, rfl⟩ := hs
      obtain ⟨⟨⟨hlen, hpos⟩, _⟩, hsq⟩ := hall l hl
      refine ⟨by simpa using hlen, fun x hx => hpos x hx, ?_⟩
      simpa [sq] using hsq

end OMA.P345493

namespace OMA.P345493

open OMA.S_oeis_a345493

lemma sum_sq_filter_pos (s : Multiset ℕ) :
    ((s.filter (fun x => 0 < x)).map (· ^ 2)).sum = (s.map (· ^ 2)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    by_cases hx : 0 < x
    · rw [Multiset.filter_cons_of_pos _ hx, Multiset.map_cons, Multiset.map_cons,
        Multiset.sum_cons, Multiset.sum_cons, ih]
    · have h0 : x = 0 := by omega
      rw [Multiset.filter_cons_of_neg _ hx, Multiset.map_cons, Multiset.sum_cons, ih, h0]
      simp

/-- `27` written as `7 - k` positive squares, each at most `5`. -/
def pad : ℕ → Multiset ℕ
  | 0 => {3, 2, 2, 2, 2, 1, 1}
  | 1 => {4, 2, 2, 1, 1, 1}
  | 2 => {3, 3, 2, 2, 1}
  | 3 => {4, 3, 1, 1}
  | _ => {5, 1, 1}

lemma pad_spec (k : ℕ) (hk : k ≤ 4) :
    Multiset.card (pad k) + k = 7 ∧ ((pad k).map (· ^ 2)).sum = 27 ∧
      ∀ x ∈ pad k, 1 ≤ x ∧ x ≤ 5 := by
  interval_cases k <;> decide

/-- Every `m ≥ 27` is a sum of seven positive squares, each part at most `5` or with square
at most `m - 27` (Lagrange's four-square theorem applied to `m - 27`). -/
lemma sum7 (m : ℕ) (hm : 27 ≤ m) : ∃ t : Multiset ℕ, Multiset.card t = 7 ∧
    (∀ x ∈ t, 1 ≤ x ∧ (x ≤ 5 ∨ x ^ 2 ≤ m - 27)) ∧ (t.map (· ^ 2)).sum = m := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares (m - 27)
  set s : Multiset ℕ := {a, b, c, d} with hs
  set t0 := s.filter (fun x => 0 < x) with ht0
  have hs2 : (s.map (· ^ 2)).sum = m - 27 := by
    rw [hs]; simp; omega
  have hk : Multiset.card t0 ≤ 4 := (Multiset.card_le_card (Multiset.filter_le _ _)).trans (by simp [hs])
  obtain ⟨hpc, hps, hpb⟩ := pad_spec (Multiset.card t0) hk
  have ht0s : (t0.map (· ^ 2)).sum = m - 27 := by rw [ht0, sum_sq_filter_pos, hs2]
  refine ⟨t0 + pad (Multiset.card t0), ?_, ?_, ?_⟩
  · rw [Multiset.card_add]; omega
  · intro x hx
    rcases Multiset.mem_add.mp hx with hx | hx
    · have hxpos : 0 < x := (Multiset.mem_filter.mp hx).2
      refine ⟨hxpos, Or.inr ?_⟩
      have : x ^ 2 ≤ (t0.map (· ^ 2)).sum :=
        Multiset.le_sum_of_mem (Multiset.mem_map_of_mem (fun y => y ^ 2) hx)
      omega
    · exact ⟨(hpb x hx).1, Or.inl (hpb x hx).2⟩
  · rw [Multiset.map_add, Multiset.sum_add, ht0s, hps]; omega

/-- A multiset whose largest element is `L` determines `L`. -/
lemma max_unique {L L' : ℕ} {t t' : Multiset ℕ} (ht : ∀ x ∈ t, x ≤ L)
    (ht' : ∀ x ∈ t', x ≤ L') (h : L ::ₘ t = L' ::ₘ t') : L = L' := by
  have h1 : L' ∈ L ::ₘ t := by rw [h]; simp
  have h2 : L ∈ L' ::ₘ t' := by rw [← h]; simp
  rcases Multiset.mem_cons.mp h1 with h1 | h1
  · exact h1.symm
  · rcases Multiset.mem_cons.mp h2 with h2 | h2
    · exact h2
    · have := ht L' h1
      have := ht' L h2
      omega

/-- For large `n`, six representations with distinct largest parts `r, r-1, ..., r-5`,
where `r = ⌊√(n - 27)⌋`. -/
lemma big (n : ℕ) (hn : 427 ≤ n) : 6 ≤ ways n := by
  classical
  set r := Nat.sqrt (n - 27) with hr
  have hr2 : r ^ 2 ≤ n - 27 := Nat.sqrt_le' (n - 27)
  have hr3 : n - 27 < (r + 1) ^ 2 := Nat.lt_succ_sqrt' (n - 27)
  have hr20 : 20 ≤ r := Nat.le_sqrt'.mpr (by omega)
  have hL : ∀ i : Fin 6, 15 ≤ r - (i : ℕ) := fun i => by have := i.isLt; omega
  have hm : ∀ i : Fin 6, 27 ≤ n - (r - (i : ℕ)) ^ 2 := by
    intro i
    have : (r - (i : ℕ)) ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left (Nat.sub_le _ _) 2
    omega
  have hkey : ∀ i : Fin 6, n - 27 ≤ 2 * (r - (i : ℕ)) ^ 2 := by
    intro i
    have hi := i.isLt
    have h15 := hL i
    have hLr : r + 1 ≤ (r - (i : ℕ)) + 6 := by omega
    have h1 : (r + 1) ^ 2 ≤ ((r - (i : ℕ)) + 6) ^ 2 := Nat.pow_le_pow_left hLr 2
    have h2 : ((r - (i : ℕ)) + 6) ^ 2 ≤ 2 * (r - (i : ℕ)) ^ 2 + 1 := by nlinarith
    omega
  choose t ht using fun i : Fin 6 => sum7 (n - (r - (i : ℕ)) ^ 2) (hm i)
  have hbound : ∀ i : Fin 6, ∀ x ∈ t i, 1 ≤ x ∧ x ≤ r - (i : ℕ) := by
    intro i x hx
    obtain ⟨-, hb, -⟩ := ht i
    obtain ⟨h1, h2⟩ := hb x hx
    refine ⟨h1, ?_⟩
    rcases h2 with h2 | h2
    · have := hL i; omega
    · have h3 := hkey i
      have h4 := hm i
      have h5 : x ^ 2 ≤ (r - (i : ℕ)) ^ 2 := by omega
      exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h5
  let f : Fin 6 → Multiset ℕ := fun i => (r - (i : ℕ)) ::ₘ t i
  have hinj : Function.Injective f := by
    intro i j hij
    have := max_unique (fun x hx => (hbound i x hx).2) (fun x hx => (hbound j x hx).2) hij
    have := i.isLt
    have := j.isLt
    ext
    omega
  have hcard : (Finset.univ.image f).card = 6 := by
    rw [Finset.card_image_of_injective _ hinj]; simp
  rw [← hcard]
  apply le_ways
  intro s hs
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨hc, -, hsum⟩ := ht i
  refine ⟨by simp [f, hc], ?_, ?_⟩
  · intro x hx
    rcases Multiset.mem_cons.mp hx with rfl | hx
    · have := hL i; omega
    · exact (hbound i x hx).1
  · simp only [f, Multiset.map_cons, Multiset.sum_cons, hsum]
    have := hm i
    omega

end OMA.P345493

namespace OMA.P345493

open OMA.S_oeis_a345493

/-- Adds to `c`, while it has fewer than 6 lists, the lists `l ++ p` where `l` is nondecreasing
with `k` entries in `[1, a]` whose squares sum to `r`. -/
def sr : ℕ → ℕ → ℕ → ℕ → List ℕ → List (List ℕ) → List (List ℕ)
  | f + 1, k + 1, a + 1, r, p, c =>
    sr f (k + 1) a r p (if c.length < 6 ∧ (a + 1) ^ 2 + k ≤ r ∧ r ≤ (k + 1) * (a + 1) ^ 2 then
      sr f k (a + 1) (r - (a + 1) ^ 2) ((a + 1) :: p) c else c)
  | _, 0, _, r, p, c => if r = 0 then p :: c else c
  | _, _, _, _, _, c => c

/-- Checks the searched representations for n, n + 1, ..., n + t - 1. -/
def chk : ℕ → ℕ → Bool
  | _, 0 => true
  | n, t + 1 => okData n (sr 99 8 20 n [] []) && chk (n + 1) t

lemma chk_spec : ∀ t n, chk n t = true → ∀ m, n ≤ m → m < n + t → 6 ≤ ways m := by
  intro t
  induction t with
  | zero => intro n _ m h1 h2; omega
  | succ t ih =>
    intro n h m h1 h2
    simp only [chk, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1'
    · exact six_of_ok _ _ h.1
    · exact ih (n + 1) h.2 m h1' (by omega)

lemma mid (n : ℕ) (h1 : 70 ≤ n) (h2 : n < 427) : 6 ≤ ways n :=
  chk_spec 357 70 (by decide +kernel) n h1 h2

/-- The terms below `70`. -/
def Tl : List ℕ := [56, 58, 59, 61, 62, 64, 65, 67, 68]

lemma low_T (m : ℕ) (hm : m ∈ Tl) : 6 ≤ ways m :=
  six_of_ok m _ (List.all_eq_true.mp
    (by decide +kernel : Tl.all (fun m => okData m (sr 99 8 20 m [] [])) = true) m hm)

lemma small_check : ∀ m < 70, m ∉ Tl →
    ((gen 8 1 8 69).filter (fun l => sq l = m)).length ≤ 5 := by
  decide +kernel

lemma low_not (m : ℕ) (h1 : m < 70) (h2 : m ∉ Tl) : ¬ 6 ≤ ways m := by
  have hle := ways_le_gen m 8 69
    (fun x hx => by
      by_contra h
      have h9 : 9 ≤ x := by omega
      have : 81 ≤ x ^ 2 := by nlinarith
      omega)
    (by omega)
  have := small_check m h1 h2
  omega

/-- The claimed set of terms. -/
def q (m : ℕ) : Prop := m ∈ Tl ∨ 70 ≤ m

instance : DecidablePred q := fun m => inferInstanceAs (Decidable (m ∈ Tl ∨ 70 ≤ m))

lemma memS_iff (m : ℕ) : m ∈ S ↔ q m := by
  show 6 ≤ ways m ↔ (m ∈ Tl ∨ 70 ≤ m)
  constructor
  · intro h
    by_contra hc
    rw [not_or] at hc
    exact low_not m (by omega) hc.1 h
  · rintro (h | h)
    · exact low_T m h
    · by_cases h' : m < 427
      · exact mid m h h'
      · exact big m (by omega)

/-- The `k`-th term (from `0`) of the sequence. -/
def f (k : ℕ) : ℕ := if k < 9 then Tl.getD k 0 else 61 + k

lemma count_q_70 (j : ℕ) : Nat.count q (70 + j) = 9 + j := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [show 70 + (j + 1) = (70 + j) + 1 by omega, Nat.count_succ, ih,
      if_pos (show q (70 + j) from Or.inr (by omega))]
    omega

lemma q_f (k : ℕ) : q (f k) := by
  unfold f
  split_ifs with h
  · left
    interval_cases k <;> decide
  · right
    omega

lemma count_f (k : ℕ) : Nat.count q (f k) = k := by
  unfold f
  split_ifs with h
  · interval_cases k <;> decide
  · rw [show 61 + k = 70 + (k - 9) by omega, count_q_70]
    omega

lemma nth_q (k : ℕ) : Nat.nth q k = f k := by
  have h := Nat.nth_count (q_f k)
  rwa [count_f] at h

lemma a_eq (n : ℕ) : a n = f (n - 1) := by
  have hS : (fun m => m ∈ S) = q := funext fun m => propext (memS_iff m)
  unfold a
  rw [hS, nth_q]

lemma a_big (n : ℕ) (h : 10 ≤ n) : a n = 60 + n := by
  rw [a_eq]
  unfold f
  rw [if_neg (by omega)]
  omega

lemma a_vals (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 13) :
    a n = [0, 56, 58, 59, 61, 62, 64, 65, 67, 68, 70, 71, 72, 73].getD n 0 := by
  rw [a_eq]
  interval_cases n <;> decide

open PowerSeries

lemma lhs_coeff (g : ℕ → ℤ) (k : ℕ) :
    coeff (k + 2) (mk g * (X - 1) ^ 2) = g (k + 2) - 2 * g (k + 1) + g k := by
  have e : (mk g * (X - 1) ^ 2 : ℤ⟦X⟧) = mk g * X ^ 2 - mk g * X - mk g * X + mk g := by ring
  rw [e, map_add, map_sub, map_sub, coeff_mul_X_pow, show k + 2 = (k + 1) + 1 from rfl,
    coeff_succ_mul_X, coeff_mk, coeff_mk, coeff_mk]
  ring

lemma lhs_coeff0 (g : ℕ → ℤ) : coeff 0 (mk g * (X - 1) ^ 2) = g 0 := by
  have e : (mk g * (X - 1) ^ 2 : ℤ⟦X⟧) = mk g * X ^ 2 - mk g * X - mk g * X + mk g := by ring
  rw [e, map_add, map_sub, map_sub, coeff_mul_X_pow', coeff_zero_mul_X, coeff_mk]
  simp

lemma lhs_coeff1 (g : ℕ → ℤ) : coeff 1 (mk g * (X - 1) ^ 2) = g 1 - 2 * g 0 := by
  have e : (mk g * (X - 1) ^ 2 : ℤ⟦X⟧) = mk g * X ^ 2 - mk g * X - mk g * X + mk g := by ring
  rw [e, map_add, map_sub, map_sub, coeff_mul_X_pow', show (1 : ℕ) = 0 + 1 from rfl,
    coeff_succ_mul_X, coeff_mk, coeff_mk]
  simp
  ring

theorem main_proof :
    (∀ n : ℕ, 11 < n → (a n : ℤ) = 2 * a (n - 1) - a (n - 2)) ∧
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (X - 1) ^ 2 =
        X * (-X ^ 10 + X ^ 9 - X ^ 8 + X ^ 7 - X ^ 6 + X ^ 5 - X ^ 4 + X ^ 3 - X ^ 2 - 54 * X + 56) := by
  refine ⟨fun n hn => ?_, ?_⟩
  · rw [a_big n (by omega), a_big (n - 1) (by omega), a_big (n - 2) (by omega)]
    omega
  · ext n
    rw [show (54 : ℤ⟦X⟧) = C 54 from (map_ofNat C 54).symm,
      show (56 : ℤ⟦X⟧) = C 56 from (map_ofNat C 56).symm]
    rcases n with _ | _ | k
    · rw [lhs_coeff0, coeff_zero_X_mul]
      simp
    · rw [lhs_coeff1, coeff_succ_X_mul]
      simp only [map_add, map_sub, map_neg, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]
      simp [a_vals]
    · rw [lhs_coeff, show k + 2 = (k + 1) + 1 from rfl, coeff_succ_X_mul]
      simp only [map_add, map_sub, map_neg, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]
      rcases Nat.lt_or_ge k 11 with hk | hk
      · interval_cases k <;> simp [a_vals]
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 11 := ⟨k - 11, by omega⟩
        have e2 : a (j + 11 + 2) = 60 + (j + 11 + 2) := a_big _ (by omega)
        have e1 : a (j + 11 + 1) = 60 + (j + 11 + 1) := a_big _ (by omega)
        have e0 : a (j + 11) = 60 + (j + 11) := a_big _ (by omega)
        simp only [e0, e1, e2]
        simp
        ring

end OMA.P345493

theorem OMA.solution : type_of% @OMA.S_oeis_a345493.main := OMA.P345493.main_proof

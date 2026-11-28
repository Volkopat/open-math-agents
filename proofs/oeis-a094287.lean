import OMAStatements.S_oeis_a094287

-- Problem: A094287: Number of (s(0), s(1), ..., s(n)) such that 0 < s(i) < 7 and |s(i) - s(i-1)| <= 1 for i = 1,2,...,n, s(0) = 1, s(n) = 1.
-- Upstream: formal-conjectures statements/oeis-a094287.lean:0 (declaration OMA.S_oeis_a094287.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: kB lo hi a R n k is the set of sequences s(0..n) with values in lo..hi, s(0) = a,
-- s(n) = k and R s(i-1) s(i) for consecutive values. Removing the last value (Fin.init, inverse
-- Fin.snoc) gives the transfer-matrix recursion |kB (n+1) k| = sum over j in lo..hi with R j k
-- of |kB n j| (kcard094287), and |kB 0 k| = [k = a, lo <= a <= hi] (kbase094287). Here
-- lo = 1, hi = 6, a = 1, R x y = (y <= x + 1 and x <= y + 1); the six counts c(n, k) satisfy
-- c(n+1, k) = c(n, k-1) + c(n, k) + c(n, k+1), and the characteristic polynomial of this 6 x 6
-- matrix gives the recurrence (a linear consequence of 21 instances, found by omega). The g.f.
-- follows by comparing coefficients.

/-- Sequences s(0..n) with values in lo..hi, s(0) = a, s(n) = k and R between consecutive
values. -/
def kB094287 (lo hi a : ℕ) (R : ℕ → ℕ → Prop) [DecidableRel R] (n k : ℕ) :
    Finset (Fin (n + 1) → ℕ) :=
  (Fintype.piFinset fun _ : Fin (n + 1) => Finset.Icc lo hi).filter
    (fun s => s 0 = a ∧ s (Fin.last n) = k ∧ ∀ i : Fin n, R (s i.castSucc) (s i.succ))

theorem kmem094287 (lo hi a : ℕ) (R : ℕ → ℕ → Prop) [DecidableRel R] (n k : ℕ)
    (s : Fin (n + 1) → ℕ) :
    s ∈ kB094287 lo hi a R n k ↔ (∀ i, lo ≤ s i ∧ s i ≤ hi) ∧ s 0 = a ∧ s (Fin.last n) = k ∧
      ∀ i : Fin n, R (s i.castSucc) (s i.succ) := by
  unfold kB094287
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  simp only [Finset.mem_Icc]

theorem kstep094287 (lo hi a : ℕ) (R : ℕ → ℕ → Prop) [DecidableRel R] (n k : ℕ)
    (hk1 : lo ≤ k) (hk2 : k ≤ hi) :
    kB094287 lo hi a R (n + 1) k = ((Finset.Icc lo hi).filter (fun j => R j k)).biUnion
      (fun j => (kB094287 lo hi a R n j).image
        (fun t => (Fin.snoc t k : Fin (n + 1 + 1) → ℕ))) := by
  ext s
  rw [Finset.mem_biUnion]
  constructor
  · intro hs
    obtain ⟨hr, h0, hl, hst⟩ := (kmem094287 lo hi a R (n + 1) k s).1 hs
    have e1 : (Fin.last n).succ = Fin.last (n + 1) := Fin.succ_last n
    have hlast := hst (Fin.last n)
    rw [e1, hl] at hlast
    refine ⟨s (Fin.last n).castSucc, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨hr _, hlast⟩
    · rw [Finset.mem_image]
      refine ⟨Fin.init s, ?_, ?_⟩
      · rw [kmem094287]
        refine ⟨fun i => hr i.castSucc, ?_, rfl, fun i => ?_⟩
        · show s (Fin.castSucc 0) = a
          rw [Fin.castSucc_zero]
          exact h0
        · show R (s i.castSucc.castSucc) (s i.succ.castSucc)
          have h := hst i.castSucc
          rw [Fin.succ_castSucc] at h
          exact h
      · show (Fin.snoc (Fin.init s) k : Fin (n + 1 + 1) → ℕ) = s
        rw [← hl]
        exact Fin.snoc_init_self s
  · rintro ⟨j, hj, hs⟩
    rw [Finset.mem_filter, Finset.mem_Icc] at hj
    rw [Finset.mem_image] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    obtain ⟨hr, h0, hl, hst⟩ := (kmem094287 lo hi a R n j t).1 ht
    rw [kmem094287]
    refine ⟨fun i => ?_, ?_, ?_, fun i => ?_⟩
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · rw [Fin.snoc_castSucc]
        exact hr i'
      · rw [Fin.snoc_last]
        exact ⟨hk1, hk2⟩
    · rw [← Fin.castSucc_zero, Fin.snoc_castSucc]
      exact h0
    · rw [Fin.snoc_last]
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact hst i'
      · have e1 : (Fin.last n).succ = Fin.last (n + 1) := Fin.succ_last n
        rw [e1, Fin.snoc_last, Fin.snoc_castSucc, hl]
        exact hj.2

/-- The transfer-matrix recursion. -/
theorem kcard094287 (lo hi a : ℕ) (R : ℕ → ℕ → Prop) [DecidableRel R] (n k : ℕ)
    (hk1 : lo ≤ k) (hk2 : k ≤ hi) :
    (kB094287 lo hi a R (n + 1) k).card =
      ∑ j ∈ (Finset.Icc lo hi).filter (fun j => R j k), (kB094287 lo hi a R n j).card := by
  rw [kstep094287 lo hi a R n k hk1 hk2, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro j _
    apply Finset.card_image_of_injective
    intro t t' h
    have h' : Fin.init (Fin.snoc t k : Fin (n + 1 + 1) → ℕ) =
        Fin.init (Fin.snoc t' k : Fin (n + 1 + 1) → ℕ) := congrArg Fin.init h
    rw [Fin.init_snoc, Fin.init_snoc] at h'
    exact h'
  · intro j _ j' _ hjj'
    exact Finset.disjoint_left.2 (fun s hs hs' => by
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hs
      obtain ⟨t', ht', e⟩ := Finset.mem_image.1 hs'
      have h1 := ((kmem094287 lo hi a R n j t).1 ht).2.2.1
      have h2 := ((kmem094287 lo hi a R n j' t').1 ht').2.2.1
      have h3 := congrFun e (Fin.last n).castSucc
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc] at h3
      omega)

/-- Sequences of length one. -/
theorem kbase094287 (lo hi a : ℕ) (R : ℕ → ℕ → Prop) [DecidableRel R] (k : ℕ) :
    (kB094287 lo hi a R 0 k).card = if k = a ∧ lo ≤ a ∧ a ≤ hi then 1 else 0 := by
  split_ifs with h
  · obtain ⟨hka, h1, h2⟩ := h
    rw [Finset.card_eq_one]
    refine ⟨fun _ => k, ?_⟩
    ext s
    rw [kmem094287, Finset.mem_singleton]
    constructor
    · rintro ⟨-, h0, -, -⟩
      funext i
      have hi0 : i = 0 := Fin.fin_one_eq_zero i
      rw [hi0]
      exact h0.trans hka.symm
    · rintro rfl
      refine ⟨fun _ => ?_, hka, rfl, fun i => i.elim0⟩
      show lo ≤ k ∧ k ≤ hi
      omega
  · rw [Finset.card_eq_zero]
    apply Finset.subset_empty.1
    intro s hs
    exfalso
    obtain ⟨hr, h0, hl, -⟩ := (kmem094287 lo hi a R 0 k s).1 hs
    have e : Fin.last 0 = 0 := Fin.fin_one_eq_zero _
    rw [e] at hl
    have hr0 := hr 0
    apply h
    omega

/-- The step relation of A094287. -/
abbrev kR094287 (x y : ℕ) : Prop := y ≤ x + 1 ∧ x ≤ y + 1

theorem kr094287 (m : ℕ) :
    (kB094287 1 6 1 kR094287 (m + 1) 1).card =
      (kB094287 1 6 1 kR094287 m 1).card + (kB094287 1 6 1 kR094287 m 2).card ∧
    (kB094287 1 6 1 kR094287 (m + 1) 2).card =
      (kB094287 1 6 1 kR094287 m 1).card + ((kB094287 1 6 1 kR094287 m 2).card +
        (kB094287 1 6 1 kR094287 m 3).card) ∧
    (kB094287 1 6 1 kR094287 (m + 1) 3).card =
      (kB094287 1 6 1 kR094287 m 2).card + ((kB094287 1 6 1 kR094287 m 3).card +
        (kB094287 1 6 1 kR094287 m 4).card) ∧
    (kB094287 1 6 1 kR094287 (m + 1) 4).card =
      (kB094287 1 6 1 kR094287 m 3).card + ((kB094287 1 6 1 kR094287 m 4).card +
        (kB094287 1 6 1 kR094287 m 5).card) ∧
    (kB094287 1 6 1 kR094287 (m + 1) 5).card =
      (kB094287 1 6 1 kR094287 m 4).card + ((kB094287 1 6 1 kR094287 m 5).card +
        (kB094287 1 6 1 kR094287 m 6).card) ∧
    (kB094287 1 6 1 kR094287 (m + 1) 6).card =
      (kB094287 1 6 1 kR094287 m 5).card + (kB094287 1 6 1 kR094287 m 6).card := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [kcard094287 1 6 1 kR094287 m 1 (by norm_num) (by norm_num),
      show (Finset.Icc 1 6).filter (fun j => kR094287 j 1) = {1, 2} by decide,
      Finset.sum_pair (show (1 : ℕ) ≠ 2 by decide)]
  · rw [kcard094287 1 6 1 kR094287 m 2 (by norm_num) (by norm_num),
      show (Finset.Icc 1 6).filter (fun j => kR094287 j 2) = {1, 2, 3} by decide,
      Finset.sum_insert (show (1 : ℕ) ∉ ({2, 3} : Finset ℕ) by decide),
      Finset.sum_pair (show (2 : ℕ) ≠ 3 by decide)]
  · rw [kcard094287 1 6 1 kR094287 m 3 (by norm_num) (by norm_num),
      show (Finset.Icc 1 6).filter (fun j => kR094287 j 3) = {2, 3, 4} by decide,
      Finset.sum_insert (show (2 : ℕ) ∉ ({3, 4} : Finset ℕ) by decide),
      Finset.sum_pair (show (3 : ℕ) ≠ 4 by decide)]
  · rw [kcard094287 1 6 1 kR094287 m 4 (by norm_num) (by norm_num),
      show (Finset.Icc 1 6).filter (fun j => kR094287 j 4) = {3, 4, 5} by decide,
      Finset.sum_insert (show (3 : ℕ) ∉ ({4, 5} : Finset ℕ) by decide),
      Finset.sum_pair (show (4 : ℕ) ≠ 5 by decide)]
  · rw [kcard094287 1 6 1 kR094287 m 5 (by norm_num) (by norm_num),
      show (Finset.Icc 1 6).filter (fun j => kR094287 j 5) = {4, 5, 6} by decide,
      Finset.sum_insert (show (4 : ℕ) ∉ ({5, 6} : Finset ℕ) by decide),
      Finset.sum_pair (show (5 : ℕ) ≠ 6 by decide)]
  · rw [kcard094287 1 6 1 kR094287 m 6 (by norm_num) (by norm_num),
      show (Finset.Icc 1 6).filter (fun j => kR094287 j 6) = {5, 6} by decide,
      Finset.sum_pair (show (5 : ℕ) ≠ 6 by decide)]

open OMA.S_oeis_a094287 in
theorem OMA.solution : type_of% @OMA.S_oeis_a094287.main := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ → ℕ, ∀ n k, c n k = (kB094287 1 6 1 kR094287 n k).card :=
    ⟨_, fun _ _ => rfl⟩
  have ha : ∀ n, a n = c n 1 := fun n =>
    (show a n = (kB094287 1 6 1 kR094287 n 1).card from rfl).trans (hc n 1).symm
  have r : ∀ m, c (m + 1) 1 = c m 1 + c m 2 ∧ c (m + 1) 2 = c m 1 + (c m 2 + c m 3) ∧
      c (m + 1) 3 = c m 2 + (c m 3 + c m 4) ∧ c (m + 1) 4 = c m 3 + (c m 4 + c m 5) ∧
      c (m + 1) 5 = c m 4 + (c m 5 + c m 6) ∧ c (m + 1) 6 = c m 5 + c m 6 := by
    intro m
    simp only [hc]
    exact kr094287 m
  have b : c 0 1 = 1 ∧ c 0 2 = 0 ∧ c 0 3 = 0 ∧ c 0 4 = 0 ∧ c 0 5 = 0 ∧ c 0 6 = 0 := by
    rw [hc, hc, hc, hc, hc, hc, kbase094287, kbase094287, kbase094287, kbase094287,
      kbase094287, kbase094287]
    decide
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := b
  have w1 : c 1 1 = 1 ∧ c 1 2 = 1 ∧ c 1 3 = 0 ∧ c 1 4 = 0 ∧ c 1 5 = 0 ∧
      c 1 6 = 0 := by
    obtain ⟨u1, u2, u3, u4, u5, u6⟩ : c 1 1 = c 0 1 + c 0 2 ∧ c 1 2 = c 0 1 + (c 0 2 + c 0 3) ∧
        c 1 3 = c 0 2 + (c 0 3 + c 0 4) ∧ c 1 4 = c 0 3 + (c 0 4 + c 0 5) ∧
        c 1 5 = c 0 4 + (c 0 5 + c 0 6) ∧ c 1 6 = c 0 5 + c 0 6 := r 0
    omega
  have w2 : c 2 1 = 2 ∧ c 2 2 = 2 ∧ c 2 3 = 1 ∧ c 2 4 = 0 ∧ c 2 5 = 0 ∧
      c 2 6 = 0 := by
    obtain ⟨u1, u2, u3, u4, u5, u6⟩ : c 2 1 = c 1 1 + c 1 2 ∧ c 2 2 = c 1 1 + (c 1 2 + c 1 3) ∧
        c 2 3 = c 1 2 + (c 1 3 + c 1 4) ∧ c 2 4 = c 1 3 + (c 1 4 + c 1 5) ∧
        c 2 5 = c 1 4 + (c 1 5 + c 1 6) ∧ c 2 6 = c 1 5 + c 1 6 := r 1
    obtain ⟨z1, z2, z3, z4, z5, z6⟩ := w1
    omega
  have w3 : c 3 1 = 4 ∧ c 3 2 = 5 ∧ c 3 3 = 3 ∧ c 3 4 = 1 ∧ c 3 5 = 0 ∧
      c 3 6 = 0 := by
    obtain ⟨u1, u2, u3, u4, u5, u6⟩ : c 3 1 = c 2 1 + c 2 2 ∧ c 3 2 = c 2 1 + (c 2 2 + c 2 3) ∧
        c 3 3 = c 2 2 + (c 2 3 + c 2 4) ∧ c 3 4 = c 2 3 + (c 2 4 + c 2 5) ∧
        c 3 5 = c 2 4 + (c 2 5 + c 2 6) ∧ c 3 6 = c 2 5 + c 2 6 := r 2
    obtain ⟨z1, z2, z3, z4, z5, z6⟩ := w2
    omega
  have w4 : c 4 1 = 9 ∧ c 4 2 = 12 ∧ c 4 3 = 9 ∧ c 4 4 = 4 ∧ c 4 5 = 1 ∧
      c 4 6 = 0 := by
    obtain ⟨u1, u2, u3, u4, u5, u6⟩ : c 4 1 = c 3 1 + c 3 2 ∧ c 4 2 = c 3 1 + (c 3 2 + c 3 3) ∧
        c 4 3 = c 3 2 + (c 3 3 + c 3 4) ∧ c 4 4 = c 3 3 + (c 3 4 + c 3 5) ∧
        c 4 5 = c 3 4 + (c 3 5 + c 3 6) ∧ c 4 6 = c 3 5 + c 3 6 := r 3
    obtain ⟨z1, z2, z3, z4, z5, z6⟩ := w3
    omega
  have w5 : c 5 1 = 21 ∧ c 5 2 = 30 ∧ c 5 3 = 25 ∧ c 5 4 = 14 ∧ c 5 5 = 5 ∧
      c 5 6 = 1 := by
    obtain ⟨u1, u2, u3, u4, u5, u6⟩ : c 5 1 = c 4 1 + c 4 2 ∧ c 5 2 = c 4 1 + (c 4 2 + c 4 3) ∧
        c 5 3 = c 4 2 + (c 4 3 + c 4 4) ∧ c 5 4 = c 4 3 + (c 4 4 + c 4 5) ∧
        c 5 5 = c 4 4 + (c 4 5 + c 4 6) ∧ c 5 6 = c 4 5 + c 4 6 := r 4
    obtain ⟨z1, z2, z3, z4, z5, z6⟩ := w4
    omega
  have v1 : a 1 = 1 := by
    rw [ha]
    exact w1.1
  have v2 : a 2 = 2 := by
    rw [ha]
    exact w2.1
  have v3 : a 3 = 4 := by
    rw [ha]
    exact w3.1
  have v4 : a 4 = 9 := by
    rw [ha]
    exact w4.1
  have v5 : a 5 = 21 := by
    rw [ha]
    exact w5.1
  have v6 : a 6 = 51 := by
    rw [ha]
    have u : c 6 1 = c 5 1 + c 5 2 := (r 5).1
    obtain ⟨z1, z2, -, -, -, -⟩ := w5
    omega
  have hrec : ∀ n : ℕ, 6 ≤ n → (a n : ℤ) = 6 * a (n - 1) - 10 * a (n - 2) + 9 * a (n - 4) -
      2 * a (n - 5) - a (n - 6) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
      show m + 6 - 4 = m + 2 by omega, show m + 6 - 5 = m + 1 by omega,
      show m + 6 - 6 = m by omega, ha, ha, ha, ha, ha, ha]
    have e61 : c (m + 6) 1 = c (m + 5) 1 + c (m + 5) 2 := (r (m + 5)).1
    have e51 : c (m + 5) 1 = c (m + 4) 1 + c (m + 4) 2 := (r (m + 4)).1
    have e52 : c (m + 5) 2 = c (m + 4) 1 + (c (m + 4) 2 + c (m + 4) 3) := (r (m + 4)).2.1
    have e41 : c (m + 4) 1 = c (m + 3) 1 + c (m + 3) 2 := (r (m + 3)).1
    have e42 : c (m + 4) 2 = c (m + 3) 1 + (c (m + 3) 2 + c (m + 3) 3) := (r (m + 3)).2.1
    have e43 : c (m + 4) 3 = c (m + 3) 2 + (c (m + 3) 3 + c (m + 3) 4) := (r (m + 3)).2.2.1
    have e31 : c (m + 3) 1 = c (m + 2) 1 + c (m + 2) 2 := (r (m + 2)).1
    have e32 : c (m + 3) 2 = c (m + 2) 1 + (c (m + 2) 2 + c (m + 2) 3) := (r (m + 2)).2.1
    have e33 : c (m + 3) 3 = c (m + 2) 2 + (c (m + 2) 3 + c (m + 2) 4) := (r (m + 2)).2.2.1
    have e34 : c (m + 3) 4 = c (m + 2) 3 + (c (m + 2) 4 + c (m + 2) 5) :=
      (r (m + 2)).2.2.2.1
    have e21 : c (m + 2) 1 = c (m + 1) 1 + c (m + 1) 2 := (r (m + 1)).1
    have e22 : c (m + 2) 2 = c (m + 1) 1 + (c (m + 1) 2 + c (m + 1) 3) := (r (m + 1)).2.1
    have e23 : c (m + 2) 3 = c (m + 1) 2 + (c (m + 1) 3 + c (m + 1) 4) := (r (m + 1)).2.2.1
    have e24 : c (m + 2) 4 = c (m + 1) 3 + (c (m + 1) 4 + c (m + 1) 5) :=
      (r (m + 1)).2.2.2.1
    have e25 : c (m + 2) 5 = c (m + 1) 4 + (c (m + 1) 5 + c (m + 1) 6) :=
      (r (m + 1)).2.2.2.2.1
    have e12 : c (m + 1) 2 = c m 1 + (c m 2 + c m 3) := (r m).2.1
    have e13 : c (m + 1) 3 = c m 2 + (c m 3 + c m 4) := (r m).2.2.1
    have e15 : c (m + 1) 5 = c m 4 + (c m 5 + c m 6) := (r m).2.2.2.2.1
    have e16 : c (m + 1) 6 = c m 5 + c m 6 := (r m).2.2.2.2.2
    omega
  refine ⟨hrec, ?_⟩
  have q1 : (a 1 : ℚ) = 1 := by exact_mod_cast v1
  have q2 : (a 2 : ℚ) = 2 := by exact_mod_cast v2
  have q3 : (a 3 : ℚ) = 4 := by exact_mod_cast v3
  have q4 : (a 4 : ℚ) = 9 := by exact_mod_cast v4
  have q5 : (a 5 : ℚ) = 21 := by exact_mod_cast v5
  have q6 : (a 6 : ℚ) = 51 := by exact_mod_cast v6
  have e : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((PowerSeries.X ^ 3 + 3 * PowerSeries.X ^ 2 - 4 * PowerSeries.X + 1) *
        (PowerSeries.X ^ 3 - PowerSeries.X ^ 2 - 2 * PowerSeries.X + 1)) =
      PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6 *
          (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * PowerSeries.X ^ 1)
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 10 *
          (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * PowerSeries.X ^ 2)
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 9 *
          (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * PowerSeries.X ^ 4)
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 *
          (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * PowerSeries.X ^ 5)
        + PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * PowerSeries.X ^ 6 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 10,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 9,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2]
    ring
  have e2 : (-PowerSeries.X * (-1 + 4 * PowerSeries.X - 2 * PowerSeries.X ^ 2 -
      5 * PowerSeries.X ^ 3 + 2 * PowerSeries.X ^ 4 + PowerSeries.X ^ 5) : PowerSeries ℚ) =
      PowerSeries.X ^ 1
        - PowerSeries.X ^ 2 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4
        + PowerSeries.X ^ 3 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2
        + PowerSeries.X ^ 4 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5
        - PowerSeries.X ^ 5 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2
        - PowerSeries.X ^ 6 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5]
    ring
  refine e.trans (Eq.trans ?_ e2.symm)
  ext m
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_C,
    PowerSeries.coeff_X_pow]
  rcases Nat.lt_or_ge m 7 with hm | hm
  · interval_cases m
    · norm_num
    · norm_num [q1]
    · norm_num [q1, q2]
    · norm_num [q1, q2, q3]
    · norm_num [q2, q3, q4]
    · norm_num [q1, q3, q4, q5]
    · norm_num [q1, q2, q4, q5, q6]
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 7 := ⟨m - 7, by omega⟩
    have n0 : ¬ (k + 7 = 0) := by omega
    have n1 : ¬ (k + 7 = 1) := by omega
    have n6 : ¬ (k + 7 = 6) := by omega
    have p1 : 1 ≤ k + 7 := by omega
    have p2 : 2 ≤ k + 7 := by omega
    have p3 : 3 ≤ k + 7 := by omega
    have p4 : 4 ≤ k + 7 := by omega
    have p5 : 5 ≤ k + 7 := by omega
    have p6 : 6 ≤ k + 7 := by omega
    have m1 : ¬ (k + 7 - 1 = 0) := by omega
    have m2 : ¬ (k + 7 - 2 = 0) := by omega
    have m3 : ¬ (k + 7 - 3 = 0) := by omega
    have m4 : ¬ (k + 7 - 4 = 0) := by omega
    have m5 : ¬ (k + 7 - 5 = 0) := by omega
    have m6 : ¬ (k + 7 - 6 = 0) := by omega
    rw [if_neg n0, if_pos p1, if_neg m1, if_pos p2, if_pos p2, if_neg m2, if_neg m2,
      if_pos p4, if_pos p4, if_neg m4, if_neg m4, if_pos p5, if_pos p5, if_neg m5, if_neg m5,
      if_pos p6, if_neg m6, if_neg n1, if_pos p3, if_neg m3, if_neg n6,
      show k + 7 - 1 = k + 6 by omega, show k + 7 - 2 = k + 5 by omega,
      show k + 7 - 4 = k + 3 by omega, show k + 7 - 5 = k + 2 by omega,
      show k + 7 - 6 = k + 1 by omega]
    have h := hrec (k + 7) (by omega)
    rw [show k + 7 - 1 = k + 6 by omega, show k + 7 - 2 = k + 5 by omega,
      show k + 7 - 4 = k + 3 by omega, show k + 7 - 5 = k + 2 by omega,
      show k + 7 - 6 = k + 1 by omega] at h
    have hq := congrArg (fun z : ℤ => (z : ℚ)) h
    push_cast at hq
    linear_combination hq

import OMAStatements.S_oeis_a202254

-- Problem: A202254: Number of zero-sum -n..n arrays of 4 elements with adjacent differences in -n..n.
-- Credit: @ceejcake
-- Proof: Parameterize by (s, b, a) with s = f 1 + f 2, b = f 1, a = f 0.
-- Valid (s, b) are exactly |s| <= n and |s - 2b| <= n, and for each (s, b), a ranges over an interval
-- of length 2n + 1 - (max S - min S), whose slice sum over b has a closed form linear in n.

namespace ProofA202254

open OMA.S_oeis_a202254
open scoped Classical
noncomputable section

private def box (n : ℕ) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset (fun _ : Fin 4 => Finset.Icc (-(n : ℤ)) n)

private lemma mem_box_of_isValid {n : ℕ} {f : Fin 4 → ℤ} (hf : isValid n f) : f ∈ box n := by
  simp only [box, Fintype.mem_piFinset, Finset.mem_Icc]
  exact hf.1

noncomputable instance fintypeValid (n : ℕ) : Fintype {f : Fin 4 → ℤ // isValid n f} :=
  Fintype.ofFinset ((box n).filter (isValid n)) (fun f => by
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨mem_box_of_isValid h, h⟩⟩)

-- Interval bounds for a = f 0 given (n, s, b) where s = f 1 + f 2 and b = f 1:
-- a ∈ [-n, n] ∩ [-s-n, -s+n] ∩ [b-n, b+n] ∩ [b-2s-n, b-2s+n]
private def loA (n : ℕ) (s b : ℤ) : ℤ :=
  -(n : ℤ) + max (max 0 (-s)) (max b (b - 2 * s))

private def hiA (n : ℕ) (s b : ℤ) : ℤ :=
  (n : ℤ) + min (min 0 (-s)) (min b (b - 2 * s))

private def sbaSet (n : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (Finset.Icc (-(n : ℤ)) n).biUnion (fun s =>
    ((Finset.Icc (-(n : ℤ)) n).filter (fun b => -(n : ℤ) ≤ s - 2 * b ∧ s - 2 * b ≤ n)).biUnion (fun b =>
      (Finset.Icc (loA n s b) (hiA n s b)).map
        ⟨fun a => (s, b, a), fun _ _ h => by simp only [Prod.mk.injEq] at h; exact h.2.2⟩))

private lemma mem_sbaSet {n : ℕ} {s b a : ℤ} :
    (s, b, a) ∈ sbaSet n ↔
      -(n : ℤ) ≤ s ∧ s ≤ n ∧ -(n : ℤ) ≤ s - 2 * b ∧ s - 2 * b ≤ n ∧
      loA n s b ≤ a ∧ a ≤ hiA n s b := by
  simp only [sbaSet, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc, Finset.mem_map]
  constructor
  · rintro ⟨s', hs', b', ⟨_, hb'⟩, a', ha', h⟩
    have h1 : s' = s := congr_arg Prod.fst h
    have h2 : b' = b := congr_arg (fun q => q.2.1) h
    have h3 : a' = a := congr_arg (fun q => q.2.2) h
    subst h1; subst h2; subst h3
    exact ⟨hs'.1, hs'.2, hb'.1, hb'.2, ha'.1, ha'.2⟩
  · rintro ⟨hs1, hs2, hb1, hb2, ha1, ha2⟩
    exact ⟨s, ⟨hs1, hs2⟩, b, ⟨⟨by omega, by omega⟩, ⟨hb1, hb2⟩⟩, a, ⟨ha1, ha2⟩, rfl⟩

-- Bijection: valid arrays ↔ sbaSet n
private lemma card_valid_eq_sba (n : ℕ) :
    ((box n).filter (isValid n)).card = (sbaSet n).card := by
  refine Finset.card_bij (fun f _ => (f 1 + f 2, f 1, f 0)) ?_ ?_ ?_
  · intro f hf
    rw [Finset.mem_filter] at hf
    rcases hf.2 with ⟨hb, hsum, hd0, hd1, hd2⟩
    have h0 := hb 0; have h1 := hb 1; have h2 := hb 2; have h3 := hb 3
    rw [mem_sbaSet]
    unfold loA hiA
    refine ⟨by omega, by omega, by omega, by omega, ?_, ?_⟩
    · have : max (max (0 : ℤ) (-(f 1 + f 2))) (max (f 1) (f 1 - 2 * (f 1 + f 2))) ≤ f 0 + n :=
        max_le (max_le (by omega) (by omega)) (max_le (by omega) (by omega))
      omega
    · have : f 0 - n ≤ min (min (0 : ℤ) (-(f 1 + f 2))) (min (f 1) (f 1 - 2 * (f 1 + f 2))) :=
        le_min (le_min (by omega) (by omega)) (le_min (by omega) (by omega))
      omega
  · intro f1 hf1 f2 hf2 h
    rw [Finset.mem_filter] at hf1 hf2
    have hs1 := hf1.2.2.1; have hs2 := hf2.2.2.1
    simp only [Prod.mk.injEq] at h
    ext i
    match i with | 0 => omega | 1 => omega | 2 => omega | 3 => omega
  · intro ⟨s, b, a⟩ hsba
    rw [mem_sbaSet] at hsba
    rcases hsba with ⟨hs1, hs2, hb1, hb2, ha1, ha2⟩
    unfold loA at ha1; unfold hiA at ha2
    have hlo1 : -(n : ℤ) ≤ a := by have := le_max_left (max (0 : ℤ) (-s)) (max b (b - 2 * s)); have := le_max_left (0 : ℤ) (-s); omega
    have hlo2 : -(n : ℤ) - s ≤ a := by have := le_max_left (max (0 : ℤ) (-s)) (max b (b - 2 * s)); have := le_max_right (0 : ℤ) (-s); omega
    have hlo3 : -(n : ℤ) + b ≤ a := by have := le_max_right (max (0 : ℤ) (-s)) (max b (b - 2 * s)); have := le_max_left b (b - 2 * s); omega
    have hlo4 : -(n : ℤ) + (b - 2 * s) ≤ a := by have := le_max_right (max (0 : ℤ) (-s)) (max b (b - 2 * s)); have := le_max_right b (b - 2 * s); omega
    have hhi1 : a ≤ (n : ℤ) := by have := min_le_left (min (0 : ℤ) (-s)) (min b (b - 2 * s)); have := min_le_left (0 : ℤ) (-s); omega
    have hhi2 : a ≤ (n : ℤ) - s := by have := min_le_left (min (0 : ℤ) (-s)) (min b (b - 2 * s)); have := min_le_right (0 : ℤ) (-s); omega
    have hhi3 : a ≤ (n : ℤ) + b := by have := min_le_right (min (0 : ℤ) (-s)) (min b (b - 2 * s)); have := min_le_left b (b - 2 * s); omega
    have hhi4 : a ≤ (n : ℤ) + (b - 2 * s) := by have := min_le_right (min (0 : ℤ) (-s)) (min b (b - 2 * s)); have := min_le_right b (b - 2 * s); omega
    let f : Fin 4 → ℤ := fun i => match i with | 0 => a | 1 => b | 2 => s - b | 3 => -s - a
    have hval : isValid n f :=
      ⟨fun i => by match i with | 0 => dsimp [f]; omega | 1 => dsimp [f]; omega | 2 => dsimp [f]; omega | 3 => dsimp [f]; omega,
       by dsimp [f]; omega,
       by dsimp [f]; omega,
       by dsimp [f]; omega,
       by dsimp [f]; omega⟩
    refine ⟨f, Finset.mem_filter.mpr ⟨mem_box_of_isValid hval, hval⟩, ?_⟩
    simp only [Prod.mk.injEq, f, and_true]; omega

-- Slice cardinality for a given s ∈ [-n, n]
private def sliceCard (n : ℕ) (s : ℤ) : ℕ :=
  ∑ b ∈ (Finset.Icc (-(n : ℤ)) n).filter (fun b => -(n : ℤ) ≤ s - 2 * b ∧ s - 2 * b ≤ n),
    (Finset.Icc (loA n s b) (hiA n s b)).card

private lemma card_sbaSet_eq_sum (n : ℕ) :
    (sbaSet n).card = ∑ s ∈ Finset.Icc (-(n : ℤ)) n, sliceCard n s := by
  unfold sbaSet sliceCard
  rw [Finset.card_biUnion]
  · refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Finset.card_biUnion]
    · refine Finset.sum_congr rfl (fun b _ => by rw [Finset.card_map])
    · intro b1 _ b2 _ hne
      dsimp only [Function.onFun]; rw [Finset.disjoint_left]
      intro p h1 h2
      simp only [Finset.mem_map] at h1 h2
      rcases h1 with ⟨_, _, rfl⟩; rcases h2 with ⟨_, _, h2⟩
      exact hne (congr_arg (fun q => q.2.1) h2).symm
  · intro s1 _ s2 _ hne
    dsimp only [Function.onFun]; rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [Finset.mem_biUnion, Finset.mem_map] at h1 h2
    rcases h1 with ⟨_, _, _, _, rfl⟩; rcases h2 with ⟨_, _, _, _, h2⟩
    exact hne (congr_arg Prod.fst h2).symm

-- Symmetry: sliceCard n (-s) = sliceCard n s (via b ↦ -b)
private lemma sliceCard_neg (n : ℕ) (s : ℤ) : sliceCard n (-s) = sliceCard n s := by
  unfold sliceCard
  refine Finset.sum_bij (fun b _ => -b) ?_ ?_ ?_ ?_
  · intro b hb; simp only [Finset.mem_filter, Finset.mem_Icc] at hb ⊢; omega
  · intro b1 _ b2 _ h; omega
  · intro b hb; simp only [Finset.mem_filter, Finset.mem_Icc] at hb
    exact ⟨-b, by simp only [Finset.mem_filter, Finset.mem_Icc]; omega, by omega⟩
  · intro b _
    rw [Int.card_Icc, Int.card_Icc]
    congr 1
    unfold loA hiA
    omega

-- Exact closed form for sliceCard n s when s = (s' : ℕ) ≤ n, written in terms of k = n - s'
private def sliceVal (n k : ℕ) : ℕ :=
  (n + 1 - k % 2) * (2 * k + 1) - (k / 2) * (k / 2 + 1)

private lemma sliceCard_nat (n s : ℕ) (hs : s ≤ n) :
    sliceCard n (s : ℤ) = sliceVal n (n - s) := by
  unfold sliceCard sliceVal
  let p : ℕ := (n - s) / 2
  have hB : (Finset.Icc (-(n : ℤ)) n).filter (fun b => -(n : ℤ) ≤ (s : ℤ) - 2 * b ∧ (s : ℤ) - 2 * b ≤ n) =
      Finset.Icc (-(p : ℤ)) ((s + p : ℕ) : ℤ) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_Icc]
    push_cast; omega
  rw [hB]
  -- Split Icc (-p) (s + p) into Icc (-p) (-1), Icc 0 s, and Icc (s + 1) (s + p)
  have hsplit1 : Finset.Icc (-(p : ℤ)) ((s + p : ℕ) : ℤ) =
      Finset.Icc (-(p : ℤ)) (-1) ∪ (Finset.Icc (0 : ℤ) (s : ℤ) ∪ Finset.Icc ((s : ℤ) + 1) ((s + p : ℕ) : ℤ)) := by
    ext b; simp only [Finset.mem_Icc, Finset.mem_union]; push_cast; omega
  have hd1 : Disjoint (Finset.Icc (-(p : ℤ)) (-1))
      (Finset.Icc (0 : ℤ) (s : ℤ) ∪ Finset.Icc ((s : ℤ) + 1) ((s + p : ℕ) : ℤ)) := by
    rw [Finset.disjoint_left]; intro b h1 h2
    simp only [Finset.mem_Icc, Finset.mem_union] at h1 h2; omega
  have hd2 : Disjoint (Finset.Icc (0 : ℤ) (s : ℤ)) (Finset.Icc ((s : ℤ) + 1) ((s + p : ℕ) : ℤ)) := by
    rw [Finset.disjoint_left]; intro b h1 h2
    simp only [Finset.mem_Icc] at h1 h2; omega
  rw [hsplit1, Finset.sum_union hd1, Finset.sum_union hd2]
  -- Helper: triangular sum ∑_{j=1}^p j = p*(p+1)/2
  have htri : ∀ m : ℕ, 2 * (∑ j ∈ Finset.Icc 1 m, j) = m * (m + 1) := by
    intro m; induction m with
    | zero => simp
    | succ m ihm =>
      have hI : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hI, Finset.sum_insert (by simp)]; nlinarith
  -- Part 1: b ∈ Icc (-p) (-1) -> card = 2*(n - s) + 1 + b (so sum over j = -b ∈ 1..p of (2*(n-s)+1-j))
  have hs1 : ∑ b ∈ Finset.Icc (-(p : ℤ)) (-1), (Finset.Icc (loA n (s : ℤ) b) (hiA n (s : ℤ) b)).card =
      ∑ j ∈ Finset.Icc 1 p, (2 * (n - s) + 1 - j) := by
    refine Finset.sum_bij (fun b _ => (-b).toNat) ?_ ?_ ?_ ?_
    · intro b hb; rw [Finset.mem_Icc] at hb ⊢; omega
    · intro b1 hb1 b2 hb2 h; rw [Finset.mem_Icc] at hb1 hb2; omega
    · intro j hj; rw [Finset.mem_Icc] at hj
      exact ⟨-(j : ℤ), Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro b hb; rw [Finset.mem_Icc] at hb
      rw [Int.card_Icc]; unfold loA hiA
      have h1 : max (max (0 : ℤ) (-(s : ℤ))) (max b (b - 2 * (s : ℤ))) = 0 := by
        have : max (0 : ℤ) (-(s : ℤ)) = 0 := max_eq_left (by omega)
        have : max b (b - 2 * (s : ℤ)) = b := max_eq_left (by omega)
        rw [‹max (0 : ℤ) _ = 0›, ‹max b _ = b›]; exact max_eq_left (by omega)
      have h2 : min (min (0 : ℤ) (-(s : ℤ))) (min b (b - 2 * (s : ℤ))) = b - 2 * (s : ℤ) := by
        have : min (0 : ℤ) (-(s : ℤ)) = -(s : ℤ) := min_eq_right (by omega)
        have : min b (b - 2 * (s : ℤ)) = b - 2 * (s : ℤ) := min_eq_right (by omega)
        rw [‹min (0 : ℤ) _ = _›, ‹min b _ = _›]; exact min_eq_right (by omega)
      rw [h1, h2]; omega
  -- Part 2: b ∈ Icc 0 s -> card = 2*(n - s) + 1
  have hs2 : ∑ b ∈ Finset.Icc (0 : ℤ) (s : ℤ), (Finset.Icc (loA n (s : ℤ) b) (hiA n (s : ℤ) b)).card =
      (s + 1) * (2 * (n - s) + 1) := by
    have hcongr : ∀ b ∈ Finset.Icc (0 : ℤ) (s : ℤ),
        (Finset.Icc (loA n (s : ℤ) b) (hiA n (s : ℤ) b)).card = 2 * (n - s) + 1 := by
      intro b hb; rw [Finset.mem_Icc] at hb
      rw [Int.card_Icc]; unfold loA hiA
      have h1 : max (max (0 : ℤ) (-(s : ℤ))) (max b (b - 2 * (s : ℤ))) = b := by
        have : max (0 : ℤ) (-(s : ℤ)) = 0 := max_eq_left (by omega)
        have : max b (b - 2 * (s : ℤ)) = b := max_eq_left (by omega)
        rw [‹max (0 : ℤ) _ = 0›, ‹max b _ = b›]; exact max_eq_right (by omega)
      have h2 : min (min (0 : ℤ) (-(s : ℤ))) (min b (b - 2 * (s : ℤ))) = b - 2 * (s : ℤ) := by
        have : min (0 : ℤ) (-(s : ℤ)) = -(s : ℤ) := min_eq_right (by omega)
        have : min b (b - 2 * (s : ℤ)) = b - 2 * (s : ℤ) := min_eq_right (by omega)
        rw [‹min (0 : ℤ) _ = _›, ‹min b _ = _›]; exact min_eq_right (by omega)
      rw [h1, h2]; omega
    rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Int.card_Icc, smul_eq_mul]
    have : ((s : ℤ) + 1 - 0).toNat = s + 1 := by omega
    rw [this]
  -- Part 3: b ∈ Icc (s + 1) (s + p) -> card = 2*(n - s) + 1 - (b - s)
  have hs3 : ∑ b ∈ Finset.Icc ((s : ℤ) + 1) ((s + p : ℕ) : ℤ),
      (Finset.Icc (loA n (s : ℤ) b) (hiA n (s : ℤ) b)).card =
      ∑ j ∈ Finset.Icc 1 p, (2 * (n - s) + 1 - j) := by
    refine Finset.sum_bij (fun b _ => (b - (s : ℤ)).toNat) ?_ ?_ ?_ ?_
    · intro b hb; rw [Finset.mem_Icc] at hb ⊢; push_cast at hb; omega
    · intro b1 hb1 b2 hb2 h; rw [Finset.mem_Icc] at hb1 hb2; omega
    · intro j hj; rw [Finset.mem_Icc] at hj
      exact ⟨(s : ℤ) + (j : ℤ), Finset.mem_Icc.mpr ⟨by omega, by push_cast; omega⟩, by omega⟩
    · intro b hb; rw [Finset.mem_Icc] at hb; push_cast at hb
      rw [Int.card_Icc]; unfold loA hiA
      have h1 : max (max (0 : ℤ) (-(s : ℤ))) (max b (b - 2 * (s : ℤ))) = b := by
        have : max (0 : ℤ) (-(s : ℤ)) = 0 := max_eq_left (by omega)
        have : max b (b - 2 * (s : ℤ)) = b := max_eq_left (by omega)
        rw [‹max (0 : ℤ) _ = 0›, ‹max b _ = b›]; exact max_eq_right (by omega)
      have h2 : min (min (0 : ℤ) (-(s : ℤ))) (min b (b - 2 * (s : ℤ))) = -(s : ℤ) := by
        have : min (0 : ℤ) (-(s : ℤ)) = -(s : ℤ) := min_eq_right (by omega)
        have : min b (b - 2 * (s : ℤ)) = b - 2 * (s : ℤ) := min_eq_right (by omega)
        rw [‹min (0 : ℤ) _ = _›, ‹min b _ = _›]; exact min_eq_left (by omega)
      rw [h1, h2]; omega
  rw [hs1, hs2, hs3]
  -- Evaluate 2 * ∑_{j=1}^p (2*(n-s) + 1 - j) + (s + 1) * (2*(n-s) + 1)
  have hsum_j : (∑ j ∈ Finset.Icc 1 p, (2 * (n - s) + 1 - j)) + (∑ j ∈ Finset.Icc 1 p, j) =
      p * (2 * (n - s) + 1) := by
    rw [← Finset.sum_add_distrib]
    have hcongr : ∀ j ∈ Finset.Icc 1 p, (2 * (n - s) + 1 - j) + j = 2 * (n - s) + 1 := by
      intro j hj; rw [Finset.mem_Icc] at hj; omega
    rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Nat.card_Icc, smul_eq_mul]
    have : p + 1 - 1 = p := by omega
    rw [this]
  have hp_tri := htri p
  have hmod : n + 1 - (n - s) % 2 = 2 * p + s + 1 := by omega
  rw [hmod]
  have hle : p * (p + 1) ≤ (2 * p + s + 1) * (2 * (n - s) + 1) := by
    have : p ≤ n - s := by omega
    nlinarith
  have hsub : ((2 * p + s + 1) * (2 * (n - s) + 1) - p * (p + 1)) + p * (p + 1) =
      (2 * p + s + 1) * (2 * (n - s) + 1) := by omega
  nlinarith

-- Sum of sliceVal n k for k = 0..n
private lemma sum_sliceVal_even (m : ℕ) :
    12 * (2 * (∑ k ∈ Finset.range (2 * m + 1), sliceVal (2 * m) k) - sliceVal (2 * m) (2 * m)) =
      22 * (2 * m) ^ 3 + 33 * (2 * m) ^ 2 + 26 * (2 * m) + 12 := by
  have hsum : 12 * (∑ k ∈ Finset.range (2 * m + 1), sliceVal (2 * m) k) =
      11 * (2 * m) ^ 3 + 27 * (2 * m) ^ 2 + 28 * (2 * m) + 12 := by
    induction m with
    | zero => simp [sliceVal]
    | succ m ih =>
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega]
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hshift : ∀ k ∈ Finset.range (2 * m + 1),
          sliceVal (2 * (m + 1)) k = sliceVal (2 * m) k + 2 * (2 * k + 1) := by
        intro k hk; rw [Finset.mem_range] at hk
        unfold sliceVal
        have h1 : (k / 2) * (k / 2 + 1) ≤ (2 * m + 1 - k % 2) * (2 * k + 1) := by
          have ha : k / 2 ≤ 2 * m + 1 - k % 2 := by omega
          have hb : k / 2 + 1 ≤ 2 * k + 1 := by omega
          exact Nat.mul_le_mul ha hb
        have h3 : 2 * (m + 1) + 1 - k % 2 = (2 * m + 1 - k % 2) + 2 := by omega
        rw [h3]
        have hmul : ((2 * m + 1 - k % 2) + 2) * (2 * k + 1) =
            (2 * m + 1 - k % 2) * (2 * k + 1) + 2 * (2 * k + 1) := by ring
        rw [hmul]; omega
      rw [Finset.sum_congr rfl hshift, Finset.sum_add_distrib]
      have hodd_sum : ∑ k ∈ Finset.range (2 * m + 1), 2 * (2 * k + 1) = 2 * (2 * m + 1) ^ 2 := by
        rw [← Finset.mul_sum]
        have hs : ∀ N : ℕ, ∑ k ∈ Finset.range N, (2 * k + 1) = N ^ 2 := by
          intro N; induction N with | zero => simp | succ N ihN => rw [Finset.sum_range_succ, ihN]; ring
        rw [hs]
      rw [hodd_sum]
      have hlast1 : sliceVal (2 * (m + 1)) (2 * m + 1) =
          (2 * m + 2) * (4 * m + 3) - m * (m + 1) := by
        unfold sliceVal
        have hmod : (2 * m + 1) % 2 = 1 := by omega
        have hdiv : (2 * m + 1) / 2 = m := by omega
        rw [hmod, hdiv]
        have : 2 * (m + 1) + 1 - 1 = 2 * m + 2 := by omega
        rw [this]; ring_nf
      have hlast2 : sliceVal (2 * (m + 1)) (2 * m + 1 + 1) =
          (2 * m + 3) * (4 * m + 5) - (m + 1) * (m + 2) := by
        unfold sliceVal
        have hmod : (2 * m + 1 + 1) % 2 = 0 := by omega
        have hdiv : (2 * m + 1 + 1) / 2 = m + 1 := by omega
        rw [hmod, hdiv]
        have : 2 * (m + 1) + 1 - 0 = 2 * m + 3 := by omega
        rw [this]; ring_nf
      rw [hlast1, hlast2]
      have hl1 : m * (m + 1) ≤ (2 * m + 2) * (4 * m + 3) := by nlinarith
      have hl2 : (m + 1) * (m + 2) ≤ (2 * m + 3) * (4 * m + 5) := by nlinarith
      have hs1 : ((2 * m + 2) * (4 * m + 3) - m * (m + 1)) + m * (m + 1) = (2 * m + 2) * (4 * m + 3) := by omega
      have hs2 : ((2 * m + 3) * (4 * m + 5) - (m + 1) * (m + 2)) + (m + 1) * (m + 2) = (2 * m + 3) * (4 * m + 5) := by omega
      nlinarith
  have hv0 : sliceVal (2 * m) (2 * m) = (2 * m + 1) * (4 * m + 1) - m * (m + 1) := by
    unfold sliceVal
    have hmod : (2 * m) % 2 = 0 := by omega
    have hdiv : (2 * m) / 2 = m := by omega
    rw [hmod, hdiv]
    have : 2 * m + 1 - 0 = 2 * m + 1 := by omega
    rw [this]; ring_nf
  have hle0 : m * (m + 1) ≤ (2 * m + 1) * (4 * m + 1) := by nlinarith
  have hs0 : ((2 * m + 1) * (4 * m + 1) - m * (m + 1)) + m * (m + 1) = (2 * m + 1) * (4 * m + 1) := by omega
  have hle_tot : sliceVal (2 * m) (2 * m) ≤ 2 * (∑ k ∈ Finset.range (2 * m + 1), sliceVal (2 * m) k) := by
    have hmem : 2 * m ∈ Finset.range (2 * m + 1) := Finset.mem_range.mpr (by omega)
    have := Finset.single_le_sum (f := fun k => sliceVal (2 * m) k) (fun _ _ => Nat.zero_le _) hmem
    omega
  have hsub_tot : (2 * (∑ k ∈ Finset.range (2 * m + 1), sliceVal (2 * m) k) - sliceVal (2 * m) (2 * m)) +
      sliceVal (2 * m) (2 * m) = 2 * (∑ k ∈ Finset.range (2 * m + 1), sliceVal (2 * m) k) := by omega
  rw [hv0] at hsub_tot ⊢
  nlinarith

private lemma sum_sliceVal_odd (m : ℕ) :
    12 * (2 * (∑ k ∈ Finset.range (2 * m + 2), sliceVal (2 * m + 1) k) - sliceVal (2 * m + 1) (2 * m + 1)) =
      22 * (2 * m + 1) ^ 3 + 33 * (2 * m + 1) ^ 2 + 26 * (2 * m + 1) + 3 := by
  have hsum : 24 * (∑ k ∈ Finset.range (2 * m + 2), sliceVal (2 * m + 1) k) =
      22 * (2 * m + 1) ^ 3 + 54 * (2 * m + 1) ^ 2 + 38 * (2 * m + 1) + 6 := by
    induction m with
    | zero => simp [sliceVal, Finset.sum_range_succ]
    | succ m ih =>
      rw [show 2 * (m + 1) + 2 = (2 * m + 2) + 2 by omega]
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hshift : ∀ k ∈ Finset.range (2 * m + 2),
          sliceVal (2 * (m + 1) + 1) k = sliceVal (2 * m + 1) k + 2 * (2 * k + 1) := by
        intro k hk; rw [Finset.mem_range] at hk
        unfold sliceVal
        have h1 : (k / 2) * (k / 2 + 1) ≤ (2 * m + 1 + 1 - k % 2) * (2 * k + 1) := by
          have ha : k / 2 ≤ 2 * m + 1 + 1 - k % 2 := by omega
          have hb : k / 2 + 1 ≤ 2 * k + 1 := by omega
          exact Nat.mul_le_mul ha hb
        have h3 : 2 * (m + 1) + 1 + 1 - k % 2 = (2 * m + 1 + 1 - k % 2) + 2 := by omega
        rw [h3]
        have hmul : ((2 * m + 1 + 1 - k % 2) + 2) * (2 * k + 1) =
            (2 * m + 1 + 1 - k % 2) * (2 * k + 1) + 2 * (2 * k + 1) := by ring
        rw [hmul]; omega
      rw [Finset.sum_congr rfl hshift, Finset.sum_add_distrib]
      have hodd_sum : ∑ k ∈ Finset.range (2 * m + 2), 2 * (2 * k + 1) = 2 * (2 * m + 2) ^ 2 := by
        rw [← Finset.mul_sum]
        have hs : ∀ N : ℕ, ∑ k ∈ Finset.range N, (2 * k + 1) = N ^ 2 := by
          intro N; induction N with | zero => simp | succ N ihN => rw [Finset.sum_range_succ, ihN]; ring
        rw [hs]
      rw [hodd_sum]
      have hlast1 : sliceVal (2 * (m + 1) + 1) (2 * m + 2) =
          (2 * m + 4) * (4 * m + 5) - (m + 1) * (m + 2) := by
        unfold sliceVal
        have hmod : (2 * m + 2) % 2 = 0 := by omega
        have hdiv : (2 * m + 2) / 2 = m + 1 := by omega
        rw [hmod, hdiv]
        have : 2 * (m + 1) + 1 + 1 - 0 = 2 * m + 4 := by omega
        rw [this]; ring_nf
      have hlast2 : sliceVal (2 * (m + 1) + 1) (2 * m + 2 + 1) =
          (2 * m + 3) * (4 * m + 7) - (m + 1) * (m + 2) := by
        unfold sliceVal
        have hmod : (2 * m + 2 + 1) % 2 = 1 := by omega
        have hdiv : (2 * m + 2 + 1) / 2 = m + 1 := by omega
        rw [hmod, hdiv]
        have : 2 * (m + 1) + 1 + 1 - 1 = 2 * m + 3 := by omega
        rw [this]; ring_nf
      rw [hlast1, hlast2]
      have hl1 : (m + 1) * (m + 2) ≤ (2 * m + 4) * (4 * m + 5) := by nlinarith
      have hl2 : (m + 1) * (m + 2) ≤ (2 * m + 3) * (4 * m + 7) := by nlinarith
      have hs1 : ((2 * m + 4) * (4 * m + 5) - (m + 1) * (m + 2)) + (m + 1) * (m + 2) = (2 * m + 4) * (4 * m + 5) := by omega
      have hs2 : ((2 * m + 3) * (4 * m + 7) - (m + 1) * (m + 2)) + (m + 1) * (m + 2) = (2 * m + 3) * (4 * m + 7) := by omega
      nlinarith
  have hv0 : sliceVal (2 * m + 1) (2 * m + 1) = (2 * m + 1) * (4 * m + 3) - m * (m + 1) := by
    unfold sliceVal
    have hmod : (2 * m + 1) % 2 = 1 := by omega
    have hdiv : (2 * m + 1) / 2 = m := by omega
    rw [hmod, hdiv]
    have : 2 * m + 1 + 1 - 1 = 2 * m + 1 := by omega
    rw [this]; ring_nf
  have hle0 : m * (m + 1) ≤ (2 * m + 1) * (4 * m + 3) := by nlinarith
  have hs0 : ((2 * m + 1) * (4 * m + 3) - m * (m + 1)) + m * (m + 1) = (2 * m + 1) * (4 * m + 3) := by omega
  have hle_tot : sliceVal (2 * m + 1) (2 * m + 1) ≤ 2 * (∑ k ∈ Finset.range (2 * m + 2), sliceVal (2 * m + 1) k) := by
    have hmem : 2 * m + 1 ∈ Finset.range (2 * m + 2) := Finset.mem_range.mpr (by omega)
    have := Finset.single_le_sum (f := fun k => sliceVal (2 * m + 1) k) (fun _ _ => Nat.zero_le _) hmem
    omega
  have hsub_tot : (2 * (∑ k ∈ Finset.range (2 * m + 2), sliceVal (2 * m + 1) k) - sliceVal (2 * m + 1) (2 * m + 1)) +
      sliceVal (2 * m + 1) (2 * m + 1) = 2 * (∑ k ∈ Finset.range (2 * m + 2), sliceVal (2 * m + 1) k) := by omega
  rw [hv0] at hsub_tot ⊢
  nlinarith

-- Express a(n) in terms of sliceVal
private lemma a_eq_sliceVal (n : ℕ) :
    a n = 2 * (∑ k ∈ Finset.range (n + 1), sliceVal n k) - sliceVal n n := by
  have ha : a n = ((box n).filter (isValid n)).card := by
    unfold a
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_ofFinset _ _
  rw [ha, card_valid_eq_sba, card_sbaSet_eq_sum]
  have hU : Finset.Icc (-(n : ℤ)) n =
      {0} ∪ ((Finset.Icc 1 n).image (fun j : ℕ => (j : ℤ)) ∪
             (Finset.Icc 1 n).image (fun j : ℕ => -(j : ℤ))) := by
    ext u
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton, Finset.mem_image]
    constructor
    · intro ⟨hu1, hu2⟩
      by_cases h0 : u = 0
      · exact Or.inl h0
      · right
        rcases lt_or_gt_of_ne h0 with hlt | hgt
        · right; exact ⟨u.natAbs, ⟨by omega, by omega⟩, by omega⟩
        · left; exact ⟨u.natAbs, ⟨by omega, by omega⟩, by omega⟩
    · rintro (rfl | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> omega
  have hd1 : Disjoint ({0} : Finset ℤ)
      ((Finset.Icc 1 n).image (fun j : ℕ => (j : ℤ)) ∪
       (Finset.Icc 1 n).image (fun j : ℕ => -(j : ℤ))) := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    rw [Finset.mem_singleton] at hx1; subst hx1
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Icc] at hx2
    rcases hx2 with ⟨j, hj, h⟩ | ⟨j, hj, h⟩ <;> omega
  have hd2 : Disjoint ((Finset.Icc 1 n).image (fun j : ℕ => (j : ℤ)))
      ((Finset.Icc 1 n).image (fun j : ℕ => -(j : ℤ))) := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    simp only [Finset.mem_image, Finset.mem_Icc] at hx1 hx2
    rcases hx1 with ⟨j1, hj1, rfl⟩; rcases hx2 with ⟨j2, hj2, h⟩; omega
  rw [hU, Finset.sum_union hd1, Finset.sum_union hd2, Finset.sum_singleton]
  rw [Finset.sum_image (fun a _ b _ h => by omega), Finset.sum_image (fun a _ b _ h => by omega)]
  have hneg : ∀ j ∈ Finset.Icc 1 n, sliceCard n (-(j : ℤ)) = sliceCard n (j : ℤ) :=
    fun j _ => sliceCard_neg n (j : ℤ)
  rw [Finset.sum_congr rfl hneg]
  have hpos : ∀ j ∈ Finset.Icc 1 n, sliceCard n (j : ℤ) = sliceVal n (n - j) :=
    fun j hj => sliceCard_nat n j (Finset.mem_Icc.mp hj).2
  rw [Finset.sum_congr rfl hpos]
  have h0 : sliceCard n 0 = sliceVal n n := by
    have := sliceCard_nat n 0 (Nat.zero_le n); simpa using this
  rw [h0]
  have hre : ∑ j ∈ Finset.Icc 1 n, sliceVal n (n - j) = ∑ k ∈ Finset.range n, sliceVal n k := by
    refine Finset.sum_bij (fun j _ => n - j) ?_ ?_ ?_ ?_
    · intro j hj; rw [Finset.mem_Icc] at hj; rw [Finset.mem_range]; omega
    · intro j1 hj1 j2 hj2 h; rw [Finset.mem_Icc] at hj1 hj2; omega
    · intro k hk; rw [Finset.mem_range] at hk
      exact ⟨n - k, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro _ _; rfl
  rw [hre, Finset.sum_range_succ]
  omega

theorem main :
    (∀ n : ℕ, 1 ≤ n → Even n → 12 * a n = 22 * n ^ 3 + 33 * n ^ 2 + 26 * n + 12) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → 12 * a n = 22 * n ^ 3 + 33 * n ^ 2 + 26 * n + 3) := by
  constructor
  · rintro n _ ⟨m, rfl⟩
    have h2m : m + m = 2 * m := by omega
    rw [h2m, a_eq_sliceVal]
    exact sum_sliceVal_even m
  · rintro n _ ⟨m, rfl⟩
    rw [a_eq_sliceVal]
    exact sum_sliceVal_odd m

end
end ProofA202254

theorem OMA.solution : type_of% @OMA.S_oeis_a202254.main :=
  ProofA202254.main

import OMAStatements.S_oeis_a248836
import Mathlib

namespace OMA.P_oeis_a248836

open OMA.S_oeis_a248836

-- Part 1: 1-parameter combinatorial DP for a248836 n

private def validArray (n : ℕ) (x : Fin n → ℕ) : Prop :=
  (∀ i : Fin n, x i ≤ i.1 + 1) ∧
    (∀ v : ℕ, (Finset.univ.filter (fun i : Fin n => x i = v)).card ≤ 2)

private def dupCount (n : ℕ) (x : Fin n → ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter
    (fun v => (Finset.univ.filter (fun i : Fin n => x i = v)).card = 2)).card

private def validSet (n : ℕ) : Set (Fin n → ℕ) :=
  {x | validArray n x}

private lemma validSet_finite (n : ℕ) : (validSet n).Finite := by
  have hsub : validSet n ⊆
      (fun f : Fin n → Fin (n + 2) => fun i => (f i).1) '' Set.univ := by
    intro x hx
    refine ⟨fun i => ⟨x i, by have := hx.1 i; omega⟩, Set.mem_univ _, ?_⟩
    funext i; rfl
  exact (Set.finite_univ.image _).subset hsub

private noncomputable def validFinset (n : ℕ) : Finset (Fin n → ℕ) :=
  (validSet_finite n).toFinset

private lemma mem_validFinset {n : ℕ} {x : Fin n → ℕ} :
    x ∈ validFinset n ↔ validArray n x := by
  simp [validFinset, validSet]

private lemma a248836_eq_card (n : ℕ) : a248836 n = (validFinset n).card := by
  unfold a248836
  rw [← Set.ncard_coe_finset]
  congr 1; ext x; simp [mem_validFinset, validArray]

private def dp : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k =>
    (k + 2) * dp n k +
      if 1 ≤ k then (n - 2 * (k - 1)) * dp n (k - 1) else 0

-- For a valid array x of length n with k = dupCount n x:
-- Every value x i lies in range (n + 1).
-- Partition range (n + 1) by multiplicity 0, 1, 2:
--   c0 + c1 + c2 = n + 1, and c1 + 2 * c2 = n!
--   So c0 = k + 1, c1 = n - 2 * k!
private lemma mult_counts {n : ℕ} {x : Fin n → ℕ} (hx : validArray n x) :
    let S := Finset.range (n + 1)
    let mult := fun v => (Finset.univ.filter (fun i : Fin n => x i = v)).card
    let c0 := (S.filter (fun v => mult v = 0)).card
    let c1 := (S.filter (fun v => mult v = 1)).card
    let c2 := (S.filter (fun v => mult v = 2)).card
    c0 = c2 + 1 ∧ c1 + 2 * c2 = n := by
  intro S mult c0 c1 c2
  have hbound : ∀ v, mult v ≤ 2 := hx.2
  have hsum_card : c0 + c1 + c2 = n + 1 := by
    have hdisj01 : Disjoint (S.filter (fun v => mult v = 0)) (S.filter (fun v => mult v = 1)) := by
      rw [Finset.disjoint_left]; intro v h1 h2; simp at h1 h2; omega
    have hdisj012 : Disjoint
        (S.filter (fun v => mult v = 0) ∪ S.filter (fun v => mult v = 1))
        (S.filter (fun v => mult v = 2)) := by
      rw [Finset.disjoint_left]; intro v h1 h2; simp at h1 h2; omega
    have hunion : S.filter (fun v => mult v = 0) ∪ S.filter (fun v => mult v = 1) ∪
        S.filter (fun v => mult v = 2) = S := by
      ext v; simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ((⟨hv, _⟩ | ⟨hv, _⟩) | ⟨hv, _⟩) <;> exact hv
      · intro hv
        have hb := hbound v
        rcases (by omega : mult v = 0 ∨ mult v = 1 ∨ mult v = 2) with h | h | h
        · left; left; exact ⟨hv, h⟩
        · left; right; exact ⟨hv, h⟩
        · right; exact ⟨hv, h⟩
    have hcard := congr_arg Finset.card hunion
    rw [Finset.card_union_of_disjoint hdisj012, Finset.card_union_of_disjoint hdisj01,
      Finset.card_range] at hcard
    exact hcard
  have hsum_mult : ∑ v ∈ S, mult v = n := by
    have hmaps : ∀ i ∈ (Finset.univ : Finset (Fin n)), x i ∈ S := by
      intro i _; simp only [S, Finset.mem_range]
      have := hx.1 i; omega
    have hfib := Finset.sum_card_fiberwise_eq_card_filter (s := Finset.univ) (t := S) (g := x)
    have hfilt : (Finset.univ.filter (fun i : Fin n => x i ∈ S)) = Finset.univ := by
      ext i; simp [hmaps i (Finset.mem_univ i)]
    rw [hfilt, Finset.card_univ, Fintype.card_fin] at hfib
    exact hfib
  have hsum_split : ∑ v ∈ S, mult v = c1 + 2 * c2 := by
    have hdisj01 : Disjoint (S.filter (fun v => mult v = 0)) (S.filter (fun v => mult v = 1)) := by
      rw [Finset.disjoint_left]; intro v h1 h2; simp at h1 h2; omega
    have hdisj012 : Disjoint
        (S.filter (fun v => mult v = 0) ∪ S.filter (fun v => mult v = 1))
        (S.filter (fun v => mult v = 2)) := by
      rw [Finset.disjoint_left]; intro v h1 h2; simp at h1 h2; omega
    have hunion : S.filter (fun v => mult v = 0) ∪ S.filter (fun v => mult v = 1) ∪
        S.filter (fun v => mult v = 2) = S := by
      ext v; simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ((⟨hv, _⟩ | ⟨hv, _⟩) | ⟨hv, _⟩) <;> exact hv
      · intro hv
        have hb := hbound v
        rcases (by omega : mult v = 0 ∨ mult v = 1 ∨ mult v = 2) with h | h | h
        · left; left; exact ⟨hv, h⟩
        · left; right; exact ⟨hv, h⟩
        · right; exact ⟨hv, h⟩
    rw [← hunion, Finset.sum_union hdisj012, Finset.sum_union hdisj01]
    have s0 : ∑ v ∈ S.filter (fun v => mult v = 0), mult v = 0 :=
      Finset.sum_eq_zero fun v hv => (Finset.mem_filter.mp hv).2
    have s1 : ∑ v ∈ S.filter (fun v => mult v = 1), mult v = c1 := by
      rw [Finset.sum_congr rfl fun v hv => (Finset.mem_filter.mp hv).2, Finset.sum_const, smul_eq_mul, mul_one]
    have s2 : ∑ v ∈ S.filter (fun v => mult v = 2), mult v = 2 * c2 := by
      rw [Finset.sum_congr rfl fun v hv => (Finset.mem_filter.mp hv).2, Finset.sum_const, smul_eq_mul, mul_comm]
    rw [s0, s1, s2, zero_add]
  omega

private lemma card_dupCount_eq_dp :
    ∀ n k : ℕ, ((validFinset n).filter (fun x => dupCount n x = k)).card = dp n k := by
  intro n
  induction n with
  | zero =>
    intro k
    have h0 : validFinset 0 = {Fin.elim0} := by
      ext x; simp only [mem_validFinset, Finset.mem_singleton]
      constructor
      · intro _; funext i; exact Fin.elim0 i
      · rintro rfl; exact ⟨fun i => Fin.elim0 i, fun v => by simp⟩
    rw [h0]
    have hdup : dupCount 0 Fin.elim0 = 0 := by simp [dupCount]
    cases k with
    | zero => simp [dp, Finset.filter_singleton, hdup]
    | succ k' => simp [dp, Finset.filter_singleton, hdup]
  | succ n ih =>
    intro k
    -- Map y : Fin (n+1) → ℕ to (init y : Fin n → ℕ, last y : ℕ)
    let init : (Fin (n + 1) → ℕ) → (Fin n → ℕ) := fun y i => y i.castSucc
    -- Split valid arrays of length n+1 with dupCount = k by whether last value appeared 0 times or 1 time in init
    let multInit := fun (x : Fin n → ℕ) (v : ℕ) =>
      (Finset.univ.filter (fun i : Fin n => x i = v)).card
    have hmult_snoc : ∀ (x : Fin n → ℕ) (a v : ℕ),
        (Finset.univ.filter (fun i : Fin (n + 1) => Fin.snoc (α := fun _ => ℕ) x a i = v)).card =
          multInit x v + (if a = v then 1 else 0) := by
      intro x a v
      have hsplit : Finset.univ.filter (fun i : Fin (n + 1) => Fin.snoc (α := fun _ => ℕ) x a i = v) =
          (Finset.univ.filter (fun i : Fin n => x i = v)).map Fin.castSuccEmb ∪
          if a = v then {Fin.last n} else ∅ := by
        ext i
        refine Fin.lastCases ?_ ?_ i
        · by_cases hav : a = v <;> simp [Fin.snoc_last, hav]
        · intro j; by_cases hav : a = v <;> simp [Fin.snoc_castSucc, Fin.castSucc_ne_last, hav]
      rw [hsplit, Finset.card_union_of_disjoint]
      · rw [Finset.card_map]
        split_ifs <;> simp [multInit]
      · rw [Finset.disjoint_left]
        intro i h1 h2
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Fin.castSuccEmb_apply] at h1
        obtain ⟨j, _, rfl⟩ := h1
        split_ifs at h2 with h
        · simp [Fin.castSucc_ne_last] at h2
        · simp at h2
    have hdup_snoc : ∀ (x : Fin n → ℕ) (a : ℕ), validArray n x → a ≤ n + 1 →
        multInit x a ≤ 1 →
        dupCount (n + 1) (Fin.snoc (α := fun _ => ℕ) x a) =
          dupCount n x + (if multInit x a = 1 then 1 else 0) := by
      intro x a hx ha hma
      unfold dupCount
      -- Value n + 1 never appears in x, so its multiplicity in snoc x a is at most 1 (never 2)!
      have hn1_ne2 : (Finset.univ.filter (fun i : Fin (n + 1) => Fin.snoc (α := fun _ => ℕ) x a i = n + 1)).card ≠ 2 := by
        rw [hmult_snoc]
        have h0 : multInit x (n + 1) = 0 := by
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro i _; have := hx.1 i; omega
        rw [h0]; split_ifs <;> omega
      rw [Finset.range_add_one, Finset.filter_insert, if_neg hn1_ne2]
      by_cases h1 : multInit x a = 1
      · simp only [h1, ↓reduceIte]
        have ha_mem : a ∈ Finset.range (n + 1) := by
          rw [Finset.mem_range]
          by_contra hge
          have h0 : multInit x a = 0 := by
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro i _; have := hx.1 i; omega
          omega
        have hset : (Finset.range (n + 1)).filter
            (fun v => (Finset.univ.filter (fun i : Fin (n + 1) => Fin.snoc (α := fun _ => ℕ) x a i = v)).card = 2) =
            insert a ((Finset.range (n + 1)).filter (fun v => multInit x v = 2)) := by
          ext v; simp only [Finset.mem_filter, Finset.mem_insert, hmult_snoc]
          by_cases hva : v = a
          · subst hva; simp [ha_mem, h1]
          · have hav : a ≠ v := fun h => hva h.symm
            simp [hva, hav]
        rw [hset, Finset.card_insert_of_notMem]
        simp [h1]
      · simp only [h1, ↓reduceIte, add_zero]
        congr 1; ext v
        simp only [Finset.mem_filter, hmult_snoc]
        by_cases hva : a = v
        · subst hva
          dsimp only [multInit] at hma h1 ⊢
          simp only [↓reduceIte, Finset.mem_range]
          constructor <;> (rintro ⟨_, h⟩; omega)
        · dsimp only [multInit]
          simp [hva]
    -- Now count pairs (x, a) with validArray n x, a ≤ n + 1, multInit x a ≤ 1, and dupCount (snoc x a) = k!
    let P0 := ((validFinset n).filter (fun x => dupCount n x = k)).sigma fun x =>
      (Finset.range (n + 2)).filter (fun a => multInit x a = 0)
    let P1 := ((validFinset n).filter (fun x => dupCount n x = k - 1 ∧ 1 ≤ k)).sigma fun x =>
      (Finset.range (n + 2)).filter (fun a => multInit x a = 1)
    -- Show card P0 = (k + 2) * dp n k and card P1 = (if 1 ≤ k then (n - 2*(k-1)) * dp n (k-1) else 0)
    have hP0 : P0.card = (k + 2) * dp n k := by
      rw [Finset.card_sigma, ← ih k, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_congr rfl
      intro x hx
      simp only [Finset.mem_filter, mem_validFinset] at hx
      have hmc := mult_counts hx.1
      have h0_n1 : multInit x (n + 1) = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i _; have := hx.1.1 i; omega
      rw [Finset.range_add_one, Finset.filter_insert, if_pos h0_n1,
        Finset.card_insert_of_notMem (by simp)]
      have hdup_eq : ((Finset.range (n + 1)).filter (fun v => multInit x v = 2)).card = k := hx.2
      dsimp only [multInit] at hmc hdup_eq ⊢
      omega
    have hP1 : P1.card = if 1 ≤ k then (n - 2 * (k - 1)) * dp n (k - 1) else 0 := by
      by_cases hk1 : 1 ≤ k
      · simp only [hk1, ↓reduceIte, and_true, P1]
        rw [Finset.card_sigma, ← ih (k - 1), mul_comm, ← smul_eq_mul, ← Finset.sum_const]
        apply Finset.sum_congr rfl
        intro x hx
        simp only [Finset.mem_filter, mem_validFinset] at hx
        have hmc := mult_counts hx.1
        have h1_n1 : multInit x (n + 1) ≠ 1 := by
          have h0 : multInit x (n + 1) = 0 := by
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro i _; have := hx.1.1 i; omega
          omega
        rw [Finset.range_add_one, Finset.filter_insert, if_neg h1_n1]
        have hdup_eq : ((Finset.range (n + 1)).filter (fun v => multInit x v = 2)).card = k - 1 := hx.2
        dsimp only [multInit] at hmc hdup_eq ⊢
        omega
      · simp only [hk1, ↓reduceIte, and_false, P1, Finset.card_sigma, Finset.filter_false,
          Finset.sum_empty]
    -- Bijection between (validFinset (n+1)).filter (dupCount = k) and P0 ⊕ P1!
    have hdisj : Disjoint P0 P1 := by
      rw [Finset.disjoint_left]
      intro p h0 h1
      simp only [P0, P1, Finset.mem_sigma, Finset.mem_filter] at h0 h1
      omega
    have hcard_eq : ((validFinset (n + 1)).filter (fun y => dupCount (n + 1) y = k)).card =
        (P0 ∪ P1).card := by
      apply Finset.card_bij'
        (fun y _ => (⟨init y, y (Fin.last n)⟩ : Σ _ : Fin n → ℕ, ℕ))
        (fun p _ => Fin.snoc (α := fun _ => ℕ) p.1 p.2)
      · intro y hy
        simp only [Finset.mem_filter, mem_validFinset] at hy
        have hsnoc : y = Fin.snoc (α := fun _ => ℕ) (init y) (y (Fin.last n)) := by
          funext i; refine Fin.lastCases ?_ ?_ i <;> simp [init, Fin.snoc_last, Fin.snoc_castSucc]
        have hinit : validArray n (init y) := by
          refine ⟨fun i => hy.1.1 i.castSucc, fun v => ?_⟩
          have hle := hy.1.2 v
          rw [hsnoc, hmult_snoc] at hle
          dsimp only [multInit] at hle
          omega
        have hlast_le : y (Fin.last n) ≤ n + 1 := hy.1.1 (Fin.last n)
        have hmlast : multInit (init y) (y (Fin.last n)) ≤ 1 := by
          have hle := hy.1.2 (y (Fin.last n))
          rw [hsnoc, hmult_snoc] at hle; simp at hle; omega
        have hdup := hdup_snoc (init y) (y (Fin.last n)) hinit hlast_le hmlast
        rw [← hsnoc, hy.2] at hdup
        simp only [Finset.mem_union, P0, P1, Finset.mem_sigma, Finset.mem_filter, mem_validFinset,
          Finset.mem_range]
        by_cases hm1 : multInit (init y) (y (Fin.last n)) = 1
        · right
          simp only [hm1, ↓reduceIte] at hdup
          exact ⟨⟨hinit, by omega, by omega⟩, by omega, hm1⟩
        · left
          simp only [hm1, ↓reduceIte, add_zero] at hdup
          exact ⟨⟨hinit, by omega⟩, by omega, by omega⟩
      · intro p hp
        simp only [Finset.mem_union, P0, P1, Finset.mem_sigma, Finset.mem_filter, mem_validFinset,
          Finset.mem_range] at hp
        simp only [Finset.mem_filter, mem_validFinset]
        rcases hp with ⟨⟨hx, hdup⟩, ha, hm0⟩ | ⟨⟨hx, hdup, hk1⟩, ha, hm1⟩
        · refine ⟨⟨fun i => Fin.lastCases (by simp [Fin.snoc_last]; omega)
              (fun j => by simp [Fin.snoc_castSucc]; exact hx.1 j) i,
            fun v => by
              rw [hmult_snoc]
              by_cases hv : p.2 = v
              · subst hv; simp [hm0]
              · simp [hv]; exact hx.2 v⟩, ?_⟩
          rw [hdup_snoc p.1 p.2 hx (by omega) (by omega)]
          simp [hm0, hdup]
        · refine ⟨⟨fun i => Fin.lastCases (by simp [Fin.snoc_last]; omega)
              (fun j => by simp [Fin.snoc_castSucc]; exact hx.1 j) i,
            fun v => by
              rw [hmult_snoc]
              by_cases hv : p.2 = v
              · subst hv; simp [hm1]
              · simp [hv]; exact hx.2 v⟩, ?_⟩
          rw [hdup_snoc p.1 p.2 hx (by omega) (by omega)]
          simp [hm1]; omega
      · intro y _
        funext i; refine Fin.lastCases ?_ ?_ i <;> simp [init, Fin.snoc_last, Fin.snoc_castSucc]
      · intro p _
        rcases p with ⟨x, a⟩
        ext
        · simp [init, Fin.snoc_castSucc]
        · simp [Fin.snoc_last]
    rw [hcard_eq, Finset.card_union_of_disjoint hdisj, hP0, hP1, dp]

private lemma dp_eq_zero_of_gt : ∀ n k : ℕ, n < k → dp n k = 0 := by
  intro n
  induction n with
  | zero =>
    intro k hk; cases k with | zero => omega | succ k' => simp [dp]
  | succ n ih =>
    intro k hk
    simp only [dp]
    have h1 : dp n k = 0 := ih k (by omega)
    have h2 : dp n (k - 1) = 0 := ih (k - 1) (by omega)
    simp [h1, h2]

private lemma a248836_eq_sum_dp (n : ℕ) :
    a248836 n = ∑ k ∈ Finset.range (n + 1), dp n k := by
  rw [a248836_eq_card]
  have hmaps : ∀ x ∈ validFinset n, dupCount n x ∈ Finset.range (n + 1) := by
    intro x hx
    rw [Finset.mem_range]
    have hmc := mult_counts (mem_validFinset.mp hx)
    dsimp only at hmc
    unfold dupCount
    omega
  have hfilt : (validFinset n).filter (fun x => dupCount n x ∈ Finset.range (n + 1)) = validFinset n := by
    ext x; simp only [Finset.mem_filter, and_iff_left_iff_imp]; exact hmaps x
  rw [← hfilt, ← Finset.sum_card_fiberwise_eq_card_filter (s := validFinset n) (t := Finset.range (n + 1))
    (g := dupCount n)]
  apply Finset.sum_congr rfl
  intro k _
  exact card_dupCount_eq_dp n k

-- Part 2: Exact PDE in PowerSeries (Polynomial ℚ) proving (1 - sin x)^2 * a248836Egf = 1!

private abbrev QPoly := Polynomial ℚ
private abbrev BivPS := PowerSeries QPoly

private noncomputable def dpPoly (n : ℕ) : QPoly :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.C (dp n k : ℚ) * Polynomial.X ^ k

private lemma dpPoly_rec (n : ℕ) :
    dpPoly (n + 1) =
      2 * dpPoly n + Polynomial.X * Polynomial.derivative (dpPoly n) +
        (n : QPoly) * Polynomial.X * dpPoly n -
        2 * Polynomial.X ^ 2 * Polynomial.derivative (dpPoly n) := by
  -- Compare coefficients of y^k for every k!
  ext k
  have hcoeff_dp : ∀ m j : ℕ, (dpPoly m).coeff j = (dp m j : ℚ) := by
    intro m j
    simp only [dpPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hjm : j < m + 1
    · rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hbj; simp [Ne.symm hbj]
      · intro hj; exact absurd (Finset.mem_range.mpr hjm) hj
    · rw [Finset.sum_eq_zero]
      · symm; norm_cast; exact dp_eq_zero_of_gt m j (by omega)
      · intro b hb; have := Finset.mem_range.mp hb; simp [show j ≠ b by omega]
  have h1 : (2 * dpPoly n).coeff k = 2 * (dp n k : ℚ) := by
    rw [Polynomial.coeff_ofNat_mul, hcoeff_dp]
  have h2 : (Polynomial.X * Polynomial.derivative (dpPoly n)).coeff k = (k : ℚ) * (dp n k : ℚ) := by
    cases k with
    | zero => simp
    | succ k' =>
      rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative, hcoeff_dp]
      push_cast; ring
  have h3 : ((n : QPoly) * Polynomial.X * dpPoly n).coeff k =
      if 1 ≤ k then (n : ℚ) * (dp n (k - 1) : ℚ) else 0 := by
    rw [mul_assoc, Polynomial.coeff_natCast_mul]
    cases k with
    | zero => simp
    | succ k' => simp [Polynomial.coeff_X_mul, hcoeff_dp]
  have h4 : (2 * Polynomial.X ^ 2 * Polynomial.derivative (dpPoly n)).coeff k =
      if 1 ≤ k then 2 * ((k - 1 : ℕ) : ℚ) * (dp n (k - 1) : ℚ) else 0 := by
    rw [mul_assoc, Polynomial.coeff_ofNat_mul, Polynomial.coeff_X_pow_mul']
    cases k with
    | zero => simp
    | succ k' =>
      cases k' with
      | zero => simp
      | succ k'' =>
        simp only [show 2 ≤ k'' + 1 + 1 by omega, ↓reduceIte,
          show k'' + 1 + 1 - 2 = k'' by omega, show 1 ≤ k'' + 1 + 1 by omega,
          show k'' + 1 + 1 - 1 = k'' + 1 by omega, Polynomial.coeff_derivative, hcoeff_dp]
        push_cast; ring
  rw [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_add, hcoeff_dp, h1, h2, h3, h4]
  simp only [dp]
  by_cases hk1 : 1 ≤ k
  · simp only [hk1, ↓reduceIte]
    by_cases hle : 2 * (k - 1) ≤ n
    · push_cast [hle]; ring
    · have hgt : n < 2 * (k - 1) := by omega
      have hdp0 : dp n (k - 1) = 0 := by
        -- Actually wait: dp n (k - 1) = 0 whenever 2 * (k - 1) > n!
        -- Prove by induction on n: if 2 * j > n then dp n j = 0!
        have hzero2 : ∀ m j : ℕ, m < 2 * j → dp m j = 0 := by
          intro m
          induction m with
          | zero => intro j hj; cases j with | zero => omega | succ j' => simp [dp]
          | succ m ih =>
            intro j hj
            simp only [dp]
            have ha : dp m j = 0 := ih j (by omega)
            by_cases hj1 : 1 ≤ j
            · by_cases hlt : m < 2 * (j - 1)
              · simp [ha, hj1, ih (j - 1) hlt]
              · have : m - 2 * (j - 1) = 0 := by omega
                simp [ha, hj1, this]
            · simp [ha, hj1]
        exact hzero2 n (k - 1) hgt
      simp only [hdp0, Nat.cast_zero, mul_zero, add_zero, sub_zero]
      push_cast; ring
  · simp only [hk1, ↓reduceIte, add_zero, sub_zero]
    push_cast; ring

-- Explicit g_n(y) for G(x, y) = F(x, y)^(-1/2):
--   g(0) = 1
--   g(2m + 1) = -(1 - 2y)^m
--   g(2m + 2) = (1 - y) * (1 - 2y)^m
private noncomputable def gPoly : ℕ → QPoly
  | 0 => 1
  | n + 1 =>
    if n % 2 = 0 then -((1 - 2 * Polynomial.X) ^ (n / 2))
    else (1 - Polynomial.X) * (1 - 2 * Polynomial.X) ^ (n / 2)

private lemma gPoly_rec (n : ℕ) :
    gPoly (n + 1) =
      -gPoly n + (n : QPoly) * Polynomial.X * gPoly n -
        (2 * Polynomial.X ^ 2 - Polynomial.X) * Polynomial.derivative (gPoly n) := by
  cases n with
  | zero =>
    simp [gPoly]
  | succ m =>
    by_cases hm : m % 2 = 0
    · obtain ⟨q, rfl⟩ : ∃ q, m = 2 * q := ⟨m / 2, by omega⟩
      have h1 : gPoly (2 * q + 1) = -((1 - 2 * Polynomial.X) ^ q) := by
        simp [gPoly, show 2 * q % 2 = 0 by omega, show 2 * q / 2 = q by omega]
      have h2 : gPoly (2 * q + 2) = (1 - Polynomial.X) * (1 - 2 * Polynomial.X) ^ q := by
        simp [gPoly, show (2 * q + 1) / 2 = q by omega]
      rw [h1, h2]
      cases q with
      | zero => simp; ring
      | succ q' =>
        have hd : Polynomial.derivative (-((1 - 2 * Polynomial.X : QPoly) ^ (q' + 1))) =
            2 * ((q' + 1 : ℕ) : QPoly) * (1 - 2 * Polynomial.X) ^ q' := by
          rw [map_neg, Polynomial.derivative_pow, Polynomial.derivative_sub,
            Polynomial.derivative_one, Polynomial.derivative_mul,
            Polynomial.derivative_ofNat, Polynomial.derivative_X]
          simp only [Nat.add_sub_cancel, Polynomial.C_eq_natCast]
          push_cast; ring
        rw [hd]
        push_cast
        ring
    · obtain ⟨q, rfl⟩ : ∃ q, m = 2 * q + 1 := ⟨m / 2, by omega⟩
      have h1 : gPoly (2 * q + 2) = (1 - Polynomial.X) * (1 - 2 * Polynomial.X) ^ q := by
        simp [gPoly, show (2 * q + 1) / 2 = q by omega]
      have h2 : gPoly (2 * q + 3) = -((1 - 2 * Polynomial.X) ^ (q + 1)) := by
        simp [gPoly, show (2 * q + 2) % 2 = 0 by omega, show (2 * q + 2) / 2 = q + 1 by omega]
      rw [h1, h2]
      cases q with
      | zero =>
        simp only [pow_zero, mul_one, pow_one, Polynomial.derivative_sub, Polynomial.derivative_one,
          Polynomial.derivative_X, Nat.mul_zero, zero_add]
        push_cast
        ring
      | succ q' =>
        have hd : Polynomial.derivative
            ((1 - Polynomial.X : QPoly) * (1 - 2 * Polynomial.X) ^ (q' + 1)) =
            -((1 - 2 * Polynomial.X) ^ (q' + 1)) -
              2 * ((q' + 1 : ℕ) : QPoly) * (1 - Polynomial.X) * (1 - 2 * Polynomial.X) ^ q' := by
          rw [Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_one,
            Polynomial.derivative_X, Polynomial.derivative_pow, Polynomial.derivative_sub,
            Polynomial.derivative_one, Polynomial.derivative_mul,
            Polynomial.derivative_ofNat, Polynomial.derivative_X]
          simp only [Nat.add_sub_cancel, Polynomial.C_eq_natCast]
          push_cast; ring
        rw [hd]
        push_cast
        ring

-- Define the differential operator L on sequences of QPoly representing e.g.f.s:
--   For A(x) = ∑ a_n x^n / n!, (1 - x y) A_x + (2 y^2 - y) A_y has x^n/n! coeff:
--   L(a)_n = a_{n+1} - n * y * a_n + (2 y^2 - y) * a_n'!
-- Notice L is a DERIVATION on binomial convolution (a * b)_n = ∑ C(n, k) a_k b_{n-k}!
private noncomputable def egfMul (a b : ℕ → QPoly) (n : ℕ) : QPoly :=
  ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : QPoly) * a k * b (n - k)

private noncomputable def L_op (a : ℕ → QPoly) (n : ℕ) : QPoly :=
  a (n + 1) - (n : QPoly) * Polynomial.X * a n +
    (2 * Polynomial.X ^ 2 - Polynomial.X) * Polynomial.derivative (a n)

private lemma L_op_egfMul (a b : ℕ → QPoly) (n : ℕ) :
    L_op (egfMul a b) n = egfMul (L_op a) b n + egfMul a (L_op b) n := by
  unfold L_op egfMul
  -- 1) Derivative of egfMul a b n:
  have hderiv : Polynomial.derivative
      (∑ k ∈ Finset.range (n + 1), (Nat.choose n k : QPoly) * a k * b (n - k)) =
      ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : QPoly) * Polynomial.derivative (a k) * b (n - k) +
      ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : QPoly) * a k * Polynomial.derivative (b (n - k)) := by
    rw [map_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [Polynomial.derivative_mul, Polynomial.derivative_mul,
      show (Nat.choose n k : QPoly) = Polynomial.C (Nat.choose n k : ℚ) by simp,
      Polynomial.derivative_C]
    ring
  -- 2) Shift (egfMul a b (n + 1)) = egfMul (a . + 1) b n + egfMul a (b . + 1) n (Pascal's rule!)
  have hshift :
      ∑ k ∈ Finset.range (n + 2), (Nat.choose (n + 1) k : QPoly) * a k * b (n + 1 - k) =
      ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : QPoly) * a (k + 1) * b (n - k) +
      ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : QPoly) * a k * b (n - k + 1) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
    have hsplit : ∑ k ∈ Finset.range (n + 1),
        (Nat.choose (n + 1) (k + 1) : QPoly) * a (k + 1) * b (n + 1 - (k + 1)) =
        ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : QPoly) * a (k + 1) * b (n - k) +
        ∑ k ∈ Finset.range (n + 1), (Nat.choose n (k + 1) : QPoly) * a (k + 1) * b (n - k) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [Nat.choose_succ_succ, Nat.cast_add, Nat.succ_sub_succ]
      ring
    rw [hsplit]
    have hreindex :
        ∑ k ∈ Finset.range (n + 1), (Nat.choose n (k + 1) : QPoly) * a (k + 1) * b (n - k) +
          a 0 * b (n + 1) =
        ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : QPoly) * a k * b (n - k + 1) := by
      rw [Finset.sum_range_succ' (fun k => (Nat.choose n k : QPoly) * a k * b (n - k + 1)) n]
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
      rw [Finset.sum_range_succ (fun k => (Nat.choose n (k + 1) : QPoly) * a (k + 1) * b (n - k)) n]
      simp only [Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k < n := Finset.mem_range.mp hk
      have hsub : n - k = n - (k + 1) + 1 := by omega
      rw [hsub]
    linear_combination hreindex
  -- 3) n * y * egfMul a b n = egfMul (k * y * a_k) b n + egfMul a ((n-k) * y * b_{n-k}) n!
  have hny :
      (n : QPoly) * Polynomial.X *
        ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : QPoly) * a k * b (n - k) =
      ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : QPoly) * ((k : QPoly) * Polynomial.X * a k) * b (n - k) +
      ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : QPoly) * a k * (((n - k : ℕ) : QPoly) * Polynomial.X * b (n - k)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hadd : ((k : ℕ) : QPoly) + ((n - k : ℕ) : QPoly) = (n : QPoly) := by
      rw [← Nat.cast_add, Nat.add_sub_of_le hkn]
    linear_combination -hadd * (Polynomial.X * (Nat.choose n k : QPoly) * a k * b (n - k))
  rw [hderiv, hshift, hny]
  simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

private lemma egfMul_g_g_dp :
    ∀ n : ℕ, egfMul (egfMul gPoly gPoly) dpPoly n = if n = 0 then 1 else 0 := by
  let h := egfMul (egfMul gPoly gPoly) dpPoly
  have hL_dp : ∀ n, L_op dpPoly n = 2 * dpPoly n := by
    intro n; unfold L_op; linear_combination dpPoly_rec n
  have hL_g : ∀ n, L_op gPoly n = -gPoly n := by
    intro n; unfold L_op; linear_combination gPoly_rec n
  have hL_gg : ∀ n, L_op (egfMul gPoly gPoly) n = -2 * egfMul gPoly gPoly n := by
    intro n
    rw [L_op_egfMul]
    unfold egfMul
    simp_rw [hL_g]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  have hL_h : ∀ n, L_op h n = 0 := by
    intro n
    dsimp only [h]
    rw [L_op_egfMul]
    have h1 : L_op (egfMul gPoly gPoly) = fun k => -2 * egfMul gPoly gPoly k := funext hL_gg
    have h2 : L_op dpPoly = fun k => 2 * dpPoly k := funext hL_dp
    rw [h1, h2]
    unfold egfMul
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero; intro k _; ring
  intro n
  induction n with
  | zero =>
    simp [egfMul, gPoly, dpPoly, dp]
  | succ n ih =>
    have h0 := hL_h n
    unfold L_op at h0
    have hprev : h n = if n = 0 then 1 else 0 := ih
    rw [hprev] at h0
    cases n with
    | zero =>
      rw [if_pos rfl] at h0
      simp only [Nat.cast_zero, zero_mul, sub_zero, Polynomial.derivative_one, mul_zero,
        add_zero] at h0
      exact h0
    | succ m =>
      rw [if_neg (Nat.succ_ne_zero m)] at h0
      simp only [mul_zero, sub_zero, Polynomial.derivative_zero, add_zero] at h0
      exact h0

-- Evaluate at y = 1 to get (1 - sinSeries)^2 * a248836Egf = 1!
private lemma gPoly_eval_one (n : ℕ) :
    (gPoly n).eval 1 =
      (Nat.factorial n : ℚ) * PowerSeries.coeff n (1 - sinSeries) := by
  cases n with
  | zero =>
    simp [gPoly, sinSeries]
  | succ m =>
    simp only [map_sub, PowerSeries.coeff_one, Nat.succ_ne_zero, ↓reduceIte, zero_sub,
      sinSeries, PowerSeries.coeff_mk]
    by_cases hm : m % 2 = 0
    · have hodd : (m + 1) % 2 = 1 := by omega
      have hdiv : (m + 1) / 2 = m / 2 := by omega
      simp only [gPoly, hm, hodd, hdiv, ↓reduceIte, Polynomial.eval_neg, Polynomial.eval_pow,
        Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_ofNat,
        Polynomial.eval_X]
      have hfac : (Nat.factorial (m + 1) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      field_simp [hfac]
      norm_num
    · have hev : (m + 1) % 2 ≠ 1 := by omega
      simp [gPoly, hm, hev]

private lemma dpPoly_eval_one (n : ℕ) :
    (dpPoly n).eval 1 = (a248836 n : ℚ) := by
  rw [a248836_eq_sum_dp]
  simp [dpPoly, Polynomial.eval_finsetSum]

private lemma manyama_egf : (1 - sinSeries) ^ 2 * a248836Egf = 1 := by
  ext n
  have h := congr_arg (Polynomial.eval (1 : ℚ)) (egfMul_g_g_dp n)
  have heval_mul : ∀ (a b : ℕ → QPoly) (m : ℕ),
      (egfMul a b m).eval 1 =
        ∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℚ) * (a k).eval 1 * (b (m - k)).eval 1 := by
    intro a b m
    simp [egfMul, Polynomial.eval_finsetSum]
  rw [heval_mul] at h
  -- Rewrite binomial convolution into PowerSeries multiplication!
  have hps : ∀ (A B : PowerSeries ℚ) (m : ℕ),
      (Nat.factorial m : ℚ) * PowerSeries.coeff m (A * B) =
        ∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℚ) *
          ((Nat.factorial k : ℚ) * PowerSeries.coeff k A) *
          ((Nat.factorial (m - k) : ℚ) * PowerSeries.coeff (m - k) B) := by
    intro A B m
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hch : (Nat.choose m k : ℚ) * (Nat.factorial k : ℚ) * (Nat.factorial (m - k) : ℚ) =
        (Nat.factorial m : ℚ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkm
    linear_combination -hch * PowerSeries.coeff k A * PowerSeries.coeff (m - k) B
  have hgg : ∀ k : ℕ, (egfMul gPoly gPoly k).eval 1 =
      (Nat.factorial k : ℚ) * PowerSeries.coeff k ((1 - sinSeries) ^ 2) := by
    intro k
    rw [pow_two, hps, heval_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [gPoly_eval_one j, gPoly_eval_one (k - j)]
  have hlhs : (Nat.factorial n : ℚ) * PowerSeries.coeff n ((1 - sinSeries) ^ 2 * a248836Egf) =
      (if n = 0 then (1 : ℚ) else 0) := by
    rw [hps]
    have hterm : ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℚ) * ((Nat.factorial k : ℚ) * PowerSeries.coeff k ((1 - sinSeries) ^ 2)) *
        ((Nat.factorial (n - k) : ℚ) * PowerSeries.coeff (n - k) a248836Egf) =
        ∑ k ∈ Finset.range (n + 1),
          (Nat.choose n k : ℚ) * (egfMul gPoly gPoly k).eval 1 * (dpPoly (n - k)).eval 1 := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hgg k, dpPoly_eval_one (n - k), a248836Egf, PowerSeries.coeff_mk]
      have hfac : (Nat.factorial (n - k) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      field_simp [hfac]
    rw [hterm, h]
    split_ifs <;> simp
  have hfac : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [PowerSeries.coeff_one]
  by_cases hn : n = 0
  · subst hn
    simp only [Nat.factorial_zero, Nat.cast_one, one_mul, ↓reduceIte] at hlhs ⊢
    exact hlhs
  · simp only [hn, ↓reduceIte] at hlhs ⊢
    exact (mul_eq_zero.mp hlhs).resolve_left hfac

-- Part 3: Kurkov's Seidel triangle R(n+1, 0) = a248836 n via Entringer identity!

private def cosCoeff (j : ℕ) : ℚ :=
  if j % 2 = 0 then (-1 : ℚ) ^ (j / 2) else 0

private def nsinCoeff (i : ℕ) : ℚ :=
  if i % 2 = 1 then -((-1 : ℚ) ^ (i / 2)) else 0

private lemma cosCoeff_succ (j : ℕ) : cosCoeff (j + 1) = nsinCoeff j := by
  unfold cosCoeff nsinCoeff
  by_cases hj : j % 2 = 0
  · have h1 : (j + 1) % 2 ≠ 0 := by omega
    have h2 : j % 2 ≠ 1 := by omega
    simp [h1, h2]
  · have h1 : (j + 1) % 2 = 0 := by omega
    have h2 : j % 2 = 1 := by omega
    have hdiv : (j + 1) / 2 = j / 2 + 1 := by omega
    simp [h1, h2, hdiv, pow_succ]

private lemma nsinCoeff_succ (i : ℕ) : nsinCoeff (i + 1) = -cosCoeff i := by
  unfold cosCoeff nsinCoeff
  by_cases hi : i % 2 = 0
  · have h1 : (i + 1) % 2 = 1 := by omega
    have hdiv : (i + 1) / 2 = i / 2 := by omega
    simp [hi, h1, hdiv]
  · have h1 : (i + 1) % 2 ≠ 1 := by omega
    simp [hi, h1]

private lemma isUnit_one_sub_sin : IsUnit (1 - sinSeries) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, map_sub, map_one, sinSeries, PowerSeries.constantCoeff_mk]
  simp

private noncomputable def inv1MinusSin : PowerSeries ℚ :=
  ↑(isUnit_one_sub_sin.unit⁻¹)

private lemma one_sub_sin_mul_inv : (1 - sinSeries) * inv1MinusSin = 1 :=
  isUnit_one_sub_sin.mul_val_inv

private noncomputable def dSeq (n : ℕ) : ℚ :=
  (Nat.factorial n : ℚ) * PowerSeries.coeff n (inv1MinusSin ^ 3)

private noncomputable def W (a b : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (b + 1), (Nat.choose b j : ℚ) * cosCoeff j * dSeq (a + b - j) +
  ∑ i ∈ Finset.range (a + 1), (Nat.choose a i : ℚ) * nsinCoeff i * dSeq (a + b - i)

private lemma W_step (a b : ℕ) : W a (b + 1) - W (a + 1) b = W b a := by
  -- Use Pascal's identity on both binomial sums!
  have hcos :
      ∑ j ∈ Finset.range (b + 2), (Nat.choose (b + 1) j : ℚ) * cosCoeff j * dSeq (a + (b + 1) - j) -
      ∑ j ∈ Finset.range (b + 1), (Nat.choose b j : ℚ) * cosCoeff j * dSeq (a + 1 + b - j) =
      ∑ j ∈ Finset.range (b + 1), (Nat.choose b j : ℚ) * nsinCoeff j * dSeq (b + a - j) := by
    rw [Finset.sum_range_succ' (fun j => (Nat.choose (b + 1) j : ℚ) * cosCoeff j * dSeq (a + (b + 1) - j)) (b + 1)]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
    have hsplit : ∑ j ∈ Finset.range (b + 1),
        (Nat.choose (b + 1) (j + 1) : ℚ) * cosCoeff (j + 1) * dSeq (a + (b + 1) - (j + 1)) =
        ∑ j ∈ Finset.range (b + 1), (Nat.choose b j : ℚ) * cosCoeff (j + 1) * dSeq (a + b - j) +
        ∑ j ∈ Finset.range (b + 1), (Nat.choose b (j + 1) : ℚ) * cosCoeff (j + 1) * dSeq (a + b - j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [Nat.choose_succ_succ, Nat.cast_add, show a + (b + 1) - (j + 1) = a + b - j by omega]
      ring
    rw [hsplit]
    have hshift :
        ∑ j ∈ Finset.range (b + 1), (Nat.choose b (j + 1) : ℚ) * cosCoeff (j + 1) * dSeq (a + b - j) +
          cosCoeff 0 * dSeq (a + (b + 1)) =
        ∑ j ∈ Finset.range (b + 1), (Nat.choose b j : ℚ) * cosCoeff j * dSeq (a + 1 + b - j) := by
      rw [Finset.sum_range_succ' (fun j => (Nat.choose b j : ℚ) * cosCoeff j * dSeq (a + 1 + b - j)) b]
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero,
        show a + (b + 1) = a + 1 + b by omega]
      rw [Finset.sum_range_succ (fun j => (Nat.choose b (j + 1) : ℚ) * cosCoeff (j + 1) * dSeq (a + b - j)) b]
      simp only [Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [show a + 1 + b - (j + 1) = a + b - j by omega]
    have hmain :
        ∑ j ∈ Finset.range (b + 1), (Nat.choose b j : ℚ) * cosCoeff (j + 1) * dSeq (a + b - j) =
        ∑ j ∈ Finset.range (b + 1), (Nat.choose b j : ℚ) * nsinCoeff j * dSeq (b + a - j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [cosCoeff_succ, add_comm a b]
    linear_combination hshift + hmain
  have hsin :
      ∑ i ∈ Finset.range (a + 1), (Nat.choose a i : ℚ) * nsinCoeff i * dSeq (a + (b + 1) - i) -
      ∑ i ∈ Finset.range (a + 2), (Nat.choose (a + 1) i : ℚ) * nsinCoeff i * dSeq (a + 1 + b - i) =
      ∑ i ∈ Finset.range (a + 1), (Nat.choose a i : ℚ) * cosCoeff i * dSeq (b + a - i) := by
    rw [Finset.sum_range_succ' (fun i => (Nat.choose (a + 1) i : ℚ) * nsinCoeff i * dSeq (a + 1 + b - i)) (a + 1)]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
    have hsplit : ∑ i ∈ Finset.range (a + 1),
        (Nat.choose (a + 1) (i + 1) : ℚ) * nsinCoeff (i + 1) * dSeq (a + 1 + b - (i + 1)) =
        ∑ i ∈ Finset.range (a + 1), (Nat.choose a i : ℚ) * nsinCoeff (i + 1) * dSeq (a + b - i) +
        ∑ i ∈ Finset.range (a + 1), (Nat.choose a (i + 1) : ℚ) * nsinCoeff (i + 1) * dSeq (a + b - i) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [Nat.choose_succ_succ, Nat.cast_add, show a + 1 + b - (i + 1) = a + b - i by omega]
      ring
    rw [hsplit]
    have hshift :
        ∑ i ∈ Finset.range (a + 1), (Nat.choose a (i + 1) : ℚ) * nsinCoeff (i + 1) * dSeq (a + b - i) +
          nsinCoeff 0 * dSeq (a + 1 + b) =
        ∑ i ∈ Finset.range (a + 1), (Nat.choose a i : ℚ) * nsinCoeff i * dSeq (a + (b + 1) - i) := by
      rw [Finset.sum_range_succ' (fun i => (Nat.choose a i : ℚ) * nsinCoeff i * dSeq (a + (b + 1) - i)) a]
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero,
        show a + (b + 1) = a + 1 + b by omega]
      rw [Finset.sum_range_succ (fun i => (Nat.choose a (i + 1) : ℚ) * nsinCoeff (i + 1) * dSeq (a + b - i)) a]
      simp only [Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [show a + b - i = a + 1 + b - (i + 1) by omega]
    have hmain :
        -(∑ i ∈ Finset.range (a + 1), (Nat.choose a i : ℚ) * nsinCoeff (i + 1) * dSeq (a + b - i)) =
        ∑ i ∈ Finset.range (a + 1), (Nat.choose a i : ℚ) * cosCoeff i * dSeq (b + a - i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [nsinCoeff_succ, add_comm a b]; ring
    linear_combination -hshift + hmain
  unfold W
  linear_combination hcos + hsin

private lemma a248836Egf_eq_inv_sq : a248836Egf = inv1MinusSin ^ 2 := by
  have h1 := manyama_egf
  have h2 := one_sub_sin_mul_inv
  calc a248836Egf = 1 * a248836Egf := (one_mul _).symm
    _ = ((1 - sinSeries) * inv1MinusSin) ^ 2 * a248836Egf := by rw [h2, one_pow]
    _ = inv1MinusSin ^ 2 * ((1 - sinSeries) ^ 2 * a248836Egf) := by ring
    _ = inv1MinusSin ^ 2 := by rw [h1, mul_one]

private lemma W_zero_right (a : ℕ) : W a 0 = (a248836 a : ℚ) := by
  unfold W
  simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton, Nat.choose_zero_right,
    Nat.cast_one, one_mul, Nat.add_zero, Nat.sub_zero, cosCoeff, Nat.zero_mod, ↓reduceIte,
    Nat.zero_div, pow_zero]
  -- dSeq a + ∑_{i=0..a} C(a, i) * nsinCoeff i * dSeq (a - i)
  -- = a! * coeff a ((1 - sinSeries) * inv1MinusSin^3) = a! * coeff a (inv1MinusSin^2) = a248836 a!
  have hprod : (1 - sinSeries) * inv1MinusSin ^ 3 = inv1MinusSin ^ 2 := by
    calc (1 - sinSeries) * inv1MinusSin ^ 3
        = ((1 - sinSeries) * inv1MinusSin) * inv1MinusSin ^ 2 := by ring
      _ = inv1MinusSin ^ 2 := by rw [one_sub_sin_mul_inv, one_mul]
  have hps : (Nat.factorial a : ℚ) * PowerSeries.coeff a ((1 - sinSeries) * inv1MinusSin ^ 3) =
      ∑ i ∈ Finset.range (a + 1), (Nat.choose a i : ℚ) *
        ((Nat.factorial i : ℚ) * PowerSeries.coeff i (1 - sinSeries)) * dSeq (a - i) := by
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hia : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hch : (Nat.choose a i : ℚ) * (Nat.factorial i : ℚ) * (Nat.factorial (a - i) : ℚ) =
        (Nat.factorial a : ℚ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hia
    unfold dSeq
    linear_combination -hch * PowerSeries.coeff i (1 - sinSeries) * PowerSeries.coeff (a - i) (inv1MinusSin ^ 3)
  have hsplit : ∑ i ∈ Finset.range (a + 1), (Nat.choose a i : ℚ) *
        ((Nat.factorial i : ℚ) * PowerSeries.coeff i (1 - sinSeries)) * dSeq (a - i) =
      dSeq a + ∑ i ∈ Finset.range (a + 1), (Nat.choose a i : ℚ) * nsinCoeff i * dSeq (a - i) := by
    rw [Finset.sum_range_succ' (fun i => (Nat.choose a i : ℚ) *
        ((Nat.factorial i : ℚ) * PowerSeries.coeff i (1 - sinSeries)) * dSeq (a - i)) a]
    rw [Finset.sum_range_succ' (fun i => (Nat.choose a i : ℚ) * nsinCoeff i * dSeq (a - i)) a]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero, Nat.factorial_zero,
      PowerSeries.coeff_zero_eq_constantCoeff, map_sub, map_one, sinSeries,
      PowerSeries.constantCoeff_mk, show (0 : ℕ) % 2 ≠ 1 by decide, ↓reduceIte, sub_zero,
      nsinCoeff, zero_mul, add_zero]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [PowerSeries.coeff_one, Nat.succ_ne_zero, ↓reduceIte, zero_sub,
      PowerSeries.coeff_mk]
    by_cases hodd : (i + 1) % 2 = 1
    · simp only [hodd, ↓reduceIte]
      have hfac : (Nat.factorial (i + 1) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      field_simp [hfac]
    · simp [hodd]
  rw [← hsplit, ← hps, hprod, ← a248836Egf_eq_inv_sq, a248836Egf, PowerSeries.coeff_mk]
  have hfac : (Nat.factorial a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp [hfac]

private def cosSeries : PowerSeries ℚ :=
  PowerSeries.mk fun n => cosCoeff n / (Nat.factorial n : ℚ)

private lemma derivative_sinSeries : PowerSeries.derivative ℚ sinSeries = cosSeries := by
  ext n
  rw [PowerSeries.coeff_derivative, sinSeries, cosSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  by_cases hn : n % 2 = 0
  · have hodd : (n + 1) % 2 = 1 := by omega
    have hdiv : (n + 1) / 2 = n / 2 := by omega
    simp only [hodd, hdiv, cosCoeff, hn, ↓reduceIte, Nat.factorial_succ]
    have hfac : (Nat.factorial n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hn1 : ((n : ℚ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp [hfac, hn1]
  · have hodd : (n + 1) % 2 ≠ 1 := by omega
    simp [hodd, cosCoeff, hn]

private lemma W_zero_left (b : ℕ) : 2 * W 0 b = (a248836 (b + 1) : ℚ) := by
  unfold W
  simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton, Nat.choose_zero_right,
    Nat.cast_one, one_mul, nsinCoeff, show (0 : ℕ) % 2 ≠ 1 by decide, ↓reduceIte, zero_mul,
    add_zero]
  -- ∑_{j=0..b} C(b, j) cosCoeff j * dSeq (b - j) = b! * coeff b (cosSeries * inv1MinusSin^3)!
  -- And derivative (inv1MinusSin^2) = 2 * cosSeries * inv1MinusSin^3!
  have hderiv_inv : PowerSeries.derivative ℚ (inv1MinusSin ^ 2) = 2 * cosSeries * inv1MinusSin ^ 3 := by
    have h1 := congr_arg (PowerSeries.derivative ℚ) one_sub_sin_mul_inv
    rw [Derivation.leibniz, Derivation.map_one_eq_zero, map_sub, Derivation.map_one_eq_zero,
      zero_sub, derivative_sinSeries] at h1
    simp only [smul_eq_mul] at h1
    have h2 : (1 - sinSeries) * PowerSeries.derivative ℚ inv1MinusSin = cosSeries * inv1MinusSin := by
      linear_combination h1
    have h3 : PowerSeries.derivative ℚ inv1MinusSin = cosSeries * inv1MinusSin ^ 2 := by
      calc PowerSeries.derivative ℚ inv1MinusSin
          = 1 * PowerSeries.derivative ℚ inv1MinusSin := (one_mul _).symm
        _ = (inv1MinusSin * (1 - sinSeries)) * PowerSeries.derivative ℚ inv1MinusSin := by
            rw [mul_comm inv1MinusSin, one_sub_sin_mul_inv]
        _ = inv1MinusSin * ((1 - sinSeries) * PowerSeries.derivative ℚ inv1MinusSin) := by ring
        _ = inv1MinusSin * (cosSeries * inv1MinusSin) := by rw [h2]
        _ = cosSeries * inv1MinusSin ^ 2 := by ring
    rw [pow_two, Derivation.leibniz, h3]; simp only [smul_eq_mul]; ring
  have hps : (Nat.factorial b : ℚ) * PowerSeries.coeff b (cosSeries * inv1MinusSin ^ 3) =
      ∑ j ∈ Finset.range (b + 1), (Nat.choose b j : ℚ) * cosCoeff j * dSeq (b - j) := by
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjb : j ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hch : (Nat.choose b j : ℚ) * (Nat.factorial j : ℚ) * (Nat.factorial (b - j) : ℚ) =
        (Nat.factorial b : ℚ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjb
    unfold dSeq cosSeries
    simp only [PowerSeries.coeff_mk]
    have hfj : (Nat.factorial j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hfbj : (Nat.factorial (b - j) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp [hfj, hfbj]
    linear_combination -hch * cosCoeff j * PowerSeries.coeff (b - j) (inv1MinusSin ^ 3)
  rw [← hps]
  have hc := congr_arg (PowerSeries.coeff b) hderiv_inv
  rw [← a248836Egf_eq_inv_sq, PowerSeries.coeff_derivative, a248836Egf, PowerSeries.coeff_mk] at hc
  rw [mul_assoc, show (2 : PowerSeries ℚ) = PowerSeries.C 2 from (map_ofNat PowerSeries.C 2).symm,
    PowerSeries.coeff_C_mul] at hc
  have hfac : (Nat.factorial b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hb1 : ((b : ℚ) + 1) ≠ 0 := by positivity
  calc 2 * ((Nat.factorial b : ℚ) * PowerSeries.coeff b (cosSeries * inv1MinusSin ^ 3))
      = (Nat.factorial b : ℚ) * (2 * PowerSeries.coeff b (cosSeries * inv1MinusSin ^ 3)) := by ring
    _ = (Nat.factorial b : ℚ) * ((a248836 (b + 1) : ℚ) / (Nat.factorial (b + 1) : ℚ) * ((b : ℚ) + 1)) := by
        rw [← hc]
    _ = (a248836 (b + 1) : ℚ) := by
        rw [Nat.factorial_succ]; push_cast; field_simp [hfac, hb1]

private lemma kurkovR_eq_a :
    ∀ n : ℕ, (kurkovR (n + 1) 0 : ℚ) = (a248836 n : ℚ) := by
  -- Better: state cleanly for n >= 1!
  have hbase0 : kurkovR 1 0 = 1 := by
    rw [kurkovR]; simp [kurkovR]
  have hbase1 : kurkovR 1 1 = 1 := by
    rw [kurkovR]; simp [hbase0]
  have ha0 : a248836 0 = 1 := by
    rw [a248836_eq_sum_dp]; simp [dp]
  -- Prove for all m >= 0:
  --   1) kurkovR (m + 1) 0 = a248836 m
  --   2) kurkovR (m + 2) (a + 1) = W a (m - a) for 0 ≤ a ≤ m
  --   3) kurkovR (m + 1) (m + 1) = W 0 m (for m >= 0) -> wait: kurkovR 1 1 = 1 = W 0 0?
  --      Check W 0 0 = a248836 1 / 2 = 2 / 2 = 1! YES!!
  have hmain : ∀ m : ℕ,
      (kurkovR (m + 1) 0 : ℚ) = (a248836 m : ℚ) ∧
      (kurkovR (m + 1) (m + 1) : ℚ) = W 0 m ∧
      (∀ a : ℕ, a ≤ m → (kurkovR (m + 2) (a + 1) : ℚ) = W a (m - a)) := by
    intro m
    induction m with
    | zero =>
      have hW00 : W 0 0 = 1 := by
        have := W_zero_right 0; rw [ha0] at this; exact this
      have hR21 : kurkovR 2 1 = 1 := by
        rw [kurkovR]; simp [hbase0]
      refine ⟨by simp [hbase0, ha0], by simp [hbase1, hW00], ?_⟩
      intro a ha
      have ha0' : a = 0 := by omega
      subst ha0'
      simp [hR21, hW00]
    | succ m ih =>
      -- Step 1: kurkovR (m + 2) 0 = 2 * kurkovR (m + 1) (m + 1) = 2 * W 0 m = a248836 (m + 1)!
      have hR0 : (kurkovR (m + 2) 0 : ℚ) = (a248836 (m + 1) : ℚ) := by
        have hdef0 : kurkovR (m + 2) 0 = ∑ j ∈ Finset.range (m + 2), kurkovR (m + 1) j := by
          rw [kurkovR]; simp
        have hdefn : kurkovR (m + 1) (m + 1) = ∑ j ∈ Finset.range (m + 1), kurkovR (m + 1) j := by
          rw [kurkovR]; simp [Fin.sum_univ_eq_sum_range]
        rw [hdef0, Finset.sum_range_succ, ← hdefn]
        push_cast
        rw [ih.2.1]
        linarith [W_zero_left m]
      -- Step 2: kurkovR (m + 2) (m + 2) = ∑_{j=0..m+1} kurkovR (m + 2) j
      -- Wait: first compute kurkovR (m + 3) (a + 1) = W a (m + 1 - a) for a = m + 1 down to 0!
      have hR3 : ∀ d : ℕ, ∀ a : ℕ, a + d = m + 1 →
          (kurkovR (m + 3) (a + 1) : ℚ) = W a d := by
        intro d
        induction d with
        | zero =>
          intro a ha
          have ha_eq : a = m + 1 := by omega
          subst ha_eq
          have hdef : kurkovR (m + 3) (m + 2) = kurkovR (m + 2) 0 := by
            rw [kurkovR]; simp
          rw [hdef, hR0, W_zero_right]
        | succ d' ihd =>
          intro a ha
          have hdef1 : kurkovR (m + 3) (a + 1) =
              ∑ j ∈ Finset.range (m + 2 - a), kurkovR (m + 2) j := by
            rw [kurkovR]; simp [show a + 1 < m + 3 by omega, show m + 3 - (a + 1) = m + 2 - a by omega]
          have hdef2 : kurkovR (m + 3) (a + 2) =
              ∑ j ∈ Finset.range (m + 1 - a), kurkovR (m + 2) j := by
            rw [kurkovR]; simp [show a + 2 < m + 3 by omega, show m + 3 - (a + 2) = m + 1 - a by omega]
          have hsub : kurkovR (m + 3) (a + 1) =
              kurkovR (m + 3) (a + 2) + kurkovR (m + 2) (m + 1 - a) := by
            rw [hdef1, show m + 2 - a = (m + 1 - a) + 1 by omega, Finset.sum_range_succ, ← hdef2]
          rw [hsub]; push_cast
          rw [ihd (a + 1) (by omega)]
          have hm1a : m + 1 - a = d' + 1 := by omega
          rw [hm1a, ih.2.2 d' (by omega), show m - d' = a by omega]
          linarith [W_step a d']
      -- Step 3: kurkovR (m + 2) (m + 2) = kurkovR (m + 3) 1 = W 0 (m + 1)!
      have hRdiag : (kurkovR (m + 2) (m + 2) : ℚ) = W 0 (m + 1) := by
        have h1 : kurkovR (m + 2) (m + 2) = ∑ j ∈ Finset.range (m + 2), kurkovR (m + 2) j := by
          rw [kurkovR]; simp [Fin.sum_univ_eq_sum_range]
        have h2 : kurkovR (m + 3) 1 = ∑ j ∈ Finset.range (m + 2), kurkovR (m + 2) j := by
          rw [kurkovR]; simp
        rw [h1, ← h2]
        exact hR3 (m + 1) 0 (by omega)
      refine ⟨hR0, hRdiag, fun a ha => hR3 (m + 1 - a) a (by omega)⟩
  intro n
  exact (hmain n).1

private theorem main_proved :
    (1 - sinSeries) ^ 2 * a248836Egf = 1 ∧
      ∀ n : ℕ, a248836 n = kurkovR (n + 1) 0 := by
  refine ⟨manyama_egf, fun n => ?_⟩
  have h := kurkovR_eq_a n
  exact_mod_cast h.symm

end OMA.P_oeis_a248836

theorem OMA.solution : type_of% @OMA.S_oeis_a248836.main :=
  OMA.P_oeis_a248836.main_proved

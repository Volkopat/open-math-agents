import OMAStatements.S_oeis_a368846

-- Problem: A368846: |Sum_{j=0..k} T(k + j, k)| = A229580(k + 1) for all k >= 0.
-- Credit: @ceejcake
-- Proof:
-- 1. Left-hand side (binomial identity via Polynomial ℤ):
--    For k >= 1, expand ((1 + X)^2 - 1)^(2k - 1) * (1 + X) two ways:
--    - By the binomial theorem, its [X^(2k)] coefficient is sum_{m < 2k} (-1)^m * C(2k-1, m) * C(4k-1-2m, 2k),
--      which truncates to m < k and (via j = k - 1 - m) equals (-1)^(k-1)/2 * sum_{j=0..k} T(k+j, k).
--    - Since (1 + X)^2 - 1 = X * (X + 2), it equals X^(2k-1) * (X + 2)^(2k-1) * (1 + X), whose [X^(2k)]
--      coefficient is [X^1]((X + 2)^(2k-1) * (1 + X)) = (2k - 1) * 2^(2k - 2) + 2^(2k - 1) = (2k + 1) * 2^(2k - 2).
--    Thus |sum_{j=0..k} T(k+j, k)| = (2k + 1) * 2^(2k - 1) for k >= 1 (and 1 for k = 0).
-- 2. Right-hand side (path-graph bijection):
--    Flattening an (k+1) x 2 array in row-major order turns horizontal + antidiagonal edges into the
--    path graph P_{2k+2}. For k >= 1, contracting the unique monochromatic edge t in Fin (2k+1) gives a
--    proper 3-coloring u of P_{2k+1} with u 0 = 0 and u 1 = 1, which has exactly 2^(2k-1) choices.
--    Hence a229580 (k + 1) = (2k + 1) * 2^(2k - 1) for k >= 1 (and 1 for k = 0).

namespace ProofA368846

open OMA.S_oeis_a368846 Polynomial
open scoped Classical
noncomputable section

-- Part 1: Binomial sum identity via Polynomial ℤ
private lemma coeff_one_add_X_pow (m r : ℕ) :
    ((1 + X : ℤ[X]) ^ m).coeff r = (Nat.choose m r : ℤ) := by
  rw [add_comm, add_pow]
  simp only [one_pow, mul_one, finsetSum_coeff, coeff_X_pow_mul']
  rw [Finset.sum_eq_single r]
  · by_cases hr : r ≤ m
    · simp
    · simp [Nat.choose_eq_zero_of_lt (by omega : m < r)]
  · intro b _ hbr
    simp only [coeff_natCast_ite]
    split_ifs <;> omega
  · intro hr
    have hlt : m < r := by simp only [Finset.mem_range, not_lt] at hr; omega
    simp [Nat.choose_eq_zero_of_lt hlt]

private lemma coeff_one_X_add_two_pow (m : ℕ) (hm : 1 ≤ m) :
    ((X + C (2 : ℤ)) ^ m * (1 + X)).coeff 1 = ((m + 2 : ℕ) : ℤ) * 2 ^ (m - 1) := by
  have h1 : ((X + C (2 : ℤ)) ^ m * (1 + X)).coeff 1 =
      ((X + C (2 : ℤ)) ^ m).coeff 1 + ((X + C (2 : ℤ)) ^ m).coeff 0 := by
    rw [mul_add, mul_one, coeff_add, coeff_mul_X]
  rw [h1, add_pow]
  simp only [finsetSum_coeff]
  have hc1 : ∑ x ∈ Finset.range (m + 1),
      ((if 1 = x then (1 : ℤ) else 0) * 2 ^ (m - x)) * (Nat.choose m x : ℤ) =
      (m : ℤ) * 2 ^ (m - 1) := by
    rw [Finset.sum_eq_single 1]
    · simp [Nat.choose_one_right]; ring
    · intro b _ hb; simp [hb.symm]
    · intro h; simp at h; omega
  have hc0 : ∑ x ∈ Finset.range (m + 1),
      ((if 0 = x then (1 : ℤ) else 0) * 2 ^ (m - x)) * (Nat.choose m x : ℤ) =
      2 ^ m := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro b _ hb; simp [hb.symm]
    · intro h; simp at h
  have hc1' : ∑ x ∈ Finset.range (m + 1),
      ((X ^ x * C (2 : ℤ) ^ (m - x) * (Nat.choose m x : ℤ[X])).coeff 1) = (m : ℤ) * 2 ^ (m - 1) := by
    convert hc1 using 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← map_pow, ← map_natCast C, mul_assoc, ← map_mul, coeff_mul_C, coeff_X_pow]; ring
  have hc0' : ∑ x ∈ Finset.range (m + 1),
      ((X ^ x * C (2 : ℤ) ^ (m - x) * (Nat.choose m x : ℤ[X])).coeff 0) = 2 ^ m := by
    convert hc0 using 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← map_pow, ← map_natCast C, mul_assoc, ← map_mul, coeff_mul_C, coeff_X_pow]; ring
  rw [hc1', hc0']
  have hpow : (2 : ℤ) ^ m = 2 * (2 : ℤ) ^ (m - 1) := by
    have : m = (m - 1) + 1 := by omega
    conv_lhs => rw [this]
    rw [pow_succ']
  rw [hpow]; push_cast; ring

private lemma lhs_sum_eq (k : ℕ) (hk : 1 ≤ k) :
    ∑ j ∈ Finset.range (k + 1), T (k + j) k = (-1 : ℤ) ^ (k - 1) * ((2 * k + 1 : ℕ) : ℤ) * 2 ^ (2 * k - 1) := by
  -- Expand P = ((1 + X)^2 - 1)^(2k - 1) * (1 + X) in two ways and take coeff (2k)
  let P : ℤ[X] := ((1 + X) ^ 2 - 1) ^ (2 * k - 1) * (1 + X)
  have hP1 : P.coeff (2 * k) =
      ∑ m ∈ Finset.range (2 * k), (-1 : ℤ) ^ m * (Nat.choose (2 * k - 1) m : ℤ) *
        (Nat.choose (4 * k - 1 - 2 * m) (2 * k) : ℤ) := by
    have hbin : P = ∑ m ∈ Finset.range (2 * k),
        C ((-1 : ℤ) ^ m * (Nat.choose (2 * k - 1) m : ℤ)) * (1 + X) ^ (4 * k - 1 - 2 * m) := by
      have hsub : ((1 + X : ℤ[X]) ^ 2 - 1) = (-1 : ℤ[X]) + (1 + X) ^ 2 := by ring
      dsimp only [P]
      rw [hsub, add_pow, Finset.sum_mul]
      have hr : 2 * k - 1 + 1 = 2 * k := by omega
      rw [hr]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm_lt : m < 2 * k := Finset.mem_range.mp hm
      have hexp : 2 * (2 * k - 1 - m) + 1 = 4 * k - 1 - 2 * m := by omega
      rw [← pow_mul, mul_assoc, mul_assoc]
      have hc : ((-1 : ℤ[X]) ^ m) = C ((-1 : ℤ) ^ m) := by simp
      have hcn : ((Nat.choose (2 * k - 1) m : ℤ[X])) = C (Nat.choose (2 * k - 1) m : ℤ) := by simp
      rw [hc, hcn, map_mul]
      calc C ((-1 : ℤ) ^ m) * ((1 + X) ^ (2 * (2 * k - 1 - m)) * (C (Nat.choose (2 * k - 1) m : ℤ) * (1 + X)))
          = C ((-1 : ℤ) ^ m) * C (Nat.choose (2 * k - 1) m : ℤ) * ((1 + X) ^ (2 * (2 * k - 1 - m)) * (1 + X)) := by ring
        _ = C ((-1 : ℤ) ^ m) * C (Nat.choose (2 * k - 1) m : ℤ) * (1 + X) ^ (2 * (2 * k - 1 - m) + 1) := by rw [pow_succ]
        _ = C ((-1 : ℤ) ^ m) * C (Nat.choose (2 * k - 1) m : ℤ) * (1 + X) ^ (4 * k - 1 - 2 * m) := by rw [hexp]
    rw [hbin, finset_sum_coeff]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [coeff_C_mul, coeff_one_add_X_pow]
  have hP2 : P.coeff (2 * k) = ((2 * k + 1 : ℕ) : ℤ) * 2 ^ (2 * k - 2) := by
    have hfac : P = X ^ (2 * k - 1) * ((X + C (2 : ℤ)) ^ (2 * k - 1) * (1 + X)) := by
      dsimp only [P]
      have hsq : ((1 + X : ℤ[X]) ^ 2 - 1) = X * (X + C (2 : ℤ)) := by simp; ring
      rw [hsq, mul_pow]; ring
    rw [hfac, coeff_X_pow_mul']
    have hge : 2 * k - 1 ≤ 2 * k := by omega
    have hsub : 2 * k - (2 * k - 1) = 1 := by omega
    rw [if_pos hge, hsub, coeff_one_X_add_two_pow (2 * k - 1) (by omega)]
    have e1 : 2 * k - 1 + 2 = 2 * k + 1 := by omega
    have e2 : 2 * k - 1 - 1 = 2 * k - 2 := by omega
    rw [e1, e2]
  -- Truncate hP1 to m < k (since 4k - 1 - 2m < 2k for m >= k)
  have htrunc : ∑ m ∈ Finset.range (2 * k), (-1 : ℤ) ^ m * (Nat.choose (2 * k - 1) m : ℤ) *
        (Nat.choose (4 * k - 1 - 2 * m) (2 * k) : ℤ) =
      ∑ m ∈ Finset.range k, (-1 : ℤ) ^ m * (Nat.choose (2 * k - 1) m : ℤ) *
        (Nat.choose (4 * k - 1 - 2 * m) (2 * k) : ℤ) := by
    rw [← Finset.sum_subset (Finset.range_mono (by omega : k ≤ 2 * k))]
    intro m hm hmk
    have hm1 : k ≤ m := by simp only [Finset.mem_range, not_lt] at hmk; exact hmk
    have hlt : 4 * k - 1 - 2 * m < 2 * k := by omega
    simp [Nat.choose_eq_zero_of_lt hlt]
  have hval : ∑ m ∈ Finset.range k, (-1 : ℤ) ^ m * (Nat.choose (2 * k - 1) m : ℤ) *
      (Nat.choose (4 * k - 1 - 2 * m) (2 * k) : ℤ) = ((2 * k + 1 : ℕ) : ℤ) * 2 ^ (2 * k - 2) := by
    rw [← htrunc, ← hP1, hP2]
  -- Relate sum_{j=0..k} T(k+j, k) to the truncated sum via j = k - 1 - m
  have hT_last : T (k + k) k = 0 := by
    unfold T; rw [if_neg (by omega)]
    have : Nat.choose (2 * k - 1) (k + k) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [this]
  rw [Finset.sum_range_succ, hT_last, add_zero]
  have hsum_eq : ∑ j ∈ Finset.range k, T (k + j) k =
      (-1 : ℤ) ^ (k - 1) * 2 * ∑ m ∈ Finset.range k, (-1 : ℤ) ^ m * (Nat.choose (2 * k - 1) m : ℤ) *
        (Nat.choose (4 * k - 1 - 2 * m) (2 * k) : ℤ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_bij (fun j _ => k - 1 - j) ?_ ?_ ?_ ?_
    · intro j hj; simp only [Finset.mem_range] at hj ⊢; omega
    · intro j1 hj1 j2 hj2 h; simp only [Finset.mem_range] at hj1 hj2; omega
    · intro m hm; simp only [Finset.mem_range] at hm
      exact ⟨k - 1 - m, Finset.mem_range.mpr (by omega), by omega⟩
    · intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      unfold T; rw [if_neg (by omega)]
      have hc : Nat.choose (2 * k - 1) (k + j) = Nat.choose (2 * k - 1) (k - 1 - j) := by
        rw [← Nat.choose_symm (by omega : k + j ≤ 2 * k - 1)]
        congr 1; omega
      have h2 : 2 * (k + j) + 1 = 4 * k - 1 - 2 * (k - 1 - j) := by omega
      have hsgn : (-1 : ℤ) ^ (k + j + k) = (-1 : ℤ) ^ (k - 1) * (-1 : ℤ) ^ (k - 1 - j) := by
        rw [← pow_add]
        have heven : Even ((k + j + k) + (k - 1 + (k - 1 - j))) := by
          refine ⟨2 * k - 1, by omega⟩
        have h1 : (-1 : ℤ) ^ (k + j + k) * (-1 : ℤ) ^ (k - 1 + (k - 1 - j)) = 1 := by
          rw [← pow_add]; exact Even.neg_one_pow heven
        have h2' : (-1 : ℤ) ^ (k - 1 + (k - 1 - j)) * (-1 : ℤ) ^ (k - 1 + (k - 1 - j)) = 1 := by
          rw [← pow_add]; exact Even.neg_one_pow ⟨_, rfl⟩
        calc (-1 : ℤ) ^ (k + j + k)
            = (-1 : ℤ) ^ (k + j + k) * ((-1 : ℤ) ^ (k - 1 + (k - 1 - j)) * (-1 : ℤ) ^ (k - 1 + (k - 1 - j))) := by
              rw [h2', mul_one]
          _ = ((-1 : ℤ) ^ (k + j + k) * (-1 : ℤ) ^ (k - 1 + (k - 1 - j))) * (-1 : ℤ) ^ (k - 1 + (k - 1 - j)) := by ring
          _ = (-1 : ℤ) ^ (k - 1 + (k - 1 - j)) := by rw [h1, one_mul]
      rw [hc, h2, hsgn]; ring
  rw [hsum_eq, hval]
  have hpow : (2 : ℤ) ^ (2 * k - 1) = 2 * (2 : ℤ) ^ (2 * k - 2) := by
    have : 2 * k - 1 = (2 * k - 2) + 1 := by omega
    conv_lhs => rw [this]
    rw [pow_succ']
  rw [hpow]; ring

-- Part 2: Path-graph count for a229580 (k + 1)
private def pathRGS (L : ℕ) (w : Fin L → Fin 3) : Prop :=
  ∀ (t : Fin L) (c : Fin 3), c < w t → ∃ s : Fin L, s.1 < t.1 ∧ w s = c

private def pathMistakes {L : ℕ} (w : Fin L → Fin 3) : ℕ :=
  (Finset.univ.filter (fun t : Fin (L - 1) => w ⟨t.1, by omega⟩ = w ⟨t.1 + 1, by omega⟩)).card

private lemma a229580_eq_path (n : ℕ) (hn : 1 ≤ n) :
    a229580 n = (Finset.univ.filter (fun w : Fin (2 * n) → Fin 3 => pathRGS (2 * n) w ∧ pathMistakes w = 1)).card := by
  unfold a229580
  refine Finset.card_bij (fun f _ t => f ⟨t.1 / 2, by omega⟩ ⟨t.1 % 2, by omega⟩) ?_ ?_ ?_
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    constructor
    · intro t c hc
      rcases hf.1 ⟨t.1 / 2, by omega⟩ ⟨t.1 % 2, by omega⟩ c hc with ⟨i', j', hlt, heq⟩
      dsimp only at hlt
      refine ⟨⟨2 * i'.1 + j'.1, by omega⟩, by dsimp only; omega, ?_⟩
      simp only [show (2 * i'.1 + j'.1) / 2 = i'.1 by omega, show (2 * i'.1 + j'.1) % 2 = j'.1 by omega]
      exact heq
    · rw [← hf.2]; unfold pathMistakes mistakes
      let S := Finset.univ.filter (fun t : Fin (2 * n - 1) =>
        f ⟨t.1 / 2, by omega⟩ ⟨t.1 % 2, by omega⟩ = f ⟨(t.1 + 1) / 2, by omega⟩ ⟨(t.1 + 1) % 2, by omega⟩)
      let Se := S.filter (fun t => t.1 % 2 = 0)
      let So := S.filter (fun t => t.1 % 2 ≠ 0)
      have hpart := Finset.card_filter_add_card_filter_not (s := S) (p := fun t => t.1 % 2 = 0)
      have he : Se.card = (Finset.univ.filter (fun i : Fin n => f i 0 = f i 1)).card := by
        refine Finset.card_bij (fun t _ => ⟨t.1 / 2, by omega⟩) ?_ ?_ ?_
        · intro t ht
          simp only [Se, S, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
          have h1 : (t.1 + 1) / 2 = t.1 / 2 := by omega
          have h2 : (t.1 + 1) % 2 = 1 := by omega
          have h3 : (⟨t.1 % 2, by omega⟩ : Fin 2) = 0 := Fin.ext ht.2
          have h4 : (⟨(t.1 + 1) % 2, by omega⟩ : Fin 2) = 1 := Fin.ext h2
          simpa only [h1, h3, h4] using ht.1
        · intro t1 h1 t2 h2 h
          simp only [Se, S, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
          have hv := congr_arg Fin.val h; dsimp only at hv; exact Fin.ext (by omega)
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          refine ⟨⟨2 * i.1, by omega⟩, ?_, Fin.ext (by dsimp only; omega)⟩
          simp only [Se, S, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨?_, by omega⟩
          simp only [show 2 * i.1 / 2 = i.1 by omega, show 2 * i.1 % 2 = 0 by omega,
            show (2 * i.1 + 1) / 2 = i.1 by omega, show (2 * i.1 + 1) % 2 = 1 by omega]
          exact hi
      have ho : So.card = (Finset.univ.filter (fun i : Fin (n - 1) =>
          f ⟨i.1, by omega⟩ 1 = f ⟨i.1 + 1, by omega⟩ 0)).card := by
        refine Finset.card_bij (fun t ht => ⟨t.1 / 2, by
            simp only [So, S, Finset.mem_filter, Finset.mem_univ, true_and] at ht; have := t.2; omega⟩) ?_ ?_ ?_
        · intro t ht
          simp only [So, S, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
          have h1 : (t.1 + 1) / 2 = t.1 / 2 + 1 := by omega
          have h2 : (t.1 + 1) % 2 = 0 := by omega
          have h3 : (⟨t.1 % 2, by omega⟩ : Fin 2) = 1 := Fin.ext (by dsimp only; omega)
          have h4 : (⟨(t.1 + 1) % 2, by omega⟩ : Fin 2) = 0 := Fin.ext h2
          simpa only [h1, h3, h4] using ht.1
        · intro t1 h1 t2 h2 h
          simp only [So, S, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
          have hv := congr_arg Fin.val h; dsimp only at hv; exact Fin.ext (by omega)
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          refine ⟨⟨2 * i.1 + 1, by omega⟩, ?_, Fin.ext (by dsimp only; omega)⟩
          simp only [So, S, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨?_, by omega⟩
          simp only [show (2 * i.1 + 1) / 2 = i.1 by omega, show (2 * i.1 + 1) % 2 = 1 by omega,
            show (2 * i.1 + 1 + 1) / 2 = i.1 + 1 by omega, show (2 * i.1 + 1 + 1) % 2 = 0 by omega]
          exact hi
      have htot : S.card = Se.card + So.card := hpart.symm
      rw [← he, ← ho]; exact htot
  · intro f1 _ f2 _ h
    funext i j
    have ht := congr_fun h ⟨2 * i.1 + j.1, by omega⟩
    dsimp only at ht
    simp only [show (2 * i.1 + j.1) / 2 = i.1 by omega, show (2 * i.1 + j.1) % 2 = j.1 by omega] at ht
    exact ht
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    let f : Fin n → Fin 2 → Fin 3 := fun i j => w ⟨2 * i.1 + j.1, by omega⟩
    have hf_flat : ∀ t : Fin (2 * n), f ⟨t.1 / 2, by omega⟩ ⟨t.1 % 2, by omega⟩ = w t := fun t => by
      dsimp only [f]; congr 1; exact Fin.ext (by dsimp only; omega)
    refine ⟨f, ?_, funext hf_flat⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro i j c hc
      rcases hw.1 ⟨2 * i.1 + j.1, by omega⟩ c hc with ⟨s, hlt, heq⟩
      dsimp only at hlt
      refine ⟨⟨s.1 / 2, by omega⟩, ⟨s.1 % 2, by omega⟩, by dsimp only; omega, ?_⟩
      rw [hf_flat s]; exact heq
    · rw [← hw.2]; unfold pathMistakes mistakes
      let S := Finset.univ.filter (fun t : Fin (2 * n - 1) => w ⟨t.1, by omega⟩ = w ⟨t.1 + 1, by omega⟩)
      let Se := S.filter (fun t => t.1 % 2 = 0)
      let So := S.filter (fun t => t.1 % 2 ≠ 0)
      have hpart := Finset.card_filter_add_card_filter_not (s := S) (p := fun t => t.1 % 2 = 0)
      have he : Se.card = (Finset.univ.filter (fun i : Fin n => f i 0 = f i 1)).card := by
        refine Finset.card_bij (fun t _ => ⟨t.1 / 2, by omega⟩) ?_ ?_ ?_
        · intro t ht
          simp only [Se, S, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
          dsimp only [f]
          have e1 : (⟨2 * (t.1 / 2) + (0 : Fin 2).1, by omega⟩ : Fin (2 * n)) = ⟨t.1, by omega⟩ := Fin.ext (by dsimp only; omega)
          have e2 : (⟨2 * (t.1 / 2) + (1 : Fin 2).1, by omega⟩ : Fin (2 * n)) = ⟨t.1 + 1, by omega⟩ := Fin.ext (by dsimp only; omega)
          rw [e1, e2]; exact ht.1
        · intro t1 h1 t2 h2 h
          simp only [Se, S, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
          have hv := congr_arg Fin.val h; dsimp only at hv; exact Fin.ext (by omega)
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          refine ⟨⟨2 * i.1, by omega⟩, ?_, Fin.ext (by dsimp only; omega)⟩
          simp only [Se, S, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hi, by omega⟩
      have ho : So.card = (Finset.univ.filter (fun i : Fin (n - 1) =>
          f ⟨i.1, by omega⟩ 1 = f ⟨i.1 + 1, by omega⟩ 0)).card := by
        refine Finset.card_bij (fun t ht => ⟨t.1 / 2, by
            simp only [So, S, Finset.mem_filter, Finset.mem_univ, true_and] at ht; have := t.2; omega⟩) ?_ ?_ ?_
        · intro t ht
          simp only [So, S, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
          dsimp only [f]
          have e1 : (⟨2 * (t.1 / 2) + (1 : Fin 2).1, by omega⟩ : Fin (2 * n)) = ⟨t.1, by omega⟩ := Fin.ext (by dsimp only; omega)
          have e2 : (⟨2 * (t.1 / 2 + 1) + (0 : Fin 2).1, by omega⟩ : Fin (2 * n)) = ⟨t.1 + 1, by omega⟩ := Fin.ext (by dsimp only; omega)
          rw [e1, e2]; exact ht.1
        · intro t1 h1 t2 h2 h
          simp only [So, S, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
          have hv := congr_arg Fin.val h; dsimp only at hv; exact Fin.ext (by omega)
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          refine ⟨⟨2 * i.1 + 1, by omega⟩, ?_, Fin.ext (by dsimp only; omega)⟩
          simp only [So, S, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨?_, by omega⟩
          dsimp only [f] at hi
          have e1 : (⟨2 * (i.1 + 1) + (0 : Fin 2).1, by omega⟩ : Fin (2 * n)) = ⟨2 * i.1 + 1 + 1, by omega⟩ := Fin.ext (by dsimp only; omega)
          rwa [e1] at hi
      have htot : S.card = Se.card + So.card := hpart.symm
      rw [← he, ← ho]; exact htot.symm

-- Count proper 3-colorings of P_m (m >= 2) with u 0 = 0 and u 1 = 1: equals 2^(m - 2)
private def properStart (m : ℕ) (hm : 2 ≤ m) : Finset (Fin m → Fin 3) :=
  Finset.univ.filter (fun u =>
    u ⟨0, by omega⟩ = 0 ∧ u ⟨1, by omega⟩ = 1 ∧
    ∀ t : Fin (m - 1), u ⟨t.1, by omega⟩ ≠ u ⟨t.1 + 1, by omega⟩)

private lemma card_properStart : ∀ (r : ℕ), (properStart (r + 2) (by omega)).card = 2 ^ r := by
  intro r
  induction r with
  | zero =>
    have heq : properStart 2 (by omega) = {fun i => if i.1 = 0 then 0 else 1} := by
      ext u; simp only [properStart, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨h0, h1, _⟩; funext i; match i with
        | 0 => exact h0
        | 1 => exact h1
      · rintro rfl; refine ⟨rfl, rfl, fun t => ?_⟩
        have : t.1 = 0 := by omega
        simp [this]
    rw [heq]; simp
  | succ r ih =>
    have hsig : ((properStart (r + 2) (by omega)).sigma (fun u =>
        (Finset.univ : Finset (Fin 3)).erase (u ⟨r + 1, by omega⟩))).card =
        (properStart (r + 2) (by omega)).card * 2 := by
      rw [Finset.card_sigma,
        Finset.sum_congr rfl (fun u _ => (by simp : ((Finset.univ : Finset (Fin 3)).erase (u ⟨r + 1, by omega⟩)).card = 2)),
        Finset.sum_const, smul_eq_mul]
    rw [pow_succ, ← ih, ← hsig]
    refine Finset.card_bij
      (fun u _ => ⟨fun i : Fin (r + 2) => u ⟨i.1, by omega⟩, u ⟨r + 2, by omega⟩⟩) ?_ ?_ ?_
    · intro u hu
      simp only [properStart, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      refine Finset.mem_sigma.mpr ⟨?_, ?_⟩
      · simp only [properStart, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hu.1, hu.2.1, fun t => hu.2.2 ⟨t.1, by omega⟩⟩
      · exact Finset.mem_erase.mpr ⟨(hu.2.2 ⟨r + 1, by omega⟩).symm, Finset.mem_univ _⟩
    · intro u1 _ u2 _ h
      simp only [Sigma.mk.injEq, heq_eq_eq] at h
      funext i
      by_cases hi : i.1 < r + 2
      · exact congr_fun h.1 ⟨i.1, hi⟩
      · have heq : i = ⟨r + 2, by omega⟩ := Fin.ext (by dsimp only; have := i.2; omega)
        rw [heq]; exact h.2
    · intro ⟨u, c⟩ huc
      simp only [Finset.mem_sigma, properStart, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true] at huc
      refine ⟨fun i => if hi : i.1 < r + 2 then u ⟨i.1, hi⟩ else c, ?_, ?_⟩
      · simp only [properStart, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨by simpa using huc.1.1, by simpa using huc.1.2.1, fun t => ?_⟩
        by_cases ht : t.1 < r + 1
        · simp only [show t.1 < r + 2 by omega, show t.1 + 1 < r + 2 by omega, ↓reduceDIte]
          exact huc.1.2.2 ⟨t.1, ht⟩
        · have heq : t.1 = r + 1 := by have := t.2; omega
          simp only [show t.1 < r + 2 by omega, show ¬ (t.1 + 1 < r + 2) by omega, ↓reduceDIte]
          have hfin : (⟨t.1, by omega⟩ : Fin (r + 2)) = ⟨r + 1, by omega⟩ := Fin.ext heq
          rw [hfin]; exact huc.2.symm
      · exact Sigma.ext (by funext i; simp [i.2]) (heq_of_eq (by simp))

-- Bijection between 1-mistake RGS words of length 2k+2 (k >= 1) and Fin (2k+1) × properStart (2k+1)
private lemma card_path_one_mistake (k : ℕ) (hk : 1 ≤ k) :
    (Finset.univ.filter (fun w : Fin (2 * (k + 1)) → Fin 3 =>
      pathRGS (2 * (k + 1)) w ∧ pathMistakes w = 1)).card = (2 * k + 1) * 2 ^ (2 * k - 1) := by
  have hprod : (2 * k + 1) * 2 ^ (2 * k - 1) =
      ((Finset.univ : Finset (Fin (2 * k + 1))) ×ˢ properStart (2 * k + 1) (by omega)).card := by
    have hps := card_properStart (2 * k - 1)
    have hcong : ∀ m1 m2 (h1 : 2 ≤ m1) (h2 : 2 ≤ m2), m1 = m2 →
        (properStart m1 h1).card = (properStart m2 h2).card := by
      rintro m _ h1 h2 rfl; rfl
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    congr 1
    rw [← hps]
    exact hcong (2 * k - 1 + 2) (2 * k + 1) (by omega) (by omega) (by omega)
  rw [hprod]
  -- Map (t, u) ↦ w by duplicating position t of u
  symm
  refine Finset.card_bij
    (fun (tu : Fin (2 * k + 1) × (Fin (2 * k + 1) → Fin 3)) _ =>
      fun i : Fin (2 * (k + 1)) => if hi : i.1 ≤ tu.1.1 then tu.2 ⟨i.1, by omega⟩ else tu.2 ⟨i.1 - 1, by omega⟩)
    ?_ ?_ ?_
  · intro ⟨t, u⟩ htu
    simp only [Finset.mem_product, Finset.mem_univ, true_and, properStart, Finset.mem_filter] at htu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    let w : Fin (2 * (k + 1)) → Fin 3 :=
      fun i => if hi : i.1 ≤ t.1 then u ⟨i.1, by omega⟩ else u ⟨i.1 - 1, by omega⟩
    change pathRGS (2 * (k + 1)) w ∧ pathMistakes w = 1
    constructor
    · -- RGS: w 0 = 0, and 1 appears at index 1 (if t >= 1) or index 2 (if t = 0) before any 2!
      intro i c hc
      have h0 : w ⟨0, by omega⟩ = 0 := by simp only [w, Nat.zero_le, ↓reduceDIte]; exact htu.1
      by_cases hc0 : c = 0
      · subst hc0
        have hi0 : 0 < i.1 := by
          by_contra h; have heq : i = ⟨0, by omega⟩ := Fin.ext (by dsimp only; omega)
          rw [heq, h0] at hc; exact absurd hc (by decide)
        exact ⟨⟨0, by omega⟩, by dsimp only; exact hi0, h0⟩
      · have hc1 : c = 1 := by
          have := c.2; have := (w i).2; have hlt : c.1 < (w i).1 := hc; exact Fin.ext (by omega)
        subst hc1
        have hwi2 : w i = 2 := by
          have := (w i).2; have hlt : (1 : Fin 3).1 < (w i).1 := hc; exact Fin.ext (by omega)
        by_cases ht0 : t.1 = 0
        · -- w 0 = 0, w 1 = 0, w 2 = 1
          have h1 : w ⟨1, by omega⟩ = 0 := by simp only [w, show ¬ (1 ≤ t.1) by omega, ↓reduceDIte]; exact htu.1
          have h2 : w ⟨2, by omega⟩ = 1 := by simp only [w, show ¬ (2 ≤ t.1) by omega, ↓reduceDIte]; exact htu.2.1
          have hi2 : 2 < i.1 := by
            by_contra h
            have : i.1 = 0 ∨ i.1 = 1 ∨ i.1 = 2 := by omega
            rcases this with h' | h' | h'
            · have e : i = ⟨0, by omega⟩ := Fin.ext h'; rw [e, h0] at hwi2; cases hwi2
            · have e : i = ⟨1, by omega⟩ := Fin.ext h'; rw [e, h1] at hwi2; cases hwi2
            · have e : i = ⟨2, by omega⟩ := Fin.ext h'; rw [e, h2] at hwi2; cases hwi2
          exact ⟨⟨2, by omega⟩, hi2, h2⟩
        · -- t >= 1: w 0 = 0, w 1 = 1
          have h1 : w ⟨1, by omega⟩ = 1 := by simp only [w, show 1 ≤ t.1 by omega, ↓reduceDIte]; exact htu.2.1
          have hi1 : 1 < i.1 := by
            by_contra h
            have : i.1 = 0 ∨ i.1 = 1 := by omega
            rcases this with h' | h'
            · have e : i = ⟨0, by omega⟩ := Fin.ext h'; rw [e, h0] at hwi2; cases hwi2
            · have e : i = ⟨1, by omega⟩ := Fin.ext h'; rw [e, h1] at hwi2; cases hwi2
          exact ⟨⟨1, by omega⟩, hi1, h1⟩
    · -- pathMistakes w = 1: the unique mistake is at s = t
      unfold pathMistakes
      have heq : Finset.univ.filter (fun s : Fin (2 * (k + 1) - 1) => w ⟨s.1, by omega⟩ = w ⟨s.1 + 1, by omega⟩) =
          {⟨t.1, by omega⟩} := by
        ext s; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hs
          by_contra hne
          have hne' : s.1 ≠ t.1 := fun e => hne (Fin.ext e)
          rcases lt_or_gt_of_ne hne' with hlt | hgt
          · simp only [w, show s.1 ≤ t.1 by omega, show s.1 + 1 ≤ t.1 by omega, ↓reduceDIte] at hs
            exact htu.2.2 ⟨s.1, by omega⟩ hs
          · simp only [w, show ¬ (s.1 ≤ t.1) by omega, show ¬ (s.1 + 1 ≤ t.1) by omega, ↓reduceDIte] at hs
            have h1 : s.1 + 1 - 1 = s.1 - 1 + 1 := by omega
            have hs' : u ⟨s.1 - 1, by omega⟩ = u ⟨s.1 - 1 + 1, by omega⟩ := by
              convert hs using 2; exact Fin.ext (by dsimp only; omega)
            exact htu.2.2 ⟨s.1 - 1, by omega⟩ hs'
        · intro hs; rw [hs]
          simp only [w, le_refl, show ¬ (t.1 + 1 ≤ t.1) by omega, ↓reduceDIte, Nat.add_sub_cancel]
      rw [heq]; simp
  · -- Injective
    intro ⟨t1, u1⟩ h1 ⟨t2, u2⟩ h2 heq
    simp only [Finset.mem_product, Finset.mem_univ, true_and, properStart, Finset.mem_filter] at h1 h2
    have ht : t1 = t2 := by
      by_contra hne
      have hw1 : (if h : t1.1 ≤ t1.1 then u1 ⟨t1.1, by omega⟩ else u1 ⟨t1.1 - 1, by omega⟩) =
          (if h : t1.1 + 1 ≤ t1.1 then u1 ⟨t1.1 + 1, by omega⟩ else u1 ⟨t1.1 + 1 - 1, by omega⟩) := by
        simp
      have e1 := congr_fun heq ⟨t1.1, by omega⟩
      have e2 := congr_fun heq ⟨t1.1 + 1, by omega⟩
      dsimp only at e1 e2
      have hw2 : (if h : t1.1 ≤ t2.1 then u2 ⟨t1.1, by omega⟩ else u2 ⟨t1.1 - 1, by omega⟩) =
          (if h : t1.1 + 1 ≤ t2.1 then u2 ⟨t1.1 + 1, by omega⟩ else u2 ⟨t1.1 + 1 - 1, by omega⟩) := by
        rw [← e1, ← e2]; exact hw1
      have hne' : t1.1 ≠ t2.1 := fun e => hne (Fin.ext e)
      rcases lt_or_gt_of_ne hne' with hlt | hgt
      · simp only [show t1.1 ≤ t2.1 by omega, show t1.1 + 1 ≤ t2.1 by omega, ↓reduceDIte] at hw2
        exact h2.2.2 ⟨t1.1, by omega⟩ hw2
      · simp only [show ¬ (t1.1 ≤ t2.1) by omega, show ¬ (t1.1 + 1 ≤ t2.1) by omega, ↓reduceDIte] at hw2
        have hw2' : u2 ⟨t1.1 - 1, by omega⟩ = u2 ⟨t1.1 - 1 + 1, by omega⟩ := by
          convert hw2 using 2; exact Fin.ext (by dsimp only; omega)
        exact h2.2.2 ⟨t1.1 - 1, by omega⟩ hw2'
    subst ht
    refine Prod.ext rfl (funext fun i => ?_)
    have hi := congr_fun heq ⟨i.1, by omega⟩
    dsimp only at hi
    by_cases hle : i.1 ≤ t1.1
    · simpa only [hle, ↓reduceDIte] using hi
    · have hi' := congr_fun heq ⟨i.1 + 1, by omega⟩
      dsimp only at hi'
      simp only [show ¬ (i.1 + 1 ≤ t1.1) by omega, ↓reduceDIte, Nat.add_sub_cancel] at hi'
      exact hi'
  · -- Surjective: find the unique mistake t and contract
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    rcases Finset.card_eq_one.mp hw.2 with ⟨t, ht_eq⟩
    have ht_mem : t ∈ Finset.univ.filter (fun s : Fin (2 * (k + 1) - 1) => w ⟨s.1, by omega⟩ = w ⟨s.1 + 1, by omega⟩) := by
      rw [ht_eq]; exact Finset.mem_singleton_self t
    have ht_w : w ⟨t.1, by omega⟩ = w ⟨t.1 + 1, by omega⟩ := (Finset.mem_filter.mp ht_mem).2
    have hother : ∀ s : Fin (2 * (k + 1) - 1), s ≠ t → w ⟨s.1, by omega⟩ ≠ w ⟨s.1 + 1, by omega⟩ := by
      intro s hs hEq
      have hmem : s ∈ Finset.univ.filter (fun s : Fin (2 * (k + 1) - 1) => w ⟨s.1, by omega⟩ = w ⟨s.1 + 1, by omega⟩) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hEq⟩
      rw [ht_eq, Finset.mem_singleton] at hmem
      exact hs hmem
    let t' : Fin (2 * k + 1) := ⟨t.1, by have := t.2; omega⟩
    let u : Fin (2 * k + 1) → Fin 3 := fun i =>
      if hi : i.1 ≤ t.1 then w ⟨i.1, by omega⟩ else w ⟨i.1 + 1, by omega⟩
    have hw0 : w ⟨0, by omega⟩ = 0 := by
      by_contra h
      have hpos : (0 : Fin 3) < w ⟨0, by omega⟩ := Fin.pos_of_ne_zero h
      rcases hw.1 ⟨0, by omega⟩ 0 hpos with ⟨s, hs, _⟩
      dsimp only at hs; omega
    have hu0 : u ⟨0, by omega⟩ = 0 := by simp only [u, Nat.zero_le, ↓reduceDIte]; exact hw0
    have hu_adj : ∀ s : Fin (2 * k + 1 - 1), u ⟨s.1, by omega⟩ ≠ u ⟨s.1 + 1, by omega⟩ := by
      intro s
      by_cases hs : s.1 < t.1
      · simp only [u, show s.1 ≤ t.1 by omega, show s.1 + 1 ≤ t.1 by omega, ↓reduceDIte]
        exact hother ⟨s.1, by omega⟩ (fun e => by have := congr_arg Fin.val e; dsimp only at this; omega)
      · by_cases hse : s.1 = t.1
        · simp only [u, show s.1 ≤ t.1 by omega, show ¬ (s.1 + 1 ≤ t.1) by omega, ↓reduceDIte]
          have e1 : (⟨s.1, by omega⟩ : Fin (2 * (k + 1))) = ⟨t.1, by omega⟩ := Fin.ext hse
          rw [e1, ht_w]
          have hne := hother ⟨t.1 + 1, by omega⟩ (fun e => by have := congr_arg Fin.val e; dsimp only at this; omega)
          convert hne using 2; exact Fin.ext (by dsimp only; omega)
        · simp only [u, show ¬ (s.1 ≤ t.1) by omega, show ¬ (s.1 + 1 ≤ t.1) by omega, ↓reduceDIte]
          exact hother ⟨s.1 + 1, by omega⟩ (fun e => by have := congr_arg Fin.val e; dsimp only at this; omega)
    have hu1 : u ⟨1, by omega⟩ = 1 := by
      have hne0 : u ⟨1, by omega⟩ ≠ 0 := by rw [← hu0]; exact (hu_adj ⟨0, by omega⟩).symm
      by_cases ht0 : t.1 = 0
      · -- u 1 = w 2, and w 0 = w 1 = 0, so w 2 < 2 by RGS!
        have hw1 : w ⟨1, by omega⟩ = 0 := by
          have : w ⟨0, by omega⟩ = w ⟨1, by omega⟩ := by
            convert ht_w using 2 <;> exact Fin.ext (by dsimp only; omega)
          rw [← this, hw0]
        have hu1_eq : u ⟨1, by omega⟩ = w ⟨2, by omega⟩ := by
          simp only [u, show ¬ (1 ≤ t.1) by omega, ↓reduceDIte]
        rw [hu1_eq] at hne0 ⊢
        by_contra hne1
        have hw2 : w ⟨2, by omega⟩ = 2 := by
          have := (w ⟨2, by omega⟩).2
          have h0' : (w ⟨2, by omega⟩).1 ≠ 0 := fun e => hne0 (Fin.ext e)
          have h1' : (w ⟨2, by omega⟩).1 ≠ 1 := fun e => hne1 (Fin.ext e)
          exact Fin.ext (by omega)
        rcases hw.1 ⟨2, by omega⟩ 1 (by rw [hw2]; decide) with ⟨s, hs, hws⟩
        dsimp only at hs
        have : s.1 = 0 ∨ s.1 = 1 := by omega
        rcases this with h0' | h1'
        · have : s = ⟨0, by omega⟩ := Fin.ext h0'; rw [this, hw0] at hws; cases hws
        · have : s = ⟨1, by omega⟩ := Fin.ext h1'; rw [this, hw1] at hws; cases hws
      · -- t >= 1: u 1 = w 1, and w 0 = 0, so w 1 = 1 by RGS!
        have hu1_eq : u ⟨1, by omega⟩ = w ⟨1, by omega⟩ := by
          simp only [u, show 1 ≤ t.1 by omega, ↓reduceDIte]
        rw [hu1_eq] at hne0 ⊢
        by_contra hne1
        have hw1 : w ⟨1, by omega⟩ = 2 := by
          have := (w ⟨1, by omega⟩).2
          have h0' : (w ⟨1, by omega⟩).1 ≠ 0 := fun e => hne0 (Fin.ext e)
          have h1' : (w ⟨1, by omega⟩).1 ≠ 1 := fun e => hne1 (Fin.ext e)
          exact Fin.ext (by omega)
        rcases hw.1 ⟨1, by omega⟩ 1 (by rw [hw1]; decide) with ⟨s, hs, hws⟩
        dsimp only at hs
        have : s = ⟨0, by omega⟩ := Fin.ext (by dsimp only; omega)
        rw [this, hw0] at hws; cases hws
    refine ⟨(t', u), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_univ, true_and, properStart, Finset.mem_filter]
      exact ⟨hu0, hu1, hu_adj⟩
    · funext i
      dsimp only [t', u]
      by_cases hi : i.1 ≤ t.1
      · simp only [hi, ↓reduceDIte]
      · by_cases hi1 : i.1 = t.1 + 1
        · simp only [hi, show i.1 - 1 ≤ t.1 by omega, ↓reduceDIte]
          have e1 : (⟨i.1 - 1, by omega⟩ : Fin (2 * (k + 1))) = ⟨t.1, by omega⟩ := Fin.ext (by dsimp only; omega)
          have e2 : i = ⟨t.1 + 1, by omega⟩ := Fin.ext hi1
          rw [e1, ht_w, ← e2]
        · simp only [hi, show ¬ (i.1 - 1 ≤ t.1) by omega, ↓reduceDIte]
          congr 1; exact Fin.ext (by dsimp only; omega)

theorem main : ∀ k : ℕ,
    |∑ j ∈ Finset.range (k + 1), T (k + j) k| = (a229580 (k + 1) : ℤ) := by
  intro k
  cases k with
  | zero =>
    have h1 : a229580 1 = 1 := by
      rw [a229580_eq_path 1 (by omega)]
      have heq : Finset.univ.filter (fun w : Fin 2 → Fin 3 => pathRGS 2 w ∧ pathMistakes w = 1) =
          {fun _ => 0} := by
        ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨hrgs, hmis⟩
          have hw0 : w 0 = 0 := by
            by_contra h
            rcases hrgs 0 0 (Fin.pos_of_ne_zero h) with ⟨s, hs, _⟩
            omega
          have h01 : w 0 = w 1 := by
            unfold pathMistakes at hmis
            rcases Finset.card_eq_one.mp hmis with ⟨t, ht⟩
            have hmem : t ∈ Finset.univ.filter (fun s : Fin (2 - 1) => w ⟨s.1, by omega⟩ = w ⟨s.1 + 1, by omega⟩) := by
              rw [ht]; exact Finset.mem_singleton_self t
            have hw := (Finset.mem_filter.mp hmem).2
            have ht0 : t.1 = 0 := by omega
            simpa [ht0] using hw
          funext i; match i with
          | 0 => exact hw0
          | 1 => rw [← h01, hw0]
        · rintro rfl
          refine ⟨fun t c hc => by simp at hc, ?_⟩
          unfold pathMistakes
          have : Finset.univ.filter (fun s : Fin (2 - 1) => (0 : Fin 3) = (0 : Fin 3)) = Finset.univ := by simp
          rw [this]; simp
      rw [heq]; simp
    simp [T, h1]
  | succ k' =>
    have hk : 1 ≤ k' + 1 := by omega
    rw [lhs_sum_eq (k' + 1) hk, a229580_eq_path (k' + 1 + 1) (by omega), card_path_one_mistake (k' + 1) hk]
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    push_cast; rfl

end
end ProofA368846

theorem OMA.solution : type_of% @OMA.S_oeis_a368846.main :=
  ProofA368846.main

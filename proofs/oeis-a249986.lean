import OMAStatements.S_oeis_a249986

/-!
# Proof of A249986

We prove that for all `n ≥ 1`, the number `a n` of arrays `x : Fin 7 → Fin (2 * n + 1)`
whose adjacent differences have absolute sum `6 * n` satisfies the exact degree-6 polynomial
formula
`a n = n * (1987 * n ^ 5 + 12198 * n ^ 4 + 27850 * n ^ 3 + 40680 * n ^ 2 - 3017 * n + 4182) / 180`.

The proof splits each 7-tuple at its middle entry `m = x 3` into two reversed 3-step walks
of total variations `v` and `6 * n - v`, giving
`a n = ∑ m ∈ range (2 * n + 1), ∑ v ∈ range (6 * n + 1), H n m v * H n m (6 * n - v)`.
We derive closed-form piecewise linear formulas for the 2-step walk count `K n x u` and
piecewise quadratic formulas for the 3-step walk count `H n m v` (both depending on parity
only through `(m + v) % 2`), evaluate the inner sum over `v` and outer sum over `m` via
telescoping sums over `ℚ`, and deduce both the generating function identity and the
order-7 linear recurrence.
-/

namespace OMA.S_oeis_a249986

open PowerSeries

/-! ### Elementary helpers -/

private def adiff (x y : ℕ) : ℕ :=
  if x ≤ y then y - x else x - y

private lemma adiff_comm (x y : ℕ) : adiff x y = adiff y x := by
  unfold adiff; split_ifs <;> omega

private lemma adiff_reflect {n x y : ℕ} (hx : x ≤ 2 * n) (hy : y ≤ 2 * n) :
    adiff (2 * n - x) (2 * n - y) = adiff x y := by
  unfold adiff; split_ifs <;> omega

private lemma adiff_cast_int (x y : ℕ) : (adiff x y : ℤ) = |(x : ℤ) - (y : ℤ)| := by
  unfold adiff; split_ifs <;> [rw [abs_of_nonpos (by omega)]; rw [abs_of_nonneg (by omega)]] <;> omega

private lemma nat_div2_cast (k : ℕ) : ((k / 2 : ℕ) : ℚ) = ((k : ℚ) - (k % 2 : ℕ)) / 2 := by
  have h := Nat.div_add_mod k 2
  have hq : ((2 * (k / 2) + k % 2 : ℕ) : ℚ) = (k : ℚ) := by exact_mod_cast h
  push_cast at hq
  linarith

private lemma sum_Ico_telescope {a b : ℕ} (h : a ≤ b) (f F : ℕ → ℚ)
    (hstep : ∀ k, f k = F (k + 1) - F k) :
    ∑ k ∈ Finset.Ico a b, f k = F b - F a := by
  induction b, h using Nat.le_induction with
  | base => simp
  | succ b h ih =>
    rw [Finset.sum_Ico_succ_top h, ih, hstep b]
    ring

private lemma sum_Ico_lin (c0 c1 : ℚ) {a b : ℕ} (h : a ≤ b) :
    ∑ k ∈ Finset.Ico a b, (c0 + c1 * (k : ℚ)) =
      c0 * ((b : ℚ) - a) + c1 * ((b : ℚ) * (b - 1) - a * (a - 1)) / 2 := by
  have ht := sum_Ico_telescope h (fun k => c0 + c1 * (k : ℚ))
    (fun k => c0 * (k : ℚ) + c1 * (k : ℚ) * ((k : ℚ) - 1) / 2)
    (fun k => by push_cast; ring)
  rw [ht]
  ring

private lemma sum_Ico_even_odd (f : ℕ → ℚ) {lo hi : ℕ} (h : lo ≤ hi) :
    ∑ v ∈ Finset.Ico lo hi, f v =
      (∑ k ∈ Finset.Ico ((lo + 1) / 2) ((hi + 1) / 2), f (2 * k)) +
      (∑ k ∈ Finset.Ico (lo / 2) (hi / 2), f (2 * k + 1)) := by
  induction hi, h using Nat.le_induction with
  | base => simp
  | succ b h ih =>
    rw [Finset.sum_Ico_succ_top h, ih]
    rcases Nat.even_or_odd' b with ⟨k, rfl | rfl⟩
    · have h1 : (2 * k + 1) / 2 = k := by omega
      have h2 : (2 * k) / 2 = k := by omega
      have h3 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
      have h4 : (lo + 1) / 2 ≤ k := by omega
      rw [h3, h1, h2, Finset.sum_Ico_succ_top h4]
      ring
    · have h1 : (2 * k + 1 + 1 + 1) / 2 = k + 1 := by omega
      have h2 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
      have h3 : (2 * k + 1) / 2 = k := by omega
      have h4 : lo / 2 ≤ k := by omega
      rw [h1, h2, h3, Finset.sum_Ico_succ_top h4]
      ring

private lemma sum_Ico_split {α : Type*} [AddCommMonoid α] (f : ℕ → α) {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    ∑ k ∈ Finset.Ico a c, f k = (∑ k ∈ Finset.Ico a b, f k) + ∑ k ∈ Finset.Ico b c, f k := by
  rw [Finset.sum_Ico_consecutive f hab hbc]

/-! ### Walk counts and center-split bijection -/

private def G (n x d : ℕ) : ℕ :=
  ((Finset.range (2 * n + 1)).filter fun y => adiff y x = d).card

private def K (n x u : ℕ) : ℕ :=
  ∑ y ∈ Finset.range (2 * n + 1), if adiff y x ≤ u then G n y (u - adiff y x) else 0

private def H (n m v : ℕ) : ℕ :=
  ∑ x ∈ Finset.range (2 * n + 1), if adiff x m ≤ v then K n x (v - adiff x m) else 0

private def halfSet (n m v : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (2 * n + 1)) ×ˢ ((Finset.range (2 * n + 1)) ×ˢ (Finset.range (2 * n + 1)))).filter
    fun p => adiff p.1 p.2.1 + adiff p.2.1 p.2.2 + adiff p.2.2 m = v

private lemma halfSet_card (n m v : ℕ) : (halfSet n m v).card = H n m v := by
  unfold halfSet H K G
  rw [Finset.card_filter, Finset.sum_product]
  simp_rw [Finset.sum_product]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext y; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hxm : adiff x m ≤ v
  · rw [if_pos hxm]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hyx : adiff y x ≤ v - adiff x m
    · rw [if_pos hyx, Finset.card_filter]
      refine Finset.sum_congr rfl fun z _ => ?_
      have hiff : (adiff z y + adiff y x + adiff x m = v) ↔ (adiff z y = v - adiff x m - adiff y x) := by
        omega
      simp only [hiff]
    · rw [if_neg hyx]
      refine Finset.sum_eq_zero fun z _ => ?_
      rw [if_neg]
      omega
  · rw [if_neg hxm]
    refine Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun z _ => ?_
    rw [if_neg]
    omega

private lemma variation_eq_adiff {n : ℕ} (x : Fin 7 → Fin (2 * n + 1)) :
    variation x =
      ((adiff (x 0).val (x 1).val + adiff (x 1).val (x 2).val + adiff (x 2).val (x 3).val +
        adiff (x 6).val (x 5).val + adiff (x 5).val (x 4).val + adiff (x 4).val (x 3).val : ℕ) : ℤ) := by
  unfold variation
  rw [Fin.sum_univ_six]
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.castSucc_one, Fin.succ_one_eq_two]
  have h2 : (2 : Fin 6).castSucc = (2 : Fin 7) := rfl
  have h2s : (2 : Fin 6).succ = (3 : Fin 7) := rfl
  have h3 : (3 : Fin 6).castSucc = (3 : Fin 7) := rfl
  have h3s : (3 : Fin 6).succ = (4 : Fin 7) := rfl
  have h4 : (4 : Fin 6).castSucc = (4 : Fin 7) := rfl
  have h4s : (4 : Fin 6).succ = (5 : Fin 7) := rfl
  have h5 : (5 : Fin 6).castSucc = (5 : Fin 7) := rfl
  have h5s : (5 : Fin 6).succ = (6 : Fin 7) := rfl
  rw [h2, h2s, h3, h3s, h4, h4s, h5, h5s]
  push_cast
  rw [adiff_cast_int, adiff_cast_int, adiff_cast_int,
      adiff_cast_int, adiff_cast_int, adiff_cast_int]
  rw [abs_sub_comm ((x 3).val : ℤ) ((x 4).val : ℤ),
      abs_sub_comm ((x 4).val : ℤ) ((x 5).val : ℤ),
      abs_sub_comm ((x 5).val : ℤ) ((x 6).val : ℤ)]
  ring

private lemma a_eq_sum_H (n : ℕ) :
    a n = ∑ m ∈ Finset.range (2 * n + 1), ∑ v ∈ Finset.range (6 * n + 1), H n m v * H n m (6 * n - v) := by
  unfold a
  let T := (Finset.range (2 * n + 1)).sigma fun m =>
    (Finset.range (6 * n + 1)).sigma fun v =>
      (halfSet n m v) ×ˢ (halfSet n m (6 * n - v))
  have hT : T.card = ∑ m ∈ Finset.range (2 * n + 1), ∑ v ∈ Finset.range (6 * n + 1),
      H n m v * H n m (6 * n - v) := by
    simp only [T, Finset.card_sigma, Finset.card_product, halfSet_card]
  rw [← hT]
  refine Finset.card_bij
    (fun x _ => ⟨(x 3).val, ⟨adiff (x 0).val (x 1).val + adiff (x 1).val (x 2).val + adiff (x 2).val (x 3).val,
      (((x 0).val, (x 1).val, (x 2).val), ((x 6).val, (x 5).val, (x 4).val))⟩⟩)
    ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [variation_eq_adiff] at hx
    have hx' : adiff (x 0).val (x 1).val + adiff (x 1).val (x 2).val + adiff (x 2).val (x 3).val +
        adiff (x 6).val (x 5).val + adiff (x 5).val (x 4).val + adiff (x 4).val (x 3).val = 6 * n := by
      omega
    simp only [T, Finset.mem_sigma, Finset.mem_range, Finset.mem_product, halfSet, Finset.mem_filter]
    refine ⟨(x 3).isLt, by omega, ⟨⟨(x 0).isLt, (x 1).isLt, (x 2).isLt⟩, trivial⟩,
      ⟨⟨(x 6).isLt, (x 5).isLt, (x 4).isLt⟩, by omega⟩⟩
  · intro x _ y _ hxy
    simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq] at hxy
    rcases hxy with ⟨h3, _, ⟨h0, h1, h2⟩, ⟨h6, h5, h4⟩⟩
    funext i
    fin_cases i <;> exact Fin.ext (by assumption)
  · intro t ht
    rcases t with ⟨m, ⟨v, ⟨⟨x0, x1, x2⟩, ⟨x6, x5, x4⟩⟩⟩⟩
    simp only [T, Finset.mem_sigma, Finset.mem_range, Finset.mem_product, halfSet, Finset.mem_filter] at ht
    rcases ht with ⟨hm, hv, ⟨⟨hx0, hx1, hx2⟩, hl⟩, ⟨⟨hx6, hx5, hx4⟩, hr⟩⟩
    let x : Fin 7 → Fin (2 * n + 1) := ![⟨x0, hx0⟩, ⟨x1, hx1⟩, ⟨x2, hx2⟩, ⟨m, hm⟩, ⟨x4, hx4⟩, ⟨x5, hx5⟩, ⟨x6, hx6⟩]
    refine ⟨x, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [variation_eq_adiff]
      simp only [x, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      omega
    · refine Sigma.ext rfl (heq_of_eq (Sigma.ext ?_ (heq_of_eq rfl)))
      simpa only [x, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] using hl

/-! ### Reflection symmetries -/

private lemma G_reflect {n x : ℕ} (hx : x ≤ 2 * n) (d : ℕ) : G n (2 * n - x) d = G n x d := by
  unfold G
  refine Finset.card_bij (fun y _ => 2 * n - y) ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_range] at hy ⊢
    refine ⟨by omega, ?_⟩
    have h1 := adiff_reflect (n := n) (x := y) (y := 2 * n - x) (by omega) (by omega)
    rw [show 2 * n - (2 * n - x) = x by omega] at h1
    rw [h1]
    exact hy.2
  · intro y1 hy1 y2 hy2 h
    simp only [Finset.mem_filter, Finset.mem_range] at hy1 hy2
    omega
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_range] at hy
    refine ⟨2 * n - y, ?_, by omega⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [adiff_reflect (by omega : y ≤ 2 * n) hx]
    exact hy.2

private lemma K_reflect {n x : ℕ} (hx : x ≤ 2 * n) (u : ℕ) : K n (2 * n - x) u = K n x u := by
  unfold K
  refine Finset.sum_bij (fun y _ => 2 * n - y) ?_ ?_ ?_ ?_
  · intro y hy; simp only [Finset.mem_range] at hy ⊢; omega
  · intro y1 hy1 y2 hy2 h; simp only [Finset.mem_range] at hy1 hy2; omega
  · intro y hy; simp only [Finset.mem_range] at hy; exact ⟨2 * n - y, by simp only [Finset.mem_range]; omega, by omega⟩
  · intro y hy
    simp only [Finset.mem_range] at hy
    have hy' : y ≤ 2 * n := by omega
    have had : adiff y (2 * n - x) = adiff (2 * n - y) x := by
      have h1 := adiff_reflect (n := n) (x := y) (y := 2 * n - x) hy' (by omega)
      have h2 : 2 * n - (2 * n - x) = x := by omega
      rw [h2] at h1
      exact h1.symm
    rw [had, G_reflect hy']

private lemma H_reflect {n m : ℕ} (hm : m ≤ 2 * n) (v : ℕ) : H n (2 * n - m) v = H n m v := by
  unfold H
  refine Finset.sum_bij (fun x _ => 2 * n - x) ?_ ?_ ?_ ?_
  · intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
  · intro x1 hx1 x2 hx2 h; simp only [Finset.mem_range] at hx1 hx2; omega
  · intro x hx; simp only [Finset.mem_range] at hx; exact ⟨2 * n - x, by simp only [Finset.mem_range]; omega, by omega⟩
  · intro x hx
    simp only [Finset.mem_range] at hx
    have hx' : x ≤ 2 * n := by omega
    have had : adiff x (2 * n - m) = adiff (2 * n - x) m := by
      have h1 := adiff_reflect (n := n) (x := x) (y := 2 * n - m) hx' (by omega)
      have h2 : 2 * n - (2 * n - m) = m := by omega
      rw [h2] at h1
      exact h1.symm
    rw [had, K_reflect hx']

/-! ### Closed forms for G and K -/

private lemma G_eq {n x : ℕ} (hx : x ≤ 2 * n) (d : ℕ) :
    G n x d = if d = 0 then 1 else (if d ≤ x then 1 else 0) + (if x + d ≤ 2 * n then 1 else 0) := by
  unfold G
  by_cases hd : d = 0
  · subst hd
    rw [if_pos rfl]
    have hset : (Finset.range (2 * n + 1)).filter (fun y => adiff y x = 0) = {x} := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      unfold adiff; split_ifs <;> omega
    rw [hset, Finset.card_singleton]
  · rw [if_neg hd]
    have hsplit : (Finset.range (2 * n + 1)).filter (fun y => adiff y x = d) =
        ((Finset.range (2 * n + 1)).filter (fun y => y + d = x)) ∪
        ((Finset.range (2 * n + 1)).filter (fun y => y = x + d)) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union]
      unfold adiff; split_ifs <;> omega
    have hdisj : Disjoint
        ((Finset.range (2 * n + 1)).filter (fun y => y + d = x))
        ((Finset.range (2 * n + 1)).filter (fun y => y = x + d)) := by
      rw [Finset.disjoint_filter]
      intro y _ h1 h2; omega
    rw [hsplit, Finset.card_union_of_disjoint hdisj]
    have h1 : ((Finset.range (2 * n + 1)).filter (fun y => y + d = x)).card = if d ≤ x then 1 else 0 := by
      split_ifs with hdx
      · have hs : (Finset.range (2 * n + 1)).filter (fun y => y + d = x) = {x - d} := by
          ext y; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]; omega
        rw [hs, Finset.card_singleton]
      · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro y _; omega
    have h2 : ((Finset.range (2 * n + 1)).filter (fun y => y = x + d)).card = if x + d ≤ 2 * n then 1 else 0 := by
      split_ifs with hxd
      · have hs : (Finset.range (2 * n + 1)).filter (fun y => y = x + d) = {x + d} := by
          ext y; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]; omega
        rw [hs, Finset.card_singleton]
      · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro y hy; simp only [Finset.mem_range] at hy; omega
    rw [h1, h2]

private lemma K_zero {n x : ℕ} (hx : x ≤ 2 * n) : K n x 0 = 1 := by
  unfold K
  rw [Finset.sum_eq_single x]
  · have had : adiff x x = 0 := by unfold adiff; simp
    rw [had, if_pos (le_refl 0), Nat.sub_zero, G_eq hx 0, if_pos rfl]
  · intro y _ hyx
    rw [if_neg]
    unfold adiff; split_ifs <;> omega
  · intro hx'; simp only [Finset.mem_range] at hx'; omega

private lemma K_pos_eq_6terms {n x u : ℕ} (hx : x ≤ 2 * n) (hu : 1 ≤ u) :
    K n x u =
      ((if u ≤ x then 1 else 0) + (if x + u ≤ 2 * n then 1 else 0)) +
      (if u ≤ x then 1 else 0) +
      (if u ≤ x then u - 1 else 0) +
      (if u ≤ 2 * n + x then (min x ((2 * n + x - u) / 2 + 1)) - (x + 1 - u) else 0) +
      (if x + u ≤ 2 * n then 1 else 0) +
      (if x + u ≤ 2 * n then u - 1 else 0) +
      ((min (2 * n + 1) (x + u)) - (max (x + 1) ((x + u + 1) / 2))) := by
  unfold K
  rw [← Nat.Ico_zero_eq_range]
  rw [sum_Ico_split _ (Nat.zero_le x) (by omega : x ≤ 2 * n + 1)]
  rw [sum_Ico_split _ (by omega : x ≤ x + 1) (by omega : x + 1 ≤ 2 * n + 1)]
  -- Middle term y = x
  have hmid : ∑ y ∈ Finset.Ico x (x + 1), (if adiff y x ≤ u then G n y (u - adiff y x) else 0) =
      (if u ≤ x then 1 else 0) + (if x + u ≤ 2 * n then 1 else 0) := by
    rw [Finset.sum_Ico_succ_top (le_refl x), Finset.Ico_self, Finset.sum_empty, zero_add]
    have had : adiff x x = 0 := by unfold adiff; simp
    rw [had, if_pos (Nat.zero_le u), Nat.sub_zero, G_eq hx u, if_neg (by omega)]
  -- Left sum y ∈ Ico 0 x
  have hlt : ∑ y ∈ Finset.Ico 0 x, (if adiff y x ≤ u then G n y (u - adiff y x) else 0) =
      (if u ≤ x then 1 else 0) + (if u ≤ x then u - 1 else 0) +
      (if u ≤ 2 * n + x then (min x ((2 * n + x - u) / 2 + 1)) - (x + 1 - u) else 0) := by
    have hrew : ∀ y ∈ Finset.Ico 0 x,
        (if adiff y x ≤ u then G n y (u - adiff y x) else 0) =
        (if y + u = x then 1 else 0) +
        (if x < y + u ∧ u ≤ x then 1 else 0) +
        (if x < y + u ∧ 2 * y + u ≤ 2 * n + x then 1 else 0) := by
      intro y hy
      simp only [Finset.mem_Ico] at hy
      have had : adiff y x = x - y := by unfold adiff; rw [if_pos (by omega)]
      rw [had]
      by_cases hle : x - y ≤ u
      · rw [if_pos hle, G_eq (by omega : y ≤ 2 * n)]
        split_ifs <;> omega
      · rw [if_neg hle]
        split_ifs <;> omega
    rw [Finset.sum_congr rfl hrew, Finset.sum_add_distrib, Finset.sum_add_distrib]
    have s1 : ∑ y ∈ Finset.Ico 0 x, (if y + u = x then 1 else 0) = if u ≤ x then 1 else 0 := by
      rw [← Finset.card_filter]
      split_ifs with hux
      · have hs : (Finset.Ico 0 x).filter (fun y => y + u = x) = {x - u} := by
          ext y; simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]; omega
        rw [hs, Finset.card_singleton]
      · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro y hy; simp at hy; omega
    have s2 : ∑ y ∈ Finset.Ico 0 x, (if x < y + u ∧ u ≤ x then 1 else 0) = if u ≤ x then u - 1 else 0 := by
      rw [← Finset.card_filter]
      split_ifs with hux
      · have hs : (Finset.Ico 0 x).filter (fun y => x < y + u ∧ u ≤ x) = Finset.Ico (x + 1 - u) x := by
          ext y; simp only [Finset.mem_filter, Finset.mem_Ico]; omega
        rw [hs, Nat.card_Ico]; omega
      · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro y _; omega
    have s3 : ∑ y ∈ Finset.Ico 0 x, (if x < y + u ∧ 2 * y + u ≤ 2 * n + x then 1 else 0) =
        if u ≤ 2 * n + x then (min x ((2 * n + x - u) / 2 + 1)) - (x + 1 - u) else 0 := by
      rw [← Finset.card_filter]
      split_ifs with hux
      · have hs : (Finset.Ico 0 x).filter (fun y => x < y + u ∧ 2 * y + u ≤ 2 * n + x) =
            Finset.Ico (x + 1 - u) (min x ((2 * n + x - u) / 2 + 1)) := by
          ext y; simp only [Finset.mem_filter, Finset.mem_Ico]; omega
        rw [hs, Nat.card_Ico]
      · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro y _; omega
    rw [s1, s2, s3]
  -- Right sum y ∈ Ico (x + 1) (2 * n + 1)
  have hgt : ∑ y ∈ Finset.Ico (x + 1) (2 * n + 1), (if adiff y x ≤ u then G n y (u - adiff y x) else 0) =
      (if x + u ≤ 2 * n then 1 else 0) + (if x + u ≤ 2 * n then u - 1 else 0) +
      ((min (2 * n + 1) (x + u)) - (max (x + 1) ((x + u + 1) / 2))) := by
    have hrew : ∀ y ∈ Finset.Ico (x + 1) (2 * n + 1),
        (if adiff y x ≤ u then G n y (u - adiff y x) else 0) =
        (if y = x + u then 1 else 0) +
        (if y < x + u ∧ x + u ≤ 2 * n then 1 else 0) +
        (if y < x + u ∧ x + u ≤ 2 * y then 1 else 0) := by
      intro y hy
      simp only [Finset.mem_Ico] at hy
      have had : adiff y x = y - x := by unfold adiff; rw [if_neg (by omega)]
      rw [had]
      by_cases hle : y - x ≤ u
      · rw [if_pos hle, G_eq (by omega : y ≤ 2 * n)]
        split_ifs <;> omega
      · rw [if_neg hle]
        split_ifs <;> omega
    rw [Finset.sum_congr rfl hrew, Finset.sum_add_distrib, Finset.sum_add_distrib]
    have s1 : ∑ y ∈ Finset.Ico (x + 1) (2 * n + 1), (if y = x + u then 1 else 0) =
        if x + u ≤ 2 * n then 1 else 0 := by
      rw [← Finset.card_filter]
      split_ifs with hxu
      · have hs : (Finset.Ico (x + 1) (2 * n + 1)).filter (fun y => y = x + u) = {x + u} := by
          ext y; simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]; omega
        rw [hs, Finset.card_singleton]
      · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro y hy; simp at hy; omega
    have s2 : ∑ y ∈ Finset.Ico (x + 1) (2 * n + 1), (if y < x + u ∧ x + u ≤ 2 * n then 1 else 0) =
        if x + u ≤ 2 * n then u - 1 else 0 := by
      rw [← Finset.card_filter]
      split_ifs with hxu
      · have hs : (Finset.Ico (x + 1) (2 * n + 1)).filter (fun y => y < x + u ∧ x + u ≤ 2 * n) =
            Finset.Ico (x + 1) (x + u) := by
          ext y; simp only [Finset.mem_filter, Finset.mem_Ico]; omega
        rw [hs, Nat.card_Ico]; omega
      · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro y _; omega
    have s3 : ∑ y ∈ Finset.Ico (x + 1) (2 * n + 1), (if y < x + u ∧ x + u ≤ 2 * y then 1 else 0) =
        (min (2 * n + 1) (x + u)) - (max (x + 1) ((x + u + 1) / 2)) := by
      rw [← Finset.card_filter]
      have hs : (Finset.Ico (x + 1) (2 * n + 1)).filter (fun y => y < x + u ∧ x + u ≤ 2 * y) =
          Finset.Ico (max (x + 1) ((x + u + 1) / 2)) (min (2 * n + 1) (x + u)) := by
        ext y; simp only [Finset.mem_filter, Finset.mem_Ico]; omega
      rw [hs, Nat.card_Ico]
    rw [s1, s2, s3]
  rw [hlt, hmid, hgt]
  omega

private lemma K_R1 {n x u : ℕ} (hx : x ≤ 2 * n) (h1 : 1 ≤ u) (h2 : u ≤ x) (h3 : u ≤ 2 * n - x) :
    (K n x u : ℚ) = 4 * (u : ℚ) := by
  have hk := K_pos_eq_6terms hx h1
  simp only [if_pos h2, if_pos (by omega : x + u ≤ 2 * n), if_pos (by omega : u ≤ 2 * n + x),
      min_eq_left (by omega : x ≤ (2 * n + x - u) / 2 + 1),
      min_eq_right (by omega : x + u ≤ 2 * n + 1),
      max_eq_left (by omega : (x + u + 1) / 2 ≤ x + 1)] at hk
  have : K n x u = 4 * u := by omega
  exact_mod_cast this

private lemma K_R2 {n x u : ℕ} (hx : x ≤ n) (h1 : x < u) (h2 : u ≤ 2 * n - x) :
    (K n x u : ℚ) = (3 * (u : ℚ) + 3 * (x : ℚ) + 2 - ((x + u) % 2 : ℕ)) / 2 := by
  have hk := K_pos_eq_6terms (by omega : x ≤ 2 * n) (by omega : 1 ≤ u)
  simp only [if_neg (by omega : ¬ u ≤ x), if_pos (by omega : x + u ≤ 2 * n), if_pos (by omega : u ≤ 2 * n + x),
      min_eq_left (by omega : x ≤ (2 * n + x - u) / 2 + 1),
      min_eq_right (by omega : x + u ≤ 2 * n + 1),
      max_eq_right (by omega : x + 1 ≤ (x + u + 1) / 2)] at hk
  have h2k : 2 * K n x u = 3 * u + 3 * x + 2 - (x + u) % 2 := by omega
  have hq : ((2 * K n x u : ℕ) : ℚ) = ((3 * u + 3 * x + 2 - (x + u) % 2 : ℕ) : ℚ) := by
    exact_mod_cast h2k
  rw [Nat.cast_sub (by omega)] at hq
  push_cast at hq
  linarith

private lemma K_R3 {n x u : ℕ} (hx : x ≤ n) (h1 : 2 * n - x < u) (h2 : u ≤ 2 * n + x) :
    (K n x u : ℚ) = 3 * (n : ℚ) - (u : ℚ) + 2 - ((x + u) % 2 : ℕ) := by
  have hk := K_pos_eq_6terms (by omega : x ≤ 2 * n) (by omega : 1 ≤ u)
  simp only [if_neg (by omega : ¬ u ≤ x), if_neg (by omega : ¬ x + u ≤ 2 * n), if_pos h2,
      min_eq_right (by omega : (2 * n + x - u) / 2 + 1 ≤ x),
      min_eq_left (by omega : 2 * n + 1 ≤ x + u),
      max_eq_right (by omega : x + 1 ≤ (x + u + 1) / 2)] at hk
  have hnat : K n x u + u + (x + u) % 2 = 3 * n + 2 := by omega
  have hq : ((K n x u + u + (x + u) % 2 : ℕ) : ℚ) = ((3 * n + 2 : ℕ) : ℚ) := by
    exact_mod_cast hnat
  push_cast at hq
  linarith

private lemma K_R4 {n x u : ℕ} (hx : x ≤ n) (h1 : 2 * n + x < u) (h2 : u ≤ 4 * n - x) :
    (K n x u : ℚ) = (4 * (n : ℚ) - (x : ℚ) - (u : ℚ) + 2 - ((x + u) % 2 : ℕ)) / 2 := by
  have hk := K_pos_eq_6terms (by omega : x ≤ 2 * n) (by omega : 1 ≤ u)
  simp only [if_neg (by omega : ¬ u ≤ x), if_neg (by omega : ¬ x + u ≤ 2 * n), if_neg (by omega : ¬ u ≤ 2 * n + x),
      min_eq_left (by omega : 2 * n + 1 ≤ x + u),
      max_eq_right (by omega : x + 1 ≤ (x + u + 1) / 2)] at hk
  have h2k : 2 * K n x u + x + u + (x + u) % 2 = 4 * n + 2 := by omega
  have hq : ((2 * K n x u + x + u + (x + u) % 2 : ℕ) : ℚ) = ((4 * n + 2 : ℕ) : ℚ) := by
    exact_mod_cast h2k
  push_cast at hq
  linarith

private lemma K_R5 {n x u : ℕ} (hx : x ≤ n) (h1 : 4 * n - x < u) :
    (K n x u : ℚ) = 0 := by
  have hk := K_pos_eq_6terms (by omega : x ≤ 2 * n) (by omega : 1 ≤ u)
  simp only [if_neg (by omega : ¬ u ≤ x), if_neg (by omega : ¬ x + u ≤ 2 * n), if_neg (by omega : ¬ u ≤ 2 * n + x),
      min_eq_left (by omega : 2 * n + 1 ≤ x + u),
      max_eq_right (by omega : x + 1 ≤ (x + u + 1) / 2)] at hk
  have h0 : K n x u = 0 := by omega
  exact_mod_cast h0

/-! ### Closed forms for H -/

private lemma H_zero {n m : ℕ} (hm : m ≤ 2 * n) : (H n m 0 : ℚ) = 1 := by
  have hnat : H n m 0 = 1 := by
    unfold H
    rw [Finset.sum_eq_single m]
    · have had : adiff m m = 0 := by unfold adiff; simp
      rw [had, if_pos (le_refl 0), Nat.sub_zero, K_zero hm]
    · intro x _ hxm
      rw [if_neg]; unfold adiff; split_ifs <;> omega
    · intro hm'; simp only [Finset.mem_range] at hm'; omega
  exact_mod_cast hnat

private lemma H_split_4 {n m v : ℕ} (hm : m ≤ n) :
    (H n m v : ℚ) =
      (∑ x ∈ Finset.Ico 0 m, (if m - x ≤ v then (K n x (v - (m - x)) : ℚ) else 0)) +
      (K n m v : ℚ) +
      (∑ x ∈ Finset.Ico (m + 1) (n + 1), (if x - m ≤ v then (K n x (v - (x - m)) : ℚ) else 0)) +
      (∑ y ∈ Finset.Ico 0 n, (if 2 * n - m - y ≤ v then (K n y (v - (2 * n - m - y)) : ℚ) else 0)) := by
  unfold H
  rw [← Nat.Ico_zero_eq_range]
  rw [sum_Ico_split _ (Nat.zero_le m) (by omega : m ≤ 2 * n + 1)]
  rw [sum_Ico_split _ (by omega : m ≤ m + 1) (by omega : m + 1 ≤ 2 * n + 1)]
  rw [sum_Ico_split _ (by omega : m + 1 ≤ n + 1) (by omega : n + 1 ≤ 2 * n + 1)]
  push_cast
  have hA : ∑ x ∈ Finset.Ico 0 m, (if adiff x m ≤ v then (K n x (v - adiff x m) : ℚ) else 0) =
      ∑ x ∈ Finset.Ico 0 m, (if m - x ≤ v then (K n x (v - (m - x)) : ℚ) else 0) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [Finset.mem_Ico] at hx
    have had : adiff x m = m - x := by unfold adiff; rw [if_pos (by omega)]
    rw [had]
  have hB : ∑ x ∈ Finset.Ico m (m + 1), (if adiff x m ≤ v then (K n x (v - adiff x m) : ℚ) else 0) =
      (K n m v : ℚ) := by
    rw [Finset.sum_Ico_succ_top (le_refl m), Finset.Ico_self, Finset.sum_empty, zero_add]
    have had : adiff m m = 0 := by unfold adiff; simp
    rw [had, if_pos (Nat.zero_le v), Nat.sub_zero]
  have hC : ∑ x ∈ Finset.Ico (m + 1) (n + 1), (if adiff x m ≤ v then (K n x (v - adiff x m) : ℚ) else 0) =
      ∑ x ∈ Finset.Ico (m + 1) (n + 1), (if x - m ≤ v then (K n x (v - (x - m)) : ℚ) else 0) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [Finset.mem_Ico] at hx
    have had : adiff x m = x - m := by unfold adiff; rw [if_neg (by omega)]
    rw [had]
  have hD : ∑ x ∈ Finset.Ico (n + 1) (2 * n + 1), (if adiff x m ≤ v then (K n x (v - adiff x m) : ℚ) else 0) =
      ∑ y ∈ Finset.Ico 0 n, (if 2 * n - m - y ≤ v then (K n y (v - (2 * n - m - y)) : ℚ) else 0) := by
    refine Finset.sum_bij (fun x _ => 2 * n - x) ?_ ?_ ?_ ?_
    · intro x hx; simp only [Finset.mem_Ico] at hx ⊢; omega
    · intro x1 hx1 x2 hx2 h; simp only [Finset.mem_Ico] at hx1 hx2; omega
    · intro y hy; simp only [Finset.mem_Ico] at hy; exact ⟨2 * n - y, by simp only [Finset.mem_Ico]; omega, by omega⟩
    · intro x hx
      simp only [Finset.mem_Ico] at hx
      have had : adiff x m = 2 * n - m - (2 * n - x) := by unfold adiff; rw [if_neg (by omega)]; omega
      rw [had]
      have hkr : K n x (v - (2 * n - m - (2 * n - x))) = K n (2 * n - x) (v - (2 * n - m - (2 * n - x))) := by
        have h1 := K_reflect (n := n) (x := 2 * n - x) (by omega) (v - (2 * n - m - (2 * n - x)))
        have h2 : 2 * n - (2 * n - x) = x := by omega
        rw [h2] at h1
        exact h1
      rw [hkr]
  rw [hA, hB, hC, hD]
  ring

private lemma H_split_3 {n m v : ℕ} (hm : m ≤ n) :
    (H n m v : ℚ) =
      (∑ x ∈ Finset.Ico 0 m, (if m - x ≤ v then (K n x (v - (m - x)) : ℚ) else 0)) +
      (K n m v : ℚ) +
      (∑ x ∈ Finset.Ico (m + 1) (2 * n + 1), (if x - m ≤ v then (K n x (v - (x - m)) : ℚ) else 0)) := by
  unfold H
  rw [← Nat.Ico_zero_eq_range]
  rw [sum_Ico_split _ (Nat.zero_le m) (by omega : m ≤ 2 * n + 1)]
  rw [sum_Ico_split _ (by omega : m ≤ m + 1) (by omega : m + 1 ≤ 2 * n + 1)]
  push_cast
  have hA : ∑ x ∈ Finset.Ico 0 m, (if adiff x m ≤ v then (K n x (v - adiff x m) : ℚ) else 0) =
      ∑ x ∈ Finset.Ico 0 m, (if m - x ≤ v then (K n x (v - (m - x)) : ℚ) else 0) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [Finset.mem_Ico] at hx
    have had : adiff x m = m - x := by unfold adiff; rw [if_pos (by omega)]
    rw [had]
  have hB : ∑ x ∈ Finset.Ico m (m + 1), (if adiff x m ≤ v then (K n x (v - adiff x m) : ℚ) else 0) =
      (K n m v : ℚ) := by
    rw [Finset.sum_Ico_succ_top (le_refl m), Finset.Ico_self, Finset.sum_empty, zero_add]
    have had : adiff m m = 0 := by unfold adiff; simp
    rw [had, if_pos (Nat.zero_le v), Nat.sub_zero]
  have hC : ∑ x ∈ Finset.Ico (m + 1) (2 * n + 1), (if adiff x m ≤ v then (K n x (v - adiff x m) : ℚ) else 0) =
      ∑ x ∈ Finset.Ico (m + 1) (2 * n + 1), (if x - m ≤ v then (K n x (v - (x - m)) : ℚ) else 0) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [Finset.mem_Ico] at hx
    have had : adiff x m = x - m := by unfold adiff; rw [if_neg (by omega)]
    rw [had]
  rw [hA, hB, hC]
  ring

private def H1p (v : ℚ) : ℚ := 4 * v ^ 2 + 2

private def H2p (m v p : ℚ) : ℚ :=
  (-2 * m ^ 2 + 20 * m * v + 10 * v ^ 2 + 12 * v + 8 - p * (4 * m + 4 * v + 2)) / 8

private def H3p (n m v p : ℚ) : ℚ :=
  (-4 * m ^ 2 + 8 * m * n - 8 * n ^ 2 + 40 * n * v - 12 * v ^ 2 + 24 * v - p * (8 * n + 8 * v + 4)) / 8

private def H4p (n m v p : ℚ) : ℚ :=
  (-m ^ 2 + 20 * m * n - 10 * m * v + 10 * m + 4 * n ^ 2 + 20 * n * v + 20 * n - 5 * v ^ 2 + 6 * v + 8 -
    p * (2 * m + 12 * n + 2 * v + 7)) / 8

private def H5p (n m v p : ℚ) : ℚ :=
  (2 * m ^ 2 - 4 * m * n + 52 * n ^ 2 - 20 * n * v + 60 * n + 2 * v ^ 2 - 12 * v + 16 -
    p * (20 * n - 4 * v + 10)) / 8

private def H6p (n m v p : ℚ) : ℚ :=
  (m ^ 2 - 12 * m * n + 2 * m * v - 6 * m + 36 * n ^ 2 - 12 * n * v + 36 * n + v ^ 2 - 6 * v + 8 -
    p * (-2 * m + 12 * n - 2 * v + 5)) / 8

private lemma H_V1 {n m v : ℕ} (hm : m ≤ n) (h1 : 1 ≤ v) (h2 : v ≤ m) :
    (H n m v : ℚ) = H1p v := by
  rw [H_split_3 hm]
  -- Left sum [0, m) splits at m - v and m - v + 1
  have hA : ∑ x ∈ Finset.Ico 0 m, (if m - x ≤ v then (K n x (v - (m - x)) : ℚ) else 0) =
      1 + ∑ x ∈ Finset.Ico (m - v + 1) m, (4 * ((v : ℚ) - m) + 4 * (x : ℚ)) := by
    rw [sum_Ico_split _ (Nat.zero_le (m - v)) (by omega : m - v ≤ m)]
    rw [sum_Ico_split _ (by omega : m - v ≤ m - v + 1) (by omega : m - v + 1 ≤ m)]
    have h0 : ∑ x ∈ Finset.Ico 0 (m - v), (if m - x ≤ v then (K n x (v - (m - x)) : ℚ) else 0) = 0 :=
      Finset.sum_eq_zero fun x hx => by simp only [Finset.mem_Ico] at hx; rw [if_neg (by omega)]
    have h1' : ∑ x ∈ Finset.Ico (m - v) (m - v + 1), (if m - x ≤ v then (K n x (v - (m - x)) : ℚ) else 0) = 1 := by
      rw [Finset.sum_Ico_succ_top (le_refl _), Finset.Ico_self, Finset.sum_empty, zero_add]
      rw [if_pos (by omega), show v - (m - (m - v)) = 0 by omega, K_zero (by omega)]
      simp
    have h2' : ∑ x ∈ Finset.Ico (m - v + 1) m, (if m - x ≤ v then (K n x (v - (m - x)) : ℚ) else 0) =
        ∑ x ∈ Finset.Ico (m - v + 1) m, (4 * ((v : ℚ) - m) + 4 * (x : ℚ)) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      simp only [Finset.mem_Ico] at hx
      rw [if_pos (by omega), K_R1 (by omega) (by omega) (by omega) (by omega)]
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; ring
    rw [h0, h1', h2', zero_add]
  have hB : (K n m v : ℚ) = 4 * (v : ℚ) := K_R1 (by omega) h1 h2 (by omega)
  have hC : ∑ x ∈ Finset.Ico (m + 1) (2 * n + 1), (if x - m ≤ v then (K n x (v - (x - m)) : ℚ) else 0) =
      (∑ x ∈ Finset.Ico (m + 1) (m + v), (4 * ((v : ℚ) + m) + (-4) * (x : ℚ))) + 1 := by
    rw [sum_Ico_split _ (by omega : m + 1 ≤ m + v) (by omega : m + v ≤ 2 * n + 1)]
    rw [sum_Ico_split _ (by omega : m + v ≤ m + v + 1) (by omega : m + v + 1 ≤ 2 * n + 1)]
    have h1' : ∑ x ∈ Finset.Ico (m + 1) (m + v), (if x - m ≤ v then (K n x (v - (x - m)) : ℚ) else 0) =
        ∑ x ∈ Finset.Ico (m + 1) (m + v), (4 * ((v : ℚ) + m) + (-4) * (x : ℚ)) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      simp only [Finset.mem_Ico] at hx
      rw [if_pos (by omega), K_R1 (by omega) (by omega) (by omega) (by omega)]
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; ring
    have h2' : ∑ x ∈ Finset.Ico (m + v) (m + v + 1), (if x - m ≤ v then (K n x (v - (x - m)) : ℚ) else 0) = 1 := by
      rw [Finset.sum_Ico_succ_top (le_refl _), Finset.Ico_self, Finset.sum_empty, zero_add]
      rw [if_pos (by omega), show v - (m + v - m) = 0 by omega, K_zero (by omega)]
      simp
    have h3' : ∑ x ∈ Finset.Ico (m + v + 1) (2 * n + 1), (if x - m ≤ v then (K n x (v - (x - m)) : ℚ) else 0) = 0 :=
      Finset.sum_eq_zero fun x hx => by simp only [Finset.mem_Ico] at hx; rw [if_neg (by omega)]
    rw [h1', h2', h3', add_zero]
  rw [hA, hB, hC, sum_Ico_lin _ _ (by omega), sum_Ico_lin _ _ (by omega)]
  unfold H1p
  rw [Nat.cast_add, Nat.cast_sub h2]
  push_cast
  ring

private lemma H_V2 {n m v : ℕ} (hm : m ≤ n) (h1 : m < v) (h2 : v ≤ 2 * n - m) :
    (H n m v : ℚ) = H2p m v ((m + v) % 2 : ℕ) := by
  rw [H_split_3 hm]
  set p := (m + v) % 2
  set mid := (m + v + 1) / 2
  have hmid_lo : m + 1 ≤ mid := by omega
  have hmid_hi : mid ≤ m + v := by omega
  have hA : ∑ x ∈ Finset.Ico 0 m, (if m - x ≤ v then (K n x (v - (m - x)) : ℚ) else 0) =
      ∑ x ∈ Finset.Ico 0 m, ((3 * (v : ℚ) - 3 * m + 2 - (p : ℕ)) / 2 + 3 * (x : ℚ)) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [Finset.mem_Ico] at hx
    rw [if_pos (by omega), K_R2 (by omega) (by omega) (by omega)]
    have hp : (x + (v - (m - x))) % 2 = p := by omega
    rw [hp, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; ring
  have hB : (K n m v : ℚ) = (3 * (v : ℚ) + 3 * m + 2 - (p : ℕ)) / 2 := K_R2 hm h1 h2
  have hC : ∑ x ∈ Finset.Ico (m + 1) (2 * n + 1), (if x - m ≤ v then (K n x (v - (x - m)) : ℚ) else 0) =
      (∑ x ∈ Finset.Ico (m + 1) mid, ((3 * (v : ℚ) + 3 * m + 2 - (p : ℕ)) / 2 + 0 * (x : ℚ))) +
      (∑ x ∈ Finset.Ico mid (m + v), (4 * ((v : ℚ) + m) + (-4) * (x : ℚ))) + 1 := by
    rw [sum_Ico_split _ hmid_lo (by omega : mid ≤ 2 * n + 1)]
    rw [sum_Ico_split _ hmid_hi (by omega : m + v ≤ 2 * n + 1)]
    rw [sum_Ico_split _ (by omega : m + v ≤ m + v + 1) (by omega : m + v + 1 ≤ 2 * n + 1)]
    have hc1 : ∑ x ∈ Finset.Ico (m + 1) mid, (if x - m ≤ v then (K n x (v - (x - m)) : ℚ) else 0) =
        ∑ x ∈ Finset.Ico (m + 1) mid, ((3 * (v : ℚ) + 3 * m + 2 - (p : ℕ)) / 2 + 0 * (x : ℚ)) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      simp only [Finset.mem_Ico] at hx
      rw [if_pos (by omega), K_R2 (by omega) (by omega) (by omega)]
      have hp : (x + (v - (x - m))) % 2 = p := by omega
      rw [hp, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; ring
    have hc2 : ∑ x ∈ Finset.Ico mid (m + v), (if x - m ≤ v then (K n x (v - (x - m)) : ℚ) else 0) =
        ∑ x ∈ Finset.Ico mid (m + v), (4 * ((v : ℚ) + m) + (-4) * (x : ℚ)) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      simp only [Finset.mem_Ico] at hx
      rw [if_pos (by omega), K_R1 (by omega) (by omega) (by omega) (by omega)]
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; ring
    have hc3 : ∑ x ∈ Finset.Ico (m + v) (m + v + 1), (if x - m ≤ v then (K n x (v - (x - m)) : ℚ) else 0) = 1 := by
      rw [Finset.sum_Ico_succ_top (le_refl _), Finset.Ico_self, Finset.sum_empty, zero_add]
      rw [if_pos (by omega), show v - (m + v - m) = 0 by omega, K_zero (by omega)]
      simp
    have hc4 : ∑ x ∈ Finset.Ico (m + v + 1) (2 * n + 1), (if x - m ≤ v then (K n x (v - (x - m)) : ℚ) else 0) = 0 :=
      Finset.sum_eq_zero fun x hx => by simp only [Finset.mem_Ico] at hx; rw [if_neg (by omega)]
    rw [hc1, hc2, hc3, hc4]
    ring
  rw [hA, hB, hC, sum_Ico_lin _ _ (Nat.zero_le m), sum_Ico_lin _ _ hmid_lo, sum_Ico_lin _ _ hmid_hi]
  have hmid_cast : (mid : ℚ) = ((m : ℚ) + v + (p : ℕ)) / 2 := by
    have hq := nat_div2_cast (m + v + 1)
    have hmod : (m + v + 1) % 2 = 1 - p := by omega
    rw [hmod, Nat.cast_sub (by omega : p ≤ 1)] at hq
    push_cast at hq
    linarith
  rw [hmid_cast]
  unfold H2p
  rcases Nat.mod_two_eq_zero_or_one (m + v) with hp | hp <;> simp only [p, hp] <;> push_cast <;> ring

private lemma H_V3 {n m v : ℕ} (hm : m ≤ n) (h1 : 2 * n - m < v) (h2 : v ≤ 2 * n + m) :
    (H n m v : ℚ) = H3p n m v ((m + v) % 2 : ℕ) := by
  rw [H_split_4 hm]
  set p := (m + v) % 2
  set midA := (2 * n + m - v) / 2 + 1
  set midD := (4 * n - m - v) / 2 + 1
  have hmidA_le : midA ≤ m := by omega
  have hmidD_le : midD ≤ n := by omega
  have hA : ∑ x ∈ Finset.Ico 0 m, (if m - x ≤ v then (K n x (v - (m - x)) : ℚ) else 0) =
      (∑ x ∈ Finset.Ico 0 midA, ((3 * (v : ℚ) - 3 * m + 2 - (p : ℕ)) / 2 + 3 * (x : ℚ))) +
      (∑ x ∈ Finset.Ico midA m, ((3 * (n : ℚ) - v + m + 2 - (p : ℕ)) + (-1) * (x : ℚ))) := by
    rw [sum_Ico_split _ (Nat.zero_le midA) hmidA_le]
    congr 1
    · refine Finset.sum_congr rfl fun x hx => ?_
      simp only [Finset.mem_Ico] at hx
      rw [if_pos (by omega), K_R2 (by omega) (by omega) (by omega)]
      have hp : (x + (v - (m - x))) % 2 = p := by omega
      rw [hp, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; ring
    · refine Finset.sum_congr rfl fun x hx => ?_
      simp only [Finset.mem_Ico] at hx
      rw [if_pos (by omega), K_R3 (by omega) (by omega) (by omega)]
      have hp : (x + (v - (m - x))) % 2 = p := by omega
      rw [hp, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; ring
  have hB : (K n m v : ℚ) = 3 * (n : ℚ) - v + 2 - (p : ℕ) := K_R3 hm h1 h2
  have hC : ∑ x ∈ Finset.Ico (m + 1) (n + 1), (if x - m ≤ v then (K n x (v - (x - m)) : ℚ) else 0) =
      ∑ x ∈ Finset.Ico (m + 1) (n + 1), ((3 * (n : ℚ) - v - m + 2 - (p : ℕ)) + 1 * (x : ℚ)) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [Finset.mem_Ico] at hx
    rw [if_pos (by omega), K_R3 (by omega) (by omega) (by omega)]
    have hp : (x + (v - (x - m))) % 2 = p := by omega
    rw [hp, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; ring
  have hD : ∑ y ∈ Finset.Ico 0 n, (if 2 * n - m - y ≤ v then (K n y (v - (2 * n - m - y)) : ℚ) else 0) =
      (∑ y ∈ Finset.Ico 0 midD, ((3 * (v : ℚ) + 3 * m - 6 * n + 2 - (p : ℕ)) / 2 + 3 * (y : ℚ))) +
      (∑ y ∈ Finset.Ico midD n, ((5 * (n : ℚ) - v - m + 2 - (p : ℕ)) + (-1) * (y : ℚ))) := by
    rw [sum_Ico_split _ (Nat.zero_le midD) hmidD_le]
    congr 1
    · refine Finset.sum_congr rfl fun y hy => ?_
      simp only [Finset.mem_Ico] at hy
      rw [if_pos (by omega), K_R2 (by omega) (by omega) (by omega)]
      have hp : (y + (v - (2 * n - m - y))) % 2 = p := by omega
      rw [hp, Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast; ring
    · refine Finset.sum_congr rfl fun y hy => ?_
      simp only [Finset.mem_Ico] at hy
      rw [if_pos (by omega), K_R3 (by omega) (by omega) (by omega)]
      have hp : (y + (v - (2 * n - m - y))) % 2 = p := by omega
      rw [hp, Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast; ring
  rw [hA, hB, hC, hD, sum_Ico_lin _ _ (Nat.zero_le midA), sum_Ico_lin _ _ hmidA_le,
      sum_Ico_lin _ _ (by omega : m + 1 ≤ n + 1),
      sum_Ico_lin _ _ (Nat.zero_le midD), sum_Ico_lin _ _ hmidD_le]
  have hmidA_cast : (midA : ℚ) = (2 * (n : ℚ) + m - v - (p : ℕ)) / 2 + 1 := by
    have hq := nat_div2_cast (2 * n + m - v)
    have hmod : (2 * n + m - v) % 2 = p := by omega
    rw [hmod, Nat.cast_sub (by omega)] at hq
    dsimp only [midA]
    push_cast at hq ⊢
    linarith
  have hmidD_cast : (midD : ℚ) = (4 * (n : ℚ) - m - v - (p : ℕ)) / 2 + 1 := by
    have hq := nat_div2_cast (4 * n - m - v)
    have hmod : (4 * n - m - v) % 2 = p := by omega
    rw [hmod, Nat.cast_sub (by omega), Nat.cast_sub (by omega)] at hq
    dsimp only [midD]
    push_cast at hq ⊢
    linarith
  rw [hmidA_cast, hmidD_cast]
  unfold H3p
  rcases Nat.mod_two_eq_zero_or_one (m + v) with hp | hp <;> simp only [p, hp] <;> push_cast <;> ring

private lemma H_V4 {n m v : ℕ} (hm : m ≤ n) (h1 : 2 * n + m < v) (h2 : v ≤ 4 * n - m) :
    (H n m v : ℚ) = H4p n m v ((m + v) % 2 : ℕ) := by
  rw [H_split_4 hm]
  set p := (m + v) % 2
  set midC := (v + m - 2 * n + 1) / 2
  set midD := (4 * n - m - v) / 2 + 1
  have hmidC_lo : m + 1 ≤ midC := by omega
  have hmidC_hi : midC ≤ n + 1 := by omega
  have hmidD_le : midD ≤ n := by omega
  have hA : ∑ x ∈ Finset.Ico 0 m, (if m - x ≤ v then (K n x (v - (m - x)) : ℚ) else 0) =
      ∑ x ∈ Finset.Ico 0 m, ((4 * (n : ℚ) + m - v + 2 - (p : ℕ)) / 2 + (-1) * (x : ℚ)) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [Finset.mem_Ico] at hx
    rw [if_pos (by omega), K_R4 (by omega) (by omega) (by omega)]
    have hp : (x + (v - (m - x))) % 2 = p := by omega
    rw [hp, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; ring
  have hB : (K n m v : ℚ) = (4 * (n : ℚ) - m - v + 2 - (p : ℕ)) / 2 := K_R4 hm h1 h2
  have hC : ∑ x ∈ Finset.Ico (m + 1) (n + 1), (if x - m ≤ v then (K n x (v - (x - m)) : ℚ) else 0) =
      (∑ x ∈ Finset.Ico (m + 1) midC, ((4 * (n : ℚ) - m - v + 2 - (p : ℕ)) / 2 + 0 * (x : ℚ))) +
      (∑ x ∈ Finset.Ico midC (n + 1), ((3 * (n : ℚ) - v - m + 2 - (p : ℕ)) + 1 * (x : ℚ))) := by
    rw [sum_Ico_split _ hmidC_lo hmidC_hi]
    congr 1
    · refine Finset.sum_congr rfl fun x hx => ?_
      simp only [Finset.mem_Ico] at hx
      rw [if_pos (by omega), K_R4 (by omega) (by omega) (by omega)]
      have hp : (x + (v - (x - m))) % 2 = p := by omega
      rw [hp, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; ring
    · refine Finset.sum_congr rfl fun x hx => ?_
      simp only [Finset.mem_Ico] at hx
      rw [if_pos (by omega), K_R3 (by omega) (by omega) (by omega)]
      have hp : (x + (v - (x - m))) % 2 = p := by omega
      rw [hp, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; ring
  have hD : ∑ y ∈ Finset.Ico 0 n, (if 2 * n - m - y ≤ v then (K n y (v - (2 * n - m - y)) : ℚ) else 0) =
      (∑ y ∈ Finset.Ico 0 midD, ((3 * (v : ℚ) + 3 * m - 6 * n + 2 - (p : ℕ)) / 2 + 3 * (y : ℚ))) +
      (∑ y ∈ Finset.Ico midD n, ((5 * (n : ℚ) - v - m + 2 - (p : ℕ)) + (-1) * (y : ℚ))) := by
    rw [sum_Ico_split _ (Nat.zero_le midD) hmidD_le]
    congr 1
    · refine Finset.sum_congr rfl fun y hy => ?_
      simp only [Finset.mem_Ico] at hy
      rw [if_pos (by omega), K_R2 (by omega) (by omega) (by omega)]
      have hp : (y + (v - (2 * n - m - y))) % 2 = p := by omega
      rw [hp, Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast; ring
    · refine Finset.sum_congr rfl fun y hy => ?_
      simp only [Finset.mem_Ico] at hy
      rw [if_pos (by omega), K_R3 (by omega) (by omega) (by omega)]
      have hp : (y + (v - (2 * n - m - y))) % 2 = p := by omega
      rw [hp, Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast; ring
  rw [hA, hB, hC, hD, sum_Ico_lin _ _ (Nat.zero_le m), sum_Ico_lin _ _ hmidC_lo,
      sum_Ico_lin _ _ hmidC_hi, sum_Ico_lin _ _ (Nat.zero_le midD), sum_Ico_lin _ _ hmidD_le]
  have hmidC_cast : (midC : ℚ) = ((v : ℚ) + m - 2 * n + (p : ℕ)) / 2 := by
    have hq := nat_div2_cast (v + m - 2 * n + 1)
    have hmod : (v + m - 2 * n + 1) % 2 = 1 - p := by omega
    rw [hmod, Nat.cast_sub (by omega : p ≤ 1), Nat.cast_add, Nat.cast_sub (by omega)] at hq
    dsimp only [midC]
    push_cast at hq ⊢
    linarith
  have hmidD_cast : (midD : ℚ) = (4 * (n : ℚ) - m - v - (p : ℕ)) / 2 + 1 := by
    have hq := nat_div2_cast (4 * n - m - v)
    have hmod : (4 * n - m - v) % 2 = p := by omega
    rw [hmod, Nat.cast_sub (by omega), Nat.cast_sub (by omega)] at hq
    dsimp only [midD]
    push_cast at hq ⊢
    linarith
  rw [hmidC_cast, hmidD_cast]
  unfold H4p
  rcases Nat.mod_two_eq_zero_or_one (m + v) with hp | hp <;> simp only [p, hp] <;> push_cast <;> ring

private lemma H_V5 {n m v : ℕ} (hm : m ≤ n) (h1 : 4 * n - m < v) (h2 : v ≤ 4 * n + m) :
    (H n m v : ℚ) = H5p n m v ((m + v) % 2 : ℕ) := by
  rw [H_split_4 hm]
  set p := (m + v) % 2
  set midA := (4 * n + m - v) / 2 + 1
  set midD := (6 * n - m - v) / 2 + 1
  have hmidA_le : midA ≤ m := by omega
  have hmidD_le : midD ≤ n := by omega
  have hA : ∑ x ∈ Finset.Ico 0 m, (if m - x ≤ v then (K n x (v - (m - x)) : ℚ) else 0) =
      ∑ x ∈ Finset.Ico 0 midA, ((4 * (n : ℚ) + m - v + 2 - (p : ℕ)) / 2 + (-1) * (x : ℚ)) := by
    rw [sum_Ico_split _ (Nat.zero_le midA) hmidA_le]
    have h0 : ∑ x ∈ Finset.Ico midA m, (if m - x ≤ v then (K n x (v - (m - x)) : ℚ) else 0) = 0 :=
      Finset.sum_eq_zero fun x hx => by
        simp only [Finset.mem_Ico] at hx
        rw [if_pos (by omega), K_R5 (by omega) (by omega)]
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [Finset.mem_Ico] at hx
    rw [if_pos (by omega), K_R4 (by omega) (by omega) (by omega)]
    have hp : (x + (v - (m - x))) % 2 = p := by omega
    rw [hp, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; ring
  have hB : (K n m v : ℚ) = 0 := K_R5 hm h1
  have hC : ∑ x ∈ Finset.Ico (m + 1) (n + 1), (if x - m ≤ v then (K n x (v - (x - m)) : ℚ) else 0) = 0 :=
    Finset.sum_eq_zero fun x hx => by
      simp only [Finset.mem_Ico] at hx
      rw [if_pos (by omega), K_R5 (by omega) (by omega)]
  have hD : ∑ y ∈ Finset.Ico 0 n, (if 2 * n - m - y ≤ v then (K n y (v - (2 * n - m - y)) : ℚ) else 0) =
      ∑ y ∈ Finset.Ico 0 midD, ((6 * (n : ℚ) - m - v + 2 - (p : ℕ)) / 2 + (-1) * (y : ℚ)) := by
    rw [sum_Ico_split _ (Nat.zero_le midD) hmidD_le]
    have h0 : ∑ y ∈ Finset.Ico midD n, (if 2 * n - m - y ≤ v then (K n y (v - (2 * n - m - y)) : ℚ) else 0) = 0 :=
      Finset.sum_eq_zero fun y hy => by
        simp only [Finset.mem_Ico] at hy
        rw [if_pos (by omega), K_R5 (by omega) (by omega)]
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun y hy => ?_
    simp only [Finset.mem_Ico] at hy
    rw [if_pos (by omega), K_R4 (by omega) (by omega) (by omega)]
    have hp : (y + (v - (2 * n - m - y))) % 2 = p := by omega
    rw [hp, Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  rw [hA, hB, hC, hD, sum_Ico_lin _ _ (Nat.zero_le midA), sum_Ico_lin _ _ (Nat.zero_le midD)]
  have hmidA_cast : (midA : ℚ) = (4 * (n : ℚ) + m - v - (p : ℕ)) / 2 + 1 := by
    have hq := nat_div2_cast (4 * n + m - v)
    have hmod : (4 * n + m - v) % 2 = p := by omega
    rw [hmod, Nat.cast_sub (by omega)] at hq
    dsimp only [midA]
    push_cast at hq ⊢
    linarith
  have hmidD_cast : (midD : ℚ) = (6 * (n : ℚ) - m - v - (p : ℕ)) / 2 + 1 := by
    have hq := nat_div2_cast (6 * n - m - v)
    have hmod : (6 * n - m - v) % 2 = p := by omega
    rw [hmod, Nat.cast_sub (by omega), Nat.cast_sub (by omega)] at hq
    dsimp only [midD]
    push_cast at hq ⊢
    linarith
  rw [hmidA_cast, hmidD_cast]
  unfold H5p
  rcases Nat.mod_two_eq_zero_or_one (m + v) with hp | hp <;> simp only [p, hp] <;> push_cast <;> ring

private lemma H_V6 {n m v : ℕ} (hm : m ≤ n) (h1 : 4 * n + m < v) (h2 : v ≤ 6 * n - m) :
    (H n m v : ℚ) = H6p n m v ((m + v) % 2 : ℕ) := by
  rw [H_split_4 hm]
  set p := (m + v) % 2
  set midD := (6 * n - m - v) / 2 + 1
  have hmidD_le : midD ≤ n := by omega
  have hA : ∑ x ∈ Finset.Ico 0 m, (if m - x ≤ v then (K n x (v - (m - x)) : ℚ) else 0) = 0 :=
    Finset.sum_eq_zero fun x hx => by
      simp only [Finset.mem_Ico] at hx
      rw [if_pos (by omega), K_R5 (by omega) (by omega)]
  have hB : (K n m v : ℚ) = 0 := K_R5 hm (by omega)
  have hC : ∑ x ∈ Finset.Ico (m + 1) (n + 1), (if x - m ≤ v then (K n x (v - (x - m)) : ℚ) else 0) = 0 :=
    Finset.sum_eq_zero fun x hx => by
      simp only [Finset.mem_Ico] at hx
      rw [if_pos (by omega), K_R5 (by omega) (by omega)]
  have hD : ∑ y ∈ Finset.Ico 0 n, (if 2 * n - m - y ≤ v then (K n y (v - (2 * n - m - y)) : ℚ) else 0) =
      ∑ y ∈ Finset.Ico 0 midD, ((6 * (n : ℚ) - m - v + 2 - (p : ℕ)) / 2 + (-1) * (y : ℚ)) := by
    rw [sum_Ico_split _ (Nat.zero_le midD) hmidD_le]
    have h0 : ∑ y ∈ Finset.Ico midD n, (if 2 * n - m - y ≤ v then (K n y (v - (2 * n - m - y)) : ℚ) else 0) = 0 :=
      Finset.sum_eq_zero fun y hy => by
        simp only [Finset.mem_Ico] at hy
        rw [if_pos (by omega), K_R5 (by omega) (by omega)]
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun y hy => ?_
    simp only [Finset.mem_Ico] at hy
    rw [if_pos (by omega), K_R4 (by omega) (by omega) (by omega)]
    have hp : (y + (v - (2 * n - m - y))) % 2 = p := by omega
    rw [hp, Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  rw [hA, hB, hC, hD, sum_Ico_lin _ _ (Nat.zero_le midD)]
  have hmidD_cast : (midD : ℚ) = (6 * (n : ℚ) - m - v - (p : ℕ)) / 2 + 1 := by
    have hq := nat_div2_cast (6 * n - m - v)
    have hmod : (6 * n - m - v) % 2 = p := by omega
    rw [hmod, Nat.cast_sub (by omega), Nat.cast_sub (by omega)] at hq
    dsimp only [midD]
    push_cast at hq ⊢
    linarith
  rw [hmidD_cast]
  unfold H6p
  rcases Nat.mod_two_eq_zero_or_one (m + v) with hp | hp <;> simp only [p, hp] <;> push_cast <;> ring

private lemma H_V7 {n m v : ℕ} (hm : m ≤ n) (h1 : 6 * n - m < v) : (H n m v : ℚ) = 0 := by
  rw [H_split_4 hm]
  have hA : ∑ x ∈ Finset.Ico 0 m, (if m - x ≤ v then (K n x (v - (m - x)) : ℚ) else 0) = 0 :=
    Finset.sum_eq_zero fun x hx => by
      simp only [Finset.mem_Ico] at hx
      rw [if_pos (by omega), K_R5 (by omega) (by omega)]
  have hB : (K n m v : ℚ) = 0 := K_R5 hm (by omega)
  have hC : ∑ x ∈ Finset.Ico (m + 1) (n + 1), (if x - m ≤ v then (K n x (v - (x - m)) : ℚ) else 0) = 0 :=
    Finset.sum_eq_zero fun x hx => by
      simp only [Finset.mem_Ico] at hx
      rw [if_pos (by omega), K_R5 (by omega) (by omega)]
  have hD : ∑ y ∈ Finset.Ico 0 n, (if 2 * n - m - y ≤ v then (K n y (v - (2 * n - m - y)) : ℚ) else 0) = 0 :=
    Finset.sum_eq_zero fun y hy => by
      simp only [Finset.mem_Ico] at hy
      rw [if_pos (by omega), K_R5 (by omega) (by omega)]
  rw [hA, hB, hC, hD]
  ring

/-! ### Universal antiderivatives for inner sums over v -/

private def F26 (m p r k : ℚ) : ℚ :=
  (48 * k ^ 5 +
    (-24 * (3 * p - 5 * r - 4)) * k ^ 4 +
    (8 * (-8 * m ^ 2 - 4 * m * p + 9 * m + 2 * p ^ 2 - 18 * p * r - 7 * p + 15 * r ^ 2 + 24 * r - 4)) * k ^ 3 +
    (12 * (3 * m ^ 3 + 6 * m ^ 2 * p - 8 * m ^ 2 * r - 7 * m ^ 2 - 4 * m * p * r - 5 * m * p + 9 * m * r +
      2 * p ^ 2 * r + p ^ 2 - 9 * p * r ^ 2 - 7 * p * r + 4 * p + 5 * r ^ 3 + 12 * r ^ 2 - 4 * r - 4)) * k ^ 2 +
    (-3 * m ^ 4 - 12 * m ^ 3 * p + 36 * m ^ 3 * r - 18 * m ^ 3 - 12 * m ^ 2 * p ^ 2 + 72 * m ^ 2 * p * r -
      24 * m ^ 2 * p - 48 * m ^ 2 * r ^ 2 - 84 * m ^ 2 * r + 136 * m ^ 2 + 24 * m * p ^ 2 - 24 * m * p * r ^ 2 -
      60 * m * p * r + 86 * m * p + 54 * m * r ^ 2 - 144 * m + 12 * p ^ 2 * r ^ 2 + 12 * p ^ 2 * r - 13 * p ^ 2 -
      36 * p * r ^ 3 - 42 * p * r ^ 2 + 48 * p * r - 4 * p + 15 * r ^ 4 + 48 * r ^ 3 - 24 * r ^ 2 - 48 * r + 32) * k) / 96

private lemma sum_Ico_P26 (n m p r : ℚ) {a b : ℕ} (h : a ≤ b) :
    ∑ k ∈ Finset.Ico a b, H2p m (2 * (k : ℚ) + r) p * H6p n m (6 * n - (2 * (k : ℚ) + r)) p =
      F26 m p r b - F26 m p r a := by
  exact sum_Ico_telescope h _ (fun k => F26 m p r k) (fun k => by
    unfold H2p H6p F26; push_cast; ring)

private def F35 (n m p r k : ℚ) : ℚ :=
  (-144 * k ^ 5 +
    (120 * (4 * n + p - 3 * r)) * k ^ 4 +
    (40 * (-2 * m ^ 2 + 4 * m * n - 14 * n ^ 2 - 12 * n * p + 24 * n * r + 9 * n + 2 * p ^ 2 +
      6 * p * r - 11 * p - 9 * r ^ 2 + 18)) * k ^ 3 +
    (60 * (3 * m ^ 2 * n - 2 * m ^ 2 * r + 2 * m ^ 2 - 6 * m * n ^ 2 + 4 * m * n * r - 4 * m * n +
      6 * n ^ 3 + 6 * n ^ 2 * p - 14 * n ^ 2 * r - n ^ 2 - 12 * n * p * r + 3 * n * p + 12 * n * r ^ 2 +
      9 * n * r - 14 * n + 2 * p ^ 2 * r + p ^ 2 + 3 * p * r ^ 2 - 11 * p * r - 6 * p - 3 * r ^ 3 + 18 * r)) * k ^ 2 +
    (-15 * m ^ 4 + 60 * m ^ 3 * n - 120 * m ^ 2 * n ^ 2 - 60 * m ^ 2 * n * p + 180 * m ^ 2 * n * r -
      90 * m ^ 2 * n + 60 * m ^ 2 * p - 60 * m ^ 2 * r ^ 2 + 120 * m ^ 2 * r - 160 * m ^ 2 + 120 * m * n ^ 3 +
      120 * m * n ^ 2 * p - 360 * m * n ^ 2 * r + 180 * m * n ^ 2 - 120 * m * n * p + 120 * m * n * r ^ 2 -
      240 * m * n * r + 320 * m * n - 60 * n ^ 4 - 120 * n ^ 3 * p + 360 * n ^ 3 * r - 180 * n ^ 3 -
      60 * n ^ 2 * p ^ 2 + 360 * n ^ 2 * p * r - 60 * n ^ 2 * p - 420 * n ^ 2 * r ^ 2 - 60 * n ^ 2 * r +
      380 * n ^ 2 + 120 * n * p ^ 2 - 360 * n * p * r ^ 2 + 180 * n * p * r + 150 * n * p + 240 * n * r ^ 3 +
      270 * n * r ^ 2 - 840 * n * r + 60 * p ^ 2 * r ^ 2 + 60 * p ^ 2 * r - 65 * p ^ 2 + 60 * p * r ^ 3 -
      330 * p * r ^ 2 - 360 * p * r + 560 * p - 45 * r ^ 4 + 540 * r ^ 2 - 576) * k) / 120

private lemma sum_Ico_P35 (n m p r : ℚ) {a b : ℕ} (h : a ≤ b) :
    ∑ k ∈ Finset.Ico a b, H3p n m (2 * (k : ℚ) + r) p * H5p n m (6 * n - (2 * (k : ℚ) + r)) p =
      F35 n m p r b - F35 n m p r a := by
  exact sum_Ico_telescope h _ (fun k => F35 n m p r k) (fun k => by
    unfold H3p H5p F35; push_cast; ring)

private def F44 (n m p r k : ℚ) : ℚ :=
  (240 * k ^ 5 +
    (600 * (-3 * n + r - 1)) * k ^ 4 +
    (-8 * (45 * m ^ 2 + 50 * m * n + 10 * m * p - 10 * m - 530 * n ^ 2 - 70 * n * p + 450 * n * r -
      320 * n + 2 * p ^ 2 - 47 * p - 75 * r ^ 2 + 150 * r + 8)) * k ^ 3 +
    (-12 * (-3 * n + r - 1) * (45 * m ^ 2 + 50 * m * n + 10 * m * p - 10 * m - 80 * n ^ 2 - 70 * n * p +
      150 * n * r - 20 * n + 2 * p ^ 2 - 47 * p - 25 * r ^ 2 + 50 * r + 58)) * k ^ 2 +
    (3 * m ^ 4 + 60 * m ^ 3 * n + 12 * m ^ 3 * p - 60 * m ^ 3 - 2244 * m ^ 2 * n ^ 2 + 228 * m ^ 2 * n * p +
      1620 * m ^ 2 * n * r - 2448 * m ^ 2 * n + 12 * m ^ 2 * p ^ 2 - 78 * m ^ 2 * p - 270 * m ^ 2 * r ^ 2 +
      540 * m ^ 2 * r + 72 * m ^ 2 - 3840 * m * n ^ 3 + 312 * m * n ^ 2 * p + 1800 * m * n ^ 2 * r -
      2400 * m * n ^ 2 + 216 * m * n * p ^ 2 + 360 * m * n * p * r - 1476 * m * n * p - 300 * m * n * r ^ 2 +
      240 * m * n * r + 1960 * m * n + 84 * m * p ^ 2 - 60 * m * p * r ^ 2 + 120 * m * p * r - 556 * m * p +
      60 * m * r ^ 2 - 120 * m * r + 520 * m - 672 * n ^ 4 + 1728 * n ^ 3 * p - 2880 * n ^ 3 * r + 192 * n ^ 3 +
      864 * n ^ 2 * p ^ 2 - 2520 * n ^ 2 * p * r + 156 * n ^ 2 * p + 3180 * n ^ 2 * r ^ 2 - 1680 * n ^ 2 * r -
      448 * n ^ 2 + 72 * n * p ^ 2 * r + 684 * n * p ^ 2 + 420 * n * p * r ^ 2 - 2532 * n * p * r - 488 * n * p -
      900 * n * r ^ 3 + 1920 * n * r ^ 2 + 1848 * n * r - 784 * n - 12 * p ^ 2 * r ^ 2 + 24 * p ^ 2 * r +
      139 * p ^ 2 + 282 * p * r ^ 2 - 564 * p * r - 148 * p + 75 * r ^ 4 - 300 * r ^ 3 - 48 * r ^ 2 +
      696 * r - 80) * k) / 192

private lemma sum_Ico_P44 (n m p r : ℚ) {a b : ℕ} (h : a ≤ b) :
    ∑ k ∈ Finset.Ico a b, H4p n m (2 * (k : ℚ) + r) p * H4p n m (6 * n - (2 * (k : ℚ) + r)) p =
      F44 n m p r b - F44 n m p r a := by
  exact sum_Ico_telescope h _ (fun k => F44 n m p r k) (fun k => by
    unfold H4p F44; push_cast; ring)

/-! ### Inner sum S(n, m) = ∑_{v=0}^{6n} H(n, m, v) * H(n, m, 6n - v) -/

private def S (n m : ℕ) : ℚ :=
  ∑ v ∈ Finset.range (6 * n + 1), (H n m v : ℚ) * (H n m (6 * n - v) : ℚ)

private lemma S_reflect {n m : ℕ} (hm : m ≤ 2 * n) : S n (2 * n - m) = S n m := by
  unfold S
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [H_reflect hm, H_reflect hm]

private lemma sum_Ico_sym_H (n m lo hi : ℕ) (h1 : lo ≤ hi) (h2 : hi ≤ 6 * n + 1) :
    ∑ v ∈ Finset.Ico (6 * n + 1 - hi) (6 * n + 1 - lo), (H n m v : ℚ) * (H n m (6 * n - v) : ℚ) =
      ∑ v ∈ Finset.Ico lo hi, (H n m v : ℚ) * (H n m (6 * n - v) : ℚ) := by
  refine Finset.sum_bij (fun v _ => 6 * n - v) ?_ ?_ ?_ ?_
  · intro v hv; simp only [Finset.mem_Ico] at hv ⊢; omega
  · intro v1 hv1 v2 hv2 h; simp only [Finset.mem_Ico] at hv1 hv2; omega
  · intro v hv; simp only [Finset.mem_Ico] at hv; exact ⟨6 * n - v, by simp; omega, by omega⟩
  · intro v hv
    simp only [Finset.mem_Ico] at hv
    rw [show 6 * n - (6 * n - v) = v by omega, mul_comm]

private lemma S_zero {n : ℕ} (hn : 1 ≤ n) :
    S n 0 = 125 * (n : ℚ) ^ 5 / 12 + 983 * (n : ℚ) ^ 4 / 24 + 73 * (n : ℚ) ^ 3 +
      613 * (n : ℚ) ^ 2 / 24 + 97 * (n : ℚ) / 12 + 1 := by
  unfold S
  rw [← Nat.Ico_zero_eq_range]
  rw [sum_Ico_split _ (by omega : 0 ≤ 1) (by omega : 1 ≤ 6 * n + 1)]
  rw [sum_Ico_split _ (by omega : 1 ≤ 2 * n) (by omega : 2 * n ≤ 6 * n + 1)]
  rw [sum_Ico_split _ (by omega : 2 * n ≤ 2 * n + 1) (by omega : 2 * n + 1 ≤ 6 * n + 1)]
  rw [sum_Ico_split _ (by omega : 2 * n + 1 ≤ 4 * n) (by omega : 4 * n ≤ 6 * n + 1)]
  rw [sum_Ico_split _ (by omega : 4 * n ≤ 4 * n + 1) (by omega : 4 * n + 1 ≤ 6 * n + 1)]
  rw [sum_Ico_split _ (by omega : 4 * n + 1 ≤ 6 * n) (by omega : 6 * n ≤ 6 * n + 1)]
  have hsym1 := sum_Ico_sym_H n 0 1 (2 * n) (by omega) (by omega)
  have hsym1' : 6 * n + 1 - 2 * n = 4 * n + 1 ∧ 6 * n + 1 - 1 = 6 * n := by omega
  rw [hsym1'.1, hsym1'.2] at hsym1
  rw [hsym1]
  have hpt0 : ∑ v ∈ Finset.Ico 0 1, (H n 0 v : ℚ) * (H n 0 (6 * n - v) : ℚ) = 1 := by
    rw [Finset.sum_Ico_succ_top (le_refl 0), Finset.Ico_self, Finset.sum_empty, zero_add]
    rw [H_zero (Nat.zero_le _), Nat.sub_zero, H_V6 (Nat.zero_le n) (by omega) (by omega)]
    have hmod : (0 + 6 * n) % 2 = 0 := by omega
    rw [hmod]; unfold H6p; push_cast; ring
  have hpt6 : ∑ v ∈ Finset.Ico (6 * n) (6 * n + 1), (H n 0 v : ℚ) * (H n 0 (6 * n - v) : ℚ) = 1 := by
    rw [Finset.sum_Ico_succ_top (le_refl _), Finset.Ico_self, Finset.sum_empty, zero_add]
    rw [Nat.sub_self, H_zero (Nat.zero_le _), H_V6 (Nat.zero_le n) (by omega) (by omega)]
    have hmod : (0 + 6 * n) % 2 = 0 := by omega
    rw [hmod]; unfold H6p; push_cast; ring
  have hpt2 : ∑ v ∈ Finset.Ico (2 * n) (2 * n + 1), (H n 0 v : ℚ) * (H n 0 (6 * n - v) : ℚ) =
      H2p 0 (2 * (n : ℚ)) 0 * H4p n 0 (4 * (n : ℚ)) 0 := by
    rw [Finset.sum_Ico_succ_top (le_refl _), Finset.Ico_self, Finset.sum_empty, zero_add]
    rw [H_V2 (Nat.zero_le n) (by omega) (by omega), H_V4 (Nat.zero_le n) (by omega) (by omega)]
    have hm1 : (0 + 2 * n) % 2 = 0 := by omega
    have hm2 : (0 + (6 * n - 2 * n)) % 2 = 0 := by omega
    have hsub : 6 * n - 2 * n = 4 * n := by omega
    rw [hm1, hm2, hsub]; push_cast; rfl
  have hpt4 : ∑ v ∈ Finset.Ico (4 * n) (4 * n + 1), (H n 0 v : ℚ) * (H n 0 (6 * n - v) : ℚ) =
      H2p 0 (2 * (n : ℚ)) 0 * H4p n 0 (4 * (n : ℚ)) 0 := by
    rw [Finset.sum_Ico_succ_top (le_refl _), Finset.Ico_self, Finset.sum_empty, zero_add]
    rw [H_V4 (Nat.zero_le n) (by omega) (by omega), H_V2 (Nat.zero_le n) (by omega) (by omega)]
    have hm1 : (0 + 4 * n) % 2 = 0 := by omega
    have hm2 : (0 + (6 * n - 4 * n)) % 2 = 0 := by omega
    have hsub : 6 * n - 4 * n = 2 * n := by omega
    rw [hm1, hm2, hsub]; push_cast; exact mul_comm _ _
  have hI26 : ∑ v ∈ Finset.Ico 1 (2 * n), (H n 0 v : ℚ) * (H n 0 (6 * n - v) : ℚ) =
      (F26 0 0 0 n - F26 0 0 0 1) + (F26 0 1 1 n - F26 0 1 1 0) := by
    rw [sum_Ico_even_odd _ (by omega)]
    have hb1 : (1 + 1) / 2 = 1 ∧ (2 * n + 1) / 2 = n ∧ 1 / 2 = 0 ∧ (2 * n) / 2 = n := by omega
    rw [hb1.1, hb1.2.1, hb1.2.2.1, hb1.2.2.2]
    congr 1
    · trans ∑ k ∈ Finset.Ico 1 n, H2p 0 (2 * (k : ℚ) + 0) 0 * H6p n 0 (6 * n - (2 * (k : ℚ) + 0)) 0
      · refine Finset.sum_congr rfl fun k hk => ?_
        simp only [Finset.mem_Ico] at hk
        rw [H_V2 (Nat.zero_le n) (by omega) (by omega), H_V6 (Nat.zero_le n) (by omega) (by omega)]
        have hp1 : (0 + 2 * k) % 2 = 0 := by omega
        have hp2 : (0 + (6 * n - 2 * k)) % 2 = 0 := by omega
        rw [hp1, hp2, Nat.cast_sub (by omega)]; push_cast; simp only [add_zero]
      · rw [sum_Ico_P26 n 0 0 0 (by omega : 1 ≤ n)]; push_cast; rfl
    · trans ∑ k ∈ Finset.Ico 0 n, H2p 0 (2 * (k : ℚ) + 1) 1 * H6p n 0 (6 * n - (2 * (k : ℚ) + 1)) 1
      · refine Finset.sum_congr rfl fun k hk => ?_
        simp only [Finset.mem_Ico] at hk
        rw [H_V2 (Nat.zero_le n) (by omega) (by omega), H_V6 (Nat.zero_le n) (by omega) (by omega)]
        have hp1 : (0 + (2 * k + 1)) % 2 = 1 := by omega
        have hp2 : (0 + (6 * n - (2 * k + 1))) % 2 = 1 := by omega
        rw [hp1, hp2, Nat.cast_sub (by omega)]; push_cast; rfl
      · rw [sum_Ico_P26 n 0 1 1 (Nat.zero_le n)]; push_cast; rfl
  have hI44 : ∑ v ∈ Finset.Ico (2 * n + 1) (4 * n), (H n 0 v : ℚ) * (H n 0 (6 * n - v) : ℚ) =
      (F44 n 0 0 0 (2 * n) - F44 n 0 0 0 (n + 1)) + (F44 n 0 1 1 (2 * n) - F44 n 0 1 1 n) := by
    rw [sum_Ico_even_odd _ (by omega)]
    have hb : (2 * n + 1 + 1) / 2 = n + 1 ∧ (4 * n + 1) / 2 = 2 * n ∧
        (2 * n + 1) / 2 = n ∧ (4 * n) / 2 = 2 * n := by omega
    rw [hb.1, hb.2.1, hb.2.2.1, hb.2.2.2]
    congr 1
    · trans ∑ k ∈ Finset.Ico (n + 1) (2 * n), H4p n 0 (2 * (k : ℚ) + 0) 0 * H4p n 0 (6 * n - (2 * (k : ℚ) + 0)) 0
      · refine Finset.sum_congr rfl fun k hk => ?_
        simp only [Finset.mem_Ico] at hk
        rw [H_V4 (Nat.zero_le n) (by omega) (by omega), H_V4 (Nat.zero_le n) (by omega) (by omega)]
        have hp1 : (0 + 2 * k) % 2 = 0 := by omega
        have hp2 : (0 + (6 * n - 2 * k)) % 2 = 0 := by omega
        rw [hp1, hp2, Nat.cast_sub (by omega)]; push_cast; simp only [add_zero]
      · rw [sum_Ico_P44 n 0 0 0 (by omega : n + 1 ≤ 2 * n)]; push_cast; rfl
    · trans ∑ k ∈ Finset.Ico n (2 * n), H4p n 0 (2 * (k : ℚ) + 1) 1 * H4p n 0 (6 * n - (2 * (k : ℚ) + 1)) 1
      · refine Finset.sum_congr rfl fun k hk => ?_
        simp only [Finset.mem_Ico] at hk
        rw [H_V4 (Nat.zero_le n) (by omega) (by omega), H_V4 (Nat.zero_le n) (by omega) (by omega)]
        have hp1 : (0 + (2 * k + 1)) % 2 = 1 := by omega
        have hp2 : (0 + (6 * n - (2 * k + 1))) % 2 = 1 := by omega
        rw [hp1, hp2, Nat.cast_sub (by omega)]; push_cast; rfl
      · rw [sum_Ico_P44 n 0 1 1 (by omega : n ≤ 2 * n)]; push_cast; rfl
  rw [hpt0, hpt6, hpt2, hpt4, hI26, hI44]
  unfold H2p H4p F26 F44
  ring

private lemma S_diag {n : ℕ} (hn : 1 ≤ n) :
    S n n = 16 * (n : ℚ) ^ 5 / 5 + 21 * (n : ℚ) ^ 4 + 50 * (n : ℚ) ^ 3 +
      89 * (n : ℚ) ^ 2 - 116 * (n : ℚ) / 5 + 8 := by
  unfold S
  rw [← Nat.Ico_zero_eq_range]
  rw [sum_Ico_split _ (by omega : 0 ≤ n) (by omega : n ≤ 6 * n + 1)]
  rw [sum_Ico_split _ (by omega : n ≤ n + 1) (by omega : n + 1 ≤ 6 * n + 1)]
  rw [sum_Ico_split _ (by omega : n + 1 ≤ 3 * n) (by omega : 3 * n ≤ 6 * n + 1)]
  rw [sum_Ico_split _ (by omega : 3 * n ≤ 3 * n + 1) (by omega : 3 * n + 1 ≤ 6 * n + 1)]
  rw [sum_Ico_split _ (by omega : 3 * n + 1 ≤ 5 * n) (by omega : 5 * n ≤ 6 * n + 1)]
  rw [sum_Ico_split _ (by omega : 5 * n ≤ 5 * n + 1) (by omega : 5 * n + 1 ≤ 6 * n + 1)]
  have hlo0 : ∑ v ∈ Finset.Ico 0 n, (H n n v : ℚ) * (H n n (6 * n - v) : ℚ) = 0 :=
    Finset.sum_eq_zero fun v hv => by
      simp only [Finset.mem_Ico] at hv
      rw [H_V7 (v := 6 * n - v) (le_refl n) (by omega), mul_zero]
  have hhi0 : ∑ v ∈ Finset.Ico (5 * n + 1) (6 * n + 1), (H n n v : ℚ) * (H n n (6 * n - v) : ℚ) = 0 :=
    Finset.sum_eq_zero fun v hv => by
      simp only [Finset.mem_Ico] at hv
      rw [H_V7 (v := v) (le_refl n) (by omega), zero_mul]
  have hsym := sum_Ico_sym_H n n (n + 1) (3 * n) (by omega) (by omega)
  have hsym' : 6 * n + 1 - 3 * n = 3 * n + 1 ∧ 6 * n + 1 - (n + 1) = 5 * n := by omega
  rw [hsym'.1, hsym'.2] at hsym
  rw [hlo0, hhi0, hsym]
  have hpt1 : ∑ v ∈ Finset.Ico n (n + 1), (H n n v : ℚ) * (H n n (6 * n - v) : ℚ) =
      H1p n * H5p n n (5 * (n : ℚ)) 0 := by
    rw [Finset.sum_Ico_succ_top (le_refl _), Finset.Ico_self, Finset.sum_empty, zero_add]
    rw [H_V1 (le_refl n) hn (le_refl n), H_V5 (le_refl n) (by omega) (by omega)]
    have hm : (n + (6 * n - n)) % 2 = 0 := by omega
    have hsub : 6 * n - n = 5 * n := by omega
    rw [hm, hsub]; push_cast; rfl
  have hpt5 : ∑ v ∈ Finset.Ico (5 * n) (5 * n + 1), (H n n v : ℚ) * (H n n (6 * n - v) : ℚ) =
      H1p n * H5p n n (5 * (n : ℚ)) 0 := by
    rw [Finset.sum_Ico_succ_top (le_refl _), Finset.Ico_self, Finset.sum_empty, zero_add]
    rw [H_V5 (v := 5 * n) (le_refl n) (by omega) (by omega),
        H_V1 (v := 6 * n - 5 * n) (le_refl n) (by omega) (by omega)]
    have hm : (n + 5 * n) % 2 = 0 := by omega
    have hsub : 6 * n - 5 * n = n := by omega
    rw [hm, hsub]; push_cast; exact mul_comm _ _
  have hpt3 : ∑ v ∈ Finset.Ico (3 * n) (3 * n + 1), (H n n v : ℚ) * (H n n (6 * n - v) : ℚ) =
      H3p n n (3 * (n : ℚ)) 0 * H3p n n (3 * (n : ℚ)) 0 := by
    rw [Finset.sum_Ico_succ_top (le_refl _), Finset.Ico_self, Finset.sum_empty, zero_add]
    rw [H_V3 (v := 3 * n) (le_refl n) (by omega) (by omega),
        H_V3 (v := 6 * n - 3 * n) (le_refl n) (by omega) (by omega)]
    have hm1 : (n + 3 * n) % 2 = 0 := by omega
    have hm2 : (n + (6 * n - 3 * n)) % 2 = 0 := by omega
    have hsub : 6 * n - 3 * n = 3 * n := by omega
    rw [hm1, hm2, hsub]; push_cast; rfl
  rw [hpt1, hpt5, hpt3]
  rcases Nat.even_or_odd' n with ⟨q, rfl | rfl⟩
  · have hI35 : ∑ v ∈ Finset.Ico (2 * q + 1) (3 * (2 * q)), (H (2 * q) (2 * q) v : ℚ) *
        (H (2 * q) (2 * q) (6 * (2 * q) - v) : ℚ) =
        (F35 (2 * q) (2 * q) 0 0 (3 * q) - F35 (2 * q) (2 * q) 0 0 (q + 1)) +
        (F35 (2 * q) (2 * q) 1 1 (3 * q) - F35 (2 * q) (2 * q) 1 1 q) := by
      rw [sum_Ico_even_odd _ (by omega)]
      have hb : (2 * q + 1 + 1) / 2 = q + 1 ∧ (3 * (2 * q) + 1) / 2 = 3 * q ∧
          (2 * q + 1) / 2 = q ∧ (3 * (2 * q)) / 2 = 3 * q := by omega
      rw [hb.1, hb.2.1, hb.2.2.1, hb.2.2.2]
      congr 1
      · trans ∑ k ∈ Finset.Ico (q + 1) (3 * q),
            H3p (2 * q) (2 * q) (2 * (k : ℚ) + 0) 0 * H5p (2 * q) (2 * q) (6 * (2 * q) - (2 * (k : ℚ) + 0)) 0
        · refine Finset.sum_congr rfl fun k hk => ?_
          simp only [Finset.mem_Ico] at hk
          rw [H_V3 (v := 2 * k) (le_refl _) (by omega) (by omega),
              H_V5 (v := 6 * (2 * q) - 2 * k) (le_refl _) (by omega) (by omega)]
          have hp1 : (2 * q + 2 * k) % 2 = 0 := by omega
          have hp2 : (2 * q + (6 * (2 * q) - 2 * k)) % 2 = 0 := by omega
          rw [hp1, hp2, Nat.cast_sub (by omega)]; push_cast; simp only [add_zero]
        · rw [sum_Ico_P35 (2 * q) (2 * q) 0 0 (by omega : q + 1 ≤ 3 * q)]; push_cast; rfl
      · trans ∑ k ∈ Finset.Ico q (3 * q),
            H3p (2 * q) (2 * q) (2 * (k : ℚ) + 1) 1 * H5p (2 * q) (2 * q) (6 * (2 * q) - (2 * (k : ℚ) + 1)) 1
        · refine Finset.sum_congr rfl fun k hk => ?_
          simp only [Finset.mem_Ico] at hk
          rw [H_V3 (v := 2 * k + 1) (le_refl _) (by omega) (by omega),
              H_V5 (v := 6 * (2 * q) - (2 * k + 1)) (le_refl _) (by omega) (by omega)]
          have hp1 : (2 * q + (2 * k + 1)) % 2 = 1 := by omega
          have hp2 : (2 * q + (6 * (2 * q) - (2 * k + 1))) % 2 = 1 := by omega
          rw [hp1, hp2, Nat.cast_sub (by omega)]; push_cast; rfl
        · rw [sum_Ico_P35 (2 * q) (2 * q) 1 1 (by omega : q ≤ 3 * q)]; push_cast; rfl
    rw [hI35]; unfold H1p H3p H5p F35; push_cast; ring
  · have hI35 : ∑ v ∈ Finset.Ico (2 * q + 1 + 1) (3 * (2 * q + 1)), (H (2 * q + 1) (2 * q + 1) v : ℚ) *
        (H (2 * q + 1) (2 * q + 1) (6 * (2 * q + 1) - v) : ℚ) =
        (F35 (2 * q + 1) (2 * q + 1) 1 0 (3 * q + 2) - F35 (2 * q + 1) (2 * q + 1) 1 0 (q + 1)) +
        (F35 (2 * q + 1) (2 * q + 1) 0 1 (3 * q + 1) - F35 (2 * q + 1) (2 * q + 1) 0 1 (q + 1)) := by
      rw [sum_Ico_even_odd _ (by omega)]
      have hb : (2 * q + 1 + 1 + 1) / 2 = q + 1 ∧ (3 * (2 * q + 1) + 1) / 2 = 3 * q + 2 ∧
          (2 * q + 1 + 1) / 2 = q + 1 ∧ (3 * (2 * q + 1)) / 2 = 3 * q + 1 := by omega
      rw [hb.1, hb.2.1, hb.2.2.1, hb.2.2.2]
      congr 1
      · trans ∑ k ∈ Finset.Ico (q + 1) (3 * q + 2),
            H3p (2 * q + 1) (2 * q + 1) (2 * (k : ℚ) + 0) 1 * H5p (2 * q + 1) (2 * q + 1) (6 * (2 * q + 1) - (2 * (k : ℚ) + 0)) 1
        · refine Finset.sum_congr rfl fun k hk => ?_
          simp only [Finset.mem_Ico] at hk
          rw [H_V3 (v := 2 * k) (le_refl _) (by omega) (by omega),
              H_V5 (v := 6 * (2 * q + 1) - 2 * k) (le_refl _) (by omega) (by omega)]
          have hp1 : (2 * q + 1 + 2 * k) % 2 = 1 := by omega
          have hp2 : (2 * q + 1 + (6 * (2 * q + 1) - 2 * k)) % 2 = 1 := by omega
          rw [hp1, hp2, Nat.cast_sub (by omega)]; push_cast; simp only [add_zero]
        · rw [sum_Ico_P35 (2 * q + 1) (2 * q + 1) 1 0 (by omega : q + 1 ≤ 3 * q + 2)]; push_cast; rfl
      · trans ∑ k ∈ Finset.Ico (q + 1) (3 * q + 1),
            H3p (2 * q + 1) (2 * q + 1) (2 * (k : ℚ) + 1) 0 * H5p (2 * q + 1) (2 * q + 1) (6 * (2 * q + 1) - (2 * (k : ℚ) + 1)) 0
        · refine Finset.sum_congr rfl fun k hk => ?_
          simp only [Finset.mem_Ico] at hk
          rw [H_V3 (v := 2 * k + 1) (le_refl _) (by omega) (by omega),
              H_V5 (v := 6 * (2 * q + 1) - (2 * k + 1)) (le_refl _) (by omega) (by omega)]
          have hp1 : (2 * q + 1 + (2 * k + 1)) % 2 = 0 := by omega
          have hp2 : (2 * q + 1 + (6 * (2 * q + 1) - (2 * k + 1))) % 2 = 0 := by omega
          rw [hp1, hp2, Nat.cast_sub (by omega)]; push_cast; rfl
        · rw [sum_Ico_P35 (2 * q + 1) (2 * q + 1) 0 1 (by omega : q + 1 ≤ 3 * q + 1)]; push_cast; rfl
    rw [hI35]; unfold H1p H3p H5p F35; push_cast; ring

private lemma S_interior_split {n m : ℕ} (h1 : 1 ≤ m) (h2 : m < n) :
    S n m =
      2 * (H1p m * H6p n m (6 * (n : ℚ) - m) 0 +
           H2p m (2 * (n : ℚ) - m) 0 * H5p n m (4 * (n : ℚ) + m) 0 +
           H3p n m (2 * (n : ℚ) + m) 0 * H4p n m (4 * (n : ℚ) - m) 0 +
           (∑ v ∈ Finset.Ico (m + 1) (2 * n - m), (H n m v : ℚ) * (H n m (6 * n - v) : ℚ)) +
           (∑ v ∈ Finset.Ico (2 * n - m + 1) (2 * n + m), (H n m v : ℚ) * (H n m (6 * n - v) : ℚ))) +
      ∑ v ∈ Finset.Ico (2 * n + m + 1) (4 * n - m), (H n m v : ℚ) * (H n m (6 * n - v) : ℚ) := by
  unfold S
  rw [← Nat.Ico_zero_eq_range]
  rw [sum_Ico_split _ (by omega : 0 ≤ m) (by omega : m ≤ 6 * n + 1)]
  rw [sum_Ico_split _ (by omega : m ≤ m + 1) (by omega : m + 1 ≤ 6 * n + 1)]
  rw [sum_Ico_split _ (by omega : m + 1 ≤ 2 * n - m) (by omega : 2 * n - m ≤ 6 * n + 1)]
  rw [sum_Ico_split _ (by omega : 2 * n - m ≤ 2 * n - m + 1) (by omega : 2 * n - m + 1 ≤ 6 * n + 1)]
  rw [sum_Ico_split _ (by omega : 2 * n - m + 1 ≤ 2 * n + m) (by omega : 2 * n + m ≤ 6 * n + 1)]
  rw [sum_Ico_split _ (by omega : 2 * n + m ≤ 2 * n + m + 1) (by omega : 2 * n + m + 1 ≤ 6 * n + 1)]
  rw [sum_Ico_split _ (by omega : 2 * n + m + 1 ≤ 4 * n - m) (by omega : 4 * n - m ≤ 6 * n + 1)]
  rw [sum_Ico_split _ (by omega : 4 * n - m ≤ 4 * n - m + 1) (by omega : 4 * n - m + 1 ≤ 6 * n + 1)]
  rw [sum_Ico_split _ (by omega : 4 * n - m + 1 ≤ 4 * n + m) (by omega : 4 * n + m ≤ 6 * n + 1)]
  rw [sum_Ico_split _ (by omega : 4 * n + m ≤ 4 * n + m + 1) (by omega : 4 * n + m + 1 ≤ 6 * n + 1)]
  rw [sum_Ico_split _ (by omega : 4 * n + m + 1 ≤ 6 * n - m) (by omega : 6 * n - m ≤ 6 * n + 1)]
  rw [sum_Ico_split _ (by omega : 6 * n - m ≤ 6 * n - m + 1) (by omega : 6 * n - m + 1 ≤ 6 * n + 1)]
  have hlo0 : ∑ v ∈ Finset.Ico 0 m, (H n m v : ℚ) * (H n m (6 * n - v) : ℚ) = 0 :=
    Finset.sum_eq_zero fun v hv => by
      simp only [Finset.mem_Ico] at hv; rw [H_V7 (v := 6 * n - v) (by omega) (by omega), mul_zero]
  have hhi0 : ∑ v ∈ Finset.Ico (6 * n - m + 1) (6 * n + 1), (H n m v : ℚ) * (H n m (6 * n - v) : ℚ) = 0 :=
    Finset.sum_eq_zero fun v hv => by
      simp only [Finset.mem_Ico] at hv; rw [H_V7 (v := v) (by omega) (by omega), zero_mul]
  have hs1 := sum_Ico_sym_H n m (m + 1) (2 * n - m) (by omega) (by omega)
  have hs1' : 6 * n + 1 - (2 * n - m) = 4 * n + m + 1 ∧ 6 * n + 1 - (m + 1) = 6 * n - m := by omega
  rw [hs1'.1, hs1'.2] at hs1
  have hs2 := sum_Ico_sym_H n m (2 * n - m + 1) (2 * n + m) (by omega) (by omega)
  have hs2' : 6 * n + 1 - (2 * n + m) = 4 * n - m + 1 ∧ 6 * n + 1 - (2 * n - m + 1) = 4 * n + m := by omega
  rw [hs2'.1, hs2'.2] at hs2
  have hb1 : ∑ v ∈ Finset.Ico m (m + 1), (H n m v : ℚ) * (H n m (6 * n - v) : ℚ) =
      H1p m * H6p n m (6 * (n : ℚ) - m) 0 := by
    rw [Finset.sum_Ico_succ_top (le_refl _), Finset.Ico_self, Finset.sum_empty, zero_add]
    rw [H_V1 (v := m) (by omega) h1 (le_refl m), H_V6 (v := 6 * n - m) (by omega) (by omega) (by omega)]
    have hm : (m + (6 * n - m)) % 2 = 0 := by omega
    rw [hm, Nat.cast_sub (by omega)]; push_cast; rfl
  have hb1' : ∑ v ∈ Finset.Ico (6 * n - m) (6 * n - m + 1), (H n m v : ℚ) * (H n m (6 * n - v) : ℚ) =
      H1p m * H6p n m (6 * (n : ℚ) - m) 0 := by
    rw [Finset.sum_Ico_succ_top (le_refl _), Finset.Ico_self, Finset.sum_empty, zero_add]
    rw [H_V6 (v := 6 * n - m) (by omega) (by omega) (by omega),
        H_V1 (v := 6 * n - (6 * n - m)) (by omega) (by omega) (by omega)]
    have hm : (m + (6 * n - m)) % 2 = 0 := by omega
    have hsub : 6 * n - (6 * n - m) = m := by omega
    rw [hm, hsub, Nat.cast_sub (by omega)]; push_cast; exact mul_comm _ _
  have hb2 : ∑ v ∈ Finset.Ico (2 * n - m) (2 * n - m + 1), (H n m v : ℚ) * (H n m (6 * n - v) : ℚ) =
      H2p m (2 * (n : ℚ) - m) 0 * H5p n m (4 * (n : ℚ) + m) 0 := by
    rw [Finset.sum_Ico_succ_top (le_refl _), Finset.Ico_self, Finset.sum_empty, zero_add]
    rw [H_V2 (v := 2 * n - m) (by omega) (by omega) (by omega),
        H_V5 (v := 6 * n - (2 * n - m)) (by omega) (by omega) (by omega)]
    have hm1 : (m + (2 * n - m)) % 2 = 0 := by omega
    have hm2 : (m + (6 * n - (2 * n - m))) % 2 = 0 := by omega
    have hsub : 6 * n - (2 * n - m) = 4 * n + m := by omega
    rw [hm1, hm2, hsub, Nat.cast_sub (by omega)]; push_cast; rfl
  have hb2' : ∑ v ∈ Finset.Ico (4 * n + m) (4 * n + m + 1), (H n m v : ℚ) * (H n m (6 * n - v) : ℚ) =
      H2p m (2 * (n : ℚ) - m) 0 * H5p n m (4 * (n : ℚ) + m) 0 := by
    rw [Finset.sum_Ico_succ_top (le_refl _), Finset.Ico_self, Finset.sum_empty, zero_add]
    rw [H_V5 (v := 4 * n + m) (by omega) (by omega) (by omega),
        H_V2 (v := 6 * n - (4 * n + m)) (by omega) (by omega) (by omega)]
    have hm1 : (m + (4 * n + m)) % 2 = 0 := by omega
    have hm2 : (m + (6 * n - (4 * n + m))) % 2 = 0 := by omega
    have hsub : 6 * n - (4 * n + m) = 2 * n - m := by omega
    rw [hm1, hm2, hsub, Nat.cast_sub (by omega)]; push_cast; exact mul_comm _ _
  have hb3 : ∑ v ∈ Finset.Ico (2 * n + m) (2 * n + m + 1), (H n m v : ℚ) * (H n m (6 * n - v) : ℚ) =
      H3p n m (2 * (n : ℚ) + m) 0 * H4p n m (4 * (n : ℚ) - m) 0 := by
    rw [Finset.sum_Ico_succ_top (le_refl _), Finset.Ico_self, Finset.sum_empty, zero_add]
    rw [H_V3 (v := 2 * n + m) (by omega) (by omega) (by omega),
        H_V4 (v := 6 * n - (2 * n + m)) (by omega) (by omega) (by omega)]
    have hm1 : (m + (2 * n + m)) % 2 = 0 := by omega
    have hm2 : (m + (6 * n - (2 * n + m))) % 2 = 0 := by omega
    have hsub : 6 * n - (2 * n + m) = 4 * n - m := by omega
    rw [hm1, hm2, hsub, Nat.cast_sub (by omega)]; push_cast; rfl
  have hb3' : ∑ v ∈ Finset.Ico (4 * n - m) (4 * n - m + 1), (H n m v : ℚ) * (H n m (6 * n - v) : ℚ) =
      H3p n m (2 * (n : ℚ) + m) 0 * H4p n m (4 * (n : ℚ) - m) 0 := by
    rw [Finset.sum_Ico_succ_top (le_refl _), Finset.Ico_self, Finset.sum_empty, zero_add]
    rw [H_V4 (v := 4 * n - m) (by omega) (by omega) (by omega),
        H_V3 (v := 6 * n - (4 * n - m)) (by omega) (by omega) (by omega)]
    have hm1 : (m + (4 * n - m)) % 2 = 0 := by omega
    have hm2 : (m + (6 * n - (4 * n - m))) % 2 = 0 := by omega
    have hsub : 6 * n - (4 * n - m) = 2 * n + m := by omega
    rw [hm1, hm2, hsub, Nat.cast_sub (by omega)]; push_cast; exact mul_comm _ _
  rw [hlo0, hhi0, hs1, hs2, hb1, hb1', hb2, hb2', hb3, hb3']
  ring

private def SevenPoly (n a : ℚ) : ℚ :=
  -8 * a ^ 5 / 5 - 20 * a ^ 4 * n - 6 * a ^ 4 + 52 * a ^ 3 * n ^ 2 / 3 + 316 * a ^ 3 * n / 3 -
    88 * a ^ 3 / 3 + 82 * a ^ 2 * n ^ 3 / 3 - 21 * a ^ 2 * n ^ 2 - 88 * a ^ 2 * n / 3 + 3 * a ^ 2 / 2 -
    179 * a * n ^ 4 / 6 - 55 * a * n ^ 3 + 8 * a * n ^ 2 + 301 * a * n / 6 - 497 * a / 30 +
    125 * n ^ 5 / 12 + 983 * n ^ 4 / 24 + 57 * n ^ 3 + 1285 * n ^ 2 / 24 - 71 * n / 12 + 5

private def SoddPoly (n a : ℚ) : ℚ :=
  -8 * a ^ 5 / 5 - 20 * a ^ 4 * n - 10 * a ^ 4 + 52 * a ^ 3 * n ^ 2 / 3 + 196 * a ^ 3 * n / 3 -
    136 * a ^ 3 / 3 + 82 * a ^ 2 * n ^ 3 / 3 + 5 * a ^ 2 * n ^ 2 + 296 * a ^ 2 * n / 3 - 107 * a ^ 2 / 2 -
    179 * a * n ^ 4 / 6 - 83 * a * n ^ 3 / 3 + 539 * a * n / 6 - 1217 * a / 30 +
    125 * n ^ 5 / 12 + 625 * n ^ 4 / 24 + 109 * n ^ 3 / 3 + 1307 * n ^ 2 / 24 + 95 * n / 4 - 7

private lemma S_even_eq {n a : ℕ} (ha1 : 1 ≤ a) (ha2 : 2 * a < n) :
    S n (2 * a) = SevenPoly n a := by
  rw [S_interior_split (by omega) ha2]
  have hI26 : ∑ v ∈ Finset.Ico (2 * a + 1) (2 * n - 2 * a), (H n (2 * a) v : ℚ) * (H n (2 * a) (6 * n - v) : ℚ) =
      (F26 (2 * a) 0 0 (n - a) - F26 (2 * a) 0 0 (a + 1)) +
      (F26 (2 * a) 1 1 (n - a) - F26 (2 * a) 1 1 a) := by
    rw [sum_Ico_even_odd _ (by omega)]
    have hb : (2 * a + 1 + 1) / 2 = a + 1 ∧ (2 * n - 2 * a + 1) / 2 = n - a ∧
        (2 * a + 1) / 2 = a ∧ (2 * n - 2 * a) / 2 = n - a := by omega
    rw [hb.1, hb.2.1, hb.2.2.1, hb.2.2.2]
    congr 1
    · trans ∑ k ∈ Finset.Ico (a + 1) (n - a),
          H2p (2 * a) (2 * (k : ℚ) + 0) 0 * H6p n (2 * a) (6 * n - (2 * (k : ℚ) + 0)) 0
      · refine Finset.sum_congr rfl fun k hk => ?_
        simp only [Finset.mem_Ico] at hk
        rw [H_V2 (v := 2 * k) (by omega) (by omega) (by omega),
            H_V6 (v := 6 * n - 2 * k) (by omega) (by omega) (by omega)]
        have hp1 : (2 * a + 2 * k) % 2 = 0 := by omega
        have hp2 : (2 * a + (6 * n - 2 * k)) % 2 = 0 := by omega
        rw [hp1, hp2, Nat.cast_sub (by omega)]; push_cast; simp only [add_zero]
      · rw [sum_Ico_P26 n (2 * a) 0 0 (by omega : a + 1 ≤ n - a), Nat.cast_sub (by omega)]; push_cast; rfl
    · trans ∑ k ∈ Finset.Ico a (n - a),
          H2p (2 * a) (2 * (k : ℚ) + 1) 1 * H6p n (2 * a) (6 * n - (2 * (k : ℚ) + 1)) 1
      · refine Finset.sum_congr rfl fun k hk => ?_
        simp only [Finset.mem_Ico] at hk
        rw [H_V2 (v := 2 * k + 1) (by omega) (by omega) (by omega),
            H_V6 (v := 6 * n - (2 * k + 1)) (by omega) (by omega) (by omega)]
        have hp1 : (2 * a + (2 * k + 1)) % 2 = 1 := by omega
        have hp2 : (2 * a + (6 * n - (2 * k + 1))) % 2 = 1 := by omega
        rw [hp1, hp2, Nat.cast_sub (by omega)]; push_cast; rfl
      · rw [sum_Ico_P26 n (2 * a) 1 1 (by omega : a ≤ n - a), Nat.cast_sub (by omega)]
  have hI35 : ∑ v ∈ Finset.Ico (2 * n - 2 * a + 1) (2 * n + 2 * a), (H n (2 * a) v : ℚ) * (H n (2 * a) (6 * n - v) : ℚ) =
      (F35 n (2 * a) 0 0 (n + a) - F35 n (2 * a) 0 0 (n - a + 1)) +
      (F35 n (2 * a) 1 1 (n + a) - F35 n (2 * a) 1 1 (n - a)) := by
    rw [sum_Ico_even_odd _ (by omega)]
    have hb : (2 * n - 2 * a + 1 + 1) / 2 = n - a + 1 ∧ (2 * n + 2 * a + 1) / 2 = n + a ∧
        (2 * n - 2 * a + 1) / 2 = n - a ∧ (2 * n + 2 * a) / 2 = n + a := by omega
    rw [hb.1, hb.2.1, hb.2.2.1, hb.2.2.2]
    congr 1
    · trans ∑ k ∈ Finset.Ico (n - a + 1) (n + a),
          H3p n (2 * a) (2 * (k : ℚ) + 0) 0 * H5p n (2 * a) (6 * n - (2 * (k : ℚ) + 0)) 0
      · refine Finset.sum_congr rfl fun k hk => ?_
        simp only [Finset.mem_Ico] at hk
        rw [H_V3 (v := 2 * k) (by omega) (by omega) (by omega),
            H_V5 (v := 6 * n - 2 * k) (by omega) (by omega) (by omega)]
        have hp1 : (2 * a + 2 * k) % 2 = 0 := by omega
        have hp2 : (2 * a + (6 * n - 2 * k)) % 2 = 0 := by omega
        rw [hp1, hp2, Nat.cast_sub (by omega)]; push_cast; simp only [add_zero]
      · rw [sum_Ico_P35 n (2 * a) 0 0 (by omega : n - a + 1 ≤ n + a)]
        push_cast [Nat.cast_sub (by omega : a ≤ n)]; rfl
    · trans ∑ k ∈ Finset.Ico (n - a) (n + a),
          H3p n (2 * a) (2 * (k : ℚ) + 1) 1 * H5p n (2 * a) (6 * n - (2 * (k : ℚ) + 1)) 1
      · refine Finset.sum_congr rfl fun k hk => ?_
        simp only [Finset.mem_Ico] at hk
        rw [H_V3 (v := 2 * k + 1) (by omega) (by omega) (by omega),
            H_V5 (v := 6 * n - (2 * k + 1)) (by omega) (by omega) (by omega)]
        have hp1 : (2 * a + (2 * k + 1)) % 2 = 1 := by omega
        have hp2 : (2 * a + (6 * n - (2 * k + 1))) % 2 = 1 := by omega
        rw [hp1, hp2, Nat.cast_sub (by omega)]; push_cast; rfl
      · rw [sum_Ico_P35 n (2 * a) 1 1 (by omega : n - a ≤ n + a), Nat.cast_sub (by omega)]; push_cast; rfl
  have hI44 : ∑ v ∈ Finset.Ico (2 * n + 2 * a + 1) (4 * n - 2 * a), (H n (2 * a) v : ℚ) * (H n (2 * a) (6 * n - v) : ℚ) =
      (F44 n (2 * a) 0 0 (2 * n - a) - F44 n (2 * a) 0 0 (n + a + 1)) +
      (F44 n (2 * a) 1 1 (2 * n - a) - F44 n (2 * a) 1 1 (n + a)) := by
    rw [sum_Ico_even_odd _ (by omega)]
    have hb : (2 * n + 2 * a + 1 + 1) / 2 = n + a + 1 ∧ (4 * n - 2 * a + 1) / 2 = 2 * n - a ∧
        (2 * n + 2 * a + 1) / 2 = n + a ∧ (4 * n - 2 * a) / 2 = 2 * n - a := by omega
    rw [hb.1, hb.2.1, hb.2.2.1, hb.2.2.2]
    congr 1
    · trans ∑ k ∈ Finset.Ico (n + a + 1) (2 * n - a),
          H4p n (2 * a) (2 * (k : ℚ) + 0) 0 * H4p n (2 * a) (6 * n - (2 * (k : ℚ) + 0)) 0
      · refine Finset.sum_congr rfl fun k hk => ?_
        simp only [Finset.mem_Ico] at hk
        rw [H_V4 (v := 2 * k) (by omega) (by omega) (by omega),
            H_V4 (v := 6 * n - 2 * k) (by omega) (by omega) (by omega)]
        have hp1 : (2 * a + 2 * k) % 2 = 0 := by omega
        have hp2 : (2 * a + (6 * n - 2 * k)) % 2 = 0 := by omega
        rw [hp1, hp2, Nat.cast_sub (by omega)]; push_cast; simp only [add_zero]
      · rw [sum_Ico_P44 n (2 * a) 0 0 (by omega : n + a + 1 ≤ 2 * n - a), Nat.cast_sub (by omega)]; push_cast; rfl
    · trans ∑ k ∈ Finset.Ico (n + a) (2 * n - a),
          H4p n (2 * a) (2 * (k : ℚ) + 1) 1 * H4p n (2 * a) (6 * n - (2 * (k : ℚ) + 1)) 1
      · refine Finset.sum_congr rfl fun k hk => ?_
        simp only [Finset.mem_Ico] at hk
        rw [H_V4 (v := 2 * k + 1) (by omega) (by omega) (by omega),
            H_V4 (v := 6 * n - (2 * k + 1)) (by omega) (by omega) (by omega)]
        have hp1 : (2 * a + (2 * k + 1)) % 2 = 1 := by omega
        have hp2 : (2 * a + (6 * n - (2 * k + 1))) % 2 = 1 := by omega
        rw [hp1, hp2, Nat.cast_sub (by omega)]; push_cast; rfl
      · rw [sum_Ico_P44 n (2 * a) 1 1 (by omega : n + a ≤ 2 * n - a), Nat.cast_sub (by omega)]; push_cast; rfl
  rw [hI26, hI35, hI44]
  unfold H1p H2p H3p H4p H5p H6p F26 F35 F44 SevenPoly
  push_cast
  ring

private lemma S_odd_eq {n a : ℕ} (ha2 : 2 * a + 1 < n) :
    S n (2 * a + 1) = SoddPoly n a := by
  rw [S_interior_split (by omega) ha2]
  have hI26 : ∑ v ∈ Finset.Ico (2 * a + 1 + 1) (2 * n - (2 * a + 1)),
        (H n (2 * a + 1) v : ℚ) * (H n (2 * a + 1) (6 * n - v) : ℚ) =
      (F26 (2 * a + 1) 1 0 (n - a) - F26 (2 * a + 1) 1 0 (a + 1)) +
      (F26 (2 * a + 1) 0 1 (n - a - 1) - F26 (2 * a + 1) 0 1 (a + 1)) := by
    rw [sum_Ico_even_odd _ (by omega)]
    have hb : (2 * a + 1 + 1 + 1) / 2 = a + 1 ∧ (2 * n - (2 * a + 1) + 1) / 2 = n - a ∧
        (2 * a + 1 + 1) / 2 = a + 1 ∧ (2 * n - (2 * a + 1)) / 2 = n - a - 1 := by omega
    rw [hb.1, hb.2.1, hb.2.2.1, hb.2.2.2]
    congr 1
    · trans ∑ k ∈ Finset.Ico (a + 1) (n - a),
          H2p (2 * a + 1) (2 * (k : ℚ) + 0) 1 * H6p n (2 * a + 1) (6 * n - (2 * (k : ℚ) + 0)) 1
      · refine Finset.sum_congr rfl fun k hk => ?_
        simp only [Finset.mem_Ico] at hk
        rw [H_V2 (v := 2 * k) (by omega) (by omega) (by omega),
            H_V6 (v := 6 * n - 2 * k) (by omega) (by omega) (by omega)]
        have hp1 : (2 * a + 1 + 2 * k) % 2 = 1 := by omega
        have hp2 : (2 * a + 1 + (6 * n - 2 * k)) % 2 = 1 := by omega
        rw [hp1, hp2, Nat.cast_sub (by omega)]; push_cast; simp only [add_zero]
      · rw [sum_Ico_P26 n (2 * a + 1) 1 0 (by omega : a + 1 ≤ n - a), Nat.cast_sub (by omega)]; push_cast; rfl
    · trans ∑ k ∈ Finset.Ico (a + 1) (n - a - 1),
          H2p (2 * a + 1) (2 * (k : ℚ) + 1) 0 * H6p n (2 * a + 1) (6 * n - (2 * (k : ℚ) + 1)) 0
      · refine Finset.sum_congr rfl fun k hk => ?_
        simp only [Finset.mem_Ico] at hk
        rw [H_V2 (v := 2 * k + 1) (by omega) (by omega) (by omega),
            H_V6 (v := 6 * n - (2 * k + 1)) (by omega) (by omega) (by omega)]
        have hp1 : (2 * a + 1 + (2 * k + 1)) % 2 = 0 := by omega
        have hp2 : (2 * a + 1 + (6 * n - (2 * k + 1))) % 2 = 0 := by omega
        rw [hp1, hp2, Nat.cast_sub (by omega)]; push_cast; rfl
      · rw [sum_Ico_P26 n (2 * a + 1) 0 1 (by omega : a + 1 ≤ n - a - 1),
            Nat.cast_sub (by omega : 1 ≤ n - a), Nat.cast_sub (by omega : a ≤ n)]; push_cast; rfl
  have hI35 : ∑ v ∈ Finset.Ico (2 * n - (2 * a + 1) + 1) (2 * n + (2 * a + 1)),
        (H n (2 * a + 1) v : ℚ) * (H n (2 * a + 1) (6 * n - v) : ℚ) =
      (F35 n (2 * a + 1) 1 0 (n + a + 1) - F35 n (2 * a + 1) 1 0 (n - a)) +
      (F35 n (2 * a + 1) 0 1 (n + a) - F35 n (2 * a + 1) 0 1 (n - a)) := by
    rw [sum_Ico_even_odd _ (by omega)]
    have hb : (2 * n - (2 * a + 1) + 1 + 1) / 2 = n - a ∧ (2 * n + (2 * a + 1) + 1) / 2 = n + a + 1 ∧
        (2 * n - (2 * a + 1) + 1) / 2 = n - a ∧ (2 * n + (2 * a + 1)) / 2 = n + a := by omega
    rw [hb.1, hb.2.1, hb.2.2.1, hb.2.2.2]
    congr 1
    · trans ∑ k ∈ Finset.Ico (n - a) (n + a + 1),
          H3p n (2 * a + 1) (2 * (k : ℚ) + 0) 1 * H5p n (2 * a + 1) (6 * n - (2 * (k : ℚ) + 0)) 1
      · refine Finset.sum_congr rfl fun k hk => ?_
        simp only [Finset.mem_Ico] at hk
        rw [H_V3 (v := 2 * k) (by omega) (by omega) (by omega),
            H_V5 (v := 6 * n - 2 * k) (by omega) (by omega) (by omega)]
        have hp1 : (2 * a + 1 + 2 * k) % 2 = 1 := by omega
        have hp2 : (2 * a + 1 + (6 * n - 2 * k)) % 2 = 1 := by omega
        rw [hp1, hp2, Nat.cast_sub (by omega)]; push_cast; simp only [add_zero]
      · rw [sum_Ico_P35 n (2 * a + 1) 1 0 (by omega : n - a ≤ n + a + 1), Nat.cast_sub (by omega)]; push_cast; rfl
    · trans ∑ k ∈ Finset.Ico (n - a) (n + a),
          H3p n (2 * a + 1) (2 * (k : ℚ) + 1) 0 * H5p n (2 * a + 1) (6 * n - (2 * (k : ℚ) + 1)) 0
      · refine Finset.sum_congr rfl fun k hk => ?_
        simp only [Finset.mem_Ico] at hk
        rw [H_V3 (v := 2 * k + 1) (by omega) (by omega) (by omega),
            H_V5 (v := 6 * n - (2 * k + 1)) (by omega) (by omega) (by omega)]
        have hp1 : (2 * a + 1 + (2 * k + 1)) % 2 = 0 := by omega
        have hp2 : (2 * a + 1 + (6 * n - (2 * k + 1))) % 2 = 0 := by omega
        rw [hp1, hp2, Nat.cast_sub (by omega)]; push_cast; rfl
      · rw [sum_Ico_P35 n (2 * a + 1) 0 1 (by omega : n - a ≤ n + a), Nat.cast_sub (by omega)]; push_cast; rfl
  have hI44 : ∑ v ∈ Finset.Ico (2 * n + (2 * a + 1) + 1) (4 * n - (2 * a + 1)),
        (H n (2 * a + 1) v : ℚ) * (H n (2 * a + 1) (6 * n - v) : ℚ) =
      (F44 n (2 * a + 1) 1 0 (2 * n - a) - F44 n (2 * a + 1) 1 0 (n + a + 1)) +
      (F44 n (2 * a + 1) 0 1 (2 * n - a - 1) - F44 n (2 * a + 1) 0 1 (n + a + 1)) := by
    rw [sum_Ico_even_odd _ (by omega)]
    have hb : (2 * n + (2 * a + 1) + 1 + 1) / 2 = n + a + 1 ∧ (4 * n - (2 * a + 1) + 1) / 2 = 2 * n - a ∧
        (2 * n + (2 * a + 1) + 1) / 2 = n + a + 1 ∧ (4 * n - (2 * a + 1)) / 2 = 2 * n - a - 1 := by omega
    rw [hb.1, hb.2.1, hb.2.2.1, hb.2.2.2]
    congr 1
    · trans ∑ k ∈ Finset.Ico (n + a + 1) (2 * n - a),
          H4p n (2 * a + 1) (2 * (k : ℚ) + 0) 1 * H4p n (2 * a + 1) (6 * n - (2 * (k : ℚ) + 0)) 1
      · refine Finset.sum_congr rfl fun k hk => ?_
        simp only [Finset.mem_Ico] at hk
        rw [H_V4 (v := 2 * k) (by omega) (by omega) (by omega),
            H_V4 (v := 6 * n - 2 * k) (by omega) (by omega) (by omega)]
        have hp1 : (2 * a + 1 + 2 * k) % 2 = 1 := by omega
        have hp2 : (2 * a + 1 + (6 * n - 2 * k)) % 2 = 1 := by omega
        rw [hp1, hp2, Nat.cast_sub (by omega)]; push_cast; simp only [add_zero]
      · rw [sum_Ico_P44 n (2 * a + 1) 1 0 (by omega : n + a + 1 ≤ 2 * n - a), Nat.cast_sub (by omega)]; push_cast; rfl
    · trans ∑ k ∈ Finset.Ico (n + a + 1) (2 * n - a - 1),
          H4p n (2 * a + 1) (2 * (k : ℚ) + 1) 0 * H4p n (2 * a + 1) (6 * n - (2 * (k : ℚ) + 1)) 0
      · refine Finset.sum_congr rfl fun k hk => ?_
        simp only [Finset.mem_Ico] at hk
        rw [H_V4 (v := 2 * k + 1) (by omega) (by omega) (by omega),
            H_V4 (v := 6 * n - (2 * k + 1)) (by omega) (by omega) (by omega)]
        have hp1 : (2 * a + 1 + (2 * k + 1)) % 2 = 0 := by omega
        have hp2 : (2 * a + 1 + (6 * n - (2 * k + 1))) % 2 = 0 := by omega
        rw [hp1, hp2, Nat.cast_sub (by omega)]; push_cast; rfl
      · rw [sum_Ico_P44 n (2 * a + 1) 0 1 (by omega : n + a + 1 ≤ 2 * n - a - 1),
            Nat.cast_sub (by omega : 1 ≤ 2 * n - a), Nat.cast_sub (by omega : a ≤ 2 * n)]; push_cast; rfl
  rw [hI26, hI35, hI44]
  unfold H1p H2p H3p H4p H5p H6p F26 F35 F44 SoddPoly
  push_cast
  ring

/-! ### Outer sum over m and closed form for a(n) -/

private def Feven (n a : ℚ) : ℚ :=
  (-96 * a ^ 6 + (-1440 * n - 144) * a ^ 5 + (1560 * n ^ 2 + 13080 * n - 1800) * a ^ 4 +
    (3280 * n ^ 3 - 5640 * n ^ 2 - 24880 * n + 4740) * a ^ 3 +
    (-5370 * n ^ 4 - 14820 * n ^ 3 + 6780 * n ^ 2 + 23790 * n - 5844) * a ^ 2 +
    (3750 * n ^ 5 + 20115 * n ^ 4 + 32060 * n ^ 3 + 16575 * n ^ 2 - 12680 * n + 4944) * a) / 360

private def Fodd (n a : ℚ) : ℚ :=
  (-96 * a ^ 6 + (-1440 * n - 432) * a ^ 5 + (1560 * n ^ 2 + 9480 * n - 2520) * a ^ 4 +
    (3280 * n ^ 3 - 2520 * n ^ 2 - 2320 * n + 540) * a ^ 3 +
    (-5370 * n ^ 4 - 9900 * n ^ 3 + 660 * n ^ 2 + 4290 * n - 1704) * a ^ 2 +
    (3750 * n ^ 5 + 14745 * n ^ 4 + 19700 * n ^ 3 + 19905 * n ^ 2 - 1460 * n + 1692) * a) / 360

private lemma sum_Ico_Seven (n : ℚ) {a b : ℕ} (h : a ≤ b) :
    ∑ k ∈ Finset.Ico a b, SevenPoly n k = Feven n b - Feven n a :=
  sum_Ico_telescope h _ (fun k => Feven n k) (fun k => by unfold SevenPoly Feven; push_cast; ring)

private lemma sum_Ico_Sodd (n : ℚ) {a b : ℕ} (h : a ≤ b) :
    ∑ k ∈ Finset.Ico a b, SoddPoly n k = Fodd n b - Fodd n a :=
  sum_Ico_telescope h _ (fun k => Fodd n k) (fun k => by unfold SoddPoly Fodd; push_cast; ring)

private def aPoly (n : ℚ) : ℚ :=
  n * (1987 * n ^ 5 + 12198 * n ^ 4 + 27850 * n ^ 3 + 40680 * n ^ 2 - 3017 * n + 4182) / 180

private lemma a_closed_form {n : ℕ} (hn : 1 ≤ n) : (a n : ℚ) = aPoly n := by
  have ha : (a n : ℚ) = ∑ m ∈ Finset.range (2 * n + 1), S n m := by
    rw [a_eq_sum_H]
    push_cast
    rfl
  rw [ha, ← Nat.Ico_zero_eq_range]
  rw [sum_Ico_split _ (Nat.zero_le n) (by omega : n ≤ 2 * n + 1)]
  rw [sum_Ico_split _ (by omega : n ≤ n + 1) (by omega : n + 1 ≤ 2 * n + 1)]
  have hsym : ∑ m ∈ Finset.Ico (n + 1) (2 * n + 1), S n m = ∑ m ∈ Finset.Ico 0 n, S n m := by
    refine Finset.sum_bij (fun m _ => 2 * n - m) ?_ ?_ ?_ ?_
    · intro m hm; simp only [Finset.mem_Ico] at hm ⊢; omega
    · intro m1 hm1 m2 hm2 h; simp only [Finset.mem_Ico] at hm1 hm2; omega
    · intro m hm; simp only [Finset.mem_Ico] at hm; exact ⟨2 * n - m, by simp; omega, by omega⟩
    · intro m hm
      simp only [Finset.mem_Ico] at hm
      have h1 := S_reflect (n := n) (m := 2 * n - m) (by omega)
      have h2 : 2 * n - (2 * n - m) = m := by omega
      rw [h2] at h1
      exact h1
  have hmid : ∑ m ∈ Finset.Ico n (n + 1), S n m = S n n := by
    rw [Finset.sum_Ico_succ_top (le_refl n), Finset.Ico_self, Finset.sum_empty, zero_add]
  rw [hsym, hmid]
  rw [sum_Ico_split _ (by omega : 0 ≤ 1) hn]
  have h0 : ∑ m ∈ Finset.Ico 0 1, S n m = S n 0 := by
    rw [Finset.sum_Ico_succ_top (le_refl 0), Finset.Ico_self, Finset.sum_empty, zero_add]
  rw [h0, S_zero hn, S_diag hn]
  rw [sum_Ico_even_odd (S n) hn]
  have hlo1 : (1 + 1) / 2 = 1 := rfl
  have hlo2 : 1 / 2 = 0 := rfl
  rw [hlo1, hlo2]
  have hev : ∑ k ∈ Finset.Ico 1 ((n + 1) / 2), S n (2 * k) =
      Feven n ((n + 1) / 2 : ℕ) - Feven n 1 := by
    trans ∑ k ∈ Finset.Ico 1 ((n + 1) / 2), SevenPoly n k
    · refine Finset.sum_congr rfl fun k hk => ?_
      simp only [Finset.mem_Ico] at hk
      exact S_even_eq hk.1 (by omega)
    · rw [sum_Ico_Seven n (by omega : 1 ≤ (n + 1) / 2)]; push_cast; ring
  have hod : ∑ k ∈ Finset.Ico 0 (n / 2), S n (2 * k + 1) =
      Fodd n (n / 2 : ℕ) - Fodd n 0 := by
    trans ∑ k ∈ Finset.Ico 0 (n / 2), SoddPoly n k
    · refine Finset.sum_congr rfl fun k hk => ?_
      simp only [Finset.mem_Ico] at hk
      exact S_odd_eq (by omega)
    · rw [sum_Ico_Sodd n (Nat.zero_le _)]; push_cast; ring
  rw [hev, hod]
  rcases Nat.even_or_odd' n with ⟨q, rfl | rfl⟩
  · have hq1 : (2 * q + 1) / 2 = q := by omega
    have hq2 : (2 * q) / 2 = q := by omega
    rw [hq1, hq2]
    unfold Feven Fodd aPoly
    push_cast
    ring
  · have hq1 : (2 * q + 1 + 1) / 2 = q + 1 := by omega
    have hq2 : (2 * q + 1) / 2 = q := by omega
    rw [hq1, hq2]
    unfold Feven Fodd aPoly
    push_cast
    ring

/-! ### Generating function and recurrence -/

private lemma coeff_eq_aPoly (n : ℕ) : (if n = 0 then (0 : ℚ) else (a n : ℚ)) = aPoly n := by
  by_cases hn : n = 0
  · subst hn; simp [aPoly]
  · rw [if_neg hn]; exact a_closed_form (by omega)

private lemma main_proof :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      2 * X * (233 + 1938 * X + 1444 * X ^ 2 + 309 * X ^ 3 + 134 * X ^ 4 - 84 * X ^ 5) ∧
    ∀ n : ℕ, 7 < n →
      (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4)
        + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  constructor
  · have hmk : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) =
        PowerSeries.mk (fun n => aPoly n) := by
      congr 1; funext n; exact coeff_eq_aPoly n
    rw [hmk]
    have hlhs : (1 - (X : PowerSeries ℚ)) ^ 7 =
        C 1 + C (-7) * X + C 21 * X ^ 2 + C (-35) * X ^ 3 + C 35 * X ^ 4 +
        C (-21) * X ^ 5 + C 7 * X ^ 6 + C (-1) * X ^ 7 := by
      simp only [map_neg, map_ofNat, map_one]
      ring
    have hrhs : (2 * (X : PowerSeries ℚ)) *
        (233 + 1938 * X + 1444 * X ^ 2 + 309 * X ^ 3 + 134 * X ^ 4 - 84 * X ^ 5) =
        C 466 * X + C 3876 * X ^ 2 + C 2888 * X ^ 3 + C 618 * X ^ 4 +
        C 268 * X ^ 5 + C (-168) * X ^ 6 := by
      simp only [map_neg, map_ofNat]
      ring
    rw [hlhs, hrhs]
    have hmul : ∀ (F : PowerSeries ℚ),
        F * (C 1 + C (-7) * X + C 21 * X ^ 2 + C (-35) * X ^ 3 + C 35 * X ^ 4 +
          C (-21) * X ^ 5 + C 7 * X ^ 6 + C (-1) * X ^ 7) =
        F + C (-7) * (X ^ 1 * F) + C 21 * (X ^ 2 * F) + C (-35) * (X ^ 3 * F) +
        C 35 * (X ^ 4 * F) + C (-21) * (X ^ 5 * F) + C 7 * (X ^ 6 * F) +
        C (-1) * (X ^ 7 * F) := by
      intro F; simp only [map_neg, map_ofNat, map_one]; ring
    rw [hmul]
    ext k
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
      PowerSeries.coeff_mk, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
    rcases k with _ | _ | _ | _ | _ | _ | _ | k
    · simp [aPoly]
    · simp [aPoly]; norm_num
    · simp [aPoly]; norm_num
    · simp [aPoly]; norm_num
    · simp [aPoly]; norm_num
    · simp [aPoly]; norm_num
    · simp [aPoly]; norm_num
    · have hadd : k + 1 + 1 + 1 + 1 + 1 + 1 + 1 = k + 7 := by omega
      simp only [hadd]
      have h1 : ¬ (k + 7 = 1) := by omega
      have h2 : ¬ (k + 7 = 2) := by omega
      have h3 : ¬ (k + 7 = 3) := by omega
      have h4 : ¬ (k + 7 = 4) := by omega
      have h5 : ¬ (k + 7 = 5) := by omega
      have h6 : ¬ (k + 7 = 6) := by omega
      have hl1 : 1 ≤ k + 7 := by omega
      have hl2 : 2 ≤ k + 7 := by omega
      have hl3 : 3 ≤ k + 7 := by omega
      have hl4 : 4 ≤ k + 7 := by omega
      have hl5 : 5 ≤ k + 7 := by omega
      have hl6 : 6 ≤ k + 7 := by omega
      have hl7 : 7 ≤ k + 7 := by omega
      simp only [h1, h2, h3, h4, h5, h6, hl1, hl2, hl3, hl4, hl5, hl6, hl7,
        ↓reduceIte, mul_zero, add_zero]
      have hs1 : k + 7 - 1 = k + 6 := by omega
      have hs2 : k + 7 - 2 = k + 5 := by omega
      have hs3 : k + 7 - 3 = k + 4 := by omega
      have hs4 : k + 7 - 4 = k + 3 := by omega
      have hs5 : k + 7 - 5 = k + 2 := by omega
      have hs6 : k + 7 - 6 = k + 1 := by omega
      have hs7 : k + 7 - 7 = k := by omega
      rw [hs1, hs2, hs3, hs4, hs5, hs6, hs7]
      unfold aPoly
      push_cast
      ring
  · intro n hn
    have hq : (a n : ℚ) = 7 * (a (n - 1) : ℚ) - 21 * (a (n - 2) : ℚ) + 35 * (a (n - 3) : ℚ) -
        35 * (a (n - 4) : ℚ) + 21 * (a (n - 5) : ℚ) - 7 * (a (n - 6) : ℚ) + (a (n - 7) : ℚ) := by
      rw [a_closed_form (by omega), a_closed_form (by omega), a_closed_form (by omega),
          a_closed_form (by omega), a_closed_form (by omega), a_closed_form (by omega),
          a_closed_form (by omega), a_closed_form (by omega)]
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n),
          Nat.cast_sub (by omega : 3 ≤ n), Nat.cast_sub (by omega : 4 ≤ n),
          Nat.cast_sub (by omega : 5 ≤ n), Nat.cast_sub (by omega : 6 ≤ n),
          Nat.cast_sub (by omega : 7 ≤ n)]
      unfold aPoly
      push_cast
      ring
    exact_mod_cast hq

end OMA.S_oeis_a249986

theorem OMA.solution : type_of% @OMA.S_oeis_a249986.main :=
  OMA.S_oeis_a249986.main_proof


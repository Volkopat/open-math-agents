import OMAReductions.R_Erdos1087_erdos_1087_R1

/-!
# Proof of `Erdos1087.erdos_1087.R1.H1`

Proves the classical Erdős–Purdy (1971) upper bound `f n = O(n ^ (3 + ε))` for every `ε ≥ 1 / 2`,
by showing `degenerateCount P ≤ 4 * n ^ (7 / 2)` for every `n`-point set `P ⊆ ℝ²`.

1. **Circle–circle intersection**: for any distinct `a ≠ b` in `ℝ²` and any `r₁, r₂ : ℝ`, at most
   two points `c ∈ ℝ²` satisfy `dist a c = r₁ ∧ dist b c = r₂` (eliminating one coordinate gives
   a nondegenerate quadratic in the other).
2. **Equal-distance pairs**: for any fixed distance `r`, double counting ordered triples `(c, a, b)`
   with `dist a c = r = dist b c` and applying Cauchy–Schwarz yields
   `E_r.card ≤ 2 * n ^ (3 / 2)`, hence `∑_r E_r.card ^ 2 ≤ 2 * n ^ (7 / 2)`.
3. **Isosceles triples**: for any distinct apices `a₁ ≠ a₂` and any `b`, at most one `c ≠ b`
   satisfies `dist a₁ c = dist a₁ b ∧ dist a₂ c = dist a₂ b` (since `b` already accounts for one
   of the at most two circle–circle intersection points). Double counting and Cauchy–Schwarz yield
   `I.card ≤ 2 * n ^ (5 / 2)`.
4. **Covering degenerate 4-subsets**: every 4-subset `S ⊆ P` with `distinctDistances S < 6`
   contains either an isosceles triple (plus a 4th point from `P`, at most `I.card * n` sets) or
   two disjoint equal-distance pairs (at most `∑_r E_r.card ^ 2` sets), giving
   `degenerateCount P ≤ 4 * n ^ (7 / 2)` and hence `f n = O(n ^ (3 + ε))` for all `ε ≥ 1 / 2`.
-/

namespace Erdos1087R1H1Proof

open Filter Asymptotics Finset
open scoped EuclideanGeometry

private lemma dist_sq_coords (a b : ℝ²) :
    dist a b ^ 2 = (a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
  simp only [Real.dist_eq, sq_abs]

private lemma quadratic_at_most_two_roots {A B C : ℝ} (hA : A ≠ 0) {S : Finset ℝ}
    (hS : ∀ x ∈ S, A * x ^ 2 + B * x + C = 0) : S.card ≤ 2 := by
  by_contra hgt
  push Not at hgt
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  have hcard_er : 0 < ((S.erase x).erase y).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hxy.symm, hy⟩),
      Finset.card_erase_of_mem hx]
    omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hcard_er
  rw [Finset.mem_erase, Finset.mem_erase] at hz
  obtain ⟨hzy, hzx, hzS⟩ := hz
  have h1 := hS x hx
  have h2 := hS y hy
  have h3 := hS z hzS
  have h12 : (x - y) * (A * (x + y) + B) = 0 := by linarith
  have h13 : (x - z) * (A * (x + z) + B) = 0 := by linarith
  have hxy' : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hxz' : x - z ≠ 0 := sub_ne_zero.mpr hzx.symm
  have hsum1 : A * (x + y) + B = 0 := (mul_eq_zero.mp h12).resolve_left hxy'
  have hsum2 : A * (x + z) + B = 0 := (mul_eq_zero.mp h13).resolve_left hxz'
  have hyz0 : A * (y - z) = 0 := by linarith
  exact hzy.symm (sub_eq_zero.mp ((mul_eq_zero.mp hyz0).resolve_left hA))

private lemma circle_inter_card_le_two {a b : ℝ²} (hab : a ≠ b) (r₁ r₂ : ℝ)
    (S : Finset ℝ²) (hS : ∀ c ∈ S, dist a c = r₁ ∧ dist b c = r₂) : S.card ≤ 2 := by
  classical
  have hdiff_ne : a 0 ≠ b 0 ∨ a 1 ≠ b 1 := by
    by_contra h
    push Not at h
    apply hab
    ext i
    fin_cases i
    · exact h.1
    · exact h.2
  have hlin : ∀ c ∈ S, 2 * (b 0 - a 0) * c 0 + 2 * (b 1 - a 1) * c 1 =
      (b 0 ^ 2 + b 1 ^ 2 - r₂ ^ 2) - (a 0 ^ 2 + a 1 ^ 2 - r₁ ^ 2) := by
    intro c hc
    have h1 := dist_sq_coords a c
    have h2 := dist_sq_coords b c
    rw [(hS c hc).1] at h1
    rw [(hS c hc).2] at h2
    linarith
  set K := (b 0 ^ 2 + b 1 ^ 2 - r₂ ^ 2) - (a 0 ^ 2 + a 1 ^ 2 - r₁ ^ 2)
  set dx := b 0 - a 0
  set dy := b 1 - a 1
  rcases hdiff_ne with h0 | h1
  · have hdx : dx ≠ 0 := sub_ne_zero.mpr h0.symm
    have hinj : Set.InjOn (fun c : ℝ² => c 1) (S : Set ℝ²) := by
      intro c₁ hc₁ c₂ hc₂ heq
      have hl1 := hlin c₁ hc₁
      have hl2 := hlin c₂ hc₂
      have h0eq : c₁ 0 = c₂ 0 := by
        have hmul : 2 * dx * (c₁ 0 - c₂ 0) = 0 := by
          dsimp only at heq
          linear_combination hl1 - hl2 - 2 * dy * heq
        exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left (mul_ne_zero two_ne_zero hdx))
      ext i
      fin_cases i
      · exact h0eq
      · exact heq
    have hcard_eq : S.card = (S.image (fun c : ℝ² => c 1)).card :=
      (Finset.card_image_of_injOn hinj).symm
    rw [hcard_eq]
    have hA : 4 * (dx ^ 2 + dy ^ 2) ≠ 0 := by positivity
    refine quadratic_at_most_two_roots hA (B := -(4 * dy * (K - 2 * dx * a 0) + 8 * dx ^ 2 * a 1))
      (C := (K - 2 * dx * a 0) ^ 2 + 4 * dx ^ 2 * (a 1 ^ 2 - r₁ ^ 2)) ?_
    intro y hy
    obtain ⟨c, hcS, rfl⟩ := Finset.mem_image.mp hy
    have hl := hlin c hcS
    have hsq := dist_sq_coords a c
    rw [(hS c hcS).1] at hsq
    have hx : 2 * dx * (c 0 - a 0) = (K - 2 * dx * a 0) - 2 * dy * c 1 := by
      dsimp [K, dx, dy] at hl ⊢
      linarith
    have hsq4 : (2 * dx * (c 0 - a 0)) ^ 2 + 4 * dx ^ 2 * (a 1 - c 1) ^ 2 = 4 * dx ^ 2 * r₁ ^ 2 := by
      have : (2 * dx * (c 0 - a 0)) ^ 2 = 4 * dx ^ 2 * (a 0 - c 0) ^ 2 := by ring
      rw [this]
      nlinarith
    rw [hx] at hsq4
    linarith
  · have hdy : dy ≠ 0 := sub_ne_zero.mpr h1.symm
    have hinj : Set.InjOn (fun c : ℝ² => c 0) (S : Set ℝ²) := by
      intro c₁ hc₁ c₂ hc₂ heq
      have hl1 := hlin c₁ hc₁
      have hl2 := hlin c₂ hc₂
      have h1eq : c₁ 1 = c₂ 1 := by
        have hmul : 2 * dy * (c₁ 1 - c₂ 1) = 0 := by
          dsimp only at heq
          linear_combination hl1 - hl2 - 2 * dx * heq
        exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left (mul_ne_zero two_ne_zero hdy))
      ext i
      fin_cases i
      · exact heq
      · exact h1eq
    have hcard_eq : S.card = (S.image (fun c : ℝ² => c 0)).card :=
      (Finset.card_image_of_injOn hinj).symm
    rw [hcard_eq]
    have hA : 4 * (dx ^ 2 + dy ^ 2) ≠ 0 := by positivity
    refine quadratic_at_most_two_roots hA (B := -(4 * dx * (K - 2 * dy * a 1) + 8 * dy ^ 2 * a 0))
      (C := (K - 2 * dy * a 1) ^ 2 + 4 * dy ^ 2 * (a 0 ^ 2 - r₁ ^ 2)) ?_
    intro x hx
    obtain ⟨c, hcS, rfl⟩ := Finset.mem_image.mp hx
    have hl := hlin c hcS
    have hsq := dist_sq_coords a c
    rw [(hS c hcS).1] at hsq
    have hy : 2 * dy * (c 1 - a 1) = (K - 2 * dy * a 1) - 2 * dx * c 0 := by
      dsimp [K, dx, dy] at hl ⊢
      linarith
    have hsq4 : 4 * dy ^ 2 * (a 0 - c 0) ^ 2 + (2 * dy * (c 1 - a 1)) ^ 2 = 4 * dy ^ 2 * r₁ ^ 2 := by
      have : (2 * dy * (c 1 - a 1)) ^ 2 = 4 * dy ^ 2 * (a 1 - c 1) ^ 2 := by ring
      rw [this]
      nlinarith
    rw [hy] at hsq4
    linarith

private lemma fixed_dist_offDiag_bound (P : Finset ℝ²) (r : ℝ) :
    ((P.offDiag.filter (fun p => dist p.1 p.2 = r)).card : ℝ) ^ 2 ≤
      3 * (P.card : ℝ) ^ 3 := by
  classical
  set E := P.offDiag.filter (fun p => dist p.1 p.2 = r)
  let N : ℝ² → Finset ℝ² := fun c => P.filter (fun a => a ≠ c ∧ dist a c = r)
  have hE_sum : E.card = ∑ c ∈ P, (N c).card := by
    have hbi : E.card = (P.biUnion (fun c => (N c).map ⟨fun a => (a, c), fun _ _ h => (Prod.mk.inj h).1⟩)).card := by
      congr 1
      ext ⟨a, c⟩
      simp only [E, N, Finset.mem_filter, Finset.mem_offDiag, Finset.mem_biUnion, Finset.mem_map]
      constructor
      · rintro ⟨⟨ha, hc, hac⟩, hr⟩
        exact ⟨c, hc, a, ⟨ha, hac, hr⟩, rfl⟩
      · rintro ⟨c', hc', a', ⟨ha', hac', hr'⟩, h⟩
        rcases Prod.mk.inj h with ⟨rfl, rfl⟩
        exact ⟨⟨ha', hc', hac'⟩, hr'⟩
    rw [hbi, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun c _ => Finset.card_map _
    · intro c₁ _ c₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      obtain ⟨_, _, rfl⟩ := Finset.mem_map.mp hp1
      obtain ⟨_, _, h2⟩ := Finset.mem_map.mp hp2
      exact hne (Prod.mk.inj h2).2.symm
  let T := (P ×ˢ P.offDiag).filter (fun x => x.2.1 ≠ x.1 ∧ x.2.2 ≠ x.1 ∧
    dist x.2.1 x.1 = r ∧ dist x.2.2 x.1 = r)
  have hT_left : T.card = ∑ c ∈ P, (N c).offDiag.card := by
    have hbi : T.card = (P.biUnion (fun c =>
        (N c).offDiag.map ⟨fun p => (c, p), fun _ _ h => (Prod.mk.inj h).2⟩)).card := by
      congr 1
      ext ⟨c, a, b⟩
      simp only [T, N, Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag,
        Finset.mem_biUnion, Finset.mem_map]
      constructor
      · rintro ⟨⟨hc, ha, hb, hab⟩, hac, hbc, hra, hrb⟩
        exact ⟨c, hc, (a, b), ⟨⟨ha, hac, hra⟩, ⟨hb, hbc, hrb⟩, hab⟩, rfl⟩
      · rintro ⟨c', hc', ⟨a', b'⟩, ⟨⟨ha', hac', hra'⟩, ⟨hb', hbc', hrb'⟩, hab'⟩, h⟩
        rcases Prod.mk.inj h with ⟨rfl, h2⟩
        rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
        exact ⟨⟨hc', ha', hb', hab'⟩, hac', hbc', hra', hrb'⟩
    rw [hbi, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun c _ => Finset.card_map _
    · intro c₁ _ c₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      obtain ⟨_, _, rfl⟩ := Finset.mem_map.mp hx1
      obtain ⟨_, _, h2⟩ := Finset.mem_map.mp hx2
      exact hne (Prod.mk.inj h2).1.symm
  have hT_right : T.card ≤ 2 * P.offDiag.card := by
    have hbi : T.card = (P.offDiag.biUnion (fun p =>
        (P.filter (fun c => p.1 ≠ c ∧ p.2 ≠ c ∧ dist p.1 c = r ∧ dist p.2 c = r)).map
          ⟨fun c => (c, p), fun _ _ h => (Prod.mk.inj h).1⟩)).card := by
      congr 1
      ext ⟨c, a, b⟩
      simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag,
        Finset.mem_biUnion, Finset.mem_map]
      constructor
      · rintro ⟨⟨hc, ha, hb, hab⟩, hac, hbc, hra, hrb⟩
        exact ⟨(a, b), ⟨ha, hb, hab⟩, c, ⟨hc, hac, hbc, hra, hrb⟩, rfl⟩
      · rintro ⟨⟨a', b'⟩, ⟨ha', hb', hab'⟩, c', ⟨hc', hac', hbc', hra', hrb'⟩, h⟩
        rcases Prod.mk.inj h with ⟨rfl, h2⟩
        rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
        exact ⟨⟨hc', ha', hb', hab'⟩, hac', hbc', hra', hrb'⟩
    rw [hbi]
    refine (Finset.card_biUnion_le).trans ?_
    calc
      ∑ p ∈ P.offDiag, ((P.filter (fun c => p.1 ≠ c ∧ p.2 ≠ c ∧ dist p.1 c = r ∧ dist p.2 c = r)).map _).card
          ≤ ∑ _p ∈ P.offDiag, 2 := by
        refine Finset.sum_le_sum fun p hp => ?_
        rw [Finset.card_map]
        have hpne : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
        exact circle_inter_card_le_two hpne r r _ (fun c hc => by
          have := (Finset.mem_filter.mp hc).2
          exact ⟨this.2.2.1, this.2.2.2⟩)
      _ = 2 * P.offDiag.card := by simp [mul_comm]
  have hsum_sq : (∑ c ∈ P, ((N c).card : ℝ) ^ 2) ≤ 2 * (P.card : ℝ) ^ 2 + (E.card : ℝ) := by
    have hnat : ∑ c ∈ P, (N c).card ^ 2 = T.card + E.card := by
      rw [hT_left, hE_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.offDiag_card]
      have : (N c).card ≤ (N c).card * (N c).card := Nat.le_mul_self _
      have : (N c).card ^ 2 = (N c).card * (N c).card := sq _
      omega
    have hoff : P.offDiag.card ≤ P.card * P.card := by
      rw [Finset.offDiag_card]
      exact Nat.sub_le _ _
    have hnat_le : ∑ c ∈ P, (N c).card ^ 2 ≤ 2 * (P.card * P.card) + E.card := by omega
    have hr : ((∑ c ∈ P, (N c).card ^ 2 : ℕ) : ℝ) ≤ ((2 * (P.card * P.card) + E.card : ℕ) : ℝ) := by
      exact_mod_cast hnat_le
    push_cast at hr
    linarith
  have hE_le : (E.card : ℝ) ≤ (P.card : ℝ) ^ 2 := by
    have h1 : E.card ≤ P.offDiag.card := Finset.card_filter_le _ _
    have h2 : P.offDiag.card ≤ P.card * P.card := by rw [Finset.offDiag_card]; exact Nat.sub_le _ _
    have h3 : E.card ≤ P.card * P.card := h1.trans h2
    have h4 : (E.card : ℝ) ≤ ((P.card * P.card : ℕ) : ℝ) := by exact_mod_cast h3
    push_cast at h4
    linarith
  have hcs : (∑ c ∈ P, ((N c).card : ℝ)) ^ 2 ≤ (P.card : ℝ) * ∑ c ∈ P, ((N c).card : ℝ) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hE_eq : (E.card : ℝ) = ∑ c ∈ P, ((N c).card : ℝ) := by exact_mod_cast hE_sum
  rw [hE_eq]
  have hP0 : (0 : ℝ) ≤ (P.card : ℝ) := Nat.cast_nonneg _
  nlinarith

private lemma sum_sq_equal_dist_pairs_bound (P : Finset ℝ²) :
    (((P.offDiag ×ˢ P.offDiag).filter (fun pq => dist pq.1.1 pq.1.2 = dist pq.2.1 pq.2.2)).card : ℝ) ≤
      2 * (P.card : ℝ) ^ (7 / 2 : ℝ) := by
  classical
  set Q := (P.offDiag ×ˢ P.offDiag).filter (fun pq => dist pq.1.1 pq.1.2 = dist pq.2.1 pq.2.2)
  set D := distanceSet P
  have hQ_eq : Q.card = ∑ r ∈ D, (P.offDiag.filter (fun p => dist p.1 p.2 = r)).card ^ 2 := by
    have hbi : Q.card = (D.biUnion (fun r =>
        (P.offDiag.filter (fun p => dist p.1 p.2 = r)) ×ˢ
        (P.offDiag.filter (fun p => dist p.1 p.2 = r)))).card := by
      congr 1
      ext ⟨p, q⟩
      simp only [Q, D, distanceSet, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion,
        Finset.mem_image]
      constructor
      · rintro ⟨⟨hp, hq⟩, hdist⟩
        exact ⟨dist p.1 p.2, ⟨p, hp, rfl⟩, ⟨hp, rfl⟩, ⟨hq, hdist.symm⟩⟩
      · rintro ⟨r, _, ⟨hp, hr1⟩, ⟨hq, hr2⟩⟩
        exact ⟨⟨hp, hq⟩, hr1.trans hr2.symm⟩
    rw [hbi, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun r _ => by rw [Finset.card_product, sq]
    · intro r₁ _ r₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro pq h1 h2
      simp only [Finset.mem_product, Finset.mem_filter] at h1 h2
      exact hne (h1.1.2.symm.trans h2.1.2)
  have hE_bound : ∀ r ∈ D,
      ((P.offDiag.filter (fun p => dist p.1 p.2 = r)).card : ℝ) ≤ 2 * (P.card : ℝ) ^ (3 / 2 : ℝ) := by
    intro r _
    have hsq := fixed_dist_offDiag_bound P r
    have hP0 : (0 : ℝ) ≤ (P.card : ℝ) := Nat.cast_nonneg _
    have hrhs_sq : (2 * (P.card : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = 4 * (P.card : ℝ) ^ 3 := by
      rw [mul_pow, ← Real.rpow_natCast ((P.card : ℝ) ^ (3 / 2 : ℝ)) 2, ← Real.rpow_mul hP0]
      norm_num
    have hle : ((P.offDiag.filter (fun p => dist p.1 p.2 = r)).card : ℝ) ^ 2 ≤
        (2 * (P.card : ℝ) ^ (3 / 2 : ℝ)) ^ 2 := by
      rw [hrhs_sq]
      nlinarith [pow_nonneg hP0 3]
    exact le_of_sq_le_sq hle (by positivity)
  have hsum_E : (∑ r ∈ D, ((P.offDiag.filter (fun p => dist p.1 p.2 = r)).card : ℝ)) =
      (P.offDiag.card : ℝ) := by
    have hnat : ∑ r ∈ D, (P.offDiag.filter (fun p => dist p.1 p.2 = r)).card = P.offDiag.card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext p
        simp only [D, distanceSet, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
        constructor
        · rintro ⟨_, _, hp, _⟩; exact hp
        · intro hp; exact ⟨dist p.1 p.2, ⟨p, hp, rfl⟩, hp, rfl⟩
      · intro r₁ _ r₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro p h1 h2
        exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    exact_mod_cast hnat
  have hP0 : (0 : ℝ) ≤ (P.card : ℝ) := Nat.cast_nonneg _
  have hQ_real : (Q.card : ℝ) = ∑ r ∈ D, ((P.offDiag.filter (fun p => dist p.1 p.2 = r)).card : ℝ) ^ 2 := by
    exact_mod_cast hQ_eq
  rw [hQ_real]
  calc
    ∑ r ∈ D, ((P.offDiag.filter (fun p => dist p.1 p.2 = r)).card : ℝ) ^ 2
        ≤ ∑ r ∈ D, (2 * (P.card : ℝ) ^ (3 / 2 : ℝ)) *
          ((P.offDiag.filter (fun p => dist p.1 p.2 = r)).card : ℝ) := by
      refine Finset.sum_le_sum fun r hr => ?_
      rw [sq]
      exact mul_le_mul_of_nonneg_right (hE_bound r hr) (Nat.cast_nonneg _)
    _ = (2 * (P.card : ℝ) ^ (3 / 2 : ℝ)) * (P.offDiag.card : ℝ) := by
      rw [← Finset.mul_sum, hsum_E]
    _ ≤ (2 * (P.card : ℝ) ^ (3 / 2 : ℝ)) * (P.card : ℝ) ^ 2 := by
      have hoff : (P.offDiag.card : ℝ) ≤ (P.card : ℝ) ^ 2 := by
        have h : P.offDiag.card ≤ P.card * P.card := by rw [Finset.offDiag_card]; exact Nat.sub_le _ _
        have h' : (P.offDiag.card : ℝ) ≤ ((P.card * P.card : ℕ) : ℝ) := by exact_mod_cast h
        push_cast at h'; linarith
      exact mul_le_mul_of_nonneg_left hoff (by positivity)
    _ = 2 * (P.card : ℝ) ^ (7 / 2 : ℝ) := by
      by_cases hPzero : (P.card : ℝ) = 0
      · simp [hPzero]
      · have hPpos : 0 < (P.card : ℝ) := lt_of_le_of_ne hP0 (Ne.symm hPzero)
        rw [mul_assoc, ← Real.rpow_natCast (P.card : ℝ) 2, ← Real.rpow_add hPpos]
        norm_num

private lemma isosceles_triples_bound (P : Finset ℝ²) :
    (((P ×ˢ P.offDiag).filter (fun x => x.1 ≠ x.2.1 ∧ x.1 ≠ x.2.2 ∧
      dist x.1 x.2.1 = dist x.1 x.2.2)).card : ℝ) ≤ 2 * (P.card : ℝ) ^ (5 / 2 : ℝ) := by
  classical
  set I := (P ×ˢ P.offDiag).filter (fun x => x.1 ≠ x.2.1 ∧ x.1 ≠ x.2.2 ∧
    dist x.1 x.2.1 = dist x.1 x.2.2)
  let M : ℝ² × ℝ² → Finset ℝ² := fun bc =>
    P.filter (fun a => a ≠ bc.1 ∧ a ≠ bc.2 ∧ dist a bc.1 = dist a bc.2)
  have hI_sum : I.card = ∑ bc ∈ P.offDiag, (M bc).card := by
    have hbi : I.card = (P.offDiag.biUnion (fun bc =>
        (M bc).map ⟨fun a => (a, bc), fun _ _ h => (Prod.mk.inj h).1⟩)).card := by
      congr 1
      ext ⟨a, b, c⟩
      simp only [I, M, Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_map]
      constructor
      · rintro ⟨⟨ha, hbc⟩, hab, hac, hd⟩
        exact ⟨(b, c), hbc, a, ⟨ha, hab, hac, hd⟩, rfl⟩
      · rintro ⟨⟨b', c'⟩, hbc', a', ⟨ha', hab', hac', hd'⟩, h⟩
        rcases Prod.mk.inj h with ⟨rfl, h2⟩
        rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
        exact ⟨⟨ha', hbc'⟩, hab', hac', hd'⟩
    rw [hbi, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun bc _ => Finset.card_map _
    · intro bc₁ _ bc₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      obtain ⟨_, _, rfl⟩ := Finset.mem_map.mp hx1
      obtain ⟨_, _, h2⟩ := Finset.mem_map.mp hx2
      exact hne (Prod.mk.inj h2).2.symm
  let W := (P.offDiag ×ˢ P.offDiag).filter (fun x =>
    x.1.1 ≠ x.2.1 ∧ x.1.1 ≠ x.2.2 ∧ x.1.2 ≠ x.2.1 ∧ x.1.2 ≠ x.2.2 ∧
    dist x.1.1 x.2.1 = dist x.1.1 x.2.2 ∧ dist x.1.2 x.2.1 = dist x.1.2 x.2.2)
  have hW_left : W.card = ∑ bc ∈ P.offDiag, (M bc).offDiag.card := by
    have hbi : W.card = (P.offDiag.biUnion (fun bc =>
        (M bc).offDiag.map ⟨fun aa => (aa, bc), fun _ _ h => (Prod.mk.inj h).1⟩)).card := by
      congr 1
      ext ⟨⟨a₁, a₂⟩, ⟨b, c⟩⟩
      simp only [W, M, Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag,
        Finset.mem_biUnion, Finset.mem_map]
      constructor
      · rintro ⟨⟨⟨ha1, ha2, ha12⟩, hb, hc, hbc⟩, h1, h2, h3, h4, hd1, hd2⟩
        exact ⟨(b, c), ⟨hb, hc, hbc⟩, (a₁, a₂), ⟨⟨ha1, h1, h2, hd1⟩, ⟨ha2, h3, h4, hd2⟩, ha12⟩, rfl⟩
      · rintro ⟨⟨b', c'⟩, ⟨hb', hc', hbc'⟩, ⟨a₁', a₂'⟩,
          ⟨⟨ha1', h1, h2, hd1⟩, ⟨ha2', h3, h4, hd2⟩, ha12'⟩, h⟩
        rcases Prod.mk.inj h with ⟨hA, hB⟩
        rcases Prod.mk.inj hA with ⟨rfl, rfl⟩
        rcases Prod.mk.inj hB with ⟨rfl, rfl⟩
        exact ⟨⟨⟨ha1', ha2', ha12'⟩, hb', hc', hbc'⟩, h1, h2, h3, h4, hd1, hd2⟩
    rw [hbi, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun bc _ => Finset.card_map _
    · intro bc₁ _ bc₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      obtain ⟨_, _, rfl⟩ := Finset.mem_map.mp hx1
      obtain ⟨_, _, h2⟩ := Finset.mem_map.mp hx2
      exact hne (Prod.mk.inj h2).2.symm
  have hW_right : W.card ≤ P.offDiag.card * P.card := by
    have hbi : W.card = ((P.offDiag ×ˢ P).biUnion (fun ab =>
        (P.filter (fun c => ab.2 ≠ c ∧ ab.1.1 ≠ ab.2 ∧ ab.1.1 ≠ c ∧ ab.1.2 ≠ ab.2 ∧ ab.1.2 ≠ c ∧
          dist ab.1.1 ab.2 = dist ab.1.1 c ∧ dist ab.1.2 ab.2 = dist ab.1.2 c)).map
          ⟨fun c => (ab.1, (ab.2, c)), fun _ _ h => (Prod.mk.inj (Prod.mk.inj h).2).2⟩)).card := by
      congr 1
      ext ⟨⟨a₁, a₂⟩, ⟨b, c⟩⟩
      simp only [W, Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag,
        Finset.mem_biUnion, Finset.mem_map]
      constructor
      · rintro ⟨⟨⟨ha1, ha2, ha12⟩, hb, hc, hbc⟩, h1, h2, h3, h4, hd1, hd2⟩
        exact ⟨((a₁, a₂), b), ⟨⟨ha1, ha2, ha12⟩, hb⟩, c, ⟨hc, hbc, h1, h2, h3, h4, hd1, hd2⟩, rfl⟩
      · rintro ⟨⟨⟨a₁', a₂'⟩, b'⟩, ⟨⟨ha1', ha2', ha12'⟩, hb'⟩, c',
          ⟨hc', hbc', h1, h2, h3, h4, hd1, hd2⟩, h⟩
        rcases Prod.mk.inj h with ⟨hA, hB⟩
        rcases Prod.mk.inj hA with ⟨rfl, rfl⟩
        rcases Prod.mk.inj hB with ⟨rfl, rfl⟩
        exact ⟨⟨⟨ha1', ha2', ha12'⟩, hb', hc', hbc'⟩, h1, h2, h3, h4, hd1, hd2⟩
    rw [hbi]
    refine (Finset.card_biUnion_le).trans ?_
    calc
      ∑ ab ∈ P.offDiag ×ˢ P, ((P.filter (fun c => ab.2 ≠ c ∧ ab.1.1 ≠ ab.2 ∧ ab.1.1 ≠ c ∧
          ab.1.2 ≠ ab.2 ∧ ab.1.2 ≠ c ∧ dist ab.1.1 ab.2 = dist ab.1.1 c ∧
          dist ab.1.2 ab.2 = dist ab.1.2 c)).map _).card
          ≤ ∑ _ab ∈ P.offDiag ×ˢ P, 1 := by
        refine Finset.sum_le_sum fun ab hab => ?_
        rw [Finset.card_map]
        have ha12 : ab.1.1 ≠ ab.1.2 := (Finset.mem_offDiag.mp (Finset.mem_product.mp hab).1).2.2
        set C := P.filter (fun c => ab.2 ≠ c ∧ ab.1.1 ≠ ab.2 ∧ ab.1.1 ≠ c ∧ ab.1.2 ≠ ab.2 ∧
          ab.1.2 ≠ c ∧ dist ab.1.1 ab.2 = dist ab.1.1 c ∧ dist ab.1.2 ab.2 = dist ab.1.2 c)
        have hnot : ab.2 ∉ C := by
          intro hm
          exact (Finset.mem_filter.mp hm).2.1 rfl
        have hle2 : (insert ab.2 C).card ≤ 2 := by
          refine circle_inter_card_le_two ha12 (dist ab.1.1 ab.2) (dist ab.1.2 ab.2) _ ?_
          intro c hc
          rw [Finset.mem_insert] at hc
          rcases hc with rfl | hcC
          · exact ⟨rfl, rfl⟩
          · have h := (Finset.mem_filter.mp hcC).2
            exact ⟨h.2.2.2.2.2.1.symm, h.2.2.2.2.2.2.symm⟩
        rw [Finset.card_insert_of_notMem hnot] at hle2
        omega
      _ = P.offDiag.card * P.card := by simp [Finset.card_product]
  have hsum_sq : (∑ bc ∈ P.offDiag, ((M bc).card : ℝ) ^ 2) ≤ 2 * (P.card : ℝ) ^ 3 := by
    have hnat : ∑ bc ∈ P.offDiag, (M bc).card ^ 2 = W.card + I.card := by
      rw [hW_left, hI_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun bc _ => ?_
      rw [Finset.offDiag_card]
      have : (M bc).card ≤ (M bc).card * (M bc).card := Nat.le_mul_self _
      have : (M bc).card ^ 2 = (M bc).card * (M bc).card := sq _
      omega
    have hI_le : I.card ≤ P.card * P.offDiag.card := by
      have := Finset.card_filter_le (P ×ˢ P.offDiag) (fun x => x.1 ≠ x.2.1 ∧ x.1 ≠ x.2.2 ∧
        dist x.1 x.2.1 = dist x.1 x.2.2)
      rwa [Finset.card_product] at this
    have hoff : P.offDiag.card ≤ P.card * P.card := by rw [Finset.offDiag_card]; exact Nat.sub_le _ _
    have hnat_le : ∑ bc ∈ P.offDiag, (M bc).card ^ 2 ≤ 2 * (P.card * P.card * P.card) := by
      have h1 : W.card ≤ P.card * P.card * P.card := by nlinarith
      have h2 : I.card ≤ P.card * P.card * P.card := by nlinarith
      omega
    have hr : ((∑ bc ∈ P.offDiag, (M bc).card ^ 2 : ℕ) : ℝ) ≤
        ((2 * (P.card * P.card * P.card) : ℕ) : ℝ) := by exact_mod_cast hnat_le
    push_cast at hr
    linarith
  have hcs : (∑ bc ∈ P.offDiag, ((M bc).card : ℝ)) ^ 2 ≤
      (P.offDiag.card : ℝ) * ∑ bc ∈ P.offDiag, ((M bc).card : ℝ) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hI_eq : (I.card : ℝ) = ∑ bc ∈ P.offDiag, ((M bc).card : ℝ) := by exact_mod_cast hI_sum
  have hP0 : (0 : ℝ) ≤ (P.card : ℝ) := Nat.cast_nonneg _
  have hoff_r : (P.offDiag.card : ℝ) ≤ (P.card : ℝ) ^ 2 := by
    have h : P.offDiag.card ≤ P.card * P.card := by rw [Finset.offDiag_card]; exact Nat.sub_le _ _
    have h' : (P.offDiag.card : ℝ) ≤ ((P.card * P.card : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'; linarith
  have hsq : (I.card : ℝ) ^ 2 ≤ (2 * (P.card : ℝ) ^ (5 / 2 : ℝ)) ^ 2 := by
    have hrhs : (2 * (P.card : ℝ) ^ (5 / 2 : ℝ)) ^ 2 = 4 * (P.card : ℝ) ^ 5 := by
      rw [mul_pow, ← Real.rpow_natCast ((P.card : ℝ) ^ (5 / 2 : ℝ)) 2, ← Real.rpow_mul hP0]
      norm_num
    rw [hrhs, hI_eq]
    have hnn : 0 ≤ ∑ bc ∈ P.offDiag, ((M bc).card : ℝ) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    nlinarith [pow_nonneg hP0 5]
  exact le_of_sq_le_sq hsq (by positivity)

private lemma exists_equal_dist_pairs_of_hasRepeatedDistance {S : Finset ℝ²}
    (hcard : S.card = 4) (hrep : Erdos1087.HasRepeatedDistance S) :
    (∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ dist a b = dist a c) ∨
    (∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S,
      a ≠ b ∧ c ≠ d ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧
      dist a b = dist c d ∧ S = {a, b, c, d}) := by
  classical
  unfold Erdos1087.HasRepeatedDistance distinctDistances at hrep
  rw [hcard] at hrep
  have hchoose : (4 : ℕ).choose 2 = 6 := by decide
  rw [hchoose] at hrep
  let pairDist : Finset ℝ² → ℝ := fun e =>
    if h : e.card = 2 then
      let a := (Finset.card_eq_two.mp h).choose
      let b := (Finset.card_eq_two.mp h).choose_spec.choose
      dist a b
    else 0
  have hpairDist_eq : ∀ {e : Finset ℝ²} {x y : ℝ²}, x ≠ y → e = {x, y} → pairDist e = dist x y := by
    intro e x y hxy he
    have h2 : e.card = 2 := by rw [he, Finset.card_pair hxy]
    simp only [pairDist, dif_pos h2]
    set a := (Finset.card_eq_two.mp h2).choose
    set b := (Finset.card_eq_two.mp h2).choose_spec.choose
    have hab := (Finset.card_eq_two.mp h2).choose_spec.choose_spec
    have hset : ({a, b} : Finset ℝ²) = {x, y} := hab.2.symm.trans he
    have ha : a ∈ ({x, y} : Finset ℝ²) := by rw [← hset]; simp
    have hb : b ∈ ({x, y} : Finset ℝ²) := by rw [← hset]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    change dist a b = dist x y
    rcases ha with hax | hay <;> rcases hb with hbx | hby
    · exact absurd (hax.trans hbx.symm) hab.1
    · rw [hax, hby]
    · rw [hay, hbx]; exact dist_comm _ _
    · exact absurd (hay.trans hby.symm) hab.1
  have hmaps : Set.MapsTo pairDist (S.powersetCard 2 : Set (Finset ℝ²)) (distanceSet S : Set ℝ) := by
    intro e he
    rw [Finset.mem_coe, Finset.mem_powersetCard] at he
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp he.2
    rw [hpairDist_eq hxy rfl, Finset.mem_coe, distanceSet, Finset.mem_image]
    exact ⟨(x, y), Finset.mem_offDiag.mpr ⟨he.1 (by simp), he.1 (by simp), hxy⟩, rfl⟩
  have hlt : (distanceSet S).card < (S.powersetCard 2).card := by
    rw [Finset.card_powersetCard, hcard, hchoose]
    exact hrep
  obtain ⟨e₁, he₁, e₂, he₂, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  rw [Finset.mem_powersetCard] at he₁ he₂
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp he₁.2
  obtain ⟨c, d, hcd, rfl⟩ := Finset.card_eq_two.mp he₂.2
  rw [hpairDist_eq hab rfl, hpairDist_eq hcd rfl] at heq
  have haS : a ∈ S := he₁.1 (by simp)
  have hbS : b ∈ S := he₁.1 (by simp)
  have hcS : c ∈ S := he₂.1 (by simp)
  have hdS : d ∈ S := he₂.1 (by simp)
  by_cases hac : a = c
  · subst hac
    have hbd : b ≠ d := fun h => hne (by rw [h])
    exact Or.inl ⟨a, haS, b, hbS, d, hdS, hab, hcd, hbd, heq⟩
  by_cases had : a = d
  · subst had
    have hbc : b ≠ c := fun h => hne (by rw [h, Finset.pair_comm])
    exact Or.inl ⟨a, haS, b, hbS, c, hcS, hab, hcd.symm, hbc, heq.trans (dist_comm _ _)⟩
  by_cases hbc : b = c
  · subst hbc
    exact Or.inl ⟨b, hbS, a, haS, d, hdS, hab.symm, hcd, had, (dist_comm _ _).trans heq⟩
  by_cases hbd : b = d
  · subst hbd
    exact Or.inl ⟨b, hbS, a, haS, c, hcS, hab.symm, hcd.symm, hac,
      (dist_comm _ _).trans (heq.trans (dist_comm _ _))⟩
  right
  refine ⟨a, haS, b, hbS, c, hcS, d, hdS, hab, hcd, hac, had, hbc, hbd, heq, ?_⟩
  have hsub : ({a, b, c, d} : Finset ℝ²) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hcard4 : ({a, b, c, d} : Finset ℝ²).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]),
      Finset.card_pair hcd]
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hcard4])).symm

private lemma degenerateCount_le_bound (P : Finset ℝ²) :
    (Erdos1087.degenerateCount P : ℝ) ≤ 4 * (P.card : ℝ) ^ (7 / 2 : ℝ) := by
  classical
  unfold Erdos1087.degenerateCount
  set I := (P ×ˢ P.offDiag).filter (fun x => x.1 ≠ x.2.1 ∧ x.1 ≠ x.2.2 ∧
    dist x.1 x.2.1 = dist x.1 x.2.2)
  set Q := (P.offDiag ×ˢ P.offDiag).filter (fun pq => dist pq.1.1 pq.1.2 = dist pq.2.1 pq.2.2)
  let f₁ : (ℝ² × ℝ² × ℝ²) × ℝ² → Finset ℝ² := fun x => {x.1.1, x.1.2.1, x.1.2.2, x.2}
  let f₂ : (ℝ² × ℝ²) × (ℝ² × ℝ²) → Finset ℝ² := fun pq => {pq.1.1, pq.1.2, pq.2.1, pq.2.2}
  have hcover : (P.powersetCard 4).filter Erdos1087.HasRepeatedDistance ⊆
      (I ×ˢ P).image f₁ ∪ Q.image f₂ := by
    intro S hS
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hS
    obtain ⟨⟨hSP, hScard⟩, hrep⟩ := hS
    rw [Finset.mem_union]
    rcases exists_equal_dist_pairs_of_hasRepeatedDistance hScard hrep with
      ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hd⟩ |
      ⟨a, ha, b, hb, c, hc, d, hd', hab, hcd, hac, had, hbc, hbd, hdist, hSeq⟩
    · left
      have hsub3 : ({a, b, c} : Finset ℝ²) ⊆ S := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      have hcard3 : ({a, b, c} : Finset ℝ²).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
      have hsdiff : (S \ {a, b, c}).card = 1 := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub3, hScard, hcard3]
      obtain ⟨e, he⟩ := Finset.card_eq_one.mp hsdiff
      have he_mem : e ∈ S \ {a, b, c} := by rw [he]; simp
      have heS : e ∈ S := (Finset.mem_sdiff.mp he_mem).1
      have hSeq' : {a, b, c, e} = S := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro (rfl | rfl | rfl | rfl) <;> assumption
        · intro hxS
          by_cases hxa : x = a; · exact Or.inl hxa
          by_cases hxb : x = b; · exact Or.inr (Or.inl hxb)
          by_cases hxc : x = c; · exact Or.inr (Or.inr (Or.inl hxc))
          have hxs : x ∈ S \ {a, b, c} := Finset.mem_sdiff.mpr ⟨hxS, by simp [hxa, hxb, hxc]⟩
          rw [he, Finset.mem_singleton] at hxs
          exact Or.inr (Or.inr (Or.inr hxs))
      refine Finset.mem_image.mpr ⟨((a, (b, c)), e), Finset.mem_product.mpr ⟨?_, hSP heS⟩, hSeq'⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hSP ha,
        Finset.mem_offDiag.mpr ⟨hSP hb, hSP hc, hbc⟩⟩, hab, hac, hd⟩
    · right
      refine Finset.mem_image.mpr ⟨((a, b), (c, d)), ?_, hSeq.symm⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_offDiag.mpr ⟨hSP ha, hSP hb, hab⟩,
         Finset.mem_offDiag.mpr ⟨hSP hc, hSP hd', hcd⟩⟩, hdist⟩
  have hcard_le : ((P.powersetCard 4).filter Erdos1087.HasRepeatedDistance).card ≤
      I.card * P.card + Q.card := by
    calc
      ((P.powersetCard 4).filter Erdos1087.HasRepeatedDistance).card
          ≤ ((I ×ˢ P).image f₁ ∪ Q.image f₂).card := Finset.card_le_card hcover
      _ ≤ ((I ×ˢ P).image f₁).card + (Q.image f₂).card := Finset.card_union_le _ _
      _ ≤ (I ×ˢ P).card + Q.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _ = I.card * P.card + Q.card := by rw [Finset.card_product]
  have hcast : (((P.powersetCard 4).filter Erdos1087.HasRepeatedDistance).card : ℝ) ≤
      (I.card : ℝ) * (P.card : ℝ) + (Q.card : ℝ) := by exact_mod_cast hcard_le
  have hI := isosceles_triples_bound P
  have hQ := sum_sq_equal_dist_pairs_bound P
  have hP0 : (0 : ℝ) ≤ (P.card : ℝ) := Nat.cast_nonneg _
  have hIP : (I.card : ℝ) * (P.card : ℝ) ≤ 2 * (P.card : ℝ) ^ (7 / 2 : ℝ) := by
    by_cases hPzero : (P.card : ℝ) = 0
    · simp [hPzero]
    · have hPpos : 0 < (P.card : ℝ) := lt_of_le_of_ne hP0 (Ne.symm hPzero)
      calc
        (I.card : ℝ) * (P.card : ℝ) ≤ (2 * (P.card : ℝ) ^ (5 / 2 : ℝ)) * (P.card : ℝ) :=
          mul_le_mul_of_nonneg_right hI hP0
        _ = 2 * ((P.card : ℝ) ^ (5 / 2 : ℝ) * (P.card : ℝ)) := by ring
        _ = 2 * (P.card : ℝ) ^ ((5 / 2 : ℝ) + 1) := by
          rw [← Real.rpow_add_one (ne_of_gt hPpos)]
        _ = 2 * (P.card : ℝ) ^ (7 / 2 : ℝ) := by norm_num
  linarith

private lemma f_le_bound (n : ℕ) : (Erdos1087.f n : ℝ) ≤ 4 * (n : ℝ) ^ (7 / 2 : ℝ) := by
  unfold Erdos1087.f
  set S := {m : ℕ | ∃ P : Finset ℝ², P.card = n ∧ Erdos1087.degenerateCount P = m}
  by_cases hne : S.Nonempty
  · have hbdd : BddAbove S := by
      refine ⟨n.choose 4, ?_⟩
      rintro m ⟨P, rfl, rfl⟩
      exact Erdos1087.degenerateCount_le P
    have hmem : sSup S ∈ S := Nat.sSup_mem hne hbdd
    obtain ⟨P, hPcard, hPeq⟩ := hmem
    rw [← hPeq, ← hPcard]
    exact degenerateCount_le_bound P
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, csSup_empty]
    simp only [Nat.bot_eq_zero, Nat.cast_zero]
    positivity

end Erdos1087R1H1Proof

theorem OMA.solution : OMA.R_Erdos1087_erdos_1087_R1.H1 := by
  intro ε hε
  rw [Asymptotics.isBigO_iff]
  refine ⟨4, Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩⟩
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ (7 / 2 : ℝ) ≤ (n : ℝ) ^ (3 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hf := Erdos1087R1H1Proof.f_le_bound n
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity)]
  linarith

import OMAStatements.S_oeis_a008368
import Mathlib.Tactic

namespace OMA.P_oeis_a008368

open OMA.S_oeis_a008368

private lemma fcc_parity : ∀ {k : ℕ} {p : ℤ × ℤ × ℤ}, FccReachable k p →
    2 ∣ (p.1 + p.2.1 + p.2.2) := by
  intro k p h
  induction h with
  | zero => simp
  | @step m a b _ hstep ih =>
    rcases hstep with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> omega

private lemma fcc_dist_lower : ∀ {k : ℕ} {p : ℤ × ℤ × ℤ}, FccReachable k p →
    p.1.natAbs ≤ k ∧ p.2.1.natAbs ≤ k ∧ p.2.2.natAbs ≤ k ∧
    p.1.natAbs + p.2.1.natAbs + p.2.2.natAbs ≤ 2 * k := by
  intro k p h
  induction h with
  | zero => simp
  | @step m a b _ hstep ih =>
    rcases hstep with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> omega

private lemma fcc_step_perm12 {a b c d e f : ℤ}
    (h : IsFccStep (a, b, c) (d, e, f)) : IsFccStep (b, a, c) (e, d, f) := by
  dsimp only [IsFccStep] at h ⊢
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · left; exact ⟨h2, h1, h3⟩
  · right; right; exact ⟨h2, h1, h3⟩
  · right; left; exact ⟨h2, h1, h3⟩

private lemma fcc_step_perm23 {a b c d e f : ℤ}
    (h : IsFccStep (a, b, c) (d, e, f)) : IsFccStep (a, c, b) (d, f, e) := by
  dsimp only [IsFccStep] at h ⊢
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · right; left; exact ⟨h1, h3, h2⟩
  · left; exact ⟨h1, h3, h2⟩
  · right; right; exact ⟨h1, h3, h2⟩

private lemma fcc_reachable_perm12 {k : ℕ} {a b c : ℤ}
    (h : FccReachable k (a, b, c)) : FccReachable k (b, a, c) := by
  generalize hp : (a, b, c) = p at h
  induction h generalizing a b c with
  | zero =>
    rcases Prod.mk.inj hp with ⟨rfl, hp2⟩
    rcases Prod.mk.inj hp2 with ⟨rfl, rfl⟩
    exact FccReachable.zero
  | @step m p q _ hstep ih =>
    rcases p with ⟨pa, pb, pc⟩
    rcases q with ⟨qa, qb, qc⟩
    rcases Prod.mk.inj hp with ⟨rfl, hp2⟩
    rcases Prod.mk.inj hp2 with ⟨rfl, rfl⟩
    exact FccReachable.step (ih rfl) (fcc_step_perm12 hstep)

private lemma fcc_reachable_perm23 {k : ℕ} {a b c : ℤ}
    (h : FccReachable k (a, b, c)) : FccReachable k (a, c, b) := by
  generalize hp : (a, b, c) = p at h
  induction h generalizing a b c with
  | zero =>
    rcases Prod.mk.inj hp with ⟨rfl, hp2⟩
    rcases Prod.mk.inj hp2 with ⟨rfl, rfl⟩
    exact FccReachable.zero
  | @step m p q _ hstep ih =>
    rcases p with ⟨pa, pb, pc⟩
    rcases q with ⟨qa, qb, qc⟩
    rcases Prod.mk.inj hp with ⟨rfl, hp2⟩
    rcases Prod.mk.inj hp2 with ⟨rfl, rfl⟩
    exact FccReachable.step (ih rfl) (fcc_step_perm23 hstep)

private lemma fcc_reachable_exact :
    ∀ n : ℕ, ∀ x y z : ℕ, x ≤ y → y ≤ z → (x + y + z) % 2 = 0 →
      max z ((x + y + z) / 2) = n →
      FccReachable n ((x : ℤ), (y : ℤ), (z : ℤ)) := by
  intro n
  induction n with
  | zero =>
    intro x y z _ _ _ hmax
    have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    have hz : z = 0 := by omega
    subst hx hy hz
    exact FccReachable.zero
  | succ m ih =>
    intro x y z hxy hyz hev hmax
    by_cases hy0 : y = 0
    · subst hy0
      have hx0 : x = 0 := by omega
      subst hx0
      have hz2 : 2 ≤ z := by omega
      have hprev : FccReachable m ((0 : ℤ), (1 : ℤ), ((z - 1 : ℕ) : ℤ)) :=
        ih 0 1 (z - 1) (by omega) (by omega) (by omega) (by omega)
      refine FccReachable.step hprev ?_
      right; right
      dsimp only
      omega
    · have hy1 : 1 ≤ y := by omega
      have hz1 : 1 ≤ z := by omega
      have hstep_yz : IsFccStep ((x : ℤ), ((y - 1 : ℕ) : ℤ), ((z - 1 : ℕ) : ℤ))
          ((x : ℤ), (y : ℤ), (z : ℤ)) := by
        right; right; dsimp only; omega
      by_cases hxy1 : x ≤ y - 1
      · have hprev : FccReachable m ((x : ℤ), ((y - 1 : ℕ) : ℤ), ((z - 1 : ℕ) : ℤ)) :=
          ih x (y - 1) (z - 1) hxy1 (by omega) (by omega) (by omega)
        exact FccReachable.step hprev hstep_yz
      · -- x = y
        have hxeq : x = y := by omega
        by_cases hxz1 : x ≤ z - 1
        · have hprev := ih (y - 1) x (z - 1) (by omega) hxz1 (by omega) (by omega)
          exact FccReachable.step (fcc_reachable_perm12 hprev) hstep_yz
        · -- x = y = z, and since 3*z is even and > 0, z >= 2
          have hzeq : z = y := by omega
          have hz2 : 2 ≤ z := by omega
          have hprev := ih (y - 1) (z - 1) x (by omega) (by omega) (by omega) (by omega)
          have hprev2 := fcc_reachable_perm12 (fcc_reachable_perm23 hprev)
          exact FccReachable.step hprev2 hstep_yz

private lemma atFccDist_iff_ordered (n x y z : ℕ) (hxy : x ≤ y) (hyz : y ≤ z) :
    AtFccDist n ((x : ℤ), (y : ℤ), (z : ℤ)) ↔
      (x + y + z) % 2 = 0 ∧ max z ((x + y + z) / 2) = n := by
  constructor
  · rintro ⟨hreach, hmin⟩
    have hpar := fcc_parity hreach
    dsimp only at hpar
    have hev : (x + y + z) % 2 = 0 := by omega
    have hlo := fcc_dist_lower hreach
    have hle : max z ((x + y + z) / 2) ≤ n := by
      simp only [Int.natAbs_natCast] at hlo
      omega
    have hge : n ≤ max z ((x + y + z) / 2) := by
      by_contra hlt
      have hstrict : max z ((x + y + z) / 2) < n := by omega
      exact hmin _ hstrict (fcc_reachable_exact _ x y z hxy hyz hev rfl)
    exact ⟨hev, le_antisymm hle hge⟩
  · rintro ⟨hev, hmax⟩
    refine ⟨fcc_reachable_exact n x y z hxy hyz hev hmax, ?_⟩
    intro k hk hreach
    have hlo := fcc_dist_lower hreach
    simp only [Int.natAbs_natCast] at hlo
    omega

/-- Case 1 count: number of `(u, v, w) ∈ ℕ^3` with `2*u + v + 2*w = n`. -/
private def count1 (n : ℕ) : ℕ :=
  (((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
    (fun t : ℕ × ℕ × ℕ => 2 * t.1 + t.2.1 + 2 * t.2.2 = n)).card

/-- Case 2 count: number of `(a, b, c) ∈ ℕ^3` with `1 ≤ a` and `3*a + 2*b + c = n`. -/
private def count2 (n : ℕ) : ℕ :=
  (((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
    (fun t : ℕ × ℕ × ℕ => 1 ≤ t.1 ∧ 3 * t.1 + 2 * t.2.1 + t.2.2 = n)).card

private lemma A008368_eq_add (n : ℕ) : A008368 n = count1 n + count2 n := by
  let B := (Finset.range (n + 1)) ×ˢ (Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))
  let F := B.filter (fun t : ℕ × ℕ × ℕ =>
    t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ (t.1 + t.2.1 + t.2.2) % 2 = 0 ∧
    max t.2.2 ((t.1 + t.2.1 + t.2.2) / 2) = n)
  have hset : { t : ℕ × ℕ × ℕ |
      t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ AtFccDist n ((t.1 : ℤ), (t.2.1 : ℤ), (t.2.2 : ℤ)) } =
      (F : Set (ℕ × ℕ × ℕ)) := by
    ext ⟨x, y, z⟩
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, F, B, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range]
    constructor
    · rintro ⟨hxy, hyz, hdist⟩
      obtain ⟨hev, hmax⟩ := (atFccDist_iff_ordered n x y z hxy hyz).mp hdist
      exact ⟨⟨by omega, by omega, by omega⟩, hxy, hyz, hev, hmax⟩
    · rintro ⟨_, hxy, hyz, hev, hmax⟩
      exact ⟨hxy, hyz, (atFccDist_iff_ordered n x y z hxy hyz).mpr ⟨hev, hmax⟩⟩
  unfold A008368
  rw [hset, Set.ncard_coe_finset]
  let F1 := F.filter (fun t : ℕ × ℕ × ℕ => t.2.2 = n)
  let F2 := F.filter (fun t : ℕ × ℕ × ℕ => t.2.2 < n)
  have hdisj : Disjoint F1 F2 := by
    rw [Finset.disjoint_left]; intro t h1 h2
    simp only [F1, F2, Finset.mem_filter] at h1 h2; omega
  have hunion : F = F1 ∪ F2 := by
    ext t
    simp only [Finset.mem_union, F1, F2, Finset.mem_filter, F]
    constructor
    · intro ht
      by_cases hz : t.2.2 = n
      · exact Or.inl ⟨ht, hz⟩
      · exact Or.inr ⟨ht, by omega⟩
    · rintro (⟨ht, _⟩ | ⟨ht, _⟩) <;> exact ht
  rw [hunion, Finset.card_union_of_disjoint hdisj]
  have hc1 : F1.card = count1 n := by
    unfold count1
    refine Finset.card_bij (fun t _ => (t.1, t.2.1 - t.1, (n - t.1 - t.2.1) / 2)) ?_ ?_ ?_
    · intro t ht
      rcases t with ⟨x, y, z⟩
      simp only [F1, F, B, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at ht ⊢
      omega
    · intro t₁ ht₁ t₂ ht₂ h
      rcases t₁ with ⟨x₁, y₁, z₁⟩; rcases t₂ with ⟨x₂, y₂, z₂⟩
      simp only [F1, F, B, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at ht₁ ht₂
      rcases Prod.mk.inj h with ⟨h1, h23⟩
      rcases Prod.mk.inj h23 with ⟨h2, _⟩
      dsimp only at h1 h2
      simp only [Prod.mk.injEq]
      omega
    · intro s hs
      rcases s with ⟨u, v, w⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hs
      rcases hs with ⟨⟨hu, hv, hw⟩, hsum⟩
      refine ⟨(u, u + v, n), ?_, ?_⟩
      · simp only [F1, F, B, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        refine ⟨⟨⟨by omega, by omega, by omega⟩, by omega, by omega, by omega, by omega⟩, trivial⟩
      · simp only [Prod.mk.injEq]
        exact ⟨trivial, by omega, by omega⟩
  have hc2 : F2.card = count2 n := by
    unfold count2
    refine Finset.card_bij (fun t _ => (n - t.2.2, t.2.2 - t.2.1, t.2.1 - t.1)) ?_ ?_ ?_
    · intro t ht
      rcases t with ⟨x, y, z⟩
      simp only [F2, F, B, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at ht ⊢
      omega
    · intro t₁ ht₁ t₂ ht₂ h
      rcases t₁ with ⟨x₁, y₁, z₁⟩; rcases t₂ with ⟨x₂, y₂, z₂⟩
      simp only [F2, F, B, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at ht₁ ht₂
      rcases Prod.mk.inj h with ⟨h1, h23⟩
      rcases Prod.mk.inj h23 with ⟨h2, h3⟩
      dsimp only at h1 h2 h3
      simp only [Prod.mk.injEq]
      omega
    · intro s hs
      rcases s with ⟨a, b, c⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hs
      refine ⟨(n - a - b - c, n - a - b, n - a), ?_, ?_⟩
      · simp only [F2, F, B, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        omega
      · simp only [Prod.mk.injEq]
        omega
  rw [hc1, hc2]

/-- Power series `∑_{k ≥ 0} X^(d * k) = 1 / (1 - X^d)` for `d ≥ 1`. -/
private noncomputable def geomPS (d : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if d ∣ n then 1 else 0

private lemma one_sub_X_pow_mul_geomPS (d : ℕ) (hd : 1 ≤ d) :
    (1 - (PowerSeries.X : PowerSeries ℤ) ^ d) * geomPS d = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_one]
  have hmul : PowerSeries.coeff n ((PowerSeries.X : PowerSeries ℤ) ^ d * geomPS d) =
      if d ≤ n then PowerSeries.coeff (n - d) (geomPS d) else 0 := by
    rw [PowerSeries.coeff_mul]
    split_ifs with h
    · rw [Finset.sum_eq_single (d, n - d)]
      · simp [PowerSeries.coeff_X_pow]
      · rintro ⟨a, b⟩ hab hne
        rw [Finset.mem_antidiagonal] at hab
        have had : a ≠ d := fun ha => hne (Prod.ext ha (by omega))
        dsimp only
        rw [PowerSeries.coeff_X_pow, if_neg had, zero_mul]
      · intro hnot; exact absurd (Finset.mem_antidiagonal.mpr (by omega)) hnot
    · refine Finset.sum_eq_zero fun ⟨a, b⟩ hab => ?_
      rw [Finset.mem_antidiagonal] at hab
      have had : a ≠ d := by omega
      dsimp only
      rw [PowerSeries.coeff_X_pow, if_neg had, zero_mul]
  rw [hmul]
  simp only [geomPS, PowerSeries.coeff_mk]
  by_cases hn0 : n = 0
  · subst hn0
    have hnot : ¬(d ≤ 0) := by omega
    simp [hnot]
  · simp only [if_neg hn0]
    by_cases hdn : d ≤ n
    · simp only [if_pos hdn]
      have hiff : d ∣ n ↔ d ∣ n - d := by
        constructor
        · rintro ⟨k, hk⟩
          exact ⟨k - 1, by
            cases k with
            | zero => omega
            | succ r => simp [Nat.mul_succ] at hk ⊢; omega⟩
        · rintro ⟨k, hk⟩
          exact ⟨k + 1, by rw [Nat.mul_succ]; omega⟩
      by_cases hdvd : d ∣ n
      · rw [if_pos hdvd, if_pos (hiff.mp hdvd), sub_self]
      · rw [if_neg hdvd, if_neg (mt hiff.mpr hdvd), sub_self]
    · simp only [if_neg hdn, sub_zero]
      have hndvd : ¬(d ∣ n) := fun ⟨k, hk⟩ => by
        cases k with
        | zero => simp at hk; omega
        | succ r => simp [Nat.mul_succ] at hk; omega
      rw [if_neg hndvd]

private lemma coeff_triple_geom (d₁ d₂ d₃ : ℕ) (h1 : 1 ≤ d₁) (h2 : 1 ≤ d₂) (h3 : 1 ≤ d₃) (n : ℕ) :
    PowerSeries.coeff n (geomPS d₁ * geomPS d₂ * geomPS d₃) =
      (((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
        (fun t : ℕ × ℕ × ℕ => d₁ * t.1 + d₂ * t.2.1 + d₃ * t.2.2 = n)).card := by
  rw [PowerSeries.coeff_mul]
  have h12 : ∀ m : ℕ, PowerSeries.coeff m (geomPS d₁ * geomPS d₂) =
      (((Finset.range (m + 1)) ×ˢ (Finset.range (m + 1))).filter
        (fun p : ℕ × ℕ => d₁ * p.1 + d₂ * p.2 = m)).card := by
    intro m
    rw [PowerSeries.coeff_mul]
    simp only [geomPS, PowerSeries.coeff_mk]
    have hrew : ∀ p ∈ Finset.antidiagonal m,
        (if d₁ ∣ p.1 then (1 : ℤ) else 0) * (if d₂ ∣ p.2 then 1 else 0) =
        if d₁ ∣ p.1 ∧ d₂ ∣ p.2 then 1 else 0 := by
      intro p _; split_ifs <;> simp_all
    rw [Finset.sum_congr rfl hrew, Finset.sum_boole]
    congr 1
    refine Finset.card_bij (fun p _ => (p.1 / d₁, p.2 / d₂)) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_product, Finset.mem_range] at hp ⊢
      have hq1 : d₁ * (p.1 / d₁) = p.1 := Nat.mul_div_cancel' hp.2.1
      have hq2 : d₂ * (p.2 / d₂) = p.2 := Nat.mul_div_cancel' hp.2.2
      exact ⟨⟨Nat.lt_succ_of_le (le_trans (Nat.div_le_self _ _) (by omega)),
              Nat.lt_succ_of_le (le_trans (Nat.div_le_self _ _) (by omega))⟩, by omega⟩
    · intro p₁ hp₁ p₂ hp₂ h
      simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hp₁ hp₂
      rcases Prod.mk.inj h with ⟨ha, hb⟩
      have h1a : d₁ * (p₁.1 / d₁) = p₁.1 := Nat.mul_div_cancel' hp₁.2.1
      have h2a : d₁ * (p₂.1 / d₁) = p₂.1 := Nat.mul_div_cancel' hp₂.2.1
      have h1b : d₂ * (p₁.2 / d₂) = p₁.2 := Nat.mul_div_cancel' hp₁.2.2
      have h2b : d₂ * (p₂.2 / d₂) = p₂.2 := Nat.mul_div_cancel' hp₂.2.2
      exact Prod.ext (by rw [← h1a, ← h2a, ha]) (by rw [← h1b, ← h2b, hb])
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq
      refine ⟨(d₁ * q.1, d₂ * q.2), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_antidiagonal]
        exact ⟨hq.2, dvd_mul_right d₁ q.1, dvd_mul_right d₂ q.2⟩
      · exact Prod.ext (Nat.mul_div_cancel_left q.1 (by omega))
          (Nat.mul_div_cancel_left q.2 (by omega))
  simp_rw [h12]
  simp only [geomPS, PowerSeries.coeff_mk]
  have hrew : ∀ p ∈ Finset.antidiagonal n,
      (((Finset.range (p.1 + 1) ×ˢ Finset.range (p.1 + 1)).filter
        (fun q : ℕ × ℕ => d₁ * q.1 + d₂ * q.2 = p.1)).card : ℤ) *
        (if d₃ ∣ p.2 then 1 else 0) =
      if d₃ ∣ p.2 then (((Finset.range (p.1 + 1) ×ˢ Finset.range (p.1 + 1)).filter
        (fun q : ℕ × ℕ => d₁ * q.1 + d₂ * q.2 = p.1)).card : ℤ) else 0 := by
    intro p _; split_ifs <;> simp
  rw [Finset.sum_congr rfl hrew, ← Finset.sum_filter]
  norm_cast
  rw [← Finset.card_sigma]
  refine Finset.card_bij (fun x _ => (x.2.1, x.2.2, x.1.2 / d₃)) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_antidiagonal,
      Finset.mem_product, Finset.mem_range] at hx ⊢
    have hq3 : d₃ * (x.1.2 / d₃) = x.1.2 := Nat.mul_div_cancel' hx.1.2
    exact ⟨⟨by omega, by omega, Nat.lt_succ_of_le (le_trans (Nat.div_le_self _ _) (by omega))⟩,
      by omega⟩
  · intro x₁ hx₁ x₂ hx₂ h
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_antidiagonal] at hx₁ hx₂
    rcases Prod.mk.inj h with ⟨ha, hbc⟩
    rcases Prod.mk.inj hbc with ⟨hb, hc⟩
    have hq3_1 : d₃ * (x₁.1.2 / d₃) = x₁.1.2 := Nat.mul_div_cancel' hx₁.1.2
    have hq3_2 : d₃ * (x₂.1.2 / d₃) = x₂.1.2 := Nat.mul_div_cancel' hx₂.1.2
    have hx12 : x₁.1.2 = x₂.1.2 := by rw [← hq3_1, ← hq3_2, hc]
    have hx11 : x₁.1.1 = x₂.1.1 := by omega
    have hfst : x₁.1 = x₂.1 := Prod.ext hx11 hx12
    have hsnd : x₁.2 = x₂.2 := Prod.ext ha hb
    rcases x₁ with ⟨p₁, q₁⟩; rcases x₂ with ⟨p₂, q₂⟩
    simp only at hfst hsnd; subst hfst; subst hsnd; rfl
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at ht
    refine ⟨⟨(d₁ * t.1 + d₂ * t.2.1, d₃ * t.2.2), (t.1, t.2.1)⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_antidiagonal,
        Finset.mem_product, Finset.mem_range]
      have hlt1 : t.1 < d₁ * t.1 + d₂ * t.2.1 + 1 := by nlinarith
      have hlt2 : t.2.1 < d₁ * t.1 + d₂ * t.2.1 + 1 := by nlinarith
      exact ⟨⟨ht.2, dvd_mul_right d₃ t.2.2⟩, ⟨hlt1, hlt2⟩, trivial⟩
    · exact Prod.ext rfl (Prod.ext rfl (Nat.mul_div_cancel_left t.2.2 (by omega)))

private lemma count1_ps :
    PowerSeries.mk (fun n => (count1 n : ℤ)) = geomPS 2 * geomPS 1 * geomPS 2 := by
  ext n
  rw [PowerSeries.coeff_mk, coeff_triple_geom 2 1 2 (by omega) (by omega) (by omega) n]
  unfold count1
  simp only [one_mul]

private lemma count2_ps :
    PowerSeries.mk (fun n => (count2 n : ℤ)) =
      (PowerSeries.X : PowerSeries ℤ) ^ 3 * (geomPS 3 * geomPS 2 * geomPS 1) := by
  ext n
  rw [PowerSeries.coeff_mk]
  have hmul : PowerSeries.coeff n ((PowerSeries.X : PowerSeries ℤ) ^ 3 * (geomPS 3 * geomPS 2 * geomPS 1)) =
      if 3 ≤ n then PowerSeries.coeff (n - 3) (geomPS 3 * geomPS 2 * geomPS 1) else 0 := by
    rw [PowerSeries.coeff_mul]
    split_ifs with h
    · rw [Finset.sum_eq_single (3, n - 3)]
      · simp [PowerSeries.coeff_X_pow]
      · rintro ⟨a, b⟩ hab hne
        rw [Finset.mem_antidiagonal] at hab
        have ha3 : a ≠ 3 := fun ha => hne (Prod.ext ha (by omega))
        dsimp only
        rw [PowerSeries.coeff_X_pow, if_neg ha3, zero_mul]
      · intro hnot; exact absurd (Finset.mem_antidiagonal.mpr (by omega)) hnot
    · refine Finset.sum_eq_zero fun ⟨a, b⟩ hab => ?_
      rw [Finset.mem_antidiagonal] at hab
      have ha3 : a ≠ 3 := by omega
      dsimp only
      rw [PowerSeries.coeff_X_pow, if_neg ha3, zero_mul]
  rw [hmul]
  split_ifs with h3
  · rw [coeff_triple_geom 3 2 1 (by omega) (by omega) (by omega) (n - 3)]
    unfold count2
    norm_cast
    refine Finset.card_bij (fun t _ => (t.1 - 1, t.2.1, t.2.2)) ?_ ?_ ?_
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at ht ⊢
      omega
    · intro t₁ ht₁ t₂ ht₂ h
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at ht₁ ht₂
      rcases Prod.mk.inj h with ⟨h1, h23⟩
      rcases Prod.mk.inj h23 with ⟨h2, h3'⟩
      rcases t₁ with ⟨a₁, b₁, c₁⟩; rcases t₂ with ⟨a₂, b₂, c₂⟩
      simp only at h1 h2 h3' ht₁ ht₂ ⊢
      exact Prod.ext (by omega) (Prod.ext h2 h3')
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hs
      rcases s with ⟨a, b, c⟩
      simp only at hs
      refine ⟨(a + 1, b, c), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        omega
      · exact Prod.ext (by omega) (Prod.ext rfl rfl)
  · unfold count2
    have hemp : (((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
        (fun t : ℕ × ℕ × ℕ => 1 ≤ t.1 ∧ 3 * t.1 + 2 * t.2.1 + t.2.2 = n)) = ∅ := by
      ext t
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
      omega
    rw [hemp, Finset.card_empty, Nat.cast_zero]

private lemma prove_main :
    ((1 - PowerSeries.X) * (1 - PowerSeries.X ^ 2) ^ 2 * (1 - PowerSeries.X ^ 3)) *
      PowerSeries.mk (fun n => (A008368 n : ℤ)) =
      1 - PowerSeries.X ^ 5 := by
  have hA : PowerSeries.mk (fun n => (A008368 n : ℤ)) =
      PowerSeries.mk (fun n => (count1 n : ℤ)) + PowerSeries.mk (fun n => (count2 n : ℤ)) := by
    ext n
    simp [A008368_eq_add]
  rw [hA, count1_ps, count2_ps, mul_add]
  have hg1 : (1 - (PowerSeries.X : PowerSeries ℤ)) * geomPS 1 = 1 := by
    simpa [pow_one] using one_sub_X_pow_mul_geomPS 1 (by omega)
  have hg2 : (1 - (PowerSeries.X : PowerSeries ℤ) ^ 2) * geomPS 2 = 1 :=
    one_sub_X_pow_mul_geomPS 2 (by omega)
  have hg3 : (1 - (PowerSeries.X : PowerSeries ℤ) ^ 3) * geomPS 3 = 1 :=
    one_sub_X_pow_mul_geomPS 3 (by omega)
  have hterm1 :
      ((1 - (PowerSeries.X : PowerSeries ℤ)) * (1 - PowerSeries.X ^ 2) ^ 2 * (1 - PowerSeries.X ^ 3)) *
        (geomPS 2 * geomPS 1 * geomPS 2) = 1 - PowerSeries.X ^ 3 := by
    calc ((1 - (PowerSeries.X : PowerSeries ℤ)) * (1 - PowerSeries.X ^ 2) ^ 2 * (1 - PowerSeries.X ^ 3)) *
          (geomPS 2 * geomPS 1 * geomPS 2)
        = (1 - PowerSeries.X ^ 3) * (((1 - PowerSeries.X) * geomPS 1) *
            ((1 - PowerSeries.X ^ 2) * geomPS 2) * ((1 - PowerSeries.X ^ 2) * geomPS 2)) := by ring
      _ = (1 - PowerSeries.X ^ 3) * (1 * 1 * 1) := by rw [hg1, hg2]
      _ = 1 - PowerSeries.X ^ 3 := by ring
  have hterm2 :
      ((1 - (PowerSeries.X : PowerSeries ℤ)) * (1 - PowerSeries.X ^ 2) ^ 2 * (1 - PowerSeries.X ^ 3)) *
        (PowerSeries.X ^ 3 * (geomPS 3 * geomPS 2 * geomPS 1)) =
        (1 - PowerSeries.X ^ 2) * PowerSeries.X ^ 3 := by
    calc ((1 - (PowerSeries.X : PowerSeries ℤ)) * (1 - PowerSeries.X ^ 2) ^ 2 * (1 - PowerSeries.X ^ 3)) *
          (PowerSeries.X ^ 3 * (geomPS 3 * geomPS 2 * geomPS 1))
        = (1 - PowerSeries.X ^ 2) * PowerSeries.X ^ 3 *
            (((1 - PowerSeries.X) * geomPS 1) * ((1 - PowerSeries.X ^ 2) * geomPS 2) *
              ((1 - PowerSeries.X ^ 3) * geomPS 3)) := by ring
      _ = (1 - PowerSeries.X ^ 2) * PowerSeries.X ^ 3 * (1 * 1 * 1) := by rw [hg1, hg2, hg3]
      _ = (1 - PowerSeries.X ^ 2) * PowerSeries.X ^ 3 := by ring
  rw [hterm1, hterm2]
  ring

end OMA.P_oeis_a008368

theorem OMA.solution : type_of% @OMA.S_oeis_a008368.main :=
  OMA.P_oeis_a008368.prove_main

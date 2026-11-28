import OMAStatements.S_arxiv_1911_00555

open OMA.S_arxiv_1911_00555

namespace OMA.P_arxiv_1911_00555

/-! ### 1. Basic properties of torsion-free groups and power graphs -/

private lemma zpow_eq_one_iff {G : Type*} [Group G] (htf : IsTorsionFreeGroup G)
    {x : G} (hx : x ≠ 1) (n : ℤ) : x ^ n = 1 ↔ n = 0 := by
  constructor
  · intro h
    cases n with
    | ofNat k =>
      cases k with
      | zero => rfl
      | succ k =>
        exfalso
        exact hx (htf x (k + 1) (Nat.succ_pos k) (by rw [← zpow_natCast]; exact h))
    | negSucc k =>
      exfalso
      have h1 : x ^ (k + 1) = 1 := by
        have : (x ^ (k + 1))⁻¹ = 1 := by simpa [zpow_negSucc] using h
        simpa using congrArg Inv.inv this
      exact hx (htf x (k + 1) (Nat.succ_pos k) h1)
  · rintro rfl; exact zpow_zero x

private lemma zpow_inj {G : Type*} [Group G] (htf : IsTorsionFreeGroup G)
    {x : G} (hx : x ≠ 1) {m n : ℤ} (h : x ^ m = x ^ n) : m = n := by
  have h1 : x ^ (m - n) = 1 := by rw [zpow_sub, h, mul_inv_cancel]
  have h0 := (zpow_eq_one_iff htf hx (m - n)).mp h1
  omega

private lemma inv_ne_self_of_tf {G : Type*} [Group G] (htf : IsTorsionFreeGroup G)
    {x : G} (hx : x ≠ 1) : x⁻¹ ≠ x := by
  intro h
  have h2 : x ^ 2 = 1 := by
    calc x ^ 2 = x * x := sq x
      _ = x⁻¹ * x := by nth_rw 1 [← h]
      _ = 1 := inv_mul_cancel x
  exact hx (htf x 2 (by omega) h2)

private lemma powerAdj_symm {G : Type*} [Group G] {x y : G} (h : PowerAdj x y) : PowerAdj y x := by
  rcases h with ⟨hne, n, h1 | h2⟩
  · exact ⟨hne.symm, n, Or.inr h1⟩
  · exact ⟨hne.symm, n, Or.inl h2⟩

private lemma powerAdj_one_left {G : Type*} [Group G] {x : G} (hx : x ≠ 1) : PowerAdj (1 : G) x :=
  ⟨hx.symm, 0, Or.inr (zpow_zero x).symm⟩

private lemma powerAdj_one_right {G : Type*} [Group G] {x : G} (hx : x ≠ 1) : PowerAdj x (1 : G) :=
  ⟨hx, 0, Or.inl (zpow_zero x).symm⟩

/-- Nonzero-exponent directed adjacency. -/
private def NzDir {G : Type*} [Group G] (x y : G) : Prop :=
  x ≠ y ∧ ∃ n : ℤ, n ≠ 0 ∧ y = x ^ n

/-- Nonzero-exponent undirected adjacency. -/
private def NzAdj {G : Type*} [Group G] (x y : G) : Prop :=
  x ≠ y ∧ ∃ n : ℤ, n ≠ 0 ∧ (y = x ^ n ∨ x = y ^ n)

private lemma nzAdj_symm {G : Type*} [Group G] {x y : G} (h : NzAdj x y) : NzAdj y x := by
  rcases h with ⟨hne, n, hn, h1 | h2⟩
  · exact ⟨hne.symm, n, hn, Or.inr h1⟩
  · exact ⟨hne.symm, n, hn, Or.inl h2⟩

private lemma powerAdj_iff_nzAdj {G : Type*} [Group G] {x y : G} (hx : x ≠ 1) (hy : y ≠ 1) :
    PowerAdj x y ↔ NzAdj x y := by
  constructor
  · rintro ⟨hne, n, h | h⟩
    · refine ⟨hne, n, ?_, Or.inl h⟩
      rintro rfl; simp at h; exact hy h
    · refine ⟨hne, n, ?_, Or.inr h⟩
      rintro rfl; simp at h; exact hx h
  · rintro ⟨hne, n, _, h⟩
    exact ⟨hne, n, h⟩

private lemma dirPowerAdj_iff_nzDir {G : Type*} [Group G] {x y : G} (hy : y ≠ 1) :
    DirPowerAdj x y ↔ NzDir x y := by
  constructor
  · rintro ⟨hne, n, h⟩
    refine ⟨hne, n, ?_, h⟩
    rintro rfl; simp at h; exact hy h
  · rintro ⟨hne, n, _, h⟩
    exact ⟨hne, n, h⟩

/-- Closed-neighborhood equivalence in the undirected power graph. -/
private def SameNhd {G : Type*} [Group G] (x y : G) : Prop :=
  ∀ z : G, (z = x ∨ PowerAdj x z) ↔ (z = y ∨ PowerAdj y z)

private lemma sameNhd_refl {G : Type*} [Group G] (x : G) : SameNhd x x := fun _ => Iff.rfl

private lemma sameNhd_symm {G : Type*} [Group G] {x y : G} (h : SameNhd x y) : SameNhd y x :=
  fun z => (h z).symm

private lemma sameNhd_trans {G : Type*} [Group G] {x y z : G}
    (h1 : SameNhd x y) (h2 : SameNhd y z) : SameNhd x z :=
  fun w => (h1 w).trans (h2 w)

private lemma sameNhd_inv {G : Type*} [Group G] (x : G) : SameNhd x x⁻¹ := by
  intro z
  by_cases hzx : z = x
  · rw [hzx]
    by_cases hxi : x = x⁻¹
    · rw [← hxi]
    · simp only [true_or, true_iff]; right
      exact ⟨Ne.symm hxi, -1, Or.inl (by simp)⟩
  · by_cases hzi : z = x⁻¹
    · rw [hzi]
      simp only [true_or, iff_true]; right
      exact ⟨fun h => hzx (hzi.trans h.symm), -1, Or.inl (by simp)⟩
    · simp only [hzx, hzi, false_or]
      constructor
      · rintro ⟨_, n, h | h⟩
        · exact ⟨Ne.symm hzi, -n, Or.inl (by rw [h, zpow_neg, inv_zpow, inv_inv])⟩
        · exact ⟨Ne.symm hzi, -n, Or.inr (by rw [zpow_neg, ← h])⟩
      · rintro ⟨_, n, h | h⟩
        · exact ⟨Ne.symm hzx, -n, Or.inl (by rw [h, inv_zpow, zpow_neg])⟩
        · exact ⟨Ne.symm hzx, -n, Or.inr (by rw [zpow_neg, ← h, inv_inv])⟩

private lemma sameNhd_of_iso {G H : Type*} [Group G] [Group H]
    (f : G ≃ H) (hf : ∀ x y, PowerAdj x y ↔ PowerAdj (f x) (f y)) {x y : G} :
    SameNhd x y ↔ SameNhd (f x) (f y) := by
  constructor
  · intro h w
    have := h (f.symm w)
    rw [hf, hf, f.apply_symm_apply] at this
    simpa [Equiv.symm_apply_eq] using this
  · intro h z
    have := h (f z)
    rw [← hf, ← hf] at this
    simpa [f.injective.eq_iff] using this

/-- Center of the undirected power graph: vertices adjacent to every other vertex. -/
private def InCenter {G : Type*} [Group G] (x : G) : Prop :=
  ∀ y : G, y ≠ x → PowerAdj x y

private lemma one_inCenter {G : Type*} [Group G] : InCenter (1 : G) :=
  fun _ hy => powerAdj_one_left hy

private lemma inCenter_of_iso {G H : Type*} [Group G] [Group H]
    (f : G ≃ H) (hf : ∀ x y, PowerAdj x y ↔ PowerAdj (f x) (f y)) {x : G} :
    InCenter x ↔ InCenter (f x) := by
  constructor
  · intro hx y hy
    have h1 : f.symm y ≠ x := fun h => hy (by rw [← h, f.apply_symm_apply])
    have := (hf x (f.symm y)).mp (hx (f.symm y) h1)
    rwa [f.apply_symm_apply] at this
  · intro hfx y hy
    exact (hf x y).mpr (hfx (f y) (fun h => hy (f.injective h)))

private lemma sameNhd_of_inCenter {G : Type*} [Group G] {x y : G}
    (hx : InCenter x) (hy : InCenter y) : SameNhd x y := by
  intro z
  by_cases hzx : z = x <;> by_cases hzy : z = y
  · exact ⟨fun _ => Or.inl hzy, fun _ => Or.inl hzx⟩
  · simp only [hzx, true_or, true_iff]; exact Or.inr (hy x (hzx ▸ hzy))
  · simp only [hzy, true_or, iff_true]; exact Or.inr (hx y (hzy ▸ hzx))
  · simp only [hzx, hzy, false_or, hx z hzx, hy z hzy]

private lemma inCenter_of_sameNhd_one {G : Type*} [Group G] {x : G}
    (h : SameNhd x 1) : InCenter x := by
  intro y hy
  have h1 := (h y).mpr ((em (y = 1)).imp id powerAdj_one_left)
  rcases h1 with rfl | hp
  · exact absurd rfl hy
  · exact hp

/-- Every non-identity element in a torsion-free group cannot be `SameNhd` with anything
outside `{x, x⁻¹}` unless `x ∈ InCenter`. -/
private lemma sameNhd_tf_eq_or_inv {G : Type*} [Group G] (htf : IsTorsionFreeGroup G)
    {x y : G} (hx : x ≠ 1) (hy : y ≠ 1) (h : SameNhd x y) : y = x ∨ y = x⁻¹ := by
  by_contra hnot
  push Not at hnot
  have hyx : y ≠ x := hnot.1
  have hyxi : y ≠ x⁻¹ := hnot.2
  have hxy : PowerAdj x y := by
    have := (h y).mpr (Or.inl rfl)
    rcases this with h1 | h2
    · exact absurd h1 hyx
    · exact h2
  rcases (powerAdj_iff_nzAdj hx hy).mp hxy with ⟨_, k, hk0, hkx | hky⟩
  · -- `y = x ^ k`, with `|k| ≥ 2`
    have hk_abs : 2 ≤ k.natAbs := by
      by_contra hlt
      have h1 : k = 1 ∨ k = -1 := by omega
      rcases h1 with rfl | rfl
      · exact hyx (by simpa using hkx)
      · exact hyxi (by simpa using hkx)
    let m : ℤ := (k.natAbs : ℤ) + 1
    have hm_ge3 : 3 ≤ m := by omega
    let w : G := x ^ m
    have hwx : PowerAdj x w := ⟨fun h1 => by
      have : (1 : ℤ) = m := zpow_inj htf hx (by simpa [w] using h1)
      omega, m, Or.inl rfl⟩
    have hw_ne_y : w ≠ y := by
      intro hwy
      have : m = k := zpow_inj htf hx (by simpa [w, hkx] using hwy)
      omega
    have hwy : PowerAdj y w := by
      have := (h w).mp (Or.inr hwx)
      rcases this with h1 | h2
      · exact absurd h1 hw_ne_y
      · exact h2
    rcases (powerAdj_iff_nzAdj hy (by
      intro h1; have := (zpow_eq_one_iff htf hx m).mp h1; omega)).mp hwy with ⟨_, r, hr0, h1 | h2⟩
    · -- `x ^ m = (x ^ k) ^ r = x ^ (k * r)`
      have hkr : m = k * r := zpow_inj htf hx (by simpa [w, hkx, zpow_mul] using h1)
      have hdvd : (k.natAbs : ℤ) ∣ m := by
        rcases Int.natAbs_eq k with hk1 | hk2
        · exact ⟨r, by rw [← hk1]; exact hkr⟩
        · have : k * r = (k.natAbs : ℤ) * (-r) := by
            calc k * r = (-(k.natAbs : ℤ)) * r := by conv_lhs => rw [hk2]
              _ = (k.natAbs : ℤ) * (-r) := by ring
          exact ⟨-r, hkr.trans this⟩
      have hdvd1 : (k.natAbs : ℤ) ∣ 1 := by
        have hsub : (k.natAbs : ℤ) ∣ m - (k.natAbs : ℤ) := dvd_sub hdvd dvd_rfl
        simpa [m] using hsub
      have hle : k.natAbs ≤ 1 := by
        have := Int.le_of_dvd (by omega) hdvd1; omega
      omega
    · -- `x ^ k = (x ^ m) ^ r = x ^ (m * r)`
      have hmr : k = m * r := zpow_inj htf hx (by simpa [w, hkx, zpow_mul] using h2)
      have h1 : m ≤ k.natAbs := by
        have hpos : 1 ≤ r.natAbs := Int.natAbs_pos.mpr hr0
        have heq : k.natAbs = m.natAbs * r.natAbs := by
          rw [hmr, Int.natAbs_mul]
        have hmabs : m.natAbs = k.natAbs + 1 := by omega
        nlinarith
      omega
  · -- `x = y ^ k`, symmetric
    have hk_abs : 2 ≤ k.natAbs := by
      by_contra hlt
      have h1 : k = 1 ∨ k = -1 := by omega
      rcases h1 with rfl | rfl
      · exact hyx (by simpa using hky.symm)
      · exact hyxi (by rw [show x = y⁻¹ by simpa using hky, inv_inv])
    let m : ℤ := (k.natAbs : ℤ) + 1
    let w : G := y ^ m
    have hwy : PowerAdj y w := ⟨fun h1 => by
      have : (1 : ℤ) = m := zpow_inj htf hy (by simpa [w] using h1)
      omega, m, Or.inl rfl⟩
    have hw_ne_x : w ≠ x := by
      intro hwx
      have : m = k := zpow_inj htf hy (by simpa [w, hky] using hwx)
      omega
    have hwx : PowerAdj x w := by
      have := (h w).mpr (Or.inr hwy)
      rcases this with h1 | h2
      · exact absurd h1 hw_ne_x
      · exact h2
    rcases (powerAdj_iff_nzAdj hx (by
      intro h1; have := (zpow_eq_one_iff htf hy m).mp h1; omega)).mp hwx with ⟨_, r, hr0, h1 | h2⟩
    · have hkr : m = k * r := zpow_inj htf hy (by simpa [w, hky, zpow_mul] using h1)
      have hdvd : (k.natAbs : ℤ) ∣ m := by
        rcases Int.natAbs_eq k with hk1 | hk2
        · exact ⟨r, by rw [← hk1]; exact hkr⟩
        · have : k * r = (k.natAbs : ℤ) * (-r) := by
            calc k * r = (-(k.natAbs : ℤ)) * r := by conv_lhs => rw [hk2]
              _ = (k.natAbs : ℤ) * (-r) := by ring
          exact ⟨-r, hkr.trans this⟩
      have hdvd1 : (k.natAbs : ℤ) ∣ 1 := by
        have hsub : (k.natAbs : ℤ) ∣ m - (k.natAbs : ℤ) := dvd_sub hdvd dvd_rfl
        simpa [m] using hsub
      have hle : k.natAbs ≤ 1 := by
        have := Int.le_of_dvd (by omega) hdvd1; omega
      omega
    · have hmr : k = m * r := zpow_inj htf hy (by simpa [w, hky, zpow_mul] using h2)
      have h1 : m ≤ k.natAbs := by
        have hpos : 1 ≤ r.natAbs := Int.natAbs_pos.mpr hr0
        have heq : k.natAbs = m.natAbs * r.natAbs := by
          rw [hmr, Int.natAbs_mul]
        have hmabs : m.natAbs = k.natAbs + 1 := by omega
        nlinarith
      omega

/-- In any group, if `x` has infinite order and `InCenter x`, then `x` generates the whole group. -/
private lemma cyclic_of_inCenter_infOrd {G : Type*} [Group G] {a : G}
    (ha_inf : ∀ n : ℤ, a ^ n = 1 → n = 0) (ha_cen : InCenter a) :
    ∀ y : G, ∃ n : ℤ, y = a ^ n := by
  intro y
  by_cases hya : y = a
  · exact ⟨1, by simp [hya]⟩
  · by_contra hnot
    have hya_adj := ha_cen y hya
    rcases hya_adj with ⟨_, k, h1 | h2⟩
    · exact hnot ⟨k, h1⟩
    · -- `a = y ^ k` with `|k| ≥ 2`
      have hy_inf : ∀ n : ℤ, y ^ n = 1 → n = 0 := by
        intro n hn
        have hk0 : k ≠ 0 := by rintro rfl; simp at h2; exact absurd (ha_inf 1 (by simpa using h2)) (by omega)
        have : a ^ n = 1 := by rw [h2, ← zpow_mul, mul_comm, zpow_mul, hn, one_zpow]
        exact ha_inf n this
      have hy_inj : ∀ m n : ℤ, y ^ m = y ^ n → m = n := fun m n h => by
        have : y ^ (m - n) = 1 := by rw [zpow_sub, h, mul_inv_cancel]
        have := hy_inf (m - n) this; omega
      have hk_abs : 2 ≤ k.natAbs := by
        by_contra hlt
        have hk0 : k ≠ 0 := by rintro rfl; simp at h2; exact absurd (ha_inf 1 (by simpa using h2)) (by omega)
        have h1 : k = 1 ∨ k = -1 := by omega
        rcases h1 with rfl | rfl
        · exact hya (by simpa using h2.symm)
        · exact hnot ⟨-1, by rw [show a = y⁻¹ by simpa using h2, zpow_neg_one, inv_inv]⟩
      let m : ℤ := (k.natAbs : ℤ) + 1
      let w : G := y ^ m
      have hwa : w ≠ a := by
        intro h1; have := hy_inj m k (by simpa [w, h2] using h1); omega
      rcases ha_cen w hwa with ⟨_, r, hr1 | hr2⟩
      · have hkr : m = k * r := hy_inj m (k * r) (by simpa [w, h2, zpow_mul] using hr1)
        have hdvd : (k.natAbs : ℤ) ∣ m := by
          rcases Int.natAbs_eq k with hk1 | hk2
          · exact ⟨r, by rw [← hk1]; exact hkr⟩
          · have : k * r = (k.natAbs : ℤ) * (-r) := by
              calc k * r = (-(k.natAbs : ℤ)) * r := by conv_lhs => rw [hk2]
                _ = (k.natAbs : ℤ) * (-r) := by ring
            exact ⟨-r, hkr.trans this⟩
        have hdvd1 : (k.natAbs : ℤ) ∣ 1 := by
          have hsub : (k.natAbs : ℤ) ∣ m - (k.natAbs : ℤ) := dvd_sub hdvd dvd_rfl
          simpa [m] using hsub
        have hle : k.natAbs ≤ 1 := by
          have := Int.le_of_dvd (by omega) hdvd1; omega
        omega
      · have hmr : k = m * r := hy_inj k (m * r) (by simpa [w, h2, zpow_mul] using hr2)
        have hr0 : r ≠ 0 := by rintro rfl; simp at hmr; omega
        have hpos : 1 ≤ r.natAbs := Int.natAbs_pos.mpr hr0
        have heq : k.natAbs = m.natAbs * r.natAbs := by rw [hmr, Int.natAbs_mul]
        have hmabs : m.natAbs = k.natAbs + 1 := by omega
        nlinarith

/-- If `z` has finite order `d ≥ 1` in any group, then `z ^ t` has the same closed neighborhood
as `z` for every `t` coprime to `d`. -/
private lemma sameNhd_pow_coprime {H : Type*} [Group H] {z : H} {d t : ℕ}
    (hd : orderOf z = d) (hcop : Nat.Coprime t d) : SameNhd z (z ^ t) := by
  have hgen : ∃ s : ℤ, (z ^ t) ^ s = z := by
    have huv := Nat.gcd_eq_gcd_ab t d
    rw [hcop] at huv
    refine ⟨Nat.gcdA t d, ?_⟩
    rw [← zpow_natCast, ← zpow_mul]
    have hzd : z ^ (d : ℤ) = 1 := by rw [zpow_natCast, ← hd, pow_orderOf_eq_one]
    have : z ^ ((t : ℤ) * Nat.gcdA t d) = z ^ ((1 : ℤ) - (d : ℤ) * Nat.gcdB t d) := by
      push_cast at huv; congr 1; linarith
    rw [this, zpow_sub, zpow_one, zpow_mul, hzd, one_zpow, inv_one, mul_one]
  obtain ⟨s, hs⟩ := hgen
  intro w
  by_cases hwz : w = z
  · rw [hwz]
    by_cases hzt : z = z ^ t
    · rw [← hzt]
    · simp only [true_or, true_iff]; right
      exact ⟨Ne.symm hzt, s, Or.inl hs.symm⟩
  · by_cases hwzt : w = z ^ t
    · rw [hwzt]
      simp only [true_or, iff_true]; right
      exact ⟨fun h => hwz (hwzt.trans h.symm), (t : ℤ), Or.inl (by simp)⟩
    · simp only [hwz, hwzt, false_or]
      constructor
      · rintro ⟨_, n, h | h⟩
        · exact ⟨Ne.symm hwzt, s * n, Or.inl (by rw [h, zpow_mul, hs])⟩
        · exact ⟨Ne.symm hwzt, n * (t : ℤ), Or.inr (by rw [zpow_mul, ← h, zpow_natCast])⟩
      · rintro ⟨_, n, h | h⟩
        · exact ⟨Ne.symm hwz, (t : ℤ) * n, Or.inl (by rw [h, zpow_mul, zpow_natCast])⟩
        · exact ⟨Ne.symm hwz, n * s, Or.inr (by rw [zpow_mul, ← h, hs])⟩

private lemma sameNhd_card_le_three_of_tf {G : Type*} [Group G] (htf : IsTorsionFreeGroup G)
    (x : G) : ∀ a b c d : G,
      SameNhd x a → SameNhd x b → SameNhd x c → SameNhd x d →
      a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d := by
  intro a b c d ha hb hc hd
  by_contra hnot
  push Not at hnot
  rcases hnot with ⟨hab, hac, had, hbc, hbd, hcd⟩
  -- At most one of `{a, b, c, d}` can equal `1`; hence at least 3 are `≠ 1`!
  have htri : ∀ u v w : G, u ≠ 1 → v ≠ 1 → w ≠ 1 →
      SameNhd u v → SameNhd u w → u = v ∨ u = w ∨ v = w := by
    intro u v w hu hv hw huv huw
    rcases sameNhd_tf_eq_or_inv htf hu hv huv with rfl | rfl
    · exact Or.inl rfl
    · rcases sameNhd_tf_eq_or_inv htf hu hw huw with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  by_cases ha1 : a = 1
  · have hb1 : b ≠ 1 := fun h => hab (ha1.trans h.symm)
    have hc1 : c ≠ 1 := fun h => hac (ha1.trans h.symm)
    have hd1 : d ≠ 1 := fun h => had (ha1.trans h.symm)
    rcases htri b c d hb1 hc1 hd1 (sameNhd_trans (sameNhd_symm hb) hc)
      (sameNhd_trans (sameNhd_symm hb) hd) with h | h | h
    · exact hbc h
    · exact hbd h
    · exact hcd h
  · by_cases hb1 : b = 1
    · have hc1 : c ≠ 1 := fun h => hbc (hb1.trans h.symm)
      have hd1 : d ≠ 1 := fun h => hbd (hb1.trans h.symm)
      rcases htri a c d ha1 hc1 hd1 (sameNhd_trans (sameNhd_symm ha) hc)
        (sameNhd_trans (sameNhd_symm ha) hd) with h | h | h
      · exact hac h
      · exact had h
      · exact hcd h
    · by_cases hc1 : c = 1
      · have hd1 : d ≠ 1 := fun h => hcd (hc1.trans h.symm)
        rcases htri a b d ha1 hb1 hd1 (sameNhd_trans (sameNhd_symm ha) hb)
          (sameNhd_trans (sameNhd_symm ha) hd) with h | h | h
        · exact hab h
        · exact had h
        · exact hbd h
      · rcases htri a b c ha1 hb1 hc1 (sameNhd_trans (sameNhd_symm ha) hb)
          (sameNhd_trans (sameNhd_symm ha) hc) with h | h | h
        · exact hab h
        · exact hac h
        · exact hbc h

/-- If every `SameNhd`-class in `H` has size at most 3, then every finite-order element
has order in `{1, 2, 3, 4, 6}`. -/
private lemma finite_order_mem_12346 {H : Type*} [Group H]
    (h3 : ∀ x a b c d : H, SameNhd x a → SameNhd x b → SameNhd x c → SameNhd x d →
      a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d)
    {z : H} (hfin : IsOfFinOrder z) :
    orderOf z = 1 ∨ orderOf z = 2 ∨ orderOf z = 3 ∨ orderOf z = 4 ∨ orderOf z = 6 := by
  set d := orderOf z
  have hd_pos : 0 < d := orderOf_pos_iff.mpr hfin
  by_contra hnot
  push Not at hnot
  have hphi_ge4 : 4 ≤ Nat.totient d := by
    by_cases hd5 : d = 5
    · rw [hd5]; decide
    · by_cases hd7 : d = 7
      · rw [hd7]; decide
      · by_cases hd8 : d = 8
        · rw [hd8]; decide
        · by_cases hd9 : d = 9
          · rw [hd9]; decide
          · by_cases hd10 : d = 10
            · rw [hd10]; decide
            · by_cases hd12 : d = 12
              · rw [hd12]; decide
              · have hd_ge7 : 7 ≤ d := by omega
                have hcop_sub : ∀ a b : ℕ, b < a → Nat.Coprime a b → Nat.Coprime a (a - b) := by
                  intro a b hba hc
                  rw [Nat.Coprime] at hc ⊢
                  have h1 : a.gcd (a - b) = b.gcd (a - b) := by
                    have := Nat.gcd_add_self_left (a - b) b
                    rwa [Nat.add_sub_of_le (le_of_lt hba)] at this
                  have h2 : a.gcd b = (a - b).gcd b := by
                    have := Nat.gcd_add_self_left b (a - b)
                    rwa [Nat.sub_add_cancel (le_of_lt hba)] at this
                  rw [h1, Nat.gcd_comm, ← h2]
                  exact hc
                rw [Nat.totient_eq_card_coprime]
                by_cases hodd : d % 2 = 1
                · have hc1 : d.Coprime 1 := Nat.coprime_one_right d
                  have hc2 : d.Coprime 2 :=
                    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two |>.mpr (by omega)).symm
                  have hc3 : d.Coprime (d - 2) := hcop_sub d 2 (by omega) hc2
                  have hc4 : d.Coprime (d - 1) := hcop_sub d 1 (by omega) hc1
                  have hsub : ({1, 2, d - 2, d - 1} : Finset ℕ) ⊆ (Finset.range d).filter d.Coprime := by
                    intro x hx
                    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
                    rcases hx with rfl | rfl | rfl | rfl <;> assumption
                  have hcard4 : ({1, 2, d - 2, d - 1} : Finset ℕ).card = 4 := by
                    rw [Finset.card_insert_of_notMem (by simp; omega),
                        Finset.card_insert_of_notMem (by simp; omega),
                        Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
                  exact le_trans (by rw [hcard4]) (Finset.card_le_card hsub)
                · have hd14 : 14 ≤ d := by omega
                  set k := d / 2
                  have hdk : d = 2 * k := by omega
                  have hc1 : d.Coprime 1 := Nat.coprime_one_right d
                  have hc4 : d.Coprime (d - 1) := hcop_sub d 1 (by omega) hc1
                  have hex : ∃ t, 1 < t ∧ t < k ∧ d.Coprime t := by
                    by_cases hk : k % 2 = 0
                    · refine ⟨k - 1, by omega, by omega, ?_⟩
                      rw [hdk]
                      refine Nat.Coprime.mul_left ?_ ?_
                      · exact Nat.Prime.coprime_iff_not_dvd Nat.prime_two |>.mpr (by omega)
                      · exact hcop_sub k 1 (by omega) (Nat.coprime_one_right k)
                    · refine ⟨k - 2, by omega, by omega, ?_⟩
                      rw [hdk]
                      refine Nat.Coprime.mul_left ?_ ?_
                      · exact Nat.Prime.coprime_iff_not_dvd Nat.prime_two |>.mpr (by omega)
                      · exact hcop_sub k 2 (by omega)
                          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two |>.mpr (by omega)).symm)
                  obtain ⟨t, ht1, htk, htc⟩ := hex
                  have htc2 : d.Coprime (d - t) := hcop_sub d t (by omega) htc
                  have hsub : ({1, t, d - t, d - 1} : Finset ℕ) ⊆ (Finset.range d).filter d.Coprime := by
                    intro x hx
                    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
                    rcases hx with rfl | rfl | rfl | rfl <;> assumption
                  have hcard4 : ({1, t, d - t, d - 1} : Finset ℕ).card = 4 := by
                    rw [Finset.card_insert_of_notMem (by simp; omega),
                        Finset.card_insert_of_notMem (by simp; omega),
                        Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
                  exact le_trans (by rw [hcard4]) (Finset.card_le_card hsub)
  -- Pick 4 distinct elements from `(Finset.range d).filter d.Coprime`
  rw [Nat.totient_eq_card_coprime] at hphi_ge4
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hphi_ge4
  obtain ⟨t1, ht1, hcard1⟩ : ∃ t1 ∈ S, (S.erase t1).card = 3 := by
    obtain ⟨t1, ht1⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    exact ⟨t1, ht1, by rw [Finset.card_erase_of_mem ht1, hScard]⟩
  obtain ⟨t2, ht2, hcard2⟩ : ∃ t2 ∈ S.erase t1, ((S.erase t1).erase t2).card = 2 := by
    obtain ⟨t2, ht2⟩ := Finset.card_pos.mp (by omega : 0 < (S.erase t1).card)
    exact ⟨t2, ht2, by rw [Finset.card_erase_of_mem ht2, hcard1]⟩
  obtain ⟨t3, ht3, hcard3⟩ : ∃ t3 ∈ (S.erase t1).erase t2, (((S.erase t1).erase t2).erase t3).card = 1 := by
    obtain ⟨t3, ht3⟩ := Finset.card_pos.mp (by omega : 0 < ((S.erase t1).erase t2).card)
    exact ⟨t3, ht3, by rw [Finset.card_erase_of_mem ht3, hcard2]⟩
  obtain ⟨t4, ht4⟩ := Finset.card_pos.mp (by omega : 0 < (((S.erase t1).erase t2).erase t3).card)
  have hmem : ∀ t ∈ S, t < d ∧ Nat.Coprime t d := fun t ht => by
    have := Finset.mem_filter.mp (hSsub ht)
    exact ⟨Finset.mem_range.mp this.1, this.2.symm⟩
  have ht2S : t2 ∈ S := Finset.mem_of_mem_erase ht2
  have ht3S : t3 ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht3)
  have ht4S : t4 ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht4))
  have hne12 : t1 ≠ t2 := (Finset.ne_of_mem_erase ht2).symm
  have hne13 : t1 ≠ t3 := (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht3)).symm
  have hne14 : t1 ≠ t4 := (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht4))).symm
  have hne23 : t2 ≠ t3 := (Finset.ne_of_mem_erase ht3).symm
  have hne24 : t2 ≠ t4 := (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht4)).symm
  have hne34 : t3 ≠ t4 := (Finset.ne_of_mem_erase ht4).symm
  have hinj : ∀ a b, a < d → b < d → z ^ a = z ^ b → a = b := fun a b ha hb h => by
    have := pow_inj_mod.mp h
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  have hcol := h3 z (z ^ t1) (z ^ t2) (z ^ t3) (z ^ t4)
    (sameNhd_pow_coprime rfl (hmem t1 ht1).2)
    (sameNhd_pow_coprime rfl (hmem t2 ht2S).2)
    (sameNhd_pow_coprime rfl (hmem t3 ht3S).2)
    (sameNhd_pow_coprime rfl (hmem t4 ht4S).2)
  rcases hcol with h | h | h | h | h | h
  · exact hne12 (hinj _ _ (hmem t1 ht1).1 (hmem t2 ht2S).1 h)
  · exact hne13 (hinj _ _ (hmem t1 ht1).1 (hmem t3 ht3S).1 h)
  · exact hne14 (hinj _ _ (hmem t1 ht1).1 (hmem t4 ht4S).1 h)
  · exact hne23 (hinj _ _ (hmem t2 ht2S).1 (hmem t3 ht3S).1 h)
  · exact hne24 (hinj _ _ (hmem t2 ht2S).1 (hmem t4 ht4S).1 h)
  · exact hne34 (hinj _ _ (hmem t3 ht3S).1 (hmem t4 ht4S).1 h)

/-! ### 2. Case A: `G` has a non-identity central vertex (`G ≅ ℤ ≅ H`) -/

private lemma case_nontrivial_center {G H : Type*} [Group G] [Group H]
    (hGtf : IsTorsionFreeGroup G) (f : G ≃ H)
    (hf : ∀ x y, PowerAdj x y ↔ PowerAdj (f x) (f y))
    {a : G} (ha1 : a ≠ 1) (ha_cen : InCenter a) :
    IsoDirPowerGraph G H := by
  classical
  have ha_inf : ∀ n : ℤ, a ^ n = 1 → n = 0 := fun n h => (zpow_eq_one_iff hGtf ha1 n).mp h
  have hGcyc : ∀ y : G, ∃ n : ℤ, y = a ^ n := cyclic_of_inCenter_infOrd ha_inf ha_cen
  -- Center of `G` is `{1, a, a⁻¹}`
  have hCenG : ∀ x : G, InCenter x ↔ x = 1 ∨ x = a ∨ x = a⁻¹ := by
    intro x
    constructor
    · intro hx
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · have hs : SameNhd a x := sameNhd_of_inCenter ha_cen hx
        rcases sameNhd_tf_eq_or_inv hGtf ha1 hx1 hs with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
    · rintro (rfl | rfl | rfl)
      · exact one_inCenter
      · exact ha_cen
      · intro y hy
        have hs : SameNhd a⁻¹ 1 := sameNhd_trans (sameNhd_symm (sameNhd_inv a))
          (sameNhd_of_inCenter ha_cen one_inCenter)
        exact inCenter_of_sameNhd_one hs y hy
  have hG3 : ∀ x p q r s : H, SameNhd x p → SameNhd x q → SameNhd x r → SameNhd x s →
      p = q ∨ p = r ∨ p = s ∨ q = r ∨ q = s ∨ r = s := by
    intro x p q r s hp hq hr hs
    have hcol := sameNhd_card_le_three_of_tf hGtf (f.symm x) (f.symm p) (f.symm q) (f.symm r) (f.symm s)
      ((sameNhd_of_iso f hf).mpr (by simpa using hp))
      ((sameNhd_of_iso f hf).mpr (by simpa using hq))
      ((sameNhd_of_iso f hf).mpr (by simpa using hr))
      ((sameNhd_of_iso f hf).mpr (by simpa using hs))
    rcases hcol with h | h | h | h | h | h <;> simp [f.symm.injective h]
  -- `Cen(H) = {f 1, f a, f a⁻¹}` has 3 distinct elements, so pick `b ∈ Cen(H) \ {1}`.
  have ha_ne_inv : a⁻¹ ≠ a := inv_ne_self_of_tf hGtf ha1
  have hai_ne_1 : a⁻¹ ≠ 1 := inv_ne_one.mpr ha1
  have hb_ex : ∃ b : H, b ≠ 1 ∧ InCenter b := by
    by_cases h1 : f a ≠ 1
    · exact ⟨f a, h1, (inCenter_of_iso f hf).mp ha_cen⟩
    · push Not at h1
      have h2 : f 1 ≠ 1 := fun h => ha1 (f.injective (h1.trans h.symm))
      exact ⟨f 1, h2, (inCenter_of_iso f hf).mp one_inCenter⟩
  obtain ⟨b, hb1, hb_cen⟩ := hb_ex
  -- `H` is infinite (since `G` is infinite).
  have hHinf : Infinite H := by
    have hGinf : Infinite G := Infinite.of_injective (fun n : ℤ => a ^ n)
      (fun m n h => zpow_inj hGtf ha1 h)
    exact Equiv.infinite_iff f |>.mp hGinf
  -- `Cen(H)` has size 3: every element of `Cen(H)` is in `{f 1, f a, f a⁻¹}`, and all 3 are in `Cen(H)` and distinct.
  have hCenH_iff : ∀ y : H, InCenter y ↔ y = f 1 ∨ y = f a ∨ y = f a⁻¹ := by
    intro y
    rw [← f.apply_symm_apply y, ← inCenter_of_iso f hf, hCenG]
    simp [Equiv.symm_apply_eq]
  -- Prove `b` has infinite order!
  have hb_inf : ∀ n : ℤ, b ^ n = 1 → n = 0 := by
    by_contra hnot
    push Not at hnot
    obtain ⟨n0, hn0_eq, hn0_ne⟩ := hnot
    have hbfin : IsOfFinOrder b := isOfFinOrder_iff_pow_eq_one.mpr ⟨n0.natAbs, Int.natAbs_pos.mpr hn0_ne, by
      rcases Int.natAbs_eq n0 with h1 | h2
      · rw [← zpow_natCast, ← h1]; exact hn0_eq
      · have : b ^ (-(n0.natAbs : ℤ)) = 1 := by rw [← h2]; exact hn0_eq
        rw [zpow_neg, inv_eq_one, zpow_natCast] at this; exact this⟩
    have hord := finite_order_mem_12346 hG3 hbfin
    have hord_ne1 : orderOf b ≠ 1 := fun h => hb1 (orderOf_eq_one_iff.mp h)
    -- Every `z ∈ H` has finite order since `b ∈ Cen(H)` and `b` has finite order
    rcases hord with h1 | h2 | h3 | h4 | h6
    · exact hord_ne1 h1
    · -- `orderOf b = 2`: `b = b⁻¹`, so there is a 3rd element `c ∈ Cen(H) \ {1, b}`!
      have hb_inv : b⁻¹ = b := by
        have : b ^ 2 = 1 := by rw [← h2, pow_orderOf_eq_one]
        calc b⁻¹ = b⁻¹ * 1 := (mul_one _).symm
          _ = b⁻¹ * (b * b) := by rw [← sq, this]
          _ = b := by group
      have hc_ex : ∃ c : H, c ≠ 1 ∧ c ≠ b ∧ InCenter c := by
        have h3ne : f 1 ≠ f a ∧ f 1 ≠ f a⁻¹ ∧ f a ≠ f a⁻¹ :=
          ⟨fun h => ha1 (f.injective h).symm, fun h => hai_ne_1 (f.injective h).symm,
           fun h => ha_ne_inv (f.injective h).symm⟩
        by_cases c1 : f 1 ≠ 1 ∧ f 1 ≠ b
        · exact ⟨f 1, c1.1, c1.2, (hCenH_iff _).mpr (Or.inl rfl)⟩
        · by_cases c2 : f a ≠ 1 ∧ f a ≠ b
          · exact ⟨f a, c2.1, c2.2, (hCenH_iff _).mpr (Or.inr (Or.inl rfl))⟩
          · have hc1 : f 1 = 1 ∨ f 1 = b := by tauto
            have hc2 : f a = 1 ∨ f a = b := by tauto
            refine ⟨f a⁻¹, ?_, ?_, (hCenH_iff _).mpr (Or.inr (Or.inr rfl))⟩
            · intro h; rcases hc1 with h1 | h1 <;> rcases hc2 with h2 | h2
              · exact h3ne.1 (h1.trans h2.symm)
              · exact h3ne.2.1 (h1.trans h.symm)
              · exact h3ne.2.2 (h2.trans h.symm)
              · exact h3ne.1 (h1.trans h2.symm)
            · intro h; rcases hc1 with h1 | h1 <;> rcases hc2 with h2 | h2
              · exact h3ne.1 (h1.trans h2.symm)
              · exact h3ne.2.2 (h2.trans h.symm)
              · exact h3ne.2.1 (h1.trans h.symm)
              · exact h3ne.1 (h1.trans h2.symm)
      obtain ⟨c, hc1, hcb, hc_cen⟩ := hc_ex
      have hci_cen : InCenter c⁻¹ :=
        inCenter_of_sameNhd_one (sameNhd_trans (sameNhd_symm (sameNhd_inv c)) (sameNhd_of_inCenter hc_cen one_inCenter))
      -- `c⁻¹ ∈ Cen(H) = {1, b, c}` and `c⁻¹ ≠ 1` and `c⁻¹ ≠ b` (else `c = b⁻¹ = b`), so `c⁻¹ = c`!
      have hci_eq : c⁻¹ = c := by
        have hmem : ∀ y : H, InCenter y → y = 1 ∨ y = b ∨ y = c := by
          intro y hy
          have h3in : (1 : H) ∈ ({f 1, f a, f a⁻¹} : Finset H) ∧
              b ∈ ({f 1, f a, f a⁻¹} : Finset H) ∧ c ∈ ({f 1, f a, f a⁻¹} : Finset H) := by
            simp only [Finset.mem_insert, Finset.mem_singleton]
            exact ⟨(hCenH_iff 1).mp one_inCenter, (hCenH_iff b).mp hb_cen, (hCenH_iff c).mp hc_cen⟩
          have hyin : y ∈ ({f 1, f a, f a⁻¹} : Finset H) := by
            simp only [Finset.mem_insert, Finset.mem_singleton]; exact (hCenH_iff y).mp hy
          have hsub : ({1, b, c} : Finset H) ⊆ {f 1, f a, f a⁻¹} := by
            intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            rcases hw with rfl | rfl | rfl <;> tauto
          have hcard_l : ({1, b, c} : Finset H).card = 3 := by
            rw [Finset.card_insert_of_notMem (by simp [Ne.symm hb1, Ne.symm hc1]),
                Finset.card_insert_of_notMem (by simp [Ne.symm hcb]), Finset.card_singleton]
          have hcard_r : ({f 1, f a, f a⁻¹} : Finset H).card ≤ 3 :=
            (Finset.card_insert_le _ _).trans (by
              have := Finset.card_insert_le (f a) {f a⁻¹}; simp at this; omega)
          have heq_set : ({1, b, c} : Finset H) = {f 1, f a, f a⁻¹} :=
            Finset.eq_of_subset_of_card_le hsub (by omega)
          rw [← heq_set] at hyin
          simpa using hyin
        rcases hmem c⁻¹ hci_cen with h | h | h
        · exact absurd (inv_eq_one.mp h) hc1
        · exact absurd (by rw [← inv_inv c, h, hb_inv]) hcb
        · exact h
      have hc2 : c ^ 2 = 1 := by
        calc c ^ 2 = c * c := sq c
          _ = c⁻¹ * c := by nth_rw 1 [← hci_eq]
          _ = 1 := inv_mul_cancel c
      have hb2 : b ^ 2 = 1 := by rw [← h2, pow_orderOf_eq_one]
      rcases hb_cen c hcb with ⟨_, k, hk | hk⟩
      · have : b ^ k = 1 ∨ b ^ k = b := by
          have hk2 : k % 2 = 0 ∨ k % 2 = 1 := by omega
          rw [show k = 2 * (k / 2) + k % 2 by omega, zpow_add, zpow_mul,
              show b ^ (2 : ℤ) = 1 by simpa using hb2, one_zpow, one_mul]
          rcases hk2 with h0 | h0 <;> simp [h0]
        rw [← hk] at this; rcases this with h | h
        · exact hc1 h
        · exact hcb h
      · have : c ^ k = 1 ∨ c ^ k = c := by
          have hk2 : k % 2 = 0 ∨ k % 2 = 1 := by omega
          rw [show k = 2 * (k / 2) + k % 2 by omega, zpow_add, zpow_mul,
              show c ^ (2 : ℤ) = 1 by simpa using hc2, one_zpow, one_mul]
          rcases hk2 with h0 | h0 <;> simp [h0]
        rw [← hk] at this; rcases this with h | h
        · exact hb1 h
        · exact hcb h.symm
    · -- `orderOf b = 3`: pick `z ∉ {1, b, b^2}` (possible since `H` is infinite)
      obtain ⟨z, hz⟩ : ∃ z : H, z ∉ ({1, b, b ^ 2} : Finset H) := by
        by_contra hall; push Not at hall
        exact absurd ((Finset.finite_toSet ({1, b, b ^ 2} : Finset H)).subset
          (fun w _ => hall w)) Set.infinite_univ
      have hz_ne1 : z ≠ 1 := fun h => hz (by simp [h])
      have hz_neb : z ≠ b := fun h => hz (by simp [h])
      have hz_neb2 : z ≠ b ^ 2 := fun h => hz (by simp [h])
      have hb3 : b ^ 3 = 1 := by rw [← h3, pow_orderOf_eq_one]
      rcases hb_cen z hz_neb with ⟨_, k, hk | hk⟩
      · exfalso
        have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
        rw [show k = 3 * (k / 3) + k % 3 by omega, zpow_add, zpow_mul,
            show b ^ (3 : ℤ) = 1 by simpa using hb3, one_zpow, one_mul] at hk
        rcases hk3 with h0 | h0 | h0
        · rw [h0, zpow_zero] at hk; exact hz_ne1 hk
        · rw [h0, zpow_one] at hk; exact hz_neb hk
        · rw [h0, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast] at hk; exact hz_neb2 hk
      · -- `b = z ^ k`, so `z` has finite order `d`, with `3 ∣ d` and `d ≠ 3` (else `z ∈ ⟨b⟩`)
        have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hb1 hk
        have hzfin : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.mpr
          ⟨3 * k.natAbs, by positivity, by
            have : z ^ (3 * k) = 1 := by rw [mul_comm, zpow_mul, ← hk]; simpa using hb3
            rcases Int.natAbs_eq k with h1 | h2
            · rw [← zpow_natCast, Nat.cast_mul, Nat.cast_ofNat, ← h1]; exact this
            · have : z ^ (-(3 * (k.natAbs : ℤ))) = 1 := by
                rw [show -(3 * (k.natAbs : ℤ)) = 3 * k by omega]; exact this
              rw [zpow_neg, inv_eq_one, ← Nat.cast_ofNat, ← Nat.cast_mul, zpow_natCast] at this
              exact this⟩
        have h3dvd : 3 ∣ orderOf z := by
          rw [← h3, hk]
          have hord_dvd := orderOf_dvd_of_pow_eq_one (show (z ^ k) ^ orderOf z = 1 by
            rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow])
          exact hord_dvd
        have hdz_ne3 : orderOf z ≠ 3 := by
          intro hdz3
          -- Then `z ^ k = b` with `k % 3 ∈ {1, 2}` so `z ∈ {b, b^2}`!
          have hz3 : z ^ 3 = 1 := by rw [← hdz3, pow_orderOf_eq_one]
          have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
          rw [show k = 3 * (k / 3) + k % 3 by omega, zpow_add, zpow_mul,
              show z ^ (3 : ℤ) = 1 by simpa using hz3, one_zpow, one_mul] at hk
          rcases hk3 with h0 | h0 | h0 <;> simp [h0] at hk
          · exact hb1 hk
          · exact hz_neb hk.symm
          · have : z = b ^ 2 := by rw [hk, ← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_add, hz3, one_mul, pow_one]
            exact hz_neb2 this
        have hordz := finite_order_mem_12346 hG3 hzfin
        have hdz6 : orderOf z = 6 := by omega
        -- Let `w = z ^ 3`: `orderOf w = 2`, so `w ≁ b` (order 3), contradicting `b ∈ Cen(H)`!
        let w := z ^ 3
        have hw1 : w ≠ 1 := by
          intro h; have := orderOf_dvd_of_pow_eq_one h; rw [hdz6] at this; exact absurd this (by decide)
        have hw2 : w ^ 2 = 1 := by
          dsimp only [w]; rw [← pow_mul, show 3 * 2 = 6 by rfl, ← hdz6, pow_orderOf_eq_one]
        have hwb : w ≠ b := by
          intro h; rw [h] at hw2
          have := orderOf_dvd_of_pow_eq_one hw2; rw [h3] at this; exact absurd this (by decide)
        rcases hb_cen w hwb with ⟨_, r, hr | hr⟩
        · have : w ^ 3 = 1 := by
            rw [hr, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]
          have : w = 1 := by
            calc w = w ^ 2 * w := by rw [hw2, one_mul]
              _ = w ^ 3 := by rw [← pow_succ]
              _ = 1 := this
          exact hw1 this
        · have : b ^ 2 = 1 := by
            rw [hr, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw2, one_zpow]
          have := orderOf_dvd_of_pow_eq_one this; rw [h3] at this; exact absurd this (by decide)
    · -- `orderOf b = 4`: `1, b, b^2, b^3` are 4 distinct elements ALL in `Cen(H)`, contradicting `|Cen(H)| = 3`!
      have hb4 : b ^ 4 = 1 := by rw [← h4, pow_orderOf_eq_one]
      have hb2_cen : InCenter (b ^ 2) := by
        intro y hy
        by_cases hyb : y = b
        · subst hyb; exact ⟨Ne.symm hy, 2, Or.inr (by simp)⟩
        · rcases hb_cen y hyb with ⟨_, k, hk | hk⟩
          · have hk4 : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
            rw [show k = 4 * (k / 4) + k % 4 by omega, zpow_add, zpow_mul,
                show b ^ (4 : ℤ) = 1 by simpa using hb4, one_zpow, one_mul] at hk
            rcases hk4 with h0 | h0 | h0 | h0 <;> simp [h0] at hk
            · exact ⟨Ne.symm hy, 0, Or.inl (by simp [hk])⟩
            · exact absurd hk hyb
            · exact absurd hk hy
            · refine ⟨Ne.symm hy, 2, Or.inr ?_⟩
              rw [hk, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast]
              calc b ^ 2 = b ^ 2 * b ^ 4 := by rw [hb4, mul_one]
                _ = (b ^ 3) ^ 2 := by rw [← pow_add, ← pow_mul]
          · exact ⟨Ne.symm hy, k * 2, Or.inr (by rw [zpow_mul, ← hk]; simp)⟩
      have hb3_cen : InCenter (b ^ 3) := by
        have : b ^ 3 = b⁻¹ := by
          calc b ^ 3 = b ^ 3 * (b * b⁻¹) := by simp
            _ = b ^ 4 * b⁻¹ := by group
            _ = b⁻¹ := by rw [hb4, one_mul]
        rw [this]
        exact inCenter_of_sameNhd_one (sameNhd_trans (sameNhd_symm (sameNhd_inv b)) (sameNhd_of_inCenter hb_cen one_inCenter))
      have hdistinct : ∀ i j : ℕ, i < 4 → j < 4 → b ^ i = b ^ j → i = j := fun i j hi hj h => by
        have := pow_inj_mod.mp h
        rwa [h4, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
      have hcol := hG3 1 1 b (b ^ 2) (b ^ 3)
        (sameNhd_refl 1) (sameNhd_of_inCenter one_inCenter hb_cen)
        (sameNhd_of_inCenter one_inCenter hb2_cen) (sameNhd_of_inCenter one_inCenter hb3_cen)
      rcases hcol with h | h | h | h | h | h
      · exact absurd (hdistinct 0 1 (by omega) (by omega) (by simpa using h)) (by omega)
      · exact absurd (hdistinct 0 2 (by omega) (by omega) (by simpa using h)) (by omega)
      · exact absurd (hdistinct 0 3 (by omega) (by omega) (by simpa using h)) (by omega)
      · exact absurd (hdistinct 1 2 (by omega) (by omega) (by simpa using h)) (by omega)
      · exact absurd (hdistinct 1 3 (by omega) (by omega) (by simpa using h)) (by omega)
      · exact absurd (hdistinct 2 3 (by omega) (by omega) (by simpa using h)) (by omega)
    · -- `orderOf b = 6`: pick `z ∉ ⟨b⟩` (`|⟨b⟩| = 6`, `H` infinite), then `6 ∣ orderOf z` and `orderOf z > 6`!
      have hb6 : b ^ 6 = 1 := by rw [← h6, pow_orderOf_eq_one]
      let S6 : Finset H := {1, b, b ^ 2, b ^ 3, b ^ 4, b ^ 5}
      obtain ⟨z, hz⟩ : ∃ z : H, z ∉ S6 := by
        by_contra hall; push Not at hall
        exact absurd ((Finset.finite_toSet S6).subset (fun w _ => hall w)) Set.infinite_univ
      have hz_neb : z ≠ b := fun h => hz (by simp [S6, h])
      rcases hb_cen z hz_neb with ⟨_, k, hk | hk⟩
      · exfalso
        have hk6 : k % 6 = 0 ∨ k % 6 = 1 ∨ k % 6 = 2 ∨ k % 6 = 3 ∨ k % 6 = 4 ∨ k % 6 = 5 := by omega
        rw [show k = 6 * (k / 6) + k % 6 by omega, zpow_add, zpow_mul,
            show b ^ (6 : ℤ) = 1 by simpa using hb6, one_zpow, one_mul] at hk
        rcases hk6 with h0 | h0 | h0 | h0 | h0 | h0 <;> simp [h0] at hk <;>
          exact hz (by simp [S6, hk])
      · have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hb1 hk
        have hzfin : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.mpr
          ⟨6 * k.natAbs, by positivity, by
            have : z ^ (6 * k) = 1 := by rw [mul_comm, zpow_mul, ← hk]; simpa using hb6
            rcases Int.natAbs_eq k with h1 | h2
            · rw [← zpow_natCast, Nat.cast_mul, Nat.cast_ofNat, ← h1]; exact this
            · have : z ^ (-(6 * (k.natAbs : ℤ))) = 1 := by
                rw [show -(6 * (k.natAbs : ℤ)) = 6 * k by omega]; exact this
              rw [zpow_neg, inv_eq_one, ← Nat.cast_ofNat, ← Nat.cast_mul, zpow_natCast] at this
              exact this⟩
        have h6dvd : 6 ∣ orderOf z := by
          rw [← h6, hk]
          exact orderOf_dvd_of_pow_eq_one (show (z ^ k) ^ orderOf z = 1 by
            rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow])
        have hdz_ne6 : orderOf z ≠ 6 := by
          intro hdz6
          have hz6 : z ^ 6 = 1 := by rw [← hdz6, pow_orderOf_eq_one]
          have h2nd : ¬ (2 : ℤ) ∣ k := by
            rintro ⟨t, rfl⟩
            have : b ^ 3 = 1 := by
              rw [hk, ← zpow_natCast, ← zpow_mul, Nat.cast_ofNat, show 2 * t * 3 = 6 * t by ring,
                  zpow_mul, show z ^ (6 : ℤ) = 1 by simpa using hz6, one_zpow]
            have := orderOf_dvd_of_pow_eq_one this; rw [h6] at this; exact absurd this (by decide)
          have h3nd : ¬ (3 : ℤ) ∣ k := by
            rintro ⟨t, rfl⟩
            have : b ^ 2 = 1 := by
              rw [hk, ← zpow_natCast, ← zpow_mul, Nat.cast_ofNat, show 3 * t * 2 = 6 * t by ring,
                  zpow_mul, show z ^ (6 : ℤ) = 1 by simpa using hz6, one_zpow]
            have := orderOf_dvd_of_pow_eq_one this; rw [h6] at this; exact absurd this (by decide)
          have hk6 : k % 6 = 1 ∨ k % 6 = 5 := by omega
          rcases hk6 with h1 | h5
          · have : b = z := by
              rw [hk, show k = 6 * (k / 6) + 1 by omega, zpow_add, zpow_mul,
                  show z ^ (6 : ℤ) = 1 by simpa using hz6, one_zpow, one_mul, zpow_one]
            exact absurd this.symm hz_neb
          · have : b = z ^ 5 := by
              rw [hk, show k = 6 * (k / 6) + 5 by omega, zpow_add, zpow_mul,
                  show z ^ (6 : ℤ) = 1 by simpa using hz6, one_zpow, one_mul]; exact zpow_ofNat z 5
            have : z = b ^ 5 := by
              rw [this, ← pow_mul, show 5 * 5 = 6 * 4 + 1 by rfl, pow_add, pow_mul, hz6, one_pow, one_mul, pow_one]
            exact absurd (by simp [S6, this] : z ∈ S6) hz
        have hordz := finite_order_mem_12346 hG3 hzfin
        omega
  -- Now BOTH `G = ⟨a⟩ ≅ ℤ` and `H = ⟨b⟩ ≅ ℤ`, so construct `G ≃* H`!
  have hHcyc : ∀ y : H, ∃ n : ℤ, y = b ^ n := cyclic_of_inCenter_infOrd hb_inf hb_cen
  have hGuniq : ∀ x : G, ∃! n : ℤ, x = a ^ n := fun x => by
    obtain ⟨n, hn⟩ := hGcyc x
    exact ⟨n, hn, fun m hm => zpow_inj hGtf ha1 (hm.symm.trans hn)⟩
  have hHuniq : ∀ y : H, ∃! n : ℤ, y = b ^ n := fun y => by
    obtain ⟨n, hn⟩ := hHcyc y
    refine ⟨n, hn, fun m hm => ?_⟩
    have hsub : b ^ (m - n) = 1 := by rw [zpow_sub, ← hm, ← hn, mul_inv_cancel]
    have := hb_inf (m - n) hsub; omega
  let toZ : G → ℤ := fun x => Classical.choose (hGuniq x)
  let ofZ : H → ℤ := fun y => Classical.choose (hHuniq y)
  have htoZ : ∀ x : G, x = a ^ toZ x := fun x => (Classical.choose_spec (hGuniq x)).1
  have htoZ_pow : ∀ n : ℤ, toZ (a ^ n) = n := fun n =>
    (Classical.choose_spec (hGuniq (a ^ n))).2 n rfl |>.symm
  have hofZ : ∀ y : H, y = b ^ ofZ y := fun y => (Classical.choose_spec (hHuniq y)).1
  have hofZ_pow : ∀ n : ℤ, ofZ (b ^ n) = n := fun n =>
    (Classical.choose_spec (hHuniq (b ^ n))).2 n rfl |>.symm
  let e : G ≃ H :=
    { toFun := fun x => b ^ toZ x
      invFun := fun y => a ^ ofZ y
      left_inv := fun x => by dsimp only; rw [hofZ_pow, ← htoZ x]
      right_inv := fun y => by dsimp only; rw [htoZ_pow, ← hofZ y] }
  refine ⟨e, fun x y => ?_⟩
  have he_pow : ∀ (u : G) (k : ℤ), e (u ^ k) = (e u) ^ k := fun u k => by
    change b ^ toZ (u ^ k) = (b ^ toZ u) ^ k
    conv_lhs => rw [htoZ u, ← zpow_mul, htoZ_pow]
    rw [zpow_mul]
  constructor
  · rintro ⟨hne, k, rfl⟩
    exact ⟨fun h => hne (e.injective h), k, he_pow x k⟩
  · rintro ⟨hne, k, hk⟩
    refine ⟨fun h => hne (by rw [h]), k, e.injective ?_⟩
    rw [he_pow, hk]

/-! ### 3. Case B: `Cen(G) = {1}` ⇒ `f 1 = 1` and `H` is torsion-free -/

private lemma H_torsionFree_of_trivial_center {G H : Type*} [Group G] [Group H]
    (hGtf : IsTorsionFreeGroup G) (f : G ≃ H)
    (hf : ∀ x y, PowerAdj x y ↔ PowerAdj (f x) (f y))
    (hCenG : ∀ x : G, InCenter x → x = 1) :
    f 1 = 1 ∧ IsTorsionFreeGroup H := by
  have hf1 : f 1 = 1 := by
    have h1 : InCenter (f.symm 1) := (inCenter_of_iso f hf).mpr (by simpa using one_inCenter)
    have h2 : f.symm 1 = 1 := hCenG _ h1
    rw [← h2, f.apply_symm_apply]
  refine ⟨hf1, ?_⟩
  -- Every `SameNhd`-class in `G \ {1}` has size ≤ 2 (in fact `{x, x⁻¹}`).
  have h2H : ∀ x a b c : H, x ≠ 1 → a ≠ 1 → b ≠ 1 → c ≠ 1 →
      SameNhd x a → SameNhd x b → SameNhd x c → a = b ∨ a = c ∨ b = c := by
    intro x a b c hx ha hb hc hsa hsb hsc
    have hx' : f.symm x ≠ 1 := fun h => hx (by rw [← hf1, ← h, f.apply_symm_apply])
    have ha' : f.symm a ≠ 1 := fun h => ha (by rw [← hf1, ← h, f.apply_symm_apply])
    have hb' : f.symm b ≠ 1 := fun h => hb (by rw [← hf1, ← h, f.apply_symm_apply])
    have hc' : f.symm c ≠ 1 := fun h => hc (by rw [← hf1, ← h, f.apply_symm_apply])
    have hsa' : SameNhd (f.symm x) (f.symm a) := (sameNhd_of_iso f hf).mpr (by simpa using hsa)
    have hsb' : SameNhd (f.symm x) (f.symm b) := (sameNhd_of_iso f hf).mpr (by simpa using hsb)
    have hsc' : SameNhd (f.symm x) (f.symm c) := (sameNhd_of_iso f hf).mpr (by simpa using hsc)
    rcases sameNhd_tf_eq_or_inv hGtf hx' ha' hsa' with h1 | h1 <;>
    rcases sameNhd_tf_eq_or_inv hGtf hx' hb' hsb' with h2 | h2 <;>
    rcases sameNhd_tf_eq_or_inv hGtf hx' hc' hsc' with h3 | h3
    · exact Or.inl (f.symm.injective (h1.trans h2.symm))
    · exact Or.inl (f.symm.injective (h1.trans h2.symm))
    · exact Or.inr (Or.inl (f.symm.injective (h1.trans h3.symm)))
    · exact Or.inr (Or.inr (f.symm.injective (h2.trans h3.symm)))
    · exact Or.inr (Or.inr (f.symm.injective (h2.trans h3.symm)))
    · exact Or.inr (Or.inl (f.symm.injective (h1.trans h3.symm)))
    · exact Or.inl (f.symm.injective (h1.trans h2.symm))
    · exact Or.inl (f.symm.injective (h1.trans h2.symm))
  -- Also every `x ≠ 1` in `H` has a partner `y ≠ x, 1` with `SameNhd x y`!
  have hpartner : ∀ x : H, x ≠ 1 → ∃ y : H, y ≠ 1 ∧ y ≠ x ∧ SameNhd x y := by
    intro x hx
    have hx' : f.symm x ≠ 1 := fun h => hx (by rw [← hf1, ← h, f.apply_symm_apply])
    refine ⟨f (f.symm x)⁻¹, ?_, ?_, ?_⟩
    · intro h; rw [← hf1] at h; exact inv_ne_one.mpr hx' (f.injective h)
    · intro h; have : (f.symm x)⁻¹ = f.symm x := f.injective (by simpa using h)
      exact inv_ne_self_of_tf hGtf hx' this
    · have := (sameNhd_of_iso f hf).mp (sameNhd_inv (f.symm x))
      simpa using this
  -- Also every `SameNhd`-class in `H` has size ≤ 3 (so `orderOf z ∈ {1,2,3,4,6}` for finite order)
  have h3H : ∀ x p q r s : H, SameNhd x p → SameNhd x q → SameNhd x r → SameNhd x s →
      p = q ∨ p = r ∨ p = s ∨ q = r ∨ q = s ∨ r = s := by
    intro x p q r s hp hq hr hs
    have hcol := sameNhd_card_le_three_of_tf hGtf (f.symm x) (f.symm p) (f.symm q) (f.symm r) (f.symm s)
      ((sameNhd_of_iso f hf).mpr (by simpa using hp))
      ((sameNhd_of_iso f hf).mpr (by simpa using hq))
      ((sameNhd_of_iso f hf).mpr (by simpa using hr))
      ((sameNhd_of_iso f hf).mpr (by simpa using hs))
    rcases hcol with h | h | h | h | h | h <;> simp [f.symm.injective h]
  -- No element of order 2 in `H`!
  have hno2 : ∀ y : H, orderOf y ≠ 2 := by
    intro y hy2
    have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hy2; omega
    have hy_sq : y ^ 2 = 1 := by rw [← hy2, pow_orderOf_eq_one]
    obtain ⟨z, hz1, hzy, hsz⟩ := hpartner y hy1
    have hyz : PowerAdj y z := by
      rcases (hsz z).mpr (Or.inl rfl) with h | h
      · exact absurd h hzy
      · exact h
    rcases hyz with ⟨_, k, hk | hk⟩
    · have hk2 : k % 2 = 0 ∨ k % 2 = 1 := by omega
      rw [show k = 2 * (k / 2) + k % 2 by omega, zpow_add, zpow_mul,
          show y ^ (2 : ℤ) = 1 by simpa using hy_sq, one_zpow, one_mul] at hk
      rcases hk2 with h0 | h0 <;> simp [h0] at hk
      · exact hz1 hk
      · exact hzy hk
    · -- `y = z ^ k` and `z ≠ y, 1`, so `z⁻¹ ≠ z` (else `z^2 = 1` -> `y ∈ {1, z}`)!
      have hzi_ne_z : z⁻¹ ≠ z := by
        intro h
        have hz2 : z ^ 2 = 1 := by
          calc z ^ 2 = z * z := sq z
            _ = z⁻¹ * z := by nth_rw 1 [← h]
            _ = 1 := inv_mul_cancel z
        have hk2 : k % 2 = 0 ∨ k % 2 = 1 := by omega
        rw [show k = 2 * (k / 2) + k % 2 by omega, zpow_add, zpow_mul,
            show z ^ (2 : ℤ) = 1 by simpa using hz2, one_zpow, one_mul] at hk
        rcases hk2 with h0 | h0 <;> simp [h0] at hk
        · exact hy1 hk
        · exact hzy hk.symm
      have hzi_ne_y : z⁻¹ ≠ y := by
        intro h
        have : z = y⁻¹ := by rw [← inv_inv z, h]
        have hyi : y⁻¹ = y := by
          calc y⁻¹ = y⁻¹ * (y * y) := by rw [← sq, hy_sq, mul_one]
            _ = y := by group
        exact hzy (this.trans hyi)
      have hcol := h2H y y z z⁻¹ hy1 hy1 hz1 (inv_ne_one.mpr hz1)
        (sameNhd_refl y) hsz (sameNhd_trans hsz (sameNhd_inv z))
      rcases hcol with h | h | h
      · exact hzy h.symm
      · exact hzi_ne_y h.symm
      · exact hzi_ne_z h.symm
  -- No element of `H` can have finite order `> 1`!
  intro y n hn_pos hyn
  by_contra hy1
  have hyfin : IsOfFinOrder y := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn_pos, hyn⟩
  have hord := finite_order_mem_12346 h3H hyfin
  have hord_ne1 : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.mp h)
  rcases hord with h1 | h2 | h3 | h4 | h6
  · exact hord_ne1 h1
  · exact hno2 y h2
  · -- `orderOf y = 3`: every neighbor `w ≠ 1` of `y` must be `y⁻¹`!
    -- Contradiction since `f.symm y ≠ 1` has at least 3 distinct non-identity neighbors in `G`!
    have hy3 : y ^ 3 = 1 := by rw [← h3, pow_orderOf_eq_one]
    have hdeg : ∀ w : H, w ≠ 1 → PowerAdj y w → w = y ^ 2 := by
      intro w hw1 hyw
      rcases hyw with ⟨hwy, k, hk | hk⟩
      · have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
        rw [show k = 3 * (k / 3) + k % 3 by omega, zpow_add, zpow_mul,
            show y ^ (3 : ℤ) = 1 by simpa using hy3, one_zpow, one_mul] at hk
        rcases hk3 with h0 | h0 | h0 <;> simp [h0] at hk
        · exact absurd hk hw1
        · exact absurd hk.symm hwy
        · exact hk
      · -- `y = w ^ k` -> `w` has finite order `d` with `3 ∣ d` -> `d ∈ {3, 6}`; `d = 6` gives `orderOf (w^3) = 2`!
        have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hy1 hk
        have hwfin : IsOfFinOrder w := isOfFinOrder_iff_pow_eq_one.mpr
          ⟨3 * k.natAbs, by positivity, by
            have : w ^ (3 * k) = 1 := by rw [mul_comm, zpow_mul, ← hk]; simpa using hy3
            rcases Int.natAbs_eq k with h1 | h2
            · rw [← zpow_natCast, Nat.cast_mul, Nat.cast_ofNat, ← h1]; exact this
            · have : w ^ (-(3 * (k.natAbs : ℤ))) = 1 := by
                rw [show -(3 * (k.natAbs : ℤ)) = 3 * k by omega]; exact this
              rw [zpow_neg, inv_eq_one, ← Nat.cast_ofNat, ← Nat.cast_mul, zpow_natCast] at this
              exact this⟩
        have h3dvd : 3 ∣ orderOf w := by
          rw [← h3, hk]
          exact orderOf_dvd_of_pow_eq_one (show (w ^ k) ^ orderOf w = 1 by
            rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow])
        have hordw := finite_order_mem_12346 h3H hwfin
        have hw_ne6 : orderOf w ≠ 6 := by
          intro hw6
          have h2 : (w ^ 3) ^ 2 = 1 := by rw [← pow_mul, show 3 * 2 = 6 by rfl, ← hw6, pow_orderOf_eq_one]
          have hne1 : w ^ 3 ≠ 1 := fun h => by
            have := orderOf_dvd_of_pow_eq_one h; rw [hw6] at this; exact absurd this (by decide)
          have hdvd := orderOf_dvd_of_pow_eq_one h2
          have hpos := orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by omega, h2⟩)
          have hne1' : orderOf (w ^ 3) ≠ 1 := fun h => hne1 (orderOf_eq_one_iff.mp h)
          have hle := Nat.le_of_dvd (by omega) hdvd
          exact hno2 (w ^ 3) (by omega)
        have hw3 : orderOf w = 3 := by omega
        have hw3_eq : w ^ 3 = 1 := by rw [← hw3, pow_orderOf_eq_one]
        have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
        rw [show k = 3 * (k / 3) + k % 3 by omega, zpow_add, zpow_mul,
            show w ^ (3 : ℤ) = 1 by simpa using hw3_eq, one_zpow, one_mul] at hk
        rcases hk3 with h0 | h0 | h0 <;> simp [h0] at hk
        · exact absurd hk hy1
        · exact absurd hk hwy
        · rw [hk, ← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_add, hw3_eq, one_mul, pow_one]
    -- Now `x := f.symm y ≠ 1` has two distinct neighbors `x^2, x^3 ≠ 1` in `G`!
    set x := f.symm y
    have hx1 : x ≠ 1 := fun h => hy1 (by rw [← hf1, ← h, f.apply_symm_apply])
    have hx2_ne1 : x ^ 2 ≠ 1 := fun h => hx1 (hGtf x 2 (by omega) h)
    have hx3_ne1 : x ^ 3 ≠ 1 := fun h => hx1 (hGtf x 3 (by omega) h)
    have hx2_nex : x ≠ x ^ 2 := fun h => by
      have := zpow_inj hGtf hx1 (show x ^ (1 : ℤ) = x ^ (2 : ℤ) by simpa using h); omega
    have hx3_nex : x ≠ x ^ 3 := fun h => by
      have := zpow_inj hGtf hx1 (show x ^ (1 : ℤ) = x ^ (3 : ℤ) by simpa using h); omega
    have hfx2 : f (x ^ 2) = y ^ 2 := hdeg (f (x ^ 2))
      (fun h => hx2_ne1 (f.injective (h.trans hf1.symm)))
      (by simpa [x] using (hf x (x ^ 2)).mp ⟨hx2_nex, 2, Or.inl (by simp)⟩)
    have hfx3 : f (x ^ 3) = y ^ 2 := hdeg (f (x ^ 3))
      (fun h => hx3_ne1 (f.injective (h.trans hf1.symm)))
      (by simpa [x] using (hf x (x ^ 3)).mp ⟨hx3_nex, 3, Or.inl (by simp)⟩)
    have hx23 : x ^ 2 = x ^ 3 := f.injective (hfx2.trans hfx3.symm)
    have := zpow_inj hGtf hx1 (show x ^ (2 : ℤ) = x ^ (3 : ℤ) by simpa using hx23)
    omega
  · -- `orderOf y = 4` -> `orderOf (y^2) = 2`!
    have h2 : (y ^ 2) ^ 2 = 1 := by rw [← pow_mul, show 2 * 2 = 4 by rfl, ← h4, pow_orderOf_eq_one]
    have hne1 : y ^ 2 ≠ 1 := fun h => by
      have := orderOf_dvd_of_pow_eq_one h; rw [h4] at this; exact absurd this (by decide)
    have hdvd := orderOf_dvd_of_pow_eq_one h2
    have hpos := orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by omega, h2⟩)
    have hne1' : orderOf (y ^ 2) ≠ 1 := fun h => hne1 (orderOf_eq_one_iff.mp h)
    have hle := Nat.le_of_dvd (by omega) hdvd
    exact hno2 (y ^ 2) (by omega)
  · -- `orderOf y = 6` -> `orderOf (y^3) = 2`!
    have h2 : (y ^ 3) ^ 2 = 1 := by rw [← pow_mul, show 3 * 2 = 6 by rfl, ← h6, pow_orderOf_eq_one]
    have hne1 : y ^ 3 ≠ 1 := fun h => by
      have := orderOf_dvd_of_pow_eq_one h; rw [h6] at this; exact absurd this (by decide)
    have hdvd := orderOf_dvd_of_pow_eq_one h2
    have hpos := orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by omega, h2⟩)
    have hne1' : orderOf (y ^ 3) ≠ 1 := fun h => hne1 (orderOf_eq_one_iff.mp h)
    have hle := Nat.le_of_dvd (by omega) hdvd
    exact hno2 (y ^ 3) (by omega)

/-! ### 4. Connected components of `NzAdj` in torsion-free nilpotency class 2 groups embed in `ℚ` -/

private lemma nilp2_comm_zpow_left {G : Type*} [Group G] (hnil : NilpotencyClassLeTwo G)
    (x y : G) : ∀ m : ℤ, x ^ m * y * (x ^ m)⁻¹ * y⁻¹ = (x * y * x⁻¹ * y⁻¹) ^ m := by
  let c := x * y * x⁻¹ * y⁻¹
  have hc_z : ∀ z : G, c * z = z * c := fun z => hnil x y z
  have hcomm_nat : ∀ (n : ℕ) (z : G), c ^ n * z = z * c ^ n := fun n z => by
    induction n with
    | zero => simp
    | succ j ihj => rw [pow_succ, mul_assoc, hc_z, ← mul_assoc, ihj, mul_assoc]
  have hcomm_int : ∀ (m : ℤ) (z : G), c ^ m * z = z * c ^ m := fun m z => by
    cases m with
    | ofNat k => simpa using hcomm_nat k z
    | negSucc k =>
      have := congrArg (fun t => (c ^ (k + 1))⁻¹ * t * (c ^ (k + 1))⁻¹) (hcomm_nat (k + 1) z)
      simpa [zpow_negSucc, mul_assoc] using this.symm
  have hxy : x * y = y * x * c := by
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = c * (y * x) := rfl
      _ = y * x * c := hc_z (y * x)
  have hnat : ∀ k : ℕ, x ^ k * y = y * x ^ k * c ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc x ^ (k + 1) * y = x ^ k * (x * y) := by rw [pow_succ, mul_assoc]
        _ = x ^ k * (y * x * c) := by rw [hxy]
        _ = (x ^ k * y) * x * c := by group
        _ = (y * x ^ k * c ^ k) * x * c := by rw [ih]
        _ = y * x ^ k * (c ^ k * x) * c := by group
        _ = y * x ^ k * (x * c ^ k) * c := by rw [hcomm_nat k x]
        _ = y * x ^ (k + 1) * c ^ (k + 1) := by rw [pow_succ, pow_succ]; group
  have hint : ∀ m : ℤ, x ^ m * y = y * x ^ m * c ^ m := by
    intro m
    cases m with
    | ofNat k => simpa using hnat k
    | negSucc k =>
      have hk := hnat (k + 1)
      have hinv : (x ^ (k + 1))⁻¹ * y = y * (x ^ (k + 1))⁻¹ * (c ^ (k + 1))⁻¹ := by
        have h1 := congrArg (fun t => (x ^ (k + 1))⁻¹ * t * (c ^ (k + 1))⁻¹) hk
        have h2 : (x ^ (k + 1))⁻¹ * (y * x ^ (k + 1) * c ^ (k + 1)) * (c ^ (k + 1))⁻¹ =
            (x ^ (k + 1))⁻¹ * y * x ^ (k + 1) := by group
        rw [h2] at h1
        have h3 : (x ^ (k + 1))⁻¹ * (x ^ (k + 1) * y) * (c ^ (k + 1))⁻¹ = y * (c ^ (k + 1))⁻¹ := by group
        rw [h3] at h1
        have h4 := congrArg (fun t => t * (x ^ (k + 1))⁻¹) h1.symm
        have h5 : (x ^ (k + 1))⁻¹ * y * x ^ (k + 1) * (x ^ (k + 1))⁻¹ = (x ^ (k + 1))⁻¹ * y := by group
        rw [h5] at h4
        rw [h4]
        have hcinv : (c ^ (k + 1))⁻¹ * (x ^ (k + 1))⁻¹ = (x ^ (k + 1))⁻¹ * (c ^ (k + 1))⁻¹ := by
          have := congrArg (fun t => (c ^ (k + 1))⁻¹ * t * (c ^ (k + 1))⁻¹) (hcomm_nat (k + 1) (x ^ (k + 1))⁻¹)
          simpa [mul_assoc] using this.symm
        rw [mul_assoc, hcinv, ← mul_assoc]
      simpa [zpow_negSucc] using hinv
  intro m
  have hm := hint m
  calc x ^ m * y * (x ^ m)⁻¹ * y⁻¹ = (y * x ^ m * c ^ m) * (x ^ m)⁻¹ * y⁻¹ := by rw [hm]
    _ = y * (x ^ m * c ^ m * (x ^ m)⁻¹) * y⁻¹ := by group
    _ = y * (c ^ m * x ^ m * (x ^ m)⁻¹) * y⁻¹ := by rw [(hcomm_int m (x ^ m)).symm]
    _ = y * c ^ m * y⁻¹ := by group
    _ = c ^ m * y * y⁻¹ := by rw [(hcomm_int m y).symm]
    _ = c ^ m := by group

private def SameComp {G : Type*} [Group G] (x y : G) : Prop :=
  ∃ m n : ℤ, m ≠ 0 ∧ n ≠ 0 ∧ x ^ m = y ^ n

private lemma sameComp_comm {G : Type*} [Group G]
    (htf : IsTorsionFreeGroup G) (hnil : NilpotencyClassLeTwo G)
    {x y : G} (h : SameComp x y) : x * y = y * x := by
  obtain ⟨m, n, hm, _, hxy⟩ := h
  have h1 : (x * y * x⁻¹ * y⁻¹) ^ m = 1 := by
    rw [← nilp2_comm_zpow_left hnil x y m, hxy]
    have hcom : y ^ n * y = y * y ^ n := by rw [← zpow_add_one, ← zpow_one_add, add_comm]
    calc y ^ n * y * (y ^ n)⁻¹ * y⁻¹ = y * y ^ n * (y ^ n)⁻¹ * y⁻¹ := by rw [hcom]
      _ = 1 := by group
  have hc1 : x * y * x⁻¹ * y⁻¹ = 1 := by
    by_contra hne
    exact hm ((zpow_eq_one_iff htf hne m).mp h1)
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = 1 * (y * x) := by rw [hc1]
    _ = y * x := one_mul _

private lemma sameComp_refl {G : Type*} [Group G] (x : G) : SameComp x x :=
  ⟨1, 1, by omega, by omega, rfl⟩

private lemma sameComp_symm {G : Type*} [Group G] {x y : G} (h : SameComp x y) : SameComp y x := by
  obtain ⟨m, n, hm, hn, hxy⟩ := h; exact ⟨n, m, hn, hm, hxy.symm⟩

private lemma sameComp_trans {G : Type*} [Group G] {x y z : G}
    (h1 : SameComp x y) (h2 : SameComp y z) : SameComp x z := by
  obtain ⟨m, n, hm, hn, hxy⟩ := h1
  obtain ⟨p, q, hp, hq, hyz⟩ := h2
  refine ⟨m * p, q * n, mul_ne_zero hm hp, mul_ne_zero hq hn, ?_⟩
  rw [zpow_mul, hxy, ← zpow_mul, mul_comm n p, zpow_mul, hyz, ← zpow_mul]

private lemma sameComp_of_nzAdj {G : Type*} [Group G] {x y : G} (h : NzAdj x y) : SameComp x y := by
  rcases h with ⟨_, n, hn, h1 | h2⟩
  · exact ⟨n, 1, hn, by omega, by simpa using h1.symm⟩
  · exact ⟨1, n, by omega, hn, by simpa using h2⟩

private lemma sameComp_mul_zpow {G : Type*} [Group G]
    (htf : IsTorsionFreeGroup G) (hnil : NilpotencyClassLeTwo G)
    {c₀ x y : G} (hx : SameComp c₀ x) (hy : SameComp c₀ y) :
    x * y = 1 ∨ SameComp c₀ (x * y) := by
  by_cases h1 : x * y = 1
  · exact Or.inl h1
  · right
    have hcomm : x * y = y * x := sameComp_comm htf hnil (sameComp_trans (sameComp_symm hx) hy)
    obtain ⟨m1, n1, hm1, hn1, h1eq⟩ := hx
    obtain ⟨m2, n2, hm2, hn2, h2eq⟩ := hy
    have hxy_pow : (x * y) ^ (n1 * n2) = c₀ ^ (m1 * n2 + m2 * n1) := by
      have hc : Commute x y := hcomm
      rw [hc.mul_zpow, zpow_add]
      congr 1
      · rw [zpow_mul, ← h1eq, ← zpow_mul]
      · rw [mul_comm n1 n2, zpow_mul, ← h2eq, ← zpow_mul]
    have hnum_ne : m1 * n2 + m2 * n1 ≠ 0 := by
      intro h0
      rw [h0, zpow_zero] at hxy_pow
      exact mul_ne_zero hn1 hn2 ((zpow_eq_one_iff htf h1 (n1 * n2)).mp hxy_pow)
    exact ⟨m1 * n2 + m2 * n1, n1 * n2, hnum_ne, mul_ne_zero hn1 hn2, hxy_pow.symm⟩

open Classical in
private noncomputable def coord {G : Type*} [Group G] (c₀ x : G) : ℚ :=
  if h : SameComp c₀ x then
    let m := Classical.choose h
    let n := Classical.choose (Classical.choose_spec h)
    (m : ℚ) / (n : ℚ)
  else 0

private lemma coord_eq_of_pow {G : Type*} [Group G] (htf : IsTorsionFreeGroup G)
    {c₀ x : G} (hc₀ : c₀ ≠ 1) {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0) (h : c₀ ^ m = x ^ n) :
    coord c₀ x = (m : ℚ) / (n : ℚ) := by
  have hsc : SameComp c₀ x := ⟨m, n, hm, hn, h⟩
  dsimp only [coord]
  rw [dif_pos hsc]
  set m' := Classical.choose hsc
  set n' := Classical.choose (Classical.choose_spec hsc)
  have hspec := Classical.choose_spec (Classical.choose_spec hsc)
  have hm' : m' ≠ 0 := hspec.1
  have hn' : n' ≠ 0 := hspec.2.1
  have heq' : c₀ ^ m' = x ^ n' := hspec.2.2
  have hpow : c₀ ^ (m' * n) = c₀ ^ (m * n') := by
    rw [zpow_mul, heq', ← zpow_mul, mul_comm n' n, zpow_mul, ← h, ← zpow_mul]
  have hint : m' * n = m * n' := zpow_inj htf hc₀ hpow
  have hq : (m' : ℚ) * (n : ℚ) = (m : ℚ) * (n' : ℚ) := by exact_mod_cast hint
  have hn_q : (n : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hn'_q : (n' : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hn'
  rw [div_eq_div_iff hn'_q hn_q]
  exact hq

private lemma coord_ne_zero {G : Type*} [Group G] (htf : IsTorsionFreeGroup G)
    {c₀ x : G} (hc₀ : c₀ ≠ 1) (hx : SameComp c₀ x) : coord c₀ x ≠ 0 := by
  obtain ⟨m, n, hm, hn, h⟩ := hx
  rw [coord_eq_of_pow htf hc₀ hm hn h]
  exact div_ne_zero (Int.cast_ne_zero.mpr hm) (Int.cast_ne_zero.mpr hn)

private lemma coord_self {G : Type*} [Group G] (htf : IsTorsionFreeGroup G)
    {c₀ : G} (hc₀ : c₀ ≠ 1) : coord c₀ c₀ = 1 := by
  rw [coord_eq_of_pow htf hc₀ (by omega : (1 : ℤ) ≠ 0) (by omega : (1 : ℤ) ≠ 0) rfl]
  simp

private lemma coord_zpow {G : Type*} [Group G] (htf : IsTorsionFreeGroup G)
    {c₀ x : G} (hc₀ : c₀ ≠ 1) (hx : SameComp c₀ x) {k : ℤ} (hk : k ≠ 0) :
    coord c₀ (x ^ k) = (k : ℚ) * coord c₀ x := by
  obtain ⟨m, n, hm, hn, h⟩ := hx
  have h1 : c₀ ^ (k * m) = (x ^ k) ^ n := by
    rw [mul_comm, zpow_mul, h, ← zpow_mul, mul_comm n k, zpow_mul]
  rw [coord_eq_of_pow htf hc₀ hm hn h, coord_eq_of_pow htf hc₀ (mul_ne_zero hk hm) hn h1]
  push_cast; ring

private lemma coord_mul {G : Type*} [Group G]
    (htf : IsTorsionFreeGroup G) (hnil : NilpotencyClassLeTwo G)
    {c₀ x y : G} (hc₀ : c₀ ≠ 1) (hx : SameComp c₀ x) (hy : SameComp c₀ y) (hxy1 : x * y ≠ 1) :
    coord c₀ (x * y) = coord c₀ x + coord c₀ y := by
  have hcomm : Commute x y := sameComp_comm htf hnil (sameComp_trans (sameComp_symm hx) hy)
  obtain ⟨m1, n1, hm1, hn1, h1⟩ := hx
  obtain ⟨m2, n2, hm2, hn2, h2⟩ := hy
  have hpow : c₀ ^ (m1 * n2 + m2 * n1) = (x * y) ^ (n1 * n2) := by
    rw [hcomm.mul_zpow, zpow_add]
    congr 1
    · rw [zpow_mul, h1, ← zpow_mul]
    · rw [zpow_mul, h2, ← zpow_mul, mul_comm]
  have hnum_ne : m1 * n2 + m2 * n1 ≠ 0 := by
    intro h0; rw [h0, zpow_zero] at hpow
    exact mul_ne_zero hn1 hn2 ((zpow_eq_one_iff htf hxy1 (n1 * n2)).mp hpow.symm)
  rw [coord_eq_of_pow htf hc₀ hm1 hn1 h1, coord_eq_of_pow htf hc₀ hm2 hn2 h2,
      coord_eq_of_pow htf hc₀ hnum_ne (mul_ne_zero hn1 hn2) hpow]
  have hn1q : (n1 : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hn1
  have hn2q : (n2 : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hn2
  field_simp; push_cast; ring

private lemma coord_inj {G : Type*} [Group G]
    (htf : IsTorsionFreeGroup G) (hnil : NilpotencyClassLeTwo G)
    {c₀ x y : G} (hc₀ : c₀ ≠ 1) (hx : SameComp c₀ x) (hy : SameComp c₀ y)
    (heq : coord c₀ x = coord c₀ y) : x = y := by
  obtain ⟨m1, n1, hm1, hn1, h1⟩ := hx
  obtain ⟨m2, n2, hm2, hn2, h2⟩ := hy
  rw [coord_eq_of_pow htf hc₀ hm1 hn1 h1, coord_eq_of_pow htf hc₀ hm2 hn2 h2] at heq
  have hn1q : (n1 : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hn1
  have hn2q : (n2 : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hn2
  rw [div_eq_div_iff hn1q hn2q] at heq
  have hint : m1 * n2 = m2 * n1 := by exact_mod_cast heq
  have hxy_pow : x ^ (n1 * n2) = y ^ (n1 * n2) := by
    calc x ^ (n1 * n2) = (x ^ n1) ^ n2 := zpow_mul x n1 n2
      _ = (c₀ ^ m1) ^ n2 := by rw [h1]
      _ = c₀ ^ (m1 * n2) := (zpow_mul c₀ m1 n2).symm
      _ = c₀ ^ (m2 * n1) := by rw [hint]
      _ = (c₀ ^ m2) ^ n1 := zpow_mul c₀ m2 n1
      _ = (y ^ n2) ^ n1 := by rw [h2]
      _ = y ^ (n1 * n2) := by rw [← zpow_mul, mul_comm]
  have hcomm_xy : Commute x y :=
    sameComp_comm htf hnil (sameComp_trans (sameComp_symm ⟨m1, n1, hm1, hn1, h1⟩) ⟨m2, n2, hm2, hn2, h2⟩)
  have hcomm : Commute x y⁻¹ := hcomm_xy.inv_right
  have hdiff : (x * y⁻¹) ^ (n1 * n2) = 1 := by
    rw [hcomm.mul_zpow, inv_zpow, hxy_pow, mul_inv_cancel]
  by_contra hne
  have hne1 : x * y⁻¹ ≠ 1 := fun h => hne (mul_inv_eq_one.mp h)
  exact mul_ne_zero hn1 hn2 ((zpow_eq_one_iff htf hne1 (n1 * n2)).mp hdiff)

/-- Locally cyclic property of each connected component: any two elements `x, y` in the
same component lie in `⟨w⟩` for a common element `w` of that component! -/
private lemma comp_locally_cyclic {G : Type*} [Group G]
    (htf : IsTorsionFreeGroup G) (hnil : NilpotencyClassLeTwo G)
    {c₀ x y : G} (hc₀ : c₀ ≠ 1) (hx : SameComp c₀ x) (hy : SameComp c₀ y) :
    ∃ w : G, SameComp c₀ w ∧ (∃ a : ℤ, a ≠ 0 ∧ x = w ^ a) ∧ (∃ b : ℤ, b ≠ 0 ∧ y = w ^ b) := by
  have hx1 : x ≠ 1 := by
    obtain ⟨m, n, hm, _, h⟩ := hx
    rintro rfl; rw [one_zpow] at h; exact hm ((zpow_eq_one_iff htf hc₀ m).mp h)
  have hy1 : y ≠ 1 := by
    obtain ⟨m, n, hm, _, h⟩ := hy
    rintro rfl; rw [one_zpow] at h; exact hm ((zpow_eq_one_iff htf hc₀ m).mp h)
  obtain ⟨m1, n1, hm1, hn1, h1⟩ := hx
  obtain ⟨m2, n2, hm2, hn2, h2⟩ := hy
  have hx' : SameComp c₀ x := ⟨m1, n1, hm1, hn1, h1⟩
  have hy' : SameComp c₀ y := ⟨m2, n2, hm2, hn2, h2⟩
  let A : ℤ := m1 * n2
  let B : ℤ := m2 * n1
  let d : ℤ := n1 * n2
  have hA : A ≠ 0 := mul_ne_zero hm1 hn2
  have hB : B ≠ 0 := mul_ne_zero hm2 hn1
  have hd : d ≠ 0 := mul_ne_zero hn1 hn2
  let g : ℤ := (Int.gcd A B : ℤ)
  have hg_pos : 0 < g := Int.natCast_pos.mpr (Int.gcd_pos_of_ne_zero_left B hA)
  let u : ℤ := Int.gcdA A B
  let v : ℤ := Int.gcdB A B
  have hbez : g = A * u + B * v := Int.gcd_eq_gcd_ab A B
  let w : G := x ^ u * y ^ v
  have hcomm : Commute x y := sameComp_comm htf hnil (sameComp_trans (sameComp_symm hx') hy')
  have hw_pow : c₀ ^ g = w ^ d := by
    have hc_uv : Commute (x ^ u) (y ^ v) := (hcomm.zpow_left u).zpow_right v
    dsimp only [w]
    rw [hc_uv.mul_zpow, ← zpow_mul, ← zpow_mul, hbez, zpow_add]
    have h1' : (x ^ (u * d)) = c₀ ^ (A * u) := by
      calc x ^ (u * d) = (x ^ n1) ^ (n2 * u) := by rw [← zpow_mul]; congr 1; dsimp [d]; ring
        _ = (c₀ ^ m1) ^ (n2 * u) := by rw [h1]
        _ = c₀ ^ (A * u) := by rw [← zpow_mul]; congr 1; dsimp [A]; ring
    have h2' : (y ^ (v * d)) = c₀ ^ (B * v) := by
      calc y ^ (v * d) = (y ^ n2) ^ (n1 * v) := by rw [← zpow_mul]; congr 1; dsimp [d]; ring
        _ = (c₀ ^ m2) ^ (n1 * v) := by rw [h2]
        _ = c₀ ^ (B * v) := by rw [← zpow_mul]; congr 1; dsimp [B]; ring
    rw [h1', h2']
  have hw_sc : SameComp c₀ w := ⟨g, d, by omega, hd, hw_pow⟩
  have hw1 : w ≠ 1 := by
    rintro h; rw [h, one_zpow] at hw_pow
    exact absurd ((zpow_eq_one_iff htf hc₀ g).mp hw_pow) (by omega)
  have hgA : g ∣ A := Int.gcd_dvd_left A B
  have hgB : g ∣ B := Int.gcd_dvd_right A B
  obtain ⟨a, ha⟩ := hgA
  obtain ⟨b, hb⟩ := hgB
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha; exact hA ha
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb; exact hB hb
  have hwa : x = w ^ a := by
    refine coord_inj htf hnil hc₀ hx' ⟨g * a, d, mul_ne_zero (by omega) ha0, hd, ?_⟩ ?_
    · rw [zpow_mul, hw_pow, ← zpow_mul, mul_comm d a, zpow_mul]
    · rw [coord_zpow htf hc₀ hw_sc ha0, coord_eq_of_pow htf hc₀ hm1 hn1 h1,
          coord_eq_of_pow htf hc₀ (by omega) hd hw_pow]
      have hdq : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hd
      have hn1q : (n1 : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hn1
      have hAq : (g : ℚ) * (a : ℚ) = (m1 : ℚ) * (n2 : ℚ) := by exact_mod_cast ha.symm
      dsimp only [d]; push_cast
      field_simp; linarith
  have hwb : y = w ^ b := by
    refine coord_inj htf hnil hc₀ hy' ⟨g * b, d, mul_ne_zero (by omega) hb0, hd, ?_⟩ ?_
    · rw [zpow_mul, hw_pow, ← zpow_mul, mul_comm d b, zpow_mul]
    · rw [coord_zpow htf hc₀ hw_sc hb0, coord_eq_of_pow htf hc₀ hm2 hn2 h2,
          coord_eq_of_pow htf hc₀ (by omega) hd hw_pow]
      have hdq : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hd
      have hn2q : (n2 : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hn2
      have hBq : (g : ℚ) * (b : ℚ) = (m2 : ℚ) * (n1 : ℚ) := by exact_mod_cast hb.symm
      dsimp only [d]; push_cast
      field_simp; linarith
  exact ⟨w, hw_sc, ⟨a, ha0, hwa⟩, ⟨b, hb0, hwb⟩⟩

/-! ### 5. Out-neighborhood `O(x)`, in-neighborhood `I(x)`, and direction rigidity -/

private def OutSet {G : Type*} [Group G] (x : G) : Set G :=
  {y : G | y ≠ 1 ∧ y ≠ x ∧ y ≠ x⁻¹ ∧ NzDir x y}

private def InSet {G : Type*} [Group G] (x : G) : Set G :=
  {y : G | y ≠ 1 ∧ y ≠ x ∧ y ≠ x⁻¹ ∧ NzDir y x}

private def MSet {G : Type*} [Group G] (x : G) : Set G :=
  {y : G | y ≠ 1 ∧ y ≠ x ∧ y ≠ x⁻¹ ∧ NzAdj x y}

private lemma mSet_eq_union {G : Type*} [Group G] (x : G) :
    MSet x = InSet x ∪ OutSet x := by
  ext y
  simp only [MSet, InSet, OutSet, Set.mem_ofPred_eq, Set.mem_union, NzAdj, NzDir]
  constructor
  · rintro ⟨h1, h2, h3, h4, n, hn, h | h⟩
    · exact Or.inr ⟨h1, h2, h3, h4, n, hn, h⟩
    · exact Or.inl ⟨h1, h2, h3, h4.symm, n, hn, h⟩
  · rintro (⟨h1, h2, h3, h4, n, hn, h⟩ | ⟨h1, h2, h3, h4, n, hn, h⟩)
    · exact ⟨h1, h2, h3, h4.symm, n, hn, Or.inr h⟩
    · exact ⟨h1, h2, h3, h4, n, hn, Or.inl h⟩

private lemma outSet_disjoint_inSet {G : Type*} [Group G] (htf : IsTorsionFreeGroup G)
    {x : G} (hx : x ≠ 1) : Disjoint (OutSet x) (InSet x) := by
  rw [Set.disjoint_left]
  intro y hyO hyI
  rcases hyO with ⟨hy1, hyx, hyxi, _, m, hm, hmy⟩
  rcases hyI with ⟨_, _, _, _, n, hn, hnx⟩
  have h1 : x ^ (1 : ℤ) = x ^ (m * n) := by rw [zpow_one, zpow_mul, ← hmy, ← hnx]
  have hmn : 1 = m * n := zpow_inj htf hx h1
  have hm1 : m = 1 ∨ m = -1 := by
    have : m.natAbs * n.natAbs = 1 := by
      have := congrArg Int.natAbs hmn; simpa [Int.natAbs_mul] using this.symm
    have := Nat.eq_one_of_mul_eq_one_right this
    omega
  rcases hm1 with rfl | rfl
  · exact hyx (by simpa using hmy)
  · exact hyxi (by simpa using hmy)

/-- In a torsion-free group, no non-adjacency edge in `M(x)` crosses between `InSet x` and `OutSet x`. -/
private lemma inSet_adj_outSet {G : Type*} [Group G] (htf : IsTorsionFreeGroup G)
    {x y z : G} (hx : x ≠ 1) (hy : y ∈ InSet x) (hz : z ∈ OutSet x) : NzAdj y z := by
  rcases hy with ⟨hy1, hyx, hyxi, _, m, hm, hmx⟩
  rcases hz with ⟨hz1, hzx, hzxi, _, n, hn, hnz⟩
  have hne : y ≠ z := fun h => by
    subst h; exact Set.disjoint_left.mp (outSet_disjoint_inSet htf hx) ⟨hz1, hzx, hzxi, hyx.symm, n, hn, hnz⟩ ⟨hy1, hyx, hyxi, hyx, m, hm, hmx⟩
  exact ⟨hne, m * n, mul_ne_zero hm hn, Or.inl (by rw [hnz, hmx, zpow_mul])⟩

/-- Any two elements of `OutSet x` are at distance ≤ 2 in the complement graph on `M(x)`. -/
private lemma outSet_comp_connected {G : Type*} [Group G] (htf : IsTorsionFreeGroup G)
    {x y z : G} (hx : x ≠ 1) (hy : y ∈ OutSet x) (hz : z ∈ OutSet x) :
    ∃ w ∈ OutSet x, ¬ NzAdj y w ∧ ¬ NzAdj w z := by
  rcases hy with ⟨_, hyx, hyxi, _, a, ha, hya⟩
  rcases hz with ⟨_, hzx, hzxi, _, b, hb, hzb⟩
  have ha2 : 2 ≤ a.natAbs := by
    by_contra hlt; have : a = 1 ∨ a = -1 := by omega
    rcases this with rfl | rfl
    · exact hyx (by simpa using hya)
    · exact hyxi (by simpa using hya)
  have hb2 : 2 ≤ b.natAbs := by
    by_contra hlt; have : b = 1 ∨ b = -1 := by omega
    rcases this with rfl | rfl
    · exact hzx (by simpa using hzb)
    · exact hzxi (by simpa using hzb)
  obtain ⟨p, hp_gt, hp_prime⟩ := Nat.exists_infinite_primes (max a.natAbs b.natAbs + 2)
  let w : G := x ^ (p : ℤ)
  have hp_ge2 : 2 ≤ p := hp_prime.two_le
  have hwO : w ∈ OutSet x := by
    refine ⟨?_, ?_, ?_, ?_, (p : ℤ), by omega, rfl⟩
    · intro h; have := (zpow_eq_one_iff htf hx (p : ℤ)).mp h; omega
    · intro h; have := zpow_inj htf hx (show x ^ (p : ℤ) = x ^ (1 : ℤ) by simpa [w] using h); omega
    · intro h; have := zpow_inj htf hx (show x ^ (p : ℤ) = x ^ (-1 : ℤ) by simpa [w] using h); omega
    · intro h; have := zpow_inj htf hx (show x ^ (1 : ℤ) = x ^ (p : ℤ) by simpa [w] using h); omega
  have hnot_adj : ∀ {c : ℤ}, 2 ≤ c.natAbs → c.natAbs < p → ¬ NzAdj (x ^ c) w := by
    intro c hc2 hcp h
    rcases h with ⟨_, r, hr0, h1 | h2⟩
    · have hcr : (p : ℤ) = c * r := zpow_inj htf hx (by simpa [w, zpow_mul] using h1)
      have hmul : p = c.natAbs * r.natAbs := by
        have := congrArg Int.natAbs hcr; simpa [Int.natAbs_mul] using this
      have hdvd : c.natAbs ∣ p := ⟨r.natAbs, hmul⟩
      rcases hp_prime.eq_one_or_self_of_dvd c.natAbs hdvd with h | h <;> omega
    · have hpr : c = (p : ℤ) * r := zpow_inj htf hx (by simpa [w, zpow_mul] using h2)
      have hmul : c.natAbs = p * r.natAbs := by
        have := congrArg Int.natAbs hpr; simpa [Int.natAbs_mul] using this
      have hr1 : 1 ≤ r.natAbs := Int.natAbs_pos.mpr hr0
      nlinarith
  refine ⟨w, hwO, ?_, ?_⟩
  · rw [hya]; exact hnot_adj ha2 (by omega)
  · intro h; rw [hzb] at h; exact hnot_adj hb2 (by omega) (nzAdj_symm h)

/-- Under a power graph isomorphism `f` with `f 1 = 1` between torsion-free groups,
`f` maps `MSet x` onto `MSet (f x)` and maps `OutSet x` either onto `OutSet (f x)` or into `InSet (f x)`. -/
private lemma image_mSet_eq {G H : Type*} [Group G] [Group H]
    (hGtf : IsTorsionFreeGroup G) (hHtf : IsTorsionFreeGroup H)
    (f : G ≃ H) (hf : ∀ x y, PowerAdj x y ↔ PowerAdj (f x) (f y)) (hf1 : f 1 = 1)
    {x : G} (hx : x ≠ 1) : f '' MSet x = MSet (f x) := by
  have hfx1 : f x ≠ 1 := fun h => hx (f.injective (h.trans hf1.symm))
  have hinv_eq : f x⁻¹ = (f x)⁻¹ := by
    have hs : SameNhd (f x) (f x⁻¹) := (sameNhd_of_iso f hf).mp (sameNhd_inv x)
    have hfxi1 : f x⁻¹ ≠ 1 := fun h => inv_ne_one.mpr hx (f.injective (h.trans hf1.symm))
    rcases sameNhd_tf_eq_or_inv hHtf hfx1 hfxi1 hs with h | h
    · exact absurd (f.injective h) (inv_ne_self_of_tf hGtf hx)
    · exact h
  ext w
  constructor
  · rintro ⟨y, ⟨hy1, hyx, hyxi, hyadj⟩, rfl⟩
    refine ⟨fun h => hy1 (f.injective (h.trans hf1.symm)),
            fun h => hyx (f.injective h),
            fun h => hyxi (f.injective (h.trans hinv_eq.symm)), ?_⟩
    exact (powerAdj_iff_nzAdj hfx1 (fun h => hy1 (f.injective (h.trans hf1.symm)))).mp
      ((hf x y).mp ((powerAdj_iff_nzAdj hx hy1).mpr hyadj))
  · intro ⟨hw1, hwx, hwxi, hwadj⟩
    refine ⟨f.symm w, ⟨?_, ?_, ?_, ?_⟩, f.apply_symm_apply w⟩
    · intro h; exact hw1 (by rw [← hf1, ← h, f.apply_symm_apply])
    · intro h; exact hwx (by rw [← h, f.apply_symm_apply])
    · intro h; exact hwxi (by rw [← hinv_eq, ← h, f.apply_symm_apply])
    · have hy1 : f.symm w ≠ 1 := fun h => hw1 (by rw [← hf1, ← h, f.apply_symm_apply])
      exact (powerAdj_iff_nzAdj hx hy1).mp
        ((hf x (f.symm w)).mpr (by simpa using (powerAdj_iff_nzAdj hfx1 hw1).mpr hwadj))

private lemma image_outSet_dichotomy {G H : Type*} [Group G] [Group H]
    (hGtf : IsTorsionFreeGroup G) (hHtf : IsTorsionFreeGroup H)
    (f : G ≃ H) (hf : ∀ x y, PowerAdj x y ↔ PowerAdj (f x) (f y)) (hf1 : f 1 = 1)
    {x : G} (hx : x ≠ 1) :
    f '' OutSet x = OutSet (f x) ∨ f '' OutSet x ⊆ InSet (f x) := by
  have hfx1 : f x ≠ 1 := fun h => hx (f.injective (h.trans hf1.symm))
  have hm := image_mSet_eq hGtf hHtf f hf hf1 hx
  have hnz : ∀ {u v : G}, u ≠ 1 → v ≠ 1 → (NzAdj u v ↔ NzAdj (f u) (f v)) := fun hu hv => by
    rw [← powerAdj_iff_nzAdj hu hv, hf, powerAdj_iff_nzAdj
      (fun h => hu (f.injective (h.trans hf1.symm)))
      (fun h => hv (f.injective (h.trans hf1.symm)))]
  by_cases hex : ∃ y ∈ OutSet x, f y ∈ OutSet (f x)
  · left
    obtain ⟨y0, hy0O, hfy0O⟩ := hex
    ext w
    constructor
    · rintro ⟨y, hyO, rfl⟩
      have hfyM : f y ∈ MSet (f x) := by
        rw [← hm]; refine ⟨y, ?_, rfl⟩; rw [mSet_eq_union]; exact Or.inr hyO
      rw [mSet_eq_union] at hfyM
      rcases hfyM with hfyI | hfyO
      · exfalso
        obtain ⟨u, huO, hnu1, hnu2⟩ := outSet_comp_connected hGtf hx hyO hy0O
        have hfuM : f u ∈ MSet (f x) := by
          rw [← hm]; refine ⟨u, ?_, rfl⟩; rw [mSet_eq_union]; exact Or.inr huO
        rw [mSet_eq_union] at hfuM
        rcases hfuM with hfuI | hfuO
        · exact hnu2 ((hnz huO.1 hy0O.1).mpr (inSet_adj_outSet hHtf hfx1 hfuI hfy0O))
        · exact hnu1 ((hnz hyO.1 huO.1).mpr (inSet_adj_outSet hHtf hfx1 hfyI hfuO))
      · exact hfyO
    · intro hwO
      have hwM : w ∈ f '' MSet x := by rw [hm, mSet_eq_union]; exact Or.inr hwO
      obtain ⟨y, hyM, rfl⟩ := hwM
      rw [mSet_eq_union] at hyM
      rcases hyM with hyI | hyO
      · exfalso
        obtain ⟨u, huO, hnu1, hnu2⟩ := outSet_comp_connected hHtf hfx1 hwO hfy0O
        have huM : u ∈ f '' MSet x := by rw [hm, mSet_eq_union]; exact Or.inr huO
        obtain ⟨v, hvM, rfl⟩ := huM
        rw [mSet_eq_union] at hvM
        rcases hvM with hvI | hvO
        · exact hnu2 ((hnz hvI.1 hy0O.1).mp (inSet_adj_outSet hGtf hx hvI hy0O))
        · exact hnu1 ((hnz hyI.1 hvO.1).mp (inSet_adj_outSet hGtf hx hyI hvO))
      · exact ⟨y, hyO, rfl⟩
  · right
    push Not at hex
    rintro _ ⟨y, hyO, rfl⟩
    have hfyM : f y ∈ MSet (f x) := by
      rw [← hm]; refine ⟨y, ?_, rfl⟩; rw [mSet_eq_union]; exact Or.inr hyO
    rw [mSet_eq_union] at hfyM
    exact hfyM.resolve_right (hex y hyO)

/-- Key directional lemma (Zahirović Lemma 13): for `x, y ∈ OutSet z` with `x → y` (strict),
`f x → f y` iff `f '' OutSet z = OutSet (f z)`. -/
private lemma dir_iff_outSet_preserved {G H : Type*} [Group G] [Group H]
    (hGtf : IsTorsionFreeGroup G) (hHtf : IsTorsionFreeGroup H)
    (f : G ≃ H) (hf : ∀ x y, PowerAdj x y ↔ PowerAdj (f x) (f y)) (hf1 : f 1 = 1)
    {z x y : G} (hz : z ≠ 1) (hxO : x ∈ OutSet z) (hyO : y ∈ OutSet z)
    (hxy : NzDir x y) (hyx : y ≠ x) (hyxi : y ≠ x⁻¹) :
    NzDir (f x) (f y) ↔ f '' OutSet z = OutSet (f z) := by
  have hfz1 : f z ≠ 1 := fun h => hz (f.injective (h.trans hf1.symm))
  have hfx1 : f x ≠ 1 := fun h => hxO.1 (f.injective (h.trans hf1.symm))
  have hfy1 : f y ≠ 1 := fun h => hyO.1 (f.injective (h.trans hf1.symm))
  have hnz : ∀ {u v : G}, u ≠ 1 → v ≠ 1 → (NzAdj u v ↔ NzAdj (f u) (f v)) := fun hu hv => by
    rw [← powerAdj_iff_nzAdj hu hv, hf, powerAdj_iff_nzAdj
      (fun h => hu (f.injective (h.trans hf1.symm)))
      (fun h => hv (f.injective (h.trans hf1.symm)))]
  -- `S := {u ∈ OutSet z | NzAdj x u ∧ ¬ NzAdj y u}` is INFINITE!
  have hS_inf : Set.Infinite {u : G | u ∈ OutSet z ∧ NzAdj x u ∧ ¬ NzAdj y u} := by
    rcases hxO with ⟨hx1, hxz, hxzi, _, a, ha, hxa⟩
    rcases hxy with ⟨_, k, hk, hyk⟩
    have ha2 : 2 ≤ a.natAbs := by
      by_contra hlt; have : a = 1 ∨ a = -1 := by omega
      rcases this with rfl | rfl
      · exact hxz (by simpa using hxa)
      · exact hxzi (by simpa using hxa)
    have hk2 : 2 ≤ k.natAbs := by
      by_contra hlt; have : k = 1 ∨ k = -1 := by omega
      rcases this with rfl | rfl
      · exact hyx (by simpa using hyk)
      · exact hyxi (by simpa using hyk)
    have hP_inf : Set.Infinite {p : ℕ | p.Prime ∧ k.natAbs < p} := by
      rw [Set.infinite_iff_exists_gt]
      intro N
      obtain ⟨p, hpgt, hp⟩ := Nat.exists_infinite_primes (max N k.natAbs + 1)
      exact ⟨p, ⟨hp, by omega⟩, by omega⟩
    have hmaps : Set.MapsTo (fun p : ℕ => x ^ (p : ℤ)) {p : ℕ | p.Prime ∧ k.natAbs < p}
        {u : G | u ∈ OutSet z ∧ NzAdj x u ∧ ¬ NzAdj y u} := by
      rintro p ⟨hp, hpk⟩
      have hp2 : 2 ≤ p := hp.two_le
      have hap : 2 ≤ (a * (p : ℤ)).natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]; nlinarith
      have hxp_eq : x ^ (p : ℤ) = z ^ (a * (p : ℤ)) := by rw [hxa, ← zpow_mul]
      refine ⟨⟨?_, ?_, ?_, ?_, a * (p : ℤ), mul_ne_zero ha (by omega), hxp_eq⟩,
              ⟨?_, (p : ℤ), by omega, Or.inl rfl⟩, ?_⟩
      · intro h; dsimp only at h; rw [hxp_eq] at h; have := (zpow_eq_one_iff hGtf hz _).mp h; exact mul_ne_zero ha (by omega) this
      · intro h; dsimp only at h; rw [hxp_eq] at h; have := zpow_inj hGtf hz (show z ^ (a * (p : ℤ)) = z ^ (1 : ℤ) by simpa using h)
        have := congrArg Int.natAbs this; simp at this; omega
      · intro h; dsimp only at h; rw [hxp_eq] at h; have := zpow_inj hGtf hz (show z ^ (a * (p : ℤ)) = z ^ (-1 : ℤ) by simpa using h)
        have := congrArg Int.natAbs this; simp at this; omega
      · intro h; dsimp only at h; rw [hxp_eq] at h; have := zpow_inj hGtf hz (show z ^ (1 : ℤ) = z ^ (a * (p : ℤ)) by simpa using h)
        have := congrArg Int.natAbs this; simp at this; omega
      · intro h; dsimp only at h; have := zpow_inj hGtf hx1 (show x ^ (1 : ℤ) = x ^ (p : ℤ) by simpa using h); omega
      · intro hadj
        rcases hadj with ⟨_, r, hr0, h1 | h2⟩
        · have hkr : (p : ℤ) = k * r := zpow_inj hGtf hx1 (by simpa [hyk, zpow_mul] using h1)
          have hmul : p = k.natAbs * r.natAbs := by
            have := congrArg Int.natAbs hkr; simpa [Int.natAbs_mul] using this
          rcases hp.eq_one_or_self_of_dvd k.natAbs ⟨r.natAbs, hmul⟩ with h | h <;> omega
        · have hpr : k = (p : ℤ) * r := zpow_inj hGtf hx1 (by simpa [hyk, zpow_mul] using h2)
          have hmul : k.natAbs = p * r.natAbs := by
            have := congrArg Int.natAbs hpr; simpa [Int.natAbs_mul] using this
          have hr1 : 1 ≤ r.natAbs := Int.natAbs_pos.mpr hr0
          nlinarith
    have hinj : Set.InjOn (fun p : ℕ => x ^ (p : ℤ)) {p : ℕ | p.Prime ∧ k.natAbs < p} := by
      intro p _ q _ h
      have := zpow_inj hGtf hx1 h
      omega
    exact (hP_inf.image hinj).mono hmaps.image_subset
  have hfS_inf : Set.Infinite {w : H | w ∈ f '' OutSet z ∧ NzAdj (f x) w ∧ ¬ NzAdj (f y) w} := by
    refine (hS_inf.image f.injective.injOn).mono ?_
    rintro _ ⟨u, ⟨huO, hxu, hnyu⟩, rfl⟩
    exact ⟨⟨u, huO, rfl⟩, (hnz hxO.1 huO.1).mp hxu, fun h => hnyu ((hnz hyO.1 huO.1).mpr h)⟩
  constructor
  · intro hfxy
    rcases image_outSet_dichotomy hGtf hHtf f hf hf1 hz with heq | hsub
    · exact heq
    · exfalso
      have hfxI : f x ∈ InSet (f z) := hsub ⟨x, hxO, rfl⟩
      have hfyI : f y ∈ InSet (f z) := hsub ⟨y, hyO, rfl⟩
      rcases hfxy with ⟨_, r, hr, hfy_r⟩
      rcases hfyI with ⟨_, _, _, _, s, hs, hfz_s⟩
      have hfz_rs : f z = (f x) ^ (r * s) := by rw [hfz_s, hfy_r, zpow_mul]
      have hbound : {w : H | w ∈ f '' OutSet z ∧ NzAdj (f x) w ∧ ¬ NzAdj (f y) w} ⊆
          insert (f y) ((fun t : ℤ => (f x) ^ t) '' Set.Icc (-(r * s).natAbs : ℤ) ((r * s).natAbs : ℤ)) := by
        intro w ⟨hwim, hfxw, hnfwy⟩
        by_cases hwy : w = f y
        · exact Set.mem_insert_iff.mpr (Or.inl hwy)
        · right
          have hwI : w ∈ InSet (f z) := hsub hwim
          rcases hwI with ⟨_, _, _, _, u, hu, hfz_u⟩
          rcases hfxw with ⟨_, t, ht, h1 | h2⟩
          · -- `w = (f x) ^ t`
            have htu : r * s = t * u := zpow_inj hHtf hfx1 (by rw [← hfz_rs, hfz_u, h1, ← zpow_mul])
            have hle : t.natAbs ≤ (r * s).natAbs := by
              have hmul : (r * s).natAbs = t.natAbs * u.natAbs := by
                have := congrArg Int.natAbs htu; simpa [Int.natAbs_mul] using this
              have hu1 : 1 ≤ u.natAbs := Int.natAbs_pos.mpr hu
              calc t.natAbs = t.natAbs * 1 := (mul_one _).symm
                _ ≤ t.natAbs * u.natAbs := Nat.mul_le_mul_left _ hu1
                _ = (r * s).natAbs := hmul.symm
            exact ⟨t, ⟨by omega, by omega⟩, h1.symm⟩
          · -- `f x = w ^ t` -> `f y = w ^ (t * r)` contradicting `¬ NzAdj (f y) w`!
            exfalso
            exact hnfwy ⟨Ne.symm hwy, t * r, mul_ne_zero ht hr, Or.inr (by rw [hfy_r, h2, ← zpow_mul])⟩
      have hfin : (insert (f y) ((fun t : ℤ => (f x) ^ t) '' Set.Icc (-(r * s).natAbs : ℤ) ((r * s).natAbs : ℤ))).Finite :=
        (Set.finite_Icc _ _).image _ |>.insert _
      exact hfS_inf (hfin.subset hbound)
  · intro heq
    have hfxO : f x ∈ OutSet (f z) := heq ▸ ⟨x, hxO, rfl⟩
    have hfyO : f y ∈ OutSet (f z) := heq ▸ ⟨y, hyO, rfl⟩
    have hfx_adj_fy : NzAdj (f x) (f y) :=
      (hnz hxO.1 hyO.1).mp ⟨hxy.1, hxy.2.choose, hxy.2.choose_spec.1, Or.inl hxy.2.choose_spec.2⟩
    rcases hfx_adj_fy with ⟨hne, r, hr, h1 | h2⟩
    · exact ⟨hne, r, hr, h1⟩
    · exfalso
      rcases hfxO with ⟨_, _, _, _, m, hm, hfx_m⟩
      rcases hfyO with ⟨_, _, _, _, n, hn, hfy_n⟩
      have hm_eq : m = n * r := zpow_inj hHtf hfz1 (by rw [← hfx_m, h2, hfy_n, ← zpow_mul])
      have hbound : {w : H | w ∈ f '' OutSet z ∧ NzAdj (f x) w ∧ ¬ NzAdj (f y) w} ⊆
          insert (f y) ((fun t : ℤ => (f z) ^ t) '' Set.Icc (-(m.natAbs : ℤ)) (m.natAbs : ℤ)) := by
        intro w ⟨hwim, hfxw, hnfwy⟩
        by_cases hwy : w = f y
        · exact Set.mem_insert_iff.mpr (Or.inl hwy)
        · right
          have hwO : w ∈ OutSet (f z) := heq ▸ hwim
          rcases hwO with ⟨_, _, _, _, t, ht, hw_t⟩
          rcases hfxw with ⟨_, u, hu, h1' | h2'⟩
          · -- `w = (f x) ^ u = (f y) ^ (r * u)` contradicting `¬ NzAdj (f y) w`!
            exfalso
            exact hnfwy ⟨Ne.symm hwy, r * u, mul_ne_zero hr hu, Or.inl (by rw [h1', h2, ← zpow_mul])⟩
          · -- `f x = w ^ u`, so `m = t * u`!
            have htu : m = t * u := zpow_inj hHtf hfz1 (by rw [← hfx_m, h2', hw_t, ← zpow_mul])
            have hle : t.natAbs ≤ m.natAbs := by
              have hmul : m.natAbs = t.natAbs * u.natAbs := by
                have := congrArg Int.natAbs htu; simpa [Int.natAbs_mul] using this
              have hu1 : 1 ≤ u.natAbs := Int.natAbs_pos.mpr hu
              calc t.natAbs = t.natAbs * 1 := (mul_one _).symm
                _ ≤ t.natAbs * u.natAbs := Nat.mul_le_mul_left _ hu1
                _ = m.natAbs := hmul.symm
            exact ⟨t, ⟨by omega, by omega⟩, hw_t.symm⟩
      have hfin : (insert (f y) ((fun t : ℤ => (f z) ^ t) '' Set.Icc (-(m.natAbs : ℤ)) (m.natAbs : ℤ))).Finite :=
        (Set.finite_Icc _ _).image _ |>.insert _
      exact hfS_inf (hfin.subset hbound)

private lemma f_inv_eq {G H : Type*} [Group G] [Group H]
    (hGtf : IsTorsionFreeGroup G) (hHtf : IsTorsionFreeGroup H)
    (f : G ≃ H) (hf : ∀ x y, PowerAdj x y ↔ PowerAdj (f x) (f y)) (hf1 : f 1 = 1)
    {x : G} (hx : x ≠ 1) : f x⁻¹ = (f x)⁻¹ := by
  have hfx1 : f x ≠ 1 := fun h => hx (f.injective (h.trans hf1.symm))
  have hfxi1 : f x⁻¹ ≠ 1 := fun h => inv_ne_one.mpr hx (f.injective (h.trans hf1.symm))
  rcases sameNhd_tf_eq_or_inv hHtf hfx1 hfxi1 ((sameNhd_of_iso f hf).mp (sameNhd_inv x)) with h | h
  · exact absurd (f.injective h) (inv_ne_self_of_tf hGtf hx)
  · exact h

private lemma outSet_inv {G : Type*} [Group G] (x : G) : OutSet x⁻¹ = OutSet x := by
  ext y
  simp only [OutSet, Set.mem_ofPred_eq, NzDir, inv_inv]
  constructor
  · rintro ⟨h1, h2, h3, _, n, hn, rfl⟩
    exact ⟨h1, h3, h2, h3.symm, -n, neg_ne_zero.mpr hn, by rw [inv_zpow, zpow_neg]⟩
  · rintro ⟨h1, h2, h3, _, n, hn, rfl⟩
    exact ⟨h1, h3, h2, h3.symm, -n, neg_ne_zero.mpr hn, by rw [inv_zpow, zpow_neg, inv_inv]⟩

private lemma outSet_preserved_of_pow {G H : Type*} [Group G] [Group H]
    (hGtf : IsTorsionFreeGroup G) (hHtf : IsTorsionFreeGroup H)
    (f : G ≃ H) (hf : ∀ x y, PowerAdj x y ↔ PowerAdj (f x) (f y)) (hf1 : f 1 = 1)
    {w u : G} (hw : w ≠ 1) {a : ℤ} (ha : a ≠ 0) (hu : u = w ^ a) :
    f '' OutSet u = OutSet (f u) ↔ f '' OutSet w = OutSet (f w) := by
  have hu1 : u ≠ 1 := by
    rw [hu]; intro h; exact ha ((zpow_eq_one_iff hGtf hw a).mp h)
  have hfu1 : f u ≠ 1 := fun h => hu1 (f.injective (h.trans hf1.symm))
  by_cases ha1 : a.natAbs = 1
  · have hcases : a = 1 ∨ a = -1 := by omega
    rcases hcases with rfl | rfl
    · simp only [zpow_one] at hu; subst hu; exact Iff.rfl
    · simp only [zpow_neg_one] at hu; subst hu
      rw [outSet_inv w, f_inv_eq hGtf hHtf f hf hf1 hw, outSet_inv (f w)]
  · have ha2 : 2 ≤ a.natAbs := by omega
    have huO : u ∈ OutSet w := by
      refine ⟨hu1, ?_, ?_, ?_, a, ha, hu⟩
      · intro h; rw [hu] at h; have := zpow_inj hGtf hw (show w ^ a = w ^ (1 : ℤ) by simpa using h); omega
      · intro h; rw [hu] at h; have := zpow_inj hGtf hw (show w ^ a = w ^ (-1 : ℤ) by simpa using h); omega
      · intro h; rw [hu] at h; have := zpow_inj hGtf hw (show w ^ (1 : ℤ) = w ^ a by simpa using h); omega
    let v := u ^ (2 : ℤ)
    have hv_eq : v = w ^ (a * 2) := by dsimp [v]; rw [hu, ← zpow_mul]
    have hv1 : v ≠ 1 := by
      rw [hv_eq]; intro h; have := (zpow_eq_one_iff hGtf hw (a * 2)).mp h; omega
    have hvu : v ≠ u := fun h => by
      have := zpow_inj hGtf hu1 (show u ^ (2 : ℤ) = u ^ (1 : ℤ) by simpa [v] using h); omega
    have hvui : v ≠ u⁻¹ := fun h => by
      have := zpow_inj hGtf hu1 (show u ^ (2 : ℤ) = u ^ (-1 : ℤ) by simpa [v] using h); omega
    have hvOw : v ∈ OutSet w := by
      refine ⟨hv1, ?_, ?_, ?_, a * 2, mul_ne_zero ha (by omega), hv_eq⟩
      · intro h; rw [hv_eq] at h; have := zpow_inj hGtf hw (show w ^ (a * 2) = w ^ (1 : ℤ) by simpa using h); omega
      · intro h; rw [hv_eq] at h; have := zpow_inj hGtf hw (show w ^ (a * 2) = w ^ (-1 : ℤ) by simpa using h); omega
      · intro h; rw [hv_eq] at h; have := zpow_inj hGtf hw (show w ^ (1 : ℤ) = w ^ (a * 2) by simpa using h); omega
    have hvOu : v ∈ OutSet u := ⟨hv1, hvu, hvui, hvu.symm, 2, by omega, rfl⟩
    have hdir_w := dir_iff_outSet_preserved hGtf hHtf f hf hf1 hw huO hvOw ⟨hvu.symm, 2, by omega, rfl⟩ hvu hvui
    rw [← hdir_w]
    constructor
    · intro heq
      have hfvO : f v ∈ OutSet (f u) := heq ▸ ⟨v, hvOu, rfl⟩
      exact hfvO.2.2.2
    · intro hdir
      rcases image_outSet_dichotomy hGtf hHtf f hf hf1 hu1 with heq | hsub
      · exact heq
      · exfalso
        have hfvI : f v ∈ InSet (f u) := hsub ⟨v, hvOu, rfl⟩
        have hfvO : f v ∈ OutSet (f u) := ⟨hfvI.1, hfvI.2.1, hfvI.2.2.1, hdir⟩
        exact Set.disjoint_left.mp (outSet_disjoint_inSet hHtf hfu1) hfvO hfvI

private lemma outSet_preserved_of_sameComp {G H : Type*} [Group G] [Group H]
    (hGtf : IsTorsionFreeGroup G) (hGnil : NilpotencyClassLeTwo G) (hHtf : IsTorsionFreeGroup H)
    (f : G ≃ H) (hf : ∀ x y, PowerAdj x y ↔ PowerAdj (f x) (f y)) (hf1 : f 1 = 1)
    {c₀ x : G} (hc₀ : c₀ ≠ 1) (hx : SameComp c₀ x) :
    f '' OutSet x = OutSet (f x) ↔ f '' OutSet c₀ = OutSet (f c₀) := by
  obtain ⟨w, hwsc, ⟨a, ha, hc₀w⟩, ⟨b, hb, hxw⟩⟩ := comp_locally_cyclic hGtf hGnil hc₀ (sameComp_refl c₀) hx
  have hw1 : w ≠ 1 := by
    rintro rfl; rw [one_zpow] at hc₀w; exact hc₀ hc₀w
  rw [outSet_preserved_of_pow hGtf hHtf f hf hf1 hw1 hb hxw,
      ← outSet_preserved_of_pow hGtf hHtf f hf hf1 hw1 ha hc₀w]

/-! ### 6. Anti-isomorphic components must be isomorphic to `(ℚ, +)` -/

/-- If `f` reverses direction on the component `C` of `c₀ ≠ 1`, then `coord c₀ '' C = ℚ \ {0}`. -/
private lemma anti_comp_surj_rat {G H : Type*} [Group G] [Group H]
    (hGtf : IsTorsionFreeGroup G) (hGnil : NilpotencyClassLeTwo G) (hHtf : IsTorsionFreeGroup H)
    (f : G ≃ H) (hf : ∀ x y, PowerAdj x y ↔ PowerAdj (f x) (f y)) (hf1 : f 1 = 1)
    {c₀ : G} (hc₀ : c₀ ≠ 1) (hanti : f '' OutSet c₀ ⊆ InSet (f c₀)) :
    ∀ q : ℚ, q ≠ 0 → ∃ x : G, SameComp c₀ x ∧ coord c₀ x = q := by
  -- Helper: on every `x ∈ C`, `f` sends `OutSet x` into `InSet (f x)`, hence `f` sends `InSet x` onto `OutSet (f x)`!
  have hanti_all : ∀ x : G, SameComp c₀ x → f '' OutSet x ⊆ InSet (f x) := by
    intro x hx
    have hx1 : x ≠ 1 := by
      obtain ⟨m, _, hm, _, h⟩ := hx
      rintro rfl; rw [one_zpow] at h; exact hm ((zpow_eq_one_iff hGtf hc₀ m).mp h)
    rcases image_outSet_dichotomy hGtf hHtf f hf hf1 hx1 with heq | hsub
    · exfalso
      have heq0 := (outSet_preserved_of_sameComp hGtf hGnil hHtf f hf hf1 hc₀ hx).mp heq
      have hc2O : c₀ ^ (2 : ℤ) ∈ OutSet c₀ := by
        refine ⟨fun h => by have := (zpow_eq_one_iff hGtf hc₀ 2).mp h; omega,
                fun h => by have := zpow_inj hGtf hc₀ (show c₀ ^ (2 : ℤ) = c₀ ^ (1 : ℤ) by simpa using h); omega,
                fun h => by have := zpow_inj hGtf hc₀ (show c₀ ^ (2 : ℤ) = c₀ ^ (-1 : ℤ) by simpa using h); omega,
                fun h => by have := zpow_inj hGtf hc₀ (show c₀ ^ (1 : ℤ) = c₀ ^ (2 : ℤ) by simpa using h); omega,
                2, by omega, rfl⟩
      have hfc₀1 : f c₀ ≠ 1 := fun h => hc₀ (f.injective (h.trans hf1.symm))
      exact Set.disjoint_left.mp (outSet_disjoint_inSet hHtf hfc₀1) (heq0 ▸ ⟨c₀ ^ (2 : ℤ), hc2O, rfl⟩) (hanti ⟨c₀ ^ (2 : ℤ), hc2O, rfl⟩)
    · exact hsub
  have hrev_dir : ∀ x y : G, SameComp c₀ x → SameComp c₀ y → y ≠ x → y ≠ x⁻¹ →
      (NzDir x y ↔ NzDir (f y) (f x)) := by
    intro x y hx hy hyx hyxi
    have hx1 : x ≠ 1 := by
      obtain ⟨m, _, hm, _, h⟩ := hx; rintro rfl; rw [one_zpow] at h; exact hm ((zpow_eq_one_iff hGtf hc₀ m).mp h)
    have hy1 : y ≠ 1 := by
      obtain ⟨m, _, hm, _, h⟩ := hy; rintro rfl; rw [one_zpow] at h; exact hm ((zpow_eq_one_iff hGtf hc₀ m).mp h)
    have hfx1 : f x ≠ 1 := fun h => hx1 (f.injective (h.trans hf1.symm))
    have hfy1 : f y ≠ 1 := fun h => hy1 (f.injective (h.trans hf1.symm))
    constructor
    · intro hxy
      have hyOx : y ∈ OutSet x := ⟨hy1, hyx, hyxi, hxy⟩
      exact (hanti_all x hx ⟨y, hyOx, rfl⟩).2.2.2
    · intro hfyx
      have hadjH : NzAdj (f x) (f y) := ⟨hfyx.1.symm, hfyx.2.choose, hfyx.2.choose_spec.1, Or.inr hfyx.2.choose_spec.2⟩
      have hadjG : NzAdj x y := (powerAdj_iff_nzAdj hx1 hy1).mp ((hf x y).mpr ((powerAdj_iff_nzAdj hfx1 hfy1).mpr hadjH))
      rcases hadjG with ⟨hne, r, hr, h1 | h2⟩
      · exact ⟨hne, r, hr, h1⟩
      · exfalso
        have hxOy : x ∈ OutSet y := ⟨hx1, hyx.symm, fun h => hyxi (by rw [h, inv_inv]), ⟨hne.symm, r, hr, h2⟩⟩
        have hfxIy : f x ∈ InSet (f y) := hanti_all y hy ⟨x, hxOy, rfl⟩
        have hfxOy : f x ∈ OutSet (f y) := ⟨hfxIy.1, hfxIy.2.1, hfxIy.2.2.1, hfyx⟩
        exact Set.disjoint_left.mp (outSet_disjoint_inSet hHtf hfy1) hfxOy hfxIy
  -- Also `f '' InSet x = OutSet (f x)` for every `x ∈ C`!
  have him_in : ∀ x : G, SameComp c₀ x → f '' InSet x = OutSet (f x) := by
    intro x hx
    have hx1 : x ≠ 1 := by
      obtain ⟨m, _, hm, _, h⟩ := hx; rintro rfl; rw [one_zpow] at h; exact hm ((zpow_eq_one_iff hGtf hc₀ m).mp h)
    have hfx1 : f x ≠ 1 := fun h => hx1 (f.injective (h.trans hf1.symm))
    ext w
    constructor
    · rintro ⟨y, hyI, rfl⟩
      have hysc : SameComp c₀ y := sameComp_trans hx (sameComp_symm (sameComp_of_nzAdj ⟨hyI.2.2.2.1, hyI.2.2.2.2.choose, hyI.2.2.2.2.choose_spec.1, Or.inl hyI.2.2.2.2.choose_spec.2⟩))
      have hdir := (hrev_dir y x hysc hx hyI.2.1.symm (fun h => hyI.2.2.1 (by rw [h, inv_inv]))).mp hyI.2.2.2
      have hfyM : f y ∈ MSet (f x) := by
        rw [← image_mSet_eq hGtf hHtf f hf hf1 hx1]; exact ⟨y, by rw [mSet_eq_union]; exact Or.inl hyI, rfl⟩
      exact ⟨hfyM.1, hfyM.2.1, hfyM.2.2.1, hdir⟩
    · intro hwO
      have hwM : w ∈ f '' MSet x := by
        rw [image_mSet_eq hGtf hHtf f hf hf1 hx1, mSet_eq_union]; exact Or.inr hwO
      obtain ⟨y, hyM, rfl⟩ := hwM
      rw [mSet_eq_union] at hyM
      rcases hyM with hyI | hyO
      · exact ⟨y, hyI, rfl⟩
      · exfalso
        exact Set.disjoint_left.mp (outSet_disjoint_inSet hHtf hfx1) hwO (hanti_all x hx ⟨y, hyO, rfl⟩)
  -- First show `1 / p^k` is in `coord c₀ '' C` for every prime `p` and `k ≥ 1`!
  have hprime_pow : ∀ (p : ℕ), p.Prime → ∀ k : ℕ, 1 ≤ k → ∃ x : G, SameComp c₀ x ∧ coord c₀ x = 1 / (p : ℚ) ^ k := by
    intro p hp k hk
    by_contra hnot
    -- Consider `c₁ := c₀ ^ (p : ℤ) ∈ C`!
    let c₁ : G := c₀ ^ (p : ℤ)
    have hp2 : 2 ≤ p := hp.two_le
    have hc₁_sc : SameComp c₀ c₁ := ⟨(p : ℤ), 1, by omega, by omega, by simp [c₁]⟩
    have hc₁1 : c₁ ≠ 1 := by
      intro h; have := (zpow_eq_one_iff hGtf hc₀ (p : ℤ)).mp h; omega
    have hfc₁1 : f c₁ ≠ 1 := fun h => hc₁1 (f.injective (h.trans hf1.symm))
    have hc₀_in_Ic₁ : c₀ ∈ InSet c₁ := by
      refine ⟨hc₀, ?_, ?_, ?_, (p : ℤ), by omega, rfl⟩
      · intro h; have := zpow_inj hGtf hc₀ (show c₀ ^ (1 : ℤ) = c₀ ^ (p : ℤ) by simpa [c₁] using h); omega
      · intro h; have := zpow_inj hGtf hc₀ (show c₀ ^ (1 : ℤ) = c₀ ^ (-(p : ℤ)) by
          rw [zpow_one, zpow_neg]; exact h); omega
      · intro h; have := zpow_inj hGtf hc₀ (show c₀ ^ (1 : ℤ) = c₀ ^ (p : ℤ) by simpa [c₁] using h); omega
    -- `q₀ := f c₀ ∈ OutSet (f c₁)`!
    let q₀ : H := f c₀
    have hq₀O : q₀ ∈ OutSet (f c₁) := him_in c₁ hc₁_sc ▸ ⟨c₀, hc₀_in_Ic₁, rfl⟩
    rcases hq₀O with ⟨hq₀1, hq₀_ne, hq₀_nei, _, m, hm0, hq₀_m⟩
    have hm2 : 2 ≤ m.natAbs := by
      by_contra hlt; have : m = 1 ∨ m = -1 := by omega
      rcases this with rfl | rfl
      · exact hq₀_ne (by simpa using hq₀_m)
      · exact hq₀_nei (by simpa using hq₀_m)
    -- Show `m.natAbs` is prime!
    have hm_prime : m.natAbs.Prime := by
      rw [Nat.prime_def_lt']
      refine ⟨hm2, fun d hd2 hdlt hdvd => ?_⟩
      obtain ⟨r, hr⟩ := hdvd
      have hr2 : 2 ≤ r := by nlinarith
      let w : H := (f c₁) ^ (d : ℤ)
      have hwO : w ∈ OutSet (f c₁) := by
        refine ⟨fun h => by have := (zpow_eq_one_iff hHtf hfc₁1 (d : ℤ)).mp h; omega,
                fun h => by have := zpow_inj hHtf hfc₁1 (show (f c₁) ^ (d : ℤ) = (f c₁) ^ (1 : ℤ) by simpa [w] using h); omega,
                fun h => by have := zpow_inj hHtf hfc₁1 (show (f c₁) ^ (d : ℤ) = (f c₁) ^ (-1 : ℤ) by simpa [w] using h); omega,
                fun h => by have := zpow_inj hHtf hfc₁1 (show (f c₁) ^ (1 : ℤ) = (f c₁) ^ (d : ℤ) by simpa [w] using h); omega,
                (d : ℤ), by omega, rfl⟩
      obtain ⟨u, huI, hfu⟩ := (him_in c₁ hc₁_sc).symm ▸ hwO
      have husc : SameComp c₀ u := sameComp_trans hc₁_sc (sameComp_symm (sameComp_of_nzAdj ⟨huI.2.2.2.1, huI.2.2.2.2.choose, huI.2.2.2.2.choose_spec.1, Or.inl huI.2.2.2.2.choose_spec.2⟩))
      have hw_dir_q₀ : NzDir w q₀ := by
        refine ⟨fun h => by
          have h' : (f c₁) ^ (d : ℤ) = (f c₁) ^ m := by simpa only [w, hq₀_m] using h
          have := zpow_inj hHtf hfc₁1 h'
          have := congrArg Int.natAbs this; simp at this; omega,
          if 0 ≤ m then (r : ℤ) else -(r : ℤ), by split_ifs <;> omega, ?_⟩
        dsimp only [w]
        rw [hq₀_m, ← zpow_mul]
        congr 1
        rcases Int.natAbs_eq m with hmpos | hmneg
        · have : 0 ≤ m := by omega
          rw [if_pos this, hmpos, hr]; push_cast; rfl
        · have : ¬ 0 ≤ m := by omega
          rw [if_neg this, hmneg, hr]; push_cast; ring
      have huc₀ : u ≠ c₀ := fun h => by
        have : w = q₀ := by rw [← hfu, h]
        exact hw_dir_q₀.1 this
      have huc₀i : u ≠ c₀⁻¹ := fun h => by
        have hwi : w = q₀⁻¹ := by rw [← hfu, h, f_inv_eq hGtf hHtf f hf hf1 hc₀]
        have h1 : (f c₁) ^ (d : ℤ) = (f c₁) ^ (-m) := by rw [zpow_neg, ← hq₀_m]; exact hwi
        have h2 := zpow_inj hHtf hfc₁1 h1
        have h3 := congrArg Int.natAbs h2; simp at h3; omega
      have hc₀_dir_u : NzDir c₀ u :=
        (hrev_dir c₀ u (sameComp_refl c₀) husc huc₀ huc₀i).mpr (by rw [hfu]; exact hw_dir_q₀)
      rcases hc₀_dir_u with ⟨_, a, ha0, hua⟩
      rcases huI with ⟨_, huc1, huc1i, _, b, hb0, hcb⟩
      have hab : (p : ℤ) = a * b := zpow_inj hGtf hc₀ (by
        calc c₀ ^ (p : ℤ) = c₁ := rfl
          _ = u ^ b := hcb
          _ = (c₀ ^ a) ^ b := by rw [hua]
          _ = c₀ ^ (a * b) := (zpow_mul c₀ a b).symm)
      have hmul : p = a.natAbs * b.natAbs := by
        have := congrArg Int.natAbs hab; simpa [Int.natAbs_mul] using this
      rcases hp.eq_one_or_self_of_dvd a.natAbs ⟨b.natAbs, hmul⟩ with ha1 | hap
      · have : a = 1 ∨ a = -1 := by omega
        rcases this with rfl | rfl
        · exact huc₀ (by simpa using hua)
        · exact huc₀i (by simpa using hua)
      · have hb1 : b.natAbs = 1 := by nlinarith
        have : b = 1 ∨ b = -1 := by omega
        rcases this with rfl | rfl
        · exact huc1 (by simpa using hcb.symm)
        · exact huc1i (by rw [show c₁ = u⁻¹ by simpa using hcb, inv_inv])
    -- Now build the chain `w_j = (f c₁) ^ (m.natAbs ^ (j + 1)) ∈ OutSet (f c₁)` for `j = 0, ..., k + 1`!
    let P_m : ℕ := m.natAbs
    have hPm2 : 2 ≤ P_m := hm2
    let topH : H := (f c₁) ^ ((P_m ^ (k + 2) : ℕ) : ℤ)
    have htopH_O : topH ∈ OutSet (f c₁) := by
      have hge2 : 2 ≤ P_m ^ (k + 2) := by
        calc 2 ≤ P_m := hPm2
          _ = P_m ^ 1 := (pow_one _).symm
          _ ≤ P_m ^ (k + 2) := Nat.pow_le_pow_right (by omega) (by omega)
      refine ⟨fun h => by have := (zpow_eq_one_iff hHtf hfc₁1 _).mp h; omega,
              fun h => by have := zpow_inj hHtf hfc₁1 (show (f c₁) ^ ((P_m ^ (k + 2) : ℕ) : ℤ) = (f c₁) ^ (1 : ℤ) by simpa only [topH, zpow_one] using h); omega,
              fun h => by have := zpow_inj hHtf hfc₁1 (show (f c₁) ^ ((P_m ^ (k + 2) : ℕ) : ℤ) = (f c₁) ^ (-1 : ℤ) by simpa only [topH, zpow_neg_one] using h); omega,
              fun h => by have := zpow_inj hHtf hfc₁1 (show (f c₁) ^ (1 : ℤ) = (f c₁) ^ ((P_m ^ (k + 2) : ℕ) : ℤ) by simpa only [topH, zpow_one] using h); omega,
              ((P_m ^ (k + 2) : ℕ) : ℤ), by omega, rfl⟩
    obtain ⟨topG, htopG_I, hftopG⟩ := (him_in c₁ hc₁_sc).symm ▸ htopH_O
    have htopG_I_orig := htopG_I
    rcases htopG_I with ⟨htopG1, _, _, _, D, hD0, hD_eq⟩
    have htopG_sc : SameComp c₀ topG :=
      sameComp_trans hc₁_sc (sameComp_symm ⟨D, 1, hD0, by omega, by simpa using hD_eq.symm⟩)
    -- Every `y ∈ OutSet (f c₁)` with `y → topH` has exponent dividing `P_m ^ (k + 2)`, hence is comparable with `q₀`!
    have hall_comp_q₀ : ∀ w ∈ OutSet (f c₁), NzDir w topH → w = q₀ ∨ w = q₀⁻¹ ∨ NzAdj w q₀ := by
      intro w hwO hwdir
      rcases hwO with ⟨_, hw_ne, hw_nei, _, e, he0, hwe⟩
      rcases hwdir with ⟨_, t, ht0, hwt⟩
      have het : ((P_m ^ (k + 2) : ℕ) : ℤ) = e * t := zpow_inj hHtf hfc₁1 (by
        calc (f c₁) ^ ((P_m ^ (k + 2) : ℕ) : ℤ) = topH := rfl
          _ = w ^ t := hwt
          _ = ((f c₁) ^ e) ^ t := by rw [hwe]
          _ = (f c₁) ^ (e * t) := (zpow_mul _ _ _).symm)
      have hdvd : e.natAbs ∣ P_m ^ (k + 2) := by
        refine ⟨t.natAbs, ?_⟩
        have := congrArg Int.natAbs het; simpa [Int.natAbs_mul] using this
      obtain ⟨j, _, hej⟩ := (Nat.dvd_prime_pow hm_prime).mp hdvd
      have hj1 : 1 ≤ j := by
        by_contra hj0
        have hj0' : j = 0 := by omega
        rw [hj0', pow_zero] at hej
        have : e = 1 ∨ e = -1 := by omega
        rcases this with rfl | rfl
        · exact hw_ne (by simpa using hwe)
        · exact hw_nei (by simpa using hwe)
      by_cases hwq : w = q₀
      · exact Or.inl hwq
      · by_cases hwqi : w = q₀⁻¹
        · exact Or.inr (Or.inl hwqi)
        · right; right
          -- `P_m ∣ e.natAbs`, so `m ∣ e`, hence `w = q₀ ^ (e / m)`!
          have hmdvd : m ∣ e := by
            have : m.natAbs ∣ e.natAbs := by rw [hej]; exact dvd_pow_self P_m (by omega)
            exact Int.natAbs_dvd_natAbs.mp this
          obtain ⟨s, hs⟩ := hmdvd
          have hs0 : s ≠ 0 := by rintro rfl; simp at hs; exact he0 hs
          exact ⟨hwq, s, hs0, Or.inr (by rw [hwe, hs, zpow_mul, ← hq₀_m])⟩
    -- Claim 1: `D.natAbs` has NO prime factor `q ≠ p`!
    have hD_only_p : ∀ q : ℕ, q.Prime → q ∣ D.natAbs → q = p := by
      intro q hq hqD
      by_contra hqp
      obtain ⟨r, hr⟩ := hqD
      have hr0 : r ≠ 0 := by rintro rfl; simp at hr; exact hD0 hr
      -- Let `u := topG ^ r` (or signed): `u ^ q = c₁` (up to sign)!
      let rZ : ℤ := if 0 ≤ D then (r : ℤ) else -(r : ℤ)
      have hD_eq_qr : D = rZ * (q : ℤ) := by
        rcases Int.natAbs_eq D with hpos | hneg
        · have : 0 ≤ D := by omega
          dsimp only [rZ]; rw [if_pos this, hpos, hr]; push_cast; ring
        · have : ¬ 0 ≤ D := by omega
          dsimp only [rZ]; rw [if_neg this, hneg, hr]; push_cast; ring
      let u : G := topG ^ rZ
      have hu_pow : u ^ (q : ℤ) = c₁ := by dsimp [u]; rw [← zpow_mul, ← hD_eq_qr, hD_eq]
      have hu1 : u ≠ 1 := by
        intro h; rw [h, one_zpow] at hu_pow; exact hc₁1 hu_pow.symm
      have hq2 : 2 ≤ q := hq.two_le
      have huI : u ∈ InSet c₁ := by
        refine ⟨hu1, ?_, ?_, ?_, (q : ℤ), by omega, hu_pow.symm⟩
        · intro h; rw [h] at hu_pow
          have := zpow_inj hGtf hc₁1 (show c₁ ^ (q : ℤ) = c₁ ^ (1 : ℤ) by simpa using hu_pow); omega
        · intro h; rw [h, inv_zpow] at hu_pow
          have := zpow_inj hGtf hc₁1 (show c₁ ^ (-(q : ℤ)) = c₁ ^ (1 : ℤ) by simpa [zpow_neg] using hu_pow); omega
        · intro h; rw [h] at hu_pow
          have := zpow_inj hGtf hc₁1 (show c₁ ^ (q : ℤ) = c₁ ^ (1 : ℤ) by simpa using hu_pow); omega
      have husc : SameComp c₀ u :=
        sameComp_trans hc₁_sc (sameComp_symm ⟨(q : ℤ), 1, by omega, by omega, by simpa using hu_pow⟩)
      -- Check `u ≠ c₀`, `u ≠ c₀⁻¹`, and `¬ NzAdj u c₀` (since `coord c₀ u = p / q` and `coord c₀ c₀ = 1` with `q ≠ p` prime)!
      have hu_coord : coord c₀ u = (p : ℚ) / (q : ℚ) :=
        coord_eq_of_pow hGtf hc₀ (by omega) (by omega) (by rw [hu_pow])
      have huc₀ : u ≠ c₀ := fun h => by
        rw [h, coord_self hGtf hc₀] at hu_coord
        have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
        have : (p : ℚ) = (q : ℚ) := by field_simp at hu_coord; linarith
        exact hqp (by exact_mod_cast this.symm)
      have huc₀i : u ≠ c₀⁻¹ := fun h => by
        have hci : coord c₀ c₀⁻¹ = -1 := by
          rw [show c₀⁻¹ = c₀ ^ (-1 : ℤ) by simp, coord_zpow hGtf hc₀ (sameComp_refl c₀) (by omega),
              coord_self hGtf hc₀]; norm_num
        rw [h, hci] at hu_coord
        have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
        have : (p : ℚ) = -(q : ℚ) := by field_simp at hu_coord; linarith
        have : (p : ℤ) + (q : ℤ) = 0 := by exact_mod_cast (by linarith : (p : ℚ) + (q : ℚ) = 0)
        omega
      have hnot_adj : ¬ NzAdj u c₀ := by
        rintro ⟨_, t, ht0, h1 | h2⟩
        · have hct : coord c₀ c₀ = (t : ℚ) * coord c₀ u := by
            conv_lhs => arg 2; rw [h1]
            exact coord_zpow hGtf hc₀ husc ht0
          rw [coord_self hGtf hc₀, hu_coord] at hct
          have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
          have hmul : (q : ℤ) = t * (p : ℤ) := by
            have : (q : ℚ) = (t : ℚ) * (p : ℚ) := by field_simp at hct; linarith
            exact_mod_cast this
          have hdvd : p ∣ q := ⟨t.natAbs, by
            have := congrArg Int.natAbs hmul; simpa [Int.natAbs_mul, mul_comm] using this⟩
          rcases hq.eq_one_or_self_of_dvd p hdvd with h | h
          · exact hp.ne_one h
          · exact hqp h.symm
        · have hct : coord c₀ u = (t : ℚ) * coord c₀ c₀ := by
            rw [h2, coord_zpow hGtf hc₀ (sameComp_refl c₀) ht0]
          rw [coord_self hGtf hc₀, hu_coord, mul_one] at hct
          have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
          have hmul : (p : ℤ) = t * (q : ℤ) := by
            have : (p : ℚ) = (t : ℚ) * (q : ℚ) := by field_simp at hct; linarith
            exact_mod_cast this
          have hdvd : q ∣ p := ⟨t.natAbs, by
            have := congrArg Int.natAbs hmul; simpa [Int.natAbs_mul, mul_comm] using this⟩
          rcases hp.eq_one_or_self_of_dvd q hdvd with h | h
          · exact hq.ne_one h
          · exact hqp h
      -- Yet `f u ∈ OutSet (f c₁)` and either `u = topG^{±1}` or `topG → u` -> `f u → topH`, so `f u` is comparable with `q₀`!
      have hfuO : f u ∈ OutSet (f c₁) := him_in c₁ hc₁_sc ▸ ⟨u, huI, rfl⟩
      have hfu_comp : f u = q₀ ∨ f u = q₀⁻¹ ∨ NzAdj (f u) q₀ := by
        by_cases hut : u = topG
        · right; right
          rw [hut, hftopG]
          have hmdvd : m ∣ ((P_m ^ (k + 2) : ℕ) : ℤ) := by
            have : m.natAbs ∣ P_m ^ (k + 2) := dvd_pow_self P_m (by omega)
            exact Int.natAbs_dvd_natAbs.mp (by simpa using this)
          obtain ⟨s, hs⟩ := hmdvd
          have hs0 : s ≠ 0 := by
            rintro rfl; simp at hs; omega
          refine ⟨fun h => huc₀ (f.injective (by rw [hut, hftopG, h])), s, hs0, Or.inr ?_⟩
          rw [hq₀_m, ← zpow_mul, ← hs]
        · by_cases huti : u = topG⁻¹
          · right; right
            rw [huti, f_inv_eq hGtf hHtf f hf hf1 htopG1, hftopG]
            have hmdvd : m ∣ (-((P_m ^ (k + 2) : ℕ) : ℤ)) := by
              have : m.natAbs ∣ P_m ^ (k + 2) := dvd_pow_self P_m (by omega)
              exact dvd_neg.mpr (Int.natAbs_dvd_natAbs.mp (by simpa using this))
            obtain ⟨s, hs⟩ := hmdvd
            have hs0 : s ≠ 0 := by
              rintro rfl; simp at hs; omega
            refine ⟨fun h => huc₀ (f.injective (by rw [huti, f_inv_eq hGtf hHtf f hf hf1 htopG1, hftopG, h])),
              s, hs0, Or.inr ?_⟩
            rw [hq₀_m, ← zpow_mul, ← hs, zpow_neg]
          · have htop_dir_u : NzDir topG u := ⟨Ne.symm hut, rZ, by dsimp [rZ]; split_ifs <;> omega, rfl⟩
            have hfu_dir_top : NzDir (f u) topH := by
              rw [← hftopG]
              exact (hrev_dir topG u htopG_sc husc hut huti).mp htop_dir_u
            exact hall_comp_q₀ (f u) hfuO hfu_dir_top
      rcases hfu_comp with h | h | h
      · exact huc₀ (f.injective h)
      · exact huc₀i (f.injective (h.trans (f_inv_eq hGtf hHtf f hf hf1 hc₀).symm))
      · exact hnot_adj ((powerAdj_iff_nzAdj hu1 hc₀).mp ((hf u c₀).mpr ((powerAdj_iff_nzAdj (fun h1 => hu1 (f.injective (h1.trans hf1.symm))) (fun h1 => hc₀ (f.injective (h1.trans hf1.symm)))).mpr h)))
    -- Claim 2: `D.natAbs` is a power `p ^ e` with `e ≥ k + 2`!
    -- Indeed, `topH = (f c₁) ^ (P_m ^ (k + 2))` has `k + 1` strict divisors `w_j = (f c₁) ^ (P_m ^ (j + 1))` (`j = 0..k`) in `OutSet (f c₁)`!
    -- Pull them back via `f⁻¹` to `k + 1` elements `u_j ∈ InSet c₁` forming a strict chain `topG → u_k → ... → u_0`!
    -- Each step multiplies the denominator by at least `2` (in fact a positive power of `p`), so `p ^ (k + 2) ∣ D.natAbs`!
    obtain ⟨e, heD⟩ : ∃ e : ℕ, D.natAbs = p ^ e := by
      have hpos : D.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD0
      have hall_p : ∀ q ∈ D.natAbs.primeFactorsList, q = p := fun q hq =>
        hD_only_p q (Nat.prime_of_mem_primeFactorsList hq) (Nat.dvd_of_mem_primeFactorsList hq)
      refine ⟨D.natAbs.primeFactorsList.length, ?_⟩
      conv_lhs => rw [← Nat.prod_primeFactorsList hpos]
      have hprod : ∀ l : List ℕ, (∀ q ∈ l, q = p) → l.prod = p ^ l.length := by
        intro l; induction l with
        | nil => intro _; simp
        | cons a tl ih => intro h; simp [h a (by simp), pow_succ', ih (fun q hq => h q (by simp [hq]))]
      exact hprod _ hall_p
    -- Show `k + 2 ≤ e` by pulling back the chain `w_j = (f c₁) ^ (P_m ^ (j + 1))` for `j = 0, ..., k + 1`!
    have hchain : ∀ j : ℕ, j ≤ k + 1 → ∃ u : G, u ∈ InSet c₁ ∧ f u = (f c₁) ^ ((P_m ^ (j + 1) : ℕ) : ℤ) := by
      intro j _
      have hge2 : 2 ≤ P_m ^ (j + 1) :=
        calc 2 ≤ P_m := hPm2
          _ = P_m ^ 1 := (pow_one _).symm
          _ ≤ P_m ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have hwO : (f c₁) ^ ((P_m ^ (j + 1) : ℕ) : ℤ) ∈ OutSet (f c₁) :=
        ⟨fun h => by have := (zpow_eq_one_iff hHtf hfc₁1 _).mp h; omega,
         fun h => by have := zpow_inj hHtf hfc₁1 (show (f c₁) ^ ((P_m ^ (j + 1) : ℕ) : ℤ) = (f c₁) ^ (1 : ℤ) by simpa only [zpow_one] using h); omega,
         fun h => by have := zpow_inj hHtf hfc₁1 (show (f c₁) ^ ((P_m ^ (j + 1) : ℕ) : ℤ) = (f c₁) ^ (-1 : ℤ) by simpa only [zpow_neg_one] using h); omega,
         fun h => by have := zpow_inj hHtf hfc₁1 (show (f c₁) ^ (1 : ℤ) = (f c₁) ^ ((P_m ^ (j + 1) : ℕ) : ℤ) by simpa only [zpow_one] using h); omega,
         ((P_m ^ (j + 1) : ℕ) : ℤ), by omega, rfl⟩
      have hmem : (f c₁) ^ ((P_m ^ (j + 1) : ℕ) : ℤ) ∈ f '' InSet c₁ := by rw [him_in c₁ hc₁_sc]; exact hwO
      exact hmem
    -- Each `u_j` has `u_j ^ d_j = c₁` (`d_j ≥ 2`), and `u_{j+1} → u_j` strictly so `d_j < d_{j+1}` and `d_j ∣ d_{j+1}`, with `d_{k+1} = D.natAbs = p^e`!
    -- Therefore `p ^ (j + 1) ∣ d_j` by induction on `j`!
    have hpow_ge : ∀ j : ℕ, j ≤ k + 1 → ∀ u : G, u ∈ InSet c₁ → f u = (f c₁) ^ ((P_m ^ (j + 1) : ℕ) : ℤ) →
        ∀ d : ℤ, d ≠ 0 → u ^ d = c₁ → p ^ (j + 1) ∣ d.natAbs := by
      intro j
      induction j with
      | zero =>
        intro _ u huI hfu d hd0 hud
        -- `u ∈ InSet c₁`, `u^d = c₁` and `d.natAbs ≥ 2`; and either `u = c₀^{±1}` (so `d.natAbs = p`) or `f u = (f c₁)^P_m = q₀^{±1}`!
        have hq : f u = q₀ ∨ f u = q₀⁻¹ := by
          rcases Int.natAbs_eq m with hpos | hneg
          · left; rw [hfu, hq₀_m, pow_one, ← hpos]
          · right; rw [hfu, hq₀_m, pow_one, ← zpow_neg]; congr 1; omega
        rcases hq with h | h
        · have huc : u = c₀ := f.injective h
          rw [huc] at hud
          have : d = (p : ℤ) := zpow_inj hGtf hc₀ hud
          rw [this, pow_one]; simp
        · have huc : u = c₀⁻¹ := f.injective (h.trans (f_inv_eq hGtf hHtf f hf hf1 hc₀).symm)
          rw [huc, inv_zpow, ← zpow_neg] at hud
          have : -d = (p : ℤ) := zpow_inj hGtf hc₀ hud
          have : d.natAbs = p := by omega
          rw [this, pow_one]
      | succ j ih =>
        intro hj u huI hfu d hd0 hud
        obtain ⟨u', hu'I, hfu'⟩ := hchain j (by omega)
        have hu'I_orig := hu'I
        rcases hu'I with ⟨hu'1, _, _, _, d', hd'0, hd'eq⟩
        have hpd' : p ^ (j + 1) ∣ d'.natAbs := ih (by omega) u' hu'I_orig hfu' d' hd'0 hd'eq.symm
        -- Note `f u' → f u` strictly (`(f c₁)^(P_m^(j+1))` to `(f c₁)^(P_m^(j+1+1))`)!
        have hdirH : NzDir (f u') (f u) := by
          rw [hfu', hfu]
          refine ⟨fun h => by
            have := zpow_inj hHtf hfc₁1 h
            have hlt : P_m ^ (j + 1) < P_m ^ (j + 1 + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
            omega, (P_m : ℤ), by omega, by rw [← zpow_mul, ← Nat.cast_mul, ← pow_succ]⟩
        have huu' : u ≠ u' := fun h => hdirH.1 (by rw [h])
        have huu'i : u ≠ u'⁻¹ := fun h => by
          have : f u = (f u')⁻¹ := by rw [h, f_inv_eq hGtf hHtf f hf hf1 hu'1]
          rw [hfu, hfu', ← zpow_neg] at this
          have := zpow_inj hHtf hfc₁1 this
          have hPm_pos : 0 < P_m := by omega
          have h1 : (0 : ℤ) < ((P_m ^ (j + 1 + 1) : ℕ) : ℤ) := by positivity
          have h2 : (0 : ℤ) < ((P_m ^ (j + 1) : ℕ) : ℤ) := by positivity
          omega
        have husc : SameComp c₀ u := sameComp_trans hc₁_sc (sameComp_symm ⟨d, 1, hd0, by omega, by simpa using hud⟩)
        have hu'sc : SameComp c₀ u' := sameComp_trans hc₁_sc (sameComp_symm ⟨d', 1, hd'0, by omega, by simpa using hd'eq.symm⟩)
        have hdirG : NzDir u u' := (hrev_dir u u' husc hu'sc huu'.symm (fun h => huu'i (by rw [h, inv_inv]))).mpr hdirH
        rcases hdirG with ⟨_, s, hs0, hus⟩
        have hs2 : 2 ≤ s.natAbs := by
          by_contra hlt; have : s = 1 ∨ s = -1 := by omega
          rcases this with rfl | rfl
          · exact huu'.symm (by simpa using hus)
          · exact huu'i (by rw [show u' = u⁻¹ by simpa using hus, inv_inv])
        have hd_eq : d = s * d' := zpow_inj hGtf huI.1 (by
          calc u ^ d = c₁ := hud
            _ = u' ^ d' := hd'eq
            _ = (u ^ s) ^ d' := by rw [hus]
            _ = u ^ (s * d') := (zpow_mul u s d').symm)
        have hd_abs : d.natAbs = s.natAbs * d'.natAbs := by
          have := congrArg Int.natAbs hd_eq; simpa [Int.natAbs_mul] using this
        -- Also `d.natAbs ∣ D.natAbs = p^e` (since `u = topG` if `j+1 = k+1`, or `topG → u` if `j+1 < k+1`)!
        have hd_dvd_D : d.natAbs ∣ D.natAbs := by
          by_cases hlast : j + 1 = k + 1
          · have hfu_top : f u = topH := by rw [hfu, hlast]
            have hutop : u = topG := f.injective (hfu_top.trans hftopG.symm)
            rw [hutop] at hud
            have : d = D := zpow_inj hGtf htopG1 (hud.trans hD_eq)
            rw [this]
          · have hlt_j : j + 1 + 1 < k + 2 := by omega
            have hPm_pos : 0 < P_m := by omega
            have hdir_topH : NzDir (f u) topH := by
              rw [hfu]
              refine ⟨fun h => by
                have := zpow_inj hHtf hfc₁1 h
                have hlt : P_m ^ (j + 1 + 1) < P_m ^ (k + 2) := Nat.pow_lt_pow_right (by omega) hlt_j
                omega, ((P_m ^ (k - j) : ℕ) : ℤ), Int.ofNat_ne_zero.mpr (pow_ne_zero _ (by omega)), by
                dsimp only [topH]
                rw [← zpow_mul, ← Nat.cast_mul, ← pow_add, show j + 1 + 1 + (k - j) = k + 2 by omega]⟩
            have hutop : topG ≠ u := fun h => hdir_topH.1 (by rw [← h, hftopG])
            have hutopi : topG ≠ u⁻¹ := fun h => by
              have : topH = (f u)⁻¹ := by rw [← hftopG, h, f_inv_eq hGtf hHtf f hf hf1 huI.1]
              rw [hfu, ← zpow_neg] at this
              have := zpow_inj hHtf hfc₁1 this
              have h1 : (0 : ℤ) < ((P_m ^ (k + 2) : ℕ) : ℤ) := by positivity
              have h2 : (0 : ℤ) < ((P_m ^ (j + 1 + 1) : ℕ) : ℤ) := by positivity
              omega
            have hdir_topG : NzDir topG u :=
              (hrev_dir topG u htopG_sc husc hutop.symm (fun h => hutopi (by rw [h, inv_inv]))).mpr (by rw [hftopG]; exact hdir_topH)
            rcases hdir_topG with ⟨_, t, ht0, hut⟩
            have hDt : D = t * d := zpow_inj hGtf htopG1 (by
              calc topG ^ D = c₁ := hD_eq.symm
                _ = u ^ d := hud.symm
                _ = (topG ^ t) ^ d := by rw [hut]
                _ = topG ^ (t * d) := (zpow_mul _ _ _).symm)
            exact ⟨t.natAbs, by have := congrArg Int.natAbs hDt; simpa [Int.natAbs_mul, mul_comm] using this⟩
        -- Since `s.natAbs ≥ 2` and `s.natAbs ∣ d.natAbs ∣ D.natAbs = p^e`, `p ∣ s.natAbs`!
        have hps : p ∣ s.natAbs := by
          obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd (by omega : s.natAbs ≠ 1)
          have hqD : q ∣ D.natAbs := dvd_trans hq_dvd (dvd_trans ⟨d'.natAbs, hd_abs⟩ hd_dvd_D)
          have hqp : q = p := hD_only_p q hq_prime hqD
          rwa [← hqp]
        rw [hd_abs, pow_succ']
        exact mul_dvd_mul hps hpd'
    have hpk2 : p ^ (k + 2) ∣ D.natAbs :=
      hpow_ge (k + 1) le_rfl topG htopG_I_orig hftopG D hD0 hD_eq.symm
    -- Now construct `x` with `coord c₀ x = 1 / p^k`!
    obtain ⟨m_div, hm_div⟩ := hpk2
    have hm_div0 : m_div ≠ 0 := by rintro rfl; simp at hm_div; exact hD0 hm_div
    let coeff : ℤ := if 0 ≤ D then ((m_div * p : ℕ) : ℤ) else -((m_div * p : ℕ) : ℤ)
    have hcoeff0 : coeff ≠ 0 := by
      have hpos : 0 < m_div * p := Nat.mul_pos (Nat.pos_of_ne_zero hm_div0) hp.pos
      dsimp [coeff]; split_ifs <;> omega
    let x : G := topG ^ coeff
    have hx_pow : x ^ ((p ^ k : ℕ) : ℤ) = c₀ := by
      have hD_fac : D = coeff * ((p ^ k : ℕ) : ℤ) * (p : ℤ) := by
        rcases Int.natAbs_eq D with hpos | hneg
        · have : 0 ≤ D := by omega
          dsimp only [coeff]; rw [if_pos this, hpos, hm_div]
          push_cast; ring
        · have : ¬ 0 ≤ D := by omega
          dsimp only [coeff]; rw [if_neg this, hneg, hm_div]
          push_cast; ring
      have hx_p : (x ^ ((p ^ k : ℕ) : ℤ)) ^ (p : ℤ) = c₀ ^ (p : ℤ) := by
        dsimp only [x]
        rw [← zpow_mul, ← zpow_mul, ← mul_assoc, ← hD_fac]
        exact hD_eq.symm
      -- `x ^ (p^k)` and `c₀` are in `SameComp c₀ _`, hence commute!
      have hx_sc : SameComp c₀ (x ^ ((p ^ k : ℕ) : ℤ)) := ⟨(p : ℤ), (p : ℤ), by omega, by omega, hx_p.symm⟩
      exact coord_inj hGtf hGnil hc₀ hx_sc (sameComp_refl c₀) (by
        rw [coord_eq_of_pow hGtf hc₀ (by omega : (p : ℤ) ≠ 0) (by omega : (p : ℤ) ≠ 0) hx_p.symm,
            coord_self hGtf hc₀]; field_simp)
    have hpk_pos : 0 < p ^ k := Nat.pos_of_ne_zero (pow_ne_zero k hp.ne_zero)
    have hx_sc : SameComp c₀ x :=
      ⟨1, ((p ^ k : ℕ) : ℤ), by omega, by omega, by rw [zpow_one, hx_pow]⟩
    have hx_coord : coord c₀ x = 1 / (p : ℚ) ^ k := by
      rw [coord_eq_of_pow hGtf hc₀ (by omega : (1 : ℤ) ≠ 0) (by omega : ((p ^ k : ℕ) : ℤ) ≠ 0) (by rw [zpow_one, hx_pow])]
      push_cast; rfl
    exact hnot ⟨x, hx_sc, hx_coord⟩
  -- Next show `1 / n` is in `coord c₀ '' C` for every `n : ℕ, 1 ≤ n` by strong induction on `n`!
  have hunit_frac : ∀ n : ℕ, 1 ≤ n → ∃ x : G, SameComp c₀ x ∧ coord c₀ x = 1 / (n : ℚ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hn1 : n = 1
      · subst hn1; exact ⟨c₀, sameComp_refl c₀, by rw [coord_self hGtf hc₀]; norm_num⟩
      · obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn1
        let e := n.factorization p
        have he1 : 1 ≤ e := Nat.Prime.factorization_pos_of_dvd hp (by omega) hpn
        have hpe_dvd : p ^ e ∣ n := Nat.ordProj_dvd n p
        obtain ⟨m, hm⟩ := hpe_dvd
        have hm1 : 1 ≤ m := by
          by_contra hm0
          have hm_eq0 : m = 0 := by omega
          rw [hm_eq0, mul_zero] at hm
          omega
        by_cases hm_eq1 : m = 1
        · rw [hm, hm_eq1, mul_one]
          obtain ⟨x, hxsc, hxc⟩ := hprime_pow p hp e he1
          exact ⟨x, hxsc, by push_cast; exact hxc⟩
        · have hcop : Nat.Coprime (p ^ e) m := by
            refine Nat.Coprime.pow_left e ?_
            rw [Nat.Prime.coprime_iff_not_dvd hp]
            intro hpm
            have hpow_dvd : p ^ (e + 1) ∣ n := by
              rw [hm, pow_succ]; exact mul_dvd_mul_left (p ^ e) hpm
            have hle := (hp.pow_dvd_iff_le_factorization (by omega : n ≠ 0)).mp hpow_dvd
            omega
          have hpe_lt : p ^ e < n := by
            rw [hm]; exact lt_mul_of_one_lt_right (Nat.pos_of_ne_zero (pow_ne_zero e hp.ne_zero)) (by omega)
          have hm_lt : m < n := by
            have hpe2 : 2 ≤ p ^ e :=
              calc 2 ≤ p := hp.two_le
                _ = p ^ 1 := (pow_one _).symm
                _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos he1
            rw [hm]; nlinarith
          obtain ⟨x1, hx1sc, hx1c⟩ := hprime_pow p hp e he1
          obtain ⟨x2, hx2sc, hx2c⟩ := ih m hm_lt hm1
          let u : ℤ := Nat.gcdA (p ^ e) m
          let v : ℤ := Nat.gcdB (p ^ e) m
          have hbez : (1 : ℤ) = (p ^ e : ℕ) * u + (m : ℕ) * v := by
            have := Nat.gcd_eq_gcd_ab (p ^ e) m
            rw [hcop] at this; simpa using this
          -- `y := x2 ^ u * x1 ^ v` has `coord c₀ y = u / m + v / p^e = 1 / n`!
          have hq_eq : (u : ℚ) * (1 / (m : ℚ)) + (v : ℚ) * (1 / (p : ℚ) ^ e) = 1 / (n : ℚ) := by
            have hnq : (n : ℚ) = (p : ℚ) ^ e * (m : ℚ) := by rw [hm]; push_cast; rfl
            have hmq : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
            have hpq : (p : ℚ) ^ e ≠ 0 := pow_ne_zero e (Nat.cast_ne_zero.mpr hp.ne_zero)
            have hbq : (1 : ℚ) = (p : ℚ) ^ e * (u : ℚ) + (m : ℚ) * (v : ℚ) := by exact_mod_cast hbez
            rw [hnq]; field_simp; linarith
          -- Handle `u = 0` or `v = 0` cleanly (actually `u ≠ 0` and `v ≠ 0` since `m > 1` and `p^e > 1`!)
          have hu0 : u ≠ 0 := by
            rintro hu; rw [hu, mul_zero, zero_add] at hbez
            have : (m : ℤ) ∣ 1 := ⟨v, hbez⟩
            have := Int.le_of_dvd (by omega) this; omega
          have hv0 : v ≠ 0 := by
            rintro hv; rw [hv, mul_zero, add_zero] at hbez
            have : ((p ^ e : ℕ) : ℤ) ∣ 1 := ⟨u, hbez⟩
            have hpe2 : 2 ≤ p ^ e :=
              calc 2 ≤ p := hp.two_le
                _ = p ^ 1 := (pow_one _).symm
                _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos he1
            have := Int.le_of_dvd (by omega) this; omega
          have hx2u : SameComp c₀ (x2 ^ u) := by
            obtain ⟨a, b, ha, hb, hab⟩ := hx2sc
            exact ⟨a * u, b, mul_ne_zero ha hu0, hb, by rw [zpow_mul, hab, ← zpow_mul, mul_comm b u, zpow_mul]⟩
          have hx1v : SameComp c₀ (x1 ^ v) := by
            obtain ⟨a, b, ha, hb, hab⟩ := hx1sc
            exact ⟨a * v, b, mul_ne_zero ha hv0, hb, by rw [zpow_mul, hab, ← zpow_mul, mul_comm b v, zpow_mul]⟩
          have hne1 : x2 ^ u * x1 ^ v ≠ 1 := by
            intro h1
            have heq : x2 ^ u = (x1 ^ v)⁻¹ := eq_inv_of_mul_eq_one_left h1
            have hci : coord c₀ (x1 ^ v)⁻¹ = -(coord c₀ (x1 ^ v)) := by
              rw [show (x1 ^ v)⁻¹ = (x1 ^ v) ^ (-1 : ℤ) by simp, coord_zpow hGtf hc₀ hx1v (by omega)]; ring
            have hsum0 : coord c₀ (x2 ^ u) + coord c₀ (x1 ^ v) = 0 := by rw [heq, hci]; ring
            rw [coord_zpow hGtf hc₀ hx2sc hu0, hx2c, coord_zpow hGtf hc₀ hx1sc hv0, hx1c, hq_eq] at hsum0
            exact absurd hsum0 (by positivity)
          have hprod_sc : SameComp c₀ (x2 ^ u * x1 ^ v) :=
            (sameComp_mul_zpow hGtf hGnil hx2u hx1v).resolve_left hne1
          refine ⟨x2 ^ u * x1 ^ v, hprod_sc, ?_⟩
          rw [coord_mul hGtf hGnil hc₀ hx2u hx1v hne1,
              coord_zpow hGtf hc₀ hx2sc hu0, hx2c, coord_zpow hGtf hc₀ hx1sc hv0, hx1c, hq_eq]
  -- Finally, for ANY `q ≠ 0`, `q = q.num / q.den`, take `x ^ q.num` where `coord c₀ x = 1 / q.den`!
  intro q hq
  obtain ⟨x, hxsc, hxc⟩ := hunit_frac q.den q.pos
  have hnum0 : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  have hxnum_sc : SameComp c₀ (x ^ q.num) := by
    obtain ⟨a, b, ha, hb, hab⟩ := hxsc
    exact ⟨a * q.num, b, mul_ne_zero ha hnum0, hb, by rw [zpow_mul, hab, ← zpow_mul, mul_comm b q.num, zpow_mul]⟩
  refine ⟨x ^ q.num, hxnum_sc, ?_⟩
  rw [coord_zpow hGtf hc₀ hxsc hnum0, hxc, mul_one_div, Rat.num_div_den]

/-! ### 7. Assemble the directed power graph isomorphism on every component -/

/-- Canonical representative of the `SameComp`-component of `x` (identical for all `y` with `SameComp x y`). -/
private noncomputable def compRep {G : Type*} [Group G] (x : G) : G :=
  Classical.choose (show ({y : G | SameComp x y}).Nonempty from ⟨x, sameComp_refl x⟩)

private lemma compRep_spec {G : Type*} [Group G] (x : G) : SameComp x (compRep x) :=
  Classical.choose_spec (show ({y : G | SameComp x y}).Nonempty from ⟨x, sameComp_refl x⟩)

private lemma compRep_eq_of_sameComp {G : Type*} [Group G] {x y : G} (h : SameComp x y) :
    compRep x = compRep y := by
  have hset : ({z : G | SameComp x z} : Set G) = {z : G | SameComp y z} := by
    ext z; exact ⟨fun hz => sameComp_trans (sameComp_symm h) hz, fun hz => sameComp_trans h hz⟩
  dsimp only [compRep]
  congr 1

private lemma compRep_ne_one {G : Type*} [Group G] (htf : IsTorsionFreeGroup G)
    {x : G} (hx : x ≠ 1) : compRep x ≠ 1 := by
  obtain ⟨m, _, hm, _, h⟩ := compRep_spec x
  intro h1; rw [h1, one_zpow] at h
  exact hm ((zpow_eq_one_iff htf hx m).mp h)

open Classical in
private noncomputable def recipMap {G H : Type*} [Group G] [Group H]
    (hGtf : IsTorsionFreeGroup G) (hGnil : NilpotencyClassLeTwo G) (hHtf : IsTorsionFreeGroup H)
    (f : G ≃ H) (hf : ∀ x y, PowerAdj x y ↔ PowerAdj (f x) (f y)) (hf1 : f 1 = 1)
    (x : G) : G :=
  if hx : x ≠ 1 then
    if hanti : f '' OutSet (compRep x) ⊆ InSet (f (compRep x)) then
      Classical.choose (anti_comp_surj_rat hGtf hGnil hHtf f hf hf1 (compRep_ne_one hGtf hx) hanti
        (coord (compRep x) x)⁻¹ (inv_ne_zero (coord_ne_zero hGtf (compRep_ne_one hGtf hx) (sameComp_symm (compRep_spec x)))))
    else x
  else 1

private lemma recipMap_one {G H : Type*} [Group G] [Group H]
    (hGtf : IsTorsionFreeGroup G) (hGnil : NilpotencyClassLeTwo G) (hHtf : IsTorsionFreeGroup H)
    (f : G ≃ H) (hf : ∀ x y, PowerAdj x y ↔ PowerAdj (f x) (f y)) (hf1 : f 1 = 1) :
    recipMap hGtf hGnil hHtf f hf hf1 1 = 1 := by
  simp [recipMap]

private lemma recipMap_spec_anti {G H : Type*} [Group G] [Group H]
    (hGtf : IsTorsionFreeGroup G) (hGnil : NilpotencyClassLeTwo G) (hHtf : IsTorsionFreeGroup H)
    (f : G ≃ H) (hf : ∀ x y, PowerAdj x y ↔ PowerAdj (f x) (f y)) (hf1 : f 1 = 1)
    {x : G} (hx : x ≠ 1) (hanti : f '' OutSet (compRep x) ⊆ InSet (f (compRep x))) :
    SameComp (compRep x) (recipMap hGtf hGnil hHtf f hf hf1 x) ∧
    coord (compRep x) (recipMap hGtf hGnil hHtf f hf hf1 x) = (coord (compRep x) x)⁻¹ := by
  dsimp only [recipMap]
  rw [dif_pos hx, dif_pos hanti]
  exact Classical.choose_spec (anti_comp_surj_rat hGtf hGnil hHtf f hf hf1 (compRep_ne_one hGtf hx) hanti
    (coord (compRep x) x)⁻¹ (inv_ne_zero (coord_ne_zero hGtf (compRep_ne_one hGtf hx) (sameComp_symm (compRep_spec x)))))

private lemma recipMap_ne_one {G H : Type*} [Group G] [Group H]
    (hGtf : IsTorsionFreeGroup G) (hGnil : NilpotencyClassLeTwo G) (hHtf : IsTorsionFreeGroup H)
    (f : G ≃ H) (hf : ∀ x y, PowerAdj x y ↔ PowerAdj (f x) (f y)) (hf1 : f 1 = 1)
    {x : G} (hx : x ≠ 1) : recipMap hGtf hGnil hHtf f hf hf1 x ≠ 1 := by
  by_cases hanti : f '' OutSet (compRep x) ⊆ InSet (f (compRep x))
  · have hsc := (recipMap_spec_anti hGtf hGnil hHtf f hf hf1 hx hanti).1
    obtain ⟨m, _, hm, _, h⟩ := hsc
    intro h1; rw [h1, one_zpow] at h
    exact hm ((zpow_eq_one_iff hGtf (compRep_ne_one hGtf hx) m).mp h)
  · dsimp only [recipMap]; rw [dif_pos hx, dif_neg hanti]; exact hx

private lemma recipMap_sameComp {G H : Type*} [Group G] [Group H]
    (hGtf : IsTorsionFreeGroup G) (hGnil : NilpotencyClassLeTwo G) (hHtf : IsTorsionFreeGroup H)
    (f : G ≃ H) (hf : ∀ x y, PowerAdj x y ↔ PowerAdj (f x) (f y)) (hf1 : f 1 = 1)
    {x : G} (hx : x ≠ 1) : SameComp x (recipMap hGtf hGnil hHtf f hf hf1 x) := by
  by_cases hanti : f '' OutSet (compRep x) ⊆ InSet (f (compRep x))
  · exact sameComp_trans (compRep_spec x) (recipMap_spec_anti hGtf hGnil hHtf f hf hf1 hx hanti).1
  · dsimp only [recipMap]; rw [dif_pos hx, dif_neg hanti]; exact sameComp_refl x

private lemma recipMap_invol {G H : Type*} [Group G] [Group H]
    (hGtf : IsTorsionFreeGroup G) (hGnil : NilpotencyClassLeTwo G) (hHtf : IsTorsionFreeGroup H)
    (f : G ≃ H) (hf : ∀ x y, PowerAdj x y ↔ PowerAdj (f x) (f y)) (hf1 : f 1 = 1)
    (x : G) : recipMap hGtf hGnil hHtf f hf hf1 (recipMap hGtf hGnil hHtf f hf hf1 x) = x := by
  by_cases hx : x = 1
  · subst hx; simp [recipMap_one]
  · set y := recipMap hGtf hGnil hHtf f hf hf1 x
    have hy : y ≠ 1 := recipMap_ne_one hGtf hGnil hHtf f hf hf1 hx
    have hrep : compRep y = compRep x :=
      compRep_eq_of_sameComp (sameComp_symm (recipMap_sameComp hGtf hGnil hHtf f hf hf1 hx))
    by_cases hanti : f '' OutSet (compRep x) ⊆ InSet (f (compRep x))
    · have hanti_y : f '' OutSet (compRep y) ⊆ InSet (f (compRep y)) := hrep.symm ▸ hanti
      have ⟨hysc, hyc⟩ := recipMap_spec_anti hGtf hGnil hHtf f hf hf1 hx hanti
      have ⟨hzsc, hzc⟩ := recipMap_spec_anti hGtf hGnil hHtf f hf hf1 hy hanti_y
      rw [hrep] at hzsc hzc
      refine coord_inj hGtf hGnil (compRep_ne_one hGtf hx) hzsc (sameComp_symm (compRep_spec x)) ?_
      rw [hzc, hyc, inv_inv]
    · have hanti_y : ¬ f '' OutSet (compRep y) ⊆ InSet (f (compRep y)) := hrep.symm ▸ hanti
      have hyx : y = x := by dsimp [y, recipMap]; rw [dif_pos hx, dif_neg hanti]
      dsimp only [recipMap]; rw [dif_pos hy, dif_neg hanti_y]; exact hyx

private lemma main_proof :
    ∀ (G H : Type) [Group G] [Group H],
      IsTorsionFreeGroup G →
      NilpotencyClassLeTwo G →
      IsoPowerGraph G H →
      IsoDirPowerGraph G H := by
  intro G H _ _ hGtf hGnil ⟨f, hf⟩
  by_cases hcen : ∃ a : G, a ≠ 1 ∧ InCenter a
  · obtain ⟨a, ha1, hac⟩ := hcen
    exact case_nontrivial_center hGtf f hf ha1 hac
  · push Not at hcen
    have hCenG : ∀ x : G, InCenter x → x = 1 := fun x hx => by
      by_contra hx1; exact hcen x hx1 hx
    obtain ⟨hf1, hHtf⟩ := H_torsionFree_of_trivial_center hGtf f hf hCenG
    let ψ := recipMap hGtf hGnil hHtf f hf hf1
    have hψ_invol : ∀ x : G, ψ (ψ x) = x := recipMap_invol hGtf hGnil hHtf f hf hf1
    let ψEquiv : G ≃ G := ⟨ψ, ψ, hψ_invol, hψ_invol⟩
    let φ : G ≃ H := ψEquiv.trans f
    have hφ1 : φ 1 = 1 := by
      change f (recipMap hGtf hGnil hHtf f hf hf1 1) = 1
      rw [recipMap_one, hf1]
    refine ⟨φ, fun x y => ?_⟩
    -- Handle `x = 1` or `y = 1` first!
    by_cases hx1 : x = 1
    · subst hx1
      rw [hφ1]
      constructor
      · rintro ⟨hne, n, rfl⟩; simp at hne
      · rintro ⟨hne, n, h⟩; simp at h; exact absurd h.symm hne
    · by_cases hy1 : y = 1
      · subst hy1
        rw [hφ1]
        have hφx1 : φ x ≠ 1 := fun h => hx1 (φ.injective (h.trans hφ1.symm))
        exact ⟨fun _ => ⟨hφx1, 0, by simp⟩, fun _ => ⟨hx1, 0, by simp⟩⟩
      · -- Both `x ≠ 1` and `y ≠ 1`!
        have hφx1 : φ x ≠ 1 := fun h => hx1 (φ.injective (h.trans hφ1.symm))
        have hφy1 : φ y ≠ 1 := fun h => hy1 (φ.injective (h.trans hφ1.symm))
        rw [dirPowerAdj_iff_nzDir hy1, dirPowerAdj_iff_nzDir hφy1]
        -- Helper: `ψ` preserves `SameComp` and preserves `NzAdj`!
        have hψx1 : ψ x ≠ 1 := recipMap_ne_one hGtf hGnil hHtf f hf hf1 hx1
        have hψy1 : ψ y ≠ 1 := recipMap_ne_one hGtf hGnil hHtf f hf hf1 hy1
        -- Both directions only hold when `SameComp x y`!
        by_cases hsc : SameComp x y
        · have hrep_eq : compRep x = compRep y := compRep_eq_of_sameComp hsc
          set c₀ := compRep x
          have hc₀1 : c₀ ≠ 1 := compRep_ne_one hGtf hx1
          have hxsc : SameComp c₀ x := sameComp_symm (compRep_spec x)
          have hysc : SameComp c₀ y := sameComp_trans hxsc hsc
          by_cases hanti : f '' OutSet c₀ ⊆ InSet (f c₀)
          · -- Anti-isomorphic component: `ψ` reverses `NzDir`, and `f` reverses `NzDir`!
            have hanti_y : f '' OutSet (compRep y) ⊆ InSet (f (compRep y)) := hrep_eq ▸ hanti
            have ⟨hψx_sc, hψx_c⟩ := recipMap_spec_anti hGtf hGnil hHtf f hf hf1 hx1 hanti
            have ⟨hψy_sc, hψy_c⟩ := recipMap_spec_anti hGtf hGnil hHtf f hf hf1 hy1 hanti_y
            rw [← hrep_eq] at hψy_sc hψy_c
            change SameComp c₀ (ψ x) at hψx_sc
            change coord c₀ (ψ x) = (coord c₀ x)⁻¹ at hψx_c
            change SameComp c₀ (ψ y) at hψy_sc
            change coord c₀ (ψ y) = (coord c₀ y)⁻¹ at hψy_c
            -- Check `ψ` reverses `NzDir` on `C`!
            have hψ_rev : NzDir x y ↔ NzDir (ψ y) (ψ x) := by
              have hcx0 : coord c₀ x ≠ 0 := coord_ne_zero hGtf hc₀1 hxsc
              have hcy0 : coord c₀ y ≠ 0 := coord_ne_zero hGtf hc₀1 hysc
              have hpow_sc : ∀ {u : G} {k : ℤ}, SameComp c₀ u → k ≠ 0 → SameComp c₀ (u ^ k) := by
                intro u k hu hk
                obtain ⟨a, b, ha, hb, hab⟩ := hu
                exact ⟨a * k, b, mul_ne_zero ha hk, hb, by rw [zpow_mul, hab, ← zpow_mul, mul_comm b k, zpow_mul]⟩
              constructor
              · rintro ⟨hne, k, hk0, hyk⟩
                refine ⟨fun h => hne (ψEquiv.injective h.symm), k, hk0, ?_⟩
                refine coord_inj hGtf hGnil hc₀1 hψx_sc (hpow_sc hψy_sc hk0) ?_
                rw [coord_zpow hGtf hc₀1 hψy_sc hk0, hψx_c, hψy_c, hyk, coord_zpow hGtf hc₀1 hxsc hk0]
                have hk0q : (k : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hk0
                field_simp
              · rintro ⟨hne, k, hk0, hψxk⟩
                refine ⟨fun h => hne (by rw [h]), k, hk0, ?_⟩
                refine coord_inj hGtf hGnil hc₀1 hysc (hpow_sc hxsc hk0) ?_
                have heq := congrArg (coord c₀) hψxk
                rw [coord_zpow hGtf hc₀1 hψy_sc hk0, hψx_c, hψy_c] at heq
                rw [coord_zpow hGtf hc₀1 hxsc hk0]
                have hk0q : (k : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hk0
                field_simp at heq ⊢
                linarith
            -- Now show `f` reverses `NzDir` between `ψ y` and `ψ x`!
            have hanti_all : ∀ u : G, SameComp c₀ u → f '' OutSet u ⊆ InSet (f u) := by
              intro u husc
              have hu1 : u ≠ 1 := by
                obtain ⟨m, _, hm, _, h⟩ := husc; rintro rfl; rw [one_zpow] at h; exact hm ((zpow_eq_one_iff hGtf hc₀1 m).mp h)
              rcases image_outSet_dichotomy hGtf hHtf f hf hf1 hu1 with heq | hsub
              · exfalso
                have heq0 := (outSet_preserved_of_sameComp hGtf hGnil hHtf f hf hf1 hc₀1 husc).mp heq
                have hc2O : c₀ ^ (2 : ℤ) ∈ OutSet c₀ :=
                  ⟨fun h => by have := (zpow_eq_one_iff hGtf hc₀1 2).mp h; omega,
                   fun h => by have := zpow_inj hGtf hc₀1 (show c₀ ^ (2 : ℤ) = c₀ ^ (1 : ℤ) by simpa using h); omega,
                   fun h => by have := zpow_inj hGtf hc₀1 (show c₀ ^ (2 : ℤ) = c₀ ^ (-1 : ℤ) by simpa using h); omega,
                   fun h => by have := zpow_inj hGtf hc₀1 (show c₀ ^ (1 : ℤ) = c₀ ^ (2 : ℤ) by simpa using h); omega,
                   2, by omega, rfl⟩
                have hfc₀1 : f c₀ ≠ 1 := fun h => hc₀1 (f.injective (h.trans hf1.symm))
                exact Set.disjoint_left.mp (outSet_disjoint_inSet hHtf hfc₀1)
                  (heq0 ▸ ⟨c₀ ^ (2 : ℤ), hc2O, rfl⟩) (hanti ⟨c₀ ^ (2 : ℤ), hc2O, rfl⟩)
              · exact hsub
            change NzDir x y ↔ NzDir (f (ψ x)) (f (ψ y))
            rw [hψ_rev]
            by_cases hpeq : ψ x = ψ y
            · rw [hpeq]; exact ⟨fun h => absurd rfl h.1, fun h => absurd rfl h.1⟩
            · by_cases hpinv : ψ x = (ψ y)⁻¹
              · rw [hpinv, f_inv_eq hGtf hHtf f hf hf1 hψy1]
                exact ⟨fun _ => ⟨inv_ne_self_of_tf hHtf hφy1, -1, by omega, by simp⟩,
                       fun _ => ⟨(inv_ne_self_of_tf hGtf hψy1).symm, -1, by omega, by simp⟩⟩
              · constructor
                · intro hdir
                  have hO : ψ x ∈ OutSet (ψ y) := ⟨hψx1, hpeq, hpinv, hdir⟩
                  exact (hanti_all (ψ y) hψy_sc ⟨ψ x, hO, rfl⟩).2.2.2
                · intro hfdir
                  have hadjH : NzAdj (f (ψ y)) (f (ψ x)) :=
                    ⟨hfdir.1.symm, hfdir.2.choose, hfdir.2.choose_spec.1, Or.inr hfdir.2.choose_spec.2⟩
                  have hadjG : NzAdj (ψ y) (ψ x) := (powerAdj_iff_nzAdj hψy1 hψx1).mp
                    ((hf (ψ y) (ψ x)).mpr ((powerAdj_iff_nzAdj hφy1 hφx1).mpr hadjH))
                  rcases hadjG with ⟨hne, r, hr, h1 | h2⟩
                  · exact ⟨hne, r, hr, h1⟩
                  · exfalso
                    have hOy : ψ y ∈ OutSet (ψ x) :=
                      ⟨hψy1, Ne.symm hpeq, fun h => hpinv (by rw [h, inv_inv]), ⟨hne.symm, r, hr, h2⟩⟩
                    have hI : f (ψ y) ∈ InSet (f (ψ x)) := hanti_all (ψ x) hψx_sc ⟨ψ y, hOy, rfl⟩
                    have hO : f (ψ y) ∈ OutSet (f (ψ x)) := ⟨hI.1, hI.2.1, hI.2.2.1, hfdir⟩
                    exact Set.disjoint_left.mp (outSet_disjoint_inSet hHtf hφx1) hO hI
          · -- Isomorphic component: `ψ x = x`, `ψ y = y`, and `f` preserves `NzDir`!
            have hψx_eq : ψ x = x := by dsimp [ψ, recipMap]; rw [dif_pos hx1, dif_neg hanti]
            have hψy_eq : ψ y = y := by
              dsimp [ψ, recipMap]; rw [dif_pos hy1, dif_neg (hrep_eq ▸ hanti)]
            change NzDir x y ↔ NzDir (f (ψ x)) (f (ψ y))
            rw [hψx_eq, hψy_eq]
            have hpres_c₀ : f '' OutSet c₀ = OutSet (f c₀) :=
              (image_outSet_dichotomy hGtf hHtf f hf hf1 hc₀1).resolve_right hanti
            have hpres_x : f '' OutSet x = OutSet (f x) :=
              (outSet_preserved_of_sameComp hGtf hGnil hHtf f hf hf1 hc₀1 hxsc).mpr hpres_c₀
            have hpres_y : f '' OutSet y = OutSet (f y) :=
              (outSet_preserved_of_sameComp hGtf hGnil hHtf f hf hf1 hc₀1 hysc).mpr hpres_c₀
            by_cases hxy_eq : y = x
            · subst hxy_eq; exact ⟨fun h => absurd rfl h.1, fun h => absurd rfl h.1⟩
            · by_cases hxy_inv : y = x⁻¹
              · subst hxy_inv
                rw [f_inv_eq hGtf hHtf f hf hf1 hx1]
                exact ⟨fun _ => ⟨(inv_ne_self_of_tf hHtf (fun h => hx1 (f.injective (h.trans hf1.symm)))).symm, -1, by omega, by simp⟩,
                       fun _ => ⟨(inv_ne_self_of_tf hGtf hx1).symm, -1, by omega, by simp⟩⟩
              · constructor
                · intro hxy
                  have hyOx : y ∈ OutSet x := ⟨hy1, hxy_eq, hxy_inv, hxy⟩
                  have hfy : f y ∈ OutSet (f x) := hpres_x ▸ (⟨y, hyOx, rfl⟩ : f y ∈ f '' OutSet x)
                  exact hfy.2.2.2
                · intro hfxy
                  have hfyOx : f y ∈ OutSet (f x) :=
                    ⟨fun h => hy1 (f.injective (h.trans hf1.symm)),
                     fun h => hxy_eq (f.injective h),
                     fun h => hxy_inv (f.injective (h.trans (f_inv_eq hGtf hHtf f hf hf1 hx1).symm)),
                     hfxy⟩
                  obtain ⟨y', hy'Ox, hfy'⟩ := hpres_x.symm ▸ hfyOx
                  rw [f.injective hfy'] at hy'Ox
                  exact hy'Ox.2.2.2
        · -- `¬ SameComp x y`: neither `NzDir x y` nor `NzDir (φ x) (φ y)` can hold!
          constructor
          · intro h
            exact absurd (sameComp_of_nzAdj ⟨h.1, h.2.choose, h.2.choose_spec.1, Or.inl h.2.choose_spec.2⟩) hsc
          · intro h
            have hadjH : NzAdj (f (ψ x)) (f (ψ y)) := ⟨h.1, h.2.choose, h.2.choose_spec.1, Or.inl h.2.choose_spec.2⟩
            have hadjG : NzAdj (ψ x) (ψ y) := (powerAdj_iff_nzAdj hψx1 hψy1).mp
              ((hf (ψ x) (ψ y)).mpr ((powerAdj_iff_nzAdj hφx1 hφy1).mpr hadjH))
            have hsc_ψ : SameComp (ψ x) (ψ y) := sameComp_of_nzAdj hadjG
            exact absurd (sameComp_trans (recipMap_sameComp hGtf hGnil hHtf f hf hf1 hx1)
              (sameComp_trans hsc_ψ (sameComp_symm (recipMap_sameComp hGtf hGnil hHtf f hf hf1 hy1)))) hsc

end OMA.P_arxiv_1911_00555

theorem OMA.solution : type_of% @OMA.S_arxiv_1911_00555.main :=
  OMA.P_arxiv_1911_00555.main_proof


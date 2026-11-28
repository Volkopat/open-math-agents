import OMAStatements.S_oeis_a102309

namespace OMA.P_oeis_a102309

private def T (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 (n - 1) ×ˢ Finset.Icc 1 (n - 1)).filter (fun p => p.1 ≤ p.2)

private lemma T_card (q : ℕ) : (T q).card = q.choose 2 := by
  induction q with
  | zero => rfl
  | succ q ih =>
    have hEq : T (q + 1) = T q ∪ (Finset.Icc 1 q).image (fun i => (i, q)) := by
      ext ⟨i, j⟩
      simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
        Finset.mem_union, Finset.mem_image, Nat.add_sub_cancel]
      constructor
      · rintro ⟨⟨⟨hi1, hiq⟩, ⟨hj1, hjq⟩⟩, hij⟩
        by_cases hj : j = q
        · right; exact ⟨i, ⟨hi1, by omega⟩, by simp [hj]⟩
        · left; refine ⟨⟨⟨hi1, by omega⟩, ⟨hj1, by omega⟩⟩, hij⟩
      · rintro (⟨⟨⟨hi1, hiq⟩, ⟨hj1, hjq⟩⟩, hij⟩ | ⟨i', ⟨hi1, hiq⟩, hpair⟩)
        · refine ⟨⟨⟨hi1, by omega⟩, ⟨hj1, by omega⟩⟩, hij⟩
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
          refine ⟨⟨⟨hi1, hiq⟩, ⟨by omega, le_rfl⟩⟩, hiq⟩
    have hdisj : Disjoint (T q) ((Finset.Icc 1 q).image (fun i => (i, q))) := by
      rw [Finset.disjoint_left]
      intro ⟨i, j⟩ h1 h2
      simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at h1
      simp only [Finset.mem_image, Finset.mem_Icc] at h2
      rcases h2 with ⟨i', _, hpair⟩
      have hjq : j = q := (Prod.mk.inj hpair).2.symm
      omega
    have hinj : Function.Injective (fun i : ℕ => (i, q)) := fun a b h => (Prod.mk.inj h).1
    rw [hEq, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj,
      Nat.card_Icc, Nat.add_sub_cancel, ih, Nat.choose_succ_succ, Nat.choose_one_right]
    ring

private lemma diff_A100448 {n : ℕ} (hn : 1 ≤ n) :
    (OMA.S_oeis_a102309.A100448 n : ℤ) - OMA.S_oeis_a102309.A100448 (n - 1) =
      (((T n).filter (fun p => Nat.gcd p.1 (Nat.gcd p.2 n) = 1)).card : ℤ) := by
  let S := fun m : ℕ =>
    (Finset.Icc 1 m ×ˢ Finset.Icc 1 m ×ˢ Finset.Icc 1 m).filter
      (fun t : ℕ × ℕ × ℕ => t.1 ≤ t.2.1 ∧ t.2.1 < t.2.2 ∧ Nat.gcd t.1 (Nat.gcd t.2.1 t.2.2) = 1)
  let R : Finset (ℕ × ℕ × ℕ) :=
    ((T n).filter (fun p => Nat.gcd p.1 (Nat.gcd p.2 n) = 1)).image (fun p => (p.1, p.2, n))
  have hEq : S n = S (n - 1) ∪ R := by
    ext ⟨i, j, k⟩
    simp only [S, R, T, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_product, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨hi1, hin⟩, ⟨hj1, hjn⟩, ⟨hk1, hkn⟩⟩, hij, hjk, hgcd⟩
      by_cases hkn1 : k ≤ n - 1
      · left; refine ⟨⟨⟨hi1, by omega⟩, ⟨hj1, by omega⟩, ⟨hk1, hkn1⟩⟩, hij, hjk, hgcd⟩
      · right
        have hkn_eq : k = n := by omega
        subst hkn_eq
        exact ⟨(i, j), ⟨⟨⟨⟨hi1, by omega⟩, ⟨hj1, by omega⟩⟩, hij⟩, hgcd⟩, rfl⟩
    · rintro (⟨⟨⟨hi1, hin⟩, ⟨hj1, hjn⟩, ⟨hk1, hkn⟩⟩, hij, hjk, hgcd⟩ | ⟨⟨i', j'⟩, ⟨⟨⟨⟨hi1, hin⟩, ⟨hj1, hjn⟩⟩, hij⟩, hgcd⟩, htrip⟩)
      · refine ⟨⟨⟨hi1, by omega⟩, ⟨hj1, by omega⟩, ⟨hk1, by omega⟩⟩, hij, hjk, hgcd⟩
      · have h1 : i' = i := congrArg Prod.fst htrip
        have h2 : j' = j := congrArg (fun x => x.2.1) htrip
        have h3 : n = k := congrArg (fun x => x.2.2) htrip
        subst h1 h2 h3
        refine ⟨⟨⟨hi1, by omega⟩, ⟨hj1, by omega⟩, ⟨hn, le_rfl⟩⟩, hij, by omega, hgcd⟩
  have hdisj : Disjoint (S (n - 1)) R := by
    rw [Finset.disjoint_left]
    intro ⟨i, j, k⟩ h1 h2
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at h1
    simp only [R, Finset.mem_image] at h2
    rcases h2 with ⟨p, _, hp⟩
    have hk : n = k := congrArg (fun x => x.2.2) hp
    omega
  have hinj : Function.Injective (fun p : ℕ × ℕ => (p.1, p.2, n)) := by
    intro ⟨a1, a2⟩ ⟨b1, b2⟩ h
    dsimp at h
    exact Prod.ext (Prod.mk.inj h).1 (Prod.mk.inj (Prod.mk.inj h).2).1
  have hcard : OMA.S_oeis_a102309.A100448 n =
      OMA.S_oeis_a102309.A100448 (n - 1) +
        ((T n).filter (fun p => Nat.gcd p.1 (Nat.gcd p.2 n) = 1)).card := by
    change (S n).card = (S (n - 1)).card + _
    rw [hEq, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj]
  omega

private lemma T_filter_dvd_card {n d : ℕ} (hn : 1 ≤ n) (hd : d ∈ n.divisors) :
    ((T n).filter (fun p => d ∣ Nat.gcd p.1 (Nat.gcd p.2 n))).card = (n / d).choose 2 := by
  have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hmul : d * (n / d) = n := Nat.mul_div_cancel' hdn
  have hEq : (T (n / d)).image (fun p => (d * p.1, d * p.2)) =
      (T n).filter (fun p => d ∣ Nat.gcd p.1 (Nat.gcd p.2 n)) := by
    ext ⟨x, y⟩
    simp only [Finset.mem_image, Finset.mem_filter, T, Finset.mem_product, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨a, b⟩, ⟨⟨⟨ha1, haq⟩, ⟨hb1, hbq⟩⟩, hab⟩, hxy⟩
      obtain ⟨hx, hy⟩ := Prod.mk.inj hxy
      subst hx hy
      have hq1 : 1 ≤ n / d := by
        by_contra hq0
        have : n / d = 0 := by omega
        rw [this, mul_zero] at hmul
        omega
      have hbx : d * b ≤ n - 1 := by
        have hb1q : b + 1 ≤ n / d := by omega
        have h1 : d * (b + 1) ≤ d * (n / d) := Nat.mul_le_mul_left d hb1q
        rw [mul_add, mul_one, hmul] at h1
        omega
      refine ⟨⟨⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, hbx⟩⟩,
        Nat.mul_le_mul_left d hab⟩, ?_⟩
      exact Nat.dvd_gcd (dvd_mul_right d a) (Nat.dvd_gcd (dvd_mul_right d b) hdn)
    · rintro ⟨⟨⟨⟨hx1, hxn⟩, ⟨hy1, hyn⟩⟩, hxy⟩, hd_gcd⟩
      rw [Nat.dvd_gcd_iff, Nat.dvd_gcd_iff] at hd_gcd
      rcases hd_gcd with ⟨hdx, hdy, _⟩
      refine ⟨(x / d, y / d), ?_, Prod.ext (Nat.mul_div_cancel' hdx) (Nat.mul_div_cancel' hdy)⟩
      have hxa : d * (x / d) = x := Nat.mul_div_cancel' hdx
      have hyb : d * (y / d) = y := Nat.mul_div_cancel' hdy
      have ha1 : 1 ≤ x / d := Nat.div_pos (Nat.le_of_dvd hx1 hdx) hd_pos
      have hb1 : 1 ≤ y / d := Nat.div_pos (Nat.le_of_dvd hy1 hdy) hd_pos
      have hab : x / d ≤ y / d := by
        apply Nat.le_of_mul_le_mul_left _ hd_pos
        rw [hxa, hyb]
        exact hxy
      have hbq : y / d ≤ n / d - 1 := by
        by_contra hbq'
        have hqb : n / d ≤ y / d := by omega
        have h1 : d * (n / d) ≤ d * (y / d) := Nat.mul_le_mul_left d hqb
        rw [hmul, hyb] at h1
        omega
      exact ⟨⟨⟨ha1, by omega⟩, ⟨hb1, hbq⟩⟩, hab⟩
  have hinj : Function.Injective (fun p : ℕ × ℕ => (d * p.1, d * p.2)) := by
    intro ⟨a1, a2⟩ ⟨b1, b2⟩ h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    exact Prod.ext (Nat.mul_left_cancel hd_pos h1) (Nat.mul_left_cancel hd_pos h2)
  rw [← hEq, Finset.card_image_of_injective _ hinj, T_card]

private lemma sum_moebius_divisors (g : ℕ) :
    ∑ d ∈ g.divisors, (ArithmeticFunction.moebius d : ℤ) = if g = 1 then 1 else 0 := by
  have h := congrArg (fun F : ArithmeticFunction ℤ => F g) ArithmeticFunction.moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  exact h

end OMA.P_oeis_a102309

theorem OMA.solution : type_of% @OMA.S_oeis_a102309.main := by
  intro n hn
  rw [OMA.P_oeis_a102309.diff_A100448 hn]
  rw [OMA.S_oeis_a102309.a]
  have hterm : ∀ d ∈ n.divisors,
      (ArithmeticFunction.moebius d : ℤ) * (((n / d).choose 2 : ℕ) : ℤ) =
        ∑ p ∈ OMA.P_oeis_a102309.T n,
          if d ∣ Nat.gcd p.1 (Nat.gcd p.2 n) then (ArithmeticFunction.moebius d : ℤ) else 0 := by
    intro d hd
    rw [← OMA.P_oeis_a102309.T_filter_dvd_card hn hd, Finset.card_filter, Nat.cast_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  have hinner : ∀ p ∈ OMA.P_oeis_a102309.T n,
      (∑ d ∈ n.divisors,
        if d ∣ Nat.gcd p.1 (Nat.gcd p.2 n) then (ArithmeticFunction.moebius d : ℤ) else 0) =
        if Nat.gcd p.1 (Nat.gcd p.2 n) = 1 then 1 else 0 := by
    intro p _
    let g := Nat.gcd p.1 (Nat.gcd p.2 n)
    have hgn : g ∣ n := dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _)
    have hfilt : n.divisors.filter (fun d => d ∣ g) = g.divisors := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨_, hn0⟩, hdg⟩
        refine ⟨hdg, ?_⟩
        intro hg0
        rw [hg0, zero_dvd_iff] at hgn
        exact hn0 hgn
      · rintro ⟨hdg, _⟩
        exact ⟨⟨dvd_trans hdg hgn, by omega⟩, hdg⟩
    rw [← Finset.sum_filter, hfilt]
    exact OMA.P_oeis_a102309.sum_moebius_divisors g
  rw [Finset.sum_congr rfl hinner, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs <;> simp

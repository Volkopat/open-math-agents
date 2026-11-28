import OMAStatements.S_wp_does_every_rational_number_with_an_odd_denominator_have_an_odd_greedy_expansion

-- Reduction wp-does-every-rational-number-with-an-odd-denominator-have-an-odd-greedy-expansion.R1 of Does every rational number with an odd denominator have an odd greedy expansion?
-- Credit: @Pixelstorm44
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_wp_does_every_rational_number_with_an_odd_denominator_have_an_odd_greedy_expansion_R1

/-- For numerator two, the ordinary greedy iteration below one third eventually
has numerator zero or one. -/
def H1 : Prop :=
  let step := fun x : ℚ => x - 1 / ((sInf {d : ℕ | Odd d ∧ 1 / (d : ℚ) ≤ x} : ℕ) : ℚ)
  ∀ x : ℚ, 0 < x → x < 1/3 → Odd x.den → x.num = 2 →
    ∃ k : ℕ, ((step^[k]) x).num.natAbs < 2

/-- Every larger numerator eventually drops below its starting value. -/
def H2 : Prop :=
  let step := fun x : ℚ => x - 1 / ((sInf {d : ℕ | Odd d ∧ 1 / (d : ℚ) ≤ x} : ℕ) : ℚ)
  ∀ x : ℚ, 0 < x → x < 1/3 → Odd x.den → 2 < x.num →
    ∃ k : ℕ, ((step^[k]) x).num.natAbs < x.num.natAbs

lemma least_exists {x : ℚ} (hx : 0 < x) :
    IsLeast {d : ℕ | Odd d ∧ 1 / (d : ℚ) ≤ x}
      (sInf {d : ℕ | Odd d ∧ 1 / (d : ℚ) ≤ x}) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / x)
  have hex : Set.Nonempty {d : ℕ | Odd d ∧ 1 / (d : ℚ) ≤ x} := by
    refine ⟨2*n+1, ⟨n,rfl⟩, le_of_lt ?_⟩
    apply (one_div_lt (by positivity) hx).2
    push_cast
    linarith
  exact ⟨Nat.sInf_mem hex, fun _ h => Nat.sInf_le h⟩

private lemma odd_sub_unit {x : ℚ} {d : ℕ} (hx : Odd x.den) (hd : Odd d) :
    Odd (x - 1 / (d : ℚ)).den := by
  apply Odd.of_dvd_nat _ (Rat.sub_den_dvd _ _)
  apply hx.mul
  simpa [one_div, Rat.inv_natCast_den_of_pos hd.pos] using hd

/-- Once x is below 1/3, the new residual is strictly below the reciprocal
just taken. Earlier denominators can no longer affect later choices. -/
private lemma strict_gap {x : ℚ} {d : ℕ} (hx : x < 1/3)
    (hd : IsLeast {j : ℕ | Odd j ∧ 1 / (j : ℚ) ≤ x} d) :
    x - 1 / (d : ℚ) < 1 / (d : ℚ) := by
  obtain ⟨⟨n, hn⟩, hu⟩ := hd.1
  have h3 : 3 < d := by
    by_contra! h
    have := one_div_le_one_div_of_le (show 0 < (d : ℚ) by exact_mod_cast hd.1.1.pos)
      (show (d : ℚ) ≤ 3 by exact_mod_cast h)
    linarith
  have hn2 : 2 ≤ n := by omega
  let j := 2*(n-1)+1
  have hj : Odd j := ⟨n-1,rfl⟩
  have hjd : j + 2 = d := by dsimp [j]; omega
  have hskip : x < 1 / (j : ℚ) := by
    by_contra! hh
    have := hd.2 (show j ∈ {k : ℕ | Odd k ∧ 1 / (k : ℚ) ≤ x} from ⟨hj,hh⟩)
    omega
  have hpos : 0 < (j : ℚ) := by exact_mod_cast hj.pos
  have hdpos : 0 < (d : ℚ) := by exact_mod_cast hd.1.1.pos
  have hh : 1 / (j : ℚ) ≤ 2 / (d : ℚ) := by
    apply (div_le_div_iff₀ hpos hdpos).2
    have : d ≤ 2*j := by omega
    exact_mod_cast (by simpa using this : 1*d ≤ 2*j)
  rw [show (2 : ℚ) / d = 1/d + 1/d by ring] at hh
  linarith

private lemma harmonic_unbounded (x : ℚ) : ∃ m, x < harmonic m := by
  let y := Real.exp ((x : ℝ) + 1)
  refine ⟨⌊y⌋₊, ?_⟩
  have h := log_le_harmonic_floor y (Real.exp_pos _).le
  dsimp [y] at h
  rw [Real.log_exp] at h
  exact_mod_cast (by linarith : (x : ℝ) < (harmonic ⌊y⌋₊ : ℝ))

-- Prepending a least admissible denominator raises the lower cutoff by two.
private lemma attach {b d : ℕ} {x : ℚ} {ds : List ℕ}
    (hd : IsLeast {j : ℕ | Odd j ∧ b ≤ j ∧ 1 / (j : ℚ) ≤ x} d)
    (hs : (ds.map fun j : ℕ => 1 / (j : ℚ)).sum = x - 1/(d : ℚ))
    (ht : ∀ (i : ℕ) (hi : i < ds.length),
      IsLeast {j : ℕ | Odd j ∧ d+2 ≤ j ∧ j ∉ ds.take i ∧
        1/(j : ℚ) ≤ x - 1/(d : ℚ) - ((ds.take i).map fun k : ℕ => 1/(k : ℚ)).sum} ds[i]) :
    ((d :: ds).map fun j : ℕ => 1 / (j : ℚ)).sum = x ∧
    ∀ (i : ℕ) (hi : i < (d :: ds).length),
      IsLeast {j : ℕ | Odd j ∧ b ≤ j ∧ j ∉ (d :: ds).take i ∧
        1/(j : ℚ) ≤ x - (((d :: ds).take i).map fun k : ℕ => 1/(k : ℚ)).sum} (d :: ds)[i] := by
  refine ⟨by simp only [List.map_cons, List.sum_cons, hs]; ring, ?_⟩
  intro i hi
  cases i with
  | zero => simpa using hd
  | succ i =>
    have hi' : i < ds.length := by simpa using hi
    have tail := ht i hi'
    simp only [List.take_succ_cons, List.mem_cons, not_or, List.map_cons, List.sum_cons,
      List.getElem_cons_succ, ← sub_sub] 
    have heq : ∀ j : ℕ, Odd j →
        1/(j : ℚ) ≤ x - 1/(d : ℚ) - ((ds.take i).map fun k : ℕ => 1/(k : ℚ)).sum →
        (b ≤ j ∧ j ≠ d ↔ d+2 ≤ j) := by
      intro j hj hjx
      have hn : 0 ≤ ((ds.take i).map fun k : ℕ => 1/(k : ℚ)).sum := by
        apply List.sum_nonneg
        simp only [List.mem_map, forall_exists_index, and_imp]
        rintro _ k _ rfl
        positivity
      constructor
      · rintro ⟨hb, hne⟩
        have hdx : 0 ≤ 1/(d : ℚ) := by positivity
        have hle := hd.2 (show j ∈ {j : ℕ | Odd j ∧ b ≤ j ∧ 1/(j : ℚ) ≤ x}
          from ⟨hj, hb, by linarith⟩)
        obtain ⟨a,ha⟩ := hj
        obtain ⟨c,hc⟩ := hd.1.1
        omega
      · have := hd.1.2.1
        omega
    convert tail using 1
    ext j
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨ho,hb,⟨hne,hm⟩,hv⟩
      exact ⟨ho,(heq j ho hv).mp ⟨hb,hne⟩,hm,hv⟩
    · rintro ⟨ho,hl,hm,hv⟩
      obtain ⟨hb,hne⟩ := (heq j ho hv).mpr hl
      exact ⟨ho,hb,⟨hne,hm⟩,hv⟩

-- Handle an arbitrary lower cutoff, provided it excludes no affordable odd unit.
private lemma small_termination (h1 : H1) (h2 : H2) (G : ℕ → ℚ → Prop)
    (empty : ∀ b, G b 0)
    (cons : ∀ {b d : ℕ} {x : ℚ}, IsLeast {j : ℕ | Odd j ∧ b ≤ j ∧ 1/(j : ℚ) ≤ x} d →
      G (d+2) (x-1/(d : ℚ)) → G b x)
    {x : ℚ} (hx : 0 < x) (hs : x < 1/3) (ho : Odd x.den)
    {b : ℕ} (hc : ∀ j : ℕ, Odd j → 1/(j : ℚ) ≤ x → b ≤ j) : G b x := by
  classical
  let denom := fun y : ℚ => sInf {j : ℕ | Odd j ∧ 1/(j : ℚ) ≤ y}
  let step := fun y : ℚ => y - 1 / (denom y : ℚ)
  let bad := fun y : ℚ => 0 < y ∧ y < 1/3 ∧ Odd y.den ∧
    ∃ a : ℕ, (∀ j : ℕ, Odd j → 1/(j : ℚ) ≤ y → a ≤ j) ∧ ¬G a y
  have next {y} (hy : bad y) : bad (step y) := by
    obtain ⟨hp, hsmall, hodd, a, ha, hbad⟩ := hy
    have hl := least_exists hp
    change IsLeast _ (denom y) at hl
    have hu := hl.1.2
    have hd := hl.1.1
    have hnext : ¬ G (denom y + 2) (step y) := by
      intro hg
      apply hbad
      refine cons ⟨⟨hd, ha _ hd hu, hu⟩, ?_⟩ hg
      exact fun j hj => hl.2 ⟨hj.1,hj.2.2⟩
    have hne : step y ≠ 0 := fun he => hnext (he ▸ empty _)
    have hnn : 0 ≤ step y := sub_nonneg.mpr hu
    have hu0 : 0 ≤ 1/(denom y : ℚ) := by positivity
    refine ⟨lt_of_le_of_ne hnn hne.symm, lt_of_le_of_lt (sub_le_self _ hu0) hsmall,
      odd_sub_unit hodd hd, denom y + 2, ?_, hnext⟩
    intro j hj hjx
    have hgap := strict_gap hsmall hl
    have hlt : denom y < j := by
      by_contra! hn
      have := one_div_le_one_div_of_le (show 0 < (j : ℚ) by exact_mod_cast hj.pos)
        (show (j : ℚ) ≤ denom y by exact_mod_cast hn)
      change 1/(j : ℚ) ≤ y - 1/(denom y : ℚ) at hjx
      linarith
    obtain ⟨m,hm⟩ := hd
    obtain ⟨n,hn⟩ := hj
    omega
  have iter {y} (hy : bad y) (k : ℕ) : bad ((step^[k]) y) := by
    induction k with
    | zero => exact hy
    | succ k ih => rw [Function.iterate_succ_apply']; exact next ih
  by_contra hf
  have initial : bad x := ⟨hx,hs,ho,b,hc,hf⟩
  have hw : ∃ m : ℕ, ∃ t : ℚ, bad t ∧ t.num.natAbs = m :=
    ⟨_, x, initial, rfl⟩
  obtain ⟨y, hy, hym⟩ := Nat.find_spec hw
  have hmin (t : ℚ) (ht : bad t) : y.num.natAbs ≤ t.num.natAbs :=
    hym.trans_le (Nat.find_min' hw ⟨t,ht,rfl⟩)
  have hyp : 0 < y.num := Rat.num_pos.mpr hy.1
  have hn1 : y.num ≠ 1 := by
    intro hone
    have heq : 1 / (y.den : ℚ) = y := by simpa [hone] using Rat.num_div_den y
    have hl := least_exists hy.1
    have hle : denom y ≤ y.den := hl.2 ⟨hy.2.2.1, heq.le⟩
    have hge := one_div_le_one_div_of_le
      (show 0 < (denom y : ℚ) by exact_mod_cast hl.1.1.pos)
      (show (denom y : ℚ) ≤ y.den by exact_mod_cast hle)
    rw [heq] at hge
    have he : step y = 0 := sub_eq_zero.mpr (le_antisymm hge hl.1.2)
    have hz := (next hy).1
    rw [he] at hz
    exact (lt_irrefl _ hz)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ((step^[k]) y).num.natAbs < y.num.natAbs := by
    by_cases htwo : y.num = 2
    · simpa [htwo,step,denom] using h1 y hy.1 hy.2.1 hy.2.2.1 htwo
    · exact h2 y hy.1 hy.2.1 hy.2.2.1 (by omega)
  exact (not_lt_of_ge (hmin _ (iter hy k))) hk

-- Scan consecutive unused odds until the first unaffordable term. The
-- harmonic bound supplies finite fuel even for arbitrarily large inputs.
private lemma scan (h1 : H1) (h2 : H2) (G : ℕ → ℚ → Prop)
    (empty : ∀ b, G b 0)
    (cons : ∀ {b d : ℕ} {x : ℚ}, IsLeast {j : ℕ | Odd j ∧ b ≤ j ∧ 1/(j : ℚ) ≤ x} d →
      G (d+2) (x-1/(d : ℚ)) → G b x)
    {x : ℚ} (hx : 0 ≤ x) (ho : Odd x.den) {n : ℕ} (hn : 1 ≤ n) :
    G (2*n+1) x := by
  have mono : Monotone harmonic := monotone_nat_of_le_succ fun k => by
    rw [harmonic_succ]; apply le_add_of_nonneg_right; positivity
  obtain ⟨m, hm⟩ := harmonic_unbounded (2*x + harmonic n)
  have fuel : 2*x < harmonic (n+m) - harmonic n := by
    have := mono (show m ≤ n+m by omega)
    linarith
  clear hm
  induction m generalizing n x with
  | zero => simp at fuel; linarith
  | succ m ih =>
    let d := 2*n+1
    have hd : Odd d := ⟨n,rfl⟩
    have hd3 : 3 ≤ d := by dsimp [d]; omega
    have hdp : 0 < (d : ℚ) := by exact_mod_cast hd.pos
    by_cases hzero : x = 0
    · exact hzero ▸ empty _
    by_cases take : 1/(d : ℚ) ≤ x
    · apply cons (d := d) ⟨⟨hd,le_rfl,take⟩, fun _ hj => hj.2.1⟩
      have he : d+2 = 2*(n+1)+1 := by dsimp [d]; omega
      rw [he]
      apply ih (sub_nonneg.mpr take) (odd_sub_unit ho hd) (by omega)
      rw [show n+1+m = n+(m+1) by omega, harmonic_succ n]
      have hcost : ((↑(n+1) : ℚ))⁻¹ ≤ 2/(d : ℚ) := by
        rw [← one_div]
        apply (div_le_div_iff₀ (by positivity) hdp).2
        have : d ≤ 2*(n+1) := by dsimp [d]; omega
        exact_mod_cast (by simpa using this : 1*d ≤ 2*(n+1))
      rw [show (2 : ℚ)/d = 1/d + 1/d by ring] at hcost
      linarith
    · have hskip := lt_of_not_ge take
      apply small_termination h1 h2 G empty @cons (lt_of_le_of_ne hx (Ne.symm hzero))
        (lt_of_lt_of_le hskip (one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hd3))) ho
      intro j hj hunit
      by_contra! hlt
      have := one_div_le_one_div_of_le (show 0 < (j : ℚ) by exact_mod_cast hj.pos)
        (show (j : ℚ) ≤ d by exact_mod_cast hlt.le)
      linarith

theorem main : H1 → H2 → type_of% @OMA.S_wp_does_every_rational_number_with_an_odd_denominator_have_an_odd_greedy_expansion.main := by
  intro h1 h2 q hp ho
  let G := fun (b : ℕ) (x : ℚ) => ∃ ds : List ℕ,
    (ds.map fun j : ℕ => 1/(j : ℚ)).sum = x ∧
    ∀ (i : ℕ) (hi : i < ds.length),
      IsLeast {j : ℕ | Odd j ∧ b ≤ j ∧ j ∉ ds.take i ∧
        1/(j : ℚ) ≤ x - ((ds.take i).map fun k : ℕ => 1/(k : ℚ)).sum} ds[i]
  have empty (b : ℕ) : G b 0 := ⟨[],by simp,by simp⟩
  have cons {b d : ℕ} {x : ℚ}
      (hd : IsLeast {j : ℕ | Odd j ∧ b ≤ j ∧ 1/(j : ℚ) ≤ x} d)
      (hg : G (d+2) (x-1/(d : ℚ))) : G b x := by
    obtain ⟨ds,hs,ht⟩ := hg
    exact ⟨d :: ds, attach hd hs ht⟩
  have initial : G 0 q := by
    by_cases h : 1 ≤ q
    · apply cons (d := 1) ⟨⟨by decide,by decide,by simpa⟩, fun j hj => hj.1.pos⟩
      exact scan h1 h2 G empty @cons (n := 1) (sub_nonneg.mpr (by simpa using h))
        (odd_sub_unit ho (by decide)) (by decide)
    by_cases h3 : 1/3 ≤ q
    · refine cons (d := 3) ⟨⟨by decide,by decide,by norm_num; exact h3⟩, ?_⟩ ?_
      · rintro j ⟨hj,_,hjv⟩
        obtain ⟨k,hk⟩ := hj
        by_contra! hlt
        have hj1 : j = 1 := by omega
        rw [hj1] at hjv
        exact h (by simpa using hjv)
      · exact scan h1 h2 G empty @cons (n := 2) (sub_nonneg.mpr h3)
          (odd_sub_unit ho (by decide)) (by decide)
    · exact small_termination h1 h2 G empty @cons hp (lt_of_not_ge h3) ho
        (fun _ _ _ => Nat.zero_le _)
  obtain ⟨ds,hs,ht⟩ := initial
  have units (l : List ℕ) : (l.map fun k => 1/(k : ℚ)).sum =
      (l.map fun k : ℕ => 1/(k : ℚ)).sum := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      change 1/(a : ℚ) + _ = 1/(a : ℚ) + _
      exact congrArg (fun t : ℚ => 1/(a : ℚ) + t) ih
  refine ⟨ds, (units ds).trans hs, ?_⟩
  intro i hi
  simpa only [units, Nat.zero_le, true_and] using ht i hi

end OMA.R_wp_does_every_rational_number_with_an_odd_denominator_have_an_odd_greedy_expansion_R1

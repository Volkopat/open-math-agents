import OMAReductions.R_Erdos424_erdos_424_variants_exact_density_R1

/-!
Let A be the generated class 2 modulo 3 and Q its saturation by powers of 3.
Every positive power of 3 is generated, so 3Q - 1 is a subset of A. Write
B for the complement of 3Q - 1 in A. The disjoint decompositions
Q = A ∪ 3Q and A = B ∪ (3Q - 1) give a contraction on the eventual
oscillation of the proportions of Q, with coefficient 2/3.

H1 and H2 ask for convergence on the two parts of B determined by whether
the 3-adic valuation of n + 1 is one or at least two.
-/

open Set Erdos424
open OMA.R_Erdos424_erdos_424_variants_exact_density_R1 (generated_constraints)

namespace OMA.R_Erdos424_erdos_424_variants_exact_density_R1_H3_R1

/-- Valuation one, with the direct factorization using three unavailable. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
    let R := generatedSet ∩ {a : ℕ | a % 3 = 2 ∧ ¬ 9 ∣ a+1 ∧ (a+1)/3 ∉ generatedSet}
    |R.partialDensity univ m - R.partialDensity univ n| < ε

/-- Higher valuations, with every factorization using a pure power of three unavailable. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
    let R := generatedSet ∩ {a : ℕ | a % 3 = 2 ∧ 9 ∣ a+1 ∧
      ¬ ∃ k x : ℕ, x ∈ generatedSet ∧ x % 3 = 2 ∧ a+1 = 3^(k+1)*x}
    |R.partialDensity univ m - R.partialDensity univ n| < ε

private lemma closed_generated {a b : ℕ} (ha : a ∈ generatedSet)
    (hb : b ∈ generatedSet) (hne : a ≠ b) : a*b-1 ∈ generatedSet := by
  have mono : Monotone sequenceSet := by
    apply monotone_nat_of_le_succ
    intro n
    exact subset_union_left
  obtain ⟨i, hi⟩ := mem_iUnion.mp ha
  obtain ⟨j, hj⟩ := mem_iUnion.mp hb
  exact mem_iUnion.mpr ⟨max i j+1, Or.inr
    ⟨a, b, mono (le_max_left _ _) hi, mono (le_max_right _ _) hj, hne, rfl⟩⟩

/-- The affine orbit of 2 under x ↦ 3x-1 supplies the power-of-three factors. -/
lemma power_three_generated (k : ℕ) : 3^(k+1) ∈ generatedSet := by
  have two : 2 ∈ generatedSet := mem_iUnion.mpr ⟨0, by simp [sequenceSet]⟩
  have three : 3 ∈ generatedSet := mem_iUnion.mpr ⟨0, by simp [sequenceSet]⟩
  have oddPow (j : ℕ) : (3^j : ℕ)%2=1 := by
    induction j with
    | zero => decide
    | succ j ih => rw [pow_succ, Nat.mul_mod, ih]
  have affine (j : ℕ) : ((3^(j+1)+1)/2 : ℕ) ∈ generatedSet := by
    induction j with
    | zero => exact two
    | succ j ih =>
      have h := oddPow (j+1)
      have hm : (3^(j+1) : ℕ)%3=0 := by rw [pow_succ]; simp
      have hne : ((3^(j+1)+1)/2 : ℕ) ≠ 3 := by omega
      have he : ((3^(j+1+1)+1)/2 : ℕ) = 3*((3^(j+1)+1)/2)-1 := by
        rw [pow_succ]
        omega
      rw [he]
      exact closed_generated three ih hne.symm
  cases k with
  | zero => exact three
  | succ k =>
    have hpow : (9 : ℕ) ≤ 3^(k+1+1) := by
      change (3 : ℕ)^2 ≤ 3^(k+1+1)
      exact (Nat.pow_le_pow_iff_right (by decide : 1 < (3 : ℕ))).mpr (by omega)
    have h := oddPow (k+1+1)
    have he : (3^(k+1+1) : ℕ) = 2*((3^(k+1+1)+1)/2)-1 := by omega
    rw [he]
    exact closed_generated two (affine (k+1)) (by omega)

private lemma ncard_three (Q : Set ℕ) (n : ℕ) :
    (((fun x : ℕ => 3*x) '' Q) ∩ Iio n).ncard = (Q ∩ Iio ((n+2)/3)).ncard := by
  have eq : ((fun x : ℕ => 3*x) '' Q) ∩ Iio n =
      (fun x : ℕ => 3*x) '' (Q ∩ Iio ((n+2)/3)) := by
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hy⟩
      exact ⟨x, ⟨hx, by change x < (n+2)/3; change 3*x < n at hy; omega⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hxlt⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, by change 3*x < n; change x < (n+2)/3 at hxlt; omega⟩
  rw [eq]
  exact InjOn.ncard_image (fun x _ y _ (he : 3*x=3*y) => by omega)

private lemma ncard_three_sub (Q : Set ℕ) (pos : ∀ x ∈ Q, 0 < x) (n : ℕ) :
    (((fun x : ℕ => 3*x-1) '' Q) ∩ Iio n).ncard = (Q ∩ Iio (n/3+1)).ncard := by
  have eq : ((fun x : ℕ => 3*x-1) '' Q) ∩ Iio n =
      (fun x : ℕ => 3*x-1) '' (Q ∩ Iio (n/3+1)) := by
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hy⟩
      have hp := pos x hx
      exact ⟨x, ⟨hx, by change x < n/3+1; change 3*x-1 < n at hy; omega⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hxlt⟩, rfl⟩
      have hp := pos x hx
      exact ⟨⟨x, hx, rfl⟩, by change 3*x-1 < n; change x < n/3+1 at hxlt; omega⟩
  rw [eq]
  apply InjOn.ncard_image
  intro x hx y hy he
  have hpx := pos x hx.1
  have hpy := pos y hy.1
  change 3*x-1 = 3*y-1 at he
  omega

private lemma count_union {S T : Set ℕ} (hd : Disjoint S T) (n : ℕ) :
    ((S ∪ T) ∩ Iio n).ncard = (S ∩ Iio n).ncard + (T ∩ Iio n).ncard := by
  rw [union_inter_distrib_right]
  exact Set.ncard_union_eq
    (Set.disjoint_left.mpr (fun _ hS hT => Set.disjoint_left.mp hd hS.1 hT.1))
    ((finite_Iio n).subset inter_subset_right) ((finite_Iio n).subset inter_subset_right)

private lemma partial_density_eq (S : Set ℕ) (n : ℕ) :
    S.partialDensity univ n = ((S∩Iio n).ncard : ℝ) / (n : ℝ) := by
  simp only [Set.partialDensity, inter_univ, univ_inter, Set.ncard_Iio_nat]

private lemma count_step (Q : Set ℕ) (m s : ℕ) (hlo : m ≤ s) (hhi : s ≤ m+1) :
    (Q∩Iio m).ncard ≤ (Q∩Iio s).ncard ∧ (Q∩Iio s).ncard ≤ (Q∩Iio m).ncard+1 := by
  constructor
  · exact ncard_le_ncard (fun _ hx => ⟨hx.1, lt_of_lt_of_le hx.2 hlo⟩)
        ((finite_Iio s).subset inter_subset_right)
  · have hsubset : Q∩Iio s ⊆ insert m (Q∩Iio m) := by
      intro x hx
      by_cases h : x = m
      · exact Or.inl h
      · have hxs : x < s := hx.2
        exact Or.inr ⟨hx.1, show x < m by omega⟩
    exact (ncard_le_ncard hsubset (((finite_Iio m).subset inter_subset_right :
      (Q∩Iio m).Finite).insert m)).trans (ncard_insert_le _ _)

private lemma density_bounds (Q : Set ℕ) (n : ℕ) :
    0 ≤ Q.partialDensity univ n ∧ Q.partialDensity univ n ≤ 1 := by
  rw [partial_density_eq]
  have hle : (Q∩Iio n).ncard ≤ n := by
    simpa only [Set.ncard_Iio_nat] using ncard_le_ncard
      (show Q∩Iio n ⊆ Iio n from inter_subset_right) (finite_Iio n)
  exact ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
    div_le_one_of_le₀ (Nat.cast_le.mpr hle) (Nat.cast_nonneg _)⟩

/-- Using a cutoff anywhere between the floor and its successor contributes
one third of the scaled density, with a uniform rounding error. -/
private lemma density_round (Q : Set ℕ) (n s : ℕ) (hn : 3 ≤ n)
    (hlo : n/3 ≤ s) (hhi : s ≤ n/3+1) :
    |((Q∩Iio s).ncard : ℝ)/(n:ℝ) - (1/3 : ℝ)*Q.partialDensity univ (n/3)| ≤ 2/(n:ℝ) := by
  let m := n/3
  let z := Q.partialDensity univ m
  have hnp : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  have hmp : 0 < (m:ℝ) := Nat.cast_pos.mpr (by dsimp [m]; omega)
  have hrem : 0 ≤ (n:ℝ)-3*(m:ℝ) ∧ (n:ℝ)-3*(m:ℝ) ≤ 2 := by
    have h1 : 3*m ≤ n := by dsimp [m]; omega
    have h2 : n ≤ 3*m+2 := by dsimp [m]; omega
    constructor
    · have h : 3*(m:ℝ) ≤ n := by exact_mod_cast h1
      linarith
    · have h : (n:ℝ) ≤ 3*(m:ℝ)+2 := by exact_mod_cast h2
      linarith
  obtain ⟨hz0, hz1⟩ := density_bounds Q m
  have hp0 : 0 ≤ ((n:ℝ)-3*(m:ℝ))/3*z := by
    exact mul_nonneg (div_nonneg hrem.1 (by norm_num)) hz0
  have hp1 : ((n:ℝ)-3*(m:ℝ))/3*z ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hz1 (div_nonneg hrem.1 (by norm_num : (0:ℝ) ≤ 3))
    nlinarith
  have hcounts := count_step Q m s hlo hhi
  have hdif0 : 0 ≤ ((Q∩Iio s).ncard:ℝ) - (Q∩Iio m).ncard := by
    exact sub_nonneg.mpr (Nat.cast_le.mpr hcounts.1)
  have hdif1 : ((Q∩Iio s).ncard:ℝ) - (Q∩Iio m).ncard ≤ 1 := by
    have h : ((Q∩Iio s).ncard:ℝ) ≤ (Q∩Iio m).ncard+1 := by exact_mod_cast hcounts.2
    linarith
  change |((Q∩Iio s).ncard : ℝ)/(n:ℝ) - (1/3 : ℝ)*z| ≤ _
  have heq : ((Q∩Iio s).ncard : ℝ)/(n:ℝ) - (1/3 : ℝ)*z =
      (((Q∩Iio s).ncard:ℝ) - (Q∩Iio m).ncard -
        (((n:ℝ)-3*(m:ℝ))/3*z)) / (n:ℝ) := by
    dsimp [z]
    rw [partial_density_eq]
    field_simp [hnp.ne', hmp.ne']
    ring
  rw [heq, abs_div, abs_of_pos hnp]
  apply div_le_div_of_nonneg_right _ hnp.le
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma reciprocal_small (c δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, 3 ≤ N ∧ ∀ n ≥ N, c / (n:ℝ) ≤ δ := by
  obtain ⟨m, hm⟩ := exists_nat_gt (c/δ)
  refine ⟨max 3 m, le_max_left _ _, ?_⟩
  intro n hn
  have hp : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  have hm' : c < (m:ℝ)*δ := (div_lt_iff₀ hδ).mp hm
  have hmn : (m:ℝ) ≤ n := Nat.cast_le.mpr (by omega)
  exact (div_le_iff₀ hp).mpr (by
    calc
      c ≤ (m:ℝ)*δ := hm'.le
      _ ≤ (n:ℝ)*δ := mul_le_mul_of_nonneg_right hmn hδ.le
      _ = _ := mul_comm _ _)

private lemma abs_difference_le (x y : ℝ) : |x-y| ≤ |x|+|y| := by
  simpa only [sub_eq_add_neg, abs_neg] using abs_add_le x (-y)

/-- An approximate recurrence with coefficient two thirds contracts the
eventual diameter after dividing the indices by three. -/
private lemma contracting_cauchy (f b : ℕ → ℝ)
    (bounds : ∀ n, 0 ≤ f n ∧ f n ≤ 1)
    (hb : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, |b m-b n| < ε)
    (recurrence : ∀ n : ℕ, 3 ≤ n → |f n-(b n+(2/3:ℝ)*f (n/3))| ≤ 4/(n:ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, |f m-f n| < ε := by
  let good : Set ℝ := {r | 0 ≤ r ∧ ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, |f m-f n| ≤ r}
  have hne : good.Nonempty := by
    refine ⟨1, by norm_num, 0, ?_⟩
    intro m _ n _
    obtain ⟨hm0, hm1⟩ := bounds m
    obtain ⟨hn0, hn1⟩ := bounds n
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hbb : BddBelow good := ⟨0, fun _ hr => hr.1⟩
  have shrink (r : ℝ) (hr : r ∈ good) (δ : ℝ) (hδ : 0 < δ) :
      (2/3:ℝ)*r+δ ∈ good := by
    obtain ⟨hr0, L, hL⟩ := hr
    obtain ⟨J, hJ⟩ := hb (δ/3) (by positivity)
    obtain ⟨K, hK3, hK⟩ := reciprocal_small 4 (δ/3) (by positivity)
    refine ⟨by positivity, max (3*L) (max J K), ?_⟩
    intro m hm n hn
    have hmK : K ≤ m := by omega
    have hnK : K ≤ n := by omega
    have hB := (hJ m (by omega) n (by omega)).le
    have hF := hL (m/3) (by omega) (n/3) (by omega)
    let e (i : ℕ) := f i - (b i+(2/3:ℝ)*f (i/3))
    have hmE : |e m| ≤ δ/3 := (recurrence m (by omega)).trans (hK m hmK)
    have hnE : |e n| ≤ δ/3 := (recurrence n (by omega)).trans (hK n hnK)
    have hE : |e m-e n| ≤ δ/3+δ/3 :=
      (abs_difference_le _ _).trans (add_le_add hmE hnE)
    have hmul : |(2/3:ℝ)*(f (m/3)-f (n/3))| ≤ (2/3:ℝ)*r := by
      rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2/3:ℝ))]
      exact mul_le_mul_of_nonneg_left hF (by norm_num)
    have heq : f m-f n = ((b m-b n)+(2/3:ℝ)*(f (m/3)-f (n/3)))+(e m-e n) := by
      dsimp [e]
      ring
    rw [heq]
    have hcore := abs_add_le (b m-b n) ((2/3:ℝ)*(f (m/3)-f (n/3)))
    have htotal := abs_add_le ((b m-b n)+(2/3:ℝ)*(f (m/3)-f (n/3))) (e m-e n)
    linarith
  have h0 : 0 ≤ sInf good := le_csInf hne (fun _ hr => hr.1)
  have hzero : sInf good = 0 := by
    by_contra hneq
    have hp : 0 < sInf good := lt_of_le_of_ne h0 (Ne.symm hneq)
    obtain ⟨r, hr, hlt⟩ := exists_lt_of_csInf_lt hne
      (show sInf good < sInf good+sInf good/10 by linarith)
    have hlower := csInf_le hbb (shrink r hr (sInf good/10) (by positivity))
    linarith
  intro ε hε
  obtain ⟨r, hr, hlt⟩ := exists_lt_of_csInf_lt hne (by simpa [hzero] using hε)
  obtain ⟨_, N, hN⟩ := hr
  exact ⟨N, fun m hm n hn => (hN m hm n hn).trans_lt hlt⟩

private lemma cauchy_sub_scaled (f a : ℕ → ℝ)
    (hf : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, |f m-f n| < ε)
    (estimate : ∀ n : ℕ, 3 ≤ n → |a n-(f n-(1/3:ℝ)*f (n/3))| ≤ 2/(n:ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, |a m-a n| < ε := by
  intro ε hε
  obtain ⟨L, hL⟩ := hf (ε/4) (by positivity)
  obtain ⟨K, hK3, hK⟩ := reciprocal_small 2 (ε/4) (by positivity)
  refine ⟨max (3*L) K, ?_⟩
  intro m hm n hn
  have hF := (hL m (by omega) n (by omega)).le
  have hsmall := (hL (m/3) (by omega) (n/3) (by omega)).le
  let e (j : ℕ) := a j-(f j-(1/3:ℝ)*f (j/3))
  have hmE : |e m| ≤ ε/4 := (estimate m (by omega)).trans (hK m (by omega))
  have hnE : |e n| ≤ ε/4 := (estimate n (by omega)).trans (hK n (by omega))
  have hE : |e m-e n| ≤ ε/4+ε/4 :=
    (abs_difference_le _ _).trans (add_le_add hmE hnE)
  have hmul : |(1/3:ℝ)*(f (m/3)-f (n/3))| ≤ (1/3:ℝ)*(ε/4) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (1/3:ℝ))]
    exact mul_le_mul_of_nonneg_left hsmall (by norm_num)
  have heq : a m-a n = ((f m-f n)-(1/3:ℝ)*(f (m/3)-f (n/3)))+(e m-e n) := by
    dsimp [e]
    ring
  rw [heq]
  have hcore := abs_difference_le (f m-f n) ((1/3:ℝ)*(f (m/3)-f (n/3)))
  have htotal := abs_add_le ((f m-f n)-(1/3:ℝ)*(f (m/3)-f (n/3))) (e m-e n)
  linarith

theorem main : H1 → H2 → OMA.R_Erdos424_erdos_424_variants_exact_density_R1.H3 := by
  intro h1 h2
  let A : Set ℕ := generatedSet ∩ {x | x%3=2}
  let Q : Set ℕ := {q | ∃ k x : ℕ, x ∈ A ∧ q = 3^k*x}
  let U := (fun x : ℕ => 3*x-1) '' Q
  let B := A \ U
  let R1 := generatedSet ∩ {a : ℕ | a%3=2 ∧ ¬ 9 ∣ a+1 ∧ (a+1)/3 ∉ generatedSet}
  let R2 := generatedSet ∩ {a : ℕ | a%3=2 ∧ 9 ∣ a+1 ∧
    ¬ ∃ k x : ℕ, x ∈ generatedSet ∧ x%3=2 ∧ a+1 = 3^(k+1)*x}
  have Qpos : ∀ q ∈ Q, 0 < q := by
    rintro q ⟨k, x, hx, rfl⟩
    exact Nat.mul_pos (Nat.pow_pos (by decide)) (by
      have := (generated_constraints hx.1).1
      omega)
  have hU (z : ℕ) : z ∈ U ↔ ∃ k x : ℕ, x ∈ A ∧ z+1 = 3^(k+1)*x := by
    constructor
    · rintro ⟨q, hq, rfl⟩
      have hp := Qpos q hq
      obtain ⟨k, x, hx, rfl⟩ := hq
      refine ⟨k, x, hx, ?_⟩
      change 3*(3^k*x)-1+1 = 3^(k+1)*x
      rw [pow_succ, show 3^k*3*x = 3*(3^k*x) by ac_rfl]
      omega
    · rintro ⟨k, x, hx, hz⟩
      have hq : 3^k*x ∈ Q := ⟨k, x, hx, rfl⟩
      refine ⟨3^k*x, hq, ?_⟩
      change 3*(3^k*x)-1 = z
      rw [pow_succ, show 3^k*3*x = 3*(3^k*x) by ac_rfl] at hz
      omega
  have Usub : U ⊆ A := by
    intro z hz
    obtain ⟨k, x, hx, heq⟩ := (hU z).mp hz
    have hp : (3^(k+1) : ℕ)%3=0 := by rw [pow_succ]; simp
    have hxmod : x%3=2 := hx.2
    have hne : (3^(k+1) : ℕ) ≠ x := by
      intro he
      rw [he] at hp
      omega
    have hg := closed_generated (power_three_generated k) hx.1 hne
    have hz' : z = 3^(k+1)*x-1 := by omega
    have hprod : (z+1)%3=0 := by rw [heq, Nat.mul_mod, hp]; simp
    exact ⟨hz' ▸ hg, by change z%3=2; omega⟩
  have hUpper : Q = A ∪ ((fun x : ℕ => 3*x) '' Q) := by
    ext q
    constructor
    · rintro ⟨k, x, hx, rfl⟩
      cases k with
      | zero => exact Or.inl (by simpa using hx)
      | succ k =>
        refine Or.inr ⟨3^k*x, ⟨k, x, hx, rfl⟩, ?_⟩
        change 3*(3^k*x) = 3^(k+1)*x
        rw [pow_succ]
        ac_rfl
    · rintro (ha | ⟨y, ⟨k, x, hx, rfl⟩, rfl⟩)
      · exact ⟨0, q, ha, by simp⟩
      · refine ⟨k+1, x, hx, ?_⟩
        change 3*(3^k*x) = 3^(k+1)*x
        rw [pow_succ]
        ac_rfl
  have hUpperDis : Disjoint A ((fun x : ℕ => 3*x) '' Q) := by
    apply Set.disjoint_left.mpr
    rintro _ ha ⟨q, _, rfl⟩
    have h : (3*q)%3=2 := ha.2
    omega
  have hLower : A = B ∪ U := by
    ext z
    constructor
    · intro hz
      by_cases h : z ∈ U
      · exact Or.inr h
      · exact Or.inl ⟨hz, h⟩
    · rintro (h | h)
      · exact h.1
      · exact Usub h
  have hLowerDis : Disjoint B U := Set.disjoint_left.mpr (fun _ h hb => h.2 hb)
  have hExactOne (z : ℕ) (hz : z ∈ A) (h9 : ¬ 9 ∣ z+1) :
      z ∈ U ↔ (z+1)/3 ∈ generatedSet := by
    constructor
    · intro h
      obtain ⟨k, x, hx, heq⟩ := (hU z).mp h
      cases k with
      | zero =>
        have hEq' : z+1=3*x := by simpa using heq
        have hxEq : (z+1)/3 = x := by omega
        rw [hxEq]
        exact hx.1
      | succ k =>
        apply (h9 ?_).elim
        refine ⟨3^k*x, ?_⟩
        rw [heq, pow_succ (3:ℕ) (k+1), pow_succ]
        change (3^k*3*3)*x = (3*3)*(3^k*x)
        ac_rfl
    · intro h
      have hm : z%3=2 := hz.2
      have hqEq : z+1=3*((z+1)/3) := by omega
      have hqNoZero : ((z+1)/3)%3 ≠ 0 := by
        intro hd
        apply h9
        exact ⟨((z+1)/3)/3, by omega⟩
      have hqNoOne := (generated_constraints h).2
      exact (hU z).mpr ⟨0, (z+1)/3, ⟨h, show ((z+1)/3)%3=2 by omega⟩, by
        simpa using hqEq⟩
  have hB : B = R1 ∪ R2 := by
    ext z
    constructor
    · rintro ⟨hz, hu⟩
      by_cases h9 : 9 ∣ z+1
      · exact Or.inr ⟨hz.1, hz.2, h9, fun ⟨k, x, hx, hm, he⟩ =>
          hu ((hU z).mpr ⟨k, x, ⟨hx, hm⟩, he⟩)⟩
      · exact Or.inl ⟨hz.1, hz.2, h9, fun h => hu ((hExactOne z hz h9).mpr h)⟩
    · rintro (h | h)
      · have hz : z ∈ A := ⟨h.1, h.2.1⟩
        exact ⟨hz, fun hu => h.2.2.2 ((hExactOne z hz h.2.2.1).mp hu)⟩
      · refine ⟨⟨h.1, h.2.1⟩, ?_⟩
        intro hu
        obtain ⟨k, x, hx, he⟩ := (hU z).mp hu
        exact h.2.2.2 ⟨k, x, hx.1, hx.2, he⟩
  have hBDis : Disjoint R1 R2 := Set.disjoint_left.mpr (fun _ h h' => h.2.2.1 h'.2.2.1)
  let f := Q.partialDensity univ
  let b := B.partialDensity univ
  let g := A.partialDensity univ
  have hSplit (n : ℕ) : b n = R1.partialDensity univ n + R2.partialDensity univ n := by
    dsimp only [b]
    rw [partial_density_eq, partial_density_eq, partial_density_eq, hB, count_union hBDis,
      Nat.cast_add, add_div]
  have hBC : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, |b m-b n| < ε := by
    intro ε hε
    obtain ⟨N1, hN1⟩ := h1 (ε/2) (by positivity)
    obtain ⟨N2, hN2⟩ := h2 (ε/2) (by positivity)
    refine ⟨max N1 N2, ?_⟩
    intro m hm n hn
    have hh1 : |R1.partialDensity univ m - R1.partialDensity univ n| < ε/2 :=
      hN1 m (by omega) n (by omega)
    have hh2 : |R2.partialDensity univ m - R2.partialDensity univ n| < ε/2 :=
      hN2 m (by omega) n (by omega)
    rw [hSplit, hSplit]
    rw [show R1.partialDensity univ m + R2.partialDensity univ m -
      (R1.partialDensity univ n + R2.partialDensity univ n) =
      (R1.partialDensity univ m-R1.partialDensity univ n)+
      (R2.partialDensity univ m-R2.partialDensity univ n) by ring]
    exact (abs_add_le _ _).trans_lt (by linarith)
  have qCount (n : ℕ) :
      (Q ∩ Iio n).ncard = (A ∩ Iio n).ncard + (Q ∩ Iio ((n+2)/3)).ncard := by
    calc
      _ = ((A ∪ ((fun x : ℕ => 3*x) '' Q))∩ Iio n).ncard :=
        congrArg (fun S => (S∩Iio n).ncard) hUpper
      _ = _ := by rw [count_union hUpperDis n, ncard_three]
  have aCount (n : ℕ) :
      (A ∩ Iio n).ncard = (B ∩ Iio n).ncard + (Q ∩ Iio (n/3+1)).ncard := by
    calc
      _ = ((B ∪ U) ∩ Iio n).ncard := congrArg (fun S => (S∩Iio n).ncard) hLower
      _ = _ := by rw [count_union hLowerDis n]; exact
            congrArg ((B∩Iio n).ncard + ·) (ncard_three_sub Q Qpos n)
  let c0 (n : ℕ) : ℝ := ((Q∩Iio ((n+2)/3)).ncard:ℝ)/(n:ℝ)
  let c1 (n : ℕ) : ℝ := ((Q∩Iio (n/3+1)).ncard:ℝ)/(n:ℝ)
  have fEq (n : ℕ) : f n = g n+c0 n := by
    dsimp only [f, g, c0]
    rw [partial_density_eq, partial_density_eq, qCount, Nat.cast_add, add_div]
  have gEq (n : ℕ) : g n = b n+c1 n := by
    dsimp only [g, b, c1]
    rw [partial_density_eq, partial_density_eq, aCount, Nat.cast_add, add_div]
  have e0 (n : ℕ) (hn : 3 ≤ n) : |c0 n-(1/3:ℝ)*f (n/3)| ≤ 2/(n:ℝ) :=
    density_round Q n ((n+2)/3) hn (by omega) (by omega)
  have e1 (n : ℕ) (hn : 3 ≤ n) : |c1 n-(1/3:ℝ)*f (n/3)| ≤ 2/(n:ℝ) :=
    density_round Q n (n/3+1) hn (by omega) (by omega)
  have hf := contracting_cauchy f b (density_bounds Q) hBC (by
    intro n hn
    have he : f n-(b n+(2/3:ℝ)*f (n/3)) =
        (c0 n-(1/3:ℝ)*f (n/3))+(c1 n-(1/3:ℝ)*f (n/3)) := by
      linarith [fEq n, gEq n]
    rw [he]
    calc
      _ ≤ |c0 n-(1/3:ℝ)*f (n/3)|+|c1 n-(1/3:ℝ)*f (n/3)| := abs_add_le _ _
      _ ≤ 2/(n:ℝ)+2/(n:ℝ) := add_le_add (e0 n hn) (e1 n hn)
      _ = _ := by ring)
  exact cauchy_sub_scaled f g hf (by
    intro n hn
    rw [show g n-(f n-(1/3:ℝ)*f (n/3))= -(c0 n-(1/3:ℝ)*f (n/3)) by
      linarith [fEq n], abs_neg]
    exact e0 n hn)

end OMA.R_Erdos424_erdos_424_variants_exact_density_R1_H3_R1

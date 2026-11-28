import OMAReductions.R_Kourovka_8_8_kourovka_8_8a_R1

/-!
# Primitive roots in torsion-free Gromov-hyperbolic 2-generated quotients

Proves `Kourovka.8.8.kourovka_8_8a.R1.H1`: in any torsion-free `δ`-hyperbolic quotient
`Q = FreeGroup (Fin 2) ⧸ N`, every nontrivial element `g ≠ 1` is an integer power `c ^ r` of a
primitive element `c`.

The proof is completely elementary in the word metric `d`:
1. Establish metric properties, left-invariance, geodesic midpoints, and finiteness of balls.
2. Uniform positive minimal displacement for `h ^ K` (`K = |B(1, 16δ + 4)| + 1`) via the
   4-point quasi-center diameter bound on the finite orbit `{x, h x, ..., h^(K-1) x}`.
3. Linear growth `2 * k ≤ d 1 (u ^ k)` for any element `u` of minimal conjugacy displacement
   `L > 6 * δ + 1`.
4. Bound every positive root exponent `n` (`h ^ n = g`) by `K * d 1 g`, and extract a maximal
   positive root `c`, which is necessarily primitive.
-/

namespace OMA.Kourovka88H1

open scoped Classical

section Metric

variable {N : Subgroup (FreeGroup (Fin 2))} [N.Normal]

/-- The word metric on `FreeGroup (Fin 2) ⧸ N` from the reduction statement. -/
noncomputable def wdist (u v : FreeGroup (Fin 2) ⧸ N) : ℕ :=
  sInf {k : ℕ | ∃ s : FreeGroup (Fin 2), s.toWord.length = k ∧ QuotientGroup.mk s = u⁻¹ * v}

private lemma wdist_set_nonempty (u v : FreeGroup (Fin 2) ⧸ N) :
    {k : ℕ | ∃ s : FreeGroup (Fin 2), s.toWord.length = k ∧ QuotientGroup.mk s = u⁻¹ * v}.Nonempty := by
  obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (u⁻¹ * v)
  exact ⟨s.toWord.length, s, rfl, hs⟩

private lemma exists_word_wdist (u v : FreeGroup (Fin 2) ⧸ N) :
    ∃ s : FreeGroup (Fin 2), s.toWord.length = wdist u v ∧ QuotientGroup.mk s = u⁻¹ * v :=
  Nat.sInf_mem (wdist_set_nonempty u v)

private lemma wdist_le_length {u v : FreeGroup (Fin 2) ⧸ N} {s : FreeGroup (Fin 2)}
    (hs : QuotientGroup.mk s = u⁻¹ * v) :
    wdist u v ≤ s.toWord.length :=
  Nat.sInf_le ⟨s, rfl, hs⟩

private lemma wdist_self (u : FreeGroup (Fin 2) ⧸ N) : wdist u u = 0 := by
  apply Nat.eq_zero_of_le_zero
  have h : QuotientGroup.mk (1 : FreeGroup (Fin 2)) = u⁻¹ * u := by simp
  simpa using wdist_le_length h

private lemma wdist_eq_zero_iff (u v : FreeGroup (Fin 2) ⧸ N) :
    wdist u v = 0 ↔ u = v := by
  constructor
  · intro h
    obtain ⟨s, hlen, hmk⟩ := exists_word_wdist u v
    rw [h] at hlen
    have hs1 : s = 1 := by
      have hw : s.toWord = [] := List.eq_nil_of_length_eq_zero hlen
      rw [← FreeGroup.mk_toWord (x := s), hw]
      rfl
    rw [hs1, QuotientGroup.mk_one] at hmk
    exact (inv_mul_eq_one.mp hmk.symm)
  · rintro rfl
    exact wdist_self u

private lemma toWord_inv_length (s : FreeGroup (Fin 2)) :
    s⁻¹.toWord.length = s.toWord.length := by
  rw [FreeGroup.toWord_inv]
  simp [FreeGroup.invRev]

private lemma toWord_mul_length_le (s t : FreeGroup (Fin 2)) :
    (s * t).toWord.length ≤ s.toWord.length + t.toWord.length := by
  rw [FreeGroup.toWord_mul]
  calc
    (FreeGroup.reduce (s.toWord ++ t.toWord)).length
        ≤ (s.toWord ++ t.toWord).length := FreeGroup.Red.length_le FreeGroup.reduce.red
    _ = s.toWord.length + t.toWord.length := List.length_append

private lemma wdist_symm (u v : FreeGroup (Fin 2) ⧸ N) : wdist u v = wdist v u := by
  have hle : ∀ a b : FreeGroup (Fin 2) ⧸ N, wdist a b ≤ wdist b a := by
    intro a b
    obtain ⟨s, hlen, hmk⟩ := exists_word_wdist b a
    have hinv : QuotientGroup.mk s⁻¹ = a⁻¹ * b := by
      rw [QuotientGroup.mk_inv, hmk, mul_inv_rev, inv_inv]
    calc
      wdist a b ≤ s⁻¹.toWord.length := wdist_le_length hinv
      _ = s.toWord.length := toWord_inv_length s
      _ = wdist b a := hlen
  exact le_antisymm (hle u v) (hle v u)

private lemma wdist_triangle (u v w : FreeGroup (Fin 2) ⧸ N) :
    wdist u w ≤ wdist u v + wdist v w := by
  obtain ⟨s₁, hlen₁, hmk₁⟩ := exists_word_wdist u v
  obtain ⟨s₂, hlen₂, hmk₂⟩ := exists_word_wdist v w
  have hmul : QuotientGroup.mk (s₁ * s₂) = u⁻¹ * w := by
    rw [QuotientGroup.mk_mul, hmk₁, hmk₂]
    group
  calc
    wdist u w ≤ (s₁ * s₂).toWord.length := wdist_le_length hmul
    _ ≤ s₁.toWord.length + s₂.toWord.length := toWord_mul_length_le s₁ s₂
    _ = wdist u v + wdist v w := by rw [hlen₁, hlen₂]

private lemma wdist_mul_left (x u v : FreeGroup (Fin 2) ⧸ N) :
    wdist (x * u) (x * v) = wdist u v := by
  unfold wdist
  congr 1
  ext k
  simp [mul_assoc]

private lemma wdist_one_inv (u : FreeGroup (Fin 2) ⧸ N) :
    wdist (1 : FreeGroup (Fin 2) ⧸ N) u⁻¹ = wdist 1 u := by
  rw [← wdist_mul_left u, mul_one, mul_inv_cancel, wdist_symm]

private lemma wdist_pow_le (u : FreeGroup (Fin 2) ⧸ N) (k : ℕ) :
    wdist (1 : FreeGroup (Fin 2) ⧸ N) (u ^ k) ≤ k * wdist 1 u := by
  induction k with
  | zero => simp [wdist_self]
  | succ k ih =>
    calc
      wdist 1 (u ^ (k + 1)) = wdist 1 (u * u ^ k) := by rw [pow_succ']
      _ ≤ wdist 1 u + wdist u (u * u ^ k) := wdist_triangle 1 u (u * u ^ k)
      _ = wdist 1 u + wdist 1 (u ^ k) := by
        have h : wdist u (u * u ^ k) = wdist 1 (u ^ k) := by
          simpa using wdist_mul_left u 1 (u ^ k)
        rw [h]
      _ ≤ wdist 1 u + k * wdist 1 u := Nat.add_le_add_left ih _
      _ = (k + 1) * wdist 1 u := by ring

private lemma wdist_conj_le (x u : FreeGroup (Fin 2) ⧸ N) :
    wdist (1 : FreeGroup (Fin 2) ⧸ N) (x⁻¹ * u * x) ≤ 2 * wdist 1 x + wdist 1 u := by
  calc
    wdist 1 (x⁻¹ * u * x) = wdist x (u * x) := by
      rw [← wdist_mul_left x, mul_one]; simp [mul_assoc]
    _ ≤ wdist x 1 + wdist 1 (u * x) := wdist_triangle x 1 (u * x)
    _ ≤ wdist x 1 + (wdist 1 u + wdist u (u * x)) :=
      Nat.add_le_add_left (wdist_triangle 1 u (u * x)) _
    _ = 2 * wdist 1 x + wdist 1 u := by
      have h1 : wdist x 1 = wdist 1 x := wdist_symm x 1
      have h2 : wdist u (u * x) = wdist 1 x := by simpa using wdist_mul_left u 1 x
      omega

/-- Existence of a geodesic midpoint between any two points in `FreeGroup (Fin 2) ⧸ N`. -/
private lemma exists_midpoint (u v : FreeGroup (Fin 2) ⧸ N) :
    ∃ m : FreeGroup (Fin 2) ⧸ N,
      wdist u m = wdist u v / 2 ∧ wdist m v = wdist u v - wdist u v / 2 := by
  obtain ⟨s, hlen, hmk⟩ := exists_word_wdist u v
  set d := wdist u v
  set l₁ : List (Fin 2 × Bool) := s.toWord.take (d / 2)
  set l₂ : List (Fin 2 × Bool) := s.toWord.drop (d / 2)
  have happ : l₁ ++ l₂ = s.toWord := List.take_append_drop (d / 2) s.toWord
  have hmul : FreeGroup.mk l₁ * FreeGroup.mk l₂ = s := by
    rw [FreeGroup.mul_mk, happ, FreeGroup.mk_toWord]
  let m : FreeGroup (Fin 2) ⧸ N := u * QuotientGroup.mk (FreeGroup.mk l₁)
  have hm1 : wdist u m ≤ d / 2 := by
    have hq : QuotientGroup.mk (FreeGroup.mk l₁) = u⁻¹ * m := by simp [m]
    calc
      wdist u m ≤ (FreeGroup.mk l₁).toWord.length := wdist_le_length hq
      _ ≤ l₁.length := FreeGroup.Red.length_le FreeGroup.reduce.red
      _ = d / 2 := by simp [l₁, hlen, Nat.min_eq_left (Nat.div_le_self d 2)]
  have hm2 : wdist m v ≤ d - d / 2 := by
    have hq : QuotientGroup.mk (FreeGroup.mk l₂) = m⁻¹ * v := by
      have hmk' : QuotientGroup.mk (FreeGroup.mk l₁) * QuotientGroup.mk (FreeGroup.mk l₂) = u⁻¹ * v := by
        rw [← QuotientGroup.mk_mul, hmul, hmk]
      calc
        QuotientGroup.mk (FreeGroup.mk l₂)
            = (QuotientGroup.mk (FreeGroup.mk l₁))⁻¹ * (u⁻¹ * v) := by
              rw [← hmk']; group
        _ = m⁻¹ * v := by simp [m, mul_assoc]
    calc
      wdist m v ≤ (FreeGroup.mk l₂).toWord.length := wdist_le_length hq
      _ ≤ l₂.length := FreeGroup.Red.length_le FreeGroup.reduce.red
      _ = d - d / 2 := by simp [l₂, hlen]
  have htri : d ≤ wdist u m + wdist m v := wdist_triangle u m v
  refine ⟨m, ?_, ?_⟩ <;> omega

/-- The ball of radius `R` around `1` in `FreeGroup (Fin 2) ⧸ N` is finite. -/
private lemma finite_ball (R : ℕ) :
    Set.Finite {x : FreeGroup (Fin 2) ⧸ N | wdist (1 : FreeGroup (Fin 2) ⧸ N) x ≤ R} := by
  let f : (Σ k : Fin (R + 1), List.Vector (Fin 2 × Bool) k.1) → FreeGroup (Fin 2) ⧸ N :=
    fun p => QuotientGroup.mk (FreeGroup.mk p.2.toList)
  refine (Set.finite_range f).subset ?_
  intro x hx
  obtain ⟨s, hlen, hmk⟩ := exists_word_wdist (1 : FreeGroup (Fin 2) ⧸ N) x
  have hle : s.toWord.length ≤ R := hlen.le.trans hx
  refine ⟨⟨⟨s.toWord.length, Nat.lt_succ_of_le hle⟩, ⟨s.toWord, rfl⟩⟩, ?_⟩
  change QuotientGroup.mk (FreeGroup.mk s.toWord) = x
  rw [FreeGroup.mk_toWord, hmk]; simp

/-- Uniform positive minimal displacement for `h ^ K` in a torsion-free `δ`-hyperbolic quotient. -/
private lemma uniform_min_disp
    (δ : ℕ)
    (hhyp : ∀ x y z w : FreeGroup (Fin 2) ⧸ N,
      wdist x y + wdist z w ≤ max (wdist x z + wdist y w) (wdist x w + wdist y z) + 2 * δ)
    (htf : ∀ g : FreeGroup (Fin 2) ⧸ N, ∀ n : ℕ, n ≠ 0 → g ^ n = 1 → g = 1) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ h : FreeGroup (Fin 2) ⧸ N, h ≠ 1 →
      ∀ x : FreeGroup (Fin 2) ⧸ N, 6 * δ + 1 < wdist x (h ^ K * x) := by
  set R : ℕ := 6 * δ + 1
  let ballFin : Finset (FreeGroup (Fin 2) ⧸ N) :=
    (finite_ball (N := N) (2 * R + 4 * δ + 2)).toFinset
  set K : ℕ := ballFin.card + 1
  refine ⟨K, Nat.succ_pos _, ?_⟩
  intro h hh x
  by_contra hle
  push Not at hle
  -- Choose y₀ minimizing max_{i : Fin K} wdist y (h ^ i.1 * x)
  let rad (y : FreeGroup (Fin 2) ⧸ N) : ℕ :=
    Finset.univ.sup (fun i : Fin K => wdist y (h ^ i.1 * x))
  have hne : ∃ r : ℕ, ∃ y : FreeGroup (Fin 2) ⧸ N, rad y = r := ⟨rad 1, 1, rfl⟩
  set r₀ : ℕ := Nat.find hne
  obtain ⟨y₀, hy₀⟩ := Nat.find_spec hne
  change rad y₀ = r₀ at hy₀
  have hr₀_min : ∀ y : FreeGroup (Fin 2) ⧸ N, r₀ ≤ rad y := fun y => Nat.find_min' hne ⟨y, rfl⟩
  have hy₀_le : ∀ i : Fin K, wdist y₀ (h ^ i.1 * x) ≤ r₀ := by
    intro i
    rw [← hy₀]
    exact Finset.le_sup (f := fun i : Fin K => wdist y₀ (h ^ i.1 * x)) (Finset.mem_univ i)
  -- For every j ≤ K and every i < K, wdist (h ^ j * y₀) (h ^ i * x) ≤ r₀ + R
  have hshift_le : ∀ j : ℕ, j ≤ K → ∀ i : Fin K, wdist (h ^ j * y₀) (h ^ i.1 * x) ≤ r₀ + R := by
    intro j hj i
    by_cases hji : j ≤ i.1
    · have hij : i.1 - j < K := by omega
      have hpow : h ^ i.1 = h ^ j * h ^ (i.1 - j) := by
        rw [← pow_add, Nat.add_sub_of_le hji]
      calc
        wdist (h ^ j * y₀) (h ^ i.1 * x)
            = wdist (h ^ j * y₀) (h ^ j * (h ^ (i.1 - j) * x)) := by rw [hpow, mul_assoc]
        _ = wdist y₀ (h ^ (i.1 - j) * x) := wdist_mul_left _ _ _
        _ ≤ r₀ := hy₀_le ⟨i.1 - j, hij⟩
        _ ≤ r₀ + R := Nat.le_add_right r₀ R
    · have hikj : i.1 + K - j < K := by omega
      have hpow1 : h ^ (i.1 + K) = h ^ j * h ^ (i.1 + K - j) := by
        rw [← pow_add, Nat.add_sub_of_le (by omega)]
      have hpow2 : h ^ (i.1 + K) = h ^ i.1 * h ^ K := pow_add h i.1 K
      calc
        wdist (h ^ j * y₀) (h ^ i.1 * x)
            ≤ wdist (h ^ j * y₀) (h ^ (i.1 + K) * x) + wdist (h ^ (i.1 + K) * x) (h ^ i.1 * x) :=
              wdist_triangle _ _ _
        _ = wdist y₀ (h ^ (i.1 + K - j) * x) + wdist (h ^ K * x) x := by
              have h1 : wdist (h ^ j * y₀) (h ^ (i.1 + K) * x) = wdist y₀ (h ^ (i.1 + K - j) * x) := by
                rw [hpow1, mul_assoc, wdist_mul_left]
              have h2 : wdist (h ^ (i.1 + K) * x) (h ^ i.1 * x) = wdist (h ^ K * x) x := by
                rw [hpow2, mul_assoc, wdist_mul_left]
              rw [h1, h2]
        _ ≤ r₀ + R := by
              rw [wdist_symm (h ^ K * x) x]
              exact Nat.add_le_add (hy₀_le ⟨i.1 + K - j, hikj⟩) hle
  -- Every j ≤ K has wdist y₀ (h ^ j * y₀) ≤ 2 * R + 4 * δ + 2
  have hdisp : ∀ j : ℕ, j ≤ K → wdist (1 : FreeGroup (Fin 2) ⧸ N) (y₀⁻¹ * h ^ j * y₀) ≤ 2 * R + 4 * δ + 2 := by
    intro j hj
    have heq : wdist (1 : FreeGroup (Fin 2) ⧸ N) (y₀⁻¹ * h ^ j * y₀) = wdist y₀ (h ^ j * y₀) := by
      rw [← wdist_mul_left y₀, mul_one]
      simp [mul_assoc]
    rw [heq]
    set D := wdist y₀ (h ^ j * y₀)
    obtain ⟨m, hm1, hm2⟩ := exists_midpoint y₀ (h ^ j * y₀)
    have hrm : r₀ ≤ rad m := hr₀_min m
    have hex : ∃ i : Fin K, r₀ ≤ wdist m (h ^ i.1 * x) := by
      by_contra hlt
      push Not at hlt
      have hsup : rad m < r₀ := by
        have hpos : 0 < r₀ := by
          by_contra hz
          have hr0 : r₀ = 0 := by omega
          have := hlt ⟨0, Nat.succ_pos _⟩
          omega
        exact (Finset.sup_lt_iff hpos).mpr (fun i _ => hlt i)
      omega
    obtain ⟨i, hi⟩ := hex
    have h4 := hhyp y₀ (h ^ j * y₀) m (h ^ i.1 * x)
    have h1 := hy₀_le i
    have h2 := hshift_le j hj i
    have hmax : max (wdist y₀ m + wdist (h ^ j * y₀) (h ^ i.1 * x))
        (wdist y₀ (h ^ i.1 * x) + wdist (h ^ j * y₀) m) ≤ D / 2 + 1 + r₀ + R := by
      rw [wdist_symm (h ^ j * y₀) m]
      exact max_le (by omega) (by omega)
    omega
  -- Pigeonhole on Fin (K + 1) -> ballFin
  let f : Fin (K + 1) → FreeGroup (Fin 2) ⧸ N := fun j => y₀⁻¹ * h ^ j.1 * y₀
  have hmaps : ∀ j ∈ (Finset.univ : Finset (Fin (K + 1))), f j ∈ ballFin := by
    intro j _
    rw [Set.Finite.mem_toFinset]
    exact hdisp j.1 (Nat.le_of_lt_succ j.2)
  have hcard : ballFin.card < (Finset.univ : Finset (Fin (K + 1))).card := by
    simp [K]
  obtain ⟨j₁, _, j₂, _, hjne, hfeq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  have hpow_eq : h ^ j₁.1 = h ^ j₂.1 := by
    have h1 : y₀ * (f j₁) * y₀⁻¹ = y₀ * (f j₂) * y₀⁻¹ := by rw [hfeq]
    simpa [f, mul_assoc] using h1
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hjne) with hlt | hgt
  · have h1 : h ^ (j₂.1 - j₁.1) = 1 := by
      have hm : h ^ j₁.1 * h ^ (j₂.1 - j₁.1) = h ^ j₁.1 * 1 := by
        rw [← pow_add, Nat.add_sub_of_le hlt.le, mul_one, hpow_eq]
      exact mul_left_cancel hm
    exact hh (htf h (j₂.1 - j₁.1) (by omega) h1)
  · have h1 : h ^ (j₁.1 - j₂.1) = 1 := by
      have hm : h ^ j₂.1 * h ^ (j₁.1 - j₂.1) = h ^ j₂.1 * 1 := by
        rw [← pow_add, Nat.add_sub_of_le hgt.le, mul_one, ← hpow_eq]
      exact mul_left_cancel hm
    exact hh (htf h (j₁.1 - j₂.1) (by omega) h1)

/-- Linear growth of powers for an element of minimal conjugacy displacement `> 6δ + 1`. -/
private lemma linear_growth_of_min_disp
    (δ : ℕ)
    (hhyp : ∀ x y z w : FreeGroup (Fin 2) ⧸ N,
      wdist x y + wdist z w ≤ max (wdist x z + wdist y w) (wdist x w + wdist y z) + 2 * δ)
    {u : FreeGroup (Fin 2) ⧸ N}
    (hmin : ∀ x : FreeGroup (Fin 2) ⧸ N, wdist 1 u ≤ wdist x (u * x))
    (hlarge : 6 * δ + 1 < wdist 1 u) :
    ∀ k : ℕ, 2 * k ≤ wdist (1 : FreeGroup (Fin 2) ⧸ N) (u ^ k) := by
  set L := wdist (1 : FreeGroup (Fin 2) ⧸ N) u
  -- Step A: 2 * L ≤ wdist 1 (u ^ 2) + 4 * δ
  have hsq : 2 * L ≤ wdist (1 : FreeGroup (Fin 2) ⧸ N) (u ^ 2) + 4 * δ := by
    obtain ⟨p, hp1, hp2⟩ := exists_midpoint (1 : FreeGroup (Fin 2) ⧸ N) u
    have hup1 : wdist u (u * p) = L / 2 := by
      simpa [hp1] using wdist_mul_left u 1 p
    have hup2 : wdist (u * p) (u ^ 2) = L - L / 2 := by
      have : wdist (u * p) (u * u) = wdist p u := wdist_mul_left u p u
      simpa [pow_two, hp2] using this
    have hp_disp : L ≤ wdist p (u * p) := hmin p
    have h4a := hhyp p (u * p) u 1
    rw [wdist_symm u 1, wdist_symm (u * p) 1, wdist_symm p 1, wdist_symm (u * p) u] at h4a
    have h1up : 2 * L ≤ (L - L / 2) + wdist 1 (u * p) + 2 * δ := by
      have hbr := le_max_iff.mp (by omega : 2 * L - 2 * δ ≤ max (wdist p u + wdist 1 (u * p)) (wdist 1 p + wdist u (u * p)))
      rcases hbr with hA | hB
      · omega
      · exfalso; omega
    have h4b := hhyp 1 (u ^ 2) (u * p) u
    have hu2u : wdist (u ^ 2) u = L := by
      rw [wdist_symm, pow_two]
      simpa using wdist_mul_left u 1 u
    have hbr2 : wdist 1 (u * p) + L ≤ max (L + (L - L / 2)) (wdist 1 (u ^ 2) + L / 2) + 2 * δ := by
      have h4b' := hhyp 1 (u * p) (u ^ 2) u
      rw [hu2u, hup2, wdist_symm (u * p) u, hup1, max_comm] at h4b'
      exact h4b'
    rcases max_choice (L + (L - L / 2)) (wdist 1 (u ^ 2) + L / 2) with hM | hM
    · rw [hM] at hbr2
      exfalso; omega
    · rw [hM] at hbr2
      omega
  -- Step B: inductive step d(1, u^k) + (L - 6δ) ≤ d(1, u^(k+1)) for all k ≥ 1
  have hstep : ∀ k : ℕ, 1 ≤ k →
      wdist (1 : FreeGroup (Fin 2) ⧸ N) (u ^ k) + (L - 6 * δ) ≤ wdist 1 (u ^ (k + 1)) := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      by_cases hk0 : k = 0
      · subst hk0
        simp only [Nat.zero_add, pow_one]
        rw [show (1 + 1 : ℕ) = 2 from rfl]
        omega
      · have hk1 : 1 ≤ k := by omega
        have hih := ih hk1
        have h4 := hhyp 1 (u ^ (k + 1)) (u ^ k) (u ^ (k + 2))
        have hd1 : wdist (u ^ k) (u ^ (k + 2)) = wdist 1 (u ^ 2) := by
          have : u ^ (k + 2) = u ^ k * u ^ 2 := pow_add u k 2
          rw [this]
          simpa using wdist_mul_left (u ^ k) 1 (u ^ 2)
        have hd2 : wdist (u ^ (k + 1)) (u ^ (k + 2)) = L := by
          have : u ^ (k + 2) = u ^ (k + 1) * u := pow_succ u (k + 1)
          rw [this]
          simpa using wdist_mul_left (u ^ (k + 1)) 1 u
        have hd3 : wdist (u ^ (k + 1)) (u ^ k) = L := by
          rw [wdist_symm]
          have : u ^ (k + 1) = u ^ k * u := pow_succ u k
          rw [this]
          simpa using wdist_mul_left (u ^ k) 1 u
        rw [hd1, hd2, hd3] at h4
        rcases max_choice (wdist 1 (u ^ k) + L) (wdist 1 (u ^ (k + 2)) + L) with hM | hM
        · rw [hM] at h4
          exfalso; omega
        · rw [hM] at h4
          have hidx : k + 1 + 1 = k + 2 := rfl
          rw [hidx]
          omega
  intro k
  induction k with
  | zero => simp [wdist_self]
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst hk0
      simp only [Nat.zero_add, pow_one]
      omega
    · have := hstep k (by omega)
      omega

/-- Every nontrivial element `g` in a torsion-free `δ`-hyperbolic 2-generated quotient has
uniformly bounded positive root exponents. -/
private lemma root_exponent_bound
    (δ : ℕ)
    (hhyp : ∀ x y z w : FreeGroup (Fin 2) ⧸ N,
      wdist x y + wdist z w ≤ max (wdist x z + wdist y w) (wdist x w + wdist y z) + 2 * δ)
    (htf : ∀ g : FreeGroup (Fin 2) ⧸ N, ∀ n : ℕ, n ≠ 0 → g ^ n = 1 → g = 1)
    (g : FreeGroup (Fin 2) ⧸ N) (hg : g ≠ 1) :
    ∃ B : ℕ, ∀ (h : FreeGroup (Fin 2) ⧸ N) (n : ℕ), 1 ≤ n → h ^ n = g → n ≤ B := by
  obtain ⟨K, hK1, hK⟩ := uniform_min_disp δ hhyp htf
  refine ⟨K * wdist 1 g + 1, ?_⟩
  intro h n hn hng
  have hh : h ≠ 1 := by
    intro h1
    rw [h1, one_pow] at hng
    exact hg hng.symm
  let u := h ^ K
  have hne_u : ∃ L : ℕ, ∃ x : FreeGroup (Fin 2) ⧸ N, wdist x (u * x) = L := ⟨wdist 1 u, 1, by simp⟩
  set L₀ := Nat.find hne_u
  obtain ⟨x₀, hx₀⟩ := Nat.find_spec hne_u
  change wdist x₀ (u * x₀) = L₀ at hx₀
  have hL₀_min : ∀ x : FreeGroup (Fin 2) ⧸ N, L₀ ≤ wdist x (u * x) :=
    fun x => Nat.find_min' hne_u ⟨x, rfl⟩
  let u' := x₀⁻¹ * u * x₀
  have hu'_len : wdist 1 u' = L₀ := by
    rw [← wdist_mul_left x₀, mul_one]
    simpa [u', mul_assoc] using hx₀
  have hu'_min : ∀ y : FreeGroup (Fin 2) ⧸ N, wdist 1 u' ≤ wdist y (u' * y) := by
    intro y
    rw [hu'_len]
    have hEq : wdist y (u' * y) = wdist (x₀ * y) (u * (x₀ * y)) := by
      rw [← wdist_mul_left x₀]
      simp [u', mul_assoc]
    rw [hEq]
    exact hL₀_min (x₀ * y)
  have hu'_large : 6 * δ + 1 < wdist 1 u' := by
    rw [hu'_len, ← hx₀]
    exact hK h hh x₀
  have hlin := linear_growth_of_min_disp δ hhyp hu'_min hu'_large
  set m : ℕ := 2 * wdist 1 x₀ + 1
  have hpow_conj : u' ^ (n * m) = x₀⁻¹ * g ^ (K * m) * x₀ := by
    have hconj_pow : ∀ t : ℕ, u' ^ t = x₀⁻¹ * u ^ t * x₀ := by
      intro t
      induction t with
      | zero => simp
      | succ t iht =>
        rw [pow_succ, pow_succ, iht]
        dsimp [u']
        group
    rw [hconj_pow]
    have hpow_eq : u ^ (n * m) = g ^ (K * m) := by
      dsimp [u]
      rw [← pow_mul, show K * (n * m) = n * (K * m) by ring, pow_mul, hng]
    rw [hpow_eq]
  have hlow : 2 * (n * m) ≤ wdist 1 (u' ^ (n * m)) := hlin (n * m)
  have hup : wdist 1 (u' ^ (n * m)) ≤ 2 * wdist 1 x₀ + K * m * wdist 1 g := by
    rw [hpow_conj]
    calc
      wdist 1 (x₀⁻¹ * g ^ (K * m) * x₀) ≤ 2 * wdist 1 x₀ + wdist 1 (g ^ (K * m)) :=
        wdist_conj_le x₀ (g ^ (K * m))
      _ ≤ 2 * wdist 1 x₀ + (K * m) * wdist 1 g :=
        Nat.add_le_add_left (wdist_pow_le g (K * m)) _
  have hm_pos : 0 < m := by omega
  have hineq : m * (2 * n) ≤ m * (K * wdist 1 g + 1) := by
    have : 2 * (n * m) ≤ m + K * m * wdist 1 g := by omega
    nlinarith
  have h2n : 2 * n ≤ K * wdist 1 g + 1 := Nat.le_of_mul_le_mul_left hineq hm_pos
  omega

end Metric

end OMA.Kourovka88H1

theorem OMA.solution : OMA.R_Kourovka_8_8_kourovka_8_8a_R1.H1 := by
  classical
  intro N _ hhyp htf g hg
  obtain ⟨δ, hδ⟩ := hhyp
  obtain ⟨B, hB⟩ := OMA.Kourovka88H1.root_exponent_bound δ hδ htf g hg
  -- Choose the maximum positive root exponent r ≤ B
  let P (n : ℕ) : Prop := 1 ≤ n ∧ ∃ h : FreeGroup (Fin 2) ⧸ N, h ^ n = g
  have hex : ∃ k : ℕ, P (B - k) := ⟨B - 1, by
    have h1B : 1 ≤ B := hB g 1 le_rfl (pow_one g)
    refine ⟨by omega, g, ?_⟩
    have : B - (B - 1) = 1 := by omega
    rw [this, pow_one]⟩
  set k₀ := Nat.find hex
  obtain ⟨hr1, c, hcr⟩ := Nat.find_spec hex
  set r := B - k₀
  have hrmax : ∀ n : ℕ, P n → n ≤ r := by
    intro n hn
    have hnB : n ≤ B := hB hn.2.choose n hn.1 hn.2.choose_spec
    by_contra hgt
    have hlt : B - n < k₀ := by omega
    have hnot := Nat.find_min hex hlt
    have hsub : B - (B - n) = n := by omega
    rw [hsub] at hnot
    exact hnot hn
  refine ⟨c, (r : ℤ), ?_, by simpa [zpow_natCast] using hcr.symm⟩
  intro h n hnc
  by_cases hn0 : n = 0
  · subst hn0
    simp only [zpow_zero] at hnc
    rw [← hnc, one_pow] at hcr
    exact (hg hcr.symm).elim
  · have habs_pos : 1 ≤ n.natAbs := by omega
    have hpow_nat : ∃ h' : FreeGroup (Fin 2) ⧸ N, h' ^ n.natAbs = c := by
      rcases Int.natAbs_eq n with heq | heq
      · refine ⟨h, ?_⟩
        rw [← zpow_natCast, ← heq, hnc]
      · refine ⟨h⁻¹, ?_⟩
        rw [inv_pow, ← zpow_natCast, ← zpow_neg, ← heq, hnc]
    obtain ⟨h', hh'⟩ := hpow_nat
    have hprod : h' ^ (n.natAbs * r) = g := by
      rw [pow_mul, hh', hcr]
    have hle : n.natAbs * r ≤ r := hrmax (n.natAbs * r) ⟨Nat.mul_pos habs_pos hr1, h', hprod⟩
    have habs1 : n.natAbs = 1 := by nlinarith
    omega

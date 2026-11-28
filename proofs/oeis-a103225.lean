import OMAStatements.S_oeis_a103225

/-!
Bill McEachen's proposed upper bound fails at the Gaussian prime 6203.
The open disc has 120879729 lattice points. All but the origin are
coprime to 6203, and 120879728 is greater than the area of the disc.
-/

namespace GaussianDiscCounterexample

open OMA.S_oeis_a103225

private abbrev Column := Fin 12405
private def x (i : Column) : ℤ := i.val - (6202 : ℤ)
private def radicand (j : ℕ) : ℤ := (6203 : ℤ)^2 - 1 - ((j : ℤ) - 6202)^2

/-- The fuel bounds the work per column. The square test below certifies
each returned height independently of convergence of Newton's iteration. -/
private def newton (n : ℕ) : ℕ → ℕ → ℕ
  | 0, g => g
  | f+1, g =>
    let y := (g + n/g)/2
    if y < g then newton n f y else g

private def heightAt (j : ℕ) : ℕ :=
  let n := (radicand j).toNat
  let h := newton n 16 8192
  if h*h ≤ n then h else 0

private def height (i : Column) : ℕ := heightAt i.val

private abbrev Points := (i : Column) × Fin (2 * height i + 1)

private def point : Points → GaussianInt
  | ⟨i, j⟩ => ⟨x i, (j.val : ℤ) - height i⟩

private theorem injective : Function.Injective point := by
  rintro ⟨i, j⟩ ⟨k, l⟩ h
  have hx := congrArg Zsqrtd.re h
  change (i.val : ℤ)-6202 = (k.val : ℤ)-6202 at hx
  have hik : i = k := Fin.ext (by omega)
  subst k
  have hy := congrArg Zsqrtd.im h
  change (j.val : ℤ) - height i = (l.val : ℤ) - height i at hy
  have hjl : j = l := Fin.ext (by omega)
  cases hjl
  rfl

private theorem columns_fit (i : Column) : (x i)^2 + (height i : ℤ)^2 < (6203 : ℤ)^2 := by
  have lo : (0 : ℤ) ≤ i.val := by positivity
  have hi : (i.val : ℤ) ≤ 12404 := by
    exact_mod_cast (show i.val ≤ 12404 by have := i.isLt; omega)
  have rad : 0 ≤ radicand i.val := by
    dsimp [radicand]
    nlinarith [mul_nonneg lo (sub_nonneg.mpr hi)]
  have hnat : height i * height i ≤ (radicand i.val).toNat := by
    by_cases h : newton (radicand i.val).toNat 16 8192 * newton (radicand i.val).toNat 16 8192 ≤ (radicand i.val).toNat
    · simpa only [height, heightAt, if_pos h] using h
    · simp [height, heightAt, h]
  have hz : (height i : ℤ) * (height i : ℤ) ≤ ((radicand i.val).toNat : ℤ) := by
    exact_mod_cast hnat
  rw [Int.toNat_of_nonneg rad] at hz
  dsimp [x, radicand] at hz ⊢
  nlinarith only [hz]

private theorem inside (p : Points) : (point p).norm < (6203 : ℤ)^2 := by
  obtain ⟨i,j⟩ := p
  have hj := j.isLt
  have hy₁ : 0 ≤ (j.val : ℤ) := by positivity
  have hy₂ : 0 ≤ 2 * (height i : ℤ) - j.val := by omega
  have h := columns_fit i
  change x i * x i - (-1) * ((j.val : ℤ) - height i) * ((j.val : ℤ) - height i) < _
  nlinarith [mul_nonneg hy₁ hy₂]

private def widthSum : ℕ → ℕ
  | 0 => 0
  | j+1 => widthSum j + (2*heightAt j+1)

private theorem widthSum_eq (n : ℕ) : widthSum n = ∑ j ∈ Finset.range n, (2*heightAt j+1) := by
  induction n with
  | zero => simp [widthSum]
  | succ j ih => rw [widthSum, ih, Finset.sum_range_succ]

set_option maxRecDepth 150000 in
set_option maxHeartbeats 2500000 in
private theorem number_of_points : Nat.card Points = 120879729 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  change (∑ i : Fin 12405, (fun j : ℕ => 2*heightAt j+1) i.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => 2*heightAt j+1) 12405, ← widthSum_eq]
  decide +kernel

private def eligible : Set GaussianInt :=
  {z | z.norm < (6203 : ℤ)^2 ∧ IsCoprime (6203 : GaussianInt) z}

private theorem finite_eligible : eligible.Finite := by
  let I := Set.Icc (-6203 : ℤ) 6203
  have hI : I.Finite := Set.finite_Icc _ _
  apply ((hI.prod hI).image (fun c : ℤ × ℤ => (⟨c.1,c.2⟩ : GaussianInt))).subset
  intro z hz
  have hn : z.re^2 + z.im^2 < (6203 : ℤ)^2 := by
    simpa [Zsqrtd.norm, sq] using hz.1
  have hre : |z.re| < (6203 : ℤ) := by
    have h : z.re^2 < (6203 : ℤ)^2 := by nlinarith [sq_nonneg z.im]
    simpa using sq_lt_sq.mp h
  have him : |z.im| < (6203 : ℤ) := by
    have h : z.im^2 < (6203 : ℤ)^2 := by nlinarith [sq_nonneg z.re]
    simpa using sq_lt_sq.mp h
  obtain ⟨hr₁, hr₂⟩ := abs_lt.mp hre
  obtain ⟨hi₁, hi₂⟩ := abs_lt.mp him
  exact ⟨(z.re, z.im), ⟨⟨hr₁.le,hr₂.le⟩, ⟨hi₁.le,hi₂.le⟩⟩, rfl⟩

private theorem coprime_of_inside {z : GaussianInt} (hz : z ≠ 0)
    (hn : z.norm < (6203 : ℤ)^2) : IsCoprime (6203 : GaussianInt) z := by
  have : Fact (Nat.Prime 6203) := ⟨by norm_num⟩
  have hp := GaussianInt.prime_of_nat_prime_of_mod_four_eq_three 6203 (by decide)
  apply hp.coprime_iff_not_dvd.mpr
  rintro ⟨w, hw⟩
  have hw₀ : w ≠ 0 := by intro h; simp [h] at hw; contradiction
  have hwpos := GaussianInt.norm_pos.mpr hw₀
  have hpN : ((6203 : ℕ) : GaussianInt).norm = 38477209 := by
    rw [Zsqrtd.norm_natCast]
    norm_num
  rw [hw, Zsqrtd.norm_mul, hpN] at hn
  omega

private theorem lower : 120879728 ≤ a 6203 := by
  have hs : Set.range point ⊆ insert 0 eligible := by
    rintro _ ⟨p,rfl⟩
    by_cases hz : point p = 0
    · exact Set.mem_insert_iff.mpr (.inl hz)
    · exact Set.mem_insert_iff.mpr (.inr ⟨inside p, coprime_of_inside hz (inside p)⟩)
  have h := Set.ncard_le_ncard hs (finite_eligible.insert 0)
  rw [Set.ncard_range_of_injective injective, number_of_points] at h
  have bound := Set.ncard_insert_le (0 : GaussianInt) eligible
  change 120879728 ≤ eligible.ncard
  omega

end GaussianDiscCounterexample

open OMA.S_oeis_a103225 GaussianDiscCounterexample

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a103225.main) := by
  intro h
  have hl : (120879728 : ℝ) ≤ (a 6203 : ℝ) := by exact_mod_cast lower
  have hu := h 6203 (by decide)
  norm_num only [Nat.cast_ofNat] at hu
  nlinarith only [hl, hu, Real.pi_lt_d20]

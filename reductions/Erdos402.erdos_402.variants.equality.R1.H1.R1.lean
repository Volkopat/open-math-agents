import OMAReductions.R_Erdos402_erdos_402_variants_equality_R1
import Mathlib

/-!
# Short prime intervals for the finite part of Graham's equality conjecture

Balasubramanian and Soundararajan, Acta Arithmetica 75 (1996), 1–38, §§2–3.
Complementary nonzero residues give the required number of pairs. A large
prime in either component blocks the associated normalized slot, forcing
additional pairs at repeated slots. Divisor clusters bound the excess.
For the larger cardinalities every relevant divisor cluster is a singleton.

The two inputs concern only a finite prime-and-divisor calculation and a short
prime interval statement. The residue counting and arbitrary-set argument are
proved in this file.
-/

namespace GrahamDivisorClusters

open Finset

private theorem gcd_exponent {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (q : ℕ) :
    (a.gcd b).factorization q = min (a.factorization q) (b.factorization q) := by
  rw [Nat.factorization_gcd ha hb, Finsupp.inf_apply]

/-- With the two row-wise coprimality conditions, a common prime factor of
the crossed products must come from one of the two crossed pairs. -/
theorem cross_gcd {a b u v : ℕ} (ha : 0 < a) (hb : 0 < b) (hu : 0 < u) (hv : 0 < v)
    (hab : a.Coprime b) (huv : u.Coprime v) :
    (a * u).gcd (b * v) = v.gcd a * u.gcd b := by
  apply Nat.eq_of_factorization_eq
    (Nat.gcd_pos_of_pos_left _ (Nat.mul_pos ha hu)).ne'
    (Nat.mul_pos (Nat.gcd_pos_of_pos_left a hv) (Nat.gcd_pos_of_pos_left b hu)).ne'
  intro q
  have hAB : min (a.factorization q) (b.factorization q) = 0 := by
    rw [← gcd_exponent ha.ne' hb.ne', hab.gcd_eq_one]
    simp
  have hUV : min (u.factorization q) (v.factorization q) = 0 := by
    rw [← gcd_exponent hu.ne' hv.ne', huv.gcd_eq_one]
    simp
  rw [gcd_exponent (Nat.mul_pos ha hu).ne' (Nat.mul_pos hb hv).ne',
    Nat.factorization_mul ha.ne' hu.ne', Nat.factorization_mul hb.ne' hv.ne',
    Nat.factorization_mul (Nat.gcd_pos_of_pos_left a hv).ne'
      (Nat.gcd_pos_of_pos_left b hu).ne']
  simp only [Finsupp.add_apply, gcd_exponent hv.ne' ha.ne', gcd_exponent hu.ne' hb.ne']
  omega

private theorem crossed_component_bounds {a b n u v X Y Z X' Y' Z' : ℕ}
    (hU : u = X * Y * Z) (hV : v = X' * Y' * Z') (hY : 0 < Y) (hX' : 0 < X')
    (hG : (a * u).gcd (b * v) = X' * Y)
    (h : a * u ≤ (a * u).gcd (b * v) * n ∧
      b * v ≤ (a * u).gcd (b * v) * n) :
    a * X * Z ≤ n * X' ∧ b * Y' * Z' ≤ n * Y := by
  constructor
  · apply Nat.le_of_mul_le_mul_right _ hY
    calc
      a * X * Z * Y = a * u := by rw [hU]; ac_rfl
      _ ≤ (a * u).gcd (b * v) * n := h.1
      _ = n * X' * Y := by rw [hG]; ac_rfl
  · apply Nat.le_of_mul_le_mul_right _ hX'
    calc
      b * Y' * Z' * X' = b * v := by rw [hV]; ac_rfl
      _ ≤ (a * u).gcd (b * v) * n := h.2
      _ = n * Y * X' := by rw [hG]; ac_rfl

/-- Lemma 2.3 in integral form. The quotient factors left after taking the
two gcds must be 1, since their product costs more than the squared budget
as soon as it reaches 2. -/
theorem coprime_pair_factors {a b n u v : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hu : 0 < u) (hv : 0 < v)
    (hab : a.Coprime b) (huv : u.Coprime v) (hlarge : n ^ 2 < 2 * a ^ 2)
    (h : a * u ≤ (a * u).gcd (b * v) * n ∧
      b * v ≤ (a * u).gcd (b * v) * n)
    (h' : a * v ≤ (a * v).gcd (b * u) * n ∧
      b * u ≤ (a * v).gcd (b * u) * n) :
    u = u.gcd a * u.gcd b ∧ v = v.gcd a * v.gcd b ∧
    a * u.gcd a ≤ n * v.gcd a ∧ a * v.gcd a ≤ n * u.gcd a ∧
    b * u.gcd b ≤ n * v.gcd b ∧ b * v.gcd b ≤ n * u.gcd b := by
  let X := u.gcd a
  let Y := u.gcd b
  let X' := v.gcd a
  let Y' := v.gcd b
  have hX : 0 < X := Nat.gcd_pos_of_pos_left _ hu
  have hY : 0 < Y := Nat.gcd_pos_of_pos_left _ hu
  have hX' : 0 < X' := Nat.gcd_pos_of_pos_left _ hv
  have hY' : 0 < Y' := Nat.gcd_pos_of_pos_left _ hv
  obtain ⟨Z, hU⟩ : X * Y ∣ u :=
    (hab.gcd_both u u).mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_left u a) (Nat.gcd_dvd_left u b)
  obtain ⟨Z', hV⟩ : X' * Y' ∣ v :=
    (hab.gcd_both v v).mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_left v a) (Nat.gcd_dvd_left v b)
  have hZ : 0 < Z := by
    by_contra! h0
    have he := Nat.eq_zero_of_le_zero h0
    rw [hU, he, Nat.mul_zero] at hu
    omega
  have hZ' : 0 < Z' := by
    by_contra! h0
    have he := Nat.eq_zero_of_le_zero h0
    rw [hV, he, Nat.mul_zero] at hv
    omega
  obtain ⟨hAX, hBY'⟩ := crossed_component_bounds hU hV hY hX' (cross_gcd ha hb hu hv hab huv) h
  obtain ⟨hAX', hBY⟩ := crossed_component_bounds hV hU hY' hX (cross_gcd ha hb hv hu hab huv.symm) h'
  have hCost : a ^ 2 * (Z * Z') ≤ n ^ 2 := by
    apply Nat.le_of_mul_le_mul_right _ (Nat.mul_pos hX hX')
    calc
      a ^ 2 * (Z * Z') * (X * X') = (a * X * Z) * (a * X' * Z') := by ring
      _ ≤ (n * X') * (n * X) := Nat.mul_le_mul hAX hAX'
      _ = n ^ 2 * (X * X') := by ring
  have hProduct : Z * Z' = 1 := by
    have hpos := Nat.mul_pos hZ hZ'
    by_contra hne
    have htwo : 2 ≤ Z * Z' := by omega
    have hmul := Nat.mul_le_mul_left (a ^ 2) htwo
    have hh : 2 * a ^ 2 ≤ n ^ 2 := (by simpa [Nat.mul_comm] using hmul.trans hCost)
    omega
  have hZOne : Z = 1 := Nat.dvd_one.mp ⟨Z', hProduct.symm⟩
  have hZ'One : Z' = 1 := Nat.dvd_one.mp ⟨Z, by simpa [Nat.mul_comm] using hProduct.symm⟩
  subst Z
  subst Z'
  simp only [Nat.mul_one] at hU hV hAX hAX' hBY hBY'
  exact ⟨hU, hV, hAX, hAX', hBY, hBY'⟩

private theorem crossed_div {a b n u v g : ℕ} (hg : 0 < g) (hgu : g ∣ u) (hgv : g ∣ v)
    (h : a * u ≤ (a * u).gcd (b * v) * n ∧
      b * v ≤ (a * u).gcd (b * v) * n) :
    a * (u / g) ≤ (a * (u / g)).gcd (b * (v / g)) * n ∧
      b * (v / g) ≤ (a * (u / g)).gcd (b * (v / g)) * n := by
  let x := u / g
  let y := v / g
  have hU : x * g = u := Nat.div_mul_cancel hgu
  have hV : y * g = v := Nat.div_mul_cancel hgv
  have hAX : a * u = (a * x) * g := by rw [Nat.mul_assoc, hU]
  have hBY : b * v = (b * y) * g := by rw [Nat.mul_assoc, hV]
  rw [hAX, hBY, Nat.gcd_mul_right] at h
  exact ⟨Nat.le_of_mul_le_mul_right (by simpa only [Nat.mul_right_comm] using h.1) hg,
    Nat.le_of_mul_le_mul_right (by simpa only [Nat.mul_right_comm] using h.2) hg⟩

/-- If the first factor admits no pair of distinct divisors in the ratio
window, coprime normalized multipliers are divisors of the second factor. -/
theorem coprime_pair_dvd_second {a b n u v : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hu : 0 < u) (hv : 0 < v)
    (hab : a.Coprime b) (huv : u.Coprime v) (hlarge : n ^ 2 < 2 * a ^ 2)
    (hUnique : ∀ x y : ℕ, x ∣ a → y ∣ a → x ≤ y → a * y ≤ n * x → x = y)
    (h : a * u ≤ (a * u).gcd (b * v) * n ∧
      b * v ≤ (a * u).gcd (b * v) * n)
    (h' : a * v ≤ (a * v).gcd (b * u) * n ∧
      b * u ≤ (a * v).gcd (b * u) * n) : u ∣ b ∧ v ∣ b := by
  obtain ⟨hU, hV, huRatio, hvRatio, _, _⟩ :=
    coprime_pair_factors ha hb hu hv hab huv hlarge h h'
  have hEqual : u.gcd a = v.gcd a := by
    rcases le_total (u.gcd a) (v.gcd a) with hle | hle
    · exact hUnique _ _ (Nat.gcd_dvd_right u a) (Nat.gcd_dvd_right v a) hle hvRatio
    · exact (hUnique _ _ (Nat.gcd_dvd_right v a) (Nat.gcd_dvd_right u a) hle huRatio).symm
  have hcop : (u.gcd a).Coprime (v.gcd a) := by
    simpa only [Nat.gcd_comm a u, Nat.gcd_comm a v] using huv.gcd_both a a
  have hone : u.gcd a = 1 := by
    rw [← hEqual, Nat.coprime_iff_gcd_eq_one, Nat.gcd_self] at hcop
    exact hcop
  have hone' := hEqual.symm.trans hone
  rw [hone, Nat.one_mul] at hU
  rw [hone', Nat.one_mul] at hV
  exact ⟨hU.symm ▸ Nat.gcd_dvd_right u b, hV.symm ▸ Nat.gcd_dvd_right v b⟩

/-- In a primitive family each prime can be tested against a multiplier
that avoids it. Pairwise cancellation then detects its full exponent. -/
theorem dvd_second_of_gcd_one {a b n : ℕ} (S : Finset ℕ)
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (hlarge : n ^ 2 < 2 * a ^ 2)
    (hgcd : S.gcd id = 1) (hpos : ∀ u ∈ S, 0 < u)
    (hUnique : ∀ x y : ℕ, x ∣ a → y ∣ a → x ≤ y → a * y ≤ n * x → x = y)
    (hCross : ∀ u ∈ S, ∀ v ∈ S,
      a * u ≤ (a * u).gcd (b * v) * n ∧ b * v ≤ (a * u).gcd (b * v) * n) :
    ∀ u ∈ S, u ∣ b := by
  intro u hu
  apply (Nat.factorization_le_iff_dvd (hpos u hu).ne' hb.ne').mp
  intro q
  by_cases hq : q.Prime
  · have hWitness : ∃ v ∈ S, ¬ q ∣ v := by
      by_contra! hall
      exact hq.not_dvd_one (hgcd ▸ Finset.dvd_gcd hall)
    obtain ⟨v, hv, hqv⟩ := hWitness
    let g := u.gcd v
    let x := u / g
    let y := v / g
    have hg : 0 < g := Nat.gcd_pos_of_pos_left v (hpos u hu)
    have hgu : g ∣ u := Nat.gcd_dvd_left u v
    have hgv : g ∣ v := Nat.gcd_dvd_right u v
    have hx : 0 < x := Nat.div_pos (Nat.gcd_le_left v (hpos u hu)) hg
    have hy : 0 < y := Nat.div_pos (Nat.gcd_le_right u (hpos v hv)) hg
    have hcop : x.Coprime y := Nat.coprime_div_gcd_div_gcd hg
    have hdiv : x ∣ b := (coprime_pair_dvd_second ha hb hx hy hab hcop hlarge hUnique
      (crossed_div hg hgu hgv (hCross u hu v hv))
      (crossed_div hg hgv hgu (hCross v hv u hu))).1
    have hzero : g.factorization q = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (fun hqg => hqv (hqg.trans hgv))
    have hExp : u.factorization q = x.factorization q := calc
      _ = (x * g).factorization q := congrArg (fun w : ℕ => w.factorization q)
        (Nat.div_mul_cancel hgu).symm
      _ = x.factorization q := by
        rw [Nat.factorization_mul hx.ne' hg.ne', Finsupp.add_apply, hzero, Nat.add_zero]
    rw [hExp]
    exact (Nat.factorization_le_iff_dvd hx.ne' hb.ne').mpr hdiv q
  · simp [Nat.factorization_eq_zero_of_not_prime _ hq]

private theorem unique_of_cluster_one {a n : ℕ} (ha : 0 < a)
    (hOne : a.divisors.sup (fun x => (a.divisors.filter (fun y => x ≤ y ∧ a * y ≤ n * x)).card) = 1) :
    ∀ x y : ℕ, x ∣ a → y ∣ a → x ≤ y → a * y ≤ n * x → x = y := by
  intro x y hx hy hxy hwindow
  by_contra hne
  let F := a.divisors.filter (fun z => x ≤ z ∧ a * z ≤ n * x)
  have hxD := Nat.mem_divisors.mpr ⟨hx, ha.ne'⟩
  have hyD := Nat.mem_divisors.mpr ⟨hy, ha.ne'⟩
  have hxF : x ∈ F := Finset.mem_filter.mpr ⟨hxD, le_rfl,
    (Nat.mul_le_mul_left a hxy).trans hwindow⟩
  have hyF : y ∈ F := Finset.mem_filter.mpr ⟨hyD, hxy, hwindow⟩
  have hlarge : 1 < F.card := Finset.one_lt_card.mpr ⟨x, hxF, y, hyF, hne⟩
  have hsmall : F.card ≤ 1 := hOne ▸ Finset.le_sup
    (f := fun x => (a.divisors.filter (fun y => x ≤ y ∧ a * y ≤ n * x)).card) hxD
  omega

private theorem cluster_of_gcd_one {a b n : ℕ} (S : Finset ℕ)
    (hne : S.Nonempty) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hlarge : n ^ 2 < 2 * a ^ 2) (hgcd : S.gcd id = 1) (hpos : ∀ u ∈ S, 0 < u)
    (hUnique : ∀ x y : ℕ, x ∣ a → y ∣ a → x ≤ y → a * y ≤ n * x → x = y)
    (hCross : ∀ u ∈ S, ∀ v ∈ S,
      a * u ≤ (a * u).gcd (b * v) * n ∧ b * v ≤ (a * u).gcd (b * v) * n) :
    ∃ x ∈ b.divisors, S ⊆ b.divisors.filter (fun y => x ≤ y ∧ b * y ≤ n * x) := by
  have hdiv := dvd_second_of_gcd_one S ha hb hab hlarge hgcd hpos hUnique hCross
  let x := S.min' hne
  have hx : x ∈ S := Finset.min'_mem S hne
  refine ⟨x, Nat.mem_divisors.mpr ⟨hdiv x hx, hb.ne'⟩, ?_⟩
  intro y hy
  have hcop : a.Coprime (b * y) := Nat.coprime_mul_iff_right.mpr
    ⟨hab, hab.coprime_dvd_right (hdiv y hy)⟩
  have hG : (a * x).gcd (b * y) = x :=
    Nat.gcd_mul_of_coprime_of_dvd hcop ((hdiv x hx).trans (dvd_mul_right b y))
  have hRatio := (hCross x hx y hy).2
  rw [hG, Nat.mul_comm x n] at hRatio
  exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdiv y hy, hb.ne'⟩,
    Finset.min'_le S y hy, hRatio⟩

/-- The number of distinct multipliers in a family is bounded by the
largest divisor cluster of the second factor. Division by the family gcd
is injective and converts the family to the primitive case. -/
theorem multipliers_cluster_bound {a b n : ℕ} (S : Finset ℕ)
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (hlarge : n ^ 2 < 2 * a ^ 2)
    (hpos : ∀ u ∈ S, 0 < u)
    (hOne : a.divisors.sup (fun x => (a.divisors.filter (fun y => x ≤ y ∧ a * y ≤ n * x)).card) = 1)
    (hCross : ∀ u ∈ S, ∀ v ∈ S,
      a * u ≤ (a * u).gcd (b * v) * n ∧ b * v ≤ (a * u).gcd (b * v) * n) :
    S.card ≤ b.divisors.sup (fun x => (b.divisors.filter (fun y => x ≤ y ∧ b * y ≤ n * x)).card) := by
  by_cases he : S.Nonempty
  · let g := S.gcd id
    let T := S.image (· / g)
    have hdiv (x : ℕ) (hx : x ∈ S) : g ∣ x := Finset.gcd_dvd hx
    have hg : 0 < g := by
      obtain ⟨x, hx⟩ := he
      exact Nat.pos_of_ne_zero (Finset.gcd_ne_zero_iff.mpr ⟨x, hx, (hpos x hx).ne'⟩)
    have hscaled (x : ℕ) (hx : x ∈ S) : (x / g) * g = x := Nat.div_mul_cancel (hdiv x hx)
    have hTcard : T.card = S.card := by
      apply Finset.card_image_of_injOn
      intro x hx y hy h
      change x / g = y / g at h
      rw [← hscaled x hx, ← hscaled y hy, h]
    have hTgcd : T.gcd id = 1 := by
      have hfact : S.gcd id = S.gcd (fun x => g * (x / g)) := by
        apply Finset.gcd_congr rfl
        intro x hx
        simpa only [id_eq, Nat.mul_comm g] using (hscaled x hx).symm
      rw [Finset.gcd_mul_left, normalize_eq] at hfact
      change g = g * S.gcd (fun x => x / g) at hfact
      change (S.image (· / g)).gcd id = 1
      rw [Finset.gcd_image]
      apply Nat.eq_of_mul_eq_mul_left hg
      simpa only [Function.comp_def, id_eq, Nat.mul_one] using hfact.symm
    have hTpos : ∀ u ∈ T, 0 < u := by
      intro u hu
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
      exact Nat.div_pos (Nat.le_of_dvd (hpos x hx) (hdiv x hx)) hg
    have hTcross : ∀ u ∈ T, ∀ v ∈ T,
        a * u ≤ (a * u).gcd (b * v) * n ∧ b * v ≤ (a * u).gcd (b * v) * n := by
      intro u hu v hv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
      exact crossed_div hg (hdiv x hx) (hdiv y hy) (hCross x hx y hy)
    have hTne : T.Nonempty := he.image _
    obtain ⟨x, hx, hsubset⟩ := cluster_of_gcd_one T hTne ha hb hab hlarge hTgcd hTpos
      (unique_of_cluster_one ha hOne) hTcross
    rw [← hTcard]
    exact (Finset.card_le_card hsubset).trans (Finset.le_sup
      (f := fun x => (b.divisors.filter (fun y => x ≤ y ∧ b * y ≤ n * x)).card) hx)
  · simp [Finset.not_nonempty_iff_eq_empty.mp he]

end GrahamDivisorClusters

namespace OMA.R_Erdos402_erdos_402_variants_equality_R1_H1_R1

open Finset

private theorem reduced_le {n a b : ℕ} (ha : 0 < a) (h : a ≤ a.gcd b * n) :
    a / a.gcd b ≤ n := by
  apply Nat.le_of_mul_le_mul_right _ (Nat.gcd_pos_of_pos_left b ha)
  rwa [Nat.div_mul_cancel (Nat.gcd_dvd_left a b), Nat.mul_comm]

private theorem nonzeroResidue {n p : ℕ} (A : Finset ℕ) (hg : A.gcd id = 1)
    (pos : ∀ a ∈ A, 0 < a) (bounds : ∀ a ∈ A, ∀ b ∈ A, a ≤ a.gcd b * n)
    (hp : p.Prime) (hnp : n < p) (a : ℕ) (ha : a ∈ A) : ¬ p ∣ a := by
  intro hpa
  have witness : ∃ b ∈ A, ¬ p ∣ b := by
    by_contra! no
    have hd : p ∣ A.gcd id := Finset.dvd_gcd no
    exact hp.not_dvd_one (hg ▸ hd)
  obtain ⟨b,hb,hpb⟩ := witness
  let g := a.gcd b
  have hpg : ¬ p ∣ g := fun h => hpb (h.trans (Nat.gcd_dvd_right a b))
  have he : a / g * g = a := Nat.div_mul_cancel (Nat.gcd_dvd_left a b)
  have hpq : p ∣ a / g := (hp.dvd_mul.mp (he.symm ▸ hpa)).resolve_right hpg
  have hqpos : 0 < a/g := Nat.div_pos (Nat.gcd_le_left b (pos a ha))
    (Nat.gcd_pos_of_pos_left b (pos a ha))
  exact (not_le_of_gt hnp) ((Nat.le_of_dvd hqpos hpq).trans (reduced_le (pos a ha) (bounds a ha b hb)))

private theorem normalizeResidue {n p a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hpa : ¬ p ∣ a)
    (hab : a ≤ a.gcd b * n) (hba : b ≤ b.gcd a * n) :
    let g := a.gcd b
    a / g ≤ n ∧ b / g ≤ n ∧
    (a : ZMod p) = (a / g : ℕ) * (g : ZMod p) ∧
    (b : ZMod p) = (b / g : ℕ) * (g : ZMod p) ∧
    (g : ZMod p) ≠ 0 := by
  dsimp
  refine ⟨reduced_le ha hab, by rw [Nat.gcd_comm a b]; exact reduced_le hb hba, ?_, ?_, ?_⟩
  · simpa only [Nat.cast_mul] using congrArg (fun t : ℕ => (t : ZMod p)) (Nat.div_mul_cancel (Nat.gcd_dvd_left a b)).symm
  · simpa only [Nat.cast_mul] using congrArg (fun t : ℕ => (t : ZMod p)) (Nat.div_mul_cancel (Nat.gcd_dvd_right a b)).symm
  · rw [ZMod.natCast_eq_zero_iff]
    exact fun hd => hpa (hd.trans (Nat.gcd_dvd_left a b))

private theorem residuesInj {n p : ℕ} (A : Finset ℕ) (hg : A.gcd id = 1)
    (pos : ∀ a ∈ A, 0 < a) (bounds : ∀ a ∈ A, ∀ b ∈ A, a ≤ a.gcd b * n)
    (hp : p.Prime) (hnp : n < p) :
    Set.InjOn (fun a => a % p) ↑A := by
  let : Fact p.Prime := ⟨hp⟩
  intro a ha b hb he
  obtain ⟨hqa,hqb,hcasta,hcastb,hg0⟩ :=
    normalizeResidue (pos a ha) (pos b hb)
      (nonzeroResidue A hg pos bounds hp hnp a ha) (bounds a ha b hb) (bounds b hb a ha)
  have hc := (ZMod.natCast_eq_natCast_iff' a b p).mpr he
  rw [hcasta,hcastb] at hc
  have hqcast := mul_right_cancel₀ hg0 hc
  have ha' := ZMod.val_natCast_of_lt (hqa.trans_lt hnp)
  have hb' := ZMod.val_natCast_of_lt (hqb.trans_lt hnp)
  have hq : a / a.gcd b = b / a.gcd b := ha'.symm.trans ((congrArg ZMod.val hqcast).trans hb')
  rw [← Nat.div_mul_cancel (Nat.gcd_dvd_left a b), hq, Nat.div_mul_cancel (Nat.gcd_dvd_right a b)]

private theorem complementary {n p a b : ℕ} (hp : p.Prime) (hnp : n < p)
    (ha : 0 < a) (hb : 0 < b) (hpa : ¬ p ∣ a)
    (hab : a ≤ a.gcd b * n) (hba : b ≤ b.gcd a * n)
    (hsum : a % p + b % p = p) : a+b = p*(a.gcd b) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨hqa,hqb,hcasta,hcastb,hg0⟩ := normalizeResidue ha hb hpa hab hba
  have hmod : (a : ZMod p) + (b : ZMod p) = 0 := by
    rw [← ZMod.natCast_mod a p, ← ZMod.natCast_mod b p, ← Nat.cast_add, hsum, ZMod.natCast_self]
  rw [hcasta,hcastb,← add_mul] at hmod
  have hqcast := (mul_eq_zero.mp hmod).resolve_right hg0
  have hdiv : p ∣ a / a.gcd b + b / a.gcd b := by
    rwa [← Nat.cast_add, ZMod.natCast_eq_zero_iff] at hqcast
  have hpos : 0 < a / a.gcd b :=
    Nat.div_pos (Nat.gcd_le_left b ha) (Nat.gcd_pos_of_pos_left b ha)
  obtain ⟨k,hk⟩ := hdiv
  have hk1 : k = 1 := by
    have hkp : 0 < k := by
      by_contra! hz
      have hzero : a / a.gcd b + b / a.gcd b = 0 := by
        simpa only [Nat.eq_zero_of_le_zero hz, Nat.mul_zero] using hk
      exact (Nat.ne_of_gt hpos) (Nat.eq_zero_of_add_eq_zero_right hzero)
    by_contra hk1
    have hk2 : 2 ≤ k := by omega
    have hc := Nat.mul_le_mul_left p hk2
    omega
  rw [hk1,mul_one] at hk
  calc
    a+b = (a / a.gcd b + b / a.gcd b)*(a.gcd b) := by
      rw [add_mul, Nat.div_mul_cancel (Nat.gcd_dvd_left a b),
        Nat.div_mul_cancel (Nat.gcd_dvd_right a b)]
    _ = _ := by rw [hk]

theorem complementCount {n p : ℕ} (A : Finset ℕ) (size : A.card = n)
    (hg : A.gcd id = 1) (pos : ∀ a ∈ A, 0 < a)
    (bounds : ∀ a ∈ A, ∀ b ∈ A, a ≤ a.gcd b * n)
    (hp : p.Prime) (hnp : n < p) :
    n-p/2 ≤ ((A ×ˢ A).filter (fun z : ℕ × ℕ =>
      z.1 < z.2 ∧ z.1+z.2 = p*(z.1.gcd z.2))).card := by
  classical
  let rs := A.image (· % p)
  let small := rs.filter (· ≤ p/2)
  let large := rs.filter (fun r => ¬ r ≤ p/2)
  let flip := large.image (p - ·)
  let paired := small ∩ flip
  have residuePos (r : ℕ) (hr : r ∈ rs) : 0 < r := by
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hr
    have ht := nonzeroResidue A hg pos bounds hp hnp a ha
    omega
  have residueLt (r : ℕ) (hr : r ∈ rs) : r < p := by
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hr
    exact Nat.mod_lt _ hp.pos
  have hrs : rs.card = n := (Finset.card_image_of_injOn (residuesInj A hg pos bounds hp hnp)).trans size
  have hf : flip.card = large.card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb he
    have hlt := residueLt _ (Finset.mem_filter.mp ha).1
    have hlt' := residueLt _ (Finset.mem_filter.mp hb).1
    change p-a = p-b at he
    omega
  have hsum : small.card + flip.card = n := by
    rw [hf, ← hrs]
    exact Finset.card_filter_add_card_filter_not _
  have hunion : (small ∪ flip).card ≤ p/2 := by
    have hs : small ∪ flip ⊆ Finset.Icc 1 (p/2) := by
      intro r hr
      rcases Finset.mem_union.mp hr with hl | hh
      · obtain ⟨hr', hrle⟩ := Finset.mem_filter.mp hl
        exact Finset.mem_Icc.mpr ⟨residuePos _ hr', hrle⟩
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hh
        obtain ⟨hu', hule⟩ := Finset.mem_filter.mp hu
        have huLt := residueLt _ hu'
        apply Finset.mem_Icc.mpr
        omega
    simpa using Finset.card_le_card hs
  have pairedCount : n-p/2 ≤ paired.card := by
    have h := Finset.card_union_add_card_inter small flip
    change _ + paired.card = _ at h
    omega
  have pairExist (r : ℕ) (hr : r ∈ paired) :
      ∃ a ∈ A, ∃ b ∈ A, a % p = r ∧ b % p = p-r ∧ a % p < b % p := by
    obtain ⟨hx,hy⟩ := Finset.mem_inter.mp hr
    obtain ⟨hrs0,hrle⟩ := Finset.mem_filter.mp hx
    obtain ⟨s,hs,hsflip⟩ := Finset.mem_image.mp hy
    obtain ⟨hrs1,hsnle⟩ := Finset.mem_filter.mp hs
    obtain ⟨a,ha,har⟩ := Finset.mem_image.mp hrs0
    obtain ⟨b,hb,hbr⟩ := Finset.mem_image.mp hrs1
    have hlt := residueLt _ hrs1
    exact ⟨a,ha,b,hb,har, by omega, by omega⟩
  have sorted (r : ℕ) (hr : r ∈ paired) :
      ∃ z ∈ (A ×ˢ A).filter (fun z : ℕ × ℕ =>
        z.1 < z.2 ∧ z.1+z.2 = p*(z.1.gcd z.2)),
      min (z.1 % p) (z.2 % p) = r := by
    obtain ⟨a,ha,b,hb,hra,hrb,hab⟩ := pairExist r hr
    have hrl := residueLt _ (Finset.mem_filter.mp (Finset.mem_inter.mp hr).1).1
    have hs : a%p+b%p=p := by omega
    have h := complementary hp hnp (pos a ha) (pos b hb)
      (nonzeroResidue A hg pos bounds hp hnp a ha) (bounds a ha b hb) (bounds b hb a ha) hs
    by_cases hab' : a < b
    · exact ⟨(a,b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha,hb⟩,hab',h⟩,
        (min_eq_left hab.le).trans hra⟩
    · have hba : b < a := by
        by_contra! hh
        have he : a=b := by omega
        simp [he] at hab
      exact ⟨(b,a), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hb,ha⟩,hba,
        by simpa only [Nat.gcd_comm b a, Nat.add_comm b a] using h⟩,
        (min_eq_right hab.le).trans hra⟩
  let pick (r : ℕ) : ℕ × ℕ := if hr : r ∈ paired then Classical.choose (sorted r hr) else (0,0)
  apply pairedCount.trans
  apply Finset.card_le_card_of_injOn pick
  · intro r hr
    have hr' : r ∈ paired := hr
    apply Finset.mem_coe.mpr
    simpa only [pick, dif_pos hr'] using (Classical.choose_spec (sorted r hr')).1
  · intro r hr s hs he
    have hr' : r ∈ paired := hr
    have hs' : s ∈ paired := hs
    simp only [pick, dif_pos hr', dif_pos hs'] at he
    have h1 := (Classical.choose_spec (sorted r hr')).2
    have h2 := (Classical.choose_spec (sorted s hs')).2
    exact h1.symm.trans (he ▸ h2)

theorem duplicateCount {n p : ℕ} (A : Finset ℕ) (size : A.card = n)
    (hg : A.gcd id = 1) (pos : ∀ a ∈ A, 0 < a)
    (bounds : ∀ a ∈ A, ∀ b ∈ A, a ≤ a.gcd b * n)
    (hn : 10 ≤ n) (hp : p.Prime) (hnp : n < p) (hpmax : p ≤ 2*n)
    (smooth : ∀ a ∈ A, ∀ q : ℕ, q.Prime → q ∣ a → 2*q ≤ n) :
    let pairs := (A ×ˢ A).filter (fun z : ℕ × ℕ =>
      z.1 < z.2 ∧ z.1+z.2 = p*(z.1.gcd z.2))
    ((Finset.Icc (max (p-n) (n/2+1)) n).filter Nat.Prime).card ≤
      pairs.card - (pairs.image (fun z => z.2 / (z.1.gcd z.2))).card := by
  classical
  obtain ⟨m,hm⟩ := hp.odd_of_ne_two (by omega)
  let pairs := (A ×ˢ A).filter (fun z : ℕ × ℕ =>
    z.1 < z.2 ∧ z.1+z.2 = p*(z.1.gcd z.2))
  let idx (z : ℕ × ℕ) := z.2 / z.1.gcd z.2
  let occupied := pairs.image idx
  let slots := Finset.Ioc (p/2) n
  let primes := (Finset.Icc (max (p-n) (n/2+1)) n).filter Nat.Prime
  let orient (q : ℕ) := max q (p-q)
  let blocked := primes.image orient
  have pairCount : n-p/2 ≤ pairs.card := complementCount A size hg pos bounds hp hnp
  have slotData {z : ℕ × ℕ} (hz : z ∈ pairs) :
      idx z ∈ slots ∧
      (∀ q : ℕ, q.Prime → n < 2*q → q ≠ idx z ∧ q ≠ p-idx z) := by
    rcases z with ⟨a,b⟩
    obtain ⟨hh,hab,hpair⟩ := Finset.mem_filter.mp hz
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hh
    let d := a.gcd b
    have hd : 0 < d := Nat.gcd_pos_of_pos_left b (pos a ha)
    have hda : a / d * d = a := Nat.div_mul_cancel (Nat.gcd_dvd_left a b)
    have hdb : b / d * d = b := Nat.div_mul_cancel (Nat.gcd_dvd_right a b)
    have hqsum : a / d + b / d = p := by
      apply Nat.eq_of_mul_eq_mul_right hd
      rw [add_mul,hda,hdb]
      exact hpair
    have hqlt : a / d < b / d := by
      have he : (a / d) * d < (b / d) * d := by simpa only [hda,hdb] using hab
      exact Nat.lt_of_mul_lt_mul_right he
    have hqb : b / d ≤ n := by
      apply Nat.le_of_mul_le_mul_right _ hd
      rw [hdb, Nat.mul_comm n d]
      simpa only [d, Nat.gcd_comm a b] using bounds b hb a ha
    change b / d ∈ slots ∧ _
    refine ⟨Finset.mem_Ioc.mpr ⟨by omega,hqb⟩, ?_⟩
    intro q hq hlarge
    change q ≠ b/d ∧ q ≠ p-b/d
    constructor
    · rintro rfl
      have stop := smooth b hb _ hq (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right a b))
      omega
    · intro he
      have hq' : q = a/d := by omega
      have hdiv : q ∣ a := hq' ▸ Nat.div_dvd_of_dvd (Nat.gcd_dvd_left a b)
      have stop := smooth a ha q hq hdiv
      omega
  have occupySub : occupied ⊆ slots := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    exact (slotData hz).1
  have blockSub : blocked ⊆ slots := by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hq1,hq2⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1
    change max q (p-q) ∈ slots
    apply Finset.mem_Ioc.mpr
    omega
  have primeInj : Set.InjOn orient ↑primes := by
    intro q hq r hr he
    obtain ⟨hqI,hqpr⟩ := Finset.mem_filter.mp hq
    obtain ⟨hrI,hrpr⟩ := Finset.mem_filter.mp hr
    obtain ⟨hq1,hq2⟩ := Finset.mem_Icc.mp hqI
    obtain ⟨hr1,hr2⟩ := Finset.mem_Icc.mp hrI
    obtain ⟨u,hu⟩ := hqpr.odd_of_ne_two (by omega)
    obtain ⟨v,hv⟩ := hrpr.odd_of_ne_two (by omega)
    change max q (p-q) = max r (p-r) at he
    omega
  have blockCount : blocked.card = primes.card := Finset.card_image_of_injOn primeInj
  have disjoint : Disjoint occupied blocked := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q,hq,he⟩ := Finset.mem_image.mp hy
    obtain ⟨hqI,hqprime⟩ := Finset.mem_filter.mp hq
    obtain ⟨hq1,hq2⟩ := Finset.mem_Icc.mp hqI
    have hqbig : n < 2*q := by omega
    obtain ⟨hlarge,hsmall⟩ := (slotData hz).2 q hqprime hqbig
    change max q (p-q) = idx z at he
    by_cases ho : q ≤ p-q
    · apply hsmall
      rw [← he, max_eq_right ho]
      omega
    · apply hlarge
      rw [← he, max_eq_left (by omega)]
  have unionSub : occupied ∪ blocked ⊆ slots := Finset.union_subset occupySub blockSub
  have room := Finset.card_le_card unionSub
  have hslots : slots.card = n-p/2 := by simp [slots, Nat.card_Ioc]
  rw [Finset.card_union_of_disjoint disjoint, blockCount, hslots] at room
  change primes.card ≤ pairs.card - occupied.card
  omega

theorem repeatSum {α β : Type*} [DecidableEq β] (s : Finset α) (f : α → β)
    (domain : Finset β) (fits : s.image f ⊆ domain) (cap : β → ℕ)
    (bounded : ∀ q ∈ domain, (s.filter (fun a => f a = q)).card ≤ cap q) :
    s.card - (s.image f).card ≤ ∑ q ∈ domain, (cap q - 1) := by
  classical
  have mass := Finset.card_eq_sum_card_image f s
  have unit (q : β) (hq : q ∈ s.image f) :
      1 ≤ (s.filter (fun a => f a = q)).card := by
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hq
    exact Finset.card_pos.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,he⟩⟩
  rw [mass, Finset.card_eq_sum_ones (s.image f), ← Finset.sum_tsub_distrib _ unit]
  apply le_trans _ (Finset.sum_le_sum_of_subset fits)
  exact Finset.sum_le_sum (fun q hq => Nat.sub_le_sub_right (bounded q (fits hq)) 1)

theorem clusterUnique {n b : ℕ} (hb : 0 < b) (hbn : b ≤ n) (hclose : (n-b)^2 < n) :
    b.divisors.sup (fun x => (b.divisors.filter (fun y => x ≤ y ∧ b*y ≤ n*x)).card) = 1 := by
  classical
  apply le_antisymm
  · apply Finset.sup_le_iff.mpr
    intro x hx
    have hxd := (Nat.mem_divisors.mp hx).1
    have hxpos : 0 < x := Nat.pos_of_dvd_of_pos hxd hb
    have sub : b.divisors.filter (fun y => x ≤ y ∧ b*y ≤ n*x) ⊆ {x} := by
      intro y hy
      obtain ⟨hyd, hxy, hwindow⟩ := Finset.mem_filter.mp hy
      have hyd' := (Nat.mem_divisors.mp hyd).1
      apply Finset.mem_singleton.mpr
      by_contra! hne
      have hlt : x < y := lt_of_le_of_ne hxy hne.symm
      let g := x.gcd y
      let X := x/g
      let Y := y/g
      have hg : 0 < g := Nat.gcd_pos_of_pos_left y hxpos
      have hX : X*g = x := Nat.div_mul_cancel (Nat.gcd_dvd_left x y)
      have hY : Y*g = y := Nat.div_mul_cancel (Nat.gcd_dvd_right x y)
      have hXpos : 0 < X := Nat.div_pos (Nat.gcd_le_left y hxpos) hg
      have hXlt : X+1 ≤ Y := by
        have hxyl : X*g < Y*g := by simpa only [hX,hY] using hlt
        exact Nat.lt_of_mul_lt_mul_right hxyl
      have hcop : X.Coprime Y := Nat.coprime_div_gcd_div_gcd hg
      have hXdiv : X ∣ b := (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left x y)).trans hxd
      have hYdiv : Y ∣ b := (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right x y)).trans hyd'
      have hprod : X*(X+1) ≤ b :=
        (Nat.mul_le_mul_left X hXlt).trans (Nat.le_of_dvd hb (hcop.mul_dvd_of_dvd_of_dvd hXdiv hYdiv))
      have hnorm : b*Y ≤ n*X := by
        apply Nat.le_of_mul_le_mul_right _ hg
        simpa only [Nat.mul_assoc,hX,hY] using hwindow
      let delta := n-b
      have htot : b+delta = n := by dsimp [delta]; omega
      have hdelta : b ≤ delta*X := by
        have hnext := (Nat.mul_le_mul_left b hXlt).trans hnorm
        rw [← htot, Nat.mul_add, Nat.mul_one, Nat.add_mul] at hnext
        omega
      have hXd : X+1 ≤ delta := by
        apply Nat.le_of_mul_le_mul_left _ hXpos
        simpa only [Nat.mul_comm delta X] using hprod.trans hdelta
      have hbad : n ≤ delta^2 := by
        calc
          n = b+delta := htot.symm
          _ ≤ delta*X + delta := Nat.add_le_add_right hdelta _
          _ = delta*(X+1) := by ring
          _ ≤ delta*delta := Nat.mul_le_mul_left delta hXd
          _ = delta^2 := by ring
      exact (not_lt_of_ge hbad) hclose
    simpa using Finset.card_le_card sub
  · let f := fun x => (b.divisors.filter (fun y => x ≤ y ∧ b*y ≤ n*x)).card
    have hbb : b ∈ b.divisors := Nat.mem_divisors.mpr ⟨dvd_refl _,hb.ne'⟩
    have hf : 0 < f b := by
      apply Finset.card_pos.mpr
      exact ⟨b, Finset.mem_filter.mpr ⟨hbb, le_rfl, Nat.mul_le_mul_right b hbn⟩⟩
    exact hf.trans_le (Finset.le_sup (f := f) hbb)

theorem strictGap {n p : ℕ} (hn : 10 ≤ n) (hp : p.Prime)
    (hlo : n < p) (hhi : p < 2*n) (short : (2*n-p)^2 ≤ n) : (2*n-p)^2 < n := by
  let d := 2*n-p
  change d^2 ≤ n at short
  change d^2 < n
  by_contra! bad
  have hd : d^2 = n := by omega
  have d2 : 2 ≤ d := by
    by_contra! h
    interval_cases d <;> simp at hd <;> omega
  have sum : p+d = 2*n := by dsimp [d]; omega
  have squareTwice : d*(2*d) = 2*n := by rw [← hd]; ring
  have decomp : d*(2*d-1)+d = d*(2*d) := by
    rw [← Nat.mul_succ]
    congr 1
    omega
  have pdvd : d ∣ p := ⟨2*d-1, by omega⟩
  rcases hp.eq_one_or_self_of_dvd d pdvd with done | done
  · omega
  · dsimp [d] at done; omega

theorem fitAlpha {n p b : ℕ} (hn : 16 ≤ n) (hhi : p ≤ 2*n)
    (hleft : p-n ≤ b) (short : (2*n-p)^2 < n) : n*n < 2*b*b := by
  let d := 2*n-p
  have hd : d*d < n := by simpa only [d,pow_two] using short
  have four : 4*d ≤ n := by
    by_cases small : d < 4
    · omega
    · have h := Nat.mul_le_mul_right d (by omega : 4 ≤ d)
      omega
  have ht : p+d = 2*n := by dsimp [d]; omega
  have three : 3*n ≤ 4*b := by omega
  have squared := Nat.mul_le_mul three three
  nlinarith [Nat.mul_pos (by omega : 0 < n) (by omega : 0 < n)]

theorem pairIndexData {A : Finset ℕ} {n p : ℕ} {z : ℕ × ℕ}
    (pos : ∀ a ∈ A, 0 < a) (bounds : ∀ a ∈ A, ∀ b ∈ A, a ≤ a.gcd b * n)
    (hz : z ∈ (A ×ˢ A).filter (fun w : ℕ × ℕ =>
      w.1 < w.2 ∧ w.1+w.2 = p*(w.1.gcd w.2))) :
    let d := z.1.gcd z.2
    let a := z.2/d
    0 < d ∧ z.2 = a*d ∧ z.1 = (p-a)*d ∧ p/2 < a ∧ a ≤ n := by
  rcases z with ⟨s,t⟩
  obtain ⟨hmem,hst,hpair⟩ := Finset.mem_filter.mp hz
  obtain ⟨hs,ht⟩ := Finset.mem_product.mp hmem
  let d := s.gcd t
  let a := t/d
  have hd : 0 < d := Nat.gcd_pos_of_pos_left t (pos s hs)
  have hds : (s/d)*d = s := Nat.div_mul_cancel (Nat.gcd_dvd_left s t)
  have hdt : a*d = t := Nat.div_mul_cancel (Nat.gcd_dvd_right s t)
  have sums : s/d+a = p := by
    apply Nat.eq_of_mul_eq_mul_right hd
    rw [add_mul,hds,hdt]
    exact hpair
  have diff : s/d < a := by
    have aux : (s/d)*d < a*d := by simpa only [hds,hdt] using hst
    exact Nat.lt_of_mul_lt_mul_right aux
  have hi : a ≤ n := by
    apply Nat.le_of_mul_le_mul_right _ hd
    rw [hdt,Nat.mul_comm n d]
    simpa only [d, Nat.gcd_comm s t] using bounds t ht s hs
  have small : s/d = p-a := by rw [← sums, Nat.add_sub_cancel]
  change 0 < d ∧ t = a*d ∧ s = (p-a)*d ∧ p/2 < a ∧ a ≤ n
  exact ⟨hd,hdt.symm,by rw [← small,hds],by omega,hi⟩

theorem pairCoprime {n p a : ℕ} (hp : p.Prime) (hnp : n < p)
    (ha : a ∈ Finset.Icc ((p+1)/2) n) : a.Coprime (p-a) := by
  obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp ha
  have hpos : 0 < a := by have := hp.two_le; omega
  have he : a+(p-a) = p := by omega
  have hd : a.gcd (p-a) ∣ p := by
    have aux : a.gcd (p-a) ∣ a+(p-a) := Nat.dvd_add (Nat.gcd_dvd_left a _) (Nat.gcd_dvd_right a _)
    exact (congrArg (fun q => a.gcd (p-a) ∣ q) he).mp aux
  rcases hp.eq_one_or_self_of_dvd _ hd with one | all
  · exact one
  · have hg := Nat.gcd_le_left (p-a) hpos
    omega

theorem reverseSum {n p : ℕ} (hn : 10 ≤ n) (hp : p.Prime) (hnp : n < p) (f : ℕ → ℕ) :
    (∑ a ∈ Finset.Icc ((p+1)/2) n, f (p-a)) =
      ∑ b ∈ Finset.Icc (p-n) ((p-1)/2), f b := by
  obtain ⟨m,hm⟩ := hp.odd_of_ne_two (by omega)
  refine Finset.sum_bij (fun a _ => p-a) ?_ ?_ ?_ ?_
  · intro a ha
    obtain ⟨hl,hh⟩ := Finset.mem_Icc.mp ha
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  · intro a ha b hb he
    have ha' := (Finset.mem_Icc.mp ha).2
    have hb' := (Finset.mem_Icc.mp hb).2
    omega
  · intro b hb
    obtain ⟨hl,hh⟩ := Finset.mem_Icc.mp hb
    exact ⟨p-b,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,by omega⟩
  · intros
    rfl

/-- A finite calculation with prime intervals and divisor clusters. -/
def H1 : Prop :=
  ∀ n : ℕ, 10 ≤ n → n ≤ 7000 →
    let U (b : ℕ) := b.divisors.sup (fun x => (b.divisors.filter (fun y => x ≤ y ∧ b*y ≤ n*x)).card)
    ∃ p, p.Prime ∧ n < p ∧ p < 2*n ∧
      (∀ a ∈ Finset.Icc ((p+1)/2) n, n*n < 2*a*a ∧ U a = 1) ∧
      (∑ b ∈ Finset.Icc (p-n) ((p-1)/2), (U b-1)) <
        ((Finset.Icc (max (p-n) (n/2+1)) n).filter Nat.Prime).card

/-- The short prime corridors used in Balasubramanian–Soundararajan, Lemma 3.2. -/
def H2 : Prop :=
  ∀ n : ℕ, 7000 < n → n ≤ 2220000000000 →
    ∃ p, p.Prime ∧ n < p ∧ p < 2*n ∧ (2*n-p)^2 ≤ n ∧
      ((Finset.Icc (max (p-n) (n/2+1)) n).filter Nat.Prime).Nonempty

theorem main : H1 → H2 → OMA.R_Erdos402_erdos_402_variants_equality_R1.H1 := by
  intro small large n hn hmax A hA hg bounds
  classical
  by_contra! noLargePrime
  obtain ⟨sub,size⟩ := Finset.mem_powersetCard.mp hA
  have pos (x : ℕ) (hx : x ∈ A) : 0 < x := by
    obtain ⟨hdiv,hD⟩ := Nat.mem_divisors.mp (sub hx)
    by_contra! hx0
    have he : x = 0 := by omega
    exact hD (by simpa only [he, zero_dvd_iff] using hdiv)
  have smooth (x : ℕ) (hx : x ∈ A) (q : ℕ) (hq : q.Prime) (hd : q ∣ x) : 2*q ≤ n := by
    by_contra! hlarge
    exact noLargePrime q hq hlarge x hx hd
  let U (b : ℕ) := b.divisors.sup (fun x => (b.divisors.filter (fun y => x ≤ y ∧ b*y ≤ n*x)).card)
  have window : ∃ p, p.Prime ∧ n < p ∧ p < 2*n ∧
      (∀ a ∈ Finset.Icc ((p+1)/2) n, n*n < 2*a*a ∧ U a = 1) ∧
      (∑ b ∈ Finset.Icc (p-n) ((p-1)/2), (U b-1)) <
        ((Finset.Icc (max (p-n) (n/2+1)) n).filter Nat.Prime).card := by
    by_cases hsmall : n ≤ 7000
    · exact small n hn hsmall
    · obtain ⟨p,hp,hpLo,hpHi,hgap,hprime⟩ := large n (by omega) hmax
      have short := strictGap hn hp hpLo hpHi hgap
      have allClusters (b : ℕ) (lo : p-n ≤ b) (hi : b ≤ n) : U b = 1 := by
        have hle : n-b ≤ 2*n-p := by omega
        exact clusterUnique (by omega) hi ((Nat.pow_le_pow_left hle _).trans_lt short)
      refine ⟨p,hp,hpLo,hpHi,?_,?_⟩
      · intro a ha
        obtain ⟨alo,ahi⟩ := Finset.mem_Icc.mp ha
        have lo : p-n ≤ a := by omega
        exact ⟨fitAlpha (by omega) hpHi.le lo short, allClusters a lo ahi⟩
      · have hsum : (∑ b ∈ Finset.Icc (p-n) ((p-1)/2), (U b-1)) = 0 := by
          apply Finset.sum_eq_zero
          intro b hb
          obtain ⟨blo,bhi⟩ := Finset.mem_Icc.mp hb
          rw [allClusters b blo (by omega), Nat.sub_self]
        rw [hsum]
        exact Finset.card_pos.mpr hprime
  obtain ⟨p,hp,hpLo,hpHi,clarity,pigeon⟩ := window
  obtain ⟨k,hk⟩ := hp.odd_of_ne_two (by omega)
  let P := (A ×ˢ A).filter (fun z : ℕ × ℕ => z.1 < z.2 ∧ z.1+z.2 = p*(z.1.gcd z.2))
  let idx (z : ℕ × ℕ) := z.2 / z.1.gcd z.2
  let domain := Finset.Icc ((p+1)/2) n
  have fits : P.image idx ⊆ domain := by
    intro a ha
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨_,_,_,hlo,hhi⟩ := pairIndexData pos bounds hz
    exact Finset.mem_Icc.mpr ⟨by change (p+1)/2 ≤ idx z; change p/2 < idx z at hlo; omega,hhi⟩
  have localCap (a : ℕ) (ha : a ∈ domain) :
      (P.filter (fun z => idx z = a)).card ≤ U (p-a) := by
    let P_a := P.filter (fun z => idx z = a)
    let mult (z : ℕ × ℕ) := z.1.gcd z.2
    let M := P_a.image mult
    have receiver (z : ℕ × ℕ) (hz : z ∈ P_a) :
        0 < mult z ∧ z.2 = a*mult z ∧ z.1 = (p-a)*mult z := by
      obtain ⟨hz',he⟩ := Finset.mem_filter.mp hz
      obtain ⟨hd,hl,hs,_,_⟩ := pairIndexData pos bounds hz'
      change idx z = a at he
      rw [← he]
      exact ⟨hd,hl,hs⟩
    have retained : M.card = P_a.card := by
      apply Finset.card_image_of_injOn
      intro z hz w hw he
      change mult z = mult w at he
      obtain ⟨_,hz2,hz1⟩ := receiver z hz
      obtain ⟨_,hw2,hw1⟩ := receiver w hw
      exact Prod.ext (by rw [hz1,hw1,he]) (by rw [hz2,hw2,he])
    have oneMultiplier (d : ℕ) (hd : d ∈ M) : 0 < d ∧ a*d ∈ A ∧ (p-a)*d ∈ A := by
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hd
      obtain ⟨hpos,hz2,hz1⟩ := receiver z hz
      obtain ⟨ha1,ha2⟩ := Finset.mem_product.mp
        (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1
      exact ⟨hpos,hz2 ▸ ha2,hz1 ▸ ha1⟩
    obtain ⟨haMin,haMax⟩ := Finset.mem_Icc.mp ha
    change P_a.card ≤ _
    rw [← retained]
    apply GrahamDivisorClusters.multipliers_cluster_bound M (by omega) (by omega)
      (pairCoprime hp hpLo ha) (by simpa only [pow_two, Nat.mul_assoc] using (clarity a ha).1)
      (fun d hd => (oneMultiplier d hd).1) (clarity a ha).2
    intro d hd e he
    have h1 := (oneMultiplier d hd).2.1
    have h2 := (oneMultiplier e he).2.2
    exact ⟨bounds _ h1 _ h2, by simpa only [Nat.gcd_comm] using bounds _ h2 _ h1⟩
  have lowCount := duplicateCount A size hg pos bounds hn hp hpLo hpHi.le smooth
  have highCount := repeatSum P idx domain fits (fun a => U (p-a)) localCap
  change P.card - (P.image idx).card ≤ ∑ a ∈ Finset.Icc ((p+1)/2) n, (U (p-a)-1) at highCount
  rw [reverseSum hn hp hpLo (fun b => U b-1)] at highCount
  exact (not_lt_of_ge (lowCount.trans highCount)) pigeon

end OMA.R_Erdos402_erdos_402_variants_equality_R1_H1_R1

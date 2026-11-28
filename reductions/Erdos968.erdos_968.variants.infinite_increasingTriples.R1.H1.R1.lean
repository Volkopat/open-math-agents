import OMAReductions.R_Erdos968_erdos_968_variants_infinite_increasingTriples_R1
import Mathlib

/-! Ford, Maynard and Tao, *Chains of large gaps between primes*,
https://arxiv.org/abs/1511.04468, Section 3. Theorem 2 supplies the sifted
offsets, while Lemma 3.1 and (3.9) supply estimates on the
Maier matrix columns. We give the finite first- and second-moment argument
and obtain actual consecutive prime gaps inside the selected row. -/

namespace OMA.Erdos968Maier

open Finset
open scoped BigOperators

/-- On a finite set of rows, a first moment of at least three and a sufficiently
small second-moment contribution from the bad rows give a good row of size three. -/
theorem exists_good_row {V : Type} (Z : Finset V) (rowCount : V → ℕ)
    (bad : V → Prop) [DecidablePred bad]
    (hFirst : 3 * Z.card ≤ ∑ z ∈ Z, rowCount z)
    (hBad : (Z.filter bad).card * (∑ z ∈ Z, rowCount z ^ 2) < Z.card ^ 2) :
    ∃ z ∈ Z, 3 ≤ rowCount z ∧ ¬ bad z := by
  by_contra! hn
  let B := Z.filter bad
  let S := Z.filter (fun x => ¬ bad x)
  have hsmall : ∀ z ∈ S, rowCount z ≤ 2 := by
    intro z hz
    obtain ⟨hZ, hgood⟩ := mem_filter.mp hz
    by_contra! hlarge
    exact hgood (hn z hZ (by omega))
  have hgoodSum : (∑ z ∈ S, rowCount z) ≤ 2 * Z.card := by
    calc
      _ ≤ ∑ _z ∈ S, 2 := sum_le_sum hsmall
      _ = 2 * S.card := by simp [mul_comm]
      _ ≤ 2 * Z.card := Nat.mul_le_mul_left _ (card_filter_le Z _)
  have hsplit : (∑ z ∈ B, rowCount z) + (∑ z ∈ S, rowCount z) = ∑ z ∈ Z, rowCount z :=
    sum_filter_add_sum_filter_not Z bad rowCount
  have hbadSum : Z.card ≤ ∑ z ∈ B, rowCount z := by omega
  have hcs := sum_mul_sq_le_sq_mul_sq B rowCount (fun _ => (1 : ℕ))
  simp only [mul_one, one_pow, sum_const, smul_eq_mul] at hcs
  have hsq : (∑ z ∈ B, rowCount z ^ 2) ≤ ∑ z ∈ Z, rowCount z ^ 2 :=
    sum_le_sum_of_subset (filter_subset _ _)
  have hbound : Z.card ^ 2 ≤ B.card * (∑ z ∈ Z, rowCount z ^ 2) := calc
    _ ≤ (∑ z ∈ B, rowCount z) ^ 2 := Nat.pow_le_pow_left hbadSum 2
    _ ≤ B.card * (∑ z ∈ B, rowCount z ^ 2) := by simpa only [nsmul_eq_mul, mul_one, mul_comm] using hcs
    _ ≤ _ := Nat.mul_le_mul_left _ hsq
  exact (not_lt_of_ge hbound) hBad

/-- Three primes in a contiguous row with no close pair give consecutive prime
gaps at least as large. The right endpoint bounds both logarithmic factors. -/
theorem large_consecutive_gaps_of_interval (L U N : ℕ) (d C : ℝ) (hC : 0 ≤ C)
    (hL : Nat.nth Nat.Prime N ≤ L)
    (hcard : 3 ≤ ((Icc L U).filter Nat.Prime).card)
    (hsep : ∀ a ∈ (Icc L U).filter Nat.Prime, ∀ b ∈ (Icc L U).filter Nat.Prime,
      a < b → d ≤ (b : ℝ) - a)
    (hscale : C * Real.log U ≤ d) :
    ∃ n ≥ N, C * Real.log (Nat.nth Nat.Prime n) ≤
        (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n ∧
      C * Real.log (Nat.nth Nat.Prime (n + 1)) ≤
        (Nat.nth Nat.Prime (n + 2) : ℝ) - Nat.nth Nat.Prime (n + 1) := by
  let P := (Icc L U).filter Nat.Prime
  have hP : 3 ≤ P.card := hcard
  let i₀ : Fin P.card := ⟨0, by omega⟩
  let i₁ : Fin P.card := ⟨1, by omega⟩
  let i₂ : Fin P.card := ⟨2, by omega⟩
  let f := P.orderEmbOfFin rfl
  have hi₀₁ : i₀ < i₁ := by change 0 < 1; decide
  have hi₁₂ : i₁ < i₂ := by change 1 < 2; decide
  have hf (i : Fin P.card) := mem_filter.mp (P.orderEmbOfFin_mem rfl i)
  obtain ⟨a, _, ha⟩ := Nat.exists_lt_card_nth_eq (hf i₀).2
  obtain ⟨b, _, hb⟩ := Nat.exists_lt_card_nth_eq (hf i₁).2
  obtain ⟨c, _, hc⟩ := Nat.exists_lt_card_nth_eq (hf i₂).2
  have mono := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hab : a < b := mono.lt_iff_lt.mp (by rw [ha, hb]; exact f.strictMono hi₀₁)
  have hbc : b < c := mono.lt_iff_lt.mp (by rw [hb, hc]; exact f.strictMono hi₁₂)
  have hLa : L ≤ Nat.nth Nat.Prime a := ha ▸ (mem_Icc.mp (hf i₀).1).1
  have hUc : Nat.nth Nat.Prime c ≤ U := hc ▸ (mem_Icc.mp (hf i₂).1).2
  have hrange (i : ℕ) (hi₀ : a ≤ i) (hi₂ : i ≤ a + 2) : Nat.nth Nat.Prime i ∈ P :=
    mem_filter.mpr ⟨mem_Icc.mpr ⟨hLa.trans (mono.monotone hi₀),
      (mono.monotone (by omega : i ≤ c)).trans hUc⟩, Nat.prime_nth_prime i⟩
  have hlog (i : ℕ) (hi₀ : a ≤ i) (hi₂ : i ≤ a + 2) :
      C * Real.log (Nat.nth Nat.Prime i) ≤ d := by
    have hUi : Nat.nth Nat.Prime i ≤ U := (mem_Icc.mp (mem_filter.mp (hrange i hi₀ hi₂)).1).2
    apply le_trans _ hscale
    apply mul_le_mul_of_nonneg_left _ hC
    exact Real.log_le_log (by exact_mod_cast (Nat.prime_nth_prime i).pos) (by exact_mod_cast hUi)
  refine ⟨a, mono.le_iff_le.mp (hL.trans hLa), ?_, ?_⟩
  · exact (hlog a (by omega) (by omega)).trans
      (hsep _ (hrange a (by omega) (by omega)) _ (hrange (a + 1) (by omega) (by omega))
        (mono (by omega)))
  · exact (hlog (a + 1) (by omega) (by omega)).trans
      (hsep _ (hrange (a + 1) (by omega) (by omega)) _ (hrange (a + 2) (by omega) (by omega))
        (mono (by omega)))

end OMA.Erdos968Maier

namespace OMA.Erdos968Maier

open Finset
open scoped BigOperators

private theorem sum_counts_comm {V W : Type} (Z : Finset V) (T : Finset W)
    (hit : V → W → Prop) [DecidableRel hit] :
    (∑ z ∈ Z, ((T.filter (hit z)).card : ℝ)) =
      ∑ a ∈ T, ((Z.filter fun z => hit z a).card : ℝ) := by
  simp only [← Finset.sum_boole]
  exact Finset.sum_comm

private theorem count_sq_le_offDiag {W : Type} [DecidableEq W] (S : Finset W) :
    (S.card : ℝ)^2 ≤ 1 + 2 * (S.offDiag.card : ℝ) := by
  have hc := Finset.card_union_of_disjoint (disjoint_diag_offDiag S)
  rw [diag_union_offDiag, card_product, diag_card] at hc
  have hcast : (S.card : ℝ)*(S.card : ℝ) = (S.card : ℝ) + (S.offDiag.card : ℝ) := by
    exact_mod_cast hc
  nlinarith only [hcast, sq_nonneg ((S.card : ℝ) - 1)]

/-- A finite Maier matrix has a row with three hits and no near pair whenever
the individual hit lower bound and simultaneous hit upper bound leave enough
room for the second-moment argument. -/
theorem exists_far_row {V W : Type} (Z : Finset V) (T : Finset W)
    (hit : V → W → Prop) [DecidableRel hit] (near : W × W → Prop) [DecidablePred near]
    (lo hi : ℝ) (hhi₀ : 0 ≤ hi)
    (hlo : ∀ a ∈ T, lo ≤ ((Z.filter fun z => hit z a).card : ℝ))
    (hhi : ∀ p ∈ T.offDiag, ((Z.filter fun z => hit z p.1 ∧ hit z p.2).card : ℝ) ≤ hi)
    (hFirst : 3 * (Z.card : ℝ) ≤ (T.card : ℝ) * lo)
    (hSafe : ((T.offDiag.filter near).card : ℝ) * hi *
        ((Z.card : ℝ) + 2 * (T.card : ℝ)^2 * hi) < (Z.card : ℝ)^2) :
    ∃ z ∈ Z, 3 ≤ (T.filter (hit z)).card ∧
      ∀ p ∈ (T.filter (hit z)).offDiag, ¬ near p := by
  classical
  let R (z : V) := T.filter (hit z)
  let hitPair (z : V) (p : W × W) : Prop := hit z p.1 ∧ hit z p.2
  let Q := T.offDiag.filter near
  let bad (z : V) : Prop := ∃ p ∈ (R z).offDiag, near p
  have hEq (z : V) : (R z).offDiag = T.offDiag.filter (hitPair z) := by
    ext p
    simp only [R, hitPair, mem_offDiag, mem_filter]
    tauto
  have hRows : (∑ z ∈ Z, ((R z).card : ℝ)) ≥ 3 * (Z.card : ℝ) := calc
    _ = ∑ a ∈ T, ((Z.filter fun z => hit z a).card : ℝ) := sum_counts_comm Z T hit
    _ ≥ ∑ a ∈ T, lo := Finset.sum_le_sum hlo
    _ = (T.card : ℝ) * lo := by simp [nsmul_eq_mul]
    _ ≥ _ := hFirst
  have hPairs : (∑ z ∈ Z, ((R z).offDiag.card : ℝ)) ≤ (T.card : ℝ)^2 * hi := calc
    _ = ∑ p ∈ T.offDiag, ((Z.filter fun z => hitPair z p).card : ℝ) := by
      simp_rw [hEq]
      exact sum_counts_comm Z T.offDiag hitPair
    _ ≤ ∑ _ ∈ T.offDiag, hi := Finset.sum_le_sum hhi
    _ = (T.offDiag.card : ℝ) * hi := by simp [nsmul_eq_mul]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hhi₀
      have hcard : T.offDiag.card ≤ T.card^2 := by
        rw [Finset.offDiag_card, pow_two]
        exact Nat.sub_le _ _
      exact_mod_cast hcard
  have hSecond : (∑ z ∈ Z, ((R z).card : ℝ)^2) ≤ (Z.card : ℝ) + 2 * (T.card : ℝ)^2 * hi := calc
    _ ≤ ∑ z ∈ Z, (1 + 2 * ((R z).offDiag.card : ℝ)) :=
      Finset.sum_le_sum (fun z _ => count_sq_le_offDiag (R z))
    _ = (Z.card : ℝ) + 2 * ∑ z ∈ Z, ((R z).offDiag.card : ℝ) := by
      simp [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := by linarith only [hPairs]
  have hsub : Z.filter bad ⊆ Q.biUnion (fun p => Z.filter (fun z => hitPair z p)) := by
    intro z hz
    obtain ⟨hzZ, p, hp, hn⟩ := mem_filter.mp hz
    rw [hEq] at hp
    exact mem_biUnion.mpr ⟨p, mem_filter.mpr ⟨(mem_filter.mp hp).1, hn⟩,
      mem_filter.mpr ⟨hzZ, (mem_filter.mp hp).2⟩⟩
  have hBadCount : ((Z.filter bad).card : ℝ) ≤ (Q.card : ℝ) * hi := calc
    _ ≤ ∑ p ∈ Q, ((Z.filter (fun z => hitPair z p)).card : ℝ) := by
      exact_mod_cast ((card_le_card hsub).trans card_biUnion_le)
    _ ≤ ∑ _ ∈ Q, hi := Finset.sum_le_sum (fun p hp => hhi p (mem_filter.mp hp).1)
    _ = _ := by simp [nsmul_eq_mul]
  have hBadReal : ((Z.filter bad).card : ℝ) * (∑ z ∈ Z, ((R z).card : ℝ)^2) < (Z.card : ℝ)^2 :=
    (mul_le_mul hBadCount hSecond
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (mul_nonneg (by positivity) hhi₀)).trans_lt hSafe
  have hFirstNat : 3 * Z.card ≤ ∑ z ∈ Z, (R z).card := by exact_mod_cast hRows
  have hBadNat : (Z.filter bad).card * (∑ z ∈ Z, (R z).card^2) < Z.card^2 := by
    exact_mod_cast hBadReal
  obtain ⟨z, hz, hc, hnb⟩ := exists_good_row Z (fun z => (R z).card) bad hFirstNat hBadNat
  exact ⟨z, hz, hc, fun p hp hn => hnb ⟨p, hp, hn⟩⟩

end OMA.Erdos968Maier

namespace OMA.Erdos968Maier

open Finset

/-- On a positive matrix row, the hits in the sifted offsets are exactly all
the primes in its corresponding contiguous interval. -/
private theorem row_image (x y m P z : ℕ) (hz : 1 ≤ z) (hP : 0 < P) :
    let T := (Ioc x y).filter (fun a => (m + a).Coprime P)
    let K := z * P + m
    ((T.filter fun a => (z * P + (m + a)).Prime).image fun a => K + a) =
      (Icc (K + x + 1) (K + y)).filter Nat.Prime := by
  classical
  dsimp
  ext q
  rw [mem_image, mem_filter]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simp only [mem_filter, mem_Ioc] at ha
    refine ⟨mem_Icc.mpr ?_, ?_⟩
    · omega
    · simpa only [Nat.add_assoc] using ha.2
  · rintro ⟨hq, hprime⟩
    rw [mem_Icc] at hq
    let a := q - (z * P + m)
    have hqa : z * P + m + a = q := by dsimp [a]; omega
    have hqP : P < q := by
      have hle : P ≤ z * P := by simpa using Nat.mul_le_mul_right P hz
      omega
    have hcop : q.Coprime P := hprime.coprime_iff_not_dvd.mpr
      (fun hdvd => (not_le_of_gt hqP) (Nat.le_of_dvd hP hdvd))
    have ha : (m + a).Coprime P := (Nat.coprime_add_mul_right_left (m + a) P z).mp
      (by rwa [Nat.add_comm (m + a), ← Nat.add_assoc, hqa])
    refine ⟨a, ?_, hqa⟩
    simp only [mem_filter, mem_Ioc]
    exact ⟨⟨⟨by omega, by omega⟩, ha⟩, by simpa only [← Nat.add_assoc, hqa]⟩

/-- The row found by the matrix moment bound gives actual consecutive primes,
with gaps controlled by the separation of the surviving columns. -/
theorem consecutive_gaps_of_matrix_row (x y m P Z z N : ℕ)
    (d C : ℝ) (hC : 0 ≤ C) (hP : 0 < P)
    (hm : m < P) (hy : y ≤ P) (hz : z ∈ Icc 1 Z)
    (hN : Nat.nth Nat.Prime N ≤ x)
    (hscale : C * Real.log (((Z + 2) * P : ℕ) : ℝ) ≤ d)
    (T : Finset ℕ) (hT : T = Finset.filter (fun a => (z * P + (m + a)).Prime)
      ((Ioc x y).filter (fun a => (m + a).Coprime P)))
    (hrow : 3 ≤ T.card ∧ ∀ p ∈ T.offDiag, ¬(p.1 < p.2 ∧ (p.2 : ℝ) - p.1 < d)) :
    ∃ n ≥ N, C * Real.log (Nat.nth Nat.Prime n) ≤
        (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n ∧
      C * Real.log (Nat.nth Nat.Prime (n + 1)) ≤
        (Nat.nth Nat.Prime (n + 2) : ℝ) - Nat.nth Nat.Prime (n + 1) := by
  classical
  let K := z * P + m
  have hImage : (T.image fun a => K + a) = (Icc (K + x + 1) (K + y)).filter Nat.Prime :=
    hT ▸ row_image x y m P z (mem_Icc.mp hz).1 hP
  apply large_consecutive_gaps_of_interval (K + x + 1) (K + y) N d C hC
  · omega
  · rw [← hImage, card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h)]
    exact hrow.1
  · rw [← hImage]
    intro a ha b hb hab
    obtain ⟨p, hp, rfl⟩ := mem_image.mp ha
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hb
    have hpq : p < q := Nat.lt_of_add_lt_add_left hab
    have hNoNear := hrow.2 (p, q) (mem_offDiag.mpr ⟨hp, hq, hpq.ne⟩)
    have hdist : d ≤ (q : ℝ) - p := le_of_not_gt (fun h => hNoNear ⟨hpq, h⟩)
    push_cast
    linarith only [hdist]
  · refine (mul_le_mul_of_nonneg_left (Real.log_le_log ?_ ?_) hC).trans hscale
    · exact_mod_cast (show 0 < K + y by
        have hzP : P ≤ z * P := by simpa using Nat.mul_le_mul_right P (mem_Icc.mp hz).1
        dsimp [K]
        omega)
    · exact_mod_cast (show K + y ≤ (Z + 2) * P by
        rw [Nat.add_mul, show 2 * P = P + P by omega]
        have hzP := Nat.mul_le_mul_right P (mem_Icc.mp hz).2
        dsimp [K]
        omega)

end OMA.Erdos968Maier

namespace OMA.Erdos968Maier

theorem exists_maier_constants (L U l u : ℝ)
    (hL : 0 < L) (hU : 0 < U) (hl : 0 < l) (hu : 0 < u) :
    ∃ A ≥ 2, ∃ ε > 0, ∀ (T Q Z w : ℝ),
      0 ≤ T → 0 < Z → 0 < w →
      L * A ≤ T * w → T * w ≤ U * A → Q * w^2 ≤ U * A^2 * ε →
      3 * Z ≤ T * (l * w * Z) ∧
        Q * (u * w^2 * Z) * (Z + 2 * T^2 * (u * w^2 * Z)) < Z^2 := by
  let A : ℝ := max 2 (3 / (L * l))
  have hA : 2 ≤ A := le_max_left _ _
  have hA₀ : 0 < A := (by norm_num : (0 : ℝ) < 2).trans_le hA
  have hA₃ : 3 ≤ A * (L * l) := (div_le_iff₀ (mul_pos hL hl)).mp (le_max_right _ _)
  let J : ℝ := 1 + 2 * (U * A)^2 * u
  have hJ : 0 < J := by dsimp [J]; positivity
  let ε : ℝ := (2 * (U * A^2 * u * J))⁻¹
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨A, hA, ε, hε, ?_⟩
  intro T Q Z w hT hZ hw hlow hupp hnear
  have hfirst := mul_le_mul_of_nonneg_right hlow (mul_nonneg hl.le hZ.le)
  have hfirst₃ := mul_le_mul_of_nonneg_right hA₃ hZ.le
  refine ⟨by nlinarith only [hfirst, hfirst₃], ?_⟩
  have hsq : (T*w)^2 ≤ (U*A)^2 := pow_le_pow_left₀ (mul_nonneg hT hw.le) hupp 2
  have hj : Z + 2 * T^2 * (u * w^2 * Z) ≤ J * Z := by
    dsimp [J]
    nlinarith only [mul_le_mul_of_nonneg_right hsq (show 0 ≤ 2*u*Z by positivity)]
  have hq : Q * (u * w^2 * Z) ≤ (U*A^2*ε*u)*Z := by
    nlinarith only [mul_le_mul_of_nonneg_right hnear (mul_nonneg hu.le hZ.le)]
  have hcombine := mul_le_mul hq hj (show 0 ≤ Z + 2 * T^2 * (u * w^2 * Z) by positivity)
    (show 0 ≤ (U*A^2*ε*u)*Z by positivity)
  have hcore : 2 * (U*A^2*ε*u*J) = 1 := by
    calc
      _ = (2 * (U*A^2*u*J)) * ε := by ring
      _ = 1 := mul_inv_cancel₀ (by positivity)
  have hbound : ((U*A^2*ε*u)*Z) * (J*Z) = Z^2 / 2 := by
    nlinarith only [congrArg (fun z : ℝ => z * Z^2) hcore]
  rw [hbound] at hcombine
  exact hcombine.trans_lt (by nlinarith only [sq_pos_of_pos hZ])

end OMA.Erdos968Maier

namespace OMA.R_Erdos968_erdos_968_variants_infinite_increasingTriples_R1_H1_R1

open Filter Finset
open OMA.Erdos968Maier

/-- The Ford–Maynard–Tao sifted interval with its total size and nearby-pair
bound. The latter follows by covering normalized offsets with overlapping
windows and using (3.4). -/
def H1 : Prop :=
  ∀ b : ℝ, 0 < b → ∃ L U : ℝ, 0 < L ∧ 0 < U ∧
    ∀ A : ℝ, 2 ≤ A → ∀ ε : ℝ, 0 < ε → ∀ R : ℝ, 0 < R →
      ∀ᶠ x : ℕ in atTop, ∀ B : ℕ,
        (B = 1 ∨ B.Prime ∧ b * Real.log x ≤ B ∧ B ≤ x) →
        let P := ((x.primesLE).erase B).prod id
        let w := Real.log x / (x : ℝ)
        ∃ m y : ℕ, m < P ∧ x < y ∧ y ≤ P ∧ R * (x : ℝ) ≤ y ∧
          let T := (Ioc x y).filter (fun a => (m + a).Coprime P)
          L * A ≤ (T.card : ℝ) * w ∧ (T.card : ℝ) * w ≤ U * A ∧
          ((T.offDiag.filter (fun p => p.1 < p.2 ∧ (p.2 : ℝ) - p.1 < ε * y)).card : ℝ) *
            w^2 ≤ U * A^2 * ε

/-- Uniform prime counts in columns and pairs of columns for an exceptional
prime-deleted primorial. The pair offsets are distinct modulo the primorial
because their ordered difference is positive and smaller than it. -/
def H2 : Prop :=
  ∃ b l u K : ℝ, 0 < b ∧ 0 < l ∧ 0 < u ∧ 0 < K ∧
    ∀ᶠ x : ℕ in atTop, ∃ B Z : ℕ,
      (B = 1 ∨ B.Prime ∧ b * Real.log x ≤ B ∧ B ≤ x) ∧ 0 < Z ∧
      let P := ((x.primesLE).erase B).prod id
      let w := Real.log x / (x : ℝ)
      let W := Icc 1 Z
      Real.log (((Z + 2) * P : ℕ) : ℝ) ≤ K * x ∧
      (∀ a : ℕ, a < 2 * P → a.Coprime P →
        l * w * Z ≤ ((W.filter (fun z => (z * P + a).Prime)).card : ℝ)) ∧
      (∀ a d : ℕ, d < 2 * P → a < d → d < a + P → a.Coprime P → d.Coprime P →
        ((W.filter (fun z => (z * P + a).Prime ∧ (z * P + d).Prime)).card : ℝ) ≤
          u * w^2 * Z)

theorem main : H1 → H2 →
    OMA.R_Erdos968_erdos_968_variants_infinite_increasingTriples_R1.H1 := by
  classical
  intro hsieve hcols C N
  obtain ⟨b, l, u, K, hb, hl, hu, hK, hcol⟩ := hcols
  obtain ⟨L, U, hL, hU, hs⟩ := hsieve b hb
  obtain ⟨A, hA, ε, hε, hscales⟩ := exists_maier_constants L U l u hL hU hl hu
  let Cp : ℝ := max C 0
  have hCp : 0 ≤ Cp := le_max_right _ _
  let R : ℝ := Cp * K / ε + 1
  have hR : 0 < R := add_pos_of_nonneg_of_pos (div_nonneg (mul_nonneg hCp hK.le) hε.le) zero_lt_one
  obtain ⟨x, hxs, hxc, hxN⟩ := ((hs A hA ε hε R hR).and (hcol.and
    (eventually_ge_atTop (Nat.nth Nat.Prime N)))).exists
  obtain ⟨B, Z, hB, hZ, hlog, hsingle, hpair⟩ := hxc
  obtain ⟨m, y, hm, hxy, hy, hRy, hTl, hTu, hQ⟩ := hxs B hB
  let P := ((x.primesLE).erase B).prod id
  let w := Real.log x / (x : ℝ)
  let W := Icc 1 Z
  let T := (Ioc x y).filter (fun a => (m + a).Coprime P)
  let hit (z a : ℕ) := (z * P + (m + a)).Prime
  let d : ℝ := ε * y
  let near (p : ℕ × ℕ) : Prop := p.1 < p.2 ∧ (p.2 : ℝ) - p.1 < d
  have hPR : 0 < P := Nat.zero_lt_of_lt hm
  have hw : 0 < w := div_pos
    (Real.log_pos (by exact_mod_cast (Nat.prime_nth_prime N).one_lt.trans_le hxN))
    (by exact_mod_cast (Nat.prime_nth_prime N).pos.trans_le hxN)
  have hW : W.card = Z := by simp [W, Nat.card_Icc]
  have ha (a : ℕ) (haT : a ∈ T) : x < a ∧ a ≤ P ∧ (m + a).Coprime P := by
    obtain ⟨haI, hcop⟩ := mem_filter.mp haT
    exact ⟨(mem_Ioc.mp haI).1, (mem_Ioc.mp haI).2.trans hy, hcop⟩
  have hlo (a : ℕ) (haT : a ∈ T) :
      l * w * Z ≤ ((W.filter (fun z => hit z a)).card : ℝ) := by
    have hlt : m + a < 2 * P := by have := (ha a haT).2.1; omega
    exact hsingle (m + a) hlt (ha a haT).2.2
  have ordered (a b : ℕ) (haT : a ∈ T) (hbT : b ∈ T) (hab : a < b) :
      ((W.filter (fun z => hit z a ∧ hit z b)).card : ℝ) ≤ u * w^2 * Z := by
    obtain ⟨hax, haP, hac⟩ := ha a haT
    obtain ⟨hbx, hbP, hbc⟩ := ha b hbT
    exact hpair (m + a) (m + b) (by omega) (by omega) (by omega) hac hbc
  have hhi (p : ℕ × ℕ) (hp : p ∈ T.offDiag) :
      ((W.filter (fun z => hit z p.1 ∧ hit z p.2)).card : ℝ) ≤ u * w^2 * Z := by
    obtain ⟨haT, hbT, hne⟩ := mem_offDiag.mp hp
    rcases lt_or_gt_of_ne hne with h | h
    · exact ordered _ _ haT hbT h
    · simpa only [and_comm] using ordered _ _ hbT haT h
  obtain ⟨hFirst, hSafe⟩ := hscales T.card (T.offDiag.filter near).card Z w
    (by positivity) (by exact_mod_cast hZ) hw hTl hTu hQ
  obtain ⟨z, hz, hzCount, hzNear⟩ :=
    exists_far_row W T hit near (l * w * Z) (u * w^2 * Z) (by positivity) hlo hhi
      (by simpa only [hW] using hFirst) (by simpa only [hW] using hSafe)
  have hscale : Cp * Real.log (((Z + 2) * P : ℕ) : ℝ) ≤ d := by
    refine (mul_le_mul_of_nonneg_left hlog hCp).trans ?_
    have hbase : Cp * K ≤ ε * R := by
      dsimp [R]
      calc
        Cp * K = ε * (Cp * K / ε) := by field_simp
        _ ≤ ε * (Cp * K / ε + 1) := by gcongr; linarith
    have hbase' := mul_le_mul_of_nonneg_right hbase (Nat.cast_nonneg x)
    have hy' := mul_le_mul_of_nonneg_left hRy hε.le
    dsimp [d]
    nlinarith only [hbase', hy']
  obtain ⟨n, hn, hg₁, hg₂⟩ :=
    consecutive_gaps_of_matrix_row x y m P Z z N d Cp hCp hPR hm hy hz hxN hscale
      (T.filter (hit z)) rfl ⟨hzCount, hzNear⟩
  have hC : C ≤ Cp := le_max_left _ _
  have log_nonneg (i : ℕ) : 0 ≤ Real.log (Nat.nth Nat.Prime i) :=
    Real.log_nonneg (by exact_mod_cast (Nat.prime_nth_prime i).one_lt.le)
  exact ⟨n, hn, (mul_le_mul_of_nonneg_right hC (log_nonneg _)).trans hg₁,
    (mul_le_mul_of_nonneg_right hC (log_nonneg _)).trans hg₂⟩

end OMA.R_Erdos968_erdos_968_variants_infinite_increasingTriples_R1_H1_R1

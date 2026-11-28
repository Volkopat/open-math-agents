import OMAReductions.R_Erdos287_erdos_287_variants_prime_conjecture_R1_H1_R1
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! Assemble the local major-arc estimates for the prime variant of Erdős 287. -/

open Filter MeasureTheory
open scoped BigOperators Function

namespace OMA.R_Erdos287_erdos_287_variants_prime_conjecture_R1_H1_R1_H1_R1

/-- Uniform integrated approximation on each arc with denominator at least two. -/
def H1 : Prop :=
  let F (N : ℕ) (θ : ℝ) :=
    ∑ p ∈ (Finset.Icc N (2 * N)).filter Nat.Prime,
      ∑ q ∈ (Finset.Icc 1 N).filter Nat.Prime,
        Real.log p * Real.log q * Real.cos (2 * Real.pi * ((p : ℝ) + 1 - 2 * q) * θ)
  let J (N : ℕ) : ℝ :=
    let δ := Real.log (N : ℝ) ^ 2 / (N : ℝ)
    ∫ β in Set.Icc (-δ) δ,
      ∫ x in Set.Icc (N : ℝ) (2 * (N : ℝ)),
        ∫ y in Set.Icc (0 : ℝ) (N : ℝ),
          Real.cos (2 * Real.pi * ((x + 1 - 2 * y) * β))
  ∀ᶠ N : ℕ in atTop, ∀ a b : ℕ, 2 ≤ b → (b : ℝ) ≤ Real.log N ^ 2 →
    a ≤ b → Nat.Coprime a b →
      let δ := Real.log (N:ℝ)^2 / N
      let c := b / Nat.gcd b 2
      |(∫ θ in (Set.Icc (0:ℝ) 1 ∩ Set.Icc ((a:ℝ)/b-δ) ((a:ℝ)/b+δ)), F N θ) -
        (((ArithmeticFunction.moebius b : ℝ) * (ArithmeticFunction.moebius c : ℝ)) /
          ((Nat.totient b : ℝ) * (Nat.totient c : ℝ))) *
          Real.cos (2 * Real.pi * ((a:ℝ)/b)) * J N| ≤ (N:ℝ)/(512 * Real.log N ^ 4)

/-- The two half-arcs for denominator one. -/
def H2 : Prop :=
  let F (N : ℕ) (θ : ℝ) :=
    ∑ p ∈ (Finset.Icc N (2 * N)).filter Nat.Prime,
      ∑ q ∈ (Finset.Icc 1 N).filter Nat.Prime,
        Real.log p * Real.log q * Real.cos (2 * Real.pi * ((p : ℝ) + 1 - 2 * q) * θ)
  let J (N : ℕ) : ℝ :=
    let δ := Real.log (N : ℝ) ^ 2 / (N : ℝ)
    ∫ β in Set.Icc (-δ) δ,
      ∫ x in Set.Icc (N : ℝ) (2 * (N : ℝ)),
        ∫ y in Set.Icc (0 : ℝ) (N : ℝ),
          Real.cos (2 * Real.pi * ((x + 1 - 2 * y) * β))
  ∀ᶠ N : ℕ in atTop,
    let δ := Real.log (N:ℝ)^2 / N
    |(∫ θ in (Set.Icc (0:ℝ) 1 ∩ Set.Icc (-δ) δ), F N θ) +
      (∫ θ in (Set.Icc (0:ℝ) 1 ∩ Set.Icc (1-δ) (1+δ)), F N θ) - J N|
      ≤ (N:ℝ)/(512 * Real.log N ^ 4)

section

private theorem nthRoots_sum (n : ℕ) (hn : 0 < n) :
    (∑ z ∈ Polynomial.nthRootsFinset n (1 : ℂ), z) = if n = 1 then 1 else 0 := by
  classical
  have : NeZero n := ⟨hn.ne'⟩
  let z := Complex.exp (2 * Real.pi * Complex.I / (n:ℂ))
  have hz : IsPrimitiveRoot z n := Complex.isPrimitiveRoot_exp n hn.ne'
  have himage : Polynomial.nthRootsFinset n (1:ℂ) = (Finset.range n).image (z ^ ·) := by
    ext x
    rw [Polynomial.mem_nthRootsFinset hn, Finset.mem_image]
    constructor
    · intro hx
      obtain ⟨i, hi, he⟩ := hz.eq_pow_of_pow_eq_one hx
      exact ⟨i, Finset.mem_range.mpr hi, he⟩
    · rintro ⟨i, -, rfl⟩
      rw [← pow_mul, mul_comm, pow_mul, hz.pow_eq_one, one_pow]
  rw [himage, Finset.sum_image hz.injOn_pow]
  split_ifs with h
  · subst n
    simp
  · have H := geom_sum_mul z n
    rw [hz.pow_eq_one, sub_self] at H
    exact (mul_eq_zero.mp H).resolve_right (sub_ne_zero.mpr (hz.ne_one (by omega)))

private theorem primitive_sum (n : ℕ) (hn : 0 < n) :
    (∑ z ∈ primitiveRoots n ℂ, z) = (ArithmeticFunction.moebius n : ℂ) := by
  classical
  let f (k : ℕ) : ℂ := ∑ z ∈ primitiveRoots k ℂ, z
  let g (k : ℕ) : ℂ := if k = 1 then 1 else 0
  have hg (k : ℕ) (hk : 0 < k) : ∑ d ∈ k.divisors, f d = g k := by
    have h := nthRoots_sum k hk
    rw [IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots, Finset.sum_biUnion] at h
    · exact h
    · intro i hi j hj hij
      exact IsPrimitiveRoot.disjoint hij
  have hm := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp hg) n hn
  change f n = _
  rw [← hm, Finset.sum_eq_single (n,1)]
  · simp [g]
  · intro a ha hne
    have hprod := (Nat.mem_divisorsAntidiagonal.mp ha).1
    have hsnd : a.2 ≠ 1 := by
      intro h
      apply hne
      apply Prod.ext
      · simpa [h] using hprod
      · exact h
    simp [g, hsnd]
  · intro h
    exact (h (Nat.mem_divisorsAntidiagonal.mpr ⟨by simp, hn.ne'⟩)).elim

theorem ramanujan_cos (n : ℕ) (hn : 2 ≤ n) :
    (∑ a ∈ (Finset.range (n+1)).filter (fun a => Nat.Coprime a n),
      Real.cos (2*Real.pi*((a:ℝ)/n))) = (ArithmeticFunction.moebius n : ℝ) := by
  classical
  have hn0 : 0 < n := by omega
  have : NeZero n := ⟨hn0.ne'⟩
  let z := Complex.exp (2 * Real.pi * Complex.I / (n:ℂ))
  have hz : IsPrimitiveRoot z n := Complex.isPrimitiveRoot_exp n hn0.ne'
  have hrange : (Finset.range (n+1)).filter (fun a => Nat.Coprime a n) =
      (Finset.range n).filter (fun a => Nat.Coprime a n) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h, hc⟩
      have hne : a ≠ n := by
        intro h'
        subst a
        have h₁ : n = 1 := by simpa [Nat.Coprime] using hc
        omega
      exact ⟨by omega, hc⟩
    · rintro ⟨h,hc⟩
      exact ⟨by omega,hc⟩
  rw [hrange]
  have hi : primitiveRoots n ℂ = ((Finset.range n).filter (fun a => Nat.Coprime a n)).image
      (z ^ ·) := by
    ext x
    rw [mem_primitiveRoots hn0, hz.isPrimitiveRoot_iff, Finset.mem_image]
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, hc, hx⟩
      exact ⟨i,⟨hi,hc⟩,hx⟩
    · rintro ⟨i,⟨hi,hc⟩,hx⟩
      exact ⟨i,hi,hc,hx⟩
  have he := primitive_sum n hn0
  have hsub : (↑((Finset.range n).filter (fun a => Nat.Coprime a n)) : Set ℕ) ⊆
      ↑(Finset.range n) := fun _ ha => Finset.mem_of_mem_filter _ ha
  rw [hi, Finset.sum_image (hz.injOn_pow.mono hsub)] at he
  have h := congrArg Complex.re he
  rw [Complex.re_sum] at h
  rw [show (ArithmeticFunction.moebius n : ℂ).re = (ArithmeticFunction.moebius n : ℝ)
    by simp] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  have hpow : z ^ i = Complex.exp ((↑(2*Real.pi*((i:ℝ)/n)) : ℂ) * Complex.I) := by
    unfold z
    rw [← Complex.exp_nat_mul]
    push_cast
    congr 1
    ring
  rw [hpow]
  simp [Complex.exp_re]


private theorem reduced_fraction_unique {a b c d : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hab : Nat.Coprime a b) (hcd : Nat.Coprime c d) (h : a*d = c*b) :
    a = c ∧ b = d := by
  have hbd : b ∣ d := hab.symm.dvd_of_dvd_mul_left ⟨c, h.trans (mul_comm _ _)⟩
  have hdb : d ∣ b := hcd.symm.dvd_of_dvd_mul_left ⟨a, h.symm.trans (mul_comm _ _)⟩
  have he := Nat.dvd_antisymm hbd hdb
  subst d
  exact ⟨Nat.eq_of_mul_eq_mul_right hb h, rfl⟩

private theorem arcs_disjoint {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hgap : 2 * δ * L ^ 2 < 1) {a b c d : ℕ}
    (hb : 0 < b) (hd : 0 < d) (hbL : (b : ℝ) ≤ L) (hdL : (d : ℝ) ≤ L)
    (hab : Nat.Coprime a b) (hcd : Nat.Coprime c d) (hne : b ≠ d ∨ a ≠ c) :
    Disjoint (Set.Icc ((a:ℝ)/b-δ) ((a:ℝ)/b+δ)) (Set.Icc ((c:ℝ)/d-δ) ((c:ℝ)/d+δ)) := by
  rw [Set.disjoint_left]
  intro θ hθ hθ'
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hprod : (b : ℝ) * d ≤ L ^ 2 := by
    rw [pow_two]
    exact mul_le_mul hbL hdL hd'.le hL
  have hdist : (a : ℝ)/b - (c : ℝ)/d ≤ 2*δ := by linarith [hθ.1, hθ'.2]
  have hdist' : (c : ℝ)/d - (a : ℝ)/b ≤ 2*δ := by linarith [hθ'.1, hθ.2]
  have hid : ((a : ℝ)/b - (c : ℝ)/d)*((b:ℝ)*d) = (a:ℝ)*d - (c:ℝ)*b := by
    field_simp [hb'.ne', hd'.ne']
  have hcap := (mul_le_mul_of_nonneg_left hprod (show 0 ≤ 2*δ by positivity)).trans_lt hgap
  have hp := (mul_le_mul_of_nonneg_right hdist (mul_nonneg hb'.le hd'.le)).trans_lt hcap
  have hp' := (mul_le_mul_of_nonneg_right hdist' (mul_nonneg hb'.le hd'.le)).trans_lt hcap
  rw [hid] at hp
  have hh : (a:ℝ)*d < (c:ℝ)*b + 1 := by linarith
  have hh' : (c:ℝ)*b < (a:ℝ)*d + 1 := by
    have hneg : ((c : ℝ)/d - (a : ℝ)/b)*((b:ℝ)*d) =
        -(((a : ℝ)/b - (c : ℝ)/d)*((b:ℝ)*d)) := by ring
    rw [hneg, hid] at hp'
    linarith
  have h1 : a*d < c*b + 1 := by exact_mod_cast hh
  have h2 : c*b < a*d + 1 := by exact_mod_cast hh'
  obtain ⟨hA, hB⟩ := reduced_fraction_unique hb hd hab hcd (by omega)
  exact hne.elim (fun h => h hB) (fun h => h hA)

private theorem finite_arcs {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hsep : 2*δ*L^2 < 1) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ θ in (Set.Icc (0:ℝ) 1 ∩ ⋃ b : ℕ, ⋃ a : ℕ,
      ⋃ (_ : 0 < b ∧ (b : ℝ) ≤ L ∧ a ≤ b ∧ Nat.Coprime a b),
        Set.Icc ((a:ℝ)/b-δ) ((a:ℝ)/b+δ)), f θ) =
      ∑ b ∈ Finset.Icc 1 (Nat.floor L),
        ∑ a ∈ (Finset.range (b+1)).filter (fun a => Nat.Coprime a b),
          ∫ θ in (Set.Icc (0:ℝ) 1 ∩ Set.Icc ((a:ℝ)/b-δ) ((a:ℝ)/b+δ)), f θ := by
  let D := (Finset.Icc 1 (Nat.floor L)).sigma
    (fun b => (Finset.range (b+1)).filter (fun a => Nat.Coprime a b))
  let B (i : Σ _ : ℕ, ℕ) : Set ℝ :=
    Set.Icc 0 1 ∩ Set.Icc ((i.2:ℝ)/i.1-δ) ((i.2:ℝ)/i.1+δ)
  have spec (i : Σ _ : ℕ, ℕ) : i ∈ D ↔
      0 < i.1 ∧ (i.1 : ℝ) ≤ L ∧ i.2 ≤ i.1 ∧ Nat.Coprime i.2 i.1 := by
    simp [D, Finset.mem_sigma, Nat.le_floor_iff hL, Nat.succ_le_iff, and_assoc]
  have hset : (Set.Icc (0:ℝ) 1 ∩ ⋃ b : ℕ, ⋃ a : ℕ,
      ⋃ (_ : 0 < b ∧ (b : ℝ) ≤ L ∧ a ≤ b ∧ Nat.Coprime a b),
        Set.Icc ((a:ℝ)/b-δ) ((a:ℝ)/b+δ)) = ⋃ i ∈ D, B i := by
    ext θ
    simp only [Set.mem_inter_iff, Set.mem_iUnion, B]
    constructor
    · rintro ⟨ht, b, a, h, hx⟩
      exact ⟨⟨b,a⟩, (spec ⟨b,a⟩).mpr h, ht, hx⟩
    · rintro ⟨⟨b,a⟩, h, ht, hx⟩
      exact ⟨ht, b, a, (spec ⟨b,a⟩).mp h, hx⟩
  have hd : Set.Pairwise (↑D) (Disjoint on B) := by
    intro i hi j hj hne
    obtain ⟨hb,hbL,_,hab⟩ := (spec i).mp hi
    obtain ⟨hd,hdL,_,hcd⟩ := (spec j).mp hj
    have hij : i.1 ≠ j.1 ∨ i.2 ≠ j.2 := by
      by_contra! h
      rcases i with ⟨b,a⟩
      rcases j with ⟨d,c⟩
      obtain ⟨hb,ha⟩ := h
      dsimp at hb ha
      subst d
      subst c
      exact hne rfl
    exact (arcs_disjoint hL hδ hsep hb hd hbL hdL hab hcd hij).mono
      Set.inter_subset_right Set.inter_subset_right
  rw [hset, integral_biUnion_finset D (fun _ _ => measurableSet_Icc.inter measurableSet_Icc)
      hd (fun _ _ => hf.integrableOn_Icc.mono_set Set.inter_subset_left)]
  rw [show D = (Finset.Icc 1 (Nat.floor L)).sigma
    (fun b => (Finset.range (b+1)).filter (fun a => Nat.Coprime a b)) by rfl, Finset.sum_sigma']

private theorem eventual_geometry :
    ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N:ℝ) ∧ 2*(Real.log (N:ℝ)^2 / N)*(Real.log (N:ℝ)^2)^2 < 1 := by
  have hc : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hL := Real.tendsto_log_atTop.comp hc
  have h := ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 6 one_ne_zero).comp hc).const_mul 2
  have hh := h.eventually (gt_mem_nhds (by norm_num : (2:ℝ)*0 < 1))
  filter_upwards [hL.eventually_ge_atTop 1, hh] with N h₁ h₂
  refine ⟨h₁, ?_⟩
  change 2*(Real.log (N:ℝ)^6 / (1*(N:ℝ)+0)) < 1 at h₂
  simp only [one_mul, add_zero] at h₂
  convert h₂ using 1
  ring

end

set_option maxHeartbeats 1500000 in
theorem main : H1 → H2 → OMA.R_Erdos287_erdos_287_variants_prime_conjecture_R1_H1_R1.H1 := by
  intro ha he
  unfold H1 at ha
  unfold H2 at he
  unfold OMA.R_Erdos287_erdos_287_variants_prime_conjecture_R1_H1_R1.H1
  let F (N : ℕ) (θ : ℝ) :=
    ∑ p ∈ (Finset.Icc N (2 * N)).filter Nat.Prime,
      ∑ q ∈ (Finset.Icc 1 N).filter Nat.Prime,
        Real.log p * Real.log q * Real.cos (2 * Real.pi * ((p : ℝ) + 1 - 2 * q) * θ)
  let A (N : ℕ) : Set ℝ :=
    Set.Icc 0 1 ∩ ⋃ b : ℕ, ⋃ a : ℕ,
      ⋃ (_ : 0 < b ∧ (b : ℝ) ≤ Real.log N ^ 2 ∧ a ≤ b ∧ Nat.Coprime a b),
        Set.Icc ((a : ℝ) / b - Real.log N ^ 2 / N) ((a : ℝ) / b + Real.log N ^ 2 / N)
  let S (N : ℕ) : ℝ :=
    ∑ b ∈ Finset.Icc 1 (Nat.floor (Real.log (N : ℝ) ^ 2)),
      let c := b / Nat.gcd b 2
      ((ArithmeticFunction.moebius b : ℝ) ^ 2 * (ArithmeticFunction.moebius c : ℝ)) /
        ((Nat.totient b : ℝ) * (Nat.totient c : ℝ))
  let J (N : ℕ) : ℝ :=
    let δ := Real.log (N : ℝ) ^ 2 / (N : ℝ)
    ∫ β in Set.Icc (-δ) δ,
      ∫ x in Set.Icc (N : ℝ) (2 * (N : ℝ)),
        ∫ y in Set.Icc (0 : ℝ) (N : ℝ),
          Real.cos (2 * Real.pi * ((x + 1 - 2 * y) * β))
  filter_upwards [ha, he, eventual_geometry, eventually_ge_atTop (1 : ℕ)] with N hA hE hG hN
  change |(∫ θ in A N, F N θ) - S N * J N| ≤ (N:ℝ)/128
  let L := Real.log (N:ℝ)
  let Q := Nat.floor (L^2)
  let δ := L^2 / (N:ℝ)
  let ε := (N:ℝ) / (512 * L^4)
  let D (b : ℕ) := (Finset.range (b+1)).filter (fun a => Nat.Coprime a b)
  let I (b a : ℕ) : ℝ :=
    ∫ θ in (Set.Icc (0:ℝ) 1 ∩ Set.Icc ((a:ℝ)/b-δ) ((a:ℝ)/b+δ)), F N θ
  let w (b : ℕ) : ℝ :=
    let c := b / Nat.gcd b 2
    ((ArithmeticFunction.moebius b : ℝ) * (ArithmeticFunction.moebius c : ℝ)) /
      ((Nat.totient b : ℝ) * (Nat.totient c : ℝ))
  let v (b : ℕ) : ℝ :=
    let c := b / Nat.gcd b 2
    ((ArithmeticFunction.moebius b : ℝ)^2 * (ArithmeticFunction.moebius c : ℝ)) /
      ((Nat.totient b : ℝ) * (Nat.totient c : ℝ))
  have hL : 1 ≤ L := hG.1
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hz : L ≠ 0 := (zero_lt_one.trans_le hL).ne'
  have hsep : 2*δ*(L^2)^2 < 1 := hG.2
  have hF : Continuous (F N) := by unfold F; fun_prop
  have hInt : (∫ θ in A N, F N θ) = ∑ b ∈ Finset.Icc 1 Q, ∑ a ∈ D b, I b a :=
    finite_arcs (sq_nonneg L) (by dsimp [δ]; positivity) hsep (F N) hF
  have hS : S N = ∑ b ∈ Finset.Icc 1 Q, v b := rfl
  have h_group (b : ℕ) (hb : b ∈ Finset.Icc 1 Q) :
      |(∑ a ∈ D b, I b a) - v b * J N| ≤ ((Q:ℝ)+1) * ε := by
    have hb' := Finset.mem_Icc.mp hb
    by_cases hb1 : b = 1
    · subst b
      have hd : D 1 = ({0,1} : Finset ℕ) := by decide
      have hv : v 1 = 1 := by norm_num [v]
      have he' : |I 1 0 + I 1 1 - J N| ≤ ε := by
        simpa [I, δ, L, ε] using hE
      rw [hd, hv, one_mul, Finset.sum_insert (by decide), Finset.sum_singleton]
      exact he'.trans (by nlinarith [Nat.cast_nonneg (α:=ℝ) Q])
    · have hb2 : 2 ≤ b := by omega
      let localModel (a : ℕ) := w b * Real.cos (2 * Real.pi * ((a:ℝ)/b)) * J N
      have hid : ∑ a ∈ D b, localModel a = v b * J N := by
        simp only [localModel, ← Finset.sum_mul, ← Finset.mul_sum]
        rw [show (∑ a ∈ D b, Real.cos (2 * Real.pi * ((a:ℝ)/b))) =
          (ArithmeticFunction.moebius b : ℝ) from ramanujan_cos b hb2]
        unfold w v
        ring
      have hlocal (a : ℕ) (hmem : a ∈ D b) : |I b a - localModel a| ≤ ε := by
        have hmem' := Finset.mem_filter.mp hmem
        have hale : a ≤ b := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hmem'.1
        have hbL : (b:ℝ) ≤ L^2 :=
          (Nat.cast_le.mpr hb'.2).trans (Nat.floor_le (sq_nonneg L))
        exact hA a b hb2 hbL hale hmem'.2
      rw [← hid, ← Finset.sum_sub_distrib]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      calc
        (∑ a ∈ D b, |I b a - localModel a|) ≤ ∑ _ ∈ D b, ε :=
          Finset.sum_le_sum hlocal
        _ = ((D b).card : ℝ) * ε := by simp [nsmul_eq_mul]
        _ ≤ ((Q:ℝ)+1) * ε := by
          apply mul_le_mul_of_nonneg_right _ hε
          have hd : (D b).card ≤ Q + 1 :=
            (Finset.card_filter_le (Finset.range (b+1)) _).trans (by
              simp only [Finset.card_range]
              omega)
          have hcast := Nat.cast_le (α := ℝ) |>.mpr hd
          simpa only [Nat.cast_add, Nat.cast_one] using hcast
  have hcount : (Finset.Icc 1 Q).card = Q := by rw [Nat.card_Icc]; omega
  have hQ : (Q:ℝ) ≤ L^2 := Nat.floor_le (sq_nonneg L)
  have hQ1 : (Q:ℝ)+1 ≤ 2*L^2 := by nlinarith [sq_nonneg (L-1)]
  rw [hInt, hS, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ b ∈ Finset.Icc 1 Q, ((Q:ℝ)+1)*ε := Finset.sum_le_sum h_group
    _ = ((Q:ℝ)*((Q:ℝ)+1))*ε := by simp [hcount, nsmul_eq_mul, mul_assoc]
    _ ≤ (4*L^4)*ε := by
      apply mul_le_mul_of_nonneg_right _ hε
      have h := mul_le_mul (show (Q:ℝ) ≤ 2*L^2 by linarith) hQ1
        (show 0 ≤ (Q:ℝ)+1 by positivity) (show 0 ≤ 2*L^2 by positivity)
      nlinarith only [h]
    _ = (N:ℝ)/128 := by dsimp [ε]; field_simp [hz]; ring

end OMA.R_Erdos287_erdos_287_variants_prime_conjecture_R1_H1_R1_H1_R1

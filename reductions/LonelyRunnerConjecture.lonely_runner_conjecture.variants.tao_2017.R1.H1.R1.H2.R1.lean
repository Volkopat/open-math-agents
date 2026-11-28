import OMAReductions.R_LonelyRunnerConjecture_lonely_runner_conjecture_variants_tao_2017_R1_H1_R1

/-! The rational-box matching step of Hu and Jing, arXiv 2610.23790,
Lemma 5.1. A one-dimensional sieve supplies bounded factors and
a small set of rough parts. The finite matching uses the resulting
bound on the number of uncovered vertices. -/

namespace OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_variants_tao_2017_R1_H1_R1_H2_R1

open Finset

private theorem box_count {V : Type*} (U : Finset V) (A B : Finset ℕ)
    (a b : V → ℕ) (ha : ∀ i ∈ U, a i ∈ A) (hb : ∀ i ∈ U, b i ∈ B)
    (hinj : Set.InjOn (fun i ↦ (a i, b i)) ↑U) : U.card ≤ A.card * B.card := by
  classical
  rw [← Finset.card_product]
  exact Finset.card_le_card_of_injOn (fun i ↦ (a i, b i))
    (fun i hi ↦ Finset.mem_product.mpr ⟨ha i hi, hb i hi⟩) hinj

private theorem cross_height {u v x y D : ℕ} (hu : 0 < u) (hx : 0 < x) (hy : 0 < y)
    (heq : u * y = v * x) (h₁ : x ≤ D) (h₂ : y ≤ D) :
    max u v ≤ D * Nat.gcd u v := by
  let g := Nat.gcd u v
  have hg : 0 < g := Nat.gcd_pos_of_pos_left v hu
  have eu : u / g * g = u := Nat.div_mul_cancel (Nat.gcd_dvd_left u v)
  have ev : v / g * g = v := Nat.div_mul_cancel (Nat.gcd_dvd_right u v)
  have h : u / g * y = v / g * x := by
    apply Nat.mul_left_cancel hg
    calc
      g * (u / g * y) = (u / g * g) * y := by ac_rfl
      _ = u * y := by rw [eu]
      _ = v * x := heq
      _ = (v / g * g) * x := by rw [ev]
      _ = g * (v / g * x) := by ac_rfl
  have cop : (u / g).Coprime (v / g) := Nat.coprime_div_gcd_div_gcd hg
  have hd₁ : u / g ∣ x := cop.dvd_of_dvd_mul_left (h ▸ dvd_mul_right (u / g) y)
  have hd₂ : v / g ∣ y := cop.symm.dvd_of_dvd_mul_left (h.symm ▸ dvd_mul_right (v / g) x)
  apply max_le
  · calc
      u = u / g * g := eu.symm
      _ ≤ D * g := Nat.mul_le_mul_right g ((Nat.le_of_dvd hx hd₁).trans h₁)
  · calc
      v = v / g * g := ev.symm
      _ ≤ D * g := Nat.mul_le_mul_right g ((Nat.le_of_dvd hy hd₂).trans h₂)

private theorem cross_of_fraction {u v a b c d : ℕ} {ξ : ℚ} (hb : 0 < b) (hd : 0 < d)
    (h₁ : (u : ℚ) = ξ * a / b) (h₂ : (v : ℚ) = ξ * c / d) :
    u * (c * b) = v * (a * d) := by
  have h₁' := (div_eq_iff (by exact_mod_cast hb.ne' : (b : ℚ) ≠ 0)).mp h₁.symm
  have h₂' := (div_eq_iff (by exact_mod_cast hd.ne' : (d : ℚ) ≠ 0)).mp h₂.symm
  exact_mod_cast (show (u : ℚ) * ((c : ℚ) * b) = (v : ℚ) * ((a : ℚ) * d) by
    calc
      _ = ((u : ℚ) * b) * c := by ring
      _ = ((v : ℚ) * d) * a := by rw [← h₁', ← h₂']; ring
      _ = _ := by ring)

private theorem finite_matching {n : ℕ} (U : Finset (Fin n)) (R : Fin n → Fin n → Prop) :
    ∃ (m : ℕ) (e : Fin m × Bool ↪ Fin n) (W : Finset (Fin n)),
      (∀ p : Fin m, e (p, false) ∈ U ∧ e (p, true) ∈ U ∧
        R (e (p, false)) (e (p, true))) ∧ W ⊆ U ∧
      U.card ≤ 2 * m + W.card ∧
      ∀ i ∈ W, ∀ j ∈ W, i ≠ j → ¬ R i j := by
  classical
  induction U using Finset.strongInductionOn with
  | _ V ih =>
    by_cases h : ∃ i ∈ V, ∃ j ∈ V, i ≠ j ∧ R i j
    · obtain ⟨i, hi, j, hj, hij, hR⟩ := h
      let V' := (V.erase i).erase j
      have hsub₁ : V.erase i ⊆ V := Finset.erase_subset _ _
      have hsub₂ : V' ⊆ V.erase i := Finset.erase_subset _ _
      have hsub : V' ⊆ V := hsub₂.trans hsub₁
      have hj' : j ∈ V.erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
      have hv : V'.card + 2 = V.card := by
        have h₁ := Finset.card_erase_of_mem hi
        have h₂ := Finset.card_erase_of_mem hj'
        change V'.card = (V.erase i).card - 1 at h₂
        have : 0 < (V.erase i).card := Finset.card_pos.mpr ⟨j, hj'⟩
        omega
      have strict : V' ⊂ V := Finset.ssubset_of_subset_of_ssubset hsub₂
        (Finset.erase_ssubset hi)
      obtain ⟨m, e, W, he, hWV, hcount, hfree⟩ := ih V' strict
      have heV (p : Fin m) (b : Bool) : e (p, b) ∈ V' := by
        cases b
        · exact (he p).1
        · exact (he p).2.1
      have avoid (p : Fin m) (b : Bool) : e (p, b) ≠ i ∧ e (p, b) ≠ j :=
        ⟨(Finset.mem_erase.mp (hsub₂ (heV p b))).1,
          (Finset.mem_erase.mp (heV p b)).1⟩
      let extend (x : Fin (m + 1) × Bool) : Fin n :=
        Fin.cases (fun b ↦ if b then j else i) (fun p b ↦ e (p, b)) x.1 x.2
      have hinj : Function.Injective extend := by
        rintro ⟨p, b⟩ ⟨q, d⟩ hEq
        induction p using Fin.cases generalizing q with
        | zero =>
          induction q using Fin.cases with
          | zero => cases b <;> cases d <;> simp_all [extend]
          | succ q =>
            cases b
            · exact ((avoid q d).1 (by simpa [extend] using hEq.symm)).elim
            · exact ((avoid q d).2 (by simpa [extend] using hEq.symm)).elim
        | succ p =>
          induction q using Fin.cases with
          | zero =>
            cases d
            · exact ((avoid p b).1 (by simpa [extend] using hEq)).elim
            · exact ((avoid p b).2 (by simpa [extend] using hEq)).elim
          | succ q =>
            have eq : (p, b) = (q, d) := e.injective (by simpa [extend] using hEq)
            injection eq with ep eb
            subst q
            subst d
            rfl
      refine ⟨m + 1, ⟨extend, hinj⟩, W, ?_, hWV.trans hsub, by omega, hfree⟩
      intro p
      induction p using Fin.cases with
      | zero => exact ⟨hi, hj, hR⟩
      | succ p => exact ⟨hsub (he p).1, hsub (he p).2.1, (he p).2.2⟩
    · let emptyMatch : Fin 0 × Bool ↪ Fin n :=
        ⟨fun p ↦ p.1.elim0, fun p _ _ ↦ p.1.elim0⟩
      refine ⟨0, emptyMatch, V, fun p ↦ p.elim0, (fun _ h ↦ h), by omega, ?_⟩
      intro i hi j hj hij hR
      exact h ⟨i, hi, j, hj, hij, hR⟩

private theorem rough_image {P A : ℕ} (G : Finset ℕ) (r : ℕ → ℕ)
    (hr : ∀ a ∈ G, r a ∈ Icc 1 A ∧ P.Coprime (r a)) :
    (G.image r).card ≤ ((Icc 1 A).filter (P.Coprime ·)).card := by
  refine card_le_card fun r' hr' ↦ ?_
  obtain ⟨a, ha, rfl⟩ := mem_image.mp hr'
  exact mem_filter.mpr (hr a ha)

/-- For an appropriate fixed modulus, the positive integers coprime to it
have arbitrarily small density in sufficiently long initial intervals. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ P N : ℕ, 0 < P ∧
    ∀ A : ℕ, N ≤ A → (((Icc 1 A).filter (P.Coprime ·)).card : ℝ) ≤ ε * A

/-- For a fixed modulus, the factor supported on its primes is uniformly
bounded outside arbitrarily small exceptional sets in initial intervals. -/
def H2 : Prop :=
  ∀ P : ℕ, 0 < P → ∀ ε : ℝ, 0 < ε → ∃ S : ℕ, 0 < S ∧
    ∀ A : ℕ, ∃ G : Finset ℕ, G ⊆ Icc 1 A ∧ ∃ s r : ℕ → ℕ,
      (∀ a ∈ G, a = s a * r a ∧ 0 < s a ∧ s a ≤ S ∧ r a ∈ Icc 1 A ∧ P.Coprime (r a)) ∧
      (((Icc 1 A \ G).card : ℕ) : ℝ) ≤ ε * A

set_option maxHeartbeats 600000 in
theorem main : H1 → H2 → OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_variants_tao_2017_R1_H1_R1.H2 := by
  classical
  intro density factors C hC
  let ε : ℝ := 1 / (8 * C)
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨P, N, hP, density⟩ := density ε hε
  obtain ⟨S, hS, sieve⟩ := factors P hP ε hε
  let N₀ := max 4 (N * N)
  let D := max (S * S) (⌈C⌉₊ * N₀)
  have hN₀ : 4 ≤ N₀ := le_max_left _ _
  have hNpos : (0 : ℝ) < N₀ := by exact_mod_cast (show 0 < N₀ by omega)
  have hη : (0 : ℝ) < 1 / (N₀ : ℝ) := one_div_pos.mpr hNpos
  refine ⟨D, 1 / (N₀ : ℝ), (Nat.mul_pos hS hS).trans_le (le_max_left _ _), hη, ?_⟩
  intro n v hv U hU ξ A B _ _ _ harea hrep
  have choices (i : Fin n) : ∃ a b : ℕ, i ∈ U →
      a ∈ Icc 1 A ∧ b ∈ Icc 1 B ∧ (v i : ℚ) = ξ * a / b := by
    by_cases hi : i ∈ U
    · obtain ⟨a, b, ha, ha', hb, hb', heq⟩ := hrep i hi
      exact ⟨a, b, fun _ ↦ ⟨mem_Icc.mpr ⟨ha, ha'⟩, mem_Icc.mpr ⟨hb, hb'⟩, heq⟩⟩
    · exact ⟨0, 0, fun h ↦ (hi h).elim⟩
  choose a b hab using choices
  have pairs : Set.InjOn (fun i ↦ (a i, b i)) (↑U : Set (Fin n)) := by
    intro i hi j hj h
    have h₁ := (hab i hi).2.2
    have h₂ := (hab j hj).2.2
    have ha' : a i = a j := congrArg Prod.fst h
    have hb' : b i = b j := congrArg Prod.snd h
    rw [ha', hb', ← h₂] at h₁
    exact v.injective (by exact_mod_cast h₁)
  by_cases hsmall : U.card < N₀
  · obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (show 1 < U.card by omega)
    let e : Fin 1 × Bool ↪ Fin n :=
      ⟨fun p ↦ if p.2 then j else i, by
        rintro ⟨p, k⟩ ⟨q, l⟩ he
        apply Prod.ext (Subsingleton.elim p q)
        cases k <;> cases l <;> simp_all⟩
    have hD' : A * B ≤ D := by
      have hC' : C ≤ (⌈C⌉₊ : ℕ) := Nat.le_ceil C
      have hU' : (U.card : ℝ) ≤ N₀ := by exact_mod_cast hsmall.le
      have ha : A * B ≤ ⌈C⌉₊ * N₀ := by
        exact_mod_cast harea.trans
          (mul_le_mul hC' hU' (by positivity) (by positivity))
      exact ha.trans (le_max_right _ _)
    have hi' := hab i hi
    have hj' := hab j hj
    have ep : (1 / (N₀ : ℝ)) * U.card ≤ 1 := by
      rw [one_div_mul_eq_div, div_le_one hNpos]
      exact_mod_cast hsmall.le
    refine ⟨1, e, by simpa using ep, fun p ↦ ⟨hi, hj, ?_⟩⟩
    have ha := mem_Icc.mp hi'.1
    have hb := mem_Icc.mp hi'.2.1
    have hc := mem_Icc.mp hj'.1
    have hd := mem_Icc.mp hj'.2.1
    exact cross_height (hv i) (mul_pos ha.1 hd.1) (mul_pos hc.1 hb.1)
      (cross_of_fraction hb.1 hd.1 hi'.2.2 hj'.2.2)
      ((Nat.mul_le_mul ha.2 hd.2).trans hD') ((Nat.mul_le_mul hc.2 hb.2).trans hD')
  · have hlarge : N₀ ≤ U.card := Nat.le_of_not_gt hsmall
    have hbox : U.card ≤ A * B := by
      simpa using box_count U (Icc 1 A) (Icc 1 B) a b
        (fun i hi ↦ (hab i hi).1) (fun i hi ↦ (hab i hi).2.1) pairs
    have longer : N ≤ A ∨ N ≤ B := by
      by_contra! h
      have : A * B < N * N := Nat.mul_lt_mul_of_lt_of_lt h.1 h.2
      exact (not_lt_of_ge ((le_max_right 4 (N * N)).trans (hlarge.trans hbox))) this
    obtain ⟨GA, hGA, sA, rA, fA, badA⟩ := sieve A
    obtain ⟨GB, hGB, sB, rB, fB, badB⟩ := sieve B
    have roughA (hA : N ≤ A) : ((GA.image rA).card : ℝ) ≤ ε * A :=
      (show ((GA.image rA).card : ℝ) ≤ (((Icc 1 A).filter (P.Coprime ·)).card : ℝ) by
        exact_mod_cast rough_image (P := P) GA rA (fun a ha ↦ (fA a ha).2.2.2)).trans
        (density A hA)
    have roughB (hB : N ≤ B) : ((GB.image rB).card : ℝ) ≤ ε * B :=
      (show ((GB.image rB).card : ℝ) ≤ (((Icc 1 B).filter (P.Coprime ·)).card : ℝ) by
        exact_mod_cast rough_image (P := P) GB rB (fun b hb ↦ (fB b hb).2.2.2)).trans
        (density B hB)
    let R (i j : Fin n) := max (v i) (v j) ≤ D * Nat.gcd (v i) (v j)
    obtain ⟨m, e, W, he, hWU, hcount, hfree⟩ := finite_matching U R
    let W₁ := W.filter fun i ↦ a i ∈ GA
    let W₂ := W₁.filter fun i ↦ b i ∈ GB
    let E₁ := W.filter fun i ↦ a i ∉ GA
    let E₂ := W₁.filter fun i ↦ b i ∉ GB
    have hclass : Set.InjOn (fun i ↦ (rA (a i), rB (b i))) (↑W₂ : Set (Fin n)) := by
      intro i hi j hj h
      have hia := mem_filter.mp (mem_filter.mp hi).1
      have hja := mem_filter.mp (mem_filter.mp hj).1
      have hib := (mem_filter.mp hi).2
      have hjb := (mem_filter.mp hj).2
      have ia := fA (a i) hia.2
      have ja := fA (a j) hja.2
      have ib := fB (b i) hib
      have jb := fB (b j) hjb
      have hra : rA (a i) = rA (a j) := congrArg Prod.fst h
      have hrb : rB (b i) = rB (b j) := congrArg Prod.snd h
      have hu := hab i (hWU hia.1)
      have hw := hab j (hWU hja.1)
      have hx := cross_of_fraction (mem_Icc.mp hu.2.1).1 (mem_Icc.mp hw.2.1).1 hu.2.2 hw.2.2
      rw [ia.1, ja.1, ib.1, jb.1, hra, hrb] at hx
      have hprod : (rA (a j) * rB (b j)) *
          (v i * (sA (a j) * sB (b i))) =
          (rA (a j) * rB (b j)) * (v j * (sA (a i) * sB (b j))) := by
        convert hx using 1 <;> ac_rfl
      have hp : 0 < rA (a j) * rB (b j) :=
        mul_pos (mem_Icc.mp ja.2.2.2.1).1 (mem_Icc.mp jb.2.2.2.1).1
      by_contra hne
      apply hfree i hia.1 j hja.1 hne
      exact cross_height (hv i) (mul_pos ia.2.1 jb.2.1) (mul_pos ja.2.1 ib.2.1)
        (Nat.mul_left_cancel hp hprod)
        ((Nat.mul_le_mul ia.2.2.1 jb.2.2.1).trans (le_max_left _ _))
        ((Nat.mul_le_mul ja.2.2.1 ib.2.2.1).trans (le_max_left _ _))
    have goodCount : W₂.card ≤ (GA.image rA).card * (GB.image rB).card :=
      box_count W₂ (GA.image rA) (GB.image rB) _ _
        (fun i hi ↦ mem_image_of_mem _ (mem_filter.mp (mem_filter.mp hi).1).2)
        (fun i hi ↦ mem_image_of_mem _ (mem_filter.mp hi).2) hclass
    have rleA : (GA.image rA).card ≤ A := by
      simpa using card_le_card (s := GA.image rA) (t := Icc 1 A) (fun x hx ↦ by
        obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
        exact (fA y hy).2.2.2.1)
    have rleB : (GB.image rB).card ≤ B := by
      simpa using card_le_card (s := GB.image rB) (t := Icc 1 B) (fun x hx ↦ by
        obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
        exact (fB y hy).2.2.2.1)
    have hGood : (W₂.card : ℝ) ≤ ε * ((A : ℝ) * B) := by
      have hcast : (W₂.card : ℝ) ≤ ((GA.image rA).card : ℝ) * (GB.image rB).card :=
        by exact_mod_cast goodCount
      have hAR : ((GA.image rA).card : ℝ) ≤ A := by exact_mod_cast rleA
      have hBR : ((GB.image rB).card : ℝ) ≤ B := by exact_mod_cast rleB
      rcases longer with hA | hB
      · calc
          _ ≤ (ε * A) * B := hcast.trans (mul_le_mul (roughA hA) hBR (by positivity) (by positivity))
          _ = _ := by ring
      · calc
          _ ≤ (A : ℝ) * (ε * B) := hcast.trans (mul_le_mul hAR (roughB hB) (by positivity) (by positivity))
          _ = _ := by ring
    have e₁Count : E₁.card ≤ (Icc 1 A \ GA).card * B := by
      simpa using box_count E₁ (Icc 1 A \ GA) (Icc 1 B) a b
        (fun i hi ↦ mem_sdiff.mpr ⟨(hab i (hWU (mem_filter.mp hi).1)).1, (mem_filter.mp hi).2⟩)
        (fun i hi ↦ (hab i (hWU (mem_filter.mp hi).1)).2.1)
        (pairs.mono fun _ hi ↦ hWU (mem_filter.mp hi).1)
    have e₂Count : E₂.card ≤ A * (Icc 1 B \ GB).card := by
      simpa using box_count E₂ (Icc 1 A) (Icc 1 B \ GB) a b
        (fun i hi ↦ (hab i (hWU (mem_filter.mp (mem_filter.mp hi).1).1)).1)
        (fun i hi ↦ mem_sdiff.mpr
          ⟨(hab i (hWU (mem_filter.mp (mem_filter.mp hi).1).1)).2.1, (mem_filter.mp hi).2⟩)
        (pairs.mono fun _ hi ↦ hWU (mem_filter.mp (mem_filter.mp hi).1).1)
    have hBad₁ : (E₁.card : ℝ) ≤ ε * ((A : ℝ) * B) := by
      calc
        _ ≤ (((Icc 1 A \ GA).card : ℕ) : ℝ) * B := by exact_mod_cast e₁Count
        _ ≤ (ε * A) * B := mul_le_mul_of_nonneg_right badA (by positivity)
        _ = _ := by ring
    have hBad₂ : (E₂.card : ℝ) ≤ ε * ((A : ℝ) * B) := by
      calc
        _ ≤ (A : ℝ) * ((Icc 1 B \ GB).card : ℝ) := by exact_mod_cast e₂Count
        _ ≤ (A : ℝ) * (ε * B) := mul_le_mul_of_nonneg_left badB (by positivity)
        _ = _ := by ring
    have part₁ : W₁.card + E₁.card = W.card := card_filter_add_card_filter_not _
    have part₂ : W₂.card + E₂.card = W₁.card := card_filter_add_card_filter_not _
    have hwCard : (W.card : ℝ) ≤ U.card / 2 := by
      have hL : ε * ((A : ℝ) * B) ≤ U.card / 8 := by
        calc
          _ ≤ ε * (C * U.card) := mul_le_mul_of_nonneg_left harea hε.le
          _ = _ := by dsimp [ε]; field_simp [show C ≠ 0 by linarith]
      have h₁ : (W₁.card : ℝ) + E₁.card = W.card := by exact_mod_cast part₁
      have h₂ : (W₂.card : ℝ) + E₂.card = W₁.card := by exact_mod_cast part₂
      linarith only [hGood, hBad₁, hBad₂, h₁, h₂, hL, Nat.cast_nonneg (α := ℝ) U.card]
    refine ⟨m, e, ?_, he⟩
    have hm : (U.card : ℝ) ≤ 2 * (m : ℝ) + W.card := by exact_mod_cast hcount
    have heighth : (4 : ℝ) ≤ N₀ := by exact_mod_cast hN₀
    calc
      _ ≤ (1 / 4 : ℝ) * U.card :=
        mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le (by norm_num) heighth) (by positivity)
      _ ≤ _ := by linarith

end OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_variants_tao_2017_R1_H1_R1_H2_R1

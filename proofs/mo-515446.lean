import OMAStatements.S_mo_515446

/-!
# A positive proportion with a prime factor exceeding the square root

Credit: @grp06.

Problem: https://mathoverflow.net/questions/515446
Related forum answer: https://mathoverflow.net/a/515857

The proof below uses an elementary block count and a square-divisor sieve.
-/

open scoped BigOperators

namespace OMA.MO515446Proof

open OMA.S_mo_515446 (Admissible Good)
open scoped Classical

private def offset (p a : ℕ) : ℕ :=
  if a % p = 0 then 0 else p - a % p

private theorem offset_lt {p : ℕ} (hp : 0 < p) (a : ℕ) :
    offset p a < p := by
  unfold offset
  split <;> omega

private theorem dvd_add_offset {p : ℕ} (hp : 0 < p) (a : ℕ) :
    p ∣ a + offset p a := by
  have ha := Nat.div_add_mod a p
  have hr := Nat.mod_lt a hp
  unfold offset
  split
  · exact ⟨a / p, by omega⟩
  · refine ⟨a / p + 1, ?_⟩
    rw [Nat.mul_add, Nat.mul_one]
    omega

private theorem half_residue_inj {p n m : ℕ} (hp : p.Prime)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hn' : n ≤ (p - 1) / 2)
    (hm' : m ≤ (p - 1) / 2) (h : n ^ 2 + n ≡ m ^ 2 + m [MOD p]) : n = m := by
  have ordered {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ (p - 1) / 2)
      (he : a ^ 2 + a ≡ b ^ 2 + b [MOD p]) : False := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hab.le
    have hfactor : b ^ 2 + b = a ^ 2 + a + k * (b + a + 1) := by
      rw [hk]
      ring
    have hd : p ∣ k * (b + a + 1) := by
      have hd' := he.dvd'
      rw [hfactor, Nat.add_sub_cancel_left] at hd'
      exact hd'
    rcases hp.dvd_mul.mp hd with hk' | hs'
    · have := Nat.le_of_dvd (show 0 < k by omega) hk'
      omega
    · have := Nat.le_of_dvd (show 0 < b + a + 1 by omega) hs'
      omega
  rcases lt_trichotomy n m with hlt | heq | hgt
  · exact (ordered hn hlt hm' h).elim
  · exact heq
  · exact (ordered hm hgt hn' h.symm).elim

private theorem block_count (L M p : ℕ) (hp : p.Prime) :
    (M / p) * ((p - 1) / 2) ≤
      ((Finset.range M).filter
        (fun x => ∃ n, 1 ≤ n ∧ n ≤ (p - 1) / 2 ∧ p ∣ n ^ 2 + n + (L + x + 1))).card := by
  classical
  let K := (p - 1) / 2
  let A (n : ℕ) := n ^ 2 + n + (L + 1)
  let f (z : Fin (M / p) × Fin K) : ℕ :=
    p * z.1.val + offset p (A (z.2.val + 1))
  have hfdiv (z : Fin (M / p) × Fin K) :
      p ∣ (z.2.val + 1) ^ 2 + (z.2.val + 1) + (L + f z + 1) := by
    have he : (z.2.val + 1) ^ 2 + (z.2.val + 1) + (L + f z + 1) =
        (A (z.2.val + 1) + offset p (A (z.2.val + 1))) + p * z.1.val := by
      dsimp only [f, A]
      ring
    rw [he]
    exact dvd_add (dvd_add_offset hp.pos _) (dvd_mul_right p _)
  have hbnd (z : Fin (M / p) × Fin K) : f z < M := by
    have hr := offset_lt hp.pos (A (z.2.val + 1))
    have hq : z.1.val + 1 ≤ M / p := z.1.isLt
    have hmul := Nat.mul_le_mul_left p hq
    have htotal : p * (M / p) ≤ M := by
      have := Nat.div_add_mod M p
      omega
    have he : p * (z.1.val + 1) = p * z.1.val + p := by ring
    dsimp only [f]
    omega
  have hinj : Function.Injective f := by
    intro z w he
    have hz := (hfdiv z).modEq_zero_nat
    have hw := (hfdiv w).modEq_zero_nat
    rw [he] at hz
    have hn := (hz.trans hw.symm).add_right_cancel' (L + f w + 1)
    have hn' : z.2.val + 1 = w.2.val + 1 :=
      half_residue_inj hp (by omega) (by omega) z.2.isLt w.2.isLt hn
    have h₂ : z.2 = w.2 := Fin.ext (by omega)
    have h₁ : z.1 = w.1 := by
      apply Fin.ext
      change p * z.1.val + offset p (A (z.2.val + 1)) =
        p * w.1.val + offset p (A (w.2.val + 1)) at he
      rw [hn'] at he
      exact Nat.eq_of_mul_eq_mul_left hp.pos (Nat.add_right_cancel he)
    exact Prod.ext h₁ h₂
  have hc := Finset.card_le_card_of_injOn
    (s := (Finset.univ : Finset (Fin (M / p) × Fin K)))
    (t := (Finset.range M).filter
      (fun x => ∃ n, 1 ≤ n ∧ n ≤ K ∧ p ∣ n ^ 2 + n + (L + x + 1))) f
    (by
      intro z _
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hbnd z),
        z.2.val + 1, by omega, z.2.isLt, hfdiv z⟩)
    hinj.injOn
  simpa [K] using hc

private noncomputable def squareClass (L M i : ℕ) : Finset ℕ :=
  (Finset.range M).filter (fun x => (2 * i + 3) ^ 2 ∣ 4 * (L + x) + 3)

private theorem mem_squareClass {L M i x : ℕ} :
    x ∈ squareClass L M i ↔ x < M ∧ (2 * i + 3) ^ 2 ∣ 4 * (L + x) + 3 := by
  simp [squareClass]

private theorem squareClass_card (L M i : ℕ) :
    (squareClass L M i).card ≤ M / (2 * i + 3) ^ 2 + 1 := by
  let q := (2 * i + 3) ^ 2
  have hodd : Odd (2 * i + 3) := ⟨i + 1, by omega⟩
  have hcop : q.Coprime 4 := by
    have h := (Nat.coprime_two_right.mpr hodd).pow 2 2
    simpa [q] using h
  have hc := Finset.card_le_card_of_injOn
    (s := squareClass L M i) (t := Finset.range (M / q + 1)) (fun x => x / q)
    (by
      intro x hx
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le
        (Nat.div_le_div_right (Nat.le_of_lt (mem_squareClass.mp hx).1))))
    (by
      intro x hx y hy hxy
      have hx' : q ∣ 4 * (L + x) + 3 := (mem_squareClass.mp hx).2
      have hy' : q ∣ 4 * (L + y) + 3 := (mem_squareClass.mp hy).2
      have he := hx'.modEq_zero_nat.trans hy'.modEq_zero_nat.symm
      have he' : 4 * x ≡ 4 * y [MOD q] := by
        rw [Nat.mul_add, Nat.mul_add] at he
        exact (he.add_right_cancel' 3).add_left_cancel' (4 * L)
      have hmod : x ≡ y [MOD q] := by
        rcases le_total x y with h | h
        · apply (Nat.modEq_iff_dvd' h).mpr
          have hd := (Nat.modEq_iff_dvd' (Nat.mul_le_mul_left 4 h)).mp he'
          rw [← Nat.mul_sub_left_distrib] at hd
          exact hcop.dvd_mul_left.mp hd
        · apply Nat.ModEq.symm
          apply (Nat.modEq_iff_dvd' h).mpr
          have hd := (Nat.modEq_iff_dvd' (Nat.mul_le_mul_left 4 h)).mp he'.symm
          rw [← Nat.mul_sub_left_distrib] at hd
          exact hcop.dvd_mul_left.mp hd
      exact (Nat.ext_div_modEq_iff q x y).mpr ⟨hxy, hmod⟩)
  simpa [q] using hc

private theorem reciprocal_step (i : ℕ) :
    1 / ((2 * (i : ℝ) + 3) ^ 2) ≤
      1 / 4 * (1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)) := by
  have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
  have ha : 0 < (i : ℝ) + 1 := by linarith
  have hb : 0 < (i : ℝ) + 2 := by linarith
  have hden : 0 < 4 * ((i : ℝ) + 1) * ((i : ℝ) + 2) := by positivity
  have he : 1 / 4 * (1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)) =
      1 / (4 * ((i : ℝ) + 1) * ((i : ℝ) + 2)) := by
    field_simp [ha.ne', hb.ne']
    ring
  rw [he]
  apply (div_le_div_iff₀ (by positivity) hden).2
  nlinarith

private theorem reciprocal_sum (S : ℕ) :
    (∑ i ∈ Finset.range S, 1 / ((2 * (i : ℝ) + 3) ^ 2)) ≤
      1 / 4 * (1 - 1 / ((S : ℝ) + 1)) := by
  induction S with
  | zero => norm_num
  | succ S ih =>
    rw [Finset.sum_range_succ]
    have hs := reciprocal_step S
    rw [Nat.cast_succ, show (S : ℝ) + 1 + 1 = (S : ℝ) + 2 by ring]
    linarith

private theorem sieve_count (L M S : ℕ) :
    (((Finset.range S).biUnion (squareClass L M)).card : ℝ) ≤ (M : ℝ) / 4 + S := by
  classical
  have hsum : (∑ i ∈ Finset.range S, 1 / ((2 * (i : ℝ) + 3) ^ 2)) ≤ 1 / 4 := by
    have hz : 0 ≤ 1 / ((S : ℝ) + 1) := by positivity
    linarith [reciprocal_sum S]
  calc
    _ ≤ ∑ i ∈ Finset.range S, ((squareClass L M i).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := Finset.range S) (t := squareClass L M))
    _ ≤ ∑ i ∈ Finset.range S, ((M : ℝ) * (1 / ((2 * (i : ℝ) + 3) ^ 2)) + 1) := by
      apply Finset.sum_le_sum
      intro i _
      let q := (2 * i + 3) ^ 2
      have hpos : 0 < (q : ℝ) := by dsimp [q]; positivity
      have hn : q * (M / q) ≤ M := by
        have := Nat.div_add_mod M q
        omega
      have hr : (q : ℝ) * ((M / q : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hn
      have hd : ((M / q : ℕ) : ℝ) ≤ (M : ℝ) / q :=
        (le_div_iff₀ hpos).2 (by simpa [mul_comm] using hr)
      have hc : ((squareClass L M i).card : ℝ) ≤ ((M / q : ℕ) : ℝ) + 1 := by
        exact_mod_cast squareClass_card L M i
      have hq : (q : ℝ) = (2 * (i : ℝ) + 3) ^ 2 := by
        dsimp [q]
        push_cast <;> rfl
      calc
        _ ≤ (M : ℝ) / q + 1 := hc.trans (add_le_add hd le_rfl)
        _ = _ := by rw [hq, div_eq_mul_one_div]
    _ = (M : ℝ) * (∑ i ∈ Finset.range S, 1 / ((2 * (i : ℝ) + 3) ^ 2)) + S := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg M)
      linarith

private theorem squarefree_of_survives {L M S Y x : ℕ}
    (hx : x < M) (hd : 4 * (L + x) + 3 ≤ Y) (hs : S = Nat.sqrt Y)
    (hx' : x ∉ (Finset.range S).biUnion (squareClass L M)) :
    Squarefree (4 * (L + x) + 3) := by
  apply Nat.squarefree_iff_prime_squarefree.mpr
  intro r hr hdiv
  have hrY : r ^ 2 ≤ Y :=
    (Nat.le_of_dvd (by omega) (show r ^ 2 ∣ 4 * (L + x) + 3 by simpa [pow_two] using hdiv)).trans hd
  have hrS : r ≤ S := by rw [hs]; exact Nat.le_sqrt'.mpr hrY
  have hne : r ≠ 2 := by
    intro he
    subst r
    obtain ⟨a, ha⟩ := hdiv
    omega
  obtain ⟨k, hk⟩ := hr.odd_of_ne_two hne
  let i := k - 1
  have hi : 2 * i + 3 = r := by
    have := hr.two_le
    dsimp [i]
    omega
  exact hx' (Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr (by omega),
    mem_squareClass.mpr ⟨hx, by simpa only [hi, pow_two] using hdiv⟩⟩)

theorem positive_proportion :
    ∃ (θ α : ℝ) (r : ℕ) (c : ℝ), 0 < θ ∧ 0 < α ∧ 0 < c ∧ ∃ Y₀ : ℕ, ∀ Y ≥ Y₀,
    c * ({d : ℕ | d ≤ Y ∧ Admissible d}.ncard : ℝ) ≤
      ({d : ℕ | d ≤ Y ∧ Admissible d ∧ Good θ α r d}.ncard : ℝ) := by
  classical
  refine ⟨1, 1 / 2, 0, 1 / 128, by norm_num, by norm_num, by norm_num, 1000000, ?_⟩
  intro Y hY
  let S := Nat.sqrt Y
  let L := (Y + 1) / 8
  let U := (Y + 1) / 4
  let M := U - L
  have hS : 1000 ≤ S := Nat.le_sqrt'.mpr (by norm_num <;> exact hY)
  have hSq : S ^ 2 ≤ Y := Nat.sqrt_le' Y
  have hSl : 1000 * S ≤ Y := by
    have h := Nat.mul_le_mul_right S hS
    rw [← pow_two] at h
    exact h.trans hSq
  have hM : Y ≤ 8 * M + 8 := by dsimp [M, U, L]; omega
  obtain ⟨p, hp, hSp, hpS⟩ := Nat.bertrand S (by omega)
  let K := (p - 1) / 2
  let C := (Finset.range M).filter
    (fun x => ∃ n, 1 ≤ n ∧ n ≤ K ∧ p ∣ n ^ 2 + n + (L + x + 1))
  let B := (Finset.range S).biUnion (squareClass L M)
  let G := C \ B
  have hKC : (M / p) * K ≤ C.card := block_count L M p hp
  have hKp : 7 * p ≤ 16 * K := by dsimp [K]; omega
  have hblocks : 7 * (p * (M / p)) ≤ 16 * C.card := by
    calc
      _ ≤ 16 * ((M / p) * K) := by
        simpa only [mul_assoc, mul_comm K (M / p)] using
          Nat.mul_le_mul_right (M / p) hKp
      _ ≤ _ := Nat.mul_le_mul_left 16 hKC
  have hC : 7 * M ≤ 16 * C.card + 16 * S := by
    have hsplit := Nat.div_add_mod M p
    have hr := Nat.mod_lt M hp.pos
    omega
  have hB : (B.card : ℝ) ≤ (M : ℝ) / 4 + S := sieve_count L M S
  have hG : C.card ≤ G.card + B.card := Finset.card_le_card_sdiff_add_card
  let D := (Finset.range (Y + 1)).filter (fun d => Admissible d ∧ Good 1 (1 / 2) 0 d)
  have hGD : G.card ≤ D.card := by
    apply Finset.card_le_card_of_injOn (fun x : ℕ => 4 * (L + x) + 3)
    · intro x hx
      have hxc := (Finset.mem_sdiff.mp hx).1
      have hxb := (Finset.mem_sdiff.mp hx).2
      obtain ⟨hxM, n, hn, hnK, hdiv⟩ := Finset.mem_filter.mp hxc
      have hxlt := Finset.mem_range.mp hxM
      let d := 4 * (L + x) + 3
      have hdY : d ≤ Y := by dsimp [d, M, U] at *; omega
      have hdhalf : Y ≤ 2 * d := by dsimp [d, L]; omega
      have hnd : n ≤ d := by
        have hnS : n ≤ S := by dsimp [K] at hnK; omega
        omega
      have hquot : (d + 1) / 4 = L + x + 1 := by dsimp [d]; omega
      have hpY : Y < p ^ 2 := Nat.sqrt_lt'.mp hSp
      have hadm : Admissible d := ⟨by dsimp [d]; omega,
        squarefree_of_survives hxlt hdY rfl hxb⟩
      have hg : Good 1 (1 / 2) 0 d := by
        refine ⟨n, hn, ?_, Or.inr ⟨p, hp, ?_, ?_⟩⟩
        · rw [Real.rpow_one]
          exact_mod_cast hnd
        · rwa [hquot]
        · rw [← Real.sqrt_eq_rpow]
          apply (Real.sqrt_lt (Nat.cast_nonneg d) (Nat.cast_nonneg p)).2
          exact_mod_cast (hdY.trans_lt hpY)
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hdY), hadm, hg⟩
    · intro x _ y _ h
      change 4 * (L + x) + 3 = 4 * (L + y) + 3 at h
      omega
  have hDeq : (D : Set ℕ) = {d : ℕ | d ≤ Y ∧ Admissible d ∧ Good 1 (1 / 2) 0 d} := by
    ext d
    simp [D]
  have hA : {d : ℕ | d ≤ Y ∧ Admissible d}.ncard ≤ Y + 1 := by
    rw [← Set.ncard_Iic_nat]
    exact Set.ncard_le_ncard (t := Set.Iic Y) (fun _ h => h.1) (Set.finite_Iic Y)
  rw [← hDeq, Set.ncard_coe_finset]
  have hYr : (1000000 : ℝ) ≤ Y := by exact_mod_cast hY
  have hMr : (Y : ℝ) ≤ 8 * (M : ℝ) + 8 := by exact_mod_cast hM
  have hSr : 1000 * (S : ℝ) ≤ Y := by exact_mod_cast hSl
  have hCr : 7 * (M : ℝ) ≤ 16 * (C.card : ℝ) + 16 * (S : ℝ) := by exact_mod_cast hC
  have hGr : (C.card : ℝ) ≤ (G.card : ℝ) + B.card := by exact_mod_cast hG
  have hDr : (G.card : ℝ) ≤ D.card := by exact_mod_cast hGD
  have hAr : ({d : ℕ | d ≤ Y ∧ Admissible d}.ncard : ℝ) ≤ (Y : ℝ) + 1 := by
    exact_mod_cast hA
  have hcount : (Y : ℝ) / 64 ≤ (D.card : ℝ) := by
    linarith only [hYr, hMr, hSr, hCr, hGr, hDr, hB]
  linarith only [hcount, hAr, hYr]

end OMA.MO515446Proof

theorem OMA.solution : type_of% @OMA.S_mo_515446.main :=
  OMA.MO515446Proof.positive_proportion

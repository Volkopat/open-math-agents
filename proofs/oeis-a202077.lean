import OMAStatements.S_oeis_a202077

/-!
A proof of Colin Barker's generating function for OEIS A202077.
Adjacent sums are odd and the total is zero, so exactly the second and fourth
entries are odd. Translate and halve all five entries to obtain a bounded
weak composition. Inclusion-exclusion gives one quartic for each parity of
the bound, and finite differences determine the generating function.
-/

namespace OMA.A202077

def box (d : Fin 5 → ℕ) (s : ℕ) : ℕ :=
  ((Finset.Nat.antidiagonalTuple 5 s).filter (fun v => ∀ i, v i < d i)).card

def widths (u v : ℕ) : Fin 5 → ℕ := ![u,v,u,v,u]

end OMA.A202077

namespace OMA.A202077

open OMA.S_oeis_a202077

private theorem entry_parity (v : Fin 5 → ℤ) (hs : ∑ i, v i = 0)
    (ho : ∀ i : Fin 4, Odd (v i.castSucc + v i.succ)) :
    ∀ i, v i % 2 = (i.val : ℤ) % 2 := by
  obtain ⟨t₀, h₀⟩ := ho 0
  obtain ⟨t₁, h₁⟩ := ho 1
  obtain ⟨t₂, h₂⟩ := ho 2
  obtain ⟨t₃, h₃⟩ := ho 3
  change v 0 + v 1 = 2*t₀+1 at h₀
  change v 1 + v 2 = 2*t₁+1 at h₁
  change v 2 + v 3 = 2*t₂+1 at h₂
  change v 3 + v 4 = 2*t₃+1 at h₃
  have hsum : v 0 + (v 1 + (v 2 + (v 3 + v 4))) = 0 := by
    simpa [Fin.sum_univ_succ] using hs
  intro i
  fin_cases i
  · change v 0 % 2 = 0
    omega
  · change v 1 % 2 = 1
    omega
  · change v 2 % 2 = 0
    omega
  · change v 3 % 2 = 1
    omega
  · change v 4 % 2 = 0
    omega

private def offset (n : ℕ) (i : Fin 5) : ℤ := ((n : ℤ) + i.val) % 2

private def decode (n : ℕ) (f : Fin 5 → ℕ) (i : Fin 5) : ℤ :=
  2 * (f i : ℤ) - n + offset n i

private theorem decode_sum (n : ℕ) (f : Fin 5 → ℕ) :
    ∑ i, decode n f i = 2 * (∑ i, f i : ℕ) - 5 * (n : ℤ) + ∑ i, offset n i := by
  simp [decode, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

private theorem decode_odd (n : ℕ) (f : Fin 5 → ℕ) (i : Fin 4) :
    Odd (decode n f i.castSucc + decode n f i.succ) := by
  refine ⟨(decode n f i.castSucc + decode n f i.succ) / 2, ?_⟩
  simp only [decode, offset, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
  omega

private theorem affine_box (n s : ℕ) (d : Fin 5 → ℕ)
    (hd : ∀ i, (d i : ℤ) = n + 1 - offset n i)
    (hs : 2*(s : ℤ) = 5*n - ∑ i, offset n i) : a n = box d s := by
  unfold a box
  symm
  apply Finset.card_bij (fun f _ => decode n f)
  · intro f hf
    obtain ⟨hf₁, hf₂⟩ := Finset.mem_filter.mp hf
    rw [Finset.Nat.mem_antidiagonalTuple] at hf₁
    apply Finset.mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr ?_, ?_, decode_odd n f⟩
    · intro i
      have hb := hf₂ i
      have he := hd i
      rw [Finset.mem_Icc]
      unfold decode offset at *
      omega
    · rw [decode_sum, hf₁]
      omega
  · intro f _ g _ h
    funext i
    have h' := congrFun h i
    unfold decode at h'
    omega
  · intro v hv
    obtain ⟨hv₁, hv₂, hv₃⟩ := Finset.mem_filter.mp hv
    have bounds (i : Fin 5) := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hv₁ i)
    have hp := entry_parity v hv₂ hv₃
    let f (i : Fin 5) : ℕ := ((v i + n - offset n i) / 2).toNat
    have hinv : decode n f = v := by
      funext i
      have hi := bounds i
      have he := hp i
      simp only [decode, f, offset]
      omega
    refine ⟨f, Finset.mem_filter.mpr ⟨Finset.Nat.mem_antidiagonalTuple.mpr ?_, ?_⟩, hinv⟩
    · have h := decode_sum n f
      rw [hinv, hv₂] at h
      omega
    · intro i
      have hi := bounds i
      have he := hd i
      have hz := congrFun hinv i
      unfold decode offset at *
      omega

theorem even_box (m : ℕ) : a (2*m) = box (widths (2*m+1) (2*m)) (5*m-1) := by
  cases m with
  | zero =>
    change a 0 = box (widths 1 0) 0
    have ha : a 0 = 0 := by
      unfold a
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v h
      obtain ⟨hv, _, ho⟩ := Finset.mem_filter.mp h
      have h₀ := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hv 0)
      have h₁ := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hv 1)
      obtain ⟨k, hk⟩ := ho 0
      change v 0 + v 1 = 2*k+1 at hk
      omega
    rw [ha]
    symm
    unfold box
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v h
    exact Nat.not_lt_zero _ ((Finset.mem_filter.mp h).2 1)
  | succ m =>
    apply affine_box
    · intro i
      fin_cases i <;> simp [offset, widths]
    · simp [offset, Fin.sum_univ_succ]
      omega

theorem odd_box (m : ℕ) : a (2*m+1) = box (widths (2*m+1) (2*m+2)) (5*m+1) := by
  apply affine_box
  · intro i
    fin_cases i <;> simp [offset, widths] <;> omega
  · simp [offset, Fin.sum_univ_succ]
    omega

end OMA.A202077

namespace OMA.A202077

open Finset

private theorem tuple_count (s : ℕ) :
    (Finset.Nat.antidiagonalTuple 5 s).card = (s + 4).choose 4 := by
  have h := Finset.card_finsuppAntidiag_nat_eq_choose (s := (univ : Finset (Fin 5))) s
  simp only [Finset.finsuppAntidiag, card_map, card_attach,
    piAntidiag_univ_fin_eq_antidiagonalTuple, card_univ, Fintype.card_fin] at h
  rw [h, show 5 + s - 1 = s + 4 by omega, ← Nat.choose_symm (show 4 ≤ s+4 by omega)]
  simp

private theorem shifted_count (d : Fin 5 → ℕ) (s : ℕ) (T : Finset (Fin 5)) :
    ((Finset.Nat.antidiagonalTuple 5 s).filter (fun v => ∀ i ∈ T, d i ≤ v i)).card =
      if ∑ i ∈ T, d i ≤ s then (s - ∑ i ∈ T, d i + 4).choose 4 else 0 := by
  classical
  let off (i : Fin 5) := if i ∈ T then d i else 0
  have hsum : ∑ i, off i = ∑ i ∈ T, d i := by simp [off]
  have hle (v : Fin 5 → ℕ) : (∀ i ∈ T, d i ≤ v i) ↔ ∀ i, off i ≤ v i := by
    constructor
    · intro h i
      by_cases hi : i ∈ T <;> simp [off, hi, h]
    · intro h i hi
      simpa [off, hi] using h i
  split_ifs with h
  · rw [← tuple_count]
    symm
    apply Finset.card_bij (fun v _ i => v i + off i)
    · intro v hv
      rw [mem_filter, Finset.Nat.mem_antidiagonalTuple, hle, sum_add_distrib, hsum]
      rw [Finset.Nat.mem_antidiagonalTuple] at hv
      exact ⟨by omega, fun i => Nat.le_add_left _ _⟩
    · intro v _ w _ he
      funext i
      exact Nat.add_right_cancel (congrFun he i)
    · intro w hw
      rw [mem_filter, Finset.Nat.mem_antidiagonalTuple, hle] at hw
      refine ⟨fun i => w i - off i, ?_, funext fun i => Nat.sub_add_cancel (hw.2 i)⟩
      rw [Finset.Nat.mem_antidiagonalTuple, Finset.sum_tsub_distrib univ (fun i _ => hw.2 i),
        hw.1, hsum]
  · apply card_eq_zero.mpr
    apply eq_empty_of_forall_notMem
    intro w hw
    rw [mem_filter, Finset.Nat.mem_antidiagonalTuple, hle] at hw
    exact h (hsum ▸ hw.1 ▸ Finset.sum_le_sum (fun i _ => hw.2 i))

theorem box_ie (d : Fin 5 → ℕ) (s : ℕ) : (box d s : ℤ) =
    ∑ T : Finset (Fin 5), (-1 : ℤ)^T.card *
      (if ∑ i ∈ T, d i ≤ s then (((s - ∑ i ∈ T, d i + 4).choose 4 : ℕ) : ℤ) else 0) := by
  classical
  let A := Finset.Nat.antidiagonalTuple 5 s
  let bad (v : Fin 5 → ℕ) := univ.filter (fun i => d i ≤ v i)
  have good (v : Fin 5 → ℕ) : (∀ i, v i < d i) ↔ bad v = ∅ := by
    simp [bad, Finset.filter_eq_empty_iff, not_le]
  have lower (T : Finset (Fin 5)) (v : Fin 5 → ℕ) :
      (∀ i ∈ T, d i ≤ v i) ↔ T ∈ (bad v).powerset := by
    simp [bad, Finset.subset_iff]
  have weight (v : Fin 5 → ℕ) : (if ∀ i, v i < d i then (1 : ℤ) else 0) =
      ∑ T : Finset (Fin 5), (if ∀ i ∈ T, d i ≤ v i then (-1 : ℤ)^T.card else 0) := by
    simp_rw [lower, good]
    rw [sum_ite_mem, univ_inter, Finset.sum_powerset_neg_one_pow_card]
  change ((A.filter (fun v => ∀ i, v i < d i)).card : ℤ) = _
  rw [← Finset.sum_boole]
  simp_rw [weight]
  rw [sum_comm]
  apply sum_congr rfl
  intro T _
  have h := congrArg (fun x : ℕ => (x : ℤ)) (shifted_count d s T)
  simp only [Nat.cast_ite, Nat.cast_zero] at h
  rw [← h, ← Finset.sum_boole, mul_sum]
  apply sum_congr rfl
  intro v _
  split_ifs <;> simp

end OMA.A202077

namespace OMA.A202077

open Finset

private def cut (s t : ℕ) : ℤ :=
  if t ≤ s then ((s - t + 4).choose 4 : ℕ) else 0

private def grouped (f : ℕ → ℤ) (u v : ℕ) : ℤ :=
  f 0 - 3*f u - 2*f v + 3*f (2*u) + 6*f (u+v) + f (2*v) -
  f (3*u) - 6*f (2*u+v) - 3*f (u+2*v) + 2*f (3*u+v) + 3*f (2*u+2*v) - f (3*u+2*v)

set_option maxHeartbeats 1000000 in
private theorem collect (f : ℕ → ℤ) (u v : ℕ) :
    (∑ T : Finset (Fin 5), (-1 : ℤ)^T.card * f (∑ i ∈ T, widths u v i)) =
      grouped f u v := by
  change (∑ T ∈ (univ : Finset (Fin 5)).powerset, _) = _
  rw [show (univ : Finset (Fin 5)) = insert 0 (insert 1 (insert 2 (insert 3 (insert 4 ∅)))) by decide]
  simp (disch := decide) only [sum_powerset_insert, powerset_empty, sum_singleton,
    sum_insert, sum_empty, card_insert_of_notMem, card_empty]
  simp only [show widths u v 0 = u from rfl, show widths u v 1 = v from rfl,
    show widths u v 2 = u from rfl, show widths u v 3 = v from rfl, show widths u v 4 = u from rfl]
  norm_num [grouped]
  ring_nf

private def simplex (x : ℚ) : ℚ := (x+1)*(x+2)*(x+3)*(x+4)/24

private theorem cut_small (s t : ℕ) (h : t ≤ s) : (cut s t : ℚ) = simplex ((s : ℚ) - t) := by
  have hc := Nat.descFactorial_eq_factorial_mul_choose (s-t+4) 4
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, mul_one] at hc
  norm_num [Nat.factorial] at hc
  unfold cut simplex
  rw [if_pos h]
  push_cast
  have hn : (s-t+1)*(s-t+2)*(s-t+3)*(s-t+4) = 24*(s-t+4).choose 4 := by
    simpa [Nat.add_assoc, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hc
  have hz := congrArg (fun k : ℕ => (k : ℚ)) hn
  push_cast [Nat.cast_sub h] at hz
  linarith

private theorem cut_large (s t : ℕ) (h : s < t) : (cut s t : ℚ) = 0 := by
  simp [cut, Nat.not_le.mpr h]

private theorem grouped_large (s u v : ℕ)
    (hu : 2*u ≤ s) (hv : 2*v ≤ s) (lu : s < 3*u) (lv : s < 3*v) :
    (grouped (cut s) u v : ℚ) = simplex s - 3*simplex ((s : ℚ)-u) -
      2*simplex ((s : ℚ)-v) + 3*simplex ((s : ℚ)-2*u) +
      6*simplex ((s : ℚ)-(u+v)) + simplex ((s : ℚ)-2*v) := by
  unfold grouped
  push_cast
  simp (disch := omega) only [cut_small, cut_large]
  push_cast
  ring

theorem evaluate_boxes
    (h : ∀ d s, (box d s : ℤ) = ∑ T : Finset (Fin 5), (-1 : ℤ)^T.card *
      (if ∑ i ∈ T, d i ≤ s then (((s - ∑ i ∈ T, d i + 4).choose 4 : ℕ) : ℤ) else 0)) :
    (∀ m : ℕ, 384 * (box (widths (2*m+1) (2*m)) (5*m-1) : ℚ) =
      230*(2*(m:ℚ))^4 + 552*(2*(m:ℚ))^3 + 424*(2*(m:ℚ))^2 + 96*(2*(m:ℚ))) ∧
    (∀ m : ℕ, 384 * (box (widths (2*m+1) (2*m+2)) (5*m+1) : ℚ) =
      230*(2*(m:ℚ)+1)^4 + 368*(2*(m:ℚ)+1)^3 + 148*(2*(m:ℚ)+1)^2 +
        16*(2*(m:ℚ)+1) + 6) := by
  have hg (s u v : ℕ) : (box (widths u v) s : ℚ) = (grouped (cut s) u v : ℚ) := by
    exact_mod_cast (h (widths u v) s).trans (collect (cut s) u v)
  constructor <;> intro m <;> rw [hg] <;> by_cases hm : m < 3
  · interval_cases m <;> norm_num [grouped, cut, Nat.choose]
  · rw [grouped_large _ _ _ (by omega) (by omega) (by omega) (by omega)]
    push_cast [Nat.cast_sub (show 1 ≤ 5*m by omega)]
    unfold simplex
    ring
  · interval_cases m <;> norm_num [grouped, cut, Nat.choose]
  · rw [grouped_large _ _ _ (by omega) (by omega) (by omega) (by omega)]
    push_cast
    unfold simplex
    ring

end OMA.A202077

namespace OMA.A202077

open PowerSeries S_oeis_a202077

lemma series_of_quartics
    (he : ∀ m : ℕ, 384 * (a (2*m) : ℚ) =
      230*(2*(m:ℚ))^4 + 552*(2*(m:ℚ))^3 + 424*(2*(m:ℚ))^2 + 96*(2*(m:ℚ)))
    (ho : ∀ m : ℕ, 384 * (a (2*m+1) : ℚ) =
      230*(2*(m:ℚ)+1)^4 + 368*(2*(m:ℚ)+1)^3 + 148*(2*(m:ℚ)+1)^2 +
      16*(2*(m:ℚ)+1)+6) : type_of% @S_oeis_a202077.main := by
  let E (x : ℚ) := (230*x^4 + 552*x^3 + 424*x^2 + 96*x) / 384
  let O (x : ℚ) := (230*x^4 + 368*x^3 + 148*x^2 + 16*x + 6) / 384
  have values (n : ℕ) : (a n : ℚ) = if n % 2 = 0 then E n else O n := by
    by_cases hn : n % 2 = 0
    · rw [if_pos hn]
      have h := he (n/2)
      have hnat : 2 * (n/2) = n := by omega
      have hrat : 2 * ((n/2 : ℕ) : ℚ) = n := by exact_mod_cast hnat
      rw [hnat, hrat] at h
      dsimp [E]
      linarith only [h]
    · rw [if_neg hn]
      have h := ho (n/2)
      have hnat : 2 * (n/2) + 1 = n := by omega
      have hrat : 2 * ((n/2 : ℕ) : ℚ) + 1 = n := by exact_mod_cast hnat
      rw [hnat, hrat] at h
      dsimp [O]
      linarith only [h]
  let F := PowerSeries.mk (fun n => (a n : ℚ))
  change F * ((1 - X)^5 * (1 + X)^4) = _
  have leftPoly : F * ((1 - X)^5 * (1 + X)^4) =
      F - F*X^1 - C (4:ℚ)*(F*X^2) + C (4:ℚ)*(F*X^3) +
      C (6:ℚ)*(F*X^4) - C (6:ℚ)*(F*X^5) - C (4:ℚ)*(F*X^6) +
      C (4:ℚ)*(F*X^7) + F*X^8 - F*X^9 := by simp only [map_ofNat]; ring
  have rightPoly : 2*X*(1 + 12*X + 22*X^2 + 45*X^3 + 22*X^4 + 12*X^5 + X^6) =
      C (2:ℚ)*X^1 + C (24:ℚ)*X^2 + C (44:ℚ)*X^3 + C (90:ℚ)*X^4 +
      C (44:ℚ)*X^5 + C (24:ℚ)*X^6 + C (2:ℚ)*X^7 := by simp only [map_ofNat]; ring
  rw [leftPoly, rightPoly]
  ext n
  simp only [map_add, map_sub, coeff_C_mul]
  simp only [coeff_X_pow, coeff_mul_X_pow', F, coeff_mk, values]
  by_cases hn : n < 9
  · interval_cases n <;> norm_num [E, O]
  · have cast_diff (k : ℕ) (hk : k ≤ n) : ((n-k : ℕ) : ℚ) = (n:ℚ) - k := Nat.cast_sub hk
    by_cases parity : n % 2 = 0 <;>
      simp (disch := omega) only [if_pos, if_neg] <;>
      simp (disch := omega) only [cast_diff, Nat.cast_ofNat, E, O] <;> ring

end OMA.A202077

open OMA.A202077 in
theorem OMA.solution : type_of% @OMA.S_oeis_a202077.main := by
  obtain ⟨he, ho⟩ := evaluate_boxes box_ie
  apply series_of_quartics
  · intro m
    rw [even_box]
    exact he m
  · intro m
    rw [odd_box]
    exact ho m

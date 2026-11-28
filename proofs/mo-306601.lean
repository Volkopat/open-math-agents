import OMAStatements.S_mo_306601
import Mathlib

namespace OMA.S_mo_306601

open Finset
open scoped BigOperators

private theorem mean_mono {α : Type*} [Fintype α] {f g : α → ℝ}
    (h : ∀ a, f a ≤ g a) : mean f ≤ mean g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => h a) (by positivity)

private theorem mean_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    mean (fun a => f a + g a) = mean f + mean g := by
  simp only [mean, sum_add_distrib, add_div]

private theorem mean_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    mean (fun a => c * f a) = c * mean f := by
  simp only [mean, ← mul_sum, mul_div_assoc]

private theorem mean_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    mean (fun _ : α => c) = c := by
  unfold mean
  rw [sum_const, card_univ, nsmul_eq_mul]
  field_simp

private theorem mean_sum {α ι : Type*} [Fintype α] [Fintype ι]
    (f : α → ι → ℝ) : mean (fun a => ∑ i, f a i) = ∑ i, mean (fun a => f a i) := by
  simp only [mean, ← sum_div]
  rw [Finset.sum_comm]

private theorem mean_equiv {α : Type*} [Fintype α] (e : α ≃ α) (f : α → ℝ) :
    mean (fun a => f (e a)) = mean f := by
  unfold mean
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

private theorem mean_bool (f : Bool → ℝ) : mean f = (f false + f true)/2 := by
  simp [mean, add_comm]

private theorem mean_prod {α β : Type*} [Fintype α] [Fintype β] (f : α × β → ℝ) :
    mean f = mean (fun a => mean (fun b => f (a, b))) := by
  simp only [mean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul, ← sum_div, div_div]
  rw [mul_comm (Fintype.card α : ℝ)]

private theorem prod_average (m : ℕ) (f : Fin m → Bool → ℝ) :
    mean (fun q : Fin m → Bool => ∏ i, f i (q i)) =
      ∏ i, (f i false + f i true)/2 := by
  unfold mean
  rw [← Fintype.prod_sum]
  simp only [Fintype.sum_bool, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow,
    Nat.cast_ofNat, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, add_comm]

private def flip {m : ℕ} (t s : Sample m) : Sample m :=
  (xor s.1 t.1, fun i => xor (s.2 i) (t.2 i))

private theorem xor_twice (a b : Bool) : xor (xor a b) b = a := by decide +revert

private def flipEquiv {m : ℕ} (t : Sample m) : Sample m ≃ Sample m :=
  { toFun := flip t
    invFun := flip t
    left_inv := fun _ => Prod.ext (xor_twice _ _) (funext fun _ => xor_twice _ _)
    right_inv := fun _ => Prod.ext (xor_twice _ _) (funext fun _ => xor_twice _ _) }

private theorem draw_flip {m : ℕ} (s t : Sample m) (i : Fin m × Bool) :
    draw (flip t s) i = xor (draw s i) (draw t i) := by
  change xor (xor (s.2 i.1) (t.2 i.1)) (xor s.1 t.1 && i.2) = _
  unfold draw
  generalize s.2 i.1 = a
  generalize t.2 i.1 = b
  generalize s.1 = c
  generalize t.1 = d
  generalize i.2 = e
  decide +revert

private theorem uniform_coordinates {m k : ℕ} (coords : Fin k → Fin m × Bool)
    (hsurj : Function.Surjective (fun s : Sample m => fun j => draw s (coords j)))
    (v : Fin k → Bool) :
    prob (fun s : Sample m => (fun j => draw s (coords j)) = v) = 1/(2:ℝ)^k := by
  classical
  let A (v : Fin k → Bool) := prob (fun s : Sample m => (fun j => draw s (coords j)) = v)
  have heq (w : Fin k → Bool) : A w = A v := by
    obtain ⟨t, ht⟩ := hsurj (fun j => xor (v j) (w j))
    have htj (j : Fin k) : draw t (coords j) = xor (v j) (w j) := congrFun ht j
    have hflip (s : Sample m) :
        (fun j => draw (flipEquiv t s) (coords j)) = w ↔ (fun j => draw s (coords j)) = v := by
      constructor
      · intro h
        funext j
        have hh := congrFun h j
        change draw (flip t s) (coords j) = w j at hh
        rw [draw_flip, htj j] at hh
        generalize draw s (coords j) = a at hh ⊢
        generalize v j = b at hh ⊢
        generalize w j = c at hh
        cases a <;> cases b <;> cases c <;> simp_all
      · intro h
        funext j
        change draw (flip t s) (coords j) = w j
        have hj : draw s (coords j) = v j := congrFun h j
        rw [draw_flip, htj j, hj]
        generalize v j = b
        generalize w j = c
        decide +revert
    dsimp only [A, prob]
    rw [← mean_equiv (flipEquiv t)]
    simp only [hflip]
    congr 1
    funext s
    by_cases h : (fun j => draw s (coords j)) = v <;> simp [h]
  have htotal : (∑ w : Fin k → Bool, A w) = 1 := by
    dsimp only [A, prob]
    rw [← mean_sum]
    have ht (s : Sample m) :
        (∑ w : Fin k → Bool, @ite ℝ ((fun j => draw s (coords j)) = w)
          (Classical.propDecidable _) 1 0) = 1 := by
      rw [Finset.sum_eq_single (fun j => draw s (coords j))]
      · simp
      · intro w _ hw
        simp [Ne.symm hw]
      · simp
    simp only [ht, mean_const]
  simp only [heq, Finset.sum_const, card_univ, nsmul_eq_mul, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat] at htotal
  change A v = _
  apply (eq_div_iff (by positivity : (2:ℝ)^k ≠ 0)).mpr
  linarith

private theorem one_value {m : ℕ} (i : Fin m × Bool) (a : Bool) :
    ∃ s : Sample m, draw s i = a := by
  exact ⟨(false, fun _ => a), by cases a <;> cases i.2 <;> rfl⟩

private theorem opposite_second {m : ℕ} {i j : Fin m × Bool} (hij : i ≠ j) (h : i.1 = j.1) :
    i.2 ≠ j.2 := fun h' => hij (Prod.ext h h')

private theorem duplicate_draw (a b c d : Bool) (h : c ≠ d) :
    xor (xor a (xor a b && c)) (xor a b && d) = b := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

private theorem two_values {m : ℕ} (i j : Fin m × Bool) (hij : i ≠ j) (a b : Bool) :
    ∃ s : Sample m, draw s i = a ∧ draw s j = b := by
  classical
  by_cases h : i.1 = j.1
  · refine ⟨(xor a b, fun _ => xor a (xor a b && i.2)), ?_, ?_⟩
    · exact xor_twice _ _
    · exact duplicate_draw a b _ _ (opposite_second hij h)
  · refine ⟨(false, fun r => if r = i.1 then a else b), ?_, ?_⟩
    · simp [draw]
    · simp [draw, Ne.symm h]

private theorem triple_duplicate {m : ℕ} (i j k : Fin m × Bool) (hij : i ≠ j)
    (h : i.1 = j.1) (hk : i.1 ≠ k.1) (a b c : Bool) :
    ∃ s : Sample m, draw s i = a ∧ draw s j = b ∧ draw s k = c := by
  let d := xor a b
  refine ⟨(d, fun r => if r = i.1 then xor a (d && i.2) else xor c (d && k.2)), ?_, ?_, ?_⟩
  · simp only [draw]
    exact xor_twice _ _
  · simp only [draw, if_pos h.symm]
    exact duplicate_draw a b _ _ (opposite_second hij h)
  · simp only [draw, if_neg hk.symm]
    exact xor_twice _ _

private theorem three_values {m : ℕ} (i j k : Fin m × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (a b c : Bool) :
    ∃ s : Sample m, draw s i = a ∧ draw s j = b ∧ draw s k = c := by
  by_cases h : i.1 = j.1
  · have hk : i.1 ≠ k.1 := by
      intro he
      have hi := opposite_second hij h
      have hj := opposite_second hik he
      have hk := opposite_second hjk (h.symm.trans he)
      generalize i.2 = bi at hi hj
      generalize j.2 = bj at hi hk
      generalize k.2 = bk at hj hk
      cases bi <;> cases bj <;> cases bk <;> simp_all
    exact triple_duplicate i j k hij h hk a b c
  · by_cases h' : i.1 = k.1
    · obtain ⟨s, hi, hk, hj⟩ := triple_duplicate i k j hik h' h a c b
      exact ⟨s, hi, hj, hk⟩
    · by_cases h'' : j.1 = k.1
      · obtain ⟨s, hj, hk, hi⟩ := triple_duplicate j k i hjk h'' (Ne.symm h) b c a
        exact ⟨s, hi, hj, hk⟩
      · refine ⟨(false, fun r => if r = i.1 then a else if r = j.1 then b else c), ?_, ?_, ?_⟩
        · simp [draw]
        · simp [draw, Ne.symm h]
        · simp [draw, Ne.symm h', Ne.symm h'']

private theorem one_uniform {m : ℕ} (i : Fin m × Bool) (a : Bool) :
    prob (fun s : Sample m => draw s i = a) = 1/2 := by
  classical
  let coords : Fin 1 → Fin m × Bool := ![i]
  have hsurj : Function.Surjective (fun s : Sample m => fun j => draw s (coords j)) := by
    intro v
    obtain ⟨s, hs⟩ := one_value i (v 0)
    refine ⟨s, ?_⟩
    funext j
    fin_cases j
    exact hs
  have h := uniform_coordinates coords hsurj ![a]
  have he (s : Sample m) : ((fun j => draw s (coords j)) = ![a]) ↔ draw s i = a := by
    constructor
    · exact fun h => congrFun h 0
    · intro h
      funext j
      fin_cases j
      exact h
  simpa only [he, pow_one] using h

private theorem two_uniform {m : ℕ} (i j : Fin m × Bool) (hij : i ≠ j) (a b : Bool) :
    prob (fun s : Sample m => draw s i = a ∧ draw s j = b) = 1/4 := by
  classical
  let coords : Fin 2 → Fin m × Bool := ![i,j]
  have hsurj : Function.Surjective (fun s : Sample m => fun k => draw s (coords k)) := by
    intro v
    obtain ⟨s, hi, hj⟩ := two_values i j hij (v 0) (v 1)
    refine ⟨s, ?_⟩
    funext k
    fin_cases k
    · exact hi
    · exact hj
  have h := uniform_coordinates coords hsurj ![a,b]
  have he (s : Sample m) : ((fun k => draw s (coords k)) = ![a,b]) ↔
      draw s i = a ∧ draw s j = b := by
    constructor
    · exact fun h => ⟨congrFun h 0, congrFun h 1⟩
    · rintro ⟨hi,hj⟩
      funext k
      fin_cases k
      · exact hi
      · exact hj
  norm_num [he] at h ⊢
  exact h

private theorem three_uniform {m : ℕ} (i j k : Fin m × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (a b c : Bool) :
    prob (fun s : Sample m => draw s i = a ∧ draw s j = b ∧ draw s k = c) = 1/8 := by
  classical
  let coords : Fin 3 → Fin m × Bool := ![i,j,k]
  have hsurj : Function.Surjective (fun s : Sample m => fun l => draw s (coords l)) := by
    intro v
    obtain ⟨s, hi, hj, hk⟩ := three_values i j k hij hik hjk (v 0) (v 1) (v 2)
    refine ⟨s, ?_⟩
    funext l
    fin_cases l
    · exact hi
    · exact hj
    · exact hk
  have h := uniform_coordinates coords hsurj ![a,b,c]
  have he (s : Sample m) : ((fun l => draw s (coords l)) = ![a,b,c]) ↔
      draw s i = a ∧ draw s j = b ∧ draw s k = c := by
    constructor
    · exact fun h => ⟨congrFun h 0, congrFun h 1, congrFun h 2⟩
    · rintro ⟨hi,hj,hk⟩
      funext l
      fin_cases l
      · exact hi
      · exact hj
      · exact hk
  norm_num [he] at h ⊢
  exact h

private def pairTerm {m : ℕ} (f : (Fin m × Bool) → Bool → ℝ)
    (b : Bool) (i : Fin m) (q : Bool) : ℝ :=
  f (i,false) q + f (i,true) (xor q b)

private noncomputable def midpoint {m : ℕ} (f : (Fin m × Bool) → Bool → ℝ) (i : Fin m) : ℝ :=
  (f (i,false) false + f (i,false) true + f (i,true) false + f (i,true) true)/2

private theorem pair_midpoint {m : ℕ} (f : (Fin m × Bool) → Bool → ℝ) (b q : Bool) (i : Fin m) :
    pairTerm f b i q + pairTerm f b i (!q) = 2 * midpoint f i := by
  cases b <;> cases q <;> simp [pairTerm, midpoint] <;> ring

private theorem additive_pairs {m : ℕ} (f : (Fin m × Bool) → Bool → ℝ) (s : Sample m) :
    additive f (draw s) = ∑ i, pairTerm f s.1 i (s.2 i) := by
  unfold additive
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro i _
  simp [draw, pairTerm, add_comm]

private theorem additive_mean {m : ℕ} (f : (Fin m × Bool) → Bool → ℝ) :
    mean (fun s : Sample m => additive f (draw s)) = ∑ i, midpoint f i := by
  let e := flipEquiv (false, fun _ : Fin m => true)
  let g (s : Sample m) := additive f (draw s)
  have heq (s : Sample m) : g s + g (e s) = 2 * ∑ i, midpoint f i := by
    dsimp only [g]
    rw [additive_pairs, additive_pairs, ← sum_add_distrib, mul_sum]
    apply sum_congr rfl
    intro i _
    change pairTerm f s.1 i (s.2 i) + pairTerm f (xor s.1 false) i (xor (s.2 i) true) = _
    have hh (q : Bool) : xor q true = !q := by decide +revert
    rw [Bool.xor_false, hh]
    exact pair_midpoint f s.1 (s.2 i) i
  have ha := mean_add g (fun s => g (e s))
  simp only [heq, mean_const, mean_equiv] at ha
  change mean g = _
  linarith

private theorem pair_exp {m : ℕ} (f : (Fin m × Bool) → Bool → ℝ)
    (hf : ∀ i b, f i b ∈ Set.Icc (0:ℝ) 1) (b : Bool) (i : Fin m) (l : ℝ) :
    (Real.exp (l * (pairTerm f b i false - midpoint f i)) +
      Real.exp (l * (pairTerm f b i true - midpoint f i)))/2 ≤ Real.exp (l^2/2) := by
  let x := pairTerm f b i false - midpoint f i
  have hx : pairTerm f b i true - midpoint f i = -x := by
    dsimp [x]
    have h := pair_midpoint f b false i
    change pairTerm f b i false + pairTerm f b i true = _ at h
    linarith
  have hterm (q : Bool) : 0 ≤ pairTerm f b i q ∧ pairTerm f b i q ≤ 2 := by
    unfold pairTerm
    exact ⟨add_nonneg (hf _ _).1 (hf _ _).1, by linarith [(hf (i,false) q).2,
      (hf (i,true) (xor q b)).2]⟩
  have hlo : -1 ≤ x := by dsimp [x] at hx ⊢; linarith [(hterm false).1, (hterm true).2]
  have hhi : x ≤ 1 := by dsimp [x] at hx ⊢; linarith [(hterm false).2, (hterm true).1]
  have hs : x^2 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hhi) (show 0 ≤ 1+x by linarith)]
  change (Real.exp (l*x) + Real.exp (l*(pairTerm f b i true - midpoint f i)))/2 ≤ _
  rw [hx, mul_neg, ← Real.cosh_eq]
  refine (Real.cosh_le_exp_half_sq _).trans (Real.exp_le_exp.mpr ?_)
  rw [mul_pow]
  nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg l)]

private theorem additive_mgf {m : ℕ} (f : (Fin m × Bool) → Bool → ℝ)
    (hf : ∀ i b, f i b ∈ Set.Icc (0:ℝ) 1) (l : ℝ) :
    mean (fun s : Sample m => Real.exp (l * (additive f (draw s) -
      mean (fun q : Sample m => additive f (draw q))))) ≤ Real.exp ((m:ℝ)*(l^2/2)) := by
  rw [mean_prod]
  refine (mean_mono (g := fun _ : Bool => Real.exp ((m:ℝ)*(l^2/2))) ?_).trans_eq (mean_const _)
  intro b
  have he (q : Fin m → Bool) :
      Real.exp (l * (additive f (draw (b,q)) - mean (fun s : Sample m => additive f (draw s)))) =
        ∏ i, Real.exp (l * (pairTerm f b i (q i) - midpoint f i)) := by
    rw [additive_pairs, additive_mean, ← sum_sub_distrib, mul_sum, Real.exp_sum]
  simp only [he]
  rw [prod_average m (fun i q => Real.exp (l * (pairTerm f b i q - midpoint f i)))]
  calc
    _ ≤ ∏ _i : Fin m, Real.exp (l^2/2) := by
      apply Finset.prod_le_prod
      · intro i _
        positivity
      · intro i _
        exact pair_exp f hf b i l
    _ = _ := by simp [← Real.exp_nat_mul]

private theorem exponential_tail {α : Type*} [Fintype α] (D : α → ℝ)
    (t l B : ℝ) (hl : 0 ≤ l) (h : mean (fun a => Real.exp (l*D a)) ≤ Real.exp B) :
    prob (fun a => t ≤ D a) ≤ Real.exp (B-l*t) := by
  classical
  have hm : Real.exp (l*t) * prob (fun a => t ≤ D a) ≤ Real.exp B := by
    change Real.exp (l*t) * mean (fun a => if t ≤ D a then 1 else 0) ≤ _
    rw [← mean_mul]
    refine (mean_mono ?_).trans h
    intro a
    by_cases ha : t ≤ D a
    · simp only [if_pos ha, mul_one]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ha hl)
    · simp [ha, Real.exp_nonneg]
  rw [Real.exp_sub]
  exact (le_div_iff₀ (Real.exp_pos (l*t))).mpr (by simpa [mul_comm] using hm)

private theorem absolute_prob {α : Type*} [Fintype α] (D : α → ℝ) (t : ℝ) :
    prob (fun a => t ≤ |D a|) ≤ prob (fun a => t ≤ D a) + prob (fun a => t ≤ -D a) := by
  classical
  change mean (fun a => if t ≤ |D a| then 1 else 0) ≤
    mean (fun a => if t ≤ D a then 1 else 0) + mean (fun a => if t ≤ -D a then 1 else 0)
  rw [← mean_add]
  apply mean_mono
  intro a
  by_cases h : 0 ≤ D a
  · rw [abs_of_nonneg h]
    exact le_add_of_nonneg_right (by split <;> norm_num)
  · rw [abs_of_neg (lt_of_not_ge h)]
    exact le_add_of_nonneg_left (by split <;> norm_num)

private theorem additive_tail {m : ℕ} (hm : 0 < m) (f : (Fin m × Bool) → Bool → ℝ)
    (hf : ∀ i b, f i b ∈ Set.Icc (0:ℝ) 1) (t : ℝ) (ht : 0 ≤ t) :
    tail (additive f) t ≤ 2 * Real.exp (-t^2/(2*m)) := by
  let D (s : Sample m) := additive f (draw s) - mean (fun q : Sample m => additive f (draw q))
  let l := t/(m:ℝ)
  have hm' : (0:ℝ) < m := by positivity
  have hl : 0 ≤ l := div_nonneg ht hm'.le
  have hpos := exponential_tail D t l ((m:ℝ)*(l^2/2)) hl (additive_mgf f hf l)
  have hneg := exponential_tail (fun s => -D s) t l ((m:ℝ)*(l^2/2)) hl (by
    simpa only [mul_neg, neg_mul, neg_sq] using additive_mgf f hf (-l))
  have hcalc : (m:ℝ)*(l^2/2)-l*t = -t^2/(2*m) := by
    unfold l
    field_simp
    ring
  rw [hcalc] at hpos hneg
  exact (absolute_prob D t).trans (by linarith)

private theorem distance_lipschitz (m : ℕ) (x y : Cube m) :
    |distance x-distance y| ≤ hamming x y := by
  unfold distance hamming
  rw [← sum_sub_distrib, Nat.cast_sum, Fintype.sum_prod_type]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  simp only [Fintype.sum_bool]
  generalize x (i,false) = a
  generalize x (i,true) = b
  generalize y (i,false) = c
  generalize y (i,true) = d
  cases a <;> cases b <;> cases c <;> cases d <;> norm_num

private theorem distance_value (m : ℕ) (s : Sample m) :
    distance (draw s) = if s.1 then (m:ℝ) else 0 := by
  unfold distance
  rcases s with ⟨b,q⟩
  cases b
  · simp [draw]
  · have h (i : Fin m) : draw (true,q) (i,false) ≠ draw (true,q) (i,true) := by
      change xor (q i) false ≠ xor (q i) true
      generalize q i = b
      decide +revert
    simp [h]

private theorem distance_mean (m : ℕ) :
    mean (fun s : Sample m => distance (draw s)) = (m:ℝ)/2 := by
  rw [mean_prod]
  simp only [distance_value]
  rw [mean_bool]
  simp [mean_const]

private theorem distance_tail (m : ℕ) (t : ℝ) :
    tail (distance (m := m)) t = if t ≤ (m:ℝ)/2 then 1 else 0 := by
  classical
  have hg (s : Sample m) :
      |distance (draw s) - mean (fun q : Sample m => distance (draw q))| = (m:ℝ)/2 := by
    rw [distance_mean, distance_value]
    have hm : (0:ℝ) ≤ m := by positivity
    cases s.1
    · simp only [Bool.false_eq_true, if_false, zero_sub, abs_neg, abs_of_nonneg (by positivity : 0 ≤ (m:ℝ)/2)]
    · rw [if_pos rfl, abs_of_nonneg (by linarith)]
      ring
  simp only [tail, hg, prob]
  exact mean_const _

private theorem distance_optimal (m : ℕ) (hm : 0 < m) (C : ℝ) :
    (∀ t : ℝ, 0 ≤ t → tail (distance (m := m)) t ≤ 2*Real.exp (-C*t^2)) ↔
      C ≤ 4*Real.log 2/(m:ℝ)^2 := by
  have hm' : (0:ℝ) < m := by positivity
  have hexp (u : ℝ) : 2 * Real.exp u = Real.exp (Real.log 2 + u) := by
    rw [Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 2)]
  constructor
  · intro h
    have hh := h ((m:ℝ)/2) (by positivity)
    rw [distance_tail, if_pos le_rfl, hexp, ← Real.exp_zero, Real.exp_le_exp] at hh
    apply (le_div_iff₀ (sq_pos_of_pos hm')).mpr
    nlinarith
  · intro h t ht
    rw [distance_tail]
    split_ifs with hc
    · rw [hexp, ← Real.exp_zero, Real.exp_le_exp]
      have hK : 0 ≤ 4*Real.log 2/(m:ℝ)^2 := by
        exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))) (sq_nonneg _)
      have hs : t^2 ≤ ((m:ℝ)/2)^2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hc) (show 0 ≤ (m:ℝ)/2+t by positivity)]
      have hb := mul_le_mul h hs (sq_nonneg t) hK
      have hval : (4*Real.log 2/(m:ℝ)^2)*((m:ℝ)/2)^2 = Real.log 2 := by
        field_simp
        ring
      linarith
    · positivity

end OMA.S_mo_306601

open OMA.S_mo_306601 in
theorem OMA.solution : type_of% @OMA.S_mo_306601.main := by
  constructor
  · intro m hm
    refine ⟨one_uniform, two_uniform, three_uniform, additive_tail hm, distance_lipschitz m,
      distance_mean m, ?_, distance_optimal m hm⟩
    rw [distance_tail, if_pos le_rfl]
  · rw [distance_tail]
    norm_num
    have he := Real.add_one_le_exp (2:ℝ)
    rw [Real.exp_neg, ← div_eq_mul_inv]
    apply (div_lt_iff₀ (Real.exp_pos _)).mpr
    linarith
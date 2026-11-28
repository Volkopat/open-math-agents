import OMAStatements.S_mo_300933

/-!
For the forward direction, select one radius for each exponent and construct a
polynomial whose corresponding term dominates at both signs of that radius.
Alternation then supplies one positive root in each gap. A parity violation
supplies an extra negative root and prevents universal interpolation.

For the reverse direction, divide the derivative by its common even power of x.
Two applications of the mean value theorem preserve a root between successive
original roots after this division, so induction gives injectivity.

Problem and real-node convention: https://mathoverflow.net/questions/300933 .
-/

namespace OMA.S_mo_300933
open Polynomial Matrix Set

noncomputable def sparse {n : ℕ} (d : Fin n → ℕ) (c : Fin n → ℝ) : ℝ[X] :=
  ∑ i, monomial (d i) (c i)

theorem sparse_eval {n : ℕ} (d : Fin n → ℕ) (c : Fin n → ℝ) (x : ℝ) :
    (sparse d c).eval x = ∑ i, c i * x ^ d i := by simp [sparse,eval_finsetSum]

theorem sparse_coeff {n : ℕ} (d : Fin n → ℕ) (hd : Function.Injective d) (c : Fin n → ℝ) (i : Fin n) :
    (sparse d c).coeff (d i) = c i := by
  classical
  simp [sparse,finsetSum_coeff,coeff_monomial,hd.eq_iff]

theorem interpolates_iff {n : ℕ} (d : Fin n → ℕ) : Interpolates d ↔
    ∀ x : Fin n → ℝ, Function.Injective x → ∀ c : Fin n → ℝ,
      (∀ i, (sparse d c).eval (x i) = 0) → c = 0 := by
  have aux (x : Fin n → ℝ) :
      (∀ y : Fin n → ℝ, ∃ c : Fin n → ℝ, ∀ i, (∑ j, c j * (x i)^d j) = y i) ↔
      (∀ c : Fin n → ℝ, (∀ i, (sparse d c).eval (x i) = 0) → c = 0) := by
    let M : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => (x i)^d j
    have he (c : Fin n → ℝ) (i : Fin n) : M.mulVecLin c i = ∑ j, c j * (x i)^d j := by
      simp [M, Matrix.mulVec, dotProduct, mul_comm]
    calc
      _ ↔ Function.Surjective M.mulVecLin := by simp only [Function.Surjective,funext_iff,he]
      _ ↔ Function.Injective M.mulVecLin := LinearMap.injective_iff_surjective.symm
      _ ↔ _ := by rw [← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_eq_bot_iff]; simp only [← Matrix.mulVecLin_apply,funext_iff,he,sparse_eval,Pi.zero_apply]
  exact forall_congr' fun x => imp_congr_right fun _ => aux x

/-- Opposite signs at endpoints force a zero strictly inside the interval. -/
theorem zero_between {g : ℝ → ℝ} (hcont : Continuous g) {a b : ℝ} (hab : a < b)
    (hs : g a * g b < 0) : ∃ t ∈ Ioo a b, g t = 0 := by
  rcases mul_neg_iff.mp hs with h | h
  · exact intermediate_value_Ioo' hab.le hcont.continuousOn ⟨h.2,h.1⟩
  · exact intermediate_value_Ioo hab.le hcont.continuousOn ⟨h.1,h.2⟩

/-- Rolle's theorem after an everywhere nonnegative factor has been removed. -/
theorem sparse_rolle {p : ℝ[X]} (hp : p ≠ 0) (q w : ℝ → ℝ) (hq : Continuous q)
    (hw : ∀ t, 0 ≤ w t) (hder : ∀ t, HasDerivAt (fun x => p.eval x) (w t*q t) t)
    {a b : ℝ} (hab : a < b) (ha : p.eval a = 0) (hb : p.eval b = 0) :
    ∃ t ∈ Ioo a b, q t = 0 := by
  obtain ⟨y,hy,hy'⟩ := (Set.Ioo_infinite hab).exists_notMem_finset p.roots.toFinset
  have hy0 : p.eval y ≠ 0 := by simpa [Polynomial.mem_roots hp, Polynomial.IsRoot] using hy'
  obtain ⟨u,hu,heu⟩ := exists_hasDerivAt_eq_slope _ _ hy.1 p.continuous.continuousOn (fun x _ => hder x)
  obtain ⟨v,hv,hev⟩ := exists_hasDerivAt_eq_slope _ _ hy.2 p.continuous.continuousOn (fun x _ => hder x)
  rw [ha,sub_zero] at heu
  rw [hb,zero_sub] at hev
  have huv : q u * q v < 0 := by
    have hs : (w u*q u)*(w v*q v) < 0 := by
      rw [heu,hev]
      rcases lt_or_gt_of_ne hy0 with h|h
      · exact mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos h (sub_pos.mpr hy.1)) (div_pos (neg_pos.mpr h) (sub_pos.mpr hy.2))
      · exact mul_neg_of_pos_of_neg (div_pos h (sub_pos.mpr hy.1)) (div_neg_of_neg_of_pos (neg_neg_of_pos h) (sub_pos.mpr hy.2))
    by_contra! hn
    nlinarith [mul_nonneg (mul_nonneg (hw u) (hw v)) hn]
  obtain ⟨t,ht,hqt⟩ := zero_between hq (hu.2.trans hv.1) huv
  exact ⟨t,⟨hu.1.trans ht.1,ht.2.trans hv.2⟩,hqt⟩
end OMA.S_mo_300933

namespace OMA.S_mo_300933
open Polynomial Finset Set

/-- At the radius indexed by i, the i-th term dominates all other terms, for
any prescribed signs. This follows from a Gaussian bound on the exponents. -/
theorem gaussian_diagonal {n : ℕ} (d : Fin n → ℕ) (hd : Function.Injective d)
    (s : Fin n → ℝ) (hs : ∀ j, |s j| = 1) (i : Fin n) :
    0 < s i * ∑ j, s j * Real.exp (-((n:ℝ)+1)*((d j:ℝ)-d i)^2) := by
  classical
  let T : ℝ := n+1
  let g (j : Fin n) := s j * Real.exp (-T*((d j:ℝ)-d i)^2)
  let S := (Finset.univ : Finset (Fin n)).erase i
  have hT : 0 < T := by dsimp [T]; positivity
  have hb (j : Fin n) (hj : j ∈ S) : |g j| ≤ (Real.exp T)⁻¹ := by
    have he : d j ≠ d i := hd.ne (mem_erase.mp hj).1
    have he' : 1 ≤ ((d j:ℝ)-d i)^2 := by
      rcases lt_or_gt_of_ne he with h|h
      · have h' : (d j:ℝ)+1 ≤ d i := by exact_mod_cast h
        nlinarith [sq_nonneg ((d j:ℝ)-d i+1)]
      · have h' : (d i:ℝ)+1 ≤ d j := by exact_mod_cast h
        nlinarith [sq_nonneg ((d j:ℝ)-d i-1)]
    simp only [g,abs_mul,hs,one_mul,abs_of_pos (Real.exp_pos _),← Real.exp_neg,Real.exp_le_exp]
    nlinarith [mul_nonneg hT.le (sub_nonneg.mpr he')]
  have bound : |∑ j ∈ S, g j| < 1 := by
    calc
      _ ≤ ∑ j ∈ S, |g j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ S, (Real.exp T)⁻¹ := Finset.sum_le_sum hb
      _ = (S.card:ℝ) / Real.exp T := by simp [div_eq_mul_inv]
      _ < 1 := by
        rw [div_lt_one (Real.exp_pos _)]
        have hcard : S.card ≤ n := by simpa using Finset.card_le_univ S
        have hcard' : (S.card:ℝ) ≤ n := by exact_mod_cast hcard
        have h := Real.add_one_le_exp T
        dsimp [T] at h ⊢; linarith
  have diag : g i = s i := by simp [g]
  have he := Finset.sum_erase_add (s := Finset.univ) g (Finset.mem_univ i)
  change (∑ j ∈ S, g j) + g i = ∑ j, g j at he
  change 0 < s i * ∑ j, g j
  rw [← he,diag]
  rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.mp (hs i) with hi|hi <;>
    rw [hi] <;> have := abs_lt.mp bound <;> linarith

theorem signs_at_radii {n : ℕ} (d : Fin n → ℕ) (hd : StrictMono d) :
    ∃ (r c : Fin n → ℝ), StrictMono r ∧ (∀ i, 0 < r i) ∧
      (∀ i, 0 < (-1:ℝ)^i.val * (sparse d c).eval (r i)) ∧
      (∀ i, 0 < (-1:ℝ)^(i.val+d i) * (sparse d c).eval (-r i)) := by
  let T : ℝ := n+1
  let r (i : Fin n) := Real.exp (2*T*(d i:ℝ))
  let c (j : Fin n) := (-1:ℝ)^j.val * Real.exp (-T*(d j:ℝ)^2)
  have ht : 0 < T := by dsimp [T]; positivity
  have hm : StrictMono r := by
    intro i j hj
    apply Real.exp_lt_exp.mpr
    exact mul_lt_mul_of_pos_left (by exact_mod_cast hd hj) (by positivity)
  have general (i : Fin n) (u : ℝ) (hu : |u| = 1) :
      0 < ((-1:ℝ)^i.val * u^d i) * (sparse d c).eval (u*r i) := by
    let s (j : Fin n) := (-1:ℝ)^j.val * u^d j
    have hs (j : Fin n) : |s j| = 1 := by simp [s,abs_mul,abs_pow,hu]
    have he : (sparse d c).eval (u*r i) = Real.exp (T*(d i:ℝ)^2) *
        ∑ j, s j * Real.exp (-T*((d j:ℝ)-d i)^2) := by
      rw [sparse_eval, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [r,c,s,mul_pow,← Real.exp_nat_mul]
      calc
        _ = ((-1:ℝ)^j.val*u^d j) * (Real.exp (-T*(d j:ℝ)^2)*Real.exp ((d j:ℝ)*(2*T*d i))) := by ring
        _ = _ := by
          have eqn : Real.exp (-T*(d j:ℝ)^2)*Real.exp ((d j:ℝ)*(2*T*d i)) =
              Real.exp (T*(d i:ℝ)^2)*Real.exp (-T*((d j:ℝ)-d i)^2) := by
            rw [← Real.exp_add,← Real.exp_add]; congr 1; ring
          rw [eqn]; ring
    rw [he,mul_left_comm]
    exact mul_pos (Real.exp_pos _) (gaussian_diagonal d hd.injective s hs i)
  refine ⟨r,c,hm,fun i => Real.exp_pos _, ?_, ?_⟩
  all_goals intro i
  · simpa using general i 1 (by norm_num)
  · simpa [pow_add] using general i (-1) (by norm_num)
end OMA.S_mo_300933

namespace OMA.S_mo_300933
open Polynomial Set

theorem first_zero {n : ℕ} (d : Fin (n+1) → ℕ) (hd : StrictMono d) (h : Interpolates d) : d 0 = 0 := by
  by_contra hn
  have hn' (i : Fin (n+1)) : d i ≠ 0 := (Nat.pos_of_ne_zero hn |>.trans_le (hd.monotone (Fin.zero_le i))).ne'
  let x (i : Fin (n+1)) : ℝ := i.val
  have hx : Function.Injective x := fun i j hij => Fin.ext (by dsimp [x] at hij; exact_mod_cast hij)
  obtain ⟨c,hc⟩ := h x hx (fun _ => 1)
  have hh := hc 0
  simp [x,zero_pow (hn' _)] at hh

theorem parity_of_interpolates {n : ℕ} (d : Fin (n+1) → ℕ) (hd : StrictMono d)
    (h : Interpolates d) (i : Fin (n+1)) : d i % 2 = i.val % 2 := by
  have h0 := first_zero d hd h
  by_contra hi
  have hi0 : (0 : Fin (n+1)) < i := by
    by_contra! hle
    have hz := Fin.le_zero_iff.mp hle
    subst i; simp [h0] at hi
  have ho : Odd (i.val+d i) := Nat.odd_iff.mpr (by omega)
  obtain ⟨r,c,hm,hr,hp,hn⟩ := signs_at_radii d hd
  let p := sparse d c
  have neg0 : 0 < p.eval (-r 0) := by simpa [p,h0] using hn 0
  have negi : p.eval (-r i) < 0 := by simpa [p,ho.neg_one_pow] using hn i
  obtain ⟨z,hz,hz0⟩ := zero_between p.continuous (neg_lt_neg (hm hi0)) (mul_neg_of_neg_of_pos negi neg0)
  have hzneg : z < 0 := hz.2.trans (neg_neg_of_pos (hr 0))
  have hcross (j : Fin n) : p.eval (r j.castSucc) * p.eval (r j.succ) < 0 := by
    have h1 := hp j.castSucc
    have h2 := hp j.succ
    simp only [Fin.val_castSucc,Fin.val_succ,pow_succ] at h1 h2
    rcases neg_one_pow_eq_or ℝ j.val with hs|hs
    · simp [hs] at h1 h2; exact mul_neg_of_pos_of_neg h1 h2
    · simp [hs] at h1 h2; exact mul_neg_of_neg_of_pos h1 h2
  have hyex (j : Fin n) := zero_between p.continuous (hm (Fin.castSucc_lt_succ (i:=j))) (hcross j)
  choose y hy hy0 using hyex
  have hym : StrictMono y := by
    intro a b hab
    exact (hy a).2.trans_le ((hm.monotone (show a.succ ≤ b.castSucc from hab)).trans (hy b).1.le)
  have hzm : StrictMono (Fin.cons z y) := Fin.strictMono_cons.mpr
    ⟨fun j => hzneg.trans ((hr _).trans (hy j).1), hym⟩
  have hc := (interpolates_iff d).mp h (Fin.cons z y) hzm.injective c (Fin.cases hz0 hy0)
  have hh := hp 0
  simp [hc,sparse_eval] at hh
end OMA.S_mo_300933

namespace OMA.S_mo_300933
open Polynomial Set

/-- Removing the common even factor from the derivative preserves parity alternation. -/
theorem ordered_zeros (n : ℕ) (d : Fin n → ℕ) (hd : StrictMono d)
    (h0 : ∀ i, i.val = 0 → d i = 0) (hpar : ∀ i, d i % 2 = i.val % 2)
    (x : Fin n → ℝ) (hx : StrictMono x) (c : Fin n → ℝ)
    (hz : ∀ i, (sparse d c).eval (x i) = 0) : c = 0 := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    cases n with
    | zero =>
      funext i
      have hi : i = 0 := Fin.ext (by have := i.isLt; change i.val = 0; omega)
      subst i
      simpa [sparse_eval,h0 0 rfl] using hz 0
    | succ k =>
      let e : Fin (k+1) → ℕ := fun i => d i.succ - d 1
      have hmin (i : Fin (k+1)) : d 1 ≤ d i.succ := hd.monotone (by change 1 ≤ i.val+1; omega)
      have hd0 := h0 0 rfl
      have hpos : 0 < d 1 := by
        have hh : d 0 < d 1 := hd (show (0:Fin (k+2)) < 1 from by change (0:ℕ) < (1:Fin (k+2)).val; simp)
        omega
      have hodd := hpar (1 : Fin (k+2))
      have h1 : (1 : Fin (k+2)).val = 1 := by simp
      rw [h1] at hodd
      have ee : StrictMono e := by
        intro i j hij
        have h := hd (Fin.strictMono_succ hij)
        dsimp [e]; have := hmin i; omega
      have ep (i : Fin (k+1)) : e i % 2 = i.val % 2 := by
        have h := hpar i.succ
        change d i.succ % 2 = (i.val+1)%2 at h
        dsimp [e]; have := hmin i; omega
      have ez (i : Fin (k+1)) (hi : i.val = 0) : e i = 0 := by
        have hi' : i = 0 := Fin.ext hi
        subst i; change d 1 - d 1 = 0; omega
      let b : Fin (k+1) → ℝ := fun i => c i.succ * (d i.succ : ℝ)
      let w : ℝ → ℝ := fun t => t^(d 1-1)
      have hw (t : ℝ) : 0 ≤ w t := by
        have heven : Even (d 1-1) := Nat.even_iff.mpr (by omega)
        exact heven.pow_nonneg _
      have deriv (t : ℝ) : HasDerivAt (fun z => (sparse d c).eval z) (w t*(sparse e b).eval t) t := by
        suffices he : (sparse d c).derivative.eval t = w t*(sparse e b).eval t by
          rw [← he]; exact (sparse d c).hasDerivAt t
        simp only [sparse, derivative_sum, eval_finsetSum, derivative_monomial, eval_monomial]
        rw [Fin.sum_univ_succ (f := fun i => c i * (d i : ℝ) * t^(d i-1)),hd0]
        simp only [Nat.cast_zero,mul_zero,zero_mul,zero_add,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        have he : d i.succ-1 = (d 1-1)+e i := by dsimp [e]; have := hmin i; omega
        rw [he,pow_add]
        dsimp [w,b]; ring
      by_contra hn
      have hp : sparse d c ≠ 0 := by
        intro he
        apply hn; funext i
        simpa [sparse_coeff d hd.injective c i] using congrArg (fun p : ℝ[X] => p.coeff (d i)) he
      have hr (i : Fin (k+1)) := sparse_rolle hp (fun t => (sparse e b).eval t) w
        (sparse e b).continuous hw deriv (hx (Fin.castSucc_lt_succ (i := i))) (hz _) (hz _)
      choose y hy hy0 using hr
      have hy' : StrictMono y := by
        intro i j hij
        exact (hy i).2.trans_le ((hx.monotone (show i.succ ≤ j.castSucc from hij)).trans (hy j).1.le)
      have bb := ih e ee ez ep y hy' b hy0
      have ztail (i : Fin (k+1)) : c i.succ = 0 := by
        have hi : (d i.succ : ℝ) ≠ 0 := by exact_mod_cast (hpos.trans_le (hmin i)).ne'
        exact (mul_eq_zero.mp (congrFun bb i)).resolve_right hi
      have z0 := hz 0
      rw [sparse_eval,Fin.sum_univ_succ,hd0] at z0
      simp [ztail] at z0
      exact hn (funext (Fin.cases z0 ztail))

theorem interpolates_of_parity {n : ℕ} (d : Fin n → ℕ) (hd : StrictMono d)
    (h0 : ∀ i, i.val = 0 → d i = 0) (hpar : ∀ i, d i % 2 = i.val % 2) : Interpolates d := by
  apply (interpolates_iff d).mpr
  intro x hx c hz
  exact ordered_zeros n d hd h0 hpar (x ∘ Tuple.sort x)
    ((Tuple.monotone_sort x).strictMono_of_injective (hx.comp (Tuple.sort x).injective)) c (fun i => hz _)
end OMA.S_mo_300933

theorem OMA.solution : type_of% @OMA.S_mo_300933.main := by
  intro n d hd
  constructor
  · intro h
    cases n with
    | zero => exact ⟨fun i => i.elim0, fun i => i.elim0⟩
    | succ n =>
      refine ⟨?_,OMA.S_mo_300933.parity_of_interpolates d hd h⟩
      intro i hi
      have he : i = 0 := Fin.ext hi
      simpa [he] using OMA.S_mo_300933.first_zero d hd h
  · rintro ⟨h0,hpar⟩
    exact OMA.S_mo_300933.interpolates_of_parity d hd h0 hpar

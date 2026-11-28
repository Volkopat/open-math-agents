import FormalConjectures.ErdosProblems.«893»

/-! Along n=3^t 2^i, each doubling contributes a coprime factor
2^n+1 with at least t divisors. A fixed bound on the doubling ratios of the
summatory function is incompatible with this growth when t is large. -/
-- Credit: @marcusbuffett
open Finset ArithmeticFunction Erdos893
open scoped ArithmeticFunction.sigma
namespace Mersenne893

private theorem many_divisors {x : ℕ} (hx : 1 < x) (t : ℕ) :
    t ≤ σ 0 (x^(3^t)+1) := by
  let F := fun j : ℕ => x^(3^j)+1
  have chain {j t : ℕ} (h : j ≤ t) : F j ∣ F t := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    simpa [F, pow_add, pow_mul] using
      Odd.nat_add_dvd_pow_add_pow (x^(3^j)) 1 ((by decide : Odd (3 : ℕ)).pow (n := k))
  have inj : Function.Injective F := by
    apply StrictMono.injective
    intro i j hij
    dsimp [F]
    exact Nat.add_lt_add_right (Nat.pow_lt_pow_right hx (Nat.pow_lt_pow_right (by decide) hij)) _
  rw [sigma_zero_apply]
  have s : (range t).image F ⊆ (F t).divisors := by
    rintro _ h
    obtain ⟨j,hj,rfl⟩ := mem_image.mp h
    exact Nat.mem_divisors.mpr ⟨chain (mem_range.mp hj).le, by dsimp [F]; omega⟩
  simpa [F,card_image_of_injective _ inj] using card_le_card s

private theorem mersenne_double (n : ℕ) (hn : 0 < n) :
    σ 0 (2^(2*n)-1) = σ 0 (2^n-1) * σ 0 (2^n+1) := by
  have hpos : 0 < 2^n := pow_pos (by decide) _
  have h2 : 2 ∣ 2^n := dvd_pow_self 2 (by omega)
  have cop : Nat.Coprime (2^n-1) (2^n+1) := by
    rw [show 2^n+1=(2^n-1)+2 by omega,Nat.coprime_self_add_right]
    rw [Nat.coprime_two_right]
    exact ⟨(2^n)/2-1,by omega⟩
  have eq : 2^(2*n)-1 = (2^n-1)*(2^n+1) := by
    rw [show 2*n=n+n by omega,pow_add]
    have hle : 1 ≤ 2^n*2^n := Nat.mul_pos hpos hpos
    zify [show 1 ≤ 2^n by omega,hle]
    ring
  rw [eq,isMultiplicative_sigma.map_mul_of_coprime cop]

private theorem term_le {n : ℕ} (hn : 0 < n) : σ 0 (2^n-1) ≤ f n :=
  single_le_sum (f := fun j : ℕ => σ 0 (2^j-1)) (fun _ _ => Nat.zero_le _)
    (mem_Icc.mpr ⟨hn,le_rfl⟩)

private theorem term_pos {n : ℕ} (hn : 0 < n) : 0 < σ 0 (2^n-1) := by
  exact sigma_pos_iff.mpr (Nat.sub_pos_of_lt
    (Nat.one_lt_pow hn.ne' (by decide : 1 < 2)))

end Mersenne893
open Mersenne893 in
theorem OMA.solution : type_of% @Erdos893.erdos_893.variants.unbounded := by
  rintro ⟨b,hb⟩
  obtain ⟨c,hc⟩ := exists_nat_gt (max b 1)
  have cpos : 0 < c := by
    have : (1:ℝ) < c := (le_max_right ..).trans_lt hc
    exact_mod_cast (show (0:ℝ) < c by linarith)
  have bound {n : ℕ} (hn : 0 < n) : f (2*n) ≤ c*f n := by
    have h := hb (Set.mem_range_self n)
    have h' : (f (2*n):ℝ) / f n ≤ c := h.trans ((le_max_left ..).trans hc.le)
    have hf : 0 < f n := (term_pos hn).trans_le (term_le hn)
    exact_mod_cast (div_le_iff₀ (by exact_mod_cast hf : (0:ℝ) < f n)).mp h'
  let t := 2*c
  let n := fun i : ℕ => 2^i*3^t
  have pos (i) : 0 < n i := by dsimp [n]; positivity
  have double (i) : n (i+1) = 2*n i := by dsimp [n]; rw [pow_succ]; ring
  have low (i : ℕ) : t^i ≤ σ 0 (2^(n i)-1) := by
    induction i with
    | zero =>
      rw [pow_zero]
      exact Nat.succ_le_of_lt (term_pos (pos 0))
    | succ i ih =>
      rw [double,mersenne_double _ (pos i),pow_succ]
      apply Nat.mul_le_mul ih
      have h := many_divisors (x := 2^(2^i))
        (Nat.one_lt_pow (by positivity) (by decide)) t
      simpa [n,pow_mul] using h
  have high (i : ℕ) : f (n i) ≤ c^i*f (n 0) := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [double,pow_succ]
      exact (bound (pos i)).trans (by nlinarith [Nat.mul_le_mul_left c ih])
  let i := f (n 0)
  have hi : f (n 0) < 2^i := Nat.lt_two_pow_self
  have h := (low i).trans ((term_le (pos i)).trans (high i))
  dsimp only [t] at h
  rw [mul_pow,mul_comm (2^i)] at h
  exact (not_le.mpr hi) (Nat.le_of_mul_le_mul_left h (pow_pos cpos i))

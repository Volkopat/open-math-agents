import OMAReductions.R_Erdos692_erdos_692_variants_cambie_local_maxima_R1

/-! Cambie's alternating-interval argument for Erdős 692.
The two arithmetic inputs are a forward prime-gap bound and a density comparison
on a polynomial window. The change in density at a prime is proved by counting
its multiples in finite prefixes. The interval packing then gives distinct peaks.
Reference: Cambie, Resolution of Erdős' problems about unimodularity, Theorem 3.
Credit: @Onionssss. -/
namespace OMA.R_Erdos692_erdos_692_variants_cambie_local_maxima_R1_H1_R1
open Filter Set Topology Erdos692
open scoped Classical

-- Forward gaps bounded by x^(2/3), written without real powers.
def H1 : Prop :=
  ∀ᶠ x : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ x < p ∧ (p-x)^3 ≤ x^2

-- The density of integers with no interval divisor exceeds the one-divisor density.
def H2 : Prop :=
  ∀ (k : ℕ) (δ : ℕ → ℕ → ℝ), (∀ a b, IsDelta₁ a b (δ a b)) →
    ∀ᶠ n : ℕ in atTop, let t := 8*(n+n^k+1)
    ∀ p : ℕ, p.Prime → 2*t^3 ≤ p → p ≤ 4*t^3 →
      ∃ z : ℝ, {x : ℕ | {d ∈ Set.Ioo n p | d ∣ x}.ncard = 0}.HasDensity z ∧ δ n p < z

lemma gap_in_window {x t : ℕ} (hx : x ≤ 4*t^3)
    (h : ∃ p : ℕ, p.Prime ∧ x < p ∧ (p-x)^3 ≤ x^2) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ p ≤ x + 3*t^2 := by
  obtain ⟨p, hp, hxp, hg⟩ := h
  refine ⟨p, hp, hxp, ?_⟩
  have hc : (p-x)^3 ≤ (3*t^2)^3 := calc
    (p-x)^3 ≤ x^2 := hg
    _ ≤ (4*t^3)^2 := Nat.pow_le_pow_left hx 2
    _ ≤ (3*t^2)^3 := by ring_nf; omega
  by_contra! hbad
  have hlt : 3*t^2 < p-x := by omega
  have := Nat.pow_lt_pow_left hlt (by decide : 3 ≠ 0)
  omega

lemma pack (n N t : ℕ) (ht : 0 < t) (hn : n < t^3) (hN : 8*N ≤ t)
    (gap : ∀ x : ℕ, t^3 ≤ x → x ≤ 4*t^3 →
      ∃ p : ℕ, p.Prime ∧ x < p ∧ (p-x)^3 ≤ x^2) :
    ∃ p q : Fin N → ℕ,
      (∀ i, (p i).Prime ∧ (q i).Prime ∧ 2*t^3 ≤ p i ∧
        n < q i ∧ p i < 2*q i ∧ 2*q i ≤ 4*t^3) ∧
      (∀ i j, i < j → 2*q i < p j) := by
  let a (i : ℕ) := t^3 + 8*t^2*i
  have step (i : ℕ) : a (i+1) = a i + 8*t^2 := by dsimp [a]; ring
  have lo (i : ℕ) : t^3 ≤ a i := Nat.le_add_right _ _
  have hi (i : ℕ) (hi : i ≤ N) : a i ≤ 2*t^3 := by
    have h : 8*i ≤ t := by omega
    have := Nat.mul_le_mul_right (t^2) h
    dsimp [a]
    nlinarith only [this]
  have w : 0 < t^2 := pow_pos ht _
  have get (i : Fin N) :
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 2*a i.val < p ∧
        n < q ∧ p < 2*q ∧ 2*q ≤ 2*a (i.val+1) := by
    have htop := hi (i.val+1) i.isLt
    rw [step] at htop
    have hbase := lo i.val
    have find (x : ℕ) (h₁ : t^3 ≤ x) (h₂ : x ≤ 4*t^3) :=
      gap_in_window h₂ (gap x h₁ h₂)
    obtain ⟨p,hp,hp₁,hp₂⟩ := find (2*a i.val) (by omega) (by omega)
    obtain ⟨q,hq,hq₁,hq₂⟩ := find (a i.val + 2*t^2) (by omega) (by omega)
    exact ⟨p,q,hp,hq,hp₁,by omega,by omega,by rw [step]; omega⟩
  choose p q hp hq hl hnq hpq hr using get
  refine ⟨p,q,fun i => ⟨hp i,hq i,?_,hnq i,hpq i,?_⟩,?_⟩
  · have := lo i.val; have := hl i; omega
  · have := hi (i.val+1) i.isLt; have := hr i; omega
  · intro i j hij
    have hstep : i.val+1 ≤ j.val := hij
    have hmono : a (i.val+1) ≤ a j.val :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ hstep) _
    have := hr i; have := hl j; omega

lemma prime_recurrence {n p : ℕ} (hn : n < p) (hp : p.Prime) {u v z : ℝ}
    (hu : IsDelta₁ n p u) (hv : IsDelta₁ n (p+1) v)
    (hz : {x : ℕ | {d ∈ Set.Ioo n p | d ∣ x}.ncard = 0}.HasDensity z) :
    v = (((p : ℝ)-1)*u + z)/p := by
  classical

  let cnt (S : Set ℕ) (b : ℕ) : ℕ := ((Finset.range b).filter (· ∈ S)).card

  have pd_eq (S : Set ℕ) (b : ℕ) : S.partialDensity Set.univ b = (cnt S b : ℝ) / b := by
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter]
    have h1 : S ∩ Iio b = ↑((Finset.range b).filter (· ∈ S)) := by
      ext n; simp [and_comm]
    rw [h1, Set.ncard_coe_finset, Nat.ncard_Iio]

  have hasDensity_iff (S : Set ℕ) (d : ℝ) :
      S.HasDensity d ↔ Tendsto (fun b => (cnt S b : ℝ) / b) atTop (𝓝 d) := by
    simp only [Set.HasDensity, pd_eq]

  have cnt_succ (S : Set ℕ) (n : ℕ) :
      cnt S (n + 1) = cnt S n + (if n ∈ S then 1 else 0) := by
    unfold cnt
    rw [Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp)]
    · simp

  let divisorsIn (n m x : ℕ) : Set ℕ := {d ∈ Set.Ioo n m | d ∣ x}
  let level (n m r : ℕ) : Set ℕ := {x | (divisorsIn n m x).ncard = r}

  have scale_level {n p : ℕ} (hp : p.Prime) (r y : ℕ) :
      p*y ∈ level n p r ↔ y ∈ level n p r := by
    have he : divisorsIn n p (p*y) = divisorsIn n p y := by
      ext d
      change (_ ∧ _) ↔ (_ ∧ _)
      apply and_congr_right
      intro hd
      have hc : Nat.Coprime d p := (hp.coprime_iff_not_dvd.mpr
        (fun h => (Nat.le_of_dvd (Nat.zero_lt_of_lt hd.1) h).not_gt hd.2)).symm
      exact ⟨hc.dvd_of_dvd_mul_left, fun h => h.trans (dvd_mul_left _ _)⟩
    change (divisorsIn n p (p*y)).ncard = r ↔ _
    rw [he]
    rfl

  have cnt_multiples {n p : ℕ} (hp : p.Prime) (r N : ℕ) :
      cnt {x | p ∣ x ∧ x ∈ level n p r} (p*N) = cnt (level n p r) N := by
    symm
    unfold cnt
    apply Finset.card_bij (fun y _ => p*y)
    · intro y hy
      simp only [Finset.mem_filter] at hy
      obtain ⟨hy,hs⟩ := hy
      simp only [Finset.mem_filter, Finset.mem_range, Set.mem_ofPred_eq]
      exact ⟨(Nat.mul_lt_mul_of_pos_left
        (Finset.mem_range.mp hy) hp.pos), dvd_mul_right _ _, (scale_level hp r y).mpr hs⟩
    · intro a _ b _ h
      exact Nat.eq_of_mul_eq_mul_left hp.pos h
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_range, Set.mem_ofPred_eq] at hx
      obtain ⟨hx,hd,hs⟩ := hx
      obtain ⟨y,rfl⟩ := hd
      refine ⟨y, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_of_mul_lt_mul_left hx, (scale_level hp r y).mp hs⟩

  have next_level {n p x : ℕ} (hn : n < p) :
      x ∈ level n (p+1) 1 ↔
        if p ∣ x then x ∈ level n p 0 else x ∈ level n p 1 := by
    have he : divisorsIn n (p+1) x = if p ∣ x then insert p (divisorsIn n p x)
        else divisorsIn n p x := by
      ext d
      by_cases h : p ∣ x
      · simp only [if_pos h, Set.mem_insert_iff]
        change ((n < d ∧ d < p+1) ∧ d ∣ x) ↔ d = p ∨ ((n < d ∧ d < p) ∧ d ∣ x)
        by_cases e : d = p <;> simp_all <;> omega
      · simp only [if_neg h]
        change ((n < d ∧ d < p+1) ∧ d ∣ x) ↔ ((n < d ∧ d < p) ∧ d ∣ x)
        by_cases e : d = p <;> simp_all <;> omega
    change (divisorsIn n (p+1) x).ncard = 1 ↔ _
    rw [he]
    by_cases h : p ∣ x
    · have hf : (divisorsIn n p x).Finite := (Set.finite_Ioo n p).subset fun _ hd => hd.1
      have hnmem : p ∉ divisorsIn n p x := fun h => (lt_irrefl p) h.1.2
      simp [h, Set.ncard_insert_of_notMem hnmem hf, level]
    · simp [h, level]

  have count_balance {n p : ℕ} (hn : n < p) (b : ℕ) :
      cnt (level n (p+1) 1) b + cnt {x | p ∣ x ∧ x ∈ level n p 1} b =
      cnt (level n p 1) b + cnt {x | p ∣ x ∧ x ∈ level n p 0} b := by
    induction b with
    | zero => simp [cnt]
    | succ b ih =>
      simp only [cnt_succ, Set.mem_ofPred_eq, next_level hn]
      by_cases h : p ∣ b <;> by_cases h₁ : b ∈ level n p 1 <;>
        by_cases h₀ : b ∈ level n p 0 <;> simp [h,h₁,h₀] <;> omega

  -- At a multiple p*N the divisible entries correspond exactly to [0,N).
  have balance (N : ℕ) :
      cnt (level n (p+1) 1) (p*N) + cnt (level n p 1) N =
      cnt (level n p 1) (p*N) + cnt (level n p 0) N := by
    simpa only [cnt_multiples hp] using count_balance hn (p*N)
  let f (s : Set ℕ) (N : ℕ) := (cnt s N : ℝ) / N
  have subseq : Tendsto (fun N : ℕ => p*N) atTop atTop :=
    tendsto_atTop_mono (fun N => by simpa using Nat.mul_le_mul_right N hp.pos) tendsto_id
  have hU : Tendsto (f (level n p 1)) atTop (𝓝 u) := (hasDensity_iff _ _).mp hu
  have hV : Tendsto (f (level n (p+1) 1)) atTop (𝓝 v) := (hasDensity_iff _ _).mp hv
  have hZ : Tendsto (f (level n p 0)) atTop (𝓝 z) := (hasDensity_iff _ _).mp hz
  have lhs := ((hV.comp subseq).mul_const (p : ℝ)).add hU
  have rhs := ((hU.comp subseq).mul_const (p : ℝ)).add hZ
  have eqn : v*p + u = u*p + z := by
    apply tendsto_nhds_unique lhs (rhs.congr' ?_)
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have pp : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have NN : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have cancel (a : ℝ) : a / ((p*N : ℕ) : ℝ) * p = a / N := by
      push_cast
      field_simp
    change (cnt _ (p*N) : ℝ) / ((p*N : ℕ) : ℝ) * p + (cnt _ N : ℝ)/N =
      (cnt _ (p*N) : ℝ) / ((p*N : ℕ) : ℝ) * p + (cnt _ N : ℝ)/N
    rw [cancel, cancel, ← add_div, ← add_div]
    exact congrArg (fun a : ℝ => a / N) (by exact_mod_cast (balance N).symm)
  apply (eq_div_iff (by exact_mod_cast hp.ne_zero)).2
  linarith

theorem main : H1 → H2 → OMA.R_Erdos692_erdos_692_variants_cambie_local_maxima_R1.H1 := by
  intro gap estimate k δ hδ
  obtain ⟨M,hM⟩ := eventually_atTop.1 gap
  filter_upwards [eventually_ge_atTop M, estimate k δ hδ] with n hMn hest
  let t := 8*(n+n^k+1)
  have ht : n < t := by dsimp [t]; omega
  have hcap : 8*n^k ≤ t := by dsimp [t]; omega
  have ht₃ : t ≤ t^3 := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < t) (by decide : 1 ≤ 3)
  obtain ⟨p,q,h,hs⟩ := pack n (n^k) t (by omega) (by omega) hcap
    (fun x hx _ => hM x (by omega))
  refine ⟨p,q,?_,fun i j hij => (hs i j hij).le⟩
  intro i
  obtain ⟨hp,hq,hlo,hn,hpq,hhi⟩ := h i
  obtain ⟨z,hz,hlt⟩ := hest (p i) hp hlo (hpq.le.trans hhi)
  have hrec := prime_recurrence (by omega : n < p i) hp (hδ n (p i)) (hδ n (p i+1)) hz
  refine ⟨by omega,hn,hq,hpq,?_⟩
  rw [hrec,lt_div_iff₀ (by exact_mod_cast hp.pos)]
  linarith

end OMA.R_Erdos692_erdos_692_variants_cambie_local_maxima_R1_H1_R1

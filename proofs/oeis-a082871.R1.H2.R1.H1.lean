import OMAReductions.R_oeis_a082871_R1_H2_R1
import Mathlib

/-!
Step oeis-a082871.R1.H2.R1.H1: for x at least 400 the primes in (x/2, x] have product at least 2^(x/2).
Credit: @xor2k
For x at least 300000: Chebyshev's argument with (30k)! k! / ((15k)! (10k)! (6k)!), which divides
lcm(1..30k) and is divisible by every prime in (5k, 30k], combined with Stirling bounds.
For 400 to 300000: a kernel-checked ladder of intervals with explicit prime products.
-/

namespace OMA.StepCheb30

def SP : List ℕ := [211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547]

def Fl : ℕ := 77292199065995824023208153902258878824166263934455710809030567704432479355775926730329178956150930367858218069907061933662864766699285659981357812398078195686942676233568689644196329360999791260133114254950545987552299242775074862671572593985441201040890792224489021536847930153955159914907780169522810594858493983770863931954181575297671966786130234165070689263502044596479973799812691397910152252557002897686618080987335185829624772693132227011721437092439971523662449551386125013698128948623656975688591266992412477525598181140395806414280149303981455373086877118032771671074506292411890897058881834677893620209813128676908843279153752011749197015051068059729693162548373104991025993492917619704822245653568993499297565173053665110279093566090548922097284116308299748891678472281856596640386151732178045327932148474025248212076645229456891123453376001278378931298611910107251015696570549972285899246777240104274078434990060208940911957377582052091560656794606292290851376587468912960676837972155933157373790385499352547715870174231009932223515035926760346723934085054099082420797142940996490048588775627595497842403361737932800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def sp (n : ℕ) : Bool := (Nat.blt n 548 && SP.any (fun p => Nat.beq p n)) || Nat.beq (Nat.gcd n Fl) 1

def fv (n : ℕ) : ℕ := cond (sp n) n 1

def blk : ℕ → ℕ → ℕ
  | 0, m => fv m
  | d+1, m => blk d m * blk d (m + 2^(d+1))

def tile : ℕ → List ℕ → ℕ
  | _, [] => 1
  | s, d :: ds => blk d s * tile (s + 2^(d+1)) ds

def tend : ℕ → List ℕ → ℕ
  | s, [] => s
  | s, d :: ds => tend (s + 2^(d+1)) ds

def rok (a b s : ℕ) (ds : List ℕ) : Bool :=
  Nat.blt a 300304 && Nat.ble 3 s && Nat.ble (b/2+1) s && Nat.ble (tend s ds) (a+1) &&
    Nat.ble (2^(b/2)) (tile s ds)

def chain : ℕ → List (ℕ × ℕ × ℕ × List ℕ) → Bool
  | c, [] => Nat.ble 300000 c
  | c, (a, b, s, ds) :: r => Nat.beq a c && rok a b s ds && chain (b+1) r

def LAD : List (ℕ × ℕ × ℕ × List ℕ) := [(400, 460, 231, [6, 4, 2, 0]), (461, 537, 269, [6, 5]), (538, 620, 311, [6, 5, 4, 1]), (621, 733, 367, [6, 5, 4, 3, 2, 1, 0]), (734, 860, 431, [7, 4, 3]), (861, 1005, 503, [7, 5, 4, 1, 0]), (1006, 1172, 587, [7, 6, 4, 1]), (1173, 1365, 683, [7, 6, 5, 4, 2, 0]), (1366, 1592, 797, [8, 4, 3, 2, 0]), (1593, 1873, 937, [8, 6, 3]), (1874, 2186, 1095, [8, 7, 2, 1]), (2187, 2565, 1283, [8, 7, 6, 2]), (2566, 2996, 1499, [9, 4, 2, 1]), (2997, 3505, 1753, [9, 6, 5, 3, 2, 1]), (3506, 4104, 2053, [9, 7, 6, 4, 2, 1, 0]), (4105, 4823, 2413, [9, 8, 6, 3, 2, 1]), (4824, 5664, 2833, [9, 8, 7, 6, 5, 2]), (5665, 6685, 3343, [10, 7, 3, 0]), (6686, 7844, 3923, [10, 8, 6, 5, 2, 1]), (7845, 9241, 4621, [10, 9, 6, 3, 2]), (9242, 10898, 5451, [10, 9, 8, 6, 5, 3]), (10899, 12825, 6413, [11, 7, 6, 1, 0]), (12826, 15130, 7567, [11, 9, 6, 2, 1]), (15131, 17807, 8905, [11, 10, 5, 3, 0]), (17808, 20956, 10479, [11, 10, 9, 6, 4, 0]), (20957, 24693, 12347, [12, 7, 6, 4, 0]), (24694, 29184, 14593, [12, 9, 8, 7, 5, 4, 3, 1, 0]), (29185, 34439, 17221, [12, 10, 9, 8, 6, 4, 3, 2, 1]), (34440, 40690, 20347, [12, 11, 9, 8, 7, 2, 1, 0]), (40691, 47833, 23917, [13, 7, 6, 1, 0]), (47834, 56400, 28201, [13, 10, 9, 6, 4, 3, 0]), (56401, 66511, 33257, [13, 11, 10, 8, 5, 4, 2]), (66512, 78432, 39217, [13, 12, 10, 8, 6, 4]), (78433, 92557, 46279, [13, 12, 11, 10, 9, 7, 6, 3, 2, 0]), (92558, 109222, 54613, [14, 11, 9, 4, 3, 2, 0]), (109223, 128963, 64483, [14, 12, 10, 9, 8, 6, 5, 1]), (128964, 152204, 76103, [14, 13, 10, 9, 8, 5, 4, 3, 2, 1, 0]), (152205, 179901, 89951, [14, 13, 12, 11, 8, 7, 4, 2, 1, 0]), (179902, 212412, 106207, [15, 11, 10, 9, 8, 7, 6, 5, 4]), (212413, 250857, 125429, [15, 13, 11, 8, 7, 6, 5, 2]), (250858, 296244, 148123, [15, 14, 11, 7, 5, 3]), (296245, 349641, 174821, [15, 14, 13, 11, 10, 8, 5, 3])]

theorem SP_prime : ∀ p ∈ SP, p.Prime := by decide +kernel

theorem Fl_eq : Fl = Nat.factorial 547 := by decide +kernel

theorem chain_ok : chain 400 LAD = true := by decide +kernel

def g (lo hi : ℕ) : ℕ := ∏ p ∈ (Finset.Ioc lo hi).filter Nat.Prime, p

theorem g_pos (lo hi : ℕ) : 1 ≤ g lo hi := by
  unfold g
  exact Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun p hp =>
    (Finset.mem_filter.mp hp).2.ne_zero)

theorem g_mul {lo mid hi : ℕ} (h1 : lo ≤ mid) (h2 : mid ≤ hi) : g lo mid * g mid hi = g lo hi := by
  unfold g
  rw [Finset.prod_filter, Finset.prod_filter, Finset.prod_filter]
  exact Finset.prod_Ioc_consecutive _ h1 h2

theorem g_mono {lo hi lo' hi' : ℕ} (h1 : lo ≤ lo') (h2 : hi' ≤ hi) : g lo' hi' ≤ g lo hi := by
  unfold g
  apply Finset.prod_le_prod_of_subset_of_one_le'
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
    exact ⟨⟨by omega, by omega⟩, hp.2⟩
  · intro p hp _
    exact (Finset.mem_filter.mp hp).2.one_lt.le

theorem sp_prime {n : ℕ} (h : sp n = true) (h2 : 2 ≤ n) (h3 : n < 300304) : n.Prime := by
  unfold sp at h
  rw [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨_, h⟩ | h
  · rw [List.any_eq_true] at h
    obtain ⟨p, hp, he⟩ := h
    have : p = n := Nat.eq_of_beq_eq_true he
    exact this ▸ SP_prime p hp
  · have hg : Nat.gcd n Fl = 1 := Nat.eq_of_beq_eq_true h
    by_contra hn
    have hm := Nat.minFac_sq_le_self (by omega) hn
    have hmp : (Nat.minFac n).Prime := Nat.minFac_prime (by omega)
    have hlt : Nat.minFac n ≤ 547 := by
      by_contra hc
      have : 548 ^ 2 ≤ Nat.minFac n ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega
    have d1 : Nat.minFac n ∣ Fl := Fl_eq ▸ Nat.dvd_factorial hmp.pos hlt
    have d2 : Nat.minFac n ∣ Nat.gcd n Fl := Nat.dvd_gcd (Nat.minFac_dvd n) d1
    rw [hg] at d2
    exact hmp.one_lt.ne' (Nat.dvd_one.mp d2)

theorem fv_le {n : ℕ} (h1 : 1 ≤ n) (h3 : n < 300304) : fv n ≤ g (n-1) (n+1) := by
  unfold fv
  cases hs : sp n
  · exact g_pos _ _
  · simp only [cond_true]
    by_cases h2 : 2 ≤ n
    · have hp := sp_prime hs h2 h3
      unfold g
      apply Finset.single_le_prod' (f := fun p => p)
      · intro p hp'
        exact (Finset.mem_filter.mp hp').2.one_lt.le
      · simp only [Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨by omega, by omega⟩, hp⟩
    · have : n = 1 := by omega
      subst this
      exact g_pos _ _

theorem blk_le : ∀ d m : ℕ, 1 ≤ m → m - 1 + 2^(d+1) ≤ 300304 → blk d m ≤ g (m-1) (m-1+2^(d+1)) := by
  intro d
  induction d with
  | zero =>
    intro m h1 h2
    simp only [blk, zero_add, pow_one]
    have := fv_le h1 (by omega)
    rwa [show m - 1 + 2 = m + 1 by omega]
  | succ d ih =>
    intro m h1 h2
    have e : 2^(d+1+1) = 2^(d+1) + 2^(d+1) := by rw [pow_succ]; ring
    have p1 : 1 ≤ 2^(d+1) := Nat.one_le_two_pow
    simp only [blk]
    have a1 := ih m h1 (by omega)
    have a2 := ih (m + 2^(d+1)) (by omega) (by omega)
    rw [show m + 2^(d+1) - 1 = m - 1 + 2^(d+1) by omega] at a2
    calc blk d m * blk d (m + 2^(d+1))
        ≤ g (m-1) (m-1+2^(d+1)) * g (m-1+2^(d+1)) (m-1+2^(d+1)+2^(d+1)) := Nat.mul_le_mul a1 a2
      _ = g (m-1) (m-1+2^(d+1+1)) := by
        rw [g_mul (by omega) (by omega)]
        congr 1
        omega

theorem tend_ge : ∀ (ds : List ℕ) (s : ℕ), s ≤ tend s ds := by
  intro ds
  induction ds with
  | nil => intro s; simp [tend]
  | cons d ds ih =>
    intro s
    simp only [tend]
    have p1 : 1 ≤ 2^(d+1) := Nat.one_le_two_pow
    have := ih (s + 2^(d+1))
    omega

theorem tile_le : ∀ (ds : List ℕ) (s : ℕ), 1 ≤ s → tend s ds ≤ 300304 →
    tile s ds ≤ g (s-1) (tend s ds - 1) := by
  intro ds
  induction ds with
  | nil => intro s _ _; simp only [tile]; exact g_pos _ _
  | cons d ds ih =>
    intro s h1 h2
    simp only [tile, tend] at h2 ⊢
    have p1 : 1 ≤ 2^(d+1) := Nat.one_le_two_pow
    have t1 := tend_ge ds (s + 2^(d+1))
    have a1 := blk_le d s h1 (by omega)
    have a2 := ih (s + 2^(d+1)) (by omega) h2
    calc blk d s * tile (s + 2^(d+1)) ds
        ≤ g (s-1) (s-1+2^(d+1)) * g (s + 2^(d+1) - 1) (tend (s + 2^(d+1)) ds - 1) :=
          Nat.mul_le_mul a1 a2
      _ = g (s-1) (tend (s + 2^(d+1)) ds - 1) := by
        rw [show s + 2^(d+1) - 1 = s - 1 + 2^(d+1) by omega]
        exact g_mul (by omega) (by omega)

theorem chain_spec : ∀ (L : List (ℕ × ℕ × ℕ × List ℕ)) (c : ℕ), chain c L = true →
    ∀ x, c ≤ x → x < 300000 → 2^(x/2) ≤ g (x/2) x := by
  intro L
  induction L with
  | nil =>
    intro c h x hx1 hx2
    simp only [chain] at h
    have := Nat.le_of_ble_eq_true h
    omega
  | cons r L ih =>
    obtain ⟨a, b, s, ds⟩ := r
    intro c h x hx1 hx2
    simp only [chain, rok, Bool.and_eq_true] at h
    obtain ⟨⟨hac, ⟨⟨⟨⟨r1, r2⟩, r3⟩, r4⟩, r5⟩⟩, hr⟩ := h
    have hac' : a = c := Nat.eq_of_beq_eq_true hac
    have r1' : a + 1 ≤ 300304 := Nat.le_of_ble_eq_true r1
    have r2' : 3 ≤ s := Nat.le_of_ble_eq_true r2
    have r3' : b/2+1 ≤ s := Nat.le_of_ble_eq_true r3
    have r4' : tend s ds ≤ a+1 := Nat.le_of_ble_eq_true r4
    have r5' : 2^(b/2) ≤ tile s ds := Nat.le_of_ble_eq_true r5
    by_cases hxb : x ≤ b
    · have t := tile_le ds s (by omega) (by omega)
      have m := g_mono (lo := x/2) (hi := x) (lo' := s-1) (hi' := tend s ds - 1) (by omega) (by omega)
      have pw : 2^(x/2) ≤ 2^(b/2) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    · exact ih (b+1) hr x (by omega) hx2

theorem finite_range (x : ℕ) (h1 : 400 ≤ x) (h2 : x < 300000) : 2^(x/2) ≤ g (x/2) x :=
  chain_spec LAD 400 chain_ok x h1 h2

def A (k : ℕ) : ℕ := (30*k).factorial * k.factorial
def B (k : ℕ) : ℕ := (15*k).factorial * (10*k).factorial * (6*k).factorial
def N (k : ℕ) : ℕ := A k / B k

theorem A_ne (k : ℕ) : A k ≠ 0 := Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
theorem B_ne (k : ℕ) : B k ≠ 0 :=
  Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
    (Nat.factorial_ne_zero _)

theorem divr (c d k q : ℕ) (hd : 0 < d) (h : c * d = 30) : c*k/q = 30*k/q/d := by
  rw [Nat.div_div_eq_div_mul, ← h, show c * d * k = d * (c * k) by ring,
    show q * d = d * q by ring, Nat.mul_div_mul_left _ _ hd]

theorem fac_eq {p : ℕ} (hp : p.Prime) (k c : ℕ) (hc : c ≤ 30) :
    (c*k).factorial.factorization p = ∑ i ∈ Finset.Ico 1 (Nat.log p (30*k) + 1), c*k / p^i :=
  Nat.factorization_factorial hp (Nat.lt_succ_of_le (Nat.log_mono_right (Nat.mul_le_mul_right k hc)))

theorem vA {p : ℕ} (hp : p.Prime) (k : ℕ) : (A k).factorization p =
    ∑ i ∈ Finset.Ico 1 (Nat.log p (30*k) + 1), (30*k/p^i + 30*k/p^i/30) := by
  unfold A
  rw [Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _), Finsupp.add_apply,
    fac_eq hp k 30 le_rfl, show k.factorial = (1*k).factorial by rw [one_mul], fac_eq hp k 1 (by norm_num),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [divr 1 30 k _ (by norm_num) (by norm_num)]

theorem vB {p : ℕ} (hp : p.Prime) (k : ℕ) : (B k).factorization p =
    ∑ i ∈ Finset.Ico 1 (Nat.log p (30*k) + 1), (30*k/p^i/2 + 30*k/p^i/3 + 30*k/p^i/5) := by
  unfold B
  rw [Nat.factorization_mul (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
    (Nat.factorial_ne_zero _), Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
    Finsupp.add_apply, Finsupp.add_apply,
    fac_eq hp k 15 (by norm_num), fac_eq hp k 10 (by norm_num), fac_eq hp k 6 (by norm_num),
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [divr 15 2 k _ (by norm_num) (by norm_num), divr 10 3 k _ (by norm_num) (by norm_num),
    divr 6 5 k _ (by norm_num) (by norm_num)]

theorem vB_le_vA {p : ℕ} (hp : p.Prime) (k : ℕ) : (B k).factorization p ≤ (A k).factorization p := by
  rw [vA hp, vB hp]
  exact Finset.sum_le_sum fun i _ => by omega

theorem vA_le {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (A k).factorization p ≤ (B k).factorization p + Nat.log p (30*k) := by
  rw [vA hp, vB hp]
  calc _ ≤ ∑ i ∈ Finset.Ico 1 (Nat.log p (30*k) + 1), (30*k/p^i/2 + 30*k/p^i/3 + 30*k/p^i/5 + 1) :=
        Finset.sum_le_sum fun i _ => by omega
    _ = _ := by rw [Finset.sum_add_distrib]; simp

theorem B_dvd_A (k : ℕ) : B k ∣ A k :=
  (Nat.factorization_prime_le_iff_dvd (B_ne k) (A_ne k)).mp fun _ hp => vB_le_vA hp k

theorem N_ne (k : ℕ) : N k ≠ 0 := by
  unfold N
  exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (A_ne k)) (B_dvd_A k))
    (Nat.pos_of_ne_zero (B_ne k))).ne'

theorem vN {p : ℕ} (k : ℕ) : (N k).factorization p = (A k).factorization p - (B k).factorization p := by
  unfold N
  rw [Nat.factorization_div (B_dvd_A k)]
  rfl

theorem N_dvd_lcm (k : ℕ) : N k ∣ Nat.lcmUpto (30*k) := by
  refine (Nat.factorization_prime_le_iff_dvd (N_ne k) (Nat.lcmUpto_ne_zero _)).mp fun p hp => ?_
  rw [vN, Nat.factorization_lcmUpto _ hp]
  have := vA_le hp k
  omega

theorem vN_pos {p k : ℕ} (hp : p.Prime) (h1 : 5*k < p) (h2 : p ≤ 30*k) : 1 ≤ (N k).factorization p := by
  rw [vN]
  have hlog : 1 ≤ Nat.log p (30*k) := Nat.le_log_of_pow_le hp.one_lt (by simpa using h2)
  have key : (B k).factorization p < (A k).factorization p := by
    rw [vA hp, vB hp]
    apply Finset.sum_lt_sum
    · intro i _; omega
    · refine ⟨1, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩, ?_⟩
      rw [pow_one]
      have t1 : 1 ≤ 30*k/p := (Nat.le_div_iff_mul_le hp.pos).mpr (by omega)
      have t2 : 30*k/p ≤ 5 := Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hp.pos).mpr (by omega))
      omega
  omega

theorem g_dvd_N {k : ℕ} : g (5*k) (30*k) ∣ N k := by
  unfold g
  apply Finset.prod_primes_dvd
  · intro a ha
    exact (Finset.mem_filter.mp ha).2.prime
  · intro a ha
    obtain ⟨hm, hpa⟩ := Finset.mem_filter.mp ha
    have hm' := Finset.mem_Ioc.mp hm
    exact (hpa.dvd_iff_one_le_factorization (N_ne k)).mpr (vN_pos hpa hm'.1 hm'.2)

theorem theta_nat (n : ℕ) :
    Chebyshev.theta n = ∑ p ∈ (Finset.Ioc 0 n).filter Nat.Prime, Real.log p := by
  unfold Chebyshev.theta
  rw [Nat.floor_natCast]

theorem log_g0 (n : ℕ) : Real.log (g 0 n) = Chebyshev.theta n := by
  rw [theta_nat]
  unfold g
  rw [Nat.cast_prod, Real.log_prod]
  intro p hp
  exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero

theorem log_g {lo hi : ℕ} (h : lo ≤ hi) :
    Real.log (g lo hi) = Chebyshev.theta hi - Chebyshev.theta lo := by
  have e := g_mul (Nat.zero_le lo) h
  rw [← log_g0, ← log_g0, ← e, Nat.cast_mul, Real.log_mul]
  · ring
  · exact_mod_cast (Nat.one_le_iff_ne_zero.mp (g_pos 0 lo))
  · exact_mod_cast (Nat.one_le_iff_ne_zero.mp (g_pos lo hi))

theorem lf_lo {n : ℕ} (hn : n ≠ 0) :
    (n:ℝ) * Real.log n - n + Real.log n / 2 ≤ Real.log n.factorial := by
  have h := Stirling.le_log_factorial_stirling hn
  have : 0 ≤ Real.log (2 * Real.pi) / 2 := by
    have : (1:ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have := Real.log_nonneg this
    linarith
  linarith

theorem lf_hi {n : ℕ} (hn : n ≠ 0) :
    Real.log n.factorial ≤ (n:ℝ) * Real.log n - n + Real.log n / 2 + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 : Stirling.stirlingSeq (m+1) ≤ Stirling.stirlingSeq 1 :=
    Stirling.stirlingSeq'_antitone (Nat.zero_le m)
  rw [Stirling.stirlingSeq_one] at h1
  have hpos := Stirling.stirlingSeq'_pos m
  have h2 := Real.log_le_log hpos h1
  rw [Stirling.log_stirlingSeq_formula, Real.log_div (Real.exp_pos 1).ne' (by positivity),
    Real.log_exp, Real.log_sqrt (by norm_num)] at h2
  have hm : (0:ℝ) < ((m+1 : ℕ) : ℝ) := by positivity
  rw [Real.log_mul (by norm_num) hm.ne', Real.log_div hm.ne' (Real.exp_pos 1).ne', Real.log_exp] at h2
  push_cast at h2 ⊢
  nlinarith

theorem logN_eq (k : ℕ) : Real.log (N k) = Real.log (30*k).factorial + Real.log k.factorial
    - Real.log (15*k).factorial - Real.log (10*k).factorial - Real.log (6*k).factorial := by
  have e : (N k : ℝ) * (B k : ℝ) = (A k : ℝ) := by
    unfold N; exact_mod_cast Nat.div_mul_cancel (B_dvd_A k)
  have hN : (N k : ℝ) ≠ 0 := by exact_mod_cast N_ne k
  have hB : (B k : ℝ) ≠ 0 := by exact_mod_cast B_ne k
  have l := congrArg Real.log e
  rw [Real.log_mul hN hB] at l
  unfold A B at l
  push_cast at l
  have f1 : ((30*k).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have f2 : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have f3 : ((15*k).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have f4 : ((10*k).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have f5 : ((6*k).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  rw [Real.log_mul f1 f2, Real.log_mul (mul_ne_zero f3 f4) f5, Real.log_mul f3 f4] at l
  linarith

noncomputable def Lc : ℝ := 30 * Real.log 30 - 15 * Real.log 15 - 10 * Real.log 10 - 6 * Real.log 6

theorem logck (c k : ℕ) (hc : c ≠ 0) (hk : k ≠ 0) :
    Real.log ((c*k : ℕ) : ℝ) = Real.log c + Real.log k := by
  push_cast
  exact Real.log_mul (by exact_mod_cast hc) (by exact_mod_cast hk)

theorem lo_c (c k : ℕ) (hc : c ≠ 0) (hk : k ≠ 0) :
    (c:ℝ) * k * (Real.log c + Real.log k) - c * k + (Real.log c + Real.log k) / 2
      ≤ Real.log (c*k).factorial := by
  have h := lf_lo (Nat.mul_ne_zero hc hk)
  rw [logck c k hc hk] at h
  push_cast at h
  linarith

theorem hi_c (c k : ℕ) (hc : c ≠ 0) (hk : k ≠ 0) :
    Real.log (c*k).factorial ≤
      (c:ℝ) * k * (Real.log c + Real.log k) - c * k + (Real.log c + Real.log k) / 2 + 1 := by
  have h := lf_hi (Nat.mul_ne_zero hc hk)
  rw [logck c k hc hk] at h
  push_cast at h
  linarith

theorem logN_lo {k : ℕ} (hk : k ≠ 0) :
    k * Lc - Real.log 30 / 2 - Real.log k / 2 - 3 ≤ Real.log (N k) := by
  rw [logN_eq]
  have a1 := lo_c 30 k (by norm_num) hk
  have a2 := lf_lo hk
  have b1 := hi_c 15 k (by norm_num) hk
  have b2 := hi_c 10 k (by norm_num) hk
  have b3 := hi_c 6 k (by norm_num) hk
  have e1 : Real.log 30 = Real.log 2 + Real.log 15 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have e2 : Real.log 15 + Real.log 10 + Real.log 6 = Real.log 30 + Real.log 30 := by
    rw [← Real.log_mul (by norm_num) (by norm_num), ← Real.log_mul (by norm_num) (by norm_num),
      ← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  unfold Lc
  push_cast at a1 b1 b2 b3
  nlinarith

theorem logN_hi {k : ℕ} (hk : k ≠ 0) : Real.log (N k) ≤ k * Lc + 2 := by
  rw [logN_eq]
  have a1 := hi_c 30 k (by norm_num) hk
  have a2 := lf_hi hk
  have b1 := lo_c 15 k (by norm_num) hk
  have b2 := lo_c 10 k (by norm_num) hk
  have b3 := lo_c 6 k (by norm_num) hk
  have e2 : Real.log 15 + Real.log 10 + Real.log 6 = Real.log 30 + Real.log 30 := by
    rw [← Real.log_mul (by norm_num) (by norm_num), ← Real.log_mul (by norm_num) (by norm_num),
      ← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have l30 : 0 ≤ Real.log 30 := Real.log_nonneg (by norm_num)
  have lk : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk)
  unfold Lc
  push_cast at a1 b1 b2 b3
  nlinarith

theorem theta_up {k : ℕ} (hk : k ≠ 0) :
    Chebyshev.theta (30*k : ℕ) ≤ Chebyshev.theta (5*k : ℕ) + k * Lc + 2 := by
  have h1 : g (5*k) (30*k) ≤ N k := Nat.le_of_dvd (Nat.pos_of_ne_zero (N_ne k)) g_dvd_N
  have h2 : Real.log (g (5*k) (30*k)) ≤ Real.log (N k) :=
    Real.log_le_log (by exact_mod_cast g_pos _ _) (by exact_mod_cast h1)
  rw [log_g (by omega)] at h2
  have := logN_hi hk
  linarith

theorem psi_lo (k : ℕ) : Real.log (N k) ≤ Chebyshev.psi (30*k : ℕ) := by
  rw [Chebyshev.psi_eq_log_lcmUpto]
  exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (N_ne k))
    (by exact_mod_cast Nat.le_of_dvd (Nat.lcmUpto_pos _) (N_dvd_lcm k))

theorem Lc_eq : Lc = 14 * Real.log 2 + 9 * Real.log 3 + 5 * Real.log 5 := by
  have h30 : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
    rw [← Real.log_mul (by norm_num) (by norm_num), ← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h15 : Real.log 15 = Real.log 3 + Real.log 5 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h10 : Real.log 10 = Real.log 2 + Real.log 5 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  unfold Lc
  rw [h30, h15, h10, h6]
  ring

theorem Lc_lo : 27.637 ≤ Lc := by
  rw [Lc_eq]
  have l2 := Real.log_two_gt_d9
  have l3 := Real.log_three_gt_d9
  have l5 : 65 * Real.log 2 ≤ 28 * Real.log 5 := by
    have := Real.log_le_log (by norm_num) (show (2:ℝ)^65 ≤ 5^28 by norm_num)
    rw [Real.log_pow, Real.log_pow] at this
    exact_mod_cast this
  linarith

theorem root_le (X : ℝ) (hX : 300000 ≤ X) :
    X ^ (3⁻¹ : ℝ) ≤ X ^ (2⁻¹ : ℝ) / 7 ∧ X ^ (5⁻¹ : ℝ) ≤ X ^ (2⁻¹ : ℝ) / 30 := by
  have h0 : 0 ≤ X := by linarith
  have s2 : (X ^ (2⁻¹ : ℝ)) ^ 2 = X := by exact_mod_cast Real.rpow_inv_natCast_pow h0 (n := 2) (by norm_num)
  have s3 : (X ^ (3⁻¹ : ℝ)) ^ 3 = X := by exact_mod_cast Real.rpow_inv_natCast_pow h0 (n := 3) (by norm_num)
  have s5 : (X ^ (5⁻¹ : ℝ)) ^ 5 = X := by exact_mod_cast Real.rpow_inv_natCast_pow h0 (n := 5) (by norm_num)
  have p2 : 0 ≤ X ^ (2⁻¹ : ℝ) := Real.rpow_nonneg h0 _
  constructor
  · apply le_of_pow_le_pow_left₀ (n := 6) (by norm_num) (by positivity)
    have e1 : (X ^ (3⁻¹ : ℝ)) ^ 6 = X ^ 2 := by
      rw [show (X ^ (3⁻¹ : ℝ)) ^ 6 = ((X ^ (3⁻¹ : ℝ)) ^ 3) ^ 2 by ring, s3]
    have e2 : (X ^ (2⁻¹ : ℝ) / 7) ^ 6 = X ^ 3 / 117649 := by
      rw [show (X ^ (2⁻¹ : ℝ) / 7) ^ 6 = ((X ^ (2⁻¹ : ℝ)) ^ 2) ^ 3 / 117649 by ring, s2]
    rw [e1, e2]
    have : X ^ 2 * 117649 ≤ X ^ 2 * X := by nlinarith
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  · apply le_of_pow_le_pow_left₀ (n := 10) (by norm_num) (by positivity)
    have e1 : (X ^ (5⁻¹ : ℝ)) ^ 10 = X ^ 2 := by
      rw [show (X ^ (5⁻¹ : ℝ)) ^ 10 = ((X ^ (5⁻¹ : ℝ)) ^ 5) ^ 2 by ring, s5]
    have e2 : (X ^ (2⁻¹ : ℝ) / 30) ^ 10 = X ^ 5 / 590490000000000 := by
      rw [show (X ^ (2⁻¹ : ℝ) / 30) ^ 10 = ((X ^ (2⁻¹ : ℝ)) ^ 2) ^ 5 / 590490000000000 by ring, s2]
    rw [e1, e2, le_div_iff₀ (by norm_num)]
    have h3 : 590490000000000 ≤ X ^ 3 := by nlinarith
    have : X ^ 2 * 590490000000000 ≤ X ^ 2 * X ^ 3 := by
      apply mul_le_mul_of_nonneg_left h3 (by positivity)
    nlinarith

theorem theta_big (x : ℕ) (hx : 300000 ≤ x) :
    (x/2 : ℕ) * Real.log 2 ≤ Chebyshev.theta x - Chebyshev.theta (x/2 : ℕ) := by
  set n := x / 30 with hn
  set h := x / 2 with hh
  set m1 := h / 30 + 1 with hm1
  set m2 := m1 / 6 + 1 with hm2
  set m3 := m2 / 6 + 1 with hm3
  have n1 : n ≠ 0 := by omega
  have u0 : Chebyshev.theta h ≤ Chebyshev.theta (30*m1 : ℕ) :=
    Chebyshev.theta_mono (by exact_mod_cast (show h ≤ 30*m1 by omega))
  have u1 := theta_up (k := m1) (by omega)
  have u2 : Chebyshev.theta (5*m1 : ℕ) ≤ Chebyshev.theta (30*m2 : ℕ) :=
    Chebyshev.theta_mono (by exact_mod_cast (show 5*m1 ≤ 30*m2 by omega))
  have u3 := theta_up (k := m2) (by omega)
  have u4 : Chebyshev.theta (5*m2 : ℕ) ≤ Chebyshev.theta (30*m3 : ℕ) :=
    Chebyshev.theta_mono (by exact_mod_cast (show 5*m2 ≤ 30*m3 by omega))
  have u5 := theta_up (k := m3) (by omega)
  have u6 := Chebyshev.theta_le_log4_mul_x (x := ((5*m3 : ℕ) : ℝ)) (by positivity)
  have l0 : Chebyshev.theta (30*n : ℕ) ≤ Chebyshev.theta x :=
    Chebyshev.theta_mono (by exact_mod_cast (show 30*n ≤ x by omega))
  have l1 := psi_lo n
  have l2 := logN_lo n1
  have hX0 : (300000:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hyX : ((30*n : ℕ) : ℝ) ≤ (x:ℝ) := by exact_mod_cast (show 30*n ≤ x by omega)
  have hy0 : 0 ≤ ((30*n : ℕ) : ℝ) := by positivity
  have l3 := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi ((30*n : ℕ) : ℝ)
  have q2 := Chebyshev.psi_le_const_mul_self (Real.rpow_nonneg hy0 (2⁻¹ : ℝ))
  have q3 := Chebyshev.psi_le_const_mul_self (Real.rpow_nonneg hy0 (3⁻¹ : ℝ))
  have q5 := Chebyshev.psi_le_const_mul_self (Real.rpow_nonneg hy0 (5⁻¹ : ℝ))
  have r2 : ((30*n : ℕ) : ℝ) ^ (2⁻¹ : ℝ) ≤ (x:ℝ) ^ (2⁻¹ : ℝ) := Real.rpow_le_rpow hy0 hyX (by norm_num)
  have r3 : ((30*n : ℕ) : ℝ) ^ (3⁻¹ : ℝ) ≤ (x:ℝ) ^ (3⁻¹ : ℝ) := Real.rpow_le_rpow hy0 hyX (by norm_num)
  have r5 : ((30*n : ℕ) : ℝ) ^ (5⁻¹ : ℝ) ≤ (x:ℝ) ^ (5⁻¹ : ℝ) := Real.rpow_le_rpow hy0 hyX (by norm_num)
  obtain ⟨r3', r5'⟩ := root_le (x:ℝ) hX0
  have s0 : 0 ≤ (x:ℝ) ^ (2⁻¹ : ℝ) := Real.rpow_nonneg (by linarith) _
  have s2 : ((x:ℝ) ^ (2⁻¹ : ℝ)) ^ 2 = (x:ℝ) := by
    exact_mod_cast Real.rpow_inv_natCast_pow (by linarith : (0:ℝ) ≤ (x:ℝ)) (n := 2) (by norm_num)
  set s := (x:ℝ) ^ (2⁻¹ : ℝ) with hs
  have s547 : 547 ≤ s := by nlinarith
  have lt2 := Real.log_two_lt_d9
  have gt2 := Real.log_two_gt_d9
  have log4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  have log30 : Real.log 30 ≤ 5 * Real.log 2 := by
    have := Real.log_le_log (by norm_num) (show (30:ℝ) ≤ 2^5 by norm_num)
    rw [Real.log_pow] at this
    exact_mod_cast this
  have hC : Real.log 4 + 4 ≤ 5.3863 := by linarith
  have ln1 : Real.log (n:ℝ) ≤ Real.log (x:ℝ) :=
    Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero n1) (by exact_mod_cast (show n ≤ x by omega))
  have ln2 : Real.log (x:ℝ) = 2 * Real.log s := by rw [← s2, Real.log_pow]; norm_num
  have ln3 : Real.log (s / 64) ≤ s / 64 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have ln4 : Real.log (s / 64) = Real.log s - 6 * Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num), show (64:ℝ) = 2^6 by norm_num, Real.log_pow]; norm_num
  have E : Chebyshev.psi ((30*n : ℕ) : ℝ) - Chebyshev.theta ((30*n : ℕ) : ℝ) ≤ 5.3863 * (s + s/7 + s/30) := by
    have a2 : (Real.log 4 + 4) * ((30*n : ℕ) : ℝ) ^ (2⁻¹ : ℝ) ≤ 5.3863 * s :=
      mul_le_mul hC r2 (Real.rpow_nonneg hy0 _) (by norm_num)
    have a3 : (Real.log 4 + 4) * ((30*n : ℕ) : ℝ) ^ (3⁻¹ : ℝ) ≤ 5.3863 * (s/7) :=
      mul_le_mul hC (r3.trans r3') (Real.rpow_nonneg hy0 _) (by norm_num)
    have a5 : (Real.log 4 + 4) * ((30*n : ℕ) : ℝ) ^ (5⁻¹ : ℝ) ≤ 5.3863 * (s/30) :=
      mul_le_mul hC (r5.trans r5') (Real.rpow_nonneg hy0 _) (by norm_num)
    linarith
  have i1 : (x:ℝ) ≤ 30 * (n:ℝ) + 29 := by exact_mod_cast (show x ≤ 30*n + 29 by omega)
  have i2 : 60 * (m1:ℝ) ≤ (x:ℝ) + 60 := by exact_mod_cast (show 60*m1 ≤ x + 60 by omega)
  have i3 : 6 * (m2:ℝ) ≤ m1 + 6 := by exact_mod_cast (show 6*m2 ≤ m1 + 6 by omega)
  have i4 : 6 * (m3:ℝ) ≤ m2 + 6 := by exact_mod_cast (show 6*m3 ≤ m2 + 6 by omega)
  have i5 : 2 * (h:ℝ) ≤ (x:ℝ) := by exact_mod_cast (show 2*h ≤ x by omega)
  have hL := Lc_lo
  have D : 29 * (x:ℝ) / 2160 - 4.34 ≤ (n:ℝ) - m1 - m2 - m3 := by linarith
  have DL : (29 * (x:ℝ) / 2160 - 4.34) * 27.637 ≤ ((n:ℝ) - m1 - m2 - m3) * Lc :=
    mul_le_mul D hL (by norm_num) (by linarith)
  have M3 : (m3:ℝ) * Real.log 2 ≤ ((x:ℝ) / 2160 + 2) * 0.6931471808 :=
    mul_le_mul (by linarith) lt2.le (by linarith) (by positivity)
  have H : (h:ℝ) * Real.log 2 ≤ ((x:ℝ) / 2) * 0.6931471808 :=
    mul_le_mul (by linarith) lt2.le (by linarith) (by positivity)
  have T : Chebyshev.theta (30*n : ℕ) ≥ (n:ℝ) * Lc - Real.log 30 / 2 - Real.log n / 2 - 3
      - 5.3863 * (s + s/7 + s/30) := by linarith
  have U : Chebyshev.theta h ≤ ((m1:ℝ) + m2 + m3) * Lc + 6 + 10 * (m3 * Real.log 2) := by
    push_cast at u0 u1 u2 u3 u4 u5 u6
    rw [log4] at u6
    linarith
  have F : (x:ℝ) = s * s := by rw [← s2]; ring
  have Q : 547 * s ≤ (x:ℝ) := by rw [F]; exact mul_le_mul_of_nonneg_right s547 s0
  linarith

theorem big_range (x : ℕ) (hx : 300000 ≤ x) : 2^(x/2) ≤ g (x/2) x := by
  have t := theta_big x hx
  rw [← log_g (by omega), ← Real.log_pow] at t
  have := (Real.log_le_log_iff (by positivity) (by exact_mod_cast g_pos _ _)).mp t
  exact_mod_cast this
end OMA.StepCheb30

theorem OMA.solution : OMA.R_oeis_a082871_R1_H2_R1.H1 := by
  intro x hx
  by_cases h : x < 300000
  · exact OMA.StepCheb30.finite_range x hx h
  · exact OMA.StepCheb30.big_range x (by omega)

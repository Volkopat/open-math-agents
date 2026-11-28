import OMAStatements.S_oeis_a003327

-- Reduction oeis-a003327.R1
-- Credit: @Pixelstorm44

namespace OMA.R_oeis_a003327_R1

open OMA.S_oeis_a003327 (IsSumOfFourPositiveCubes)

/-- Expansion for a pair with midpoint m + e/2 and root gap 2u + e. -/
private theorem expand_pair (m u e : ℕ) (h : u < m) :
    (m-u)^3 + (m+u+e)^3 =
      m^3 + (m+e)^3 + 3*(2*m+e)*u*(u+e) := by
  have hm := Nat.sub_add_cancel h.le
  generalize m-u = a at *
  rw [← hm]
  ring

private theorem pair_coordinates (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ∃ m u : ℕ, u < m ∧ a^3 + b^3 =
      m^3 + (m+(a+b)%2)^3 + 3*(2*m+(a+b)%2)*u*(u+(a+b)%2) := by
  wlog hab : a ≤ b generalizing a b
  · simpa only [Nat.add_comm b a, Nat.add_comm (b^3) (a^3)] using
      this b a hb ha (by omega)
  let u := (b-a)/2
  have hg : b = a + 2*u + (a+b)%2 := by dsimp [u]; omega
  refine ⟨a+u, u, by omega, ?_⟩
  calc
    _ = a^3 + (a+2*u+(a+b)%2)^3 := congrArg (fun t => a^3+t^3) hg
    _ = _ := by ring

private theorem cube_parity (a : ℕ) : a^3 % 2 = a % 2 := by
  calc
    _ = (a%2)^3 % 2 := Nat.pow_mod ..
    _ = _ := by rcases (show a%2 = 0 ∨ a%2 = 1 by omega) with h | h <;> rw [h]

/-- Among three roots, two have the same parity. Pair those first. -/
private theorem arrange_pairs {n : ℕ} (hn : IsSumOfFourPositiveCubes n) :
    ∃ a b c d : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ (a+b)%2 = 0 ∧
      n = (a^3+b^3) + (c^3+d^3) := by
  obtain ⟨a,b,c,d,ha,hb,hc,hd,rfl⟩ := hn
  by_cases hab : (a+b)%2 = 0
  · exact ⟨a,b,c,d,ha,hb,hc,hd,hab, by ac_rfl⟩
  by_cases hac : (a+c)%2 = 0
  · exact ⟨a,c,b,d,ha,hc,hb,hd,hac, by ac_rfl⟩
  exact ⟨b,c,a,d,hb,hc,ha,hd,by omega, by ac_rfl⟩

/-- Exact bounded quadratic test. The second pair has an integral or half-integral
midpoint according to the parity of n. The strict bounds ensure positive roots. -/
theorem coordinates_iff (n : ℕ) : IsSumOfFourPositiveCubes n ↔
    ∃ m k u v : ℕ, u < m ∧ v < k ∧
      n = 2*m^3 + k^3 + (k+n%2)^3 + 6*m*u^2 +
        3*(2*k+n%2)*v*(v+n%2) := by
  constructor
  · intro hn
    obtain ⟨a,b,c,d,ha,hb,hc,hd,hab,he⟩ := arrange_pairs hn
    have hcd : (c+d)%2 = n%2 := by
      have := cube_parity a
      have := cube_parity b
      have := cube_parity c
      have := cube_parity d
      omega
    obtain ⟨m,u,hu,hm⟩ := pair_coordinates a b ha hb
    obtain ⟨k,v,hv,hk⟩ := pair_coordinates c d hc hd
    rw [hab] at hm
    rw [hcd] at hk
    exact ⟨m,k,u,v,hu,hv, by calc
      n = _ := he
      _ = _ := by rw [hm,hk]; ring⟩
  · rintro ⟨m,k,u,v,hu,hv,hn⟩
    refine ⟨m-u,m+u,k-v,k+v+n%2,by omega,by omega,by omega,by omega,?_⟩
    have hm := expand_pair m u 0 hu
    have hk := expand_pair k v (n%2) hv
    simp only [Nat.add_zero] at hm
    calc
      n = _ := hn
      _ = ((m-u)^3+(m+u)^3) + ((k-v)^3+(k+v+n%2)^3) := by rw [hm,hk]; ring
      _ = _ := by ac_rfl

/-- Explicit witnesses for the first 64 integers above the conjectural cutoff. -/
private theorem initial_window (n : ℕ) (lo : 7373170279850 < n) (hi : n ≤ 7373170279914) :
    IsSumOfFourPositiveCubes n := by
  let roots : List (ℕ × ℕ × ℕ × ℕ) := [
    (69, 494, 671, 19463),
    (159, 413, 2892, 19442),
    (391, 401, 1370, 19461),
    (84, 922, 1241, 19461),
    (391, 443, 1366, 19461),
    (73, 160, 748, 19463),
    (205, 1941, 2242, 19447),
    (28, 1960, 2911, 19435),
    (1523, 2246, 4655, 19361),
    (404, 485, 624, 19463),
    (509, 791, 977, 19462),
    (159, 176, 2118, 19455),
    (66, 335, 2344, 19452),
    (729, 1465, 1815, 19455),
    (468, 481, 1104, 19462),
    (868, 1719, 2980, 19435),
    (667, 1876, 4639, 19369),
    (1289, 2285, 4865, 19349),
    (800, 1437, 1928, 19454),
    (1973, 2001, 3828, 19400),
    (42, 164, 748, 19463),
    (210, 357, 1700, 19459),
    (369, 1186, 2506, 19448),
    (631, 1864, 1942, 19451),
    (490, 1152, 1492, 19459),
    (25, 1312, 2347, 19450),
    (779, 2135, 14954, 15899),
    (398, 479, 630, 19463),
    (335, 496, 641, 19463),
    (210, 1496, 1712, 19456),
    (385, 611, 1525, 19460),
    (373, 600, 1344, 19461),
    (11, 190, 2275, 19453),
    (555, 592, 1057, 19462),
    (259, 1930, 3379, 19423),
    (404, 1286, 9893, 18569),
    (560, 824, 1751, 19458),
    (153, 162, 746, 19463),
    (750, 824, 833, 19462),
    (258, 345, 1145, 19462),
    (808, 1223, 1377, 19459),
    (274, 310, 1383, 19461),
    (67, 1840, 2161, 19449),
    (145, 1939, 6385, 19225),
    (737, 1496, 1517, 19457),
    (719, 806, 4592, 19377),
    (620, 1353, 1502, 19458),
    (101, 465, 685, 19463),
    (1532, 2106, 3594, 19411),
    (594, 1475, 1705, 19456),
    (205, 496, 2267, 19453),
    (394, 643, 1668, 19459),
    (154, 2119, 7246, 19114),
    (1418, 2057, 3767, 19406),
    (1721, 1739, 2190, 19445),
    (447, 455, 621, 19463),
    (290, 312, 1700, 19459),
    (113, 472, 1694, 19459),
    (34, 974, 1210, 19461),
    (1080, 1372, 1783, 19455),
    (4, 936, 2431, 19450),
    (1636, 2266, 5368, 19312),
    (92, 968, 1850, 19457),
    (1370, 1895, 2579, 19440)]
  let row (i : Fin 64) := roots.getD i.val (0,0,0,0)
  have checked : ∀ i : Fin 64,
      0 < (row i).1 ∧ 0 < (row i).2.1 ∧ 0 < (row i).2.2.1 ∧ 0 < (row i).2.2.2 ∧
      7373170279851 + i.val =
        (row i).1^3 + (row i).2.1^3 + (row i).2.2.1^3 + (row i).2.2.2^3 := by
    decide
  let i : Fin 64 := ⟨n-7373170279851, by omega⟩
  have he : 7373170279851 + i.val = n := by dsimp [i]; omega
  exact ⟨(row i).1,(row i).2.1,(row i).2.2.1,(row i).2.2.2,he ▸ checked i⟩

/-- Even targets give a diagonal binary quadratic form in the two half-gaps.
Only targets without a smaller above-cutoff cube quotient require a search. -/
def H1 : Prop :=
  ∀ n : ℕ, 7373170279914 < n → n % 2 = 0 →
    (∀ q d : ℕ, 1 < d → n = q*d^3 → q ≤ 7373170279850) →
    ∃ m k u v : ℕ, u < m ∧ v < k ∧
      n / 2 = m^3 + k^3 + 3*(m*u^2 + k*v^2)

/-- At odd targets the second pair has an odd gap, giving v(v+1). -/
def H2 : Prop :=
  ∀ n : ℕ, 7373170279914 < n → n % 2 = 1 →
    (∀ q d : ℕ, 1 < d → n = q*d^3 → q ≤ 7373170279850) →
    ∃ m k u v : ℕ, u < m ∧ v < k ∧
      n = 2*m^3 + k^3 + (k+1)^3 + 6*m*u^2 + 3*(2*k+1)*v*(v+1)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a003327.main := by
  intro evenCase oddCase n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases small : n ≤ 7373170279914
    · exact initial_window n hn small
    by_cases primitive : ∀ q d : ℕ, 1 < d → n = q*d^3 → q ≤ 7373170279850
    · apply (coordinates_iff n).2
      by_cases even : n%2 = 0
      · obtain ⟨m,k,u,v,hu,hv,he⟩ := evenCase n (by omega) even primitive
        refine ⟨m,k,u,v,hu,hv,?_⟩
        rw [even]
        calc
          n = 2*(n/2) := by omega
          _ = _ := by rw [he]; ring
      · have odd : n%2 = 1 := by omega
        rw [odd]
        exact oddCase n (by omega) odd primitive
    · push_neg at primitive
      obtain ⟨q,d,hd,he,hq⟩ := primitive
      have hc : 1 < d^3 := one_lt_pow₀ hd (by decide)
      have hlt : q < n := by
        rw [he]
        simpa using Nat.mul_lt_mul_of_pos_left hc (by omega : 0 < q)
      obtain ⟨a,b,c,e,ha,hb,hc',he',hrep⟩ := ih q hlt hq
      refine ⟨a*d,b*d,c*d,e*d,by positivity,by positivity,by positivity,by positivity,?_⟩
      rw [he,hrep]
      ring

end OMA.R_oeis_a003327_R1

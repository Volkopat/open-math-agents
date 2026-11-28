import OMAReductions.R_OeisA78680_conjecture_R1_H1_R1

/-!
# Divisor certificates and Pépin tests for the Fermat tail

Each pair below gives an index and a proper factor from the FermatSearch list
(https://www.fermatsearch.org/factors/faclist.php). The kernel checks each
residue by repeated squaring. The remaining two tasks are the published
Pépin computations for F20 and F24 and a bounded divisor search at each
remaining index from 33 onwards. The two directions of the respective tests
are included to identify precisely what each certificate establishes.
-/
namespace OMA.R_OeisA78680_conjecture_R1_H1_R1_H2_R1
open Nat

/-- Repeated squaring with reduction at each step. -/
theorem squares_mod (d t x : ℕ) :
    ((fun y : ℕ => y*y % d)^[t]) (x % d) = x ^ (2^t) % d := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ, pow_mul, pow_two, ← Nat.mul_mod]

theorem pepin_iff {n : ℕ} (hn : 0 < n) :
    (fermatNumber n).Prime ↔
    (3 : ZMod (fermatNumber n)) ^ ((fermatNumber n-1)/2) = -1 := by
  refine ⟨fun hp => ?_, Nat.pepin_primality' n⟩
  let p := fermatNumber n
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have h4 : p % 4 = 1 := by
    have two : 2 ≤ 2 ^ (j+1) := by rw [pow_succ]; have := Nat.one_le_two_pow (n := j); omega
    have hd : 4 ∣ 2 ^ (2 ^ (j+1)) := pow_dvd_pow 2 two
    change (2 ^ (2 ^ (j+1)) + 1) % 4 = 1
    omega
  have h3 : p % 3 = 2 := by
    change (2 ^ (2 ^ (j+1)) + 1) % 3 = 2
    rw [pow_succ, Nat.mul_comm (2^j) 2, pow_mul]
    rw [Nat.add_mod, Nat.pow_mod]
    norm_num
  have sym : legendreSym p 3 = -1 := by
    rw [show (3:ℤ) = (3:ℕ) by rfl, ← legendreSym.quadratic_reciprocity_one_mod_four h4 (by decide : 3 ≠ 2),
      legendreSym.mod]
    rw_mod_cast [h3]
    decide
  have he := legendreSym.eq_pow p 3
  rw [sym] at he
  change (3 : ZMod p) ^ ((p-1)/2) = -1
  rw [show (p-1)/2 = p/2 by omega]
  simpa using he.symm

theorem pepin_residue {n : ℕ} (hn : 0 < n) :
    (fermatNumber n).Prime ↔
    ((fun y : ℕ => y*y % fermatNumber n)^[2^n-1]) (3 % fermatNumber n) = fermatNumber n - 1 := by
  have hF := Nat.two_lt_fermatNumber n
  let : NeZero (fermatNumber n) := ⟨by omega⟩
  have e : (fermatNumber n-1)/2 = 2^(2^n-1) := by
    simp only [fermatNumber, Nat.add_sub_cancel]
    have h := Nat.one_le_two_pow (n := n)
    conv_lhs => rw [show 2^n = (2^n-1)+1 by omega, pow_succ, Nat.mul_div_cancel _ (by decide : 0<2)]
  rw [pepin_iff hn, e, squares_mod, ← (ZMod.val_injective (fermatNumber n)).eq_iff]
  change ((↑(3 : ℕ) : ZMod (fermatNumber n)) ^ _).val = _ ↔ _
  rw [← Nat.cast_pow, ZMod.val_natCast]
  rw [show (-1 : ZMod (fermatNumber n)).val = fermatNumber n-1 from
    ZMod.val_neg_one (2^(2^n))]

/-- Checking a residue against a candidate divisor only needs n modular squarings. -/
theorem divisor_iff {n d : ℕ} (hd : 1 < d) :
    d ∣ fermatNumber n ↔ ((fun y : ℕ => y*y % d)^[n]) (2 % d) = d-1 := by
  rw [fermatNumber, Nat.dvd_iff_mod_eq_zero, squares_mod, Nat.add_mod,
    Nat.mod_eq_of_lt (show 1 < d from hd)]
  have h := Nat.mod_lt (2 ^ (2 ^ n)) (by omega : 0 < d)
  constructor
  · intro he
    by_contra! ne
    have hs : 2 ^ (2 ^ n) % d + 1 < d := by omega
    rw [Nat.mod_eq_of_lt hs] at he
    omega
  · intro he
    rw [he, Nat.sub_add_cancel (by omega), Nat.mod_self]

/-- A composite Fermat number has a Lucas-form factor at most its square root. -/
theorem small_factor_iff {n : ℕ} (hn : 1 < n) :
    ¬(fermatNumber n).Prime ↔ ∃ t : ℕ, let d := t * 2^(n+2) + 1
      1 < d ∧ d^2 ≤ fermatNumber n ∧ ((fun y : ℕ => y*y % d)^[n]) (2 % d) = d-1 := by
  have hf := Nat.two_lt_fermatNumber n
  constructor
  · intro hc
    let d := (fermatNumber n).minFac
    have hp : d.Prime := Nat.minFac_prime (by omega)
    have hd : d ∣ fermatNumber n := Nat.minFac_dvd _
    obtain ⟨t, ht⟩ := Nat.fermat_primeFactors_one_lt n d hn hp hd
    refine ⟨t, ?_⟩
    dsimp only
    rw [← ht]
    exact ⟨hp.one_lt, Nat.minFac_sq_le_self (by omega) hc, (divisor_iff hp.one_lt).mp hd⟩
  · rintro ⟨t, ht, hs, hr⟩
    exact Nat.not_prime_of_dvd_of_lt ((divisor_iff ht).mpr hr) ht
      ((lt_self_pow₀ ht (by decide : 1 < 2)).trans_le hs)


/-- Each index has a proper factor whose residue is verified by the kernel. -/
theorem table_composite {n : ℕ} (hin : n ∈ [21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32, 36, 37, 38, 39, 40, 42, 43, 48, 52, 55, 58, 61,
    62, 63, 64, 65, 66, 71, 72, 73, 75, 77, 81, 83, 86, 88, 90, 91, 93, 94, 96, 99, 103, 107,
    116, 117, 118, 122, 125, 132, 133, 142, 144, 146, 147, 150, 160, 164, 166, 172, 178, 184,
    195, 201, 205, 207, 215, 226, 228, 230, 232, 250, 251, 255]) :
    ¬(fermatNumber n).Prime := by
  let factors : List (ℕ × ℕ) := [
  (21, 4485296422913),
  (22, 64658705994591851009055774868504577),
  (23, 167772161),
  (25, 25991531462657),
  (26, 76861124116481),
  (27, 151413703311361),
  (28, 1766730974551267606529),
  (29, 2405286912458753),
  (30, 640126220763137),
  (31, 46931635677864055013377),
  (32, 25409026523137),
  (36, 2748779069441),
  (37, 701179711390136401921),
  (38, 6597069766657),
  (39, 46179488366593),
  (40, 326895348124320718380574179329),
  (42, 1529992420282859521),
  (43, 7482850493766970889994241),
  (48, 2408911986953445595315961857),
  (52, 74201307460556292097),
  (55, 4179340454199820289),
  (58, 219055085875300925441),
  (61, 4057181540151185357230047233),
  (62, 12857380619375557476353),
  (63, 1328165573307087716353),
  (64, 2634732075339197803231444993),
  (65, 357393347081793620781479724788482049),
  (66, 4457323664018586376077313),
  (71, 6450752615599935361908737),
  (72, 1443765874709062348345951911937),
  (73, 188894659314785808547841),
  (75, 520961043404985083798310879233),
  (77, 256896736668108699625062401),
  (81, 5241902353849032101525979137),
  (83, 246947940268608417020015902258307792897),
  (86, 6195449970597928748332522715641578258433),
  (88, 148481934042154969241780501829489000449),
  (90, 985016348367230226078056532654006730753),
  (91, 14072902366596202965053244178433),
  (93, 7316007754729683197725441917976577),
  (94, 76459067246115642538831634131564386844673),
  (96, 8453027931784477309850388309101819121893377),
  (99, 329244355096077565991935730125897729),
  (103, 308096120572890968848095925369777111595921440769),
  (107, 3346902437331832346018436558958369334886401),
  (116, 4563438810603420826872624280490561141381005313),
  (117, 9304595970494411110326649421962412033),
  (118, 2030912570882086247957711831528946513898296129355777),
  (122, 111331351706159727817280425663664652445286401),
  (125, 850705917302346158658436518579420528641),
  (132, 46842071212744845599962218807393559947324348854918184961),
  (133, 3836232386548105510567872577199319351015739156856833),
  (142, 363618066009591119386121910507749518730588867002369),
  (144, 3032901347000164747248857685080177164813336577),
  (146, 13235038053749721162769301995307025251972223086886913),
  (147, 2230074519853062314153571827264836150598041600001),
  (150, 124204803210043452689216278205372864748572142206977),
  (160, 1014636747094880794614972066871046493126084253283324393917775873),
  (164, 343390041044181900054983258125842173093877961821829176754177),
  (166, 8005705634611551271269985633916919970948098093294822472135213057),
  (172, 492544145925433733451855533863925475950550777193174123310743553),
  (178, 479744144560996421795040836675707785358665797968769873751310337),
  (184, 22953190542224652377639611826608942557783370967811443134226759681),
  (195, 9761213910603494986281795830720869047027739722070601061612088452553113601),
  (201, 124569837190956926160012901398286924947521176078042100592562667521),
  (205, 47905779865361936656012887182939964920375512098173614759150973091841),
  (207, 2468256835981809063232453773836025757474103798450369795022913537),
  (215, 6763365995538079644113691573900682504384080816814065022974359599316993),
  (226, 12940774400232307101440167241769422723345829322819474790929732919623681),
  (228, 100075322028463174917803960003016869060541080096470605049856601245089793),
  (230, 2569079122613327940664251164321869487190059887122386310274973217735004454387713),
  (232, 7829316209512367114436352285045953475968909194037786694784768894390715704934401),
  (250, 2916513247664901672231194184906326679054237738765821706743837897199311952805889),
  (251, 2483788281013398950069551842716895472418469388169137840250018522273911908790580543489),
  (255, 145666448260543773842852299140929388079413640709375829561637640681954717087039489)]
  have cert : ∀ row ∈ factors, 10 ≤ row.1 ∧ 1 < row.2 ∧ row.2 < fermatNumber 10 ∧
      ((fun y : ℕ => y*y % row.2)^[row.1]) (2 % row.2) = row.2-1 := by decide +kernel
  change n ∈ factors.map Prod.fst at hin
  obtain ⟨⟨m,d⟩, hr, rfl⟩ := List.mem_map.mp hin
  obtain ⟨hm, hd, hlt, he⟩ := cert _ hr
  exact Nat.not_prime_of_dvd_of_lt ((divisor_iff hd).mpr he) hd
    (hlt.trans_le (fermatNumber_mono hm))

/-- The two published Pépin computations without known proper factors. -/
def H1 : Prop := ∀ n ∈ [20, 24],
  ((fun y : ℕ => y*y % fermatNumber n)^[2^n-1]) (3 % fermatNumber n) ≠ fermatNumber n-1

/-- A Lucas-form divisor at most the square root, for each uncovered later index. -/
def H2 : Prop := ∀ n : ℕ, 33 ≤ n → n ∉ [21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32, 36, 37, 38, 39, 40, 42, 43, 48, 52, 55, 58, 61,
    62, 63, 64, 65, 66, 71, 72, 73, 75, 77, 81, 83, 86, 88, 90, 91, 93, 94, 96, 99, 103, 107,
    116, 117, 118, 122, 125, 132, 133, 142, 144, 146, 147, 150, 160, 164, 166, 172, 178, 184,
    195, 201, 205, 207, 215, 226, 228, 230, 232, 250, 251, 255] →
  ∃ t : ℕ, let d := t * 2^(n+2) + 1
    1 < d ∧ d^2 ≤ fermatNumber n ∧ ((fun y : ℕ => y*y % d)^[n]) (2 % d) = d-1

theorem main : H1 → H2 → OMA.R_OeisA78680_conjecture_R1_H1_R1.H2 := by
  intro tests large n hn hp
  have miss := fun hit => table_composite (n := n) hit hp
  by_cases late : 33 ≤ n
  · exact (small_factor_iff (by omega)).mpr (large n late miss) hp
  have special : n = 20 ∨ n = 24 := by
    by_contra! hx
    have upper : n ≤ 32 := by omega
    apply miss
    interval_cases n <;> first | omega | decide
  exact tests n (by rcases special with rfl | rfl <;> decide)
    ((pepin_residue (by omega)).mp hp)

end OMA.R_OeisA78680_conjecture_R1_H1_R1_H2_R1

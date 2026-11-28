import OMAStatements.S_oeis_a226751

-- Problem: A226751: G.f.: 1 / (1 + 6*x*G(x) - 7*x*G(x)^2), where G(x) = 1 + x*G(x)^3 is the g.f. of A001764.
-- Upstream: formal-conjectures statements/oeis-a226751.lean:0 (declaration OMA.S_oeis_a226751.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A226751Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (11 : ℚ⟦X⟧) * G + (24 - 162 * X : ℚ⟦X⟧) * G ^ 2 + (-36 + 211 * X + 216 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    (1980 * X ^ 3 - 11605 * X ^ 4 - 11880 * X ^ 5) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (2214 * X ^ 2 - 41109 * X ^ 3 - 78624 * X ^ 4) * derivative ℚ (derivative ℚ G) + (-378 * X - 16542 * X ^ 2 - 103872 * X ^ 3) * derivative ℚ G + (582 * X - 17088 * X ^ 2) * G =
      204 * X := by
  have d11 : derivative ℚ (11 : ℚ⟦X⟧) = 0 := dnum 11
  have d24 : derivative ℚ (24 : ℚ⟦X⟧) = 0 := dnum 24
  have d36 : derivative ℚ (36 : ℚ⟦X⟧) = 0 := dnum 36
  have d48 : derivative ℚ (48 : ℚ⟦X⟧) = 0 := dnum 48
  have d108 : derivative ℚ (108 : ℚ⟦X⟧) = 0 := dnum 108
  have d162 : derivative ℚ (162 : ℚ⟦X⟧) = 0 := dnum 162
  have d211 : derivative ℚ (211 : ℚ⟦X⟧) = 0 := dnum 211
  have d216 : derivative ℚ (216 : ℚ⟦X⟧) = 0 := dnum 216
  have d324 : derivative ℚ (324 : ℚ⟦X⟧) = 0 := dnum 324
  have d432 : derivative ℚ (432 : ℚ⟦X⟧) = 0 := dnum 432
  have d633 : derivative ℚ (633 : ℚ⟦X⟧) = 0 := dnum 633
  have d648 : derivative ℚ (648 : ℚ⟦X⟧) = 0 := dnum 648
  have d1266 : derivative ℚ (1266 : ℚ⟦X⟧) = 0 := dnum 1266
  have d1296 : derivative ℚ (1296 : ℚ⟦X⟧) = 0 := dnum 1296
  have d2592 : derivative ℚ (2592 : ℚ⟦X⟧) = 0 := dnum 2592
  have hp0 : (1 : ℚ⟦X⟧) + (11 : ℚ⟦X⟧) * G + (24 - 162 * X : ℚ⟦X⟧) * G * G + (-36 + 211 * X + 216 * (X * X) : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((1 : ℚ⟦X⟧) + (11 : ℚ⟦X⟧) * G + (24 - 162 * X : ℚ⟦X⟧) * G * G + (-36 + 211 * X + 216 * (X * X) : ℚ⟦X⟧) * G * G * G) =
      (11 : ℚ⟦X⟧) * (derivative ℚ G) + (48 - 324 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (-162 : ℚ⟦X⟧) * G ^ 2 + (-108 + 633 * X + 648 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (211 + 432 * X : ℚ⟦X⟧) * G ^ 3 := by
    simp [Derivation.leibniz, d11, d24, d36, d162, d211, d216]
    ring
  have hd1 : (11 : ℚ⟦X⟧) * (derivative ℚ G) + (48 - 324 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (-162 : ℚ⟦X⟧) * G ^ 2 + (-108 + 633 * X + 648 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (211 + 432 * X : ℚ⟦X⟧) * G ^ 3 = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (11 : ℚ⟦X⟧) * (derivative ℚ G) + (48 - 324 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (-162 : ℚ⟦X⟧) * G * G + (-108 + 633 * X + 648 * (X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (211 + 432 * X : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((11 : ℚ⟦X⟧) * (derivative ℚ G) + (48 - 324 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (-162 : ℚ⟦X⟧) * G * G + (-108 + 633 * X + 648 * (X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (211 + 432 * X : ℚ⟦X⟧) * G * G * G) =
      (11 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (48 - 324 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (48 - 324 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-648 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-216 + 1266 * X + 1296 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-108 + 633 * X + 648 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (1266 + 2592 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (432 : ℚ⟦X⟧) * G ^ 3 := by
    simp [Derivation.leibniz, d11, d48, d108, d162, d211, d324, d432, d633, d648]
    ring
  have hd2 : (11 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (48 - 324 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (48 - 324 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-648 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-216 + 1266 * X + 1296 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-108 + 633 * X + 648 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (1266 + 2592 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (432 : ℚ⟦X⟧) * G ^ 3 = 0 := by rw [← hL2, hp1, map_zero]
  have hp2 : (11 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (48 - 324 * X : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ G) + (48 - 324 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-648 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-216 + 1266 * X + 1296 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ G) + (-108 + 633 * X + 648 * (X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ (derivative ℚ G)) + (1266 + 2592 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (432 : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hd2
  have hL3 : derivative ℚ ((11 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (48 - 324 * X : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ G) + (48 - 324 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-648 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-216 + 1266 * X + 1296 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ G) + (-108 + 633 * X + 648 * (X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ (derivative ℚ G)) + (1266 + 2592 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (432 : ℚ⟦X⟧) * G * G * G) =
      (11 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (144 - 972 * X : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (-972 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-216 + 1266 * X + 1296 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 3 + (48 - 324 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-972 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-648 + 3798 * X + 3888 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (3798 + 7776 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-108 + 633 * X + 648 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (1899 + 3888 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (3888 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) := by
    simp [Derivation.leibniz, d11, d48, d108, d216, d324, d432, d633, d648, d1266, d1296, d2592]
    ring
  have hd3 : (11 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (144 - 972 * X : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (-972 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-216 + 1266 * X + 1296 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 3 + (48 - 324 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-972 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-648 + 3798 * X + 3888 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (3798 + 7776 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-108 + 633 * X + 648 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (1899 + 3888 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (3888 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) = 0 := by rw [← hL3, hp2, map_zero]
  have hfull : ((11 : ℚ⟦X⟧) + (48 - 324 * X : ℚ⟦X⟧) * G + (-108 + 633 * X + 648 * X ^ 2 : ℚ⟦X⟧) * G ^ 2) ^ 5 * ((1980 * X ^ 3 - 11605 * X ^ 4 - 11880 * X ^ 5) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (2214 * X ^ 2 - 41109 * X ^ 3 - 78624 * X ^ 4) * derivative ℚ (derivative ℚ G) + (-378 * X - 16542 * X ^ 2 - 103872 * X ^ 3) * derivative ℚ G + (582 * X - 17088 * X ^ 2) * G - (204 * X)) = 0 := by
    linear_combination ((-32854404 * X : ℚ⟦X⟧) + (-261693234 * X + 2086518192 * X ^ 2 : ℚ⟦X⟧) * G + (172569474 * X - 66356025384 * X ^ 2 - 135779760864 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 + (2817826704 * X + 8887956264 * X ^ 2 + 1439459372208 * X ^ 3 + 4044553108992 * X ^ 4 : ℚ⟦X⟧) * G ^ 3 + (-795591720 * X + 1063444333050 * X ^ 2 - 8418841897620 * X ^ 3 + 2986592510880 * X ^ 4 - 56573334195840 * X ^ 5 : ℚ⟦X⟧) * G ^ 4 + (1890477792 * X - 1746028839600 * X ^ 2 + 2974109578470 * X ^ 3 + 50983766110080 * X ^ 4 + 4683009453120 * X ^ 5 + 328926783066624 * X ^ 6 : ℚ⟦X⟧) * G ^ 5 + (-56386598688 * X - 2111641975296 * X ^ 2 + 63418602021570 * X ^ 3 - 446950309570680 * X ^ 4 + 1313840504119680 * X ^ 5 - 2799687493207296 * X ^ 6 - 236163469197312 * X ^ 7 : ℚ⟦X⟧) * G ^ 6 + (113555478528 * X + 6370316554752 * X ^ 2 - 123946566726528 * X ^ 3 + 765700193017440 * X ^ 4 - 2302420853214720 * X ^ 5 + 3223341787401216 * X ^ 6 + 4998343562993664 * X ^ 7 - 270826551115776 * X ^ 8 : ℚ⟦X⟧) * G ^ 7 + (-63874956672 * X - 3640080801312 * X ^ 2 + 66534785506296 * X ^ 3 - 368733075209046 * X ^ 4 + 912261633424560 * X ^ 5 - 661919328805824 * X ^ 6 - 4423239147884544 * X ^ 7 - 2346831846494208 * X ^ 8 + 135413275557888 * X ^ 9 : ℚ⟦X⟧) * G ^ 8) * hP +
      ((-5534298 * X - 242191422 * X ^ 2 - 1520789952 * X ^ 3 : ℚ⟦X⟧) + (-141448032 * X ^ 2 + 6142735368 * X ^ 3 - 27718639344 * X ^ 4 - 49275664416 * X ^ 5 : ℚ⟦X⟧) * (derivative ℚ G) + (2225219040 * X ^ 3 - 38734336080 * X ^ 4 + 209267819310 * X ^ 5 - 268052645520 * X ^ 6 - 432209986560 * X ^ 7 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-96598656 * X - 1665751824 * X ^ 2 - 33466163544 * X ^ 3 + 111364450560 * X ^ 4 : ℚ⟦X⟧) * G + (-1215167184 * X ^ 2 + 33820781148 * X ^ 3 - 401741970696 * X ^ 4 + 1062349521552 * X ^ 5 + 3254649590016 * X ^ 6 : ℚ⟦X⟧) * G * (derivative ℚ G) + (7000266240 * X ^ 3 - 239708937600 * X ^ 4 + 2847807309600 * X ^ 5 - 13666767265800 * X ^ 6 + 17467922419200 * X ^ 7 + 28479115399680 * X ^ 8 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-414935136 * X + 8287451172 * X ^ 2 - 166472321994 * X ^ 3 + 1964746217808 * X ^ 4 - 3580942913856 * X ^ 5 : ℚ⟦X⟧) * G ^ 2 + (4418789760 * X ^ 2 - 179670934080 * X ^ 3 + 1117032764760 * X ^ 4 + 2390141429280 * X ^ 5 - 9788131251360 * X ^ 6 - 75303290684160 * X ^ 7 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-81770705280 * X ^ 3 + 1949648991840 * X ^ 4 - 14570227009800 * X ^ 5 + 15527577834450 * X ^ 6 + 218885703418800 * X ^ 7 - 515133688037760 * X ^ 8 - 609719453291520 * X ^ 9 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (1005903360 * X + 43290567936 * X ^ 2 - 269480404512 * X ^ 3 + 2994226085664 * X ^ 4 - 32062093386048 * X ^ 5 + 58908552189696 * X ^ 6 : ℚ⟦X⟧) * G ^ 3 + (42219527616 * X ^ 2 - 846096163488 * X ^ 3 + 7037356209660 * X ^ 4 - 25601137754640 * X ^ 5 + 2563702183440 * X ^ 6 + 40074938479872 * X ^ 7 + 739769741835264 * X ^ 8 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (60600545280 * X ^ 3 + 1415819243520 * X ^ 4 - 60556050593280 * X ^ 5 + 619506916934400 * X ^ 6 - 2247563225437200 * X ^ 7 + 473725316972160 * X ^ 8 + 8103662697968640 * X ^ 9 + 4829387522826240 * X ^ 10 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) ^ 2 + (7208212032 * X - 174144787488 * X ^ 2 + 2419696306980 * X ^ 3 - 26191121003820 * X ^ 4 + 107057147955840 * X ^ 5 + 56896328271744 * X ^ 6 - 471559138891776 * X ^ 7 : ℚ⟦X⟧) * G ^ 4 + (-72307468800 * X ^ 2 + 2228905019520 * X ^ 3 - 29183706315360 * X ^ 4 + 211170247666200 * X ^ 5 - 891488095129800 * X ^ 6 + 1948936148035200 * X ^ 7 - 838169131484160 * X ^ 8 - 3060218563153920 * X ^ 9 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (1262080258560 * X ^ 3 - 43002183882240 * X ^ 4 + 556237739977920 * X ^ 5 - 3216774898861920 * X ^ 6 + 6212051320122450 * X ^ 7 + 10622832682817520 * X ^ 8 - 29442014045642880 * X ^ 9 - 48023690283740160 * X ^ 10 - 17921100687114240 * X ^ 11 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) ^ 2 + (-9876142080 * X - 192701037312 * X ^ 2 + 4363551098496 * X ^ 3 - 45994917996720 * X ^ 4 + 425762876276280 * X ^ 5 - 1964432446914240 * X ^ 6 + 2353776417040896 * X ^ 7 + 1544518492250112 * X ^ 8 : ℚ⟦X⟧) * G ^ 5 + (-351414298368 * X ^ 2 + 5659640932032 * X ^ 3 + 4048297780464 * X ^ 4 - 520546329983484 * X ^ 5 + 2964057068165940 * X ^ 6 - 3007293189872256 * X ^ 7 - 9290996997705216 * X ^ 8 + 555655617404928 * X ^ 9 + 3584141773258752 * X ^ 10 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (-3591690854400 * X ^ 3 + 108449109964800 * X ^ 4 - 1222488518169600 * X ^ 5 + 5792174097811200 * X ^ 6 - 5425308339818400 * X ^ 7 - 34379487245485800 * X ^ 8 + 32219799068793600 * X ^ 9 + 140758813545292800 * X ^ 10 + 118116345437798400 * X ^ 11 + 31420111594291200 * X ^ 12 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) ^ 2 + (-39998375424 * X + 1612418342976 * X ^ 2 - 27080984791008 * X ^ 3 + 275640690092868 * X ^ 4 - 1680213491823930 * X ^ 5 + 4719403359456192 * X ^ 6 - 1192477113727488 * X ^ 7 - 9505758494140416 * X ^ 8 - 2976780319432704 * X ^ 9 : ℚ⟦X⟧) * G ^ 6 + (937104795648 * X ^ 2 - 17853404368896 * X ^ 3 + 73610593834752 * X ^ 4 + 403600966206336 * X ^ 5 - 2698126140309912 * X ^ 6 - 1973125834357464 * X ^ 7 + 15924773101624128 * X ^ 8 + 30210042919371264 * X ^ 9 + 19861847984074752 * X ^ 10 + 4544808060911616 * X ^ 11 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (2693768140800 * X ^ 3 - 78942371904000 * X ^ 4 + 844566981984000 * X ^ 5 - 3529138227912000 * X ^ 6 + 207531856323000 * X ^ 7 + 29401487660659950 * X ^ 8 - 1245191137938000 * X ^ 9 - 127048976204832000 * X ^ 10 - 182426468108544000 * X ^ 11 - 102309313987584000 * X ^ 12 - 20946741062860800 * X ^ 13 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) ^ 2 + (91424858112 * X - 2527486156800 * X ^ 2 + 38409247429632 * X ^ 3 - 381857087628288 * X ^ 4 + 2085312699519264 * X ^ 5 - 4224312857389536 * X ^ 6 - 4562714031802560 * X ^ 7 + 14535660956742144 * X ^ 8 + 16866534539833344 * X ^ 9 + 4303603163824128 * X ^ 10 : ℚ⟦X⟧) * G ^ 7 + (-602424511488 * X ^ 2 + 11625831659520 * X ^ 3 - 57776124009600 * X ^ 4 - 68666004624960 * X ^ 5 + 400609281355380 * X ^ 6 + 3843616466991348 * X ^ 7 - 2561379898937760 * X ^ 8 - 34657716805056000 * X ^ 9 - 56842415095173120 * X ^ 10 - 36769641256304640 * X ^ 11 - 8581816338481152 * X ^ 12 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (-51426482688 * X + 1309062477312 * X ^ 2 - 18990200810304 * X ^ 3 + 187969300705728 * X ^ 4 - 982915461405666 * X ^ 5 + 1378792318663890 * X ^ 6 + 5065509180234384 * X ^ 7 - 6523395468726528 * X ^ 8 - 20047497405179904 * X ^ 9 - 14243431284006912 * X ^ 10 - 3224528624222208 * X ^ 11 : ℚ⟦X⟧) * G ^ 8) * hd1 +
      ((32415174 * X ^ 2 - 601876869 * X ^ 3 - 1151133984 * X ^ 4 : ℚ⟦X⟧) + (-379494720 * X ^ 3 + 4785850080 * X ^ 4 - 12736791540 * X ^ 5 - 15369536160 * X ^ 6 : ℚ⟦X⟧) * (derivative ℚ G) + (565792128 * X ^ 2 - 11762994672 * X ^ 3 + 35805758076 * X ^ 4 + 120254976864 * X ^ 5 : ℚ⟦X⟧) * G + (-3260204640 * X ^ 3 + 76166315280 * X ^ 4 - 551459134710 * X ^ 5 + 1044378094320 * X ^ 6 + 1419586248960 * X ^ 7 : ℚ⟦X⟧) * G * (derivative ℚ G) + (2430334368 * X ^ 2 - 59130961956 * X ^ 3 + 476019229257 * X ^ 4 - 548817031224 * X ^ 5 - 4843800352512 * X ^ 6 : ℚ⟦X⟧) * G ^ 2 + (11855289600 * X ^ 3 - 53395848000 * X ^ 4 - 2003108778000 * X ^ 5 + 18699470014500 * X ^ 6 - 36010442160000 * X ^ 7 - 48151105516800 * X ^ 8 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-5891719680 * X ^ 2 + 106763184000 * X ^ 3 + 14412103200 * X ^ 4 - 5488121806200 * X ^ 5 + 1935279799200 * X ^ 6 + 93481237175040 * X ^ 7 : ℚ⟦X⟧) * G ^ 3 + (113271903360 * X ^ 3 - 3000338146080 * X ^ 4 + 26426524152600 * X ^ 5 - 65636801292150 * X ^ 6 - 194947121595600 * X ^ 7 + 713161397013120 * X ^ 8 + 723635914890240 * X ^ 9 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-42219527616 * X ^ 2 + 1070666440848 * X ^ 3 - 9539984001060 * X ^ 4 + 25700077403415 * X ^ 5 + 58996393785360 * X ^ 6 - 136932308091072 * X ^ 7 - 872748770079744 * X ^ 8 : ℚ⟦X⟧) * G ^ 4 + (-193995648000 * X ^ 3 + 2010780288000 * X ^ 4 + 28820970288000 * X ^ 5 - 503350170840000 * X ^ 6 + 2186042088532500 * X ^ 7 - 829853624556000 * X ^ 8 - 8153699441184000 * X ^ 9 - 4727563087104000 * X ^ 10 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (57845975040 * X ^ 2 - 1159856029440 * X ^ 3 + 5096519559360 * X ^ 4 + 20481781921200 * X ^ 5 - 53946099800100 * X ^ 6 - 1086116061993120 * X ^ 7 + 3155571833137920 * X ^ 8 + 3615869464197120 * X ^ 9 : ℚ⟦X⟧) * G ^ 5 + (-942818849280 * X ^ 3 + 33078475077120 * X ^ 4 - 438751019424960 * X ^ 5 + 2597482338564960 * X ^ 6 - 5179319414096850 * X ^ 7 - 8484862177463760 * X ^ 8 + 24677613679213440 * X ^ 9 + 39746818294318080 * X ^ 10 + 14779089527685120 * X ^ 11 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (234276198912 * X ^ 2 - 6604278245568 * X ^ 3 + 67882213813104 * X ^ 4 - 259200125504964 * X ^ 5 - 239884629004485 * X ^ 6 + 3681696459427704 * X ^ 7 - 2653490226465216 * X ^ 8 - 13059483452923392 * X ^ 9 - 6956621939294208 * X ^ 10 : ℚ⟦X⟧) * G ^ 6 + (2514183598080 * X ^ 3 - 75914376975360 * X ^ 4 + 855741962718720 * X ^ 5 - 4054521868467840 * X ^ 6 + 3797715837872880 * X ^ 7 + 24065641071840060 * X ^ 8 - 22553859348155520 * X ^ 9 - 98531169481704960 * X ^ 10 - 82681441806458880 * X ^ 11 - 21994078116003840 * X ^ 12 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (-535488454656 * X ^ 2 + 14233254100992 * X ^ 3 - 134445877208064 * X ^ 4 + 451727233095168 * X ^ 5 + 430067551430304 * X ^ 6 - 4417225447048992 * X ^ 7 - 1052126233153056 * X ^ 8 + 15153784104989952 * X ^ 9 + 17702200190232576 * X ^ 10 + 5731790054473728 * X ^ 11 : ℚ⟦X⟧) * G ^ 7 + (-1616260884480 * X ^ 3 + 47365423142400 * X ^ 4 - 506740189190400 * X ^ 5 + 2117482936747200 * X ^ 6 - 124519113793800 * X ^ 7 - 17640892596395970 * X ^ 8 + 747114682762800 * X ^ 9 + 76229385722899200 * X ^ 10 + 109455880865126400 * X ^ 11 + 61385588392550400 * X ^ 12 + 12568044637716480 * X ^ 13 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (301212255744 * X ^ 2 - 7918045747200 * X ^ 3 + 73931634377280 * X ^ 4 - 247998055920480 * X ^ 5 - 178167909336570 * X ^ 6 + 1998390121258986 * X ^ 7 + 1081459367398800 * X ^ 8 - 6386950489040640 * X ^ 9 - 10496438982236160 * X ^ 10 - 6169414728867840 * X ^ 11 - 1294889447522304 * X ^ 12 : ℚ⟦X⟧) * G ^ 8) * hd2 +
      ((28989180 * X ^ 3 - 169908805 * X ^ 4 - 173935080 * X ^ 5 : ℚ⟦X⟧) + (505992960 * X ^ 3 - 6381133440 * X ^ 4 + 16982388720 * X ^ 5 + 20492714880 * X ^ 6 : ℚ⟦X⟧) * G + (2173469760 * X ^ 3 - 50777543520 * X ^ 4 + 367639423140 * X ^ 5 - 696252062880 * X ^ 6 - 946390832640 * X ^ 7 : ℚ⟦X⟧) * G ^ 2 + (-5269017600 * X ^ 3 + 23731488000 * X ^ 4 + 890270568000 * X ^ 5 - 8310875562000 * X ^ 6 + 16004640960000 * X ^ 7 + 21400491340800 * X ^ 8 : ℚ⟦X⟧) * G ^ 3 + (-37757301120 * X ^ 3 + 1000112715360 * X ^ 4 - 8808841384200 * X ^ 5 + 21878933764050 * X ^ 6 + 64982373865200 * X ^ 7 - 237720465671040 * X ^ 8 - 241211971630080 * X ^ 9 : ℚ⟦X⟧) * G ^ 4 + (51732172800 * X ^ 3 - 536208076800 * X ^ 4 - 7685592076800 * X ^ 5 + 134226712224000 * X ^ 6 - 582944556942000 * X ^ 7 + 221294299881600 * X ^ 8 + 2174319850982400 * X ^ 9 + 1260683489894400 * X ^ 10 : ℚ⟦X⟧) * G ^ 5 + (209515299840 * X ^ 3 - 7350772239360 * X ^ 4 + 97500226538880 * X ^ 5 - 577218297458880 * X ^ 6 + 1150959869799300 * X ^ 7 + 1885524928325280 * X ^ 8 - 5483914150936320 * X ^ 9 - 8832626287626240 * X ^ 10 - 3284242117263360 * X ^ 11 : ℚ⟦X⟧) * G ^ 6 + (-478892113920 * X ^ 3 + 14459881328640 * X ^ 4 - 162998469089280 * X ^ 5 + 772289879708160 * X ^ 6 - 723374445309120 * X ^ 7 - 4583931632731440 * X ^ 8 + 4295973209172480 * X ^ 9 + 18767841806039040 * X ^ 10 + 15748846058373120 * X ^ 11 + 4189348212572160 * X ^ 12 : ℚ⟦X⟧) * G ^ 7 + (269376814080 * X ^ 3 - 7894237190400 * X ^ 4 + 84456698198400 * X ^ 5 - 352913822791200 * X ^ 6 + 20753185632300 * X ^ 7 + 2940148766065995 * X ^ 8 - 124519113793800 * X ^ 9 - 12704897620483200 * X ^ 10 - 18242646810854400 * X ^ 11 - 10230931398758400 * X ^ 12 - 2094674106286080 * X ^ 13 : ℚ⟦X⟧) * G ^ 8) * hd3
  have k11 : constantCoeff (11 : ℚ⟦X⟧) = 11 := cnum 11
  have k48 : constantCoeff (48 : ℚ⟦X⟧) = 48 := cnum 48
  have k108 : constantCoeff (108 : ℚ⟦X⟧) = 108 := cnum 108
  have hPG : (11 : ℚ⟦X⟧) + (48 - 324 * X : ℚ⟦X⟧) * G + (-108 + 633 * X + 648 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0, k11, k48, k108] at h'
    norm_num at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 5 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (11 : ℚ⟦X⟧) * G + (24 - 162 * X : ℚ⟦X⟧) * G ^ 2 + (-36 + 211 * X + 216 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C 1980 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * C (-11605) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C (-11880) + derivative ℚ (derivative ℚ G) * X * X * C 2214 +
      derivative ℚ (derivative ℚ G) * X * X * X * C (-41109) + derivative ℚ (derivative ℚ G) * X * X * X * X * C (-78624) +
      derivative ℚ G * X * C (-378) + derivative ℚ G * X * X * C (-16542) +
      derivative ℚ G * X * X * X * C (-103872) + G * X * C 582 +
      G * X * X * C (-17088) =
      C 204 * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (11 : ℚ⟦X⟧) * G + (24 - 162 * X : ℚ⟦X⟧) * G ^ 2 + (-36 + 211 * X + 216 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) (m : ℕ) :
    1980 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-11605) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G +
      (-11880) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1) G + 2214 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-41109) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + (-78624) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      (-378) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-16542) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-103872) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 582 * coeff (m + 1 + 1 + 1 + 1) G +
      (-17088) * coeff (m + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (11 : ℚ⟦X⟧) * G + (24 - 162 * X : ℚ⟦X⟧) * G ^ 2 + (-36 + 211 * X + 216 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    4428 * coeff (0 + 1 + 1) G + (-756) * coeff (0 + 1 + 1) G +
      (-16542) * coeff (0 + 1) G + 582 * coeff (0 + 1) G +
      (-17088) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (11 : ℚ⟦X⟧) * G + (24 - 162 * X : ℚ⟦X⟧) * G ^ 2 + (-36 + 211 * X + 216 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    11880 * coeff (0 + 1 + 1 + 1) G + 13284 * coeff (0 + 1 + 1 + 1) G +
      (-82218) * coeff (0 + 1 + 1) G + (-1134) * coeff (0 + 1 + 1 + 1) G +
      (-33084) * coeff (0 + 1 + 1) G + (-103872) * coeff (0 + 1) G +
      582 * coeff (0 + 1 + 1) G + (-17088) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE2 (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (11 : ℚ⟦X⟧) * G + (24 - 162 * X : ℚ⟦X⟧) * G ^ 2 + (-36 + 211 * X + 216 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    47520 * coeff (0 + 1 + 1 + 1 + 1) G + (-69630) * coeff (0 + 1 + 1 + 1) G +
      26568 * coeff (0 + 1 + 1 + 1 + 1) G + (-246654) * coeff (0 + 1 + 1 + 1) G +
      (-157248) * coeff (0 + 1 + 1) G + (-1512) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-49626) * coeff (0 + 1 + 1 + 1) G + (-207744) * coeff (0 + 1 + 1) G +
      582 * coeff (0 + 1 + 1 + 1) G + (-17088) * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A226751Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a226751.main := by
  intro T G hT hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  have e1 : m + 1 + 1 - 1 = m + 1 := rfl
  have e2 : m + 1 + 1 - 2 = m := rfl
  rw [e1, e2]
  have kn6 : PowerSeries.constantCoeff (6 : PowerSeries ℚ) = 6 := A226751Aux.cnum 6
  have kn7 : PowerSeries.constantCoeff (7 : PowerSeries ℚ) = 7 := A226751Aux.cnum 7
  have hN1 : ((1) + (6) * PowerSeries.X * T + (-7) * PowerSeries.X * T ^ 2) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    simp [kn6, kn7] at h'
  have hM : ((1 : PowerSeries ℚ) * PowerSeries.X ^ 4) * (((1) + (6) * PowerSeries.X * T + (-7) * PowerSeries.X * T ^ 2) ^ 3 * ((1 : PowerSeries ℚ) + (11 : PowerSeries ℚ) * G + (24 - 162 * PowerSeries.X : PowerSeries ℚ) * G ^ 2 + (-36 + 211 * PowerSeries.X + 216 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 3)) = 0 := by
    linear_combination ((-49) * PowerSeries.X ^ 5 + (-343) * PowerSeries.X ^ 5 * T + (-216) * PowerSeries.X ^ 6 + (756) * PowerSeries.X ^ 6 * T + (-882) * PowerSeries.X ^ 6 * T ^ 2 + (343) * PowerSeries.X ^ 6 * T ^ 3) * hT +
      ((-1) * PowerSeries.X ^ 4 + (-12) * PowerSeries.X ^ 4 * G + (-36) * PowerSeries.X ^ 4 * G ^ 2 + (49) * PowerSeries.X ^ 5 + (276) * PowerSeries.X ^ 5 * T + (-322) * PowerSeries.X ^ 5 * T ^ 2 + (49) * PowerSeries.X ^ 5 * G + (72) * PowerSeries.X ^ 5 * G * T + (-84) * PowerSeries.X ^ 5 * G * T ^ 2 + (211) * PowerSeries.X ^ 5 * G ^ 2 + (-432) * PowerSeries.X ^ 5 * G ^ 2 * T + (504) * PowerSeries.X ^ 5 * G ^ 2 * T ^ 2 + (216) * PowerSeries.X ^ 6 + (-972) * PowerSeries.X ^ 6 * T + (1530) * PowerSeries.X ^ 6 * T ^ 2 + (-924) * PowerSeries.X ^ 6 * T ^ 3 + (539) * PowerSeries.X ^ 6 * T ^ 4 + (216) * PowerSeries.X ^ 6 * G + (-678) * PowerSeries.X ^ 6 * G * T + (1655) * PowerSeries.X ^ 6 * G * T ^ 2 + (-2016) * PowerSeries.X ^ 6 * G * T ^ 3 + (1176) * PowerSeries.X ^ 6 * G * T ^ 4 + (216) * PowerSeries.X ^ 6 * G ^ 2 + (2532) * PowerSeries.X ^ 6 * G ^ 2 * T + (-4250) * PowerSeries.X ^ 6 * G ^ 2 * T ^ 2 + (3024) * PowerSeries.X ^ 6 * G ^ 2 * T ^ 3 + (-1764) * PowerSeries.X ^ 6 * G ^ 2 * T ^ 4 + (1296) * PowerSeries.X ^ 7 * G * T + (-7344) * PowerSeries.X ^ 7 * G * T ^ 2 + (13608) * PowerSeries.X ^ 7 * G * T ^ 3 + (-7938) * PowerSeries.X ^ 7 * G * T ^ 4 + (2592) * PowerSeries.X ^ 7 * G ^ 2 * T + (4572) * PowerSeries.X ^ 7 * G ^ 2 * T ^ 2 + (-17724) * PowerSeries.X ^ 7 * G ^ 2 * T ^ 3 + (10339) * PowerSeries.X ^ 7 * G ^ 2 * T ^ 4 + (7776) * PowerSeries.X ^ 8 * G ^ 2 * T ^ 2 + (-18144) * PowerSeries.X ^ 8 * G ^ 2 * T ^ 3 + (10584) * PowerSeries.X ^ 8 * G ^ 2 * T ^ 4) * hG
  have hLne : ((1 : PowerSeries ℚ) * PowerSeries.X ^ 4) ≠ 0 := mul_ne_zero one_ne_zero (pow_ne_zero 4 PowerSeries.X_ne_zero)
  have hP : (1 : PowerSeries ℚ) + (11 : PowerSeries ℚ) * G + (24 - 162 * PowerSeries.X : PowerSeries ℚ) * G ^ 2 + (-36 + 211 * PowerSeries.X + 216 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 3 = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hM).resolve_left hLne)).resolve_left (pow_ne_zero 3 hN1)
  have h0c : PowerSeries.constantCoeff G = (1 : ℚ) := by
    have h := congrArg PowerSeries.constantCoeff hG
    simpa using h
  cases m with
  | zero =>
    have r := A226751Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A226751Aux.relE1 G hP h0c
      push_cast
      linear_combination r
    | succ m =>
      cases m with
      | zero =>
        have r := A226751Aux.relE2 G hP h0c
        push_cast
        linear_combination r
      | succ m =>
        have r := A226751Aux.rel G hP h0c m
        push_cast
        linear_combination r

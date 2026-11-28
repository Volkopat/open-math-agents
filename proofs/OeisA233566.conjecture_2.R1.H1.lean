import OMAReductions.R_OeisA233566_conjecture_2_R1
import Mathlib


/-! Finite part of Zhi-Wei Sun's second conjecture for OEIS A233566 (2013),
from the reduction by @eltociear in PR #31099. Each block certifies the supplied
witnesses using Euler's totient product formula and a kernel-checked primality test. -/


namespace OMA.A233566Square

private def multipleRange (u : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | k+1, s => u % (s+1) == 0 && multipleRange u k (s+1)

private theorem multipleRange_sound {u k s d : ℕ} (h : multipleRange u k s = true)
    (hlo : s < d) (hhi : d ≤ s+k) : d ∣ u := by
  induction k generalizing s with
  | zero => omega
  | succ k ih =>
    simp only [multipleRange, Bool.and_eq_true, beq_iff_eq] at h
    by_cases hd : d = s+1
    · exact hd ▸ Nat.dvd_of_mod_eq_zero h.1
    · exact ih h.2 (by omega) (by omega)

private def gcdTest (n k u : ℕ) : Bool :=
  decide (2 ≤ n) && decide (n < (k+1)*(k+1)) && (n.gcd u == 1)

private theorem gcdTest_sound {n k u : ℕ} (hc : multipleRange u k 0 = true)
    (h : gcdTest n k u = true) : n.Prime := by
  simp only [gcdTest, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  refine Nat.prime_def_le_sqrt.mpr ⟨h.1.1, ?_⟩
  intro d hd hdn hdv
  have hdk := Nat.sqrt_lt.mpr h.1.2
  have hu : d ∣ u := multipleRange_sound hc (by omega) (by omega)
  have hdiv := Nat.dvd_gcd hdv hu
  rw [h.2] at hdiv
  have := Nat.le_of_dvd (by decide : 0 < 1) hdiv
  omega

private def multiple16 : ℕ := 0xaff50
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem covered16 : multipleRange multiple16 16 0 = true := by decide +kernel

private def multiple128 : ℕ := 0x8b6b72b1e90d10fc5a7c5fa4ff1061c4d61d61478b2780
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem covered128 : multipleRange multiple128 128 0 = true := by decide +kernel

private def multiple512 : ℕ := 0x67bfd02bef01d7a4a7d3018fde15ef65434c5d2ecdecd32bdab805c5270799e540c47d1b625175a57f3c30c90e4ef05875cab5f03c844a8a59e7e290a90a92b39d2dfacd20556db05bb29ca1b5225b9bff9ef2ec239d08e783d4661600
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem covered512 : multipleRange multiple512 512 0 = true := by decide +kernel

private def multiple2048 : ℕ := 0x134c43df05c1b2271bb1d3eacca431a87bdfd6193b3da20584feed2db5d79762955a76c03d726defb75b0ed5b77545c660545973c5eeac854abcc980fd38cfa87d63d24bca0ca6dc5d144ec32741caee69d8c17bda126c3606f4f54110f5aa8afb07f0800715ba8103dcbd38a1efdbc3b8eded49fba5e348c5d3699ab5627c656fc3e6ff6fce67b917dae2817d23c4e8c2ad94a68821db300d37a2b4742c2220df58c067ac037d73f4e78db5e64a2ebe82de8cd63ccc1694ce7b7c4229d406f1bb4005cca805859f0a6fadba86f6cbcdb91b7c6b4421cf2da4d9da334d1edc07a110535632b8b939741024f19e691b1c7f767ed656a1e4397e8ace81d8dbcc455b7924251d2ea670b64e6624203372af08abde2a694dd1f941882f4a724253b92024f3978f17990d6e9f22c6e98d3b822e5ef0b5b260254b9538bd1ddc15eb80183d041c1df7744a006ae549814c71910c23ac3472b608810c7b6f1f3d9ca2d55ae26b06e46c2249d8b4e4fe67dbe6800
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem covered2048 : multipleRange multiple2048 2048 0 = true := by decide +kernel

private def multiple8192 : ℕ := 0x1d4eef4163690b6d06da918ccd821c3edf299237df23af046bb765dfd02f13859a90b976b410e7e76989889530b931071c20a51ba2fe0df363555c19d80181b78a3dd7ef275fa3240af38e9ef1a87f2d32b0905c723d20ce8607f4ae1251a44e008f077cda36f0ea135aaccea2a80f9993aac32e888fdf0253bbfa54c057eececefc94e66cc7fc2e2ce7d583324fd7acfd562b4a49ba8444b2d9da3eda283cb90e124977274082265365dda8261ef9b6a6ac1140267d18be4edc52a9efbed298c49cb10b247f1f8543ae252d973870aea4b639a4f9552a5d07dea02c331b8a4efe126ad9f1b12fdf25016c4d98f2a28267476c0f7b23cc11f1811a6df5454406f2d167f18b3fa45a800d470e0b84d7f81cc18d5519f80de55357dfb90c4a6d98c27e5e99fff07cb599a21f47aeaee3be1fe24b1febe6229ad7232e860e43aa4b941d56191d9239cebd1213b87ebf536e105971c25bac341e0935a84c3fcd38c31aae1638d7b980155a0438497a657b550796acf4a4f0e254f74a66e7143a516e0f0cb0c5f5b29c88b27a816234cddbe11ab549e7ebfc1f008251da407b1c44d9d50018d88eb6c5ed45dcf14824471d86daba89f3ac1944b3939b2fbcabaceaae958be69fd3232b3ea647c914d76a7e2898ae487624e21167b3f0726dbb60932ed70a969b190c7c27b5010e12f69c39e908a3e7e15ae1763d2e447219d6a468455af9f6907d4a489ec3bef50f94c1a82b8de6a465cf694d039ddbff7865653a56ab47147d5f406b07ca492d384f9f849945512107887ae827d9d3aa35c108b4f7746c3b4251e4eb3492aab117a007f4a8d880ab642af2de0e02a77ed490ba0a029096bc19bd453085426e5d66460d5c7ef629389f905e2f79cadf489ac373d4c28d4b2125ce56231901d25a784d71db033a9405bfd20fbd26491ac455546d03ace3387c957be169e54ce27ad9e568fcbeac17162b3eb2cde4490f780c252585583cfafe364b16aa671ad238e567dbd6134865203e9b2485b52f06d61519dbe0ef45c597f5a5e5626f4aa441dfcfc68a2da69e71cc7d6fb4953440eaa8b66bf307f64079774b8d6c345d725dfe20677b159fef7936baaa787fe3f81718e50362c77d0485f48cf9988e6517d3b7c5888e6711c872a605d9e5c42a4f6cde262e145ee07fb4031be75b5660382c4cc827763a1e686e6210a8788e06c5ab38dacba25199e2513bd8b182503ecac12d313261504ad58c50b6358b77544d6da0ca8f15f50ff6e90098512dff04f0015bf74a0d2eb63cfb698fc3e8e55736fbb830ad22d2b6575ccc40ac0a1b24735c39e217b31a8a8a0a1d1812474a3ea159a2644b91f03b33c379678c7361ff81562c313f32aede5992254ab9c2965f2d0ddab35d03c7eb9145dff7e3a8d3bd27e38f227d124bfab0bcf49822c914912d2a9e5320c527015f4c6be5a957c1b4940afb809b8e8b7220c1d9ac10eb29db2b04d2963b6014dd014108f616bf1fab4b3eb2629dda2aade759d1f931c8ea51df881138828d0ce7a18834832ece814ff00cec88dd06a6bec0905aba23efaac53ae34f658a024b860d13810f36c0f4f08f6b225111d532d473a2bb006052604a0fd217dd84a73c9d4e93c156f7132f959f76b112ed47b94f68ca9659202c0f4e10511e285cb224ae16654c16d7d9a2b28da34a5bf727420e82a01f4b330f518b37f2a27101fa82f943d009f5f40695390a6e648d58f2a6a8a6f8f45529965219d3585baf59c02239b9612c41642be21f0a5b6af3b149ad073915ee9150f9a50059c27a7c687aa961df4caf6acc8d1a13cf0f420f4aef354e0c16c19535584a85061c290f290a875b5b5057444bc711b894cf63c2f0df3d961ac601e6b1c656a8b43d77a669a3907dfc57147a52cb0f5024db5379bd79f72ff38e2d3718322a57f8738a4fbd88e0db3583ba22fcd9562d84f08a03e760c0341f4b9c2a9d2d122465439c3f4a5e951f43ec325a58eee5388741da93738868cddff14369dac0dc05b7d1d97c8fcb89dbd0c3016fd6d3074933221ec375b9d95bc1c421c1f18e7fe846ba99ebb5a463746000
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem covered8192 : multipleRange multiple8192 8192 0 = true := by decide +kernel

private def multiple22432 : ℕ := 0x6b401c29dbdf68152ef6842783d953803f146d76578432d1b8acf849237f27653b62659d5e5301f9cfd885c414beed481327319d4a258767ecfc25f8a6f29609b14043227f8a9d1d992a0248cb2eeb3606d81f86c7844f60f3f0510ed0dabb33e985fc20985f54ee45f306cdf709b0141b90610154c5fc22e3e4bfadbf86c141a50c38376914cc4bd3e94e308e32020b657fad8ef023617000aed7ffe1193eee9c2f5bdb9a79d1d2aa30a74d4b02c9a91a773e579364f8f6eeea975d21257bf142ad4d57f43462111714836af598dd1772b5cab82c80673fdd3dddf4445fef2d80c348a3a8f20fe028ab6e91a8140418e56a06cfdc43aae19db2ced7478de02e91e37a32f993e70e58a220894ada4526f19b80992883a357245d1183ea2148cc7ab134cb5e17a88d9c782f6863b5254445f4acd4b44242579339f06b5db03f1538562bbb9dec0f569ce13906a8d5550557049f7a358d19796ad7fa10362b84ce559de895ed6401e2f966d28ffc6a8560348b9fd0eddc54f7cbfff94f74ed5aa0c8d23ebf1875e4150788a6fd644552b23feb6643bfa1cbe3362ef388f6a52887544361477e2fff82c29f48301996d62d43ea8874f5e9708d8a70d67f61d8dc2891d827e7e282df4dd2d796a7f19bfbcc67e178bd82c368fbb2ff1f2b50321ad4c3cbd611e8d1222206fb103cbe1b2e466ebf3ad0933b36f4c19993c551c3f743b8e16432ec7d3050b9bc9b1acdcf5232051d3baf3c8b7e5c0b604d9168bfb70f1d779a7fa6fd61709d14c8f13fdaa4072a5db30a49e9ba3eb7f9e0771e3c4b3234178720fc84b0035d0f1778826980eccbffad4653b934354c5ff65438383d80fa8e7cad79d6a11f8cef30a2d01940dac26b9b6e101487d2d1316a5e71a16a296706f40649203a6f50e5f3f8bd7a21059f8f25057502d492b28f71bf5b537a10a876e8906c93b82cdd4160f83ac6b7aea72654592b60e57434f2e2ede5ece4d7b995ed1e1ca5be856152a9144397aec4906c0ba26383588b08c9a3f7a1819c4ad105a5f60098f481bf61d5a1373da109f5e2faa2731da3a744898ded764ce807b6e6d6c29dc9eee00d52feb8c287a4c8f5482478add62ddc042e7634978a475672c657e1fa46cda4bf57b53b3e7deacfc6ceb4460c0feee45b575d0bbbfa25e99e1edd3e4aa5e4f2dfc01eb2ac02ec6ec23ac23b06d77c0ee64335e3f375afa3acf386006430b0543ba77f6e01d55ee9bbcab64d8c256d681d16c96e134f42ce038894eb8d8bb320bfab2961b506ed578513cf1860cba0604b035b2c88ad37ebf83afdfb9f2f033e55f66b234a31fab04c5d8c29a09944531daaa5507aa3bb7700d1ef6735d60417cba38e9c1e00eb55b6260622a30173ef42413e54f2d1f36350820bae0e2b45b16ac688b331d7de00125656fa7320948001678a05a30e6cdab35ee79a60be617d8ab7a25dc35aa0490844d70bb779d0ea899f5873b752d7dc360749219e7c3fb4911acffc462afd841d64eaaa43acf3bab7d1277f911c54016e7534cf7281d0a248b49a129b7ff21bea8e4a8c57731601e076204aca1b7167151515d091e9a5897e69f2ce25e0fe71b811316b25bfc9b5e2d0e587eac6477539acbce4138d8cb63eaccfe79115d84d2a5a2f79f27495bc402c8f61b52444626f01ea6f1b4fb4d7f0529f4cfc8ab2ba32f9aec1e63e3a0bf1b41d02670e3b9398df4a26470bd51adcc182cdbb80e5991a55a5c4e85cdc5a680db2a21e3e68a0792511702c4e98b66a34a7a10d231355899b1f576d9a9dce2ff1ef8e6c96fc3bcfe25422a8a37230166eb6a3ae6a08fd7e309ff0cbda4441fac3ab0dfdbc11535a2c9346361db96db1958012eadd0c571254310acb082f230591e833fb9c6c005e871ed386da2713b58da05e20a887604d10b44308ffcc00618c646459afd4e3760ba31657aa9262e07bb380867a5f7fa17a3d503216c487f1d6149769211a91f189229ee8be19cfc3232c9ebfaa76f016b77d5ff22114ba9c55cb942abc31a2bd2e87458b1e6c0306f11f59e1e7ee0ce16a1f269ad068effca9571a016ca15558ab5a86a296a9d091764a10c3ea03b59e7751381a7070f7e92b0bf5caded273b84d4dc7ee53d93e74fa8ec88c561f641e649c15ee9194c280b985fd9774a9eee3173f82b883ba7c271f651519c9bfe2a38598bcfc05182dad5ce705bf9dd8c153c1bdb43d819f57520e0884b76a1cd673e9231b3822103fc8502dfc3c4388b6b1288fa619f4b27f342185e6eb7b6faea36f4abd977a4938bc44dcb61498f44b3e15767fc3bf8b304f23adcd98f0927eb49461ea6018598ceca2bbb156bee35f53615cc68a7c97c6a9fee2f777b7fc1ec8d2afb16544375b7e93d9706658287c1575b14aa7055a61cfb0c45af89bf561ed894c90f3e4088ba0e697fead5bc0e9681983c7dd6b218740f4e4f14a38ed3d8fd95cf45c37d886f70c9b7b4f7886d10ec89ecf92df2669cbd251dda88d12e6075c63206999d40efb6876099063876f044bc1d21652e117287f0db1718b24a3fea5589d9bf5f6604ed1c9f04ece77e3d050ee46ff7a4d1e2e6c0b5c6f20ff07dc9fe1c65fe72d340f4dc7906341330f92193383b5b13e8ef3d307b5d44dbb37d87f2e90cfbd5141adfb0259676c7a1cd13f00da4478b4e4e264093f85a4f571bd08f95ee05dff4195ff6d04396dbd62455b781fc5570db9a6cd6e973fb827cd506f990584c2a628e35a423f3706c1c15c7aff7edab13c6a5f39708dfc6227e56be21366068e755a915411b8d9b58565864ed29e27f70bafb5b0d341cca941438a0b1d7417cb0397c45a222120beb8e3385c45738970c711f1cc1618bb9a128d110aa61d7c7836ddf836af6c0d76d1552439953877b92231143165617967ac16d63d9236229ad2e84db419eadc0b40b3a5a2ceebf06771f1840f1a6e805e08722685a0933c1150e24b1d5ecbe71e9ca885cdc16a1b9ceef6330b0b1dc2230527e43c0c486784378c4118bfa53b9f88e6cc02d5d4d32393d6dac0fa59aec33999f79de0f29c01e1fead858816dc3604cc7ba9d3b097d2e006ad7bcc66733810f5ebd8e03f0ec7d8374b17f2cf8cdd62fe27fc8759305011e3114c59cca13d945dcd271709b8b0448f33247d4b0eb55ff048be9994cf0566d14587bd08c666254e7edf51d065f7b57526c72fe78029bba906d702a3158e3f4b84992a5972edaa7eb9a5e0a118ac9885ff5bda272fb3c559e8d39491b4eaf641b02495d63ddbe02281009234e76a294152a780be5e779d909c3ea8fc07fe8dfb1ae316165905459ff2e4e2235023183576fa8d82ee427e1ef943830c3b9e86207262cf6d37b2bb39f8e487774164c3c807256fd3b8092ccdeb326a0172fdc54198ca365ecfbf168ef3bf6d61b9da6a87d8ea9ff287e2907ff63075e760c79ce58566ac174b5df4d28b1fa2123fc1fb7eb8b3951cb3f7c945af03507f5c15a8c755278e5f190484816024f261001d279d742c95d9340cee46a56e59b5ae6840b13c8855a3d22b0f882ad79fbdbea5cec751b393e3ea75bbe1b9c49681f67e192c731b4d8eacaf503e0cfe8caacef129e9ff48ff84f35150f0a267f3da4990a991a98af4dc0032779c67c89eaa61a55d3a614b51f5d2c72ffa8f7504f2844f712e93a6f713c2767df304e62c011bcbe4cd3b7422715dfa4363c54033a69ea7b4191cf03621b48374b62c326b3497ad57eee1f0976dc71574655ad654b9ae7cff20566ba4a4a13136c80d25119939cc9c17768b022d16807a55362a6c84db8fd38fd81bc4225d05cf7e650e90062ca1f331a18ceffa8a9bd4e464c4818176b22bbdf7d6aa15301db5aabe302e5ba69cf35dd1dba8022ea24bbb660d22d9db1dce9a5376f13074a90484dcdbd929a7644122270cdb8cc1494a178e7355ef56be494d425fdb5b6ef0d716ced9fd147625c42b3e91b91b02ed2b10c2b126ebfc27512cfcfc7688609c8b1496f1df8cef0c24f5bd6b8525c258826d1eb4f2659d429187013960afbab5b9cc7ebd63008cc0bbfae8caaef6f6e6b549cfdb174ebe63b6eea1c2a0d182db3fd72d9927d1b825d44f0b9869effb1ef3b2f504e2f31ce6c19cc81348420b39960ef118570e0ded556e2bc2b39629a2cc1fd3329a86c72824dab01d703cc99bc911c79604ea3d259de70e5851eda7456c1f255b24fd675800325518a855acbee26d763cb5343b4c7c4b139d58c2044b4022678ad2eeeaef44371f810a59d633d0f145f59d38449a426561ff89e16d622430515d1d8c6873fe8b97466a0779bdd50db7b396569da9548be397f402b80c46e054aaec6531e643e7ffc6422669c8c611cc791c49ffb4a53b1533ca0c0bbe6a2413297f49c94f275a76efccc50e4134b958d230158efc051879795d4f00e6a6851514648becde4d5fbb57ceb931c2d1f3357a6524b027494ca01244ea691a2da55d2c0c68f832207dfc8ee1fb1107d7a986611f05ffcf29ca798560355141364e1fbea7ebc7434dcf2f9c8aafd8776fac3c417714680c9d27d017103b4414e6a473ecbfe07c5628cf9eab7a21ba930d97a93d36f6d0d8850a7d6a7d549186b36eec9335fdf6ec0ea5b95d152fdebe3016723756e3e4d4a272640348f03f10c0280d862485f83c14d48ca4a387e63561bbebe30d1f7e6b25971cf9ff970ecbf526237fdeb336f1291fd884eab7d7c3906c42f28c357a5aea59500dd5f70817112effd504d0fb1a06bc5c8b256247f2d37ef50ef8568f85d01cb4b3f7b4d0260e4b7c11affc94eafe3ad403b7f6280cf7184364f2f9c5b27f0c9d6d1aaf28622d6720e41a57386c33b3f24b9fd94365255680933f6559fd9f54e197bde200a26ef84a44eb1a1c708c8e096b9cf740b1989cfd42c15191112e3ce57f463c7ea4c6d3438df4e8109762b3d89fd641d3f20e5c90e8532d7561e4bcc6a2808315c52cc8179be8c11beea52139f008cb71b8a624e311581e6c0e2ea2123847c64fe0818d60f7320b0cf7e6c5e3eafb750402ac2101e3b902aafd8b40006c362154c85be4e19cf768bf1833af56316f2652cbc5bc069e67c6cccee87ed15b8d00612f5623eb65328e024c5ac2f34002b4d649ac8d40ad2bb709d3f39092f76fac1300f5fce11cc9c62f0732ec21604dabd2f2c35080a6f2ecf444c4b79437aca439284039d9de5a06762e1c8a64945485f2aa10cc2a15813857a818829fe0050bd04fa813b92b20844fde839a62a7e3fa597f17c14af5712afc705d60346c2d5cbae933d82fd579dedf5c8494e7bbe8b816abeaa08e21eadfff0b929bc0613e1291993b20cc9495267b7bbac0cd248d4409c2f14a6a0854c251338efe40d3573636416fe0fe4af37f211adcce6adb68c343f065b4483911c5d5f9a2d847deb9a57207b9f339e8c5724a8b016cd27b80e873ae4b5a6d26db30ef8b5105e91a88dc7a4f5407a18bdbf3d263a681f6e1bfcf02a8d26f97e739f23a340f213e62db2370769d0d6ea40aa564546dbbf1c61c4aa3eb39d070b6d995fce4fa0e1f6f2ffb6047d56c8c846def058ced869de129311e521a9d004966e282bb0de99614c4cbc759ae1b6ef7bc4974d918ed3fe612a91e860a7427079b142eb8c7f320c4e5a8d39ab4a75602803556a43cd25f805621f6ce2fbd98e447c96323e382006eef254fcfaa29070cf71473e8f8c3ac1d17ec000
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem covered22432 : multipleRange multiple22432 22432 0 = true := by decide +kernel

def primeCheck (n : ℕ) : Bool :=
  if n ≤ 16 then decide n.Prime
  else if n < 289 then gcdTest n 16 multiple16
  else if n < 16641 then gcdTest n 128 multiple128
  else if n < 263169 then gcdTest n 512 multiple512
  else if n < 4198401 then gcdTest n 2048 multiple2048
  else if n < 67125249 then gcdTest n 8192 multiple8192
  else gcdTest n 22432 multiple22432

theorem primeCheck_sound {n : ℕ} (h : primeCheck n = true) : n.Prime := by
  unfold primeCheck at h
  split at h
  · exact of_decide_eq_true h
  · split at h
    · exact gcdTest_sound covered16 h
    · split at h
      · exact gcdTest_sound covered128 h
      · split at h
        · exact gcdTest_sound covered512 h
        · split at h
          · exact gcdTest_sound covered2048 h
          · split at h
            · exact gcdTest_sound covered8192 h
            · exact gcdTest_sound covered22432 h

end OMA.A233566Square

namespace OMA.A233566Square

private def phiValue (n : ℕ) : ℕ :=
  (n / ∏ p ∈ n.primeFactors, p) * ∏ p ∈ n.primeFactors, (p-1)

private def checkWitness (n p : ℕ) : Bool :=
  decide (p < n) && decide p.Prime && primeCheck (p^2 * phiValue (n-p) - 1)

private def checkRows (first : ℕ) : List ℕ → Bool
  | [] => true
  | p :: rest => checkWitness first p && checkRows (first+1) rest

private def Verified (lo hi : ℕ) : Prop := ∀ n, lo ≤ n → n < hi →
  ∃ p < n, p.Prime ∧ (p^2 * (n-p).totient - 1).Prime

private theorem verifyRows (first : ℕ) (ps : List ℕ) (h : checkRows first ps = true) :
    Verified first (first+ps.length) := by
  induction ps generalizing first with
  | nil => intro n hlo hhi; simp only [List.length_nil, Nat.add_zero] at hhi; omega
  | cons p ps ih =>
    simp only [checkRows, Bool.and_eq_true] at h
    intro n hlo hhi
    by_cases he : n = first
    · subst n
      obtain ⟨⟨hlt, hp⟩, hq⟩ := (show (p < first ∧ p.Prime) ∧
          primeCheck (p^2 * phiValue (first-p) - 1) = true by
        simpa only [checkWitness, Bool.and_eq_true, decide_eq_true_eq] using h.1)
      refine ⟨p,hlt,hp,?_⟩
      simpa only [phiValue, ← Nat.totient_eq_div_primeFactors_mul] using primeCheck_sound hq
    · exact ih (first+1) h.2 n (by omega) (by simp only [List.length_cons] at hhi; omega)

private theorem joinRows {lo mid hi : ℕ} (left : Verified lo mid) (right : Verified mid hi) :
    Verified lo hi := fun n hlo hhi =>
  if hm : n < mid then left n hlo hm else right n (Nat.le_of_not_lt hm) hhi

end OMA.A233566Square


namespace OMA.A233566Square

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_3_131 : Verified 3 131 :=
  verifyRows 3 [2,2,2,2,3,2,2,3,2,3,7,3,2,2,2,2,3,2,2,2,2,3,3,2,2,2,2,2,3,2,3,3,2,3,11,2,3,2,11,17,5,2,2,2,3,5,3,5,2,2,2,5,5,2,5,3,5,11,3,3,2,13,3,2,2,2,2,2,5,7,37,13,5,3,5,3,2,7,2,2,5,5,3,7,7,2,2,3,3,5,13,3,2,17,11,2,2,2,2,5,3,2,19,2,2,3,3,3,2,3,3,2,3,11,13,2,3,3,2,2,2,2,13,2,5,5,2,7] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_131_259 : Verified 131 259 :=
  verifyRows 131 [7,2,3,5,2,2,3,3,19,3,11,2,2,3,2,2,3,5,3,7,3,5,2,11,2,2,2,2,3,2,3,7,5,3,2,5,3,3,5,2,3,7,2,3,7,2,2,67,2,5,5,2,2,3,2,11,7,2,7,2,2,3,3,3,7,2,2,3,5,2,5,7,3,3,5,3,7,3,41,2,2,2,2,3,7,3,3,3,2,2,3,7,3,7,2,2,2,17,5,5,2,7,2,11,7,3,3,2,17,2,3,3,5,2,2,2,5,3,2,2,5,5,5,5,3,2,11,3] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_259_387 : Verified 259 387 :=
  verifyRows 259 [3,11,2,2,3,3,5,3,3,2,3,3,3,3,3,7,3,17,3,7,2,5,2,2,3,2,3,7,3,2,5,2,2,3,5,53,7,5,11,3,2,3,13,23,3,2,5,5,7,2,2,2,5,2,5,2,3,41,5,13,7,3,7,31,3,3,2,2,3,2,2,23,2,5,2,3,2,7,3,2,3,3,5,11,3,2,3,5,3,3,13,11,7,2,2,5,3,2,7,19,3,23,3,2,2,2,3,3,2,2,7,37,3,11,7,2,2,3,3,7,7,2,2,13,5,3,3,5] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_387_515 : Verified 387 515 :=
  verifyRows 387 [3,7,17,3,5,2,3,3,2,3,7,2,2,7,2,7,3,5,2,19,2,5,2,5,3,3,2,3,7,7,3,5,2,2,3,2,3,2,2,5,2,3,2,7,3,5,3,13,67,2,3,2,2,29,5,13,3,3,19,5,5,2,3,3,29,2,5,7,5,3,2,3,2,2,2,3,3,2,2,3,5,5,3,7,2,17,11,11,3,3,2,5,17,5,3,13,3,7,43,5,3,2,43,3,5,5,3,3,3,2,7,17,5,3,11,3,2,17,5,3,31,7,3,11,3,29,3,7] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_515_643 : Verified 515 643 :=
  verifyRows 515 [7,5,7,3,3,2,59,7,5,3,2,2,3,5,3,7,3,17,3,2,17,5,3,13,2,3,3,3,79,5,2,5,47,5,7,2,2,5,89,5,2,2,2,2,5,2,3,17,2,3,5,11,13,7,13,19,37,17,97,19,23,5,2,17,13,2,3,7,59,11,7,2,2,3,11,3,3,37,2,2,3,2,3,7,2,53,7,3,2,3,2,17,2,7,2,2,3,3,2,3,2,2,2,3,5,29,19,7,2,11,2,3,2,7,2,29,29,5,7,3,7,3,3,5,3,37,13,3] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_643_771 : Verified 643 771 :=
  verifyRows 643 [31,5,3,13,41,2,3,2,23,13,2,11,23,2,11,2,3,2,29,5,3,2,3,23,43,2,53,2,5,29,2,3,2,3,2,7,17,5,19,17,7,13,3,2,5,7,2,83,3,5,3,7,2,73,2,3,23,5,13,37,5,2,2,2,2,13,2,3,3,19,2,3,3,3,19,2,3,3,3,29,2,2,5,2,2,3,2,2,3,2,2,3,2,7,17,3,3,3,11,2,3,13,13,5,17,2,3,2,2,13,2,2,2,5,2,2,2,2,2,2,3,37,2,7,5,13,7,3] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_771_899 : Verified 771 899 :=
  verifyRows 771 [11,3,11,41,11,3,2,3,5,11,2,5,13,3,3,7,3,2,3,2,3,23,2,3,2,2,2,2,11,2,7,2,2,3,2,41,2,2,2,7,5,2,23,7,3,2,2,5,2,3,3,2,3,2,3,23,3,5,7,3,5,3,2,3,2,2,17,2,5,37,3,3,29,3,2,3,3,2,5,2,5,2,2,3,2,2,7,43,5,3,17,67,3,11,17,2,3,17,29,2,2,3,2,3,11,2,2,2,3,3,7,2,3,3,2,3,5,13,7,2,2,3,3,5,19,3,3,7] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_899_1027 : Verified 899 1027 :=
  verifyRows 899 [2,3,2,3,37,3,17,47,2,17,2,13,2,2,3,2,3,2,11,2,2,2,2,13,2,3,2,3,2,2,2,3,5,5,2,3,17,5,11,2,3,2,31,2,13,7,5,3,11,23,3,3,5,2,13,5,5,23,61,19,2,3,7,5,2,3,2,7,5,3,2,2,5,89,29,17,7,3,3,29,5,3,7,3,2,17,3,2,3,7,2,3,7,5,5,5,29,3,2,3,5,3,2,41,2,2,13,2,2,3,3,2,3,5,2,2,23,7,2,3,2,3,7,3,2,13,2,3] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_1027_1155 : Verified 1027 1155 :=
  verifyRows 1027 [5,13,5,3,2,5,3,5,2,11,2,3,17,11,5,3,2,37,3,5,2,2,17,3,3,3,7,19,2,5,2,2,3,7,17,2,7,3,5,41,2,3,5,5,2,29,17,2,3,2,2,2,13,7,3,2,3,7,13,13,2,2,5,23,5,3,5,2,3,11,17,5,5,2,17,3,2,5,19,7,3,2,2,2,3,2,3,2,3,11,3,2,2,79,5,17,11,2,3,2,2,3,5,2,41,3,2,3,2,13,19,2,2,3,5,2,3,3,2,3,5,5,103,3,11,2,17,7] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_1155_1283 : Verified 1155 1283 :=
  verifyRows 1155 [13,13,7,13,17,13,11,3,2,3,29,3,23,13,3,3,23,2,2,3,263,23,3,5,3,3,2,3,5,2,3,3,17,5,7,2,19,3,2,3,17,2,47,2,2,47,3,2,2,2,3,7,7,2,7,2,2,2,2,11,7,2,2,43,5,7,3,7,2,2,3,67,2,2,3,2,3,2,2,3,13,53,7,5,2,5,23,3,7,2,13,3,11,2,2,19,37,2,13,3,2,2,7,3,2,3,29,2,3,17,2,3,5,3,3,3,5,3,2,2,2,3,5,2,3,3,3,37] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_1283_1411 : Verified 1283 1411 :=
  verifyRows 1283 [2,13,5,13,7,7,2,2,3,11,3,7,17,151,3,5,13,5,5,11,13,2,29,2,2,3,3,11,7,19,2,3,2,3,29,2,3,3,5,2,2,7,2,3,2,5,2,3,3,5,37,3,2,13,5,13,37,3,13,2,3,2,3,37,17,2,2,2,2,2,13,11,5,13,31,3,13,3,13,7,11,3,5,2,3,13,7,29,7,3,5,2,13,2,5,2,3,29,2,5,2,5,13,5,23,2,7,2,5,2,2,3,2,3,2,7,2,7,2,7,2,3,2,7,19,2,2,3] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_1411_1539 : Verified 1411 1539 :=
  verifyRows 1411 [47,2,7,3,5,2,3,3,31,7,2,2,2,2,3,5,2,29,3,7,2,7,23,3,47,5,3,7,2,11,23,3,7,2,3,11,5,3,2,2,2,2,3,2,2,2,37,3,2,7,3,3,5,2,3,3,13,2,23,2,17,17,2,3,2,3,2,5,2,11,2,29,13,23,2,3,2,5,13,7,13,7,2,3,11,7,19,43,17,2,7,29,11,2,29,3,5,2,7,2,3,2,3,41,31,2,3,2,3,2,2,5,13,3,7,3,2,2,11,11,2,53,7,5,29,7,3,5] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_1539_1667 : Verified 1539 1667 :=
  verifyRows 1539 [29,3,3,3,2,11,97,3,3,7,3,5,73,2,3,5,3,3,7,3,2,2,17,5,11,3,2,37,19,5,2,2,3,7,23,5,2,11,2,5,2,7,2,5,5,2,3,11,13,2,19,2,3,2,2,2,3,5,11,3,19,19,5,23,47,2,2,31,2,2,17,2,3,2,2,2,11,2,11,19,2,3,7,3,7,13,5,2,2,3,19,2,5,2,7,3,7,2,3,7,5,3,5,13,5,29,23,5,13,7,37,3,2,41,2,7,3,5,2,2,3,5,3,3,3,2,3,3] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_1667_1795 : Verified 1667 1795 :=
  verifyRows 1667 [3,2,3,2,3,11,2,2,2,5,2,2,3,5,3,7,11,3,3,2,3,2,3,2,3,5,11,2,3,3,2,5,3,3,2,19,11,2,3,2,2,2,5,2,31,31,37,2,5,3,2,5,11,5,17,2,3,5,79,3,17,3,3,7,7,17,13,29,11,31,5,2,19,2,3,19,2,2,3,5,11,3,2,2,2,2,3,5,11,3,3,7,3,3,7,13,7,17,2,11,31,2,3,3,2,11,2,5,2,5,11,5,2,2,3,31,5,5,2,11,5,3,3,3,2,3,2,3] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_1795_1923 : Verified 1795 1923 :=
  verifyRows 1795 [3,2,3,2,2,2,2,13,11,7,2,3,2,19,13,2,2,2,13,2,2,2,7,3,2,2,3,3,23,23,7,41,13,3,29,5,2,29,23,5,7,2,3,7,7,2,7,13,2,2,2,3,5,2,3,43,53,2,11,3,2,2,3,2,2,17,11,7,31,2,2,3,5,7,13,2,3,5,13,3,2,13,3,2,3,3,7,3,23,3,31,101,37,7,3,5,23,31,17,2,2,11,2,37,31,5,2,2,5,3,13,23,3,29,11,11,11,7,11,23,11,2,3,2,2,59,5,11] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_1923_2051 : Verified 1923 2051 :=
  verifyRows 1923 [5,2,2,3,2,2,5,19,17,59,3,2,2,2,3,5,2,29,11,7,2,5,13,2,17,3,2,31,3,13,23,19,23,3,3,2,19,7,3,2,2,2,37,2,2,109,2,5,19,5,13,2,23,2,3,11,5,29,5,19,5,3,2,5,5,5,3,2,3,2,3,29,3,61,3,31,3,2,13,3,19,2,7,11,7,41,7,3,2,2,2,3,2,3,3,3,5,3,7,11,2,2,3,5,3,3,11,3,2,2,2,17,13,2,3,3,7,5,3,3,2,2,5,3,7,2,3,13] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_2051_2179 : Verified 2051 2179 :=
  verifyRows 2051 [19,7,7,2,11,31,3,3,2,2,7,53,2,7,5,2,3,2,11,13,5,2,3,7,2,19,5,3,2,7,3,3,3,2,11,2,5,11,5,2,3,2,2,3,43,11,3,2,19,3,3,31,11,3,59,17,2,2,7,5,37,2,3,11,2,11,59,83,11,3,31,17,2,3,3,11,3,37,23,3,23,2,3,7,5,23,41,3,2,2,2,2,5,3,11,7,17,5,5,3,11,2,2,31,23,7,11,2,2,3,7,3,13,17,19,17,2,3,13,19,3,2,47,2,7,3,7,3] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_2179_2307 : Verified 2179 2307 :=
  verifyRows 2179 [7,83,3,5,2,5,5,5,41,7,59,3,2,11,2,5,3,83,23,2,2,3,3,7,5,2,2,41,7,5,23,3,2,3,2,5,3,2,5,7,2,11,2,5,19,3,3,61,2,31,19,2,3,7,2,2,2,2,11,5,7,3,2,11,2,5,17,3,5,3,2,3,3,2,2,3,19,3,5,11,5,13,3,2,2,2,3,61,2,2,37,2,19,3,2,23,3,2,3,3,2,5,19,5,5,7,2,3,3,2,3,5,5,5,17,11,13,3,3,17,11,3,2,11,3,3,2,3] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_2307_2435 : Verified 2307 2435 :=
  verifyRows 2307 [3,5,2,11,23,3,2,3,2,83,101,3,2,5,3,2,13,2,3,13,2,3,2,13,3,3,13,2,13,41,3,13,11,3,3,5,47,2,3,31,13,7,7,29,2,11,47,2,3,31,3,17,3,2,3,3,2,37,2,11,2,13,2,5,5,29,2,5,47,11,5,2,29,3,3,3,3,2,3,23,11,67,5,2,2,3,2,3,11,2,5,2,17,11,3,11,2,2,3,2,2,3,41,3,13,3,7,2,3,3,3,2,3,2,11,3,3,2,7,13,5,7,11,3,7,2,7,5] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_2435_2563 : Verified 2435 2563 :=
  verifyRows 2435 [7,7,7,2,2,7,23,5,59,2,13,7,31,61,7,3,3,2,2,17,11,3,31,73,5,11,7,13,13,2,3,3,19,3,47,3,3,19,2,7,2,2,2,2,7,3,3,3,2,3,23,2,2,5,3,5,3,3,3,13,13,2,5,5,3,11,17,7,3,3,2,5,11,2,11,2,5,5,3,7,7,2,3,5,2,3,3,17,2,3,13,2,13,2,3,5,2,29,3,2,3,17,3,11,2,11,2,5,2,2,3,3,3,2,3,3,11,5,7,17,3,43,2,2,2,3,13,43] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_2563_2691 : Verified 2563 2691 :=
  verifyRows 2563 [41,2,31,2,3,83,7,2,2,3,11,73,2,2,5,11,2,3,5,2,3,11,11,3,23,5,41,2,5,5,5,7,5,3,2,2,17,17,11,89,5,101,2,2,23,3,3,23,7,2,3,67,11,5,43,7,2,83,2,2,13,2,2,2,2,2,2,3,41,3,3,3,31,3,3,7,11,3,7,3,7,2,2,2,5,2,3,2,5,2,5,3,3,2,3,3,3,13,2,7,11,5,3,3,19,2,2,11,3,5,41,3,5,5,3,3,5,3,13,23,11,3,5,2,3,5,17,31] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_2691_2819 : Verified 2691 2819 :=
  verifyRows 2691 [3,11,7,17,23,2,2,43,2,2,5,2,11,3,17,11,7,11,11,2,2,17,3,2,2,3,3,3,41,5,47,19,2,53,2,13,47,5,13,2,3,3,59,29,29,17,31,7,2,43,3,3,3,3,2,2,11,3,2,5,19,29,3,5,7,3,5,3,5,2,2,17,5,2,5,2,2,17,5,2,2,5,11,2,11,11,41,3,7,5,11,3,5,2,2,2,5,2,3,2,3,2,2,11,2,2,7,3,7,2,11,5,5,2,3,7,2,2,7,3,5,5,2,5,11,2,3,2] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_2819_2947 : Verified 2819 2947 :=
  verifyRows 2819 [2,7,3,11,19,19,3,19,3,11,3,2,2,107,3,13,19,7,29,13,3,2,3,13,3,2,41,3,3,7,2,3,3,2,2,2,2,5,5,41,2,2,11,5,37,5,2,3,2,3,7,11,2,17,2,5,19,2,19,2,3,73,3,11,2,7,3,83,13,5,19,2,5,11,2,5,31,2,2,7,3,2,3,31,2,3,3,5,3,2,2,2,5,3,3,23,2,2,11,3,3,37,3,17,2,5,3,73,17,3,3,5,17,11,7,43,11,3,3,17,2,7,5,2,3,2,3,197] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_2947_3075 : Verified 2947 3075 :=
  verifyRows 2947 [3,2,2,2,5,2,2,3,2,2,2,2,17,2,5,7,11,13,11,5,19,2,3,3,5,2,7,3,2,23,7,5,11,3,2,5,2,2,3,5,11,5,2,3,2,3,23,2,2,3,3,2,3,13,5,3,7,29,13,3,3,3,2,3,11,3,37,5,3,11,3,13,13,17,2,2,2,19,29,3,11,31,3,2,31,11,5,2,11,3,3,17,2,2,11,59,47,5,3,2,3,41,3,5,17,2,3,3,7,3,2,2,3,2,7,3,2,3,7,7,2,3,2,13,3,5,2,11] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_3075_3203 : Verified 3075 3203 :=
  verifyRows 3075 [7,13,3,2,2,3,3,3,2,2,107,3,5,19,3,2,11,3,7,23,5,3,2,3,19,31,3,2,2,5,23,2,11,37,2,3,29,5,3,5,2,2,2,7,3,7,5,5,2,7,3,5,13,2,7,3,2,19,17,53,2,2,7,3,7,5,5,31,5,13,13,2,7,2,5,2,2,2,7,2,29,2,2,3,3,2,11,5,37,29,2,17,2,11,5,3,2,11,11,11,3,3,2,3,2,19,3,7,3,2,23,3,5,3,2,2,3,11,3,23,2,3,2,17,2,5,7,2] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_3203_3331 : Verified 3203 3331 :=
  verifyRows 3203 [3,5,17,3,13,2,2,13,23,2,13,17,2,3,2,29,19,37,5,3,23,2,5,11,2,17,5,5,2,17,41,103,2,2,3,5,3,7,2,5,2,5,5,7,5,3,3,17,7,2,3,17,2,7,3,3,3,3,3,19,13,31,3,13,47,7,2,2,13,3,5,3,2,5,2,3,7,13,5,2,3,3,2,11,2,3,7,11,2,19,13,3,2,5,3,3,2,2,7,11,7,2,2,3,2,11,19,2,3,2,2,3,5,11,2,5,5,3,3,17,3,13,3,23,13,11,2,2] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_3331_3459 : Verified 3331 3459 :=
  verifyRows 3331 [5,5,11,13,5,17,5,5,23,3,2,61,11,2,2,13,2,2,5,3,3,2,29,11,2,5,7,2,3,5,7,5,3,7,3,11,13,11,19,2,11,7,5,5,2,3,3,2,2,3,2,31,5,3,2,5,7,31,3,2,5,2,5,3,7,3,3,23,2,2,41,2,3,13,3,31,19,17,41,11,3,2,3,3,13,3,3,3,2,19,5,41,11,13,5,53,3,11,3,3,5,2,17,29,5,5,37,2,3,3,2,13,5,11,2,7,17,5,3,3,5,13,3,13,2,79,29,7] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_3459_3587 : Verified 3459 3587 :=
  verifyRows 3459 [83,17,41,2,19,3,19,2,3,3,13,3,3,43,2,31,3,13,5,5,23,23,13,2,2,2,23,3,5,3,7,2,3,11,3,5,13,2,7,3,5,2,19,2,2,29,13,5,13,19,3,11,3,13,7,7,3,3,3,3,7,3,2,2,3,3,2,2,23,2,7,7,5,3,3,3,7,5,3,2,11,2,7,13,2,2,2,5,5,2,7,13,2,11,97,11,2,2,2,2,71,3,5,11,3,3,13,3,2,2,7,2,5,17,3,53,23,3,3,3,29,2,3,17,5,2,2,2] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_3587_3715 : Verified 3587 3715 :=
  verifyRows 3587 [11,11,7,5,5,29,5,5,3,2,13,2,37,2,5,3,101,17,37,3,2,2,2,11,11,2,17,5,2,3,23,13,3,2,3,7,3,17,5,2,3,2,43,2,2,19,2,13,29,2,3,2,2,13,3,13,17,13,13,5,47,29,2,13,17,5,3,7,3,13,29,17,2,2,5,7,2,7,7,19,13,11,5,17,11,5,19,3,5,13,2,17,19,3,29,29,2,2,13,3,2,2,3,7,2,3,2,2,2,11,2,41,2,7,2,3,3,11,2,31,2,2,3,7,2,13,2,3] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_3715_3843 : Verified 3715 3843 :=
  verifyRows 3715 [3,2,7,3,3,7,5,3,2,3,23,2,2,2,3,3,3,37,2,3,3,3,7,13,5,5,2,2,3,17,3,3,41,2,41,2,23,11,3,61,97,5,3,5,11,47,2,41,7,71,3,37,11,11,7,3,7,3,7,2,5,3,37,7,3,3,5,43,73,29,5,2,13,2,2,47,2,2,2,7,5,3,2,2,3,2,7,7,3,19,3,3,17,13,11,2,47,5,17,13,31,3,5,3,37,3,11,2,3,5,2,7,11,5,2,7,2,3,3,5,3,2,17,29,2,3,19,3] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_3843_3971 : Verified 3843 3971 :=
  verifyRows 3843 [7,7,3,11,59,2,2,2,3,2,3,2,3,3,2,19,7,5,23,2,5,11,13,3,31,2,2,2,3,5,2,2,31,2,7,5,7,3,11,2,5,2,13,2,2,3,3,13,2,67,3,3,2,2,2,3,13,3,23,13,19,5,2,3,13,47,3,3,7,5,3,5,19,37,31,2,13,11,2,23,7,2,5,37,2,113,13,5,11,2,11,7,5,2,29,2,3,3,97,2,2,3,2,5,3,53,3,11,17,11,13,2,3,5,31,17,3,23,2,5,37,13,2,2,2,2,5,5] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_3971_4099 : Verified 3971 4099 :=
  verifyRows 3971 [5,3,2,2,7,17,5,2,2,17,5,13,2,7,19,3,3,5,2,47,13,47,7,13,2,19,23,47,2,13,2,3,41,3,2,3,2,5,5,13,13,3,5,23,3,3,2,3,2,2,5,3,5,2,3,17,2,2,2,2,23,5,3,7,2,11,3,47,2,3,101,5,5,2,2,3,5,7,2,2,17,13,3,7,7,13,2,41,2,2,3,3,7,2,5,5,3,7,13,11,5,13,3,23,3,5,2,13,2,11,3,5,2,2,43,5,13,7,3,2,2,5,11,2,3,7,2,2] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_4099_4227 : Verified 4099 4227 :=
  verifyRows 4099 [2,19,5,13,29,7,2,3,73,41,7,2,53,3,3,2,19,2,2,2,11,17,5,11,13,2,2,17,3,13,19,5,19,17,3,3,23,13,5,13,11,19,7,53,37,3,5,2,3,2,41,5,5,7,2,2,2,2,2,7,5,11,2,2,7,3,3,11,13,5,2,127,3,3,2,2,53,5,3,3,2,17,5,3,2,2,3,5,11,7,2,31,3,5,2,3,3,37,3,7,29,3,7,5,37,3,3,3,3,3,29,5,2,2,67,3,5,11,11,53,19,11,2,2,7,3,2,2] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_4227_4355 : Verified 4227 4355 :=
  verifyRows 4227 [2,2,23,3,11,7,29,3,29,127,2,5,3,3,11,17,19,2,3,3,3,47,2,101,2,5,7,3,7,13,2,2,2,3,7,3,3,7,37,43,41,3,7,3,5,23,3,11,3,2,31,2,83,2,29,3,3,3,3,29,17,7,2,2,5,5,29,7,3,41,3,5,2,13,11,2,61,2,5,11,23,5,2,11,11,5,2,2,17,2,3,37,2,17,2,5,7,5,2,3,2,19,5,3,31,2,3,2,2,5,37,3,113,3,2,3,3,11,5,3,2,5,3,3,29,5,3,2] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_4355_4483 : Verified 4355 4483 :=
  verifyRows 4355 [7,3,2,2,5,7,5,2,2,2,7,2,5,5,5,7,19,5,11,19,19,31,3,19,43,2,13,3,2,2,11,5,3,7,11,47,3,13,3,3,3,2,2,2,11,3,7,13,5,29,3,73,11,2,5,7,3,3,7,3,47,3,3,3,3,2,3,2,5,2,17,2,5,3,2,13,3,5,2,2,11,2,41,2,5,2,5,19,11,7,2,71,23,5,2,2,17,2,13,5,7,11,3,5,7,29,13,2,2,2,13,7,3,2,2,3,5,7,5,5,2,3,3,89,11,2,5,2] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_4483_4611 : Verified 4483 4611 :=
  verifyRows 4483 [5,2,7,13,2,71,2,2,3,23,3,3,17,2,3,13,5,11,2,2,3,2,3,11,3,5,3,37,3,3,2,5,2,47,11,3,23,7,3,19,3,2,3,3,13,7,5,3,23,2,3,23,7,3,3,11,2,5,3,3,11,2,13,3,5,3,41,2,2,13,2,3,2,2,13,2,2,3,7,19,41,3,17,17,5,2,3,13,101,13,2,2,5,47,5,3,5,5,37,11,7,3,5,2,2,7,3,5,29,7,11,13,2,3,3,7,3,2,13,2,2,19,3,2,2,2,3,2] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_4611_4739 : Verified 4611 4739 :=
  verifyRows 4611 [5,3,13,11,2,2,13,11,19,7,3,37,31,2,3,5,3,2,7,2,11,5,3,2,5,2,2,3,5,53,13,19,3,13,3,2,13,13,5,19,23,2,3,3,7,2,5,2,17,3,3,23,3,11,5,3,3,5,2,113,2,53,43,5,71,41,2,7,5,5,29,3,7,3,3,11,3,29,2,2,2,23,11,3,3,7,11,211,17,2,2,3,2,11,3,17,47,19,2,23,3,13,2,13,11,5,7,7,13,3,2,13,3,2,5,2,19,2,2,2,2,2,2,2,5,2,11,13] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_4739_4867 : Verified 4739 4867 :=
  verifyRows 4739 [13,3,2,13,5,2,2,3,7,5,17,3,3,7,13,17,2,43,2,3,5,3,2,2,2,7,3,7,37,5,2,3,41,3,13,7,17,37,2,17,23,2,2,13,5,2,3,2,5,5,7,7,11,13,3,5,11,17,13,13,2,3,19,2,3,2,2,11,2,3,5,7,3,2,2,5,11,5,3,5,3,5,2,17,5,11,29,11,2,43,3,41,2,3,2,11,3,5,5,17,3,11,3,2,11,3,13,11,7,17,2,19,19,19,2,3,71,3,3,3,19,3,19,43,5,7,2,53] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_4867_4995 : Verified 4867 4995 :=
  verifyRows 4867 [83,67,2,5,2,7,7,47,31,2,5,2,5,5,2,13,2,37,7,5,3,7,2,2,17,3,17,3,7,5,3,2,11,13,3,2,2,2,5,2,3,3,3,3,11,3,29,2,3,5,13,13,2,13,41,2,2,31,2,2,2,3,2,3,2,11,3,5,2,7,2,17,7,7,7,2,2,2,37,11,2,2,3,2,3,2,3,2,3,23,3,23,3,5,3,13,2,2,3,3,2,19,31,11,5,2,97,5,5,5,37,7,5,5,3,5,3,5,7,2,13,23,11,11,5,17,47,2] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_4995_5123 : Verified 4995 5123 :=
  verifyRows 4995 [11,3,7,3,11,3,2,5,2,11,3,5,2,2,5,5,5,5,7,2,5,23,3,5,3,79,2,3,53,3,5,3,2,17,7,3,5,13,7,7,2,2,3,5,2,13,101,3,5,2,3,5,2,23,7,2,2,3,13,2,5,19,5,13,23,2,2,2,2,3,3,2,7,73,2,3,2,5,13,2,2,2,5,11,5,2,5,13,3,2,37,11,3,47,3,11,17,7,2,89,3,3,3,5,3,7,19,2,2,7,41,31,2,47,41,3,2,2,3,2,13,2,3,2,2,5,7,2] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_5123_5251 : Verified 5123 5251 :=
  verifyRows 5123 [7,3,5,3,3,3,3,7,3,47,11,5,41,3,3,5,3,2,2,2,11,3,5,2,13,2,37,7,3,11,2,2,11,2,3,2,2,17,3,11,7,3,2,5,23,5,2,7,5,31,41,7,23,17,2,47,2,3,7,2,2,5,83,2,2,7,3,3,3,2,41,19,3,19,2,2,3,7,13,29,2,5,11,2,2,2,3,7,3,31,3,5,11,5,2,7,3,5,2,5,11,5,5,3,5,23,2,31,2,5,11,2,3,2,29,37,11,2,2,19,2,43,2,5,17,2,2,37] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_5251_5379 : Verified 5251 5379 :=
  verifyRows 5251 [3,2,3,7,3,2,3,2,3,3,3,29,11,3,3,2,13,3,2,7,3,3,17,7,3,37,3,3,17,3,3,2,3,7,17,2,5,2,61,2,17,89,7,2,5,5,3,2,11,11,2,3,2,41,3,2,5,7,3,2,23,13,3,13,2,61,5,3,2,2,13,2,3,3,7,2,47,113,3,2,2,3,2,2,3,2,2,7,2,13,17,5,2,3,3,31,5,3,2,23,5,5,3,2,5,11,3,2,3,47,29,2,5,23,2,2,2,97,2,3,2,5,5,5,37,7,29,2] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_5379_5507 : Verified 5379 5507 :=
  verifyRows 5379 [11,5,2,47,17,7,7,7,19,13,13,3,3,2,31,11,5,2,31,2,3,3,3,59,3,73,3,31,17,149,13,31,17,17,37,3,2,37,17,3,47,2,31,3,5,5,19,5,3,2,3,17,37,13,3,3,2,3,43,5,13,7,13,2,17,2,2,101,2,2,2,11,5,3,11,2,7,11,5,3,2,13,3,11,13,7,2,5,2,23,7,3,29,5,11,2,3,2,2,3,29,5,2,31,3,5,3,19,13,2,3,3,2,3,2,241,2,2,23,5,11,3,5,41,5,3,5,7] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_5507_5635 : Verified 5507 5635 :=
  verifyRows 5507 [17,17,3,2,3,3,3,3,29,3,23,3,17,2,7,13,2,11,17,5,2,17,11,13,17,2,7,5,11,3,2,3,3,2,7,2,2,19,3,53,3,3,2,3,3,11,3,2,2,5,29,3,3,71,3,2,2,5,2,7,7,2,2,3,2,3,2,5,3,3,3,17,2,13,23,5,3,2,2,3,31,2,2,2,3,5,3,7,3,13,2,3,2,3,5,5,5,3,2,3,2,7,2,5,2,2,2,2,23,5,3,2,3,5,47,7,5,2,7,5,3,5,17,11,19,11,3,3] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_5635_5763 : Verified 5635 5763 :=
  verifyRows 5635 [2,2,2,13,3,5,41,3,7,7,2,13,2,7,5,5,3,7,7,2,7,3,3,23,3,2,5,7,11,23,2,5,2,7,5,5,3,5,23,13,19,13,3,2,43,37,5,3,41,3,2,3,11,5,3,2,2,5,2,7,11,2,3,7,3,3,2,23,3,2,2,2,2,2,2,3,2,11,37,2,5,2,3,2,3,11,2,3,5,37,2,2,7,2,2,43,2,2,3,5,11,7,19,13,2,2,5,13,5,2,7,11,5,23,19,3,3,19,11,3,2,7,47,2,17,59,5,2] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_5763_5891 : Verified 5763 5891 :=
  verifyRows 5763 [2,2,41,2,3,5,13,2,2,23,7,2,3,3,43,3,3,3,5,11,3,2,7,7,5,13,7,3,7,2,2,2,2,3,5,11,11,5,37,23,13,2,3,3,3,5,37,2,7,3,2,11,5,2,3,7,107,17,3,2,2,3,41,3,11,2,53,3,2,11,3,5,2,11,37,5,2,3,29,3,5,2,19,7,37,53,2,13,5,3,2,19,5,3,2,5,17,7,2,2,3,13,13,7,5,3,3,7,43,7,7,71,31,2,61,3,2,7,7,3,7,3,3,13,3,11,113,17] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_5891_6019 : Verified 5891 6019 :=
  verifyRows 5891 [3,11,19,3,7,2,2,2,31,5,7,3,3,2,3,3,11,2,7,2,3,2,17,2,2,53,7,17,2,3,13,5,13,7,2,2,2,19,5,2,3,3,2,3,2,3,3,5,2,3,3,3,3,13,3,23,3,2,37,2,5,11,2,5,71,5,2,2,3,2,149,5,2,2,31,2,5,13,5,2,3,3,17,5,7,2,3,3,5,2,3,2,7,3,2,3,3,2,3,7,5,17,13,79,2,13,5,5,53,3,2,11,11,5,2,7,29,5,2,53,5,7,3,7,5,2,2,13] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_6019_6147 : Verified 6019 6147 :=
  verifyRows 6019 [2,3,3,7,3,3,2,11,19,11,5,11,29,3,2,71,7,5,13,7,5,2,23,37,3,2,5,3,2,3,3,2,3,11,2,61,3,5,3,7,2,37,47,5,59,7,3,53,2,59,3,2,3,47,2,2,11,2,2,2,2,11,7,7,5,3,2,2,13,13,2,23,17,5,2,29,2,5,5,3,3,3,2,5,3,7,3,3,2,3,3,3,3,2,13,97,17,5,7,3,17,3,3,2,5,2,3,2,3,3,7,5,7,2,3,2,2,2,11,13,5,11,2,2,3,2,23,2] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_6147_6275 : Verified 6147 6275 :=
  verifyRows 6147 [11,3,5,29,5,5,13,31,3,2,3,3,5,3,3,7,5,2,19,3,7,7,3,2,23,11,5,11,11,3,19,17,2,3,3,3,19,5,23,5,3,11,3,97,23,2,3,5,3,29,73,7,61,3,41,11,3,2,5,3,53,17,3,3,3,3,13,3,2,2,3,2,3,13,7,5,5,11,61,7,13,2,2,13,19,2,5,2,3,5,5,19,2,11,5,2,13,2,19,41,5,3,7,5,5,11,7,3,3,3,3,7,3,2,19,7,7,3,47,31,3,2,2,2,5,5,3,7] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_6275_6403 : Verified 6275 6403 :=
  verifyRows 6275 [2,5,37,17,7,7,2,5,131,7,17,3,17,13,11,29,3,11,2,2,37,5,13,7,17,2,43,3,3,7,2,41,11,5,3,2,13,2,3,5,17,3,3,11,3,3,53,3,7,3,11,3,2,2,2,23,7,2,2,13,2,5,3,5,2,2,11,2,3,7,2,2,3,7,2,3,5,2,2,2,31,2,7,2,2,13,19,3,2,13,3,41,13,3,2,2,2,7,3,3,7,2,2,13,2,3,13,7,17,3,19,2,3,2,3,3,17,2,7,3,5,2,17,7,2,7,3,3] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_6403_6531 : Verified 6403 6531 :=
  verifyRows 6403 [2,53,17,2,2,3,3,2,2,3,3,3,3,2,5,2,11,13,2,3,2,23,29,2,2,2,2,7,23,2,31,2,2,13,2,3,11,5,3,2,2,7,3,2,13,7,13,2,3,2,2,3,5,19,2,3,23,2,11,37,23,5,11,2,2,2,5,2,5,3,2,23,11,5,53,19,2,2,2,2,2,2,7,2,37,5,31,2,5,5,3,11,7,71,13,23,2,5,2,7,2,3,2,3,53,2,11,2,5,5,3,2,3,17,3,11,13,5,13,5,3,3,37,3,17,13,2,2] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_6531_6659 : Verified 6531 6659 :=
  verifyRows 6531 [2,13,2,3,2,2,19,5,5,13,3,2,3,11,3,13,2,2,2,3,2,2,3,2,3,3,2,2,2,7,5,3,3,19,3,7,11,2,11,13,23,2,3,2,11,5,2,13,3,2,2,2,17,3,3,2,5,2,11,89,11,3,2,7,17,2,13,5,3,47,13,37,11,11,11,3,5,2,2,3,17,2,7,17,3,3,3,7,11,23,11,2,17,2,3,2,17,17,7,7,5,2,5,11,7,7,3,2,7,3,67,11,13,7,5,97,2,29,11,2,2,7,17,5,7,2,13,103] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_6659_6787 : Verified 6659 6787 :=
  verifyRows 6659 [3,3,13,2,3,13,41,31,37,29,7,2,2,11,5,2,2,5,3,5,2,2,2,3,11,5,2,17,43,2,2,2,3,2,2,2,3,5,2,7,2,5,23,2,131,31,13,3,2,2,2,5,3,7,3,7,5,3,17,2,2,3,7,2,2,11,11,5,37,3,13,5,3,47,5,3,2,13,3,7,7,3,53,19,2,17,31,3,7,2,3,2,2,19,5,3,113,2,3,7,3,2,7,3,11,23,3,2,2,2,2,2,7,3,7,5,7,5,2,2,11,3,3,3,3,53,3,61] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_6787_6915 : Verified 6787 6915 :=
  verifyRows 6787 [11,5,3,2,23,19,17,5,7,2,3,23,2,3,13,53,2,3,37,23,13,7,2,2,13,3,11,2,2,3,5,7,7,13,13,73,3,53,3,13,2,3,3,5,11,61,3,2,3,2,5,71,2,19,17,2,3,3,11,3,3,3,5,2,149,3,2,3,7,5,2,3,23,3,3,3,2,13,19,3,5,3,2,2,7,11,2,31,2,37,3,5,11,2,5,5,2,5,2,2,7,2,2,5,5,3,2,11,2,5,3,2,47,17,5,2,2,13,2,17,2,2,7,2,29,5,5,3] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_6915_7043 : Verified 6915 7043 :=
  verifyRows 6915 [7,29,29,3,3,11,2,3,3,5,3,7,2,5,13,3,31,5,3,7,5,3,3,5,3,7,13,2,47,2,37,2,2,19,5,5,2,23,11,2,2,5,5,5,7,3,3,7,3,2,23,3,3,3,3,2,2,5,3,7,7,13,3,13,7,41,5,3,5,3,41,29,19,7,3,2,2,5,3,2,2,5,2,89,2,97,3,7,3,2,5,13,5,277,11,5,11,31,13,5,11,5,11,29,19,3,7,2,2,3,2,5,83,19,3,5,29,3,3,2,2,41,2,5,3,2,2,7] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_7043_7171 : Verified 7043 7171 :=
  verifyRows 7043 [3,3,3,3,13,2,2,3,13,3,7,19,13,3,29,5,3,13,3,41,2,5,3,17,3,7,17,3,7,3,3,3,2,7,3,5,2,19,7,5,2,2,3,2,5,2,2,2,17,11,11,3,7,5,11,23,37,2,17,3,11,3,29,5,13,2,3,2,5,2,5,3,2,17,2,7,11,7,2,173,3,5,3,7,7,17,3,19,19,2,7,3,11,5,73,2,13,11,5,2,2,3,61,3,11,3,3,3,5,11,3,5,5,3,23,2,2,17,2,23,13,23,11,7,3,2,3,29] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_7171_7299 : Verified 7171 7299 :=
  verifyRows 7171 [2,31,17,2,5,7,11,2,2,37,11,7,5,41,7,3,11,13,3,47,11,3,3,19,11,7,31,3,2,43,3,71,11,7,31,5,5,107,3,3,5,2,3,5,3,2,5,2,5,3,2,7,2,47,5,3,3,2,3,53,13,5,2,11,7,5,5,11,3,3,2,2,2,13,5,2,2,73,5,3,3,3,5,3,13,3,47,13,11,2,2,2,11,2,23,7,5,11,127,3,5,7,2,3,3,2,2,2,11,11,11,7,2,11,13,3,2,23,2,5,19,41,41,13,2,2,2,13] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_7299_7427 : Verified 7299 7427 :=
  verifyRows 7299 [5,5,7,2,3,7,5,3,2,23,19,23,2,17,19,2,2,2,5,7,3,5,7,17,17,2,11,2,3,17,5,2,2,19,5,2,2,7,2,2,5,3,5,17,5,3,3,3,2,3,2,5,3,2,2,11,2,3,3,2,3,73,11,11,2,2,3,3,2,3,2,2,3,2,2,5,11,11,5,5,3,2,2,11,2,2,13,5,7,2,19,2,29,2,7,13,2,2,11,2,3,2,3,2,2,11,2,11,31,2,2,2,2,2,3,7,19,17,5,2,2,2,29,7,5,2,3,3] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_7427_7555 : Verified 7427 7555 :=
  verifyRows 7427 [17,13,2,2,2,29,3,11,11,7,19,2,41,3,3,5,7,2,3,2,3,17,23,11,7,2,17,3,3,7,3,19,7,3,11,2,3,2,2,5,5,7,2,7,2,3,7,5,5,5,5,2,37,2,3,3,3,5,41,7,11,61,3,7,7,3,7,11,2,17,37,3,2,23,11,3,2,3,5,2,5,3,31,7,3,7,13,59,53,3,13,43,11,2,43,11,7,3,11,5,19,7,19,11,29,3,47,3,5,43,3,11,23,19,2,31,13,7,3,3,2,43,3,17,47,3,29,11] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_7555_7683 : Verified 7555 7683 :=
  verifyRows 7555 [23,7,3,7,47,3,5,2,3,7,41,5,43,7,19,3,17,5,2,2,3,2,17,3,7,2,3,11,47,2,7,7,2,3,3,2,11,2,11,23,7,151,5,2,3,7,13,2,3,3,5,2,29,17,3,2,3,19,5,2,13,11,5,5,3,17,31,23,3,5,17,53,41,5,3,37,5,7,3,23,13,11,3,2,13,5,3,17,5,23,7,3,2,2,13,3,5,5,7,3,2,2,7,3,2,2,3,3,5,5,37,3,5,7,3,2,2,3,17,5,7,2,3,3,23,17,3,2] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_7683_7811 : Verified 7683 7811 :=
  verifyRows 7683 [11,3,5,5,163,23,5,2,3,3,3,31,3,2,2,29,5,7,5,71,3,17,3,3,47,7,3,17,3,2,13,2,2,47,2,2,7,7,109,3,3,7,11,2,2,7,3,2,7,17,3,19,2,2,13,5,5,41,7,23,3,2,3,3,2,41,11,2,5,5,2,5,7,3,3,3,11,11,5,3,3,3,2,5,13,3,19,7,3,2,3,2,2,3,2,3,3,2,47,11,37,3,3,13,17,2,2,7,2,2,2,2,5,5,3,2,19,3,2,3,5,19,2,23,3,2,3,2] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_7811_7939 : Verified 7811 7939 :=
  verifyRows 7811 [2,5,7,3,7,11,3,5,5,17,2,11,2,73,13,7,3,13,11,23,31,3,3,3,31,37,11,5,53,2,13,3,37,5,2,3,2,5,11,5,3,2,11,3,5,3,7,2,3,73,7,101,2,5,2,7,11,7,3,3,5,89,2,7,3,109,3,5,11,13,2,3,5,2,3,3,3,2,11,3,13,3,5,3,2,3,2,2,11,3,53,2,7,17,5,11,2,5,5,3,3,7,2,2,13,3,5,2,2,2,5,3,2,3,19,3,7,2,41,3,29,2,3,2,2,3,11,2] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_7939_8067 : Verified 7939 8067 :=
  verifyRows 7939 [5,17,3,2,7,2,2,2,7,23,17,2,3,5,2,3,11,2,47,17,19,7,2,2,11,2,2,11,2,5,3,3,5,5,2,3,2,2,47,31,11,3,29,2,3,3,43,3,13,2,101,7,19,5,31,3,3,2,2,5,3,2,3,2,2,3,3,3,7,2,3,2,3,2,5,3,61,31,37,5,2,67,3,2,2,13,5,11,5,41,3,3,2,2,2,5,2,2,3,17,17,3,3,2,2,7,53,71,11,5,2,2,11,2,13,11,3,2,5,3,5,3,7,2,2,5,5,11] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_8067_8195 : Verified 8067 8195 :=
  verifyRows 8067 [11,2,2,2,19,5,2,2,7,2,2,3,5,5,13,2,5,3,5,3,7,2,3,23,11,19,7,23,7,2,3,37,13,3,2,17,11,7,47,7,2,47,73,5,3,2,13,5,2,2,7,2,5,3,3,23,2,53,3,11,5,67,2,2,13,7,5,2,7,3,19,17,31,7,13,2,3,5,5,5,5,73,5,5,37,2,31,107,13,2,2,3,3,5,7,2,13,2,5,5,5,3,7,2,29,3,5,2,3,13,47,107,2,2,5,137,2,7,3,5,3,5,5,3,3,2,3,3] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_8195_8323 : Verified 8195 8323 :=
  verifyRows 8195 [2,2,13,3,3,3,2,2,19,11,5,13,2,2,2,5,2,7,7,17,13,11,79,5,13,3,3,3,3,7,7,13,2,5,3,5,5,2,11,19,17,19,83,2,3,5,2,29,11,19,3,3,3,2,5,3,11,5,7,5,2,5,5,23,13,11,17,41,7,3,3,3,2,43,2,3,2,3,2,5,3,5,2,3,3,5,5,2,11,3,3,2,29,7,13,3,2,13,5,3,5,7,7,2,23,11,13,73,7,2,11,11,3,2,7,11,2,2,5,2,19,11,2,47,43,2,11,3] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_8323_8451 : Verified 8323 8451 :=
  verifyRows 8323 [3,7,2,5,29,13,13,2,2,5,23,7,11,2,7,5,53,3,2,2,17,2,2,2,2,5,5,5,3,29,2,11,7,2,2,2,5,59,3,2,2,2,5,5,3,3,2,2,37,19,5,2,7,2,2,3,2,5,2,3,13,2,3,11,2,7,7,5,19,7,2,67,2,7,2,5,5,41,17,7,5,23,3,2,5,5,3,53,3,5,3,3,5,5,2,23,13,2,11,5,103,13,3,3,2,7,11,41,3,29,23,2,7,3,2,3,3,2,2,3,5,3,2,2,5,2,5,13] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_8451_8579 : Verified 8451 8579 :=
  verifyRows 8451 [2,2,23,3,2,3,2,5,2,3,7,2,19,5,3,5,7,5,2,2,5,2,5,7,2,7,3,2,7,11,2,83,2,13,13,3,3,11,3,19,83,13,17,2,11,2,7,7,5,2,41,2,19,11,3,41,2,17,2,37,11,2,37,3,13,2,3,13,2,3,3,7,13,3,13,5,13,7,7,2,7,5,3,5,5,5,3,2,23,223,73,2,3,5,5,103,3,3,3,101,3,5,7,3,3,83,11,2,5,3,2,2,2,7,3,5,7,3,2,7,7,7,13,3,19,2,3,3] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_8579_8707 : Verified 8579 8707 :=
  verifyRows 8579 [5,3,7,5,2,5,23,2,7,7,2,2,2,17,5,5,7,2,13,3,37,13,11,7,2,11,19,2,3,5,2,17,5,3,89,7,113,2,2,3,5,5,7,2,17,2,2,5,2,13,29,11,2,71,2,19,2,2,11,2,5,2,5,7,5,5,19,29,13,2,2,3,17,2,2,2,3,41,3,23,37,11,2,5,2,7,3,5,3,2,5,2,3,17,2,23,13,17,3,2,2,2,2,2,3,7,2,73,23,17,2,2,3,2,2,3,5,11,3,7,5,3,7,11,2,7,13,3] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_8707_8835 : Verified 8707 8835 :=
  verifyRows 8707 [17,3,3,2,3,2,2,2,2,11,7,3,41,3,2,11,11,2,5,7,5,3,11,13,3,5,2,2,11,5,5,5,5,3,2,2,19,17,19,2,7,109,5,3,7,13,2,2,11,5,2,7,7,3,2,5,5,2,41,7,2,5,7,59,13,3,5,11,7,7,19,5,2,5,2,5,31,3,3,2,3,17,3,2,13,2,3,17,31,11,3,17,29,3,2,2,11,5,5,5,3,173,5,7,5,7,7,11,47,3,2,2,13,3,3,41,2,3,3,13,3,47,2,3,2,7,3,5] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_8835_8963 : Verified 8835 8963 :=
  verifyRows 8835 [3,7,3,11,7,5,3,31,3,11,3,2,2,23,2,7,17,3,3,3,11,2,11,2,3,13,5,2,5,2,2,3,7,5,7,2,59,19,59,5,3,5,13,31,3,3,7,5,31,5,97,3,23,2,2,3,3,5,67,3,3,2,3,19,5,5,11,3,5,31,13,5,2,17,2,5,5,5,29,2,3,19,11,3,3,31,3,2,13,2,5,11,2,5,23,2,3,7,5,31,5,2,3,47,29,29,5,3,2,19,2,2,2,2,3,5,7,3,5,2,2,3,13,2,3,5,13,5] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_8963_9091 : Verified 8963 9091 :=
  verifyRows 8963 [3,3,43,2,2,13,13,2,17,2,2,19,7,2,41,3,3,89,2,3,13,5,2,7,5,13,3,7,7,5,2,7,17,5,19,7,11,2,11,5,2,7,3,11,3,17,53,5,5,5,11,5,13,31,13,2,2,3,3,2,2,2,2,5,7,2,2,3,5,5,3,2,61,11,5,37,7,7,23,3,47,3,5,11,17,3,2,5,2,5,2,3,7,29,3,2,47,3,3,19,3,3,5,2,13,17,2,2,3,5,2,29,2,2,2,2,3,3,3,29,47,13,7,3,5,37,2,3] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_9091_9219 : Verified 9091 9219 :=
  verifyRows 9091 [13,5,3,5,5,31,11,23,23,2,11,2,3,2,3,43,2,2,19,2,5,3,7,3,2,2,3,2,11,3,2,5,2,11,3,7,3,41,7,2,2,3,2,7,2,13,2,5,3,3,13,2,2,2,5,5,13,3,11,2,23,13,2,2,5,7,29,13,3,5,11,2,3,11,2,2,19,13,5,3,7,2,71,7,5,17,5,13,17,3,5,3,11,3,11,2,5,2,3,2,7,3,5,7,31,3,2,17,23,5,2,3,2,2,19,29,37,3,2,19,3,2,2,7,11,11,2,3] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_9219_9347 : Verified 9219 9347 :=
  verifyRows 9219 [3,3,2,3,3,47,11,11,53,2,3,23,3,7,2,3,11,3,23,5,2,23,5,47,7,7,3,3,3,7,5,7,7,41,2,3,3,5,11,3,5,13,31,2,37,11,2,5,2,3,29,19,17,2,3,3,13,5,5,5,3,11,19,3,11,37,5,3,3,5,2,17,11,19,2,2,23,5,13,7,2,17,7,3,3,3,3,23,2,3,7,3,2,61,13,5,3,3,3,3,11,5,5,5,7,3,47,5,2,3,3,43,2,3,31,19,2,2,13,5,11,2,13,37,5,3,5,7] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_9347_9475 : Verified 9347 9475 :=
  verifyRows 9347 [13,5,7,2,3,2,5,7,5,3,7,5,2,3,3,11,7,5,3,2,43,3,41,2,19,5,61,5,13,2,3,11,53,2,11,2,5,3,3,3,3,5,41,3,2,11,13,3,17,5,2,3,7,2,2,3,3,2,2,7,3,41,5,3,11,13,2,7,7,2,5,17,17,11,17,3,11,2,23,83,2,11,5,19,2,3,19,2,11,7,3,2,7,2,5,13,7,3,59,11,23,3,11,3,2,5,2,5,11,2,3,43,47,2,23,5,13,2,2,17,13,5,11,3,11,13,61,11] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_9475_9603 : Verified 9475 9603 :=
  verifyRows 9475 [11,3,3,7,2,2,5,5,5,7,3,2,2,2,3,5,5,43,5,11,5,79,3,13,7,11,73,3,13,41,47,2,3,2,2,61,3,2,2,7,2,5,3,2,3,2,3,3,3,2,7,43,3,11,7,2,5,5,2,5,7,2,3,7,17,23,3,67,2,31,2,83,13,7,2,61,2,2,19,2,5,13,2,17,7,2,2,7,13,3,13,3,5,13,3,3,2,11,7,17,17,17,2,5,3,3,23,3,5,7,43,13,17,5,13,29,19,11,23,3,13,2,3,2,5,5,11,19] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_9603_9731 : Verified 9603 9731 :=
  verifyRows 9603 [3,3,2,3,37,2,2,7,5,2,3,2,2,13,2,37,5,19,3,3,5,2,5,2,5,7,5,2,5,7,5,2,5,3,5,2,3,2,5,2,2,61,2,5,2,5,47,2,41,2,11,2,3,7,7,37,17,2,3,2,2,2,2,13,2,11,2,7,3,7,11,2,3,43,5,29,3,3,2,11,2,17,3,5,11,5,41,7,113,29,17,7,19,2,13,2,2,13,5,2,5,2,3,2,7,3,2,7,5,11,3,2,2,3,2,2,19,13,7,13,3,7,13,2,2,2,71,17] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_9731_9859 : Verified 9731 9859 :=
  verifyRows 9731 [7,3,7,2,5,2,7,3,7,2,29,2,19,11,7,11,47,11,2,11,7,17,3,3,2,41,17,2,71,2,11,2,2,2,2,11,5,7,7,2,3,3,5,2,13,2,5,5,7,7,3,7,2,3,3,7,3,13,7,59,3,29,5,7,3,7,11,2,23,3,19,5,59,2,7,17,5,3,2,2,11,17,2,3,11,19,3,13,5,5,3,2,3,13,2,2,5,13,5,7,3,11,2,13,3,2,2,17,5,3,13,31,3,2,11,5,13,2,2,3,3,2,3,5,7,2,3,2] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_9859_9987 : Verified 9859 9987 :=
  verifyRows 9859 [11,2,11,3,2,23,2,3,13,2,23,2,2,2,7,13,3,3,7,2,37,11,2,5,13,2,5,3,7,7,7,17,2,2,13,3,2,13,3,7,11,11,3,3,3,11,2,3,37,5,2,3,11,5,13,11,5,13,11,107,2,3,5,2,7,2,17,17,7,7,3,29,59,2,2,7,3,11,19,2,7,5,3,17,5,3,7,31,5,5,7,7,2,53,2,19,5,11,17,2,5,3,29,17,2,7,2,19,17,3,2,11,11,71,2,5,2,5,5,13,7,5,7,29,2,7,19,3] (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem verified_9987_10001 : Verified 9987 10001 :=
  verifyRows 9987 [3,5,3,7,5,3,3,7,3,47,3,23,5,2] (by decide +kernel)

private theorem verified_3_259 : Verified 3 259 := joinRows verified_3_131 verified_131_259

private theorem verified_259_515 : Verified 259 515 := joinRows verified_259_387 verified_387_515

private theorem verified_515_771 : Verified 515 771 := joinRows verified_515_643 verified_643_771

private theorem verified_771_1027 : Verified 771 1027 := joinRows verified_771_899 verified_899_1027

private theorem verified_1027_1283 : Verified 1027 1283 := joinRows verified_1027_1155 verified_1155_1283

private theorem verified_1283_1539 : Verified 1283 1539 := joinRows verified_1283_1411 verified_1411_1539

private theorem verified_1539_1795 : Verified 1539 1795 := joinRows verified_1539_1667 verified_1667_1795

private theorem verified_1795_2051 : Verified 1795 2051 := joinRows verified_1795_1923 verified_1923_2051

private theorem verified_2051_2307 : Verified 2051 2307 := joinRows verified_2051_2179 verified_2179_2307

private theorem verified_2307_2563 : Verified 2307 2563 := joinRows verified_2307_2435 verified_2435_2563

private theorem verified_2563_2819 : Verified 2563 2819 := joinRows verified_2563_2691 verified_2691_2819

private theorem verified_2819_3075 : Verified 2819 3075 := joinRows verified_2819_2947 verified_2947_3075

private theorem verified_3075_3331 : Verified 3075 3331 := joinRows verified_3075_3203 verified_3203_3331

private theorem verified_3331_3587 : Verified 3331 3587 := joinRows verified_3331_3459 verified_3459_3587

private theorem verified_3587_3843 : Verified 3587 3843 := joinRows verified_3587_3715 verified_3715_3843

private theorem verified_3843_4099 : Verified 3843 4099 := joinRows verified_3843_3971 verified_3971_4099

private theorem verified_4099_4355 : Verified 4099 4355 := joinRows verified_4099_4227 verified_4227_4355

private theorem verified_4355_4611 : Verified 4355 4611 := joinRows verified_4355_4483 verified_4483_4611

private theorem verified_4611_4867 : Verified 4611 4867 := joinRows verified_4611_4739 verified_4739_4867

private theorem verified_4867_5123 : Verified 4867 5123 := joinRows verified_4867_4995 verified_4995_5123

private theorem verified_5123_5379 : Verified 5123 5379 := joinRows verified_5123_5251 verified_5251_5379

private theorem verified_5379_5635 : Verified 5379 5635 := joinRows verified_5379_5507 verified_5507_5635

private theorem verified_5635_5891 : Verified 5635 5891 := joinRows verified_5635_5763 verified_5763_5891

private theorem verified_5891_6147 : Verified 5891 6147 := joinRows verified_5891_6019 verified_6019_6147

private theorem verified_6147_6403 : Verified 6147 6403 := joinRows verified_6147_6275 verified_6275_6403

private theorem verified_6403_6659 : Verified 6403 6659 := joinRows verified_6403_6531 verified_6531_6659

private theorem verified_6659_6915 : Verified 6659 6915 := joinRows verified_6659_6787 verified_6787_6915

private theorem verified_6915_7171 : Verified 6915 7171 := joinRows verified_6915_7043 verified_7043_7171

private theorem verified_7171_7427 : Verified 7171 7427 := joinRows verified_7171_7299 verified_7299_7427

private theorem verified_7427_7683 : Verified 7427 7683 := joinRows verified_7427_7555 verified_7555_7683

private theorem verified_7683_7939 : Verified 7683 7939 := joinRows verified_7683_7811 verified_7811_7939

private theorem verified_7939_8195 : Verified 7939 8195 := joinRows verified_7939_8067 verified_8067_8195

private theorem verified_8195_8451 : Verified 8195 8451 := joinRows verified_8195_8323 verified_8323_8451

private theorem verified_8451_8707 : Verified 8451 8707 := joinRows verified_8451_8579 verified_8579_8707

private theorem verified_8707_8963 : Verified 8707 8963 := joinRows verified_8707_8835 verified_8835_8963

private theorem verified_8963_9219 : Verified 8963 9219 := joinRows verified_8963_9091 verified_9091_9219

private theorem verified_9219_9475 : Verified 9219 9475 := joinRows verified_9219_9347 verified_9347_9475

private theorem verified_9475_9731 : Verified 9475 9731 := joinRows verified_9475_9603 verified_9603_9731

private theorem verified_9731_9987 : Verified 9731 9987 := joinRows verified_9731_9859 verified_9859_9987

private theorem verified_3_515 : Verified 3 515 := joinRows verified_3_259 verified_259_515

private theorem verified_515_1027 : Verified 515 1027 := joinRows verified_515_771 verified_771_1027

private theorem verified_1027_1539 : Verified 1027 1539 := joinRows verified_1027_1283 verified_1283_1539

private theorem verified_1539_2051 : Verified 1539 2051 := joinRows verified_1539_1795 verified_1795_2051

private theorem verified_2051_2563 : Verified 2051 2563 := joinRows verified_2051_2307 verified_2307_2563

private theorem verified_2563_3075 : Verified 2563 3075 := joinRows verified_2563_2819 verified_2819_3075

private theorem verified_3075_3587 : Verified 3075 3587 := joinRows verified_3075_3331 verified_3331_3587

private theorem verified_3587_4099 : Verified 3587 4099 := joinRows verified_3587_3843 verified_3843_4099

private theorem verified_4099_4611 : Verified 4099 4611 := joinRows verified_4099_4355 verified_4355_4611

private theorem verified_4611_5123 : Verified 4611 5123 := joinRows verified_4611_4867 verified_4867_5123

private theorem verified_5123_5635 : Verified 5123 5635 := joinRows verified_5123_5379 verified_5379_5635

private theorem verified_5635_6147 : Verified 5635 6147 := joinRows verified_5635_5891 verified_5891_6147

private theorem verified_6147_6659 : Verified 6147 6659 := joinRows verified_6147_6403 verified_6403_6659

private theorem verified_6659_7171 : Verified 6659 7171 := joinRows verified_6659_6915 verified_6915_7171

private theorem verified_7171_7683 : Verified 7171 7683 := joinRows verified_7171_7427 verified_7427_7683

private theorem verified_7683_8195 : Verified 7683 8195 := joinRows verified_7683_7939 verified_7939_8195

private theorem verified_8195_8707 : Verified 8195 8707 := joinRows verified_8195_8451 verified_8451_8707

private theorem verified_8707_9219 : Verified 8707 9219 := joinRows verified_8707_8963 verified_8963_9219

private theorem verified_9219_9731 : Verified 9219 9731 := joinRows verified_9219_9475 verified_9475_9731

private theorem verified_9731_10001 : Verified 9731 10001 := joinRows verified_9731_9987 verified_9987_10001

private theorem verified_3_1027 : Verified 3 1027 := joinRows verified_3_515 verified_515_1027

private theorem verified_1027_2051 : Verified 1027 2051 := joinRows verified_1027_1539 verified_1539_2051

private theorem verified_2051_3075 : Verified 2051 3075 := joinRows verified_2051_2563 verified_2563_3075

private theorem verified_3075_4099 : Verified 3075 4099 := joinRows verified_3075_3587 verified_3587_4099

private theorem verified_4099_5123 : Verified 4099 5123 := joinRows verified_4099_4611 verified_4611_5123

private theorem verified_5123_6147 : Verified 5123 6147 := joinRows verified_5123_5635 verified_5635_6147

private theorem verified_6147_7171 : Verified 6147 7171 := joinRows verified_6147_6659 verified_6659_7171

private theorem verified_7171_8195 : Verified 7171 8195 := joinRows verified_7171_7683 verified_7683_8195

private theorem verified_8195_9219 : Verified 8195 9219 := joinRows verified_8195_8707 verified_8707_9219

private theorem verified_9219_10001 : Verified 9219 10001 := joinRows verified_9219_9731 verified_9731_10001

private theorem verified_3_2051 : Verified 3 2051 := joinRows verified_3_1027 verified_1027_2051

private theorem verified_2051_4099 : Verified 2051 4099 := joinRows verified_2051_3075 verified_3075_4099

private theorem verified_4099_6147 : Verified 4099 6147 := joinRows verified_4099_5123 verified_5123_6147

private theorem verified_6147_8195 : Verified 6147 8195 := joinRows verified_6147_7171 verified_7171_8195

private theorem verified_8195_10001 : Verified 8195 10001 := joinRows verified_8195_9219 verified_9219_10001

private theorem verified_3_4099 : Verified 3 4099 := joinRows verified_3_2051 verified_2051_4099

private theorem verified_4099_8195 : Verified 4099 8195 := joinRows verified_4099_6147 verified_6147_8195

private theorem verified_3_8195 : Verified 3 8195 := joinRows verified_3_4099 verified_4099_8195

private theorem verified_3_10001 : Verified 3 10001 := joinRows verified_3_8195 verified_8195_10001

end OMA.A233566Square

open OMA.A233566Square in

theorem OMA.solution : OMA.R_OeisA233566_conjecture_2_R1.H1 := by

  intro n hlo hhi

  exact verified_3_10001 n (by omega) (by omega)

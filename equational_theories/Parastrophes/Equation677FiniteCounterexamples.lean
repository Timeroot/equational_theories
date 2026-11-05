import equational_theories.Parastrophes.Attributes
import equational_theories.ManuallyProved.Equation677

/-!
# Finite E677 magmas which are not right quasigroups

Canonical tables from the Equation 677 Database maintained by ICARM
(the NSF Institute for Computer-Aided Reasoning in Mathematics, NSF Grant
DMS 2425401), originally imported there from memoryleak47/eq677.
Source URLs and byte hashes are recorded in `data/parastrophes/e677_icarm.json`.

Both tables satisfy E677 and E255, but fail right cancellation. The order-25
example is idempotent; the order-49 example is not. Ordinary kernel reduction
checks the tables, with no external certificates or native-decide axioms.
-/
namespace Parastrophes.Eq677Finite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Canonical labeling of https://eq677.icarm.cloud/magma/d732efd172ca4d7b9967999fff8c2c19. -/
def table25 : Nat :=
  0x189519655d2d5960078901192a63c5d3a5e47c22cf5c449054659860e3288d65f1614a147cd45091a8024717317531e18255a34d1ca8cc487c96509ec6602f2b5d74260b380028708c37a6353a9ac78dc2c4d662b2c90c50d554f005e9225a985de121b22778aa5425c43366a005ac858c8c44205aaeea9644a266219def1964a75c50c4d6669e81032c925511682853592c5be588c0e49a87513828b9a907a4a11db0e25c4daa8089b22b91d72714403ddf01b6d8092a664528a2a677d6d26b808bcf0c1d17028522510d183089b0102c346f32ef5928b33ba340926c3b6f6598b0a470a90ea9781011386aba2245d307b01f20a6ae29a62641b4516511d40669c414dd68c41f69b9842226fba40c6d434808b159c6ac1ace91ec2515d5486eb021f38b306a0c8d84a409a936099c782c88ad18f89717189a3889856d1c85867593c1731e04c5949322490a80bb1450ac66db931438dcc7de6c204a873c115586d342583d562a256fc11573959500a09a4cd245871685d68d5024bae56488f80e660d14dc2ce0

/-- Row-major table, 5 bits per entry. The final remainder makes the operation
well-typed independently of the data; the original table is saved in JSON. -/
@[implicit_reducible] def magma25 : Magma (Fin 25) :=
  ⟨fun x y => ⟨((table25 >>> (5 * (25 * x.val + y.val))) % 32) % 25,
    Nat.mod_lt _ (by decide)⟩⟩

theorem equation677_25 : @Equation677 (Fin 25) magma25 := by decide +kernel

theorem equation255_25 : @Equation255 (Fin 25) magma25 := by decide +kernel

theorem leftQuasigroup25 : IsSideQuasigroup .left magma25 :=
  fun x => ⟨@Eq677.eq677_leftMul_inj _ magma25 _ equation677_25 x,
    @Eq677.eq677_leftMul_surj _ magma25 equation677_25 x⟩

/-- Distinct elements 1 and 10 have the same product with 0 on the right. -/
theorem right_collision25 : magma25.op 1 0 = magma25.op 10 0 := by decide +kernel

theorem not_rightQuasigroup25 : ¬ IsSideQuasigroup .right magma25 := by
  intro h
  exact (by decide : (1 : Fin 25) ≠ 10) ((h 0).1 right_collision25)

theorem not_quasigroup25 : ¬ IsQuasigroup magma25 := fun h => not_rightQuasigroup25 h.2

/-- Canonical labeling of https://eq677.icarm.cloud/magma/fa885ee6c3df774cdb6f92bab42105d2. -/
def table49 : Nat :=
  0x30beeb6caea9279a5a6871b69865d5d65544d24503ce34c2ca2481c61440c20407a38a17e0b6eaafaf0b215cf18171b758a1a6524d45a754e44d98c40994a1cb2290800c41638247a27ecc2daeeaaf7d644901a6287596dc4d55d252730d39098f20b1e518a0e91011429218228deaabc2cbeeb605102c365a61b75ca164a75d54cd3d130e9861c82a5242141a401229237de86bb6fc2ab2e89338a158a1c65a75b9d449559740c9913cd1c92c6225001084a4385e7e4823bacaeab6fc2354c1c275969c6e86145d39d258f9903513a520624a2c402914305f89e82192faacbb0b6b79234811b759a1c61a5675935d498e30f41128694b2470431400a981f86392298e34c3d0470929a259d35925d552385e7e08851030810186d975c6881ca1892eaaecbeeb691440810c09b0967a247e381e8a1beeaedb2a20728624b5945d349575c6da65830f35140e9227a38607e7a30a669491cb20a19a65c61b76eb6fb2aac204400315039134c3d75955134a861b75c65a9699f092640f38c351003045102513592557b6cbaaaef85f8e089e2882c71899d34955d45a89649b0a421410c010b2892071a089f7a384e35030f46caadaefb9a65c61b7652881c62c9a66a249f0beabacb6b38d40c3d171a75961b7a38a17e04954d75940811000c52891889472c135d912b30bedbaba8f40e44c999718a1b69e8e285f8145975674c3102140a492e518a20711062452eb30aedaaf30e3e644da196dd69c7a38a17e04e75564970020e91412062c91ca94031c915aabb70becb8d4663903db6196a875e8e285f8164d25179c11690840c69472c824a1516645afaabb30bad42634f38c69ba1c7587a38a17e09d75135521290430801c824a2e51833da917aedbafab0b2631140d39875c6d9a1e8e285f8155274935a900510108b1ca94918808e6e44edbacaabbf044f30d9907686987197a38a17e05d25a7515143001a44140044a420cdb0856886281f8e47b0b6aaeebcb2461e52979d44964dd71b69961131098e3c404300216932a1d7a1f8e17a4822af0bacbed24a20b1a54d64a755475c6da65839044f98d0c216900110eb4a4a88e18a47de82eab0bebb0620994b1e74d55d459d71b69960d98f40c442100143a413eb196a207a48628dfb6fb30aae1cb9482895524d49d775c6da65840d30e466069083100151bc95288a07a385f92ab2dbb0ae518b2872125d65539dd71b69960f3a630d4000e904510242e2d3a1e91f8a0863b2bbeab702a51c92065159d65d275c6da65899138d3cc7a181f8e29276aa08f1c62a52482dd6d8668730b2bbedb850c006911198e3103575955134a379f8a09219d9ac144628b2479486dc69d628bf0b6abac0c40850293503263ce5d65544d289f85e92382772c10c22524a2c61d869ba1d66daf0bafa80083a4506634f44e4175955134a192381e7e29d8bc04091c62252ca65da1a71bb2eab0aed045a421033cc34e9915d65544d27e092189e8e76ee0ce2c894628726861d7196abaacb70be900510108c4503cd9975955134a08e291f85e9ddb4534a2c81c626572865b698aafbabb3012904308038f99044c5d65544d275b698668709054ae19903ce30d445004a420d75524e75b0aafbacb5e8a07e48cb94818a1dca1d65b6982c04ef7e640f38c351084143a415565174a7bb0b2bb6a8a385e8241ca1a52486dc65a758a06096aa39903ce30d441a431001525159d74ecbf0b6eae086291e7e51c92c829a6687186dd2834ae82640f38c3511010021694d79d4595aadaf0bec7de9218e22461c894b65d62869c6c8155b629903ce30d4430a900112749759352faeab30ba481e8df8462ca24795869c6e87591c45ec7a640f38c351a450810c05a74d5512aeeb6fab08e47e286020994a2c65e75544964da95f3af0e908004414b28920719e8239218913cc366430aeeb6ab1d6d86687165275d349566580db85100a420c12ca2481c68637a291f3d0391326b70aafb2b6dc69d6285525935275dc96142b0010c5102a4b28920719f9228e078c38f99136abb0b2dbd869ba1d6545539d65d262588cb44001085a432ca2481c68df8217a435198e40faecbf0baa65da1a71b4d65d29d551b95e3ec085103a4100b2892071a286481f8e631140d3aebebab0b6861d7196925d45954e77658d1a810e91001422ca2481c691e85f8a042634f38cbedb2eaf072865b69845098f38d32e8a96485154935a75de9218237c510308101d61ca1a6cb2461e52b0bedb2ba9030e9913cdb5ea581d35945e74957e38248a11440c204069c75ba1924a20b1a5b30aeeaaf3e63103513af82968a5945674d74a47e27a18c5103081019a1b71874620994b1ebb70aacb8e44f366310b23a5b1925e75155938a07e191e1440c204071961a7681cb948289beabb0b6b34f41130e9aa8697495525d65139e07a389f90510308101b6a861972518b28722dbafaf0b0c35139098fadfa5c2d79d35525168629237a01440c2040a1d6996d82a51c9206bacaadbf0

/-- Row-major table, 6 bits per entry. The final remainder makes the operation
well-typed independently of the data; the original table is saved in JSON. -/
@[implicit_reducible] def magma49 : Magma (Fin 49) :=
  ⟨fun x y => ⟨((table49 >>> (6 * (49 * x.val + y.val))) % 64) % 49,
    Nat.mod_lt _ (by decide)⟩⟩

theorem equation677_49 : @Equation677 (Fin 49) magma49 := by decide +kernel

theorem equation255_49 : @Equation255 (Fin 49) magma49 := by decide +kernel

theorem leftQuasigroup49 : IsSideQuasigroup .left magma49 :=
  fun x => ⟨@Eq677.eq677_leftMul_inj _ magma49 _ equation677_49 x,
    @Eq677.eq677_leftMul_surj _ magma49 equation677_49 x⟩

/-- Distinct elements 18 and 19 have the same product with 0 on the right. -/
theorem right_collision49 : magma49.op 18 0 = magma49.op 19 0 := by decide +kernel

theorem not_rightQuasigroup49 : ¬ IsSideQuasigroup .right magma49 := by
  intro h
  exact (by decide : (18 : Fin 49) ≠ 19) ((h 0).1 right_collision49)

theorem not_quasigroup49 : ¬ IsQuasigroup magma49 := fun h => not_rightQuasigroup49 h.2

theorem idempotent25 : ∀ x, magma25.op x x = x := by decide +kernel

theorem not_idempotent49 : ¬ (∀ x, magma49.op x x = x) := by
  intro h
  exact (by decide +kernel : magma49.op 0 0 ≠ 0) (h 0)

/-- info: 'Parastrophes.Eq677Finite.equation677_25' does not depend on any axioms -/
#guard_msgs in
#print axioms equation677_25

/-- info: 'Parastrophes.Eq677Finite.equation255_25' does not depend on any axioms -/
#guard_msgs in
#print axioms equation255_25

/-- info: 'Parastrophes.Eq677Finite.equation677_49' does not depend on any axioms -/
#guard_msgs in
#print axioms equation677_49

/-- info: 'Parastrophes.Eq677Finite.equation255_49' does not depend on any axioms -/
#guard_msgs in
#print axioms equation255_49

end Parastrophes.Eq677Finite

namespace Parastrophes.Catalogue

/-- ICARM's order-25 model refutes right bijectivity for finite E677 magmas. -/
@[parastrophe_result] theorem not_rightQuasigroup677_fin :
    ¬ SideQuasigroupLaw .fin Law677 .right := by
  intro h
  exact Eq677Finite.not_rightQuasigroup25
    (h (Fin 25) Eq677Finite.magma25 (inferInstance : Finite (Fin 25))
      ((@Law677.models_iff _ Eq677Finite.magma25).mpr Eq677Finite.equation677_25))

@[parastrophe_result] theorem not_quasigroup677_fin : ¬ QuasigroupLaw .fin Law677 :=
  fun h => not_rightQuasigroup677_fin (quasigroup_side h .right)

end Parastrophes.Catalogue

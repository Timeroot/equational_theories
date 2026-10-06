import equational_theories.Spectrum.SmallPairs.OrderThirteen.Encoding
import equational_theories.Definability.IncludeGzip
import equational_theories.Spectrum.Status

/-! Generated saved LRAT proofs. Hashes and solver timings are in
 data/spectrum/1279_order13_refutations.json. -/
namespace Spectrum.SmallPairs.OrderThirteen
open Std.Sat Std.Tactic.BVDecide LRAT

private def proofTexts : Array String := #[
  -- Expanded LRAT SHA-256: 0c62af7b61f80f26b41d15a4970e301eae15bbd4754339b8f981ab7f93800185
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row000.lrat.gz",
  -- Expanded LRAT SHA-256: d20269ef126310bfc5b97c516acf86a50d44abcae2dd124492f144dcc571fa9b
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row001.lrat.gz",
  -- Expanded LRAT SHA-256: 80b4ca279df2d927fded17ef570fce82ab78faba281ce08379130f9ad44e8c07
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row002.lrat.gz",
  -- Expanded LRAT SHA-256: f7febd347d14e7d43a57ebbf19cf106a60312a1d67ea0e9eedeb0c435064a15b
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row003.lrat.gz",
  -- Expanded LRAT SHA-256: 4d193acd9cdbef467359f91b63bed6629a7792f536e5a9e650921619db619d66
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row004.lrat.gz",
  -- Expanded LRAT SHA-256: 2c2309d676ae42064153fb046b903a359667825baf3b6e28078472bbc318a10b
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row005.lrat.gz",
  -- Expanded LRAT SHA-256: 7ffaad776f2b0aa91be2d38ef73b45bb60dd65fa8986911959f2bffcc30e7809
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row006.lrat.gz",
  -- Expanded LRAT SHA-256: 4b970f55d173aea79461b62003eb9df5cea348836766f804a1d828f7560d1352
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row007.lrat.gz",
  -- Expanded LRAT SHA-256: d48f0718d52b8c47014c77f139ac8599d6d850410fda1c00226e243365d62921
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row008.lrat.gz",
  -- Expanded LRAT SHA-256: 80a0b5b26b2f1e938abc34226d0c8da46e55afb4118400c8ed3009a4f467ec7d
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row009.lrat.gz",
  -- Expanded LRAT SHA-256: a36b865eefb0afd2912c859bd8b8e7fc9ddae42b5d8f107fbe3d69cb6c9ac8f3
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row010.lrat.gz",
  -- Expanded LRAT SHA-256: 962db53b7cfbf8509949577271c0a5bedd84d6b1e5ba723813b0dab5fde82c62
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row011.lrat.gz",
  -- Expanded LRAT SHA-256: a04cfb4e3318e9bc9420c4c8f19f4016575694a8fb59e50414bdb36105375cc1
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row012.lrat.gz",
  -- Expanded LRAT SHA-256: e25ac8cd14cdc2da7e1ee39742a5eaf89ddd06663a093ca3914544402151e269
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row013.lrat.gz",
  -- Expanded LRAT SHA-256: b5278cabad218bfc35add8cf634f11d1af18b042cd4e22c1da4d7d99d5a8fc28
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row014.lrat.gz",
  -- Expanded LRAT SHA-256: 4d193acd9cdbef467359f91b63bed6629a7792f536e5a9e650921619db619d66
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row015.lrat.gz",
  -- Expanded LRAT SHA-256: cb710040c24a81fd1f7171d5f5f681aac9e15fd05b3e69fd3a0c0e46d67cf772
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row016.lrat.gz",
  -- Expanded LRAT SHA-256: cb710040c24a81fd1f7171d5f5f681aac9e15fd05b3e69fd3a0c0e46d67cf772
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row017.lrat.gz",
  -- Expanded LRAT SHA-256: 7e02bfc0f0c95d58cf6e9db5c0315ad51154d49835356ac71d3dfdfd64470119
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row018.lrat.gz",
  -- Expanded LRAT SHA-256: 496094c56ae3f8336c94bcc98916be3741107d9f202c8813d54b7fb9e3957a5a
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row019.lrat.gz",
  -- Expanded LRAT SHA-256: a36b865eefb0afd2912c859bd8b8e7fc9ddae42b5d8f107fbe3d69cb6c9ac8f3
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row020.lrat.gz",
  -- Expanded LRAT SHA-256: c886d5b267ad30021c91e5f0638060c78478d13e7885d5d86e7364133dd72be8
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row021.lrat.gz",
  -- Expanded LRAT SHA-256: 21d893c63a6a149c89717f9f008410b4e5a2ebb341318db4b6fb942a7f6b0b9a
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row022.lrat.gz",
  -- Expanded LRAT SHA-256: 8d6b4f66812b012425664bbde1792606021d70acf7205e2c30203b87183d1a15
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row023.lrat.gz",
  -- Expanded LRAT SHA-256: cb66cc95f1f68f1d8b1d36e2ef9bc2e012f90ec20bee449cbea8a1cd1a8e6ca3
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row024.lrat.gz",
  -- Expanded LRAT SHA-256: ab69e52810f790cbb552c5e4629070a9a75313fee347c3563853a07155555beb
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row025.lrat.gz",
  -- Expanded LRAT SHA-256: 0e37701b1b16085c465ce4e289405616b224ee893bef058774610c2288e15774
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row026.lrat.gz",
  -- Expanded LRAT SHA-256: 99ac9404e13e183bf4ff4386cdfb4b880e2a7a524a7edaee07b372d35a849188
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row027.lrat.gz",
  -- Expanded LRAT SHA-256: 0df82e948167f6796127487caad1602e84edb567a1ca1b84ff89ca9756a5a253
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row028.lrat.gz",
  -- Expanded LRAT SHA-256: f2506f0c60a785406d38679b58cea2660a1d5deb286db0c5dbbbfb9ad784957d
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row029.lrat.gz",
  -- Expanded LRAT SHA-256: d39829bf9928d18b6317e844d40e7389c2a4d06a484f4a4d18ea3948dc9114bd
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row030.lrat.gz",
  -- Expanded LRAT SHA-256: 81cd78843ad1c836805b98e45f52866375cc52e0b182af8c47fdd5e8ec241427
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row031.lrat.gz",
  -- Expanded LRAT SHA-256: a04cfb4e3318e9bc9420c4c8f19f4016575694a8fb59e50414bdb36105375cc1
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row032.lrat.gz",
  -- Expanded LRAT SHA-256: 99ac9404e13e183bf4ff4386cdfb4b880e2a7a524a7edaee07b372d35a849188
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row033.lrat.gz",
  -- Expanded LRAT SHA-256: 6e967bb2adcb7aaba044e7194dea8dd43411da36244bf0cb6eb5bb6613d81113
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row034.lrat.gz",
  -- Expanded LRAT SHA-256: 0df82e948167f6796127487caad1602e84edb567a1ca1b84ff89ca9756a5a253
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row035.lrat.gz",
  -- Expanded LRAT SHA-256: adc70901083032456eaeb9fe41aa4c3607aa878ebcd95d7dacc4326a21f3a9dd
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row036.lrat.gz",
  -- Expanded LRAT SHA-256: 8d6b4f66812b012425664bbde1792606021d70acf7205e2c30203b87183d1a15
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row037.lrat.gz",
  -- Expanded LRAT SHA-256: e81ba28193ce0923d4ea06654b1b7e7cf19aec4b2dfaa83526a46e4d0f28ec9e
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row038.lrat.gz",
  -- Expanded LRAT SHA-256: 6e967bb2adcb7aaba044e7194dea8dd43411da36244bf0cb6eb5bb6613d81113
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row039.lrat.gz",
  -- Expanded LRAT SHA-256: cb66cc95f1f68f1d8b1d36e2ef9bc2e012f90ec20bee449cbea8a1cd1a8e6ca3
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row040.lrat.gz",
  -- Expanded LRAT SHA-256: 1781221d420dbe81931a619493ed4bc1981ec10b57e9ccb81949a9d3797b11b0
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row041.lrat.gz",
  -- Expanded LRAT SHA-256: 5abc91f10c807825ae0d93cd6666ba023dafcb7d0a5aa32cf1e87a2d560f41cc
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row042.lrat.gz",
  -- Expanded LRAT SHA-256: 962db53b7cfbf8509949577271c0a5bedd84d6b1e5ba723813b0dab5fde82c62
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row043.lrat.gz",
  -- Expanded LRAT SHA-256: a04cfb4e3318e9bc9420c4c8f19f4016575694a8fb59e50414bdb36105375cc1
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row044.lrat.gz",
  -- Expanded LRAT SHA-256: cb66cc95f1f68f1d8b1d36e2ef9bc2e012f90ec20bee449cbea8a1cd1a8e6ca3
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row045.lrat.gz",
  -- Expanded LRAT SHA-256: 0e37701b1b16085c465ce4e289405616b224ee893bef058774610c2288e15774
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row046.lrat.gz",
  -- Expanded LRAT SHA-256: 99ac9404e13e183bf4ff4386cdfb4b880e2a7a524a7edaee07b372d35a849188
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row047.lrat.gz",
  -- Expanded LRAT SHA-256: 0df82e948167f6796127487caad1602e84edb567a1ca1b84ff89ca9756a5a253
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row048.lrat.gz",
  -- Expanded LRAT SHA-256: f2506f0c60a785406d38679b58cea2660a1d5deb286db0c5dbbbfb9ad784957d
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row049.lrat.gz",
  -- Expanded LRAT SHA-256: 81cd78843ad1c836805b98e45f52866375cc52e0b182af8c47fdd5e8ec241427
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row050.lrat.gz",
  -- Expanded LRAT SHA-256: 81cd78843ad1c836805b98e45f52866375cc52e0b182af8c47fdd5e8ec241427
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row051.lrat.gz",
  -- Expanded LRAT SHA-256: e81ba28193ce0923d4ea06654b1b7e7cf19aec4b2dfaa83526a46e4d0f28ec9e
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row052.lrat.gz",
  -- Expanded LRAT SHA-256: 72b07006df1d54198c90389f2daaa0dd9bfbfa0ec2a4b33c25c631d7613f5335
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row053.lrat.gz",
  -- Expanded LRAT SHA-256: cb66cc95f1f68f1d8b1d36e2ef9bc2e012f90ec20bee449cbea8a1cd1a8e6ca3
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row054.lrat.gz",
  -- Expanded LRAT SHA-256: 8d98bc394fd3ae931023f2fbc0cde0c78c375c5be51fa3ed310abf2e63f7e875
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row055.lrat.gz",
  -- Expanded LRAT SHA-256: 26f611cb9bb07a818d33ec033f247fc822c884c76f5381d0cc5b3430ad211cf6
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row056.lrat.gz",
  -- Expanded LRAT SHA-256: 5d21dc8ea7b097855489f64a132746e98c5e86c0d197eb480d778a946e5096b8
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row057.lrat.gz",
  -- Expanded LRAT SHA-256: 5031170e2487c2325c6bc74f4a74254f9c6bb886191a6d710c73ab5f22e3d91c
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row058.lrat.gz",
  -- Expanded LRAT SHA-256: 718ad1cff3f8d0be902f2f1c85f485512f293aaff755a0daf12fef9cd233c6c2
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row059.lrat.gz",
  -- Expanded LRAT SHA-256: d0c6cd615ee308910a06342bde25f8d2761bb8ae377f5b990b7a509b0b972a85
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row060.lrat.gz",
  -- Expanded LRAT SHA-256: 84b94339d25feb42c0e441dd3fc9de852d552df07ea3a5f71be90e41c70617c3
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row061.lrat.gz",
  -- Expanded LRAT SHA-256: 8617d4660dcfae7119beda5d52906f62889307e276389fc16a2ca0adbbd0220f
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row062.lrat.gz",
  -- Expanded LRAT SHA-256: c5ce5f237c4b85aa422f469611799b1d0c70f59d1b2261f3c9086f6ae559654b
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row063.lrat.gz",
  -- Expanded LRAT SHA-256: da10019b391a8a91424b24f36d3b838bccca3d0ddacb0a26de233ba980625963
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row064.lrat.gz",
  -- Expanded LRAT SHA-256: b1bf4a4a5f72e6147db91064645ed9bd99d33d9cd5b9b3b1b3be61add9dc1bf3
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row065.lrat.gz",
  -- Expanded LRAT SHA-256: c6bcb8b383214a8c3053d081d9761a298a1dc16350b3d2368e8cc39f3f34fca3
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row066.lrat.gz",
  -- Expanded LRAT SHA-256: 09483327cfb5cd2f1120596bbcd33a3294baa9255363a7f4648b49be096badcb
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row067.lrat.gz",
  -- Expanded LRAT SHA-256: 9dfc7adafc11e011a5747225add77f258fe7c54b46b11b877918ffb9bdc03672
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row068.lrat.gz",
  -- Expanded LRAT SHA-256: 8ce24ca09ba8291c1330b30aaa32f663cb2cc76c9243ba748f30f0ee307da058
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row069.lrat.gz",
  -- Expanded LRAT SHA-256: 8bae8648f875f7c8f042da98edca6f5bb2c4fca7c7b7105a89adb2739e909bdf
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row070.lrat.gz",
  -- Expanded LRAT SHA-256: a87d799ebc2576bd876e2d1da4f3e0dafc8aa32419662cba4684d1e5572202a8
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row071.lrat.gz",
  -- Expanded LRAT SHA-256: 148e09320606eac0a2bf29c153221bd5d23c130c00d8b2dbcdf9f31a942da8a6
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row072.lrat.gz",
  -- Expanded LRAT SHA-256: 1838b3d18a6fa0bf1ddce9771229d17fcc8514c11ae050552350d94a829900aa
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row073.lrat.gz",
  -- Expanded LRAT SHA-256: 1ec39c0f9c2db6a781f2556feac9e26ada902bac0900de99a440b15d6fa38435
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row074.lrat.gz",
  -- Expanded LRAT SHA-256: 4d9a03dd0205ebf3fd456f694adee5a165b162c55e6111b886f91d95275cf8ff
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row075.lrat.gz",
  -- Expanded LRAT SHA-256: 5ce4e0cddb99c5a8c99d24c34a08643e87cfd1bba3ae01a4a651a7e33dff2ee7
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row076.lrat.gz",
  -- Expanded LRAT SHA-256: 488d8f18c64c5a6362204a0b8093548d8ef0348ce047bf3c953ba7704e9e2f8a
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row077.lrat.gz",
  -- Expanded LRAT SHA-256: 473bcfcdabe7ec7d54ea9370285cd357a31a5fd3c207909dbae4ab57c341fe23
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row078.lrat.gz",
  -- Expanded LRAT SHA-256: b73179d58d29f4729e64bb736cfa25ef92487260ff79d872c2a98eea0cf871aa
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row079.lrat.gz",
  -- Expanded LRAT SHA-256: 69aa1c3c796c4788cf793e5641bd2ddce6f6a647f7be5197714a0905841fdce4
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row080.lrat.gz",
  -- Expanded LRAT SHA-256: 7d5593cd5423b969f4a0b3a5393f7edb38424d0aea114747b755b7c1ea2b24b4
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row081.lrat.gz",
  -- Expanded LRAT SHA-256: a5bcf78e6b9aa09d99d74383149cc40eeb0ea64ea250a384903550ca39a76170
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row082.lrat.gz",
  -- Expanded LRAT SHA-256: 9e188027009c6b10e8019b20138900dd9c4145f52b50fbb33ae53bb7f0da340d
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row083.lrat.gz",
  -- Expanded LRAT SHA-256: ff838227697eba7f10c7a37e15a72bab7ff1611e1b5e07ed5a73d679005410f8
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row084.lrat.gz",
  -- Expanded LRAT SHA-256: b7989f1c3572a60dc69d16614969f910fd34c125790c4fbe084e2dcf58d850c0
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row085.lrat.gz",
  -- Expanded LRAT SHA-256: 9bede3e188e0f976559daea90a2c97f72333c58f7578d9716b5d88f154516844
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row086.lrat.gz",
  -- Expanded LRAT SHA-256: 215dd29798a59d6f1a95bde652aabe293e2d184e5960f6203ac75cb801430a4f
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row087.lrat.gz",
  -- Expanded LRAT SHA-256: ff762e95fbdde5edbe77460a54294d978d77f354bb114f6a24fc8780561126bb
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row088.lrat.gz",
  -- Expanded LRAT SHA-256: 39d787541f304aa75762726bcc5c45a1e9bd7a049a1fee25d0c7740104089527
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row089.lrat.gz",
  -- Expanded LRAT SHA-256: cf968e7204cc0b65e776b4a97aeead90884dbe19c8f2a88d8e25280a75ae51f4
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row090.lrat.gz",
  -- Expanded LRAT SHA-256: b2c6583576b5eddb8ad670929efda295b846e5eea84c16f1e4c5de574e5aaeef
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row091.lrat.gz",
  -- Expanded LRAT SHA-256: 7d5593cd5423b969f4a0b3a5393f7edb38424d0aea114747b755b7c1ea2b24b4
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row092.lrat.gz",
  -- Expanded LRAT SHA-256: 8782539a092debeb6ae230713e76f652d2cc4457ea1f4b8f4aedcd208c291872
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row093.lrat.gz",
  -- Expanded LRAT SHA-256: 8782539a092debeb6ae230713e76f652d2cc4457ea1f4b8f4aedcd208c291872
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row094.lrat.gz",
  -- Expanded LRAT SHA-256: 994c5beba268e04e0cd0f1241c17c1843689c1868b7a6cd883052e370e8278c2
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row095.lrat.gz",
  -- Expanded LRAT SHA-256: 0d1f1afb88f575708654ed24c9fbf4edfe03f4ae085ee86e42a3b49113f10991
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row096.lrat.gz",
  -- Expanded LRAT SHA-256: 215dd29798a59d6f1a95bde652aabe293e2d184e5960f6203ac75cb801430a4f
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row097.lrat.gz",
  -- Expanded LRAT SHA-256: 46933a1283865ad503b4a8df8a642194c9ae9e899628b7552bd78ac4bb7f30a5
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row098.lrat.gz",
  -- Expanded LRAT SHA-256: ea567f77edb3e07fa85d1ad1bb56feffe8382a6a1b2c70453099453e23dc9ce5
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row099.lrat.gz",
  -- Expanded LRAT SHA-256: 369c536c15dfcf7d996c091ed85894c4efba3cb0041ed8c44610e4bd91eff054
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row100.lrat.gz",
  -- Expanded LRAT SHA-256: 2fa2256606ee42ff25f627ab3232b3eef972e00dff03ceb0f3f30862a694db99
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row101.lrat.gz",
  -- Expanded LRAT SHA-256: 562c8c27e8b673f87a6b677103eb35a8af43f977781929877a82146d53ceceeb
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row102.lrat.gz",
  -- Expanded LRAT SHA-256: 10a2e9210228cdb93d14fc466770d55f615f0e1f3f42385459c016c6e61e22f9
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row103.lrat.gz",
  -- Expanded LRAT SHA-256: d04bc3b80dc42f2441f7ae387a4713f86efbac6c4cc265574a4c3c4480ae2d34
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row104.lrat.gz",
  -- Expanded LRAT SHA-256: e91cec2a05ba1be28310925357b5cee3cb2f3c680047568a198a395e5b3cddb1
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row105.lrat.gz",
  -- Expanded LRAT SHA-256: 65a006e5f0933fb26514336b474ba3fd87473b7f73d64a2bec3de1883f2074e8
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row106.lrat.gz",
  -- Expanded LRAT SHA-256: 1b5b2c3652d721a6532b0a16dfa8a7d7e80c825bda8bef8833b958dc96b9b912
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row107.lrat.gz",
  -- Expanded LRAT SHA-256: 39d8522394a88ed8afe32d9fadadc396512de3ed397637db6522a64235d6f22b
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row108.lrat.gz",
  -- Expanded LRAT SHA-256: 39d787541f304aa75762726bcc5c45a1e9bd7a049a1fee25d0c7740104089527
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row109.lrat.gz",
  -- Expanded LRAT SHA-256: d04bc3b80dc42f2441f7ae387a4713f86efbac6c4cc265574a4c3c4480ae2d34
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row110.lrat.gz",
  -- Expanded LRAT SHA-256: 8b2859649104da9afb0338cbce45dffdd210979154707ed6387134bbac5c8b94
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row111.lrat.gz",
  -- Expanded LRAT SHA-256: e91cec2a05ba1be28310925357b5cee3cb2f3c680047568a198a395e5b3cddb1
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row112.lrat.gz",
  -- Expanded LRAT SHA-256: 2dab7f4ebfe1690a558dfdd3fdaeda7c11e0fd31d654a54309751aabfe917b4d
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row113.lrat.gz",
  -- Expanded LRAT SHA-256: 369c536c15dfcf7d996c091ed85894c4efba3cb0041ed8c44610e4bd91eff054
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row114.lrat.gz",
  -- Expanded LRAT SHA-256: 0a563716cf9c81ad9932cd29488af931d447ac77c2cc9a1ede535e089d426f86
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row115.lrat.gz",
  -- Expanded LRAT SHA-256: 8b2859649104da9afb0338cbce45dffdd210979154707ed6387134bbac5c8b94
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row116.lrat.gz",
  -- Expanded LRAT SHA-256: 2fa2256606ee42ff25f627ab3232b3eef972e00dff03ceb0f3f30862a694db99
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row117.lrat.gz",
  -- Expanded LRAT SHA-256: 69d0f7d87058a8d17362e125ff96cbec53ea36b86f3c7ed51ef67444b65058a2
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row118.lrat.gz",
  -- Expanded LRAT SHA-256: c9c8a28be2a20523ddfb2bdb937237e7c13b81c06ee67a20d5d8555ceef03f9b
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row119.lrat.gz",
  -- Expanded LRAT SHA-256: ff762e95fbdde5edbe77460a54294d978d77f354bb114f6a24fc8780561126bb
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row120.lrat.gz",
  -- Expanded LRAT SHA-256: 39d787541f304aa75762726bcc5c45a1e9bd7a049a1fee25d0c7740104089527
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row121.lrat.gz",
  -- Expanded LRAT SHA-256: 2fa2256606ee42ff25f627ab3232b3eef972e00dff03ceb0f3f30862a694db99
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row122.lrat.gz",
  -- Expanded LRAT SHA-256: 10a2e9210228cdb93d14fc466770d55f615f0e1f3f42385459c016c6e61e22f9
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row123.lrat.gz",
  -- Expanded LRAT SHA-256: d04bc3b80dc42f2441f7ae387a4713f86efbac6c4cc265574a4c3c4480ae2d34
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row124.lrat.gz",
  -- Expanded LRAT SHA-256: e91cec2a05ba1be28310925357b5cee3cb2f3c680047568a198a395e5b3cddb1
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row125.lrat.gz",
  -- Expanded LRAT SHA-256: 65a006e5f0933fb26514336b474ba3fd87473b7f73d64a2bec3de1883f2074e8
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row126.lrat.gz",
  -- Expanded LRAT SHA-256: 39d8522394a88ed8afe32d9fadadc396512de3ed397637db6522a64235d6f22b
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row127.lrat.gz",
  -- Expanded LRAT SHA-256: 39d8522394a88ed8afe32d9fadadc396512de3ed397637db6522a64235d6f22b
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row128.lrat.gz",
  -- Expanded LRAT SHA-256: 0a563716cf9c81ad9932cd29488af931d447ac77c2cc9a1ede535e089d426f86
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row129.lrat.gz",
  -- Expanded LRAT SHA-256: 1c0cc9be3be7d8a63a0d2d03dec0bc62214c4578fbfd59cbc87be0801a68594b
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row130.lrat.gz",
  -- Expanded LRAT SHA-256: 2fa2256606ee42ff25f627ab3232b3eef972e00dff03ceb0f3f30862a694db99
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row131.lrat.gz",
  -- Expanded LRAT SHA-256: 742756367f9d5cd1e63585e4099804e66be1249792da95df447033e9134852ff
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row132.lrat.gz",
  -- Expanded LRAT SHA-256: c8d66d37e24ba39d51a9677b9ba67ba63959be4107bc699ec2ee1db80b8af555
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row133.lrat.gz",
  -- Expanded LRAT SHA-256: 38489a87c51499aacb497bd4d3411b52146c0db89e90f0ce08a9c26e3dad9321
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row134.lrat.gz",
  -- Expanded LRAT SHA-256: ccc6a09f441c7aabb799831c8ac8d921b254642c631683f13fb2175be942e3d7
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row135.lrat.gz",
  -- Expanded LRAT SHA-256: 9916cad8e2236a448510be0ba0aba98e3f2879ea96192e1424e358c5e70ae112
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row136.lrat.gz",
  -- Expanded LRAT SHA-256: e3398ad2f45b9bd454c7930d107f953f0c6866f84d843d1d8ce8f2ad38d2413c
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row137.lrat.gz",
  -- Expanded LRAT SHA-256: a1cbea61f539d068c6a836881f07c84ede3cf45883ea9812bb0339df35fda235
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row138.lrat.gz",
  -- Expanded LRAT SHA-256: 87391f4a27853ff09d09a80c180111795f992d071f51c3a6e5687e13b12f8f83
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row139.lrat.gz",
  -- Expanded LRAT SHA-256: 274390a994b6d530e790b266a50a1b7bb22c4ffb4e6282cbe4c7161e7e9ab412
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row140.lrat.gz",
  -- Expanded LRAT SHA-256: e46ef65f37573b6a6e6e24a50f316ff8f7d3aa5d7ea92d12e258611cd7aab07e
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row141.lrat.gz",
  -- Expanded LRAT SHA-256: 719b3adb6c6db862665ad01d2c2b8e6d591df3c8e44b7051f0c6788477edb0f8
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row142.lrat.gz",
  -- Expanded LRAT SHA-256: 6b11b7cf921bfc32dc4754f1706f4f9055182635c05d76ffe1353a6072e1d5cf
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row143.lrat.gz",
  -- Expanded LRAT SHA-256: 651b39b3b8520faa0bb43897f855927903b59c5efd256cd166b70b551bd1c696
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row144.lrat.gz",
  -- Expanded LRAT SHA-256: b38eafd2ed2fc18fddfe79516174cdc24b2d7787077b0fe9ddea53688f588d7a
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row145.lrat.gz",
  -- Expanded LRAT SHA-256: 42bff0ab62340b6d478bcfae48500b7dce972393e6ab0da19eb152e8a7d669d1
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row146.lrat.gz",
  -- Expanded LRAT SHA-256: 31a09f3719eb6cd91d096cd3685900e3153731709b76b7621d25ce0270ab9f9f
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row147.lrat.gz",
  -- Expanded LRAT SHA-256: b5624b3c9903c393f661befd8db1b473d75bcd583e69bed87a6a85a7f5f9644e
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row148.lrat.gz",
  -- Expanded LRAT SHA-256: e930315e49f1d73178e11d13a655eb760eeca0d09225c942c7dc5e4eac5447c8
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row149.lrat.gz",
  -- Expanded LRAT SHA-256: 02b4cfe770924c9840e29dd28546097a476bb832e02a0acf5bf1634f93211f21
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row150.lrat.gz",
  -- Expanded LRAT SHA-256: 5948dcd89865e438ece297eb30e44812971eebc0b9fd98d2f7a6031467566a1d
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row151.lrat.gz",
  -- Expanded LRAT SHA-256: ad1f60a6ff6e4aa7ed7e9def728ef6aaa495c4993af4fcdadd1b29d7a5dd4b0e
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row152.lrat.gz",
  -- Expanded LRAT SHA-256: 2b547129883ffdb55c95fb9df3a8651f72031665a7f26fc0a1eae9bae788f51e
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row153.lrat.gz",
  -- Expanded LRAT SHA-256: 9384dde0f5253c0cb1beeef0d83048091a2fc6005ebcc337230260e9f8981892
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row154.lrat.gz",
  -- Expanded LRAT SHA-256: 5f5bd072df1cd12685c97a6016698e6987fda10d9cce490712ebd9d64c68ad4b
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row155.lrat.gz",
  -- Expanded LRAT SHA-256: 284e7f9283668ea88e681daa7450558ff8609610c40959cd529e21814b8f7fa2
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row156.lrat.gz",
  -- Expanded LRAT SHA-256: b29c38242450f0bfb39cec0acf0f34d193ef7e28c10e46ac77838acc558cd809
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row157.lrat.gz",
  -- Expanded LRAT SHA-256: c77ea29b5093e2748864e9a5c49ef58285e4964fa6bfe9a717316b8d326a44e2
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row158.lrat.gz",
  -- Expanded LRAT SHA-256: e3adb138529a670f9feb230d68720656ec984853ea55ea300167a5f02b69c80b
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row159.lrat.gz",
  -- Expanded LRAT SHA-256: d17a117688437d19e18d20fff6d122ecc3e7d7b81078f1475279d923790e7ad4
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row160.lrat.gz",
  -- Expanded LRAT SHA-256: b8c4c58aeedf9bab8f722960c712265406d6c5b1d3b0fa24f303c542df47e778
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row161.lrat.gz",
  -- Expanded LRAT SHA-256: 481571e3af1e497ee54e742a18a462bfcca0ae2df18ec58391bcd16e9d4cd2e2
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row162.lrat.gz",
  -- Expanded LRAT SHA-256: 8afad4a213493939bcb06d3e8cd5ee21e65d732a73d8010caf660a50080da014
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row163.lrat.gz",
  -- Expanded LRAT SHA-256: 359b594b40b4423ffc70b3a0d1f683d32872285abb035dc4827a43aaf15e4eaa
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row164.lrat.gz",
  -- Expanded LRAT SHA-256: b02137529c7816fb7f3aba015e24409d312fac8c7ac077feef9d10b08b3ad221
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row165.lrat.gz",
  -- Expanded LRAT SHA-256: 023ac05c4ed901021c29a8e60edb9aaf1e362e28fc812feb473176f33eee877e
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row166.lrat.gz",
  -- Expanded LRAT SHA-256: c7dd3f504b31fceea79dd0e7366ee694a51bfb908ea122fd5b030c5abc88d7bc
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row167.lrat.gz",
  -- Expanded LRAT SHA-256: 283077e70a0fac14d8202579d9d9f143d685351f649b41e892ba7af7d8354395
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row168.lrat.gz",
  -- Expanded LRAT SHA-256: a49b08086f2f02ababd2146f3fc3a57a1d1a6b18e277385bc58bea1aeb1e5720
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row169.lrat.gz",
  -- Expanded LRAT SHA-256: e950e61e50109bf551cf646b34de430919ac61217f27db2a5722ce8c2a2cdec3
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row170.lrat.gz",
  -- Expanded LRAT SHA-256: 0b292d4c1778e4f48dd4f6842a6d68638238e478faafda6abe3f9ef50241fc65
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row171.lrat.gz",
  -- Expanded LRAT SHA-256: eec2cdfec506bcc84019a103cb4359681c4849d1cccf55649545bbb137fabdb9
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row172.lrat.gz",
  -- Expanded LRAT SHA-256: e44a656fcc127fa4b7ebad33ed85fe26f73aec1f9bdd9c7759f1d8991f933125
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row173.lrat.gz",
  -- Expanded LRAT SHA-256: 49f047a70096012a3609971667ccd0f2101a05cd5b4f6c2d2f8119e17af29200
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row174.lrat.gz",
  -- Expanded LRAT SHA-256: 8f4b951ba58d3d6cc1c95cbe0d99354007c57a397729ea8508dea19f9ea89fa4
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row175.lrat.gz",
  -- Expanded LRAT SHA-256: 0c2593cda02de7d2b2d2aba2f766dab8e860b68f43f6d695f70bcc60a2b3cbdb
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row176.lrat.gz",
  -- Expanded LRAT SHA-256: 0cc7d5228ab3c2637de0adca24f1e3c805fdd8d1d4b5493aeefa2153b9799b5f
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row177.lrat.gz",
  -- Expanded LRAT SHA-256: e15c61a9d1e050ddfb85fad939e147ed2c6da36a3f7c0607ad17d3bc870e0238
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row178.lrat.gz",
  -- Expanded LRAT SHA-256: b62f9404cde2dcfd989863fe3f378eb17d2fe7ed2e0db537a51d86ec2ca10a13
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row179.lrat.gz",
  -- Expanded LRAT SHA-256: 4a6b1e172c01918cca40f5c1d0b1fdb964f024a3d537b48f8d278c277ff2a285
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row180.lrat.gz",
  -- Expanded LRAT SHA-256: 2b730a51f821b19e96f77f88c52a6f39cacdce2fd3a9df2c97c4470c552459dd
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row181.lrat.gz",
  -- Expanded LRAT SHA-256: cb092c846a7b457cc7a11b91f49456fbe0c42770ed6f51caeb791bb85551848f
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row182.lrat.gz",
  -- Expanded LRAT SHA-256: 38a8b5c0e67e9c51ab14cc0e3829357ab8fd6fab77fceb02788ac4fc54195e38
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row183.lrat.gz",
  -- Expanded LRAT SHA-256: 55508a19dc0033317bcf74dc084f057eba08546f7726cec0840c4a7a371a1108
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row184.lrat.gz",
  -- Expanded LRAT SHA-256: 84c96bdc32b95157cf522fd2c6a9cf3f89c8de85cccb786fa3b04ed2419b1e90
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row185.lrat.gz",
  -- Expanded LRAT SHA-256: b401a8f6a52be93e02d02e9a52ee4dee4660d69cb809cabe1167ffc3515f75b6
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row186.lrat.gz",
  -- Expanded LRAT SHA-256: 7fa68bf234400e5d8bba33980b920da5c50946f8b4b91e5eb5a606963a58291f
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row187.lrat.gz",
  -- Expanded LRAT SHA-256: 6ec4272b8d8c3a87c5824b8062fa6ffe10de1f91b6b37e30b3c23e49bcf1ca96
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row188.lrat.gz",
  -- Expanded LRAT SHA-256: 4850e3e04fab8dd55422f4950b76994f8b1331ce998bb0cc58f2595a118f7d94
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row189.lrat.gz",
  -- Expanded LRAT SHA-256: e83eaf81170109e1a96462afff988504b62a02e693b2573c2ad9a42dc14c39f6
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row190.lrat.gz",
  -- Expanded LRAT SHA-256: 06d2b80340ef1f2606146f71fb4aea60a8d538adfb3aca52423240752a0670d4
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row191.lrat.gz",
  -- Expanded LRAT SHA-256: 6abc0ff70d820e3e41dc35f32cffe981003d66e049f2bc6df4d6162c962febea
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row192.lrat.gz",
  -- Expanded LRAT SHA-256: e2be1efeed08521e324e859647093879acd09dbac95e8683332c7eb8c8df7763
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row193.lrat.gz",
  -- Expanded LRAT SHA-256: 3aba58be1c64a0a1e084409a5a30f55a7d5689b1c27d7d155145e5c11f7f76f5
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row194.lrat.gz",
  -- Expanded LRAT SHA-256: 18d8a470865b6a26f34bcfa02e8141208989703bbfd7fe9895a3d13e4974fb2c
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row195.lrat.gz",
  -- Expanded LRAT SHA-256: 6b8b38dc03c1e0e825f79c744edcf1fc2bb6653250d566df986854b1a7fbfa1d
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row196.lrat.gz",
  -- Expanded LRAT SHA-256: 27e20706d2ab903b2b04d9a9cf18cb383df42242bb33e2afb6a785296d246798
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row197.lrat.gz",
  -- Expanded LRAT SHA-256: 5186a04056026472aa64467e04e5aee1579887d34417647ba8cc09e72db247ff
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row198.lrat.gz",
  -- Expanded LRAT SHA-256: 812c7c0f1b2ab3e9438b158659526ccfda098ea4962a502992f922546e492279
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row199.lrat.gz",
  -- Expanded LRAT SHA-256: 73e1a1c2ad44dd3165297a14f31691a19c56c822ae237743a7e7f6ba03265a46
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row200.lrat.gz",
  -- Expanded LRAT SHA-256: fa4fe2bfb32a8dce0142ba706759282fcd1632465d33c0c72d46625dad5bb774
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row201.lrat.gz",
  -- Expanded LRAT SHA-256: 529a609b383a679214d3497b4ee0fe694df424f7c6adca6ea37757602d7aea90
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row202.lrat.gz",
  -- Expanded LRAT SHA-256: b2803a8efe8e11953ba1d77c808db37fcd8a77d465ea77371845f7d7b6086d1b
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row203.lrat.gz",
  -- Expanded LRAT SHA-256: 41245fd6179c1c54e532d1a71a44a74a6dd064229a50cf4b919545d8c1d064ee
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row204.lrat.gz",
  -- Expanded LRAT SHA-256: f336c25f63a08281db07a7937394cf182582083223933b55aa006ae427d3f3a1
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row205.lrat.gz",
  -- Expanded LRAT SHA-256: d5f583cd1241880440af3016321f2ae0b2cc699ef289f9c39129f32eb7c4eb0c
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row206.lrat.gz",
  -- Expanded LRAT SHA-256: 3b5631c5e35d369142e32a8aef0e8e857377fd887b64f77a39a2fffa54ab0d2d
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row207.lrat.gz",
  -- Expanded LRAT SHA-256: 071792198204a20a968e2402952e25ad088823762ded0271a6d21d66d52ff1ce
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row208.lrat.gz",
  -- Expanded LRAT SHA-256: c5639c8883afa541a5e3fb15d47e8a35b4f082d3580d2a9001dbcc5fc267d0c4
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row209.lrat.gz",
  -- Expanded LRAT SHA-256: 5dc9d698161a0a73d572e6a3ac7fef04d94455f565400dba6f20a2ae56650bc6
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row210.lrat.gz",
  -- Expanded LRAT SHA-256: 1eb4a431a3b579de5c5d1339a08785b075b493fe1b6455e301dcbcfeef60aa22
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row211.lrat.gz",
  -- Expanded LRAT SHA-256: 8d1f6c94ca94d90a8e9f081ff2e170f9a1b5e7e29ab85e1ab1e97fb47200d621
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row212.lrat.gz",
  -- Expanded LRAT SHA-256: 1142c9d646f0a2b7d6fb982998831f9516ccf30edcd0988d2b1924c288f8c1ef
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row213.lrat.gz",
  -- Expanded LRAT SHA-256: 919a3f565bc0e7e8be37270b3389db5f0eb9ecdc2aa6fcab4dfef7f6c92141b7
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row214.lrat.gz",
  -- Expanded LRAT SHA-256: 1b11bea361789885003b4fc0c9b5d7d607f1334a289ea9e78ccf87030ae9b98c
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row215.lrat.gz",
  -- Expanded LRAT SHA-256: f541226979c50bc05d0c3431496f92f2b140ddb8e93742c914056cda922143ce
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row216.lrat.gz",
  -- Expanded LRAT SHA-256: d6e363270b18191cd83a5c7f1e6629dca0c914e34e12f8384b8b2e7a1eba97f4
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row217.lrat.gz",
  -- Expanded LRAT SHA-256: 6fe03bf33be31d9088dffc23ef01efcefd69c548c0774fb42af039b3aba08de9
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row218.lrat.gz",
  -- Expanded LRAT SHA-256: b92eb3e5fd9c4d7b2de6fcd336a5b1525e60002181068ae01aba4e321663b6b0
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row219.lrat.gz",
  -- Expanded LRAT SHA-256: a9e9905c438bae630a15fc3265f7853301fdae01e6d62acda724d16bf01b70d8
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row220.lrat.gz",
  -- Expanded LRAT SHA-256: 2e2383225262353c5caaa6f44fb225836f7644f335ca92173514c5c9f51d0a25
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row221.lrat.gz",
  -- Expanded LRAT SHA-256: 67bed8de305547deaf09219227003f4cbfe8c6ecef62c025ec49796cdaf419a4
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row222.lrat.gz",
  -- Expanded LRAT SHA-256: 3d12dc2c97cf18bd6e274ff80eb1fc2e436fcdf005c0e9f74c7d5a72b1593ee5
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row223.lrat.gz",
  -- Expanded LRAT SHA-256: e83f508beb4c5c05f7e393d9dfe2ab8ef2349d5261705f27a369888bf025d129
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row224.lrat.gz",
  -- Expanded LRAT SHA-256: 3b83a96e2d368e12ec382c2d1692fccf6e09e05db4a798459360e70881b111e1
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row225.lrat.gz",
  -- Expanded LRAT SHA-256: 723fafff3ab481494f2628da505e0017440523fe2fd4f7e40831f9268f9e84f5
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row226.lrat.gz",
  -- Expanded LRAT SHA-256: f519b38e25cd206001ddfa4b31b3654994c09192d33c713dd7f278962c486a8f
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row227.lrat.gz",
  -- Expanded LRAT SHA-256: 65f56dcbe6b0ed589beac60111f989607bc26b8b6121f5a8a01a3c6ce4bcb69b
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row228.lrat.gz",
  -- Expanded LRAT SHA-256: ad4be6d796c6c09f5c444fbbce71e6ab71a54f9642031c41865e60211040ac70
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row229.lrat.gz",
  -- Expanded LRAT SHA-256: c2cb1992ce60d404d4c92bdde2f52a2606c635dc6ba0ebcd271c464547a6d7b1
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row230.lrat.gz",
  -- Expanded LRAT SHA-256: 40060a7ac71363afebfaf2e866d6f4f9f21344c566eea4a2df0929843e34b4a2
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row231.lrat.gz",
  -- Expanded LRAT SHA-256: 6acd4532beb894a59f642d8b4194551c5f691ecef5ecf4bc5853484786ac3692
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row232.lrat.gz",
  -- Expanded LRAT SHA-256: d2a91ffa2430e9a14e9dd89dee3e0ba211ea7c059bdd4bfcefed24002a26e66e
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row233.lrat.gz",
  -- Expanded LRAT SHA-256: 48ba12e03d4792dfe092322d8bf3da2cbe57995f43d6905d10ced3c76837897b
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row234.lrat.gz",
  -- Expanded LRAT SHA-256: 13f2cffa3e1ce5a49733c881919af611af8061fc45501959553910d22fc57143
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row235.lrat.gz",
  -- Expanded LRAT SHA-256: 2ad517b87f3f2d5e6e6d56adf9e45f08d12f4cdf5192fc01350616e40c373881
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row236.lrat.gz",
  -- Expanded LRAT SHA-256: b29edc9ec8f53a7eeb109ea27cca9176656bb674e37e5a32d3d1f9e7fffa2328
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row237.lrat.gz",
  -- Expanded LRAT SHA-256: 86fee1d0b75a9949afdd2d9c9320106302ab33177cb4e36a36b9867958b61db8
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row238.lrat.gz",
  -- Expanded LRAT SHA-256: 043bc214abbfc2d376fb02f1079fb23fbfd8470099af1c4c2f8e7f52c4e3305f
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row239.lrat.gz",
  -- Expanded LRAT SHA-256: 47cc2d388fc80f7c3a117cbef6e2a1365724680bc9b1f6953a3589842c2a7d04
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row240.lrat.gz",
  -- Expanded LRAT SHA-256: d039c5e90fcc015b697e60e7e7665ea235ab2cfe68fa5c784a0af41b10ab555e
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row241.lrat.gz",
  -- Expanded LRAT SHA-256: 06d43b7312faaae253423be621ca85e6de4a011a065dbe94932d1844567f73c3
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row242.lrat.gz",
  -- Expanded LRAT SHA-256: 1c62501219229f4086e62c97977a46d16434802d408a762cc462ff93f2fc0af5
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row243.lrat.gz",
  -- Expanded LRAT SHA-256: d4a0479a4a896635e6ef8b1af0509d1fe18b99f7e71654a5e0bdb6b037035b8e
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row244.lrat.gz",
  -- Expanded LRAT SHA-256: db27d7a7045610b6adf97844f74fd876ebd28e2ac69ab2303d7b9684377b3145
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row245.lrat.gz",
  -- Expanded LRAT SHA-256: 17ed38f7cd7aea3e403ed02c155cbd417f523678993b1dacef61d0b84706544b
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row246.lrat.gz",
  -- Expanded LRAT SHA-256: ed159067a681e7354a6c64a9369e02cd95b24706fc9253d0775a14a4f45edca3
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row247.lrat.gz",
  -- Expanded LRAT SHA-256: c6c02a2a0c11b3554c0611bfad797df8560da2605d82eb9aff2150315530aebe
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row248.lrat.gz",
  -- Expanded LRAT SHA-256: 7145aacb4beac94b887b39939c6920d2cf3740e8602dce1306dfd7fc73ccdab5
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row249.lrat.gz",
  -- Expanded LRAT SHA-256: 06db37cab858abcbd8ecc90f868133d37f9c483c068c30953429ffe7a1a3d2d6
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row250.lrat.gz",
  -- Expanded LRAT SHA-256: fb688352a1f085361b742fb6b096ecfd6edfcd227c6917f5b84478da14c00852
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row251.lrat.gz",
  -- Expanded LRAT SHA-256: c4766c7bc38d143c7b31c35c3c5b3495aa2aa05374959a0bf4d499528163ac4d
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row252.lrat.gz",
  -- Expanded LRAT SHA-256: 323e30fc1f8bf37c9e23ed3578eecd5b77893caa181111424558638b6d9f319f
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row253.lrat.gz",
  -- Expanded LRAT SHA-256: 52cdc1277e3a1be50408525582dde763a406f2e38e36c22f88c578120d8e0f57
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row254.lrat.gz",
  -- Expanded LRAT SHA-256: 8ddb6f57981a6fb07d39b81dc7641cd2f97edd75e9cca5ed5bb54e512efa7311
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row255.lrat.gz",
  -- Expanded LRAT SHA-256: f4ad6555eea37a80e2a27a0678a3c6308e95f4db59940182f52f84d4f54d6c54
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row256.lrat.gz",
  -- Expanded LRAT SHA-256: e47888809a8c90ac68ce3e3dd1ea2f0365cb5a88c4c258fc8041f3156121cd31
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row257.lrat.gz",
  -- Expanded LRAT SHA-256: fded6773194da4b100b82c444338401704c4b804a1a217133dd009559fc85532
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row258.lrat.gz",
  -- Expanded LRAT SHA-256: bdc0f7d1c0a96eb183dfee9e4d0ff0a3573477616ab61d5db86e7c59c23821f9
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row259.lrat.gz",
  -- Expanded LRAT SHA-256: 7f7f0319b54c314e0b23db2fc96be458f180927a18786f0fcb0a420682c27e71
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row260.lrat.gz",
  -- Expanded LRAT SHA-256: 0150553f32d558f5b0649a5d6dc379adb1eb53302b80375403387b2092d1a048
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row261.lrat.gz",
  -- Expanded LRAT SHA-256: e894debdd81ca738402ce29ac4fe30603e3d393dcb3c407df70abfb17ffc1658
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row262.lrat.gz",
  -- Expanded LRAT SHA-256: 2ae06b7652afd3c91798b9ffd767eaf0d4cdb576472442bcc1caf76e5b3d647d
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row263.lrat.gz",
  -- Expanded LRAT SHA-256: cbac15ee2381354a50ca270b6d46b2315886593a5d99bbff702e2699103ff6c8
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row264.lrat.gz",
  -- Expanded LRAT SHA-256: b4f3a031332ac1718a6c93308ed3f5373dff2b1e8d7e7b17e6a8c7485f565310
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row265.lrat.gz",
  -- Expanded LRAT SHA-256: 594bc4cc3cfe96f720abc977cac135d9c08fdcedba105ce9e70cc70dfb8b445c
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row266.lrat.gz",
  -- Expanded LRAT SHA-256: 018ce2221532a31cfd2a77401368ae17d0e852f10486570c4c19517f8672622c
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row267.lrat.gz",
  -- Expanded LRAT SHA-256: fc1de69858d656901667d1046abbd39630536323411a69b0ef78881e01c7e432
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row268.lrat.gz",
  -- Expanded LRAT SHA-256: 458681f98bec5cff413b4eba542298fcd4ee692ec25e448153c267febc36405a
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row269.lrat.gz",
  -- Expanded LRAT SHA-256: d04e45651ae1e379f5cfea6bfec1fc5b400ac19f0b941fdff3b658fda1adf041
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row270.lrat.gz",
  -- Expanded LRAT SHA-256: 1f6aca7fc43eec8f0213429d35f468fe4bc8d7d49c7b2f42df8ffda8aa37ec4c
  include_gzip_str "../../../../data/spectrum/1279_thirteen_lrat/row271.lrat.gz"]

/-- Parse one case at a time to bound the memory used by the finite check. -/
private def proof (i : Fin 272) : Array IntAction :=
  (parseLRATProof proofTexts[i.val]!.toUTF8).toOption.getD #[]

private def allChecked : Bool :=
  let common := natBase
  (List.finRange 272).all (fun i => check (proof i) (natFormulaWith common i))

@[spectrum_native]
private theorem all_checked : allChecked = true := by native_decide

theorem checked (i : Fin 272) : check (proof i) (natFormula i) = true := by
  exact List.all_eq_true.mp all_checked i (List.mem_finRange i)

theorem unsat (i : Fin 272) : (natFormula i).Unsat :=
  check_sound _ _ (checked i)

spectrum_assert unsat complete
end Spectrum.SmallPairs.OrderThirteen

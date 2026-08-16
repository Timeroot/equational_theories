import equational_theories.Definability.Affine
import equational_theories.Equations.All

/-!
# Clone certificates

The magmas whose clone `Definability/NegativeCover.lean` needs, each with its clone spelled
out as an explicit family and the composition data that witnesses closure.

Most of the bank is affine, and closure is then proved by `Magma.affineFin_isCloneFamily`
or `Magma.affineOf_isCloneFamily` rather than by `decide` -- see `Definability/Affine.lean`
for why. The remainder are given as raw tables, and for those all three
`Magma.IsCloneFamily` fields are `decideFin!`.

| certificate | carrier | table | clone | shape |
| --- | --- | --- | --- | --- |
| `Magma.negCert1` | `Fin 3` | `000102010002020100` | `12` | `table` |
| `Magma.negCert2` | `Fin 4` | `03010301030103010200020002000200` | `16` | `table` |
| `Magma.negCert3` | `Fin 8` | `00010203040506070100030205040706020300010706040503020100060705040405060700010302050407060100020306070504020300010706040503020100` | `8` | `table` |
| `Magma.negCert4` | `Fin 2` | `00010100` | `4` | `full` |
| `Magma.negCert5` | `Fin 3` | `000201010002020100` | `9` | `full` |
| `Magma.negCert6` | `Fin 2` | `00000001` | `3` | `table` |
| `Magma.negCert7` | `Fin 9` | `000807060504030201080706050403020100070605040302010008060504030201000807050403020100080706040302010008070605030201000807060504020100080706050403010008070605040302` | `27` | `aff` |
| `Magma.negCert8` | `Fin 19` | `000e0904120d0803110c0702100b06010f0a0506010f0a05000e0904120d0803110c0702100b0c0702100b06010f0a05000e0904120d080311120d0803110c0702100b06010f0a05000e090405000e0904120d0803110c0702100b06010f0a0b06010f0a05000e0904120d0803110c070210110c0702100b06010f0a05000e0904120d080304120d0803110c0702100b06010f0a05000e090a05000e0904120d0803110c0702100b06010f100b06010f0a05000e0904120d0803110c070203110c0702100b06010f0a05000e0904120d080904120d0803110c0702100b06010f0a05000e0f0a05000e0904120d0803110c0702100b060102100b06010f0a05000e0904120d0803110c070803110c0702100b06010f0a05000e0904120d0e0904120d0803110c0702100b06010f0a0500010f0a05000e0904120d0803110c0702100b060702100b06010f0a05000e0904120d0803110c0d0803110c0702100b06010f0a05000e090412` | `19` | `idem` |
| `Magma.negCert9` | `Fin 16` | `00090108020b030a040d050c060f070e080109000a030b020c050d040e070f06030a020b01080009070e060f050c040d0b020a03090008010f060e070d040c05060f070e040d050c020b030a000901080e070f060c050d040a030b0208010900050c040d070e060f01080009030a020b0d040c050f060e07090008010b020a030c050d040e070f06080109000a030b02040d050c060f070e00090108020b030a0f060e070d040c050b020a0309000801070e060f050c040d030a020b010800090a030b02080109000e070f060c050d04020b030a00090108060f070e040d050c090008010b020a030d040c050f060e0701080009030a020b050c040d070e060f` | `16` | `gf16` |
| `Magma.negCert10` | `Fin 5` | `02010304000002040103040302000103000102040104000302` | `25` | `table` |
| `Magma.negCert11` | `Fin 13` | `000701080209030a040b050c060701080209030a040b050c060001080209030a040b050c060007080209030a040b050c060007010209030a040b050c060007010809030a040b050c060007010802030a040b050c060007010802090a040b050c0600070108020903040b050c06000701080209030a0b050c06000701080209030a04050c06000701080209030a040b0c06000701080209030a040b0506000701080209030a040b050c` | `13` | `idem` |
| `Magma.negCert12` | `Fin 5` | `00010203040402000103010403000202030104000300040201` | `25` | `table` |
| `Magma.negCert13` | `Fin 16` | `000306050c0f0a090b080d0e07040102020104070e0d080b090a0f0c0506030004070201080b0e0d0f0c090a03000506060500030a090c0f0d0e0b0801020704080b0e0d04070201030005060f0c090a0a090c0f06050003010207040d0e0b080c0f0a0900030605070401020b080d0e0e0d080b0201040705060300090a0f0c030005060f0c090a080b0e0d04070201010207040d0e0b080a090c0f06050003070401020b080d0e0c0f0a090003060505060300090a0f0c0e0d080b020104070b080d0e07040102000306050c0f0a09090a0f0c05060300020104070e0d080b0f0c090a0300050604070201080b0e0d0d0e0b0801020704060500030a090c0f` | `16` | `gf16` |
| `Magma.negCert14` | `Fin 13` | `000b09070503010c0a0806040203010c0a08060402000b090705060402000b09070503010c0a0809070503010c0a08060402000b0c0a08060402000b090705030102000b09070503010c0a0806040503010c0a08060402000b090708060402000b09070503010c0a0b09070503010c0a0806040200010c0a08060402000b090705030402000b09070503010c0a0806070503010c0a08060402000b090a08060402000b09070503010c` | `13` | `idem` |
| `Magma.negCert15` | `Fin 13` | `0008030b060109040c07020a05060109040c07020a050008030b0c07020a050008030b06010904050008030b060109040c07020a0b060109040c07020a05000803040c07020a050008030b0601090a050008030b060109040c0702030b060109040c07020a05000809040c07020a050008030b0601020a050008030b060109040c0708030b060109040c07020a05000109040c07020a050008030b0607020a050008030b060109040c` | `13` | `idem` |
| `Magma.negCert16` | `Fin 5` | `00020304010103000204020104000303040201000400010302` | `25` | `table` |
| `Magma.negCert17` | `Fin 4` | `00010203010003020203010003020001` | `16` | `table` |
| `Magma.negCert18` | `Fin 17` | `000f0d0b0907050301100e0c0a080604020301100e0c0a08060402000f0d0b090705060402000f0d0b0907050301100e0c0a080907050301100e0c0a08060402000f0d0b0c0a08060402000f0d0b0907050301100e0f0d0b0907050301100e0c0a080604020001100e0c0a08060402000f0d0b090705030402000f0d0b0907050301100e0c0a080607050301100e0c0a08060402000f0d0b090a08060402000f0d0b0907050301100e0c0d0b0907050301100e0c0a08060402000f100e0c0a08060402000f0d0b090705030102000f0d0b0907050301100e0c0a080604050301100e0c0a08060402000f0d0b090708060402000f0d0b0907050301100e0c0a0b0907050301100e0c0a08060402000f0d0e0c0a08060402000f0d0b090705030110` | `17` | `idem` |
| `Magma.negCert19` | `Fin 9` | `000204060801030507020406080103050700040608010305070002060801030507000204080103050700020406010305070002040608030507000204060801050700020406080103070002040608010305` | `27` | `aff` |
| `Magma.negCert20` | `Fin 7` | `00020406010305010305000204060204060103050003050002040601040601030500020500020406010306010305000204` | `49` | `full` |

The cheapest of these is worth singling out: the two-element semilattice, whose clone is
just `{x, y, x ⊓ y}`. It is the finite shadow of `(ℕ, +)` — an `x ⊓ y` term with `c` leaves
labelled `x` and `d` labelled `y` computes `min(c, 1) x ⊓ min(d, 1) y`, and `min(·, 1)` is a
semiring homomorphism out of `ℕ`, so it sees exactly the sign pattern of the coefficients.
That is what lets it refute the cyclic-associativity laws, whose invariant operations are
affine and hence invisible to every automorphism certificate.

The affine certificates are there for the opposite reason. Every term of `(R, a x + b y)`
is again of the form `p x + q y`, so the clone lives in coefficient space; and when
`a + b = 1` the magma is idempotent and every term`s coefficient pair sums to `1` too,
which pins the clone down to `|R|` operations. Those are the only certificates that say
anything at all about the rigid `x = (word in x and y)` laws: such a law asks for a word
with coefficient pair `(1, 0)`, which a semilattice or a rectangular band can never produce
but an affine magma readily does.

This file is generated.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Magma

/-- A magma on `Fin 3` whose binary clone has only `12` members. -/
@[implicit_reducible]
def negCert1 : Magma (Fin 3) := ⟨![![0, 1, 2], ![1, 0, 2], ![2, 1, 0]]⟩

/-- The `12` operations term-definable from `Magma.negCert1`. -/
@[implicit_reducible]
def negCert1Clone : Fin 12 → Magma (Fin 3) := ![⟨![![0, 0, 0], ![1, 1, 1], ![2, 2, 2]]⟩, ⟨![![0, 1, 2], ![0, 1, 2], ![0, 1, 2]]⟩, ⟨![![0, 0, 0], ![0, 0, 0], ![0, 0, 0]]⟩, ⟨![![0, 1, 2], ![1, 0, 2], ![2, 1, 0]]⟩, ⟨![![0, 1, 2], ![1, 0, 1], ![2, 2, 0]]⟩, ⟨![![0, 0, 0], ![1, 1, 0], ![2, 0, 2]]⟩, ⟨![![0, 0, 0], ![1, 1, 2], ![2, 1, 2]]⟩, ⟨![![0, 1, 2], ![0, 1, 1], ![0, 2, 2]]⟩, ⟨![![0, 0, 0], ![0, 0, 1], ![0, 2, 0]]⟩, ⟨![![0, 0, 0], ![0, 0, 2], ![0, 1, 0]]⟩, ⟨![![0, 1, 2], ![0, 1, 0], ![0, 0, 2]]⟩, ⟨![![0, 1, 2], ![1, 0, 0], ![2, 0, 0]]⟩]

/-- Where each composite of two members of `Magma.negCert1Clone` lands. -/
@[implicit_reducible]
def negCert1Comp : Fin 12 → Fin 12 → Fin 12 :=
  ![![2, 3, 0, 1, 10, 8, 9, 11, 5, 6, 4, 7],
    ![4, 2, 1, 5, 0, 3, 11, 8, 7, 10, 9, 6],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
    ![7, 5, 3, 2, 8, 1, 10, 0, 4, 11, 6, 9],
    ![10, 6, 4, 9, 2, 7, 1, 5, 11, 3, 0, 8],
    ![8, 3, 5, 1, 7, 2, 9, 4, 0, 6, 11, 10],
    ![8, 11, 6, 10, 7, 9, 2, 4, 0, 5, 3, 1],
    ![11, 9, 7, 6, 5, 4, 3, 2, 10, 1, 8, 0],
    ![5, 1, 8, 3, 11, 0, 6, 10, 2, 9, 7, 4],
    ![0, 10, 9, 11, 4, 6, 5, 7, 8, 2, 1, 3],
    ![4, 9, 10, 6, 0, 11, 3, 8, 7, 1, 2, 5],
    ![7, 6, 11, 9, 8, 10, 1, 0, 4, 3, 5, 2]]

theorem negCert1_isCloneFamily :
    negCert1.IsCloneFamily negCert1Clone 0 1 negCert1Comp :=
  ⟨by decideFin!, by decideFin!, by decideFin!⟩

/-- A magma on `Fin 4` whose binary clone has only `16` members. -/
@[implicit_reducible]
def negCert2 : Magma (Fin 4) := ⟨![![3, 1, 3, 1], ![3, 1, 3, 1], ![2, 0, 2, 0], ![2, 0, 2, 0]]⟩

/-- The `16` operations term-definable from `Magma.negCert2`. -/
@[implicit_reducible]
def negCert2Clone : Fin 16 → Magma (Fin 4) := ![⟨![![0, 0, 0, 0], ![1, 1, 1, 1], ![2, 2, 2, 2], ![3, 3, 3, 3]]⟩, ⟨![![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]⟩, ⟨![![3, 3, 3, 3], ![1, 1, 1, 1], ![2, 2, 2, 2], ![0, 0, 0, 0]]⟩, ⟨![![3, 1, 3, 1], ![3, 1, 3, 1], ![2, 0, 2, 0], ![2, 0, 2, 0]]⟩, ⟨![![3, 3, 2, 2], ![1, 1, 0, 0], ![3, 3, 2, 2], ![1, 1, 0, 0]]⟩, ⟨![![3, 1, 2, 0], ![3, 1, 2, 0], ![3, 1, 2, 0], ![3, 1, 2, 0]]⟩, ⟨![![1, 1, 0, 0], ![1, 1, 0, 0], ![3, 3, 2, 2], ![3, 3, 2, 2]]⟩, ⟨![![2, 0, 2, 0], ![3, 1, 3, 1], ![2, 0, 2, 0], ![3, 1, 3, 1]]⟩, ⟨![![2, 1, 2, 1], ![2, 1, 2, 1], ![2, 1, 2, 1], ![2, 1, 2, 1]]⟩, ⟨![![1, 1, 2, 2], ![1, 1, 2, 2], ![1, 1, 2, 2], ![1, 1, 2, 2]]⟩, ⟨![![2, 2, 2, 2], ![1, 1, 1, 1], ![2, 2, 2, 2], ![1, 1, 1, 1]]⟩, ⟨![![1, 1, 1, 1], ![1, 1, 1, 1], ![2, 2, 2, 2], ![2, 2, 2, 2]]⟩, ⟨![![0, 1, 0, 1], ![0, 1, 0, 1], ![2, 3, 2, 3], ![2, 3, 2, 3]]⟩, ⟨![![0, 0, 2, 2], ![1, 1, 3, 3], ![0, 0, 2, 2], ![1, 1, 3, 3]]⟩, ⟨![![2, 3, 2, 3], ![0, 1, 0, 1], ![2, 3, 2, 3], ![0, 1, 0, 1]]⟩, ⟨![![1, 1, 3, 3], ![1, 1, 3, 3], ![0, 0, 2, 2], ![0, 0, 2, 2]]⟩]

/-- Where each composite of two members of `Magma.negCert2Clone` lands. -/
@[implicit_reducible]
def negCert2Comp : Fin 16 → Fin 16 → Fin 16 :=
  ![![2, 3, 11, 11, 15, 15, 15, 2, 3, 15, 2, 11, 3, 2, 3, 11],
    ![4, 5, 6, 6, 9, 9, 9, 4, 5, 9, 4, 6, 5, 4, 5, 6],
    ![10, 7, 0, 0, 13, 13, 13, 10, 7, 13, 10, 0, 7, 10, 7, 0],
    ![14, 8, 12, 12, 1, 1, 1, 14, 8, 1, 14, 12, 8, 14, 8, 12],
    ![10, 7, 0, 0, 13, 13, 13, 10, 7, 13, 10, 0, 7, 10, 7, 0],
    ![14, 8, 12, 12, 1, 1, 1, 14, 8, 1, 14, 12, 8, 14, 8, 12],
    ![2, 3, 11, 11, 15, 15, 15, 2, 3, 15, 2, 11, 3, 2, 3, 11],
    ![14, 8, 12, 12, 1, 1, 1, 14, 8, 1, 14, 12, 8, 14, 8, 12],
    ![14, 8, 12, 12, 1, 1, 1, 14, 8, 1, 14, 12, 8, 14, 8, 12],
    ![4, 5, 6, 6, 9, 9, 9, 4, 5, 9, 4, 6, 5, 4, 5, 6],
    ![10, 7, 0, 0, 13, 13, 13, 10, 7, 13, 10, 0, 7, 10, 7, 0],
    ![2, 3, 11, 11, 15, 15, 15, 2, 3, 15, 2, 11, 3, 2, 3, 11],
    ![2, 3, 11, 11, 15, 15, 15, 2, 3, 15, 2, 11, 3, 2, 3, 11],
    ![4, 5, 6, 6, 9, 9, 9, 4, 5, 9, 4, 6, 5, 4, 5, 6],
    ![10, 7, 0, 0, 13, 13, 13, 10, 7, 13, 10, 0, 7, 10, 7, 0],
    ![4, 5, 6, 6, 9, 9, 9, 4, 5, 9, 4, 6, 5, 4, 5, 6]]

theorem negCert2_isCloneFamily :
    negCert2.IsCloneFamily negCert2Clone 0 1 negCert2Comp :=
  ⟨by decideFin!, by decideFin!, by decideFin!⟩

/-- A magma on `Fin 8` whose binary clone has only `8` members. -/
@[implicit_reducible]
def negCert3 : Magma (Fin 8) := ⟨![![0, 1, 2, 3, 4, 5, 6, 7], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 7, 6, 4, 5], ![3, 2, 1, 0, 6, 7, 5, 4], ![4, 5, 6, 7, 0, 1, 3, 2], ![5, 4, 7, 6, 1, 0, 2, 3], ![6, 7, 5, 4, 2, 3, 0, 1], ![7, 6, 4, 5, 3, 2, 1, 0]]⟩

/-- The `8` operations term-definable from `Magma.negCert3`. -/
@[implicit_reducible]
def negCert3Clone : Fin 8 → Magma (Fin 8) := ![⟨![![0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1], ![2, 2, 2, 2, 2, 2, 2, 2], ![3, 3, 3, 3, 3, 3, 3, 3], ![4, 4, 4, 4, 4, 4, 4, 4], ![5, 5, 5, 5, 5, 5, 5, 5], ![6, 6, 6, 6, 6, 6, 6, 6], ![7, 7, 7, 7, 7, 7, 7, 7]]⟩, ⟨![![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7]]⟩, ⟨![![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]]⟩, ⟨![![0, 1, 2, 3, 4, 5, 6, 7], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 7, 6, 4, 5], ![3, 2, 1, 0, 6, 7, 5, 4], ![4, 5, 6, 7, 0, 1, 3, 2], ![5, 4, 7, 6, 1, 0, 2, 3], ![6, 7, 5, 4, 2, 3, 0, 1], ![7, 6, 4, 5, 3, 2, 1, 0]]⟩, ⟨![![0, 1, 2, 3, 4, 5, 6, 7], ![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 6, 7, 5, 4], ![3, 2, 1, 0, 7, 6, 4, 5], ![4, 5, 7, 6, 0, 1, 2, 3], ![5, 4, 6, 7, 1, 0, 3, 2], ![6, 7, 4, 5, 3, 2, 0, 1], ![7, 6, 5, 4, 2, 3, 1, 0]]⟩, ⟨![![0, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1], ![2, 2, 2, 2, 3, 3, 3, 3], ![3, 3, 3, 3, 2, 2, 2, 2], ![4, 4, 5, 5, 4, 4, 5, 5], ![5, 5, 4, 4, 5, 5, 4, 4], ![6, 6, 7, 7, 7, 7, 6, 6], ![7, 7, 6, 6, 6, 6, 7, 7]]⟩, ⟨![![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 4, 5, 6, 7], ![0, 1, 2, 3, 5, 4, 7, 6], ![0, 1, 2, 3, 5, 4, 7, 6], ![0, 1, 3, 2, 4, 5, 7, 6], ![0, 1, 3, 2, 4, 5, 7, 6], ![0, 1, 3, 2, 5, 4, 6, 7], ![0, 1, 3, 2, 5, 4, 6, 7]]⟩, ⟨![![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 1, 1, 1], ![0, 0, 0, 0, 1, 1, 1, 1], ![0, 0, 1, 1, 0, 0, 1, 1], ![0, 0, 1, 1, 0, 0, 1, 1], ![0, 0, 1, 1, 1, 1, 0, 0], ![0, 0, 1, 1, 1, 1, 0, 0]]⟩]

/-- Where each composite of two members of `Magma.negCert3Clone` lands. -/
@[implicit_reducible]
def negCert3Comp : Fin 8 → Fin 8 → Fin 8 :=
  ![![2, 3, 0, 6, 1, 7, 4, 5],
    ![4, 2, 1, 0, 5, 3, 7, 6],
    ![0, 1, 2, 3, 4, 5, 6, 7],
    ![1, 5, 3, 2, 7, 6, 0, 4],
    ![6, 0, 4, 7, 2, 1, 5, 3],
    ![7, 4, 5, 1, 6, 2, 3, 0],
    ![3, 7, 6, 5, 0, 4, 2, 1],
    ![5, 6, 7, 4, 3, 0, 1, 2]]

theorem negCert3_isCloneFamily :
    negCert3.IsCloneFamily negCert3Clone 0 1 negCert3Comp :=
  ⟨by decideFin!, by decideFin!, by decideFin!⟩

/-- The affine magma `x ◇ y = 1 x + 1 y` on `Fin 2`. -/
@[implicit_reducible]
def negCert4 : Magma (Fin 2) := affineFin 2 1 1

/-- The clone is all `2 * 2` affine operations, indexed here by
`2 p + q` for the coefficient pair `(p, q)`. -/
@[implicit_reducible]
def negCert4P : Fin 4 → ℕ := fun i ↦ i.val / 2

@[implicit_reducible]
def negCert4Q : Fin 4 → ℕ := fun i ↦ i.val % 2

/-- The `4` operations term-definable from `Magma.negCert4`. -/
@[implicit_reducible]
def negCert4Clone : Fin 4 → Magma (Fin 2) := fun i ↦ affineFin 2 (negCert4P i) (negCert4Q i)

/-- Coefficients compose affinely: `(1 p + 1 p′, 1 q + 1 q′)`. -/
@[implicit_reducible]
def negCert4Comp : Fin 4 → Fin 4 → Fin 4 := fun i j ↦ ⟨(2 * ((1 * (i.val / 2) + 1 * (j.val / 2)) % 2) + (1 * (i.val % 2) + 1 * (j.val % 2)) % 2) % 4, Nat.mod_lt _ (by omega)⟩

theorem negCert4_isCloneFamily :
    negCert4.IsCloneFamily negCert4Clone 2 1 negCert4Comp :=
  affineFin_isCloneFamily 2 1 1 negCert4P negCert4Q 2 1 negCert4Comp
    (by decide) (by decide) (by decide) (by decide) (by decide!)

/-- The affine magma `x ◇ y = 1 x + 2 y` on `Fin 3`. -/
@[implicit_reducible]
def negCert5 : Magma (Fin 3) := affineFin 3 1 2

/-- The clone is all `3 * 3` affine operations, indexed here by
`3 p + q` for the coefficient pair `(p, q)`. -/
@[implicit_reducible]
def negCert5P : Fin 9 → ℕ := fun i ↦ i.val / 3

@[implicit_reducible]
def negCert5Q : Fin 9 → ℕ := fun i ↦ i.val % 3

/-- The `9` operations term-definable from `Magma.negCert5`. -/
@[implicit_reducible]
def negCert5Clone : Fin 9 → Magma (Fin 3) := fun i ↦ affineFin 3 (negCert5P i) (negCert5Q i)

/-- Coefficients compose affinely: `(1 p + 2 p′, 1 q + 2 q′)`. -/
@[implicit_reducible]
def negCert5Comp : Fin 9 → Fin 9 → Fin 9 := fun i j ↦ ⟨(3 * ((1 * (i.val / 3) + 2 * (j.val / 3)) % 3) + (1 * (i.val % 3) + 2 * (j.val % 3)) % 3) % 9, Nat.mod_lt _ (by omega)⟩

theorem negCert5_isCloneFamily :
    negCert5.IsCloneFamily negCert5Clone 3 1 negCert5Comp :=
  affineFin_isCloneFamily 3 1 2 negCert5P negCert5Q 3 1 negCert5Comp
    (by decide) (by decide) (by decide) (by decide) (by decide!)

/-- A magma on `Fin 2` whose binary clone has only `3` members. -/
@[implicit_reducible]
def negCert6 : Magma (Fin 2) := ⟨![![0, 0], ![0, 1]]⟩

/-- The `3` operations term-definable from `Magma.negCert6`. -/
@[implicit_reducible]
def negCert6Clone : Fin 3 → Magma (Fin 2) := ![⟨![![0, 0], ![0, 1]]⟩, ⟨![![0, 1], ![0, 1]]⟩, ⟨![![0, 0], ![1, 1]]⟩]

/-- Where each composite of two members of `Magma.negCert6Clone` lands. -/
@[implicit_reducible]
def negCert6Comp : Fin 3 → Fin 3 → Fin 3 :=
  ![![0, 0, 0],
    ![0, 1, 0],
    ![0, 0, 2]]

theorem negCert6_isCloneFamily :
    negCert6.IsCloneFamily negCert6Clone 2 1 negCert6Comp :=
  ⟨by decideFin!, by decideFin!, by decideFin!⟩

/-- The affine magma `x ◇ y = 8 x + 8 y` on `Fin 9`. -/
@[implicit_reducible]
def negCert7 : Magma (Fin 9) := affineFin 9 8 8

/-- The `27` coefficient pairs of the clone. -/
@[implicit_reducible]
def negCert7P : Fin 27 → ℕ := ![5, 8, 2, 4, 3, 6, 0, 3, 1, 6, 2, 8, 2, 0, 1, 7, 8, 7, 0, 4, 4, 5, 3, 1, 6, 7, 5]

@[implicit_reducible]
def negCert7Q : Fin 27 → ℕ := ![8, 8, 8, 0, 4, 4, 1, 7, 6, 7, 2, 5, 5, 4, 0, 6, 2, 3, 7, 3, 6, 2, 1, 3, 1, 0, 5]

/-- The `27` operations term-definable from `Magma.negCert7`. -/
@[implicit_reducible]
def negCert7Clone : Fin 27 → Magma (Fin 9) := fun i ↦ affineFin 9 (negCert7P i) (negCert7Q i)

/-- Coefficients compose affinely: `(8 p + 8 p′, 8 q + 8 q′)`. -/
@[implicit_reducible]
def negCert7Comp : Fin 27 → Fin 27 → Fin 27 :=
  ![![16, 21, 10, 6, 8, 15, 3, 23, 4, 17, 2, 26, 12, 20, 22, 5, 0, 9, 19, 18, 13, 1, 14, 7, 25, 24, 11],
    ![21, 10, 16, 24, 15, 20, 14, 17, 13, 19, 1, 12, 11, 8, 6, 4, 2, 7, 23, 9, 5, 0, 25, 18, 3, 22, 26],
    ![10, 16, 21, 22, 20, 8, 25, 19, 5, 23, 0, 11, 26, 15, 24, 13, 1, 18, 17, 7, 4, 2, 3, 9, 14, 6, 12],
    ![6, 24, 22, 14, 12, 11, 0, 10, 19, 16, 7, 5, 4, 26, 3, 17, 9, 15, 21, 8, 23, 18, 2, 20, 1, 25, 13],
    ![8, 15, 20, 12, 22, 6, 5, 7, 0, 18, 19, 25, 3, 24, 26, 1, 17, 16, 9, 10, 2, 23, 4, 21, 13, 11, 14],
    ![15, 20, 8, 11, 6, 24, 4, 18, 2, 9, 23, 3, 14, 22, 12, 0, 19, 21, 7, 16, 1, 17, 13, 10, 5, 26, 25],
    ![3, 14, 25, 0, 5, 4, 18, 24, 16, 22, 15, 23, 17, 13, 1, 10, 8, 12, 6, 26, 21, 20, 9, 11, 7, 2, 19],
    ![23, 17, 19, 10, 7, 18, 24, 4, 26, 13, 3, 15, 20, 9, 21, 11, 25, 1, 5, 2, 12, 14, 22, 0, 6, 16, 8],
    ![4, 13, 5, 19, 0, 2, 16, 26, 15, 12, 24, 18, 9, 1, 17, 8, 6, 14, 11, 3, 20, 22, 21, 25, 10, 23, 7],
    ![17, 19, 23, 16, 18, 9, 22, 13, 12, 5, 14, 20, 8, 7, 10, 26, 3, 0, 4, 1, 11, 25, 6, 2, 24, 21, 15],
    ![2, 1, 0, 7, 19, 23, 15, 3, 24, 14, 26, 16, 21, 17, 9, 6, 11, 13, 25, 4, 22, 12, 20, 5, 8, 18, 10],
    ![26, 12, 11, 5, 25, 3, 23, 15, 18, 20, 16, 2, 1, 14, 13, 7, 10, 22, 8, 24, 9, 21, 17, 6, 19, 4, 0],
    ![12, 11, 26, 4, 3, 14, 17, 20, 9, 8, 21, 1, 0, 25, 5, 18, 16, 6, 15, 22, 7, 10, 19, 24, 23, 13, 2],
    ![20, 8, 15, 26, 24, 22, 13, 9, 1, 7, 17, 14, 25, 6, 11, 2, 23, 10, 18, 21, 0, 19, 5, 16, 4, 12, 3],
    ![22, 6, 24, 3, 26, 12, 1, 21, 17, 10, 9, 13, 5, 11, 25, 23, 18, 8, 16, 20, 19, 7, 0, 15, 2, 14, 4],
    ![5, 4, 13, 17, 1, 0, 10, 11, 8, 26, 6, 7, 18, 2, 23, 20, 22, 3, 12, 25, 15, 24, 16, 14, 21, 19, 9],
    ![0, 2, 1, 9, 17, 19, 8, 25, 6, 3, 11, 10, 16, 23, 18, 22, 12, 4, 14, 5, 24, 26, 15, 13, 20, 7, 21],
    ![9, 7, 18, 15, 16, 21, 12, 1, 14, 0, 13, 22, 6, 10, 8, 3, 4, 19, 2, 17, 25, 5, 11, 23, 26, 20, 24],
    ![19, 23, 17, 21, 9, 7, 6, 5, 11, 4, 25, 8, 15, 18, 16, 12, 14, 2, 13, 0, 26, 3, 24, 1, 22, 10, 20],
    ![18, 9, 7, 8, 10, 16, 26, 2, 3, 1, 4, 24, 22, 21, 20, 25, 5, 17, 0, 23, 14, 13, 12, 19, 11, 15, 6],
    ![13, 5, 4, 23, 2, 1, 21, 12, 20, 11, 22, 9, 7, 0, 19, 15, 24, 25, 26, 14, 8, 6, 10, 3, 16, 17, 18],
    ![1, 0, 2, 18, 23, 17, 20, 14, 22, 25, 12, 21, 10, 19, 7, 24, 26, 5, 3, 13, 6, 11, 8, 4, 15, 9, 16],
    ![14, 25, 3, 2, 4, 13, 9, 22, 21, 6, 20, 17, 19, 5, 0, 16, 15, 11, 24, 12, 10, 8, 7, 26, 18, 1, 23],
    ![7, 18, 9, 20, 21, 10, 11, 0, 25, 2, 5, 6, 24, 16, 15, 14, 13, 23, 1, 19, 3, 4, 26, 17, 12, 8, 22],
    ![25, 3, 14, 1, 13, 5, 7, 6, 10, 24, 8, 19, 23, 4, 2, 21, 20, 26, 22, 11, 16, 15, 18, 12, 9, 0, 17],
    ![24, 22, 6, 25, 11, 26, 2, 16, 23, 21, 18, 4, 13, 12, 14, 19, 7, 20, 10, 15, 17, 9, 1, 8, 0, 3, 5],
    ![11, 26, 12, 13, 14, 25, 19, 8, 7, 15, 10, 0, 2, 3, 4, 9, 21, 24, 20, 6, 18, 16, 23, 22, 17, 5, 1]]

theorem negCert7_isCloneFamily :
    negCert7.IsCloneFamily negCert7Clone 14 6 negCert7Comp :=
  affineFin_isCloneFamily 9 8 8 negCert7P negCert7Q 14 6 negCert7Comp
    (by decide) (by decide) (by decide) (by decide) (by decide!)

/-- The affine magma `x ◇ y = 6 x + 14 y` on `Fin 19`. -/
@[implicit_reducible]
def negCert8 : Magma (Fin 19) := affineFin 19 6 14

/-- Since `6 + 14 = 1` the magma is idempotent, so every term of it is
`p x + (1 - p) y` and its clone has exactly `19` members, indexed here by
the coefficient `p` of `x`. -/
@[implicit_reducible]
def negCert8P : Fin 19 → ℕ := fun i ↦ i.val

@[implicit_reducible]
def negCert8Q : Fin 19 → ℕ := fun i ↦ (19 + 1 - i.val) % 19

/-- The `19` operations term-definable from `Magma.negCert8`. -/
@[implicit_reducible]
def negCert8Clone : Fin 19 → Magma (Fin 19) := fun i ↦ affineFin 19 (negCert8P i) (negCert8Q i)

/-- Coefficients compose affinely: `6 i + 14 j`. -/
@[implicit_reducible]
def negCert8Comp : Fin 19 → Fin 19 → Fin 19 := fun i j ↦ ⟨(6 * i.val + 14 * j.val) % 19, Nat.mod_lt _ (by omega)⟩

theorem negCert8_isCloneFamily :
    negCert8.IsCloneFamily negCert8Clone 1 0 negCert8Comp :=
  affineFin_isCloneFamily 19 6 14 negCert8P negCert8Q 1 0 negCert8Comp
    (by decide) (by decide) (by decide) (by decide) (by decide!)

/-- The affine magma `x ◇ y = 8 x + 9 y` over `GF(16)`. Since `8 + 9 = 1`
it is idempotent, so its clone is the `16` operations `p x + (1 - p) y`, indexed
here by the coefficient `p` of `x`. -/
@[implicit_reducible]
def negCert9 : Magma (Fin 16) := affineOf gf16add gf16 8 9

@[implicit_reducible]
def negCert9P : Fin 16 → Fin 16 := fun i ↦ i

@[implicit_reducible]
def negCert9Q : Fin 16 → Fin 16 := fun i ↦ gf16add 1 i

/-- The `16` operations term-definable from `Magma.negCert9`. -/
@[implicit_reducible]
def negCert9Clone : Fin 16 → Magma (Fin 16) := fun i ↦ affineOf gf16add gf16 (negCert9P i) (negCert9Q i)

/-- Coefficients compose affinely: `8 p + 9 p′`. -/
@[implicit_reducible]
def negCert9Comp : Fin 16 → Fin 16 → Fin 16 := fun i j ↦ gf16add (gf16 8 i) (gf16 9 j)

theorem negCert9_isCloneFamily :
    negCert9.IsCloneFamily negCert9Clone 1 0 negCert9Comp :=
  affineOf_isCloneFamily gf16add gf16 0 1 gf16add_assoc gf16add_comm
    gf16add_zero gf16_one gf16_zero gf16_assoc gf16_distrib gf16_distrib'
    8 9 negCert9P negCert9Q 1 0 negCert9Comp rfl (by decide) rfl (by decide) (by decide!)

/-- A magma on `Fin 5` whose binary clone has only `25` members. -/
@[implicit_reducible]
def negCert10 : Magma (Fin 5) := ⟨![![2, 1, 3, 4, 0], ![0, 2, 4, 1, 3], ![4, 3, 2, 0, 1], ![3, 0, 1, 2, 4], ![1, 4, 0, 3, 2]]⟩

/-- The `25` operations term-definable from `Magma.negCert10`. -/
@[implicit_reducible]
def negCert10Clone : Fin 25 → Magma (Fin 5) := ![⟨![![0, 0, 0, 0, 0], ![1, 1, 1, 1, 1], ![2, 2, 2, 2, 2], ![3, 3, 3, 3, 3], ![4, 4, 4, 4, 4]]⟩, ⟨![![0, 1, 2, 3, 4], ![0, 1, 2, 3, 4], ![0, 1, 2, 3, 4], ![0, 1, 2, 3, 4], ![0, 1, 2, 3, 4]]⟩, ⟨![![2, 2, 2, 2, 2], ![2, 2, 2, 2, 2], ![2, 2, 2, 2, 2], ![2, 2, 2, 2, 2], ![2, 2, 2, 2, 2]]⟩, ⟨![![2, 1, 3, 4, 0], ![0, 2, 4, 1, 3], ![4, 3, 2, 0, 1], ![3, 0, 1, 2, 4], ![1, 4, 0, 3, 2]]⟩, ⟨![![2, 0, 4, 3, 1], ![1, 2, 3, 0, 4], ![3, 4, 2, 1, 0], ![4, 1, 0, 2, 3], ![0, 3, 1, 4, 2]]⟩, ⟨![![3, 4, 2, 1, 0], ![3, 4, 2, 1, 0], ![3, 4, 2, 1, 0], ![3, 4, 2, 1, 0], ![3, 4, 2, 1, 0]]⟩, ⟨![![4, 3, 2, 0, 1], ![4, 3, 2, 0, 1], ![4, 3, 2, 0, 1], ![4, 3, 2, 0, 1], ![4, 3, 2, 0, 1]]⟩, ⟨![![3, 2, 0, 4, 1], ![2, 4, 1, 0, 3], ![0, 1, 2, 3, 4], ![4, 0, 3, 1, 2], ![1, 3, 4, 2, 0]]⟩, ⟨![![4, 2, 1, 3, 0], ![2, 3, 0, 1, 4], ![1, 0, 2, 4, 3], ![3, 1, 4, 0, 2], ![0, 4, 3, 2, 1]]⟩, ⟨![![3, 0, 1, 2, 4], ![1, 4, 0, 3, 2], ![4, 3, 2, 0, 1], ![0, 2, 4, 1, 3], ![2, 1, 3, 4, 0]]⟩, ⟨![![4, 1, 0, 2, 3], ![0, 3, 1, 4, 2], ![3, 4, 2, 1, 0], ![1, 2, 3, 0, 4], ![2, 0, 4, 3, 1]]⟩, ⟨![![4, 4, 4, 4, 4], ![3, 3, 3, 3, 3], ![2, 2, 2, 2, 2], ![0, 0, 0, 0, 0], ![1, 1, 1, 1, 1]]⟩, ⟨![![3, 3, 3, 3, 3], ![4, 4, 4, 4, 4], ![2, 2, 2, 2, 2], ![1, 1, 1, 1, 1], ![0, 0, 0, 0, 0]]⟩, ⟨![![2, 3, 0, 1, 4], ![4, 2, 1, 3, 0], ![1, 0, 2, 4, 3], ![0, 4, 3, 2, 1], ![3, 1, 4, 0, 2]]⟩, ⟨![![2, 4, 1, 0, 3], ![3, 2, 0, 4, 1], ![0, 1, 2, 3, 4], ![1, 3, 4, 2, 0], ![4, 0, 3, 1, 2]]⟩, ⟨![![1, 0, 2, 4, 3], ![1, 0, 2, 4, 3], ![1, 0, 2, 4, 3], ![1, 0, 2, 4, 3], ![1, 0, 2, 4, 3]]⟩, ⟨![![0, 2, 4, 1, 3], ![2, 1, 3, 4, 0], ![4, 3, 2, 0, 1], ![1, 4, 0, 3, 2], ![3, 0, 1, 2, 4]]⟩, ⟨![![1, 2, 3, 0, 4], ![2, 0, 4, 3, 1], ![3, 4, 2, 1, 0], ![0, 3, 1, 4, 2], ![4, 1, 0, 2, 3]]⟩, ⟨![![0, 4, 3, 2, 1], ![3, 1, 4, 0, 2], ![1, 0, 2, 4, 3], ![4, 2, 1, 3, 0], ![2, 3, 0, 1, 4]]⟩, ⟨![![1, 3, 4, 2, 0], ![4, 0, 3, 1, 2], ![0, 1, 2, 3, 4], ![3, 2, 0, 4, 1], ![2, 4, 1, 0, 3]]⟩, ⟨![![4, 0, 3, 1, 2], ![1, 3, 4, 2, 0], ![0, 1, 2, 3, 4], ![2, 4, 1, 0, 3], ![3, 2, 0, 4, 1]]⟩, ⟨![![3, 1, 4, 0, 2], ![0, 4, 3, 2, 1], ![1, 0, 2, 4, 3], ![2, 3, 0, 1, 4], ![4, 2, 1, 3, 0]]⟩, ⟨![![0, 3, 1, 4, 2], ![4, 1, 0, 2, 3], ![3, 4, 2, 1, 0], ![2, 0, 4, 3, 1], ![1, 2, 3, 0, 4]]⟩, ⟨![![1, 4, 0, 3, 2], ![3, 0, 1, 2, 4], ![4, 3, 2, 0, 1], ![2, 1, 3, 4, 0], ![0, 2, 4, 1, 3]]⟩, ⟨![![1, 1, 1, 1, 1], ![0, 0, 0, 0, 0], ![2, 2, 2, 2, 2], ![4, 4, 4, 4, 4], ![3, 3, 3, 3, 3]]⟩]

/-- Where each composite of two members of `Magma.negCert10Clone` lands. -/
@[implicit_reducible]
def negCert10Comp : Fin 25 → Fin 25 → Fin 25 :=
  ![![2, 3, 12, 21, 7, 20, 18, 6, 22, 8, 1, 0, 11, 5, 9, 17, 13, 19, 4, 23, 16, 10, 14, 15, 24],
    ![4, 2, 5, 7, 9, 6, 1, 11, 18, 20, 16, 22, 10, 21, 12, 15, 14, 23, 13, 24, 0, 8, 3, 19, 17],
    ![11, 6, 2, 13, 14, 1, 15, 16, 17, 18, 19, 24, 0, 4, 3, 5, 8, 7, 10, 9, 23, 22, 20, 21, 12],
    ![20, 8, 14, 2, 4, 22, 24, 18, 23, 0, 17, 19, 1, 3, 13, 9, 11, 5, 6, 21, 15, 16, 10, 12, 7],
    ![8, 10, 13, 3, 2, 0, 23, 22, 19, 16, 24, 15, 18, 14, 4, 7, 6, 12, 20, 5, 17, 1, 11, 9, 21],
    ![21, 5, 15, 23, 24, 2, 6, 4, 20, 3, 11, 8, 13, 19, 17, 1, 9, 0, 7, 22, 10, 14, 12, 16, 18],
    ![19, 15, 1, 0, 22, 5, 2, 21, 3, 12, 4, 14, 7, 16, 18, 6, 24, 10, 23, 8, 13, 9, 17, 11, 20],
    ![5, 12, 17, 19, 23, 3, 20, 2, 8, 14, 6, 10, 4, 15, 24, 18, 7, 16, 21, 0, 11, 13, 9, 1, 22],
    ![23, 19, 16, 22, 18, 21, 4, 7, 2, 5, 13, 3, 9, 0, 1, 11, 17, 8, 24, 20, 14, 12, 15, 10, 6],
    ![7, 21, 19, 24, 17, 4, 11, 13, 6, 2, 10, 20, 14, 23, 15, 16, 12, 22, 9, 18, 8, 3, 5, 0, 1],
    ![15, 17, 18, 16, 0, 12, 3, 5, 14, 9, 2, 13, 21, 1, 22, 20, 23, 11, 19, 10, 4, 7, 24, 6, 8],
    ![24, 23, 0, 18, 1, 7, 13, 9, 4, 21, 14, 2, 12, 22, 16, 10, 15, 20, 17, 6, 3, 5, 19, 8, 11],
    ![12, 9, 24, 15, 19, 14, 8, 3, 10, 13, 20, 11, 2, 17, 23, 22, 21, 1, 5, 16, 6, 4, 7, 18, 0],
    ![6, 20, 3, 4, 13, 18, 17, 1, 24, 22, 15, 23, 16, 2, 14, 12, 10, 21, 11, 7, 19, 0, 8, 5, 9],
    ![10, 11, 4, 14, 3, 16, 19, 0, 15, 1, 23, 17, 22, 13, 2, 21, 20, 9, 8, 12, 24, 18, 6, 7, 5],
    ![16, 1, 6, 10, 8, 15, 5, 19, 12, 17, 21, 9, 23, 11, 20, 2, 22, 13, 0, 14, 7, 24, 18, 4, 3],
    ![14, 13, 7, 12, 5, 10, 0, 8, 16, 11, 22, 1, 20, 9, 21, 23, 2, 17, 3, 15, 18, 6, 4, 24, 19],
    ![18, 22, 8, 6, 11, 24, 9, 17, 7, 23, 12, 21, 15, 20, 10, 14, 16, 2, 1, 4, 5, 19, 0, 3, 13],
    ![3, 14, 9, 5, 21, 8, 22, 20, 0, 10, 18, 16, 6, 12, 7, 24, 4, 15, 2, 19, 1, 11, 13, 17, 23],
    ![22, 0, 10, 20, 6, 23, 7, 24, 21, 19, 9, 5, 17, 8, 11, 13, 1, 3, 18, 2, 12, 15, 16, 14, 4],
    ![17, 24, 22, 1, 16, 9, 14, 12, 13, 7, 3, 4, 5, 18, 0, 8, 19, 6, 15, 11, 2, 21, 23, 20, 10],
    ![9, 7, 23, 17, 15, 13, 10, 14, 11, 4, 8, 6, 3, 24, 19, 0, 5, 18, 12, 1, 20, 2, 21, 22, 16],
    ![13, 4, 21, 9, 12, 11, 16, 10, 1, 6, 0, 18, 8, 7, 5, 19, 3, 24, 14, 17, 22, 20, 2, 23, 15],
    ![1, 18, 20, 11, 10, 17, 12, 15, 9, 24, 5, 7, 19, 6, 8, 3, 0, 4, 16, 13, 21, 23, 22, 2, 14],
    ![0, 16, 11, 8, 20, 19, 21, 23, 5, 15, 7, 12, 24, 10, 6, 4, 18, 14, 22, 3, 9, 17, 1, 13, 2]]

theorem negCert10_isCloneFamily :
    negCert10.IsCloneFamily negCert10Clone 0 1 negCert10Comp :=
  ⟨by decideFin!, by decideFin!, by decideFin!⟩

/-- The affine magma `x ◇ y = 7 x + 7 y` on `Fin 13`. -/
@[implicit_reducible]
def negCert11 : Magma (Fin 13) := affineFin 13 7 7

/-- Since `7 + 7 = 1` the magma is idempotent, so every term of it is
`p x + (1 - p) y` and its clone has exactly `13` members, indexed here by
the coefficient `p` of `x`. -/
@[implicit_reducible]
def negCert11P : Fin 13 → ℕ := fun i ↦ i.val

@[implicit_reducible]
def negCert11Q : Fin 13 → ℕ := fun i ↦ (13 + 1 - i.val) % 13

/-- The `13` operations term-definable from `Magma.negCert11`. -/
@[implicit_reducible]
def negCert11Clone : Fin 13 → Magma (Fin 13) := fun i ↦ affineFin 13 (negCert11P i) (negCert11Q i)

/-- Coefficients compose affinely: `7 i + 7 j`. -/
@[implicit_reducible]
def negCert11Comp : Fin 13 → Fin 13 → Fin 13 := fun i j ↦ ⟨(7 * i.val + 7 * j.val) % 13, Nat.mod_lt _ (by omega)⟩

theorem negCert11_isCloneFamily :
    negCert11.IsCloneFamily negCert11Clone 1 0 negCert11Comp :=
  affineFin_isCloneFamily 13 7 7 negCert11P negCert11Q 1 0 negCert11Comp
    (by decide) (by decide) (by decide) (by decide) (by decide!)

/-- A magma on `Fin 5` whose binary clone has only `25` members. -/
@[implicit_reducible]
def negCert12 : Magma (Fin 5) := ⟨![![0, 1, 2, 3, 4], ![4, 2, 0, 1, 3], ![1, 4, 3, 0, 2], ![2, 3, 1, 4, 0], ![3, 0, 4, 2, 1]]⟩

/-- The `25` operations term-definable from `Magma.negCert12`. -/
@[implicit_reducible]
def negCert12Clone : Fin 25 → Magma (Fin 5) := ![⟨![![0, 0, 0, 0, 0], ![1, 1, 1, 1, 1], ![2, 2, 2, 2, 2], ![3, 3, 3, 3, 3], ![4, 4, 4, 4, 4]]⟩, ⟨![![0, 1, 2, 3, 4], ![0, 1, 2, 3, 4], ![0, 1, 2, 3, 4], ![0, 1, 2, 3, 4], ![0, 1, 2, 3, 4]]⟩, ⟨![![0, 0, 0, 0, 0], ![2, 2, 2, 2, 2], ![3, 3, 3, 3, 3], ![4, 4, 4, 4, 4], ![1, 1, 1, 1, 1]]⟩, ⟨![![0, 1, 2, 3, 4], ![4, 2, 0, 1, 3], ![1, 4, 3, 0, 2], ![2, 3, 1, 4, 0], ![3, 0, 4, 2, 1]]⟩, ⟨![![0, 4, 1, 2, 3], ![1, 2, 4, 3, 0], ![2, 0, 3, 1, 4], ![3, 1, 0, 4, 2], ![4, 3, 2, 0, 1]]⟩, ⟨![![0, 2, 3, 4, 1], ![0, 2, 3, 4, 1], ![0, 2, 3, 4, 1], ![0, 2, 3, 4, 1], ![0, 2, 3, 4, 1]]⟩, ⟨![![0, 4, 1, 2, 3], ![2, 0, 3, 1, 4], ![3, 1, 0, 4, 2], ![4, 3, 2, 0, 1], ![1, 2, 4, 3, 0]]⟩, ⟨![![0, 1, 2, 3, 4], ![1, 4, 3, 0, 2], ![2, 3, 1, 4, 0], ![3, 0, 4, 2, 1], ![4, 2, 0, 1, 3]]⟩, ⟨![![0, 2, 3, 4, 1], ![4, 0, 1, 3, 2], ![1, 3, 0, 2, 4], ![2, 1, 4, 0, 3], ![3, 4, 2, 1, 0]]⟩, ⟨![![0, 2, 3, 4, 1], ![3, 4, 2, 1, 0], ![4, 0, 1, 3, 2], ![1, 3, 0, 2, 4], ![2, 1, 4, 0, 3]]⟩, ⟨![![0, 3, 4, 1, 2], ![1, 0, 2, 4, 3], ![2, 4, 0, 3, 1], ![3, 2, 1, 0, 4], ![4, 1, 3, 2, 0]]⟩, ⟨![![0, 0, 0, 0, 0], ![4, 4, 4, 4, 4], ![1, 1, 1, 1, 1], ![2, 2, 2, 2, 2], ![3, 3, 3, 3, 3]]⟩, ⟨![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]⟩, ⟨![![0, 0, 0, 0, 0], ![3, 3, 3, 3, 3], ![4, 4, 4, 4, 4], ![1, 1, 1, 1, 1], ![2, 2, 2, 2, 2]]⟩, ⟨![![0, 1, 2, 3, 4], ![2, 3, 1, 4, 0], ![3, 0, 4, 2, 1], ![4, 2, 0, 1, 3], ![1, 4, 3, 0, 2]]⟩, ⟨![![0, 4, 1, 2, 3], ![4, 3, 2, 0, 1], ![1, 2, 4, 3, 0], ![2, 0, 3, 1, 4], ![3, 1, 0, 4, 2]]⟩, ⟨![![0, 3, 4, 1, 2], ![0, 3, 4, 1, 2], ![0, 3, 4, 1, 2], ![0, 3, 4, 1, 2], ![0, 3, 4, 1, 2]]⟩, ⟨![![0, 2, 3, 4, 1], ![1, 3, 0, 2, 4], ![2, 1, 4, 0, 3], ![3, 4, 2, 1, 0], ![4, 0, 1, 3, 2]]⟩, ⟨![![0, 4, 1, 2, 3], ![3, 1, 0, 4, 2], ![4, 3, 2, 0, 1], ![1, 2, 4, 3, 0], ![2, 0, 3, 1, 4]]⟩, ⟨![![0, 3, 4, 1, 2], ![3, 2, 1, 0, 4], ![4, 1, 3, 2, 0], ![1, 0, 2, 4, 3], ![2, 4, 0, 3, 1]]⟩, ⟨![![0, 4, 1, 2, 3], ![0, 4, 1, 2, 3], ![0, 4, 1, 2, 3], ![0, 4, 1, 2, 3], ![0, 4, 1, 2, 3]]⟩, ⟨![![0, 2, 3, 4, 1], ![2, 1, 4, 0, 3], ![3, 4, 2, 1, 0], ![4, 0, 1, 3, 2], ![1, 3, 0, 2, 4]]⟩, ⟨![![0, 3, 4, 1, 2], ![4, 1, 3, 2, 0], ![1, 0, 2, 4, 3], ![2, 4, 0, 3, 1], ![3, 2, 1, 0, 4]]⟩, ⟨![![0, 1, 2, 3, 4], ![3, 0, 4, 2, 1], ![4, 2, 0, 1, 3], ![1, 4, 3, 0, 2], ![2, 3, 1, 4, 0]]⟩, ⟨![![0, 3, 4, 1, 2], ![2, 4, 0, 3, 1], ![3, 2, 1, 0, 4], ![4, 1, 3, 2, 0], ![1, 0, 2, 4, 3]]⟩]

/-- Where each composite of two members of `Magma.negCert12Clone` lands. -/
@[implicit_reducible]
def negCert12Comp : Fin 25 → Fin 25 → Fin 25 :=
  ![![2, 3, 12, 23, 6, 8, 20, 14, 9, 17, 24, 13, 11, 0, 1, 18, 22, 21, 4, 10, 15, 5, 19, 7, 16],
    ![4, 5, 6, 8, 10, 12, 24, 17, 11, 13, 7, 15, 20, 18, 21, 22, 1, 0, 19, 23, 16, 2, 3, 9, 14],
    ![11, 7, 13, 14, 15, 17, 18, 3, 21, 5, 22, 2, 0, 12, 23, 6, 10, 8, 20, 16, 4, 9, 24, 1, 19],
    ![20, 9, 15, 17, 16, 13, 22, 5, 0, 2, 1, 4, 18, 6, 8, 10, 23, 12, 24, 14, 19, 11, 7, 21, 3],
    ![24, 11, 16, 13, 14, 15, 1, 2, 18, 4, 21, 19, 22, 10, 12, 23, 8, 6, 7, 17, 3, 20, 9, 0, 5],
    ![7, 20, 14, 15, 17, 16, 21, 4, 22, 19, 0, 3, 1, 23, 6, 8, 12, 10, 9, 13, 5, 24, 11, 18, 2],
    ![22, 0, 19, 2, 3, 4, 23, 11, 6, 20, 8, 24, 10, 16, 13, 14, 17, 15, 1, 5, 7, 18, 21, 12, 9],
    ![6, 8, 20, 9, 24, 11, 16, 21, 13, 0, 14, 18, 15, 4, 5, 19, 3, 2, 10, 7, 22, 12, 23, 17, 1],
    ![1, 18, 3, 4, 5, 19, 8, 20, 10, 24, 12, 7, 23, 14, 15, 17, 13, 16, 21, 2, 9, 22, 0, 6, 11],
    ![23, 6, 7, 20, 9, 24, 17, 18, 16, 22, 13, 1, 14, 3, 4, 5, 2, 19, 8, 11, 21, 10, 12, 15, 0],
    ![21, 22, 5, 19, 2, 3, 12, 24, 23, 7, 6, 9, 8, 17, 16, 13, 15, 14, 0, 4, 11, 1, 18, 10, 20],
    ![12, 23, 11, 7, 20, 9, 15, 1, 17, 21, 16, 0, 13, 2, 3, 4, 19, 5, 6, 24, 18, 8, 10, 14, 22],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24],
    ![13, 14, 0, 1, 18, 21, 4, 23, 5, 8, 19, 12, 2, 11, 7, 20, 24, 9, 15, 22, 6, 17, 16, 3, 10],
    ![15, 17, 18, 21, 22, 0, 19, 8, 2, 12, 3, 6, 4, 20, 9, 24, 7, 11, 16, 1, 10, 13, 14, 5, 23],
    ![16, 13, 22, 0, 1, 18, 3, 12, 4, 6, 5, 10, 19, 24, 11, 7, 9, 20, 14, 21, 23, 15, 17, 2, 8],
    ![17, 16, 21, 22, 0, 1, 2, 10, 3, 23, 4, 8, 5, 9, 24, 11, 20, 7, 13, 18, 12, 14, 15, 19, 6],
    ![14, 15, 1, 18, 21, 22, 5, 6, 19, 10, 2, 23, 3, 7, 20, 9, 11, 24, 17, 0, 8, 16, 13, 4, 12],
    ![19, 2, 10, 12, 23, 6, 7, 13, 20, 15, 9, 16, 24, 22, 0, 1, 21, 18, 3, 8, 14, 4, 5, 11, 17],
    ![9, 24, 17, 16, 13, 14, 0, 19, 1, 3, 18, 5, 21, 8, 10, 12, 6, 23, 11, 15, 2, 7, 20, 22, 4],
    ![10, 12, 24, 11, 7, 20, 14, 0, 15, 18, 17, 22, 16, 19, 2, 3, 5, 4, 23, 9, 1, 6, 8, 13, 21],
    ![3, 4, 23, 6, 8, 10, 9, 15, 24, 16, 11, 14, 7, 1, 18, 21, 0, 22, 5, 12, 17, 19, 2, 20, 13],
    ![5, 19, 8, 10, 12, 23, 11, 16, 7, 14, 20, 17, 9, 21, 22, 0, 18, 1, 2, 6, 13, 3, 4, 24, 15],
    ![18, 21, 4, 5, 19, 2, 10, 9, 12, 11, 23, 20, 6, 15, 17, 16, 14, 13, 22, 3, 24, 0, 1, 8, 7],
    ![8, 10, 9, 24, 11, 7, 13, 22, 14, 1, 15, 21, 17, 5, 19, 2, 4, 3, 12, 20, 0, 23, 6, 16, 18]]

theorem negCert12_isCloneFamily :
    negCert12.IsCloneFamily negCert12Clone 0 1 negCert12Comp :=
  ⟨by decideFin!, by decideFin!, by decideFin!⟩

/-- The affine magma `x ◇ y = 2 x + 3 y` over `GF(16)`. Since `2 + 3 = 1`
it is idempotent, so its clone is the `16` operations `p x + (1 - p) y`, indexed
here by the coefficient `p` of `x`. -/
@[implicit_reducible]
def negCert13 : Magma (Fin 16) := affineOf gf16add gf16 2 3

@[implicit_reducible]
def negCert13P : Fin 16 → Fin 16 := fun i ↦ i

@[implicit_reducible]
def negCert13Q : Fin 16 → Fin 16 := fun i ↦ gf16add 1 i

/-- The `16` operations term-definable from `Magma.negCert13`. -/
@[implicit_reducible]
def negCert13Clone : Fin 16 → Magma (Fin 16) := fun i ↦ affineOf gf16add gf16 (negCert13P i) (negCert13Q i)

/-- Coefficients compose affinely: `2 p + 3 p′`. -/
@[implicit_reducible]
def negCert13Comp : Fin 16 → Fin 16 → Fin 16 := fun i j ↦ gf16add (gf16 2 i) (gf16 3 j)

theorem negCert13_isCloneFamily :
    negCert13.IsCloneFamily negCert13Clone 1 0 negCert13Comp :=
  affineOf_isCloneFamily gf16add gf16 0 1 gf16add_assoc gf16add_comm
    gf16add_zero gf16_one gf16_zero gf16_assoc gf16_distrib gf16_distrib'
    2 3 negCert13P negCert13Q 1 0 negCert13Comp rfl (by decide) rfl (by decide) (by decide!)

/-- The affine magma `x ◇ y = 3 x + 11 y` on `Fin 13`. -/
@[implicit_reducible]
def negCert14 : Magma (Fin 13) := affineFin 13 3 11

/-- Since `3 + 11 = 1` the magma is idempotent, so every term of it is
`p x + (1 - p) y` and its clone has exactly `13` members, indexed here by
the coefficient `p` of `x`. -/
@[implicit_reducible]
def negCert14P : Fin 13 → ℕ := fun i ↦ i.val

@[implicit_reducible]
def negCert14Q : Fin 13 → ℕ := fun i ↦ (13 + 1 - i.val) % 13

/-- The `13` operations term-definable from `Magma.negCert14`. -/
@[implicit_reducible]
def negCert14Clone : Fin 13 → Magma (Fin 13) := fun i ↦ affineFin 13 (negCert14P i) (negCert14Q i)

/-- Coefficients compose affinely: `3 i + 11 j`. -/
@[implicit_reducible]
def negCert14Comp : Fin 13 → Fin 13 → Fin 13 := fun i j ↦ ⟨(3 * i.val + 11 * j.val) % 13, Nat.mod_lt _ (by omega)⟩

theorem negCert14_isCloneFamily :
    negCert14.IsCloneFamily negCert14Clone 1 0 negCert14Comp :=
  affineFin_isCloneFamily 13 3 11 negCert14P negCert14Q 1 0 negCert14Comp
    (by decide) (by decide) (by decide) (by decide) (by decide!)

/-- The affine magma `x ◇ y = 6 x + 8 y` on `Fin 13`. -/
@[implicit_reducible]
def negCert15 : Magma (Fin 13) := affineFin 13 6 8

/-- Since `6 + 8 = 1` the magma is idempotent, so every term of it is
`p x + (1 - p) y` and its clone has exactly `13` members, indexed here by
the coefficient `p` of `x`. -/
@[implicit_reducible]
def negCert15P : Fin 13 → ℕ := fun i ↦ i.val

@[implicit_reducible]
def negCert15Q : Fin 13 → ℕ := fun i ↦ (13 + 1 - i.val) % 13

/-- The `13` operations term-definable from `Magma.negCert15`. -/
@[implicit_reducible]
def negCert15Clone : Fin 13 → Magma (Fin 13) := fun i ↦ affineFin 13 (negCert15P i) (negCert15Q i)

/-- Coefficients compose affinely: `6 i + 8 j`. -/
@[implicit_reducible]
def negCert15Comp : Fin 13 → Fin 13 → Fin 13 := fun i j ↦ ⟨(6 * i.val + 8 * j.val) % 13, Nat.mod_lt _ (by omega)⟩

theorem negCert15_isCloneFamily :
    negCert15.IsCloneFamily negCert15Clone 1 0 negCert15Comp :=
  affineFin_isCloneFamily 13 6 8 negCert15P negCert15Q 1 0 negCert15Comp
    (by decide) (by decide) (by decide) (by decide) (by decide!)

/-- A magma on `Fin 5` whose binary clone has only `25` members. -/
@[implicit_reducible]
def negCert16 : Magma (Fin 5) := ⟨![![0, 2, 3, 4, 1], ![1, 3, 0, 2, 4], ![2, 1, 4, 0, 3], ![3, 4, 2, 1, 0], ![4, 0, 1, 3, 2]]⟩

/-- The `25` operations term-definable from `Magma.negCert16`. -/
@[implicit_reducible]
def negCert16Clone : Fin 25 → Magma (Fin 5) := ![⟨![![0, 0, 0, 0, 0], ![1, 1, 1, 1, 1], ![2, 2, 2, 2, 2], ![3, 3, 3, 3, 3], ![4, 4, 4, 4, 4]]⟩, ⟨![![0, 1, 2, 3, 4], ![0, 1, 2, 3, 4], ![0, 1, 2, 3, 4], ![0, 1, 2, 3, 4], ![0, 1, 2, 3, 4]]⟩, ⟨![![0, 0, 0, 0, 0], ![3, 3, 3, 3, 3], ![4, 4, 4, 4, 4], ![1, 1, 1, 1, 1], ![2, 2, 2, 2, 2]]⟩, ⟨![![0, 2, 3, 4, 1], ![1, 3, 0, 2, 4], ![2, 1, 4, 0, 3], ![3, 4, 2, 1, 0], ![4, 0, 1, 3, 2]]⟩, ⟨![![0, 1, 2, 3, 4], ![2, 3, 1, 4, 0], ![3, 0, 4, 2, 1], ![4, 2, 0, 1, 3], ![1, 4, 3, 0, 2]]⟩, ⟨![![0, 3, 4, 1, 2], ![0, 3, 4, 1, 2], ![0, 3, 4, 1, 2], ![0, 3, 4, 1, 2], ![0, 3, 4, 1, 2]]⟩, ⟨![![0, 1, 2, 3, 4], ![4, 2, 0, 1, 3], ![1, 4, 3, 0, 2], ![2, 3, 1, 4, 0], ![3, 0, 4, 2, 1]]⟩, ⟨![![0, 2, 3, 4, 1], ![3, 4, 2, 1, 0], ![4, 0, 1, 3, 2], ![1, 3, 0, 2, 4], ![2, 1, 4, 0, 3]]⟩, ⟨![![0, 0, 0, 0, 0], ![2, 2, 2, 2, 2], ![3, 3, 3, 3, 3], ![4, 4, 4, 4, 4], ![1, 1, 1, 1, 1]]⟩, ⟨![![0, 1, 2, 3, 4], ![1, 4, 3, 0, 2], ![2, 3, 1, 4, 0], ![3, 0, 4, 2, 1], ![4, 2, 0, 1, 3]]⟩, ⟨![![0, 3, 4, 1, 2], ![3, 2, 1, 0, 4], ![4, 1, 3, 2, 0], ![1, 0, 2, 4, 3], ![2, 4, 0, 3, 1]]⟩, ⟨![![0, 3, 4, 1, 2], ![2, 4, 0, 3, 1], ![3, 2, 1, 0, 4], ![4, 1, 3, 2, 0], ![1, 0, 2, 4, 3]]⟩, ⟨![![0, 0, 0, 0, 0], ![4, 4, 4, 4, 4], ![1, 1, 1, 1, 1], ![2, 2, 2, 2, 2], ![3, 3, 3, 3, 3]]⟩, ⟨![![0, 3, 4, 1, 2], ![4, 1, 3, 2, 0], ![1, 0, 2, 4, 3], ![2, 4, 0, 3, 1], ![3, 2, 1, 0, 4]]⟩, ⟨![![0, 2, 3, 4, 1], ![2, 1, 4, 0, 3], ![3, 4, 2, 1, 0], ![4, 0, 1, 3, 2], ![1, 3, 0, 2, 4]]⟩, ⟨![![0, 4, 1, 2, 3], ![3, 1, 0, 4, 2], ![4, 3, 2, 0, 1], ![1, 2, 4, 3, 0], ![2, 0, 3, 1, 4]]⟩, ⟨![![0, 2, 3, 4, 1], ![0, 2, 3, 4, 1], ![0, 2, 3, 4, 1], ![0, 2, 3, 4, 1], ![0, 2, 3, 4, 1]]⟩, ⟨![![0, 1, 2, 3, 4], ![3, 0, 4, 2, 1], ![4, 2, 0, 1, 3], ![1, 4, 3, 0, 2], ![2, 3, 1, 4, 0]]⟩, ⟨![![0, 3, 4, 1, 2], ![1, 0, 2, 4, 3], ![2, 4, 0, 3, 1], ![3, 2, 1, 0, 4], ![4, 1, 3, 2, 0]]⟩, ⟨![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]⟩, ⟨![![0, 2, 3, 4, 1], ![4, 0, 1, 3, 2], ![1, 3, 0, 2, 4], ![2, 1, 4, 0, 3], ![3, 4, 2, 1, 0]]⟩, ⟨![![0, 4, 1, 2, 3], ![1, 2, 4, 3, 0], ![2, 0, 3, 1, 4], ![3, 1, 0, 4, 2], ![4, 3, 2, 0, 1]]⟩, ⟨![![0, 4, 1, 2, 3], ![2, 0, 3, 1, 4], ![3, 1, 0, 4, 2], ![4, 3, 2, 0, 1], ![1, 2, 4, 3, 0]]⟩, ⟨![![0, 4, 1, 2, 3], ![4, 3, 2, 0, 1], ![1, 2, 4, 3, 0], ![2, 0, 3, 1, 4], ![3, 1, 0, 4, 2]]⟩, ⟨![![0, 4, 1, 2, 3], ![0, 4, 1, 2, 3], ![0, 4, 1, 2, 3], ![0, 4, 1, 2, 3], ![0, 4, 1, 2, 3]]⟩]

/-- Where each composite of two members of `Magma.negCert16Clone` lands. -/
@[implicit_reducible]
def negCert16Comp : Fin 25 → Fin 25 → Fin 25 :=
  ![![2, 3, 8, 10, 16, 21, 20, 11, 19, 7, 22, 24, 12, 23, 5, 4, 18, 14, 15, 0, 13, 17, 1, 6, 9],
    ![4, 5, 6, 8, 10, 16, 18, 12, 17, 11, 20, 7, 9, 3, 2, 23, 19, 13, 14, 1, 0, 22, 15, 21, 24],
    ![12, 7, 0, 13, 14, 15, 16, 18, 8, 20, 21, 22, 19, 24, 11, 9, 10, 3, 23, 2, 5, 6, 4, 1, 17],
    ![7, 9, 14, 15, 1, 0, 6, 22, 16, 17, 8, 19, 20, 12, 24, 11, 21, 4, 2, 3, 23, 10, 5, 13, 18],
    ![9, 11, 1, 0, 13, 14, 10, 19, 6, 18, 16, 20, 17, 7, 12, 24, 8, 5, 3, 4, 2, 21, 23, 15, 22],
    ![11, 24, 13, 14, 15, 1, 21, 20, 10, 22, 6, 17, 18, 9, 7, 12, 16, 23, 4, 5, 3, 8, 2, 0, 19],
    ![1, 13, 17, 19, 18, 20, 11, 2, 9, 5, 7, 3, 4, 14, 0, 15, 12, 10, 16, 6, 8, 24, 21, 22, 23],
    ![20, 17, 3, 23, 4, 2, 1, 21, 14, 6, 0, 8, 16, 19, 22, 18, 15, 9, 12, 7, 24, 13, 11, 5, 10],
    ![0, 14, 19, 18, 20, 22, 7, 5, 12, 3, 24, 23, 2, 15, 13, 1, 11, 16, 21, 8, 10, 9, 6, 17, 4],
    ![17, 18, 4, 2, 5, 3, 13, 8, 1, 10, 14, 16, 6, 20, 19, 22, 0, 11, 7, 9, 12, 15, 24, 23, 21],
    ![13, 15, 18, 20, 22, 17, 24, 3, 11, 23, 9, 4, 5, 1, 14, 0, 7, 21, 6, 10, 16, 12, 8, 19, 2],
    ![18, 22, 5, 3, 23, 4, 15, 16, 13, 21, 1, 6, 10, 17, 20, 19, 14, 24, 9, 11, 7, 0, 12, 2, 8],
    ![19, 20, 2, 5, 3, 23, 14, 10, 0, 16, 15, 21, 8, 22, 18, 17, 13, 7, 24, 12, 11, 1, 9, 4, 6],
    ![5, 23, 10, 16, 21, 6, 22, 7, 18, 24, 17, 9, 11, 4, 3, 2, 20, 15, 1, 13, 14, 19, 0, 8, 12],
    ![3, 4, 16, 21, 6, 8, 17, 24, 20, 9, 19, 12, 7, 2, 23, 5, 22, 1, 0, 14, 15, 18, 13, 10, 11],
    ![23, 2, 21, 6, 8, 10, 19, 9, 22, 12, 18, 11, 24, 5, 4, 3, 17, 0, 13, 15, 1, 20, 14, 16, 7],
    ![14, 1, 20, 22, 17, 19, 9, 23, 7, 4, 12, 2, 3, 0, 15, 13, 24, 6, 8, 16, 21, 11, 10, 18, 5],
    ![6, 10, 9, 12, 11, 7, 5, 0, 4, 13, 3, 14, 1, 16, 8, 21, 2, 18, 20, 17, 19, 23, 22, 24, 15],
    ![10, 21, 11, 7, 24, 9, 23, 14, 5, 15, 4, 1, 13, 6, 16, 8, 3, 22, 17, 18, 20, 2, 19, 12, 0],
    ![8, 16, 12, 11, 7, 24, 3, 13, 2, 14, 23, 15, 0, 21, 10, 6, 5, 20, 22, 19, 18, 4, 17, 9, 1],
    ![16, 6, 7, 24, 9, 12, 4, 15, 3, 1, 2, 0, 14, 8, 21, 10, 23, 17, 19, 20, 22, 5, 18, 11, 13],
    ![15, 0, 22, 17, 19, 18, 12, 4, 24, 2, 11, 5, 23, 13, 1, 14, 9, 8, 10, 21, 6, 7, 16, 20, 3],
    ![21, 8, 24, 9, 12, 11, 2, 1, 23, 0, 5, 13, 15, 10, 6, 16, 4, 19, 18, 22, 17, 3, 20, 7, 14],
    ![24, 12, 15, 1, 0, 13, 8, 17, 21, 19, 10, 18, 22, 11, 9, 7, 6, 2, 5, 23, 4, 16, 3, 14, 20],
    ![22, 19, 23, 4, 2, 5, 0, 6, 15, 8, 13, 10, 21, 18, 17, 20, 1, 12, 11, 24, 9, 14, 7, 3, 16]]

theorem negCert16_isCloneFamily :
    negCert16.IsCloneFamily negCert16Clone 0 1 negCert16Comp :=
  ⟨by decideFin!, by decideFin!, by decideFin!⟩

/-- A magma on `Fin 4` whose binary clone has only `16` members. -/
@[implicit_reducible]
def negCert17 : Magma (Fin 4) := ⟨![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 1, 0], ![3, 2, 0, 1]]⟩

/-- The `16` operations term-definable from `Magma.negCert17`. -/
@[implicit_reducible]
def negCert17Clone : Fin 16 → Magma (Fin 4) := ![⟨![![0, 0, 0, 0], ![1, 1, 1, 1], ![2, 2, 2, 2], ![3, 3, 3, 3]]⟩, ⟨![![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]⟩, ⟨![![0, 0, 0, 0], ![0, 0, 0, 0], ![1, 1, 1, 1], ![1, 1, 1, 1]]⟩, ⟨![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 1, 0], ![3, 2, 0, 1]]⟩, ⟨![![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1], ![0, 0, 1, 1]]⟩, ⟨![![0, 1, 2, 3], ![0, 1, 2, 3], ![1, 0, 3, 2], ![1, 0, 3, 2]]⟩, ⟨![![0, 0, 1, 1], ![1, 1, 0, 0], ![2, 2, 3, 3], ![3, 3, 2, 2]]⟩, ⟨![![0, 0, 0, 0], ![1, 1, 1, 1], ![3, 3, 3, 3], ![2, 2, 2, 2]]⟩, ⟨![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]⟩, ⟨![![0, 1, 2, 3], ![1, 0, 3, 2], ![3, 2, 0, 1], ![2, 3, 1, 0]]⟩, ⟨![![0, 0, 1, 1], ![0, 0, 1, 1], ![1, 1, 0, 0], ![1, 1, 0, 0]]⟩, ⟨![![0, 0, 1, 1], ![1, 1, 0, 0], ![3, 3, 2, 2], ![2, 2, 3, 3]]⟩, ⟨![![0, 1, 3, 2], ![1, 0, 2, 3], ![2, 3, 0, 1], ![3, 2, 1, 0]]⟩, ⟨![![0, 1, 3, 2], ![0, 1, 3, 2], ![1, 0, 2, 3], ![1, 0, 2, 3]]⟩, ⟨![![0, 1, 3, 2], ![1, 0, 2, 3], ![3, 2, 1, 0], ![2, 3, 0, 1]]⟩, ⟨![![0, 1, 3, 2], ![0, 1, 3, 2], ![0, 1, 3, 2], ![0, 1, 3, 2]]⟩]

/-- Where each composite of two members of `Magma.negCert17Clone` lands. -/
@[implicit_reducible]
def negCert17Comp : Fin 16 → Fin 16 → Fin 16 :=
  ![![2, 3, 7, 5, 6, 9, 10, 8, 0, 1, 11, 4, 13, 14, 15, 12],
    ![3, 4, 5, 6, 15, 10, 12, 9, 1, 11, 13, 14, 0, 2, 7, 8],
    ![7, 5, 8, 9, 10, 1, 11, 0, 2, 3, 4, 6, 14, 15, 12, 13],
    ![5, 6, 9, 10, 12, 11, 13, 1, 3, 4, 14, 15, 2, 7, 8, 0],
    ![6, 15, 10, 12, 8, 13, 0, 11, 4, 14, 2, 7, 3, 5, 9, 1],
    ![9, 10, 1, 11, 13, 4, 14, 3, 5, 6, 15, 12, 7, 8, 0, 2],
    ![10, 12, 11, 13, 0, 14, 2, 4, 6, 15, 7, 8, 5, 9, 1, 3],
    ![8, 9, 0, 1, 11, 3, 4, 2, 7, 5, 6, 10, 15, 12, 13, 14],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![1, 11, 3, 4, 14, 6, 15, 5, 9, 10, 12, 13, 8, 0, 2, 7],
    ![11, 13, 4, 14, 2, 15, 7, 6, 10, 12, 8, 0, 9, 1, 3, 5],
    ![4, 14, 6, 15, 7, 12, 8, 10, 11, 13, 0, 2, 1, 3, 5, 9],
    ![13, 0, 14, 2, 3, 7, 5, 15, 12, 8, 9, 1, 10, 11, 4, 6],
    ![14, 2, 15, 7, 5, 8, 9, 12, 13, 0, 1, 3, 11, 4, 6, 10],
    ![15, 7, 12, 8, 9, 0, 1, 13, 14, 2, 3, 5, 4, 6, 10, 11],
    ![12, 8, 13, 0, 1, 2, 3, 14, 15, 7, 5, 9, 6, 10, 11, 4]]

theorem negCert17_isCloneFamily :
    negCert17.IsCloneFamily negCert17Clone 0 1 negCert17Comp :=
  ⟨by decideFin!, by decideFin!, by decideFin!⟩

/-- The affine magma `x ◇ y = 3 x + 15 y` on `Fin 17`. -/
@[implicit_reducible]
def negCert18 : Magma (Fin 17) := affineFin 17 3 15

/-- Since `3 + 15 = 1` the magma is idempotent, so every term of it is
`p x + (1 - p) y` and its clone has exactly `17` members, indexed here by
the coefficient `p` of `x`. -/
@[implicit_reducible]
def negCert18P : Fin 17 → ℕ := fun i ↦ i.val

@[implicit_reducible]
def negCert18Q : Fin 17 → ℕ := fun i ↦ (17 + 1 - i.val) % 17

/-- The `17` operations term-definable from `Magma.negCert18`. -/
@[implicit_reducible]
def negCert18Clone : Fin 17 → Magma (Fin 17) := fun i ↦ affineFin 17 (negCert18P i) (negCert18Q i)

/-- Coefficients compose affinely: `3 i + 15 j`. -/
@[implicit_reducible]
def negCert18Comp : Fin 17 → Fin 17 → Fin 17 := fun i j ↦ ⟨(3 * i.val + 15 * j.val) % 17, Nat.mod_lt _ (by omega)⟩

theorem negCert18_isCloneFamily :
    negCert18.IsCloneFamily negCert18Clone 1 0 negCert18Comp :=
  affineFin_isCloneFamily 17 3 15 negCert18P negCert18Q 1 0 negCert18Comp
    (by decide) (by decide) (by decide) (by decide) (by decide!)

/-- The affine magma `x ◇ y = 2 x + 2 y` on `Fin 9`. -/
@[implicit_reducible]
def negCert19 : Magma (Fin 9) := affineFin 9 2 2

/-- The `27` coefficient pairs of the clone. -/
@[implicit_reducible]
def negCert19P : Fin 27 → ℕ := ![5, 8, 2, 4, 3, 6, 0, 3, 1, 6, 8, 2, 2, 0, 1, 7, 4, 8, 0, 7, 4, 5, 3, 1, 6, 7, 5]

@[implicit_reducible]
def negCert19Q : Fin 27 → ℕ := ![8, 8, 8, 0, 4, 4, 1, 7, 6, 7, 5, 2, 5, 4, 0, 6, 3, 2, 7, 3, 6, 2, 1, 3, 1, 0, 5]

/-- The `27` operations term-definable from `Magma.negCert19`. -/
@[implicit_reducible]
def negCert19Clone : Fin 27 → Magma (Fin 9) := fun i ↦ affineFin 9 (negCert19P i) (negCert19Q i)

/-- Coefficients compose affinely: `(2 p + 2 p′, 2 q + 2 q′)`. -/
@[implicit_reducible]
def negCert19Comp : Fin 27 → Fin 27 → Fin 27 :=
  ![![12, 10, 26, 18, 15, 20, 14, 19, 22, 16, 1, 21, 0, 8, 7, 24, 13, 17, 23, 5, 6, 11, 25, 4, 3, 9, 2],
    ![10, 26, 12, 9, 20, 8, 25, 16, 6, 23, 0, 11, 2, 15, 18, 22, 5, 21, 19, 4, 24, 17, 3, 13, 14, 7, 1],
    ![26, 12, 10, 7, 8, 15, 3, 23, 24, 19, 2, 17, 1, 20, 9, 6, 4, 11, 16, 13, 22, 21, 14, 5, 25, 18, 0],
    ![18, 9, 7, 25, 0, 2, 17, 26, 23, 12, 24, 4, 22, 1, 14, 16, 15, 5, 10, 20, 19, 13, 21, 8, 11, 3, 6],
    ![15, 20, 8, 0, 7, 18, 24, 4, 17, 13, 3, 23, 14, 9, 1, 11, 26, 16, 5, 12, 21, 19, 22, 10, 6, 2, 25],
    ![20, 8, 15, 2, 18, 9, 22, 13, 21, 5, 14, 19, 25, 7, 0, 17, 12, 23, 4, 10, 11, 16, 6, 26, 24, 1, 3],
    ![14, 25, 3, 17, 24, 22, 13, 9, 12, 7, 19, 20, 16, 6, 11, 26, 1, 15, 18, 0, 10, 8, 5, 2, 4, 21, 23],
    ![19, 16, 23, 26, 4, 13, 9, 22, 1, 6, 20, 14, 8, 5, 10, 2, 21, 3, 24, 11, 0, 25, 7, 17, 18, 12, 15],
    ![22, 6, 24, 23, 17, 21, 12, 1, 20, 0, 13, 9, 5, 11, 16, 15, 14, 18, 2, 25, 8, 7, 10, 3, 26, 19, 4],
    ![16, 23, 19, 12, 13, 5, 7, 6, 0, 24, 8, 25, 15, 4, 26, 1, 11, 14, 22, 17, 2, 3, 18, 21, 9, 10, 20],
    ![1, 0, 2, 24, 3, 14, 19, 20, 13, 8, 21, 12, 11, 25, 6, 4, 9, 26, 15, 7, 5, 10, 16, 18, 23, 22, 17],
    ![21, 11, 17, 4, 23, 19, 20, 14, 9, 25, 12, 1, 10, 16, 5, 18, 22, 2, 3, 6, 7, 0, 8, 24, 15, 13, 26],
    ![0, 2, 1, 22, 14, 25, 16, 8, 5, 15, 11, 10, 17, 3, 24, 13, 7, 12, 20, 18, 4, 26, 23, 9, 19, 6, 21],
    ![8, 15, 20, 1, 9, 7, 6, 5, 11, 4, 25, 16, 3, 18, 2, 21, 10, 19, 13, 26, 17, 23, 24, 12, 22, 0, 14],
    ![7, 18, 9, 14, 1, 0, 11, 10, 16, 26, 6, 5, 24, 2, 3, 19, 8, 13, 12, 15, 23, 4, 17, 20, 21, 25, 22],
    ![24, 22, 6, 16, 11, 17, 26, 2, 15, 1, 4, 18, 13, 21, 19, 8, 3, 7, 0, 14, 20, 9, 12, 25, 10, 23, 5],
    ![13, 5, 4, 15, 26, 12, 1, 21, 14, 11, 9, 22, 7, 10, 8, 3, 19, 24, 17, 16, 25, 6, 0, 23, 2, 20, 18],
    ![17, 21, 11, 5, 16, 23, 15, 3, 18, 14, 26, 2, 12, 19, 13, 7, 24, 0, 25, 22, 9, 1, 20, 6, 8, 4, 10],
    ![23, 19, 16, 10, 5, 4, 18, 24, 2, 22, 15, 3, 20, 13, 12, 0, 17, 25, 6, 21, 1, 14, 9, 11, 7, 26, 8],
    ![5, 4, 13, 20, 12, 10, 0, 11, 25, 17, 7, 6, 18, 26, 15, 14, 16, 22, 21, 23, 3, 24, 2, 19, 1, 8, 9],
    ![6, 24, 22, 19, 21, 11, 10, 0, 8, 2, 5, 7, 4, 17, 23, 20, 25, 9, 1, 3, 15, 18, 26, 14, 12, 16, 13],
    ![11, 17, 21, 13, 19, 16, 8, 25, 7, 3, 10, 0, 26, 23, 4, 9, 6, 1, 14, 24, 18, 2, 15, 22, 20, 5, 12],
    ![25, 3, 14, 21, 22, 6, 5, 7, 10, 18, 16, 8, 23, 24, 17, 12, 0, 20, 9, 2, 26, 15, 4, 1, 13, 11, 19],
    ![4, 13, 5, 8, 10, 26, 2, 17, 3, 21, 18, 24, 9, 12, 20, 25, 23, 6, 11, 19, 14, 22, 1, 16, 0, 15, 7],
    ![3, 14, 25, 11, 6, 24, 4, 18, 26, 9, 23, 15, 19, 22, 21, 10, 2, 8, 7, 1, 12, 20, 13, 0, 5, 17, 16],
    ![9, 7, 18, 3, 2, 1, 21, 12, 19, 10, 22, 13, 6, 0, 25, 23, 20, 4, 26, 8, 16, 5, 11, 15, 17, 14, 24],
    ![2, 1, 0, 6, 25, 3, 23, 15, 4, 20, 17, 26, 21, 14, 22, 5, 18, 10, 8, 9, 13, 12, 19, 7, 16, 24, 11]]

theorem negCert19_isCloneFamily :
    negCert19.IsCloneFamily negCert19Clone 14 6 negCert19Comp :=
  affineFin_isCloneFamily 9 2 2 negCert19P negCert19Q 14 6 negCert19Comp
    (by decide) (by decide) (by decide) (by decide) (by decide!)

/-- The affine magma `x ◇ y = 1 x + 2 y` on `Fin 7`. -/
@[implicit_reducible]
def negCert20 : Magma (Fin 7) := affineFin 7 1 2

/-- The clone is all `7 * 7` affine operations, indexed here by
`7 p + q` for the coefficient pair `(p, q)`. -/
@[implicit_reducible]
def negCert20P : Fin 49 → ℕ := fun i ↦ i.val / 7

@[implicit_reducible]
def negCert20Q : Fin 49 → ℕ := fun i ↦ i.val % 7

/-- The `49` operations term-definable from `Magma.negCert20`. -/
@[implicit_reducible]
def negCert20Clone : Fin 49 → Magma (Fin 7) := fun i ↦ affineFin 7 (negCert20P i) (negCert20Q i)

/-- Coefficients compose affinely: `(1 p + 2 p′, 1 q + 2 q′)`. -/
@[implicit_reducible]
def negCert20Comp : Fin 49 → Fin 49 → Fin 49 := fun i j ↦ ⟨(7 * ((1 * (i.val / 7) + 2 * (j.val / 7)) % 7) + (1 * (i.val % 7) + 2 * (j.val % 7)) % 7) % 49, Nat.mod_lt _ (by omega)⟩

theorem negCert20_isCloneFamily :
    negCert20.IsCloneFamily negCert20Clone 7 1 negCert20Comp :=
  affineFin_isCloneFamily 7 1 2 negCert20P negCert20Q 7 1 negCert20Comp
    (by decide) (by decide) (by decide) (by decide) (by decide!)

end Magma

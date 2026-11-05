import equational_theories.Parastrophes.Equation1518TermDepth

/-!
# A depth-six obstruction to finite uniform division for E1518

Extend the 45-element depth-five example by two copies of F3. The 2025
base offsets are encoded as digits 0,...,8, one for each pair of ternary
coordinates. Checking their linear cocycle equations proves the law for
all 405 elements. The layer certificate then rules out EVERY unary term
of depth at most five at the distinguished point; an explicit depth-six
term reaches its square root. This is still only a finite lower bound.

The offsets were found by solving the universal additive cocycle equations
on the 45-element base (85 free coordinates), then projecting to two
coordinates while preserving the obstruction. Neither that search nor
its linear algebra is trusted: Lean checks the retained offsets and layers.
-/
namespace Parastrophes.Eq1518TermDepthSix
open FreeMagma Eq1518SquareCycles
open Eq1518Uniform (termDepth)

abbrev Base := Fin 15 × ZMod 3
abbrev Carrier := Base × (ZMod 3 × ZMod 3)

def baseIndex (x : Base) : Fin 45 :=
  ⟨Eq1518TermDepth.index x, by
    have hx := x.1.isLt
    have hu := x.2.val_lt
    dsimp [Eq1518TermDepth.index]
    omega⟩

/-- Four bits per pair of ternary offsets; no multiplication table is stored. -/
def masks : Fin 45 → ℕ := ![
  103488229326385320648669590529961817769084731119708689,
  193306480855202863032238123987978786606611110821430928,
  13670256043969353052448643560107181735656108340613714,
  103419351551096085389890810227003999373858470728083985,
  193190469714092048823408584906319277102404823389607568,
  13577807344494395614571937723409936111938878856790610,
  970162532200218636729548289538125894643507010893554948,
  964596975564472671379129770545973930285892225745326497,
  957839034830395369665968413234883045607015292985182824,
  862034771290605195430078842754470326062511670243775066,
  772286741273240253017109534408644295240610820850225769,
  969811678898701459184289290234378375558056838821192264,
  862241538884332199432315928607186053542592945482530970,
  772470150965219661041314418750046969688392249072062873,
  969971794629662293608981641423650913065978488547877033,
  804562646021082034147071314302595687551211152347637024,
  995329420395560974676720720768339527795267875719762200,
  899946135928127381703736437824992127793349721522739460,
  874878482869741491974034285460614824001880361352335400,
  964696460432137558461023963476264841836473700019635554,
  767101299212028320132625444109818519235052192422733958,
  874773083571452690658831505166557568332474782306025538,
  964544407253476322704698213860927287848027359484945797,
  767043033345038370942829203011214545903204575009638425,
  638036537852602578138663934972627983229179882912351237,
  632401098883881924407026188590830343045027791029031584,
  625713108925234861867482756294035537061243623671236954,
  223507835138135138359736437633405103435200488529877017,
  133689859648026242291422894869383506730203736356962370,
  25913019739275207442880098417458874798878436188247429,
  223481144223637409525981828793945321592410867245787173,
  133710098845437810080621571781188338213707234723404326,
  25909622443753542816286547670754353696018876645591332,
  390854735173480372194361297151758571546751460638788134,
  582743938521728139139332917248728314856747071068772644,
  487360380099195808319394413972498290051760216715110437,
  157892429651054286029269389790833512803991866879004809,
  157892429651054285606746232933101250416648420136604946,
  157892429652261517319003657954420015734494157361943208,
  157892429643268860344380767326636141909993347126263961,
  157892429650700627237842317156482463201377782857859225,
  157892429645979572568172563599256908083088198497019989,
  157892429657247658689081061158289783707468452711796838,
  157892429657250186880729054397342250016366559863251046,
  157892429652346934461419359182545559425751696847503957]

def offset (x y : Base) : ZMod 3 × ZMod 3 :=
  let c := (masks (baseIndex x) >>> (4 * (baseIndex y).val)) % 16
  ((c % 4 : ℕ), (c / 4 : ℕ))

theorem offset_condition : ∀ x y : Base,
    offset y x + offset x (Eq1518TermDepth.model.op y x) +
      offset (Eq1518TermDepth.model.op y y)
        (Eq1518TermDepth.model.op x (Eq1518TermDepth.model.op y x)) = 0 := by
  intro ⟨i,u⟩
  fin_cases i <;> revert u <;> decide +kernel

@[implicit_reducible] def model : Magma Carrier :=
  extension Eq1518TermDepth.model offset

theorem model_law : @Equation1518 Carrier model :=
  extension_law Eq1518TermDepth.model Eq1518TermDepth.model_law offset offset_condition

def index (x : Carrier) : ℕ :=
  9 * Eq1518TermDepth.index x.1 + x.2.1.val + 3 * x.2.2.val

def point (n : ℕ) : Carrier :=
  (Eq1518TermDepth.point (n / 9), (n, (n / 3 : ℕ)))

theorem point_index (x : Carrier) : point (index x) = x := by
  have hu := x.2.1.val_lt
  have hv := x.2.2.val_lt
  apply Prod.ext
  · have hq : index x / 9 = Eq1518TermDepth.index x.1 := by
      dsimp [index]
      omega
    change Eq1518TermDepth.point (index x / 9) = x.1
    rw [hq, Eq1518TermDepth.point_index]
  · apply Prod.ext
    · apply ZMod.val_injective
      change (index x : ZMod 3).val = x.2.1.val
      rw [ZMod.val_natCast]
      dsimp [index]
      omega
    · apply ZMod.val_injective
      change ((index x / 3 : ℕ) : ZMod 3).val = x.2.2.val
      rw [ZMod.val_natCast]
      dsimp [index]
      omega

/-- Only the first four depths need closure tables. At depth five, it
suffices to check that no product of two depth-four values is the root. -/
def balls : Fin 5 → List ℕ := ![
    [0],
    [0,28],
    [0,28,60,324],
    [0,28,60,87,115,170,192,246,302,324,353,356],
    [0,3,7,9,28,29,30,31,32,33,35,38,39,56,57,60,62,87,89,92,100,102,110,114,115,116,122,127,130,135,138,141,145,154,165,166,169,170,176,183,189,192,194,205,206,210,211,212,213,214,215,221,235,238,241,243,246,249,257,265,266,270,273,274,279,280,281,284,285,286,287,302,304,310,312,313,324,325,338,340,350,352,353,356,379,382,384,385,386,389,391,401,404]
  ]

theorem ball_base : ∀ n : Fin 5, index ((0,0),(0,0)) ∈ balls n := by decide

theorem ball_step_data : ∀ n : Fin 4,
    (balls n.castSucc).all (fun a => (balls n.castSucc).all (fun b =>
      (balls n.succ).contains (index (model.op (point a) (point b))))) = true := by
  decide +kernel

theorem ball_step (n : Fin 4) (x y : Carrier)
    (hx : index x ∈ balls n.castSucc) (hy : index y ∈ balls n.castSucc) :
    index (model.op x y) ∈ balls n.succ := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp (ball_step_data n) _ hx) _ hy
  simpa only [point_index] using List.contains_iff_mem.mp h

theorem no_pair_data :
    (balls 4).all (fun a => (balls 4).all (fun b =>
      decide (index (model.op (point a) (point b)) ≠ 320))) = true := by
  decide +kernel

theorem no_pair (x y : Carrier)
    (hx : index x ∈ balls 4) (hy : index y ∈ balls 4) :
    index (model.op x y) ≠ 320 := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp no_pair_data _ hx) _ hy
  simpa only [point_index, decide_eq_true_eq] using h

theorem eval_mem (t : FreeMagma (Fin 2)) (n : Fin 5) (ht : termDepth t ≤ n.val) :
    index (@evalInMagma _ _ model (fun _ => ((0,0),(0,0))) t) ∈ balls n := by
  induction t generalizing n with
  | Leaf i => exact ball_base n
  | Fork t u ihT ihU =>
    have hn : 0 < n.val := by simp only [termDepth] at ht; omega
    let k : Fin 4 := ⟨n.val-1, by omega⟩
    have hkn : k.succ = n := by apply Fin.ext; simp only [Fin.val_succ]; dsimp [k]; omega
    rw [← hkn]
    apply ball_step k
    · exact ihT k.castSucc (by simp only [termDepth] at ht; dsimp [k]; omega)
    · exact ihU k.castSucc (by simp only [termDepth] at ht; dsimp [k]; omega)

theorem eval_ne_root (t : FreeMagma (Fin 2)) (ht : termDepth t ≤ 5) :
    @evalInMagma _ _ model (fun _ => ((0,0),(0,0))) t ≠ point 320 := by
  cases t with
  | Leaf i =>
    change ((0,0),(0,0)) ≠ point 320
    decide
  | Fork t u =>
    have ht' : termDepth t ≤ 4 := by simp only [termDepth] at ht; omega
    have hu' : termDepth u ≤ 4 := by simp only [termDepth] at ht; omega
    have hn := no_pair _ _ (eval_mem t 4 ht') (eval_mem u 4 hu')
    intro he
    apply hn
    have hi := congrArg index he
    simpa only [evalInMagma] using hi

theorem root_square : model.op (point 320) (point 320) = ((0,0),(0,0)) := by
  decide +kernel

theorem no_shallow_squareRoot (t : FreeMagma (Fin 2)) (ht : termDepth t ≤ 5) :
    ¬ Eq1518Uniform.SquareRootWitness t := by
  intro h
  have hm := h _ model inferInstance model_law ((0,0),(0,0))
  have hi := (Catalogue.square_bijective1518 model model_law).1
  have he := hi (hm.trans root_square.symm)
  apply eval_ne_root t ht
  simpa only [termMagma, Magma.op, ite_self] using he

/-- An unrestricted positive answer would require a term of depth at least six. -/
theorem division_depth_lower_bound (t : FreeMagma (Fin 2))
    (h : UniformTermWitness .fin Law1518 .left t) : 6 ≤ termDepth t := by
  by_contra hn
  exact no_shallow_squareRoot t (by omega) (Eq1518Uniform.root_of_division h)

def attainingTerm : FreeMagma (Fin 2) := (Lf 0 ⋆ (((Lf 0 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ Lf 0) ⋆ ((((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0)) ⋆ Lf 0) ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 0)))))

theorem attaining_depth : termDepth attainingTerm = 6 := by decide

theorem attaining_root :
    let x := (termMagma model attainingTerm).op ((0,0),(0,0)) ((0,0),(0,0))
    model.op x x = ((0,0),(0,0)) := by decide +kernel

end Parastrophes.Eq1518TermDepthSix

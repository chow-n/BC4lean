import BC4lean.KasparovFiniteAveraging

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Eigenspace splitting for a central involution

For an involution `g` over trivial coefficients, `P_s = (1 + s U_g)/2` (`s = ±1`) are the
eigenprojections of the unitary `U_g` (`EquivariantHilbertModule.eigenProjection`). When `g` is
central and acts trivially on `A`, they reduce every cycle whose operator commutes with `U_g`, and
a class is the sum of the classes of its two eigen parts (`KasparovCycle.exists_eigenSplit`,
`OddKasparovCycle.exists_eigenSplit`). The averaging over `Γ` that provides such an operator is in
`KasparovFiniteAveraging`. -/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {E : Type uE} [Group Γ] [Fintype Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

/-! ## Eigenspace projections of an involution

Over a trivial coefficient action every group element acts by an adjointable unitary `U_g`.
For an involution `g`, `P_s = (1 + s U_g)/2` with `s = ±1` are complementary star projections
onto the eigenspaces of `U_g`. They commute with every operator fixed by conjugation by `g`,
with the representation on `g`-fixed elements, and with the grading. -/

open scoped InnerProductSpace

namespace EquivariantHilbertModule

omit [Fintype Γ] [StarOrderedRing B] [CompleteSpace E]

variable [β.IsTrivial] (V : EquivariantHilbertModule β E)

variable {g : Γ} (hg : g * g = 1)
include hg

theorem actionOperator_mul_self : V.actionOperator g * V.actionOperator g = 1 := by
  rw [← actionOperator_mul, hg, actionOperator_one]

theorem star_actionOperator_of_mul_self : star (V.actionOperator g) = V.actionOperator g := by
  rw [star_actionOperator, inv_eq_of_mul_eq_one_right hg]

omit hg in
/-- The projection `(1 + s U_g)/2`; for an involution and `s = ±1`, onto the `s`-eigenspace. -/
def eigenProjection (g : Γ) (s : ℂ) : AdjointableMap B E E :=
  (2 : ℂ)⁻¹ • (1 + s • V.actionOperator g)

theorem eigenProjection_isStarProjection {s : ℂ} (hs : s * s = 1) (hsr : star s = s) :
    IsStarProjection (V.eigenProjection g s) where
  isIdempotentElem := by
    have hU := V.actionOperator_mul_self hg
    have key : (1 + s • V.actionOperator g) * (1 + s • V.actionOperator g) =
        (2 : ℂ) • (1 + s • V.actionOperator g) := by
      simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, hs, hU, one_smul]
      module
    rw [IsIdempotentElem, eigenProjection, smul_mul_smul_comm, key, smul_smul]
    norm_num
  isSelfAdjoint := by
    simp only [IsSelfAdjoint, eigenProjection, star_smul, star_add, star_one, hsr,
      V.star_actionOperator_of_mul_self hg, star_inv₀, star_ofNat]

omit hg in
theorem eigenProjection_add_neg (g : Γ) :
    V.eigenProjection g 1 + V.eigenProjection g (-1) = 1 := by
  simp only [eigenProjection]
  module

/-- `U_g` acts by the scalar `s` on the range of `P_s`. -/
theorem actionOperator_mul_eigenProjection {s : ℂ} (hs : s * s = 1) :
    V.actionOperator g * V.eigenProjection g s = s • V.eigenProjection g s := by
  have hU := V.actionOperator_mul_self hg
  simp only [eigenProjection, mul_smul_comm, mul_add, mul_one, hU]
  rw [smul_comm s ((2 : ℂ)⁻¹), smul_add s, smul_smul s s, hs, one_smul,
    add_comm (s • (1 : AdjointableMap B E E))]

omit hg in
/-- The eigenprojections commute with every operator fixed by conjugation by `g`. -/
theorem commute_eigenProjection {g : Γ} {T : AdjointableMap B E E}
    (hT : V.conjugateOperator g T = T) (s : ℂ) : Commute (V.eigenProjection g s) T :=
  ((Commute.one_left T).add_left ((V.commute_actionOperator hT).smul_left s)).smul_left _

omit hg in
/-- The eigenprojections commute with a grading preserved by the action. -/
theorem eigenProjection_grading {γ : GradedHilbertModule (CStarGrading.trivial : CStarGrading B) E}
    (hγ : V.PreservesGrading γ) (g : Γ) (s : ℂ) (x : E) :
    V.eigenProjection g s (γ.grading x) = γ.grading (V.eigenProjection g s x) := by
  simp [eigenProjection, hγ g x, map_add, map_smul]

end EquivariantHilbertModule

namespace KasparovCycle

/-- Over trivial coefficients, the eigenprojections of `U_g` commute with the averaged operator. -/
theorem commute_eigenProjection_averagedOperator
    [β.IsTrivial] (c : KasparovCycle α β E) (g : Γ) (s : ℂ) :
    Commute (c.groupAction.eigenProjection g s) c.averagedOperator :=
  c.groupAction.commute_eigenProjection (c.conjugateOperator_averagedOperator g) s

omit [Fintype Γ] in
/-- The eigenprojections commute with the representation on elements fixed by `g`. -/
theorem commute_eigenProjection_representation
    [β.IsTrivial] (c : KasparovCycle α β E) {g : Γ} {a : A}
    (ha : α.automorphism g a = a) (s : ℂ) :
    Commute (c.groupAction.eigenProjection g s) (c.representation a) :=
  c.groupAction.commute_eigenProjection (by rw [c.representation_equivariant, ha]) s

omit [Fintype Γ] in
/-- The eigenprojections commute with the grading. -/
theorem eigenProjection_grading
    [β.IsTrivial] (c : KasparovCycle α β E) (g : Γ) (s : ℂ)
    (x : E) : c.groupAction.eigenProjection g s (c.grading.grading x) =
      c.grading.grading (c.groupAction.eigenProjection g s x) :=
  c.groupAction.eigenProjection_grading c.grading_preserved g s x

end KasparovCycle
namespace OddKasparovCycle

variable [TopologicalSpace.SeparableSpace B]

omit [TopologicalSpace.SeparableSpace B] in
/-- Over trivial coefficients, the eigenprojections of `U_g` commute with the averaged operator. -/
theorem commute_eigenProjection_averagedOperator
    [β.IsTrivial] (c : OddKasparovCycle α β E) (g : Γ)
    (s : ℂ) : Commute (c.groupAction.eigenProjection g s) c.averagedOperator :=
  c.groupAction.commute_eigenProjection (c.conjugateOperator_averagedOperator g) s

omit [Fintype Γ] [TopologicalSpace.SeparableSpace B] in
/-- The eigenprojections commute with the representation on elements fixed by `g`. -/
theorem commute_eigenProjection_representation
    [β.IsTrivial] (c : OddKasparovCycle α β E) {g : Γ}
    {a : A} (ha : α.automorphism g a = a) (s : ℂ) :
    Commute (c.groupAction.eigenProjection g s) (c.representation a) :=
  c.groupAction.commute_eigenProjection (by rw [c.representation_equivariant, ha]) s

end OddKasparovCycle
/-! ## Splitting a class into the eigenspaces of a central involution

Let `g` be a central involution acting trivially on `A`, over trivial coefficients. After
averaging, the operator commutes with `U_g`, so the eigenprojections `P_{±1} = (1 ± U_g)/2`
reduce the cycle. The class is the sum of the class of the `+1` part, on which `g` acts
trivially, and the class of the `-1` part, on which `g` acts by `-1`. -/

namespace EquivariantHilbertModule

omit [Fintype Γ] [StarOrderedRing B] [CompleteSpace E]

variable [β.IsTrivial] (V : EquivariantHilbertModule β E)

/-- The eigenprojections of a central element commute with the whole action. -/
theorem eigenProjection_action {g : Γ} (hcentral : ∀ h, h * g = g * h) (s : ℂ) (h : Γ) (x : E) :
    V.eigenProjection g s (V.action h x) = V.action h (V.eigenProjection g s x) := by
  simp only [eigenProjection, AdjointableMap.coe_smul_apply, AdjointableMap.coe_add_apply,
    AdjointableMap.one_apply, actionOperator_apply, map_smul, map_add, ← V.mul_apply]
  rw [hcentral]

/-- On the range of `P_s` the involution acts by the scalar `s`. -/
theorem action_of_eigenProjection_fixed {g : Γ} (hg : g * g = 1) {s : ℂ} (hs : s * s = 1)
    {x : E} (hx : V.eigenProjection g s x = x) : V.action g x = s • x := by
  have h := congrArg (fun T : AdjointableMap B E E => T x)
    (V.actionOperator_mul_eigenProjection hg hs)
  simp only [AdjointableMap.mul_apply, AdjointableMap.coe_smul_apply, actionOperator_apply,
    hx] at h
  exact h

/-- The complement of `P_1` is `P_{-1}`. -/
theorem one_sub_eigenProjection (g : Γ) :
    1 - V.eigenProjection g 1 = V.eigenProjection g (-1) := by
  rw [← V.eigenProjection_add_neg g]
  abel

end EquivariantHilbertModule

namespace KasparovCycle

omit [Fintype Γ] in
/-- If the operator commutes with `U_g` for a central involution `g` acting trivially on `A`,
the eigenprojections of `U_g` reduce the cycle. -/
theorem reducingProjection_eigenProjection
    [β.IsTrivial] (c : KasparovCycle α β E) {g : Γ}
    (hg : g * g = 1) (hcentral : ∀ h, h * g = g * h) (hα : ∀ a, α.automorphism g a = a)
    (hF : c.groupAction.conjugateOperator g c.operator = c.operator)
    {s : ℂ} (hs : s * s = 1) (hsr : star s = s) :
    c.ReducingProjection (c.groupAction.eigenProjection g s) where
  isStarProjection := c.groupAction.eigenProjection_isStarProjection hg hs hsr
  commute_operator := c.groupAction.commute_eigenProjection hF s
  commute_representation a := c.commute_eigenProjection_representation (hα a) s
  grading x := c.eigenProjection_grading g s x
  action h x := c.groupAction.eigenProjection_action hcentral s h x

/-- Eigenspace splitting of a class. Every class over trivial coefficients is the sum of the
class of a cycle on which `g` acts trivially and the class of a cycle on which `g` acts by
`-1`; both are compressions of one averaged representative. -/
theorem exists_eigenSplit
    [β.IsTrivial] (c : KasparovCycle α β E) {g : Γ}
    (hg : g * g = 1) (hcentral : ∀ h, h * g = g * h) (hα : ∀ a, α.automorphism g a = a) :
    ∃ (T : AdjointableMap B E E) (hT : c.OperatorConditions T)
      (hP : (c.withOperator T hT).ReducingProjection (c.groupAction.eigenProjection g 1)),
      (∀ x, ((c.withOperator T hT).compress hP).groupAction.action g x = x) ∧
      (∀ x, ((c.withOperator T hT).compress hP.one_sub).groupAction.action g x = -x) ∧
      KasparovHomotopyClass.mk.{uΓ,uA,uB,uE} (BundledKasparovCycle.of c) =
        KasparovHomotopyClass.mk (BundledKasparovCycle.of ((c.withOperator T hT).compress hP)) +
          KasparovHomotopyClass.mk
            (BundledKasparovCycle.of ((c.withOperator T hT).compress hP.one_sub)) := by
  obtain ⟨T, hT, -, hTg, hmk⟩ := c.exists_equivariant_selfadjoint_representative
  have hP : (c.withOperator T hT).ReducingProjection (c.groupAction.eigenProjection g 1) :=
    (c.withOperator T hT).reducingProjection_eigenProjection hg hcentral hα (hTg g)
      (by norm_num) (by simp)
  refine ⟨T, hT, hP, fun x => Subtype.ext ?_, fun x => Subtype.ext ?_,
    hmk.trans ((c.withOperator T hT).mk_eq_add_compress hP)⟩
  · have hx : c.groupAction.eigenProjection g 1 (x : E) = (x : E) := x.property
    change c.groupAction.action g (x : E) = (x : E)
    simpa using c.groupAction.action_of_eigenProjection_fixed hg (by norm_num) hx
  · have hx : c.groupAction.eigenProjection g (-1) (x : E) = (x : E) := by
      rw [← c.groupAction.one_sub_eigenProjection]
      exact x.property
    change c.groupAction.action g (x : E) = -(x : E)
    simpa using c.groupAction.action_of_eigenProjection_fixed hg (by norm_num) hx

end KasparovCycle

namespace OddKasparovCycle

omit [Fintype Γ] in
/-- Odd analogue of `KasparovCycle.reducingProjection_eigenProjection`. -/
theorem reducingProjection_eigenProjection
    [β.IsTrivial] (c : OddKasparovCycle α β E) {g : Γ}
    (hg : g * g = 1) (hcentral : ∀ h, h * g = g * h) (hα : ∀ a, α.automorphism g a = a)
    (hF : c.groupAction.conjugateOperator g c.operator = c.operator)
    {s : ℂ} (hs : s * s = 1) (hsr : star s = s) :
    c.ReducingProjection (c.groupAction.eigenProjection g s) where
  isStarProjection := c.groupAction.eigenProjection_isStarProjection hg hs hsr
  commute_operator := c.groupAction.commute_eigenProjection hF s
  commute_representation a := c.commute_eigenProjection_representation (hα a) s
  action h x := c.groupAction.eigenProjection_action hcentral s h x

/-- Odd eigenspace splitting of a class, as `KasparovCycle.exists_eigenSplit`. -/
theorem exists_eigenSplit [TopologicalSpace.SeparableSpace B]
    [β.IsTrivial] (c : OddKasparovCycle α β E) {g : Γ}
    (hg : g * g = 1) (hcentral : ∀ h, h * g = g * h) (hα : ∀ a, α.automorphism g a = a) :
    ∃ (T : AdjointableMap B E E) (hT : c.OperatorConditions T)
      (hP : (c.withOperator T hT).ReducingProjection (c.groupAction.eigenProjection g 1)),
      (∀ x, ((c.withOperator T hT).compress hP).groupAction.action g x = x) ∧
      (∀ x, ((c.withOperator T hT).compress hP.one_sub).groupAction.action g x = -x) ∧
      OddKK.mk.{uΓ,uA,uB,uE} (BundledOddKasparovCycle.of c) =
        OddKK.mk (BundledOddKasparovCycle.of ((c.withOperator T hT).compress hP)) +
          OddKK.mk (BundledOddKasparovCycle.of ((c.withOperator T hT).compress hP.one_sub)) := by
  obtain ⟨T, hT, -, hTg, hmk⟩ := c.exists_equivariant_selfadjoint_representative
  have hP : (c.withOperator T hT).ReducingProjection (c.groupAction.eigenProjection g 1) :=
    (c.withOperator T hT).reducingProjection_eigenProjection hg hcentral hα (hTg g)
      (by norm_num) (by simp)
  refine ⟨T, hT, hP, fun x => Subtype.ext ?_, fun x => Subtype.ext ?_,
    hmk.trans ((c.withOperator T hT).mk_eq_add_compress hP)⟩
  · have hx : c.groupAction.eigenProjection g 1 (x : E) = (x : E) := x.property
    change c.groupAction.action g (x : E) = (x : E)
    simpa using c.groupAction.action_of_eigenProjection_fixed hg (by norm_num) hx
  · have hx : c.groupAction.eigenProjection g (-1) (x : E) = (x : E) := by
      rw [← c.groupAction.one_sub_eigenProjection]
      exact x.property
    change c.groupAction.action g (x : E) = -(x : E)
    simpa using c.groupAction.action_of_eigenProjection_fixed hg (by norm_num) hx

end OddKasparovCycle
end BC4lean.KKTheory

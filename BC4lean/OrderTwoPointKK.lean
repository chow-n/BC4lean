import BC4lean.KasparovLocalCompactPerturbation
import BC4lean.KasparovHomotopyGroup
import BC4lean.OddFredholmLocalCompactPerturbation
import BC4lean.OddFredholmFullNormalization
import BC4lean.KasparovReducingCompression

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! Averaging the operator of a Kasparov cycle over a finite group.

For a finite group the operator `F` of a cycle is equivariant only modulo compact operators
after the representation. If `F` is selfadjoint, its average `|Γ|⁻¹ ∑_g U_g F U_g*` is an
admissible operator that commutes exactly with the group action, and the affine path from `F`
to the average is an operator homotopy. The same holds for odd (ungraded) cycles. -/

noncomputable section
universe uΓ uA uB uE
namespace BC4lean.KKTheory

variable {Γ : Type uΓ} {A : Type uA} {B : Type uB} {E : Type uE} [Group Γ] [Fintype Γ]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}

namespace EquivariantHilbertModule

variable (U : EquivariantHilbertModule β E)

/-- Conjugation by a group element as an additive map of adjointable operators. -/
def conjugateAddHom (g : Γ) : AdjointableMap B E E →+ AdjointableMap B E E where
  toFun := U.conjugateOperator g
  map_zero' := by ext x; simp
  map_add' S T := by ext x; simp [map_add]

omit [Fintype Γ] [StarOrderedRing B] [CompleteSpace E] in
@[simp] theorem conjugateAddHom_apply (g : Γ) (T : AdjointableMap B E E) :
    U.conjugateAddHom g T = U.conjugateOperator g T := rfl

omit [Fintype Γ] [StarOrderedRing B] [CompleteSpace E] in
theorem conjugateOperator_smul (g : Γ) (z : ℂ) (T : AdjointableMap B E E) :
    U.conjugateOperator g (z • T) = z • U.conjugateOperator g T := by
  ext x; simp [map_smul]

omit [Fintype Γ] [StarOrderedRing B] [CompleteSpace E] in
theorem star_conjugateOperator (g : Γ) (T : AdjointableMap B E E) :
    star (U.conjugateOperator g T) = U.conjugateOperator g (star T) := by
  simp only [AdjointableMap.star_eq_adjoint, conjugateMap_adjoint]

end EquivariantHilbertModule

/-! ## Coefficient actions that fix every element

`CStarAlgebraAction.IsTrivial β` says that every group element acts as the identity on the
coefficients. The trivial action has it, and so does its pointwise extension to continuous
sections over a parameter space; the second instance lets interval cycles of a homotopy use
the eigenprojections below. -/

section IsTrivial

omit [Fintype Γ] [PartialOrder B] [StarOrderedRing B]

/-- Every group element acts as the identity on the coefficients. -/
class CStarAlgebraAction.IsTrivial (β : CStarAlgebraAction Γ B) : Prop where
  apply_eq : ∀ g b, β.automorphism g b = b

instance CStarAlgebraAction.isTrivial_trivial :
    (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B).IsTrivial :=
  ⟨fun _ _ => rfl⟩

instance CStarAlgebraAction.isTrivial_continuousSections {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [β.IsTrivial] : (β.continuousSections (X := X)).IsTrivial :=
  ⟨fun g b => by ext t; exact CStarAlgebraAction.IsTrivial.apply_eq g (b t)⟩

theorem CStarAlgebraAction.opStarAlgEquiv_apply_of_isTrivial [β.IsTrivial] (g : Γ)
    (z : Bᵐᵒᵖ) : opStarAlgEquiv (β.automorphism g) z = z := by
  rw [opStarAlgEquiv_apply, CStarAlgebraAction.IsTrivial.apply_eq, MulOpposite.op_unop]

end IsTrivial

/-! ## Eigenspace projections of an involution

Over a trivial coefficient action every group element acts by an adjointable unitary `U_g`.
For an involution `g`, `P_s = (1 + s U_g)/2` with `s = ±1` are complementary star projections
onto the eigenspaces of `U_g`. They commute with every operator fixed by conjugation by `g`,
with the representation on `g`-fixed elements, and with the grading. -/

open scoped InnerProductSpace

namespace EquivariantHilbertModule

omit [Fintype Γ] [StarOrderedRing B] [CompleteSpace E]

variable [β.IsTrivial] (V : EquivariantHilbertModule β E)

/-- Over trivial coefficients each group element acts by an adjointable unitary. -/
def actionOperator (g : Γ) : AdjointableMap B E E where
  toCLM := (V.action g).toContinuousLinearEquiv.toContinuousLinearMap
  adjointCLM := (V.action g⁻¹).toContinuousLinearEquiv.toContinuousLinearMap
  adjoint_identity x y := by
    change ⟪V.action g x, y⟫_(Bᵐᵒᵖ) = ⟪x, V.action g⁻¹ y⟫_(Bᵐᵒᵖ)
    rw [V.inner_action_left, CStarAlgebraAction.opStarAlgEquiv_apply_of_isTrivial]

@[simp] theorem actionOperator_apply (g : Γ) (x : E) : V.actionOperator g x = V.action g x := rfl

theorem star_actionOperator (g : Γ) : star (V.actionOperator g) = V.actionOperator g⁻¹ := by
  ext x
  rfl

theorem actionOperator_mul (g h : Γ) :
    V.actionOperator (g * h) = V.actionOperator g * V.actionOperator h := by
  ext x
  simp

theorem actionOperator_one : V.actionOperator 1 = 1 := by
  ext x
  simp

/-- Conjugation is multiplication by the unitaries. -/
theorem conjugateOperator_eq (g : Γ) (T : AdjointableMap B E E) :
    V.conjugateOperator g T = V.actionOperator g * T * V.actionOperator g⁻¹ := by
  ext x
  rfl

/-- An operator fixed by conjugation commutes with the unitary. -/
theorem commute_actionOperator {g : Γ} {T : AdjointableMap B E E}
    (hT : V.conjugateOperator g T = T) : Commute (V.actionOperator g) T := by
  have h := congrArg (· * V.actionOperator g) hT
  simp only [conjugateOperator_eq, mul_assoc, ← actionOperator_mul, inv_mul_cancel,
    actionOperator_one, mul_one] at h
  exact h

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

/-- The average `|Γ|⁻¹ ∑_g U_g F U_g*` of the conjugates of the operator. -/
def averagedOperator (c : KasparovCycle α β E) : AdjointableMap B E E :=
  (Fintype.card Γ : ℂ)⁻¹ • ∑ g, c.groupAction.conjugateOperator g c.operator

/-- The averaged operator commutes exactly with the group action. -/
theorem conjugateOperator_averagedOperator (c : KasparovCycle α β E) (h : Γ) :
    c.groupAction.conjugateOperator h c.averagedOperator = c.averagedOperator := by
  rw [averagedOperator, EquivariantHilbertModule.conjugateOperator_smul]
  congr 1
  rw [← EquivariantHilbertModule.conjugateAddHom_apply, map_sum]
  simp only [EquivariantHilbertModule.conjugateAddHom_apply,
    ← EquivariantHilbertModule.conjugateMap_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun _ => rfl)

/-- The perturbation from the operator to its average is the mean of the equivariance defects. -/
theorem averagedOperator_sub (c : KasparovCycle α β E) :
    c.averagedOperator - c.operator = (Fintype.card Γ : ℂ)⁻¹ •
      ∑ g, (c.groupAction.conjugateOperator g c.operator - c.operator) := by
  have hcard : (Fintype.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [averagedOperator, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, smul_sub,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]

/-- The averaging perturbation is locally compact. -/
theorem averagedOperator_sub_mul_isModuleCompact (c : KasparovCycle α β E) (a : A) :
    IsModuleCompact ((c.averagedOperator - c.operator) * c.representation a) := by
  rw [averagedOperator_sub, smul_mul_assoc, Finset.sum_mul]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun g _ => c.equivariance_mod_compact g a)

/-- The averaged operator is odd. -/
theorem averagedOperator_isOdd (c : KasparovCycle α β E) :
    c.grading.IsOdd c.grading c.averagedOperator := by
  have hzero : c.grading.IsOdd c.grading 0 := by
    have h := c.operator_odd.smul (0 : ℂ)
    change c.grading.IsOdd c.grading ((0 : ℂ) • c.operator) at h
    rwa [zero_smul] at h
  have hsum : c.grading.IsOdd c.grading
      (∑ g, c.groupAction.conjugateOperator g c.operator) :=
    Finset.sum_induction _ (fun T => c.grading.IsOdd c.grading T) (fun _ _ h₁ h₂ => h₁.add h₂)
      hzero (fun g _ => EquivariantHilbertModule.conjugateMap_isOdd c.groupAction c.groupAction
        c.grading_preserved c.grading_preserved g c.operator_odd)
  exact hsum.smul _

/-- A selfadjoint operator has a selfadjoint average. -/
theorem star_averagedOperator (c : KasparovCycle α β E) (hF : star c.operator = c.operator) :
    star c.averagedOperator = c.averagedOperator := by
  simp only [averagedOperator, star_smul, star_inv₀, star_natCast, star_sum,
    EquivariantHilbertModule.star_conjugateOperator, hF]

/-- For a selfadjoint operator, the average is admissible on the same module. -/
theorem operatorConditions_averagedOperator (c : KasparovCycle α β E)
    (hF : star c.operator = c.operator) : c.OperatorConditions c.averagedOperator := by
  have hodd : c.grading.IsOdd c.grading (c.averagedOperator - c.operator) := by
    have h := c.averagedOperator_isOdd.add (c.operator_odd.smul (-1))
    change c.grading.IsOdd c.grading (c.averagedOperator + (-1 : ℂ) • c.operator) at h
    rwa [neg_one_smul, ← sub_eq_add_neg] at h
  have hstar : star (c.averagedOperator - c.operator) = c.averagedOperator - c.operator := by
    rw [star_sub, c.star_averagedOperator hF, hF]
  have h := c.operatorConditions_add_locallyCompact (c.averagedOperator - c.operator) hodd
    c.averagedOperator_sub_mul_isModuleCompact
    (fun a => by rw [hstar]; exact c.averagedOperator_sub_mul_isModuleCompact a)
  rwa [add_sub_cancel] at h

/-- The affine operator homotopy from a selfadjoint operator to its average. -/
def averagingHomotopy (c : KasparovCycle α β E) (hF : star c.operator = c.operator) :
    KasparovOperatorHomotopy c c.operator c.averagedOperator :=
  KasparovOperatorHomotopy.compactPerturbation c c.averagedOperator
    (c.operatorConditions_averagedOperator hF) c.averagedOperator_sub_mul_isModuleCompact

/-- Replacing a selfadjoint operator by its average does not change the class. -/
theorem mk_averagedCycle (c : KasparovCycle α β E) (hF : star c.operator = c.operator) :
    KasparovHomotopyClass.mk.{uΓ,uA,uB,uE} (BundledKasparovCycle.of c) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (c.withOperator c.averagedOperator (c.operatorConditions_averagedOperator hF))) := by
  have h := KasparovHomotopyClass.mk_eq_of_full
    (FullKasparovHomotopy.ofOperatorHomotopy (c.averagingHomotopy hF))
  rwa [withOperator_self] at h

/-- Every class of a finite group has a representative on the same module whose operator is
selfadjoint and commutes exactly with the group action. -/
theorem exists_equivariant_selfadjoint_representative (c : KasparovCycle α β E) :
    ∃ (T : AdjointableMap B E E) (hT : c.OperatorConditions T),
      star T = T ∧ (∀ g, c.groupAction.conjugateOperator g T = T) ∧
      KasparovHomotopyClass.mk.{uΓ,uA,uB,uE} (BundledKasparovCycle.of c) =
        KasparovHomotopyClass.mk (BundledKasparovCycle.of (c.withOperator T hT)) := by
  let c₁ := c.withOperator (c.operator + c.symmetrizingPerturbation)
    c.operatorConditions_symmetrization
  have hF₁ : star c₁.operator = c₁.operator := c.symmetrizedOperator_selfadjoint
  have h₀ : KasparovHomotopyClass.mk.{uΓ,uA,uB,uE} (BundledKasparovCycle.of c) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of c₁) := by
    have h := KasparovHomotopyClass.mk_eq_of_full
      (FullKasparovHomotopy.ofOperatorHomotopy c.symmetrizationHomotopy)
    rwa [withOperator_self] at h
  have h₁ := c₁.operatorConditions_averagedOperator hF₁
  have hT : c.OperatorConditions c₁.averagedOperator := ⟨h₁.1, h₁.2, h₁.3, h₁.4, h₁.5⟩
  refine ⟨c₁.averagedOperator, hT, c₁.star_averagedOperator hF₁,
    c₁.conjugateOperator_averagedOperator, ?_⟩
  exact h₀.trans (c₁.mk_averagedCycle hF₁)

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

/-- The average `|Γ|⁻¹ ∑_g U_g F U_g*` of the conjugates of the operator of an odd cycle. -/
def averagedOperator (c : OddKasparovCycle α β E) : AdjointableMap B E E :=
  (Fintype.card Γ : ℂ)⁻¹ • ∑ g, c.groupAction.conjugateOperator g c.operator

/-- The averaged operator commutes exactly with the group action. -/
theorem conjugateOperator_averagedOperator (c : OddKasparovCycle α β E) (h : Γ) :
    c.groupAction.conjugateOperator h c.averagedOperator = c.averagedOperator := by
  rw [averagedOperator, EquivariantHilbertModule.conjugateOperator_smul]
  congr 1
  rw [← EquivariantHilbertModule.conjugateAddHom_apply, map_sum]
  simp only [EquivariantHilbertModule.conjugateAddHom_apply,
    ← EquivariantHilbertModule.conjugateMap_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun _ => rfl)

/-- The perturbation from the operator to its average is the mean of the equivariance defects. -/
theorem averagedOperator_sub (c : OddKasparovCycle α β E) :
    c.averagedOperator - c.operator = (Fintype.card Γ : ℂ)⁻¹ •
      ∑ g, (c.groupAction.conjugateOperator g c.operator - c.operator) := by
  have hcard : (Fintype.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [averagedOperator, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, smul_sub,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]

/-- The averaging perturbation is locally compact. -/
theorem averagedOperator_sub_mul_isModuleCompact (c : OddKasparovCycle α β E) (a : A) :
    IsModuleCompact ((c.averagedOperator - c.operator) * c.representation a) := by
  rw [averagedOperator_sub, smul_mul_assoc, Finset.sum_mul]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun g _ => c.equivariance_mod_compact g a)

/-- A selfadjoint operator has a selfadjoint average. -/
theorem star_averagedOperator (c : OddKasparovCycle α β E) (hF : star c.operator = c.operator) :
    star c.averagedOperator = c.averagedOperator := by
  simp only [averagedOperator, star_smul, star_inv₀, star_natCast, star_sum,
    EquivariantHilbertModule.star_conjugateOperator, hF]

/-- For a selfadjoint operator, the average is admissible on the same module. -/
theorem operatorConditions_averagedOperator (c : OddKasparovCycle α β E)
    (hF : star c.operator = c.operator) : c.OperatorConditions c.averagedOperator := by
  have hstar : star (c.averagedOperator - c.operator) = c.averagedOperator - c.operator := by
    rw [star_sub, c.star_averagedOperator hF, hF]
  have h := c.operatorConditions_add_locallyCompact (c.averagedOperator - c.operator)
    c.averagedOperator_sub_mul_isModuleCompact
    (fun a => by rw [hstar]; exact c.averagedOperator_sub_mul_isModuleCompact a)
  rwa [add_sub_cancel] at h

/-- The affine operator homotopy from a selfadjoint operator to its average. -/
def averagingHomotopy (c : OddKasparovCycle α β E) (hF : star c.operator = c.operator) :
    OddKasparovOperatorHomotopy c c.operator c.averagedOperator :=
  OddKasparovOperatorHomotopy.compactPerturbation c c.averagedOperator
    (c.operatorConditions_averagedOperator hF) c.averagedOperator_sub_mul_isModuleCompact

variable [TopologicalSpace.SeparableSpace B]

/-- Replacing a selfadjoint operator by its average does not change the odd class. -/
theorem mk_averagedCycle (c : OddKasparovCycle α β E) (hF : star c.operator = c.operator) :
    OddKK.mk.{uΓ,uA,uB,uE} (BundledOddKasparovCycle.of c) =
      OddKK.mk (BundledOddKasparovCycle.of
        (c.withOperator c.averagedOperator (c.operatorConditions_averagedOperator hF))) := by
  have h := OddKK.mk_eq_of_full
    (FullOddKasparovHomotopy.ofOperatorHomotopy (c.averagingHomotopy hF))
  rwa [withOperator_self] at h

/-- Every odd class of a finite group has a representative on the same module whose operator
is selfadjoint and commutes exactly with the group action. -/
theorem exists_equivariant_selfadjoint_representative (c : OddKasparovCycle α β E) :
    ∃ (T : AdjointableMap B E E) (hT : c.OperatorConditions T),
      star T = T ∧ (∀ g, c.groupAction.conjugateOperator g T = T) ∧
      OddKK.mk.{uΓ,uA,uB,uE} (BundledOddKasparovCycle.of c) =
        OddKK.mk (BundledOddKasparovCycle.of (c.withOperator T hT)) := by
  let c₁ := c.symmetrized
  have hF₁ : star c₁.operator = c₁.operator := c.symmetrizedOperator_selfadjoint
  have h₀ : OddKK.mk.{uΓ,uA,uB,uE} (BundledOddKasparovCycle.of c) =
      OddKK.mk (BundledOddKasparovCycle.of c₁) := by
    have h := OddKK.mk_eq_of_full
      (FullOddKasparovHomotopy.ofOperatorHomotopy c.symmetrizationHomotopy)
    rwa [withOperator_self] at h
  have h₁ := c₁.operatorConditions_averagedOperator hF₁
  have hT : c.OperatorConditions c₁.averagedOperator := ⟨h₁.1, h₁.2, h₁.3, h₁.4⟩
  refine ⟨c₁.averagedOperator, hT, c₁.star_averagedOperator hF₁,
    c₁.conjugateOperator_averagedOperator, ?_⟩
  exact h₀.trans (c₁.mk_averagedCycle hF₁)

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

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
to the average is an operator homotopy. The same holds for odd (ungraded) cycles.

Over a coefficient action that fixes every element (`CStarAlgebraAction.IsTrivial`), each group
element acts on the module by an adjointable unitary `U_g` (`actionOperator`). -/

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
operators built from the unitaries `U_g`. -/

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

end OddKasparovCycle
end BC4lean.KKTheory

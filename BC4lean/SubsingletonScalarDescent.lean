import BC4lean.UnitScalarDescent
import BC4lean.KKGroupRestriction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Scalar descent for trivial actions

For a countable group `Γ` acting trivially on `ℂ` and on `B`, the descended
class of `x ∈ KK^Γ(ℂ, B)`, pulled back along the scalar coefficient inclusion
`ℂ → ℂ ⋊ᵣ Γ`, is the ordinary coefficient extension of the restricted class
`res x ∈ KK(ℂ, B)` (restriction along `Unit →* Γ`) along `B → B ⋊ᵣ Γ`.
No hypothesis on the size of `Γ` is used; the one-element case is where
restriction is also invertible (`GroupRestriction.subsingletonParityEquiv`). The proof is the whole-cycle identity
isomorphism of `UnitScalarDescent`: restriction to `Unit` changes only the
group action, and both cycles are built on the same completed module
`E ⊗_B (B ⋊ᵣ Γ)`.
-/

noncomputable section
universe uΓ uB uE u
namespace BC4lean.KKTheory.SubsingletonScalarDescent
open GroupRestriction
open scoped KasparovDescent ComplexOrder

variable (Γ : Type uΓ) [Group Γ] [Countable Γ]
variable {B : Type uB} [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]

abbrev scalarAction : CStarAlgebraAction Γ ℂ := CStarAlgebraAction.trivial
abbrev coefficientAction : CStarAlgebraAction Γ B := CStarAlgebraAction.trivial
abbrev scalarInclusion : ℂ →⋆ₙₐ[ℂ] ReducedCrossedProduct (scalarAction Γ) :=
  coefficientToReducedCrossed (scalarAction Γ)
abbrev coefficientInclusion : B →⋆ₙₐ[ℂ]
    ReducedCrossedProduct (coefficientAction Γ (B := B)) :=
  coefficientToReducedCrossed (coefficientAction Γ (B := B))
abbrev descendedScalarAction : CStarAlgebraAction Unit (ReducedCrossedProduct (scalarAction Γ)) :=
  CStarAlgebraAction.trivial
abbrev descendedCoefficientAction : CStarAlgebraAction Unit
    (ReducedCrossedProduct (coefficientAction Γ (B := B))) := CStarAlgebraAction.trivial

omit [Countable Γ] in
/-- The scalar coefficient inclusion is equivariant for the trivial `Unit` actions. -/
theorem scalarCoefficient_equivariant : ∀ (g : Unit) (a : ℂ),
    scalarInclusion Γ ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ).automorphism g a) =
      (descendedScalarAction Γ).automorphism g (scalarInclusion Γ a) := fun _ _ => rfl

section Raw
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

/-- Descent restricted to scalar coefficients is the ordinary scalar
coefficient extension of the restricted cycle, on the same module. -/
def evenCoefficientRestrictionIso
    (c : KasparovCycle (scalarAction Γ) (coefficientAction Γ (B := B)) E) :
    KasparovCycleIso
      (NativeSourcePullback.evenCycle CStarAlgebraAction.trivial (scalarInclusion Γ) (fun _ _ => rfl)
        (KasparovDescent.evenCycle (coefficientAction Γ (B := B)) (scalarAction Γ) c))
      ((cycleComap (fromUnitHom (Γ := Γ)) c).scalarCoefficientTensor
        (coefficientInclusion Γ (B := B))) where
  moduleEquiv := HilbertModuleEquiv.refl
  grading_intertwine _ := rfl
  action_intertwine _ _ := rfl
  representation_intertwine a z := by
    change KasparovDescent.reducedSourceRepresentation (coefficientAction Γ (B := B)) E
        (scalarAction Γ) c.groupAction c.representation c.representation_equivariant
        (scalarInclusion Γ a) z =
      KasparovDescent.sourceRepresentation (coefficientAction Γ (B := B)) E c.representation a z
    exact congrArg
      (fun T : AdjointableMap (ReducedCrossedProduct (coefficientAction Γ (B := B)))
          (KasparovDescent.Module (coefficientAction Γ (B := B)) E)
          (KasparovDescent.Module (coefficientAction Γ (B := B)) E) => T z)
      (KasparovDescent.reducedSourceRepresentation_coefficient (coefficientAction Γ (B := B)) E
        (scalarAction Γ) c.groupAction c.representation c.representation_equivariant a)
  operator_intertwine _ := rfl

/-- The odd cycle has the same coefficient restriction. -/
def oddCoefficientRestrictionIso
    (c : OddKasparovCycle (scalarAction Γ) (coefficientAction Γ (B := B)) E) :
    OddKasparovCycleIso
      (NativeSourcePullback.oddCycle CStarAlgebraAction.trivial (scalarInclusion Γ) (fun _ _ => rfl)
        (KasparovDescent.oddCycle (coefficientAction Γ (B := B)) (scalarAction Γ) c))
      ((oddCycleComap (fromUnitHom (Γ := Γ)) c).coefficientTensor
        (coefficientInclusion Γ (B := B))) where
  moduleEquiv := HilbertModuleEquiv.refl
  action_intertwine _ _ := rfl
  representation_intertwine a z := by
    change KasparovDescent.reducedSourceRepresentation (coefficientAction Γ (B := B)) E
        (scalarAction Γ) c.groupAction c.representation c.representation_equivariant
        (scalarInclusion Γ a) z =
      KasparovDescent.sourceRepresentation (coefficientAction Γ (B := B)) E c.representation a z
    exact congrArg
      (fun T : AdjointableMap (ReducedCrossedProduct (coefficientAction Γ (B := B)))
          (KasparovDescent.Module (coefficientAction Γ (B := B)) E)
          (KasparovDescent.Module (coefficientAction Γ (B := B)) E) => T z)
      (KasparovDescent.reducedSourceRepresentation_coefficient (coefficientAction Γ (B := B)) E
        (scalarAction Γ) c.groupAction c.representation c.representation_equivariant a)
  operator_intertwine _ := rfl

end Raw

/-- Even half: scalar pullback of descent is coefficient extension of the restriction. -/
theorem evenClass_coefficientRestriction
    (x : KasparovHomotopyClass.{uΓ,0,uB,max u uB} (scalarAction Γ) (coefficientAction Γ (B := B))) :
    GroupUniverseParityFunctoriality.sourcePullback.{0,0,uΓ,max uΓ uB,u}
      (Γ := Unit) (A := ℂ) (B := ReducedCrossedProduct (scalarAction Γ))
      (C := ReducedCrossedProduct (coefficientAction Γ (B := B)))
      («α» := CStarAlgebraAction.trivial) («β» := descendedScalarAction Γ)
      (γ := descendedCoefficientAction Γ (B := B))
      false (scalarInclusion Γ) (scalarCoefficient_equivariant Γ)
        (KasparovDescent.evenClass (coefficientAction Γ (B := B)) (scalarAction Γ) x) =
      GroupUniverseOrdinaryEven.coefficientPushforward.{uB,max uΓ uB,max u uB}
        (B := B) (C := ReducedCrossedProduct (coefficientAction Γ (B := B)))
        (coefficientInclusion Γ (B := B)) (evenComap (fromUnitHom (Γ := Γ)) x) := by
  refine Quotient.inductionOn' x ?_
  intro c
  change GroupUniverseParityFunctoriality.sourcePullback.{0,0,uΓ,max uΓ uB,u}
      (Γ := Unit) (A := ℂ) (B := ReducedCrossedProduct (scalarAction Γ))
      (C := ReducedCrossedProduct (coefficientAction Γ (B := B)))
      («α» := CStarAlgebraAction.trivial) («β» := descendedScalarAction Γ)
      (γ := descendedCoefficientAction Γ (B := B))
      false (scalarInclusion Γ) (scalarCoefficient_equivariant Γ)
        (KasparovDescent.evenClass (coefficientAction Γ (B := B)) (scalarAction Γ)
          (KasparovHomotopyClass.mk c)) =
      GroupUniverseOrdinaryEven.coefficientPushforward.{uB,max uΓ uB,max u uB}
        (B := B) (C := ReducedCrossedProduct (coefficientAction Γ (B := B)))
        (coefficientInclusion Γ (B := B))
        (KasparovHomotopyClass.mk (BundledKasparovCycle.of (cycleComap (fromUnitHom (Γ := Γ)) c.cycle)))
  rw [KasparovDescent.evenClass_mk, NativeSourcePullback.even_mk]
  change (KasparovHomotopyClass.mk (BundledKasparovCycle.of
      (NativeSourcePullback.evenCycle CStarAlgebraAction.trivial (scalarInclusion Γ)
        (scalarCoefficient_equivariant Γ)
        (KasparovDescent.evenCycle (coefficientAction Γ (B := B)) (scalarAction Γ) c.cycle))) :
      KasparovHomotopyClass.{0,0,max uΓ uB,max u uΓ uB} CStarAlgebraAction.trivial
        (descendedCoefficientAction Γ (B := B))) = _
  exact (KasparovHomotopyClass.mk_eq_of_iso (evenCoefficientRestrictionIso Γ c.cycle)).trans
    (GroupUniverseOrdinaryEven.coefficientPushforward_mk_scalarCoefficientTensor
      (cycleComap (fromUnitHom (Γ := Γ)) c.cycle) (coefficientInclusion Γ (B := B))).symm

/-- Odd half: scalar pullback of descent is coefficient extension of the restriction. -/
theorem oddClass_coefficientRestriction
    (x : OddKK.{uΓ,0,uB,max u uB} (scalarAction Γ) (coefficientAction Γ (B := B))) :
    GroupUniverseParityFunctoriality.sourcePullback.{0,0,uΓ,max uΓ uB,u}
      (Γ := Unit) (A := ℂ) (B := ReducedCrossedProduct (scalarAction Γ))
      (C := ReducedCrossedProduct (coefficientAction Γ (B := B)))
      («α» := CStarAlgebraAction.trivial) («β» := descendedScalarAction Γ)
      (γ := descendedCoefficientAction Γ (B := B))
      true (scalarInclusion Γ) (scalarCoefficient_equivariant Γ)
        (KasparovDescent.oddClass (coefficientAction Γ (B := B)) (scalarAction Γ) x) =
      GroupUniverseOrdinaryOdd.coefficientPushforward.{uB,max uΓ uB,max u uB}
        (B := B) (C := ReducedCrossedProduct (coefficientAction Γ (B := B)))
        (coefficientInclusion Γ (B := B)) (oddComap (fromUnitHom (Γ := Γ)) x) := by
  refine Quotient.inductionOn' x ?_
  intro c
  change GroupUniverseParityFunctoriality.sourcePullback.{0,0,uΓ,max uΓ uB,u}
      (Γ := Unit) (A := ℂ) (B := ReducedCrossedProduct (scalarAction Γ))
      (C := ReducedCrossedProduct (coefficientAction Γ (B := B)))
      («α» := CStarAlgebraAction.trivial) («β» := descendedScalarAction Γ)
      (γ := descendedCoefficientAction Γ (B := B))
      true (scalarInclusion Γ) (scalarCoefficient_equivariant Γ)
        (KasparovDescent.oddClass (coefficientAction Γ (B := B)) (scalarAction Γ) (OddKK.mk c)) =
      GroupUniverseOrdinaryOdd.coefficientPushforward.{uB,max uΓ uB,max u uB}
        (B := B) (C := ReducedCrossedProduct (coefficientAction Γ (B := B)))
        (coefficientInclusion Γ (B := B))
        (OddKK.mk (BundledOddKasparovCycle.of (oddCycleComap (fromUnitHom (Γ := Γ)) c.cycle)))
  rw [KasparovDescent.oddClass_mk, NativeSourcePullback.odd_mk]
  change (OddKK.mk (BundledOddKasparovCycle.of
      (NativeSourcePullback.oddCycle CStarAlgebraAction.trivial (scalarInclusion Γ)
        (scalarCoefficient_equivariant Γ)
        (KasparovDescent.oddCycle (coefficientAction Γ (B := B)) (scalarAction Γ) c.cycle))) :
      OddKK.{0,0,max uΓ uB,max u uΓ uB} CStarAlgebraAction.trivial
        (descendedCoefficientAction Γ (B := B))) = _
  exact (OddKK.mk_eq_of_iso (oddCoefficientRestrictionIso Γ c.cycle)).trans
    (GroupUniverseOrdinaryOdd.coefficientPushforward_mk_coefficientTensor
      (oddCycleComap (fromUnitHom (Γ := Γ)) c.cycle) (coefficientInclusion Γ (B := B))).symm

end BC4lean.KKTheory.SubsingletonScalarDescent

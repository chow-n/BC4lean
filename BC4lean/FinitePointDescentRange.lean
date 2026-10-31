import BC4lean.FinitePointCompressedDescent

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! The point Green–Julg map of a general cycle.

Let `Γ` be finite with `n = |Γ|`, and let `c = (E, U, π, F)` be a `Γ`-equivariant cycle from
`C₀(pt)` to `ℂ`. Descent followed by the cutoff product sends `[c]` to the class of the range
cycle: the support cycle of the descended cycle pulled back along `z ↦ z • e`, where
`e = n⁻¹ ∑_g δ_g` is the averaging projection. Both parities.

On `E ⊗ C*_r(Γ)` that support projection is `Q = n⁻¹ ∑_g π(1) U_g ⊗ λ_g`; when the point acts
unitally it is `Q_U = n⁻¹ ∑_g U_g ⊗ λ_g`. No assumption on `U` is made: this generalizes
`FinitePointCharacterTensor.reducedSourceRepresentation_averaging_mk`, where `U_g = χ(g)`. -/

noncomputable section
namespace BC4lean.KKTheory.FinitePointDescentRange
open BC4lean.ProperActions BC4lean.OperatorKTheory BC4lean.Chapter8Examples
open KKTheory.GroupUniverseParityGroup KKTheory.GroupUniverseParityFunctoriality
open KKTheory.FinitePointCharacterTensor KKTheory.FinitePointCompressedDescent
open scoped ZeroAtInfty ComplexOrder KasparovDescent InnerProductSpace

section Projection
variable {Γ : Type} [Group Γ] [Fintype Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul ℂᵐᵒᵖ E]
  [CStarModule ℂᵐᵒᵖ E] [CompleteSpace E]
variable (U : EquivariantHilbertModule (scalarAction Γ) E)
  (π : C₀(FiniteGroupPoint.{0}, ℂ) →⋆ₙₐ[ℂ] AdjointableMap ℂ E E)
  (hπ : ∀ g a, U.conjugateOperator g (π a) = π ((pointAction Γ).automorphism g a))

/-- The averaging element acts on the descended module as `n⁻¹ ∑_g π(1) U_g ⊗ λ_g`. -/
theorem averaging_mk (x : E) (d : (GroupCrossed Γ)ᵐᵒᵖ) :
    KasparovDescent.reducedSourceRepresentation (scalarAction Γ) E (pointAction Γ) U π hπ
        (FinitePointCutoff.averaging Γ) (KasparovDescent.mk (scalarAction Γ) E x d) =
      ∑ g : Γ, (Fintype.card Γ : ℂ)⁻¹ • KasparovDescent.mk (scalarAction Γ) E
        (π (pointScalar 1) (U.action g x)) (MulOpposite.op (regular Γ g * MulOpposite.unop d)) := by
  have hscalar : pointScalar ((Fintype.card Γ : ℂ)⁻¹) =
      (Fintype.card Γ : ℂ)⁻¹ • pointScalar 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [averaging_eq_sum, map_sum, finiteAdjointable_sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [KasparovDescent.reducedSourceRepresentation_single, KasparovDescent.sourceGenerator_mk,
    leftRegular_eq_mul, hscalar, map_smul, AdjointableMap.coe_smul_apply]
  unfold KasparovDescent.mk
  exact LinearMap.map_smul₂ _ _ _ _

/-- With the point acting unitally, the averaging element acts as `Q_U = n⁻¹ ∑_g U_g ⊗ λ_g`. -/
theorem averaging_mk_of_unital (h1 : π (pointScalar 1) = 1) (x : E) (d : (GroupCrossed Γ)ᵐᵒᵖ) :
    KasparovDescent.reducedSourceRepresentation (scalarAction Γ) E (pointAction Γ) U π hπ
        (FinitePointCutoff.averaging Γ) (KasparovDescent.mk (scalarAction Γ) E x d) =
      ∑ g : Γ, (Fintype.card Γ : ℂ)⁻¹ • KasparovDescent.mk (scalarAction Γ) E
        (U.action g x) (MulOpposite.op (regular Γ g * MulOpposite.unop d)) := by
  rw [averaging_mk, h1]
  rfl

end Projection

section Class
variable {Γ : Type} [Group Γ] [Fintype Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul ℂᵐᵒᵖ E]
  [CStarModule ℂᵐᵒᵖ E] [CompleteSpace E]

local instance pointCZero_separable :
    TopologicalSpace.SeparableSpace C₀(FiniteGroupPoint.{0}, ℂ) :=
  TopologicalKHomology.cZero_separableSpace

/-- The range cycle of an even cycle: the support cycle of its pulled-back descent, on the
range of `Q = n⁻¹ ∑_g π(1) U_g ⊗ λ_g`. -/
abbrev rangeCycle (c : KasparovCycle (pointAction Γ) (scalarAction Γ) E) :=
  (pulledDescent c).scalarSupportCycle

/-- The range cycle of an odd cycle. -/
abbrev oddRangeCycle (c : OddKasparovCycle (pointAction Γ) (scalarAction Γ) E) :=
  (oddPulledDescent c).scalarSupportCycle

/-- The support projection of the pulled-back descent is `n⁻¹ ∑_g π(1) U_g ⊗ λ_g`. -/
theorem pulledDescent_support_mk (c : KasparovCycle (pointAction Γ) (scalarAction Γ) E)
    (x : E) (d : (GroupCrossed Γ)ᵐᵒᵖ) :
    (pulledDescent c).scalarSupportProjection (KasparovDescent.mk (scalarAction Γ) E x d) =
      ∑ g : Γ, (Fintype.card Γ : ℂ)⁻¹ • KasparovDescent.mk (scalarAction Γ) E
        (c.representation (pointScalar 1) (c.groupAction.action g x))
        (MulOpposite.op (regular Γ g * MulOpposite.unop d)) := by
  change KasparovDescent.reducedSourceRepresentation (scalarAction Γ) E (pointAction Γ)
    c.groupAction c.representation c.representation_equivariant
    ((1 : ℂ) • FinitePointCutoff.averaging Γ) _ = _
  rw [one_smul]
  exact averaging_mk c.groupAction c.representation c.representation_equivariant x d

/-- The odd support projection of the pulled-back descent is `n⁻¹ ∑_g π(1) U_g ⊗ λ_g`. -/
theorem oddPulledDescent_support_mk (c : OddKasparovCycle (pointAction Γ) (scalarAction Γ) E)
    (x : E) (d : (GroupCrossed Γ)ᵐᵒᵖ) :
    (oddPulledDescent c).scalarSupportProjection (KasparovDescent.mk (scalarAction Γ) E x d) =
      ∑ g : Γ, (Fintype.card Γ : ℂ)⁻¹ • KasparovDescent.mk (scalarAction Γ) E
        (c.representation (pointScalar 1) (c.groupAction.action g x))
        (MulOpposite.op (regular Γ g * MulOpposite.unop d)) := by
  change KasparovDescent.reducedSourceRepresentation (scalarAction Γ) E (pointAction Γ)
    c.groupAction c.representation c.representation_equivariant
    ((1 : ℂ) • FinitePointCutoff.averaging Γ) _ = _
  rw [one_smul]
  exact averaging_mk c.groupAction c.representation c.representation_equivariant x d

/-- The source pullback of the descent of `[c]` along `z ↦ z • e` is the class of the
pulled-back descended cycle. -/
theorem pulledDescent_class (c : KasparovCycle (pointAction Γ) (scalarAction Γ) E) :
    sourcePullback.{0,0,0,0,0} (Γ := Unit) (A := ℂ)
        (B := ReducedCrossedProduct (pointAction Γ)) (C := GroupCrossed Γ)
        («α» := (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)) («β» := CStarAlgebraAction.trivial) («γ» := CStarAlgebraAction.trivial)
        false (FinitePointCutoff.averagingHom Γ) averagingHom_equivariant
        (KasparovDescent.evenClass (scalarAction Γ) (pointAction Γ)
          (KasparovHomotopyClass.mk (BundledKasparovCycle.of c))) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of (pulledDescent c)) := by
  rw [KasparovDescent.evenClass_mk, NativeSourcePullback.even_mk]
  rfl

/-- Odd case of `pulledDescent_class`. -/
theorem oddPulledDescent_class (c : OddKasparovCycle (pointAction Γ) (scalarAction Γ) E) :
    sourcePullback.{0,0,0,0,0} (Γ := Unit) (A := ℂ)
        (B := ReducedCrossedProduct (pointAction Γ)) (C := GroupCrossed Γ)
        («α» := (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)) («β» := CStarAlgebraAction.trivial) («γ» := CStarAlgebraAction.trivial)
        true (FinitePointCutoff.averagingHom Γ) averagingHom_equivariant
        (KasparovDescent.oddClass (scalarAction Γ) (pointAction Γ)
          (OddKK.mk (BundledOddKasparovCycle.of c))) =
      OddKK.mk (BundledOddKasparovCycle.of (oddPulledDescent c)) := by
  rw [KasparovDescent.oddClass_mk, NativeSourcePullback.odd_mk]
  rfl

/-- Even case: the cutoff product of the descent of `[c]` is the class of the range cycle. -/
theorem even_cutoffProduct_descent (cf : Cutoff.CutoffFunction Γ FiniteGroupPoint.{0})
    (c : KasparovCycle (pointAction Γ) (scalarAction Γ) E) :
    Assembly.cutoffProductHom Γ FiniteGroupPoint.{0} false cf
        (KasparovDescent.classHom (scalarAction Γ) (pointAction Γ) false
          (KasparovHomotopyClass.mk (BundledKasparovCycle.of c))) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of (rangeCycle c)) := by
  rw [FinitePointCutoff.cutoffProductHom_eq_averagingPullback, KasparovDescent.classHom_even]
  exact (pulledDescent_class c).trans (KasparovCycle.scalarSupport_class _)

/-- Odd case: the cutoff product of the descent of `[c]` is the class of the range cycle. -/
theorem odd_cutoffProduct_descent (cf : Cutoff.CutoffFunction Γ FiniteGroupPoint.{0})
    (c : OddKasparovCycle (pointAction Γ) (scalarAction Γ) E) :
    Assembly.cutoffProductHom Γ FiniteGroupPoint.{0} true cf
        (KasparovDescent.classHom (scalarAction Γ) (pointAction Γ) true
          (OddKK.mk (BundledOddKasparovCycle.of c))) =
      OddKK.mk (BundledOddKasparovCycle.of (oddRangeCycle c)) := by
  rw [FinitePointCutoff.cutoffProductHom_eq_averagingPullback, KasparovDescent.classHom_odd]
  exact (oddPulledDescent_class c).trans (OddKasparovCycle.scalarSupport_class _)

end Class

end BC4lean.KKTheory.FinitePointDescentRange

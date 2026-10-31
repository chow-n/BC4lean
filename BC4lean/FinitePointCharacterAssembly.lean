import BC4lean.OperatorKProductEquiv
import BC4lean.FinitePointCompressedDescent
import BC4lean.KasparovTrivialInflation
import BC4lean.ReducedScalarKKComparison
import BC4lean.AssemblyPieceHom
import BC4lean.OddKTheoryIndependentCoefficientNaturality
import BC4lean.ScalarKasparovK0ComparisonNaturality
import BC4lean.UnitAssemblyEquivalence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Assembly of character-twisted point classes

Let `Γ` be a finite group and `χ : Γ → U(1)` a character. A class of `KK_p(ℂ, ℂ)`, pulled back to
`C₀(pt)`, inflated along `Γ → 1` and twisted by `χ`, is a class of `KK^Γ_p(C₀(pt), ℂ)`. On such a
class the point assembly map is computed explicitly: cutoff product and descent give the coefficient
extension along `z ↦ z • P_χ`, where `P_χ = |Γ|⁻¹ ∑_g χ(g) λ_g`, and the scalar index theorem
then gives `(P_χ)_* [a]` in `K_p(C*_r Γ)` (`spaceAssembly_even_class`, `spaceAssembly_odd_class`).
This is the part of the order-two computation that holds for every finite group.
-/

noncomputable section

namespace BC4lean.Chapter8Examples.FinitePointAssembly
open ProperActions KKTheory OperatorKTheory
open KKTheory.GroupUniverseParityGroup KKTheory.GroupUniverseParityFunctoriality
open KKTheory.FinitePointCompressedDescent KKTheory.FinitePointCharacterTensor KKTheory.FinitePointCutoff
open scoped ZeroAtInfty ComplexOrder KasparovDescent

variable {Γ : Type} [Group Γ] [Countable Γ] [Fintype Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul ℂᵐᵒᵖ E]
  [CStarModule ℂᵐᵒᵖ E] [CompleteSpace E]

/-- The scalar crossed product identified with `C*_r(Γ)`. -/
abbrev crossedHom (Γ : Type) [Group Γ] [Countable Γ] : GroupCrossed Γ →⋆ₙₐ[ℂ] ReducedGroupCStar Γ :=
  (reducedCrossedScalarProductEquiv (Γ := Γ)).toNonUnitalStarAlgHom

/-- Assembly of an even point cycle on which `Γ` acts through `χ` and the point unitally:
`P_χ` pushed forward along the underlying scalar class. -/
theorem spaceAssembly_even_mk (c0 : Cutoff.CutoffFunction Γ FiniteGroupPoint.{0})
    (χ : Γ →* unitary ℂ) (c : KasparovCycle (pointAction Γ) (scalarAction Γ) E)
    (hU : ∀ g x, c.groupAction.action g x = (χ g : ℂ) • x)
    (h1 : c.representation (pointScalar 1) = 1) :
    Assembly.spaceAssemblyHom Γ FiniteGroupPoint.{0} false c0
        (KasparovHomotopyClass.mk (BundledKasparovCycle.of c)) =
      letI : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
      letI : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
      operatorK0UnitalEquiv (ReducedGroupCStar Γ)
        (operatorK0Map ((crossedHom Γ).comp (characterHom Γ χ))
          (scalarKKOperatorK0AddEquiv
            (KasparovHomotopyClass.mk (BundledKasparovCycle.of (pointScalarCycle c))))) := by
  change Assembly.reducedScalarKKToAnalyticHom Γ false (Assembly.cutoffProductHom Γ FiniteGroupPoint.{0} false c0
    (KasparovDescent.classHom (scalarAction Γ) (pointAction Γ) false
      (KasparovHomotopyClass.mk (BundledKasparovCycle.of c)))) = _
  rw [cutoffProductHom_eq_averagingPullback]
  erw [even_compressedDescent χ c hU h1]
  let : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
  change operatorK0UnitalEquiv (ReducedGroupCStar Γ) (operatorK0Map (crossedHom Γ)
    (scalarKKOperatorK0AddEquiv (GroupUniverseOrdinaryEven.coefficientPushforward.{0,0,0}
      (characterHom Γ χ) _))) = _
  rw [scalarKKOperatorK0AddEquiv_natural, ← AddMonoidHom.comp_apply, ← operatorK0Map_comp]

/-- Odd analogue of `spaceAssembly_even_mk`. -/
theorem spaceAssembly_odd_mk (c0 : Cutoff.CutoffFunction Γ FiniteGroupPoint.{0})
    (χ : Γ →* unitary ℂ) (c : OddKasparovCycle (pointAction Γ) (scalarAction Γ) E)
    (hU : ∀ g x, c.groupAction.action g x = (χ g : ℂ) • x)
    (h1 : c.representation (pointScalar 1) = 1) :
    Assembly.spaceAssemblyHom Γ FiniteGroupPoint.{0} true c0
        (OddKK.mk (BundledOddKasparovCycle.of c)) =
      letI : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
      letI : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
      operatorK1UnitalEquiv (ReducedGroupCStar Γ)
        (operatorK1Map ((crossedHom Γ).comp (characterHom Γ χ))
          (oddKKOperatorK1AllModuleUniversesAddEquiv
            (OddKK.mk (BundledOddKasparovCycle.of (oddPointScalarCycle c))))) := by
  change Assembly.reducedScalarKKToAnalyticHom Γ true (Assembly.cutoffProductHom Γ FiniteGroupPoint.{0} true c0
    (KasparovDescent.classHom (scalarAction Γ) (pointAction Γ) true
      (OddKK.mk (BundledOddKasparovCycle.of c)))) = _
  rw [cutoffProductHom_eq_averagingPullback]
  erw [odd_compressedDescent χ c hU h1]
  let : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
  change operatorK1UnitalEquiv (ReducedGroupCStar Γ) (operatorK1Map (crossedHom Γ)
    (oddKKOperatorK1AllModuleUniversesAddEquiv (GroupUniverseOrdinaryOdd.coefficientPushforward.{0,0,0}
      (characterHom Γ χ) _))) = _
  simp only [oddKKOperatorK1AllModuleUniversesAddEquiv_apply]
  rw [oddKKOperatorK1Index_independentCoefficientPushforward, ← AddMonoidHom.comp_apply,
    ← operatorK1Map_comp]

/-- Evaluation at the point, the inverse of `ℂ ≅ C₀(pt)`. -/
abbrev pointEval : C₀(FiniteGroupPoint.{0}, ℂ) →⋆ₙₐ[ℂ] ℂ :=
  ((UnitPointCutoff.pointCZeroEquiv FiniteGroupPoint.{0} default).symm : C₀(FiniteGroupPoint.{0}, ℂ) →⋆ₙₐ[ℂ] ℂ)

/-- Evaluation at the point is equivariant for the trivial actions. -/
theorem pointEval_equivariant : ∀ (k : Unit) (a : C₀(FiniteGroupPoint.{0}, ℂ)),
    pointEval ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit C₀(FiniteGroupPoint.{0}, ℂ)).automorphism k a) =
      unitScalarAction.automorphism k (pointEval a) := fun _ _ => rfl

variable (Γ) in
/-- A scalar cycle over the trivial group, read over the point, inflated to `Γ` and twisted by `χ`. -/
abbrev inflatedCycle (χ : Γ →* unitary ℂ) (c : KasparovCycle unitScalarAction unitScalarAction E) :
    KasparovCycle (pointAction Γ) (scalarAction Γ) E :=
  ((NativeSourcePullback.evenCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Unit C₀(FiniteGroupPoint.{0}, ℂ))
    pointEval pointEval_equivariant c).comap (1 : Γ →* Unit)
    (CStarAlgebraAction.apply_eq_trivial_unit (pointAction Γ))
    (CStarAlgebraAction.apply_eq_trivial_unit (scalarAction Γ))).twist χ

/-- `spaceAssembly_even_mk` for an inflated, twisted cycle with unital scalar representation. -/
theorem spaceAssembly_even_inflated (c0 : Cutoff.CutoffFunction Γ FiniteGroupPoint.{0})
    (χ : Γ →* unitary ℂ) (c : KasparovCycle unitScalarAction unitScalarAction E) (h1 : ∀ z x, c.representation z x = z • x) :
    Assembly.spaceAssemblyHom Γ FiniteGroupPoint.{0} false c0
        (KasparovHomotopyClass.mk (BundledKasparovCycle.of (inflatedCycle Γ χ c))) =
      letI : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
      letI : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
      operatorK0UnitalEquiv (ReducedGroupCStar Γ)
        (operatorK0Map ((crossedHom Γ).comp (characterHom Γ χ))
          (scalarKKOperatorK0AddEquiv (KasparovHomotopyClass.mk (BundledKasparovCycle.of c)))) := by
  have hU : ∀ g x, (inflatedCycle Γ χ c).groupAction.action g x = (χ g : ℂ) • x := by
    intro g x
    change (χ g : ℂ) • c.groupAction.action ((1 : Γ →* Unit) g) x = _
    rw [MonoidHom.one_apply, EquivariantHilbertModule.one_apply]
  have h1' : (inflatedCycle Γ χ c).representation (pointScalar 1) = 1 := by
    ext x
    exact (h1 1 x).trans (one_smul ℂ x)
  rw [spaceAssembly_even_mk c0 χ _ hU h1']
  congr 3

variable (Γ) in
/-- The odd analogue of `inflatedCycle`. -/
abbrev oddInflatedCycle (χ : Γ →* unitary ℂ) (c : OddKasparovCycle unitScalarAction unitScalarAction E) :
    OddKasparovCycle (pointAction Γ) (scalarAction Γ) E :=
  ((NativeSourcePullback.oddCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Unit C₀(FiniteGroupPoint.{0}, ℂ))
    pointEval pointEval_equivariant c).comap (1 : Γ →* Unit)
    (CStarAlgebraAction.apply_eq_trivial_unit (pointAction Γ))
    (CStarAlgebraAction.apply_eq_trivial_unit (scalarAction Γ))).twist χ

/-- Odd analogue of `spaceAssembly_even_inflated`. -/
theorem spaceAssembly_odd_inflated (c0 : Cutoff.CutoffFunction Γ FiniteGroupPoint.{0})
    (χ : Γ →* unitary ℂ) (c : OddKasparovCycle unitScalarAction unitScalarAction E) (h1 : ∀ z x, c.representation z x = z • x) :
    Assembly.spaceAssemblyHom Γ FiniteGroupPoint.{0} true c0
        (OddKK.mk (BundledOddKasparovCycle.of (oddInflatedCycle Γ χ c))) =
      letI : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
      letI : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
      operatorK1UnitalEquiv (ReducedGroupCStar Γ)
        (operatorK1Map ((crossedHom Γ).comp (characterHom Γ χ))
          (oddKKOperatorK1AllModuleUniversesAddEquiv (OddKK.mk (BundledOddKasparovCycle.of c)))) := by
  have hU : ∀ g x, (oddInflatedCycle Γ χ c).groupAction.action g x = (χ g : ℂ) • x := by
    intro g x
    change (χ g : ℂ) • c.groupAction.action ((1 : Γ →* Unit) g) x = _
    rw [MonoidHom.one_apply, EquivariantHilbertModule.one_apply]
  have h1' : (oddInflatedCycle Γ χ c).representation (pointScalar 1) = 1 := by
    ext x
    exact (h1 1 x).trans (one_smul ℂ x)
  rw [spaceAssembly_odd_mk c0 χ _ hU h1']
  congr 3

local instance pointCZero_separable : TopologicalSpace.SeparableSpace C₀(FiniteGroupPoint.{0}, ℂ) :=
  TopologicalKHomology.cZero_separableSpace

omit [Countable Γ] [Fintype Γ] in
/-- Twisting by the trivial character is the identity on even classes. -/
theorem twist_one_even (x : KasparovHomotopyClass.{0,0,0,0} (pointAction Γ) (scalarAction Γ)) :
    KasparovHomotopyClass.twist (1 : Γ →* unitary ℂ) x = x := by
  induction x using Quotient.inductionOn with
  | h c => exact KasparovHomotopyClass.mk_eq_of_iso (c.cycle.twistTrivialIso 1 fun _ => rfl)

omit [Countable Γ] [Fintype Γ] in
/-- Twisting by the trivial character is the identity on odd classes. -/
theorem twist_one_odd (x : OddKK.{0,0,0,0} (pointAction Γ) (scalarAction Γ)) :
    OddKK.twist (1 : Γ →* unitary ℂ) x = x := by
  induction x using Quotient.inductionOn with
  | h c => exact OddKK.mk_eq_of_iso (c.cycle.twistTrivialIso 1 fun _ => rfl)

/-- Class form, even: inflate the pulled-back class, twist by `χ`, assemble. -/
theorem spaceAssembly_even_class (c0 : Cutoff.CutoffFunction Γ FiniteGroupPoint.{0})
    (χ : Γ →* unitary ℂ) (a : KasparovHomotopyClass.{0,0,0,0} unitScalarAction unitScalarAction) :
    Assembly.spaceAssemblyHom Γ FiniteGroupPoint.{0} false c0
        (KasparovHomotopyClass.twist χ (KasparovHomotopyClass.comap (1 : Γ →* Unit)
          (CStarAlgebraAction.apply_eq_trivial_unit (pointAction Γ))
          (CStarAlgebraAction.apply_eq_trivial_unit (scalarAction Γ))
          (sourcePullback.{0,0,0,0,0} false pointEval pointEval_equivariant a))) =
      letI : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
      letI : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
      operatorK0UnitalEquiv (ReducedGroupCStar Γ)
        (operatorK0Map ((crossedHom Γ).comp (characterHom Γ χ)) (scalarKKOperatorK0AddEquiv a)) := by
  induction a using Quotient.inductionOn with
  | h c =>
    cases c with | mk F c =>
    have h := KasparovCycle.scalarSupport_class c
    refine (congrArg (fun y => Assembly.spaceAssemblyHom Γ FiniteGroupPoint.{0} false c0
      (KasparovHomotopyClass.twist χ (KasparovHomotopyClass.comap (1 : Γ →* Unit)
        (CStarAlgebraAction.apply_eq_trivial_unit (pointAction Γ))
        (CStarAlgebraAction.apply_eq_trivial_unit (scalarAction Γ))
        (sourcePullback.{0,0,0,0,0} false pointEval pointEval_equivariant y)))) h).trans ?_
    erw [NativeSourcePullback.even_mk, spaceAssembly_even_inflated c0 χ _
      (fun z x => c.scalarSupportRepresentation_apply z x)]
    erw [← h]
    rfl

/-- Class form, odd. -/
theorem spaceAssembly_odd_class (c0 : Cutoff.CutoffFunction Γ FiniteGroupPoint.{0})
    (χ : Γ →* unitary ℂ) (a : OddKK.{0,0,0,0} unitScalarAction unitScalarAction) :
    Assembly.spaceAssemblyHom Γ FiniteGroupPoint.{0} true c0
        (OddKK.twist χ (OddKK.comap (1 : Γ →* Unit)
          (CStarAlgebraAction.apply_eq_trivial_unit (pointAction Γ))
          (CStarAlgebraAction.apply_eq_trivial_unit (scalarAction Γ))
          (sourcePullback.{0,0,0,0,0} true pointEval pointEval_equivariant a))) =
      letI : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
      letI : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
      operatorK1UnitalEquiv (ReducedGroupCStar Γ)
        (operatorK1Map ((crossedHom Γ).comp (characterHom Γ χ))
          (oddKKOperatorK1AllModuleUniversesAddEquiv a)) := by
  induction a using Quotient.inductionOn with
  | h c =>
    cases c with | mk F c =>
    have h := OddKasparovCycle.scalarSupport_class c
    refine (congrArg (fun y => Assembly.spaceAssemblyHom Γ FiniteGroupPoint.{0} true c0
      (OddKK.twist χ (OddKK.comap (1 : Γ →* Unit)
        (CStarAlgebraAction.apply_eq_trivial_unit (pointAction Γ))
        (CStarAlgebraAction.apply_eq_trivial_unit (scalarAction Γ))
        (sourcePullback.{0,0,0,0,0} true pointEval pointEval_equivariant y)))) h).trans ?_
    erw [NativeSourcePullback.odd_mk, spaceAssembly_odd_inflated c0 χ _
      (fun z x => c.scalarSupportRepresentation_apply z x)]
    erw [← h]
    rfl

section Algebra

omit [Countable Γ] [Fintype Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- The crossed-product equivalence sends `λ_g` to the left regular operator. -/
theorem crossedHom_regular [Countable Γ] (g : Γ) :
    crossedHom Γ (regular Γ g) = ⟨regularOperator g, regularOperator_mem_reducedAlgebra g⟩ := by
  apply Subtype.ext
  have h : reducedCrossedGenerator (scalarAction Γ) 1 g = reducedCrossedRegular g := by
    rw [reducedCrossedGenerator, reducedCrossedCoefficient_scalar, one_smul, one_mul]
  change reducedCrossedScalarOperatorEquiv (reducedCrossedRegular g) = regularOperator g
  rw [← h, reducedCrossedScalarOperatorEquiv_generator, one_smul]


omit [Countable Γ] [Fintype Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- `*`-homomorphisms out of `ℂ` agree once they agree at `1`. -/
theorem scalarHom_ext {R : Type*} [NonUnitalCStarAlgebra R] {f f' : ℂ →⋆ₙₐ[ℂ] R}
    (h : f 1 = f' 1) : f = f' := by
  ext z
  rw [show z = z • (1 : ℂ) by simp, map_smul, map_smul, h]

end Algebra

end BC4lean.Chapter8Examples.FinitePointAssembly

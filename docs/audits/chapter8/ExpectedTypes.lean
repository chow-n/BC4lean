import BC4lean.BaumConnesProperty
import BC4lean.BaumConnesInvariance
import BC4lean.AssemblyBijectivityCriteria
import BC4lean.TrivialAnalyticCalibration
import BC4lean.CompactModelColimitCalibration
import BC4lean.FiniteGroupPointCalibration
import BC4lean.UnitScalarDescent
import BC4lean.ScalarUnitProjection
import BC4lean.UnitPointCutoff
import BC4lean.UnitAssemblyEquivalence
import BC4lean.FinitePointCutoff
import BC4lean.KKGroupRestriction
import BC4lean.SubsingletonScalarDescent
import BC4lean.ScalarIdentityUniverse
import BC4lean.SubsingletonAssemblyEquivalence
import BC4lean.TrivialAnalyticScalar

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-!
Independent source-only expected mathematical signatures, prepared without a
Lean invocation. The first ten imports denote the ten proposed final module
locations; the eleventh supplies the finite-point cutoff endpoints, the next
four the endpoints for groups with one element, and the last their scalar
K-group endpoints.
No native acceptance is claimed by this file. A source hash change requires a
fresh review before the fixture becomes an acceptance input.

Each example states a mathematical type explicitly and supplies the endpoint
as its witness. The property and conjecture bodies are checked by definitional
equality against explicit quantification over the actual canonical assembly
map. There is no `#check`, declaration-type quotation, or theorem concluding
the general conjecture. Constant kinds require the separate auditor checks.
-/

noncomputable section
universe u uΓ uX uJ uL uI uV uB uE
namespace Chapter8ExpectedTypes
open BC4lean BC4lean.ProperActions BC4lean.KKTheory BC4lean.OperatorKTheory
open scoped ZeroAtInfty ComplexOrder KasparovDescent

section Property
variable (Γ : Type u) [Group Γ] [Countable Γ]
  [TopologicalSpace Γ] [DiscreteTopology Γ]

-- endpoint: BC4lean.Assembly.BaumConnesProperty (definition body)
example : Assembly.BaumConnesProperty Γ ↔
    ∀ p : Bool, Function.Bijective (Assembly.reducedAssemblyHom Γ p) := Iff.rfl

-- endpoint: BC4lean.Assembly.baumConnesProperty_iff_even_and_odd
example : Assembly.BaumConnesProperty Γ ↔
    Function.Bijective (Assembly.reducedAssemblyEvenHom Γ) ∧
    Function.Bijective (Assembly.reducedAssemblyOddHom Γ) :=
  Assembly.baumConnesProperty_iff_even_and_odd Γ

end Property

-- endpoint: BC4lean.Assembly.BaumConnesConjecture (definition body)
-- This equivalence does not provide a witness of either side.
example : Assembly.BaumConnesConjecture.{u} ↔
    ∀ (G : Type u) [Group G] [Countable G]
      [TopologicalSpace G] [DiscreteTopology G],
      ∀ p : Bool, Function.Bijective (Assembly.reducedAssemblyHom G p) := Iff.rfl

section ProperSpaces
variable (Γ : Type uΓ) [Group Γ] [Countable Γ]
  [TopologicalSpace Γ] [DiscreteTopology Γ]
  (X : Type uX) [TopologicalSpace X] [MulAction Γ X]
  [ContinuousConstSMul Γ X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [ProperSMul Γ X]

-- endpoint: BC4lean.Assembly.modelAssemblyProperty (definition body)
example : Assembly.modelAssemblyProperty Γ X ↔
    ∀ p : Bool, Function.Bijective (Assembly.assemblyHom Γ X p) := Iff.rfl

section Homotopy
variable (Y : Type uX) [TopologicalSpace Y] [MulAction Γ Y]
  [ContinuousConstSMul Γ Y] [LocallyCompactSpace Y] [T2Space Y]
  [SecondCountableTopology Y] [ProperSMul Γ Y]

-- endpoint: BC4lean.Assembly.assemblyHom_injective_iff_homotopyEquiv
example (p : Bool) (e : EquivariantHomotopyEquiv Γ X Y) :
    Function.Injective (Assembly.assemblyHom Γ X p) ↔
      Function.Injective (Assembly.assemblyHom Γ Y p) :=
  Assembly.assemblyHom_injective_iff_homotopyEquiv Γ X Y p e

-- endpoint: BC4lean.Assembly.assemblyHom_surjective_iff_homotopyEquiv
example (p : Bool) (e : EquivariantHomotopyEquiv Γ X Y) :
    Function.Surjective (Assembly.assemblyHom Γ X p) ↔
      Function.Surjective (Assembly.assemblyHom Γ Y p) :=
  Assembly.assemblyHom_surjective_iff_homotopyEquiv Γ X Y p e

-- endpoint: BC4lean.Assembly.assemblyHom_bijective_iff_homotopyEquiv
example (p : Bool) (e : EquivariantHomotopyEquiv Γ X Y) :
    Function.Bijective (Assembly.assemblyHom Γ X p) ↔
      Function.Bijective (Assembly.assemblyHom Γ Y p) :=
  Assembly.assemblyHom_bijective_iff_homotopyEquiv Γ X Y p e

-- endpoint: BC4lean.Assembly.modelAssemblyProperty_iff_homotopyEquiv
example (e : EquivariantHomotopyEquiv Γ X Y) :
    Assembly.modelAssemblyProperty Γ X ↔ Assembly.modelAssemblyProperty Γ Y :=
  Assembly.modelAssemblyProperty_iff_homotopyEquiv Γ X Y e

end Homotopy

section Cofinal
variable {J : Type uJ} [Preorder J] [Nonempty J] [IsDirectedOrder J]
  {L : Type uL} [Preorder L] [Nonempty L] [IsDirectedOrder L]

-- endpoint: BC4lean.Assembly.indexedAssemblyProperty (definition body)
example (φ : J →o CocompactPiece Γ X) :
    Assembly.indexedAssemblyProperty Γ X φ ↔
      ∀ p : Bool, Function.Bijective (Assembly.indexedAssemblyHom Γ X p φ) := Iff.rfl

-- endpoint: BC4lean.Assembly.indexedAssemblyHom_injective_iff_cofinalIndex
example (p : Bool) (φ : J →o CocompactPiece Γ X)
    (hφ : ∀ S : CocompactPiece Γ X, ∃ j, S ≤ φ j) :
    Function.Injective (Assembly.indexedAssemblyHom Γ X p φ) ↔
      Function.Injective (Assembly.assemblyHom Γ X p) :=
  Assembly.indexedAssemblyHom_injective_iff_cofinalIndex Γ X p φ hφ

-- endpoint: BC4lean.Assembly.indexedAssemblyHom_surjective_iff_cofinalIndex
example (p : Bool) (φ : J →o CocompactPiece Γ X)
    (hφ : ∀ S : CocompactPiece Γ X, ∃ j, S ≤ φ j) :
    Function.Surjective (Assembly.indexedAssemblyHom Γ X p φ) ↔
      Function.Surjective (Assembly.assemblyHom Γ X p) :=
  Assembly.indexedAssemblyHom_surjective_iff_cofinalIndex Γ X p φ hφ

-- endpoint: BC4lean.Assembly.indexedAssemblyHom_bijective_iff_cofinalIndex
example (p : Bool) (φ : J →o CocompactPiece Γ X)
    (hφ : ∀ S : CocompactPiece Γ X, ∃ j, S ≤ φ j) :
    Function.Bijective (Assembly.indexedAssemblyHom Γ X p φ) ↔
      Function.Bijective (Assembly.assemblyHom Γ X p) :=
  Assembly.indexedAssemblyHom_bijective_iff_cofinalIndex Γ X p φ hφ

-- endpoint: BC4lean.Assembly.indexedAssemblyProperty_iff_cofinalIndex
example (φ : J →o CocompactPiece Γ X)
    (hφ : ∀ S : CocompactPiece Γ X, ∃ j, S ≤ φ j) :
    Assembly.indexedAssemblyProperty Γ X φ ↔ Assembly.modelAssemblyProperty Γ X :=
  Assembly.indexedAssemblyProperty_iff_cofinalIndex Γ X φ hφ

-- endpoint: BC4lean.Assembly.indexedAssemblyHom_bijective_iff_cofinalComparison
example (p : Bool) (φ : J →o CocompactPiece Γ X) (ψ : L →o CocompactPiece Γ X)
    (hφ : ∀ S : CocompactPiece Γ X, ∃ j, S ≤ φ j)
    (hψ : ∀ S : CocompactPiece Γ X, ∃ j, S ≤ ψ j) :
    Function.Bijective (Assembly.indexedAssemblyHom Γ X p φ) ↔
      Function.Bijective (Assembly.indexedAssemblyHom Γ X p ψ) :=
  Assembly.indexedAssemblyHom_bijective_iff_cofinalComparison Γ X p φ ψ hφ hψ

-- endpoint: BC4lean.Assembly.indexedAssemblyProperty_iff_cofinalComparison
example (φ : J →o CocompactPiece Γ X) (ψ : L →o CocompactPiece Γ X)
    (hφ : ∀ S : CocompactPiece Γ X, ∃ j, S ≤ φ j)
    (hψ : ∀ S : CocompactPiece Γ X, ∃ j, S ≤ ψ j) :
    Assembly.indexedAssemblyProperty Γ X φ ↔ Assembly.indexedAssemblyProperty Γ X ψ :=
  Assembly.indexedAssemblyProperty_iff_cofinalComparison Γ X φ ψ hφ hψ

end Cofinal

-- endpoint: BC4lean.Assembly.assemblyHom_surjective_iff_pieceImages
example (p : Bool) : Function.Surjective (Assembly.assemblyHom Γ X p) ↔
    ∀ y : Assembly.analyticGroup Γ p,
      ∃ (S : CocompactPiece Γ X) (x : TopologicalKHomology.pieceGroup p S),
        Assembly.pieceAssemblyHom Γ X p S x = y :=
  Assembly.assemblyHom_surjective_iff_pieceImages Γ X p

-- endpoint: BC4lean.Assembly.assemblyHom_injective_iff_commonTransition
example (p : Bool) : Function.Injective (Assembly.assemblyHom Γ X p) ↔
    ∀ (S T : CocompactPiece Γ X)
      (x : TopologicalKHomology.pieceGroup p S)
      (y : TopologicalKHomology.pieceGroup p T),
      Assembly.pieceAssemblyHom Γ X p S x = Assembly.pieceAssemblyHom Γ X p T y →
        ∃ (U : CocompactPiece Γ X) (hSU : S ≤ U) (hTU : T ≤ U),
          TopologicalKHomology.transition p hSU x =
            TopologicalKHomology.transition p hTU y :=
  Assembly.assemblyHom_injective_iff_commonTransition Γ X p

-- endpoint: BC4lean.Assembly.assemblyHom_bijective_iff_pieceCriteria
example (p : Bool) : Function.Bijective (Assembly.assemblyHom Γ X p) ↔
    (∀ (S T : CocompactPiece Γ X)
      (x : TopologicalKHomology.pieceGroup p S)
      (y : TopologicalKHomology.pieceGroup p T),
      Assembly.pieceAssemblyHom Γ X p S x = Assembly.pieceAssemblyHom Γ X p T y →
        ∃ (U : CocompactPiece Γ X) (hSU : S ≤ U) (hTU : T ≤ U),
          TopologicalKHomology.transition p hSU x =
            TopologicalKHomology.transition p hTU y) ∧
    (∀ y : Assembly.analyticGroup Γ p,
      ∃ (S : CocompactPiece Γ X) (x : TopologicalKHomology.pieceGroup p S),
        Assembly.pieceAssemblyHom Γ X p S x = y) :=
  Assembly.assemblyHom_bijective_iff_pieceCriteria Γ X p

end ProperSpaces

section UniversalModels
-- The source API deliberately uses one common group/space universe here.
variable (Γ : Type uX) [Group Γ] [Countable Γ]
  [TopologicalSpace Γ] [DiscreteTopology Γ]
  (X Y : Type uX) [TopologicalSpace X] [TopologicalSpace Y]
  [MulAction Γ X] [MulAction Γ Y]
  [ContinuousConstSMul Γ X] [ContinuousConstSMul Γ Y]
  [LocallyCompactSpace X] [LocallyCompactSpace Y] [T2Space X] [T2Space Y]
  [SecondCountableTopology X] [SecondCountableTopology Y]

-- endpoint: BC4lean.Assembly.assemblyHom_bijective_iff_universalModels
example (p : Bool) (cX : EquivariantCWComplex (topologicalAction Γ X))
    (cY : EquivariantCWComplex (topologicalAction Γ Y))
    (hX : FixedPointCriterion Γ X) (hY : FixedPointCriterion Γ Y) :
    letI := cX.proper
    letI := cY.proper
    Function.Bijective (Assembly.assemblyHom Γ X p) ↔
      Function.Bijective (Assembly.assemblyHom Γ Y p) :=
  Assembly.assemblyHom_bijective_iff_universalModels Γ X Y p cX cY hX hY

-- endpoint: BC4lean.Assembly.modelAssemblyProperty_iff_universalModels
example (cX : EquivariantCWComplex (topologicalAction Γ X))
    (cY : EquivariantCWComplex (topologicalAction Γ Y))
    (hX : FixedPointCriterion Γ X) (hY : FixedPointCriterion Γ Y) :
    letI := cX.proper
    letI := cY.proper
    Assembly.modelAssemblyProperty Γ X ↔ Assembly.modelAssemblyProperty Γ Y :=
  Assembly.modelAssemblyProperty_iff_universalModels Γ X Y cX cY hX hY

-- endpoint: BC4lean.Assembly.assemblyHom_bijective_iff_canonical
example (p : Bool) (cX : EquivariantCWComplex (topologicalAction Γ X))
    (hX : FixedPointCriterion Γ X) :
    letI := cX.proper
    Function.Bijective (Assembly.assemblyHom Γ X p) ↔
      Function.Bijective (Assembly.reducedAssemblyHom Γ p) :=
  Assembly.assemblyHom_bijective_iff_canonical Γ X p cX hX

-- endpoint: BC4lean.Assembly.modelAssemblyProperty_iff_baumConnesProperty
example (cX : EquivariantCWComplex (topologicalAction Γ X))
    (hX : FixedPointCriterion Γ X) :
    letI := cX.proper
    Assembly.modelAssemblyProperty Γ X ↔ Assembly.BaumConnesProperty Γ :=
  Assembly.modelAssemblyProperty_iff_baumConnesProperty Γ X cX hX

end UniversalModels

open BC4lean.Chapter8Examples

section TrivialAnalyticTarget
variable (Γ : Type u) [Group Γ] [Subsingleton Γ]
local instance reducedOrder : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
local instance reducedStarOrder : StarOrderedRing (ReducedGroupCStar Γ) :=
  CStarAlgebra.spectralOrderedRing _

-- endpoint: BC4lean.Chapter8Examples.trivialAnalyticK0Equiv
example : K0 ℂ ≃+ ReducedK0 Γ := trivialAnalyticK0Equiv Γ

-- endpoint: BC4lean.Chapter8Examples.trivialAnalyticK1Equiv
example : K1 ℂ ≃+ ReducedK1 Γ := trivialAnalyticK1Equiv Γ

-- endpoint: BC4lean.Chapter8Examples.trivialAnalyticK0Equiv_projection
example (q : FiniteProjection ℂ) :
    trivialAnalyticK0Equiv Γ (k0Projection q) =
      k0Projection (FiniteProjection.map (trivialReducedEquiv (Γ := Γ)).toStarAlgHom q) :=
  trivialAnalyticK0Equiv_projection Γ q

-- endpoint: BC4lean.Chapter8Examples.trivialAnalyticK1Equiv_unitary
example (v : FiniteUnitary ℂ) :
    trivialAnalyticK1Equiv Γ (K1.of v) =
      K1.of (FiniteUnitary.map (trivialReducedEquiv (Γ := Γ)).toStarAlgHom v) :=
  trivialAnalyticK1Equiv_unitary Γ v

end TrivialAnalyticTarget

section TrivialScalarKGroups
variable (Γ : Type u) [Group Γ] [Subsingleton Γ]

-- endpoint: BC4lean.Chapter8Examples.trivialReducedK0Equiv
example : ReducedK0 Γ ≃+ ℤ := trivialReducedK0Equiv Γ

-- endpoint: BC4lean.Chapter8Examples.trivialReducedK0Equiv_one
example : trivialReducedK0Equiv Γ (trivialAnalyticK0Equiv Γ
    (k0Projection (FiniteProjection.ofProjection (Projection.one : MatrixProjection ℂ Unit)))) = 1 :=
  trivialReducedK0Equiv_one Γ

-- endpoint: BC4lean.Chapter8Examples.trivialReducedK1_eq_zero
example (x : ReducedK1 Γ) : x = 0 := trivialReducedK1_eq_zero Γ x

end TrivialScalarKGroups

section TerminalDiagram
variable {I : Type uI} [Preorder I] [Nonempty I] [IsDirectedOrder I]
  (D : DirectedAddGroupDiagram.{uI, uV} I) (t : I) (ht : ∀ i, i ≤ t)

-- endpoint: BC4lean.Chapter8Examples.terminalEvaluation
example : D.Colimit →+ D.obj t := terminalEvaluation D t ht

-- endpoint: BC4lean.Chapter8Examples.terminalColimitEquiv
example : D.Colimit ≃+ D.obj t := terminalColimitEquiv D t ht

-- endpoint: BC4lean.Chapter8Examples.terminalColimitEquiv_of
example (i : I) (x : D.obj i) :
    terminalColimitEquiv D t ht (D.of i x) = D.map i t (ht i) x :=
  terminalColimitEquiv_of D t ht i x

end TerminalDiagram

section CompactCalibration
variable (Γ : Type uΓ) [Group Γ] [Countable Γ]
  [TopologicalSpace Γ] [DiscreteTopology Γ]
  (X : Type uX) [TopologicalSpace X] [MulAction Γ X] [CompactSpace X]
  [ContinuousConstSMul Γ X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [ProperSMul Γ X]

-- endpoint: BC4lean.Chapter8Examples.wholeCompactPiece
example : CocompactPiece Γ X := wholeCompactPiece Γ X

-- endpoint: BC4lean.Chapter8Examples.le_wholeCompactPiece
example : ∀ S : CocompactPiece Γ X, S ≤ wholeCompactPiece Γ X := le_wholeCompactPiece Γ X

-- endpoint: BC4lean.Chapter8Examples.compactWholePieceEquiv
example (p : Bool) : TopologicalKHomology.group (Γ := Γ) (X := X) p ≃+
    TopologicalKHomology.pieceGroup p (wholeCompactPiece Γ X) := compactWholePieceEquiv Γ X p

-- endpoint: BC4lean.Chapter8Examples.compactSpaceGroupEquiv
example (p : Bool) : TopologicalKHomology.group (Γ := Γ) (X := X) p ≃+
    TopologicalKHomology.spaceGroup p Γ X := compactSpaceGroupEquiv Γ X p

-- endpoint: BC4lean.Chapter8Examples.assemblyHom_eq_compactSpaceAssembly
example (p : Bool) (c : Cutoff.CutoffFunction Γ X)
    (x : TopologicalKHomology.group (Γ := Γ) (X := X) p) :
    Assembly.assemblyHom Γ X p x =
      Assembly.spaceAssemblyHom Γ X p c (compactSpaceGroupEquiv Γ X p x) :=
  assemblyHom_eq_compactSpaceAssembly Γ X p c x

end CompactCalibration

section FinitePointCalibration
-- endpoint: BC4lean.Chapter8Examples.FiniteGroupPoint (definition body)
example : FiniteGroupPoint.{u} = ULift.{u} Unit := rfl

-- endpoint: BC4lean.Chapter8Examples.finiteGroupPoint_fixedPoints_contractible
example (Γ : Type u) [Group Γ] (H : Subgroup Γ) :
    ContractibleSpace (FixedPointSpace H FiniteGroupPoint.{u}) :=
  finiteGroupPoint_fixedPoints_contractible Γ H

variable (Γ : Type u) [Group Γ] [Finite Γ]
  [TopologicalSpace Γ] [DiscreteTopology Γ]

-- endpoint: BC4lean.Chapter8Examples.finiteGroupPoint_fixedPointCriterion
example : FixedPointCriterion Γ FiniteGroupPoint.{u} := finiteGroupPoint_fixedPointCriterion Γ

-- endpoint: BC4lean.Chapter8Examples.finiteGroupPoint_proper
example : ProperSMul Γ FiniteGroupPoint.{u} := finiteGroupPoint_proper Γ

-- endpoint: BC4lean.Chapter8Examples.finiteCanonicalGlobalFixedPoint
example : FixedPointSpace (⊤ : Subgroup Γ) (LabeledOrbitTelescope.Model Γ) :=
  finiteCanonicalGlobalFixedPoint Γ

-- endpoint: BC4lean.Chapter8Examples.finiteCanonicalPointHomotopyEquiv
example : EquivariantHomotopyEquiv Γ (LabeledOrbitTelescope.Model Γ) FiniteGroupPoint.{u} :=
  finiteCanonicalPointHomotopyEquiv Γ

-- endpoint: BC4lean.Chapter8Examples.finiteCanonicalPointKHomologyEquiv
example (p : Bool) : TopologicalKHomology.topologicalGroup p Γ ≃+
    TopologicalKHomology.group (Γ := Γ) (X := FiniteGroupPoint.{u}) p :=
  finiteCanonicalPointKHomologyEquiv Γ p

-- endpoint: BC4lean.Chapter8Examples.finiteTopologicalPointSpaceEquiv
example (p : Bool) : TopologicalKHomology.topologicalGroup p Γ ≃+
    TopologicalKHomology.spaceGroup p Γ FiniteGroupPoint.{u} := finiteTopologicalPointSpaceEquiv Γ p

-- endpoint: BC4lean.Chapter8Examples.finitePointCutoff
example : Cutoff.CutoffFunction Γ FiniteGroupPoint.{u} := finitePointCutoff Γ

-- endpoint: BC4lean.Chapter8Examples.reducedAssemblyHom_finitePoint
example (p : Bool) (x : TopologicalKHomology.topologicalGroup p Γ) :
    Assembly.reducedAssemblyHom Γ p x =
      Assembly.spaceAssemblyHom Γ FiniteGroupPoint.{u} p (finitePointCutoff Γ)
        (finiteTopologicalPointSpaceEquiv Γ p x) := reducedAssemblyHom_finitePoint Γ p x

-- endpoint: BC4lean.Chapter8Examples.reducedAssemblyHom_finitePoint_formula
example (p : Bool) (x : TopologicalKHomology.topologicalGroup p Γ) :
    Assembly.reducedAssemblyHom Γ p x =
      Assembly.reducedScalarKKToAnalyticHom Γ p
        (Assembly.cutoffProductHom Γ FiniteGroupPoint.{u} p (finitePointCutoff Γ)
          (KasparovDescent.classHom
            (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
            (CZero.action Γ (X := FiniteGroupPoint.{u})) p
            (finiteTopologicalPointSpaceEquiv Γ p x))) :=
  reducedAssemblyHom_finitePoint_formula Γ p x

end FinitePointCalibration

section UnitDescent
variable {B : Type uB} [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]







-- endpoint: BC4lean.KKTheory.UnitScalarDescent.evenClass_coefficientRestriction
example (x : KasparovHomotopyClass.{0,0,uB,max u uB} ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)) ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit B))) :
    GroupUniverseParityFunctoriality.sourcePullback.{0,0,0,uB,u}
      (Γ := Unit) (A := ℂ) (B := ReducedCrossedProduct ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)))
      (C := ReducedCrossedProduct ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit B))) (α := ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ))) (β := ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)))))) (γ := ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit B))))))
      false (coefficientToReducedCrossed ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ))) UnitScalarDescent.scalarCoefficient_equivariant
        (KasparovDescent.evenClass ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit B)) ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)) x) =
      GroupUniverseOrdinaryEven.coefficientPushforward.{uB,uB,max u uB}
        (B := B) (C := ReducedCrossedProduct ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit B))) (coefficientToReducedCrossed ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit B))) x :=
  UnitScalarDescent.evenClass_coefficientRestriction x

-- endpoint: BC4lean.KKTheory.UnitScalarDescent.oddClass_coefficientRestriction
example (x : OddKK.{0,0,uB,max u uB} ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)) ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit B))) :
    GroupUniverseParityFunctoriality.sourcePullback.{0,0,0,uB,u}
      (Γ := Unit) (A := ℂ) (B := ReducedCrossedProduct ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)))
      (C := ReducedCrossedProduct ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit B))) (α := ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ))) (β := ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)))))) (γ := ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit (ReducedCrossedProduct ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit B))))))
      true (coefficientToReducedCrossed ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ))) UnitScalarDescent.scalarCoefficient_equivariant
        (KasparovDescent.oddClass ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit B)) ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)) x) =
      GroupUniverseOrdinaryOdd.coefficientPushforward.{uB,uB,max u uB}
        (B := B) (C := ReducedCrossedProduct ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit B))) (coefficientToReducedCrossed ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit B))) x :=
  UnitScalarDescent.oddClass_coefficientRestriction x

end UnitDescent

section ScalarUnit


-- endpoint: BC4lean.KKTheory.ScalarUnitProjection.unitRelativeCycleIso
example : KasparovCycleIso
    (unitizedRelativeProjectionCycle (Γ := Unit) ScalarUnitProjection.scalarUnitProjection
      (unitizationScalarShadowProjection ScalarUnitProjection.scalarUnitProjection)
      (unitizationScalarShadowProjection_scalar ScalarUnitProjection.scalarUnitProjection))
    ScalarUnitProjection.scalarIdentityCycle := ScalarUnitProjection.unitRelativeCycleIso

-- endpoint: BC4lean.KKTheory.ScalarUnitProjection.relativeMap_nonunitalUnitProjection
example : nonunitalRelativeK0KasparovMap
    (nonunitalProjectionK0 (1 : ℂ) (by
      apply isStarProjection_iff'.mpr
      exact ⟨one_mul 1, star_one _⟩)) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of ScalarUnitProjection.scalarIdentityCycle) :=
  ScalarUnitProjection.relativeMap_nonunitalUnitProjection

-- endpoint: BC4lean.KKTheory.ScalarUnitProjection.scalarKKOperatorK0AddEquiv_identity
example : scalarKKOperatorK0AddEquiv (GroupUniverseParityUnits.identity.{0,0,0} ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ))) =
    nonunitalProjectionK0 (1 : ℂ) (by
      apply isStarProjection_iff'.mpr
      exact ⟨one_mul 1, star_one _⟩) := ScalarUnitProjection.scalarKKOperatorK0AddEquiv_identity

end ScalarUnit

section UnitPointCutoff
open BC4lean.KKTheory.UnitPointCutoff
variable (X : Type) [TopologicalSpace X] [MulAction Unit X]
  [ContinuousConstSMul Unit X] [CompactSpace X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [ProperSMul Unit X]

local instance cZeroSeparableForCutoff : TopologicalSpace.SeparableSpace C₀(X, ℂ) :=
  TopologicalKHomology.cZero_separableSpace

-- endpoint: BC4lean.KKTheory.UnitPointCutoff.scalarToCZero
example : ℂ →⋆ₙₐ[ℂ] C₀(X, ℂ) := scalarToCZero X

-- endpoint: BC4lean.KKTheory.UnitPointCutoff.pointCZeroEquiv
example [Subsingleton X] (x : X) : ℂ ≃⋆ₐ[ℂ] C₀(X, ℂ) := pointCZeroEquiv X x

-- endpoint: BC4lean.KKTheory.UnitPointCutoff.cutoff_square_one
example (c : Cutoff.CutoffFunction Unit X) (x : X) : c x ^ 2 = 1 := cutoff_square_one X c x

-- endpoint: BC4lean.KKTheory.UnitPointCutoff.algebraicProjection_eq_single
example (c : Cutoff.CutoffFunction Unit X) : Cutoff.algebraicProjection c =
    AlgebraicCrossedProduct.single (CZero.action Unit) 1 (scalarToCZero X 1) :=
  algebraicProjection_eq_single X c

-- endpoint: BC4lean.KKTheory.UnitPointCutoff.reducedCutoffProjection_eq_scalarCoefficient
example (c : Cutoff.CutoffFunction Unit X) :
    Cutoff.reducedCutoffProjection c = scalarCrossedCoefficient X 1 :=
  reducedCutoffProjection_eq_scalarCoefficient X c

-- endpoint: BC4lean.KKTheory.UnitPointCutoff.cutoffKKClass_eq_homClass
example (c : Cutoff.CutoffFunction Unit X) : Assembly.cutoffKKClass Unit X c =
    GroupUniverseParityHomCycle.homClass.{0,0,0,0}
      (scalarCrossedCoefficient X) (fun _ _ => rfl) := cutoffKKClass_eq_homClass X c

end UnitPointCutoff

section FinitePointCutoff
open BC4lean.KKTheory.FinitePointCutoff
open BC4lean.KKTheory.GroupUniverseParityGroup
open BC4lean.KKTheory.GroupUniverseParityFunctoriality

-- endpoint: BC4lean.KKTheory.FinitePointCutoff.projectionScalarHom (definition body)
example {B : Type uB} [NonUnitalCStarAlgebra B] (p : B) (hp : IsStarProjection p) (z : ℂ) :
    projectionScalarHom p hp z = z • p := rfl

variable (Γ : Type) [Group Γ] [Countable Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
  (X : Type) [TopologicalSpace X] [MulAction Γ X]
  [ContinuousConstSMul Γ X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [ProperSMul Γ X]

local instance cZeroSeparableForFiniteCutoff : TopologicalSpace.SeparableSpace C₀(X, ℂ) :=
  TopologicalKHomology.cZero_separableSpace

-- endpoint: BC4lean.KKTheory.FinitePointCutoff.cutoffKKClass_eq_homClass
example (c : Cutoff.CutoffFunction Γ X)
    (f : ℂ →⋆ₙₐ[ℂ] ReducedCrossedProduct (CZero.action Γ (X := X)))
    (hf : f 1 = Cutoff.reducedCutoffProjection c) :
    Assembly.cutoffKKClass Γ X c =
      GroupUniverseParityHomCycle.homClass.{0,0,0,0}
        («α» := (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ))
        («β» := CStarAlgebraAction.trivial) f (fun _ _ => rfl) :=
  cutoffKKClass_eq_homClass Γ X c f hf

-- endpoint: BC4lean.KKTheory.FinitePointCutoff.cutoffProductHom_eq_sourcePullback
example (p : Bool) (c : Cutoff.CutoffFunction Γ X)
    (f : ℂ →⋆ₙₐ[ℂ] ReducedCrossedProduct (CZero.action Γ (X := X)))
    (hf : f 1 = Cutoff.reducedCutoffProjection c)
    (y : KKParityGroup.{0,0,0,0} p
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
        (ReducedCrossedProduct (CZero.action Γ (X := X))))
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
        (ReducedCrossedProduct (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)))) :
    Assembly.cutoffProductHom Γ X p c y =
      sourcePullback.{0,0,0,0,0} (Γ := Unit) (A := ℂ)
        («α» := CStarAlgebraAction.trivial) («β» := CStarAlgebraAction.trivial)
        («γ» := CStarAlgebraAction.trivial) p f (fun _ _ => rfl) y :=
  cutoffProductHom_eq_sourcePullback Γ X p c f hf y

end FinitePointCutoff

section FinitePointAveraging
open BC4lean.KKTheory.FinitePointCutoff
open BC4lean.KKTheory.GroupUniverseParityGroup
open BC4lean.KKTheory.GroupUniverseParityFunctoriality
variable (Γ : Type) [Group Γ] [Finite Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]

local instance pointCZeroSeparableForAveraging :
    TopologicalSpace.SeparableSpace C₀(FiniteGroupPoint.{0}, ℂ) :=
  TopologicalKHomology.cZero_separableSpace

-- endpoint: BC4lean.KKTheory.FinitePointCutoff.cutoff_apply
example (c : Cutoff.CutoffFunction Γ FiniteGroupPoint.{0}) (x : FiniteGroupPoint.{0}) :
    c x = (Real.sqrt (Nat.card Γ))⁻¹ := cutoff_apply Γ c x

-- endpoint: BC4lean.KKTheory.FinitePointCutoff.averaging
example : ReducedCrossedProduct (CZero.action Γ (X := FiniteGroupPoint.{0})) := averaging Γ

-- endpoint: BC4lean.KKTheory.FinitePointCutoff.reducedCutoffProjection_eq_averaging
example (c : Cutoff.CutoffFunction Γ FiniteGroupPoint.{0}) :
    Cutoff.reducedCutoffProjection c = averaging Γ :=
  reducedCutoffProjection_eq_averaging Γ c

-- endpoint: BC4lean.KKTheory.FinitePointCutoff.averaging_coe
example [Fintype Γ] :
    (averaging Γ : AdjointableMap C₀(FiniteGroupPoint.{0}, ℂ)
        (ReducedCrossedHilbertModule C₀(FiniteGroupPoint.{0}, ℂ) Γ)
        (ReducedCrossedHilbertModule C₀(FiniteGroupPoint.{0}, ℂ) Γ)) =
      ∑ g : Γ, reducedCrossedGenerator (CZero.action Γ)
        (UnitPointCutoff.scalarToCZero FiniteGroupPoint.{0} ((Nat.card Γ : ℂ)⁻¹)) g :=
  averaging_coe Γ

-- endpoint: BC4lean.KKTheory.FinitePointCutoff.cutoffKKClass_eq_averagingHomClass
example (c : Cutoff.CutoffFunction Γ FiniteGroupPoint.{0}) :
    Assembly.cutoffKKClass Γ FiniteGroupPoint.{0} c =
      GroupUniverseParityHomCycle.homClass.{0,0,0,0}
        («α» := (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ))
        («β» := CStarAlgebraAction.trivial)
        (projectionScalarHom (averaging Γ) (averaging_isStarProjection Γ)) (fun _ _ => rfl) :=
  cutoffKKClass_eq_averagingHomClass Γ c

-- endpoint: BC4lean.KKTheory.FinitePointCutoff.cutoffProductHom_eq_averagingPullback
example (p : Bool) (c : Cutoff.CutoffFunction Γ FiniteGroupPoint.{0})
    (y : KKParityGroup.{0,0,0,0} p
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
        (ReducedCrossedProduct (CZero.action Γ (X := FiniteGroupPoint.{0}))))
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
        (ReducedCrossedProduct (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)))) :
    Assembly.cutoffProductHom Γ FiniteGroupPoint.{0} p c y =
      sourcePullback.{0,0,0,0,0} (Γ := Unit) (A := ℂ)
        («α» := CStarAlgebraAction.trivial) («β» := CStarAlgebraAction.trivial)
        («γ» := CStarAlgebraAction.trivial) p
        (projectionScalarHom (averaging Γ) (averaging_isStarProjection Γ)) (fun _ _ => rfl) y :=
  cutoffProductHom_eq_averagingPullback Γ p c y

end FinitePointAveraging

section UnitAssembly
open BC4lean.KKTheory.UnitPointCutoff
open BC4lean.KKTheory.GroupUniverseParityGroup
open BC4lean.KKTheory.GroupUniverseParityFunctoriality



-- endpoint: BC4lean.Chapter8Examples.unitScalarAnalyticEquiv
example (p : Bool) : KKParityGroup.{0,0,0,0} p ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)) ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)) ≃+ Assembly.analyticGroup Unit p :=
  unitScalarAnalyticEquiv p

-- endpoint: BC4lean.Chapter8Examples.reducedScalarKKToK0Hom_coefficient
example (x : KasparovHomotopyClass.{0,0,0,0} ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)) ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ))) :
    Assembly.reducedScalarKKToK0Hom Unit
      (GroupUniverseOrdinaryEven.coefficientPushforward (coefficientToReducedCrossed ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ))) x) = unitScalarAnalyticEquiv false x :=
  reducedScalarKKToK0Hom_coefficient x

-- endpoint: BC4lean.Chapter8Examples.reducedScalarKKToK1Hom_coefficient
example (x : OddKK.{0,0,0,0} ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)) ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ))) :
    Assembly.reducedScalarKKToK1Hom Unit
      (GroupUniverseOrdinaryOdd.coefficientPushforward (coefficientToReducedCrossed ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ))) x) = unitScalarAnalyticEquiv true x :=
  reducedScalarKKToK1Hom_coefficient x

section CompactPoint
variable (X : Type) [TopologicalSpace X] [MulAction Unit X]
  [ContinuousConstSMul Unit X] [CompactSpace X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [ProperSMul Unit X]

local instance cZeroSeparableForAssembly : TopologicalSpace.SeparableSpace C₀(X, ℂ) :=
  TopologicalKHomology.cZero_separableSpace

-- endpoint: BC4lean.Chapter8Examples.unitPointSourceEquiv
example [Subsingleton X] (x : X) (p : Bool) :
    TopologicalKHomology.spaceGroup p Unit X ≃+ KKParityGroup.{0,0,0,0} p ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)) ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)) :=
  unitPointSourceEquiv X x p

-- endpoint: BC4lean.Chapter8Examples.cutoffProduct_descent_eq_coefficient (even)
example (c : Cutoff.CutoffFunction Unit X)
    (x : TopologicalKHomology.spaceGroup false Unit X) :
    Assembly.cutoffProductHom Unit X false c
      (KasparovDescent.classHom ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)) (CZero.action Unit (X := X)) false x) =
    GroupUniverseOrdinaryEven.coefficientPushforward (coefficientToReducedCrossed ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)))
      (sourcePullback false (scalarToCZero X) (scalarToCZero_equivariant X) x) :=
  cutoffProduct_descent_eq_coefficient X false c x

-- endpoint: BC4lean.Chapter8Examples.cutoffProduct_descent_eq_coefficient (odd)
example (c : Cutoff.CutoffFunction Unit X)
    (x : TopologicalKHomology.spaceGroup true Unit X) :
    Assembly.cutoffProductHom Unit X true c
      (KasparovDescent.classHom ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)) (CZero.action Unit (X := X)) true x) =
    GroupUniverseOrdinaryOdd.coefficientPushforward (coefficientToReducedCrossed ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)))
      (sourcePullback true (scalarToCZero X) (scalarToCZero_equivariant X) x) :=
  cutoffProduct_descent_eq_coefficient X true c x

-- endpoint: BC4lean.Chapter8Examples.spaceAssemblyHom_eq_unitPointEquiv
example [Subsingleton X] (x0 : X) (p : Bool) (c : Cutoff.CutoffFunction Unit X)
    (x : TopologicalKHomology.spaceGroup p Unit X) :
    Assembly.spaceAssemblyHom Unit X p c x =
      ((unitPointSourceEquiv X x0 p).trans (unitScalarAnalyticEquiv p)) x :=
  spaceAssemblyHom_eq_unitPointEquiv X x0 p c x

end CompactPoint

-- endpoint: BC4lean.Chapter8Examples.unitAssemblyAddEquiv
example (p : Bool) : TopologicalKHomology.topologicalGroup p Unit ≃+
    Assembly.analyticGroup Unit p := unitAssemblyAddEquiv p

-- endpoint: BC4lean.Chapter8Examples.reducedAssemblyHom_unit_eq
example (p : Bool) (x : TopologicalKHomology.topologicalGroup p Unit) :
    Assembly.reducedAssemblyHom Unit p x = unitAssemblyAddEquiv p x :=
  reducedAssemblyHom_unit_eq p x

-- endpoint: BC4lean.Chapter8Examples.baumConnesProperty_unit (actual target)
-- No supplied assembly bijectivity, inverse, or compatibility hypothesis.
example : ∀ p : Bool, Function.Bijective (Assembly.reducedAssemblyHom Unit p) :=
  baumConnesProperty_unit

-- endpoint: BC4lean.Chapter8Examples.baumConnesProperty_unit (named property)
example : Assembly.BaumConnesProperty Unit := baumConnesProperty_unit

end UnitAssembly

section GroupRestriction
open BC4lean.KKTheory.GroupRestriction
open BC4lean.KKTheory.GroupUniverseParityGroup
universe uA uG
variable {Γ : Type uΓ} {Γ' : Type uG} [Group Γ] [Group Γ'] (f : Γ →* Γ')
  {A : Type uA} {B : Type uB} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  {α : CStarAlgebraAction Γ' A} {β : CStarAlgebraAction Γ' B}

-- endpoint: BC4lean.KKTheory.GroupRestriction.cycleComap
example {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
    [CStarModule Bᵐᵒᵖ E] [CompleteSpace E] (c : KasparovCycle α β E) :
    KasparovCycle (actionComap f α) (actionComap f β) E := cycleComap f c

-- endpoint: BC4lean.KKTheory.GroupRestriction.cycleComap (definition body)
example {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
    [CStarModule Bᵐᵒᵖ E] [CompleteSpace E] (c : KasparovCycle α β E) (g : Γ) :
    (cycleComap f c).groupAction.action g = c.groupAction.action (f g) ∧
      (cycleComap f c).grading = c.grading ∧
      (cycleComap f c).representation = c.representation ∧
      (cycleComap f c).operator = c.operator := ⟨rfl, rfl, rfl, rfl⟩

-- endpoint: BC4lean.KKTheory.GroupRestriction.evenComap
example (x : KasparovHomotopyClass.{uG,uA,uB,uE} α β) :
    KasparovHomotopyClass.{uΓ,uA,uB,uE} (actionComap f α) (actionComap f β) := evenComap f x

-- endpoint: BC4lean.KKTheory.GroupRestriction.evenComap (additive)
example (x y : KasparovHomotopyClass.{uG,uA,uB,uE} α β) :
    evenComap f (x + y) = evenComap f x + evenComap f y := evenComap_add f x y

variable [TopologicalSpace.SeparableSpace B]

-- endpoint: BC4lean.KKTheory.GroupRestriction.oddComap
example (x : OddKK.{uG,uA,uB,uE} α β) :
    OddKK.{uΓ,uA,uB,uE} (actionComap f α) (actionComap f β) := oddComap f x

-- endpoint: BC4lean.KKTheory.GroupRestriction.oddComap (additive)
example (x y : OddKK.{uG,uA,uB,uE} α β) :
    oddComap f (x + y) = oddComap f x + oddComap f y := oddComap_add f x y

-- endpoint: BC4lean.KKTheory.GroupRestriction.subsingletonParityEquiv
example [Subsingleton Γ] (p : Bool) :
    KKParityGroup.{uΓ,uA,uB,uE} p (CStarAlgebraAction.trivial : CStarAlgebraAction Γ A)
        (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B) ≃+
      KKParityGroup.{0,uA,uB,uE} p (CStarAlgebraAction.trivial : CStarAlgebraAction Unit A)
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit B) :=
  subsingletonParityEquiv p

-- endpoint: BC4lean.KKTheory.GroupRestriction.subsingletonParityEquiv (even half is restriction)
example [Subsingleton Γ]
    (x : KasparovHomotopyClass.{uΓ,uA,uB,uE} (CStarAlgebraAction.trivial : CStarAlgebraAction Γ A)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B)) :
    subsingletonParityEquiv false x = evenComap (1 : Unit →* Γ) x := rfl

end GroupRestriction

section SubsingletonScalarDescent
open BC4lean.KKTheory.GroupRestriction BC4lean.KKTheory.SubsingletonScalarDescent
open BC4lean.KKTheory.GroupUniverseParityGroup
variable (Γ : Type uΓ) [Group Γ] [Countable Γ]
  {B : Type uB} [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]

-- endpoint: BC4lean.KKTheory.SubsingletonScalarDescent.evenClass_coefficientRestriction
example (x : KasparovHomotopyClass.{uΓ,0,uB,max u uB}
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B)) :
    GroupUniverseParityFunctoriality.sourcePullback.{0,0,uΓ,max uΓ uB,u}
      (Γ := Unit) (A := ℂ)
      («α» := CStarAlgebraAction.trivial) («β» := CStarAlgebraAction.trivial)
      (γ := CStarAlgebraAction.trivial) false
      (coefficientToReducedCrossed (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ))
      (fun _ _ => rfl)
      (KasparovDescent.evenClass (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B)
        (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) x) =
    GroupUniverseOrdinaryEven.coefficientPushforward.{uB,max uΓ uB,max u uB}
      (coefficientToReducedCrossed (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B))
      (evenComap (1 : Unit →* Γ) x) :=
  evenClass_coefficientRestriction Γ x

-- endpoint: BC4lean.KKTheory.SubsingletonScalarDescent.oddClass_coefficientRestriction
example (x : OddKK.{uΓ,0,uB,max u uB}
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B)) :
    GroupUniverseParityFunctoriality.sourcePullback.{0,0,uΓ,max uΓ uB,u}
      (Γ := Unit) (A := ℂ)
      («α» := CStarAlgebraAction.trivial) («β» := CStarAlgebraAction.trivial)
      (γ := CStarAlgebraAction.trivial) true
      (coefficientToReducedCrossed (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ))
      (fun _ _ => rfl)
      (KasparovDescent.oddClass (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B)
        (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) x) =
    GroupUniverseOrdinaryOdd.coefficientPushforward.{uB,max uΓ uB,max u uB}
      (coefficientToReducedCrossed (CStarAlgebraAction.trivial : CStarAlgebraAction Γ B))
      (oddComap (1 : Unit →* Γ) x) :=
  oddClass_coefficientRestriction Γ x

end SubsingletonScalarDescent

section ScalarIdentityUniverse
open BC4lean.KKTheory.GroupUniverseParityGroup

-- endpoint: BC4lean.KKTheory.ScalarUnitProjection.identity_universe
example : GroupUniverseParityUnits.identity.{0,0,uV}
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ) =
    GroupShrinkEvenBridge.addEquivalence.{0,0,0,0,uV}
      (GroupUniverseParityUnits.identity.{0,0,0}
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)) :=
  ScalarUnitProjection.identity_universe

-- endpoint: BC4lean.KKTheory.ScalarUnitProjection.scalarKKOperatorK0AddEquiv_identity_universe
example : scalarKKOperatorK0AddEquiv.{0,uV}
      (GroupUniverseParityUnits.identity.{0,0,uV}
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)) =
    nonunitalProjectionK0 (1 : ℂ) (by
      apply isStarProjection_iff'.mpr
      exact ⟨one_mul 1, star_one _⟩) :=
  ScalarUnitProjection.scalarKKOperatorK0AddEquiv_identity_universe

end ScalarIdentityUniverse

section SubsingletonAssembly
open BC4lean.Chapter8Examples.SubsingletonAssembly
variable (Γ : Type u) [Group Γ] [Subsingleton Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]

-- endpoint: BC4lean.Chapter8Examples.SubsingletonAssembly.assemblyAddEquiv
example (p : Bool) : TopologicalKHomology.topologicalGroup p Γ ≃+
    Assembly.analyticGroup Γ p := assemblyAddEquiv Γ p

-- endpoint: BC4lean.Chapter8Examples.SubsingletonAssembly.reducedAssemblyHom_eq
example (p : Bool) (x : TopologicalKHomology.topologicalGroup p Γ) :
    Assembly.reducedAssemblyHom Γ p x = assemblyAddEquiv Γ p x :=
  reducedAssemblyHom_eq Γ p x

-- endpoint: BC4lean.Chapter8Examples.SubsingletonAssembly.baumConnesProperty_of_subsingleton
-- No supplied assembly bijectivity, inverse, or compatibility hypothesis.
example : ∀ p : Bool, Function.Bijective (Assembly.reducedAssemblyHom Γ p) :=
  baumConnesProperty_of_subsingleton Γ

-- endpoint: BC4lean.Chapter8Examples.SubsingletonAssembly.baumConnesProperty_of_subsingleton (named property)
example : Assembly.BaumConnesProperty Γ := baumConnesProperty_of_subsingleton Γ

-- endpoint: BC4lean.Chapter8Examples.SubsingletonAssembly.baumConnesProperty_of_subsingleton (lifted Unit)
example : Assembly.BaumConnesProperty (ULift.{uV} Unit) :=
  baumConnesProperty_of_subsingleton (ULift.{uV} Unit)

end SubsingletonAssembly
end Chapter8ExpectedTypes

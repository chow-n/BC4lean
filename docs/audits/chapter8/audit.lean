import BC4lean.AssemblyBijectivityCriteria
import BC4lean.BaumConnesInvariance
import BC4lean.BaumConnesProperty
import BC4lean.CompactModelColimitCalibration
import BC4lean.CosetAssembly
import BC4lean.CosetAssemblyUnit
import BC4lean.CosetCompressedDescent
import BC4lean.CosetUnitCycle
import BC4lean.FiniteAbelianAssemblyEquivalence
import BC4lean.FiniteAbelianCharacterProjection
import BC4lean.FiniteAbelianCharacterSplit
import BC4lean.FiniteAbelianReducedEquiv
import BC4lean.FiniteAssemblyEquivalence
import BC4lean.FiniteAssemblyUnit
import BC4lean.FiniteGroupCStarMatrix
import BC4lean.FiniteGroupOperatorK
import BC4lean.FiniteGroupPointCalibration
import BC4lean.FinitePointCharacterAssembly
import BC4lean.FinitePointCharacterTensor
import BC4lean.FinitePointCompressedDescent
import BC4lean.FinitePointCutoff
import BC4lean.FinitePointDescentRange
import BC4lean.FiniteReducedGroupCStar
import BC4lean.FiniteScalarCrossed
import BC4lean.GreenJulgCorrespondence
import BC4lean.GreenJulgPoint
import BC4lean.GreenJulgPointLeft
import BC4lean.GreenJulgRepresentative
import BC4lean.KKGroupRestriction
import BC4lean.KasparovEquivariantDirectSum
import BC4lean.KasparovEquivariantRepresentative
import BC4lean.KasparovFiniteAveraging
import BC4lean.KasparovGroupChange
import BC4lean.KasparovReducingCompression
import BC4lean.KasparovReducingCompressionFibre
import BC4lean.KasparovTrivialInflation
import BC4lean.OperatorKFinitePi
import BC4lean.OperatorKMatrixStability
import BC4lean.OperatorKProductEquiv
import BC4lean.OrderTwoAssemblyEquivalence
import BC4lean.OrderTwoEigenSplitAdditive
import BC4lean.OrderTwoEigenSplitInvariance
import BC4lean.OrderTwoPointKK
import BC4lean.OrderTwoPointKKScalar
import BC4lean.OrderTwoPointKKSplit
import BC4lean.ReducedGroupTrace
import BC4lean.ScalarIdentityUniverse
import BC4lean.ScalarOperatorK0
import BC4lean.ScalarOperatorK1
import BC4lean.ScalarOperatorKNonunital
import BC4lean.ScalarProjectionRank
import BC4lean.ScalarUnitProjection
import BC4lean.SubsingletonAssemblyEquivalence
import BC4lean.SubsingletonScalarDescent
import BC4lean.TrivialAnalyticCalibration
import BC4lean.TrivialAnalyticScalar
import BC4lean.UnitAssemblyEquivalence
import BC4lean.UnitPointCutoff
import BC4lean.UnitScalarDescent
import Lean
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let modules : Array String := #["BC4lean.AssemblyBijectivityCriteria", "BC4lean.BaumConnesInvariance", "BC4lean.BaumConnesProperty", "BC4lean.CompactModelColimitCalibration", "BC4lean.CosetAssembly", "BC4lean.CosetAssemblyUnit", "BC4lean.CosetCompressedDescent", "BC4lean.CosetUnitCycle", "BC4lean.FiniteAbelianAssemblyEquivalence", "BC4lean.FiniteAbelianCharacterProjection", "BC4lean.FiniteAbelianCharacterSplit", "BC4lean.FiniteAbelianReducedEquiv", "BC4lean.FiniteAssemblyEquivalence", "BC4lean.FiniteAssemblyUnit", "BC4lean.FiniteGroupCStarMatrix", "BC4lean.FiniteGroupOperatorK", "BC4lean.FiniteGroupPointCalibration", "BC4lean.FinitePointCharacterAssembly", "BC4lean.FinitePointCharacterTensor", "BC4lean.FinitePointCompressedDescent", "BC4lean.FinitePointCutoff", "BC4lean.FinitePointDescentRange", "BC4lean.FiniteReducedGroupCStar", "BC4lean.FiniteScalarCrossed", "BC4lean.GreenJulgCorrespondence", "BC4lean.GreenJulgPoint", "BC4lean.GreenJulgPointLeft", "BC4lean.GreenJulgRepresentative", "BC4lean.KKGroupRestriction", "BC4lean.KasparovEquivariantDirectSum", "BC4lean.KasparovEquivariantRepresentative", "BC4lean.KasparovFiniteAveraging", "BC4lean.KasparovGroupChange", "BC4lean.KasparovReducingCompression", "BC4lean.KasparovReducingCompressionFibre", "BC4lean.KasparovTrivialInflation", "BC4lean.OperatorKFinitePi", "BC4lean.OperatorKMatrixStability", "BC4lean.OperatorKProductEquiv", "BC4lean.OrderTwoAssemblyEquivalence", "BC4lean.OrderTwoEigenSplitAdditive", "BC4lean.OrderTwoEigenSplitInvariance", "BC4lean.OrderTwoPointKK", "BC4lean.OrderTwoPointKKScalar", "BC4lean.OrderTwoPointKKSplit", "BC4lean.ReducedGroupTrace", "BC4lean.ScalarIdentityUniverse", "BC4lean.ScalarOperatorK0", "BC4lean.ScalarOperatorK1", "BC4lean.ScalarOperatorKNonunital", "BC4lean.ScalarProjectionRank", "BC4lean.ScalarUnitProjection", "BC4lean.SubsingletonAssemblyEquivalence", "BC4lean.SubsingletonScalarDescent", "BC4lean.TrivialAnalyticCalibration", "BC4lean.TrivialAnalyticScalar", "BC4lean.UnitAssemblyEquivalence", "BC4lean.UnitPointCutoff", "BC4lean.UnitScalarDescent"]
  let links : Array String := #["BC4lean.Assembly.BaumConnesConjecture", "BC4lean.Assembly.BaumConnesProperty", "BC4lean.Assembly.assemblyHom_bijective_iff_homotopyEquiv", "BC4lean.Assembly.assemblyHom_bijective_iff_pieceCriteria", "BC4lean.Assembly.assemblyHom_injective_iff_commonTransition", "BC4lean.Assembly.assemblyHom_injective_iff_homotopyEquiv", "BC4lean.Assembly.assemblyHom_surjective_iff_homotopyEquiv", "BC4lean.Assembly.assemblyHom_surjective_iff_pieceImages", "BC4lean.Assembly.baumConnesProperty_iff_even_and_odd", "BC4lean.Assembly.indexedAssemblyHom_bijective_iff_cofinalIndex", "BC4lean.Assembly.indexedAssemblyHom_injective_iff_cofinalIndex", "BC4lean.Assembly.indexedAssemblyHom_surjective_iff_cofinalIndex", "BC4lean.Assembly.indexedAssemblyProperty_iff_cofinalComparison", "BC4lean.Assembly.modelAssemblyProperty_iff_baumConnesProperty", "BC4lean.Chapter8Examples.CosetAssembly.coset_proper", "BC4lean.Chapter8Examples.CosetAssembly.reducedAssemblyHom_toModel", "BC4lean.Chapter8Examples.CosetAssembly.toModel", "BC4lean.Chapter8Examples.CosetAssemblyUnit.cosetUnitClass", "BC4lean.Chapter8Examples.CosetAssemblyUnit.lambdaGroup", "BC4lean.Chapter8Examples.CosetAssemblyUnit.lambdaGroup_le", "BC4lean.Chapter8Examples.CosetAssemblyUnit.reducedAssemblyHom_cosetUnitClass", "BC4lean.Chapter8Examples.CosetAssemblyUnit.reducedAssemblyHom_ne_zero", "BC4lean.Chapter8Examples.CosetAssemblyUnit.reducedTraceK0_assembly_cosetUnitClass", "BC4lean.Chapter8Examples.CosetAssemblyUnit.subgroupElement_eq", "BC4lean.Chapter8Examples.CosetUnitCycle.multiplication_isModuleCompact", "BC4lean.Chapter8Examples.FiniteAbelianAssembly.finiteAbelianAnalyticEquiv", "BC4lean.Chapter8Examples.FiniteAbelianAssembly.spaceAssemblyHom_finiteAbelian", "BC4lean.Chapter8Examples.FiniteAssemblyUnit.assembly_unitClass_not_mem_zmultiples", "BC4lean.Chapter8Examples.FiniteAssemblyUnit.reducedAssemblyHom_characterClass", "BC4lean.Chapter8Examples.FiniteAssemblyUnit.reducedAssemblyHom_unitClass", "BC4lean.Chapter8Examples.FiniteAssemblyUnit.reducedTraceK0_assembly_unitClass", "BC4lean.Chapter8Examples.FiniteGroupPoint", "BC4lean.Chapter8Examples.FinitePointAssembly.spaceAssembly_even_class", "BC4lean.Chapter8Examples.FinitePointAssembly.spaceAssembly_odd_class", "BC4lean.Chapter8Examples.OrderTwoAssembly.orderTwoAnalyticEquiv", "BC4lean.Chapter8Examples.OrderTwoAssembly.spaceAssemblyHom_orderTwo", "BC4lean.Chapter8Examples.SubsingletonAssembly.assemblyAddEquiv", "BC4lean.Chapter8Examples.SubsingletonAssembly.baumConnesProperty_of_subsingleton", "BC4lean.Chapter8Examples.SubsingletonAssembly.reducedAssemblyHom_eq", "BC4lean.Chapter8Examples.assemblyHom_eq_compactSpaceAssembly", "BC4lean.Chapter8Examples.baumConnesProperty_of_card_two", "BC4lean.Chapter8Examples.baumConnesProperty_of_finite", "BC4lean.Chapter8Examples.baumConnesProperty_of_finite_commGroup", "BC4lean.Chapter8Examples.baumConnesProperty_of_pointGreenJulg_bijective", "BC4lean.Chapter8Examples.baumConnesProperty_unit", "BC4lean.Chapter8Examples.baumConnesProperty_zmod_two", "BC4lean.Chapter8Examples.compactSpaceGroupEquiv", "BC4lean.Chapter8Examples.finiteAbelianAssemblyAddEquiv", "BC4lean.Chapter8Examples.finiteAbelianReducedK0Equiv", "BC4lean.Chapter8Examples.finiteAssemblyAddEquiv", "BC4lean.Chapter8Examples.finiteCanonicalGlobalFixedPoint", "BC4lean.Chapter8Examples.finiteCanonicalPointHomotopyEquiv", "BC4lean.Chapter8Examples.finiteTopologicalPointSpaceEquiv", "BC4lean.Chapter8Examples.orderTwoAssemblyAddEquiv", "BC4lean.Chapter8Examples.reducedAssemblyHom_finiteAbelian_eq", "BC4lean.Chapter8Examples.reducedAssemblyHom_finitePoint_formula", "BC4lean.Chapter8Examples.reducedAssemblyHom_finite_eq", "BC4lean.Chapter8Examples.reducedAssemblyHom_orderTwo_eq", "BC4lean.Chapter8Examples.reducedAssemblyHom_unit_eq", "BC4lean.Chapter8Examples.reducedScalarKKToAnalyticHom_bijective", "BC4lean.Chapter8Examples.terminalColimitEquiv", "BC4lean.Chapter8Examples.trivialAnalyticK0Equiv", "BC4lean.Chapter8Examples.trivialAnalyticK0Equiv_projection", "BC4lean.Chapter8Examples.trivialAnalyticK1Equiv", "BC4lean.Chapter8Examples.trivialAnalyticK1Equiv_unitary", "BC4lean.Chapter8Examples.trivialReducedK0Equiv", "BC4lean.Chapter8Examples.trivialReducedK0Equiv_one", "BC4lean.Chapter8Examples.trivialReducedK1_eq_zero", "BC4lean.Chapter8Examples.unitAssemblyAddEquiv", "BC4lean.Chapter8Examples.wholeCompactPiece", "BC4lean.CharacterDual.card_eq", "BC4lean.KKTheory.CosetCompressedDescent.even_compressedDescent", "BC4lean.KKTheory.CosetCompressedDescent.subgroupProjection_isStarProjection", "BC4lean.KKTheory.FinitePointCharacterTensor.characterIsometry", "BC4lean.KKTheory.FinitePointCharacterTensor.characterProjection_isStarProjection", "BC4lean.KKTheory.FinitePointCharacterTensor.characterRangeEquiv", "BC4lean.KKTheory.FinitePointCharacterTensor.reducedSourceRepresentation_averaging_mk", "BC4lean.KKTheory.FinitePointCompressedDescent.characterCycleIso", "BC4lean.KKTheory.FinitePointCompressedDescent.even_compressedDescent", "BC4lean.KKTheory.FinitePointCompressedDescent.oddCharacterCycleIso", "BC4lean.KKTheory.FinitePointCompressedDescent.odd_compressedDescent", "BC4lean.KKTheory.FinitePointCutoff.averaging", "BC4lean.KKTheory.FinitePointCutoff.averaging_coe", "BC4lean.KKTheory.FinitePointCutoff.cutoffKKClass_eq_averagingHomClass", "BC4lean.KKTheory.FinitePointCutoff.cutoffKKClass_eq_homClass", "BC4lean.KKTheory.FinitePointCutoff.cutoffProductHom_eq_averagingPullback", "BC4lean.KKTheory.FinitePointCutoff.cutoffProductHom_eq_sourcePullback", "BC4lean.KKTheory.FinitePointCutoff.cutoff_apply", "BC4lean.KKTheory.FinitePointCutoff.projectionScalarHom", "BC4lean.KKTheory.FinitePointCutoff.reducedCutoffProjection_eq_averaging", "BC4lean.KKTheory.GreenJulgCorrespondence.greenJulgInverse", "BC4lean.KKTheory.GreenJulgPoint.greenJulgInverse_pointGreenJulgHom", "BC4lean.KKTheory.GreenJulgPoint.greenJulgPointEquiv", "BC4lean.KKTheory.GreenJulgPoint.pointGreenJulgHom", "BC4lean.KKTheory.GreenJulgPoint.pointGreenJulgHom_greenJulgInverse", "BC4lean.KKTheory.GroupRestriction.cycleComap", "BC4lean.KKTheory.GroupRestriction.evenComap", "BC4lean.KKTheory.GroupRestriction.oddComap", "BC4lean.KKTheory.GroupRestriction.subsingletonParityEquiv", "BC4lean.KKTheory.KasparovHomotopyClass.orderTwoSplit", "BC4lean.KKTheory.OddKK.orderTwoSplit", "BC4lean.KKTheory.ScalarUnitProjection.identity_universe", "BC4lean.KKTheory.ScalarUnitProjection.relativeMap_nonunitalUnitProjection", "BC4lean.KKTheory.ScalarUnitProjection.scalarKKOperatorK0AddEquiv_identity", "BC4lean.KKTheory.ScalarUnitProjection.scalarKKOperatorK0AddEquiv_identity_universe", "BC4lean.KKTheory.ScalarUnitProjection.unitRelativeCycleIso", "BC4lean.KKTheory.SubsingletonScalarDescent.evenClass_coefficientRestriction", "BC4lean.KKTheory.SubsingletonScalarDescent.oddClass_coefficientRestriction", "BC4lean.KKTheory.UnitPointCutoff.cutoffKKClass_eq_homClass", "BC4lean.KKTheory.UnitPointCutoff.pointCZeroEquiv", "BC4lean.KKTheory.UnitPointCutoff.reducedCutoffProjection_eq_scalarCoefficient", "BC4lean.KKTheory.UnitScalarDescent.evenClass_coefficientRestriction", "BC4lean.KKTheory.UnitScalarDescent.evenCoefficientRestrictionIso", "BC4lean.KKTheory.UnitScalarDescent.oddClass_coefficientRestriction", "BC4lean.KKTheory.UnitScalarDescent.oddCoefficientRestrictionIso", "BC4lean.KKTheory.finiteAbelianPointKKSplit", "BC4lean.KKTheory.orderTwoKKParitySplit", "BC4lean.KKTheory.orderTwoPointKKSplit", "BC4lean.KKTheory.sourcePullbackEquiv", "BC4lean.finiteAbelianReducedEquiv", "BC4lean.reducedK0EquivOfStarAlgEquiv", "BC4lean.reducedK0_finite", "BC4lean.reducedK0_of_card_eq_two", "BC4lean.reducedK0_of_commute", "BC4lean.reducedK1_eq_zero_of_starAlgEquiv", "BC4lean.reducedK1_finite"]
  let endpoints : Array String := #["BC4lean.Assembly.BaumConnesConjecture", "BC4lean.Assembly.BaumConnesProperty", "BC4lean.Assembly.assemblyHom_bijective_iff_canonical", "BC4lean.Assembly.assemblyHom_bijective_iff_homotopyEquiv", "BC4lean.Assembly.assemblyHom_bijective_iff_pieceCriteria", "BC4lean.Assembly.assemblyHom_bijective_iff_universalModels", "BC4lean.Assembly.assemblyHom_injective_iff_commonTransition", "BC4lean.Assembly.assemblyHom_injective_iff_homotopyEquiv", "BC4lean.Assembly.assemblyHom_surjective_iff_homotopyEquiv", "BC4lean.Assembly.assemblyHom_surjective_iff_pieceImages", "BC4lean.Assembly.baumConnesProperty_iff_even_and_odd", "BC4lean.Assembly.indexedAssemblyHom_bijective_iff_cofinalComparison", "BC4lean.Assembly.indexedAssemblyHom_bijective_iff_cofinalIndex", "BC4lean.Assembly.indexedAssemblyHom_injective_iff_cofinalIndex", "BC4lean.Assembly.indexedAssemblyHom_surjective_iff_cofinalIndex", "BC4lean.Assembly.indexedAssemblyProperty", "BC4lean.Assembly.indexedAssemblyProperty_iff_cofinalComparison", "BC4lean.Assembly.indexedAssemblyProperty_iff_cofinalIndex", "BC4lean.Assembly.modelAssemblyProperty", "BC4lean.Assembly.modelAssemblyProperty_iff_baumConnesProperty", "BC4lean.Assembly.modelAssemblyProperty_iff_homotopyEquiv", "BC4lean.Assembly.modelAssemblyProperty_iff_universalModels", "BC4lean.Chapter8Examples.CosetAssembly.coset_proper", "BC4lean.Chapter8Examples.CosetAssembly.reducedAssemblyHom_toModel", "BC4lean.Chapter8Examples.CosetAssembly.toModel", "BC4lean.Chapter8Examples.CosetAssemblyUnit.cosetUnitClass", "BC4lean.Chapter8Examples.CosetAssemblyUnit.lambdaGroup", "BC4lean.Chapter8Examples.CosetAssemblyUnit.lambdaGroup_le", "BC4lean.Chapter8Examples.CosetAssemblyUnit.reducedAssemblyHom_cosetUnitClass", "BC4lean.Chapter8Examples.CosetAssemblyUnit.reducedAssemblyHom_ne_zero", "BC4lean.Chapter8Examples.CosetAssemblyUnit.reducedTraceK0_assembly_cosetUnitClass", "BC4lean.Chapter8Examples.CosetAssemblyUnit.subgroupElement_eq", "BC4lean.Chapter8Examples.CosetUnitCycle.multiplication_isModuleCompact", "BC4lean.Chapter8Examples.FiniteAbelianAssembly.finiteAbelianAnalyticEquiv", "BC4lean.Chapter8Examples.FiniteAbelianAssembly.spaceAssemblyHom_finiteAbelian", "BC4lean.Chapter8Examples.FiniteAssemblyUnit.assembly_unitClass_not_mem_zmultiples", "BC4lean.Chapter8Examples.FiniteAssemblyUnit.reducedAssemblyHom_characterClass", "BC4lean.Chapter8Examples.FiniteAssemblyUnit.reducedAssemblyHom_unitClass", "BC4lean.Chapter8Examples.FiniteAssemblyUnit.reducedTraceK0_assembly_unitClass", "BC4lean.Chapter8Examples.FiniteGroupPoint", "BC4lean.Chapter8Examples.FinitePointAssembly.spaceAssembly_even_class", "BC4lean.Chapter8Examples.FinitePointAssembly.spaceAssembly_odd_class", "BC4lean.Chapter8Examples.OrderTwoAssembly.orderTwoAnalyticEquiv", "BC4lean.Chapter8Examples.OrderTwoAssembly.spaceAssemblyHom_orderTwo", "BC4lean.Chapter8Examples.SubsingletonAssembly.assemblyAddEquiv", "BC4lean.Chapter8Examples.SubsingletonAssembly.baumConnesProperty_of_subsingleton", "BC4lean.Chapter8Examples.SubsingletonAssembly.reducedAssemblyHom_eq", "BC4lean.Chapter8Examples.assemblyHom_eq_compactSpaceAssembly", "BC4lean.Chapter8Examples.baumConnesProperty_of_card_two", "BC4lean.Chapter8Examples.baumConnesProperty_of_finite", "BC4lean.Chapter8Examples.baumConnesProperty_of_finite_commGroup", "BC4lean.Chapter8Examples.baumConnesProperty_of_pointGreenJulg_bijective", "BC4lean.Chapter8Examples.baumConnesProperty_unit", "BC4lean.Chapter8Examples.baumConnesProperty_zmod_two", "BC4lean.Chapter8Examples.compactSpaceGroupEquiv", "BC4lean.Chapter8Examples.compactWholePieceEquiv", "BC4lean.Chapter8Examples.cutoffProduct_descent_eq_coefficient", "BC4lean.Chapter8Examples.finiteAbelianAssemblyAddEquiv", "BC4lean.Chapter8Examples.finiteAbelianReducedK0Equiv", "BC4lean.Chapter8Examples.finiteAssemblyAddEquiv", "BC4lean.Chapter8Examples.finiteCanonicalGlobalFixedPoint", "BC4lean.Chapter8Examples.finiteCanonicalPointHomotopyEquiv", "BC4lean.Chapter8Examples.finiteCanonicalPointKHomologyEquiv", "BC4lean.Chapter8Examples.finiteGroupPoint_fixedPointCriterion", "BC4lean.Chapter8Examples.finiteGroupPoint_fixedPoints_contractible", "BC4lean.Chapter8Examples.finiteGroupPoint_proper", "BC4lean.Chapter8Examples.finitePointCutoff", "BC4lean.Chapter8Examples.finiteTopologicalPointSpaceEquiv", "BC4lean.Chapter8Examples.le_wholeCompactPiece", "BC4lean.Chapter8Examples.orderTwoAssemblyAddEquiv", "BC4lean.Chapter8Examples.reducedAssemblyHom_finiteAbelian_eq", "BC4lean.Chapter8Examples.reducedAssemblyHom_finitePoint", "BC4lean.Chapter8Examples.reducedAssemblyHom_finitePoint_formula", "BC4lean.Chapter8Examples.reducedAssemblyHom_finite_eq", "BC4lean.Chapter8Examples.reducedAssemblyHom_orderTwo_eq", "BC4lean.Chapter8Examples.reducedAssemblyHom_unit_eq", "BC4lean.Chapter8Examples.reducedScalarKKToAnalyticHom_bijective", "BC4lean.Chapter8Examples.reducedScalarKKToK0Hom_coefficient", "BC4lean.Chapter8Examples.reducedScalarKKToK1Hom_coefficient", "BC4lean.Chapter8Examples.spaceAssemblyHom_eq_unitPointEquiv", "BC4lean.Chapter8Examples.terminalColimitEquiv", "BC4lean.Chapter8Examples.terminalColimitEquiv_of", "BC4lean.Chapter8Examples.terminalEvaluation", "BC4lean.Chapter8Examples.trivialAnalyticK0Equiv", "BC4lean.Chapter8Examples.trivialAnalyticK0Equiv_projection", "BC4lean.Chapter8Examples.trivialAnalyticK1Equiv", "BC4lean.Chapter8Examples.trivialAnalyticK1Equiv_unitary", "BC4lean.Chapter8Examples.trivialReducedK0Equiv", "BC4lean.Chapter8Examples.trivialReducedK0Equiv_one", "BC4lean.Chapter8Examples.trivialReducedK1_eq_zero", "BC4lean.Chapter8Examples.unitAssemblyAddEquiv", "BC4lean.Chapter8Examples.unitPointSourceEquiv", "BC4lean.Chapter8Examples.unitScalarAnalyticEquiv", "BC4lean.Chapter8Examples.wholeCompactPiece", "BC4lean.CharacterDual.card_eq", "BC4lean.KKTheory.CosetCompressedDescent.even_compressedDescent", "BC4lean.KKTheory.CosetCompressedDescent.subgroupProjection_isStarProjection", "BC4lean.KKTheory.FinitePointCharacterTensor.characterIsometry", "BC4lean.KKTheory.FinitePointCharacterTensor.characterProjection_isStarProjection", "BC4lean.KKTheory.FinitePointCharacterTensor.characterRangeEquiv", "BC4lean.KKTheory.FinitePointCharacterTensor.reducedSourceRepresentation_averaging_mk", "BC4lean.KKTheory.FinitePointCompressedDescent.characterCycleIso", "BC4lean.KKTheory.FinitePointCompressedDescent.even_compressedDescent", "BC4lean.KKTheory.FinitePointCompressedDescent.oddCharacterCycleIso", "BC4lean.KKTheory.FinitePointCompressedDescent.odd_compressedDescent", "BC4lean.KKTheory.FinitePointCutoff.averaging", "BC4lean.KKTheory.FinitePointCutoff.averaging_coe", "BC4lean.KKTheory.FinitePointCutoff.cutoffKKClass_eq_averagingHomClass", "BC4lean.KKTheory.FinitePointCutoff.cutoffKKClass_eq_homClass", "BC4lean.KKTheory.FinitePointCutoff.cutoffProductHom_eq_averagingPullback", "BC4lean.KKTheory.FinitePointCutoff.cutoffProductHom_eq_sourcePullback", "BC4lean.KKTheory.FinitePointCutoff.cutoff_apply", "BC4lean.KKTheory.FinitePointCutoff.projectionScalarHom", "BC4lean.KKTheory.FinitePointCutoff.reducedCutoffProjection_eq_averaging", "BC4lean.KKTheory.GreenJulgCorrespondence.greenJulgInverse", "BC4lean.KKTheory.GreenJulgPoint.greenJulgInverse_pointGreenJulgHom", "BC4lean.KKTheory.GreenJulgPoint.greenJulgPointEquiv", "BC4lean.KKTheory.GreenJulgPoint.pointGreenJulgHom", "BC4lean.KKTheory.GreenJulgPoint.pointGreenJulgHom_greenJulgInverse", "BC4lean.KKTheory.GroupRestriction.cycleComap", "BC4lean.KKTheory.GroupRestriction.evenComap", "BC4lean.KKTheory.GroupRestriction.oddComap", "BC4lean.KKTheory.GroupRestriction.subsingletonParityEquiv", "BC4lean.KKTheory.KasparovHomotopyClass.orderTwoSplit", "BC4lean.KKTheory.OddKK.orderTwoSplit", "BC4lean.KKTheory.ScalarUnitProjection.identity_universe", "BC4lean.KKTheory.ScalarUnitProjection.relativeMap_nonunitalUnitProjection", "BC4lean.KKTheory.ScalarUnitProjection.scalarKKOperatorK0AddEquiv_identity", "BC4lean.KKTheory.ScalarUnitProjection.scalarKKOperatorK0AddEquiv_identity_universe", "BC4lean.KKTheory.ScalarUnitProjection.unitRelativeCycleIso", "BC4lean.KKTheory.SubsingletonScalarDescent.evenClass_coefficientRestriction", "BC4lean.KKTheory.SubsingletonScalarDescent.oddClass_coefficientRestriction", "BC4lean.KKTheory.UnitPointCutoff.algebraicProjection_eq_single", "BC4lean.KKTheory.UnitPointCutoff.cutoffKKClass_eq_homClass", "BC4lean.KKTheory.UnitPointCutoff.cutoff_square_one", "BC4lean.KKTheory.UnitPointCutoff.pointCZeroEquiv", "BC4lean.KKTheory.UnitPointCutoff.reducedCutoffProjection_eq_scalarCoefficient", "BC4lean.KKTheory.UnitPointCutoff.scalarToCZero", "BC4lean.KKTheory.UnitScalarDescent.evenClass_coefficientRestriction", "BC4lean.KKTheory.UnitScalarDescent.oddClass_coefficientRestriction", "BC4lean.KKTheory.finiteAbelianPointKKSplit", "BC4lean.KKTheory.orderTwoKKParitySplit", "BC4lean.KKTheory.orderTwoPointKKSplit", "BC4lean.KKTheory.sourcePullbackEquiv", "BC4lean.finiteAbelianReducedEquiv", "BC4lean.reducedK0EquivOfStarAlgEquiv", "BC4lean.reducedK0_finite", "BC4lean.reducedK0_of_card_eq_two", "BC4lean.reducedK0_of_commute", "BC4lean.reducedK1_eq_zero_of_starAlgEquiv", "BC4lean.reducedK1_finite"]
  let mut declarations : Array (String × Lean.Name) := #[]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let origin := env.header.moduleNames[idx]!.toString
      if modules.contains origin then
        if info matches .axiomInfo _ then
          throwError "New axiom declaration {name} in {origin}"
        declarations := declarations.push (origin, name)
  Lean.Elab.Command.liftIO <| IO.println "CH8_START|1"
  for (origin, name) in declarations do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected axiom {axiomName} in {name}"
    let axiomText := String.intercalate "," (axioms.toList.map Lean.Name.toString)
    Lean.Elab.Command.liftIO <| IO.println s!"CH8_DECL|{origin}|{name.toString}|{axiomText}"
    let some info := env.find? name
      | throwError "Missing declaration metadata {name}"
    let kind := match info with
      | .axiomInfo _ => "axiom"
      | .defnInfo _ => "definition"
      | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
    Lean.Elab.Command.liftIO <| IO.println s!"CH8_KIND|{name.toString}|{kind}"
  for text in (links ++ endpoints).toList.eraseDups do
    let name := text.toName
    unless (env.find? name).isSome do
      throwError "Unknown exact blueprint/endpoint declaration {text}"
    if endpoints.contains text then
      let some idx := env.getModuleIdxFor? name
        | throwError "Missing imported endpoint origin {text}"
      unless modules.contains env.header.moduleNames[idx]!.toString do
        throwError "Required endpoint outside the Chapter 8 declaration scope: {text}"
  for text in links do
    let name := text.toName
    let some idx := env.getModuleIdxFor? name
      | throwError "Missing imported origin for blueprint link {text}"
    let origin := env.header.moduleNames[idx]!.toString
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "Unexpected axiom {axiomName} in blueprint link {text}"
    let axiomText := String.intercalate "," (axioms.toList.map Lean.Name.toString)
    Lean.Elab.Command.liftIO <| IO.println s!"CH8_LINK|{text}|{origin}|{axiomText}"
  for origin in modules do
    let count := (declarations.filter (·.1 == origin)).size
    Lean.Elab.Command.liftIO <| IO.println s!"CH8_MODULE|{origin}|{count}"
  for text in endpoints do
    let name := text.toName
    let some idx := env.getModuleIdxFor? name
      | throwError "Missing imported endpoint origin {text}"
    let origin := env.header.moduleNames[idx]!.toString
    let axioms ← Lean.collectAxioms name
    let axiomText := String.intercalate "," (axioms.toList.map Lean.Name.toString)
    Lean.Elab.Command.liftIO <| IO.println s!"CH8_ENDPOINT|{text}|{origin}|{axiomText}"
  Lean.Elab.Command.liftIO <| IO.println s!"CH8_END|{declarations.size}|{links.size}|{endpoints.size}"

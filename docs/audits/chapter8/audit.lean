import BC4lean.AssemblyBijectivityCriteria
import BC4lean.BaumConnesInvariance
import BC4lean.BaumConnesProperty
import BC4lean.CompactModelColimitCalibration
import BC4lean.FiniteGroupPointCalibration
import BC4lean.FinitePointCutoff
import BC4lean.FiniteReducedGroupCStar
import BC4lean.KKGroupRestriction
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
  let modules : Array String := #["BC4lean.AssemblyBijectivityCriteria", "BC4lean.BaumConnesInvariance", "BC4lean.BaumConnesProperty", "BC4lean.CompactModelColimitCalibration", "BC4lean.FiniteGroupPointCalibration", "BC4lean.FinitePointCutoff", "BC4lean.FiniteReducedGroupCStar", "BC4lean.KKGroupRestriction", "BC4lean.ScalarIdentityUniverse", "BC4lean.ScalarOperatorK0", "BC4lean.ScalarOperatorK1", "BC4lean.ScalarOperatorKNonunital", "BC4lean.ScalarProjectionRank", "BC4lean.ScalarUnitProjection", "BC4lean.SubsingletonAssemblyEquivalence", "BC4lean.SubsingletonScalarDescent", "BC4lean.TrivialAnalyticCalibration", "BC4lean.TrivialAnalyticScalar", "BC4lean.UnitAssemblyEquivalence", "BC4lean.UnitPointCutoff", "BC4lean.UnitScalarDescent"]
  let links : Array String := #["BC4lean.Assembly.BaumConnesConjecture", "BC4lean.Assembly.BaumConnesProperty", "BC4lean.Assembly.assemblyHom_bijective_iff_homotopyEquiv", "BC4lean.Assembly.assemblyHom_bijective_iff_pieceCriteria", "BC4lean.Assembly.assemblyHom_injective_iff_commonTransition", "BC4lean.Assembly.assemblyHom_injective_iff_homotopyEquiv", "BC4lean.Assembly.assemblyHom_surjective_iff_homotopyEquiv", "BC4lean.Assembly.assemblyHom_surjective_iff_pieceImages", "BC4lean.Assembly.baumConnesProperty_iff_even_and_odd", "BC4lean.Assembly.indexedAssemblyHom_bijective_iff_cofinalIndex", "BC4lean.Assembly.indexedAssemblyHom_injective_iff_cofinalIndex", "BC4lean.Assembly.indexedAssemblyHom_surjective_iff_cofinalIndex", "BC4lean.Assembly.indexedAssemblyProperty_iff_cofinalComparison", "BC4lean.Assembly.modelAssemblyProperty_iff_baumConnesProperty", "BC4lean.Chapter8Examples.FiniteGroupPoint", "BC4lean.Chapter8Examples.SubsingletonAssembly.assemblyAddEquiv", "BC4lean.Chapter8Examples.SubsingletonAssembly.baumConnesProperty_of_subsingleton", "BC4lean.Chapter8Examples.SubsingletonAssembly.reducedAssemblyHom_eq", "BC4lean.Chapter8Examples.assemblyHom_eq_compactSpaceAssembly", "BC4lean.Chapter8Examples.baumConnesProperty_unit", "BC4lean.Chapter8Examples.compactSpaceGroupEquiv", "BC4lean.Chapter8Examples.finiteCanonicalGlobalFixedPoint", "BC4lean.Chapter8Examples.finiteCanonicalPointHomotopyEquiv", "BC4lean.Chapter8Examples.finiteTopologicalPointSpaceEquiv", "BC4lean.Chapter8Examples.reducedAssemblyHom_finitePoint_formula", "BC4lean.Chapter8Examples.reducedAssemblyHom_unit_eq", "BC4lean.Chapter8Examples.terminalColimitEquiv", "BC4lean.Chapter8Examples.trivialAnalyticK0Equiv", "BC4lean.Chapter8Examples.trivialAnalyticK0Equiv_projection", "BC4lean.Chapter8Examples.trivialAnalyticK1Equiv", "BC4lean.Chapter8Examples.trivialAnalyticK1Equiv_unitary", "BC4lean.Chapter8Examples.trivialReducedK0Equiv", "BC4lean.Chapter8Examples.trivialReducedK0Equiv_one", "BC4lean.Chapter8Examples.trivialReducedK1_eq_zero", "BC4lean.Chapter8Examples.unitAssemblyAddEquiv", "BC4lean.Chapter8Examples.wholeCompactPiece", "BC4lean.KKTheory.FinitePointCutoff.averaging", "BC4lean.KKTheory.FinitePointCutoff.averaging_coe", "BC4lean.KKTheory.FinitePointCutoff.cutoffKKClass_eq_averagingHomClass", "BC4lean.KKTheory.FinitePointCutoff.cutoffKKClass_eq_homClass", "BC4lean.KKTheory.FinitePointCutoff.cutoffProductHom_eq_averagingPullback", "BC4lean.KKTheory.FinitePointCutoff.cutoffProductHom_eq_sourcePullback", "BC4lean.KKTheory.FinitePointCutoff.cutoff_apply", "BC4lean.KKTheory.FinitePointCutoff.projectionScalarHom", "BC4lean.KKTheory.FinitePointCutoff.reducedCutoffProjection_eq_averaging", "BC4lean.KKTheory.GroupRestriction.cycleComap", "BC4lean.KKTheory.GroupRestriction.evenComap", "BC4lean.KKTheory.GroupRestriction.oddComap", "BC4lean.KKTheory.GroupRestriction.subsingletonParityEquiv", "BC4lean.KKTheory.ScalarUnitProjection.identity_universe", "BC4lean.KKTheory.ScalarUnitProjection.relativeMap_nonunitalUnitProjection", "BC4lean.KKTheory.ScalarUnitProjection.scalarKKOperatorK0AddEquiv_identity", "BC4lean.KKTheory.ScalarUnitProjection.scalarKKOperatorK0AddEquiv_identity_universe", "BC4lean.KKTheory.ScalarUnitProjection.unitRelativeCycleIso", "BC4lean.KKTheory.SubsingletonScalarDescent.evenClass_coefficientRestriction", "BC4lean.KKTheory.SubsingletonScalarDescent.oddClass_coefficientRestriction", "BC4lean.KKTheory.UnitPointCutoff.cutoffKKClass_eq_homClass", "BC4lean.KKTheory.UnitPointCutoff.pointCZeroEquiv", "BC4lean.KKTheory.UnitPointCutoff.reducedCutoffProjection_eq_scalarCoefficient", "BC4lean.KKTheory.UnitScalarDescent.evenClass_coefficientRestriction", "BC4lean.KKTheory.UnitScalarDescent.evenCoefficientRestrictionIso", "BC4lean.KKTheory.UnitScalarDescent.oddClass_coefficientRestriction", "BC4lean.KKTheory.UnitScalarDescent.oddCoefficientRestrictionIso"]
  let endpoints : Array String := #["BC4lean.Assembly.BaumConnesConjecture", "BC4lean.Assembly.BaumConnesProperty", "BC4lean.Assembly.assemblyHom_bijective_iff_canonical", "BC4lean.Assembly.assemblyHom_bijective_iff_homotopyEquiv", "BC4lean.Assembly.assemblyHom_bijective_iff_pieceCriteria", "BC4lean.Assembly.assemblyHom_bijective_iff_universalModels", "BC4lean.Assembly.assemblyHom_injective_iff_commonTransition", "BC4lean.Assembly.assemblyHom_injective_iff_homotopyEquiv", "BC4lean.Assembly.assemblyHom_surjective_iff_homotopyEquiv", "BC4lean.Assembly.assemblyHom_surjective_iff_pieceImages", "BC4lean.Assembly.baumConnesProperty_iff_even_and_odd", "BC4lean.Assembly.indexedAssemblyHom_bijective_iff_cofinalComparison", "BC4lean.Assembly.indexedAssemblyHom_bijective_iff_cofinalIndex", "BC4lean.Assembly.indexedAssemblyHom_injective_iff_cofinalIndex", "BC4lean.Assembly.indexedAssemblyHom_surjective_iff_cofinalIndex", "BC4lean.Assembly.indexedAssemblyProperty", "BC4lean.Assembly.indexedAssemblyProperty_iff_cofinalComparison", "BC4lean.Assembly.indexedAssemblyProperty_iff_cofinalIndex", "BC4lean.Assembly.modelAssemblyProperty", "BC4lean.Assembly.modelAssemblyProperty_iff_baumConnesProperty", "BC4lean.Assembly.modelAssemblyProperty_iff_homotopyEquiv", "BC4lean.Assembly.modelAssemblyProperty_iff_universalModels", "BC4lean.Chapter8Examples.FiniteGroupPoint", "BC4lean.Chapter8Examples.SubsingletonAssembly.assemblyAddEquiv", "BC4lean.Chapter8Examples.SubsingletonAssembly.baumConnesProperty_of_subsingleton", "BC4lean.Chapter8Examples.SubsingletonAssembly.reducedAssemblyHom_eq", "BC4lean.Chapter8Examples.assemblyHom_eq_compactSpaceAssembly", "BC4lean.Chapter8Examples.baumConnesProperty_unit", "BC4lean.Chapter8Examples.compactSpaceGroupEquiv", "BC4lean.Chapter8Examples.compactWholePieceEquiv", "BC4lean.Chapter8Examples.cutoffProduct_descent_eq_coefficient", "BC4lean.Chapter8Examples.finiteCanonicalGlobalFixedPoint", "BC4lean.Chapter8Examples.finiteCanonicalPointHomotopyEquiv", "BC4lean.Chapter8Examples.finiteCanonicalPointKHomologyEquiv", "BC4lean.Chapter8Examples.finiteGroupPoint_fixedPointCriterion", "BC4lean.Chapter8Examples.finiteGroupPoint_fixedPoints_contractible", "BC4lean.Chapter8Examples.finiteGroupPoint_proper", "BC4lean.Chapter8Examples.finitePointCutoff", "BC4lean.Chapter8Examples.finiteTopologicalPointSpaceEquiv", "BC4lean.Chapter8Examples.le_wholeCompactPiece", "BC4lean.Chapter8Examples.reducedAssemblyHom_finitePoint", "BC4lean.Chapter8Examples.reducedAssemblyHom_finitePoint_formula", "BC4lean.Chapter8Examples.reducedAssemblyHom_unit_eq", "BC4lean.Chapter8Examples.reducedScalarKKToK0Hom_coefficient", "BC4lean.Chapter8Examples.reducedScalarKKToK1Hom_coefficient", "BC4lean.Chapter8Examples.spaceAssemblyHom_eq_unitPointEquiv", "BC4lean.Chapter8Examples.terminalColimitEquiv", "BC4lean.Chapter8Examples.terminalColimitEquiv_of", "BC4lean.Chapter8Examples.terminalEvaluation", "BC4lean.Chapter8Examples.trivialAnalyticK0Equiv", "BC4lean.Chapter8Examples.trivialAnalyticK0Equiv_projection", "BC4lean.Chapter8Examples.trivialAnalyticK1Equiv", "BC4lean.Chapter8Examples.trivialAnalyticK1Equiv_unitary", "BC4lean.Chapter8Examples.trivialReducedK0Equiv", "BC4lean.Chapter8Examples.trivialReducedK0Equiv_one", "BC4lean.Chapter8Examples.trivialReducedK1_eq_zero", "BC4lean.Chapter8Examples.unitAssemblyAddEquiv", "BC4lean.Chapter8Examples.unitPointSourceEquiv", "BC4lean.Chapter8Examples.unitScalarAnalyticEquiv", "BC4lean.Chapter8Examples.wholeCompactPiece", "BC4lean.KKTheory.FinitePointCutoff.averaging", "BC4lean.KKTheory.FinitePointCutoff.averaging_coe", "BC4lean.KKTheory.FinitePointCutoff.cutoffKKClass_eq_averagingHomClass", "BC4lean.KKTheory.FinitePointCutoff.cutoffKKClass_eq_homClass", "BC4lean.KKTheory.FinitePointCutoff.cutoffProductHom_eq_averagingPullback", "BC4lean.KKTheory.FinitePointCutoff.cutoffProductHom_eq_sourcePullback", "BC4lean.KKTheory.FinitePointCutoff.cutoff_apply", "BC4lean.KKTheory.FinitePointCutoff.projectionScalarHom", "BC4lean.KKTheory.FinitePointCutoff.reducedCutoffProjection_eq_averaging", "BC4lean.KKTheory.GroupRestriction.cycleComap", "BC4lean.KKTheory.GroupRestriction.evenComap", "BC4lean.KKTheory.GroupRestriction.oddComap", "BC4lean.KKTheory.GroupRestriction.subsingletonParityEquiv", "BC4lean.KKTheory.ScalarUnitProjection.identity_universe", "BC4lean.KKTheory.ScalarUnitProjection.relativeMap_nonunitalUnitProjection", "BC4lean.KKTheory.ScalarUnitProjection.scalarKKOperatorK0AddEquiv_identity", "BC4lean.KKTheory.ScalarUnitProjection.scalarKKOperatorK0AddEquiv_identity_universe", "BC4lean.KKTheory.ScalarUnitProjection.unitRelativeCycleIso", "BC4lean.KKTheory.SubsingletonScalarDescent.evenClass_coefficientRestriction", "BC4lean.KKTheory.SubsingletonScalarDescent.oddClass_coefficientRestriction", "BC4lean.KKTheory.UnitPointCutoff.algebraicProjection_eq_single", "BC4lean.KKTheory.UnitPointCutoff.cutoffKKClass_eq_homClass", "BC4lean.KKTheory.UnitPointCutoff.cutoff_square_one", "BC4lean.KKTheory.UnitPointCutoff.pointCZeroEquiv", "BC4lean.KKTheory.UnitPointCutoff.reducedCutoffProjection_eq_scalarCoefficient", "BC4lean.KKTheory.UnitPointCutoff.scalarToCZero", "BC4lean.KKTheory.UnitScalarDescent.evenClass_coefficientRestriction", "BC4lean.KKTheory.UnitScalarDescent.oddClass_coefficientRestriction"]
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

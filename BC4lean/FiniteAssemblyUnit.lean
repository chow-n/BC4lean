import BC4lean.FinitePointCharacterAssembly
import BC4lean.ReducedGroupTrace
import BC4lean.ScalarUnitProjection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The assembly map of a finite group sends the unit class to the averaging projection

For a finite group `Γ`, let `1_Γ ∈ KK^Γ(C₀(pt), ℂ)` be the native identity class of `KK(ℂ, ℂ)`
pulled back to the point and inflated along `Γ → 1`, i.e. `ℂ` with the trivial representation.
Its reduced assembly is the class of the averaging projection `p_Γ = |Γ|⁻¹ ∑_g λ_g`
(`reducedAssemblyHom_unitClass`), so the canonical trace of the assembled class is `1 / |Γ|`
(`reducedTraceK0_assembly_unitClass`). For `|Γ| > 1` the assembled class is not an integer multiple
of `[1]` (`assembly_unitClass_not_mem_zmultiples`).

More generally, for a character `χ : Γ → U(1)` the class `χ ⊗ 1_Γ` (the module action twisted by
`χ`) assembles to `[e_χ]`, `e_χ = |Γ|⁻¹ ∑_g χ(g) λ_g`, again of trace `1 / |Γ|`
(`reducedAssemblyHom_characterClass`); the unit class is the case `χ = 1`.

The canonical colimit is the point model (`reducedAssemblyHom_finitePoint`); on a `χ`-twisted
inflated point class the assembly map is `(P_χ)_*` of the scalar index
(`spaceAssembly_even_class`, `FinitePointCharacterAssembly`); the scalar index of the identity
class is `[1]`
(`scalarKKOperatorK0AddEquiv_identity`), and `[1]` is carried to `[P_χ]`
(`nonunitalProjectionK0_map`). Under `C*_r(Γ ⋉ ℂ) ≅ C*_r(Γ)` the projection `P_χ` is `e_χ`, and
`P_1` is `p_Γ`. -/

noncomputable section

namespace BC4lean.OperatorKTheory

local instance (priority := high) unitAgreementSpectralOrder (B : Type*) [CStarAlgebra B] : PartialOrder B :=
  CStarAlgebra.spectralOrder B
local instance (priority := high) unitAgreementSpectralOrderedRing (B : Type*) [CStarAlgebra B] :
    StarOrderedRing B :=
  CStarAlgebra.spectralOrderedRing B

/-- For unital `C`, the agreement `OperatorK0 C ≃ K0 C` sends `[e]` to the class of `e`. -/
theorem operatorK0UnitalEquiv_nonunitalProjectionK0 {C : Type*} [CStarAlgebra C] (e : C)
    (he : IsStarProjection e) :
    operatorK0UnitalEquiv C (nonunitalProjectionK0 e he) =
      k0Projection (FiniteProjection.ofProjection (unitMatrixProjection e he)) := by
  rw [operatorK0UnitalEquiv_apply, operatorK0Inclusion_nonunitalProjectionK0, nonunitalFiniteProjection,
    k0Map_projection]
  have h : matrixProjectionMap (unitizationEval C)
      (⟨nonunitalProjectionMatrix e, nonunitalProjectionMatrix_isStarProjection e he⟩ :
        MatrixProjection (Unitization ℂ C) PUnit.{1}) = unitMatrixProjection e he := by
    apply Subtype.ext
    ext i j
    change unitizationEval C (e : Unitization ℂ C) = e
    simp
  change k0Projection (FiniteProjection.ofProjection (matrixProjectionMap (unitizationEval C)
    (⟨nonunitalProjectionMatrix e, nonunitalProjectionMatrix_isStarProjection e he⟩ :
      MatrixProjection (Unitization ℂ C) PUnit.{1}))) = _
  rw [h]

end BC4lean.OperatorKTheory

namespace BC4lean.Chapter8Examples.FiniteAssemblyUnit
open ProperActions KKTheory OperatorKTheory FinitePointAssembly
open KKTheory.GroupUniverseParityGroup KKTheory.GroupUniverseParityFunctoriality
open KKTheory.FinitePointCompressedDescent KKTheory.FinitePointCharacterTensor KKTheory.FinitePointCutoff
open scoped ZeroAtInfty ComplexOrder KasparovDescent

local instance pointCZero_separable : TopologicalSpace.SeparableSpace C₀(FiniteGroupPoint.{0}, ℂ) :=
  TopologicalKHomology.cZero_separableSpace

variable {Γ : Type} [Group Γ] [Countable Γ] [Fintype Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]

variable (Γ) in
/-- The point class of a scalar class: pull back to the point, inflate along `Γ → 1`, twist by `χ`. -/
abbrev pointClass (χ : Γ →* unitary ℂ) (a : KasparovHomotopyClass.{0,0,0,0} unitScalarAction unitScalarAction) :
    TopologicalKHomology.spaceGroup false Γ FiniteGroupPoint.{0} :=
  KasparovHomotopyClass.twist χ (KasparovHomotopyClass.comap (1 : Γ →* Unit)
    (CStarAlgebraAction.apply_eq_trivial_unit (pointAction Γ))
    (CStarAlgebraAction.apply_eq_trivial_unit (scalarAction Γ))
    (sourcePullback.{0,0,0,0,0} false pointEval pointEval_equivariant a))

/-! ### `P_χ` in `C*_r(Γ)` -/

/- The spectral order on `C*_r(Γ)`, as in `ReducedGroupTrace` (only on this algebra, so the orders on
`ℂ` stay the standard ones). -/
local instance unitClassSpectralOrder (Γ : Type) [Group Γ] :
    PartialOrder (ReducedGroupCStar Γ) :=
  CStarAlgebra.spectralOrder _
local instance unitClassSpectralOrderedRing (Γ : Type) [Group Γ] :
    StarOrderedRing (ReducedGroupCStar Γ) :=
  CStarAlgebra.spectralOrderedRing _

omit [Fintype Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- The crossed-product equivalence sends `λ_g` to `λ_g`. -/
theorem crossedHom_regular_eq_reducedDelta (g : Γ) : crossedHom Γ (regular Γ g) = reducedDelta Γ g := by
  rw [crossedHom_regular]
  exact Subtype.ext (reducedDelta_coe g).symm

variable (Γ) in
/-- `e_χ = |Γ|⁻¹ ∑_g χ(g) λ_g ∈ C*_r(Γ)`, the image of `P_χ`. -/
abbrev characterElement (χ : Γ →* unitary ℂ) : ReducedGroupCStar Γ :=
  crossedHom Γ (characterProjection Γ χ)

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
theorem characterElement_isStarProjection (χ : Γ →* unitary ℂ) :
    IsStarProjection (characterElement Γ χ) :=
  (characterProjection_isStarProjection Γ χ).map (crossedHom Γ)

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- `z ↦ z • P_χ`, read in `C*_r(Γ)`, sends `1` to `e_χ`. -/
theorem crossedHom_characterHom_one (χ : Γ →* unitary ℂ) :
    (crossedHom Γ).comp (characterHom Γ χ) 1 = characterElement Γ χ := by
  change crossedHom Γ ((1 : ℂ) • characterProjection Γ χ) = _
  rw [one_smul]

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- `e_1 = p_Γ`. -/
theorem characterElement_one : characterElement Γ 1 = averagingElement Γ := by
  rw [characterElement, characterProjection, map_sum, averagingElement, Finset.smul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smul, crossedHom_regular_eq_reducedDelta, MonoidHom.one_apply, OneMemClass.coe_one, mul_one]

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- `τ(e_χ) = 1 / |Γ|`. -/
theorem reducedTrace_characterElement (χ : Γ →* unitary ℂ) :
    (reducedTrace Γ).toLinearMap (characterElement Γ χ) = (Fintype.card Γ : ℂ)⁻¹ := by
  classical
  rw [characterElement, characterProjection, map_sum, map_sum]
  simp only [map_smul, crossedHom_regular_eq_reducedDelta, reducedTrace_reducedDelta]
  simp

variable (Γ) in
/-- `[e_χ] ∈ K₀(C*_r Γ)`. -/
def characterK0Class (χ : Γ →* unitary ℂ) : ReducedK0 Γ :=
  reducedK0Class Γ (StableProjectionMonoid.of (FiniteProjection.ofProjection
    (unitMatrixProjection (characterElement Γ χ) (characterElement_isStarProjection χ))))

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
theorem reducedTraceK0_characterK0Class (χ : Γ →* unitary ℂ) :
    reducedTraceK0 Γ (characterK0Class Γ χ) = (Fintype.card Γ : ℝ)⁻¹ := by
  rw [characterK0Class, reducedTraceK0_class]
  change ((reducedTrace Γ).projectionTrace
    (unitMatrixProjection (characterElement Γ χ) (characterElement_isStarProjection χ))).re = _
  rw [TracialFunctional.projectionTrace_unitMatrixProjection, reducedTrace_characterElement]
  simp

omit [Countable Γ] [Fintype Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] in
theorem k0Projection_unitMatrixProjection_congr {e e' : ReducedGroupCStar Γ} (h : e = e')
    (he : IsStarProjection e) (he' : IsStarProjection e') :
    k0Projection (FiniteProjection.ofProjection (unitMatrixProjection e he)) =
      k0Projection (FiniteProjection.ofProjection (unitMatrixProjection e' he')) := by
  subst h
  rfl

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
theorem characterK0Class_one : characterK0Class Γ 1 = averagingClass Γ :=
  k0Projection_unitMatrixProjection_congr characterElement_one _ _

/-! ### The unit class, character classes and their assembly -/

/-- The native identity class of `KK(ℂ, ℂ)`. -/
abbrev scalarUnitKK : KasparovHomotopyClass.{0,0,0,0} unitScalarAction unitScalarAction :=
  GroupUniverseParityUnits.identity.{0,0,0} ScalarUnitProjection.scalarIdentityAction

/-- Its scalar index is `[1] ∈ K₀(ℂ)`. -/
theorem scalarKKOperatorK0AddEquiv_scalarUnitKK :
    scalarKKOperatorK0AddEquiv scalarUnitKK =
      nonunitalProjectionK0 (1 : ℂ) (IsStarProjection.one ℂ) :=
  ScalarUnitProjection.scalarKKOperatorK0AddEquiv_identity

variable (Γ) in
/-- `χ ⊗ 1_Γ`: the unit class of the point twisted by `χ`, in `K^Γ_0(E_FIN Γ)` (via
`finiteTopologicalPointSpaceEquiv`). -/
def characterClass (χ : Γ →* unitary ℂ) : TopologicalKHomology.topologicalGroup false Γ :=
  (finiteTopologicalPointSpaceEquiv Γ false).symm (pointClass Γ χ scalarUnitKK)

variable (Γ) in
/-- The unit class of the point: the identity class of `KK(ℂ, ℂ)` pulled back to `C₀(pt)` and
inflated along `Γ → 1`, an element of `KK^Γ(C₀(pt), ℂ)`. -/
def pointUnitClass : TopologicalKHomology.spaceGroup false Γ FiniteGroupPoint.{0} :=
  KasparovHomotopyClass.comap (1 : Γ →* Unit)
    (CStarAlgebraAction.apply_eq_trivial_unit (pointAction Γ))
    (CStarAlgebraAction.apply_eq_trivial_unit (scalarAction Γ))
    (sourcePullback.{0,0,0,0,0} false pointEval pointEval_equivariant scalarUnitKK)

variable (Γ) in
/-- The unit class in the canonical topological `K`-homology of `Γ`. -/
def unitClass : TopologicalKHomology.topologicalGroup false Γ :=
  (finiteTopologicalPointSpaceEquiv Γ false).symm (pointUnitClass Γ)

theorem characterClass_one : characterClass Γ 1 = unitClass Γ := by
  rw [characterClass, unitClass, pointClass, twist_one_even]
  rfl

/-- `μ₀(χ ⊗ 1_Γ) = [e_χ]` for every character `χ` of the finite group `Γ`. -/
theorem reducedAssemblyHom_characterClass (χ : Γ →* unitary ℂ) :
    Assembly.reducedAssemblyHom Γ false (characterClass Γ χ) = characterK0Class Γ χ := by
  let : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
  rw [reducedAssemblyHom_finitePoint, characterClass, AddEquiv.apply_symm_apply,
    spaceAssembly_even_class, scalarKKOperatorK0AddEquiv_scalarUnitKK, nonunitalProjectionK0_map,
    operatorK0UnitalEquiv_nonunitalProjectionK0]
  exact k0Projection_unitMatrixProjection_congr (crossedHom_characterHom_one χ) _ _

/-- For a finite group `Γ`, the reduced assembly map `μ₀` sends the unit class of the
point to the class of the averaging projection `p_Γ = |Γ|⁻¹ ∑_g λ_g`. -/
theorem reducedAssemblyHom_unitClass :
    Assembly.reducedAssemblyHom Γ false (unitClass Γ) = averagingClass Γ := by
  rw [← characterClass_one, reducedAssemblyHom_characterClass, characterK0Class_one]

/-- The canonical trace of `μ₀(χ ⊗ 1_Γ)` is `1 / |Γ|` for every character `χ`. -/
theorem reducedTraceK0_assembly_characterClass (χ : Γ →* unitary ℂ) :
    reducedTraceK0 Γ (Assembly.reducedAssemblyHom Γ false (characterClass Γ χ)) =
      (Fintype.card Γ : ℝ)⁻¹ := by
  rw [reducedAssemblyHom_characterClass, reducedTraceK0_characterK0Class]

/-- The canonical trace of `μ₀(1_Γ)` is `1 / |Γ|`. -/
theorem reducedTraceK0_assembly_unitClass :
    reducedTraceK0 Γ (Assembly.reducedAssemblyHom Γ false (unitClass Γ)) =
      (Fintype.card Γ : ℝ)⁻¹ := by
  rw [reducedAssemblyHom_unitClass, reducedTraceK0_averagingClass]

/-- For `|Γ| > 1`, `μ₀(1_Γ)` is not an integer multiple of `[1_{C*_r Γ}]`. -/
theorem assembly_unitClass_not_mem_zmultiples (h : 1 < Fintype.card Γ) :
    Assembly.reducedAssemblyHom Γ false (unitClass Γ) ∉
      AddSubgroup.zmultiples (reducedUnitClass Γ) := by
  rw [reducedAssemblyHom_unitClass]
  exact averagingClass_not_mem_zmultiples Γ h

end BC4lean.Chapter8Examples.FiniteAssemblyUnit

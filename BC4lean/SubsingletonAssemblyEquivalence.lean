import BC4lean.UnitAssemblyEquivalence
import BC4lean.SubsingletonScalarDescent
import BC4lean.ScalarIdentityUniverse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The Baum–Connes property for one-element groups

`baumConnesProperty_unit` proves the property for the literal group `Unit`.
This file proves it for every group `Γ : Type u` with exactly one element, in
every universe `u` (so also for `ULift.{u} Unit`), by running the same
argument with `Γ` in place of `Unit`, not by transporting along `Γ ≃* Unit`
(no invariance of `BaumConnesProperty` under isomorphism is used).

Two ingredients of the `Unit` proof are stated only in universe `0`: the
constant-function and evaluation maps of `UnitPointCutoff` (`X : Type`),
restated here for `X : Type u`, and the scalar index of the identity class,
generalized in `ScalarIdentityUniverse`
(`ScalarUnitProjection.scalarKKOperatorK0AddEquiv_identity_universe`).

The steps are those of the `Unit` proof:
* the canonical model is replaced by the one-point model
  (`finiteTopologicalPointSpaceEquiv`, valid for finite groups);
* on the point the cutoff projection is the scalar coefficient `1`, so the
  cutoff product is the source pullback along `ℂ → C₀(X) ⋊ᵣ Γ`;
* descent followed by this pullback is the ordinary coefficient extension of
  the restriction of the class to `Unit` (`SubsingletonScalarDescent`);
* restriction `KK^Γ → KK` is invertible for a one-element group
  (`GroupRestriction.subsingletonParityEquiv`), and the scalar index maps
  identify ordinary `KK_p(ℂ, ℂ)` with `K_p(C*_r Γ)` through
  `trivialReducedEquiv`.

Composing these gives an explicit additive equivalence equal to the
canonical assembly map in each parity. `Countable Γ`, required by
`BaumConnesProperty`, is inferred from `Subsingleton Γ` through `Finite Γ`.
-/

noncomputable section
universe u uG uA uB uC w
namespace BC4lean.Chapter8Examples.SubsingletonAssembly
open ProperActions KKTheory OperatorKTheory
open KKTheory.GroupUniverseParityGroup KKTheory.GroupUniverseParityFunctoriality
open KKTheory.GroupRestriction KKTheory.SubsingletonScalarDescent
open scoped ZeroAtInfty ComplexOrder KasparovDescent

section CompactCoefficients
variable (X : Type u) [TopologicalSpace X] [CompactSpace X]

/-- Constant functions on a compact space. This is
`UnitPointCutoff.scalarToCZero`, which is stated for `X : Type`, in every universe. -/
def scalarToCZero : ℂ →⋆ₙₐ[ℂ] C₀(X, ℂ) where
  toFun z := ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty (ContinuousMap.const X z)
  map_zero' := by ext x; rfl
  map_add' _ _ := by ext x; rfl
  map_mul' _ _ := by ext x; rfl
  map_smul' _ _ := by ext x; rfl
  map_star' _ := by ext x; rfl

@[simp] theorem scalarToCZero_apply (z : ℂ) (x : X) : scalarToCZero X z x = z := rfl

end CompactCoefficients

/-- Evaluation at a point. This is `UnitPointCutoff.cZeroEvaluation` in every universe. -/
def cZeroEvaluation (X : Type u) [TopologicalSpace X] (x : X) : C₀(X, ℂ) →⋆ₙₐ[ℂ] ℂ where
  toFun f := f x
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

/-- Equal equivariant source maps give equal source pullbacks, whatever the
proofs of equivariance. This is `UnitAssemblyEquivalence`'s private
`unitSourcePullback_congr` for an arbitrary countable group and universes. -/
theorem sourcePullback_congr {G : Type uG} [Group G] [Countable G]
    {A : Type uA} {B : Type uB} {C : Type uC} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
    [TopologicalSpace.SeparableSpace C]
    {α : CStarAlgebraAction G A} {β : CStarAlgebraAction G B}
    {γ : CStarAlgebraAction G C}
    (p : Bool) (f g : A →⋆ₙₐ[ℂ] B)
    (hf : ∀ k a, f (α.automorphism k a) = β.automorphism k (f a))
    (hg : ∀ k a, g (α.automorphism k a) = β.automorphism k (g a))
    (h : f = g) (x : KKParityGroup.{uG,uB,uC,max w (max uA (max uB uC))} p β γ) :
    sourcePullback.{uG,uA,uB,uC,w} p f hf x = sourcePullback.{uG,uA,uB,uC,w} p g hg x := by
  cases h
  rfl

variable (Γ : Type u) [Group Γ] [Subsingleton Γ]

section Analytic

abbrev reducedAlgebra := ReducedGroupCStar Γ
local instance reducedOrder : PartialOrder (reducedAlgebra Γ) := CStarAlgebra.spectralOrder _
local instance reducedStarOrder : StarOrderedRing (reducedAlgebra Γ) :=
  CStarAlgebra.spectralOrderedRing _

/-- Ordinary `KK_p(ℂ, ℂ)` is `K_p(C*_r Γ)`: the scalar index comparison, unital
agreement, and the scalar identification `ℂ ≃ C*_r Γ` of a one-element group. -/
def analyticEquiv (p : Bool) :
    KKParityGroup.{0,0,0,u} p unitScalarAction unitScalarAction ≃+ Assembly.analyticGroup Γ p := by
  cases p
  · exact (scalarKKOperatorK0AddEquiv.{0,u}).trans
      ((operatorK0UnitalEquiv ℂ).trans (@k0Equiv ℂ (reducedAlgebra Γ) inferInstance inferInstance
        (CStarAlgebra.spectralOrder ℂ) (CStarAlgebra.spectralOrderedRing ℂ)
        (reducedOrder Γ) (reducedStarOrder Γ) (trivialReducedEquiv (Γ := Γ))))
  · exact (oddKKOperatorK1AllModuleUniversesAddEquiv.{0,u}).trans
      ((operatorK1UnitalEquiv ℂ).trans (@k1Equiv ℂ (reducedAlgebra Γ) inferInstance inferInstance
        (CStarAlgebra.spectralOrder ℂ) (CStarAlgebra.spectralOrderedRing ℂ)
        (reducedOrder Γ) (reducedStarOrder Γ) (trivialReducedEquiv (Γ := Γ))))

/-- The scalar crossed-product equivalence restricted to scalar coefficients is
the scalar identification `ℂ ≃ C*_r Γ`. -/
theorem scalarCrossedCoefficient_comp_eq :
    (reducedCrossedScalarProductEquiv (Γ := Γ)).toNonUnitalStarAlgHom.comp (scalarInclusion Γ) =
      (trivialReducedEquiv (Γ := Γ)).toNonUnitalStarAlgHom := by
  apply DFunLike.ext
  intro z
  change reducedCrossedScalarProductEquiv (scalarInclusion Γ z) = trivialReducedEquiv z
  calc
    _ = reducedCrossedScalarProductEquiv (scalarInclusion Γ (z • (1 : ℂ))) := by simp
    _ = z • reducedCrossedScalarProductEquiv (scalarInclusion Γ (1 : ℂ)) := by
      rw [map_smul, map_smul]
    _ = z • (1 : reducedAlgebra Γ) := by rw [reducedCrossedScalarProductEquiv_oneCoefficient]
    _ = trivialReducedEquiv z := by
      rw [trivialReducedEquiv_apply, Algebra.algebraMap_eq_smul_one]

/-- Even half: the analytic comparison of a coefficient-extended class. -/
theorem reducedScalarKKToK0Hom_coefficient
    (x : KasparovHomotopyClass.{0,0,0,u} unitScalarAction unitScalarAction) :
    Assembly.reducedScalarKKToK0Hom Γ
      (GroupUniverseOrdinaryEven.coefficientPushforward (scalarInclusion Γ) x) =
        analyticEquiv Γ false x := by
  change operatorK0UnitalEquiv (reducedAlgebra Γ)
      (operatorK0Map (reducedCrossedScalarProductEquiv (Γ := Γ)).toNonUnitalStarAlgHom
        (scalarKKOperatorK0AddEquiv
          (GroupUniverseOrdinaryEven.coefficientPushforward (scalarInclusion Γ) x))) = _
  rw [scalarKKOperatorK0AddEquiv_natural]
  rw [← AddMonoidHom.comp_apply, ← operatorK0Map_comp, scalarCrossedCoefficient_comp_eq]
  exact operatorK0UnitalEquiv_natural (trivialReducedEquiv (Γ := Γ)).toStarAlgHom
    (scalarKKOperatorK0AddEquiv x)

/-- Odd half: the analytic comparison of a coefficient-extended class. -/
theorem reducedScalarKKToK1Hom_coefficient
    (x : OddKK.{0,0,0,u} unitScalarAction unitScalarAction) :
    Assembly.reducedScalarKKToK1Hom Γ
      (GroupUniverseOrdinaryOdd.coefficientPushforward (scalarInclusion Γ) x) =
        analyticEquiv Γ true x := by
  change operatorK1UnitalEquiv (reducedAlgebra Γ)
      (operatorK1Map (reducedCrossedScalarProductEquiv (Γ := Γ)).toNonUnitalStarAlgHom
        (oddKKOperatorK1AllModuleUniversesAddEquiv
          (GroupUniverseOrdinaryOdd.coefficientPushforward (scalarInclusion Γ) x))) = _
  simp only [oddKKOperatorK1AllModuleUniversesAddEquiv_apply]
  rw [oddKKOperatorK1Index_independentCoefficientPushforward]
  rw [← AddMonoidHom.comp_apply, ← operatorK1Map_comp, scalarCrossedCoefficient_comp_eq]
  change operatorK1UnitalEquiv (reducedAlgebra Γ)
      (operatorK1Map (trivialReducedEquiv (Γ := Γ)).toNonUnitalStarAlgHom
        (oddKKOperatorK1Index x)) =
    (@k1Equiv ℂ (reducedAlgebra Γ) inferInstance inferInstance
      (CStarAlgebra.spectralOrder ℂ) (CStarAlgebra.spectralOrderedRing ℂ)
      (reducedOrder Γ) (reducedStarOrder Γ) (trivialReducedEquiv (Γ := Γ)))
        (operatorK1UnitalEquiv ℂ (oddKKOperatorK1AllModuleUniversesAddEquiv x))
  rw [oddKKOperatorK1AllModuleUniversesAddEquiv_apply]
  exact operatorK1UnitalEquiv_natural (trivialReducedEquiv (Γ := Γ)).toStarAlgHom
    (oddKKOperatorK1Index x)

end Analytic

variable [TopologicalSpace Γ] [DiscreteTopology Γ]

section CompactPoint
variable (X : Type u) [TopologicalSpace X] [MulAction Γ X]
  [ContinuousConstSMul Γ X] [CompactSpace X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [ProperSMul Γ X]

local instance cZeroSeparable : TopologicalSpace.SeparableSpace C₀(X, ℂ) :=
  TopologicalKHomology.cZero_separableSpace

/-- The scalar map into the crossed source algebra. -/
def scalarCrossedCoefficient : ℂ →⋆ₙₐ[ℂ] ReducedCrossedProduct (CZero.action Γ (X := X)) :=
  (coefficientToReducedCrossed (CZero.action Γ)).comp (scalarToCZero X)

omit [TopologicalSpace Γ] [DiscreteTopology Γ] [ContinuousConstSMul Γ X] [CompactSpace X]
  [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X] [ProperSMul Γ X] in
/-- For a one-element group, normalization of a cutoff says `c(x)² = 1`. -/
theorem cutoff_square_one (c : Cutoff.CutoffFunction Γ X) (x : X) : c x ^ 2 = 1 := by
  let : Unique Γ := uniqueOfSubsingleton 1
  change c.toFun x ^ 2 = 1
  have hd : (default : Γ) = 1 := Subsingleton.elim _ _
  simpa only [finsum_unique, hd, inv_one, one_smul] using c.normalized x

omit [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X] in
/-- The algebraic cutoff projection has only its identity coefficient, the
constant function one. -/
theorem algebraicProjection_eq_single (c : Cutoff.CutoffFunction Γ X) :
    Cutoff.algebraicProjection c =
      AlgebraicCrossedProduct.single (CZero.action Γ) 1 (scalarToCZero X 1) := by
  apply AlgebraicCrossedProduct.ext
  intro g
  have hg : g = 1 := Subsingleton.elim _ _
  subst g
  apply ZeroAtInftyContinuousMap.ext
  intro x
  simp only [Cutoff.algebraicProjection, Cutoff.coeff_mixedAlgebraic,
    Cutoff.mixedCZeroCoefficient_apply, AlgebraicCrossedProduct.coeff_single,
    Finsupp.single_eq_same, scalarToCZero_apply, inv_one, one_smul]
  exact (congrArg Complex.ofReal (by
    simpa only [pow_two] using cutoff_square_one Γ X c x) : _)

omit [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X] in
/-- The completed cutoff projection is `f(1)` for the scalar coefficient map `f`. -/
theorem reducedCutoffProjection_eq_scalarCoefficient (c : Cutoff.CutoffFunction Γ X) :
    Cutoff.reducedCutoffProjection c = scalarCrossedCoefficient Γ X 1 := by
  unfold Cutoff.reducedCutoffProjection
  rw [algebraicProjection_eq_single Γ X]
  apply Subtype.ext
  rw [algebraicToReducedCrossed_single]
  change reducedCrossedCoefficient (CZero.action Γ) (scalarToCZero X 1) *
      reducedCrossedRegular (1 : Γ) =
    reducedCrossedCoefficient (CZero.action Γ) (scalarToCZero X 1)
  rw [reducedCrossedRegular_one, mul_one]

/-- The cutoff KK class is the class of the scalar coefficient homomorphism.
The argument is that of `UnitPointCutoff.cutoffKKClass_eq_homClass`. -/
theorem cutoffKKClass_eq_homClass (c : Cutoff.CutoffFunction Γ X) :
    Assembly.cutoffKKClass Γ X c =
      GroupUniverseParityHomCycle.homClass.{0,0,u,u}
        (scalarCrossedCoefficient Γ X) (fun _ _ => rfl) := by
  let α : CStarAlgebraAction Unit ℂ := CStarAlgebraAction.trivial
  let f := scalarCrossedCoefficient Γ X
  let e := GroupUniverseParityUnits.identity.{0,0,u} α
  let δ : CStarAlgebraAction Unit
      (ReducedCrossedProduct (CZero.action Γ (X := X))) := CStarAlgebraAction.trivial
  have hproduct : GroupUniverseParityFunctoriality.coefficientPushforward.{0,0,0,u,u}
      (Γ := Unit) (A := ℂ) (B := ℂ)
      (C := ReducedCrossedProduct (CZero.action Γ (X := X)))
      («α» := α) («β» := α) (γ := δ) false f (fun _ _ => rfl) e =
      GroupUniverseParityHomCycle.homClass.{0,0,u,u}
        (Γ := Unit) (A := ℂ) (B := ReducedCrossedProduct (CZero.action Γ (X := X)))
        («α» := α) («β» := δ) f (fun _ _ => rfl) := by
    change GroupUniverseParityUnits.leftEvenProduct false e
      (GroupUniverseParityHomCycle.homClass.{0,0,u,u}
        (Γ := Unit) (A := ℂ) (B := ReducedCrossedProduct (CZero.action Γ (X := X)))
        («α» := α) («β» := δ) f (fun _ _ => rfl)) = _
    exact GroupUniverseParityUnits.left_identity false _
  have hn := Assembly.scalarKKOperatorK0_native_coefficient_natural.{0,u,u} f e
  rw [hproduct, ScalarUnitProjection.scalarKKOperatorK0AddEquiv_identity_universe] at hn
  rw [nonunitalProjectionK0_map] at hn
  apply (scalarKKOperatorK0AddEquiv.{u,u}
    (B := ReducedCrossedProduct (CZero.action Γ (X := X)))).injective
  change scalarKKOperatorK0AddEquiv
      (scalarKKOperatorK0AddEquiv.symm (Cutoff.cutoffK0 c)) = scalarKKOperatorK0AddEquiv _
  rw [AddEquiv.apply_symm_apply, hn]
  unfold Cutoff.cutoffK0
  have hclass : ∀ (p q : ReducedCrossedProduct (CZero.action Γ (X := X)))
      (hp : IsStarProjection p) (hq : IsStarProjection q),
      p = q → nonunitalProjectionK0 p hp = nonunitalProjectionK0 q hq := by
    intro p q hp hq heq
    cases heq
    rfl
  exact hclass _ _ _ _ (reducedCutoffProjection_eq_scalarCoefficient Γ X c)

omit [Subsingleton Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [LocallyCompactSpace X]
  [T2Space X] [SecondCountableTopology X] [ProperSMul Γ X] in
/-- Constant functions are equivariant for any action on `X`. -/
theorem scalarToCZero_equivariant : ∀ (g : Γ) (z : ℂ),
    scalarToCZero X ((scalarAction Γ).automorphism g z) =
      (CZero.action Γ (X := X)).automorphism g (scalarToCZero X z) := by
  intro g z
  apply ZeroAtInftyContinuousMap.ext
  intro x
  rfl

omit [TopologicalSpace Γ] [DiscreteTopology Γ] [CompactSpace X] [LocallyCompactSpace X]
  [T2Space X] [SecondCountableTopology X] [ProperSMul Γ X] in
/-- Evaluation at a point is equivariant because the group has one element. -/
theorem cZeroEvaluation_equivariant (x : X) : ∀ (g : Γ) (f : C₀(X, ℂ)),
    cZeroEvaluation X x ((CZero.action Γ (X := X)).automorphism g f) =
      (scalarAction Γ).automorphism g (cZeroEvaluation X x f) := by
  intro g f
  have hg : g = 1 := Subsingleton.elim _ _
  subst g
  rw [CStarAlgebraAction.one_apply, CStarAlgebraAction.one_apply]

/-- On a one-point space, source pullback along the constant-function map is
an additive equivalence `K^Γ_p(X) ≃ KK^Γ_p(ℂ, ℂ)`, with inverse the pullback
along evaluation. -/
def pointSourceEquiv [Subsingleton X] (x : X) (p : Bool) :
    TopologicalKHomology.spaceGroup p Γ X ≃+
      KKParityGroup.{u,0,0,u} p (scalarAction Γ) (scalarAction Γ) where
  toFun := sourcePullbackHom.{u,0,u,0,0} p (scalarToCZero X) (scalarToCZero_equivariant Γ X)
  invFun := sourcePullbackHom.{u,u,0,0,0} p (cZeroEvaluation X x)
    (cZeroEvaluation_equivariant Γ X x)
  left_inv z := by
    change sourcePullback p (cZeroEvaluation X x) (cZeroEvaluation_equivariant Γ X x)
      (sourcePullback p (scalarToCZero X) (scalarToCZero_equivariant Γ X) z) = z
    rw [sourcePullback_comp]
    have h : (scalarToCZero X).comp (cZeroEvaluation X x) =
        NonUnitalStarAlgHom.id ℂ C₀(X, ℂ) := by
      ext f y
      exact congrArg f (Subsingleton.elim x y)
    exact (sourcePullback_congr («α» := CZero.action Γ (X := X))
      («β» := CZero.action Γ (X := X)) (γ := scalarAction Γ)
      p _ _ _ (fun _ _ => rfl) h z).trans (sourcePullback_id p z)
  right_inv z := by
    change sourcePullback p (scalarToCZero X) (scalarToCZero_equivariant Γ X)
      (sourcePullback p (cZeroEvaluation X x) (cZeroEvaluation_equivariant Γ X x) z) = z
    rw [sourcePullback_comp]
    have h : (cZeroEvaluation X x).comp (scalarToCZero X) =
        NonUnitalStarAlgHom.id ℂ ℂ := by ext a; rfl
    exact (sourcePullback_congr («α» := scalarAction Γ)
      («β» := scalarAction Γ) (γ := scalarAction Γ)
      p _ _ _ (fun _ _ => rfl) h z).trans (sourcePullback_id p z)
  map_add' := (sourcePullbackHom p (scalarToCZero X) (scalarToCZero_equivariant Γ X)).map_add

abbrev pointCrossedAction : CStarAlgebraAction Unit
    (ReducedCrossedProduct (CZero.action Γ (X := X))) := CStarAlgebraAction.trivial

abbrev pointCrossedMap : ReducedCrossedProduct (scalarAction Γ) →⋆ₙₐ[ℂ]
    ReducedCrossedProduct (CZero.action Γ (X := X)) :=
  reducedCrossedMap (scalarAction Γ) (CZero.action Γ (X := X))
    (scalarToCZero X) (scalarToCZero_equivariant Γ X)

/-- The cutoff product is the source pullback along the scalar coefficient map. -/
theorem cutoffProduct_eq_source (p : Bool) (c : Cutoff.CutoffFunction Γ X)
    (y : KKParityGroup.{0,u,u,u} p (pointCrossedAction Γ X) (descendedScalarAction Γ)) :
    Assembly.cutoffProductHom Γ X p c y =
      sourcePullback.{0,0,u,u,0} (Γ := Unit) (A := ℂ)
        (B := ReducedCrossedProduct (CZero.action Γ (X := X)))
        (C := ReducedCrossedProduct (scalarAction Γ)) («α» := unitScalarAction)
        («β» := pointCrossedAction Γ X) (γ := descendedScalarAction Γ)
        p (scalarCrossedCoefficient Γ X) (fun _ _ => rfl) y := by
  cases p
  · change GroupUniverseParityUnits.leftEvenProduct.{0,0,u,u,u}
      (Γ := Unit) (A := ℂ) (B := ReducedCrossedProduct (CZero.action Γ (X := X)))
      (C := ReducedCrossedProduct (scalarAction Γ)) («α» := unitScalarAction)
      («β» := pointCrossedAction Γ X) (γ := descendedScalarAction Γ)
      false (Assembly.cutoffKKClass Γ X c) y = _
    rw [cutoffKKClass_eq_homClass Γ X c]
    rfl
  · change GroupUniverseParityUnits.leftEvenProduct.{0,0,u,u,u}
      (Γ := Unit) (A := ℂ) (B := ReducedCrossedProduct (CZero.action Γ (X := X)))
      (C := ReducedCrossedProduct (scalarAction Γ)) («α» := unitScalarAction)
      («β» := pointCrossedAction Γ X) (γ := descendedScalarAction Γ)
      true (Assembly.cutoffKKClass Γ X c) y = _
    rw [cutoffKKClass_eq_homClass Γ X c]
    rfl

omit [Subsingleton Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [LocallyCompactSpace X]
  [T2Space X] [SecondCountableTopology X] [ProperSMul Γ X] in
/-- Crossed-product functoriality identifies the two scalar coefficient maps. -/
theorem pointCrossedMap_coefficient :
    (pointCrossedMap Γ X).comp (scalarInclusion Γ) = scalarCrossedCoefficient Γ X := by
  apply DFunLike.ext
  intro a
  exact reducedCrossedMap_coefficient (scalarAction Γ) (CZero.action Γ (X := X))
    (scalarToCZero X) (scalarToCZero_equivariant Γ X) a

omit [TopologicalSpace Γ] [DiscreteTopology Γ] [ProperSMul Γ X] in
/-- Source naturality of descent moves the constant-function map before descent. -/
theorem cutoffSource_descent (p : Bool) (x : TopologicalKHomology.spaceGroup p Γ X) :
    sourcePullback.{0,0,u,u,0} (Γ := Unit) (A := ℂ)
      (B := ReducedCrossedProduct (CZero.action Γ (X := X)))
      (C := ReducedCrossedProduct (scalarAction Γ)) («α» := unitScalarAction)
      («β» := pointCrossedAction Γ X) (γ := descendedScalarAction Γ)
      p (scalarCrossedCoefficient Γ X) (fun _ _ => rfl)
      (KasparovDescent.classHom (scalarAction Γ) (CZero.action Γ (X := X)) p x) =
    sourcePullback.{0,0,u,u,0} (Γ := Unit) (A := ℂ)
      (B := ReducedCrossedProduct (scalarAction Γ)) (C := ReducedCrossedProduct (scalarAction Γ))
      («α» := unitScalarAction) («β» := descendedScalarAction Γ)
      (γ := descendedScalarAction Γ) p (scalarInclusion Γ) (fun _ _ => rfl)
      (KasparovDescent.classHom (scalarAction Γ) (scalarAction Γ) p
        (sourcePullback.{u,0,u,0,0} p (scalarToCZero X) (scalarToCZero_equivariant Γ X) x)) := by
  have hn := KasparovDescent.classHom_sourcePullback.{u,u,0,0,0}
    (scalarAction Γ) (CZero.action Γ (X := X)) (scalarAction Γ) p (scalarToCZero X)
      (scalarToCZero_equivariant Γ X) x
  have hc := sourcePullback_comp.{0,0,u,u,u,0}
    (Γ := Unit) (A := ℂ) (B := ReducedCrossedProduct (scalarAction Γ))
    (C := ReducedCrossedProduct (CZero.action Γ (X := X)))
    (D := ReducedCrossedProduct (scalarAction Γ)) («α» := unitScalarAction)
    («β» := descendedScalarAction Γ) (γ := pointCrossedAction Γ X)
    (η := descendedScalarAction Γ) p (scalarInclusion Γ) (pointCrossedMap Γ X)
    (fun _ _ => rfl) (fun _ _ => rfl)
    (KasparovDescent.classHom (scalarAction Γ) (CZero.action Γ (X := X)) p x)
  have he := sourcePullback_congr («α» := unitScalarAction)
    («β» := pointCrossedAction Γ X) (γ := descendedScalarAction Γ) p
    ((pointCrossedMap Γ X).comp (scalarInclusion Γ)) (scalarCrossedCoefficient Γ X)
    (fun _ _ => rfl) (fun _ _ => rfl) (pointCrossedMap_coefficient Γ X)
    (KasparovDescent.classHom (scalarAction Γ) (CZero.action Γ (X := X)) p x)
  exact (hc.trans he).symm.trans (congrArg
    (sourcePullback.{0,0,u,u,0} (Γ := Unit) (A := ℂ)
      (B := ReducedCrossedProduct (scalarAction Γ)) (C := ReducedCrossedProduct (scalarAction Γ))
      («α» := unitScalarAction) («β» := descendedScalarAction Γ)
      (γ := descendedScalarAction Γ) p (scalarInclusion Γ) (fun _ _ => rfl)) hn.symm)

/-- The cutoff product of the descended class is the ordinary coefficient
extension of the restriction to `Unit` of the pulled-back class. -/
theorem cutoffProduct_descent_eq_coefficient (p : Bool) (c : Cutoff.CutoffFunction Γ X)
    (x : TopologicalKHomology.spaceGroup p Γ X) :
    Assembly.cutoffProductHom Γ X p c
      (KasparovDescent.classHom (scalarAction Γ) (CZero.action Γ (X := X)) p x) =
    (by
      cases p
      · exact GroupUniverseOrdinaryEven.coefficientPushforward.{0,u,u} (scalarInclusion Γ)
          (evenComap (fromUnitHom (Γ := Γ))
            (sourcePullback.{u,0,u,0,0} false (scalarToCZero X) (scalarToCZero_equivariant Γ X) x))
      · exact GroupUniverseOrdinaryOdd.coefficientPushforward.{0,u,u} (scalarInclusion Γ)
          (oddComap (fromUnitHom (Γ := Γ))
            (sourcePullback.{u,0,u,0,0} true (scalarToCZero X) (scalarToCZero_equivariant Γ X) x)) :
      KKParityGroup.{0,0,u,u} p unitScalarAction (descendedScalarAction Γ)) := by
  have h := (cutoffProduct_eq_source Γ X p c
    (KasparovDescent.classHom (scalarAction Γ) (CZero.action Γ (X := X)) p x)).trans
      (cutoffSource_descent Γ X p x)
  cases p
  · exact h.trans (evenClass_coefficientRestriction Γ _)
  · exact h.trans (oddClass_coefficientRestriction Γ _)

/-- On a one-point space the assembly map is the composite of the point source
equivalence, restriction to `Unit`, and the analytic comparison. -/
theorem spaceAssemblyHom_eq_pointEquiv [Subsingleton X] (x0 : X) (p : Bool)
    (c : Cutoff.CutoffFunction Γ X) (x : TopologicalKHomology.spaceGroup p Γ X) :
    Assembly.spaceAssemblyHom Γ X p c x =
      ((pointSourceEquiv Γ X x0 p).trans
        ((subsingletonParityEquiv p).trans (analyticEquiv Γ p))) x := by
  change Assembly.reducedScalarKKToAnalyticHom Γ p
    (Assembly.cutoffProductHom Γ X p c
      (KasparovDescent.classHom (scalarAction Γ) (CZero.action Γ (X := X)) p x)) = _
  rw [cutoffProduct_descent_eq_coefficient Γ X]
  cases p
  · exact reducedScalarKKToK0Hom_coefficient Γ _
  · exact reducedScalarKKToK1Hom_coefficient Γ _

end CompactPoint

/-- An additive equivalence from the canonical topological group, through the
one-point model, restriction to `Unit` and the analytic comparison. -/
def assemblyAddEquiv (p : Bool) :
    TopologicalKHomology.topologicalGroup p Γ ≃+ Assembly.analyticGroup Γ p :=
  (finiteTopologicalPointSpaceEquiv Γ p).trans
    ((pointSourceEquiv Γ FiniteGroupPoint.{u} default p).trans
      ((subsingletonParityEquiv p).trans (analyticEquiv Γ p)))

/-- The canonical assembly map of a one-element group is `assemblyAddEquiv`. -/
theorem reducedAssemblyHom_eq (p : Bool) (x : TopologicalKHomology.topologicalGroup p Γ) :
    Assembly.reducedAssemblyHom Γ p x = assemblyAddEquiv Γ p x := by
  rw [reducedAssemblyHom_finitePoint]
  exact spaceAssemblyHom_eq_pointEquiv Γ FiniteGroupPoint.{u} default p
    (finitePointCutoff Γ) (finiteTopologicalPointSpaceEquiv Γ p x)

/-- The coefficient-free reduced Baum–Connes property holds for every discrete
group `Γ : Type u` with exactly one element, in every universe `u`. -/
theorem baumConnesProperty_of_subsingleton : Assembly.BaumConnesProperty Γ := by
  intro p
  have h : (Assembly.reducedAssemblyHom Γ p :
      TopologicalKHomology.topologicalGroup p Γ → Assembly.analyticGroup Γ p) =
      assemblyAddEquiv Γ p := funext (reducedAssemblyHom_eq Γ p)
  rw [h]
  exact (assemblyAddEquiv Γ p).bijective

end BC4lean.Chapter8Examples.SubsingletonAssembly

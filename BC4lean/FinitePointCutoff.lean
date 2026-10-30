import BC4lean.UnitPointCutoff
import BC4lean.FiniteGroupPointCalibration

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! Cutoff projections and cutoff classes for finite groups on the point.

For a proper action with a normalized cutoff `c`, the cutoff class is the class
of any scalar homomorphism sending `1` to `p_c`, such as `z ↦ z • p_c`, and the
cutoff product is the source pullback along it. For a finite group on the one-point model every normalized cutoff
takes the value `|Γ|^(-1/2)`, so the cutoff projection is the averaging
element `|Γ|⁻¹ ∑_g δ_g` of the reduced crossed product. -/

noncomputable section
namespace BC4lean.KKTheory.FinitePointCutoff
open BC4lean.ProperActions BC4lean.OperatorKTheory BC4lean.Chapter8Examples
open KKTheory.GroupUniverseParityGroup KKTheory.GroupUniverseParityFunctoriality
open scoped ZeroAtInfty ComplexOrder KasparovDescent

section Projection
variable {B : Type*} [NonUnitalCStarAlgebra B]

/-- The scalar homomorphism `z ↦ z • p` of a star projection `p`. -/
def projectionScalarHom (p : B) (hp : IsStarProjection p) : ℂ →⋆ₙₐ[ℂ] B where
  toFun z := z • p
  map_zero' := zero_smul ℂ p
  map_add' z w := add_smul z w p
  map_smul' z w := mul_smul z w p
  map_mul' z w := by
    change (z * w) • p = (z • p) * (w • p)
    rw [smul_mul_smul_comm, hp.isIdempotentElem.eq]
  map_star' z := by
    rw [star_smul, hp.isSelfAdjoint.star_eq]

@[simp] theorem projectionScalarHom_apply (p : B) (hp : IsStarProjection p) (z : ℂ) :
    projectionScalarHom p hp z = z • p := rfl

theorem projectionScalarHom_one (p : B) (hp : IsStarProjection p) :
    projectionScalarHom p hp 1 = p := one_smul ℂ p

end Projection

section CutoffClass
variable (Γ : Type) [Group Γ] [Countable Γ]
  [TopologicalSpace Γ] [DiscreteTopology Γ]
  (X : Type) [TopologicalSpace X] [MulAction Γ X]
  [ContinuousConstSMul Γ X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [ProperSMul Γ X]

local instance cZero_separable : TopologicalSpace.SeparableSpace C₀(X, ℂ) :=
  TopologicalKHomology.cZero_separableSpace

/-- The actual cutoff KK class is the scalar homomorphism class of any
homomorphism sending one to the cutoff projection. This is the argument of
`UnitPointCutoff.cutoffKKClass_eq_homClass`, which nowhere uses the group.
For example `f = projectionScalarHom _ (Cutoff.reducedCutoffProjection_isStarProjection c)`,
by `projectionScalarHom_one`. Like that lemma, it is stated for `Γ X : Type`, whereas
`Assembly.cutoffKKClass` is universe polymorphic. -/
theorem cutoffKKClass_eq_homClass (c : Cutoff.CutoffFunction Γ X)
    (f : ℂ →⋆ₙₐ[ℂ] ReducedCrossedProduct (CZero.action Γ (X := X)))
    (hf : f 1 = Cutoff.reducedCutoffProjection c) :
    Assembly.cutoffKKClass Γ X c =
      GroupUniverseParityHomCycle.homClass.{0,0,0,0}
        (Γ := Unit) (A := ℂ) (B := ReducedCrossedProduct (CZero.action Γ (X := X)))
        («α» := CStarAlgebraAction.trivial) («β» := CStarAlgebraAction.trivial)
        f (fun _ _ => rfl) := by
  let α : CStarAlgebraAction Unit ℂ := CStarAlgebraAction.trivial
  let e := GroupUniverseParityUnits.identity.{0,0,0} α
  let δ : CStarAlgebraAction Unit
      (ReducedCrossedProduct (CZero.action Γ (X := X))) := CStarAlgebraAction.trivial
  have hproduct : GroupUniverseParityFunctoriality.coefficientPushforward.{0,0,0,0,0}
      (Γ := Unit) (A := ℂ) (B := ℂ)
      (C := ReducedCrossedProduct (CZero.action Γ (X := X)))
      («α» := α) («β» := α) (γ := δ) false f (fun _ _ => rfl) e =
      GroupUniverseParityHomCycle.homClass.{0,0,0,0}
        (Γ := Unit) (A := ℂ) (B := ReducedCrossedProduct (CZero.action Γ (X := X)))
        («α» := α) («β» := δ) f (fun _ _ => rfl) := by
    change GroupUniverseParityUnits.leftEvenProduct false e
      (GroupUniverseParityHomCycle.homClass.{0,0,0,0}
        (Γ := Unit) (A := ℂ) (B := ReducedCrossedProduct (CZero.action Γ (X := X)))
        («α» := α) («β» := δ) f (fun _ _ => rfl)) = _
    exact GroupUniverseParityUnits.left_identity false _
  have hn := Assembly.scalarKKOperatorK0_native_coefficient_natural.{0,0,0} f e
  rw [hproduct, ScalarUnitProjection.scalarKKOperatorK0AddEquiv_identity] at hn
  rw [nonunitalProjectionK0_map] at hn
  apply (scalarKKOperatorK0AddEquiv.{0,0}
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
  exact hclass _ _ _ _ hf.symm

/-- The cutoff product, in either parity, is the actual source pullback along
the scalar homomorphism of the cutoff projection. -/
theorem cutoffProductHom_eq_sourcePullback (p : Bool) (c : Cutoff.CutoffFunction Γ X)
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
        («γ» := CStarAlgebraAction.trivial) p f (fun _ _ => rfl) y := by
  cases p
  · change GroupUniverseParityUnits.leftEvenProduct false (Assembly.cutoffKKClass Γ X c) y = _
    rw [cutoffKKClass_eq_homClass Γ X c f hf]
    rfl
  · change GroupUniverseParityUnits.leftEvenProduct true (Assembly.cutoffKKClass Γ X c) y = _
    rw [cutoffKKClass_eq_homClass Γ X c f hf]
    rfl

end CutoffClass

section FinitePoint
variable (Γ : Type) [Group Γ] [Finite Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]

local instance pointCZero_separable :
    TopologicalSpace.SeparableSpace C₀(FiniteGroupPoint.{0}, ℂ) :=
  TopologicalKHomology.cZero_separableSpace

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- On the point, normalization says `|Γ| c(x)² = 1`. -/
theorem cutoff_sq (c : Cutoff.CutoffFunction Γ FiniteGroupPoint.{0}) (x : FiniteGroupPoint.{0}) :
    c x ^ 2 = (Nat.card Γ : ℝ)⁻¹ := by
  let := Fintype.ofFinite Γ
  have hn : ∑ᶠ _ : Γ, c x ^ 2 = 1 := c.normalized x
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card] at hn
  exact eq_inv_of_mul_eq_one_right hn

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- Every normalized cutoff on the point is the constant `|Γ|^(-1/2)`. -/
theorem cutoff_apply (c : Cutoff.CutoffFunction Γ FiniteGroupPoint.{0}) (x : FiniteGroupPoint.{0}) :
    c x = (Real.sqrt (Nat.card Γ))⁻¹ := by
  have h0 : 0 ≤ c x := c.nonneg x
  rw [← Real.sqrt_inv, ← cutoff_sq Γ c x, Real.sqrt_sq h0]

/-- The algebraic averaging element: every coefficient is the constant `|Γ|⁻¹`. -/
def algebraicAveraging : AlgebraicCrossedProduct (CZero.action Γ (X := FiniteGroupPoint.{0})) :=
  AlgebraicCrossedProduct.ofCoeff _ (Finsupp.ofSupportFinite
    (fun _ => UnitPointCutoff.scalarToCZero FiniteGroupPoint.{0} ((Nat.card Γ : ℂ)⁻¹))
    (Set.toFinite _))

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
@[simp] theorem coeff_algebraicAveraging (g : Γ) :
    AlgebraicCrossedProduct.coeff _ (algebraicAveraging Γ) g =
      UnitPointCutoff.scalarToCZero FiniteGroupPoint.{0} ((Nat.card Γ : ℂ)⁻¹) := rfl

/-- The algebraic cutoff projection on the point is the averaging element,
whichever normalized cutoff is used. -/
theorem algebraicProjection_eq_averaging (c : Cutoff.CutoffFunction Γ FiniteGroupPoint.{0}) :
    Cutoff.algebraicProjection c = algebraicAveraging Γ := by
  apply AlgebraicCrossedProduct.ext
  intro g
  apply ZeroAtInftyContinuousMap.ext
  intro x
  rw [coeff_algebraicAveraging, UnitPointCutoff.scalarToCZero_apply]
  change ((c x * c x : ℝ) : ℂ) = _
  rw [← pow_two, cutoff_sq]
  push_cast
  rfl

/-- The averaging element of the reduced crossed product of the point. -/
def averaging : ReducedCrossedProduct (CZero.action Γ (X := FiniteGroupPoint.{0})) :=
  algebraicToReducedCrossed _ (algebraicAveraging Γ)

/-- The concrete reduced cutoff projection on the point is the averaging element. -/
theorem reducedCutoffProjection_eq_averaging (c : Cutoff.CutoffFunction Γ FiniteGroupPoint.{0}) :
    Cutoff.reducedCutoffProjection c = averaging Γ := by
  unfold Cutoff.reducedCutoffProjection
  rw [algebraicProjection_eq_averaging]
  rfl

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- As an operator, the averaging element is `∑_g π(|Γ|⁻¹) λ_g`. -/
theorem averaging_coe [Fintype Γ] :
    (averaging Γ : AdjointableMap C₀(FiniteGroupPoint.{0}, ℂ)
        (ReducedCrossedHilbertModule C₀(FiniteGroupPoint.{0}, ℂ) Γ)
        (ReducedCrossedHilbertModule C₀(FiniteGroupPoint.{0}, ℂ) Γ)) =
      ∑ g : Γ, reducedCrossedGenerator (CZero.action Γ)
        (UnitPointCutoff.scalarToCZero FiniteGroupPoint.{0} ((Nat.card Γ : ℂ)⁻¹)) g := by
  have h : algebraicAveraging Γ = ∑ g : Γ, AlgebraicCrossedProduct.single (CZero.action Γ) g
      (UnitPointCutoff.scalarToCZero FiniteGroupPoint.{0} ((Nat.card Γ : ℂ)⁻¹)) := by
    apply AlgebraicCrossedProduct.ext
    intro g
    rw [coeff_algebraicAveraging, AlgebraicCrossedProduct.coeff_sum, Finsupp.finsetSum_apply]
    simp
  unfold averaging
  rw [h, map_sum]
  simp only [AddSubmonoidClass.coe_finsetSum, algebraicToReducedCrossed_single]

theorem averaging_isStarProjection : IsStarProjection (averaging Γ) := by
  rw [← reducedCutoffProjection_eq_averaging Γ (finitePointCutoff Γ)]
  exact Cutoff.reducedCutoffProjection_isStarProjection _

/-- The scalar homomorphism `z ↦ z • e` of the averaging projection `e`. -/
abbrev averagingHom : ℂ →⋆ₙₐ[ℂ] ReducedCrossedProduct (CZero.action Γ (X := FiniteGroupPoint.{0})) :=
  projectionScalarHom (averaging Γ) (averaging_isStarProjection Γ)

theorem averagingHom_one (c : Cutoff.CutoffFunction Γ FiniteGroupPoint.{0}) :
    averagingHom Γ 1 = Cutoff.reducedCutoffProjection c := by
  rw [projectionScalarHom_one, reducedCutoffProjection_eq_averaging]

/-- For a finite group on the point, the cutoff class is the class of the
averaging homomorphism, for every normalized cutoff. -/
theorem cutoffKKClass_eq_averagingHomClass (c : Cutoff.CutoffFunction Γ FiniteGroupPoint.{0}) :
    Assembly.cutoffKKClass Γ FiniteGroupPoint.{0} c =
      GroupUniverseParityHomCycle.homClass.{0,0,0,0}
        («α» := (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ))
        («β» := CStarAlgebraAction.trivial) (averagingHom Γ) (fun _ _ => rfl) :=
  cutoffKKClass_eq_homClass Γ FiniteGroupPoint.{0} c _ (averagingHom_one Γ c)

/-- For a finite group on the point, the cutoff product is the source pullback
along the averaging homomorphism, in either parity. -/
theorem cutoffProductHom_eq_averagingPullback (p : Bool)
    (c : Cutoff.CutoffFunction Γ FiniteGroupPoint.{0})
    (y : KKParityGroup.{0,0,0,0} p
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
        (ReducedCrossedProduct (CZero.action Γ (X := FiniteGroupPoint.{0}))))
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
        (ReducedCrossedProduct (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)))) :
    Assembly.cutoffProductHom Γ FiniteGroupPoint.{0} p c y =
      sourcePullback.{0,0,0,0,0} (Γ := Unit) (A := ℂ)
        («α» := CStarAlgebraAction.trivial) («β» := CStarAlgebraAction.trivial)
        («γ» := CStarAlgebraAction.trivial) p (averagingHom Γ) (fun _ _ => rfl) y :=
  cutoffProductHom_eq_sourcePullback Γ FiniteGroupPoint.{0} p c _ (averagingHom_one Γ c) y

end FinitePoint

end BC4lean.KKTheory.FinitePointCutoff

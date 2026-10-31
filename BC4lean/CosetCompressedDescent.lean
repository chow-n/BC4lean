import BC4lean.CosetAssembly
import BC4lean.FinitePointCompressedDescent
import BC4lean.ScalarHilbertModule
import BC4lean.ScalarUnitProjection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! Compressed descent on the coset space `Γ ⧸ F`.

Let `F` be a finite subgroup of a countable discrete group `Γ` and `P_F = |F|⁻¹ ∑_{f ∈ F} λ_f`,
a projection in `C*_r(Γ)`. Let `c` be an even cycle for `C₀(Γ ⧸ F)` on a Hilbert space `H`
with zero operator and trivial grading, in which `δ_{eF}` acts as the rank-one projection onto a
unit vector `v` fixed by `F`. Then the cutoff projection `p = ∑_{f ∈ F} |F|⁻¹ δ_{eF} δ_f` acts on
the descended module `H ⊗ C*_r(Γ)` as `x ⊗ d ↦ ⟨v, x⟩ v ⊗ P_F d`, and the source pullback of the
descent of `[c]` along `z ↦ z • p` is the coefficient extension of the identity class of
`KK(ℂ, ℂ)` along `z ↦ z • P_F`.

This is `FinitePointCompressedDescent` with the point replaced by `Γ ⧸ F`, the averaging
projection of `Γ` by `P_F`, and the isometry `x ⊗ d ↦ x ⊗ P_χ d` by
`z ⊗ d ↦ z v ⊗ P_F d` from `ℂ ⊗_{P_F} C*_r(Γ)`. -/

noncomputable section
namespace BC4lean.KKTheory.CosetCompressedDescent
open BC4lean.ProperActions BC4lean.OperatorKTheory BC4lean.Chapter8Examples
open KKTheory.GroupUniverseParityGroup KKTheory.GroupUniverseParityFunctoriality
open KKTheory.FinitePointCharacterTensor Chapter8Examples.CosetAssembly
open scoped ZeroAtInfty ComplexOrder KasparovDescent InnerProductSpace ScalarHilbertModule

section Projection
variable (Γ : Type) [Group Γ] (F : Subgroup Γ) [Fintype F]

/-- The subgroup projection `P_F = |F|⁻¹ ∑_{f ∈ F} λ_f`. -/
def subgroupProjection : GroupCrossed Γ :=
  ∑ f : F, (Nat.card F : ℂ)⁻¹ • regular Γ (f : Γ)

/-- Translating the sum over `F` by an element of `F`. -/
theorem sum_regular_mul (f : F) :
    ∑ h : F, regular Γ (f : Γ) * regular Γ (h : Γ) = ∑ h : F, regular Γ (h : Γ) := by
  refine Fintype.sum_equiv (Equiv.mulLeft f) _ _ fun h => ?_
  rw [regular_mul, Equiv.coe_mulLeft, Subgroup.coe_mul]

theorem subgroupProjection_isStarProjection : IsStarProjection (subgroupProjection Γ F) := by
  have hn : (Nat.card F : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  refine isStarProjection_iff'.mpr ⟨?_, ?_⟩
  · unfold subgroupProjection
    rw [Finset.sum_mul_sum]
    have hinner : ∀ f : F, ∑ h : F, ((Nat.card F : ℂ)⁻¹ • regular Γ (f : Γ)) *
        ((Nat.card F : ℂ)⁻¹ • regular Γ (h : Γ)) =
        (Nat.card F : ℂ)⁻¹ • ∑ k : F, (Nat.card F : ℂ)⁻¹ • regular Γ (k : Γ) := by
      intro f
      simp only [smul_mul_smul_comm, ← Finset.smul_sum]
      rw [sum_regular_mul, smul_smul]
    rw [Finset.sum_congr rfl fun f _ => hinner f, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← Nat.card_eq_fintype_card, mul_inv_cancel₀ hn,
      one_smul]
  · unfold subgroupProjection
    rw [star_sum]
    refine Fintype.sum_equiv (Equiv.inv F) _ _ fun f => ?_
    rw [star_smul, star_regular, Equiv.inv_apply, Subgroup.coe_inv, star_inv₀, star_natCast]

/-- The scalar homomorphism `z ↦ z • P_F`. -/
abbrev subgroupHom : ℂ →⋆ₙₐ[ℂ] GroupCrossed Γ :=
  FinitePointCutoff.projectionScalarHom (subgroupProjection Γ F)
    (subgroupProjection_isStarProjection Γ F)

end Projection

section Tensor
variable {Γ : Type} [Group Γ] (F : Subgroup Γ) [Fintype F]
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The coefficient extension `ℂ ⊗_{P_F} C*_r(Γ)` of the standard module of `ℂ`. -/
abbrev SubgroupTensor :=
  InteriorModuleTensor (E := ℂᵐᵒᵖ) (standardCoefficientImageRepresentation (subgroupHom Γ F))

/-- Left multiplication by `P_F` on the standard module. -/
def subgroupLeftMul : (GroupCrossed Γ)ᵐᵒᵖ →ₗ[ℂ] (GroupCrossed Γ)ᵐᵒᵖ where
  toFun d := MulOpposite.op (subgroupProjection Γ F * MulOpposite.unop d)
  map_add' d d' := by simp [mul_add]
  map_smul' z d := by simp [mul_smul_comm]

@[simp] theorem subgroupLeftMul_apply (d : (GroupCrossed Γ)ᵐᵒᵖ) :
    subgroupLeftMul F d = MulOpposite.op (subgroupProjection Γ F * MulOpposite.unop d) := rfl

theorem subgroupLeftMul_idem (d : (GroupCrossed Γ)ᵐᵒᵖ) :
    subgroupLeftMul F (subgroupLeftMul F d) = subgroupLeftMul F d := by
  rw [subgroupLeftMul_apply, subgroupLeftMul_apply, MulOpposite.unop_op, ← mul_assoc,
    (subgroupProjection_isStarProjection Γ F).isIdempotentElem.eq]

/-- Scalar coefficients act on the reduced group algebra by scalar multiplication. -/
theorem coefficientToReducedCrossed_scalar_mul (z : ℂ) (a : GroupCrossed Γ) :
    coefficientToReducedCrossed (scalarAction Γ) z * a = z • a := by
  apply Subtype.ext
  change reducedCrossedCoefficient (scalarAction Γ) z * (a : AdjointableMap ℂ
    (ReducedCrossedHilbertModule ℂ Γ) (ReducedCrossedHilbertModule ℂ Γ)) = z • (a : _)
  rw [reducedCrossedCoefficient_scalar, smul_mul_assoc, one_mul]

/-- Left multiplication by `P_F` intertwines the two scalar actions. -/
theorem subgroupLeftMul_intertwines (z : ℂ) (d : (GroupCrossed Γ)ᵐᵒᵖ) :
    MulOpposite.op (coefficientToReducedCrossed (scalarAction Γ) z *
        MulOpposite.unop (subgroupLeftMul F d)) =
      subgroupLeftMul F (standardCoefficientImageRepresentation (subgroupHom Γ F) z d) := by
  apply MulOpposite.unop_injective
  have h : MulOpposite.unop (standardCoefficientImageRepresentation (subgroupHom Γ F) z d) =
      (z • subgroupProjection Γ F) * MulOpposite.unop d := rfl
  simp only [subgroupLeftMul_apply, MulOpposite.unop_op]
  rw [h, coefficientToReducedCrossed_scalar_mul, smul_mul_assoc, mul_smul_comm, ← mul_assoc,
    (subgroupProjection_isStarProjection Γ F).isIdempotentElem.eq]

variable (v : H)

/-- `z ↦ z v`, from the standard module of `ℂ` to `H`. -/
def vectorMap : ℂᵐᵒᵖ →ₗ[ℂ] H where
  toFun z := MulOpposite.unop z • v
  map_add' z w := by simp [add_smul]
  map_smul' a z := by simp [mul_smul]

omit [CompleteSpace H] in
@[simp] theorem vectorMap_apply (z : ℂᵐᵒᵖ) : vectorMap v z = MulOpposite.unop z • v := rfl

/-- The bilinear map `(z, d) ↦ z v ⊗ P_F d`. -/
def subgroupBilinear :
    ℂᵐᵒᵖ →ₗ[ℂ] (GroupCrossed Γ)ᵐᵒᵖ →ₗ[ℂ] DescendedModule (Γ := Γ) H :=
  ((interiorModuleTensorMk (KasparovDescent.coefficientRepresentation (scalarAction Γ))).comp
    (vectorMap v)).compl₂ (subgroupLeftMul F)

@[simp] theorem subgroupBilinear_apply (z : ℂᵐᵒᵖ) (d : (GroupCrossed Γ)ᵐᵒᵖ) :
    subgroupBilinear F v z d =
      KasparovDescent.mk (scalarAction Γ) H (MulOpposite.unop z • v) (subgroupLeftMul F d) :=
  rfl

theorem subgroupBilinear_balance (z : ℂ) (w : ℂᵐᵒᵖ) (d : (GroupCrossed Γ)ᵐᵒᵖ) :
    subgroupBilinear F v (MulOpposite.op z • w) d =
      subgroupBilinear F v w (standardCoefficientImageRepresentation (subgroupHom Γ F) z d) := by
  rw [subgroupBilinear_apply, subgroupBilinear_apply, ← subgroupLeftMul_intertwines,
    ← KasparovDescent.mk_balance]
  congr 1
  change (MulOpposite.unop w * z) • v = z • (MulOpposite.unop w • v)
  rw [smul_smul, mul_comm]

/-- The balanced map `z ⊗ d ↦ z v ⊗ P_F d`. -/
def subgroupBalanced :
    BalancedModuleTensor (E := ℂᵐᵒᵖ) (standardCoefficientImageRepresentation (subgroupHom Γ F)) →ₗ[ℂ]
      DescendedModule (Γ := Γ) H :=
  moduleTensorLift _ (subgroupBilinear F v) (subgroupBilinear_balance F v)

@[simp] theorem subgroupBalanced_mk (z : ℂᵐᵒᵖ) (d : (GroupCrossed Γ)ᵐᵒᵖ) :
    subgroupBalanced F v (moduleTensorMk _ z d) =
      KasparovDescent.mk (scalarAction Γ) H (MulOpposite.unop z • v) (subgroupLeftMul F d) := rfl

variable {v}

omit [CompleteSpace H] in
/-- For a unit vector, `z ↦ z v` preserves the inner product. -/
theorem inner_vectorMap (hv : ⟪v, v⟫_ℂ = 1) (z w : ℂᵐᵒᵖ) :
    ⟪MulOpposite.unop z • v, MulOpposite.unop w • v⟫_(ℂᵐᵒᵖ) = ⟪z, w⟫_(ℂᵐᵒᵖ) := by
  rw [ScalarHilbertModule.inner_eq_op, inner_smul_left, inner_smul_right, hv, mul_one]
  rfl

theorem subgroupBalanced_inner_mk (hv : ⟪v, v⟫_ℂ = 1) (z z' : ℂᵐᵒᵖ)
    (y y' : (GroupCrossed Γ)ᵐᵒᵖ) :
    ⟪subgroupBalanced F v (moduleTensorMk _ z y),
        subgroupBalanced F v (moduleTensorMk _ z' y')⟫_((GroupCrossed Γ)ᵐᵒᵖ) =
      moduleTensorInner (standardCoefficientImageRepresentation (subgroupHom Γ F))
        (moduleTensorMk _ z y) (moduleTensorMk _ z' y') := by
  rw [subgroupBalanced_mk, subgroupBalanced_mk, moduleTensorInner_mk_mk,
    KasparovDescent.mk_inner, inner_vectorMap hv]
  unfold moduleTensorPureInner
  change _ = MulOpposite.op (star (MulOpposite.unop y) *
    (subgroupHom Γ F (MulOpposite.unop ⟪z, z'⟫_(ℂᵐᵒᵖ)) * MulOpposite.unop y'))
  have hP := subgroupProjection_isStarProjection Γ F
  rw [subgroupLeftMul_apply, subgroupLeftMul_apply, MulOpposite.unop_op, MulOpposite.unop_op,
    coefficientToReducedCrossed_scalar_mul, FinitePointCutoff.projectionScalarHom_apply, star_mul,
    hP.isSelfAdjoint.star_eq, mul_smul_comm, smul_mul_assoc, mul_smul_comm, ← mul_assoc,
    mul_assoc _ (subgroupProjection Γ F), mul_assoc (star (MulOpposite.unop y)),
    ← mul_assoc (subgroupProjection Γ F) (subgroupProjection Γ F),
    hP.isIdempotentElem.eq]

theorem subgroupBalanced_inner (hv : ⟪v, v⟫_ℂ = 1)
    (u w : BalancedModuleTensor (E := ℂᵐᵒᵖ)
      (standardCoefficientImageRepresentation (subgroupHom Γ F))) :
    ⟪subgroupBalanced F v u, subgroupBalanced F v w⟫_((GroupCrossed Γ)ᵐᵒᵖ) =
      moduleTensorInner _ u w := by
  revert w
  refine moduleTensor_induction _ u ?_ ?_ ?_
  · intro w
    simp only [map_zero, LinearMap.zero_apply]
    exact CStarModule.inner_zero_left (A := (GroupCrossed Γ)ᵐᵒᵖ)
      (E := DescendedModule (Γ := Γ) H)
  · intro z y w
    refine moduleTensor_induction _ w ?_ ?_ ?_
    · simp only [map_zero]
      exact CStarModule.inner_zero_right (A := (GroupCrossed Γ)ᵐᵒᵖ)
        (E := DescendedModule (Γ := Γ) H)
    · intro z' y'
      exact subgroupBalanced_inner_mk F hv z z' y y'
    · intro w w' hw hw'
      simp only [map_add]
      rw [CStarModule.inner_add_right (A := (GroupCrossed Γ)ᵐᵒᵖ)
        (E := DescendedModule (Γ := Γ) H), hw, hw']
  · intro u u' hu hu' w
    simp only [map_add, LinearMap.add_apply]
    rw [CStarModule.inner_add_left (A := (GroupCrossed Γ)ᵐᵒᵖ)
      (E := DescendedModule (Γ := Γ) H), hu w, hu' w]

/-- The completed isometry `ℂ ⊗_{P_F} C*_r(Γ) → H ⊗ C*_r(Γ)`, `z ⊗ d ↦ z v ⊗ P_F d`. -/
def subgroupIsometry (hv : ⟪v, v⟫_ℂ = 1) :
    SubgroupTensor F →ₗᵢ[ℂ] DescendedModule (Γ := Γ) H :=
  InteriorModuleTensorFormCompletion.completedIsometry _ (subgroupBalanced F v)
    (subgroupBalanced_inner F hv)

@[simp] theorem subgroupIsometry_mk (hv : ⟪v, v⟫_ℂ = 1) (z : ℂᵐᵒᵖ) (d : (GroupCrossed Γ)ᵐᵒᵖ) :
    subgroupIsometry F hv (interiorModuleTensorMk _ z d) =
      KasparovDescent.mk (scalarAction Γ) H (MulOpposite.unop z • v)
        (MulOpposite.op (subgroupProjection Γ F * MulOpposite.unop d)) :=
  InteriorModuleTensorFormCompletion.completedIsometry_mk _ _ _ z d

theorem subgroupIsometry_inner (hv : ⟪v, v⟫_ℂ = 1) (u w : SubgroupTensor F) :
    ⟪subgroupIsometry F hv u, subgroupIsometry F hv w⟫_((GroupCrossed Γ)ᵐᵒᵖ) =
      ⟪u, w⟫_((GroupCrossed Γ)ᵐᵒᵖ) :=
  InteriorModuleTensorFormCompletion.completedIsometry_inner _ _ _ u w

theorem subgroupTensor_clm_ext {M : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M]
    {L L' : SubgroupTensor F →L[ℂ] M}
    (h : ∀ z d, L (interiorModuleTensorMk _ z d) = L' (interiorModuleTensorMk _ z d)) :
    L = L' :=
  ContinuousLinearMap.ext_on (interiorModuleTensor_span_dense _)
    (by rintro _ ⟨⟨z, d⟩, rfl⟩; exact h z d)

end Tensor

section Range
variable {Γ : Type} [Group Γ] (F : Subgroup Γ) [Fintype F]
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {v : H} (hv : ⟪v, v⟫_ℂ = 1)
  (p : AdjointableMap (GroupCrossed Γ) (DescendedModule (Γ := Γ) H) (DescendedModule (Γ := Γ) H))

/-- The support condition: `p` acts as `x ⊗ d ↦ ⟨v, x⟩ v ⊗ P_F d`. -/
def IsSubgroupSupport : Prop :=
  ∀ x d, p (KasparovDescent.mk (scalarAction Γ) H x d) =
    KasparovDescent.mk (scalarAction Γ) H (⟪v, x⟫_ℂ • v) (subgroupLeftMul F d)

include hv in
/-- The support projection fixes the image of `ℂ ⊗_{P_F} C*_r(Γ)`. -/
theorem projection_subgroupIsometry (hp : IsSubgroupSupport F (v := v) p) (u : SubgroupTensor F) :
    p (subgroupIsometry F hv u) = subgroupIsometry F hv u := by
  let L := (subgroupIsometry (H := H) F hv).toContinuousLinearMap
  have h : p.toCLM.comp L = L := by
    apply subgroupTensor_clm_ext
    intro z d
    change p (subgroupIsometry F hv (interiorModuleTensorMk _ z d)) =
      subgroupIsometry F hv (interiorModuleTensorMk _ z d)
    rw [subgroupIsometry_mk]
    change p (KasparovDescent.mk (scalarAction Γ) H (MulOpposite.unop z • v) (subgroupLeftMul F d)) =
      KasparovDescent.mk (scalarAction Γ) H (MulOpposite.unop z • v) (subgroupLeftMul F d)
    rw [hp, subgroupLeftMul_idem, inner_smul_right, hv, mul_one]
  exact DFunLike.congr_fun h u

include hv in
/-- Every fixed vector of the support projection lies in the image of `ℂ ⊗_{P_F} C*_r(Γ)`. -/
theorem mem_range_subgroupIsometry (hp : IsSubgroupSupport F (v := v) p)
    (w : DescendedModule (Γ := Γ) H) (hw : p w = w) :
    ∃ u, subgroupIsometry F hv u = w := by
  let R := LinearMap.range (subgroupIsometry (H := H) F hv).toLinearMap
  have hclosed : IsClosed (R : Set (DescendedModule (Γ := Γ) H)) :=
    (subgroupIsometry (H := H) F hv).isometry.isClosedEmbedding.isClosed_range
  let K : Submodule ℂ (DescendedModule (Γ := Γ) H) := R.comap p.toCLM.toLinearMap
  have hK : IsClosed (K : Set (DescendedModule (Γ := Γ) H)) :=
    hclosed.preimage p.toCLM.continuous
  have hspan : Submodule.span ℂ (Set.range fun q : H × (GroupCrossed Γ)ᵐᵒᵖ =>
      interiorModuleTensorMk (KasparovDescent.coefficientRepresentation (scalarAction Γ))
        q.1 q.2) ≤ K := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨x, d⟩, rfl⟩
    refine ⟨interiorModuleTensorMk _ (MulOpposite.op ⟪v, x⟫_ℂ) d, ?_⟩
    change subgroupIsometry F hv (interiorModuleTensorMk _ (MulOpposite.op ⟪v, x⟫_ℂ) d) =
      p (KasparovDescent.mk (scalarAction Γ) H x d)
    rw [subgroupIsometry_mk, hp]
    rfl
  have hw' : w ∈ K := hK.closure_subset_iff.mpr hspan (interiorModuleTensor_span_dense _ w)
  obtain ⟨u, hu⟩ := hw'
  exact ⟨u, hu.trans hw⟩

/-- The isometry, corestricted to the range of the support projection. -/
def subgroupRangeIsometry (hp : IsSubgroupSupport F (v := v) p) :
    SubgroupTensor F →ₗᵢ[ℂ] ProjectionModule p where
  toLinearMap := (subgroupIsometry (H := H) F hv).toLinearMap.codRestrict
    (projectionFixedSubmodule p) (projection_subgroupIsometry F hv p hp)
  norm_map' u := (subgroupIsometry (H := H) F hv).norm_map u

theorem subgroupRangeIsometry_surjective (hp : IsSubgroupSupport F (v := v) p) :
    Function.Surjective (subgroupRangeIsometry F hv p hp) := by
  intro y
  obtain ⟨u, hu⟩ := mem_range_subgroupIsometry F hv p hp (y : DescendedModule (Γ := Γ) H)
    y.property
  exact ⟨u, Subtype.ext hu⟩

/-- `ℂ ⊗_{P_F} C*_r(Γ)` is unitarily the range of the support projection. -/
def subgroupRangeEquiv (hp : IsSubgroupSupport F (v := v) p) :
    HilbertModuleEquiv (GroupCrossed Γ) (SubgroupTensor F) (ProjectionModule p) where
  linearIsometryEquiv := LinearIsometryEquiv.ofSurjective (subgroupRangeIsometry F hv p hp)
    (subgroupRangeIsometry_surjective F hv p hp)
  inner_map u w := subgroupIsometry_inner F hv u w

@[simp] theorem subgroupRangeEquiv_coe (hp : IsSubgroupSupport F (v := v) p)
    (u : SubgroupTensor F) :
    ((subgroupRangeEquiv F hv p hp u : ProjectionModule p) : DescendedModule (Γ := Γ) H) =
      subgroupIsometry F hv u := rfl

end Range

section Sum
variable {B M : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Bᵐᵒᵖ M] [CStarModule Bᵐᵒᵖ M]

/-- Finite sums of adjointable maps are evaluated pointwise. -/
theorem adjointable_finsetSum_apply {ι : Type*} (s : Finset ι) (T : ι → AdjointableMap B M M)
    (u : M) : (∑ i ∈ s, T i) u = ∑ i ∈ s, T i u := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, AdjointableMap.coe_add_apply, ih]

end Sum

section Support
variable {Γ : Type} [Group Γ] [Countable Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
  (F : Subgroup Γ) [Fintype F]
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The translation action of `Γ` on `C₀(Γ ⧸ F)`. -/
abbrev cosetAction : CStarAlgebraAction Γ C₀(Γ ⧸ F, ℂ) := CZero.action Γ

/-- The cutoff projection `p = ∑_{f ∈ F} |F|⁻¹ δ_{eF} δ_f` of `C₀(Γ ⧸ F) ⋊_r Γ`. -/
abbrev cutoffProjection : ReducedCrossedProduct (cosetAction F) :=
  Cutoff.reducedCutoffProjection (baseCutoff Γ F)

omit [Countable Γ] in
theorem cutoffProjection_eq_sum :
    cutoffProjection F = ∑ f : F, algebraicToReducedCrossed (cosetAction F)
      (AlgebraicCrossedProduct.single (cosetAction F) (f : Γ)
        ((Nat.card F : ℂ)⁻¹ • cosetDelta Γ F)) := by
  unfold cutoffProjection Cutoff.reducedCutoffProjection
  rw [algebraicProjection_baseCutoff, map_sum]

omit [Countable Γ] in
/-- If `δ_{eF}` acts as the rank-one projection onto a unit vector `v` fixed by `F`, the cutoff
projection acts on the descended module as `x ⊗ d ↦ ⟨v, x⟩ v ⊗ P_F d`. -/
theorem reducedSourceRepresentation_cutoffProjection_mk {v : H}
    (U : EquivariantHilbertModule (scalarAction Γ) H)
    (π : C₀(Γ ⧸ F, ℂ) →⋆ₙₐ[ℂ] AdjointableMap ℂ H H)
    (hπ : ∀ g a, U.conjugateOperator g (π a) = π ((cosetAction F).automorphism g a))
    (hrep : ∀ x, π (cosetDelta Γ F) x = ⟪v, x⟫_ℂ • v)
    (hfix : ∀ f ∈ F, U.action f v = v)
    (x : H) (d : (GroupCrossed Γ)ᵐᵒᵖ) :
    KasparovDescent.reducedSourceRepresentation (scalarAction Γ) H (cosetAction F) U π hπ
        (cutoffProjection F) (KasparovDescent.mk (scalarAction Γ) H x d) =
      KasparovDescent.mk (scalarAction Γ) H (⟪v, x⟫_ℂ • v) (subgroupLeftMul F d) := by
  have hinv : ∀ f : F, ⟪v, U.action (f : Γ) x⟫_ℂ = ⟪v, x⟫_ℂ := by
    intro f
    have h := U.inner_action (f : Γ) v x
    rw [hfix (f : Γ) f.2] at h
    exact congrArg MulOpposite.unop h
  have hterm : ∀ f : F, KasparovDescent.reducedSourceRepresentation (scalarAction Γ) H
      (cosetAction F) U π hπ (algebraicToReducedCrossed (cosetAction F)
        (AlgebraicCrossedProduct.single (cosetAction F) (f : Γ)
          ((Nat.card F : ℂ)⁻¹ • cosetDelta Γ F))) (KasparovDescent.mk (scalarAction Γ) H x d) =
      KasparovDescent.mk (scalarAction Γ) H (⟪v, x⟫_ℂ • v)
        (MulOpposite.op (((Nat.card F : ℂ)⁻¹ • regular Γ (f : Γ)) * MulOpposite.unop d)) := by
    intro f
    rw [KasparovDescent.reducedSourceRepresentation_single, KasparovDescent.sourceGenerator_mk,
      leftRegular_eq_mul, map_smul, AdjointableMap.coe_smul_apply, hrep, hinv,
      smul_mul_assoc, MulOpposite.op_smul]
    unfold KasparovDescent.mk
    rw [LinearMap.map_smul₂]
    exact (map_smul _ _ _).symm
  refine (congrArg (fun q => KasparovDescent.reducedSourceRepresentation (scalarAction Γ) H
    (cosetAction F) U π hπ q (KasparovDescent.mk (scalarAction Γ) H x d))
    (cutoffProjection_eq_sum F)).trans ?_
  rw [map_sum]
  refine (adjointable_finsetSum_apply _ _ _).trans ?_
  refine (Finset.sum_congr rfl fun f _ => hterm f).trans ?_
  have hd : subgroupLeftMul F d =
      ∑ f : F, MulOpposite.op (((Nat.card F : ℂ)⁻¹ • regular Γ (f : Γ)) * MulOpposite.unop d) := by
    apply MulOpposite.unop_injective
    rw [subgroupLeftMul_apply, MulOpposite.unop_op, subgroupProjection, Finset.sum_mul,
      Finset.unop_sum]
    simp only [MulOpposite.unop_op]
  rw [hd]
  unfold KasparovDescent.mk
  exact (map_sum _ _ _).symm

end Support

section Zero
variable {Γ B E : Type*} [Group Γ]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]
  {β : CStarAlgebraAction Γ B}

/-- A scalar cycle with zero operator has zero support compression. -/
theorem scalarSupportCompression_eq_zero
    (c : KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) β E)
    (h : c.operator = 0) (x : ProjectionModule c.scalarSupportProjection) :
    (c.scalarSupportCompression x : E) = 0 := by
  rw [KasparovCycle.scalarSupportCompression_coe, KasparovCycle.scalarSupportBlockOperator, h]
  simp

end Zero

section EvenCycle
variable {Γ : Type} [Group Γ] [Countable Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
  (F : Subgroup Γ) [Fintype F]
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance cosetCZero_separable : TopologicalSpace.SeparableSpace C₀(Γ ⧸ F, ℂ) :=
  TopologicalKHomology.cZero_separableSpace

/-- The scalar homomorphism `z ↦ z • p` of the cutoff projection. -/
abbrev cutoffHom : ℂ →⋆ₙₐ[ℂ] ReducedCrossedProduct (cosetAction F) :=
  FinitePointCutoff.projectionScalarHom (cutoffProjection F)
    (Cutoff.reducedCutoffProjection_isStarProjection _)

omit [Countable Γ] in
theorem cutoffHom_equivariant : ∀ (g : Unit) (a : ℂ),
    cutoffHom F ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ).automorphism g a) =
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit
        (ReducedCrossedProduct (cosetAction F))).automorphism g (cutoffHom F a) := fun _ _ => rfl

/-- The descended cycle pulled back along `z ↦ z • p`. -/
abbrev pulledDescent (c : KasparovCycle (cosetAction F) (scalarAction Γ) H) :=
  NativeSourcePullback.evenCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
    (cutoffHom F) (cutoffHom_equivariant F)
    (KasparovDescent.evenCycle (scalarAction Γ) (cosetAction F) c)

/-- The coefficient extension of the identity cycle of `KK(ℂ, ℂ)` along `z ↦ z • P_F`. -/
abbrev identityTensorCycle :
    KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (GroupCrossed Γ)) (SubgroupTensor F) :=
  ScalarUnitProjection.scalarIdentityCycle.scalarCoefficientTensor (subgroupHom Γ F)

variable {F} {v : H} (hv : ⟪v, v⟫_ℂ = 1) (c : KasparovCycle (cosetAction F) (scalarAction Γ) H)
  (hrep : ∀ x, c.representation (cosetDelta Γ F) x = ⟪v, x⟫_ℂ • v)
  (hfix : ∀ f ∈ F, c.groupAction.action f v = v)

include hrep hfix in
theorem pulledDescent_support : IsSubgroupSupport F (v := v) (pulledDescent F c).scalarSupportProjection := by
  intro x d
  change KasparovDescent.reducedSourceRepresentation (scalarAction Γ) H (cosetAction F)
    c.groupAction c.representation c.representation_equivariant
    ((1 : ℂ) • cutoffProjection F) _ = _
  rw [one_smul]
  exact reducedSourceRepresentation_cutoffProjection_mk F c.groupAction c.representation
    c.representation_equivariant hrep hfix x d

/-- The standard identity representation is scalar multiplication. -/
theorem identity_representation (z : ℂ) :
    ScalarUnitProjection.scalarIdentityCycle.representation z = z • 1 := by
  ext x
  change MulOpposite.op (z * MulOpposite.unop x) = MulOpposite.unop (MulOpposite.op (z • x))
  rfl

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
theorem identityTensor_representation (z : ℂ) (u : SubgroupTensor F) :
    (identityTensorCycle F).representation z u = z • u := by
  change interiorModuleTensorOperatorHom _
    (ScalarUnitProjection.scalarIdentityCycle.representation z) u = z • u
  rw [identity_representation, map_smul, map_one]
  rfl

include hv hrep hfix in
theorem supportEquiv_representation (z : ℂ) (u : SubgroupTensor F) :
    subgroupRangeEquiv F hv _ (pulledDescent_support c hrep hfix)
        ((identityTensorCycle F).representation z u) =
      (pulledDescent F c).scalarSupportRepresentation z
        (subgroupRangeEquiv F hv _ (pulledDescent_support c hrep hfix) u) := by
  refine Eq.trans ?_ (KasparovCycle.scalarSupportRepresentation_apply _ z _).symm
  apply Subtype.ext
  refine (subgroupRangeEquiv_coe F hv _ _ _).trans ?_
  refine (congrArg (subgroupIsometry F hv) (identityTensor_representation z u)).trans ?_
  refine (map_smul _ z u).trans ?_
  rfl

include hv hrep hfix in
theorem supportEquiv_operator (hop : c.operator = 0) (u : SubgroupTensor F) :
    subgroupRangeEquiv F hv _ (pulledDescent_support c hrep hfix)
        ((identityTensorCycle F).operator u) =
      (pulledDescent F c).scalarSupportCompression
        (subgroupRangeEquiv F hv _ (pulledDescent_support c hrep hfix) u) := by
  apply Subtype.ext
  have h0 : (pulledDescent F c).operator = 0 := by
    change KasparovDescent.operatorHom (scalarAction Γ) H c.operator = 0
    rw [hop, map_zero]
  have hs0 : (identityTensorCycle F).operator = 0 := by
    change interiorModuleTensorOperator _ (0 : AdjointableMap ℂ ℂᵐᵒᵖ ℂᵐᵒᵖ) = 0
    exact map_zero (interiorModuleTensorOperatorHom
      (standardCoefficientImageRepresentation (subgroupHom Γ F)))
  refine (congrArg (fun T => (subgroupRangeEquiv F hv _ (pulledDescent_support c hrep hfix)
    (T u)).1) hs0).trans ?_
  refine Eq.trans ?_ (scalarSupportCompression_eq_zero _ h0 _).symm
  change (subgroupRangeEquiv F hv _ (pulledDescent_support c hrep hfix) 0).1 = 0
  rw [map_zero]
  rfl

include hv hrep hfix in
theorem supportEquiv_grading (hgr : ∀ x, c.grading.grading x = x) (u : SubgroupTensor F) :
    subgroupRangeEquiv F hv _ (pulledDescent_support c hrep hfix)
        ((identityTensorCycle F).grading.grading u) =
      (pulledDescent F c).scalarSupportGrading.grading
        (subgroupRangeEquiv F hv _ (pulledDescent_support c hrep hfix) u) := by
  apply Subtype.ext
  refine (subgroupRangeEquiv_coe F hv _ _ _).trans ?_
  refine Eq.trans ?_ (KasparovCycle.scalarSupportGrading_coe _ _).symm
  let V := (subgroupIsometry (H := H) F hv).toContinuousLinearMap
  have h : V.comp (identityTensorCycle F).grading.grading.toLinearIsometry.toContinuousLinearMap =
      (KasparovDescent.ordinaryModuleGrading (scalarAction Γ)
        c.grading).grading.toLinearIsometry.toContinuousLinearMap.comp V := by
    apply subgroupTensor_clm_ext
    intro z d
    have hg : (identityTensorCycle F).grading.grading (interiorModuleTensorMk _ z d) =
        interiorModuleTensorMk _ z d := by
      refine (GradedHilbertModule.interiorTensor_grading_mk _ _ _ z d).trans ?_
      rfl
    change subgroupIsometry F hv ((identityTensorCycle F).grading.grading
        (interiorModuleTensorMk _ z d)) =
      (KasparovDescent.ordinaryModuleGrading (scalarAction Γ) c.grading).grading
        (subgroupIsometry F hv (interiorModuleTensorMk _ z d))
    rw [hg, subgroupIsometry_mk, KasparovDescent.ordinaryModuleGrading_mk, hgr]
  exact DFunLike.congr_fun h u

/-- The whole-cycle isomorphism: the coefficient extension of the identity class along
`z ↦ z • P_F` is the support cycle of the pulled-back descent of `c`. -/
def supportIso (hop : c.operator = 0) (hgr : ∀ x, c.grading.grading x = x) :
    KasparovCycleIso (identityTensorCycle F) (pulledDescent F c).scalarSupportCycle where
  moduleEquiv := subgroupRangeEquiv F hv _ (pulledDescent_support c hrep hfix)
  grading_intertwine := supportEquiv_grading hv c hrep hfix hgr
  action_intertwine _ _ := rfl
  representation_intertwine := supportEquiv_representation hv c hrep hfix
  operator_intertwine := supportEquiv_operator hv c hrep hfix hop

/-- The identity class of `KK(ℂ, ℂ)` is the class of the standard identity cycle. -/
theorem identity_eq_mk :
    GroupUniverseParityUnits.identity.{0,0,0} ScalarUnitProjection.scalarIdentityAction =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of ScalarUnitProjection.scalarIdentityCycle) := by
  unfold GroupUniverseParityUnits.identity
  rw [GradedKasparovHomotopyClass.ulift_eq_self]
  rfl

include hv hrep hfix in
/-- Compressed descent on `Γ ⧸ F`, even case: the descent of `[c]` pulled back along
`z ↦ z • p` is the identity class of `KK(ℂ, ℂ)` pushed forward along `z ↦ z • P_F`. -/
theorem even_compressedDescent (hop : c.operator = 0) (hgr : ∀ x, c.grading.grading x = x) :
    sourcePullback.{0,0,0,0,0} (Γ := Unit) (A := ℂ)
        (B := ReducedCrossedProduct (cosetAction F)) (C := GroupCrossed Γ)
        («α» := (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ))
        («β» := CStarAlgebraAction.trivial) («γ» := CStarAlgebraAction.trivial)
        false (cutoffHom F) (cutoffHom_equivariant F)
        (KasparovDescent.evenClass (scalarAction Γ) (cosetAction F)
          (KasparovHomotopyClass.mk (BundledKasparovCycle.of c))) =
      GroupUniverseOrdinaryEven.coefficientPushforward.{0,0,0} (subgroupHom Γ F)
        (GroupUniverseParityUnits.identity.{0,0,0} ScalarUnitProjection.scalarIdentityAction) := by
  calc _ = KasparovHomotopyClass.mk (BundledKasparovCycle.of (pulledDescent F c)) := by
        rw [KasparovDescent.evenClass_mk, NativeSourcePullback.even_mk]
        rfl
    _ = KasparovHomotopyClass.mk (BundledKasparovCycle.of (pulledDescent F c).scalarSupportCycle) :=
        KasparovCycle.scalarSupport_class _
    _ = KasparovHomotopyClass.mk (BundledKasparovCycle.of (identityTensorCycle F)) :=
        (KasparovHomotopyClass.mk_eq_of_iso (supportIso hv c hrep hfix hop hgr)).symm
    _ = _ := by
        rw [identity_eq_mk]
        exact (GroupUniverseOrdinaryEven.coefficientPushforward_mk_scalarCoefficientTensor
          ScalarUnitProjection.scalarIdentityCycle (subgroupHom Γ F)).symm

end EvenCycle

end BC4lean.KKTheory.CosetCompressedDescent

import BC4lean.FinitePointCutoff
import BC4lean.KasparovDescentClass
import BC4lean.NativeEvenSourcePullback
import BC4lean.NativeOddSourcePullback
import BC4lean.OrdinaryScalarCoefficientTensor
import BC4lean.OrdinaryOddCoefficientTensor
import BC4lean.GroupUniverseOrdinaryEven
import BC4lean.GroupUniverseOrdinaryOdd
import BC4lean.ScalarKasparovSupportClass
import BC4lean.OddScalarKasparovSupportClass
import BC4lean.InteriorModuleTensorFormCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! The character projection of a finite group and the coefficient extension along it.

For a finite group `Γ` and a unitary character `χ`, `P_χ = |Γ|⁻¹ ∑_g χ(g) λ_g` is a
star projection in `C*_r(Γ)`. For a Hilbert space `E`, the map `x ⊗ d ↦ x ⊗ P_χ d`
is an isometry from the coefficient extension `E ⊗_{P_χ} C*_r(Γ)` along
`z ↦ z • P_χ` onto the fixed space of any projection on `E ⊗ C*_r(Γ)` that acts
as `1 ⊗ P_χ` on elementary tensors. If `Γ` acts on `E` through `χ` and the
point acts unitally, the averaging element of `C*_r(Γ ⋉ C₀(pt))` acts on the
descended module in exactly this way. -/

noncomputable section
namespace BC4lean.KKTheory.FinitePointCharacterTensor
open BC4lean.ProperActions BC4lean.OperatorKTheory BC4lean.Chapter8Examples
open KKTheory.GroupUniverseParityGroup KKTheory.GroupUniverseParityFunctoriality
open scoped ZeroAtInfty ComplexOrder KasparovDescent InnerProductSpace

section Character
variable (Γ : Type) [Group Γ]

/-- The trivial action of `Γ` on the scalars. -/
abbrev scalarAction : CStarAlgebraAction Γ ℂ := CStarAlgebraAction.trivial

/-- The reduced group C*-algebra, as the reduced crossed product of the scalars. -/
abbrev GroupCrossed := ReducedCrossedProduct (scalarAction Γ)

/-- Scalar coefficients act on the regular module as scalar multiples of the identity. -/
theorem reducedCrossedCoefficient_scalar (z : ℂ) :
    reducedCrossedCoefficient (scalarAction Γ) z = z • 1 := by
  apply reducedCrossedRegular_ext
  intro x
  rw [reducedCrossedCoefficient_mk, AdjointableMap.coe_smul_apply, AdjointableMap.one_apply,
    ← map_smul]
  congr 1
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy, smul_add]
  | single i b =>
    rw [reducedCrossedFiniteDiagonal_single, Finsupp.smul_single]
    congr 1

/-- The regular unitary `λ_g` as an element of the reduced group algebra. -/
def regular (g : Γ) : GroupCrossed Γ :=
  ⟨reducedCrossedRegular g, by
    have h : reducedCrossedGenerator (scalarAction Γ) 1 g = reducedCrossedRegular g := by
      rw [reducedCrossedGenerator, reducedCrossedCoefficient_scalar, one_smul, one_mul]
    exact h ▸ reducedCrossedGenerator_mem (scalarAction Γ) 1 g⟩

@[simp] theorem regular_coe (g : Γ) :
    (regular Γ g : AdjointableMap ℂ (ReducedCrossedHilbertModule ℂ Γ)
      (ReducedCrossedHilbertModule ℂ Γ)) = reducedCrossedRegular g := rfl

theorem regular_mul (g h : Γ) : regular Γ g * regular Γ h = regular Γ (g * h) :=
  Subtype.ext (reducedCrossedRegular_mul g h).symm

theorem star_regular (g : Γ) : star (regular Γ g) = regular Γ g⁻¹ :=
  Subtype.ext (reducedCrossedRegular_star g)

/-- The left regular multiplier on the descended coefficients is left
multiplication by `λ_g`. -/
theorem leftRegular_eq_mul (g : Γ) (c : GroupCrossed Γ) :
    KasparovDescent.leftRegular (scalarAction Γ) g c = regular Γ g * c := rfl

variable [Fintype Γ]

/-- The character projection `P_χ = |Γ|⁻¹ ∑_g χ(g) λ_g` of a unitary character; it satisfies
`λ_h P_χ = χ(h)⁻¹ P_χ`. -/
def characterProjection (χ : Γ →* unitary ℂ) : GroupCrossed Γ :=
  ∑ g : Γ, ((Fintype.card Γ : ℂ)⁻¹ * (χ g : ℂ)) • regular Γ g

theorem characterProjection_isStarProjection (χ : Γ →* unitary ℂ) :
    IsStarProjection (characterProjection Γ χ) := by
  have hn : (Fintype.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hχ : ∀ g h : Γ, (χ g : ℂ) * (χ h : ℂ) = (χ (g * h) : ℂ) := fun g h => by
    rw [map_mul]; rfl
  have hstar : ∀ g : Γ, star (χ g : ℂ) = (χ g⁻¹ : ℂ) := fun g => by
    rw [map_inv, ← Unitary.coe_star, Unitary.star_eq_inv]
  refine isStarProjection_iff'.mpr ⟨?_, ?_⟩
  · unfold characterProjection
    rw [Finset.sum_mul_sum]
    have hinner : ∀ g : Γ, ∑ h : Γ, (((Fintype.card Γ : ℂ)⁻¹ * (χ g : ℂ)) • regular Γ g) *
        (((Fintype.card Γ : ℂ)⁻¹ * (χ h : ℂ)) • regular Γ h) =
        ∑ k : Γ, ((Fintype.card Γ : ℂ)⁻¹ * ((Fintype.card Γ : ℂ)⁻¹ * (χ k : ℂ))) •
          regular Γ k := by
      intro g
      refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h => ?_
      rw [smul_mul_smul_comm, regular_mul, Equiv.coe_mulLeft, mul_mul_mul_comm, hχ, mul_assoc]
    rw [Finset.sum_congr rfl fun g _ => hinner g, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℂ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  · unfold characterProjection
    rw [star_sum]
    refine Fintype.sum_equiv (Equiv.inv Γ) _ _ fun g => ?_
    rw [star_smul, star_regular, Equiv.inv_apply, star_mul', hstar, star_inv₀,
      star_natCast, mul_comm]

/-- The scalar homomorphism `z ↦ z • P_χ`. -/
abbrev characterHom (χ : Γ →* unitary ℂ) : ℂ →⋆ₙₐ[ℂ] GroupCrossed Γ :=
  FinitePointCutoff.projectionScalarHom (characterProjection Γ χ)
    (characterProjection_isStarProjection Γ χ)

end Character

section Tensor
variable {Γ : Type} [Group Γ] [Fintype Γ]
variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul ℂᵐᵒᵖ E]
  [CStarModule ℂᵐᵒᵖ E] [CompleteSpace E]

/-- The descended module `E ⊗ C*_r(Γ)`. -/
abbrev DescendedModule := KasparovDescent.Module (scalarAction Γ) E

/-- The coefficient extension `E ⊗_{P_χ} C*_r(Γ)` along `z ↦ z • P_χ`. -/
abbrev CharacterTensor (χ : Γ →* unitary ℂ) :=
  InteriorModuleTensor (E := E) (standardCoefficientImageRepresentation (characterHom Γ χ))

omit [Fintype Γ] in
/-- Scalar coefficients act on the reduced group algebra by scalar multiplication. -/
private theorem coefficientToReducedCrossed_mul (z : ℂ) (a : GroupCrossed Γ) :
    coefficientToReducedCrossed (scalarAction Γ) z * a = z • a := by
  apply Subtype.ext
  change reducedCrossedCoefficient (scalarAction Γ) z * (a : AdjointableMap ℂ
    (ReducedCrossedHilbertModule ℂ Γ) (ReducedCrossedHilbertModule ℂ Γ)) = z • (a : _)
  rw [reducedCrossedCoefficient_scalar, smul_mul_assoc, one_mul]

variable {E}

/-- Left multiplication by `P_χ` on the standard module. -/
def characterLeftMul (χ : Γ →* unitary ℂ) :
    (GroupCrossed Γ)ᵐᵒᵖ →ₗ[ℂ] (GroupCrossed Γ)ᵐᵒᵖ where
  toFun d := MulOpposite.op (characterProjection Γ χ * MulOpposite.unop d)
  map_add' d d' := by simp [mul_add]
  map_smul' z d := by simp [mul_smul_comm]

@[simp] theorem characterLeftMul_apply (χ : Γ →* unitary ℂ) (d : (GroupCrossed Γ)ᵐᵒᵖ) :
    characterLeftMul χ d = MulOpposite.op (characterProjection Γ χ * MulOpposite.unop d) := rfl

/-- The bilinear map `(x, d) ↦ x ⊗ P_χ d`. -/
def characterBilinear (χ : Γ →* unitary ℂ) :
    E →ₗ[ℂ] (GroupCrossed Γ)ᵐᵒᵖ →ₗ[ℂ] DescendedModule (Γ := Γ) E :=
  (interiorModuleTensorMk (KasparovDescent.coefficientRepresentation (scalarAction Γ))).compl₂
    (characterLeftMul χ)

/-- Left multiplication by `P_χ` intertwines the two scalar actions. -/
theorem characterLeftMul_intertwines (χ : Γ →* unitary ℂ) (z : ℂ) (d : (GroupCrossed Γ)ᵐᵒᵖ) :
    MulOpposite.op (coefficientToReducedCrossed (scalarAction Γ) z *
        MulOpposite.unop (characterLeftMul χ d)) =
      characterLeftMul χ (standardCoefficientImageRepresentation (characterHom Γ χ) z d) := by
  apply MulOpposite.unop_injective
  have h : MulOpposite.unop (standardCoefficientImageRepresentation (characterHom Γ χ) z d) =
      (z • characterProjection Γ χ) * MulOpposite.unop d := rfl
  simp only [characterLeftMul_apply, MulOpposite.unop_op]
  rw [h, coefficientToReducedCrossed_mul, smul_mul_assoc, mul_smul_comm, ← mul_assoc,
    (characterProjection_isStarProjection Γ χ).isIdempotentElem.eq]

@[simp] theorem characterBilinear_apply (χ : Γ →* unitary ℂ) (x : E) (d : (GroupCrossed Γ)ᵐᵒᵖ) :
    characterBilinear χ x d = KasparovDescent.mk (scalarAction Γ) E x (characterLeftMul χ d) :=
  rfl

theorem characterBilinear_balance (χ : Γ →* unitary ℂ) (z : ℂ) (x : E)
    (d : (GroupCrossed Γ)ᵐᵒᵖ) :
    characterBilinear χ (MulOpposite.op z • x) d =
      characterBilinear χ x (standardCoefficientImageRepresentation (characterHom Γ χ) z d) := by
  rw [characterBilinear_apply, characterBilinear_apply, KasparovDescent.mk_balance,
    characterLeftMul_intertwines]

/-- The balanced map `x ⊗ d ↦ x ⊗ P_χ d`. -/
def characterBalanced (χ : Γ →* unitary ℂ) :
    BalancedModuleTensor (E := E) (standardCoefficientImageRepresentation (characterHom Γ χ)) →ₗ[ℂ]
      DescendedModule (Γ := Γ) E :=
  moduleTensorLift _ (characterBilinear χ) (characterBilinear_balance χ)

@[simp] theorem characterBalanced_mk (χ : Γ →* unitary ℂ) (x : E) (d : (GroupCrossed Γ)ᵐᵒᵖ) :
    characterBalanced χ (moduleTensorMk _ x d) =
      KasparovDescent.mk (scalarAction Γ) E x (characterLeftMul χ d) := rfl

/-- The inner product of two pure tensors is preserved by `x ⊗ d ↦ x ⊗ P_χ d`. -/
theorem characterBalanced_inner_mk (χ : Γ →* unitary ℂ) (x x' : E)
    (y y' : (GroupCrossed Γ)ᵐᵒᵖ) :
    ⟪characterBalanced χ (moduleTensorMk _ x y),
        characterBalanced χ (moduleTensorMk _ x' y')⟫_((GroupCrossed Γ)ᵐᵒᵖ) =
      moduleTensorInner (standardCoefficientImageRepresentation (characterHom Γ χ))
        (moduleTensorMk _ x y) (moduleTensorMk _ x' y') := by
  rw [characterBalanced_mk, characterBalanced_mk, moduleTensorInner_mk_mk,
    KasparovDescent.mk_inner]
  unfold moduleTensorPureInner
  change _ = MulOpposite.op (star (MulOpposite.unop y) *
    (characterHom Γ χ (MulOpposite.unop ⟪x, x'⟫_(ℂᵐᵒᵖ)) * MulOpposite.unop y'))
  have hP := characterProjection_isStarProjection Γ χ
  rw [characterLeftMul_apply, characterLeftMul_apply, MulOpposite.unop_op, MulOpposite.unop_op,
    coefficientToReducedCrossed_mul, FinitePointCutoff.projectionScalarHom_apply, star_mul,
    hP.isSelfAdjoint.star_eq, mul_smul_comm, smul_mul_assoc, mul_smul_comm, ← mul_assoc,
    mul_assoc _ (characterProjection Γ χ), mul_assoc (star (MulOpposite.unop y)),
    ← mul_assoc (characterProjection Γ χ) (characterProjection Γ χ),
    hP.isIdempotentElem.eq]

theorem characterBalanced_inner (χ : Γ →* unitary ℂ)
    (u v : BalancedModuleTensor (E := E)
      (standardCoefficientImageRepresentation (characterHom Γ χ))) :
    ⟪characterBalanced χ u, characterBalanced χ v⟫_((GroupCrossed Γ)ᵐᵒᵖ) =
      moduleTensorInner _ u v := by
  revert v
  refine moduleTensor_induction _ u ?_ ?_ ?_
  · intro v
    simp only [map_zero, LinearMap.zero_apply]
    exact CStarModule.inner_zero_left (A := (GroupCrossed Γ)ᵐᵒᵖ)
      (E := DescendedModule (Γ := Γ) E)
  · intro x y v
    refine moduleTensor_induction _ v ?_ ?_ ?_
    · simp only [map_zero]
      exact CStarModule.inner_zero_right (A := (GroupCrossed Γ)ᵐᵒᵖ)
        (E := DescendedModule (Γ := Γ) E)
    · intro x' y'
      exact characterBalanced_inner_mk χ x x' y y'
    · intro v w hv hw
      simp only [map_add]
      rw [CStarModule.inner_add_right (A := (GroupCrossed Γ)ᵐᵒᵖ)
        (E := DescendedModule (Γ := Γ) E), hv, hw]
  · intro u w hu hw v
    simp only [map_add, LinearMap.add_apply]
    rw [CStarModule.inner_add_left (A := (GroupCrossed Γ)ᵐᵒᵖ)
      (E := DescendedModule (Γ := Γ) E), hu v, hw v]

/-- The completed isometry `E ⊗_{P_χ} C*_r(Γ) → E ⊗ C*_r(Γ)`, `x ⊗ d ↦ x ⊗ P_χ d`. -/
def characterIsometry (χ : Γ →* unitary ℂ) :
    CharacterTensor E χ →ₗᵢ[ℂ] DescendedModule (Γ := Γ) E :=
  InteriorModuleTensorFormCompletion.completedIsometry _ (characterBalanced χ)
    (characterBalanced_inner χ)

@[simp] theorem characterIsometry_mk (χ : Γ →* unitary ℂ) (x : E) (d : (GroupCrossed Γ)ᵐᵒᵖ) :
    characterIsometry χ (interiorModuleTensorMk _ x d) =
      KasparovDescent.mk (scalarAction Γ) E x
        (MulOpposite.op (characterProjection Γ χ * MulOpposite.unop d)) :=
  InteriorModuleTensorFormCompletion.completedIsometry_mk _ _ _ x d

theorem characterIsometry_inner (χ : Γ →* unitary ℂ) (u v : CharacterTensor E χ) :
    ⟪characterIsometry χ u, characterIsometry χ v⟫_((GroupCrossed Γ)ᵐᵒᵖ) =
      ⟪u, v⟫_((GroupCrossed Γ)ᵐᵒᵖ) :=
  InteriorModuleTensorFormCompletion.completedIsometry_inner _ _ _ u v

end Tensor

section Sum
variable {B M : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B]
  [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul Bᵐᵒᵖ M] [CStarModule Bᵐᵒᵖ M]

/-- Finite sums of adjointable maps are evaluated pointwise. -/
private theorem adjointable_sum_apply {ι : Type*} (s : Finset ι) (T : ι → AdjointableMap B M M)
    (u : M) : (∑ i ∈ s, T i) u = ∑ i ∈ s, T i u := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, AdjointableMap.coe_add_apply, ih]

end Sum

section Support
variable {Γ : Type} [Group Γ] [Fintype Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul ℂᵐᵒᵖ E]
  [CStarModule ℂᵐᵒᵖ E] [CompleteSpace E]

/-- The translation action of `Γ` on `C₀(pt)`. -/
abbrev pointAction (Γ : Type) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] :
    CStarAlgebraAction Γ C₀(FiniteGroupPoint.{0}, ℂ) := CZero.action Γ

/-- The constant function `z` on the point. -/
abbrev pointScalar (z : ℂ) : C₀(FiniteGroupPoint.{0}, ℂ) :=
  UnitPointCutoff.scalarToCZero FiniteGroupPoint.{0} z

/-- The averaging element as a sum of generators. -/
theorem averaging_eq_sum :
    FinitePointCutoff.averaging Γ = ∑ g : Γ, algebraicToReducedCrossed (pointAction Γ)
      (AlgebraicCrossedProduct.single (pointAction Γ) g
        (pointScalar ((Fintype.card Γ : ℂ)⁻¹))) := by
  unfold FinitePointCutoff.averaging
  rw [← map_sum]
  congr 1
  apply AlgebraicCrossedProduct.ext
  intro g
  rw [FinitePointCutoff.coeff_algebraicAveraging, AlgebraicCrossedProduct.coeff_sum,
    Finsupp.finsetSum_apply, Nat.card_eq_fintype_card]
  simp

/-- If `Γ` acts on `E` through `χ` and the point acts unitally, the averaging
element acts on the descended module as `1 ⊗ P_χ`. -/
theorem reducedSourceRepresentation_averaging_mk (χ : Γ →* unitary ℂ)
    (U : EquivariantHilbertModule (scalarAction Γ) E)
    (π : C₀(FiniteGroupPoint.{0}, ℂ) →⋆ₙₐ[ℂ] AdjointableMap ℂ E E)
    (hπ : ∀ g a, U.conjugateOperator g (π a) = π ((pointAction Γ).automorphism g a))
    (hU : ∀ g x, U.action g x = (χ g : ℂ) • x) (h1 : π (pointScalar 1) = 1)
    (x : E) (d : (GroupCrossed Γ)ᵐᵒᵖ) :
    KasparovDescent.reducedSourceRepresentation (scalarAction Γ) E (pointAction Γ) U π hπ
        (FinitePointCutoff.averaging Γ) (KasparovDescent.mk (scalarAction Γ) E x d) =
      KasparovDescent.mk (scalarAction Γ) E x (characterLeftMul χ d) := by
  have hscalar : pointScalar ((Fintype.card Γ : ℂ)⁻¹) =
      (Fintype.card Γ : ℂ)⁻¹ • pointScalar 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [averaging_eq_sum, map_sum, adjointable_sum_apply]
  simp only [KasparovDescent.reducedSourceRepresentation_single,
    KasparovDescent.sourceGenerator_mk, hU, leftRegular_eq_mul, hscalar, map_smul, h1,
    AdjointableMap.coe_smul_apply, AdjointableMap.one_apply, smul_smul]
  unfold KasparovDescent.mk
  simp only [LinearMap.map_smul₂, ← map_smul, ← map_sum]
  congr 1
  apply MulOpposite.unop_injective
  simp only [characterLeftMul_apply, characterProjection, Finset.unop_sum, MulOpposite.unop_smul,
    MulOpposite.unop_op, Finset.sum_mul, smul_mul_assoc, mul_comm]

end Support

section Range
variable {Γ : Type} [Group Γ] [Fintype Γ]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul ℂᵐᵒᵖ E]
  [CStarModule ℂᵐᵒᵖ E] [CompleteSpace E]
variable (χ : Γ →* unitary ℂ)
  (p : AdjointableMap (GroupCrossed Γ) (DescendedModule (Γ := Γ) E) (DescendedModule (Γ := Γ) E))

theorem characterTensor_clm_ext {M : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M]
    {L L' : CharacterTensor E χ →L[ℂ] M}
    (h : ∀ x d, L (interiorModuleTensorMk _ x d) = L' (interiorModuleTensorMk _ x d)) :
    L = L' :=
  ContinuousLinearMap.ext_on (interiorModuleTensor_span_dense _)
    (by rintro _ ⟨⟨x, d⟩, rfl⟩; exact h x d)

theorem characterLeftMul_idem (d : (GroupCrossed Γ)ᵐᵒᵖ) :
    characterLeftMul χ (characterLeftMul χ d) = characterLeftMul χ d := by
  rw [characterLeftMul_apply, characterLeftMul_apply, MulOpposite.unop_op, ← mul_assoc,
    (characterProjection_isStarProjection Γ χ).isIdempotentElem.eq]

/-- The support projection fixes the image of `E ⊗_{P_χ} C*_r(Γ)`. -/
theorem projection_characterIsometry
    (hp : ∀ x d, p (KasparovDescent.mk (scalarAction Γ) E x d) =
      KasparovDescent.mk (scalarAction Γ) E x (characterLeftMul χ d))
    (u : CharacterTensor E χ) :
    p (characterIsometry χ u) = characterIsometry χ u := by
  let L := (characterIsometry (E := E) χ).toContinuousLinearMap
  have h : p.toCLM.comp L = L := by
    apply ContinuousLinearMap.ext_on (interiorModuleTensor_span_dense _)
    rintro _ ⟨⟨x, d⟩, rfl⟩
    change p (characterIsometry χ (interiorModuleTensorMk _ x d)) =
      characterIsometry χ (interiorModuleTensorMk _ x d)
    rw [characterIsometry_mk]
    change p (KasparovDescent.mk (scalarAction Γ) E x (characterLeftMul χ d)) =
      KasparovDescent.mk (scalarAction Γ) E x (characterLeftMul χ d)
    rw [hp, characterLeftMul_idem]
  exact DFunLike.congr_fun h u

/-- Every fixed vector of the support projection lies in the image of
`E ⊗_{P_χ} C*_r(Γ)`: the image is closed and contains `p` of every elementary
tensor. -/
theorem mem_range_characterIsometry
    (hp : ∀ x d, p (KasparovDescent.mk (scalarAction Γ) E x d) =
      KasparovDescent.mk (scalarAction Γ) E x (characterLeftMul χ d))
    (w : DescendedModule (Γ := Γ) E) (hw : p w = w) :
    ∃ u, characterIsometry χ u = w := by
  let R := LinearMap.range (characterIsometry (E := E) χ).toLinearMap
  have hclosed : IsClosed (R : Set (DescendedModule (Γ := Γ) E)) :=
    (characterIsometry (E := E) χ).isometry.isClosedEmbedding.isClosed_range
  let K : Submodule ℂ (DescendedModule (Γ := Γ) E) := R.comap p.toCLM.toLinearMap
  have hK : IsClosed (K : Set (DescendedModule (Γ := Γ) E)) :=
    hclosed.preimage p.toCLM.continuous
  have hspan : Submodule.span ℂ (Set.range fun q : E × (GroupCrossed Γ)ᵐᵒᵖ =>
      interiorModuleTensorMk (KasparovDescent.coefficientRepresentation (scalarAction Γ))
        q.1 q.2) ≤ K := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨x, d⟩, rfl⟩
    refine ⟨interiorModuleTensorMk _ x d, ?_⟩
    change characterIsometry χ (interiorModuleTensorMk _ x d) =
      p (KasparovDescent.mk (scalarAction Γ) E x d)
    rw [characterIsometry_mk, hp]
    rfl
  have hw' : w ∈ K := hK.closure_subset_iff.mpr hspan (interiorModuleTensor_span_dense _ w)
  obtain ⟨u, hu⟩ := hw'
  exact ⟨u, hu.trans hw⟩

/-- The isometry, corestricted to the range of the support projection. -/
def characterRangeIsometry
    (hp : ∀ x d, p (KasparovDescent.mk (scalarAction Γ) E x d) =
      KasparovDescent.mk (scalarAction Γ) E x (characterLeftMul χ d)) :
    CharacterTensor E χ →ₗᵢ[ℂ] ProjectionModule p where
  toLinearMap := (characterIsometry (E := E) χ).toLinearMap.codRestrict
    (projectionFixedSubmodule p) (projection_characterIsometry χ p hp)
  norm_map' u := (characterIsometry (E := E) χ).norm_map u

@[simp] theorem characterRangeIsometry_coe
    (hp : ∀ x d, p (KasparovDescent.mk (scalarAction Γ) E x d) =
      KasparovDescent.mk (scalarAction Γ) E x (characterLeftMul χ d))
    (u : CharacterTensor E χ) :
    ((characterRangeIsometry χ p hp u : ProjectionModule p) : DescendedModule (Γ := Γ) E) =
      characterIsometry χ u := rfl

theorem characterRangeIsometry_surjective
    (hp : ∀ x d, p (KasparovDescent.mk (scalarAction Γ) E x d) =
      KasparovDescent.mk (scalarAction Γ) E x (characterLeftMul χ d)) :
    Function.Surjective (characterRangeIsometry χ p hp) := by
  intro y
  obtain ⟨u, hu⟩ := mem_range_characterIsometry χ p hp (y : DescendedModule (Γ := Γ) E) y.property
  refine ⟨u, Subtype.ext ?_⟩
  rw [characterRangeIsometry_coe]
  exact hu

/-- `E ⊗_{P_χ} C*_r(Γ)` is unitarily the range of the support projection. -/
def characterRangeEquiv
    (hp : ∀ x d, p (KasparovDescent.mk (scalarAction Γ) E x d) =
      KasparovDescent.mk (scalarAction Γ) E x (characterLeftMul χ d)) :
    HilbertModuleEquiv (GroupCrossed Γ) (CharacterTensor E χ) (ProjectionModule p) where
  linearIsometryEquiv := LinearIsometryEquiv.ofSurjective (characterRangeIsometry χ p hp)
    (characterRangeIsometry_surjective χ p hp)
  inner_map u v := characterIsometry_inner χ u v

@[simp] theorem characterRangeEquiv_coe
    (hp : ∀ x d, p (KasparovDescent.mk (scalarAction Γ) E x d) =
      KasparovDescent.mk (scalarAction Γ) E x (characterLeftMul χ d))
    (u : CharacterTensor E χ) :
    ((characterRangeEquiv χ p hp u : ProjectionModule p) : DescendedModule (Γ := Γ) E) =
      characterIsometry χ u := rfl

end Range

end BC4lean.KKTheory.FinitePointCharacterTensor

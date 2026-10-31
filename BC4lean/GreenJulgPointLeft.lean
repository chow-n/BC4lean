import BC4lean.GreenJulgPoint
import BC4lean.OrderTwoEigenSplitInvariance

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The left round trip of the point Green–Julg map

Let `Γ` be finite with `n = |Γ|`, `Cr = ℂ ⋊_r Γ` with regular unitaries `λ_g` and trace `τ`, and
let `Ψ_p : KK^Γ_p(C₀(pt), ℂ) → KK_p(ℂ, Cr)` be descent followed by the cutoff product
(`pointGreenJulgHom`, from `GreenJulgPoint`). Julg's inverse is `L_p y = ev^*(infl y · [ℓ²Γ])`
(`GreenJulgCorrespondence.greenJulgInverse`). This file proves `L_p ∘ Ψ_p = id` for both parities
(`greenJulgInverse_pointGreenJulgHom`).

Every class has a representative `c = (E, U, π, F)` on which the point acts unitally and whose
operator commutes with `U` (`mk_unitalCycle`). For such `c`, `Ψ_p [c]` is the class of the range
cycle on `range(Q)`, `Q = n⁻¹ ∑_g U_g ⊗ λ_g` (`FinitePointDescentRange`), and `L_p` of that is the
class of the tensor cycle on `range(Q) ⊗_{Cr} ℓ²Γ` (`GreenJulgRepresentative`;
`GreenJulgPoint.evenInverseCycle`). The map
`W x = √n · Q(x ⊗ λ_e) ⊗ δ_e` is a unitary `E → range(Q) ⊗_{Cr} ℓ²Γ` that intertwines the
gradings, the actions, the representations and the operators (`leftIso`, `oddLeftIso`).

The unitary is built once, for any Hilbert `Cr`-module `M` and complex-linear `R : E → M` with
* `n τ⟪R x, R y⟫ = ⟪x, y⟫` (here: `⟪Q a, Q b⟫ = ⟪a, Q b⟫ = n⁻¹ ∑_g ⟪x, U_g y⟫ λ_g`, and
  `τ(λ_g) = [g = e]`);
* `R x · λ_k = R(U_k⁻¹ x)` (here: `Q(x ⊗ λ_k) = Q(U_k⁻¹ x ⊗ λ_e)`), so that
  `R x ⊗ δ_k = R x λ_k ⊗ δ_e = R(U_k⁻¹ x) ⊗ δ_e`;
* the vectors `R x · a` span a dense subspace of `M` (here: `Q(x ⊗ a) = Q(x ⊗ λ_e) a`).

The first makes `W x = √n · R x ⊗ δ_e` isometric, the other two make it onto: its closed range
contains every `R x ⊗ δ_k`, hence (`ℓ²Γ = span δ_k`) every `R x ⊗ ξ`, hence every `R x a ⊗ ξ =
R x ⊗ λ(a) ξ`, hence every `v ⊗ ξ`. Working with an abstract `M` keeps the elaborator away from
the range module until the single specialisation `M = range(Q)`. -/

noncomputable section
namespace BC4lean.KKTheory.GreenJulgPoint
open BC4lean.ProperActions BC4lean.OperatorKTheory BC4lean.Chapter8Examples
open KKTheory.GroupUniverseParityGroup KKTheory.GroupUniverseParityFunctoriality
open KKTheory.FinitePointCharacterTensor KKTheory.FinitePointCompressedDescent
open KKTheory.FinitePointDescentRange KKTheory.GreenJulgCorrespondence
open KKTheory.GreenJulgRepresentative
open scoped ZeroAtInfty ComplexOrder KasparovDescent InnerProductSpace

/-! ## The unitary `W : E → M ⊗_{Cr} ℓ²Γ` -/

section Unitary
variable {Γ : Type} [Group Γ] [Fintype Γ]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul ℂᵐᵒᵖ E]
  [CStarModule ℂᵐᵒᵖ E] [CompleteSpace E]
variable {M : Type} [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul (Cr Γ)ᵐᵒᵖ M]
  [CStarModule (Cr Γ)ᵐᵒᵖ M] [CompleteSpace M]
variable (R : E →ₗ[ℂ] M)
  (hR : ∀ x y, (Fintype.card Γ : ℂ) * scalarTrace (MulOpposite.unop ⟪R x, R y⟫_((Cr Γ)ᵐᵒᵖ)) =
    MulOpposite.unop ⟪x, y⟫_(ℂᵐᵒᵖ))
  (U : EquivariantHilbertModule (scalarAction Γ) E)
  (hU : ∀ (k : Γ) x, MulOpposite.op (scalarRegular Γ k) • R x = R (U.action k⁻¹ x))
  (hD : ∀ v : M, v ∈ (Submodule.span ℂ (Set.range fun q : E × Cr Γ =>
    MulOpposite.op q.2 • R q.1)).topologicalClosure)

variable (Γ) in
/-- `√n`. -/
abbrev rootCard : ℂ := ((Real.sqrt (Fintype.card Γ) : ℝ) : ℂ)

omit [Group Γ] in
theorem star_rootCard_mul : star (rootCard Γ) * rootCard Γ = Fintype.card Γ := by
  rw [rootCard, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]

theorem rootCard_ne_zero : rootCard Γ ≠ 0 := by
  rw [rootCard, Complex.ofReal_ne_zero]
  exact (Real.sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)).ne'

variable (Γ) in
/-- `W x = √n · R x ⊗ δ_e`. -/
def leftLinear : E →ₗ[ℂ] RegularTensor Γ M := rootCard Γ • (tensorDelta Γ M).comp R

omit [SMul ℂᵐᵒᵖ E] [CStarModule ℂᵐᵒᵖ E] [CompleteSpace E] in
theorem leftLinear_apply (x : E) : leftLinear Γ R x = rootCard Γ • tensorDelta Γ M (R x) := rfl

omit [CompleteSpace E] in
include hR in
/-- `⟪W x, W y⟫ = n τ⟪R x, R y⟫ = ⟪x, y⟫`. -/
theorem inner_leftLinear (x y : E) :
    ⟪leftLinear Γ R x, leftLinear Γ R y⟫_(ℂᵐᵒᵖ) = ⟪x, y⟫_(ℂᵐᵒᵖ) := by
  rw [leftLinear_apply, leftLinear_apply,
    CStarModule.inner_smul_left_complex (A := ℂᵐᵒᵖ) (E := RegularTensor Γ M),
    CStarModule.inner_smul_right_complex (A := ℂᵐᵒᵖ) (E := RegularTensor Γ M), inner_tensorDelta,
    smul_smul, star_rootCard_mul]
  apply MulOpposite.unop_injective
  rw [MulOpposite.unop_smul, MulOpposite.unop_op, smul_eq_mul, hR]

variable (Γ) in
/-- `W` as a linear isometry. -/
def leftIsometry : E →ₗᵢ[ℂ] RegularTensor Γ M where
  toLinearMap := leftLinear Γ R
  norm_map' x := by
    rw [CStarModule.norm_eq_sqrt_norm_inner_self (A := ℂᵐᵒᵖ) (leftLinear Γ R x),
      CStarModule.norm_eq_sqrt_norm_inner_self (A := ℂᵐᵒᵖ) x]
    exact congrArg (fun z => Real.sqrt ‖z‖) (inner_leftLinear R hR x x)

omit [Fintype Γ] [CompleteSpace E] in
include hU in
/-- `R x ⊗ δ_k = R(U_k⁻¹ x) ⊗ δ_e`. -/
theorem mk_delta_left (x : E) (k : Γ) :
    interiorModuleTensorMk (regularRep Γ) (R x) (delta Γ k) =
      tensorDelta Γ M (R (U.action k⁻¹ x)) := by
  rw [mk_delta, hU]

omit [Fintype Γ] in
/-- `v ↦ v ⊗ ξ` is continuous. -/
theorem continuous_mk_flip (ξ : L2 Γ) :
    Continuous ((interiorModuleTensorMk (E := M) (regularRep Γ)).flip ξ) := by
  refine AddMonoidHomClass.continuous_of_bound _ ‖ξ‖ fun v => ?_
  rw [LinearMap.flip_apply, mul_comm]
  exact interiorModuleTensorMk_norm_le (regularRep Γ) v ξ

include hU hD in
/-- `W` is onto. -/
theorem leftIsometry_surjective : Function.Surjective (leftIsometry Γ R hR) := by
  let S := LinearMap.range (leftIsometry Γ R hR).toLinearMap
  have hS : IsClosed (S : Set (RegularTensor Γ M)) :=
    (leftIsometry Γ R hR).isometry.isClosedEmbedding.isClosed_range
  have hA : ∀ x k, interiorModuleTensorMk (regularRep Γ) (R x) (delta Γ k) ∈ S := by
    intro x k
    rw [mk_delta_left R U hU]
    refine ⟨(rootCard Γ)⁻¹ • U.action k⁻¹ x, ?_⟩
    change leftLinear Γ R _ = _
    rw [map_smul, leftLinear_apply, smul_smul, inv_mul_cancel₀ rootCard_ne_zero, one_smul]
  have hB : ∀ x ξ, interiorModuleTensorMk (regularRep Γ) (R x) ξ ∈ S := by
    intro x ξ
    rw [eq_sum_delta ξ, map_sum]
    exact S.sum_mem fun k _ => by rw [map_smul]; exact S.smul_mem _ (hA x k)
  let T : Submodule ℂ M :=
    ⨅ ξ : L2 Γ, S.comap ((interiorModuleTensorMk (E := M) (regularRep Γ)).flip ξ)
  have hT : IsClosed (T : Set M) := by
    simp only [T, Submodule.coe_iInf]
    exact isClosed_iInter fun ξ => hS.preimage (continuous_mk_flip ξ)
  have hspan : Submodule.span ℂ (Set.range fun q : E × Cr Γ => MulOpposite.op q.2 • R q.1) ≤ T := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨x, a⟩, rfl⟩
    change MulOpposite.op a • R x ∈ T
    rw [Submodule.mem_iInf]
    intro ξ
    rw [Submodule.mem_comap, LinearMap.flip_apply, interiorModuleTensorMk_balance]
    exact hB x _
  have hM : ∀ v : M, v ∈ T := fun v => Submodule.topologicalClosure_minimal _ hspan hT (hD v)
  have hspan' : Submodule.span ℂ (Set.range fun q : M × L2 Γ =>
      interiorModuleTensorMk (regularRep Γ) q.1 q.2) ≤ S := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨v, ξ⟩, rfl⟩
    exact (Submodule.mem_iInf _).mp (hM v) ξ
  intro t
  exact hS.closure_subset_iff.mpr hspan' (interiorModuleTensor_span_dense _ t)

variable (Γ) in
/-- **The unitary `W : E ≅ M ⊗_{Cr} ℓ²Γ`**, `W x = √n · R x ⊗ δ_e`. -/
def leftEquiv : HilbertModuleEquiv ℂ E (RegularTensor Γ M) where
  linearIsometryEquiv := LinearIsometryEquiv.ofSurjective (leftIsometry Γ R hR)
    (leftIsometry_surjective R hR U hU hD)
  inner_map x y := inner_leftLinear R hR x y

theorem leftEquiv_apply (x : E) :
    leftEquiv Γ R hR U hU hD x = rootCard Γ • tensorDelta Γ M (R x) := rfl

end Unitary

/-! ## The range of `Q = n⁻¹ ∑_g U_g ⊗ λ_g` -/

section Range
variable {Γ : Type} [Group Γ] [Fintype Γ]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul ℂᵐᵒᵖ E]
  [CStarModule ℂᵐᵒᵖ E] [CompleteSpace E]
variable (U : EquivariantHilbertModule (scalarAction Γ) E)
  (p : AdjointableMap (GroupCrossed Γ) (DescendedModule (Γ := Γ) E) (DescendedModule (Γ := Γ) E))
  (hP : IsStarProjection p)
  (hp : ∀ x d, p (KasparovDescent.mk (scalarAction Γ) E x d) =
    ∑ g : Γ, (Fintype.card Γ : ℂ)⁻¹ • KasparovDescent.mk (scalarAction Γ) E
      (U.action g x) (MulOpposite.op (regular Γ g * MulOpposite.unop d)))

variable (Γ) in
/-- `λ_e`, as a vector of the standard module. -/
abbrev unitVector : (GroupCrossed Γ)ᵐᵒᵖ := MulOpposite.op (regular Γ 1)

/-- `x ↦ Q(x ⊗ λ_e)`, into the range of `Q`. -/
def rangeVector : E →ₗ[ℂ] ProjectionModule p :=
  ((projectionCorestrictCLM p hP).comp
    (interiorModuleTensorLeftCLM (KasparovDescent.coefficientRepresentation (scalarAction Γ))
      (unitVector Γ))).toLinearMap

omit [Fintype Γ] in
@[simp] theorem rangeVector_coe (x : E) :
    ((rangeVector p hP x : ProjectionModule p) : DescendedModule (Γ := Γ) E) =
      p (KasparovDescent.mk (scalarAction Γ) E x (unitVector Γ)) := rfl

omit [Fintype Γ] in
theorem regular_eq_scalarRegular (g : Γ) : regular Γ g = scalarRegular Γ g := rfl

omit [Fintype Γ] in
/-- Scalar coefficients act on the reduced group algebra by scalar multiplication. -/
theorem coefficient_mul (z : ℂ) (a : GroupCrossed Γ) :
    coefficientToReducedCrossed (scalarAction Γ) z * a = z • a := by
  apply Subtype.ext
  change reducedCrossedCoefficient (scalarAction Γ) z * (a : AdjointableMap ℂ
    (ReducedCrossedHilbertModule ℂ Γ) (ReducedCrossedHilbertModule ℂ Γ)) = z • (a : _)
  rw [reducedCrossedCoefficient_scalar, smul_mul_assoc, one_mul]

omit [Fintype Γ] in
include hP in
/-- `⟪Q a, Q b⟫ = ⟪a, Q b⟫`. -/
theorem inner_projection (a b : DescendedModule (Γ := Γ) E) :
    ⟪p a, p b⟫_((GroupCrossed Γ)ᵐᵒᵖ) = ⟪a, p b⟫_((GroupCrossed Γ)ᵐᵒᵖ) := by
  rw [p.adjoint_identity]
  congr 1
  have h : p.adjoint * p = p := by
    have hs : p.adjoint = p := hP.isSelfAdjoint.star_eq
    rw [hs, hP.isIdempotentElem.eq]
  exact congrArg (fun T : AdjointableMap (GroupCrossed Γ) _ _ => T b) h

omit [Fintype Γ] in
/-- `⟪x ⊗ λ_e, y ⊗ λ_g⟫ = ⟪x, y⟫ λ_g`. -/
theorem inner_mk_unitVector (x y : E) (g : Γ) :
    ⟪KasparovDescent.mk (scalarAction Γ) E x (unitVector Γ),
      KasparovDescent.mk (scalarAction Γ) E y
        (MulOpposite.op (regular Γ g * MulOpposite.unop (unitVector Γ)))⟫_((GroupCrossed Γ)ᵐᵒᵖ) =
      MulOpposite.op (MulOpposite.unop ⟪x, y⟫_(ℂᵐᵒᵖ) • scalarRegular Γ g) := by
  rw [KasparovDescent.mk_inner, MulOpposite.unop_op, MulOpposite.unop_op, regular_mul, mul_one,
    star_regular, inv_one, coefficient_mul, regular_eq_scalarRegular, regular_eq_scalarRegular,
    scalarRegular_one_mul]

include hP hp in
/-- `n τ⟪Q(x ⊗ λ_e), Q(y ⊗ λ_e)⟫ = ⟪x, y⟫`. -/
theorem trace_inner_rangeVector (x y : E) :
    (Fintype.card Γ : ℂ) * scalarTrace (MulOpposite.unop
      ⟪rangeVector p hP x, rangeVector p hP y⟫_((Cr Γ)ᵐᵒᵖ)) = MulOpposite.unop ⟪x, y⟫_(ℂᵐᵒᵖ) := by
  classical
  rw [projectionModule_inner, rangeVector_coe, rangeVector_coe, inner_projection p hP, hp,
    CStarModule.inner_sum_right (A := (GroupCrossed Γ)ᵐᵒᵖ) (E := DescendedModule (Γ := Γ) E)]
  simp only [CStarModule.inner_smul_right_complex (A := (GroupCrossed Γ)ᵐᵒᵖ)
      (E := DescendedModule (Γ := Γ) E), inner_mk_unitVector, ← MulOpposite.op_smul,
    ← Finset.op_sum]
  rw [MulOpposite.unop_op, map_sum]
  simp only [map_smul, map_smul, scalarTrace_scalarRegular, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul, map_one]
  rfl

include hp in
/-- `Q(x ⊗ λ_k) = Q(U_k⁻¹ x ⊗ λ_e)`. -/
theorem projection_mk_regular (x : E) (k : Γ) :
    p (KasparovDescent.mk (scalarAction Γ) E x (MulOpposite.op (regular Γ k))) =
      p (KasparovDescent.mk (scalarAction Γ) E (U.action k⁻¹ x) (unitVector Γ)) := by
  rw [hp, hp]
  refine Fintype.sum_equiv (Equiv.mulRight k) _ _ (fun g => ?_)
  simp only [Equiv.coe_mulRight, MulOpposite.unop_op, regular_mul, mul_one, U.mul_apply,
    U.apply_inv_apply]

omit [Fintype Γ] in
/-- In the standard module, `d = λ_e d`. -/
theorem smul_unitVector (d : (GroupCrossed Γ)ᵐᵒᵖ) : d • unitVector Γ = d := by
  apply MulOpposite.unop_injective
  rw [smul_eq_mul, MulOpposite.unop_mul, MulOpposite.unop_op, regular_eq_scalarRegular]
  exact scalarRegular_one_mul _

omit [Fintype Γ] in
/-- `x ⊗ d = (x ⊗ λ_e) d`. -/
theorem mk_eq_smul (x : E) (d : (GroupCrossed Γ)ᵐᵒᵖ) :
    KasparovDescent.mk (scalarAction Γ) E x d =
      d • KasparovDescent.mk (scalarAction Γ) E x (unitVector Γ) := by
  unfold KasparovDescent.mk
  simp only [interiorModuleTensor_smul_mk, smul_unitVector]

include hp in
/-- `Q(x ⊗ λ_e) λ_k = Q(U_k⁻¹ x ⊗ λ_e)`. -/
theorem op_smul_rangeVector (k : Γ) (x : E) :
    MulOpposite.op (scalarRegular Γ k) • rangeVector p hP x = rangeVector p hP (U.action k⁻¹ x) := by
  apply Subtype.ext
  simp only [projectionModule_coe_op_smul, rangeVector_coe, ← p.map_op_smul]
  exact (congrArg p (mk_eq_smul x (MulOpposite.op (regular Γ k)))).symm.trans
    (projection_mk_regular U p hp x k)

omit [Fintype Γ] in
/-- The vectors `Q(x ⊗ λ_e) a` span a dense subspace of the range of `Q`. -/
theorem rangeVector_dense (v : ProjectionModule p) :
    v ∈ (Submodule.span ℂ (Set.range fun q : E × Cr Γ =>
      MulOpposite.op q.2 • rangeVector p hP q.1)).topologicalClosure := by
  set N := (Submodule.span ℂ (Set.range fun q : E × Cr Γ =>
    MulOpposite.op q.2 • rangeVector p hP q.1)).topologicalClosure
  let K : Submodule ℂ (DescendedModule (Γ := Γ) E) :=
    N.comap (projectionCorestrictCLM p hP).toLinearMap
  have hN : IsClosed (N : Set (ProjectionModule p)) := Submodule.isClosed_topologicalClosure _
  have hK : IsClosed (K : Set (DescendedModule (Γ := Γ) E)) :=
    hN.preimage (projectionCorestrictCLM p hP).continuous
  have hspan : Submodule.span ℂ (Set.range fun q : E × (GroupCrossed Γ)ᵐᵒᵖ =>
      interiorModuleTensorMk (KasparovDescent.coefficientRepresentation (scalarAction Γ))
        q.1 q.2) ≤ K := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨x, d⟩, rfl⟩
    change projectionCorestrictCLM p hP (KasparovDescent.mk (scalarAction Γ) E x d) ∈ N
    simp only [mk_eq_smul x d, projectionCorestrictCLM_op_smul]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(x, MulOpposite.unop d), rfl⟩)
  have hv : projectionCorestrictCLM p hP (v : DescendedModule (Γ := Γ) E) = v :=
    Subtype.ext v.property
  rw [← hv]
  exact hK.closure_subset_iff.mpr hspan (interiorModuleTensor_span_dense _ _)

include hp in
/-- An operator `A` on `E` commuting with `U`, and an operator `Ã` on `E ⊗ Cr` acting as
`A ⊗ 1`: then `Ã Q(x ⊗ λ_e) = Q(A x ⊗ λ_e)`. -/
theorem commute_projection (A : E →ₗ[ℂ] E)
    (Ã : DescendedModule (Γ := Γ) E →ₗ[ℂ] DescendedModule (Γ := Γ) E)
    (hÃ : ∀ x d, Ã (KasparovDescent.mk (scalarAction Γ) E x d) =
      KasparovDescent.mk (scalarAction Γ) E (A x) d)
    (hA : ∀ g x, A (U.action g x) = U.action g (A x)) (x : E) :
    Ã (p (KasparovDescent.mk (scalarAction Γ) E x (unitVector Γ))) =
      p (KasparovDescent.mk (scalarAction Γ) E (A x) (unitVector Γ)) := by
  rw [hp, hp, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smul, hÃ, hA]

variable (Γ) in
/-- `W = √n · Q(· ⊗ λ_e) ⊗ δ_e : E ≅ range(Q) ⊗_{Cr} ℓ²Γ`. -/
abbrev rangeLeftEquiv : HilbertModuleEquiv ℂ E (RegularTensor Γ (ProjectionModule p)) :=
  leftEquiv Γ (rangeVector p hP) (trace_inner_rangeVector U p hP hp) U (op_smul_rangeVector U p hP hp)
    (rangeVector_dense p hP)

end Range

/-- `z ↦ z · 1` inverts evaluation at the point. -/
theorem pointScalar_pointEval (a : C₀(FiniteGroupPoint.{0}, ℂ)) : pointScalar (pointEval a) = a := by
  ext y
  exact congrArg a (Subsingleton.elim _ _)

/-! ## Generic cycle isomorphisms

`W` is an isomorphism of a cycle `c` on `E` with the representative `evenInverseCycle Γ d` of
`L_0 [d]` for any cycle `d` on an abstract `M` that `R` intertwines with `c`. Stating this over an
abstract `M` keeps every rewrite at generic instance terms (as in `GreenJulgPoint`); rewriting directly at
`M = range(Q)` times out in `isDefEq`. -/

section GenericIso
variable {Γ : Type} [Group Γ] [Fintype Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul ℂᵐᵒᵖ E]
  [CStarModule ℂᵐᵒᵖ E] [CompleteSpace E]
variable {M : Type} [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul (Cr Γ)ᵐᵒᵖ M]
  [CStarModule (Cr Γ)ᵐᵒᵖ M] [CompleteSpace M]
variable (R : E →ₗ[ℂ] M)
  (hR : ∀ x y, (Fintype.card Γ : ℂ) * scalarTrace (MulOpposite.unop ⟪R x, R y⟫_((Cr Γ)ᵐᵒᵖ)) =
    MulOpposite.unop ⟪x, y⟫_(ℂᵐᵒᵖ))
  (hD : ∀ v : M, v ∈ (Submodule.span ℂ (Set.range fun q : E × Cr Γ =>
    MulOpposite.op q.2 • R q.1)).topologicalClosure)

section Even
variable (d : KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ) (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (Cr Γ)) M)

theorem evenInverseCycle_representation_delta (hrep : ∀ z m, d.representation z m = z • m)
    (a : C₀(FiniteGroupPoint.{0}, ℂ)) (m : M) :
    (evenInverseCycle Γ d).representation a (tensorDelta Γ M m) =
      pointEval a • tensorDelta Γ M m := by
  rw [evenSourcePullback_representation, evenTensorCycle_representation, tensorDelta_apply,
    interiorModuleTensorOperator_mk,
    show (inflateEven Γ d).representation (pointEval a) m = pointEval a • m from hrep _ m]
  exact LinearMap.map_smul₂ _ _ _ _

theorem evenInverseCycle_operator_delta (m : M) :
    (evenInverseCycle Γ d).operator (tensorDelta Γ M m) = tensorDelta Γ M (d.operator m) := by
  rw [evenSourcePullback_operator, evenTensorCycle_operator, tensorDelta_apply, tensorDelta_apply,
    interiorModuleTensorOperator_mk]
  rfl

variable (c : KasparovCycle (pointAction Γ) (scalarAction Γ) E)
  (hU : ∀ (k : Γ) x, MulOpposite.op (scalarRegular Γ k) • R x = R (c.groupAction.action k⁻¹ x))
  (hrep : ∀ z m, d.representation z m = z • m)
  (hπ : ∀ a x, c.representation a x = pointEval a • x)
  (hγ : ∀ x, R (c.grading.grading x) = d.grading.grading (R x))
  (hF : ∀ x, R (c.operator x) = d.operator (R x))

include hrep hπ hγ hF in
/-- **`W` on even cycles.** If `R` intertwines `c` with `d`, then `W` is an isomorphism of `c`
with the representative `evenInverseCycle Γ d` of `L_0 [d]`. -/
def evenLeftIso : KasparovCycleIso c (evenInverseCycle Γ d) where
  moduleEquiv := leftEquiv Γ R hR c.groupAction hU hD
  grading_intertwine x := by
    rw [leftEquiv_apply, leftEquiv_apply, hγ, ← evenInverseCycle_grading d, map_smul]
  action_intertwine g x := by
    rw [leftEquiv_apply, leftEquiv_apply, map_smul, evenInverseCycle_action d, hU, inv_inv]
  representation_intertwine a x := by
    rw [hπ, map_smul, leftEquiv_apply, map_smul, evenInverseCycle_representation_delta d hrep,
      smul_comm]
  operator_intertwine x := by
    simp only [leftEquiv_apply, hF, map_smul, evenInverseCycle_operator_delta d]

end Even

section Odd
variable (d : OddKasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ) (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (Cr Γ)) M)

theorem oddInverseCycle_representation_delta (hrep : ∀ z m, d.representation z m = z • m)
    (a : C₀(FiniteGroupPoint.{0}, ℂ)) (m : M) :
    (oddInverseCycle Γ d).representation a (tensorDelta Γ M m) =
      pointEval a • tensorDelta Γ M m := by
  rw [oddSourcePullback_representation, oddTensorCycle_representation, tensorDelta_apply,
    interiorModuleTensorOperator_mk,
    show (inflateOdd Γ d).representation (pointEval a) m = pointEval a • m from hrep _ m]
  exact LinearMap.map_smul₂ _ _ _ _

theorem oddInverseCycle_operator_delta (m : M) :
    (oddInverseCycle Γ d).operator (tensorDelta Γ M m) = tensorDelta Γ M (d.operator m) := by
  have hop : (oddInverseCycle Γ d).operator = interiorModuleTensorOperator (regularRep Γ) d.operator :=
    oddTensorCycle_operator (rightRegular Γ) (regularRep Γ) (regularRep_equivariant Γ)
      (regularRep_isModuleCompact Γ) (isCountablyGenerated Γ) (inflateOdd Γ d)
  rw [hop, tensorDelta_apply, tensorDelta_apply, interiorModuleTensorOperator_mk]

variable (c : OddKasparovCycle (pointAction Γ) (scalarAction Γ) E)
  (hU : ∀ (k : Γ) x, MulOpposite.op (scalarRegular Γ k) • R x = R (c.groupAction.action k⁻¹ x))
  (hrep : ∀ z m, d.representation z m = z • m)
  (hπ : ∀ a x, c.representation a x = pointEval a • x)
  (hF : ∀ x, R (c.operator x) = d.operator (R x))

include hrep hπ hF in
/-- **`W` on odd cycles.** -/
def oddLeftIsoOf : OddKasparovCycleIso c (oddInverseCycle Γ d) where
  moduleEquiv := leftEquiv Γ R hR c.groupAction hU hD
  action_intertwine g x := by
    rw [leftEquiv_apply, leftEquiv_apply, map_smul, oddInverseCycle_action d, hU, inv_inv]
  representation_intertwine a x := by
    rw [hπ, map_smul, leftEquiv_apply, map_smul, oddInverseCycle_representation_delta d hrep,
      smul_comm]
  operator_intertwine x := by
    rw [leftEquiv_apply, leftEquiv_apply, hF, map_smul, oddInverseCycle_operator_delta d]

end Odd

end GenericIso

/-! ## Even cycles: `W` is a whole-cycle isomorphism -/

section EvenCycle
variable {Γ : Type} [Group Γ] [Fintype Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul ℂᵐᵒᵖ E]
  [CStarModule ℂᵐᵒᵖ E] [CompleteSpace E]
variable (c : KasparovCycle (pointAction Γ) (scalarAction Γ) E)
  (h1 : c.representation (pointScalar 1) = 1)

include h1 in
/-- With the point acting unitally, the support projection of the pulled-back descent is
`Q = n⁻¹ ∑_g U_g ⊗ λ_g`. -/
theorem support_mk_of_unital (x : E) (d : (GroupCrossed Γ)ᵐᵒᵖ) :
    (pulledDescent c).scalarSupportProjection (KasparovDescent.mk (scalarAction Γ) E x d) =
      ∑ g : Γ, (Fintype.card Γ : ℂ)⁻¹ • KasparovDescent.mk (scalarAction Γ) E
        (c.groupAction.action g x) (MulOpposite.op (regular Γ g * MulOpposite.unop d)) := by
  rw [FinitePointDescentRange.pulledDescent_support_mk, h1]
  rfl

/-- The vector `Q(x ⊗ λ_e)` of the range cycle. -/
abbrev leftVector (x : E) : ProjectionModule (pulledDescent c).scalarSupportProjection :=
  rangeVector (pulledDescent c).scalarSupportProjection
    (pulledDescent c).scalarSupportProjection_isStarProjection x

include h1 in
/-- `Q` commutes with the grading. -/
theorem leftVector_grading (x : E) :
    leftVector c (c.grading.grading x) = (rangeCycle c).grading.grading (leftVector c x) := by
  apply Subtype.ext
  refine Eq.trans ?_ (KasparovCycle.scalarSupportGrading_coe _ _).symm
  change (pulledDescent c).scalarSupportProjection
      (KasparovDescent.mk (scalarAction Γ) E (c.grading.grading x) (unitVector Γ)) =
    (KasparovDescent.ordinaryModuleGrading (scalarAction Γ) c.grading).grading
      ((pulledDescent c).scalarSupportProjection
        (KasparovDescent.mk (scalarAction Γ) E x (unitVector Γ)))
  exact (commute_projection c.groupAction _ (support_mk_of_unital c h1)
    c.grading.grading.toLinearEquiv.toLinearMap
    (KasparovDescent.ordinaryModuleGrading (scalarAction Γ) c.grading).grading.toLinearEquiv.toLinearMap
    (fun x d => KasparovDescent.ordinaryModuleGrading_mk _ c.grading x d)
    (fun g x => (c.grading_preserved g x).symm) x).symm

omit [Fintype Γ] in
include h1 in
/-- The point acts on `E` through evaluation. -/
theorem representation_eq_smul (a : C₀(FiniteGroupPoint.{0}, ℂ)) (x : E) :
    c.representation a x = pointEval a • x := by
  have ha : a = pointEval a • pointScalar 1 := by
    conv_lhs => rw [← pointScalar_pointEval a]
    rw [← map_smul, smul_eq_mul, mul_one]
  have h : c.representation a = pointEval a • c.representation (pointScalar 1) := by
    rw [← map_smul]; exact congrArg _ ha
  rw [h, h1, AdjointableMap.coe_smul_apply, AdjointableMap.one_apply]

variable (hF : ∀ g x, c.operator (c.groupAction.action g x) = c.groupAction.action g (c.operator x))

include h1 hF in
/-- `Q` commutes with the operator. -/
theorem leftVector_operator (x : E) :
    (rangeCycle c).operator (leftVector c x) = leftVector c (c.operator x) := by
  apply Subtype.ext
  refine (KasparovCycle.scalarSupportCompression_coe _ _).trans ?_
  set D := pulledDescent c
  have hP := D.scalarSupportProjection_isStarProjection
  have hQ : ∀ y, D.scalarSupportProjection (D.scalarSupportProjection y) =
      D.scalarSupportProjection y :=
    fun y => congrArg (fun T : AdjointableMap _ _ _ => T y) hP.isIdempotentElem.eq
  have hv : D.scalarSupportProjection (leftVector c x : DescendedModule (Γ := Γ) E) =
      leftVector c x := hQ _
  have h2 : D.scalarSupportBlockOperator (leftVector c x : DescendedModule (Γ := Γ) E) =
      D.scalarSupportProjection (D.operator (leftVector c x : DescendedModule (Γ := Γ) E)) := by
    unfold KasparovCycle.scalarSupportBlockOperator
    simp only [AdjointableMap.coe_add_apply, AdjointableMap.mul_apply,
      AdjointableMap.coe_sub_apply, AdjointableMap.one_apply, hv, sub_self, map_zero, add_zero]
  have hF' : KasparovDescent.operatorHom (scalarAction Γ) E c.operator
      (D.scalarSupportProjection (KasparovDescent.mk (scalarAction Γ) E x (unitVector Γ))) =
      D.scalarSupportProjection (KasparovDescent.mk (scalarAction Γ) E (c.operator x)
        (unitVector Γ)) :=
    commute_projection c.groupAction _ (support_mk_of_unital c h1)
      c.operator.toCLM.toLinearMap
      (KasparovDescent.operatorHom (scalarAction Γ) E c.operator).toCLM.toLinearMap
      (fun x d => KasparovDescent.operatorHom_mk _ _ c.operator x d) hF x
  rw [h2]
  change D.scalarSupportProjection (KasparovDescent.operatorHom (scalarAction Γ) E c.operator
    (D.scalarSupportProjection (KasparovDescent.mk (scalarAction Γ) E x (unitVector Γ)))) =
    D.scalarSupportProjection (KasparovDescent.mk (scalarAction Γ) E (c.operator x) (unitVector Γ))
  rw [hF', hQ]

/-- `W` is an isomorphism of `c` with the representative
`evenInverseCycle Γ (rangeCycle c)` of `L_0 (Ψ_0 [c])`. -/
def leftIso : KasparovCycleIso c (evenInverseCycle Γ (rangeCycle c)) :=
  evenLeftIso (rangeVector _ (pulledDescent c).scalarSupportProjection_isStarProjection)
    (trace_inner_rangeVector c.groupAction _ _ (support_mk_of_unital c h1))
    (rangeVector_dense _ _) (rangeCycle c) c
    (op_smul_rangeVector c.groupAction _ _ (support_mk_of_unital c h1))
    (fun z m => KasparovCycle.scalarSupportRepresentation_apply _ z m)
    (representation_eq_smul c h1) (leftVector_grading c h1)
    (fun x => (leftVector_operator c h1 hF x).symm)

end EvenCycle

/-! ## Odd cycles -/

section OddCycle
variable {Γ : Type} [Group Γ] [Fintype Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul ℂᵐᵒᵖ E]
  [CStarModule ℂᵐᵒᵖ E] [CompleteSpace E]
variable (c : OddKasparovCycle (pointAction Γ) (scalarAction Γ) E)
  (h1 : c.representation (pointScalar 1) = 1)

include h1 in
theorem oddSupport_mk_of_unital (x : E) (d : (GroupCrossed Γ)ᵐᵒᵖ) :
    (oddPulledDescent c).scalarSupportProjection (KasparovDescent.mk (scalarAction Γ) E x d) =
      ∑ g : Γ, (Fintype.card Γ : ℂ)⁻¹ • KasparovDescent.mk (scalarAction Γ) E
        (c.groupAction.action g x) (MulOpposite.op (regular Γ g * MulOpposite.unop d)) := by
  rw [FinitePointDescentRange.oddPulledDescent_support_mk, h1]
  rfl

/-- The vector `Q(x ⊗ λ_e)` of the odd range cycle. -/
abbrev oddLeftVector (x : E) : ProjectionModule (oddPulledDescent c).scalarSupportProjection :=
  rangeVector (oddPulledDescent c).scalarSupportProjection
    (oddPulledDescent c).scalarSupportProjection_isStarProjection x

omit [Fintype Γ] in
include h1 in
theorem oddRepresentation_eq_smul (a : C₀(FiniteGroupPoint.{0}, ℂ)) (x : E) :
    c.representation a x = pointEval a • x := by
  have ha : a = pointEval a • pointScalar 1 := by
    conv_lhs => rw [← pointScalar_pointEval a]
    rw [← map_smul, smul_eq_mul, mul_one]
  have h : c.representation a = pointEval a • c.representation (pointScalar 1) := by
    rw [← map_smul]; exact congrArg _ ha
  rw [h, h1, AdjointableMap.coe_smul_apply, AdjointableMap.one_apply]

variable (hF : ∀ g x, c.operator (c.groupAction.action g x) = c.groupAction.action g (c.operator x))

include h1 hF in
theorem oddLeftVector_operator (x : E) :
    (oddRangeCycle c).operator (oddLeftVector c x) = oddLeftVector c (c.operator x) := by
  apply Subtype.ext
  refine (OddKasparovCycle.scalarSupportCompression_coe _ _).trans ?_
  set D := oddPulledDescent c
  have hP := D.scalarSupportProjection_isStarProjection
  have hQ : ∀ y, D.scalarSupportProjection (D.scalarSupportProjection y) =
      D.scalarSupportProjection y :=
    fun y => congrArg (fun T : AdjointableMap _ _ _ => T y) hP.isIdempotentElem.eq
  have hv : D.scalarSupportProjection (oddLeftVector c x : DescendedModule (Γ := Γ) E) =
      oddLeftVector c x := hQ _
  have h2 : D.scalarSupportBlockOperator (oddLeftVector c x : DescendedModule (Γ := Γ) E) =
      D.scalarSupportProjection (D.operator (oddLeftVector c x : DescendedModule (Γ := Γ) E)) := by
    unfold OddKasparovCycle.scalarSupportBlockOperator
    simp only [AdjointableMap.coe_add_apply, AdjointableMap.mul_apply,
      AdjointableMap.coe_sub_apply, AdjointableMap.one_apply, hv, sub_self, map_zero, add_zero]
  have hF' : KasparovDescent.operatorHom (scalarAction Γ) E c.operator
      (D.scalarSupportProjection (KasparovDescent.mk (scalarAction Γ) E x (unitVector Γ))) =
      D.scalarSupportProjection (KasparovDescent.mk (scalarAction Γ) E (c.operator x)
        (unitVector Γ)) :=
    commute_projection c.groupAction _ (oddSupport_mk_of_unital c h1)
      c.operator.toCLM.toLinearMap
      (KasparovDescent.operatorHom (scalarAction Γ) E c.operator).toCLM.toLinearMap
      (fun x d => KasparovDescent.operatorHom_mk _ _ c.operator x d) hF x
  rw [h2]
  change D.scalarSupportProjection (KasparovDescent.operatorHom (scalarAction Γ) E c.operator
    (D.scalarSupportProjection (KasparovDescent.mk (scalarAction Γ) E x (unitVector Γ)))) =
    D.scalarSupportProjection (KasparovDescent.mk (scalarAction Γ) E (c.operator x) (unitVector Γ))
  rw [hF', hQ]

/-- The odd case of `leftIso`. -/
def oddLeftIso : OddKasparovCycleIso c (oddInverseCycle Γ (oddRangeCycle c)) :=
  oddLeftIsoOf (rangeVector _ (oddPulledDescent c).scalarSupportProjection_isStarProjection)
    (trace_inner_rangeVector c.groupAction _ _ (oddSupport_mk_of_unital c h1))
    (rangeVector_dense _ _) (oddRangeCycle c) c
    (op_smul_rangeVector c.groupAction _ _ (oddSupport_mk_of_unital c h1))
    (fun z m => OddKasparovCycle.scalarSupportRepresentation_apply _ z m)
    (oddRepresentation_eq_smul c h1)
    (fun x => (oddLeftVector_operator c h1 hF x).symm)

end OddCycle

/-! ## A unital, equivariant representative of every class -/

section Representative
variable {Γ : Type} [Group Γ] [Fintype Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul ℂᵐᵒᵖ E]
  [CStarModule ℂᵐᵒᵖ E] [CompleteSpace E]

/-- `ℂ → C₀(pt)`, `z ↦ z · 1`, the inverse of `ev`. -/
abbrev pointInclusion : ℂ →⋆ₙₐ[ℂ] C₀(FiniteGroupPoint.{0}, ℂ) :=
  UnitPointCutoff.scalarToCZero FiniteGroupPoint.{0}

omit [Fintype Γ] in
theorem pointInclusion_equivariant : ∀ (g : Γ) (z : ℂ),
    pointInclusion ((scalarAction Γ).automorphism g z) =
      (pointAction Γ).automorphism g (pointInclusion z) := by
  intro g z
  ext y
  rfl

omit [Fintype Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- An operator commuting with the group action, read pointwise. -/
theorem commute_of_conjugate {B F : Type} [NonUnitalCStarAlgebra B] [PartialOrder B]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
    {β : CStarAlgebraAction Γ B} (V : EquivariantHilbertModule β F) (T : AdjointableMap B F F)
    (hT : ∀ g, V.conjugateOperator g T = T) (g : Γ) (x : F) :
    T (V.action g x) = V.action g (T x) := by
  have h := congrArg (fun S : AdjointableMap B F F => S (V.action g x)) (hT g)
  simp only [EquivariantHilbertModule.conjugateOperator, EquivariantHilbertModule.conjugateMap_apply,
    EquivariantHilbertModule.inv_apply_apply] at h
  exact h.symm

/-- `c` read over `ℂ` through `ℂ ≅ C₀(pt)`. -/
abbrev scalarCycle (c : KasparovCycle (pointAction Γ) (scalarAction Γ) E) :=
  evenSourcePullback pointInclusion pointInclusion_equivariant c

/-- The representative with unital point action and equivariant operator: the scalar support of
`c` over `ℂ`, with the averaged operator, read back over `C₀(pt)`. -/
abbrev unitalCycle (c : KasparovCycle (pointAction Γ) (scalarAction Γ) E) :=
  evenSourcePullback pointEval (pointEval_equivariant Γ)
    (scalarCycle c).scalarSupportCycle.equivariantCycle

theorem mk_unitalCycle (c : KasparovCycle (pointAction Γ) (scalarAction Γ) E) :
    KasparovHomotopyClass.mk (BundledKasparovCycle.of c) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of (unitalCycle c)) := by
  have h0 : KasparovHomotopyClass.mk (BundledKasparovCycle.of c) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of
        (evenSourcePullback pointEval (pointEval_equivariant Γ) (scalarCycle c))) :=
    KasparovHomotopyClass.mk_eq_of_iso
      { moduleEquiv := HilbertModuleEquiv.refl
        grading_intertwine := fun _ => rfl
        action_intertwine := fun _ _ => rfl
        representation_intertwine := fun a x => by
          change c.representation a x = c.representation (pointScalar (pointEval a)) x
          rw [pointScalar_pointEval]
        operator_intertwine := fun _ => rfl }
  refine h0.trans ?_
  rw [← sourcePullback_mk_even pointEval (pointEval_equivariant Γ) (scalarCycle c),
    ← sourcePullback_mk_even pointEval (pointEval_equivariant Γ) ((scalarCycle c).scalarSupportCycle.equivariantCycle),
    KasparovCycle.scalarSupport_class (scalarCycle c),
    KasparovCycle.mk_equivariantCycle (scalarCycle c).scalarSupportCycle]

theorem unitalCycle_unital (c : KasparovCycle (pointAction Γ) (scalarAction Γ) E) :
    (unitalCycle c).representation (pointScalar 1) = 1 := by
  ext x
  exact congrArg Subtype.val
    ((KasparovCycle.scalarSupportRepresentation_apply (scalarCycle c) 1 x).trans (one_smul ℂ x))

theorem unitalCycle_commute (c : KasparovCycle (pointAction Γ) (scalarAction Γ) E) (g : Γ)
    (x : ProjectionModule (scalarCycle c).scalarSupportProjection) :
    (unitalCycle c).operator ((unitalCycle c).groupAction.action g x) =
      (unitalCycle c).groupAction.action g ((unitalCycle c).operator x) :=
  commute_of_conjugate _ _
    ((scalarCycle c).scalarSupportCycle.conjugateOperator_equivariantOperator) g x

/-- Odd `c` read over `ℂ`. -/
abbrev oddScalarCycle (c : OddKasparovCycle (pointAction Γ) (scalarAction Γ) E) :=
  oddSourcePullback pointInclusion pointInclusion_equivariant c

/-- The odd representative with unital point action and equivariant operator. -/
abbrev oddUnitalCycle (c : OddKasparovCycle (pointAction Γ) (scalarAction Γ) E) :=
  oddSourcePullback pointEval (pointEval_equivariant Γ)
    (oddScalarCycle c).scalarSupportCycle.equivariantCycle

theorem mk_oddUnitalCycle (c : OddKasparovCycle (pointAction Γ) (scalarAction Γ) E) :
    OddKK.mk (BundledOddKasparovCycle.of c) =
      OddKK.mk (BundledOddKasparovCycle.of (oddUnitalCycle c)) := by
  have h0 : OddKK.mk (BundledOddKasparovCycle.of c) =
      OddKK.mk (BundledOddKasparovCycle.of
        (oddSourcePullback pointEval (pointEval_equivariant Γ) (oddScalarCycle c))) :=
    OddKK.mk_eq_of_iso
      { moduleEquiv := HilbertModuleEquiv.refl
        action_intertwine := fun _ _ => rfl
        representation_intertwine := fun a x => by
          change c.representation a x = c.representation (pointScalar (pointEval a)) x
          rw [pointScalar_pointEval]
        operator_intertwine := fun _ => rfl }
  refine h0.trans ?_
  rw [← sourcePullback_mk_odd pointEval (pointEval_equivariant Γ) (oddScalarCycle c),
    ← sourcePullback_mk_odd pointEval (pointEval_equivariant Γ) ((oddScalarCycle c).scalarSupportCycle.equivariantCycle),
    OddKasparovCycle.scalarSupport_class (oddScalarCycle c),
    OddKasparovCycle.mk_equivariantCycle (oddScalarCycle c).scalarSupportCycle]

theorem oddUnitalCycle_unital (c : OddKasparovCycle (pointAction Γ) (scalarAction Γ) E) :
    (oddUnitalCycle c).representation (pointScalar 1) = 1 := by
  ext x
  exact congrArg Subtype.val
    ((OddKasparovCycle.scalarSupportRepresentation_apply (oddScalarCycle c) 1 x).trans
      (one_smul ℂ x))

theorem oddUnitalCycle_commute (c : OddKasparovCycle (pointAction Γ) (scalarAction Γ) E) (g : Γ)
    (x : ProjectionModule (oddScalarCycle c).scalarSupportProjection) :
    (oddUnitalCycle c).operator ((oddUnitalCycle c).groupAction.action g x) =
      (oddUnitalCycle c).groupAction.action g ((oddUnitalCycle c).operator x) :=
  commute_of_conjugate _ _
    ((oddScalarCycle c).scalarSupportCycle.conjugateOperator_equivariantOperator) g x

end Representative

/-! ## The left round trip on classes -/

section Classes
variable {Γ : Type} [Group Γ] [Fintype Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul ℂᵐᵒᵖ E]
  [CStarModule ℂᵐᵒᵖ E] [CompleteSpace E]

/-- `L_0 (Ψ_0 [c]) = [c]` for a cycle with unital point action and equivariant operator. -/
theorem greenJulgInverse_pointGreenJulgHom_mk_even
    (c : KasparovCycle (pointAction Γ) (scalarAction Γ) E)
    (h1 : c.representation (pointScalar 1) = 1)
    (hF : ∀ g x, c.operator (c.groupAction.action g x) = c.groupAction.action g (c.operator x)) :
    greenJulgInverse Γ false
        (pointGreenJulgHom Γ false (KasparovHomotopyClass.mk (BundledKasparovCycle.of c))) =
      KasparovHomotopyClass.mk (BundledKasparovCycle.of c) := by
  change greenJulgInverse Γ false (Assembly.cutoffProductHom Γ FiniteGroupPoint.{0} false
    (finitePointCutoff Γ) (KasparovDescent.classHom (scalarAction Γ) (pointAction Γ) false
      (KasparovHomotopyClass.mk (BundledKasparovCycle.of c)))) = _
  rw [even_cutoffProduct_descent, greenJulgInverse_mk_even]
  exact (KasparovHomotopyClass.mk_eq_of_iso (leftIso c h1 hF)).symm

/-- `L_1 (Ψ_1 [c]) = [c]` for an odd cycle with unital point action and equivariant operator. -/
theorem greenJulgInverse_pointGreenJulgHom_mk_odd
    (c : OddKasparovCycle (pointAction Γ) (scalarAction Γ) E)
    (h1 : c.representation (pointScalar 1) = 1)
    (hF : ∀ g x, c.operator (c.groupAction.action g x) = c.groupAction.action g (c.operator x)) :
    greenJulgInverse Γ true
        (pointGreenJulgHom Γ true (OddKK.mk (BundledOddKasparovCycle.of c))) =
      OddKK.mk (BundledOddKasparovCycle.of c) := by
  change greenJulgInverse Γ true (Assembly.cutoffProductHom Γ FiniteGroupPoint.{0} true
    (finitePointCutoff Γ) (KasparovDescent.classHom (scalarAction Γ) (pointAction Γ) true
      (OddKK.mk (BundledOddKasparovCycle.of c)))) = _
  rw [odd_cutoffProduct_descent, greenJulgInverse_mk_odd]
  exact (OddKK.mk_eq_of_iso (oddLeftIso c h1 hF)).symm

variable (Γ) in
/-- `L_0 ∘ Ψ_0 = id`. -/
theorem greenJulgInverse_pointGreenJulgHom_even
    (x : KKParityGroup.{0, 0, 0, 0} false (pointAction Γ) (scalarAction Γ)) :
    greenJulgInverse Γ false (pointGreenJulgHom Γ false x) = x := by
  induction x using Quotient.inductionOn with
  | h b =>
    change greenJulgInverse Γ false (pointGreenJulgHom Γ false (KasparovHomotopyClass.mk b)) =
      KasparovHomotopyClass.mk b
    rw [← BundledKasparovCycle.of_storedCycle b, mk_unitalCycle b.cycle]
    exact greenJulgInverse_pointGreenJulgHom_mk_even _ (unitalCycle_unital _)
      (unitalCycle_commute _)

variable (Γ) in
/-- `L_1 ∘ Ψ_1 = id`. -/
theorem greenJulgInverse_pointGreenJulgHom_odd
    (x : KKParityGroup.{0, 0, 0, 0} true (pointAction Γ) (scalarAction Γ)) :
    greenJulgInverse Γ true (pointGreenJulgHom Γ true x) = x := by
  induction x using Quotient.inductionOn with
  | h b =>
    change greenJulgInverse Γ true (pointGreenJulgHom Γ true (OddKK.mk b)) = OddKK.mk b
    rw [← oddBundled_of_storedCycle b, mk_oddUnitalCycle b.cycle]
    exact greenJulgInverse_pointGreenJulgHom_mk_odd _ (oddUnitalCycle_unital _)
      (oddUnitalCycle_commute _)

end Classes

section Target
variable (Γ : Type) [Group Γ] [Countable Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [Finite Γ]

/-- `L_p ∘ Ψ_p = id` in both parities: Julg's inverse is a left inverse of the point Green–Julg
map. -/
theorem greenJulgInverse_pointGreenJulgHom (p : Bool)
    (x : KKParityGroup.{0, 0, 0, 0} p (CZero.action Γ (X := FiniteGroupPoint.{0}))
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)) :
    greenJulgInverse Γ p (pointGreenJulgHom Γ p x) = x := by
  obtain ⟨_⟩ := nonempty_fintype Γ
  cases p
  · exact greenJulgInverse_pointGreenJulgHom_even Γ x
  · exact greenJulgInverse_pointGreenJulgHom_odd Γ x

/-- Consequently `Ψ_p` is injective. -/
theorem pointGreenJulgHom_injective (p : Bool) : Function.Injective (pointGreenJulgHom Γ p) :=
  Function.LeftInverse.injective (greenJulgInverse_pointGreenJulgHom Γ p)

end Target

end BC4lean.KKTheory.GreenJulgPoint

import BC4lean.GreenJulgRepresentative
import BC4lean.FinitePointDescentRange
import BC4lean.FiniteScalarCrossed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The right round trip of the point Green–Julg map

Let `Γ` be finite with `n = |Γ|`, `Cr = ℂ ⋊_r Γ`, `λ_g` its unitaries, `τ` its trace and
`δ_e ∈ ℓ²Γ` the basis vector at the identity. The point Green–Julg map is
`Ψ_p = cutoff product ∘ descent : KK^Γ_p(C₀(pt), ℂ) → KK_p(ℂ, Cr)`, and Julg's inverse is
`L_p y = ev^* (infl y · [ℓ²Γ])` (`GreenJulgCorrespondence.greenJulgInverse`). This file proves
`Ψ_p (L_p y) = y` in both parities (`pointGreenJulgHom_greenJulgInverse`).

Let `d = (M, π, G)` be a cycle over `(ℂ, Cr)` for the trivial group with `π(z) = z`; every class
has such a representative (`KasparovCycle.scalarSupport_class`). By `GreenJulgRepresentative`, `L_p [d]` is the
class of the cycle on `H = M ⊗_{Cr} ℓ²Γ` with action `1 ⊗ ρ` and operator `G ⊗ 1`; by
`FinitePointDescentRange`,
`Ψ_p` of that class is the class of the compression of the descended cycle on `H ⊗ Cr` to the
range of `Q = n⁻¹ ∑_g V_g ⊗ λ_g`. The map
`K m = n^{-1/2} ∑_g (m λ_g⋆ ⊗ δ_e) ⊗ λ_g` is a unitary `M → range Q`:
* `⟪K m, K m'⟫ = n⁻¹ ∑_{g,h} τ(λ_g b λ_h⋆) λ_g⋆ λ_h = b` with `b = ⟪m, m'⟫`, by Fourier inversion
  in `Cr` (`sum_scalarTrace_regular_mul_mul_star`);
* `Q((m ⊗ δ_e) ⊗ λ_h) = n^{-1/2} K(m λ_h)`, so `Q K = K` and, since the vectors
  `(m ⊗ δ_e) ⊗ a` span a dense subspace, `K` is onto `range Q`;
* `K` intertwines the operators because `G` is `Cr`-linear, and the gradings likewise.

So `K` is a whole-cycle isomorphism `d ≅ range-cycle`, and `Ψ_p (L_p [d]) = [d]`. -/

noncomputable section
namespace BC4lean.KKTheory.GreenJulgPoint
open BC4lean.ProperActions BC4lean.OperatorKTheory BC4lean.Chapter8Examples
open KKTheory.GroupUniverseParityGroup
open KKTheory.FinitePointCharacterTensor KKTheory.FinitePointCompressedDescent
open KKTheory.FinitePointDescentRange KKTheory.GreenJulgCorrespondence
open KKTheory.GreenJulgRepresentative
open scoped ZeroAtInfty ComplexOrder KasparovDescent InnerProductSpace

/-! ## Vectors of `ℓ²Γ` -/

section Delta
variable {Γ : Type} [Group Γ]

theorem regularDeltaOne_eq_delta : regularDeltaOne Γ = delta Γ 1 := rfl

/-- `λ_g δ_e = δ_g`. -/
theorem regular_delta_one (g : Γ) : reducedCrossedRegular (B := ℂ) g (delta Γ 1) = delta Γ g := by
  rw [reducedCrossedRegular, delta, delta, reducedCrossedReindex_mk]
  congr 1
  ext i
  classical
  rw [reducedCrossedEmbeddingLinear_equiv_apply]
  simp only [Equiv.coe_mulLeft, Equiv.mulLeft_symm, Finsupp.single_apply]
  congr 1
  apply propext
  constructor
  · intro h
    rw [eq_inv_mul_iff_mul_eq, mul_one] at h
    exact h
  · intro h
    rw [eq_inv_mul_iff_mul_eq, mul_one]
    exact h

/-- `ρ_k δ_e = δ_{k⁻¹}`. -/
theorem rightTranslate_delta_one (k : Γ) : rightTranslate Γ k (delta Γ 1) = delta Γ k⁻¹ := by
  rw [rightTranslate_delta, one_mul]

/-- The right regular action: `ρ_k δ_e = δ_{k⁻¹}`. -/
theorem rightRegular_action_delta_one (k : Γ) :
    (rightRegular Γ).action k (delta Γ 1) = delta Γ k⁻¹ :=
  rightTranslate_delta_one k

omit [Group Γ] in
/-- The right `ℂᵐᵒᵖ`-action on `ℓ²Γ` is the complex action. -/
theorem op_smul_eq_smul (c : ℂ) (x : L2 Γ) : MulOpposite.op c • x = c • x := by
  apply module_inner_ext_right (B := ℂ)
  intro w
  rw [CStarModule.inner_op_smul_right, CStarModule.inner_smul_right_complex]
  apply MulOpposite.unop_injective
  rw [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_smul, smul_eq_mul, mul_comm]

omit [Group Γ] in
/-- For finite `Γ`, every vector of `ℓ²Γ` is `∑_g ⟪δ_g, ξ⟫ δ_g`. -/
theorem eq_sum_delta [Fintype Γ] (ξ : L2 Γ) :
    ξ = ∑ g : Γ, MulOpposite.unop ⟪delta Γ g, ξ⟫_(ℂᵐᵒᵖ) • delta Γ g := by
  have h := congrArg (fun T : AdjointableMap ℂ (L2 Γ) (L2 Γ) => T ξ) (one_eq_sum_rankOne (Γ := Γ))
  simp only [AdjointableMap.id_apply] at h
  refine h.trans ?_
  rw [finiteAdjointable_sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [moduleRankOne_apply, ← op_smul_eq_smul, MulOpposite.op_unop]

end Delta

/-! ## The isometry `K : M → H ⊗ Cr` -/

section Vector
variable {Γ : Type} [Group Γ] [Fintype Γ]
variable {M : Type} [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul (Cr Γ)ᵐᵒᵖ M]
  [CStarModule (Cr Γ)ᵐᵒᵖ M] [CompleteSpace M]

variable (Γ M) in
/-- `H = M ⊗_{Cr} ℓ²Γ`, the module of `L_p [d]`. -/
abbrev RegularTensor := InteriorModuleTensor (E := M) (regularRep Γ)

variable (Γ M) in
/-- `H ⊗ Cr`, the module of the descent of `L_p [d]`. -/
abbrev RegularDescended := DescendedModule (Γ := Γ) (RegularTensor Γ M)

omit [Fintype Γ] [CompleteSpace M] in
/-- The right action `m ↦ m λ` is complex linear. -/
theorem op_smul_complex_comm (a : Cr Γ) (z : ℂ) (m : M) :
    MulOpposite.op a • (z • m) = z • (MulOpposite.op a • m) := by
  apply module_inner_ext_right (B := Cr Γ)
  intro w
  rw [CStarModule.inner_op_smul_right, CStarModule.inner_smul_right_complex,
    CStarModule.inner_smul_right_complex, CStarModule.inner_op_smul_right, mul_smul_comm]

omit [Fintype Γ] [CompleteSpace M] in
theorem op_smul_op_smul (a b : Cr Γ) (m : M) :
    MulOpposite.op a • MulOpposite.op b • m = MulOpposite.op (b * a) • m := by
  rw [← module_mul_smul, ← MulOpposite.op_mul]

omit [Fintype Γ] [CompleteSpace M] in
theorem op_smul_regular_one (m : M) : MulOpposite.op (scalarRegular Γ 1) • m = m := by
  apply module_inner_ext_right (B := Cr Γ)
  intro w
  rw [CStarModule.inner_op_smul_right]
  apply MulOpposite.unop_injective
  rw [MulOpposite.unop_mul, MulOpposite.unop_op, mul_scalarRegular_one]

omit [Fintype Γ] [CompleteSpace M] in
/-- `m λ_g λ_g⋆ = m`. -/
theorem op_smul_regular_inv (g : Γ) (m : M) :
    MulOpposite.op (scalarRegular Γ g) • MulOpposite.op (scalarRegular Γ g⁻¹) • m = m := by
  rw [op_smul_op_smul, scalarRegular_mul, inv_mul_cancel, op_smul_regular_one]

omit [Fintype Γ] [CompleteSpace M] in
variable (M) in
/-- The right action `m ↦ m a` as a complex-linear map. -/
def rightMul (a : Cr Γ) : M →ₗ[ℂ] M where
  toFun m := MulOpposite.op a • m
  map_add' := module_smul_add _
  map_smul' z m := op_smul_complex_comm a z m

omit [Fintype Γ] in
variable (Γ M) in
/-- `m ↦ m ⊗ δ_e`. -/
def tensorDelta : M →ₗ[ℂ] RegularTensor Γ M :=
  (interiorModuleTensorMk (regularRep Γ)).flip (delta Γ 1)

omit [Fintype Γ] in
theorem tensorDelta_apply (m : M) :
    tensorDelta Γ M m = interiorModuleTensorMk (regularRep Γ) m (delta Γ 1) := rfl

omit [Fintype Γ] in
/-- `m ⊗ δ_g = m λ_g ⊗ δ_e`. -/
theorem mk_delta (m : M) (g : Γ) :
    interiorModuleTensorMk (regularRep Γ) m (delta Γ g) =
      tensorDelta Γ M (MulOpposite.op (scalarRegular Γ g) • m) := by
  rw [tensorDelta_apply, interiorModuleTensorMk_balance]
  congr 1
  exact (regular_delta_one g).symm

/-- For finite `Γ`, every elementary tensor `m ⊗ ξ` is a combination of vectors `m' ⊗ δ_e`. -/
theorem mk_eq_sum (m : M) (ξ : L2 Γ) :
    interiorModuleTensorMk (regularRep Γ) m ξ = ∑ g : Γ, MulOpposite.unop ⟪delta Γ g, ξ⟫_(ℂᵐᵒᵖ) •
      tensorDelta Γ M (MulOpposite.op (scalarRegular Γ g) • m) := by
  conv_lhs => rw [eq_sum_delta ξ]
  rw [map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smul, mk_delta]

omit [Fintype Γ] in
variable (Γ M) in
/-- `x ↦ x ⊗ a`, from `H` to `H ⊗ Cr`. -/
def descendedMk (a : Cr Γ) : RegularTensor Γ M →ₗ[ℂ] RegularDescended Γ M :=
  (interiorModuleTensorMk (KasparovDescent.coefficientRepresentation (scalarAction Γ))).flip
    (MulOpposite.op a)

omit [Fintype Γ] in
theorem descendedMk_apply (a : Cr Γ) (x : RegularTensor Γ M) :
    descendedMk Γ M a x =
      KasparovDescent.mk (scalarAction Γ) (RegularTensor Γ M) x (MulOpposite.op a) := rfl

omit [Fintype Γ] in
/-- `x ↦ x ⊗ a` is continuous. -/
theorem continuous_descendedMk (a : Cr Γ) : Continuous (descendedMk Γ M a) := by
  refine AddMonoidHomClass.continuous_of_bound (descendedMk Γ M a) ‖MulOpposite.op a‖ fun x => ?_
  rw [descendedMk_apply, mul_comm]
  exact interiorModuleTensorMk_norm_le (KasparovDescent.coefficientRepresentation (scalarAction Γ)) x
    (MulOpposite.op a)

omit [Fintype Γ] in
/-- `a ↦ x ⊗ a` is linear. -/
theorem descendedMk_add_smul (x : RegularTensor Γ M) (s : Finset Γ) (c : Γ → ℂ) (a : Γ → Cr Γ) :
    KasparovDescent.mk (scalarAction Γ) (RegularTensor Γ M) x (MulOpposite.op (∑ g ∈ s, c g • a g)) =
      ∑ g ∈ s, c g • descendedMk Γ M (a g) x := by
  let L : Cr Γ →ₗ[ℂ] RegularDescended Γ M :=
    (interiorModuleTensorMk (KasparovDescent.coefficientRepresentation (scalarAction Γ)) x).comp
      (MulOpposite.opLinearEquiv ℂ).toLinearMap
  have h := map_sum L (fun g => c g • a g) s
  simp only [map_smul] at h
  exact h

variable (Γ M) in
/-- The unnormalised `K`: `m ↦ ∑_g (m λ_g⋆ ⊗ δ_e) ⊗ λ_g`. -/
def regularSum : M →ₗ[ℂ] RegularDescended Γ M :=
  ∑ g : Γ, (descendedMk Γ M (scalarRegular Γ g)).comp
    ((tensorDelta Γ M).comp (rightMul M (scalarRegular Γ g⁻¹)))

theorem regularSum_apply (m : M) :
    regularSum Γ M m = ∑ g : Γ, descendedMk Γ M (scalarRegular Γ g)
      (tensorDelta Γ M (MulOpposite.op (scalarRegular Γ g⁻¹) • m)) := by
  unfold regularSum
  rw [LinearMap.sum_apply]
  rfl

omit [Fintype Γ] in
/-- Scalar coefficients act on `Cr` by scalar multiplication. -/
theorem coefficientToReducedCrossed_mul (z : ℂ) (a : Cr Γ) :
    coefficientToReducedCrossed (scalarAction Γ) z * a = z • a := by
  apply Subtype.ext
  change reducedCrossedCoefficient (scalarAction Γ) z * (a : AdjointableMap ℂ
    (ReducedCrossedHilbertModule ℂ Γ) (ReducedCrossedHilbertModule ℂ Γ)) = z • (a : _)
  rw [reducedCrossedCoefficient_trivial, smul_mul_assoc, one_mul]

omit [Fintype Γ] in
/-- `⟪m ⊗ δ_e, m' ⊗ δ_e⟫ = τ⟪m, m'⟫`. -/
theorem inner_tensorDelta (m m' : M) :
    ⟪tensorDelta Γ M m, tensorDelta Γ M m'⟫_(ℂᵐᵒᵖ) =
      MulOpposite.op (scalarTrace (MulOpposite.unop ⟪m, m'⟫_((Cr Γ)ᵐᵒᵖ))) := by
  rw [tensorDelta_apply, tensorDelta_apply, interiorModuleTensorInner_mk_mk, scalarTrace_eq_inner,
    MulOpposite.op_unop]
  rfl

omit [Fintype Γ] in
/-- The inner product of two terms of `regularSum`. -/
theorem inner_regularTerm (m m' : M) (g h : Γ) :
    ⟪descendedMk Γ M (scalarRegular Γ g) (tensorDelta Γ M (MulOpposite.op (scalarRegular Γ g⁻¹) • m)),
      descendedMk Γ M (scalarRegular Γ h)
        (tensorDelta Γ M (MulOpposite.op (scalarRegular Γ h⁻¹) • m'))⟫_((Cr Γ)ᵐᵒᵖ) =
      MulOpposite.op (scalarTrace (scalarRegular Γ g * MulOpposite.unop ⟪m, m'⟫_((Cr Γ)ᵐᵒᵖ) *
        star (scalarRegular Γ h)) • (star (scalarRegular Γ g) * scalarRegular Γ h)) := by
  have hg : star (scalarRegular Γ g⁻¹) = scalarRegular Γ g := by rw [star_scalarRegular, inv_inv]
  have hh : scalarRegular Γ h⁻¹ = star (scalarRegular Γ h) := by rw [star_scalarRegular]
  simp only [descendedMk_apply, KasparovDescent.mk_inner, inner_tensorDelta,
    CStarModule.inner_op_smul_left, CStarModule.inner_op_smul_right,
    MulOpposite.unop_op, MulOpposite.unop_mul, MulOpposite.unop_star, hg, hh]
  rw [coefficientToReducedCrossed_mul, mul_smul_comm, mul_assoc]

/-- `⟪∑ m, ∑ m'⟫ = n ⟪m, m'⟫`. -/
theorem inner_regularSum (m m' : M) :
    ⟪regularSum Γ M m, regularSum Γ M m'⟫_((Cr Γ)ᵐᵒᵖ) =
      (Fintype.card Γ : ℂ) • ⟪m, m'⟫_((Cr Γ)ᵐᵒᵖ) := by
  simp only [regularSum_apply, CStarModule.inner_sum_left (A := (Cr Γ)ᵐᵒᵖ) (E := RegularDescended Γ M),
    CStarModule.inner_sum_right (A := (Cr Γ)ᵐᵒᵖ) (E := RegularDescended Γ M),
    inner_regularTerm, ← Finset.op_sum]
  simp only [sum_scalarTrace_regular_mul_mul_star, MulOpposite.op_smul, MulOpposite.op_unop]

variable (Γ) in
/-- `n^{-1/2}`. -/
abbrev normalizer : ℂ := ((Real.sqrt (Fintype.card Γ))⁻¹ : ℝ)

theorem star_normalizer_mul : star (normalizer Γ) * normalizer Γ * (Fintype.card Γ : ℂ) = 1 := by
  have hn : (0 : ℝ) < Fintype.card Γ := Nat.cast_pos.mpr Fintype.card_pos
  have hs : Real.sqrt (Fintype.card Γ) ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  rw [normalizer, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    ← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← mul_inv,
    Real.mul_self_sqrt hn.le, inv_mul_cancel₀ hn.ne', Complex.ofReal_one]

theorem inner_normalized (m m' : M) :
    ⟪(normalizer Γ • regularSum Γ M) m, (normalizer Γ • regularSum Γ M) m'⟫_((Cr Γ)ᵐᵒᵖ) =
      ⟪m, m'⟫_((Cr Γ)ᵐᵒᵖ) := by
  simp only [LinearMap.smul_apply,
    CStarModule.inner_smul_left_complex (A := (Cr Γ)ᵐᵒᵖ) (E := RegularDescended Γ M),
    CStarModule.inner_smul_right_complex (A := (Cr Γ)ᵐᵒᵖ) (E := RegularDescended Γ M),
    inner_regularSum, smul_smul, ← mul_assoc, star_normalizer_mul, one_smul]

theorem norm_normalized (m : M) : ‖(normalizer Γ • regularSum Γ M) m‖ = ‖m‖ := by
  refine (CStarModule.norm_eq_sqrt_norm_inner_self (A := (Cr Γ)ᵐᵒᵖ) _).trans ?_
  refine Eq.trans ?_ (CStarModule.norm_eq_sqrt_norm_inner_self (A := (Cr Γ)ᵐᵒᵖ) m).symm
  exact congrArg (fun z => Real.sqrt ‖z‖) (inner_normalized m m)

variable (Γ M) in
/-- `K = n^{-1/2} ∑_g (· λ_g⋆ ⊗ δ_e) ⊗ λ_g`, an isometry `M → H ⊗ Cr`. -/
def regularIsometry : M →ₗᵢ[ℂ] RegularDescended Γ M where
  toLinearMap := normalizer Γ • regularSum Γ M
  norm_map' := norm_normalized

theorem regularIsometry_apply (m : M) :
    regularIsometry Γ M m = normalizer Γ • regularSum Γ M m := rfl

theorem inner_regularIsometry (m m' : M) :
    ⟪regularIsometry Γ M m, regularIsometry Γ M m'⟫_((Cr Γ)ᵐᵒᵖ) = ⟪m, m'⟫_((Cr Γ)ᵐᵒᵖ) :=
  inner_normalized m m'

/-- `∑ = n^{1/2} K`. -/
theorem regularSum_eq (m : M) :
    regularSum Γ M m = regularIsometry Γ M ((Real.sqrt (Fintype.card Γ) : ℂ) • m) := by
  have hn : (0 : ℝ) < Fintype.card Γ := Nat.cast_pos.mpr Fintype.card_pos
  have hs : Real.sqrt (Fintype.card Γ) ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  have hc : (Real.sqrt (Fintype.card Γ) : ℂ) * normalizer Γ = 1 := by
    rw [normalizer, ← Complex.ofReal_mul, mul_inv_cancel₀ hs, Complex.ofReal_one]
  simp only [regularIsometry_apply, map_smul, smul_smul, hc, one_smul]

end Vector

/-! ## `K` is a unitary onto the range of `Q`

Here `Q` is any projection on `H ⊗ Cr` that sends `(m ⊗ δ_e) ⊗ λ_h` to `n⁻¹ ∑(m λ_h)`. The
support projections of the pulled-back descents of `L_0 [d]` and `L_1 [d]` are such
projections (`evenSupport_regular`, `oddSupport_regular`). -/

section Range
variable {Γ : Type} [Group Γ] [Fintype Γ]
variable {M : Type} [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul (Cr Γ)ᵐᵒᵖ M]
  [CStarModule (Cr Γ)ᵐᵒᵖ M] [CompleteSpace M]
variable (Q : AdjointableMap (Cr Γ) (RegularDescended Γ M) (RegularDescended Γ M))
  (hQ : ∀ (m : M) (h : Γ), Q (descendedMk Γ M (scalarRegular Γ h) (tensorDelta Γ M m)) =
    (Fintype.card Γ : ℂ)⁻¹ • regularSum Γ M (MulOpposite.op (scalarRegular Γ h) • m))

include hQ in
/-- `Q` fixes the image of `K`. -/
theorem projection_regularIsometry (m : M) : Q (regularIsometry Γ M m) = regularIsometry Γ M m := by
  have hn : (Fintype.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hc : (∑ _g : Γ, (Fintype.card Γ : ℂ)⁻¹) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hn]
  have hsum : Q (regularSum Γ M m) = regularSum Γ M m := by
    conv_lhs => rw [regularSum_apply]
    simp only [map_sum, hQ, op_smul_regular_inv]
    simp only [← Finset.sum_smul, hc, one_smul]
  simp only [regularIsometry_apply, map_smul, hsum]

include hQ in
/-- `Q((m ⊗ δ_e) ⊗ a)` lies in the image of `K`. -/
theorem projection_mk_mem (m : M) (a : Cr Γ) :
    Q (KasparovDescent.mk (scalarAction Γ) (RegularTensor Γ M) (tensorDelta Γ M m)
      (MulOpposite.op a)) ∈ LinearMap.range (regularIsometry Γ M).toLinearMap := by
  have ha := descendedMk_add_smul (tensorDelta Γ M m) Finset.univ
    (fun g => scalarTrace (a * star (scalarRegular Γ g))) (fun g => scalarRegular Γ g)
  simp only [scalarCrossed_fourier a] at ha
  simp only [ha, map_sum, map_smul]
  refine Submodule.sum_mem _ fun h _ => Submodule.smul_mem _ _ ?_
  simp only [hQ, regularSum_eq]
  exact Submodule.smul_mem _ _ ⟨_, rfl⟩

include hQ in
/-- Every fixed vector of `Q` lies in the image of `K`: the image is closed, and it contains `Q`
of the vectors `(m ⊗ δ_e) ⊗ a`, which span a dense subspace. -/
theorem mem_range_regularIsometry (w : RegularDescended Γ M) (hw : Q w = w) :
    ∃ m, regularIsometry Γ M m = w := by
  let R := LinearMap.range (regularIsometry Γ M).toLinearMap
  have hclosed : IsClosed (R : Set (RegularDescended Γ M)) :=
    (regularIsometry Γ M).isometry.isClosedEmbedding.isClosed_range
  let S : Submodule ℂ (RegularDescended Γ M) := R.comap Q.toCLM.toLinearMap
  have hS : IsClosed (S : Set (RegularDescended Γ M)) := hclosed.preimage Q.toCLM.continuous
  have h2 : ∀ (x : RegularTensor Γ M) (a : Cr Γ), descendedMk Γ M a x ∈ S := by
    intro x a
    let T : Submodule ℂ (RegularTensor Γ M) := S.comap (descendedMk Γ M a)
    have hT : IsClosed (T : Set (RegularTensor Γ M)) := hS.preimage (continuous_descendedMk a)
    have hspan : Submodule.span ℂ (Set.range fun p : M × L2 Γ =>
        interiorModuleTensorMk (regularRep Γ) p.1 p.2) ≤ T := by
      rw [Submodule.span_le]
      rintro _ ⟨⟨m, ξ⟩, rfl⟩
      change descendedMk Γ M a (interiorModuleTensorMk (regularRep Γ) m ξ) ∈ S
      simp only [mk_eq_sum, map_sum, map_smul]
      exact S.sum_mem fun g _ => S.smul_mem _ (projection_mk_mem Q hQ _ a)
    exact hT.closure_subset_iff.mpr hspan (interiorModuleTensor_span_dense _ x)
  have hspan : Submodule.span ℂ (Set.range fun p : RegularTensor Γ M × (Cr Γ)ᵐᵒᵖ =>
      interiorModuleTensorMk (KasparovDescent.coefficientRepresentation (scalarAction Γ))
        p.1 p.2) ≤ S := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨x, a⟩, rfl⟩
    exact h2 x (MulOpposite.unop a)
  have hw' : w ∈ S := hS.closure_subset_iff.mpr hspan (interiorModuleTensor_span_dense _ w)
  obtain ⟨u, hu⟩ := hw'
  exact ⟨u, hu.trans hw⟩

/-- `K`, corestricted to the range of `Q`. -/
def regularRangeIsometry : M →ₗᵢ[ℂ] ProjectionModule Q where
  toLinearMap := (regularIsometry Γ M).toLinearMap.codRestrict
    (projectionFixedSubmodule Q) (projection_regularIsometry Q hQ)
  norm_map' m := (regularIsometry Γ M).norm_map m

@[simp] theorem regularRangeIsometry_coe (m : M) :
    ((regularRangeIsometry Q hQ m : ProjectionModule Q) : RegularDescended Γ M) =
      regularIsometry Γ M m := rfl

theorem regularRangeIsometry_surjective : Function.Surjective (regularRangeIsometry Q hQ) := by
  intro y
  obtain ⟨m, hm⟩ := mem_range_regularIsometry Q hQ (y : RegularDescended Γ M) y.property
  exact ⟨m, Subtype.ext hm⟩

/-- **The unitary `M ≅ range Q`.** -/
def regularRangeEquiv : HilbertModuleEquiv (Cr Γ) M (ProjectionModule Q) where
  linearIsometryEquiv := LinearIsometryEquiv.ofSurjective (regularRangeIsometry Q hQ)
    (regularRangeIsometry_surjective Q hQ)
  inner_map u v := inner_regularIsometry u v

@[simp] theorem regularRangeEquiv_coe (m : M) :
    ((regularRangeEquiv Q hQ m : ProjectionModule Q) : RegularDescended Γ M) =
      regularIsometry Γ M m := rfl

end Range

/-! ## Whole-cycle isomorphisms onto a support compression -/

section SupportRange
variable {Γ : Type} [Group Γ] [Fintype Γ]
variable {M : Type} [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul (Cr Γ)ᵐᵒᵖ M]
  [CStarModule (Cr Γ)ᵐᵒᵖ M] [CompleteSpace M]

omit [Fintype Γ] [CompleteSpace M] in
/-- The trivial group acts trivially. -/
theorem unit_action
    (U : EquivariantHilbertModule (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (Cr Γ)) M)
    (g : Unit) (m : M) : U.action g m = m := by
  rw [Subsingleton.elim g 1, map_one]
  rfl

section RangeIso
variable (d : KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
    (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (Cr Γ)) M)
  (D : KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
    (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (GroupCrossed Γ)) (RegularDescended Γ M))
  (hQ : ∀ (m : M) (h : Γ), D.scalarSupportProjection
      (descendedMk Γ M (scalarRegular Γ h) (tensorDelta Γ M m)) =
    (Fintype.card Γ : ℂ)⁻¹ • regularSum Γ M (MulOpposite.op (scalarRegular Γ h) • m))

include hQ in
theorem regularRangeEquiv_grading
    (hgr : ∀ m, D.grading.grading (regularIsometry Γ M m) = regularIsometry Γ M (d.grading.grading m))
    (x : M) :
    regularRangeEquiv _ hQ (d.grading.grading x) =
      D.scalarSupportGrading.grading (regularRangeEquiv _ hQ x) := by
  apply Subtype.ext
  refine Eq.trans ?_ (KasparovCycle.scalarSupportGrading_coe D _).symm
  exact (hgr x).symm

include hQ in
theorem regularRangeEquiv_action (hact : ∀ g v, D.groupAction.action g v = v) (g : Unit) (x : M) :
    regularRangeEquiv _ hQ (d.groupAction.action g x) =
      D.scalarSupportGroupAction.action g (regularRangeEquiv _ hQ x) := by
  apply Subtype.ext
  refine Eq.trans ?_ (KasparovCycle.scalarSupportGroupAction_coe D g _).symm
  refine Eq.trans ?_ (hact g _).symm
  exact congrArg (regularIsometry Γ M) (unit_action d.groupAction g x)

include hQ in
theorem regularRangeEquiv_representation (hrep : ∀ z m, d.representation z m = z • m) (z : ℂ)
    (x : M) :
    regularRangeEquiv _ hQ (d.representation z x) =
      D.scalarSupportRepresentation z (regularRangeEquiv _ hQ x) := by
  refine Eq.trans ?_ (KasparovCycle.scalarSupportRepresentation_apply D z _).symm
  apply Subtype.ext
  refine (congrArg (regularIsometry Γ M) (hrep z x)).trans ?_
  exact map_smul (regularIsometry Γ M) z x

include hQ in
theorem regularRangeEquiv_operator
    (hF : ∀ m, D.operator (regularIsometry Γ M m) = regularIsometry Γ M (d.operator m)) (x : M) :
    regularRangeEquiv _ hQ (d.operator x) =
      D.scalarSupportCompression (regularRangeEquiv _ hQ x) := by
  apply Subtype.ext
  refine Eq.trans ?_ (KasparovCycle.scalarSupportCompression_coe D _).symm
  have hv : D.scalarSupportProjection (regularIsometry Γ M x) = regularIsometry Γ M x :=
    projection_regularIsometry _ hQ x
  have h2 : D.scalarSupportBlockOperator (regularIsometry Γ M x) =
      D.scalarSupportProjection (D.operator (regularIsometry Γ M x)) := by
    unfold KasparovCycle.scalarSupportBlockOperator
    simp only [AdjointableMap.coe_add_apply, AdjointableMap.mul_apply,
      AdjointableMap.coe_sub_apply, AdjointableMap.one_apply, hv, sub_self, map_zero, add_zero]
  refine Eq.trans ?_ h2.symm
  simp only [regularRangeEquiv_coe, hF, projection_regularIsometry _ hQ]

/-- `K` is an isomorphism from `d` onto the support compression of any cycle `D` on `H ⊗ Cr`
whose support projection is `Q`, whose action is trivial and whose grading and operator restrict
to those of `d` along `K`. -/
def supportRangeIso (hrep : ∀ z m, d.representation z m = z • m)
    (hgr : ∀ m, D.grading.grading (regularIsometry Γ M m) = regularIsometry Γ M (d.grading.grading m))
    (hact : ∀ g v, D.groupAction.action g v = v)
    (hF : ∀ m, D.operator (regularIsometry Γ M m) = regularIsometry Γ M (d.operator m)) :
    KasparovCycleIso d D.scalarSupportCycle where
  moduleEquiv := regularRangeEquiv _ hQ
  grading_intertwine := regularRangeEquiv_grading d D hQ hgr
  action_intertwine := regularRangeEquiv_action d D hQ hact
  representation_intertwine := regularRangeEquiv_representation d D hQ hrep
  operator_intertwine := regularRangeEquiv_operator d D hQ hF

end RangeIso

section OddRangeIso
variable (d : OddKasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
    (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (Cr Γ)) M)
  (D : OddKasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
    (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (GroupCrossed Γ)) (RegularDescended Γ M))
  (hQ : ∀ (m : M) (h : Γ), D.scalarSupportProjection
      (descendedMk Γ M (scalarRegular Γ h) (tensorDelta Γ M m)) =
    (Fintype.card Γ : ℂ)⁻¹ • regularSum Γ M (MulOpposite.op (scalarRegular Γ h) • m))

include hQ in
theorem oddRegularRangeEquiv_action (hact : ∀ g v, D.groupAction.action g v = v) (g : Unit) (x : M) :
    regularRangeEquiv _ hQ (d.groupAction.action g x) =
      D.scalarSupportGroupAction.action g (regularRangeEquiv _ hQ x) := by
  apply Subtype.ext
  refine Eq.trans ?_ (OddKasparovCycle.scalarSupportGroupAction_coe D g _).symm
  refine Eq.trans ?_ (hact g _).symm
  exact congrArg (regularIsometry Γ M) (unit_action d.groupAction g x)

include hQ in
theorem oddRegularRangeEquiv_representation (hrep : ∀ z m, d.representation z m = z • m) (z : ℂ)
    (x : M) :
    regularRangeEquiv _ hQ (d.representation z x) =
      D.scalarSupportRepresentation z (regularRangeEquiv _ hQ x) := by
  refine Eq.trans ?_ (OddKasparovCycle.scalarSupportRepresentation_apply D z _).symm
  apply Subtype.ext
  refine (congrArg (regularIsometry Γ M) (hrep z x)).trans ?_
  exact map_smul (regularIsometry Γ M) z x

include hQ in
theorem oddRegularRangeEquiv_operator
    (hF : ∀ m, D.operator (regularIsometry Γ M m) = regularIsometry Γ M (d.operator m)) (x : M) :
    regularRangeEquiv _ hQ (d.operator x) =
      D.scalarSupportCompression (regularRangeEquiv _ hQ x) := by
  apply Subtype.ext
  refine Eq.trans ?_ (OddKasparovCycle.scalarSupportCompression_coe D _).symm
  have hv : D.scalarSupportProjection (regularIsometry Γ M x) = regularIsometry Γ M x :=
    projection_regularIsometry _ hQ x
  have h2 : D.scalarSupportBlockOperator (regularIsometry Γ M x) =
      D.scalarSupportProjection (D.operator (regularIsometry Γ M x)) := by
    unfold OddKasparovCycle.scalarSupportBlockOperator
    simp only [AdjointableMap.coe_add_apply, AdjointableMap.mul_apply,
      AdjointableMap.coe_sub_apply, AdjointableMap.one_apply, hv, sub_self, map_zero, add_zero]
  refine Eq.trans ?_ h2.symm
  simp only [regularRangeEquiv_coe, hF, projection_regularIsometry _ hQ]

/-- `K` is an isomorphism from `d` onto the support compression of any odd cycle `D` on `H ⊗ Cr`
whose support projection is `Q`, whose action is trivial and whose operator restricts to that of
`d` along `K`. -/
def oddSupportRangeIso (hrep : ∀ z m, d.representation z m = z • m)
    (hact : ∀ g v, D.groupAction.action g v = v)
    (hF : ∀ m, D.operator (regularIsometry Γ M m) = regularIsometry Γ M (d.operator m)) :
    OddKasparovCycleIso d D.scalarSupportCycle where
  moduleEquiv := regularRangeEquiv _ hQ
  action_intertwine := oddRegularRangeEquiv_action d D hQ hact
  representation_intertwine := oddRegularRangeEquiv_representation d D hQ hrep
  operator_intertwine := oddRegularRangeEquiv_operator d D hQ hF

end OddRangeIso

end SupportRange

/-! ## The representatives of `L_p [d]` and their descents -/

section Cycle
variable {Γ : Type} [Group Γ] [Fintype Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
variable {M : Type} [NormedAddCommGroup M] [NormedSpace ℂ M] [SMul (Cr Γ)ᵐᵒᵖ M]
  [CStarModule (Cr Γ)ᵐᵒᵖ M] [CompleteSpace M]

omit [Group Γ] [Fintype Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [NormedAddCommGroup M]
  [NormedSpace ℂ M] [SMul (Cr Γ)ᵐᵒᵖ M] [CStarModule (Cr Γ)ᵐᵒᵖ M] [CompleteSpace M] in
/-- Evaluation at the point sends the constant `1` to `1`. -/
theorem pointEval_pointScalar_one : pointEval (pointScalar 1) = 1 := rfl

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- The descent formula `n⁻¹ ∑_k π(1) V_k x ⊗ λ_k λ_h` of `FinitePointDescentRange`, at `x = m ⊗ δ_e`. -/
theorem descentSum_eq (π₁ : RegularTensor Γ M → RegularTensor Γ M)
    (V : Γ → RegularTensor Γ M → RegularTensor Γ M)
    (hπ : ∀ x, π₁ (tensorDelta Γ M x) = tensorDelta Γ M x)
    (hV : ∀ k m, V k (tensorDelta Γ M m) =
      tensorDelta Γ M (MulOpposite.op (scalarRegular Γ k⁻¹) • m)) (m : M) (h : Γ) :
    ∑ g : Γ, (Fintype.card Γ : ℂ)⁻¹ • KasparovDescent.mk (scalarAction Γ) (RegularTensor Γ M)
        (π₁ (V g (tensorDelta Γ M m)))
        (MulOpposite.op (regular Γ g * MulOpposite.unop (MulOpposite.op (scalarRegular Γ h)))) =
      (Fintype.card Γ : ℂ)⁻¹ • regularSum Γ M (MulOpposite.op (scalarRegular Γ h) • m) := by
  simp only [regularSum_apply, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight h) _ _ fun k => ?_
  simp only [hV, hπ, Equiv.coe_mulRight, descendedMk_apply, op_smul_op_smul, scalarRegular_mul,
    mul_inv_rev, mul_inv_cancel_left, MulOpposite.unop_op]
  change _ = (Fintype.card Γ : ℂ)⁻¹ • KasparovDescent.mk (scalarAction Γ) (RegularTensor Γ M) _
    (MulOpposite.op (scalarRegular Γ (k * h)))
  rw [← scalarRegular_mul]
  rfl

variable (Γ) in
/-- The representative of `L_0 [d]` (`greenJulgInverse_mk_even`): `(M ⊗_{Cr} ℓ²Γ, 1 ⊗ ρ, (π ∘ ev) ⊗ 1, G ⊗ 1)`. -/
abbrev evenInverseCycle
    (d : KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (Cr Γ)) M) :
    KasparovCycle (pointAction Γ) (scalarAction Γ) (RegularTensor Γ M) :=
  evenSourcePullback pointEval (pointEval_equivariant Γ)
    (evenTensorCycle (rightRegular Γ) (regularRep Γ) (regularRep_equivariant Γ)
      (regularRep_isModuleCompact Γ) (isCountablyGenerated Γ) (inflateEven Γ d))

variable (Γ) in
/-- The representative of `L_1 [d]` (`greenJulgInverse_mk_odd`). -/
abbrev oddInverseCycle
    (d : OddKasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
        (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (Cr Γ)) M) :
    OddKasparovCycle (pointAction Γ) (scalarAction Γ) (RegularTensor Γ M) :=
  oddSourcePullback pointEval (pointEval_equivariant Γ)
    (oddTensorCycle (rightRegular Γ) (regularRep Γ) (regularRep_equivariant Γ)
      (regularRep_isModuleCompact Γ) (isCountablyGenerated Γ) (inflateOdd Γ d))

/-! ### Even cycles -/

section Even
variable (d : KasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
    (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (Cr Γ)) M)
  (hrep : ∀ z m, d.representation z m = z • m)

theorem evenInverseCycle_action (k : Γ) (m : M) :
    (evenInverseCycle Γ d).groupAction.action k (tensorDelta Γ M m) =
      tensorDelta Γ M (MulOpposite.op (scalarRegular Γ k⁻¹) • m) := by
  rw [← mk_delta, tensorDelta_apply]
  change (evenTensorCycle (rightRegular Γ) (regularRep Γ) (regularRep_equivariant Γ)
      (regularRep_isModuleCompact Γ) (isCountablyGenerated Γ) (inflateEven Γ d)).groupAction.action k
    (interiorModuleTensorMk (regularRep Γ) m (delta Γ 1)) = _
  rw [evenTensorCycle_action, EquivariantHilbertModule.interiorTensor_action_mk,
    rightRegular_action_delta_one]
  exact congrArg (fun y => interiorModuleTensorMk (regularRep Γ) y (delta Γ k⁻¹))
    (unit_action d.groupAction _ m)

include hrep in
theorem evenInverseCycle_representation_one (x : M) :
    (evenInverseCycle Γ d).representation (pointScalar 1) (tensorDelta Γ M x) =
      tensorDelta Γ M x := by
  rw [evenSourcePullback_representation, evenTensorCycle_representation, tensorDelta_apply,
    interiorModuleTensorOperator_mk]
  exact congrArg (fun y => interiorModuleTensorMk (regularRep Γ) y (delta Γ 1))
    ((hrep _ x).trans (by rw [pointEval_pointScalar_one, one_smul]))

include hrep in
/-- The support projection of the pulled-back descent of `L_0 [d]` on `(m ⊗ δ_e) ⊗ λ_h`. -/
theorem evenSupport_regular (m : M) (h : Γ) :
    (pulledDescent (evenInverseCycle Γ d)).scalarSupportProjection
        (descendedMk Γ M (scalarRegular Γ h) (tensorDelta Γ M m)) =
      (Fintype.card Γ : ℂ)⁻¹ • regularSum Γ M (MulOpposite.op (scalarRegular Γ h) • m) := by
  simp only [descendedMk_apply, FinitePointDescentRange.pulledDescent_support_mk]
  exact descentSum_eq _ _ (evenInverseCycle_representation_one d hrep)
    (evenInverseCycle_action d) m h

theorem evenInverseCycle_grading (m : M) :
    (evenInverseCycle Γ d).grading.grading (tensorDelta Γ M m) =
      tensorDelta Γ M (d.grading.grading m) := by
  rw [tensorDelta_apply, tensorDelta_apply]
  exact GradedHilbertModule.interiorTensor_grading_mk _ _ _ m _

theorem regularSum_grading (m : M) :
    (KasparovDescent.ordinaryModuleGrading (scalarAction Γ)
        (evenInverseCycle Γ d).grading).grading (regularSum Γ M m) =
      regularSum Γ M (d.grading.grading m) := by
  simp only [regularSum_apply, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [descendedMk_apply, KasparovDescent.ordinaryModuleGrading_mk,
    evenInverseCycle_grading, GradedHilbertModule.map_op_smul]
  rfl

theorem regularSum_operator (m : M) :
    KasparovDescent.operatorHom (scalarAction Γ) (RegularTensor Γ M) (evenInverseCycle Γ d).operator
        (regularSum Γ M m) = regularSum Γ M (d.operator m) := by
  simp only [regularSum_apply, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [descendedMk_apply, KasparovDescent.operatorHom_mk,
    evenSourcePullback_operator, evenTensorCycle_operator, tensorDelta_apply,
    interiorModuleTensorOperator_mk, AdjointableMap.map_op_smul]
  rfl

theorem evenGrading_regularIsometry (m : M) :
    (pulledDescent (evenInverseCycle Γ d)).grading.grading (regularIsometry Γ M m) =
      regularIsometry Γ M (d.grading.grading m) := by
  change (KasparovDescent.ordinaryModuleGrading (scalarAction Γ)
    (evenInverseCycle Γ d).grading).grading (normalizer Γ • regularSum Γ M m) = _
  rw [map_smul, regularSum_grading]
  rfl

theorem evenOperator_regularIsometry (m : M) :
    (pulledDescent (evenInverseCycle Γ d)).operator (regularIsometry Γ M m) =
      regularIsometry Γ M (d.operator m) := by
  change KasparovDescent.operatorHom (scalarAction Γ) (RegularTensor Γ M)
    (evenInverseCycle Γ d).operator (normalizer Γ • regularSum Γ M m) = _
  rw [map_smul, regularSum_operator]
  rfl

/-- **The whole-cycle isomorphism, even case.** `d` is isomorphic to the range cycle of
`L_0 [d]`, by `K`. -/
def evenRangeIso : KasparovCycleIso d (rangeCycle (evenInverseCycle Γ d)) :=
  supportRangeIso d (pulledDescent (evenInverseCycle Γ d)) (evenSupport_regular d hrep) hrep
    (evenGrading_regularIsometry d) (fun _ _ => rfl) (evenOperator_regularIsometry d)

end Even

/-! ### Odd cycles -/

section Odd
variable (d : OddKasparovCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
    (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (Cr Γ)) M)
  (hrep : ∀ z m, d.representation z m = z • m)

theorem oddInverseCycle_action (k : Γ) (m : M) :
    (oddInverseCycle Γ d).groupAction.action k (tensorDelta Γ M m) =
      tensorDelta Γ M (MulOpposite.op (scalarRegular Γ k⁻¹) • m) := by
  rw [← mk_delta, tensorDelta_apply]
  change (oddTensorCycle (rightRegular Γ) (regularRep Γ) (regularRep_equivariant Γ)
      (regularRep_isModuleCompact Γ) (isCountablyGenerated Γ) (inflateOdd Γ d)).groupAction.action k
    (interiorModuleTensorMk (regularRep Γ) m (delta Γ 1)) = _
  rw [oddTensorCycle_action, EquivariantHilbertModule.interiorTensor_action_mk,
    rightRegular_action_delta_one]
  exact congrArg (fun y => interiorModuleTensorMk (regularRep Γ) y (delta Γ k⁻¹))
    (unit_action d.groupAction _ m)

include hrep in
theorem oddInverseCycle_representation_one (x : M) :
    (oddInverseCycle Γ d).representation (pointScalar 1) (tensorDelta Γ M x) =
      tensorDelta Γ M x := by
  rw [oddSourcePullback_representation, oddTensorCycle_representation, tensorDelta_apply,
    interiorModuleTensorOperator_mk]
  exact congrArg (fun y => interiorModuleTensorMk (regularRep Γ) y (delta Γ 1))
    ((hrep _ x).trans (by rw [pointEval_pointScalar_one, one_smul]))

include hrep in
/-- The support projection of the pulled-back descent of `L_1 [d]` on `(m ⊗ δ_e) ⊗ λ_h`. -/
theorem oddSupport_regular (m : M) (h : Γ) :
    (oddPulledDescent (oddInverseCycle Γ d)).scalarSupportProjection
        (descendedMk Γ M (scalarRegular Γ h) (tensorDelta Γ M m)) =
      (Fintype.card Γ : ℂ)⁻¹ • regularSum Γ M (MulOpposite.op (scalarRegular Γ h) • m) := by
  simp only [descendedMk_apply, FinitePointDescentRange.oddPulledDescent_support_mk]
  exact descentSum_eq _ _ (oddInverseCycle_representation_one d hrep)
    (oddInverseCycle_action d) m h

theorem oddRegularSum_operator (m : M) :
    KasparovDescent.operatorHom (scalarAction Γ) (RegularTensor Γ M) (oddInverseCycle Γ d).operator
        (regularSum Γ M m) = regularSum Γ M (d.operator m) := by
  have hop : (oddInverseCycle Γ d).operator = interiorModuleTensorOperator (regularRep Γ) d.operator :=
    oddTensorCycle_operator (rightRegular Γ) (regularRep Γ) (regularRep_equivariant Γ)
      (regularRep_isModuleCompact Γ) (isCountablyGenerated Γ) (inflateOdd Γ d)
  simp only [hop, regularSum_apply, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [descendedMk_apply, KasparovDescent.operatorHom_mk, tensorDelta_apply,
    interiorModuleTensorOperator_mk, AdjointableMap.map_op_smul]

theorem oddOperator_regularIsometry (m : M) :
    (oddPulledDescent (oddInverseCycle Γ d)).operator (regularIsometry Γ M m) =
      regularIsometry Γ M (d.operator m) := by
  change KasparovDescent.operatorHom (scalarAction Γ) (RegularTensor Γ M)
    (oddInverseCycle Γ d).operator (normalizer Γ • regularSum Γ M m) = _
  rw [map_smul, oddRegularSum_operator]
  rfl

/-- **The whole-cycle isomorphism, odd case.** -/
def oddRangeIso : OddKasparovCycleIso d (oddRangeCycle (oddInverseCycle Γ d)) :=
  oddSupportRangeIso d (oddPulledDescent (oddInverseCycle Γ d)) (oddSupport_regular d hrep) hrep
    (fun _ _ => rfl) (oddOperator_regularIsometry d)

end Odd

end Cycle

/-- Rebundling the stored odd cycle gives the bundled cycle back (the odd analogue of
`BundledKasparovCycle.of_storedCycle`). -/
theorem oddBundled_of_storedCycle {Γ A B : Type} [Group Γ] [NonUnitalCStarAlgebra A]
    [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
    (c : BundledOddKasparovCycle.{0, 0, 0, 0} α β) : BundledOddKasparovCycle.of c.cycle = c := by
  cases c
  rfl

/-! ## The right round trip -/

section Point
variable (Γ : Type) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]

/-- The point Green–Julg map `Ψ_p`: descent followed by the cutoff product. -/
def pointGreenJulgHom [Finite Γ] (p : Bool) :
    KKParityGroup.{0, 0, 0, 0} p (CZero.action Γ (X := FiniteGroupPoint.{0}))
        (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) →+
      KKParityGroup.{0, 0, 0, 0} p (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
          (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (Cr Γ)) :=
  (Assembly.cutoffProductHom Γ FiniteGroupPoint.{0} p (finitePointCutoff Γ)).comp
    (KasparovDescent.classHom (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
      (CZero.action Γ (X := FiniteGroupPoint.{0})) p)

variable [Fintype Γ]

/-- `Ψ_0 (L_0 y) = y`. -/
theorem pointGreenJulgHom_greenJulgInverse_even
    (y : KKParityGroup.{0, 0, 0, 0} false (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (Cr Γ))) :
    pointGreenJulgHom Γ false (greenJulgInverse Γ false y) = y := by
  induction y using Quotient.inductionOn with
  | h c =>
    change pointGreenJulgHom Γ false (greenJulgInverse Γ false (KasparovHomotopyClass.mk c)) =
      KasparovHomotopyClass.mk c
    rw [← BundledKasparovCycle.of_storedCycle c, KasparovCycle.scalarSupport_class c.cycle,
      greenJulgInverse_mk_even]
    change Assembly.cutoffProductHom Γ FiniteGroupPoint.{0} false (finitePointCutoff Γ)
        (KasparovDescent.classHom (scalarAction Γ) (pointAction Γ) false
          (KasparovHomotopyClass.mk (BundledKasparovCycle.of
            (evenInverseCycle Γ c.cycle.scalarSupportCycle)))) = _
    rw [even_cutoffProduct_descent]
    exact (KasparovHomotopyClass.mk_eq_of_iso (evenRangeIso c.cycle.scalarSupportCycle
      (KasparovCycle.scalarSupportRepresentation_apply c.cycle))).symm

/-- `Ψ_1 (L_1 y) = y`. -/
theorem pointGreenJulgHom_greenJulgInverse_odd
    (y : KKParityGroup.{0, 0, 0, 0} true (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (Cr Γ))) :
    pointGreenJulgHom Γ true (greenJulgInverse Γ true y) = y := by
  induction y using Quotient.inductionOn with
  | h c =>
    change pointGreenJulgHom Γ true (greenJulgInverse Γ true (OddKK.mk c)) = OddKK.mk c
    rw [← oddBundled_of_storedCycle c, OddKasparovCycle.scalarSupport_class c.cycle,
      greenJulgInverse_mk_odd]
    change Assembly.cutoffProductHom Γ FiniteGroupPoint.{0} true (finitePointCutoff Γ)
        (KasparovDescent.classHom (scalarAction Γ) (pointAction Γ) true
          (OddKK.mk (BundledOddKasparovCycle.of
            (oddInverseCycle Γ c.cycle.scalarSupportCycle)))) = _
    rw [odd_cutoffProduct_descent]
    exact (OddKK.mk_eq_of_iso (oddRangeIso c.cycle.scalarSupportCycle
      (OddKasparovCycle.scalarSupportRepresentation_apply c.cycle))).symm

end Point

section Target
variable (Γ : Type) [Group Γ] [Countable Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [Finite Γ]

/-- `Ψ_p ∘ L_p = id` in both parities: Julg's inverse is a right inverse of the point
Green–Julg map. -/
theorem pointGreenJulgHom_greenJulgInverse (p : Bool)
    (y : KKParityGroup.{0, 0, 0, 0} p (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (Cr Γ))) :
    pointGreenJulgHom Γ p (greenJulgInverse Γ p y) = y := by
  obtain ⟨_⟩ := nonempty_fintype Γ
  cases p
  · exact pointGreenJulgHom_greenJulgInverse_even Γ y
  · exact pointGreenJulgHom_greenJulgInverse_odd Γ y

/-- Consequently `Ψ_p` is surjective. -/
theorem pointGreenJulgHom_surjective (p : Bool) : Function.Surjective (pointGreenJulgHom Γ p) :=
  fun y => ⟨greenJulgInverse Γ p y, pointGreenJulgHom_greenJulgInverse Γ p y⟩

end Target

end BC4lean.KKTheory.GreenJulgPoint

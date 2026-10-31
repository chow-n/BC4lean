import BC4lean.ReducedOperatorK0

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # Traces on K₀ and the canonical trace of the reduced group C⋆-algebra

A complex-linear functional `τ` on a unital C⋆-algebra `A` with `τ (a * b) = τ (b * a)` gives the
matrix trace `∑ i, τ (M i i)`. It satisfies `Tr (v * w) = Tr (w * v)` for rectangular `v`, `w`, so
it is constant on rectangular Murray–von Neumann classes, additive on block sums and zero on the
empty projection. By the universal property of the Grothendieck group it induces
`traceK0 τ : K0 A →+ ℂ` (`traceK0_k0Projection`).
-/

noncomputable section
open scoped Matrix

universe u

namespace BC4lean.OperatorKTheory

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A projection of `A` as a `1 × 1` matrix projection. -/
def unitMatrixProjection (e : A) (he : IsStarProjection e) : MatrixProjection A Unit :=
  ⟨CStarMatrix.ofMatrix (fun _ _ => e), ⟨by
    change CStarMatrix.ofMatrix (fun _ _ => e) * CStarMatrix.ofMatrix (fun _ _ => e) =
      CStarMatrix.ofMatrix (fun (_ : Unit) (_ : Unit) => e)
    ext i j
    simp only [CStarMatrix.mul_apply, Finset.univ_unique, Finset.sum_singleton]
    exact he.isIdempotentElem.eq, by
    change star (CStarMatrix.ofMatrix (fun _ _ => e)) =
      CStarMatrix.ofMatrix (fun (_ : Unit) (_ : Unit) => e)
    ext i j
    simp only [CStarMatrix.star_apply]
    exact he.isSelfAdjoint.star_eq⟩⟩

/-- A complex-linear tracial functional. -/
structure TracialFunctional (A : Type u) [CStarAlgebra A] where
  toLinearMap : A →ₗ[ℂ] ℂ
  map_mul_comm : ∀ a b : A, toLinearMap (a * b) = toLinearMap (b * a)

namespace TracialFunctional

variable (τ : TracialFunctional A)

/-- The matrix trace `∑ i, τ (M i i)`. -/
def matrixTrace {ι : Type} [Fintype ι] (M : Matrix ι ι A) : ℂ := ∑ i, τ.toLinearMap (M i i)

omit [PartialOrder A] [StarOrderedRing A] in
theorem matrixTrace_mul_comm {ι κ : Type} [Fintype ι] [Fintype κ] (v : Matrix ι κ A)
    (w : Matrix κ ι A) : τ.matrixTrace (v * w) = τ.matrixTrace (w * v) := by
  simp only [matrixTrace, Matrix.mul_apply, map_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => τ.map_mul_comm _ _

/-- The trace of a matrix projection. -/
def projectionTrace {ι : Type} [Fintype ι] [DecidableEq ι] (p : MatrixProjection A ι) : ℂ :=
  τ.matrixTrace (projectionMatrix p)

theorem projectionTrace_eq_of_rectEquivalent {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {p : MatrixProjection A ι} {q : MatrixProjection A κ}
    (h : RectEquivalent p q) : τ.projectionTrace p = τ.projectionTrace q := by
  obtain ⟨v, hp, hq⟩ := h
  rw [projectionTrace, projectionTrace, ← hp, ← hq, matrixTrace_mul_comm]

theorem projectionTrace_blockSum {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (p : MatrixProjection A ι) (q : MatrixProjection A κ) :
    τ.projectionTrace (projectionBlockSum p q) = τ.projectionTrace p + τ.projectionTrace q := by
  simp [projectionTrace, matrixTrace, Fintype.sum_sum_type, projectionBlockSum_coe,
    matrixBlockSum]

theorem projectionTrace_zero {ι : Type} [Fintype ι] [DecidableEq ι] :
    τ.projectionTrace (Projection.zero : MatrixProjection A ι) = 0 := by
  simp [projectionTrace, matrixTrace, Projection.zero]

theorem projectionTrace_one {ι : Type} [Fintype ι] [DecidableEq ι] :
    τ.projectionTrace (Projection.one : MatrixProjection A ι) =
      Fintype.card ι * τ.toLinearMap 1 := by
  simp [projectionTrace, matrixTrace, Projection.one]

theorem projectionTrace_unitMatrixProjection (e : A) (he : IsStarProjection e) :
    τ.projectionTrace (unitMatrixProjection e he) = τ.toLinearMap e := by
  simp [projectionTrace, matrixTrace, unitMatrixProjection]
  rfl

/-- The trace on the stable projection monoid. -/
def monoidTrace : StableProjectionMonoid A →+ ℂ where
  toFun := Quotient.lift (fun p : FiniteProjection A => τ.projectionTrace p.projection)
    fun _ _ h => τ.projectionTrace_eq_of_rectEquivalent h
  map_zero' := τ.projectionTrace_zero
  map_add' x y := Quotient.inductionOn₂ x y fun _ _ => τ.projectionTrace_blockSum _ _

@[simp] theorem monoidTrace_of (p : FiniteProjection A) :
    τ.monoidTrace (StableProjectionMonoid.of p) = τ.projectionTrace p.projection := rfl

/-- The trace on K₀. -/
def traceK0 : K0 A →+ ℂ := k0Universal τ.monoidTrace

@[simp] theorem traceK0_k0Projection (p : FiniteProjection A) :
    τ.traceK0 (k0Projection p) = τ.projectionTrace p.projection :=
  k0Universal_class τ.monoidTrace _

end TracialFunctional

end BC4lean.OperatorKTheory

/-! ## The canonical trace of `C⋆_r(Γ)` -/

namespace BC4lean

open OperatorKTheory

variable (Γ : Type u) [Group Γ]

/-- The vector state `T ↦ ⟪δ_e, T δ_e⟫` on bounded operators of `ℓ²(Γ)`. -/
def regularVectorState : (L2Group Γ →L[ℂ] L2Group Γ) →L[ℂ] ℂ :=
  (innerSL ℂ (L2Group.delta (1 : Γ))).comp
    (ContinuousLinearMap.apply ℂ (L2Group Γ) (L2Group.delta (1 : Γ)))

variable {Γ}

theorem regularVectorState_apply (T : L2Group Γ →L[ℂ] L2Group Γ) :
    regularVectorState Γ T = T (L2Group.delta 1) 1 := by
  simp [regularVectorState]

open scoped Classical in
theorem regularVectorState_regularOperator (g : Γ) :
    regularVectorState Γ (regularOperator g) = if g = 1 then 1 else 0 := by
  rw [regularVectorState_apply, regularOperator_delta, mul_one, L2Group.delta_apply]
  simp only [eq_comm]

/-- Two continuous functionals that agree on every `λ_g` agree on `C⋆_r(Γ)`. -/
theorem eq_on_reducedAlgebra (f f' : (L2Group Γ →L[ℂ] L2Group Γ) →L[ℂ] ℂ)
    (h : ∀ g : Γ, f (regularOperator g) = f' (regularOperator g))
    {T : L2Group Γ →L[ℂ] L2Group Γ} (hT : T ∈ reducedAlgebra Γ) : f T = f' T := by
  have hspan : Set.EqOn f f'
      (Submodule.span ℂ (Set.range (regularOperator (Γ := Γ))) : Set _) :=
    LinearMap.eqOn_span' (f := (f : (L2Group Γ →L[ℂ] L2Group Γ) →ₗ[ℂ] ℂ))
      (g := (f' : (L2Group Γ →L[ℂ] L2Group Γ) →ₗ[ℂ] ℂ)) (by rintro _ ⟨g, rfl⟩; exact h g)
  have hT' : T ∈ closure
      (Submodule.span ℂ (Set.range (regularOperator (Γ := Γ))) : Set _) := by
    rw [← reducedAlgebra_coe_eq_closure_span]
    exact hT
  exact hspan.closure f.continuous f'.continuous hT'

theorem regularVectorState_regularOperator_mul_comm (g h : Γ) :
    regularVectorState Γ (regularOperator g * regularOperator h) =
      regularVectorState Γ (regularOperator h * regularOperator g) := by
  classical
  rw [← regularOperator_mul, ← regularOperator_mul, regularVectorState_regularOperator,
    regularVectorState_regularOperator]
  simp only [mul_eq_one_comm]

theorem regularVectorState_regularOperator_mul_comm_of_mem (g : Γ)
    {T : L2Group Γ →L[ℂ] L2Group Γ} (hT : T ∈ reducedAlgebra Γ) :
    regularVectorState Γ (regularOperator g * T) = regularVectorState Γ (T * regularOperator g) := by
  have key := eq_on_reducedAlgebra
    ((regularVectorState Γ).comp
      (ContinuousLinearMap.mul ℂ (L2Group Γ →L[ℂ] L2Group Γ) (regularOperator g)))
    ((regularVectorState Γ).comp
      ((ContinuousLinearMap.mul ℂ (L2Group Γ →L[ℂ] L2Group Γ)).flip (regularOperator g)))
    (fun h => by simpa using regularVectorState_regularOperator_mul_comm g h) hT
  simpa using key

/-- The vector state at `δ_e` is tracial on `C⋆_r(Γ)`. -/
theorem regularVectorState_mul_comm {S T : L2Group Γ →L[ℂ] L2Group Γ}
    (hS : S ∈ reducedAlgebra Γ) (hT : T ∈ reducedAlgebra Γ) :
    regularVectorState Γ (S * T) = regularVectorState Γ (T * S) := by
  have key := eq_on_reducedAlgebra
    ((regularVectorState Γ).comp ((ContinuousLinearMap.mul ℂ (L2Group Γ →L[ℂ] L2Group Γ)).flip T))
    ((regularVectorState Γ).comp (ContinuousLinearMap.mul ℂ (L2Group Γ →L[ℂ] L2Group Γ) T))
    (fun g => by simpa using regularVectorState_regularOperator_mul_comm_of_mem g hT) hS
  simpa using key

/-- The vector state is positive: `τ(T⋆T) = ‖T δ_e‖²`. -/
theorem regularVectorState_star_mul_self (T : L2Group Γ →L[ℂ] L2Group Γ) :
    regularVectorState Γ (star T * T) = (‖T (L2Group.delta 1)‖ ^ 2 : ℝ) := by
  have h1 : regularVectorState Γ (star T * T) =
      inner ℂ (L2Group.delta (1 : Γ)) ((star T) (T (L2Group.delta 1))) := rfl
  rw [h1, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (T (L2Group.delta 1))]
  push_cast
  rfl

variable (Γ)

/-- The canonical trace `τ(a) = ⟪δ_e, a δ_e⟫` of `C⋆_r(Γ)`. -/
def reducedTrace : TracialFunctional (ReducedGroupCStar Γ) where
  toLinearMap :=
    { toFun := fun a => regularVectorState Γ a
      map_add' := fun a b => map_add (regularVectorState Γ) (a : L2Group Γ →L[ℂ] L2Group Γ) b
      map_smul' := fun z a => map_smul (regularVectorState Γ) z (a : L2Group Γ →L[ℂ] L2Group Γ) }
  map_mul_comm a b := regularVectorState_mul_comm a.property b.property

variable {Γ}

theorem reducedTrace_apply (a : ReducedGroupCStar Γ) :
    (reducedTrace Γ).toLinearMap a = (a : L2Group Γ →L[ℂ] L2Group Γ) (L2Group.delta 1) 1 :=
  regularVectorState_apply _

@[simp] theorem reducedTrace_one : (reducedTrace Γ).toLinearMap 1 = 1 := by
  rw [reducedTrace_apply]
  simp

open scoped Classical in
theorem reducedTrace_integratedToReduced_delta (g : Γ) :
    (reducedTrace Γ).toLinearMap (integratedToReduced (GroupAlgebra.delta g)) =
      if g = 1 then 1 else 0 := by
  change regularVectorState Γ (integratedRepresentation (GroupAlgebra.delta g)) = _
  rw [integratedRepresentation_delta, regularVectorState_regularOperator]


/-! ## Finite groups: the averaging projection -/

section Finite

variable (Γ)

/-- `λ_g` as an element of `C⋆_r(Γ)`. -/
def reducedDelta (g : Γ) : ReducedGroupCStar Γ := integratedToReduced (GroupAlgebra.delta g)

variable {Γ}

@[simp] theorem reducedDelta_coe (g : Γ) :
    (reducedDelta Γ g : L2Group Γ →L[ℂ] L2Group Γ) = regularOperator g := by
  simp [reducedDelta]

theorem reducedDelta_mul (g h : Γ) : reducedDelta Γ g * reducedDelta Γ h = reducedDelta Γ (g * h) :=
  Subtype.ext (by simp [regularOperator_mul])

theorem star_reducedDelta (g : Γ) : star (reducedDelta Γ g) = reducedDelta Γ g⁻¹ :=
  Subtype.ext (by simp)

open scoped Classical in
theorem reducedTrace_reducedDelta (g : Γ) :
    (reducedTrace Γ).toLinearMap (reducedDelta Γ g) = if g = 1 then 1 else 0 :=
  reducedTrace_integratedToReduced_delta g

variable (Γ) [Fintype Γ]

/-- The averaging element `p_Γ = |Γ|⁻¹ ∑_g λ_g` of `C⋆_r(Γ)`. -/
def averagingElement : ReducedGroupCStar Γ := (Fintype.card Γ : ℂ)⁻¹ • ∑ g, reducedDelta Γ g

variable {Γ}

theorem reducedDelta_mul_averagingElement (h : Γ) :
    reducedDelta Γ h * averagingElement Γ = averagingElement Γ := by
  rw [averagingElement, mul_smul_comm, Finset.mul_sum]
  simp only [reducedDelta_mul]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft h) (fun g => reducedDelta Γ g)

theorem averagingElement_isStarProjection : IsStarProjection (averagingElement Γ) := by
  have hcard : (Fintype.card Γ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  refine ⟨?_, ?_⟩
  · change averagingElement Γ * averagingElement Γ = averagingElement Γ
    have hsq : averagingElement Γ * averagingElement Γ =
        (Fintype.card Γ : ℂ)⁻¹ • ∑ g, (reducedDelta Γ g * averagingElement Γ) := by
      rw [← Finset.sum_mul, ← smul_mul_assoc]
      rfl
    rw [hsq]
    simp only [reducedDelta_mul_averagingElement, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  · change star (averagingElement Γ) = averagingElement Γ
    rw [averagingElement, star_smul, star_sum]
    simp only [star_reducedDelta, star_inv₀, star_natCast]
    congr 1
    exact Equiv.sum_comp (Equiv.inv Γ) (fun g => reducedDelta Γ g)

theorem reducedTrace_averagingElement :
    (reducedTrace Γ).toLinearMap (averagingElement Γ) = (Fintype.card Γ : ℂ)⁻¹ := by
  classical
  rw [averagingElement, map_smul, map_sum]
  simp [reducedTrace_reducedDelta]

end Finite


section K0

variable (Γ)

local instance traceSpectralOrder : PartialOrder (ReducedGroupCStar Γ) :=
  CStarAlgebra.spectralOrder _
local instance traceSpectralOrderedRing : StarOrderedRing (ReducedGroupCStar Γ) :=
  CStarAlgebra.spectralOrderedRing _

/-- The trace `τ_* : K₀(C⋆_r Γ) → ℝ`, the real part of the trace of a representing projection. -/
def reducedTraceK0 : ReducedK0 Γ →+ ℝ :=
  reducedK0Universal Γ (Complex.reAddGroupHom.comp (reducedTrace Γ).monoidTrace)

/-- The class of the unit of `C⋆_r(Γ)`. -/
def reducedUnitClass : ReducedK0 Γ :=
  reducedK0Class Γ (StableProjectionMonoid.of
    (FiniteProjection.ofProjection (Projection.one : MatrixProjection (ReducedGroupCStar Γ) Unit)))

theorem reducedTraceK0_class (p : FiniteProjection (ReducedGroupCStar Γ)) :
    reducedTraceK0 Γ (reducedK0Class Γ (StableProjectionMonoid.of p)) =
      ((reducedTrace Γ).projectionTrace p.projection).re :=
  k0Universal_class _ _

@[simp] theorem reducedTraceK0_unitClass : reducedTraceK0 Γ (reducedUnitClass Γ) = 1 := by
  rw [reducedUnitClass, reducedTraceK0_class]
  change ((reducedTrace Γ).projectionTrace
    (Projection.one : MatrixProjection (ReducedGroupCStar Γ) Unit)).re = 1
  rw [TracialFunctional.projectionTrace_one, reducedTrace_one]
  simp

/-- `τ_*(n [1]) = n`, so `[1]` has infinite order in `K₀(C⋆_r Γ)` for every group. -/
theorem addOrderOf_reducedUnitClass : addOrderOf (reducedUnitClass Γ) = 0 := by
  rw [addOrderOf_eq_zero_iff']
  intro n hn h
  have := congrArg (reducedTraceK0 Γ) h
  rw [map_nsmul, reducedTraceK0_unitClass, map_zero, nsmul_eq_mul, mul_one] at this
  exact hn.ne' (by exact_mod_cast this)

/-! ### Finite groups -/

variable [Fintype Γ]

/-- The class `[p_Γ]` of the averaging projection. -/
def averagingClass : ReducedK0 Γ :=
  reducedK0Class Γ (StableProjectionMonoid.of (FiniteProjection.ofProjection
    (unitMatrixProjection (averagingElement Γ) averagingElement_isStarProjection)))

/-- `τ_*[p_Γ] = 1/|Γ|`. -/
theorem reducedTraceK0_averagingClass :
    reducedTraceK0 Γ (averagingClass Γ) = (Fintype.card Γ : ℝ)⁻¹ := by
  rw [averagingClass, reducedTraceK0_class]
  change ((reducedTrace Γ).projectionTrace
    (unitMatrixProjection (averagingElement Γ) averagingElement_isStarProjection)).re = _
  rw [TracialFunctional.projectionTrace_unitMatrixProjection, reducedTrace_averagingElement]
  simp

/-- For `|Γ| > 1` the class `[p_Γ]` is not an integer multiple of `[1]`. -/
theorem averagingClass_not_mem_zmultiples (h : 1 < Fintype.card Γ) :
    averagingClass Γ ∉ AddSubgroup.zmultiples (reducedUnitClass Γ) := by
  rintro ⟨n, hn⟩
  have := congrArg (reducedTraceK0 Γ) hn
  rw [map_zsmul, reducedTraceK0_unitClass, reducedTraceK0_averagingClass, zsmul_one] at this
  have hc : (1 : ℝ) < Fintype.card Γ := by exact_mod_cast h
  have hpos : (0 : ℝ) < (n : ℝ) := by rw [this]; positivity
  have hlt : (n : ℝ) < 1 := by rw [this]; exact inv_lt_one_of_one_lt₀ hc
  have h0 : (0 : ℤ) < n := by exact_mod_cast hpos
  have h1 : n < (1 : ℤ) := by exact_mod_cast hlt
  omega

end K0

end BC4lean

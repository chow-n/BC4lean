import BC4lean.CircleProjection
import BC4lean.IntFourier
import BC4lean.ScalarOperatorK0
import BC4lean.OperatorK0Equivalence
import BC4lean.ReducedOperatorK0

/-! # `K₀(C*_r ℤ) ≃+ ℤ`, with `[1] ↦ 1`

Chain of three additive equivalences:
1. `k0Equiv fourierStarEquiv : K₀(C*_r ℤ) ≃+ K₀(C(𝕋))`, transported along the Fourier
   star-algebra equivalence;
2. `circleK0Equiv : K₀(C(𝕋)) ≃+ K₀(ℂ)`, induced by evaluation at `0`, with inverse induced by
   the constants. One composite is induced by `ev₀ ∘ incl = id`; the other sends `[P]` to
   `[P(0)]`, and `[P] = [P(0)]` by `CircleProjection.exists_partialIsometry_const`;
3. `k0ScalarEquiv : K₀(ℂ) ≃+ ℤ` (rank).

All three C⋆-algebras carry their spectral order, as `ReducedK0` does; for `C(𝕋)` and `ℂ` these
are local instances of this file. -/

noncomputable section
open scoped Matrix

namespace BC4lean
open OperatorKTheory

local instance (priority := high) circleOrder : PartialOrder C(AddCircle (1 : ℝ), ℂ) :=
  CStarAlgebra.spectralOrder _
local instance (priority := high) circleStarOrderedRing : StarOrderedRing C(AddCircle (1 : ℝ), ℂ) :=
  CStarAlgebra.spectralOrderedRing _
local instance (priority := high) scalarOrder : PartialOrder ℂ := CStarAlgebra.spectralOrder _
local instance (priority := high) scalarStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing _
local instance (priority := high) reducedOrder : PartialOrder (ReducedGroupCStar (Multiplicative ℤ)) :=
  CStarAlgebra.spectralOrder _
local instance (priority := high) reducedStarOrderedRing : StarOrderedRing (ReducedGroupCStar (Multiplicative ℤ)) :=
  CStarAlgebra.spectralOrderedRing _

/-- Evaluation at `0 ∈ 𝕋`. -/
def circleEv0 : C(AddCircle (1 : ℝ), ℂ) →⋆ₐ[ℂ] ℂ := ContinuousMap.evalStarAlgHom ℂ ℂ 0

/-- Constant functions. -/
def circleConst : ℂ →⋆ₐ[ℂ] C(AddCircle (1 : ℝ), ℂ) := StarAlgHom.ofId ℂ C(AddCircle (1 : ℝ), ℂ)

theorem circleEv0_comp_circleConst : circleEv0.comp circleConst = StarAlgHom.id ℂ ℂ := by
  ext z
  rfl

/-- `[P(0)] = [P]` for every finite projection `P` over `C(𝕋)`. -/
theorem equivalent_const_ev0 (p : FiniteProjection C(AddCircle (1 : ℝ), ℂ)) :
    FiniteProjection.Equivalent (FiniteProjection.map (circleConst.comp circleEv0) p) p := by
  obtain ⟨v, h₁, h₂⟩ := CircleProjection.exists_partialIsometry_const
    (projectionMatrix p.projection) (projectionMatrix_mul _) (projectionMatrix_star _)
  have e : vᴴᴴ = v := Matrix.conjTranspose_conjTranspose v
  exact ⟨vᴴ, (congrArg (vᴴ * ·) e).trans h₂, (congrArg (· * vᴴ) e).trans h₁⟩

/-- `K₀(C(𝕋)) ≃+ K₀(ℂ)`, induced by evaluation at `0`. -/
def circleK0Equiv : K0 C(AddCircle (1 : ℝ), ℂ) ≃+ K0 ℂ where
  toFun := k0Map circleEv0
  invFun := k0Map circleConst
  left_inv x := by
    have h : (k0Map circleConst).comp (k0Map circleEv0) = AddMonoidHom.id (K0 C(AddCircle (1 : ℝ), ℂ)) := by
      rw [← k0Map_comp]
      apply k0Hom_ext
      intro p
      rw [k0Map_projection, AddMonoidHom.id_apply]
      exact k0Projection_eq_of_equivalent (equivalent_const_ev0 p)
    exact DFunLike.congr_fun h x
  right_inv x := by
    have h : (k0Map circleEv0).comp (k0Map circleConst) = AddMonoidHom.id (K0 ℂ) := by
      rw [← k0Map_comp, circleEv0_comp_circleConst, k0Map_id]
    exact DFunLike.congr_fun h x
  map_add' := map_add _

/-- `K₀(C*_r ℤ) ≅ ℤ`. -/
def reducedK0IntEquiv : ReducedK0 (Multiplicative ℤ) ≃+ ℤ :=
  ((k0Equiv fourierStarEquiv).trans circleK0Equiv).trans k0ScalarEquiv

/-- The class `[1]` of the `1 × 1` unit projection of `C*_r ℤ`. -/
def reducedK0One : ReducedK0 (Multiplicative ℤ) :=
  k0Projection (FiniteProjection.ofProjection
    (Projection.one : MatrixProjection (ReducedGroupCStar (Multiplicative ℤ)) Unit))

theorem reducedK0IntEquiv_apply_projection (p : FiniteProjection (ReducedGroupCStar (Multiplicative ℤ))) :
    reducedK0IntEquiv (k0Projection p) =
      k0ScalarEquiv (k0Projection (FiniteProjection.map
        (circleEv0.comp fourierStarEquiv.toStarAlgHom) p)) := by
  change k0ScalarEquiv (k0Map circleEv0 (k0Map fourierStarEquiv.toStarAlgHom _)) = _
  rw [k0Map_projection, k0Map_projection, FiniteProjection.map_comp]

/-- Normalization: `[1] ↦ 1`. -/
theorem reducedK0IntEquiv_one : reducedK0IntEquiv reducedK0One = 1 := by
  rw [reducedK0One, reducedK0IntEquiv_apply_projection]
  have h : FiniteProjection.map (circleEv0.comp fourierStarEquiv.toStarAlgHom)
      (FiniteProjection.ofProjection
        (Projection.one : MatrixProjection (ReducedGroupCStar (Multiplicative ℤ)) Unit)) =
      FiniteProjection.ofProjection (Projection.one : MatrixProjection ℂ Unit) :=
    congrArg (fun q : MatrixProjection ℂ Unit => FiniteProjection.ofProjection q)
      (Projection.map_one _)
  rw [h]
  exact k0ScalarEquiv_one

end BC4lean

import BC4lean.CircleWinding
import BC4lean.IntFourier

/-! # The winding number on `K₁(C⋆_r ℤ)`, with `[λ(1)] ↦ 1`

`windingK1 = windingHom fourierStarEquiv` on `ReducedK1 (Multiplicative ℤ)`, with the spectral order
that `ReducedK1` uses: the winding number of the determinant of a matrix unitary, read on the circle
through the Fourier isomorphism `C⋆_r ℤ ≃⋆ₐ[ℂ] C(𝕋)`. `lambdaOneK1` is the class of the `1 × 1`
unitary `λ(1)`, and `windingK1 lambdaOneK1 = 1` because `λ(1) ↦ fourier 1`, which has winding number
one. Hence `windingK1` is surjective.
-/

noncomputable section
open Complex Real
open scoped CStarAlgebra

namespace BC4lean

open OperatorKTheory OperatorKTheory.CircleWinding

/-- The generator λ(1) of `C*_r ℤ`. -/
def lambdaOne : ReducedGroupCStar (Multiplicative ℤ) :=
  ⟨regularOperator (Multiplicative.ofAdd (1 : ℤ)), regularOperator_mem_reducedAlgebra _⟩

theorem lambdaOne_mem_unitary : lambdaOne ∈ unitary (ReducedGroupCStar (Multiplicative ℤ)) :=
  Unitary.mem_iff.2 ⟨Subtype.ext (regularOperator_unitary _).1, Subtype.ext (regularOperator_unitary _).2⟩

/-- The `1 × 1` matrix `[λ(1)]`. -/
def lambdaOneMatrix : CStarMatrix Unit Unit (ReducedGroupCStar (Multiplicative ℤ)) :=
  CStarMatrix.ofMatrix fun _ _ => lambdaOne

theorem lambdaOneMatrix_mem_unitary :
    lambdaOneMatrix ∈ unitary (CStarMatrix Unit Unit (ReducedGroupCStar (Multiplicative ℤ))) := by
  have h := Unitary.mem_iff.1 lambdaOne_mem_unitary
  rw [Unitary.mem_iff]
  constructor <;> refine CStarMatrix.ext_iff.1 fun i j => ?_ <;> cases i <;> cases j <;>
    rw [CStarMatrix.mul_apply, Fintype.sum_unique, CStarMatrix.one_apply_eq, CStarMatrix.star_apply]
  · exact h.1
  · exact h.2

/-- The winding number of the determinant, `K₁(C⋆_r ℤ) →+ ℤ`, through the Fourier isomorphism. -/
def windingK1 : ReducedK1 (Multiplicative ℤ) →+ ℤ := by
  letI := CStarAlgebra.spectralOrder (ReducedGroupCStar (Multiplicative ℤ))
  letI := CStarAlgebra.spectralOrderedRing (ReducedGroupCStar (Multiplicative ℤ))
  exact windingHom (fourierStarEquiv : ReducedGroupCStar (Multiplicative ℤ) →⋆ₐ[ℂ] C(AddCircle (1 : ℝ), ℂ))

/-- The K₁ class of λ(1) as a 1×1 unitary. -/
def lambdaOneK1 : ReducedK1 (Multiplicative ℤ) := by
  letI := CStarAlgebra.spectralOrder (ReducedGroupCStar (Multiplicative ℤ))
  letI := CStarAlgebra.spectralOrderedRing (ReducedGroupCStar (Multiplicative ℤ))
  exact K1.of
    { Index := Unit
      val := ⟨lambdaOneMatrix, lambdaOneMatrix_mem_unitary⟩ }  -- the 1×1 matrix unitary [λ(1)]

theorem circleDet_lambdaOneMatrix :
    circleDet (fourierStarEquiv : ReducedGroupCStar (Multiplicative ℤ) →⋆ₐ[ℂ] C(AddCircle (1 : ℝ), ℂ)) lambdaOneMatrix = fourier 1 := by
  rw [circleDet, Matrix.det_unique, circleMatrix_apply]
  exact fourierStarEquiv_lambda 1

theorem windingK1_lambdaOne : windingK1 lambdaOneK1 = 1 :=
  (winding_congr circleDet_lambdaOneMatrix _ (fourier_ne_zero 1)).trans (winding_fourier 1)

/-- The winding number is onto `ℤ`: `k • [λ(1)] ↦ k`. -/
theorem windingK1_surjective : Function.Surjective windingK1 := fun k =>
  ⟨k • lambdaOneK1, by rw [map_zsmul, windingK1_lambdaOne, smul_eq_mul, mul_one]⟩

end BC4lean

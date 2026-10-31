import BC4lean.IntWinding

/-! # `K₁(C⋆_r ℤ) ≃+ ℤ`

The winding number of the determinant, `windingK1`, is injective: `CircleWinding.windingHom_injective`
applies to the Fourier isomorphism `C⋆_r ℤ ≃⋆ₐ[ℂ] C(𝕋)`. With `windingK1_surjective` it is an
additive equivalence `reducedK1IntEquiv : ReducedK1 (Multiplicative ℤ) ≃+ ℤ`, sending `[λ(1)]` to `1`.
-/

noncomputable section

namespace BC4lean

open OperatorKTheory

/-- The winding number is injective on `K₁(C⋆_r ℤ)`. -/
theorem windingK1_injective : Function.Injective windingK1 := by
  let _ := CStarAlgebra.spectralOrder (ReducedGroupCStar (Multiplicative ℤ))
  let _ := CStarAlgebra.spectralOrderedRing (ReducedGroupCStar (Multiplicative ℤ))
  exact CircleWinding.windingHom_injective fourierStarEquiv

/-- `K₁(C⋆_r ℤ) ≅ ℤ` by the winding number of the determinant; `[λ(1)] ↦ 1`. -/
def reducedK1IntEquiv : ReducedK1 (Multiplicative ℤ) ≃+ ℤ :=
  AddEquiv.ofBijective windingK1 ⟨windingK1_injective, windingK1_surjective⟩

theorem reducedK1IntEquiv_lambdaOne : reducedK1IntEquiv lambdaOneK1 = 1 :=
  windingK1_lambdaOne

end BC4lean

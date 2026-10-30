import BC4lean.ScalarOperatorK0
import BC4lean.ScalarOperatorK1
import BC4lean.OperatorKUnitalAgreement

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Nonunital operator K-groups of the scalars

The unitization-kernel groups of `ℂ` agree with the unital ones, so
`K₀^op(ℂ) ≃+ ℤ` and `K₁^op(ℂ) = 0`. The agreement equivalences use the
spectral order on `ℂ`, at which the generic scalar results are instantiated.
-/

noncomputable section
namespace BC4lean.OperatorKTheory

local instance scalarNonunitalSpectralOrder : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
local instance scalarNonunitalSpectralOrderedRing : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ

/-- `K₀^op(ℂ) ≃+ ℤ`. -/
def operatorK0ScalarEquiv : OperatorK0 ℂ ≃+ ℤ :=
  (operatorK0UnitalEquiv ℂ).trans k0ScalarEquiv

/-- Every element of `K₁^op(ℂ)` is zero. -/
theorem operatorK1Scalar_eq_zero (x : OperatorK1 ℂ) : x = 0 := by
  apply (operatorK1UnitalEquiv ℂ).injective
  rw [map_zero]
  exact k1Scalar_eq_zero _

instance : Subsingleton (OperatorK1 ℂ) :=
  ⟨fun x y => (operatorK1Scalar_eq_zero x).trans (operatorK1Scalar_eq_zero y).symm⟩

end BC4lean.OperatorKTheory

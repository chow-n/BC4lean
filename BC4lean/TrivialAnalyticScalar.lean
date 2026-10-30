import BC4lean.ScalarOperatorK0
import BC4lean.ScalarOperatorK1
import BC4lean.TrivialAnalyticCalibration

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Reduced K-groups of a one-element group

Composing the trivial-group calibration with the scalar computations gives
`K₀(C*_r(Γ)) ≃+ ℤ`, sending the image of `[1]` to `1`, and `K₁(C*_r(Γ)) = 0`
for every group `Γ` with one element. The calibration is stated under
`ComplexOrder`, at which the generic scalar results are instantiated. Assembly
is not identified here.
-/

noncomputable section
open scoped ComplexOrder
universe u
namespace BC4lean.Chapter8Examples
open OperatorKTheory

variable (Γ : Type u) [Group Γ] [Subsingleton Γ]

/-- `K₀(C*_r(Γ)) ≃+ ℤ` for a group with one element. -/
def trivialReducedK0Equiv : ReducedK0 Γ ≃+ ℤ :=
  (trivialAnalyticK0Equiv Γ).symm.trans k0ScalarEquiv

/-- The image of `[1]` under the calibration goes to `1`. -/
theorem trivialReducedK0Equiv_one :
    trivialReducedK0Equiv Γ (trivialAnalyticK0Equiv Γ k0ScalarOne) = 1 := by
  change k0ScalarEquiv ((trivialAnalyticK0Equiv Γ).symm (trivialAnalyticK0Equiv Γ k0ScalarOne)) = 1
  rw [AddEquiv.symm_apply_apply]
  exact k0ScalarEquiv_one

/-- Every element of `K₁(C*_r(Γ))` is zero for a group with one element. -/
theorem trivialReducedK1_eq_zero (x : ReducedK1 Γ) : x = 0 := by
  apply (trivialAnalyticK1Equiv Γ).symm.injective
  rw [map_zero]
  exact k1Scalar_eq_zero _

end BC4lean.Chapter8Examples

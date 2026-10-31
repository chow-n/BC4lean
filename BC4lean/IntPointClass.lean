import BC4lean.CosetAssemblyUnit
import BC4lean.IntegerGroup
import BC4lean.IntK0

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The point class of the integers, and even assembly onto `K₀(C*_r ℤ)`

For every countable discrete group `Γ : Type`, the free orbit `Γ = Γ ⧸ ⊥` assembles to the class
of the unit projection, `μ₀[Γ] = [1]` (`CosetAssemblyUnit.reducedAssemblyHom_cosetUnitClass_bot`).
For the integers, as `Multiplicative ℤ`, call this class `pointClass`. Then
`reducedK0IntEquiv (μ₀ pointClass) = 1` (`reducedK0IntEquiv_assembly_pointClass`), and since
`reducedK0IntEquiv : ReducedK0 (Multiplicative ℤ) ≃+ ℤ`, even assembly for the integers is
surjective (`reducedAssemblyHom_even_surjective`). Injectivity, and the odd half, are not
addressed here.

Under the line model `ℝ` the point class is the cycle `(ℓ²ℤ, f ↦ f|ℤ, 0)` of `C₀(ℝ)`: the orbit map
`ℤ → ℝ` and the inclusion are equivariantly homotopic by the straight line. That identification is
not formalized here, and nothing below uses it. -/

noncomputable section

namespace BC4lean.Chapter8Examples.IntPointClass
open ProperActions KKTheory OperatorKTheory Chapter8Examples.CosetAssemblyUnit

/-- The even point class of the integers: the unit cycle of the free orbit `ℤ` (`ℓ²ℤ`,
translations, `C₀(ℤ)` acting by multiplication, operator `0`), pushed into the canonical model
along the orbit map of a chosen point (`cosetUnitClass (Multiplicative ℤ) ⊥`). The statements below
are about its assembly value, which does not depend on that choice. -/
def pointClass : TopologicalKHomology.topologicalGroup false (Multiplicative ℤ) :=
  cosetUnitClass (Multiplicative ℤ) (⊥ : Subgroup (Multiplicative ℤ))

/-- `μ₀(pointClass) = [1]` in `K₀(C*_r ℤ)`. -/
theorem reducedAssemblyHom_pointClass :
    Assembly.reducedAssemblyHom (Multiplicative ℤ) false pointClass = reducedK0One :=
  reducedAssemblyHom_cosetUnitClass_bot (Multiplicative ℤ)

/-- Even assembly sends the point class to the generator: `reducedK0IntEquiv (μ₀ pointClass) = 1`. -/
theorem reducedK0IntEquiv_assembly_pointClass :
    reducedK0IntEquiv (Assembly.reducedAssemblyHom (Multiplicative ℤ) false pointClass) = 1 := by
  rw [reducedAssemblyHom_pointClass, reducedK0IntEquiv_one]

/-- Even assembly for `ℤ` followed by `reducedK0IntEquiv`, as one additive map. -/
def evenDetect : TopologicalKHomology.topologicalGroup false (Multiplicative ℤ) →+ ℤ :=
  reducedK0IntEquiv.toAddMonoidHom.comp (Assembly.reducedAssemblyEvenHom (Multiplicative ℤ))

theorem evenDetect_apply (x : TopologicalKHomology.topologicalGroup false (Multiplicative ℤ)) :
    evenDetect x = reducedK0IntEquiv (Assembly.reducedAssemblyHom (Multiplicative ℤ) false x) := rfl

/-- `μ₀(n • pointClass) = n • [1]` is read by `reducedK0IntEquiv` as `n`. -/
theorem reducedK0IntEquiv_assembly_zsmul_pointClass (n : ℤ) :
    reducedK0IntEquiv (Assembly.reducedAssemblyHom (Multiplicative ℤ) false (n • pointClass)) = n := by
  rw [← evenDetect_apply, map_zsmul, evenDetect_apply, reducedK0IntEquiv_assembly_pointClass,
    smul_eq_mul, mul_one]

/-- **Even assembly for `ℤ` is surjective**: every `y ∈ K₀(C*_r ℤ)` is
`μ₀((reducedK0IntEquiv y) • pointClass)`. -/
theorem reducedAssemblyHom_zsmul_pointClass (y : ReducedK0 (Multiplicative ℤ)) :
    Assembly.reducedAssemblyHom (Multiplicative ℤ) false (reducedK0IntEquiv y • pointClass) = y :=
  reducedK0IntEquiv.injective (reducedK0IntEquiv_assembly_zsmul_pointClass _)

theorem reducedAssemblyHom_even_surjective :
    Function.Surjective (Assembly.reducedAssemblyHom (Multiplicative ℤ) false) :=
  fun y => ⟨_, reducedAssemblyHom_zsmul_pointClass y⟩

/-- `pointClass` has infinite order. -/
theorem zsmul_pointClass_eq_zero_iff (n : ℤ) : n • pointClass = 0 ↔ n = 0 := by
  constructor
  · intro h
    have := reducedK0IntEquiv_assembly_zsmul_pointClass n
    rw [h, ← evenDetect_apply, map_zero] at this
    exact this.symm
  · rintro rfl
    exact zero_zsmul pointClass

/-- `pointClass` is primitive: if it is a multiple `n • x`, then `n = ±1`. Hence, if the
topological group is cyclic (not proved here), `pointClass` generates it. -/
theorem pointClass_primitive (n : ℤ) (x : TopologicalKHomology.topologicalGroup false (Multiplicative ℤ))
    (h : pointClass = n • x) : IsUnit n := by
  have h1 := reducedK0IntEquiv_assembly_pointClass
  rw [h, ← evenDetect_apply, map_zsmul, evenDetect_apply, smul_eq_mul] at h1
  exact IsUnit.of_mul_eq_one _ h1

end BC4lean.Chapter8Examples.IntPointClass

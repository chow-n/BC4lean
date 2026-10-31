import BC4lean.ReducedGroupCStar
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Function.Holder

/-! # The reduced group C⋆-algebra of the integers is `C(𝕋)`

The Fourier basis identifies `ℓ²(ℤ)` with `L²` of the circle `AddCircle 1` (Haar probability
measure). Under this unitary the regular operator `λ(n)` becomes multiplication by the character
`fourier n`. Multiplication by continuous functions is an injective star homomorphism
`C(𝕋) → B(L²(𝕋))`, hence isometric. Its range is closed, and it is the smallest closed star
subalgebra containing the characters, because their span is dense in `C(𝕋)`. Transported back
to `ℓ²(ℤ)`, that range is the reduced group C⋆-algebra.

Main declarations:
* `circleMulOp f`: multiplication by `f : C(𝕋, ℂ)` on `L²(𝕋)`, with
  `norm_circleMulOp : ‖circleMulOp f‖ = ‖f‖`;
* `fourierUnitary : ℓ²(ℤ) ≃ₗᵢ[ℂ] L²(𝕋)`, sending `δ_n` to `fourierLp 2 n`;
* `fourierStarEquiv : ReducedGroupCStar (Multiplicative ℤ) ≃⋆ₐ[ℂ] C(AddCircle 1, ℂ)`, and
  `fourierStarEquiv_lambda : λ(n) ↦ fourier n`.

Here `𝕋` is `AddCircle (1 : ℝ)`. The instance `Fact ((0 : ℝ) < 1)` that `fourierBasis` and
`haarAddCircle` need is Mathlib's.
-/

noncomputable section

open MeasureTheory AddCircle ENNReal

namespace BC4lean

/-- `L²` of the circle of length one, for the Haar probability measure. -/
abbrev L2Circle := Lp ℂ 2 (haarAddCircle (T := 1))

/-! ### Multiplication operators -/

/-- Multiplication by a continuous function, as a bounded operator on `L²(𝕋)`. -/
def circleMulOp (f : C(AddCircle (1 : ℝ), ℂ)) : L2Circle →L[ℂ] L2Circle :=
  LinearMap.mkContinuous
    { toFun := fun g => ((ContinuousMap.toLp ∞ (haarAddCircle (T := 1)) ℂ f : Lp ℂ ∞ (haarAddCircle (T := 1))) • g : L2Circle)
      map_add' := fun g₁ g₂ => Lp.add_smul _ g₁ g₂
      map_smul' := fun c g => (Lp.smul_comm c _ g).symm }
    ‖(ContinuousMap.toLp ∞ (haarAddCircle (T := 1)) ℂ f : Lp ℂ ∞ (haarAddCircle (T := 1)))‖ (fun g => Lp.norm_smul_le _ g)

theorem circleMulOp_ae (f : C(AddCircle (1 : ℝ), ℂ)) (g : L2Circle) :
    (circleMulOp f g : AddCircle (1 : ℝ) → ℂ) =ᵐ[(haarAddCircle (T := 1))] fun x => f x * g x := by
  change (((ContinuousMap.toLp ∞ (haarAddCircle (T := 1)) ℂ f : Lp ℂ ∞ (haarAddCircle (T := 1))) • g : L2Circle) : AddCircle (1 : ℝ) → ℂ)
    =ᵐ[(haarAddCircle (T := 1))] _
  filter_upwards [Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
      (ContinuousMap.toLp ∞ (haarAddCircle (T := 1)) ℂ f : Lp ℂ ∞ (haarAddCircle (T := 1))) g,
    ContinuousMap.coeFn_toLp (p := ∞) (μ := (haarAddCircle (T := 1))) (𝕜 := ℂ) f] with x hx hf
  rw [hx, Pi.smul_apply', hf, smul_eq_mul]

theorem circleMulOp_one : circleMulOp 1 = 1 := by
  ext1 g
  apply Lp.ext
  filter_upwards [circleMulOp_ae 1 g] with x hx
  simp [hx]

theorem circleMulOp_mul (f₁ f₂ : C(AddCircle (1 : ℝ), ℂ)) : circleMulOp (f₁ * f₂) = circleMulOp f₁ * circleMulOp f₂ := by
  ext1 g
  apply Lp.ext
  filter_upwards [circleMulOp_ae (f₁ * f₂) g, circleMulOp_ae f₁ (circleMulOp f₂ g), circleMulOp_ae f₂ g]
    with x h₁₂ h₁ h₂
  simp [h₁₂, h₁, h₂, mul_assoc]

theorem circleMulOp_add (f₁ f₂ : C(AddCircle (1 : ℝ), ℂ)) : circleMulOp (f₁ + f₂) = circleMulOp f₁ + circleMulOp f₂ := by
  ext1 g
  apply Lp.ext
  filter_upwards [circleMulOp_ae (f₁ + f₂) g, circleMulOp_ae f₁ g, circleMulOp_ae f₂ g,
    Lp.coeFn_add (circleMulOp f₁ g) (circleMulOp f₂ g)] with x h₁₂ h₁ h₂ hs
  rw [h₁₂, show (circleMulOp f₁ + circleMulOp f₂) g = circleMulOp f₁ g + circleMulOp f₂ g from rfl, hs, Pi.add_apply,
    h₁, h₂, ContinuousMap.add_apply, add_mul]

theorem circleMulOp_algebraMap (c : ℂ) :
    circleMulOp (algebraMap ℂ C(AddCircle (1 : ℝ), ℂ) c) = algebraMap ℂ (L2Circle →L[ℂ] L2Circle) c := by
  ext1 g
  apply Lp.ext
  filter_upwards [circleMulOp_ae (algebraMap ℂ C(AddCircle (1 : ℝ), ℂ) c) g, Lp.coeFn_smul c g]
    with x h hc
  rw [h]
  simp [Algebra.algebraMap_eq_smul_one, hc]

theorem circleMulOp_star (f : C(AddCircle (1 : ℝ), ℂ)) : circleMulOp (star f) = star (circleMulOp f) := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
  intro g h
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [circleMulOp_ae (star f) g, circleMulOp_ae f h] with x hg hh
  simp only [hg, hh, RCLike.inner_apply, ContinuousMap.star_apply, map_mul, RCLike.star_def,
    RCLike.conj_conj]
  ring

/-- Multiplication operators as a star algebra homomorphism. -/
def circleMulStarHom : C(AddCircle (1 : ℝ), ℂ) →⋆ₐ[ℂ] (L2Circle →L[ℂ] L2Circle) where
  toFun := circleMulOp
  map_one' := circleMulOp_one
  map_mul' := circleMulOp_mul
  map_zero' := by simpa using circleMulOp_algebraMap 0
  map_add' := circleMulOp_add
  commutes' := circleMulOp_algebraMap
  map_star' := circleMulOp_star

@[simp] theorem circleMulStarHom_apply (f : C(AddCircle (1 : ℝ), ℂ)) : circleMulStarHom f = circleMulOp f := rfl

/-- Multiplying the constant function `1` recovers `f` as an element of `L²`. -/
theorem circleMulOp_toLp_one (f : C(AddCircle (1 : ℝ), ℂ)) :
    circleMulOp f (ContinuousMap.toLp 2 (haarAddCircle (T := 1)) ℂ 1) = ContinuousMap.toLp 2 (haarAddCircle (T := 1)) ℂ f := by
  apply Lp.ext
  filter_upwards [circleMulOp_ae f (ContinuousMap.toLp 2 (haarAddCircle (T := 1)) ℂ 1),
    ContinuousMap.coeFn_toLp (p := 2) (μ := (haarAddCircle (T := 1))) (𝕜 := ℂ) (1 : C(AddCircle (1 : ℝ), ℂ)),
    ContinuousMap.coeFn_toLp (p := 2) (μ := (haarAddCircle (T := 1))) (𝕜 := ℂ) f] with x h h₁ hf
  rw [h, h₁, hf, ContinuousMap.one_apply, mul_one]

theorem circleMulStarHom_injective : Function.Injective circleMulStarHom := by
  intro f₁ f₂ h
  apply ContinuousMap.toLp_injective (p := 2) (haarAddCircle (T := 1)) (𝕜 := ℂ)
  calc ContinuousMap.toLp 2 (haarAddCircle (T := 1)) ℂ f₁ = circleMulOp f₁ (ContinuousMap.toLp 2 (haarAddCircle (T := 1)) ℂ 1) :=
        (circleMulOp_toLp_one f₁).symm
    _ = circleMulOp f₂ (ContinuousMap.toLp 2 (haarAddCircle (T := 1)) ℂ 1) :=
        congrArg (fun T : L2Circle →L[ℂ] L2Circle => T (ContinuousMap.toLp 2 (haarAddCircle (T := 1)) ℂ 1)) h
    _ = ContinuousMap.toLp 2 (haarAddCircle (T := 1)) ℂ f₂ := circleMulOp_toLp_one f₂

/-- Multiplication operators are isometric for the supremum norm. -/
theorem norm_circleMulOp (f : C(AddCircle (1 : ℝ), ℂ)) : ‖circleMulOp f‖ = ‖f‖ :=
  NonUnitalStarAlgHom.norm_map circleMulStarHom circleMulStarHom_injective f

/-- Multiplication by `fourier n` shifts the Fourier basis by `n`. -/
theorem circleMulOp_fourierLp (n m : ℤ) : circleMulOp (fourier n) (fourierLp 2 m) = fourierLp 2 (n + m) := by
  apply Lp.ext
  filter_upwards [circleMulOp_ae (fourier n) (fourierLp 2 m), coeFn_fourierLp (T := 1) 2 m,
    coeFn_fourierLp (T := 1) 2 (n + m)] with x h hm hnm
  rw [h, hm, hnm, fourier_add]

/-! ### The Fourier unitary -/

/-- The Fourier unitary `ℓ²(ℤ) → L²(𝕋)`, the inverse of the Fourier-coefficient map.
It uses that `L2Group (Multiplicative ℤ)` is definitionally Mathlib's `ℓ²(ℤ, ℂ)`. -/
def fourierUnitary : L2Group (Multiplicative ℤ) ≃ₗᵢ[ℂ] L2Circle :=
  (fourierBasis (T := 1)).repr.symm

theorem fourierUnitary_delta (n : ℤ) :
    fourierUnitary (L2Group.delta (Multiplicative.ofAdd n)) = fourierLp 2 n := by
  classical
  rw [← coe_fourierBasis, ← HilbertBasis.repr_symm_single]
  change fourierUnitary _ = fourierUnitary _
  congr 1
  ext m
  change _ = (lp.single 2 n (1 : ℂ) : lp (fun _ : ℤ => ℂ) 2) (Multiplicative.toAdd m)
  rw [L2Group.delta_apply, lp.single_apply, Pi.single_apply]
  by_cases hm : m = Multiplicative.ofAdd n
  · simp [hm]
  · have hm' : Multiplicative.toAdd m ≠ n := fun h => hm (by rw [← h]; rfl)
    simp [hm, hm']

/-- Multiplication operators transported to `ℓ²(ℤ)`. -/
def laurentStarHom : C(AddCircle (1 : ℝ), ℂ) →⋆ₐ[ℂ] (L2Group (Multiplicative ℤ) →L[ℂ] L2Group (Multiplicative ℤ)) :=
  (fourierUnitary.symm.conjStarAlgEquiv : (L2Circle →L[ℂ] L2Circle) →⋆ₐ[ℂ] _).comp circleMulStarHom

theorem laurentStarHom_apply (f : C(AddCircle (1 : ℝ), ℂ)) (ξ : L2Group (Multiplicative ℤ)) :
    laurentStarHom f ξ = fourierUnitary.symm (circleMulOp f (fourierUnitary ξ)) := rfl

theorem laurentStarHom_injective : Function.Injective laurentStarHom := fun _ _ h =>
  circleMulStarHom_injective ((LinearIsometryEquiv.conjStarAlgEquiv fourierUnitary.symm).injective h)

theorem laurentStarHom_isometry : Isometry laurentStarHom :=
  NonUnitalStarAlgHom.isometry laurentStarHom laurentStarHom_injective

/-- The character `fourier n` goes to the regular operator `λ(n)`. -/
theorem laurentStarHom_fourier (n : ℤ) :
    laurentStarHom (fourier n) = regularOperator (Multiplicative.ofAdd n) := by
  apply ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.2 L2Group.delta_dense_span)
  rintro _ ⟨g, rfl⟩
  rw [laurentStarHom_apply, regularOperator_delta, ← ofAdd_toAdd g, fourierUnitary_delta,
    circleMulOp_fourierLp, ← fourierUnitary_delta, LinearIsometryEquiv.symm_apply_apply, ← ofAdd_add]

theorem laurentStarHom_mem (f : C(AddCircle (1 : ℝ), ℂ)) : laurentStarHom f ∈ reducedAlgebra (Multiplicative ℤ) := by
  let S : Submodule ℂ C(AddCircle (1 : ℝ), ℂ) :=
    (reducedAlgebra (Multiplicative ℤ)).toSubalgebra.toSubmodule.comap laurentStarHom.toAlgHom.toLinearMap
  have hS : IsClosed (S : Set C(AddCircle (1 : ℝ), ℂ)) :=
    reducedAlgebra_isClosed.preimage laurentStarHom_isometry.continuous
  have hspan : Submodule.span ℂ (Set.range (fourier (T := 1))) ≤ S := by
    rw [Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    change laurentStarHom (fourier n) ∈ reducedAlgebra (Multiplicative ℤ)
    rw [laurentStarHom_fourier]
    exact regularOperator_mem_reducedAlgebra _
  have := Submodule.topologicalClosure_minimal _ hspan hS
  rw [span_fourier_closure_eq_top] at this
  exact this Submodule.mem_top

theorem reducedAlgebra_le_range : reducedAlgebra (Multiplicative ℤ) ≤ laurentStarHom.range := by
  apply reducedAlgebra_minimal
  · exact laurentStarHom_isometry.isClosedEmbedding.isClosed_range
  · intro g
    refine ⟨fourier (Multiplicative.toAdd g), ?_⟩
    change laurentStarHom _ = _
    rw [laurentStarHom_fourier, ofAdd_toAdd]

/-- `C(𝕋) ≃ C⋆_r(ℤ)`, `f ↦ F⁻¹ M_f F`. -/
def fourierStarEquivSymm : C(AddCircle (1 : ℝ), ℂ) ≃⋆ₐ[ℂ] ReducedGroupCStar (Multiplicative ℤ) :=
  StarAlgEquiv.ofBijective (laurentStarHom.codRestrict (reducedAlgebra (Multiplicative ℤ)) laurentStarHom_mem)
    ⟨fun f₁ f₂ h => laurentStarHom_injective (congrArg Subtype.val h),
      fun T => by
        obtain ⟨f, hf⟩ := reducedAlgebra_le_range T.2
        exact ⟨f, Subtype.ext hf⟩⟩

/-- The Fourier isomorphism `C⋆_r(ℤ) ≃⋆ₐ[ℂ] C(𝕋)`. -/
def fourierStarEquiv : ReducedGroupCStar (Multiplicative ℤ) ≃⋆ₐ[ℂ] C(AddCircle (1 : ℝ), ℂ) :=
  fourierStarEquivSymm.symm

theorem fourierStarEquiv_symm_apply (f : C(AddCircle (1 : ℝ), ℂ)) :
    (fourierStarEquiv.symm f : L2Group (Multiplicative ℤ) →L[ℂ] L2Group (Multiplicative ℤ)) = laurentStarHom f := rfl

/-- `λ(n) ↦ fourier n`; for `n = 1` the identity function of the circle. -/
theorem fourierStarEquiv_lambda (n : ℤ) :
    fourierStarEquiv ⟨regularOperator (Multiplicative.ofAdd n), regularOperator_mem_reducedAlgebra _⟩
      = fourier n := by
  rw [fourierStarEquiv, StarAlgEquiv.symm_apply_eq]
  exact Subtype.ext (laurentStarHom_fourier n).symm

/-- `λ(1)` goes to the identity function of the circle, `x ↦ x ∈ 𝕋 ⊆ ℂ`. -/
theorem fourierStarEquiv_lambda_one (x : AddCircle (1 : ℝ)) :
    fourierStarEquiv ⟨regularOperator (Multiplicative.ofAdd 1), regularOperator_mem_reducedAlgebra _⟩ x
      = toCircle x := by
  rw [fourierStarEquiv_lambda, fourier_one]

/-- The Fourier isomorphism is isometric. -/
theorem norm_fourierStarEquiv (a : ReducedGroupCStar (Multiplicative ℤ)) : ‖fourierStarEquiv a‖ = ‖a‖ :=
  StarAlgEquiv.norm_map _ a

end BC4lean

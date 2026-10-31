import BC4lean.ReducedCrossedScalarProduct

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The scalar reduced crossed product of a finite group

`ScalarCrossed Γ` is the reduced crossed product `ℂ ⋊_r Γ` of the scalars by the trivial action,
a closed star subalgebra of the adjointable operators on `ℓ²Γ = ReducedCrossedHilbertModule ℂ Γ`.
`scalarRegular Γ g` is the regular unitary `λ_g` in it, and `scalarTrace` is the canonical trace
`τ(a) = ⟪δ_e, a δ_e⟫`, defined for every group (`scalarTrace_eq_inner`), with `τ(λ_g) = [g = e]`.

For a finite group:
* `scalarCrossed_fourier`: Fourier inversion `a = ∑_g τ(a λ_g⋆) λ_g`. The operators of the
  crossed product lie in the linear span of the `λ_g`, because that span is a finite-dimensional,
  hence closed, star subalgebra containing every generator (`reducedCrossedAlgebra_minimal`);
* `span_scalarRegular`, `scalarRegularBasis`: the `λ_g` form a basis with coordinates
  `τ(a λ_g⋆)`, so the crossed product has dimension `|Γ|`;
* `scalarTrace_mul_comm`, `scalarTrace_star`: `τ` is tracial and star-preserving;
* `scalarTrace_star_mul`: Plancherel, `τ(a⋆ b) = ∑_g conj(τ(a λ_g⋆)) τ(b λ_g⋆)`, so `τ` is
  positive and faithful (`scalarTrace_star_mul_self_eq_zero_iff`);
* `sum_scalarTrace_regular_mul_mul_star`: `∑_{g,h} τ(λ_g b λ_h⋆) λ_g⋆ λ_h = |Γ| b`, the identity
  behind the isometry of Julg's inverse on the crossed-product side.
-/

noncomputable section
namespace BC4lean.KKTheory
open scoped InnerProductSpace ComplexOrder

variable {Γ : Type*} [Group Γ]

/-- Trivial scalar coefficients act on the regular module by scalar multiplication. -/
theorem reducedCrossedCoefficient_trivial (z : ℂ) :
    reducedCrossedCoefficient (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) z = z • 1 := by
  apply reducedCrossedRegular_ext
  intro x
  rw [reducedCrossedCoefficient_mk, AdjointableMap.coe_smul_apply, AdjointableMap.one_apply,
    ← map_smul]
  congr 1
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, hx, hy, smul_add]
  | single i b =>
    rw [reducedCrossedFiniteDiagonal_single, Finsupp.smul_single]
    congr 1

/-- A trivial scalar generator is a scalar multiple of the regular translation. -/
theorem reducedCrossedGenerator_trivial (z : ℂ) (g : Γ) :
    reducedCrossedGenerator (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) z g =
      z • reducedCrossedRegular g := by
  rw [reducedCrossedGenerator, reducedCrossedCoefficient_trivial, smul_mul_assoc, one_mul]

variable (Γ) in
/-- The scalar reduced crossed product `ℂ ⋊_r Γ`. -/
abbrev ScalarCrossed := ReducedCrossedProduct (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)

variable (Γ) in
/-- The regular unitary `λ_g` as an element of the scalar reduced crossed product. -/
def scalarRegular (g : Γ) : ScalarCrossed Γ :=
  ⟨reducedCrossedRegular g, by
    simpa only [reducedCrossedGenerator_trivial, one_smul] using
      reducedCrossedGenerator_mem (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) 1 g⟩

@[simp] theorem scalarRegular_coe (g : Γ) :
    (scalarRegular Γ g : AdjointableMap ℂ (ReducedCrossedHilbertModule ℂ Γ)
      (ReducedCrossedHilbertModule ℂ Γ)) = reducedCrossedRegular g := rfl

theorem scalarRegular_mul (g h : Γ) : scalarRegular Γ g * scalarRegular Γ h = scalarRegular Γ (g * h) :=
  Subtype.ext (reducedCrossedRegular_mul g h).symm

theorem star_scalarRegular (g : Γ) : star (scalarRegular Γ g) = scalarRegular Γ g⁻¹ :=
  Subtype.ext (reducedCrossedRegular_star g)

/-- `λ_e` is a left unit of the scalar crossed product. -/
@[simp] theorem scalarRegular_one_mul (a : ScalarCrossed Γ) : scalarRegular Γ 1 * a = a :=
  Subtype.ext (by
    change reducedCrossedRegular (B := ℂ) (1 : Γ) * (a : AdjointableMap ℂ (ReducedCrossedHilbertModule ℂ Γ)
      (ReducedCrossedHilbertModule ℂ Γ)) = a
    rw [reducedCrossedRegular_one, one_mul])

/-- `λ_e` is a right unit of the scalar crossed product. -/
@[simp] theorem mul_scalarRegular_one (a : ScalarCrossed Γ) : a * scalarRegular Γ 1 = a :=
  Subtype.ext (by
    change (a : AdjointableMap ℂ (ReducedCrossedHilbertModule ℂ Γ)
      (ReducedCrossedHilbertModule ℂ Γ)) * reducedCrossedRegular (B := ℂ) (1 : Γ) = a
    rw [reducedCrossedRegular_one, mul_one])

variable (Γ) in
/-- The delta vector `δ_e ∈ ℓ²Γ` at the identity. -/
def regularDeltaOne : ReducedCrossedHilbertModule ℂ Γ :=
  reducedCrossedInclusion 1 (MulOpposite.op 1)

/-- The vector state at `δ_e` on operators of `ℓ²Γ`, read off as the identity coordinate of `T δ_e`. -/
def regularTrace :
    AdjointableMap ℂ (ReducedCrossedHilbertModule ℂ Γ) (ReducedCrossedHilbertModule ℂ Γ) →ₗ[ℂ] ℂ where
  toFun T := MulOpposite.unop (reducedCrossedEvaluation 1 (T (regularDeltaOne Γ)))
  map_add' S T := by
    rw [AdjointableMap.coe_add_apply, map_add, MulOpposite.unop_add]
  map_smul' c T := by
    rw [AdjointableMap.coe_smul_apply, map_smul, MulOpposite.unop_smul, RingHom.id_apply]

theorem regularTrace_apply
    (T : AdjointableMap ℂ (ReducedCrossedHilbertModule ℂ Γ) (ReducedCrossedHilbertModule ℂ Γ)) :
    regularTrace T = MulOpposite.unop (reducedCrossedEvaluation 1 (T (regularDeltaOne Γ))) := rfl

/-- The vector state is `T ↦ ⟪δ_e, T δ_e⟫`. -/
theorem regularTrace_eq_inner
    (T : AdjointableMap ℂ (ReducedCrossedHilbertModule ℂ Γ) (ReducedCrossedHilbertModule ℂ Γ)) :
    regularTrace T = MulOpposite.unop ⟪regularDeltaOne Γ, T (regularDeltaOne Γ)⟫_(ℂᵐᵒᵖ) := by
  rw [regularDeltaOne, (reducedCrossedInclusion (B := ℂ) (Γ := Γ) 1).adjoint_identity,
    regularTrace_apply, regularDeltaOne]
  change _ = MulOpposite.unop (reducedCrossedEvaluation 1 (T (reducedCrossedInclusion 1
    (MulOpposite.op 1))) * star (MulOpposite.op (1 : ℂ)))
  rw [MulOpposite.unop_mul, MulOpposite.unop_star, MulOpposite.unop_op, star_one, one_mul]

open scoped Classical in
theorem regularTrace_regular (g : Γ) :
    regularTrace (reducedCrossedRegular (B := ℂ) g) = if g = 1 then 1 else 0 := by
  rw [regularTrace_apply, regularDeltaOne, reducedCrossedEvaluation_regular,
    reducedCrossedEvaluation_inclusion, mul_one]
  by_cases hg : g = 1
  · subst hg
    simp
  · rw [if_neg (fun h => hg (inv_eq_one.mp h.symm)), if_neg hg, MulOpposite.unop_zero]

/-- The canonical trace `τ(a) = ⟪δ_e, a δ_e⟫` of the scalar reduced crossed product. -/
def scalarTrace : ScalarCrossed Γ →ₗ[ℂ] ℂ where
  toFun a := regularTrace (a : AdjointableMap ℂ (ReducedCrossedHilbertModule ℂ Γ)
    (ReducedCrossedHilbertModule ℂ Γ))
  map_add' a b := map_add regularTrace (a : AdjointableMap ℂ (ReducedCrossedHilbertModule ℂ Γ)
    (ReducedCrossedHilbertModule ℂ Γ)) b
  map_smul' c a := map_smul regularTrace c (a : AdjointableMap ℂ (ReducedCrossedHilbertModule ℂ Γ)
    (ReducedCrossedHilbertModule ℂ Γ))

theorem scalarTrace_apply (a : ScalarCrossed Γ) :
    scalarTrace a = regularTrace (a : AdjointableMap ℂ (ReducedCrossedHilbertModule ℂ Γ)
      (ReducedCrossedHilbertModule ℂ Γ)) := rfl

theorem scalarTrace_eq_inner (a : ScalarCrossed Γ) :
    scalarTrace a = MulOpposite.unop ⟪regularDeltaOne Γ, (a : AdjointableMap ℂ
      (ReducedCrossedHilbertModule ℂ Γ) (ReducedCrossedHilbertModule ℂ Γ)) (regularDeltaOne Γ)⟫_(ℂᵐᵒᵖ) :=
  regularTrace_eq_inner _

open scoped Classical in
@[simp] theorem scalarTrace_scalarRegular (g : Γ) :
    scalarTrace (scalarRegular Γ g) = if g = 1 then 1 else 0 :=
  regularTrace_regular g

section Finite

variable [Fintype Γ]

variable (Γ) in
/-- The linear span of the regular translations, as a star subalgebra of the operators on `ℓ²Γ`. -/
def regularSpan : NonUnitalStarSubalgebra ℂ
    (AdjointableMap ℂ (ReducedCrossedHilbertModule ℂ Γ) (ReducedCrossedHilbertModule ℂ Γ)) where
  __ := Submodule.span ℂ (Set.range (reducedCrossedRegular (B := ℂ) (Γ := Γ)))
  mul_mem' {S T} hS hT := by
    have h := Submodule.mul_mem_mul hS hT
    rw [Submodule.span_mul_span] at h
    refine Submodule.span_mono ?_ h
    rintro _ ⟨_, ⟨g, rfl⟩, _, ⟨h, rfl⟩, rfl⟩
    exact ⟨g * h, reducedCrossedRegular_mul g h⟩
  star_mem' {T} hT := by
    change star T ∈ Submodule.span ℂ (Set.range (reducedCrossedRegular (B := ℂ) (Γ := Γ)))
    induction hT using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact Submodule.subset_span ⟨g⁻¹, (reducedCrossedRegular_star g).symm⟩
    | zero => rw [star_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [star_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [star_smul]; exact Submodule.smul_mem _ _ hx

/-- Every operator of the scalar crossed product of a finite group is a linear combination of the
regular translations. -/
theorem scalarCrossed_mem_regularSpan (a : ScalarCrossed Γ) :
    (a : AdjointableMap ℂ (ReducedCrossedHilbertModule ℂ Γ) (ReducedCrossedHilbertModule ℂ Γ)) ∈
      Submodule.span ℂ (Set.range (reducedCrossedRegular (B := ℂ) (Γ := Γ))) := by
  have hfin : FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range (reducedCrossedRegular (B := ℂ) (Γ := Γ)))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hclosed : IsClosed (regularSpan Γ : Set (AdjointableMap ℂ (ReducedCrossedHilbertModule ℂ Γ)
      (ReducedCrossedHilbertModule ℂ Γ))) :=
    Submodule.closed_of_finiteDimensional _
  have hle := reducedCrossedAlgebra_minimal CStarAlgebraAction.trivial (regularSpan Γ) hclosed
    (fun z g => by
      rw [reducedCrossedGenerator_trivial]
      exact Submodule.smul_mem _ z (Submodule.subset_span ⟨g, rfl⟩))
  exact hle a.property

/-- Fourier inversion for operators in the span of the regular translations. -/
theorem regularTrace_fourier_of_mem_span
    {T : AdjointableMap ℂ (ReducedCrossedHilbertModule ℂ Γ) (ReducedCrossedHilbertModule ℂ Γ)}
    (hT : T ∈ Submodule.span ℂ (Set.range (reducedCrossedRegular (B := ℂ) (Γ := Γ)))) :
    ∑ g, regularTrace (T * reducedCrossedRegular g⁻¹) • reducedCrossedRegular g = T := by
  classical
  induction hT using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    simp_rw [← reducedCrossedRegular_mul, regularTrace_regular, mul_inv_eq_one, ite_smul,
      one_smul, zero_smul]
    rw [Finset.sum_ite_eq Finset.univ h, if_pos (Finset.mem_univ h)]
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [add_mul, map_add, add_smul, Finset.sum_add_distrib, hx, hy]
  | smul c x _ hx =>
    simp only [smul_mul_assoc, map_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum, hx]

/-- **Fourier inversion** in the scalar reduced crossed product of a finite group:
`a = ∑_g τ(a λ_g⋆) λ_g`. -/
theorem scalarCrossed_fourier (a : ScalarCrossed Γ) :
    ∑ g, scalarTrace (a * star (scalarRegular Γ g)) • scalarRegular Γ g = a := by
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum]
  refine Eq.trans (Finset.sum_congr rfl fun g _ => ?_)
    (regularTrace_fourier_of_mem_span (scalarCrossed_mem_regularSpan a))
  rw [star_scalarRegular]
  rfl

/-- The trace of a product with `λ_h⋆` picks out the coefficient at `h`. -/
theorem scalarTrace_sum_mul_star (c : Γ → ℂ) (h : Γ) :
    scalarTrace ((∑ g, c g • scalarRegular Γ g) * star (scalarRegular Γ h)) = c h := by
  classical
  simp_rw [Finset.sum_mul, smul_mul_assoc, star_scalarRegular, scalarRegular_mul, map_sum, map_smul,
    scalarTrace_scalarRegular, mul_inv_eq_one, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ h, if_pos (Finset.mem_univ h)]

/-- The trace of a linear combination of regular translations is its coefficient at `e`. -/
theorem scalarTrace_sum (c : Γ → ℂ) : scalarTrace (∑ g, c g • scalarRegular Γ g) = c 1 := by
  simpa only [star_scalarRegular, inv_one, mul_scalarRegular_one] using scalarTrace_sum_mul_star c 1

theorem linearIndependent_scalarRegular : LinearIndependent ℂ (scalarRegular Γ) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc h
  simpa only [hc, zero_mul, map_zero] using (scalarTrace_sum_mul_star c h).symm

theorem span_scalarRegular : Submodule.span ℂ (Set.range (scalarRegular Γ)) = ⊤ := by
  refine eq_top_iff.mpr fun a _ => ?_
  rw [← scalarCrossed_fourier a]
  exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

variable (Γ) in
/-- The regular translations form a basis of the scalar crossed product of a finite group. -/
def scalarRegularBasis : Module.Basis Γ ℂ (ScalarCrossed Γ) :=
  Module.Basis.mk linearIndependent_scalarRegular span_scalarRegular.ge

@[simp] theorem scalarRegularBasis_apply (g : Γ) : scalarRegularBasis Γ g = scalarRegular Γ g :=
  Module.Basis.mk_apply _ _ _

/-- The coordinates of an element in the regular basis are its Fourier coefficients. -/
theorem scalarRegularBasis_repr (a : ScalarCrossed Γ) (g : Γ) :
    (scalarRegularBasis Γ).repr a g = scalarTrace (a * star (scalarRegular Γ g)) := by
  conv_lhs => rw [← scalarCrossed_fourier a]
  simp_rw [← scalarRegularBasis_apply]
  rw [Module.Basis.repr_sum_self]

instance scalarCrossed_finiteDimensional : FiniteDimensional ℂ (ScalarCrossed Γ) :=
  Module.Basis.finiteDimensional_of_finite (scalarRegularBasis Γ)

theorem finrank_scalarCrossed : Module.finrank ℂ (ScalarCrossed Γ) = Fintype.card Γ :=
  Module.finrank_eq_card_basis (scalarRegularBasis Γ)

/-- The trace of a product of two linear combinations. -/
theorem scalarTrace_sum_mul_sum (c d : Γ → ℂ) :
    scalarTrace ((∑ g, c g • scalarRegular Γ g) * ∑ h, d h • scalarRegular Γ h) =
      ∑ g, c g * d g⁻¹ := by
  classical
  simp_rw [Finset.sum_mul_sum, smul_mul_smul_comm, scalarRegular_mul, map_sum, map_smul,
    scalarTrace_scalarRegular, mul_eq_one_iff_inv_eq, smul_eq_mul, mul_ite, mul_one, mul_zero]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.sum_ite_eq Finset.univ g⁻¹, if_pos (Finset.mem_univ _)]

/-- `τ` is a trace. -/
theorem scalarTrace_mul_comm (a b : ScalarCrossed Γ) : scalarTrace (a * b) = scalarTrace (b * a) := by
  rw [← scalarCrossed_fourier a, ← scalarCrossed_fourier b, scalarTrace_sum_mul_sum,
    scalarTrace_sum_mul_sum]
  refine Fintype.sum_equiv (Equiv.inv Γ) _ _ fun g => ?_
  rw [Equiv.inv_apply, inv_inv, mul_comm]

/-- The adjoint of a linear combination of regular translations. -/
theorem star_sum_scalarRegular (c : Γ → ℂ) :
    star (∑ g, c g • scalarRegular Γ g) = ∑ g, star (c g⁻¹) • scalarRegular Γ g := by
  rw [star_sum]
  refine Fintype.sum_equiv (Equiv.inv Γ) _ _ fun g => ?_
  rw [star_smul, star_scalarRegular, Equiv.inv_apply, inv_inv]

theorem scalarTrace_star (a : ScalarCrossed Γ) : scalarTrace (star a) = star (scalarTrace a) := by
  rw [← scalarCrossed_fourier a, star_sum_scalarRegular, scalarTrace_sum, scalarTrace_sum, inv_one]

/-- **Plancherel**: `τ(a⋆ b) = ∑_g conj(τ(a λ_g⋆)) τ(b λ_g⋆)`. -/
theorem scalarTrace_star_mul (a b : ScalarCrossed Γ) :
    scalarTrace (star a * b) = ∑ g, star (scalarTrace (a * star (scalarRegular Γ g))) *
      scalarTrace (b * star (scalarRegular Γ g)) := by
  conv_lhs => rw [← scalarCrossed_fourier a, ← scalarCrossed_fourier b]
  rw [star_sum_scalarRegular, scalarTrace_sum_mul_sum]
  exact Fintype.sum_equiv (Equiv.inv Γ) _ _ fun g => rfl

theorem scalarTrace_star_mul_self_nonneg (a : ScalarCrossed Γ) : 0 ≤ scalarTrace (star a * a) := by
  rw [scalarTrace_star_mul]
  exact Finset.sum_nonneg fun g _ => star_mul_self_nonneg _

/-- `τ` is faithful. -/
theorem scalarTrace_star_mul_self_eq_zero_iff (a : ScalarCrossed Γ) :
    scalarTrace (star a * a) = 0 ↔ a = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, mul_zero, map_zero]⟩
  rw [scalarTrace_star_mul, Finset.sum_eq_zero_iff_of_nonneg fun g _ => star_mul_self_nonneg _] at h
  rw [← scalarCrossed_fourier a]
  refine Finset.sum_eq_zero fun g hg => ?_
  rw [(CStarRing.star_mul_self_eq_zero_iff (scalarTrace (a * star (scalarRegular Γ g)))).mp (h g hg),
    zero_smul]

/-- The double sum behind Julg's inverse: `∑_{g,h} τ(λ_g b λ_h⋆) λ_g⋆ λ_h = |Γ| b`. -/
theorem sum_scalarTrace_regular_mul_mul_star (b : ScalarCrossed Γ) :
    ∑ g, ∑ h, scalarTrace (scalarRegular Γ g * b * star (scalarRegular Γ h)) •
      (star (scalarRegular Γ g) * scalarRegular Γ h) = (Fintype.card Γ : ℂ) • b := by
  have hinner : ∀ g : Γ, ∑ h, scalarTrace (scalarRegular Γ g * b * star (scalarRegular Γ h)) •
      (star (scalarRegular Γ g) * scalarRegular Γ h) = b := by
    intro g
    conv_rhs => rw [← scalarCrossed_fourier b]
    refine (Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun k => ?_).symm
    change _ = scalarTrace (scalarRegular Γ g * b * star (scalarRegular Γ (g * k))) •
      (star (scalarRegular Γ g) * scalarRegular Γ (g * k))
    have hunit : star (scalarRegular Γ g) * scalarRegular Γ (g * k) = scalarRegular Γ k := by
      rw [star_scalarRegular, scalarRegular_mul, inv_mul_cancel_left]
    have htrace : scalarTrace (scalarRegular Γ g * b * star (scalarRegular Γ (g * k))) =
        scalarTrace (b * star (scalarRegular Γ k)) := by
      rw [mul_assoc, scalarTrace_mul_comm, mul_assoc, star_scalarRegular, star_scalarRegular,
        scalarRegular_mul, mul_inv_rev, inv_mul_cancel_right]
    rw [hunit, htrace]
  rw [Finset.sum_congr rfl fun g _ => hinner g, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ]

end Finite

end BC4lean.KKTheory

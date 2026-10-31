import BC4lean.FiniteGroupPointCalibration
import BC4lean.UnitPointCutoff
import BC4lean.GroupUniverseParityFunctoriality
import BC4lean.GroupUniverseParityUnits
import BC4lean.GroupUniverseCompactCorrespondenceProduct
import BC4lean.GroupUniverseEvenBridge
import BC4lean.KasparovGroupChange

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The Green–Julg correspondence `ℓ²Γ` and Julg's inverse at the point

Let `Γ` be a finite group and `Cr = ℂ ⋊_r Γ` the scalar reduced crossed product, which upstream
defines as a closed algebra of operators on `ℓ²Γ = ReducedCrossedHilbertModule ℂ Γ`. Let `Γ` act
on `ℓ²Γ` by right translation, `(ρ_g x)(i) = x(i g)`. This file proves:

* `rightRegular_commute`: every element of `Cr` commutes with every `ρ_g`. Each `ρ_g` is a
  permutation of coordinates by right multiplication, the generators `b λ_h` of `Cr` are scalars
  times permutations by left multiplication, and the commutant of a self-adjoint set is a closed
  star subalgebra;
* `one_eq_sum_rankOne`: for finite `Γ` the identity of `ℓ²Γ` is `∑_g θ(δ_g, δ_g)`, so every
  adjointable operator on `ℓ²Γ` is compact;
* `isCountablyGenerated`: `ℓ²Γ` is countably generated for every countable `Γ` (the `δ_g`
  generate a dense subspace).

Hence `(ℓ²Γ, ρ, Cr ↪ B(ℓ²Γ), 0)` is a `Γ`-equivariant compact correspondence from `Cr` (trivial
action) to `ℂ` (trivial action), and `regularCorrespondenceClass` is its class in `KK^Γ(Cr, ℂ)`.
Julg's inverse `greenJulgInverse p : KK_p(ℂ, Cr) → KK^Γ_p(C₀(pt), ℂ)` is
`y ↦ ev^* (infl y · [ℓ²Γ])`: inflation along `Γ →* Unit` (`KasparovGroupChange`), the product with
`[ℓ²Γ]` (`rightEvenProduct`), and the pullback along evaluation `C₀(pt) → ℂ`. Each factor is an
additive map of `KK` groups, so `greenJulgInverse p` is one as well.

That it inverts the point Green–Julg map is proved in `GreenJulgPoint` and `GreenJulgPointLeft`. -/

noncomputable section
namespace BC4lean.KKTheory.GreenJulgCorrespondence
open BC4lean.Chapter8Examples
open KKTheory.GroupUniverseParityGroup
open scoped ZeroAtInfty ComplexOrder KasparovDescent InnerProductSpace

variable (Γ : Type) [Group Γ]

/-- The scalar reduced crossed product `ℂ ⋊_r Γ`. -/
abbrev Cr := ReducedCrossedProduct (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)

/-- `ℓ²Γ`, the Hilbert space on which `ℂ ⋊_r Γ` is defined. -/
abbrev L2 := ReducedCrossedHilbertModule ℂ Γ

/-! ## The right regular representation -/

section Regular

/-- The left regular representation: `ℂ ⋊_r Γ` is by definition a closed algebra of operators on
`ℓ²Γ`. -/
def regularRep : Cr Γ →⋆ₙₐ[ℂ] AdjointableMap ℂ (L2 Γ) (L2 Γ) :=
  NonUnitalStarSubalgebraClass.subtype
    (reducedCrossedAlgebra (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ))

@[simp] theorem regularRep_apply (b : Cr Γ) : regularRep Γ b = (b : AdjointableMap ℂ (L2 Γ) (L2 Γ)) :=
  rfl

omit [Group Γ] in
/-- Coordinate permutations compose. -/
theorem reindex_reindex (e e' : Γ ≃ Γ) (x : L2 Γ) :
    reducedCrossedReindex (B := ℂ) e (reducedCrossedReindex e' x) =
      reducedCrossedReindex (e'.trans e) x := by
  have h : (reducedCrossedReindex (B := ℂ) e).comp (reducedCrossedReindex e') =
      reducedCrossedReindex (e'.trans e) := by
    apply reducedCrossed_adjointable_ext_mk
    intro v
    change reducedCrossedReindex e (reducedCrossedReindex e' (reducedCrossedMk v)) = _
    rw [reducedCrossedReindex_mk, reducedCrossedReindex_mk, reducedCrossedReindex_mk]
    congr 1
    ext i
    rw [reducedCrossedEmbeddingLinear_equiv_apply, reducedCrossedEmbeddingLinear_equiv_apply,
      reducedCrossedEmbeddingLinear_equiv_apply]
    rfl
  exact congrArg (fun T : AdjointableMap ℂ (L2 Γ) (L2 Γ) => T x) h

omit [Group Γ] in
/-- The identity permutation acts as the identity. -/
theorem reindex_refl (x : L2 Γ) : reducedCrossedReindex (B := ℂ) (Equiv.refl Γ) x = x := by
  have h : reducedCrossedReindex (B := ℂ) (Equiv.refl Γ) = AdjointableMap.id := by
    apply reducedCrossed_adjointable_ext_mk
    intro v
    rw [reducedCrossedReindex_mk]
    change reducedCrossedMk _ = reducedCrossedMk v
    congr 1
    ext i
    rw [reducedCrossedEmbeddingLinear_equiv_apply]
    rfl
  exact congrArg (fun T : AdjointableMap ℂ (L2 Γ) (L2 Γ) => T x) h

/-- Right translation by `g`: `(ρ_g x)(i) = x(i g)`. -/
def rightTranslate (g : Γ) : L2 Γ ≃ₗᵢ[ℂ] L2 Γ where
  toFun := reducedCrossedReindex (Equiv.mulRight g⁻¹)
  invFun := reducedCrossedReindex (Equiv.mulRight g⁻¹).symm
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv x := by
    have h := reducedCrossedReindex_adjoint_comp_self (B := ℂ) (Equiv.mulRight g⁻¹)
    rw [reducedCrossedReindex_adjoint] at h
    exact congrArg (fun T : AdjointableMap ℂ (L2 Γ) (L2 Γ) => T x) h
  right_inv x := by
    have h := reducedCrossedReindex_comp_adjoint (B := ℂ) (Equiv.mulRight g⁻¹)
    rw [reducedCrossedReindex_adjoint] at h
    exact congrArg (fun T : AdjointableMap ℂ (L2 Γ) (L2 Γ) => T x) h
  norm_map' := reducedCrossedReindex_norm _

theorem rightTranslate_apply (g : Γ) (x : L2 Γ) :
    rightTranslate Γ g x = reducedCrossedReindex (Equiv.mulRight g⁻¹) x := rfl

/-- Right translation is a representation of `Γ`. -/
theorem rightTranslate_mul (g h : Γ) (x : L2 Γ) :
    rightTranslate Γ (g * h) x = rightTranslate Γ g (rightTranslate Γ h x) := by
  change _ = reducedCrossedReindex (Equiv.mulRight g⁻¹) (reducedCrossedReindex (Equiv.mulRight h⁻¹) x)
  rw [reindex_reindex]
  rw [show (Equiv.mulRight h⁻¹).trans (Equiv.mulRight g⁻¹) = Equiv.mulRight (g * h)⁻¹ from
    Equiv.ext fun i => by simp [mul_assoc]]
  rfl

/-- `ρ_1 = 1`. -/
theorem rightTranslate_one (x : L2 Γ) : rightTranslate Γ 1 x = x := by
  change reducedCrossedReindex (Equiv.mulRight (1 : Γ)⁻¹) x = x
  have : Equiv.mulRight (1 : Γ)⁻¹ = Equiv.refl Γ := Equiv.ext fun i => by simp
  rw [this, reindex_refl]

/-- `ℓ²Γ` with the right regular action, a `Γ`-Hilbert space for the trivial action on `ℂ`. -/
def rightRegular : EquivariantHilbertModule (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
    (L2 Γ) where
  action :=
    { toFun := rightTranslate Γ
      map_one' := LinearIsometryEquiv.ext (rightTranslate_one Γ)
      map_mul' := fun g h => LinearIsometryEquiv.ext (rightTranslate_mul Γ g h) }
  inner_action _ x y := reducedCrossedReindex_inner _ x y

/-- A generator `b λ_h` of `ℂ ⋊_r Γ` commutes with right multiplication of coordinates. -/
theorem reindex_mulRight_mul_generator (k : Γ) (b : ℂ) (h : Γ) :
    reducedCrossedReindex (Equiv.mulRight k) *
        reducedCrossedGenerator (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) b h =
      reducedCrossedGenerator (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) b h *
        reducedCrossedReindex (Equiv.mulRight k) := by
  apply reducedCrossedRegular_ext
  intro x
  simp only [reducedCrossedGenerator, AdjointableMap.mul_apply, reducedCrossedRegular,
    reducedCrossedReindex_mk, reducedCrossedCoefficient_mk]
  congr 1
  ext i
  simp only [reducedCrossedEmbeddingLinear_equiv_apply, reducedCrossedFiniteDiagonal_apply,
    Equiv.mulRight_symm, Equiv.mulLeft_symm, Equiv.coe_mulRight, Equiv.coe_mulLeft, mul_assoc]
  rfl

/-- The coordinate permutations by right multiplication, as adjointable operators. -/
def rightPermutations : Set (AdjointableMap ℂ (L2 Γ) (L2 Γ)) :=
  Set.range fun k : Γ => reducedCrossedReindex (Equiv.mulRight k)

/-- `ℂ ⋊_r Γ` lies in the commutant of the right permutations. -/
theorem reducedCrossedAlgebra_le_centralizer :
    reducedCrossedAlgebra (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) ≤
      NonUnitalStarSubalgebra.centralizer ℂ (rightPermutations Γ) := by
  apply reducedCrossedAlgebra_minimal
  · rw [NonUnitalStarSubalgebra.coe_centralizer]
    exact Set.isClosed_centralizer _
  · intro b h
    rw [NonUnitalStarSubalgebra.mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    refine ⟨reindex_mulRight_mul_generator Γ k b h, ?_⟩
    have hstar : star (reducedCrossedReindex (B := ℂ) (Equiv.mulRight k)) =
        reducedCrossedReindex (Equiv.mulRight k⁻¹) := by
      rw [show star (reducedCrossedReindex (B := ℂ) (Equiv.mulRight k)) =
        (reducedCrossedReindex (B := ℂ) (Equiv.mulRight k)).adjoint from rfl,
        reducedCrossedReindex_adjoint, Equiv.mulRight_symm]
    rw [hstar]
    exact reindex_mulRight_mul_generator Γ k⁻¹ b h

/-- Every element of `ℂ ⋊_r Γ` commutes with every right translation. -/
theorem rightRegular_commute (g : Γ) (b : Cr Γ) (y : L2 Γ) :
    rightTranslate Γ g (regularRep Γ b y) = regularRep Γ b (rightTranslate Γ g y) := by
  have hb := (NonUnitalStarSubalgebra.mem_centralizer_iff ℂ).mp
    (reducedCrossedAlgebra_le_centralizer Γ b.2) _ ⟨g⁻¹, rfl⟩
  exact congrArg (fun T : AdjointableMap ℂ (L2 Γ) (L2 Γ) => T y) hb.1

/-- The left regular representation of `ℂ ⋊_r Γ` (trivial action) is equivariant
for the right regular action of `Γ`. -/
theorem regularRep_equivariant :
    ModuleTensorRepresentationEquivariant (regularRep Γ)
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ (Cr Γ)) (rightRegular Γ) :=
  fun g b y => rightRegular_commute Γ g b y

end Regular

/-! ## Compactness and countable generation -/

section Finite

/-- The basis vector `δ_g ∈ ℓ²Γ`. -/
def delta (g : Γ) : L2 Γ := reducedCrossedMk (Finsupp.single g 1)

omit [Group Γ] in
/-- `⟪δ_g, x⟫ = x(g)` on finite vectors. -/
theorem inner_delta_mk (g : Γ) (x : ReducedCrossedVectors ℂ Γ) :
    ⟪delta Γ g, reducedCrossedMk x⟫_(ℂᵐᵒᵖ) = x g := by
  rw [delta, reducedCrossedMk_inner, reducedCrossedFiniteInner_single_left]
  change x g * star (1 : ℂᵐᵒᵖ) = x g
  rw [star_one, mul_one]

omit [Group Γ] in
/-- A coordinate vector is a coefficient multiple of a basis vector. -/
theorem mk_single (g : Γ) (a : ℂᵐᵒᵖ) :
    reducedCrossedMk (Finsupp.single g a) = a • delta Γ g := by
  rw [delta, ← reducedCrossedMk_op_smul, Finsupp.smul_single]
  simp

/-- Right translation on basis vectors: `ρ_g δ_h = δ_{h g⁻¹}`. -/
theorem rightTranslate_delta (g h : Γ) : rightTranslate Γ g (delta Γ h) = delta Γ (h * g⁻¹) := by
  rw [rightTranslate_apply, delta, delta, reducedCrossedReindex_mk]
  congr 1
  ext i
  classical
  rw [reducedCrossedEmbeddingLinear_equiv_apply]
  simp only [Equiv.mulRight_symm, Equiv.coe_mulRight, inv_inv, Finsupp.single_apply,
    mul_inv_eq_iff_eq_mul]

omit [Group Γ] in
/-- For finite `Γ`, the identity of `ℓ²Γ` is `∑_g θ(δ_g, δ_g)`. -/
theorem one_eq_sum_rankOne [Fintype Γ] :
    (AdjointableMap.id : AdjointableMap ℂ (L2 Γ) (L2 Γ)) =
      ∑ g : Γ, moduleRankOne (delta Γ g) (delta Γ g) := by
  apply reducedCrossed_adjointable_ext_mk
  intro x
  have hg (g : Γ) : moduleRankOne (B := ℂ) (delta Γ g) (delta Γ g) (reducedCrossedMk x) =
      reducedCrossedMk (Finsupp.single g (x g)) := by
    rw [moduleRankOne_apply, inner_delta_mk, mk_single]
  rw [finiteAdjointable_sum_apply]
  simp only [hg]
  rw [← map_sum, Finsupp.univ_sum_single]
  rfl

omit [Group Γ] in
/-- For finite `Γ` every adjointable operator on `ℓ²Γ` is compact; in particular so
is every element of `ℂ ⋊_r Γ`. -/
theorem isModuleCompact [Finite Γ] (T : AdjointableMap ℂ (L2 Γ) (L2 Γ)) : IsModuleCompact T := by
  have := Fintype.ofFinite Γ
  have hid : IsModuleCompact (AdjointableMap.id : AdjointableMap ℂ (L2 Γ) (L2 Γ)) := by
    rw [one_eq_sum_rankOne]
    exact (moduleCompact ℂ (L2 Γ) (L2 Γ)).sum_mem fun g _ =>
      moduleFiniteRank_le_moduleCompact (Submodule.subset_span ⟨(delta Γ g, delta Γ g), rfl⟩)
  exact hid.comp_left T

theorem regularRep_isModuleCompact [Finite Γ] (b : Cr Γ) : IsModuleCompact (regularRep Γ b) :=
  isModuleCompact Γ _

/-- `ℓ²Γ` is countably generated for every countable `Γ`: the basis vectors span the
finite vectors, which are dense. -/
theorem isCountablyGenerated [Countable Γ] : IsCountablyGeneratedModule ℂ (L2 Γ) := by
  obtain ⟨e, he⟩ := exists_surjective_nat Γ
  refine ⟨fun n => delta Γ (e n), ?_⟩
  refine reducedCrossedMk_denseRange.mono ?_
  rintro _ ⟨x, rfl⟩
  induction x using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | single g a =>
    obtain ⟨n, rfl⟩ := he g
    rw [mk_single]
    exact smul_mem_moduleGeneratingSpan _ n a

end Finite

/-! ## The class `[ℓ²Γ]` and Julg's inverse -/

section Inverse

variable [Countable Γ] [Finite Γ]

/-- The class `[ℓ²Γ, ρ, λ, 0] ∈ KK^Γ(ℂ ⋊_r Γ, ℂ)`, both actions on algebras trivial. -/
def regularCorrespondenceClass :
    KasparovHomotopyClass.{0, 0, 0, 0}
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ (Cr Γ))
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) :=
  GroupUniverseEvenBridge.evenClass
    (GroupUniverseCompactCorrespondenceProduct.correspondenceClass
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ (Cr Γ))
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
      CStarGrading.trivial CStarGrading.trivial GradedHilbertModule.trivial (rightRegular Γ)
      (CStarAlgebraAction.preservesGrading_trivial _) (CStarAlgebraAction.preservesGrading_trivial _)
      (fun _ _ => rfl) (regularRep Γ) (fun _ _ => rfl) (regularRep_equivariant Γ)
      (regularRep_isModuleCompact Γ) (isCountablyGenerated Γ))

/-- Inflation `KK_p(ℂ, ℂ ⋊_r Γ) → KK^Γ_p(ℂ, ℂ ⋊_r Γ)` along `Γ →* Unit` (trivial actions). -/
def inflate (p : Bool) :
    KKParityGroup.{0, 0, 0, 0} p (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ) (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (Cr Γ)) →+
      KKParityGroup.{0, 0, 0, 0} p (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
        (CStarAlgebraAction.trivial : CStarAlgebraAction Γ (Cr Γ)) := by
  cases p
  · exact KasparovHomotopyClass.comap (1 : Γ →* Unit) (fun _ _ => rfl) (fun _ _ => rfl)
  · exact OddKK.comap (1 : Γ →* Unit) (fun _ _ => rfl) (fun _ _ => rfl)

/-- `C₀(pt)` is separable: it is the image of `ℂ` (as
`OrderTwoPointKKScalar.cZero_separableSpace_of_subsingleton` in the C2 chain). -/
instance pointCZero_separableSpace : TopologicalSpace.SeparableSpace C₀(FiniteGroupPoint.{0}, ℂ) :=
  let e := UnitPointCutoff.pointCZeroEquiv FiniteGroupPoint.{0} default
  e.surjective.denseRange.separableSpace
    (LinearMap.continuous_of_finiteDimensional (LinearMap.mk ⟨e, map_add e⟩ (map_smul e) :
      ℂ →ₗ[ℂ] C₀(FiniteGroupPoint.{0}, ℂ)))

/-- Evaluation `C₀(pt) → ℂ`. -/
abbrev pointEval : C₀(FiniteGroupPoint.{0}, ℂ) →⋆ₙₐ[ℂ] ℂ :=
  ((UnitPointCutoff.pointCZeroEquiv FiniteGroupPoint.{0} default).symm :
    C₀(FiniteGroupPoint.{0}, ℂ) →⋆ₙₐ[ℂ] ℂ)

omit [Countable Γ] [Finite Γ] in
/-- Evaluation at the point is invariant under the point action. -/
theorem pointEval_equivariant : ∀ (g : Γ) (a : C₀(FiniteGroupPoint.{0}, ℂ)),
    pointEval ((CZero.action Γ (X := FiniteGroupPoint.{0})).automorphism g a) =
      (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ).automorphism g (pointEval a) := by
  intro g a
  change a (g⁻¹ • default) = a default
  exact congrArg a (Subsingleton.elim _ _)

/-- The product with `[ℓ²Γ]`, `KK^Γ_p(ℂ, ℂ ⋊_r Γ) → KK^Γ_p(ℂ, ℂ)`, as an additive map. -/
def regularProduct (p : Bool) :
    KKParityGroup.{0, 0, 0, 0} p (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
        (CStarAlgebraAction.trivial : CStarAlgebraAction Γ (Cr Γ)) →+
      KKParityGroup.{0, 0, 0, 0} p (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
        (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) :=
  AddMonoidHom.mk' (fun x => GroupUniverseParityUnits.rightEvenProduct p x (regularCorrespondenceClass Γ))
    (by
      cases p
      · exact fun x x' => GroupUniverseParityProduct.evenProduct_add_first x x' _
      · exact fun x x' => GroupUniverseOddFirstParityProduct.oddEvenProduct_add_first x x' _)

/-- The pullback along `ev : C₀(pt) → ℂ`, as an additive map. -/
def pointPullback (p : Bool) :
    KKParityGroup.{0, 0, 0, 0} p (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ)
        (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) →+
      KKParityGroup.{0, 0, 0, 0} p (CZero.action Γ (X := FiniteGroupPoint.{0}))
        (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) :=
  AddMonoidHom.mk'
    (GroupUniverseParityFunctoriality.sourcePullback.{0} p pointEval (pointEval_equivariant Γ))
    (GroupUniverseParityFunctoriality.sourcePullback_add p pointEval (pointEval_equivariant Γ))

/-- **Julg's inverse** `L_p : KK_p(ℂ, ℂ ⋊_r Γ) → KK^Γ_p(C₀(pt), ℂ)`,
`L_p y = ev^* (infl y · [ℓ²Γ])`. -/
def greenJulgInverse (p : Bool) :
    KKParityGroup.{0, 0, 0, 0} p (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ) (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (Cr Γ)) →+
      KKParityGroup.{0, 0, 0, 0} p (CZero.action Γ (X := FiniteGroupPoint.{0}))
        (CStarAlgebraAction.trivial : CStarAlgebraAction Γ ℂ) :=
  (pointPullback Γ p).comp ((regularProduct Γ p).comp (inflate Γ p))

/-- The defining formula of `L_p`. -/
theorem greenJulgInverse_apply (p : Bool)
    (y : KKParityGroup.{0, 0, 0, 0} p (CStarAlgebraAction.trivial : CStarAlgebraAction Unit ℂ) (CStarAlgebraAction.trivial : CStarAlgebraAction Unit (Cr Γ))) :
    greenJulgInverse Γ p y =
      GroupUniverseParityFunctoriality.sourcePullback.{0} p pointEval (pointEval_equivariant Γ)
        (GroupUniverseParityUnits.rightEvenProduct p (inflate Γ p y) (regularCorrespondenceClass Γ)) :=
  rfl

end Inverse

end BC4lean.KKTheory.GreenJulgCorrespondence

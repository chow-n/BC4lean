import BC4lean.OperatorK0Product
import BC4lean.OperatorK1Product
import BC4lean.OperatorKUnitalAgreement
import BC4lean.FinitePointCompressedDescent
import BC4lean.OrderTwoPointKKScalar
import BC4lean.FiniteReducedGroupCStar
import BC4lean.ReducedScalarKKComparison
import BC4lean.AssemblyPieceHom
import BC4lean.BaumConnesProperty
import BC4lean.OddKTheoryIndependentCoefficientNaturality
import BC4lean.ScalarKasparovK0ComparisonNaturality
import BC4lean.UnitAssemblyEquivalence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The assembly map for a group of order two

For `Nat.card Γ = 2` the reduced assembly map is identified, in both parities, with an explicit
additive equivalence, so `Γ` has the coefficient-free reduced Baum–Connes property
(`baumConnesProperty_of_card_two`). The proof follows `UnitAssemblyEquivalence`:

* the canonical colimit is the point model (`reducedAssemblyHom_finitePoint`);
* `KK^Γ_p(C₀(pt), ℂ) ≅ KK_p(ℂ, ℂ)²` by the `±1` eigen parts of the generator
  (`orderTwoPointKKSplit`), with inverse `(a, b) ↦ infl a + χ ⊗ infl b`, `χ` the sign character;
* on a class of the form `χ ⊗ infl a`, cutoff product and descent give the coefficient extension
  of `a` along `z ↦ z • P_χ` (`even_compressedDescent`, `odd_compressedDescent`), and the scalar
  index theorem then gives `(P_χ)_* [a]` in `K_p(C*_r Γ)`;
* under `ℂ × ℂ ≅ C*_r Γ` the projections `P_1` and `P_sign` are the two coordinate idempotents
  (`crossedHom_comp_characterHom_one`, `crossedHom_comp_characterHom_sign`), so the composite is
  `KK_p(ℂ, ℂ)² ≅ K_p(ℂ)² ≅ K_p(ℂ × ℂ) ≅ K_p(C*_r Γ)` (`orderTwoAnalyticEquiv`).
-/

noncomputable section
namespace BC4lean.OperatorKTheory

local instance (priority := high) spectralOrder' (B : Type*) [CStarAlgebra B] : PartialOrder B :=
  CStarAlgebra.spectralOrder B
local instance (priority := high) spectralOrderedRing' (B : Type*) [CStarAlgebra B] :
    StarOrderedRing B :=
  CStarAlgebra.spectralOrderedRing B

section Zero
variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

theorem unitization_starMap_zero :
    Unitization.starMap (0 : A →⋆ₙₐ[ℂ] B) = (scalarSection B).comp (scalarQuotient A) := by
  apply StarAlgHom.ext
  intro x
  apply Unitization.ext <;> simp [scalarSection, scalarQuotient] <;> rfl

@[simp] theorem operatorK0Map_zero : operatorK0Map (0 : A →⋆ₙₐ[ℂ] B) = 0 := by
  ext x
  apply Subtype.ext
  change k0Map (Unitization.starMap (0 : A →⋆ₙₐ[ℂ] B)) x.val = 0
  rw [unitization_starMap_zero, k0Map_comp, AddMonoidHom.comp_apply, x.property, map_zero]

@[simp] theorem operatorK1Map_zero : operatorK1Map (0 : A →⋆ₙₐ[ℂ] B) = 0 := by
  ext x
  apply Subtype.ext
  change k1Map (Unitization.starMap (0 : A →⋆ₙₐ[ℂ] B)) x.val = 0
  rw [unitization_starMap_zero, k1Map_comp, AddMonoidHom.comp_apply, x.property, map_zero]

end Zero

section Product
variable (A B : Type*) [CStarAlgebra A] [CStarAlgebra B]

/-- `K₀` of a product, on operator K-groups: `x ↦ (fst_* x, snd_* x)`, inverse `(u, v) ↦ inl_* u + inr_* v`. -/
def operatorK0ProductEquiv : OperatorK0 (A × B) ≃+ OperatorK0 A × OperatorK0 B :=
  (operatorK0UnitalEquiv (A × B)).trans ((k0ProductEquiv A B).trans
    ((operatorK0UnitalEquiv A).symm.prodCongr (operatorK0UnitalEquiv B).symm))

theorem operatorK0ProductEquiv_apply (x : OperatorK0 (A × B)) :
    operatorK0ProductEquiv A B x =
      (operatorK0Map (StarAlgHom.fst ℂ A B).toNonUnitalStarAlgHom x,
        operatorK0Map (StarAlgHom.snd ℂ A B).toNonUnitalStarAlgHom x) := by
  refine Prod.ext ?_ ?_
  · change (operatorK0UnitalEquiv A).symm (k0Map (StarAlgHom.fst ℂ A B) (operatorK0UnitalEquiv (A × B) x)) = _
    rw [AddEquiv.symm_apply_eq]
    exact (operatorK0UnitalEquiv_natural (StarAlgHom.fst ℂ A B) x).symm
  · change (operatorK0UnitalEquiv B).symm (k0Map (StarAlgHom.snd ℂ A B) (operatorK0UnitalEquiv (A × B) x)) = _
    rw [AddEquiv.symm_apply_eq]
    exact (operatorK0UnitalEquiv_natural (StarAlgHom.snd ℂ A B) x).symm

theorem operatorK0ProductEquiv_symm_apply (u : OperatorK0 A) (v : OperatorK0 B) :
    (operatorK0ProductEquiv A B).symm (u, v) =
      operatorK0Map (NonUnitalStarAlgHom.inl ℂ A B) u +
        operatorK0Map (NonUnitalStarAlgHom.inr ℂ A B) v := by
  rw [AddEquiv.symm_apply_eq, operatorK0ProductEquiv_apply, map_add, map_add,
    ← AddMonoidHom.comp_apply (operatorK0Map _) (operatorK0Map (NonUnitalStarAlgHom.inl ℂ A B)),
    ← AddMonoidHom.comp_apply (operatorK0Map _) (operatorK0Map (NonUnitalStarAlgHom.inr ℂ A B)),
    ← AddMonoidHom.comp_apply (operatorK0Map _) (operatorK0Map (NonUnitalStarAlgHom.inl ℂ A B)),
    ← AddMonoidHom.comp_apply (operatorK0Map _) (operatorK0Map (NonUnitalStarAlgHom.inr ℂ A B)),
    ← operatorK0Map_comp, ← operatorK0Map_comp, ← operatorK0Map_comp, ← operatorK0Map_comp]
  have h1 : (StarAlgHom.fst ℂ A B).toNonUnitalStarAlgHom.comp (NonUnitalStarAlgHom.inl ℂ A B) =
      NonUnitalStarAlgHom.id ℂ A := by ext; rfl
  have h2 : (StarAlgHom.fst ℂ A B).toNonUnitalStarAlgHom.comp (NonUnitalStarAlgHom.inr ℂ A B) = 0 := by
    ext; rfl
  have h3 : (StarAlgHom.snd ℂ A B).toNonUnitalStarAlgHom.comp (NonUnitalStarAlgHom.inl ℂ A B) = 0 := by
    ext; rfl
  have h4 : (StarAlgHom.snd ℂ A B).toNonUnitalStarAlgHom.comp (NonUnitalStarAlgHom.inr ℂ A B) =
      NonUnitalStarAlgHom.id ℂ B := by ext; rfl
  rw [h1, h2, h3, h4]
  simp

/-- `K₁` of a product, on operator K-groups: `x ↦ (fst_* x, snd_* x)`, inverse `(u, v) ↦ inl_* u + inr_* v`. -/
def operatorK1ProductEquiv : OperatorK1 (A × B) ≃+ OperatorK1 A × OperatorK1 B :=
  (operatorK1UnitalEquiv (A × B)).trans ((k1ProductEquiv A B).trans
    ((operatorK1UnitalEquiv A).symm.prodCongr (operatorK1UnitalEquiv B).symm))

theorem operatorK1ProductEquiv_apply (x : OperatorK1 (A × B)) :
    operatorK1ProductEquiv A B x =
      (operatorK1Map (StarAlgHom.fst ℂ A B).toNonUnitalStarAlgHom x,
        operatorK1Map (StarAlgHom.snd ℂ A B).toNonUnitalStarAlgHom x) := by
  refine Prod.ext ?_ ?_
  · change (operatorK1UnitalEquiv A).symm (k1Map (StarAlgHom.fst ℂ A B) (operatorK1UnitalEquiv (A × B) x)) = _
    rw [AddEquiv.symm_apply_eq]
    exact (operatorK1UnitalEquiv_natural (StarAlgHom.fst ℂ A B) x).symm
  · change (operatorK1UnitalEquiv B).symm (k1Map (StarAlgHom.snd ℂ A B) (operatorK1UnitalEquiv (A × B) x)) = _
    rw [AddEquiv.symm_apply_eq]
    exact (operatorK1UnitalEquiv_natural (StarAlgHom.snd ℂ A B) x).symm

theorem operatorK1ProductEquiv_symm_apply (u : OperatorK1 A) (v : OperatorK1 B) :
    (operatorK1ProductEquiv A B).symm (u, v) =
      operatorK1Map (NonUnitalStarAlgHom.inl ℂ A B) u +
        operatorK1Map (NonUnitalStarAlgHom.inr ℂ A B) v := by
  rw [AddEquiv.symm_apply_eq, operatorK1ProductEquiv_apply, map_add, map_add,
    ← AddMonoidHom.comp_apply (operatorK1Map _) (operatorK1Map (NonUnitalStarAlgHom.inl ℂ A B)),
    ← AddMonoidHom.comp_apply (operatorK1Map _) (operatorK1Map (NonUnitalStarAlgHom.inr ℂ A B)),
    ← AddMonoidHom.comp_apply (operatorK1Map _) (operatorK1Map (NonUnitalStarAlgHom.inl ℂ A B)),
    ← AddMonoidHom.comp_apply (operatorK1Map _) (operatorK1Map (NonUnitalStarAlgHom.inr ℂ A B)),
    ← operatorK1Map_comp, ← operatorK1Map_comp, ← operatorK1Map_comp, ← operatorK1Map_comp]
  have h1 : (StarAlgHom.fst ℂ A B).toNonUnitalStarAlgHom.comp (NonUnitalStarAlgHom.inl ℂ A B) =
      NonUnitalStarAlgHom.id ℂ A := by ext; rfl
  have h2 : (StarAlgHom.fst ℂ A B).toNonUnitalStarAlgHom.comp (NonUnitalStarAlgHom.inr ℂ A B) = 0 := by
    ext; rfl
  have h3 : (StarAlgHom.snd ℂ A B).toNonUnitalStarAlgHom.comp (NonUnitalStarAlgHom.inl ℂ A B) = 0 := by
    ext; rfl
  have h4 : (StarAlgHom.snd ℂ A B).toNonUnitalStarAlgHom.comp (NonUnitalStarAlgHom.inr ℂ A B) =
      NonUnitalStarAlgHom.id ℂ B := by ext; rfl
  rw [h1, h2, h3, h4]
  simp

end Product

section MapEquiv
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

/-- A `*`-isomorphism induces an isomorphism of operator `K₀`. -/
def operatorK0MapEquiv (e : A ≃⋆ₐ[ℂ] B) : OperatorK0 A ≃+ OperatorK0 B where
  toFun := operatorK0Map e.toNonUnitalStarAlgHom
  invFun := operatorK0Map e.symm.toNonUnitalStarAlgHom
  left_inv x := by
    rw [← AddMonoidHom.comp_apply, ← operatorK0Map_comp]
    have h : e.symm.toNonUnitalStarAlgHom.comp e.toNonUnitalStarAlgHom = NonUnitalStarAlgHom.id ℂ A := by
      ext a; exact e.symm_apply_apply a
    rw [h, operatorK0Map_id]; rfl
  right_inv x := by
    rw [← AddMonoidHom.comp_apply, ← operatorK0Map_comp]
    have h : e.toNonUnitalStarAlgHom.comp e.symm.toNonUnitalStarAlgHom = NonUnitalStarAlgHom.id ℂ B := by
      ext a; exact e.apply_symm_apply a
    rw [h, operatorK0Map_id]; rfl
  map_add' := map_add _

/-- A `*`-isomorphism induces an isomorphism of operator `K₁`. -/
def operatorK1MapEquiv (e : A ≃⋆ₐ[ℂ] B) : OperatorK1 A ≃+ OperatorK1 B where
  toFun := operatorK1Map e.toNonUnitalStarAlgHom
  invFun := operatorK1Map e.symm.toNonUnitalStarAlgHom
  left_inv x := by
    rw [← AddMonoidHom.comp_apply, ← operatorK1Map_comp]
    have h : e.symm.toNonUnitalStarAlgHom.comp e.toNonUnitalStarAlgHom = NonUnitalStarAlgHom.id ℂ A := by
      ext a; exact e.symm_apply_apply a
    rw [h, operatorK1Map_id]; rfl
  right_inv x := by
    rw [← AddMonoidHom.comp_apply, ← operatorK1Map_comp]
    have h : e.toNonUnitalStarAlgHom.comp e.symm.toNonUnitalStarAlgHom = NonUnitalStarAlgHom.id ℂ B := by
      ext a; exact e.apply_symm_apply a
    rw [h, operatorK1Map_id]; rfl
  map_add' := map_add _

end MapEquiv

end BC4lean.OperatorKTheory

namespace BC4lean.Chapter8Examples.OrderTwoAssembly
open ProperActions KKTheory OperatorKTheory OrderTwo
open KKTheory.GroupUniverseParityGroup KKTheory.GroupUniverseParityFunctoriality
open KKTheory.FinitePointCompressedDescent KKTheory.FinitePointCharacterTensor KKTheory.FinitePointCutoff
open scoped ZeroAtInfty ComplexOrder KasparovDescent

variable {Γ : Type} [Group Γ] [Countable Γ] [Fintype Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul ℂᵐᵒᵖ E]
  [CStarModule ℂᵐᵒᵖ E] [CompleteSpace E]

/-- The scalar crossed product identified with `C*_r(Γ)`. -/
abbrev crossedHom (Γ : Type) [Group Γ] [Countable Γ] : GroupCrossed Γ →⋆ₙₐ[ℂ] ReducedGroupCStar Γ :=
  (reducedCrossedScalarProductEquiv (Γ := Γ)).toNonUnitalStarAlgHom

/-- Assembly of an even point cycle on which `Γ` acts through `χ` and the point unitally:
`P_χ` pushed forward along the underlying scalar class. -/
theorem spaceAssembly_even_mk (c0 : Cutoff.CutoffFunction Γ FiniteGroupPoint.{0})
    (χ : Γ →* unitary ℂ) (c : KasparovCycle (pointAction Γ) (scalarAction Γ) E)
    (hU : ∀ g x, c.groupAction.action g x = (χ g : ℂ) • x)
    (h1 : c.representation (pointScalar 1) = 1) :
    Assembly.spaceAssemblyHom Γ FiniteGroupPoint.{0} false c0
        (KasparovHomotopyClass.mk (BundledKasparovCycle.of c)) =
      letI : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
      letI : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
      operatorK0UnitalEquiv (ReducedGroupCStar Γ)
        (operatorK0Map ((crossedHom Γ).comp (characterHom Γ χ))
          (scalarKKOperatorK0AddEquiv
            (KasparovHomotopyClass.mk (BundledKasparovCycle.of (pointScalarCycle c))))) := by
  change Assembly.reducedScalarKKToAnalyticHom Γ false (Assembly.cutoffProductHom Γ FiniteGroupPoint.{0} false c0
    (KasparovDescent.classHom (scalarAction Γ) (pointAction Γ) false
      (KasparovHomotopyClass.mk (BundledKasparovCycle.of c)))) = _
  rw [cutoffProductHom_eq_averagingPullback]
  erw [even_compressedDescent χ c hU h1]
  let : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
  change operatorK0UnitalEquiv (ReducedGroupCStar Γ) (operatorK0Map (crossedHom Γ)
    (scalarKKOperatorK0AddEquiv (GroupUniverseOrdinaryEven.coefficientPushforward.{0,0,0}
      (characterHom Γ χ) _))) = _
  rw [scalarKKOperatorK0AddEquiv_natural, ← AddMonoidHom.comp_apply, ← operatorK0Map_comp]

/-- Odd analogue of `spaceAssembly_even_mk`. -/
theorem spaceAssembly_odd_mk (c0 : Cutoff.CutoffFunction Γ FiniteGroupPoint.{0})
    (χ : Γ →* unitary ℂ) (c : OddKasparovCycle (pointAction Γ) (scalarAction Γ) E)
    (hU : ∀ g x, c.groupAction.action g x = (χ g : ℂ) • x)
    (h1 : c.representation (pointScalar 1) = 1) :
    Assembly.spaceAssemblyHom Γ FiniteGroupPoint.{0} true c0
        (OddKK.mk (BundledOddKasparovCycle.of c)) =
      letI : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
      letI : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
      operatorK1UnitalEquiv (ReducedGroupCStar Γ)
        (operatorK1Map ((crossedHom Γ).comp (characterHom Γ χ))
          (oddKKOperatorK1AllModuleUniversesAddEquiv
            (OddKK.mk (BundledOddKasparovCycle.of (oddPointScalarCycle c))))) := by
  change Assembly.reducedScalarKKToAnalyticHom Γ true (Assembly.cutoffProductHom Γ FiniteGroupPoint.{0} true c0
    (KasparovDescent.classHom (scalarAction Γ) (pointAction Γ) true
      (OddKK.mk (BundledOddKasparovCycle.of c)))) = _
  rw [cutoffProductHom_eq_averagingPullback]
  erw [odd_compressedDescent χ c hU h1]
  let : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
  change operatorK1UnitalEquiv (ReducedGroupCStar Γ) (operatorK1Map (crossedHom Γ)
    (oddKKOperatorK1AllModuleUniversesAddEquiv (GroupUniverseOrdinaryOdd.coefficientPushforward.{0,0,0}
      (characterHom Γ χ) _))) = _
  simp only [oddKKOperatorK1AllModuleUniversesAddEquiv_apply]
  rw [oddKKOperatorK1Index_independentCoefficientPushforward, ← AddMonoidHom.comp_apply,
    ← operatorK1Map_comp]

/-- Evaluation at the point, the inverse of `ℂ ≅ C₀(pt)`. -/
abbrev pointEval : C₀(FiniteGroupPoint.{0}, ℂ) →⋆ₙₐ[ℂ] ℂ :=
  ((UnitPointCutoff.pointCZeroEquiv FiniteGroupPoint.{0} default).symm : C₀(FiniteGroupPoint.{0}, ℂ) →⋆ₙₐ[ℂ] ℂ)

/-- Evaluation at the point is equivariant for the trivial actions. -/
theorem pointEval_equivariant : ∀ (k : Unit) (a : C₀(FiniteGroupPoint.{0}, ℂ)),
    pointEval ((CStarAlgebraAction.trivial : CStarAlgebraAction Unit C₀(FiniteGroupPoint.{0}, ℂ)).automorphism k a) =
      unitScalarAction.automorphism k (pointEval a) := fun _ _ => rfl

variable (Γ) in
/-- A scalar cycle over the trivial group, read over the point, inflated to `Γ` and twisted by `χ`. -/
abbrev inflatedCycle (χ : Γ →* unitary ℂ) (c : KasparovCycle unitScalarAction unitScalarAction E) :
    KasparovCycle (pointAction Γ) (scalarAction Γ) E :=
  ((NativeSourcePullback.evenCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Unit C₀(FiniteGroupPoint.{0}, ℂ))
    pointEval pointEval_equivariant c).comap (1 : Γ →* Unit)
    (CStarAlgebraAction.apply_eq_trivial_unit (pointAction Γ))
    (CStarAlgebraAction.apply_eq_trivial_unit (scalarAction Γ))).twist χ

/-- `spaceAssembly_even_mk` for an inflated, twisted cycle with unital scalar representation. -/
theorem spaceAssembly_even_inflated (c0 : Cutoff.CutoffFunction Γ FiniteGroupPoint.{0})
    (χ : Γ →* unitary ℂ) (c : KasparovCycle unitScalarAction unitScalarAction E) (h1 : ∀ z x, c.representation z x = z • x) :
    Assembly.spaceAssemblyHom Γ FiniteGroupPoint.{0} false c0
        (KasparovHomotopyClass.mk (BundledKasparovCycle.of (inflatedCycle Γ χ c))) =
      letI : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
      letI : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
      operatorK0UnitalEquiv (ReducedGroupCStar Γ)
        (operatorK0Map ((crossedHom Γ).comp (characterHom Γ χ))
          (scalarKKOperatorK0AddEquiv (KasparovHomotopyClass.mk (BundledKasparovCycle.of c)))) := by
  have hU : ∀ g x, (inflatedCycle Γ χ c).groupAction.action g x = (χ g : ℂ) • x := by
    intro g x
    change (χ g : ℂ) • c.groupAction.action ((1 : Γ →* Unit) g) x = _
    rw [MonoidHom.one_apply, EquivariantHilbertModule.one_apply]
  have h1' : (inflatedCycle Γ χ c).representation (pointScalar 1) = 1 := by
    ext x
    exact (h1 1 x).trans (one_smul ℂ x)
  rw [spaceAssembly_even_mk c0 χ _ hU h1']
  congr 3

variable (Γ) in
/-- The odd analogue of `inflatedCycle`. -/
abbrev oddInflatedCycle (χ : Γ →* unitary ℂ) (c : OddKasparovCycle unitScalarAction unitScalarAction E) :
    OddKasparovCycle (pointAction Γ) (scalarAction Γ) E :=
  ((NativeSourcePullback.oddCycle (CStarAlgebraAction.trivial : CStarAlgebraAction Unit C₀(FiniteGroupPoint.{0}, ℂ))
    pointEval pointEval_equivariant c).comap (1 : Γ →* Unit)
    (CStarAlgebraAction.apply_eq_trivial_unit (pointAction Γ))
    (CStarAlgebraAction.apply_eq_trivial_unit (scalarAction Γ))).twist χ

/-- Odd analogue of `spaceAssembly_even_inflated`. -/
theorem spaceAssembly_odd_inflated (c0 : Cutoff.CutoffFunction Γ FiniteGroupPoint.{0})
    (χ : Γ →* unitary ℂ) (c : OddKasparovCycle unitScalarAction unitScalarAction E) (h1 : ∀ z x, c.representation z x = z • x) :
    Assembly.spaceAssemblyHom Γ FiniteGroupPoint.{0} true c0
        (OddKK.mk (BundledOddKasparovCycle.of (oddInflatedCycle Γ χ c))) =
      letI : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
      letI : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
      operatorK1UnitalEquiv (ReducedGroupCStar Γ)
        (operatorK1Map ((crossedHom Γ).comp (characterHom Γ χ))
          (oddKKOperatorK1AllModuleUniversesAddEquiv (OddKK.mk (BundledOddKasparovCycle.of c)))) := by
  have hU : ∀ g x, (oddInflatedCycle Γ χ c).groupAction.action g x = (χ g : ℂ) • x := by
    intro g x
    change (χ g : ℂ) • c.groupAction.action ((1 : Γ →* Unit) g) x = _
    rw [MonoidHom.one_apply, EquivariantHilbertModule.one_apply]
  have h1' : (oddInflatedCycle Γ χ c).representation (pointScalar 1) = 1 := by
    ext x
    exact (h1 1 x).trans (one_smul ℂ x)
  rw [spaceAssembly_odd_mk c0 χ _ hU h1']
  congr 3

local instance pointCZero_separable : TopologicalSpace.SeparableSpace C₀(FiniteGroupPoint.{0}, ℂ) :=
  TopologicalKHomology.cZero_separableSpace

omit [Countable Γ] [Fintype Γ] in
/-- Twisting by the trivial character is the identity on even classes. -/
theorem twist_one_even (x : KasparovHomotopyClass.{0,0,0,0} (pointAction Γ) (scalarAction Γ)) :
    KasparovHomotopyClass.twist (1 : Γ →* unitary ℂ) x = x := by
  induction x using Quotient.inductionOn with
  | h c => exact KasparovHomotopyClass.mk_eq_of_iso (c.cycle.twistTrivialIso 1 fun _ => rfl)

omit [Countable Γ] [Fintype Γ] in
/-- Twisting by the trivial character is the identity on odd classes. -/
theorem twist_one_odd (x : OddKK.{0,0,0,0} (pointAction Γ) (scalarAction Γ)) :
    OddKK.twist (1 : Γ →* unitary ℂ) x = x := by
  induction x using Quotient.inductionOn with
  | h c => exact OddKK.mk_eq_of_iso (c.cycle.twistTrivialIso 1 fun _ => rfl)

/-- Class form, even: inflate the pulled-back class, twist by `χ`, assemble. -/
theorem spaceAssembly_even_class (c0 : Cutoff.CutoffFunction Γ FiniteGroupPoint.{0})
    (χ : Γ →* unitary ℂ) (a : KasparovHomotopyClass.{0,0,0,0} unitScalarAction unitScalarAction) :
    Assembly.spaceAssemblyHom Γ FiniteGroupPoint.{0} false c0
        (KasparovHomotopyClass.twist χ (KasparovHomotopyClass.comap (1 : Γ →* Unit)
          (CStarAlgebraAction.apply_eq_trivial_unit (pointAction Γ))
          (CStarAlgebraAction.apply_eq_trivial_unit (scalarAction Γ))
          (sourcePullback.{0,0,0,0,0} false pointEval pointEval_equivariant a))) =
      letI : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
      letI : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
      operatorK0UnitalEquiv (ReducedGroupCStar Γ)
        (operatorK0Map ((crossedHom Γ).comp (characterHom Γ χ)) (scalarKKOperatorK0AddEquiv a)) := by
  induction a using Quotient.inductionOn with
  | h c =>
    cases c with | mk F c =>
    have h := KasparovCycle.scalarSupport_class c
    refine (congrArg (fun y => Assembly.spaceAssemblyHom Γ FiniteGroupPoint.{0} false c0
      (KasparovHomotopyClass.twist χ (KasparovHomotopyClass.comap (1 : Γ →* Unit)
        (CStarAlgebraAction.apply_eq_trivial_unit (pointAction Γ))
        (CStarAlgebraAction.apply_eq_trivial_unit (scalarAction Γ))
        (sourcePullback.{0,0,0,0,0} false pointEval pointEval_equivariant y)))) h).trans ?_
    erw [NativeSourcePullback.even_mk, spaceAssembly_even_inflated c0 χ _
      (fun z x => c.scalarSupportRepresentation_apply z x)]
    erw [← h]
    rfl

/-- Class form, odd. -/
theorem spaceAssembly_odd_class (c0 : Cutoff.CutoffFunction Γ FiniteGroupPoint.{0})
    (χ : Γ →* unitary ℂ) (a : OddKK.{0,0,0,0} unitScalarAction unitScalarAction) :
    Assembly.spaceAssemblyHom Γ FiniteGroupPoint.{0} true c0
        (OddKK.twist χ (OddKK.comap (1 : Γ →* Unit)
          (CStarAlgebraAction.apply_eq_trivial_unit (pointAction Γ))
          (CStarAlgebraAction.apply_eq_trivial_unit (scalarAction Γ))
          (sourcePullback.{0,0,0,0,0} true pointEval pointEval_equivariant a))) =
      letI : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
      letI : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
      operatorK1UnitalEquiv (ReducedGroupCStar Γ)
        (operatorK1Map ((crossedHom Γ).comp (characterHom Γ χ))
          (oddKKOperatorK1AllModuleUniversesAddEquiv a)) := by
  induction a using Quotient.inductionOn with
  | h c =>
    cases c with | mk F c =>
    have h := OddKasparovCycle.scalarSupport_class c
    refine (congrArg (fun y => Assembly.spaceAssemblyHom Γ FiniteGroupPoint.{0} true c0
      (OddKK.twist χ (OddKK.comap (1 : Γ →* Unit)
        (CStarAlgebraAction.apply_eq_trivial_unit (pointAction Γ))
        (CStarAlgebraAction.apply_eq_trivial_unit (scalarAction Γ))
        (sourcePullback.{0,0,0,0,0} true pointEval pointEval_equivariant y)))) h).trans ?_
    erw [NativeSourcePullback.odd_mk, spaceAssembly_odd_inflated c0 χ _
      (fun z x => c.scalarSupportRepresentation_apply z x)]
    erw [← h]
    rfl

section Algebra

omit [Countable Γ] [Fintype Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- The crossed-product equivalence sends `λ_g` to the left regular operator. -/
theorem crossedHom_regular [Countable Γ] (g : Γ) :
    crossedHom Γ (regular Γ g) = ⟨regularOperator g, regularOperator_mem_reducedAlgebra g⟩ := by
  apply Subtype.ext
  have h : reducedCrossedGenerator (scalarAction Γ) 1 g = reducedCrossedRegular g := by
    rw [reducedCrossedGenerator, reducedCrossedCoefficient_scalar, one_smul, one_mul]
  change reducedCrossedScalarOperatorEquiv (reducedCrossedRegular g) = regularOperator g
  rw [← h, reducedCrossedScalarOperatorEquiv_generator, one_smul]

variable (h2 : Nat.card Γ = 2)

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- For `Γ = {1, g}`, the image of `P_χ` in `C*_r(Γ)` is `(1 + χ(g) λ_g) / 2`. -/
theorem crossedHom_characterProjection (χ : Γ →* unitary ℂ) :
    crossedHom Γ (characterProjection Γ χ) =
      (2⁻¹ : ℂ) • (1 : ReducedGroupCStar Γ) + ((2⁻¹ : ℂ) * (χ (orderTwoGenerator h2) : ℂ)) •
        ⟨regularOperator (orderTwoGenerator h2), regularOperator_mem_reducedAlgebra _⟩ := by
  have hcard : (Fintype.card Γ : ℂ) = 2 := by
    rw [Fintype.card_eq_nat_card, h2]; norm_num
  have hone : (⟨regularOperator (1 : Γ), regularOperator_mem_reducedAlgebra 1⟩ :
      ReducedGroupCStar Γ) = 1 := Subtype.ext regularOperator_one
  rw [characterProjection, map_sum, Fintype.sum_eq_add 1 (orderTwoGenerator h2)
    (orderTwoGenerator_ne_one h2).symm (fun x hx => by
      rcases eq_one_or_eq_orderTwoGenerator h2 x with h | h
      · exact absurd h hx.1
      · exact absurd h hx.2)]
  rw [map_smul, map_smul, crossedHom_regular, crossedHom_regular, hone, hcard, map_one,
    OneMemClass.coe_one, mul_one]

omit [Countable Γ] [Fintype Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- `*`-homomorphisms out of `ℂ` agree once they agree at `1`. -/
theorem scalarHom_ext {R : Type*} [NonUnitalCStarAlgebra R] {f f' : ℂ →⋆ₙₐ[ℂ] R}
    (h : f 1 = f' 1) : f = f' := by
  ext z
  rw [show z = z • (1 : ℂ) by simp, map_smul, map_smul, h]

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- The trivial-character projection is the first idempotent of `ℂ × ℂ ≅ C*_r(Γ)`. -/
theorem crossedHom_comp_characterHom_one :
    (crossedHom Γ).comp (characterHom Γ 1) =
      (orderTwoReducedEquiv h2).toNonUnitalStarAlgHom.comp (NonUnitalStarAlgHom.inl ℂ ℂ ℂ) := by
  apply scalarHom_ext
  change crossedHom Γ ((1 : ℂ) • characterProjection Γ 1) = orderTwoReducedEquiv h2 (1, 0)
  rw [one_smul, crossedHom_characterProjection h2,
    orderTwoReducedEquiv_apply h2 (orderTwoGenerator_ne_one h2)]
  simp only [MonoidHom.one_apply, OneMemClass.coe_one]
  norm_num

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- The sign-character projection is the second idempotent of `ℂ × ℂ ≅ C*_r(Γ)`. -/
theorem crossedHom_comp_characterHom_sign :
    (crossedHom Γ).comp (characterHom Γ (orderTwoUnitarySign h2)) =
      (orderTwoReducedEquiv h2).toNonUnitalStarAlgHom.comp (NonUnitalStarAlgHom.inr ℂ ℂ ℂ) := by
  apply scalarHom_ext
  change crossedHom Γ ((1 : ℂ) • characterProjection Γ (orderTwoUnitarySign h2)) =
    orderTwoReducedEquiv h2 (0, 1)
  rw [one_smul, crossedHom_characterProjection h2,
    orderTwoReducedEquiv_apply h2 (orderTwoGenerator_ne_one h2), orderTwoUnitarySign_generator h2]
  norm_num

end Algebra

section Glue

local instance pointCZero_separable' : TopologicalSpace.SeparableSpace C₀(FiniteGroupPoint.{0}, ℂ) :=
  TopologicalKHomology.cZero_separableSpace

variable (h2 : Nat.card Γ = 2)

omit [Fintype Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] in
variable (Γ) in
/-- Even analytic side for `|Γ| = 2`: `KK₀(ℂ,ℂ)² ≅ K₀(ℂ)² ≅ K₀(ℂ × ℂ) ≅ K₀(C*_r Γ)`. -/
def orderTwoK0Equiv :
    KasparovHomotopyClass.{0,0,0,0} unitScalarAction unitScalarAction ×
      KasparovHomotopyClass.{0,0,0,0} unitScalarAction unitScalarAction ≃+ ReducedK0 Γ :=
  letI : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
  letI : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
  (scalarKKOperatorK0AddEquiv.{0,0}.prodCongr scalarKKOperatorK0AddEquiv.{0,0}).trans
    ((operatorK0ProductEquiv ℂ ℂ).symm.trans ((operatorK0MapEquiv (orderTwoReducedEquiv h2)).trans
      (operatorK0UnitalEquiv (ReducedGroupCStar Γ))))

omit [Fintype Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] in
variable (Γ) in
/-- Odd analytic side for `|Γ| = 2`: `KK₁(ℂ,ℂ)² ≅ K₁(ℂ)² ≅ K₁(ℂ × ℂ) ≅ K₁(C*_r Γ)`. -/
def orderTwoK1Equiv :
    OddKK.{0,0,0,0} unitScalarAction unitScalarAction ×
      OddKK.{0,0,0,0} unitScalarAction unitScalarAction ≃+ ReducedK1 Γ :=
  letI : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
  letI : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
  (oddKKOperatorK1AllModuleUniversesAddEquiv.{0,0}.prodCongr
    oddKKOperatorK1AllModuleUniversesAddEquiv.{0,0}).trans
    ((operatorK1ProductEquiv ℂ ℂ).symm.trans ((operatorK1MapEquiv (orderTwoReducedEquiv h2)).trans
      (operatorK1UnitalEquiv (ReducedGroupCStar Γ))))

omit [Fintype Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] in
variable (Γ) in
/-- The analytic side for `|Γ| = 2` in either parity. -/
def orderTwoAnalyticEquiv (p : Bool) :
    KKParityGroup.{0,0,0,0} p unitScalarAction unitScalarAction ×
      KKParityGroup.{0,0,0,0} p unitScalarAction unitScalarAction ≃+
      Assembly.analyticGroup Γ p :=
  match p with
  | false => orderTwoK0Equiv Γ h2
  | true => orderTwoK1Equiv Γ h2

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- `orderTwoK0Equiv` as the sum of the two character pushforwards. -/
theorem orderTwoK0Equiv_apply (a b : KasparovHomotopyClass.{0,0,0,0} unitScalarAction unitScalarAction) :
    orderTwoK0Equiv Γ h2 (a, b) =
      letI : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
      letI : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
      operatorK0UnitalEquiv (ReducedGroupCStar Γ)
          (operatorK0Map ((crossedHom Γ).comp (characterHom Γ 1)) (scalarKKOperatorK0AddEquiv a)) +
        operatorK0UnitalEquiv (ReducedGroupCStar Γ)
          (operatorK0Map ((crossedHom Γ).comp (characterHom Γ (orderTwoUnitarySign h2)))
            (scalarKKOperatorK0AddEquiv b)) := by
  rw [crossedHom_comp_characterHom_one h2, crossedHom_comp_characterHom_sign h2, operatorK0Map_comp,
    operatorK0Map_comp, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ← map_add, ← map_add,
    ← operatorK0ProductEquiv_symm_apply]
  rfl

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- `orderTwoK1Equiv` as the sum of the two character pushforwards. -/
theorem orderTwoK1Equiv_apply (a b : OddKK.{0,0,0,0} unitScalarAction unitScalarAction) :
    orderTwoK1Equiv Γ h2 (a, b) =
      letI : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
      letI : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
      operatorK1UnitalEquiv (ReducedGroupCStar Γ)
          (operatorK1Map ((crossedHom Γ).comp (characterHom Γ 1))
            (oddKKOperatorK1AllModuleUniversesAddEquiv a)) +
        operatorK1UnitalEquiv (ReducedGroupCStar Γ)
          (operatorK1Map ((crossedHom Γ).comp (characterHom Γ (orderTwoUnitarySign h2)))
            (oddKKOperatorK1AllModuleUniversesAddEquiv b)) := by
  rw [crossedHom_comp_characterHom_one h2, crossedHom_comp_characterHom_sign h2, operatorK1Map_comp,
    operatorK1Map_comp, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ← map_add, ← map_add,
    ← operatorK1ProductEquiv_symm_apply]
  rfl

/-- On the point, the assembly map is the eigen split `orderTwoPointKKSplit` followed by
`orderTwoAnalyticEquiv`, in both parities and for every cutoff. -/
theorem spaceAssemblyHom_orderTwo (c0 : Cutoff.CutoffFunction Γ FiniteGroupPoint.{0}) (p : Bool)
    (x : TopologicalKHomology.spaceGroup p Γ FiniteGroupPoint.{0}) :
    Assembly.spaceAssemblyHom Γ FiniteGroupPoint.{0} p c0 x =
      orderTwoAnalyticEquiv Γ h2 p (orderTwoPointKKSplit.{0,0} FiniteGroupPoint.{0} h2 default p x) := by
  obtain ⟨⟨a, b⟩, rfl⟩ := (orderTwoPointKKSplit.{0,0} FiniteGroupPoint.{0} h2 default p).symm.surjective x
  rw [AddEquiv.apply_symm_apply]
  cases p
  · have ha := spaceAssembly_even_class c0 1 a
    rw [twist_one_even] at ha
    exact ((map_add (Assembly.spaceAssemblyHom Γ FiniteGroupPoint.{0} false c0) _ _).trans
      (congrArg₂ (· + ·) ha (spaceAssembly_even_class c0 (orderTwoUnitarySign h2) b))).trans
      (orderTwoK0Equiv_apply h2 a b).symm
  · have ha := spaceAssembly_odd_class c0 1 a
    rw [twist_one_odd] at ha
    exact ((map_add (Assembly.spaceAssemblyHom Γ FiniteGroupPoint.{0} true c0) _ _).trans
      (congrArg₂ (· + ·) ha (spaceAssembly_odd_class c0 (orderTwoUnitarySign h2) b))).trans
      (orderTwoK1Equiv_apply h2 a b).symm

end Glue

end BC4lean.Chapter8Examples.OrderTwoAssembly

namespace BC4lean.Chapter8Examples
open OrderTwoAssembly KKTheory OrderTwo

/-- The reduced assembly map of a group of order two, as an explicit additive equivalence. -/
def orderTwoAssemblyAddEquiv (Γ : Type) [Group Γ] [Countable Γ] [TopologicalSpace Γ]
    [DiscreteTopology Γ] (h2 : Nat.card Γ = 2) (p : Bool) :
    TopologicalKHomology.topologicalGroup p Γ ≃+ Assembly.analyticGroup Γ p :=
  haveI : Finite Γ := finite_of_card_eq_two h2
  (finiteTopologicalPointSpaceEquiv Γ p).trans
    ((orderTwoPointKKSplit.{0,0} FiniteGroupPoint.{0} h2 default p).trans (orderTwoAnalyticEquiv Γ h2 p))

/-- Identification with Chapter 7's canonical assembly map. -/
theorem reducedAssemblyHom_orderTwo_eq (Γ : Type) [Group Γ] [Countable Γ] [TopologicalSpace Γ]
    [DiscreteTopology Γ] (h2 : Nat.card Γ = 2) (p : Bool)
    (x : TopologicalKHomology.topologicalGroup p Γ) :
    Assembly.reducedAssemblyHom Γ p x = orderTwoAssemblyAddEquiv Γ h2 p x := by
  have : Finite Γ := finite_of_card_eq_two h2
  let : Fintype Γ := Fintype.ofFinite Γ
  rw [reducedAssemblyHom_finitePoint]
  exact spaceAssemblyHom_orderTwo (Γ := Γ) h2 (finitePointCutoff Γ) p _

/-- The coefficient-free reduced Baum–Connes property for every countable discrete group of
order two. -/
theorem baumConnesProperty_of_card_two (Γ : Type) [Group Γ] [Countable Γ] [TopologicalSpace Γ]
    [DiscreteTopology Γ] (h2 : Nat.card Γ = 2) : Assembly.BaumConnesProperty Γ := by
  intro p
  have h : (Assembly.reducedAssemblyHom Γ p :
      TopologicalKHomology.topologicalGroup p Γ → Assembly.analyticGroup Γ p) =
      orderTwoAssemblyAddEquiv Γ h2 p := funext (reducedAssemblyHom_orderTwo_eq Γ h2 p)
  rw [h]
  exact (orderTwoAssemblyAddEquiv Γ h2 p).bijective

/-- The cyclic group of order two, with the discrete topology. -/
theorem baumConnesProperty_zmod_two :
    letI : TopologicalSpace (Multiplicative (ZMod 2)) := ⊥
    haveI : DiscreteTopology (Multiplicative (ZMod 2)) := ⟨rfl⟩
    Assembly.BaumConnesProperty (Multiplicative (ZMod 2)) :=
  letI : TopologicalSpace (Multiplicative (ZMod 2)) := ⊥
  haveI : DiscreteTopology (Multiplicative (ZMod 2)) := ⟨rfl⟩
  baumConnesProperty_of_card_two _ (by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card])

end BC4lean.Chapter8Examples

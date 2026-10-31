import BC4lean.OperatorK0Product
import BC4lean.OperatorK1Product
import BC4lean.OperatorKUnitalAgreement

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Operator K-theory of products and of `*`-isomorphisms

The operator K-groups of a product of unital C*-algebras are the products of the K-groups
(`operatorK0ProductEquiv`, `operatorK1ProductEquiv`), with the projections as forward maps and the
inclusions as inverse; a `*`-isomorphism induces isomorphisms of operator K-groups
(`operatorK0MapEquiv`, `operatorK1MapEquiv`); the zero homomorphism induces zero.
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

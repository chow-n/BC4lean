import BC4lean.OperatorK0Product
import BC4lean.OperatorK1Product
import BC4lean.OperatorK0Equivalence
import BC4lean.OperatorK1Equivalence
import Mathlib.Algebra.Order.Star.Pi

/-! # Finite product decomposition for unital operator K-theory

`k0ProductEquiv` and `k1ProductEquiv` split K-theory of a binary product. Here
the splitting is extended to products indexed by `Fin n`, by induction on `n`
through `(Π i : Fin (n + 1), A i) ≃ A 0 × Π i : Fin n, A i.succ`. The empty
product is the zero algebra, whose K-groups vanish.
-/

noncomputable section
namespace BC4lean.OperatorKTheory

universe u

section Subsingleton
variable {B : Type u} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [Subsingleton B]

/-- Over the zero algebra every finite matrix projection is equivalent to the empty one. -/
theorem FiniteProjection.equivalent_zero_of_subsingleton (p : FiniteProjection B) :
    FiniteProjection.Equivalent p FiniteProjection.zero := by
  refine ⟨0, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- K₀ of the zero algebra is trivial. -/
instance K0.subsingleton_of_subsingleton : Subsingleton (K0 B) := by
  have h : AddMonoidHom.id (K0 B) = 0 := by
    apply k0Hom_ext
    intro p
    rw [AddMonoidHom.id_apply, AddMonoidHom.zero_apply,
      k0Projection_eq_of_equivalent (FiniteProjection.equivalent_zero_of_subsingleton p),
      k0Projection_zero]
  refine ⟨fun x y => ?_⟩
  rw [← AddMonoidHom.id_apply (K0 B) x, ← AddMonoidHom.id_apply (K0 B) y, h]
  rfl

/-- K₁ of the zero algebra is trivial: every matrix unitary is the identity. -/
instance K1.subsingleton_of_subsingleton : Subsingleton (K1 B) := by
  have h : ∀ x : K1 B, x = 0 := by
    intro x
    refine Quotient.inductionOn x ?_
    intro a
    have ha : a = FiniteUnitary.identity a.Index := by
      cases a
      exact congrArg _ (Subsingleton.elim _ _)
    change K1.of a = 0
    rw [ha, K1.of_identity]
  exact ⟨fun x y => (h x).trans (h y).symm⟩

end Subsingleton

section FinSucc
variable {n : ℕ} (A : Fin (n + 1) → Type u) [∀ i, CStarAlgebra (A i)]

/-- Split off the first factor of a product of C⋆-algebras indexed by `Fin (n + 1)`. -/
def piFinSuccStarAlgEquiv : (Π i, A i) ≃⋆ₐ[ℂ] A 0 × Π i : Fin n, A i.succ where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := by simp
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_star' _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem piFinSuccStarAlgEquiv_apply (f : Π i, A i) :
    piFinSuccStarAlgEquiv A f = (f 0, fun i : Fin n => f i.succ) := rfl

/-- The same splitting for products of abelian groups. -/
def piFinSuccAddEquiv (G : Fin (n + 1) → Type*) [∀ i, AddCommGroup (G i)] :
    (Π i, G i) ≃+ G 0 × Π i : Fin n, G i.succ where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := by simp
  map_add' _ _ := rfl

end FinSucc

/-- K₀ carries products of unital C⋆-algebras indexed by `Fin n` to products of groups. -/
def k0PiEquiv : ∀ {n : ℕ} (A : Fin n → Type u) [∀ i, CStarAlgebra (A i)]
    [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)],
    K0 (Π i, A i) ≃+ Π i, K0 (A i)
  | 0, _, _, _, _ =>
    { toFun := fun _ => 0
      invFun := fun _ => 0
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _
      map_add' := fun _ _ => (add_zero 0).symm }
  | _ + 1, A, _, _, _ =>
    (k0Equiv (piFinSuccStarAlgEquiv A)).trans <|
      (k0ProductEquiv _ _).trans <|
        (AddEquiv.prodCongr (AddEquiv.refl _) (k0PiEquiv fun i => A i.succ)).trans
          (piFinSuccAddEquiv fun i => K0 (A i)).symm

/-- K₁ carries products of unital C⋆-algebras indexed by `Fin n` to products of groups. -/
def k1PiEquiv : ∀ {n : ℕ} (A : Fin n → Type u) [∀ i, CStarAlgebra (A i)]
    [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)],
    K1 (Π i, A i) ≃+ Π i, K1 (A i)
  | 0, _, _, _, _ =>
    { toFun := fun _ => 0
      invFun := fun _ => 0
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _
      map_add' := fun _ _ => (add_zero 0).symm }
  | _ + 1, A, _, _, _ =>
    (k1Equiv (piFinSuccStarAlgEquiv A)).trans <|
      (k1ProductEquiv _ _).trans <|
        (AddEquiv.prodCongr (AddEquiv.refl _) (k1PiEquiv fun i => A i.succ)).trans
          (piFinSuccAddEquiv fun i => K1 (A i)).symm

/-- K₀ does not depend on the compatible order chosen on the algebra: the two orders give
two syntactically different types, identified by `k0Equiv` of the identity. -/
def k0OrderEquiv (B : Type u) [CStarAlgebra B] (o₁ : PartialOrder B)
    (s₁ : @StarOrderedRing B _ o₁ _) (o₂ : PartialOrder B)
    (s₂ : @StarOrderedRing B _ o₂ _) : @K0 B _ o₁ s₁ ≃+ @K0 B _ o₂ s₂ :=
  @k0Equiv B B _ _ o₁ s₁ o₂ s₂ (StarAlgEquiv.refl ℂ B)

/-- K₁ does not depend on the compatible order chosen on the algebra. -/
def k1OrderEquiv (B : Type u) [CStarAlgebra B] (o₁ : PartialOrder B)
    (s₁ : @StarOrderedRing B _ o₁ _) (o₂ : PartialOrder B)
    (s₂ : @StarOrderedRing B _ o₂ _) : @K1 B _ o₁ s₁ ≃+ @K1 B _ o₂ s₂ :=
  @k1Equiv B B _ _ o₁ s₁ o₂ s₂ (StarAlgEquiv.refl ℂ B)

end BC4lean.OperatorKTheory

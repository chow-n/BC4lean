import BC4lean.ScalarOperatorK0
import BC4lean.ScalarOperatorK1
import BC4lean.ReducedOperatorK1
import BC4lean.OperatorKMatrixStability
import BC4lean.OperatorKFinitePi
import BC4lean.FiniteGroupCStarMatrix

/-! # K-theory of the reduced group C⋆-algebra of a finite group

For a finite group `Γ`, `K₀(C*_r(Γ)) ≅ ℤ^c` with `c` the number of conjugacy classes of `Γ`, and
`K₁(C*_r(Γ)) = 0`.

The proof assembles four results. `C*_r(Γ)` is ⋆-isomorphic to a product of `c` full matrix
algebras `M_{d i}(ℂ)` (`exists_reducedStarAlgEquiv_pi_conjClasses`); K-theory is invariant under
⋆-isomorphism (`k0Equiv`, `k1Equiv`); it carries finite products to products (`k0PiEquiv`,
`k1PiEquiv`); it is matrix stable (`k0MatrixEquiv`, `k1MatrixEquiv`); and `K₀(ℂ) ≅ ℤ`,
`K₁(ℂ) = 0` (`k0ScalarEquiv`, `k1Scalar_eq_zero`).

The orders on the matrix blocks are their spectral orders, as on `C*_r(Γ)` in `ReducedK0`. The
product carries the product order; K-groups do not depend on the compatible order chosen.

## Main declarations

* `BC4lean.OperatorKTheory.k0PiMatrixEquiv`: `K₀(Π i : Fin n, M_{d i}(ℂ)) ≃+ (Fin n → ℤ)`.
* `BC4lean.OperatorKTheory.k1PiMatrix_eq_zero`: `K₁(Π i : Fin n, M_{d i}(ℂ)) = 0`.
* `BC4lean.reducedK0EquivOfStarAlgEquiv`: `ReducedK0 Γ ≃+ (Fin n → ℤ)` from any ⋆-isomorphism
  `C*_r(Γ) ≃⋆ₐ[ℂ] Π i : Fin n, M_{d i}(ℂ)`.
* `BC4lean.reducedK0_finite`: `ReducedK0 Γ ≃+ (Fin (Nat.card (ConjClasses Γ)) → ℤ)` for finite `Γ`.
* `BC4lean.reducedK1_finite`: every element of `ReducedK1 Γ` is zero for finite `Γ`.
* `BC4lean.reducedK0_of_card_eq_two`: `ReducedK0 Γ ≃+ (Fin 2 → ℤ)` when `Nat.card Γ = 2`.
-/

noncomputable section

open scoped ComplexOrder

namespace BC4lean.OperatorKTheory

section MatrixBlocks

variable {n : ℕ} (d : Fin n → ℕ) [∀ i, NeZero (d i)]
variable [∀ i, PartialOrder (CStarMatrix (Fin (d i)) (Fin (d i)) ℂ)]
variable [∀ i, StarOrderedRing (CStarMatrix (Fin (d i)) (Fin (d i)) ℂ)]

/-- K₀ of a finite product of full matrix algebras over `ℂ` is free abelian on the blocks. -/
def k0PiMatrixEquiv : K0 (Π i, CStarMatrix (Fin (d i)) (Fin (d i)) ℂ) ≃+ (Fin n → ℤ) :=
  (k0PiEquiv _).trans <| AddEquiv.piCongrRight fun _ => k0MatrixEquiv.trans k0ScalarEquiv

/-- K₁ of a finite product of full matrix algebras over `ℂ` vanishes. -/
theorem k1PiMatrix_eq_zero (x : K1 (Π i, CStarMatrix (Fin (d i)) (Fin (d i)) ℂ)) : x = 0 := by
  have : ∀ i, Subsingleton (K1 (CStarMatrix (Fin (d i)) (Fin (d i)) ℂ)) := fun _ =>
    k1MatrixEquiv.injective.subsingleton
  have : Subsingleton (K1 (Π i, CStarMatrix (Fin (d i)) (Fin (d i)) ℂ)) :=
    (k1PiEquiv _).injective.subsingleton
  exact Subsingleton.elim _ _

end MatrixBlocks

end BC4lean.OperatorKTheory

namespace BC4lean

open OperatorKTheory

variable {Γ : Type*} [Group Γ]

section Decomposition

variable {n : ℕ} {d : Fin n → ℕ} [∀ i, NeZero (d i)]

/-- `K₀(C*_r(Γ)) ≅ ℤⁿ`, given a ⋆-isomorphism of `C*_r(Γ)` onto `n` full matrix blocks. -/
def reducedK0EquivOfStarAlgEquiv
    (e : ReducedGroupCStar Γ ≃⋆ₐ[ℂ] Π i, CStarMatrix (Fin (d i)) (Fin (d i)) ℂ) :
    ReducedK0 Γ ≃+ (Fin n → ℤ) :=
  letI := CStarAlgebra.spectralOrder (ReducedGroupCStar Γ)
  letI := CStarAlgebra.spectralOrderedRing (ReducedGroupCStar Γ)
  letI (i : Fin n) := CStarAlgebra.spectralOrder (CStarMatrix (Fin (d i)) (Fin (d i)) ℂ)
  letI (i : Fin n) := CStarAlgebra.spectralOrderedRing (CStarMatrix (Fin (d i)) (Fin (d i)) ℂ)
  (k0Equiv e).trans (k0PiMatrixEquiv d)

/-- `K₁(C*_r(Γ)) = 0`, given a ⋆-isomorphism of `C*_r(Γ)` onto full matrix blocks. -/
theorem reducedK1_eq_zero_of_starAlgEquiv
    (e : ReducedGroupCStar Γ ≃⋆ₐ[ℂ] Π i, CStarMatrix (Fin (d i)) (Fin (d i)) ℂ)
    (x : ReducedK1 Γ) : x = 0 := by
  let _ := CStarAlgebra.spectralOrder (ReducedGroupCStar Γ)
  let _ := CStarAlgebra.spectralOrderedRing (ReducedGroupCStar Γ)
  let _ (i : Fin n) := CStarAlgebra.spectralOrder (CStarMatrix (Fin (d i)) (Fin (d i)) ℂ)
  let _ (i : Fin n) := CStarAlgebra.spectralOrderedRing (CStarMatrix (Fin (d i)) (Fin (d i)) ℂ)
  have h (y : K1 (ReducedGroupCStar Γ)) : y = 0 :=
    (k1Equiv e).injective <| by rw [map_zero]; exact k1PiMatrix_eq_zero d _
  exact h x

end Decomposition

section Finite

variable [Finite Γ]

/-- **K₀ of a finite group.** `K₀(C*_r(Γ)) ≅ ℤ^c`, `c` the number of conjugacy classes of `Γ`. -/
theorem reducedK0_finite :
    Nonempty (ReducedK0 Γ ≃+ (Fin (Nat.card (ConjClasses Γ)) → ℤ)) := by
  obtain ⟨d, hd, ⟨e⟩⟩ := exists_reducedStarAlgEquiv_pi_conjClasses (Γ := Γ)
  exact ⟨reducedK0EquivOfStarAlgEquiv e⟩

/-- **K₁ of a finite group.** Every element of `K₁(C*_r(Γ))` is zero. -/
theorem reducedK1_finite (x : ReducedK1 Γ) : x = 0 := by
  obtain ⟨n, d, hd, ⟨e⟩⟩ := exists_reducedStarAlgEquiv_pi (Γ := Γ)
  exact reducedK1_eq_zero_of_starAlgEquiv e x

instance reducedK1_subsingleton : Subsingleton (ReducedK1 Γ) :=
  ⟨fun x y => (reducedK1_finite x).trans (reducedK1_finite y).symm⟩

end Finite

section Abelian

/-- In a commutative group every conjugacy class is a single element. -/
theorem card_conjClasses_of_commute (h : ∀ a b : Γ, a * b = b * a) :
    Nat.card (ConjClasses Γ) = Nat.card Γ := by
  let _ : CommGroup Γ := { ‹Group Γ› with mul_comm := h }
  exact (Nat.card_congr (ConjClasses.mkEquiv (α := Γ))).symm

/-- For a finite commutative group, `K₀(C*_r(Γ)) ≅ ℤ^|Γ|`. -/
theorem reducedK0_of_commute [Finite Γ] (h : ∀ a b : Γ, a * b = b * a) :
    Nonempty (ReducedK0 Γ ≃+ (Fin (Nat.card Γ) → ℤ)) := by
  rw [← card_conjClasses_of_commute h]
  exact reducedK0_finite

/-- A group of order two has two conjugacy classes. -/
theorem card_conjClasses_of_card_eq_two (h2 : Nat.card Γ = 2) :
    Nat.card (ConjClasses Γ) = 2 := by
  have : IsCyclic Γ := isCyclic_of_prime_card (p := 2) h2
  rw [card_conjClasses_of_commute (IsCyclic.commGroup (α := Γ)).mul_comm, h2]

/-- For a group of order two, `K₀(C*_r(Γ)) ≅ ℤ²`. -/
theorem reducedK0_of_card_eq_two (h2 : Nat.card Γ = 2) :
    Nonempty (ReducedK0 Γ ≃+ (Fin 2 → ℤ)) := by
  have : Finite Γ := Nat.finite_of_card_ne_zero (by omega)
  rw [← card_conjClasses_of_card_eq_two h2]
  exact reducedK0_finite

end Abelian

end BC4lean

import BC4lean.GroupIsoModel
import BC4lean.KKGroupRestriction
import BC4lean.GroupUniverseParityGroup
import BC4lean.TopologicalKHomologyDiagram
import BC4lean.DirectedAddGroupColimitMap
import BC4lean.NativeEvenSourcePullback
import BC4lean.NativeOddSourcePullback
import BC4lean.AssemblyColimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Equivariant K-homology along a group isomorphism

Restriction along `e` identifies the piece groups of `X` (for `Γ'`) and of `Pull e X` (for `Γ`),
compatibly with the transitions; hence an additive bijection of the topological K-homology groups.
-/

noncomputable section

/-! ## Equivariant K-homology of a pulled-back space

For `e : Γ ≃* Γ'` and a `Γ'`-space `Y`, restriction along `e` followed by the identification
`C₀(e* Y)`-action `= (C₀(Y)-action) ∘ e` is an additive bijection
`KK^{Γ'}_p(C₀(Y), ℂ) ≃ KK^Γ_p(C₀(e* Y), ℂ)` in both parities. Its inverse is restriction along
`e⁻¹`. The two round trips are restrictions along `e⁻¹ ∘ e` and `e ∘ e⁻¹`, which are the identity
homomorphisms only propositionally; the casts along the resulting equalities of actions are
removed with `subst`, after which restriction along `MonoidHom.id` is the identity definitionally
(structure eta).
-/

namespace BC4lean.KKTheory.GroupIso
open scoped ComplexOrder
open KKTheory.GroupRestriction
open KKTheory KKTheory.GroupUniverseParityGroup

section Parity
universe uΓ uΓ' uΓ'' uA uB uE
variable {A : Type uA} {B : Type uB} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]

/-- Restriction along a group homomorphism on the parity groups. -/
def parityComap {Γ : Type uΓ} {Γ' : Type uΓ'} [Group Γ] [Group Γ'] (f : Γ →* Γ') (p : Bool)
    {α : CStarAlgebraAction Γ' A} {β : CStarAlgebraAction Γ' B} :
    KKParityGroup.{uΓ', uA, uB, uE} p α β →+
      KKParityGroup.{uΓ, uA, uB, uE} p (actionComap f α) (actionComap f β) :=
  match p with
  | false => AddMonoidHom.mk' (evenComap f) (fun x y => evenComap_add f x y)
  | true => AddMonoidHom.mk' (oddComap f) (fun x y => oddComap_add f x y)

/-- Transport between parity groups along equalities of the actions. -/
def parityCast {Γ : Type uΓ} [Group Γ] (p : Bool)
    {α₁ α₂ : CStarAlgebraAction Γ A} {β₁ β₂ : CStarAlgebraAction Γ B}
    (hα : α₁ = α₂) (hβ : β₁ = β₂) :
    KKParityGroup.{uΓ, uA, uB, uE} p α₁ β₁ ≃+ KKParityGroup.{uΓ, uA, uB, uE} p α₂ β₂ := by
  subst hα
  subst hβ
  exact AddEquiv.refl _

/-- Restriction is functorial on the nose. -/
theorem parityComap_comp {Γ : Type uΓ} {Γ' : Type uΓ'} {Γ'' : Type uΓ''}
    [Group Γ] [Group Γ'] [Group Γ''] (f : Γ' →* Γ'') (g : Γ →* Γ') (p : Bool)
    {α : CStarAlgebraAction Γ'' A} {β : CStarAlgebraAction Γ'' B}
    (x : KKParityGroup.{uΓ'', uA, uB, uE} p α β) :
    parityComap g p (parityComap f p x) = parityComap (f.comp g) p x := by
  cases p
  · induction x using Quotient.inductionOn
    rfl
  · induction x using Quotient.inductionOn
    rfl

theorem actionComap_symm_comp {Γ : Type uΓ} {Γ' : Type uΓ'} [Group Γ] [Group Γ']
    (e : Γ ≃* Γ') (α : CStarAlgebraAction Γ' A) :
    actionComap e.symm.toMonoidHom (actionComap e.toMonoidHom α) = α := by
  have h : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Γ' := by
    ext g
    exact e.apply_symm_apply g
  change actionComap (e.toMonoidHom.comp e.symm.toMonoidHom) α = α
  rw [h]
  rfl

/-- A cast between parity groups is heterogeneously equal to its argument. -/
theorem parityCast_heq {Γ : Type uΓ} [Group Γ] (p : Bool)
    {α₁ α₂ : CStarAlgebraAction Γ A} {β₁ β₂ : CStarAlgebraAction Γ B}
    (hα : α₁ = α₂) (hβ : β₁ = β₂) (x : KKParityGroup.{uΓ, uA, uB, uE} p α₁ β₁) :
    HEq (parityCast p hα hβ x) x := by
  subst hα hβ
  rfl

/-- Restriction respects heterogeneous equality along equal actions. -/
theorem parityComap_heq_congr {Γ : Type uΓ} {Γ' : Type uΓ'} [Group Γ] [Group Γ'] (f : Γ →* Γ')
    (p : Bool) {α₁ α₂ : CStarAlgebraAction Γ' A} {β₁ β₂ : CStarAlgebraAction Γ' B}
    (hα : α₁ = α₂) (hβ : β₁ = β₂) {x₁ : KKParityGroup.{uΓ', uA, uB, uE} p α₁ β₁}
    {x₂ : KKParityGroup.{uΓ', uA, uB, uE} p α₂ β₂} (h : HEq x₁ x₂) :
    HEq (parityComap f p x₁) (parityComap f p x₂) := by
  subst hα hβ
  rw [eq_of_heq h]

/-- Restriction along a homomorphism equal to the identity is heterogeneously the identity. -/
theorem parityComap_heq_of_eq_id {Γ : Type uΓ} [Group Γ] (h : Γ →* Γ)
    (hh : h = MonoidHom.id Γ) (p : Bool)
    {α : CStarAlgebraAction Γ A} {β : CStarAlgebraAction Γ B}
    (x : KKParityGroup.{uΓ, uA, uB, uE} p α β) : HEq (parityComap h p x) x := by
  subst hh
  cases p
  · induction x using Quotient.inductionOn
    rfl
  · induction x using Quotient.inductionOn
    rfl

/-- Restriction along a group isomorphism, with the restricted actions replaced by given equal
ones. -/
def parityRelabel {Γ Γ' : Type uΓ} [Group Γ] [Group Γ'] (e : Γ ≃* Γ') (p : Bool)
    {α : CStarAlgebraAction Γ' A} {β : CStarAlgebraAction Γ' B}
    {α' : CStarAlgebraAction Γ A} {β' : CStarAlgebraAction Γ B}
    (hα : actionComap e.toMonoidHom α = α') (hβ : actionComap e.toMonoidHom β = β') :
    KKParityGroup.{uΓ, uA, uB, uE} p α β ≃+ KKParityGroup.{uΓ, uA, uB, uE} p α' β' where
  toFun x := parityCast p hα hβ (parityComap e.toMonoidHom p x)
  invFun y := parityCast p (actionComap_symm_comp e α) (actionComap_symm_comp e β)
    (parityComap e.symm.toMonoidHom p (parityCast p hα.symm hβ.symm y))
  left_inv x := by
    refine eq_of_heq ((parityCast_heq p _ _ _).trans ?_)
    refine (parityComap_heq_congr e.symm.toMonoidHom p rfl rfl
      ((parityCast_heq p _ _ _).trans (parityCast_heq p _ _ _))).trans ?_
    exact (heq_of_eq (parityComap_comp e.toMonoidHom e.symm.toMonoidHom p x)).trans
      (parityComap_heq_of_eq_id _ (by
        ext g
        exact e.apply_symm_apply g) p x)
  right_inv y := by
    refine eq_of_heq ((parityCast_heq p _ _ _).trans ?_)
    refine (parityComap_heq_congr e.toMonoidHom p (actionComap_symm_comp e α).symm
      (actionComap_symm_comp e β).symm (parityCast_heq p _ _ _)).trans ?_
    exact (heq_of_eq (parityComap_comp e.symm.toMonoidHom e.toMonoidHom p _)).trans
      ((parityComap_heq_of_eq_id _ (by
        ext g
        exact e.symm_apply_apply g) p _).trans (parityCast_heq p _ _ _))
  map_add' x y := by
    simp only [map_add]

@[simp] theorem parityRelabel_apply {Γ Γ' : Type uΓ} [Group Γ] [Group Γ'] (e : Γ ≃* Γ')
    (p : Bool) {α : CStarAlgebraAction Γ' A} {β : CStarAlgebraAction Γ' B}
    {α' : CStarAlgebraAction Γ A} {β' : CStarAlgebraAction Γ B}
    (hα : actionComap e.toMonoidHom α = α') (hβ : actionComap e.toMonoidHom β = β')
    (x : KKParityGroup.{uΓ, uA, uB, uE} p α β) :
    parityRelabel e p hα hβ x = parityCast p hα hβ (parityComap e.toMonoidHom p x) := rfl

end Parity

end BC4lean.KKTheory.GroupIso

/-! ## Colimit equivalence along an order isomorphism

Upstream has the colimit map of a diagram morphism (`DirectedAddGroupDiagram.Hom.colimitMap`) but
no equivalence of colimits. Given an order isomorphism `σ : ι ≃o κ` and natural additive bijections
`f i : D i ≃+ E (σ i)`, the colimits are additively equivalent. The inverse is built without casts:
`E k` is first moved to `E (σ (σ⁻¹ k))` by the transition map along `k ≤ σ (σ⁻¹ k)` (an equality of
indices), and then pulled back by `f (σ⁻¹ k)`.
-/

namespace BC4lean.KKTheory.GroupIso
open DirectedAddGroupDiagram

universe u v uκ vκ w

variable {ι : Type u} [Preorder ι] {κ : Type uκ} [Preorder κ]
  {D : DirectedAddGroupDiagram.{u, v} ι} {E : DirectedAddGroupDiagram.{uκ, vκ} κ}
  (σ : ι ≃o κ) (f : ∀ i, D.obj i ≃+ E.obj (σ i))
  (hf : ∀ i j (hij : i ≤ j) (x : D.obj i),
    E.map (σ i) (σ j) (σ.monotone hij) (f i x) = f j (D.map i j hij x))

include hf in
/-- Naturality of the inverse family. -/
theorem colimitEquiv_symm_natural (i j : ι) (hij : i ≤ j) (y : E.obj (σ i)) :
    D.map i j hij ((f i).symm y) = (f j).symm (E.map (σ i) (σ j) (σ.monotone hij) y) := by
  apply (f j).injective
  rw [AddEquiv.apply_symm_apply, ← hf i j hij, AddEquiv.apply_symm_apply]

/-- The backward map on one object of `E`. -/
def colimitEquivInvApp [Nonempty ι] [IsDirectedOrder ι] (k : κ) : E.obj k →+ D.Colimit :=
  (D.of (σ.symm k)).comp (((f (σ.symm k)).symm : E.obj (σ (σ.symm k)) →+ D.obj (σ.symm k)).comp
    (E.map k (σ (σ.symm k)) (σ.apply_symm_apply k).ge))

variable [Nonempty ι] [IsDirectedOrder ι] [Nonempty κ] [IsDirectedOrder κ]

/-- The forward colimit map. -/
def colimitEquivFwd : D.Colimit →+ E.Colimit :=
  D.desc (fun i => (E.of (σ i)).comp (f i : D.obj i →+ E.obj (σ i))) (by
    intro i j hij x
    change E.of (σ j) (f j (D.map i j hij x)) = E.of (σ i) (f i x)
    rw [← hf i j hij, E.of_map])

/-- The backward colimit map. -/
def colimitEquivBwd : E.Colimit →+ D.Colimit :=
  E.desc (colimitEquivInvApp σ f) (by
    intro k k' hkk' y
    change D.of (σ.symm k') ((f (σ.symm k')).symm
        (E.map k' (σ (σ.symm k')) _ (E.map k k' hkk' y))) =
      D.of (σ.symm k) ((f (σ.symm k)).symm (E.map k (σ (σ.symm k)) _ y))
    have hle : σ.symm k ≤ σ.symm k' := σ.symm.monotone hkk'
    rw [← D.of_map hle ((f (σ.symm k)).symm (E.map k (σ (σ.symm k)) _ y)),
      colimitEquiv_symm_natural σ f hf, E.map_comp, E.map_comp])

/-- The colimits are additively equivalent. -/
def colimitEquiv : D.Colimit ≃+ E.Colimit where
  toFun := colimitEquivFwd σ f hf
  invFun := colimitEquivBwd σ f hf
  left_inv z := by
    obtain ⟨i, x, rfl⟩ := D.exists_of z
    change D.of (σ.symm (σ i)) ((f (σ.symm (σ i))).symm
        (E.map (σ i) (σ (σ.symm (σ i))) _ (f i x))) = D.of i x
    have hij : i ≤ σ.symm (σ i) := (σ.symm_apply_apply i).ge
    rw [hf i _ hij, AddEquiv.symm_apply_apply, D.of_map]
  right_inv z := by
    obtain ⟨k, y, rfl⟩ := E.exists_of z
    change E.of (σ (σ.symm k)) (f (σ.symm k) ((f (σ.symm k)).symm
        (E.map k (σ (σ.symm k)) _ y))) = E.of k y
    rw [AddEquiv.apply_symm_apply, E.of_map]
  map_add' := map_add (colimitEquivFwd σ f hf)

@[simp] theorem colimitEquiv_of (i : ι) (x : D.obj i) :
    colimitEquiv σ f hf (D.of i x) = E.of (σ i) (f i x) := rfl

/-- Maps out of the two colimits that agree on corresponding objects agree across the
equivalence. -/
theorem colimitEquiv_comp_eq {P : Type w} [AddCommGroup P] (F : D.Colimit →+ P)
    (G : E.Colimit →+ P) (h : ∀ i (x : D.obj i), G (E.of (σ i) (f i x)) = F (D.of i x))
    (z : D.Colimit) : G (colimitEquiv σ f hf z) = F z := by
  obtain ⟨i, x, rfl⟩ := D.exists_of z
  exact h i x

end BC4lean.KKTheory.GroupIso

/-! ## Piece transitions under relabelling and the map `φ` of the relabelling square

Piece transitions are source pullback along restriction of functions. Restriction along a group
isomorphism commutes with source pullback: on representatives both sides keep the module, the
grading and the operator and precompose the representation (`NativeSourcePullback.even_mk`,
`odd_mk`), so the two cycles agree. With the order isomorphism of pieces (`pieceRelabel`) and the piece-group
bijections this gives an isomorphism of directed systems, hence (`colimitEquiv`) an additive bijection `φ` of
the topological K-homology groups of `X` (for `Γ'`) and of `e* X` (for `Γ`).

`relabelSquare_of_pieces` reduces `RelabelSquare` to the square on each piece.
-/

namespace BC4lean.KKTheory.GroupIso
open scoped ZeroAtInfty ComplexOrder
open KKTheory.GroupRestriction
open KKTheory KKTheory.GroupUniverseParityGroup KKTheory.GroupUniverseParityFunctoriality
open ProperActions

section Abstract
universe uΓ uA uA' uB u
variable {Γ Γ' : Type uΓ} [Group Γ] [Group Γ'] [Countable Γ] [Countable Γ'] (e : Γ ≃* Γ')
  {A' : Type uA'} {A : Type uA} {B : Type uB}
  [NonUnitalCStarAlgebra A'] [PartialOrder A'] [StarOrderedRing A']
  [TopologicalSpace.SeparableSpace A']
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [TopologicalSpace.SeparableSpace A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [TopologicalSpace.SeparableSpace B]

omit [PartialOrder A'] [StarOrderedRing A'] in
/-- Restriction along `e` commutes with source pullback (abstract form). -/
theorem parityComap_sourcePullback (p : Bool) {α' : CStarAlgebraAction Γ' A'}
    {α : CStarAlgebraAction Γ' A} {β : CStarAlgebraAction Γ' B} (f : A' →⋆ₙₐ[ℂ] A)
    (hf : ∀ g a, f (α'.automorphism g a) = α.automorphism g (f a))
    (x : KKParityGroup.{uΓ, uA, uB, max u (max uA' (max uA uB))} p α β) :
    parityComap e.toMonoidHom p (sourcePullback.{uΓ, uA', uA, uB, u} p f hf x) =
      sourcePullback.{uΓ, uA', uA, uB, u} p f (fun g a => hf (e g) a)
        (parityComap e.toMonoidHom p x) := by
  cases p
  · induction x using Quotient.inductionOn with
    | h c =>
      exact (congrArg (parityComap e.toMonoidHom false)
          (NativeSourcePullback.even_mk α' f hf c)).trans
        (NativeSourcePullback.even_mk (α := actionComap e.toMonoidHom α)
          (β := actionComap e.toMonoidHom β) (actionComap e.toMonoidHom α') f
          (fun g a => hf (e g) a) (bundledComap e.toMonoidHom c)).symm
  · induction x using Quotient.inductionOn with
    | h c =>
      exact (congrArg (parityComap e.toMonoidHom true)
          (NativeSourcePullback.odd_mk α' f hf c)).trans
        (NativeSourcePullback.odd_mk (α := actionComap e.toMonoidHom α)
          (β := actionComap e.toMonoidHom β) (actionComap e.toMonoidHom α') f
          (fun g a => hf (e g) a) (bundledOddComap e.toMonoidHom c)).symm

omit [PartialOrder A'] [StarOrderedRing A'] in
/-- `parityComap_sourcePullback` with the restricted actions replaced by given equal ones, and the source map by an equal
one (stated separately so that the kernel never unfolds two definitionally equal restriction
maps against each other; doing so times out). -/
theorem parityRelabel_sourcePullback (p : Bool) {α' : CStarAlgebraAction Γ' A'}
    {α : CStarAlgebraAction Γ' A} {β : CStarAlgebraAction Γ' B}
    {γ' : CStarAlgebraAction Γ A'} {γ : CStarAlgebraAction Γ A} {δ : CStarAlgebraAction Γ B}
    (hα' : actionComap e.toMonoidHom α' = γ') (hα : actionComap e.toMonoidHom α = γ)
    (hβ : actionComap e.toMonoidHom β = δ) (f fγ : A' →⋆ₙₐ[ℂ] A) (hff : f = fγ)
    (hf : ∀ g a, f (α'.automorphism g a) = α.automorphism g (f a))
    (hfγ : ∀ g a, fγ (γ'.automorphism g a) = γ.automorphism g (fγ a))
    (x : KKParityGroup.{uΓ, uA, uB, max u (max uA' (max uA uB))} p α β) :
    parityRelabel e p hα' hβ (sourcePullback.{uΓ, uA', uA, uB, u} p f hf x) =
      sourcePullback.{uΓ, uA', uA, uB, u} p fγ hfγ (parityRelabel e p hα hβ x) := by
  subst hff hα' hα hβ
  exact parityComap_sourcePullback e p f hf x

end Abstract

section Pieces
universe u v
variable {Γ Γ' : Type u} [Group Γ] [Group Γ'] [Countable Γ] [Countable Γ'] (e : Γ ≃* Γ')
  (X : Type v) [TopologicalSpace X] [MulAction Γ' X] [ContinuousConstSMul Γ' X]
  [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X]

local instance piece_locallyCompact' (S : CocompactPiece Γ' X) :
    LocallyCompactSpace S.toInvariantSubset := S.locallyCompact

local instance piece_locallyCompact (S : CocompactPiece Γ (Pull e X)) :
    LocallyCompactSpace S.toInvariantSubset := S.locallyCompact

local instance piece_separable' (S : CocompactPiece Γ' X) :
    TopologicalSpace.SeparableSpace C₀(S.toInvariantSubset, ℂ) :=
  TopologicalKHomology.cZero_separableSpace

local instance piece_separable (S : CocompactPiece Γ (Pull e X)) :
    TopologicalSpace.SeparableSpace C₀(S.toInvariantSubset, ℂ) :=
  TopologicalKHomology.cZero_separableSpace

omit [Countable Γ] [Countable Γ'] [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X] in
/-- The `C₀` action of `Γ` on the relabelled piece is the restriction of that of `Γ'` (`cZeroAction_pull` for
pieces). -/
theorem pieceAction_pull (S : CocompactPiece Γ' X) :
    actionComap e.toMonoidHom (CZero.action Γ' (X := S.toInvariantSubset)) =
      (CZero.action Γ (X := ((pieceRelabel e X).symm S).toInvariantSubset) :
        CStarAlgebraAction Γ C₀(S.toInvariantSubset, ℂ)) := by
  unfold CZero.action actionComap
  congr 1
  ext g a x
  change a ((e g)⁻¹ • x) = a (e g⁻¹ • x)
  rw [map_inv]

/-- On pieces: the piece group of a `Γ'`-piece is that of the corresponding `Γ`-piece. -/
def pieceEquiv (p : Bool) (S : CocompactPiece Γ' X) :
    TopologicalKHomology.pieceGroup p S ≃+
      TopologicalKHomology.pieceGroup p ((pieceRelabel e X).symm S) :=
  parityRelabel e p (pieceAction_pull e X S) (actionComap_trivial e.toMonoidHom)

omit [Countable Γ] [Countable Γ'] [ContinuousConstSMul Γ' X] [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X] in
/-- Restriction of functions is the same map for the two labellings of the pieces. -/
theorem pieceRestriction_pull {S T : CocompactPiece Γ' X} (h : S ≤ T) :
    CZero.pieceRestriction h =
      (CZero.pieceRestriction ((pieceRelabel e X).symm.monotone h) :
        C₀(T.toInvariantSubset, ℂ) →⋆ₙₐ[ℂ] C₀(S.toInvariantSubset, ℂ)) := by
  ext a x
  rfl

omit [Countable Γ] [Countable Γ'] [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X] in
theorem pieceEquiv_apply (p : Bool) (S : CocompactPiece Γ' X)
    (x : TopologicalKHomology.pieceGroup p S) :
    pieceEquiv e X p S x =
      parityRelabel e p (pieceAction_pull e X S) (actionComap_trivial e.toMonoidHom) x :=
  rfl

/-- The piece bijections commute with source pullback along restriction (the transitions,
unfolded). -/
theorem pieceRelabel_sourcePullback (p : Bool) {S T : CocompactPiece Γ' X} (h : S ≤ T)
    (x : TopologicalKHomology.pieceGroup p S) :
    sourcePullback.{u, v, v, 0, v} p
        (CZero.pieceRestriction ((pieceRelabel e X).symm.monotone h))
        (CZero.pieceRestriction_equivariant ((pieceRelabel e X).symm.monotone h))
        (parityRelabel e p (pieceAction_pull e X S) (actionComap_trivial e.toMonoidHom) x) =
      parityRelabel e p (pieceAction_pull e X T) (actionComap_trivial e.toMonoidHom)
        (sourcePullback.{u, v, v, 0, v} p (CZero.pieceRestriction h)
          (CZero.pieceRestriction_equivariant h) x) :=
  (parityRelabel_sourcePullback.{u, v, v, 0, v} e p (pieceAction_pull e X T)
    (pieceAction_pull e X S) (actionComap_trivial e.toMonoidHom) (CZero.pieceRestriction h)
    (CZero.pieceRestriction ((pieceRelabel e X).symm.monotone h))
    (pieceRestriction_pull e X h) (CZero.pieceRestriction_equivariant h)
    (CZero.pieceRestriction_equivariant ((pieceRelabel e X).symm.monotone h)) x).symm

/-- The piece bijections commute with the transitions. The transitions and `pieceEquiv` are
unfolded by rewriting, so that the kernel never compares the folded and unfolded forms. -/
theorem pieceEquiv_transition (p : Bool) {S T : CocompactPiece Γ' X} (h : S ≤ T)
    (x : TopologicalKHomology.pieceGroup p S) :
    TopologicalKHomology.transition p ((pieceRelabel e X).symm.monotone h)
        (pieceEquiv e X p S x) =
      pieceEquiv e X p T (TopologicalKHomology.transition p h x) := by
  rw [show TopologicalKHomology.transition p h x =
      sourcePullback.{u, v, v, 0, v} p (CZero.pieceRestriction h)
        (CZero.pieceRestriction_equivariant h) x from rfl,
    show TopologicalKHomology.transition p ((pieceRelabel e X).symm.monotone h)
        (pieceEquiv e X p S x) =
      sourcePullback.{u, v, v, 0, v} p
        (CZero.pieceRestriction ((pieceRelabel e X).symm.monotone h))
        (CZero.pieceRestriction_equivariant ((pieceRelabel e X).symm.monotone h))
        (pieceEquiv e X p S x) from rfl,
    pieceEquiv_apply, pieceEquiv_apply]
  exact pieceRelabel_sourcePullback e X p h x

/-- The map `φ` (inverse direction): `K^{Γ'}_p(X) ≃ K^Γ_p(e* X)`. -/
def groupRelabel (p : Bool) :
    TopologicalKHomology.group (Γ := Γ') (X := X) p ≃+
      TopologicalKHomology.group (Γ := Γ) (X := Pull e X) p :=
  colimitEquiv (D := TopologicalKHomology.diagram (Γ := Γ') (X := X) p)
    (E := TopologicalKHomology.diagram (Γ := Γ) (X := Pull e X) p)
    (pieceRelabel e X).symm (pieceEquiv e X p)
    (fun _ _ hij x => pieceEquiv_transition e X p hij x)

@[simp] theorem groupRelabel_ofPiece (p : Bool) (S : CocompactPiece Γ' X)
    (x : TopologicalKHomology.pieceGroup p S) :
    groupRelabel e X p (TopologicalKHomology.ofPiece p S x) =
      TopologicalKHomology.ofPiece p ((pieceRelabel e X).symm S) (pieceEquiv e X p S x) := rfl

end Pieces

end BC4lean.KKTheory.GroupIso

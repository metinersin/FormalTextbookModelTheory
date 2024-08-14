import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Satisfiability
import Mathlib.ModelTheory.Bundled
import Mathlib.ModelTheory.Order
import Mathlib.Order.CountableDenseLinearOrder

import FormalTextbookModelTheory.ForMathlib.Matrix


open Cardinal
open FirstOrder Language Structure Theory Order
open Matrix (Vector_eq_VecNotation₂ comp_VecNotation₂)

namespace FirstOrder.Language.Order --region

section

variable {M : Type w} [instStructure : Language.order.Structure M]

/--
The interpretation of the unique binary relation symbol of the language `Language.order` on a type `M` gives a
natural binary relation on `M` and it is written with `≤`.
-/
instance instLE : LE M where
  le := fun x y => instStructure.RelMap leSymb ![x, y]

/--
Given a type `M` and `𝓜 : Language.order.Structure`, the `Language.order.Structure M` instance induced by the `LE M`
instance which is induced by `𝓜` is equal to `𝓜`. In other words, for a fixed type `M`, `@orderStructure M` is the
left-inverse of `@instLE M`.
-/
@[simp]
lemma orderStructure_of_LE : @orderStructure M (@instLE M instStructure) = instStructure := by
  ext1
  · funext _ r
    exfalso
    exact IsEmpty.elim (by infer_instance) r
  · funext n r x
    match n with
    | 0 | 1 | _ + 3 =>
      exfalso
      simp only [Language.order, mk₂_Relations, Sequence₂] at r
      exact IsEmpty.elim (by infer_instance) r
    | 2 =>
      rw [Vector_eq_VecNotation₂ x, (by apply Subsingleton.allEq : r = leSymb)]
      simp only [orderStructure, LE.le, Structure.relMap_apply₂]

/--
By definition, the binary relation `≤` is equal to the interpretation of the unique binary relation symbol of the
language `Language.order`.
-/
instance : @OrderedStructure Language.order M _ instLE instStructure := by
  simp only [OrderedStructure, orderLHom_order, orderStructure_of_LE]
  exact @LHom.id_isExpansionOn Language.order M instStructure

end

section

variable {M : Type w} [Language.order.Structure M]
variable {N : Type w} [Language.order.Structure N]

/--
An order embedding `φ : M ↪o N`, induces and embedding of structures with the same underlying function.
-/
def toLEmbedding (φ : M ↪o N) : M ↪[Language.order] N where
  toEmbedding := φ.toEmbedding
  map_fun' := by
    intro n f
    exfalso
    exact IsEmpty.elim (by infer_instance) f
  map_rel' := by
    intro n r x
    match n with
    | 0 | 1 | _ + 3 =>
      exfalso
      simp [Language.order, Sequence₂] at r
      exact IsEmpty.elim (by infer_instance) r
    | 2 =>
      rw [Vector_eq_VecNotation₂ x, comp_VecNotation₂ φ.toFun,
          (by apply Subsingleton.allEq : r = leSymb), relMap_leSymb, relMap_leSymb]
      exact φ.map_rel_iff

/--
An order isomorphism `φ : M ≃o N`, induces and isomorphism of structures with the same underlying function.
-/
def toLIso (φ : M ≃o N) : M ≃[Language.order] N where
  toEquiv := φ.toEquiv
  map_fun' := (toLEmbedding (φ.toOrderEmbedding)).map_fun'
  map_rel' := (toLEmbedding (φ.toOrderEmbedding)).map_rel'

end

namespace DLO --region

section

variable (M : Type w) [Language.order.Structure M]
variable [M ⊨ Language.order.dlo]

/--
Models of the theory `Language.order.dlo` satisfies the reflexivity sentence.
-/
protected lemma realize_reflexive : M ⊨ (leSymb (L := Language.order)).reflexive := by
  apply realize_sentence_of_mem Language.order.dlo
  unfold dlo linearOrderTheory
  left; left; rfl

/--
Models of the theory `Language.order.dlo` satisfies the transitivity sentence.
-/
protected lemma realize_transitive : M ⊨ (leSymb (L := Language.order)).transitive := by
  apply realize_sentence_of_mem Language.order.dlo
  unfold dlo linearOrderTheory
  left; right; right; left; rfl

/--
Models of the theory `Language.order.dlo` satisfies the antisymmetric sentence.
-/
protected lemma realize_antisymmetric : M ⊨ (leSymb (L := Language.order)).antisymmetric := by
  apply realize_sentence_of_mem Language.order.dlo
  unfold dlo linearOrderTheory
  left; right; left; rfl

/--
Models of the theory `Language.order.dlo` satisfies the totality sentence.
-/
protected lemma realize_total : M ⊨ (leSymb (L := Language.order)).total := by
  apply realize_sentence_of_mem Language.order.dlo
  unfold dlo linearOrderTheory
  left; right; right; right; rfl

/--
Models of the theory `Language.order.dlo` satisfies the densely ordered sentence.
-/
protected lemma realize_denselyOrderedSentence : M ⊨ Language.order.denselyOrderedSentence := by
  apply realize_sentence_of_mem Language.order.dlo
  unfold dlo linearOrderTheory
  right; right; right; rfl

/--
Models of the theory `Language.order.dlo` satisfies the noBotOrder sentence.
-/
protected lemma realize_noBotOrderSentence : M ⊨ Language.order.noBotOrderSentence := by
  apply realize_sentence_of_mem Language.order.dlo
  unfold dlo linearOrderTheory
  right; right; left; rfl

/--
Models of the theory `Language.order.dlo` satisfies the noTopOrder sentence.
-/
protected lemma realize_noTopOrderSentence : M ⊨ Language.order.noTopOrderSentence := by
  apply realize_sentence_of_mem Language.order.dlo
  unfold dlo linearOrderTheory
  right; left; rfl

end

section

variable {M : Type w} [instStructure : Language.order.Structure M]
variable [instModel : M ⊨ Language.order.dlo]

instance instPreorder : Preorder M where
  le := (@instLE M instStructure).le
  le_refl := by
    have := DLO.realize_reflexive M
    simp only [Relations.realize_reflexive] at this
    exact this
  le_trans := by
    have := DLO.realize_transitive M
    simp only [Relations.realize_transitive] at this
    exact this

@[simp]
lemma toLE_of_Preorder
    : (@instPreorder M instStructure instModel).toLE = @instLE M instStructure := rfl

noncomputable instance instLinearOrder : LinearOrder M where
  toPreorder := @instPreorder M instStructure instModel
  le_antisymm := by
    have := DLO.realize_antisymmetric M
    simp only [Relations.realize_antisymmetric] at this
    exact this
  le_total := by
    have := DLO.realize_total M
    simp only [Relations.realize_total] at this
    exact this
  decidableLE := by apply Classical.decRel

@[simp]
lemma toLE_of_LinearOrder
    : (@instLinearOrder M instStructure instModel).toLE = @instLE M instStructure := rfl

instance : @NoMinOrder M instLinearOrder.toLT where
  exists_lt := by
    have := DLO.realize_noBotOrderSentence M
    simp only [noBotOrderSentence] at this
    intro a
    replace this := this a
    simp at this
    rcases this with ⟨b, h⟩
    use b
    exact h

instance : @NoMaxOrder M instLinearOrder.toLT where
  exists_gt := by
    have := DLO.realize_noTopOrderSentence M
    simp only [noTopOrderSentence] at this
    intro a
    replace this := this a
    simp at this
    rcases this with ⟨b, h⟩
    use b
    exact h

instance : DenselyOrdered M where
  dense := by
    have := DLO.realize_denselyOrderedSentence M
    simp only [denselyOrderedSentence] at this
    intro a₁ a₂ h
    replace this := this a₁ a₂
    simp only [BoundedFormula.realize_imp, Term.realize_lt, Term.realize_var,
               BoundedFormula.realize_ex, BoundedFormula.realize_inf] at this
    replace this := this h
    rcases this with ⟨a, h₁, h₂⟩
    use a
    exact ⟨h₁, h₂⟩

end

theorem aleph0_categorical_of_dlo : aleph0.Categorical Language.order.dlo := by
  unfold Categorical
  rintro ⟨M⟩ ⟨N⟩ hM hN
  simp only at *
  apply Nonempty.map toLIso
  have : Countable M := by apply mk_le_aleph0_iff.mp; rw [hM]
  have : Countable N := by apply mk_le_aleph0_iff.mp; rw [hN]
  apply iso_of_countable_dense

end DLO --end

end FirstOrder.Language.Order --end

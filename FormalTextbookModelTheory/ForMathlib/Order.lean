import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Satisfiability
import Mathlib.ModelTheory.Order
import Mathlib.Order.CountableDenseLinearOrder
import Mathlib.Order.Basic
import FormalTextbookModelTheory.ForMathlib.Matrix
import FormalTextbookModelTheory.ForMathlib.Language

universe u v w

open Cardinal
open Matrix
open FirstOrder Language Theory Order Structure

namespace FirstOrder.Language.Order --{{{

section Language.order

scoped notation "L≤" => Language.order

instance instIsRelational₂: IsRelational₂ L≤ where
  empty_functions := Language.instIsRelational.empty_functions
  only_rel₂ := by
    intro n hn
    simp only [Language.order, Language.mk₂, Sequence₂]
    match n with
    | 0 => exact instIsEmptyPEmpty
    | 1 => exact instIsEmptyEmpty
    | 2 => contradiction
    | _ + 3 => exact instIsEmptyPEmpty

end Language.order

section LE

#check (@orderStructure)

#check (@orderLHom)

#check (@OrderedStructure)
/-
tabiki L≤.Structure yapisi orderStructure ile LE M den infer ediliyor.
orderLHom : L≤ →ᴸ L homomorphismasinin expansion oldugunu soyluyor.
-/

#check (@orderedStructure_LE)
/-
bu baya trivial bir sey. orderLHom : L≤ →ᴸ L≤ zaten identity. bunun bir expansion oldugunu soyluyor.
-/

def inst_LE_of_IsOrdered
    (L : Language.{u, v}) [IsOrdered L] {M : Type w} [L.Structure M] : LE M where
  le := fun x y => (@RelMap L M _ 2 leSymb) ![x, y]

#check (@inst_LE_of_IsOrdered)
/-
burada da ordered bir languageden LE M turetiyoruz.
-/

@[simp]
lemma orderStructure_of_LE_of_structure {M : Type w} [inst : L≤.Structure M]
    : @orderStructure M (inst_LE_of_IsOrdered L≤) = inst := by
  ext r₂ m
  simp only [orderStructure, inst_LE_of_IsOrdered]
  rw [Vector_eq_VecNotation₂ m, relMap_apply₂]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd]
  rw [←eq_iff_iff]
  apply congrArg (fun s => RelMap s _)
  apply Subsingleton.allEq
/-
bu aslinda onemli. L≤.Structure M --(inst_LE_of_IsOrdered)--> LE M --(orderStructure)--> L≤.Structure M isleminin
bizi ayni noktaya getirdigini soyluyor.
-/

end LE

section IsOrdered

variable {L : Language.{u, v}} [instIsOrdered : IsOrdered L]
variable {M : Type w} [instStructure : L.Structure M]

lemma OrderedStructure_of_IsOrdered
    : @OrderedStructure L M instIsOrdered (inst_LE_of_IsOrdered L) instStructure := by
  let inst : L≤.Structure M := by exact @orderStructure M (inst_LE_of_IsOrdered L)
  simp only [OrderedStructure]
  refine {
    map_onFunction := by simp only [IsEmpty.forall_iff, implies_true]
    map_onRelation := ?map_onRelation
  }
  intro n
  match n with
  | 0 | 1 | _ + 3 =>
    simp only [Language.order, mk₂_Relations, Sequence₂, instIsEmptyPEmpty, IsEmpty.forall_iff]
  | 2     =>
    intro _ x
    rw [Vector_eq_VecNotation₂ x]
    simp only [inst_LE_of_IsOrdered, orderStructure_of_LE_of_structure, relMap_apply₂]
    apply congrArg (fun r => @RelMap L M instStructure 2 r ![x 0, x 1])
    rfl

section LinearOrder

lemma linearOrderTheory_subset_dlo : L.linearOrderTheory ⊆ L.dlo := by
  simp only [dlo]
  exact Set.subset_union_left

lemma reflexive_in_linearOrderTheory : leSymb.reflexive ∈ L.linearOrderTheory := by
  simp only [linearOrderTheory, Set.mem_insert_iff, Set.mem_singleton_iff, true_or]

lemma transitive_in_linearOrderTheory : leSymb.transitive ∈ L.linearOrderTheory := by
  simp only [linearOrderTheory, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]

lemma antisymmetric_in_linearOrderTheory : leSymb.antisymmetric ∈ L.linearOrderTheory := by
  simp only [linearOrderTheory, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true, or_true]

lemma total_in_linearOrderTheory : leSymb.total ∈ L.linearOrderTheory := by
  simp only [linearOrderTheory, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true, or_true, or_true]

lemma realize_reflexive_of_model_linearOrderTheory (h : M ⊨ L.linearOrderTheory)
    : M ⊨ (leSymb (L := L)).reflexive := by
  simp only [model_iff] at h
  replace h := h leSymb.reflexive reflexive_in_linearOrderTheory
  exact h

lemma realize_transitive_of_model_linearOrderTheory (h : M ⊨ L.linearOrderTheory)
    : M ⊨ (leSymb (L := L)).transitive := by
  simp only [model_iff] at h
  replace h := h leSymb.transitive transitive_in_linearOrderTheory
  exact h

lemma realize_antisymmetric_of_model_linearOrderTheory (h : M ⊨ L.linearOrderTheory)
    : M ⊨ (leSymb (L := L)).antisymmetric := by
  simp only [model_iff] at h
  replace h := h leSymb.antisymmetric antisymmetric_in_linearOrderTheory
  exact h

lemma realize_total_of_model_linearOrderTheory (h : M ⊨ L.linearOrderTheory)
    : M ⊨ (leSymb (L := L)).total := by
  simp only [model_iff] at h
  replace h := h leSymb.total total_in_linearOrderTheory
  exact h

end LinearOrder

section DLO

section

variable {L : Language.{u, v}} [instIsOrdered : IsOrdered L]

lemma reflexive_in_dlo : leSymb.reflexive ∈ L.dlo :=
  linearOrderTheory_subset_dlo reflexive_in_linearOrderTheory

lemma transitive_in_dlo : leSymb.transitive ∈ L.dlo :=
  linearOrderTheory_subset_dlo transitive_in_linearOrderTheory

lemma antisymmetry_in_dlo : leSymb.antisymmetric ∈ L.dlo :=
  linearOrderTheory_subset_dlo antisymmetric_in_linearOrderTheory

lemma total_in_dlo : leSymb.total ∈ L.dlo :=
  linearOrderTheory_subset_dlo total_in_linearOrderTheory

lemma denselyOrderedSentence_in_dlo : L.denselyOrderedSentence ∈ L.dlo := by
  simp only [dlo, Set.union_insert, Set.union_singleton, Set.mem_insert_iff, true_or, or_true]

end

section

variable {L : Language.{u, v}} [instIsOrdered : IsOrdered L]
variable {M : Type w} [instStructure : L.Structure M]

lemma realize_reflexive_of_model_dlo (h : M ⊨ L.dlo) : M ⊨ (leSymb (L := L)).reflexive := by
  simp only [model_iff] at h
  replace h := h leSymb.reflexive reflexive_in_dlo
  exact h

lemma realize_transitive_of_model_dlo (h : M ⊨ L.dlo) : M ⊨ (leSymb (L := L)).transitive := by
  simp only [model_iff] at h
  replace h := h leSymb.transitive transitive_in_dlo
  exact h

lemma model_linearOrderTheory_of_model_dlo (h : M ⊨ L.dlo) : M ⊨ L.linearOrderTheory := by
  simp [model_iff] at *
  intro φ hφ
  exact h φ (linearOrderTheory_subset_dlo hφ)

lemma realize_denselyOrderedSentence_of_model_dlo (h : M ⊨ L.dlo) : M ⊨ L.denselyOrderedSentence := by
  simp only [model_iff] at h
  replace h := h L.denselyOrderedSentence denselyOrderedSentence_in_dlo
  exact h

end

section

variable (L : Language.{u, v}) [instIsOrdered : IsOrdered L]
variable {M : Type w} [instStructure : L.Structure M] [instModel : M ⊨ L.dlo]

def inst_Preorder_of_dlo : Preorder M where
  le := (inst_LE_of_IsOrdered L).le
  le_refl := by
    have := realize_reflexive_of_model_dlo instModel
    simp only [Relations.realize_reflexive, Reflexive] at this
    exact this
  le_trans := by
    have := realize_transitive_of_model_dlo instModel
    simp only [Relations.realize_transitive, Transitive] at this
    exact this

noncomputable def inst_LinearOrder_of_dlo : LinearOrder M where
  toPreorder := inst_Preorder_of_dlo L
  le_antisymm := by
    have := realize_antisymmetric_of_model_linearOrderTheory
        (model_linearOrderTheory_of_model_dlo instModel)
    simp only [Relations.realize_antisymmetric, Antisymm] at this
    exact this
  le_total := by
    have := realize_total_of_model_linearOrderTheory
        (model_linearOrderTheory_of_model_dlo instModel)
    simp only [Relations.realize_total, Total] at this
    exact this
  decidableLE := Classical.decRel _

def inst_DenselyOrdered_of_dlo : @DenselyOrdered M (inst_Preorder_of_dlo L).toLT := by

  have : M ⊨ L.denselyOrderedSentence := realize_denselyOrderedSentence_of_model_dlo instModel

  simp only [Sentence.Realize, denselyOrderedSentence, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_ex, BoundedFormula.realize_inf] at this

  let _ : LT M := (inst_Preorder_of_dlo L).toLT
  refine {
    dense := ?dense
  }

  intro a b h
  replace this := this a b
  simp only [
    @Term.realize_lt L _ M 2 instIsOrdered instStructure (inst_Preorder_of_dlo L) OrderedStructure_of_IsOrdered] at this
  replace this := this h
  rcases this with ⟨a₂, ⟨h₁, h₂⟩⟩
  use a₂
  simp only [
    @Term.realize_lt L _ M 3 instIsOrdered instStructure (inst_Preorder_of_dlo L) OrderedStructure_of_IsOrdered,
    Function.comp_apply] at h₁ h₂
  exact ⟨h₁, h₂⟩

end

end DLO

end IsOrdered

end FirstOrder.Language.Order --}}}

namespace FirstOrder

namespace Language

/-
section

variable {L : Language.{u, v}} [IsOrdered L] {M : Type w} [L.Structure M]

theorem realize_sentence_of_mem_of_model_theory
    {T : Theory L} (h : M ⊨ T) {p : L.Sentence} (hp : p ∈ T) : M ⊨ p := by
  simp only [model_iff] at h
  exact h p hp

theorem model_theory_of_subset_of_model_theory {T T' : Theory L} (h : T' ⊆ T) (hT : M ⊨ T) :
    M ⊨ T' := by
  simp only [model_iff] at *
  intro φ hφ
  exact hT φ (h hφ)

theorem realize_reflexive_of_model_linearOrderTheory (h :  M ⊨ L.linearOrderTheory) :
    M ⊨ (leSymb (L := L)).reflexive :=
  realize_sentence_of_mem_of_model_theory h reflexive_in_linearOrderTheory

end
-/

/-
section -- {{{

variable {M : Type w} [inst₁ : L≤.Structure M]

theorem realize_reflexive_iff : M ⊨ (leSymb (L := L≤)).reflexive ↔ ∀ a : M, a ≤ a := by
  simp only [Relations.realize_reflexive, Reflexive]
  constructor <;> {intro; assumption}

theorem realize_transitive_iff
    : M ⊨ (leSymb (L := L≤)).transitive ↔ ∀ (a b c : M), a ≤ b → b ≤ c → a ≤ c := by
  simp only [Relations.realize_transitive, Transitive]
  constructor <;> {intro; assumption}

instance [inst : M ⊨ L≤.dlo] : Preorder M where
  le := (· ≤ ·)
  le_refl := by
    apply realize_reflexive_iff.1
    apply realize_sentence_of_mem_of_model_theory inst
    apply reflexive_in_dlo
  le_trans := by
    apply realize_transitive_iff.1
    apply realize_sentence_of_mem_of_model_theory inst
    apply transitive_in_dlo

instance [inst : M ⊨ L≤.dlo] : DenselyOrdered M := by
  apply realize_denselyOrdered_iff.mp
  #check @realize_sentence_of_mem L≤ M inst₁ L≤.dlo inst L≤.denselyOrderedSentence
  apply @realize_sentence_of_mem L≤ M inst₁ L≤.dlo inst L≤.denselyOrderedSentence
  sorry

#check realize_denselyOrdered_iff
#check realize_sentence_of_mem

end -- }}}
-/

end Language

end FirstOrder

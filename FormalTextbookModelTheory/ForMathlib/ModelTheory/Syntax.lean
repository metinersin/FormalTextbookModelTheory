import Mathlib.ModelTheory.Syntax

namespace FirstOrder.Language.BoundedFormula

universe u v w
variable {L : Language.{u, v}}
variable {α : Type w} {n : ℕ}

section lInf

open List

def lInf (l : List (L.BoundedFormula α n)) := l.foldr (· ⊓ ·) ⊤

def lInf_nil : lInf [] = (⊤ : L.BoundedFormula α n) := by rfl

def lInf_singleton (φ : L.BoundedFormula α n) : lInf [φ] = φ ⊓ ⊤ := by rfl

def lInf_cons_cons (φ ψ : L.BoundedFormula α n) (l : List (L.BoundedFormula α n)) :
    lInf (φ :: ψ :: l) = φ ⊓ lInf (ψ :: l) := by rfl

end lInf

section lSup

open List

def lSup (l : List (L.BoundedFormula α n)) := l.foldr (· ⊔ ·) ⊥

def lSup_nil : lSup [] = (⊥ : L.BoundedFormula α n) := by rfl

def lSup_singleton (φ : L.BoundedFormula α n) : lSup [φ] = φ ⊔ ⊥ := by rfl

def lSup_cons_cons (φ ψ : L.BoundedFormula α n) (l : List (L.BoundedFormula α n)) :
    lSup (φ :: ψ :: l) = φ ⊔ lSup (ψ :: l) := by rfl

end lSup

section iInf

open Finset List

variable {ι : Type*} (f : ι → L.BoundedFormula α n)

theorem iInf_empty : iInf ∅ f = ⊤ := by rw [iInf, toList_empty, map_nil, foldr_nil]

theorem iInf_singleton (i : ι) : iInf {i} f = f i ⊓ ⊤ := by
  rw [BoundedFormula.iInf, toList_singleton, List.map_singleton, foldr_cons, foldr_nil]

end iInf

section iSup

open Finset List

variable {ι : Type*} (f : ι → L.BoundedFormula α n)

theorem iSup_empty : iSup ∅ f = ⊥ := by rw [iSup, toList_empty, map_nil, foldr_nil]

theorem iSup_singleton (i : ι) : iSup {i} f = f i ⊔ ⊥ := by
  rw [BoundedFormula.iSup, toList_singleton, List.map_singleton, foldr_cons, foldr_nil]

end iSup

-- noncomputable instance : InfSet (L.BoundedFormula α n) where
--   sInf := by
--     intro s
--     by_cases hs : s.Finite
--     · exact iInf hs.toFinset id
--     · exact ⊥

-- noncomputable instance : SupSet (L.BoundedFormula α n) where
--   sSup := by
--     intro s
--     by_cases hs : s.Finite
--     · exact iSup hs.toFinset id
--     · exact ⊥

-- variable {ι : Type*} (s : Set ι) (f : ι → L.BoundedFormula α n)

-- lemma iInf_finite (hs : s.Finite) : ⨅ i ∈ s, f i = iInf hs.toFinset f := by
--   unfold _root_.iInf sInf instInfSet_formalTextbookModelTheory
--   dsimp


--   sorry

-- lemma sInf_empty (f : ι → L.BoundedFormula α n) : ⨅ i ∈ (∅ : Set ι), f i = ⊤ := by
--   unfold _root_.iInf
--   sorry

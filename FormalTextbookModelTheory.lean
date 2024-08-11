import FormalTextbookModelTheory.ForMathlib2.Matrix
import FormalTextbookModelTheory.ForMathlib2.Cardinal
import FormalTextbookModelTheory.ForMathlib2.DLO

---region automatically create leanblueprint

import Lean.Elab.Print
import Mathlib.Lean.Expr.Basic
import Batteries.Tactic.PrintDependents

set_option linter.hashCommand false

open Lean Elab Command

abbrev excludedRootNames : NameSet := NameSet.empty
  |>.insert `Init
  |>.insert `Lean
  |>.insert `Qq
  |>.insert `ImportGraph
  |>.insert `ProofWidgets
  |>.insert `Std
  |>.insert `Aesop
  |>.insert `Batteries
  |>.insert `Mathlib

def userDefinedModules (env : Environment) : Array Name := by
  let allowedImports := env.allImportedModuleNames.filter (!excludedRootNames.contains ·.getRoot)
  exact allowedImports.qsort Name.lt

def test_userDefinedModules : CommandElabM Unit := do
  let env ← getEnv
  let modules := userDefinedModules env
  logInfo modules.toList.toString

def moduleNameToFileName (moduleName : Name) : System.FilePath :=
  System.FilePath.addExtension (System.mkFilePath $ moduleName.toString.splitOn ".") "lean"

def test_moduleNameToFileName : CommandElabM Unit := do
  let env ← getEnv
  let modules := userDefinedModules env
  let mut fnames := #[]
  for module in modules do
    fnames := fnames.push (moduleNameToFileName module)
  logInfo fnames.toList.toString

def userDefinedDecls (env : Environment) : Array Name := Id.run do
  let mut modIdx : HashSet Nat := .empty
  let mut modsSeen : NameSet := .empty
  let allowedImports := userDefinedModules env
  for imp in allowedImports do
    if let some nm := env.getModuleIdx? imp then
      modIdx := modIdx.insert nm
      modsSeen := modsSeen.insert imp
 --
  let consts := env.constants
  let newDeclNames := consts.fold (init := ({} : NameSet)) fun a b _c =>
    match env.getModuleIdxFor? b with
      | none => a
      | some idx => if modIdx.contains idx then a.insert b else a
  --
  let mut newDeclNamesFiltered := #[]
  for decl in newDeclNames do
    if decl.isAnonymous then
      continue
    if decl.isNum then
      continue
    if decl.isAuxLemma then
      continue
    if decl.isInternal then
      continue
    if decl.isInternalDetail then
      continue
    if decl.isImplementationDetail then
      continue
    if decl.isInaccessibleUserName then
      continue
    newDeclNamesFiltered := newDeclNamesFiltered.push decl
  return newDeclNamesFiltered.qsort Name.lt


def test_userDefinedDecls : CommandElabM Unit := do
  let env ← getEnv
  let decls := userDefinedDecls env
  logInfo decls.size.repr
  logInfo decls.toList.toString

def getDocstring (env : Environment) (decl : Name) : IO $ Option String := do
  return ← findDocString? env decl

def test_getDocstring : CoreM Unit := do
  let env ← getEnv
  let doc ← getDocstring env `FirstOrder.Language.Order.DLO.aleph0_categorical_of_dlo
  IO.println doc


/-- extracts the names of the declarations in `env` on which `decl` depends. -/
-- source:
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Counting.20prerequisites.20of.20a.20theorem/near/425370265
def getVisited (env : Environment) (decl : Name) : NameSet :=
  let (_, { visited, .. }) := Elab.Command.CollectAxioms.collect decl |>.run env |>.run {}
  visited

def getDependencies (decl : Name) : CommandElabM (Array Name) := do
  let env ← getEnv
  let visited := (getVisited env decl).toArray
  let decls := userDefinedDecls env
  let visited := visited.filter $ fun name => name ∈ decls ∧ name ≠ decl
  return visited

#eval test_userDefinedModules
#eval test_moduleNameToFileName
#eval test_userDefinedDecls
#eval test_getDocstring
#eval (getDependencies `FirstOrder.Language.Order.orderStructure_of_LE)

--end

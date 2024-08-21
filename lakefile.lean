import Lake
open Lake DSL

package "FormalTextbookModelTheory" where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require "leanprover-community" / "mathlib"

@[default_target]
lean_lib «FormalTextbookModelTheory» where

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"

-- require AutoBlueprint from git
--   "https://github.com/metinersin/AutoBlueprint" @ "development"

require AutoBlueprint from "/home/metinersin/projects/AutoBlueprint"

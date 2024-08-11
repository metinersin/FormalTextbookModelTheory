-- import Mathlib.ModelTheory.Basic
import Mathlib.Tactic.Linarith

section

def ite_lt [LT α] {x y : α} {flag : Prop} [Decidable flag] {z : α} (h₁ : x < z) (h₂ : y < z)
    : (if flag then x else y) < z := by
  by_cases hf : flag <;> {simp only [hf]; assumption}

private def parse_line? (line : String) (field : String) : Option String :=
  let line := line.trim
  if line.startsWith ("\\" ++ field ++ "{") && line.endsWith "}" then
    let value := String.mk line.data.toArray[field.length + 2:line.length - 1].toArray.toList
    if value.length > 0 then some value else none
  else none

private def parse_first_line? (line : String) : Option String :=
  parse_line? line "begin"

private def parse_last_line? (line : String) : Option String :=
  parse_line? line "end"

private def parse_label? (line : String) : Option String :=
  parse_line? line "label"

private def parse_name? (line : String) : Option String :=
  parse_line? line "lean"

private def parse_uses? (line : String) : Option (List String) :=
  let content := parse_line? line "uses"
  match content with
  | none => none
  | some content =>
    let lst := List.map String.trim (content.splitOn ",")
    some lst

private def parse_content (lines : List String) : String :=
  String.intercalate "\n" (lines.filter (fun line => ¬ line.startsWith "\\"))

private def split_environments? (s : String) : Option (String × String) :=
  let lines := List.map String.trim (s.splitOn "\n")
  let begins := List.findIdxs (fun line => not (parse_first_line? line).isNone) lines
  let ends := List.findIdxs (fun line => not (parse_last_line? line).isNone) lines
  match hb : begins.length, he : ends.length with
  | 2, 2 =>
    let begin₁ := begins[0]
    let end₁ := ends[0]
    let begin₂ := begins[1]
    let end₂ := ends[1]
    some ⟨String.intercalate "\n" (lines.toArray[begin₁:end₁ + 1].toArray.toList),
          String.intercalate "\n" (lines.toArray[begin₂:end₂ + 1].toArray.toList)⟩
  | _, _ => none


end

structure EnvironmentWithoutProof where
  type : String
  leanok : Bool
  uses : List String
  content : String

namespace EnvironmentWithoutProof --region

instance : ToString EnvironmentWithoutProof where
  toString env :=
    "\\begin{" ++ env.type ++ "}\n" ++
    (if env.leanok then "\\leanok\n" else "") ++
    "\\uses{" ++ (String.intercalate ", " env.uses) ++ "}\n" ++
    env.content ++ "\n" ++
    "\\end{" ++ env.type ++ "}\n"

def parse? (s : String) : Option EnvironmentWithoutProof :=
  let lines := List.map String.trim (s.splitOn "\n")
  let len := lines.length
  match h : len with
  | 0 | 1 | 2 => none
  | n + 3 =>
    let type_first? := parse_first_line? lines[0]
    let type_last? := parse_last_line? lines[len - 1]
    match type_first?, type_last? with
    | _, none | none, _ => none
    | some type, some type' =>
      if type ≠ type' then none else
        let leanok := lines[1] == "\\leanok"
        let uses_idx := if leanok then 2 else 1
        let uses? := parse_uses? (lines[uses_idx]'(by apply ite_lt <;> linarith))
        match uses? with
        | none => none
        | some uses =>
          let content := parse_content lines
          some {type := type, leanok := leanok, uses := uses, content := content}

end EnvironmentWithoutProof --end

structure ProofEnvironment where
  leanok : Bool
  uses : List String
  content : String

def EnvironmentWithoutProof.toProofEnvironment {env : EnvironmentWithoutProof} (_ : env.type = "proof")
    : ProofEnvironment :=
  {leanok := env.leanok, uses := env.uses, content := env.content}

namespace ProofEnvironment --region

def toEnvironmentWithoutProof (env : ProofEnvironment) : EnvironmentWithoutProof :=
  {env with type := "proof"}

instance : Coe ProofEnvironment EnvironmentWithoutProof where
  coe env := env.toEnvironmentWithoutProof

instance : ToString ProofEnvironment where
  toString env := toString (env : EnvironmentWithoutProof)

def parse? (s : String) : Option ProofEnvironment :=
  let env? := EnvironmentWithoutProof.parse? s
  match env? with
  | none => none
  | some env =>
  if h : env.type ≠ "proof" then none else
  some $ env.toProofEnvironment (by push_neg at h; exact h)

end ProofEnvironment --end

structure EnvironmentWithProof where
  type : String
  label : String
  name : String
  leanok : Bool
  uses : List String
  content : String
  proof : ProofEnvironment

namespace EnvironmentWithProof --region

instance : ToString EnvironmentWithProof where
  toString env :=
    "\\begin{" ++ env.type ++ "}\n" ++
    "\\label{" ++ env.label ++ "}\n" ++
    "\\lean{" ++ env.name ++ "}\n" ++
    (if env.leanok then "\\leanok\n" else "") ++
    "\\uses{" ++ (String.intercalate ", " env.uses) ++ "}\n" ++
    env.content ++ "\n" ++
    "\\end{" ++ env.type ++ "}\n" ++
    toString env.proof

def parse? (s : String) : Option EnvironmentWithProof :=
  let s? := split_environments? s
  match s? with
  | none => none
  | some (s₁, s₂) =>
  let lines := List.map String.trim (s₁.splitOn "\n")
  let len := lines.length
  match h : len with
  | 0 | 1 | 2 | 3 | 4 => none
  | n + 5 =>
  let type_first? := parse_first_line? lines[0]
  let type_last? := parse_last_line? lines[len - 1]
  match type_first?, type_last? with
  | _, none | none, _ => none
  | some type, some type' =>
  if type ≠ type' then none else
    let label? := parse_label? lines[1]
    match label? with
    | none => none
    | some label =>
    let name? := parse_name? lines[2]
    match name? with
    | none => none
    | some name =>
    let leanok := lines[3] == "\\leanok"
    let uses_idx := if leanok then 4 else 3
    let uses? := parse_uses? (lines[uses_idx]'(by apply ite_lt <;> linarith))
    match uses? with
    | none => none
    | some uses =>
    let content := parse_content lines
    let proof? := ProofEnvironment.parse? s₂
    match proof? with
    | none => none
    | some proof =>
    some {type := type, label := label, name := name, leanok := leanok,
          uses := uses, content := content, proof := proof}

end EnvironmentWithProof --end

structure TheoremEnvironment where
  label : String
  name : String
  leanok : Bool
  uses : List String
  content : String
  proof : ProofEnvironment

def EnvironmentWithProof.toTheoremEnvironment {env : EnvironmentWithProof} (_ : env.type = "theorem")
    : TheoremEnvironment :=
  {label := env.label, name := env.name, leanok := env.leanok,
   uses := env.uses, content := env.content, proof := env.proof}

namespace TheoremEnvironment --region

def toEnvironmentWithProof (env : TheoremEnvironment) : EnvironmentWithProof :=
  {env with type := "theorem"}

instance : Coe TheoremEnvironment EnvironmentWithProof where
  coe := toEnvironmentWithProof

instance : ToString TheoremEnvironment where
  toString env := toString (env : EnvironmentWithProof)

def parse? (s : String) : Option TheoremEnvironment :=
  let env? := EnvironmentWithProof.parse? s
  match env? with
  | none => none
  | some env =>
  if h : env.type ≠ "theorem" then none else
  some $ env.toTheoremEnvironment (by push_neg at h; exact h)

end TheoremEnvironment --end

structure LemmaEnvironment where
  label : String
  name : String
  leanok : Bool
  uses : List String
  content : String
  proof : ProofEnvironment

def EnvironmentWithProof.toLemmaEnvironment {env : EnvironmentWithProof} (_ : env.type = "lemma")
    : LemmaEnvironment :=
  {label := env.label, name := env.name, leanok := env.leanok,
    uses := env.uses, content := env.content, proof := env.proof}

namespace LemmaEnvironment --region

def toEnvironmentWithProof (env : LemmaEnvironment) : EnvironmentWithProof :=
  {env with type := "theorem"}

instance : Coe LemmaEnvironment EnvironmentWithProof where
  coe env := env.toEnvironmentWithProof

instance : ToString LemmaEnvironment where
  toString env := toString (env : EnvironmentWithProof)

def parse? (s : String) : Option LemmaEnvironment :=
  let env? := EnvironmentWithProof.parse? s
  match env? with
  | none => none
  | some env =>
  if h : env.type ≠ "lemma" then none else
  some $ env.toLemmaEnvironment (by push_neg at h; exact h)

end LemmaEnvironment --end

namespace BlueprintLatex.Test --region

def env₁ : ProofEnvironment where
  leanok := false
  uses := ["thm:merhaba"]
  content := "This is a proof."

def env₂ : TheoremEnvironment where
  label := "thm:current_theorem"
  name := "FirstOrder.Language.mytheorem"
  leanok := true
  uses := ["thm:old-theorem", "lem:old-lemma", "def:old-definition"]
  content := "This is a very important theorem."
  proof := env₁

#eval env₁
#eval env₂

open EnvironmentWithoutProof

def test_parse_line? : IO Unit := do
  let line := "\\begin{merhaba}"
  IO.println (parse_line? line "begin")

def test_parse₁? : IO Unit := do
  let stream ← IO.FS.Handle.mk "proof.tex" IO.FS.Mode.read
  let s ← stream.readToEnd
  let env? := parse? s
  match env? with
  | none => IO.println "No environment found"
  | some env =>
    IO.println $ "type: " ++ env.type
    IO.println $ "leanok: " ++ reprStr env.leanok
    IO.println $ "uses: " ++ env.uses.toString
    IO.println $ "content: " ++ env.content

def test_splitEnvironment? : IO Unit := do
  let stream ← IO.FS.Handle.mk "theorem.tex" IO.FS.Mode.read
  let s ← stream.readToEnd
  let envs? := split_environments? s
  match envs? with
  | none => IO.println "No environments found"
  | some (env₁, env₂) => do
    IO.println env₁
    IO.println env₂

def test_parse?_theorem : IO Unit := do
  let stream ← IO.FS.Handle.mk "theorem.tex" IO.FS.Mode.read
  let s ← stream.readToEnd
  let env? := TheoremEnvironment.parse? s
  match env? with
  | none => IO.println "No theorem found"
  | some env => IO.println env

#eval test_parse_line?
#eval test_parse₁?
#eval test_splitEnvironment?
#eval test_parse?_theorem

end BlueprintLatex.Test --end

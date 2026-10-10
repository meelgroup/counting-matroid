import Lean
open Lean Elab Command Meta
namespace Tex2Lean.RecoveryRequestsV1

structure Dependency where
  name : Name
  canonicalType : String
  typeSource : String
  levelParams : List Name
  deriving Inhabited
structure Obligation where
  key : String
  presentation : String
  expression : Expr
  levelParams : List Name
  dependencies : Array Dependency
  deriving Inhabited
structure Request where
  id : String
  goal : Name
  target : Name
  reason : String
  module : Name
  line : Nat
  column : Nat
  obligations : Array Obligation
  deriving Inhabited

initialize requests : SimplePersistentEnvExtension Request (Array Request) ←
  registerSimplePersistentEnvExtension {
    name := `Tex2Lean.RecoveryRequestsV1.requests
    addEntryFn := Array.push
    addImportedFn := fun entries => entries.foldl (fun acc next => acc ++ next) #[]
  }


partial def canonicalExpr : Expr → Expr
  | .const n ls => .const (privateToUserName n) ls
  | .app f a => .app (canonicalExpr f) (canonicalExpr a)
  | .lam _ t b bi => .lam Name.anonymous (canonicalExpr t) (canonicalExpr b) bi
  | .forallE _ t b bi => .forallE Name.anonymous (canonicalExpr t) (canonicalExpr b) bi
  | .letE _ t v b nondep => .letE Name.anonymous (canonicalExpr t) (canonicalExpr v) (canonicalExpr b) nondep
  | .mdata _ e => canonicalExpr e
  | .proj n i e => .proj (privateToUserName n) i (canonicalExpr e)
  | e => e

def canonical (info : ConstantInfo) (e : Expr) : String :=
  let levels := info.levelParams.zipIdx |>.map fun (_, i) =>
    Level.param (Name.num (Name.str Name.anonymous "tex2leanUniverse") i)
  reprStr (canonicalExpr (e.instantiateLevelParams info.levelParams levels))


def namesJson (names : List Name) : Json :=
  toJson (names.map toString)
def obligationJson (o : Obligation) : Json := Json.mkObj [
  ("key", toJson o.key), ("presentation", toJson o.presentation),
  ("exprSource", toJson (reprStr o.expression)), ("levelParams", namesJson o.levelParams),
  ("dependencies", Json.arr (o.dependencies.map fun d => Json.mkObj [
    ("name", toJson (toString d.name)), ("canonicalType", toJson d.canonicalType), ("typeSource", toJson d.typeSource),
    ("levelParams", namesJson d.levelParams)]))]
def requestJson (r : Request) : Json := Json.mkObj [
  ("schema", toJson "tex2lean.model-request/1"), ("id", toJson r.id),
  ("goal", toJson (toString (privateToUserName r.goal))), ("target", toJson (toString (privateToUserName r.target))),
  ("reason", toJson r.reason), ("module", toJson (toString r.module)),
  ("line", toJson r.line), ("column", toJson r.column),
  ("obligations", Json.arr (r.obligations.map obligationJson))]
def exportJson (env : Environment) : Json :=
  Json.arr ((requests.getState env).map requestJson)
def exportJsonForModules (env : Environment) (modules : Array Name) : Json :=
  Json.arr (((requests.getState env).filter fun r => modules.contains r.module).map requestJson)

syntax recoveryObligation := ident " : " term
-- Positional fields avoid reserving common declaration names such as goal/target/reason.
syntax (name := modelRequest) "#model_request " ident " => " ident str "[" recoveryObligation,+ "]" : command

@[command_elab modelRequest] def elaborateRequest : CommandElab := fun stx => do
  let goalSyntax := stx[1]
  let targetSyntax := stx[3]
  let reasonSyntax := stx[4]
  let items := stx[6].getSepArgs
  if reasonSyntax.isStrLit?.getD "" |>.trimAscii |>.isEmpty then
    throwError "a Model request needs a nonempty explanation"
  let goalName ← resolveGlobalConstNoOverload goalSyntax
  let targetName ← resolveGlobalConstNoOverload targetSyntax
  let env ← getEnv
  let some targetInfo := env.find? targetName | throwError "unknown Model target"
  unless targetInfo matches .defnInfo _ | .opaqueInfo _ do
    throwError "Model target must be a definition"
  let mut obligations := #[]
  let mut keys : Array String := #[]
  for item in items do
    let key := item[0]
    let term := item[2]
    let keyText := key.getId.toString
    if keys.contains keyText then throwError "duplicate preservation obligation key: {keyText}"
    keys := keys.push keyText
    let obligation ← liftTermElabM do
      let expression ← Term.elabTermEnsuringType term (mkSort .zero)
      Term.synthesizeSyntheticMVarsNoPostponing
      let expression ← instantiateMVars expression
      if expression.hasFVar || expression.hasMVar || expression.hasLevelMVar || expression.hasLooseBVars then
        throwError "preservation obligations must be closed, fully quantified propositions without unresolved metavariables"
      let constants := expression.getUsedConstants.toList
      if constants.contains `sorryAx then throwError "preservation obligations may not contain sorry"
      let mut dependencies := #[]
      let mut pending := constants
      let mut seen : NameSet := {}
      while !pending.isEmpty do
        let name := pending.head!
        pending := pending.tail!
        if seen.contains name then continue
        seen := seen.insert name
        let some info := (← getEnv).find? name | throwError "unknown obligation dependency: {name}"
        dependencies := dependencies.push { name, canonicalType := canonical info info.type, typeSource := reprStr info.type, levelParams := info.levelParams }
        -- Type dependencies are frozen transitively; implementation bodies intentionally are not.
        pending := pending ++ info.type.getUsedConstants.toList
      let mut levels : List Name := []
      for level in (collectLevelParams {} expression).params do
        unless levels.contains level do levels := levels ++ [level]
      let presentationText := (← ppExpr expression).pretty
      return ({ key := keyText, presentation := presentationText, expression := expression, levelParams := levels, dependencies := dependencies } : Obligation)
    obligations := obligations.push obligation
  unless obligations.any (fun o => o.dependencies.any (fun d => d.name == targetName)) do
    throwError "at least one preservation obligation must refer to the requested Model definition"
  let fileMap ← getFileMap
  let position := fileMap.toPosition (stx.getPos?.getD 0)
  let moduleName := env.mainModule
  let id := s!"{moduleName}:{position.line}:{position.column}:{goalName}:{targetName}"
  let request : Request := { id, «goal» := goalName, «target» := targetName, «reason» := reasonSyntax.isStrLit?.getD "", module := moduleName, line := position.line, column := position.column, obligations }
  modifyEnv fun env => requests.addEntry env request
end Tex2Lean.RecoveryRequestsV1

import Lean
import Lean.Data.Json.FromToJson
import Lean.Message

open Lean Elab Term Meta Std

inductive TheoremTypeEquivalenceMode where
  | alpha
  | defeq

structure TheoremTypeCluster where
  representativeName : String
  statement : String
  theoremNames : List String

structure ClusterState where
  representativeName : Name
  representativeType : Expr
  statement : String
  theoremNames : Array Name

def writeJsonToFile (filePath : String) (json : Json) : IO Unit := do
  let jsonString := toString json
  IO.FS.withFile filePath IO.FS.Mode.write fun handle => do
    handle.putStr jsonString

def theoremTypeExpr (declName : Name) : TermElabM Expr := do
  let constInfo ← getConstInfo declName
  pure constInfo.toConstantVal.type

def theoremTypeString (declName : Name) : TermElabM String := do
  let typeExpr ← theoremTypeExpr declName
  let rendered ← ppExpr typeExpr
  pure s!"{rendered}"

def theoremTypesEquivalent (mode : TheoremTypeEquivalenceMode) (lhs rhs : Expr) : TermElabM Bool := do
  match mode with
  | .alpha => pure (lhs.eqv rhs)
  | .defeq => withoutModifyingState do
      isDefEq lhs rhs

def insertIntoClusters
    (mode : TheoremTypeEquivalenceMode)
    (clusters : Array ClusterState)
    (declName : Name) :
    TermElabM (Array ClusterState) := do
  let typeExpr ← theoremTypeExpr declName
  let statement ← theoremTypeString declName
  let mut i := 0
  while h : i < clusters.size do
    let cluster : ClusterState := clusters[i]
    if ← theoremTypesEquivalent mode (ClusterState.representativeType cluster) typeExpr then
      let updated : ClusterState := {
        representativeName := ClusterState.representativeName cluster
        representativeType := ClusterState.representativeType cluster
        statement := ClusterState.statement cluster
        theoremNames := (ClusterState.theoremNames cluster).push declName
      }
      return clusters.set i updated
    i := i + 1
  pure <|
    clusters.push {
      representativeName := declName
      representativeType := typeExpr
      statement := statement
      theoremNames := #[declName]
    }

def buildTheoremTypeClustersWithMode
    (mode : TheoremTypeEquivalenceMode)
    (declNames : List Name) :
    TermElabM (Array ClusterState) := do
  let mut clusters : Array ClusterState := #[]
  for declName in declNames do
    clusters ← insertIntoClusters mode clusters declName
  pure clusters

def buildTheoremTypeClusters (declNames : List Name) : TermElabM (Array ClusterState) := do
  buildTheoremTypeClustersWithMode .alpha declNames

def duplicateTheoremTypeClustersWithMode
    (mode : TheoremTypeEquivalenceMode)
    (declNames : List Name) :
    TermElabM (List TheoremTypeCluster) := do
  let clusters ← buildTheoremTypeClustersWithMode mode declNames
  let mut duplicates : List TheoremTypeCluster := []
  for cluster in clusters do
    if cluster.theoremNames.size < 2 then
      continue
    duplicates := {
      representativeName := toString cluster.representativeName
      statement := cluster.statement
      theoremNames := cluster.theoremNames.toList.map toString
    } :: duplicates
  pure duplicates.reverse

def duplicateTheoremTypeClusters (declNames : List Name) : TermElabM (List TheoremTypeCluster) := do
  duplicateTheoremTypeClustersWithMode .alpha declNames

def duplicateTheoremTypeClustersDefEq (declNames : List Name) : TermElabM (List TheoremTypeCluster) := do
  duplicateTheoremTypeClustersWithMode .defeq declNames

def theoremTypeClusterToJson (cluster : TheoremTypeCluster) : Json :=
  Json.mkObj
    [ ("representative_name", Json.str cluster.representativeName)
    , ("statement", Json.str cluster.statement)
    , ("theorem_names", Json.arr <| cluster.theoremNames.map Json.str |> List.toArray)
    ]

def theoremTypeClustersToJson (clusters : List TheoremTypeCluster) : Json :=
  Json.arr <| clusters.map theoremTypeClusterToJson |> List.toArray

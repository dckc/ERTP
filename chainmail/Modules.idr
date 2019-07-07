module Modules

import Pruviloj
import Pruviloj.Derive.DecEq

import Notation

%language ElabReflection

% default total
%access public export

||| we use metavariables as follows: x ∈ VarId, and x includes this
data VarId = VarI String | This

decVarIdEq : (x1, x2 : VarId) -> Dec (x1 = x2)
%runElab (deriveDecEq `{decVarIdEq})
implementation DecEq VarId where
  decEq = decVarIdEq

||| f ∈ FldId 
record FldId where
  constructor FldI
  id: String

decFldIdEq : (f1, f2 : FldId) -> Dec (f1 = f2)
%runElab (deriveDecEq `{decFldIdEq})
implementation DecEq FldId where
  decEq = decFldIdEq

||| m ∈ MethId
record MethId where
  constructor MethI
  id: String

decMethIdEq : (x1, x2 : MethId) -> Dec (x1 = x2)
%runElab (deriveDecEq `{decMethIdEq})
implementation DecEq MethId where
  decEq = decMethIdEq

||| C ∈ ClassId
record ClassId where
  constructor ClassI
  id: String

decClassIdEq : (x1, x2 : ClassId) -> Dec (x1 = x2)
%runElab (deriveDecEq `{decClassIdEq})
implementation DecEq ClassId where
  decEq = decClassIdEq

FieldDecl: Type
FieldDecl = FldId

infix 12 ..
||| (we write `x .. f` for `x.f`)
data FieldAccess = (..) VarId FldId

||| x.m(x*)
data Call = MkCall VarId MethId (List VarId)

||| x.f:= x | x:= x.f | x:= x.m( x* ) | x:= new C ( x∗ ) | return x
data Stmt = SetField FieldAccess VarId
          | GetField VarId FieldAccess
          | GetCall VarId Call
          | GetNew VarId ClassId (List VarId)
          | Return VarId

Stmts : Type
Stmts = List Stmt

MethDecl: Type
MethDecl = (MethId, (List VarId, Stmts))

||| e ::= true | false | null | x | e=e | if e then e else e | e.f( e∗)
data Expr = True | False | Null | Var VarId
  | Eq Expr Expr | If Expr Expr Expr
  | CallExpr Call

GhostDecl: Type
GhostDecl = (FldId, (List VarId, Expr))

||| DEFINITION 16 (CLASSES). Class descriptions consist of field
||| declarations, method declarations, and ghostfield declarations.
data ClassDescr: Type where
  ClassDef: ClassId
            -> (List FieldDecl) -> (List MethDecl) -> (List GhostDecl)
            -> ClassDescr

||| DEFINITION 15 (MODULES). We define Module as the set of mappings
||| from identifiers to class descriptions (the latter defined in
|||
||| Module ≜ { M | M : Identifier −> ClassDescr }
Module: Type
Module = ClassId :==> ClassDescr

test: (List MethDecl) -> (List (MethId, (List VarId, List Stmt)))
test = id

||| DEFINITION 17 (Lookup)
||| M(M, C, m)
bigM: Module -> ClassId -> MethId -> Maybe MethDecl
bigM mod cid mid =
  do
    (ClassDef _ _ methods _) <- mod .@ cid
    mdef <- methods .@ mid
    pure (mid, mdef)

bigG: Module -> ClassId -> FldId -> Maybe GhostDecl
bigG mod cid gid =
  do
    (ClassDef _ _ _ gs) <- mod .@ cid
    gdef <- gs .@ gid
    pure (gid, gdef)



-- Local Variables:
-- idris-load-packages: ("pruviloj")
-- End:

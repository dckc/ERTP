module Chainmail

import Data.Vect

{-
A THE UNDERLYING PROGRAMMING LANGUAGE, Loo

A.1 Modules and Classes

Loo programs consist of modules, which are repositories of code. Since
we study class based oo languages, in this work, code is represented
as classes, and modules are mappings from identifiers to class
descriptions.
-}

mutual

  ||| DEFINITION 15 (MODULES). We define Module as the set of mappings
  ||| from identifiers to class descriptions (the latter defined in
  |||
  ||| Module ≜ { M | M : Identifier −> ClassDescr }
  Module: {nc, nf, nm, ng: Nat} -> Type
  Module {nc} {nf} {nm} {ng} = Vect nc (ClassId, ClassDescr {nf=nf} {nm=nm} {ng=ng})

  ||| DEFINITION 16 (CLASSES). Class descriptions consist of field
  ||| declarations, method declarations, and ghostfield declarations.
  data ClassDescr: {nf, nm, ng: Nat} -> Type where
    ClassDef: ClassId
              -> (Vect nf FieldDecl)
              -> (Vect nm MethDecl)
              -> (Vect ng GhostDecl)
              -> ClassDescr
 
  FieldDecl: Type
  FieldDecl = FldId

  MethDecl: {np, ns: Nat} -> Type
  MethDecl {np} {ns} = (MethId, (Vect np VarId, Stmts {ns=ns}))

  Stmts : {ns: Nat} -> Type
  Stmts {ns} = Vect ns Stmt

  ||| x.f:= x | x:= x.f | x:= x.m( x ) | @@TODO x:= new C ( x∗ ) | return x
  data Stmt: Type where
    FieldAssign: {x: VarId} -> {f:FldId} -> {v: VarId}
      -> Stmt
    AssignGet: {lhs: VarId} -> {x: VarId} -> {f: FldId}
      -> Stmt

  GhostDecl: Type
  GhostDecl = (FldId, (List VarId, Expr))

  data Expr = True | False | Null
    | Var VarId | Eq Expr Expr
    | If Expr Expr Expr
    | Call Expr FldId (List Expr)

  ||| we use metavariables as follows: x ∈ VarId f ∈ FldId m ∈ MethId
  ||| C ∈ ClassId, and x includes this
  data VarId = VarI String | This
  Eq VarId where
   This == This = True
   This == _ = False
   _ == This = False
   (VarI a) == (VarI b) = a == b

  record FldId where
    constructor FldI
    id: String
  record MethId where
    constructor MethI
    id: String
  Eq MethId where
    (MethI a) == (MethI b) = a == b
  record ClassId where
    constructor ClassI
    id: String
  Eq ClassId where
    (ClassI a) == (ClassI b) = a == b

  lc: {nc, nf, nm, ng: Nat} -> (Module {nc=nc} {nf=nf} {nm=nm} {ng=ng}) -> ClassId -> Maybe (ClassDescr {nf=nf} {nm=nm} {ng=ng})
  lc {nc} {nf} {nm} {ng} mod cid = Vect.lookup cid mod

  ||| lookup M(M, C, m)
  bigM: {nc, nf, nm, ng, np, ns: Nat}
        -> (Module {nc=nc} {nf=nf} {nm=nm} {ng=ng})
        -> ClassId
        -> MethId
         -> Maybe (MethDecl {np=np} {ns=ns})
  bigM {nc} {nf} {nm} {ng} {np} {ns} mod cid mid =
   case (Vect.lookup {n=nc} cid mod) of
    (Just (ClassDef {nm=nm} _ _ methods _)) =>
     case (Vect.lookup {n=nm} mid methods) of
      (Just mdef) => Just (mid, mdef)
      Nothing => Nothing
    Nothing => Nothing


{-

DEFINITION 1. Given runtime configurations σ, σ′, and a module-pair
M#M′ we define execution where M is the internal, and M′ is the
external module as below:• M # M′, σ ❀ σ′ if there exist n ≥ 2 and
runtime configurations σ1, ... σn, such that– σ=σ1, and σn = σ′.–
M◦M′, σi ❀ σ′ i+1, for 1 ≤ i ≤ n−1 – Class(this)σ < dom(M), and
Class(this)σ′ < dom(M), – Class(this)σi ∈ dom(M), for 2 ≤ i ≤ n−2

-}


data Configuration = Conf Nat {- @@@ -}

data ModulePair: Type where
  Semi: (M: Module) -> (M': Module) -> ModulePair


infix 7 ~>

{- where the paper uses M;M' , we use M#M' -}
infix 11 #

data ModuleContext: Type where
  (#): Module -> Module -> ModuleContext

data ConfigInContext = (/) ModuleContext Configuration

{- Execution -}
data (~>): ConfigInContext -> Configuration -> Type where
  TwoModuleExecution: (sigma, sigma': Configuration)
           -> (m, m': Module)
           -> (n: Nat)
           -> (sigmas: (Vect (S n) Configuration))
           -> sigma = head sigmas
           -> sigma' = last sigmas
           {- @@@ -> ({i :Fin n} -> Vect.index i sigmas) -}
           -> m # m' / sigma ~> sigma'

-- Local Variables:
-- idris-load-packages: ("contrib")
-- End:

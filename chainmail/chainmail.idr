module Chainmail

import Data.Vect

%default total

{-
A THE UNDERLYING PROGRAMMING LANGUAGE, Loo

A.1 Modules and Classes

Loo programs consist of modules, which are repositories of code. Since
we study class based oo languages, in this work, code is represented
as classes, and modules are mappings from identifiers to class
descriptions.
-}

VecLen: (a: Type) -> Type
VecLen a = (n: Nat ** Vect n a)

VMap: (k: Type) -> (v: Type) -> Type
VMap k v = VecLen (k, v)

vlookup: Eq k => k -> (VMap k v) -> (Maybe v)
vlookup key (n ** pairs) = Vect.lookup {n=n} key pairs

infix 12 .@
(.@): Eq k => (VMap k v) -> k -> (Maybe v)
m .@ k = vlookup k m

infix 11 $?
($?): (Maybe a) -> (a -> Maybe b) -> (Maybe b)
(Just a) $? f = f a
Nothing $? f = Nothing

infix 12 ..

{- where the paper uses M;M' , we use M#M' -}
infix 7 ~>
infix 7 ~~>
infix 11 #

mutual

  ||| DEFINITION 15 (MODULES). We define Module as the set of mappings
  ||| from identifiers to class descriptions (the latter defined in
  |||
  ||| Module ≜ { M | M : Identifier −> ClassDescr }
  Module: Type
  Module = VMap ClassId ClassDescr

  ||| DEFINITION 16 (CLASSES). Class descriptions consist of field
  ||| declarations, method declarations, and ghostfield declarations.
  data ClassDescr: Type where
    ClassDef: ClassId
              -> (VecLen FieldDecl)
              -> (VecLen MethDecl)
              -> (VecLen GhostDecl)
              -> ClassDescr
 
  FieldDecl: Type
  FieldDecl = FldId

  MethDecl: Type
  MethDecl = (MethId, (VecLen VarId, Stmts))

  Stmts : Type
  Stmts = VecLen Stmt

  data FieldAccess = (..) VarId FldId
  data Call = MkCall VarId FldId (VecLen VarId)

  ||| x.f:= x | x:= x.f | x:= x.m( x* ) | x:= new C ( x∗ ) | return x
  data Stmt = SetField FieldAccess VarId
            | GetField VarId FieldAccess
            | GetCall VarId Call
            | GetNew VarId ClassId (VecLen VarId)
            | Return VarId

  GhostDecl: Type
  GhostDecl = (FldId, (VMap VarId Expr))

  ||| e ::= true | false | null | x | e=e | if e then e else e | e.f( e∗)
  data Expr = True | False | Null | Var VarId
    | Eq Expr Expr | If Expr Expr Expr
    | CallExpr Call

  ||| we use metavariables as follows: x ∈ VarId, and x includes this
  data VarId = VarI String | This
  Eq VarId where
   This == This = True
   This == _ = False
   _ == This = False
   (VarI a) == (VarI b) = a == b

  ||| f ∈ FldId 
  record FldId where
    constructor FldI
    id: String
  Eq FldId where
    (FldI a) == (FldI b) = a == b
  ||| m ∈ MethId
  record MethId where
    constructor MethI
    id: String
  Eq MethId where
    (MethI a) == (MethI b) = a == b
  ||| C ∈ ClassId
  record ClassId where
    constructor ClassI
    id: String
  Eq ClassId where
    (ClassI a) == (ClassI b) = a == b

  ||| lookup M(M, C, m)
  bigM: Module -> ClassId -> MethId -> Maybe MethDecl
  bigM mod cid mid = mod .@ cid $?
    \(ClassDef _ _ methods _) =>
      methods .@ mid $?
       \mdef => Just (mid, mdef)

  bigG: Module -> ClassId -> FldId -> Maybe GhostDecl
  bigG mod cid gid = mod .@ cid $?
    \(ClassDef _ _ _ gs) =>
      gs .@ gid $?
       \gdef => Just (gid, gdef)

{-
DEFINITION 18 (RUNTIME ENTITIES). We define addresses, values, frames,
stacks, heaps and runtime configurations.
-}

||| We take addresses to be an enumerable set, Addr, and use the
||| identifier α ∈ Addr to indicate an address.
data Addr = MkAddr Nat
Eq Addr where
  (MkAddr a) == (MkAddr b) = a == b

Set: Type -> Type
Set a = a -> (Dec a)

||| Values, v, are either addresses, or sets of addresses or null: v ∈
||| {null} ∪ Addr ∪ P(Addr).
data Value = ValNull | ValAddr Addr | P (Set Addr)

||| Continuations are either statements (as defined in Definition 16)
||| or a marker, x:= •, for a nested call followed by statements to be
||| executed once the call returns.
data Continuation = Cont Stmts | NestedCall VarId Stmts

data CodeStub {- @@ISSUE: where is this defined??? -}

||| Frames, ϕ, consist of a code stub and a mapping from identifiers to values:
record Frame where
  constructor MkFrame
  contn: CodeStub
  varMap: VMap VarId Value


||| Stacks, ψ, are sequences of frames, ψ ::= ϕ | ϕ · ψ.
Stack: Type
Stack = VecLen Frame

||| Objects consist of a class identifier, and a partial mapping from
||| field identifier to values:
Object: Type
Object = (ClassId, VMap FldId Value)

||| Heaps, χ, are mappings from addresses to objects:
Heap: Type
Heap = VMap Addr Object

||| Runtime configurations, σ, are pairs of stacks and heaps,
||| σ ::= ( ψ, χ ).-}
Configuration: Type
Configuration = (Stack, Heap)

{-
DEFINITION 19 (INTERPRETATIONS). We first define lookup of fields and
classes, where α is an address, and f is a field identifier:
-}

infix 12 ..@
||| χ (α, f) ≜ fldMap(α, f) if χ (α) = (_, fldMap).
(..@): Heap -> (Addr, FldId) -> (Maybe Value)
chi ..@ (a, f) = chi .@ a $? \(_, fldMap) => vlookup f fldMap

||| Class(α)χ ≜ C if χ (α) = (C, _)
Class: Addr -> Heap -> (Maybe ClassId)
Class alpha chi = chi .@ alpha $? \(c, _) => Just c


infix 11 //
infix 11 ///

data VarInterp = VI VarId
data Interp = (//) VarId Frame | (///) FieldAccess (Frame, Heap)

|||We now define interpretations as follows:
||| ⌊x⌋ϕ ≜ ϕ(x)
||| ⌊x.f⌋(ϕ, χ ) ≜ v, if χ (ϕ(x)) = (_, fldMap) and fldMap(f)=v
interp: Interp -> (Maybe Value)
interp (x // phi) = (varMap phi) .@ x
interp ((x .. f) /// (phi, chi)) =
  (varMap phi) .@ x $? \v =>
    case v of
      (ValAddr a) => chi .@ a $? \(_, fldMap) => fldMap .@ f
      _ => Nothing

{-
Operational Semantics

methCall_OS

ϕ.contn = x:= x0.m( x1, ...xn) ; Stmts
⌊x0⌋ϕ = α
M(M, Class(α)χ , m) = m( p1, . . . pn) { Stmts1}
ϕ′′ = ( Stmts1, ( this 7→ α, p1 7→ ⌊x1⌋ϕ, . . . pn 7→ ⌊xn⌋ϕ ) )
---
M, ( ϕ · ψ, χ ) ❀ ( ϕ′′ · ϕ[contn 7→ x:= • ; Stmts] · ψ, χ )
-}

data (~>): (Module, (Stack, Heap)) -> (Stack, Heap) -> Type where
  MethCall_OS:
     (m: Module)
     -> (phi, phi'': Frame)
     -> (ns: Nat) -> (psi: Vect ns Frame)
     -> (chi: Heap)
     -> (m, (((S ns) ** phi :: psi), chi)) ~> (((S ns) ** phi'' :: psi), chi)


{-

DEFINITION 1. Given runtime configurations σ, σ′, and a module-pair
M#M′ we define execution where M is the internal, and M′ is the
external module as below:• M # M′, σ ❀ σ′ if there exist n ≥ 2 and
runtime configurations σ1, ... σn, such that– σ=σ1, and σn = σ′.–
M◦M′, σi ❀ σ′ i+1, for 1 ≤ i ≤ n−1 – Class(this)σ < dom(M), and
Class(this)σ′ < dom(M), – Class(this)σi ∈ dom(M), for 2 ≤ i ≤ n−2

-}



data ModulePair: Type where
  Semi: (M: Module) -> (M': Module) -> ModulePair


data ModuleContext: Type where
  (#): Module -> Module -> ModuleContext

data ConfigInContext = (/) ModuleContext Configuration

{- Execution -}
data (~~>): ConfigInContext -> Configuration -> Type where
  TwoModuleExecution: (sigma, sigma': Configuration)
           -> (m, m': Module)
           -> (n: Nat)
           -> (sigmas: (Vect (S n) Configuration))
           -> sigma = head sigmas
           -> sigma' = last sigmas
           {- @@@ -> ({i :Fin n} -> Vect.index i sigmas) -}
           -> m # m' / sigma ~~> sigma'

-- Local Variables:
-- idris-load-packages: ("contrib")
-- End:

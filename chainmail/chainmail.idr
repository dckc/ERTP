module Chainmail

import Data.Vect

%default total

||| Finite sequences: where the paper has `phi | phi \middot psi`, we
||| implicitly convert `phi` using `toSeq` and we write `phi :: psi`
||| for adding an element.
Seq: (a: Type) -> Type
Seq = List

implicit toSeq: (Vect n a) -> (Seq a)
toSeq = toList

infix 8 :==>
||| Finite mappings: we use sequences of key, value pairs,
||| assuming we never need to compare mappings for equality.
(:==>): (k: Type) -> (v: Type) -> Type
(:==>) k v = Seq (k, v)

infix 12 .@
||| Where the paper writes `m(k)` we write `m .@ k`. Since `m(k)` may
||| be undefined, we return `Maybe v`
(.@): Eq k => (k :==> v) -> k -> (Maybe v)
m .@ k = lookup k m

infix 11 $?
||| Where the paper has `f(m(k))`, since `m(k)` may be undefined
||| (i.e. Nothing) we write `m .@ k ?: f`
($?): (Maybe a) -> (a -> Maybe b) -> (Maybe b)
(Just a) $? f = f a
Nothing $? f = Nothing

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
  Module: Type
  Module = ClassId :==> ClassDescr

  ||| DEFINITION 16 (CLASSES). Class descriptions consist of field
  ||| declarations, method declarations, and ghostfield declarations.
  data ClassDescr: Type where
    ClassDef: ClassId
              -> (Seq FieldDecl)
              -> (Seq MethDecl)
              -> (Seq GhostDecl)
              -> ClassDescr
 
  FieldDecl: Type
  FieldDecl = FldId

  MethDecl: Type
  MethDecl = (MethId, (Seq VarId, Stmts))

  Stmts : Type
  Stmts = Seq Stmt

  infix 12 ..

  data FieldAccess = (..) VarId FldId
  data Call = MkCall VarId MethId (Seq VarId)

  ||| x.f:= x | x:= x.f | x:= x.m( x* ) | x:= new C ( x∗ ) | return x
  data Stmt = SetField FieldAccess VarId
            | GetField VarId FieldAccess
            | GetCall VarId Call
            | GetNew VarId ClassId (Seq VarId)
            | Return VarId

  GhostDecl: Type
  GhostDecl = (FldId, VarId :==> Expr)

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

||| Frames, ϕ, consist of a code stub and a mapping from identifiers to values:
Frame: Type
Frame = (Continuation, VarId :==> Value)

||| Stacks, ψ, are sequences of frames, ψ ::= ϕ | ϕ · ψ.
Stack: Type
Stack = Seq Frame

implicit asStack: Frame -> Stack
asStack f = [f]

||| Objects consist of a class identifier, and a partial mapping from
||| field identifier to values:
Object: Type
Object = (ClassId, FldId :==> Value)

||| Heaps, χ, are mappings from addresses to objects:
Heap: Type
Heap = Addr :==> Object

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
chi ..@ (a, f) = chi .@ a $? \(_, fldMap) => lookup f fldMap

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
interp (x // (_, varMap)) = varMap .@ x
interp ((x .. f) /// (phi, chi)) =
  (snd phi) .@ x $? \v =>
    case v of
      (ValAddr a) => chi .@ a $? \(_, fldMap) => fldMap .@ f
      _ => Nothing

{-

DEFINITION 20 (LOOKUP AND UPDATE OF RUNTIME CONFIGURATIONS). We define
convenient shorthands for looking up in runtime entities.
-}
||| Assuming that φ is the tuple (stub,varMap), we use the notation φ.contn to obtain stub.
contn: Frame -> Continuation
contn (c, _) = c

||| • Assuming a value v, and that φ is the tuple (stub,varMap), we define
||| φ[contn 􏰀→ stub’] for updating the stub, i.e. (stub’,varMap).
updateStub: Continuation -> Continuation -> Frame -> Frame
updateStub contn stub' phi = (stub', snd phi)

||| We use φ[x 􏰀→ v] for updating the variable map, i.e. (stub,varMap[x 􏰀→ v]).
varMapUpdate: VarId -> Value -> Frame -> Frame
varMapUpdate x v (stub, varMap) = (stub, ((x, v) :: varMap))

||| • Assuming a heap χ, a value v, and that χ(α) = (C, fieldMap), we
||| use χ[α,f 􏰀→ v] as a shorthand for updating the object, i.e.
|||  χ[α􏰀→ (C, fieldMap[f 􏰀→ v]].
heapUpdate: Addr -> FldId -> Value -> Heap -> Heap
heapUpdate alpha f v chi = ?todo

pmap: {n: Nat}
      -> (p1n: (Vect n VarId)) -> (x1n: (Vect n VarId)) -> (phi: Frame) -> (Maybe (Vect n (VarId, Value)))
pmap {n=Z} [] [] phi = Just []
pmap {n=S k} (p1 :: p2n) (x1 :: x2n) phi =
  case pmap {n=k} p2n x2n phi of
    (Just m2n) => (interp (x1 // phi)) $? \v1 => Just ((p1, v1) :: m2n)
    Nothing => Nothing

newStack: Frame -> VarId -> Stmts -> Frame -> Stack -> Stack
newStack phi'' x stmts (_, vm) psi = phi'' :: (((NestedCall x stmts), vm) :: psi)

infix 7 ~>
infix 7 ~>*
infix 7 ~~>
||| Execution of a statement has the form M, σ Y σ ′,
||| and is defined in figure 6.
||| Operational Semantics
data (~>): (Module, (Stack, Heap)) -> (Stack, Heap) -> Type where
  ||| methCall_OS
  ||| ϕ.contn = x:= x0.m( x1, ...xn) ; Stmts
  ||| ⌊x0⌋ϕ = α
  ||| M(M, Class(α)χ , m) = m( p1, . . . pn) { Stmts1}
  ||| ϕ′′ = ( Stmts1, ( this 7→ α, p1 7→ ⌊x1⌋ϕ, . . . pn 7→ ⌊xn⌋ϕ ) )
  ||| ---
  ||| M, ( ϕ · ψ, χ ) ❀ ( ϕ′′ · ϕ[contn 7→ x:= • ; Stmts] · ψ, χ )
  MethCall_OS:
     {phi: Frame} -> {x, x0: VarId} -> {m: MethId} -> {n: Nat} -> {x1n: Vect n VarId} -> {stmts, stmts1: Stmts}
     -> {alpha: Addr}
     -> {mm: Module} -> {chi: Heap} -> {p1n: Vect n VarId} 
     -> (phi'': Frame)
     -> {psi: Stack}
     -> (contn phi) = (Cont ((GetCall x (MkCall x0 m x1n)) :: stmts))
     -> interp (x0 // phi) = Just (ValAddr alpha)
     -> (Class alpha chi) = (Just cid) -> (bigM mm cid m) = Just (m, (p1n, stmts1))
     -> (pmap p1n x1n phi) = (Just m1n) -> phi'' = ((Cont stmts1), ((This, (ValAddr alpha)) :: m1n))
     -> (mm, (phi :: psi, chi)) ~> (newStack phi'' x stmts phi psi, chi)


{-
DEFINITION 21 (EXECUTION). of one or more steps is defined as follows:

  • The relation M,σ Yσ′,itisdefinedinFigure6.

  • M,σ Y∗ σ′ holds, if i) σ=σ′, or ii) there exists a σ′′ such that M,σ Y∗ σ′′ and M,σ′′ Y σ′.
-}
data (~>*): (Module, Configuration) -> Configuration -> Type where
  ExcRefl: (m, sigma) ~>* sigma
  ExcTrans: (m, sigma) ~>* sigma'' -> (m, sigma'') ~> sigma' -> (m, sigma) ~>* sigma'

{-

DEFINITION 22 (EXTENDING RUNTIME CONFIGURATIONS). The relation ⊑ is
defined on runtime configurations as follows. Take arbitrary
configurations σ , σ ′, σ ′′, frame φ, stacks ψ , ψ ′, heap χ ,
address α free in χ , value v and object o, and define σ ⊑ σ ′ as the
smallest relation such that:

• σ⊑σ
• (φ[x􏰀→v]·ψ,χ)⊑(φ·ψ,χ)
• (φ · ψ · ψ ′, χ ) ⊑ (φ · ψ , χ )
• (φ, χ[α 􏰀→ o) ⊑ (φ ·ψ, χ)
• σ′ ⊑σ′′ andσ′′ ⊑σ implyσ′ ⊑σ
-}
data Extends: Configuration -> Configuration -> Type where
  ExtRefl: Extends sigma sigma
  ExtVmap: Extends ((varMapUpdate x v phi) :: psi, chi)  (phi :: psi, chi)
  -- stack
  -- heap
  ExtHeap: {phi: Frame} -> Extends (phi, (alpha, o) :: chi) (phi :: psi, chi)
  ExtTrans: Extends sig' sig'' -> Extends sig'' sig -> Extends sig' sig

{-
LEMMA A.1 (PRESERVATION OF INTERPRETATIONS AND EXECUTIONS). If σ′ ⊑ σ, then
• If ⌊x⌋σ is defined, then ⌊x⌋σ ′ =⌊x⌋σ .
• If ⌊this.f⌋σ is defined, then ⌊this.f⌋σ ′ =⌊this.f⌋σ .
• If Class(α)σ is defined, then Class(α)σ′ = Class(α)σ .
• If M,σ Y∗ σ′′, then there exists a σ′′, so that M,σ′ Y∗ σ′′′ and σ′′′ ⊑ σ′′.
-}

{-

DEFINITION 1. Given runtime configurations σ, σ′, and a module-pair
M#M′ we define execution where M is the internal, and M′ is the
external module as below:• M # M′, σ ❀ σ′ if there exist n ≥ 2 and
runtime configurations σ1, ... σn, such that– σ=σ1, and σn = σ′.–
M◦M′, σi ❀ σ′ i+1, for 1 ≤ i ≤ n−1 – Class(this)σ < dom(M), and
Class(this)σ′ < dom(M), – Class(this)σi ∈ dom(M), for 2 ≤ i ≤ n−2

-}

{- where the paper uses M;M' , we use M#M' -}
infix 11 #


data ModulePair: Type where
  Semi: (M: Module) -> (M': Module) -> ModulePair


data ModuleContext: Type where
  (#): Module -> Module -> ModuleContext

data ConfigInContext = (/) ModuleContext Configuration

{- Execution -}
data (~~>): ConfigInContext -> Configuration -> Type where
  TwoModuleExecution: (sigma, sigma': Configuration)
           -> (m, m': Module)
           -> (sigmas: (Seq Configuration)) -> NonEmpty sigmas
           -> sigma = head sigmas
           -> sigma' = last sigmas
           {- @@@ -> ({i :Fin n} -> Vect.index i sigmas) -}
           -> m # m' / sigma ~~> sigma'



{-
http://docs.idris-lang.org/en/latest/tutorial/typesfuns.html

Infix operators can use any of the symbols:

:+-*\/=.?|&><!@$%^~#

Some operators built from these symbols can’t be user defined. These
are :, =>, ->, <-, =, ?=, |, **, ==>, \, %, ~, ?, and !.

-}

{-

http://docs.idris-lang.org/en/latest/tutorial/miscellany.html?highlight=literate#implicit-conversions

implicit intString : Int -> String
intString = show

test : Int -> String
test x = "Number " ++ x
-}

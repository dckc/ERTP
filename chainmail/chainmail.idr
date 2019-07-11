module Chainmail

import Data.Vect
import Data.List
import Data.List.Quantifiers as Q
import Pruviloj
import Pruviloj.Derive.DecEq

import Notation
import Modules

%language ElabReflection

%default total

{-
A THE UNDERLYING PROGRAMMING LANGUAGE, Loo

A.1 Modules and Classes

Loo programs consist of modules, which are repositories of code. Since
we study class based oo languages, in this work, code is represented
as classes, and modules are mappings from identifiers to class
descriptions.
-}

{-
DEFINITION 18 (RUNTIME ENTITIES). We define addresses, values, frames,
stacks, heaps and runtime configurations.
-}

||| We take addresses to be an enumerable set, Addr, and use the
||| identifier α ∈ Addr to indicate an address.
data Addr = MkAddr Nat
Eq Addr where
  (MkAddr a) == (MkAddr b) = a == b
decAddrEq : (x1, x2 : Addr) -> Dec (x1 = x2)
%runElab (deriveDecEq `{decAddrEq})
DecEq Addr where
  decEq = decAddrEq

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

VarEnv VarId Frame where
  vars (_, varMap) = vars varMap

implicit locals: Frame -> (VarId :==> Value)
locals (_, varMap) = varMap

infix 10 :*:
||| Stacks, ψ, are sequences of frames, ψ ::= ϕ | ϕ · ψ.
data Stack = One Frame | (:*:) Frame Stack

VarEnv VarId Stack where
  vars (One phi) = vars phi
  vars (phi :*: psi) = (vars phi) ++ (vars psi)

-- ISSUE: subsume implicit with interfaces?
implicit asStack: Frame -> Stack
asStack f = One f

implicit asList: Stack -> (List Frame)
asList (One f) = [f]
asList (f :*: s) = f :: s

infix 9 :++:
(:++:): Stack -> Stack -> Stack
(:++:) (One f) b = f :*: b
(:++:) (f :*: a) b = f :*: (a :++: b)

||| Objects consist of a class identifier, and a partial mapping from
||| field identifier to values:
Object: Type
Object = (ClassId, FldId :==> Value)

||| Heaps, χ, are mappings from addresses to objects:
Heap: Type
Heap = Addr :==> Object

||| Runtime configurations, σ, are pairs of stacks and heaps,
||| σ ::= ( ψ, χ ).
Configuration: Type
Configuration = (Stack, Heap)

infix 12 ..@
||| DEFINITION 19 (INTERPRETATIONS). We first define lookup of fields and
||| classes, where α is an address, and f is a field identifier:
|||
||| χ (α, f) ≜ fldMap(α, f) if χ (α) = (_, fldMap).
(..@): Heap -> (Addr, FldId) -> (Maybe Value)
chi ..@ (a, f) =
  do
    (_, fldMap) <- chi .@ a
    v <- fldMap .@ f
    pure v

||| Class(α)χ ≜ C if χ (α) = (C, _)
Class: Addr -> Heap -> (Maybe ClassId)
Class alpha chi =
  do
    (c, _) <- chi .@ alpha
    pure c


infix 11 //

interface InterpContext t a where
  (//) : t -> a -> Maybe Value

|||We now define interpretations as follows:
||| ⌊x⌋ϕ ≜ ϕ(x)
InterpContext VarId Frame where
  x // phi = phi .@ x

||| ⌊x.f⌋(ϕ, χ ) ≜ v, if χ (ϕ(x)) = (_, fldMap) and fldMap(f)=v
InterpContext FieldAccess (Frame, Heap) where
 (x .. f) // (phi, chi) = (locals phi) .@ x `ifdef` \addr => case addr of
   (ValAddr a) => chi .@ a `ifdef` \(_, fldMap) => fldMap .@ f
   _ => Nothing
 where
   ifdef : (Maybe a) -> (a -> Maybe b) -> Maybe b
   ifdef Nothing _ = Nothing
   ifdef (Just x) f = (f x)

||| For ease of notation, we also use the shorthands below:
||| • ⌊x⌋(φ·ψ,χ) ≜⌊x⌋φ
InterpContext VarId Configuration where
  x // (One phi, chi) = x // phi
  x // (phi :*: psi, chi) = x // phi

-- • ⌊x.f⌋(φ·ψ,χ) ≜ ⌊x.f⌋(φ,χ)
InterpContext FieldAccess Configuration where
  (x .. f) // (phi :*: psi, chi) = (x .. f) // (phi, chi)
  (x .. f) // _ = Nothing

||| • Class(α ) (ψ , χ ) ≜ Class(α ) χ
||| • Class(x) σ ≜ Class(⌊x⌋ σ ) σ

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
updateStub contn stub' phi = (stub', locals phi)

||| We use φ[x 􏰀→ v] for updating the variable map, i.e. (stub,varMap[x 􏰀→ v]).
updateVarMap: VarId -> Value -> Frame -> Frame
updateVarMap x v (stub, varMap) = (stub, ((x, v) :: varMap))


prependSame : {x: VarId} -> {v: Value} -> {phi : Frame} ->
  (x :: vars (locals phi)) = vars $ locals $ updateVarMap x v phi
prependSame {phi = (_, [])} = Refl
prependSame {phi = (_, (x0, v0) :: rest)} = Refl

||| • Assuming a heap χ, a value v, and that χ(α) = (C, fieldMap), we
||| use χ[α,f 􏰀→ v] as a shorthand for updating the object, i.e.
|||  χ[α􏰀→ (C, fieldMap[f 􏰀→ v]].
heapUpdate: Addr -> FldId -> Value -> Heap -> Heap
heapUpdate alpha f v chi = case chi .@ alpha of
  Just (c, fieldMap) => (alpha, (c, (f, v) :: fieldMap)) :: chi
  Nothing => chi


pmap: {n: Nat}
      -> (p1n: (Vect n VarId)) -> (x1n: (Vect n VarId)) -> (phi: Frame) -> (Maybe (Vect n (VarId, Value)))
pmap {n=Z} [] [] phi = Just []
pmap {n=S k} (p1 :: p2n) (x1 :: x2n) phi =
  case pmap {n=k} p2n x2n phi of
    (Just m2n) => case (x1 // phi) of
      Just v1 => Just ((p1, v1) :: m2n)
      Nothing => Nothing
    Nothing => Nothing

newStack: Frame -> VarId -> Stmts -> Frame -> Stack -> Stack
newStack phi'' x stmts (_, vm) psi = phi'' :*: (((NestedCall x stmts), vm) :*: psi)

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
     -> (contn phi) = (Cont ((GetCall x (MkCall x0 m $ toList x1n)) :: stmts))
     -> (x0 // phi) = Just (ValAddr alpha)
     -> (Class alpha chi) = (Just cid) -> (bigM mm cid m) = Just (m, (toList p1n, stmts1))
     -> (pmap p1n x1n phi) = (Just m1n) -> phi'' = ((Cont stmts1), ((This, (ValAddr alpha)) :: (toList m1n)))
     -> (mm, (phi :*: psi, chi)) ~> (newStack phi'' x stmts phi psi, chi)


{-
DEFINITION 21 (EXECUTION). of one or more steps is defined as follows:

  • The relation M,σ Yσ′,itisdefinedinFigure6.

  • M,σ Y∗ σ′ holds, if i) σ=σ′, or ii) there exists a σ′′ such that M,σ Y∗ σ′′ and M,σ′′ Y σ′.
-}
data (~>*): (Module, Configuration) -> Configuration -> Type where
  ExcRefl: (m, sigma) ~>* sigma
  ExcTrans: (m, sigma) ~>* sigma'' -> (m, sigma'') ~> sigma' -> (m, sigma) ~>* sigma'


||| DEFINITION 22 (EXTENDING RUNTIME CONFIGURATIONS). The relation ⊑ is
||| defined on runtime configurations as follows. Take arbitrary
||| configurations σ , σ ′, σ ′′, frame φ, stacks ψ , ψ ′, heap χ ,
||| address α free in χ , value v and object o, and define σ ⊑ σ ′ as the
||| smallest relation such that:
|||
||| • σ⊑σ
||| • (φ[x􏰀→v]·ψ,χ)⊑(φ·ψ,χ)
||| • (φ · ψ · ψ ′, χ ) ⊑ (φ · ψ , χ )
||| • (φ, χ[α 􏰀→ o) ⊑ (φ ·ψ, χ)
||| • σ′ ⊑σ′′ andσ′′ ⊑σ implyσ′ ⊑σ
data Extension: Configuration -> Configuration -> Type where
  ExtRefl: Extension sigma sigma
  ExtVmap: (x: VarId) -> (v: Value) -> (phi: Frame)
           -> (psi: Stack) -> (chi: Heap)
           -> {auto xfree: x `freeIn` phi}
           -> Extension ((updateVarMap x v phi) :*: psi, chi)
                        (phi :*: psi, chi)
  ExtStack: {psi: Stack}
            -> Extension (phi :*: (psi :++: psi'), chi) (phi :*: psi, ch)
  ExtHeap: {phi: Frame} -> {auto afree: alpha `freeIn` chi}
           -> Extension (phi, (alpha, o) :: chi) (phi :*: psi, chi)
  ExtTrans: Extension sig' sig'' -> Extension sig'' sig -> Extension sig' sig

extDefined : {x: VarId} -> (ext: Extension sig' sig) -> (defined: IsJust (x // sig)) -> (IsJust (x // sig'))
extDefined ExtRefl defined = defined
extDefined {x} (ExtVmap x' v' phi psi chi) defined =
  let
    hasKey = definedHasKey {env=locals phi} {key=x} defined
    sameList = prependSame {phi} {x=x'} {v=v'}
    l1 = There {y=x'} hasKey
    h1 = keysDefined {key=x} {env=locals phi} hasKey
    h2 = replace {P=\t => Elem x t} sameList l1
  in
    keysDefined {key=x} h2
extDefined ExtStack defined = ?extDefined_stack
extDefined ExtHeap defined = ?extDefined_heap
extDefined (ExtTrans ext12 ext20) defined = ?extDefined_trans

{-
LEMMA A.1 (PRESERVATION OF INTERPRETATIONS AND EXECUTIONS). If σ′ ⊑ σ, then
• If ⌊x⌋σ is defined, then ⌊x⌋σ ′ =⌊x⌋σ .
• If ⌊this.f⌋σ is defined, then ⌊this.f⌋σ ′ =⌊this.f⌋σ .
• If Class(α)σ is defined, then Class(α)σ′ = Class(α)σ .
• If M,σ Y∗ σ′′, then there exists a σ′′, so that M,σ′ Y∗ σ′′′ and σ′′′ ⊑ σ′′.
-}
lemmaA1: {x : VarId}
      -> (Extension sig' sig)
      -> ((IsJust $ (x // sig))
      -> (x // sig') = (x // sig))
lemmaA1 ExtRefl _ = Refl
lemmaA1 {x} (ExtVmap x' v (cont, varMap) psi chi {xfree}) defined with (decEq x x')
  | Yes pfEq =
    let
      sigx' = replace {P=\t => IsJust $ varMap .@ t} pfEq defined
      x'bound = definedHasKey {env=varMap} sigx'
    in absurd $ xfree x'bound
  | No pfNeq = Refl
lemmaA1 ExtStack defined = Refl
lemmaA1 ExtHeap defined = Refl
lemmaA1 {x} (ExtTrans ext12 ext20 {sig} {sig'} {sig''}) defined =
  let
    d20 = extDefined ext20 defined
    eq20 = lemmaA1 {x} {sig'=sig''} {sig} ext20 ?d20
    eq12 = lemmaA1 {x} {sig'} {sig=sig''} ext12 ?d12
  in trans eq12 eq20


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
           -> (sigmas: (List Configuration)) -> NonEmpty sigmas
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

-- Local Variables:
-- idris-load-packages: ("pruviloj" "contrib")
-- End:

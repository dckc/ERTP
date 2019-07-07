module Notation

import Data.List

%default total
%access public export

{-
||| Finite mappings
||| see also coq's WSFun
||| https://coq.inria.fr/library/Coq.FSets.FMapInterface.html
-}

infix 8 :==>
(:==>) : Type -> Type -> Type
(:==>) k v = List (k, v)

infix 12 .@
||| Where the paper writes `m(k)` we write `m .@ k`. Since `m(k)` may
||| be undefined, we return `Maybe v`
||| Where the paper has `f(m(k))`, since `m(k)` may be undefined
||| (i.e. Nothing) we use do notation
(.@): DecEq k => (m: k :==> v) -> (key: k) -> Maybe v
[] .@ key = Nothing
((k0, v0) :: rest) .@ key with (decEq key k0)
 | Yes _ = Just v0
 | No _ = rest .@ key

add_1: DecEq k => (key: k) -> (val: v) -> (m: k :==> v) ->
  (((key, val) :: m) .@ key) = (Just val)
add_1 key val _ = rewrite (decEqSelfIsYes {x=key}) in Refl

mapNeqRest: DecEq k => (key, k0: k) -> Not (key = k0) -> ((k0, v0) :: m') .@ key = m' .@ key
mapNeqRest key k0 neq with (decEq key k0)
  | Yes pfEq = absurd $ neq pfEq
  | No _ = Refl

interface DecEq x => VarEnv x a where
  vars : a -> List x

DecEq x => VarEnv x (x :==> v) where
  vars m = map fst m

freeIn: (DecEq x, VarEnv x e) => (var: x) -> e -> Type
freeIn var env = Not (Elem var (vars env))

freeMapsToNothing: (DecEq x) => {n: x} -> (n `freeIn` env) -> env .@ n = Nothing
freeMapsToNothing {env=[]} pf = Refl
freeMapsToNothing {n} {env=(n0, v0) :: env'} notElem with (decEq n n0)
  | Yes pfEq = absurd $ notElem here where here = rewrite pfEq in Here
  | No pfNeq with (isElem n (map fst env'))
    | Yes later = absurd $ notElem $ There later
    | No notLater = let r = mapNeqRest {m'=env'} {v0} n n0 pfNeq
      in freeMapsToNothing notLater

-- Local Variables:
-- idris-load-packages: ("containers" "contrib")
-- End:

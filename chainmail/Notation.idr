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
((k0, v0) :: m') .@ key with (decEq key k0)
 | Yes _ = Just v0
 | No _ = m' .@ key

add_1: DecEq k => (key: k) -> (val: v) -> (m: k :==> v) ->
  (((key, val) :: m) .@ key) = (Just val)
add_1 key val _ = rewrite (decEqSelfIsYes {x=key}) in Refl

mapNeqRest: DecEq k => (key, k0: k) -> Not (key = k0) -> ((k0, v0) :: m') .@ key = m' .@ key
mapNeqRest key k0 neq with (decEq key k0)
  | Yes pfEq = absurd $ neq pfEq
  | No _ = Refl

interface DecEq k => VarEnv k a where
  vars : a -> List k

DecEq k => VarEnv k (k :==> v) where
  vars m = map fst m

freeIn: (DecEq k, VarEnv k e) => (key: k) -> e -> Type
freeIn key env = Not (Elem key (vars env))

freeMapsToNothing: (DecEq k) => {key: k} -> (key `freeIn` env) -> env .@ key = Nothing
freeMapsToNothing {env=[]} pf = Refl
freeMapsToNothing {key} {env=(k0, v0) :: env'} notElem with (decEq key k0)
  | Yes pfEq = absurd $ notElem here where here = rewrite pfEq in Here
  | No pfNeq with (isElem key (map fst env'))
    | Yes later = absurd $ notElem $ There later
    | No notLater = freeMapsToNothing notLater

definedHasKey: (DecEq k) => {key: k} -> {v: Type} -> {env: k :==> v} ->
  (IsJust (env .@ key)) -> Elem key (vars env)
definedHasKey {env} {key} defined = case env of
 [] impossible
 (k0, v0) :: env' => case decEq key k0 of
  Yes pfEq => rewrite pfEq in Here
  No pfNeq => case isElem key (vars env') of
      Yes later => There later
      No notLater =>
        let
          h1 = freeMapsToNothing {env = env'} notLater
          h2 = mapNeqRest {m'=env'} {v0} key k0 pfNeq
          h3 = trans h2 h1
          h4 = replace h3 defined
        in absurd h4

-- Local Variables:
-- idris-load-packages: ("containers" "contrib")
-- End:

module Notation

import Data.Vect
import Decidable.Order

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

data MapsTo : (DecEq k) =>
     (key: k) -> (val: v) -> (m: List (k, v)) -> Type where
  Here: (DecEq k) =>
    (key: k) -> (val: v) -> (m: List (k, v)) ->
    MapsTo key val ((key, val) :: m)
  MThere: (DecEq k) =>
    (key, k0: k) -> (val, v0: v) -> (m: List (k, v)) ->
    ((k0 = key) -> Void) -> (MapsTo key val m) ->
    MapsTo key val ((k0, v0) :: m)

private
noMapToNil : (DecEq k) => (key: k) -> MapsTo key val [] -> Void
noMapToNil _ (Here _ _ _) impossible
noMapToNil _ (MThere _ _ _ _ _ _ _) impossible

private
notHereNotThere : (DecEq k) => {kvs : List (k, v)} ->
     (neq: (k0 = key) -> Void) ->
     (notThere: (val : v ** MapsTo key val kvs) -> Void) ->
     (val : v ** MapsTo key val ((k0, v0) :: kvs)) -> Void
notHereNotThere neq _ (v1 ** Here key v1 ((k0, val) :: kvs)) = neq Refl
notHereNotThere {key} neq _ (v0 ** Here key v0 []) = neq Refl
notHereNotThere {key} neq notThere (x ** MThere key _ x _ _ _ maps) =
  notThere (x ** maps)

mapsTo: (DecEq k) => (key: k) -> (m: List (k, v)) ->
  Dec (val: v ** MapsTo key val m)
mapsTo key [] = No (\(_ ** toNil) => noMapToNil key toNil)
mapsTo key ((k0, v0) :: kvs) = case decEq k0 key of
  Yes eq => rewrite eq in Yes (v0 ** Here key v0 kvs)
  No neq => case mapsTo key kvs of
    Yes (it ** maps) => Yes (it ** MThere key k0 it v0 kvs neq maps)
    No notFound => No $ notHereNotThere neq notFound

mapVal : (DecEq k) => (key: k) -> (List (k, v)) -> Maybe v
mapVal key m = case mapsTo key m of
  Yes (it ** maps) => Just it
  No _ => Nothing

insertMap: (DecEq k) => (key: k) -> (val: v) -> (m: List (k, v)) ->
  (m': List (k, v) ** MapsTo key val m')
insertMap key val [] = ([(key, val)] ** Here key val [])
insertMap key val ((k0, v0) :: kvs) with (decEq k0 key)
  | Yes eq = ((key, val) :: kvs ** Here key val kvs)
  | No neq = let (mm ** maps) = insertMap key val kvs in
    ((k0, v0) :: mm ** MThere key k0 val v0 mm neq maps)


add1: (DecEq k) => {rest: List (k, v)} -> MapsTo key val ((key, val) :: rest)
add1 {key} {val} {rest} = Here key val rest


freeIn: DecEq k => (key: k) -> (k :==> v) -> Type
freeIn key dict = Not $ (val: v ** MapsTo key val dict)

definedAt: DecEq k => (m: (k :==> v)) -> (key: k) -> Type
definedAt m key = (val: v ** MapsTo key val m)

{-
export

keyValue: (key: k) -> (dict: (Dict k v)) -> (pf: HasKey key dict)
  -> v
keyValue key (MkDict $ Element t inv) (IsKey (IsKey found)) =
  keyValue' key t found
    where
      keyValue': (key: k) -> (t: Tree k v) -> (found: IsKeyIn key t) -> v
      keyValue' key (Node key val _ _) Here = val
      keyValue' key (Node not_key val left r) (InRight later) =
        keyValue' key r later
      keyValue' key (Node not_key val l right) (InLeft later) =
        keyValue' key l later

insertValue: DecEq k => Ord k => (key: k) -> (dict: Dict k v)
  -> keyValue key (insert key val dict) found = val
insertValue {val} {found} key dict = ?insertValue_rhs

mapSame: DecEq k => Ord k => (x, y: k) -> (m: Dict k v)
  -> (notfound: (x `freeIn` m))
  -> (found: (m `definedAt` y))
  -> (keyValue x (insert x vx m) foundx = keyValue y m found)
mapSame {foundx} x y m notfound found = ?mapSame_rhs


cantBe : DecEq k => (val : v) -> (rest : List (k, v))
  -> (notThere : (val1 : v ** Elem (key, val1) rest) -> Void)
  -> (notEq : (key = k0) -> Void)
  -> (val2 : v ** Elem (key, val2) ((k0, val) :: rest)) -> Void
cantBe val rest notThere notEq (vx ** pf) = case pf of
  Here {x=(k0, val)} {xs=rest} => notEq Refl
  There {later} => notThere (vx ** later)



export
at: DecEq k => (m: List (k, v)) -> (key: k)
  -> Dec (val: v ** lookup k m = Just v)
at [] key = No noSuch
  where noSuch (_ ** pf) = absurd pf
at ((k0, val) :: rest) key = case decEq key k0 of
  Yes pfEq => rewrite pfEq in Yes (val ** Here {x=(k0, val)} {xs=rest})
  No notEq => case rest `at` key of
    Yes (val ** inRest) => Yes (val ** There inRest)
    No notThere => No (cantBe val rest notThere notEq)


infix 12 .@
||| Where the paper writes `m(k)` we write `m .@ k`. Since `m(k)` may
||| be undefined, we return `Maybe v`
export
(.@): DecEq k => (m: k :==> v) -> (key: k) -> Maybe v
m .@ key = case m `at` key of
  Yes (v ** _) => Just v
  No _ => Nothing

infix 11 $?
||| Where the paper has `f(m(k))`, since `m(k)` may be undefined
||| (i.e. Nothing) we write `m .@ k ?: f`
export
($?): (Maybe a) -> (a -> Maybe b) -> (Maybe b)
(Just a) $? f = f a
Nothing $? f = Nothing
-}

-- Local Variables:
-- idris-load-packages: ("containers" "contrib")
-- End:

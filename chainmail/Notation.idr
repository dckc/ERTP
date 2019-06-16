module Notation

import Data.AVL
import Data.AVL.Dict
import Data.List

%default total

infix 8 :==>
||| Finite mappings
public export
(:==>): (k: Type) -> (v: Type) -> Type
(:==>) k v = Dict k v

freeIn: DecEq k => (key: k) -> (k :==> v) -> Type
freeIn key dict = Not $ HasKey key dict

export
definedAt: (m: (k :==> v)) -> (key: k) -> Type
definedAt m key = HasKey key m

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

{-
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

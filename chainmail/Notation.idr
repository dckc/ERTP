module Notation

import Data.List

%default total


infix 8 :==>
||| Finite mappings: we use sequences of key, value pairs,
||| assuming we never need to compare mappings for equality.
public export
(:==>): (k: Type) -> (v: Type) -> Type
(:==>) k v = List (k, v)

export
definedAt: (m: (k :==> v)) -> (key: k) -> Type
definedAt m key = (val: v ** Elem (key, val) m)

cantBe : DecEq k => (val : v) -> (rest : List (k, v))
  -> (notThere : (val1 : v ** Elem (key, val1) rest) -> Void)
  -> (notEq : (key = k0) -> Void)
  -> (val2 : v ** Elem (key, val2) ((k0, val) :: rest)) -> Void
cantBe val rest notThere notEq (vx ** pf) = case pf of
  Here {x=(k0, val)} {xs=rest} => notEq Refl
  There {later} => notThere (vx ** later)

export
at: DecEq k => (m: List (k, v)) -> (key: k)
  -> Dec (val: v ** Elem (key, val) m)
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

-- Local Variables:
-- idris-load-packages: ("pruviloj")
-- End:

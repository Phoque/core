module STLC

data Kind : Type where
  Star : Kind
  Arr : Kind -> Kind -> Kind

data Const : Kind -> Type where
  Unit : Const Star
  Sum : Const (Star `Arr` (Star `Arr` Star))
--  Prod : Const (Star `Arr` (Star `Arr` Star))

data Ctx : Type where
  Empty : Ctx
  Cons : Ctx -> Kind -> Ctx

data V : Kind -> Ctx -> Type where
  Top : V k (g `Cons` k) 
  Pop : V k g -> V k (g `Cons` k') 

data Typ : Ctx -> Kind -> Type where 
  Var  : V k g -> Typ g k 
  Lam  : Typ (g₁ `Cons` k) k₂ -> Typ g (k `Arr` k)
  App  : Typ g (k' `Arr` k) -> Typ g k' -> Typ g k
  Con  : Const k -> Typ g k


data SumT : Type -> Type -> Type where
  Un : {a : Type} -> { b :Type} -> a -> b -> SumT a b

sem : Kind -> Type
sem Star = Type
sem (a `Arr` b) = sem a -> sem b

interp_c : Const k -> sem k
interp_c Unit = ()
interp_c Sum = SumT

data Env : Ctx -> Type where
  EEmpty : Env Empty
  ECons : Env g -> sem k -> Env (g `Cons` k)

sLookup : V k g -> Env g -> sem k
sLookup Top (g `ECons` v) = v
sLookup (Pop x) (g `ECons` v) = sLookup x g

interp : Typ g k -> Env g -> sem k
interp (Var x) e = sLookup x e
-- interp (Lam t) e = \y => interp t (e `ECons` y) -- what's up with this case?
interp (App t1 t2) e = (interp t1 e) (interp t2 e)
interp (Con c) e = interp_c c
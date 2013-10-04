module LC

data Tp : Type where
  Unit : Tp
  Arr : Tp -> Tp -> Tp

data Var : Nat -> Type where
  Top : Var (S n)
  Pop : Var n -> Var (S n)

same : Var n -> Var n -> Bool
same v1 v2 = False


data Exp : Nat -> Type where
  One : Exp n
  V : Var n -> Exp n
  Lam : Exp (S n) -> Exp n
  App : Exp n -> Exp n -> Exp n

total weaken : Exp n -> Exp (S n)
weaken One = One
weaken (V x) = V (Pop x)
weaken (Lam e) = Lam (weaken e)
weaken (App e1 e2) = App (weaken e1) (weaken e2)

data Sub : Nat -> Nat -> Type where
     E : Sub Z n
     (::) : Exp n -> Sub m n -> Sub (S m) n

total weakensub : Sub m n -> Sub m (S n)
weakensub E = E
weakensub (e :: s) = weaken e :: weakensub s

total idsub : (m : Nat) -> Sub m m
idsub Z = E
idsub (S n) = (V Top) :: (weakensub (idsub n))

total subst : Sub m n -> Exp m -> Exp n
subst s One = One
subst s (Lam e) = Lam (subst (V Top :: weakensub s) e)
subst s (App e1 e2) = App (subst s e1) (subst s e2)
subst s (V x) = app s x
  where
    total app : Sub m n -> Var m -> Exp n
    app (y :: s) Top = y
    app (y :: s) (Pop x) = app s x

eval : Exp n -> Maybe (Exp n)
eval (V x) = Just (V x)
eval (Lam e) = Just (Lam e)
eval One = Just One
eval (App e1 e2) =
  case eval e1 of
    Just (Lam e) => eval (subst (e2 :: idsub _) e)
    _ => Nothing

example : Exp Z
example = App (Lam (V Top)) One

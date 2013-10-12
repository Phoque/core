{- SSGIP Examples, Stephanie Weirich, March 24-26, 2010 -}
{-# OPTIONS --type-in-type --no-termination-check --no-positivity-check #-}
module gh where

open import Data.Nat
open import Data.Vec hiding (_∈_)
open import Data.Unit hiding (Unit)
open import Data.Product
open import Data.Sum
open import Data.Bool
open import Relation.Binary.PropositionalEquality

infixr 50 _⇒_

data Kind : Set where 
  ⋆      : Kind 
  _⇒_    : Kind → Kind → Kind

data Const : Kind → Set where
  Unit  : Const ⋆
  Sum   : Const (⋆ ⇒ ⋆ ⇒ ⋆) 
  Prod  : Const (⋆ ⇒ ⋆ ⇒ ⋆)

data Ctx : Set where 
  []    : Ctx
  _∷_   : Kind → Ctx → Ctx

data V : Kind → Ctx → Set where
  top   : ∀ {Γ k} → V k (k ∷ Γ) 
  pop   : ∀ {Γ k' k} → V k Γ → V k (k' ∷ Γ) 

data Typ (Γ : Ctx) : Kind → Set where 
  Var  : ∀ {k} → V k Γ → Typ Γ k 
  Lam  : ∀ {k₁ k₂} → Typ (k₁ ∷ Γ) k₂ 
       → Typ Γ (k₁ ⇒ k₂)
  App  : ∀ {k₁ k₂} → Typ Γ (k₁ ⇒ k₂) → Typ Γ k₁
       → Typ Γ k₂
  Con  : ∀ {k} → Const k → Typ Γ k

Ty : Kind → Set
Ty k = Typ [] k

⟦_⟧        : Kind → Set
⟦ ⋆ ⟧      = Set
⟦ a ⇒ b ⟧  = ⟦ a ⟧ → ⟦ b ⟧

interp-c : ∀ {k} → Const k → ⟦ k ⟧
interp-c Unit     = ⊤     -- has kind Set
interp-c Sum      = _⊎_   -- has kind Set → Set → Set
interp-c Prod     = _×_

data Env : Ctx → Set where
  []   : Env [] 
  _∷_  : ∀ {k Γ} → ⟦ k ⟧ → Env Γ → Env (k ∷ Γ)

sLookup : ∀ {k Γ} → V k Γ → Env Γ → ⟦ k ⟧
sLookup top      (v ∷ Γ) = v
sLookup (pop x)  (v ∷ Γ) = sLookup x Γ

interp : ∀ {k Γ} → Typ Γ k → Env Γ → ⟦ k ⟧
interp (Var x)      e  = sLookup x e
interp (Lam t)      e  = \ y → interp t (y ∷ e)
interp (App t1 t2)  e  = (interp t1 e) (interp t2 e)
interp (Con c)      e  = interp-c c

⌊_⌋ : ∀ {k} → Ty k → ⟦ k ⟧
⌊ t ⌋ = interp t []

fco : Ty ( ⋆ ⇒ ⋆ )
fco = App (Lam (Var top)) (Lam (Var top)) 
 
Maybe : Set → Set
Maybe = \ A → ⊤ ⊎ A

maybe : Ty (⋆ ⇒ ⋆) 
maybe = 
   Lam (App (App (Con Sum) (Con Unit)) (Var top))

_⟨_⟩_ : (Set → Set) → (k : Kind) → ⟦ k ⟧ → Set 
b ⟨ ⋆ ⟩         t  = b t
b ⟨ k1 ⇒ k2 ⟩  t  = ∀ { A } → b ⟨ k1 ⟩ A → b ⟨ k2 ⟩ (t A)

data VarEnv  (b : Set → Set) : Ctx → Set where
   []   : VarEnv b []
   _∷_  : {k : Kind}  {Γ : Ctx}{a : ⟦ k ⟧}
          → b ⟨ k ⟩ a 
          → VarEnv b Γ 
          → VarEnv b (k ∷ Γ)

toEnv : {Γ : Ctx}{b : Set → Set} → VarEnv b Γ → Env Γ
toEnv [] = []
toEnv (_∷_ {_}{_}{a} _ r) = a ∷ toEnv r

vLookup : ∀ {Γ k}{b : Set → Set} 
           → (v : V k Γ) → (ve : VarEnv b Γ)
           → b ⟨ k ⟩ (sLookup v (toEnv ve))
vLookup top      (v ∷ ve)  = v
vLookup (pop x)  (v ∷ ve)  = vLookup x ve

Eq : Set → Set
Eq A = A → A → Bool

mutual
  geq-open : {Γ : Ctx}{k : Kind} 
    → (ve : VarEnv Eq Γ)
    → (t : Typ Γ k) → Eq ⟨ k ⟩ (interp t (toEnv ve))
  geq-open ve (Var v)      = vLookup v ve
  geq-open ve (Lam t)      = \ y → geq-open (y ∷ ve) t
  geq-open ve (App t1 t2)  = (geq-open ve t1) (geq-open ve t2)
  -- geq-open ve (Mu t)       = 
  --   \ x y → geq-open ve (App t (Mu t)) (unroll x) (unroll y)
  geq-open ve (Con c)      = geq-c c  

  geq-sum   : ∀ {A} → (A → A → Bool)
            → ∀ {B} → (B → B → Bool)
            → (A ⊎ B) → (A ⊎ B) → Bool
  geq-sum ra rb (inj₁ x₁) (inj₁ x₂) = ra x₁ x₂
  geq-sum ra rb (inj₂ x₁) (inj₂ x₂) = rb x₁ x₂
  geq-sum _ _ _ _  = false

  geq-prod  : ∀ {A} → (A → A → Bool) 
            → ∀{B} → (B → B → Bool)
            → (A × B) → (A × B) → Bool
  geq-prod ra rb ( x₁ , x₂ ) (y₁ , y₂) = ra x₁ y₁ ∧ rb x₂ y₂

  geq-c : {k : Kind} → (c : Const k) → Eq ⟨ k ⟩ ⌊ Con c ⌋
  geq-c Unit = \ t1 t2 → true
  geq-c Sum  = geq-sum 
  geq-c Prod = geq-prod

ConstEnv : (Set → Set) → Set
ConstEnv b = ∀ {k} → (c : Const k) → b ⟨ k ⟩ ⌊ Con c ⌋

-- MuGen : (Set → Set) → Set
-- MuGen b = ∀ {A} → b (A (μ A)) → b (μ A)


{-
gen-open : {b : Set → Set}{Γ : Ctx}{k : Kind} 
    → ConstEnv b → (ve : VarEnv b Γ) → MuGen b
    → (t : Typ Γ k) → b ⟨ k ⟩ (interp t (toEnv ve))
gen-open ce ve d (Var v)      = vLookup v ve
gen-open ce ve d (Lam t)      = \ y → gen-open ce (y ∷ ve) d t
gen-open ce ve d (App t1 t2)  = 
   (gen-open ce ve d t1) (gen-open ce ve d t2)
gen-open ce ve d (Con c)      = ce c 
gen-open ce ve d (Mu t)       = 
   d (gen-open ce ve d (App t (Mu t)))

gen : {b : Set → Set}{k : Kind} → ConstEnv b → MuGen b
    → (t : Ty k) → b ⟨ k ⟩ ⌊ t ⌋
gen c b t = gen-open c [] b t

geq : {k : Kind} → (t : Ty k) → Eq ⟨ k ⟩ ⌊ t ⌋
geq = gen geq-c eb where
  eb : ∀ {A} → Eq (A (μ A)) → Eq (μ A)
  eb f = \ x y → f (unroll x) (unroll y)

eq-list : List Nat → List Nat → Bool
eq-list = geq (App list nat)

Count : Set → Set 
Count A = A → ℕ

gcount : {k : Kind} → (t : Ty k) → Count ⟨ k ⟩ ⌊ t ⌋
gcount = gen ee eb where
  ee : ConstEnv Count
  ee Unit = \ t → 0
  ee Sum  = g where
     g : ∀ { A } → _ → ∀ { B } → _ → (A ⊎ B) → ℕ
     g ra rb (inj₁ x) = ra x 
     g ra rb (inj₂ x) = rb x
  ee Prod = g where
     g : ∀ { A } → _ → ∀ { B } → _ → (A × B) → ℕ
     g ra rb ( x₁ , x₂ ) = ra x₁ + rb  x₂

  eb : MuGen Count
  eb f = \ x → f (unroll x)

gsize : (t : Ty (⋆ ⇒ ⋆)) → ∀ {A} → ⌊ t ⌋ A → ℕ
gsize t = gcount t (\ x → 1)

gsum : (t : Ty (⋆ ⇒ ⋆)) → ⌊ t ⌋ ℕ → ℕ
gsum t = gcount t (\ x → x)

exlist2 : List ℕ
exlist2 = 1 ∶ 2 ∶ 3 ∶ nil

_⟨_⟩₂ : (Set → Set → Set) → (k : Kind) → ⟦ k ⟧ → ⟦ k ⟧ → Set 
b ⟨ ⋆ ⟩₂         = \ t₁ t₂ → b t₁ t₂
b ⟨ k₁ ⇒ k₂ ⟩₂  = \ t₁ t₂ → ∀ { a₁ a₂ } → 
   (b ⟨ k₁ ⟩₂) a₁ a₂ → (b ⟨ k₂ ⟩₂) (t₁ a₁) (t₂ a₂)
Map : Set → Set → Set
Map A B = A → B
Vec' : ℕ -> Set -> Set
Vec' zero     = \ A -> ⊤
Vec' (suc n)  = \ A -> A × (Vec' n A)
-}

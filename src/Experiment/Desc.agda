module Experiment.Desc where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.String hiding (_++_)

open import Data.List
open import Relation.Unary hiding (_⊆_ ; _⊇_ ; _∈_)

open import Relation.Binary.PropositionalEquality
  
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any hiding (lookup)
open import Data.List.Relation.Unary.All 

open import Function
open import Level

infixr 5 _`×_
data Con : Set where
  `var `0 `1 : Con
  _`×_ : (x y : Con) → Con

⟦_⟧con : ∀ {ℓ} → Con → Set ℓ → Set ℓ
⟦ `var   ⟧con X = X
⟦ `0     ⟧con X = Lift _ ⊥
⟦ `1     ⟧con X = Lift _ ⊤
⟦ x `× y ⟧con X = ⟦ x ⟧con X × ⟦ y ⟧con X

-- Constructors have a String label attached. This is purely to help out
-- instance search
Constructor = String × Con 

⟦_⟧ty : ∀ {ℓ} → List Constructor → Set ℓ → Set ℓ
⟦ []     ⟧ty _ = Lift _ ⊥
⟦ (_ , C) ∷ cs ⟧ty X = ⟦ C ⟧con X ⊎ ⟦ cs ⟧ty X


TypeDesc = List Constructor

data Mu (T : TypeDesc) : Set where
  mk : ⟦_⟧ty T (Mu T) → Mu T

map-con : ∀ {x y} {X : Set x} {Y : Set y} {C} → (X → Y) → ⟦ C ⟧con X → ⟦ C ⟧con Y
map-con {C = `var}   f x       = f x
map-con {C = `1}     f (lift tt)      = lift tt
map-con {C = _ `× _} f (x , y) = map-con f x , map-con f y

map-desc : ∀ {ℓ} {X Y : Set ℓ} {T} → (X → Y) → ⟦ T ⟧ty X → ⟦ T ⟧ty Y
map-desc {T = c ∷ cs} f (inj₁ x) = inj₁ (map-con  f x)
map-desc {T = c ∷ cs} f (inj₂ y) = inj₂ (map-desc f y)

Algebra : ∀ {ℓ} → TypeDesc → Set ℓ → Set ℓ
Algebra d a = ⟦ d ⟧ty a → a

_⊚_ : ∀ {ℓ} {a : Set ℓ} {T₁ T₂} → Algebra T₁ a → Algebra T₂ a → Algebra (T₁ ++ T₂) a
_⊚_ {T₁ = []} f g x = g x
_⊚_ {T₁ = C ∷ T₁} f g (inj₁ x) = f (inj₁ x)
_⊚_ {T₁ = C ∷ T₁} f g (inj₂ y) = ((f ∘ inj₂) ⊚ g) y

mutual 
  fold-desc : ∀ {ℓ} {T a} → Algebra {ℓ} T a → Mu T → a 
  fold-desc {ℓ} f (mk x) = f (map-fold f x)

  map-fold : ∀ {ℓ} {T₁ T₂ a} → Algebra {ℓ} T₂ a → ⟦ T₁ ⟧ty (Mu T₂) → ⟦ T₁ ⟧ty a
  map-fold {ℓ} {C ∷ cs} f (inj₁ x) = inj₁ (map-fold-con f x) 
  map-fold {ℓ} {C ∷ cs} f (inj₂ y) = inj₂ (map-fold f y)

  map-fold-con : ∀ {ℓ} {C T a} → Algebra {ℓ} T a → ⟦ C ⟧con (Mu T) → ⟦ C ⟧con a 
  map-fold-con {_} {`var}   f x         = fold-desc f x
  map-fold-con {_} {`1}     f (lift tt) = lift tt
  map-fold-con {_} {_ `× _} f (x , y)   = map-fold-con f x , map-fold-con f y

  -- A predicate for membership 
  Member : ∀ {ℓ} {A : Set ℓ} → List A → A → Set ℓ
  Member xs x = x ∈ xs
  
  _⊆_ : ∀ {ℓ} {A : Set ℓ} → (xs ys : List A) → Set ℓ
  xs ⊆ ys = All (Member ys) xs

  _⊇_ : ∀ {ℓ} {A : Set ℓ} → (xs ys : List A) → Set ℓ
  xs ⊇ ys = ys ⊆ xs


record _≼_ (C : Constructor) (T : TypeDesc) : Set where
  field sub : C ∈ T 

  inj : ∀ {ℓ} {C T} → C ∈ T  → ∀[ ⟦ C . proj₂ ⟧con ⇒ ⟦_⟧ty {ℓ} T ]
  inj (here refl) x = inj₁ x
  inj {ℓ} (there px) x = inj₂ (inj {ℓ} px x)

open _≼_ ⦃...⦄

variable
  C C₁ C₂ : Constructor 
  T T₁ T₂ : TypeDesc 

inject : ⦃ C ≼ T ⦄ → ⟦ (C .proj₂) ⟧con (Mu T) → Mu T
inject = mk ∘ inj sub 

instance ≼-here : C ≼ (C ∷ T)
≼-here .sub = here refl

instance ≼-there : ⦃ C₁ ≼ T ⦄ → C₁ ≼ (C₂ ∷ T)
≼-there .sub = there sub

record ReprClause {ℓ} (C : Constructor) (a : Set ℓ) : Set ℓ where
  field clause : ⟦ C .proj₂ ⟧con a → a

open ReprClause public 

ReprDesc : ∀ {ℓ} → (T : TypeDesc) → Set ℓ → Set ℓ
ReprDesc T a = All (λ C → ReprClause C a) T

toAlgebra : ∀ {ℓ} {a : Set ℓ} {T : TypeDesc} → ReprDesc T a → Algebra T a
toAlgebra {T = (_ , C) ∷ T} (f ∷ _)  (inj₁ x) = f .clause x
toAlgebra {T = (_ , C) ∷ T} (_ ∷ px) (inj₂ y) = toAlgebra px y

<_> : ∀ {ℓ} {a : Set ℓ} {T : TypeDesc} → ReprDesc T a → Mu T → a
< r > = fold-desc (toAlgebra r)

-- Clause inclusion 
record _◃_ {ℓ} {a : Set ℓ} {C : Constructor} {T : TypeDesc} (rc : ReprClause C a) (r : ReprDesc T a) : Set ℓ where
  field

    -- The constructor C is part of the type description T 
    ⦃ type-sub ⦄ : C ≼ T

    -- The canonical form(s) defined by C are preserved by T 
    canonical    : r [ sub ]= rc

open _◃_ 


instance ◃-here : ∀ {ℓ} {a : Set ℓ}  {C} {T} {rc : ReprClause C a} {V : ReprDesc T a} → rc ◃ (rc ∷ V)
_◃_.type-sub ◃-here = ≼-here
_◃_.canonical ◃-here = here

instance ◃-there : ∀ {ℓ} {a : Set ℓ}  {C C' : Constructor} {T : TypeDesc} {rc' : ReprClause C' a} {rc : ReprClause C a} {V : ReprDesc T a} → ⦃ _ : rc ◃ V ⦄ → rc ◃ (rc' ∷ V)
_◃_.type-sub ◃-there = ≼-there
_◃_.canonical (◃-there ⦃ px ⦄) = there (canonical px)

-- up/down cast

postulate ↑ : ∀ {l : String} {c : Con} {T : TypeDesc}
                 {rc : ReprClause (l , c) Set} {V : ReprDesc T Set} {t : ⟦ c ⟧con (Mu T)}
               → ⦃ _ : rc ◃ V ⦄
               → rc .clause (map-con < V > t) → < V > (inject t)
               
postulate ↓ : ∀ {l : String} {c : Con} {T : TypeDesc}
                 {rc : ReprClause (l , c) Set} {V : ReprDesc T Set} {t : ⟦ c ⟧con (Mu T)}
               → ⦃ _ : rc ◃  V ⦄
               → < V > (inject t) → rc .clause (map-con < V > t) 

module Experiment.Desc where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.String

open import Data.List
open import Relation.Unary hiding (_⊆_ ; _⊇_ ; _∈_)

open import Relation.Binary.PropositionalEquality
  
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any hiding (lookup)
open import Data.List.Relation.Unary.All 

open import Function

infixr 5 _`×_
data Con : Set where
  `var `0 `1 : Con
  _`×_ : (x y : Con) → Con

⟦_⟧con : Con → Set → Set
⟦ `var   ⟧con X = X
⟦ `0     ⟧con X = ⊥
⟦ `1     ⟧con X = ⊤
⟦ x `× y ⟧con X = ⟦ x ⟧con X × ⟦ y ⟧con X

Constructor = String × Con 

⟦_⟧ty : List Constructor → Set → Set
⟦ []     ⟧ty _ = ⊥
⟦ (_ , C) ∷ cs ⟧ty X = ⟦ C ⟧con X ⊎ ⟦ cs ⟧ty X


TypeDesc = List Constructor

data Mu (T : TypeDesc) : Set where
  mk : ⟦ T ⟧ty (Mu T) → Mu T

map-con : ∀ {X Y C} → (X → Y) → ⟦ C ⟧con X → ⟦ C ⟧con Y
map-con {C = `var}   f x       = f x
map-con {C = `1}     f tt      = tt
map-con {C = _ `× _} f (x , y) = map-con f x , map-con f y

map-desc : ∀ {X Y T} → (X → Y) → ⟦ T ⟧ty X → ⟦ T ⟧ty Y
map-desc {T = c ∷ cs} f (inj₁ x) = inj₁ (map-con  f x)
map-desc {T = c ∷ cs} f (inj₂ y) = inj₂ (map-desc f y)

Algebra : TypeDesc → Set → Set
Algebra d a = ⟦ d ⟧ty a → a

mutual 
  fold-desc : ∀ {T a} → Algebra T a → Mu T → a 
  fold-desc {d} f (mk x) = f (map-fold f x)

  map-fold : ∀ {T₁ T₂ a} → Algebra T₂ a → ⟦ T₁ ⟧ty (Mu T₂) → ⟦ T₁ ⟧ty a
  map-fold {C ∷ cs} f (inj₁ x) = inj₁ (map-fold-con f x) 
  map-fold {C ∷ cs} f (inj₂ y) = inj₂ (map-fold f y)

  map-fold-con : ∀ {C T a} → Algebra T a → ⟦ C ⟧con (Mu T) → ⟦ C ⟧con a 
  map-fold-con {`var}   f x        = fold-desc f x
  map-fold-con {`1}     f tt       = tt
  map-fold-con {_ `× _} f (x , y)  = map-fold-con f x , map-fold-con f y

  -- A predicate for membership 
  Member : ∀ {ℓ} {A : Set ℓ} → List A → A → Set ℓ
  Member xs x = x ∈ xs
  
  _⊆_ : ∀ {ℓ} {A : Set ℓ} → (xs ys : List A) → Set ℓ
  xs ⊆ ys = All (Member ys) xs

  _⊇_ : ∀ {ℓ} {A : Set ℓ} → (xs ys : List A) → Set ℓ
  xs ⊇ ys = ys ⊆ xs


record _≼_ (C : Constructor) (T : TypeDesc) : Set where
  field sub : C ∈ T 

  inj : ∀ {C T} → C ∈ T  → ∀[ ⟦ C . proj₂ ⟧con ⇒ ⟦ T ⟧ty ]
  inj (here refl) x = inj₁ x
  inj (there px)  x = inj₂ (inj px x)


open _≼_ ⦃...⦄


variable
  C C₁ C₂ : Constructor 
  T T₁ T₂ : TypeDesc 

inject : ⦃ C ≼ T ⦄ → ⟦ C .proj₂ ⟧con (Mu T) → Mu T
inject = mk ∘ inj sub 

instance ≼-here : C ≼ (C ∷ T)
≼-here .sub = here refl

instance ≼-there : ⦃ C₁ ≼ T ⦄ → C₁ ≼ (C₂ ∷ T)
≼-there .sub = there sub

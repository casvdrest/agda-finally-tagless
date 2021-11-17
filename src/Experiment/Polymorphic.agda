module Experiment.Polymorphic where

open import Data.Vec  using (Vec ; _∷_ ; [] ; lookup)
open import Data.Fin  using (Fin ; suc ; zero)
open import Data.List using (List ; _∷_ ; [])
open import Data.Nat
open import Data.Bool 
open import Data.Product 

open import Data.List.Membership.Propositional using (_∈_)

open import Relation.Binary.PropositionalEquality

open import Level renaming (suc to sucL ; zero to zeroL)

module Initial where 

  infix  4 ∀[_]
  infixr 5 _↦_
  infix  6 #_
  data Type : Set₁ where
    ∀[_] : (Set → Type) → Type
    _↦_  : Type → Type → Type
    #_   : Set → Type 

  Val : Type → Set₁
  Val ∀[ t ]  = (a : Set) → Val (t a)
  Val (s ↦ t) = Val s → Val t
  Val (# a)   = Lift _ a


  {- Expressions -} 

  data Expr : (t : Type) → Set₁ where
  
    val  :  ∀ {a}
            → a
              ----------
            → Expr (# a) 

    lam  :  ∀ {s t}
            → (Val s → Expr t)
              ----------------
            → Expr (s ↦ t)

    _·_  :  ∀ {s t}
            → Expr (s ↦ t) → Expr s
              ---------------------
            → Expr t

    ⟨_⟩ :   ∀ {f}
            → Expr ∀[ f ] → {a : Set}
              -----------------------
            → Expr (f a)

    Λ_    : ∀ {f}
            → ({a : Set} → Expr (f a))
              ------------------------
            → Expr ∀[ f ]

    letin : ∀ {t}
            → (s : Type) → Expr s → (Val s → Expr t)
              --------------------------------------
            → Expr t


  let-syntax : ∀ {t} → (s : Type) → Expr s → (Val s → Expr t) → Expr t 
  let-syntax = letin
  
  syntax let-syntax s e₁ e₂ = use e₁ ∶ s as e₂

  eval : ∀ {t} → Expr t → Val t
  eval (lam e)   = λ x → eval (e x)
  eval (val x)   = lift x
  eval (⟨ ef ⟩)  = eval ef _
  eval (ef · ex) = eval ef (eval ex)
  eval (Λ f)     = λ a → eval (f {a})
  eval (letin _ e₁ e₂) = eval (e₂ (eval e₁))


  {- A few sample expressions -} 

  -- Polymorphic identity function
  id : Expr ∀[ (λ a → # a ↦ # a ) ]
  id = Λ lam λ x → val (x .lower)

  ttt = ⟨ id ⟩ · val true
  zzz = ⟨ id ⟩ · val 0


  foo : Expr (# (ℕ × Bool))
  foo =
    use
      (Λ lam λ x → val (x . lower)) ∶ ∀[ (λ a → # a ↦ # a ) ]
    as λ id →
     use
       val (id _ (lift true) .lower) ∶ # Bool
     as λ tt →
      use
       val (id _ (lift 10) .lower) ∶ # ℕ
     as λ ten →
      val (ten .lower , tt .lower) 


  {- Sanity check -}

  test₀ : eval ttt .lower ≡ true
  test₀ = refl

  test₁ : eval zzz .lower ≡ 0
  test₁ = refl 

  test₂ : eval foo .lower ≡ (10 , true)
  test₂ = refl

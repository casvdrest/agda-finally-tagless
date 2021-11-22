{-# OPTIONS --overlapping-instances #-}
module Experiment.DeBruijn where 

open import Experiment.ListSyntax

import Data.Bool    as B 
import Data.Nat     as N 
open import Data.Product renaming (_×_ to _P×_ ; _,_ to _∙_)
import Data.Sum     as S 
import Data.List    as L

open import Data.String

open import Relation.Unary using (IUniversal)

module Initial where 
  data Type : Set where
    nat : Type
    _↦_ : (s t : Type) → Type

  Ctx : Set
  Ctx = L.List (String P× Type)

  data _∶_∈_ (x : String) (t : Type) : Ctx → Set where
    here  : ∀ {Γ} → x ∶ t ∈ ((x ∙ t) L.∷ Γ)
    there : ∀ {Γ y s} → x ∶ t ∈ Γ → x ∶ t ∈ ((y ∙ s) L.∷ Γ) 

  instance ∈-here : ∀ {Γ x t} → x ∶ t ∈ ((x ∙ t) L.∷ Γ)
  ∈-here = here

  instance ∈-there : ∀ {Γ x y s t} → ⦃ _ : x ∶ t ∈ Γ ⦄ → x ∶ t ∈ ((y ∙ s) L.∷ Γ)
  ∈-there ⦃ w ⦄ = there w

  infixl 5 _·_
  infix  6 ƛ_⇒_
  infix  7 `_
  data Term (Γ : Ctx) : Type → Set where
    `_   : ∀ {t} → (x : String) → ⦃ _ : (x ∶ t ∈ Γ) ⦄ → Term Γ t  
    ƛ_⇒_ : ∀ {s t} → (x : String) → Term ((x ∙ s) L.∷ Γ) t → Term Γ (s ↦ t)
    _·_  : ∀ {s t} → Term Γ (s ↦ t) → Term Γ s → Term Γ t
    nlit : N.ℕ → Term Γ nat 

  Val : Type → Set
  Val nat = N.ℕ
  Val (s ↦ t) = Val s → Val t

  data Env : Ctx → Set where
    []  : Env L.[] 
    _∷_ : ∀ {Γ} {subst : String P× Type} → Val (proj₂ subst) → Env Γ → Env (subst L.∷ Γ) 

  lookup : ∀ {x t Γ} → x ∶ t ∈ Γ → Env Γ → Val t
  lookup here      (v ∷ _)  = v
  lookup (there l) (_ ∷ nv) = lookup l nv

  eval : ∀ {Γ t} → Term Γ t → Env Γ → Val t
  eval (`_ x ⦃ l ⦄) nv = lookup l nv
  eval (ƛ x ⇒ e) nv = λ v → eval e (v ∷ nv)
  eval (e₁ · e₂) nv = eval e₁ nv (eval e₂ nv)
  eval (nlit x) nv = x

  term₁ : Term L.[] nat
  term₁ = ƛ "x" ⇒ ` "x" · nlit 10
  
  term₂ : Term L.[] nat
  term₂ = ƛ "f" ⇒ (ƛ "n" ⇒ (` "f" · ` "n")) · ƛ "x" ⇒ ` "x" · nlit 10

  term₃ : Term L.[] nat
  term₃ = ƛ "x" ⇒ (ƛ "y" ⇒ ` "x") · nlit 11 · nlit 10


module Final where 

  variable a b c T : Set 

  record FunTy (T : Set) : Set where
    field
      _↦_ : T → T → T

  open FunTy ⦃...⦄
  
  record BoolTy (T : Set) : Set where
    field
      bool : T

  open BoolTy ⦃...⦄

  
  record NatTy (T : Set) : Set where
    field
      nat : T
  
  open NatTy ⦃...⦄
  
  record ProdTy (T : Set) : Set where
    field
      _×_ : T → T → T 
  
  open ProdTy ⦃...⦄
  
  record SumTy (T : Set) : Set where
    field
      _⊎_ : T → T → T 
  
  open SumTy ⦃...⦄

  Ctx : Set → Set
  Ctx T = L.List (String P× T)
  
  data _∶_∈_ {T} (x : String) (t : T) : Ctx T → Set where
    here  : ∀ {Γ} → x ∶ t ∈ ((x ∙ t) L.∷ Γ)
    there : ∀ {Γ y s} → x ∶ t ∈ Γ → x ∶ t ∈ ((y ∙ s) L.∷ Γ) 

  instance ∈-here : ∀ {T} {Γ x} {t : T} → x ∶ t ∈ ((x ∙ t) L.∷ Γ)
  ∈-here = here

  instance ∈-there : ∀ {T} {Γ x y s} {t : T} → ⦃ _ : x ∶ t ∈ Γ ⦄ → x ∶ t ∈ ((y ∙ s) L.∷ Γ)
  ∈-there ⦃ w ⦄ = there w

  record Lambda {T} ⦃ _ : FunTy T ⦄ (ρ : Ctx T → T → Set) : Set where
    infixl 9 _·_
    infix  2 ƛ_⇒_
    infix  10 `_
    field
      ƛ_⇒_ : ∀ {Γ s t} → (x : String) → ρ ((x ∙ s) L.∷ Γ) t → ρ Γ (s ↦ t) 
      _·_  : ∀ {Γ s t} → ρ Γ (s ↦ t) → ρ Γ s → ρ Γ t
      `_   : ∀ {Γ t}   → (x : String) → ⦃ x ∶ t ∈ Γ ⦄ → ρ Γ t

  record Let {T} ⦃ _ : FunTy T ⦄ (ρ : Ctx T → T → Set) : Set where
    infix 1 lett_∷=_inn_
    field
      lett_∷=_inn_ : ∀ {Γ s t} → (x : String) → ρ Γ s → ρ ((x ∙ s) L.∷ Γ) t → ρ Γ t 

  record Boolean {T} ⦃ _ : BoolTy T ⦄ (ρ : Ctx T → T → Set) : Set where
    infix 1 ¬_
    infix 4 _∧_
    infix 3 _∨_
    field
      blit : ∀ {Γ} → B.Bool → ρ Γ bool
      ¬_   : ∀ {Γ} → ρ Γ bool → ρ Γ bool
      _∧_  : ∀ {Γ} → ρ Γ bool → ρ Γ bool → ρ Γ bool 
      _∨_  : ∀ {Γ} → ρ Γ bool → ρ Γ bool → ρ Γ bool
  
  record Nats {T} ⦃ _ : NatTy T ⦄ (ρ : Ctx T → T → Set) : Set where
    infix 4 _*_
    infix 3 _+_
    field
      nlit : ∀ {Γ} → N.ℕ → ρ Γ nat  
      _+_  : ∀ {Γ} → ρ Γ nat → ρ Γ nat → ρ Γ nat
      _*_  : ∀ {Γ} → ρ Γ nat → ρ Γ nat → ρ Γ nat

  record NatElim {T} ⦃ _ : NatTy T ⦄ (ρ : Ctx T → T → Set) : Set where
    infix 1 ncase_of⟨Z⇒_⟩⟨S_⇒_⟩
    field
      ncase_of⟨Z⇒_⟩⟨S_⇒_⟩ : ∀ {Γ t} → ρ Γ nat → ρ Γ t → (x : String) → ρ ((x ∙ nat) L.∷ Γ) t → ρ Γ t 
  
  record Ord {T} ⦃ _ : NatTy T ⦄ ⦃ _ : BoolTy T ⦄ (ρ : Ctx T → T → Set) : Set where
    infix 2 _≤_
    field
      _≤_ : ∀ {Γ} → ρ Γ  nat → ρ Γ nat → ρ Γ bool
  
  record Cond {T} ⦃ _ : BoolTy T ⦄ (ρ : Ctx T → T → Set) : Set where
    infix 1 if_then_else_
    field
      if_then_else_ : ∀ {Γ t} → ρ Γ bool → ρ Γ t → ρ Γ t → ρ Γ t
  
  record Product {T} ⦃ _ : ProdTy T ⦄ (ρ : Ctx T → T → Set) : Set where
    infix 2 _,_
    field
      _,_ : ∀ {Γ s t} → ρ Γ s → ρ Γ t → ρ Γ (s × t)
      fst : ∀ {Γ s t} → ρ Γ (s × t) → ρ Γ s
      snd : ∀ {Γ s t} → ρ Γ (s × t) → ρ Γ t
  
  record Sum {T} ⦃ _ : SumTy T ⦄ (ρ : Ctx T → T → Set) : Set where
    field
      inl   : ∀ {Γ s t} → ρ Γ s → ρ Γ (s ⊎ t)
      inr   : ∀ {Γ s t} → ρ Γ t → ρ Γ (s ⊎ t)
  
  record SumElim {T} ⦃ _ : SumTy T ⦄ ⦃ _ : FunTy T ⦄ (ρ : Ctx T → T → Set) : Set where
    infix 1 [_,_]
    field
      [_,_] : ∀ {Γ s t u} → ρ Γ (s ↦ u) → ρ Γ (t ↦ u) → ρ Γ ((s ⊎ t) ↦ u)
  
  record Fix {T} ⦃ _ : FunTy T ⦄ (ρ : Ctx T → T → Set) : Set where
    field
      μ_,_⇒_ : ∀ {Γ s t} → (f x : String) → ρ ((x ∙ s) L.∷ (f ∙ (s ↦ t)) L.∷ Γ) t → ρ Γ (s ↦ t)
  
  open Lambda  ⦃...⦄
  open Let     ⦃...⦄ 
  open Boolean ⦃...⦄
  open Nats    ⦃...⦄
  open NatElim ⦃...⦄
  open Ord     ⦃...⦄
  open Cond    ⦃...⦄
  open Product ⦃...⦄
  open Sum     ⦃...⦄
  open SumElim ⦃...⦄
  open Fix     ⦃...⦄
  
  Term : {T : Set} → (cs : L.List ((Ctx T → T → Set) → Set)) → Ctx T → T → (Ctx T → T → Set) → Set
  Term cs Γ t ρ = L.foldr (λ C a → ⦃ _ : C ρ ⦄ → a) (ρ Γ t) cs

  ∅ : ∀[ Ctx ]
  ∅ = L.[]
  
  {- Some terms -}
  
  term₁ : ⦃ _ : FunTy T ⦄ ⦃ _ : BoolTy T ⦄
        → ∀[ Term [ Lambda ∙ Boolean ] ∅ bool ] 
  term₁ =
    (ƛ "x" ⇒ ` "x") · blit B.false
  
  term₂ : ⦃ _ : BoolTy T ⦄ ⦃ _ : NatTy T ⦄ ⦃ _ : FunTy T ⦄
        → ∀[ Term [ Boolean ∙ Ord ∙ Nats ∙ Lambda ] ∅ bool ]
  term₂ =
    ¬ nlit 10 ≤ (ƛ "x" ⇒ ` "x" * ` "x") · nlit 3
  
  term₃ : ⦃ _ : FunTy T ⦄ ⦃ _ : BoolTy T ⦄ ⦃ _ : NatTy T ⦄
        → ∀[ Term [ Lambda ∙ Ord ∙ Cond ∙ Nats ] ∅ nat ]
  term₃ =
    if
      nlit 1 + nlit 2 ≤ nlit 3
    then
      (ƛ "x" ⇒ ` "x" + ` "x") · nlit 3
    else
      nlit 0

  term₄ : ⦃ _ : FunTy T ⦄ ⦃ _ : NatTy T ⦄
        → ∀[ Term [ Lambda ∙ Let ∙ Nats ∙ NatElim ∙ Fix ] ∅ nat ]
  term₄ =
    lett
      "factorial" ∷=
        μ "rec" , "n" ⇒
          ncase ` "n"
            of⟨Z⇒
              nlit 1
            ⟩⟨S "k" ⇒
              ` "n" * (` "rec" · ` "k")
            ⟩
    inn
      ` "factorial" · nlit 6
  
  -- {- Interpreter -}
  
  data Type : Set where
    `nat `bool : Type
    _`↦_ _`×_ _`⊎_ : Type → Type → Type 
  
  Val : Type → Set
  Val `nat = N.ℕ
  Val `bool = B.Bool
  Val (s `↦ t) = Val s → Val t
  Val (s `× t) = Val s P× Val t
  Val (s `⊎ t) = Val s S.⊎ Val t

  data Env : Ctx Type → Set where
    []  : Env L.[] 
    _∷_ : ∀ {Γ} {subst : String P× Type} → Val (proj₂ subst) → Env Γ → Env (subst L.∷ Γ) 

  lookup : ∀ {x t Γ} → x ∶ t ∈ Γ → Env Γ → Val t
  lookup here      (v ∷ _)  = v
  lookup (there l) (_ ∷ nv) = lookup l nv

  Interp : Ctx Type → Type → Set
  Interp Γ t = Env Γ → Val t

  instance type-fun : FunTy Type
  type-fun ._↦_ = _`↦_
  
  instance type-nat : NatTy Type
  type-nat .nat = `nat
  
  instance type-bool : BoolTy Type
  type-bool .bool = `bool
  
  instance type-product : ProdTy Type
  type-product ._×_ = _`×_
  
  instance type-sum : SumTy Type
  type-sum ._⊎_ = _`⊎_
  
  instance eval-lambda : Lambda Interp
  eval-lambda .ƛ_⇒_ = λ _ f nv x   → f (x ∷ nv) 
  eval-lambda ._·_  = λ f x nv     → f nv (x nv)
  eval-lambda .`_   = λ _ ⦃ x ⦄ nv → lookup x nv

  instance eval-let : Let Interp
  eval-let .lett_∷=_inn_ = λ x e₁ e₂ nv → e₂ (e₁ nv ∷ nv)

  import Function
  ↑₀ = Function.const

  ↑₁ : ∀ {A B C : Set} → (A → B) → (C → A) → (C → B)
  ↑₁ h f x = h (f x)

  ↑₂ : ∀ {A B C D : Set} → (A → B → C) → (D → A) → (D → B) → D → C
  ↑₂ h f g x = h (f x) (g x)

  ↑₃ : ∀ {A B C D E : Set} → (A → B → C → D) → (E → A) → (E → B) → (E → C) → E → D
  ↑₃ h f g g' x = h (f x) (g x) (g' x)
  
  instance eval-boolean : Boolean Interp
  eval-boolean .blit = ↑₀ 
  eval-boolean .¬_   = ↑₁ B.not
  eval-boolean ._∧_  = ↑₂ B._∧_
  eval-boolean ._∨_  = ↑₂ B._∨_

  instance eval-nats : Nats Interp
  eval-nats .nlit = ↑₀ 
  eval-nats ._+_  = ↑₂ N._+_
  eval-nats ._*_  = ↑₂ N._*_

  instance eval-ncase : NatElim Interp
  eval-ncase .ncase_of⟨Z⇒_⟩⟨S_⇒_⟩
    = λ n z _ s nv → Function.case n nv of λ { N.zero → z nv ; (N.suc k) → s (k ∷ nv) }

  instance eval-ord : Ord Interp
  eval-ord ._≤_ = ↑₂ λ n m → B.not (m N.<ᵇ n)
  
  instance eval-cond : Cond Interp
  eval-cond .if_then_else_ = ↑₃ B.if_then_else_
  
  instance eval-prod : Product Interp
  eval-prod ._,_ = ↑₂ _∙_
  eval-prod .fst = ↑₁ proj₁
  eval-prod .snd = ↑₁ proj₂
  
  instance eval-sum : Sum Interp
  eval-sum .inl = ↑₁ S.inj₁
  eval-sum .inr = ↑₁ S.inj₂
  
  instance eval-sum-elim : SumElim Interp
  eval-sum-elim .[_,_] = ↑₂ S.[_,_]
  
  {-# TERMINATING #-} -- nope
  fix' : ∀ {A B : Set} → ((A → B) → A → B) → A → B
  fix' f = f (fix' f)
  
  instance eval-fix : Fix Interp
  eval-fix .μ_,_⇒_ = λ _ x e nv → fix' λ f v → e (v ∷ (f ∷ nv))
  
  term₁-eval : B.Bool
  term₁-eval = term₁ []
  
  term₂-eval : B.Bool
  term₂-eval = term₂ []
  
  term₃-eval : N.ℕ
  term₃-eval = term₃ []

  term₄-eval : N.ℕ
  term₄-eval = term₄ []
  
  {- Pretty printing -}
  
  open import Data.String
  open import Agda.Builtin.String renaming (primShowNat to showℕ)
  
  PP : Ctx T → T → Set
  PP _ _ = String
  
  showB : B.Bool → String
  showB B.true  = "true"
  showB B.false = "false"
  
  instance pp-lambda : Lambda PP
  pp-lambda .ƛ_⇒_ = λ x f → "(λ" ++ x  ++ " → " ++ f ++ ")"  
  pp-lambda ._·_  = λ f x → f ++ " " ++ x
  pp-lambda .`_   = λ x → x 
  
  instance pp-boolean : Boolean PP
  pp-boolean .blit = λ x → showB x
  pp-boolean .¬_   = λ x → "¬ " ++ x
  pp-boolean ._∧_  = λ x y → x ++ " ∧ " ++ y
  pp-boolean ._∨_  = λ x y → x ++ " ∨ " ++ y
  
  instance pp-nats : Nats PP
  pp-nats .nlit = λ n → showℕ n
  pp-nats ._+_ = λ x y → x ++ " + " ++ y
  pp-nats ._*_ = λ x y → x ++ " * " ++ y
  
  instance pp-ord : Ord PP
  pp-ord ._≤_ = λ x y → x ++ " ≤ " ++ y
  
  instance pp-cond : Cond PP
  pp-cond .if_then_else_ = λ c t e → "if " ++ c ++ " then " ++ t ++ " else " ++ e 
  
  instance pp-prod : Product PP
  pp-prod ._,_ = λ x y → x ++ " , " ++ y 
  pp-prod .fst = λ x → "fst " ++ x 
  pp-prod .snd = λ y → "snd " ++ y
  
  instance pp-sum : Sum PP
  pp-sum .inl = λ x → "inl " ++ x 
  pp-sum .inr = λ x → "inr " ++ x
  
  instance pp-sum-elim : SumElim PP
  pp-sum-elim .[_,_] = λ l r → "[ " ++ l ++ " , " ++ r ++ "]" 
  
  variable s t u : T
  
  term₁-pp : String
  term₁-pp = term₁
  
  term₂-pp : String
  term₂-pp = term₂
  
  term₃-pp : String
  term₃-pp = term₃
  

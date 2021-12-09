{-# OPTIONS --overlapping-instances #-}
module Experiment.Fragment where 

open import Experiment.ListSyntax

import Data.Bool    as B 
import Data.Nat     as N 
open import Data.Product renaming (_×_ to _P×_ )
import Data.Sum     as S 
import Data.List    as L
open import Data.Unit using (⊤ ; tt)
open import Data.String

import Relation.Binary.PropositionalEquality as P
open import Relation.Unary using (IUniversal ; _⇒_)

open import Function
open import Level

open import Experiment.Desc

module Final where 

  variable a b c : Set 

  {- Various types -} 

  NatT : Constructor
  NatT = "nat" , `1

  nat : ∀ {T} → ⦃ _ : NatT ≼ T ⦄ → Mu T
  nat = inject tt 

  BoolT : Constructor
  BoolT = "bool" , `1

  bool : ∀ {T} → ⦃ BoolT ≼ T ⦄ → Mu T
  bool = inject tt

  FunT : Constructor
  FunT = "fun" , `var `× `var

  _↦_ : ∀ {T} → ⦃ FunT ≼ T ⦄ → Mu T → Mu T → Mu T
  s ↦ t = inject (s , t)

  ProdT : Constructor
  ProdT = "product" , `var `× `var

  _×_ : ∀ {T} → ⦃ ProdT ≼ T ⦄ → Mu T → Mu T → Mu T
  s × t = inject (s , t)

  SumT : Constructor
  SumT = "sum" , `var `× `var

  _⊎_ : ∀ {T} → ⦃ SumT ≼ T ⦄ → Mu T → Mu T → Mu T
  s ⊎ t = inject (s , t)
  
  {- Contexts & instance search for typed De Bruijn -} 

  Ctx : Set → Set
  Ctx T = L.List (String P× T)
  
  data _∶_∈_ {T} (x : String) (t : T) : Ctx T → Set where
    here  : ∀ {Γ} → x ∶ t ∈ ((x , t) L.∷ Γ)
    there : ∀ {Γ y s} → x ∶ t ∈ Γ → x ∶ t ∈ ((y , s) L.∷ Γ) 

  instance ∈-here : ∀ {T} {Γ x} {t : T} → x ∶ t ∈ ((x , t) L.∷ Γ)
  ∈-here = here

  instance ∈-there : ∀ {T} {Γ x y s} {t : T} → ⦃ _ : x ∶ t ∈ Γ ⦄ → x ∶ t ∈ ((y , s) L.∷ Γ)
  ∈-there ⦃ w ⦄ = there w

  Repr : TypeDesc → Set₁
  Repr T = Ctx (Mu T) → Mu T → Set 


  {- Language Fragments -}

  constrain : TypeDesc →  L.List Constructor → Set₁ → Set₁
  constrain T L.[] A = A
  constrain T (C L.∷ types) A = ⦃ C ≼ T ⦄ → constrain T types A

  record Fragment (types : L.List Constructor) : Set₁ where
    field sem : {T : TypeDesc} → constrain T types ((ρ : Repr T) → Set)  

  open Fragment


  {- λ-abstraction, application, and variables -} 

  record Lambda {T} ⦃ _ : FunT ≼ T ⦄ (ρ : Repr T) : Set where
    infixl 9 _·_
    infix  2 ƛ_⇒_
    infix  10 `_
    field
      ƛ_⇒_ : ∀ {Γ s t} → (x : String) → ρ ((x , s) L.∷ Γ) t → ρ Γ (s ↦ t) 
      _·_  : ∀ {Γ s t} → ρ Γ (s ↦ t) → ρ Γ s → ρ Γ t
      `_   : ∀ {Γ t}   → (x : String) → ⦃ x ∶ t ∈ Γ ⦄ → ρ Γ t

  LambdaF : Fragment [ FunT ]
  LambdaF .sem = Lambda


  {- Let-binding -} 

  record Let {T} ⦃ _ : FunT ≼ T ⦄ (ρ : Repr T) : Set where
    infix 1 lett_∷=_inn_
    field
      lett_∷=_inn_ : ∀ {Γ s t} → (x : String) → ρ Γ s → ρ ((x , s) L.∷ Γ) t → ρ Γ t 

  LetF : Fragment [ FunT ]
  LetF .sem = Let


  {- Boolean expressions -} 

  record Boolean {T} ⦃ _ : BoolT ≼ T ⦄ (ρ : Repr T) : Set where
    infix 1 ¬_
    infix 4 _∧_
    infix 3 _∨_
    field
      blit : ∀ {Γ} → B.Bool → ρ Γ bool
      ¬_   : ∀ {Γ} → ρ Γ bool → ρ Γ bool
      _∧_  : ∀ {Γ} → ρ Γ bool → ρ Γ bool → ρ Γ bool 
      _∨_  : ∀ {Γ} → ρ Γ bool → ρ Γ bool → ρ Γ bool

  BoolF : Fragment [ BoolT ]
  BoolF .sem = Boolean
  

  {- Natural number expressions -} 

  record Nats {T} ⦃ _ : NatT ≼ T ⦄ (ρ : Repr T) : Set where
    infix 4 _*_
    infix 3 _+_
    field
      nlit : ∀ {Γ} → N.ℕ → ρ Γ nat  
      _+_  : ∀ {Γ} → ρ Γ nat → ρ Γ nat → ρ Γ nat
      _*_  : ∀ {Γ} → ρ Γ nat → ρ Γ nat → ρ Γ nat

  NatsF : Fragment [ NatT ]
  NatsF .sem = Nats
  

  {- NatCase  -} 
  
  record NatElim {T} ⦃ _ : NatT ≼ T ⦄ (ρ : Repr T) : Set where
    infix 1 ncase_of⟨Z⇒_⟩⟨S_⇒_⟩
    field
      ncase_of⟨Z⇒_⟩⟨S_⇒_⟩ : ∀ {Γ t} → ρ Γ nat → ρ Γ t → (x : String) → ρ ((x , nat) L.∷ Γ) t → ρ Γ t 

  NCaseF : Fragment [ NatT ]
  NCaseF .sem = NatElim


  {- LEQ for natural numbers -} 

  record Ord {T} ⦃ _ : NatT ≼ T ⦄ ⦃ _ : BoolT ≼ T ⦄ (ρ : Repr T) : Set where
    infix 2 _≤_
    field
      _≤_ : ∀ {Γ} → ρ Γ nat → ρ Γ nat → ρ Γ bool 

  OrdF : Fragment [ NatT , BoolT ]
  OrdF .sem = Ord


  {- Conditionals -} 

  record Cond {T} ⦃ _ : BoolT ≼ T ⦄ (ρ : Repr T) : Set where
    infix 1 if_then_else_
    field
      if_then_else_ : ∀ {Γ t} → ρ Γ bool → ρ Γ t → ρ Γ t → ρ Γ t

  CondF : Fragment [ BoolT ]
  CondF .sem = Cond


  {- Product types -}

  record Product {T} ⦃ _ : ProdT ≼ T ⦄ (ρ : Repr T) : Set where
    infix 2 _,,_
    field
      _,,_ : ∀ {Γ s t} → ρ Γ s → ρ Γ t → ρ Γ (s × t)
      fst : ∀ {Γ s t} → ρ Γ (s × t) → ρ Γ s
      snd : ∀ {Γ s t} → ρ Γ (s × t) → ρ Γ t

  ProductF : Fragment [ ProdT ]
  ProductF .sem = Product


  {- Sum Types -} 

  record Sum {T} ⦃ _ : SumT ≼ T ⦄ (ρ : Repr T) : Set where
    field
      inl   : ∀ {Γ s t} → ρ Γ s → ρ Γ (s ⊎ t)
      inr   : ∀ {Γ s t} → ρ Γ t → ρ Γ (s ⊎ t)

  SumF : Fragment [ SumT ]
  SumF .sem = Sum
  

  {- Sum elimination (either) -} 

  record SumElim {T} ⦃ _ : SumT ≼ T ⦄ ⦃ _ : FunT ≼ T ⦄ (ρ : Repr T) : Set where
    infix 1 ⟪_,_⟫
    field
      ⟪_,_⟫ : ∀ {Γ s t u} → ρ Γ (s ↦ u) → ρ Γ (t ↦ u) → ρ Γ ((s ⊎ t) ↦ u)

  SumElimF : Fragment [ SumT , FunT ]
  SumElimF .sem = SumElim
  

  {- Recursive functions -} 

  record Fix {T} ⦃ _ : FunT ≼ T ⦄ (ρ : Repr T) : Set where
    field
      μ_,_⇒_ : ∀ {Γ s t} → (f x : String) → ρ ((x , s) L.∷ (f , (s ↦ t)) L.∷ Γ) t → ρ Γ (s ↦ t)

  FixF : Fragment [ FunT ]
  FixF .sem = Fix

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


  {- Language composition -}

  -- When composing two languaegs, it may be that they impose different
  -- constraints on the set of types.  We use witnesses of a proof-relevant
  -- ternary relation on lists (supplied by the user) to mediate the constraints
  -- of different languages.

  -- First, bring in some dependencies from ternary.agda and stdlib

  open import Relation.Ternary.Core 
  open Rel₃ ⦃...⦄ hiding (_≤_)

  open import Data.These 
  
  open import Data.List.Membership.Propositional
  open import Data.List.Membership.Propositional.Properties
  open import Data.List.Relation.Unary.Any hiding (lookup)
  open import Data.List.Relation.Unary.All 

  infixr 9 _⋈_
  _⋈_ : ∀ {a ℓ} {A : Set a} → (P Q : A → Set ℓ) → A → Set ℓ
  (P ⋈ Q) x = These (P x) (Q x)

  -- List unions, as a ternary relation
  --
  -- Read as: zs is a union of xs and ys, iff:
  -- - every element of xs is in zs
  -- - every element of ys is in zs
  -- - every element of zs is either in xs, in ys, or in both.
  -- 
  record ListUnion {ℓ} {A : Set ℓ} (xs ys zs : L.List A) : Set ℓ where
    field
      inj-xs  : ∀[ Member xs ⇒ Member zs ]
      inj-ys  : ∀[ Member ys ⇒ Member zs ]

      from-zs : ∀[ Member zs ⇒ Member xs ⋈ Member ys ]

      -- TODO: inverse laws? e.g. from-zs ∘ inj-xs ≈ id

  open ListUnion

  instance list-rel : ∀ {ℓ} {A : Set ℓ} → Rel₃ (L.List A)
  Rel₃._∙_≣_ list-rel = ListUnion

  -- TODO: use defs from ternary.agda
  ∙-disjoint : ∀ {ℓ} {A : Set ℓ} {xs ys : L.List A} → xs ∙ ys ≣ (xs L.++ ys)
  inj-xs   ∙-disjoint            = ∈-++⁺ˡ
  inj-ys   ∙-disjoint            = ∈-++⁺ʳ _ 
  from-zs (∙-disjoint {xs = xs}) = S.[ this , that ] ∘ ∈-++⁻ xs

  ∙-copy : ∀ {ℓ} {A : Set ℓ} {xs : L.List A} → xs ∙ xs ≣ xs
  inj-xs  ∙-copy = id
  inj-ys  ∙-copy = id
  from-zs ∙-copy = λ x → these x x

  -- A language is just a bunch of constructs (fragments), that share a common
  -- set of constraints on their index type. 
  record Language (types : L.List Constructor) : Set₁ where
    constructor ⟪_⟫
    field constructs : L.List (Fragment types)

  open Language

  -- Strengthen the assumed type constraints of a fragment
  --
  -- Alternatively we could say that Fragment is a presheaf over the category
  -- induced by -⊆-
  fragment-mono : ∀ {xs ys} → ys ⊇ xs → Fragment xs → Fragment ys
  fragment-mono ys⊇xs f .sem = gather (discharge ys⊇xs (f .sem))

    where gather : ∀ {T A} {xs : L.List Constructor}
                   → (All (λ C → C ≼ T) xs → A)
                   → constrain T xs A 
          gather {xs = L.[]} f = f []
          gather {xs = x L.∷ xs} f ⦃ C ⦄ = gather {xs = xs} λ xs → f (C ∷ xs)

          discharge : ∀ {T A} {xs ys : L.List Constructor}
                      → ys ⊇ xs → constrain T xs A
                      → All (λ C → C ≼ T) ys → A
          discharge {xs = L.[]}     ys⊇xs ca cs = ca
          discharge {xs = C L.∷ xs} (x∈ys ∷ ys⊇xs) ca cs
            = discharge ys⊇xs (ca ⦃ lookup cs x∈ys ⦄) cs

  -- The same goes for Language
  language-mono : ∀ {xs ys} → ys ⊇ xs → Language xs → Language ys
  language-mono ys⊇xs l .constructs = L.map (fragment-mono ys⊇xs) (l .constructs)

  ⊆-fromMembership : ∀ {a} {A : Set a} {xs ys : L.List A}
                     → ∀[ Member xs ⇒ Member ys ] → xs ⊆ ys 
  ⊆-fromMembership {xs = L.[]}     f
    = []
  ⊆-fromMembership {xs = x L.∷ xs} f
    = f (here P.refl) ∷ ⊆-fromMembership {xs = xs} λ x → f (there x)

  union→⊇₁ : ∀ {a} {A : Set a} {xs ys zs : L.List A} → xs ∙ ys ≣ zs → zs ⊇ xs
  union→⊇₁ σ = ⊆-fromMembership (σ .inj-xs)

  union→⊇₂ : ∀ {a} {A : Set a} {xs ys zs : L.List A} → xs ∙ ys ≣ zs → zs ⊇ ys
  union→⊇₂ σ = ⊆-fromMembership (σ .inj-ys)

  -- Compose two languages with the same type constraints
  _⊕_ : ∀[ Language ⇒ Language ⇒ Language ]
  (l₁ ⊕ l₂) .constructs = l₁ .constructs L.++ l₂ .constructs

  -- Compose two languages with heterogeneous type constraints, using a
  -- user-supplied witness σ to mediate between the constraints of l₁ and l₂
  ⊕[_] : ∀[ Language ✴ Language ⇒ Language ]
  ⊕[ l₁ ∙⟨ σ ⟩ l₂ ] = language-mono (union→⊇₁ σ) l₁ ⊕ language-mono (union→⊇₂ σ) l₂

  -- Convenient syntax for composing anonymous languages
  infixr 1 _⊕⟨_⟩_
  _⊕⟨_⟩_ : ∀ {xs ys zs} → L.List (Fragment xs) → xs ∙ ys ≣ zs → L.List (Fragment ys) → L.List (Fragment zs)
  fs₁ ⊕⟨ σ ⟩ fs₂ = ⊕[ (λ where .constructs → fs₁) ∙⟨ σ ⟩ (λ where .constructs → fs₂) ] .constructs

  -- {- Calculate the type of terms in a language -} 

  -- Abstract over a set of type constraints 
  abstr : L.List (Set → Set) → (T : Set) → Set
  abstr L.[] T = T
  abstr (C L.∷ ts) T = C T → abstr ts T

  -- Calculate a term type for a list of semantics (sems) constrained by a list
  -- of type constraints (types)
  --
  -- We proceed by induction over the list of type constraints (types), where at
  -- every step we apply the constraint at the head of the list to every bit of
  -- semantics.
  --
  -- At the end, when there are no more type constraints left (and thus all bits
  -- of semantics are unconstrained), we return the term type, S, with instance
  -- arguments for all the elements of sems.
  TermOf : ∀ {T}
           → (types : L.List Constructor)
           → (sems : L.List (constrain T types ((ρ : Repr T) → Set)))
           → Repr T
           → (Mu T → Set)
           → Set
  TermOf {T} L.[]       fs ρ S
    = L.foldr (λ C a → ⦃ C ρ ⦄ → a) (∃ λ t → S t) fs
  TermOf {T} (C L.∷ types) fs ρ S
    = ⦃ tyC : C ≼ T ⦄ → TermOf types (L.map (λ f → f ⦃ tyC ⦄) fs) ρ S 

  mkpair : ∀ {a b} {A : Set a} {B : A → Set b} → (x : A) → (y : B x) → Σ A B
  mkpair = _,_

  infix 0 mkpair
  syntax mkpair x y = y ⦂ x  

  -- Calcuate the type of terms in a language, using TermOf
  Term : ∀ {types}
         → Language types
         → Set₁
  Term {types = types} lang 
    = ∀ {T ρ} → TermOf {T} types (L.map (λ f → f .sem) (lang .constructs)) ρ (ρ L.[])


  {- Example languages -} 

  LBool : Language [ BoolT ]
  LBool .constructs = [ BoolF , CondF ]

  LArith : Language [ NatT ]
  LArith .constructs = [ NatsF ]

  LExpr = ⊕[ LBool ∙⟨ ∙-disjoint ⟩ LArith ] 

  miniML = ⟪ [ BoolF ]                 ⊕⟨ ∙-disjoint ⟩
             [ NatsF , NCaseF ]        ⊕⟨ ∙-disjoint ⟩
             [ LambdaF , FixF , LetF ]
           ⟫ 

  {- Some Terms -} 

  term₁ : Term LBool
  term₁ = (blit B.true ∧ blit B.false)
        ⦂ bool

  term₂ : Term LArith
  term₂ = ((nlit 1 + nlit 2) * nlit 3)
        ⦂ nat 

  term₃ : Term LExpr
  term₃ = 
    if
      blit B.true ∨ blit B.false
    then
      nlit 2 * nlit 2
    else
      nlit 3 + nlit 3
    ⦂ nat

  term₄ : Term ⟪ [ LambdaF ] ⊕⟨ ∙-disjoint ⟩ [ BoolF ] ⟫
  term₄ =
    (ƛ "x" ⇒ ` "x") · blit B.false
    ⦂ bool

  term₅ : Term
        ⟪ [ LambdaF  ] ⊕⟨ ∙-disjoint ⟩
          [ OrdF     ] ⊕⟨ ∙-copy     ⟩
          [ NatsF    ] ⊕⟨ ∙-disjoint ⟩
          [ BoolF    ]
        ⟫
  term₅ = ¬ nlit 10 ≤ ((ƛ "n" ⇒ ` "n" * ` "n") · nlit 3) ⦂ bool 

  term₆ : Term ⟪ [ LambdaF ] ⊕⟨ ∙-disjoint ⟩ [ OrdF ] ⊕⟨ ∙-copy ⟩ [ NatsF ] ⊕⟨ ∙-disjoint ⟩ [ CondF ] ⟫
  term₆ =
    if
      nlit 1 + nlit 2 ≤ nlit 3
    then
      (ƛ "x" ⇒ ` "x" + ` "x") · nlit 3
    else
      nlit 0
    ⦂ nat

  term₇ : Term miniML
  term₇ =
    lett
      "factorial" ∷=
        μ "rec" , "n" ⇒
         ncase ` "n"
           of⟨Z⇒
             nlit 1
           ⟩⟨S "m" ⇒
             ` "n" * (` "rec" · ` "m")
           ⟩
    inn
      ` "factorial" · nlit 6
    ⦂ nat

  
  {- Interpreter -}

  Type : TypeDesc
  Type = [ NatT , BoolT , FunT , ProdT , SumT ]

  -- TODO: specify (modularly) as an algebra over a type description
  Val : Mu Type → Set
  Val (mk (S.inj₁ tt)) = N.ℕ
  Val (mk (S.inj₂ (S.inj₁ tt))) = B.Bool
  Val (mk (S.inj₂ (S.inj₂ (S.inj₁ (s , t))))) = Val s → Val t
  Val (mk (S.inj₂ (S.inj₂ (S.inj₂ (S.inj₁ (s , t)))))) = Val s P× Val t
  Val (mk (S.inj₂ (S.inj₂ (S.inj₂ (S.inj₂ (S.inj₁ (s , t))))))) = Val s S.⊎ Val t

  data Env : Ctx (Mu Type) → Set where
    []  : Env L.[] 
    _∷_ : ∀ {Γ} {subst : String P× Mu Type} → Val (proj₂ subst) → Env Γ → Env (subst L.∷ Γ) 

  fetch : ∀ {x t Γ} → x ∶ t ∈ Γ → Env Γ → Val t
  fetch here      (v ∷ _)  = v
  fetch (there l) (_ ∷ nv) = fetch l nv

  Interp : Ctx (Mu Type) → Mu Type → Set
  Interp Γ t = Env Γ → Val t
  
  instance eval-lambda : Lambda Interp
  eval-lambda .ƛ_⇒_ = λ _ f nv x   → f (x ∷ nv) 
  eval-lambda ._·_  = λ f x nv     → f nv (x nv)
  eval-lambda .`_   = λ _ ⦃ x ⦄ nv → fetch x nv

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
  eval-prod ._,,_ = ↑₂ _,_
  eval-prod .fst  = ↑₁ proj₁
  eval-prod .snd  = ↑₁ proj₂
  
  instance eval-sum : Sum Interp
  eval-sum .inl = ↑₁ S.inj₁
  eval-sum .inr = ↑₁ S.inj₂
  
  instance eval-sum-elim : SumElim Interp
  eval-sum-elim .⟪_,_⟫ = ↑₂ S.[_,_]
  
  {-# TERMINATING #-} -- nope
  fix' : ∀ {A B : Set} → ((A → B) → A → B) → A → B
  fix' f = f (fix' f)
  
  instance eval-fix : Fix Interp
  eval-fix .μ_,_⇒_ = λ _ x e nv → fix' λ f v → e (v ∷ (f ∷ nv))

  test₁ : proj₂ term₁ [] P.≡ B.false
  test₁ = P.refl

  test₂ : proj₂ term₂ [] P.≡ 9
  test₂ = P.refl

  test₃ : proj₂ term₃ [] P.≡ 4
  test₃ = P.refl

  test₄ : proj₂ term₄ [] P.≡ B.false
  test₄ = P.refl

  test₅ : proj₂ term₅ [] P.≡ B.true
  test₅ = P.refl

  test₆ : proj₂ term₆ [] P.≡ 6
  test₆ = P.refl

  test₇ : proj₂ term₇ [] P.≡ 720
  test₇ = P.refl

  {- Pretty printing -}
  
  open import Data.String
  open import Agda.Builtin.String renaming (primShowNat to showℕ)
  
  PP : Ctx (Mu Type) → (Mu Type) → Set
  PP _ _ = String
  
  showB : B.Bool → String
  showB B.true  = "true"
  showB B.false = "false"
  
  instance pp-lambda : Lambda PP
  pp-lambda .ƛ_⇒_ = λ x f → "(λ" ++ x  ++ " → " ++ f ++ ")"  
  pp-lambda ._·_  = λ f x → f ++ " " ++ x
  pp-lambda .`_   = λ x → x

  instance pp-let : Let PP
  Let.lett_∷=_inn_ pp-let = λ x y z → "let " ++ x ++ " ∷= " ++ y ++ " in " ++ z
  
  instance pp-boolean : Boolean PP
  pp-boolean .blit = λ x → showB x
  pp-boolean .¬_   = λ x → "¬ " ++ x
  pp-boolean ._∧_  = λ x y → x ++ " ∧ " ++ y
  pp-boolean ._∨_  = λ x y → x ++ " ∨ " ++ y
  
  instance pp-nats : Nats PP
  pp-nats .nlit = λ n → showℕ n
  pp-nats ._+_ = λ x y → x ++ " + " ++ y
  pp-nats ._*_ = λ x y → x ++ " * " ++ y

  instance pp-ncase : NatElim PP
  NatElim.ncase_of⟨Z⇒_⟩⟨S_⇒_⟩ pp-ncase = λ n z k s → "ncase " ++ n ++ " of ⟨Z⇒ " ++ z ++ " ⟩⟨S " ++ k ++ " ⇒ " ++ s ++ "⟩"

  instance pp-ord : Ord PP
  pp-ord ._≤_ = λ x y → x ++ " ≤ " ++ y
  
  instance pp-cond : Cond PP
  pp-cond .if_then_else_ = λ c t e → "if " ++ c ++ " then " ++ t ++ " else " ++ e 
  
  instance pp-prod : Product PP
  pp-prod ._,,_ = λ x y → x ++ " , " ++ y 
  pp-prod .fst = λ x → "fst " ++ x 
  pp-prod .snd = λ y → "snd " ++ y
  
  instance pp-sum : Sum PP
  pp-sum .inl = λ x → "inl " ++ x 
  pp-sum .inr = λ x → "inr " ++ x
  
  instance pp-sum-elim : SumElim PP
  pp-sum-elim .⟪_,_⟫ = λ l r → "[ " ++ l ++ " , " ++ r ++ "]"

  instance pp-fix : Fix PP
  pp-fix .μ_,_⇒_  = λ rec x f → "μ " ++ rec ++ " " ++ x ++ " → " ++ f 
  
  test₈ : proj₂ term₁ P.≡ "true ∧ false"
  test₈ = P.refl

  test₉ : proj₂ term₂ P.≡ "1 + 2 * 3"
  test₉ = P.refl

  test₁₀ : proj₂ term₃ P.≡ "if true ∨ false then 2 * 2 else 3 + 3"
  test₁₀ = P.refl

  test₁₁ : proj₂ term₄ P.≡ "(λx → x) false"
  test₁₁ = P.refl

  test₁₂ : proj₂ term₅ P.≡ "¬ 10 ≤ (λn → n * n) 3"
  test₁₂ = P.refl

  test₁₃ : proj₂ term₆ P.≡ "if 1 + 2 ≤ 3 then (λx → x + x) 3 else 0"
  test₁₃ = P.refl

  test₁₄ : proj₂ term₇ P.≡ "let factorial ∷= μ rec n → ncase n of ⟨Z⇒ 1 ⟩⟨S m ⇒ n * rec m⟩ in factorial 6"
  test₁₄ = P.refl 
  

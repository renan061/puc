\begin{code}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.String.Unsafe using (_≟_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_)
open import Algebra.Structures using (IsMonoid)
open import Level using (Level)
open import Relation.Unary using (Decidable)
open import plfa.Relations using (_<_; z<s; s<s)
open import plfa.Isomorphism using (_≃_; ≃-sym; ≃-trans; _≲_; extensionality)
open plfa.Isomorphism.≃-Reasoning
open import plfa.Lists using (List; []; _∷_; [_]; [_,_]; [_,_,_]; [_,_,_,_];
  _++_; reverse; map; foldr; sum; All; Any; here; there; _∈_)
open import plfa.Lambda hiding (ƛ′_⇒_; case′_[zero⇒_|suc_⇒_]; μ′_⇒_; plus′)
open import plfa.Properties hiding (value?; unstuck; preserves; wttdgs)

--------------------------------------------------------------------------------
--
-- Lambda
-- 
--------------------------------------------------------------------------------

-- exercise [mul] (recommended)

-- write out the definition of a lambda term that multiplies two natural numbers

mul : Term
mul = μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒ case ` "m"
  [zero⇒ `zero
  |suc "m" ⇒ plus · ` "n" · (` "*" · ` "m" · ` "n")
  ]

--------------------------------------------------------------------------------

-- exercise [primed] (stretch)

-- we can make examples with lambda terms slightly easier
-- to write by adding the following definitions

ƛ′_⇒_ : Term → Term → Term
ƛ′ (` x) ⇒ N = ƛ x ⇒ N
ƛ′ _ ⇒ _     = ⊥-elim impossible
  where postulate impossible : ⊥

case′_[zero⇒_|suc_⇒_] : Term → Term → Term → Term → Term
case′ L [zero⇒ M |suc (` x) ⇒ N ] = case L [zero⇒ M |suc x ⇒ N ]
case′ _ [zero⇒ _ |suc _ ⇒ _ ]     = ⊥-elim impossible
  where postulate impossible : ⊥

μ′_⇒_ : Term → Term → Term
μ′ (` x) ⇒ N = μ x ⇒ N
μ′ _ ⇒ _     = ⊥-elim impossible
  where postulate impossible : ⊥

-- the definition of plus can now be written as follows

plus′ : Term
plus′ = μ′ + ⇒ ƛ′ m ⇒ ƛ′ n ⇒
  case′ m [zero⇒ n |suc m ⇒ `suc (+ · m · n) ]
  where + = ` "+"; m = ` "m"; n = ` "n"

-- write out the definition of multiplication in the same style

mul′ : Term
mul′ = μ′ * ⇒ ƛ′ m ⇒ ƛ′ n ⇒
  case′ m [zero⇒ `zero |suc m ⇒ plus′ · n · (* · m · n)]
  where * = ` "*"; m = ` "m"; n = ` "n"

--------------------------------------------------------------------------------

-- exercise _[_:=_]′ (stretch)

-- the definition of substitution above has three clauses (ƛ, case, and μ) that
-- invoke a with clause to deal with bound variables

-- rewrite the definition to factor the common part of these three clauses
-- into a single function, defined by mutual recursion with substitution

private
  _if_≟_else_ : Term → Id → Id → Term → Term
  A if x ≟ y else B with x ≟ y
  ... | yes _ = A
  ... | no  _ = B

  bound? : Id → Id → Term → Term → Term

_[_:=_]′ : Term → Id → Term → Term
(` x)     [ y := V ]′ = V if x ≟ y else (` x)
(ƛ x ⇒ N) [ y := V ]′ = ƛ x ⇒ bound? x y N V
(L · M)   [ y := V ]′ = L [ y := V ]′ · M [ y := V ]′
(`zero)   [ y := V ]′ = `zero
(`suc M)  [ y := V ]′ = `suc M [ y := V ]′
(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ]′ =
  case L  [ y := V ]′ [zero⇒ M [ y := V ]′ |suc x ⇒ bound? x y N V ]
(μ x ⇒ N) [ y := V ]′ = μ x ⇒ bound? x y N V

bound? x y N V = N if x ≟ y else (N [ y := V ]′)

--------------------------------------------------------------------------------

-- exercise [—↠≲—↠′]

-- show that the first notion of reflexive and transitive
-- closure above embeds into the second

private
  —↠-trans : ∀ {L M N : Term} → L —↠ M → M —↠ N → L —↠ N
  —↠-trans {L} (L ∎) L↠N = L↠N
  —↠-trans {L} (L —→⟨ L→A ⟩ A↠N) M↠N = L —→⟨ L→A ⟩ —↠-trans A↠N M↠N

—↠≲—↠′ : ∀ {M N : Term} → M —↠ N ≲ M —↠′ N
—↠≲—↠′ {M} {N} = record { to = to ; from = from ; from∘to = from∘to }
  where
    to : ∀ {M N : Term} → M —↠ N → M —↠′ N
    to (M ∎) = refl′
    to (L —→⟨ L→M ⟩ M↠N) = trans′ (step′ L→M) (to M↠N)

    from : ∀ {M N : Term} → M —↠′ N → M —↠ N
    from {M} {N} (step′ M→N) = M —→⟨ M→N ⟩ N _—↠_.∎
    from {M} refl′ = M _—↠_.∎
    from (trans′ M↠′A A↠′N) = —↠-trans (from M↠′A) (from A↠′N)

    from∘to : ∀ {M N : Term} (x : M —↠ N) → from (to x) ≡ x
    from∘to (M ∎) = refl
    from∘to (M —→⟨ M↠A ⟩ A↠N) rewrite from∘to A↠N = refl

-- why are they not isomorphic?

-- don't know

--------------------------------------------------------------------------------

-- exercise [plus-example]

-- write out the reduction sequence demonstrating that one plus one is two

private
  one = `suc `zero

_ : plus · one · one —↠ `suc `suc `zero
_ = let mˢ = "m"; nˢ = "n"; mᵛ = ` mˢ; nᵛ = ` nˢ; m+n = plus · mᵛ · nᵛ in
  plfa.Lambda.begin
    plus · one · one
  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ mˢ ⇒ ƛ nˢ ⇒ case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc m+n ]) · one · one
  —→⟨ ξ-·₁ (β-ƛ (V-suc V-zero)) ⟩
    (ƛ nˢ ⇒ case one [zero⇒ nᵛ |suc mˢ ⇒ `suc m+n ]) · one
  —→⟨ β-ƛ (V-suc V-zero) ⟩
    case one [zero⇒ one |suc mˢ ⇒ `suc (plus · mᵛ · one) ]
  —→⟨ β-suc V-zero ⟩
    `suc (plus · `zero · one)
  —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc ((ƛ mˢ ⇒ ƛ nˢ ⇒ case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc m+n ]) · `zero · one)
  —→⟨ ξ-suc (ξ-·₁ (β-ƛ V-zero)) ⟩
    `suc ((ƛ nˢ ⇒ case `zero [zero⇒ nᵛ |suc mˢ ⇒ `suc m+n ]) · one)
  —→⟨ ξ-suc (β-ƛ (V-suc V-zero)) ⟩
    `suc (case `zero [zero⇒ one |suc mˢ ⇒ `suc (plus · mᵛ · one) ])
  —→⟨ ξ-suc (β-zero) ⟩
    `suc one
  _—↠_.∎

--------------------------------------------------------------------------------

-- exercise [mul-type] (recommended)

-- using the term mul you defined earlier, write out
-- the derivation showing that it is well-typed

⊢mul : ∀ {Γ} → Γ ⊢ mul ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢mul = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` ∋m) (⊢zero) N)))
  where
    ∋m = S ("m" ≠ "n") Z
    ∋n = S ("n" ≠ "m") Z
    ∋* = S ("*" ≠ "m") (S ("*" ≠ "n") (S ("*" ≠ "m") Z))
    N  = ⊢plus · (⊢` ∋n) · ((⊢` ∋*) · ⊢` Z · (⊢` ∋n))

--------------------------------------------------------------------------------
--
-- Properties
-- 
--------------------------------------------------------------------------------

-- exercise [Progress-≃]
-- exercise [progress′]

-- skipped

--------------------------------------------------------------------------------

-- exercise [value?]

-- combine progress and —→¬V to write a program that
-- decides whether a well-typed term is a value

value? : ∀ {A M} → ∅ ⊢ M ⦂ A → Dec (Value M)
value? ⊢M with progress ⊢M
... | step M→M′ = no (—→¬V M→M′)
... | done VM = yes VM

--------------------------------------------------------------------------------

-- exercise [subst′] (stretch)

-- skipped

--------------------------------------------------------------------------------

-- exercise [mul-eval] (recommended)

-- using the evaluator, confirm that two times two is four

⊢2*2 : ∅ ⊢ (mul · two · two) ⦂ `ℕ
⊢2*2 = ⊢mul · ⊢two · ⊢two

private
  mˢ = "m"; mᵛ = ` mˢ
  nˢ = "n"; nᵛ = ` nˢ
  +ˢ = "+"; +ᵛ = ` +ˢ
  *ˢ = "*"; *ᵛ = ` *ˢ

_ : eval (gas 100) ⊢2*2 ≡
  steps
  ((μ *ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
      case mᵛ [zero⇒ `zero |suc mˢ ⇒
      (μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
         case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
         ])))
      · nᵛ
      · (*ᵛ · mᵛ · nᵛ)
      ])))
   · two
   · two
   —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
   (ƛ mˢ ⇒ (ƛ nˢ ⇒
     case mᵛ [zero⇒ `zero |suc mˢ ⇒
     (μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
        ])))
     · nᵛ
     ·
     ((μ *ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
         case mᵛ [zero⇒ `zero |suc mˢ ⇒
         (μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
            case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
            ])))
         · nᵛ
         · (*ᵛ · mᵛ · nᵛ)
         ])))
      · mᵛ
      · nᵛ)
     ]))
   · two
   · two
   —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
   (ƛ nˢ ⇒
    case two [zero⇒ `zero |suc mˢ ⇒
    (μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
       case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
       ])))
    · nᵛ
    ·
    ((μ *ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ `zero |suc mˢ ⇒
        (μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
           case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
           ])))
        · nᵛ
        · (*ᵛ · mᵛ · nᵛ)
        ])))
     · mᵛ
     · nᵛ)
    ])
   · two
   —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
   case two [zero⇒ `zero |suc mˢ ⇒
   (μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
      case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
      ])))
   · two
   ·
   ((μ *ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
       case mᵛ [zero⇒ `zero |suc mˢ ⇒
       (μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
          case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
          ])))
       · nᵛ
       · (*ᵛ · mᵛ · nᵛ)
       ])))
    · mᵛ
    · two)
   ]
   —→⟨ β-suc (V-suc V-zero) ⟩
   (μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
      case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
      ])))
   · two
   ·
   ((μ *ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
       case mᵛ [zero⇒ `zero |suc mˢ ⇒
       (μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
          case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
          ])))
       · nᵛ
       · (*ᵛ · mᵛ · nᵛ)
       ])))
    · one
    · two)
   —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
   (ƛ mˢ ⇒ (ƛ nˢ ⇒
     case mᵛ [zero⇒ nᵛ |suc mˢ ⇒
     `suc
     ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
         case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
         ])))
      · mᵛ
      · nᵛ)
     ]))
   · two
   ·
   ((μ *ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
       case mᵛ [zero⇒ `zero |suc mˢ ⇒
       (μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
          case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
          ])))
       · nᵛ
       · (*ᵛ · mᵛ · nᵛ)
       ])))
    · one
    · two)
   —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
   (ƛ nˢ ⇒
    case two [zero⇒ nᵛ |suc mˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
        ])))
     · mᵛ
     · nᵛ)
    ])
   ·
   ((μ *ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
       case mᵛ [zero⇒ `zero |suc mˢ ⇒
       (μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
          case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
          ])))
       · nᵛ
       · (*ᵛ · mᵛ · nᵛ)
       ])))
    · one
    · two)
   —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ)) ⟩
   (ƛ nˢ ⇒
    case two [zero⇒ nᵛ |suc mˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
        ])))
     · mᵛ
     · nᵛ)
    ])
   ·
   ((ƛ mˢ ⇒ (ƛ nˢ ⇒
      case mᵛ [zero⇒ `zero |suc mˢ ⇒
      (μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
         case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
         ])))
      · nᵛ
      ·
      ((μ *ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
          case mᵛ [zero⇒ `zero |suc mˢ ⇒
          (μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
             case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
             ])))
          · nᵛ
          · (*ᵛ · mᵛ · nᵛ)
          ])))
       · mᵛ
       · nᵛ)
      ]))
    · one
    · two)
   —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
   (ƛ nˢ ⇒
    case two [zero⇒ nᵛ |suc mˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
        ])))
     · mᵛ
     · nᵛ)
    ])
   ·
   ((ƛ nˢ ⇒
     case one [zero⇒ `zero |suc mˢ ⇒
     (μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
        ])))
     · nᵛ
     ·
     ((μ *ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
         case mᵛ [zero⇒ `zero |suc mˢ ⇒
         (μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
            case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
            ])))
         · nᵛ
         · (*ᵛ · mᵛ · nᵛ)
         ])))
      · mᵛ
      · nᵛ)
     ])
    · two)
   —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
   (ƛ nˢ ⇒
    case two [zero⇒ nᵛ |suc mˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
        ])))
     · mᵛ
     · nᵛ)
    ])
   ·
   case one [zero⇒ `zero |suc mˢ ⇒
   (μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
      case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
      ])))
   · two
   ·
   ((μ *ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
       case mᵛ [zero⇒ `zero |suc mˢ ⇒
       (μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
          case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
          ])))
       · nᵛ
       · (*ᵛ · mᵛ · nᵛ)
       ])))
    · mᵛ
    · two)
   ]
   —→⟨ ξ-·₂ V-ƛ (β-suc V-zero) ⟩
   (ƛ nˢ ⇒
    case two [zero⇒ nᵛ |suc mˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
        ])))
     · mᵛ
     · nᵛ)
    ])
   ·
   ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
       case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
       ])))
    · two
    ·
    ((μ *ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ `zero |suc mˢ ⇒
        (μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
           case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
           ])))
        · nᵛ
        · (*ᵛ · mᵛ · nᵛ)
        ])))
     · `zero
     · two))
   —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ)) ⟩
   (ƛ nˢ ⇒
    case two [zero⇒ nᵛ |suc mˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
        ])))
     · mᵛ
     · nᵛ)
    ])
   ·
   ((ƛ mˢ ⇒ (ƛ nˢ ⇒
      case mᵛ [zero⇒ nᵛ |suc mˢ ⇒
      `suc
      ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
          case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
          ])))
       · mᵛ
       · nᵛ)
      ]))
    · two
    ·
    ((μ *ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ `zero |suc mˢ ⇒
        (μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
           case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
           ])))
        · nᵛ
        · (*ᵛ · mᵛ · nᵛ)
        ])))
     · `zero
     · two))
   —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ (V-suc (V-suc V-zero)))) ⟩
   (ƛ nˢ ⇒
    case two [zero⇒ nᵛ |suc mˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
        ])))
     · mᵛ
     · nᵛ)
    ])
   ·
   ((ƛ nˢ ⇒
     case two [zero⇒ nᵛ |suc mˢ ⇒
     `suc
     ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
         case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
         ])))
      · mᵛ
      · nᵛ)
     ])
    ·
    ((μ *ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ `zero |suc mˢ ⇒
        (μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
           case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
           ])))
        · nᵛ
        · (*ᵛ · mᵛ · nᵛ)
        ])))
     · `zero
     · two))
   —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ))) ⟩
   (ƛ nˢ ⇒
    case two [zero⇒ nᵛ |suc mˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
        ])))
     · mᵛ
     · nᵛ)
    ])
   ·
   ((ƛ nˢ ⇒
     case two [zero⇒ nᵛ |suc mˢ ⇒
     `suc
     ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
         case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
         ])))
      · mᵛ
      · nᵛ)
     ])
    ·
    ((ƛ mˢ ⇒ (ƛ nˢ ⇒
       case mᵛ [zero⇒ `zero |suc mˢ ⇒
       (μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
          case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
          ])))
       · nᵛ
       ·
       ((μ *ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
           case mᵛ [zero⇒ `zero |suc mˢ ⇒
           (μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
              case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
              ])))
           · nᵛ
           · (*ᵛ · mᵛ · nᵛ)
           ])))
        · mᵛ
        · nᵛ)
       ]))
     · `zero
     · two))
   —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-zero))) ⟩
   (ƛ nˢ ⇒
    case two [zero⇒ nᵛ |suc mˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
        ])))
     · mᵛ
     · nᵛ)
    ])
   ·
   ((ƛ nˢ ⇒
     case two [zero⇒ nᵛ |suc mˢ ⇒
     `suc
     ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
         case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
         ])))
      · mᵛ
      · nᵛ)
     ])
    ·
    ((ƛ nˢ ⇒
      case `zero [zero⇒ `zero |suc mˢ ⇒
      (μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
         case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
         ])))
      · nᵛ
      ·
      ((μ *ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
          case mᵛ [zero⇒ `zero |suc mˢ ⇒
          (μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
             case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
             ])))
          · nᵛ
          · (*ᵛ · mᵛ · nᵛ)
          ])))
       · mᵛ
       · nᵛ)
      ])
     · two))
   —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero)))) ⟩
   (ƛ nˢ ⇒
    case two [zero⇒ nᵛ |suc mˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
        ])))
     · mᵛ
     · nᵛ)
    ])
   ·
   ((ƛ nˢ ⇒
     case two [zero⇒ nᵛ |suc mˢ ⇒
     `suc
     ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
         case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
         ])))
      · mᵛ
      · nᵛ)
     ])
    ·
    case `zero [zero⇒ `zero |suc mˢ ⇒
    (μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
       case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
       ])))
    · two
    ·
    ((μ *ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ `zero |suc mˢ ⇒
        (μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
           case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
           ])))
        · nᵛ
        · (*ᵛ · mᵛ · nᵛ)
        ])))
     · mᵛ
     · two)
    ])
   —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ β-zero) ⟩
   (ƛ nˢ ⇒
    case two [zero⇒ nᵛ |suc mˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
        ])))
     · mᵛ
     · nᵛ)
    ])
   ·
   ((ƛ nˢ ⇒
     case two [zero⇒ nᵛ |suc mˢ ⇒
     `suc
     ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
         case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
         ])))
      · mᵛ
      · nᵛ)
     ])
    · `zero)
   —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
   (ƛ nˢ ⇒
    case two [zero⇒ nᵛ |suc mˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
        ])))
     · mᵛ
     · nᵛ)
    ])
   ·
   case two [zero⇒ `zero |suc mˢ ⇒
   `suc
   ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
       case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
       ])))
    · mᵛ
    · `zero)
   ]
   —→⟨ ξ-·₂ V-ƛ (β-suc (V-suc V-zero)) ⟩
   (ƛ nˢ ⇒
    case two [zero⇒ nᵛ |suc mˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
        ])))
     · mᵛ
     · nᵛ)
    ])
   ·
   `suc
   ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
       case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
       ])))
    · one
    · `zero)
   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
   (ƛ nˢ ⇒
    case two [zero⇒ nᵛ |suc mˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
        ])))
     · mᵛ
     · nᵛ)
    ])
   ·
   `suc
   ((ƛ mˢ ⇒ (ƛ nˢ ⇒
      case mᵛ [zero⇒ nᵛ |suc mˢ ⇒
      `suc
      ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
          case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
          ])))
       · mᵛ
       · nᵛ)
      ]))
    · one
    · `zero)
   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero)))) ⟩
   (ƛ nˢ ⇒
    case two [zero⇒ nᵛ |suc mˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
        ])))
     · mᵛ
     · nᵛ)
    ])
   ·
   `suc
   ((ƛ nˢ ⇒
     case one [zero⇒ nᵛ |suc mˢ ⇒
     `suc
     ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
         case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
         ])))
      · mᵛ
      · nᵛ)
     ])
    · `zero)
   —→⟨ ξ-·₂ V-ƛ (ξ-suc (β-ƛ V-zero)) ⟩
   (ƛ nˢ ⇒
    case two [zero⇒ nᵛ |suc mˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
        ])))
     · mᵛ
     · nᵛ)
    ])
   ·
   `suc
   case one [zero⇒ `zero |suc mˢ ⇒
   `suc
   ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
       case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
       ])))
    · mᵛ
    · `zero)
   ]
   —→⟨ ξ-·₂ V-ƛ (ξ-suc (β-suc V-zero)) ⟩
   (ƛ nˢ ⇒
    case two [zero⇒ nᵛ |suc mˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
        ])))
     · mᵛ
     · nᵛ)
    ])
   ·
   `suc
   (`suc
    ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
        ])))
     · `zero
     · `zero))
   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ)))) ⟩
   (ƛ nˢ ⇒
    case two [zero⇒ nᵛ |suc mˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
        ])))
     · mᵛ
     · nᵛ)
    ])
   ·
   `suc
   (`suc
    ((ƛ mˢ ⇒ (ƛ nˢ ⇒
       case mᵛ [zero⇒ nᵛ |suc mˢ ⇒
       `suc
       ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
           case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
           ])))
        · mᵛ
        · nᵛ)
       ]))
     · `zero
     · `zero))
   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero)))) ⟩
   (ƛ nˢ ⇒
    case two [zero⇒ nᵛ |suc mˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
        ])))
     · mᵛ
     · nᵛ)
    ])
   ·
   `suc
   (`suc
    ((ƛ nˢ ⇒
      case `zero [zero⇒ nᵛ |suc mˢ ⇒
      `suc
      ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
          case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
          ])))
       · mᵛ
       · nᵛ)
      ])
     · `zero))
   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc (β-ƛ V-zero))) ⟩
   (ƛ nˢ ⇒
    case two [zero⇒ nᵛ |suc mˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
        ])))
     · mᵛ
     · nᵛ)
    ])
   ·
   `suc
   (`suc
    case `zero [zero⇒ `zero |suc mˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
        ])))
     · mᵛ
     · `zero)
    ])
   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc β-zero)) ⟩
   (ƛ nˢ ⇒
    case two [zero⇒ nᵛ |suc mˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
        ])))
     · mᵛ
     · nᵛ)
    ])
   · two
   —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
   case two [zero⇒ two |suc mˢ ⇒
   `suc
   ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
       case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
       ])))
    · mᵛ
    · two)
   ]
   —→⟨ β-suc (V-suc V-zero) ⟩
   `suc
   ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
       case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
       ])))
    · one
    · two)
   —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
   `suc
   ((ƛ mˢ ⇒ (ƛ nˢ ⇒
      case mᵛ [zero⇒ nᵛ |suc mˢ ⇒
      `suc
      ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
          case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
          ])))
       · mᵛ
       · nᵛ)
      ]))
    · one
    · two)
   —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
   `suc
   ((ƛ nˢ ⇒
     case one [zero⇒ nᵛ |suc mˢ ⇒
     `suc
     ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
         case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
         ])))
      · mᵛ
      · nᵛ)
     ])
    · two)
   —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
   `suc
   case one [zero⇒ two |suc mˢ ⇒
   `suc
   ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
       case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
       ])))
    · mᵛ
    · two)
   ]
   —→⟨ ξ-suc (β-suc V-zero) ⟩
   `suc
   (`suc
    ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
        ])))
     · `zero
     · two))
   —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
   `suc
   (`suc
    ((ƛ mˢ ⇒ (ƛ nˢ ⇒
       case mᵛ [zero⇒ nᵛ |suc mˢ ⇒
       `suc
       ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
           case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
           ])))
        · mᵛ
        · nᵛ)
       ]))
     · `zero
     · two))
   —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
   `suc
   (`suc
    ((ƛ nˢ ⇒
      case `zero [zero⇒ nᵛ |suc mˢ ⇒
      `suc
      ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
          case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
          ])))
       · mᵛ
       · nᵛ)
      ])
     · two))
   —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
   `suc
   (`suc
    case `zero [zero⇒ two |suc mˢ ⇒
    `suc
    ((μ +ˢ ⇒ (ƛ mˢ ⇒ (ƛ nˢ ⇒
        case mᵛ [zero⇒ nᵛ |suc mˢ ⇒ `suc (+ᵛ · mᵛ · nᵛ)
        ])))
     · mᵛ
     · two)
    ])
   —→⟨ ξ-suc (ξ-suc β-zero) ⟩ `suc (`suc (`suc (`suc (`zero)))) _—↠_.∎)
  (done (V-suc (V-suc (V-suc (V-suc V-zero)))))
_ = refl

--------------------------------------------------------------------------------

-- exercise [progress-preservation]
-- exercise [subject-expansion]

-- skipped

--------------------------------------------------------------------------------

-- exercise [stuck]

-- give an example of an ill-typed term that does get stuck

bad : Stuck (`zero · `suc `zero)
bad = ⟨ (λ{ (ξ-·₁ ()) ; (ξ-·₂ _ (ξ-suc ())) }) , (λ()) ⟩

--------------------------------------------------------------------------------

-- exercise [unstuck] (recommended)

-- provide proofs of the three postulates, unstuck, preserves, and wttdgs above

unstuck : ∀ {M A} → ∅ ⊢ M ⦂ A → ¬ (Stuck M)
unstuck ⊢M with progress ⊢M
... | step M→M′ = λ ¬M→M′ → proj₁ ¬M→M′ M→M′
... | done VM = λ ¬VM → proj₂ ¬VM VM

preserves : ∀ {M N A} → ∅ ⊢ M ⦂ A → M —↠ N → ∅ ⊢ N ⦂ A
preserves ⊢M (M ∎) = ⊢M
preserves ⊢L (L —→⟨ L→M ⟩ M↠N) with preserve ⊢L L→M
... | ⊢M = preserves ⊢M M↠N

wttdgs : ∀ {M N A} → ∅ ⊢ M ⦂ A → M —↠ N → ¬ (Stuck N)
wttdgs ⊢M M↠N with preserves ⊢M M↠N
... | ⊢N = unstuck ⊢N

\end{code}

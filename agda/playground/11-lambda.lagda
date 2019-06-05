\begin{code}

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.String using (String)
open import Data.String.Unsafe using (_≟_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (¬?)
open import Data.List using (List; _∷_; [])

open import plfa.Isomorphism using (extensionality; _≲_; _≃_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

--------------------------------------------------------------------------------

Id : Set
Id = String

infix  5  ƛ_⇒_
infix  5  μ_⇒_
infixl 7  _·_
infix  8  `suc_
infix  9  `_

data Term : Set where
  `_                   : Id → Term
  ƛ_⇒_                 : Id → Term → Term
  _·_                  : Term → Term → Term
  `zero                : Term
  `suc_                : Term → Term
  case_[zero⇒_|suc_⇒_] : Term → Term → Id → Term → Term
  μ_⇒_                 : Id → Term → Term

--------------------------------------------------------------------------------

two : Term
two = `suc `suc `zero

plus : Term
plus = μ "+" ⇒ ƛ "a" ⇒ ƛ "b" ⇒ case ` "a"
  [zero⇒ ` "b"
  |suc "a" ⇒ `suc ( ` "+" · ` "a" · ` "b" )
  ]

four : Term
four = plus · two · two

--------------------------------------------------------------------------------

-- church

twoᶜ : Term
twoᶜ = ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · ` "z")

plusᶜ : Term
plusᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc (` "n")

--------------------------------------------------------------------------------

-- exercise [mul] (recommended)

-- write out the definition of a lambda term
-- that multiplies two natural numbers

-- your definition may use plus as defined earlier

mul : Term
mul = μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒ case ` "m"
  [zero⇒ `zero
  |suc "m" ⇒ plus · ` "n" · (` "*" · ` "m" · ` "n")
  ]

--------------------------------------------------------------------------------

-- exercise [mulᶜ]

-- write out the definition of a lambda term that multiplies two
-- natural numbers represented as Church numerals

-- your definition may use plusᶜ as defined earlier (or may
-- not — there are nice definitions both ways)

mulᶜ : Term
mulᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ ` "m" · (` "n" · ` "s") · ` "z"

--------------------------------------------------------------------------------

-- exercise [primed] (stretch)

-- we can make examples with lambda terms slightly easier
-- to write by adding the following definitions

ƛ′_⇒_ : Term → Term → Term
ƛ′ (` x) ⇒ N  = ƛ x ⇒ N
ƛ′ _ ⇒ _      = ⊥-elim impossible
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
          case′ m
            [zero⇒ n
            |suc m ⇒ `suc (+ · m · n)
            ]
  where
    + = ` "+"
    m = ` "m"
    n = ` "n"

-- write out the definition of multiplication in the same style

mul′ : Term
mul′ = μ′ * ⇒ ƛ′ m ⇒ ƛ′ n ⇒
  case′ m [zero⇒ `zero |suc m ⇒ plus · n · (* · m · n)]
  where * = ` "*"; m = ` "m"; n = ` "n"

--------------------------------------------------------------------------------

-- values

data Value : Term → Set where
  V-ƛ    : ∀ {x N} → Value (ƛ x ⇒ N)
  V-zero : Value `zero
  V-suc  : ∀ {V} → Value V → Value (`suc V)

infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y
... | yes _          = V
... | no  _          = ` x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _          = ƛ x ⇒ N
... | no  _          = ƛ x ⇒ N [ y := V ]
(L · M) [ y := V ]   = L [ y := V ] · M [ y := V ]
(`zero) [ y := V ]   = `zero
(`suc M) [ y := V ]  = `suc M [ y := V ]
(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ] with x ≟ y
... | yes _ = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]
... | no  _ = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _          = μ x ⇒ N
... | no  _          = μ x ⇒ N [ y := V ]

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
(` x) [ y := V ]′ = V if x ≟ y else (` x)
(ƛ x ⇒ N) [ y := V ]′ = ƛ x ⇒ bound? x y N V
(L · M) [ y := V ]′   = L [ y := V ]′ · M [ y := V ]′
(`zero) [ y := V ]′   = `zero
(`suc M) [ y := V ]′  = `suc M [ y := V ]′
(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ]′ =
  case L [ y := V ]′ [zero⇒ M [ y := V ]′ |suc x ⇒ bound? x y N V ]
(μ x ⇒ N) [ y := V ]′ = μ x ⇒ bound? x y N V

bound? x y N V = N if x ≟ y else (N [ y := V ]′)

-- testing

_ : (ƛ "z" ⇒ ` "s" · (` "s" · ` "z")) [ "s" := sucᶜ ]′
       ≡  ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")
_ = refl

_ : (sucᶜ · (sucᶜ · ` "z")) [ "z" := `zero ]′ ≡  sucᶜ · (sucᶜ · `zero)
_ = refl

_ : (ƛ "x" ⇒ ` "y") [ "y" := `zero ]′ ≡ ƛ "x" ⇒ `zero
_ = refl

_ : (ƛ "x" ⇒ ` "x") [ "x" := `zero ]′ ≡ ƛ "x" ⇒ ` "x"
_ = refl

_ : (ƛ "y" ⇒ ` "y") [ "x" := `zero ]′ ≡ ƛ "y" ⇒ ` "y"
_ = refl

--------------------------------------------------------------------------------

-- reduction

infix 4 _—→_

data _—→_ : Term → Term → Set where
  ξ-·₁   : ∀ {L L′ M} → L —→ L′           → L · M         —→ L′ · M
  ξ-·₂   : ∀ {V M M′} → Value V → M —→ M′ → V · M         —→ V · M′
  ξ-suc  : ∀ {M M′}   → M —→ M′           → `suc M        —→ `suc M′
  β-ƛ    : ∀ {x N V}  → Value V           → (ƛ x ⇒ N) · V —→ N [ x := V ]
  β-μ    : ∀ {x M}                        → μ x ⇒ M       —→ M [ x := μ x ⇒ M ]
  β-zero : ∀ {x M N}  → case `zero [zero⇒ M |suc x ⇒ N ]  —→ M

  β-suc  : ∀ {x V M N} → Value V
    → case `suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]

  ξ-case : ∀ {x L L′ M N} → L —→ L′
    → case L [zero⇒ M |suc x ⇒ N ] —→ case L′ [zero⇒ M |suc x ⇒ N ]

--------------------------------------------------------------------------------

-- reflexive and transitive closure

infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ : Term → Term → Set where
  _∎      : ∀ M                         → M —↠ M
  _—→⟨_⟩_ : ∀ L {M N} → L —→ M → M —↠ N → L —↠ N

begin_ : ∀ {M N} → M —↠ N → M —↠ N
begin M—↠N = M—↠N

-- alternative
data _—↠′_ : Term → Term → Set where
  step′  : ∀ {M N}   → M —→ N            → M —↠′ N
  refl′  : ∀ {M}                         → M —↠′ M
  trans′ : ∀ {L M N} → L —↠′ M → M —↠′ N → L —↠′ N

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
    from {M} {N} (step′ M→N) = M —→⟨ M→N ⟩ N ∎
    from {M} refl′ = M ∎
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
_ = let aˢ = "a"; bˢ = "b"; a = ` aˢ; b = ` bˢ; a+b = plus · a · b in
  begin
    plus · one · one
  —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
    (ƛ aˢ ⇒ ƛ bˢ ⇒ case a [zero⇒ b |suc aˢ ⇒ `suc a+b ]) · one · one
  —→⟨ ξ-·₁ (β-ƛ (V-suc V-zero)) ⟩
    (ƛ bˢ ⇒ case one [zero⇒ b |suc aˢ ⇒ `suc a+b ]) · one
  —→⟨ β-ƛ (V-suc V-zero) ⟩
    case one [zero⇒ one |suc aˢ ⇒ `suc (plus · a · one) ]
  —→⟨ β-suc V-zero ⟩
    `suc (plus · `zero · one)
  —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
    `suc ((ƛ aˢ ⇒ ƛ bˢ ⇒ case a [zero⇒ b |suc aˢ ⇒ `suc a+b ]) · `zero · one)
  —→⟨ ξ-suc (ξ-·₁ (β-ƛ V-zero)) ⟩
    `suc ((ƛ bˢ ⇒ case `zero [zero⇒ b |suc aˢ ⇒ `suc a+b ]) · one)
  —→⟨ ξ-suc (β-ƛ (V-suc V-zero)) ⟩
    `suc (case `zero [zero⇒ one |suc aˢ ⇒ `suc (plus · a · one) ])
  —→⟨ ξ-suc (β-zero) ⟩
    `suc one
  ∎

--------------------------------------------------------------------------------

-- types

infixr 7 _⇒_
data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ  : Type

infixl 5 _,_⦂_
data Context : Set where
  ∅     : Context
  _,_⦂_ : Context → Id → Type → Context

--------------------------------------------------------------------------------

-- exercise [Context-≃]

-- show that Context is isomorphic to List (Id × Type)

-- for instance, the isomorphism relates the context
--   ∅ , "s" ⦂ `ℕ ⇒ `ℕ , "z" ⦂ `ℕ
-- to the list
--   [ ⟨ "z" , `ℕ ⟩ , ⟨ "s" , `ℕ ⇒ `ℕ ⟩ ]

Context-≃ : Context ≃ List (Id × Type)
Context-≃ = record
  { to = to ; from = from ; from∘to = from∘to ; to∘from = to∘from }
  where
    to : Context → List (Id × Type)
    to ∅ = []
    to (c , id ⦂ t) = ⟨ id , t ⟩ ∷ to c

    from : List (Id × Type) → Context
    from [] = ∅
    from (⟨ id , t ⟩ ∷ xs) = from xs , id ⦂ t

    from∘to : (x : Context) → from (to x) ≡ x
    from∘to ∅ = refl
    from∘to (c , id ⦂ t) rewrite from∘to c = refl

    to∘from : (x : List (Id × Type)) → to (from x) ≡ x
    to∘from [] = refl
    to∘from (⟨ id , t ⟩ ∷ xs) rewrite to∘from xs = refl

--------------------------------------------------------------------------------

-- lookup judgment

infix  4  _∋_⦂_
data _∋_⦂_ : Context → Id → Type → Set where
  Z : ∀ {Γ x A}     → (Γ , x ⦂ A ∋ x ⦂ A)
  S : ∀ {Γ x y A B} → (x ≢ y) → (Γ ∋ x ⦂ A) → (Γ , y ⦂ B ∋ x ⦂ A)

infix  4  _⊢_⦂_
data _⊢_⦂_ : Context → Term → Type → Set where
  -- Axiom
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
    → Γ ⊢ ` x ⦂ A

  -- ⇒-I
  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ⦂ B
    → Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B

  -- ⇒-E
  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
    → Γ ⊢ L · M ⦂ B

  -- ℕ-I₁
  ⊢zero : ∀ {Γ}
    → Γ ⊢ `zero ⦂ `ℕ

  -- ℕ-I₂
  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ⦂ `ℕ
    → Γ ⊢ `suc M ⦂ `ℕ

  -- ℕ-E
  ⊢case : ∀ {Γ L M x N A}
    → Γ ⊢ L ⦂ `ℕ
    → Γ ⊢ M ⦂ A
    → Γ , x ⦂ `ℕ ⊢ N ⦂ A
    → Γ ⊢ case L [zero⇒ M |suc x ⇒ N ] ⦂ A

  ⊢μ : ∀ {Γ x M A}
    → Γ , x ⦂ A ⊢ M ⦂ A
    → Γ ⊢ μ x ⇒ M ⦂ A

--------------------------------------------------------------------------------

-- inequality & impossible

_≠_ : ∀ (x y : Id) → x ≢ y
x ≠ y with x ≟ y
... | no  x≢y = x≢y
... | yes _   = ⊥-elim impossible
  where postulate impossible : ⊥

--------------------------------------------------------------------------------

-- interaction with agda

⊢sucᶜ : ∅ ⊢ sucᶜ ⦂ `ℕ ⇒ `ℕ
⊢sucᶜ = ⊢ƛ (⊢suc (⊢` Z))

--------------------------------------------------------------------------------

-- lookup is injective

∋-injective : ∀ {Γ x A B} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
∋-injective Z        Z         = refl
∋-injective Z        (S x≢ _)  = ⊥-elim (x≢ refl)
∋-injective (S x≢ _) Z         = ⊥-elim (x≢ refl)
∋-injective (S _ ∋x) (S _ ∋x′) = ∋-injective ∋x ∋x′

--------------------------------------------------------------------------------

⊢plus : ∀ {Γ} → Γ ⊢ plus ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢plus = ⊢μ (⊢ƛ (⊢ƛ (⊢case
    (⊢` ∋m)
    (⊢` ∋n)
    (⊢suc (⊢` ∋+ · ⊢` ∋m′ · ⊢` ∋n′))
  )))
  where
  ∋+  = (S ("+" ≠ "a") (S ("+" ≠ "b") (S ("+" ≠ "a") Z)))
  ∋m  = (S ("a" ≠ "b") Z)
  ∋n  = Z
  ∋m′ = Z
  ∋n′ = (S ("b" ≠ "a") Z)

--------------------------------------------------------------------------------

-- exercise [mul-type] (recommended)

-- using the term mul you defined earlier, write out
-- the derivation showing that it is well-typed

mul-type : ∀ {Γ} → Γ ⊢ mul ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
mul-type = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` ∋m) (⊢zero) N)))
  where
    ∋m = S ("m" ≠ "n") Z
    ∋n = S ("n" ≠ "m") Z
    ∋* = S ("*" ≠ "m") (S ("*" ≠ "n") (S ("*" ≠ "m") Z))
    N  = ⊢plus · (⊢` ∋n) · ((⊢` ∋*) · ⊢` Z · (⊢` ∋n))

--------------------------------------------------------------------------------

-- Exercise [mulᶜ-type]

-- using the term mulᶜ you defined earlier, write out
-- the derivation showing that it is well-typed

Ch : Type → Type
Ch A = (A ⇒ A) ⇒ A ⇒ A

mulᶜ-type : ∀ {Γ A} → Γ ⊢ mulᶜ ⦂ Ch A ⇒ Ch A ⇒ Ch A
mulᶜ-type = ⊢ƛ (⊢ƛ (⊢ƛ (⊢ƛ T)))
  where
    ∋m = S ("m" ≠ "z") (S ("m" ≠ "s") (S ("m" ≠ "n") Z))
    ∋n = S ("n" ≠ "z") (S ("n" ≠ "s") Z)
    ∋s = (S ("s" ≠ "z") Z)
    T  = (⊢` ∋m) · ((⊢` ∋n) · (⊢` ∋s)) · (⊢` Z)

\end{code}

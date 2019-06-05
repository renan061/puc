\begin{code}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Function using (_∘_)
open import Level using (Level)
open import 5-isomorphism using (_≃_; _⇔_)

--------------------------------------------------------------------------------

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

{-# BUILTIN LIST List #-}

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

--------------------------------------------------------------------------------

-- functions over lists

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

++-assoc : ∀ {A : Set} (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs rewrite ++-assoc xs ys zs = refl

++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs = refl

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] = refl
++-identityʳ (x ∷ xs) = begin
  (x ∷ xs) ++ []  ≡⟨⟩
  x ∷ (xs ++ [])  ≡⟨ cong (x ∷_) (++-identityʳ xs) ⟩
  x ∷ xs          ∎

reverse : ∀ {A : Set} → List A → List A
reverse []       = []
reverse (x ∷ xs) = reverse xs ++ [ x ]

--------------------------------------------------------------------------------

-- exercise [reverse-++-commute] (recommended)

-- show that the reverse of one list appended to another is the reverse
-- of the second appended to the reverse of the first:

reverse-++-commute : ∀ {A : Set} {xs ys : List A} →
  reverse (xs ++ ys) ≡ reverse ys ++ reverse xs

reverse-++-commute {_} {[]} {ys} rewrite ++-identityʳ (reverse ys) = refl
reverse-++-commute {_} {x ∷ xs} {ys}
  rewrite reverse-++-commute {_} {xs} {ys}
        | ++-assoc (reverse ys) (reverse xs) ([ x ])
        = refl

--------------------------------------------------------------------------------

-- exercise [reverse-involutive] (recommended)

-- a function is an involution if when applied twice it acts as the identity
-- function

-- show that reverse is an involution

reverse-involutive : ∀ {A : Set} {xs : List A} → reverse (reverse xs) ≡ xs
reverse-involutive {_} {[]} = refl
reverse-involutive {_} {x ∷ xs}
  rewrite reverse-++-commute {_} {reverse xs} {x ∷ []}
        | reverse-involutive {_} {xs}
        = refl

--------------------------------------------------------------------------------

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

--------------------------------------------------------------------------------

-- exercise [map-compose]

-- prove that the map of a composition is equal to the composition of two maps

postulate
  extensionality : ∀ {A B : Set} {f g : A → B} → (∀ (x : A) → f x ≡ g x) → f ≡ g

map-compose : ∀ {A B C : Set} {f : A → B} {g : B → C} →
  map (g ∘ f) ≡ map g ∘ map f

map-compose {_} {_} {_} {f} {g} = extensionality helper
  where
    helper : ∀ {A B C : Set} {f : A → B} {g : B → C} →
      ∀ (xs : List A) → map (g ∘ f) xs ≡ (map g ∘ map f) xs
    helper [] = refl
    helper {_} {_} {_} {f} {g} (x ∷ xs)
      rewrite helper {_} {_} {_} {f} {g} xs = refl

--------------------------------------------------------------------------------

-- exercise [map-++-commute]

-- prove the following relationship between map and append

map-++-commute : ∀ {A B : Set} {f : A → B} {xs ys : List A} →
  map f (xs ++ ys) ≡ map f xs ++ map f ys

map-++-commute {_} {_} {f} {[]} {ys} = refl
map-++-commute {_} {_} {f} {x ∷ xs} {ys}
  rewrite map-++-commute {_} {_} {f} {xs} {ys} = refl

--------------------------------------------------------------------------------

-- exercise [map-Tree]

-- define a type of trees with leaves of type A and internal nodes of type B

data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

-- define a suitable map operator over trees:

map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f _ (leaf a) = leaf (f a)
map-Tree f g (node l b r) = node (map-Tree f g l) (g b) (map-Tree f g r)

--------------------------------------------------------------------------------

-- fold

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e []       = e
foldr _⊗_ e (x ∷ xs) = x ⊗ foldr _⊗_ e xs

--------------------------------------------------------------------------------

-- exercise [product] (recommended)

-- use fold to define a function to find the product of a list of numbers
-- for example: product [ 1 , 2 , 3 , 4 ] ≡ 24

product : List ℕ → ℕ
product = foldr _*_ 1

--------------------------------------------------------------------------------

-- exercise [foldr-++] (recommended)

-- show that fold and append are related as follows

foldr-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (e : B) (xs ys : List A) →
  foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs

foldr-++ ⊗ e [] ys = refl
foldr-++ ⊗ e (x ∷ xs) ys rewrite foldr-++ ⊗ e xs ys = refl

--------------------------------------------------------------------------------

-- exercise [map-is-foldr]

-- show that map can be defined using fold

map-is-foldr : ∀ {A B : Set} {f : A → B} → map f ≡ foldr (λ x xs → f x ∷ xs) []
map-is-foldr {_} {_} {f} = extensionality helper
  where
    helper : ∀ {A B : Set} {f : A → B} →
      (ys : List A) → map f ys ≡ foldr (λ x xs → f x ∷ xs) [] ys
    helper {_} {_} {f} [] = refl
    helper {_} {_} {f} (y ∷ ys) rewrite helper {_} {_} {f} ys = refl

--------------------------------------------------------------------------------

-- exercise [fold-Tree]

-- define a suitable fold function for the type of trees given earlier:

fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree l⊗ n⊗ (leaf a) = l⊗ a
fold-Tree l⊗ n⊗ (node l b r) = n⊗ (fold-Tree l⊗ n⊗ l) b (fold-Tree l⊗ n⊗ r)

--------------------------------------------------------------------------------

-- exercise [map-is-fold-Tree]

-- demonstrate an analogue of map-is-foldr for the type of trees

-- map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
-- map-Tree f _ (leaf a) = leaf (f a)
-- map-Tree f g (node l b r) = node (map-Tree f g l) (g b) (map-Tree f g r)

{-
tree-map-is-fold : ∀ {A B C D : Set} {f : A → C} {g : B → D} →
  map-Tree f g ≡ fold-Tree (λ a → leaf (f a)) (λ b → node )

tree-map-is-fold = {!!}
-}

-- TODO

--------------------------------------------------------------------------------

-- exercise [sum-downFrom] (stretch)

sum : List ℕ → ℕ
sum = foldr _+_ 0

downFrom : ℕ → List ℕ
downFrom zero = []
downFrom (suc n) = n ∷ downFrom n

{-
sum-downFrom : ∀ (n : ℕ) → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
sum-downFrom zero = refl
sum-downFrom (suc n) = {!!}
-}

-- TODO

--------------------------------------------------------------------------------

-- monoids

record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid

+-monoid : IsMonoid _+_ 0
+-monoid =
  record
    { assoc = +-assoc
    ; identityˡ = +-identityˡ
    ; identityʳ = +-identityʳ
    }

*-monoid : IsMonoid _*_ 1
*-monoid =
  record
    { assoc = *-assoc
    ; identityˡ = *-identityˡ
    ; identityʳ = *-identityʳ
    }

++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
++-monoid =
  record
    { assoc = ++-assoc
    ; identityˡ = ++-identityˡ
    ; identityʳ = ++-identityʳ
    }

--------------------------------------------------------------------------------

foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y

foldr-monoid _⊗_ e ⊗-monoid [] y rewrite identityˡ ⊗-monoid y = refl
foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y = begin
  foldr _⊗_ y (x ∷ xs)      ≡⟨⟩
  x ⊗ (foldr _⊗_ y xs)      ≡⟨ cong (x ⊗_) (foldr-monoid _⊗_ e ⊗-monoid xs y) ⟩
  x ⊗ (foldr _⊗_ e xs ⊗ y)  ≡⟨ sym (assoc ⊗-monoid x (foldr _⊗_ e xs) y) ⟩
  (x ⊗ foldr _⊗_ e xs) ⊗ y  ≡⟨⟩
  foldr _⊗_ e (x ∷ xs) ⊗ y  ∎

foldr-monoid-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs ys : List A) → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ e xs ⊗ foldr _⊗_ e ys

foldr-monoid-++ _⊗_ e monoid-⊗ xs ys
  rewrite foldr-++ _⊗_ e xs ys
        | foldr-monoid _⊗_ e monoid-⊗ xs (foldr _⊗_ e ys)
        = refl

--------------------------------------------------------------------------------

-- exercise [foldl]

-- define a function foldl which is analogous to foldr, but where operations
-- associate to the left rather than the right

-- for example:
--   foldr _⊗_ e [ x , y , z ]  =  x ⊗ (y ⊗ (z ⊗ e))
--   foldl _⊗_ e [ x , y , z ]  =  ((e ⊗ x) ⊗ y) ⊗ z

foldl : ∀ {A B : Set} → (B → A → B) → B → List A → B
foldl _⊗_ b []       = b
foldl _⊗_ b (a ∷ as) = foldl _⊗_ (b ⊗ a) as

--------------------------------------------------------------------------------

-- exercise [foldr-monoid-foldl]

-- show that if _⊗_ and e form a monoid, then `foldr _⊗_ e` and
-- `foldl _⊗_ e` always compute the same result

postulate
  foldr-monoid-foldl : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
    ∀ (as : List A) → foldr _⊗_ e as ≡ foldl _⊗_ e as

{-
foldr-monoid-foldl _⊗_ e _ [] = refl
foldr-monoid-foldl _⊗_ e m [ a ] rewrite identityʳ m a | identityˡ m a = refl
foldr-monoid-foldl _⊗_ e m (a₁ ∷ a₂ ∷ as)
  rewrite sym (assoc m a₁ a₂ (foldr _⊗_ e as))
        | foldr-monoid-foldl _⊗_ e m (a₁ ⊗ a₂ ∷ as)
        | sym (assoc m e a₁ a₂)
        = refl
-}

--------------------------------------------------------------------------------

-- all

data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

--------------------------------------------------------------------------------

-- any

data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

infix 4 _∈_ _∉_

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)

--------------------------------------------------------------------------------

-- all & append

All-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ⇔ (All P xs × All P ys)

All-++-⇔ xs ys =
  record
    { to       =  to xs ys
    ; from     =  from xs ys
    }
  where
    to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
      All P (xs ++ ys) → (All P xs × All P ys)
    to [] ys Pys = ⟨ [] , Pys ⟩
    to (x ∷ xs) ys (Px ∷ Pxs++ys) with to xs ys Pxs++ys
    ... | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩

    from : ∀ { A : Set} {P : A → Set} (xs ys : List A) →
      All P xs × All P ys → All P (xs ++ ys)
    from [] ys ⟨ [] , Pys ⟩ = Pys
    from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ =  Px ∷ from xs ys ⟨ Pxs , Pys ⟩

--------------------------------------------------------------------------------

-- exercise [Any-++-⇔] (recommended)

-- prove a result similar to All-++-⇔, but with Any in place of All, and a
-- suitable replacement for _×_

id : {A : Set} → A → A
id x = x

Any-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)

Any-++-⇔ xs ys =
  record
    { to   = to xs ys
    ; from = from xs ys
    }
  where
    to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
      Any P (xs ++ ys) → (Any P xs ⊎ Any P ys)
    to [] ys AnyPys = inj₂ AnyPys
    to (x ∷ xs) ys (here Px) = inj₁ (here Px)
    to (x ∷ xs) ys (there AnyP[xs++ys]) with to xs ys AnyP[xs++ys]
    ... | inj₁ AnyPxs = inj₁ (there AnyPxs)
    ... | inj₂ AnyPys = inj₂ AnyPys

    from : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
      (Any P xs ⊎ Any P ys) → Any P (xs ++ ys)
    from [] [] = case-⊎ id id
    from [] (y ∷ ys) (inj₁ ())
    from [] (y ∷ ys) (inj₂ AnyP[y∷ys]) = AnyP[y∷ys]
    from (x ∷ xs) [] (inj₁ AnyP[x∷xs]) rewrite ++-identityʳ xs = AnyP[x∷xs]
    from (x ∷ xs) [] (inj₂ ())
    from (x ∷ xs) (y ∷ ys) (inj₁ (here Px)) = here Px
    from (x ∷ xs) r@(y ∷ ys) (inj₁ (there AnyPxs)) =
      there (from xs r (inj₁ AnyPxs))
    from (x ∷ xs) r@(y ∷ ys) (inj₂ (here Py)) =
      there (from xs r (inj₂ (here Py)))
    from (x ∷ xs) r@(y ∷ ys) (inj₂ (there AnyPys)) =
      there (from xs r (inj₂ (there AnyPys)))

-- as a consequence, demonstrate an equivalence relating _∈_ and _++_

∈-++ : ∀ {A : Set} (a : A) (xs ys : List A) → (a ∈ xs ++ ys) ⇔ (a ∈ xs ⊎ a ∈ ys)
∈-++ {A} a xs ys = Any-++-⇔ xs ys

--------------------------------------------------------------------------------

-- decidability

all : ∀ {A : Set} → (A → Bool) → List A → Bool
all p = foldr _∧_ true ∘ map p

Decidable : ∀ {A : Set} → (A → Set) → Set
Decidable {A} P  =  ∀ (x : A) → Dec (P x)

{-
All? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (All P)
All? P? []                                 = yes []
All? P? (x ∷ xs) with P? x   | All? P? xs
...                 | yes Px | yes Pxs     = yes (Px ∷ Pxs)
...                 | no ¬Px | _           = no λ{ (Px ∷ Pxs) → ¬Px Px   }
...                 | _      | no ¬Pxs     = no λ{ (Px ∷ Pxs) → ¬Pxs Pxs }
-}

-- TODO: exercises

\end{code}

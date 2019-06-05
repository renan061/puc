\begin{code}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using ()
  renaming (contradiction to ¬¬-intro)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)

open import 3-relations using (_<_; z<s; s<s)
open import 5-isomorphism using (_⇔_)

--------------------------------------------------------------------------------

data Bool : Set where
  true  : Bool
  false : Bool

--------------------------------------------------------------------------------

data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

¬s≤z : ∀ {m : ℕ} → ¬ (suc m ≤ zero)
¬s≤z ()

¬s≤s : ∀ {m n : ℕ} → ¬ (m ≤ n) → ¬ (suc m ≤ suc n)
¬s≤s ¬m≤n (s≤s m≤n) = ¬m≤n m≤n

_≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)
zero ≤? n = yes z≤n
suc m ≤? zero = no ¬s≤z
suc m ≤? suc n with m ≤? n
... | yes m≤n = yes (s≤s m≤n)
... | no ¬m≤n = no (¬s≤s ¬m≤n)

--------------------------------------------------------------------------------

-- exercise [_<?_] (recommended)

-- analogous to the function above, define a
-- function to decide strict inequality

¬z<z : ¬ zero < zero
¬z<z ()

¬s<z : ∀ {m : ℕ} → ¬ suc m < zero
¬s<z {zero} ()
¬s<z {suc m} ()

¬s<s : ∀ {m n : ℕ} → ¬ (m < n) → ¬ (suc m < suc n)
¬s<s ¬m<n (s<s m<n) = ¬m<n m<n 

_<?_ : ∀ (m n : ℕ) → Dec (m < n)
zero <? zero = no ¬z<z
zero <? suc _ = yes z<s
suc m <? zero = no ¬s<z
suc m <? suc n with m <? n
... | yes m<n = yes (s<s m<n)
... | no ¬m<n = no (¬s<s ¬m<n)

--------------------------------------------------------------------------------

-- exercise [_≡ℕ?_]

-- define a function to decide whether two naturals are equal

_≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)
zero ≡ℕ? zero = yes refl
zero ≡ℕ? suc n = no λ()
suc m ≡ℕ? zero = no λ()
suc m ≡ℕ? suc n with m ≡ℕ? n
... | yes refl = yes refl
... | no ¬m≡n = no (λ{ refl → ¬m≡n refl })

--------------------------------------------------------------------------------

-- erasure

⌊_⌋ : ∀ {A : Set} → Dec A → Bool
⌊ yes x ⌋ = true
⌊ no ¬x ⌋ = false

--------------------------------------------------------------------------------

-- logical connectives

infixr 6 _∧_

_∧_ : Bool → Bool → Bool
true  ∧ true  = true
true  ∧ false = false
false ∧ _     = false

infixr 6 _×-dec_

_×-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A × B)
yes x ×-dec yes y = yes ⟨ x , y ⟩
no ¬x ×-dec _     = no λ{ ⟨ x , y ⟩ → ¬x x }
yes _ ×-dec no ¬y = no λ{ ⟨ x , y ⟩ → ¬y y }

infixr 5 _∨_

_∨_ : Bool → Bool → Bool
true  ∨ _     = true
false ∨ true  = true
false ∨ false = false

infixr 5 _⊎-dec_

_⊎-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⊎ B)
yes x ⊎-dec _     = yes (inj₁ x)
no _  ⊎-dec yes y = yes (inj₂ y)
no ¬x ⊎-dec no ¬y = no λ{ (inj₁ x) → ¬x x ; (inj₂ y) → ¬y y }

not : Bool → Bool
not true  = false
not false = true

¬? : ∀ {A : Set} → Dec A → Dec (¬ A)
¬? (yes x) = no (¬¬-intro x)
¬? (no ¬x) = yes ¬x

-- implication
_⊃_ : Bool → Bool → Bool
_     ⊃ true  = true
false ⊃ false = true
true  ⊃ false = false

_→-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A → B)
_     →-dec yes y = yes (λ _ → y)
no ¬x →-dec no  _ = yes (λ x → ⊥-elim (¬x x))
yes x →-dec no ¬y = no (λ f → ¬y (f x))

--------------------------------------------------------------------------------

-- exercise [erasure]

-- TODO

--------------------------------------------------------------------------------

-- exercise [iff-erasure] (recommended)

-- give analogues of the _⇔_ operation from Chapter Isomorphism, operation
-- on booleans and decidables, and also show the corresponding erasure

open _⇔_

_iff_ : Bool → Bool → Bool
a iff b = (a ⊃ b) ∧ (b ⊃ a)

_⇔-dec_ : ∀ {A B : Set} → Dec A → Dec B → Dec (A ⇔ B)
yes a ⇔-dec yes b = yes (record
  { to   = λ a → b
  ; from = λ b → a
  })
yes a ⇔-dec no ¬b = no λ a⇔b → ¬b (to a⇔b a)
no ¬a ⇔-dec yes b = no λ a⇔b → ¬a (from a⇔b b)
no ¬a ⇔-dec no ¬b = yes (record
  { to   = λ a → ⊥-elim (¬a a)
  ; from = λ b → ⊥-elim (¬b b)
  })

iff-⇔ : ∀ {A B : Set} (x : Dec A) (y : Dec B) → ⌊ x ⌋ iff ⌊ y ⌋ ≡ ⌊ x ⇔-dec y ⌋
iff-⇔ (yes a) (yes b) = refl
iff-⇔ (yes a) (no ¬b) = refl
iff-⇔ (no ¬a) (yes b) = refl
iff-⇔ (no ¬a) (no ¬b) = refl

\end{code}

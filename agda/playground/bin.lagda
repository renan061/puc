\begin{code}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc)

--------------------------------------------------------------------------------

-- bin
data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

-- binary increment
inc : Bin → Bin
inc nil = x1 nil
inc (x0 b) = x1 b
inc (x1 b) = x0 (inc b)

-- natural to binary
to : ℕ → Bin
to zero = x0 nil
to (suc n) = inc (to n)

-- natural from binary
from : Bin → ℕ
from nil = 0
from (x0 b) = from b + from b
from (x1 b) = suc (from b + from b)

--------------------------------------------------------------------------------

-- from (inc x) ≡ suc (from x)
from-inc≡suc-from : ∀ (x : Bin) → from (inc x) ≡ suc (from x)
from-inc≡suc-from nil = refl
from-inc≡suc-from (x0 x) = refl
from-inc≡suc-from (x1 x) rewrite
  from-inc≡suc-from x | +-suc (from x) (from x) = refl

-- from (to n) ≡ n
from-to≡id : ∀ (n : ℕ) → from (to n) ≡ n
from-to≡id zero = refl
from-to≡id (suc n) rewrite from-inc≡suc-from (to n) | from-to≡id n = refl

--------------------------------------------------------------------------------

data One : Bin → Set
data Can : Bin → Set

data One where
  one : ∀ {b : Bin} → Can b → One (inc b)
  
data Can where
  zero : Can (x0 nil)
  suc : ∀ {b : Bin} → One b → Can b

-- increment preserves canonical bitstrings
one-inc : ∀ {b : Bin} → One b → One (inc b)
can-inc : ∀ {b : Bin} → Can b → Can (inc b)

one-inc (one cb) = one (can-inc cb)
can-inc zero = suc (one zero)
can-inc (suc ob) = suc (one-inc ob)

-- converting a natural to a bitstring always yields a canonical bitstring
can-to : ∀ {n : ℕ} → Can (to n)
can-to {zero} = zero 
can-to {suc n} = suc (one (can-to {n}))

-- converting a canonical bitstring to a natural and back is the identity

-- auxiliary
can-from-inc≡suc-from : ∀ {b : Bin} → Can b → from (inc b) ≡ suc (from b)
can-from-inc≡suc-from {b} _ = from-inc≡suc-from b

one-to-from≡id : ∀ {b : Bin} → One b → to (from b) ≡ b
can-to-from≡id : ∀ {b : Bin} → Can b → to (from b) ≡ b

one-to-from≡id (one cb)
  rewrite can-from-inc≡suc-from cb  | can-to-from≡id cb = refl
can-to-from≡id zero = refl
can-to-from≡id osb@(suc ob)
  rewrite can-from-inc≡suc-from osb | one-to-from≡id ob = refl

--------------------------------------------------------------------------------

\end{code}

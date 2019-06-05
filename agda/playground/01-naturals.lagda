\begin{code}

-- natural numbers
data N : Set where
  zero : N
  suc  : N -> N

{-# BUILTIN NATURAL N  #-}

-- seven
seven : N
seven = suc (suc (suc (suc (suc (suc (suc zero))))))

-- definition of equality and notations for reasoning about it
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

-- addition
_+_ : N -> N -> N
zero  + n = n
suc m + n = suc (m + n)

-- proofs
_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩    -- is shorthand for
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩    -- inductive case
    suc ((suc zero) + (suc (suc (suc zero))))
  ≡⟨⟩    -- inductive case
    suc (suc (zero + (suc (suc (suc zero)))))
  ≡⟨⟩    -- base case
    suc (suc (suc (suc (suc zero))))
  ≡⟨⟩    -- is longhand for
    5
  ∎

_ : 1 + 3 ≡ 4
_ = refl

-- multiplication
_*_ : N -> N -> N
zero  * n = zero
suc m * n = n + (m * n)

_ : 5 * 3 ≡ 15
_ = refl

_ =
  begin
    3 * 4
  ≡⟨⟩
    (2 * 4) + 4
  ≡⟨⟩
    ((1 * 4) + 4) + 4
  ≡⟨⟩
    (((0 * 4) + 4) + 4) + 4
  ≡⟨⟩
    (((0) + 4) + 4) + 4
  ≡⟨⟩
    (4 + 4) + 4
  ≡⟨⟩
    12
  ∎

-- exponentiation
_^_ : N -> N -> N
m ^ zero    = 1
m ^ (suc n) = (m ^ n) * m

_ : 3 ^ 4 ≡ 81
_ = refl

-- monus
_∸_ : N -> N -> N
m       ∸ zero    = m
zero    ∸ (suc n) = zero
(suc m) ∸ (suc n) = m ∸ n

_ : 7 ∸ 3 ≡ 4
_ = refl

_ : 3 ∸ 7 ≡ 0
_ = refl

-- precendence
infixl 6 _+_ _∸_
infixl 7 _*_
infixl 8 _^_

-- more efficient
{-# BUILTIN NATPLUS  _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

-- binaries
data Bin : Set where
  nil : Bin
  x0_ : Bin -> Bin
  x1_ : Bin -> Bin

inc : Bin -> Bin
inc nil    = x1 nil
inc (x0 b) = x1 b
inc (x1 b) = x0 (inc b)

_ : inc (x1 x1 x0 x1 nil) ≡ x0 x0 x1 x1 nil
_ = refl

to : N -> Bin
to zero    = nil
to (suc n) = inc (to n)

_ : to 32 ≡ x0 x0 x0 x0 x0 x1 nil
_ = refl

_ : to 91 ≡ x1 x1 x0 x1 x1 x0 x1 nil
_ = refl

from : Bin -> N
from nil    = 0
from (x0 b) = 2 * (from b)
from (x1 b) = 2 * (from b) + 1

_ : from (x0 x0 x0 x0 x0 x1 nil) ≡ 32
_ = refl

_ : from (x1 x1 x0 x1 x1 x0 x1 nil) ≡ 91
_ = refl

\end{code}

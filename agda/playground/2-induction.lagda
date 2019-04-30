\begin{code}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

import Data.Nat.Properties as P
open P using (+-assoc; +-comm; +-identityʳ; +-suc)

-- exercise (operators)
-- example of an operator that has an identity and is
--     associative but is not commutative
-- concatenation (.)
-- identity (empty string):
--   a . "" ≡ "" . a ≡ a
-- associative:
--   (a . b) . c ≡ a . (b . c)
-- not commutative
--   a . b ≠ b . a

-- swap
+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p rewrite sym (+-assoc m n p) | +-comm m n | +-assoc n m p = refl

-- multiplication distribution over plus
*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p =
  begin
    (suc m + n) * p
  ≡⟨⟩
    suc (m + n) * p
  ≡⟨⟩
    p + ((m + n) * p)
  ≡⟨ cong (p +_) (*-distrib-+ m n p) ⟩
    p + ((m * p) + (n * p))
  ≡⟨ sym (+-assoc p (m * p) (n * p)) ⟩
    (p + (m * p)) + (n * p)
  ≡⟨⟩
    (suc m) * p + n * p
  ∎

-- multiplication is associative
*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p =
  begin
    ((suc m) * n) * p
  ≡⟨⟩
    (n + (m * n)) * p
  ≡⟨ *-distrib-+ n (m * n) p ⟩
    (n * p) + ((m * n) * p)
  ≡⟨ cong ((n * p) +_) (*-assoc m n p) ⟩
    (n * p) + (m * (n * p))
  ≡⟨⟩
    suc m * (n * p)
  ∎

-- multiplication zero
*-zero : ∀ (m : ℕ) → m * zero ≡ zero
*-zero zero = refl
*-zero (suc m) rewrite *-zero m = refl

-- *-identity (left and right)
*-identity-r : ∀ (m : ℕ) → m * 1 ≡ m
*-identity-r zero = refl
*-identity-r (suc m) rewrite *-identity-r m = refl

*-identity-l : ∀ (m : ℕ) → 1 * m ≡ m
*-identity-l zero = refl
*-identity-l (suc m) rewrite *-identity-l m = refl

-- rearrange
+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q
  ∎

-- multiplication distribution is commutative → (m + n) * p ≡ p * (m + n)
-- lema for *-comm
*-distrib-+′ : ∀ (m n p : ℕ) → m * (n + p) ≡ m * n + m * p
*-distrib-+′ zero n p = refl
*-distrib-+′ (suc m) n p =
  begin
    suc m * (n + p)
  ≡⟨⟩ -- multiplication constructor
    (n + p) + (m * (n + p))
  ≡⟨ cong ((n + p) +_) (*-distrib-+′ m n p) ⟩
    n + p + (m * n + m * p)
  ≡⟨ sym (+-assoc (n + p) (m * n) (m * p)) ⟩
    n + p + (m * n) + (m * p)
  ≡⟨ cong (_+ (m * p)) (+-assoc n p (m * n)) ⟩
    n + (p + m * n) + (m * p)
  ≡⟨ sym (+-rearrange n p (m * n) (m * p)) ⟩
    (n + p) + (m * n + m * p)
  ≡⟨ +-assoc n p (m * n + m * p) ⟩
    n + (p + (m * n + m * p))
  ≡⟨ cong (n +_) (+-swap p (m * n) (m * p)) ⟩
    n + (m * n + (p + m * p))
  ≡⟨ sym (+-assoc n (m * n) (p + m * p)) ⟩
    n + m * n + (p + m * p)
  ≡⟨⟩ -- multiplication constructor (2 times)
    (suc m) * n + (suc m) * p
  ∎

-- lema for *-comm
*-suc′ : ∀ (m n : ℕ) → m * suc n ≡ m + (n * m)
*-suc′ zero n rewrite *-zero n = refl
*-suc′ (suc m) n =
  begin
    suc m * suc n
  ≡⟨⟩
    suc n + (m * suc n)
  ≡⟨ cong (suc n +_) (*-suc′ m n) ⟩
    suc n + (m + n * m)
  ≡⟨⟩
    suc n + (suc n * m)
  ≡⟨⟩
    1 + n + ((1 + n) * m)
  ≡⟨ cong ((1 + n) +_) (*-distrib-+ 1 n m) ⟩
    1 + n + (1 * m + n * m)
  ≡⟨ cong ((1 + n) +_) (cong (_+ (n * m)) (*-identity-l m)) ⟩
    1 + n + (m + n * m)
  ≡⟨ cong (1 +_) (+-swap n m (n * m)) ⟩
    1 + m + (n + n * m)
  ≡⟨ cong ((1 + m) +_) (cong (_+ (n * m)) (sym (*-identity-r n))) ⟩
    1 + m + (n * 1 + n * m)
  ≡⟨ cong ((1 + m) +_) (sym (*-distrib-+′ n 1 m)) ⟩
    1 + m + (n * (1 + m))
  ≡⟨⟩
    suc m + (n * suc m)
  ∎

-- multiplication is commutative
*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm m zero rewrite *-zero m = refl
*-comm m (suc n) =
  begin
    m * (suc n)
  ≡⟨ *-suc′ m n ⟩
    m + (n * m)
  ≡⟨ cong (_+ (n * m)) (sym (*-identity-l m)) ⟩
    1 * m + n * m
  ≡⟨ sym (*-distrib-+ 1 n m) ⟩
    (1 + n) * m
  ≡⟨⟩
    suc n * m
  ∎

-- 0 ∸ m ≡ 0
zero-monus : ∀ (m : ℕ) → zero ∸ m ≡ zero
zero-monus zero = refl
zero-monus (suc m) = refl

-- monus associates with addition
∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc zero zero p = refl
∸-+-assoc zero (suc n) p rewrite zero-monus (suc n) | zero-monus p = refl
∸-+-assoc (suc m) zero p rewrite zero-monus (suc m) = refl
∸-+-assoc (suc m) (suc n) p =
  begin
    suc m ∸ suc n ∸ p
  ≡⟨⟩
    m ∸ n ∸ p
  ≡⟨ ∸-+-assoc m n p ⟩
    m ∸ (n + p)
  ≡⟨⟩
    suc m ∸ suc (n + p)
  ≡⟨⟩
    suc m ∸ (suc n + p)
  ∎

-- (stretch)

data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

inc : Bin → Bin
inc nil    = x1 nil
inc (x0 b) = x1 b
inc (x1 b) = x0 (inc b)

to : ℕ → Bin
to zero = nil
to (suc n) = inc (to n)

from : Bin → ℕ
from nil = 0
from (x0 b) = 2 * (from b)
from (x1 b) = 2 * (from b) + 1

-- lema for bin-1
+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

-- bin1 → from (inc x) ≡ suc (from x)
bin-1 : ∀ (x : Bin) → from (inc x) ≡ suc (from x)
bin-1 nil = refl
bin-1 (x0 x) =
  begin
    from (inc (x0 x))
  ≡⟨⟩
    from (x1 x)
  ≡⟨⟩
    2 * (from x) + 1
  ≡⟨⟩
    suc (suc 0) * (from x) + 1
  ≡⟨⟩
    from x + (suc 0 * (from x)) + 1
  ≡⟨⟩
    from x + (suc 0 * (from x)) + suc zero
  ≡⟨ +-suc′ (from x + (suc 0 * (from x))) zero ⟩
    suc (from x + (suc 0 * (from x)) + zero )
  ≡⟨ cong suc ( +-identityʳ (from x + (suc 0 * (from x)))) ⟩
    suc (from x + (suc 0 * (from x)))
  ≡⟨⟩
    suc (from x + (from x + (0 * (from x))))
  ≡⟨⟩
    suc (from x + (from x + 0))
  ≡⟨⟩
    suc (2 * (from x))
  ≡⟨⟩
    suc (from (x0 x))
  ∎
bin-1 (x1 x) =
  begin
    from (inc (x1 x))
  ≡⟨⟩
    from (x0 (inc x))
  ≡⟨⟩
    2 * (from (inc x))
  ≡⟨ cong (2 *_) (bin-1 x) ⟩
    2 * (suc (from x))
  ≡⟨⟩
    2 * (1 + (from x))
  ≡⟨ *-distrib-+′ 2 1 (from x) ⟩
    2 * 1 + 2 * (from x)
  ≡⟨ cong (_+ (2 * (from x))) (*-identity-r 2) ⟩
    2 + 2 * (from x)
  ≡⟨⟩
    suc 1 + 2 * (from x)
  ≡⟨⟩
    suc (1 + 2 * (from x))
  ≡⟨ cong suc (+-comm 1 (2 * (from x))) ⟩
    suc (2 * (from x) + 1)
  ≡⟨⟩
    suc (from (x1 x))
  ∎

-- to (from x) ≡ x
-- false
--   to (from (x0 nil))
--   to (2 * (from nil))
--   to (2 * 0)
--   to 0
--   nil
-- x0 nil ≠ nil

-- bin-2 → from (to n) ≡ n
bin-2 : ∀ (x : ℕ) → from (to x) ≡ x
bin-2 zero = refl
bin-2 (suc x) =
  begin
    from (to (suc x))
  ≡⟨⟩
    from (inc (to x))
  ≡⟨ bin-1 (to x) ⟩
    suc (from (to x))
  ≡⟨ cong suc (bin-2 x) ⟩
    suc x
  ∎

\end{code}
